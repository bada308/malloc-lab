/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // size_t의 크기를 ALIGNMENT의 배수로 올림한 결과

/* Basic constants and macros */
#define WSIZE 4             /* 워드의 크기 (바이트) */
#define DSIZE 8             /* 더블워드의 크기 (바이트) */
#define CHUNKSIZE (1 << 12) /* 힙을 이민큼 확장 (바이트) */

#define MAX(x, y) ((x > y) ? (x) : (y)) /* 두 값 중 최대값 반환 */

#define PACK(size, alloc) ((size) | (alloc)) /* 크기와 할당 비트를 워드로 패킹 */

#define GET(p) (*(unsigned int *)(p))              /* 주소에서 워드 읽기 */
#define PUT(p, val) (*(unsigned int *)(p) = (val)) /* 주소에 워드 쓰기 */

#define GET_SIZE(p) (GET(p) & ~0x7) /* 주소 p에서 크기 필드를 읽음 */
#define GET_ALLOC(p) (GET(p) & 0x1) /* 주소 p에서 할당 필드를 읽음 */

#define HDRP(bp) ((char *)(bp)-WSIZE)                        /* 블록의 헤더 주소 계산 */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) /* 블록의 푸터 주소 계산 */

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))       /* 다음 블록의 주소 계산 */
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(HDRP(bp) - WSIZE)) /* 이전 블록의 주소 계산 */

/* explicit */
#define PRED(bp) ((char *)bp)           /* 블록의 pred 주소 계산 */
#define SUCC(bp) ((char *)(bp) + WSIZE) /* 블록의 succ 주소 계산 */

#define GET_PRED(bp) (*(void **)(bp))                   /* 이전 가용 블록의 주소 */
#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) /* 다음 가용 블록의 주소 */

/* function prototype */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *first_fit(size_t asize);
static void place(void *bp, size_t asize);

static void splice_free_block(void *bp); /* 가용 리스트에서 제거 */
static void add_free_block(void *bp);    /* 가용 리스트에 추가 */

/* global variable*/
char *free_listp; // 프롤로그 블록을 가리키는 포인터

/**
 * 블록에 저장할 정보: header, footer, pred, succ
 * → 최소 블록 크기 == 4 * WSIZE
 */

/**
 * @brief malloc 패키지 초기화 함수
 *
 * @return int 초기화 성공 시 0 반환, 실패 시 -1 반환
 */
int mm_init(void)
{
    if ((free_listp = mem_sbrk(8 * WSIZE)) == (void *)-1)
        return -1;

    PUT(free_listp, 0);                              /* 정렬 패딩 */
    PUT(free_listp + 1 * WSIZE, PACK(DSIZE, 1));     /* 프롤로그 header */
    PUT(free_listp + 2 * WSIZE, PACK(DSIZE, 1));     /* 프롤로그 footer */
    PUT(free_listp + 3 * WSIZE, PACK(4 * WSIZE, 0)); /* first free block header */
    PUT(free_listp + 4 * WSIZE, NULL);               /* first free block pred */
    PUT(free_listp + 5 * WSIZE, NULL);               /* first free block succ */
    PUT(free_listp + 6 * WSIZE, PACK(4 * WSIZE, 0)); /* first free block footer */
    PUT(free_listp + 7 * WSIZE, PACK(0, 1));         /* 에필로그 블록 */

    free_listp += 4 * WSIZE;

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/**
 * @brief 메모리를 할당하는 함수
 *
 * @param size 할당하려는 메모리 크기
 * @return void*  할당된 메모리 블록의 포인터. 할당에 실패하면 NULL 반환
 */
void *mm_malloc(size_t size)
{
    size_t adjusted_size; // 정렬을 위해 조정된 메모리 크기
    size_t extend_size;   // 힙을 확장할 크기
    char *bp;             // 할당된 블록의 포인터

    /* 요청 크기가 0인 경우 NULL 반환 */
    if (size == 0)
        return NULL;

    /* 할당할 메모리 크기를 DSIZE의 배수로 정렬 */
    if (size <= DSIZE)
        adjusted_size = 2 * DSIZE;
    else
        adjusted_size = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    /* 할당 가능한 블록 탐색 후 배치 */
    if ((bp = first_fit(adjusted_size)) != NULL)
    {
        place(bp, adjusted_size);
        return bp;
    }

    /* 할당 가능한 블록이 존재하지 않는 경우 힙 확장 후 배치 */
    extend_size = MAX(adjusted_size, CHUNKSIZE);
    if ((bp = extend_heap(extend_size / WSIZE)) != NULL)
    {
        place(bp, adjusted_size);
        return bp;
    }

    return NULL;
}

/**
 * @brief 메모리를 해제하는 함수
 *
 * @param bp 해제할 메모리 블록의 포인터
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // 해제할 블록의 크기

    /* header, footer 설정 */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    /* 가용 리스트에 추가 - pred, succ 설정 */
    add_free_block(bp);

    coalesce(bp);
}

/**
 * @brief 메모리 블록의 크기를 재할당하는 함수
 *
 * @param ptr 크기를 재할당할 메모리 블록의 포인터
 * @param size 재할당할 크기
 * @return void* 재할당된 메모리 블록의 포인터. 할당에 실패하면 NULL 반환
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr; // 기존 블록 포인터
    void *newptr;       // 새롭게 재할당한 블록 포인터
    size_t copySize;    // 복사할 데이터의 크기

    newptr = mm_malloc(size);

    /* 할당 불가할 시 NULL 리턴 */
    if (newptr == NULL)
        return NULL;

    copySize = GET_SIZE(HDRP(ptr));

    /* 요청된 크기가 기존 블록의 크기보다 작은 경우, 복사할 크기를 요청된 크기로 설정 */
    if (size < copySize)
        copySize = size;

    /* 기존 블록의 데이터를 새로운 블록으로 복사 후 해제*/
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);

    return newptr;
}

/**
 * @brief 주어진 워드 수만큼 힙을 확장하고, 새로 생성된 블록을 반환하는 함수
 *
 * @param words 힙에 추가할 워드의 개수
 * @return void* 새로 확장된 힙 영역에서의 블록 포인터. 확장에 실패하면 NULL 반환
 */
static void *extend_heap(size_t words)
{
    char *bp;    // 새로 확장된 힙 영역에서의 블록 포인터
    size_t size; // 힙을 확장할 바이트 크기

    /* 확장할 크기를 워드 단위에서 바이트 단위로 변환 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    /* brk 증가 */
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* header, footer, 에필로그 블록 설정 */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    /* 가용 리스트에 추가 - pred, succ 설정 */
    add_free_block(bp);

    /* 이전 블록이 free 상태라면, 새로운 블록과 이전 블록을 병합 */
    return coalesce(bp);
}

/** TODO:
 * @brief 현재 블록 앞뒤에 있는 free 블록을 연결하는 함수
 *
 * @param bp 현재 블록 포인터
 * @return void* 연결 작업 후 생성된 블록 포인터
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 할당 여부
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록의 크기

    /* Case 1 - 이전 블록과 다음 블록 모두 할당됨 */
    if (prev_alloc && next_alloc)
    {
        return bp;
    }
    /* Case 2 - 다음 블록만 free */
    else if (prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* Case 3 - 이전 블록만 free */
    else if (!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* Case 4 - 이전 블록과 다음 블록 모두 free */
    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/** TODO:
 * @brief asize만큼 할당할 수 있는 첫 번째 free 블록을 찾는 함수
 *
 * @param asize 할당하려는 크기
 * @return void* asize 크기를 할당할 수 있는 첫 번째 free 블록의 포인터. 적합한 블록을 찾지 못하면 NULL 반환
 */
static void *first_fit(size_t asize)
{
    void *bp;
    /* 가용 연결 리스트 순회하며 asize 크기를 할당할 수 있는 첫 번째 free 블록 탐색 */
    for (bp = free_listp; GET_SUCC(bp) != NULL; bp = GET_SUCC(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
        {
            return bp;
        }
    }
    /* 적합한 블록을 찾지 못한 경우 NULL 반환 */
    return NULL;
}

/**
 * @brief 주어진 블록에 asize 크기를 할당하는 함수
 *
 * @param bp 할당할 블록의 포인터
 * @param asize 할당할 크기
 */
static void place(void *bp, size_t asize)
{
    size_t current_size = GET_SIZE(HDRP(bp)); /* 현재 블록의 크기 */

    /* 분할이 필요한 경우 - 남은 블록의 크기가 2 * DSIZE보다 큼*/
    if ((current_size - asize) >= 2 * DSIZE)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        splice_free_block(bp);

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(current_size - asize, 0));
        PUT(FTRP(bp), PACK(current_size - asize, 0));
        add_free_block(bp);
    }
    /* 분할이 필요하지 않은 경우 - 남은 블록의 크기가 2 * DSIZE보다 작음 */
    else
    {
        PUT(HDRP(bp), PACK(current_size, 1));
        PUT(FTRP(bp), PACK(current_size, 1));
        splice_free_block(bp);
    }
}

/**
 * @brief 가용 리스트에서 블록을 제거하는 함수
 *
 * @param bp 가용 리스트에서 제거할 블록의 포인터
 */
static void splice_free_block(void *bp)
{
    char *pred = GET_PRED(bp); // 제거할 블록의 이전 가용 블록의 포인터
    char *succ = GET_SUCC(bp); // 제거할 블록의 다음 가용 블록의 포인터

    /* 이전 가용 블록이 NULL이 아닌 경우 다음 블록을 succ로 연결 */
    if (pred != NULL)
        PUT(SUCC(pred), succ);

    /* 다음 가용 블록이 NULL이 아닌 경우 이전 블록을 pred로 연결 */
    if (succ != NULL)
        PUT(PRED(succ), pred);
}

/**
 * @brief 가용 리스트에 블록을 추가하는 함수
 *
 * @param bp 가용 리스트에 추가할 블록의 포인터
 */
static void add_free_block(void *bp)
{
    char *curr = free_listp;     // 현재 블록의 포인터
    char *next = GET_SUCC(curr); // 다음 블록의 포인터

    /* 가용 리스트를 순회하며 적절한 위치 탐색 */
    while (next != NULL)
    {
        /* 새로운 블록이 현재 블록과 다음 블록 사이에 위치해야 하는 경우 리스트에 삽입 */
        if (curr < bp && bp < next)
        {
            PUT(SUCC(curr), bp);
            PUT(SUCC(bp), next);
            PUT(PRED(next), bp);
            PUT(PRED(bp), curr);
            return;
        }
        curr = next;
        next = GET_SUCC(next);
    }

    /* 새로운 블록이 가용 리스트 마지막에 추가되는 경우 */
    PUT(SUCC(curr), bp);
    PUT(PRED(bp), curr);
    PUT(SUCC(bp), NULL);
}