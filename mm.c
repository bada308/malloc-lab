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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // size_t의 크기를 ALIGNMENT의 배수로 올림한 결과

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *first_fit(size_t asize);
static void *next_fit(size_t asize);
static void place(void *bp, size_t asize);

char *heap_listp; // 프롤로그 블록을 가리키는 포인터
char *rover;      // next fit 사용 시 이전에 할당된 블록을 가리키는 포인터

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    {
        return -1;
    }

    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + 1 * WSIZE, PACK(DSIZE, 1)); /* 프롤로그 header */
    PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1)); /* 프롤로그 footer */
    PUT(heap_listp + 3 * WSIZE, PACK(0, 1));     /* 에필로그 블록 */

    heap_listp += 2 * WSIZE;
    rover = heap_listp; // FIXME: next fit 사용 시에만 유효함

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t adjusted_size;
    size_t extend_size;
    char *bp;

    if (size == 0)
    {
        return NULL;
    }

    if (size <= DSIZE)
    {
        adjusted_size = 2 * DSIZE;
    }
    else
    {
        adjusted_size = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = next_fit(adjusted_size)) != NULL)
    {
        place(bp, adjusted_size);
        return bp;
    }

    extend_size = MAX(adjusted_size, CHUNKSIZE);
    if ((bp = extend_heap(extend_size / WSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, adjusted_size);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); /* 해제할 블록의 크기 */

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr; /* 기존 블록 포인터 */
    void *newptr;       /* 새롭게 재할당한 블록 포인터*/
    size_t copySize;    /* 복사할 데이터의 크기 */

    newptr = mm_malloc(size);
    if (newptr == NULL) /* 할당 불가할 시 NULL 리턴 */
        return NULL;

    copySize = GET_SIZE(HDRP(ptr));

    if (size < copySize)
        copySize = size;
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

    // 확장할 크기를 워드 단위에서 바이트 단위로 변환
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // 힙을 확장하고, 새로운 블록의 포인터를 얻음
    if ((long)(bp = mem_sbrk(size)) == -1)
    {
        return NULL;
    }

    // 새로운 블록의 헤더와 푸터 설정 후 에필로그 블록 설정
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 이전 블록이 free 상태라면, 새로운 블록과 이전 블록을 병합
    return coalesce(bp);
}

/**
 * @brief 현재 블록 앞뒤에 있는 free 블록을 연결하는 함수
 *
 * @param bp 현재 블록 포인터
 * @return void* 연결 작업 후 생성된 블록 포인터
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 1 - 이전 블록과 다음 블록 모두 할당됨 */
    if (prev_alloc && next_alloc)
    {
        return bp;
    }
    /* Case 2 - 다음 블록만 free */
    else if (prev_alloc && !next_alloc)
    {
        if (rover == NEXT_BLKP(bp))
        {
            rover = bp;
        }
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* Case 3 - 이전 블록만 free */
    else if (!prev_alloc && next_alloc)
    {
        if (rover == bp)
        {
            rover = PREV_BLKP(bp);
        }
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    /* Case 4 - 이전 블록과 다음 블록 모두 free */
    else
    {
        if (rover == bp || rover == NEXT_BLKP(bp))
        {
            rover = PREV_BLKP(bp);
        }
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/**
 * @brief asize만큼 할당할 수 있는 첫 번째 free 블록을 찾는 함수
 *
 * @param asize 할당하려는 크기
 * @return void* asize 크기를 할당할 수 있는 첫 번째 free 블록의 포인터. 적합한 블록을 찾지 못하면 NULL 반환
 */
static void *first_fit(size_t asize)
{
    void *bp;
    /* 힙 리스트 순회하며 asize 크기를 할당할 수 있는 첫 번째 free 블록 탐색 */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
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
 * @brief
 *
 * @param asize
 * @return void*
 */
static void *next_fit(size_t asize)
{
    void *bp;
    void *old_rover = rover;

    for (bp = rover; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
        {
            rover = NEXT_BLKP(bp);
            return bp;
        }
    }

    for (bp = heap_listp; bp < old_rover; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
        {
            rover = NEXT_BLKP(bp);
            return bp;
        }
    }
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

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(current_size - asize, 0));
        PUT(FTRP(bp), PACK(current_size - asize, 0));
    }
    /* 분할이 필요하지 않은 경우 - 남은 블록의 크기가 2 * DSIZE보다 작음 */
    else
    {
        PUT(HDRP(bp), PACK(current_size, 1));
        PUT(FTRP(bp), PACK(current_size, 1));
    }
}