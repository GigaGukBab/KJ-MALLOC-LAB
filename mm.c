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
#include <stddef.h>
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
    "giaggookbob",
    /* First member's full name */
    "Jinwoo Han",
    /* First member's email address */
    "qew8502@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
// #define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
// #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0b1111)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// >> helper functions prototypes
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
char *_fisrt_fit(size_t asize);
char *_next_fit(size_t asize);
char *_best_fit(size_t asize);
static void *find_fit(size_t asize);
void _fisrt_fit_place(void *bp, size_t asize);
void _next_fit_place(void *bp, size_t asize);
void _best_fit_place(void *bp, size_t asize);
static void place(void *bp, size_t asize);
void printblock(char *bp);

static char *heap_listp; // NOTE: This always points to prologue block
static char *next_p;

// >> Basic constants and macros
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

void printblock(char *bp)
{
  size_t hsize = GET_SIZE(HDRP(bp));
  size_t fsize = GET_SIZE(FTRP(bp));
  int halloc = GET_ALLOC(HDRP(bp));
  int falloc = GET_ALLOC(FTRP(bp));

  printf("Block Info at %p:\n", bp);
  printf("  Header: alloc = %d, size = %zu\n", halloc, hsize);
  printf("  Footer: alloc = %d, size = %zu\n", falloc, fsize);
}

static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc)
  { // Case 1: No coalescing
    return bp;
  }
  else if (prev_alloc && !next_alloc)
  { // Case 2: Coalesce with next
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  else if (!prev_alloc && next_alloc)
  { // Case 3: Coalesce with prev
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }
  else
  { // Case 4: Coalesce with both
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  if ((next_p > (char *)bp) && (((char *)bp + size) > next_p))
  {
    next_p = bp;
  }

  return bp;
}

/*
  extend_heap function calls when
    - heap is initalized
    - mm_malloc still not found fit block
 */
static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1)
  {
    return NULL;
  }

  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

  /* Coalesce if the previous block was free */
  return coalesce(bp);
}

// mm_init - initialize the malloc package.
int mm_init(void)
{
  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
  {
    return -1;
  }

  PUT(heap_listp, 0);                            /* Alignment padding */
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue block header*/
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue block footer*/
  PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue block header*/
  heap_listp += (2 * WSIZE);
  next_p = NULL;

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
  {
    return -1;
  }
  return 0;
}

// >> Memory allocation methods
char *_fisrt_fit(size_t asize)
{
  char *curr = NEXT_BLKP(heap_listp);

  while (GET_SIZE(HDRP(curr)) > 0)
  {
    if ((GET_ALLOC(HDRP(curr)) == 0) && (GET_SIZE(HDRP(curr)) >= asize))
    {
      return curr;
    }
    else
    {
      curr = NEXT_BLKP(curr);
    }
  }

  return NULL;
}
char *_next_fit(size_t asize)
{
  if (next_p == NULL)
  {
    // allocating first time
    char *curr = NEXT_BLKP(heap_listp);
    while (GET_SIZE(HDRP(curr)) > 0)
    {
      if ((GET_ALLOC(HDRP(curr)) == 0) &&
          (GET_SIZE(HDRP(curr)) >= asize))
      {
        return curr;
      }
      else
      {
        curr = NEXT_BLKP(curr);
      }
    }

    return NULL;
  }
  else
  {
    // not a first time
    char *curr = next_p;
    while (GET_SIZE(HDRP(curr)) > 0)
    {
      if ((GET_ALLOC(HDRP(curr)) == 0) &&
          (GET_SIZE(HDRP(curr)) >= asize))
      {
        return curr;
      }
      else
      {
        curr = NEXT_BLKP(curr);
      }
    }

    // 처음부터 다시 순회 (다시 돌아올때까지)
    curr = NEXT_BLKP(heap_listp);
    while (curr != next_p)
    {
      if ((GET_ALLOC(HDRP(curr)) == 0) &&
          (GET_SIZE(HDRP(curr)) >= asize))
      {
        return curr;
      }
      else
      {
        curr = NEXT_BLKP(curr);
      }
    }

    // printf("After find_fit :");
    // printblock(curr);
    return NULL;
  }
}
char *_best_fit(size_t asize)
{
  return NULL;
}

static void *find_fit(size_t asize)
{
  // return _fisrt_fit(asize);
  return _next_fit(asize);
  // return _best_fit(asize);
}

void _fisrt_fit_place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));

  // printf("Before place :");
  // printblock(bp);

  if (csize - asize < (2 * DSIZE))
  {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
  else
  {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));
  }

  // printf("After place :");
  // printblock(bp);
}
void _next_fit_place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));

  if (csize - asize < (2 * DSIZE))
  {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
  else
  {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(csize - asize, 0));
  }

  next_p = NEXT_BLKP(bp);
}
void _best_fit_place(void *bp, size_t asize)
{
}

static void place(void *bp, size_t asize)
{
  // _fisrt_fit_place(bp, asize);
  _next_fit_place(bp, asize);
  // _best_fit_place(bp, asize);
}

// mm_malloc - Allocate a block by incrementing the brk pointer.
// Always allocate a block whose size is a multiple of the alignment.
void *mm_malloc(size_t size)
{
  size_t asize;      /* Adjusted block size */
  size_t extendsize; /* Amount to extend heap if no fit */
  char *bp;

  /* Ignore spurious requests */
  if (size == 0)
  {
    return NULL;
  }

  /* Adjust block size to include overhead and alignment requirements */
  if (size <= DSIZE)
  {
    asize = 2 * DSIZE;
  }
  else
  {
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }

  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL)
  {
    place(bp, asize);
    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
  {
    return NULL;
  }

  place(bp, asize);
  return bp;
}

// /*
//  * mm_malloc - Allocate a block by incrementing the brk pointer.
//  *     Always allocate a block whose size is a multiple of the alignment.
//  */
// void *mm_malloc(size_t size)
// {
//   int newsize = ALIGN(size + SIZE_T_SIZE);
//   void *p = mem_sbrk(newsize);
//   if (p == (void *)-1)
//     return NULL;
//   else
//   {
//     *(size_t *)p = size;
//     return (void *)((char *)p + SIZE_T_SIZE);
//   }
// }

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);
}

// /*
//  * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
//  */
// void *mm_realloc(void *ptr, size_t size)
// {
//   void *oldptr = ptr;
//   void *newptr;
//   size_t copySize;

//   newptr = mm_malloc(size);
//   if (newptr == NULL)
//     return NULL;
//   copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
//   if (size < copySize)
//     copySize = size;
//   memcpy(newptr, oldptr, copySize);
//   mm_free(oldptr);
//   return newptr;
// }

// 만약 메모리를 확장할 만큼 충분한 공간이 없으면, 원래의 블록은 변경되지 않으며 NULL을 반환합니다.
// memblock이 NULL이면 realloc은 malloc(size)처럼 작동하여 새 블록을 할당합니다.
// 만약 size가 0이면, memblock이 가리키는 블록이 해제되고, 반환값은 NULL입니다.
// 이 경우 memblock은 해제된 블록을 여전히 가리키게 됩니다.
void *mm_realloc(void *ptr, size_t size)
{
  void *oldptr = ptr;
  void *newptr;
  size_t copySize;

  if (ptr == NULL)
  {
    return mm_malloc(size);
  }

  if (size == 0)
  {
    mm_free(ptr);
    return NULL;
  }

  newptr = mm_malloc(size);
  if (newptr == NULL)
  {
    return NULL;
  }

  if (size <= DSIZE)
  {
    copySize = 2 * DSIZE;
  }
  else
  {
    copySize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }

  // 실제로 복사할 크기(copySize)가 요청한 size보다 클 경우, size로 잘라냅니다.
  // 이유: 내부 블록 크기 계산에는 padding 및 alignment를 고려해서,
  //       실제 payload보다 약간 더 크게 계산될 수 있습니다.
  //       하지만 memcpy는 정확히 유효한 데이터만 복사해야 하므로,
  //       copySize가 size를 초과할 경우 잘라주는 것이 안전합니다.
  /*
   예시:
   사용자 요청: size = 13바이트
   내부 계산: copySize = 8 * ((13 + 8 + 7) / 8) = 8 * 3 = 24
    → 실제로는 13바이트만 의미 있는 데이터인데,
       24바이트를 복사하면 불필요한 padding 영역까지 복사될 수 있음

   따라서, copySize = 13 으로 조정하여 안전하게 복사
  */
  if (size < copySize)
  {
    copySize = size;
  }
  memcpy(newptr, oldptr, copySize);
  mm_free(oldptr);
  return newptr;
}