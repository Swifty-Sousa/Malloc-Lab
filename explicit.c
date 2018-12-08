#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory.h>
#include "mm.h"
#include "memlib.h"

team_t team = {
  "The BOI",
  "Vincent Liu",
  "vili1624@colorado.edu",
  "Christian Sousa",
  "chso8299@colorado.edu"
};

#define WSIZE       4       
#define DSIZE       8       
#define CHUNKSIZE  (1<<12)  
#define OVERHEAD    8
#define MINIMUM     24

static inline int MAX(int x, int y)
{
  return x > y ? x : y;
}

static inline uint32_t PACK(uint32_t size, int alloc)
{
  return ((size) | (alloc & 0x1));
}

static inline uint32_t GET(void *p)
{ 
  return  *(uint32_t *)p;
}

static inline void PUT( void *p, uint32_t val)
{
  *((uint32_t *)p) = val;
}

static inline uint32_t GET_SIZE(void *p)
{ 
  return GET(p) & ~0x7;
}

static inline int GET_ALLOC(void *p)
{
  return GET(p) & 0x1;
}

static inline void *HDRP(void *bp)
{
  return ( (char *)bp) - WSIZE;
}

static inline void *FTRP(void *bp)
{
  return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

static inline void *NEXT_BLKP(void *bp)
{
  return  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));
}

static inline void* PREV_BLKP(void *bp)
{
  return  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));
}

typedef struct freelist
{
  struct freelist *prev;
  struct freelist *next;
}freelist;

static void *start;
static freelist *firstfree;

static void *extend_heap(uint32_t words);
static void insert_to_free(freelist *bp);
static void remove_from_free(freelist* bp);
static void *find_fit(uint32_t asize);
static void place(void *bp, uint32_t asize);
static void *coalesce(void *bp);
static void ph(void);
static void pb(void *bp);
static void pf(void);
int mallc = 0;
int freec = 0;

int mm_init(void)
{
  firstfree = NULL;

  if((start = mem_sbrk(4*WSIZE)) == (void*) -1)
    return -1;
    
  PUT(start, 0);
  PUT(start + (WSIZE), PACK(DSIZE, 1));
  PUT(start + (2*WSIZE), PACK(DSIZE, 1));
  PUT(start + (3*WSIZE), PACK(0,1));
  start += (2*WSIZE);
    
  if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
    return -1;
    
  return 0;
}

static void *extend_heap(uint32_t words) 
{
  void *bp;
  uint32_t size;
  size = (words%2) ? (words+1) * WSIZE : words * WSIZE;
  if((bp = mem_sbrk(size)) == (void*) -1)
      return NULL;
    
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

  return coalesce(bp);
}

void *mm_malloc(uint32_t size)
{
  uint32_t asize;
  uint32_t extendsize;
  void *bp;

  if(size == 0)
  {
    return NULL;
  }

  if(size <= DSIZE)
  {
    size = DSIZE;
  }
  else if((size%DSIZE) != 0)
  {
    uint32_t time = size/DSIZE;
    size = (time + 1) * DSIZE;
  }

  asize = size + DSIZE;

  if((bp = find_fit(asize)) != NULL)
  {
    place(bp, asize);
    mallc += 1;
    return bp;
  }

  extendsize = MAX(asize, CHUNKSIZE);
  if((bp = extend_heap(extendsize/WSIZE)) == NULL)
    return NULL;

  place(bp, asize);
    mallc += 1;
  return bp;
}

static void *find_fit(uint32_t asize)
{
  freelist* bp;

  for(bp = firstfree; bp != NULL; bp = bp->next)
  {
    if(!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize))
    {
      return bp;
    }
  }
  return NULL;
}

static void place(void *bp, uint32_t asize)
{
  uint32_t csize = GET_SIZE(HDRP(bp));

  if((csize - asize) >= MINIMUM)
  {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    remove_from_free((freelist*)bp);

    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    insert_to_free((freelist*)bp);
  }
  else
  {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
    remove_from_free((freelist*)bp);
  }
}

static void remove_from_free(freelist* bp)
{
    if(GET_SIZE(HDRP(bp)) == 0)
    {
        PUT(HDRP(bp), PACK(0,1));
        return;
    }
  if(bp->next == NULL && bp->prev == NULL)
  {
    firstfree = NULL;
  }
  else if(bp->prev == NULL && bp->next != NULL)
  {
    firstfree = bp->next;
    firstfree->prev = NULL;
  }
  else if(bp->prev != NULL && bp->next == NULL)
  {
    bp->prev->next = NULL;
  }
  else if(bp->prev != NULL && bp->next != NULL)
  {
    bp->prev->next = bp->next;
    bp->next->prev = bp->prev;
    bp->prev = NULL;
    bp->next = NULL;
  }
}

static void insert_to_free(freelist *bp)
{
    if(GET_ALLOC(HDRP(bp)))
    {
        return;
    }
  if(firstfree == NULL)
  {
    firstfree = bp;
    bp->next = NULL;
    bp->prev = NULL;
  }
  else if(firstfree != NULL)
  {
    bp->prev = firstfree->prev;
    bp->next = firstfree;
    firstfree->prev = bp;
    firstfree = bp;
  }
}

void mm_free(void *bp)
{
  if(bp == 0)
    return;

  uint32_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));

  coalesce(bp);
}

static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if(prev_alloc && next_alloc)
  {
    insert_to_free((freelist*)bp);
    return bp;
  }

  else if(prev_alloc && !next_alloc)
  {
    size = size + GET_SIZE(HDRP(NEXT_BLKP(bp)));
    remove_from_free((freelist*)NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    insert_to_free((freelist*)bp);
    return bp;
  }
  else if(!prev_alloc && next_alloc)
  {
    size = size + GET_SIZE(HDRP(PREV_BLKP(bp)));
    bp = PREV_BLKP(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    return bp;
  }
  else if(!prev_alloc && !next_alloc)
  {
    size = size + GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    remove_from_free((freelist*)NEXT_BLKP(bp));
    remove_from_free((freelist*)PREV_BLKP(bp));

    bp = PREV_BLKP(bp);
    insert_to_free((freelist*)bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    return bp;
  }
  printf("something bad happened!!!");
  return bp;
}

void *mm_realloc(void *ptr, uint32_t size)
{
    void *newp;
    uint32_t copySize;

    newp = mm_malloc(size);
    if (newp == NULL)
    {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
    {
        copySize = size;
    }
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

static void ph(void)
{
    printf("\n");
    void *bp;
    
    for(bp = start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        uint32_t hsize, halloc, fsize, falloc;

        hsize = GET_SIZE(HDRP(bp));
        halloc = GET_ALLOC(HDRP(bp));  
        fsize = GET_SIZE(FTRP(bp));
        falloc = GET_ALLOC(FTRP(bp)); 

        if(hsize == 0)
        {
            printf("%p: EOL\n", bp);
        }

        printf("%p: header: [%d:%c] (next [%p] prev [%p]) footer: [%d:%c]\n", bp, (int) hsize, (halloc ? 'a' : 'f'), ((freelist*)bp)->next, ((freelist*)bp)->prev,(int) fsize, (falloc ? 'a' : 'f')); 
    }
    if(GET_SIZE(HDRP(bp)) == 0)
    {
        uint32_t hsize, halloc, fsize, falloc;

        hsize = GET_SIZE(HDRP(bp));
        halloc = GET_ALLOC(HDRP(bp));
        fsize = GET_SIZE(FTRP(bp));
        falloc = GET_ALLOC(FTRP(bp));
        
        printf("last block %p: header: [%d:%c] (next [%p] prev [%p]) footer: [%d:%c]\n", bp, (int) hsize, (halloc ? 'a' : 'f'), ((freelist*)bp)->next, ((freelist*)bp)->prev,(int) fsize, (falloc ? 'a' : 'f'));
    }
}

static void pf(void)
{
    freelist* bp = firstfree;
    do
    {
        uint32_t hsize, halloc, fsize, falloc;

        hsize = GET_SIZE(HDRP(bp));
        halloc = GET_ALLOC(HDRP(bp));  
        fsize = GET_SIZE(FTRP(bp));
        falloc = GET_ALLOC(FTRP(bp));
        printf("%p: header: [%d:%c] (next [%p] prev [%p]) footer: [%d:%c]\n", bp, (int) hsize, (halloc ? 'a' : 'f'), ((freelist*)bp)->next, ((freelist*)bp)->prev,(int) fsize, (falloc ? 'a' : 'f'));
        bp = bp->next;
    }
    while(bp != NULL);
}

static void pb(void *bp) 
{
    uint32_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    printf("\n");
    if(hsize == 0)
    {
        printf("%p: EOL\n", bp);
        printf("%p: header: [%d:%c] (next [%p] prev [%p]) footer: [%d:%c]\n", bp, (int) hsize, (halloc ? 'a' : 'f'), ((freelist*)bp)->next, ((freelist*)bp)->prev,(int) fsize, (falloc ? 'a' : 'f'));
        return;
    }

    printf("%p: header: [%d:%c] (next [%p] prev [%p]) footer: [%d:%c]\n", bp, (int) hsize, (halloc ? 'a' : 'f'), ((freelist*)bp)->next, ((freelist*)bp)->prev,(int) fsize, (falloc ? 'a' : 'f')); 
}
