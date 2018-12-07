/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
 #include <stdio.h>
 #include <stdlib.h>
 #include <unistd.h>
 #include <memory.h>
 #include "mm.h"
 #include "memlib.h"
 
 /*********************************************************
  * NOTE TO STUDENTS: Before you do anything else, please
  * provide your team information in the following struct.
  ********************************************************/
 team_t team = {
   /* Team name */
   "MEME DREAM CODE TEAN",
    "Vincent Liu",
   " vili1624@colorado.edu ",
    "Christian Sousa",
    "chso8299@colorado.edu"
 };
 
 /////////////////////////////////////////////////////////////////////////////
 // Constants and macros
 //
 // These correspond to the material in Figure 9.43 of the text
 // The macros have been turned into C++ inline functions to
 // make debugging code easier.
 //
 /////////////////////////////////////////////////////////////////////////////
 #define WSIZE       4       /* word size (bytes) */  
 #define DSIZE       8       /* doubleword size (bytes) */
 #define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
 #define OVERHEAD    8       /* overhead of header and footer (bytes) */
 #define MIN 24 // minimum block size
 
 static inline int MAX(int x, int y)
 {
     return x > y ? x : y;
 }
 
 //
 // Pack a size and allocated bit into a word
 // We mask of the "alloc" field to insure only
 // the lower bit is used
 //
 static inline uint32_t PACK(uint32_t size, int alloc)
 {
     return ((size) | (alloc & 0x1));
 }
 
 //
 // Read and write a word at address p
 //
 static inline uint32_t GET(void *p)
 { 
     return  *(uint32_t *)p;
 }
 
 static inline void PUT( void *p, uint32_t val)
 {
     *((uint32_t *)p) = val;
 }
 
 //
 // Read the size and allocated fields from address p
 //
 static inline uint32_t GET_SIZE(void *p)
 { 
     return GET(p) & ~0x7;
 }
 
 static inline int GET_ALLOC(void *p)
 {
     return GET(p) & 0x1;
 }
 
 //
 // Given block ptr bp, compute address of its header and footer
 //
 static inline void *HDRP(void *bp)
 {
     return ( (char *)bp) - WSIZE;
 }
 
 static inline void *FTRP(void *bp)
 {
     return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
 }
 
 //
 // Given block ptr bp, compute address of next and previous blocks
 //
 static inline void *NEXT_BLKP(void *bp)
 {
     return  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));
 }
 
 static inline void* PREV_BLKP(void *bp)
 {
     return  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));
 }

// given block pointer return adress of next/prev free block
 static inline void* NEXT_FB(void *ptr)
 {
     return (*(char**)((char*)(ptr)+DSIZE));
 }
 
 static inline void* PREV_FB(void *ptr)
 {
     return (*(char**)((char*)(ptr)));
 }

/*remove free block
case 1: there is only one thing in the list
case 2: block is at the top
case 3: block is at the end of the list
case 4: block is between two other blocks
all of this will become redundant if impiliment
circular lists, but we will see
*/
static void rmfb(void *bp)
{
    if(heap_listp==0)
    {
        // see if the list is empty
        return;
    }
    else if(NEXT_FB(bp)==NULL && PREV_FB(bp==NULL))
    {
        //case 1
        heap_listp=0;
    
    else if(NEXT_FB(bp)!=NULL && PREV_FB(bp)==NULL)
    {
        // case 2
        heap_listp= NEXT_FB(bp);
        PREV_FB(heap)=NULL;
    }
    else if(NEXT_FB(bp)==NULL && PREV_FB(bp)!=NULL)
    {
        //case 3
        NEXT_FB(PREV_FB(bp))=NULL;
    }
    else if(NEXT_FB(bp)!=NULL && PREV_FB(bp)!=NULL)
    {
        //bp->next->prev= bp->prev;
        PREV_FB(NEXT_FB(bp))=PREV_FB(bp);
        NEXT_FB(PREV_FB(bp))=NEXT_FB(bp);
    }
}
// to insert free blocks
/*
    either list is empty and you add a new one or 
    or its not and you append the front
*/
static void insfb(*void bp)
{
    if(heap_listp==NULL)
    {
        NEXT_FB(bp)=NULL;
        PREV_FB(bp)= NULL;
        heap_listp=bp;
    }
    PREV_FB(bp)=NULL;
    prev(heap_listp)=bp;
    NEXT_FB(bp)=heap_listp;
    heap_listp=bp;
}
 /////////////////////////////////////////////////////////////////////////////
 //
 // Global Variables
 //
 
 static char *heap_listp;  /* pointer to first block */  
 
 //
 // function prototypes for internal helper routines
 //
 static void *extend_heap(uint32_t words);
 static void place(void *bp, uint32_t asize);
 static void *find_fit(uint32_t asize);
 static void *coalesce(void *bp);
 static void printblock(void *bp); 
 static void checkblock(void *bp);
 
 // mm_init: Before calling mm_malloc mm_realloc or mm_free, the 
 // application program (i.e., the trace-driven driver program that 
 // you will use to evaluate your implementation) calls mm_init 
 // to perform any necessary initializations, such as allocating 
 // the initial heap area. The return value should be -1 if there 
 // was a problem in performing the initialization, 0 otherwise.
 
 int mm_init(void) 
 {
     if((heap_listp = mem_sbrk(4*WSIZE)) == (void*) -1)
         return -1;
     /* padding */
     PUT(heap_listp, 0);
     /* prologue blocks */
     PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
     PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
     /* epiogue block */
     PUT(heap_listp + (3*WSIZE), PACK(0,1));
     /* start it out in the middle of the prologue block */
     heap_listp += DSIZE;
     /* add 1026 more word size blocks */
     if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
         return -1;
     return 0;
 }
 //
 // extend_heap - Extend heap with free block and return its block pointer
 //
 static void *extend_heap(uint32_t words) 
 {
     char *bp;
     size_t size;
     /* align the size to be will added */
     size = (words%2) ? (words+1) * WSIZE : words * WSIZE;
     /* increase the avaiable heap by words blocks */
     if((long)(bp = mem_sbrk(size)) == -1)
         return NULL;
     /* making the header and footer */
     PUT(HDRP(bp), PACK(size, 0));
     PUT(FTRP(bp), PACK(size, 0));
 
     /* making a epilogue block */
     PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));
     // this is the new epilog header
     return coalesce(bp);
 }
 
 
 //
 // Practice problem 9.8
 //
 // find_fit - Find a fit for a block with asize bytes 
 //
 static void *find_fit(uint32_t asize)
 {
     /* First-fit search */
     void *bp;
     
     for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
     {
         if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
         {
             return bp;
         }
     }
     return NULL;
 //#endif
 }
 
 // mm_free: The mm_free routine frees the block pointed to by ptr. 
 // It returns nothing. This routine is only guaranteed to work 
 // when the passed pointer (ptr) was returned by an earlier call 
 // to mm_malloc or mm_realloc and has not yet been freed.
 
 void mm_free(void *bp)
 {
     size_t size = GET_SIZE(HDRP(bp));
     
     PUT(HDRP(bp), PACK(size, 0));
     PUT(FTRP(bp), PACK(size, 0));
     coalesce(bp);
 }
 
 //
 // coalesce - boundary tag coalescing. Return ptr to coalesced block
 //
 static void *coalesce(void *bp) 
 {
     size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
     size_t size = GET_SIZE(HDRP(bp));
     /* both the left and right are not free */
     if(prev_alloc && next_alloc)
         return bp;
     /* the right is free */
     else if(prev_alloc && !next_alloc)
     {
         size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
         PUT(HDRP(bp), PACK(size, 0));
         PUT(FTRP(bp), PACK(size, 0));
     }
     /* the left is free */
     else if(!prev_alloc && next_alloc)
     {
         size += GET_SIZE(HDRP(PREV_BLKP(bp)));
         PUT(FTRP(bp), PACK(size, 0));
         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
         bp = PREV_BLKP(bp);
     }
     /* both left and right are free */
     else
     {
         size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
         PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
         bp = PREV_BLKP(bp);
     }
     return bp;
 }
 
 // mm_malloc: The mm_malloc routine returns a pointer to an allocated 
 // block payload of at least size bytes. The entire allocated block 
 // should lie within the heap region and should not overlap with any
 // other allocated chunk. We will comparing your implementation to the 
 // version of malloc supplied in the standard C library (libc). Since 
 // the libcmalloc always returns payload pointers that are aligned to 8 
 // bytes, your malloc implementation should do likewise and always 
 // return 8-byte aligned pointers.
 
 void *mm_malloc(uint32_t size) 
 {
     size_t asize;
     size_t extendsize;
     char* bp;
     
     if(size == 0)
         return NULL;
     
     if(size <= DSIZE)
         asize = 2*DSIZE;
     else
         asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
     
     if((bp = find_fit(asize)) != NULL)
     {
         place(bp, asize);
         return bp;
     }
     
     extendsize = MAX(asize, CHUNKSIZE);
     if((bp = extend_heap(extendsize/WSIZE)) == NULL)
         return NULL;
     
     place(bp, asize);
     return bp;
 } 
 
 //
 //
 // Practice problem 9.9
 //
 // place - Place block of asize bytes at start of free block bp 
 //         and split if remainder would be at least minimum block size
 //
 static void place(void *bp, uint32_t asize)
 {
     size_t csize = GET_SIZE(HDRP(bp));
     
     if((csize - asize) >= (2*DSIZE))
     {
         PUT(HDRP(bp), PACK(asize, 1));
         PUT(FTRP(bp), PACK(asize, 1));
         rmfb(bp);
         bp = NEXT_BLKP(bp);
         PUT(HDRP(bp), PACK(csize - asize, 0));
         PUT(FTRP(bp), PACK(csize - asize, 0));
         coalesce(bp);
     }
     else
     {
         PUT(HDRP(bp), PACK(csize, 1));
         PUT(FTRP(bp), PACK(csize, 1));
         rmfb(bp);
     }
 }
 
 // mm_realloc -- implemented for you
 
 // mm_realloc: The mm_realloc routine returns a pointer to an allocated 
 //             region of at least size bytes with the following constraints.
 
 // if ptr is NULL, the call is equivalent to mm_malloc(size);
 
 // if size is equal to zero, the call is equivalent to mm_free(ptr);
 
 /* if ptr is not NULL, it must have been returned by an earlier call to 
         mm_malloc or mm_realloc. The call tomm_realloc changes the size 
         of the memory block pointed to by ptr (the {\em old block}) to 
         size bytes and returns the address of the new block. Notice that 
         the address of the new block might be the same as the old block, 
         or it might be different, depending on your implementation, the 
         amount of internal fragmentation in the old block, and the size 
         of the realloc request. The contents of the new block are the same 
         as those of the old ptr block, up to the minimum of the old and new sizes. 
         Everything else is uninitialized. For example, if the old block is 8 bytes 
         and the new block is 12 bytes, then the first 8 bytes of the new block are 
         identical to the first 8 bytes of the old block and the last 4 bytes are 
         uninitialized. Similarly, if the old block is 8 bytes and the new block 
         is 4 bytes, then the contents of the new block are identical to the f
         irst 4 bytes of the old block. 
 */
 
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
 
 //
 // mm_checkheap - Check the heap for consistency 
 //
 void mm_checkheap(int verbose) 
 {
   //
   // This provided implementation assumes you're using the structure
   // of the sample solution in the text. If not, omit this code
   // and provide your own mm_checkheap
   //
     void *bp = heap_listp;
   
     if(verbose)
     {
         printf("Heap (%p):\n", heap_listp);
     }
 
     if((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
     {
         printf("Bad prologue header\n");
     }
     checkblock(heap_listp);
 
     for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
     {
         if (verbose)
         {
           printblock(bp);
         }
         checkblock(bp);
     }
      
     if(verbose)
     {
         printblock(bp);
     }
 
     if((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
     {
         printf("Bad epilogue header\n");
     }
 }
 
 static void printblock(void *bp) 
 {
     uint32_t hsize, halloc, fsize, falloc;
 
     hsize = GET_SIZE(HDRP(bp));
     halloc = GET_ALLOC(HDRP(bp));  
     fsize = GET_SIZE(FTRP(bp));
     falloc = GET_ALLOC(FTRP(bp));  
     
     if(hsize == 0)
     {
         printf("%p: EOL\n", bp);
         return;
     }
 
     printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, (int) hsize, (halloc ? 'a' : 'f'), (int) fsize, (falloc ? 'a' : 'f')); 
 }
 
 static void checkblock(void *bp) 
 {
     if((uintptr_t)bp % 8)
     {
         printf("Error: %p is not doubleword aligned\n", bp);
     }
 
     if(GET(HDRP(bp)) != GET(FTRP(bp)))
     {
         printf("Error: header does not match footer\n");
     }
 }

 