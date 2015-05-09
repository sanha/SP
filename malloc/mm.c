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

team_t team = {
	/* Team name : Your student ID */
  	"2013-11415",
	  /* Your full name */
	  "Sanha Lee",
	  /* Your student ID */
	  "2013-11415",
	  /* leave blank */
	  "",
	  /* leave blank */
	  ""
};

/* DON'T MODIFY THIS VALUE AND LEAVE IT AS IT WAS */
static range_t **gl_ranges;

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN (size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* CSAPP Chapter9 830p */
/* Basic constants and macros */
#define WSIZE		4	// Word and header / footer size
#define DSIZE		8	// Double word size
#define CHUNKSIZE	(1<<12)	// Extend heap by yhis amount

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)		(*(unsigned int *)(p))
#define PUT(p, val)	(*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)	(GET (p) & ~0x7)
#define GET_ALLOC(p)	(GET (p) & 0x1)

/* Given block ptr bp, compute address of its header nad footer */
#define HDRP(bp)	((char *)(bp) - WSIZE)
#define FTRP(bp)	((char *)(bp) + GET_SIZE (HDRP (bp)) - DSIZE)

/* GIven block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)	((char *)(bp) + GET_SIZE (((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)	((char *)(bp) - GET_SIZE (((char *)(bp) - DSIZE)))

/* 
 * remove_range - manipulate range lists
 * DON'T MODIFY THIS FUNCTION AND LEAVE IT AS IT WAS
 */
static void remove_range(range_t **ranges, char *lo)
{
	range_t *p;
	range_t **prevpp = ranges;
  
	if (!ranges)
    		return;

  	for (p = *ranges;  p != NULL; p = p->next) {
    		if (p->lo == lo) {
      			*prevpp = p->next;
      			free(p);
    			  break;
   	 	}
   	 	prevpp = &(p->next);
  	}
}

static char *heap_listp;	// heap base pointer

/* function pre-definition */
static void *extend_heap (size_t words);
static void *coalesce (void *bp);
static void place (char *bp, size_t asize);
static void *find_fit (size_t asize);


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(range_t **ranges)
{
//	printf ("starting init\n");
//	printf ("heap_listp is %x\n", heap_listp);

	/* Create the initial empty heap */
  	if ((heap_listp = mem_sbrk (4*WSIZE)) == (void *) -1)
		return -1;
  	PUT (heap_listp, 0);				// Alignment padding
	PUT (heap_listp + (1*WSIZE), PACK (DSIZE, 1));	// Prologue header
	PUT (heap_listp + (2*WSIZE), PACK (DSIZE, 1));	// Prologue footer
	PUT (heap_listp + (3*WSIZE), PACK (0, 1));	// Epilogue header
	heap_listp += DSIZE;
//	printf ("heap_listp is %x\n", heap_listp);

  	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
  	if (extend_heap (CHUNKSIZE/WSIZE) == NULL)
		return -1;

  	/* DON't MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
  	gl_ranges = ranges;

  	return 0;
}

static void *extend_heap (size_t words){
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	
	if (size < DSIZE) size = DSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;

//	printf("extend_heap, size is %d\n",size);
//	printf("bp is %x\n", bp);
	
//	printf("GET_ALLOC bp is %d\n", GET_ALLOC (HDRP (bp)));
//	printf("GET_SIZE bp is %d\n", GET_SIZE (HDRP (bp)));
	
	/* Initialize free block header/footer and the epilogue header */
	PUT (HDRP (bp), PACK (size, 0));	// Free block header
	PUT (FTRP (bp), PACK (size, 0));	// Free block footer
	PUT (HDRP (NEXT_BLKP (bp)), PACK (0, 1));	// New epilogue header
       
//	printf("bp is %x\n", bp);
//	printf("GET_ALLOC bp is %d\n", GET_ALLOC (HDRP (bp)));
//	printf("GET_SIZE bp is %d\n", GET_SIZE (HDRP (bp)));

	/* Coalesce if the previous block was free */
	return coalesce (bp);
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void* mm_malloc(size_t size)
{
//	printf("Starting malloc. \n");
//	printf("Heap start at %x\n", heap_listp);
//	printf("Heap size is %d\n", mem_heapsize());

	size_t asize;			// Adjusted block size
	size_t extendsize;		// Amount to extend heap if no fit
	char *bp;

	/* Ignore spurious requests */
	if (size == 0) return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE) asize = 2*DSIZE;
	else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

//	printf ("asize is %d\n", asize);

	/* Search the free list for a fit */
	if ((bp = find_fit (asize)) != NULL) {
		place (bp, asize);
		return bp;
	}
	
	/* No fit found, Get more memory and place the block */
	extendsize = MAX (asize, CHUNKSIZE);
	if ((bp = extend_heap (extendsize / WSIZE)) == NULL) return NULL;
	place (bp, asize);
	return bp;
}

static void *find_fit (size_t asize){
	char *p = heap_listp;
	char *end = mem_heap_hi();
	
//	printf("end is %x\n", end);

	while (1){
		if (p < end){
//			printf ("p is %x\n", p);
//			printf ("GET_ALLOC p is %d\n", GET_ALLOC (HDRP (p)));
//			printf ("GET_SIZE p is %d\n", GET_SIZE (HDRP (p)));
			if ((GET_ALLOC (HDRP (p)) || (GET_SIZE (HDRP (p)) < asize)))
				p = NEXT_BLKP (p);
			else return p;
		}
		else return NULL;
	}
}

static void place (char *bp, size_t asize){
	size_t bsize = GET_SIZE (HDRP (bp));
	size_t nsize = bsize - asize;
	
	if (nsize >= 2*DSIZE){
		PUT (HDRP (bp), PACK (asize, 1));
		PUT (FTRP (bp), PACK (asize, 1));
		bp = NEXT_BLKP (bp);
		PUT (HDRP (bp), PACK (nsize, 0));
		PUT (FTRP (bp), PACK (nsize, 0));
	}
	else {
		PUT (HDRP (bp), PACK (bsize, 1));
		PUT (FTRP (bp), PACK (bsize, 1));
	}
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
//	printf ("starting free\n");
	if (!GET_ALLOC (HDRP (ptr))) { //doubly-freed
	    printf ("You doubly freed memory.\n");
	    exit(-1);
	}
    
    	size_t size = GET_SIZE (HDRP (ptr));
	
	PUT (HDRP (ptr), PACK (size, 0));
	PUT (FTRP (ptr), PACK (size, 0));
	coalesce (ptr);

  	/* DON't MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
  	if (gl_ranges)
    		remove_range(gl_ranges, ptr);
}

static void *coalesce (void *bp){
//	printf ("coalesce\n");

	size_t prev_alloc = GET_ALLOC (FTRP (PREV_BLKP (bp)));
	size_t next_alloc = GET_ALLOC (HDRP (NEXT_BLKP (bp)));
	size_t size = GET_SIZE (HDRP (bp));

	if (prev_alloc && next_alloc) {
		return bp;	// case 1: prev & next block is allocated
	}

	else if (prev_alloc) {				// case 2: prev block is allocated only
		size += GET_SIZE (HDRP (NEXT_BLKP (bp)));
		PUT (HDRP (bp), PACK (size, 0));
		PUT (FTRP (bp), PACK (size, 0));
	}

	else if (next_alloc) {				// case 3: next block is allocated only
		size += GET_SIZE (HDRP (PREV_BLKP (bp)));
		PUT (FTRP (bp), PACK (size, 0));
		PUT (HDRP (PREV_BLKP (bp)), PACK (size, 0));
		bp = PREV_BLKP (bp);
	}

	else {						// case 4: nothing is allocated
		size += GET_SIZE (HDRP (PREV_BLKP (bp))) + GET_SIZE (FTRP (NEXT_BLKP (bp)));
		PUT (HDRP (PREV_BLKP (bp)), PACK (size, 0));
		PUT (FTRP (NEXT_BLKP (bp)), PACK (size, 0));
		bp = PREV_BLKP (bp);
	}

	return bp;
}


/*
 * mm_realloc - empty implementation; YOU DO NOT NEED TO IMPLEMENT THIS
 */
void* mm_realloc(void *ptr, size_t t)
{
	return NULL;
}

/*
 * mm_exit - finalize the malloc package.
 */
void mm_exit(void)
{
	char *p = NEXT_BLKP (heap_listp);

	while (GET_SIZE (HDRP (p)) != 0){
//	   	printf ("p is %x\n", p);
		if (GET_ALLOC (HDRP (p))){
		    mm_free (p);
//		    printf ("p was freed\n");
		}
		p = NEXT_BLKP (p);
	}
}

