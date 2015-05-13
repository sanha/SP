/*
 * mm.c with segregated free list
 *
 * I referred some basics and implicit method in the textbook, which is
 * Bryand & O'Hallaron, Computer Systems - A programmer's Perspective.
 *
 * For increasing throuputs, the segregated free list is used.
 * The pointer pointing head of each free list is saved at the begining of heap.
 * Free block have two pointers additional to Header and footer, each pointing 
 * it's next node and prev node of free list.
 * Block looks like this. (w/o considering padding.)
 * 
 * ==============================
 * |	HEADER (4 byte)		|
 * ------------------------------
 * |	NEXT POINTER (4 byte)	|
 * ------------------------------
 * |	PREV POINTER (4 byte)	|
 * ------------------------------
 * |	PAYLOAD			|
 * ------------------------------
 * | 	FOOTER (4 byte)		|
 * ==============================
 *
 * So, the minimum block size is 16 (with 0 payload).
 * 20 segregated list entries are on heap, and each holds 2^n ~ 2^(n+1) -1 size block.
 * Because of the minimum block size, n is 4 ~ 24.
 *
 * When some block is freed, coalesce it and put it into segregated free list, and
 * when alloc some block, find appropreate block in the segregated free list.
 * The list sorted by only block size, not pointer address. 
 *
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
#define LIST_MAX	20	// segregated free list exist

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)		(*(unsigned int *)(p))
#define PUT(p, val)	(*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)	(GET (p) & ~0x7)
#define GET_ALLOC(p)	(GET (p) & 0x1)

/* Read and write the free-list pointer */ 
#define GET_NP(bp)		(*(char **)(bp))
#define GET_PP(bp)		(*(char **)(bp + WSIZE))
#define SET_NP(bp, p)		(*(char **)(bp) = p)
#define SET_PP(bp, p)		(*(char **)(bp + WSIZE) = p)

/* Given block ptr bp, compute address of its header nad footer */
#define HDRP(bp)	((char *)(bp) - WSIZE)
#define FTRP(bp)	((char *)(bp) + GET_SIZE (HDRP (bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)	((char *)(bp) + GET_SIZE (((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)	((char *)(bp) - GET_SIZE (((char *)(bp) - DSIZE)))

/* return pointer pointing n'th seg list */
#define NTH(n, ptr)	(*(char **)(ptr + n*WSIZE))

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

/* pointers used to check inital heap space */
static char *heap_listp;	// heap base pointer
static char *seg_lists;		// seg lists entries pointer

/* function pre-definition */
static void *extend_heap (size_t words);
static void *coalesce (void *bp);
static void place (char *bp, size_t asize);
static char *find_fit (size_t asize);
static void simpl_free (char *ptr);
/* function for segregated list */
static void seg_insert (char *bp);
static char *seg_delete (char *bp);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(range_t **ranges)
{
	int i;

	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk (24*WSIZE)) == (void *) -1)
		return -1;
    	PUT (heap_listp, 0);					// Alignment padding
    	for (i=1; i<=LIST_MAX; i++) 
		*(char **)(heap_listp + i * WSIZE) = NULL;	// 20 seg list pointer 	
    	PUT (heap_listp + (21*WSIZE), PACK (DSIZE, 1));		// Prologue header
    	PUT (heap_listp + (22*WSIZE), PACK (DSIZE, 1));		// Prologue footer
	PUT (heap_listp + (23*WSIZE), PACK (0, 1));		// Epilogue header
    	seg_lists = heap_listp + WSIZE;
    	heap_listp += 22*WSIZE;
	    
	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap (CHUNKSIZE/WSIZE) == NULL)
		return -1;

	/* DON't MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
	gl_ranges = ranges;

	return 0;
}

/*
 * extend_heap - when more heap space needed, extend the heap.
 */
static void *extend_heap (size_t words){
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	    
	if (size < 2*DSIZE) size = 2*DSIZE;		
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
	    
	/* Initialize free block header/footer and the epilogue header */
	PUT (HDRP (bp), PACK (size, 0));	// Free block header
	PUT (FTRP (bp), PACK (size, 0));	// Free block footer
	PUT (HDRP (NEXT_BLKP (bp)), PACK (0, 1));	// New epilogue header
	   

	/* Coalesce if the previous block was free */
	return coalesce (bp);
}

//TODO: maybe delete?
static void *extend_asize (size_t words){
        char *bp;
        size_t size;

        /* Allocate an even number of words to maintain alignment */
        size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    
        if (size < 2*DSIZE) size = 2*DSIZE;             
        if ((long)(bp = mem_sbrk(size)) == -1) 
                return NULL;

        /* Initialize free block header/footer and the epilogue header */
        PUT (HDRP (bp), PACK (size, 0));        // Free block header
        PUT (FTRP (bp), PACK (size, 0));        // Free block footer
        PUT (HDRP (NEXT_BLKP (bp)), PACK (0, 1));       // New epilogue header
    
        /* Coalesce if the previous block was free */
        SET_NP (bp, NULL);                              // initializing for insertion
        SET_PP (bp, NULL);
        seg_insert (bp);

        return bp;
}



/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 */
void* mm_malloc(size_t size)
{
	size_t asize;			// Adjusted block size
	size_t extendsize;		// Amount to extend heap if no fit
	char *bp = NULL;

	/* Ignore spurious requests */
	if (size == 0) return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE) asize = 2*DSIZE;
	else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

	/* Search the free list for a fit */
	if ((bp = find_fit (asize)) != NULL) {
		seg_delete (bp);
		place (bp, asize);
		return bp;
	}
	    
	/* No fit found, Get more memory */	
	extendsize = MAX (asize, CHUNKSIZE);
        if ((bp = extend_heap (extendsize / WSIZE)) == NULL) return NULL;
//	if ((bp = extend_heap (asize / WSIZE)) == NULL) return NULL;
	seg_delete (bp);
	place (bp, asize);

//	extend_asize (asize / WSIZE);
//	extend_asize (asize / WSIZE);

	return bp;
}

/*
 * find_fit - find appropreate block by searching in segregated free list.
 */
static char *find_fit (size_t asize) {
	size_t size = asize;
	char *bp = NULL;
	int i;
        for (i=0; i<LIST_MAX; i++){
		if ((i == LIST_MAX - 1) || ((size <= 1) && (NTH (i, seg_lists) != NULL))){
                 	bp = NTH (i, seg_lists);
		    	while ((bp != NULL) && (asize > GET_SIZE (HDRP (bp)))) {
                        	bp = GET_NP (bp); 
                	}
		}
                if (bp != NULL) break;
		size >>= 1;
        }
	return bp;
}


/*
 * place - after find appropreate block, resize it and place new block.
 */
static void place (char *bp, size_t asize) {
	size_t bsize = GET_SIZE (HDRP (bp));
	size_t nsize = bsize - asize;

	/* Check wheter it could be splited */
	if (nsize >= 2*DSIZE){				// If remainder > 16byte, seperate them.
		PUT (HDRP (bp), PACK (asize, 1));	// allocated block
		PUT (FTRP (bp), PACK (asize, 1));
		bp = NEXT_BLKP (bp);			// fregmented block
		PUT (HDRP (bp), PACK (nsize, 0));	
		PUT (FTRP (bp), PACK (nsize, 0));	

	        /* insert bp in segregated free list */
		SET_NP (bp, NULL);			// initialization for segr list insertion.
		SET_PP (bp, NULL);		
		seg_insert (bp);    
	}
	else {						// Else, just allocate.
		PUT (HDRP (bp), PACK (bsize, 1));
		PUT (FTRP (bp), PACK (bsize, 1));
	}
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
	if (!GET_ALLOC (HDRP (ptr))) { 		//doubly-freed
	    printf ("You doubly freed memory.\n");
	    abort();
	}

    	size_t size = GET_SIZE (HDRP (ptr));
	
	PUT (HDRP (ptr), PACK (size, 0));	// deallocated. 
	PUT (FTRP (ptr), PACK (size, 0));	

	coalesce (ptr);

  	/* DON't MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
  	if (gl_ranges)
    		remove_range(gl_ranges, ptr);
}

/*
 * coalesce - when some block freed, chaeck the front & lear block, and 
 * 	      if it us free also, coalesce it and insert it in the segregated list.
 */
static void *coalesce (void *bp){
	size_t prev_alloc = GET_ALLOC (FTRP (PREV_BLKP (bp)));
	size_t next_alloc = GET_ALLOC (HDRP (NEXT_BLKP (bp)));
	size_t size = GET_SIZE (HDRP (bp));

	if (prev_alloc && next_alloc) ;			// case 1: prev & next block is allocated

	else if (prev_alloc) {				// case 2: prev block is allocated only
	    	seg_delete (NEXT_BLKP (bp));
		size += GET_SIZE (HDRP (NEXT_BLKP (bp)));	// initialization for insertion
		PUT (HDRP (bp), PACK (size, 0));
		PUT (FTRP (bp), PACK (size, 0));
	}
	else if (next_alloc) {				// case 3: next block is allocated only
	    	seg_delete (PREV_BLKP (bp));
		size += GET_SIZE (HDRP (PREV_BLKP (bp)));	// initialization for insertion
		PUT (FTRP (bp), PACK (size, 0));
		bp = PREV_BLKP (bp);
		PUT (HDRP (bp), PACK (size, 0));
	}
	else {						// case 4: nothing is allocated
	    	seg_delete (NEXT_BLKP (bp));
		seg_delete (PREV_BLKP (bp));
	    	size += GET_SIZE (HDRP (PREV_BLKP (bp))) + GET_SIZE (FTRP (NEXT_BLKP (bp)));
		PUT (HDRP (PREV_BLKP (bp)), PACK (size, 0));	// initalization for insertion
		PUT (FTRP (NEXT_BLKP (bp)), PACK (size, 0));
		bp = PREV_BLKP (bp);
	}

	/* insert bp in segregated free list */
	SET_NP (bp, NULL);				// initializing for insertion
	SET_PP (bp, NULL);
	seg_insert (bp);			
	return bp;
}

/*
 * seg_insert - Insert a free block that bp is poining. The first list (seg_lists) has 
 * 		16 ~ 31 size blocks, and the last list (seg_lists + (19*NSIZE)) has 
 *		2^23 ~ size blocks. They are sorted in increasing order of SIZE and address.
 */
static void seg_insert (char *bp) {
	size_t size = GET_SIZE (HDRP (bp));
	int i;				// iterator
	char *curr, *prev = NULL;	// current, previous pointer
	
	/* Find segregated list */
	for (i = 0; (i < LIST_MAX -1) && (size > 1); i ++) {
		size >>= 1;
	}


	size_t asize = GET_SIZE (HDRP (bp));
	/* Search appropriate block in the selected segregated list */
	curr = NTH (i, seg_lists);
	for (;curr != NULL; curr = GET_NP (curr)) {
		if (asize > GET_SIZE (HDRP (curr))) prev = curr; 
		else break;
	}

	/* If found the position, rearange the pointer. */
	if (prev == NULL) {
		if (curr == NULL) {			// case 1: list is empty.
			NTH (i, seg_lists) = bp;
		}
		else {					// case 2: bp shold be the first node of list.
			SET_NP (bp, curr);
			SET_PP (curr, bp);
			NTH (i, seg_lists) = bp;
		}
	}
	else if (curr == NULL){				// case 3: bo shold be the last node of list.
		SET_PP (bp, prev);
		SET_NP (prev, bp);
	}
	else {						// case 4: bp shold be inserted in middle of list.
		SET_NP (prev, bp);
		SET_PP (bp, prev);
		SET_NP (bp, curr);
		SET_PP (curr, bp);
	}
}

/*
 * seg_delete - Delete a free block that bp is pointing. 
 */
static char *seg_delete (char *bp) {
    	size_t size = GET_SIZE (HDRP (bp));
	int i;
	
	/* Find segregated list */
	for (i = 0; (i < LIST_MAX -1) && (size > 1); i++) {
		size >>= 1;
	}

	char *next = GET_NP (bp);
	char *prev = GET_PP (bp);

	if (next == NULL) {				// case 1: list had only bp.
		if (prev == NULL) NTH (i, seg_lists) = NULL;
	    	else SET_NP (prev, NULL);		// case 2: bp was first node of list.
	}
	else if (prev == NULL){				// case 3: bp was last node of list.
	    	SET_PP (next, NULL);
	    	NTH (i, seg_lists) = next;
	}
	else {						// case 4: bp was in the middle of list.
		SET_NP (prev, next);
		SET_PP (next, prev);
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
		if (GET_ALLOC (HDRP (p))){
		    simpl_free (p);		// don't care about list, but just free
		}
		p = NEXT_BLKP (p);
	}
}

/*
 * simpl_free - Just free, don't care about segregated free list.
 */
static void simpl_free(char *ptr) {
        size_t size = GET_SIZE (HDRP (ptr));
    
        PUT (HDRP (ptr), PACK (size, 0));    
        PUT (FTRP (ptr), PACK (size, 0));   

        /* DON't MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
        if (gl_ranges)
                remove_range(gl_ranges, ptr);
}

