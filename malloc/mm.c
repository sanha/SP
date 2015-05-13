/*
 * mm.c with rbtree.
 *
 * I referred some basics and implicit method in the textbook, which is
 * Bryand & O'Hallaron, Computer Systems - A programmer's Perspective.
 *
 * And also referred the red-black tree implementation in the
 * www.eternallyconfuzzled.com/tuts/datastructures/jsw_tut_rbtree.aspx
 *
 * For increasing throuputs, the red-black tree is used.
 * The pointer pointing root of rb tree is saved at the begining of heap.
 * The red-black flag is saved right before the allocation flag, and
 * the pointers pointing children is saved right after the flags.
 * When some block is freed, coalesce it and put it into the rb tree, and
 * when alloc some block, find appropreate block in the rb tree.
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
#define LIST_MAX	20	// 20 segregated free list exist

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)		(*(unsigned int *)(p))
#define PUT(p, val)	(*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)	(GET (p) & ~0x7)
#define GET_ALLOC(p)	(GET (p) & 0x1)

/* Read and write the free-list pointer */ // TODO: check?
#define GET_NP(bp)		(*(char **)(bp))
#define GET_PP(bp)		(*(char **)(bp + WSIZE))
#define SET_NP(bp, p)		(*(char **)(bp) = p)
#define SET_PP(bp, p)		(*(char **)(bp + WSIZE) = p)

/*
#define PTR_GET(f, bp)		((f)? (*(char **)(bp + WSIZE)) : (*(char **)(bp)))
#define PTR_PUT(f, bp, p)	((f)? (*(char **)(bp + WSIZE) = p) : (*(char **)(bp) = p))
*/
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

static char *heap_listp;	// heap base pointer
static char *seg_lists;		// seg lists pointer

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
	printf ("starting init!!!\n");
//	printf ("heap_listp is %x\n", heap_listp);
	int i;

	/* Create the initial empty heap */
  	if ((heap_listp = mem_sbrk (24*WSIZE)) == (void *) -1)
		return -1;
  	PUT (heap_listp, 0);					// Alignment padding
	for (i=1; i<=LIST_MAX; i++) 
		*(char **)(heap_listp + i * WSIZE) = NULL;	// 20 seg list pointer 	
	PUT (heap_listp + (21*WSIZE), PACK (DSIZE, 1));	// Prologue header
	PUT (heap_listp + (22*WSIZE), PACK (DSIZE, 1));	// Prologue footer
	PUT (heap_listp + (23*WSIZE), PACK (0, 1));		// Epilogue header
	seg_lists = heap_listp + WSIZE;
	heap_listp += 22*WSIZE;
	printf ("heap_listp is %x\n", heap_listp);
	printf ("seg_lists is %x\n", seg_lists);
  	
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

	printf ("extend_heap with size %u, last bit is %x\n", size, mem_heap_hi());

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
	printf("	Starting malloc. ");
//	printf("heq_listp at %x\n", heap_listp);
//	printf("Heap size is %d\n", mem_heapsize());

	size_t asize;			// Adjusted block size
	size_t extendsize;		// Amount to extend heap if no fit
	char *bp;

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
	seg_delete (bp);
	place (bp, asize);

	printf ("allocated block is %x, size is %u\n", bp, GET_SIZE (HDRP (bp)));
	return bp;
}

/*
 * find_fit - find appropreate block by searching in segregated free list.
 */
static char *find_fit (size_t asize){
	size_t size = asize;
	char *bp = NULL;
	int i;
	size >>= 4;			// minimum segr list start with size 16
        for (i=0; i<LIST_MAX; i++){
		bp = NTH (i, seg_lists);
		if ((i == LIST_MAX - 1) || ((size <= 1) && (bp != NULL))){
                	while ((bp != NULL) && (asize > GET_SIZE (HDRP (bp)))) {
                        	bp = GET_NP (bp); 
                	}
		}
                if (bp != NULL) break;
        }
	return bp;
}

/*
 * place - after find appropreate block, resize it and place new block.
 */
static void place (char *bp, size_t asize){
	size_t bsize = GET_SIZE (HDRP (bp));
	size_t nsize = bsize - asize;
	
	if (nsize >= 2*DSIZE){				// If remainder > 16byte, seperate them.
		PUT (HDRP (bp), PACK (asize, 1));	// allocated block
		PUT (FTRP (bp), PACK (asize, 1));
		bp = NEXT_BLKP (bp);			// fregmentation block
//		printf ("next blkp bp is %x\n", bp);
		PUT (HDRP (bp), PACK (nsize, 0));	// initionlization for
		PUT (FTRP (bp), PACK (nsize, 0));	// insereting into the rb tree

	        /* insert bp in segregated free list */
        	*(char **)bp = NULL;                            // initializing for insertion
         	*(char **)(bp + WSIZE) = NULL;
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
	printf ("	starting free, freed bp is %x, size is %d\n", ptr, GET_SIZE (HDRP (ptr)));
	if (!GET_ALLOC (HDRP (ptr))) { //doubly-freed
	    printf ("You doubly freed memory.\n");
	    abort();
	}

    	size_t size = GET_SIZE (HDRP (ptr));
	
	PUT (HDRP (ptr), PACK (size, 0));	// initalization for 
	PUT (FTRP (ptr), PACK (size, 0));	// inserting into the rb tree

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
	printf ("coalesced bp is %x, size is %d\n", bp, GET_SIZE (HDRP (bp)));

	size_t prev_alloc = GET_ALLOC (FTRP (PREV_BLKP (bp)));
	printf ("prev_alloc is %d, ", prev_alloc);
	size_t next_alloc = GET_ALLOC (HDRP (NEXT_BLKP (bp)));
	printf ("next_alloc is %d\n", next_alloc);
	size_t size = GET_SIZE (HDRP (bp));
//	printf ("size is %d\n\n", size);

	if (prev_alloc && next_alloc) ;			// case 1: prev & next block is allocated
		//printf ("case 1");
	else if (prev_alloc) {				// case 2: prev block is allocated only
//	    	printf ("case 2");
	    	if (NULL == seg_delete (NEXT_BLKP (bp))) {
			printf ("next bp %x wasn't in the tree.\n", NEXT_BLKP (bp));
			abort();
		}
		size += GET_SIZE (HDRP (NEXT_BLKP (bp)));	// initialization for insertion
		PUT (HDRP (bp), PACK (size, 0));
		PUT (FTRP (bp), PACK (size, 0));
	}
	else if (next_alloc) {				// case 3: next block is allocated only
//	    	printf ("case 3");
		if (NULL == seg_delete (PREV_BLKP (bp))) {
			printf ("prev bp %x wasn't in the tree.\n", PREV_BLKP (bp));
			abort();
		}
		size += GET_SIZE (HDRP (PREV_BLKP (bp)));	// initialization for insertion
		PUT (FTRP (bp), PACK (size, 0));
		bp = PREV_BLKP (bp);
		PUT (HDRP (bp), PACK (size, 0));
	}
	else {						// case 4: nothing is allocated
//	    	printf ("case 4\n\n");
		if (NULL == seg_delete (NEXT_BLKP (bp))) {
			printf ("next bp %x wasn't in the tree.\n", NEXT_BLKP (bp));
			abort();
		}
		else if (NULL == seg_delete (PREV_BLKP (bp))) {
			printf ("prev bp %x wasn't in the tree.\n", PREV_BLKP (bp));
			abort();
		}
		size += GET_SIZE (HDRP (PREV_BLKP (bp))) + GET_SIZE (FTRP (NEXT_BLKP (bp)));
		PUT (HDRP (PREV_BLKP (bp)), PACK (size, 0));	// initalization for insertion
		PUT (FTRP (NEXT_BLKP (bp)), PACK (size, 0));
		bp = PREV_BLKP (bp);
	}

	/* insert bp in segregated free list */
	*(char **)bp = NULL;				// initializing for insertion
	*(char **)(bp + WSIZE) = NULL;
	seg_insert (bp);			
//	if (rb_root != NULL)
//		printf ("after insertion, rb_root & it's size is %x, %d\n", rb_root, GET_SIZE (HDRP (rb_root)));
//	else printf ("rb_root is NULL\n");
	return bp;
}

/*
 * seg_insert - Insert a free block that bp is poining. The first list (seg_lists) has 
 * 		16 ~ 31 size blocks, and the last list (seg_lists + (19*NSIZE)) has 
 *		2^23 ~ size blocks. They are sorted in increasing order of SIZE and address.
 */
static void seg_insert (char *bp) {
    	printf ("inserting %x, size is %u\n", bp, GET_SIZE (HDRP (bp)));
	size_t bsize, size = GET_SIZE (HDRP (bp));
	size_t tmpsize = size;
	int i;				// iterator
	char *curr, *prev = NULL;	// current, previous pointer

	tmpsize >>= 4;			// smallest block size is 16
	/* Find segregated list */
	for (i = 0; (i < LIST_MAX -1) && (tmpsize > 1); i ++) {
		tmpsize >>= 1;
	}

	/* Search appropriate block in the selected segregated list */
	curr = NTH (i, seg_lists);
	printf ("i is %d, prev is %x, curr is %x\n", i, prev, curr);
	printf ("curr != NULL? %d\n", curr != NULL);
	for (;;) {
	    	if (curr == NULL) {
		    break;
		}
	    	bsize = GET_SIZE (HDRP (curr));
		if (size > bsize) prev = curr;
		else if (size < bsize) break;
		else if (bp > curr) prev = curr;
		else if (bp == curr) {
			printf ("It was already in the list\n");
			abort();
		}
		else break;

		curr = GET_NP (curr);
	}
	/* Found the position, so rearange the pointer. */
	if (prev == NULL) {
//	    	printf ("prev is %x, curr is %x\n", prev, curr);
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
	printf ("NTH (i, seg_lists) is %x\n", NTH (i, seg_lists));
}

/*
 * seg_delete - Delete a free block that bp is pointing. 
 */
static char *seg_delete (char *bp) {
	size_t bsize, size = GET_SIZE (HDRP (bp));
	size_t tmpsize = size;
	int i;
	char *curr, *prev;

	tmpsize >>= 4;
	/* Find segregated list */
	for (i = 0; (i < LIST_MAX -1) && (tmpsize > 1); i++) {
		tmpsize >>= 1;
	}

	/* Search bp in the selected sefregated list */
	curr = NTH (i, seg_lists);
	for (; curr != NULL; curr = GET_NP (curr)) {
		bsize = GET_SIZE (HDRP (curr));
		if (size > bsize) prev = curr;
		else if (size < bsize) return NULL;
		else if (bp > curr) prev = curr;
		else if (bp == curr) {
			break;
		}
		else return NULL;
	}

	curr = GET_NP (bp);
	if (prev == NULL) {
		if (curr == NULL) {			// case 1: list had only bp.
			NTH(i, seg_lists) = NULL;
		}
		else {					// case 2: bp was first node of list.
			SET_PP (curr, NULL);
			NTH(i, seg_lists) = curr;
		}
	}
	else if (curr == NULL) {			// case 3: bp was last node of list.
		SET_NP (prev, NULL);
	}
	else {						// case 4: bp was in the middle of list.
		SET_NP (prev, curr);
		SET_PP (curr, prev);
	}
	SET_NP (bp, NULL);
	SET_PP (bp, NULL);

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
			iET_PP
 */
void mm_exit(void)
{
	char *p = NEXT_BLKP (heap_listp);
//	printf ("!!!!!!!!!exit\n\n");
	while (GET_SIZE (HDRP (p)) != 0){	// TODO : till end.
//	   	printf ("p is %x\n", p);
		if (GET_ALLOC (HDRP (p))){
		    simpl_free (p);		// don't care about tree, but just free
//		    printf ("p was freed\n");
		}
		p = NEXT_BLKP (p);
	}
}

/*
 * simpl_free - Just free, don't care tree.
 */
static void simpl_free(char *ptr) {
//      printf ("starting free, freed bp is %x\n", ptr);
//    	printf ("simpl free, freed bp is %x\n\n", ptr);
       
        size_t size = GET_SIZE (HDRP (ptr));
    
        PUT (HDRP (ptr), PACK (size, 0));    // initalization for 
        PUT (FTRP (ptr), PACK (size, 0));    // inserting into the rb tree

        /* DON't MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
        if (gl_ranges)
                remove_range(gl_ranges, ptr);
}

