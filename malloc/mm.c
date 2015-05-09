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

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size, rb bit and allocated bit into word */
#define PACK(size, rb, alloc) ((size) | (rb << 1) | (alloc))

/* Read and write a word at address p */
#define GET(p)		(*(unsigned int *)(p))
#define PUT(p, val)	(*(unsigned int *)(p) = (val))

/* Read the size, rb and allocated fields from address p */
#define GET_SIZE(p)	(GET (p) & ~0x7)
#define GET_ALLOC(p)	(GET (p) & 0x1)

/* Set RB flags */
#define SET_RB(r, p)	((r)? (PUT (p, (GET (p) | 0x10))) : (PUT (p, (GET_SIZE (p) | GET_ALLOC(p)))))

/* Read and write the children pointer */
#define CHILD_GET(f, bp)	((f)? (*(char **)(bp + WSIZE)) : (*(char **)(bp)))
#define CHILD_PUT(f, bp, p)	((f)? (*(char **)(bp + WSIZE) = p) : (*(char **)(bp) = p))

/* Given block ptr bp, compute address of its header nad footer */
#define HDRP(bp)	((char *)(bp) - WSIZE)
#define FTRP(bp)	((char *)(bp) + GET_SIZE (HDRP (bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)	((char *)(bp) + GET_SIZE (((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)	((char *)(bp) - GET_SIZE (((char *)(bp) - DSIZE)))

/* Determine wether the node is red */
#define IS_RED(bp)      ((bp != NULL) && (GET (HDRP (bp)) & 0x10))


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
static char *rb_root = NULL;	// pointing rb tree's root
static char *rb_head = NULL;	// pointing head node

/* function pre-definition */
static void *extend_heap (size_t words);
static void *coalesce (void *bp);
static void place (char *bp, size_t asize);
static void *find_fit (size_t asize);
/* functions used for rb tree */
static char *rot_single (char *root, int dir);
static char *rot_double (char *root, int dir);
static int rb_assert ();
static int rb_insert (char *bp);
static char *rb_remove (char *bp);


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(range_t **ranges)
{
//	printf ("starting init\n");
//	printf ("heap_listp is %x\n", heap_listp);

	/* Create the initial empty heap */
  	if ((heap_listp = mem_sbrk (4*DSIZE)) == (void *) -1)
		return -1;
  	PUT (heap_listp, 0);					// Alignment padding
	PUT (heap_listp + WSIZE, 0);
	PUT (heap_listp + (2*WSIZE), 0);			// Used to RB-tree head node
	*(heap_listp + (3*WSIZE)) = NULL;
	*(heap_listp + (4*WSIZE)) = NULL;
	PUT (heap_listp + (5*WSIZE), PACK (DSIZE, 0, 1));	// Prologue header
	PUT (heap_listp + (6*WSIZE), PACK (DSIZE, 0, 1));	// Prologue footer
	PUT (heap_listp + (7*WSIZE), PACK (0, 0, 1));		// Epilogue header
	rb_head = heap_listp + (3*WSIZE);
	heap_listp += 6*WSIZE;
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
	
	if (size < 2*DSIZE) size = 2*DSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;

//	printf("extend_heap, size is %d\n",size);
//	printf("bp is %x\n", bp);
	
//	printf("GET_ALLOC bp is %d\n", GET_ALLOC (HDRP (bp)));
//	printf("GET_SIZE bp is %d\n", GET_SIZE (HDRP (bp)));
	
	/* Initialize free block header/footer and the epilogue header */
	//TODO: change this to insert (rb_root, bp) => coal deal with this.
	PUT (HDRP (bp), PACK (size, 1, 0));	// Free block header
	PUT (FTRP (bp), PACK (size, 1, 0));	// Free block footer
	PUT (HDRP (NEXT_BLKP (bp)), PACK (0, 0, 1));	// New epilogue header
       
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
	if (size <= 0) return NULL;

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
	//TODO : Change this to search & delete from tree.
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
		PUT (HDRP (bp), PACK (asize, 0, 1));	// allocated block
		PUT (FTRP (bp), PACK (asize, 0, 1));
		bp = NEXT_BLKP (bp);			// fregmentation block
		PUT (HDRP (bp), PACK (nsize, 1, 0));	// initionlization for
		PUT (FTRP (bp), PACK (nsize, 1, 0));	// insereting into the rb tree
		coalesce (bp);
	}
	else {
		PUT (HDRP (bp), PACK (bsize, 0, 1));
		PUT (FTRP (bp), PACK (bsize, 0, 1));
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
	    abort();
	}
    
    	size_t size = GET_SIZE (HDRP (ptr));
	
	PUT (HDRP (ptr), PACK (size, 1, 0));	// initalization for 
	PUT (FTRP (ptr), PACK (size, 1, 0));	// inserting into the rb tree

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

	if (prev_alloc && next_alloc) ;	// case 1: prev & next blokc is allocated

	else if (prev_alloc) {				// case 2: prev block is allocated only
		size += GET_SIZE (HDRP (NEXT_BLKP (bp)));	// initialization for insertion
		PUT (HDRP (bp), PACK (size, 1, 0));
		PUT (FTRP (bp), PACK (size, 1, 0));
	}

	else if (next_alloc) {				// case 3: next block is allocated only
		size += GET_SIZE (HDRP (PREV_BLKP (bp)));	// initialization for insertion
		PUT (FTRP (bp), PACK (size, 1, 0));
		bp = PREV_BLKP (bp);
		PUT (HDRP (bp), PACK (size, 1, 0));
	}

	else {						// case 4: nothing is allocated
		size += GET_SIZE (HDRP (PREV_BLKP (bp))) + GET_SIZE (FTRP (NEXT_BLKP (bp)));
		PUT (HDRP (PREV_BLKP (bp)), PACK (size, 1, 0));	// initalization for insertion
		PUT (FTRP (NEXT_BLKP (bp)), PACK (size, 1, 0));
		bp = PREV_BLKP (bp);
	}

	*(char *)bp = NULL;
	*(char *)(bp + WSIZE) = NULL;
	//TODO: insert
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


/*
static int rb_assert (); 
static char *rb_remove (char *root, char *bp);
*/
/*
 * Funcitons used to build & destruct Red-black tree
 */
static char *rot_single (char *root, int dir){
	char *opposite = CHILD_GET (!dir, root);

	CHILD_PUT (!dir, root, CHILD_GET (dir, opposite));
	CHILD_PUT (dir, opposite, root);
	
	SET_RB (1, (HDRP (root)));
	SET_RB (0, (HDRP (opposite)));

	return opposite;
}

static char *rot_double (char *root, int dir){
	CHILD_PUT (!dir, root, rot_single (CHILD_GET (!dir, root), !dir));

	return rot_single (root, dir);
}

static int rb_insert (char *bp){
	if (rb_root == NULL)	// Empty tree
		rb_root = bp;
	else {
	    	/* setup for iterating */
		PUT (HDRP (rb_head), 0);	// bp_head points the False root.
		*rb_head = NULL;
		*(rb_head + WSIZE) = NULL;

		char *g, *t;	// Grandparent & parent
		char *p, *q;	// Iterator & parent
		int last, dir = 0;

		t = rb_head;
		g = p = NULL;
		q = rb_root;
		CHILD_PUT (1, t, rb_root);

		/* iteration with searching */
		while (1){
			if (q == NULL){
				q = bp;
				CHILD_PUT (dir, p, q);
			}
			else if (IS_RED (CHILD_GET (0, q)) && IS_RED (CHILD_GET (1, q))) {
				/* Color flip */
			    	SET_RB (1, HDRP (q));
				SET_RB (0, HDRP (CHILD_GET (0, q)));
				SET_RB (0, HDRP (CHILD_GET (1, q)));
			}

			/* Fix red violation */
			if ((IS_RED (q)) && (IS_RED (p))) {
				int dir2 = (CHILD_GET (1, t) == g);

				if (q == (CHILD_GET (last, p))) CHILD_PUT (dir2, t, rot_single (g, !last));
				else CHILD_PUT (dir2, t, rot_double (g, !last));
			}

			/* Update direction */
			if (q == bp) break;	// Stop if found
			
			last = dir;	
			if ((GET_SIZE (HDRP (q))) == (GET_SIZE (HDRP (bp)))) dir = (q < bp);
			else dir = ((GET_SIZE (HDRP (q))) < (GET_SIZE (HDRP (bp))));

			/* Update helpers */
			if (g != NULL) t = g;
			g = p, p = q;
			q = CHILD_GET (dir, q);
		}
	
		/* Update root */
		rb_root = CHILD_GET (dir, rb_head);
	}

	SET_RB (0, (HDRP (rb_root)));	// Make root black

	return 1;
}
