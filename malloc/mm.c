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
#define SET_RB(r, p)	((r)? (PUT (p, (GET (p) | 0x2))) : (PUT (p, (GET (p) & ~0x2))))

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
#define IS_RED(bp)      ((bp != NULL) && (GET (HDRP (bp)) & 0x2))


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
static void simpl_free (char *ptr);
/* functions used for rb tree */
static char *rot_single (char *root, int dir);
static char *rot_double (char *root, int dir);
static int rb_assert (char *root);
static void rb_insert (char *bp);
static char *rb_fit (size_t size);
static char *rb_remove (char *bp);
static char *find_parent (char *child);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(range_t **ranges)
{
//	printf ("starting init!!!\n\n");
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
	rb_root = NULL;
	heap_listp += 6*WSIZE;
//	printf ("heap_listp is %x\n", heap_listp);

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

//	printf("extend_heap, size is %d\n",size);
//	printf("bp is %x\n", bp);
	
//	printf("GET_ALLOC bp is %d\n", GET_ALLOC (HDRP (bp)));
//	printf("GET_SIZE bp is %d\n", GET_SIZE (HDRP (bp)));
	
	/* Initialize free block header/footer and the epilogue header */
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
	printf("	Starting malloc. ");
//	printf("heq_listp at %x\n", heap_listp);
//	printf("Heap size is %d\n", mem_heapsize());

	size_t asize;			// Adjusted block size
	size_t extendsize;		// Amount to extend heap if no fit
	char *bp;

	/* Ignore spurious requests */
	if (size <= 0) return NULL;

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE) asize = 2*DSIZE;
	else asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

	

	/* Search the free list for a fit */
	if ((bp = find_fit (asize)) != NULL) {
		place (bp, asize);
		printf ("allocated block is %x, size is %d\n", bp, GET_SIZE (HDRP (bp)));
		return bp;
	}
	
	/* No fit found, Get more memory and place the block */
	extendsize = MAX (asize, CHUNKSIZE);
	if ((bp = extend_heap (extendsize / WSIZE)) == NULL) return NULL;
	bp = rb_fit (asize);
	place (bp, asize);
	printf ("allocated block is %x, size is %d\n", bp, GET_SIZE (HDRP (bp)));
	return bp;
}

/*
 * find_fit - find appropreate block by searching at the rb tree.
 */
static void *find_fit (size_t asize){
//	char *p = heap_listp;
//	char *end = mem_heap_hi();
	//TODO : Change this to search & delete from tree. before this, check result > size
	//	if it is NULL, extend.
//	printf("end is %x\n", end);

//	while (1){
//		if (p < end){
//			printf ("p is %x\n", p);
//			printf ("GET_ALLOC p is %d\n", GET_ALLOC (HDRP (p)));
//			printf ("GET_SIZE p is %d\n", GET_SIZE (HDRP (p)));
//			if ((GET_ALLOC (HDRP (p)) || (GET_SIZE (HDRP (p)) < asize)))
//				p = NEXT_BLKP (p);
//			else return p;
//		}
//		else return NULL;
//	}
    	char *block = rb_fit (asize);			// free block from rb tree;
	return block;					// TODO : we don't need this.

}

/*
 * place - after find appropreate block, resize it and place new block.
 */
static void place (char *bp, size_t asize){
	size_t bsize = GET_SIZE (HDRP (bp));
	size_t nsize = bsize - asize;
	
	if (nsize >= 2*DSIZE){	//TODO : CHECK
		PUT (HDRP (bp), PACK (asize, 0, 1));	// allocated block
		PUT (FTRP (bp), PACK (asize, 0, 1));
		bp = NEXT_BLKP (bp);			// fregmentation block
//		printf ("next blkp bp is %x\n", bp);
		PUT (HDRP (bp), PACK (nsize, 1, 0));	// initionlization for
		PUT (FTRP (bp), PACK (nsize, 1, 0));	// insereting into the rb tree

	        /* insert bp in rb tree */
	        *(char **)bp = NULL;                            // initializing for insertion
        	*(char **)(bp + WSIZE) = NULL;
        	rb_insert (bp);    
//        	printf ("at place, rb_root & it's size is %x, %d\n", rb_root, GET_SIZE (HDRP (rb_root)));
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
	printf ("	starting free, freed bp is %x, size is %d\n", ptr, GET_SIZE (HDRP (ptr)));
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

/*
 * coalesce - when some block freed, chaeck the front & lear block
 * 	      and if it us free also, coalesce it.
 */
static void *coalesce (void *bp){
	printf ("coalesced bp is %x, size is %d\n", bp, GET_SIZE (HDRP (bp)));

	size_t prev_alloc = GET_ALLOC (FTRP (PREV_BLKP (bp)));
//	printf ("prev_alloc is %d\n\n", prev_alloc);
	size_t next_alloc = GET_ALLOC (HDRP (NEXT_BLKP (bp)));
//	printf ("next_alloc is %d\n\n", next_alloc);
	size_t size = GET_SIZE (HDRP (bp));
//	printf ("size is %d\n\n", size);

	if (prev_alloc && next_alloc) printf ("case 1");	// case 1: prev & next blokc is allocated
	else if (prev_alloc) {				// case 2: prev block is allocated only
//	    	printf ("case 2");
	    	if (NULL == rb_remove (NEXT_BLKP (bp))) {
			printf ("next bp %x wasn't in the tree.\n", NEXT_BLKP (bp));
			abort();
		}
		size += GET_SIZE (HDRP (NEXT_BLKP (bp)));	// initialization for insertion
		PUT (HDRP (bp), PACK (size, 1, 0));
		PUT (FTRP (bp), PACK (size, 1, 0));
	}
	else if (next_alloc) {				// case 3: next block is allocated only
//	    	printf ("case 3");
		if (NULL == rb_remove (PREV_BLKP (bp))) {
			printf ("prev bp %x wasn't in the tree.\n", PREV_BLKP (bp));
			abort();
		}
		size += GET_SIZE (HDRP (PREV_BLKP (bp)));	// initialization for insertion
		PUT (FTRP (bp), PACK (size, 1, 0));
		bp = PREV_BLKP (bp);
		PUT (HDRP (bp), PACK (size, 1, 0));
	}
	else {						// case 4: nothing is allocated
//	    	printf ("case 4\n\n");
		if (NULL == rb_remove (NEXT_BLKP (bp))) {
			printf ("next bp %x wasn't in the tree.\n", NEXT_BLKP (bp));
			abort();
		}
		else if (NULL == rb_remove (PREV_BLKP (bp))) {
			printf ("prev bp %x wasn't in the tree.\n", PREV_BLKP (bp));
			abort();
		}
		size += GET_SIZE (HDRP (PREV_BLKP (bp))) + GET_SIZE (FTRP (NEXT_BLKP (bp)));
		PUT (HDRP (PREV_BLKP (bp)), PACK (size, 1, 0));	// initalization for insertion
		PUT (FTRP (NEXT_BLKP (bp)), PACK (size, 1, 0));
		bp = PREV_BLKP (bp);
	}

	/* insert bp in rb tree */
	*(char **)bp = NULL;				// initializing for insertion
	*(char **)(bp + WSIZE) = NULL;
	rb_insert (bp);			
//	if (rb_root != NULL)
//		printf ("after insertion, rb_root & it's size is %x, %d\n", rb_root, GET_SIZE (HDRP (rb_root)));
//	else printf ("rb_root is NULL\n");
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
    	printf ("simpl free, freed bp is %x\n\n", ptr);
        if (!GET_ALLOC (HDRP (ptr))) { //doubly-freed
            printf ("You doubly freed memory.\n");
            abort();
        }
       
        size_t size = GET_SIZE (HDRP (ptr));
    
        PUT (HDRP (ptr), PACK (size, 1, 0));    // initalization for 
        PUT (FTRP (ptr), PACK (size, 1, 0));    // inserting into the rb tree

        /* DON't MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
        if (gl_ranges)
                remove_range(gl_ranges, ptr);
}



/*
 * rot_single - rotate the rb tree according to direction.
 */
static char *rot_single (char *root, int dir){
	char *opposite = CHILD_GET (!dir, root);

	CHILD_PUT (!dir, root, CHILD_GET (dir, opposite));
	CHILD_PUT (dir, opposite, root);
	
	SET_RB (1, (HDRP (root)));
	SET_RB (0, (HDRP (opposite)));

	return opposite;
}
/*
 * rot_double - rotate the rb tree accoring to direction twice.
 */
static char *rot_double (char *root, int dir){
	CHILD_PUT (!dir, root, rot_single (CHILD_GET (!dir, root), !dir));

	return rot_single (root, dir);
}
//TODO : change the name of val.
/*
 * rb_assrt - check the tree is well-constucted.
 	      when really run-time, this function is not used, so
	      implementation with recursion doesn't matter.
 */
static int rb_assert (char *root){
	int lh, rh;
	
	if (root == NULL) return 1;
	else {
		char *ln = CHILD_GET (0, root);
		char *rn = CHILD_GET (1, root);
		
		/* Consecutive red links */
		if (IS_RED (root)) {
			if (IS_RED (ln) || (IS_RED (rn))) {
				printf ("Red violation");
				return 0;
			}
		}

		lh = rb_assert (ln);
		rh = rb_assert (rn);

		/* Invalid binary search tree */
		if ((ln != NULL) && (((GET_SIZE (HDRP (ln))) > (GET_SIZE (HDRP(root)))) || (((GET_SIZE (HDRP (ln)
				    )) == (GET_SIZE (HDRP (root)))) && (ln >= root)))) { // left child violated
			printf ("Binary tree violation\n");
		    	return 0;
		}
		if ((rn != NULL) && (((GET_SIZE (HDRP (rn))) < (GET_SIZE (HDRP(root)))) || (((GET_SIZE (HDRP (rn)
				    )) == (GET_SIZE (HDRP (root)))) && (rn <= root)))) { // right child violated
		    	printf ("Binary tree violation\n");
			return 0;
			
		}

		/* Black height mismatch */
		if (lh != 0 && rh != 0 && lh != rh){
			printf ("Black violation\n");
			return 0;
		}

		/* Only cound black links */
		if (lh != 0 && rh != 0){
		    return IS_RED (root) ? lh : lh + 1;
		}
		else return 0;
	}
}

/*
 * rb_insert - insert new free block with tow-down algorithm.
 */
static void rb_insert (char *bp){
	printf ("start rb_insert, inserting bp is %x, size is %u\n", bp, GET_SIZE (HDRP (bp)));
	if (GET_SIZE (HDRP (bp)) > 1000000) abort();		// TODO: test

	if (rb_root == NULL)	// Empty tree
		rb_root = bp;
	else {
	    	/* setup for iterating */
		PUT (HDRP (rb_head), 0);	// bp_head points the False root.
		*rb_head = NULL;
		*(rb_head + WSIZE) = NULL;

		char *g, *t;	// Grandparent & head
		char *q, *p;	// Iterator & parent
		int last, dir = 0;

		t = rb_head;
		g = p = NULL;
		q = rb_root;
		CHILD_PUT (1, t, rb_root);

//		printf ("	inserting bp & it's size is %x, %d\n", bp, GET_SIZE (HDRP (bp)));
//		printf ("rb_root & it's size & rb is %x, %d. %d\n", rb_root, GET_SIZE (HDRP (rb_root)), IS_RED (rb_root));

		/* iteration with searching */
		while (1){
//	                printf ("t, g, p, q, dir is %x, %x, %x, %x, %d\n", t, g, p, q, dir);  
//        	        printf ("q is alloc? %d\n", GET_ALLOC (HDRP (q)));
//			printf ("*q is %x\n", *q);
/*	                if (q!=NULL) {
				char *left = CHILD_GET (0, q);
        		        char *right = CHILD_GET (1, q);
                		printf ("left  is %x ", left);
	                	printf ("right is %x ", right);
				printf ("q's size is %d\n", GET_SIZE (HDRP (q)));
			}
*/
			if (q == NULL){
				q = bp;
				CHILD_PUT (dir, p, q);
//				printf ("t is %x, g is %x, p is %x, q is %x \n", t, g, p, q);
//				printf ("p is red? %d, q is red? %d\n", IS_RED(p), IS_RED(q));
//				if (g != NULL)
//					printf ("g's right child is p? %d\n", CHILD_GET (1, g) == p);
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

				if (q == (CHILD_GET (last, p))) {
//				 	printf ("\n hi, dir2 is %d, last is %d\n", dir2, last);
					CHILD_PUT (dir2, t, rot_single (g, !last));
					// TODO: check
					g = t;
//					printf ("t is %x, t's dir child is %x\n", t, CHILD_GET (dir2, t));
				}
				else {	// TODO: check							
					CHILD_PUT (dir2, t, rot_double (g, !last));
					p = t;
					g = NULL;
					t = NULL;
				}
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
		rb_root = CHILD_GET (1, rb_head);
	}
	
	SET_RB (0, (HDRP (rb_root)));	// Make root black
	return ;
}

/*
 * rb_fit - find appropreate (best-fit) free block from rb_tree and return the pointer 
 *	    after remove it with top-down algorithm
 */
static char *rb_fit (size_t size){
//	printf ("Starting rb_fit \n");	
    	if (rb_root == NULL) return NULL;	// empty tree

	PUT (HDRP (rb_head), 0);        	// bp_head points the False root.
	*rb_head = NULL;
	*(rb_head + WSIZE) = NULL;
	
	/* setup helper node pointers */
	char *q = rb_head;
	char *f, *g, *p;
	f = g = p = NULL;
	CHILD_PUT (1, q, rb_root);
	size_t bsize = GET_SIZE (HDRP (rb_root));
	int same = (bsize == size);
	if (same) f = rb_root;
	int dir = 1;
	int last;

	/* Search and push a red down */
	while (CHILD_GET (dir,q) != NULL){
		last = dir;

		/* Update helpers */
		g = p, p = q;
		q = CHILD_GET (dir, q);
		bsize = GET_SIZE (HDRP (q));
	
//		printf ("g, p, q is %x, %x, %x\n", g, p, q);
//		printf ("q, bsize, size is %x, %d, %d\n", q, bsize, size);

		if (same) {	// if we found already, just go down.
			if (f == q) dir = 0;
			else dir = 1;
		}
		else {
		    	dir = (bsize < size);
			/* Save found best-fit block pointer at f */
			same = (bsize == size);
			if (same) {			// if block size is equal to wanted size,
				f = q;			// this is the final f, so set same as 1.
			}				// at right after found same size, go left.

			else if (!dir) {		// if block size is larger than wanted size,
			    	f = q;			// just save it in f and go left.
			}
		}
/*
		printf ("same is %d, dir is %d, f is %x\n", same, dir, f);
		printf ("f's is_red is %d\n", IS_RED (f));
		printf ("q is alloc? %d\n", GET_ALLOC (HDRP (q)));
		char *left = CHILD_GET (0, q);
		char *right = CHILD_GET (1, q);
		printf ("left  is %x\n", left);
		printf ("right is %x\n", right);
		if (!(left == NULL))
			printf ("left & it's size is %x, %d\n", left, GET_SIZE (HDRP (left)));
		if (!(right == NULL))
			printf ("right & it's size is %x, %d\n", left, GET_SIZE (HDRP (right)));
*/
		/* Push the red node down */
		if (!(IS_RED(q)) && !(IS_RED (CHILD_GET (dir, q)))) {	// double black
		    	if (IS_RED (CHILD_GET (!dir, q))) {
				CHILD_PUT (last, p, rot_single (q, dir));
				p = CHILD_GET (last, p);		
			}
			else if (!(IS_RED (CHILD_GET (!dir, q)))) {	
			   	char *s = CHILD_GET (!last, p);
	
				if (s != NULL){
					if (!(IS_RED (CHILD_GET (!last, s))) && !(IS_RED (CHILD_GET (last, s)))){
						/* Color flip */
		  				SET_RB (0, HDRP (p));
						SET_RB (1, HDRP (s));
						SET_RB (1, HDRP (q));
					}
					else {
						int dir2 = (CHILD_GET (1, g) == p);
						
						if (IS_RED (CHILD_GET (last, s))) 
							CHILD_PUT (dir2, g, rot_double (p, last)); 
						else if (IS_RED (CHILD_GET (!last, s)))
						    	CHILD_PUT (dir2, g, rot_single (p, last));

						/* Ensure correct coloring */
						SET_RB (1, CHILD_GET (dir2, g));
						SET_RB (0, CHILD_GET (0, CHILD_GET (dir2, g)));
						SET_RB (0, CHILD_GET (1, CHILD_GET (dir2, g)));
						
						if (IS_RED(q) != 1) {	// TODO: test
							printf ("q is not red\n");
							abort();
						}
					}
				}
			}
		}
	}

/*	printf ("found1 f is %x\n", f);
	if (f != NULL) {
		printf ("size is %d, f's size is %d\n", size, GET_SIZE (HDRP (f)));
		if (size > GET_SIZE (HDRP (f))) {
			printf ("fucked\n");
			abort();
		}
	}
*/
	/* Replace and remove if found */
	if (f != NULL) {
		/* Find f's parent */
		char *fparent = find_parent (f);
		if (fparent == NULL) {	// something wrong.
			printf ("we can't find f's parent.\n");
			abort();
		}

//		printf ("p is %x, q is %x\n", p, q);
		
		/* Chain q with f's parent and f's children */
	    	CHILD_PUT (CHILD_GET (1, p) == q, p, CHILD_GET (!dir, q));
		if (f == q) ;					// if f == q, enough
		else if (f == p) {
//			printf ("dir is %d, f's 1 child is %x\n", dir, CHILD_GET (dir, f)); 
			CHILD_PUT (dir, q, CHILD_GET (dir, f));
			CHILD_PUT (CHILD_GET (1, fparent) == f, fparent, q);
		}
		else {				
			CHILD_PUT (0, q, CHILD_GET (0, f));
			CHILD_PUT (1, q, CHILD_GET (1, f));
			CHILD_PUT (CHILD_GET (1, fparent) == f, fparent, q);	
		}
		
	}

	/* Update root and make it black */
//	printf ("head and right child is %x, %x\n", rb_head, CHILD_GET (1, rb_head));

	rb_root = CHILD_GET (1, rb_head);
	if (rb_root != NULL) SET_RB (0, HDRP (rb_root));	// TODO : CHECK

	return f;
}

/*
 * rb_remove - find indicated free block in the rb tree and return the pointer 
 *             after remove it with top-down algorithm
 */
static char *rb_remove (char *bp){
	printf ("start rb_remove, finding bp is %x\n", bp);
        if (rb_root == NULL) return NULL;       // empty tree

        PUT (HDRP (rb_head), 0);                // bp_head points the False root.
        *rb_head = NULL;
        *(rb_head + WSIZE) = NULL;

	size_t size = GET_SIZE (HDRP (bp));
        /* setup helper node pointers */
        char *q = rb_head;
        char *f, *g, *p;
        f = g = p = NULL;
        CHILD_PUT (1, q, rb_root);
       	size_t bsize = GET_SIZE (HDRP (rb_root));
        int same = (rb_root == bp);
	if (same) f = rb_root;
	int dir = 1;
	int last;

        /* Search and push a red down */
        while (CHILD_GET (dir,q) != NULL){
                last = dir; 

                /* Update helpers */
                g = p, p = q;
                q = CHILD_GET (dir, q);
                bsize = GET_SIZE (HDRP (q));
		
                if (same) {     // if we found already, just go down. TODO:WIERD
			if (f == q) dir = 0;
			else dir = 1;
                }
                else {
                        /* Save found best-fit block pointer at f */
                        if (bsize == size) {            // if block size is equal to wanted size, 
                                if (q == bp) {		// found required block.
					same = 1;
				    	f = q;
				}
				dir = (q < bp);
                        }                              
                	else dir = (bsize < size);
		}
/*
	        printf ("g, p, q is %x, %x, %x\n", g, p, q);  
*/
//		printf ("bsize, size is %u, %d\n", bsize, size);
		printf ("bsize is %u, point %x\n", bsize, (char *)bsize);
/*
                printf ("same is %d, dir is %d, f is %x\n", same, dir, f);
                printf ("g, p, q is_red is %d, %d, %d\n", IS_RED (g), IS_RED (p), IS_RED (q));
		char *left = CHILD_GET (0, q);
                char *right = CHILD_GET (1, q);
                printf ("left  is %x, ", left);
                printf ("right is %x\n", right);
*/

                /* Push the red node down */
                if (!(IS_RED(q)) && !(IS_RED (CHILD_GET (dir, q)))){    // double black
                	if ((IS_RED (CHILD_GET (!dir, q)))) {
			    	CHILD_PUT (last, p, rot_single (q, dir));
        	                p = CHILD_GET (last, p);
                	}
	                else if (!(IS_RED (CHILD_GET (!dir, q)))) {
        	                char *s = CHILD_GET (!last, p);
 	
		                if (s != NULL){
                	        	if (!(IS_RED (CHILD_GET (!last, s))) && !(IS_RED (CHILD_GET (last, s)))){
                        	        	/* Color flip */
                                	        SET_RB (0, HDRP (p));
                                        	SET_RB (1, HDRP (s));
	                                        SET_RB (1, HDRP (q));
        	                        }
                	                else {
                        	                int dir2 = (CHILD_GET (1, g) == p);
	
        	                                if (IS_RED (CHILD_GET (last, s))) {
                	                                CHILD_PUT (dir2, g, rot_double (p, last));
						}
                        	                else if (IS_RED (CHILD_GET (!last, s))) {
                                	                CHILD_PUT (dir2, g, rot_single (p, last));
						}

	                                        /* Ensure correct coloring */
        	                                SET_RB (1, CHILD_GET (dir2, g));
                	                        SET_RB (0, CHILD_GET (0, CHILD_GET (dir2, g)));
                        	                SET_RB (0, CHILD_GET (1, CHILD_GET (dir2, g)));
                                	}
                        	}
                	}
		}
        }

	printf ("	found2 is %x\n", f);
	
        /* Replace and remove if found */
        if (f != NULL) {
                /* Find f's parent */
                char *fparent = find_parent (f);
                if (fparent == NULL) {  // something wrong.
                        printf ("we can't find f's parent.\n");
                        abort();
                }
                /* Chain q with f's parent and f's children */
                CHILD_PUT (CHILD_GET (1, p) == q, p, CHILD_GET (!dir, q));
                if (f != q) {                                   // if f == q, enough.
                        CHILD_PUT (0, q, CHILD_GET (0, f));
                        CHILD_PUT (1, q, CHILD_GET (1, f));
                        CHILD_PUT (CHILD_GET (1, fparent) == f, fparent, q);
                }

        }

        /* Update root and make it black */
        rb_root = CHILD_GET (1, rb_head);
        if (rb_root != NULL) SET_RB (0, HDRP (rb_root));

        return f;
}
//TODO :: needed?
/*
 * find_parent - find parent node at the rb tree. it is needed to maintain the smallest
 * 		 free block size small, simultaneously not use recursion.
 */
static char *find_parent (char *child) {

        /* setup helper node pointers */
	size_t size = GET_SIZE (HDRP (child));
	char *p = NULL;
        char *q = rb_head;
        int dir = 1;
        size_t bsize;

        /* Search child's parent */
        while (CHILD_GET (dir,q) != NULL){

		p = q;
                q = CHILD_GET (dir, q);		// update iterator 
		bsize = GET_SIZE (HDRP (q));
    
		if (bsize == size) {		// if find same size, 
			if (q == child) {
//				printf ("found parent is %x\n", p);
				return p;
			}
			dir = (q < child);	
		}                
		else dir = (bsize < size);
	}

	return NULL;
}
