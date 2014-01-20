/*
 * 15213 ICS - Fall 2013 
 *     malloc lab
 *      Name : Enze Li 
 * Andrew id : enzel
 *
 * --- Implementation ---
 * Segregated free list: Maintain 10 buckets of free blocks. 
 * Semi-best-fit: Search from lower bucket to higher ones, 
 *				choose the best one among the first 5 fits in one bucket,
 *				or return best fit so far when jumping to a higher bucket.
 * Extend-heap: Initialize with heap size CHUNKSIZE/4.
 * 				When heap is small, only double its size;
 * 				When heap is large, extend it by CHUNCKSIZE.
 *
 * --- Reference ---
 * Some starter code is from CS:APP.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8


/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Basic constants and macros FROM CS:APP code sample*/
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<10)  /* Extend heap by this amount (bytes) */ 
#define SEG_COUNT	10     	/* Number of free list segragations */

#define MAX(x, y) ((x) > (y) ? (x) : (y))  
#define MIN(x, y) ((x) < (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Min block size and compute block size according to payload size */
#define MIN_BLK_SIZE 	(3*DSIZE)
#define BLK_SIZE(size) 	(((size)<=2*DSIZE) ? MIN_BLK_SIZE : ALIGN(DSIZE+size))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* Given block ptr bp, compute address of next and previous free blocks */
#define NEXT_FREEBLKP(bp)  			(*(void **)(bp)) 
#define PREV_FREEBLKP(bp)  			(*(void **)(bp + DSIZE)) 

/* Set next and previous blocks of a free block in the free list */
#define SET_NEXT_FREEBLK(bp, ptr) 	(NEXT_FREEBLKP(bp) = ptr)
#define SET_PREV_FREEBLK(bp, ptr)  	(PREV_FREEBLKP(bp) = ptr)
	
/* $end mallocmacros */

/* Global variables*/
static char *heap_listp = 0;  		/* Pointer to first block in heap */  
static char *seg_listp[SEG_COUNT];  /* Pointers to each segregation */

/* malloc key functions */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

/* functions for seg free list */
static void add_to_seglist(void *bp);
static void delete_from_seglist(void *bp);
static int seg_idx(size_t blksize);

/* functions for checking correctness */
static void checkblock(void *bp);
static void printblock(void *bp);
static void checkfreelist(void);
static void printfreeblock(void *bp);
static void printfreelist(void);

/*
 * mm_init: initialize heap and seg free list. 
 * 	return -1 on error, 0 on success.
 */
int mm_init(void) {
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
	   return -1; 

    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);

    /* Create the initial empty seg list */
    for (int i = 0; i < SEG_COUNT; ++i){
    	seg_listp[i] = NULL;
    }

    /* Extend the empty heap with a free block of (CHUNKSIZE/4) bytes */
    if (extend_heap(CHUNKSIZE/(WSIZE*4)) == NULL)  
    	return -1;

    /* initialization succeeds */
    return 0;
}

/*
 * malloc: return ptr to allocated block with payload >= size
 */
void *malloc (size_t size) {
    size_t blksize = BLK_SIZE(size);    /* Compute the block size needed */
    size_t esize; 						/* Size to extend heap if needed */
    char *bp;

    /* init heap if heap is empty */
    if (heap_listp == 0) 
    	mm_init();

    /* ignore spurious requests */
    if (size == 0)
    	return NULL;

    /* search for a fit, place in it if found */
    if ((bp = find_fit(blksize)) != NULL) {  
    	place(bp, blksize);                  
    } 

    /* No fit found. Get more memory and place the block */
    /* If heap is small, only double the heapsize; else use CHUNKSIZE */
    else { 
	    esize = MAX(blksize, MIN(mem_heapsize(), CHUNKSIZE)); 
	    if ((bp = extend_heap(esize/WSIZE)) == NULL)  
	    	return NULL;                                   
	    place(bp, blksize);  
	}

    return bp;
}

/*
 * free: free the block pointed to by ptr
 */
void free (void *ptr) {
    if (ptr == 0) 
    	return;

    size_t size = GET_SIZE(HDRP(ptr));

	if (heap_listp == 0) 
		mm_init(); 

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * realloc: re-allocate an allocated block
 * 		malloc a new block and copy data to it
 */
void *realloc (void *oldptr, size_t size) {
	size_t oldsize;
	void *newptr;

	/* no old ptr, just malloc */
	if (oldptr == NULL) {
		return malloc(size);
	} 

	/* free block when size == 0 */
	if (size == 0){
		free(oldptr);
		return 0;
	} 

	/* malloc a new block and copy original data */
	newptr = malloc(size);
    if(!newptr) 
    	return 0;
    oldsize = GET_SIZE(HDRP(oldptr));
    if(size < oldsize)
        oldsize = size;
    memcpy(newptr, oldptr, oldsize);
    free(oldptr);

    return newptr;
}

/*
 * calloc - malloc requested bytes and set all bits to zero
 */
void *calloc (size_t nmemb, size_t size) {
  	size_t bytes = nmemb * size;
  	void *newptr;

  	newptr = malloc(bytes);
  	memset(newptr, 0, bytes);

  	return newptr;
}

/*
 * Return whether the pointer is in the heap.
 * Useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * Useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * Print location, header and footer of a block.
 */
static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
    	printf("%p: EOL\n", bp);
    	return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
			(int)hsize, (halloc ? 'a' : 'f'), 
			(int)fsize, (falloc ? 'a' : 'f')); 
}

/* 
 * Print details of a free block with printblock(),
 * 	plus its connections in seg list.
 */
static void printfreeblock(void *bp){
	printblock(bp);
	printf("PREV_FREEBLKP: %p\n", PREV_FREEBLKP(bp));
	printf("NEXT_FREEBLKP: %p\n", NEXT_FREEBLKP(bp));
}

/*
 * Print out all blocks in seg free list by bucket order.
 */
static void printfreelist(void){
	char *bp;
	printf("-> Start printing seg list:\n");
	for (int i = 0; i < SEG_COUNT; ++i){
		printf("-> Seg_listp[%d]:\n", i);
		for (bp = seg_listp[i]; bp != NULL ; bp = NEXT_FREEBLKP(bp)) {
		    printfreeblock(bp);
	    }
	}
    printf("<- End printing seg list.\n");
}


 /* 
  * check correctness of the seg free list. print list upon error.
  * things to check: 
  *	- block correctness (double check!)
  * - block in the list must free
  * - block-bucket consistency
  * - total number of free blocks consistent with heap
  */
static void checkfreelist(void){ 
	char *bp;
	int listfreecount = 0;
	int heapfreecount = 0;

	for (int i = 0; i < SEG_COUNT; ++i){
		for (bp = seg_listp[i]; bp != NULL; bp = NEXT_FREEBLKP(bp)) {
			listfreecount++; 	/* count free blocks in list */
			checkblock(bp); 	/* check block correctness */

			/* check if block is free */
			if (GET_ALLOC(HDRP(bp))) {
			    printf("ERROR %p: allocated block in free list.\n", bp);
			    printfreelist();
			    exit(-1);
			}

			/* check block-bucket consistency */
			if (seg_idx(GET_SIZE(HDRP(bp))) != i) {
			    printf("ERROR %p: block located in wrong bucket.\n", bp);
			    printfreelist();
			    exit(-1);
			}
	    }	
	}

	/* check total number of free blocks in heap */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp))) {
			printf("Found free in heap:%p\n", bp);
			printblock(bp);
			heapfreecount++;
	    }
	}

    if (listfreecount != heapfreecount){
    	printf("ERROR: numbers of free blocks inconsistent with heap.\n");
    	exit(-1);
    }

}

/*
 * check correctness of a single block
 * things to check: 
 *	- in-heapness
 *  - alignment
 * 	- header-footer consistency
 *	- coalesing correctness
 */
static void checkblock(void *bp) 
{
	/* check if the block is in the heap */       
    if( !in_heap(bp)) {
        printf("ERROR: %p is not in mem heap \n", bp);     
        exit(-1);   
    }

	/* check alignment */
    if (!aligned(bp)){
		printf("Error: %p is not doubleword aligned\n", bp);
		exit(-1);
	}

	/* check header-footer consistency */
    if (GET(HDRP(bp)) != GET(FTRP(bp))){
		printf("Error: header does not match footer\n");
		exit(-1);
	}

	/* check coalescing correctness */
    if (GET_ALLOC(HDRP(bp)) == 0 
    		&& NEXT_BLKP(bp) != NULL 
        	&& GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0) 
    {
        printf("ERROR: %p is not coalesced with next block\n", bp);        
        // print_all();
        exit(-1);
    }
}

/*
 * mm_checkheap: check heap consistency and free list consistency
 */
void mm_checkheap(int verbose) {
    char *bp = heap_listp;

    if (verbose)
		printf("Heap (%p):\n", heap_listp);

	/* check prologue */
    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))){
		printf("Bad prologue header\n");
		exit(-1);
	}
	checkblock(heap_listp);

	/* check each block in the heap */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose) 
			printblock(bp);
		checkblock(bp);
    }

    /* check epilougue */
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))){
		printf("Bad epilogue header\n");
		exit(-1);
	}

	/* check correctness of the seg free list */
	checkfreelist();
}

/*
 * Boundary tag coalescing. Return ptr to coalesced block.
 * Maintain seg free list at the same time.
 */
static void *coalesce(void *bp) 
{
    char *prev_block = PREV_BLKP(bp);
    char *next_block = NEXT_BLKP(bp);
    size_t prev_alloc = GET_ALLOC(FTRP(prev_block));
    size_t next_alloc = GET_ALLOC(HDRP(next_block));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {				/* Case 1 */
    	/* bp stay put */
    	add_to_seglist(bp);
	    return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
		/* bp stay put */
		size += GET_SIZE(HDRP(next_block));
		delete_from_seglist(next_block);

		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size,0));

		add_to_seglist(bp);
	    return bp;
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
    	bp = prev_block;
		size += GET_SIZE(HDRP(prev_block));
		delete_from_seglist(prev_block); 

		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));

		add_to_seglist(bp);
	    return bp;
    }

    else {                                     /* Case 4 */
    	delete_from_seglist(prev_block);
    	delete_from_seglist(next_block);
		size += (GET_SIZE(HDRP(prev_block)) + GET_SIZE(FTRP(next_block)));
		PUT(HDRP(prev_block), PACK(size, 0));
		PUT(FTRP(next_block), PACK(size, 0));

		bp = prev_block;	
		add_to_seglist(bp);
	    return bp;
    }
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
		return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 

    /* Coalesce if the adjacent blocks are free */
    return coalesce(bp);
}

/* 
 * place - Place block of asize bytes at start of free block bp,
 *         Split if remainder would be at least minimum block size
 *		   Maintain free list at the same time.
 */
static void place(void *bp, size_t blksize)
{
	char *nextp; 
    size_t freesize = GET_SIZE(HDRP(bp)); 

    if (!GET_ALLOC(bp)){
	    delete_from_seglist(bp); 
	} else {
		printf("Error: Attempt to place in allocated block %p.\n", bp);
		return;
	}

    if ((freesize - blksize) >= MIN_BLK_SIZE) { 
		PUT(HDRP(bp), PACK(blksize, 1));
		PUT(FTRP(bp), PACK(blksize, 1));
		/* split free block and put the remainder in seg list */
		nextp = NEXT_BLKP(bp);
		PUT(HDRP(nextp), PACK(freesize-blksize, 0));
		PUT(FTRP(nextp), PACK(freesize-blksize, 0));
		add_to_seglist(nextp);
    } else { 
    	/* allocate all freesize for blksize */
		PUT(HDRP(bp), PACK(freesize, 1));
		PUT(FTRP(bp), PACK(freesize, 1));
    } 
}

/* 
 * find_fit - Find a fit for a block with required size .
 * 			  Return ptr to that block, or NULL if no fit found.
 * Strategy: Search from the lowest seg list index.
 * 			 Return the best one of first 5 fits in one bucket.
 */

 static void *find_fit(size_t blksize)
{
    void *bp;
    void *bestfit = NULL;
    unsigned int remain = (~0x0);
    int count = 0;

    /* search from the lowest seg_idx */
    for (int i = seg_idx(blksize); i < SEG_COUNT; ++i) {

    	/* return when jumping to a higher bucket with a fit */
	    if (bestfit != NULL) 
	    	return bestfit;

	    /* return best fit among first 5 fits in the same bucket */
    	for (bp = seg_listp[i]; bp != NULL; bp = NEXT_FREEBLKP(bp)){
    		if (blksize <= GET_SIZE(HDRP(bp))) {
    			if ((GET_SIZE(HDRP(bp)) - blksize) < remain){
			    	bestfit = bp;
			    	remain = GET_SIZE(HDRP(bp)) - blksize;
			    }

			    count++;
			    if (count > 5) 
			    	return bestfit; 
    		}
    	}
    }

    return bestfit;
}


/*
 * Add a free block LIFO to seg list based on its size.
 */
static void add_to_seglist(void *bp){
	int idx = seg_idx(GET_SIZE(HDRP(bp)));

	/* no free block this bucket */
	if (seg_listp[idx] == NULL){ 	
		SET_PREV_FREEBLK(bp, NULL);
		SET_NEXT_FREEBLK(bp, NULL);
		seg_listp[idx] = bp;
	} 

	/* add block to the head of the bucket */
	else {
		SET_PREV_FREEBLK(bp, NULL);
		SET_NEXT_FREEBLK(bp, seg_listp[idx]);
		SET_PREV_FREEBLK(seg_listp[idx], bp);
		seg_listp[idx] = bp;
	}
}

/*
 * Delete a free block from seg free list.
 */
static void delete_from_seglist(void *bp){
	int idx = seg_idx(GET_SIZE(HDRP(bp)));
	char *prev_block = PREV_FREEBLKP(bp);
	char *next_block = NEXT_FREEBLKP(bp);

	/* clear the deleted block */
	SET_PREV_FREEBLK(bp, NULL);
	SET_NEXT_FREEBLK(bp, NULL);

	/* rewire connections of the list */
	if (prev_block == NULL){
		if (next_block == NULL){
			/* delete the only free block */
			seg_listp[idx] = NULL;
		} else {
			/* delete the first free block */
			seg_listp[idx] = next_block;
			SET_PREV_FREEBLK(next_block, NULL);
		}
	} 

	else if (next_block == NULL){
		/* delete the last free block */
		SET_NEXT_FREEBLK(prev_block, NULL);
	} 

	else {
		/* delete an intermediate free block */
		SET_PREV_FREEBLK(next_block, prev_block);
		SET_NEXT_FREEBLK(prev_block, next_block);
	}

}

/*
 * Return seg list index based on block size.
 */
static int seg_idx(size_t blksize){
	if (blksize <= 32) 			return 0;
	else if (blksize <= 64) 	return 1;
	else if (blksize <= 128) 	return 2;
	else if (blksize <= 256) 	return 3;
	else if (blksize <= 512) 	return 4;
	else if (blksize <= 1024) 	return 5;
	else if (blksize <= 2048) 	return 6;
	else if (blksize <= 4096) 	return 7;
	else if (blksize <= 8192) 	return 8;
	else  						return 9;
}
