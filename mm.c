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
    "anti",
    /* First member's full name */
    "Andreas Nicolaj Tietgen",
    /* First member's email address */
    "anti@itu.dk",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define SET_FREE_P(p, np) (*(unsigned int *)(p) = (unsigned int)np)

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - (WSIZE)) 
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - (DSIZE)) // Skip next blocks prev, next and header block and go to footer

// https://www.tutorialspoint.com/cprogramming/c_pointer_to_pointer.htm
#define NEXT_FRBP(bp) ((char *)(bp) + WSIZE)
#define PREV_FRBP(bp) ((char *)(bp))
#define NEXT_FREE_BLOCK(bp) (*(char **)NEXT_FRBP(bp))
#define PREV_FREE_BLOCK(bp) (*(char **)PREV_FRBP(bp))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - (WSIZE))))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - (DSIZE))))

// Global variables
static char *heap_listp;
static int heap_size;
static char *free_listp;

/* Function definitions */

static void *insert_free_block(void *);
static void remove_free_block(void *);
static void *coalesce(void *);
static void mm_check();
static void print_pointer_info(char *, void *);



static void *find_fit(size_t size) {

    char *current = free_listp;

    while(current != NULL) {

        size_t current_size = GET_SIZE(HDRP(current)); 

        if(current_size >= size)
            return current;
            
        current = NEXT_FREE_BLOCK(current);    
    }

    return NULL;
}

static void place(void *bp, size_t asize) {
    size_t size = GET_SIZE(HDRP(bp));
    size_t size_diff = GET_SIZE(HDRP(bp)) - asize;
    unsigned int should_split = size_diff >= 2 * DSIZE;
    
    remove_free_block(bp);

    if(!should_split) {

        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1)); 
    } else {

        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        void *split_p = NEXT_BLKP(bp);
        PUT(HDRP(split_p), PACK(size_diff, 0));
        PUT(FTRP(split_p), PACK(size_diff, 0));

        insert_free_block(split_p);
    }
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) /* Case 1 */
        return bp;
    else if (prev_alloc && !next_alloc) { /* Case 2 */

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
        // Clean next and prev pointers of the right free block
        remove_free_block(NEXT_BLKP(bp));

        // Coalesce the two free blocks
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    } else if (!prev_alloc && next_alloc) { /* Case 3 */

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        // Clean next and prev pointers of the left free block
        remove_free_block(PREV_BLKP(bp));

        // Coalesce the two free blocks
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }
    else { /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));

        // Clean next and prev pointers of both the right and left free block
        remove_free_block(NEXT_BLKP(bp));
        remove_free_block(PREV_BLKP(bp));

        // Coalesce the three blocks into one common block
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp; 
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    heap_size += size;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    
    /* Coalesce if the previous block was free */
    return insert_free_block(bp);
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    heap_size = 4*WSIZE;
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(heap_size)) == (void *)-1)
        return -1;

    /* Alignment padding */
    PUT(heap_listp, 0);                          
    
    /* Prologue header */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */

    /* Epilogue header */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); 

    heap_listp += DSIZE; // Point to the first data bp

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}



/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
            asize = 2 * DSIZE; // Sets size to 2 * DSIZE (for header, next, prev and footer) and 1 DSIZE to keep alignment for data
    else
        asize = ALIGN(size + DSIZE); 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp; 
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {

    if(bp == NULL)
        return;

    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    insert_free_block(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - WSIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*
Inserts the free block as the first entry into the free list and coalesces it

Input:
A free block to be inserted

Returns:
The free block coalesced
*/
static void *insert_free_block(void *bp) {

    void *result_bp = coalesce(bp);
    char *old_free_listp = free_listp;

    // Check that the old free list pointer is not null
    if(old_free_listp != NULL) 
        SET_FREE_P(PREV_FRBP(old_free_listp), result_bp); // Insert old free list pointer
    else 
        SET_FREE_P(NEXT_FRBP(result_bp), NULL); 
    
    // Make sure that it doesn't set it self to be the next in the free list
    if(old_free_listp != result_bp)
        SET_FREE_P(NEXT_FRBP(result_bp), old_free_listp);

    /* 
    *  Since the new free block is being inserted 
    *  at the start of the list then there is no previous 
    */
    SET_FREE_P(PREV_FRBP(result_bp), NULL);

    free_listp = result_bp;

    return result_bp;
}

/*
Remove the block from the free list and binds the surounding free block together

Input:
bp - The free block to be removed from the free list
*/
static void remove_free_block(void *bp) {

    void *next = NEXT_FREE_BLOCK(bp);
    void *prev = PREV_FREE_BLOCK(bp);

    // Remove previous block pointer refs
    SET_FREE_P(NEXT_FRBP(bp), NULL);
    SET_FREE_P(PREV_FRBP(bp), NULL); 

    /* 
    *   If the current block(that is going to be removed) 
    *   then set beginning of free_listp to the next pointer 
    */
    if(bp == free_listp)
        free_listp = next;

    if(next != NULL && prev != NULL) {

        SET_FREE_P(NEXT_FRBP(prev), next);
        SET_FREE_P(PREV_FRBP(next), prev);
    } else if (next != NULL && prev == NULL) {

        SET_FREE_P(PREV_FRBP(next), NULL);
    } else if (next == NULL && prev != NULL) {

        SET_FREE_P(NEXT_FRBP(prev), NULL);     
    }

}

/****************************************
************* DEBUG UTILS ***************
****************************************/

/*
Checks that the free list is consistent

Input:
function_name - Name of the function that it is being called from
*/
static void mm_check(char *function_name) {

    void *current = free_listp;

    printf("mm_check of %s \n", function_name);

    if(current == NULL) {
        printf("Nothing in free list! \n \n");
        return;
    }

    // Go through heap
    while(current != NULL) {

        print_pointer_info("", current);
        
        int size_header = GET_SIZE(HDRP(current));
        int alloc_header = GET_ALLOC(HDRP(current));
        int alloc_footer = GET_ALLOC(FTRP(current));
        int size_footer = GET_SIZE(FTRP(current));

        void *next = NEXT_FREE_BLOCK(current);
        

        if(GET_ALLOC(HDRP(current))) {
            printf("There is something allocated in the free list \n");
            abort();
        }


        if(next == current) {
            printf("The current and next points to the same \n");
            abort();
        }

        if(size_footer != size_header || alloc_footer != alloc_header) {
            printf("Header and footer does not match! \n");
            abort();
        }

        printf("\n");
        current = next;
    }

    printf("\n");
}

/*
Prints information about the memory block at the pointer location

Inputs:
func_name - Name of the function it is being called from.
bp        - The pointer to the memory block that we want information from.
*/
static void print_pointer_info(char *func_name, void *bp) {

    void *bp_header = HDRP(bp);
    void *bp_footer = FTRP(bp);

    printf("--------- \n");
    printf("%s \n", func_name);
    printf("block addr: %p \n", bp);
    

    if(bp_header != NULL) {

        printf("POINTER ADD: %p \n", bp_header);
        printf("HEADER SIZE: %d \n", GET_SIZE(HDRP(bp)));
        printf("HEADER ALLOC: %d \n", GET_ALLOC(HDRP(bp)));
    }

    if(bp_footer != NULL) {

        printf("FOOTER SIZE: %d \n", GET_SIZE(FTRP(bp)));
        printf("FOOTER ALLOC: %d \n", GET_ALLOC(FTRP(bp)));
        printf("FOOTER ADD: %p \n", FTRP(bp));
    }

    printf("next addr: %p \n", NEXT_FREE_BLOCK(bp));
    printf("prev addr: %p \n", PREV_FREE_BLOCK(bp));
}