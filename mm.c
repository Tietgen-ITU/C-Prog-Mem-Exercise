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

/*
 * The implementation of the dynamic memory allocator uses a segregated free list
 * in order to manage the free block in the heap. The current implementation is built 
 * on top of the implementation from the book. The implementaition consists of two different
 * states of a memory block. An allocated and not allocated block.
 * 
 * They are different in terms of what data is being expected to be present in them.
 * 
 * Allocated block:
 * <HEADER>           - This consist of the size and an allocation status flag
 * <PAYLOAD>          - The blocks that can contain data from the user of the allocator
 * <FOOTER>           - This consist of the size and an allocation status flag
 * 
 * Free block:
 * <HEADER>           - This consist of the size and an allocation status flag
 * <PREVIOUS POINTER> - A pointer to the previous free block
 * <NEXT POINTER>     - A pointer to the next free block
 * <PAYLOAD>          - The blocks that can contain data from the user of the allocator
 * <FOOTER>           - This consist of the size and an allocation status flag
 *  
 * The next and previous pointers are gone one a block is allocated. 
 * The next and previous pointers points to the first byte of the payload.
 * 
 * The allocator has 10 free lists 
 * that contains specific size ranges(Rules for finding the specific 
 * list index based on size can be found in the 'get_free_list_index' function).
 * 
 * When the allocator wants to find a free block then it finds the first list
 * where it could be possible to get a block that "fits". If that is not possible 
 * then it moves on the next list in order to find a free block.
*/

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

/* Set the pointer address of the NEXT or PREV block pointer */
#define SET_FREE_P(p, np) (*(unsigned int *)(p) = (unsigned int)np)

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - (WSIZE)) 
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - (DSIZE)) // Skip next blocks prev, next and header block and go to footer

/* Get the pointer to the NEXT and PREV fields */
#define NEXT_FRBP(bp) ((char *)(bp) + WSIZE)
#define PREV_FRBP(bp) ((char *)(bp))

/* Get the NEXT or PREV free block */
#define NEXT_FREE_BLOCK(bp) (*(char **)NEXT_FRBP(bp))
#define PREV_FREE_BLOCK(bp) (*(char **)PREV_FRBP(bp))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - (WSIZE))))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - (DSIZE))))

// Global variables
static char *heap_listp;
static unsigned int num_free_lists = 10;
static char *free_lists[10];


/* Function definitions */

static void *insert_free_block(void *);
static void remove_free_block(void *);
static void *coalesce(void *);
static char *get_free_list(size_t);
static int get_free_list_index(size_t);
static void mm_check();
static void print_pointer_info(char *, void *);


/*
 * Get a free block that fits the given size
 * 
 * Input:
 * size - The size the block of memory should have
 * 
 * Returns:
 * A pointer to the block that can have the amount of data indicated by the size.
 * If no one of the free blocks can fulfill that requirement then it 
 * returns NULL.
*/
static void *find_fit(size_t size) {

    // Get index for free list based on size
    int index = get_free_list_index(size); 

    for(int i = index; i < num_free_lists; i++) {

        char *current = free_lists[i];

        if(current == NULL)
            continue;

        // Go through the list and take the first that fits
        while(current != NULL) {

            size_t current_size = GET_SIZE(HDRP(current)); 

            /* If the size of the current free block is greater than the requested
            then return it */ 
            if(current_size >= size)
                return current;
                
            current = NEXT_FREE_BLOCK(current);    
        }
    }

    return NULL;
}

/*
 * Place the block of memory by setting the header and footer to be allocated
 * with the specified adjusted size.
 * 
 * If the given block pointer has a size difference greater than or equal to 
 * 2 * DSIZE then it is going to split the block and insert the rest of the
 * splitted block into the free list
 * 
 * Inputs:
 * bp - pointer to the block of memory that should be placed
 * asize - the size that should be placed
*/
static void place(void *bp, size_t asize) {
    size_t size = GET_SIZE(HDRP(bp));
    size_t size_diff = size - asize;
    unsigned int should_split = size_diff >= 2 * DSIZE;
    
    remove_free_block(bp);

    if(!should_split) {

        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1)); 
    } else { // Split bp and inserted the rest into the free list
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        void *split_p = NEXT_BLKP(bp);
        PUT(HDRP(split_p), PACK(size_diff, 0));
        PUT(FTRP(split_p), PACK(size_diff, 0));
        insert_free_block(split_p);
    }
}

/*
 * Coalesces the memory block if possible
 * 
 * Input:
 * The block pointer to coalesce
 * 
 * Returns:
 * A pointer to the coalesced block
*/
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

/*
 * Extends the heap with more memory and inserts the free memory into the 
 * segregated free list.
 * 
 * Input:
 * The size to extend the heap with
 * 
 * Returns:
 * Pointer to the new free block of memory
*/
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

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
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    // Initialize the free lists. Ensure they are set to null
    for(int i = 0; i < num_free_lists; i++) 
        free_lists[i] = NULL;

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
 * Allocates a block of memory with the requested size.
 * 
 * Input:
 * size - The size that should be allocated
 * 
 * Returns:
 * The pointer to the allocated block of memory. 
 * If it is not able to allocate more memory then it returns NULL
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
            asize = 2 * DSIZE; // Sets size to 2 * DSIZE (for header and footer)
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
 * Freeing the block og memory and inserts it into the 
 * segregated free list.
 * 
 * Input:
 * bp - the block of memory to be free'ed
 */
void mm_free(void *bp) {

    // If the block pointer is null then do nothing...
    if(bp == NULL)
        return;

    // Set header and footer to signal that it is not allocated
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // Insert the free block into the segregated free list
    insert_free_block(bp);
}

/*
 * Extends the current allocated block if possible or if the size is below the current allocated size then it does nothing. 
 * If it is not possible then it reallocates the block of memory.
 * 
 * Inputs:
 * ptr - The pointer to the block of memory that needs to be allocated
 * size - The new size that it needs to be allocated to
 * 
 * Returns:
 * The pointer to the reallocated block of memory
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t aligned_size = ALIGN(size + DSIZE);
    size_t current_size = GET_SIZE(HDRP(ptr));

    // Handle cases where we do not extend the current block or reallocates it
    if(size < 0)
        return NULL;
    else if(size == 0) {
        mm_free(ptr); // Free the block since size is 0
        return NULL;
    } else if(current_size >= aligned_size) {
        return ptr; // We can return the same block since the aligned size fits in the current
    }

    void *oldptr = ptr;
    size_t old_size = GET_SIZE(HDRP(oldptr));
    void *old_next_ptr = NEXT_BLKP(oldptr);
    size_t old_next_size = GET_SIZE(HDRP(old_next_ptr));
    
    // If the next block is not alloacted and that the size is bigger then the requested size
    if(!GET_ALLOC(HDRP(old_next_ptr)) && (old_size+old_next_size) >= aligned_size) {

        size_t new_size = old_size + old_next_size;

        remove_free_block(old_next_ptr); // Remove the free block from free list

        PUT(HDRP(oldptr), PACK(new_size, 1));
        PUT(FTRP(oldptr), PACK(new_size, 1));

        return oldptr;
    } 

    /* If the block cannot be extended by the blocks beside it then we need
     * to allocate a new fresh block
    */
    void *newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    size_t copySize = *(size_t *)((char *)oldptr - WSIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*
 * Coalesces the bp and inserts the resulting_bp into the segregated free list
 *
 * Input:
 * A free block to be inserted
 * 
 * Returns:
 * The free block coalesced
*/
static void *insert_free_block(void *bp) {

    void *result_bp = coalesce(bp);
    char *free_listp = get_free_list(GET_SIZE(HDRP(result_bp)));
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

    // Sets the top of the list where the size of the new block should be in
    size_t size = GET_SIZE(HDRP(result_bp));
    int index = get_free_list_index(size);
    free_lists[index] = result_bp;

    return result_bp;
}

/*
 * Remove the block from the free list and binds the surounding free block together
 *
 * Input:
 * bp - The free block to be removed from the free list
*/
static void remove_free_block(void *bp) {

    size_t size = GET_SIZE(HDRP(bp));
    int free_list_index = get_free_list_index(size);

    void *next = NEXT_FREE_BLOCK(bp);
    void *prev = PREV_FREE_BLOCK(bp);

    // Remove previous block pointer refs
    SET_FREE_P(NEXT_FRBP(bp), NULL);
    SET_FREE_P(PREV_FRBP(bp), NULL); 

    /* 
    *   If the current block(that is going to be removed) 
    *   then set beginning of free_listp to the next pointer 
    */
    if(bp == free_lists[free_list_index])
        free_lists[free_list_index] = next;

    if(next != NULL && prev != NULL) {

        SET_FREE_P(NEXT_FRBP(prev), next);
        SET_FREE_P(PREV_FRBP(next), prev);
    } else if (next != NULL && prev == NULL) {

        SET_FREE_P(PREV_FRBP(next), NULL);
    } else if (next == NULL && prev != NULL) {

        SET_FREE_P(NEXT_FRBP(prev), NULL);     
    }

}

/*
 * Get the pointer to the first that the item size "fits" in
 * 
 * Input:
 * size - the size that the block could be in
 * 
 * Returns:
 * The pointer to the first block in the free linked list
*/
static char *get_free_list(size_t size) {

    return free_lists[get_free_list_index(size)];
}

/*
 * Gets the index that the size should be in
 *
 * Input:
 * size - The size that the list should be able to hold
 * 
 * Returns:
 * The index of the free list
*/
static int get_free_list_index(size_t size) { 
   if (size > 16384)
        return 9;
    else if (size > 8192)
        return 8;
    else if (size > 4096)
        return 7;
    else if (size > 2048)
        return 6;
    else if (size > 1024)
        return 5;
    else if (size > 512)
        return 4;
    else if (size > 256)
        return 3;
    else if (size > 128)
        return 2;
    else if (size > 64)
        return 1;
    else
        return 0; 
}

/****************************************
************* DEBUG UTILS ***************
****************************************/

/*
 * Checks that the block is allocated in the correct list
 * 
 * Inputs:
 * list_index - index that the block is currently located in
 * bp - block pointer to the current free block
*/
static void mm_check_size(int list_index, void *bp) {

    size_t size = GET_SIZE(HDRP(bp));

    if(size > 16384 && list_index == 9)
        return;
    else if ((size <= 16384 || size > 8192) && list_index == 8 )
        return;
    else if ((size <= 8192 || size > 4096) && list_index == 7)
        return;
    else if ((size <= 4096 || size > 2048) && list_index == 6)
        return;
    else if((size <= 2048 || size > 1024) && list_index == 5)
        return;
    else if((size <= 1024 || size > 512) && list_index == 4)
        return;
    else if((size <= 512 || size > 256) && list_index == 3)
        return;
    else if((size <= 256 || size > 128) && list_index == 2)
        return;
    else if((size <= 128 || size > 64) && list_index == 1)
        return;
    else if(size <= 64 && list_index == 0)
        return;
    else {
        printf("Block is not allocated in the correct list");
        abort();
    }
}


/*
Checks that the free lists is consistent

Input:
function_name - Name of the function that it is being called from
*/
static void mm_check(char *function_name) {


    printf("mm_check of %s \n", function_name);

    for(int i = 0; i < num_free_lists; i++) {
        void *current = free_lists[i];

        if(current == NULL) {
            printf("Nothing in free list nr. %d! \n \n", i);
            continue;
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

            mm_check_size(i, current);

            printf("\n");
            current = next;
        }
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