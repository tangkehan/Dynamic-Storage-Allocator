/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: insert your documentation here. :)
 *
 *************************************************************************
 *
 * ADVICE FOR STUDENTS.
 * - Step 0: Please read the writeup!
 * - Step 1: Write your heap checker.
 * - Step 2: Write contracts / debugging assert statements.
 * - Good luck, and have fun!
 *
 *************************************************************************
 *
 * @author Kehan Tang <kehant@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printf(...) ((void)printf(__VA_ARGS__))
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, these should emit no code whatsoever,
 * not even from evaluation of argument expressions.  However,
 * argument expressions should still be syntax-checked and should
 * count as uses of any variables involved.  This used to use a
 * straightforward hack involving sizeof(), but that can sometimes
 * provoke warnings about misuse of sizeof().  I _hope_ that this
 * newer, less straightforward hack will be more robust.
 * Hat tip to Stack Overflow poster chqrlie (see
 * https://stackoverflow.com/questions/72647780).
 */
#define dbg_discard_expr_(...) ((void)((0) && printf(__VA_ARGS__)))
#define dbg_requires(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_assert(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_ensures(expr) dbg_discard_expr_("%d", !(expr))
#define dbg_printf(...) dbg_discard_expr_(__VA_ARGS__)
#define dbg_printheap(...) ((void)((0) && print_heap(__VA_ARGS__)))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/**
 * TODO: explain what chunksize is
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: explain what alloc_mask is
 */
static const word_t alloc_mask = 0x1;

/**
 * boundary_mask is the flag show the previous block is allocated or free
 */
static const word_t bound_alloc_mask = 0x1 << 1;

/**
 * mini_mask is the flag show if the previous block is a mini block
 */
static const word_t bound_mini_mask = 0x1 << 2;

/**
 * TODO: explain what size_mask is
 */
static const word_t size_mask = ~(word_t)0xF;

/*put the prev and next pointer together*/
typedef struct freeNode {
    struct block *prev;
    struct block *next;
} freeNode_t;

/*put the payload and prev and next pointer in the union*/
typedef union {
    char *payload;
    freeNode_t free_node;
} blockBody_t;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A pointer to the block payload.
     *
     * TODO: feel free to delete this comment once you've read it carefully.
     * We don't know what the size of the payload will be, so we will declare
     * it as a zero-length array, which is a GNU compiler extension. This will
     * allow us to obtain a pointer to the start of the payload. (The similar
     * standard-C feature of "flexible array members" won't work here because
     * those are not allowed to be members of a union.)
     *
     * WARNING: A zero-length array must be the last element in a struct, so
     * there should not be any struct fields after it. For this lab, we will
     * allow you to include a zero-length array in a union, as long as the
     * union is the last field in its containing struct. However, this is
     * compiler-specific behavior and should be avoided in general.
     *
     * WARNING: DO NOT cast this pointer to/from other types! Instead, you
     * should use a union to alias this zero-length array with another struct,
     * in order to store additional types of data in the payload memory.
     */
    char payload[0];

    /*
     * TODO: delete or replace this comment once you've thought about it.
     * Why can't we declare the block footer here as part of the struct?
     * Why do we even have footers -- will the code work fine without them?
     * which functions actually use the data contained in footers?
     */
} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/*set my segregated block lists*/
static int num = 15;
static block_t *free_head[15];

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc, bool prev_mini) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }

    if (prev_alloc) {
        word |= bound_alloc_mask;
    }

    if (prev_mini) {
        word |= bound_mini_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + dsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Returns the previous allocation status of a given header value.
 *
 * This is based on the second lowest bit of the header value.
 *
 * @param[in] word
 * @return The previous allocation status correpsonding to the word
 */
static bool extract_prev_alloc(word_t word) {
    return (bool)(word & bound_alloc_mask);
}

/**
 * @brief Returns the previous allocation status of a block, based on its
 * header.
 * @param[in] block
 * @return The previous allocation status of the block
 */
static bool get_prev_alloc(block_t *block) {
    return extract_prev_alloc(block->header);
}

/**
 * @brief Returns the previous block-size status of a given header value.
 *
 * This is based on the third lowest bit of the header value.
 *
 * @param[in] word
 * @return The previous block-size status correpsonding to the word
 */
static bool extract_prev_mini(word_t word) {
    if ((word & bound_mini_mask) == 0) {
        return false;
    }

    return true;
}

/**
 * @brief Returns the previous block-size status of a block, based on its
 * header.
 * @param[in] block
 * @return The previous block-size status of the block
 */
static bool get_prev_mini(block_t *block) {
    return extract_prev_mini(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == (char *)mem_heap_hi() - 7);
    block->header = pack(0, true, false, false);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 * *@param[in] prev_alloc The allocation status of the previous block
 * @param[in] prev_mini The size status of the new block if is mini size block
 */
static void write_header(block_t *block, size_t size, bool alloc,
                         bool prev_alloc, bool prev_mini) {
    dbg_requires(block != NULL);
    /*write the header*/
    block->header = pack(size, alloc, prev_alloc, prev_mini);
}

/*write the footer
 * The mini size don't have footer
 */
static void write_footer(block_t *block, size_t size, bool alloc,
                         bool prev_alloc, bool prev_mini) {
    if (get_size(block) <= min_block_size) {
        return;
    }
    word_t *footerp = header_to_footer(block);
    *footerp = pack(size, alloc, prev_alloc, prev_mini);
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");

    if (block == NULL) {
        return NULL;
    }

    if (get_size(block) == 0) {
        return NULL;
    }

    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    if (block == NULL) {
        return NULL;
    }

    if (get_size(block) == 0) {
        return NULL;
    }

    if (get_prev_mini(block)) {
        return (block_t *)((char *)block - min_block_size);
    }

    word_t *footerp = find_prev_footer(block);
    return (block_t *)((char *)block - extract_size(*footerp));
}

static void connect_free_next(block_t *block, block_t *block_next) {
    if (!block || get_size(block) < min_block_size) {
        return;
    }
    blockBody_t body;
    body.payload = block->payload;
    body.free_node.next = block_next;
}

static void connect_free_prev(block_t *block, block_t *block_prev) {
    if (!block || get_size(block) <= min_block_size) {
        return;
    }
    blockBody_t body;
    body.payload = block->payload;
    body.free_node.prev = block_prev;
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/****************************Self Defined Helper****************************/
// check for epilogue and prologue blocks
// root and heap_start
// flag is allocted and the size = 0
static bool check_epilogue_prologue(block_t *block) {
    if (!get_alloc(block)) {
        return false;
    } else if ((get_size(block) != 0)) {
        return false;
    }

    return true;
}

// Check each block's address alignment.
// check if the block's address is aligned with the dsize 16-byte
static bool check_align(block_t *block) {
    // if aligned with dsize
    if ((uintptr_t)(char *)(block->payload) % dsize != 0) {
        return false;
    }

    return true;
}

// Check blocks lie within heap boundaries.
static bool check_bound(block_t *block) {
    // if the block's address is out the the range
    // mem_heap_hi----the high address of the heap
    // mem_heap_lo----the low address of the heap
    if ((uintptr_t)(char *)block < (uintptr_t)mem_heap_lo() ||
        (uintptr_t)(char *)block > (uintptr_t)mem_heap_hi()) {
        return false;
    }
    return true;
}

// Check each block's header and footer: size (minimum size)
// previous/next allocate/free bit consistency,
// header and footer matching each other.
static bool check_block(block_t *block) {
    // check minimum size
    if (get_size(block) < min_block_size) {
        return false;
    }

    // check allocation flag and free bit consistency
    if (!get_alloc(block) && get_size(block) > min_block_size) {
        word_t footer;
        footer = *header_to_footer(block);
        if (extract_alloc(footer) != get_alloc(block)) {
            return false;
        }

        if (extract_size(footer) != get_size(block)) {
            return false;
        }
    }

    return true;
}

// Check coalescing: no consecutive free blocks in the heap.
static bool check_coalesce(block_t *block, block_t *block_prev) {
    block_t *block_next = find_next(block);
    bool prev_status = true;
    bool next_status = true;
    if (block_prev != NULL) {
        prev_status = get_alloc(block_prev);
    }

    if (block_next != NULL) {
        next_status = get_alloc(block_next);
    }

    if ((get_alloc(block) || next_status) &&
        (get_alloc(block) || prev_status)) {
        return true;
    }

    return true;
}
/******************************************************************/

/* 17-32 33-64 65-128 ......*/
/*find which free_head list to put the block*/
static int find_index(size_t size) {
    // start from list 0
    int index = 0;

    for (size_t assigned_size = min_block_size; assigned_size < size;
         assigned_size *= 2) {
        if (index < num - 1) {
            index += 1;
        } else {
            break;
        }
    }

    return index;
}

static block_t *next_free(block_t *block) {
    if (block == NULL) {
        return NULL;
    }

    if (get_alloc(block)) {
        return NULL;
    }
    // only free blocks have free Nodes
    blockBody_t body;
    body.payload = block->payload;
    return body.free_node.next;
}

static block_t *prev_free(block_t *block) {
    // only free blocks have free Nodes
    if (block == NULL) {
        return NULL;
    }

    if (get_alloc(block)) {
        return NULL;
    }
    // mini blocks only iterator with next pointer to find it
    if (get_size(block) <= min_block_size) {
        if (!block || get_alloc(block) || get_size(block) > min_block_size) {
            return NULL;
        }

        // find the free list for mini block
        size_t size = get_size(block);
        int index = find_index(size);

        // iterator over the list, double pointer to find the previous one
        block_t *target_free_block = free_head[index];
        block_t *block_prev = NULL;

        while (target_free_block) {
            if (target_free_block == block) {
                return block_prev;
            } else {
                block_prev = target_free_block;
                target_free_block = next_free(target_free_block);
            }
        }
        return NULL;
    }
    blockBody_t body;
    return body.free_node.prev;
}

static void free_add(block_t *block) {
    if (block == NULL) {
        return;
    }

    size_t size = get_size(block);
    int index = find_index(size);
    block_t *block_next = free_head[index];
    block_t *block_prev = NULL;

    // connect all free blocks
    connect_free_prev(block_next, block);
    connect_free_prev(block, block_prev);
    connect_free_next(block, block_next);
    connect_free_next(block_prev, block);

    // inset at head so update it
    free_head[index] = block;
}

static void free_remove(block_t *block) {
    if (block == NULL) {
        return;
    }

    size_t size = get_size(block);
    int index = find_index(size);

    block_t *prev = prev_free(block);
    block_t *next = next_free(block);

    // remove current block
    connect_free_prev(next, prev);
    connect_free_next(prev, next);

    // update head only when the head is removed
    if (block == free_head[index]) {
        free_head[index] = next;
    }
}

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @return
 */
static block_t *coalesce_block(block_t *block) {
    /*
     * TODO: delete or replace this comment once you're done.
     *
     * Before you start, it will be helpful to review the "Dynamic Memory
     * Allocation: Basic" lecture, and especially the four coalescing
     * cases that are described.
     *
     * The actual content of the function will probably involve a call to
     * find_prev(), and multiple calls to write_block(). For examples of how
     * to use write_block(), take a look at split_block().
     *
     * Please do not reference code from prior semesters for this, including
     * old versions of the 213 website. We also discourage you from looking
     * at the malloc code in CS:APP and K&R, which make heavy use of macros
     * and which we no longer consider to be good style.
     */

    // find the next and prev consecutive block on the heap
    block_t *block_next = find_next(block);
    block_t *block_prev;

    // get the consecutive blocks' alloc status if allocated or free
    bool block_next_status = get_alloc(block_next);
    bool block_prev_status = get_prev_alloc(block);

    size_t size = get_size(block);

    // case 1   alloc --- alloc
    if ((block_next_status && block_prev_status)) {
        // insert the block to the root and connect
        free_add(block);
    }

    // case 2    alloc --- free
    else if ((block_prev_status && !block_next_status)) {

        free_remove(block_next);
        // get block size and next block size
        size_t next_block_size = get_size(block_next);
        size_t total_size = size + next_block_size;

        write_header(block, total_size, false, get_prev_alloc(block),
                     get_prev_mini(block));
        write_footer(block, total_size, false, false, false);
        free_add(block);

    }

    // case 3   free --- alloc
    else if ((!block_prev_status && block_next_status)) {

        block_prev = find_prev(block);

        free_remove(block_prev);
        // get block size and prev block size
        size_t prev_block_size = get_size(block_prev);
        size_t total_size = size + prev_block_size;

        write_header(block_prev, total_size, false, get_prev_alloc(block_prev),
                     get_prev_mini(block_prev));
        write_footer(block_prev, total_size, false, false, false);
        // update block for futher next block status change
        block = block_prev;
        free_add(block);
    }

    // case 4  free --- free
    else {
        block_prev = find_prev(block);
        free_remove(block_prev);
        free_remove(block_next);
        // merge both area
        size_t prev_block_size = get_size(block_prev);
        size_t next_block_size = get_size(block_next);
        size_t total_size = size + prev_block_size + next_block_size;

        write_header(block_prev, total_size, false, get_prev_alloc(block_prev),
                     get_prev_mini(block_prev));
        write_footer(block_prev, total_size, false, false, false);
        // update block for futher next block status change
        block = block_prev;
        free_add(block);
    }
    // remember to update block_next's status
    block_next = find_next(block);
    bool is_curr_mini = false;
    if (get_size(block) == min_block_size) {
        is_curr_mini = true;
    }
    write_header(block_next, get_size(block_next), get_alloc(block_next), false,
                 is_curr_mini);

    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk((intptr_t)size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_header(block, size, false, get_prev_alloc(block),
                 get_prev_mini(block));
    write_footer(block, size, false, false, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_header(block_next, 0, true, false, false);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    size_t block_size = get_size(block);

    // we can split out a mini block
    if ((block_size - asize) >= min_block_size) {
        write_header(block, asize, true, get_prev_alloc(block),
                     get_prev_mini(block));

        block_t *block_next = find_next(block);

        bool is_prev_mini = false;
        if (asize == min_block_size) {
            is_prev_mini = true;
        }
        // update block_next status
        write_header(block_next, block_size - asize, false, true, is_prev_mini);
        write_footer(block_next, block_size - asize, false, false, false);
        dbg_ensures(mm_checkheap(__LINE__));
        free_add(block_next);

        // write next next block to update its prev mini
        bool is_current_free_mini = false;
        if (block_size - asize == min_block_size) {
            is_current_free_mini = true;
        }
        block_t *block_next_next = find_next(block_next);
        write_header(block_next_next, get_size(block_next_next),
                     get_alloc(block_next_next), false, is_current_free_mini);
    } else {
        block_t *block_next = find_next(block);
        // write next block to update its prev mini
        bool is_current_free_mini = false;
        if (block_size == min_block_size) {
            is_current_free_mini = true;
        }
        // allocated block only have headers
        write_header(block_next, get_size(block_next), get_alloc(block_next),
                     true, true);
        dbg_ensures(mm_checkheap(__LINE__));
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    int index = find_index(asize);

    for (; index < num; index++) {
        block_t *block = free_head[index];
        // first fit
        while (block) {
            size_t size = get_size(block);
            // minimize internal fragmentation
            if (asize <= size) {
                return block;
            }
            block = next_free(block);
        }
    }
    return NULL; // no fit found
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] line
 * @return
 */
bool mm_checkheap(int line) {
    /*
     * TODO: Delete this comment!
     *
     * You will need to write the heap checker yourself.
     * Please keep modularity in mind when you're writing the heap checker!
     *
     * As a filler: one guacamole is equal to 6.02214086 x 10**23 guacas.
     * One might even call it...  the avocado's number.
     *
     * Internal use only: If you mix guacamole on your bibimbap,
     * do you eat it with a pair of chopsticks, or with a spoon?
     */
    // dbg_printf("I did not write a heap checker (called at line %d)\n", line);

    block_t *epilogue = (block_t *)((char *)mem_heap_hi() - 7);
    block_t *prologue = (block_t *)((char *)mem_heap_lo());
    block_t *block = heap_start;
    block_t *block_prev = NULL;

    if (!check_epilogue_prologue(epilogue)) {
        dbg_printf("Error: check epilogue prologue\n");
        return false;
    }

    while (get_size(block) > 0) {
        if (!check_align(block)) {
            dbg_printf("Error: check align\n");
            return false;
        }

        if (!check_bound(block)) {
            dbg_printf("Error: check bound\n");
            return false;
        }

        if (!check_block(block)) {
            dbg_printf("Error: check block\n");
            return false;
        }

        if (!check_coalesce(block, block_prev)) {
            dbg_printf("Error: check coalesce\n");
            return false;
        }

        block_prev = block;
        block = find_next(block);
    }

    if (!check_epilogue_prologue(prologue)) {
        dbg_printf("Error: check epilogue prologue\n");
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    // initialize the head of free block list
    for (int i = 0; i < num; i++) {
        free_head[i] = NULL;
    }

    start[0] = pack(0, true, true, false); // Heap prologue (block footer)
    start[1] = pack(0, true, true, false); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    return true;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        if (!(mm_init())) {
            dbg_printf("Problem initializing heap. Likely due to sbrk");
            return NULL;
        }
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);
        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));
    free_remove(block);

    // Mark block as allocated
    size_t block_size = get_size(block);
    write_header(block, block_size, true, get_prev_alloc(block),
                 get_prev_mini(block));

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    if (!get_alloc(block)) {
        return;
    }
    // The block should be marked as allocated
    // dbg_assert(get_alloc(block));

    // Mark the block as free
    dbg_ensures(mm_checkheap(__LINE__));

    write_header(block, size, false, get_prev_alloc(block),
                 get_prev_mini(block));
    write_footer(block, size, false, false, false);

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    block_t *block = payload_to_header(ptr);
    block_t *block_next = find_next(block);
    size_t copysize;
    size_t block_size = get_size(block);
    void *newptr = NULL;

    // add possible free memory first
    if (!get_alloc(block_next)) {
        block_size += get_size(block_next);
    }

    size_t asize = round_up(size + wsize, dsize);
    if (asize < min_block_size) {
        asize = min_block_size;
    }
    // the next block has enough space to store the more size
    if (block_size < asize) {
        newptr = malloc(size);
        // If malloc fails, the original block is left untouched
        if (newptr == NULL) {
            return NULL;
        }

        // Copy the old data
        copysize = get_payload_size(block); // gets size of old payload
        // if (size < copysize) {
        //     copysize = size;
        // }
        memcpy(newptr, ptr, copysize);

        // Free the old block
        free(ptr);
    } else {
        // Otherwise, proceed with reallocation
        if (!get_alloc(block_next)) {
            free_remove(block_next);
        }
        // rewrite the entire block
        write_header(block, block_size, true, get_prev_alloc(block),
                     get_prev_mini(block));
        split_block(block, asize);
        newptr = header_to_payload(block);
    }
    return newptr;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
