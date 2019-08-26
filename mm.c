/* 
 * mm.c - Malloc implementation with external segregated lists
 * 
 * We implemented a heap memory allocator, using:
 *      - Explicit segregated free lists, with address-ordered insertion policy
 *      - We keep multiple pointers for each power of two size class
 *      - Seglist is kept on the heap 
 *
 * Specifics : 
 *   Malloc :
 *      - we search for an optimal sized free block in the seglist
 *      - if its too big, we resize it
 *      - if we didn't find one, we look at the heap's last block
 *      - if its free, and big enough ("big" for us is 50*SIZE_T, but can be chosen arbitrarly), we'll only allocate the space necessary to fit the requested size
 *      - if its free and small, we'll leave it free and allocate another block. This is our policy to regroup small blocks together (even if it increases fragmentation a bit)
 *      - if its not free, and the requested size is large, allocate the needed space
 *      - if its not free and the requested block is small, allocate twice the space : Again, this enables small blocks to be near each other. 
 *
 *   Free : 
 *      - Free the block, and coalesce with neighbors
 *
 *   Realloc : 
 *      - Try to fit the block in the neighboring free blocks. If there is enough space, we'll move the content if needed to resize the block without allocating anything new
 *      - If not, but if this block is the last, we'll add to the heap only the space needed to make this block big enough, then move data to that last block
 *      - If the last block is full, simply add the requested size to the heap by calling mm_malloc
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
    "Pickle Rick",
    /* First member's full name */
    "Pierre-Jean Grenier",
    /* First member's email address */
    "pierre-jean.grenier@polytechnique.edu",
    /* Second member's full name (leave blank if none) */
    "Julien Piet",
    /* Second member's email address (leave blank if none) */
    "julien.piet@polytechnique.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

// header is a size_t
#define GETSIZE(header) ((header) & -2)
// header is a size_t
#define GETDIRTYBIT(header) ((header) & 1)
// header_ptr is a void*
#define GETFOOTER(header_ptr) ((header_ptr) + GETSIZE(*(size_t *)(header_ptr)) - SIZE_T_SIZE)
#define GETNEXTBLOCK(header_ptr) (header_ptr + GETSIZE(*(size_t *)(header_ptr)))
// header_ptr is a void*
#define GETNEXTFREE(header_ptr) (*(size_t *)((header_ptr) + SIZE_T_SIZE))
#define GETPREVFREE(header_ptr) (*(size_t *)((header_ptr) + 2*SIZE_T_SIZE))
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define DEBUG 0

#define MAXPOW 25

//Pointer to the seglist array in heap
void **free_seglist;

/*
 * Function declaration (.h file not included in handin)
 */

void remove_link(void *ptr);
void add_to_list(void *ptr);
void *get_optimal_free_block(size_t size);
int seglist_index(size_t size);
void mm_check();

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init()
{
#if DEBUG    
    printf("\n\n\n##########INIT###########\n\n\n");
#endif
    int i = 0;
    mem_sbrk(ALIGN(MAXPOW * sizeof(void *)));
    free_seglist = mem_heap_lo();
    if (free_seglist == NULL) return 0;
    for (i = 0; i < MAXPOW; i++){
        free_seglist[i] = NULL;
    }
    return 1;
}

/*
 * display_free - display the contents of the seglist
 */
void display_free(){
    int index = 0;
    while(index < MAXPOW){
        printf("SIZE : %d :: ", 1<<(index+5));
        void *ptr = free_seglist[index];
        int i = 0;
        while(ptr != NULL){
            i++;
            printf("Addr : %x\t", ptr);
            ptr = (void *)GETNEXTFREE(ptr);
        }
        printf("%d\n", i);
        index++;
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    
#if DEBUG
    printf("Asking Malloc for size %d\n", size);
    display_free();
#endif 

    if(size == 0) return NULL;
    
    size_t new_size = ALIGN(size + 2*SIZE_T_SIZE);
    if(new_size < ALIGN(4*SIZE_T_SIZE)) new_size = ALIGN(4*SIZE_T_SIZE);
    size_t new_header = new_size | 1; // set dirty bit to 1
    void *p = get_optimal_free_block(new_size);
    void *end = mem_heap_hi();
    if(p != NULL)
    {
#if DEBUG
        printf("Found a spot %x in memory\n", p);
#endif
        remove_link(p);    
        int old_size = GETSIZE(*(size_t *)p);
        if(old_size - new_size >= ALIGN(4*SIZE_T_SIZE)){
            void *leftover = p + new_size;
            *(size_t *)leftover = old_size - new_size;
            *(size_t *)GETFOOTER(leftover) = old_size - new_size;
            add_to_list(leftover);
        }
        else new_header = old_size | 1;
        *(size_t *)p = new_header;
        *(size_t *)GETFOOTER(p) = new_header;
    }
    else
    {
#if DEBUG
        printf("allocating space\n");
#endif

        // end is now the footer of the last block of the heap
        end -= SIZE_T_SIZE - 1;

        if (mem_heapsize() != 0 && !GETDIRTYBIT(*(size_t *)end)) {
            // The last block of the heap is free.
            // We will look at its size, and if it's big enough
            // we will expand to fit the size asked by the user

            if (GETSIZE(*(size_t *) end) > 50 * SIZE_T_SIZE) {
                // The block is big enough not to ignore it,
                // otherwise we would have a big fragmentation.
                // We expand it to the size required by the user.
                p = end - GETSIZE(*(size_t *) end) + SIZE_T_SIZE;
                mem_sbrk((int) GETSIZE(new_header) - GETSIZE(*(size_t *) end));
                remove_link(p);
            } else {
                // The last block is rather small, we let it
                // there. The bet we make here is the following:
                // the user will sooner or later allocate another
                // small block, and we will then use this one.
                // This allows us to manage the place of blocks
                // in the heap, depending of their sizes: small
                // blocks are next one to another.
                p = mem_sbrk((int) GETSIZE(new_header));
                if (p == NULL)
                    return NULL;
            }

        } else {
            // The last block in the heap is not free, we
            // need to expand the heap.
            // We expand twice the size asked. This combined
            // with our "expansion on last block" policy
            // (only when the last block is big) allows
            // us to manage the place of blocks in the heap:
            // when the user allocates a small block, we will
            // reserve the room for another small block right
            // after, and this cannot be used to allocated
            // a big block.
            // This allows us to manage the place of blocks
            // in the heap, depending of their sizes: small
            // blocks are next one to another.
            if (GETSIZE(new_header) > 50 * SIZE_T_SIZE) {
                p = mem_sbrk((int) GETSIZE(new_header));
                if (p == NULL)
                    return NULL;
            } else {
                p = mem_sbrk((int) GETSIZE(new_header) * 2);
                if (p == NULL)
                    return NULL;
                *(size_t *) (p + GETSIZE(new_header)) = new_header & -2;
                *(size_t *) (GETFOOTER(p + GETSIZE(new_header))) = new_header & -2;
                add_to_list(p + GETSIZE(new_header));
            }
        }
        *(size_t *)p = new_header;
        *(size_t *)(GETFOOTER(p)) = new_header;
    }
#if DEBUG
    printf("Giving out at address %x\n", p+SIZE_T_SIZE);
//    display_free();
#endif
    return p + SIZE_T_SIZE;
}

/*
 * remove_link - removes a link from the right seg free list
 */
void remove_link(void *ptr){
#if DEBUG
    printf("Removing %x\n", ptr);
#endif
    if((void *)GETNEXTFREE(ptr) == NULL && (void *)GETPREVFREE(ptr) == NULL) {
        free_seglist[seglist_index(GETSIZE(*(size_t *) ptr))] = NULL;
    }
    else if((void *)GETNEXTFREE(ptr) == NULL) {
        GETNEXTFREE((void *) GETPREVFREE(ptr)) = (size_t) NULL;
    }
    else if((void *)GETPREVFREE(ptr) == NULL){
        GETPREVFREE((void *)GETNEXTFREE(ptr)) = (size_t) NULL;
        free_seglist[seglist_index(GETSIZE(*(size_t *) ptr))] = (void *)GETNEXTFREE(ptr);
    }
    else{
        GETNEXTFREE((void *)GETPREVFREE(ptr)) = GETNEXTFREE(ptr);
        GETPREVFREE((void *)GETNEXTFREE(ptr)) = GETPREVFREE(ptr);
    }
#if DEBUG
    display_free();
#endif
}

/*
 * add_to_list - adds a link to the right seglist
 */
void add_to_list(void *ptr){
#if DEBUG
    printf("Adding %x, size of block is %lu\n", ptr, GETSIZE(*(size_t*)ptr));
#endif
    //Ordered blocks stategy
    int index = seglist_index(GETSIZE(*(size_t *)ptr));
    if(free_seglist[index] == NULL){
        free_seglist[index] = ptr;
        GETNEXTFREE(ptr) = (size_t)NULL;
        GETPREVFREE(ptr) = (size_t)NULL;
#if DEBUG
    display_free();
#endif
        return;
    }

    //Now, we'll find the spot to insert this free block
    void *free_slot = free_seglist[index];
    while(GETNEXTFREE(free_slot) != (size_t)NULL && GETSIZE(GETNEXTFREE(free_slot)) < GETSIZE(*(size_t *)ptr)) free_slot = (void *)GETNEXTFREE(free_slot);
    GETNEXTFREE(ptr) = GETNEXTFREE(free_slot);
    GETPREVFREE(ptr) = (size_t)free_slot;
    if(GETNEXTFREE(free_slot) != (size_t)NULL) GETPREVFREE((void *)GETNEXTFREE(free_slot)) = (size_t)ptr;
    GETNEXTFREE(free_slot) = (size_t)ptr;
#if DEBUG
    display_free(); 
#endif
}

/*
 * mm_coalesce - coalesce a free block with the neighboring free blocks
 */
void mm_coalesce(void **header_ptr) {
    void *start = mem_heap_lo() + ALIGN(MAXPOW * sizeof(void *));
    void *end = mem_heap_hi();
    void *next_header = *header_ptr + GETSIZE(*(size_t *)*header_ptr);
    if(next_header < end && !GETDIRTYBIT(*(size_t *)next_header)){
        //First, we'll remove this free block from the list of free blocks
        remove_link(next_header);
        //Now, coalesce
        *(size_t *)*header_ptr += GETSIZE(*(size_t *)next_header);
        *(size_t *)GETFOOTER(next_header) = *(size_t *)*header_ptr;
    }

    void *footer = GETFOOTER(*header_ptr);
    void *prev_footer = footer - GETSIZE(*(size_t *)footer);
    if (prev_footer <= start) return;
    void *prev_header = prev_footer - GETSIZE(*(size_t *)prev_footer) + SIZE_T_SIZE;
    if(!GETDIRTYBIT(*(size_t *)prev_header)){
        //First, we'll remove this free block from the list of free blocks
        remove_link(prev_header);
        //Now, coalesce
        *(size_t *)prev_header += GETSIZE(*(size_t*)*header_ptr);
        *(size_t *)footer = *(size_t *)prev_header;
        *header_ptr = prev_header;
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    //first, lets define useful variables
#if DEBUG
    printf("Freeing at address %x\n", ptr);
    mm_check();
#endif 
    void *header_ptr = ptr - SIZE_T_SIZE;

    if(!GETDIRTYBIT(*(size_t *)header_ptr)){
        printf("Warning : attempting to free a free block\n");
        return;
    }

    //Coalesce
    mm_coalesce(&header_ptr);

    //Insert in free list
    add_to_list(header_ptr);    

    //change flag
    *(size_t*)header_ptr &= -2;

#if DEBUG
//   display_free();
#endif
}

/*
 * mm_check - check and verify the integrity of the heap and the surrounding parameters
 */
void mm_check(){
    //Are all blocks in the free list marked as free ?
    int flist = 0;
    int i = 0;
    int sizepb = 0;
    for(i = 0; i < MAXPOW; i++){
        void *current_free_block = free_seglist[i];
        while(current_free_block != NULL){
            if(GETDIRTYBIT(*(size_t *)current_free_block)){
                flist = 1;
                break;
            }
            if(GETSIZE(*(size_t *)current_free_block) < 1<<(i+5)){
                sizepb = 1;
                break;
            }
            current_free_block = (void *)GETNEXTFREE(current_free_block);
        }
    }

    //Are all free blocks coalesced ?
    int coald = 0;
    void *start = mem_heap_lo() + ALIGN(MAXPOW*sizeof(void *));
    void *end = mem_heap_hi();
    if(start != end){
        void *current_block = GETNEXTBLOCK(start);
        int prev_type = (int)GETDIRTYBIT(*(size_t *)start);
        while(current_block < end){
            if(prev_type == 0 && prev_type == (int)GETDIRTYBIT(*(size_t *)current_block)){
                coald = 1;
                break;
            }
            prev_type = (int)GETDIRTYBIT(*(size_t *)current_block);
            current_block = GETNEXTBLOCK(current_block);
        }
    }

    //Are all free blocks in the list ? 
    int finlist = 0;
    if(start != end){
        void *current_block = GETNEXTBLOCK(start);
        while(current_block < end){
            if(GETDIRTYBIT(*(size_t *)current_block) == 0){
                void *current_free_block = free_seglist[seglist_index(GETSIZE(*(size_t *)current_block))];
                while(current_free_block != NULL){
                    if(current_free_block == current_block) break;
                    current_free_block = (void *)GETNEXTFREE(current_free_block);
                }
                if(current_free_block == NULL){
                    finlist = 1;
                    break;
                }
            }
            current_block = GETNEXTBLOCK(current_block);
        }
    }

    //Are all blocks "coherent" ? 
    int coherent = 0;
    if(start != end){
        void *current_block = GETNEXTBLOCK(start);
        while(current_block < end){
            size_t size = GETSIZE(*(size_t *)current_block);
            if(size != GETSIZE(*(size_t *)GETFOOTER(current_block))){
                coherent = 1;
                break;   
            }
            current_block = GETNEXTBLOCK(current_block);
        }
    }

    if(flist || sizepb || coald || finlist || coherent){
        printf("Test results : \n");
        if(flist) printf("Some elts of the free list aren't free\n");
        if(sizepb) printf("Some free blocks are in the wrong category\n");
        if(coald) printf("Some free blocks are not coalesced\n");
        if(finlist) printf("Some free blocks are not in the list\n");
        if(coherent) printf("Incoherent block layout\n");
        printf("\n____ENDTEST____\n");
        exit(0);
    }
}

/*
 * mm_realloc - Standalone implementation for efficiency 
 */
void *mm_realloc(void *ptr, size_t newsize) {
    void *oldptr = ptr;
    void *newptr = oldptr;

    // count the space needed for the header and the footer
    newsize = ALIGN(newsize + 2 * SIZE_T_SIZE);
    if(newsize < ALIGN(4* SIZE_T_SIZE)) newsize = ALIGN(4*SIZE_T_SIZE);
    // get the size of the block the user asks to expand
    size_t *header = (size_t *) (oldptr - SIZE_T_SIZE);
    //printf("header contains %d\n", *header);
    size_t current_size = GETSIZE(*header);
#if DEBUG
    printf("realloc: newsize is %d and current size is %d\n", newsize, current_size);
#endif
    if (newsize > current_size) {
        // we want to expand the size of the current block
        void *start = mem_heap_lo() + ALIGN(MAXPOW*sizeof(void *));
        void *end = mem_heap_hi();

        // get the footer of the current block
        size_t *footer = GETFOOTER((void *) header);

        // get the header of the block right next in memory
        size_t *next_header = (size_t *) ((void *) header + GETSIZE(*header));

        // get the footer of the previous block in memory
        size_t *prev_footer = (size_t *) ((void *) header - SIZE_T_SIZE);

        int next_header_exists = (void *)next_header <= end;
        int prev_footer_exists = (void *)prev_footer >= start;
        
        if(prev_footer_exists && next_header_exists && !GETDIRTYBIT(*next_header) && !GETDIRTYBIT(*prev_footer) && GETSIZE(*next_header) + current_size + GETSIZE(*prev_footer) >= newsize)
        {
            //If we're caught in a sandwich of two blocks, and there's enough space, we'll push this block to the end of the available slot
            //Size of the leftover free space
            size_t new_free_size = GETSIZE(*next_header) + current_size + GETSIZE(*prev_footer) - newsize;
            
            //We remove surrounding free blocks from the free list to use them
            remove_link((void *) next_header);
            size_t *prev_header = (size_t *) ((void *) prev_footer - GETSIZE(*prev_footer) + SIZE_T_SIZE);
            remove_link((void *) prev_header);
            
            //Pointer to the new position of the header
            size_t *new_header;
            if(new_free_size < 4*SIZE_T_SIZE){
                
                //If the free space isn't large enough for a new block, we'll just insert it in the nex block
                newsize = new_free_size + newsize;
                //New block will start at the start of the available space
                new_header = prev_header;
                //Move the data
                memmove((void *)new_header + SIZE_T_SIZE, ptr, current_size - SIZE_T_SIZE);
                //Set the header and footer
                *new_header = newsize | 1;
                *(size_t *)GETFOOTER((void *)new_header) = newsize | 1;
            
            } else {
                //If the free space is large enough for a free block
                //New block is put in the highest address possible (optimization for realloc tests)
                new_header = (size_t *) (((void *)next_header) + GETSIZE(*next_header) - newsize); 
                memmove((void *)new_header + SIZE_T_SIZE, ptr, current_size - SIZE_T_SIZE);
                *new_header = newsize | 1;
                *(size_t *)GETFOOTER((void *)new_header) = newsize | 1;
                *prev_header = new_free_size & -2;
                *(size_t *)GETFOOTER((void *)prev_header) = new_free_size & -2;
                add_to_list((void *)prev_header);
            }
            return (void *)new_header + SIZE_T_SIZE;   
        }

        if (next_header_exists && !GETDIRTYBIT(*next_header) && (GETSIZE(*next_header) + current_size) >= newsize) {
            // block right next in memory is free
            // and it is big enough so we can use it to
            // expand the current block at a minimal cost

            // change the list of free blocks: remove block next to current
            // that we will use to expand
            remove_link((void *) next_header);
            
            void *free_block_header = NULL;
            size_t newheader;
            if (GETSIZE(*next_header) + current_size - newsize < 4 * SIZE_T_SIZE) {
                // no room for appending a free block at the end
                newheader = GETSIZE(*next_header) + current_size | 1;
            } else {
                // append a free block at then end
                newheader = newsize | 1;

                size_t header_tmp = GETSIZE(*next_header) + current_size - newsize;
                free_block_header = ((void *) header + newsize);
                *(size_t*)free_block_header = header_tmp;
                *(size_t*)GETFOOTER(free_block_header) = header_tmp;
                add_to_list(free_block_header);
            }
            // change the header and the footer
            *header = newheader;
            *(size_t *) GETFOOTER((void *) header) = newheader;
            if (free_block_header != NULL) mm_coalesce(&free_block_header);
            return newptr;
        }
        if (prev_footer_exists && !GETDIRTYBIT(*prev_footer) && (GETSIZE(*prev_footer) + current_size) >= newsize) {
            // If the previous block is free and large enough to fit the resized block
            size_t *prev_header = (size_t *) ((void *) prev_footer - GETSIZE(*prev_footer) + SIZE_T_SIZE);
            
            // Remove free link
            remove_link((void *) prev_header);
            
            //prepare the new header pointer, and the different sizes
            size_t *new_header;
            size_t available_size = GETSIZE(*prev_footer) + current_size;
            size_t new_free_size = available_size - newsize;
            
            if(new_free_size < 4*SIZE_T_SIZE){
                
                //If we can't create a new free block
                new_header = prev_header;
                memmove((void *)new_header + SIZE_T_SIZE, ptr, current_size - SIZE_T_SIZE);
                *new_header = available_size | 1;
                *(size_t *)GETFOOTER((void *)new_header) = available_size | 1;
                return (void *)new_header + SIZE_T_SIZE;
            }
            //If we get here, we have wiggle room. We'll put the resized block at the highest possible address for optimization
            new_header = (size_t *) ((void *)header + current_size - newsize);
            memmove((void *)new_header + SIZE_T_SIZE, ptr, current_size - SIZE_T_SIZE);
            *new_header = newsize | 1;
            *(size_t *)GETFOOTER((void *)new_header) = newsize | 1;
            *prev_header = new_free_size & -2;
            *(size_t *)GETFOOTER((void *)prev_header) = new_free_size & -2;
            add_to_list((void *)prev_header);
            return (void *)new_header + SIZE_T_SIZE;
        }
    
        if (!next_header_exists){
            //If this block is the last, we'll simply extend by the amount needed
            size_t addition;
            if(prev_footer_exists && !GETDIRTYBIT(*prev_footer)){
                
                // If the previous block is fere, we can use the space
                size_t *prev_header = (size_t *) ((void *) prev_footer - GETSIZE(*prev_footer) + SIZE_T_SIZE);
                remove_link((void *) prev_header);
                header = prev_header;
                memmove((void *) header + SIZE_T_SIZE, ptr, current_size - SIZE_T_SIZE);
                addition = newsize - (current_size + GETSIZE(*prev_header));
            }
            else addition = newsize - current_size;  
            if(mem_sbrk(addition) == NULL) return NULL;
            *header = newsize | 1;
            footer = GETFOOTER((void *) header);
            *footer = newsize | 1;
            return ptr;
        }
    
        //worst case
        newptr = mm_malloc(newsize);
        memmove(newptr, oldptr, current_size - 2);
        mm_free(ptr);
        return newptr;

    } else {
        // we have current_size >= newsize: we have to shrink the block
        // and free the right part

        // if we have not enough space to create the new free block
        // then don't actually resize anything
        if (current_size - newsize > 4 * SIZE_T_SIZE) {
            size_t newheader = newsize | 1;
            *header = newheader;
            size_t *footer = (size_t *) GETFOOTER((void *) header);
            *footer = newheader;

            newheader = (current_size - newsize);
            void *free_block_header = (size_t *) ((void *) footer + SIZE_T_SIZE);
            *(size_t*)free_block_header = newheader;
            *(size_t *) GETFOOTER( free_block_header) = newheader;
            add_to_list(free_block_header);
            mm_coalesce(&free_block_header);
        }

        return ptr;
    }
}

/*
 * seglist_index - returns the index of this size in the free seglist
 */
int seglist_index(size_t size){
    if(size < 64) return 0;
    
    int rsp = 0;
    while (size){
        size = size >> 1;
        rsp += 1;
    }
    if(rsp-6 < MAXPOW) return rsp-6;
    return MAXPOW-1;   
}

/*
 * get_optimal_free_block - returns an optimal free block for the requested size
 */
void *get_optimal_free_block(size_t size){
    int index = seglist_index(size);
    while(index < MAXPOW){
        void *free_list = free_seglist[index];
        while(free_list != NULL) {
            if(GETSIZE(*(size_t *)free_list) >= size) return free_list;
            free_list = (void *)GETNEXTFREE(free_list);
        }
        index++;
    }
    return NULL;
}
