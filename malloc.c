#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <signal.h>

int heap_init();
uint64_t mem_alloc(uint32_t size);
void mem_free(uint64_t vaddr);

static int implicit_free_list_heap_init();
static uint64_t implicit_free_list_mem_alloc(uint32_t size);
static void implicit_free_list_mem_free(uint64_t payload_vaddr);

static uint32_t extend_heap(uint32_t size);

void os_syscall_brk() {}

uint64_t heap_start_vaddr = 0;
uint64_t heap_end_vaddr = 4096;

#define HEAP_MAX_SIZE (4096 * 8)
uint8_t heap[HEAP_MAX_SIZE];

static uint64_t round_up(uint64_t x, uint64_t n);

static uint32_t get_blocksize(uint64_t header_vaddr);
static void set_blocksize(uint64_t header_vaddr, uint32_t blocksize);

static uint32_t get_allocated(uint64_t header_vaddr);
static void set_allocated(uint64_t header_vaddr, uint32_t allocated);

static uint64_t get_prologue();
static uint64_t get_epilogue();

static uint64_t get_firstblock();
static uint64_t get_lastblock();

static int is_lastblock(uint64_t vaddr);
static int is_firstblock(uint64_t vaddr);

static uint64_t get_payload(uint64_t vaddr);
static uint64_t get_header(uint64_t vaddr);
static uint64_t get_footer(uint64_t vaddr);

static uint64_t get_nextheader(uint64_t vaddr);
static uint64_t get_prevheader(uint64_t vaddr);

static uint64_t round_up(uint64_t x, uint64_t n) {
    return n * ((x + n - 1) / n);
}

static uint32_t extend_heap(uint32_t size) {
    size = round_up(size, 4096);
    if (heap_end_vaddr - heap_start_vaddr + size > HEAP_MAX_SIZE) return 0;
    os_syscall_brk();
    heap_end_vaddr += size;

    uint64_t epilogue = get_epilogue();
    set_allocated(epilogue, 1);
    set_blocksize(epilogue, 0);
    return size;
}

uint32_t get_blocksize(uint64_t header_vaddr){
    if (header_vaddr == 0) return 0;
    assert(get_prologue() <= header_vaddr && header_vaddr <= get_epilogue());
    assert((header_vaddr & 0x3) == 0);
    uint32_t header_value = *(uint32_t *)&heap[header_vaddr];
    return header_value & 0xFFFFFFF8;
}

void set_blocksize(uint64_t header_vaddr, uint32_t blocksize){
    if (header_vaddr == 0) return 0;
    assert(get_prologue() <= header_vaddr && header_vaddr <= get_epilogue());
    assert((header_vaddr & 0x3) == 0);
    assert((blocksize & 0x7) == 0);
    *(uint32_t *)&heap[header_vaddr] &= 0x7;
    *(uint32_t *)&heap[header_vaddr] |= blocksize;
}

uint32_t get_allocated(uint64_t header_vaddr){
    if (header_vaddr == 0) return 0;
    assert(get_prologue() <= header_vaddr && header_vaddr <= get_epilogue());
    assert((header_vaddr & 0x3) == 0);
    uint32_t header_value = *(uint32_t *)&heap[header_vaddr];
    return header_value & 0x1;
}

void set_allocated(uint64_t header_vaddr, uint32_t allocated){
    if (header_vaddr == 0) return 0;
    assert(get_prologue() <= header_vaddr && header_vaddr <= get_epilogue());
    assert((header_vaddr & 0x3) == 0);
    assert((allocated & 0xFFFFFFFE) == 0);
    *(uint32_t *)&heap[header_vaddr] &= 0xFFFFFFF8;
    *(uint32_t *)&heap[header_vaddr] |= allocated;
}

static uint64_t get_prologue() {
    assert(heap_end_vaddr > heap_start_vaddr);
    assert((heap_end_vaddr - heap_start_vaddr) % 4096 == 0);
    assert(heap_start_vaddr % 4096 == 0);
    return heap_start_vaddr + 4;
}

static uint64_t get_epilogue() {
    assert(heap_end_vaddr > heap_start_vaddr);
    assert((heap_end_vaddr - heap_start_vaddr) % 4096 == 0);
    assert(heap_start_vaddr % 4096 == 0);
    return heap_end_vaddr - 4;
}

static uint64_t get_firstblock() {
    assert(heap_end_vaddr > heap_start_vaddr);
    assert((heap_end_vaddr - heap_start_vaddr) % 4096 == 0);
    assert(heap_start_vaddr % 4096 == 0);
    return heap_start_vaddr + 8;
}

static uint64_t get_lastblock() {
    assert(heap_end_vaddr > heap_start_vaddr);
    assert((heap_end_vaddr - heap_start_vaddr) % 4096 == 0);
    assert(heap_start_vaddr % 4096 == 0);
    uint64_t epilogue_header = get_epilogue();
    uint64_t last_footer = epilogue_header - 4;
    uint32_t last_blocksize = get_blocksize(last_footer);
    uint64_t last_header = epilogue_header - last_blocksize;
    assert(get_firstblock() <= last_header);
    return last_header;
}

static int is_firstblock(uint64_t vaddr) {
    if (vaddr == 0) return 0;
    assert(get_firstblock() <= vaddr && vaddr < get_epilogue());
    assert((vaddr & 0x3) == 0);
    uint64_t header_vaddr = get_header(vaddr);
    if (header_vaddr == get_firstblock()) return 1;
    return 0;
}

static int is_lastblock(uint64_t vaddr) {
    if (vaddr == 0) return 0;
    assert(get_firstblock() <= vaddr && vaddr < get_epilogue());
    assert((vaddr & 0x3) == 0);
    uint64_t header_vaddr = get_header(vaddr);
    uint64_t blocksize = get_header(header_vaddr);
    if (header_vaddr + blocksize == get_lastblock()) return 1;
    return 0;
}

static uint64_t get_payload(uint64_t vaddr) {
    if (vaddr == 0) return 0;
    assert(get_firstblock() <= vaddr && vaddr < get_epilogue());
    assert((vaddr & 0x3) == 0);
    return round_up(vaddr, 8);
}

static uint64_t get_header(uint64_t vaddr) {
    if (vaddr == 0) return 0;
    assert(get_firstblock() <= vaddr && vaddr < get_epilogue());
    assert((vaddr & 0x3) == 0);
    uint64_t playload_vaddr = get_payload(vaddr);
    return playload_vaddr == 0 ? 0 : playload_vaddr - 4;
}

static uint64_t get_footer(uint64_t vaddr) {
    if (vaddr == 0) return 0;
    assert(get_firstblock() <= vaddr && vaddr < get_epilogue());
    assert((vaddr & 0x3) == 0);
    uint64_t header_vaddr = get_header(vaddr);
    uint64_t footer_vaddr = header_vaddr + get_blocksize(header_vaddr) - 4;
    assert(get_firstblock() < footer_vaddr && footer_vaddr < get_epilogue());
    return footer_vaddr;
}

static uint64_t get_nextheader(uint64_t vaddr) {
    if (vaddr == 0 || is_lastblock(vaddr)) return 0;
    assert(get_firstblock() <= vaddr && vaddr < get_lastblock());
    uint64_t header_vaddr = get_header(vaddr);
    uint64_t blocksize = get_blocksize(header_vaddr);
    uint64_t next_header_vaddr = header_vaddr + blocksize;
    assert(get_firstblock() < next_header_vaddr && next_header_vaddr <= get_lastblock());
    return next_header_vaddr;
}

static uint64_t get_prevheader(uint64_t vaddr) {
    if (vaddr == 0 || is_firstblock(vaddr)) return 0;
    assert(get_firstblock() < vaddr && vaddr <= get_lastblock());
    uint64_t header_vaddr = get_header(vaddr);
    uint64_t prev_footer_vaddr = header_vaddr - 4;
    uint32_t prev_bloksize = get_blocksize(prev_footer_vaddr);
    uint64_t prev_header_vaddr = prev_footer_vaddr - prev_bloksize;
    assert(get_firstblock() <= prev_header_vaddr && prev_header_vaddr <= get_lastblock());
    assert(*(uint32_t *)&heap[prev_header_vaddr] == *(uint32_t *)&heap[prev_footer_vaddr]);
    return prev_header_vaddr;
}

// 将low和high两个头部所表示的段合并
static uint64_t merge_blocks_as_free(uint64_t low, uint64_t high) {
    assert(low % 8 == 4);
    assert(high % 8 == 4);
    assert(get_firstblock() <= low && low < get_lastblock());
    assert(get_firstblock() < high && high <= get_lastblock());
    assert(get_nextheader(low) == high);
    assert(low == get_prevheader(high));

    uint32_t blocksize = get_blocksize(low) + get_blocksize(high);
    
    set_blocksize(low, blocksize);
    set_allocated(low, 0);

    uint32_t footer = get_footer(high);
    set_blocksize(footer, blocksize);
    set_allocated(footer, 0);

    return low;
}

static uint64_t try_alloc_with_spliting(uint64_t block_vaddr, uint64_t request_blocksize, uint64_t min_blocksize) {
    if (request_blocksize < min_blocksize) return 0;
    uint64_t b = block_vaddr;
    uint64_t b_blocksize = get_blocksize(b);
    uint64_t b_allocated = get_allocated(b);

    if (b_allocated == 0 && b_blocksize <= request_blocksize) {
        if (b_blocksize - request_blocksize >= min_blocksize) {
            uint64_t last_footer = get_footer(b);
            set_blocksize(last_footer, b_blocksize - request_blocksize);
            set_allocated(last_footer, 0);

            set_blocksize(b, request_blocksize);
            set_allocated(b, 1);

            uint64_t now_footer = get_footer(b);
            set_blocksize(now_footer, request_blocksize);
            set_allocated(now_footer, 1);

            uint64_t next_header = get_nextheader(b);
            set_blocksize(next_header, b_blocksize - request_blocksize);
            set_allocated(next_header, 0);

            assert(get_footer(next_header) == last_footer);

            return get_payload(b);
        } else if (b_blocksize - request_blocksize < min_blocksize) {
            // TODO: potential optimization: reduce the padding size
            // no need to split this block
            // set_blocksize(b, request_blocksize);

            set_allocated(b, 1);
            uint64_t footer = get_footer(b);
            set_allocated(footer, 1);

            return get_payload(b);
        }
    }
    return 0;
}

static uint64_t try_extend_heap_to_alloc(uint32_t size, uint32_t min_blocksize) {
    uint64_t old_last = get_lastblock();
    uint64_t last_blocksize = get_blocksize(old_last);
    uint64_t last_allocated = get_allocated(old_last);
    uint64_t to_request_from_os = size;
    if (last_allocated == 0) to_request_from_os -= last_blocksize;
    uint64_t old_epilogue = get_epilogue();
    uint64_t os_allocated_size = extend_heap(to_request_from_os);

    if (os_allocated_size != 0) {
        assert(os_allocated_size >= 4096);
        assert(os_allocated_size % 4096 == 0);
        uint64_t payload_header = 0;
        if (last_allocated == 1) {
            uint64_t new_last = old_epilogue;
            set_blocksize(new_last, os_allocated_size);
            set_allocated(new_last, 0);

            uint64_t new_last_footer = get_footer(new_last);
            set_blocksize(new_last_footer, os_allocated_size);
            set_allocated(new_last_footer, 0);

            payload_header = new_last;
        } else {
            set_blocksize(old_last, last_blocksize + os_allocated_size);
            set_allocated(old_last, 0);

            uint64_t last_footer = get_footer(old_last);
            set_blocksize(last_footer, last_blocksize + os_allocated_size);
            set_allocated(last_footer, 0);

            payload_header = old_last;
        }
        uint64_t payload_vaddr = try_alloc_with_spliting(payload_header, size, min_blocksize);
        if (payload_vaddr != 0) {
            return payload_vaddr;
        }
    }
    return 0;
}

/* ------------------------------------- */
/*  Implicit Free List                   */
/* ------------------------------------- */

/*  Allocated block:
    ff ff ff f9/f1  [8n + 24] - footer
    ?? ?? ?? ??     [8n + 20] - padding
    xx xx ?? ??     [8n + 16] - payload & padding
    xx xx xx xx     [8n + 12] - payload
    xx xx xx xx     [8n + 8] - payload
    hh hh hh h9/h1  [8n + 4] - header
    Free block:
    ff ff ff f8/f0  [8n + 24] - footer
    ?? ?? ?? ??     [8n + 20]
    ?? ?? ?? ??     [8n + 16]
    ?? ?? ?? ??     [8n + 12]
    ?? ?? ?? ??     [8n + 8]
    hh hh hh h8/h0  [8n + 4] - header
*/

#define MIN_IMPLICIT_FREE_LIST_BLOCKSIZE (8)

static int implicit_free_list_heap_init() {
    for (int i = 0; i < HEAP_MAX_SIZE / 8; i += 8) *(uint64_t *)&heap[i] = 0;

    heap_start_vaddr = 0;
    heap_end_vaddr = 4096;

    uint64_t prologue_header = get_prologue();
    set_blocksize(prologue_header, 8);
    set_allocated(prologue_header, 1);
    uint64_t prologue_footer = prologue_header + 4;
    set_blocksize(prologue_footer, 8);
    set_allocated(prologue_footer, 1);

    uint64_t epilogue = get_epilogue();
    set_blocksize(epilogue, 0);
    set_allocated(epilogue, 1);

    uint64_t first_header = get_firstblock();
    set_blocksize(first_header, 4096 - 4 - 4 - 8);
    set_allocated(first_header, 0);

    uint64_t first_footer = get_footer(first_header);
    set_blocksize(first_footer, 4096 - 4 - 4 - 8);
    set_allocated(first_footer, 0);

    return 1;
}

static uint64_t implicit_free_list_mem_alloc(uint32_t size) {
    assert(0 < size && size < HEAP_MAX_SIZE - 4 - 4 - 8);
    uint64_t payload_vaddr = 0;
    uint32_t request_blocksize = round_up(size, 8) + 4 + 4;
    request_blocksize = request_blocksize < MIN_IMPLICIT_FREE_LIST_BLOCKSIZE ? MIN_IMPLICIT_FREE_LIST_BLOCKSIZE : request_blocksize;
    uint64_t b = get_firstblock();
    uint64_t epilogue = get_epilogue();

    while (b != 0 && b < epilogue) {
        payload_vaddr = try_alloc_with_spliting(b, size, MIN_IMPLICIT_FREE_LIST_BLOCKSIZE);
        if (payload_vaddr != 0) {
            return payload_vaddr;
        } else {
            b = get_nextheader(b);
        }
    }

    return try_extend_heap_to_alloc(size, MIN_IMPLICIT_FREE_LIST_BLOCKSIZE);
}

static void implicit_free_list_mem_free(uint64_t payload_vaddr) {
    if (payload_vaddr == 0) return 0;
    assert(get_firstblock() < payload_vaddr && payload_vaddr <= get_epilogue());
    assert((payload_vaddr & 0x7) == 0);

    uint64_t req = get_header(payload_vaddr);
    uint64_t req_footer = get_footer(req);
    uint64_t req_blocksize = get_blocksize(req);
    uint64_t req_allocated = get_allocated(req);
    assert(req_allocated == 1);

    uint64_t next = get_nextheader(req);
    uint64_t prev = get_prevheader(req);
    uint64_t next_header = get_header(next);
    uint64_t prev_header = get_header(prev);
    uint64_t next_allocated = get_allocated(next_header);
    uint64_t prev_allocated = get_allocated(prev_header);

    if (next_allocated == 1 && prev_allocated == 1) {
        set_allocated(req, 0);
        set_allocated(req_footer, 0);
    } else if (next_allocated == 0 && prev_allocated == 1) {
        merge_blocks_as_free(req, next);
    } else if (next_allocated == 1 && prev_allocated == 0) {
        merge_blocks_as_free(prev, req);
    } else if (next_allocated == 0 && prev_allocated == 0) {
        uint64_t merged = merge_blocks_as_free(prev, req);;
        merge_blocks_as_free(merged, next);
    } 
}

/* ------------------------------------- */
/*  Explicit Free List                   */
/* ------------------------------------- */

/*  Allocated block:
    ff ff ff f9/f1  [8n + 24] - footer
    ?? ?? ?? ??     [8n + 20] - padding
    xx xx ?? ??     [8n + 16] - payload & padding
    xx xx xx xx     [8n + 12] - payload
    xx xx xx xx     [8n + 8] - payload
    hh hh hh h9/h1  [8n + 4] - header
    Free block:
    ff ff ff f8/f0  [8n + 24] - footer
    ?? ?? ?? ??     [8n + 20]
    ?? ?? ?? ??     [8n + 16]
    nn nn nn nn     [8n + 12] - next free block address
    pp pp pp pp     [8n + 8] - previous free block address
    hh hh hh h8/h0  [8n + 4] - header
*/

#define MIN_EXPLICIT_FREE_LIST_BLOCKSIZE (16)

static uint64_t explicit_list_head = 0;
static uint64_t explicit_list_counter = 0;

void check_explicit_vaddr (uint64_t vaddr) {
    assert(get_firstblock() <= vaddr && vaddr <= get_lastblock());
    assert(get_blocksize(vaddr) >= MIN_EXPLICIT_FREE_LIST_BLOCKSIZE);
    assert(vaddr % 8 == 4);
}
static uint64_t get_prevfree(uint64_t header_vaddr) {
    check_explicit_vaddr(header_vaddr);
    uint32_t perv_vaddr = *(int32_t *) &heap[header_vaddr + 4];
    return (uint64_t)perv_vaddr;
}

static uint64_t get_nextfree(uint64_t header_vaddr) {
    check_explicit_vaddr(header_vaddr);
    uint32_t perv_vaddr = *(int32_t *) &heap[header_vaddr + 8];
    return (uint64_t)perv_vaddr;
}

static void set_prevfree(uint64_t header_vaddr, uint64_t prev_vaddr) {
    check_explicit_vaddr(header_vaddr);
    check_explicit_vaddr(prev_vaddr);
    *(int32_t *) &heap[header_vaddr + 4] = prev_vaddr;
}

static void set_nextfree(uint64_t header_vaddr, uint64_t next_vaddr) {
    check_explicit_vaddr(header_vaddr);
    check_explicit_vaddr(next_vaddr);
    *(int32_t *) &heap[header_vaddr + 8] = next_vaddr;
}

static void explicit_list_insert(uint64_t *head_vaddr, uint32_t *counter_ptr, uint64_t block){
    check_explicit_vaddr(block);
    if ((*head_vaddr) == 0 || (*counter_ptr) == 0){
        assert((*head_vaddr) == 0);
        assert((*counter_ptr) == 0);
        set_prevfree(block, block);
        set_nextfree(block, block);
        (*head_vaddr) = block;
        (*counter_ptr) = 1;
        return;
    }
    uint64_t head = (*head_vaddr);
    uint64_t tail = get_prevfree(head);
    set_nextfree(block, head);
    set_prevfree(head, block);
    set_nextfree(tail, block);
    set_prevfree(block, tail);
    (*head_vaddr) = block;
    (*counter_ptr) += 1;
}

static void explicit_list_delete(uint64_t *head_vaddr, uint32_t *counter_ptr, uint64_t block){
    check_explicit_vaddr(block);
    if ((*head_vaddr) == 0 || (*counter_ptr) == 0) {
        assert((*head_vaddr) == 0);
        assert((*counter_ptr) == 0);
        return;
    }
    if ((*counter_ptr) == 1){
        assert(get_prevfree((*head_vaddr)) == (*head_vaddr));
        assert(get_nextfree((*head_vaddr)) == (*head_vaddr));
        (*head_vaddr) = 0;
        (*counter_ptr) = 0;
        return;
    }
    uint64_t prev = get_prevfree(block);
    uint64_t next = get_nextfree(block);
    if (block == (*head_vaddr)) (*head_vaddr) = next;
    set_nextfree(prev, next);
    set_prevfree(next, prev);
    (*counter_ptr) -= 1;
}

static int explicit_free_list_heap_init () {
    if (implicit_free_list_heap_init() == 0) return 0;
    uint64_t block = get_firstblock();
    set_prevfree(block, block);
    set_nextfree(block, block);
    explicit_list_counter = 1;
    explicit_list_head = block;
    return 1;
}

static uint64_t explict_free_list_mem_alloc(uint32_t size) {
    assert(0 < size && size < HEAP_MAX_SIZE - 4 - 8 - 4);
    uint64_t payload_vaddr = 0;
    uint32_t request_blocksize = round_up(size, 8) + 4 + 4;
    request_blocksize = request_blocksize < MIN_EXPLICIT_FREE_LIST_BLOCKSIZE ? MIN_EXPLICIT_FREE_LIST_BLOCKSIZE : request_blocksize;
    uint64_t b = explicit_list_head;
    uint32_t copy_count = explicit_list_counter;
    for (int i = 0; i < copy_count; i ++) {
        uint32_t b_old_blocksize = get_blocksize(b);
        payload_vaddr = try_alloc_with_spliting(b, request_blocksize, MIN_EXPLICIT_FREE_LIST_BLOCKSIZE);
        if (payload_vaddr != 0) {
            uint32_t b_new_blocksize = get_blocksize(b);
            assert(b_old_blocksize >= b_new_blocksize);
            explicit_list_delete(&explicit_list_head, &explicit_list_counter, b);
            if (b_old_blocksize > b_new_blocksize) {
                uint64_t b_new_header = get_header(b);
                assert(get_allocated(b_new_header) == 0);
                assert(get_blocksize(b_new_header) == b_old_blocksize - b_new_blocksize);
                explicit_list_insert(&explicit_list_head, &explicit_list_counter, b_new_header);
            }
            return payload_vaddr;
        } else {
            b = get_nextfree(b);
        }
    }
    uint64_t old_last = get_lastblock();
    if (get_allocated(old_last) == 0) explicit_list_delete(&explicit_list_head, &explicit_list_counter, old_last);
    payload_vaddr = try_extend_heap_to_alloc(request_blocksize, MIN_EXPLICIT_FREE_LIST_BLOCKSIZE);
    uint64_t new_last = get_lastblock();
    if (get_allocated(new_last) == 0) explicit_list_insert(&explicit_list_head, &explicit_list_counter, new_last);
    return payload_vaddr;
}

static uint64_t explict_free_list_mem_free(uint64_t payload_vaddr) {
    if (payload_vaddr == 0) return 0;
    assert(get_firstblock() < payload_vaddr && payload_vaddr < get_epilogue());
    assert((payload_vaddr & 0x7) == 0);

    uint64_t req = get_header(payload_vaddr);
    uint64_t req_footer = get_footer(req);
    uint64_t req_blocksize = get_blocksize(req);
    uint64_t req_allocated = get_allocated(req);
    assert(req_allocated == 1);

    uint64_t next = get_nextheader(req);
    uint64_t prev = get_prevheader(req);
    uint64_t next_allocated = get_allocated(next);
    uint64_t prev_allocated = get_allocated(prev);

    if (next_allocated == 1 && prev_allocated == 1) {
        set_allocated(req, 0);
        set_allocated(req_footer, 0);
        explicit_list_insert(&explicit_list_head, &explicit_list_counter, req);
    } else if (next_allocated == 0 && prev_allocated == 1) {
        explicit_list_delete(&explicit_list_head, &explicit_list_counter, next);
        uint64_t merged = merge_blocks_as_free(req, next);
        explicit_list_insert(&explicit_list_head, &explicit_list_counter, merged);
    } else if (next_allocated == 1 && prev_allocated == 0) {
        explicit_list_delete(&explicit_list_head, &explicit_list_counter, prev);
        uint64_t merged = merge_blocks_as_free(prev, req);
        explicit_list_insert(&explicit_list_head, &explicit_list_counter, merged);
    } else if (next_allocated == 0 && prev_allocated == 0) {
        explicit_list_delete(&explicit_list_head, &explicit_list_counter, prev);
        explicit_list_delete(&explicit_list_head, &explicit_list_counter, next);
        uint64_t merged = merge_blocks_as_free(merge_blocks_as_free(prev, req), next);
        explicit_list_insert(&explicit_list_head, &explicit_list_counter, merged);
    } 
}