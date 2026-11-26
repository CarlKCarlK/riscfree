#ifndef RISCFREE_VEC_FFI_H
#define RISCFREE_VEC_FFI_H

#include <stddef.h>
#include <stdint.h>

enum vec_status {
    VEC_OK = 0,
    VEC_FULL = 1,
    VEC_INDEX_OUT_OF_BOUNDS = 2,
    VEC_INVALID_LENGTH = 3,
};

struct vec_pair {
    uint32_t key;
    uint32_t value;
};

struct u32_vec {
    uint32_t *data;
    uint32_t length;
    uint32_t capacity;
};

struct pair_vec {
    struct vec_pair *data;
    uint32_t length;
    uint32_t capacity;
};

size_t heapless_u32_size(void);
size_t heapless_u32_align(void);
void heapless_u32_init(void *storage);
uint32_t heapless_u32_push(void *storage, uint32_t value);
uint32_t heapless_u32_insert(void *storage, uint32_t index, uint32_t value);
uint32_t heapless_view_u32_insert_cap16(
    void *storage,
    uint32_t index,
    uint32_t value
);

size_t heapless_pair_size(void);
size_t heapless_pair_align(void);
void heapless_pair_init(void *storage);
uint32_t heapless_pair_push(void *storage, struct vec_pair value);
uint32_t heapless_pair_insert(
    void *storage,
    uint32_t index,
    struct vec_pair value
);

uint32_t custom_u32_push(struct u32_vec *vec, uint32_t value);
uint32_t custom_u32_insert(struct u32_vec *vec, uint32_t index, uint32_t value);
uint32_t custom_u32_insert_loop(
    struct u32_vec *vec,
    uint32_t index,
    uint32_t value
);
uint32_t custom_pair_push(struct pair_vec *vec, struct vec_pair value);
uint32_t custom_pair_insert(
    struct pair_vec *vec,
    uint32_t index,
    struct vec_pair value
);
uint32_t custom_pair_insert_loop(
    struct pair_vec *vec,
    uint32_t index,
    struct vec_pair value
);

#endif
