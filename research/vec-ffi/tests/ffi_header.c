#include "../vec_ffi.h"

_Static_assert(sizeof(struct vec_pair) == 8, "vec_pair must be two RV32 words");
_Static_assert(sizeof(struct u32_vec) == 12, "u32_vec must be three RV32 words");
_Static_assert(sizeof(struct pair_vec) == 12, "pair_vec must be three RV32 words");

uint32_t exercise_declarations(
    struct u32_vec *u32_vec,
    struct pair_vec *pair_vec,
    struct vec_pair pair
) {
    uint32_t status = custom_u32_push(u32_vec, 1);
    status += custom_u32_insert_loop(u32_vec, 0, 2);
    status += custom_pair_push(pair_vec, pair);
    status += custom_pair_insert_loop(pair_vec, 0, pair);
    return status;
}
