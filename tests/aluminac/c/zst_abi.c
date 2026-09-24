// The C side of zst_abi.alu: the Alumina functions' zero-sized parameters
// and results are not there.
#include <stdint.h>

int32_t zst_unit(int32_t b);
int32_t zst_empty(int32_t b);
int32_t zst_aligned(int32_t b);
int32_t zst_array(int32_t b);
int32_t zst_tuple(int32_t b);
int32_t zst_fn_item(int32_t b);
int32_t zst_many(int32_t a, int32_t b, int32_t c);
void zst_result(void);

int32_t c_calls_alumina(void) {
    zst_result();
    return zst_unit(1) + zst_empty(2) + zst_aligned(3) + zst_array(4) + zst_tuple(5) + zst_fn_item(6)
        + zst_many(7, 8, 9);
}

int32_t c_takes_with_zsts(int32_t a, int32_t b) {
    return a * 10 + b;
}
