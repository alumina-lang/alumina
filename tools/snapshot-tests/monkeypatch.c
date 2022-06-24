#include <stdint.h>
#include <sys/types.h>

ssize_t getrandom_mock(void *buf, size_t buflen, unsigned int flags) {
    for (int i = 0; i < buflen; ++i) {
        ((unsigned char*)buf)[i] = (unsigned char)(0x7f + i);
    }
    return buflen;
}
