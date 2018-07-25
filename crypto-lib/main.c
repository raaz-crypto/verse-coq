#include <stdio.h>
#include <stdint.h>

extern void verse_zerobuf_c(uint16_t *buf);

int main()
{
    uint16_t buf[10];
    buf[0] = 0xff00;
    printf("before %x\n", buf[0]);
    verse_zerobuf_c(buf);
    printf("after %x\n", buf[0]);

}
