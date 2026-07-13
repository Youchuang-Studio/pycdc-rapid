#include "FastStack.h"
#include "data.h"

#include <cassert>

int main()
{
    const unsigned char bytes[] = { 0x11, 0x22, 0x33 };
    PycBuffer buffer(bytes, 3);

    assert(buffer.setPos(1));
    assert(!buffer.setPos(-1));
    assert(buffer.pos() == 1);
    assert(!buffer.setPos(4));
    assert(buffer.pos() == 1);

    unsigned char output[2] = {};
    buffer.getBuffer(2, output);
    assert(output[0] == 0x22 && output[1] == 0x33);
    assert(buffer.atEof());

    FastStack stack(0);
    assert(!stack.swap(2));
    stack.push(nullptr);
    assert(!stack.swap(2));
    stack.push(nullptr);
    assert(stack.swap(2));
    assert(!stack.swap(0));

    return 0;
}
