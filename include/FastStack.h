#ifndef _PYC_FASTSTACK_H
#define _PYC_FASTSTACK_H

#include "ASTNode.h"
#include <stack>

class FastStack {
public:
    FastStack(int size) : m_ptr(-1)
    {
        m_stack.resize(size);
        m_dup.resize(size, -1);
    }

    FastStack(const FastStack& copy)
        : m_stack(copy.m_stack), m_dup(copy.m_dup), m_ptr(copy.m_ptr) { }

    FastStack& operator=(const FastStack& copy)
    {
        m_stack = copy.m_stack;
        m_dup = copy.m_dup;
        m_ptr = copy.m_ptr;
        return *this;
    }

    // dupAt >= 0 is the bytecode offset of the DUP_TOP or COPY 1 that created this slot.
    void push(PycRef<ASTNode> node, int dupAt = -1)
    {
        if (static_cast<int>(m_stack.size()) == m_ptr + 1) {
            m_stack.emplace_back(nullptr);
            m_dup.emplace_back(-1);
        }

        m_stack[++m_ptr] = std::move(node);
        m_dup[m_ptr] = dupAt;
    }

    void pop()
    {
        if (m_ptr > -1) {
            m_dup[m_ptr] = -1;
            m_stack[m_ptr--] = nullptr;
        }
        else {
            #ifdef BLOCK_DEBUG
                fprintf(stderr, "pop from empty stack\n");
            #endif
        }
    }

    PycRef<ASTNode> top(int i = 1) const
    {
        if (i > 0) {
            int idx = m_ptr + 1 - i;
            if ((m_ptr > -1) && (idx >= 0))
                return m_stack[idx];
            else {
                #ifdef BLOCK_DEBUG
                    fprintf(stderr, "insufficient values on stack\n");
                #endif
                return nullptr;
            }
        }
        else {
            fprintf(stderr, "incorrect operand %i\n", i);
            return nullptr;
        }
    }

    // Bytecode offset of the DUP_TOP/COPY 1 that produced this slot, or -1.
    int top_dup_at(int i = 1) const
    {
        if (i <= 0)
            return -1;
        int idx = m_ptr + 1 - i;
        if (m_ptr > -1 && idx >= 0 && idx < static_cast<int>(m_dup.size()))
            return m_dup[idx];
        return -1;
    }

    bool top_is_dup(int i = 1) const
    {
        return top_dup_at(i) >= 0;
    }

    /* Swap the top of stack with the i-th element from the top (i >= 2). */
    bool swap(int i)
    {
        int a = m_ptr;
        int b = m_ptr + 1 - i;
        if (i < 2 || a < 0 || b < 0 || a == b)
            return false;
        std::swap(m_stack[a], m_stack[b]);
        std::swap(m_dup[a], m_dup[b]);
        return true;
    }

    int size() const
    {
        return m_ptr + 1;
    }

    bool empty() const
    {
        return m_ptr == -1;
    }

private:
    std::vector<PycRef<ASTNode>> m_stack;
    std::vector<int> m_dup;
    int m_ptr;
};

typedef std::stack<FastStack> stackhist_t;

#endif
