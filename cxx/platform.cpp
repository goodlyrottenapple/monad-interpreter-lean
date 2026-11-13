// Freestanding platform layer for the pure interpreter: a bump allocator, a
// trap for unreachable paths, and simple libc and libgcc replacements.

#include <cstddef>
#include <cstdint>

extern "C"
{
    extern uint8_t monad_pure_heap[];
    extern uint8_t monad_pure_heap_end[];
    static uint8_t *heap_next = monad_pure_heap;

    [[noreturn]] void abort()
    {
        for (;;) {
            __asm__ volatile("ebreak");
        }
    }

    [[noreturn]] void zkvm_halt(int)
    {
        abort();
    }

    void *aligned_alloc(size_t const alignment, size_t const size)
    {
        if (size == 0) {
            return nullptr;
        }
        auto const p = (reinterpret_cast<uintptr_t>(heap_next) + alignment - 1) &
                       ~(uintptr_t{alignment} - 1);
        if (size > static_cast<size_t>(
                       reinterpret_cast<uintptr_t>(monad_pure_heap_end) - p)) {
            abort();
        }
        heap_next = reinterpret_cast<uint8_t *>(p + size);
        return reinterpret_cast<void *>(p);
    }

    void *malloc(size_t const size)
    {
        return aligned_alloc(32, size);
    }

    // Byte-at-a-time string functions and shift-subtract 128-bit division:
    // slower than newlib's and libgcc's, but far smaller proof obligations.

    void *memcpy(void *const dst, void const *const src, size_t const n)
    {
        auto *const d = static_cast<uint8_t *>(dst);
        auto const *const s = static_cast<uint8_t const *>(src);
        for (size_t i = 0; i < n; ++i) {
            d[i] = s[i];
        }
        return dst;
    }

    void *memmove(void *const dst, void const *const src, size_t const n)
    {
        auto *const d = static_cast<uint8_t *>(dst);
        auto const *const s = static_cast<uint8_t const *>(src);
        if (reinterpret_cast<uintptr_t>(d) <= reinterpret_cast<uintptr_t>(s)) {
            for (size_t i = 0; i < n; ++i) {
                d[i] = s[i];
            }
        }
        else {
            for (size_t i = n; i > 0; --i) {
                d[i - 1] = s[i - 1];
            }
        }
        return dst;
    }

    void *memset(void *const dst, int const c, size_t const n)
    {
        auto *const d = static_cast<uint8_t *>(dst);
        for (size_t i = 0; i < n; ++i) {
            d[i] = static_cast<uint8_t>(c);
        }
        return dst;
    }

    int memcmp(void const *const a, void const *const b, size_t const n)
    {
        auto const *const x = static_cast<uint8_t const *>(a);
        auto const *const y = static_cast<uint8_t const *>(b);
        for (size_t i = 0; i < n; ++i) {
            if (x[i] != y[i]) {
                return x[i] < y[i] ? -1 : 1;
            }
        }
        return 0;
    }

    int __clzdi2(uint64_t x)
    {
        int n = 0;
        while (n < 64 && (x >> 63) == 0) {
            x <<= 1;
            ++n;
        }
        return n;
    }

    using u128 = unsigned __int128;

    static u128 udivmod128(u128 const num, u128 const den, u128 *const rem)
    {
        u128 q = 0;
        u128 r = 0;
        for (int i = 127; i >= 0; --i) {
            r = (r << 1) | ((num >> i) & 1);
            if (r >= den) {
                r -= den;
                q |= u128{1} << i;
            }
        }
        *rem = r;
        return q;
    }

    u128 __udivti3(u128 const a, u128 const b)
    {
        u128 r;
        return udivmod128(a, b, &r);
    }

    u128 __umodti3(u128 const a, u128 const b)
    {
        u128 r;
        (void)udivmod128(a, b, &r);
        return r;
    }

    void *calloc(size_t const num, size_t const size)
    {
        // Fresh heap memory is zero: the heap is never reused.
        size_t total;
        if (__builtin_mul_overflow(num, size, &total)) {
            return nullptr;
        }
        return aligned_alloc(32, total);
    }

    void free(void *) {}

}

void *operator new(size_t const n)
{
    return malloc(n);
}

void *operator new[](size_t const n)
{
    return malloc(n);
}

void operator delete(void *) noexcept {}

void operator delete[](void *) noexcept {}

void operator delete(void *, size_t) noexcept {}

void operator delete[](void *, size_t) noexcept {}

// Referenced by Host's exception-capture member; never reached without
// exceptions.
namespace std::__exception_ptr
{
    struct exception_ptr
    {
        void _M_release() noexcept;
    };

    void exception_ptr::_M_release() noexcept {}
}
