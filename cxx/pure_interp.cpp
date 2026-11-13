// Pure-EVM slice of the monad interpreter, built as a freestanding RV64IM
// object for machine-code verification.
//
// The opcode handlers, runtime functions and Intercode analysis are the
// unmodified monad sources. This file only adds:
//   * an instruction table (Cancun) in which every opcode that touches
//     world state, the block/tx environment, logs or other contracts is
//     replaced by `invalid`, as are KECCAK256, TLOAD and TSTORE for now;
//   * a Host with no live methods;
//   * a C entry point with a flat in-memory ABI.

#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/host.hpp>
#include <category/vm/interpreter/instruction_table.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/interpreter/stack_top.hpp>
#include <category/vm/interpreter/trampoline.hpp>
#include <category/vm/runtime/types.hpp>

#include <cstdint>
#include <cstdlib>
#include <cstring>

using PureTraits = monad::EvmTraits<monad::EvmRevision::Cancun>;

namespace monad::vm::interpreter
{
    consteval InstrTable make_pure_table()
    {
        InstrTable t = make_instruction_table<PureTraits>();
        constexpr uint8_t impure[] = {
            0x20, // KECCAK256
            0x31, // BALANCE
            0x32, // ORIGIN
            0x3A, // GASPRICE
            0x3B, // EXTCODESIZE
            0x3C, // EXTCODECOPY
            0x3F, // EXTCODEHASH
            0x40, // BLOCKHASH
            0x41, // COINBASE
            0x42, // TIMESTAMP
            0x43, // NUMBER
            0x44, // PREVRANDAO
            0x45, // GASLIMIT
            0x46, // CHAINID
            0x47, // SELFBALANCE
            0x48, // BASEFEE
            0x49, // BLOBHASH
            0x4A, // BLOBBASEFEE
            0x54, // SLOAD
            0x55, // SSTORE
            0x5C, // TLOAD
            0x5D, // TSTORE
            0xA0, 0xA1, 0xA2, 0xA3, 0xA4, // LOG0..LOG4
            0xF0, // CREATE
            0xF1, // CALL
            0xF2, // CALLCODE
            0xF4, // DELEGATECALL
            0xF5, // CREATE2
            0xFA, // STATICCALL
            0xFF, // SELFDESTRUCT
        };
        for (uint8_t const op : impure) {
            t[op] = invalid;
        }
        return t;
    }

    template <>
    constexpr InstrTable instruction_table<PureTraits> = make_pure_table();
}

namespace
{
    using namespace monad;
    using namespace monad::vm;

    class PureHost final : public Host
    {
    public:
        bool account_exists(Address const &) const override
        {
            std::abort();
        }

        bytes32_t get_storage(Address const &, bytes32_t const &) const override
        {
            std::abort();
        }

        StorageStatus set_storage(
            Address const &, bytes32_t const &, bytes32_t const &) override
        {
            std::abort();
        }

        uint256_t get_balance(Address const &) const override
        {
            std::abort();
        }

        size_t get_code_size(Address const &) const override
        {
            std::abort();
        }

        bytes32_t get_code_hash(Address const &) const override
        {
            std::abort();
        }

        size_t
        copy_code(Address const &, size_t, uint8_t *, size_t) const override
        {
            std::abort();
        }

        bool selfdestruct(Address const &, Address const &) override
        {
            std::abort();
        }

        Result call(Message const &) override
        {
            std::abort();
        }

        TxContext const *get_tx_context() const override
        {
            return nullptr;
        }

        bytes32_t get_block_hash(int64_t) const override
        {
            std::abort();
        }

        void emit_log(
            Address const &, uint8_t const *, size_t, bytes32_t const[],
            size_t) override
        {
            std::abort();
        }

        AccessStatus access_account(Address const &) override
        {
            std::abort();
        }

        AccessStatus access_storage(Address const &, bytes32_t const &) override
        {
            std::abort();
        }

        bytes32_t
        get_transient_storage(Address const &, bytes32_t const &) const override
        {
            std::abort();
        }

        void set_transient_storage(
            Address const &, bytes32_t const &, bytes32_t const &) override
        {
            std::abort();
        }

        PageStorageStatus
        update_page(Address const &, bytes32_t const &, StorageStatus) override
        {
            std::abort();
        }
    };

    void core_loop(
        void *, runtime::Context *const ctx,
        interpreter::Intercode const *const analysis,
        uint256_t *const stack_ptr, void *)
    {
        interpreter::StackTop const stack_top{stack_ptr};
        auto const *const stack_bottom = stack_ptr;
        auto const *const instr_ptr = analysis->code();
        auto const gas_remaining = ctx->gas_remaining;
        interpreter::instruction_table<PureTraits>[*instr_ptr](
            *ctx, *analysis, stack_bottom, stack_top, gas_remaining, instr_ptr);
    }
}

extern "C"
{
    struct monad_pure_input
    {
        uint8_t const *code;
        uint64_t code_size;
        uint8_t const *calldata;
        uint64_t calldata_size;
        int64_t gas;
        // Zeroed scratch buffer for EVM memory, `memory_capacity` bytes.
        uint8_t *memory;
        uint32_t memory_capacity;
        // 1024 + 1 slots of 32 bytes, 32-byte aligned.
        uint8_t *stack;
    };

    struct monad_pure_output
    {
        // 0 success, 1 revert, 2 failure (any exceptional halt)
        uint64_t status;
        int64_t gas_left;
        uint8_t const *output;
        uint64_t output_size;
    };

    void monad_pure_execute(
        monad_pure_input const *const in, monad_pure_output *const out)
    {
        PureHost host;
        Message msg{};
        msg.kind = CallKind::Call;
        msg.gas = in->gas;
        msg.input_data = in->calldata;
        msg.input_size = in->calldata_size;
        msg.memory_handle = in->memory;
        msg.memory = in->memory;
        msg.memory_capacity = in->memory_capacity;

        interpreter::Intercode const icode{
            std::span<uint8_t const>{in->code, in->code_size}};
        auto ctx = runtime::Context::from(host, &msg, icode.code_span());
        interpreter::trampoline(
            ctx, icode, reinterpret_cast<uint256_t *>(in->stack), core_loop);

        auto const result = ctx.copy_to_result<PureTraits>();
        switch (result.status_code) {
        case CallStatus::Success:
            out->status = 0;
            break;
        case CallStatus::Revert:
            out->status = 1;
            break;
        default:
            out->status = 2;
            break;
        }
        out->gas_left = result.gas_left;
        out->output = result.output_data;
        out->output_size = result.output_size;
    }
}
