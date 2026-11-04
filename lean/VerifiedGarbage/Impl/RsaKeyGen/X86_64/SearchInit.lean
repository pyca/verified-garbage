module

public import VerifiedGarbage.TCB.X86_64.Isa

/-! # Starting the RSA prime search on x86-64

`vg_rsa_prime_search_init(state, prime_len, e, e_len)`
(`VG.Spec.RsaKeyGen.primeInit`): for a width `prime_len` a multiple of 8 in
32..=512 and an exponent of 1 to 8 octets, the counted candidates allowed
(`primeLimit`: `40 prime_len`, or `64 prime_len` for an exponent of 3, with
any leading zeros), `prime_len`, the entropy budget `32769 prime_len` and
the first request `32 prime_len`; otherwise four zeros.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.X86_64.SearchInit

open VG VG.X86_64

def field (j : Nat) : MemOp := { base := .rdi, disp := (8 * j : Nat) }

def clear : Prog isa := .block [
  .mov32 .rax (.imm 0), .store (field 0) .rax, .store (field 1) .rax,
  .store (field 2) .rax, .store (field 3) .rax]

/-- Whether `e` (rdx, `e_len` octets in rcx) is 3, in zf: the OR of its
leading octets in r9, then its last octet XOR 3 ORed in. -/
def isThree : Prog isa := .seq
  (.block [.mov32 .r9 (.imm 0), .mov .r11 (.reg .rcx), .alu .sub .r11 (.imm 1),
    .alu .test .r11 (.reg .r11)])
  (.seq (.ite .e (.block [])
      (.loop (.block [.movzx8 .rax { base := .rdx }, .alu .or .r9 (.reg .rax),
        .alu .add .rdx (.imm 1), .alu .sub .r11 (.imm 1)]) .ne))
    (.block [.movzx8 .rax { base := .rdx }, .alu .xor .rax (.imm 3), .alu .or .rax (.reg .r9)]))

/-- The four words, for `prime_len` in rsi: the budget `40 prime_len`
(`5 · bits`), or `64 prime_len` (`8 · bits`) for `e = 3`. -/
def initializeState : Prog isa := .seq isThree (.block [
  .mov .r9 (.reg .rax), .mov .rax (.reg .rsi), .shift .shl .rax 3, .mov .rcx (.reg .rax), .shift .shl .rax 2,
  .alu .add .rax (.reg .rcx), .mov .rcx (.reg .rsi), .shift .shl .rcx 6,
  .alu .test .r9 (.reg .r9), .cmov .e .rax (.reg .rcx), .store (field 0) .rax,
  .store (field 1) .rsi,
  .mov .rax (.reg .rsi), .shift .shl .rax 15, .alu .add .rax (.reg .rsi), .store (field 2) .rax,
  .mov .rax (.reg .rsi), .shift .shl .rax 5, .store (field 3) .rax, .mov32 .rax (.imm 1)])

/-- `e_len` in rcx: 1 to 8. -/
def checkExponent : Prog isa := .seq (.block [.alu .test .rcx (.reg .rcx)])
  (.ite .e clear (.seq (.block [.alu .cmp .rcx (.imm 9)]) (.ite .ae clear initializeState)))

/-- `prime_len` in rsi: a multiple of 8 from 32 to 512. -/
def init : Prog isa := .seq (.block [.alu .cmp .rsi (.imm 32)])
  (.ite .b clear (.seq (.block [.alu .cmp .rsi (.imm 513)])
    (.ite .ae clear (.seq (.block [.mov .rax (.reg .rsi), .alu .and .rax (.imm 7)])
      (.ite .ne clear checkExponent)))))

end VG.Impl.RsaKeyGen.X86_64.SearchInit
