module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Core

/-! # Callable shared Miller–Rabin round on x86-64

The RSA proof carries public bookkeeping fields which the prepared round
never needs. Save, normalize and restore those words so they do not enlarge
the callable's public input. Two fixed frames also supply the existing
proof's three-region representation without granting access outside the
workspace and stack. -/

@[expose] public section

namespace VG.Impl.MillerRabin.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate

/-- Unused RSA bookkeeping, paired with caller-saved staging registers. -/
def bookkeeping : List (Nat × Reg) :=
  [(kOut, .rsi), (kLen, .rdx), (kUsedP, .rcx), (kRand, .r8),
    (kRandLen, .r9), (kChecks, .rax), (kI, .r10), (kUsed, .r11)]

/-- The outer frame's eight caller-saved values and five callee-saved registers.
`rbp` occupies the inner frame. -/
def saved : List Reg := [.rbx, .r12, .r13, .r14, .r15] ++ bookkeeping.map (·.2)

def stage : List Instr := bookkeeping.map fun e => .mov e.2 (.mem (hdr e.1))

/-- The six unused fields whose normalized value is zero. -/
def zeroWords : List Nat := [kOut, kUsedP, kRand, kRandLen, kChecks, kI]

/-- Only the limb count is used to construct public bookkeeping. -/
def normalize : List Instr :=
  [.mov .rax (.mem (hdr sW)), .shift .shl .rax 3,
    .store (hdr kLen) .rax, .store (hdr kUsed) .rax, .mov32 .rax (.imm 0)] ++
    zeroWords.map (fun j => .store (hdr j) .rax)

/-- Restore every staged word and preserved register; then return the flag. -/
def finish : List Instr :=
  (bookkeeping.zipIdx.map fun (e, j) =>
    ([.mov .r11 (.mem { base := .rsp, disp := (8 * (8 - j) : Nat) }), .store (hdr e.1) .r11] : List Instr)).flatten ++
  [.mov .rbx (.mem { base := .rsp, disp := 104 }), .mov .r12 (.mem { base := .rsp, disp := 96 }),
    .mov .r13 (.mem { base := .rsp, disp := 88 }), .mov .r14 (.mem { base := .rsp, disp := 80 }),
    .mov .r15 (.mem { base := .rsp, disp := 72 }), .mov .rax (.mem (hdr kFlag)), .alu .and .rax (.imm 1)]

/-- A 112-byte frame, plus the return address used by Montgomery calls. -/
def round (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block stage)
    (.frame (.push saved)
      (.frame (.push [.rbp])
        (.seq (.block normalize) (.seq (seqs (preparedRound mul)) (.block finish)))
        (.pop .rbp 1))
      (.pop .r11 13))

end VG.Impl.MillerRabin.X86_64
