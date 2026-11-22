module

import VerifiedGarbage.Proof.Framework.X86.SseEquiv

/-!
# Two XMM programs that compute the same, on x86 (32-bit)

`SseEquiv.equiv` equates two blocks that differ in the order of independent
instructions, in the registers' names and in copies, and rejects a block
whose instructions are in an order that changes what one reads, that names
another register in one operand, or that stores elsewhere; `equiv_wp` then
gives a block what was proven of the other.
-/

namespace VG.Test.X86SseEquiv

open VG VG.X86 VG.X86.SseEquiv

def table : List (BitVec 64) :=
  [0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f, 0x0405060700010203, 0x0c0d0e0f08090a0b,
   0x0706050403020100, 0x0f0e0d0c0b0a0908]

def tb (d : XReg) (o : Nat) : Instr := .movdquTbl d ⟨.ebx, o⟩ "T" table
def x (op : XBinOp) (a b : XReg) : Instr := .xop (.bin op a b)

/-- The table at `ebx`; a buffer of 96 bytes at `edi`, whose first 32 the
programs store to; 64 bytes of keys at `esi`. -/
def prm : Params :=
  { tb := .ebx, name := "T", mreg := .edi, mlen := 96, kreg := .esi, klen := 64, slo := 0, shi := 32 }

/-- A block of the buffer through a byte map, the S-boxes and a key, twice,
to the buffer's start: the block at `i`, with the key at `k`, to `o`, in
the registers `a`, `b` and `c` (`xmm7` holds the mask). -/
def one (i k o : Nat) (a b c : XReg) : List Instr :=
  [.movdquLoad a ⟨.edi, i⟩, tb b 16, x .pshufb a b, x .aesenclast a .xmm7, .movqLoad c ⟨.esi, k⟩,
   x .punpcklqdq c c, x .pxor a c, x .movdqa b a, .xop (.shift .psrld b 4), x .pand b .xmm7,
   .xop (.pshufd c b 0x4e), x .pxor a c, .movdquStore ⟨.edi, o⟩ a, .movdquLoad c ⟨.edi, o⟩, x .paddd a c]

/-- One block after the other, in the same registers. -/
def P : List Instr :=
  tb .xmm7 0 :: (one 32 0 0 .xmm0 .xmm1 .xmm2 ++ (x .movdqa .xmm3 .xmm0 :: one 48 8 16 .xmm0 .xmm1 .xmm2))

/-- The two blocks' instructions in turn, in registers of their own, the
first block's result left where it is. -/
def weave : List Instr → List Instr → List Instr
  | a :: as, b :: bs => a :: b :: weave as bs
  | as, [] => as
  | [], bs => bs

def Q : List Instr := tb .xmm7 0 :: weave (one 32 0 0 .xmm3 .xmm1 .xmm2) (one 48 8 16 .xmm0 .xmm4 .xmm5)

/-- The results: the first block's in `xmm3`, the second's in `xmm0`. -/
def outs : List (XReg × XReg) := [(.xmm3, .xmm3), (.xmm0, .xmm0)]

example : equiv prm P Q outs = true := by decide +kernel

/-- `Q` with the instructions at `i` and at `j`, after it, in each other's
place. -/
def swap (i j : Nat) : List Instr :=
  Q.take i ++ (Q.drop j).take 1 ++ (Q.drop (i + 1)).take (j - i - 1) ++ (Q.drop i).take 1 ++ Q.drop (j + 1)

-- Two instructions of different blocks in the other order: the same.
example : equiv prm P (swap 5 6) outs = true := by decide +kernel

-- The second block's `pshufb` before the load of its table.
example : (Q.getD 4 (tb .xmm0 0), Q.getD 6 (tb .xmm0 0)) = (tb .xmm4 16, x .pshufb .xmm0 .xmm4) := by
  decide +kernel
example : equiv prm P (swap 4 6) outs = false := by decide +kernel
-- Its load of what it stored before the store.
example : (Q.getD 26 (tb .xmm0 0), Q.getD 28 (tb .xmm0 0)) =
    (.movdquStore ⟨.edi, 16⟩ .xmm0, .movdquLoad .xmm5 ⟨.edi, 16⟩) := by decide +kernel
example : equiv prm P (swap 26 28) outs = false := by decide +kernel

/-- `Q` with its instruction at `i` replaced. -/
def subst (i : Nat) (j : Instr) : List Instr := Q.take i ++ j :: Q.drop (i + 1)

-- One operand names the other block's register.
example : Q.getD 13 (tb .xmm0 0) = x .pxor .xmm3 .xmm2 := by decide +kernel
example : equiv prm P (subst 13 (x .pxor .xmm3 .xmm5)) outs = false := by decide +kernel
-- The operands in the other order: another node, although `pxor` commutes.
example : equiv prm P (subst 13 (x .pxor .xmm2 .xmm3)) outs = false := by decide +kernel
-- A store to another place of the buffer, and a missing one.
example : Q.getD 25 (tb .xmm0 0) = .movdquStore ⟨.edi, 0⟩ .xmm3 := by decide +kernel
example : equiv prm P (subst 25 (.movdquStore ⟨.edi, 16⟩ .xmm3)) outs = false := by decide +kernel
example : equiv prm P (Q ++ [.movdquStore ⟨.edi, 0⟩ .xmm0]) outs = false := by decide +kernel
-- A result in another register than `outs` says.
example : equiv prm P Q [(.xmm3, .xmm0)] = false := by decide +kernel

-- A store outside `[slo, shi)`, and an instruction that is not followed.
example : (run prm .init [.movdquStore ⟨.edi, 32⟩ .xmm0]).isSome = false := by decide +kernel
example : (run prm .init [.xop (.movd .xmm0 .eax)]).isSome = false := by decide +kernel

/-- What is proven of `P` holds of `Q`. -/
example {s : State} (hp : Pre prm s) {R : State → Prop}
    (h : WP isa (.block P) s fun sP => ∀ sQ : State, sQ.mem = sP.mem → (∀ ab ∈ outs, sQ.xmm ab.2 = sP.xmm ab.1) →
      (∃ f m, sQ = { s with xmm := f, mem := m }) → R sQ) : WP isa (.block Q) s R :=
  equiv_wp (by decide +kernel) hp h

end VG.Test.X86SseEquiv
