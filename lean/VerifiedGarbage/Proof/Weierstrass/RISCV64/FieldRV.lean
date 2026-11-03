module

public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# The functions of `Proof/Weierstrass/MontContract.lean` on RISC-V, by register

The contracts of `vg_<curve>_{mul,add,sub}_mod_<p|n>` stated on the
registers the code reads (`mulRV`, `addRV`, `subRV`): `ws` in `a0`, aligned,
as a `[u64]` is, and the offsets' low words in `a1`–`a3`, the callee's
regions `ws` alone. Their own working space (`rvOwn` to `rvOwnEnd`) is
the `64 k` bytes below byte 4096 (`Impl.Weierstrass.Mont.ownAt k`) for up
to six words, and the top `64 k` bytes of the working space for more, so
that a wider field's operands may take every byte below 4096. Each field's
proof shows its code meets them, and the shared contracts follow; callers (`Proof/Weierstrass/RISCV64/Call.lean`)
use them at their calls. The calls' offsets are zero-extended multiples of 8
(`OffsOk`), for which each function has code without its entry's
zero-extension and copies, meeting the contracts for them (`alignedC`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64

open VG VG.RISCV64
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus ownAt ownBytes wsBytes)

/-- An offset argument, the low word of its register. -/
abbrev offArg (s : State) (r : Reg) : BitVec 32 := (s.gpr r).setWidth 32

/-- Where the own working space of `k`-word functions starts. -/
def rvOwn (k : Nat) : Nat := if k ≤ 6 then ownAt k else wsBytes - ownBytes k

/-- Where it ends. -/
def rvOwnEnd (k : Nat) : Nat := if k ≤ 6 then 4096 else wsBytes

theorem rvOwn_cases (k : Nat) :
    (k ≤ 6 ∧ rvOwn k = 4096 - 64 * k ∧ rvOwnEnd k = 4096) ∨
      (6 < k ∧ rvOwn k = 8192 - 64 * k ∧ rvOwnEnd k = 8192) := by
  simp only [rvOwn, rvOwnEnd, ownAt, ownBytes, wsBytes]
  by_cases h : k ≤ 6
  · exact .inl ⟨h, by simp only [h, ↓reduceIte], by simp only [h, ↓reduceIte]⟩
  · exact .inr ⟨by omega, by simp only [h, ↓reduceIte], by simp only [h, ↓reduceIte]⟩

theorem rvOwn_le {k : Nat} (h : k ≤ 6) : rvOwn k = ownAt k := by simp only [rvOwn, h, ↓reduceIte]

theorem rvOwnEnd_le {k : Nat} (h : k ≤ 6) : rvOwnEnd k = 4096 := by simp only [rvOwnEnd, h, ↓reduceIte]

/-- What the three contracts by register share. -/
def rvPre (S : Modulus) (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    S.Fit (offArg s .a1) (offArg s .a2) (offArg s .a3) (rvOwn S.k) ∧ (s.gpr .a0).toNat % 8 = 0

/-- The number at the offset in `r`. -/
abbrev arg (S : Modulus) (s : State) (r : Reg) : Nat := numAt s.mem (s.gpr .a0) (offArg s r) S.k

/-- The result. -/
abbrev res (S : Modulus) (s s' : State) : Nat := numAt s'.mem (s.gpr .a0) (offArg s .a1) S.k

/-- What two runs agree on. -/
def rvPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ offArg s₁ .a1 = offArg s₂ .a1 ∧ offArg s₁ .a2 = offArg s₂ .a2 ∧
    offArg s₁ .a3 = offArg s₂ .a3 ∧ s₁.sp = s₂.sp

def mulRV (S : Modulus) : Contract isa where
  pre s := rvPre S s ∧ arg S s .a3 < S.m
  post s s' := res S s s' < S.m ∧ res S s s' * S.R % S.m = arg S s .a2 * arg S s .a3 % S.m ∧
    Keeps S.k (s.gpr .a0) (offArg s .a1) s.mem s'.mem (rvOwn S.k) (rvOwnEnd S.k)
  pub := rvPub

def addRV (S : Modulus) : Contract isa where
  pre s := rvPre S s ∧ arg S s .a2 + arg S s .a3 < 2 * S.m
  post s s' := res S s s' = (arg S s .a2 + arg S s .a3) % S.m ∧
    Keeps S.k (s.gpr .a0) (offArg s .a1) s.mem s'.mem (rvOwn S.k) (rvOwnEnd S.k)
  pub := rvPub

def subRV (S : Modulus) : Contract isa where
  pre s := rvPre S s ∧ arg S s .a2 < S.m ∧ arg S s .a3 < S.m
  post s s' := res S s s' = (arg S s .a2 + S.m - arg S s .a3) % S.m ∧
    Keeps S.k (s.gpr .a0) (offArg s .a1) s.mem s'.mem (rvOwn S.k) (rvOwnEnd S.k)
  pub := rvPub

/-- The offsets' registers as the calls set them: below `2³²`, multiples of 8. -/
def OffsOk (s : State) : Prop :=
  ∀ r ∈ [Reg.a1, .a2, .a3], (s.gpr r).toNat < 2 ^ 32 ∧ (s.gpr r).toNat % 8 = 0

/-- `K` for offsets as the calls set them (`OffsOk`): the contracts of the
functions without the entry's zero-extension and copies. -/
def alignedC (K : Contract isa) : Contract isa where
  pre s := K.pre s ∧ OffsOk s
  post := K.post
  pub := K.pub

/-- Code meets a contract by register. -/
abbrev Meets (c : Prog isa) (k : Contract isa) : Prop :=
  ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'

end VG.Proof.Weierstrass.RISCV64
