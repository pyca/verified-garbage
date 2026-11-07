module

import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Sha512.Spec
public import VerifiedGarbage.Impl.Sha512.X86_64.Avx2
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# SHA-512 with AVX2 on x86-64: one round

`round j t` computes `roundKW`, with `Σ₀` and `Σ₁` as three `rorx`, `Ch` as a
sum of two disjoint masks and `Maj` from the previous round's `a ⊕ b`.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha512.X86_64.Avx2
open VG.Spec.Sha512 (HashValue Word Block K W bsig0 bsig1 ch maj)
open VG.Proof.Sha512 (roundKW rounds_succ round_eq)

/-- The working variables `v` are in the registers of round `t`, and
`b ⊕ c` is in `carry t`. -/
def Vars (t : Nat) (s : State) (v : HashValue) : Prop :=
  s.gpr (var t 0) = v[0] ∧ s.gpr (var t 1) = v[1] ∧ s.gpr (var t 2) = v[2] ∧
  s.gpr (var t 3) = v[3] ∧ s.gpr (var t 4) = v[4] ∧ s.gpr (var t 5) = v[5] ∧
  s.gpr (var t 6) = v[6] ∧ s.gpr (var t 7) = v[7] ∧ s.gpr (carry t) = v[1] ^^^ v[2]

/-- The registers that hold pointers and the count, and `rsp`: never written
by the rounds. -/
def pubRegs : List Reg := [.rdi, .rsi, .rdx, .rcx, .rsp]

theorem var_succ (t k : Nat) (hk : k < 7) : var (t + 1) (k + 1) = var t k := by
  simp only [var]; congr 1; omega

theorem var_succ_zero (t : Nat) : var (t + 1) 0 = var t 7 := by
  simp only [var]; congr 1; omega

/-- The registers of a round are all different. -/
theorem round_nodup (t : Nat) :
    [var t 0, var t 1, var t 2, var t 3, var t 4, var t 5, var t 6, var t 7, carry t, carry (t + 1), T,
      .rdi, .rsi, .rdx, .rcx, .rsp].Nodup := by
  have e : carry (t + 1) = if t % 2 = 0 then .r14 else .r13 := by
    simp only [carry]; split <;> split <;> first | rfl | omega
  rw [e]
  simp only [var, carry]
  have h8 := Nat.mod_lt t (show 8 > 0 by omega)
  rw [show t % 2 = t % 8 % 2 by omega]
  generalize t % 8 = c at *
  revert h8; revert c; decide +kernel

theorem ch_add (e f g : Word) : ch e f g = (e &&& f) + (~~~e &&& g) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i hi
    simp only [ch, BitVec.getElem_xor, BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases e[i] <;> cases f[i] <;> cases g[i] <;> rfl
  · ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases e[i] <;> cases f[i] <;> cases g[i] <;> rfl

theorem maj_carry (a b c : Word) : maj a b c = (b ^^^ c) &&& (a ^^^ b) ^^^ b := by
  ext i hi
  simp only [maj, BitVec.getElem_xor, BitVec.getElem_and]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

theorem bsig0_rorx (x : Word) : bsig0 x = x.rotateRight 28 ^^^ x.rotateRight 34 ^^^ x.rotateRight 39 := rfl
theorem bsig1_rorx (x : Word) : bsig1 x = x.rotateRight 14 ^^^ x.rotateRight 18 ^^^ x.rotateRight 41 := rfl

/-- `T₁` in the order the round adds it up. -/
theorem t1_order (h e f g k w : Word) :
    h + k + w + ((e &&& f) + (~~~e &&& g)) +
        (e.rotateRight 14 ^^^ e.rotateRight 18 ^^^ e.rotateRight 41) =
      h + bsig1 e + ch e f g + k + w := by
  rw [ch_add, bsig1_rorx]; ac_rfl

/-! ## Rounds of a block -/

/-- What the rounds leave alone. -/
def Keeps (s s' : State) : Prop :=
  s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ pubRegs, s'.gpr r = s.gpr r) ∧
    s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi

theorem Keeps.refl (s : State) : Keeps s s := ⟨rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {s₁ s₂ s₃ : State} (h₁ : Keeps s₁ s₂) (h₂ : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    fun r hr => (h₂.2.2.2.1 r hr).trans (h₁.2.2.2.1 r hr), h₂.2.2.2.2.1.trans h₁.2.2.2.2.1,
    h₂.2.2.2.2.2.trans h₁.2.2.2.2.2⟩

/-- Round `t` of block `j` can read `Wₜ` of `M`. -/
def WOk (j : Nat) (M : Block) (s : State) (t : Nat) : Prop :=
  InRegions (s.rd ++ s.wr) (s.ea (wSlot j t)) 8 ∧ s.mem.readW (s.ea (wSlot j t)) 64 = W M t

theorem WOk.keeps {j : Nat} {M : Block} {s s' : State} {t : Nat} (h : WOk j M s t) (hk : Keeps s s') :
    WOk j M s' t := by
  have e : s'.ea (wSlot j t) = s.ea (wSlot j t) := by
    simp only [State.ea, wSlot, at_, hk.2.2.2.1 .rcx (by decide)]
  rw [WOk, e, hk.1, hk.2.1, hk.2.2.1]; exact h

end VG.Proof.Sha512.X86_64.Avx2
