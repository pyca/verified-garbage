module

public import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
public import VerifiedGarbage.Proof.Rsa.X86.RvMontInverse
public import VerifiedGarbage.Proof.Rsa.X86.RvMontPower
public import VerifiedGarbage.Proof.Rsa.RecoverMath

/-! # Montgomery setup preserves the tracked prime-recovery workspace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {m : Nat}

theorem KS.setupInverse (h : KS g s0 A live AW liveW V ls s)
    (hm : mBase ∈ live) (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (odd : m % 2 = 1) (slots : ∀ d ∈ ls, d + 4 ≤ sInv ∨ sInv + 4 ≤ d) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.setupInverse (arr g.w mBase) sInv)) s
      fun t => KS g s0 A live AW liveW V ls t ∧ MR g m t := by
  refine WP.mono (setupInverse_ok h.ws (by have := h.lower; omega)
    ((h.arrs mBase hm).trans value) bound odd) fun t ⟨mr, k, r⟩ => ?_
  refine ⟨h.core k (by simp) (by decide) r ?_ h.live_lt ?_ h.liveW_lt ?_ h.ls_ok, mr⟩
  · exact h.arrs_w k (by simp) (by decide)
  · exact h.arrsW_w k (by simp) (by decide)
  · exact h.sl_keep k (by simpa using slots)

theorem KS.setupR2 (h : KS g s0 A live AW liveW V ls s) (mr : MR g m s)
    (hm : 1 < m)
    (hl : ∀ j ∈ live, j = mR2 ∨ (j ≠ mTmp ∧ j ≠ mAcc ∧ j ≠ mAcc + 1))
    (hlW : ∀ j ∈ liveW, ∀ i ∈ montWrites mR2, i / 2 ≠ j) :
    WP isa (setupR2 g.n) s fun t =>
      KS g s0 (upd A mR2 (2 ^ (128 * g.n) % m)) (mR2 :: live) AW liveW V ls t ∧
      MR g m t := by
  refine WP.mono (setupR2_ok mr hm h.upper) fun t ⟨mt, k, r, value⟩ => ?_
  have ht := h.montResult (by decide : mR2 < nArr) k r hl hlW
  rw [value] at ht
  exact ⟨ht, mt⟩

theorem KS.copyMont {o a : Nat} (h : KS g s0 A live AW liveW V ls s)
    (mr : MR g m s) (ho : o < nArr) (ha : a ∈ live) (hom : o ≠ mBase)
    (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (copy g.w o a) s fun t =>
      KS g s0 (upd A o (A a)) (o :: live) AW liveW V ls t ∧ MR g m t := by
  refine WP.mono (Keys.copy_ok h.ws ho (h.live_lt a ha)) fun t ⟨_, k, e, r, _⟩ => ?_
  have rest : Keeps opRegs s t := r.mono (by decide)
  exact ⟨h.write_w k ho (by simp) rest (e.trans (h.arrs a ha)) hlW (by simp),
    mr.keep k (by simpa using hom) rest⟩

theorem KS.subMont {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {o a b m : Nat}
    (h : KS g s0 A live AW liveW V ls s)
    (mr : MR g m s) (hom : o ≠ mBase) (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hoa : o ≠ a) (hob : o ≠ b)
    (le : A b ≤ A a) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 g.w o a b) s fun t =>
      KS g s0 (upd A o (A a - A b)) (o :: live) AW liveW V ls t ∧ MR g m t := by
  refine WP.mono (Keys.sub3_ok h.ws ho (h.live_lt a ha) (h.live_lt b hb) hoa hob)
    fun t ⟨_, k, value, borrow, r⟩ => ?_
  have rest : Keeps opRegs s t := r.mono (by decide)
  have ht := h.write_w k ho (by simp) rest rfl hlW (by simp)
  rw [h.arrs a ha, h.arrs b hb] at value
  let X := num t.mem g.B g.w o
  have bound : X < 2 ^ (32 * g.w) := by
    exact val32_lt _ _ _ _
  have result : X = A a - A b := by
    have zero : (t.gpr .ebx).toNat = 0 := by
      by_contra ne
      have one : (t.gpr .ebx).toNat = 1 := by omega
      rw [one, Nat.mul_one] at value
      omega
    rw [zero, Nat.mul_zero, Nat.add_zero] at value
    omega
  change num t.mem g.B g.w o = A a - A b at result
  rw [result] at ht
  exact ⟨ht, mr.keep k (by simpa using hom) rest⟩


/-- Multiplying one by R squared yields the Montgomery representation of one. -/
theorem mont_one {n m X : Nat} (odd : m % 2 = 1) (bound : X < m)
    (value : X * 2 ^ (64 * n) % m = 1 * (2 ^ (128 * n) % m) % m) :
    X = 2 ^ (64 * n) % m := by
  apply VG.Proof.Rsa.r_one (VG.Proof.Bignum.coprime_pow2 odd _) bound
    (R2 := 2 ^ (128 * n) % m)
  · rw [Nat.mod_mod, ← Nat.pow_add]
    congr 2
    omega
  · simpa only [Nat.mul_comm 1] using value

end
end VG.Proof.Rsa.X86.Recover
