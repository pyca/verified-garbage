module

public import VerifiedGarbage.Proof.Rsa.X86.RvMontGeometry

import VerifiedGarbage.Proof.Rsa.X86.RvMontPower
import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvMontFrame
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Rsa.X86.RvWrite
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Word
import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.RvBase
/-! # The prime-recovery Montgomery setup stage -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvMontSetup.lean`, which only this module imported.
section

/-! # Montgomery setup preserves the tracked prime-recovery workspace -/

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverRt (nar)
open VG.Impl.Rsa.X86.KeyRt (sub3)
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {m : Nat}

theorem KS.subMont {o a b : Nat} (h : KS g s0 A live AW liveW V ls s)
    (mr : MR g m s) (hom : o ≠ mBase) (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live)
    (le : A b ≤ A a) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 nar o a b) s fun t =>
      KS g s0 (upd A o (A a - A b)) (o :: live) AW liveW V ls t ∧ MR g m t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.sub3_ok h.rt ho (h.live_lt a ha) (h.live_lt b hb))
    fun t ⟨_, k, value, borrow, r⟩ => ?_
  rw [kw_nar] at k value
  have rest : Keeps opRegs s t := r.mono (by decide)
  have ht := h.write_w k ho (by simp) rest rfl hlW (by simp)
  rw [h.arrs a ha, h.arrs b hb] at value
  replace value : num t.mem g.B g.w o + A b = A a + 2 ^ (32 * g.w) * (t.gpr .ebx).toNat := value
  have bound : num t.mem g.B g.w o < 2 ^ (32 * g.w) := val32_lt _ _ _ _
  have result : num t.mem g.B g.w o = A a - A b := by
    have zero : (t.gpr .ebx).toNat = 0 := by
      by_contra ne
      have one : (t.gpr .ebx).toNat = 1 := by omega
      rw [one, Nat.mul_one] at value
      omega
    rw [zero, Nat.mul_zero, Nat.add_zero] at value
    omega
  rw [result] at ht
  exact ⟨ht, mr.keepD h.ws k (by simpa using hom) (by simp) (by simp)⟩

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
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvMontInverse.lean`, which only this module imported.
section

/-! # The negative Montgomery inverse of the public recovery modulus

`KS.setupInverse`: `setupInverse` reads `[mBase]`'s low word through a
pointer to the array, and stores `-m⁻¹ mod 2³²` in the header word `sInv`.
-/

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {m : Nat}

theorem KS.setupInverse (h : KS g s0 A live AW liveW V ls s)
    (hm : mBase ∈ live) (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (odd : m % 2 = 1) (slots : ∀ d ∈ ls, d + 4 ≤ sInv ∨ sInv + 4 ≤ d) :
    WP isa (.block VG.Impl.Rsa.X86.RecoverRt.setupInverse) s
      fun t => KS g s0 A live AW liveW V ls t ∧ MR g m t := by
  have positive : 0 < g.n := by have := h.lower; omega
  have header := h.ws.hdr_le
  have nw := h.ws.workspace.nowrap
  have hv : num s.mem g.B g.w mBase = m := (h.arrs mBase hm).trans value
  have kn := kw_nar g.n
  unfold VG.Impl.Rsa.X86.RecoverRt.setupInverse
  simp only [List.append_assoc]
  refine VG.Proof.Rsa.X86.KeyRt.lowPtr_ok h.rt (by decide : mBase < nArr) fun u hu K mu p => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (VG.Proof.Rsa.X86.KeyRt.lowSrc hu (by decide) p) fun v Vv _ => ?_
  have low := VG.Proof.Rsa.X86.KeyRt.low_word (B := g.B) (m := u.mem) (j := mBase)
    (w := VG.Proof.Rsa.X86.KeyRt.kw (8 * g.n + 8)) (by rw [kn]; unfold width; omega)
  rw [mu, kn] at low
  have hodd : (v.gpr .ebx).toNat % 2 = 1 := by
    rw [Vv.gpr, mu, kn, ← low, hv, Nat.mod_mod_of_dvd _ (by decide), odd]
  refine WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.inverse_ok v hodd) fun x ⟨inv, kx, mx⟩ => ?_)
  have Kx : Keeps opRegs s x :=
    ((K.mono (by decide)).trans (Vv.keeps.mono (by decide))).trans (kx.mono (by decide))
  have hs : Scr x g.B g.Z := h.ws.workspace.of_keeps Kx (by decide)
  refine wp_storeS (hs.ea (by unfold sInv hdr at *; omega)) (hs.write (by unfold sInv hdr at *; omega))
    fun t mt => WP.block_nil ?_
  have ms : x.mem = s.mem := by rw [mx, Vv.mem, mu]
  have frame : Outside g.B sInv 4 s.mem t.mem := by
    rw [mt.mem, ms]
    exact writeW32_outside _ _ _ (by unfold sInv hdr at *; omega)
  have k : Keep g.B g.w [] [sInv] s.mem t.mem := Keep.of_slot frame (by simp)
  have r : Keeps opRegs s t := Kx.trans (mt.keeps [] |>.mono (by decide))
  refine ⟨h.core k (by simp) (by simp [sInv]; decide) r (h.arrs_w k (by simp) (by simp [sInv]; decide)) h.live_lt
    (h.arrsW_w k (by simp) (by simp [sInv]; decide)) h.liveW_lt (h.sl_keep k (by simpa using slots)) h.ls_ok,
    positive, ?_, bound, ?_⟩
  · rw [k.num (by simp) (by decide) (h.ws.fit64 (by decide)), hv]
  · have stored : w32 t.mem g.B sInv = (x.gpr .eax).toNat := by rw [mt.mem, w32_write_self]
    rw [Vv.gpr, mu, kn] at inv
    have lowBound : (s.mem.readW (off g.B (arr g.w mBase)) 32).toNat < 2 ^ 32 :=
      (s.mem.readW (off g.B (arr g.w mBase)) 32).isLt
    have product : m * w32 t.mem g.B sInv % 2 ^ 32 =
        (s.mem.readW (off g.B (arr g.w mBase)) 32).toNat * (x.gpr .eax).toNat % 2 ^ 32 := by
      rw [stored, Nat.mul_mod m, Nat.mul_mod (s.mem.readW _ 32).toNat, ← hv, low,
        Nat.mod_eq_of_lt lowBound]
    rw [Nat.add_mod, product, ← Nat.add_mod]
    exact inv

end
end VG.Proof.Rsa.X86.Recover
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvSubtract.lean`, which only this module imported.
section

/-! # Recovery subtraction without a borrow -/

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.RecoverRt (nar)
open VG.Impl.Rsa.X86.KeyRt (sub3)
open VG.Proof.Rsa.X86.Keys

theorem KS.sub_w {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {o a b : Nat}
    (h : KS g s0 A live AW liveW V ls s)
    (ho : o < nArr) (ha : a ∈ live) (hb : b ∈ live) (hoa : o ≠ a) (hob : o ≠ b)
    (le : A b ≤ A a) (hlW : ∀ j ∈ liveW, o / 2 ≠ j) :
    WP isa (sub3 nar o a b) s fun t =>
      KS g s0 (upd A o (A a - A b)) (o :: live) AW liveW V ls t ∧ Keeps opRegs s t := by
  refine WP.mono (h.sub3_w ho ha hb hoa hob hlW) fun t ⟨X, ht, r, value, borrow⟩ => ?_
  have bound : X < 2 ^ (32 * g.w) := by
    have v := ht.arrs o (by simp)
    rw [upd_self] at v
    rw [← v]
    exact val32_lt _ _ _ _
  have result : X = A a - A b := by
    have zero : (t.gpr .ebx).toNat = 0 := by
      by_contra ne
      have one : (t.gpr .ebx).toNat = 1 := by omega
      rw [one, Nat.mul_one] at value
      omega
    rw [zero, Nat.mul_zero, Nat.add_zero] at value
    omega
  rw [result] at ht
  exact ⟨ht, r⟩

end VG.Proof.Rsa.X86.Recover
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

def AM (A : Nat → Nat) (n m : Nat) : Nat → Nat :=
  upd (upd (upd (upd (upd (upd (upd A aZ 0) aOne 1) mBase m)
    mR2 (2 ^ (128 * n) % m)) mXm (2 ^ (64 * n) % m)) aO (2 ^ (64 * n) % m))
    aNg (m - 2 ^ (64 * n) % m)

theorem upd_twice (A : Nat → Nat) (j x y : Nat) : upd (upd A j x) j y = upd A j y := by
  funext i
  simp only [upd]
  split <;> rfl

abbrev liveM : List Nat := [aNg, aO, mR2, mBase, aOne, aZ, aN]

/-- The arrays after `montHead`. -/
def AH (A : Nat → Nat) (n m : Nat) : Nat → Nat :=
  upd (upd (upd (upd (upd A aZ 0) aOne 1) mBase m) mR2 (2 ^ (128 * n) % m)) mXm 1

abbrev liveH : List Nat := [mXm, mR2, mBase, aOne, aZ, aN]

theorem montHead_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m : Nat}
    (h : KS g s0 A [aN] AW [wR] V [sTc, sCnt] s)
    (value : A aN = m) (bound : m < 2 ^ (64 * g.n))
    (odd : m % 2 = 1) (hm : 1 < m) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.montHead s fun t =>
      KS g s0 (AH A g.n m) liveH AW [wR] V [sTc, sCnt] t ∧ MR g m t := by
  have value32 : A 32 = m := value
  unfold VG.Impl.Rsa.X86.RecoverRt.montHead
  simp only [seqs]
  refine WP.seq (WP.mono (h.sub_w (o := aZ) (a := aN) (b := aN)
    (by decide) (by simp) (by simp) (by decide) (by decide) (by omega_arith)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s1 ⟨h1, _⟩ => ?_)
  simp only [Nat.sub_self] at h1
  refine WP.seq (WP.mono (h1.copy_w (o := aOne) (a := aZ) (by decide) (by simp) (by decide)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s2 ⟨h2, _, _⟩ => ?_)
  simp only [upd_self] at h2
  refine WP.seq (WP.mono (h2.setOne_w (j := aOne) (by simp)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s3 ⟨h3, _⟩ => ?_)
  simp only [upd_self, Nat.zero_div, Nat.mul_zero, Nat.add_zero, upd_twice] at h3
  refine WP.seq (WP.mono (h3.copy_w (o := mBase) (a := aN) (by decide) (by simp) (by decide)
    (by simp only [List.mem_singleton]; rintro j rfl; decide)) fun s4 ⟨h4, _, _⟩ => ?_)
  have vn : upd (upd A aZ 0) aOne 1 aN = m := by simpa only [upd, show aN ≠ aOne by decide, show aN ≠ aZ by decide, ite_false] using value
  rw [vn] at h4
  refine WP.seq (WP.mono (h4.setupInverse (by simp) (by simp [upd]) bound odd
    (by decide)) fun s5 ⟨h5, mr5⟩ => ?_)
  refine WP.seq (WP.mono (h5.setupR2 mr5 hm (by simp) (by simp [upd, aN, aZ, aOne, mBase, value32]) (by simp)
    (by simp [upd, aZ, aOne, mBase]) (by simp) (by simp [upd, aOne, mBase]) (by decide) (by decide) (by decide)) fun s6 ⟨h6, mr6⟩ => ?_)
  refine WP.mono (h6.copyMont mr6 (o := mXm) (a := aOne) (by decide)
    (by simp) (by decide) (by decide) (by decide)) fun s7 ⟨h7, mr7, _⟩ => ?_
  have vone : upd (upd (upd (upd A aZ 0) aOne 1) mBase m)
      mR2 (2 ^ (128 * g.n) % m) aOne = 1 := by simp [upd, aOne, mBase, mR2]
  rw [vone] at h7
  refine ⟨h7.mono (fun j hj => ⟨?_, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩), mr7⟩
  simp only [liveH, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
  omega_arith


theorem mont_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m : Nat}
    (h : KS g s0 A [aN] AW [wR] V [sTc, sCnt] s)
    (value : A aN = m) (bound : m < 2 ^ (64 * g.n))
    (odd : m % 2 = 1) (hm : 1 < m) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.mont s fun t =>
      KS g s0 (AM A g.n m) liveM AW [wR] V [sTc, sCnt] t ∧ MR g m t := by
  have value32 : A 32 = m := value
  unfold VG.Impl.Rsa.X86.RecoverRt.mont
  simp only [seqs]
  refine WP.seq (WP.mono (montHead_ok h value bound odd hm) fun s7 ⟨h7, mr7⟩ => ?_)
  refine WP.seq (WP.mono (h7.mmul mr7 (o := mXm) (a := mXm) (b := mR2)
    (by decide) (by decide) (by decide) (by decide) (by simp) (by simp)
    (by simpa [AH, upd] using hm)
    (by simpa [AH, upd, mXm, mR2] using Nat.mod_lt (2 ^ (128 * g.n)) (by omega_arith : 0 < m))
    (by decide) (by decide)) fun s8 ⟨X, h8, mr8, _, xlt, xe⟩ => ?_)
  have vx : X = 2 ^ (64 * g.n) % m := mont_one odd xlt (by simpa [AH, upd, mXm, mR2] using xe)
  rw [vx] at h8
  unfold VG.Impl.Rsa.X86.RecoverRt.montTail
  simp only [seqs]
  refine WP.seq (WP.mono (h8.copyMont mr8 (o := aO) (a := mXm) (by decide)
    (by simp) (by decide) (by decide) (by decide)) fun s9 ⟨h9, mr9, _⟩ => ?_)
  simp only [upd_self] at h9
  refine WP.mono (h9.subMont mr9 (o := aNg) (a := aN) (b := aO)
    (by decide) (by decide) (by simp) (by simp)
    (by simpa [AH, upd, aN, aZ, aOne, mBase, mR2, mXm, aO, value32] using
      Nat.le_of_lt (Nat.mod_lt (2 ^ (64 * g.n)) (by omega_arith : 0 < m)))
    (by decide)) fun t ⟨ht, mt⟩ => ?_
  refine ⟨ht.mono ?_ (by simp) (by simp), mt⟩
  intro j hj
  simp only [liveM, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [AM, AH, upd, aNg, aO, mXm, mR2, mBase, aOne, aZ, aN, value32]

end VG.Proof.Rsa.X86.Recover
