module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Proof.Rsa.X86.RvDivSet

import VerifiedGarbage.Proof.Rsa.X86.RvBatchGcd
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Div
import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvSubWrap
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import Mathlib.Tactic.SplitIfs
/-! # Computing and ordering the two factors from the search result -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvDivide.lean`, which only this module imported.
section

/-! # Dividing the modulus to obtain the second recovered factor -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

def AQ (p q : Nat) : Nat → Nat := upd (upd (fun _ => q) aZero 0) 1 p

theorem divide_ok {g : Geo} {s0 s : State} {V : Nat → Nat} {m p : Nat}
    (h : KS g s0 (AD m p) [aQ, aDv, 1, aZero] (fun _ => 0) [] V [sMask] s)
    (top : w32 s.mem g.B (arr g.w aDv + 4 * g.w) = 0) (positive : 0 < p) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.div VG.Impl.Rsa.X86.RecoverRt.nar aQ aRm aDv aDt) s
      fun t => KS g s0 (AQ p (m / p)) [1, aQ, aZero] (fun _ => 0) [] V [sMask] t := by
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.div_ok h.rt (q := aQ) (r := aRm) (d := aDv) (t := aDt)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [kw_nar]; exact top)) fun t ⟨_, k, r, result⟩ => ?_
  rw [kw_nar] at k result
  have numerator : num s.mem g.B g.w aQ = m := by rw [h.arrs aQ (by simp)]; rfl
  have divisor : num s.mem g.B g.w aDv = p := by rw [h.arrs aDv (by simp)]; rfl
  have quotient := (result (by rw [divisor]; exact positive)).1
  rw [numerator, divisor] at quotient
  have hd : ∀ d ∈ [VG.Impl.Rsa.X86.KeyRt.sCy, VG.Impl.Rsa.X86.KeyRt.sQb], SlotOk d := by decide
  have hd' : ∀ d ∈ [VG.Impl.Rsa.X86.KeyRt.sCy, VG.Impl.Rsa.X86.KeyRt.sQb], d + 4 ≤ hdr := by decide
  refine h.core k ?_ hd (r.mono (by decide)) ?_ (by decide) (by simp [Arrs])
    (by simp) (h.sl_keep k (by decide)) h.ls_ok
  · intro j hj
    exact h.ws.arr_fit ((by decide : ∀ j ∈ [aQ, aRm, aDt], j < nArr) j hj)
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [k.num (by decide) hd' (h.ws.fit64 (by decide)), h.arrs 1 (by simp)]
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact quotient
      · rw [k.num (by decide) hd' (h.ws.fit64 (by decide)), h.arrs aZero (by simp)]
        rfl

end VG.Proof.Rsa.X86.Recover
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/RvOrder.lean`, which only this module imported.
section

/-! # Ordering the recovered factors, larger first -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

def AF (p q : Nat) : Nat → Nat := upd (upd (fun _ => 0) 5 (max p q)) 6 (min p q)

theorem order_ok {g : Geo} {s0 s : State} {V : Nat → Nat} {p q : Nat}
    (h : KS g s0 (AQ p q) [1, aQ, aZero] (fun _ => 0) [] V [sMask] s) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.order s fun t => KS g s0 (AF p q) [5, 6, aZero] (fun _ => 0) [] V [sMask] t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.order
  simp only [seqs]
  refine WP.seq (WP.mono (h.subWrap (o := aW) (a := 1) (b := aQ)
    (by decide) (by simp) (by simp) (by decide) (by decide) (by simp)) fun s1 ⟨h1, borrow⟩ => ?_)
  have flag : (s1.gpr .ebx).toNat = b2n (decide (p < q)) := borrow
  refine WP.seq (WP.mono (h1.storeSlot (d := sLt) (by decide) .ebx) fun s2 ⟨h2, _, _⟩ => ?_)
  rw [flag] at h2
  refine WP.seq (WP.mono (h2.sel_w (o := 5) (a := 1) (b := aQ) (sl := sLt)
    (by decide) (by simp) (by simp) (by simp)
    (by rw [upd_self]; exact VG.Proof.Rsa.b2n_le _) (.inl (by decide)) (by simp)) fun s3 ⟨h3, _⟩ => ?_)
  refine WP.mono (h3.sel_w (o := 6) (a := aQ) (b := 1) (sl := sLt)
    (by decide) (by simp) (by simp) (by simp)
    (by rw [upd_self]; exact VG.Proof.Rsa.b2n_le _) (.inl (by decide)) (by simp)) fun t ⟨hout, _⟩ => ?_
  refine hout.mono ?_ (by simp) ?_
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;>
      simp [AF, AQ, upd, aQ, aW, aZero, b2n, Nat.max_def, Nat.min_def] <;> split_ifs <;> omega
  · intro d hd
    simp only [List.mem_singleton] at hd
    subst d
    exact ⟨by simp, upd_ne _ _ (by decide)⟩

end VG.Proof.Rsa.X86.Recover
end

end

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sub32)

theorem factors_ok {g : Geo} {s0 s : State} {A V : Nat → Nat} {m y : Nat}
    (h : KS g s0 A [mY, aN, aZ, aOne] (fun _ => 0) [] V [sMask] s)
    (modulus : A aN = m) (value : A mY = y) (zero : A aZ = 0) (one : A aOne = 1)
    (odd : m % 2 = 1) (hm : 1 < m) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.factors s fun t =>
      KS g s0 (AF (Nat.gcd (sub32 g.w y 1) m) (m / Nat.gcd (sub32 g.w y 1) m))
        [5, 6, aZero] (fun _ => 0) [] V [sMask] t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.factors
  simp only [seqs, VG.Impl.Rsa.X86.RecoverRt.factorTail]
  refine WP.seq (WP.mono (gcdSet_ok h modulus value zero one) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (batchGcd_ok h1 odd) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (divSet_ok h2) fun s3 ⟨h3, top⟩ => ?_)
  refine WP.seq (WP.mono (divide_ok h3 top (Nat.gcd_pos_of_pos_right _ (by omega))) fun s4 h4 => ?_)
  exact order_ok h4

end VG.Proof.Rsa.X86.Recover
