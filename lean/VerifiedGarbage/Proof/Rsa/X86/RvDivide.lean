module

public import VerifiedGarbage.Proof.Rsa.X86.RvDivSet
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Div
import VerifiedGarbage.Proof.Rsa.X86.RvFrames

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
