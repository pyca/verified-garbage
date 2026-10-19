module

public import VerifiedGarbage.Proof.Rsa.X86.RvDivSet
public import VerifiedGarbage.Proof.Rsa.X86.KeyDiv

/-! # Dividing the modulus to obtain the second recovered factor -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

def divIds : Fin 4 → Nat := fun i => if i = 0 then aQ else if i = 1 then aRm else if i = 2 then aDv else aDt
def AQ (p q : Nat) : Nat → Nat := upd (upd (fun _ => q) aZero 0) 1 p

theorem divide_ok {g : Geo} {s0 s : State} {V : Nat → Nat} {m p : Nat}
    (h : KS g s0 (AD m p) [aQ, aDv, 1, aZero] (fun _ => 0) [] V [sMask] s)
    (top : w32 s.mem g.B (arr g.w aDv + 4 * g.w) = 0) (positive : 0 < p) :
    WP isa (VG.Impl.Rsa.X86.Div.code g.w (arr g.w aQ) (arr g.w aRm) (arr g.w aDv) (arr g.w aDt)) s
      fun t => KS g s0 (AQ p (m / p)) [1, aQ, aZero] (fun _ => 0) [] V [sMask] t := by
  refine WP.mono (div_ok (ids := divIds) h.ws (by decide) (by decide) top)
    fun t ⟨_, k, r, result⟩ => ?_
  have numerator : num s.mem g.B g.w (divIds 0) = m := by change num s.mem g.B g.w aQ = m; rw [h.arrs aQ (by simp)]; rfl
  have divisor : num s.mem g.B g.w (divIds 2) = p := by change num s.mem g.B g.w aDv = p; rw [h.arrs aDv (by simp)]; rfl
  have quotient := (result (by rw [divisor]; exact positive)).1
  rw [numerator, divisor] at quotient
  refine h.core k ?_ (by simp) (r.mono (by decide)) ?_ (by decide) (by simp [Arrs])
    (by simp) (h.sl_keep k (by simp)) h.ls_ok
  · intro j hj
    exact h.ws.arr_fit ((by decide : ∀ j ∈ [divIds 0, divIds 1, divIds 3], j < nArr) j hj)
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [k.num (by decide) (by simp) (h.ws.fit64 (by decide)), h.arrs 1 (by simp)]
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact quotient
      · rw [k.num (by decide) (by simp) (h.ws.fit64 (by decide)), h.arrs aZero (by simp)]
        rfl

end VG.Proof.Rsa.X86.Recover
