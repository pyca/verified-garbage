module

public import VerifiedGarbage.Proof.Rsa.X86.RvGcdSet
import VerifiedGarbage.Proof.Rsa.X86.InvLoop
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.InvLoop
import VerifiedGarbage.Proof.Rsa.X86.RvFrames
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic.Push
import Mathlib.Algebra.NeZero
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The first recovered factor from the verified binary GCD -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sub32)

def AP (m p : Nat) : Nat → Nat := upd (upd (fun _ => m) aZero 0) 1 p

theorem gcd_ok {g : Geo} {s0 s : State} {V : Nat → Nat} {m y : Nat}
    (h : KS g s0 (AG g.w m y) liveG (fun _ => 0) [] V [sMask] s)
    (odd : m % 2 = 1) (hm : 1 < m) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.inverse VG.Impl.Rsa.X86.RecoverRt.nar) s fun t =>
      KS g s0 (AP m (Nat.gcd (sub32 g.w y 1) m)) [1, aN, aZero] (fun _ => 0) [] V [sMask] t := by
  have vn : num s.mem g.B g.w aM = m := by rw [h.arrs aM (by simp [liveG])]; rfl
  have vz : num s.mem g.B g.w aZero = 0 := by rw [h.arrs aZero (by simp [liveG])]; rfl
  have vu : num s.mem g.B g.w 0 = sub32 g.w y 1 := by rw [h.arrs 0 (by simp [liveG])]; rfl
  have vm : num s.mem g.B g.w aNM = sub32 g.w 0 m := by rw [h.arrs aNM (by simp [liveG])]; rfl
  have ml : m < 2 ^ (32 * g.w) := by rw [← vn]; exact val32_lt _ _ _ _
  have bankValue : bank s.mem g.B g.w 0 = (num s.mem g.B g.w 0, num s.mem g.B g.w aM, 1, 0) := by
    simp only [bank]
    rw [h.arrs 1 (by simp [liveG]), h.arrs 2 (by simp [liveG]), h.arrs 3 (by simp [liveG]), vn]
    rfl
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.inverse_ok h.rt (by decide)) fun t ⟨_, k, r, inv⟩ => ?_
  rw [kw_nar] at k inv
  have result := (inv (by rw [vn, vm]; unfold sub32; rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; show 2 ^ (32 * g.w) - m + m = 2 ^ (32 * g.w); omega)
    vz (by rw [vn]; exact odd) (by rw [vn]; exact hm) bankValue).1
  rw [vn, vu] at result
  refine h.core k ?_ (by decide) (r.mono (by decide)) ?_ (by decide) (by simp [Arrs])
    (by simp) (h.sl_keep k (by decide)) h.ls_ok
  · intro j hj
    exact h.ws.arr_fit ((by decide : ∀ j ∈ invArrs, j < nArr) j hj)
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact result
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · rw [k.num (by decide) (by decide) (h.ws.fit64 (by decide)), h.arrs aN (by simp [liveG])]
        rfl
      · rw [k.num (by decide) (by decide) (h.ws.fit64 (by decide)), h.arrs aZero (by simp [liveG])]
        rfl

end VG.Proof.Rsa.X86.Recover
