module

public import VerifiedGarbage.Proof.Rsa.X86.KcLoadsTiming
public import VerifiedGarbage.Proof.Rsa.X86.KcCoreTiming

/-! # Fixed-width key validation has a trace independent of private components -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys

theorem core_ready {g : CallGeometry} {s : State} {v : Vals} (h : Inputs g s)
    (start : BodyIn (geometry g) v s) :
    WP isa (if g.full then keyBody (2 * g.n) else crtBody (2 * g.n)) s fun t =>
      Inputs g t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have finish {t : State} {A : Nat → Nat} {live : List Nat} {c : Bool}
      (ht : Stg (geometry g) s A live c t) :
      Inputs g t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
    have frame := h.keepOutside ht.keep (fun j hj => List.mem_range.mp hj) (by decide)
    exact ⟨h.after ht.rest (by decide) (by decide) (h.scratchFrame frame), ht.rest.mono (by decide)⟩
  split
  · exact WP.mono (keyBody_ok start) fun _ ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ht⟩ => finish ht
  · exact WP.mono (crtBody_ok start) fun _ ⟨_, _, _, _, _, _, _, ht⟩ => finish ht

theorem return_relCT (g : CallGeometry) : RelCT isa (Pair g)
    (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc sMask))]) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (VG.Proof.Mont.X86.Dynamic.workspaceTaint false)
    (fun _ _ h => h.workspace) (hc := .block [])
  rfl

theorem sized_relCT (g : CallGeometry) : RelCT isa (Pair g) (sized g.full g.n) (fun _ _ => True) := by
  intro s t tr ur sf tf h es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      obtain ⟨eq1, pair1⟩ := loads_relCT g _ _ _ _ _ _ h e1 f1
      obtain ⟨hs, ss, _, _⟩ := wp_result (loads_ok h.left) e1
      obtain ⟨ht, st, _, _⟩ := wp_result (loads_ok h.right) f1
      cases er with
      | @seq _ _ _ x _ _ _ e2 e3 =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 f3 =>
          have eq2 := core_constantTime g.full (2 * g.n) _ _ _ _ _ _ trivial trivial pair1.workspace e2 f2
          obtain ⟨hx, kx⟩ := wp_result (core_ready hs ss) e2
          obtain ⟨hy, ky⟩ := wp_result (core_ready ht st) f2
          have pair2 := pair1.after hx hy kx ky (by decide)
          have eq3 := (return_relCT g _ _ _ _ _ _ pair2 e3 f3).1
          exact ⟨by rw [eq1, eq2, eq3], trivial⟩
end VG.Proof.Rsa.X86.KeyCheck
