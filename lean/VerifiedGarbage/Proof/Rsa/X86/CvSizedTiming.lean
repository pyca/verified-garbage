module

import VerifiedGarbage.Proof.Rsa.X86.CvLoadsTiming
public import VerifiedGarbage.Proof.Rsa.X86.CvStoresTiming
public import VerifiedGarbage.Proof.Rsa.X86.CvLoads
import VerifiedGarbage.Proof.Rsa.X86.CvCoreTiming
import VerifiedGarbage.Proof.Rsa.X86.CvLoad
import VerifiedGarbage.Proof.Rsa.X86.CvCore
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Complete fixed-width CRT calculation has a secret-independent trace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

theorem core_ready {g : CallGeometry} {s : State} {m : Mem} (h : Inputs g s)
    (start : Start (arithmeticGeometry g m) s) :
    WP isa (VG.Impl.Rsa.X86.CrtValues.core (2 * g.n)) s fun t =>
      Inputs g t ∧ Ready g t ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (core_ok start) fun t ⟨keep, rest, zero, _, _, _, computed⟩ => ?_
  have outside := h.keepOutside keep (by decide) (by decide)
  have ht := h.after rest (by decide) (by decide) (h.scratchFrame outside)
  obtain ⟨_, mask, _⟩ := computed.mask
  exact ⟨ht, ⟨zero, _, mask⟩, rest.mono (by decide)⟩

theorem sized_relCT (g : CallGeometry) : RelCT isa (Pair g) (sized g.n) (fun _ _ => True) := by
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
          have eq2 := core_constantTime (2 * g.n) _ _ _ _ _ _ trivial trivial pair1.workspace e2 f2
          obtain ⟨hx, rx, kx⟩ := wp_result (core_ready hs ss) e2
          obtain ⟨hy, ry, ky⟩ := wp_result (core_ready ht st) f2
          have pair2 := pair1.after hx hy kx ky (by decide)
          have eq3 := (stores_relCT g _ _ _ _ _ _ ⟨pair2, rx, ry⟩ e3 f3).1
          exact ⟨by rw [eq1, eq2, eq3], trivial⟩

end VG.Proof.Rsa.X86.CrtValues
