module
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.CrtLinksCT
import VerifiedGarbage.Proof.Bignum.Arm.SetupCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Public geometry determines the main CRT initialization trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (arrAt)

structure CrtMainInput (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  ptr : s.gpr .r0 = base
  count : s.gpr .r7 = BitVec.ofNat 32 w
  zero : s.gpr .r3 = 0

theorem crt_setupMain_ct {base : BitVec 32} {len w : Nat} (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (fits : arrAt w 8 ≤ 8 * len) :
    RelCT isa (fun s t => CrtMainInput base len w s ∧ CrtMainInput base len w t) setupMain (fun _ _ => True) := by
  let P := CrtMainInput base len w
  have first : RelCT isa (fun s t => P s ∧ P t) setup (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨setup_ct s t tr1 tr2 u v trivial trivial (h.1.ptr.trans h.2.ptr.symm) e1 e2, trivial⟩
  have wp (s : State) (h : P s) : WP isa setup s (CrtLinksInput base (8 * len) w) := by
    refine WP.mono (setup_frame_ok s h.workspace hw hw' fits h.ptr h.count h.zero) ?_
    rintro t ⟨layout, width, ptr, _, rest⟩
    have shape : CrtLayoutState base len w t.mem := ⟨layout, width⟩
    exact ⟨h.workspace.congr rest.wr, ptr, shape.nativeCount (h.workspace.congr rest.wr)⟩
  have size : 52 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  exact (pair_posts first wp).seq (crt_links_ct size)

end VG.Proof.Bignum.Arm
