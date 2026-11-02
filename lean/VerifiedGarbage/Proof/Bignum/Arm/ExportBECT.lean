module

import VerifiedGarbage.Proof.Bignum.Arm.ReverseBytesCT
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
public import VerifiedGarbage.Impl.Bignum.Arm.ExportBE
import VerifiedGarbage.Proof.Bignum.Arm.ExportBEArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.ReverseBytesCT
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
meta import VerifiedGarbage.Impl.Bignum.Arm.ExportBE
meta import VerifiedGarbage.Proof.Bignum.Arm.ExportBEArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # I2OSP serialization has public addresses and output length -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem exportBE_ct {base dst : BitVec 32} {len w o k : Nat} (ho : o < 8) (hk : 0 < k) :
    RelCT isa (fun s t => SmallFnReady base len w o s ∧ SmallFnReady base len w o t ∧
      s.gpr .r4 = dst ∧ t.gpr .r4 = dst ∧ s.gpr .r6 = BitVec.ofNat 32 k ∧
      t.gpr .r6 = BitVec.ofNat 32 k) exportBE (fun _ _ => True) := by
  let P := fun s : State => SmallFnReady base len w o s ∧ s.gpr .r4 = dst ∧ s.gpr .r6 = BitVec.ofNat 32 k
  let Q := fun s : State => s.gpr .r0 = dst ∧
    s.gpr .r1 = base + BitVec.ofNat 32 (arrAt w o) + BitVec.ofNat 32 (k - 1) ∧ s.gpr .lr = BitVec.ofNat 32 k
  have args : RelCT isa (fun s t => P s ∧ P t) (.block exportBEArgs) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0, .r2]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.ptr.trans h.2.1.ptr.symm
    · exact h.1.1.index.trans h.2.1.index.symm
  have wp (s : State) (h : P s) : WP isa (.block exportBEArgs) s Q := by
    have fits := h.1.layout.2.2.1
    have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
    have header := nativeHeader_of_layout s.mem base h.1.workspace.nowrap (Nat.le_refl _) h.1.layout
    rw [h.1.width] at header
    exact WP.mono (exportBEArgs_ok s h.1.workspace size header ho hk h.1.ptr h.1.index h.2.2)
      (fun _ j => ⟨j.1.trans h.2.1, j.2.1, j.2.2.1⟩)
  have copy : RelCT isa (fun s t => Q s ∧ Q t) reverseBytes (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨reverseBytes_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.trans h.2.1.symm, h.1.2.1.trans h.2.2.1.symm,
        h.1.2.2.trans h.2.2.2.symm⟩ e1 e2, trivial⟩
  have restore : RelCT isa (fun _ _ => True) (.block [.mov .r0 (.reg .r5)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact ((pair_posts args wp).seq (copy.seq restore)).mono
    (fun _ _ h => ⟨⟨h.1, h.2.2.1, h.2.2.2.2.1⟩, ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.2⟩⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm
