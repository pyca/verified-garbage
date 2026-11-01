module

import VerifiedGarbage.Proof.Bignum.Arm.ExportBECT
public import VerifiedGarbage.Proof.Bignum.Arm.MaskOutputCT
public import VerifiedGarbage.Impl.Bignum.Arm.ExportMasked
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
import VerifiedGarbage.Proof.Bignum.Arm.ExportBE
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Serialization and rejection masking reveal no result or acceptance bits -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

structure ExportMaskedInput (base dst : BitVec 32) (len w o k : Nat) (s : State) : Prop where
  ready : SmallFnReady base len w o s
  positive : 0 < k
  fits : k ≤ 8 * w
  outputFit : dst.toNat + k ≤ 2 ^ 32
  write : InRegions s.wr (State.addr dst) k
  separate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, k⟩
  output : s.gpr .r4 = dst
  count : s.gpr .r6 = BitVec.ofNat 32 k
  stackFit : s.sp.toNat + 52 ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4

theorem exportMasked_ready (s : State) {base dst : BitVec 32} {len w o k : Nat}
    (h : ExportMaskedInput base dst len w o k s) (ho : o < 8) :
    WP isa exportBE s (MaskOutputInput dst k) := by
  refine WP.mono (exportBE_truncated_ok s h.ready.workspace h.ready.layout h.ready.width ho h.positive h.fits
    h.outputFit h.write h.separate h.ready.ptr h.ready.index h.output h.count) ?_
  rintro t ⟨_, _, _, output, rest⟩
  exact ⟨output, (rest.gpr .r6 (by simp)).trans h.count, by rw [rest.sp]; exact h.stackFit,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.read⟩

theorem exportMasked_ct {base dst : BitVec 32} {len w o k : Nat} (ho : o < 8) (hk : 0 < k) :
    RelCT isa (fun s t => ExportMaskedInput base dst len w o k s ∧
      ExportMaskedInput base dst len w o k t ∧ s.sp = t.sp) exportMasked (fun _ _ => True) := by
  let P := fun s t => ExportMaskedInput base dst len w o k s ∧
    ExportMaskedInput base dst len w o k t ∧ s.sp = t.sp
  have exportCT := (exportBE_ct ho hk).mono (P' := P)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.1.output, h.2.1.output, h.1.count, h.2.1.count⟩) (fun _ _ h => h)
  have ready := (relCT_keep_sp exportCT (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨exportMasked_ready s h.1 ho, exportMasked_ready t h.2.1 ho⟩)
  exact ready.seq (maskOutput_ct.mono (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

end VG.Proof.Bignum.Arm
