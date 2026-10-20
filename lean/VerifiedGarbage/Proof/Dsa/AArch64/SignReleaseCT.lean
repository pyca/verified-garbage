module

public import VerifiedGarbage.Proof.Dsa.AArch64.SignRelease
public import VerifiedGarbage.Proof.Dsa.AArch64.FailureCT
public import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarHead
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarCT
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.SignRelease
meta import VerifiedGarbage.Proof.Dsa.AArch64.FailureCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarHead
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant time of masked signature release and register restoration -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ReleasePublic extends FailurePublic where
  positive : 0 < width
  bound : width ≤ 32

structure ReleasePre (p : ReleasePublic) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  x0 : s.gpr .x0 = p.base
  out : word s.mem p.base Field.out.offset = p.output
  width : word s.mem p.base Field.qLen.offset = BitVec.ofNat 64 p.width
  mask : ∃ valid : Bool, word s.mem p.base Field.mask.offset = mask valid
  writable : ∀ i < 2 * p.width, InRegions s.wr (p.output + BitVec.ofNat 64 i) 1
  separate : ∀ i < 2 * p.width, usedBytes ≤ ofs p.base (p.output + BitVec.ofNat 64 i)

theorem releaseScalar_ct (offset : Nat) (second : Bool) (ho : offset < 2 ^ 16)
    (hend : offset + 32 ≤ usedBytes)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (scalarHead offset second)) hc).isSome = true) :
    RelCT isa (Two ReleasePre) (SignVerify.writeScalar offset second) (Two ReleasePre) := by
  refine two_post (two_map ReleasePublic.toFailurePublic
    (fun _ _ h => ⟨usedBytes, h.scratch, by decide, h.x0, h.out, h.width⟩)
    (writeScalar_ct offset second ho hT)) ?_
  intro p s h
  obtain ⟨valid, hm⟩ := h.mask
  have hw : ∀ i < p.width, InRegions s.wr
      ((if second then p.output + BitVec.ofNat 64 p.width else p.output) + BitVec.ofNat 64 i) 1 := by
    intro i hi
    cases second
    · exact h.writable i (by omega)
    · rw [ite_eq_left rfl, Offset.add_add]
      exact h.writable _ (by omega)
  have hsep : ∀ i < p.width, usedBytes ≤ ofs p.base
      ((if second then p.output + BitVec.ofNat 64 p.width else p.output) + BitVec.ofNat 64 i) := by
    intro i hi
    cases second
    · exact h.separate i (by omega)
    · rw [ite_eq_left rfl, Offset.add_add]
      exact h.separate _ (by omega)
  refine WP.mono (writeScalar_ok h.scratch h.x0 (by decide) ho h.out h.width hm second p.positive
    (by have := p.bound; omega) (by have := p.bound; omega) hw hsep) fun t ⟨_, hf, hk⟩ => ?_
  have hword (f : Field) : word t.mem p.base f.offset = word s.mem p.base f.offset := by
    apply Mem.readW_congr
    intro i hi
    apply hf _
    intro j hj
    exact scr_ne_out hsep (by have hb := (VG.Proof.Dsa.field_bounds f).2; change f.offset + 8 ≤ 3456 at hb; change f.offset + i < 15712; omega)
      (by have := h.scratch.nowrap; omega) j hj
  exact ⟨h.scratch.congr hk.wr, (hk.gpr .x0 (by decide)).trans h.x0,
    (hword .out).trans h.out, (hword .qLen).trans h.width, ⟨valid, (hword .mask).trans hm⟩,
    fun i hi => by rw [hk.wr]; exact h.writable i hi, h.separate⟩

theorem signRelease_ct : RelCT isa (Two ReleasePre) signRelease (fun _ _ => True) := by
  unfold signRelease seqs
  refine RelCT.seq (releaseScalar_ct r false (by decide) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (releaseScalar_ct s true (by decide) (by decide) (by taint_decide)) ?_
  exact two_map (fun p : ReleasePublic => p.base) (fun _ _ h => h.x0) result_ct

end VG.Proof.Dsa.AArch64
