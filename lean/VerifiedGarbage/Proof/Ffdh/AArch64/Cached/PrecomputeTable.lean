module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeInitial
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeBasisLoop
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeControls
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete verified construction of the canonical 32-entry comb table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem precomputeTable_ok (M : Mont) {s : State} {p : Parameters} {dom : Addr} {bs : List Byte}
 (field : FieldInitial p s) (space : ContextSpace p s)
 (generator : GeneratorSource p (dom+BitVec.ofNat 64 p.k) bs s) (words : p.w=(p.k+7)/8)
 (positive : 0<p.k) (size : p.k<2^31) (reduced : p.G<p.P) (bits : 0<p.N ∧ p.N≤8192)
 (context : word s.mem p.B (8*sCtx)=p.ctx) (domain : word s.mem p.B (8*sDom)=dom)
 (length : word s.mem p.B (8*sLen)=BitVec.ofNat 64 p.k)
 (rows : word s.mem p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N)) :
 WP isa (Precompute.table M.mm) s fun t =>
 BasisState p 5 t ∧ BuildFrame p s.mem t.mem ∧ Keep mmRegs s t := by
 unfold Precompute.table
 rw [WP.seq_iff]
 refine WP.mono (precomputeInitial_ok M field space generator words positive size reduced context domain length rows) ?_
 rintro a ⟨basisA,spaceA,ctxA,rowsA,tableA,frameA,restA⟩
 rw [WP.seq_iff]
 refine WP.mono (setControlNat_ok basisA.good p.room (by decide : 16≤sD) (by decide : sD<32) (by decide : 2<2^16)) ?_
 rintro b ⟨goodB,indexB,frameB,restB⟩
 have inB : InScr p.B p.Z a.mem b.mem :=
  InScr.of_outside frameB (by have := hdr_lt_slot p.w 8 (show sD<32 by decide);have := p.room;omega)
 have basisB := basisA.after_header goodB frameB (by decide : sD<32)
 have stateB : BasisState p 1 b :=
  ⟨⟨by decide,by decide⟩,bits,(by simpa only [Nat.sub_self,Nat.zero_mul,Nat.pow_zero] using basisB),spaceA.after restB,
   (header_other frameB (by decide) (by decide) (by decide)).trans ctxA,indexB,
   (header_other frameB (by decide) (by decide) (by decide)).trans rowsA,
   tableA.after_inscr spaceA (by decide) inB⟩
 refine WP.mono (precomputeBasisLoop_ok M stateB) ?_
 rintro t ⟨state,frame,rest⟩
 exact ⟨state,(frameA.trans (BuildFrame.of_inscr inB)).trans frame,
  ((restA.trans restB).trans rest).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached
