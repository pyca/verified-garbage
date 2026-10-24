module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BasisState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BasisStore
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SquareFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeProducts
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeControls
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.Ring

/-! Build one tooth and all new subsets containing it. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem regroup {a b c : Prog isa} {s : State} {Q : State → Prop} :
 WP isa (.seq a (.seq b c)) s Q ↔ WP isa (.seq (.seq a b) c) s Q := ⟨WP.assoc',WP.assoc⟩

theorem precomputeBasis_ok (M : Mont) {s : State} {p : Parameters} {b : Nat}
 (h : BasisState p b s) (more : b<5) :
 WP isa (Precompute.basis M.mm) s fun t =>
 BasisState p (b+1) t ∧ t.gpr .x3=BitVec.ofNat 64 (2^(b+1))-32#64 ∧
 BuildFrame p s.mem t.mem ∧ Keep mmRegs s t := by
 have toothBound : 2^b≤16 := Nat.pow_le_pow_right (by decide) (by omega : b≤4)
 have toothPositive : 0<2^b := Nat.two_pow_pos b
 have rowsPositive := VG.Proof.Rsa.FixedBaseComb.rows_pos h.bits.1
 have rowsBound := (VG.Proof.Rsa.FixedBaseComb.rows_small h.bits.2).1
 unfold Precompute.basis
 rw [WP.seq_iff]
 refine WP.mono (precomputeSquares_ok M h.basis h.rows rowsPositive (by omega)) ?_
 rintro a ⟨basisA,_,frameA,restA⟩
 have exponent : 2^((b-1)*Spec.Rsa.FixedBaseComb.rows p.N)*2^(Spec.Rsa.FixedBaseComb.rows p.N)=
   2^(b*Spec.Rsa.FixedBaseComb.rows p.N) := by
  rw [←Nat.pow_add]
  congr 1
  calc
   (b-1)*Spec.Rsa.FixedBaseComb.rows p.N+Spec.Rsa.FixedBaseComb.rows p.N=
    (b-1+1)*Spec.Rsa.FixedBaseComb.rows p.N := by ring
   _=b*Spec.Rsa.FixedBaseComb.rows p.N := by rw [Nat.sub_add_cancel h.tooth.1]
 rw [exponent] at basisA
 have spaceA := h.space.after restA
 have ctxA := (squareFrame_header frameA (by decide : sCtx<32) (by decide)).trans h.context
 have indexA := (squareFrame_header frameA (by decide : sD<32) (by decide)).trans h.index
 have rowsA := (squareFrame_header frameA (by decide : sRows<32) (by decide)).trans h.rows
 have inA := InScr.of_frm frameA (fun r hr => Nat.le_trans (basisSquareRanges_le p.w r hr) p.room)
 have tableA := h.table.after_inscr h.space (by omega) inA
 rw [regroup,WP.seq_iff]
 refine WP.mono (basisStore_ok basisA.good spaceA ctxA indexA (by omega)) ?_
 rintro c ⟨goodC,valueC,frameC,sameC,restC⟩
 have basisC := basisA.after_workspace goodC sameC
 have spaceC := spaceA.after restC
 have ctxC := (workspace_header basisA.good sameC (by decide : sCtx<32)).trans ctxA
 have indexC := (workspace_header basisA.good sameC (by decide : sD<32)).trans indexA
 have rowsC := (workspace_header basisA.good sameC (by decide : sRows<32)).trans rowsA
 have entryC : wv c.mem p.ctx (entryOffset p.w (2^b)) p.w=entryValue p (2^b) := by
  unfold entryValue
  rw [valueC,basisA.value,VG.Proof.Rsa.FixedBaseComb.exponent_tooth p.N b more]
 have tableC := tableA.extend (by omega : 2^b<32) frameC entryC
 rw [WP.seq_iff]
 refine WP.mono (setControlOne_ok goodC p.room (by decide : 16≤sJ) (by decide : sJ<32)) ?_
 rintro d ⟨goodD,oneD,frameD,restD⟩
 have inD : InScr p.B p.Z c.mem d.mem := InScr.of_outside frameD (by have := hdr_lt_slot p.w 8 (show sJ<32 by decide);have := p.room;omega)
 have tableD := tableC.after_inscr spaceC (by omega) inD
 have productD : ProductState p b 1 d :=
  ⟨more,⟨by omega,by omega⟩,basisC.after_header goodD frameD (by decide),spaceC.after restD,
   (header_other frameD (by decide) (by decide) (by decide)).trans ctxC,
   (header_other frameD (by decide) (by decide) (by decide)).trans indexC,oneD,tableD,
   (header_other frameD (by decide) (by decide) (by decide)).trans rowsC⟩
 rw [WP.seq_iff]
 refine WP.mono (precomputeProducts_ok M productD (by have := h.tooth;omega)) ?_
 rintro e ⟨stateE,frameE,restE⟩
 refine WP.mono (basisNext_ok stateE.basis.good p.room stateE.basisIndex) ?_
 rintro t ⟨goodT,indexT,testT,frameT,restT⟩
 have inT : InScr p.B p.Z e.mem t.mem := InScr.of_outside frameT (by have := hdr_lt_slot p.w 8 (show sD<32 by decide);have := p.room;omega)
 have tableT := stateE.table.after_inscr stateE.space stateE.limit inT
 have nextPower : 2*2^b=2^(b+1) := by rw [Nat.pow_succ];omega
 have nextCount : 2^b+2^b=2^(b+1) := by rw [Nat.pow_succ];omega
 have stateT : BasisState p (b+1) t := by
  refine ⟨⟨by omega,by omega⟩,h.bits,?_,stateE.space.after restT,
   (header_other frameT (by decide) (by decide) (by decide)).trans stateE.context,?_,
   (header_other frameT (by decide) (by decide) (by decide)).trans stateE.rows,?_⟩
  · simpa only [Nat.add_sub_cancel] using stateE.basis.after_header goodT frameT (by decide : sD<32)
  · simpa only [nextPower] using indexT
  · simpa only [nextCount] using tableT
 have frames : BuildFrame p s.mem t.mem :=
  ((((BuildFrame.of_inscr inA).trans (BuildFrame.of_entry (by omega : 2^b<32) frameC)).trans
    (BuildFrame.of_inscr inD)).trans frameE).trans (BuildFrame.of_inscr inT)
 refine ⟨stateT,?_,frames,((((restA.trans restC).trans restD).trans restE).trans restT).mono (by simp [mmRegs])⟩
 simpa only [nextPower] using testT

end VG.Proof.Ffdh.AArch64.Cached
