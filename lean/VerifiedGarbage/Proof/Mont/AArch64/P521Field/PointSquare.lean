module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointProductSchedule
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointReduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeProduct
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def pointFirstSquareArithmetic : List Instr := (doubleFnBlocks.flatten.drop 14).take 238

theorem pointFirstSquareArithmetic_eq : pointFirstSquareArithmetic=
    pointFirstSquareProduct++(pointFoldCode++pointCorrectCode) := by
  apply chunks_eq 128 <;> decide

theorem point_first_square_arith_ok {s : State} {p : Addr}
    (hp : Ptr s .x27 p 216) (ha : wordsVal s.mem p 144 9<fieldPrime) :
    WP isa (.block pointFirstSquareArithmetic) s fun t =>
      regsVal t pointFoldOutRegs<fieldPrime ∧
      regsVal t pointFoldOutRegs=(wordsVal s.mem p 144 9*wordsVal s.mem p 144 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ VG.Proof.Ed25519.AArch64.Keeps pointFullProductClob s t := by
  have fieldBound : fieldPrime≤2^521 := by
    dsimp only [fieldPrime]
    have hb := Nat.sub_le ((2:Nat)^521) 1
    exact hb
  have ha' : wordsVal s.mem p 144 9<2^521 := Nat.lt_of_lt_of_le ha fieldBound
  rw [pointFirstSquareArithmetic_eq,WP.block_append_iff]
  refine WP.mono (point_first_square_product_ok hp ha') fun u ⟨prod,hz,kp⟩ => ?_
  have hu : regsVal u pointProductRegs<fieldPrime*fieldPrime := by
    rw [prod]
    exact Nat.mul_lt_mul'' ha ha
  refine WP.mono (point_reduce_ok hz hu) fun t ⟨canon,val,z1,mask,kr⟩ => ?_
  exact ⟨canon,by rw [val,prod],z1,mask,kp.trans (kr.mono (by decide))⟩

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

def pointFirstSquareCode : List Instr := (doubleFnBlocks.flatten.drop 14).take 247
def pointFirstSquareStores : List Instr := storesR .x28 pointFoldOutRegs 0

theorem pointFirstSquareStores_eq : (doubleFnBlocks.flatten.drop 252).take 9=
    pointFirstSquareStores := by decide

theorem pointFirstSquareCode_eq : pointFirstSquareCode=
    pointFirstSquareArithmetic++pointFirstSquareStores := by
  apply chunks_eq 128 <;> decide

/-- All input reads precede stores, so no input/output separation is needed. -/
theorem point_first_square_ok {s : State} {p q : Addr}
    (hp : Ptr s .x27 p 216) (hq : PtrW s .x28 q 72)
    (ha : wordsVal s.mem p 144 9<fieldPrime) :
    WP isa (.block pointFirstSquareCode) s fun t =>
      wordsVal t.mem q 0 9<fieldPrime ∧
      wordsVal t.mem q 0 9=(wordsVal s.mem p 144 9*wordsVal s.mem p 144 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointFullProductClob s t ∧ Outside q 0 72 s.mem t.mem := by
  rw [pointFirstSquareCode_eq,WP.block_append_iff]
  refine WP.mono (point_first_square_arith_ok hp ha) fun u ⟨canon,val,z1,mask,ka⟩ => ?_
  have hqu := hq.of_keepRegs (Keeps.regs ka) (by decide)
  refine WP.mono (storesR_ok pointFoldOutRegs hqu (o:=0) (by decide) (by decide) (by decide))
    fun t ⟨stored,ks,frame⟩ => ?_
  change wordsVal t.mem q 0 9=regsVal u pointFoldOutRegs at stored
  exact ⟨by rw [stored]; exact canon,by rw [stored,val],
    (ks.gpr .x1 (by decide)).trans z1,(ks.gpr .x0 (by decide)).trans mask,(Keeps.regs ka).trans (ks.mono (by decide)),by rw [ka.mem] at frame; exact frame⟩

/-- Scalar point arithmetic also preserves the SIMD lanes carrying the
outer kernel's return address, workspace pointer, and table pointer. -/
theorem point_first_square_vectors {s : State} {p q : Addr}
    (hp : Ptr s .x27 p 216) (hq : PtrW s .x28 q 72)
    (ha : wordsVal s.mem p 144 9<fieldPrime) :
    WP isa (.block pointFirstSquareCode) s fun t =>
      (wordsVal t.mem q 0 9<fieldPrime ∧
      wordsVal t.mem q 0 9=(wordsVal s.mem p 144 9*wordsVal s.mem p 144 9)%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ KeepRegs pointFullProductClob s t ∧ Outside q 0 72 s.mem t.mem) ∧ t.v=s.v := by
  apply VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec ?_
    (point_first_square_ok hp hq ha)
  have hc : pointFirstSquareCode.all (fun i => (vdstOf i).isNone)=true := by
    have hsplit := List.take_append_drop 128 pointFirstSquareCode
    rw [←hsplit,List.all_append,Bool.and_eq_true]
    constructor <;> decide
  intro i hi
  exact Option.isNone_iff_eq_none.mp (List.all_eq_true.mp hc i hi)

end VG.Proof.Mont.AArch64.P521Field
