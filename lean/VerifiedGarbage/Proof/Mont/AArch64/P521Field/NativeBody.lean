module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeLayout
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeEntry
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeExit
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.Block

/-! Instruction partitions and vector frames of the ordinary multiplier. -/

-- separate module: exact body assembly and SIMD save preservation
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (insCode)

def nativeStores : List Instr := storesR .x0 bRegs 0

theorem nativeStores_eq : (mulFnBlocks.flatten.drop 410).take 9=nativeStores := by decide

theorem nativeMul_body : mulFnBlocks.flatten=
    insCode nativeSaved 0++(nativePointers++(nativeArithmetic++(nativeStores++nativeExit))) := by
  have hlen : mulFnBlocks.flatten.length=430 := by
    rw [List.length_flatten]
    decide
  have h0 := List.take_add (l:=mulFnBlocks.flatten) (i:=16) (j:=414)
  have h1 := List.take_add (l:=mulFnBlocks.flatten.drop 16) (i:=394) (j:=20)
  have h2 := List.take_add (l:=mulFnBlocks.flatten.drop 410) (i:=9) (j:=11)
  simp only [List.drop_drop,Nat.reduceAdd] at h0 h1 h2
  rw [←hlen,List.take_length] at h0
  rw [h0,h1,h2,nativeEntry_eq,nativeArithmetic_eq,nativeStores_eq,nativeExit_eq,List.append_assoc]

theorem all_chunks {α : Type} {xs : List α} {P : α → Prop} (n : Nat)
    (ht : ∀i∈xs.take n,P i) (hd : ∀i∈xs.drop n,P i) : ∀i∈xs,P i := by
  intro i hi
  rw [←List.take_append_drop n xs,List.mem_append] at hi
  exact hi.elim (ht i) (hd i)

theorem arithmetic_vectors {s : State} {pa pb pt : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) (ht : PtrW s .x27 pt 64)
    (stable : StableInput s pa pt)
    (ha' : wordsVal s.mem pa 0 9<VG.Proof.Mont.AArch64.P521Square.fieldPrime)
    (hb' : wordsVal s.mem pb 0 9<VG.Proof.Mont.AArch64.P521Square.fieldPrime) :
    WP isa (.block nativeArithmetic) s fun t =>
      (regsVal t bRegs<VG.Proof.Mont.AArch64.P521Square.fieldPrime ∧
      regsVal t bRegs=wordsVal s.mem pa 0 9*wordsVal s.mem pb 0 9%VG.Proof.Mont.AArch64.P521Square.fieldPrime ∧
      Outside pt 0 64 s.mem t.mem ∧ KeepRegs arithmeticClob s t) ∧ t.v=s.v := by
  apply VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec ?_
    (native_arithmetic_ok ha hb ht stable ha' hb')
  have hc : nativeArithmetic.all (fun i => (vdstOf i).isNone)=true := by
    simp only [nativeArithmetic,List.all_append,Bool.and_eq_true]
    constructor
    · have hsplit := List.take_append_drop 128 nativeProductCode
      rw [←hsplit,List.all_append,Bool.and_eq_true]
      constructor
      · decide
      · have hsplit' := List.take_append_drop 128 (nativeProductCode.drop 128)
        rw [←hsplit',List.all_append,Bool.and_eq_true]
        constructor <;> decide
    · constructor <;> decide
  intro i hi
  have h := List.all_eq_true.mp hc i hi
  exact Option.isNone_iff_eq_none.mp h

theorem stores_vectors {s : State} {p : Addr} (hp : PtrW s .x0 p 72) :
    WP isa (.block nativeStores) s fun t =>
      (wordsVal t.mem p 0 9=regsVal s bRegs ∧ KeepRegs [] s t ∧ Outside p 0 72 s.mem t.mem) ∧ t.v=s.v := by
  exact VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (storesR_ok bRegs hp (o:=0) (by decide) (by decide) (by decide))

end VG.Proof.Mont.AArch64.P521Field
