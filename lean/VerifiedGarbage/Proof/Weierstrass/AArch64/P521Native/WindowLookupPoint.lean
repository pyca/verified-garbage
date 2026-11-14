module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLookupCode
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleOutput
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.Lookup
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowSignedY
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldStep
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64

 def WindowSignedFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<1576 ∨ 1648≤ofs base x) → (ofs base x<2224 ∨ 2296≤ofs base x) → m' x=m x

 theorem WindowSignedFrame.word {base : Addr} {m m' : Mem} (frame : WindowSignedFrame base m m') {d : Nat}
    (ha : d+8≤1576 ∨ 1648≤d) (hb : d+8≤2224 ∨ 2296≤d) (hd : d+8≤2^64) :
    word m' base d=word m base d := by
  exact (Mem.readW_congr fun i hi =>
    (frame _ (by rw [ofs_off base (by omega_arith)]; omega_arith)
      (by rw [ofs_off base (by omega_arith)]; omega_arith)).symm).symm

 theorem WindowSignedFrame.wordsVal {base : Addr} {m m' : Mem} (frame : WindowSignedFrame base m m') {d k : Nat}
    (ha : d+8*k≤1576 ∨ 1648≤d) (hb : d+8*k≤2224 ∨ 2296≤d) (hd : d+8*k≤2^64) :
    wordsVal m' base d k=wordsVal m base d k := by
  apply wordsVal_of_words₂
  intro j hj
  exact WindowSignedFrame.word frame (by omega_arith) (by omega_arith) (by omega_arith)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem lookup_values_ok {s : State} {base table : Addr} {size d : Nat}
    (hs : Scr s base size) (hsize : 1720≤size) (ht : LookupTableReadable s table)
    (hd : d≤16) (digit : s.gpr .x2=BitVec.ofNat 64 d) :
    WP isa lookupProgram s fun t =>
      wordsVal t.mem base 1504 9=(if d=0 then 0 else wordsVal s.mem table (lookupEntryOffset d) 9) ∧
      wordsVal t.mem base 1576 9=(if d=0 then 1 else wordsVal s.mem table (lookupEntryOffset d+72) 9) ∧
      wordsVal t.mem base 1648 9=(if d=0 then 0 else 1) ∧
      KeepRegs lookupClob s t ∧ Outside base 1504 216 s.mem t.mem := by
  refine WP.mono (lookup_ok hs hsize ht hd digit) fun t ⟨words,z,k,frame⟩ => ?_
  refine ⟨?_,?_,z,k,frame⟩
  · by_cases h : d=0
    · simp only [h,ite_true]
      apply (wordsVal_eq_zero_iff t.mem base 1504 9).mpr
      intro j hj
      have e := words j (by omega_arith)
      have jne : j≠9 := by omega_arith
      simpa only [h,jne,ite_true,ite_false] using e
    · simp only [h,ite_false]
      apply wordsVal_of_words₂
      intro j hj
      have e := words j (by omega_arith)
      simpa only [h,ite_false] using e
  · by_cases h : d=0
    · simp only [h,ite_true]
      have head := words 9 (by decide)
      simp only [h,ite_true,Nat.reduceMul,Nat.reduceAdd] at head
      have tail : wordsVal t.mem base 1584 8=0 := by
        apply (wordsVal_eq_zero_iff t.mem base 1584 8).mpr
        intro j hj
        have e := words (j+10) (by omega_arith)
        have jne : j+10≠9 := by omega_arith
        simp only [h,jne,ite_true,ite_false] at e
        rwa [show 1504+8*(j+10)=1584+8*j by omega_arith] at e
      rw [wordsVal,head,tail]
      rfl
    · simp only [h,ite_false]
      apply wordsVal_of_words₂
      intro j hj
      have e := words (j+9) (by omega_arith)
      simp only [h,ite_false] at e
      rwa [show 1504+8*(j+9)=1576+8*j by omega_arith,
        show lookupEntryOffset d+8*(j+9)=lookupEntryOffset d+72+8*j by omega_arith] at e

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

 def windowX (m : Mem) (table : Addr) (d : Nat) := if d=0 then 0 else wordsVal m table (lookupEntryOffset d) 9
 def windowY (m : Mem) (table : Addr) (d : Nat) := if d=0 then 1 else wordsVal m table (lookupEntryOffset d+72) 9

 theorem window_lookup_ok {s : State} {base table : Addr} {size k j : Nat}
    (hs : Scr s base size) (room : 3829≤size) (hj : j<105)
    (ht : LookupTableReadable s table) (zero : wordsVal s.mem base 280 9=0)
    (canonical : ∀d,1≤d → d≤16 → wordsVal s.mem table (lookupEntryOffset d) 9<fieldPrime ∧
      wordsVal s.mem table (lookupEntryOffset d+72) 9<fieldPrime)
    (counter : s.gpr .x19=BitVec.ofNat 64 j)
    (bits : ∀t<525,s.mem (off base (3304+t))=if k.testBit t then 1 else 0) :
    WP isa (.block windowLookupCode) s fun t =>
      wordsVal t.mem base 1504 9=windowX s.mem table (magH 16 (combWin 5 k j)) ∧
      wordsVal t.mem base 1576 9=(if combWin 5 k j<16 then
        (fieldPrime-windowY s.mem table (magH 16 (combWin 5 k j)))%fieldPrime
        else windowY s.mem table (magH 16 (combWin 5 k j))) ∧
      wordsVal t.mem base 1648 9=(if magH 16 (combWin 5 k j)=0 then 0 else 1) ∧
      canonicalPoint t.mem base 1504 ∧ KeepRegs (clob 9) s t ∧
      (∀x,(ofs base x<1504 ∨ 1720≤ofs base x) →
        (ofs base x<2224 ∨ 2296≤ofs base x) → t.mem x=s.mem x) := by
  rw [windowLookupCode,List.append_assoc,WP.block_append_iff]
  refine WP.mono (window_digit_ok hs room hj counter bits) fun u ⟨digit,ku⟩ => ?_
  rw [WP.block_append_iff]
  let d := magH 16 (combWin 5 k j)
  have hd : d≤16 := magH_le (combWin_lt 5 k j)
  have hu := hs.of_keeps ku (by decide)
  have htu : LookupTableReadable u table :=
    ⟨(ku.gpr _ (by decide)).trans ht.reg,by rw [ku.rd,ku.wr]; exact ht.read⟩
  refine WP.mono (lookup_values_ok hu (by omega_arith) htu hd digit) fun v ⟨ex,ey,ez,kv,fv⟩ => ?_
  rw [ku.mem] at ex ey
  have hv := hu.of_keepRegs kv (by decide)
  have zeroV : wordsVal v.mem base 280 9=0 := by
    rw [fv.wordsVal (by decide) (by have h:=hs.nowrap; omega_arith),ku.mem,zero]
  have hp1 : 1<fieldPrime := by decide +kernel
  have boundV : wordsVal v.mem base 1576 9<fieldPrime := by
    rw [ey]
    by_cases h : d=0
    · simpa only [h,ite_true] using hp1
    · simpa only [h,ite_false] using (canonical d (by omega_arith) hd).2
  have cv : v.gpr .x19=BitVec.ofNat 64 j := by
    rw [kv.gpr _ (by decide),ku.gpr _ (by decide),counter]
  have bv : ∀t<525,v.mem (off base (3304+t))=if k.testBit t then 1 else 0 := by
    intro t ht
    have e : ofs base (off base (3304+t))=3304+t := by
      have hf:=hs.nowrap
      simpa only [BitVec.add_zero,Nat.add_zero] using (ofs_off base (d:=3304+t) (i:=0) (by omega_arith))
    rw [fv _ (by rw [e]; omega_arith),ku.mem,bits t ht]
  refine WP.mono (window_signed_y_ok hv room hj zeroV boundV cv bv) fun t ⟨ty,byy,kt,ft,_⟩ => ?_
  have tx : wordsVal t.mem base 1504 9=windowX s.mem table d := by
    rw [WindowSignedFrame.wordsVal ft (by decide) (by decide) (by have h:=hs.nowrap; omega_arith),ex]
    rfl
  have tz : wordsVal t.mem base 1648 9=if d=0 then 0 else 1 := by
    rw [WindowSignedFrame.wordsVal ft (by decide) (by decide) (by have h:=hs.nowrap; omega_arith),ez]
  have ty' : wordsVal t.mem base 1576 9=if combWin 5 k j<16 then
      (fieldPrime-windowY s.mem table d)%fieldPrime else windowY s.mem table d := by
    simpa only [ey,windowY] using ty
  refine ⟨tx,ty',tz,?_,(VG.Proof.Mont.AArch64.Keeps.regs (ku.mono (by decide))).trans ((kv.mono (by decide)).trans kt),?_⟩
  · refine ⟨?_,byy,?_⟩
    · change wordsVal t.mem base 1504 9<fieldPrime
      rw [tx,windowX]
      by_cases h : d=0
      · simpa only [h,ite_true] using Nat.lt_trans (by decide : 0<1) hp1
      · simpa only [h,ite_false] using (canonical d (by omega_arith) hd).1
    · change wordsVal t.mem base 1648 9<fieldPrime
      rw [tz]; by_cases h : d=0 <;> simp only [h,ite_true,ite_false] <;> omega_arith
  · intro x hx hn
    exact (ft x (by omega_arith) hn).trans (by rw [fv x hx,ku.mem])

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64

 def WindowLookupFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<1504 ∨ 1720≤ofs base x) → (ofs base x<2224 ∨ 2296≤ofs base x) → m' x=m x

 theorem WindowLookupFrame.word {base : Addr} {m m' : Mem} (frame : WindowLookupFrame base m m') {d : Nat}
    (ha : d+8≤1504 ∨ 1720≤d) (hb : d+8≤2224 ∨ 2296≤d) (hd : d+8≤2^64) :
    word m' base d=word m base d := by
  exact (Mem.readW_congr fun i hi =>
    (frame _ (by rw [ofs_off base (by omega_arith)]; omega_arith)
      (by rw [ofs_off base (by omega_arith)]; omega_arith)).symm).symm

 theorem WindowLookupFrame.wordsVal {base : Addr} {m m' : Mem} (frame : WindowLookupFrame base m m') {d k : Nat}
    (ha : d+8*k≤1504 ∨ 1720≤d) (hb : d+8*k≤2224 ∨ 2296≤d) (hd : d+8*k≤2^64) :
    wordsVal m' base d k=wordsVal m base d k := by
  apply wordsVal_of_words₂
  intro j hj
  exact WindowLookupFrame.word frame (by omega_arith) (by omega_arith) (by omega_arith)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

 def WindowTableCanonical (m : Mem) (table : Addr) : Prop :=
  ∀d,1≤d → d≤16 → wordsVal m table (lookupEntryOffset d) 9<fieldPrime ∧
    wordsVal m table (lookupEntryOffset d+72) 9<fieldPrime

 def windowAffine (m : Mem) (table : Addr) (k j : Nat) : Fin fieldPrime×Fin fieldPrime×Fin fieldPrime :=
  let d := magH 16 (combWin 5 k j)
  (Fin.ofNat fieldPrime (windowX m table d),
   Fin.ofNat fieldPrime (if combWin 5 k j<16 then (fieldPrime-windowY m table d)%fieldPrime else windowY m table d),
   Fin.ofNat fieldPrime (if d=0 then 0 else 1))

 theorem window_lookup_safe_vectors : ∀i∈windowLookupCode,vdstOf i≠some .v29 ∧ vdstOf i≠some .v31 := by
  have h : windowLookupCode.all (fun i => (vdstOf i != some .v29) && (vdstOf i != some .v31))=true := by lit_decide
  simpa only [List.all_eq_true,Bool.and_eq_true,bne_iff_ne] using h

 theorem window_lookup_point_ok {s : State} {base table : Addr} {size k j : Nat}
    (hs : Scr s base size) (room : 3829≤size) (hj : j<105)
    (ht : LookupTableReadable s table) (zero : wordsVal s.mem base 280 9=0)
    (canonical : WindowTableCanonical s.mem table) (counter : s.gpr .x19=BitVec.ofNat 64 j)
    (bits : ∀t<525,s.mem (off base (3304+t))=if k.testBit t then 1 else 0) :
    WP isa (.block windowLookupCode) s fun t =>
      canonicalPoint t.mem base 1504 ∧ ordinaryPoint t.mem base 1504=windowAffine s.mem table k j ∧
      Scr t base size ∧ FieldPublic s t ∧ KeepRegs (clob 9) s t ∧
      WindowLookupFrame base s.mem t.mem ∧ t.v .v29=s.v .v29 := by
  obtain ⟨trace,t,exec,ex,ey,ez,b,k,frame⟩ := window_lookup_ok hs room hj ht zero canonical counter bits
  have v29 : t.v .v29=s.v .v29 := Exec.vec (c:=.block windowLookupCode) (fun i hi => (window_lookup_safe_vectors i hi).1) exec
  have v31 : t.v .v31=s.v .v31 := Exec.vec (c:=.block windowLookupCode) (fun i hi => (window_lookup_safe_vectors i hi).2) exec
  refine ⟨trace,t,exec,b,?_,hs.of_keepRegs k (by decide),?_,k,frame,v29⟩
  · change (Fin.ofNat _ (wordsVal t.mem base 1504 9),Fin.ofNat _ (wordsVal t.mem base 1576 9),
      Fin.ofNat _ (wordsVal t.mem base 1648 9))=_
    rw [ex,ey,ez]
    rfl
  · exact ⟨fun r hr => k.gpr r ((by decide : ∀r∈fieldPublicRegs,r∉clob 9) r hr),k.sp,k.rd,k.wr,v31⟩

end VG.Proof.Weierstrass.AArch64.P521Native
