module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Linear
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationFin
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.OuterBlocks
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowSelectWords
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native
open VG.Impl.Weierstrass.AArch64 (signMaskW)

 def windowSignY : List Instr := signMaskW 5 3304++windowSelectWords 1576 2224 1576 9

 theorem window_sign_y_source : (outerBlock142.drop 688).take 59=windowSignY := by
  have h := drop_flatten_prefix outerBlock142Chunks 21 672 16
    (by rw [List.length_flatten]; lit_decide)
  rw [outerBlock142,h]
  decide

 theorem window_sign_y_ok {s : State} {base : Addr} {size k j : Nat}
    (hs : Scr s base size) (room : 3829≤size) (hj : j<105)
    (counter : s.gpr .x19=BitVec.ofNat 64 j)
    (bits : ∀t<525,s.mem (off base (3304+t))=if k.testBit t then 1 else 0) :
    WP isa (.block windowSignY) s fun t =>
      wordsVal t.mem base 1576 9=
        (if combWin 5 k j<16 then wordsVal s.mem base 2224 9 else wordsVal s.mem base 1576 9) ∧
      KeepRegs [.x1,.x2,.x3,.x16] s t ∧ Outside base 1576 72 s.mem t.mem := by
  rw [windowSignY,WP.block_append_iff]
  refine WP.mono (signMaskW_ok hs 5 3304 (k:=k) (j:=j) (N:=525)
    (by decide) (by decide) (by omega_arith) (by omega_arith) (by decide) counter bits)
    fun u ⟨mask,ku⟩ => ?_
  have mu : u.gpr .x3=if decide (combWin 5 k j<16) then BitVec.allOnes 64 else 0 := mask
  refine WP.mono (window_select_words (hs.of_keeps ku (by decide)) (a:=1576) (b:=2224) (o:=1576) (n:=9)
    (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide)
    (by left; rfl) (by right; right; decide) (decide (combWin 5 k j<16)) mu 9 (by decide))
    fun t ⟨words,kt,frame⟩ => ?_
  refine ⟨?_,(Keeps.regs (ku.mono (by simp))).trans (kt.mono (by simp)),?_⟩
  · by_cases h : combWin 5 k j<16
    · simp only [h,ite_true]
      apply wordsVal_of_words₂
      intro i hi
      have e := words i hi
      simpa only [h,decide_true,ite_true,ku.mem] using e
    · simp only [h,ite_false]
      apply wordsVal_of_words₂
      intro i hi
      have e := words i hi
      simpa only [h,decide_false,Bool.false_eq_true,ite_false,ku.mem] using e
  · rwa [ku.mem] at frame

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native

 def windowNegateY : List Instr := VG.Impl.Mont.AArch64.P521Linear.sub 2224 280 1576

 theorem window_negate_y_source : (outerBlock142.drop 640).take 48=windowNegateY := by
  have h := drop_flatten_prefix outerBlock142Chunks 20 640 0
    (by rw [List.length_flatten]; lit_decide)
  rw [Nat.add_zero] at h
  rw [outerBlock142,h]
  decide

 theorem window_negate_y_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (room : 2296≤size)
    (zero : wordsVal s.mem base 280 9=0) (bound : wordsVal s.mem base 1576 9<fieldPrime) :
    WP isa (.block windowNegateY) s fun t =>
      wordsVal t.mem base 2224 9=(fieldPrime-wordsVal s.mem base 1576 9)%fieldPrime ∧
      wordsVal t.mem base 2224 9<fieldPrime ∧ KeepRegs (clob 9) s t ∧ Outside base 2224 72 s.mem t.mem := by
  have hp : 0<fieldPrime := by decide +kernel
  have hm : fieldPrime+1=512*(2^64)^8 := by decide +kernel
  refine WP.mono (VG.Proof.Mont.AArch64.P521Linear.sub_ok hs (o:=2224) (a:=280) (b:=1576)
    (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide) hm
    (by rw [zero]; exact hp) bound) fun t ⟨e,b,k,f⟩ => ?_
  rw [zero,Nat.zero_add] at e
  exact ⟨e,b,k,f⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native

 def windowSignedY : List Instr := windowNegateY++windowSignY

 theorem window_signed_y_source : (outerBlock142.drop 640).take 107=windowSignedY := by
  rw [windowSignedY,←window_negate_y_source,←window_sign_y_source]
  have h : (outerBlock142.drop 640).drop 48=outerBlock142.drop 688 := by rw [List.drop_drop]
  rw [←h,←List.take_add]

 theorem window_signed_y_novec : ∀i∈windowSignedY,vdstOf i=none := by
  have h : windowSignedY.all (fun i => vdstOf i==none)=true := by lit_decide
  simpa only [List.all_eq_true,beq_iff_eq] using h

 theorem window_signed_y_core {s : State} {base : Addr} {size k j : Nat}
    (hs : Scr s base size) (room : 3829≤size) (hj : j<105)
    (zero : wordsVal s.mem base 280 9=0) (bound : wordsVal s.mem base 1576 9<fieldPrime)
    (counter : s.gpr .x19=BitVec.ofNat 64 j)
    (bits : ∀t<525,s.mem (off base (3304+t))=if k.testBit t then 1 else 0) :
    WP isa (.block windowSignedY) s fun t =>
      wordsVal t.mem base 1576 9=(if combWin 5 k j<16 then
        (fieldPrime-wordsVal s.mem base 1576 9)%fieldPrime else wordsVal s.mem base 1576 9) ∧
      wordsVal t.mem base 1576 9<fieldPrime ∧ KeepRegs (clob 9) s t ∧
      (∀x,(ofs base x<1576 ∨ 1648≤ofs base x) →
        (ofs base x<2224 ∨ 2296≤ofs base x) → t.mem x=s.mem x) := by
  rw [windowSignedY,WP.block_append_iff]
  refine WP.mono (window_negate_y_ok hs (by omega_arith) zero bound) fun u ⟨eNeg,bNeg,ku,fu⟩ => ?_
  have hu := hs.of_keepRegs ku (by decide)
  have cu : u.gpr .x19=BitVec.ofNat 64 j := (ku.gpr _ (by decide)).trans counter
  have bu : ∀t<525,u.mem (off base (3304+t))=if k.testBit t then 1 else 0 := by
    intro t ht
    have e : ofs base (off base (3304+t))=3304+t := by
      have hf := hs.nowrap
      simpa only [BitVec.add_zero,Nat.add_zero] using
        (ofs_off base (d:=3304+t) (i:=0) (by omega_arith))
    rw [fu _ (by rw [e]; omega_arith),bits t ht]
  refine WP.mono (window_sign_y_ok hu room hj cu bu) fun t ⟨ey,kt,ft⟩ => ?_
  have oldY : wordsVal u.mem base 1576 9=wordsVal s.mem base 1576 9 :=
    fu.wordsVal (by decide) (by have hf:=hs.nowrap; omega_arith)
  rw [eNeg,oldY] at ey
  refine ⟨ey,?_,ku.trans (kt.mono (by decide)),fun x hx hn => (ft x hx).trans (fu x hn)⟩
  by_cases h : combWin 5 k j<16
  · rw [ey]; simp only [h,ite_true]; rw [eNeg] at bNeg; exact bNeg
  · rw [ey]; simpa only [h,ite_false] using bound

 theorem window_signed_y_ok {s : State} {base : Addr} {size k j : Nat}
    (hs : Scr s base size) (room : 3829≤size) (hj : j<105)
    (zero : wordsVal s.mem base 280 9=0) (bound : wordsVal s.mem base 1576 9<fieldPrime)
    (counter : s.gpr .x19=BitVec.ofNat 64 j)
    (bits : ∀t<525,s.mem (off base (3304+t))=if k.testBit t then 1 else 0) :
    WP isa (.block windowSignedY) s fun t =>
      wordsVal t.mem base 1576 9=(if combWin 5 k j<16 then
        (fieldPrime-wordsVal s.mem base 1576 9)%fieldPrime else wordsVal s.mem base 1576 9) ∧
      wordsVal t.mem base 1576 9<fieldPrime ∧ KeepRegs (clob 9) s t ∧
      (∀x,(ofs base x<1576 ∨ 1648≤ofs base x) →
        (ofs base x<2224 ∨ 2296≤ofs base x) → t.mem x=s.mem x) ∧ t.v=s.v := by
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec window_signed_y_novec
    (window_signed_y_core hs room hj zero bound counter bits)) fun t ⟨⟨e,b,k,f⟩,v⟩ => ?_
  exact ⟨e,b,k,f,v⟩

end VG.Proof.Weierstrass.AArch64.P521Native
