module

-- separate module: The consolidated batch-inversion recurrence, zero-safe machine composition, and memory-frame proof cost about 0.54 seconds; API/recode changes reuse this complete phase contract.

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizePrefixCode
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeBackCode
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizePrefixInv
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeInverse
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeBackInv
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvBatchStart
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeBackWork
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeMath
public import VerifiedGarbage.Spec.P521

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

theorem normalize_prefix_machine_ok {base table : Addr} {W : Nat} {s : State}
    {X Y Z : Nat → Fin fieldPrime} (layout : NormalizeLayout base table W)
    (inv : NormalizePrefixInv base table W 1 s X Y Z) :
    WP isa normalizePrefixMachine s fun t =>
      NormalizePrefixInv base table W 16 t X Y Z ∧ Outside base 0 W s.mem t.mem ∧
      t.gpr .x0=base ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      (∀r∈preserved,r≠.x20 → t.gpr r=s.gpr r) ∧
      t.gpr .x20=word s.mem base 3944 ∧ t.v .v31=s.v .v31 ∧
      Outside base 1216 6120 s.mem t.mem ∧ VG.Proof.Weierstrass.Unch base normalizePrefixWrites s.mem t.mem := by
  apply normalize_prefix_machine_wp.mpr
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (ldR_ok inv.workspace.ptr (d:=3944) (by have h:=layout.workspaceSize; omega_arith)
      (by decide) .x20)) fun u ⟨⟨value,ku,_⟩,vu⟩ => ?_
  have iu : NormalizePrefixInv base table W 1 u X Y Z := by
    refine ⟨inv.workspace.of_keeps ku (by decide),inv.tablePtr.of_keeps ku (by decide),?_,?_,?_⟩
    · constructor
      · intro i hi c hc; rw [ku.mem]; exact inv.tableValues.canonical i hi c hc
      · intro i hi; rw [ku.mem]; exact inv.tableValues.xValue i hi
      · intro i hi; rw [ku.mem]; exact inv.tableValues.yValue i hi
      · intro i hi; rw [ku.mem]; exact inv.tableValues.zValue i hi
    · intro i hi hn; rw [ku.mem]; exact inv.bounds i hi hn
    · intro i hi hn; rw [ku.mem]; exact inv.values i hi hn
  refine WP.mono (normalize_prefix_all_ok layout iu) fun t ⟨it,ot,zero,rd,wr,sp,gp,v31,low,unch⟩ => ?_
  refine ⟨it,?_,zero,rd.trans ku.rd,wr.trans ku.wr,sp.trans ku.sp,?_,?_,?_,?_,?_⟩
  · rw [ku.mem] at ot; exact ot
  · intro r hr h20
    exact (gp r hr).trans (ku.gpr r (by simpa only [List.mem_singleton] using h20))
  · rw [gp .x20 (by decide),value]
  · rw [v31,vu]
  · rw [ku.mem] at low; exact low
  · rw [ku.mem] at unch; exact unch

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

def normalizeInverseMachine : Prog isa := sequence [
  .block (representationMemoryCode representationToCode 1216),
  .block outerBlock044,callInvModP,.block outerBlock045,
  .block (representationMemoryCode representationFromCode 2152)]

private theorem inv_wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem normalize_inverse_machine_wp {s : State} {Q : State → Prop} :
    WP isa normalizeInverseMachine s Q ↔ WP isa normalizeInversePhase s Q := by
  have powSource : config.pPow=.seq (.block outerBlock044) (.seq callInvModP (.block outerBlock045)) := rfl
  simp only [normalizeInverseMachine,normalizeInversePhase,sequence,List.foldr_cons,List.foldr_nil,powSource]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_nil_iff] | (apply inv_wp_post_iff; intro t)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config)

structure NormalizeInverseState (base table : Addr) (s : State) (X Y Z : Nat → Fin fieldPrime) : Prop where
  workspace : Scr s base 8192
  tablePtr : Ptr s .x26 table 3456
  tableValues : NormalizeTable table s X Y Z
  prefixBounds : ∀i,1≤i → i<16 → wordsVal s.mem base (normalizePrefixSlot i) 9<fieldPrime
  prefixValues : ∀i,1≤i → i<16 →
    Fin.ofNat fieldPrime (wordsVal s.mem base (normalizePrefixSlot i) 9)=normalizeProduct Z i
  inverseBound : wordsVal s.mem base 2152 9<fieldPrime
  inverseValue : Fin.ofNat fieldPrime (wordsVal s.mem base 2152 9)=normalizeProduct Z 16^(fieldPrime-2)

theorem normalize_inverse_state_ok {base table : Addr} {s : State} {X Y Z : Nat → Fin fieldPrime}
    (hc : VG.Proof.Ecdsa.AArch64.BaseCfgOk config) (layout : NormalizeLayout base table 8192)
    (inv : NormalizePrefixInv base table 8192 16 s X Y Z)
    (hM : ModOkA config.MP' 8192 config.C.p s.mem base) :
    WP isa normalizeInverseMachine s fun t => NormalizeInverseState base table t X Y Z ∧
      Unch base normalizeInverseWrites s.mem t.mem ∧ t.gpr .x0=base ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      t.gpr .x20=s.gpr .x20 ∧ t.gpr .x26=s.gpr .x26 ∧ t.gpr .x30=s.gpr .x30 ∧ t.v .v31=s.v .v31 ∧ (∀r∈[Reg.x27,Reg.x28],t.gpr r=s.gpr r) := by
  apply normalize_inverse_machine_wp.mpr
  have bound := inv.bounds 16 (by decide) (by decide)
  change wordsVal s.mem base 1216 9<fieldPrime at bound
  refine WP.mono (normalize_inverse_phase_ok hc inv.workspace hM bound)
    fun t ⟨outBound,outValue,frame,zero,rd,wr,sp,g20,g26,g30,v31,_,tailGP⟩ => ?_
  have outside : Outside base 0 8192 s.mem t.mem := frame.outside fun w hw =>
    ⟨Nat.zero_le _,by simpa only [Nat.zero_add] using normalize_inverse_writes_fit w hw⟩
  have prefixSame (i : Nat) (hi : 1≤i) (hn : i<16) :
      wordsVal t.mem base (normalizePrefixSlot i) 9=wordsVal s.mem base (normalizePrefixSlot i) 9 :=
    frame.wordsVal (normalize_inverse_prefix_apart i hn hi)
      (by have h:=normalize_prefix_slot_fits i hi (by omega_arith); omega_arith)
  have sourceValue := inv.values 16 (by decide) (by decide)
  change Fin.ofNat fieldPrime (wordsVal s.mem base 1216 9)=normalizeProduct Z 16 at sourceValue
  rw [sourceValue] at outValue
  refine ⟨⟨⟨zero,by rw [wr]; exact inv.workspace.wr,inv.workspace.nowrap,inv.workspace.enc⟩,
    ⟨g26.trans inv.tablePtr.reg,by rw [rd,wr]; exact inv.tablePtr.ld,inv.tablePtr.enc⟩,
    inv.tableValues.of_workspace_write layout.tableApart outside,?_,?_,outBound,outValue⟩,
    frame,zero,rd,wr,sp,g20,g26,g30,v31,tailGP⟩
  · intro i hi hn
    rw [prefixSame i hi hn]
    exact inv.bounds i hi (by omega_arith)
  · intro i hi hn
    rw [prefixSame i hi hn]
    exact inv.values i hi (by omega_arith)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

theorem normalize_back_start_ok {base table : Addr} {s : State} {X Y Z : Nat → Fin fieldPrime}
    (layout : NormalizeLayout base table 8192) (inv : NormalizeInverseState base table s X Y Z)
    (tableW : PtrW s .x26 table 3456) :
    WP isa (.block (VG.Impl.Weierstrass.AArch64.copy 9 1504 2152)) s fun t =>
      NormalizeBackInv base table t X Y Z (normalizeProduct Z) (normalizeProduct Z 16^(fieldPrime-2)) ∧
      NormalizeBackKept s t ∧ Outside base 1504 72 s.mem t.mem := by
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (VG.Proof.Weierstrass.AArch64.copy_ok 9 inv.workspace (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))))
    fun t ⟨⟨value,keep,outside⟩,vectors⟩ => ?_
  have gp (r : Reg) (hr : r∈preserved) : t.gpr r=s.gpr r :=
    keep.gpr r ((by decide : ∀r∈preserved,r∉[Reg.x1]) r hr)
  have ctx : NormalizeContext base table 8192 t :=
    (NormalizeContext.advance ⟨inv.workspace,inv.tablePtr,tableW⟩
      (inv.workspace.of_keepRegs keep (by decide)) gp keep.rd keep.wr)
  have whole : Outside base 0 8192 s.mem t.mem := outside.mono (by decide) (by decide)
  have tableValues:=inv.tableValues.of_workspace_write layout.tableApart whole
  have prefixSame (n : Nat) (lo : 1≤n) (hi : n<16) :
      wordsVal t.mem base (normalizePrefixSlot n) 9=wordsVal s.mem base (normalizePrefixSlot n) 9 := by
    apply outside.wordsVal
    · have h:=(normalize_back_layout_prefix lo hi).previous
      rcases h with h|h <;> omega_arith
    · have h:=(normalize_back_layout_prefix lo hi).fits; omega_arith
  refine ⟨⟨ctx,tableValues,?_,?_,?_,?_⟩,⟨gp,keep.sp,congrFun vectors .v31,keep.rd,keep.wr⟩,outside⟩
  · intro n lo hi
    rw [prefixSame n lo hi]
    exact inv.prefixBounds n lo hi
  · intro n lo hi
    rw [prefixSame n lo hi]
    exact inv.prefixValues n lo hi
  · rw [value]; exact inv.inverseBound
  · rw [value]; exact inv.inverseValue

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)

theorem normalize_back_machine_ok {base table : Addr} {s : State} {X Y Z : Nat → Fin fieldPrime}
    (layout : NormalizeLayout base table 8192) (inv : NormalizeInverseState base table s X Y Z)
    (tableW : PtrW s .x26 table 3456) :
    let R:=normalizeBackResult Z (normalizeProduct Z) 15 X Y (normalizeProduct Z 16^(fieldPrime-2))
    WP isa normalizeBackMachine s fun t =>
      NormalizeBackInv base table t R.1 R.2.1 Z (normalizeProduct Z) R.2.2 ∧
      NormalizeBackKept s t ∧ NormalizeBackFrame base table 0 3456 s.mem t.mem := by
  apply normalize_back_machine_wp.mpr
  rw [WP.seq_iff]
  refine WP.mono (normalize_back_start_ok layout inv tableW) fun a ⟨ia,ka,fa⟩ => ?_
  refine WP.mono (normalize_back_work_ok 15 layout (by decide) ia) fun t ⟨it,kt,ft⟩ => ?_
  have frame : NormalizeBackFrame base table 0 3456 s.mem a.mem := by
    intro x hw _ _
    apply fa x
    omega_arith
  exact ⟨it,ka.trans kt,frame.trans ft⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

def normalizeInitProgram : Prog isa :=
  .seq (.block (VG.Impl.Weierstrass.AArch64.setConst 9 1072 0)) <|
  .seq (.block (VG.Impl.Weierstrass.AArch64.setConst 9 1144 1)) <|
  .seq (.block (VG.Impl.Weierstrass.AArch64.setConst 9 1216 0)) <|
  .block [.movz .x .x19 105 0]

theorem normalize_init_source : outerBlock136.drop 19=
    VG.Impl.Weierstrass.AArch64.setConst 9 1072 0++
    VG.Impl.Weierstrass.AArch64.setConst 9 1144 1++
    VG.Impl.Weierstrass.AArch64.setConst 9 1216 0++[.movz .x .x19 105 0] := by lit_decide

private theorem wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem normalize_init_wp {s : State} {Q : State → Prop} :
    WP isa (.block (outerBlock136.drop 19)) s Q ↔ WP isa normalizeInitProgram s Q := by
  rw [normalize_init_source,normalizeInitProgram]
  repeat' first | rfl | rw [WP.block_append_iff] | rw [WP.seq_iff] | (apply wp_post_iff; intro t)

private theorem const_zero_bound (n : Nat) : 0<2^(64*n) := Nat.pow_pos (by decide)

private theorem const_one_bound (n : Nat) (hn : n≠0) : 1<2^(64*n) :=
  Nat.one_lt_pow (Nat.mul_ne_zero (by decide) hn) (by decide)

private theorem set_zero_ok {s : State} {base : Addr} {W n o : Nat} (hs : Scr s base W)
    (fit : o+8*n≤W) (aligned : o%8=0) :
    WP isa (.block (VG.Impl.Weierstrass.AArch64.setConst n o 0)) s fun t =>
      wordsVal t.mem base o n=0 ∧ KeepRegs [.x1] s t ∧ Outside base o (8*n) s.mem t.mem :=
  VG.Proof.Weierstrass.AArch64.setConst_ok hs fit aligned (const_zero_bound n)

private theorem set_one_ok {s : State} {base : Addr} {W n o : Nat} (hs : Scr s base W)
    (fit : o+8*n≤W) (aligned : o%8=0) (nonzero : n≠0) :
    WP isa (.block (VG.Impl.Weierstrass.AArch64.setConst n o 1)) s fun t =>
      wordsVal t.mem base o n=1 ∧ KeepRegs [.x1] s t ∧ Outside base o (8*n) s.mem t.mem :=
  VG.Proof.Weierstrass.AArch64.setConst_ok hs fit aligned (const_one_bound n nonzero)

theorem normalize_init_ok {base : Addr} {s : State} (hs : Scr s base 8192) :
    WP isa (.block (outerBlock136.drop 19)) s fun t =>
      wordsVal t.mem base 1072 9=0 ∧ wordsVal t.mem base 1144 9=1 ∧ wordsVal t.mem base 1216 9=0 ∧
      t.gpr .x19=105 ∧ KeepRegs [.x1,.x19] s t ∧ t.v=s.v ∧ Outside base 1072 216 s.mem t.mem := by
  apply normalize_init_wp.mpr
  rw [normalizeInitProgram,WP.seq_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (set_zero_ok (n:=9) (o:=1072) hs (by decide) (by decide)))
    fun a ⟨⟨ax,ka,fa⟩,va⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (set_one_ok (n:=9) (o:=1144) (hs.of_keepRegs ka (by decide)) (by decide) (by decide) (by decide)))
    fun b ⟨⟨byY,kb,fb⟩,vb⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (set_zero_ok (n:=9) (o:=1216)
      ((hs.of_keepRegs ka (by decide)).of_keepRegs kb (by decide)) (by decide) (by decide)))
    fun c ⟨⟨cz,kc,fc⟩,vc⟩ => ?_
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (VG.Proof.Weierstrass.AArch64.movzI_ok c .x19 105)) fun t ⟨⟨counter,kd⟩,vd⟩ => ?_
  have xSame:=fc.wordsVal (k:=9) (d:=1072) (Or.inl (by decide)) (by decide)
  have xEarlier:=fb.wordsVal (k:=9) (d:=1072) (Or.inl (by decide)) (by decide)
  have ySame:=fc.wordsVal (k:=9) (d:=1144) (Or.inl (by decide)) (by decide)
  refine ⟨?_,?_,?_,counter,?_,vd.trans (vc.trans (vb.trans va)),?_⟩
  · rw [kd.mem,xSame,xEarlier,ax]
  · rw [kd.mem,ySame,byY]
  · rw [kd.mem,cz]
  · exact (ka.trans (kb.trans kc)).mono (by simp) |>.trans ((VG.Proof.Mont.AArch64.Keeps.regs kd).mono (by simp))
  · rw [kd.mem]
    exact (fa.mono (by decide) (by decide)).trans ((fb.mono (by decide) (by decide)).trans (fc.mono (by decide) (by decide)))

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native

 theorem normalize_back_result_correct {F : Type} [Mul F] (Z P J K : Nat → F) (n : Nat)
    (step : ∀r,1≤r → r≤n → J (r+1)*P r=K r ∧ J (r+1)*Z r=J r)
    (X Y : Nat → F) :
    let R:=normalizeBackResult Z P n X Y (J (n+1))
    (∀i,R.1 i=if 1≤i ∧ i≤n then K i*K i*X i else X i) ∧
    (∀i,R.2.1 i=if 1≤i ∧ i≤n then Y i*((K i*K i)*K i) else Y i) ∧ R.2.2=J 1 := by
  induction n generalizing X Y with
  | zero =>
    simp only [normalizeBackResult]
    exact ⟨fun i => by rw [ite_eq_right (by omega_arith)],fun i => by rw [ite_eq_right (by omega_arith)],trivial⟩
  | succ n ih =>
    have st:=step (n+1) (by omega_arith) (by omega_arith)
    have tailProof:=ih (fun r lo hi => step r lo (by omega_arith))
      (Function.update X (n+1) (K (n+1)*K (n+1)*X (n+1)))
      (Function.update Y (n+1) (Y (n+1)*((K (n+1)*K (n+1))*K (n+1))))
    simp only [normalizeBackResult]
    rw [st.1,st.2]
    refine ⟨?_,?_,tailProof.2.2⟩
    · intro i
      rw [tailProof.1]
      by_cases he : i=n+1
      · subst i
        rw [ite_eq_right (by omega_arith),Function.update_self,ite_eq_left (by omega_arith)]
      · rw [Function.update_of_ne he]
        by_cases h : 1≤i ∧ i≤n
        · rw [ite_eq_left h,ite_eq_left (by omega_arith)]
        · rw [ite_eq_right h,ite_eq_right (by omega_arith)]
    · intro i
      rw [tailProof.2.1]
      by_cases he : i=n+1
      · subst i
        rw [ite_eq_right (by omega_arith),Function.update_self,ite_eq_left (by omega_arith)]
      · rw [Function.update_of_ne he]
        by_cases h : 1≤i ∧ i≤n
        · rw [ite_eq_left h,ite_eq_left (by omega_arith)]
        · rw [ite_eq_right h,ite_eq_right (by omega_arith)]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Weierstrass Spec.Weierstrass

theorem normalize_back_result_nonzero {C : Curve} (law : Law C) (X Y Z : Nat → Fe C)
    (nonzero : ∀i,i<16 → Z i≠0) :
    let R:=normalizeBackResult Z (normalizeProduct Z) 15 X Y (normalizeProduct Z 16^(C.p-2))
    (∀i,R.1 i=if 1≤i ∧ i≤15 then (Z i^(C.p-2))*(Z i^(C.p-2))*X i else X i) ∧
    (∀i,R.2.1 i=if 1≤i ∧ i≤15 then Y i*(((Z i^(C.p-2))*(Z i^(C.p-2)))*(Z i^(C.p-2))) else Y i) ∧
    R.2.2=normalizeProduct Z 1^(C.p-2) := by
  exact normalize_back_result_correct Z (normalizeProduct Z)
    (fun n => normalizeProduct Z n^(C.p-2)) (fun n => Z n^(C.p-2)) 15
    (fun r _ hi => normalize_back_step law Z nonzero (by omega_arith)) X Y

theorem normalize_back_affine_rows {C : Curve} (law : Law C) (X Y Z : Nat → Fe C)
    (Q : Nat → Point C) (rep : ∀i,i<16 → InvJ C (X i) (Y i) (Z i) (Q i))
    (nonzero : ∀i,i<16 → Z i≠0) (one : Z 0=1) :
    let R:=normalizeBackResult Z (normalizeProduct Z) 15 X Y (normalizeProduct Z 16^(C.p-2))
    ∀i,i<16 → RepA C (R.1 i) (R.2.1 i) 1 (Q i) := by
  intro R i hi
  have values:=normalize_back_result_nonzero law X Y Z nonzero
  have hx:=values.1 i
  have hy:=values.2.1 i
  change R.1 i=_ at hx
  change R.2.1 i=_ at hy
  rw [hx,hy]
  by_cases lo : 1≤i
  · rw [ite_eq_left (by omega_arith),ite_eq_left (by omega_arith)]
    have affine:=normalize_affine law (rep i hi) (nonzero i hi)
    have comm : Z i^(C.p-2)*Z i^(C.p-2)*X i=X i*(Z i^(C.p-2)*Z i^(C.p-2)) :=
      Lean.Grind.CommRing.mul_comm _ _
    rw [comm]
    exact affine
  · have eq : i=0 := by omega_arith
    subst i
    rw [ite_eq_right (by omega_arith),ite_eq_right (by omega_arith)]
    have r:=rep 0 hi
    rw [one] at r
    refine ⟨?_,Or.inl rfl⟩
    simpa only [Lean.Grind.Semiring.mul_one] using r.rep_of_ne law.one_ne_zero

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (config outerBlock136)

def normalizePhases : Prog isa :=
  .seq normalizePrefixMachine <| .seq normalizeInverseMachine <|
  .seq normalizeBackMachine (.block (outerBlock136.drop 19))

structure NormalizePost (base table : Addr) (s t : State) (X Y Z : Nat → Fin fieldPrime) : Prop where
  context : NormalizeContext base table 8192 t
  tableValues : let R:=normalizeBackResult Z (normalizeProduct Z) 15 X Y (normalizeProduct Z 16^(fieldPrime-2))
    NormalizeTable table t R.1 R.2.1 Z
  accumulatorX : wordsVal t.mem base 1072 9=0
  accumulatorY : wordsVal t.mem base 1144 9=1
  accumulatorZ : wordsVal t.mem base 1216 9=0
  counter : t.gpr .x19=105
  outputPointer : t.gpr .x20=word s.mem base 3944
  link : t.gpr .x30=s.gpr .x30
  vector31 : t.v .v31=s.v .v31
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  lowMemory : ∀d,d<856 → t.mem (off base d)=s.mem (off base d)
  originalD : wordsVal t.mem base 2368 9=wordsVal s.mem base 2368 9
  readonly : ∀d,3232≤d → d<3952 → t.mem (off base d)=s.mem (off base d)
  tailGP : ∀r∈[Reg.x27,Reg.x28],t.gpr r=s.gpr r
  farMemory : ∀x,8192≤ofs base x → 3456≤ofs table x → t.mem x=s.mem x

theorem normalize_phases_ok {base table : Addr} {s : State} {X Y Z : Nat → Fin fieldPrime}
    (hc : VG.Proof.Ecdsa.AArch64.BaseCfgOk config) (layout : NormalizeLayout base table 8192)
    (inv : NormalizePrefixInv base table 8192 1 s X Y Z) (tableW : PtrW s .x26 table 3456)
    (hM : ModOkA config.MP' 8192 config.C.p s.mem base) :
    WP isa normalizePhases s fun t => NormalizePost base table s t X Y Z := by
  rw [normalizePhases,WP.seq_iff]
  refine WP.mono (normalize_prefix_machine_ok layout inv)
    fun a ⟨ia,_,_,ra,wa,sa,ga,g20a,v31a,_,fa⟩ => ?_
  have modSame := fa.wordsVal (d:=config.MP'.mo) (k:=config.MP'.n) (by decide) (by decide)
  have ma : ModOkA config.MP' 8192 config.C.p a.mem base := {hM with val:=by rw [modSame]; exact hM.val}
  rw [WP.seq_iff]
  refine WP.mono (normalize_inverse_state_ok hc layout ia ma)
    fun b ⟨ib,fb,_,rb,wb,sb,g20b,g26b,g30b,v31b,tailB⟩ => ?_
  have ptA : PtrW a .x26 table 3456 :=
    ⟨(ga .x26 (by decide) (by decide)).trans tableW.reg,by rw [wa]; exact tableW.st,tableW.enc,tableW.nowrap⟩
  have ptB : PtrW b .x26 table 3456 :=
    ⟨g26b.trans ptA.reg,by rw [wb]; exact ptA.st,ptA.enc,ptA.nowrap⟩
  rw [WP.seq_iff]
  refine WP.mono (normalize_back_machine_ok layout ib ptB) fun c ⟨ic,kc,fc⟩ => ?_
  refine WP.mono (normalize_init_ok ic.context.workspace) fun t ⟨tx,ty,tz,tc,kt,vt,ft⟩ => ?_
  have gpInit (r : Reg) (hr : r∈preserved) (ne : r≠.x19) : t.gpr r=c.gpr r :=
    kt.gpr r (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; exact ⟨(by
      have h : ∀r∈preserved,r≠Reg.x1 := by decide
      exact h r hr),ne⟩)
  have ctx : NormalizeContext base table 8192 t :=
    ⟨ic.context.workspace.of_keepRegs kt (by decide),
      ⟨(gpInit .x26 (by decide) (by decide)).trans ic.context.readTable.reg,
        by rw [kt.rd,kt.wr]; exact ic.context.readTable.ld,ic.context.readTable.enc⟩,
      ⟨(gpInit .x26 (by decide) (by decide)).trans ic.context.tableW.reg,
        by rw [kt.wr]; exact ic.context.tableW.st,ic.context.tableW.enc,ic.context.tableW.nowrap⟩⟩
  refine ⟨ctx,ic.tableValues.of_workspace_write layout.tableApart (ft.mono (by decide) (by decide)),tx,ty,tz,tc,
    (gpInit .x20 (by decide) (by decide)).trans ((kc.gp .x20 (by decide)).trans (g20b.trans g20a)),
    (gpInit .x30 (by decide) (by decide)).trans ((kc.gp .x30 (by decide)).trans
      (g30b.trans (ga .x30 (by decide) (by decide)))),
    (congrFun vt .v31).trans (kc.v31.trans (v31b.trans v31a)),
    kt.rd.trans (kc.rd.trans (rb.trans ra)),kt.wr.trans (kc.wr.trans (wb.trans wa)),
    kt.sp.trans (kc.sp.trans (sb.trans sa)),?_,?_,?_,?_,?_⟩
  · intro d hd
    have aSame:=fa.byte (d:=d) (by
      intro w hw
      have h : ∀w∈normalizePrefixWrites,856≤w.1 := by decide
      exact Or.inl (by have e:=h w hw; omega_arith)) (by omega_arith)
    have bSame:=fb.byte (d:=d) (by
      intro w hw
      have h : ∀w∈normalizeInverseWrites,856≤w.1 := by decide
      exact Or.inl (by have e:=h w hw; omega_arith)) (by omega_arith)
    have cSame:=fc.workspace_byte layout.tableApart (by decide) (by decide) (by omega_arith)
      (d:=d) (Or.inl (by omega_arith)) (Or.inl (by omega_arith))
    have tSame : t.mem (off base d)=c.mem (off base d) := by
      apply ft
      rw [ofs_off0 base (by omega_arith)]
      exact Or.inl (by omega_arith)
    exact tSame.trans (cSame.trans (bSame.trans aSame))
  · rw [ft.wordsVal (k:=9) (d:=2368) (Or.inr (by decide)) (by decide),
      fc.workspace_words layout.tableApart (by decide) (by decide) 9 2368 (by decide) (Or.inr (by decide)) (Or.inl (by decide)),
      fb.wordsVal (d:=2368) (k:=9) (by decide) (by decide),
      fa.wordsVal (d:=2368) (k:=9) (by decide) (by decide)]
  · intro d lo hi
    have aSame:=fa.byte (d:=d) (by intro w hw; have h:=normalize_prefix_readonly w hw; omega_arith) (by omega_arith)
    have bSame:=fb.byte (d:=d) (by intro w hw; have h:=normalize_inverse_readonly w hw; omega_arith) (by omega_arith)
    have cSame:=fc.readonly layout.tableApart (by decide) lo hi
    have tSame : t.mem (off base d)=c.mem (off base d) := by
      apply ft
      rw [ofs_off0 base (by omega_arith)]
      omega_arith
    exact tSame.trans (cSame.trans (bSame.trans aSame))
  · intro r hr
    have choices : r=Reg.x27 ∨ r=Reg.x28 := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hr
    rcases choices with rfl|rfl
    · exact (gpInit .x27 (by decide) (by decide)).trans ((kc.gp .x27 (by decide)).trans ((tailB .x27 (by decide)).trans (ga .x27 (by decide) (by decide))))
    · exact (gpInit .x28 (by decide) (by decide)).trans ((kc.gp .x28 (by decide)).trans ((tailB .x28 (by decide)).trans (ga .x28 (by decide) (by decide))))
  · intro x workspaceFar tableFar
    have first:=fa.far (x:=x) (by
      intro w hw
      have fits : ∀w∈normalizePrefixWrites,w.1+w.2≤8192 := by decide
      have fit:=fits w hw
      omega_arith)
    have second:=fb.far (x:=x) (by intro w hw; have fit:=normalize_inverse_writes_fit w hw; omega_arith)
    have third:=fc x (Or.inr (by omega_arith)) (Or.inr (by omega_arith)) (Or.inr tableFar)
    have fourth:=ft x (Or.inr (by omega_arith))
    exact fourth.trans (third.trans (second.trans first))

end VG.Proof.Weierstrass.AArch64.P521Native
