module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeFunction
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Square
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (callNormalMul callNormalSqr)
open VG.Proof.Weierstrass.AArch64.Mont (Pre arg Kept)

theorem NativePre.callEntry {s : State} {W o a b : Nat} (h : NativePre s W o a b) :
    NativePre s.callEntry W o a b := by
  have k : KeepRegs linkRegs s s.callEntry :=
    ⟨fun r hr => State.callEntry_gpr s hr,rfl,rfl,rfl⟩
  have ce0 := State.callEntry_gpr s (r:=.x0) (by decide)
  refine ⟨?_,h.scratch,h.output,h.inputA,h.inputB,h.scratchA,?_,?_,?_⟩
  · rw [ce0]
    exact h.workspace.of_keepRegs k (by decide)
  · exact (State.callEntry_gpr s (by decide)).trans h.argO
  · exact (State.callEntry_gpr s (by decide)).trans h.argA
  · exact (State.callEntry_gpr s (by decide)).trans h.argB

theorem normalize_mul_call_ok {s : State} {W o a b : Nat} (hp : NativePre s W o a b)
    (ha : wordsVal s.mem (s.gpr .x0) a 9<fieldPrime)
    (hb : wordsVal s.mem (s.gpr .x0) b 9<fieldPrime) :
    WP isa callNormalMul s fun t =>
      wordsVal t.mem (s.gpr .x0) o 9<fieldPrime ∧
      wordsVal t.mem (s.gpr .x0) o 9=wordsVal s.mem (s.gpr .x0) a 9*wordsVal s.mem (s.gpr .x0) b 9%fieldPrime ∧
      (∀x,(ofs (s.gpr .x0) x<o ∨ o+72≤ofs (s.gpr .x0) x) →
        (ofs (s.gpr .x0) x<3952 ∨ 4016≤ofs (s.gpr .x0) x) → t.mem x=s.mem x) ∧
      t.gpr .x0=s.gpr .x0 ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      (∀r∈preserved,r≠.x30 → t.gpr r=s.gpr r) ∧ t.v .v29=s.v .v29 ∧ t.v .v31=s.v .v31 := by
  have ce0 := State.callEntry_gpr s (r:=.x0) (by decide)
  have ha' : wordsVal s.callEntry.mem (s.callEntry.gpr .x0) a 9<fieldPrime := by rw [ce0]; exact ha
  have hb' : wordsVal s.callEntry.mem (s.callEntry.gpr .x0) b 9<fieldPrime := by rw [ce0]; exact hb
  obtain ⟨trace,t,exec,abi,⟨bound,prod⟩,frame,zero,rd,wr,vec⟩ := native_mul_fn_ok (NativePre.callEntry hp) ha' hb'
  have ret : isa.ret s.callEntry t=some t := by
    have link := abi.1 .x30 (by decide)
    simp only [isa,VG.AArch64.ret,link,ite_true]
  refine ⟨_,t,Exec.call (call_callEntry s) exec ret,?_,?_,?_,?_,rd,wr,abi.2.1,?_,?_,?_⟩
  · simpa only [ce0,State.callEntry_mem] using bound
  · simpa only [ce0,State.callEntry_mem] using prod
  · simpa only [ce0,State.callEntry_mem] using frame
  · exact zero.trans ce0
  · intro r hr h30
    exact (abi.1 r hr).trans (State.callEntry_gpr s (preserved_not_link r hr h30))
  · exact vec .v29 (by decide)
  · exact vec .v31 (by decide)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Weierstrass.AArch64.P521Native (callNormalSqr)
open VG.Proof.Weierstrass.AArch64.Mont (Pre arg Kept)

structure NormalizeSquarePre (s : State) (W o a : Nat) : Prop where
  workspace : Scr s (s.gpr .x0) W
  min : 4024≤W
  max : W≤8192
  output : o+72≤3520
  input : a+72≤3520
  argO : s.gpr .x1=BitVec.ofNat 64 o
  argA : s.gpr .x2=BitVec.ofNat 64 a
  argB : s.gpr .x3=BitVec.ofNat 64 a

def normalizeSquareK (W o a : Nat) (base : Addr) (mem : Mem) : Contract isa where
  pre t := Pre 9 W t ∧ t.gpr .x0=base ∧ arg t .x1=o ∧ arg t .x2=a ∧ t.mem=mem
  post s t := (wordsVal t.mem base o 9<fieldPrime ∧
      wordsVal t.mem base o 9=wordsVal mem base a 9*wordsVal mem base a 9%fieldPrime) ∧
    Kept 9 base o mem t.mem ∧ t.gpr .x0=base ∧ t.v .v29=s.v .v29 ∧ t.v .v31=s.v .v31
  pub _ _ := True

theorem normalize_square_call_ok {s : State} {W o a : Nat} (hp : NormalizeSquarePre s W o a)
    (ha : wordsVal s.mem (s.gpr .x0) a 9<fieldPrime) :
    WP isa callNormalSqr s fun t =>
      wordsVal t.mem (s.gpr .x0) o 9<fieldPrime ∧
      wordsVal t.mem (s.gpr .x0) o 9=wordsVal s.mem (s.gpr .x0) a 9*wordsVal s.mem (s.gpr .x0) a 9%fieldPrime ∧
      Kept 9 (s.gpr .x0) o s.mem t.mem ∧ t.gpr .x0=s.gpr .x0 ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      (∀r∈preserved,r≠.x30 → t.gpr r=s.gpr r) ∧ t.v .v29=s.v .v29 ∧ t.v .v31=s.v .v31 := by
  let base := s.gpr .x0
  have hcov : Covers [⟨base,W⟩] s.wr := by
    exact Covers.one ⟨_,hp.workspace.wr,by
      have h := hp.workspace.contains (d:=0) (n:=W) (by omega_arith) (by have hmin:=hp.min; omega_arith)
      simpa [off] using h⟩
  let entry := s.callEntry.withRegions [] [⟨base,W⟩]
  have ce (r : Reg) (hr : r∉linkRegs) : entry.gpr r=s.gpr r := State.callEntry_gpr s hr
  have e0 : entry.gpr .x0=base := ce .x0 (by decide)
  have e1 : arg entry .x1=o := by
    simp only [arg,ce .x1 (by decide),hp.argO,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    have h:=hp.output
    omega_arith
  have e2 : arg entry .x2=a := by
    simp only [arg,ce .x2 (by decide),hp.argA,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    have h:=hp.input
    omega_arith
  have e3 : arg entry .x3=a := by
    simp only [arg,ce .x3 (by decide),hp.argB,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    have h:=hp.input
    omega_arith
  have pre : Pre 9 W entry := by
    refine ⟨rfl,?_,?_,hp.min,hp.max,?_,?_,?_⟩
    · rw [e0]; rfl
    · rw [e0]; exact hp.workspace.nowrap
    · rw [e1]; exact hp.output
    · rw [e2]; exact hp.input
    · rw [e3]; exact hp.input
  apply WP.callV (k:=normalizeSquareK W o a base s.mem)
    (fun t ⟨pt,t0,t1,t2,mt⟩ => ?_)
    (rd:=[]) (wr:=[⟨base,W⟩]) ⟨pre,e0,e1,e2,rfl⟩ (Covers.right hcov) hcov
    (fun t rd wr sp _ gp _ _ post => ?_) (by rfl)
  · have ht : wordsVal t.mem (t.gpr .x0) (arg t .x2) 9<fieldPrime := by rw [t0,t2,mt]; exact ha
    obtain ⟨trace,u,exec,abi,frame,value,zero,_,_,v29,v31⟩ := square_fn_ok pt ht
    rw [t0,t1,mt] at frame
    rw [t0,t1,t2,mt] at value
    rw [t0] at zero
    exact ⟨trace,u,exec,abi,value,frame,zero,v29,v31⟩
  · rcases post with ⟨⟨b,p⟩,frame,zero,v29,v31⟩
    exact ⟨b,p,frame,zero,rd,wr,sp,gp,v29,v31⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Impl.Weierstrass.AArch64.P521Native (callNormalMul callNormalSqr)

def normalizeCallArgs (o a b : Nat) : List Instr := [
  .vop (.ins .d2 .v29 0 .x30),.movz .x .x1 (BitVec.ofNat 16 o) 0,
  .movz .x .x2 (BitVec.ofNat 16 a) 0,.movz .x .x3 (BitVec.ofNat 16 b) 0]

theorem normalize_args_ok (s : State) {o a b : Nat} (ho : o<2^16) (ha : a<2^16) (hb : b<2^16) :
    WP isa (.block (normalizeCallArgs o a b)) s fun t =>
      t.gpr .x1=BitVec.ofNat 64 o ∧ t.gpr .x2=BitVec.ofNat 64 a ∧ t.gpr .x3=BitVec.ofNat 64 b ∧
      Keeps [.x1,.x2,.x3] s t ∧ (t.v .v29).extractLsb' 0 64=s.gpr .x30 ∧ t.v .v31=s.v .v31 := by
  have h := VG.Proof.Weierstrass.AArch64.Mont.args_ok s ho ha hb
  obtain ⟨trace,t,exec,o,a,b,k,lr⟩ := h
  have eqOfNat (x : BitVec 64) (n : Nat) (hx : x.toNat=n) : x=BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat,←hx,Nat.mod_eq_of_lt x.isLt]
  refine ⟨trace,t,exec,eqOfNat _ _ o,eqOfNat _ _ a,eqOfNat _ _ b,k,lr,?_⟩
  apply Exec.vec (c:=.block (normalizeCallArgs _ _ _)) (r:=.v31) ?_ exec
  simp only [instrs,normalizeCallArgs,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    vdstOf,VOp.dst,and_self]
  decide

def normalizeMulStep (o a b : Nat) : Prog isa :=
  .seq (.block (normalizeCallArgs o a b)) (.seq callNormalMul (.block [.umov .x .x30 .v29 0]))

theorem normalize_mul_step_ok {s : State} {base : Addr} {W o a b : Nat} (hs : Scr s base W)
    (hW : 4016≤W) (ho : o+72≤W) (ha : a+72≤W) (hb : b+72≤W)
    (scratchA : a+72≤3952 ∨ 4016≤a)
    (boundA : wordsVal s.mem base a 9<fieldPrime) (boundB : wordsVal s.mem base b 9<fieldPrime) :
    WP isa (normalizeMulStep o a b) s fun t =>
      wordsVal t.mem base o 9<fieldPrime ∧
      wordsVal t.mem base o 9=wordsVal s.mem base a 9*wordsVal s.mem base b 9%fieldPrime ∧
      (∀x,(ofs base x<o ∨ o+72≤ofs base x) → (ofs base x<3952 ∨ 4016≤ofs base x) → t.mem x=s.mem x) ∧
      t.gpr .x0=base ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      (∀r∈preserved,t.gpr r=s.gpr r) ∧ t.v .v31=s.v .v31 := by
  rw [normalizeMulStep,WP.seq_iff]
  refine WP.mono (normalize_args_ok s (o:=o) (a:=a) (b:=b)
    (by have h:=hs.enc; omega_arith) (by have h:=hs.enc; omega_arith) (by have h:=hs.enc; omega_arith))
    fun u ⟨ao,aa,ab,ku,lr,vu⟩ => ?_
  have hu : u.gpr .x0=base := (ku.gpr .x0 (by decide)).trans hs.x0
  have upre : NativePre u W o a b :=
    ⟨by rw [hu]; exact hs.of_keeps ku (by decide),hW,ho,ha,hb,scratchA,ao,aa,ab⟩
  have ba : wordsVal u.mem (u.gpr .x0) a 9<fieldPrime := by rw [ku.mem,hu]; exact boundA
  have bb : wordsVal u.mem (u.gpr .x0) b 9<fieldPrime := by rw [ku.mem,hu]; exact boundB
  rw [WP.seq_iff]
  refine WP.mono (normalize_mul_call_ok upre ba bb) fun v ⟨bo,prod,frame,zero,rd,wr,sp,gp,v29,v31⟩ => ?_
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (VG.Proof.Weierstrass.AArch64.Mont.lr_ok v)) fun t ⟨⟨rest,kt⟩,vt⟩ => ?_
  rw [hu] at bo prod frame
  rw [ku.mem] at prod frame
  refine ⟨?_,?_,?_,?_,kt.rd.trans (rd.trans ku.rd),kt.wr.trans (wr.trans ku.wr),
    kt.sp.trans (sp.trans ku.sp),?_,?_⟩
  · rw [kt.mem]; exact bo
  · rw [kt.mem]; exact prod
  · rw [kt.mem]; exact frame
  · exact (kt.gpr .x0 (by decide)).trans (zero.trans hu)
  · intro r hr
    by_cases h30 : r=.x30
    · rw [h30,rest,v29,lr]
    · exact (kt.gpr r (by simpa only [List.mem_singleton] using h30)).trans
        ((gp r hr h30).trans (ku.gpr r ((by decide : ∀r∈preserved,r∉[Reg.x1,.x2,.x3]) r hr)))
  · rw [vt,v31,vu]

def normalizeSquareStep (o a : Nat) : Prog isa :=
  .seq (.block (normalizeCallArgs o a a)) (.seq callNormalSqr (.block [.umov .x .x30 .v29 0]))

theorem normalize_square_step_ok {s : State} {base : Addr} {W o a : Nat} (hs : Scr s base W)
    (hW : 4024≤W) (hMax : W≤8192) (ho : o+72≤3520) (ha : a+72≤3520)
    (boundA : wordsVal s.mem base a 9<fieldPrime) :
    WP isa (normalizeSquareStep o a) s fun t =>
      wordsVal t.mem base o 9<fieldPrime ∧
      wordsVal t.mem base o 9=wordsVal s.mem base a 9*wordsVal s.mem base a 9%fieldPrime ∧
      VG.Proof.Weierstrass.AArch64.Mont.Kept 9 base o s.mem t.mem ∧
      t.gpr .x0=base ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      (∀r∈preserved,t.gpr r=s.gpr r) ∧ t.v .v31=s.v .v31 := by
  rw [normalizeSquareStep,WP.seq_iff]
  refine WP.mono (normalize_args_ok s (o:=o) (a:=a) (b:=a)
    (by omega_arith) (by omega_arith) (by omega_arith))
    fun u ⟨ao,aa,ab,ku,lr,vu⟩ => ?_
  have hu : u.gpr .x0=base := (ku.gpr .x0 (by decide)).trans hs.x0
  have upre : NormalizeSquarePre u W o a :=
    ⟨by rw [hu]; exact hs.of_keeps ku (by decide),hW,hMax,ho,ha,ao,aa,ab⟩
  have ba : wordsVal u.mem (u.gpr .x0) a 9<fieldPrime := by rw [ku.mem,hu]; exact boundA
  rw [WP.seq_iff]
  refine WP.mono (normalize_square_call_ok upre ba) fun v ⟨bo,prod,frame,zero,rd,wr,sp,gp,v29,v31⟩ => ?_
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (VG.Proof.Weierstrass.AArch64.Mont.lr_ok v)) fun t ⟨⟨rest,kt⟩,vt⟩ => ?_
  rw [hu] at bo prod frame
  rw [ku.mem] at prod frame
  refine ⟨?_,?_,?_,?_,kt.rd.trans (rd.trans ku.rd),kt.wr.trans (wr.trans ku.wr),
    kt.sp.trans (sp.trans ku.sp),?_,?_⟩
  · rw [kt.mem]; exact bo
  · rw [kt.mem]; exact prod
  · rw [kt.mem]; exact frame
  · exact (kt.gpr .x0 (by decide)).trans (zero.trans hu)
  · intro r hr
    by_cases h30 : r=.x30
    · rw [h30,rest,v29,lr]
    · exact (kt.gpr r (by simpa only [List.mem_singleton] using h30)).trans
        ((gp r hr h30).trans (ku.gpr r ((by decide : ∀r∈preserved,r∉[Reg.x1,.x2,.x3]) r hr)))
  · rw [vt,v31,vu]

end VG.Proof.Weierstrass.AArch64.P521Native
