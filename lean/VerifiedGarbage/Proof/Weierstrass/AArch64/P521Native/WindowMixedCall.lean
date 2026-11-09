module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedFunction
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleOutput
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-! A fused mixed-add call on the fixed window buffers, with real ABI and permissions. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Impl.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native (callNormalMadd)
open VG.Proof.Weierstrass (maddJF)

 def windowMixedEnv (mem : Mem) (base : Addr) (i : Nat) : Fin fieldPrime :=
  Fin.ofNat fieldPrime (wordsVal mem base (mixedSlot 1072 1504 i) 9)

 def windowMixedValue (mem : Mem) (base : Addr) :=
  if wordsVal mem base 1216 9=0 then (windowMixedEnv mem base 3,windowMixedEnv mem base 4,1)
  else maddJF (windowMixedEnv mem base 0) (windowMixedEnv mem base 1) (windowMixedEnv mem base 2)
    (windowMixedEnv mem base 3) (windowMixedEnv mem base 4)

 def WindowMixedFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<4080 ∨ 4512≤ofs base x) →
    (ofs base x<1288 ∨ 1504≤ofs base x) → m' x=m x

 def windowMixedK (W : Nat) (base : Addr) (mem : Mem) : Contract isa where
  pre t := Scr t (t.gpr .x0) W ∧ t.gpr .x0=base ∧ t.mem=mem ∧
    t.gpr .x1=1288#64 ∧ t.gpr .x2=1072#64 ∧ t.gpr .x3=1504#64 ∧
    canonicalPoint t.mem base 1072 ∧ canonicalPoint t.mem base 1504
  post s t := canonicalPoint t.mem base 1288 ∧ ordinaryPoint t.mem base 1288=windowMixedValue mem base ∧
    WindowMixedFrame base mem t.mem ∧ t.gpr .x0=base ∧ t.v .v29=s.v .v29 ∧ t.v .v31=s.v .v31
  pub _ _ := True

 theorem window_mixed_no29 : ∀i∈instrs mixedFn,vdstOf i≠some .v29 := by
  change ∀i∈mixedFnBlocks.flatten,vdstOf i≠some .v29
  have h : mixedFnBlocks.flatten.all (fun i => vdstOf i != some .v29)=true := by lit_decide
  simpa only [List.all_eq_true,bne_iff_ne] using h

 theorem window_mixed_call_ok {s : State} {W : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4512≤W)
    (argO : s.gpr .x1=1288#64) (argA : s.gpr .x2=1072#64) (argB : s.gpr .x3=1504#64)
    (ca : canonicalPoint s.mem (s.gpr .x0) 1072) (ce : canonicalPoint s.mem (s.gpr .x0) 1504) :
    WP isa callNormalMadd s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1288 ∧ ordinaryPoint t.mem (s.gpr .x0) 1288=windowMixedValue s.mem (s.gpr .x0) ∧
      WindowMixedFrame (s.gpr .x0) s.mem t.mem ∧ t.gpr .x0=s.gpr .x0 ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp ∧
      (∀r∈preserved,r≠.x30 → t.gpr r=s.gpr r) ∧ t.v .v29=s.v .v29 ∧ t.v .v31=s.v .v31 := by
  let base := s.gpr .x0
  have hcov : Covers [⟨base,W⟩] s.wr := Covers.one ⟨_,hs.wr,by
    have h := hs.contains (d:=0) (n:=W) (by omega_arith) (by omega_arith)
    simpa [off] using h⟩
  let entry := s.callEntry.withRegions [] [⟨base,W⟩]
  have cg (r : Reg) (hr : r∉linkRegs) : entry.gpr r=s.gpr r := State.callEntry_gpr s hr
  have e0 : entry.gpr .x0=base := cg .x0 (by decide)
  have ws : Scr entry (entry.gpr .x0) W := by
    refine ⟨rfl,?_,?_,hs.enc⟩
    · rw [e0]; exact List.mem_cons_self
    · rw [e0]; exact hs.nowrap
  apply WP.callV (k:=windowMixedK W base s.mem)
    (fun t ⟨ht,t0,mt,to,ta,tb,cat,cet⟩ => ?_)
    (rd:=[]) (wr:=[⟨base,W⟩])
    ⟨ws,e0,rfl,(cg .x1 (by decide)).trans argO,(cg .x2 (by decide)).trans argA,
      (cg .x3 (by decide)).trans argB,ca,ce⟩ (Covers.right hcov) hcov
    (fun t rd wr sp _ gp _ _ post => ?_) (by rfl)
  · have inv : OrdinaryInv (t.gpr .x0) fieldPrime (mixedSlot 1072 1504) [0,1,2,3,4]
        (windowMixedEnv s.mem base) (fun _ => 1) t := by
      constructor
      · intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl
        · simpa only [t0,mixedSlot,Nat.reduceLT,ite_true,Nat.mul_zero,Nat.add_zero,Nat.one_mul] using cat.1
        · simpa only [t0,mixedSlot,Nat.reduceLT,ite_true,Nat.mul_one,Nat.reduceAdd,Nat.one_mul] using cat.2.1
        · simpa only [t0,mixedSlot,Nat.reduceLT,ite_true,Nat.reduceMul,Nat.reduceAdd,Nat.one_mul] using cat.2.2
        · simpa only [t0,mixedSlot,Nat.reduceLT,ite_true,ite_false,Nat.reduceSub,Nat.mul_zero,Nat.add_zero,Nat.one_mul] using cet.1
        · simpa only [t0,mixedSlot,Nat.reduceLT,ite_true,ite_false,Nat.reduceSub,Nat.mul_one,Nat.reduceAdd,Nat.one_mul] using cet.2.1
      · intro i _; rw [t0,mt]; rfl
    obtain ⟨trace,u,exec,abi,bx,byy,bz,p,f,z,_,_,v31⟩ := mixed_fn_ok ht room
      (a:=1072) (b:=1504) (o:=1288) (by constructor <;> decide) (by decide) to ta tb inv
    have v29 := Exec.vec window_mixed_no29 exec
    rw [t0] at bx byy bz p f z
    rw [mt] at p f
    exact ⟨trace,u,exec,abi,⟨bx,byy,bz⟩,p,f,z,v29,v31⟩
  · rcases post with ⟨b,p,frame,zero,v29,v31⟩
    exact ⟨b,p,frame,zero,rd,wr,sp,gp,v29,v31⟩

end VG.Proof.Weierstrass.AArch64.P521Native
