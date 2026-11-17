module

-- separate module: this consolidated proof replays 1.05s of elaboration/kernel work versus 0.53s importing its dependencies (local Lean trace); retaining the boundary avoids replaying it in its sole importer.
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowZero
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowSelectWords
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.OuterBlocks
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.DoubleOutput
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.KernelSlice
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowDoublePair
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedFunction
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! ### `Weierstrass.AArch64.P521Native.WindowMixedStep`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.AArch64.P521Native.WindowMixedCall`, which this module and modules that import it used -/

section

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

end

end

/-! Exact mixed-call argument setup and complete measured BL protocol. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native

 def windowMixedArgs : List Instr := [.movz .x .x1 1288 0,.movz .x .x2 1072 0,.movz .x .x3 1504 0]
 def windowMixedStep : Prog isa := .seq (.block windowMixedArgs) callNormalMadd

 theorem window_mixed_args_source : outerBlock142.drop 747=windowMixedArgs := by
  have h := drop_flatten_prefix outerBlock142Chunks 23 736 11
    (by rw [List.length_flatten]; lit_decide)
  rw [outerBlock142,h]
  decide

 theorem window_mixed_args_ok (s : State) :
    WP isa (.block windowMixedArgs) s fun t =>
      t.gpr .x1=1288#64 ∧ t.gpr .x2=1072#64 ∧ t.gpr .x3=1504#64 ∧
      Keeps [.x1,.x2,.x3] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [windowMixedArgs,runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,Nat.reduceMul,
    Nat.reduceLT,ite_true,BitVec.shiftLeft_zero,RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,rfl,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩,rfl⟩
  reg_keeps

 theorem window_mixed_step_ok {s : State} {W : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4512≤W)
    (ca : canonicalPoint s.mem (s.gpr .x0) 1072) (ce : canonicalPoint s.mem (s.gpr .x0) 1504) :
    WP isa windowMixedStep s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1288 ∧ ordinaryPoint t.mem (s.gpr .x0) 1288=windowMixedValue s.mem (s.gpr .x0) ∧
      WindowMixedFrame (s.gpr .x0) s.mem t.mem ∧ WindowStable s t := by
  rw [windowMixedStep,WP.seq_iff]
  refine WP.mono (window_mixed_args_ok s) fun u ⟨o,a,b,ku,vu⟩ => ?_
  have u0 := ku.gpr .x0 (by decide)
  have hu : Scr u (u.gpr .x0) W := by rw [u0]; exact hs.of_keeps ku (by decide)
  have au : canonicalPoint u.mem (u.gpr .x0) 1072 := by rw [u0,ku.mem]; exact ca
  have bu : canonicalPoint u.mem (u.gpr .x0) 1504 := by rw [u0,ku.mem]; exact ce
  refine WP.mono (window_mixed_call_ok hu room o a b au bu)
    fun t ⟨bt,pt,ft,zero,rd,wr,sp,gp,v29,v31⟩ => ?_
  rw [u0] at bt pt ft zero
  rw [ku.mem] at pt ft
  have fresh : ∀r∈preserved,r∉[Reg.x1,Reg.x2,Reg.x3] := by decide
  exact ⟨bt,pt,ft,zero,rd.trans ku.rd,wr.trans ku.wr,sp.trans ku.sp,
    fun r hr hn => (gp r hr hn).trans (ku.gpr r (fresh r hr)),by rw [v29,vu],by rw [v31,vu]⟩

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

theorem window_select_digit_source :
    (outerBlock143.drop 20).take 162=windowSelectWords 1072 1288 1288 27 := by decide

theorem window_select_infinity_source :
    (outerBlock143.drop 202).take 162=windowSelectWords 1504 1288 1072 27 := by decide

theorem window_select_partition : outerBlock143=
    outerBlock143.take 20++windowSelectWords 1072 1288 1288 27++
    (outerBlock143.drop 182).take 20++windowSelectWords 1504 1288 1072 27++
    outerBlock143.drop 364 := by
  rw [←window_select_digit_source,←window_select_infinity_source]
  have split (xs : List Instr) : xs=
      xs.take 20++(xs.drop 20).take 162++(xs.drop 182).take 20++
      (xs.drop 202).take 162++xs.drop 364 := by
    simp only [←List.take_add,List.take_append_drop,Nat.reduceAdd]
  exact split outerBlock143

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Weierstrass.AArch64.P521Native

def windowSelectTail : List Instr := windowZeroCode 1648++windowSelectWords 1072 1288 1288 27++
  windowZeroCode 1216++windowSelectWords 1504 1288 1072 27

theorem window_select_tail_source : outerBlock143.take 364=windowSelectTail := by
  rw [windowSelectTail,←window_zero_digit_source,←window_select_digit_source,
    ←window_zero_accumulator_source,←window_select_infinity_source]
  simp only [←List.take_add,Nat.reduceAdd]

theorem window_select_tail_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hsz : 1720≤size) :
    WP isa (.block windowSelectTail) s fun t =>
      (∀i<27,word t.mem base (1072+8*i)=
        if wordsVal s.mem base 1216 9=0 then word s.mem base (1504+8*i)
        else if wordsVal s.mem base 1648 9=0 then word s.mem base (1072+8*i)
        else word s.mem base (1288+8*i)) ∧
      KeepRegs [.x1,.x2,.x3,.x7,.x16] s t ∧ Outside base 1072 432 s.mem t.mem := by
  rw [windowSelectTail,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (window_zero_ok hs (z:=1648) (by omega_arith) (by decide)) fun u ⟨maskU,ku⟩ => ?_
  rw [WP.block_append_iff]
  let d : Bool := decide (wordsVal s.mem base 1648 9≠0)
  obtain mu : u.gpr .x3=if d then BitVec.allOnes 64 else 0 := by
    rw [maskU]; dsimp only [d]
    by_cases h : wordsVal s.mem base 1648 9=0 <;> simp [h]
  obtain hu := hs.of_keeps ku (by decide)
  refine WP.mono (window_select_words hu (a:=1072) (b:=1288) (o:=1288) (n:=27)
    (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide)
    (by right; left; decide) (by left; rfl) d mu 27 (by decide)) fun v ⟨ev,kv,ov⟩ => ?_
  rw [WP.block_append_iff]
  obtain hv := hu.of_keepRegs kv (by decide)
  refine WP.mono (window_zero_ok hv (z:=1216) (by omega_arith) (by decide)) fun w ⟨maskW,kw⟩ => ?_
  let a : Bool := decide (wordsVal s.mem base 1216 9≠0)
  obtain vz : wordsVal v.mem base 1216 9=wordsVal s.mem base 1216 9 := by
    rw [ov.wordsVal (by omega_arith) (by have := hs.nowrap; omega_arith),ku.mem]
  obtain mw : w.gpr .x3=if a then BitVec.allOnes 64 else 0 := by
    rw [maskW,vz]; dsimp only [a]
    by_cases h : wordsVal s.mem base 1216 9=0 <;> simp [h]
  obtain hw := hv.of_keeps kw (by decide)
  refine WP.mono (window_select_words hw (a:=1504) (b:=1288) (o:=1072) (n:=27)
    (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide)
    (by right; right; decide) (by right; right; decide) a mw 27 (by decide)) fun t ⟨et,kt,ot⟩ => ?_
  refine ⟨fun i hi => ?_,(Keeps.regs ku).trans ((kv.mono (by simp)).trans
    ((Keeps.regs kw).trans (kt.mono (by simp)))),?_⟩
  · have eE : word w.mem base (1504+8*i)=word s.mem base (1504+8*i) := by
      rw [kw.mem,ov.word (by omega_arith) (by have := hs.nowrap; omega_arith),ku.mem]
    obtain eB : word w.mem base (1288+8*i)=
        if d then word s.mem base (1288+8*i) else word s.mem base (1072+8*i) := by
      rw [kw.mem,ev i hi,ku.mem]
    rw [et i hi,eE,eB]
    dsimp only [a,d]
    by_cases ha : wordsVal s.mem base 1216 9=0 <;>
      by_cases hd : wordsVal s.mem base 1648 9=0 <;> simp [ha,hd]
  · have ov' : Outside base 1072 432 s.mem w.mem := by
      rw [kw.mem,←ku.mem]; exact ov.mono (by decide) (by decide)
    exact ov'.trans (ot.mono (by decide) (by decide))

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass
open VG.Proof.Mont.AArch64.P521Field

 theorem window_select_tail_novec : ∀i∈windowSelectTail,vdstOf i=none := by
  obtain h : windowSelectTail.all (fun i => vdstOf i==none)=true := by lit_decide
  simpa only [List.all_eq_true,beq_iff_eq] using h

 theorem window_select_values_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hsz : 1720≤size) :
    WP isa (.block windowSelectTail) s fun t =>
      (∀c<3,wordsVal t.mem base (1072+72*c) 9=
        if wordsVal s.mem base 1216 9=0 then wordsVal s.mem base (1504+72*c) 9
        else if wordsVal s.mem base 1648 9=0 then wordsVal s.mem base (1072+72*c) 9
        else wordsVal s.mem base (1288+72*c) 9) ∧
      KeepRegs [.x1,.x2,.x3,.x7,.x16] s t ∧ Outside base 1072 432 s.mem t.mem ∧ t.v=s.v := by
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec window_select_tail_novec
    (window_select_tail_ok hs hsz)) fun t ⟨⟨words,k,frame⟩,v⟩ => ?_
  refine ⟨fun c hc => ?_,k,frame,v⟩
  by_cases ha : wordsVal s.mem base 1216 9=0
  · simp only [ha,ite_true]
    apply VG.Proof.Weierstrass.AArch64.wordsVal_of_words₂
    intro j hj
    obtain e := words (9*c+j) (by omega_arith)
    simp only [ha,ite_true] at e
    rwa [show 1072+8*(9*c+j)=1072+72*c+8*j by omega_arith,
      show 1504+8*(9*c+j)=1504+72*c+8*j by omega_arith] at e
  · by_cases hd : wordsVal s.mem base 1648 9=0
    · simp only [ha,hd,ite_false,ite_true]
      apply VG.Proof.Weierstrass.AArch64.wordsVal_of_words₂
      intro j hj
      obtain e := words (9*c+j) (by omega_arith)
      simp only [ha,hd,ite_false,ite_true] at e
      rwa [show 1072+8*(9*c+j)=1072+72*c+8*j by omega_arith] at e
    · simp only [ha,hd,ite_false]
      apply VG.Proof.Weierstrass.AArch64.wordsVal_of_words₂
      intro j hj
      obtain e := words (9*c+j) (by omega_arith)
      simp only [ha,hd,ite_false] at e
      rwa [show 1072+8*(9*c+j)=1072+72*c+8*j by omega_arith,
        show 1288+8*(9*c+j)=1288+72*c+8*j by omega_arith] at e

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field

 theorem window_select_point_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hsz : 1720≤size)
    (ca : canonicalPoint s.mem base 1072) (cb : canonicalPoint s.mem base 1288)
    (ce : canonicalPoint s.mem base 1504) :
    WP isa (.block windowSelectTail) s fun t =>
      canonicalPoint t.mem base 1072 ∧
      ordinaryPoint t.mem base 1072=
        (if wordsVal s.mem base 1216 9=0 then ordinaryPoint s.mem base 1504
        else if wordsVal s.mem base 1648 9=0 then ordinaryPoint s.mem base 1072
        else ordinaryPoint s.mem base 1288) ∧
      KeepRegs [.x1,.x2,.x3,.x7,.x16] s t ∧ Outside base 1072 432 s.mem t.mem ∧ t.v=s.v := by
  refine WP.mono (window_select_values_ok hs hsz) fun t ⟨values,k,frame,v⟩ => ?_
  obtain x := values 0 (by decide)
  obtain y := values 1 (by decide)
  obtain z := values 2 (by decide)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.reduceMul,Nat.reduceAdd] at x y z
  refine ⟨?_,?_,k,frame,v⟩
  · change wordsVal t.mem base 1072 9<_ ∧ wordsVal t.mem base 1144 9<_ ∧ wordsVal t.mem base 1216 9<_
    rw [x,y,z]
    by_cases ha : wordsVal s.mem base 1216 9=0
    · simpa only [ha,ite_true,canonicalPoint,Nat.reduceAdd] using ce
    · by_cases hd : wordsVal s.mem base 1648 9=0
      · simpa only [ha,hd,ite_false,ite_true,canonicalPoint,Nat.reduceAdd] using ca
      · simpa only [ha,hd,ite_false,canonicalPoint,Nat.reduceAdd] using cb
  · by_cases ha : wordsVal s.mem base 1216 9=0 <;>
      by_cases hd : wordsVal s.mem base 1648 9=0 <;>
      simp only [ha,hd,ite_false,ite_true] at x y z ⊢ <;>
      simp only [ordinaryPoint,Nat.reduceAdd,x,y,z,hd]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native

 theorem window_tail_counter_source : outerBlock143.drop 364=[.subImm .x .x4 .x19 1] := by
  obtain h := drop_flatten_prefix outerBlock143Chunks 11 352 12
    (by rw [List.length_flatten]; lit_decide)
  rw [outerBlock143,h]
  decide

 theorem window_tail_source : outerBlock143=windowSelectTail++[.subImm .x .x4 .x19 1] := by
  rw [←window_select_tail_source,←window_tail_counter_source,List.take_append_drop]

 theorem window_tail_counter_ok (s : State) :
    WP isa (.block [.subImm .x .x4 .x19 1]) s fun t =>
      t.gpr .x4=s.gpr .x19-1#64 ∧ Keeps [.x4] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.reduceLT,ite_true,
    RegUpd.gpr_write_self,BitVec.setWidth_eq,Option.some.injEq,exists_eq_left']
  refine ⟨trivial,⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
    rfl,rfl,rfl,rfl⟩,rfl⟩

 theorem window_tail_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hsz : 1720≤size)
    (ca : canonicalPoint s.mem base 1072) (cb : canonicalPoint s.mem base 1288)
    (ce : canonicalPoint s.mem base 1504) :
    WP isa (.block outerBlock143) s fun t =>
      canonicalPoint t.mem base 1072 ∧
      ordinaryPoint t.mem base 1072=
        (if wordsVal s.mem base 1216 9=0 then ordinaryPoint s.mem base 1504
        else if wordsVal s.mem base 1648 9=0 then ordinaryPoint s.mem base 1072
        else ordinaryPoint s.mem base 1288) ∧
      KeepRegs [.x1,.x2,.x3,.x4,.x7,.x16] s t ∧ VG.Proof.Mont.Outside base 1072 432 s.mem t.mem ∧ t.v=s.v ∧
      t.gpr .x4=s.gpr .x19-1#64 := by
  rw [window_tail_source,WP.block_append_iff]
  refine WP.mono (window_select_point_ok hs hsz ca cb ce) fun u ⟨b,p,k,f,v⟩ => ?_
  refine WP.mono (window_tail_counter_ok u) fun t ⟨e4,kt,vt⟩ => ?_
  rw [k.gpr .x19 (by decide)] at e4
  refine ⟨?_,?_,(k.mono (by simp)).trans (Keeps.regs (kt.mono (by simp))),?_,vt.trans v,e4⟩
  · rw [kt.mem]; exact b
  · rw [kt.mem]; exact p
  · rw [kt.mem]; exact f

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass.AArch64


 theorem WindowMixedFrame.word {base : Addr} {m m' : Mem} (frame : WindowMixedFrame base m m') {d : Nat}
    (ha : d+8≤4080 ∨ 4512≤d) (hb : d+8≤1288 ∨ 1504≤d) (hd : d+8≤2^64) :
    word m' base d=word m base d := by
  exact (Mem.readW_congr fun i hi =>
    (frame _ (by rw [ofs_off base (by omega_arith)]; omega_arith)
      (by rw [ofs_off base (by omega_arith)]; omega_arith)).symm).symm

 theorem WindowMixedFrame.wordsVal {base : Addr} {m m' : Mem} (frame : WindowMixedFrame base m m') {d k : Nat}
    (ha : d+8*k≤4080 ∨ 4512≤d) (hb : d+8*k≤1288 ∨ 1504≤d) (hd : d+8*k≤2^64) :
    wordsVal m' base d k=wordsVal m base d k := by
  apply wordsVal_of_words₂
  intro j hj
  exact WindowMixedFrame.word frame (by omega_arith) (by omega_arith) (by omega_arith)

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field VG.Proof.Weierstrass
open VG.Impl.Weierstrass.AArch64.P521Native

 def windowAddValue (mem : Mem) (base : Addr) :=
  if wordsVal mem base 1216 9=0 then ordinaryPoint mem base 1504
  else if wordsVal mem base 1648 9=0 then ordinaryPoint mem base 1072
  else maddJF (ordinaryPoint mem base 1072).1 (ordinaryPoint mem base 1072).2.1
    (ordinaryPoint mem base 1072).2.2 (ordinaryPoint mem base 1504).1 (ordinaryPoint mem base 1504).2.1

 def windowCompleteAdd : Prog isa := .seq windowMixedStep (.block outerBlock143)

 theorem window_complete_add_ok {s : State} {W : Nat}
    (hs : Scr s (s.gpr .x0) W) (room : 4584≤W)
    (ca : canonicalPoint s.mem (s.gpr .x0) 1072) (ce : canonicalPoint s.mem (s.gpr .x0) 1504) :
    WP isa windowCompleteAdd s fun t =>
      canonicalPoint t.mem (s.gpr .x0) 1072 ∧ ordinaryPoint t.mem (s.gpr .x0) 1072=windowAddValue s.mem (s.gpr .x0) ∧
      WindowWorkFrame (s.gpr .x0) s.mem t.mem ∧ WindowStable s t ∧ t.gpr .x4=s.gpr .x19-1#64 := by
  rw [windowCompleteAdd,WP.seq_iff]
  refine WP.mono (window_mixed_step_ok hs (by omega_arith) ca ce) fun u ⟨bu,pu,fu,ku⟩ => ?_
  obtain hu := ku.scr hs
  have same (d : Nat) (hd : d+72≤1288 ∨ 1504≤d) (lo : d+72≤4080) :
      wordsVal u.mem (s.gpr .x0) d 9=wordsVal s.mem (s.gpr .x0) d 9 :=
    WindowMixedFrame.wordsVal fu (Or.inl lo) hd (by have h:=hs.nowrap; omega_arith)
  obtain ax := same 1072 (by decide) (by decide)
  obtain ay := same 1144 (by decide) (by decide)
  obtain az := same 1216 (by decide) (by decide)
  obtain ex := same 1504 (by decide) (by decide)
  obtain ey := same 1576 (by decide) (by decide)
  obtain ez := same 1648 (by decide) (by decide)
  obtain au : canonicalPoint u.mem (u.gpr .x0) 1072 := by
    rw [ku.base]; change wordsVal u.mem (s.gpr .x0) 1072 9<_ ∧ wordsVal u.mem (s.gpr .x0) 1144 9<_ ∧ wordsVal u.mem (s.gpr .x0) 1216 9<_
    rw [ax,ay,az]; exact ca
  obtain eu : canonicalPoint u.mem (u.gpr .x0) 1504 := by
    rw [ku.base]; change wordsVal u.mem (s.gpr .x0) 1504 9<_ ∧ wordsVal u.mem (s.gpr .x0) 1576 9<_ ∧ wordsVal u.mem (s.gpr .x0) 1648 9<_
    rw [ex,ey,ez]; exact ce
  obtain bU : canonicalPoint u.mem (u.gpr .x0) 1288 := by rw [ku.base]; exact bu
  refine WP.mono (window_tail_ok hu (by omega_arith) au bU eu) fun t ⟨bt,pt,kt,ft,vt,e4⟩ => ?_
  rw [ku.base] at bt pt ft
  rw [ku.gp .x19 (by decide) (by decide)] at e4
  obtain aa : ordinaryPoint u.mem (s.gpr .x0) 1072=ordinaryPoint s.mem (s.gpr .x0) 1072 := by
    simp only [ordinaryPoint,Nat.reduceAdd,ax,ay,az]
  obtain ee : ordinaryPoint u.mem (s.gpr .x0) 1504=ordinaryPoint s.mem (s.gpr .x0) 1504 := by
    simp only [ordinaryPoint,Nat.reduceAdd,ex,ey,ez]
  refine ⟨bt,?_,?_,?_,e4⟩
  · rw [az,ez,aa,ee,pu] at pt
    rw [pt]
    unfold windowAddValue windowMixedValue
    by_cases h : wordsVal s.mem (s.gpr .x0) 1216 9=0 <;> simp only [h,ite_true,ite_false]
    · rfl
  · intro x hx ht
    exact (ft x hx).trans (fu x (by omega_arith) (by omega_arith))
  · have fresh : ∀r∈preserved,r∉[Reg.x1,Reg.x2,Reg.x3,Reg.x4,Reg.x7,Reg.x16] := by decide
    exact ⟨(kt.gpr _ (by decide)).trans ku.base,kt.rd.trans ku.rd,kt.wr.trans ku.wr,kt.sp.trans ku.sp,
      fun r hr hn => (kt.gpr r (fresh r hr)).trans (ku.gp r hr hn),
      by rw [vt,ku.v29],by rw [vt,ku.v31]⟩

end VG.Proof.Weierstrass.AArch64.P521Native
