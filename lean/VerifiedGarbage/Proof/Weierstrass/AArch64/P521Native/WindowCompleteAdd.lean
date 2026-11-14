module

-- separate module: this consolidated proof replays 1.05s of elaboration/kernel work versus 0.53s importing its dependencies (local Lean trace); retaining the boundary avoids replaying it in its sole importer.

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowMixedStep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowMixedCall
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
  have mu : u.gpr .x3=if d then BitVec.allOnes 64 else 0 := by
    rw [maskU]; dsimp only [d]
    by_cases h : wordsVal s.mem base 1648 9=0 <;> simp [h]
  have hu := hs.of_keeps ku (by decide)
  refine WP.mono (window_select_words hu (a:=1072) (b:=1288) (o:=1288) (n:=27)
    (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide)
    (by right; left; decide) (by left; rfl) d mu 27 (by decide)) fun v ⟨ev,kv,ov⟩ => ?_
  rw [WP.block_append_iff]
  have hv := hu.of_keepRegs kv (by decide)
  refine WP.mono (window_zero_ok hv (z:=1216) (by omega_arith) (by decide)) fun w ⟨maskW,kw⟩ => ?_
  let a : Bool := decide (wordsVal s.mem base 1216 9≠0)
  have vz : wordsVal v.mem base 1216 9=wordsVal s.mem base 1216 9 := by
    rw [ov.wordsVal (by omega_arith) (by have := hs.nowrap; omega_arith),ku.mem]
  have mw : w.gpr .x3=if a then BitVec.allOnes 64 else 0 := by
    rw [maskW,vz]; dsimp only [a]
    by_cases h : wordsVal s.mem base 1216 9=0 <;> simp [h]
  have hw := hv.of_keeps kw (by decide)
  refine WP.mono (window_select_words hw (a:=1504) (b:=1288) (o:=1072) (n:=27)
    (by omega_arith) (by omega_arith) (by omega_arith) (by decide) (by decide) (by decide)
    (by right; right; decide) (by right; right; decide) a mw 27 (by decide)) fun t ⟨et,kt,ot⟩ => ?_
  refine ⟨fun i hi => ?_,(Keeps.regs ku).trans ((kv.mono (by simp)).trans
    ((Keeps.regs kw).trans (kt.mono (by simp)))),?_⟩
  · have eE : word w.mem base (1504+8*i)=word s.mem base (1504+8*i) := by
      rw [kw.mem,ov.word (by omega_arith) (by have := hs.nowrap; omega_arith),ku.mem]
    have eB : word w.mem base (1288+8*i)=
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
  have h : windowSelectTail.all (fun i => vdstOf i==none)=true := by lit_decide
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
    have e := words (9*c+j) (by omega_arith)
    simp only [ha,ite_true] at e
    rwa [show 1072+8*(9*c+j)=1072+72*c+8*j by omega_arith,
      show 1504+8*(9*c+j)=1504+72*c+8*j by omega_arith] at e
  · by_cases hd : wordsVal s.mem base 1648 9=0
    · simp only [ha,hd,ite_false,ite_true]
      apply VG.Proof.Weierstrass.AArch64.wordsVal_of_words₂
      intro j hj
      have e := words (9*c+j) (by omega_arith)
      simp only [ha,hd,ite_false,ite_true] at e
      rwa [show 1072+8*(9*c+j)=1072+72*c+8*j by omega_arith] at e
    · simp only [ha,hd,ite_false]
      apply VG.Proof.Weierstrass.AArch64.wordsVal_of_words₂
      intro j hj
      have e := words (9*c+j) (by omega_arith)
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
  have x := values 0 (by decide)
  have y := values 1 (by decide)
  have z := values 2 (by decide)
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
  have h := drop_flatten_prefix outerBlock143Chunks 11 352 12
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
  have hu := ku.scr hs
  have same (d : Nat) (hd : d+72≤1288 ∨ 1504≤d) (lo : d+72≤4080) :
      wordsVal u.mem (s.gpr .x0) d 9=wordsVal s.mem (s.gpr .x0) d 9 :=
    WindowMixedFrame.wordsVal fu (Or.inl lo) hd (by have h:=hs.nowrap; omega_arith)
  have ax := same 1072 (by decide) (by decide)
  have ay := same 1144 (by decide) (by decide)
  have az := same 1216 (by decide) (by decide)
  have ex := same 1504 (by decide) (by decide)
  have ey := same 1576 (by decide) (by decide)
  have ez := same 1648 (by decide) (by decide)
  have au : canonicalPoint u.mem (u.gpr .x0) 1072 := by
    rw [ku.base]; change wordsVal u.mem (s.gpr .x0) 1072 9<_ ∧ wordsVal u.mem (s.gpr .x0) 1144 9<_ ∧ wordsVal u.mem (s.gpr .x0) 1216 9<_
    rw [ax,ay,az]; exact ca
  have eu : canonicalPoint u.mem (u.gpr .x0) 1504 := by
    rw [ku.base]; change wordsVal u.mem (s.gpr .x0) 1504 9<_ ∧ wordsVal u.mem (s.gpr .x0) 1576 9<_ ∧ wordsVal u.mem (s.gpr .x0) 1648 9<_
    rw [ex,ey,ez]; exact ce
  have bU : canonicalPoint u.mem (u.gpr .x0) 1288 := by rw [ku.base]; exact bu
  refine WP.mono (window_tail_ok hu (by omega_arith) au bU eu) fun t ⟨bt,pt,kt,ft,vt,e4⟩ => ?_
  rw [ku.base] at bt pt ft
  rw [ku.gp .x19 (by decide) (by decide)] at e4
  have aa : ordinaryPoint u.mem (s.gpr .x0) 1072=ordinaryPoint s.mem (s.gpr .x0) 1072 := by
    simp only [ordinaryPoint,Nat.reduceAdd,ax,ay,az]
  have ee : ordinaryPoint u.mem (s.gpr .x0) 1504=ordinaryPoint s.mem (s.gpr .x0) 1504 := by
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
