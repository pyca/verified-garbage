module

-- separate module: The complete mixedFn entry/exit, vector, and ABI replay (mixedFn_partition) costs 1.78s of proof versus 0.38s of imports; WindowMixedCall composition edits reuse this checked computation.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedBody
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MixedFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.Proof.Mont
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off Outside.of_off)

theorem mixed_stable_z {base : Addr} {scratch out : Nat} {original m : Mem}
    (apart : scratch+432≤out ∨ out+144≤scratch+360)
    (scratchFits : scratch+432≤2^64) (outFits : out+144<2^64)
    (frame : Outside (off base out) 0 144 original m) :
    wordsVal m (off base scratch) 360 9=wordsVal original (off base scratch) 360 9 := by
  have h := Outside.of_off frame outFits
  have v := h.wordsVal (d:=scratch+360) (k:=9) (by omega_arith) (by omega_arith)
  simpa only [wordsVal_off] using v

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime lane)
open VG.Proof.Weierstrass.AArch64.Mont (wordsVal_off)
open VG.Proof.Weierstrass (maddJF)

private theorem mixed_ops_input {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) (i : Nat) (hi : i<5) :
    pointRun mixedOps E i=E i := by
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega_arith
  rcases hc with rfl|rfl|rfl|rfl|rfl <;> rfl

private theorem select_canonical_point {p : Nat} [NeZero p] {zero : Prop} [Decidable zero]
    {x y z ax ay cx cy cz : Nat} {A B : Fin p} {P : Fin p × Fin p × Fin p}
    (large : 1<p) (hx : x=(if zero then ax else cx)) (hy : y=(if zero then ay else cy))
    (hz : z=(if zero then 1 else cz)) (bax : ax<p) (bay : ay<p) (bcx : cx<p) (bcy : cy<p) (bcz : cz<p)
    (eax : Fin.ofNat p ax=A) (eay : Fin.ofNat p ay=B)
    (ec : (Fin.ofNat p cx,Fin.ofNat p cy,Fin.ofNat p cz)=P) :
    x<p ∧ y<p ∧ z<p ∧ (Fin.ofNat p x,Fin.ofNat p y,Fin.ofNat p z)=(if zero then (A,B,1) else P) := by
  by_cases h : zero
  · simp only [h,ite_true] at hx hy hz ⊢
    rw [hx,hy,hz]
    exact ⟨bax,bay,large,by rw [eax,eay]; rfl⟩
  · simp only [h,ite_false] at hx hy hz ⊢
    rw [hx,hy,hz]
    exact ⟨bcx,bcy,bcz,ec⟩

private theorem field_prime_large : 1<fieldPrime := by
  simpa only [fieldPrime,VG.Proof.Mont.AArch64.P521Square.prime_value] using
    (by decide : 1<6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151)

theorem mixedFn_partition : mixedFnBlocks.flatten=(mixedFnBlocks.flatten.take 16)++
    (mixedArithmeticCode++mixedFinishCode) := by lit_decide

theorem mixedFn_keepsV : mixedFn.allInstrs keepsV=true := by lit_decide

theorem mixed_fn_core [NeZero fieldPrime] {s : State} {W a b o : Nat} {E : Nat → Fin fieldPrime}
    (hs : Scr s (s.gpr .x0) W) (hW : 4512≤W) (layout : MixedLayoutState a b) (outputLow : o+216≤4080)
    (argO : s.gpr .x1=BitVec.ofNat 64 o) (argA : s.gpr .x2=BitVec.ofNat 64 a)
    (argB : s.gpr .x3=BitVec.ofNat 64 b)
    (inv : OrdinaryInv (s.gpr .x0) fieldPrime (mixedSlot a b) [0,1,2,3,4] E (fun _ => 1) s) :
    WP isa mixedFn s fun t =>
      GprAbi s t ∧
      (wordsVal t.mem (s.gpr .x0) o 9<fieldPrime ∧
      wordsVal t.mem (s.gpr .x0) (o+72) 9<fieldPrime ∧ wordsVal t.mem (s.gpr .x0) (o+144) 9<fieldPrime ∧
      (Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) o 9),
        Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) (o+72) 9),
        Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) (o+144) 9))=
        (if wordsVal s.mem (s.gpr .x0) (a+144) 9=0 then (E 3,E 4,1) else maddJF (E 0) (E 1) (E 2) (E 3) (E 4)) ∧
      (∀x,(ofs (s.gpr .x0) x<4080 ∨ 4512≤ofs (s.gpr .x0) x) →
        (ofs (s.gpr .x0) x<o ∨ o+216≤ofs (s.gpr .x0) x) → t.mem x=s.mem x) ∧
      t.gpr .x0=s.gpr .x0 ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.v .v31=s.v .v31) := by
  let base := s.gpr .x0
  rw [mixedFn,mixedFn_partition,WP.block_append_iff]
  refine WP.mono (mixed_entry_ok s) fun u ⟨go,ga,gb,gt,workspace,link,saved,ku,v31⟩ => ?_
  have go' : u.gpr .x26=off base o := by rw [go,argO]
  have ga' : u.gpr .x27=off base a := by rw [ga,argA]
  have gb' : u.gpr .x28=off base b := by rw [gb,argB]
  have ctx : MixedContext base a b o u :=
    ⟨workspace_ptr hs (by have h:=layout.inputLow; omega_arith) ga' ku.rd ku.wr,
      workspace_ptr hs (by have h:=layout.affineLow; omega_arith) gb' ku.rd ku.wr,
      workspace_ptr hs (by omega_arith) gt ku.rd ku.wr,
      workspace_ptrW hs (by omega_arith) (by decide) gt ku.wr,
      workspace_ptrW hs (by omega_arith) (by decide) go' ku.wr,layout.inputLow,layout.affineLow⟩
  have iu : OrdinaryInv base fieldPrime (mixedSlot a b) [0,1,2,3,4] E (fun _ => 1) u := by
    constructor
    · intro i hi; rw [ku.mem]; exact inv.bound i hi
    · intro i hi; rw [ku.mem]; exact inv.value i hi
  rw [WP.block_append_iff]
  refine WP.mono (mixed_body_ok ctx layout iu) fun w ⟨iw,cw,_,_,kw,ow,vw⟩ => ?_
  have zp := ow.wordsVal (d:=a+144) (k:=9) (Or.inl (by have h:=layout.inputLow; omega_arith))
    (by have h:=layout.inputLow; omega_arith)
  rw [ku.mem] at zp
  have hstable : ∀m,Outside (off base o) 0 144 w.mem m →
      wordsVal m (off base 4080) 360 9=wordsVal w.mem (off base 4080) 360 9 := by
    intro m hm
    exact mixed_stable_z (Or.inr (by omega_arith)) (by decide) (by omega_arith) hm
  refine WP.mono (mixed_finish_ok (caller:=s) cw.input cw.temp cw.affine cw.output (by decide) (by decide) (by decide) (by decide)
    hstable (by rw [vw]; exact workspace) (by rw [vw]; exact link)
    (by intro i hi; rw [vw]; exact saved i hi)) fun t ⟨x,y,z,baseReset,lr,restored,kt,ot,vt⟩ => ?_
  simp only [wordsVal_off,Nat.add_zero] at x y z
  rw [zp] at x y z
  have ba := iw.bound 3 (by decide)
  have bb := iw.bound 4 (by decide)
  have bx := iw.bound 5 (by decide)
  have by' := iw.bound 9 (by decide)
  have bz := iw.bound 10 (by decide)
  simp only [Nat.one_mul] at ba bb bx by' bz
  have fa := iw.value 3 (by decide)
  have fb := iw.value 4 (by decide)
  have fx := iw.value 5 (by decide)
  have fy := iw.value 9 (by decide)
  have fz := iw.value 10 (by decide)
  rw [mixed_ops_input E 3 (by decide)] at fa
  rw [mixed_ops_input E 4 (by decide)] at fb
  change wordsVal w.mem base (b+0) 9<fieldPrime at ba
  change wordsVal w.mem base (b+72) 9<fieldPrime at bb
  change wordsVal w.mem base (4080+0) 9<fieldPrime at bx
  change wordsVal w.mem base (4080+288) 9<fieldPrime at by'
  change wordsVal w.mem base (4080+360) 9<fieldPrime at bz
  change Fin.ofNat fieldPrime (wordsVal w.mem base (b+0) 9)=E 3 at fa
  change Fin.ofNat fieldPrime (wordsVal w.mem base (b+72) 9)=E 4 at fb
  change Fin.ofNat fieldPrime (wordsVal w.mem base (4080+0) 9)=pointRun mixedOps E 5 at fx
  change Fin.ofNat fieldPrime (wordsVal w.mem base (4080+288) 9)=pointRun mixedOps E 9 at fy
  change Fin.ofNat fieldPrime (wordsVal w.mem base (4080+360) 9)=pointRun mixedOps E 10 at fz
  have results := select_canonical_point (p:=fieldPrime) (zero:=wordsVal s.mem base (a+144) 9=0)
    (A:=E 3) (B:=E 4) (P:=maddJF (E 0) (E 1) (E 2) (E 3) (E 4)) field_prime_large x y z ba bb bx by' bz fa fb
    (by rw [fx,fy,fz]; exact mixedOps_value E)
  have keepEntry : KeepRegs mixedFinishClob s w :=
    ((Keeps.regs ku).mono (by decide)).trans (kw.mono (by decide))
  have keepAll : KeepRegs mixedFinishClob s t := keepEntry.trans kt
  have os : Outside base o 216 w.mem t.mem := outside_rebase ot (by omega_arith)
  refine ⟨⟨?_,keepAll.sp⟩,results.1,results.2.1,results.2.2.1,results.2.2.2,?_,baseReset,keepAll.rd,keepAll.wr,?_⟩
  · intro r hr
    have hp : preserved=nativeSaved++[.x30] := by decide
    rw [hp,List.mem_append] at hr
    rcases hr with hr|hr
    · exact restored r hr
    · have he : r=.x30 := List.mem_singleton.mp hr
      subst r; exact lr
  · intro q htmp hout
    rw [os q hout,ow q htmp,ku.mem]
  · rw [vt,vw,v31]

theorem mixed_fn_ok [NeZero fieldPrime] {s : State} {W a b o : Nat} {E : Nat → Fin fieldPrime}
    (hs : Scr s (s.gpr .x0) W) (hW : 4512≤W) (layout : MixedLayoutState a b) (outputLow : o+216≤4080)
    (argO : s.gpr .x1=BitVec.ofNat 64 o) (argA : s.gpr .x2=BitVec.ofNat 64 a)
    (argB : s.gpr .x3=BitVec.ofNat 64 b)
    (inv : OrdinaryInv (s.gpr .x0) fieldPrime (mixedSlot a b) [0,1,2,3,4] E (fun _ => 1) s) :
    WP isa mixedFn s fun t =>
      abiPreserved s t ∧
      (wordsVal t.mem (s.gpr .x0) o 9<fieldPrime ∧
      wordsVal t.mem (s.gpr .x0) (o+72) 9<fieldPrime ∧ wordsVal t.mem (s.gpr .x0) (o+144) 9<fieldPrime ∧
      (Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) o 9),
        Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) (o+72) 9),
        Fin.ofNat fieldPrime (wordsVal t.mem (s.gpr .x0) (o+144) 9))=
        (if wordsVal s.mem (s.gpr .x0) (a+144) 9=0 then (E 3,E 4,1) else maddJF (E 0) (E 1) (E 2) (E 3) (E 4)) ∧
      (∀x,(ofs (s.gpr .x0) x<4080 ∨ 4512≤ofs (s.gpr .x0) x) →
        (ofs (s.gpr .x0) x<o ∨ o+216≤ofs (s.gpr .x0) x) → t.mem x=s.mem x) ∧
      t.gpr .x0=s.gpr .x0 ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.v .v31=s.v .v31) := by
  exact WP.withPreservedV (mixed_fn_core hs hW layout outputLow argO argA argB inv) mixedFn_keepsV

end VG.Proof.Mont.AArch64.P521Field
