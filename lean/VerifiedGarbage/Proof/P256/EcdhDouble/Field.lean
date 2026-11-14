module

public import VerifiedGarbage.Impl.P256.EcdhDouble
public import VerifiedGarbage.Impl.P256.VerifySparse
public import VerifiedGarbage.Proof.P256.EcdhJac.State
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
import VerifiedGarbage.Proof.P256.EcdhDouble.LinearField
import VerifiedGarbage.Proof.P256.VerifySparse.Fprog
import VerifiedGarbage.Proof.P256.Linear.WeakAdd
public import VerifiedGarbage.Proof.P256.EcdhDouble.MacroField
public import VerifiedGarbage.Proof.P256.EcdhDouble.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
import VerifiedGarbage.Proof.Weierstrass.JacInplace
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall

/-! ### `P256.EcdhDouble.Raw`, which only this module used -/

section

/-! ### `P256.EcdhDouble.WeakField`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.P256.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open EcdhJac (C K M)

def weakMulCode : List Instr := Impl.P256.Linear.weakAdd 864 512 800 ++
  Impl.P256.VerifySparse.op (.mul 896 864 896)

theorem weakMul_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl)
    (h864 : Sl 864) (h896 : Sl 896) {base : Addr} {s : State} {V : List Nat} {E : Nat→Fin C.p}
    (hm : UnitMod C.p (2^256)) (hi : Inv M base 8192 C.p Sl V E s)
    (h512 : 512∈V) (h800 : 800∈V) (hv896 : 896∈V) (hn : 864∉V) :
    WP isa (.block weakMulCode) s fun t =>
      ProgKeep M base [864,896] s t ∧
      Inv M base 8192 C.p Sl (896::V) (Function.update E 896 ((E 512+E 800)*E 896)) t := by
  rw [weakMulCode,WP.block_append_iff]
  refine WP.mono (Linear.weakAdd_ok hi.scr (hi.lt 512 h512) (hi.lt 800 h800))
    fun u ⟨kr,ko,_,hv⟩ => ?_
  have ku : OpKeep M base 864 s u := linearKeep kr ko
  have iu := inv_keep_unused layout hi h864 hn ku
  have eu : toM C.p (2^256) (wordsVal u.mem base 864 4)=E 512+E 800 := by
    rw [←toM_mod,hv,toM_add]
    exact congrArg₂ (·+·) (hi.val 512 h512) (hi.val 800 h800)
  refine WP.mono (VerifySparse.mulOp_ok (M:=M) (m:=C.p) iu.scr rfl rfl iu.mod aligned.mod
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (iu.lt 896 hv896))
    fun t ⟨kt,hlt,he⟩ => ?_
  refine ⟨⟨fun r hr => (kt.gpr r hr).trans (ku.gpr r hr),kt.rd.trans ku.rd,
    kt.wr.trans ku.wr,kt.sp.trans ku.sp,fun x hx ht => ?_⟩,
    iu.update layout h896 kt hlt ?_⟩
  · rw [kt.mem x (hx 896 (by simp)) ht,ku.mem x (hx 864 (by simp)) ht]
  · change toM C.p (2^256) (wordsVal t.mem base 896 4)=_
    have ee := toM_mul hm he
    change toM C.p (2^256) (wordsVal t.mem base 896 4)=toM C.p (2^256) (wordsVal u.mem base 864 4)*toM C.p (2^256) (wordsVal u.mem base 896 4) at ee
    rw [ee,eu]
    exact congrArg ((E 512+E 800)*·) (iu.val 896 hv896)
end VG.Proof.P256.EcdhDouble

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open EcdhJac (C K M)

def ops1 : List FOp := [.mul 800 576 576,.mul 832 544 544,.sub 896 512 800]
def ops2 : List FOp := [.add 864 544 576,.mul 928 512 832,.mul 960 896 896,.mul 864 864 864]
def ops3 : List FOp := [.sub 864 864 800,.sub 576 864 832]
def ops4 : List FOp := [.mul 896 960 896,.mul 800 832 832]
def writes : List Nat := [512,544,576,800,832,864,896,928,960]
def result {F : Type _} [Lean.Grind.CommRing F] (E : Nat→F) : Nat→F :=
  let e := runOps ops1 E
  let e := Function.update e 896 ((e 512+e 800)*e 896)
  let e := runOps ops2 e
  let e := Function.update e 960 (12*e 928-9*e 960)
  let e := runOps ops3 e
  let e := Function.update e 512 (4*e 928-e 960)
  let e := runOps ops4 e
  Function.update e 544 (3*e 896-8*e 800)

theorem result_xyz {F : Type _} [Lean.Grind.CommRing F] (E : Nat→F) :
    (result E 512,result E 544,result E 576)=values (E 512) (E 544) (E 576) := by
  simp [result,ops1,ops2,ops3,ops4,runOps,FOp.run,values]

theorem opKeep_prog {base : Addr} {o : Nat} {s t : State} (hk : OpKeep M base o s t) :
    ProgKeep M base [o] s t :=
  ⟨hk.gpr,hk.rd,hk.wr,hk.sp,fun x hx ht => hk.mem x (hx o (by simp)) ht⟩

theorem prog_trans {base : Addr} {s t u : State} {W : List Nat}
    (h1 : ProgKeep M base W s t) (h2 : ProgKeep M base W t u) : ProgKeep M base W s u :=
  ⟨fun r hr => (h2.gpr r hr).trans (h1.gpr r hr),h2.rd.trans h1.rd,h2.wr.trans h1.wr,
   h2.sp.trans h1.sp,fun x hx ht => (h2.mem x hx ht).trans (h1.mem x hx ht)⟩

theorem result_unch {F : Type _} [Lean.Grind.CommRing F] (E : Nat→F) {x : Nat}
    (hx : x∉writes) : result E x=E x := by
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false,not_or] at hx
  simp [result,ops1,ops2,ops3,ops4,runOps,FOp.run,
    hx.1,hx.2.1,hx.2.2.1,hx.2.2.2.1,hx.2.2.2.2.1,hx.2.2.2.2.2.1,
    hx.2.2.2.2.2.2.1,hx.2.2.2.2.2.2.2.1,hx.2.2.2.2.2.2.2.2]

/-- The slots the field operations name lie among the doubling's writes. -/
theorem slots_of {Sl : Nat → Prop} (hw : ∀ x∈writes,Sl x) {ops : List FOp}
    (h : ∀ op∈ops,∀ x∈op.out::op.ins,x∈writes) : ∀ op∈ops,∀ x∈op.out::op.ins,Sl x :=
  fun op hop x hx => hw x (h op hop x hx)

/-- The raw doubling from the accumulator `R` alone: every written slot ends valid. -/
theorem rawR_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl)
    (hw : ∀ x∈writes,Sl x)
    (h129 : LinearCorrect (Impl.P256.Linear.linear129 960 928 960) 960 928 960 12 9)
    (h38 : LinearCorrect (Impl.P256.Linear.linear38 544 896 800) 544 896 800 3 8)
    (hm : UnitMod C.p (2^256)) {base : Addr} {s : State} {E : Nat→Fin C.p}
    (hi : Inv M base 8192 C.p Sl [512,544,576] E s) :
    WP isa (.block Impl.P256.EcdhDouble.raw) s fun t =>
      ProgKeep M base writes s t ∧ Inv M base 8192 C.p Sl writes (result E) t := by
  have cut : Impl.P256.EcdhDouble.raw = ops1.flatMap Impl.P256.VerifySparse.op ++ weakMulCode ++
    ops2.flatMap Impl.P256.VerifySparse.op ++ Impl.P256.Linear.linear129 960 928 960 ++
    ops3.flatMap Impl.P256.VerifySparse.op ++ Impl.P256.Linear.linear41 512 928 960 ++
    ops4.flatMap Impl.P256.VerifySparse.op ++ Impl.P256.Linear.linear38 544 896 800 := by
      simp only [Impl.P256.EcdhDouble.raw,ops1,ops2,ops3,ops4,weakMulCode,
        List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]
  have sw (x : Nat) (hx : x∈writes := by decide) : Sl x := hw x hx
  rw [cut]
  simp only [List.append_assoc]
  apply WP.block_append
  refine WP.mono (VerifySparse.fprog_ok (M:=M) (m:=C.p) rfl rfl layout aligned hm ops1 hi
    (slots_of hw (by decide +kernel)) (by decide +kernel)) fun s1 ⟨k1,i1⟩ => ?_
  apply WP.block_append
  refine WP.mono (weakMul_ok layout aligned (sw 864) (sw 896) hm i1 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun s2 ⟨k2,i2⟩ => ?_
  apply WP.block_append
  refine WP.mono (VerifySparse.fprog_ok (M:=M) (m:=C.p) rfl rfl layout aligned hm ops2 i2
    (slots_of hw (by decide +kernel)) (by decide +kernel)) fun s3 ⟨k3,i3⟩ => ?_
  apply WP.block_append
  refine WP.mono (linearField_ok layout h129 (sw 960) i3 (by decide +kernel) (by decide +kernel))
    fun s4 ⟨k4,i4⟩ => ?_
  apply WP.block_append
  refine WP.mono (VerifySparse.fprog_ok (M:=M) (m:=C.p) rfl rfl layout aligned hm ops3 i4
    (slots_of hw (by decide +kernel)) (by decide +kernel)) fun s5 ⟨k5,i5⟩ => ?_
  apply WP.block_append
  refine WP.mono (linear41Field_ok layout (sw 512) i5 (by decide +kernel) (by decide +kernel))
    fun s6 ⟨k6,i6⟩ => ?_
  apply WP.block_append
  refine WP.mono (VerifySparse.fprog_ok (M:=M) (m:=C.p) rfl rfl layout aligned hm ops4 i6
    (slots_of hw (by decide +kernel)) (by decide +kernel)) fun s7 ⟨k7,i7⟩ => ?_
  refine WP.mono (linearField_ok layout h38 (sw 544) i7 (by decide +kernel) (by decide +kernel))
    fun t ⟨k8,i8⟩ => ?_
  refine ⟨?_,?_⟩
  · exact prog_trans (prog_trans (prog_trans (prog_trans (prog_trans (prog_trans (prog_trans
      (k1.mono (by decide +kernel)) (k2.mono (by decide +kernel))) (k3.mono (by decide +kernel)))
      ((opKeep_prog k4).mono (by decide +kernel))) (k5.mono (by decide +kernel)))
      ((opKeep_prog k6).mono (by decide +kernel))) (k7.mono (by decide +kernel)))
      ((opKeep_prog k8).mono (by decide +kernel))
  · exact i8.sub (by decide +kernel)

/-- The raw doubling on any live slots holding `R`: it keeps those it does not write. -/
theorem raw_ok {Sl : Nat → Prop} (layout : Lay M 8192 Sl) (aligned : Aligned M Sl)
    (hw : ∀ x∈writes,Sl x)
    (h129 : LinearCorrect (Impl.P256.Linear.linear129 960 928 960) 960 928 960 12 9)
    (h38 : LinearCorrect (Impl.P256.Linear.linear38 544 896 800) 544 896 800 3 8)
    (hm : UnitMod C.p (2^256)) {live : List Nat} (hR : ∀ x∈[512,544,576],x∈live)
    {base : Addr} {s : State} {E : Nat→Fin C.p}
    (hi : Inv M base 8192 C.p Sl live E s) :
    WP isa (.block Impl.P256.EcdhDouble.raw) s fun t =>
      ProgKeep M base writes s t ∧ Inv M base 8192 C.p Sl live (result E) t := by
  refine WP.mono (rawR_ok layout aligned hw h129 h38 hm (hi.sub hR)) fun t ⟨hk,it⟩ => ⟨hk,?_⟩
  have keep (x : Nat) (hx : x∈live) (hn : x∉writes) :
      wordsVal t.mem base x M.n=wordsVal s.mem base x M.n := by
    have hb := layout.le x (hi.sl x hx)
    refine hk.unch.wordsVal (fun w hw' => ?_) (by omega_using [hb])
    simp only [List.mem_append,List.mem_map,List.mem_singleton] at hw'
    rcases hw' with ⟨y,hy,rfl⟩ | rfl
    · exact layout.apart x y (hi.sl x hx) (hw y hy) (fun he => hn (he ▸ hy))
    · exact layout.tmp x (hi.sl x hx)
  refine ⟨it.scr,it.mod,hi.sl,fun x hx => ?_,fun x hx => ?_⟩
  · by_cases hn : x∈writes
    · exact it.lt x hn
    · rw [keep x hx hn]; exact hi.lt x hx
  · by_cases hn : x∈writes
    · exact it.val x hn
    · rw [keep x hx hn,hi.val x hx,result_unch E hn]
end VG.Proof.P256.EcdhDouble

end

end


@[expose] public section

namespace VG.Proof.P256.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.P256.VerifyArithmetic Spec.Weierstrass
open EcdhJac (C K M Sl layout aligned live ro work)

/-- On any live slots holding `R` or untouched by the doubling, the raw result
is the doubling's field program. -/
theorem result_of {F : Type _} [Lean.Grind.CommRing F] (E : Nat→F) {live : List Nat}
    (h : ∀x∈live,x∈[512,544,576] ∨ (x∉writes ∧ ∀op∈operations .doubleRR,op.out≠x)) :
    ∀x∈live,result E x=runOps (operations .doubleRR) E x := by
  have e := (result_xyz E).trans (values_eq (E 512) (E 544) (E 576))
  have d := dblJMul_inplace_run (S:=K.S) (p:=K.R) (by decide +kernel) E
  change (runOps (operations .doubleRR) E 512,runOps (operations .doubleRR) E 544,
    runOps (operations .doubleRR) E 576)=dblJF (E 512) (E 544) (E 576) at d
  have ex := e.trans d.symm
  intro x hx
  rcases h x hx with hx|⟨hw,ho⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact congrArg Prod.fst ex
    · exact congrArg (fun p => p.2.1) ex
    · exact congrArg (fun p => p.2.2) ex
  · rw [result_unch E hw]
    symm
    exact runOps_of_not_out _ _ ho

theorem result_live {F : Type _} [Lean.Grind.CommRing F] (E : Nat→F) :
    ∀x∈live,result E x=runOps (operations .doubleRR) E x :=
  result_of E (by decide +kernel)

 theorem field_ok
    (h129 : LinearCorrect (Impl.P256.Linear.linear129 960 928 960) 960 928 960 12 9)
    (h38 : LinearCorrect (Impl.P256.Linear.linear38 544 896 800) 544 896 800 3 8)
    (hm : UnitMod C.p (2^256)) {base : Addr} {s : State} {E : Nat→Fe C}
    (hi : Inv M base 8192 C.p Sl live E s) :
    WP isa Impl.P256.EcdhDouble.program s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧
      Inv M base 8192 C.p Sl live (runOps (operations .doubleRR) E) t := by
  refine WP.mono (Certificate.refine hi.scr (raw_ok layout aligned (by decide +kernel) h129 h38 hm
    (by decide +kernel) hi))
    fun t ⟨u,⟨_,hu⟩,ho,hk⟩ => ?_
  have hs := hk.scr allocatedRegs_x0 hi.scr
  have ht := hi.mod.unch hk.unch
    (show ∀w∈VerifyAllocated.work,M.mo+8*M.n≤w.1 ∨ w.1+w.2≤M.mo by decide)
    hi.scr.nowrap
  refine ⟨hk.mono (fun _ h => h) (by decide +kernel),?_⟩
  apply (hu.congr_env (result_live E)).of_observed hs ht
  intro x hx i him
  apply ho (x+8*i) ((show ∀x∈live,∀i<4,Certificate.observe (x+8*i) by decide +kernel) x hx i him)
  · have ha := aligned.sl x (hu.sl x hx)
    omega_using [ha]
  · have hb := layout.le x (hu.sl x hx)
    change i<4 at him
    change x+32≤8192 at hb
    omega_using [him, hb]

 theorem double_ok
    (h129 : LinearCorrect (Impl.P256.Linear.linear129 960 928 960) 960 928 960 12 9)
    (h38 : LinearCorrect (Impl.P256.Linear.linear38 544 896 800) 544 896 800 3 8)
    (hm : UnitMod C.p (2^256)) (hC : Law C) (ha : AM3 C)
    {base : Addr} {E : Nat→Fe C} {s : State}
    (hi : Inv M base 8192 C.p Sl live E s) {P : Point C}
    (hp : onCurve C P=true) (hj : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) P) :
    WP isa Impl.P256.EcdhDouble.program s fun t =>
      AllocatedFrame allocatedRegs base work s t ∧ Inv M base 8192 C.p Sl live (runOps (operations .doubleRR) E) t ∧
      InvJ C (runOps (operations .doubleRR) E K.R.x) (runOps (operations .doubleRR) E K.R.y)
        (runOps (operations .doubleRR) E K.R.z) (add P P) := by
  exact WP.mono (field_ok h129 h38 hm hi) fun _ ⟨hk,it⟩ =>
    ⟨hk,it,InvJ.dbl' hC ha hp hj (dblJMul_inplace_run (by decide +kernel) E)⟩
end VG.Proof.P256.EcdhDouble
