module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.CompactStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint.TableLayout
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.BrainpoolP512r1.Joint.Math

/-! The fifteen table additions share one bounded public loop. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64 VG.Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)
open VG.Impl.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint

theorem tableIncrement_ok (s : State) {d : Nat} (h19 : s.gpr .x19=BitVec.ofNat 64 d) :
    WP isa (.block [.addImm .x .x19 .x19 1,.subImm .x .x6 .x19 16]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (d+1) ∧
      t.gpr .x6=BitVec.ofNat 64 (d+1)-16 ∧ Keeps [.x19,.x6] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,
    show (1 : Nat)<4096 by decide,show (16 : Nat)<4096 by decide,
    ite_true,BitVec.setWidth_eq,RegUpd.gpr_write,reduceCtorEq,ite_false,h19,
    Option.some.injEq,exists_eq_left']
  have e : BitVec.ofNat 64 d+1=BitVec.ofNat 64 (d+1) := by
    change BitVec.ofNat 64 d+BitVec.ofNat 64 1=_
    rw [←BitVec.ofNat_add]
  refine ⟨e,congrArg (fun x : BitVec 64 => x-BitVec.ofNat 64 16) e,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  simp only [List.mem_cons,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem tableLoopStep_ok {base : Addr} {P Q : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    {d : Nat} (h1 : 1 ≤ d) (h15 : d ≤ 15) (hi : Inputs base P Q s)
    (ht : Table base P Q (d-1) s) (h19 : s.gpr .x19=BitVec.ofNat 64 d) :
    WP isa tableLoopStep s fun t =>
      Changes base arithmeticWork s t ∧ Inputs base P Q t ∧ Table base P Q d t ∧
      t.gpr .x19=BitVec.ofNat 64 (d+1) ∧ t.gpr .x6=BitVec.ofNat 64 (d+1)-16 := by
  rw [tableLoopStep]
  refine WP.seq (WP.mono (prepChoice_ok hc hC h1 h15 hi ht h19) fun a ⟨⟨W,I,R,E⟩,c⟩ => ?_)
  have hA : onCurve C (pair P Q ((previous d)%4) ((previous d)/4))=true := pair_curve hC hP hQ _ _
  have he : onCurve C (if d%4=0 then Q else P)=true := by split <;> with_reducible assumption
  refine WP.seq (WP.mono (sum_points hc hC I.scr I.mod I.a I.b I.a_lt I.b_lt he hA E R)
    fun b ⟨W',R',c'⟩ => ?_)
  have K := W.trans (W'.mono addWork_sub)
  have I' := hi.unch (K.mono loopWork_sub)
  have T : Table base P Q (d-1) b := fun j hj hjm => K.table hi.scr hj (by omega) (ht j hj hjm)
  rw [table_step hC hP hQ h1] at R'
  refine WP.seq (WP.mono (storeChoice_ok h1 h15 I' T R' (c'.trans (c.trans h19)))
    fun u ⟨⟨L,Iu,Tu⟩,cu⟩ => ?_)
  refine WP.mono (tableIncrement_ok u (cu.trans (c'.trans (c.trans h19)))) fun t ⟨ct,ft,kt⟩ => ?_
  have Z : Changes base arithmeticWork u t := Changes.of_keeps kt (by decide)
  exact ⟨((K.mono loopWork_sub).trans L).trans Z,Iu.unch Z,
    fun j hj hjd => (Tu j hj hjd).of_mem kt.mem,ct,ft⟩

theorem buildTable_ok {base : Addr} {P Q : Point C} {s : State}
    (hc : BaseCfgOk cfg) (hC : Law C) (hP : onCurve C P=true) (hQ : onCurve C Q=true)
    (hi : Inputs base P Q s) :
    WP isa buildTable s fun t =>
      Changes base arithmeticWork s t ∧ Inputs base P Q t ∧ Table base P Q 15 t := by
  rw [buildTable]
  refine WP.seq (WP.mono (setCounter_ok s (j:=1) (by decide)) fun a ⟨ca,ka⟩ => ?_)
  have Wa : Changes base arithmeticWork s a := Changes.of_keeps ka (by decide)
  let Inv := fun j t => Changes base arithmeticWork s t ∧ Inputs base P Q t ∧
    Table base P Q (15-j) t ∧ t.gpr .x19=BitVec.ofNat 64 (16-j)
  refine WP.loop (M:=isa) (fun j t => 1 ≤ j ∧ j ≤ 15 ∧ Inv j t)
    (fun j t ⟨h1,h15,ht⟩ => ?_) 15 a ⟨by decide,by decide,Wa,hi.unch Wa,?_,ca⟩
  · obtain ⟨W,I,T,c⟩ := ht
    have T' : Table base P Q ((16-j)-1) t := by simpa only [show 16-j-1=15-j by omega] using T
    refine WP.mono (tableLoopStep_ok hc hC hP hQ (by omega) (by omega) I T' c)
      fun u ⟨L,Iu,Tu,cu,fu⟩ => ?_
    by_cases e : j=1
    · subst j
      refine Or.inl ⟨?_,W.trans L,Iu,Tu⟩
      change some (u.read .x .x6 != 0)=some false
      rw [read_x,fu]; rfl
    · refine Or.inr ⟨?_,j-1,by omega,by omega,by omega,W.trans L,Iu,?_,?_⟩
      · change some (u.read .x .x6 != 0)=some true
        rw [read_x,fu]
        apply congrArg some
        rw [bne_iff_ne]
        intro hz
        have hh := congrArg BitVec.toNat hz
        rw [BitVec.toNat_sub,BitVec.toNat_ofNat] at hh
        change (2^64-16+((16-j+1)%(2^64)))%(2^64)=0 at hh
        rw [Nat.mod_eq_of_lt (by omega : 16-j+1 < 2^64)] at hh
        omega
      · simpa only [show 15-(j-1)=16-j by omega] using Tu
      · simpa only [show 16-(j-1)=16-j+1 by omega] using cu
  · intro j hj h0; omega
end VG.Proof.Ecdsa.Verify.AArch64.BrainpoolP256r1.Joint
