import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.TableState
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointCopy
import VerifiedGarbage.Proof.Weierstrass.X86_64.PointMask
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacZero

/-! Initialize the first table entry with the affine peer and two cached ones. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps)
open Spec.Weierstrass

theorem table_initCounter_ok (s : State) :
    WP isa (.block [.mov32 .rbx (.imm 2)]) s fun t => t.gpr .rbx=2 ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,readSrc32,State.setReg32,
    Option.map_some,RegUpd.gpr_setReg,ite_true,Option.some.injEq,exists_eq_left']
  exact ⟨rfl,fun r hr => by
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg,hr,ite_false],rfl,rfl,rfl⟩

theorem table_init_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : SecretLay K size) (hOne : K.one<C.p)
    (hOneVal : toM C.p (2^(64*K.M.n)) K.one=1)
    {P : Point C} {s : State} {E : Nat → Fe C}
    (hI : Inv K.M base size C.p (·∈slots K) (winRo K) E s)
    (hJ : InvJ C (E K.P.x) (E K.P.y) (E K.P.z) P) (hAff : E K.P.z=1) :
    WP isa (.block (copyPt 4 (Impl.Ecdh.X86_64.Window5.tablePt K 1) K.P ++
      setConst 4 ((Impl.Ecdh.X86_64.Window5.tablePt K 1).x+96) K.one ++
      setConst 4 ((Impl.Ecdh.X86_64.Window5.tablePt K 1).x+128) K.one ++
      ([.mov32 .rbx (.imm 2)] : List Instr))) s fun t => TableInv K C base size P s t 1 := by
  let o := Impl.Ecdh.X86_64.Window5.tablePt K 1
  have oe : o=⟨K.tbl,K.tbl+32,K.tbl+64⟩ := rfl
  have pr : ∀ x∈jacCoords K.P,x∈winRo K := by
    intro x hx
    simp only [jacCoords,winRo,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  have tw : ∀ i<5,K.tbl+32*i∈writes K := fun i hi =>
    List.mem_append_right _ (by simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using (table_mem K (a:=1) (m:=16) (by decide) (by decide) hi))
  have ts : ∀ i<5,K.tbl+32*i∈slots K := fun i hi =>
    List.mem_append_right _ (by simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using (table_mem K (a:=1) (m:=16) (by decide) (by decide) hi))
  have od : ∀ x∈jacCoords o,x∈slots K := by
    intro x hx
    rw [oe] at hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact ts 0 (by decide)
    · exact ts 1 (by decide)
    · exact ts 2 (by decide)
  have ow : ∀ x∈jacCoords o,x∈writes K := by
    intro x hx
    rw [oe] at hx
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl
    · exact tw 0 (by decide)
    · exact tw 1 (by decide)
    · exact tw 2 (by decide)
  have oa : ∀ x∈jacCoords K.P,∀ y∈jacCoords o,x≠y := by
    intro x hx y hy
    have hs := hL.tbl x (List.mem_append_left _ (pr x hx))
    rw [oe] at hy
    simp only [jacCoords,List.mem_cons,List.not_mem_nil,or_false] at hy
    omega
  have hR := wordsVal_lt s.mem base K.M.mo K.M.n
  rw [hI.mod.val] at hR
  change WP isa (.block (copyPt 4 o K.P++setConst 4 (o.x+96) K.one++
    setConst 4 (o.x+128) K.one++([.mov32 .rbx (.imm 2)] : List Instr))) s _
  rw [List.append_assoc,List.append_assoc,WP.block_append_iff,←hL.n]
  refine WP.mono (copyPointTransfer_ok hL.lay hI (by rw [oe]) (by rw [oe]) od pr oa)
    fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setField_ok hL.lay ia (ts 3 (by decide)) hOne hR) fun b ⟨kb,ib⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setField_ok hL.lay ib (ts 4 (by decide)) hOne hR) fun c ⟨kc,ic⟩ => ?_
  refine WP.mono (table_initCounter_ok c) fun t ⟨ct,kt⟩ => ?_
  let F := Function.update (Function.update (pointTransferEnv E o K.P) (K.tbl+96) (1 : Fe C))
    (K.tbl+128) 1
  have it : Inv K.M base size C.p (·∈slots K)
      ((K.tbl+128)::(K.tbl+96)::(jacCoords o++winRo K)) F t := by
    simpa only [hOneVal,F,oe] using ic.of_keeps kt (by decide)
  have fr : ∀ x∈winRo K,F x=E x := by
    intro x hx
    have hs := hL.tbl x (List.mem_append_left _ hx)
    simp (disch := omega) only [F,pointTransferEnv,oe,Function.update_of_ne,ite_eq_right]
  have fv : (F K.tbl,F (K.tbl+32),F (K.tbl+64))=(E K.P.x,E K.P.y,E K.P.z) := by
    simp [F,pointTransferEnv,oe]
  have f2 : F (K.tbl+96)=1 := by simp [F]
  have f3 : F (K.tbl+128)=1 := by simp [F]
  have jm : InvJ C (F K.tbl) (F (K.tbl+32)) (F (K.tbl+64)) P := by
    simp only [Prod.mk.injEq] at fv
    rw [fv.1,fv.2.1,fv.2.2]
    exact hJ
  have pz : F K.P.z=1 := (fr _ (by simp [winRo])).trans hAff
  have jz : F (K.tbl+64)=1 := by
    simp only [Prod.mk.injEq] at fv
    exact fv.2.2.trans hAff
  have jm' : InvJ C (tmv C K.M.n base t K.tbl) (tmv C K.M.n base t (K.tbl+32))
      (tmv C K.M.n base t (K.tbl+64)) P :=
    it.point_tmv (p:=⟨K.tbl,K.tbl+32,K.tbl+64⟩) (by simp [jacCoords,oe]) jm
  have tv : ∀ x∈((K.tbl+128)::(K.tbl+96)::(jacCoords o++winRo K)),tmv C K.M.n base t x=F x :=
    fun x hx => it.val x hx
  refine ⟨it.to_tmv.sub ?_,?_,?_,?_,?_,ct,?_⟩
  · intro x hx
    simp only [tableLive,tableSlots,consecutiveFields,List.range_succ,List.range_zero,
      List.map_append,List.map_cons,List.map_nil,List.nil_append,oe,jacCoords,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    grind
  · apply it.point_tmv (p:=K.P) (fun x hx => by simp only [List.mem_cons,List.mem_append]; exact Or.inr (Or.inr (Or.inr (pr x hx))))
    rw [fr _ (by simp [winRo]),fr _ (by simp [winRo]),fr _ (by simp [winRo])]
    exact hJ
  · rw [tv _ (by simp [winRo]),pz]
  · intro a ha ha1
    obtain rfl : a=1 := by omega
    simpa only [Impl.Ecdh.X86_64.Window5.tablePt,Nat.sub_self,Nat.mul_zero,Nat.add_zero,mul_one_pt] using jm'
  · intro a ha ha1
    obtain rfl : a=1 := by omega
    dsimp only [Impl.Ecdh.X86_64.Window5.tablePt]
    simp only [Nat.sub_self,Nat.mul_zero,Nat.add_zero]
    rw [tv _ (by simp),tv _ (by simp [jacCoords,oe]),tv _ (by simp),f2,f3,jz]
    exact ⟨(Lean.Grind.Semiring.mul_one _).symm,(Lean.Grind.Semiring.mul_one _).symm⟩
  · exact ((CounterKeep.of_progKeep ka).mono ow).trans
      ((CounterKeep.of_progKeep (progKeep_of_op kb (tw 3 (by decide)))).trans
      ((CounterKeep.of_progKeep (progKeep_of_op kc (tw 4 (by decide)))).trans (.of_keeps kt)))

end VG.Proof.Ecdh.X86_64.Secret
