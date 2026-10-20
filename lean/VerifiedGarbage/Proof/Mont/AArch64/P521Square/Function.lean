module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Saves
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionMath
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The P-521 square as an alias-safe leaf function with caller-state restoration. -/

set_option exponentiation.threshold 1024

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Square
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Square
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)
open VG.Proof.Weierstrass.AArch64.Mont (Pre arg own Kept zext_ok off_off wordsVal_off Outside.of_off)

/-- Pointer setup reads both offsets before loading the input. -/
def pointers : List Instr := [.add .x .x30 .x0 .x1,.add .x .x1 .x0 .x2]
def park : List Instr := [.vop (.dup .d2 .v22 .x30),.movz .x .x30 0 0]
def unpark : List Instr := [.umov .x .x30 .v22 0]

theorem pointers_ok (s : State) :
    WP isa (.block pointers) s fun t =>
      t.gpr .x30 = s.gpr .x0+s.gpr .x1 ∧ t.gpr .x1 = s.gpr .x0+s.gpr .x2 ∧
      Keeps [.x30,.x1] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [pointers,runBlock_cons,runStep_some,runBlock_nil,exec,VG.Proof.Ed25519.AArch64.read_x,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,rfl,rfl,rfl,rfl⟩,rfl⟩
  · simp only [RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true]
  · simp only [RegUpd.gpr_write,BitVec.setWidth_eq,reduceCtorEq,ite_false,ite_true]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem park_ok (s : State) :
    WP isa (.block park) s fun t =>
      t.gpr .x30=0 ∧ (t.v .v22).extractLsb' 0 64=s.gpr .x30 ∧
      Keeps [.x30] s t ∧ (∀ d, d≠.v22 → t.v d=s.v d) := by
  apply WP.of_runBlock
  simp only [park,runBlock_cons,exec,VOp.eval,Option.map_some,show 16*0<Size.x.bits by decide,
    ite_true,runStep_some,runBlock_nil,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,?_,⟨?_,rfl,rfl,rfl,rfl⟩,?_⟩
  · change vdword (ofVDwords (s.gpr .x30) (s.gpr .x30)) 0=_
    exact vdword_ofVDwords_0 _ _
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false,RegUpd.gpr_setV]
  · intro d hd
    simp only [RegUpd.v_write,RegUpd.v_setV,hd,ite_false]

theorem unpark_ok (s : State) :
    WP isa (.block unpark) s fun t =>
      t.gpr .x30=(s.v .v22).extractLsb' 0 64 ∧ Keeps [.x30] s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [unpark,runBlock_cons,VG.Proof.Weierstrass.AArch64.Mont.exec_umov (s := s) (d := .x30) (n := .v22) (i := 0) (by decide),
    runStep_some,runBlock_nil,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,rfl,rfl,rfl,rfl⟩,rfl⟩
  · simp only [RegUpd.gpr_write_self,BitVec.setWidth_eq,Nat.mul_zero]
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write,hr,ite_false]

abbrev coreClob : List Reg := [.x30,.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28]
abbrev fnClob : List Reg := .x30::coreClob

theorem core_ok (s : State) (hz : s.gpr .x30=0) (ha : regsVal s aRegs<fieldPrime) :
    WP isa (.block core) s fun t =>
      regsVal t (uRegs.take 9)<fieldPrime ∧
      regsVal t (uRegs.take 9)*montBase%fieldPrime=regsVal s aRegs*regsVal s aRegs%fieldPrime ∧
      Keeps coreClob s t ∧ t.v=s.v := by
  have hb : WP isa (.block core) s fun t =>
      regsVal t (uRegs.take 9)<fieldPrime ∧
      regsVal t (uRegs.take 9)*montBase%fieldPrime=regsVal s aRegs*regsVal s aRegs%fieldPrime ∧
      Keeps coreClob s t := by
    rw [core,List.append_assoc,List.append_assoc,WP.block_append_iff]
    refine WP.mono (product_ok s hz ha) fun s₁ ⟨h₁,k₁⟩ => ?_
    have z₁ : s₁.gpr .x30=0 := (k₁.gpr .x30 (by decide)).trans hz
    have h₁b : regsVal s₁ uRegs<fieldPrime*fieldPrime := by
      rw [h₁]
      exact Nat.mul_lt_mul'' ha ha
    refine WP.mono (reduction_ok s₁ z₁ h₁b) fun t ⟨h₂,c₂,k₂⟩ => ?_
    exact ⟨h₂,by rw [c₂,h₁],(k₁.mono (by decide)).trans (k₂.mono (by decide))⟩
  exact WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by
    simp only [core,product,List.mem_append,or_imp,forall_and]
    repeat' constructor
    all_goals decide) hb)
    (fun _ ⟨⟨h,c,k⟩,v⟩ => ⟨h,c,k,v⟩)

theorem square_wp {s : State} {Q : State → Prop} : WP isa square s Q ↔
    WP isa (.block (([.addImm .w .x1 .x1 0,.addImm .w .x2 .x2 0,.addImm .w .x3 .x3 0] : List Instr) ++
      (saves ++ (pointers ++ (loadsR .x1 aRegs 0 ++ (park ++
      (core ++ (unpark ++ (storesR .x30 (uRegs.take 9) 0 ++ restores))))))))) s Q := by
  rw [square,WP.seq_iff,←WP.block_append_iff]
  simp only [entry,exit,pointers,park,unpark,List.append_assoc]

/-- The leaf square preserves the ABI and changes only the output bytes. -/
theorem square_fn_ok {s : State} {W : Nat} (hp : Pre 9 W s)
    (ha : wordsVal s.mem (s.gpr .x0) (arg s .x2) 9 < fieldPrime) :
    WP isa square s fun t =>
      abiPreserved s t ∧ Kept 9 (s.gpr .x0) (arg s .x1) s.mem t.mem ∧
      (wordsVal t.mem (s.gpr .x0) (arg s .x1) 9 < fieldPrime ∧
      wordsVal t.mem (s.gpr .x0) (arg s .x1) 9 * montBase % fieldPrime =
        wordsVal s.mem (s.gpr .x0) (arg s .x2) 9 * wordsVal s.mem (s.gpr .x0) (arg s .x2) 9 % fieldPrime) ∧
      t.gpr .x0=s.gpr .x0 ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.v .v29=s.v .v29 := by
  let base := s.gpr .x0
  let pa := off base (arg s .x2)
  let po := off base (arg s .x1)
  have hW : 4024≤W := hp.w
  have hW8 := hp.w8
  have ho : arg s .x1+72≤3520 := hp.o
  have haoff : arg s .x2+72≤3520 := hp.a
  rw [square_wp,WP.block_append_iff]
  refine WP.mono (zext_ok s) fun s₁ ⟨g₁,g₂,g₃,k₁,v₁⟩ => ?_
  rw [WP.block_append_iff,saves_eq]
  refine WP.mono (saves_ok saved 0 (s:=s₁) (by decide)) fun s₂ ⟨k₂,l₂,_,v₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointers_ok s₂) fun s₃ ⟨go,ga,k₃,v₃⟩ => ?_
  have x0₃ : s₃.gpr .x0=base := by rw [k₃.gpr _ (by decide),k₂.gpr,k₁.gpr _ (by decide)]
  have hs₃ : Scr s₃ base W := ⟨x0₃,by rw [k₃.wr,k₂.wr,k₁.wr,hp.wr]; simp [base],hp.fit,by omega⟩
  have gpa : s₃.gpr .x1=pa := by rw [ga,k₂.gpr,g₂,k₁.gpr _ (by decide)]
  have hpa : Ptr s₃ .x1 pa 72 := by
    refine ⟨gpa,fun d hd => ?_,by decide⟩
    change InRegions _ (off pa d) 8
    dsimp only [pa]
    rw [off_off]
    have h := hs₃.ld (d:=arg s .x2+d) (by omega)
    rwa [x0₃] at h
  have hmem₃ : s₃.mem=s.mem := k₃.mem.trans (k₂.mem.trans k₁.mem)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (loadsR_ok aRegs hpa (a:=0) (by decide) (by decide) (by decide) (by decide)))
    fun s₄ ⟨⟨a₄,k₄,_⟩,v₄⟩ => ?_
  change regsVal s₄ aRegs=wordsVal s₃.mem pa 0 9 at a₄
  have a₄' : regsVal s₄ aRegs=wordsVal s.mem base (arg s .x2) 9 := by
    rw [a₄,wordsVal_off,Nat.add_zero,hmem₃]
  rw [WP.block_append_iff]
  refine WP.mono (park_ok s₄) fun s₅ ⟨z₅,po₅,k₅,v₅⟩ => ?_
  have a₅ : regsVal s₅ aRegs=wordsVal s.mem base (arg s .x2) 9 := by
    rw [regsVal_congr (fun r hr => k₅.gpr r (by
      have h : ∀r∈aRegs,r∉([Reg.x30]:List Reg) := by decide
      exact h r hr)),a₄']
  rw [WP.block_append_iff]
  refine WP.mono (core_ok s₅ z₅ (by rw [a₅]; exact ha)) fun s₆ ⟨b₆,c₆,k₆,v₆⟩ => ?_
  rw [a₅] at c₆
  rw [WP.block_append_iff]
  refine WP.mono (unpark_ok s₆) fun s₇ ⟨po₇,k₇,v₇⟩ => ?_
  have k₃₇ : Keeps fnClob s₃ s₇ :=
    (k₄.mono (by decide)).trans ((k₅.mono (by decide)).trans ((k₆.mono (by decide)).trans (k₇.mono (by decide))))
  have hs₇ := hs₃.of_keeps k₃₇ (by decide)
  have hmem₇ : s₇.mem=s.mem := k₃₇.mem.trans hmem₃
  have v₇₂ : ∀d,d≠.v22 → s₇.v d=s₂.v d := fun d hd => by rw [v₇,v₆,v₅ d hd,v₄,v₃]
  have gpo : s₇.gpr .x30=po := by
    rw [po₇,v₆,po₅,k₄.gpr _ (by decide),go,k₂.gpr,g₁,k₁.gpr _ (by decide)]
  have hpo : PtrW s₇ .x30 po 72 := by
    refine ⟨gpo,fun d hd => ?_,by decide,?_⟩
    · change InRegions _ (off po d) 8
      dsimp only [po]
      rw [off_off]
      have h := hs₇.st (d:=arg s .x1+d) (by omega)
      rwa [hs₇.x0] at h
    · have hfit := hp.fit
      dsimp only [po,base,off]
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a:=arg s .x1) (by omega),Nat.mod_eq_of_lt (by omega)]
      omega
  have out₇ : regsVal s₇ (uRegs.take 9)=regsVal s₆ (uRegs.take 9) :=
    regsVal_congr (fun r hr => k₇.gpr r (by
      have h : ∀r∈uRegs.take 9,r∉([Reg.x30]:List Reg) := by decide
      exact h r hr))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.Mont.WP.block_novec (by decide)
    (storesR_ok (uRegs.take 9) hpo (o:=0) (by decide) (by decide) (by decide)))
    fun s₈ ⟨⟨out₈,k₈,o₈⟩,v₈⟩ => ?_
  change wordsVal s₈.mem po 0 9=regsVal s₇ (uRegs.take 9) at out₈
  change Outside po 0 72 s₇.mem s₈.mem at o₈
  rw [restores_eq]
  refine WP.mono (restores_ok saved 0 (by decide) (by decide)) fun t ⟨k₉,v₉,r₉⟩ => ?_
  have out : wordsVal t.mem base (arg s .x1) 9=regsVal s₆ (uRegs.take 9) := by
    have e := wordsVal_off s₈.mem base (arg s .x1) 0 9
    rw [Nat.add_zero] at e
    rw [k₉.mem,←e]
    exact out₈.trans out₇
  have vkeep : ∀d,d≠.v22 → (∀i<12,d≠(slot i).1) → t.v d=s.v d := fun d hd hi => by
    rw [v₉,v₈,v₇₂ d hd,v₂ d hi,v₁]
  have gpres : ∀r∈preserved,t.gpr r=s.gpr r := by
    intro r hr
    have hsave : saved=preserved := by decide
    rw [←hsave] at hr
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hr
    have l := l₂ i hi
    rw [Nat.zero_add] at l
    rw [r₉ i hi,Nat.zero_add,lane,v₈,v₇₂ _ (by
      have h : ∀i<12,(slot i).1≠.v22 := by decide
      exact h i (by have hlen : saved.length=11 := rfl; omega))]
    change lane s₂.v i=s.gpr saved[i]
    rw [l,k₁.gpr _ (by
      have h : ∀r∈saved,r∉([Reg.x1,.x2,.x3]:List Reg) := by decide
      exact h _ (List.getElem_mem hi))]
  have spkeep : t.sp=s.sp := by rw [k₉.sp,k₈.sp,k₇.sp,k₆.sp,k₅.sp,k₄.sp,k₃.sp,k₂.sp,k₁.sp]
  refine ⟨⟨gpres,spkeep,?_⟩,?_,⟨by rw [out]; exact b₆,by rw [out]; exact c₆⟩,?_,?_,?_,vkeep .v29 (by decide) (by decide)⟩
  · intro d hd
    have h : ∀d∈preservedV,d≠.v22 ∧ ∀i<12,d≠(slot i).1 := by decide
    rw [vkeep d (h d hd).1 (h d hd).2]
  · intro x hx _
    rw [k₉.mem]
    have h := Outside.of_off o₈ (by dsimp only [po,base] at *; have hfit:=hp.fit; omega)
    rw [h x hx,hmem₇]
  · rw [k₉.gpr _ (by decide),k₈.gpr _ (by simp),k₃₇.gpr _ (by decide),k₃.gpr _ (by decide),k₂.gpr,k₁.gpr _ (by decide)]
  · rw [k₉.rd,k₈.rd,k₃₇.rd,k₃.rd,k₂.rd,k₁.rd]
  · rw [k₉.wr,k₈.wr,k₃₇.wr,k₃.wr,k₂.wr,k₁.wr]

end VG.Proof.Mont.AArch64.P521Square
