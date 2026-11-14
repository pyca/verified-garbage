module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Saves
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! The ordinary-field square has the same alias-safe entry and exit. -/

-- separate module: isolates pointer and ABI composition from the arithmetic core
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Square
open VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Square
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)
open VG.Proof.Weierstrass.AArch64.Mont (Pre arg own Kept zext_ok off_off wordsVal_off Outside.of_off)

theorem square_wp {s : State} {Q : State → Prop} : WP isa VG.Impl.Mont.AArch64.P521Field.square s Q ↔
    WP isa (.block (([.addImm .w .x1 .x1 0,.addImm .w .x2 .x2 0,.addImm .w .x3 .x3 0] : List Instr) ++
      (saves ++ (pointers ++ (loadsR .x1 aRegs 0 ++ (park ++
      (squareCore ++ (unpark ++ (storesR .x30 (uRegs.take 9) 0 ++ restores))))))))) s Q := by
  rw [VG.Impl.Mont.AArch64.P521Field.square,WP.seq_iff,←WP.block_append_iff]
  simp only [entry,exit,pointers,park,unpark,List.append_assoc]

/-- The leaf VG.Impl.Mont.AArch64.P521Field.square preserves the ABI and changes only the output bytes. -/
theorem square_fn_ok {s : State} {W : Nat} (hp : Pre 9 W s)
    (ha : wordsVal s.mem (s.gpr .x0) (arg s .x2) 9 < fieldPrime) :
    WP isa VG.Impl.Mont.AArch64.P521Field.square s fun t =>
      abiPreserved s t ∧ Kept 9 (s.gpr .x0) (arg s .x1) s.mem t.mem ∧
      (wordsVal t.mem (s.gpr .x0) (arg s .x1) 9 < fieldPrime ∧
      wordsVal t.mem (s.gpr .x0) (arg s .x1) 9 =
        wordsVal s.mem (s.gpr .x0) (arg s .x2) 9 * wordsVal s.mem (s.gpr .x0) (arg s .x2) 9 % fieldPrime) ∧
      t.gpr .x0=s.gpr .x0 ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.v .v29=s.v .v29 ∧ t.v .v31=s.v .v31 := by
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
  have hs₃ : Scr s₃ base W := ⟨x0₃,by rw [k₃.wr,k₂.wr,k₁.wr,hp.wr]; simp [base],hp.fit,by omega_arith⟩
  have gpa : s₃.gpr .x1=pa := by rw [ga,k₂.gpr,g₂,k₁.gpr _ (by decide)]
  have hpa : Ptr s₃ .x1 pa 72 := by
    refine ⟨gpa,fun d hd => ?_,by decide⟩
    change InRegions _ (off pa d) 8
    dsimp only [pa]
    rw [off_off]
    have h := hs₃.ld (d:=arg s .x2+d) (by omega_arith)
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
  refine WP.mono (squareCore_ok s₅ z₅ (by rw [a₅]; exact ha)) fun s₆ ⟨b₆,c₆,k₆,v₆⟩ => ?_
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
      have h := hs₇.st (d:=arg s .x1+d) (by omega_arith)
      rwa [hs₇.x0] at h
    · have hfit := hp.fit
      dsimp only [po,base,off]
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a:=arg s .x1) (by omega_arith),Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
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
      exact h i (by have hlen : saved.length=11 := rfl; omega_arith))]
    change lane s₂.v i=s.gpr saved[i]
    rw [l,k₁.gpr _ (by
      have h : ∀r∈saved,r∉([Reg.x1,.x2,.x3]:List Reg) := by decide
      exact h _ (List.getElem_mem hi))]
  have spkeep : t.sp=s.sp := by rw [k₉.sp,k₈.sp,k₇.sp,k₆.sp,k₅.sp,k₄.sp,k₃.sp,k₂.sp,k₁.sp]
  refine ⟨⟨gpres,spkeep,?_⟩,?_,⟨by rw [out]; exact b₆,by rw [out]; exact c₆⟩,?_,?_,?_,⟨vkeep .v29 (by decide) (by decide),vkeep .v31 (by decide) (by decide)⟩⟩
  · intro d hd
    have h : ∀d∈preservedV,d≠.v22 ∧ ∀i<12,d≠(slot i).1 := by decide
    rw [vkeep d (h d hd).1 (h d hd).2]
  · intro x hx _
    rw [k₉.mem]
    have h := Outside.of_off o₈ (by dsimp only [po,base] at *; have hfit:=hp.fit; omega_arith)
    rw [h x hx,hmem₇]
  · rw [k₉.gpr _ (by decide),k₈.gpr _ (by simp),k₃₇.gpr _ (by decide),k₃.gpr _ (by decide),k₂.gpr,k₁.gpr _ (by decide)]
  · rw [k₉.rd,k₈.rd,k₃₇.rd,k₃.rd,k₂.rd,k₁.rd]
  · rw [k₉.wr,k₈.wr,k₃₇.wr,k₃.wr,k₂.wr,k₁.wr]


end VG.Proof.Mont.AArch64.P521Field
