import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64
open HighPack
open VG.Proof.MlDsa.AArch64.Round

 theorem setup_ready (s : State) {g : Nat} (hg : IsG g) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.HighPack.constants g++Impl.MlDsa.AArch64.Optimized.HighPack.packSetup)) s fun t=>
      SetupKeep [.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23,.v28,.v29,.v24,.v25] s t ∧ Ready g t := by
  rw [WP.block_append_iff]
  refine WP.mono (constants_ok s g) fun a ha=>?_
  refine WP.mono (packSetup_ok a) fun t ht=>?_
  obtain ⟨hk,_,h17,h18,h19,h20,h21,h22,h23⟩ := ha
  refine ⟨hk.trans ht.1,⟨⟨?_,?_,?_,?_⟩,⟨ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2⟩⟩,?_,?_,?_⟩
  · intro e he;rw [ht.1.vec .v17 (by decide),h17,repeatedWord_lane _ he]
  · intro e he;rw [ht.1.vec .v18 (by decide),h18,repeatedWord_lane _ he]
    rcases hg with rfl|rfl <;> rfl
  · intro e he;rw [ht.1.vec .v19 (by decide),h19,repeatedWord_lane _ he]
    rcases hg with rfl|rfl <;> rfl
  · intro e he;rw [ht.1.vec .v20 (by decide),h20,repeatedWord_lane _ he]
  · intro e he;rw [ht.1.vec .v21 (by decide),h21,repeatedWord_lane _ he]
  · intro e he;rw [ht.1.vec .v22 (by decide),h22,repeatedWord_lane _ he];rfl
  · intro e _;rw [ht.1.vec .v23 (by decide),h23];simp [vword]

 theorem code_eq (g : Nat) : Impl.MlDsa.AArch64.Optimized.UseHintPack.code g=
    .seq (.block (Impl.MlDsa.AArch64.Optimized.HighPack.constants g++
      Impl.MlDsa.AArch64.Optimized.HighPack.packSetup++([.movz .x .x11 16 0] : List Instr)))
      (.loop (.block (groupCode g++advance g)) (.nonzero .x .x11)) := by
  simp only [Impl.MlDsa.AArch64.Optimized.UseHintPack.code,groupCode,loadFour,advance,packWidth,
    beq_iff_eq,List.append_assoc]

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
