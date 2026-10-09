import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailNonce

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (WP.cons)

def upperFinish : List Instr :=
  [.lsl .x .x7 .x5 48,.lsr .x .x7 .x7 48,.movz .x .x8 31 1,.add .x .x7 .x7 .x8,
    .vop (.ins .d2 .v8 1 .x7),.movz .x .x7 0x8000 3,.vop (.ins .d2 .v16 1 .x7)]

private theorem pad7_ok (s : State) :
    WP isa (.block [.movz .x .x7 0x8000 3]) s fun t =>
      RegKeep [.x7] s t ∧ t.mem=s.mem ∧ t.v=s.v ∧ t.gpr .x7=0x8000000000000000 := by
  refine WP.cons rfl (WP.block_nil_iff.mpr ?_)
  refine ⟨⟨fun r hr => ?_,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩
  have hr' : r≠.x7 := by simpa using hr
  simp only [RegUpd.gpr_write,hr',ite_false]

/-- Adds the two-byte nonce and SHAKE padding to the second stream. -/
theorem upperFinish_ok {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) :
    WP isa (.block upperFinish) s fun t =>
      RegKeep [.x7,.x8] s t ∧ t.mem=s.mem ∧
      Pairs t A (replaceWord (replaceWord B 8 (nonceWord (s.gpr .x5))) 16 0x8000000000000000) := by
  change WP isa (.block (([.lsl .x .x7 .x5 48,.lsr .x .x7 .x7 48,
    .movz .x .x8 31 1,.add .x .x7 .x7 .x8] : List Instr) ++
    [.vop (.ins .d2 .v8 1 .x7),.movz .x .x7 0x8000 3,.vop (.ins .d2 .v16 1 .x7)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (nonce_ok s) fun a ⟨ha,hma,hva,ea⟩ => ?_
  have hpa : Pairs a A B := by intro i hi; rw [hva]; exact hp i hi
  change WP isa (.block (([.vop (.ins .d2 .v8 1 .x7)] : List Instr) ++
    [.movz .x .x7 0x8000 3,.vop (.ins .d2 .v16 1 .x7)])) a _
  rw [WP.block_append_iff]
  refine WP.mono (insertHigh_ok (j:=8) (by decide) hpa) fun b ⟨hb,hmb,hpb⟩ => ?_
  rw [ea] at hpb
  change WP isa (.block (([.movz .x .x7 0x8000 3] : List Instr) ++
    [.vop (.ins .d2 .v16 1 .x7)])) b _
  rw [WP.block_append_iff]
  refine WP.mono (pad7_ok b) fun c ⟨hc,hmc,hvc,ec⟩ => ?_
  have hpc : Pairs c A (replaceWord B 8 (nonceWord (s.gpr .x5))) := by
    intro i hi; rw [hvc]; exact hpb i hi
  refine WP.mono (insertHigh_ok (j:=16) (by decide) hpc) fun t ⟨ht,hmt,hpt⟩ => ?_
  rw [ec] at hpt
  exact ⟨(((ha.trans hb).trans hc).trans ht).mono (by simp),
    hmt.trans (hmc.trans (hmb.trans hma)),hpt⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
