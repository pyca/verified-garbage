import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedConstants

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.HighPack (SetupKeep)
open VG.Proof.MlDsa.AArch64.Optimized.Response (setup_mono)
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Impl.MlDsa.AArch64.Round

def lowConstants (g : Nat) : List Instr :=
  vc .v11 127 ++ vc .v12 (dMul g) ++ vc .v13 (2^(dShift g-1)) ++
  vc .v14 (if g==261888 then 15 else dMod g) ++ vc .v15 (2*g)

theorem lowConstants_ok (g : Nat) (s : State) : WP isa (.block (lowConstants g)) s fun t =>
    SetupKeep [.v11,.v12,.v13,.v14,.v15] s t ∧
    t.v .v11=HighPack.repeatedWord 127 ∧ t.v .v12=HighPack.repeatedWord (dMul g) ∧
    t.v .v13=HighPack.repeatedWord (2^(dShift g-1)) ∧
    t.v .v14=HighPack.repeatedWord (if g==261888 then 15 else dMod g) ∧
    t.v .v15=HighPack.repeatedWord (2*g) := by
  unfold lowConstants
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok s .v11 127) fun a ha => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok a .v12 (dMul g)) fun b hb => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok b .v13 (2^(dShift g-1))) fun c hc => ?_
  rw [WP.block_append_iff]
  refine WP.mono (HighPack.vc_ok c .v14 (if g==261888 then 15 else dMod g)) fun d hd => ?_
  refine WP.mono (HighPack.vc_ok d .v15 (2*g)) fun t ht => ?_
  refine ⟨setup_mono ((SetupKeep.ofConst ha.1).trans ((SetupKeep.ofConst hb.1).trans
    ((SetupKeep.ofConst hc.1).trans ((SetupKeep.ofConst hd.1).trans (SetupKeep.ofConst ht.1)))))
    (by decide),?_,?_,?_,?_,ht.2⟩
  · rw [ht.1.vec .v11 (by decide),hd.1.vec .v11 (by decide),hc.1.vec .v11 (by decide),hb.1.vec .v11 (by decide),ha.2]
  · rw [ht.1.vec .v12 (by decide),hd.1.vec .v12 (by decide),hc.1.vec .v12 (by decide),hb.2]
  · rw [ht.1.vec .v13 (by decide),hd.1.vec .v13 (by decide),hc.2]
  · rw [ht.1.vec .v14 (by decide),hd.2]

end VG.Proof.MlDsa.AArch64.Optimized.Paired
