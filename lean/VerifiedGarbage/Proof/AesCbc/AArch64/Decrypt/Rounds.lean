module

public import VerifiedGarbage.Impl.AesCbc.AArch64.Decrypt
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Dec
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # The fixed-key-size inverse rounds before CBC's fused final XOR -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.Aes.AArch64.Aese
open VG.Impl.Aes.AArch64.Aese

def middle (nr : Nat) (regs : List VReg) : List Instr :=
  if nr = 10 then [] else
    (if nr = 12 then [] else drnd regs .v29 ++ drnd regs .v28) ++
      drnd regs .v27 ++ drnd regs .v26

theorem middle_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : DKeys nr w s) (hI : DInv regs nr w x 1 s) :
    WP isa (.block (middle nr regs)) s fun t =>
      DInv regs nr w x (nr-9) t ∧ VFrame regs s t := by
  obtain rfl | rfl | rfl := hK.rounds
  · exact WP.block_nil ⟨hI, VFrame.refl _ _⟩
  · change WP isa (.block (drnd regs .v27 ++ drnd regs .v26)) s _
    exact dtwo_ok hr 11 rfl rfl (by omega) (by omega) (by omega) hK hI
  · rw [middle, ite_eq_right (by decide), ite_eq_right (by decide),
      List.append_assoc (drnd regs .v29 ++ drnd regs .v28), WP.block_append_iff]
    refine WP.mono (dtwo_ok hr 13 rfl rfl (by omega) (by omega) (by omega) hK hI)
      fun t ⟨hI', hf⟩ => ?_
    exact WP.mono (dtwo_ok hr 11 rfl rfl (by omega) (by omega) (by omega)
      (hK.of_frame hf hr) hI') fun u ⟨hI'', hf'⟩ => ⟨hI'', hf.trans hf'⟩

def lastValue (v k : BitVec 128) : BitVec 128 :=
  aesMapBytes aesInvSbox (aesInvShiftRows (v ^^^ k))

theorem last_run (b : VReg) (s : State) :
    runBlock isa [.vop (.aesd b .v17)] s = some (s.setV b (lastValue (s.v b) (s.v .v17))) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]
  rfl

theorem last_values {regs : List VReg} (hr : BlockRegs regs) (s : State) :
    WP isa (.block (regs.map fun b => .vop (.aesd b .v17))) s fun t =>
      (∀ b ∈ regs, t.v b = lastValue (s.v b) (s.v .v17)) ∧ VFrame regs s t := by
  have hm : regs.flatMap (fun b => [Instr.vop (.aesd b .v17)]) =
      regs.map (fun b => Instr.vop (.aesd b .v17)) := by
    clear hr
    induction regs with
    | nil => rfl
    | cons b bs ih => simp only [List.flatMap_cons, List.map_cons, List.singleton_append, ih]
  rw [← hm]
  exact each_ok (fun b => [.vop (.aesd b .v17)]) lastValue .v17
    (fun b s _ => last_run b s) regs s hr.1 (fun h => (hr.2 _ h).2.1 rfl)

/-- The key-zero XOR is delayed until the chaining XOR; its value remains available. -/
theorem last_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {x : VReg → Spec.Aes.State} {s : State} (hK : DKeys nr w s)
    (hI : DInv regs nr w x (nr-1) s) :
    WP isa (.block (regs.map fun b => .vop (.aesd b .v17))) s fun t =>
      (∀ b ∈ regs, st (t.v b ^^^ t.v .v16) = Spec.Aes.invCipher nr w (x b)) ∧ VFrame regs s t := by
  have hn : 2 ≤ nr := by obtain h | h | h := hK.rounds <;> omega
  have hk1 : KeyIs (s.v .v17) (dkey nr w (nr-1)) := by
    rw [dkey, ite_eq_right (by omega), show nr - (nr-1) = 1 by omega]
    exact hK.mid 1 (by omega) (by omega)
  refine WP.mono (last_values hr s) fun t ⟨hv,hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, hf.v _ (fun h => (hr.2 _ h).1 rfl)]
  exact (dlast_st hk1 hK.k0 (hI b hb)).trans (Proof.Aes.invCipher_eq _ _ _).symm

theorem rounds_ok {regs : List VReg} (hr : BlockRegs regs) {nr : Nat} {w : List Byte}
    {s : State} (hK : DKeys nr w s) :
    WP isa (Impl.AesCbc.AArch64.Decrypt.rounds nr regs) s fun t =>
      (∀ b ∈ regs, st (t.v b ^^^ t.v .v16) = Spec.Aes.invCipher nr w (st (s.v b))) ∧
      VFrame regs s t := by
  have hn : 10 ≤ nr := by obtain h | h | h := hK.rounds <;> omega
  let x : VReg → Spec.Aes.State := fun b => st (s.v b)
  have hI : DInv regs nr w x 0 s := fun b _ => by simp [dkey, Proof.Aes.invMid, x]
  change WP isa (.block (drnd regs .v30 ++ middle nr regs ++
    (List.range 8).flatMap (fun j => drnd regs (kreg (9-j))) ++
    regs.map (fun b => .vop (.aesd b .v17)))) s _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (dround_ok hr (m := 0) (by omega) hr.v30 (by simpa [dkey] using hK.last) hI)
    fun s₁ ⟨hI₁,hf₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (middle_ok hr (hK.of_frame hf₁ hr) hI₁) fun s₂ ⟨hI₂,hf₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (drounds_ok hr hn 8 (by omega) (hK.of_frame (hf₁.trans hf₂) hr) hI₂)
    fun s₃ ⟨hI₃,hf₃⟩ => ?_
  rw [show nr-9+8 = nr-1 by omega] at hI₃
  exact WP.mono (last_ok hr (hK.of_frame (hf₁.trans (hf₂.trans hf₃)) hr) hI₃)
    fun t ⟨hv,hf⟩ => ⟨hv, hf₁.trans (hf₂.trans (hf₃.trans hf))⟩

end VG.Proof.AesCbc.AArch64.Decrypt
