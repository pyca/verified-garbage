module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Crypt
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Prepared
import VerifiedGarbage.Proof.Modes.AArch64.Fb
import VerifiedGarbage.Proof.Camellia.AArch64.Lit

/-! # The serial Camellia core implements the existing feedback-mode interface -/

@[expose] public section
namespace VG.Proof.Camellia.AArch64.Serial
open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial
open VG.Proof.Modes.AArch64 (CoreSpec BlockSpec KeepsReg)

@[simp] theorem core_bw : core.bw = 2 := rfl

def coreSpec : CoreSpec core where
  Key := Nat × List (BitVec 64)
  cipher k := Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := VG.Proof.Camellia.AArch64.KeyArgs
  Ready s B k := Ready s.mem B k ∧ s.gpr .x1 = BitVec.ofNat 64 k.1
  cipher_len _ _ := by simp [Spec.Camellia.cipher]
  layout := ⟨by decide,by decide,by decide,by decide,by decide⟩
  keyRegs_ok := by decide
  regs_ok := by decide
  keyArgs_congr h hr hrd hwr _ hf := VG.Proof.Camellia.AArch64.keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ hg := ⟨h.1.frame hf hd,(hg .x1 (by decide)).trans h.2⟩
  prepare_wp hb hs hr hk := WP.mono (prepare_wp hb hs hr hk)
    (fun _ ⟨r,c,b,d,l,f,rd,wr⟩ => ⟨⟨r,c⟩,b,d,l,f,rd,wr⟩)
  crypt_wp hb hs hr := WP.mono (crypt_wp hb hs hr.1 hr.2)
    (fun _ ⟨b,d,l,r,c,f,o,rd,wr⟩ => ⟨b,d,l,⟨r,c⟩,f,by
      intro j hj
      have hj0 : j = 0 := by change j < 1 at hj; omega
      subst j
      exact o,rd,wr⟩)

abbrev blockSpec : BlockSpec core := coreSpec.toBlock rfl

theorem prepare_regSafe_x19 : VG.Proof.Modes.AArch64.regSafe .x19 core.prepare = true := by
  show VG.Proof.Modes.AArch64.regSafe .x19 (.seq (.block table) copySchedule) = true
  rw [VG.Proof.Camellia.AArch64.serialTable.lit_eq]
  decide +kernel

theorem crypt_regSafe_x19 : VG.Proof.Modes.AArch64.regSafe .x19 core.crypt = true := by decide +kernel

theorem keeps_x19 : KeepsReg .x19 core.prepare ∧ KeepsReg .x19 core.crypt :=
  ⟨VG.Proof.Modes.AArch64.keepsReg_of_regSafe prepare_regSafe_x19,
    VG.Proof.Modes.AArch64.keepsReg_of_regSafe crypt_regSafe_x19⟩

theorem prepare_regSafe_x30 : VG.Proof.Modes.AArch64.regSafe .x30 core.prepare = true := by
  show VG.Proof.Modes.AArch64.regSafe .x30 (.seq (.block table) copySchedule) = true
  rw [VG.Proof.Camellia.AArch64.serialTable.lit_eq]
  decide +kernel

theorem crypt_regSafe_x30 : VG.Proof.Modes.AArch64.regSafe .x30 core.crypt = true := by decide +kernel

theorem keeps_x30 : KeepsReg .x30 core.prepare ∧ KeepsReg .x30 core.crypt :=
  ⟨VG.Proof.Modes.AArch64.keepsReg_of_regSafe prepare_regSafe_x30,
    VG.Proof.Modes.AArch64.keepsReg_of_regSafe crypt_regSafe_x30⟩

end VG.Proof.Camellia.AArch64.Serial
