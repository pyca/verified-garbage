module

public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Crypt
import VerifiedGarbage.Proof.Modes.AArch64.Fb
import VerifiedGarbage.Proof.Sm4.AArch64.Lit
public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Prepared
public import VerifiedGarbage.Proof.Sm4.AArch64.PreparedBody

/-! # The single-block SM4 core meets the existing mode interface -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Modes.AArch64 (CoreSpec BlockSpec KeepsReg bufAddr)

@[simp] theorem core_bw : core.bw = 2 := rfl

def coreSpec : CoreSpec core where
  Key := Spec.Sm4.Schedule
  cipher := Spec.Sm4.cipher
  KeyArgs := VG.Proof.Sm4.AArch64.KeyArgs
  Ready s B k := Ready s.mem B k
  cipher_len _ _ := by simp [Spec.Sm4.cipher]
  layout := ⟨by decide,by decide,by decide,by decide,by decide⟩
  keyRegs_ok := by decide
  regs_ok := by decide
  keyArgs_congr h hr hrd hwr _ hf := VG.Proof.Sm4.AArch64.keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ _ := h.frame hf hd
  prepare_wp := prepare_wp
  crypt_wp := by
    intro s B k hb hs hr
    refine WP.mono (crypt_wp hb hs hr) fun t ⟨tb,td,tl,tr,tf,to,rd,wr⟩ =>
      ⟨tb,td,tl,tr,tf,?_,rd,wr⟩
    intro j hj
    have hj' : j < 1 := hj
    have hj0 : j = 0 := by omega
    subst j
    change Spec.Aes.bytesAt t.mem (B+BitVec.ofNat 64 (768+16*0)) 16 =
      Spec.Sm4.cipher k (Spec.Aes.bytesAt s.mem (B+BitVec.ofNat 64 (768+16*0)) 16)
    exact to

abbrev blockSpec : BlockSpec core := coreSpec.toBlock rfl

theorem prepare_regSafe_x19 : VG.Proof.Modes.AArch64.regSafe .x19 core.prepare = true := by
  show VG.Proof.Modes.AArch64.regSafe .x19 (.seq (.block preparedTable) copySchedule) = true
  rw [VG.Proof.Sm4.AArch64.serialTable.lit_eq]
  decide +kernel

theorem crypt_regSafe_x19 : VG.Proof.Modes.AArch64.regSafe .x19 core.crypt = true := by decide +kernel

theorem keeps_x19 : KeepsReg .x19 core.prepare ∧ KeepsReg .x19 core.crypt :=
  ⟨VG.Proof.Modes.AArch64.keepsReg_of_regSafe prepare_regSafe_x19,
    VG.Proof.Modes.AArch64.keepsReg_of_regSafe crypt_regSafe_x19⟩

attribute [local irreducible] Spec.Sm4.cipher in
theorem cipher_eq (k : Spec.Sm4.Schedule) : blockSpec.cipher k = Spec.Sm4.cipher k := rfl

end VG.Proof.Sm4.AArch64.Serial
