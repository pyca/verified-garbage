module

public import VerifiedGarbage.Impl.AesOfb.RISCV64.Final
public import VerifiedGarbage.Proof.AesOfb.Final
public import VerifiedGarbage.Proof.AesOfb.RISCV64.Verified
public import VerifiedGarbage.Proof.AesCfb.RISCV64.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.AesCbc.Spec

/-!
# AES-OFB of a message's last piece on RISC-V

`cryptFinal_framed`: `vg_aes_ofb_final` (`Impl/AesOfb/RISCV64/Final.lean`)
meets `Proof.AesOfb.finalRoundsContract`, from which the shared contract
follows (`Proof.AesOfb.final_keyed`).

Its code is AES-CFB's final function around a call of the whole-block
AES-OFB function, so its proof is AES-CFB's (`Proof/AesCfb/RISCV64/Final.lean`),
for OFB as a `Mode` (`ofbMode`): `final_wp` runs it, for any mode, to what it
leaves before restoring the registers (`Done`); `final_ct` gives its
constant time. `ofbFinalRISCV64` is AES-CFB's code contract with OFB's
postcondition, which `final_post` gives from `Done` by
`Proof.AesOfb.cryptFinal_of`.
-/

@[expose] public section

namespace VG.Proof.AesOfb.RISCV64

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCfb.RISCV64.Final (finalRISCV64 FPre Done fW fR fIv fD fL fN final_wp final_ct finalSat
  finalFrameSat)
open VG.Impl.AesOfb.RISCV64

/-- The code's contract, with the arguments `(schedule = a0, rounds = a1,
iv = a2, data = a3, len = a4, scratch = a5, save = a6)`: AES-CFB's final
functions' (`finalRISCV64`), with the data and the block at `iv` as
`Spec.Ofb.CryptFinal` says, by AES with the key schedule it is given. -/
def ofbFinalRISCV64 : Contract isa :=
  { finalRISCV64 true with
    post := fun s s' => Spec.Ofb.CryptFinal (ciphAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) 16 s.mem s'.mem
      (s.gpr .a2) (s.gpr .a3) (s.gpr .a4).toNat }

/-- The contract the frame needs: the shared one, with `save`, 64 bytes, as
a seventh argument, and no stack (a call keeps its return address in
`ra`). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract RISCV64.abi Spec.Ofb.aesFinalSig "save" .u64 8 (finalPre RISCV64.abi.ptrBits)
    (finalPost RISCV64.abi.ptrBits) false 0

theorem final_implies : ofbFinalRISCV64.Implies finalScratchContract := by
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Ofb.aesFinalSig, finalPre, finalPost, ofbFinalRISCV64, finalRISCV64, RISCV64.abi,
    RISCV64.argRegs] [finalSat] using finalSat

/-- `Spec.Ofb.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done ofbMode s₀ s₁) (hm : s'.mem = s₁.mem) :
    ofbFinalRISCV64.post s₀ s' := by
  show Spec.Ofb.CryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) 16 s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
  have e := AesCbc.length_blocksAt s₀.mem (fD s₀) (fN s₀)
  have hb := h.blocks
  have ht := h.tail
  have hi := h.iv
  rw [ofbMode_out] at hb
  rw [ofbMode_chain, e] at ht hi
  exact cryptFinal_of (aesWith_length _ _) (by rw [hm]; exact hb) (fun q hq => by rw [hm]; exact ht q hq)
    (by rw [hm]; exact hi)

/-! ## The code's properties -/

theorem crypt_noFrames : crypt.noFrames = true := rfl

theorem final_correct (s : State) (hs : ofbFinalRISCV64.pre s) :
    ∃ t s', Exec isa cryptFinal s t s' ∧ abiPreserved s s' ∧ ofbFinalRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, s₁, h₁, hm⟩ :=
    final_wp (M := ofbMode) crypt_correct crypt_noFrames (FPre.of (enc := true) hs)
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, final_post h₁ hm⟩

/-! ## Verified -/

theorem cryptFinal_verified : Verified RISCV64.target cryptFinal finalScratchContract :=
  Verified.of_correct final_correct (final_ct (enc := true) crypt_correct crypt_ct crypt_noFrames)
    final_implies

/-! ## With `save` on the stack

As AES-CFB's final functions, the code runs in a frame of 64 bytes on the
stack (`withStackScratchWiped`), `save`'s 64 bytes, which it zeroes before
returning. Its calls use no stack, so 64 in all. -/

theorem frameSat_pre : ∃ s, (finalRoundsContract RISCV64.abi 64).pre s := by
  implies_sat [finalRoundsContract, Spec.Ofb.aesFinalSig, finalPre, finalPost, RISCV64.abi,
    RISCV64.argRegs] [finalFrameSat, finalSat] using finalFrameSat

theorem cryptFinal_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 cryptFinal)
      (finalRoundsContract RISCV64.abi 64) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Ofb.aesFinalSig) (nm := "save") (e := .u64) (n := 8)
    (pre := finalPre RISCV64.abi.ptrBits) (post := finalPost RISCV64.abi.ptrBits) (wa := false)
    (stack := 0) (bytes := 64) (words := 8) cryptFinal_verified (by decide) (by decide) (by decide)
    (finalPost_localOut _) frameSat_pre

end VG.Proof.AesOfb.RISCV64
