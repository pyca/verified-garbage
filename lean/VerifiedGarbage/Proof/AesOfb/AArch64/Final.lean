module

public import VerifiedGarbage.Impl.AesOfb.AArch64.Final
public import VerifiedGarbage.Proof.AesOfb.Final
public import VerifiedGarbage.Proof.AesOfb.AArch64.Verified
public import VerifiedGarbage.Proof.AesCfb.AArch64.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.AesOfb.AArch64.Body
import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCbc.AArch64.CT

/-!
# AES-OFB of a message's last piece on AArch64

`cryptFinal_framed`: `vg_aes_ofb_final` (`Impl/AesOfb/AArch64/Final.lean`), for
any implementation `v` of the block functions (`BlocksImpl`), meets
`Proof.AesOfb.finalRoundsContract`, from which the shared contract follows
(`Proof.AesOfb.final_keyed`).

Its code is AES-CFB's final function around a call of the whole-block
AES-OFB function, so its proof is AES-CFB's (`Proof/AesCfb/AArch64/Final.lean`),
for OFB as a `Mode` (`ofbMode`): `final_wp` runs it, for any mode, to what it
leaves before restoring the registers (`Done`); `final_rel` gives its
constant time. `ofbFinalAArch64` is AES-CFB's code contract with OFB's
postcondition, which `final_post` gives from `Done` by
`Proof.AesOfb.cryptFinal_of`.
-/

@[expose] public section

namespace VG.Proof.AesOfb.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCfb.AArch64.Final (finalAArch64 FPre Done fW fR fIv fD fL fN fU fT fWk fIv0 fBlks final_wp
  final_ct final_keepsV finalSat finalFrameSat)
open VG.Proof.AesCbc.AArch64 (modeAArch64)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Impl.AesOfb.AArch64
open VG.Impl.AesCfb.AArch64 (final finalTail)

/-- The code's contract, with the arguments `(schedule = x0, rounds = x1,
iv = x2, data = x3, len = x4, scratch = x5, save = x6)`: AES-CFB's final
functions' (`finalAArch64`), with the data and the block at `iv` as
`Spec.Ofb.CryptFinal` says, by AES with the key schedule it is given. -/
def ofbFinalAArch64 : Contract isa :=
  { finalAArch64 true with
    post := fun s s' => Spec.Ofb.CryptFinal (ciphAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 16 s.mem s'.mem
      (s.gpr .x2) (s.gpr .x3) (s.gpr .x4).toNat }

/-- The contract the frame needs: the shared one, with `save`, 64 bytes, as
a seventh argument, and no stack (a call keeps its return address in
`x30`). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract AArch64.abi Spec.Ofb.aesFinalSig "save" .u64 8 (finalPre AArch64.abi.ptrBits)
    (finalPost AArch64.abi.ptrBits) false 0

theorem final_implies : ofbFinalAArch64.Implies finalScratchContract := by
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Ofb.aesFinalSig, finalPre, finalPost, ofbFinalAArch64, finalAArch64, AArch64.abi,
    AArch64.argRegs] [finalSat] using finalSat

/-- `Spec.Ofb.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done ofbMode s₀ s₁) (hm : s'.mem = s₁.mem) :
    ofbFinalAArch64.post s₀ s' := by
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

theorem crypt_noFrames (v : BlocksImpl) : (crypt v.enc).noFrames = true := by
  simp only [crypt, Impl.AesCbc.AArch64.whole, body, Code.noFrames, v.encNoFrames, Bool.and_self]

theorem final_correct (v : BlocksImpl) (s : State) (hs : ofbFinalAArch64.pre s) :
    ∃ t s', Exec isa (cryptFinal v.enc v.suffix) s t s' ∧ abiPreserved s s' ∧ ofbFinalAArch64.post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ :=
    final_wp (M := ofbMode) (crypt_correct v) (crypt_noFrames v) v (FPre.of (enc := true) hs)
  exact ⟨t, s', he, ⟨hg, AArch64.Exec.sp he, Exec.preservedV he (final_keepsV v (crypt_keepsV v))⟩,
    final_post h₁ hm⟩

/-! ## Verified -/

theorem cryptFinal_verified (v : BlocksImpl) :
    Verified AArch64.target (cryptFinal v.enc v.suffix) finalScratchContract :=
  Verified.of_correct (final_correct v)
    (final_ct (enc := true) (crypt_correct v) (AesCbc.AArch64.whole_ct (body_ok v) (body_ct v))
      (crypt_noFrames v) v)
    final_implies

/-! ## With `save` on the stack

As AES-CFB's final functions, the code runs in a frame of 64 bytes on the
stack (`withStackScratchWiped`), `save`'s 64 bytes, which it zeroes before
returning. Its calls use no stack, so 64 in all. -/

theorem frameSat_pre : ∃ s, (finalRoundsContract AArch64.abi 64).pre s := by
  implies_sat [finalRoundsContract, Spec.Ofb.aesFinalSig, finalPre, finalPost, AArch64.abi,
    AArch64.argRegs] [finalFrameSat, finalSat] using finalFrameSat

theorem cryptFinal_framed (v : BlocksImpl) :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (cryptFinal v.enc v.suffix))
      (finalRoundsContract AArch64.abi 64) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Ofb.aesFinalSig) (nm := "save") (e := .u64) (n := 8)
    (pre := finalPre AArch64.abi.ptrBits) (post := finalPost AArch64.abi.ptrBits) (wa := false)
    (stack := 0) (bytes := 64) (words := 8) (cryptFinal_verified v) (by decide) (by decide) (by decide)
    (finalPost_localOut _) frameSat_pre

end VG.Proof.AesOfb.AArch64
