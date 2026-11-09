module

public import VerifiedGarbage.Impl.AesOfb.PPC64LE.Final
public import VerifiedGarbage.Proof.AesOfb.Final
public import VerifiedGarbage.Proof.AesOfb.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesCfb.PPC64LE.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.AesOfb.PPC64LE.Body
import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT

/-!
# AES-OFB of a message's last piece on PPC64LE

`cryptFinal_framed`: `vg_aes_ofb_final` (`Impl/AesOfb/PPC64LE/Final.lean`)
meets `Proof.AesOfb.finalRoundsContract`, from which the shared contract
follows (`Proof.AesOfb.final_keyed`).

Its code is AES-CFB's final function around a call of the whole-block
AES-OFB function, so its proof is AES-CFB's (`Proof/AesCfb/PPC64LE/Final.lean`),
for OFB as a `Mode` (`ofbMode`): `final_wp` runs it, for any mode, to what it
leaves before restoring the registers (`Done`); `final_ct` gives its
constant time. `ofbFinalPPC64LE` is AES-CFB's code contract with OFB's
postcondition, which `final_post` gives from `Done` by
`Proof.AesOfb.cryptFinal_of`.
-/

@[expose] public section

namespace VG.Proof.AesOfb.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCfb.PPC64LE.Final (finalPPC64LE FPre Done fW fR fIv fD fL fN fU fT fWk fIv0 fBlks final_wp
  final_ct finalSat finalFrameSat)
open VG.Proof.AesCbc.PPC64LE (modePPC64LE)
open VG.Impl.AesOfb.PPC64LE

/-- The code's contract, with the arguments `(schedule = r3, rounds = r4,
iv = r5, data = r6, len = r7, scratch = r8, save = r9)`: AES-CFB's final
functions' (`finalPPC64LE`), with the data and the block at `iv` as
`Spec.Ofb.CryptFinal` says, by AES with the key schedule it is given. -/
def ofbFinalPPC64LE : Contract isa :=
  { finalPPC64LE true with
    post := fun s s' => Spec.Ofb.CryptFinal (ciphAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) 16 s.mem s'.mem
      (s.gpr .r5) (s.gpr .r6) (s.gpr .r7).toNat }

/-- The contract the frame needs: the shared one, with `save`, 64 bytes, as
a seventh argument, and no stack (a call stores nothing in memory). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract PPC64LE.abi Spec.Ofb.aesFinalSig "save" .u64 8 (finalPre PPC64LE.abi.ptrBits)
    (finalPost PPC64LE.abi.ptrBits) false 0

theorem final_implies : ofbFinalPPC64LE.Implies finalScratchContract := by
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Ofb.aesFinalSig, finalPre, finalPost, ofbFinalPPC64LE, finalPPC64LE, PPC64LE.abi,
    PPC64LE.argRegs] [finalSat] using finalSat

/-- `Spec.Ofb.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done ofbMode s₀ s₁) (hm : s'.mem = s₁.mem) :
    ofbFinalPPC64LE.post s₀ s' := by
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

theorem crypt_noFrames : crypt.noFrames = true := by
  simp only [crypt, Impl.AesCbc.PPC64LE.whole, body, Impl.AesCbc.PPC64LE.encCall, Code.noFrames,
    Bool.true_and, Bool.and_true]
  exact Proof.AesCbc.PPC64LE.encryptBlocks_noFrames

theorem final_correct (s : State) (hs : ofbFinalPPC64LE.pre s) :
    ∃ t s', Exec isa cryptFinal s t s' ∧ abiPreserved s s' ∧ ofbFinalPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hl, s₁, h₁, hm⟩ :=
    final_wp (M := ofbMode) crypt_correct crypt_noFrames (FPre.of (enc := true) hs)
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hl⟩, final_post h₁ hm⟩

/-! ## Verified -/

theorem cryptFinal_verified : Verified PPC64LE.target cryptFinal finalScratchContract :=
  Verified.of_correct final_correct
    (final_ct (enc := true) crypt_correct (AesCbc.PPC64LE.whole_ct body_ok body_ct) crypt_noFrames)
    final_implies

/-! ## With `save` on the stack

As AES-CFB's final functions, the code runs in a frame of 96 bytes on the
stack (`withStackScratchWiped`), its 32-byte header and `save`'s 64 bytes,
which it zeroes before returning. Its calls use no stack, so 96 in all. -/

theorem frameSat_pre : ∃ s, (finalRoundsContract PPC64LE.abi (0 + 96)).pre s := by
  implies_sat [finalRoundsContract, Spec.Ofb.aesFinalSig, finalPre, finalPost, PPC64LE.abi,
    PPC64LE.argRegs] [finalFrameSat, finalSat] using finalFrameSat

theorem cryptFinal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r9 8 cryptFinal)
      (finalRoundsContract PPC64LE.abi 96) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Ofb.aesFinalSig) (nm := "save") (e := .u64) (n := 8)
    (pre := finalPre PPC64LE.abi.ptrBits) (post := finalPost PPC64LE.abi.ptrBits) (wa := false)
    (stack := 0) (bytes := 96) (words := 8) cryptFinal_verified (by decide) (by decide) (by decide)
    (finalPre_local _) (finalPost_local _) (finalPost_localOut _) frameSat_pre

end VG.Proof.AesOfb.PPC64LE
