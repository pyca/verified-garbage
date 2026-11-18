module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Final
public import VerifiedGarbage.Proof.AesCfb.RISCV64.Final
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Aes.Scratch
public import VerifiedGarbage.Proof.AesEcb.Wipe
public import VerifiedGarbage.Proof.AesCbc.Wipe
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Final
meta import VerifiedGarbage.Proof.AesCfb.RISCV64.Final
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Aes.Scratch
meta import VerifiedGarbage.Proof.AesEcb.Wipe
meta import VerifiedGarbage.Proof.AesCbc.Wipe
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.CallWipe
public import VerifiedGarbage.Proof.Zeroize.RISCV64
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallWipe
meta import VerifiedGarbage.Proof.Zeroize.RISCV64
meta import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Impl.StackScratch.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Aes.RISCV64.ExpandKeyVerified
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
public import VerifiedGarbage.Impl.Aes.RISCV64.ExpandKey
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Aes.Contract
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Aes.RISCV64.ExpandKeyVerified
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Impl.Aes.RISCV64.ExpandKey
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Verified
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Lit
public import VerifiedGarbage.Proof.AesCfb8.Rounds
public import VerifiedGarbage.Impl.AesCfb8.RISCV64
public import VerifiedGarbage.Spec.Cfb8.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Aes.RISCV64.ChainModes
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Chain
public import VerifiedGarbage.Proof.AesCfb8.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCfb8.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Aes.RISCV64.ChainModes
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Chain
meta import VerifiedGarbage.Proof.AesCfb8.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.AesCfb8.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.AesCfb8.Rounds
meta import VerifiedGarbage.Impl.AesCfb8.RISCV64
meta import VerifiedGarbage.Spec.Cfb8.Contract
public import VerifiedGarbage.Impl.AesOfb.RISCV64.Final
public import VerifiedGarbage.Proof.AesOfb.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.AesOfb.Spec
public import VerifiedGarbage.Proof.AesOfb.Rounds
public import VerifiedGarbage.Impl.AesOfb.RISCV64
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
public import VerifiedGarbage.Spec.Ofb.Contract
meta import VerifiedGarbage.Impl.AesOfb.RISCV64.Final
meta import VerifiedGarbage.Proof.AesOfb.Final
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.AesOfb.Spec
meta import VerifiedGarbage.Proof.AesOfb.Rounds
meta import VerifiedGarbage.Impl.AesOfb.RISCV64
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
meta import VerifiedGarbage.Spec.Ofb.Contract

/-! ### `AesOfb.RISCV64.Final`, which only this module used -/

section

/-! ### `AesOfb.RISCV64.Verified`, which this module and modules that import it used -/

section

/-!
# AES-OFB on RISC-V: `Verified`

Correctness and constant time, from the OFB chain's
(`Proof/Aes/RISCV64/ChainModes.lean`) and its call's (`wrap_wp`, `wrap_ct`,
`Proof/AesCbc/RISCV64/Chain.lean`), a state satisfying the precondition, and
the shared contract of
`Spec/Ofb/Contract.lean` (with no stack: a call stores nothing in memory, and
the return address is saved in the scratch buffer).
-/

@[expose] public section

namespace VG.Proof.AesOfb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOfb.RISCV64
open VG.Proof.AesCbc.RISCV64

theorem crypt_correct (s : State) (hs : (modeRISCV64 ofbMode).pre s) :
    ∃ t s', Exec isa crypt s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 ofbMode).post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ :=
    wrap_wp Proof.Aes.RISCV64.ofbChain_k (name := "vg_aes_ofb_chain") (encrypt_wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem crypt_ct : ConstantTime isa (modeRISCV64 ofbMode).pre (modeRISCV64 ofbMode).pub crypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    wrap_ct Proof.Aes.RISCV64.ofbChain_k "vg_aes_ofb_chain" _ _ _ _ _ _ (encrypt_wpre h₁) (encrypt_wpre h₂)
      hq e₁ e₂

theorem crypt_verified : Verified RISCV64.target crypt (Proof.AesOfb.roundsContract RISCV64.abi) :=
  Verified.of_correct crypt_correct crypt_ct
    { pre := by sig_implies_pre [Proof.AesOfb.roundsContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeRISCV64,
        RISCV64.abi, RISCV64.argRegs]
      -- `ofbMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Proof.AesOfb.roundsContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeRISCV64, ofbMode, RISCV64.abi,
          RISCV64.argRegs]
        sig_reduce [Proof.AesOfb.roundsContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeRISCV64, ofbMode, RISCV64.abi,
          RISCV64.argRegs] at h
        sig_simp [Proof.AesOfb.roundsContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeRISCV64, ofbMode, RISCV64.abi,
          RISCV64.argRegs] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Proof.AesOfb.roundsContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeRISCV64,
        RISCV64.abi, RISCV64.argRegs]
      sat := by sig_implies_sat [Proof.AesOfb.roundsContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, modeRISCV64,
        RISCV64.abi, RISCV64.argRegs] [sat] using sat }

end VG.Proof.AesOfb.RISCV64

end

end

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

end

end

/-! ### `AesCfb8.RISCV64.Verified`, which only this module used -/

section

/-! ### `AesCfb8.RISCV64.Chain`, which only this module used -/

section

/-!
# AES-CFB8 on RISC-V: the chain

`cfb8Chain enc` (`Impl/Aes/RISCV64/Chain.lean`) runs `chain`'s frame
(`ChainFrame.lean`) over the `n` bytes at `data`, with the input block in
two slots of the scratch buffer (58 and 63, `slotQ`), stored there from
the registers of block 0 before the loop and loaded back after it. Each
byte loads it into those registers, enciphers it (`encrypt4`), XORs its
first byte into the data byte, and shifts the input block left by a byte
with the ciphertext byte shifted in. After `k` bytes (`BAt`) the input
block is CFB8's after the first `k` bytes (`inK`), and those bytes are
CFB8's of them.

Its contract (`cfb8KRISCV64 enc`) is the functions' (`cfb8RISCV64 enc`),
with the first 2048 bytes of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.AesCfb8.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes VG.Proof.Aes.RISCV64
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cfb8_encrypt` (`enc`) or `vg_aes_cfb8_decrypt`, with the
arguments `(schedule = a0, rounds = a1, iv = a2, data = a3, len = a4, scratch = a5)`. -/
def cfb8RISCV64 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let iv : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2176⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧
      iv.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    let ciph := Spec.Cbc.aesWith (s.gpr .a1).toNat (bytesAt s.mem (s.gpr .a0) (16 * ((s.gpr .a1).toNat + 1)))
    let iv := bytesAt s.mem (s.gpr .a2) 16
    let xs := bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat
    bytesAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat = cfb8 enc ciph iv xs ∧
      bytesAt s'.mem (s.gpr .a2) 16 = inK enc ciph iv xs
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

/-- The chain's contract: `cfb8RISCV64 enc`'s postcondition, with
`chain`'s precondition over `len` bytes (a scratch buffer of 2048 bytes). -/
def cfb8KRISCV64 (enc : Bool) : Contract isa where
  pre := framePre true id
  post := (cfb8RISCV64 enc).post
  pub := (cfb8RISCV64 enc).pub

/-! ## The input block -/

/-- The input block's two slots, as the registers of block 0. -/
abbrev slotQ (m : Mem) (b : Addr) : Nat → BitVec 64 :=
  fun i => if i = 0 then m.readW (b + BitVec.ofNat 64 464) 64 else m.readW (b + BitVec.ofNat 64 504) 64

/-- The input block shifted left by a byte, with the low byte of `c` shifted in. -/
theorem regBlock_shift (lo hi c : BitVec 64) :
    (regBlock (fun i => if i = 0 then lo >>> 8 ||| hi <<< 56 else hi >>> 8 ||| c <<< 56) 0).toList =
      (regBlock (fun i => if i = 0 then lo else hi) 0).toList.tail ++ [c.setWidth 8] := by
  apply List.ext_getElem (by simp)
  intro t h₁ h₂
  obtain ht : t < 16 := by simpa using h₁
  rw [Vector.getElem_toList]
  by_cases h15 : t < 15
  · rw [List.getElem_append_left (by simpa using h15), List.getElem_tail, Vector.getElem_toList]
    simp only [regBlock, Vector.getElem_ofFn, Nat.zero_add]
    refine byte_ext fun j hj => ?_
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
    by_cases h8 : t < 7
    · rw [show t / 8 = 0 by omega_using [h8], show (t + 1) / 8 = 0 by omega_using [h8]]
      simp only [Nat.mul_zero, ↓reduceIte, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_shiftLeft]
      rw [show 8 + (8 * (t % 8) + j) = 8 * ((t + 1) % 8) + j by omega_using [h8]]
      have : 8 * (t % 8) + j < 56 := by omega_using [hj, h8]
      simp [this]
    · by_cases h7 : t = 7
      · subst h7
        simp only [show 7 / 8 = 0 from rfl, show (7 + 1) / 8 = 1 from rfl, Nat.mul_zero, Nat.mul_one,
          ↓reduceIte, show (4 = 0) = False by decide, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
          BitVec.getLsbD_shiftLeft]
        rw [show (7 + 1) % 8 = 0 from rfl, show 7 % 8 = 7 from rfl]
        obtain e1 : (lo.getLsbD (8 + (8 * 7 + j))) = false := BitVec.getLsbD_of_ge _ _ (by omega_using [])
        rw [e1]
        simp [show ¬ (8 * 7 + j < 56) by omega_using [], show 8 * 7 + j < 64 by omega_using [hj], show 8 * 7 + j - 56 = j by omega_using []]
      · rw [show t / 8 = 1 by omega_using [ht, h8, h7], show (t + 1) / 8 = 1 by omega_using [h15, h8]]
        simp only [Nat.mul_one, show (4 = 0) = False by decide, ↓reduceIte, BitVec.getLsbD_or,
          BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
        rw [show 8 + (8 * (t % 8) + j) = 8 * ((t + 1) % 8) + j by omega_using [h15, h7]]
        have : 8 * (t % 8) + j < 56 := by omega_using [h15, hj, h7]
        simp [this]
  · have e : t = 15 := by omega_using [ht, h15]
    subst e
    rw [List.getElem_append_right (by simp)]
    simp only [regBlock, Vector.getElem_ofFn, Nat.zero_add]
    refine byte_ext fun j hj => ?_
    simp only [show 15 / 8 = 1 from rfl, show 15 % 8 = 7 from rfl, Nat.mul_one,
      show (4 = 0) = False by decide, ↓reduceIte, BitVec.getLsbD_extractLsb', hj, decide_true,
      Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    obtain e1 : (hi.getLsbD (8 + (8 * 7 + j))) = false := BitVec.getLsbD_of_ge _ _ (by omega_using [])
    rw [e1]
    simp [show ¬ (8 * 7 + j < 56) by omega_using [], show 8 * 7 + j < 64 by omega_using [hj], show 8 * 7 + j - 56 = j by omega_using [], hj]

/-- The first byte of the registers of block 0. -/
theorem regBlock_zero (Q : Nat → BitVec 64) : (regBlock Q 0)[0] = (Q 0).setWidth 8 := by
  simp only [regBlock, Vector.getElem_ofFn]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [hj]

/-- A data byte XORed with the low byte of a register. -/
theorem xor_low (x : Byte) (y : BitVec 64) :
    ((x.setWidth 64) ^^^ (y &&& BitVec.ofInt 64 255)).setWidth 8 = x ^^^ y.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_and, hj, decide_true, Bool.true_and,
    show j < 64 by omega_using [hj]]
  rw [show BitVec.ofInt 64 255 = BitVec.allOnes 64 >>> 56 by decide, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes]
  simp [show 56 + j < 64 by omega_using [hj]]

/-! ## The slots -/

section Slots

variable {s : State} {X b : Addr} (hscr : Scr s X 2048) (hb : s.gpr sb = b)
include hscr hb

theorem slot_in (d : Nat) (hd : d + 8 + 7 ≤ 2048) : (⟨X, 2048⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [← hb]; exact hscr.contains hd (by decide)

theorem slot_al (d : Nat) (hd : d % 8 = 0) : (b + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [← hb]; exact Align.al_add (k := 8) hscr.al (by decide) (by omega_using [hd])

/-- The input block from its slots into the registers of block 0. -/
theorem slots_load {Φ : State → Prop}
    (k : ∀ s', regBlock (Q s') 0 = regBlock (slotQ s.mem b) 0 →
      (∀ r, r ≠ q 0 → r ≠ q 4 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → Φ s') :
    WP isa (.block [ldS (q 0) iLo, ldS (q 4) iHi]) s Φ := by
  refine wp_ld (t := q 0) (n := sb) (off := 8 * iLo) (a := b + BitVec.ofNat 64 464) (by decide)
    (by rw [hb]; rfl) (slot_al hscr hb 464 (by decide))
    ⟨_, List.mem_append_right _ hscr.wr, slot_in hscr hb 464 (by decide)⟩ fun s₁ u₁ => ?_
  refine wp_ld (t := q 4) (n := sb) (off := 8 * iHi) (a := b + BitVec.ofNat 64 504) (by decide)
    (by rw [u₁.other _ (by decide), hb]; rfl) (slot_al hscr hb 504 (by decide))
    ⟨_, by rw [u₁.rd, u₁.wr]; exact List.mem_append_right _ hscr.wr, slot_in hscr hb 504 (by decide)⟩
    fun s₂ u₂ => WP.block_nil ?_
  refine k s₂ (regBlock_congr ?_ ?_) (fun r h0 h4 => by rw [u₂.other _ h4, u₁.other _ h0])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  · show s₂.gpr (q 0) = _
    rw [u₂.other _ (by decide), u₁.gpr]; rfl
  · show s₂.gpr (q 4) = _
    rw [u₂.gpr, u₁.mem]; rfl

/-- The registers of block 0 into the input block's slots. -/
theorem slots_store {Φ : State → Prop}
    (k : ∀ s', regBlock (slotQ s'.mem b) 0 = regBlock (Q s) 0 → (∀ r, s'.gpr r = s.gpr r) →
      s'.mem = (s.mem.writeW (b + BitVec.ofNat 64 464) (s.gpr (q 0))).writeW (b + BitVec.ofNat 64 504)
        (s.gpr (q 4)) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Φ s') :
    WP isa (.block [stS iLo (q 0), stS iHi (q 4)]) s Φ := by
  refine wp_sd (t := q 0) (n := sb) (off := 8 * iLo) (a := b + BitVec.ofNat 64 464) (by decide)
    (by rw [hb]; rfl) (slot_al hscr hb 464 (by decide)) ⟨_, hscr.wr, slot_in hscr hb 464 (by decide)⟩
    fun s₁ u₁ => ?_
  refine wp_sd (t := q 4) (n := sb) (off := 8 * iHi) (a := b + BitVec.ofNat 64 504) (by decide)
    (by rw [u₁.gpr, hb]; rfl) (slot_al hscr hb 504 (by decide))
    ⟨_, by rw [u₁.wr]; exact hscr.wr, slot_in hscr hb 504 (by decide)⟩ fun s₂ u₂ => WP.block_nil ?_
  obtain hm : s₂.mem = (s.mem.writeW (b + BitVec.ofNat 64 464) (s.gpr (q 0))).writeW (b + BitVec.ofNat 64 504)
      (s.gpr (q 4)) := by rw [u₂.mem, u₁.mem, u₁.gpr]
  refine k s₂ (regBlock_congr ?_ ?_) (fun r => by rw [u₂.gpr, u₁.gpr]) hm (by rw [u₂.rd, u₁.rd])
    (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  · show s₂.mem.readW (b + BitVec.ofNat 64 464) 64 = s.gpr (q 0)
    rw [hm, Mem.readW_writeW_sep (Offset.sep b (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_self64]
  · show s₂.mem.readW (b + BitVec.ofNat 64 504) 64 = s.gpr (q 4)
    rw [hm, Mem.readW_writeW_self64]

/-- The input block in its slots shifted left by a byte, with the low byte of
`t2` shifted in; on to the next byte. -/
theorem shift_ok {Φ : State → Prop}
    (k : ∀ s', (regBlock (slotQ s'.mem b) 0).toList =
        (regBlock (slotQ s.mem b) 0).toList.tail ++ [(s.gpr .t2).setWidth 8] →
      Frame [⟨b + BitVec.ofNat 64 464, 8⟩, ⟨b + BitVec.ofNat 64 504, 8⟩] s.mem s'.mem →
      s'.gpr .a3 = s.gpr .a3 + BitVec.ofNat 64 1 → s'.gpr .a4 = s.gpr .a4 - BitVec.ofNat 64 1 →
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ .t3 → r ≠ .a3 → r ≠ .a4 → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Φ s') :
    WP isa (.block cfb8Shift) s Φ := by
  unfold cfb8Shift
  refine wp_ld (t := t0) (n := sb) (off := 8 * iLo) (a := b + BitVec.ofNat 64 464) (by decide)
    (by rw [hb]; rfl) (slot_al hscr hb 464 (by decide))
    ⟨_, List.mem_append_right _ hscr.wr, slot_in hscr hb 464 (by decide)⟩ fun s₁ u₁ => ?_
  refine wp_ld (t := t1) (n := sb) (off := 8 * iHi) (a := b + BitVec.ofNat 64 504) (by decide)
    (by rw [u₁.other _ (by decide), hb]; rfl) (slot_al hscr hb 504 (by decide))
    ⟨_, by rw [u₁.rd, u₁.wr]; exact List.mem_append_right _ hscr.wr, slot_in hscr hb 504 (by decide)⟩
    fun s₂ u₂ => ?_
  refine wp_srl (by decide) fun s₃ u₃ => wp_sll (by decide) fun s₄ u₄ => wp_or fun s₅ u₅ => ?_
  refine wp_srl (by decide) fun s₆ u₆ => wp_sll (by decide) fun s₇ u₇ => wp_or fun s₈ u₈ => ?_
  obtain o₈ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ .t3 → s₈.gpr r = s.gpr r := fun r h0 h1 h3 => by
    rw [u₈.other _ h1, u₇.other _ h3, u₆.other _ h1, u₅.other _ h0, u₄.other _ h3, u₃.other _ h0,
      u₂.other _ h1, u₁.other _ h0]
  obtain m₈ : s₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain sp₈ : s₈.sp = s.sp := by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  let lo := s.mem.readW (b + BitVec.ofNat 64 464) 64
  let hi := s.mem.readW (b + BitVec.ofNat 64 504) 64
  obtain t0₈ : s₈.gpr t0 = lo >>> 8 ||| hi <<< 56 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr,
      u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
  obtain t1₈ : s₈.gpr t1 = hi >>> 8 ||| s.gpr .t2 <<< 56 := by
    rw [u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine wp_sd (t := t0) (n := sb) (off := 8 * iLo) (a := b + BitVec.ofNat 64 464) (by decide)
    (by rw [o₈ _ (by decide) (by decide) (by decide), hb]; rfl) (slot_al hscr hb 464 (by decide))
    ⟨_, by rw [wr₈]; exact hscr.wr, slot_in hscr hb 464 (by decide)⟩ fun s₉ u₉ => ?_
  refine wp_sd (t := t1) (n := sb) (off := 8 * iHi) (a := b + BitVec.ofNat 64 504) (by decide)
    (by rw [u₉.gpr, o₈ _ (by decide) (by decide) (by decide), hb]; rfl) (slot_al hscr hb 504 (by decide))
    ⟨_, by rw [u₉.wr, wr₈]; exact hscr.wr, slot_in hscr hb 504 (by decide)⟩ fun s₁₀ u₁₀ => ?_
  refine wp_addi (imm := 1) (by decide) fun s₁₁ u₁₁ => wp_subi (imm := 1) (by decide)
    fun s₁₂ u₁₂ => WP.block_nil ?_
  obtain hm : s₁₂.mem = (s.mem.writeW (b + BitVec.ofNat 64 464) (lo >>> 8 ||| hi <<< 56)).writeW
      (b + BitVec.ofNat 64 504) (hi >>> 8 ||| s.gpr .t2 <<< 56) := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₉.gpr, m₈, t0₈, t1₈]
  refine k s₁₂ ?_ ?_ ?_ ?_ (fun r h0 h1 h3 h3' h4 => ?_) (by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, rd₈])
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, wr₈]) (by rw [u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, sp₈])
  · rw [← regBlock_shift lo hi (s.gpr .t2)]
    refine congrArg Vector.toList (regBlock_congr ?_ ?_)
    · show s₁₂.mem.readW (b + BitVec.ofNat 64 464) 64 = _
      rw [hm, Mem.readW_writeW_sep (Offset.sep b (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
        Mem.readW_writeW_self64]; rfl
    · show s₁₂.mem.readW (b + BitVec.ofNat 64 504) 64 = _
      rw [hm, Mem.readW_writeW_self64]; rfl
  · rw [hm]
    exact ((Frame.refl _ _).writeW (r := ⟨b + BitVec.ofNat 64 464, 8⟩) (by simp) _
      (Region.contains_self _ 8)).writeW (r := ⟨b + BitVec.ofNat 64 504, 8⟩) (by simp) _
      (Region.contains_self _ 8)
  · rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.gpr, u₉.gpr, o₈ _ (by decide) (by decide) (by decide)]
  · rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, o₈ _ (by decide) (by decide) (by decide)]
  · rw [u₁₂.other _ h4, u₁₁.other _ h3', u₁₀.gpr, u₉.gpr, o₈ r h0 h1 h3]

end Slots

/-- `C#ⱼ` (if `enc`) or `P#ⱼ` (else) over the data byte at `a3`: the byte XORed
with the first byte of the registers of block 0, the ciphertext byte left
in `t2`. -/
theorem byte_ok (enc : Bool) {s : State} {P : Addr} (hP : s.gpr .a3 = P)
    (hin : InRegions s.wr P 1) {Φ : State → Prop}
    (k : ∀ s', s'.mem = s.mem.writeW P (s.mem P ^^^ (s.gpr (q 0)).setWidth 8) →
      (s'.gpr .t2).setWidth 8 = (if enc then s.mem P ^^^ (s.gpr (q 0)).setWidth 8 else s.mem P) →
      (∀ r, r ≠ t1 → r ≠ .t2 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Φ s') :
    WP isa (.block (if enc then cfb8Enc else cfb8Dec)) s Φ := by
  obtain hrw : InRegions (s.rd ++ s.wr) P 1 := by
    obtain ⟨r, hr, hc⟩ := hin; exact ⟨r, List.mem_append_right _ hr, hc⟩
  cases enc
  · unfold cfb8Dec
    refine wp_lbu (a := P) (by decide) (by rw [hP]; simp) hrw fun s₁ u₁ => ?_
    refine wp_andi (by decide) fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
    refine wp_sb (a := P) (by decide)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hP]; simp)
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hin) fun s₄ u₄ => WP.block_nil ?_
    obtain t1₃ : s₃.gpr t1 = (s.gpr (q 0) &&& BitVec.ofInt 64 255) ^^^ (s.mem P).setWidth 64 := by
      rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.other _ (by decide)]
    refine k s₄ ?_ ?_ (fun r h1 h2 => ?_) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp])
    · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, t1₃, BitVec.xor_comm, xor_low]
    · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp [hj]
    · rw [u₄.gpr, u₃.other _ h1, u₂.other _ h1, u₁.other _ h2]
  · unfold cfb8Enc
    refine wp_lbu (a := P) (by decide) (by rw [hP]; simp) hrw fun s₁ u₁ => ?_
    refine wp_andi (by decide) fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
    refine wp_sb (a := P) (by decide)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hP]; simp)
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hin) fun s₄ u₄ => WP.block_nil ?_
    obtain t2₃ : s₃.gpr .t2 = (s.mem P).setWidth 64 ^^^ (s.gpr (q 0) &&& BitVec.ofInt 64 255) := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.other _ (by decide)]
    refine k s₄ ?_ ?_ (fun r h1 h2 => ?_) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp])
    · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, t2₃, xor_low]
    · rw [u₄.gpr, t2₃, xor_low]; rfl
    · rw [u₄.gpr, u₃.other _ h2, u₂.other _ h1, u₁.other _ h2]

/-! ## The loop -/

theorem writeW8_self (m : Mem) (p : Addr) (v : Byte) : m.writeW p v p = v := by
  rw [AesCfb8.writeW8_apply, BitVec.sub_self]; simp

/-- Byte `D + j` after a byte store at `D + k`. -/
theorem writeW8_ne (m : Mem) (D : Addr) {j k : Nat} (hj : j < 2 ^ 64) (hk : k < 2 ^ 64) (h : j ≠ k)
    (v : Byte) : m.writeW (D + BitVec.ofNat 64 k) v (D + BitVec.ofNat 64 j) = m (D + BitVec.ofNat 64 j) := by
  rw [AesCfb8.writeW8_apply]
  have : ¬ ((D + BitVec.ofNat 64 j) - (D + BitVec.ofNat 64 k)).toNat < 1 := fun hc =>
    Offset.disjoint D (d := k) (n := 1) (e := j) (k := 1) (by omega_using [h]) (by omega_using [hk]) (by omega_using [hj]) _
      (by simp only [Region.Contains]; omega_using [hc]) (Region.contains_self _ _)
  simp only [this, ↓reduceIte]

theorem headD_toList (v : Spec.Aes.State) : v.toList.headD 0 = v[0] := by
  rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, Vector.getElem?_toList]; rfl

/-- What the loop runs with: `s₂` is the state after the input block is
stored in its slots, `X` the scratch buffer (rounded to `b`), `D` the data
(`n` bytes). -/
structure B8Setup (s₂ : State) (X b D : Addr) (n R : Nat) (w : List Byte) : Prop where
  scr : Scr s₂ X 2048
  base : s₂.gpr sb = b
  masks : MasksAt s₂.mem b allKs
  dat : (⟨D, n⟩ : Region) ∈ s₂.wr
  hn : n < 2 ^ 64
  sep : Region.Disjoint ⟨D, n⟩ ⟨X, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 64 (1920 - 64 * R)) R w
  a0 : s₂.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R)

section Loop

variable {m₀ : Mem} {s₂ : State} {X b D : Addr} {n R : Nat} {w iv : List Byte}

/-- The scratch buffer's regions `fRegions` has, within it. -/
theorem B8Setup.sub (hs : B8Setup s₂ X b D n R w) {d l : Nat} (h : d + l + 7 ≤ 2048) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨X, 2048⟩ := by
  rw [← hs.base]; exact hs.scr.sub h

theorem B8Setup.dX (hs : B8Setup s₂ X b D n R w) :
    ∀ r ∈ [(⟨b, 320⟩ : Region), ⟨b + BitVec.ofNat 64 464, 8⟩, ⟨b + BitVec.ofNat 64 504, 8⟩],
      Region.Disjoint ⟨D, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine hs.sep.sub_right ?_
    have := hs.sub (d := 0) (l := 320) (by omega_using [])
    simpa using this
  · exact hs.sep.sub_right (hs.sub (by omega_using []))
  · exact hs.sep.sub_right (hs.sub (by omega_using []))

theorem B8Setup.masks_disj (hs : B8Setup s₂ X b D n R w) : ∀ r ∈ fRegions b D n,
    Region.Disjoint ⟨b + BitVec.ofNat 64 416, 48⟩ r ∧
      Region.Disjoint ⟨b + BitVec.ofNat 64 512, 96⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨Offset.disjoint_base b (by omega_using []) (by omega_using []), Offset.disjoint_base b (by omega_using []) (by omega_using [])⟩
  · exact ⟨Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using []), Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])⟩
  · exact ⟨Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using []), Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])⟩
  · exact ⟨Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using []), Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])⟩
  · exact ⟨(hs.sep.sub_right (hs.sub (by omega_using []))).symm, (hs.sep.sub_right (hs.sub (by omega_using []))).symm⟩

theorem B8Setup.keys_disj (hs : B8Setup s₂ X b D n R w) :
    ∀ r ∈ fRegions b D n, Region.Disjoint ⟨b + 1024, 960⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact keys_disjoint b
  · exact Offset.disjoint b (d := 1024) (by omega_using []) (by omega_using []) (by omega_using [])
  · exact Offset.disjoint b (d := 1024) (by omega_using []) (by omega_using []) (by omega_using [])
  · exact Offset.disjoint b (d := 1024) (by omega_using []) (by omega_using []) (by omega_using [])
  · exact (hs.sep.sub_right (hs.sub (d := 1024) (l := 960) (by omega_using []))).symm

/-- The input block enciphered in the registers of block 0. -/
theorem enc8_ok (hs : B8Setup s₂ X b D n R w) {s : State}
    (keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s.gpr r = s₂.gpr r)
    (hwr : s.wr = s₂.wr) (hf : Frame (fRegions b D n) s₂.mem s.mem) :
    WP isa encrypt4 s fun s₅ => regBlock (Q s₅) 0 = Spec.Aes.cipher R w (regBlock (Q s) 0) ∧
      (∀ r, r ∉ sboxWrites → r ≠ kp → s₅.gpr r = s.gpr r) ∧ Frame [⟨b, 320⟩] s.mem s₅.mem ∧
      s₅.rd = s.rd ∧ s₅.wr = s.wr ∧ s₅.sp = s.sp := by
  obtain hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega_using [h]
  obtain hb : s.gpr sb = b := by rw [keep sb (by decide) (by decide) (by decide) (by decide), hs.base]
  obtain a0 : s.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [keep .a0 (by decide) (by decide) (by decide) (by decide)]; exact hs.a0
  obtain hp : EncPre s X R w :=
    ⟨hs.scr.congr hwr (by rw [hb, hs.base]), by rw [hb]; exact masks_frame hf hs.masks_disj hs.masks,
      hs.rounds, by rw [a0, hb], by rw [a0]; exact keysAt_frame hR hf hs.keys_disj hs.keys⟩
  refine WP.mono (encrypt4_ok hp (inRel_regBlock (Q s))) fun s₅ ⟨hc₅, hin₅⟩ =>
    ⟨regBlock_of_inRel hin₅ (by decide), hc₅.keep, by have := hc₅.frame; rw [hb] at this; exact this,
      hc₅.rd, hc₅.wr, hc₅.sp⟩

/-- After `k` bytes: the input block CFB8's after the first `k` bytes, which
are CFB8's of them, and the other bytes `m₀`'s. -/
structure BAt (enc : Bool) (m₀ : Mem) (s₂ : State) (b D : Addr) (n R : Nat) (w iv : List Byte) (k : Nat)
    (s : State) : Prop where
  hk : k ≤ n
  a3 : s.gpr .a3 = D + BitVec.ofNat 64 k
  a4 : s.gpr .a4 = BitVec.ofNat 64 (n - k)
  keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (fRegions b D n) s₂.mem s.mem
  inb : (regBlock (slotQ s.mem b) 0).toList = inK enc (Spec.Cbc.aesWith R w) iv ((bytesAt m₀ D n).take k)
  done : bytesAt s.mem D k = cfb8 enc (Spec.Cbc.aesWith R w) iv ((bytesAt m₀ D n).take k)
  rest : ∀ j, k ≤ j → j < n → s.mem (D + BitVec.ofNat 64 j) = m₀ (D + BitVec.ofNat 64 j)

theorem take_bytesAt (m : Mem) (D : Addr) {n k : Nat} (hk : k < n) :
    (bytesAt m D n).take (k + 1) = (bytesAt m D n).take k ++ [m (D + BitVec.ofNat 64 k)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [bytesAt]; omega_using [hk])]
  simp [bytesAt]

theorem bytesAt_succ (m : Mem) (D : Addr) (k : Nat) :
    bytesAt m D (k + 1) = bytesAt m D k ++ [m (D + BitVec.ofNat 64 k)] := by
  simp only [bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- One byte: from after `k` bytes to after `k + 1`. -/
theorem body8_ok (enc : Bool) (hs : B8Setup s₂ X b D n R w) (hiv : iv ≠ []) {k : Nat} (hkn : k < n)
    {s : State} (hi : BAt enc m₀ s₂ b D n R w iv k s) :
    WP isa (cfb8Body enc) s fun s' => isa.eval (.nonzero .a4) s' = some (decide (n - (k + 1) ≠ 0)) ∧
      BAt enc m₀ s₂ b D n R w iv (k + 1) s' := by
  have hn := hs.hn
  obtain hb : s.gpr sb = b := (hi.keep sb (by decide) (by decide) (by decide) (by decide)).trans hs.base
  obtain hscr : Scr s X 2048 := hs.scr.congr hi.wr (by rw [hb, hs.base])
  have dX := hs.dX
  unfold cfb8Body
  refine WP.seq (slots_load hscr hb fun s₁ st₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_)
  obtain keep₁ : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s₁.gpr r = s₂.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [o₁ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))]; exact hi.keep r h1 h2 h3 h4
  refine WP.seq (WP.mono (enc8_ok hs keep₁ (by rw [wr₁, hi.wr]) (by rw [m₁]; exact hi.frame))
    fun s₅ ⟨st₅, keep₅, fr₅, rd₅, wr₅, sp₅⟩ => ?_)
  rw [WP.block_append_iff (M := isa)]
  obtain a3₅ : s₅.gpr .a3 = D + BitVec.ofNat 64 k := by
    rw [keep₅ _ (by decide) (by decide), o₁ _ (by decide) (by decide)]; exact hi.a3
  obtain hDw : (⟨D, n⟩ : Region) ∈ s₅.wr := by rw [wr₅, wr₁, hi.wr]; exact hs.dat
  refine byte_ok enc a3₅ (in_off hDw (by omega_using [hkn]) hn) fun s₆ m₆ t2₆ o₆ rd₆ wr₆ sp₆ => ?_
  obtain hb₆ : s₆.gpr sb = b := by
    rw [o₆ _ (by decide) (by decide), keep₅ _ (by decide) (by decide), o₁ _ (by decide) (by decide), hb]
  obtain hscr₆ : Scr s₆ X 2048 := hscr.congr (by rw [wr₆, wr₅, wr₁]) (by rw [hb₆, hb])
  refine shift_ok hscr₆ hb₆ fun s₇ inb₇ fr₇ a3₇ a4₇ o₇ rd₇ wr₇ sp₇ => ?_
  -- The data byte, and the first byte of the enciphered input block.
  let P := D + BitVec.ofNat 64 k
  let ciph := Spec.Cbc.aesWith R w
  let xs := (bytesAt m₀ D n).take k
  obtain x₅ : s₅.mem P = m₀ P := by
    obtain e := fr₅.bytes (R := ⟨D, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dX _ (by simp)) (by simp only; omega_using [hn]) hkn
    rw [e, m₁]; exact hi.rest k (Nat.le_refl _) hkn
  obtain c₅ : (s₅.gpr (q 0)).setWidth 8 = (ciph (inK enc ciph iv xs)).headD 0 := by
    rw [← hi.inb, show ciph = Spec.Cbc.aesWith R w from rfl, aesWith_toList, headD_toList, ← st₁, ← st₅,
      regBlock_zero]
  -- The slots, unchanged until the shift.
  obtain sl₆ : regBlock (slotQ s₆.mem b) 0 = regBlock (slotQ s.mem b) 0 := by
    obtain hd : ∀ d, d = 464 ∨ d = 504 → s₆.mem.readW (b + BitVec.ofNat 64 d) 64 =
        s.mem.readW (b + BitVec.ofNat 64 d) 64 := fun d hd => by
      obtain hsl : Region.Disjoint ⟨b + BitVec.ofNat 64 d, 8⟩ ⟨D, n⟩ := (dX _ (by rcases hd with rfl | rfl <;> simp)).symm
      obtain hsP : Region.Disjoint ⟨b + BitVec.ofNat 64 d, 8⟩ ⟨P, 1⟩ :=
        hsl.sub_right (Offset.sub_base D (by omega_using [hkn]))
      rw [m₆, Mem.readW_writeW_sep (fun x h₁ h₂ => hsP x h₁ h₂) (by decide),
        fr₅.readW (r := ⟨b + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rcases hd with rfl | rfl
          · exact Offset.disjoint_base b (by omega_using []) (by omega_using [])
          · exact Offset.disjoint_base b (by omega_using []) (by omega_using [])) (by decide), m₁]
    exact regBlock_congr (hd 464 (.inl rfl)) (hd 504 (.inr rfl))
  -- Bytes other than `P`, unchanged.
  obtain other : ∀ j < n, j ≠ k → s₇.mem (D + BitVec.ofNat 64 j) = s.mem (D + BitVec.ofNat 64 j) := by
    intro j hj hjk
    obtain e₇ := fr₇.bytes (R := ⟨D, n⟩) (fun r hr => dX r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)) (by simp only; omega_using [hn]) hj
    obtain e₅ := fr₅.bytes (R := ⟨D, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dX _ (by simp)) (by simp only; omega_using [hn]) hj
    simp only at e₇ e₅
    rw [e₇, m₆, writeW8_ne _ D (by omega_using [hn, hj]) (by omega_using [hkn, hn]) hjk, e₅, m₁]
  obtain self₇ : s₇.mem P = m₀ P ^^^ (ciph (inK enc ciph iv xs)).headD 0 := by
    obtain e₇ := fr₇.bytes (R := ⟨D, n⟩) (fun r hr => dX r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)) (by simp only; omega_using [hn]) hkn
    simp only at e₇
    rw [e₇, m₆, writeW8_self, x₅, c₅]
  obtain tk := take_bytesAt m₀ D hkn
  have x₀ : (bytesAt m₀ D n).take (k + 1) = xs ++ [m₀ P] := tk
  refine ⟨Steps.eval_nonzero_ofNat s₇ .a4 (by omega_using [hn]) ?a4, ?_⟩
  case a4 =>
    rw [a4₇, o₆ _ (by decide) (by decide), keep₅ _ (by decide) (by decide), o₁ _ (by decide) (by decide),
      hi.a4, ofNat_sub_ofNat' (by omega_using [hkn]), show n - k - 1 = n - (k + 1) by omega_using []]
  refine ⟨by omega_using [hkn], ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [rd₇, rd₆, rd₅, rd₁, hi.rd],
    by rw [wr₇, wr₆, wr₅, wr₁, hi.wr], by rw [sp₇, sp₆, sp₅, sp₁, hi.sp], ?_, ?_, ?_, ?_⟩
  · rw [a3₇, o₆ _ (by decide) (by decide), a3₅, Offset.add_add]
  · rw [a4₇, o₆ _ (by decide) (by decide), keep₅ _ (by decide) (by decide), o₁ _ (by decide) (by decide),
      hi.a4, ofNat_sub_ofNat' (by omega_using [hkn]), show n - k - 1 = n - (k + 1) by omega_using []]
  · rw [o₇ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)) h3 h4,
      o₆ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)), keep₅ r h1 h2]
    exact keep₁ r h1 h2 h3 h4
  · -- The frame.
    obtain f₆ : Frame (fRegions b D n) s₂.mem s₆.mem := by
      rw [m₆]
      refine ((hi.frame.trans (m₁ ▸ fr₅.mono fun r hr => by simp at hr; simp [hr]))).writeW
        (r := ⟨D, n⟩) (by simp) _ ?_
      show Region.Contains _ (D + BitVec.ofNat 64 k) 1
      exact Offset.contains_base D (by omega_using [hkn]) (by omega_using [hkn, hn])
    exact f₆.trans (fr₇.mono fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  · rw [inb₇, sl₆, hi.inb, x₀, inK_snoc enc ciph hiv]
    refine congrArg (fun x => (inK enc ciph iv xs).tail ++ [x]) ?_
    rw [t2₆, x₅, c₅]
  · rw [bytesAt_succ, x₀, cfb8_snoc enc ciph hiv, ← hi.done, self₇]
    refine congrArg (· ++ [m₀ P ^^^ (ciph (inK enc ciph iv xs)).headD 0]) ?_
    simp only [bytesAt]
    refine List.map_congr_left fun j hj => other j (by simp at hj; omega_using [hkn, hj]) (by simp at hj; omega_using [hj])
  · intro j hj hjn
    rw [other j hjn (by omega_using [hj])]; exact hi.rest j (by omega_using [hj]) hjn

/-- The loop over the bytes. -/
theorem loop8_ok (enc : Bool) (hs : B8Setup s₂ X b D n R w) (hiv : iv ≠ []) (hn0 : 0 < n) {s : State}
    (hi : BAt enc m₀ s₂ b D n R w iv 0 s) :
    WP isa (.loop (cfb8Body enc) (.nonzero .a4)) s (BAt enc m₀ s₂ b D n R w iv n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ BAt enc m₀ s₂ b D n R w iv k s)
    (fun m s ⟨k, hm, hk, h⟩ => WP.mono (body8_ok enc hs hiv hk h) fun s' ⟨ev, h'⟩ => ?_) n s
    ⟨0, by omega_using [], hn0, hi⟩
  by_cases hl : n - (k + 1) = 0
  · have e : k + 1 = n := by omega_using [hk, hl]
    exact .inl ⟨by rw [ev]; simp [hl], e ▸ h'⟩
  · exact .inr ⟨by rw [ev]; simp [hl], n - (k + 1), by omega_using [hm, hk], k + 1, rfl, by omega_using [hl], h'⟩

end Loop

/-! ## The whole function -/

/-- The input block's slots, outside the masks and the round keys. -/
theorem slots_disj (b : Addr) :
    ∀ r ∈ [(⟨b + BitVec.ofNat 64 464, 8⟩ : Region), ⟨b + BitVec.ofNat 64 504, 8⟩],
      (Region.Disjoint ⟨b + BitVec.ofNat 64 416, 48⟩ r ∧ Region.Disjoint ⟨b + BitVec.ofNat 64 512, 96⟩ r) ∧
        Region.Disjoint ⟨b + 1024, 960⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using []), Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])⟩,
      Offset.disjoint b (d := 1024) (by omega_using []) (by omega_using []) (by omega_using [])⟩
  · exact ⟨⟨Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using []), Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])⟩,
      Offset.disjoint b (d := 1024) (by omega_using []) (by omega_using []) (by omega_using [])⟩

theorem frame_slots (m : Mem) (b : Addr) (v₁ v₂ : BitVec 64) :
    Frame [⟨b + BitVec.ofNat 64 464, 8⟩, ⟨b + BitVec.ofNat 64 504, 8⟩] m
      ((m.writeW (b + BitVec.ofNat 64 464) v₁).writeW (b + BitVec.ofNat 64 504) v₂) :=
  ((Frame.refl _ _).writeW (r := ⟨b + BitVec.ofNat 64 464, 8⟩) (by simp) _
    (Region.contains_self _ 8)).writeW (r := ⟨b + BitVec.ofNat 64 504, 8⟩) (by simp) _
    (Region.contains_self _ 8)

theorem cfb8Chain_correct (enc : Bool) {s₀ : State} (hp : (cfb8KRISCV64 enc).pre s₀) :
    WP isa (cfb8Chain enc) s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (cfb8KRISCV64 enc).post s₀ s' := by
  let n := (s₀.gpr .a4).toNat
  let R := (s₀.gpr .a1).toNat
  let St := s₀.gpr .a2
  let D := s₀.gpr .a3
  let w := bytesAt s₀.mem (s₀.gpr .a0) (16 * (R + 1))
  let iv := bytesAt s₀.mem St 16
  have hp' : framePre true id s₀ := hp
  have dDSt : Region.Disjoint ⟨D, n⟩ ⟨St, 16⟩ := hp.2.2.2.1
  obtain hiv : iv ≠ [] := fun h => by simpa [iv, bytesAt] using congrArg List.length h
  obtain hn : n < 2 ^ 64 := (s₀.gpr .a4).isLt
  let Res : State → Prop := fun s =>
    (regBlock (Q s) 0).toList = inK enc (Spec.Cbc.aesWith R w) iv (bytesAt s₀.mem D n) ∧
      bytesAt s.mem D n = cfb8 enc (Spec.Cbc.aesWith R w) iv (bytesAt s₀.mem D n)
  obtain hlen : (bytesAt s₀.mem D n).length ≤ n := by simp [bytesAt]
  unfold cfb8Chain
  refine WP.mono (frame_wp (Res := Res) hp' fun s₉ X b hsF => ?_) fun s' ⟨hg, hra, hm⟩ => ⟨hg, hra, ?_⟩
  · have hR : R ≤ 14 := by rcases hsF.rounds with h | h | h <;> omega
    refine slots_store hsF.scr hsF.base fun s₂ sl₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
    obtain f₂ : Frame [⟨b + BitVec.ofNat 64 464, 8⟩, ⟨b + BitVec.ofNat 64 504, 8⟩] s₉.mem s₂.mem := by
      rw [m₂]; exact frame_slots _ _ _ _
    obtain sd := slots_disj b
    obtain hs : B8Setup s₂ X b D n R w :=
      { scr := hsF.scr.congr wr₂ (by rw [g₂])
        base := by rw [g₂]; exact hsF.base
        masks := masks_frame f₂ (fun r hr => (sd r hr).1) hsF.masks
        dat := by rw [wr₂]; exact hsF.dat rfl
        hn := hn
        sep := hsF.sep
        rounds := hsF.rounds
        keys := keysAt_frame hR f₂ (fun r hr => (sd r hr).2) hsF.keys
        a0 := by rw [g₂]; exact hsF.a0 }
    have dX := hs.dX
    obtain bi₀ : BAt enc s₀.mem s₂ b D n R w iv 0 s₂ :=
      { hk := Nat.zero_le _
        a3 := by rw [g₂, hsF.a3]; simp [D]
        a4 := by rw [g₂, hsF.a4]; simp [n]
        keep := fun _ _ _ _ _ => rfl
        rd := rfl
        wr := rfl
        sp := rfl
        frame := Frame.refl _ _
        inb := by
          rw [List.take_zero, inK_nil, sl₂, hsF.st, ← AesCbc.bytesAt_toList]
        done := by rw [List.take_zero, cfb8_nil]; rfl
        rest := fun j _ hj => by
          obtain e₂ := f₂.bytes (R := ⟨D, n⟩) (fun r hr => dX r (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
            (by simp only; omega_using []) hj
          obtain e₀ := hsF.f₀.bytes (R := ⟨D, n⟩) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact hsF.sep) (by simp only; omega_using []) hj
          simp only at e₂ e₀
          rw [e₂, e₀] }
    refine WP.mono (loop8_ok enc hs hiv hsF.hn0 bi₀) fun s₃ c => ?_
    obtain hb₃ : s₃.gpr sb = b := (c.keep sb (by decide) (by decide) (by decide) (by decide)).trans hs.base
    refine slots_load (hs.scr.congr c.wr (by rw [hb₃, hs.base])) hb₃ fun s₄ st₄ o₄ m₄ rd₄ wr₄ sp₄ => ?_
    exact { base := by rw [o₄ _ (by decide) (by decide)]; exact hb₃
            ra := by
              rw [o₄ _ (by decide) (by decide), c.keep .ra (by decide) (by decide) (by decide) (by decide), g₂]
            rd := by rw [rd₄, c.rd, rd₂]
            wr := by rw [wr₄, c.wr, wr₂]
            sp := by rw [sp₄, c.sp, sp₂]
            frame := by
              rw [m₄]
              refine (f₂.mono fun r hr => ?_).trans c.frame
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
              rcases hr with rfl | rfl <;> simp
            res := ⟨by rw [st₄, c.inb, List.take_of_length_le hlen],
              by rw [m₄, c.done, List.take_of_length_le hlen]⟩ }
  · show bytesAt s'.mem D n = cfb8 enc (Spec.Cbc.aesWith R w) iv (bytesAt s₀.mem D n) ∧
      bytesAt s'.mem St 16 = inK enc (Spec.Cbc.aesWith R w) iv (bytesAt s₀.mem D n)
    rcases hm with ⟨hn0, hmem⟩ | ⟨s, ⟨hst, hdat⟩, hmem⟩
    · rw [hmem, show n = 0 from hn0, show bytesAt s₀.mem D 0 = [] from rfl, cfb8_nil, inK_nil]
      exact ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hmem, AesCbc.RISCV64.bytesAt_frame (frame_writeW2 _ _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dDSt) (by omega_using []), hdat]
    · rw [hmem, bytesAt_writeW2 _ _ _ _ (regBlock_bytes (Q := Q s) rfl), hst]

/-! ## Constant time, and the call -/

theorem cfb8_agree (enc : Bool) :
    ∀ s₁ s₂, (cfb8KRISCV64 enc).pre s₁ → (cfb8KRISCV64 enc).pre s₂ → (cfb8KRISCV64 enc).pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) s₁ s₂ := by
  rintro s₁ s₂ - - ⟨h0, h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5]

theorem cfb8Chain_ct (enc : Bool) :
    ConstantTime isa (cfb8KRISCV64 enc).pre (cfb8KRISCV64 enc).pub (cfb8Chain enc) := by
  cases enc
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
      (cfb8_agree _) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
      (cfb8_agree _) (by taint_decide)

/-- The chain, as a chain to call. -/
theorem cfb8Chain_k (enc : Bool) : AesCbc.RISCV64.ChainK true id (cfb8KRISCV64 enc) (cfb8Chain enc) where
  pre _ h := h
  pub_of _ _ h := h
  correct s hs := by
    obtain ⟨t, s', he, hg, hra, hp⟩ := cfb8Chain_correct enc hs
    exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩
  ct := cfb8Chain_ct enc
  noFrames := by cases enc <;> rfl
  post {s₀ s t t'} h hg hm ht hp := by
    obtain g0 := hg .a0 (by simp)
    obtain g1 := hg .a1 (by simp)
    obtain g2 := hg .a2 (by simp)
    obtain g3 := hg .a3 (by simp)
    obtain g4 := hg .a4 (by simp)
    have edata : bytesAt (AesCbc.RISCV64.chMem s₀) (s₀.gpr .a3) (s₀.gpr .a4).toNat =
        bytesAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat := h.data_eq
    simp only [cfb8KRISCV64, cfb8RISCV64, g0, g1, g2, g3, g4, hm, ht] at hp ⊢
    rw [h.sch_eq, h.iv_eq, edata] at hp
    exact hp

end VG.Proof.AesCfb8.RISCV64

end

end

/-!
# AES-CFB8 on RISC-V: `Verified`

Correctness and constant time, from the CFB8 chain's (`Chain.lean`) and its
call's (`wrap_wp`, `wrap_ct`, `Proof/AesCbc/RISCV64/Chain.lean`), a state
satisfying the precondition, and the shared contracts of
`Spec/Cfb8/Contract.lean` (with no stack: a call stores nothing in memory,
and the return address is saved in the scratch buffer).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.RISCV64

open VG VG.RISCV64 VG.Impl.AesCfb8.RISCV64
open VG.Proof.AesCbc.RISCV64 (sat wrap_wp wrap_ct)

/-- The precondition, a chain's that writes the bytes (with the scratch buffer of 2176 bytes). -/
theorem wpre {enc : Bool} {s : State} (hs : (cfb8RISCV64 enc).pre s) :
    Proof.AesCbc.RISCV64.WPre true id s :=
  let ⟨a, b, c, _, e, f, g, h, i, j, k, l⟩ := hs
  ⟨a, b, c, e, f.symm, h, g, i, j, k, l⟩

theorem encrypt_correct (s : State) (hs : (cfb8RISCV64 true).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (cfb8RISCV64 true).post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ :=
    wrap_wp (cfb8Chain_k true) (name := "vg_aes_cfb8_enc_chain") (wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (cfb8RISCV64 false).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (cfb8RISCV64 false).post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ :=
    wrap_wp (cfb8Chain_k false) (name := "vg_aes_cfb8_dec_chain") (wpre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem encrypt_ct : ConstantTime isa (cfb8RISCV64 true).pre (cfb8RISCV64 true).pub encrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    wrap_ct (cfb8Chain_k true) "vg_aes_cfb8_enc_chain" _ _ _ _ _ _ (wpre h₁) (wpre h₂) hq e₁ e₂

theorem decrypt_ct : ConstantTime isa (cfb8RISCV64 false).pre (cfb8RISCV64 false).pub decrypt :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    wrap_ct (cfb8Chain_k false) "vg_aes_cfb8_dec_chain" _ _ _ _ _ _ (wpre h₁) (wpre h₂) hq e₁ e₂

theorem encrypt_verified : Verified RISCV64.target encrypt (Proof.AesCfb8.encryptRoundsContract RISCV64.abi) :=
  Verified.of_correct encrypt_correct encrypt_ct (by
    sig_implies [Proof.AesCfb8.encryptRoundsContract, Spec.Cfb8.aesSig, cfb8RISCV64, cfb8, cts, inK, RISCV64.abi,
      RISCV64.argRegs] [sat] using sat)

theorem decrypt_verified : Verified RISCV64.target decrypt (Proof.AesCfb8.decryptRoundsContract RISCV64.abi) :=
  Verified.of_correct decrypt_correct decrypt_ct (by
    sig_implies [Proof.AesCfb8.decryptRoundsContract, Spec.Cfb8.aesSig, cfb8RISCV64, cfb8, cts, inK, RISCV64.abi,
      RISCV64.argRegs] [sat] using sat)

end VG.Proof.AesCfb8.RISCV64

end

end

/-! ### `AesCbc.RISCV64.Wiped`, which only this module used -/

section

/-!
# AES-CBC on RISC-V, zeroing the scratch it writes

`vg_aes_cbc_encrypt` and `vg_aes_cbc_decrypt` call their code, as the
internal functions `vg_aes_cbc_{en,de}crypt_unwiped`, by `callWipe`, which
then zeroes the whole of `scratch` with `vg_zeroize`. Each meets its contract
and leaves each byte of `scratch` unchanged or zero (`*_scrubbed`), which
is the contract of `Spec/Cbc/` (`*_verified`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64.Wiped

open VG VG.RISCV64 VG.Proof.AesCbc.Wipe

theorem sdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : sdepth c = 0 := by
  induction c <;> simp_all [Code.noFrames, sdepth]

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
2176 bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.RISCV64.callWipe .a5 2176 name body "vg_zeroize" Impl.Zeroize.RISCV64.zeroize

/-- `vg_aes_cbc_encrypt`, wiping `scratch`. -/
def encrypt : Prog isa := wiped "vg_aes_cbc_encrypt_unwiped" Impl.AesCbc.RISCV64.encrypt

/-- `vg_aes_cbc_decrypt`, wiping `scratch`. -/
def decrypt : Prog isa := wiped "vg_aes_cbc_decrypt_unwiped" Impl.AesCbc.RISCV64.decrypt

theorem sat (P : Spec.Cbc.aesSig.Post 64) :
    ∃ s, (Spec.Cbc.aesSig.contract abi (pre 64) P false 32 none).pre s := by
  implies_sat [Spec.Cbc.aesSig, pre, RISCV64.abi, RISCV64.argRegs] [Proof.AesCbc.RISCV64.sat]
    using Proof.AesCbc.RISCV64.sat

theorem wiped_verified {P : Spec.Cbc.aesSig.Post 64} {name : String} {body : Prog isa}
    (h : Verified target body (Spec.Cbc.aesSig.contract abi (pre 64) P false 0 none))
    (hd : body.noFrames = true)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (Spec.Cbc.aesSig.words 64).length →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words 64) P vs m₁ m' x → Curry.apply (Spec.Cbc.aesSig.words 64) P vs m₂ m' x)
    (hout : ∀ vs m m₁ m₂ x, vs.length = (Spec.Cbc.aesSig.words 64).length →
      (Sig.bufs Spec.Cbc.aesSig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs Spec.Cbc.aesSig.params vs, b.1.Disjoint ⟨vs.getD 5 0, 272 * Elem.u64.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (Spec.Cbc.aesSig.words 64) P vs m m₁ x → Curry.apply (Spec.Cbc.aesSig.words 64) P vs m m₂ x) :
    Verified target (wiped name body)
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 P) false 32 none) :=
  Verified.callWipe' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("iv", .array true .u8 16), ("data", .slice true (.array .u8 16) "n")]) (ps₂ := [])
    (nm := "scratch") (e := .u64) (k := 272) (n := 2176) (i := 5) h Proof.Zeroize.RISCV64.verified
    (by decide) rfl rfl rfl (by decide) (by decide) (by rw [sdepth_of_noFrames hd])
    (by rw [sdepth_of_noFrames (by decide)]) (Nat.zero_le _)
    (pre_local 64) hpost hout (Wipe.wiped 64 P) (sat _)

theorem encrypt_scrubbed :
    Verified target encrypt
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (encPost 64)) false 32 none) :=
  wiped_verified (Proof.AesCbc.encrypt_keyed Proof.AesCbc.RISCV64.encrypt_verified) (by lit_decide)
    (encPost_local 64) (encPost_out 64)

theorem decrypt_scrubbed :
    Verified target decrypt
      (Spec.Cbc.aesSig.contract abi (pre 64) (scrubbedPost 64 (decPost 64)) false 32 none) :=
  wiped_verified (Proof.AesCbc.decrypt_keyed Proof.AesCbc.RISCV64.decrypt_verified) (by lit_decide)
    (decPost_local 64) (decPost_out 64)

theorem encrypt_verified : Verified target encrypt (Spec.Cbc.aesEncryptContract abi 32) :=
  encrypt_scrubbed

theorem decrypt_verified : Verified target decrypt (Spec.Cbc.aesDecryptContract abi 32) :=
  decrypt_scrubbed

end VG.Proof.AesCbc.RISCV64.Wiped

end

end

/-! ### `Aes.RISCV64.Frame`, which only this module used -/

section

/-!
# The AES key expansion on RISC-V, with its working space on the stack

`vg_aes_expand_key` runs the code of `vg_aes_expand_key_scratch`, proved with
the working space as an argument, in a frame that allocates it and zeroes it
after the code (`Verified.stackScratchWiped`), since it may hold the key and
its schedule: 512 bytes, all working space. The code uses no other stack.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64

/-- A state satisfying `vg_aes_expand_key`'s precondition: a 16-byte key at
`0x1000` and the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 16 | .a2 => 0x2000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 240⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Aes.expandKeyContract RISCV64.abi 512).pre s := by
  implies_sat [Spec.Aes.expandKeyContract, Spec.Aes.expandKeySig, Spec.Aes.expandKeyPre,
    Spec.Aes.expandKeyPost, RISCV64.abi, RISCV64.argRegs] [expandKeyFrameSat] using expandKeyFrameSat

theorem expandKey_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a3 64 Impl.Aes.RISCV64.expandKey)
      (Spec.Aes.expandKeyContract RISCV64.abi 512) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Aes.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 64) (pre := Spec.Aes.expandKeyPre RISCV64.abi.ptrBits)
    (post := Spec.Aes.expandKeyPost RISCV64.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 512) (words := 64) (Proof.Aes.expandKey_scratch expandKey_verified) (by decide)
    (by decide) (by decide) (Proof.Aes.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Aes.RISCV64

end

end

/-! ### `AesEcb.RISCV64`, which only this module used -/

section

/-!
# AES-ECB on RISC-V

`vg_aes_ecb_encrypt` and `vg_aes_ecb_decrypt` call `vg_aes_encrypt_blocks`
and `vg_aes_decrypt_blocks`, which write `scratch`, by `callWipe`, which then
zeroes the whole of `scratch` with `vg_zeroize`.
-/

@[expose] public section

namespace VG.Proof.AesEcb.RISCV64

open VG VG.RISCV64

theorem sdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : sdepth c = 0 := by
  induction c <;> simp_all [Code.noFrames, sdepth]

/-- A call of `name`, whose code is `body`, then of `vg_zeroize` on the
2048 bytes of `scratch`. -/
def wiped (name : String) (body : Prog isa) : Prog isa :=
  Impl.CallWipe.RISCV64.callWipe .a4 2048 name body "vg_zeroize" Impl.Zeroize.RISCV64.zeroize

/-- `vg_aes_ecb_encrypt`. -/
def encrypt : Prog isa := wiped "vg_aes_encrypt_blocks" Impl.Aes.RISCV64.encryptBlocks

/-- `vg_aes_ecb_decrypt`. -/
def decrypt : Prog isa := wiped "vg_aes_decrypt_blocks" Impl.Aes.RISCV64.decryptBlocks

theorem sat (g : List Byte → Spec.Aes.State → Spec.Aes.State) :
    ∃ s, (Spec.Aes.blocksSig.contract abi (pre 64) (ecbPost 64 g) false 32 none).pre s := by
  implies_sat [Spec.Aes.blocksSig, pre, RISCV64.abi, RISCV64.argRegs] [Proof.Aes.RISCV64.blocksSat]
    using Proof.Aes.RISCV64.blocksSat

theorem wiped_verified {g : List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {body : Prog isa}
    (h : Verified target body (Spec.Aes.blocksSig.contract abi (pre 64) (post 64 g) false 0 none))
    (hd : body.noFrames = true) :
    Verified target (wiped name body) (Spec.Aes.blocksSig.contract abi (pre 64) (ecbPost 64 g) false 32 none) :=
  Verified.callWipe' (ps₁ := [("schedule", .array false .u8 240), ("rounds", .int .usize true),
      ("data", .slice true (.array .u8 16) "n")]) (ps₂ := []) (nm := "scratch") (e := .u64)
    (k := 256) (n := 2048) (i := 4) h Proof.Zeroize.RISCV64.verified (by decide) rfl rfl rfl
    (by decide) (by decide) (by rw [sdepth_of_noFrames hd])
    (by rw [sdepth_of_noFrames (by decide)]) (Nat.zero_le _)
    (pre_local 64) (post_local 64 g) (post_out 64 g) (AesEcb.wiped 64 g) (sat g)

theorem encrypt_verified : Verified target encrypt (Spec.AesEcb.encryptContract abi 32) :=
  wiped_verified (Proof.Aes.encryptBlocks_keyed Proof.Aes.RISCV64.encryptBlocks_verified) (by lit_decide)

theorem decrypt_verified : Verified target decrypt (Spec.AesEcb.decryptContract abi 32) :=
  wiped_verified (Proof.Aes.decryptBlocks_keyed Proof.Aes.RISCV64.decryptBlocks_verified) (by lit_decide)

end VG.Proof.AesEcb.RISCV64

end

end

/-!
# AES and its modes on RISC-V, without secret residue

`vg_aes_expand_key`, `vg_aes_ecb_encrypt`, `vg_aes_ecb_decrypt`,
`vg_aes_cbc_encrypt`, `vg_aes_cbc_decrypt`, `vg_aes_ctr`,
`vg_aes_ctr_final`, `vg_aes_cfb128_encrypt`, `vg_aes_cfb128_decrypt`, their
`_final` functions, `vg_aes_cfb8_encrypt`, `vg_aes_cfb8_decrypt`,
`vg_aes_ofb` and `vg_aes_ofb_final`, each followed by
`Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.withScrub`), which clears the
caller-saved registers and the stack its frames used. Their postconditions
read the memory on return only within their buffers
(`RISCV64.Scrub.PostOut`), as on x86-64 (`Proof/Aes/X86_64/Scrub.lean`,
`Proof/AesEcb/X86_64.lean`, `Proof/AesCbc/X86_64/Wiped.lean`,
`Proof/Aes/X86_64/ModesScrub.lean`, `Proof/Aes/X86_64/FinalScrub.lean`).
The `_final` functions call the code of the whole-block ones as internal
functions of their own, `vg_aes_ctr_core`, ….

The key expansion and the final partial-block functions of CTR, CFB and OFB instead clear only the runs of doublewords that the residue
analysis (`RISCV64.rtaint`) finds may differ between two runs
(`RISCV64.Scrub.withScrubSel`, `scrubSel_noResidue`). Their code wipes most of
its own scratch space, which leaves few such doublewords, or none.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Aes.expandKeyContract RISCV64.abi stack) (Spec.Aes.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Aes.expandKeyPostOut_local _)

theorem len_le (x : BitVec 64) (k : Nat) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len_le1 (x : BitVec 64) : ((ArgWord.int abi.ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

namespace Ecb

open VG.Proof.AesEcb

/-- The postcondition of `vg_aes_ecb_encrypt` reads the memory on return only
within the buffers. -/
theorem encryptOut (stack : Nat) :
    PostOut (Spec.AesEcb.encryptContract abi stack) (Spec.Aes.blocksSig.retBits 64) := by
  rw [Proof.AesEcb.encrypt_eq]
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · show Spec.Aes.statesAt m₂ c (d.setWidth abi.ptrBits).toNat = _
      have hd := agree_of hb.2.1
      rw [statesAt_congr fun i hi => hd i (by have := n_le (pb := abi.ptrBits) d; omega_using [hi, this])]
      exact h1 key hk
    · rw [← hb.2.2 z hz]
      exact h2 z hz

/-- The postcondition of `vg_aes_ecb_decrypt` reads the memory on return only
within the buffers. -/
theorem decryptOut (stack : Nat) :
    PostOut (Spec.AesEcb.decryptContract abi stack) (Spec.Aes.blocksSig.retBits 64) := by
  rw [Proof.AesEcb.decrypt_eq]
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · show Spec.Aes.statesAt m₂ c (d.setWidth abi.ptrBits).toNat = _
      have hd := agree_of hb.2.1
      rw [statesAt_congr fun i hi => hd i (by have := n_le (pb := abi.ptrBits) d; omega_using [hi, this])]
      exact h1 key hk
    · rw [← hb.2.2 z hz]
      exact h2 z hz

end Ecb

namespace Cbc

open VG.Proof.AesCbc.Wipe

/-- The postcondition of `vg_aes_cbc_encrypt` reads the memory on return only
within the buffers. -/
theorem encryptOut (stack : Nat) :
    PostOut (Spec.Cbc.aesEncryptContract abi stack) (Spec.Cbc.aesSig.retBits 64) := by
  rw [Proof.AesCbc.Wipe.encrypt_eq]
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    have hd := AesEcb.agree_of hb.2.2.1
    have hb' : Spec.Cbc.blocksAt m₂ d (e.setWidth abi.ptrBits).toNat = Spec.Cbc.blocksAt m₁ d (e.setWidth abi.ptrBits).toNat :=
      blocksAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) e; omega_using [hi, this])
    have hc := AesEcb.bytesAt_congr (AesEcb.agree_of hb.2.1)
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · obtain ⟨h1a, h1b⟩ := h1 key hk
      exact ⟨hb'.trans h1a, hc.trans h1b⟩
    · rw [← hb.2.2.2 z hz]
      exact h2 z hz

/-- The postcondition of `vg_aes_cbc_decrypt` reads the memory on return only
within the buffers. -/
theorem decryptOut (stack : Nat) :
    PostOut (Spec.Cbc.aesDecryptContract abi stack) (Spec.Cbc.aesSig.retBits 64) := by
  rw [Proof.AesCbc.Wipe.decrypt_eq]
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ x hlen hb h => by
    obtain ⟨a, b, c, d, e, f, rfl⟩ := vs_eq hlen
    rw [bufs_eq] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨h1, h2⟩ := h
    have hd := AesEcb.agree_of hb.2.2.1
    have hb' : Spec.Cbc.blocksAt m₂ d (e.setWidth abi.ptrBits).toNat = Spec.Cbc.blocksAt m₁ d (e.setWidth abi.ptrBits).toNat :=
      blocksAt_congr fun i hi => hd i (by have := AesEcb.n_le (pb := abi.ptrBits) e; omega_using [hi, this])
    have hc := AesEcb.bytesAt_congr (AesEcb.agree_of hb.2.1)
    refine ⟨fun key hk => ?_, fun z hz => ?_⟩
    · obtain ⟨h1a, h1b⟩ := h1 key hk
      exact ⟨hb'.trans h1a, hc.trans h1b⟩
    · rw [← hb.2.2.2 z hz]
      exact h2 z hz

end Cbc

theorem cfb8EncryptOut (stack : Nat) :
    PostOut (Spec.Cfb8.aesEncryptContract RISCV64.abi stack) (Spec.Cfb8.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb8.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfb8DecryptOut (stack : Nat) :
    PostOut (Spec.Cfb8.aesDecryptContract RISCV64.abi stack) (Spec.Cfb8.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb8.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) :
    PostOut (Spec.Cfb.aesEncryptContract RISCV64.abi stack) (Spec.Cfb.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) :
    PostOut (Spec.Cfb.aesDecryptContract RISCV64.abi stack) (Spec.Cfb.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) :
    PostOut (Spec.Ofb.aesContract RISCV64.abi stack) (Spec.Ofb.aesSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Ofb.aesSig, Spec.Cbc.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrOut (stack : Nat) :
    PostOut (Spec.Ctr.aesContract RISCV64.abi stack) (Spec.Ctr.aesSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ctr, dt, ln, sc], _ =>
      simp only [Spec.Ctr.aesSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Cbc.blocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ctr 16 = _
      intro key hk
      rw [blocksAt_of0 hb.2.2.1 (len_le ln 16), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ctrFinalOut (stack : Nat) :
    PostOut (Spec.Ctr.aesFinalContract RISCV64.abi stack) (Spec.Ctr.aesFinalSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, ctr, dt, ln, sc], _ =>
      simp only [Spec.Ctr.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ ctr 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (Spec.Cfb.aesEncryptFinalContract RISCV64.abi stack) (Spec.Cfb.aesFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (Spec.Cfb.aesDecryptFinalContract RISCV64.abi stack) (Spec.Cfb.aesFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Cfb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) :
    PostOut (Spec.Ofb.aesFinalContract RISCV64.abi stack) (Spec.Ofb.aesFinalSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Ofb.aesFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Aes.KeySchedule m sch _ key → Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 16 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2.1 (len_le1 ln), bytesAt_of0 (n := 16) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## The registrations -/

/-- `Spec.Aes.expandKeyApi`. -/
def expandKeyReg : Registration Spec.Aes.expandKeyApi RISCV64.target :=
  withScrubSel {
      code := Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a3 64 Impl.Aes.RISCV64.expandKey
      verified := Proof.Aes.RISCV64.expandKey_framed } []
    (expandKeyOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (expandKeyOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a3 64 Impl.Aes.RISCV64.expandKey) 512 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.AesEcb.encryptApi`. -/
def ecbEncryptReg : Registration Spec.AesEcb.encryptApi RISCV64.target :=
  withScrub {
      code := Proof.AesEcb.RISCV64.encrypt
      verified := Proof.AesEcb.RISCV64.encrypt_verified }
    (Ecb.encryptOut _)

/-- `Spec.AesEcb.decryptApi`. -/
def ecbDecryptReg : Registration Spec.AesEcb.decryptApi RISCV64.target :=
  withScrub {
      code := Proof.AesEcb.RISCV64.decrypt
      verified := Proof.AesEcb.RISCV64.decrypt_verified }
    (Ecb.decryptOut _)

/-- `Spec.Cbc.aesEncryptApi`. -/
def cbcEncryptReg : Registration Spec.Cbc.aesEncryptApi RISCV64.target :=
  withScrub {
      code := Proof.AesCbc.RISCV64.Wiped.encrypt
      verified := Proof.AesCbc.RISCV64.Wiped.encrypt_verified }
    (Cbc.encryptOut _)

/-- `Spec.Cbc.aesDecryptApi`. -/
def cbcDecryptReg : Registration Spec.Cbc.aesDecryptApi RISCV64.target :=
  withScrub {
      code := Proof.AesCbc.RISCV64.Wiped.decrypt
      verified := Proof.AesCbc.RISCV64.Wiped.decrypt_verified }
    (Cbc.decryptOut _)

/-- `Spec.Ctr.aesApi`. -/
def ctrReg : Registration Spec.Ctr.aesApi RISCV64.target :=
  withScrub {
      code := Impl.AesCtr.RISCV64.crypt
      verified := Proof.AesCtr.keyed Proof.AesCtr.RISCV64.crypt_verified }
    (ctrOut _)

/-- `Spec.Ctr.aesFinalApi`. -/
def ctrFinalReg : Registration Spec.Ctr.aesFinalApi RISCV64.target :=
  withScrubSel {
      code := Impl.StackScratch.RISCV64.withStackScratchWiped 80 .a6 10 Impl.AesCtr.RISCV64.cryptFinal
      verified := Proof.AesCtr.final_keyed Proof.AesCtr.RISCV64.Final.cryptFinal_framed } []
    (ctrFinalOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (ctrFinalOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 80 .a6 10 Impl.AesCtr.RISCV64.cryptFinal) 80 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Cfb.aesEncryptApi`. -/
def cfbEncryptReg : Registration Spec.Cfb.aesEncryptApi RISCV64.target :=
  withScrub {
      code := Impl.AesCfb.RISCV64.encrypt
      verified := Proof.AesCfb.encrypt_keyed Proof.AesCfb.RISCV64.encrypt_verified }
    (cfbEncryptOut _)

/-- `Spec.Cfb.aesDecryptApi`. -/
def cfbDecryptReg : Registration Spec.Cfb.aesDecryptApi RISCV64.target :=
  withScrub {
      code := Impl.AesCfb.RISCV64.decrypt
      verified := Proof.AesCfb.decrypt_keyed Proof.AesCfb.RISCV64.decrypt_verified }
    (cfbDecryptOut _)

/-- `Spec.Cfb.aesEncryptFinalApi`. -/
def cfbEncryptFinalReg : Registration Spec.Cfb.aesEncryptFinalApi RISCV64.target :=
  withScrubSel {
      code := Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 Impl.AesCfb.RISCV64.encryptFinal
      verified := Proof.AesCfb.encryptFinal_keyed Proof.AesCfb.RISCV64.Final.encryptFinal_framed } []
    (cfbEncryptFinalOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (cfbEncryptFinalOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 Impl.AesCfb.RISCV64.encryptFinal) 64 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Cfb.aesDecryptFinalApi`. -/
def cfbDecryptFinalReg : Registration Spec.Cfb.aesDecryptFinalApi RISCV64.target :=
  withScrubSel {
      code := Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 Impl.AesCfb.RISCV64.decryptFinal
      verified := Proof.AesCfb.decryptFinal_keyed Proof.AesCfb.RISCV64.Final.decryptFinal_framed } []
    (cfbDecryptFinalOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (cfbDecryptFinalOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 Impl.AesCfb.RISCV64.decryptFinal) 64 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

/-- `Spec.Cfb8.aesEncryptApi`. -/
def cfb8EncryptReg : Registration Spec.Cfb8.aesEncryptApi RISCV64.target :=
  withScrub {
      code := Impl.AesCfb8.RISCV64.encrypt
      verified := Proof.AesCfb8.encrypt_keyed Proof.AesCfb8.RISCV64.encrypt_verified }
    (cfb8EncryptOut _)

/-- `Spec.Cfb8.aesDecryptApi`. -/
def cfb8DecryptReg : Registration Spec.Cfb8.aesDecryptApi RISCV64.target :=
  withScrub {
      code := Impl.AesCfb8.RISCV64.decrypt
      verified := Proof.AesCfb8.decrypt_keyed Proof.AesCfb8.RISCV64.decrypt_verified }
    (cfb8DecryptOut _)

/-- `Spec.Ofb.aesApi`. -/
def ofbReg : Registration Spec.Ofb.aesApi RISCV64.target :=
  withScrub {
      code := Impl.AesOfb.RISCV64.crypt
      verified := Proof.AesOfb.keyed Proof.AesOfb.RISCV64.crypt_verified }
    (ofbOut _)

/-- `Spec.Ofb.aesFinalApi`. -/
def ofbFinalReg : Registration Spec.Ofb.aesFinalApi RISCV64.target :=
  withScrubSel {
      code := Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 Impl.AesOfb.RISCV64.cryptFinal
      verified := Proof.AesOfb.final_keyed Proof.AesOfb.RISCV64.cryptFinal_framed } []
    (ofbFinalOut _)
    (fun hfs hsz hrb => scrubSel_noResidue _ _ [] hfs hsz hrb (ofbFinalOut _) (hbp_nil _)
      (Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 Impl.AesOfb.RISCV64.cryptFinal) 64 0
      rfl rfl rfl (by exact ⟨_, by taint_decide_ct⟩))

end VG.Proof.Aes.RISCV64.Scrub
