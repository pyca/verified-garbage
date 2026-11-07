module

import VerifiedGarbage.Proof.Camellia.AArch64.Link
import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
public import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
public import VerifiedGarbage.Impl.Camellia.AArch64.FbFinal
public import VerifiedGarbage.Spec.Camellia.CfbFinal
public import VerifiedGarbage.Proof.Modes.FbFinal
public import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Camellia.AArch64.Link
meta import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Camellia.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Camellia.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.Camellia.AArch64.FbLit
meta import VerifiedGarbage.Impl.Camellia.AArch64.FbFinal
meta import VerifiedGarbage.Spec.Camellia.CfbFinal
meta import VerifiedGarbage.Proof.Modes.FbFinal
meta import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Camellia-CFB128 of a message's last piece on AArch64 meets its contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`: the modes' CFB over a message's
last piece (`Proof.Modes.AArch64.fbFinal_wp`) over Camellia's serial
encryption core (`fbCoreSpec`), with the IV's address in `x19`, as for OFB
and CFB encryption of whole blocks (`FbVerified.lean`), and the
specification's results (`Proof.Modes.cfbEncFinal_of_bytes`, …).
`cfbEncryptFinal_verified`, …: each is correct and constant time, by the
taint analysis, as the whole-block functions are, for the subkeys at
`schedule` (`Proof.Camellia.cfbEncFinalScratchContract`);
`cfbEncryptFinal_framed`, … run them with their working space on the stack,
zeroed on return: 3344 bytes, the 418 words of the scratch buffer, and meet
the contracts for every key whose subkeys those are
(`Proof.Camellia.cfbEncryptFinal_of_sk`).
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.Impl.Camellia.AArch64
open VG.Proof.Camellia (schedWords)

/-- The data's length, in bytes. -/
abbrev finalLen (s : State) : Nat := (s.gpr .x4).toNat

/-- What the modes' OFB and CFB over a message's last piece give, for a mode
`mo`: each byte of the data that of `fbOut` of its block, and the IV
`fbNextF`, keeping the callee-saved registers. -/
theorem fbFinal_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre finalLen s₀) :
    WP isa (fbCore.fbFinal mo ⟨.x2, .x3, .x4, .x5⟩ .x19) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      (∀ i < finalLen s₀, s'.mem (s₀.gpr .x3 + BitVec.ofNat 64 i) =
        (Modes.fbOut mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (i / 16)).getD (i % 16) 0) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .x2) 16 =
        Modes.fbNextF mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (finalLen s₀) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB, hR⟩ := hp
  have hwS : (⟨s₀.gpr .x5, 8 * (slots + 12)⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.fbFinal_wp fbCoreSpec mo (r := ⟨.x2, .x3, .x4, .x5⟩)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x19)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (len := finalLen s₀)
    (k := ((s₀.gpr .x1).toNat, schedWords s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ keeps_x19)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [fbCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem cipher_length (s : State) (x : List Byte) : (ciphOf s x).length = 16 := by
  have := fbCoreSpec.cipher_len ((s.gpr .x1).toNat, schedWords s.mem (s.gpr .x0) (s.gpr .x1).toNat) x
  rw [fbCipher_eq] at this
  exact this

/-- The final encryption's contract on AArch64: the data `len = x4` bytes
long, and the data and the IV as `Spec.Cfb.EncryptFinal` says. -/
def cfbEncFinalAArch64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Cfb.EncryptFinal (ciphOf s) 16 s.mem s'.mem (s.gpr .x2) (s.gpr .x3) (finalLen s)
  pub := fbPub

/-- The final decryption's contract on AArch64. -/
def cfbDecFinalAArch64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Cfb.DecryptFinal (ciphOf s) 16 s.mem s'.mem (s.gpr .x2) (s.gpr .x3) (finalLen s)
  pub := fbPub

theorem cfbEncryptFinal_wp {s₀ : State} (hp : cfbEncFinalAArch64.pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbEncFinalAArch64.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEncFinal_of_bytes (by decide) (cipher_length s₀) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : cfbDecFinalAArch64.pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecFinalAArch64.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDecFinal_of_bytes (by decide) (cipher_length s₀) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbEncryptFinal_keeps_x30 : Modes.AArch64.KeepsReg .x30 cfbEncryptFinal := by camellia_keeps_x30
theorem cfbDecryptFinal_keeps_x30 : Modes.AArch64.KeepsReg .x30 cfbDecryptFinal := by camellia_keeps_x30

/-! ## Verified -/

/-- A state satisfying the precondition (one byte, 18 rounds). -/
def finalSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 18 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 1⟩, ⟨0x4000, 8 * 418⟩]

/-- A state satisfying the contracts' precondition: the schedule at
`0x1000`, the IV at `0x2000`, one byte at `0x3000`, 18 rounds. -/
def finalFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 18 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 1⟩]

theorem cfbEncryptFinal_verified :
    Verified AArch64.target cfbEncryptFinal (Proof.Camellia.cfbEncFinalScratchContract AArch64.abi (slots + 12)) :=
  Verified.of_correct (k := cfbEncFinalAArch64) (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cfbEncryptFinal_keeps_x30 (cfbEncryptFinal_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
      fbTaint_agree (by taint_decide)) (by
    sig_implies [Proof.Camellia.cfbEncFinalScratchContract, Sig.scratchContract, Sig.withScratch,
      Curry.withScratch, Curry.app, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre,
      Proof.Camellia.cfbEncryptFinalPostSk, cfbEncFinalAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs, slots,
      tailSlot, savedSlot, endSlot, keySlot] [finalSat] using finalSat)

theorem cfbEncryptFinalFrameSat_pre : ∃ s, (Proof.Camellia.cfbEncryptFinalContractSk AArch64.abi 3344).pre s := by
  implies_sat [Proof.Camellia.cfbEncryptFinalContractSk, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre,
    Proof.Camellia.cfbEncryptFinalPostSk, AArch64.abi, AArch64.argRegs] [finalFrameSat] using finalFrameSat

theorem cfbDecryptFinal_verified :
    Verified AArch64.target cfbDecryptFinal (Proof.Camellia.cfbDecFinalScratchContract AArch64.abi (slots + 12)) :=
  Verified.of_correct (k := cfbDecFinalAArch64) (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cfbDecryptFinal_keeps_x30 (cfbDecryptFinal_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
      fbTaint_agree (by taint_decide)) (by
    sig_implies [Proof.Camellia.cfbDecFinalScratchContract, Sig.scratchContract, Sig.withScratch,
      Curry.withScratch, Curry.app, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre,
      Proof.Camellia.cfbDecryptFinalPostSk, cfbDecFinalAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs, slots,
      tailSlot, savedSlot, endSlot, keySlot] [finalSat] using finalSat)

theorem cfbDecryptFinalFrameSat_pre : ∃ s, (Proof.Camellia.cfbDecryptFinalContractSk AArch64.abi 3344).pre s := by
  implies_sat [Proof.Camellia.cfbDecryptFinalContractSk, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre,
    Proof.Camellia.cfbDecryptFinalPostSk, AArch64.abi, AArch64.argRegs] [finalFrameSat] using finalFrameSat

/-- The final CFB128 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 cfbEncryptFinal)
      (Spec.Camellia.cfbEncryptFinalContract AArch64.abi 3344) :=
  Proof.Camellia.cfbEncryptFinal_of_sk <|
  AArch64.Verified.stackScratchWiped (sig := Spec.Camellia.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 418) (pre := Spec.Camellia.cfbFinalPre AArch64.abi.ptrBits)
    (post := Proof.Camellia.cfbEncryptFinalPostSk AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3344) cfbEncryptFinal_verified
    (by decide) (by decide) (by decide) (Proof.Camellia.cfbEncryptFinalPostOut_local _) cfbEncryptFinalFrameSat_pre

/-- The final CFB128 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3344 .x5 418 cfbDecryptFinal)
      (Spec.Camellia.cfbDecryptFinalContract AArch64.abi 3344) :=
  Proof.Camellia.cfbDecryptFinal_of_sk <|
  AArch64.Verified.stackScratchWiped (sig := Spec.Camellia.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 418) (pre := Spec.Camellia.cfbFinalPre AArch64.abi.ptrBits)
    (post := Proof.Camellia.cfbDecryptFinalPostSk AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3344) cfbDecryptFinal_verified
    (by decide) (by decide) (by decide) (Proof.Camellia.cfbDecryptFinalPostOut_local _) cfbDecryptFinalFrameSat_pre

end VG.Proof.Camellia.AArch64
