module

import VerifiedGarbage.Proof.Sm4.AArch64.Link
import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
public import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
public import VerifiedGarbage.Impl.Sm4.AArch64.FbFinal
public import VerifiedGarbage.Spec.Sm4.CfbFinal
public import VerifiedGarbage.Proof.Modes.FbFinal
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Sm4.AArch64.Link
meta import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Sm4.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.Sm4.AArch64.FbLit
meta import VerifiedGarbage.Impl.Sm4.AArch64.FbFinal
meta import VerifiedGarbage.Spec.Sm4.CfbFinal
meta import VerifiedGarbage.Proof.Modes.FbFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# SM4-CFB128 of a message's last piece on AArch64 meets its contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`: the modes' CFB over a message's
last piece (`Proof.Modes.AArch64.fbFinal_wp`) over SM4's serial encryption
core (`fbCoreSpec`), with the IV's address in `x19`, as for OFB and CFB
encryption of whole blocks (`FbVerified.lean`), and the specification's
results (`Proof.Modes.cfbEncFinal_of_bytes`, …).
`cfbEncryptFinal_verified`, …: each is correct and constant time, by the
taint analysis, as the whole-block functions are; `cfbEncryptFinal_framed`,
… run them with their working space on the stack, zeroed on return: 3264
bytes, the 408 words of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.Impl.Sm4.AArch64

/-- The data's length, in bytes. -/
abbrev finalLen (s : State) : Nat := (s.gpr .x3).toNat

/-- What the modes' OFB and CFB over a message's last piece give, for a mode
`mo`: each byte of the data that of `fbOut` of its block, and the IV
`fbNextF`, keeping the callee-saved registers. -/
theorem fbFinal_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre finalLen s₀) :
    WP isa (fbCore.fbFinal mo ⟨.x1, .x2, .x3, .x4⟩ .x19) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      (∀ i < finalLen s₀, s'.mem (s₀.gpr .x2 + BitVec.ofNat 64 i) =
        (Modes.fbOut mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (i / 16)).getD (i % 16) 0) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .x1) 16 =
        Modes.fbNextF mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (finalLen s₀) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * (slots + 12)⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.fbFinal_wp fbCoreSpec mo (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x19)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (len := finalLen s₀)
    (k := Spec.Sm4.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ keeps_x19)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [fbCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem cipher_length (k : Spec.Sm4.Schedule) (x : List Byte) : (Spec.Sm4.cipher k x).length = 16 := by
  simp [Spec.Sm4.cipher]

/-- The final encryption's contract on AArch64: the data `len = x3` bytes
long, and the data and the IV as `Spec.Cfb.EncryptFinal` says. -/
def cfbEncFinalAArch64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Cfb.EncryptFinal (ciphOf s) 16 s.mem s'.mem (s.gpr .x1) (s.gpr .x2) (finalLen s)
  pub := fbPub

/-- The final decryption's contract on AArch64. -/
def cfbDecFinalAArch64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Cfb.DecryptFinal (ciphOf s) 16 s.mem s'.mem (s.gpr .x1) (s.gpr .x2) (finalLen s)
  pub := fbPub

theorem cfbEncryptFinal_wp {s₀ : State} (hp : cfbEncFinalAArch64.pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbEncFinalAArch64.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEncFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : cfbDecFinalAArch64.pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecFinalAArch64.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDecFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbEncryptFinal_keeps_x30 : Modes.AArch64.KeepsReg .x30 cfbEncryptFinal := by sm4_keeps_x30
theorem cfbDecryptFinal_keeps_x30 : Modes.AArch64.KeepsReg .x30 cfbDecryptFinal := by sm4_keeps_x30

/-! ## Verified -/

/-- A state satisfying the precondition (one byte). -/
def finalSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 1⟩, ⟨0x4000, 8 * 408⟩]

/-- A state satisfying the contracts' precondition: the schedule at
`0x1000`, the IV at `0x2000`, one byte at `0x3000`. -/
def finalFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 1⟩]

/-- SM4's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.Sm4.cipher (Spec.Sm4.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 128 16

theorem cfbEncryptFinal_verified :
    Verified AArch64.target cfbEncryptFinal (Sig.scratchContract AArch64.abi finalSig "scratch" .u64
      (slots + 12) (Curry.const (fun _ => True) _) (Proof.Modes.encFinalPost ciphAt 16 AArch64.abi.ptrBits) true 0) :=
  Verified.of_correct (k := cfbEncFinalAArch64) (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cfbEncryptFinal_keeps_x30 (cfbEncryptFinal_wp hs)
      exact ⟨t, s', he, modeAbi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide_sum [cryptSum])) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, cfbEncFinalAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs, slots,
      tableEnd, tableSlot] [finalSat]
      using finalSat)

theorem cfbDecryptFinal_verified :
    Verified AArch64.target cfbDecryptFinal (Sig.scratchContract AArch64.abi finalSig "scratch" .u64
      (slots + 12) (Curry.const (fun _ => True) _) (Proof.Modes.decFinalPost ciphAt 16 AArch64.abi.ptrBits) true 0) :=
  Verified.of_correct (k := cfbDecFinalAArch64) (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs' cfbDecryptFinal_keeps_x30 (cfbDecryptFinal_wp hs)
      exact ⟨t, s', he, modeAbi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime_of_exists (A := VectorTaint.taint)
        (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide_sum [cryptSum])) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, cfbDecFinalAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs, slots,
      tableEnd, tableSlot] [finalSat]
      using finalSat)

theorem cfbEncFinalFrameSat_pre : ∃ s, (Spec.Sm4.cfbEncryptFinalContract AArch64.abi 3264).pre s := by
  implies_sat [Spec.Sm4.cfbEncryptFinalContract, Spec.Sm4.cfbFinalSig, AArch64.abi, AArch64.argRegs]
    [finalFrameSat] using finalFrameSat

theorem cfbDecFinalFrameSat_pre : ∃ s, (Spec.Sm4.cfbDecryptFinalContract AArch64.abi 3264).pre s := by
  implies_sat [Spec.Sm4.cfbDecryptFinalContract, Spec.Sm4.cfbFinalSig, AArch64.abi, AArch64.argRegs]
    [finalFrameSat] using finalFrameSat

/-- The final CFB128 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 cfbEncryptFinal)
      (Spec.Sm4.cfbEncryptFinalContract AArch64.abi 3264) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Modes.encFinalPost ciphAt 16 AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3264) cfbEncryptFinal_verified
    (by decide) (by decide) (by decide) (Proof.Modes.encFinalPost_local _) cfbEncFinalFrameSat_pre

/-- The final CFB128 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 3264 .x4 408 cfbDecryptFinal)
      (Spec.Sm4.cfbDecryptFinalContract AArch64.abi 3264) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 408) (post := Proof.Modes.decFinalPost ciphAt 16 AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 3264) cfbDecryptFinal_verified
    (by decide) (by decide) (by decide) (Proof.Modes.decFinalPost_local _) cfbDecFinalFrameSat_pre

end VG.Proof.Sm4.AArch64
