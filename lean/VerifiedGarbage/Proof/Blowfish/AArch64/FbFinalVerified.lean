module

import VerifiedGarbage.Proof.Blowfish.AArch64.ModeCore
import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
public import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
public import VerifiedGarbage.Impl.Blowfish.AArch64.FbFinal
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
public import VerifiedGarbage.Proof.Modes.FbFinal
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Blowfish.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Blowfish.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Blowfish.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.Blowfish.AArch64.ModesLit
meta import VerifiedGarbage.Impl.Blowfish.AArch64.FbFinal
meta import VerifiedGarbage.Spec.Blowfish.CfbFinal
meta import VerifiedGarbage.Proof.Modes.FbFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# Blowfish-CFB64 of a message's last piece on AArch64 meets its contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`: the modes' CFB over a message's
last piece (`Proof.Modes.AArch64.fbFinal_wp`) over Blowfish's encryption
core (`dirCoreSpec true`), with the IV's address in `x25`, as for the
whole-block functions (`FbVerified.lean`), and the specification's results
(`Proof.Modes.cfbEncFinal_of_bytes`, …). The low halves of `v8`–`v15` are
kept as there: the modes' code writes no vector register and every run of
`crypt` keeps them. `cfbEncryptFinal_verified`, …: each is correct and
constant time, by the taint analysis, as the whole-block functions are;
`cfbEncryptFinal_framed`, … run them with their working space on the stack,
zeroed on return: 224 bytes, the 28 words of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.Blowfish.AArch64

open VG VG.AArch64 VG.Impl.Blowfish.AArch64

/-- The data's length, in bytes. -/
abbrev finalLen (s : State) : Nat := (s.gpr .x3).toNat

/-- What the modes' OFB and CFB over a message's last piece give, for a mode
`mo`: each byte of the data that of `fbOut` of its block, and the IV
`fbNextF`, keeping the callee-saved registers. -/
theorem fbFinal_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre finalLen s₀) :
    WP isa ((dirCore true).fbFinal mo modeRegs .x25) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      (∀ i < finalLen s₀, s'.mem (s₀.gpr .x2 + BitVec.ofNat 64 i) =
        (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (i / 8)).getD (i % 8) 0) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .x1) 8 =
        Modes.fbNextF mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (finalLen s₀) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 28⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.fbFinal_wp (dirCoreSpec true) mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (len := finalLen s₀)
    (k := Spec.Blowfish.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, ⟨by rw [hrd]; simp, fitK, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dKV
      · exact dKD
      · exact dKS⟩, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ crypt_keeps)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [dirCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem cipher_length (k : Spec.Blowfish.Schedule) (x : List Byte) : (Spec.Blowfish.cipher k x).length = 8 := by
  simp [Spec.Blowfish.cipher]

/-- The final encryption's contract on AArch64: the data `len = x3` bytes
long, and the data and the IV as `Spec.Cfb.EncryptFinal` says. -/
def cfbEncFinalAArch64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Cfb.EncryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .x1) (s.gpr .x2) (finalLen s)
  pub := fbPub

/-- The final decryption's contract on AArch64. -/
def cfbDecFinalAArch64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Cfb.DecryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .x1) (s.gpr .x2) (finalLen s)
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

/-- Every instruction keeps `v8`–`v15`, but in `crypt`. -/
theorem fbFinal_vSafe (mo : Impl.Modes.FbMode) :
    VSafeBut (dirCore true).crypt ((dirCore true).fbFinal mo modeRegs .x25) := by
  cases mo <;> vsafe_but

/-- The callee-saved registers and the rest of the ABI, from what a mode
keeps. -/
theorem finalAbi_of {mo : Impl.Modes.FbMode} {s s' : State} {t : List Leak}
    (he : Exec isa ((dirCore true).fbFinal mo modeRegs .x25) s t s')
    (h₁ : ∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19))
    (h₃ : ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r) : abiPreserved s s' :=
  ⟨Modes.AArch64.preserved_of h₁ h₃, Exec.sp he, vKeep_of_vSafeBut (fbFinal_vSafe mo) (crypt_vKeep true) _ _ _ he⟩

/-! ## Verified -/

/-- A state satisfying the precondition (one byte). -/
def finalSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 0x4000 | .x3 => 1 | .x4 => 0x5000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 1⟩, ⟨0x5000, 8 * 28⟩]

/-- A state satisfying the contracts' precondition: the schedule at
`0x1000`, the IV at `0x3000`, one byte at `0x4000`. -/
def finalFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x3000 | .x2 => 0x4000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 1⟩]

/-- Blowfish's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.Blowfish.cipher (Spec.Blowfish.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 4168 8

theorem cfbEncryptFinal_verified :
    Verified AArch64.target cfbEncryptFinal (Sig.scratchContract AArch64.abi finalSig "scratch" .u64 28
      (Curry.const (fun _ => True) _) (Proof.Modes.encFinalPost ciphAt 8 AArch64.abi.ptrBits) true 0) :=
  Verified.of_correct (k := cfbEncFinalAArch64) (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbEncryptFinal_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, finalAbi_of he h₁ h₃, h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, cfbEncFinalAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [finalSat]
      using finalSat)

theorem cfbDecryptFinal_verified :
    Verified AArch64.target cfbDecryptFinal (Sig.scratchContract AArch64.abi finalSig "scratch" .u64 28
      (Curry.const (fun _ => True) _) (Proof.Modes.decFinalPost ciphAt 8 AArch64.abi.ptrBits) true 0) :=
  Verified.of_correct (k := cfbDecFinalAArch64) (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbDecryptFinal_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, finalAbi_of he h₁ h₃, h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, cfbDecFinalAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [finalSat]
      using finalSat)

theorem cfbEncFinalFrameSat_pre : ∃ s, (Spec.Blowfish.cfbEncryptFinalContract AArch64.abi 224).pre s := by
  implies_sat [Spec.Blowfish.cfbEncryptFinalContract, Spec.Blowfish.cfbFinalSig, AArch64.abi, AArch64.argRegs]
    [finalFrameSat] using finalFrameSat

theorem cfbDecFinalFrameSat_pre : ∃ s, (Spec.Blowfish.cfbDecryptFinalContract AArch64.abi 224).pre s := by
  implies_sat [Spec.Blowfish.cfbDecryptFinalContract, Spec.Blowfish.cfbFinalSig, AArch64.abi, AArch64.argRegs]
    [finalFrameSat] using finalFrameSat

/-- The final CFB64 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 cfbEncryptFinal)
      (Spec.Blowfish.cfbEncryptFinalContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Modes.encFinalPost ciphAt 8 AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) cfbEncryptFinal_verified
    (by decide) (by decide) (by decide) (Proof.Modes.encFinalPost_local _) cfbEncFinalFrameSat_pre

/-- The final CFB64 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 cfbDecryptFinal)
      (Spec.Blowfish.cfbDecryptFinalContract AArch64.abi 224) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 28) (post := Proof.Modes.decFinalPost ciphAt 8 AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 224) cfbDecryptFinal_verified
    (by decide) (by decide) (by decide) (Proof.Modes.decFinalPost_local _) cfbDecFinalFrameSat_pre

end VG.Proof.Blowfish.AArch64
