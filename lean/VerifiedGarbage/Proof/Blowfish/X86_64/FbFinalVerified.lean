module

import VerifiedGarbage.Proof.Blowfish.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
public import VerifiedGarbage.Proof.Blowfish.X86_64.FbVerified
import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
public import VerifiedGarbage.Impl.Blowfish.X86_64.FbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
public import VerifiedGarbage.Proof.Modes.FbFinal
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Blowfish.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Blowfish.X86_64.FbVerified
meta import VerifiedGarbage.Proof.Blowfish.X86_64.FbFinalLit
meta import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
meta import VerifiedGarbage.Impl.Blowfish.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Spec.Blowfish.CfbFinal
meta import VerifiedGarbage.Proof.Modes.FbFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# Blowfish-CFB64 of a message's last piece on x86-64 meets its contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`: the modes' CFB over a message's
last piece (`Proof.Modes.X86_64.fbFinal_wp`) over Blowfish's core
(`dirCoreSpec true`), with the specification's results
(`Proof.Modes.cfbEncFinal_of_bytes`, …). `cfbEncryptFinal_verified`, …:
each is correct and constant time, by the taint analysis, as the
whole-block functions are (`FbVerified.lean`); `cfbEncryptFinal_framed`, …
run them with their working space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64

/-- The data's length, in bytes. -/
abbrev finalLen (s : State) : Nat := (s.gpr .rcx).toNat

/-- What the modes' OFB and CFB over a message's last piece give, for a mode
`mo`: each byte of the data that of `fbOut` of its block, and the IV
`fbNextF`, keeping the callee-saved registers. -/
theorem fbFinal_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre finalLen s₀) :
    WP isa ((dirCore true).fbFinal mo modeRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      (∀ i < finalLen s₀, s'.mem (s₀.gpr .rdx + BitVec.ofNat 64 i) =
        (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (i / 8)).getD (i % 8) 0) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rsi) 8 =
        Modes.fbNextF mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (finalLen s₀) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 11⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.fbFinal_wp (dirCoreSpec true) mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (len := finalLen s₀)
    (k := Spec.Blowfish.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, ⟨by rw [hrd]; simp, fitK, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dKV
      · exact dKD
      · exact dKS⟩, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), crypt_keepsIv true⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by rw [dirCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV

theorem cipher_length (k : Spec.Blowfish.Schedule) (x : List Byte) : (Spec.Blowfish.cipher k x).length = 8 := by
  simp [Spec.Blowfish.cipher]

/-- The final encryption's contract on x86-64: the data `len = rcx` bytes
long, and the data and the IV as `Spec.Cfb.EncryptFinal` says. -/
def cfbEncFinalX86_64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Cfb.EncryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .rsi) (s.gpr .rdx) (finalLen s)
  pub := fbPub

/-- The final decryption's contract on x86-64. -/
def cfbDecFinalX86_64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Cfb.DecryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .rsi) (s.gpr .rdx) (finalLen s)
  pub := fbPub

theorem cfbEncryptFinal_wp {s₀ : State} (hp : cfbEncFinalX86_64.pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncFinalX86_64.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEncFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : cfbDecFinalX86_64.pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecFinalX86_64.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDecFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

/-! ## Verified -/

theorem finalLen_congr : ∀ s t : State, s.gpr .rcx = t.gpr .rcx → finalLen s = finalLen t := fun _ _ h => by
  simp only [finalLen, h]

/-- A state satisfying the precondition (one byte). -/
def finalSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 0x4000 | .rcx => 1 | .r8 => 0x5000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 1⟩, ⟨0x5000, 8 * 11⟩]

/-- Blowfish's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.Blowfish.cipher (Spec.Blowfish.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 4168 8

theorem cfbEncryptFinal_verified :
    Verified X86_64.target cfbEncryptFinal (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 11
      (Curry.const (fun _ => True) _) (Proof.Modes.encFinalPost ciphAt 8 X86_64.abi.ptrBits) true 0) :=
  Verified.of_correct (k := cfbEncFinalX86_64) (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncryptFinal_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncryptFinal) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree finalLen_congr) (by taint_decide)) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, cfbEncFinalX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [finalSat]
      using finalSat)

theorem cfbDecryptFinal_verified :
    Verified X86_64.target cfbDecryptFinal (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 11
      (Curry.const (fun _ => True) _) (Proof.Modes.decFinalPost ciphAt 8 X86_64.abi.ptrBits) true 0) :=
  Verified.of_correct (k := cfbDecFinalX86_64) (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecryptFinal_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecryptFinal) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree finalLen_congr) (by taint_decide)) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, cfbDecFinalX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [finalSat]
      using finalSat)

/-- The final CFB64 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 cfbEncryptFinal)
      (Spec.Blowfish.cfbEncryptFinalContract X86_64.abi 96) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Modes.encFinalPost ciphAt 8 X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) cfbEncryptFinal_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Modes.encFinalPost_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- The final CFB64 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 cfbDecryptFinal)
      (Spec.Blowfish.cfbDecryptFinalContract X86_64.abi 96) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Modes.decFinalPost ciphAt 8 X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) cfbDecryptFinal_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Modes.decFinalPost_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Blowfish.X86_64
