module

import VerifiedGarbage.Proof.Camellia.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
public import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified
import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
public import VerifiedGarbage.Impl.Camellia.X86_64.FbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Spec.Camellia.CfbFinal
public import VerifiedGarbage.Proof.Modes.FbFinal
public import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Camellia.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified
meta import VerifiedGarbage.Proof.Camellia.X86_64.FbFinalLit
meta import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
meta import VerifiedGarbage.Impl.Camellia.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Spec.Camellia.CfbFinal
meta import VerifiedGarbage.Proof.Modes.FbFinal
meta import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# Camellia-CFB128 of a message's last piece on x86-64 meets its contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`: the modes' CFB over a message's
last piece (`Proof.Modes.X86_64.fbFinal_wp`) over Camellia's core, with the
specification's results (`Proof.Modes.cfbEncFinal_of_bytes`, …).
`cfbEncryptFinal_verified`, …: each is correct and constant time, by the
taint analysis, as the whole-block functions are (`FbVerified.lean`);
`cfbEncryptFinal_framed`, … run them with their working space on the stack,
zeroed on return, and give the specification's contracts on every key whose
subkeys are at `schedule` (`Proof.Camellia.cfbEncryptFinal_of_sk`, …).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.Impl.Camellia.X86_64

/-- The data's length, in bytes. -/
abbrev finalLen (s : State) : Nat := (s.gpr .r8).toNat

/-- What the modes' OFB and CFB over a message's last piece give, for a mode
`mo`: each byte of the data that of `fbOut` of its block, and the IV
`fbNextF`, keeping the callee-saved registers. -/
theorem fbFinal_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre finalLen s₀) :
    WP isa ((dirCore .encrypt).fbFinal mo ⟨.rdx, .rcx, .r8, .r9⟩) s₀ fun s' => gprPreserved s₀ s' ∧
      (∀ i < finalLen s₀, s'.mem (s₀.gpr .rcx + BitVec.ofNat 64 i) =
        (Modes.fbOut mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (i / 16)).getD (i % 16) 0) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rdx) 16 =
        Modes.fbNextF mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (finalLen s₀) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, dTV, dTD, dTS, hst, fitK, fitV, fitD, fitB, hR⟩ :=
    hp
  have hwS : (⟨s₀.gpr .r9, 8 * 409⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.fbFinal_wp ((dirCoreSpec .encrypt).toBlock rfl) mo (r := ⟨.rdx, .rcx, .r8, .r9⟩)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r9) (P := s₀.gpr .rdx) (D := s₀.gpr .rcx) (len := finalLen s₀)
    (k := ((s₀.gpr .rsi).toNat, schedWords s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKS, hst, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dTS⟩
    ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩
    (hstk := .inr ⟨hst, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dTV
      · exact dTD
      · exact dTS⟩))
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by rw [encCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [stkList_dirCore] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV
  · exact VG.Offset.base_disjoint_below _ (by decide)

theorem cipher_length (s : State) (x : List Byte) : (ciphOf s x).length = 16 := by
  have := ((dirCoreSpec .encrypt).toBlock rfl).cipher_len ((s.gpr .rsi).toNat, schedWords s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) x
  rw [encCipher_eq] at this
  exact this

/-- The final encryption's contract on x86-64: the data `len = r8` bytes
long, and the data and the IV as `Spec.Cfb.EncryptFinal` says. -/
def cfbEncFinalX86_64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Cfb.EncryptFinal (ciphOf s) 16 s.mem s'.mem (s.gpr .rdx) (s.gpr .rcx) (finalLen s)
  pub := fbPub

/-- The final decryption's contract on x86-64. -/
def cfbDecFinalX86_64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Cfb.DecryptFinal (ciphOf s) 16 s.mem s'.mem (s.gpr .rdx) (s.gpr .rcx) (finalLen s)
  pub := fbPub

theorem cfbEncryptFinal_wp {s₀ : State} (hp : cfbEncFinalX86_64.pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncFinalX86_64.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEncFinal_of_bytes (by decide) (cipher_length s₀) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : cfbDecFinalX86_64.pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecFinalX86_64.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDecFinal_of_bytes (by decide) (cipher_length s₀) hd
    exact ⟨hg, h1, hv.trans h2⟩

/-! ## Verified -/

theorem finalLen_congr : ∀ s t : State, s.gpr .r8 = t.gpr .r8 → finalLen s = finalLen t := fun _ _ h => by
  simp only [finalLen, h]

/-- A state satisfying the precondition (one byte). -/
def finalSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 18 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 1⟩, ⟨0x4000, 8 * 409⟩]

/-- A state satisfying the precondition of the contracts on the stack. -/
def finalFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 18 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 1⟩]

theorem cfbEncryptFinal_ct : ConstantTime isa cfbEncFinalX86_64.pre cfbEncFinalX86_64.pub cfbEncryptFinal :=
  VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree finalLen_congr) (by taint_decide)

theorem cfbEncryptFinal_verified :
    Verified X86_64.target cfbEncryptFinal (Proof.Camellia.cfbEncFinalScratchContract X86_64.abi 409 8) :=
  Verified.of_correct (k := cfbEncFinalX86_64) (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncryptFinal_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncryptFinal) (by lit_decide) he hg, hpost⟩)
    cfbEncryptFinal_ct (by
    sig_implies [Proof.Camellia.cfbEncFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre, Proof.Camellia.cfbEncryptFinalPostSk, cfbEncFinalX86_64, fbPre,
      fbPub, X86_64.abi, X86_64.argRegs, slots, tailSlot, endSlot, keySlot] [finalSat] using finalSat)

theorem cfbEncryptFinalFrameSat_pre : ∃ s, (Proof.Camellia.cfbEncryptFinalContractSk X86_64.abi 3288).pre s := by
  implies_sat [Proof.Camellia.cfbEncryptFinalContractSk, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre,
    Proof.Camellia.cfbEncryptFinalPostSk, X86_64.abi, X86_64.argRegs] [finalFrameSat] using finalFrameSat

/-- The final CFB128 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 cfbEncryptFinal)
      (Spec.Camellia.cfbEncryptFinalContract X86_64.abi 3288) :=
  Proof.Camellia.cfbEncryptFinal_of_sk <|
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 409) (pre := Spec.Camellia.cfbFinalPre X86_64.abi.ptrBits)
    (post := Proof.Camellia.cfbEncryptFinalPostSk X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3280) cfbEncryptFinal_verified
    (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Camellia.cfbEncryptFinalPostOut_local _) cfbEncryptFinalFrameSat_pre

theorem cfbDecryptFinal_ct : ConstantTime isa cfbDecFinalX86_64.pre cfbDecFinalX86_64.pub cfbDecryptFinal :=
  VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree finalLen_congr) (by taint_decide)

theorem cfbDecryptFinal_verified :
    Verified X86_64.target cfbDecryptFinal (Proof.Camellia.cfbDecFinalScratchContract X86_64.abi 409 8) :=
  Verified.of_correct (k := cfbDecFinalX86_64) (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecryptFinal_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecryptFinal) (by lit_decide) he hg, hpost⟩)
    cfbDecryptFinal_ct (by
    sig_implies [Proof.Camellia.cfbDecFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre, Proof.Camellia.cfbDecryptFinalPostSk, cfbDecFinalX86_64, fbPre,
      fbPub, X86_64.abi, X86_64.argRegs, slots, tailSlot, endSlot, keySlot] [finalSat] using finalSat)

theorem cfbDecryptFinalFrameSat_pre : ∃ s, (Proof.Camellia.cfbDecryptFinalContractSk X86_64.abi 3288).pre s := by
  implies_sat [Proof.Camellia.cfbDecryptFinalContractSk, Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre,
    Proof.Camellia.cfbDecryptFinalPostSk, X86_64.abi, X86_64.argRegs] [finalFrameSat] using finalFrameSat

/-- The final CFB128 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 cfbDecryptFinal)
      (Spec.Camellia.cfbDecryptFinalContract X86_64.abi 3288) :=
  Proof.Camellia.cfbDecryptFinal_of_sk <|
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 409) (pre := Spec.Camellia.cfbFinalPre X86_64.abi.ptrBits)
    (post := Proof.Camellia.cfbDecryptFinalPostSk X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3280) cfbDecryptFinal_verified
    (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Camellia.cfbDecryptFinalPostOut_local _) cfbDecryptFinalFrameSat_pre

end VG.Proof.Camellia.X86_64
