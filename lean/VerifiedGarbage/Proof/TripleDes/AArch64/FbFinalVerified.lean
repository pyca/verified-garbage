module

public import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
import VerifiedGarbage.Proof.TripleDes.AArch64.BlockSum
import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
public import VerifiedGarbage.Impl.TripleDes.AArch64.FbFinal
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
public import VerifiedGarbage.Spec.TripleDes.OfbFinal
public import VerifiedGarbage.Proof.Modes.FbFinal
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
meta import VerifiedGarbage.Proof.TripleDes.AArch64.BlockSum
meta import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbLit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.FbFinal
meta import VerifiedGarbage.Spec.TripleDes.CfbFinal
meta import VerifiedGarbage.Spec.TripleDes.OfbFinal
meta import VerifiedGarbage.Proof.Modes.FbFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# Triple DES-CFB64 and Triple DES-OFB of a message's last piece on AArch64 meet their contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`, `ofbFinal_wp`: the modes' CFB and
OFB over a message's last piece (`Proof.Modes.AArch64.fbFinal_wp`) over the
table core (`tableCoreSpec`), with the IV's address in `x28`,
as for the whole-block functions (`FbVerified.lean`), and the specification's
results (`Proof.Modes.cfbEncFinal_of_bytes`, …,
`Proof.Modes.ofbFinal_of_bytes`). `cfbEncryptFinal_verified`, …:
each is correct and constant time, by the taint analysis, as the
whole-block functions are; `cfbEncryptFinal_framed`, … run them with their
working space on the stack, zeroed on return: 560 bytes, the 70 words of the
scratch buffer.
-/

@[expose] public section

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

/-- The data's length, in bytes. -/
abbrev finalLen (s : State) : Nat := (s.gpr .x3).toNat

/-- What the modes' OFB and CFB over a message's last piece give, for a mode
`mo`: each byte of the data that of `fbOut` of its block, and the IV
`fbNextF`, keeping the callee-saved registers. -/
theorem fbFinal_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre finalLen s₀) :
    WP isa (tableCore.fbFinal mo fbRegs .x28) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      (∀ i < finalLen s₀, s'.mem (s₀.gpr .x2 + BitVec.ofNat 64 i) =
        (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (i / 8)).getD (i % 8) 0) ∧
      Spec.TripleDes.bytesAt s'.mem (s₀.gpr .x1) 8 =
        Modes.fbNextF mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (finalLen s₀) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 70⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.fbFinal_wp tableCoreSpec mo (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x28)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (len := finalLen s₀)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .x0)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .x0, rfl, rfl, ⟨by rw [hrd]; simp, fitK, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dKV
      · exact dKD
      · exact dKS⟩, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ keeps_x28)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [tableCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem cipher_length (k : Spec.TripleDes.Schedule) (x : List Byte) : (Spec.TripleDes.cipher k x).length = 8 := by
  simp [Spec.TripleDes.cipher]

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

/-! ## Verified -/

/-- A state satisfying the precondition (one byte). -/
def finalSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩, ⟨0x4000, 8 * 70⟩]

/-- A state satisfying the contracts' precondition: the schedule at
`0x1000`, the IV at `0x2000`, one byte at `0x3000`. -/
def finalFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩]

/-- Triple DES's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 384 8

theorem cfbEncryptFinal_verified :
    Verified AArch64.target cfbEncryptFinal (Sig.scratchContract AArch64.abi finalSig "scratch" .u64 70
      (Curry.const (fun _ => True) _) (Proof.Modes.encFinalPost ciphAt 8 AArch64.abi.ptrBits) true 0) :=
  Verified.of_correct (k := cfbEncFinalAArch64) (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbEncryptFinal_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, cfbEncFinalAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [finalSat]
      using finalSat)

theorem cfbDecryptFinal_verified :
    Verified AArch64.target cfbDecryptFinal (Sig.scratchContract AArch64.abi finalSig "scratch" .u64 70
      (Curry.const (fun _ => True) _) (Proof.Modes.decFinalPost ciphAt 8 AArch64.abi.ptrBits) true 0) :=
  Verified.of_correct (k := cfbDecFinalAArch64) (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbDecryptFinal_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, cfbDecFinalAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [finalSat]
      using finalSat)

theorem cfbEncFinalFrameSat_pre : ∃ s, (Spec.TripleDes.cfbEncryptFinalContract AArch64.abi 560).pre s := by
  implies_sat [Spec.TripleDes.cfbEncryptFinalContract, Spec.TripleDes.cfbFinalSig, AArch64.abi, AArch64.argRegs]
    [finalFrameSat] using finalFrameSat

theorem cfbDecFinalFrameSat_pre : ∃ s, (Spec.TripleDes.cfbDecryptFinalContract AArch64.abi 560).pre s := by
  implies_sat [Spec.TripleDes.cfbDecryptFinalContract, Spec.TripleDes.cfbFinalSig, AArch64.abi, AArch64.argRegs]
    [finalFrameSat] using finalFrameSat

/-- The final CFB64 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 cfbEncryptFinal)
      (Spec.TripleDes.cfbEncryptFinalContract AArch64.abi 560) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 70) (post := Proof.Modes.encFinalPost ciphAt 8 AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 560) cfbEncryptFinal_verified
    (by decide) (by decide) (by decide) (Proof.Modes.encFinalPost_local _) cfbEncFinalFrameSat_pre

/-- The final CFB64 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 cfbDecryptFinal)
      (Spec.TripleDes.cfbDecryptFinalContract AArch64.abi 560) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 70) (post := Proof.Modes.decFinalPost ciphAt 8 AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 560) cfbDecryptFinal_verified
    (by decide) (by decide) (by decide) (Proof.Modes.decFinalPost_local _) cfbDecFinalFrameSat_pre

/-! ## OFB of a message's last piece -/

/-- The final OFB function's contract on AArch64. -/
def ofbFinalAArch64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Ofb.CryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .x1) (s.gpr .x2) (finalLen s)
  pub := fbPub

theorem ofbFinal_wp {s₀ : State} (hp : ofbFinalAArch64.pre s₀) :
    WP isa ofbFinal s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ofbFinalAArch64.post s₀ s' :=
  WP.mono (fbFinal_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofbFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem ofbFinal_verified :
    Verified AArch64.target ofbFinal (Sig.scratchContract AArch64.abi finalSig "scratch" .u64 70
      (Curry.const (fun _ => True) _) (Proof.Modes.ofbFinalPost ciphAt 8 AArch64.abi.ptrBits) true 0) :=
  Verified.of_correct (k := ofbFinalAArch64) (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (ofbFinal_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) fbTaint_agree
      (by taint_decide)) (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.ofbFinalPost, ofbFinalAArch64, fbPre, fbPub, AArch64.abi, AArch64.argRegs] [finalSat]
      using finalSat)

theorem ofbFinalFrameSat_pre : ∃ s, (Spec.TripleDes.ofbFinalContract AArch64.abi 560).pre s := by
  implies_sat [Spec.TripleDes.ofbFinalContract, Spec.TripleDes.ofbFinalSig, AArch64.abi, AArch64.argRegs]
    [finalFrameSat] using finalFrameSat

/-- The final OFB function with its working space on the stack. -/
theorem ofbFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 560 .x4 70 ofbFinal)
      (Spec.TripleDes.ofbFinalContract AArch64.abi 560) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.ofbFinalSig) (nm := "scratch") (e := .u64)
    (n := 70) (post := Proof.Modes.ofbFinalPost ciphAt 8 AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 560) ofbFinal_verified
    (by decide) (by decide) (by decide) (Proof.Modes.ofbFinalPost_local _) ofbFinalFrameSat_pre

end VG.Proof.TripleDes.AArch64
