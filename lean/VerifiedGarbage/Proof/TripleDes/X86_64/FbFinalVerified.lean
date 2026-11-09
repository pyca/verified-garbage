module

import VerifiedGarbage.Proof.TripleDes.X86_64.ModeCore
import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalLit
import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
public import VerifiedGarbage.Impl.TripleDes.X86_64.FbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
public import VerifiedGarbage.Spec.TripleDes.OfbFinal
public import VerifiedGarbage.Proof.Modes.FbFinal
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.TripleDes.X86_64.CallPatch
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.TripleDes.X86_64.BlockSum
import VerifiedGarbage.Proof.TripleDes.X86_64.ConstantTime
meta import VerifiedGarbage.Proof.TripleDes.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FbFinalLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FbLit
meta import VerifiedGarbage.Impl.TripleDes.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Spec.TripleDes.CfbFinal
meta import VerifiedGarbage.Spec.TripleDes.OfbFinal
meta import VerifiedGarbage.Proof.Modes.FbFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.TripleDes.X86_64.CallPatch
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInline
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.TripleDes.X86_64.BlockSum
meta import VerifiedGarbage.Proof.TripleDes.X86_64.ConstantTime

/-!
# Triple DES-CFB64 and Triple DES-OFB of a message's last piece on x86-64 meet their contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`, `ofbFinal_wp`: the modes' CFB and
OFB over a message's last piece (`Proof.Modes.X86_64.fbFinal_wp`) over Triple
DES's core (`dirCoreSpec .encrypt`), with the specification's results
(`Proof.Modes.cfbEncFinal_of_bytes`, …, `Proof.Modes.ofbFinal_of_bytes`).
`cfbEncryptFinal_verified`, …: each is correct and constant time, by the taint
analysis, as the whole-block functions are (`FbVerified.lean`);
`cfbEncryptFinal_framed`, … run them with their working space on the stack,
zeroed on return.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

/-- The data's length, in bytes. -/
abbrev finalLen (s : State) : Nat := (s.gpr .rcx).toNat

/-- What the modes' OFB and CFB over a message's last piece give, for a mode
`mo`: each byte of the data that of `fbOut` of its block, and the IV
`fbNextF`, keeping the callee-saved registers. -/
theorem fbFinal_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre finalLen s₀) :
    WP isa ((dirCore .encrypt).fbFinal mo fbRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      (∀ i < finalLen s₀, s'.mem (s₀.gpr .rdx + BitVec.ofNat 64 i) =
        (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (i / 8)).getD (i % 8) 0) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rsi) 8 =
        Modes.fbNextF mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (finalLen s₀) := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 121⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.fbFinal_wp (dirCoreSpec .encrypt) mo (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (len := finalLen s₀)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by rw [dirCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV

theorem cipher_length (k : Spec.TripleDes.Schedule) (x : List Byte) : (Spec.TripleDes.cipher k x).length = 8 := by
  simp [Spec.TripleDes.cipher]

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
    WP isa cfbEncryptFinalI s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncFinalX86_64.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEncFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : cfbDecFinalX86_64.pre s₀) :
    WP isa cfbDecryptFinalI s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecFinalX86_64.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDecFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

/-! ## Verified -/

theorem finalLen_congr : ∀ s t : State, s.gpr .rcx = t.gpr .rcx → finalLen s = finalLen t := fun _ _ h => by
  simp only [finalLen, h]

/-- A state satisfying the precondition (one byte). -/
def finalSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 384⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩, ⟨0x4000, 8 * 121⟩]

/-- Triple DES's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 384 8

theorem aesBytesAt_congr {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = m' (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m p n = Spec.Aes.bytesAt m' p n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem cfbEncryptFinal_correct (s : State) (hs : cfbEncFinalX86_64.pre s) :
    ∃ t s', Exec isa cfbEncryptFinalI s t s' ∧ abiPreserved s s' ∧ cfbEncFinalX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cfbEncryptFinal_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncryptFinalI) (by lit_decide) he hg, hpost⟩

theorem cfbEncryptFinal_ct : ConstantTime isa cfbEncFinalX86_64.pre cfbEncFinalX86_64.pub cfbEncryptFinal := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint cfbEncryptFinal h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree finalLen_congr) h

theorem cfbEncryptFinal_implies : cfbEncFinalX86_64.Implies (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 121
      (Curry.const (fun _ => True) _) (Proof.Modes.encFinalPost ciphAt 8 X86_64.abi.ptrBits) true 0) := by
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
    Proof.Modes.encFinalPost, cfbEncFinalX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [finalSat] using finalSat

theorem cfbEncryptFinal_implies8 : cfbEncFinalX86_64.Implies (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 121
      (Curry.const (fun _ => True) _) (Proof.Modes.encFinalPost ciphAt 8 X86_64.abi.ptrBits) true 8) :=
  cfbEncryptFinal_implies.stack8_abi (by
    sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      X86_64.abi, X86_64.argRegs, finalSat] [finalSat] using finalSat)

/-- The data and the IV are apart from the call's return address. -/
theorem cfbEncryptFinal_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 121
      (Curry.const (fun _ => True) _) (Proof.Modes.encFinalPost ciphAt 8 X86_64.abi.ptrBits) true 8).pre s) (hp : cfbEncFinalX86_64.post s b) :
    cfbEncFinalX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := cfbEncryptFinal_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := finalLen s)
    (by rw [hwr]; simp) (by omega)
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega)
  obtain ⟨h₁, h₂⟩ := hp
  exact ⟨by rw [aesBytesAt_congr (patch_mem hbD)]; exact h₁, by rw [aesBytesAt_congr (patch_mem hbI)]; exact h₂⟩

theorem cfbEncryptFinal_inline : cfbEncryptFinal.inline = cfbEncryptFinalI := rfl

theorem cfbEncryptFinal_verified : Verified X86_64.target cfbEncryptFinal (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 121
      (Curry.const (fun _ => True) _) (Proof.Modes.encFinalPost ciphAt 8 X86_64.abi.ptrBits) true 8) :=
  Verified.of_inline_ct (by lit_decide) (fun s hs => by rw [cfbEncryptFinal_inline]; exact cfbEncryptFinal_correct s hs)
    cfbEncryptFinal_ct cfbEncryptFinal_implies8 (fun _ h => Sig.clear_of_pre h) cfbEncryptFinal_patch

theorem cfbDecryptFinal_correct (s : State) (hs : cfbDecFinalX86_64.pre s) :
    ∃ t s', Exec isa cfbDecryptFinalI s t s' ∧ abiPreserved s s' ∧ cfbDecFinalX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cfbDecryptFinal_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecryptFinalI) (by lit_decide) he hg, hpost⟩

theorem cfbDecryptFinal_ct : ConstantTime isa cfbDecFinalX86_64.pre cfbDecFinalX86_64.pub cfbDecryptFinal := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint cfbDecryptFinal h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree finalLen_congr) h

theorem cfbDecryptFinal_implies : cfbDecFinalX86_64.Implies (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 121
      (Curry.const (fun _ => True) _) (Proof.Modes.decFinalPost ciphAt 8 X86_64.abi.ptrBits) true 0) := by
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
    Proof.Modes.decFinalPost, cfbDecFinalX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [finalSat] using finalSat

theorem cfbDecryptFinal_implies8 : cfbDecFinalX86_64.Implies (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 121
      (Curry.const (fun _ => True) _) (Proof.Modes.decFinalPost ciphAt 8 X86_64.abi.ptrBits) true 8) :=
  cfbDecryptFinal_implies.stack8_abi (by
    sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      X86_64.abi, X86_64.argRegs, finalSat] [finalSat] using finalSat)

/-- The data and the IV are apart from the call's return address. -/
theorem cfbDecryptFinal_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 121
      (Curry.const (fun _ => True) _) (Proof.Modes.decFinalPost ciphAt 8 X86_64.abi.ptrBits) true 8).pre s) (hp : cfbDecFinalX86_64.post s b) :
    cfbDecFinalX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := cfbDecryptFinal_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := finalLen s)
    (by rw [hwr]; simp) (by omega)
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega)
  obtain ⟨h₁, h₂⟩ := hp
  exact ⟨by rw [aesBytesAt_congr (patch_mem hbD)]; exact h₁, by rw [aesBytesAt_congr (patch_mem hbI)]; exact h₂⟩

theorem cfbDecryptFinal_inline : cfbDecryptFinal.inline = cfbDecryptFinalI := rfl

theorem cfbDecryptFinal_verified : Verified X86_64.target cfbDecryptFinal (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 121
      (Curry.const (fun _ => True) _) (Proof.Modes.decFinalPost ciphAt 8 X86_64.abi.ptrBits) true 8) :=
  Verified.of_inline_ct (by lit_decide) (fun s hs => by rw [cfbDecryptFinal_inline]; exact cfbDecryptFinal_correct s hs)
    cfbDecryptFinal_ct cfbDecryptFinal_implies8 (fun _ h => Sig.clear_of_pre h) cfbDecryptFinal_patch

/-- The final CFB64 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cfbEncryptFinal)
      (Spec.TripleDes.cfbEncryptFinalContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.Modes.encFinalPost ciphAt 8 X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) cfbEncryptFinal_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Modes.encFinalPost_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- The final CFB64 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cfbDecryptFinal)
      (Spec.TripleDes.cfbDecryptFinalContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.Modes.decFinalPost ciphAt 8 X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) cfbDecryptFinal_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Modes.decFinalPost_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## OFB of a message's last piece -/

/-- The final OFB function's contract on x86-64: the data `len = rcx` bytes
long, and the data and the IV as `Spec.Ofb.CryptFinal` says. -/
def ofbFinalX86_64 : Contract isa where
  pre := fbPre finalLen
  post s s' := Spec.Ofb.CryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .rsi) (s.gpr .rdx) (finalLen s)
  pub := fbPub

theorem ofbFinal_wp {s₀ : State} (hp : ofbFinalX86_64.pre s₀) :
    WP isa ofbFinalI s₀ fun s' => gprPreserved s₀ s' ∧ ofbFinalX86_64.post s₀ s' :=
  WP.mono (fbFinal_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofbFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem ofbFinal_correct (s : State) (hs : ofbFinalX86_64.pre s) :
    ∃ t s', Exec isa ofbFinalI s t s' ∧ abiPreserved s s' ∧ ofbFinalX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := ofbFinal_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := ofbFinalI) (by lit_decide) he hg, hpost⟩

theorem ofbFinal_ct : ConstantTime isa ofbFinalX86_64.pre ofbFinalX86_64.pub ofbFinal := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint ofbFinal h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree finalLen_congr) h

theorem ofbFinal_implies : ofbFinalX86_64.Implies (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 121
      (Curry.const (fun _ => True) _) (Proof.Modes.ofbFinalPost ciphAt 8 X86_64.abi.ptrBits) true 0) := by
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
    Proof.Modes.ofbFinalPost, ofbFinalX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [finalSat] using finalSat

theorem ofbFinal_implies8 : ofbFinalX86_64.Implies (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 121
      (Curry.const (fun _ => True) _) (Proof.Modes.ofbFinalPost ciphAt 8 X86_64.abi.ptrBits) true 8) :=
  ofbFinal_implies.stack8_abi (by
    sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      X86_64.abi, X86_64.argRegs, finalSat] [finalSat] using finalSat)

/-- The data and the IV are apart from the call's return address. -/
theorem ofbFinal_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 121
      (Curry.const (fun _ => True) _) (Proof.Modes.ofbFinalPost ciphAt 8 X86_64.abi.ptrBits) true 8).pre s) (hp : ofbFinalX86_64.post s b) :
    ofbFinalX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := ofbFinal_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := finalLen s)
    (by rw [hwr]; simp) (by omega)
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega)
  obtain ⟨h₁, h₂⟩ := hp
  exact ⟨by rw [aesBytesAt_congr (patch_mem hbD)]; exact h₁, by rw [aesBytesAt_congr (patch_mem hbI)]; exact h₂⟩

theorem ofbFinal_inline : ofbFinal.inline = ofbFinalI := rfl

theorem ofbFinal_verified : Verified X86_64.target ofbFinal (Sig.scratchContract X86_64.abi finalSig "scratch" .u64 121
      (Curry.const (fun _ => True) _) (Proof.Modes.ofbFinalPost ciphAt 8 X86_64.abi.ptrBits) true 8) :=
  Verified.of_inline_ct (by lit_decide) (fun s hs => by rw [ofbFinal_inline]; exact ofbFinal_correct s hs)
    ofbFinal_ct ofbFinal_implies8 (fun _ h => Sig.clear_of_pre h) ofbFinal_patch

/-- The final OFB function with its working space on the stack. -/
theorem ofbFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 ofbFinal)
      (Spec.TripleDes.ofbFinalContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.ofbFinalSig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.Modes.ofbFinalPost ciphAt 8 X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) ofbFinal_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Modes.ofbFinalPost_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.TripleDes.X86_64
