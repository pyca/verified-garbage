module

public import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
public import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalVerified
public import VerifiedGarbage.Proof.Sm4.FbScratch
public import VerifiedGarbage.Proof.Sm4.CbcScratch
public import VerifiedGarbage.Proof.Modes.FbFinal
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Spec.Sm4.Cfb
public import VerifiedGarbage.Spec.Sm4.Cbc
public import VerifiedGarbage.Spec.Sm4.CfbFinal
public import VerifiedGarbage.Spec.Sm4.OfbFinal
import VerifiedGarbage.Proof.Modes.AArch64.Fb
import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Sm4.AArch64.Sm4e.Modes
meta import VerifiedGarbage.Proof.Sm4.AArch64.FbFinalVerified
meta import VerifiedGarbage.Proof.Sm4.FbScratch
meta import VerifiedGarbage.Proof.Sm4.CbcScratch
meta import VerifiedGarbage.Proof.Modes.FbFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Spec.Sm4.Cfb
meta import VerifiedGarbage.Spec.Sm4.Cbc
meta import VerifiedGarbage.Spec.Sm4.CfbFinal
meta import VerifiedGarbage.Spec.Sm4.OfbFinal
meta import VerifiedGarbage.Proof.Modes.AArch64.Fb
meta import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Modes.AArch64.CbcEncChained
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# SM4's chained modes with the Armv8 SM4 instructions

CBC encryption, OFB and CFB128 encryption, and OFB and CFB128 (either
direction) of a message's last piece: the modes whose blocks each depend on
the one before (`Proof.Modes.AArch64.cbcEncryptChained_wp`, `fb_wp`,
`fbFinal_wp`), over the core of one block with `sm4e` (`coreSpec1 .encrypt`,
`Modes.lean`), with the IV's address kept in `x19`: the core writes no
general-purpose register (`keeps_x19`), and reads the schedule through
`x0`, which these modes do not write either (it is none of `modeRegs`, as
`CoreSpec.ready_frame` needs, nor the register of the IV's address).

Each `_verified` is the function with its working space of 14 words as an
argument, correct and constant time by the taint analysis, as the modes of
`Modes.lean`; each `_framed` runs it with the working space on the stack,
zeroed on return: 112 bytes.
-/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Sm4e

open VG VG.AArch64
open VG.Impl.Sm4.AArch64.Sm4e
open VG.Impl.Modes (FbMode)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.AArch64 (finalSig ciphAt cipher_length finalLen)

/-- The core of one block writes no general-purpose register. -/
theorem keeps_x19 : Modes.AArch64.KeepsReg .x19 (core1 .encrypt).prepare ∧
    Modes.AArch64.KeepsReg .x19 (core1 .encrypt).crypt :=
  ⟨Modes.AArch64.keepsReg_of_regSafe (by decide), Modes.AArch64.keepsReg_of_regSafe (by decide)⟩

/-- The cipher of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Sm4.cipher (schedOf s)

attribute [local irreducible] Spec.Sm4.cipher in
/-- The core's cipher is the contracts', without unfolding it. -/
theorem cipher1_eq (k : Spec.Sm4.Schedule) : ((coreSpec1 .encrypt).toBlock rfl).cipher k = Spec.Sm4.cipher k :=
  rfl

/-! ## The contracts with the working space at `x4` -/

def cbcEncC : Contract isa where
  pre := mPre 14 blkLen
  post s s' := blocksOf s s'.mem = Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    bytesAt s'.mem (s.gpr .x1) 16 =
      Spec.Cbc.next (ivOf s) (Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := mPub

def ofbC : Contract isa where
  pre := mPre 14 blkLen
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    bytesAt s'.mem (s.gpr .x1) 16 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .x3).toNat
  pub := mPub

def cfbEncC : Contract isa where
  pre := mPre 14 blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    bytesAt s'.mem (s.gpr .x1) 16 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := mPub

/-- The final functions' contracts: the data `len = x3` bytes long. -/
def cfbEncFinalC : Contract isa where
  pre := mPre 14 finalLen
  post s s' := Spec.Cfb.EncryptFinal (ciphOf s) 16 s.mem s'.mem (s.gpr .x1) (s.gpr .x2) (finalLen s)
  pub := mPub

def cfbDecFinalC : Contract isa where
  pre := mPre 14 finalLen
  post s s' := Spec.Cfb.DecryptFinal (ciphOf s) 16 s.mem s'.mem (s.gpr .x1) (s.gpr .x2) (finalLen s)
  pub := mPub

def ofbFinalC : Contract isa where
  pre := mPre 14 finalLen
  post s s' := Spec.Ofb.CryptFinal (ciphOf s) 16 s.mem s'.mem (s.gpr .x1) (s.gpr .x2) (finalLen s)
  pub := mPub

/-- The scratch buffer of the precondition is the only region the key must
be outside of before `prepare`. -/
theorem keyArgs_scr {len : State → Nat} {s : State} (hp : mPre 14 len s) :
    KeyArgs s [⟨s.gpr .x4, 8 * 14⟩] (schedOf s) :=
  keyArgs_of_pre' hp _ fun r hr => by
    rw [hp.2.1]
    simp only [List.mem_singleton] at hr
    subst hr
    simp

/-! ## The modes -/

theorem cbcEncryptChained_wp {s₀ : State} (hp : cbcEncC.pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => Saved s₀ s' ∧ cbcEncC.post s₀ s' := by
  have hk : KeyArgs s₀ [⟨s₀.gpr .x4, 8 * 14⟩, ⟨s₀.gpr .x2, 16 * (s₀.gpr .x3).toNat⟩] (schedOf s₀) :=
    keyArgs_of_pre' hp _ fun r hr => by
      rw [hp.2.1]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl
      · exact .inr (.inr rfl)
      · exact .inr (.inl rfl)
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 14⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.cbcEncryptChained_wp ((coreSpec1 .encrypt).toBlock rfl)
    (r := ⟨.x1, .x2, .x3, .x4⟩) ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x19)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := schedOf s₀) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD hk keeps_x19)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [cipher1_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the IV
as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : FbMode) {s₀ : State} (hp : mPre 14 blkLen s₀) :
    WP isa (fb mo) s₀ fun s' => Saved s₀ s' ∧
      Modes.blocksOf 16 s'.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat =
        (List.range (s₀.gpr .x3).toNat).map (Modes.fbOut mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀)) ∧
      bytesAt s'.mem (s₀.gpr .x1) 16 =
        Modes.fbIn mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat := by
  have hk := keyArgs_scr hp
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 14⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.fb_wp ((coreSpec1 .encrypt).toBlock rfl) mo (r := ⟨.x1, .x2, .x3, .x4⟩)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x19)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (n := (s₀.gpr .x3).toNat)
    (k := schedOf s₀) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD hk keeps_x19)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [cipher1_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem ofb_wp {s₀ : State} (hp : ofbC.pre s₀) : WP isa (fb .ofb) s₀ fun s' => Saved s₀ s' ∧ ofbC.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncC.pre s₀) :
    WP isa (fb .cfbEnc) s₀ fun s' => Saved s₀ s' ∧ cfbEncC.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (s₀.gpr .x3).toNat
    exact ⟨hg, hd.trans h1, hv.trans h2⟩

/-- What the modes' OFB and CFB over a message's last piece give, for a mode
`mo`: each byte of the data that of `fbOut` of its block, and the IV
`fbNextF`, keeping the callee-saved registers. -/
theorem fbFinal_wp' (mo : FbMode) {s₀ : State} (hp : mPre 14 finalLen s₀) :
    WP isa (fbFinal mo) s₀ fun s' => Saved s₀ s' ∧
      (∀ i < finalLen s₀, s'.mem (s₀.gpr .x2 + BitVec.ofNat 64 i) =
        (Modes.fbOut mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (i / 16)).getD (i % 16) 0) ∧
      bytesAt s'.mem (s₀.gpr .x1) 16 =
        Modes.fbNextF mo 16 (ciphOf s₀) s₀.mem (s₀.gpr .x2) (ivOf s₀) (finalLen s₀) := by
  have hk := keyArgs_scr hp
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .x4, 8 * 14⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.AArch64.fbFinal_wp ((coreSpec1 .encrypt).toBlock rfl) mo
    (r := ⟨.x1, .x2, .x3, .x4⟩) ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x19)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x4) (P := s₀.gpr .x1) (D := s₀.gpr .x2) (len := finalLen s₀)
    (k := schedOf s₀) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD hk keeps_x19)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [cipher1_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem cfbEncryptFinal_wp {s₀ : State} (hp : cfbEncFinalC.pre s₀) :
    WP isa (fbFinal .cfbEnc) s₀ fun s' => Saved s₀ s' ∧ cfbEncFinalC.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEncFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : cfbDecFinalC.pre s₀) :
    WP isa (fbFinal .cfbDec) s₀ fun s' => Saved s₀ s' ∧ cfbDecFinalC.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDecFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem ofbFinal_wp {s₀ : State} (hp : ofbFinalC.pre s₀) :
    WP isa (fbFinal .ofb) s₀ fun s' => Saved s₀ s' ∧ ofbFinalC.post s₀ s' :=
  WP.mono (fbFinal_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofbFinal_of_bytes (by decide) (cipher_length _) hd
    exact ⟨hg, h1, hv.trans h2⟩

/-! ## Verified -/

/-- A state satisfying the precondition (one block). -/
def mSat1 : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 16⟩, ⟨0x4000, 8 * 14⟩]

/-- A state satisfying the final functions' precondition (one byte). -/
def finalSat1 : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 1 | .x4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 1⟩, ⟨0x4000, 8 * 14⟩]

theorem cbcEncryptChained_verified :
    Verified AArch64.target cbcEncryptChained (Proof.Sm4.cbcEncChainedScratchContract AArch64.abi 14) :=
  Verified.of_correct
    (correct_of (k := cbcEncC) (fun _ => cbcEncryptChained_wp) (by lit_decide) (by lit_decide) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) taint_agree (by taint_decide))
    (by
      sig_implies [Proof.Sm4.cbcEncChainedScratchContract, Proof.Sm4.cbcChainedScratchSig, Spec.Sm4.cbcChainedSig,
        Proof.Sm4.cbcEncChainedPost, cbcEncC, mPre, mPub, AArch64.abi, AArch64.argRegs] [mSat1] using mSat1)

theorem ofb_verified :
    Verified AArch64.target (fb .ofb) (Proof.Sm4.fbScratchContract AArch64.abi 14 Proof.Sm4.ofbPost) :=
  Verified.of_correct
    (correct_of (k := ofbC) (fun _ => ofb_wp) (by lit_decide) (by lit_decide) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) taint_agree (by taint_decide))
    (by
      sig_implies [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig, Proof.Sm4.ofbPost,
        ofbC, mPre, mPub, AArch64.abi, AArch64.argRegs] [mSat1] using mSat1)

theorem cfbEncrypt_verified :
    Verified AArch64.target (fb .cfbEnc) (Proof.Sm4.fbScratchContract AArch64.abi 14 Proof.Sm4.cfbEncPost) :=
  Verified.of_correct
    (correct_of (k := cfbEncC) (fun _ => cfbEncrypt_wp) (by lit_decide) (by lit_decide) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) taint_agree (by taint_decide))
    (by
      sig_implies [Proof.Sm4.fbScratchContract, Proof.Sm4.fbScratchSig, Spec.Sm4.ofbSig, Proof.Sm4.cfbEncPost,
        cfbEncC, mPre, mPub, AArch64.abi, AArch64.argRegs] [mSat1] using mSat1)

theorem cfbEncryptFinal_verified :
    Verified AArch64.target (fbFinal .cfbEnc) (Sig.scratchContract AArch64.abi finalSig "scratch" .u64
      14 (Curry.const (fun _ => True) _) (Proof.Modes.encFinalPost ciphAt 16 AArch64.abi.ptrBits) true 0) :=
  Verified.of_correct
    (correct_of (k := cfbEncFinalC) (fun _ => cfbEncryptFinal_wp) (by lit_decide) (by lit_decide) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) taint_agree (by taint_decide))
    (by
      sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
        Proof.Modes.encFinalPost, cfbEncFinalC, mPre, mPub, AArch64.abi, AArch64.argRegs] [finalSat1]
        using finalSat1)

theorem cfbDecryptFinal_verified :
    Verified AArch64.target (fbFinal .cfbDec) (Sig.scratchContract AArch64.abi finalSig "scratch" .u64
      14 (Curry.const (fun _ => True) _) (Proof.Modes.decFinalPost ciphAt 16 AArch64.abi.ptrBits) true 0) :=
  Verified.of_correct
    (correct_of (k := cfbDecFinalC) (fun _ => cfbDecryptFinal_wp) (by lit_decide) (by lit_decide) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) taint_agree (by taint_decide))
    (by
      sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
        Proof.Modes.decFinalPost, cfbDecFinalC, mPre, mPub, AArch64.abi, AArch64.argRegs] [finalSat1]
        using finalSat1)

theorem ofbFinal_verified :
    Verified AArch64.target (fbFinal .ofb) (Sig.scratchContract AArch64.abi finalSig "scratch" .u64
      14 (Curry.const (fun _ => True) _) (Proof.Modes.ofbFinalPost ciphAt 16 AArch64.abi.ptrBits) true 0) :=
  Verified.of_correct
    (correct_of (k := ofbFinalC) (fun _ => ofbFinal_wp) (by lit_decide) (by lit_decide) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) taint_agree (by taint_decide))
    (by
      sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
        Proof.Modes.ofbFinalPost, ofbFinalC, mPre, mPub, AArch64.abi, AArch64.argRegs] [finalSat1]
        using finalSat1)

/-! ## The working space on the stack -/

open VG.Proof.Sm4.AArch64 (finalFrameSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.Sm4.cbcEncryptChainedContract AArch64.abi 112).pre s := by
  implies_sat [Spec.Sm4.cbcEncryptChainedContract, Spec.Sm4.cbcChainedSig, AArch64.abi, AArch64.argRegs]
    [frameSat] using frameSat

theorem ofbFrameSat_pre : ∃ s, (Spec.Sm4.ofbContract AArch64.abi 112).pre s := by
  implies_sat [Spec.Sm4.ofbContract, Spec.Sm4.ofbSig, AArch64.abi, AArch64.argRegs] [frameSat] using frameSat

theorem cfbEncFrameSat_pre : ∃ s, (Spec.Sm4.cfbEncryptContract AArch64.abi 112).pre s := by
  implies_sat [Spec.Sm4.cfbEncryptContract, Spec.Sm4.cfbSig, Spec.Sm4.ofbSig, AArch64.abi, AArch64.argRegs]
    [frameSat] using frameSat

theorem cfbEncFinalFrameSat_pre : ∃ s, (Spec.Sm4.cfbEncryptFinalContract AArch64.abi 112).pre s := by
  implies_sat [Spec.Sm4.cfbEncryptFinalContract, Spec.Sm4.cfbFinalSig, AArch64.abi, AArch64.argRegs]
    [finalFrameSat] using finalFrameSat

theorem cfbDecFinalFrameSat_pre : ∃ s, (Spec.Sm4.cfbDecryptFinalContract AArch64.abi 112).pre s := by
  implies_sat [Spec.Sm4.cfbDecryptFinalContract, Spec.Sm4.cfbFinalSig, AArch64.abi, AArch64.argRegs]
    [finalFrameSat] using finalFrameSat

theorem ofbFinalFrameSat_pre : ∃ s, (Spec.Sm4.ofbFinalContract AArch64.abi 112).pre s := by
  implies_sat [Spec.Sm4.ofbFinalContract, Spec.Sm4.ofbFinalSig, AArch64.abi, AArch64.argRegs]
    [finalFrameSat] using finalFrameSat

/-- `vg_sm4_cbc_encrypt_chained_sm4`: CBC encryption with its working space
on the stack. -/
theorem cbcEncryptChained_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 cbcEncryptChained)
      (Spec.Sm4.cbcEncryptChainedContract AArch64.abi 112) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 14) (post := Proof.Sm4.cbcEncChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 112) cbcEncryptChained_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.cbcEncChainedPostOut_local _) cbcEncFrameSat_pre

/-- `vg_sm4_ofb_sm4`: OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 (fb .ofb))
      (Spec.Sm4.ofbContract AArch64.abi 112) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.ofbSig) (nm := "scratch") (e := .u64)
    (n := 14) (post := Proof.Sm4.ofbPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 112) ofb_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.ofbPostOut_local _) ofbFrameSat_pre

/-- `vg_sm4_cfb128_encrypt_sm4`: CFB128 encryption with its working space on
the stack. -/
theorem cfbEncrypt_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 (fb .cfbEnc))
      (Spec.Sm4.cfbEncryptContract AArch64.abi 112) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.cfbSig) (nm := "scratch") (e := .u64)
    (n := 14) (post := Proof.Sm4.cfbEncPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 112) cfbEncrypt_verified
    (by decide) (by decide) (by decide) (Proof.Sm4.cfbEncPostOut_local _) cfbEncFrameSat_pre

/-- `vg_sm4_cfb128_encrypt_final_sm4`. -/
theorem cfbEncryptFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 (fbFinal .cfbEnc))
      (Spec.Sm4.cfbEncryptFinalContract AArch64.abi 112) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 14) (post := Proof.Modes.encFinalPost ciphAt 16 AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 112) cfbEncryptFinal_verified
    (by decide) (by decide) (by decide) (Proof.Modes.encFinalPost_local _) cfbEncFinalFrameSat_pre

/-- `vg_sm4_cfb128_decrypt_final_sm4`. -/
theorem cfbDecryptFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 (fbFinal .cfbDec))
      (Spec.Sm4.cfbDecryptFinalContract AArch64.abi 112) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 14) (post := Proof.Modes.decFinalPost ciphAt 16 AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 112) cfbDecryptFinal_verified
    (by decide) (by decide) (by decide) (Proof.Modes.decFinalPost_local _) cfbDecFinalFrameSat_pre

/-- `vg_sm4_ofb_final_sm4`. -/
theorem ofbFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x4 14 (fbFinal .ofb))
      (Spec.Sm4.ofbFinalContract AArch64.abi 112) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Sm4.ofbFinalSig) (nm := "scratch") (e := .u64)
    (n := 14) (post := Proof.Modes.ofbFinalPost ciphAt 16 AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 112) ofbFinal_verified
    (by decide) (by decide) (by decide) (Proof.Modes.ofbFinalPost_local _) ofbFinalFrameSat_pre

end VG.Proof.Sm4.AArch64.Sm4e
