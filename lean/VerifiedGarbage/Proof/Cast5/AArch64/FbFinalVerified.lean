module

public import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
public import VerifiedGarbage.Proof.Cast5.CfbFinal
import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.ModeScratch
import VerifiedGarbage.Proof.Cast5.AArch64.ModeCore
public import VerifiedGarbage.Proof.Cast5.AArch64.EcbVerified
import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
public import VerifiedGarbage.Proof.Modes.FbFinal
import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
import VerifiedGarbage.Proof.Cast5.AArch64.Lit
public import VerifiedGarbage.Impl.Cast5.AArch64.FbFinal
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Cast5.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Cast5.CfbFinal
meta import VerifiedGarbage.Proof.Cast5.Rounds
meta import VerifiedGarbage.Proof.Cast5.ModeScratch
meta import VerifiedGarbage.Proof.Cast5.AArch64.ModeCore
meta import VerifiedGarbage.Proof.Cast5.AArch64.EcbVerified
meta import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Modes.FbFinal
meta import VerifiedGarbage.Proof.Cast5.AArch64.FbFinalLit
meta import VerifiedGarbage.Proof.Cast5.AArch64.ModesLit
meta import VerifiedGarbage.Proof.Cast5.AArch64.Lit
meta import VerifiedGarbage.Impl.Cast5.AArch64.FbFinal
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# CAST5-CFB64 and CAST5-OFB of a message's last piece on AArch64 meet their contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`, `ofbFinal_wp`: the modes' CFB and
OFB over a message's last piece (`Proof.Modes.AArch64.fbFinal_wp`) over
CAST5's core (`Mode.dirCoreSpec true`), with the IV's address in `x25`, as
for the whole-block functions (`FbVerified.lean`), and the specification's
results (`Proof.Modes.cfbEncFinal_of_bytes`, …,
`Proof.Modes.ofbFinal_of_bytes`). `cfbEncryptFinal_verified`, …: each is
correct and constant time, by the taint analysis, as the whole-block
functions are, for the subkeys at `schedule` (`Proof.Cast5.cfbEncFinalPost`);
`cfbEncryptFinal_framed`, … run them with their working space on the stack,
zeroed on return: 112 bytes, the 13 words of the scratch buffer and 8 more.
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Cast5.AArch64.Mode (dirCoreSpec TabAt SchedAt dirCore_bw)

/-- The data's length, in bytes. -/
abbrev finalLen (s : State) : Nat := (s.gpr .x4).toNat

/-- What the modes' OFB and CFB over a message's last piece give, for a mode
`mo`: each byte of the data that of `fbOut` of its block, and the IV
`fbNextF`, keeping the callee-saved registers. -/
theorem fbFinal_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : FPre finalLen s₀) :
    WP isa ((dirCore true).fbFinal mo modeRegs .x25) s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧
      (∀ i < finalLen s₀, s'.mem (s₀.gpr .x3 + BitVec.ofNat 64 i) =
        (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (i / 8)).getD (i % 8) 0) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .x2) 8 =
        Modes.fbNextF mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .x3) (ivOf s₀) (finalLen s₀) := by
  have hwS : (⟨s₀.gpr .x5, 8 * 13⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.mono (Proof.Modes.AArch64.fbFinal_wp (dirCoreSpec true) mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide) (ivR := .x25)
    ⟨by decide, by decide, by decide, by decide, by decide⟩
    (B := s₀.gpr .x5) (P := s₀.gpr .x2) (D := s₀.gpr .x3) (len := finalLen s₀)
    (k := (keyOf s₀, (s₀.gpr .x1).toNat)) rfl rfl rfl rfl ⟨hwS, hp.fS⟩
    (by rw [hp.wr]; simp) (by rw [hp.wr]; simp) hp.dVS hp.dDS hp.dVD hp.fD
    ⟨⟨s₀.gpr .x0, rfl, rfl, hp.schedAt, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dKS⟩,
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hp.rounds, hp.tabAt, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dTS⟩ Mode.crypt_keeps)
    fun s' ⟨hcs, hdata, hiv, _, _, _⟩ => ⟨hcs, by rw [dirCore_bw] at hdata hiv; exact ⟨hdata, hiv⟩⟩

theorem cipher_length (s : State) (x : List Byte) : (ciphOf s x).length = 8 := by
  simp [Spec.Cast5.cipher]

/-- The final encryption's contract on AArch64: the data `len = x4` bytes
long, and the data and the IV as `Spec.Cfb.EncryptFinal` says. -/
def cfbEncFinalX : Contract isa where
  pre := FPre finalLen
  post s s' := Spec.Cfb.EncryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .x2) (s.gpr .x3) (finalLen s)
  pub := cbcPub

/-- The final decryption's contract on AArch64. -/
def cfbDecFinalX : Contract isa where
  pre := FPre finalLen
  post s s' := Spec.Cfb.DecryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .x2) (s.gpr .x3) (finalLen s)
  pub := cbcPub

theorem cfbEncryptFinal_wp {s₀ : State} (hp : cfbEncFinalX.pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbEncFinalX.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEncFinal_of_bytes (by decide) (cipher_length s₀) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : cfbDecFinalX.pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cfbDecFinalX.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDecFinal_of_bytes (by decide) (cipher_length s₀) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbEncryptFinal_ct : ConstantTime isa cfbEncFinalX.pre cfbEncFinalX.pub cfbEncryptFinal :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs modePub) fbTaint_agree (by taint_decide)

theorem cfbDecryptFinal_ct : ConstantTime isa cfbDecFinalX.pre cfbDecFinalX.pub cfbDecryptFinal :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs modePub) fbTaint_agree (by taint_decide)

/-! ## The contracts -/

/-- The final functions' contract with the working space as a sixth argument,
under the calling convention with the table. -/
abbrev finalK (post : Spec.Cast5.cfbFinalSig.Post AArch64.abi.ptrBits) : Contract isa :=
  Proof.Cast5.modeScratchContract (AArch64.abi.withConsts ecbConsts) Spec.Cast5.cfbFinalSig 13
    (Spec.Cast5.cfbFinalPre AArch64.abi.ptrBits) post

/-- A state satisfying the precondition: one byte, 16 rounds. -/
def finalSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | .x5 => 0x4000 | _ => 0
  sp := 0x8000
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩, ⟨0x4000, 104⟩]
  syms _ := 0x100000

theorem final_implies {postX : State → State → Prop} {post : Spec.Cast5.cfbFinalSig.Post AArch64.abi.ptrBits}
    (hpost : ∀ s s', postX s s' → (finalK post).post s s') :
    ({ pre := FPre finalLen, post := postX, pub := cbcPub } : Contract isa).Implies (finalK post) where
  pre s h := by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig,
      Spec.Cast5.cfbFinalPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch] at h
    obtain ⟨hdr, hheld, hfit, hdw, -, htk, hw, dKV, dKD, dKS, dVD, dVS, dDS, fK, -, fD, fS, hr⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), dKV, dKD, dKS,
      dVD, dVS, dDS, fK, fD, fS, hr⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ hq := hpost s s' hq
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig,
      AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
    obtain ⟨hsp, hsy, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, hsp, hsy⟩
  sat := ⟨finalSat, by
    generalize e : finalSat = s
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig,
      Spec.Cast5.cfbFinalPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch]
    subst s
    refine ⟨rfl, ecbSatMem_held, by decide, ?_, ?_⟩
    · intro r hr
      change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 1⟩, ⟨0x4000, 104⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · repeat' apply And.intro
      all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)⟩

theorem cfbEncryptFinal_verified :
    Verified AArch64.target cfbEncryptFinal (finalK (Proof.Cast5.cfbEncFinalPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbEncryptFinal_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    cfbEncryptFinal_ct (final_implies (post := Proof.Cast5.cfbEncFinalPost AArch64.abi.ptrBits) fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig,
        Proof.Cast5.cfbEncFinalPost, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

theorem cfbDecryptFinal_verified :
    Verified AArch64.target cfbDecryptFinal (finalK (Proof.Cast5.cfbDecFinalPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (cfbDecryptFinal_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    cfbDecryptFinal_ct (final_implies (post := Proof.Cast5.cfbDecFinalPost AArch64.abi.ptrBits) fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig,
        Proof.Cast5.cfbDecFinalPost, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

/-! ## The functions with their working space on the stack -/

/-- A state satisfying the functions' precondition, with 112 bytes of stack. -/
def finalFrameSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 16 | .x2 => 0x2000 | .x3 => 0x3000 | .x4 => 1 | _ => 0
  sp := 0x8000
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩]
  syms _ := 0x100000

theorem finalFrame_sat (post : Spec.Cast5.cfbFinalSig.Post AArch64.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cfbFinalSig.contract (AArch64.abi.withConsts ecbConsts)
      (Spec.Cast5.cfbFinalPre AArch64.abi.ptrBits) post true (0 + 112)).pre s := by
  refine ⟨finalFrameSat, ?_⟩
  generalize e : finalFrameSat = s
  sig_pre [Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, AArch64.abi, AArch64.argRegs, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  refine ⟨by decide, rfl, ecbSatMem_held, by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 1⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

/-- The final CFB64 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 cfbEncryptFinal)
      (Proof.Cast5.cfbEncryptFinalRoundsContract (AArch64.abi.withConsts ecbConsts) 112) :=
  AArch64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbFinalSig)
    (nm := "scratch") (e := .u64) (n := 13) (pre := Spec.Cast5.cfbFinalPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.cfbEncFinalPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 112)
    cfbEncryptFinal_verified (by decide) (by decide) (by decide) (Proof.Cast5.cfbEncFinalPostOut_local _)
    (finalFrame_sat _)

/-- The final CFB64 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 cfbDecryptFinal)
      (Proof.Cast5.cfbDecryptFinalRoundsContract (AArch64.abi.withConsts ecbConsts) 112) :=
  AArch64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbFinalSig)
    (nm := "scratch") (e := .u64) (n := 13) (pre := Spec.Cast5.cfbFinalPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.cfbDecFinalPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 112)
    cfbDecryptFinal_verified (by decide) (by decide) (by decide) (Proof.Cast5.cfbDecFinalPostOut_local _)
    (finalFrame_sat _)

/-! ## OFB of a message's last piece -/

/-- The final OFB function's contract on AArch64: the data `len = x4` bytes
long, and the data and the IV as `Spec.Ofb.CryptFinal` says. -/
def ofbFinalX : Contract isa where
  pre := FPre finalLen
  post s s' := Spec.Ofb.CryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .x2) (s.gpr .x3) (finalLen s)
  pub := cbcPub

theorem ofbFinal_wp {s₀ : State} (hp : ofbFinalX.pre s₀) :
    WP isa ofbFinal s₀ fun s' => (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
      s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ ofbFinalX.post s₀ s' :=
  WP.mono (fbFinal_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofbFinal_of_bytes (by decide) (cipher_length s₀) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem ofbFinal_ct : ConstantTime isa ofbFinalX.pre ofbFinalX.pub ofbFinal :=
  VG.Taint.constantTime (A := taintS [s1234Sym]) (Taint.ofRegs modePub) fbTaint_agree (by taint_decide)

theorem ofbFinal_verified :
    Verified AArch64.target ofbFinal (finalK (Proof.Cast5.ofbFinalPost AArch64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := WP.gprs (rs := [.x30]) (ofbFinal_wp hs) (by lit_decide)
        (by lit_decide)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    ofbFinal_ct (final_implies (post := Proof.Cast5.ofbFinalPost AArch64.abi.ptrBits) fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbFinalSig,
        Proof.Cast5.ofbFinalPost, AArch64.abi, AArch64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

/-- The final OFB function with its working space on the stack. -/
theorem ofbFinal_framed :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 112 .x5 13 ofbFinal)
      (Proof.Cast5.ofbFinalRoundsContract (AArch64.abi.withConsts ecbConsts) 112) :=
  AArch64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.ofbFinalSig)
    (nm := "scratch") (e := .u64) (n := 13) (pre := Spec.Cast5.ofbFinalPre AArch64.abi.ptrBits)
    (post := Proof.Cast5.ofbFinalPost AArch64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 112)
    ofbFinal_verified (by decide) (by decide) (by decide) (Proof.Cast5.ofbFinalPostOut_local _)
    (finalFrame_sat _)

end VG.Proof.Cast5.AArch64
