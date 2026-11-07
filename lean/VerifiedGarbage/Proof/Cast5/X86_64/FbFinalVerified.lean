module

public import VerifiedGarbage.Proof.Cast5.X86_64.FbVerified
public import VerifiedGarbage.Proof.Cast5.CfbFinal
import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.ModeScratch
import VerifiedGarbage.Proof.Cast5.X86_64.ModeCore
public import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
public import VerifiedGarbage.Proof.Modes.FbFinal
import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalLit
import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
public import VerifiedGarbage.Impl.Cast5.X86_64.FbFinal
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Modes.X86_64.KeepIv
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Cast5.X86_64.FbVerified
meta import VerifiedGarbage.Proof.Cast5.CfbFinal
meta import VerifiedGarbage.Proof.Cast5.Rounds
meta import VerifiedGarbage.Proof.Cast5.ModeScratch
meta import VerifiedGarbage.Proof.Cast5.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
meta import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Modes.FbFinal
meta import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalLit
meta import VerifiedGarbage.Proof.Cast5.X86_64.ModesLit
meta import VerifiedGarbage.Impl.Cast5.X86_64.FbFinal
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Modes.X86_64.KeepIv
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# CAST5-CFB64 of a message's last piece on x86-64 meets its contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`: the modes' CFB over a message's
last piece (`Proof.Modes.X86_64.fbFinal_wp`) over CAST5's core, with the
specification's results (`Proof.Modes.cfbEncFinal_of_bytes`, …).
`cfbEncryptFinal_verified`, …: each is correct and constant time, by the
taint analysis, as the whole-block functions are (`FbVerified.lean`);
`cfbEncryptFinal_framed`, … run them with their working space on the stack,
zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.Impl.Cast5.X86_64
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Cast5.X86_64.Mode (dirCoreSpec TabAt dirCore_bw)

/-- The data's length, in bytes. -/
abbrev finalLen (s : State) : Nat := (s.gpr .r8).toNat

theorem finalLen_congr : ∀ s t : State, s.gpr .r8 = t.gpr .r8 → finalLen s = finalLen t := fun _ _ h => by
  simp only [finalLen, h]

/-- What the modes' OFB and CFB over a message's last piece give, for a mode
`mo`: each byte of the data that of `fbOut` of its block, and the IV
`fbNextF`, keeping the callee-saved registers. -/
theorem fbFinal_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : FPre finalLen s₀) :
    WP isa ((dirCore true).fbFinal mo modeRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      (∀ i < finalLen s₀, s'.mem (s₀.gpr .rcx + BitVec.ofNat 64 i) =
        (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (i / 8)).getD (i % 8) 0) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rdx) 8 =
        Modes.fbNextF mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rcx) (ivOf s₀) (finalLen s₀) := by
  have hwS : (⟨s₀.gpr .r9, 8 * 29⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.mono (Proof.Modes.X86_64.fbFinal_wp (dirCoreSpec true) mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r9) (P := s₀.gpr .rdx) (D := s₀.gpr .rcx) (len := finalLen s₀)
    (k := (keyOf s₀, (s₀.gpr .rsi).toNat)) rfl rfl rfl rfl ⟨hwS, hp.fS⟩
    (by rw [hp.wr]; simp) (by rw [hp.wr]; simp) hp.dVS hp.dDS hp.dVD hp.fD
    ⟨⟨s₀.gpr .rdi, rfl, rfl, by rw [hp.rd]; simp, hp.fK, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dKS⟩,
      by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq], hp.rounds, hp.tabAt, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.dTS⟩ keepsIv_core)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, by rw [dirCore_bw] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.dRS
  · exact hp.dRD
  · exact hp.dRV

theorem cipher_length (s : State) (x : List Byte) : (ciphOf s x).length = 8 := by
  simp [Spec.Cast5.cipher]

/-- The final encryption's contract on x86-64: the data `len = r8` bytes
long, and the data and the IV as `Spec.Cfb.EncryptFinal` says. -/
def cfbEncFinalX : Contract isa where
  pre := FPre finalLen
  post s s' := Spec.Cfb.EncryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .rdx) (s.gpr .rcx) (finalLen s)
  pub := cbcPub

/-- The final decryption's contract on x86-64. -/
def cfbDecFinalX : Contract isa where
  pre := FPre finalLen
  post s s' := Spec.Cfb.DecryptFinal (ciphOf s) 8 s.mem s'.mem (s.gpr .rdx) (s.gpr .rcx) (finalLen s)
  pub := cbcPub

theorem cfbEncryptFinal_wp {s₀ : State} (hp : cfbEncFinalX.pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncFinalX.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEncFinal_of_bytes (by decide) (cipher_length s₀) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : cfbDecFinalX.pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecFinalX.post s₀ s' :=
  WP.mono (fbFinal_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDecFinal_of_bytes (by decide) (cipher_length s₀) hd
    exact ⟨hg, h1, hv.trans h2⟩

theorem cfbEncryptFinal_ct : ConstantTime isa cfbEncFinalX.pre cfbEncFinalX.pub cfbEncryptFinal :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) fbTaint (fbTaint_agree finalLen_congr) (by taint_decide)

theorem cfbDecryptFinal_ct : ConstantTime isa cfbDecFinalX.pre cfbDecFinalX.pub cfbDecryptFinal :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) fbTaint (fbTaint_agree finalLen_congr) (by taint_decide)

/-! ## The contracts -/

/-- The final functions' contract with the working space as a sixth argument,
under the calling convention with the table. -/
abbrev finalK (post : Spec.Cast5.cfbFinalSig.Post X86_64.abi.ptrBits) : Contract isa :=
  Proof.Cast5.modeScratchContract (X86_64.abi.withConsts ecbConsts) Spec.Cast5.cfbFinalSig 29
    (Spec.Cast5.cfbFinalPre X86_64.abi.ptrBits) post

/-- A state satisfying the precondition: one byte, 16 rounds. -/
def finalSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .r9 => 0x4000
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩, ⟨0x4000, 232⟩]
  syms _ := 0x100000

theorem final_implies {postX : State → State → Prop} {post : Spec.Cast5.cfbFinalSig.Post X86_64.abi.ptrBits}
    (hpost : ∀ s s', postX s s' → (finalK post).post s s') :
    ({ pre := FPre finalLen, post := postX, pub := cbcPub } : Contract isa).Implies (finalK post) where
  pre s h := by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig,
      Spec.Cast5.cfbFinalPre, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch] at h
    obtain ⟨hdr, hheld, hfit, hdw, -, -, htk, hw, dKV, dKD, dKS, dVD, dVS, dDS, -, spV, spD, spS, fK, -, fD, fS,
      hr⟩ := h
    refine ⟨?_, hw, hheld, hfit, hdw _ (by rw [hw]; exact List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ List.mem_cons_self),
      hdw _ (by rw [hw]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), dKV, dKD, dKS,
      dVD, dVS, dDS, spV, spD, spS, fK, fD, fS, hr⟩
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htk, hdr]
    rfl
  post s s' _ hq := hpost s s' hq
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig, X86_64.abi,
      X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
    obtain ⟨hsp, hsy, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, hsp, hsy⟩
  sat := ⟨finalSat, by
    generalize e : finalSat = s
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig,
      Spec.Cast5.cfbFinalPre, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Abi.constRegions,
      Abi.constsHeld, stackBelow, s1234_length, Curry.withScratch]
    subst s
    refine ⟨rfl, ecbSatMem_held, by decide, ?_, ?_⟩
    · intro r hr
      change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 1⟩, ⟨0x4000, 232⟩] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
    · repeat' apply And.intro
      all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)⟩

theorem cfbEncryptFinal_verified :
    Verified X86_64.target cfbEncryptFinal (finalK (Proof.Cast5.cfbEncFinalPost X86_64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncryptFinal_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncryptFinal) (by lit_decide) he hg, hpost⟩)
    cfbEncryptFinal_ct (final_implies (post := Proof.Cast5.cfbEncFinalPost X86_64.abi.ptrBits) fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig,
        Proof.Cast5.cfbEncFinalPost, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

theorem cfbDecryptFinal_verified :
    Verified X86_64.target cfbDecryptFinal (finalK (Proof.Cast5.cfbDecFinalPost X86_64.abi.ptrBits)) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecryptFinal_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecryptFinal) (by lit_decide) he hg, hpost⟩)
    cfbDecryptFinal_ct (final_implies (post := Proof.Cast5.cfbDecFinalPost X86_64.abi.ptrBits) fun s s' h => by
      sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig,
        Proof.Cast5.cfbDecFinalPost, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h)

/-! ## The functions with their working space on the stack -/

/-- A state satisfying the functions' precondition, with 240 bytes of stack. -/
def finalFrameSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 0x3000 | .r8 => 1 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := ecbSatMem
  rd := [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩]
  syms _ := 0x100000

theorem finalFrame_sat (post : Spec.Cast5.cfbFinalSig.Post X86_64.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cfbFinalSig.contract (X86_64.abi.withConsts ecbConsts) (Spec.Cast5.cfbFinalPre X86_64.abi.ptrBits) post
      true (0 + 240)).pre s := by
  refine ⟨finalFrameSat, ?_⟩
  generalize e : finalFrameSat = s
  sig_pre [Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, X86_64.abi, X86_64.argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
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
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 cfbEncryptFinal)
      (Proof.Cast5.cfbEncryptFinalRoundsContract (X86_64.abi.withConsts ecbConsts) 240) :=
  X86_64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbFinalSig)
    (nm := "scratch") (e := .u64) (n := 29) (pre := Spec.Cast5.cfbFinalPre X86_64.abi.ptrBits)
    (post := Proof.Cast5.cfbEncFinalPost X86_64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 240)
    cfbEncryptFinal_verified (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Cast5.cfbEncFinalPostOut_local _) (finalFrame_sat _)

/-- The final CFB64 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 29 cfbDecryptFinal)
      (Proof.Cast5.cfbDecryptFinalRoundsContract (X86_64.abi.withConsts ecbConsts) 240) :=
  X86_64.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbFinalSig)
    (nm := "scratch") (e := .u64) (n := 29) (pre := Spec.Cast5.cfbFinalPre X86_64.abi.ptrBits)
    (post := Proof.Cast5.cfbDecFinalPost X86_64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 240)
    cfbDecryptFinal_verified (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Cast5.cfbDecFinalPostOut_local _) (finalFrame_sat _)

end VG.Proof.Cast5.X86_64
