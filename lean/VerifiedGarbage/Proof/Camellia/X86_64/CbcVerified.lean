module

public import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified
meta import VerifiedGarbage.Proof.Camellia.X86_64.FbVerified
public import VerifiedGarbage.Proof.Camellia.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Camellia.X86_64.ModeCore
public import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
public import VerifiedGarbage.Proof.Modes.X86_64.CbcEncChained
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcEncChained
public import VerifiedGarbage.Proof.Camellia.CbcScratch
meta import VerifiedGarbage.Proof.Camellia.CbcScratch
public import VerifiedGarbage.Impl.Camellia.X86_64.Cbc
meta import VerifiedGarbage.Impl.Camellia.X86_64.Cbc
public import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintMono
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Camellia.X86_64.Lit
meta import VerifiedGarbage.Proof.Camellia.X86_64.Lit
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.AesSiv.Ctr32
public import VerifiedGarbage.Proof.AesSiv.Words
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Modes.X86_64.Ctr
public import VerifiedGarbage.Proof.Modes.X86_64.Xor
meta import VerifiedGarbage.Proof.AesSiv.Ctr32
meta import VerifiedGarbage.Proof.AesSiv.Words
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Modes.X86_64.Ctr
meta import VerifiedGarbage.Proof.Modes.X86_64.Xor

/-!
# Camellia-CBC on x86-64 meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value over Camellia's core for each direction
(`Proof.Modes.X86_64.cbcEncryptChained_wp` and `cbcDecryptChained_wp` with
`dirCoreSpec`); encryption keeps the IV's address in `xmm15`, which the
core's scalar code leaves alone. The IV is read and written, as for OFB and
CFB, whose precondition, public arguments and initial taint these share
(`fbPre`, `fbPub`, `fbTaint`). `cbcEncryptChained_verified`,
`cbcDecryptChained_verified`: each is correct and constant time, by the
taint analysis: the pointers, `rounds`, `n` and the stack pointer are
public, and so is everything the code computes from them; the IV is secret.
`cbcEncryptChained_framed` and `cbcDecryptChained_framed` run them with
their working space on the stack, zeroed on return: 3280 bytes, the 409
words of the scratch buffer and 8 more, below the 8 bytes the call of
`vg_camellia_crypt_prepared` uses.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.Impl.Camellia.X86_64

/-- Camellia's inverse under the subkeys of `s`'s arguments. -/
abbrev invCiphOf (s : State) : Spec.Cbc.Cipher :=
  Spec.Camellia.invCipher (Spec.Camellia.subkeysAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)

/-- CBC decryption on x86-64 that updates the chaining value. -/
def cbcDecX86_64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Cbc.decrypt (invCiphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- CBC encryption on x86-64 that updates the chaining value. -/
def cbcEncX86_64 : Contract isa where
  pre := fbPre
  post s s' := blocksOf s s'.mem = Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 =
      Spec.Cbc.next (ivOf s) (Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

attribute [local irreducible] Spec.Camellia.invCipher in
/-- The core's cipher is the contract's, without unfolding it (as `cipher_eq`). -/
theorem invCipher_eq (m : Mem) (p : Addr) (R : Nat) :
    ((dirCoreSpec .decrypt).toBlock rfl).cipher (R, schedWords m p R) =
      Spec.Camellia.invCipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecX86_64.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => gprPreserved s₀ s' ∧ cbcDecX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, dTV, dTD, dTS, hst, fitK, fitV, fitD, fitB, hR⟩ :=
    hp
  have hwS : (⟨s₀.gpr .r9, 8 * 409⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcDecryptChained_wp ((dirCoreSpec .decrypt).toBlock rfl)
    (r := ⟨.rdx, .rcx, .r8, .r9⟩) ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r9) (P := s₀.gpr .rdx) (D := s₀.gpr .rcx) (n := (s₀.gpr .r8).toNat)
    (k := ((s₀.gpr .rsi).toNat, schedWords s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dKS
        · exact dKV, hst, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dTS
        · exact dTV⟩
    (hstk := .inr ⟨hst, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dTV
      · exact dTD
      · exact dTS⟩))
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, by rw [invCipher_eq] at hdata; exact ⟨hdata, hiv⟩⟩
  rw [stkList_dirCore] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV
  · exact VG.Offset.base_disjoint_below _ (by decide)

theorem cbcEncryptChained_wp {s₀ : State} (hp : cbcEncX86_64.pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => gprPreserved s₀ s' ∧ cbcEncX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, dTV, dTD, dTS, hst, fitK, fitV, fitD, fitB, hR⟩ :=
    hp
  have hwS : (⟨s₀.gpr .r9, 8 * 409⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcEncryptChained_wp ((dirCoreSpec .encrypt).toBlock rfl)
    (r := ⟨.rdx, .rcx, .r8, .r9⟩) ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r9) (P := s₀.gpr .rdx) (D := s₀.gpr .rcx) (n := (s₀.gpr .r8).toNat)
    (k := ((s₀.gpr .rsi).toNat, schedWords s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat))
    rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, by apply BitVec.eq_of_toNat_eq; simp, hR, rfl, by rw [hrd]; simp, fitK,
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dKS
        · exact dKD, hst, fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dTS
        · exact dTD⟩
    ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩
    (hstk := .inr ⟨hst, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dTV
      · exact dTD
      · exact dTS⟩))
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, by rw [encCipher_eq] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [stkList_dirCore] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV
  · exact VG.Offset.base_disjoint_below _ (by decide)

/-! ## Constant time -/

theorem cbcEncryptChained_ct : ConstantTime isa cbcEncX86_64.pre cbcEncX86_64.pub cbcEncryptChained :=
  VG.Taint.constantTime (A := taint) fbTaint fbTaint_agree (by taint_decide)

theorem cbcDecryptChained_ct : ConstantTime isa cbcDecX86_64.pre cbcDecX86_64.pub cbcDecryptChained :=
  VG.Taint.constantTime (A := taint) fbTaint fbTaint_agree (by taint_decide)

/-! ## The contracts -/

theorem cbcEncryptChained_verified :
    Verified X86_64.target cbcEncryptChained (Proof.Camellia.cbcEncChainedScratchContract X86_64.abi 409 8) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cbcEncryptChained_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cbcEncryptChained) (by lit_decide) he hg, hpost⟩)
    cbcEncryptChained_ct (by
    sig_implies [Proof.Camellia.cbcEncChainedScratchContract, Proof.Camellia.cbcChainedScratchSig,
      Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, Proof.Camellia.cbcEncChainedPost, cbcEncX86_64,
      fbPre, fbPub, X86_64.abi, X86_64.argRegs, slots, tailSlot, endSlot, keySlot] [fbSat] using fbSat)

theorem cbcDecryptChained_verified :
    Verified X86_64.target cbcDecryptChained (Proof.Camellia.cbcDecChainedScratchContract X86_64.abi 409 8) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cbcDecryptChained_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cbcDecryptChained) (by lit_decide) he hg, hpost⟩)
    cbcDecryptChained_ct (by
    sig_implies [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig,
      Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, Proof.Camellia.cbcDecChainedPost, cbcDecX86_64,
      fbPre, fbPub, X86_64.abi, X86_64.argRegs, slots, tailSlot, endSlot, keySlot] [fbSat] using fbSat)

theorem cbcEncFrameSat_pre : ∃ s, (Spec.Camellia.cbcEncryptChainedContract X86_64.abi 3288).pre s := by
  implies_sat [Spec.Camellia.cbcEncryptChainedContract, Spec.Camellia.cbcChainedSig, X86_64.abi, X86_64.argRegs]
    [fbFrameSat] using fbFrameSat

theorem cbcDecFrameSat_pre : ∃ s, (Spec.Camellia.cbcDecryptChainedContract X86_64.abi 3288).pre s := by
  implies_sat [Spec.Camellia.cbcDecryptChainedContract, Spec.Camellia.cbcChainedSig, X86_64.abi, X86_64.argRegs]
    [fbFrameSat] using fbFrameSat

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 cbcEncryptChained)
      (Spec.Camellia.cbcEncryptChainedContract X86_64.abi 3288) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 409) (pre := Proof.Camellia.cbcChainedPre X86_64.abi.ptrBits)
    (post := Proof.Camellia.cbcEncChainedPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3280) (by rw [← Proof.Camellia.cbcEncChainedScratchContract_eq]; exact cbcEncryptChained_verified)
    (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Camellia.cbcEncChainedPostOut_local _) cbcEncFrameSat_pre

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 cbcDecryptChained)
      (Spec.Camellia.cbcDecryptChainedContract X86_64.abi 3288) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Camellia.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 409) (pre := Proof.Camellia.cbcChainedPre X86_64.abi.ptrBits)
    (post := Proof.Camellia.cbcDecChainedPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 3280) (by rw [← Proof.Camellia.cbcDecChainedScratchContract_eq]; exact cbcDecryptChained_verified)
    (by decide) (by decide) (by decide) (Code.all_of_allInstrs (by lit_decide))
    (by lit_decide) (by decide) (Proof.Camellia.cbcDecChainedPostOut_local _) cbcDecFrameSat_pre

end VG.Proof.Camellia.X86_64
