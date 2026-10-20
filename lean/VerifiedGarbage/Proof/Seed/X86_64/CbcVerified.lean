module

public import VerifiedGarbage.Proof.Seed.X86_64.FbVerified
import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
import VerifiedGarbage.Proof.Modes.X86_64.CbcEncChained
import VerifiedGarbage.Proof.Modes.X86_64.KeepIv
public import VerifiedGarbage.Proof.Seed.CbcScratch
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Seed.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Seed.X86_64.FbVerified
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcEncChained
meta import VerifiedGarbage.Proof.Modes.X86_64.KeepIv
meta import VerifiedGarbage.Proof.Seed.CbcScratch
meta import VerifiedGarbage.Proof.Seed.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Seed.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# SEED-CBC on x86-64 meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value over SEED's core for each direction
(`Proof.Modes.X86_64.cbcEncryptChained_wp` and `cbcDecryptChained_wp` with
`dirCoreSpec`), with the feedback modes' precondition (`fbPre`, as the IV
is written too); encryption keeps the IV's address in `xmm15`, as those
modes do. `cbcEncryptChained_verified`, `cbcDecryptChained_verified`: each
is correct and constant time, by the taint analysis: the pointers, `n` and
the stack pointer are public, and so is everything the code computes from
them; the IV is secret. Encryption's analysis reads the feedback modes'
summary of the loop of rounds (`fbRoundSum`). `cbcEncryptChained_framed`
and `cbcDecryptChained_framed` run them with their working space on the
stack, zeroed on return: 1512 bytes, the 188 words of the scratch buffer
and 8 more.
-/

@[expose] public section

namespace VG.Proof.Seed.X86_64

open VG VG.X86_64 VG.Impl.Seed.X86_64

/-- CBC decryption on x86-64 that updates the chaining value. -/
def cbcDecX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem =
      Spec.Cbc.decrypt (Spec.Seed.invCipher (Spec.Seed.scheduleAt s.mem (s.gpr .rdi))) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 16 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- CBC encryption on x86-64 that updates the chaining value. -/
def cbcEncX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 16 =
      Spec.Cbc.next (ivOf s) (Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

attribute [local irreducible] Spec.Seed.invCipher in
/-- The core's cipher is the contract's (stated once: unifying them unfolds the cipher's spec). -/
theorem decCipher_eq : (dirCoreSpec .decrypt).cipher = Spec.Seed.invCipher := rfl

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecX86_64.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => gprPreserved s₀ s' ∧ cbcDecX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 188⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcDecryptChained_wp (dirCoreSpec .decrypt) (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Seed.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [dirCore_bw, hwr]; exact List.mem_cons_self)
    (by rw [dirCore_bw, show 8 * 2 = 16 from rfl, hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKV⟩) fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, ?_⟩
  · rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
    refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dRS
    · exact dRD
    · exact dRV
  · rw [dirCore_bw, show 8 * 2 = 16 from rfl] at hdata hiv
    rw [decCipher_eq] at hdata
    exact ⟨hdata, hiv⟩

theorem cbcDecryptChained_ct : ConstantTime isa cbcDecX86_64.pre cbcDecX86_64.pub cbcDecryptChained :=
  VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)

theorem cbcDecryptChained_verified :
    Verified X86_64.target cbcDecryptChained (Proof.Seed.cbcDecChainedScratchContract X86_64.abi 188) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cbcDecryptChained_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cbcDecryptChained) (by lit_decide) he hg, hpost⟩)
    cbcDecryptChained_ct (by
    sig_implies [Proof.Seed.cbcDecChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig,
      Proof.Seed.cbcDecChainedPost, cbcDecX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 1512 .r8 188 cbcDecryptChained)
      (Spec.Seed.cbcDecryptChainedContract X86_64.abi 1512) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Seed.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 188) (post := Proof.Seed.cbcDecChainedPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1512) cbcDecryptChained_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Seed.cbcDecChainedPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## Encryption -/

theorem cbcEncryptChained_wp {s₀ : State} (hp : cbcEncX86_64.pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => gprPreserved s₀ s' ∧ cbcEncX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 188⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcEncryptChained_wp (dirCoreSpec .encrypt) (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Seed.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [dirCore_bw, hwr]; exact List.mem_cons_self)
    (by rw [dirCore_bw, show 8 * 2 = 16 from rfl, hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKD⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide),
      Modes.X86_64.keepsIv_of_ivSafe (by lit_decide)⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, ?_⟩
  · rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
    refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dRS
    · exact dRD
    · exact dRV
  · rw [dirCore_bw, show 8 * 2 = 16 from rfl, encCipher_eq] at hdata hiv
    exact ⟨hdata, hiv⟩

theorem cbcEncryptChained_ct : ConstantTime isa cbcEncX86_64.pre cbcEncX86_64.pub cbcEncryptChained :=
  let ⟨_, h⟩ := (by taint_decide_sum [fbRoundSum] : ∃ h, (taintS.check fbTaint cbcEncryptChained h).isSome = true)
  VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree blkLen_congr) h

theorem cbcEncryptChained_verified :
    Verified X86_64.target cbcEncryptChained (Proof.Seed.cbcEncChainedScratchContract X86_64.abi 188) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cbcEncryptChained_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cbcEncryptChained) (by lit_decide) he hg, hpost⟩)
    cbcEncryptChained_ct (by
    sig_implies [Proof.Seed.cbcEncChainedScratchContract, Proof.Seed.cbcChainedScratchSig, Spec.Seed.cbcChainedSig,
      Proof.Seed.cbcEncChainedPost, cbcEncX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 1512 .r8 188 cbcEncryptChained)
      (Spec.Seed.cbcEncryptChainedContract X86_64.abi 1512) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Seed.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 188) (post := Proof.Seed.cbcEncChainedPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1512) cbcEncryptChained_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Seed.cbcEncChainedPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Seed.X86_64
