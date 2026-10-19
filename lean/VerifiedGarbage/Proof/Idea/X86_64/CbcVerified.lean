module

public import VerifiedGarbage.Proof.Idea.X86_64.FbVerified
import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
import VerifiedGarbage.Proof.Modes.X86_64.CbcEncChained
public import VerifiedGarbage.Proof.Idea.CbcScratch
import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Idea.X86_64.ModeCore
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Idea.X86_64.FbVerified
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcEncChained
meta import VerifiedGarbage.Proof.Idea.CbcScratch
meta import VerifiedGarbage.Proof.Idea.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Idea.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.TaintSum

/-!
# IDEA-CBC on x86-64 meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value over IDEA's core (`Proof.Modes.X86_64.cbcEncryptChained_wp`
and `cbcDecryptChained_wp` with `modeCoreSpec`; decryption is the same code
under the decryption subkeys), with the feedback modes' precondition
(`fbPre`, as the IV is written too); encryption keeps the IV's address in
`xmm15`, which the core's scalar code leaves alone, as those modes do.
`cbcEncryptChained_verified`, `cbcDecryptChained_verified`: each is correct
and constant time, by the taint analysis: the pointers, `n` and the stack
pointer are public, and so is everything the code computes from them; the
IV is secret. `cbcEncryptChained_framed` and `cbcDecryptChained_framed` run
them with their working space on the stack, zeroed on return: 184 bytes, the
22 words of the scratch buffer and 8 more.
-/

@[expose] public section

namespace VG.Proof.Idea.X86_64

open VG VG.X86_64 VG.Impl.Idea.X86_64

/-- CBC decryption on x86-64 that updates the chaining value. -/
def cbcDecX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem =
      Spec.Cbc.decrypt (Spec.Idea.cipher (Spec.Idea.scheduleAt s.mem (s.gpr .rdi))) (ivOf s)
        (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- CBC encryption on x86-64 that updates the chaining value. -/
def cbcEncX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecX86_64.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => gprPreserved s₀ s' ∧ cbcDecX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 22⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcDecryptChained_wp modeCoreSpec (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
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
  · rw [modeCore_bw, Nat.mul_one] at hdata hiv
    refine ⟨?_, ?_⟩
    · change Spec.Idea.cbcBlocksAt _ _ _ = Spec.Cbc.decrypt _ _ (Spec.Idea.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata
    · change _ = Spec.Cbc.next _ (Spec.Idea.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq]; exact hiv

theorem cbcDecryptChained_verified :
    Verified X86_64.target cbcDecryptChained (Proof.Idea.cbcDecChainedScratchContract X86_64.abi 22) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cbcDecryptChained_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cbcDecryptChained) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Idea.cbcDecChainedScratchContract, Proof.Idea.cbcChainedScratchSig,
      Spec.Idea.cbcChainedSig, Proof.Idea.cbcDecChainedPost, cbcDecX86_64, fbPre, fbPub, X86_64.abi,
      X86_64.argRegs] [fbSat] using fbSat)

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 cbcDecryptChained)
      (Spec.Idea.cbcDecryptChainedContract X86_64.abi 184) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Idea.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 22) (post := Proof.Idea.cbcDecChainedPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 184) cbcDecryptChained_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Idea.cbcDecChainedPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## Encryption -/

theorem cbcEncryptChained_wp {s₀ : State} (hp : cbcEncX86_64.pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => gprPreserved s₀ s' ∧ cbcEncX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 22⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcEncryptChained_wp modeCoreSpec (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Idea.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKD⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), Modes.X86_64.keepsIv_of_scal (by lit_decide)⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, ?_⟩
  · rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
    refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dRS
    · exact dRD
    · exact dRV
  · rw [modeCore_bw, Nat.mul_one] at hdata hiv
    refine ⟨?_, ?_⟩
    · change Spec.Idea.cbcBlocksAt _ _ _ = Spec.Cbc.encrypt _ _ (Spec.Idea.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata
    · change _ = Spec.Cbc.next _ (Spec.Cbc.encrypt _ _ (Spec.Idea.cbcBlocksAt _ _ _))
      rw [cbcBlocksAt_eq]; exact hiv

theorem cbcEncryptChained_verified :
    Verified X86_64.target cbcEncryptChained (Proof.Idea.cbcEncChainedScratchContract X86_64.abi 22) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cbcEncryptChained_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cbcEncryptChained) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Idea.cbcEncChainedScratchContract, Proof.Idea.cbcChainedScratchSig,
      Spec.Idea.cbcChainedSig, Proof.Idea.cbcEncChainedPost, cbcEncX86_64, fbPre, fbPub, X86_64.abi,
      X86_64.argRegs] [fbSat] using fbSat)

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 184 .r8 22 cbcEncryptChained)
      (Spec.Idea.cbcEncryptChainedContract X86_64.abi 184) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Idea.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 22) (post := Proof.Idea.cbcEncChainedPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 184) cbcEncryptChained_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Idea.cbcEncChainedPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Idea.X86_64
