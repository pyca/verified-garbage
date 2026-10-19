module

public import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
meta import VerifiedGarbage.Proof.TripleDes.X86_64.FbVerified
import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcDecChained
import VerifiedGarbage.Proof.Modes.X86_64.CbcEncChained
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcEncChained
public import VerifiedGarbage.Proof.TripleDes.CbcScratch
meta import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.X86_64.CbcLit
meta import VerifiedGarbage.Proof.TripleDes.X86_64.CbcLit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.TripleDes.X86_64.ModeCore
meta import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.TripleDes.X86_64.CallPatch
meta import VerifiedGarbage.Proof.TripleDes.X86_64.CallPatch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Modes.CbcNext
import VerifiedGarbage.Proof.Modes.X86_64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
import VerifiedGarbage.Proof.Modes.X86_64.Cfb8
import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Loop
import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Steps
import VerifiedGarbage.Proof.Modes.X86_64.Copy
import VerifiedGarbage.Proof.Modes.X86_64.Counter
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Modes.X86_64.Unchain
import VerifiedGarbage.Proof.Modes.X86_64.Words
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.X86_64.Box
import VerifiedGarbage.Proof.TripleDes.X86_64.Pre
import VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody
import VerifiedGarbage.Spec.Ctr.Contract
import VerifiedGarbage.Spec.TripleDes.Contract
meta import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.Modes.Addr
meta import VerifiedGarbage.Proof.Modes.CbcNext
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcEncLoop
meta import VerifiedGarbage.Proof.Modes.X86_64.CbcGroup
meta import VerifiedGarbage.Proof.Modes.X86_64.Cfb8
meta import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Loop
meta import VerifiedGarbage.Proof.Modes.X86_64.Cfb8Steps
meta import VerifiedGarbage.Proof.Modes.X86_64.Copy
meta import VerifiedGarbage.Proof.Modes.X86_64.Counter
meta import VerifiedGarbage.Proof.Modes.X86_64.Steps
meta import VerifiedGarbage.Proof.Modes.X86_64.Unchain
meta import VerifiedGarbage.Proof.Modes.X86_64.Words
meta import VerifiedGarbage.Proof.Rc2.Word
meta import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish
meta import VerifiedGarbage.Proof.TripleDes.Permutation
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Box
meta import VerifiedGarbage.Proof.TripleDes.X86_64.ModeCore
meta import VerifiedGarbage.Proof.TripleDes.X86_64.Pre
meta import VerifiedGarbage.Proof.TripleDes.X86_64.RoundBody
meta import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Spec.TripleDes.Contract

/-!
# Triple DES-CBC on x86-64 meets its contracts

`cbcEncryptChained_wp`, `cbcDecryptChained_wp`: the modes' CBC that updates
the chaining value over Triple DES's core for each direction
(`Proof.Modes.X86_64.cbcEncryptChained_wp` and `cbcDecryptChained_wp` with
`dirCoreSpec`, the block function inlined), with the feedback modes'
precondition (`fbPre`, as the IV is written too); encryption keeps the IV's
address in `xmm15`, which the scalar code leaves alone, as those modes do.
`cbcEncryptChained_verified`, `cbcDecryptChained_verified`: each is correct
and constant time, by the taint analysis (encryption's with the block
function's summary, `encSum`): the pointers, `n` and the stack pointer are
public, and so is everything the code computes from them; the IV is secret.
The emitted code calls the block function (`Verified.of_inline_ct`).
`cbcEncryptChained_framed` and `cbcDecryptChained_framed` run them with
their working space on the stack, zeroed on return: 976 bytes, the 121
words of the scratch buffer and 8 more.
-/

@[expose] public section

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Impl.TripleDes.X86_64

/-- CBC decryption on x86-64 that updates the chaining value. -/
def cbcDecX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem =
      Spec.Cbc.decrypt (Spec.TripleDes.invCipher (Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi))) (ivOf s)
        (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- CBC encryption on x86-64 that updates the chaining value. -/
def cbcEncX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.TripleDes.bytesAt s'.mem (s.gpr .rsi) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cbc.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

/-- The core's cipher is the contract's. -/
theorem invCipher_eq (k : Spec.TripleDes.Schedule) : (dirCoreSpec .decrypt).cipher k = Spec.TripleDes.invCipher k := rfl

theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecX86_64.pre s₀) :
    WP isa cbcDecryptChainedI s₀ fun s' => gprPreserved s₀ s' ∧ cbcDecX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 121⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcDecryptChained_wp (dirCoreSpec .decrypt) (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, by rw [hrd]; simp, fitK, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKV⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ => ⟨⟨hcs, ?_⟩, ?_⟩
  · rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
    refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dRS
    · exact dRD
    · exact dRV
  · rw [dirCore_bw, Nat.mul_one] at hdata hiv
    rw [invCipher_eq] at hdata
    refine ⟨?_, ?_⟩
    · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cbc.decrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata
    · change _ = Spec.Cbc.next _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq]; exact hiv

theorem cbcDecryptChained_correct (s : State) (hs : cbcDecX86_64.pre s) :
    ∃ t s', Exec isa cbcDecryptChainedI s t s' ∧ abiPreserved s s' ∧ cbcDecX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cbcDecryptChained_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cbcDecryptChainedI) (by lit_decide) he hg, hpost⟩

theorem cbcDecryptChained_ct : ConstantTime isa cbcDecX86_64.pre cbcDecX86_64.pub cbcDecryptChained :=
  VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)

theorem cbcDecChained_implies :
    cbcDecX86_64.Implies (Proof.TripleDes.cbcDecChainedScratchContract X86_64.abi 121) := by
    sig_implies [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
      Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcDecChainedPost, cbcDecX86_64, fbPre, fbPub, X86_64.abi,
      X86_64.argRegs] [fbSat] using fbSat

theorem cbcDecChained_implies8 :
    cbcDecX86_64.Implies (Proof.TripleDes.cbcDecChainedScratchContract X86_64.abi 121 8) :=
  cbcDecChained_implies.stack8_abi (by
    sig_implies_sat [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, X86_64.abi,
      X86_64.argRegs, fbSat] [fbSat] using fbSat)

/-- The data and the IV are apart from the call's return address. -/
theorem cbcDecChained_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.TripleDes.cbcDecChainedScratchContract X86_64.abi 121 8).pre s) (hp : cbcDecX86_64.post s b) :
    cbcDecX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := cbcDecChained_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := 8 * (s.gpr .rcx).toNat)
    (by rw [hwr]; simp) (by simp only [blkLen] at fitD; omega)
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega)
  obtain ⟨h₁, h₂⟩ := hp
  refine ⟨?_, ?_⟩
  · show Spec.TripleDes.cbcBlocksAt _ _ _ = _
    rw [cbcBlocksAt_congr (patch_mem hbD)]; exact h₁
  · rw [bytesAt_congr (patch_mem hbI)]; exact h₂

theorem cbcDecryptChained_inline : cbcDecryptChained.inline = cbcDecryptChainedI := rfl

theorem cbcDecryptChained_verified :
    Verified X86_64.target cbcDecryptChained (Proof.TripleDes.cbcDecChainedScratchContract X86_64.abi 121 8) :=
  Verified.of_inline_ct (by lit_decide)
    (fun s hs => by rw [cbcDecryptChained_inline]; exact cbcDecryptChained_correct s hs) cbcDecryptChained_ct
    cbcDecChained_implies8 (fun _ h => Sig.clear_of_pre h) cbcDecChained_patch

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cbcDecryptChained)
      (Spec.TripleDes.cbcDecryptChainedContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.cbcDecChainedPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) cbcDecryptChained_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.cbcDecChainedPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## Encryption -/

theorem cbcEncryptChained_wp {s₀ : State} (hp : cbcEncX86_64.pre s₀) :
    WP isa cbcEncryptChainedI s₀ fun s' => gprPreserved s₀ s' ∧ cbcEncX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 121⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.cbcEncryptChained_wp (dirCoreSpec .encrypt) (r := fbRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.TripleDes.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
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
  · rw [dirCore_bw, Nat.mul_one] at hdata hiv
    refine ⟨?_, ?_⟩
    · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cbc.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact hdata
    · change _ = Spec.Cbc.next _ (Spec.Cbc.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _))
      rw [cbcBlocksAt_eq]; exact hiv

theorem cbcEncryptChained_correct (s : State) (hs : cbcEncX86_64.pre s) :
    ∃ t s', Exec isa cbcEncryptChainedI s t s' ∧ abiPreserved s s' ∧ cbcEncX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := cbcEncryptChained_wp hs
  exact ⟨t, s', he, abiPreserved_of_exec (c := cbcEncryptChainedI) (by lit_decide) he hg, hpost⟩

theorem cbcEncryptChained_ct : ConstantTime isa cbcEncX86_64.pre cbcEncX86_64.pub cbcEncryptChained := by
  obtain ⟨_, h⟩ : ∃ h, (taintS.check fbTaint cbcEncryptChained h).isSome = true :=
    by taint_decide_sum [encSum]
  exact VG.Taint.constantTime (A := taintS) fbTaint (fbTaint_agree blkLen_congr) h

theorem cbcEncChained_implies :
    cbcEncX86_64.Implies (Proof.TripleDes.cbcEncChainedScratchContract X86_64.abi 121) := by
    sig_implies [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
      Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcEncChainedPost, cbcEncX86_64, fbPre, fbPub, X86_64.abi,
      X86_64.argRegs] [fbSat] using fbSat

theorem cbcEncChained_implies8 :
    cbcEncX86_64.Implies (Proof.TripleDes.cbcEncChainedScratchContract X86_64.abi 121 8) :=
  cbcEncChained_implies.stack8_abi (by
    sig_implies_sat [Proof.TripleDes.cbcEncChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig, X86_64.abi,
      X86_64.argRegs, fbSat] [fbSat] using fbSat)

/-- The data and the IV are apart from the call's return address. -/
theorem cbcEncChained_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Proof.TripleDes.cbcEncChainedScratchContract X86_64.abi 121 8).pre s) (hp : cbcEncX86_64.post s b) :
    cbcEncX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, fitI, fitD, -⟩ := cbcEncChained_implies8.pre s hs
  have hbD := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdx) (n := 8 * (s.gpr .rcx).toNat)
    (by rw [hwr]; simp) (by simp only [blkLen] at fitD; omega)
  have hbI := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rsi) (n := 8) (by rw [hwr]; simp) (by omega)
  obtain ⟨h₁, h₂⟩ := hp
  refine ⟨?_, ?_⟩
  · show Spec.TripleDes.cbcBlocksAt _ _ _ = _
    rw [cbcBlocksAt_congr (patch_mem hbD)]; exact h₁
  · rw [bytesAt_congr (patch_mem hbI)]; exact h₂

theorem cbcEncryptChained_inline : cbcEncryptChained.inline = cbcEncryptChainedI := rfl

theorem cbcEncryptChained_verified :
    Verified X86_64.target cbcEncryptChained (Proof.TripleDes.cbcEncChainedScratchContract X86_64.abi 121 8) :=
  Verified.of_inline_ct (by lit_decide)
    (fun s hs => by rw [cbcEncryptChained_inline]; exact cbcEncryptChained_correct s hs) cbcEncryptChained_ct
    cbcEncChained_implies8 (fun _ h => Sig.clear_of_pre h) cbcEncChained_patch

/-- CBC encryption with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 976 .r8 121 cbcEncryptChained)
      (Spec.TripleDes.cbcEncryptChainedContract X86_64.abi 984) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 121) (post := Proof.TripleDes.cbcEncChainedPost X86_64.abi.ptrBits) (wa := true) (stack := 8)
    (bytes := 976) cbcEncryptChained_verified (by decide) (by decide) (by decide)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by decide)
    (Proof.TripleDes.cbcEncChainedPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.TripleDes.X86_64
