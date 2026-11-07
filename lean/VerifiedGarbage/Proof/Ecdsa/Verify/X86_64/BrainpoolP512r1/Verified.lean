module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.CombGeneral
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.BrainpoolP512r1.Comb7
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.BrainpoolP512r1.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Front
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.BrainpoolP512r1.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.X86_64
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Weierstrass.WinLay
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.BrainpoolP512r1.Contract
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Front
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.BrainpoolP512r1.X86_64
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP512r1.Lit
meta import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Hash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.EraseChecks
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.EraseChecks

/-!
# ECDSA verification over brainpoolP512r1 on x86-64: `Verified`

brainpoolp512r1S is a curve the proof supports (`brainpoolp512r1S_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.BrainpoolP512r1.law`), with the
signature's comb (`brainpoolp512r1S_comb`, its tables checked by
`Proof.BrainpoolP512r1.combOk7`), so `verifyG_ok` gives the contract's
postcondition; the callee-saved registers are restored, `rsp` is never
written, and every store is to `scratch`, which the return address is apart
from (`abiPreserved`). Constant time by taint tracking: the only branches are
on loop counters, and every address is an argument, or the tables' address,
plus a constant or a counter (the comb's entries are scanned, as the
signature's are), so only the pointers affect timing (the contract would let
the key, the hash and the signature affect it too).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.BrainpoolP512r1

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.BrainpoolP512r1

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre brainpoolp512r1S s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7, held, fit, hdw⟩ := h
  refine ⟨by rw [h1, bp_combConsts, show brainpoolp512r1S.C.len = 64 from rfl]; simp only [Abi.constRegions_cons,
    Abi.constRegions_nil, List.cons_append, List.nil_append], h2, h3, h4, h5, h7, ?_⟩
  rw [TblsHeld, bp_combConsts, Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  refine ⟨fun c hc => ?_, fit, fun r hr => hdw r ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact held
  · rw [h2] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    simp [hr]

/-- `verifyBrainpoolP512r1` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`), and its checks of every instruction
(`EraseChecks`). -/
def verifyBrainpoolP512r1Erased : Prog isa := Code.erase verifyBrainpoolP512r1

materialize_shared verifyBrainpoolP512r1Erased

theorem verify_inlineOk : verifyBrainpoolP512r1.InlineOk = true :=
  Code.inlineOk_of_erase (show verifyBrainpoolP512r1Erased.InlineOk = true by lit_decide)

theorem verify_x86 (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa verifyBrainpoolP512r1.inline s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := verifyG_ok (brainpoolp512r1S_ok hI) hL brainpoolp512r1S_comb
    (Proof.BrainpoolP512r1.combOk7 hL) rfl (pre_of hs)
  have hok := verify_inlineOk
  have hsp := Code.clobbers_rsp_of_inlineOk hok
  have hmx : verifyBrainpoolP512r1.inline.allInstrs (fun i => !loadsMxcsr i) = true := by
    rw [Code.allInstrs_inline]
    exact Code.allInstrs_of_erase (fun i => by rw [Instr.loadsMxcsr_erase])
      (show verifyBrainpoolP512r1Erased.allInstrs _ = true by lit_decide)
  have F := (Exec.regions he (Code.noCalls_inline hok)).2.2
  obtain ⟨-, hwr, -, -, -, hrs, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec hmx he
    ⟨fun r hr => ?_, ?_⟩, hpost⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact Exec.gpr hsp he
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
    · exact hsv _ (by decide)
  · rw [hwr] at F
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      exact hrs) (by decide)

theorem verify_ct : ConstantTime isa verifyX86_64.pre verifyX86_64.pub verifyBrainpoolP512r1 :=
  VG.Taint.constantTime_mapBlocks (c' := verifyBrainpoolP512r1Erased)
    (taintSym_eraseInv ["VG_BRAINPOOLP512R1_COMB"])
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) rfl
    (fun _ _ _ _ ⟨h0, h1, h2, h3, h4, hsy⟩ => ⟨Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h0, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    rfl (by taint_decide)

/-- `satState` satisfies the precondition with 8 bytes of stack. -/
theorem sat_spec8 :
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst
      (X86_64.abi.withConsts brainpoolp512r1S.combConsts) 8).pre satState := by
  have held : ∀ i < bpW.length, satState.mem.readW (satState.syms "VG_BRAINPOOLP512R1_COMB" +
      BitVec.ofNat 64 (8 * i)) 64 = bpW.getD i 0 := satMem_held
  sig_pre [Spec.Ecdsa.BrainpoolP512r1.inst, Proof.Ecdsa.verifyContract, Proof.Ecdsa.verifySig,
    Spec.BrainpoolP512r1.curve, Spec.Ecdsa.scratchWords, X86_64.abi, X86_64.argRegs, bp_combConsts,
    Abi.withConsts, bp_constRegions, Abi.constsHeld, stackBelow]
  sig_and_intros
  all_goals first | exact Region.disjoint_of_sep (by decide) | rfl | exact held | decide

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 : verifyX86_64.Implies
    (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst (X86_64.abi.withConsts brainpoolp512r1S.combConsts) 8) :=
  implies.stack8 ⟨satState, sat_spec8⟩

theorem verify_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target verifyBrainpoolP512r1
      (Proof.Ecdsa.verifyContract Spec.Ecdsa.BrainpoolP512r1.inst (X86_64.abi.withConsts brainpoolp512r1S.combConsts) 8) :=
  Verified.of_inline_ct verify_inlineOk (verify_x86 hL hI) verify_ct implies8
    (fun _ h => Sig.clear_of_pre_consts h) fun _ _ _ _ _ hp => hp

/-- `vg_ecdsa_brainpoolp512r1_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHash_verified (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target
      (Impl.Ecdsa.X86_64.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP512r1.inst.curve.len false verifyBrainpoolP512r1)
      (Spec.Ecdsa.BrainpoolP512r1.inst.verifyHashContract (X86_64.abi.withConsts brainpoolp512r1S.combConsts) 96) :=
  Proof.Ecdsa.Verify.X86_64.Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.brainpoolP512r1_len (by decide)
    (verify_verified hL hI) (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by taint_decide)
    (Proof.Ecdsa.Verify.X86_64.Hash.hashSat_cons (by decide) sat_spec8 (by decide) fun r hr => by
      simp only [satState, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

end VG.Proof.Ecdsa.Verify.X86_64.BrainpoolP512r1
