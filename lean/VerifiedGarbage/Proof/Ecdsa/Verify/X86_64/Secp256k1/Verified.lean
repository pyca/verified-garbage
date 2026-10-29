module

import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Front
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.X86_64
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Lit
import VerifiedGarbage.Proof.Weierstrass.WinLay
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Contract
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Front
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.X86_64
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Weierstrass.WinLay
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.EraseChecks
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.EraseChecks

/-!
# ECDSA verification over secp256k1 on x86-64: `Verified`

secp256k1 is a curve the proof supports (`secp256k1_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.Secp256k1.law`), so `verify_ok` gives
the contract's postcondition; the callee-saved registers are restored, `rsp`
is never written, and every store is to `scratch`, which the return address is
apart from (`abiPreserved`). Constant time by taint tracking: the only
branches are on loop counters, and every address is an argument plus a
constant or a counter, so only the pointers affect timing (the contract would
let the key, the hash and the signature affect it too).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.Secp256k1

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.Secp256k1

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre secp256k1 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h7, by simp [TblsHeld, Cfg.combConsts, secp256k1, Abi.constsHeld, Abi.constRegions]⟩

/-- `verifySecp256k1` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`), and its checks of every instruction
(`EraseChecks`). -/
def verifySecp256k1Erased : Prog isa := Code.erase verifySecp256k1

materialize_shared verifySecp256k1Erased

theorem verify_inlineOk : verifySecp256k1.InlineOk = true :=
  Code.inlineOk_of_erase (show verifySecp256k1Erased.InlineOk = true by lit_decide)

theorem verify_x86 (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa verifySecp256k1.inline s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := verify_ok (secp256k1_ok hI) hL secp256k1_tbls (pre_of hs) secp256k1_mulBase.2
  have hok := verify_inlineOk
  have hsp := Code.clobbers_rsp_of_inlineOk hok
  have hmx : verifySecp256k1.inline.allInstrs (fun i => !loadsMxcsr i) = true := by
    rw [Code.allInstrs_inline]
    exact Code.allInstrs_of_erase (fun i => by rw [Instr.loadsMxcsr_erase])
      (show verifySecp256k1Erased.allInstrs _ = true by lit_decide)
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

theorem verify_ct : ConstantTime isa verifyX86_64.pre verifyX86_64.pub verifySecp256k1 := by
  refine VG.Taint.constantTime_mapBlocks (c' := verifySecp256k1Erased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) rfl ?_ rfl (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h0

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 : verifyX86_64.Implies (Spec.Ecdsa.Secp256k1.inst.verifyContract X86_64.abi 8) :=
  implies.stack8_abi (by
    sig_implies_sat [Spec.Ecdsa.Secp256k1.inst, Spec.Ecdsa.Instance.verifyContract,
      Spec.Ecdsa.Instance.verifySig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, X86_64.abi,
      X86_64.argRegs, satState] [satState] using satState)

theorem verify_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target verifySecp256k1 (Spec.Ecdsa.Secp256k1.inst.verifyContract X86_64.abi 8) :=
  Verified.of_inline_ct verify_inlineOk (verify_x86 hL hI) verify_ct implies8
    (fun _ h => Sig.clear_of_pre h) fun _ _ _ _ _ hp => hp

end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
