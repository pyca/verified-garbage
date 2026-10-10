import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Contract
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.Secp256k1.Verified
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.LitShare

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

namespace VG.Proof.Ecdsa.Verify.X86_64.Secp256k1

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.Secp256k1

theorem pre_of {s : State} (h : verifyX86_64.pre s) : VPre secp256k1 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h7, by simp [TblsHeld, Cfg.combConsts, secp256k1, Abi.constsHeld, Abi.constRegions]⟩

theorem verify_x86 (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : verifyX86_64.pre s) :
    ∃ t s', Exec isa verifySecp256k1 s t s' ∧ abiPreserved s s' ∧ verifyX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := verify_ok (secp256k1_ok hI) hL secp256k1_tbls (pre_of hs)
  have hsp : ∀ i ∈ instrs verifySecp256k1, Taint.clobbers i .rsp = false := by
    have h : verifySecp256k1.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (by lit_decide)).2.2
  obtain ⟨-, hwr, -, -, -, hrs, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, hpost⟩
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

/-- `verifySecp256k1` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def verifySecp256k1Erased : Prog isa := Code.erase verifySecp256k1

materialize_shared verifySecp256k1Erased

theorem verify_ct : ConstantTime isa verifyX86_64.pre verifyX86_64.pub verifySecp256k1 := by
  refine VG.Taint.constantTime_mapBlocks (c' := verifySecp256k1Erased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) rfl ?_ rfl (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem verify_verified (hL : Weierstrass.Law Spec.Secp256k1.curve) (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target verifySecp256k1 (Spec.Ecdsa.Secp256k1.inst.verifyContract X86_64.abi) :=
  Verified.of_correct (verify_x86 hL hI) verify_ct implies

end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
