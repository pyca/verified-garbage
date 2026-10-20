module

public import VerifiedGarbage.Proof.EcKey.X86_64.Main
public import VerifiedGarbage.Proof.EcKey.X86_64.BrainpoolP256r1.Contract
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.EcKey.X86_64.BrainpoolP256r1.Lit
public import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.X86_64
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Lit
meta import VerifiedGarbage.Proof.EcKey.X86_64.Main
meta import VerifiedGarbage.Proof.EcKey.X86_64.BrainpoolP256r1.Contract
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Verified
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
meta import VerifiedGarbage.Proof.Weierstrass.X86_64.CodeErase
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.EcKey.X86_64.BrainpoolP256r1.Lit
meta import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.X86_64
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.BrainpoolP256r1.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# brainpoolP256r1 public keys on x86-64: `Verified`

brainpoolp256r1 is a curve the proof supports (`brainpoolp256r1_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.BrainpoolP256r1.law`), so `publicKey_ok`
gives the contract's postcondition; the callee-saved registers are restored,
`rsp` is never written, and every store is to `out` or `scratch`, which the
return address is apart from (`abiPreserved`). Constant time by taint
tracking: the only branches are on loop counters, and every address is an
argument plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86_64.BrainpoolP256r1

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.EcKey.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.BrainpoolP256r1

theorem pre_of {s : State} (h : pkX86_64.pre s) : PkPre brainpoolp256r1 s := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h8, h9, by simp [TblsHeld, Cfg.combConsts, brainpoolp256r1, Abi.constsHeld, Abi.constRegions]⟩

theorem post_of {s s' : State} (h : PkPost brainpoolp256r1 s s') : pkX86_64.post s s' := by
  unfold PkPost at h
  show match pk s.mem (s.gpr .rsi) with
    | some (.affine x y) => (s'.gpr .rax).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 65 = Spec.EcKey.encodePoint (.affine x y)
    | _ => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 65 = List.replicate 65 0
  revert h
  generalize hq : pk s.mem (s.gpr .rsi) = q
  rw [show Spec.EcKey.publicKey brainpoolp256r1.C (dk brainpoolp256r1 s) = pk s.mem (s.gpr .rsi) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

/-- `publicKeyBrainpoolP256r1` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def publicKeyBrainpoolP256r1Erased : Prog isa := Code.erase publicKeyBrainpoolP256r1

materialize_shared publicKeyBrainpoolP256r1Erased

theorem pk_inlineOk : publicKeyBrainpoolP256r1.InlineOk = true := by
  rw [← Code.InlineOk_erase]
  show publicKeyBrainpoolP256r1Erased.InlineOk = true
  lit_decide

theorem pk_x86 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : pkX86_64.pre s) :
    ∃ t s', Exec isa publicKeyBrainpoolP256r1.inline s t s' ∧ abiPreserved s s' ∧ pkX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := publicKey_ok (brainpoolp256r1_ok hI) hL brainpoolp256r1_tbls (pre_of hs) brainpoolp256r1_mulBase
  have hsp := Code.clobbers_rsp_of_inlineOk pk_inlineOk
  have F := (Exec.regions he (Code.noCalls_inline pk_inlineOk)).2.2
  obtain ⟨-, hwr, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by
    rw [Code.allInstrs_inline, ← Code.allInstrs_mapBlocks (f := Instr.erase) fun i => by rw [loadsMxcsr_erase]]
    show publicKeyBrainpoolP256r1Erased.allInstrs _ = true
    lit_decide) he
    ⟨fun r hr => ?_, ?_⟩, post_of hpost⟩
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
      rintro r (rfl | rfl)
      · exact hro
      · exact hrs) (by decide)


theorem pk_ct : ConstantTime isa pkX86_64.pre pkX86_64.pub publicKeyBrainpoolP256r1 := by
  refine VG.Taint.constantTime_mapBlocks (c' := publicKeyBrainpoolP256r1Erased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) rfl ?_ rfl (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h0

/-- The contract with 8 bytes of stack, for the calls' return address. -/
theorem implies8 : pkX86_64.Implies (Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract X86_64.abi 8) :=
  implies.stack8_abi (by
    sig_implies_sat [Spec.EcKey.BrainpoolP256r1.inst, Spec.EcKey.Instance.publicKeyContract,
      Spec.EcKey.Instance.publicKeySig, Spec.BrainpoolP256r1.curve, Spec.EcKey.scratchWords, X86_64.abi,
      X86_64.argRegs, satState] [satState] using satState)

/-- The output is apart from the calls' return address. -/
theorem pk_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract X86_64.abi 8).pre s)
    (hp : pkX86_64.post s b) : pkX86_64.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -⟩ := implies8.pre s hs
  have hb := Clear.wr_bytes (Sig.clear_of_pre hs) (p := s.gpr .rdi) (n := 65)
    (by rw [hwr]; simp) (by decide)
  simpa only [pkX86_64, State.patch_gpr, EcKey.bytesAt_patch hb] using hp

theorem pk_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target publicKeyBrainpoolP256r1 (Spec.EcKey.BrainpoolP256r1.inst.publicKeyContract X86_64.abi 8) :=
  Verified.of_inline_ct pk_inlineOk (pk_x86 hL hI) pk_ct implies8
    (fun _ h => Sig.clear_of_pre h) pk_patch

end VG.Proof.EcKey.X86_64.BrainpoolP256r1
