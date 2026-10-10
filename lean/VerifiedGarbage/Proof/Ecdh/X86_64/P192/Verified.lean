import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdh.X86_64.P192.Contract
import VerifiedGarbage.Proof.Ecdh.X86_64.P192.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P192.Verified
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.LitShare

/-!
# ECDH over p192 on x86-64: `Verified`

p192 is a curve the proof supports (`p192_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.P192.law`), so `exchange_ok`
gives the contract's postcondition; the callee-saved registers are restored,
`rsp` is never written, and every store is to `out` or `scratch`, which the
return address is apart from (`abiPreserved`). Constant time by taint
tracking: the only branches are on loop counters, and every address is an
argument plus a constant or a counter, so not even the peer's key (which the
contract would let leak) affects timing.
-/

namespace VG.Proof.Ecdh.X86_64.P192

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P192

theorem pre_of {s : State} (h : ecdhX86_64.pre s) : EPre p192 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, -, -, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h10, h11⟩

theorem post_of {s s' : State} (h : EPost p192 s s') : ecdhX86_64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .rsi) (s.gpr .rdx) with
    | some z => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 24 = z
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 24 = List.replicate 24 0
  revert h
  generalize hq : ex s.mem (s.gpr .rsi) (s.gpr .rdx) = q
  rw [show Spec.Ecdh.exchange p192.C (dk p192 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdx) (1 + 2 * p192.C.len)) = ex s.mem (s.gpr .rsi) (s.gpr .rdx) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_x86 (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.X86_64.InvSounds) (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa exchangeP192 s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := exchange_ok (p192_ok hI) hL (pre_of hs)
  have hsp : ∀ i ∈ instrs exchangeP192, Taint.clobbers i .rsp = false := by
    have h : exchangeP192.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
    rw [Code.allInstrs_eq, List.all_eq_true] at h
    intro i hi
    simpa using h i hi
  have F := (Exec.regions he (by lit_decide)).2.2
  obtain ⟨-, hwr, -, -, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ⟨fun r hr => ?_, ?_⟩, post_of hpost⟩
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

/-- `exchangeP192` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def exchangeP192Erased : Prog isa := Code.erase exchangeP192

materialize_shared exchangeP192Erased

theorem ecdh_ct : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP192 := by
  refine VG.Taint.constantTime_mapBlocks (c' := exchangeP192Erased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) rfl ?_ rfl (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem ecdh_verified (hL : Weierstrass.Law Spec.P192.curve) (hI : Weierstrass.X86_64.InvSounds) :
    Verified X86_64.target exchangeP192 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P192.inst X86_64.abi) :=
  Verified.of_correct (ecdh_x86 hL hI) ecdh_ct implies

end VG.Proof.Ecdh.X86_64.P192
