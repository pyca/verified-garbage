import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Contract
import VerifiedGarbage.Proof.Ecdh.X86_64.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
import VerifiedGarbage.Proof.P384.X86_64.TaintSums
import VerifiedGarbage.Proof.Ecdh.X86_64.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleIn

/-!
# ECDH over P-384 on x86-64: `Verified`

P-384 is a curve the proof supports (`p384_ok`, and `Law` for its group law
and `InvSounds` for its inversions, which the registration file supplies:
`Proof.P384.law` and the variant's `inv`), so `exchangeWith_ok`, given the
`MulOk` of its scalar multiplication, gives the contract's postcondition:
`exchangeP384` multiplies by the Jacobian window method (`mulQJ_ok`), which
needs P-384's prime order and `n mod 32 ≥ 17` (`n_mod32`), with the doubling
in place (`doubleIn_dblOk`, `mulQJP384_ok`); the callee-saved registers are restored,
`rsp` is never written, and every store is to `out` or `scratch`, which the
return address is apart from (`abiPreserved`). Constant time by taint
tracking: the only branches are on loop counters, and every address is an
argument plus a constant or a counter, so not even the peer's key (which the
contract would let leak) affects timing.
-/

namespace VG.Proof.Ecdh.X86_64.P384

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdsa.X86_64.P384

theorem pre_of {s : State} (h : ecdhX86_64.pre s) : EPre p384 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, -, -, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h10, h11⟩

theorem post_of {s s' : State} (h : EPost p384 s s') : ecdhX86_64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .rsi) (s.gpr .rdx) with
    | some z => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 48 = z
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 48 = List.replicate 48 0
  revert h
  generalize hq : ex s.mem (s.gpr .rsi) (s.gpr .rdx) = q
  rw [show Spec.Ecdh.exchange p384.C (dk p384 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdx) (1 + 2 * p384.C.len)) = ex s.mem (s.gpr .rsi) (s.gpr .rdx) from rfl, hq]
  rcases q with _ | z <;> exact id

/-- P-384's order is at least `17` modulo `32` (it is `19`). -/
theorem n_mod32 : 17 ≤ Spec.P384.curve.n % 32 := by decide

theorem n_ge64 : 64 ≤ Spec.P384.curve.n := by decide

/-- The Jacobian window method with the doubling in place computes `[d]P` on
P-384, which has prime order. -/
theorem mulQJP384_ok {c : Cfg} (hc : CfgOk c) (h6 : c.n = 6) (hcC : c.C = Spec.P384.curve)
    (hL : Weierstrass.Law c.C) (hO : Weierstrass.PrimeOrder c.C) :
    MulOk c (Impl.Ecdh.X86_64.Cfg.mulQJ c (Impl.Weierstrass.X86_64.doubleIn c.MP' c.rcbSlots)) (mulQJW c) :=
  mulQJ_ok hc (Or.inr h6) hL hO (Weierstrass.X86_64.doubleIn_dblOk
    (Weierstrass.unitMod_pow_two hc.p_odd _) hL hc.am3) (hcC ▸ n_mod32) (hcC ▸ n_ge64)

theorem ecdh_x86 (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa exchangeP384 s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' := by
  obtain ⟨t, s', he, hsv, hpost⟩ := exchangeWith_ok (p384_ok hI) hL
    (mulQJP384_ok (p384_ok hI) rfl rfl hL hO) (mulQJ_w (p384_ok hI)) (pre_of hs)
  have hsp : ∀ i ∈ instrs exchangeP384, Taint.clobbers i .rsp = false := by
    have h : exchangeP384.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by lit_decide
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

theorem ecdh_ct : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP384 := by
  obtain ⟨_, hc⟩ : ∃ h, (taintS.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) exchangeP384 h).isSome = true := by
    taint_decide_sum [Proof.P384.X86_64.ladderGSum, Proof.P384.X86_64.powPSum]
  refine VG.Taint.constantTime (A := taintS) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ hc
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem ecdh_verified (hL : Weierstrass.Law Spec.P384.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve) :
    Verified X86_64.target exchangeP384 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst X86_64.abi) :=
  Verified.of_correct (ecdh_x86 hL hI hO) ecdh_ct implies

end VG.Proof.Ecdh.X86_64.P384
