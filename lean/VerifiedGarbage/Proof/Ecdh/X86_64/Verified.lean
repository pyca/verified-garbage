import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Ecdh.X86_64.Contract
import VerifiedGarbage.Proof.Ecdh.X86_64.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdh.X86_64.WinJac
import VerifiedGarbage.Proof.P256.X86_64.WinJac
import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Framework.LitShare

/-!
# ECDH over P-256 on x86-64: `Verified`

P-256 is a curve the proof supports (`p256_ok`, and `Law` for its group law
and `InvSounds` for its inversions, which the registration file supplies:
`Proof.P256.law` and the variant's `inv`), so `exchangeWith_ok`, given the
`MulOk` of its scalar multiplication (`ecdh_x86_of`), gives the contract's
postcondition: `exchangeP256` multiplies by the Jacobian window method
(`mulQJ_ok`), which needs P-256's prime order, with the doubling by halving
(`mulQJP256_ok`); the callee-saved registers are restored,
`rsp` is never written, and every store is to `out` or `scratch`, which the
return address is apart from (`abiPreserved`). Constant time by taint
tracking: the only branches are on loop counters, and every address is an
argument plus a constant or a counter, so not even the peer's key (which the
contract would let leak) affects timing.
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG.Proof.Ecdsa.X86_64

theorem pre_of {s : State} (h : ecdhX86_64.pre s) : EPre p256 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, -, -, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h10, h11⟩

theorem post_of {s s' : State} (h : EPost p256 s s') : ecdhX86_64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .rsi) (s.gpr .rdx) with
    | some z => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 32 = z
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .rdi) 32 = List.replicate 32 0
  revert h
  generalize hq : ex s.mem (s.gpr .rsi) (s.gpr .rdx) = q
  rw [show Spec.Ecdh.exchange p256.C (dk p256 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .rdx) (1 + 2 * p256.C.len)) = ex s.mem (s.gpr .rsi) (s.gpr .rdx) from rfl, hq]
  rcases q with _ | z <;> exact id

/-- The exchange `code` of a curve `c` (P-256, with either multiplication)
that the proof supports, with a scalar multiplication `mq` that computes
`[d]P` (`MulOk`, writing only `W`: `MulW`), whose precondition the
contract's gives (`hpre`), never writing `rsp`, calling or loading MXCSR
(which its literal decides). -/
theorem ecdh_x86_of {c : Cfg} {mq code : Prog isa} {W : List (Nat × Nat)} (hc : CfgOk c)
    (hL : Weierstrass.Law c.C) (hmq : MulOk c mq W) (hW : MulW c W)
    (hpre : ∀ s, ecdhX86_64.pre s → EPre c s) (hpost : ∀ s s', EPost c s s' → ecdhX86_64.post s s')
    (hcode : Impl.Ecdh.X86_64.Cfg.exchangeWith c mq = code)
    (hsp : code.allInstrs (fun i => !Taint.clobbers i .rsp) = true)
    (hnc : code.noCalls = true) (hmx : code.allInstrs (fun i => !loadsMxcsr i) = true) (s : State)
    (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' := by
  subst hcode
  obtain ⟨t, s', he, hsv, hpost'⟩ := wp_of_inline hnc <| exchangeWith_ok hc hL hmq hW (hpre s hs)
  have hsp : ∀ i ∈ instrs (Impl.Ecdh.X86_64.Cfg.exchangeWith c mq), Taint.clobbers i .rsp = false := by
    rw [Code.allInstrs_eq, List.all_eq_true] at hsp
    intro i hi
    simpa using hsp i hi
  have F := (Exec.regions he hnc).2.2
  obtain ⟨-, hwr, -, -, -, -, -, hro, hrs, -, -⟩ := hs
  refine ⟨t, s', he, abiPreserved_of_exec hmx he ⟨fun r hr => ?_, ?_⟩, hpost _ _ hpost'⟩
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

/-- The Jacobian window method with the doubling by halving computes `[d]P`
on P-256, which has prime order. -/
theorem mulQJP256_ok (hI : Weierstrass.X86_64.InvSounds) (hL : Weierstrass.Law Spec.P256.curve)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve) :
    MulOk p256 (Impl.Ecdh.X86_64.Cfg.mulQJ p256 (Impl.P256.X86_64.doubleHalfPublic p256.MP' p256.rcbSlots))
      (mulQJW p256) :=
  mulQJ_ok (p256_ok hI) (Or.inl rfl) hL hO (Proof.P256.X86_64.doubleHalfPublic_dblOk rfl
    (Weierstrass.unitMod_pow_two (p256_ok hI).p_odd _) hL (p256_ok hI).am3) (Nat.le_of_eq Proof.P256.X86_64.n_mod32.symm)
    Proof.P256.X86_64.n_ge64

theorem ecdh_x86 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve) (s : State) (hs : ecdhX86_64.pre s) :
    ∃ t s', Exec isa exchangeP256 s t s' ∧ abiPreserved s s' ∧ ecdhX86_64.post s s' :=
  ecdh_x86_of (p256_ok hI) hL (mulQJP256_ok hI hL hO) (mulQJ_w (p256_ok hI))
    (fun _ => pre_of) (fun _ _ => post_of) rfl (by lit_decide) (by lit_decide) (by lit_decide) s hs

/-- `exchangeP256` without its displacements, as a literal of shared blocks
(`materialize_shared`): what its constant-time check analyses
(`Proof/Framework/X86_64/TaintErase.lean`). -/
def exchangeP256Erased : Prog isa := Code.erase exchangeP256

materialize_shared exchangeP256Erased

theorem ecdh_ct : ConstantTime isa ecdhX86_64.pre ecdhX86_64.pub exchangeP256 := by
  refine VG.Taint.constantTime_mapBlocks (c' := exchangeP256Erased) taintS_eraseInv
    (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) rfl ?_ rfl (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem ecdh_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve) :
    Verified X86_64.target exchangeP256 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst X86_64.abi) :=
  Verified.of_correct (ecdh_x86 hL hI hO) ecdh_ct implies

end VG.Proof.Ecdh.X86_64
