module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Order.Fn
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Verified
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV
public import VerifiedGarbage.Proof.Weierstrass.MontContract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Impl.Weierstrass.RISCV64.P384Order
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Order.Fn
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Verified

/-!
# Arithmetic modulo P-384's order on RISC-V: verified

As the functions modulo `p` (`Proof/Weierstrass/RISCV64/P384Field/Verified.lean`),
whose lemmas this uses: each function meets a contract by register from
`fn_ok`, which the shared contracts of `Proof/Weierstrass/MontContract.lean` imply, and
is constant time by the taint analysis.
-/

-- Checking `N` against the contract's modulus evaluates `2³⁸⁴`.
set_option exponentiation.threshold 512

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P384Order

open VG VG.RISCV64
open VG.Impl.Weierstrass.RISCV64.P384Field (fn)
open VG.Proof.Weierstrass.RISCV64.P384Field (numAt_d6 keeps_of_frame fn_ct read_zero satWs CoreOk fn_ok d6)
open VG.Impl.Weierstrass.RISCV64.P384Order (mulFn addFn subFn)
open VG.Impl.Weierstrass.Mont (numAt Keeps p384n Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV)

theorem n_eq : p384n.m = N := by decide

/-- `fn core` meets a contract by register, from `fn_ok`. -/
theorem fn_rv {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {s : State} (hs : rvPre p384n s) (hp : pre (arg p384n s .a2) (arg p384n s .a3)) :
    ∃ t s', Exec isa (fn core) s t s' ∧ abiPreserved s s' ∧
      res (arg p384n s .a2) (arg p384n s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) 6) ∧
      Keeps 6 (s.gpr .a0) (offArg s .a1) s.mem s'.mem := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes] at fo fa fb
  simp only [arg, show p384n.k = 6 from rfl, numAt_d6] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fn_ok hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame fo f⟩

theorem mul_rv (s : State) (hs : (mulRV p384n).pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ (mulRV p384n).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv (@mulCore_core) hs.1 (by rw [← n_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v1, by rw [n_eq]; exact v2, k⟩

theorem add_rv (s : State) (hs : (addRV p384n).pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ (addRV p384n).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv (@addCore_core) hs.1 (by rw [← n_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v, k⟩

theorem sub_rv (s : State) (hs : (subRV p384n).pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ (subRV p384n).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv (@subCore_core) hs.1 (by rw [← n_eq]; exact hs.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v, k⟩

/-! ## Constant time -/

open VG.Proof.Ed25519.RISCV64 (mulAgreeLo)

theorem mulFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub mulFn :=
  fn_ct hpub (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide))

theorem addFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub addFn :=
  fn_ct hpub (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide))

theorem subFn_ct {Pre : State → Prop} {Pub : State → State → Prop}
    (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → mulAgreeLo s₁ s₂) :
    ConstantTime isa Pre Pub subFn :=
  fn_ct hpub (RelCT.taint (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3]) (fun _ _ h => h) (by taint_decide))

theorem rvPub_agree : ∀ s₁ s₂ : State, rvPre p384n s₁ → rvPre p384n s₂ → rvPub s₁ s₂ → mulAgreeLo s₁ s₂ :=
  fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, h0, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩

/-! ## The shared contracts -/

theorem sat_pre : rvPre p384n satWs ∧ arg p384n satWs .a2 = 0 ∧ arg p384n satWs .a3 = 0 := by
  refine ⟨⟨rfl, rfl, by decide, ⟨?_, ?_, ?_⟩, by decide⟩, read_zero _ _, read_zero _ _⟩ <;>
    simp [Fits, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes, satWs, offArg, p384n]

theorem mul_verified : Verified RISCV64.target mulFn (p384n.mulContract RISCV64.abi) :=
  Verified.of_correct mul_rv (mulFn_ct (Pre := (mulRV p384n).pre) fun s₁ s₂ h₁ h₂ hp => rvPub_agree s₁ s₂ h₁.1 h₂.1 hp)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg, mulRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg,
        mulRV, rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.mulContract, Impl.Weierstrass.Mont.sig, arg, mulRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; decide⟩ }

theorem add_verified : Verified RISCV64.target addFn (p384n.addContract RISCV64.abi) :=
  Verified.of_correct add_rv (addFn_ct (Pre := (addRV p384n).pre) fun s₁ s₂ h₁ h₂ hp => rvPub_agree s₁ s₂ h₁.1 h₂.1 hp)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg, addRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg,
        addRV, rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.addContract, Impl.Weierstrass.Mont.sig, arg, addRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; decide⟩ }

theorem sub_verified : Verified RISCV64.target subFn (p384n.subContract RISCV64.abi) :=
  Verified.of_correct sub_rv (subFn_ct (Pre := (subRV p384n).pre) fun s₁ s₂ h₁ h₂ hp => rvPub_agree s₁ s₂ h₁.1 h₂.1 hp)
    { pre := by sig_implies_pre [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg, subRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      post := by sig_implies_post [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg,
        subRV, rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      pub := by sig_implies_pub [Impl.Weierstrass.Mont.Modulus.subContract, Impl.Weierstrass.Mont.sig, arg, subRV,
        rvPre, rvPub, offArg, res, RISCV64.abi, RISCV64.argRegs]
      sat := ⟨satWs, by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.Mont.sig, RISCV64.abi, RISCV64.argRegs, satWs]
        obtain ⟨⟨-, -, -, hfit, -⟩, -, -⟩ := sat_pre
        refine ⟨⟨by decide, trivial, .inl (by decide)⟩, rfl, rfl, by simp, by simp, by simp, ?_⟩
        simp only [Bool.cond_true]
        refine ⟨⟨hfit, ?_⟩, by simp⟩
        rw [numAt, read_zero]; decide⟩ }

end VG.Proof.Weierstrass.RISCV64.P384Order
