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
`fn_ok`.
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
  simp only [Fits, VG.Proof.Weierstrass.RISCV64.rvOwn_le (show p384n.k ≤ 6 by decide), Impl.Weierstrass.Mont.ownAt,
    Impl.Weierstrass.Mont.ownBytes] at fo fa fb
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

theorem mulA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p384n)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.P384Order.mulFnA s t s' ∧ abiPreserved s s' ∧
      (mulRV p384n).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ :=
    P384Field.fnA_rv rfl (@mulCore_core) hs.1.1 hs.2 (by rw [← n_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v1, by rw [n_eq]; exact v2, k⟩

theorem addA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p384n)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.P384Order.addFnA s t s' ∧ abiPreserved s s' ∧
      (addRV p384n).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := P384Field.fnA_rv rfl (@addCore_core) hs.1.1 hs.2 (by rw [← n_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v, k⟩

theorem subA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p384n)).pre s) :
    ∃ t s', Exec isa Impl.Weierstrass.RISCV64.P384Order.subFnA s t s' ∧ abiPreserved s s' ∧
      (subRV p384n).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := P384Field.fnA_rv rfl (@subCore_core) hs.1.1 hs.2 (by rw [← n_eq]; exact hs.1.2)
  exact ⟨t, s', he, a, by rw [n_eq]; exact v, k⟩


end VG.Proof.Weierstrass.RISCV64.P384Order
