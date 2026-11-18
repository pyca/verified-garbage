module

public import VerifiedGarbage.Impl.Ecdsa.P224.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P224Field.Lit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
meta import VerifiedGarbage.Impl.Ecdsa.P224.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P224Field.Lit

/-! ### `Weierstrass.RISCV64.P224Field.Verified`, which this module and modules that import it used -/

section

/-!
# Arithmetic modulo P-224's `p` and `n` on RISC-V: verified

The functions of any four-word modulus (`Proof/Weierstrass/RISCV64/Gen4.lean`)
for P-224's `p` and `n`: each modulus meets `Ok` (`ok_p`, `ok_n`, by
`decide`), and the taint analysis finds each operation constant time.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P224Field

open VG VG.RISCV64
open VG.Impl.Weierstrass.Mont (p224p p224n)
open VG.Proof.Weierstrass.RISCV64 (mulRV addRV subRV)
open VG.Impl.Ecdsa.RISCV64 (p224MulP p224AddP p224SubP p224MulN p224AddN p224SubN)
open VG.Proof.Weierstrass.RISCV64.Gen4 (Ok CtOk)

theorem ok_p : Ok p224p.m := ⟨by decide, by decide, by decide⟩
theorem ok_n : Ok p224n.m := ⟨by decide, by decide, by decide⟩

theorem mul_rv (s : State) (hs : (mulRV p224p).pre s) :
    ∃ t s', Exec isa p224MulP s t s' ∧ abiPreserved s s' ∧ (mulRV p224p).post s s' := Gen4.mul_rv rfl ok_p s hs
theorem add_rv (s : State) (hs : (addRV p224p).pre s) :
    ∃ t s', Exec isa p224AddP s t s' ∧ abiPreserved s s' ∧ (addRV p224p).post s s' := Gen4.add_rv rfl ok_p s hs
theorem sub_rv (s : State) (hs : (subRV p224p).pre s) :
    ∃ t s', Exec isa p224SubP s t s' ∧ abiPreserved s s' ∧ (subRV p224p).post s s' := Gen4.sub_rv rfl ok_p s hs
theorem mul_rv_n (s : State) (hs : (mulRV p224n).pre s) :
    ∃ t s', Exec isa p224MulN s t s' ∧ abiPreserved s s' ∧ (mulRV p224n).post s s' := Gen4.mul_rv rfl ok_n s hs
theorem add_rv_n (s : State) (hs : (addRV p224n).pre s) :
    ∃ t s', Exec isa p224AddN s t s' ∧ abiPreserved s s' ∧ (addRV p224n).post s s' := Gen4.add_rv rfl ok_n s hs
theorem sub_rv_n (s : State) (hs : (subRV p224n).pre s) :
    ∃ t s', Exec isa p224SubN s t s' ∧ abiPreserved s s' ∧ (subRV p224n).post s s' := Gen4.sub_rv rfl ok_n s hs

theorem mulA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p224p)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p224MulPA s t s' ∧ abiPreserved s s' ∧ (mulRV p224p).post s s' :=
  Gen4.mulA_rv rfl ok_p s hs
theorem addA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p224p)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p224AddPA s t s' ∧ abiPreserved s s' ∧ (addRV p224p).post s s' :=
  Gen4.addA_rv rfl ok_p s hs
theorem subA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p224p)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p224SubPA s t s' ∧ abiPreserved s s' ∧ (subRV p224p).post s s' :=
  Gen4.subA_rv rfl ok_p s hs
theorem mulA_rv_n (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p224n)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p224MulNA s t s' ∧ abiPreserved s s' ∧ (mulRV p224n).post s s' :=
  Gen4.mulA_rv rfl ok_n s hs
theorem addA_rv_n (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p224n)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p224AddNA s t s' ∧ abiPreserved s s' ∧ (addRV p224n).post s s' :=
  Gen4.addA_rv rfl ok_n s hs
theorem subA_rv_n (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p224n)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p224SubNA s t s' ∧ abiPreserved s s' ∧ (subRV p224n).post s s' :=
  Gen4.subA_rv rfl ok_n s hs

end VG.Proof.Weierstrass.RISCV64.P224Field

end

end

/-!
# P-224's field on RISC-V, for `vg_p224_mul` and its callers

The facts the proofs of `vg_p224_mul` (`Proof/Ecdh/RISCV64/P224/Tail.lean`)
and its callers share: P-224's field functions meet the contracts by register
(`field_ok`), and `R = 2²⁵⁶` is a unit modulo `p` (`unit`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P224

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- P-224. -/
abbrev W : Curve := Spec.P224.curve

theorem field_ok : FieldOk p224Field :=
  ⟨P224Field.mul_rv, P224Field.add_rv, P224Field.sub_rv,
    Impl.Ecdsa.RISCV64.p224MulP_noFrames,
    Impl.Ecdsa.RISCV64.p224AddP_noFrames, Impl.Ecdsa.RISCV64.p224SubP_noFrames,
    P224Field.mulA_rv, P224Field.addA_rv, P224Field.subA_rv,
    Impl.Ecdsa.RISCV64.p224MulPA_noFrames,
    Impl.Ecdsa.RISCV64.p224AddPA_noFrames, Impl.Ecdsa.RISCV64.p224SubPA_noFrames⟩

instance : NeZero p224Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 4)) := unitMod_pow_two p_odd _

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (p224.sl i) 4

end VG.Proof.Ecdsa.RISCV64.P224
