module

public import VerifiedGarbage.Impl.Ecdsa.P192.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
meta import VerifiedGarbage.Impl.Ecdsa.P192.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P192Field.Lit

/-! ### `Weierstrass.RISCV64.P192Field.Verified`, which this module and modules that import it used -/

section

/-!
# Arithmetic modulo P-192's `p` and `n` on RISC-V: verified

The functions of any four-word modulus (`Proof/Weierstrass/RISCV64/Gen4.lean`)
for P-192's `p` and `n`: each modulus meets `Ok` (`ok_p`, `ok_n`, by
`decide`), and the taint analysis finds each operation constant time.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P192Field

open VG VG.RISCV64
open VG.Impl.Ecdsa.RISCV64 (p192p4 p192n4)
open VG.Proof.Weierstrass.RISCV64 (mulRV addRV subRV)
open VG.Impl.Ecdsa.RISCV64 (p192MulP p192AddP p192SubP p192MulN p192AddN p192SubN)
open VG.Proof.Weierstrass.RISCV64.Gen4 (Ok CtOk)

theorem ok_p : Ok p192p4.m := ⟨by decide, by decide, by decide⟩
theorem ok_n : Ok p192n4.m := ⟨by decide, by decide, by decide⟩

theorem mul_rv (s : State) (hs : (mulRV p192p4).pre s) :
    ∃ t s', Exec isa p192MulP s t s' ∧ abiPreserved s s' ∧ (mulRV p192p4).post s s' := Gen4.mul_rv rfl ok_p s hs
theorem add_rv (s : State) (hs : (addRV p192p4).pre s) :
    ∃ t s', Exec isa p192AddP s t s' ∧ abiPreserved s s' ∧ (addRV p192p4).post s s' := Gen4.add_rv rfl ok_p s hs
theorem sub_rv (s : State) (hs : (subRV p192p4).pre s) :
    ∃ t s', Exec isa p192SubP s t s' ∧ abiPreserved s s' ∧ (subRV p192p4).post s s' := Gen4.sub_rv rfl ok_p s hs
theorem mul_rv_n (s : State) (hs : (mulRV p192n4).pre s) :
    ∃ t s', Exec isa p192MulN s t s' ∧ abiPreserved s s' ∧ (mulRV p192n4).post s s' := Gen4.mul_rv rfl ok_n s hs
theorem add_rv_n (s : State) (hs : (addRV p192n4).pre s) :
    ∃ t s', Exec isa p192AddN s t s' ∧ abiPreserved s s' ∧ (addRV p192n4).post s s' := Gen4.add_rv rfl ok_n s hs
theorem sub_rv_n (s : State) (hs : (subRV p192n4).pre s) :
    ∃ t s', Exec isa p192SubN s t s' ∧ abiPreserved s s' ∧ (subRV p192n4).post s s' := Gen4.sub_rv rfl ok_n s hs

theorem mulA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p192p4)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p192MulPA s t s' ∧ abiPreserved s s' ∧ (mulRV p192p4).post s s' :=
  Gen4.mulA_rv rfl ok_p s hs
theorem addA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p192p4)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p192AddPA s t s' ∧ abiPreserved s s' ∧ (addRV p192p4).post s s' :=
  Gen4.addA_rv rfl ok_p s hs
theorem subA_rv (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p192p4)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p192SubPA s t s' ∧ abiPreserved s s' ∧ (subRV p192p4).post s s' :=
  Gen4.subA_rv rfl ok_p s hs
theorem mulA_rv_n (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (mulRV p192n4)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p192MulNA s t s' ∧ abiPreserved s s' ∧ (mulRV p192n4).post s s' :=
  Gen4.mulA_rv rfl ok_n s hs
theorem addA_rv_n (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (addRV p192n4)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p192AddNA s t s' ∧ abiPreserved s s' ∧ (addRV p192n4).post s s' :=
  Gen4.addA_rv rfl ok_n s hs
theorem subA_rv_n (s : State) (hs : (VG.Proof.Weierstrass.RISCV64.alignedC (subRV p192n4)).pre s) :
    ∃ t s', Exec isa Impl.Ecdsa.RISCV64.p192SubNA s t s' ∧ abiPreserved s s' ∧ (subRV p192n4).post s s' :=
  Gen4.subA_rv rfl ok_n s hs

end VG.Proof.Weierstrass.RISCV64.P192Field

end

end

/-!
# P-192's field on RISC-V, for `vg_p192_mul` and its callers

The facts the proofs of `vg_p192_mul` (`Proof/Ecdsa/RISCV64/P192/Window.lean`)
and its callers share: P-192's field functions meet the contracts by register
(`field_ok`), and `R = 2²⁵⁶` is a unit modulo `p` (`unit`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P192

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- P-192. -/
abbrev W : Curve := Spec.P192.curve

theorem field_ok : FieldOk p192Field :=
  ⟨P192Field.mul_rv, P192Field.add_rv, P192Field.sub_rv,
    Impl.Ecdsa.RISCV64.p192MulP_noFrames,
    Impl.Ecdsa.RISCV64.p192AddP_noFrames, Impl.Ecdsa.RISCV64.p192SubP_noFrames,
    P192Field.mulA_rv, P192Field.addA_rv, P192Field.subA_rv,
    Impl.Ecdsa.RISCV64.p192MulPA_noFrames,
    Impl.Ecdsa.RISCV64.p192AddPA_noFrames, Impl.Ecdsa.RISCV64.p192SubPA_noFrames⟩

instance : NeZero p192Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 4)) := unitMod_pow_two p_odd _

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (p192.sl i) 4

end VG.Proof.Ecdsa.RISCV64.P192
