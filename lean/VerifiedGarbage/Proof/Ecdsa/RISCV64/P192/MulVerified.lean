module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.MulFn
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.P192.Point
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P192.MulFn
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# `vg_p192_mul` on RISC-V: the contract

The facts of `Impl.Weierstrass.Mul.Curve.mulInRangeContract` for P-192 on
RISC-V, by register (`mulRVc`: `ws` in `a0`), which the windowed
`vg_p192_mul` meets (`Proof/Ecdsa/RISCV64/P192/Window.lean`), and a state
satisfying the precondition (`satState`: the constants and `G` in
Montgomery's form at their slots).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P192

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- P-192's curve of `Proof/Weierstrass/MulContract.lean`, with P-224's,
P-256's and P-384's layout on RISC-V: the multiplication's own slots in the
tail (`tail`), and a result in range (`inRange`). -/
abbrev MC : Impl.Weierstrass.Mul.Curve := { Impl.Weierstrass.Mul.p192 with tail := true, inRange := true }

/-- `vg_p192_mul(ws = a0)`. -/
def mulRVc : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ MC.ConstsOk (s.gpr .a0) s.mem ∧ MC.PointOk (s.gpr .a0) s.mem
  post s s' := MC.ResultInRange (MC.scalar (s.gpr .a0) s.mem) (MC.point (s.gpr .a0) s.mem) (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0

/-- `Represents` is the proofs' `Rep`. -/
theorem represents_of_rep {C : Curve} {X Y Z : Fe C} {P : Point C}
    (h : Rep C X Y Z P) : Impl.Weierstrass.MulBase.Represents X Y Z P := by
  cases P <;> exact h

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    MC.toPoint.coordAt m ws o = wordsVal m ws o 4 := by
  unfold Impl.Weierstrass.Point.Curve.coordAt
  rw [Impl.Weierstrass.Mont.numAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws 4 o

/-- The saves, at `mulSave = 1504`. -/
abbrev saves : List (Nat × Nat) := [(1504, 8), (1512, 8), (1520, 8)]

/-- Byte `a` of the number `x` at slot `i` of a working space at `0x1000`,
if `a` is in that slot. -/
def satByte (a : Addr) (i x : Nat) : Option (BitVec 8) :=
  if 0x1000 + p192.sl i ≤ a.toNat ∧ a.toNat < 0x1000 + p192.sl i + 32 then
    some (BitVec.ofNat 8 (x >>> (8 * (a.toNat - (0x1000 + p192.sl i)))))
  else none

/-- `x R mod p`. -/
abbrev mont (x : Nat) : Nat := x * 2 ^ 256 % W.p

/-- The memory of `satState`: `p`, and one, `a`, `3 b` and `G`'s coordinates
in Montgomery's form, at their slots for `ws = 0x1000`, zeros elsewhere. -/
def satMem : Mem := fun a =>
  ((satByte a MP W.p).orElse fun _ => (satByte a ONEP (mont 1)).orElse fun _ =>
    (satByte a AP (mont W.a)).orElse fun _ => (satByte a B3P (mont (3 * W.b))).orElse fun _ =>
    (satByte a RX (mont W.gx)).orElse fun _ => satByte a RY (mont W.gy)).getD 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | _ => 0
  sp := 0x10000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_consts : MC.ConstsOk 0x1000 satMem := by
  unfold Impl.Weierstrass.Mul.Curve.ConstsOk
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem sat_x : (MC.qCoords 0x1000 satMem).1 = mont W.gx := by decide +kernel

theorem sat_y : (MC.qCoords 0x1000 satMem).2 = mont W.gy := by decide +kernel

theorem sat_point (hL : VG.Proof.Weierstrass.Law W) : MC.PointOk 0x1000 satMem := by
  have dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 256) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) unit
  have hp0 : 0 < W.p := by decide
  refine ⟨by rw [sat_x]; exact Nat.mod_lt _ hp0, by rw [sat_y]; exact Nat.mod_lt _ hp0, ?_⟩
  have eG : MC.point 0x1000 satMem = Spec.Weierstrass.G W := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [sat_x, sat_y, dq, dq]
    exact congrArg₂ Point.affine (toM_mont unit) (toM_mont unit)
  rw [eG]
  exact VG.Proof.P192.onCurve_G


end VG.Proof.Ecdsa.RISCV64.P192
