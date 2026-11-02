module

import VerifiedGarbage.Proof.Ed448.RISCV64.BaseSel
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseBits
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
public import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder

/-!
# Ed448 on RISCV64: the addition of `R` and `P`

RFC 8032 §5.2.4's addition `T = R + P` of `Impl/Ed448/RISCV64/ScalarBase.lean`
(`addition`) as X448's field operations, and its elements (`addV_vals`), which
verification's equation runs (`VStep.lean`); the slots of `R` and `d`
(`RQ`) and their elements (`ptV`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (ACC BITS X2 Z2 R)
open VG.Spec.X448 (Fe)
open VG.Spec.Ed448 (Point pointAdd basePoint)

/-- `p` or, if `sw = 1`, `q`. -/
abbrev pick {α : Type} (sw : Nat) (p q : α) : α := VG.Proof.X25519.sel sw p q

theorem pick_X (sw : Nat) (p q : Point) : (pick sw p q).X = pick sw p.X q.X := by
  unfold pick VG.Proof.X25519.sel; split <;> rfl

theorem pick_Y (sw : Nat) (p q : Point) : (pick sw p q).Y = pick sw p.Y q.Y := by
  unfold pick VG.Proof.X25519.sel; split <;> rfl

theorem pick_Z (sw : Nat) (p q : Point) : (pick sw p q).Z = pick sw p.Z q.Z := by
  unfold pick VG.Proof.X25519.sel; split <;> rfl

/-! ## The slots -/

/-- The elements of `R = r`, `P = p` and `d`. -/
def ptV (r p : Point) (q : Nat) : Fe :=
  if q = RX then r.X else if q = RY then r.Y else if q = RZ then r.Z else if q = PX then p.X
  else if q = PY then p.Y else if q = PZ then p.Z else Spec.Ed448.d

/-- The slots of `R` and `d`, between iterations. -/
def RQ : List Nat := [RX, RY, RZ, DK]

/-- With `P`'s, after the selection. -/
def SQ : List Nat := [PZ, PY, PX, RX, RY, RZ, DK]

/-- The addition but its last operation. -/
def addOps : List FOp :=
  [.mul TA RZ PZ, .mul TY TA TA, .mul TC RX PX, .mul TD RY PY, .mul TZ DK TC, .mul TZ TZ TD,
    .sub TF TY TZ, .add TG TY TZ, .add TH RX RY, .add TX PX PY, .mul TH TH TX, .mul TX TA TF,
    .sub TH TH TC, .sub TH TH TD, .mul TX TX TH, .mul TY TA TG, .sub TH TD TC, .mul TY TY TH]

theorem addition_eq : addition = R64.opsCode addOps (R64.fcode (FOp.mul TZ TF TG)) := rfl

theorem addOps_ok : R64.opsOk addOps SQ = true := by decide

/-- The slots after the addition. -/
def FQ : List Nat := TZ :: outsQ addOps SQ

theorem last_ok : R64.Sep8 TZ (outsQ addOps SQ) = true ∧ TZ + 56 ≤ ACC ∧ TF ∈ outsQ addOps SQ ∧
    TG ∈ outsQ addOps SQ := by decide

/-- The elements after the addition. -/
def addV (r p : Point) : Nat → Fe :=
  upd (runOps addOps (ptV r p)) TZ (runOps addOps (ptV r p) TF * runOps addOps (ptV r p) TG)

theorem addV_vals (r p : Point) :
    addV r p RX = r.X ∧ addV r p RY = r.Y ∧ addV r p RZ = r.Z ∧ addV r p DK = Spec.Ed448.d ∧
      addV r p TX = (pointAdd r p).X ∧ addV r p TY = (pointAdd r p).Y ∧
      addV r p TZ = (pointAdd r p).Z := by
  simp only [addV, addOps, runOps, FOp.out, FOp.val, upd, ptV, pointAdd, RX, RY, RZ, PX, PY, PZ, DK, TX,
    TY, TZ, TA, TC, TD, TF, TG, TH, X2, Z2, R, Nat.reduceEqDiff, ↓reduceIte, and_self]

/-! ## Bits -/

section

theorem par_shift (x : Nat) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x <<< 63) >>> 63 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  have := bit_shift (BitVec.ofNat 64 x) (j := 0) (by decide)
  rw [Nat.sub_zero, Nat.shiftRight_zero, toNat_imm hx, Nat.and_one_is_mod] at this
  rw [this, toNat_imm (by omega_arith)]

theorem wp_or {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

end

end VG.Proof.Ed448.RISCV64
