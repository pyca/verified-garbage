module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute

/-! Public context-entry address calculation preserves all memory. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Impl.Ffdh.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem combTableArgs_raw_ok (s : State) {base ctx : BitVec 32} {len w digit : Nat}
    (ws : Workspace s base (8*len)) (locals : Locals base len s)
    (fit : 52 ≤ 8*len) (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (saved : s.mem.readW (off (State.addr s.sp) 4) 32 = ctx)
    (index : s.gpr .r3 = BitVec.ofNat 32 digit) :
    WP isa (.block CombPrecompute.tableArgs) s fun t =>
      (t.gpr .r4 = ctx + (BitVec.ofNat 32 digit + 2) * (BitVec.ofNat 32 w <<< 3) + 24 ∧
        t.gpr .r0 = base ∧ t.mem = s.mem) ∧ Rest roundClobbers s t := by
  apply withAllRest
  have stackAddr : State.addr (s.sp + BitVec.ofNat 32 4) = off (State.addr s.sp) 4 :=
    addr_add (by have := locals.space.nowrap; omega)
  have baseAddr : State.addr (base + BitVec.ofNat 32 48) = off (State.addr base) 48 :=
    addr_add (by have := ws.nowrap; omega)
  have stackRead := locals.read (d := 4) (by decide)
  have baseRead := ws.read fit
  unfold CombPrecompute.tableArgs
  ffrun [stackAddr, baseAddr, stackRead, baseRead, count, saved, ptr, index]
  simp only [BitVec.natCast_eq_ofNat]
  rfl

theorem combTableAddress (ctx : BitVec 32) (w digit : Nat) :
    ctx + (BitVec.ofNat 32 digit + 2) * (BitVec.ofNat 32 w <<< 3) + 24 =
      ctx + BitVec.ofNat 32 (24 + 8*w*(digit+2)) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change ctx + (BitVec.ofNat 32 digit + BitVec.ofNat 32 2) *
    (BitVec.ofNat 32 w * BitVec.ofNat 32 8) + BitVec.ofNat 32 24 = _
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_mul, ← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 1
  congr 1
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]

end VG.Proof.Ffdh.Arm
