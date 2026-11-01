module

public import VerifiedGarbage.Impl.Bignum.Arm.NormalizedR2
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Public addresses and loop count for normalized R-squared setup. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_mov wp_str op2_lsl op2_imm op2_reg dpVal)

theorem normalizedR2Top_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (hw : 2 ≤ w)
    (fits : Proof.Rsa.Mont.arrAt w 4 + 8 * w ≤ size) (ptr : s.gpr .r0 = base)
    (width : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.block NormalizedR2.top) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (Proof.Rsa.Mont.arrAt w 4 + 8 * (w - 1))) (1#32) ∧
      Rest [.r1, .r2, .r3] s t := by
  have nowrap := ws.nowrap
  have topFit : Proof.Rsa.Mont.arrAt w 4 + 8 * (w - 1) + 4 ≤ size := by omega
  have a48 : State.addr (s.gpr .r0 + BitVec.ofNat 32 48) = off (State.addr base) 48 := by
    rw [ptr]; exact addr_add (by simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega)
  unfold NormalizedR2.top
  refine wp_ldr (a := off (State.addr base) 48) (by decide) a48
    (ws.read (by simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega)) fun s1 u1 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_reg _ _) fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun s6 u6 => ?_
  have address : State.addr (s6.gpr .r2 + 0#32) =
      off (State.addr base) (Proof.Rsa.Mont.arrAt w 4 + 8 * (w - 1)) := by
    rw [BitVec.add_zero, u6.other .r2 (by decide), u5.gpr, dpVal,
      u4.other .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide),
      u1.other .r0 (by decide), ptr,
      u4.gpr, dpVal, u3.gpr, u2.gpr, dpVal,
      u1.gpr, width]
    simp only [BitVec.shiftLeft_eq_mul_twoPow]
    change State.addr (base + ((BitVec.ofNat 32 w + BitVec.ofNat 32 w * BitVec.ofNat 32 4) *
      BitVec.ofNat 32 8 + BitVec.ofNat 32 312)) = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    have offset : (w + w * 4) * 8 + 312 = Proof.Rsa.Mont.arrAt w 4 + 8 * (w - 1) := by
      simp only [Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]; omega
    rw [offset]
    exact addr_add (by omega)
  refine wp_str (a := off (State.addr base) (Proof.Rsa.Mont.arrAt w 4 + 8 * (w - 1)))
    (by decide) address (by rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]; exact ws.write topFit)
    fun t u7 => WP.block_nil ?_
  refine ⟨?_, (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans
    ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans (u7.rest _))))))⟩
  rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u6.gpr]
  rfl

theorem normalizedR2Count_ok (s : State) {base : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fits : 212 ≤ size) (ptr : s.gpr .r0 = base)
    (width : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w) :
    WP isa (.block NormalizedR2.count) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) 208) (BitVec.ofNat 32 (w + 64)) ∧ Rest [.r1] s t := by
  have nowrap := ws.nowrap
  have a48 : State.addr (s.gpr .r0 + BitVec.ofNat 32 48) = off (State.addr base) 48 := by
    rw [ptr]; exact addr_add (by omega)
  have a208 : State.addr (s.gpr .r0 + BitVec.ofNat 32 208) = off (State.addr base) 208 := by
    rw [ptr]; exact addr_add (by omega)
  unfold NormalizedR2.count
  refine wp_ldr (a := off (State.addr base) 48) (by decide) a48 (ws.read (by omega)) fun s1 u1 => ?_
  refine wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_str (a := off (State.addr base) 208) (by decide)
    (by rw [u2.other .r0 (by decide), u1.other .r0 (by decide)]; exact a208)
    (by rw [u2.wr, u1.wr]; exact ws.write (by omega)) fun t u3 => WP.block_nil ?_
  refine ⟨?_, (u1.rest (by simp)).trans ((u2.rest (by simp)).trans (u3.rest _))⟩
  rw [u3.mem, u2.mem, u1.mem, u2.gpr, dpVal, u1.gpr, width]
  exact congrArg (s.mem.writeW _) (BitVec.ofNat_add _ _).symm

end VG.Proof.Bignum.Arm
