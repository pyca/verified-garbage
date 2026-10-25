module
public import VerifiedGarbage.Impl.Bignum.Arm.Row
public import VerifiedGarbage.Proof.Bignum.Arm.RowState

import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Two words of a row an iteration preserve the row invariant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest mask16 ofNat_beq_zero)

/-- The address of a word `k` bytes above a pointer into the workspace. -/
theorem row_addr_at {s0 s : State} {base : BitVec 32} {size o b n d k : Nat}
    (ctx : RowCtx s0 base size o b n) {r : Reg}
    (hr : s.gpr r = base + BitVec.ofNat 32 d) (hd : d + k < size) :
    State.addr (s.gpr r + BitVec.ofNat 32 k) = off (State.addr base) (d + k) := by
  rw [hr, Offset.add_add]
  exact VG.Arm.addr_add (by have := ctx.nowrap; omega)

theorem rowBody2_ok {s0 s : State} {x base : BitVec 32} {size o b n i : Nat}
    (ctx : RowCtx s0 base size o b n) (inv : RowLoopInv s0 x base o b n i s) (hi : i + 2 ≤ n)
    (h1 : s0.gpr .r1 = x &&& mask16) (h10 : s0.gpr .r10 = x >>> 16) (h9 : s0.gpr .r9 = mask16) :
    WP isa rowBody2 s fun t => RowLoopInv s0 x base o b n (i + 2) t ∧ t.z = decide (i + 2 = n) := by
  have ho := ctx.outFits
  have hb := ctx.inFits
  have hn := ctx.nowrap
  have read (u : State) (hu : u.wr = s0.wr) (d : Nat) (hd : d + 4 ≤ size) :
      InRegions (u.rd ++ u.wr) (off (State.addr base) d) 4 := by
    rcases row_writable ctx hu hd with ⟨R, hR, hsub⟩
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  rw [rowBody2, WP.seq_iff]
  refine WP.mono (rowStepAt_ok s 0 (by decide) _ _ x (by rw [inv.rest.gpr .r1 (by decide), h1])
    (by rw [inv.rest.gpr .r10 (by decide), h10]) (by rw [inv.rest.gpr .r9 (by decide), h9])
    (row_addr_at ctx inv.outPtr (by omega_arith)) (row_addr_at ctx inv.inPtr (by omega_arith))
    (read s inv.rest.wr _ (by omega_arith)) (row_writable ctx inv.rest.wr (by omega_arith))) ?_
  rintro s1 ⟨v1, m1, k1⟩
  obtain ⟨outside1, value1⟩ := row_value_step ctx inv (by omega_arith) m1 v1
  have wr1 : s1.wr = s0.wr := k1.wr.trans inv.rest.wr
  have p0 : s1.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i) :=
    (k1.gpr .r0 (by decide)).trans inv.outPtr
  have p12 : s1.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * i) :=
    (k1.gpr .r12 (by decide)).trans inv.inPtr
  have rest1 : Rest stepClobbers s0 s1 := inv.rest.trans (k1.mono (by decide))
  rw [WP.seq_iff]
  refine WP.mono (rowStepAt_ok s1 4 (by decide) _ _ x (by rw [rest1.gpr .r1 (by decide), h1])
    (by rw [rest1.gpr .r10 (by decide), h10]) (by rw [rest1.gpr .r9 (by decide), h9])
    (row_addr_at ctx p0 (by omega_arith)) (row_addr_at ctx p12 (by omega_arith))
    (read s1 wr1 _ (by omega_arith)) (row_writable ctx wr1 (by omega_arith))) ?_
  rintro s2 ⟨v2, m2, k2⟩
  rw [show o + 4 * i + 4 = o + 4 * (i + 1) by omega_arith] at m2
  rw [show b + 4 * i + 4 = b + 4 * (i + 1) by omega_arith, show o + 4 * i + 4 = o + 4 * (i + 1) by omega_arith] at v2
  obtain ⟨outside2, value2⟩ := row_value_step_of ctx outside1 value1 (by omega_arith) m2 v2
  refine WP.mono (rowAdvance2_ok s2) ?_
  rintro s3 ⟨q0, q12, cnt, zero, mem, k3⟩
  have count2 : s2.gpr .lr = BitVec.ofNat 32 (n - i) :=
    (k2.gpr .lr (by decide)).trans ((k1.gpr .lr (by decide)).trans inv.count)
  have sub2 : BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 2 = BitVec.ofNat 32 (n - (i + 2)) := by
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), show n - i - 2 = n - (i + 2) by omega_arith]
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [q0, k2.gpr .r0 (by decide), p0]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 8 = _
    rw [Offset.add_add, show o + 4 * i + 8 = o + 4 * (i + 2) by omega_arith]
  · rw [q12, k2.gpr .r12 (by decide), p12]
    change base + BitVec.ofNat 32 (b + 4 * i) + BitVec.ofNat 32 8 = _
    rw [Offset.add_add, show b + 4 * i + 8 = b + 4 * (i + 2) by omega_arith]
  · rw [cnt, count2]
    exact sub2
  · rw [mem, show 4 * (i + 2) = 4 * (i + 1 + 1) by omega_arith]; exact outside2
  · rw [mem, k3.gpr .r11 (by decide), show i + 2 = i + 1 + 1 by omega_arith]; exact value2
  · refine rest1.trans ((k2.mono ?_).trans (k3.mono ?_))
    all_goals decide
  · rw [zero, count2]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 2 == 0) = _
    rw [sub2, ofNat_beq_zero (by omega_arith)]
    simp only [show n - (i + 2) = 0 ↔ i + 2 = n by omega_arith]

end VG.Proof.Bignum.Arm
