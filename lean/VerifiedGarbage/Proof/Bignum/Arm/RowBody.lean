module

public import VerifiedGarbage.Proof.Bignum.Arm.RowState
public import VerifiedGarbage.Impl.Bignum.Arm.Row
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # One iteration preserves the full row invariant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest mask16 ofNat_beq_zero)

theorem rowBody_ok {s0 s : State} {x base : BitVec 32} {size o b n i : Nat}
    (ctx : RowCtx s0 base size o b n) (inv : RowLoopInv s0 x base o b n i s) (hi : i < n)
    (h1 : s0.gpr .r1 = x &&& mask16) (h10 : s0.gpr .r10 = x >>> 16) (h9 : s0.gpr .r9 = mask16) :
    WP isa rowBody s fun t => RowLoopInv s0 x base o b n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have ho := ctx.outFits
  have hb := ctx.inFits
  have hn := ctx.nowrap
  have readB := row_writable ctx inv.rest.wr (d := b + 4 * i) (by omega)
  have readB' : InRegions (s.rd ++ s.wr) (off (State.addr base) (b + 4 * i)) 4 := by
    rcases readB with ⟨R, hR, hsub⟩
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  rw [rowBody, WP.seq_iff]
  refine WP.mono (rowStep_ok s _ _ x (by rw [inv.rest.gpr .r1 (by decide), h1])
    (by rw [inv.rest.gpr .r10 (by decide), h10]) (by rw [inv.rest.gpr .r9 (by decide), h9]) (row_addr ctx inv.outPtr (by omega))
    (row_addr ctx inv.inPtr (by omega)) readB'
    (row_writable ctx inv.rest.wr (by omega))) ?_
  rintro s1 ⟨v1, m1, k1⟩
  obtain ⟨outside, value⟩ := row_value_step ctx inv hi m1 v1
  refine WP.mono (rowAdvance_ok s1) ?_
  rintro s2 ⟨p0, p12, cnt, zero, mem, k2⟩
  have count1 : s1.gpr .lr = BitVec.ofNat 32 (n - i) :=
    (k1.gpr .lr (by decide)).trans inv.count
  have count2 : s2.gpr .lr = BitVec.ofNat 32 (n - (i + 1)) := by
    rw [cnt, count1]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  refine ⟨⟨by omega, ?_, ?_, count2, ?_, ?_, ?_⟩, ?_⟩
  · rw [p0, k1.gpr .r0 (by decide), inv.outPtr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p12, k1.gpr .r12 (by decide), inv.inPtr]
    change base + BitVec.ofNat 32 (b + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [mem]; exact outside
  · rw [mem, k2.gpr .r11 (by decide)]; exact value
  · refine inv.rest.trans ((k1.mono ?_).trans (k2.mono ?_))
    all_goals decide
  · rw [zero, count1]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

end VG.Proof.Bignum.Arm
