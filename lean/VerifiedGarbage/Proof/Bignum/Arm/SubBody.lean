module

public import VerifiedGarbage.Proof.Bignum.Arm.SubState
public import VerifiedGarbage.Impl.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
import VerifiedGarbage.Proof.Bignum.Arm.SubStep
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # One subtraction iteration preserves the full prefix invariant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem subBody_ok {s0 s : State} {base : BitVec 32} {size o a b n i : Nat}
    (ctx : SubCtx s0 base size o a b n) (inv : SubInv s0 base o a b n i s) (hi : i < n) :
    WP isa subBody s fun t => SubInv s0 base o a b n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have hn := ctx.nowrap
  have ho := ctx.outFits
  have ha := ctx.aFits
  have hb := ctx.bFits
  have addr {r : Reg} {d : Nat} (hp : s.gpr r = base + BitVec.ofNat 32 d) (hd : d < size) :
      State.addr (s.gpr r + BitVec.ofNat 32 0) = off (State.addr base) d := by
    rw [hp, Offset.add_add, Nat.add_zero]
    exact VG.Arm.addr_add (by omega)
  have writable (d : Nat) (hd : d + 4 ≤ size) : InRegions s.wr (off (State.addr base) d) 4 := by
    rw [inv.rest.wr]
    exact ⟨_, ctx.writable, Offset.contains_base _ hd (by omega)⟩
  have readable (d : Nat) (hd : d + 4 ≤ size) :
      InRegions (s.rd ++ s.wr) (off (State.addr base) d) 4 := by
    obtain ⟨R, hR, hsub⟩ := writable d hd
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  rw [subBody, WP.seq_iff]
  refine WP.mono (subStep_ok s _ _ _ (addr inv.outPtr (by omega)) (addr inv.aPtr (by omega))
    (addr inv.bPtr (by omega)) (writable _ (by omega)) (readable _ (by omega))
    (readable _ (by omega)) inv.borrow) ?_
  rintro u ⟨value, borrow, mem, keep⟩
  obtain ⟨outside, prefixValue⟩ := sub_value_step ctx inv hi mem value
  refine WP.mono (subAdvance_ok u) ?_
  rintro t ⟨p0, p10, p12, count, zero, mem2, keep2⟩
  have uc : u.gpr .lr = BitVec.ofNat 32 (n - i) :=
    (keep.gpr .lr (by simp [subClobbers])).trans inv.count
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [p0, keep.gpr .r0 (by simp [subClobbers]), inv.outPtr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p10, keep.gpr .r10 (by simp [subClobbers]), inv.aPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p12, keep.gpr .r12 (by simp [subClobbers]), inv.bPtr]
    change base + BitVec.ofNat 32 (b + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, uc]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [keep2.gpr .r11 (by simp)]; exact borrow
  · rw [mem2]; exact outside
  · rw [mem2, keep2.gpr .r11 (by simp)]; exact prefixValue
  · refine inv.rest.trans ((keep.mono ?_).trans (keep2.mono ?_))
    all_goals decide
  · rw [zero, uc]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

end VG.Proof.Bignum.Arm
