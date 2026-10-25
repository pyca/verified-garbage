module

public import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasState
public import VerifiedGarbage.Impl.Bignum.Arm.Select
import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # One in-place selection iteration preserves the full prefix invariant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem selectAliasBody_ok {s0 s : State} {base : BitVec 32} {size o a b n i : Nat}
    (ctx : SelectCtx s0 base size o a b n) (inv : SelectInv s0 base o a b n i s) (hi : i < n)
    (hc : (s0.gpr .r11).toNat ≤ 1) :
    WP isa selectBody s fun t => SelectInv s0 base o a b n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have hn := ctx.nowrap
  have ho := ctx.outFits
  have ha := ctx.aFits
  have hb := ctx.bFits
  have addr {r : Reg} {d : Nat} (hp : s.gpr r = base + BitVec.ofNat 32 d) (hd : d < size) :
      State.addr (s.gpr r + BitVec.ofNat 32 0) = off (State.addr base) d := by
    rw [hp, Offset.add_add, Nat.add_zero]
    exact VG.Arm.addr_add (by omega_arith)
  have writable (d : Nat) (hd : d + 4 ≤ size) : InRegions s.wr (off (State.addr base) d) 4 := by
    rw [inv.rest.wr]
    exact ⟨_, ctx.writable, Offset.contains_base _ hd (by omega_arith)⟩
  have readable (d : Nat) (hd : d + 4 ≤ size) :
      InRegions (s.rd ++ s.wr) (off (State.addr base) d) 4 := by
    obtain ⟨R, hR, hsub⟩ := writable d hd
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  rw [selectBody, WP.seq_iff]
  refine WP.mono (selectStep_ok s _ _ _ (addr inv.outPtr (by omega_arith)) (addr inv.aPtr (by omega_arith))
    (addr inv.bPtr (by omega_arith)) (writable _ (by omega_arith)) (readable _ (by omega_arith))
    (readable _ (by omega_arith)) (by rw [inv.rest.gpr .r11 (by simp [selectLoopClobbers])]; exact hc) inv.mask) ?_
  rintro u ⟨mem, keep⟩
  obtain ⟨outside, prefixValue⟩ := selectAlias_value_step ctx inv hi mem
  refine WP.mono (subAdvance_ok u) ?_
  rintro t ⟨p0, p10, p12, count, zero, mem2, keep2⟩
  have uc : u.gpr .lr = BitVec.ofNat 32 (n - i) :=
    (keep.gpr .lr (by simp [selectClobbers])).trans inv.count
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [p0, keep.gpr .r0 (by simp [selectClobbers]), inv.outPtr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p10, keep.gpr .r10 (by simp [selectClobbers]), inv.aPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p12, keep.gpr .r12 (by simp [selectClobbers]), inv.bPtr]
    change base + BitVec.ofNat 32 (b + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, uc]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
    congr 1
  · rw [mem2]; exact outside
  · rw [mem2]; exact prefixValue
  · rw [keep2.gpr .r4 (by simp), keep.gpr .r4 (by simp [selectClobbers]),
      keep2.gpr .r11 (by simp), keep.gpr .r11 (by simp [selectClobbers])]
    exact inv.mask
  · refine inv.rest.trans ((keep.mono ?_).trans (keep2.mono ?_))
    all_goals decide
  · rw [zero, uc]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_arith]

end VG.Proof.Bignum.Arm
