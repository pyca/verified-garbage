module

public import VerifiedGarbage.Impl.Bignum.Arm.CopyWords
public import VerifiedGarbage.Proof.Bignum.Arm.SelectState

import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.SelectWord
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
import VerifiedGarbage.Proof.Bignum.Arm.SubAdvance
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
/-! # Termination and exact value of runtime-length word copying -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CopyWord.lean`, which only this module imported.
section

/-! A word copy writes the source once, without evaluating a selection mask. -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

theorem copyWord_ok (s : State) (o a : Addr)
    (ho : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = o)
    (ha : State.addr (s.gpr .r10 + BitVec.ofNat 32 0) = a)
    (wo : InRegions s.wr o 4) (ra : InRegions (s.rd ++ s.wr) a 4) :
    WP isa copyWord s fun t =>
      t.mem = s.mem.writeW o (s.mem.readW a 32) ∧ Rest selectClobbers s t := by
  unfold copyWord
  refine wp_ldr (a := a) (by decide) ha ra fun u load => ?_
  refine wp_str (a := o) (by decide) (by rw [load.other .r0 (by decide)]; exact ho)
    (by rw [load.wr]; exact wo) fun t store => WP.block_nil ?_
  refine ⟨?_, (load.rest (by simp [selectClobbers])).trans (store.rest _)⟩
  rw [store.mem,load.mem,load.gpr]

end VG.Proof.Bignum.Arm
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CopyWordBody.lean`, which only this module imported.
section

/-! # A word copy preserves the selection invariant with identical sources -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem copyWordBody_ok {s0 s : State} {base : BitVec 32} {size o a n i : Nat}
    (ctx : SubCtx s0 base size o a a n) (inv : SelectInv s0 base o a a n i s) (hi : i < n) :
    WP isa copyWordBody s fun t => SelectInv s0 base o a a n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
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
  rw [copyWordBody, WP.seq_iff]
  refine WP.mono (copyWord_ok s _ _ (addr inv.outPtr (by omega)) (addr inv.aPtr (by omega))
    (writable _ (by omega)) (readable _ (by omega))) ?_
  rintro u ⟨mem, keep⟩
  have selected : u.mem = s.mem.writeW (off (State.addr base) (o + 4 * i))
      (if (s.gpr .r11).toNat = 0 then s.mem.readW (off (State.addr base) (a + 4 * i)) 32
        else s.mem.readW (off (State.addr base) (a + 4 * i)) 32) := by
    simpa only [ite_self] using mem
  obtain ⟨outside, prefixValue⟩ := select_value_step ctx inv hi selected
  refine WP.mono (subAdvance_ok u) ?_
  rintro t ⟨p0, p10, p12, count, zero, mem2, keep2⟩
  have uc : u.gpr .lr = BitVec.ofNat 32 (n - i) :=
    (keep.gpr .lr (by simp [selectClobbers])).trans inv.count
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [p0, keep.gpr .r0 (by simp [selectClobbers]), inv.outPtr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p10, keep.gpr .r10 (by simp [selectClobbers]), inv.aPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p12, keep.gpr .r12 (by simp [selectClobbers]), inv.bPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, uc]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
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
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem copyWords_ok (s : State) {base : BitVec 32} {size o a n : Nat}
    (ctx : SubCtx s base size o a a n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hp10 : s.gpr .r10 = base + BitVec.ofNat 32 a)
    (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 a)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa copyWords s (SelectInv s base o a a n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ SelectInv s base o a a n i t
  rw [copyWords, WP.seq_iff]
  refine WP.mono (selectMask_ok s) ?_
  rintro u ⟨mask, keep⟩
  refine WP.loop (M := isa) inv ?_ n u ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (copyWordBody_ok ctx hi (by omega)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (show Rest [.r4] s u from ⟨keep.regs, keep.rd, keep.wr, keep.sp⟩).mono (by simp [selectLoopClobbers])⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using (keep.regs .r0 (by simp)).trans hp0
    · simpa only [Nat.mul_zero, Nat.add_zero] using (keep.regs .r10 (by simp)).trans hp10
    · simpa only [Nat.mul_zero, Nat.add_zero] using (keep.regs .r12 (by simp)).trans hp12
    · simpa only [Nat.sub_zero] using (keep.regs .lr (by simp)).trans hcount
    · rw [keep.mem]; exact Outside.refl _ _ _ _
    · rw [keep.mem]; simp only [val32, ite_self]
    · rw [keep.regs .r11 (by simp)]; exact mask

end VG.Proof.Bignum.Arm
