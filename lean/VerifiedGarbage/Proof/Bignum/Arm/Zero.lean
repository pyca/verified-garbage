module

public import VerifiedGarbage.Proof.Bignum.Arm.ZeroStep
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.CallLay
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A runtime-length zeroing of a packed-word accumulator -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

structure ZeroCtx (s : State) (base : BitVec 32) (size o n : Nat) : Prop where
  nowrap : base.toNat + size ≤ 2 ^ 32
  fits : o + 4 * n ≤ size
  writable : InRegions s.wr (State.addr base) size

structure ZeroInv (s0 : State) (base : BitVec 32) (o n i : Nat) (s : State) : Prop where
  index : i ≤ n
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) o i = 0
  rest : Rest [.r0, .lr] s0 s

theorem zeroBody_ok {s0 s : State} {base : BitVec 32} {size o n i : Nat}
    (ctx : ZeroCtx s0 base size o n) (inv : ZeroInv s0 base o n i s) (hi : i < n)
    (hz : s0.gpr .r3 = 0) :
    WP isa (.block zeroStep) s fun t => ZeroInv s0 base o n (i + 1) t ∧
      t.z = decide (i + 1 = n) := by
  have hn := ctx.nowrap
  have hf := ctx.fits
  have writable (d : Nat) (hd : d + 4 ≤ size) :
      InRegions s.wr (off (State.addr base) d) 4 := by
    rw [inv.rest.wr]
    exact CallLay.inRegions_sub ctx.writable hd (by omega)
  have alo : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) =
      off (State.addr base) (o + 4 * i) := by
    rw [inv.ptr, Offset.add_add, Nat.add_zero]
    exact VG.Arm.addr_add (by omega)
  refine WP.mono (zeroStep_ok s _ alo (writable _ (by omega))
    ((inv.rest.gpr .r3 (by simp)).trans hz)) ?_
  rintro t ⟨mem, ptr, count, zero, rest⟩
  have wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i) (0 : BitVec 32) (by omega)
  rw [← mem] at wr
  have low := wr.val32 (d := o) (k := i) (by omega) (by omega)
  have top : w32 t.mem (State.addr base) (o + 4 * i) = 0 := by
    rw [mem, w32_write_self]
    rfl
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [ptr, inv.ptr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · exact (inv.outside.mono (Nat.le_refl _) (by omega)).trans (wr.mono (by omega) (by omega))
  · rw [val32_succ, low, top, inv.value, Nat.mul_zero, Nat.add_zero]
  · rw [zero, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

/-- Zero a nonempty packed-word range, preserving all other memory. -/
theorem zero_ok (s : State) {base : BitVec 32} {size o n : Nat}
    (ctx : ZeroCtx s base size o n) (hn : 0 < n)
    (hp : s.gpr .r0 = base + BitVec.ofNat 32 o)
    (hc : s.gpr .lr = BitVec.ofNat 32 n) (hz : s.gpr .r3 = 0) :
    WP isa zero s (ZeroInv s base o n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ ZeroInv s base o n i t
  unfold zero
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (zeroBody_ok ctx hi (by omega) hz) ?_
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
    refine ⟨by omega, ?_, ?_, Outside.refl _ _ _ _, rfl, Rest.refl _ _⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using hp
    · simpa only [Nat.sub_zero] using hc

end VG.Proof.Bignum.Arm
