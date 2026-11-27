module

import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Bignum.Arm.ReverseBytes
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.ReverseByteStep
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Bignum.Arm.ReverseBytes`, which this module and modules that import it used -/

section

/-! # Runtime endian conversion, with byte-exact output and memory preservation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

/-- The source pointer starts at the last byte; the destination starts at the first.
The address conditions also allow a caller to use subranges of a larger workspace. -/
structure ReverseCtx (s : State) (src dst : BitVec 32) (n : Nat) : Prop where
  countFits : n < 2 ^ 32
  readable : ∀ i < n, InRegions (s.rd ++ s.wr) (State.addr (src - BitVec.ofNat 32 i)) 1
  writable : ∀ i < n, InRegions s.wr (State.addr (dst + BitVec.ofNat 32 i)) 1
  separate : ∀ i < n, ∀ j < n,
    State.addr (src - BitVec.ofNat 32 i) ≠ State.addr (dst + BitVec.ofNat 32 j)
  distinct : ∀ i < n, ∀ j < n,
    State.addr (dst + BitVec.ofNat 32 i) = State.addr (dst + BitVec.ofNat 32 j) → i = j

structure ReverseInv (s0 : State) (src dst : BitVec 32) (n i : Nat) (s : State) : Prop where
  index : i ≤ n
  source : s.gpr .r1 = src - BitVec.ofNat 32 i
  dest : s.gpr .r0 = dst + BitVec.ofNat 32 i
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  copied : ∀ j < i, s.mem (State.addr (dst + BitVec.ofNat 32 j)) =
    s0.mem (State.addr (src - BitVec.ofNat 32 j))
  outside : ∀ a, (∀ j < i, a ≠ State.addr (dst + BitVec.ofNat 32 j)) → s.mem a = s0.mem a
  rest : Rest [.r0, .r1, .r2, .lr] s0 s

theorem reverseBody_ok {s0 s : State} {src dst : BitVec 32} {n i : Nat}
    (ctx : ReverseCtx s0 src dst n) (inv : ReverseInv s0 src dst n i s) (hi : i < n) :
    WP isa (.block reverseByteStep) s fun t =>
      ReverseInv s0 src dst n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have hs : State.addr (s.gpr .r1 + BitVec.ofNat 32 0) =
      State.addr (src - BitVec.ofNat 32 i) := by rw [inv.source]; simp
  have hd : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) =
      State.addr (dst + BitVec.ofNat 32 i) := by rw [inv.dest]; simp
  have hr := ctx.readable i hi
  have hw := ctx.writable i hi
  rw [← inv.rest.rd, ← inv.rest.wr] at hr
  rw [← inv.rest.wr] at hw
  refine WP.mono (reverseByteStep_ok s _ _ hs hd hr hw) ?_
  rintro t ⟨mem, dest, source, count, zero, rest⟩
  have original : s.mem (State.addr (src - BitVec.ofNat 32 i)) =
      s0.mem (State.addr (src - BitVec.ofNat 32 i)) :=
    inv.outside _ fun j hj => ctx.separate i hi j (by omega_using [hi, hj])
  refine ⟨⟨by omega_using [hi], ?_, ?_, ?_, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [source, inv.source, BitVec.sub_sub]
    change src - (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [dest, inv.dest, BitVec.add_assoc]
    change dst + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi])]
    congr 1
  · intro j hj
    rw [mem, VG.WriteBytes.writeW8_apply]
    by_cases he : j = i
    · subst j; simp only [ite_true, original]
    · have ne : State.addr (dst + BitVec.ofNat 32 j) ≠ State.addr (dst + BitVec.ofNat 32 i) :=
        fun h => he (ctx.distinct j (by omega_using [hi, hj]) i hi h)
      rw [ite_eq_right ne]
      exact inv.copied j (by omega_using [hj, he])
  · intro a ha
    rw [mem, VG.WriteBytes.writeW8_apply, ite_eq_right (ha i (by omega_using []))]
    exact inv.outside a fun j hj => ha j (by omega_using [hj])
  · rw [zero, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi]), ofNat_beq_zero (by have := ctx.countFits; omega_using [this])]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_using [hi]]

/-- Reverse a nonempty byte range without touching any other memory. -/
theorem reverseBytes_ok (s : State) {src dst : BitVec 32} {n : Nat}
    (ctx : ReverseCtx s src dst n) (hn : 0 < n)
    (hs : s.gpr .r1 = src) (hd : s.gpr .r0 = dst)
    (hc : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa reverseBytes s (ReverseInv s src dst n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ ReverseInv s src dst n i t
  unfold reverseBytes
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (reverseBody_ok ctx hi (by omega_using [hik, hk])) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_using [hk], i + 1, by omega_using [hik, hk], by omega_using [hik, hk, he], hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega_using [], hn, ?_⟩
    exact ⟨by omega_using [], by simpa using hs, by simpa using hd,
      by simpa using hc, by intro j hj; omega, by intros; rfl, Rest.refl _ _⟩

end VG.Proof.Bignum.Arm

end

end

/-! # Endian conversion of ordinary disjoint byte buffers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm

theorem reverse_source_addr (src : BitVec 32) {n i : Nat}
    (fit : src.toNat + n ≤ 2 ^ 32) (hi : i < n) :
    State.addr (src + BitVec.ofNat 32 (n - 1) - BitVec.ofNat 32 i) =
      State.addr src + BitVec.ofNat 64 (n - 1 - i) := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
    Offset.ofNat_sub_ofNat (by omega_using [hi])]
  exact addr_add (by omega_using [fit])

/-- Standard readable/writable, nonoverlapping buffers discharge all loop conditions. -/
theorem reverseCtx_of_regions (s : State) (src dst : BitVec 32) {n : Nat}
    (hn : n < 2 ^ 32) (srcFit : src.toNat + n ≤ 2 ^ 32)
    (dstFit : dst.toNat + n ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) n)
    (write : InRegions s.wr (State.addr dst) n)
    (sep : Region.Disjoint ⟨State.addr src, n⟩ ⟨State.addr dst, n⟩) :
    ReverseCtx s (src + BitVec.ofNat 32 (n - 1)) dst n := by
  have ds (j : Nat) (hj : j < n) := addr_add (a := dst) (k := j) (by omega_using [dstFit, hj])
  have sc (i : Nat) (hi : i < n) :
      (⟨State.addr src, n⟩ : Region).Contains (State.addr src + BitVec.ofNat 64 (n - 1 - i)) 1 :=
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn])
  have dc (j : Nat) (hj : j < n) :
      (⟨State.addr dst, n⟩ : Region).Contains (State.addr dst + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega_using [hj]) (by omega_using [hn, hj])
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [reverse_source_addr src srcFit hi]
    obtain ⟨r, hr, hc⟩ := read
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hn])]; omega_using [hi])⟩
  · intro j hj
    rw [ds j hj]
    obtain ⟨r, hr, hc⟩ := write
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hn, hj])]; omega_using [hj])⟩
  · intro i hi j hj he
    rw [reverse_source_addr src srcFit hi, ds j hj] at he
    exact sep _ (he ▸ sc i hi) (dc j hj)
  · intro i hi j hj he
    rw [ds i hi, ds j hj] at he
    have e := congrArg (fun a => (a - State.addr dst).toNat) he
    simpa only [Mem.sub_ofNat_toNat _ (by omega_using [hn, hi] : i < 2 ^ 64),
      Mem.sub_ofNat_toNat _ (by omega_using [hn, hj] : j < 2 ^ 64)] using e

theorem ReverseInv.frame {s0 s : State} {src dst : BitVec 32} {n i : Nat}
    (inv : ReverseInv s0 src dst n i s) (fit : dst.toNat + n ≤ 2 ^ 32) :
    Frame [⟨State.addr dst, n⟩] s0.mem s.mem := by
  intro a ha
  apply inv.outside a
  intro j hj he
  apply ha ⟨State.addr dst, n⟩ (by simp)
  rw [he, addr_add (by have := inv.index; omega_using [fit, hj, this])]
  exact Offset.contains_base _ (by have := inv.index; omega_using [hj, this]) (by have := inv.index; omega_using [fit, hj, this])

end VG.Proof.Bignum.Arm
