module

public import VerifiedGarbage.Proof.Bignum.Arm.MaskByteStep
public import VerifiedGarbage.Proof.Framework.WriteBytes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Exact byte masking with public loop bounds -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

structure MaskCtx (s : State) (dst : BitVec 32) (n : Nat) : Prop where
  countFits : n < 2 ^ 32
  readable : ∀ i < n, InRegions (s.rd ++ s.wr) (State.addr (dst + BitVec.ofNat 32 i)) 1
  writable : ∀ i < n, InRegions s.wr (State.addr (dst + BitVec.ofNat 32 i)) 1
  distinct : ∀ i < n, ∀ j < n,
    State.addr (dst + BitVec.ofNat 32 i) = State.addr (dst + BitVec.ofNat 32 j) → i = j

structure MaskInv (s0 : State) (dst : BitVec 32) (n i : Nat) (s : State) : Prop where
  index : i ≤ n
  dest : s.gpr .r0 = dst + BitVec.ofNat 32 i
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  masked : ∀ j < i, s.mem (State.addr (dst + BitVec.ofNat 32 j)) =
    s0.mem (State.addr (dst + BitVec.ofNat 32 j)) &&& (s0.gpr .r2).setWidth 8
  outside : ∀ a, (∀ j < i, a ≠ State.addr (dst + BitVec.ofNat 32 j)) → s.mem a = s0.mem a
  rest : Rest [.r0, .r1, .lr] s0 s

theorem maskBody_ok {s0 s : State} {dst : BitVec 32} {n i : Nat}
    (ctx : MaskCtx s0 dst n) (inv : MaskInv s0 dst n i s) (hi : i < n) :
    WP isa (.block maskByteStep) s fun t =>
      MaskInv s0 dst n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have hd : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) =
      State.addr (dst + BitVec.ofNat 32 i) := by rw [inv.dest]; simp
  have hr := ctx.readable i hi
  have hw := ctx.writable i hi
  rw [← inv.rest.rd, ← inv.rest.wr] at hr
  rw [← inv.rest.wr] at hw
  refine WP.mono (maskByteStep_ok s _ hd hr hw) ?_
  rintro t ⟨mem, dest, count, zero, rest⟩
  have original : s.mem (State.addr (dst + BitVec.ofNat 32 i)) =
      s0.mem (State.addr (dst + BitVec.ofNat 32 i)) :=
    inv.outside _ fun j hj he => by have := ctx.distinct i hi j (by omega) he; omega
  have mask := inv.rest.gpr .r2 (by simp)
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [dest, inv.dest, BitVec.add_assoc]
    change dst + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · intro j hj
    rw [mem, VG.WriteBytes.writeW8_apply]
    by_cases he : j = i
    · subst j; simp only [ite_true, original, mask]
    · have ne : State.addr (dst + BitVec.ofNat 32 j) ≠ State.addr (dst + BitVec.ofNat 32 i) :=
        fun h => he (ctx.distinct j (by omega) i hi h)
      rw [ite_eq_right ne]
      exact inv.masked j (by omega)
  · intro a ha
    rw [mem, VG.WriteBytes.writeW8_apply, ite_eq_right (ha i (by omega))]
    exact inv.outside a fun j hj => ha j (by omega)
  · rw [zero, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by have := ctx.countFits; omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

theorem maskBytes_ok (s : State) {dst : BitVec 32} {n : Nat}
    (ctx : MaskCtx s dst n) (hn : 0 < n)
    (hd : s.gpr .r0 = dst) (hc : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa maskBytes s (MaskInv s dst n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ MaskInv s dst n i t
  unfold maskBytes
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (maskBody_ok ctx hi (by omega)) ?_
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
    exact ⟨by omega, by simpa using hd, by simpa using hc,
      by intro j hj; omega, by intros; rfl, Rest.refl _ _⟩

end VG.Proof.Bignum.Arm
