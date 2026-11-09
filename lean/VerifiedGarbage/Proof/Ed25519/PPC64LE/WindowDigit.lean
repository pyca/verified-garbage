module

public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.VerifyWindow
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# A window's digit on PPC64LE

`nibble p o` leaves in `r9` nibble `r15` of the bytes at `p + o`, as the
comb's digit reads its scalar's (`nibble_ok`, `nibAt`): the byte's low and
high nibbles, the low one plus the counter's parity times their difference
(`nibble_sel`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE

/-- Digit `i`'s nibble of the scalar at `p`. -/
def nibAt (m : Mem) (p : Addr) (i : Nat) : Nat :=
  (m (p + BitVec.ofNat 64 (i / 2))).toNat / 16 ^ (i % 2) % 16

theorem nibAt_lt (m : Mem) (p : Addr) (i : Nat) : nibAt m p i < 16 := Nat.mod_lt _ (by decide)

/-- A byte's low nibble (`<<< 60 >>> 60`) and high nibble (`>>> 4`). -/
private theorem byte_facts : ∀ x : BitVec 8,
    BitVec.ofNat 64 x.toNat <<< 60 >>> 60 = BitVec.ofNat 64 (x.toNat / 16 ^ 0 % 16) ∧
      BitVec.ofNat 64 x.toNat >>> 4 = BitVec.ofNat 64 (x.toNat / 16 ^ 1 % 16) := by
  decide

/-- The counter's half and parity. -/
private theorem counter_facts : ∀ i < 128,
    BitVec.ofNat 64 i >>> 1 = BitVec.ofNat 64 (i / 2) ∧
      BitVec.ofNat 64 i <<< 63 >>> 63 = BitVec.ofNat 64 (i % 2) := by
  decide

/-- **The selection**: the low nibble plus the parity times the difference is the nibble. -/
theorem nibble_sel (x : BitVec 8) {i : Nat} (hi : i < 128) :
    BitVec.ofNat 64 x.toNat <<< 60 >>> 60 +
        (BitVec.ofNat 64 x.toNat >>> 4 - BitVec.ofNat 64 x.toNat <<< 60 >>> 60) *
          (BitVec.ofNat 64 i <<< 63 >>> 63) =
      BitVec.ofNat 64 (x.toNat / 16 ^ (i % 2) % 16) := by
  obtain ⟨lo, hi4⟩ := byte_facts x
  rw [(counter_facts i hi).2, lo, hi4]
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h]
    generalize BitVec.ofNat 64 (x.toNat / 16 ^ 0 % 16) = u
    generalize BitVec.ofNat 64 (x.toNat / 16 ^ 1 % 16) = w
    exact (congrArg (u + ·) (BitVec.mul_zero (x := w - u))).trans (BitVec.add_zero u)
  · rw [h]
    generalize BitVec.ofNat 64 (x.toNat / 16 ^ 0 % 16) = u
    generalize BitVec.ofNat 64 (x.toNat / 16 ^ 1 % 16) = w
    exact (congrArg (u + ·) (BitVec.mul_one (x := w - u))).trans (by rw [BitVec.add_comm, BitVec.sub_add_cancel])

theorem nibble_ok {s : State} {p : Reg} (hp : p ∉ [Reg.r8, .r9, .r10, .r15]) {P : Addr} (hP : s.gpr p = P)
    {o i : Nat} (ho : o < 2 ^ 15) (hi : i < 128) (h15 : s.gpr .r15 = BitVec.ofNat 64 i)
    (hin : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 o + BitVec.ofNat 64 (i / 2)) 1) :
    WP isa (.block (nibble p o)) s fun t =>
      Rest [.r8, .r9, .r10] s t ∧ t.mem = s.mem ∧
      t.gpr .r9 = BitVec.ofNat 64 (nibAt s.mem (P + BitVec.ofNat 64 o) i) := by
  have cf := counter_facts i hi
  have hp8 : p ≠ .r8 := fun e => hp (by simp [e])
  unfold nibble
  refine wp_lsr (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ => ?_
  let a := P + BitVec.ofNat 64 o + BitVec.ofNat 64 (i / 2)
  have ea : s₂.gpr .r8 + BitVec.ofNat 64 o = a := by
    rw [u₂.gpr, u₁.other _ hp8, hP, u₁.gpr, h15, cf.1, BitVec.add_assoc,
      BitVec.add_comm (BitVec.ofNat 64 (i / 2)), ← BitVec.add_assoc]
  have hin' : InRegions (s₂.rd ++ s₂.wr) a 1 := by
    rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin
  refine wp_lbz (a := a) (by decide) ho ea hin' fun s₃ u₃ => ?_
  have m2 : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have e3 : s₃.gpr .r9 = BitVec.ofNat 64 (s.mem a).toNat := by rw [u₃.gpr, m2]
  refine wp_lsr (by decide) fun s₄ u₄ => wp_lsl (by decide) fun s₅ u₅ => wp_lsr (by decide) fun s₆ u₆ =>
    wp_sub fun s₇ u₇ => wp_lsl (by decide) fun s₈ u₈ => wp_lsr (by decide) fun s₉ u₉ =>
    wp_mul fun s₁₀ u₁₀ => wp_add fun t u₁₁ => WP.block_nil ?_
  refine ⟨(u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
      ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans
      ((u₇.rest (by decide)).trans ((u₈.rest (by decide)).trans ((u₉.rest (by decide)).trans
      ((u₁₀.rest (by decide)).trans (u₁₁.rest (by decide))))))))))),
    by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m2], ?_⟩
  -- The low nibble in `r9`, the difference in `r10`, the parity in `r8`.
  have e6 : s₆.gpr .r9 = BitVec.ofNat 64 (s.mem a).toNat <<< 60 >>> 60 := by
    rw [u₆.gpr, u₅.gpr, u₄.other _ (by decide), e3]
  have e7 : s₇.gpr .r10 = BitVec.ofNat 64 (s.mem a).toNat >>> 4 - BitVec.ofNat 64 (s.mem a).toNat <<< 60 >>> 60 := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, e3, e6]
  have e9 : s₉.gpr .r8 = BitVec.ofNat 64 i <<< 63 >>> 63 := by
    rw [u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h15]
  rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
    e6, u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), e7, e9, nibble_sel _ hi]
  rfl

end VG.Proof.Ed25519.PPC64LE
