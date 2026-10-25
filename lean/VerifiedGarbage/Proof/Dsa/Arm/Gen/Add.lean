module

import VerifiedGarbage.Proof.Dsa.Arm.Gen.Frame
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Dsa.Arm.Generation
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.St
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # DSA parameter generation on ARMv7: `seed + offset + j`

`addBE n` adds `r1` to the `n` big-endian bytes ending at `r0`, a byte at a
time from the last, the carry and the addend's higher bytes on in `r1`:
`addBE_ok`, against `Spec.Dsa.encodeBE n (decodeBE bytes + addend)`
(`Proof.Dsa.Generation.seedAdd_snoc`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_subs wp_ldrb wp_strb op2_imm op2_reg op2_lsr dpVal
  ofNat_beq_zero toNat_shr)

/-- One step: the byte at `r0` := its sum with `r1`, `r1` := that sum's higher bits. -/
theorem addStep_ok {s : State} {a : Addr} (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (hw : InRegions s.wr a 1) (hc : (s.mem a).toNat + (s.gpr .r1).toNat < 2 ^ 32) :
    WP isa (.block addStep) s fun t =>
      t.mem = s.mem.writeW a (BitVec.ofNat 8 ((s.mem a).toNat + (s.gpr .r1).toNat)) ∧
      t.gpr .r1 = BitVec.ofNat 32 (((s.mem a).toNat + (s.gpr .r1).toNat) / 256) ∧
      t.gpr .r0 = s.gpr .r0 - 1 ∧ t.gpr .r2 = s.gpr .r2 - 1 ∧ t.z = (s.gpr .r2 - 1 == 0) ∧
      Rest [.r0, .r1, .r2, .r3] s t := by
  have hr : InRegions (s.rd ++ s.wr) a 1 := let ⟨r, hr, hc⟩ := hw; ⟨r, List.mem_append_right _ hr, hc⟩
  unfold addStep
  refine wp_ldrb (by decide) ha hr fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  have v : s₂.gpr .r3 = BitVec.ofNat 32 ((s.mem a).toNat + (s.gpr .r1).toNat) := by
    rw [u₂.gpr, dpVal, u₁.gpr, u₁.other .r1 (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := (s.mem a).isLt
    rw [Nat.mod_eq_of_lt (by omega_arith : (s.mem a).toNat < 2 ^ 32)]
  refine wp_strb (a := a) (by decide) (by rw [u₂.other .r0 (by decide), u₁.other .r0 (by decide)]; exact ha)
    (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ u₃ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₄ u₄ => wp_dp (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_subs (op2_imm (by decide)) fun t u₆ z₆ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  · rw [u₆.other .r1 (by decide), u₅.other .r1 (by decide), u₄.gpr, u₃.gpr, v]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
      Nat.mod_eq_of_lt (by omega_arith)]
  · rw [u₆.other .r0 (by decide), u₅.gpr, dpVal, u₄.other .r0 (by decide), u₃.gpr, u₂.other .r0 (by decide),
      u₁.other .r0 (by decide)]
  · rw [u₆.gpr, u₅.other .r2 (by decide), u₄.other .r2 (by decide), u₃.gpr, u₂.other .r2 (by decide),
      u₁.other .r2 (by decide)]
  · rw [z₆, u₅.other .r2 (by decide), u₄.other .r2 (by decide), u₃.gpr, u₂.other .r2 (by decide),
      u₁.other .r2 (by decide)]
  · exact ((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans ((u₃.rest _).trans
      ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))))

/-- After `i` of the `n` bytes, with `c` carried. -/
structure AddInv (s₀ : State) (base : BitVec 32) (n add i c : Nat) (t : State) : Prop where
  le : i ≤ n
  r0 : t.gpr .r0 + BitVec.ofNat 32 i = base + BitVec.ofNat 32 (n - 1)
  r1 : t.gpr .r1 = BitVec.ofNat 32 c
  cle : c ≤ add
  r2 : t.gpr .r2 = BitVec.ofNat 32 (n - i)
  frame : Frame [⟨State.addr base, n⟩] s₀.mem t.mem
  pre : ∀ j < n - i, t.mem (State.addr base + BitVec.ofNat 64 j) = s₀.mem (State.addr base + BitVec.ofNat 64 j)
  eq : Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₀.mem (State.addr base) n) + add) =
    Spec.Dsa.encodeBE (n - i) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt s₀.mem (State.addr base) n).take (n - i)) + c) ++
      Spec.Rsa.bytesAt t.mem (State.addr base + BitVec.ofNat 64 (n - i)) i
  rest : Rest [.r0, .r1, .r2, .r3] s₀ t

/-- One byte of the addition, from the last: `seedAdd_snoc` on a prefix of the bytes. -/
theorem encode_step (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) (c : Nat) :
    Spec.Dsa.encodeBE (k + 1) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt m p n).take (k + 1)) + c) =
      Spec.Dsa.encodeBE k (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt m p n).take k) +
        ((m (p + BitVec.ofNat 64 k)).toNat + c) / 256) ++
        [BitVec.ofNat 8 ((m (p + BitVec.ofNat 64 k)).toNat + c)] := by
  have e : (Spec.Rsa.bytesAt m p n).take (k + 1) = (Spec.Rsa.bytesAt m p n).take k ++ [m (p + BitVec.ofNat 64 k)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by rw [bytesAt_length']; exact hk)]
    simp [Spec.Rsa.bytesAt]
  have l : ((Spec.Rsa.bytesAt m p n).take k).length = k := by rw [List.length_take, bytesAt_length']; omega_arith
  have := VG.Proof.Dsa.Generation.seedAdd_snoc ((Spec.Rsa.bytesAt m p n).take k) (m (p + BitVec.ofNat 64 k)) c
  rw [l] at this
  rw [e, this]

theorem ofNat_sub_one {a : Nat} (h : 0 < a) (h2 : a < 2 ^ 32) :
    BitVec.ofNat 32 a - 1 = BitVec.ofNat 32 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]
  show (2 ^ 32 - 1 + a) % 2 ^ 32 = _
  omega_arith

theorem bytesAt_cons (m : Mem) (p : Addr) (k i : Nat) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 k) (i + 1) =
      m (p + BitVec.ofNat 64 k) :: Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 (k + 1)) i := by
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  rw [BitVec.add_zero]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  show m (p + BitVec.ofNat 64 k + BitVec.ofNat 64 (j + 1)) = m (p + BitVec.ofNat 64 (k + 1) + BitVec.ofNat 64 j)
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 3; omega_arith

theorem addBody_ok {s₀ t : State} {base : BitVec 32} {n add i c : Nat} (hn256 : n < 256)
    (hfit : base.toNat + n ≤ 2 ^ 32)
    (hadd : add < 2 ^ 24) (hw : InRegions s₀.wr (State.addr base) n) (h : AddInv s₀ base n add i c t)
    (hi : i < n) :
    WP isa (.block addStep) t fun u =>
      AddInv s₀ base n add (i + 1) (((t.mem (State.addr base + BitVec.ofNat 64 (n - 1 - i))).toNat + c) / 256) u ∧
        u.z = decide (i + 1 = n) := by
  have hj : n - 1 - i < n := by omega_arith
  have ea : State.addr (t.gpr .r0 + BitVec.ofNat 32 0) = State.addr base + BitVec.ofNat 64 (n - 1 - i) := by
    rw [BitVec.add_zero, ← addr_add (show base.toNat + (n - 1 - i) < 2 ^ 32 by omega_arith)]
    congr 1
    have e := h.r0
    rw [show n - 1 = (n - 1 - i) + i by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc] at e
    have := congrArg (· - BitVec.ofNat 32 i) e
    simpa only [BitVec.add_sub_cancel] using this
  have hw1 : InRegions t.wr (State.addr base + BitVec.ofNat 64 (n - 1 - i)) 1 := by
    rw [h.rest.wr]
    exact Covers.one hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have bl := (t.mem (State.addr base + BitVec.ofNat 64 (n - 1 - i))).isLt
  have c24 : c < 2 ^ 24 := by have := h.cle; omega_arith
  refine WP.mono (addStep_ok ea hw1 (by rw [h.r1, BitVec.toNat_ofNat]; omega_arith)) ?_
  rintro u ⟨mu, r1, r0, r2, z, Ru⟩
  rw [h.r1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at mu r1
  refine ⟨⟨by omega_arith, ?_, r1, ?_, ?_, ?_, ?_, ?_, h.rest.trans Ru⟩, ?_⟩
  · rw [r0, ← h.r0]
    have : ∀ (x : BitVec 32) (y : Nat), x - 1 + BitVec.ofNat 32 (y + 1) = x + BitVec.ofNat 32 y := fun x y => by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_assoc (x - 1), BitVec.add_comm (BitVec.ofNat 32 y),
        ← BitVec.add_assoc]
      congr 1
      exact BitVec.sub_add_cancel x 1
    exact this _ _
  · have := h.cle; rcases Nat.eq_zero_or_pos c with rfl | hc0 <;> omega_arith
  · rw [r2, h.r2, ofNat_sub_one (by omega_arith) (by have := h.le; omega_arith)]; congr 1
  · rw [mu]
    exact h.frame.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  · intro j hj'
    rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_right (fun e => by
      have := Offset.add_ofNat_ne (State.addr base) (a := j) (b := n - 1 - i) (by omega_arith) (by omega_arith) (by omega_arith)
      exact this e)]
    exact h.pre j (by omega_arith)
  · rw [h.eq, show n - i = (n - 1 - i) + 1 by omega_arith, encode_step _ _ (by omega_arith), ← h.pre (n - 1 - i) (by omega_arith),
      show n - (i + 1) = n - 1 - i by omega_arith, bytesAt_cons, List.append_assoc, List.singleton_append]
    congr 2
    · rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_left rfl]
    · refine List.map_congr_left fun k hk => ?_
      have hk := List.mem_range.mp hk
      rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_right (fun e => by
        rw [Offset.add_add] at e
        exact Offset.add_ofNat_ne (State.addr base) (a := n - 1 - i + 1 + k) (b := n - 1 - i) (by omega_arith) (by omega_arith)
          (by omega_arith) e)]
  · rw [z, h.r2, ofNat_sub_one (by omega_arith) (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_arith]

/-- `addBE n`: the `n` big-endian bytes at `base`, `r0` at their last, plus `r1`. -/
theorem addBE_ok {s : State} {base : BitVec 32} {n add : Nat} (hn : 0 < n) (hn256 : n < 256)
    (hfit : base.toNat + n ≤ 2 ^ 32) (hadd : add < 2 ^ 24) (hw : InRegions s.wr (State.addr base) n)
    (h0 : s.gpr .r0 = base + BitVec.ofNat 32 (n - 1)) (h1 : s.gpr .r1 = BitVec.ofNat 32 add) :
    WP isa (addBE n) s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr base) n =
        Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr base) n) + add) ∧
      Frame [⟨State.addr base, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3] s t := by
  unfold addBE
  refine WP.seq (wp_mov (op2_imm (VG.Proof.Rsa.Arm.Keys.encodable_lt hn256)) fun s₁ u₁ => WP.block_nil ?_)
  let inv := fun k t => ∃ i c, i + k = n ∧ 0 < k ∧ AddInv s base n add i c t
  refine WP.loop (M := isa) inv ?_ n s₁ ⟨0, add, by omega_arith, hn, ?_⟩
  · intro k t ⟨i, c, hik, hk, hi⟩
    refine WP.mono (addBody_ok hn256 hfit hadd hw hi (by omega_arith)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨by change some (!u.z) = some false; simp only [hz, he, decide_true, Bool.not_true], ?_⟩
      have e := hu.eq
      rw [he, Nat.sub_self, VG.Proof.Dsa.Generation.seedAdd_nil, List.nil_append, BitVec.add_zero] at e
      exact ⟨e.symm, hu.frame, hu.rest⟩
    · right
      refine ⟨by change some (!u.z) = some true; simp only [hz, he, decide_false, Bool.not_false],
        k - 1, by omega_arith, i + 1, _, by omega_arith, by omega_arith, hu⟩
  · refine ⟨by omega_arith, by rw [u₁.other _ (by decide), h0, BitVec.add_zero], by rw [u₁.other _ (by decide), h1],
      Nat.le_refl _, by rw [u₁.gpr]; rfl, by rw [u₁.mem]; exact Frame.refl _ _, fun j _ => by rw [u₁.mem], ?_,
      u₁.rest (by simp)⟩
    rw [Nat.sub_zero, List.take_of_length_le (by rw [bytesAt_length'])]
    simp [Spec.Rsa.bytesAt]

end VG.Proof.Dsa.Arm.Gen
