module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Bytes
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.Generation.SeedAdd
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.PPC64LE.ByteStep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: `seed + offset + j`

The loop of `seedAdd` adds `r4` to the `r6` big-endian bytes ending at `r3`,
a byte at a time from the last, the carry and the addend's higher bytes on
in `r4` (`addLoop_ok`), against `Spec.Dsa.encodeBE n (decodeBE bytes + addend)`
(`Proof.Dsa.Generation.seedAdd_snoc`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- One step: the byte at `r3` := its sum with `r4`, `r4` := that sum's higher bits. -/
theorem addStep_ok {s : State} {a : Addr} (ha : s.gpr .r3 = a) (hw : InRegions s.wr a 1)
    (hc : (s.gpr .r4).toNat < 2 ^ 63) :
    WP isa (.block addStep) s fun t =>
      t.mem = s.mem.writeW a (BitVec.ofNat 8 ((s.mem a).toNat + (s.gpr .r4).toNat)) ∧
      t.gpr .r4 = BitVec.ofNat 64 (((s.mem a).toNat + (s.gpr .r4).toNat) / 256) ∧
      t.gpr .r3 = s.gpr .r3 - 1 ∧ t.gpr .r6 = s.gpr .r6 - 1 ∧
      Keep [.r3, .r4, .r5, .r6] s t ∧ t.sp = s.sp := by
  have hr : InRegions (s.rd ++ s.wr) a 1 := let ⟨r, hr, hc⟩ := hw; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.sp_eq ?_
  unfold addStep
  refine wp_lbz (by decide) (by decide) (by rw [ha, BitVec.add_zero]) hr fun s₁ u₁ => ?_
  refine WP.wr exec_add fun s₂ u₂ _ _ => ?_
  have v : s₂.gpr .r5 = BitVec.ofNat 64 ((s.mem a).toNat + (s.gpr .r4).toNat) := by
    rw [u₂.gpr, u₁.gpr, u₁.other .r4 (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := (s.mem a).isLt
    rw [Nat.mod_eq_of_lt (by omega : (s.mem a).toNat < 2 ^ 64)]
  refine wp_stb (a := a) (by decide) (by decide)
    (by rw [u₂.other .r3 (by decide), u₁.other .r3 (by decide), ha, BitVec.add_zero])
    (by rw [u₂.wr, u₁.wr]; exact hw) fun s₃ m₃ => ?_
  refine WP.wr (exec_lsr_d (by decide)) fun s₄ u₄ _ _ => ?_
  refine WP.wr (exec_subi (by decide) (by decide)) fun s₅ u₅ _ _ => ?_
  refine WP.wr (exec_subi (by decide) (by decide)) fun t u₆ _ _ => WP.block_nil fun sp => ⟨?_, ?_, ?_, ?_, ?_, sp⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, m₃.mem, v, u₂.mem, u₁.mem]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  · have bl := (s.mem a).isLt
    rw [u₆.other .r4 (by decide), u₅.other .r4 (by decide), u₄.gpr, m₃.gpr, v]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
  · rw [u₆.other .r3 (by decide), u₅.gpr, u₄.other .r3 (by decide), m₃.gpr, u₂.other .r3 (by decide),
      u₁.other .r3 (by decide)]; rfl
  · rw [u₆.gpr, u₅.other .r6 (by decide), u₄.other .r6 (by decide), m₃.gpr, u₂.other .r6 (by decide),
      u₁.other .r6 (by decide)]; rfl
  · refine ⟨fun r hr => ?_, by rw [u₆.rd, u₅.rd, u₄.rd, m₃.rd, u₂.rd, u₁.rd],
      by rw [u₆.wr, u₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.2.2, u₅.other _ hr.1, u₄.other _ hr.2.1, m₃.gpr, u₂.other _ hr.2.2.1,
      u₁.other _ hr.2.2.1]

/-- After `i` of the `n` bytes, with `c` carried. -/
structure AddInv (s₀ : State) (base : Addr) (n add i c : Nat) (t : State) : Prop where
  le : i ≤ n
  r3 : t.gpr .r3 + BitVec.ofNat 64 i = base + BitVec.ofNat 64 (n - 1)
  r4 : t.gpr .r4 = BitVec.ofNat 64 c
  cle : c ≤ add
  r6 : t.gpr .r6 = BitVec.ofNat 64 (n - i)
  frame : Frame [⟨base, n⟩] s₀.mem t.mem
  pre : ∀ j < n - i, t.mem (base + BitVec.ofNat 64 j) = s₀.mem (base + BitVec.ofNat 64 j)
  enc : Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₀.mem base n) + add) =
    Spec.Dsa.encodeBE (n - i) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt s₀.mem base n).take (n - i)) + c) ++
      Spec.Rsa.bytesAt t.mem (base + BitVec.ofNat 64 (n - i)) i
  keep : Keep [.r3, .r4, .r5, .r6] s₀ t
  sp : t.sp = s₀.sp

/-- One byte of the addition, from the last: `seedAdd_snoc` on a prefix of the bytes. -/
theorem encode_step (m : Mem) (p : Addr) {n k : Nat} (hk : k < n) (c : Nat) :
    Spec.Dsa.encodeBE (k + 1) (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt m p n).take (k + 1)) + c) =
      Spec.Dsa.encodeBE k (Spec.Dsa.decodeBE ((Spec.Rsa.bytesAt m p n).take k) +
        ((m (p + BitVec.ofNat 64 k)).toNat + c) / 256) ++
        [BitVec.ofNat 8 ((m (p + BitVec.ofNat 64 k)).toNat + c)] := by
  have e : (Spec.Rsa.bytesAt m p n).take (k + 1) = (Spec.Rsa.bytesAt m p n).take k ++ [m (p + BitVec.ofNat 64 k)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Rsa.bytesAt]; exact hk)]
    simp [Spec.Rsa.bytesAt]
  have l : ((Spec.Rsa.bytesAt m p n).take k).length = k := by simp [Spec.Rsa.bytesAt]; omega
  have := VG.Proof.Dsa.Generation.seedAdd_snoc ((Spec.Rsa.bytesAt m p n).take k) (m (p + BitVec.ofNat 64 k)) c
  rw [l] at this
  rw [e, this]

theorem bytesAt_cons (m : Mem) (p : Addr) (k i : Nat) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 k) (i + 1) =
      m (p + BitVec.ofNat 64 k) :: Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 (k + 1)) i := by
  simp only [Spec.Rsa.bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  rw [BitVec.add_zero]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  show m (p + BitVec.ofNat 64 k + BitVec.ofNat 64 (j + 1)) = m (p + BitVec.ofNat 64 (k + 1) + BitVec.ofNat 64 j)
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 3; omega

theorem addBody_ok {s₀ t : State} {base : Addr} {n add i c : Nat} (hn : n < 2 ^ 15)
    (hfit : base.toNat + n ≤ 2 ^ 64) (hadd : add < 2 ^ 32) (hw : InRegions s₀.wr base n)
    (h : AddInv s₀ base n add i c t) (hi : i < n) :
    WP isa (.block addStep) t fun u =>
      AddInv s₀ base n add (i + 1) (((t.mem (base + BitVec.ofNat 64 (n - 1 - i))).toNat + c) / 256) u ∧
        (u.gpr .r6 != 0) = decide (i + 1 ≠ n) := by
  have hj : n - 1 - i < n := by omega
  have ea : t.gpr .r3 = base + BitVec.ofNat 64 (n - 1 - i) := by
    have e := h.r3
    rw [show n - 1 = (n - 1 - i) + i by omega, BitVec.ofNat_add, ← BitVec.add_assoc] at e
    have := congrArg (· - BitVec.ofNat 64 i) e
    simpa only [BitVec.add_sub_cancel] using this
  have hw1 : InRegions t.wr (base + BitVec.ofNat 64 (n - 1 - i)) 1 := by
    rw [h.keep.2.2]
    exact Covers.one hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  have bl := (t.mem (base + BitVec.ofNat 64 (n - 1 - i))).isLt
  have c32 : c < 2 ^ 32 := by have := h.cle; omega
  refine WP.mono (addStep_ok ea hw1 (by rw [h.r4, BitVec.toNat_ofNat]; omega)) ?_
  rintro u ⟨mu, r4, r3, r6, Ku, spu⟩
  rw [h.r4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at mu r4
  refine ⟨⟨by omega, ?_, r4, ?_, ?_, ?_, ?_, ?_, (h.keep.trans Ku).mono (by simp), by rw [spu, h.sp]⟩, ?_⟩
  · rw [r3, ← h.r3, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_assoc (t.gpr .r3 - 1),
      BitVec.add_comm (BitVec.ofNat 64 i), ← BitVec.add_assoc]
    show t.gpr .r3 - 1 + 1 + _ = _
    rw [BitVec.sub_add_cancel]
  · have := h.cle; rcases Nat.eq_zero_or_pos c with rfl | hc0 <;> omega
  · have e : BitVec.ofNat 64 (n - i) - 1 = BitVec.ofNat 64 (n - (i + 1)) := count_sub (by omega)
    rw [r6, h.r6, e]
  · rw [mu]
    exact h.frame.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  · intro j hj'
    rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_right (fun e => by
      have := Offset.add_ofNat_ne base (a := j) (b := n - 1 - i) (by omega) (by omega) (by omega)
      exact this e)]
    exact h.pre j (by omega)
  · rw [h.enc, show n - i = (n - 1 - i) + 1 by omega, encode_step _ _ (by omega), ← h.pre (n - 1 - i) (by omega),
      show n - (i + 1) = n - 1 - i by omega, bytesAt_cons, List.append_assoc, List.singleton_append]
    congr 2
    · rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_left rfl]
    · refine List.map_congr_left fun k hk => ?_
      have hk := List.mem_range.mp hk
      rw [mu, VG.WriteBytes.writeW8_apply, ite_eq_right (fun e => by
        rw [Offset.add_add] at e
        exact Offset.add_ofNat_ne base (a := n - 1 - i + 1 + k) (b := n - 1 - i) (by omega) (by omega)
          (by omega) e)]
  · have e : BitVec.ofNat 64 (n - i) - 1 = BitVec.ofNat 64 (n - (i + 1)) := count_sub (by omega)
    rw [r6, h.r6, e]
    exact count_nz (by omega) (by omega)

/-- The loop of `seedAdd`: the `n` big-endian bytes at `base`, `r3` at their
last, plus `r4`, the count in `r6`. -/
theorem addLoop_ok {s : State} {base : Addr} {n add : Nat} (hn : 0 < n) (hn15 : n < 2 ^ 15)
    (hfit : base.toNat + n ≤ 2 ^ 64) (hadd : add < 2 ^ 32) (hw : InRegions s.wr base n)
    (h3 : s.gpr .r3 = base + BitVec.ofNat 64 (n - 1)) (h4 : s.gpr .r4 = BitVec.ofNat 64 add)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 n) :
    WP isa (.loop (.block addStep) (.nonzero .d .r6)) s fun t =>
      Spec.Rsa.bytesAt t.mem base n =
        Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem base n) + add) ∧
      Frame [⟨base, n⟩] s.mem t.mem ∧ Keep [.r3, .r4, .r5, .r6] s t ∧ t.sp = s.sp := by
  refine loop_nz (fun i t => ∃ c, AddInv s base n add i c t) hn
    (fun i hi t ⟨c, h⟩ => WP.mono (addBody_ok hn15 hfit hadd hw h hi) fun u ⟨hu, hz⟩ => ⟨⟨_, hu⟩, hz⟩)
    (fun t ⟨c, h⟩ => ?_) ⟨add, by omega, by rw [h3, BitVec.add_zero], h4, Nat.le_refl _, by rw [h6, Nat.sub_zero],
      Frame.refl _ _, fun _ _ => rfl, ?_, Keep.refl _ _, rfl⟩
  · rw [Nat.sub_zero, List.take_of_length_le (by simp [Spec.Rsa.bytesAt])]
    simp [Spec.Rsa.bytesAt]
  · have e := h.enc
    rw [Nat.sub_self, VG.Proof.Dsa.Generation.seedAdd_nil, List.nil_append, BitVec.add_zero] at e
    exact ⟨e.symm, h.frame, h.keep, h.sp⟩

end VG.Proof.Dsa.PPC64LE.Gen
