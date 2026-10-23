module
public import VerifiedGarbage.Impl.MdStream.PPC64LE
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.MdStream.Spec

import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Sha256.Stream
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Streaming Merkle–Damgård hash functions on PPC64LE: length fields and digests

What the length fields (`len64`, `len128`) and digests (`out32`, `out64`) of
`Impl/MdStream/PPC64LE.lean` write (the same as on AArch64), for the hash functions' `Shape`s.
-/

@[expose] public section

namespace VG.Proof.MdStream.PPC64LE

open VG VG.PPC64LE VG.Impl.MdStream.PPC64LE
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil write_eq_writeBytes writeBytes_append
  writeBytes_frame)

/-! ## Byte order -/

/-- The bytes of a byte-reversed word, one by one. -/
theorem rev32_byte_0 (x : BitVec 32) : (rev32 x).extractLsb' 0 8 = x.extractLsb' 24 8 := by
  unfold rev32
  rw [BitVec.extractLsb'_append_eq_of_add_le (v := 24) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev32_byte_1 (x : BitVec 32) : (rev32 x).extractLsb' 8 8 = x.extractLsb' 16 8 := by
  unfold rev32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 16) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev32_byte_2 (x : BitVec 32) : (rev32 x).extractLsb' 16 8 = x.extractLsb' 8 8 := by
  unfold rev32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev32_byte_3 (x : BitVec 32) : (rev32 x).extractLsb' 24 8 = x.extractLsb' 0 8 := by
  unfold rev32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self


theorem rev64_byte_0 (x : BitVec 64) : (rev64 x).extractLsb' 0 8 = x.extractLsb' 56 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_add_le (v := 56) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_1 (x : BitVec 64) : (rev64 x).extractLsb' 8 8 = x.extractLsb' 48 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 48) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_2 (x : BitVec 64) : (rev64 x).extractLsb' 16 8 = x.extractLsb' 40 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 40) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_3 (x : BitVec 64) : (rev64 x).extractLsb' 24 8 = x.extractLsb' 32 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 32) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_4 (x : BitVec 64) : (rev64 x).extractLsb' 32 8 = x.extractLsb' 24 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 24) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_5 (x : BitVec 64) : (rev64 x).extractLsb' 40 8 = x.extractLsb' 16 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 16) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_6 (x : BitVec 64) : (rev64 x).extractLsb' 48 8 = x.extractLsb' 8 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_7 (x : BitVec 64) : (rev64 x).extractLsb' 56 8 = x.extractLsb' 0 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self


theorem bytes32_store (be : Bool) (x : BitVec 32) :
    (List.range 4).map (fun j => (if be then rev32 x else x).extractLsb' (8 * j) 8) = bytes32 be x := by
  cases be
  · rfl
  · simp only [bytes32, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, Nat.reduceMul, rev32_byte_0, rev32_byte_1, rev32_byte_2,
      rev32_byte_3]


theorem bytes64_store (be : Bool) (x : BitVec 64) :
    (List.range 8).map (fun j => (if be then rev64 x else x).extractLsb' (8 * j) 8) = bytes64 be x := by
  cases be
  · rfl
  · simp only [bytes64, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, List.reverse_cons, List.reverse_nil, Nat.reduceMul,
      rev64_byte_0, rev64_byte_1, rev64_byte_2, rev64_byte_3, rev64_byte_4, rev64_byte_5, rev64_byte_6,
      rev64_byte_7]


theorem writeW32 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 32) :
    m.writeW a (if be then rev32 x else x) = writeBytes m a (bytes32 be x) := by
  rw [Mem.writeW, write_eq_writeBytes, ← bytes32_store]; rfl

theorem writeW64 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 64) :
    m.writeW a (if be then rev64 x else x) = writeBytes m a (bytes64 be x) := by
  rw [Mem.writeW, write_eq_writeBytes, ← bytes64_store]; rfl

/-! ## Regions -/

theorem InRegions.offset {rs : List Region} {a : Addr} {n off m : Nat} (h : InRegions rs a n)
    (hm : off + m ≤ n) (hn : n < 2 ^ 64) : InRegions rs (a + BitVec.ofNat 64 off) m := by
  obtain ⟨R, hR, hc⟩ := h
  refine ⟨R, hR, ?_⟩
  simp only [Region.Contains] at *
  have : (a + BitVec.ofNat 64 off - R.base).toNat ≤ (a - R.base).toNat + off := by
    rw [Offset.add_sub_comm,
      BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

/-! ## The length field -/

theorem times8 (x : BitVec 64) : x + x + (x + x) + (x + x + (x + x)) = BitVec.ofNat 64 (8 * x.toNat) := by
  bv_omega

/-- `len64 d be` stores `8 · r29` at `r26 + d`. -/
theorem len64_ok {d : Nat} {be : Bool} {s : State} (hd : d < 2 ^ 15)
    (hout : InRegions s.wr (s.gpr .r26 + BitVec.ofNat 64 d) 8) :
    WP isa (.block (len64 d be)) s fun s' => (∀ r, r ≠ .r8 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .r26 + BitVec.ofNat 64 d)
        (bytes64 be (BitVec.ofNat 64 (8 * (s.gpr .r29).toNat))) := by
  unfold len64
  rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_add fun s₁ u₁ => wp_add fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  have g₃ : ∀ r, r ≠ .r8 → s₃.gpr r = s.gpr r := fun r h => by
    rw [u₃.other r h, u₂.other r h, u₁.other r h]
  have v₃ : s₃.gpr .r8 = BitVec.ofNat 64 (8 * (s.gpr .r29).toNat) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, times8]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  have h26 : s₃.gpr .r26 = s.gpr .r26 := g₃ _ (by decide)
  cases be
  · simp only [Bool.false_eq_true, ite_false]
    by_cases hd4 : d % 4 = 0
    · simp only [hd4, ite_true]
      refine wp_std (a := s.gpr .r26 + BitVec.ofNat 64 d) ⟨hd, hd4⟩ (by rw [h26])
        (by rw [wr₃]; exact hout) fun s' g' => WP.block_nil ⟨fun r h h' => by rw [g'.gpr, g₃ r h],
          g'.rd.trans rd₃, g'.wr.trans wr₃, g'.sp.trans sp₃, ?_⟩
      rw [g'.mem, m₃, v₃]
      exact writeW64 _ _ false _
    · simp only [hd4, ite_false]
      refine wp_addi hd fun t₁ u => wp_std (a := s.gpr .r26 + BitVec.ofNat 64 d) (by decide)
        (by rw [u.gpr, h26]; simp) (by rw [u.wr, wr₃]; exact hout) fun s' g' => WP.block_nil
          ⟨fun r h h' => by rw [g'.gpr, u.other r h', g₃ r h], by rw [g'.rd, u.rd, rd₃],
            by rw [g'.wr, u.wr, wr₃], by rw [g'.sp, u.sp, sp₃], ?_⟩
      rw [g'.mem, u.mem, m₃, u.other _ (by decide), v₃]
      exact writeW64 _ _ false _
  · simp only [ite_true]
    refine wp_li hd fun s₄ u₄ => wp_stdbrx (a := s.gpr .r26 + BitVec.ofNat 64 d)
      (by rw [u₄.other _ (by decide), u₄.gpr, h26]) (by rw [u₄.wr, wr₃]; exact hout)
      fun s' g' => WP.block_nil ⟨fun r h h' => by rw [g'.gpr, u₄.other r h', g₃ r h],
        by rw [g'.rd, u₄.rd, rd₃], by rw [g'.wr, u₄.wr, wr₃], by rw [g'.sp, u₄.sp, sp₃], ?_⟩
    rw [g'.mem, u₄.mem, m₃, u₄.other _ (by decide), v₃, show rev64 (BitVec.ofNat 64 (8 * (s.gpr .r29).toNat)) =
      (if true then rev64 (BitVec.ofNat 64 (8 * (s.gpr .r29).toNat))
        else BitVec.ofNat 64 (8 * (s.gpr .r29).toNat)) from rfl, writeW64]

/-- `len128 d` stores the length in bits of the byte count in `r29`, as a
128-bit big-endian integer, at `r26 + d`. -/
theorem len128_ok {d : Nat} (hd : d + 8 < 2 ^ 15) {s : State}
    (hout : InRegions s.wr (s.gpr .r26 + BitVec.ofNat 64 d) 16) :
    WP isa (.block (len128 d)) s fun s' => (∀ r, r ≠ .r8 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .r26 + BitVec.ofNat 64 d)
        (bytes64 true (s.gpr .r29 >>> 61) ++ bytes64 true (BitVec.ofNat 64 (8 * (s.gpr .r29).toNat))) := by
  have e8 : s.gpr .r26 + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = s.gpr .r26 + BitVec.ofNat 64 (d + 8) :=
    Offset.add_add _ _ _
  unfold len128
  simp only [List.cons_append, List.nil_append]
  refine wp_lsr (by decide) fun s₁ u₁ => wp_li (by omega) fun s₂ u₂ =>
    wp_stdbrx (a := s.gpr .r26 + BitVec.ofNat 64 d)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), u₂.gpr])
    (by rw [u₂.wr, u₁.wr]; simpa using InRegions.offset (off := 0) (m := 8) hout (by omega) (by omega))
    fun s₃ g₃ => ?_
  have h26 : s₃.gpr .r26 = s.gpr .r26 := by rw [g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  have h29 : s₃.gpr .r29 = s.gpr .r29 := by rw [g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  refine (len64_ok (d := d + 8) (be := true) hd (by
    rw [h26, g₃.wr, u₂.wr, u₁.wr, ← e8]; exact InRegions.offset hout (by omega) (by omega))).mono
    fun s' ⟨g, rd, wr, sp, m⟩ => ⟨fun r h h' => by rw [g r h h', g₃.gpr, u₂.other r h', u₁.other r h],
      by rw [rd, g₃.rd, u₂.rd, u₁.rd], by rw [wr, g₃.wr, u₂.wr, u₁.wr], by rw [sp, g₃.sp, u₂.sp, u₁.sp], ?_⟩
  rw [m, h26, h29, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr,
    show rev64 (s.gpr .r29 >>> 61) = (if true then rev64 (s.gpr .r29 >>> 61) else s.gpr .r29 >>> 61) from rfl,
    writeW64, ← e8, show (8 : Nat) = (bytes64 true (s.gpr .r29 >>> 61)).length from rfl,
    writeBytes_append _ _ _ _ (by rw [bytes64_length, bytes64_length]; omega)]

/-! ## The digest -/

theorem setWidth32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `out32 n be` writes the `n` 32-bit words at `r26` to `r28`. -/
theorem out32_ok {n : Nat} (be : Bool) (hn : 4 * n ≤ 64) {s₀ : State}
    (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r26) (4 * n)) (hout : InRegions s₀.wr (s₀.gpr .r28) (4 * n))
    (hd : Region.Disjoint ⟨s₀.gpr .r26, 4 * n⟩ ⟨s₀.gpr .r28, 4 * n⟩) :
    WP isa (.block (out32 n be)) s₀ fun s' =>
      (∀ r, r ≠ .r8 → r ≠ .r11 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      s'.mem = writeBytes s₀.mem (s₀.gpr .r28)
        ((List.range n).flatMap fun k => bytes32 be (s₀.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (4 * k)) 32)) := by
  let f : Nat → List Byte := fun k => bytes32 be (s₀.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (4 * k)) 32)
  have hflat : ∀ k, ((List.range k).flatMap f).length = 4 * k := by
    intro k
    rw [List.length_flatMap, List.map_congr_left (fun x _ => bytes32_length _ _), List.map_const',
      List.sum_replicate_nat, List.length_range, Nat.mul_comm]
  -- Words `[n - j, n)` are left, the others written.
  suffices h : ∀ j ≤ n, ∀ s, (∀ r, r ≠ .r8 → r ≠ .r11 → s.gpr r = s₀.gpr r) → s.rd = s₀.rd →
      s.wr = s₀.wr → s.sp = s₀.sp → s.mem = writeBytes s₀.mem (s₀.gpr .r28) ((List.range (n - j)).flatMap f) →
      WP isa (.block (((List.range n).drop (n - j)).flatMap fun k =>
        [.load .w .r8 .r26 (4 * k)] ++
          (if be then [.li .r11 (4 * k), .storeRev .w .r8 .r28 .r11] else [.store .w .r8 .r28 (4 * k)])))
        s fun s' => (∀ r, r ≠ .r8 → r ≠ .r11 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
          s'.sp = s₀.sp ∧ s'.mem = writeBytes s₀.mem (s₀.gpr .r28) ((List.range n).flatMap f) by
    have := h n (Nat.le_refl _) s₀ (fun _ _ _ => rfl) rfl rfl rfl
      (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, writeBytes_nil])
    rwa [Nat.sub_self, List.drop_zero] at this
  intro j
  induction j with
  | zero =>
    intro _ s g rd wr sp m
    rw [Nat.sub_zero, List.drop_of_length_le (by simp), List.flatMap_nil]
    exact WP.block_nil ⟨g, rd, wr, sp, m⟩
  | succ j ih =>
    intro hj s g rd wr sp m
    have hk : n - (j + 1) < n := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_range,
      List.append_assoc]
    rw [show n - (j + 1) + 1 = n - j by omega]
    have hoff : 4 * (n - (j + 1)) + 4 ≤ 4 * n := by omega
    -- The word read is not yet overwritten.
    have hread : s.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32 =
        s₀.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32 := by
      rw [m]
      refine (writeBytes_frame _ _ _ (R := ⟨s₀.gpr .r28, 4 * n⟩) ?_).readW
        (r := ⟨s₀.gpr .r26 + BitVec.ofNat 64 (4 * (n - (j + 1))), 4⟩) (Region.contains_self _ _) ?_ (by decide)
      · rw [hflat]
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
        omega
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (sub_offset hoff (by omega))
    have hmem : ∀ (t : State), t.mem = s.mem →
        t.mem.writeW (s₀.gpr .r28 + BitVec.ofNat 64 (4 * (n - (j + 1))))
          (if be then rev32 (s.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32)
            else s.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32) =
        writeBytes s₀.mem (s₀.gpr .r28) ((List.range (n - j)).flatMap f) := by
      intro t ht
      rw [ht, writeW32, hread, m, show n - j = n - (j + 1) + 1 by omega, List.range_succ,
        List.flatMap_append, List.flatMap_singleton,
        ← writeBytes_append _ _ _ _ (by rw [hflat, bytes32_length]; omega), hflat]
    rw [List.cons_append]
    refine wp_lwz (a := s₀.gpr .r26 + BitVec.ofNat 64 (4 * (n - (j + 1)))) (by omega)
      (by rw [g _ (by decide) (by decide)]) (by rw [rd, wr]; exact InRegions.offset hin hoff (by omega))
      fun s₁ u₁ => ?_
    cases be
    · simp only [Bool.false_eq_true, ite_false, List.cons_append, List.nil_append]
      refine wp_stw (by omega) (by rw [u₁.other _ (by decide), g _ (by decide) (by decide)])
        (by rw [u₁.wr, wr]; exact InRegions.offset hout hoff (by omega)) fun s₂ g₂ => ?_
      refine ih (by omega) s₂ (fun r h h' => by rw [g₂.gpr, u₁.other r h, g r h h']) (by rw [g₂.rd, u₁.rd, rd])
        (by rw [g₂.wr, u₁.wr, wr]) (by rw [g₂.sp, u₁.sp, sp]) ?_
      rw [g₂.mem, u₁.gpr, setWidth32]
      exact hmem s₁ u₁.mem
    · simp only [ite_true, List.cons_append, List.nil_append]
      refine wp_li (by omega) fun s₂ u₂ => wp_stwbrx (by rw [u₂.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), g _ (by decide) (by decide)])
        (by rw [u₂.wr, u₁.wr, wr]; exact InRegions.offset hout hoff (by omega)) fun s₃ g₃ => ?_
      refine ih (by omega) s₃ (fun r h h' => by rw [g₃.gpr, u₂.other r h', u₁.other r h, g r h h'])
        (by rw [g₃.rd, u₂.rd, u₁.rd, rd]) (by rw [g₃.wr, u₂.wr, u₁.wr, wr]) (by rw [g₃.sp, u₂.sp, u₁.sp, sp]) ?_
      rw [g₃.mem, u₂.mem, u₂.other _ (by decide), u₁.gpr, setWidth32]
      exact hmem s₁ u₁.mem

/-- `out64 n` writes the `n` 64-bit words at `r26` to `r28`, big-endian. -/
theorem out64_ok {n : Nat} (hn : 8 * n ≤ 64) {s₀ : State}
    (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r26) (8 * n)) (hout : InRegions s₀.wr (s₀.gpr .r28) (8 * n))
    (hd : Region.Disjoint ⟨s₀.gpr .r26, 8 * n⟩ ⟨s₀.gpr .r28, 8 * n⟩) :
    WP isa (.block (out64 n)) s₀ fun s' =>
      (∀ r, r ≠ .r8 → r ≠ .r11 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      s'.mem = writeBytes s₀.mem (s₀.gpr .r28)
        ((List.range n).flatMap fun k => bytes64 true (s₀.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (8 * k)) 64)) := by
  let f : Nat → List Byte := fun k => bytes64 true (s₀.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (8 * k)) 64)
  have hflat : ∀ k, ((List.range k).flatMap f).length = 8 * k := by
    intro k
    rw [List.length_flatMap, List.map_congr_left (fun x _ => bytes64_length _ _), List.map_const',
      List.sum_replicate_nat, List.length_range, Nat.mul_comm]
  -- Words `[n - j, n)` are left, the others written.
  suffices h : ∀ j ≤ n, ∀ s, (∀ r, r ≠ .r8 → r ≠ .r11 → s.gpr r = s₀.gpr r) → s.rd = s₀.rd →
      s.wr = s₀.wr → s.sp = s₀.sp → s.mem = writeBytes s₀.mem (s₀.gpr .r28) ((List.range (n - j)).flatMap f) →
      WP isa (.block (((List.range n).drop (n - j)).flatMap fun k =>
        ([.load .d .r8 .r26 (8 * k), .li .r11 (8 * k), .storeRev .d .r8 .r28 .r11] : List Instr)))
        s fun s' => (∀ r, r ≠ .r8 → r ≠ .r11 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
          s'.sp = s₀.sp ∧ s'.mem = writeBytes s₀.mem (s₀.gpr .r28) ((List.range n).flatMap f) by
    have := h n (Nat.le_refl _) s₀ (fun _ _ _ => rfl) rfl rfl rfl
      (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, writeBytes_nil])
    rwa [Nat.sub_self, List.drop_zero] at this
  intro j
  induction j with
  | zero =>
    intro _ s g rd wr sp m
    rw [Nat.sub_zero, List.drop_of_length_le (by simp), List.flatMap_nil]
    exact WP.block_nil ⟨g, rd, wr, sp, m⟩
  | succ j ih =>
    intro hj s g rd wr sp m
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_range]
    rw [show n - (j + 1) + 1 = n - j by omega]
    have hoff : 8 * (n - (j + 1)) + 8 ≤ 8 * n := by omega
    -- The word read is not yet overwritten.
    have hread : s.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64 =
        s₀.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64 := by
      rw [m]
      refine (writeBytes_frame _ _ _ (R := ⟨s₀.gpr .r28, 8 * n⟩) ?_).readW
        (r := ⟨s₀.gpr .r26 + BitVec.ofNat 64 (8 * (n - (j + 1))), 8⟩) (Region.contains_self _ _) ?_ (by decide)
      · rw [hflat]
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
        omega
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (sub_offset hoff (by omega))
    simp only [List.cons_append, List.nil_append]
    refine wp_ld (a := s₀.gpr .r26 + BitVec.ofNat 64 (8 * (n - (j + 1)))) ⟨by omega, by omega⟩
      (by rw [g _ (by decide) (by decide)]) (by rw [rd, wr]; exact InRegions.offset hin hoff (by omega))
      fun s₁ u₁ => ?_
    refine wp_li (by omega) fun s₂ u₂ => wp_stdbrx (a := s₀.gpr .r28 + BitVec.ofNat 64 (8 * (n - (j + 1))))
      (by rw [u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), g _ (by decide) (by decide)])
      (by rw [u₂.wr, u₁.wr, wr]; exact InRegions.offset hout hoff (by omega)) fun s₃ g₃ => ?_
    refine ih (by omega) s₃ (fun r h h' => by rw [g₃.gpr, u₂.other r h', u₁.other r h, g r h h'])
      (by rw [g₃.rd, u₂.rd, u₁.rd, rd]) (by rw [g₃.wr, u₂.wr, u₁.wr, wr]) (by rw [g₃.sp, u₂.sp, u₁.sp, sp]) ?_
    rw [g₃.mem, u₂.mem, u₂.other _ (by decide), u₁.gpr, u₁.mem, hread,
      show rev64 (s₀.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64) =
        (if true then rev64 (s₀.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64) else
          s₀.mem.readW (s₀.gpr .r26 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64) from rfl,
      writeW64, m, show n - j = n - (j + 1) + 1 by omega, List.range_succ,
      List.flatMap_append, List.flatMap_singleton,
      ← writeBytes_append _ _ _ _ (by simp only [hflat, f, bytes64_length]; omega), hflat]

end VG.Proof.MdStream.PPC64LE
