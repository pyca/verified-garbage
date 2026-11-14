module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X448.Pairs
public import VerifiedGarbage.Proof.X448.AArch64.Mul
import VerifiedGarbage.Proof.X448.Encoding
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem

/-! ### `X448.AArch64.Pack`, which only this module used -/

section

/-!
# X448 on AArch64: writing seven-byte chunks

Each pair of bounded limbs is combined in a register and written with seven
byte stores.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

abbrev packed (m : Mem) (base : Addr) (i : Nat) : Nat :=
  limbs m base X2 (2 * i) + radix * limbs m base X2 (2 * i + 1)

theorem packed_bound {m : Mem} {base : Addr} (hb : Bounded m base X2) {i : Nat} (hi : i < 8) :
    packed m base i < 2 ^ 56 := by
  have h0 := hb (2 * i) (by omega_using [hi])
  have h1 := hb (2 * i + 1) (by omega_using [hi])
  simp only [packed, radix] at h0 h1 ⊢
  omega_using [h0, h1]

def packHead (i : Nat) : List Instr :=
  [ld .x4 (X2 + 16 * i + 8), .lsl .x .x4 .x4 28,
    ld .x5 (X2 + 16 * i), .add .x .x4 .x4 .x5]

theorem packHead_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    {i : Nat} (hi : i < 8) :
    WP isa (.block (packHead i)) s fun t =>
      (t.gpr .x4).toNat = packed s.mem base i ∧ t.mem = s.mem ∧ Keeps [.x4, .x6, .x5] s t := by
  have lo := hs.read (d := X2 + 16 * i) (n := 8) (by simp only [X2, slot]; omega_using [hi])
  have lh := hs.read (d := X2 + 16 * i + 8) (n := 8) (by simp only [X2, slot]; omega_using [hi])
  have b := packed_bound hb hi
  have he0 : X2 + 16 * i = X2 + 8 * (2 * i) := by omega_using []
  have he1 : X2 + 16 * i + 8 = X2 + 8 * (2 * i + 1) := by omega_using []
  have le : (X2 + 16 * i) % 8 = 0 ∧ X2 + 16 * i < 32768 := by simp only [X2, slot]; omega_using [hi]
  have he : (X2 + 16 * i + 8) % 8 = 0 ∧ X2 + 16 * i + 8 < 32768 := by simp only [X2, slot]; omega_using [hi]
  apply WP.of_runBlock
  simp only [packHead, ld, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Size.bytes, Nat.reduceLT, BitVec.setWidth_eq, addr, le, he, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hs.x3, State.load, lo, lh, read8_eq, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · rw [he1, he0, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (limbs s.mem base X2 (2 * i + 1) * radix % 2 ^ 64 +
      limbs s.mem base X2 (2 * i)) % 2 ^ 64 = _
    change limbs s.mem base X2 (2 * i) + radix * limbs s.mem base X2 (2 * i + 1) < _ at b
    rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega_using [b]), Nat.mod_eq_of_lt (by omega_using [b])]
    exact Nat.add_comm _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.2, ite_false]

def packByte (i j : Nat) : List Instr :=
  [.strb .x4 .x1 (7 * i + j), .lsr .x .x4 .x4 8]

theorem packByte_ok {s : State} {p : Addr} {i j : Nat} (hp : s.gpr .x1 = p) (hi : i < 8) (hj : j < 7)
    (hw : InRegions s.wr (off p (7 * i + j)) 1) :
    WP isa (.block (packByte i j)) s fun t =>
      (t.gpr .x4).toNat = (s.gpr .x4).toNat / 256 ∧
      t.mem = s.mem.writeW (off p (7 * i + j)) (BitVec.ofNat 8 (s.gpr .x4).toNat) ∧ Keeps [.x4] s t := by
  have enc : (7 * i + j) % 1 = 0 ∧ 7 * i + j < 4096 := by omega_using [hi, hj]
  apply WP.of_runBlock
  simp only [packByte, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceLT, BitVec.setWidth_eq, addr, enc, and_self,
    State.store, hp, hw, ite_true, Option.bind_some, write1_eq,
    RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · apply congrArg (s.mem.writeW (off p (7 * i + j)))
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_using []
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

theorem writeSeven_ok {s : State} {p : Addr} {i : Nat} (hi : i < 8) (hp : s.gpr .x1 = p)
    (hw : ∀ j < 7, InRegions s.wr (off p (7 * i + j)) 1) :
    WP isa (.block ((List.range 7).flatMap (packByte i))) s fun t =>
      (∀ j < 7, t.mem (off p (7 * i + j)) = BitVec.ofNat 8 ((s.gpr .x4).toNat / 256 ^ j)) ∧
      Outside p (7 * i) 7 s.mem t.mem ∧ Keeps [.x4] s t := by
  let inv := fun n (t : State) =>
    (t.gpr .x4).toNat = (s.gpr .x4).toNat / 256 ^ n ∧
    (∀ j < n, t.mem (off p (7 * i + j)) = BitVec.ofNat 8 ((s.gpr .x4).toNat / 256 ^ j)) ∧
    Outside p (7 * i) n s.mem t.mem ∧ Keeps [.x4] s t
  have st : ∀ n t, n < 7 → inv n t → WP isa (.block (packByte i n)) t (inv (n + 1)) := by
    intro n t hn ⟨ta, tf, tm, tk⟩
    refine WP.mono (packByte_ok ((tk.1 _ (by decide)).trans hp) hi hn
      (by rw [tk.2.2]; exact hw n hn)) fun u ⟨ua, um, uk⟩ => ?_
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · rw [ua, ta, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    · intro j hj
      rw [um, writeW8_apply]
      simp only [off_eq_iff p (d := 7 * i + j) (e := 7 * i + n) (by omega_using [hi, hn, hj]) (by omega_using [hi, hn])]
      by_cases h : j = n
      · rw [ite_eq_left (by omega_using [h]), h, ta]
      · rw [ite_eq_right (by omega_using [h])]; exact tf j (by omega_using [hj, h])
    · intro q hq
      rw [um, writeW8_outside _ _ _ (by omega_using [hi, hn]) (by omega_using [hq])]
      exact tm q (by omega_using [hq])
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv st 7 (by decide) s
    ⟨by rw [Nat.pow_zero, Nat.div_one], fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩)
    fun t ⟨_, tf, tm, tk⟩ => ⟨tf, tm, tk⟩

end VG.Proof.X448.AArch64

end

end


/-!
# X448 on AArch64: the output buffer

Output stores cover exactly 56 bytes. The disjoint working space retains the
source limbs and saved registers until the function restores them.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem packPair_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    {i : Nat} (hi : i < 8) (hp : s.gpr .x1 = p)
    (hw : ∀ j < 7, InRegions s.wr (off p (7 * i + j)) 1) :
    WP isa (.block (packPair i)) s fun t =>
      chunk t.mem p i = packed s.mem base i ∧ Outside p (7 * i) 7 s.mem t.mem ∧ Keeps clob s t := by
  change WP isa (.block (packHead i ++ (List.range 7).flatMap (packByte i))) s _
  rw [WP.block_append_iff]
  refine WP.mono (packHead_ok hs hb hi) fun t ⟨ta, tm, tk⟩ => ?_
  refine WP.mono (writeSeven_ok hi ((tk.1 _ (by decide)).trans hp)
    (by intro j hj; rw [tk.2.2]; exact hw j hj)) fun u ⟨uf, um, uk⟩ => ?_
  refine ⟨?_, tm ▸ um, (tk.mono ?_).trans (uk.mono ?_)⟩
  · have bytes : Spec.X448.bytesAt u.mem (off p (7 * i)) 7 =
        VG.Proof.X25519.leBytes 7 (packed s.mem base i) := by
      apply List.map_congr_left
      intro j hj
      rw [Offset.add_add, uf j (List.mem_range.mp hj), ta]
    change VG.Proof.X25519.leNum _ = _
    rw [bytes]
    exact leNum_leBytes (packed_bound hb hi)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide

/-- Writes to the output preserve a word in the disjoint working space. -/
theorem output_word {m m' : Mem} {base p : Addr} {n d : Nat} (h : Outside p 0 n m m') (hn : n ≤ 56)
    (hd : d + 8 ≤ 8192) (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    word m' base d = word m base d := by
  apply Mem.readW_congr
  intro i hi
  rw [Offset.add_add]
  exact h _ (Or.inr (Nat.le_trans (by omega_using [hn] : 0 + n ≤ 56) (hfar _ (by omega_using [hd, hi]))))

theorem output_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    (hp : s.gpr .x1 = p) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) :
    WP isa (.block ((List.range 8).flatMap packPair)) s fun t =>
      Spec.X448.bytesAt t.mem p 56 = VG.Proof.X25519.leBytes 56 (fe s.mem base X2) ∧
      Outside p 0 56 s.mem t.mem ∧ Keeps clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, chunk t.mem p i = packed s.mem base i) ∧ Outside p 0 (7 * n) s.mem t.mem ∧ Keeps clob s t
  have st : ∀ n t, n < 8 → inv n t → WP isa (.block (packPair n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have eq : ∀ j < 16, limbs t.mem base X2 j = limbs s.mem base X2 j := by
      intro j hj
      exact congrArg BitVec.toNat (output_word tm (by omega_using [hn]) (by simp only [X2, slot]; omega_using [hj]) hfar)
    have tb : Bounded t.mem base X2 := by intro j hj; rw [eq j hj]; exact hb j hj
    refine WP.mono (packPair_ok (hs.of_keeps tk (by decide)) tb hn ((tk.1 _ (by decide)).trans hp)
      (by intro j hj; rw [tk.2.2]; exact hw _ (by omega_using [hn, hj]))) fun u ⟨uv, um, uk⟩ => ?_
    have pv : packed t.mem base n = packed s.mem base n := by
      rw [packed, eq (2 * n) (by omega_using [hn]), eq (2 * n + 1) (by omega_using [hn])]
    refine ⟨?_, (tm.mono (by decide) (by omega_using [])).trans (um.mono (by omega_using []) (by omega_using [])), tk.trans uk⟩
    intro i hi
    by_cases h : i = n
    · subst i; exact uv.trans pv
    · have bytes : Spec.X448.bytesAt u.mem (off p (7 * i)) 7 = Spec.X448.bytesAt t.mem (off p (7 * i)) 7 := by
        apply List.map_congr_left
        intro j hj
        have hj := List.mem_range.mp hj
        rw [Offset.add_add]
        exact um _ (Or.inl (by rw [ofs_off' p (by omega_using [hn, hi, hj])]; omega_using [hi, h, hj]))
      change VG.Proof.X25519.leNum _ = _
      rw [bytes]; exact tf i (by omega_using [hi, h])
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv st 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ =>
    ⟨packed_bytes hb tf, tm, tk⟩

end VG.Proof.X448.AArch64
