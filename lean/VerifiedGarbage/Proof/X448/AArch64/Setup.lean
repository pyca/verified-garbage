module

public import VerifiedGarbage.Proof.X448.AArch64.Env
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X448.AArch64.Initial
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.X448.AArch64
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.X448.AArch64.Swap
import VerifiedGarbage.Proof.X448.AArch64.Step
public import VerifiedGarbage.Proof.X448.Limbs
public import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `X448.AArch64.DecodeAll`, which this module and modules that import it used -/

section

/-! ### `X448.AArch64.DecodeStore`, which this module and modules that import it used -/

section

/-! ### `X448.AArch64.Decode`, which this module and modules that import it used -/

section

/-! ### `X448.Pairs`, which this module and modules that import it used -/

section

/-!
# X448: seven-byte chunks and limb pairs

A seven-byte chunk contains exactly two 28-bit limbs. Reading eight chunks
uses all 56 input bytes.
-/

@[expose] public section

namespace VG.Proof.X448

open VG VG.Spec.X448
open VG.Proof.X25519 (leNum leNum_append leNum_lt)

abbrev chunk (m : Mem) (p : Addr) (i : Nat) : Nat :=
  leNum (bytesAt m (p + BitVec.ofNat 64 (7 * i)) 7)

def decoded (m : Mem) (p : Addr) (i : Nat) : Nat :=
  if i % 2 = 0 then chunk m p (i / 2) % radix else chunk m p (i / 2) / radix

theorem chunk_lt (m : Mem) (p : Addr) (i : Nat) : chunk m p i < radix * radix := by
  have h := leNum_lt (bytesAt m (p + BitVec.ofNat 64 (7 * i)) 7)
  rw [length_bytesAt] at h
  exact h

theorem decoded_even (m : Mem) (p : Addr) (i : Nat) : decoded m p (2 * i) = chunk m p i % radix := by
  rw [decoded, show 2 * i % 2 = 0 by omega_using [], ite_eq_left rfl, show 2 * i / 2 = i by omega_using []]

theorem decoded_odd (m : Mem) (p : Addr) (i : Nat) : decoded m p (2 * i + 1) = chunk m p i / radix := by
  have hd : (2 * i + 1) / 2 = i := by omega_using []
  have hm : (2 * i + 1) % 2 = 1 := by omega_using []
  rw [decoded, hd, hm, ite_eq_right (by decide)]

theorem decoded_bound (m : Mem) (p : Addr) (i : Nat) : decoded m p i < radix := by
  unfold decoded
  split
  · exact Nat.mod_lt _ (by decide)
  · have h := chunk_lt m p (i / 2)
    exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h

theorem byte_power (n : Nat) : 256 ^ (7 * n) = radix ^ (2 * n) := by
  rw [Nat.pow_mul, Nat.pow_mul]
  exact congrArg (fun b => b ^ n) (by decide)

theorem decoded_val (m : Mem) (p : Addr) (n : Nat) :
    valN (decoded m p) (2 * n) = leNum (bytesAt m p (7 * n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega_using [], valN, valN, ih, decoded_even, decoded_odd,
      Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.mod_add_div]
    rw [show 7 * (n + 1) = 7 * n + 7 by omega_using [], bytesAt_add, leNum_append, length_bytesAt, byte_power]

/-- Accumulating a seven-byte chunk from its highest byte downwards. -/
def suffix (m : Mem) (p : Addr) (i n : Nat) : Nat :=
  leNum (bytesAt m (p + BitVec.ofNat 64 (7 * i + (7 - n))) n)

theorem suffix_bound (m : Mem) (p : Addr) (i n : Nat) : suffix m p i n < 256 ^ n := by
  have h := leNum_lt (bytesAt m (p + BitVec.ofNat 64 (7 * i + (7 - n))) n)
  rw [length_bytesAt] at h
  exact h

theorem suffix_succ (m : Mem) (p : Addr) (i : Nat) {n : Nat} (hn : n < 7) :
    suffix m p i (n + 1) = 256 * suffix m p i n + (m (p + BitVec.ofNat 64 (7 * i + (6 - n)))).toNat := by
  unfold suffix
  have bs : ∀ (q : Addr) (n : Nat), bytesAt m q (n + 1) = m q :: bytesAt m (q + 1) n :=
    VG.Proof.X25519.bytesAt_succ m
  rw [bs, leNum]
  have he : p + BitVec.ofNat 64 (7 * i + (7 - (n + 1))) + 1 =
      p + BitVec.ofNat 64 (7 * i + (7 - n)) := by
    change p + BitVec.ofNat 64 (7 * i + (7 - (n + 1))) + BitVec.ofNat 64 1 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega_using [hn]
  rw [he, show 7 - (n + 1) = 6 - n by omega_using [], Nat.add_comm]

end VG.Proof.X448

end

end

/-!
# X448 on AArch64: decoding the u-coordinate

Seven byte loads form each pair of 28-bit limbs; no load extends past the
56-byte input.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- Accumulate one byte from the high end of a seven-byte chunk. -/
def decodeByte (i j : Nat) : List Instr :=
  [.lsl .x .x4 .x4 8, .ldrb .x7 .x2 (7 * i + (6 - j)), .add .x .x4 .x4 .x7]

theorem decodeByte_ok {s : State} {p : Addr} {i j : Nat}
    (hp : s.gpr .x2 = p) (hi : i < 8) (hb : (s.gpr .x4).toNat < 2 ^ 48)
    (hr : InRegions (s.rd ++ s.wr) (off p (7 * i + (6 - j))) 1) :
    WP isa (.block (decodeByte i j)) s fun t =>
      (t.gpr .x4).toNat = 256 * (s.gpr .x4).toNat + (s.mem (off p (7 * i + (6 - j)))).toNat ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x7] s t := by
  have byteb := (s.mem (off p (7 * i + (6 - j)))).isLt
  have mulb : (s.gpr .x4).toNat * 256 < 2 ^ 64 := by omega_using [hb]
  have enc : (7 * i + (6 - j)) % 1 = 0 ∧ 7 * i + (6 - j) < 4096 := by omega_using [hi]
  apply WP.of_runBlock
  simp only [decodeByte, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceLT, BitVec.setWidth_eq, addr, enc, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hp,
    State.load, hr, read1_eq, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    change (((s.gpr .x4).toNat * 256) % 2 ^ 64 +
      ((s.mem (off p (7 * i + (6 - j)))).toNat % 2 ^ 32) % 2 ^ 64) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt mulb, Nat.mod_eq_of_lt (by omega_using [] : (s.mem (off p (7 * i + (6 - j)))).toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [] : (s.mem (off p (7 * i + (6 - j)))).toNat < 2 ^ 64)]
    omega_using [hb]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.2, ite_false]

def readSeven (i : Nat) : List Instr :=
  [.movz .x .x4 0 0] ++ (List.range 7).flatMap (decodeByte i)

theorem readSevenInit_ok (s : State) :
    WP isa (.block [.movz .x .x4 0 0]) s fun t =>
      (t.gpr .x4).toNat = 0 ∧ t.mem = s.mem ∧ Keeps [.x4, .x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, ite_false]

theorem readSeven_ok {s : State} {p : Addr} {i : Nat} (hp : s.gpr .x2 = p) (hi : i < 8)
    (hr : ∀ j < 7, InRegions (s.rd ++ s.wr) (off p (7 * i + j)) 1) :
    WP isa (.block (readSeven i)) s fun t =>
      (t.gpr .x4).toNat = chunk s.mem p i ∧ t.mem = s.mem ∧ Keeps [.x4, .x5, .x7, .x8] s t := by
  rw [readSeven, WP.block_append_iff]
  refine WP.mono (readSevenInit_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  let inv := fun n (u : State) =>
    (u.gpr .x4).toNat = suffix s.mem p i n ∧ u.mem = s.mem ∧ Keeps [.x4, .x5, .x7] t u
  have step : ∀ n u, n < 7 → inv n u → WP isa (.block (decodeByte i n)) u (inv (n + 1)) := by
    intro n u hn ⟨uv, um, uk⟩
    have up : u.gpr .x2 = p := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hp)
    have ub : (u.gpr .x4).toNat < 2 ^ 48 := by
      rw [uv]
      have h := suffix_bound s.mem p i n
      have hpow : 256 ^ n ≤ 256 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega_using [hn])
      exact Nat.lt_of_lt_of_le h hpow
    have ur : InRegions (u.rd ++ u.wr) (off p (7 * i + (6 - n))) 1 := by
      rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2]; exact hr _ (by omega_using [])
    refine WP.mono (decodeByte_ok up hi ub ur) fun v ⟨vv, vm, vk⟩ => ⟨?_, vm.trans um, uk.trans vk⟩
    rw [vv, uv, um, suffix_succ _ _ _ hn]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv step 7 (by decide) t
    ⟨tz, tm, Keeps.refl _ _⟩) fun u ⟨uv, um, uk⟩ => ⟨?_, um, ?_⟩
  · exact uv
  · refine (tk.mono ?_).trans (uk.mono ?_)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide

end VG.Proof.X448.AArch64

end

end

/-!
# X448 on AArch64: storing decoded limb pairs

Each seven-byte chunk is split into two limbs and stored into both copies of
the input coordinate.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def storePair (i : Nat) : List Instr :=
  [.logic .and .x .x7 .x4 .x12, st .x7 (X1 + 16 * i), st .x7 (X3 + 16 * i),
    .lsr .x .x4 .x4 28, st .x4 (X1 + 16 * i + 8), st .x4 (X3 + 16 * i + 8)]

def pairMem (m : Mem) (base : Addr) (i v : Nat) : Mem :=
  (((m.writeW (off base (X1 + 16 * i)) (BitVec.ofNat 64 (v % radix))).writeW
    (off base (X3 + 16 * i)) (BitVec.ofNat 64 (v % radix))).writeW
    (off base (X1 + 16 * i + 8)) (BitVec.ofNat 64 (v / radix))).writeW
    (off base (X3 + 16 * i + 8)) (BitVec.ofNat 64 (v / radix))

theorem storePair_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 8) :
    WP isa (.block (storePair i)) s fun t =>
      t.mem = pairMem s.mem base i (s.gpr .x4).toNat ∧ Keeps [.x4, .x7] s t := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 := fun _ hd => hs.write hd
  have low : s.gpr .x4 &&& (0x0fffffff : BitVec 64) = BitVec.ofNat 64 ((s.gpr .x4).toNat % radix) := by
    apply BitVec.eq_of_toNat_eq
    rw [and28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide : radix < 2 ^ 64))]
  have high : s.gpr .x4 >>> 28 = BitVec.ofNat 64 ((s.gpr .x4).toNat / radix) := by
    apply BitVec.eq_of_toNat_eq
    rw [shr28, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (s.gpr .x4).isLt)]
  have enc : ∀ d, d % 8 = 0 → d + 8 ≤ 8192 → d % 8 = 0 ∧ d < 32768 :=
    fun d hd hb => ⟨hd, by omega_using [hb]⟩
  apply WP.of_runBlock
  simp only [storePair, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, State.read, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.wr_write, BitVec.setWidth_eq, hs.x3, hs.mask,
    enc (X1 + 16 * i) (by simp only [X1, slot]; omega_using []) (by simp only [X1, slot]; omega_using [hi]),
    enc (X3 + 16 * i) (by simp only [X3, slot]; omega_using []) (by simp only [X3, slot]; omega_using [hi]),
    enc (X1 + 16 * i + 8) (by simp only [X1, slot]; omega_using []) (by simp only [X1, slot]; omega_using [hi]),
    enc (X3 + 16 * i + 8) (by simp only [X3, slot]; omega_using []) (by simp only [X3, slot]; omega_using [hi]),
    w (X1 + 16 * i) (by simp only [X1, slot]; omega_using [hi]),
    w (X3 + 16 * i) (by simp only [X3, slot]; omega_using [hi]),
    w (X1 + 16 * i + 8) (by simp only [X1, slot]; omega_using [hi]),
    w (X3 + 16 * i + 8) (by simp only [X3, slot]; omega_using [hi]),
    Nat.reduceLT, and_self, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, write8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [low, high]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem pairMem_limbs (m : Mem) (base : Addr) {i j v : Nat} (hi : i < 8) (hj : j < 16)
    (hv : v < radix * radix) :
    limbs (pairMem m base i v) base X1 j =
      (if j = 2 * i + 1 then v / radix else if j = 2 * i then v % radix else limbs m base X1 j) ∧
    limbs (pairMem m base i v) base X3 j =
      (if j = 2 * i + 1 then v / radix else if j = 2 * i then v % radix else limbs m base X3 j) := by
  have lo : (BitVec.ofNat 64 (v % radix)).toNat = v % radix := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide : radix < 2 ^ 64))]
  have high : (BitVec.ofNat 64 (v / radix)).toNat = v / radix := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans ((Nat.div_lt_iff_lt_mul (by decide)).mpr hv)
      (by decide : radix < 2 ^ 64))]
  let m₁ := (m.writeW (off base (X1 + 8 * (2 * i))) (BitVec.ofNat 64 (v % radix))).writeW
    (off base (X3 + 8 * (2 * i))) (BitVec.ofNat 64 (v % radix))
  have p₁ := pair_write (m := m) (base := base) (x := X1) (y := X3) (n := 2 * i)
    (by decide) (by decide) (by decide) (by omega_using [hi]) hj (BitVec.ofNat 64 (v % radix)) (BitVec.ofNat 64 (v % radix))
  have p₂ := pair_write (m := m₁) (base := base) (x := X1) (y := X3) (n := 2 * i + 1)
    (by decide) (by decide) (by decide) (by omega_using [hi]) hj (BitVec.ofNat 64 (v / radix)) (BitVec.ofNat 64 (v / radix))
  have index0 : 8 * (2 * i) = 16 * i := by omega_using []
  have index1 : 8 * (2 * i + 1) = 16 * i + 8 := by omega_using []
  simp only [m₁, index0, index1, ← Nat.add_assoc, lo, high] at p₁ p₂
  rw [p₁.1, p₁.2] at p₂
  exact p₂

theorem pairMem_outside (m : Mem) (base : Addr) {i : Nat} (hi : i < 8) (v : Nat) :
    Outside2 base X1 (16 * (i + 1)) X3 (16 * (i + 1)) m (pairMem m base i v) := by
  intro p hx hy
  simp only [pairMem]
  have x0 : X1 + 16 * i + 8 ≤ 8192 := by simp only [X1, slot]; omega_using [hi]
  have x1 : X1 + 16 * i + 8 + 8 ≤ 8192 := by simp only [X1, slot]; omega_using [hi]
  have y0 : X3 + 16 * i + 8 ≤ 8192 := by simp only [X3, slot]; omega_using [hi]
  have y1 : X3 + 16 * i + 8 + 8 ≤ 8192 := by simp only [X3, slot]; omega_using [hi]
  rw [writeW_outside _ _ _ y1 p (by omega_using [hy]), writeW_outside _ _ _ x1 p (by omega_using [hx]),
    writeW_outside _ _ _ y0 p (by omega_using [hy]), writeW_outside _ _ _ x0 p (by omega_using [hx])]

theorem decodePair_ok {s : State} {base p : Addr} (hs : Scr s base) {i : Nat} (hi : i < 8)
    (hp : s.gpr .x2 = p) (hr : ∀ j < 7, InRegions (s.rd ++ s.wr) (off p (7 * i + j)) 1) :
    WP isa (.block (decodePair i)) s fun t =>
      t.mem = pairMem s.mem base i (chunk s.mem p i) ∧ Keeps [.x4, .x5, .x7, .x8] s t := by
  change WP isa (.block (readSeven i ++ storePair i)) s _
  rw [WP.block_append_iff]
  refine WP.mono (readSeven_ok hp hi hr) fun t ⟨tv, tm, tk⟩ => ?_
  refine WP.mono (storePair_ok (hs.of_keeps tk (by decide)) hi) fun u ⟨um, uk⟩ => ?_
  refine ⟨?_, tk.trans (uk.mono ?_)⟩
  · rw [um, tv, tm]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide

end VG.Proof.X448.AArch64

end

end

/-!
# X448 on AArch64: all input-coordinate bytes

Eight limb pairs fill the two coordinate slots. The input lies outside the
writable working space.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- Equal input bytes give equal seven-byte chunks. -/
theorem chunk_congr {m m' : Mem} {p : Addr} {i : Nat} (hi : i < 8)
    (h : ∀ j < 56, m' (off p j) = m (off p j)) : chunk m' p i = chunk m p i := by
  apply congrArg VG.Proof.X25519.leNum
  simp only [Spec.X448.bytesAt]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  rw [Offset.add_add]
  exact h _ (by omega_using [hi, hj])

theorem decodeAll_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .x2 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block ((List.range 8).flatMap decodePair)) s fun t =>
      (∀ j < 16, limbs t.mem base X1 j = decoded s.mem p j) ∧
      (∀ j < 16, limbs t.mem base X3 j = decoded s.mem p j) ∧
      Outside2 base X1 128 X3 128 s.mem t.mem ∧ Keeps [.x4, .x5, .x7, .x8] s t := by
  let inv := fun n (t : State) =>
    (∀ j < 2 * n, limbs t.mem base X1 j = decoded s.mem p j) ∧
    (∀ j < 2 * n, limbs t.mem base X3 j = decoded s.mem p j) ∧
    Outside2 base X1 (16 * n) X3 (16 * n) s.mem t.mem ∧ Keeps [.x4, .x5, .x7, .x8] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (decodePair n)) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tp := (tk.1 .x2 (by decide)).trans hp
    have tr : ∀ j < 7, InRegions (t.rd ++ t.wr) (off p (7 * n + j)) 1 := by
      intro j hj; rw [tk.2.1, tk.2.2]; exact hr _ (by omega_using [hn, hj])
    have byte : ∀ j < 56, t.mem (off p j) = s.mem (off p j) := by
      intro j hj
      have h := hd j hj
      exact tm _ (Or.inr (by simp only [X1, slot]; omega_using [hn, h])) (Or.inr (by simp only [X3, slot]; omega_using [hn, h]))
    have chunkEq := chunk_congr hn byte
    refine WP.mono (decodePair_ok (hs.of_keeps tk (by decide)) hn tp tr) fun u ⟨um, uk⟩ => ?_
    rw [chunkEq] at um
    have pair := fun (j : Nat) (hj : j < 16) => pairMem_limbs t.mem base hn hj (chunk_lt s.mem p n)
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · intro j hj
      rw [um, (pair j (by omega_using [hn, hj])).1]
      by_cases h1 : j = 2 * n + 1
      · rw [ite_eq_left h1, h1, decoded_odd]
      · rw [ite_eq_right h1]
        by_cases h0 : j = 2 * n
        · rw [ite_eq_left h0, h0, decoded_even]
        · rw [ite_eq_right h0]; exact tx j (by omega_using [hj, h1, h0])
    · intro j hj
      rw [um, (pair j (by omega_using [hn, hj])).2]
      by_cases h1 : j = 2 * n + 1
      · rw [ite_eq_left h1, h1, decoded_odd]
      · rw [ite_eq_right h1]
        by_cases h0 : j = 2 * n
        · rw [ite_eq_left h0, h0, decoded_even]
        · rw [ite_eq_right h0]; exact ty j (by omega_using [hj, h1, h0])
    · rw [um]
      exact (tm.mono (by omega_using []) (by omega_using [])).trans (pairMem_outside _ _ hn _)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, fun _ hj => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64

end

end

/-!
# X448 on AArch64: reading the arguments

Setup saves the two callee-saved registers, decodes the coordinate, and
initializes the ladder.
-/

@[expose] public section

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

def Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  word m base 0 = g .x19 ∧ word m base 8 = g .x20

theorem Saved.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved base g m)
    {o n : Nat} (ho : Outside base o n m m') (h16 : 16 ≤ o) : Saved base g m' :=
  ⟨(ho.word (Or.inl (by omega_using [h16])) (by decide)).trans h.1,
    (ho.word (Or.inl h16) (by decide)).trans h.2⟩

theorem Saved.outside2 {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved base g m)
    {x nx y ny : Nat} (ho : Outside2 base x nx y ny m m') (hx : 16 ≤ x) (hy : 16 ≤ y) :
    Saved base g m' :=
  ⟨(ho.word (Or.inl (by omega_using [hx])) (Or.inl (by omega_using [hy])) (by decide)).trans h.1,
    (ho.word (Or.inl hx) (Or.inl hy) (by decide)).trans h.2⟩

def setupHead : List Instr :=
  [st .x19 0, st .x20 8, .addImm .x .x20 .x0 0,
    .movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1]

theorem setupHead_ok {s : State} {base : Addr} (hc : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block setupHead) s fun t =>
      Scr t base ∧ t.gpr .x20 = s.gpr .x0 ∧ t.gpr .x2 = s.gpr .x2 ∧
      Saved base s.gpr t.mem ∧ Outside base 0 16 s.mem t.mem ∧ Keeps [.x20, .x12] s t := by
  have w : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun _ hd => ⟨_, hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [setupHead, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, State.read, State.store, hc, w 0 (by decide), w 8 (by decide),
    Nat.reduceMod, Nat.reduceLT, Nat.reduceMul, and_self, BitVec.setWidth_eq,
    BitVec.shiftLeft_zero, RegUpd.gpr_write,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, write8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨hc, ?_, hw, hn⟩, BitVec.add_zero _, trivial, ?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [RegUpd.gpr_write_self]; decide
  · change Saved base s.gpr ((s.mem.writeW (off base 0) (s.gpr .x19)).writeW (off base 8) (s.gpr .x20))
    constructor
    · rw [word_write_aligned _ base (by decide) (by decide) (by decide) (by decide),
        ite_eq_right (by decide)]
      exact Mem.readW_writeW_self64 _ _ _
    · exact Mem.readW_writeW_self64 _ _ _
  · exact ((writeW_outside s.mem base _ (d := 0) (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ base _ (d := 8) (by decide)).mono (by decide) (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

def setupRegs : List Reg := [.x4, .x5, .x7, .x8, .x20, .x12]

theorem setup_ok {s : State} {base p : Addr} (hc : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hp : s.gpr .x2 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block setup) s fun t =>
      Scr t base ∧ BoundedEnv t.mem base ∧ t.gpr .x20 = s.gpr .x0 ∧ Keeps setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ Saved base s.gpr t.mem ∧
      E t.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      E t.mem base 1 = 1 ∧ E t.mem base 2 = 0 ∧
      E t.mem base 3 = E t.mem base 0 ∧ E t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 := by
  change WP isa (.block (setupHead ++ ((List.range 8).flatMap decodePair ++ initSlots))) s _
  rw [WP.block_append_iff]
  refine WP.mono (setupHead_ok hc hw hn) fun t ⟨ts, tp, tr, tv, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decodeAll_ok ts (tr.trans hp)
    (by intro j hj; rw [tk.2.1, tk.2.2]; exact hr j hj) hd) fun u ⟨ux, uy, um, uk⟩ => ?_
  have ub0 : Bounded u.mem base X1 := by intro j hj; rw [ux j hj]; exact decoded_bound _ _ _
  have ub3 : Bounded u.mem base X3 := by intro j hj; rw [uy j hj]; exact decoded_bound _ _ _
  have uv0 : E u.mem base 0 = toFe (VG.Proof.X25519.leNum (Spec.X448.bytesAt t.mem p 56)) := by
    apply congrArg toFe
    exact (valN_congr ux).trans (decoded_val t.mem p 8)
  have uv3 : E u.mem base 3 = E u.mem base 0 := congrArg toFe ((valN_congr uy).trans (valN_congr ux).symm)
  have byte : Spec.X448.bytesAt t.mem p 56 = Spec.X448.bytesAt s.mem p 56 := by
    apply List.map_congr_left
    intro j hj
    exact tm _ (Or.inr (Nat.le_trans (by decide) (hd j (List.mem_range.mp hj))))
  rw [byte] at uv0
  refine WP.mono (initSlots_ok (ts.of_keeps uk (by decide)) ub0 ub3)
    fun v ⟨vb, v0, v1, v2, v3, v4, vw, vm, vk⟩ => ?_
  refine ⟨(ts.of_keeps uk (by decide)).of_keeps vk (by decide), vb,
    (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tp),
    (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_)),
    (tm.mono (by decide) (by decide)).trans ?_,
    (tv.outside2 um (by decide) (by decide)).outside vm (by decide),
    ?_, v1, v2, v3.trans (uv3.trans v0.symm), v4, vw⟩
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> decide
  · intro r h; simp only [List.mem_singleton] at h; subst r; decide
  · exact (show Outside base 0 8192 t.mem u.mem from fun q h =>
      um q (by simp only [X1, slot]; omega_using [h]) (by simp only [X3, slot]; omega_using [h])).trans
      (vm.mono (by decide) (by decide))
  · rw [decodeUCoordinate_eq (length_bytesAt _ _ _)]
    exact v0.trans uv0

end VG.Proof.X448.AArch64
