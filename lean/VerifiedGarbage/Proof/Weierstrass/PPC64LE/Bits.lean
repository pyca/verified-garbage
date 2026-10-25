module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Loop
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Short Weierstrass curves on PPC64LE: tables of bits, and masks of bits

`bits src dst (8 n)` writes the bits of the `n`-word number at `src`, one byte
each, to the table at `dst` (`bits_ok`): a loop over its bytes, from the top
one down, each giving eight bytes of the table (`bitsBody_ok`). `bitMask d`
makes the mask `r10` of the byte `r31` of the table at `d` (`bitMask_ok`):
all ones for a 1, zero for a 0 (`bitMask_bool_ok`). As on 32-bit ARM
(`Proof/Weierstrass/Arm/Bits.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE

/-! ## Bytes through a register -/

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega_arith, dite_true]

/-- `lbz t, d(r)` with `r` at `K` bytes into the working space. -/
theorem lbz_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t r : Reg} {K d : Nat}
    (hr : At s base r K) (hr0 : r ≠ .r0) (hd : K + d + 1 ≤ size) :
    exec (.lbz t r d) s = some (s.write t ((s.mem (off base (K + d))).setWidth 64)) := by
  have hs15 := hs.small
  rw [exec_lbz hr0 (by omega_arith) (by rw [hr, off_add]; exact hs.read hd), hr, off_add, read_one]

/-- `stb t, d(r)` with `r` at `K` bytes into the working space. -/
theorem stb_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t r : Reg} {K d : Nat}
    (hr : At s base r K) (hr0 : r ≠ .r0) (hd : K + d + 1 ≤ size) :
    exec (.stb t r d) s =
      some { s with mem := s.mem.writeW (off base (K + d)) ((s.gpr t).setWidth 8 : BitVec 8) } := by
  have hs15 := hs.small
  rw [exec_stb hr0 (by omega_arith) (by rw [hr, off_add]; exact hs.wrIn hd), hr, off_add]
  rfl

/-- `d = r3 + r` for `r = k`, with `r3` the working space's base. -/
theorem add_at {s : State} {base : Addr} {r : Reg} {k : Nat} (h3 : At s base .r3 0)
    (hr : s.gpr r = BitVec.ofNat 64 k) : s.gpr .r3 + s.gpr r = off base k := by
  rw [h3, hr, off_add, Nat.zero_add]

/-! ## Masks -/

/-- `r10 = -[r3 + r31 + d]`, the byte zero-extended. -/
theorem bitMask_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {d t : Nat} (ht : s.gpr .r31 = BitVec.ofNat 64 t) (hd : t + d + 1 ≤ size) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .r10 = 0 - (s.mem (off base (d + t))).setWidth 64 ∧ Kp [.r4, .r5, .r10] s s' ∧
        s'.mem = s.mem := by
  simp only [bitMask]
  refine wp_step exec_add ?_
  have a₁ : At (s.write .r4 (s.gpr .r3 + s.gpr .r31)) base .r4 t := by
    show s.gpr .r3 + s.gpr .r31 = _
    exact add_at h3 ht
  refine wp_step (lbz_ok (hs.write _ _) a₁ (by decide) hd) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub (WP.block_nil ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩)
  · simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
    rw [Nat.add_comm d t]; rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false]

theorem neg_bit (c : Bool) :
    0 - ((if c then 1 else 0 : BitVec 8)).setWidth 64 = (if c then BitVec.allOnes 64 else 0) := by
  cases c <;> decide

/-- The mask of a byte that is 0 or 1. -/
theorem bitMask_bool_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {d t : Nat} (ht : s.gpr .r31 = BitVec.ofNat 64 t) (hd : t + d + 1 ≤ size) {c : Bool}
    (hc : s.mem (off base (d + t)) = if c then 1 else 0) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .r10 = (if c then BitVec.allOnes 64 else 0) ∧ Kp [.r4, .r5, .r10] s s' ∧ s'.mem = s.mem :=
  WP.mono (bitMask_ok hs h3 ht hd) fun _ ⟨e, k, m⟩ => ⟨by rw [e, hc, neg_bit], k, m⟩

/-! ## The table of bits -/

/-- The body of `bits`' loop. -/
def bitsBody (src dst : Nat) : List Instr :=
  [decCounter, .add .r4 wb .r31, .lbz .r4 .r4 src, .lsl .r5 .r31 3, .add .r5 wb .r5, .li .r7 1] ++
    (List.range 8).flatMap (bitJ dst)

theorem bits_eq (src dst nbytes : Nat) :
    bits src dst nbytes = .seq (.block [.li .r31 nbytes]) (.loop (.block (bitsBody src dst)) more) :=
  rfl

theorem bit_byte (b : BitVec 8) (j : Nat) :
    ((((b.setWidth 64 >>> j) &&& BitVec.ofNat 64 1).setWidth 8) : BitVec 8) = if b.getLsbD j then 1 else 0 :=
  bitByte_getLsbD 64 (by decide) b j

theorem bit_byte0 (b : BitVec 8) :
    (((b.setWidth 64 &&& BitVec.ofNat 64 1).setWidth 8) : BitVec 8) = if b.getLsbD 0 then 1 else 0 := by
  rw [← BitVec.ushiftRight_zero (b.setWidth 64)]; exact bit_byte b 0

/-- What `bitJ` keeps. -/
abbrev bitClob : List Reg := [.r6]

/-- Byte `j` of the eight at `r5 + dst`: bit `j` of the byte in `r4`. -/
theorem bitJ_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {i : Nat}
    {dst : Nat} (hb : At s base .r5 (8 * i)) {b : BitVec 8}
    (ha : s.gpr .r4 = b.setWidth 64) (h7 : s.gpr .r7 = BitVec.ofNat 64 1) {j : Nat} (hj : j < 8)
    (hd : dst + (8 * i + j) + 1 ≤ size) :
    WP isa (.block (bitJ dst j)) s fun s' => Kp bitClob s s' ∧
      s'.mem = s.mem.writeW (off base (dst + (8 * i + j))) (if b.getLsbD j then 1 else 0 : BitVec 8) := by
  have e : 8 * i + (dst + j) = dst + (8 * i + j) := by omega_arith
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [bitJ, ite_true, List.cons_append, List.nil_append]
    refine wp_step exec_logic ?_
    refine wp_step (stb_ok (hs.write _ _) (hb.write _) (by decide) (by omega_arith)) (WP.block_nil ?_)
    simp only [write_gpr, ite_true]
    refine ⟨(Kp.write s _ (by decide)).trans (Kp.store _ _ _), ?_⟩
    simp only [write_mem]
    rw [e, ha, h7, bit_byte0]
  · simp only [bitJ, show ¬j = 0 by omega_arith, ite_false, List.cons_append, List.nil_append]
    refine wp_step (exec_lsr_d (by omega_arith)) ?_
    refine wp_step exec_logic ?_
    refine wp_step (stb_ok ((hs.write _ _).write _ _) ((hb.write _).write _) (by decide) (by omega_arith))
      (WP.block_nil ?_)
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    refine ⟨((Kp.write s _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.store _ _ _), ?_⟩
    simp only [write_mem]
    rw [e, ha, h7, bit_byte]

/-- The first `k` bits of the byte in `r4`. -/
theorem bitJs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    {i dst : Nat} (hb : At s base .r5 (8 * i)) {b : BitVec 8}
    (ha : s.gpr .r4 = b.setWidth 64) (h7 : s.gpr .r7 = BitVec.ofNat 64 1) (hd : dst + 8 * i + 8 ≤ size) :
    ∀ k ≤ 8,
    WP isa (.block ((List.range k).flatMap (bitJ dst))) s fun s' => Kp bitClob s s' ∧
      (∀ j < k, s'.mem (off base (dst + (8 * i + j))) = if b.getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) k s.mem s'.mem
  | 0, _ => WP.block_nil ⟨Kp.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine wp_append (WP.mono (bitJs_ok hs hb ha h7 hd k (by omega_arith)) fun s₁ ⟨k₁, e₁, O₁⟩ => ?_)
    refine WP.mono (bitJ_ok (k₁.ws hs) (k₁.at hb) (b := b) (by rw [k₁.g]; exact ha) (by rw [k₁.g]; exact h7)
      (j := k) (by omega_arith) (by omega_arith)) fun s₂ ⟨k₂, m₂⟩ => ?_
    have O₂ : Outside base (dst + (8 * i + k)) 1 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW8_outside _ _ _ (by omega_arith)
    refine ⟨k₁.trans k₂, fun j hj => ?_,
      (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂ _ (by rw [ofs_off0 base (d := dst + (8 * i + j)) (by omega_arith)]; omega_arith), e₁ j h]
    · obtain rfl : j = k := by omega_arith
      rw [m₂, writeW8_self]

theorem shl3 (i : Nat) : BitVec.ofNat 64 i <<< 3 = BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]
  congr 1; omega_arith

/-- What the loop of `bits` changes. -/
abbrev bitsClob : List Reg := [.r4, .r5, .r6, .r7, .r31]

/-- One byte of the number at `src`, the one below `r31 = i + 1`: its bits to
the table at `dst`. -/
theorem bitsBody_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {src dst i : Nat} (ht : s.gpr .r31 = BitVec.ofNat 64 (i + 1))
    (hsrc : i + src + 1 ≤ size) (hd : dst + 8 * i + 8 ≤ size) :
    WP isa (.block (bitsBody src dst)) s fun s' =>
      s'.gpr .r31 = BitVec.ofNat 64 i ∧ Kp bitsClob s s' ∧
      (∀ j < 8, s'.mem (off base (dst + (8 * i + j))) =
        if (s.mem (off base (src + i))).getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) 8 s.mem s'.mem := by
  have hs15 := hs.small
  simp only [bitsBody, List.cons_append]
  refine wp_decCounter (j := i + 1) (by omega_arith) ht ?_
  rw [Nat.add_sub_cancel]
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 i) = s₁
  have K₁ : Kp bitsClob s s₁ := by rw [← hs₁]; exact Kp.write s _ (by decide)
  have c₁ : s₁.gpr .r31 = BitVec.ofNat 64 i := by rw [← hs₁]; simp only [write_gpr, ite_true]
  have h3₁ := K₁.at h3
  refine wp_step exec_add ?_
  have a₂ : At (s₁.write .r4 (s₁.gpr .r3 + s₁.gpr .r31)) base .r4 i := by
    show s₁.gpr .r3 + s₁.gpr .r31 = _
    exact add_at h3₁ c₁
  refine wp_step (lbz_ok (K₁.ws hs |>.write _ _) a₂ (by decide) hsrc) ?_
  refine wp_step (exec_lsl (by decide)) ?_
  refine wp_step exec_add ?_
  refine wp_step (exec_li (by decide)) ?_
  generalize hs₂ : ((((s₁.write .r4 (s₁.gpr .r3 + s₁.gpr .r31)).write .r4 _).write .r5 _).write .r5 _).write
    .r7 (BitVec.ofNat 64 1) = s₂
  have K₂ : Kp bitsClob s₁ s₂ := by
    rw [← hs₂]
    exact ((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))
  have m₂ : s₂.mem = s.mem := by rw [← hs₂, ← hs₁]; rfl
  have r4₂ : s₂.gpr .r4 = (s.mem (off base (src + i))).setWidth 64 := by
    rw [← hs₂]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true, write_mem]
    rw [← hs₁, Nat.add_comm i src]; rfl
  have r7₂ : s₂.gpr .r7 = BitVec.ofNat 64 1 := by rw [← hs₂]; simp only [write_gpr, ite_true]
  have r5₂ : At s₂ base .r5 (8 * i) := by
    rw [← hs₂]; simp only [At, write_gpr, reduceCtorEq, ite_false, ite_true]
    rw [c₁, shl3 i, h3₁, off_add, Nat.zero_add]
  have c₂ : s₂.gpr .r31 = BitVec.ofNat 64 i := by
    rw [← hs₂]; simp only [write_gpr, reduceCtorEq, ite_false]; exact c₁
  refine WP.mono (bitJs_ok (K₂.ws (K₁.ws hs)) r5₂ r4₂ r7₂ hd 8 (Nat.le_refl _)) fun s₃ ⟨k₃, e₃, O₃⟩ =>
    ⟨by rw [k₃.g, c₂], (K₁.trans K₂).trans (k₃.mono), e₃, by rw [← m₂]; exact O₃⟩

/-- `bits`' loop invariant, at `r31 = i`: the bytes from `i` up are done. -/
structure BInv (base : Addr) (size src dst n : Nat) (s₀ s : State) (i : Nat) : Prop where
  ws : Ws s base size
  r3 : At s base .r3 0
  r31 : s.gpr .r31 = BitVec.ofNat 64 i
  keep : Kp bitsClob s₀ s
  mem : Outside base dst (64 * n) s₀.mem s.mem
  bits : ∀ t, 8 * i ≤ t → t < 64 * n → s.mem (off base (dst + t)) =
    if (s₀.mem (off base (src + t / 8))).getLsbD (t % 8) then 1 else 0

/-- `bits src dst (8 n)`: byte `t` of the table at `dst` is bit `t` of the
`n`-word number at `src`. -/
theorem bits_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {n src dst : Nat} (hn0 : 0 < n) (hsrc : src + 8 * n ≤ size) (hdst : dst + 64 * n ≤ size)
    (hsep : src + 8 * n ≤ dst ∨ dst + 64 * n ≤ src) :
    WP isa (bits src dst (8 * n)) s fun s' =>
      (∀ t < 64 * n, s'.mem (off base (dst + t)) =
        if (wordsVal s.mem base src n).testBit t then 1 else 0) ∧
      Kp bitsClob s s' ∧ Outside base dst (64 * n) s.mem s'.mem := by
  have hnw := hs.nowrap
  have hs15 := hs.small
  rw [bits_eq]
  refine WP.seq (wp_step (exec_li (by omega_arith)) (WP.block_nil ?_))
  have h₁ : BInv base size src dst n s (s.write .r31 (BitVec.ofNat 64 (8 * n))) (8 * n) :=
    ⟨hs.write _ _, h3.write _, by simp only [write_gpr, ite_true], Kp.write s _ (by decide), Outside.refl _ _ _ _,
      fun t ht ht' => absurd ht' (by omega_arith)⟩
  refine countLoop_ok (Inv := fun j s' => BInv base size src dst n s s' j) (n := 8 * n)
    (fun j s' hb => hb.r31) (fun j s' h1 h2 hb => ?_) (fun s' hb => ⟨fun t ht => ?_, hb.keep, hb.mem⟩)
    (by omega_arith) (by omega_arith) h₁
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_arith⟩
    refine WP.mono (bitsBody_ok hb.ws hb.r3 hb.r31 (by omega_arith) (by omega_arith))
      fun s'' ⟨b', k', bits', O'⟩ => ?_
    have hbyte : s'.mem (off base (src + i)) = s.mem (off base (src + i)) :=
      hb.mem _ (by rw [ofs_off0 base (d := src + i) (by omega_arith)]; omega_arith)
    refine ⟨k'.ws hb.ws, k'.at hb.r3, by rw [b', Nat.add_sub_cancel], hb.keep.trans k',
      hb.mem.trans (O'.mono (by omega_arith) (by omega_arith)), fun t ht ht' => ?_⟩
    rcases Nat.lt_or_ge t (8 * (i + 1)) with h | h
    · have e := bits' (t - 8 * i) (by omega_arith)
      rw [show 8 * i + (t - 8 * i) = t by omega_arith, hbyte] at e
      rw [e, show t / 8 = i by omega_arith, show t % 8 = t - 8 * i by omega_arith]
    · rw [O' _ (by rw [ofs_off0 base (d := dst + t) (by omega_arith)]; omega_arith), hb.bits t (by omega_arith) ht']
  · rw [hb.bits t (by omega_arith) ht, show t = 8 * (t / 8) + t % 8 from (Nat.div_add_mod t 8).symm,
      VG.Proof.Weierstrass.testBit_byte s.mem base (a := src) (n := n) (by omega_arith) (Nat.mod_lt _ (by decide))]
    simp only [show (8 * (t / 8) + t % 8) / 8 = t / 8 by omega_arith, show (8 * (t / 8) + t % 8) % 8 = t % 8 by omega_arith]

end VG.Proof.Weierstrass.PPC64LE
