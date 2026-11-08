module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Rc2.PPC64LE.Lookup
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-!
# RC2 on PPC64LE: the scan of a table

`vscan_run`: the scan of a table of four or eight 32-byte chunks leaves in
`r11` its byte, or two bytes, at the offset in `r10`. Vectors are reasoned
about a byte at a time (`vbyte`).
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

theorem read_sixteen (m : Mem) (a : Addr) : m.read a 16 = m.readW a 128 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

/-- The address of chunk `i` of the table at `T`, as the code makes it. -/
def ch (T : Addr) : Nat → Addr
  | 0 => T
  | i + 1 => ch T i + 32#64

theorem ch_eq (T : Addr) : ∀ i, ch T i = T + BitVec.ofNat 64 (32 * i)
  | 0 => by simp [ch]
  | i + 1 => by
    rw [ch, ch_eq T i, show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, Offset.add_add]; congr 2

/-! ## Bytes -/

theorem vbyte_and (a b : BitVec 128) (i : Nat) : vbyte (a &&& b) i = vbyte a i &&& vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr; simp [vbyte, hr]

theorem vbyte_or (a b : BitVec 128) (i : Nat) : vbyte (a ||| b) i = vbyte a i ||| vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr; simp [vbyte, hr]

theorem vbyte_not0 (a : BitVec 128) : vbyte (~~~a) 0 = ~~~vbyte a 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp [vbyte, hr, show 8 * (15 - 0) + r < 128 by omega]

theorem vbyte_not1 (a : BitVec 128) : vbyte (~~~a) 1 = ~~~vbyte a 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp [vbyte, hr, show 8 * (15 - 1) + r < 128 by omega]

/-- Byte `i` (of the first eight) of a vector, from its first doubleword. -/
theorem vbyte_hi (x u : BitVec 64) {i : Nat} (hi : i < 8) : vbyte (x ++ u) i = x.extractLsb' (8 * (7 - i)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hr, decide_true, Bool.true_and,
    show ¬ 8 * (15 - i) + r < 64 by omega, ite_false]
  exact congrArg x.getLsbD (by omega)

/-- `0 - ((q << (63 - c)) >> 63)`: all ones if bit `c` of `q` is set. -/
theorem bitMask_eq (q : BitVec 64) {c : Nat} (hc : c < 64) :
    0#64 - (q <<< (63 - c)) >>> 63 = if q.getLsbD c then BitVec.allOnes 64 else 0 := by
  have e : (q <<< (63 - c)) >>> 63 = if q.getLsbD c then 1#64 else 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    by_cases h0 : i = 0
    · subst h0
      simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
        show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
        show ¬ (63 < 63 - c) by omega, decide_false, Bool.not_false,
        show 63 - (63 - c) = c by omega]
      cases q.getLsbD c <;> rfl
    · have : (q <<< (63 - c) >>> 63).getLsbD i = false := by
        simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
        simp only [show ¬ (63 + i < 64) by omega, decide_false, Bool.false_and]
      rw [this]
      cases q.getLsbD c
      · simp
      · simp [h0]
  rw [e]
  cases q.getLsbD c <;> decide

/-- A mask's bytes. -/
theorem vbyte_mask (q u : BitVec 64) {c i : Nat} (hc : c < 64) (hi : i < 8) :
    vbyte ((0#64 - (q <<< (63 - c)) >>> 63) ++ u) i = if q.getLsbD c then 255#8 else 0#8 := by
  rw [vbyte_hi _ _ hi, bitMask_eq _ hc]
  cases q.getLsbD c
  · simp
  · have : ∀ i < 8, (BitVec.allOnes 64).extractLsb' (8 * (7 - i)) 8 = 255#8 := by decide
    exact this i hi

theorem sel8 (a b : Byte) (c : Bool) :
    (a &&& ~~~(if c then 255#8 else 0#8)) ||| (b &&& (if c then 255#8 else 0#8)) = if c then b else a := by
  cases c
  · simp only [Bool.false_eq_true, ite_false, show ~~~(0#8 : Byte) = BitVec.allOnes 8 by decide,
      BitVec.and_allOnes, BitVec.and_zero, BitVec.or_zero]
  · simp only [ite_true, show (255#8 : Byte) = BitVec.allOnes 8 by decide, BitVec.not_allOnes, BitVec.and_zero,
      BitVec.zero_or, BitVec.and_allOnes]

theorem vbyte_load (m : Mem) (a : Addr) {k : Nat} (hk : k < 16) :
    vbyte (swapDwords (m.readW a 128)) k = m (a + BitVec.ofNat 64 (k ^^^ 7)) := by
  have e : ∀ k < 16, 15 - (if k < 8 then k + 8 else k - 8) = k ^^^ 7 := by decide
  rw [vbyte_swapDwords _ hk, vbyte, Mem.readW, BitVec.setWidth_eq, ← e k hk]
  exact Mem.extractLsb'_read m a (n := 16) (by split <;> omega)

/-- `vperm`'s byte `x XOR 7` of a 32-byte chunk loaded by `lxvd2x`: its byte
`x`. -/
theorem pick (m : Mem) (a : Addr) {x : Nat} (hx : x < 32) :
    (if (x ^^^ 7) < 16 then vbyte (swapDwords (m.readW a 128)) (x ^^^ 7)
      else vbyte (swapDwords (m.readW (a + 16#64) 128)) ((x ^^^ 7) - 16)) = m (a + BitVec.ofNat 64 x) := by
  have lo : ∀ x < 16, (x ^^^ 7) < 16 ∧ (x ^^^ 7) ^^^ 7 = x := by decide
  have hi : ∀ x < 32, 16 ≤ x → ¬ (x ^^^ 7) < 16 ∧ (x ^^^ 7) - 16 < 16 ∧ 16 + (((x ^^^ 7) - 16) ^^^ 7) = x := by
    decide
  by_cases h : x < 16
  · obtain ⟨l1, l2⟩ := lo x h
    rw [ite_eq_left l1, vbyte_load _ _ l1, l2]
  · obtain ⟨l1, l2, l3⟩ := hi x hx (by omega)
    rw [ite_eq_right l1, vbyte_load _ _ l2, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add, l3]

/-- Bytes 0 and 1 of a vector, from the GPR `mfvsrd` makes of it. -/
theorem top0 (X : BitVec 128) : vdword X 0 >>> 56 = (vbyte X 0).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, vbyte, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp [h, show 56 + i < 64 by omega, show i < 64 by omega]; congr 1; omega
  · simp [h, show ¬ 56 + i < 64 by omega]

theorem top1 (X : BitVec 128) : (vdword X 0 <<< 8) >>> 56 = (vbyte X 1).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, vbyte, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp [h, show 56 + i < 64 by omega, show ¬ 56 + i < 8 by omega, show i < 64 by omega]
    rw [decide_eq_true (show 56 + i - 8 < 64 by omega), Bool.true_and]
    exact congrArg X.getLsbD (by omega)
  · simp [h, show ¬ 56 + i < 64 by omega]

theorem xor7_mod (x : Byte) : (x ^^^ 7#8).toNat % 32 = (x.toNat % 32) ^^^ 7 := by
  have : ∀ x : Byte, (x ^^^ 7#8).toNat % 32 = (x.toNat % 32) ^^^ 7 := by decide
  exact this x

theorem ctl0 (x : BitVec 64) : (x <<< 56).extractLsb' (8 * (7 - 0)) 8 = x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show 56 + i < 64 by omega, show i < 64 by omega]

/-- The chunk the bits 5, 6 and 7 of `q` name. -/
theorem tree_sel {α : Type} (e : Nat → α) (q : BitVec 64) :
    (if q.getLsbD 7 then (if q.getLsbD 6 then (if q.getLsbD 5 then e 7 else e 6) else
        (if q.getLsbD 5 then e 5 else e 4)) else
      (if q.getLsbD 6 then (if q.getLsbD 5 then e 3 else e 2) else (if q.getLsbD 5 then e 1 else e 0))) =
      e (q.toNat / 32 % 8) := by
  have tb : ∀ b < 3, q.getLsbD (5 + b) = (q.toNat / 32 % 8).testBit b := fun b hb => by
    rw [BitVec.getLsbD, show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_mod_two_pow, show (32 : Nat) = 2 ^ 5 from rfl,
      Nat.testBit_div_two_pow]
    simp [hb, Nat.add_comm]
  rw [show (7 : Nat) = 5 + 2 from rfl, show (6 : Nat) = 5 + 1 from rfl, show (5 : Nat) = 5 + 0 from rfl,
    tb 0 (by decide), tb 1 (by decide), tb 2 (by decide)]
  have : q.toNat / 32 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize q.toNat / 32 % 8 = r at this ⊢
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem tree_sel4 {α : Type} (e : Nat → α) (q : BitVec 64) :
    (if q.getLsbD 6 then (if q.getLsbD 5 then e 3 else e 2) else (if q.getLsbD 5 then e 1 else e 0)) =
      e (q.toNat / 32 % 4) := by
  have tb : ∀ b < 2, q.getLsbD (5 + b) = (q.toNat / 32 % 4).testBit b := fun b hb => by
    rw [BitVec.getLsbD, show (4 : Nat) = 2 ^ 2 from rfl, Nat.testBit_mod_two_pow, show (32 : Nat) = 2 ^ 5 from rfl,
      Nat.testBit_div_two_pow]
    simp [hb, Nat.add_comm]
  rw [show (6 : Nat) = 5 + 1 from rfl, show (5 : Nat) = 5 + 0 from rfl, tb 0 (by decide), tb 1 (by decide)]
  have : q.toNat / 32 % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize q.toNat / 32 % 4 = r at this ⊢
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> rfl

/-! ## The scans -/

/-- The byte scan of PITABLE (eight chunks). -/
theorem piScan_run (s : State) {T : Addr} (h7 : s.gpr .r7 = T) (hq : (s.gpr .r10).toNat < 256)
    (hr : ∀ i < 8, InRegions (s.rd ++ s.wr) (ch T i) 16 ∧ InRegions (s.rd ++ s.wr) (ch T i + 16#64) 16) :
    WP isa (.block (vscan .r7 .r15 true false)) s fun t =>
      t.gpr .r11 = (s.mem (T + s.gpr .r10)).setWidth 64 ∧ t.mem = s.mem := by
  have a0 := hr 0 (by decide); have a1 := hr 1 (by decide); have a2 := hr 2 (by decide)
  have a3 := hr 3 (by decide); have a4 := hr 4 (by decide); have a5 := hr 5 (by decide)
  have a6 := hr 6 (by decide); have a7 := hr 7 (by decide)
  simp only [ch] at a0 a1 a2 a3 a4 a5 a6 a7
  unfold vscan ctl bitMask chunk choose
  rrun [reduceVOpEval, vCtl, vBit, vLo, vHi, vPick, vpr_writeV, gpr_writeV, mem_writeV, rd_writeV, wr_writeV,
    ↓read_sixteen, addrX, BitVec.or_self, h7, a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2,
    a5.1, a5.2, a6.1, a6.2, a7.1, a7.2]
  generalize hx : (s.gpr .r10).toNat = x at hq
  have hc : ((s.gpr .r10 ^^^ 7#64).setWidth 8).toNat % 32 = (x % 32) ^^^ 7 := by
    rw [show (s.gpr .r10 ^^^ 7#64).setWidth 8 = (s.gpr .r10).setWidth 8 ^^^ 7#8 by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi], xor7_mod, BitVec.toNat_setWidth, hx,
      Nat.mod_eq_of_lt (show x < 2 ^ 8 by omega)]
  rw [top0]
  simp only [vbyte_or, vbyte_and, vbyte_not0, vbyte_mask _ _ (show 5 < 64 by decide) (show 0 < 8 by decide),
    vbyte_mask _ _ (show 6 < 64 by decide) (show 0 < 8 by decide),
    vbyte_mask _ _ (show 7 < 64 by decide) (show 0 < 8 by decide), sel8, vbyte_packed _ (show 0 < 16 by decide),
    vbyte_hi _ _ (show 0 < 8 by decide), ctl0, hc]
  have hx32 : x % 32 < 32 := Nat.mod_lt _ (by decide)
  refine (congrArg (BitVec.setWidth 64) (tree_sel (fun t =>
    if x % 32 ^^^ 7 < 16 then vbyte (swapDwords (s.mem.readW (ch T t) 128)) (x % 32 ^^^ 7)
    else vbyte (swapDwords (s.mem.readW (ch T t + 16#64) 128)) ((x % 32 ^^^ 7) - 16)) (s.gpr .r10))).trans ?_
  rw [pick _ _ hx32, ch_eq, Offset.add_add, hx, show 32 * (x / 32 % 8) + x % 32 = x by omega,
    ← hx, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ctl_lo (x y : BitVec 64) :
    (x <<< 56 ||| y <<< 56 >>> 8).extractLsb' (8 * (7 - 0)) 8 = x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show 56 + i < 64 by omega, show i < 64 by omega, show ¬ 56 + i < 56 by omega]
  intro _; omega

theorem ctl_hi (x y : BitVec 64) :
    (x <<< 56 ||| y <<< 56 >>> 8).extractLsb' (8 * (7 - 1)) 8 = y.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show 48 + i < 64 by omega, show i < 64 by omega, show 48 + i < 56 by omega,
    show 8 + (48 + i) < 64 by omega, show 8 + (48 + i) - 56 = i by omega]
  intro _; omega

/-- The two-byte scan of the schedule (four chunks), at an even offset. -/
theorem keyScan_run (s : State) {T : Addr} (h3 : s.gpr .r3 = T) (hq : (s.gpr .r10).toNat < 128)
    (he : (s.gpr .r10).toNat % 2 = 0)
    (hr : ∀ i < 4, InRegions (s.rd ++ s.wr) (ch T i) 16 ∧ InRegions (s.rd ++ s.wr) (ch T i + 16#64) 16) :
    WP isa (.block (vscan .r3 .r5 false true)) s fun t =>
      t.gpr .r11 = (s.mem (T + s.gpr .r10)).setWidth 64 |||
        (s.mem (T + s.gpr .r10 + 1#64)).setWidth 64 <<< 8 ∧ t.mem = s.mem := by
  have a0 := hr 0 (by decide); have a1 := hr 1 (by decide); have a2 := hr 2 (by decide)
  have a3 := hr 3 (by decide)
  simp only [ch] at a0 a1 a2 a3
  unfold vscan ctl bitMask chunk choose
  rrun [reduceVOpEval, vCtl, vBit, vLo, vHi, vPick, vpr_writeV, gpr_writeV, mem_writeV, rd_writeV, wr_writeV,
    ↓read_sixteen, addrX, BitVec.or_self, h3, a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  generalize hx : (s.gpr .r10).toNat = x at hq he
  have x7 : ∀ y : BitVec 64, ∀ z : Nat, y.toNat = z → z < 256 → ((y ^^^ 7#64).setWidth 8).toNat % 32 = (z % 32) ^^^ 7 :=
    fun y z hy hz => by
      rw [show (y ^^^ 7#64).setWidth 8 = y.setWidth 8 ^^^ 7#8 by
        apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi], xor7_mod, BitVec.toNat_setWidth, hy,
        Nat.mod_eq_of_lt (show z < 2 ^ 8 by omega)]
  have h1 : (s.gpr .r10 + 1#64).toNat = x + 1 := by
    rw [BitVec.toNat_add, hx]; simp; omega
  rw [top0, top1]
  simp only [vbyte_or, vbyte_and, vbyte_not0, vbyte_not1,
    vbyte_mask _ _ (show 5 < 64 by decide) (show 0 < 8 by decide),
    vbyte_mask _ _ (show 6 < 64 by decide) (show 0 < 8 by decide),
    vbyte_mask _ _ (show 5 < 64 by decide) (show 1 < 8 by decide),
    vbyte_mask _ _ (show 6 < 64 by decide) (show 1 < 8 by decide), sel8,
    vbyte_packed _ (show 0 < 16 by decide), vbyte_packed _ (show 1 < 16 by decide),
    vbyte_hi _ _ (show 0 < 8 by decide), vbyte_hi _ _ (show 1 < 8 by decide), ctl_lo, ctl_hi,
    x7 _ _ hx (by omega), x7 _ _ h1 (by omega)]
  have hx32 : x % 32 < 32 := Nat.mod_lt _ (by decide)
  have hx1 : (x + 1) % 32 = x % 32 + 1 := by omega
  rw [hx1]
  have hl : x / 32 % 4 = x / 32 := by omega
  have t0 := tree_sel4 (fun t =>
    if x % 32 ^^^ 7 < 16 then vbyte (swapDwords (s.mem.readW (ch T t) 128)) (x % 32 ^^^ 7)
    else vbyte (swapDwords (s.mem.readW (ch T t + 16#64) 128)) ((x % 32 ^^^ 7) - 16)) (s.gpr .r10)
  have t1 := tree_sel4 (fun t =>
    if (x % 32 + 1) ^^^ 7 < 16 then vbyte (swapDwords (s.mem.readW (ch T t) 128)) ((x % 32 + 1) ^^^ 7)
    else vbyte (swapDwords (s.mem.readW (ch T t + 16#64) 128)) (((x % 32 + 1) ^^^ 7) - 16)) (s.gpr .r10)
  simp only [ch] at t0 t1
  rw [t0, t1, pick _ _ hx32, pick _ _ (show x % 32 + 1 < 32 by omega), ch_eq, Offset.add_add, Offset.add_add, hx, hl,
    show 32 * (x / 32) + x % 32 = x by omega, show 32 * (x / 32) + (x % 32 + 1) = x + 1 by omega]
  have e : s.gpr .r10 = BitVec.ofNat 64 x := by rw [← hx, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [e, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.add_add]

end VG.Proof.Rc2.PPC64LE
