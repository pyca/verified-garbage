module

public import VerifiedGarbage.Impl.Rc4.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc4.Qword
import VerifiedGarbage.Proof.Rc4.Memory
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc4.Table
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! # RC4 on PPC64LE: the table lookup, 32 bytes at a time -/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Proof.Rc4

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp

theorem read_eight (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem write_eight (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

/-- Steps a block of the RC4 code, keeping loads of a doubleword as
`Mem.readW` and of a byte as the byte. -/
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic|
      crun [List.cons_append, List.nil_append, ↓read_one, ↓read_eight, write_eight, false_implies,
        $ls,*])

theorem flatMap_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = (List.range n).flatMap f ++ f n := by
  rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem low8 (x : BitVec 64) : (x <<< 56) >>> 56 = x &&& BitVec.ofNat 64 255 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem read_sixteen (m : Mem) (a : Addr) : m.read a 16 = m.readW a 128 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

/-! ## Bytes of vectors -/

theorem vbyte_and (a b : BitVec 128) (i : Nat) : vbyte (a &&& b) i = vbyte a i &&& vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr; simp [vbyte, hr]

theorem vbyte_or (a b : BitVec 128) (i : Nat) : vbyte (a ||| b) i = vbyte a i ||| vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr; simp [vbyte, hr]

theorem vbyte_xor (a b : BitVec 128) (i : Nat) : vbyte (a ^^^ b) i = vbyte a i ^^^ vbyte b i := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr; simp [vbyte, hr]

theorem vbyte_not0 (a : BitVec 128) : vbyte (~~~a) 0 = ~~~vbyte a 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp [vbyte, hr, show 8 * (15 - 0) + r < 128 by omega]

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

theorem top0 (X : BitVec 128) : vdword X 0 >>> 56 = (vbyte X 0).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, vbyte, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp [h, show 56 + i < 64 by omega, show i < 64 by omega]; congr 1; omega
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

/-- The address of chunk `i` of the table at `T`, as the code makes it. -/
def ch (T : Addr) : Nat → Addr
  | 0 => T
  | i + 1 => ch T i + 32#64

theorem ch_eq (T : Addr) : ∀ i, ch T i = T + BitVec.ofNat 64 (32 * i)
  | 0 => by simp [ch]
  | i + 1 => by
    rw [ch, ch_eq T i, show (32#64 : BitVec 64) = BitVec.ofNat 64 32 from rfl, Offset.add_add]; congr 2

/-! ## The lookup -/

theorem lookup_core (s : State) (idx : Byte) (h9 : s.gpr .r9 = idx.setWidth 64)
    (h8 : s.gpr .r8 = 0) (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256) :
    WP isa (.block lookup) s fun t =>
      t.gpr .r10 = (s.mem (s.gpr .r3 + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem := by
  obtain ⟨T, hT⟩ : ∃ T, s.gpr .r3 = T := ⟨_, rfl⟩
  have rc : ∀ i < 8, InRegions (s.rd ++ s.wr) (ch T i) 16 ∧ InRegions (s.rd ++ s.wr) (ch T i + 16#64) 16 :=
    fun i hi => by
      rw [ch_eq, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add, ← hT]
      exact ⟨region_offset _ _ _ _ _ (by omega) (by omega) hr, region_offset _ _ _ _ _ (by omega) (by omega) hr⟩
  have a0 := rc 0 (by decide); have a1 := rc 1 (by decide); have a2 := rc 2 (by decide)
  have a3 := rc 3 (by decide); have a4 := rc 4 (by decide); have a5 := rc 5 (by decide)
  have a6 := rc 6 (by decide); have a7 := rc 7 (by decide)
  simp only [ch] at a0 a1 a2 a3 a4 a5 a6 a7
  unfold lookup bitMask chunk choose vperm
  rrun [reduceVOpEval, vCtl, vBit, vLo, vHi, vPick, vpr_writeV, gpr_writeV, mem_writeV, rd_writeV, wr_writeV,
    ↓read_sixteen, addrX, BitVec.or_self, hT, h8, a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2,
    a5.1, a5.2, a6.1, a6.2, a7.1, a7.2]
  have hx : (s.gpr .r9).toNat = idx.toNat := by rw [h9, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  have hq : idx.toNat < 256 := idx.isLt
  generalize idx.toNat = x at hx hq ⊢
  have hc : ((s.gpr .r9 ^^^ 7#64).setWidth 8).toNat % 32 = (x % 32) ^^^ 7 := by
    rw [show (s.gpr .r9 ^^^ 7#64).setWidth 8 = (s.gpr .r9).setWidth 8 ^^^ 7#8 by
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
    else vbyte (swapDwords (s.mem.readW (ch T t + 16#64) 128)) ((x % 32 ^^^ 7) - 16)) (s.gpr .r9))).trans ?_
  rw [pick _ _ hx32, ch_eq, Offset.add_add, hx, show 32 * (x / 32 % 8) + x % 32 = x by omega]

end VG.Proof.Rc4.PPC64LE
