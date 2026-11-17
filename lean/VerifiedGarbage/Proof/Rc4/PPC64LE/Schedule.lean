module

public import VerifiedGarbage.Proof.Rc4.Identity
public import VerifiedGarbage.Proof.Rc4.Schedule
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Impl.Rc4.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Rc4.Qword
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc4.Table
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! ### `Rc4.PPC64LE.Replace`, which this module and modules that import it used -/

section

/-! ### `Rc4.PPC64LE.Lookup`, which this module and modules that import it used -/

section

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
  omega_using []

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
  simp [vbyte, hr, show 8 * (15 - 0) + r < 128 by omega_using [hr]]

/-- Byte `i` (of the first eight) of a vector, from its first doubleword. -/
theorem vbyte_hi (x u : BitVec 64) {i : Nat} (hi : i < 8) : vbyte (x ++ u) i = x.extractLsb' (8 * (7 - i)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hr, decide_true, Bool.true_and,
    show ¬ 8 * (15 - i) + r < 64 by omega_using [hi], ite_false]
  exact congrArg x.getLsbD (by omega_using [hi])

/-- `0 - ((q << (63 - c)) >> 63)`: all ones if bit `c` of `q` is set. -/
theorem bitMask_eq (q : BitVec 64) {c : Nat} (hc : c < 64) :
    0#64 - (q <<< (63 - c)) >>> 63 = if q.getLsbD c then BitVec.allOnes 64 else 0 := by
  have e : (q <<< (63 - c)) >>> 63 = if q.getLsbD c then 1#64 else 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    by_cases h0 : i = 0
    · subst h0
      simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
        show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
        show ¬ (63 < 63 - c) by omega_using [], decide_false, Bool.not_false,
        show 63 - (63 - c) = c by omega_using [hc]]
      cases q.getLsbD c <;> rfl
    · have : (q <<< (63 - c) >>> 63).getLsbD i = false := by
        simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
        simp only [show ¬ (63 + i < 64) by omega_using [h0], decide_false, Bool.false_and]
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
  exact Mem.extractLsb'_read m a (n := 16) (by split <;> omega_using [])

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
  · obtain ⟨l1, l2, l3⟩ := hi x hx (by omega_using [h])
    rw [ite_eq_right l1, vbyte_load _ _ l2, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add, l3]

theorem top0 (X : BitVec 128) : vdword X 0 >>> 56 = (vbyte X 0).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, vbyte, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp [h, show 56 + i < 64 by omega_using [h], show i < 64 by omega_using [hi]]; congr 1; omega_using []
  · simp [h, show ¬ 56 + i < 64 by omega_using [h]]

theorem xor7_mod (x : Byte) : (x ^^^ 7#8).toNat % 32 = (x.toNat % 32) ^^^ 7 := by
  have : ∀ x : Byte, (x ^^^ 7#8).toNat % 32 = (x.toNat % 32) ^^^ 7 := by decide
  exact this x

theorem ctl0 (x : BitVec 64) : (x <<< 56).extractLsb' (8 * (7 - 0)) 8 = x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show 56 + i < 64 by omega_using [hi], show i < 64 by omega_using [hi]]

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
  rcases (by omega_using [this] : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7) with
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
      exact ⟨region_offset _ _ _ _ _ (by omega_using [hi]) (by omega_using [hi]) hr, region_offset _ _ _ _ _ (by omega_using [hi]) (by omega_using [hi]) hr⟩
  have a0 := rc 0 (by decide); have a1 := rc 1 (by decide); have a2 := rc 2 (by decide)
  have a3 := rc 3 (by decide); have a4 := rc 4 (by decide); have a5 := rc 5 (by decide)
  have a6 := rc 6 (by decide); have a7 := rc 7 (by decide)
  simp only [ch] at a0 a1 a2 a3 a4 a5 a6 a7
  unfold lookup bitMask chunk choose vperm
  rrun [reduceVOpEval, vCtl, vBit, vLo, vHi, vPick, vpr_writeV, gpr_writeV, mem_writeV, rd_writeV, wr_writeV,
    ↓read_sixteen, addrX, BitVec.or_self, hT, h8, a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2,
    a5.1, a5.2, a6.1, a6.2, a7.1, a7.2]
  have hx : (s.gpr .r9).toNat = idx.toNat := by rw [h9, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega_using [])
  have hq : idx.toNat < 256 := idx.isLt
  generalize idx.toNat = x at hx hq ⊢
  have hc : ((s.gpr .r9 ^^^ 7#64).setWidth 8).toNat % 32 = (x % 32) ^^^ 7 := by
    rw [show (s.gpr .r9 ^^^ 7#64).setWidth 8 = (s.gpr .r9).setWidth 8 ^^^ 7#8 by
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi], xor7_mod, BitVec.toNat_setWidth, hx,
      Nat.mod_eq_of_lt (show x < 2 ^ 8 by omega_using [hq])]
  rw [top0]
  simp only [vbyte_or, vbyte_and, vbyte_not0, vbyte_mask _ _ (show 5 < 64 by decide) (show 0 < 8 by decide),
    vbyte_mask _ _ (show 6 < 64 by decide) (show 0 < 8 by decide),
    vbyte_mask _ _ (show 7 < 64 by decide) (show 0 < 8 by decide), sel8, vbyte_packed _ (show 0 < 16 by decide),
    vbyte_hi _ _ (show 0 < 8 by decide), ctl0, hc]
  have hx32 : x % 32 < 32 := Nat.mod_lt _ (by decide)
  refine (congrArg (BitVec.setWidth 64) (tree_sel (fun t =>
    if x % 32 ^^^ 7 < 16 then vbyte (swapDwords (s.mem.readW (ch T t) 128)) (x % 32 ^^^ 7)
    else vbyte (swapDwords (s.mem.readW (ch T t + 16#64) 128)) ((x % 32 ^^^ 7) - 16)) (s.gpr .r9))).trans ?_
  rw [pick _ _ hx32, ch_eq, Offset.add_add, hx, show 32 * (x / 32 % 8) + x % 32 = x by omega_using [hq]]

end VG.Proof.Rc4.PPC64LE

end

end

/-! # RC4 on PPC64LE: replacing a secret-indexed byte of the table

The difference is XORed into each of the table's 16 vectors under a mask
that is the difference in one lane of one vector: `vperm` of one-hot
vectors that conditional rotations (`rotStep_run`) move to the lane and
to the vector (`chain_bytes`). A vector's store then changes only that
byte (`write_xor`).
-/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Proof.Rc4

theorem byte_addr (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem xor_byte (a b : Byte) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  rw [BitVec.setWidth_xor]

theorem hi64 (a b : BitVec 64) : (a ++ b).extractLsb' 64 64 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 64 + i < 64 by omega_using [], ite_false, Nat.add_sub_cancel_left]

theorem lo64 (a b : BitVec 64) : (a ++ b).extractLsb' 0 64 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    Nat.zero_add, ite_true]

/-! ## Rotations -/

/-- `vsldoi d x x n`: `x` rotated left by `n` bytes. -/
def rotl (x : BitVec 128) (n : Nat) : BitVec 128 := BitVec.extractLsb' 128 128 ((x ++ x) <<< (8 * n))

theorem vbyte_zero (i : Nat) : vbyte 0#128 i = 0#8 := by simp [vbyte]

theorem ofVBytes_const_ite (c : Prop) [Decidable c] :
    (ofVBytes fun _ => if c then 255#8 else 0#8) = if c then BitVec.allOnes 128 else 0#128 := by
  by_cases h : c
  · simp only [h, ite_true]; decide
  · simp only [h, ite_false]; decide

theorem sel_ite (a b : BitVec 128) (c : Prop) [Decidable c] :
    (a &&& ~~~(if c then BitVec.allOnes 128 else 0#128)) ||| (b &&& (if c then BitVec.allOnes 128 else 0#128)) =
      if c then b else a := by
  by_cases h : c
  · simp only [h, ite_true, BitVec.not_allOnes, BitVec.and_zero, BitVec.zero_or, BitVec.and_allOnes]
  · simp only [h, ite_false, BitVec.not_zero, BitVec.and_allOnes, BitVec.and_zero, BitVec.or_zero]

/-- A splat of a bit's mask: all ones if bit `c` of `q` is set. -/
theorem splat_mask (q u : BitVec 64) {c : Nat} (hc : c < 64) :
    (ofVBytes fun i => if (vbyte 0#128 i).toNat % 32 < 16 then
        vbyte ((0#64 - (q <<< (63 - c)) >>> 63) ++ u) ((vbyte 0#128 i).toNat % 32)
      else vbyte ((0#64 - (q <<< (63 - c)) >>> 63) ++ u) ((vbyte 0#128 i).toNat % 32 - 16)) =
      if q.getLsbD c = true then BitVec.allOnes 128 else 0#128 := by
  simp only [vbyte_zero, BitVec.toNat_zero, Nat.zero_mod, show (0 : Nat) < 16 by decide, ite_true,
    vbyte_mask _ _ hc (show 0 < 8 by decide)]
  exact ofVBytes_const_ite _

theorem rotStep_run (u : State) {v w : VReg} (hv : (v = .v0 ∧ w = .v1) ∨ (v = .v1 ∧ w = .v0)) {b : Nat}
    (hb : b < 4) (hz : u.vpr .v14 = 0#128) (h8 : u.gpr .r8 = 0) :
    WP isa (.block (rotStep v b)) u fun t =>
      t.vpr v = (if (u.gpr .r0).getLsbD b = true then rotl (u.vpr v) (2 ^ b) else u.vpr v) ∧
      t.vpr .v14 = u.vpr .v14 ∧ t.vpr .v15 = u.vpr .v15 ∧ t.vpr w = u.vpr w ∧ t.mem = u.mem := by
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
  · unfold rotStep vperm
    rrun [reduceVOpEval, vRotM, vRot, vZ, vpr_writeV, gpr_writeV, mem_writeV, hz, h8,
      splat_mask _ _ (show 0 < 64 by decide), splat_mask _ _ (show 1 < 64 by decide),
      splat_mask _ _ (show 2 < 64 by decide), splat_mask _ _ (show 3 < 64 by decide), sel_ite, rotl]

/-- Byte 0's one-hot vector. -/
abbrev oh0 : BitVec 128 := 0xFF000000000000000000000000000000#128

/-- The four conditional rotations, by the bits of `n`. -/
def chain (n : Nat) (x : BitVec 128) : BitVec 128 :=
  let x1 := if n.testBit 0 = true then rotl x 1 else x
  let x2 := if n.testBit 1 = true then rotl x1 2 else x1
  let x3 := if n.testBit 2 = true then rotl x2 4 else x2
  if n.testBit 3 = true then rotl x3 8 else x3

theorem chain_bytes : ∀ n < 16, ∀ t < 16, vbyte (chain n oh0) t = if t = (16 - n) % 16 then 255#8 else 0#8 := by
  decide

theorem oneHot0_run (u : State) {v : VReg} (hv : v = .v0 ∨ v = .v1) (hz : u.vpr .v14 = 0#128) :
    WP isa (.block (oneHot0 v)) u fun t =>
      t.vpr v = oh0 ∧ t.vpr .v14 = u.vpr .v14 ∧ t.vpr .v15 = u.vpr .v15 ∧
      (∀ w, w ≠ v → w ≠ .v14 → t.vpr w = u.vpr w) ∧ t.mem = u.mem := by
  rcases hv with rfl | rfl <;>
  · unfold oneHot0
    rrun [reduceVOpEval, vZ, vpr_writeV, gpr_writeV, mem_writeV, hz, sldoi8_eq, hi64, lo64]
    refine ⟨by decide, fun w h1 _ => ?_⟩
    simp [h1]

theorem getLsbD_testBit (x : BitVec 64) (b : Nat) : x.getLsbD b = x.toNat.testBit b := rfl

theorem oneHot_run (u : State) {v w : VReg} (hv : (v = .v0 ∧ w = .v1) ∨ (v = .v1 ∧ w = .v0))
    (hz : u.vpr .v14 = 0#128) (h8 : u.gpr .r8 = 0) (hn : (u.gpr .r0).toNat < 16) :
    WP isa (.block (oneHot v)) u fun t =>
      (∀ i < 16, vbyte (t.vpr v) i = if i = (16 - (u.gpr .r0).toNat) % 16 then 255#8 else 0#8) ∧
      t.vpr .v14 = u.vpr .v14 ∧ t.vpr .v15 = u.vpr .v15 ∧ t.vpr w = u.vpr w ∧ t.mem = u.mem ∧
      Keep [.r12] u t := by
  have hv' : v = .v0 ∨ v = .v1 := by rcases hv with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hwv : w ≠ v := by rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;> decide
  have hw14 : w ≠ .v14 := by rcases hv with ⟨_, h2⟩ | ⟨_, h2⟩ <;> subst h2 <;> decide
  unfold oneHot
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (oneHot0_run u hv' hz) (by rcases hv' with h | h <;> subst h <;> decide) (by
    rcases hv' with h | h <;> subst h <;> decide)) fun t₀ ⟨⟨a0, z0, d0, o0, m0⟩, k0⟩ => ?_
  have g0 : t₀.gpr .r0 = u.gpr .r0 := k0.gpr (by decide)
  have e0 : t₀.gpr .r8 = 0 := by rw [k0.gpr (by decide), h8]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (rotStep_run t₀ hv (b := 0) (by decide) (by rw [z0, hz]) e0)
    (by rcases hv' with h | h <;> subst h <;> decide) (by rcases hv' with h | h <;> subst h <;> decide))
    fun t₁ ⟨⟨a1, z1, d1, o1, m1⟩, k1⟩ => ?_
  have g1 : t₁.gpr .r0 = u.gpr .r0 := (k1.gpr (by decide)).trans g0
  have e1 : t₁.gpr .r8 = 0 := by rw [k1.gpr (by decide), e0]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (rotStep_run t₁ hv (b := 1) (by decide) (by rw [z1, z0, hz]) e1)
    (by rcases hv' with h | h <;> subst h <;> decide) (by rcases hv' with h | h <;> subst h <;> decide))
    fun t₂ ⟨⟨a2, z2, d2, o2, m2⟩, k2⟩ => ?_
  have g2 : t₂.gpr .r0 = u.gpr .r0 := (k2.gpr (by decide)).trans g1
  have e2 : t₂.gpr .r8 = 0 := by rw [k2.gpr (by decide), e1]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (rotStep_run t₂ hv (b := 2) (by decide) (by rw [z2, z1, z0, hz]) e2)
    (by rcases hv' with h | h <;> subst h <;> decide) (by rcases hv' with h | h <;> subst h <;> decide))
    fun t₃ ⟨⟨a3, z3, d3, o3, m3⟩, k3⟩ => ?_
  have g3 : t₃.gpr .r0 = u.gpr .r0 := (k3.gpr (by decide)).trans g2
  have e3 : t₃.gpr .r8 = 0 := by rw [k3.gpr (by decide), e2]
  refine WP.mono (WP.keep [.r12] (rotStep_run t₃ hv (b := 3) (by decide) (by rw [z3, z2, z1, z0, hz]) e3)
    (by rcases hv' with h | h <;> subst h <;> decide) (by rcases hv' with h | h <;> subst h <;> decide))
    fun t₄ ⟨⟨a4, z4, d4, o4, m4⟩, k4⟩ => ?_
  refine ⟨fun i hi => ?_, by rw [z4, z3, z2, z1, z0], by rw [d4, d3, d2, d1, d0],
    by rw [o4, o3, o2, o1, o0 w hwv hw14], by rw [m4, m3, m2, m1, m0],
    (((k0.trans k1).trans k2).trans (k3.trans k4)).mono (by decide)⟩
  have := chain_bytes _ hn i hi
  rw [← this, a4, g3, a3, g2, a2, g1, a1, g0, a0]
  simp only [chain, getLsbD_testBit]

/-! ## The masks -/

theorem vbyte_top (x u : BitVec 64) : vbyte (x <<< 56 ++ u) 0 = x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  simp only [show ¬ 8 * (15 - 0) + i < 64 by omega_using [], ite_false, show 8 * (15 - 0) + i - 64 < 64 by omega_using [hi],
    decide_true, Bool.true_and, show ¬ 8 * (15 - 0) + i - 64 < 56 by omega_using [], decide_false, Bool.not_false]
  congr 1; omega_using []

/-- The lane's rotation: `(16 - ((index mod 16) XOR 7)) mod 16`. -/
theorem laneRot (b : Byte) :
    (((0#64 - ((b.setWidth 64 <<< 60 >>> 60) ^^^ 7#64)) <<< 60) >>> 60).toNat = (16 - ((b.toNat % 16) ^^^ 7)) % 16 := by
  have : ∀ b : Byte, (((0#64 - ((b.setWidth 64 <<< 60 >>> 60) ^^^ 7#64)) <<< 60) >>> 60).toNat =
      (16 - ((b.toNat % 16) ^^^ 7)) % 16 := by decide
  exact this b

/-- The vector's rotation: `(16 - index / 16) mod 16`. -/
theorem vecRot (b : Byte) : (((0#64 - b.setWidth 64 >>> 4) <<< 60) >>> 60).toNat = (16 - b.toNat / 16) % 16 := by
  have : ∀ b : Byte, (((0#64 - b.setWidth 64 >>> 4) <<< 60) >>> 60).toNat = (16 - b.toNat / 16) % 16 := by decide
  exact this b

theorem rot_back {p : Nat} (hp : p < 16) : (16 - (16 - p) % 16) % 16 = p := by omega_using [hp]

theorem and_ff (d : Byte) (c : Prop) [Decidable c] : (if c then 255#8 else 0#8) &&& d = if c then d else 0#8 := by
  by_cases h : c
  · simp only [h, ite_true, show (255#8 : Byte) = BitVec.allOnes 8 by decide, BitVec.allOnes_and]
  · simp [h]

theorem replaceStart_run (u : State) (idx d : Byte) (h9 : u.gpr .r9 = idx.setWidth 64) (h8 : u.gpr .r8 = 0)
    (h0 : u.gpr .r0 = d.setWidth 64) :
    WP isa (.block replaceStart) u fun t =>
      (∀ i < 16, vbyte (t.vpr .v0) i = if i = (idx.toNat % 16) ^^^ 7 then d else 0#8) ∧
      (∀ i < 16, vbyte (t.vpr .v1) i = if i = idx.toNat / 16 then 255#8 else 0#8) ∧
      t.vpr .v14 = 0#128 ∧ t.gpr .r11 = u.gpr .r3 ∧ t.mem = u.mem ∧ Keep [.r0, .r11, .r12] u t := by
  unfold replaceStart
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r12] (Q := fun t => t.vpr .v14 = 0#128 ∧ (∀ i < 16, vbyte (t.vpr .v15) i = d) ∧
      (t.gpr .r0).toNat = (16 - ((idx.toNat % 16) ^^^ 7)) % 16 ∧ t.mem = u.mem) (by
    unfold laneStart vperm
    rrun [reduceVOpEval, vZ, vDiff, vpr_writeV, gpr_writeV, mem_writeV, h0, h9, h8, BitVec.xor_self]
    refine ⟨fun i hi => ?_, laneRot idx⟩
    rw [vbyte_packed _ hi]
    simp only [vbyte_zero, BitVec.toNat_zero, Nat.zero_mod, show (0 : Nat) < 16 by decide, ite_true, vbyte_top]
    apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]) (by decide) rfl) fun t₁ ⟨⟨z1, d1, r1, m1⟩, k1⟩ => ?_
  have e8 : t₁.gpr .r8 = 0 := by rw [k1.gpr (by decide), h8]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (oneHot_run t₁ (v := .v0) (w := .v1) (.inl ⟨rfl, rfl⟩) z1 e8 (by rw [r1]; omega_using []))
    (by decide) rfl) fun t₂ ⟨⟨a2, z2, d2, _, m2, _⟩, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r12] (Q := fun t => (∀ i < 16, vbyte (t.vpr .v0) i =
      if i = (idx.toNat % 16) ^^^ 7 then d else 0#8) ∧ t.vpr .v14 = 0#128 ∧
      (t.gpr .r0).toNat = (16 - idx.toNat / 16) % 16 ∧ t.mem = u.mem) (by
    unfold vecStart
    rrun [reduceVOpEval, vLane, vDiff, vpr_writeV, gpr_writeV, mem_writeV, z2, z1, m2, m1,
      show t₂.gpr .r9 = idx.setWidth 64 by rw [k2.gpr (by decide), k1.gpr (by decide), h9],
      show t₂.gpr .r8 = 0 by rw [k2.gpr (by decide), e8]]
    refine ⟨fun i hi => ?_, vecRot idx⟩
    rw [vbyte_and, a2 i hi, d2, d1 i hi, r1, rot_back (Nat.xor_lt_two_pow (n := 4) (Nat.mod_lt _ (by decide))
      (by decide)), and_ff]) (by decide) rfl)
    fun t₃ ⟨⟨a3, z3, r3, m3⟩, k3⟩ => ?_
  have e8' : t₃.gpr .r8 = 0 := by rw [k3.gpr (by decide), k2.gpr (by decide), e8]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (oneHot_run t₃ (v := .v1) (w := .v0) (.inr ⟨rfl, rfl⟩) z3 e8' (by rw [r3]; omega_using []))
    (by decide) rfl) fun t₄ ⟨⟨a4, z4, _, o4, m4, _⟩, k4⟩ => ?_
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = t₄.gpr .r3 ∧ t.vpr = t₄.vpr ∧ t.mem = t₄.mem)
    (by rrun [BitVec.or_self]) (by decide) rfl) fun t ⟨⟨t11, tv, tm⟩, tk⟩ => ?_
  refine ⟨fun i hi => by rw [tv, o4]; exact a3 i hi, fun i hi => by
    rw [tv, a4 i hi, r3, show (16 - (16 - idx.toNat / 16) % 16) % 16 = idx.toNat / 16 by have := idx.isLt; omega_using []],
    by rw [tv, z4, z3], by rw [t11, k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide)],
    by rw [tm, m4, m3], (((k1.trans k2).trans k3).trans (k4.trans tk)).mono (by decide)⟩

/-! ## The stores -/

theorem swapDwords_xor (a b : BitVec 128) : swapDwords (a ^^^ b) = swapDwords a ^^^ swapDwords b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_swapDwords _ hi, BitVec.getLsbD_xor, BitVec.getLsbD_xor, getLsbD_swapDwords _ hi,
    getLsbD_swapDwords _ hi]

theorem extract_xor (a b : BitVec 128) (j : Nat) :
    (a ^^^ b).extractLsb' (8 * j) 8 = a.extractLsb' (8 * j) 8 ^^^ b.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

/-- Byte `x` of a vector's store of its load XORed with `W`. -/
theorem write_xor (m : Mem) (a : Addr) (W : BitVec 128) (x : Addr) :
    (m.write a 16 (swapDwords (swapDwords (m.readW a 128) ^^^ W))) x =
      if (x - a).toNat < 16 then m x ^^^ vbyte W ((x - a).toNat ^^^ 7) else m x := by
  unfold Mem.write
  split
  · rename_i h
    rw [swapDwords_xor, swapDwords_involutive, extract_xor]
    have e1 : (m.readW a 128).extractLsb' (8 * (x - a).toNat) 8 = m x := by
      rw [Mem.readW, BitVec.setWidth_eq]
      rw [show (m.read a (128 / 8)) = m.read a 16 from rfl, Mem.extractLsb'_read m a h, BitVec.ofNat_toNat,
        BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    have e2 : ∀ (X : BitVec 128) (j : Nat), j < 16 → (swapDwords X).extractLsb' (8 * j) 8 = vbyte X (j ^^^ 7) := by
      intro X j hj
      have f : ∀ j < 16, (if 15 - j < 8 then 15 - j + 8 else 15 - j - 8) = j ^^^ 7 := by decide
      rw [← f j hj, ← vbyte_swapDwords _ (by omega_using []), vbyte, show 15 - (15 - j) = j by omega_using [hj]]
    rw [e1, e2 W _ h]
  · rfl

/-- The scatter's state after `k` of the table's vectors, from `s₀`: the
replaced byte `x` (with value `nv`) is in place if its vector is done. -/
structure SInv (s₀ : State) (T : Addr) (x : Nat) (dd nv : Byte) (k : Nat) (u : State) : Prop where
  le : k ≤ 16
  lane : ∀ i < 16, vbyte (u.vpr .v0) i = if i = (x % 16) ^^^ 7 then dd else 0#8
  hot : ∀ i < 16, vbyte (u.vpr .v1) i = if (i + k) % 16 = x / 16 then 255#8 else 0#8
  z : u.vpr .v14 = 0#128
  r11 : u.gpr .r11 = T + BitVec.ofNat 64 (16 * k)
  r8 : u.gpr .r8 = 0
  mem : ∀ y, u.mem y = if (y - T).toNat < 16 * k ∧ (y - T).toNat = x then nv else s₀.mem y
  keep : Keep [.r11] s₀ u

theorem vbyte_rotl1 (H : BitVec 128) {t : Nat} (ht : t < 16) :
    vbyte (BitVec.extractLsb' 128 128 ((H ++ H) <<< 8)) t = vbyte H ((t + 1) % 16) := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, hr,
    decide_true, Bool.true_and, show 128 + (8 * (15 - t) + r) < 128 + 128 by omega_using [hr],
    show ¬ 128 + (8 * (15 - t) + r) < 8 by omega_using [], decide_false, Bool.not_false]
  by_cases h : t = 15
  · subst h
    rw [ite_eq_left (show 128 + (8 * (15 - 15) + r) - 8 < 128 by omega_using [hr]),
      decide_eq_true (show 8 * (15 - 15) + r < 128 by omega_using [hr]), Bool.true_and]
    exact congrArg H.getLsbD (by omega_using [])
  · rw [ite_eq_right (show ¬ 128 + (8 * (15 - t) + r) - 8 < 128 by omega_using [ht, h]),
      decide_eq_true (show 8 * (15 - t) + r < 128 by omega_using [hr]), Bool.true_and]
    exact congrArg H.getLsbD (by omega_using [ht, h])

theorem scatter_run (u : State) (hz : u.vpr .v14 = 0#128) (h8 : u.gpr .r8 = 0) {a : Addr} (h11 : u.gpr .r11 = a)
    (hr : InRegions (u.rd ++ u.wr) a 16) (hw : InRegions u.wr a 16) :
    WP isa (.block scatterStep) u fun t =>
      t.mem = u.mem.write a 16 (swapDwords (swapDwords (u.mem.readW a 128) ^^^ (u.vpr .v0 &&&
        ofVBytes fun _ => vbyte (u.vpr .v1) 0))) ∧
      t.vpr .v1 = BitVec.extractLsb' 128 128 ((u.vpr .v1 ++ u.vpr .v1) <<< 8) ∧
      t.vpr .v0 = u.vpr .v0 ∧ t.vpr .v14 = u.vpr .v14 ∧ t.gpr .r11 = a + 16#64 ∧ t.rd = u.rd ∧ t.wr = u.wr := by
  unfold scatterStep vperm
  rrun [reduceVOpEval, vMask, vHot, vLane, vS, vZ, vpr_writeV, gpr_writeV, mem_writeV, rd_writeV, wr_writeV,
    ↓read_sixteen, addrX, hz, h8, h11, hr, hw, State.store, vbyte_zero, BitVec.toNat_ofNat, Nat.zero_mod]

theorem sub_off (y T : Addr) (c : Nat) (hc : c < 2 ^ 64) :
    (y - (T + BitVec.ofNat 64 c)).toNat = ((y - T).toNat + (2 ^ 64 - c)) % 2 ^ 64 := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hc]

theorem xor7_inj : ∀ j < 16, ∀ q < 16, (j ^^^ 7 = q ^^^ 7 ↔ j = q) := by decide

theorem xor7_lt : ∀ j < 16, j ^^^ 7 < 16 := by decide

theorem eq_off (y T : Addr) : y = T + BitVec.ofNat 64 (y - T).toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

theorem scatter_step {s₀ : State} {T : Addr} {x : Nat} {dd nv : Byte} (hw : InRegions s₀.wr T 256)
    (hnv : nv = s₀.mem (T + BitVec.ofNat 64 x) ^^^ dd) {k : Nat} (hk : k < 16) {u : State}
    (I : SInv s₀ T x dd nv k u) :
    WP isa (.block scatterStep) u (SInv s₀ T x dd nv (k + 1)) := by
  have hwu : u.wr = s₀.wr := I.keep.2.2
  have hwa : InRegions u.wr (T + BitVec.ofNat 64 (16 * k)) 16 := by
    rw [hwu]; exact region_offset _ _ _ _ _ (by omega_using [hk]) (by omega_using [hk]) hw
  have hra : InRegions (u.rd ++ u.wr) (T + BitVec.ofNat 64 (16 * k)) 16 := by
    obtain ⟨r, hr, hc⟩ := hwa; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep [.r11] (scatter_run u I.z I.r8 I.r11 hra hwa) (by decide) rfl)
    fun t ⟨⟨tm, t1, t0, t14, t11, trd, twr⟩, tk⟩ => ?_
  have hM : (ofVBytes fun _ => vbyte (u.vpr .v1) 0) = if k = x / 16 then BitVec.allOnes 128 else 0#128 := by
    rw [I.hot 0 (by decide), show (0 + k) % 16 = k by omega_using [hk]]
    exact ofVBytes_const_ite _
  have hW : ∀ j < 16, vbyte (u.vpr .v0 &&& ofVBytes fun _ => vbyte (u.vpr .v1) 0) (j ^^^ 7) =
      if k = x / 16 ∧ j = x % 16 then dd else 0#8 := by
    intro j hj
    rw [hM, vbyte_and, I.lane _ (xor7_lt j hj)]
    by_cases e : k = x / 16
    · rw [ite_eq_left e, show vbyte (BitVec.allOnes 128) (j ^^^ 7) = 255#8 by
        have : ∀ j < 16, vbyte (BitVec.allOnes 128) j = 255#8 := by decide
        exact this _ (xor7_lt j hj)]
      have := xor7_inj j hj (x % 16) (by omega_using [])
      by_cases e2 : j = x % 16
      · rw [ite_eq_left (this.mpr e2), ite_eq_left ⟨e, e2⟩, show (255#8 : Byte) = BitVec.allOnes 8 by decide,
          BitVec.and_allOnes]
      · rw [ite_eq_right (fun h => e2 (this.mp h)), ite_eq_right (fun h => e2 h.2), BitVec.zero_and]
    · rw [ite_eq_right e, vbyte_zero, BitVec.and_zero, ite_eq_right (fun h => e h.1)]
  refine ⟨by omega_using [hk], fun i hi => by rw [t0]; exact I.lane i hi, fun i hi => ?_, by rw [t14]; exact I.z, ?_,
    by rw [tk.gpr (by decide)]; exact I.r8, fun y => ?_, I.keep.trans tk |>.mono (by decide)⟩
  · rw [t1, vbyte_rotl1 _ hi, I.hot _ (Nat.mod_lt _ (by decide)), show ((i + 1) % 16 + k) % 16 = (i + (k + 1)) % 16 by
      omega_using []]
  · rw [t11, show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add]; congr 2
  · rw [tm, write_xor, sub_off _ _ _ (by omega_using [hk])]
    have ho := (y - T).isLt
    generalize ho' : (y - T).toNat = o at ho
    split
    · rename_i hin
      have h1 : 16 * k ≤ o ∧ o < 16 * k + 16 := by omega_using [hk, ho', hin]
      rw [show (o + (2 ^ 64 - 16 * k)) % 2 ^ 64 = o - 16 * k by omega_using [hk, ho', hin], hW _ (by omega_using [ho', hin]), I.mem y, ho',
        ite_eq_right (show ¬ (o < 16 * k ∧ o = x) by omega_using [hk, hin])]
      by_cases e : o = x
      · rw [ite_eq_left ⟨by omega_using [hk, ho', hin, e], by omega_using [hk, ho', hin, e]⟩, ite_eq_left ⟨by omega_using [ho', hin], by omega_using [e]⟩, hnv, eq_off y T, ho', e]
      · rw [ite_eq_right (fun h => e (by omega_using [h1, h])), ite_eq_right (fun h => e h.2), BitVec.xor_zero]
    · rename_i hout
      rw [I.mem y, ho']
      by_cases e : o < 16 * k
      · simp only [show (o < 16 * k ∧ o = x) ↔ (o < 16 * (k + 1) ∧ o = x) by omega_using [hk, hout]]
      · rw [ite_eq_right (show ¬ (o < 16 * k ∧ o = x) by omega_using [e]), ite_eq_right (show ¬ (o < 16 * (k + 1) ∧ o = x) by omega_using [hk, hout, e])]

theorem scatter_all {s₀ : State} {T : Addr} {x : Nat} {dd nv : Byte} (hw : InRegions s₀.wr T 256)
    (hnv : nv = s₀.mem (T + BitVec.ofNat 64 x) ^^^ dd) :
    ∀ k ≤ 16, ∀ u, SInv s₀ T x dd nv 0 u →
      WP isa (.block ((List.range k).flatMap fun _ => scatterStep)) u (SInv s₀ T x dd nv k)
  | 0, _, u, I => WP.block_nil I
  | k + 1, hk, u, I => by
    rw [flatMap_succ, WP.block_append_iff]
    exact WP.mono (scatter_all hw hnv k (by omega_using [hk]) u I) fun v V => scatter_step hw hnv (by omega_using [hk]) V

/-! ## The replacement -/

theorem replace_core (s : State) (idx ii : Byte) (h9 : s.gpr .r9 = idx.setWidth 64)
    (h8 : s.gpr .r8 = 0) (hcx : s.gpr .r6 = ii.setWidth 64)
    (hw : InRegions s.wr (s.gpr .r3) 256) :
    WP isa (.block replace) s fun t =>
      t.gpr .r10 = (s.mem (s.gpr .r3 + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem.write (s.gpr .r3 + BitVec.ofNat 64 idx.toNat) 1
        (s.mem (s.gpr .r3 + BitVec.ofNat 64 ii.toNat)) := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  obtain ⟨T, hT⟩ : ∃ T, s.gpr .r3 = T := ⟨_, rfl⟩
  let b := s.mem (T + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (T + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r10, .r11, .r12] (lookup_core s idx h9 h8 hr) (by decide))
    fun t ⟨⟨t10, tm⟩, tk⟩ => ?_
  rw [WP.block_append_iff]
  have hi : InRegions (t.rd ++ t.wr) (T + ii.setWidth 64) 1 := by
    rw [tk.2.1, tk.2.2, byte_addr, ← hT]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega_using []) (by have := ii.isLt; omega_using []) hr
  refine WP.mono (WP.keep [.r0, .r12] (Q := fun u => u.gpr .r0 = v.setWidth 64 ∧ u.mem = s.mem) (by
    unfold loadI
    rrun [show t.gpr .r3 = T by rw [tk.gpr (by decide), hT], show t.gpr .r6 = ii.setWidth 64 by
      rw [tk.gpr (by decide), hcx], hi, tm]
    show _ = (s.mem (T + BitVec.ofNat 64 ii.toNat)).setWidth 64
    rw [← byte_addr ii]) (by decide) rfl) fun u ⟨⟨u0, um⟩, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r0] (Q := fun w => w.gpr .r0 = (v ^^^ b).setWidth 64 ∧ w.mem = s.mem ∧ w.vpr = u.vpr)
    (by rrun [u0, show u.gpr .r10 = b.setWidth 64 by rw [uk.gpr (by decide), t10, hT], um, xor_byte])
    (by decide) rfl) fun w ⟨⟨w0, wm, _⟩, wk⟩ => ?_
  have K : Keep [.r0, .r10, .r11, .r12] s w := ((tk.trans uk).trans wk).mono (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (replaceStart_run w idx (v ^^^ b) (by rw [K.gpr (by decide), h9])
    (by rw [K.gpr (by decide), h8]) w0) fun z ⟨zl, zh, zz, z11, zm, zk⟩ => ?_
  have K2 : Keep [.r0, .r10, .r11, .r12] s z := (K.trans zk).mono (by decide)
  have hwz : InRegions z.wr T 256 := by rw [K2.2.2, ← hT]; exact hw
  have I0 : SInv z T idx.toNat (v ^^^ b) v 0 z := ⟨by decide, zl, fun i hi => by rw [zh i hi, Nat.add_zero,
      Nat.mod_eq_of_lt hi], zz, by rw [z11, K.gpr (by decide), hT]; simp,
    by rw [K2.gpr (by decide), h8], fun y => by simp, Keep.refl _ _⟩
  have hnv : v = z.mem (T + BitVec.ofNat 64 idx.toNat) ^^^ (v ^^^ b) := by
    rw [zm, wm, show s.mem (T + BitVec.ofNat 64 idx.toNat) = b from rfl, BitVec.xor_comm v b,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  refine WP.mono (scatter_all hwz hnv 16 (by decide) z I0) fun f F => ⟨?_, ?_⟩
  · rw [F.keep.gpr (by decide), zk.gpr (by decide), wk.gpr (by decide), uk.gpr (by decide), t10, hT]
  · funext y
    rw [F.mem y, zm, wm, hT]
    unfold Mem.write
    have ho := (y - T).isLt
    rw [sub_off _ _ _ (by have := idx.isLt; omega_using [])]
    by_cases e : (y - T).toNat = idx.toNat
    · rw [ite_eq_left ⟨by have := idx.isLt; omega_using [e], e⟩, ite_eq_left (by rw [e]; omega_using [])]
      rw [e, show (idx.toNat + (2 ^ 64 - idx.toNat)) % 2 ^ 64 = 0 by omega_using []]
      apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
      show (s.mem (T + BitVec.ofNat 64 ii.toNat))[i] = _
      rw [← byte_addr ii]
    · rw [ite_eq_right (fun h => e h.2), ite_eq_right (by omega_using [e])]

end VG.Proof.Rc4.PPC64LE

end

end

/-! # RC4 on PPC64LE: key scheduling -/

@[expose] public section

namespace VG.Proof.Rc4.PPC64LE
open VG VG.PPC64LE VG.Impl.Rc4.PPC64LE VG.Spec.Rc4 VG.Proof.Rc4

theorem low_byte (b : Byte) : (b.setWidth 64).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

theorem ofNat_low (r : Nat) : (BitVec.ofNat 64 r).setWidth 8 = BitVec.ofNat 8 r := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

theorem mask255 (x : BitVec 64) : (x <<< 56) >>> 56 = (x.setWidth 8).setWidth 64 := by
  rw [low8]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (255 % 2 ^ 64 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega_using []

theorem byte_add (a b : Byte) :
    ((a.setWidth 64 + b.setWidth 64) <<< 56) >>> 56 = (a + b).setWidth 64 := by
  rw [mask255]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega_using []

theorem byte_add3 (j a k : Byte) :
    ((j.setWidth 64 + a.setWidth 64 + k.setWidth 64) <<< 56) >>> 56 = (j + a + k).setWidth 64 := by
  rw [mask255]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega_using []

/-! ## The identity permutation -/

def IdentityInv (s₀ : State) (r : Nat) (s : State) : Prop :=
  s.mem = identityMem s₀.mem (s₀.gpr .r3) r ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
    s.gpr .r3 = s₀.gpr .r3 ∧ s.gpr .r7 = s₀.gpr .r7 ∧ s.gpr .r4 = s₀.gpr .r4 ∧
    s.gpr .r6 = BitVec.ofNat 64 r

theorem identity_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .r3) 256) (h : IdentityInv s₀ r s) :
    WP isa (.block identityStep) s fun t => IdentityInv s₀ (r + 1) t ∧
      t.gpr .r12 = BitVec.ofNat 64 (r + 1) - BitVec.ofNat 64 256 := by
  obtain ⟨hm, hrd, hwr, hp3, h7, h4, h6⟩ := h
  have hw : InRegions s₀.wr (s₀.gpr .r3 + BitVec.ofNat 64 r) 1 :=
    region_offset _ _ _ _ _ (by omega_using [hr]) (by omega_using [hr]) hp
  have hadd : BitVec.ofNat 64 r + 1#64 = BitVec.ofNat 64 (r + 1) := by
    rw [BitVec.ofNat_add]
  unfold identityStep
  rrun [hw, hm, hrd, hwr, hp3, h7, h4, h6, hadd, ofNat_low, IdentityInv]
  exact identityMem_store _ _ _ hr

theorem sub256_ne (j : Nat) (hj : j + 1 < 256) :
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 256 == (0 : BitVec 64)) = false :=
  beq_eq_false_iff_ne.mpr (by bv_omega)

theorem identity_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hp : InRegions s₀.wr (s₀.gpr .r3) 256) (h : IdentityInv s₀ r s) :
    WP isa (.loop (.block identityStep) (.nonzero .d .r12)) s (IdentityInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ IdentityInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (identity_step s₀ t hj hp ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hz, hend]
    rfl
  · right
    refine ⟨?_, 256 - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hu⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hz, bne]
    rw [sub256_ne j (by omega_using [hj, hend])]
    rfl

/-! ## The key offset -/

/-- The key offset after `o`, as the code advances it to `o + 1`: back to 0 at
the key length `len`, without a branch. -/
def offNext (o len : BitVec 64) : BitVec 64 :=
  (o + 1#64) &&& (((o + 1#64 - len - 1#64) ^^^ (o + 1#64 - len)) >>> 63 - 1#64)

theorem offNext_eq (r : Nat) (len : BitVec 64) (hl : 0 < len.toNat) (hlen : len.toNat ≤ 256) :
    offNext (BitVec.ofNat 64 (r % len.toNat)) len = BitVec.ofNat 64 ((r + 1) % len.toNat) := by
  have hb := Nat.mod_lt r hl
  have ht : (BitVec.ofNat 64 (r % len.toNat) + 1#64).toNat = r % len.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r % len.toNat < 2 ^ 64 by omega_using [hb])]
    change (r % len.toNat + 1) % 2 ^ 64 = _
    omega_using [hb]
  have ha : (r + 1) % len.toNat = (r % len.toNat + 1) % len.toNat := by
    simp only [Nat.add_mod, Nat.mod_mod]
  unfold offNext
  by_cases h : r % len.toNat + 1 < len.toNat
  · have hd : ∀ x : BitVec 64, x.toNat = 2 ^ 64 - (len.toNat - (r % len.toNat + 1)) →
        x >>> 63 = 1#64 := by
      intro x hx
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hx]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega_using [hlen, h]
    have h1 : (BitVec.ofNat 64 (r % len.toNat) + 1#64 - len) >>> 63 = 1#64 :=
      hd _ (by rw [BitVec.toNat_sub, ht]; omega_using [h])
    have h2 : (BitVec.ofNat 64 (r % len.toNat) + 1#64 - len - 1#64) >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_sub, ht]
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      omega_using [hlen, hb]
    rw [BitVec.ushiftRight_xor_distrib, h1, h2, show (1#64 ^^^ 1#64) - 1#64 = BitVec.allOnes 64 by
      decide, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    rw [ht, BitVec.toNat_ofNat, ha, Nat.mod_eq_of_lt h,
      Nat.mod_eq_of_lt (show r % len.toNat + 1 < 2 ^ 64 by omega_using [hb])]
  · have he : BitVec.ofNat 64 (r % len.toNat) + 1#64 = len := by
      apply BitVec.eq_of_toNat_eq
      rw [ht]; omega_using [hb, h]
    rw [he, BitVec.sub_self, ha, show r % len.toNat + 1 = len.toNat by omega_using [hb, h], Nat.mod_self,
      show (0#64 - 1#64 ^^^ 0#64) >>> 63 - 1#64 = 0#64 by decide, BitVec.and_zero]

/-! ## One round -/

theorem schedule_before (s : State) (i j : Byte)
    (hcx : s.gpr .r6 = i.setWidth 64) (h9 : s.gpr .r9 = j.setWidth 64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .r7 + s.gpr .r5) 1) :
    WP isa (.block (loadI ++ ([.add .r9 .r9 .r0, .add .r12 .r7 .r5, .lbz .r0 .r12 0,
      .add .r9 .r9 .r0, .lsl .r9 .r9 56, .lsr .d .r9 .r9 56] : List Instr))) s
      fun t => t.gpr .r9 = (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 i.toNat) +
          s.mem (s.gpr .r7 + s.gpr .r5)).setWidth 64 ∧ Keep [.r0, .r9, .r12] s t ∧
        t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .r3 + s.gpr .r6) 1 := by
    rw [hcx, byte_addr i]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega_using []) (by have := i.isLt; omega_using []) hp
  refine WP.mono (WP.keep (Q := fun t => t.gpr .r9 = (j + s.mem (s.gpr .r3 + BitVec.ofNat 64 i.toNat) +
      s.mem (s.gpr .r7 + s.gpr .r5)).setWidth 64 ∧ t.mem = s.mem) [.r0, .r9, .r12] ?_
      (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold loadI
  rrun [hi, hk, h9]
  rw [hcx, byte_addr i, byte_add3]

theorem schedule_after (s : State) (i b : Byte)
    (hcx : s.gpr .r6 = i.setWidth 64) (hax : s.gpr .r10 = b.setWidth 64)
    (hw : InRegions s.wr (s.gpr .r3 + BitVec.ofNat 64 i.toNat) 1) :
    WP isa (.block [.add .r12 .r3 .r6, .stb .r10 .r12 0,
      .addi .r5 .r5 1, .sub .r12 .r5 .r4, .subi .r0 .r12 1, .logic .xor .r0 .r0 .r12,
      .lsr .d .r12 .r0 63, .subi .r12 .r12 1, .logic .and .r5 .r5 .r12,
      .addi .r6 .r6 1, .li .r12 256, .sub .r12 .r6 .r12]) s fun t =>
      t.mem = s.mem.write (s.gpr .r3 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r5 = offNext (s.gpr .r5) (s.gpr .r4) ∧
      t.gpr .r6 = i.setWidth 64 + 1#64 ∧
      t.gpr .r12 = i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 ∧
      Keep [.r0, .r5, .r6, .r12] s t := by
  have hw' : InRegions s.wr (s.gpr .r3 + s.gpr .r6) 1 := by rw [hcx, byte_addr i]; exact hw
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = s.mem.write (s.gpr .r3 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r5 = offNext (s.gpr .r5) (s.gpr .r4) ∧
      t.gpr .r6 = i.setWidth 64 + 1#64 ∧
      t.gpr .r12 = i.setWidth 64 + 1#64 - BitVec.ofNat 64 256) [.r0, .r5, .r6, .r12] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hk⟩
  rrun [hw', hax, low_byte, offNext]
  rw [hcx, byte_addr i]
  exact ⟨rfl, rfl, rfl⟩

/-- One concrete key-scheduling round, with both swap operands read before either write. -/
theorem schedule_step (s : State) (i j : Byte)
    (hcx : s.gpr .r6 = i.setWidth 64) (h9 : s.gpr .r9 = j.setWidth 64) (h8 : s.gpr .r8 = 0)
    (hp : InRegions s.wr (s.gpr .r3) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .r7 + s.gpr .r5) 1) :
    let a := s.mem (s.gpr .r3 + BitVec.ofNat 64 i.toNat)
    let jj := j + a + s.mem (s.gpr .r7 + s.gpr .r5)
    let b := s.mem (s.gpr .r3 + BitVec.ofNat 64 jj.toNat)
    WP isa (.block scheduleStep) s fun t =>
      t.mem = (s.mem.write (s.gpr .r3 + BitVec.ofNat 64 jj.toNat) 1 a).write
        (s.gpr .r3 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.gpr .r5 = offNext (s.gpr .r5) (s.gpr .r4) ∧
      t.gpr .r9 = jj.setWidth 64 ∧ t.gpr .r6 = i.setWidth 64 + 1#64 ∧
      t.gpr .r12 = i.setWidth 64 + 1#64 - BitVec.ofNat 64 256 ∧
      Keep ([.r0, .r9, .r12] ++ [.r0, .r10, .r11, .r12] ++ [.r0, .r5, .r6, .r12]) s t := by
  intro a jj b
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .r3) 256 := by
    obtain ⟨r, hr, hc⟩ := hp
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scheduleStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (schedule_before s i j hcx h9 hr hk) fun t ⟨t9, tk, tm⟩ => ?_
  have tcx : t.gpr .r6 = i.setWidth 64 := (tk.gpr (by decide)).trans hcx
  have tp : t.gpr .r3 = s.gpr .r3 := tk.gpr (by decide)
  have t8 : t.gpr .r8 = 0 := (tk.gpr (by decide)).trans h8
  have tr5 : t.gpr .r5 = s.gpr .r5 := tk.gpr (by decide)
  have tr4 : t.gpr .r4 = s.gpr .r4 := tk.gpr (by decide)
  have htp : InRegions t.wr (t.gpr .r3) 256 := by rw [tk.2.2, tp]; exact hp
  refine WP.mono (WP.keep [.r0, .r10, .r11, .r12] (replace_core t jj i t9 t8 tcx htp)
    (by decide +kernel)) fun u ⟨⟨uax, um⟩, uk⟩ => ?_
  have ucx : u.gpr .r6 = i.setWidth 64 := (uk.gpr (by decide)).trans tcx
  have up : u.gpr .r3 = s.gpr .r3 := (uk.gpr (by decide)).trans tp
  have ur5 : u.gpr .r5 = s.gpr .r5 := (uk.gpr (by decide)).trans tr5
  have ur4 : u.gpr .r4 = s.gpr .r4 := (uk.gpr (by decide)).trans tr4
  have u9 : u.gpr .r9 = jj.setWidth 64 := (uk.gpr (by decide)).trans t9
  rw [tm, tp] at uax um
  have hw : InRegions u.wr (u.gpr .r3 + BitVec.ofNat 64 i.toNat) 1 := by
    rw [uk.2.2, tk.2.2, up]
    exact region_offset _ _ _ _ _ (by have := i.isLt; omega_using []) (by have := i.isLt; omega_using []) hp
  refine WP.mono (schedule_after u i b ucx uax hw) fun v ⟨vm, v5, vcx, vz, vk⟩ => ?_
  refine ⟨?_, ?_, (vk.gpr (by decide)).trans u9, vcx, vz, (tk.trans uk).trans vk⟩
  · rw [vm, um, up]
  · rw [v5, ur5, ur4]

/-- The key bytes, from the key pointer and length of a state. -/
def keyAt (s : State) : List Byte := bytesAt s.mem (s.gpr .r7) (s.gpr .r4).toNat

structure ScheduleInv (s₀ : State) (r : Nat) (s : State) : Prop where
  frame : TableFrame (s₀.gpr .r3) s₀.mem s.mem
  table : (contextAt s.mem (s₀.gpr .r3)).table = (schedulePrefix (keyAt s₀) r).1
  j : s.gpr .r9 = (schedulePrefix (keyAt s₀) r).2.setWidth 64
  i : s.gpr .r6 = BitVec.ofNat 64 r
  off : s.gpr .r5 = BitVec.ofNat 64 (r % (s₀.gpr .r4).toNat)
  p : s.gpr .r3 = s₀.gpr .r3
  len : s.gpr .r4 = s₀.gpr .r4
  key : s.gpr .r7 = s₀.gpr .r7
  zero : s.gpr .r8 = 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem schedule_inv_step (s₀ s : State) {r : Nat} (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .r4).toNat ∧ (s₀.gpr .r4).toNat ≤ 256)
    (hp : InRegions s₀.wr (s₀.gpr .r3) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r7) (s₀.gpr .r4).toNat)
    (hs : Mem.Sep (s₀.gpr .r7) (s₀.gpr .r4).toNat (s₀.gpr .r3) 256)
    (h : ScheduleInv s₀ r s) :
    WP isa (.block scheduleStep) s fun t => ScheduleInv s₀ (r + 1) t ∧
      t.gpr .r12 = BitVec.ofNat 64 (r + 1) - BitVec.ofNat 64 256 := by
  let key := keyAt s₀
  let st := schedulePrefix key r
  have hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hi : s.gpr .r6 = (BitVec.ofNat 8 r).setWidth 64 := by
    rw [h.i, byte_addr, hrt]
  have hpoint : InRegions s.wr (s.gpr .r3) 256 := by rw [h.wr, h.p]; exact hp
  have hmod := Nat.mod_lt r (show 0 < (s₀.gpr .r4).toNat by omega_using [hlen])
  have hkeypoint : InRegions (s.rd ++ s.wr) (s.gpr .r7 + s.gpr .r5) 1 := by
    rw [h.rd, h.wr, h.key, h.off]
    exact region_offset _ _ _ _ _ (by omega_using [hmod]) (by omega_using [hmod]) hk
  have hkeybyte : s.mem (s.gpr .r7 + s.gpr .r5) = key.getD (r % key.length) 0 := by
    rw [h.key, h.off]
    have hsep := hs (s₀.gpr .r7 + BitVec.ofNat 64 (r % (s₀.gpr .r4).toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hmod])]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, keyAt]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  have htablebyte : s.mem (s.gpr .r3 + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    rw [h.p]
    have hg := table_get s.mem (s₀.gpr .r3) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  refine WP.mono (schedule_step s _ _ hi h.j h.zero hpoint hkeypoint)
    fun t ⟨tm, t5, t9, tcx, tz, tk⟩ => ?_
  have hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  have hcast : (BitVec.ofNat 8 r).setWidth 64 + 1#64 = BitVec.ofNat 64 (r + 1) := by
    rw [byte_addr, hrt, BitVec.ofNat_add]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, (tk.gpr (by decide)).trans h.p, (tk.gpr (by decide)).trans h.len,
    (tk.gpr (by decide)).trans h.key, (tk.gpr (by decide)).trans h.zero, tk.2.1.trans h.rd,
    tk.2.2.trans h.wr⟩, ?_⟩
  · rw [tm, h.p]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [tm, h.p, table_swap, h.table, hnext, hrt]
    have hb := htablebyte
    rw [h.p] at hb
    rw [hb, hkeybyte]
  · rw [t9, hrt, htablebyte, hkeybyte, hnext]
  · rw [tcx, hcast]
  · rw [t5, h.off, h.len]
    exact offNext_eq r _ (by omega_using [hlen]) hlen.2
  · rw [tz, hcast]

/-- All 256 scheduling rounds realize the complete specified permutation. -/
theorem schedule_loop (s₀ s : State) {r : Nat} (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .r4).toNat ∧ (s₀.gpr .r4).toNat ≤ 256)
    (hp : InRegions s₀.wr (s₀.gpr .r3) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .r7) (s₀.gpr .r4).toNat)
    (hs : Mem.Sep (s₀.gpr .r7) (s₀.gpr .r4).toNat (s₀.gpr .r3) 256)
    (h : ScheduleInv s₀ r s) :
    WP isa (.loop (.block scheduleStep) (.nonzero .d .r12)) s (ScheduleInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ ScheduleInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (schedule_inv_step s₀ t hj hlen hp hk hs ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hz, hend]
    rfl
  · right
    refine ⟨?_, 256 - (j + 1), by omega_using [hj, hrem], j + 1, by omega_using [hj, hend], rfl, hu⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hz, bne]
    rw [sub256_ne j (by omega_using [hj, hend])]
    rfl

end VG.Proof.Rc4.PPC64LE
