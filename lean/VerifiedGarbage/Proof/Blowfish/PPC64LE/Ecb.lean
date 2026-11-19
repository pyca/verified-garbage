module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Blowfish.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Blowfish.F
public import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
public import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Blowfish
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! ### `Blowfish.PPC64LE.Cipher`, which this module and modules that import it used -/

section

/-! ### `Blowfish.PPC64LE.Run`, which this module and modules that import it used -/

section

/-!
# Blowfish on PPC64LE: running blocks

`brun [facts]` runs a block of the Blowfish code symbolically (`crun`),
keeping 32-bit loads and doubleword stores as `Mem.readW` and `Mem.writeW`
and byte loads as the byte, as IDEA's `irun` (`Proof/Idea/PPC64LE/Ecb.lean`).
The code's 32-bit values live in the low words of registers: `lo` is that
word, and the `lo_*` lemmas take it through the operations the code uses.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp

theorem read_four (m : Mem) (a : Addr) : m.read a 4 = m.readW a 32 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem read_eight (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem write_eight (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem write_four (m : Mem) (a : Addr) (v : BitVec 32) : m.write a 4 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

/-- Steps a block of the Blowfish code. -/
syntax "brun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| brun) => `(tactic| brun [])
  | `(tactic| brun [$ls,*]) => `(tactic|
      crun [List.cons_append, List.nil_append, ↓read_one, ↓read_four, ↓read_eight, write_eight,
        write_four, false_implies, zero, sch, xL, xR, fReg, pPtr, qReg, acc, tmp, rowPtr, o16, o256, o272,
        ptr, cnt, $ls,*])

theorem WP.reassoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

/-! ## Low words -/

/-- The low word of a register. -/
abbrev lo (x : BitVec 64) : BitVec 32 := x.setWidth 32

theorem lo_and (x y : BitVec 64) : lo (x &&& y) = lo x &&& lo y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem lo_or (x y : BitVec 64) : lo (x ||| y) = lo x ||| lo y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem lo_xor (x y : BitVec 64) : lo (x ^^^ y) = lo x ^^^ lo y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem lo_add (x y : BitVec 64) : lo (x + y) = lo x + lo y := lo32_add x y

theorem lo_ext (x : BitVec 32) : lo (x.setWidth 64) = x := lo32_ext x

/-- Whether bit `c` of `q` is set, as the mask `0 - ((q << (63 - c)) >> 63)`. -/
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

/-- `x XOR ((r XOR x) AND m)` for an all-ones-or-zero mask. -/
theorem select_eq (x r : BitVec 64) (b : Bool) :
    x ^^^ ((r ^^^ x) &&& (if b then BitVec.allOnes 64 else 0)) = if b then r else x := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm r x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- `0 - ((v - 1) >> 63)` is all ones exactly when `v < 2 ^ 63` is zero. -/
theorem isZero_eq (v : BitVec 64) (h : v.toNat < 2 ^ 63) :
    0#64 - (v - 1#64) >>> 63 = if v.toNat = 0 then BitVec.allOnes 64 else 0 := by
  by_cases e : v.toNat = 0
  · have : v = 0#64 := BitVec.eq_of_toNat_eq (by simp [e])
    subst this; decide
  · rw [ite_eq_right e]
    have : (v - 1#64) >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega_using [h, e]
    rw [this]; rfl

end VG.Proof.Blowfish.PPC64LE

end

end

/-! ### `Blowfish.PPC64LE.Lookup`, which this module and modules that import it used -/

section

/-!
# Blowfish on PPC64LE: an S-box lookup

`lookup_run`: `lookup j` leaves S-box `j`'s entry for the byte `3 - j` of
xL's low word in the accumulator's low word, changing only the lookup's
registers (and vector registers).
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

/-- What a lookup needs: the schedule at `r3` readable and zero in `r0`. -/
structure LookEnv (s : State) : Prop where
  rd : ∀ o n, o + n ≤ 4168 → InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 o) n
  zero : s.gpr .r0 = 0#64

/-- The registers a lookup writes. -/
def lookRegs : List Reg := [.r9, .r10, .r11, .r12, .r14, .r15]

theorem LookEnv.keep {s t : State} (E : LookEnv s) {rs : List Reg} (h : Keep rs s t)
    (h3 : Reg.r3 ∉ rs) (h0 : Reg.r0 ∉ rs) : LookEnv t := by
  refine ⟨fun o n ho => ?_, by rw [h.gpr h0]; exact E.zero⟩
  rw [h.gpr h3, h.2.1, h.2.2]; exact E.rd o n ho

theorem lo_zero : lo 0#64 = 0#32 := rfl

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .d r) s = some (s.gpr r != 0#64) := by
  simp only [eval, State.read, BitVec.setWidth_eq]; rfl

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .d r) s = some (s.gpr r == 0#64) := by
  simp only [eval, State.read, BitVec.setWidth_eq]; rfl

/-- `a - c` (as doublewords, both below `2 ^ 64`) is nonzero iff `a ≠ c`. -/
theorem ofNat_sub_bne {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c != 0#64) = !decide (a = c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 c ≠ 0#64 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      omega_arith
    simp [this, h]

theorem ofNat_bne_zero {a : Nat} (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a != 0#64) = !decide (a = 0) := by
  by_cases h : a = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 a ≠ 0#64 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      omega_arith
    simp [this, h]

/-! ## The index -/

theorem index_val (x : BitVec 64) {j : Nat} (hj : j < 4) :
    (x <<< (32 + 8 * j)) >>> 56 = (quarter (lo x) j).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [quarter, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  by_cases h8 : i < 8
  · simp only [h8, decide_true, Bool.true_and, show 56 + i < 64 by omega_arith,
      show ¬ (56 + i < 32 + 8 * j) by omega_arith, decide_false, Bool.not_false,
      show 8 * (3 - j) + i < 32 by omega_arith]
    rw [decide_eq_true hi, Bool.true_and]
    congr 1; omega_arith
  · simp only [h8, decide_false, Bool.false_and]
    by_cases h : 56 + i < 64
    · omega_arith
    · simp [h]

theorem index_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block (index j)) s fun t =>
      t.gpr .r9 = (quarter (lo (s.gpr .r4)) j).setWidth 64 ∧ t.mem = s.mem := by
  rw [← index_val _ hj]
  unfold index
  brun [show 32 + 8 * j < 64 by omega_arith]

/-! ## Vector values -/

theorem read_sixteen (m : Mem) (a : Addr) : m.read a 16 = m.readW a 128 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

/-- `c` in every byte. -/
def splatV (c : Byte) : BitVec 128 := ofVBytes fun _ => c

theorem vbyte_splatV (c : Byte) (i : Nat) : vbyte (splatV c) i = c := by
  by_cases hi : i < 16
  · exact vbyte_packed _ hi
  · have : vbyte (splatV c) i = vbyte (splatV c) 15 := by
      simp only [vbyte, show 15 - i = 0 by omega_using [hi]]
    rw [this]; exact vbyte_packed _ (by decide)

theorem vbyte_zero (i : Nat) : vbyte 0#128 i = 0#8 := by simp [vbyte]

theorem vbyte_top (x u : BitVec 64) : vbyte (x <<< 56 ++ u) 0 = x.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  simp only [show ¬ 8 * (15 - 0) + i < 64 by omega_using [], ite_false, show 8 * (15 - 0) + i - 64 < 64 by omega_using [hi],
    decide_true, Bool.true_and, show ¬ 8 * (15 - 0) + i - 64 < 56 by omega_using [], decide_false, Bool.not_false]
  congr 1; omega_using []

theorem perm_splat0 (x u : BitVec 64) :
    (ofVBytes fun i =>
      if (vbyte (0#128) i).toNat % 32 < 16 then vbyte (x <<< 56 ++ u) ((vbyte (0#128) i).toNat % 32)
      else vbyte (x <<< 56 ++ u) ((vbyte (0#128) i).toNat % 32 - 16)) = splatV (x.setWidth 8) := by
  simp only [vbyte_zero, BitVec.toNat_zero, Nat.zero_mod, show (0 : Nat) < 16 by decide, ite_true, vbyte_top]
  rfl

theorem setWidth_xor7 (idx : Byte) : (idx.setWidth 64 ^^^ 7#64).setWidth 8 = idx ^^^ 7#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem setWidth_shr5 (idx : Byte) : (idx.setWidth 64 >>> 5).setWidth 8 = idx >>> 5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
  by_cases h : 5 + i < 8 <;> simp [h, show 5 + i < 64 by omega_using [hi]]

theorem vbyte_hot (u : BitVec 64) {k : Nat} (hk : k < 8) :
    vbyte (255#64 <<< 56 ++ u) k = if k = 0 then 255#8 else 0#8 := by
  obtain e : vbyte (255#64 <<< 56 ++ u) k = (255#64 <<< 56).extractLsb' (8 * (7 - k)) 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
      show ¬ 8 * (15 - k) + i < 64 by omega_using [hk], ite_false]
    congr 1; omega_using [hk]
  rw [e]
  have : ∀ k < 8, (255#64 <<< 56).extractLsb' (8 * (7 - k)) 8 = if k = 0 then 255#8 else 0#8 := by decide
  exact this k hk

/-! ## The start -/

theorem start_run (s : State) {j : Nat} (hj : j < 4) {idx : Byte} (h9 : s.gpr .r9 = idx.setWidth 64) :
    WP isa (.block (lookupStart j)) s fun t =>
      t.vpr .v0 = 0#128 ∧ t.vpr .v1 = splatV (idx ^^^ 7#8) ∧ t.vpr .v2 = splatV (idx >>> 5) ∧
      (∀ k < 8, vbyte (t.vpr .v3) k = if k = 0 then 255#8 else 0#8) ∧
      t.gpr .r15 = s.gpr .r3 + BitVec.ofNat 64 (1024 * j) ∧ t.gpr .r11 = 16#64 ∧ t.gpr .r14 = 256#64 ∧
      t.gpr .r9 = 272#64 ∧ t.mem = s.mem := by
  unfold lookupStart splat vperm
  brun [reduceVOpEval, vZero, vIdx, vChunk, vHot, vpr_writeV, gpr_writeV, mem_writeV, ↓read_sixteen,
    show 1024 * j < 32768 by omega_using [hj], BitVec.xor_self, h9, perm_splat0, setWidth_xor7, setWidth_shr5]
  intro k hk; rw [vbyte_hot _ hk]

/-! ## A row -/

theorem row_run (u : State) {j : Nat} (hj : j < 4) {rp : Addr} {M : BitVec 128} (h15 : u.gpr .r15 = rp)
    (h0 : u.gpr .r0 = 0#64) (h11 : u.gpr .r11 = 16#64) (h14 : u.gpr .r14 = 256#64) (h9 : u.gpr .r9 = 272#64)
    (hM : (ofVBytes fun i => if (vbyte (u.vpr .v2) i).toNat % 32 < 16 then
        vbyte (u.vpr .v3) ((vbyte (u.vpr .v2) i).toNat % 32)
      else vbyte (u.vpr .v3) ((vbyte (u.vpr .v2) i).toNat % 32 - 16)) = M)
    (a0 : InRegions (u.rd ++ u.wr) rp 16) (a16 : InRegions (u.rd ++ u.wr) (rp + 16#64) 16)
    (a256 : InRegions (u.rd ++ u.wr) (rp + 256#64) 16) (a272 : InRegions (u.rd ++ u.wr) (rp + 272#64) 16)
    (b0 : InRegions (u.rd ++ u.wr) (rp + 512#64) 16) (b16 : InRegions (u.rd ++ u.wr) (rp + 512#64 + 16#64) 16)
    (b256 : InRegions (u.rd ++ u.wr) (rp + 512#64 + 256#64) 16)
    (b272 : InRegions (u.rd ++ u.wr) (rp + 512#64 + 272#64) 16) :
    WP isa (.block (row j)) u fun t =>
      let sel := fun (v : VReg) (a : Addr) => (u.vpr v &&& ~~~M) ||| (swapDwords (u.mem.readW a 128) &&& M)
      t.vpr .v6 = sel .v6 rp ∧ t.vpr .v7 = sel .v7 (rp + 16#64) ∧ t.vpr .v8 = sel .v8 (rp + 256#64) ∧
      t.vpr .v9 = sel .v9 (rp + 272#64) ∧ t.vpr .v10 = sel .v10 (rp + 512#64) ∧
      t.vpr .v11 = sel .v11 (rp + 512#64 + 16#64) ∧ t.vpr .v12 = sel .v12 (rp + 512#64 + 256#64) ∧
      t.vpr .v13 = sel .v13 (rp + 512#64 + 272#64) ∧
      t.vpr .v3 = BitVec.extractLsb' 128 128 ((u.vpr .v0 ++ u.vpr .v3) <<< 120) ∧
      t.vpr .v0 = u.vpr .v0 ∧ t.vpr .v1 = u.vpr .v1 ∧ t.vpr .v2 = u.vpr .v2 ∧
      t.gpr .r15 = rp + 512#64 - 480#64 ∧
      t.gpr .r12 = rp + 512#64 - 480#64 - u.gpr .r3 - BitVec.ofNat 64 (1024 * j + 256) ∧ t.mem = u.mem := by
  unfold row selLoad vperm offReg
  brun [reduceVOpEval, vZero, vIdx, vChunk, vHot, vMask, vLoad, vSel, vpr_writeV, gpr_writeV, mem_writeV,
    ↓read_sixteen, h15, h0, h11, h14, h9, addrX, rd_writeV, wr_writeV, List.getD_cons_zero, List.getD_cons_succ,
    a0, a16, a256, a272, b0, b16, b256, b272, hM, show 1024 * j ≤ 32512 by omega_using [hj]]

/-! ## The mask and the one-hot vector -/

theorem ofVBytes_const_ite (c : Prop) [Decidable c] :
    (ofVBytes fun _ => if c then 255#8 else 0#8) = if c then BitVec.allOnes 128 else 0#128 := by
  by_cases h : c
  · simp only [h, ite_true]; decide
  · simp only [h, ite_false]; decide

theorem mask_eq {v2 v3 : BitVec 128} {idx : Byte} {i : Nat} (h2 : v2 = splatV (idx >>> 5))
    (h3 : ∀ k < 8, vbyte v3 k = if k = i then 255#8 else 0#8) :
    (ofVBytes fun k => if (vbyte v2 k).toNat % 32 < 16 then vbyte v3 ((vbyte v2 k).toNat % 32)
      else vbyte v3 ((vbyte v2 k).toNat % 32 - 16)) =
      if idx.toNat / 32 = i then BitVec.allOnes 128 else 0#128 := by
  obtain hx : (idx >>> 5).toNat = idx.toNat / 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  obtain hl : idx.toNat / 32 < 8 := by have := idx.isLt; omega_using []
  subst h2
  simp only [vbyte_splatV, hx, Nat.mod_eq_of_lt (show idx.toNat / 32 < 32 by omega_using []),
    show idx.toNat / 32 < 16 by omega_using [], ite_true, h3 _ hl]
  exact ofVBytes_const_ite _

theorem sel_ite (a b : BitVec 128) (c : Prop) [Decidable c] :
    (a &&& ~~~(if c then BitVec.allOnes 128 else 0#128)) ||| (b &&& (if c then BitVec.allOnes 128 else 0#128)) =
      if c then b else a := by
  by_cases h : c
  · simp only [h, ite_true, BitVec.not_allOnes, BitVec.and_zero, BitVec.zero_or, BitVec.and_allOnes]
  · simp only [h, ite_false, BitVec.not_zero, BitVec.and_allOnes, BitVec.and_zero, BitVec.or_zero]

theorem vbyte_shift1 (x : BitVec 128) {k : Nat} (hk : k < 16) :
    vbyte (BitVec.extractLsb' 128 128 ((0#128 ++ x) <<< 120)) k = if k = 0 then 0#8 else vbyte x (k - 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, hr,
    decide_true, Bool.true_and]
  by_cases h0 : k = 0
  · subst h0
    simp only [ite_true, BitVec.getLsbD_zero, show 128 + (8 * (15 - 0) + r) < 128 + 128 by omega_using [hr],
      decide_true, Bool.true_and, show ¬ 128 + (8 * (15 - 0) + r) < 120 by omega_using [], decide_false, Bool.not_false,
      show ¬ 128 + (8 * (15 - 0) + r) - 120 < 128 by omega_using [], ite_false, Bool.and_false]
  · simp only [h0, ite_false, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and,
      show 128 + (8 * (15 - k) + r) < 128 + 128 by omega_using [hr], show ¬ 128 + (8 * (15 - k) + r) < 120 by omega_using [],
      decide_false, Bool.not_false, show 128 + (8 * (15 - k) + r) - 120 < 128 by omega_using [hr, h0], ite_true]
    simp only [show 8 * (15 - k) + r < 128 by omega_using [hr], decide_true, Bool.true_and]
    congr 1; omega_using [hk, h0]

theorem hot_shift (x : BitVec 128) {i : Nat} (h : ∀ k < 8, vbyte x k = if k = i then 255#8 else 0#8) :
    ∀ k < 8, vbyte (BitVec.extractLsb' 128 128 ((0#128 ++ x) <<< 120)) k =
      if k = i + 1 then 255#8 else 0#8 := by
  intro k hk
  rw [vbyte_shift1 _ (by omega_using [hk])]
  by_cases h0 : k = 0
  · simp [h0]
  · rw [ite_eq_right h0, h _ (by omega_using [hk])]
    by_cases e : k - 1 = i
    · rw [ite_eq_left e, ite_eq_left (by omega_using [h0, e])]
    · rw [ite_eq_right e, ite_eq_right (by omega_using [e])]

/-! ## The rows -/

/-- Half `hf` of plane `b`'s row of S-box `j` that holds `x` (entries
`32 (x / 32)` to `32 (x / 32) + 31`), as `lxvd2x` loads it. -/
def chunk (m : Mem) (S : Addr) (j x b hf : Nat) : BitVec 128 :=
  swapDwords (m.readW (S + BitVec.ofNat 64 (1024 * j + 256 * b + 16 * hf + 32 * (x / 32))) 128)

/-- After `i` rows of S-box `j` for the index `idx`, from the lookup's
start `s₀`. -/
structure RowInv (s₀ : State) (j : Nat) (idx : Byte) (i : Nat) (u : State) : Prop where
  le : i ≤ 8
  v0 : u.vpr .v0 = 0#128
  v1 : u.vpr .v1 = splatV (idx ^^^ 7#8)
  v2 : u.vpr .v2 = splatV (idx >>> 5)
  hot : ∀ k < 8, vbyte (u.vpr .v3) k = if k = i then 255#8 else 0#8
  sel : idx.toNat / 32 < i → ∀ b < 4, ∀ hf < 2,
    u.vpr (vSel (2 * b + hf)) = chunk s₀.mem (s₀.gpr .r3) j idx.toNat b hf
  rp : u.gpr .r15 = s₀.gpr .r3 + BitVec.ofNat 64 (1024 * j + 32 * i)
  o16 : u.gpr .r11 = 16#64
  o256 : u.gpr .r14 = 256#64
  o272 : u.gpr .r9 = 272#64
  keep : Keep lookRegs s₀ u
  mem : u.mem = s₀.mem

theorem add512_sub480 (p : Addr) : p + 512#64 - 480#64 = p + BitVec.ofNat 64 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using []

/-- A kept row: the loaded half if the row holds the index, else what was
kept. -/
theorem sel_step {idx : Byte} {i : Nat} {old new c : BitVec 128}
    (hn : idx.toNat / 32 = i → new = c) (ho : idx.toNat / 32 < i → old = c) (h : idx.toNat / 32 < i + 1) :
    (if idx.toNat / 32 = i then new else old) = c := by
  by_cases e : idx.toNat / 32 = i
  · rw [ite_eq_left e]; exact hn e
  · rw [ite_eq_right e]; exact ho (by omega_using [h, e])

theorem row_step {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) (idx : Byte) {i : Nat}
    (hi : i < 8) {u : State} (I : RowInv s₀ j idx i u) :
    WP isa (.block (row j)) u fun u' =>
      RowInv s₀ j idx (i + 1) u' ∧
        u'.gpr .r12 = BitVec.ofNat 64 (1024 * j + 32 * (i + 1)) - BitVec.ofNat 64 (1024 * j + 256) := by
  obtain hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  obtain h3 : u.gpr .r3 = s₀.gpr .r3 := I.keep.gpr (by decide)
  obtain h0 : u.gpr .r0 = 0#64 := by rw [I.keep.gpr (by decide)]; exact E.zero
  obtain ⟨S, hS⟩ : ∃ S, s₀.gpr .r3 = S := ⟨_, rfl⟩
  obtain hrp : u.gpr .r15 = S + BitVec.ofNat 64 (1024 * j + 32 * i) := by rw [I.rp, hS]
  obtain reg : ∀ o, o ≤ 784 →
      InRegions (u.rd ++ u.wr) (S + BitVec.ofNat 64 (1024 * j + 32 * i + o)) 16 := fun o ho => by
    rw [hrd, ← hS]; exact E.rd _ _ (by omega_using [hj, hi, ho])
  obtain f1 : ∀ o, S + BitVec.ofNat 64 (1024 * j + 32 * i) + BitVec.ofNat 64 o =
      S + BitVec.ofNat 64 (1024 * j + 32 * i + o) := fun o => Offset.add_add _ _ _
  obtain f2 : ∀ o, S + BitVec.ofNat 64 (1024 * j + 32 * i) + 512#64 + BitVec.ofNat 64 o =
      S + BitVec.ofNat 64 (1024 * j + 32 * i + (512 + o)) := fun o => by
    rw [show (512#64 : BitVec 64) = BitVec.ofNat 64 512 from rfl, Offset.add_add, Offset.add_add, Nat.add_assoc]
  have f0 : S + BitVec.ofNat 64 (1024 * j + 32 * i) = S + BitVec.ofNat 64 (1024 * j + 32 * i + 0) := rfl
  have g16 : (16#64 : BitVec 64) = BitVec.ofNat 64 16 := rfl
  have g256 : (256#64 : BitVec 64) = BitVec.ofNat 64 256 := rfl
  have g272 : (272#64 : BitVec 64) = BitVec.ofNat 64 272 := rfl
  obtain a0 := reg 0 (by decide)
  obtain a16 := reg 16 (by decide)
  obtain a256 := reg 256 (by decide)
  obtain a272 := reg 272 (by decide)
  obtain b0 := reg (512 + 0) (by decide)
  obtain b16 := reg (512 + 16) (by decide)
  obtain b256 := reg (512 + 256) (by decide)
  obtain b272 := reg (512 + 272) (by decide)
  rw [← f0] at a0
  rw [← f1, ← g16] at a16
  rw [← f1, ← g256] at a256
  rw [← f1, ← g272] at a272
  rw [← f2, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at b0
  rw [← f2, ← g16] at b16
  rw [← f2, ← g256] at b256
  rw [← f2, ← g272] at b272
  refine WP.mono (WP.keep [.r15, .r12]
    (row_run u hj hrp (by rw [h0]) I.o16 I.o256 I.o272 (mask_eq I.v2 I.hot) a0 a16 a256 a272 b0 b16 b256 b272)
    (by rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide) rfl)
    fun u' ⟨⟨e6, e7, e8, e9, e10, e11, e12, e13, e3, e0, e1, e2, e15, er12, em⟩, ak⟩ => ?_
  simp only [sel_ite] at e6 e7 e8 e9 e10 e11 e12 e13
  have hm : u.mem = s₀.mem := I.mem
  -- The kept halves.
  obtain hs : ∀ (v : VReg) (b hf o : Nat) (a : Addr), b < 4 → hf < 2 →
      a = S + BitVec.ofNat 64 (1024 * j + 32 * i + o) → o = 256 * b + 16 * hf →
      u.vpr v = u.vpr (vSel (2 * b + hf)) →
      idx.toNat / 32 < i + 1 →
      (if idx.toNat / 32 = i then swapDwords (u.mem.readW a 128) else u.vpr v) = chunk s₀.mem S j idx.toNat b hf :=
    fun v b hf o a hb hhf ha ho hv h => sel_step (fun e => by
        rw [hm, ha, chunk]; congr 4; omega_using [ho, e])
      (fun h' => by rw [hv, ← hS]; exact I.sel h' b hb hf hhf) h
  obtain rp' : u'.gpr .r15 = S + BitVec.ofNat 64 (1024 * j + 32 * (i + 1)) := by
    rw [e15, add512_sub480, Offset.add_add]; congr 2
  refine ⟨⟨by omega_using [hi], by rw [e0, I.v0], by rw [e1, I.v1], by rw [e2, I.v2],
    by rw [e3, I.v0]; exact hot_shift _ I.hot, fun h b hb hf hhf => ?_, by rw [rp', hS],
    by rw [ak.gpr (by decide), I.o16], by rw [ak.gpr (by decide), I.o256], by rw [ak.gpr (by decide), I.o272],
    I.keep.trans ak |>.mono (by decide), em.trans I.mem⟩, ?_⟩
  · rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
      rcases (by omega_using [hhf] : hf = 0 ∨ hf = 1) with rfl | rfl
    · rw [show vSel (2 * 0 + 0) = .v6 from rfl, e6, hS]
      exact hs _ 0 0 0 _ (by decide) (by decide) rfl rfl rfl h
    · rw [show vSel (2 * 0 + 1) = .v7 from rfl, e7, hS]
      exact hs _ 0 1 16 _ (by decide) (by decide) (by rw [g16, f1]) rfl rfl h
    · rw [show vSel (2 * 1 + 0) = .v8 from rfl, e8, hS]
      exact hs _ 1 0 256 _ (by decide) (by decide) (by rw [g256, f1]) rfl rfl h
    · rw [show vSel (2 * 1 + 1) = .v9 from rfl, e9, hS]
      exact hs _ 1 1 272 _ (by decide) (by decide) (by rw [g272, f1]) rfl rfl h
    · rw [show vSel (2 * 2 + 0) = .v10 from rfl, e10, hS]
      exact hs _ 2 0 512 _ (by decide) (by decide)
        (by rw [← BitVec.add_zero (_ + 512#64), show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, f2]) rfl rfl h
    · rw [show vSel (2 * 2 + 1) = .v11 from rfl, e11, hS]
      exact hs _ 2 1 528 _ (by decide) (by decide) (by rw [g16, f2]) rfl rfl h
    · rw [show vSel (2 * 3 + 0) = .v12 from rfl, e12, hS]
      exact hs _ 3 0 768 _ (by decide) (by decide) (by rw [g256, f2]) rfl rfl h
    · rw [show vSel (2 * 3 + 1) = .v13 from rfl, e13, hS]
      exact hs _ 3 1 784 _ (by decide) (by decide) (by rw [g272, f2]) rfl rfl h
  · rw [er12, ← e15, rp', h3, hS, Offset.add_sub_cancel_left]

theorem rows_run {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) (idx : Byte) {u : State}
    (I : RowInv s₀ j idx 0 u) : WP isa (.loop (.block (row j)) (.nonzero .d .r12)) u (RowInv s₀ j idx 8) := by
  refine WP.loop (M := isa) (Q := RowInv s₀ j idx 8)
    (fun (n : Nat) (v : State) => ∃ k, k < 8 ∧ n = 8 - k ∧ RowInv s₀ j idx k v) ?_ 8 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨k, hk, hn, J⟩
  refine WP.mono (row_step E hj idx hk J) fun v' ⟨J', hz⟩ => ?_
  rw [eval_nonzero, hz, ofNat_sub_bne (by omega_arith) (by omega_arith)]
  by_cases e : k + 1 = 8
  · left
    exact ⟨by rw [e]; simp, e ▸ J'⟩
  · right
    exact ⟨by simp; omega_arith, n - 1, by omega_arith, k + 1, by omega_arith, by omega_arith, J'⟩

/-! ## The entry -/

theorem top_byte (f : Nat → Byte) : vdword (ofVBytes f) 0 >>> 56 = (f 0).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vdword, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp only [show 56 + i < 64 by omega_using [h], decide_true, Bool.true_and]
    have := getLsbD_packed f (j := 15) (r := i) (by decide) h
    rw [show 64 * (1 - 0) + (56 + i) = 8 * 15 + i by omega_using [], this]
    simp [show i < 64 by omega_using [hi]]
  · simp [show ¬ 56 + i < 64 by omega_using [h], BitVec.getLsbD_of_ge (f 0) i (by omega_using [h])]

theorem vbyte_load (m : Mem) (a : Addr) {k : Nat} (hk : k < 16) :
    vbyte (swapDwords (m.readW a 128)) k = m (a + BitVec.ofNat 64 (15 - (if k < 8 then k + 8 else k - 8))) := by
  rw [vbyte_swapDwords _ hk, vbyte, Mem.readW, BitVec.setWidth_eq]
  exact Mem.extractLsb'_read m a (n := 16) (by split <;> omega_using [])

theorem pick (m : Mem) (a a' : Addr) (ha : a' = a + BitVec.ofNat 64 16) {x : Nat} (hx : x < 32) :
    (if (x ^^^ 7) < 16 then vbyte (swapDwords (m.readW a 128)) (x ^^^ 7)
      else vbyte (swapDwords (m.readW a' 128)) ((x ^^^ 7) - 16)) = m (a + BitVec.ofNat 64 x) := by
  obtain lo : ∀ x < 16, (x ^^^ 7) < 16 ∧ 15 - (if (x ^^^ 7) < 8 then (x ^^^ 7) + 8 else (x ^^^ 7) - 8) = x := by
    decide
  obtain hi : ∀ x < 32, 16 ≤ x → ¬ (x ^^^ 7) < 16 ∧ (x ^^^ 7) - 16 < 16 ∧
      16 + (15 - (if (x ^^^ 7) - 16 < 8 then (x ^^^ 7) - 16 + 8 else (x ^^^ 7) - 16 - 8)) = x := by
    decide
  by_cases h : x < 16
  · obtain ⟨l1, l2⟩ := lo x h
    rw [ite_eq_left l1, vbyte_load _ _ l1, l2]
  · obtain ⟨l1, l2, l3⟩ := hi x hx (by omega_using [h])
    rw [ite_eq_right l1, vbyte_load _ _ l2, ha, Offset.add_add, l3]

theorem xor7_mod (x : Byte) : (x ^^^ 7#8).toNat % 32 = (x.toNat % 32) ^^^ 7 := by
  have : ∀ x : Byte, (x ^^^ 7#8).toNat % 32 = (x.toNat % 32) ^^^ 7 := by decide
  exact this x

/-- The low word of four bytes ORed into place. -/
theorem assemble (b0 b1 b2 b3 : Byte) {c : Nat} (hc : c < 4) :
    (lo ((((b0.setWidth 64 ||| b1.setWidth 64 <<< 8) ||| b2.setWidth 64 <<< 16) |||
      b3.setWidth 64 <<< 24))).extractLsb' (8 * c) 8 = [b0, b1, b2, b3].getD c 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  obtain z : ∀ (b : Byte) (n : Nat), 8 ≤ n → b.getLsbD n = false := fun b n h => BitVec.getLsbD_of_ge b n h
  rcases (by omega_using [hc] : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
  · simp [show i < 32 by omega_using [hi], show i < 64 by omega_using [hi], hi, show i < 16 by omega_using [hi], show i < 24 by omega_using [hi]]
  · simp [show 8 + i < 32 by omega_using [hi], show 8 + i < 64 by omega_using [hi], show 8 + i < 16 by omega_using [hi],
      show 8 + i < 24 by omega_using [hi], show i < 64 by omega_using [hi]]
  · simp [show 16 + i < 32 by omega_using [hi], show 16 + i < 64 by omega_using [hi], show ¬ 16 + i < 16 by omega_using [],
      show 16 + i < 24 by omega_using [hi], z b0 (16 + i) (by omega_using []), z b1 (16 + i - 8) (by omega_using []), show i < 64 by omega_using [hi]]
  · simp [show 24 + i < 32 by omega_using [hi], show 24 + i < 64 by omega_using [hi], show ¬ 24 + i < 16 by omega_using [],
      show ¬ 24 + i < 24 by omega_using [], z b0 (24 + i) (by omega_using []), z b1 (24 + i - 8) (by omega_using []),
      z b2 (24 + i - 16) (by omega_using []), show i < 64 by omega_using [hi]]

theorem end_run (v : State) {S : Addr} {j : Nat} (hj : j < 4) {idx : Byte} {m : Mem}
    (h1 : v.vpr .v1 = splatV (idx ^^^ 7#8))
    (hs : ∀ b < 4, ∀ hf < 2, v.vpr (vSel (2 * b + hf)) = chunk m S j idx.toNat b hf) :
    WP isa (.block lookupEnd) v fun t => lo (t.gpr .r10) = sEntry (scheduleAt m S) j idx ∧ t.mem = v.mem := by
  unfold lookupEnd entryByte vperm
  brun [reduceVOpEval, vByte, vSel, vIdx, List.getD_cons_zero, List.getD_cons_succ, vpr_writeV, gpr_writeV,
    mem_writeV, List.range_succ, List.range_zero, List.map_cons, List.map_nil, top_byte, h1, vbyte_splatV, xor7_mod]
  obtain hx : idx.toNat % 32 < 32 := Nat.mod_lt _ (by decide)
  obtain pb : ∀ b < 4, ∀ r₀ r₁ : VReg, r₀ = vSel (2 * b) → r₁ = vSel (2 * b + 1) →
      (if idx.toNat % 32 ^^^ 7 < 16 then vbyte (v.vpr r₀) (idx.toNat % 32 ^^^ 7)
        else vbyte (v.vpr r₁) ((idx.toNat % 32 ^^^ 7) - 16)) =
        m (S + BitVec.ofNat 64 (1024 * j + 256 * b + idx.toNat)) := by
    intro b hb r₀ r₁ e₀ e₁
    rw [e₀, e₁, show 2 * b = 2 * b + 0 from rfl, hs b hb 0 (by decide), hs b hb 1 (by decide), chunk, chunk,
      pick m _ _ (by rw [Offset.add_add]; congr 2; omega_using []) hx, Offset.add_add,
      show 1024 * j + 256 * b + 16 * 0 + 32 * (idx.toNat / 32) + idx.toNat % 32 = 1024 * j + 256 * b + idx.toNat by
        omega_using []]
  rw [pb 0 (by decide) .v6 .v7 rfl rfl, pb 1 (by decide) .v8 .v9 rfl rfl, pb 2 (by decide) .v10 .v11 rfl rfl,
    pb 3 (by decide) .v12 .v13 rfl rfl]
  refine word_ext fun c hc => ?_
  rw [assemble _ _ _ _ hc, sEntry_byte m S hj hc idx]
  rcases (by omega_using [hc] : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The lookup of S-box `j` for the byte `3 - j` of xL's low word. -/
theorem lookup_run {s : State} (E : LookEnv s) {j : Nat} (hj : j < 4) :
    WP isa (lookup j) s fun t =>
      lo (t.gpr .r10) = sEntry (scheduleAt s.mem (s.gpr .r3)) j (quarter (lo (s.gpr .r4)) j) ∧
        Keep lookRegs s t ∧ t.mem = s.mem := by
  let idx := quarter (lo (s.gpr .r4)) j
  unfold lookup
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r9] (index_run s hj) (by rfl) rfl) fun t ⟨⟨t9, tm⟩, tk⟩ => ?_
  refine WP.mono (WP.keep [.r12, .r9, .r15, .r11, .r14] (start_run t hj t9)
    (by rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide) rfl)
    fun u ⟨⟨u0, u1, u2, u3, u15, u11, u14, u9, um⟩, uk⟩ => ?_
  obtain K0 : Keep lookRegs s u := (tk.trans uk).mono (by decide)
  obtain I0 : RowInv s j idx 0 u := ⟨by decide, u0, u1, u2, u3, fun h => absurd h (Nat.not_lt_zero _),
    by rw [u15, tk.gpr (by decide)]; rfl, u11, u14, u9, K0, by rw [um, tm]⟩
  apply WP.seq
  refine WP.mono (rows_run E hj idx I0) fun v V => ?_
  obtain hl : idx.toNat / 32 < 8 := by have := idx.isLt; omega_using []
  refine WP.mono (WP.keep [.r10, .r12] (end_run v hj V.v1 (V.sel hl)) (by decide) rfl)
    fun w ⟨⟨w10, wm⟩, wk⟩ => ⟨w10, (V.keep.trans wk).mono (by decide), by rw [wm, V.mem]⟩

end VG.Proof.Blowfish.PPC64LE
end

end

/-!
# Blowfish on PPC64LE: F and the block function

`f_run`: F of xL's low word into `r7`'s, one S-box at a time (`fAcc`).
`cipher_run`: `cipher up` takes the halves in the low words of `r4` and
`r5` to their encryption (`up`) or decryption under the schedule at `r3`,
changing only `r4`, `r5`, `r7`–`r12`, `r14` and `r15`.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

/-! ## F -/

/-- The registers F writes. -/
def fRegs : List Reg := .r7 :: lookRegs

theorem combine_run (u : State) {j : Nat} (hj : j < 4) :
    WP isa (.block [combine j]) u fun t =>
      lo (t.gpr .r7) = (if j = 0 then lo (u.gpr .r10) else if j = 2 then lo (u.gpr .r7) ^^^ lo (u.gpr .r10)
        else lo (u.gpr .r7) + lo (u.gpr .r10)) ∧ t.mem = u.mem := by
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    brun [combine] <;> simp only [lo_xor, lo_add, BitVec.or_self]

/-- S-box `j`'s lookup, then its accumulation, from `fAcc … (j - 1)` (or
anything, for `j = 0`) in `r7`. -/
theorem step_run {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) {u : State} (k : Keep fRegs s₀ u)
    (hm : u.mem = s₀.mem) (h7 : 0 < j → lo (u.gpr .r7) = fAcc (scheduleAt s₀.mem (s₀.gpr .r3))
      (lo (s₀.gpr .r4)) (j - 1)) {Q : State → Prop}
    (hQ : ∀ t, lo (t.gpr .r7) = fAcc (scheduleAt s₀.mem (s₀.gpr .r3)) (lo (s₀.gpr .r4)) j →
      Keep fRegs s₀ t → t.mem = s₀.mem → Q t) :
    WP isa (.seq (lookup j) (.block [combine j])) u Q := by
  have Eu : LookEnv u := E.keep k (by decide) (by decide)
  apply WP.seq
  refine WP.mono (lookup_run Eu hj) fun v ⟨v10, vk, vm⟩ => ?_
  refine WP.mono (WP.keep [.r7] (combine_run v hj) (by
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide) rfl)
    fun t ⟨⟨t7, tm⟩, tk⟩ => hQ t ?_ ((k.trans vk).trans tk |>.mono (by decide)) (by rw [tm, vm, hm])
  have e3 : u.gpr .r3 = s₀.gpr .r3 := k.gpr (by decide)
  have e4 : u.gpr .r4 = s₀.gpr .r4 := k.gpr (by decide)
  rw [t7, v10, hm, e3, e4, vk.gpr (by decide)]
  exact fAcc_step _ _ hj _ h7

theorem f_run {s : State} (E : LookEnv s) :
    WP isa Impl.Blowfish.PPC64LE.f s fun t =>
      lo (t.gpr .r7) = Spec.Blowfish.f (scheduleAt s.mem (s.gpr .r3)) (lo (s.gpr .r4)) ∧
        Keep fRegs s t ∧ t.mem = s.mem := by
  unfold Impl.Blowfish.PPC64LE.f
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 0) (by decide) (Keep.refl _ _) rfl (fun h => absurd h (by decide))
    fun t0 h0 k0 m0 => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 1) (by decide) k0 m0 (fun _ => h0) fun t1 h1 k1 m1 => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 2) (by decide) k1 m1 (fun _ => h1) fun t2 h2 k2 m2 => ?_
  refine step_run E (j := 3) (by decide) k2 m2 (fun _ => h2) fun t3 h3 k3 m3 => ?_
  exact ⟨by rw [h3, fAcc_three], k3, m3⟩

/-! ## Rounds -/

/-- The P-array entry of round `m`. -/
def ord (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

/-- `pPtr`'s offset in the schedule after `i` rounds. -/
def pBase (up : Bool) (i : Nat) : Nat := if up then 4096 + 4 * i else 4160 - 4 * i

/-- The registers the block function writes. -/
def cRegs : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15]

theorem ofs_sub (S : BitVec 64) {a b : Nat} (h : b ≤ a) :
    S + BitVec.ofNat 64 a - BitVec.ofNat 64 b = S + BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [h]

/-- The address of the P-array entry of round `i`. -/
theorem addr_P (S : BitVec 64) (up : Bool) {i : Nat} (hi : i < 16) :
    S + BitVec.ofNat 64 (pBase up i) + BitVec.ofNat 64 (pAt up) = S + BitVec.ofNat 64 (4096 + 4 * ord up i) :=
  Offset.add_add_eq _ (by cases up <;> simp [pBase, pAt, ord] <;> omega_using [hi])

/-- After `i` rounds from `s₀`. -/
structure CInv (s₀ : State) (up : Bool) (i : Nat) (u : State) : Prop where
  le : i ≤ 16
  p : u.gpr .r8 = s₀.gpr .r3 + BitVec.ofNat 64 (pBase up i)
  halves : (lo (u.gpr .r4), lo (u.gpr .r5)) =
    iter (scheduleAt s₀.mem (s₀.gpr .r3)) (ord up) i (lo (s₀.gpr .r4), lo (s₀.gpr .r5))
  keep : Keep cRegs s₀ u
  mem : u.mem = s₀.mem

theorem round_head (u : State) (up : Bool) {P : BitVec 32} {a : Addr}
    (hp : u.gpr .r8 + BitVec.ofNat 64 (pAt up) = a)
    (hr : InRegions (u.rd ++ u.wr) a 4) (hP : u.mem.readW a 32 = P) :
    WP isa (.block [.load .w tmp pPtr (pAt up), .logic .xor xL xL tmp]) u fun t =>
      lo (t.gpr .r4) = lo (u.gpr .r4) ^^^ P ∧ t.mem = u.mem := by
  have ho : pAt up < 2 ^ 15 := by cases up <;> decide
  rw [← hp] at hr hP
  brun [ho, hr, hP]
  simp only [lo_xor, lo_ext]

theorem round_tail (u : State) (up : Bool) (S : BitVec 64) {i : Nat} (hi : i < 16)
    (h3 : u.gpr .r3 = S) (h8 : u.gpr .r8 = S + BitVec.ofNat 64 (pBase up i)) :
    WP isa (.block [.logic .xor xR xR fReg, .logic .or tmp xL xL, .logic .or xL xR xR,
        .logic .or xR tmp tmp, if up then .addi pPtr pPtr 4 else .subi pPtr pPtr 4,
        .sub tmp pPtr sch, .subi tmp tmp (if up then pOff + 64 else pOff)]) u fun t =>
      lo (t.gpr .r4) = lo (u.gpr .r5) ^^^ lo (u.gpr .r7) ∧ lo (t.gpr .r5) = lo (u.gpr .r4) ∧
        t.gpr .r8 = S + BitVec.ofNat 64 (pBase up (i + 1)) ∧
        t.gpr .r12 = BitVec.ofNat 64 (pBase up (i + 1)) - BitVec.ofNat 64 (pBase up 16) ∧
        t.mem = u.mem := by
  cases up
  · brun [h3, h8, pOff]
    simp only [pBase, Bool.false_eq_true, ite_false, lo_xor, BitVec.or_self]
    have e : S + BitVec.ofNat 64 (4160 - 4 * i) - 4#64 = S + BitVec.ofNat 64 (4160 - 4 * (i + 1)) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ofs_sub S (by omega_using [hi])]; congr 2
    refine ⟨trivial, trivial, e, ?_⟩
    rw [e, Offset.add_sub_cancel_left]
  · brun [h3, h8, pOff]
    simp only [pBase, ite_true, lo_xor, BitVec.or_self]
    have e : S + BitVec.ofNat 64 (4096 + 4 * i) + 4#64 = S + BitVec.ofNat 64 (4096 + 4 * (i + 1)) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    refine ⟨trivial, trivial, e, ?_⟩
    rw [e, Offset.add_sub_cancel_left]

theorem keep_reads {s t : State} {rs : List Reg} (k : Keep rs s t) : t.rd ++ t.wr = s.rd ++ s.wr := by
  rw [k.2.1, k.2.2]

theorem round_step {s₀ : State} (E : LookEnv s₀) (up : Bool) {i : Nat} (hi : i < 16) {u : State}
    (I : CInv s₀ up i u) :
    WP isa (round up) u fun u' => CInv s₀ up (i + 1) u' ∧
      u'.gpr .r12 = BitVec.ofNat 64 (pBase up (i + 1)) - BitVec.ofNat 64 (pBase up 16) := by
  have ho : ord up i < 18 := by cases up <;> simp [ord] <;> omega_arith
  let K := scheduleAt s₀.mem (s₀.gpr .r3)
  have u3 : u.gpr .r3 = s₀.gpr .r3 := I.keep.gpr (by decide)
  unfold round
  apply WP.seq
  refine WP.mono (WP.keep [.r4, .r12] (round_head u up (P := pEntry K (ord up i))
    (by rw [I.p, addr_P _ up hi]) (by rw [keep_reads I.keep]; exact E.rd _ _ (by omega_using [ho]))
    (by rw [I.mem, pEntry_read _ _ ho])) (by cases up <;> decide) rfl) fun v ⟨⟨v4, vm⟩, vk⟩ => ?_
  have kv : Keep cRegs s₀ v := (I.keep.trans vk).mono (by decide)
  have Ev : LookEnv v := E.keep kv (by decide) (by decide)
  apply WP.seq
  refine WP.mono (f_run Ev) fun w ⟨w7, wk, wm⟩ => ?_
  have w3 : w.gpr .r3 = s₀.gpr .r3 := by rw [wk.gpr (by decide), vk.gpr (by decide), u3]
  have w8 : w.gpr .r8 = s₀.gpr .r3 + BitVec.ofNat 64 (pBase up i) := by
    rw [wk.gpr (by decide), vk.gpr (by decide), I.p]
  refine WP.mono (WP.keep [.r4, .r5, .r8, .r12] (round_tail w up _ hi w3 w8) (by
    cases up <;> decide) rfl) fun x ⟨⟨x4, x5, x8, x12, xm⟩, xk⟩ => ?_
  have hK : scheduleAt v.mem (v.gpr .r3) = K := by rw [vm, I.mem, vk.gpr (by decide), u3]
  refine ⟨⟨by omega_using [hi], x8, ?_, ((kv.trans wk).trans xk).mono (by decide), by rw [xm, wm, vm, I.mem]⟩, x12⟩
  have w4 : w.gpr .r4 = v.gpr .r4 := wk.gpr (by decide)
  have w5 : w.gpr .r5 = u.gpr .r5 := by rw [wk.gpr (by decide), vk.gpr (by decide)]
  rw [x4, x5, w7, hK, w4, w5, v4, iter_succ, ← I.halves]
  simp only [roundStep]
  rw [BitVec.xor_comm (lo (u.gpr .r5))]

theorem cipher_start (s : State) (up : Bool) :
    WP isa (.block [.addi pPtr sch (if up then pOff else pOff + 64)]) s fun t =>
      t.gpr .r8 = s.gpr .r3 + BitVec.ofNat 64 (pBase up 0) ∧ t.mem = s.mem := by
  cases up <;> brun [pOff, pBase]

theorem rounds_run {s : State} (E : LookEnv s) (up : Bool) {u : State} (I : CInv s up 0 u) :
    WP isa (.loop (round up) (.nonzero .d tmp)) u (CInv s up 16) := by
  refine WP.loop (M := isa) (Q := CInv s up 16)
    (fun (n : Nat) (v : State) => ∃ i, i < 16 ∧ n = 16 - i ∧ CInv s up i v) ?_ 16 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨i, hi, hn, J⟩
  refine WP.mono (round_step E up hi J) fun v' ⟨J', hz⟩ => ?_
  rw [tmp, eval_nonzero, hz, ofNat_sub_bne (by cases up <;> simp [pBase] <;> omega_arith)
    (by cases up <;> simp [pBase])]
  have e : (pBase up (i + 1) = pBase up 16) ↔ i + 1 = 16 := by cases up <;> simp [pBase] <;> omega_using []
  by_cases e' : i + 1 = 16
  · left
    exact ⟨by simp [e.mpr e'], e' ▸ J'⟩
  · right
    have hne : ¬ pBase up (i + 1) = pBase up 16 := fun h => e' (e.mp h)
    exact ⟨by simp [hne], n - 1, by omega_using [hi, hn], i + 1, by omega_using [hi, e'], by omega_using [hn], J'⟩

theorem cipher_end (u : State) (up : Bool) {P₁₆ P₁₇ : BitVec 32} {a b : Addr}
    (ha : u.gpr .r8 + BitVec.ofNat 64 (pAt up) = a)
    (hb : u.gpr .r8 + BitVec.ofNat 64 (4 - pAt up) = b)
    (hra : InRegions (u.rd ++ u.wr) a 4) (hrb : InRegions (u.rd ++ u.wr) b 4)
    (h16 : u.mem.readW a 32 = P₁₆) (h17 : u.mem.readW b 32 = P₁₇) :
    WP isa (.block [.load .w tmp pPtr (pAt up), .logic .xor tmp xL tmp,
        .load .w xL pPtr (4 - pAt up), .logic .xor xL xL xR, .logic .or xR tmp tmp]) u fun t =>
      lo (t.gpr .r4) = P₁₇ ^^^ lo (u.gpr .r5) ∧ lo (t.gpr .r5) = lo (u.gpr .r4) ^^^ P₁₆ ∧
        t.mem = u.mem := by
  have ho : pAt up < 2 ^ 15 := by cases up <;> decide
  have ho' : 4 - pAt up < 2 ^ 15 := by cases up <;> decide
  rw [← ha] at hra h16
  rw [← hb] at hrb h17
  brun [ho, ho', hra, hrb, h16, h17]
  simp only [lo_xor, lo_ext, BitVec.or_self, and_self]

/-- The block function. -/
theorem cipher_run {s : State} (E : LookEnv s) (up : Bool) :
    WP isa (cipher up) s fun t =>
      (lo (t.gpr .r4), lo (t.gpr .r5)) =
        feistel (scheduleAt s.mem (s.gpr .r3)) (ord up) (lo (s.gpr .r4)) (lo (s.gpr .r5)) ∧
      Keep cRegs s t ∧ t.mem = s.mem := by
  unfold cipher
  apply WP.seq
  refine WP.mono (WP.keep [.r8] (cipher_start s up) (by cases up <;> decide) rfl)
    fun u ⟨⟨u8, um⟩, uk⟩ => ?_
  have I0 : CInv s up 0 u :=
    ⟨by decide, u8, by rw [uk.gpr (by decide), uk.gpr (by decide)]; rfl, uk.mono (by decide), um⟩
  apply WP.seq
  refine WP.mono (rounds_run E up I0) fun v V => ?_
  have hrd := keep_reads V.keep
  let K := scheduleAt s.mem (s.gpr .r3)
  have r16 : 4096 + 4 * ord up 16 + 4 ≤ 4168 := by cases up <;> decide
  have r17 : 4096 + 4 * ord up 17 + 4 ≤ 4168 := by cases up <;> decide
  have o16 : ord up 16 < 18 := by cases up <;> decide
  have o17 : ord up 17 < 18 := by cases up <;> decide
  refine WP.mono (WP.keep [.r4, .r5, .r12] (cipher_end v up (P₁₆ := pEntry K (ord up 16))
    (P₁₇ := pEntry K (ord up 17)) (a := s.gpr .r3 + BitVec.ofNat 64 (4096 + 4 * ord up 16))
    (b := s.gpr .r3 + BitVec.ofNat 64 (4096 + 4 * ord up 17))
    (by rw [V.p]; exact Offset.add_add_eq _ (by cases up <;> simp [pBase, pAt, ord]))
    (by rw [V.p]; exact Offset.add_add_eq _ (by cases up <;> simp [pBase, pAt, ord]))
    (by rw [hrd]; exact E.rd _ _ r16) (by rw [hrd]; exact E.rd _ _ r17)
    (by rw [V.mem, pEntry_read _ _ o16]) (by rw [V.mem, pEntry_read _ _ o17])) (by cases up <;> decide) rfl)
    fun t ⟨⟨t4, t5, tm⟩, tk⟩ => ?_
  refine ⟨?_, (V.keep.trans tk).mono (by decide), by rw [tm, V.mem]⟩
  rw [t4, t5, feistel_eq, ← V.halves, BitVec.xor_comm]

end VG.Proof.Blowfish.PPC64LE

end

end

/-!
# Blowfish on PPC64LE: ECB

`ecb_wp`: every block becomes its encryption or decryption, one at a time;
our caller's `r14`–`r17` are saved in the working space and restored.
-/

@[expose] public section

namespace VG.Proof.Blowfish.PPC64LE

open VG VG.PPC64LE VG.Impl.Blowfish.PPC64LE VG.Spec.Blowfish VG.Proof.Blowfish

/-! ## Blocks in and out of the halves -/

theorem rev32_byte (x : BitVec 32) {b : Nat} (hb : b < 4) :
    (rev32 x).extractLsb' (8 * b) 8 = x.extractLsb' (8 * (3 - b)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [rev32, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, BitVec.getLsbD_append]
  rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega_arith) [ite_eq_left, ite_eq_right, show i < 8 from hi] <;>
    rw [decide_eq_true (by omega_arith), Bool.true_and] <;> congr 1 <;> omega_arith

/-- The big-endian word at offset `o` of the block at `q`. -/
theorem rev_load (m : Mem) (q : Addr) {o : Nat} (ho : o ≤ 4) :
    rev32 (m.readW (q + BitVec.ofNat 64 o) 32) = decodeWord (blockAt m q) o := by
  refine word_ext fun b hb => ?_
  rw [rev32_byte _ hb, decodeWord_byte _ _ hb, blockAt_getD _ _ (by omega_arith),
    ← Mem.readW_byte m _ (by omega_arith), Offset.add_add]

/-- The block at `r16` into the halves, as big-endian words. -/
theorem loadBlock_run (u : State) {q : Addr} (hq : u.gpr .r16 = q) (h0 : u.gpr .r0 = 0#64)
    (r0 : InRegions (u.rd ++ u.wr) q 4) (r4 : InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 4) 4) :
    WP isa (.block loadBlock) u fun t =>
      lo (t.gpr .r4) = decodeWord (blockAt u.mem q) 0 ∧ lo (t.gpr .r5) = decodeWord (blockAt u.mem q) 4 ∧
        t.mem = u.mem := by
  have l0 := rev_load u.mem q (o := 0) (by decide)
  have l4 := rev_load u.mem q (o := 4) (by decide)
  rw [BitVec.add_zero] at l0
  unfold loadBlock
  brun [hq, h0, r0, r4, addrX, lo_ext, l0, l4]

theorem st_byte (m : Mem) (a : Addr) (v : BitVec 32) {t : Nat} (ht : t < 4) :
    m.writeW a v (a + BitVec.ofNat 64 t) = v.extractLsb' (8 * t) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a ht, Mem.readW_writeW_self32]

theorem writeW32_other {m : Mem} {a x : Addr} (v : BitVec 32) (h : Region.Disjoint ⟨x, 1⟩ ⟨a, 4⟩) :
    m.writeW a v x = m x :=
  Mem.write_apply fun h' => h x (Region.contains_self _ _) ((Region.contains_self a 4).byte h')

/-- The halves to the block at `r16`, the next block's pointer, and the
counter less one. -/
theorem storeBlock_run (u : State) {q : Addr} (hq : u.gpr .r16 = q) (h0 : u.gpr .r0 = 0#64)
    (w0 : InRegions u.wr q 4) (w4 : InRegions u.wr (q + BitVec.ofNat 64 4) 4) :
    WP isa (.block storeBlock) u fun t =>
      t.mem = (u.mem.writeW q (rev32 (lo (u.gpr .r4)))).writeW (q + BitVec.ofNat 64 4)
        (rev32 (lo (u.gpr .r5))) ∧
      t.gpr .r16 = q + 8#64 ∧ t.gpr .r17 = u.gpr .r17 - 1#64 ∧ Keep [.r12, .r16, .r17] u t := by
  refine WP.mono (WP.keep [.r12, .r16, .r17] (Q := fun t =>
      t.mem = (u.mem.writeW q (rev32 (lo (u.gpr .r4)))).writeW (q + BitVec.ofNat 64 4)
        (rev32 (lo (u.gpr .r5))) ∧ t.gpr .r16 = q + 8#64 ∧ t.gpr .r17 = u.gpr .r17 - 1#64) ?_
    (by decide) rfl) fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  unfold storeBlock
  brun [hq, h0, w0, w4, addrX]

/-- What the stores leave: the block. -/
theorem stored_block (m : Mem) (q : Addr) (L R : BitVec 32) :
    blockAt ((m.writeW q (rev32 L)).writeW (q + BitVec.ofNat 64 4) (rev32 R)) q = encodeBlock L R := by
  refine blockAt_eq _ _ _ fun i hi => ?_
  rw [encodeBlock_getD _ _ hi]
  by_cases h4 : i < 4
  · rw [ite_eq_left h4, writeW32_other _ (Offset.disjoint q (d := i) (n := 1) (e := 4) (k := 4) (by omega_arith)
      (by omega_arith) (by decide)), st_byte _ _ _ h4, rev32_byte _ h4]
  · rw [ite_eq_right h4, show i = 4 + (i - 4) by omega_arith, ← Offset.add_add, st_byte _ _ _ (by omega_arith),
      rev32_byte _ (by omega_arith)]
    congr 2; omega_arith

theorem stored_frame (m : Mem) (q : Addr) (L R : BitVec 32) :
    Frame [⟨q, 8⟩] m ((m.writeW q (rev32 L)).writeW (q + BitVec.ofNat 64 4) (rev32 R)) := by
  have c0 : Region.Contains ⟨q, 8⟩ q (32 / 8) := by
    have := Offset.contains_base q (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have c4 : Region.Contains ⟨q, 8⟩ (q + BitVec.ofNat 64 4) (32 / 8) :=
    Offset.contains_base q (by decide) (by decide)
  exact ((Frame.refl _ m).writeW List.mem_cons_self _ c0).writeW List.mem_cons_self _ c4

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

/-! ## The loop -/

/-- A block's encryption (`up`) or decryption. -/
def blockOut (K : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock K b else decryptBlock K b

theorem blockOut_eq (K : Schedule) (up : Bool) (b : Block) :
    blockOut K up b = encodeBlock (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).1
      (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).2 := by
  cases up <;> rfl

/-- The block `b` of the data at `D`. -/
abbrev wAt (D : Addr) (b : Nat) : Addr := D + BitVec.ofNat 64 (8 * b)

/-- The registers the loop writes. -/
def loopRegs : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17]

/-- The loop's fixed facts, about the state `s₀` before it. -/
structure LoopEnv (S D : Addr) (n : Nat) (s₀ : State) : Prop where
  r3 : s₀.gpr .r3 = S
  r0 : s₀.gpr .r0 = 0#64
  key : (⟨S, 4168⟩ : Region) ∈ s₀.rd ++ s₀.wr
  data : (⟨D, 8 * n⟩ : Region) ∈ s₀.wr
  keyData : (⟨S, 4168⟩ : Region).Disjoint ⟨D, 8 * n⟩
  fit : D.toNat + 8 * n ≤ 2 ^ 64

/-- After `k` blocks. -/
structure EInv (S D : Addr) (n : Nat) (up : Bool) (s₀ : State) (k : Nat) (u : State) : Prop where
  le : k ≤ n
  ptr : u.gpr .r16 = wAt D k
  cnt : u.gpr .r17 = BitVec.ofNat 64 (n - k)
  keep : Keep loopRegs s₀ u
  done : ∀ b < k, blockAt u.mem (wAt D b) = blockOut (scheduleAt s₀.mem S) up (blockAt s₀.mem (wAt D b))
  rest : ∀ b, k ≤ b → b < n → blockAt u.mem (wAt D b) = blockAt s₀.mem (wAt D b)
  frame : Frame [⟨D, 8 * n⟩] s₀.mem u.mem

theorem ecb_step {S D : Addr} {n : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D n s₀) {k : Nat}
    (hk : k < n) {u : State} (I : EInv S D n up s₀ k u) :
    WP isa (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) u
      (fun u' => EInv S D n up s₀ (k + 1) u' ∧ u'.gpr .r17 = BitVec.ofNat 64 (n - (k + 1))) := by
  have fit := L.fit
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  have dR : (⟨D, 8 * n⟩ : Region) ∈ u.wr := by rw [I.keep.2.2]; exact L.data
  have inD : ∀ o, o + 4 ≤ 8 → InRegions u.wr (wAt D k + BitVec.ofNat 64 o) 4 := fun o ho =>
    ⟨_, dR, by rw [Offset.add_add]; exact Offset.contains_base D (by omega_arith) (by omega_arith)⟩
  have inD' : ∀ o, o + 4 ≤ 8 → InRegions (u.rd ++ u.wr) (wAt D k + BitVec.ofNat 64 o) 4 := fun o ho =>
    let ⟨r, hr, hc⟩ := inD o ho; ⟨r, List.mem_append_right _ hr, hc⟩
  have u0 : u.gpr .r0 = 0#64 := by rw [I.keep.gpr (by decide)]; exact L.r0
  have i0 := inD' 0 (by decide)
  rw [BitVec.add_zero] at i0
  apply WP.seq
  refine WP.mono (WP.keep [.r4, .r5, .r12] (loadBlock_run u I.ptr u0 i0 (inD' 4 (by decide)))
    (by decide) rfl) fun u₁ ⟨⟨l₁, h₁, m₁⟩, k₁⟩ => ?_
  have hK : scheduleAt u.mem S = scheduleAt s₀.mem S :=
    scheduleAt_eq_of_frame S I.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.keyData
  have Ku₁ : Keep loopRegs s₀ u₁ := (I.keep.trans k₁).mono (by decide)
  have E : LookEnv u₁ := by
    refine ⟨fun o n ho => ?_, by rw [Ku₁.gpr (by decide)]; exact L.r0⟩
    rw [Ku₁.gpr (by decide), L.r3, Ku₁.2.1, Ku₁.2.2]
    exact ⟨_, L.key, Offset.contains_base S ho (by omega_arith)⟩
  apply WP.seq
  refine WP.mono (cipher_run E up) fun u₂ ⟨c₂, k₂, m₂⟩ => ?_
  have Ku₂ : Keep loopRegs s₀ u₂ := (Ku₁.trans k₂).mono (by decide)
  have wr₂ : u₂.wr = u.wr := by rw [k₂.2.2, k₁.2.2]
  have p₂ : u₂.gpr .r16 = wAt D k := by rw [k₂.gpr (by decide), k₁.gpr (by decide), I.ptr]
  have z₂ : u₂.gpr .r0 = 0#64 := by rw [Ku₂.gpr (by decide)]; exact L.r0
  have w0 := inD 0 (by decide)
  rw [BitVec.add_zero] at w0
  refine WP.mono (storeBlock_run u₂ p₂ z₂ (by rw [wr₂]; exact w0) (by rw [wr₂]; exact inD 4 (by decide)))
    fun u₃ ⟨m₃, p₃, c₃, k₃⟩ => ?_
  have subK : Region.Sub ⟨wAt D k, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega_arith)
  have hc₂ : u₂.gpr .r17 = BitVec.ofNat 64 (n - k) := by
    rw [k₂.gpr (by decide), k₁.gpr (by decide), I.cnt]
  have other : ∀ b, b < n → b ≠ k → blockAt u₃.mem (wAt D b) = blockAt u.mem (wAt D b) := fun b hb hne => by
    rw [m₃, blockAt_frame (stored_frame _ _ _ _) fun r hr => ?_, m₂, m₁]
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)
  have c₃' : u₃.gpr .r17 = BitVec.ofNat 64 (n - (k + 1)) := by
    rw [c₃, hc₂]; apply BitVec.eq_of_toNat_eq; simp; omega_arith
  refine ⟨⟨by omega_arith, ?_, c₃', (Ku₂.trans k₃).mono (by decide), fun b hb => ?_, fun b h1 h2 => ?_, ?_⟩, c₃'⟩
  · rw [p₃, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, wAt, wAt, Offset.add_add]
    congr 2
  · by_cases hbk : b = k
    · subst hbk
      have e1 := congrArg Prod.fst c₂
      have e2 := congrArg Prod.snd c₂
      simp only at e1 e2
      rw [m₃, stored_block, e1, e2, l₁, h₁, m₁, Ku₁.gpr (by decide), L.r3, hK, I.rest b (by omega_arith) hk,
        blockOut_eq]
    · rw [other b (by omega_arith) hbk]; exact I.done b (by omega_arith)
  · rw [other b h2 (by omega_arith)]; exact I.rest b (by omega_arith) h2
  · rw [m₃]
    refine I.frame.trans ?_
    rw [← m₁, ← m₂]
    exact (stored_frame _ _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, subK⟩

theorem loop_run {S D : Addr} {n : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D n s₀) (hn : 0 < n)
    {u : State} (I : EInv S D n up s₀ 0 u) :
    WP isa (.loop (.seq (.block loadBlock) (.seq (cipher up) (.block storeBlock))) (.nonzero .d cnt)) u
      (EInv S D n up s₀ n) := by
  refine WP.loop (M := isa) (Q := EInv S D n up s₀ n)
    (fun m v => ∃ k, k < n ∧ m = n - k ∧ EInv S D n up s₀ k v) ?_ n u ⟨0, hn, rfl, I⟩
  intro m v ⟨k, hk, hm, J⟩
  refine WP.mono (ecb_step L hk J) fun v' ⟨J', hz⟩ => ?_
  have hn64 : n < 2 ^ 64 := by have := L.fit; omega_arith
  rw [cnt, eval_nonzero, hz, ofNat_bne_zero (by omega_arith)]
  by_cases e : k + 1 = n
  · left
    exact ⟨by simp [e], e ▸ J'⟩
  · right
    exact ⟨by simp; omega_arith, n - (k + 1), by omega_arith, k + 1, by omega_arith, rfl, J'⟩

/-! ## The function -/

theorem save_eq : save = Spill.saveCode .r6 saved := rfl
theorem restore_eq : restore = Spill.restoreCode .r6 saved := rfl
theorem saved_fits : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide
theorem saved_lt : ∀ p ∈ saved, p.2 + 8 ≤ 32 := by decide

/-- What ECB may assume: the schedule readable, the `n` blocks and the
working space writable, apart, the blocks not wrapping around. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r3, 4168⟩]
  wr : s.wr = [⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩, ⟨s.gpr .r6, 256⟩]
  keyData : (⟨s.gpr .r3, 4168⟩ : Region).Disjoint ⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩
  keyBuf : (⟨s.gpr .r3, 4168⟩ : Region).Disjoint ⟨s.gpr .r6, 256⟩
  dataBuf : (⟨s.gpr .r4, 8 * (s.gpr .r5).toNat⟩ : Region).Disjoint ⟨s.gpr .r6, 256⟩
  fit : (s.gpr .r4).toNat + 8 * (s.gpr .r5).toNat ≤ 2 ^ 64

/-- What ECB guarantees. -/
structure EcbPost (up : Bool) (s s' : State) : Prop where
  done : ∀ b < (s.gpr .r5).toNat, blockAt s'.mem (wAt (s.gpr .r4) b) =
    blockOut (scheduleAt s.mem (s.gpr .r3)) up (blockAt s.mem (wAt (s.gpr .r4) b))
  saved : ∀ r ∈ saved.map Prod.fst, s'.gpr r = s.gpr r

theorem ecb_wp (up : Bool) {s : State} (h : EcbPre s) :
    WP isa (Impl.Blowfish.PPC64LE.ecb up) s (EcbPost up s) := by
  have fit := h.fit
  have bR : (⟨s.gpr .r6, 256⟩ : Region) ∈ s.wr := by rw [h.wr]; simp
  have slot : ∀ p ∈ saved, Region.Sub ⟨s.gpr .r6 + BitVec.ofNat 64 p.2, 8⟩ ⟨s.gpr .r6, 256⟩ := fun p hp =>
    Offset.sub_base _ (by have := saved_lt p hp; omega_arith)
  unfold Impl.Blowfish.PPC64LE.ecb
  apply WP.seq
  rw [save_eq]
  refine Spill.save_ok (by decide) saved_fits (fun p hp =>
    ⟨_, bR, Offset.contains_base _ (by have := saved_lt p hp; omega_arith) (by have := saved_lt p hp; omega_arith)⟩) ?_
  let M₀ := Spill.saveMem s.mem (s.gpr .r6) s.gpr saved
  refine WP.mono (WP.keep [.r0, .r16, .r17] (Q := fun t => t.gpr .r0 = 0#64 ∧ t.gpr .r16 = s.gpr .r4 ∧
      t.gpr .r17 = s.gpr .r5 ∧ t.mem = M₀) (by brun [BitVec.or_self]; rfl) (by decide) rfl)
    fun s₀ ⟨⟨z₀, p₀, c₀, m₀⟩, k₀⟩ => ?_
  have F₀ : Frame [⟨s.gpr .r6, 32⟩] s.mem M₀ :=
    Spill.saveMem_frame_base (fun p hp => saved_lt p hp) (by decide) _ _ _
  have r₀ : s₀.rd = s.rd ∧ s₀.wr = s.wr := ⟨k₀.2.1, k₀.2.2⟩
  have sub32 : Region.Sub ⟨s.gpr .r6, 32⟩ ⟨s.gpr .r6, 256⟩ := Region.sub_prefix (by decide)
  have L : LoopEnv (s.gpr .r3) (s.gpr .r4) (s.gpr .r5).toNat s₀ := by
    refine ⟨by rw [k₀.gpr (by decide)], z₀, ?_, ?_, h.keyData, fit⟩
    · rw [r₀.1, r₀.2, h.rd]; simp
    · rw [r₀.2, h.wr]; simp
  have I0 : EInv (s.gpr .r3) (s.gpr .r4) (s.gpr .r5).toNat up s₀ 0 s₀ :=
    ⟨by omega_arith, by rw [p₀]; simp [wAt], by rw [c₀]; simp, Keep.refl _ _, fun b hb => absurd hb (by omega_arith),
      fun _ _ _ => rfl, Frame.refl _ _⟩
  apply WP.seq
  refine WP.mono (Q := EInv (s.gpr .r3) (s.gpr .r4) (s.gpr .r5).toNat up s₀ (s.gpr .r5).toNat) ?_
    fun u U => ?_
  · refine WP.ite (s.gpr .r5 == 0#64) (by rw [cnt, eval_zero, c₀]) (fun hz => ?_) (fun hz => ?_)
    · have hn : (s.gpr .r5).toNat = 0 := by simp only [beq_iff_eq] at hz; simp [hz]
      exact WP.block_nil (hn ▸ I0)
    · have hn : 0 < (s.gpr .r5).toNat := by
        have : s.gpr .r5 ≠ 0#64 := by simpa using hz
        have : (s.gpr .r5).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
        omega_arith
      exact loop_run L hn I0
  · rw [restore_eq]
    have r6 : u.gpr .r6 = s.gpr .r6 := by rw [U.keep.gpr (by decide), k₀.gpr (by decide)]
    have hsv : Spill.Saved (s.gpr .r6) s.gpr saved u.mem := by
      have : Spill.Saved (s.gpr .r6) s.gpr saved s₀.mem := by
        rw [m₀]; exact Spill.saveMem_saved (by decide) s.mem (s.gpr .r6) s.gpr
      exact this.frame U.frame fun p hp r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.dataBuf.symm.sub_left (slot p hp))
    refine WP.mono (Spill.restore_wp (by decide) r6 saved_fits (by decide) (fun p hp => ?_) hsv)
      fun s' R => ⟨fun b hb => ?_, fun r hr => ?_⟩
    · rw [U.keep.2.1, U.keep.2.2, r₀.1, r₀.2]
      exact ⟨_, List.mem_append_right _ bR, Offset.contains_base _ (by have := saved_lt p hp; omega_arith)
        (by have := saved_lt p hp; omega_arith)⟩
    · have dK : ∀ r ∈ [(⟨s.gpr .r6, 32⟩ : Region)], (⟨s.gpr .r3, 4168⟩ : Region).Disjoint r := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.keyBuf.sub_right sub32
      have dB : ∀ r ∈ [(⟨s.gpr .r6, 32⟩ : Region)], (⟨wAt (s.gpr .r4) b, 8⟩ : Region).Disjoint r :=
        fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (h.dataBuf.sub_left (Offset.sub_base _ (by omega_arith))).sub_right sub32
      rw [R.mem, U.done b hb, m₀, scheduleAt_eq_of_frame _ F₀ dK, blockAt_frame F₀ dB]
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      exact R.gpr p hp

end VG.Proof.Blowfish.PPC64LE
