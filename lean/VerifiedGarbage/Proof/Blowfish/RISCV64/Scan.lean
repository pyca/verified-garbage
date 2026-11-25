module

public import VerifiedGarbage.Proof.Blowfish.F
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Blowfish.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Blowfish
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.TCB.Code

/-! ### `Blowfish.RISCV64.Run`, which this module and modules that import it used -/

section

/-!
# Blowfish on RISC-V: running blocks

`brun [facts]` runs a block of the Blowfish code symbolically (`mrun`). The
code's 32-bit values live in the low words of registers: `lo` is that word,
and the `lo_*` lemmas take it through the operations the code uses. The
masks are made by arithmetic shifts (`bit_mask`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64

/-- Steps a block of the Blowfish code. -/
syntax "brun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| brun) => `(tactic| brun [])
  | `(tactic| brun [$ls,*]) => `(tactic|
      mrun [sch, xL, xR, fReg, pPtr, qReg, acc, mReg, tmp, rowPtr, ptr, cnt, $ls,*])

theorem WP.reassoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

/-! ## Low words -/

/-- The low word of a register. -/
abbrev lo (x : BitVec 64) : BitVec 32 := x.setWidth 32

theorem lo_or (x y : BitVec 64) : lo (x ||| y) = lo x ||| lo y := lo32_or x y
theorem lo_xor (x y : BitVec 64) : lo (x ^^^ y) = lo x ^^^ lo y := lo32_xor x y
theorem lo_add (x y : BitVec 64) : lo (x + y) = lo x + lo y := lo32_add x y
theorem lo_ext (x : BitVec 32) : lo (x.setWidth 64) = x := lo32_ext x
theorem lo_sext (x : BitVec 32) : lo (sext32 x) = x := lo32_sext x

/-! ## Masks -/

/-- Bit `c` of `q` shifted to the top and arithmetically back: all ones if
it is set. -/
theorem bit_mask (q : BitVec 64) {c : Nat} (hc : c < 64) :
    (q <<< (63 - c)).sshiftRight 63 = if q.getLsbD c then BitVec.allOnes 64 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  have key : (q <<< (63 - c)).getLsbD 63 = q.getLsbD c := by
    rw [BitVec.getLsbD_shiftLeft]
    simp only [show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
      show ¬ (63 < 63 - c) by omega_using [], decide_false, Bool.not_false, show 63 - (63 - c) = c by omega_using [hc]]
  rw [show (if 63 + i < 64 then (q <<< (63 - c)).getLsbD (63 + i) else (q <<< (63 - c)).getLsbD (64 - 1)) =
    (q <<< (63 - c)).getLsbD 63 by split; (congr 1; omega_arith); rfl, key]
  cases q.getLsbD c
  · simp
  · simp only [ite_true, BitVec.getLsbD_allOnes, hi, decide_true, show ¬ 64 ≤ i by omega_using [hi], decide_false,
      Bool.not_false, Bool.and_true]

end VG.Proof.Blowfish.RISCV64

end

end

/-! ### `Blowfish.RISCV64.Lookup`, which this module and modules that import it used -/

section

/-! ### `Blowfish.Scan64`, which only this module used -/

section

/-!
# A lookup that scans an S-box's planes a doubleword at a time

What 64-bit implementations hold while scanning S-box `j` for the index `x`
a row of eight entries (a doubleword of each plane) at a time, with one
accumulator per plane: the OR of the rows' doublewords, each masked to all
ones if the row holds `x` and to zero otherwise (`scanPlane`), which after
the last row is plane `b`'s doubleword of the row holding `x`; and that
doubleword's byte in `x`'s lane `x mod 8` is byte `b` of the entry
(`planeWord64_byte`).
-/

@[expose] public section

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

/-- Plane `b`'s doubleword of row `k` of S-box `j`, in the schedule at `p`. -/
def planeWord64 (m : Mem) (p : Addr) (j b k : Nat) : BitVec 64 :=
  m.readW (p + BitVec.ofNat 64 (1024 * j + 256 * b + 8 * k)) 64

/-- Plane `b`'s accumulator once rows `0, …, k - 1` are scanned for `x`. -/
def scanPlane (m : Mem) (p : Addr) (j b x k : Nat) : BitVec 64 :=
  if x / 8 < k then planeWord64 m p j b (x / 8) else 0

/-- The mask of row `k` for `x`. -/
def rowSel (x k : Nat) : BitVec 64 := if x / 8 = k then BitVec.allOnes 64 else 0

/-- Row 0, masked: the accumulator after it. -/
theorem scanPlane_one (m : Mem) (p : Addr) (j b x : Nat) :
    planeWord64 m p j b 0 &&& rowSel x 0 = scanPlane m p j b x 1 := by
  unfold scanPlane rowSel
  by_cases h : x / 8 = 0
  · rw [ite_eq_left h, ite_eq_left (by omega_arith), BitVec.and_allOnes, h]
  · rw [ite_eq_right h, ite_eq_right (by omega_arith)]
    exact BitVec.and_zero

/-- Row `k`, masked, ORed into the accumulator. -/
theorem scanPlane_succ (m : Mem) (p : Addr) (j b x k : Nat) :
    scanPlane m p j b x k ||| (planeWord64 m p j b k &&& rowSel x k) = scanPlane m p j b x (k + 1) := by
  unfold scanPlane rowSel
  by_cases h : x / 8 = k
  · subst h
    rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _),
      BitVec.and_allOnes]
    exact BitVec.zero_or
  · rw [ite_eq_right h, show planeWord64 m p j b k &&& 0 = 0 from BitVec.and_zero,
      show ∀ y : BitVec 64, y ||| 0 = y from fun _ => BitVec.or_zero]
    by_cases h' : x / 8 < k
    · rw [ite_eq_left h', ite_eq_left (by omega_arith)]
    · rw [ite_eq_right h', ite_eq_right (by omega_arith)]

theorem scanPlane_all (m : Mem) (p : Addr) (j b : Nat) (x : Byte) :
    scanPlane m p j b x.toNat 32 = planeWord64 m p j b (x.toNat / 8) := by
  have := x.isLt
  rw [scanPlane, ite_eq_left (by omega_arith)]

/-- Byte `x mod 8` of plane `c`'s doubleword of the row holding `x` is byte
`c` of S-box `j`'s entry `x`. -/
theorem planeWord64_byte (m : Mem) (p : Addr) {j c : Nat} (hj : j < 4) (hc : c < 4) (x : Byte) :
    (planeWord64 m p j c (x.toNat / 8)).extractLsb' (8 * (x.toNat % 8)) 8 =
      (sEntry (scheduleAt m p) j x).extractLsb' (8 * c) 8 := by
  rw [sEntry_byte m p hj hc, planeWord64]
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]
  rw [Mem.extractLsb'_read m _ (Nat.mod_lt _ (by decide)), Offset.add_add]
  congr 3
  omega_arith

end VG.Proof.Blowfish

end

end


/-!
# Blowfish on RISC-V: an S-box lookup

`lookup_run`: `lookup j`, with `a7` at S-box `j` of the schedule at `S`,
leaves S-box `j`'s entry for the byte `3 - j` of xL's low word in the
accumulator's low word, changing only the lookup's registers. The rows
(`Chunk.row_step`, in two passes) leave each plane's doubleword of the
index's row in its accumulator (`scanPlane`, `Proof/Blowfish/Scan64.lean`),
each row's mask being its bit of `2 ^ q` spread over the doubleword
(`Chunk.shifted_mask`); the end (`extract`) shifts each right by `8L` (`lane_val`),
which brings the byte of the index's lane `L` to the bottom (`shr_byte`),
and packs the four bytes into the entry (`pack_byte`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- What a lookup needs: the schedule at `a7` readable a word or a
doubleword at a time, and doubleword-aligned. -/
structure LookEnv (s : State) : Prop where
  rd : ∀ o, o % 4 = 0 → o + 4 ≤ 4168 → InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 o) 4
  rd8 : ∀ o, o % 8 = 0 → o + 8 ≤ 4168 → InRegions (s.rd ++ s.wr) (s.gpr .a7 + BitVec.ofNat 64 o) 8
  al : (s.gpr .a7).toNat % 4 = 0
  al8 : (s.gpr .a7).toNat % 8 = 0

/-- The registers a lookup writes. -/
def lookRegs : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6]

theorem LookEnv.keep {s t : State} (E : LookEnv s) {rs : List Reg} (h : Keep rs s t)
    (h7 : Reg.a7 ∉ rs) : LookEnv t := by
  refine ⟨fun o ha ho => ?_, fun o ha ho => ?_, by rw [h.gpr h7]; exact E.al, by rw [h.gpr h7]; exact E.al8⟩
  · rw [h.gpr h7, h.2.1, h.2.2]; exact E.rd o ha ho
  · rw [h.gpr h7, h.2.1, h.2.2]; exact E.rd8 o ha ho

/-- An 8-byte aligned offset of an 8-byte aligned base. -/
theorem al8_add {p : Addr} (hp : p.toNat % 8 = 0) {d : Nat} (hd : d % 8 = 0) (hd' : d < 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) hd']
  have := p.isLt
  omega_using [hp, hd]

/-- A 4-byte aligned offset of a 4-byte aligned base. -/
theorem al_add {p : Addr} (hp : p.toNat % 4 = 0) {d : Nat} (hd : d % 4 = 0) (hd' : d < 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) hd']
  have := p.isLt
  omega_using [hp, hd]

/-- `a - c` (as doublewords, both below `2 ^ 64`) is nonzero iff `a ≠ c`. -/
theorem ofNat_sub_bne {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c != (0 : BitVec 64)) = !decide (a = c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 c ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at this
      omega_using [ha, hc, h, this]
    rw [decide_eq_false h, Bool.not_false]
    exact bne_iff_ne.mpr this

theorem lo_zero : lo 0#64 = 0#32 := rfl

/-! ## The index -/

theorem index_val (x : BitVec 64) {j : Nat} (hj : j < 4) :
    (x <<< (32 + 8 * j)) >>> 56 = (quarter (lo x) j).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [quarter, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft]
  by_cases h8 : i < 8
  · simp only [h8, decide_true, Bool.true_and, show 56 + i < 64 by omega_using [h8],
      show ¬ (56 + i < 32 + 8 * j) by omega_using [hj], decide_false, Bool.not_false,
      show 8 * (3 - j) + i < 32 by omega_using [h8]]
    rw [decide_eq_true hi, Bool.true_and]
    congr 1; omega_using [hj]
  · simp only [h8, decide_false, Bool.false_and]
    by_cases h : 56 + i < 64
    · omega
    · simp [h]

/-! ## The rows -/

/-- Row `k > 0`: each accumulator ORed with its plane's doubleword, masked. -/
theorem row_run (u : State) {k : Nat} (hk : k < 32) {B q : BitVec 64}
    (h7 : u.gpr .a7 = B) (h1 : u.gpr .t1 = q)
    (r0 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (8 * k)) 8)
    (r1 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (256 + 8 * k)) 8)
    (r2 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (512 + 8 * k)) 8)
    (r3 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (768 + 8 * k)) 8)
    (a0 : (B + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0)
    (a1 : (B + BitVec.ofNat 64 (256 + 8 * k)).toNat % 8 = 0)
    (a2 : (B + BitVec.ofNat 64 (512 + 8 * k)).toNat % 8 = 0)
    (a3 : (B + BitVec.ofNat 64 (768 + 8 * k)).toNat % 8 = 0) :
    WP isa (.block (row k)) u fun t =>
      let M := (q <<< (63 - k)).sshiftRight 63
      t.gpr .t2 = u.gpr .t2 ||| (u.mem.readW (B + BitVec.ofNat 64 (8 * k)) 64 &&& M) ∧
      t.gpr .t5 = u.gpr .t5 ||| (u.mem.readW (B + BitVec.ofNat 64 (256 + 8 * k)) 64 &&& M) ∧
      t.gpr .t6 = u.gpr .t6 ||| (u.mem.readW (B + BitVec.ofNat 64 (512 + 8 * k)) 64 &&& M) ∧
      t.gpr .t0 = u.gpr .t0 ||| (u.mem.readW (B + BitVec.ofNat 64 (768 + 8 * k)) 64 &&& M) ∧
      t.mem = u.mem := by
  unfold row rowMask plane
  brun [accOf, Nat.zero_add, h7, h1, r0, r1, r2, r3, a0, a1, a2, a3, show 63 - k < 64 by omega_using [],
    show 8 * k < 2048 by omega_using [hk], show 256 * 1 + 8 * k < 2048 by omega_using [hk],
    show 256 * 2 + 8 * k < 2048 by omega_using [hk], show 256 * 3 + 8 * k < 2048 by omega_using [hk]]

theorem index_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block (index j)) s fun t =>
      t.gpr .t1 = BitVec.twoPow 64 ((quarter (lo (s.gpr .a3)) j).toNat / 8) ∧ t.mem = s.mem := by
  have e : (s.gpr .a3 <<< (32 + 8 * j)) >>> 59 = BitVec.ofNat 64 ((quarter (lo (s.gpr .a3)) j).toNat / 8) := by
    have h := congrArg (fun v : BitVec 64 => v >>> 3) (index_val (s.gpr .a3) hj)
    rw [← BitVec.shiftRight_add] at h
    rw [h]
    apply BitVec.eq_of_toNat_eq
    have := (quarter (lo (s.gpr .a3)) j).isLt
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  have hq := (quarter (lo (s.gpr .a3)) j).isLt
  unfold index
  brun [show 32 + 8 * j < 64 by omega_using [hj], e]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  rfl

/-- The schedule at `S`, readable a doubleword at a time, and aligned. -/
structure SchAt (s : State) (S : Addr) : Prop where
  rd8 : ∀ o, o % 8 = 0 → o + 8 ≤ 4168 → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 o) 8
  al8 : S.toNat % 8 = 0

theorem lane_val (x : BitVec 64) {j : Nat} (hj : j < 4) :
    ((x >>> (24 - 8 * j)) &&& 7#64) <<< 3 = BitVec.ofNat 64 (8 * ((quarter (lo x) j).toNat % 8)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [quarter, BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  rw [show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    show 24 - 8 * j = 8 * (3 - j) by omega]
  have e32 : (2 : Nat) ^ 32 = 2 ^ (8 * (3 - j)) * 2 ^ (32 - 8 * (3 - j)) := by
    rw [← Nat.pow_add]; congr 1; omega_using []
  rw [e32, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2 ^ 8),
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_using [] : 3 ≤ 32 - 8 * (3 - j)))]
  generalize x.toNat / 2 ^ (8 * (3 - j)) = n
  have : n % 8 < 8 := Nat.mod_lt _ (by decide)
  show n % 8 * 8 % 2 ^ 64 = 8 * (n % 8) % 2 ^ 64
  rw [Nat.mul_comm]

theorem lane_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block [.shift .srl .d mReg xL (24 - 8 * j), .logicImm .and mReg mReg 7,
      .shift .sll .d mReg mReg 3]) s fun t =>
      t.gpr .t3 = BitVec.ofNat 64 (8 * ((quarter (lo (s.gpr .a3)) j).toNat % 8)) ∧ t.mem = s.mem := by
  rw [← lane_val _ hj]
  brun [show 24 - 8 * j < 64 by omega_using []]

theorem pick_run (u : State) {K A0 A1 A2 A3 : BitVec 64} (h3 : u.gpr .t3 = K) (h2 : u.gpr .t2 = A0)
    (h5 : u.gpr .t5 = A1) (h6 : u.gpr .t6 = A2) (h0 : u.gpr .t0 = A3) :
    WP isa (.block (pick 0 ++ pick 1 ++ pick 2 ++ pick 3 ++
      ([.logic .or acc acc (accOf 1), .logic .or (accOf 2) (accOf 2) (accOf 3), .logic .or acc acc (accOf 2)] :
        List Instr))) u fun t =>
      t.gpr .t2 = ((A0 >>> (K.toNat % 64) &&& 255#64) ||| (A1 >>> (K.toNat % 64) &&& 255#64) <<< 8) |||
        ((A2 >>> (K.toNat % 64) &&& 255#64) <<< 16 ||| (A3 >>> (K.toNat % 64) &&& 255#64) <<< 24) ∧
        t.mem = u.mem := by
  unfold pick
  brun [accOf, h3, h2, h5, h6, h0]

/-- A doubleword shifted right by `8L` and masked: its byte `L`. -/
theorem shr_byte (a : BitVec 64) (L : Nat) :
    (a >>> (8 * L)) &&& 255#64 = (a.extractLsb' (8 * L) 8).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb']
  by_cases h8 : i < 8
  · have : (255#64).getLsbD i = true := by
      rcases (by omega_using [h8] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    rw [this, Bool.and_true, decide_eq_true h8, decide_eq_true hi, Bool.true_and, Bool.true_and, Nat.add_comm]
  · have : (255#64).getLsbD i = false := by
      rw [BitVec.getLsbD_ofNat]; simp only [Bool.and_eq_false_iff]; right
      rw [Nat.testBit_lt_two_pow (by have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega_using [h8] : 8 ≤ i); omega_using [this])]
    rw [this, Bool.and_false, decide_eq_false h8, Bool.false_and, Bool.and_false]

/-- The low word of four bytes ORed into place. -/
theorem pack_byte (y : Nat → Byte) {c : Nat} (hc : c < 4) :
    (lo ((((y 0).setWidth 64 ||| (y 1).setWidth 64 <<< 8) |||
      ((y 2).setWidth 64 <<< 16 ||| (y 3).setWidth 64 <<< 24)))).extractLsb' (8 * c) 8 = y c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rcases (by omega_using [hc] : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and, Bool.and_true,
      Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false,
      Nat.add_sub_cancel_left, Nat.zero_add, BitVec.getLsbD_of_ge, Nat.reduceMul]


end VG.Proof.Blowfish.RISCV64

end

end


@[expose] public section
namespace VG.Proof.Blowfish.RISCV64
open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- The registers the lookups of both blocks write. -/
def lookRegs2 : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .s4, .s5, .s6, .s7, .s8, .s9, .s10]

/-! ## Two blocks: the indices -/

theorem index2_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block (index2 j)) s fun t =>
      t.gpr .s4 = BitVec.twoPow 64 ((quarter (lo (s.gpr .s1)) j).toNat / 8) ∧ t.mem = s.mem := by
  obtain e : (s.gpr .s1 <<< (32 + 8 * j)) >>> 59 = BitVec.ofNat 64 ((quarter (lo (s.gpr .s1)) j).toNat / 8) := by
    obtain h := congrArg (fun v : BitVec 64 => v >>> 3) (index_val (s.gpr .s1) hj)
    rw [← BitVec.shiftRight_add] at h
    rw [h]
    apply BitVec.eq_of_toNat_eq
    have := (quarter (lo (s.gpr .s1)) j).isLt
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  obtain hq := (quarter (lo (s.gpr .s1)) j).isLt
  unfold index2
  brun [xL2, qReg2, mReg2, show 32 + 8 * j < 64 by omega_using [hj], e]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  rfl

/-! ## Two blocks: the rows -/

/-- Row `k > 0` for both blocks. -/
theorem row2_run (u : State) {k : Nat} (hk : k < 32) {B q q' : BitVec 64}
    (h7 : u.gpr .a7 = B) (h1 : u.gpr .t1 = q) (h4 : u.gpr .s4 = q')
    (r0 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (8 * k)) 8)
    (r1 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (256 + 8 * k)) 8)
    (r2 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (512 + 8 * k)) 8)
    (r3 : InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (768 + 8 * k)) 8)
    (a0 : (B + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0)
    (a1 : (B + BitVec.ofNat 64 (256 + 8 * k)).toNat % 8 = 0)
    (a2 : (B + BitVec.ofNat 64 (512 + 8 * k)).toNat % 8 = 0)
    (a3 : (B + BitVec.ofNat 64 (768 + 8 * k)).toNat % 8 = 0) :
    WP isa (.block (row2 k)) u fun t =>
      let M := (q <<< (63 - k)).sshiftRight 63
      let M' := (q' <<< (63 - k)).sshiftRight 63
      t.gpr .t2 = u.gpr .t2 ||| (u.mem.readW (B + BitVec.ofNat 64 (8 * k)) 64 &&& M) ∧
      t.gpr .t5 = u.gpr .t5 ||| (u.mem.readW (B + BitVec.ofNat 64 (256 + 8 * k)) 64 &&& M) ∧
      t.gpr .t6 = u.gpr .t6 ||| (u.mem.readW (B + BitVec.ofNat 64 (512 + 8 * k)) 64 &&& M) ∧
      t.gpr .t0 = u.gpr .t0 ||| (u.mem.readW (B + BitVec.ofNat 64 (768 + 8 * k)) 64 &&& M) ∧
      t.gpr .s6 = u.gpr .s6 ||| (u.mem.readW (B + BitVec.ofNat 64 (8 * k)) 64 &&& M') ∧
      t.gpr .s7 = u.gpr .s7 ||| (u.mem.readW (B + BitVec.ofNat 64 (256 + 8 * k)) 64 &&& M') ∧
      t.gpr .s8 = u.gpr .s8 ||| (u.mem.readW (B + BitVec.ofNat 64 (512 + 8 * k)) 64 &&& M') ∧
      t.gpr .s9 = u.gpr .s9 ||| (u.mem.readW (B + BitVec.ofNat 64 (768 + 8 * k)) 64 &&& M') ∧
      t.mem = u.mem := by
  unfold row2 rowMask2 rowMask plane2
  brun [accOf, accOf2, qReg2, mReg2, tmp2, Nat.zero_add, h7, h1, h4, r0, r1, r2, r3, a0, a1, a2, a3,
    show 63 - k < 64 by omega_using [],
    show 8 * k < 2048 by omega_using [hk], show 256 * 1 + 8 * k < 2048 by omega_using [hk],
    show 256 * 2 + 8 * k < 2048 by omega_using [hk], show 256 * 3 + 8 * k < 2048 by omega_using [hk]]

theorem lane2_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block [.shift .srl .d mReg2 xL2 (24 - 8 * j), .logicImm .and mReg2 mReg2 7,
      .shift .sll .d mReg2 mReg2 3]) s fun t =>
      t.gpr .s5 = BitVec.ofNat 64 (8 * ((quarter (lo (s.gpr .s1)) j).toNat % 8)) ∧ t.mem = s.mem := by
  rw [← lane_val _ hj]
  brun [mReg2, xL2, show 24 - 8 * j < 64 by omega_using []]

theorem pick2_run (u : State) {K A0 A1 A2 A3 : BitVec 64} (h3 : u.gpr .s5 = K) (h2 : u.gpr .s6 = A0)
    (h5 : u.gpr .s7 = A1) (h6 : u.gpr .s8 = A2) (h0 : u.gpr .s9 = A3) :
    WP isa (.block (pick2 0 ++ pick2 1 ++ pick2 2 ++ pick2 3 ++
      ([.logic .or (accOf2 0) (accOf2 0) (accOf2 1), .logic .or (accOf2 2) (accOf2 2) (accOf2 3),
        .logic .or (accOf2 0) (accOf2 0) (accOf2 2)] : List Instr))) u fun t =>
      t.gpr .s6 = ((A0 >>> (K.toNat % 64) &&& 255#64) ||| (A1 >>> (K.toNat % 64) &&& 255#64) <<< 8) |||
        ((A2 >>> (K.toNat % 64) &&& 255#64) <<< 16 ||| (A3 >>> (K.toNat % 64) &&& 255#64) <<< 24) ∧
        t.mem = u.mem := by
  unfold pick2
  brun [accOf2, mReg2, h3, h2, h5, h6, h0]

/-- The entry of S-box `j` for `idx`, from the accumulators of the four
planes after the 32 rows, shifted by `8 (idx mod 8)`. -/
theorem entry_eq (m : Mem) (S : Addr) {j : Nat} (hj : j < 4) (idx : Byte) {K : BitVec 64}
    (hK : K.toNat % 64 = 8 * (idx.toNat % 8)) :
    lo (((scanPlane m S j 0 idx.toNat 32 >>> (K.toNat % 64) &&& 255#64) |||
        (scanPlane m S j 1 idx.toNat 32 >>> (K.toNat % 64) &&& 255#64) <<< 8) |||
      ((scanPlane m S j 2 idx.toNat 32 >>> (K.toNat % 64) &&& 255#64) <<< 16 |||
        (scanPlane m S j 3 idx.toNat 32 >>> (K.toNat % 64) &&& 255#64) <<< 24)) =
      sEntry (scheduleAt m S) j idx := by
  rw [hK, scanPlane_all, scanPlane_all, scanPlane_all, scanPlane_all, shr_byte, shr_byte,
    shr_byte, shr_byte]
  refine word_ext fun c hc => ?_
  obtain e := pack_byte (fun b => (planeWord64 m S j b (idx.toNat / 8)).extractLsb' (8 * (idx.toNat % 8)) 8) hc
  rw [e, planeWord64_byte _ _ hj hc]


end VG.Proof.Blowfish.RISCV64

@[expose] public section
namespace VG.Proof.Blowfish.RISCV64.Chunk
open VG VG.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish VG.Proof.Blowfish.RISCV64
open VG.Impl.Blowfish.RISCV64

theorem mask128 (x : BitVec 64) :
    x &&& 128 = if (x.setWidth 8).toNat < 128 then 0 else 128 := by
  rw [show (128 : BitVec 64) = BitVec.twoPow 64 7 from rfl, BitVec.and_twoPow]
  have h7 : x.getLsbD 7 = (x.setWidth 8).msb := by
    simp only [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth]
    simp
  rw [h7, BitVec.msb_eq_decide]
  by_cases h : (x.setWidth 8).toNat < 128
  · simp only [show ¬128 ≤ (x.setWidth 8).toNat by omega_using [h], decide_false, Bool.false_eq_true,
      ite_false, h, ite_true]
    rfl
  · simp only [show 128 ≤ (x.setWidth 8).toNat by omega_using [h], decide_true, ite_true, h, ite_false]

theorem scan_counter {p b : BitVec 64} (h : ((p - b).setWidth 8).toNat < 128) {c j : Nat} (hc : c < 2) :
    (p - (b + BitVec.ofNat 64 (1024 * j + 128 * (c + 1)))) &&& 128 = if c = 0 then 128 else 0 := by
  rw [mask128]
  rcases (show c = 0 ∨ c = 1 by omega_using [hc]) with rfl | rfl
  · have hn : ¬ ((p - (b + BitVec.ofNat 64 (1024 * j + 128 * (0 + 1)))).setWidth 8).toNat < 128 := by bv_omega
    simp only [hn, ite_false, ite_true]
  · have hn : ((p - (b + BitVec.ofNat 64 (1024 * j + 128 * (1 + 1)))).setWidth 8).toNat < 128 := by bv_omega
    simp only [hn, ite_true, Nat.one_ne_zero, ite_false]

theorem shifted_mask (x : Byte) {c k : Nat} (hc : c < 2) (hk : k < 16) :
    ((BitVec.twoPow 64 (x.toNat / 8) >>> (16 * c)) <<< (63 - k)).sshiftRight 63 = rowSel x.toNat (16 * c + k) := by
  rw [bit_mask _ (by omega_using [hk]), BitVec.getLsbD_ushiftRight, BitVec.getLsbD_twoPow, rowSel]
  have hx := x.isLt
  by_cases h : x.toNat / 8 = 16 * c + k
  · simp [h, show 16 * c + k < 64 by omega_using [hc, hk]]
  · simp [h]



structure Inv (R : List Reg) (s₀ : State) (S : Addr) (j : Nat) (idx : Byte) (c k : Nat) (u : State) : Prop where
  q : u.gpr .t1 = BitVec.twoPow 64 (idx.toNat / 8) >>> (16 * c)
  p0 : u.gpr .t2 = scanPlane s₀.mem S j 0 idx.toNat (16 * c + k)
  p1 : u.gpr .t5 = scanPlane s₀.mem S j 1 idx.toNat (16 * c + k)
  p2 : u.gpr .t6 = scanPlane s₀.mem S j 2 idx.toNat (16 * c + k)
  p3 : u.gpr .t0 = scanPlane s₀.mem S j 3 idx.toNat (16 * c + k)
  keep : Keep R s₀ u
  mem : u.mem = s₀.mem
  sch : u.gpr .a7 = S + BitVec.ofNat 64 (1024 * j + 128 * c)

structure Inv2 (s₀ : State) (S : Addr) (j : Nat) (idx idx' : Byte) (c k : Nat) (u : State) : Prop extends
    Inv (.a7 :: lookRegs2) s₀ S j idx c k u where
  q' : u.gpr .s4 = BitVec.twoPow 64 (idx'.toNat / 8) >>> (16 * c)
  p0' : u.gpr .s6 = scanPlane s₀.mem S j 0 idx'.toNat (16 * c + k)
  p1' : u.gpr .s7 = scanPlane s₀.mem S j 1 idx'.toNat (16 * c + k)
  p2' : u.gpr .s8 = scanPlane s₀.mem S j 2 idx'.toNat (16 * c + k)
  p3' : u.gpr .s9 = scanPlane s₀.mem S j 3 idx'.toNat (16 * c + k)

/-- The same 32 table rows, addressed sixteen at a time. -/
theorem row_info {s₀ u : State} {S : Addr} (E : SchAt s₀ S) {j c k : Nat}
    (hj : j < 4) (hc : c < 2) (hk : k < 16) {R : List Reg} (hr : Keep R s₀ u)
    (hm : u.mem = s₀.mem) (h7 : u.gpr .a7 = S + BitVec.ofNat 64 (1024 * j + 128 * c)) :
    ∀ b < 4,
      InRegions (u.rd ++ u.wr) (u.gpr .a7 + BitVec.ofNat 64 (256 * b + 8 * k)) 8 ∧
      (u.gpr .a7 + BitVec.ofNat 64 (256 * b + 8 * k)).toNat % 8 = 0 ∧
      u.mem.readW (u.gpr .a7 + BitVec.ofNat 64 (256 * b + 8 * k)) 64 =
        planeWord64 s₀.mem S j b (16 * c + k) := by
  intro b hb
  have ad : u.gpr .a7 + BitVec.ofNat 64 (256 * b + 8 * k) =
      S + BitVec.ofNat 64 (1024 * j + 256 * b + 8 * (16 * c + k)) := by
    rw [h7, Offset.add_add]
    congr 2
    omega_using []
  rw [ad, hr.2.1, hr.2.2]
  exact ⟨E.rd8 _ (by omega_using []) (by omega_using [hj, hc, hk, hb]),
    al8_add E.al8 (by omega_using []) (by omega_using [hj, hc, hk, hb]), by rw [hm]; rfl⟩

theorem row_step {s₀ : State} {S : Addr} (E : SchAt s₀ S) {j c k : Nat}
    (hj : j < 4) (hc : c < 2) (hk : k < 16) (idx : Byte) {u : State}
    (I : Inv (.a7 :: lookRegs) s₀ S j idx c k u) :
    WP isa (.block (row k)) u (Inv (.a7 :: lookRegs) s₀ S j idx c (k + 1)) := by
  have info := row_info E hj hc hk I.keep I.mem I.sch
  have hr := fun b hb => (info b hb).1
  have hal := fun b hb => (info b hb).2.1
  have pl := fun b hb => (info b hb).2.2
  have r0 := hr 0 (by decide)
  have l0 := hal 0 (by decide)
  have p0 := pl 0 (by decide)
  have r1 := hr 1 (by decide)
  have l1 := hal 1 (by decide)
  have p1 := pl 1 (by decide)
  have r2 := hr 2 (by decide)
  have l2 := hal 2 (by decide)
  have p2 := pl 2 (by decide)
  have r3 := hr 3 (by decide)
  have l3 := hal 3 (by decide)
  have p3 := pl 3 (by decide)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.reduceMul] at r0 l0 p0 r1 l1 p1 r2 l2 p2 r3 l3 p3
  refine WP.mono (WP.keep [.t2, .t3, .t4, .t5, .t6, .t0] (row_run u (by omega_using [hk]) rfl I.q r0 r1 r2 r3 l0 l1 l2 l3)
    (by rfl) rfl) fun t ⟨⟨t2, t5, t6, t0, tm⟩, tk⟩ => ?_
  have M := shifted_mask idx hc hk
  refine ⟨by rw [tk.gpr (by decide), I.q], ?_, ?_, ?_, ?_, I.keep.trans tk |>.mono (by decide), tm.trans I.mem, by rw [tk.gpr (by decide), I.sch]⟩
  · rw [t2, M, p0, I.p0, scanPlane_succ, Nat.add_assoc]
  · rw [t5, M, p1, I.p1, scanPlane_succ, Nat.add_assoc]
  · rw [t6, M, p2, I.p2, scanPlane_succ, Nat.add_assoc]
  · rw [t0, M, p3, I.p3, scanPlane_succ, Nat.add_assoc]


theorem row2_step {s₀ : State} {S : Addr} (E : SchAt s₀ S) {j c k : Nat}
    (hj : j < 4) (hc : c < 2) (hk : k < 16) (idx idx' : Byte) {u : State}
    (I : Inv2 s₀ S j idx idx' c k u) :
    WP isa (.block (row2 k)) u (Inv2 s₀ S j idx idx' c (k + 1)) := by
  have info := row_info E hj hc hk I.keep I.mem I.sch
  have hr := fun b hb => (info b hb).1
  have hal := fun b hb => (info b hb).2.1
  have pl := fun b hb => (info b hb).2.2
  obtain r0 := hr 0 (by decide)
  obtain l0 := hal 0 (by decide)
  obtain p0 := pl 0 (by decide)
  obtain r1 := hr 1 (by decide)
  obtain l1 := hal 1 (by decide)
  obtain p1 := pl 1 (by decide)
  obtain r2 := hr 2 (by decide)
  obtain l2 := hal 2 (by decide)
  obtain p2 := pl 2 (by decide)
  obtain r3 := hr 3 (by decide)
  obtain l3 := hal 3 (by decide)
  obtain p3 := pl 3 (by decide)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.reduceMul] at r0 l0 p0 r1 l1 p1 r2 l2 p2 r3 l3 p3
  refine WP.mono (WP.keep [.t2, .t3, .t4, .t5, .t6, .t0, .s5, .s6, .s7, .s8, .s9, .s10]
    (row2_run u (by omega_using [hk]) rfl I.q I.q' r0 r1 r2 r3 l0 l1 l2 l3)
    (by rfl) rfl) fun t ⟨⟨t2, t5, t6, t0, s6, s7, s8, s9, tm⟩, tk⟩ => ?_
  obtain M := shifted_mask idx hc hk
  obtain M' := shifted_mask idx' hc hk
  refine ⟨⟨by rw [tk.gpr (by decide), I.q], ?_, ?_, ?_, ?_,
    I.keep.trans tk |>.mono (by decide), tm.trans I.mem, by rw [tk.gpr (by decide), I.sch]⟩,
    by rw [tk.gpr (by decide), I.q'], ?_, ?_, ?_, ?_⟩
  · rw [t2, M, p0, I.p0, scanPlane_succ, Nat.add_assoc]
  · rw [t5, M, p1, I.p1, scanPlane_succ, Nat.add_assoc]
  · rw [t6, M, p2, I.p2, scanPlane_succ, Nat.add_assoc]
  · rw [t0, M, p3, I.p3, scanPlane_succ, Nat.add_assoc]
  · rw [s6, M', p0, I.p0', scanPlane_succ, Nat.add_assoc]
  · rw [s7, M', p1, I.p1', scanPlane_succ, Nat.add_assoc]
  · rw [s8, M', p2, I.p2', scanPlane_succ, Nat.add_assoc]
  · rw [s9, M', p3, I.p3', scanPlane_succ, Nat.add_assoc]



def foot : List Instr := [.addi sch sch 128, .shift .srl .d qReg qReg 16,
  .sub tmp pPtr sch, .logicImm .and tmp tmp 128]
def body : Prog isa := .block ((List.range 16).flatMap row ++ foot)

theorem foot_run (u : State) : WP isa (.block foot) u fun t =>
    t.gpr .a7 = u.gpr .a7 + 128 ∧ t.gpr .t1 = u.gpr .t1 >>> 16 ∧
    t.gpr .t4 = (u.gpr .a6 - (u.gpr .a7 + 128)) &&& 128 ∧ t.mem = u.mem := by
  unfold foot
  brun [sch, qReg, tmp, pPtr]
  exact ⟨rfl, rfl⟩

theorem body_run {s₀ : State} {S : Addr} (E : SchAt s₀ S) {j c : Nat}
    (hj : j < 4) (hc : c < 2) (idx : Byte) {u : State}
    (hp : ((s₀.gpr .a6 - S).setWidth 8).toNat < 128)
    (I : Inv (.a7 :: lookRegs) s₀ S j idx c 0 u) :
    WP isa body u fun t => Inv (.a7 :: lookRegs) s₀ S j idx (c + 1) 0 t ∧
      t.gpr .t4 = if c = 0 then 128 else 0 := by
  rw [body, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16)
    (fun k t => Inv (.a7 :: lookRegs) s₀ S j idx c k t)
    (fun k t hk hI => row_step E hj hc hk idx hI) 16 (by decide) u I) fun v V => ?_
  refine WP.mono (WP.keep [.a7, .t1, .t4] (foot_run v) (by rfl) rfl)
    fun t ⟨⟨a7, q, ctr, mem⟩, fk⟩ => ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, V.keep.trans fk |>.mono (by decide), mem.trans V.mem, ?_⟩, ?_⟩
  · rw [q, V.q, ← BitVec.shiftRight_add]
    congr 1
  · rw [fk.gpr (by decide), V.p0]
    congr 1
  · rw [fk.gpr (by decide), V.p1]
    congr 1
  · rw [fk.gpr (by decide), V.p2]
    congr 1
  · rw [fk.gpr (by decide), V.p3]
    congr 1
  · rw [a7, V.sch]
    bv_omega
  · rw [ctr, V.sch, V.keep.gpr (by decide)]
    have hbase : S + BitVec.ofNat 64 (1024 * j + 128 * c) + 128 =
        S + BitVec.ofNat 64 (1024 * j + 128 * (c + 1)) := by bv_omega
    rw [hbase]
    exact scan_counter hp hc

def foot2 : List Instr := [.addi sch sch 128, .shift .srl .d qReg qReg 16, .shift .srl .d qReg2 qReg2 16,
  .sub tmp pPtr sch, .logicImm .and tmp tmp 128]
def body2 : Prog isa := .block ((List.range 16).flatMap row2 ++ foot2)

theorem foot2_run (u : State) : WP isa (.block foot2) u fun t =>
    t.gpr .a7 = u.gpr .a7 + 128 ∧ t.gpr .t1 = u.gpr .t1 >>> 16 ∧ t.gpr .s4 = u.gpr .s4 >>> 16 ∧
    t.gpr .t4 = (u.gpr .a6 - (u.gpr .a7 + 128)) &&& 128 ∧ t.mem = u.mem := by
  unfold foot2
  brun [sch, qReg, qReg2, tmp, pPtr]
  exact ⟨rfl, rfl⟩

theorem body2_run {s₀ : State} {S : Addr} (E : SchAt s₀ S) {j c : Nat}
    (hj : j < 4) (hc : c < 2) (idx idx' : Byte) {u : State}
    (hp : ((s₀.gpr .a6 - S).setWidth 8).toNat < 128)
    (I : Inv2 s₀ S j idx idx' c 0 u) :
    WP isa body2 u fun t => Inv2 s₀ S j idx idx' (c + 1) 0 t ∧
      t.gpr .t4 = if c = 0 then 128 else 0 := by
  rw [body2, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16)
    (fun k t => Inv2 s₀ S j idx idx' c k t)
    (fun k t hk hI => row2_step E hj hc hk idx idx' hI) 16 (by decide) u I) fun v V => ?_
  refine WP.mono (WP.keep [.a7, .t1, .s4, .t4] (foot2_run v) (by rfl) rfl)
    fun t ⟨⟨a7, q, q', ctr, mem⟩, fk⟩ => ?_
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, V.keep.trans fk |>.mono (by decide), mem.trans V.mem, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [q, V.q, ← BitVec.shiftRight_add]
    congr 1
  · rw [fk.gpr (by decide), V.p0]
    congr 1
  · rw [fk.gpr (by decide), V.p1]
    congr 1
  · rw [fk.gpr (by decide), V.p2]
    congr 1
  · rw [fk.gpr (by decide), V.p3]
    congr 1
  · rw [a7, V.sch]
    bv_omega
  · rw [q', V.q', ← BitVec.shiftRight_add]
    congr 1
  · rw [fk.gpr (by decide), V.p0']
    congr 1
  · rw [fk.gpr (by decide), V.p1']
    congr 1
  · rw [fk.gpr (by decide), V.p2']
    congr 1
  · rw [fk.gpr (by decide), V.p3']
    congr 1
  · rw [ctr, V.sch, V.keep.gpr (by decide)]
    have hbase : S + BitVec.ofNat 64 (1024 * j + 128 * c) + 128 =
        S + BitVec.ofNat 64 (1024 * j + 128 * (c + 1)) := by bv_omega
    rw [hbase]
    exact scan_counter hp hc


/-- A two-pass scan with a public, nonzero/zero loop test. -/
theorem loop2_ok {P : Nat → State → Prop} {code : Prog isa}
    (step : ∀ c, c < 2 → ∀ s, P c s → WP isa code s fun t => P (c + 1) t ∧
      t.gpr .t4 = if c = 0 then 128 else 0) {s : State} (h : P 0 s) :
    WP isa (.loop code (.nonzero .t4)) s (P 2) := by
  refine WP.loop (M := isa) (Q := P 2)
    (fun n t => ∃ c, c < 2 ∧ n = 2 - c ∧ P c t) ?_ 2 s ⟨0, by decide, rfl, h⟩
  intro n u ⟨c, hc, hn, I⟩
  refine WP.mono (step c hc u I) fun t ⟨T, ctr⟩ => ?_
  rw [Steps.eval_nonzero, ctr]
  rcases (show c = 0 ∨ c = 1 by omega_using [hc]) with rfl | rfl
  · right
    exact ⟨by decide, 1, by omega_using [hn], 1, by decide, by decide, T⟩
  · left
    exact ⟨by decide, T⟩


def zeros : List Instr := [.li .t2 0, .li .t5 0, .li .t6 0, .li .t0 0]
def zeros2 : List Instr := zeros ++ [.li .s6 0, .li .s7 0, .li .s8 0, .li .s9 0]
def restore : Prog isa := .block [.addi sch sch (-256)]
def scan : Prog isa := .seq (.block zeros) (.seq (.loop body (.nonzero .t4)) restore)
def scan2 : Prog isa := .seq (.block zeros2) (.seq (.loop body2 (.nonzero .t4)) restore)

theorem zeros_run (u : State) : WP isa (.block zeros) u fun t =>
    t.gpr .t2 = 0 ∧ t.gpr .t5 = 0 ∧ t.gpr .t6 = 0 ∧ t.gpr .t0 = 0 ∧ t.mem = u.mem := by
  unfold zeros
  brun []
  rfl

theorem zeros2_run (u : State) : WP isa (.block zeros2) u fun t =>
    t.gpr .t2 = 0 ∧ t.gpr .t5 = 0 ∧ t.gpr .t6 = 0 ∧ t.gpr .t0 = 0 ∧
    t.gpr .s6 = 0 ∧ t.gpr .s7 = 0 ∧ t.gpr .s8 = 0 ∧ t.gpr .s9 = 0 ∧ t.mem = u.mem := by
  unfold zeros2 zeros
  brun []
  rfl

theorem restore_run (u : State) : WP isa restore u fun t =>
    t.gpr .a7 = u.gpr .a7 - 256 ∧ t.mem = u.mem := by
  unfold restore
  brun [sch]
  bv_omega

/-- Restoring the S-box pointer removes it from the final register clobbers. -/
theorem finish {R : List Reg} {s₀ u : State} {S : Addr} {j : Nat} {idx : Byte}
    (I : Inv (.a7 :: R) s₀ S j idx 2 0 u)
    (h7 : s₀.gpr .a7 = S + BitVec.ofNat 64 (1024 * j)) :
    WP isa restore u fun t => Keep R s₀ t ∧ t.mem = s₀.mem ∧
      ∀ r, r ≠ .a7 → t.gpr r = u.gpr r := by
  refine WP.mono (WP.keep [.a7] (restore_run u) (by rfl) rfl) fun t ⟨⟨a7, mem⟩, rk⟩ => ?_
  have K : Keep (.a7 :: R) s₀ t := I.keep.trans rk |>.mono (by simp [or_comm])
  refine ⟨⟨fun r hr => ?_, K.2.1, K.2.2⟩, mem.trans I.mem, fun r hr => rk.gpr (by simpa using hr)⟩
  by_cases h : r = .a7
  · subst r
    rw [a7, I.sch, h7]
    bv_omega
  · exact K.gpr (by simp only [List.mem_cons, not_or]; exact ⟨h, hr⟩)

structure Result (R : List Reg) (s₀ : State) (S : Addr) (j : Nat) (idx : Byte) (u : State) : Prop where
  p0 : u.gpr .t2 = scanPlane s₀.mem S j 0 idx.toNat 32
  p1 : u.gpr .t5 = scanPlane s₀.mem S j 1 idx.toNat 32
  p2 : u.gpr .t6 = scanPlane s₀.mem S j 2 idx.toNat 32
  p3 : u.gpr .t0 = scanPlane s₀.mem S j 3 idx.toNat 32
  keep : Keep R s₀ u
  mem : u.mem = s₀.mem

structure Result2 (s₀ : State) (S : Addr) (j : Nat) (idx idx' : Byte) (u : State) : Prop extends
    Result lookRegs2 s₀ S j idx u where
  p0' : u.gpr .s6 = scanPlane s₀.mem S j 0 idx'.toNat 32
  p1' : u.gpr .s7 = scanPlane s₀.mem S j 1 idx'.toNat 32
  p2' : u.gpr .s8 = scanPlane s₀.mem S j 2 idx'.toNat 32
  p3' : u.gpr .s9 = scanPlane s₀.mem S j 3 idx'.toNat 32

theorem scan_run {s₀ u : State} {S : Addr} (E : SchAt s₀ S) {j : Nat} (hj : j < 4) (idx : Byte)
    (hq : u.gpr .t1 = BitVec.twoPow 64 (idx.toNat / 8)) (K : Keep lookRegs s₀ u) (hm : u.mem = s₀.mem)
    (h7 : s₀.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (hp : ((s₀.gpr .a6 - S).setWidth 8).toNat < 128) :
    WP isa scan u (Result lookRegs s₀ S j idx) := by
  rw [scan]
  refine WP.seq (WP.mono (WP.keep [.t2, .t5, .t6, .t0] (zeros_run u) (by rfl) rfl)
    fun v ⟨⟨z0, z1, z2, z3, vm⟩, zk⟩ => ?_)
  have I : Inv (.a7 :: lookRegs) s₀ S j idx 0 0 v :=
    ⟨by simpa using (zk.gpr (by decide)).trans hq,
      by simpa [scanPlane] using z0, by simpa [scanPlane] using z1,
      by simpa [scanPlane] using z2, by simpa [scanPlane] using z3,
      K.trans zk |>.mono (by decide), vm.trans hm,
      by simpa using (zk.gpr (by decide)).trans ((K.gpr (by decide)).trans h7)⟩
  refine WP.seq (WP.mono (loop2_ok (fun c hc s hs => body_run E hj hc idx hp hs) I) fun w W => ?_)
  refine WP.mono (finish W h7) fun t ⟨tk, tm, regs⟩ => ?_
  exact ⟨(regs _ (by decide)).trans W.p0, (regs _ (by decide)).trans W.p1,
    (regs _ (by decide)).trans W.p2, (regs _ (by decide)).trans W.p3, tk, tm⟩

theorem scan2_run {s₀ u : State} {S : Addr} (E : SchAt s₀ S) {j : Nat} (hj : j < 4) (idx idx' : Byte)
    (hq : u.gpr .t1 = BitVec.twoPow 64 (idx.toNat / 8))
    (hq' : u.gpr .s4 = BitVec.twoPow 64 (idx'.toNat / 8))
    (K : Keep lookRegs2 s₀ u) (hm : u.mem = s₀.mem)
    (h7 : s₀.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (hp : ((s₀.gpr .a6 - S).setWidth 8).toNat < 128) :
    WP isa scan2 u (Result2 s₀ S j idx idx') := by
  rw [scan2]
  refine WP.seq (WP.mono (WP.keep [.t2, .t5, .t6, .t0, .s6, .s7, .s8, .s9] (zeros2_run u) (by rfl) rfl)
    fun v ⟨⟨z0, z1, z2, z3, z0', z1', z2', z3', vm⟩, zk⟩ => ?_)
  have I : Inv2 s₀ S j idx idx' 0 0 v :=
    ⟨⟨by simpa using (zk.gpr (by decide)).trans hq,
      by simpa [scanPlane] using z0, by simpa [scanPlane] using z1,
      by simpa [scanPlane] using z2, by simpa [scanPlane] using z3,
      K.trans zk |>.mono (by decide), vm.trans hm,
      by simpa using (zk.gpr (by decide)).trans ((K.gpr (by decide)).trans h7)⟩,
      by simpa using (zk.gpr (by decide)).trans hq',
      by simpa [scanPlane] using z0', by simpa [scanPlane] using z1',
      by simpa [scanPlane] using z2', by simpa [scanPlane] using z3'⟩
  refine WP.seq (WP.mono (loop2_ok (fun c hc s hs => body2_run E hj hc idx idx' hp hs) I) fun w W => ?_)
  refine WP.mono (finish W.toInv h7) fun t ⟨tk, tm, regs⟩ => ?_
  exact ⟨⟨(regs _ (by decide)).trans W.p0, (regs _ (by decide)).trans W.p1,
    (regs _ (by decide)).trans W.p2, (regs _ (by decide)).trans W.p3, tk, tm⟩,
    (regs _ (by decide)).trans W.p0', (regs _ (by decide)).trans W.p1',
    (regs _ (by decide)).trans W.p2', (regs _ (by decide)).trans W.p3'⟩


def lookupChunk (j : Nat) : Prog isa := .seq (.block (index j)) (.seq scan (.block (extract j)))
def lookupChunk2 (j : Nat) : Prog isa :=
  .seq (.block (index j ++ index2 j)) (.seq scan2 (.block (extract j ++ extractB j)))

theorem lookupChunk_ok {s : State} {S : Addr} (E : SchAt s S) {j : Nat} (hj : j < 4)
    (h7 : s.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (hp : ((s.gpr .a6 - S).setWidth 8).toNat < 128) :
    WP isa (lookupChunk j) s fun t =>
      lo (t.gpr .t2) = sEntry (scheduleAt s.mem S) j (quarter (lo (s.gpr .a3)) j) ∧
        Keep lookRegs s t ∧ t.mem = s.mem := by
  let idx := quarter (lo (s.gpr .a3)) j
  rw [lookupChunk]
  refine WP.seq (WP.mono (WP.keep [.t1, .t3] (index_run s hj) (by rfl) rfl) fun u ⟨⟨u1, um⟩, uk⟩ => ?_)
  have uk' : Keep lookRegs s u := uk.mono (by decide)
  refine WP.seq (WP.mono (scan_run E hj idx u1 uk' um h7 hp) fun v V => ?_)
  unfold extract
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t3] (lane_run v hj) (by rfl) rfl) fun w ⟨⟨w3, wm⟩, wk⟩ => ?_
  have hv3 : v.gpr .a3 = s.gpr .a3 := V.keep.gpr (by decide)
  have hK : (w.gpr .t3).toNat % 64 = 8 * (idx.toNat % 8) := by
    have := idx.isLt
    rw [w3, hv3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  simp only [← List.append_assoc]
  refine WP.mono (WP.keep [.t2, .t5, .t6, .t0] (pick_run w rfl
    ((wk.gpr (by decide)).trans V.p0) ((wk.gpr (by decide)).trans V.p1)
    ((wk.gpr (by decide)).trans V.p2) ((wk.gpr (by decide)).trans V.p3)) (by rfl) rfl)
    fun t ⟨⟨t2, tm⟩, tk⟩ => ?_
  refine ⟨?_, (V.keep.trans wk).trans tk |>.mono (by decide), by rw [tm, wm, V.mem]⟩
  rw [t2, hK, scanPlane_all, scanPlane_all, scanPlane_all, scanPlane_all, shr_byte, shr_byte,
    shr_byte, shr_byte]
  refine word_ext fun c hc => ?_
  have e := pack_byte (fun b => (planeWord64 s.mem S j b (idx.toNat / 8)).extractLsb' (8 * (idx.toNat % 8)) 8) hc
  rw [e, planeWord64_byte _ _ hj hc]

theorem lookupChunk2_ok {s : State} {S : Addr} (E : SchAt s S) {j : Nat} (hj : j < 4)
    (h7 : s.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (hp : ((s.gpr .a6 - S).setWidth 8).toNat < 128) :
    WP isa (lookupChunk2 j) s fun t =>
      lo (t.gpr .t2) = sEntry (scheduleAt s.mem S) j (quarter (lo (s.gpr .a3)) j) ∧
      lo (t.gpr .s6) = sEntry (scheduleAt s.mem S) j (quarter (lo (s.gpr .s1)) j) ∧
        Keep lookRegs2 s t ∧ t.mem = s.mem := by
  let idx := quarter (lo (s.gpr .a3)) j
  let idx' := quarter (lo (s.gpr .s1)) j
  obtain hx : extract j ++ extractB j =
      [.shift .srl .d mReg xL (24 - 8 * j), .logicImm .and mReg mReg 7, .shift .sll .d mReg mReg 3] ++
      ((pick 0 ++ pick 1 ++ pick 2 ++ pick 3 ++
        ([.logic .or acc acc (accOf 1), .logic .or (accOf 2) (accOf 2) (accOf 3), .logic .or acc acc (accOf 2)] :
          List Instr)) ++
      ([.shift .srl .d mReg2 xL2 (24 - 8 * j), .logicImm .and mReg2 mReg2 7, .shift .sll .d mReg2 mReg2 3] ++
      (pick2 0 ++ pick2 1 ++ pick2 2 ++ pick2 3 ++
      ([.logic .or (accOf2 0) (accOf2 0) (accOf2 1), .logic .or (accOf2 2) (accOf2 2) (accOf2 3),
        .logic .or (accOf2 0) (accOf2 0) (accOf2 2)] : List Instr)))) := by
    simp only [extract, extractB, List.append_assoc]
  rw [lookupChunk2]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t1, .t3] (index_run s hj) (by rfl) rfl) fun u₀ ⟨⟨u1, um₀⟩, uk₀⟩ => ?_
  refine WP.mono (WP.keep [.s4, .s5] (index2_run u₀ hj) (by rfl) rfl) fun u ⟨⟨u4, um⟩, uk⟩ => ?_
  have e1 : u₀.gpr .s1 = s.gpr .s1 := uk₀.gpr (by decide)
  rw [e1] at u4
  have u1' : u.gpr .t1 = BitVec.twoPow 64 (idx.toNat / 8) := by rw [uk.gpr (by decide), u1]
  have uk' : Keep lookRegs2 s u := (uk₀.trans uk).mono (by decide)
  refine WP.seq (WP.mono (scan2_run E hj idx idx' u1' u4 uk' (um.trans um₀) h7 hp) fun v V => ?_)
  rw [hx, WP.block_append_iff]
  refine WP.mono (WP.keep [.t3] (lane_run v hj) (by rfl) rfl) fun w ⟨⟨w3, wm⟩, wk⟩ => ?_
  obtain hv3 : v.gpr .a3 = s.gpr .a3 := V.keep.gpr (by decide)
  obtain hK : (w.gpr .t3).toNat % 64 = 8 * (idx.toNat % 8) := by
    have := idx.isLt
    rw [w3, hv3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2, .t5, .t6, .t0] (pick_run w rfl
    ((wk.gpr (by decide)).trans V.p0) ((wk.gpr (by decide)).trans V.p1)
    ((wk.gpr (by decide)).trans V.p2) ((wk.gpr (by decide)).trans V.p3)) (by rfl) rfl)
    fun x ⟨⟨x2, xm⟩, xk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.s5] (lane2_run x hj) (by rfl) rfl) fun y ⟨⟨y5, ym⟩, yk⟩ => ?_
  obtain hx1 : x.gpr .s1 = s.gpr .s1 := by
    rw [xk.gpr (by decide), wk.gpr (by decide), V.keep.gpr (by decide)]
  obtain hK' : (y.gpr .s5).toNat % 64 = 8 * (idx'.toNat % 8) := by
    have := idx'.isLt
    rw [y5, hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  obtain g : ∀ r, r ∉ [Reg.s5] → r ∉ [Reg.t2, .t5, .t6, .t0] → r ∉ [Reg.t3] → y.gpr r = v.gpr r :=
    fun r h1 h2 h3 => by rw [yk.gpr h1, xk.gpr h2, wk.gpr h3]
  refine WP.mono (WP.keep [.s6, .s7, .s8, .s9] (pick2_run y rfl
    ((g .s6 (by decide) (by decide) (by decide)).trans V.p0')
    ((g .s7 (by decide) (by decide) (by decide)).trans V.p1')
    ((g .s8 (by decide) (by decide) (by decide)).trans V.p2')
    ((g .s9 (by decide) (by decide) (by decide)).trans V.p3')) (by rfl) rfl)
    fun t ⟨⟨t6, tm⟩, tk⟩ => ?_
  refine ⟨?_, ?_, (((V.keep.trans wk).trans xk).trans yk).trans tk |>.mono (by decide),
    by rw [tm, ym, xm, wm, V.mem]⟩
  · rw [tk.gpr (by decide), yk.gpr (by decide), x2]
    exact entry_eq s.mem S hj idx hK
  · rw [t6]
    exact entry_eq s.mem S hj idx' hK'

end VG.Proof.Blowfish.RISCV64.Chunk

@[expose] public section
namespace VG.Proof.Blowfish.RISCV64
open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

theorem lookup_run {s : State} {S : Addr} (E : SchAt s S) {j : Nat} (hj : j < 4)
    (h7 : s.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (phase : ((s.gpr .a6 - S).setWidth 8).toNat < 128) :
    WP isa (lookup j) s fun t =>
      lo (t.gpr .t2) = sEntry (scheduleAt s.mem S) j (quarter (lo (s.gpr .a3)) j) ∧
        Keep lookRegs s t ∧ t.mem = s.mem := Chunk.lookupChunk_ok E hj h7 phase

theorem lookup2_run {s : State} {S : Addr} (E : SchAt s S) {j : Nat} (hj : j < 4)
    (h7 : s.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (phase : ((s.gpr .a6 - S).setWidth 8).toNat < 128) :
    WP isa (lookup2 j) s fun t =>
      lo (t.gpr .t2) = sEntry (scheduleAt s.mem S) j (quarter (lo (s.gpr .a3)) j) ∧
      lo (t.gpr .s6) = sEntry (scheduleAt s.mem S) j (quarter (lo (s.gpr .s1)) j) ∧
        Keep lookRegs2 s t ∧ t.mem = s.mem := Chunk.lookupChunk2_ok E hj h7 phase

end VG.Proof.Blowfish.RISCV64
