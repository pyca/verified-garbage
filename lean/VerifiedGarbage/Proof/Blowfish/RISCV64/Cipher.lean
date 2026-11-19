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
(`row_step`, by induction in `rows_run`) leave each plane's doubleword of the
index's row in its accumulator (`scanPlane`, `Proof/Blowfish/Scan64.lean`),
each row's mask being its bit of `2 ^ q` spread over the doubleword
(`mask_eq`); the end (`extract`) shifts each right by `8L` (`lane_val`),
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

/-- Row 0: each accumulator its plane's doubleword, masked. -/
theorem row0_run (u : State) {B q : BitVec 64}
    (h7 : u.gpr .a7 = B) (h1 : u.gpr .t1 = q)
    (r0 : InRegions (u.rd ++ u.wr) B 8)
    (r1 : InRegions (u.rd ++ u.wr) (B + 256#64) 8)
    (r2 : InRegions (u.rd ++ u.wr) (B + 512#64) 8)
    (r3 : InRegions (u.rd ++ u.wr) (B + 768#64) 8)
    (a0 : B.toNat % 8 = 0) (a1 : (B + 256#64).toNat % 8 = 0)
    (a2 : (B + 512#64).toNat % 8 = 0) (a3 : (B + 768#64).toNat % 8 = 0) :
    WP isa (.block row0) u fun t =>
      let M := (q <<< (63 - 0)).sshiftRight 63
      t.gpr .t2 = u.mem.readW B 64 &&& M ∧ t.gpr .t5 = u.mem.readW (B + 256#64) 64 &&& M ∧
      t.gpr .t6 = u.mem.readW (B + 512#64) 64 &&& M ∧ t.gpr .t0 = u.mem.readW (B + 768#64) 64 &&& M ∧
      t.mem = u.mem := by
  unfold row0 rowMask firstPlane
  brun [accOf, h7, h1, r0, r1, r2, r3, a0, a1, a2, a3]

/-- The row's mask, from the bit of the index's row in `t1`. -/
theorem mask_eq (x : Byte) {k : Nat} (hk : k < 32) :
    (BitVec.twoPow 64 (x.toNat / 8) <<< (63 - k)).sshiftRight 63 = rowSel x.toNat k := by
  rw [bit_mask _ (by omega_using [hk]), BitVec.getLsbD_twoPow, rowSel]
  by_cases h : x.toNat / 8 = k
  · subst h; simp only [ite_true, decide_eq_true (by omega_using [] : x.toNat / 8 < 64), Bool.true_and, decide_true]
  · simp [h]

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

/-- After rows `0, …, n - 1` of S-box `j` of the schedule at `S` for the
index `idx`, from the lookup's start `s₀`. -/
structure RowInv (s₀ : State) (S : Addr) (j : Nat) (idx : Byte) (n : Nat) (u : State) : Prop where
  q : u.gpr .t1 = BitVec.twoPow 64 (idx.toNat / 8)
  p0 : u.gpr .t2 = scanPlane s₀.mem S j 0 idx.toNat n
  p1 : u.gpr .t5 = scanPlane s₀.mem S j 1 idx.toNat n
  p2 : u.gpr .t6 = scanPlane s₀.mem S j 2 idx.toNat n
  p3 : u.gpr .t0 = scanPlane s₀.mem S j 3 idx.toNat n
  keep : Keep lookRegs s₀ u
  mem : u.mem = s₀.mem

/-- The address of plane `b`'s doubleword of row `k`. -/
theorem plane_addr (S : Addr) (j b k : Nat) (_ : 1024 * j + 256 * b + 8 * k < 2 ^ 64) :
    S + BitVec.ofNat 64 (1024 * j) + BitVec.ofNat 64 (256 * b + 8 * k) =
      S + BitVec.ofNat 64 (1024 * j + 256 * b + 8 * k) :=
  Offset.add_add_eq _ (by omega_using [])

theorem row0_step {s₀ : State} {S : Addr} (E : SchAt s₀ S) {j : Nat} (hj : j < 4) (idx : Byte)
    {u : State} (h7 : u.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (hq : u.gpr .t1 = BitVec.twoPow 64 (idx.toNat / 8)) (hk : Keep lookRegs s₀ u) (hm : u.mem = s₀.mem) :
    WP isa (.block row0) u (RowInv s₀ S j idx 1) := by
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [hk.2.1, hk.2.2]
  let B := S + BitVec.ofNat 64 (1024 * j)
  have ad : ∀ b < 4, B + BitVec.ofNat 64 (256 * b) = S + BitVec.ofNat 64 (1024 * j + 256 * b + 8 * 0) :=
    fun b hb => plane_addr S j b 0 (by omega_using [hj, hb])
  have hr : ∀ b < 4, InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (256 * b)) 8 :=
    fun b hb => by rw [ad b hb, hrd]; exact E.rd8 _ (by omega_using []) (by omega_using [hj, hb])
  have hal : ∀ b < 4, (B + BitVec.ofNat 64 (256 * b)).toNat % 8 = 0 :=
    fun b hb => by rw [ad b hb]; exact al8_add E.al8 (by omega_using []) (by omega_using [hj, hb])
  have r0 := hr 0 (by decide)
  have l0 := hal 0 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero] at r0 l0
  refine WP.mono (WP.keep [.t2, .t3, .t5, .t6, .t0] (row0_run u h7 hq r0 (hr 1 (by decide)) (hr 2 (by decide))
    (hr 3 (by decide)) l0 (hal 1 (by decide)) (hal 2 (by decide)) (hal 3 (by decide))) (by rfl) rfl)
    fun t ⟨⟨t2, t5, t6, t0, tm⟩, tk⟩ => ?_
  have M := mask_eq idx (k := 0) (by decide)
  have pl : ∀ b < 4, u.mem.readW (B + BitVec.ofNat 64 (256 * b)) 64 = planeWord64 s₀.mem S j b 0 :=
    fun b hb => by rw [ad b hb, hm]; rfl
  have p0 := pl 0 (by decide)
  simp only [Nat.mul_zero, BitVec.add_zero] at p0
  refine ⟨by rw [tk.gpr (by decide), hq], ?_, ?_, ?_, ?_, hk.trans tk |>.mono (by decide), tm.trans hm⟩
  · rw [t2, M, p0, scanPlane_one]
  · rw [t5, M, show (256#64 : BitVec 64) = BitVec.ofNat 64 (256 * 1) from rfl, pl 1 (by decide), scanPlane_one]
  · rw [t6, M, show (512#64 : BitVec 64) = BitVec.ofNat 64 (256 * 2) from rfl, pl 2 (by decide), scanPlane_one]
  · rw [t0, M, show (768#64 : BitVec 64) = BitVec.ofNat 64 (256 * 3) from rfl, pl 3 (by decide), scanPlane_one]

theorem row_step {s₀ : State} {S : Addr} (E : SchAt s₀ S) {j : Nat} (hj : j < 4) (idx : Byte)
    {k : Nat} (hk : k < 32) {u : State} (h7 : u.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (I : RowInv s₀ S j idx k u) :
    WP isa (.block (row k)) u (RowInv s₀ S j idx (k + 1)) := by
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [I.keep.2.1, I.keep.2.2]
  let B := S + BitVec.ofNat 64 (1024 * j)
  have ad : ∀ b < 4, B + BitVec.ofNat 64 (256 * b + 8 * k) = S + BitVec.ofNat 64 (1024 * j + 256 * b + 8 * k) :=
    fun b hb => plane_addr S j b k (by omega_using [hj, hk, hb])
  have hr : ∀ b < 4, InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (256 * b + 8 * k)) 8 :=
    fun b hb => by rw [ad b hb, hrd]; exact E.rd8 _ (by omega_using []) (by omega_using [hj, hk, hb])
  have hal : ∀ b < 4, (B + BitVec.ofNat 64 (256 * b + 8 * k)).toNat % 8 = 0 :=
    fun b hb => by rw [ad b hb]; exact al8_add E.al8 (by omega_using []) (by omega_using [hj, hk, hb])
  have pl : ∀ b < 4, u.mem.readW (B + BitVec.ofNat 64 (256 * b + 8 * k)) 64 = planeWord64 s₀.mem S j b k :=
    fun b hb => by rw [ad b hb, I.mem]; rfl
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
  refine WP.mono (WP.keep [.t2, .t3, .t4, .t5, .t6, .t0] (row_run u hk h7 I.q r0 r1 r2 r3 l0 l1 l2 l3)
    (by rfl) rfl) fun t ⟨⟨t2, t5, t6, t0, tm⟩, tk⟩ => ?_
  have M := mask_eq idx hk
  refine ⟨by rw [tk.gpr (by decide), I.q], ?_, ?_, ?_, ?_, I.keep.trans tk |>.mono (by decide), tm.trans I.mem⟩
  · rw [t2, M, p0, I.p0, scanPlane_succ]
  · rw [t5, M, p1, I.p1, scanPlane_succ]
  · rw [t6, M, p2, I.p2, scanPlane_succ]
  · rw [t0, M, p3, I.p3, scanPlane_succ]

theorem rows_succ (n : Nat) : rows (n + 1) = rows n ++ row (n + 1) := by
  simp only [rows, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

theorem rows_run {s₀ : State} {S : Addr} (E : SchAt s₀ S) {j : Nat} (hj : j < 4) (idx : Byte)
    {u : State} (h7 : u.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (hq : u.gpr .t1 = BitVec.twoPow 64 (idx.toNat / 8)) (hk : Keep lookRegs s₀ u) (hm : u.mem = s₀.mem)
    (h7₀ : s₀.gpr .a7 = S + BitVec.ofNat 64 (1024 * j)) :
    ∀ n, n < 32 → WP isa (.block (rows n)) u (RowInv s₀ S j idx (n + 1)) := by
  intro n
  induction n with
  | zero => intro _; exact row0_step E hj idx h7 hq hk hm
  | succ n ih =>
    intro hn
    rw [rows_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun v V => row_step E hj idx hn ?_ V
    rw [V.keep.gpr (by decide), h7₀]

/-! ## The entry from the accumulators -/

/-- `t3 := 8L` for the lane `L` of xL's byte `3 - j`. -/
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

/-- The lookup of S-box `j` (at `sch`, moved to it) for the byte `3 - j` of
xL's low word. -/
theorem lookup_run {s : State} {S : Addr} (E : SchAt s S) {j : Nat} (hj : j < 4)
    (h7 : s.gpr .a7 = S + BitVec.ofNat 64 (1024 * j)) :
    WP isa (lookup j) s fun t =>
      lo (t.gpr .t2) = sEntry (scheduleAt s.mem S) j (quarter (lo (s.gpr .a3)) j) ∧
        Keep lookRegs s t ∧ t.mem = s.mem := by
  let idx := quarter (lo (s.gpr .a3)) j
  unfold lookup
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.t1, .t3] (index_run s hj) (by rfl) rfl) fun u ⟨⟨u1, um⟩, uk⟩ => ?_
  rw [WP.block_append_iff]
  have uk' : Keep lookRegs s u := uk.mono (by decide)
  refine WP.mono (rows_run E hj idx (by rw [uk.gpr (by decide), h7]) u1 uk' um h7 31 (by decide))
    fun v V => ?_
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

end VG.Proof.Blowfish.RISCV64

end

end

/-!
# Blowfish on RISCV64: F and the block function

`f_run`: F of xL's low word into `a5`'s, one S-box at a time (`fAcc`).
`cipher_run`: `cipher up` takes the halves in the low words of `a3` and
`a4` to their encryption (`up`) or decryption under the schedule at `a7`,
changing only `a3`–`a6` and the lookup's temporaries. The structure of
PPC64LE's (`Proof/Blowfish/PPC64LE/Ecb.lean`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64 VG.Spec.Blowfish VG.Proof.Blowfish

/-! ## F -/

/-- The registers F writes. -/
def fRegs : List Reg := .a5 :: lookRegs

theorem combine_run (u : State) {j : Nat} (hj : j < 4) :
    WP isa (.block [combine j]) u fun t =>
      lo (t.gpr .a5) = (if j = 0 then lo (u.gpr .t2) else if j = 2 then lo (u.gpr .a5) ^^^ lo (u.gpr .t2)
        else lo (u.gpr .a5) + lo (u.gpr .t2)) ∧ t.mem = u.mem := by
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    brun [combine] <;> simp only [lo_xor, lo_add, BitVec.or_self]

/-- What a run of `Keep (r :: rs)` that leaves `r` as it was keeps. -/
theorem keep_restore {r : Reg} {rs : List Reg} {s t : State} (h : Keep (r :: rs) s t)
    (hr : t.gpr r = s.gpr r) : Keep rs s t :=
  ⟨fun r' h' => by
    by_cases e : r' = r
    · rw [e]; exact hr
    · exact h.1 r' (by simp only [List.mem_cons, not_or]; exact ⟨e, h'⟩), h.2⟩

/-- The registers F writes, with the schedule pointer, which it moves and
restores. -/
def fRegs7 : List Reg := .a7 :: fRegs

/-- S-box `j`'s lookup, then its accumulation, from `fAcc … (j - 1)` (or
anything, for `j = 0`) in `a5`, with `sch` at S-box `j`. -/
theorem step_run {s₀ : State} (E : LookEnv s₀) {j : Nat} (hj : j < 4) {u : State} (k : Keep fRegs7 s₀ u)
    (hm : u.mem = s₀.mem) (h7 : u.gpr .a7 = s₀.gpr .a7 + BitVec.ofNat 64 (1024 * j))
    (hp : 0 < j → lo (u.gpr .a5) = fAcc (scheduleAt s₀.mem (s₀.gpr .a7))
      (lo (s₀.gpr .a3)) (j - 1)) {Q : State → Prop}
    (hQ : ∀ t, lo (t.gpr .a5) = fAcc (scheduleAt s₀.mem (s₀.gpr .a7)) (lo (s₀.gpr .a3)) j →
      Keep fRegs7 s₀ t → t.mem = s₀.mem → t.gpr .a7 = u.gpr .a7 → Q t) :
    WP isa (.seq (lookup j) (.block [combine j])) u Q := by
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [k.2.1, k.2.2]
  have Eu : SchAt u (s₀.gpr .a7) := ⟨fun o h1 h2 => by rw [hrd]; exact E.rd8 o h1 h2, E.al8⟩
  apply WP.seq
  refine WP.mono (lookup_run Eu hj h7) fun v ⟨v10, vk, vm⟩ => ?_
  refine WP.mono (WP.keep [.a5] (combine_run v hj) (by
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide) rfl)
    fun t ⟨⟨t7, tm⟩, tk⟩ => hQ t ?_ ((k.trans vk).trans tk |>.mono (by decide)) (by rw [tm, vm, hm])
      (by rw [tk.gpr (by decide), vk.gpr (by decide)])
  have e4 : u.gpr .a3 = s₀.gpr .a3 := k.gpr (by decide)
  rw [t7, v10, hm, e4, vk.gpr (by decide)]
  exact fAcc_step _ _ hj _ hp

theorem nextBox_run (u : State) :
    WP isa (.block [nextBox]) u fun t => t.gpr .a7 = u.gpr .a7 + BitVec.ofNat 64 1024 ∧ t.mem = u.mem := by
  brun [nextBox]

/-- `nextBox` after the lookup of S-box `j < 3`, and what it keeps. -/
theorem next_run {s₀ : State} {j : Nat} {u : State} (k : Keep fRegs7 s₀ u)
    (h7 : u.gpr .a7 = s₀.gpr .a7 + BitVec.ofNat 64 (1024 * j)) :
    WP isa (.block [nextBox]) u fun t => Keep fRegs7 s₀ t ∧ t.mem = u.mem ∧
      t.gpr .a7 = s₀.gpr .a7 + BitVec.ofNat 64 (1024 * (j + 1)) ∧ t.gpr .a5 = u.gpr .a5 := by
  refine WP.mono (WP.keep [.a7] (nextBox_run u) (by rfl) rfl) fun t ⟨⟨t7, tm⟩, tk⟩ =>
    ⟨(k.trans tk).mono (by decide), tm, ?_, tk.gpr (by decide)⟩
  rw [t7, h7, Offset.add_add]
  congr 2

theorem f_run {s : State} (E : LookEnv s) :
    WP isa Impl.Blowfish.RISCV64.f s fun t =>
      lo (t.gpr .a5) = Spec.Blowfish.f (scheduleAt s.mem (s.gpr .a7)) (lo (s.gpr .a3)) ∧
        Keep fRegs s t ∧ t.mem = s.mem := by
  unfold Impl.Blowfish.RISCV64.f
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 0) (by decide) (Keep.refl _ _) rfl (by simp) (fun h => absurd h (by decide))
    fun t0 h0 k0 m0 e0 => ?_
  apply WP.seq
  refine WP.mono (next_run (j := 0) k0 (by rw [e0]; simp)) fun u0 ⟨k0', m0', e0', a0⟩ => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 1) (by decide) k0' (m0'.trans m0) e0' (fun _ => by rw [a0]; exact h0)
    fun t1 h1 k1 m1 e1 => ?_
  apply WP.seq
  refine WP.mono (next_run (j := 1) k1 (by rw [e1, e0'])) fun u1 ⟨k1', m1', e1', a1⟩ => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 2) (by decide) k1' (m1'.trans m1) e1' (fun _ => by rw [a1]; exact h1)
    fun t2 h2 k2 m2 e2 => ?_
  apply WP.seq
  refine WP.mono (next_run (j := 2) k2 (by rw [e2, e1'])) fun u2 ⟨k2', m2', e2', a2⟩ => ?_
  apply WP.reassoc; apply WP.seq
  refine step_run E (j := 3) (by decide) k2' (m2'.trans m2) e2' (fun _ => by rw [a2]; exact h2)
    fun t3 h3 k3 m3 e3 => ?_
  have back : WP isa (.block [.addi sch sch (-2048), .addi sch sch (-1024)]) t3 fun t =>
      t.gpr .a7 = t3.gpr .a7 - BitVec.ofNat 64 2048 - BitVec.ofNat 64 1024 ∧ t.mem = t3.mem := by
    brun
  refine WP.mono (WP.keep [.a7] back (by rfl) rfl) fun t ⟨⟨t7, tm⟩, tk⟩ => ?_
  have e7 : t.gpr .a7 = s.gpr .a7 := by
    rw [t7, e3, e2', BitVec.sub_sub, BitVec.ofNat_add_ofNat]
    exact BitVec.add_sub_cancel _ _
  refine ⟨?_, keep_restore ((k3.trans tk).mono (by decide)) e7, tm.trans m3⟩
  rw [tk.gpr (by decide), h3, fAcc_three]

/-! ## Rounds -/

/-- The P-array entry of round `m`. -/
def ord (up : Bool) (m : Nat) : Nat := if up then m else 17 - m

/-- `pPtr`'s offset in the schedule after `i` rounds. -/
def pBase (up : Bool) (i : Nat) : Nat := if up then 4096 + 4 * i else 4160 - 4 * i

/-- The registers the block function writes. -/
def cRegs : List Reg := [.a3, .a4, .a5, .a6, .t0, .t1, .t2, .t3, .t4, .t5, .t6]

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
  p : u.gpr .a6 = s₀.gpr .a7 + BitVec.ofNat 64 (pBase up i)
  halves : (lo (u.gpr .a3), lo (u.gpr .a4)) =
    iter (scheduleAt s₀.mem (s₀.gpr .a7)) (ord up) i (lo (s₀.gpr .a3), lo (s₀.gpr .a4))
  keep : Keep cRegs s₀ u
  mem : u.mem = s₀.mem

theorem round_head (u : State) (up : Bool) {P : BitVec 32} {a : Addr}
    (hp : u.gpr .a6 + BitVec.ofNat 64 (pAt up) = a)
    (hr : InRegions (u.rd ++ u.wr) a 4) (hal : a.toNat % 4 = 0) (hP : u.mem.readW a 32 = P) :
    WP isa (.block [.load .w tmp pPtr (pAt up), .logic .xor xL xL tmp]) u fun t =>
      lo (t.gpr .a3) = lo (u.gpr .a3) ^^^ P ∧ t.mem = u.mem := by
  have ho : pAt up < 2048 := by cases up <;> decide
  rw [← hp] at hr hP hal
  brun [ho, hr, hP, hal]
  simp only [lo_xor, lo_ext]

/-- The round's end test: `pPtr - sch` less the end offset, in three
immediates. -/
theorem sub_end (S : Addr) (a : Nat) {e : Nat} (he : 4094 ≤ e) :
    S + BitVec.ofNat 64 a - S - BitVec.ofNat 64 2047 - BitVec.ofNat 64 2047 - BitVec.ofNat 64 (e - 4094) =
      BitVec.ofNat 64 a - BitVec.ofNat 64 e := by
  rw [Offset.add_sub_cancel_left, BitVec.sub_sub, BitVec.sub_sub, BitVec.ofNat_add_ofNat,
    BitVec.ofNat_add_ofNat, show 2047 + (2047 + (e - 4094)) = e by omega_using [he]]

theorem round_tail (u : State) (up : Bool) (S : BitVec 64) {i : Nat} (hi : i < 16)
    (h3 : u.gpr .a7 = S) (h8 : u.gpr .a6 = S + BitVec.ofNat 64 (pBase up i)) :
    WP isa (.block [.logic .xor xR xR fReg, .logic .or tmp xL xL, .logic .or xL xR xR,
        .logic .or xR tmp tmp, .addi pPtr pPtr (if up then 4 else -4),
        .sub tmp pPtr sch, .addi tmp tmp (-2047), .addi tmp tmp (-2047),
        .addi tmp tmp (-(pEnd up - 4094 : Nat))]) u fun t =>
      lo (t.gpr .a3) = lo (u.gpr .a4) ^^^ lo (u.gpr .a5) ∧ lo (t.gpr .a4) = lo (u.gpr .a3) ∧
        t.gpr .a6 = S + BitVec.ofNat 64 (pBase up (i + 1)) ∧
        t.gpr .t4 = BitVec.ofNat 64 (pBase up (i + 1)) - BitVec.ofNat 64 (pBase up 16) ∧
        t.mem = u.mem := by
  have hend : pEnd up = pBase up 16 := by cases up <;> rfl
  have e4 : 4094 ≤ pEnd up := by cases up <;> decide
  cases up
  · have e : S + BitVec.ofNat 64 (4160 - 4 * i) - 4#64 = S + BitVec.ofNat 64 (4160 - 4 * (i + 1)) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ofs_sub S (by omega_using [hi])]; congr 2
    brun [h3, h8, show pEnd false - 4094 ≤ 2048 by decide]
    simp only [pBase, Bool.false_eq_true, ite_false, lo_xor, BitVec.or_self, e]
    refine ⟨trivial, trivial, trivial, ?_⟩
    rw [sub_end S _ e4, hend]
    simp only [pBase, Bool.false_eq_true, ite_false]
  · have e : S + BitVec.ofNat 64 (4096 + 4 * i) + 4#64 = S + BitVec.ofNat 64 (4096 + 4 * (i + 1)) := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add]; congr 2
    brun [h3, h8, show pEnd true - 4094 ≤ 2048 by decide]
    simp only [pBase, ite_true, lo_xor, BitVec.or_self, e]
    refine ⟨trivial, trivial, trivial, ?_⟩
    rw [sub_end S _ e4, hend]
    simp only [pBase, ite_true]

theorem keep_reads {s t : State} {rs : List Reg} (k : Keep rs s t) : t.rd ++ t.wr = s.rd ++ s.wr := by
  rw [k.2.1, k.2.2]

theorem round_step {s₀ : State} (E : LookEnv s₀) (up : Bool) {i : Nat} (hi : i < 16) {u : State}
    (I : CInv s₀ up i u) :
    WP isa (round up) u fun u' => CInv s₀ up (i + 1) u' ∧
      u'.gpr .t4 = BitVec.ofNat 64 (pBase up (i + 1)) - BitVec.ofNat 64 (pBase up 16) := by
  have ho : ord up i < 18 := by cases up <;> simp [ord] <;> omega_arith
  let K := scheduleAt s₀.mem (s₀.gpr .a7)
  have u3 : u.gpr .a7 = s₀.gpr .a7 := I.keep.gpr (by decide)
  unfold round
  apply WP.seq
  refine WP.mono (WP.keep [.a3, .t4] (round_head u up (P := pEntry K (ord up i))
    (by rw [I.p, addr_P _ up hi]) (by rw [keep_reads I.keep]; exact E.rd _ (by omega_using []) (by omega_using [ho]))
    (al_add E.al (by omega_using []) (by omega_using [ho]))
    (by rw [I.mem, pEntry_read _ _ ho])) (by cases up <;> decide) rfl) fun v ⟨⟨v4, vm⟩, vk⟩ => ?_
  have kv : Keep cRegs s₀ v := (I.keep.trans vk).mono (by decide)
  have Ev : LookEnv v := E.keep kv (by decide)
  apply WP.seq
  refine WP.mono (f_run Ev) fun w ⟨w7, wk, wm⟩ => ?_
  have w3 : w.gpr .a7 = s₀.gpr .a7 := by rw [wk.gpr (by decide), vk.gpr (by decide), u3]
  have w8 : w.gpr .a6 = s₀.gpr .a7 + BitVec.ofNat 64 (pBase up i) := by
    rw [wk.gpr (by decide), vk.gpr (by decide), I.p]
  refine WP.mono (WP.keep [.a3, .a4, .a6, .t4] (round_tail w up _ hi w3 w8) (by
    cases up <;> decide) rfl) fun x ⟨⟨x4, x5, x8, x12, xm⟩, xk⟩ => ?_
  have hK : scheduleAt v.mem (v.gpr .a7) = K := by rw [vm, I.mem, vk.gpr (by decide), u3]
  refine ⟨⟨by omega_using [hi], x8, ?_, ((kv.trans wk).trans xk).mono (by decide), by rw [xm, wm, vm, I.mem]⟩, x12⟩
  have w4 : w.gpr .a3 = v.gpr .a3 := wk.gpr (by decide)
  have w5 : w.gpr .a4 = u.gpr .a4 := by rw [wk.gpr (by decide), vk.gpr (by decide)]
  rw [x4, x5, w7, hK, w4, w5, v4, iter_succ, ← I.halves]
  simp only [roundStep]
  rw [BitVec.xor_comm (lo (u.gpr .a4))]

theorem cipher_start (s : State) (up : Bool) :
    WP isa (.block [.addi pPtr sch 2047, .addi pPtr pPtr 2047,
      .addi pPtr pPtr ((if up then pOff else pOff + 64) - 4094 : Nat)]) s fun t =>
      t.gpr .a6 = s.gpr .a7 + BitVec.ofNat 64 (pBase up 0) ∧ t.mem = s.mem := by
  cases up <;> brun [pOff, pBase] <;> rw [Offset.add_add, Offset.add_add]

theorem rounds_run {s : State} (E : LookEnv s) (up : Bool) {u : State} (I : CInv s up 0 u) :
    WP isa (.loop (round up) (.nonzero tmp)) u (CInv s up 16) := by
  refine WP.loop (M := isa) (Q := CInv s up 16)
    (fun (n : Nat) (v : State) => ∃ i, i < 16 ∧ n = 16 - i ∧ CInv s up i v) ?_ 16 u ⟨0, by decide, rfl, I⟩
  intro n v ⟨i, hi, hn, J⟩
  refine WP.mono (round_step E up hi J) fun v' ⟨J', hz⟩ => ?_
  rw [tmp, Steps.eval_nonzero, hz, ofNat_sub_bne (by cases up <;> simp [pBase] <;> omega_arith)
    (by cases up <;> simp [pBase])]
  have e : (pBase up (i + 1) = pBase up 16) ↔ i + 1 = 16 := by cases up <;> simp [pBase] <;> omega_using []
  by_cases e' : i + 1 = 16
  · left
    exact ⟨by simp [e.mpr e'], e' ▸ J'⟩
  · right
    have hne : ¬ pBase up (i + 1) = pBase up 16 := fun h => e' (e.mp h)
    exact ⟨by simp [hne], n - 1, by omega_using [hi, hn], i + 1, by omega_using [hi, e'], by omega_using [hn], J'⟩

theorem cipher_end (u : State) (up : Bool) {P₁₆ P₁₇ : BitVec 32} {a b : Addr}
    (ha : u.gpr .a6 + BitVec.ofNat 64 (pAt up) = a)
    (hb : u.gpr .a6 + BitVec.ofNat 64 (4 - pAt up) = b)
    (hra : InRegions (u.rd ++ u.wr) a 4) (hrb : InRegions (u.rd ++ u.wr) b 4)
    (hla : a.toNat % 4 = 0) (hlb : b.toNat % 4 = 0)
    (h16 : u.mem.readW a 32 = P₁₆) (h17 : u.mem.readW b 32 = P₁₇) :
    WP isa (.block [.load .w tmp pPtr (pAt up), .logic .xor tmp xL tmp,
        .load .w xL pPtr (4 - pAt up), .logic .xor xL xL xR, .logic .or xR tmp tmp]) u fun t =>
      lo (t.gpr .a3) = P₁₇ ^^^ lo (u.gpr .a4) ∧ lo (t.gpr .a4) = lo (u.gpr .a3) ^^^ P₁₆ ∧
        t.mem = u.mem := by
  have ho : pAt up < 2048 := by cases up <;> decide
  have ho' : 4 - pAt up < 2048 := by cases up <;> decide
  rw [← ha] at hra h16 hla
  rw [← hb] at hrb h17 hlb
  brun [ho, ho', hra, hrb, h16, h17, hla, hlb]
  simp only [lo_xor, lo_ext, BitVec.or_self, and_self]

/-- The block function. -/
theorem cipher_run {s : State} (E : LookEnv s) (up : Bool) :
    WP isa (cipher up) s fun t =>
      (lo (t.gpr .a3), lo (t.gpr .a4)) =
        feistel (scheduleAt s.mem (s.gpr .a7)) (ord up) (lo (s.gpr .a3)) (lo (s.gpr .a4)) ∧
      Keep cRegs s t ∧ t.mem = s.mem := by
  unfold cipher
  apply WP.seq
  refine WP.mono (WP.keep [.a6] (cipher_start s up) (by cases up <;> decide) rfl)
    fun u ⟨⟨u8, um⟩, uk⟩ => ?_
  have I0 : CInv s up 0 u :=
    ⟨by decide, u8, by rw [uk.gpr (by decide), uk.gpr (by decide)]; rfl, uk.mono (by decide), um⟩
  apply WP.seq
  refine WP.mono (rounds_run E up I0) fun v V => ?_
  have hrd := keep_reads V.keep
  let K := scheduleAt s.mem (s.gpr .a7)
  have r16 : 4096 + 4 * ord up 16 + 4 ≤ 4168 := by cases up <;> decide
  have r17 : 4096 + 4 * ord up 17 + 4 ≤ 4168 := by cases up <;> decide
  have o16 : ord up 16 < 18 := by cases up <;> decide
  have o17 : ord up 17 < 18 := by cases up <;> decide
  refine WP.mono (WP.keep [.a3, .a4, .t4] (cipher_end v up (P₁₆ := pEntry K (ord up 16))
    (P₁₇ := pEntry K (ord up 17)) (a := s.gpr .a7 + BitVec.ofNat 64 (4096 + 4 * ord up 16))
    (b := s.gpr .a7 + BitVec.ofNat 64 (4096 + 4 * ord up 17))
    (by rw [V.p]; exact Offset.add_add_eq _ (by cases up <;> simp [pBase, pAt, ord]))
    (by rw [V.p]; exact Offset.add_add_eq _ (by cases up <;> simp [pBase, pAt, ord]))
    (by rw [hrd]; exact E.rd _ (by omega_using []) r16) (by rw [hrd]; exact E.rd _ (by omega_using []) r17)
    (al_add E.al (by omega_using []) (by omega_using [r16])) (al_add E.al (by omega_using []) (by omega_using [r17]))
    (by rw [V.mem, pEntry_read _ _ o16]) (by rw [V.mem, pEntry_read _ _ o17])) (by cases up <;> decide) rfl)
    fun t ⟨⟨t4, t5, tm⟩, tk⟩ => ?_
  refine ⟨?_, (V.keep.trans tk).mono (by decide), by rw [tm, V.mem]⟩
  rw [t4, t5, feistel_eq, ← V.halves, BitVec.xor_comm]

end VG.Proof.Blowfish.RISCV64
