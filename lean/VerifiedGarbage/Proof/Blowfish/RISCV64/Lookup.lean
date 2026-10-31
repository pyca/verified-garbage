module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Run
public import VerifiedGarbage.Proof.Blowfish.Scan64
public import VerifiedGarbage.Proof.Blowfish.F
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Impl.Blowfish.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep

/-!
# Blowfish on RISC-V: an S-box lookup

`lookup_run`: `lookup j`, with `a7` at S-box `j` of the schedule at `S`,
leaves S-box `j`'s entry for the byte `3 - j` of xL's low word in the
accumulator's low word, changing only the lookup's registers. The rows
(`row_step`, by induction in `rows_run`) leave each plane's doubleword of the
index's row in its accumulator (`scanPlane`, `Proof/Blowfish/Scan64.lean`);
the end (`extract`) multiplies each by `2 ^ (56 - 8L)` (`fac_prod`), which
brings the byte of the index's lane `L` to the top (`mul_byte`), and packs
the four bytes into the entry (`pack_byte`).
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
  omega

/-- A 4-byte aligned offset of a 4-byte aligned base. -/
theorem al_add {p : Addr} (hp : p.toNat % 4 = 0) {d : Nat} (hd : d % 4 = 0) (hd' : d < 2 ^ 64) :
    (p + BitVec.ofNat 64 d).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) hd']
  have := p.isLt
  omega

/-- `a - c` (as doublewords, both below `2 ^ 64`) is nonzero iff `a ≠ c`. -/
theorem ofNat_sub_bne {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c != (0 : BitVec 64)) = !decide (a = c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 c ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at this
      omega
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
  · simp only [h8, decide_true, Bool.true_and, show 56 + i < 64 by omega,
      show ¬ (56 + i < 32 + 8 * j) by omega, decide_false, Bool.not_false,
      show 8 * (3 - j) + i < 32 by omega]
    rw [decide_eq_true hi, Bool.true_and]
    congr 1; omega
  · simp only [h8, decide_false, Bool.false_and]
    by_cases h : 56 + i < 64
    · omega
    · simp [h]

/-! ## The rows -/

/-- `xori` of a numeral below 2048. -/
theorem exec_xori_nat {s : State} {d n : Reg} {m : Nat} (h : m < 2048) :
    exec (.logicImm .xor d n (m : Int)) s = some (s.write d (s.gpr n ^^^ BitVec.ofNat 64 m)) := by
  rw [exec_logicImm (by unfold imm12; omega), BitVec.ofInt_natCast]

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
      let M := ((q ^^^ BitVec.ofNat 64 k) - 1#64).sshiftRight 63
      t.gpr .t2 = u.gpr .t2 ||| (u.mem.readW (B + BitVec.ofNat 64 (8 * k)) 64 &&& M) ∧
      t.gpr .t5 = u.gpr .t5 ||| (u.mem.readW (B + BitVec.ofNat 64 (256 + 8 * k)) 64 &&& M) ∧
      t.gpr .t6 = u.gpr .t6 ||| (u.mem.readW (B + BitVec.ofNat 64 (512 + 8 * k)) 64 &&& M) ∧
      t.gpr .t0 = u.gpr .t0 ||| (u.mem.readW (B + BitVec.ofNat 64 (768 + 8 * k)) 64 &&& M) ∧
      t.mem = u.mem := by
  unfold row rowMask plane
  brun [↓exec_xori_nat, accOf, Nat.zero_add, h7, h1, r0, r1, r2, r3, a0, a1, a2, a3, show k < 2048 by omega,
    show 8 * k < 2048 by omega, show 256 * 1 + 8 * k < 2048 by omega,
    show 256 * 2 + 8 * k < 2048 by omega, show 256 * 3 + 8 * k < 2048 by omega]

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
      let M := ((q ^^^ BitVec.ofNat 64 0) - 1#64).sshiftRight 63
      t.gpr .t2 = u.mem.readW B 64 &&& M ∧ t.gpr .t5 = u.mem.readW (B + 256#64) 64 &&& M ∧
      t.gpr .t6 = u.mem.readW (B + 512#64) 64 &&& M ∧ t.gpr .t0 = u.mem.readW (B + 768#64) 64 &&& M ∧
      t.mem = u.mem := by
  unfold row0 rowMask firstPlane
  brun [↓exec_xori_nat, accOf, h7, h1, r0, r1, r2, r3, a0, a1, a2, a3]

/-- The row's mask, from the index's row in `t1`. -/
theorem mask_eq (x : Byte) {k : Nat} (hk : k < 32) :
    ((BitVec.ofNat 64 (x.toNat / 8) ^^^ BitVec.ofNat 64 k) - 1#64).sshiftRight 63 = rowSel x.toNat k := by
  have hx := x.isLt
  have e : (BitVec.ofNat 64 (x.toNat / 8) ^^^ BitVec.ofNat 64 k).toNat = x.toNat / 8 ^^^ k := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hl : x.toNat / 8 ^^^ k < 2 ^ 5 := Nat.xor_lt_two_pow (by omega) (by omega)
  rw [sra_mask _ (by rw [e]; omega), rowSel]
  by_cases h : x.toNat / 8 = k
  · rw [ite_eq_left h, ite_eq_left (by rw [h, BitVec.xor_self]; rfl)]
  · have hne : BitVec.ofNat 64 (x.toNat / 8) ≠ BitVec.ofNat 64 k := fun e' => h (by
      have := congrArg BitVec.toNat e'
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exact this)
    rw [ite_eq_right h, ite_eq_right (fun h' => hne (BitVec.xor_eq_zero_iff.mp (BitVec.eq_of_toNat_eq (by
      rw [h']; rfl))))]

theorem index_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block (index j)) s fun t =>
      t.gpr .t1 = BitVec.ofNat 64 ((quarter (lo (s.gpr .a3)) j).toNat / 8) ∧ t.mem = s.mem := by
  have e : (s.gpr .a3 <<< (32 + 8 * j)) >>> 59 = BitVec.ofNat 64 ((quarter (lo (s.gpr .a3)) j).toNat / 8) := by
    have h := congrArg (fun v : BitVec 64 => v >>> 3) (index_val (s.gpr .a3) hj)
    rw [← BitVec.shiftRight_add] at h
    rw [h]
    apply BitVec.eq_of_toNat_eq
    have := (quarter (lo (s.gpr .a3)) j).isLt
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [← e]
  unfold index
  brun [show 32 + 8 * j < 64 by omega]

/-- The schedule at `S`, readable a doubleword at a time, and aligned. -/
structure SchAt (s : State) (S : Addr) : Prop where
  rd8 : ∀ o, o % 8 = 0 → o + 8 ≤ 4168 → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 o) 8
  al8 : S.toNat % 8 = 0

/-- After rows `0, …, n - 1` of S-box `j` of the schedule at `S` for the
index `idx`, from the lookup's start `s₀`. -/
structure RowInv (s₀ : State) (S : Addr) (j : Nat) (idx : Byte) (n : Nat) (u : State) : Prop where
  q : u.gpr .t1 = BitVec.ofNat 64 (idx.toNat / 8)
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
  Offset.add_add_eq _ (by omega)

theorem row0_step {s₀ : State} {S : Addr} (E : SchAt s₀ S) {j : Nat} (hj : j < 4) (idx : Byte)
    {u : State} (h7 : u.gpr .a7 = S + BitVec.ofNat 64 (1024 * j))
    (hq : u.gpr .t1 = BitVec.ofNat 64 (idx.toNat / 8)) (hk : Keep lookRegs s₀ u) (hm : u.mem = s₀.mem) :
    WP isa (.block row0) u (RowInv s₀ S j idx 1) := by
  have hrd : u.rd ++ u.wr = s₀.rd ++ s₀.wr := by rw [hk.2.1, hk.2.2]
  let B := S + BitVec.ofNat 64 (1024 * j)
  have ad : ∀ b < 4, B + BitVec.ofNat 64 (256 * b) = S + BitVec.ofNat 64 (1024 * j + 256 * b + 8 * 0) :=
    fun b hb => plane_addr S j b 0 (by omega)
  have hr : ∀ b < 4, InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (256 * b)) 8 :=
    fun b hb => by rw [ad b hb, hrd]; exact E.rd8 _ (by omega) (by omega)
  have hal : ∀ b < 4, (B + BitVec.ofNat 64 (256 * b)).toNat % 8 = 0 :=
    fun b hb => by rw [ad b hb]; exact al8_add E.al8 (by omega) (by omega)
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
    fun b hb => plane_addr S j b k (by omega)
  have hr : ∀ b < 4, InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 (256 * b + 8 * k)) 8 :=
    fun b hb => by rw [ad b hb, hrd]; exact E.rd8 _ (by omega) (by omega)
  have hal : ∀ b < 4, (B + BitVec.ofNat 64 (256 * b + 8 * k)).toNat % 8 = 0 :=
    fun b hb => by rw [ad b hb]; exact al8_add E.al8 (by omega) (by omega)
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
    (hq : u.gpr .t1 = BitVec.ofNat 64 (idx.toNat / 8)) (hk : Keep lookRegs s₀ u) (hm : u.mem = s₀.mem)
    (h7₀ : s₀.gpr .a7 = S + BitVec.ofNat 64 (1024 * j)) :
    ∀ n, n < 32 → WP isa (.block (rows n)) u (RowInv s₀ S j idx (n + 1)) := by
  intro n
  induction n with
  | zero => intro _; exact row0_step E hj idx h7 hq hk hm
  | succ n ih =>
    intro hn
    rw [rows_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun v V => row_step E hj idx hn ?_ V
    rw [V.keep.gpr (by decide), h7₀]

/-! ## The entry from the accumulators -/

theorem notShift_run (s : State) {j : Nat} (hj : j < 4) :
    WP isa (.block [.shift .sll .d mReg xL (32 + 8 * j), .logicImm .xor mReg mReg (-1)]) s fun t =>
      t.gpr .t3 = ~~~(s.gpr .a3 <<< (32 + 8 * j)) ∧ t.mem = s.mem := by
  brun [show 32 + 8 * j < 64 by omega]
  rw [show (-1#64 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.xor_allOnes]

theorem ones_fac : ∀ c < 3, BitVec.allOnes 64 >>> (64 - 8 * 2 ^ c) + 1#64 = BitVec.ofNat 64 (2 ^ (8 * 2 ^ c)) := by
  decide

theorem factor_run (s : State) (d : Reg) {c : Nat} (hc : c < 3) :
    WP isa (.block (factor d c)) s fun t =>
      t.gpr d = (if (s.gpr .t3).getLsbD (56 + c) then BitVec.ofNat 64 (2 ^ (8 * 2 ^ c)) else 1) ∧
        t.mem = s.mem := by
  unfold factor
  have bm := bit_mask (s.gpr .t3) (c := 56 + c) (by omega)
  rw [show 63 - (56 + c) = 7 - c by omega] at bm
  brun [show 7 - c < 64 by omega, show 64 - 8 * 2 ^ c < 64 by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide]
  rw [bm]
  by_cases h : (s.gpr .t3).getLsbD (56 + c) = true
  · rw [ite_eq_left h, ite_eq_left h, ones_fac c hc]
  · rw [ite_eq_right h, ite_eq_right h]
    exact (by simp : ∀ n : Nat, (0 : BitVec 64) >>> n + 1#64 = 1) _

theorem pick_run (u : State) {K A0 A1 A2 A3 : BitVec 64} (h1 : u.gpr .t1 = K) (h2 : u.gpr .t2 = A0)
    (h5 : u.gpr .t5 = A1) (h6 : u.gpr .t6 = A2) (h0 : u.gpr .t0 = A3) :
    WP isa (.block (pick 0 ++ pick 1 ++ pick 2 ++ pick 3 ++
      ([.logic .or acc acc (accOf 1), .logic .or (accOf 2) (accOf 2) (accOf 3), .logic .or acc acc (accOf 2)] :
        List Instr))) u fun t =>
      t.gpr .t2 = ((A0 * K) >>> 56 ||| ((A1 * K) >>> 56) <<< 8) |||
        (((A2 * K) >>> 56) <<< 16 ||| ((A3 * K) >>> 56) <<< 24) ∧ t.mem = u.mem := by
  unfold pick
  brun [accOf, h1, h2, h5, h6, h0]

/-- A doubleword times `2 ^ (56 - 8L)`, shifted down 56: its byte `L`. -/
theorem mul_byte (a : BitVec 64) {L : Nat} (hL : L < 8) :
    (a * BitVec.ofNat 64 (2 ^ (56 - 8 * L))) >>> 56 = (a.extractLsb' (8 * L) 8).setWidth 64 := by
  have e : BitVec.ofNat 64 (2 ^ (56 - 8 * L)) = BitVec.twoPow 64 (56 - 8 * L) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_twoPow, BitVec.toNat_ofNat]
  rw [e, BitVec.mul_twoPow_eq_shiftLeft]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb']
  by_cases h8 : i < 8
  · simp only [h8, decide_true, Bool.true_and, show 56 + i < 64 by omega,
      show ¬ (56 + i < 56 - 8 * L) by omega, decide_false, Bool.not_false]
    rw [decide_eq_true (by omega : i < 64), Bool.true_and]
    congr 1; omega
  · simp only [h8, decide_false, Bool.false_and]
    by_cases h : 56 + i < 64
    · omega
    · simp [h]

/-- The low word of four bytes ORed into place. -/
theorem pack_byte (y : Nat → Byte) {c : Nat} (hc : c < 4) :
    (lo ((((y 0).setWidth 64 ||| (y 1).setWidth 64 <<< 8) |||
      ((y 2).setWidth 64 <<< 16 ||| (y 3).setWidth 64 <<< 24)))).extractLsb' (8 * c) 8 = y c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false, Bool.true_and, Bool.and_true,
      Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, Bool.not_true, Bool.not_false,
      Nat.add_sub_cancel_left, Nat.zero_add, BitVec.getLsbD_of_ge, Nat.reduceMul]

/-- The low three bits of `q`, by `q`'s residue mod 8. -/
theorem bit012 (q : BitVec 64) :
    q.getLsbD 0 = decide (q.toNat % 8 % 2 = 1) ∧ q.getLsbD 1 = decide (q.toNat % 8 / 2 % 2 = 1) ∧
      q.getLsbD 2 = decide (q.toNat % 8 / 4 = 1) := by
  simp only [BitVec.getLsbD, Nat.testBit_zero, Nat.testBit_succ]
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> apply propext <;> omega

/-- The three factors' product, `2 ^ (56 - 8L)`, by the lane's bits. -/
theorem fac_prod {L : Nat} (hL : L < 8) :
    (if (!decide (L % 8 % 2 = 1)) = true then BitVec.ofNat 64 (2 ^ (8 * 2 ^ 0)) else 1) *
      (if (!decide (L % 8 / 2 % 2 = 1)) = true then BitVec.ofNat 64 (2 ^ (8 * 2 ^ 1)) else 1) *
      (if (!decide (L % 8 / 4 = 1)) = true then BitVec.ofNat 64 (2 ^ (8 * 2 ^ 2)) else 1) =
      BitVec.ofNat 64 (2 ^ (56 - 8 * L)) := by
  have h : ∀ L < 8,
      (if (!decide (L % 8 % 2 = 1)) = true then BitVec.ofNat 64 (2 ^ (8 * 2 ^ 0)) else 1) *
        (if (!decide (L % 8 / 2 % 2 = 1)) = true then BitVec.ofNat 64 (2 ^ (8 * 2 ^ 1)) else 1) *
        (if (!decide (L % 8 / 4 = 1)) = true then BitVec.ofNat 64 (2 ^ (8 * 2 ^ 2)) else 1) =
        BitVec.ofNat 64 (2 ^ (56 - 8 * L)) := by
    decide
  exact h L hL

/-- `fac_prod` for any index, by its lane. -/
theorem fac_prod' (x : Nat) :
    (if (!decide (x % 8 % 2 = 1)) = true then BitVec.ofNat 64 (2 ^ (8 * 2 ^ 0)) else 1) *
      (if (!decide (x % 8 / 2 % 2 = 1)) = true then BitVec.ofNat 64 (2 ^ (8 * 2 ^ 1)) else 1) *
      (if (!decide (x % 8 / 4 = 1)) = true then BitVec.ofNat 64 (2 ^ (8 * 2 ^ 2)) else 1) =
      BitVec.ofNat 64 (2 ^ (56 - 8 * (x % 8))) := by
  have := fac_prod (L := x % 8) (Nat.mod_lt _ (by decide))
  rw [Nat.mod_mod] at this
  exact this

/-- Bit `56 + c` of the complemented, shifted xL is the complement of bit
`c` of the index. -/
theorem notShift_bit (x : BitVec 64) {j c : Nat} (hj : j < 4) (hc : c < 8) :
    (~~~(x <<< (32 + 8 * j))).getLsbD (56 + c) = !((quarter (lo x) j).setWidth 64).getLsbD c := by
  rw [← index_val x hj, BitVec.getLsbD_not, BitVec.getLsbD_ushiftRight, decide_eq_true (by omega : 56 + c < 64),
    Bool.true_and]

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
  refine WP.mono (WP.keep [.t1] (index_run s hj) (by rfl) rfl) fun u ⟨⟨u1, um⟩, uk⟩ => ?_
  rw [WP.block_append_iff]
  have uk' : Keep lookRegs s u := uk.mono (by decide)
  refine WP.mono (rows_run E hj idx (by rw [uk.gpr (by decide), h7]) u1 uk' um h7 31 (by decide))
    fun v V => ?_
  unfold extract
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t3] (notShift_run v hj) (by rfl) rfl) fun w ⟨⟨w3, wm⟩, wk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t4] (factor_run w .t4 (c := 0) (by decide)) (by rfl) rfl)
    fun x ⟨⟨x4, xm⟩, xk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t1] (factor_run x .t1 (c := 1) (by decide)) (by rfl) rfl)
    fun y ⟨⟨y1, ym⟩, yk⟩ => ?_
  rw [WP.block_append_iff]
  have mul1 : WP isa (.block [.mul tmp tmp qReg]) y fun t =>
      t.gpr .t4 = y.gpr .t4 * y.gpr .t1 ∧ t.mem = y.mem := by brun
  refine WP.mono (WP.keep [.t4] mul1 (by rfl) rfl) fun z ⟨⟨z4, zm⟩, zk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t1] (factor_run z .t1 (c := 2) (by decide)) (by rfl) rfl)
    fun z' ⟨⟨z'1, z'm⟩, z'k⟩ => ?_
  rw [WP.block_append_iff]
  have mul2 : WP isa (.block [.mul qReg tmp qReg]) z' fun t =>
      t.gpr .t1 = z'.gpr .t4 * z'.gpr .t1 ∧ t.mem = z'.mem := by brun
  refine WP.mono (WP.keep [.t1] mul2 (by rfl) rfl) fun a ⟨⟨a1, am⟩, ak⟩ => ?_
  simp only [← List.append_assoc]
  -- the factors' product
  have hv3 : v.gpr .a3 = s.gpr .a3 := V.keep.gpr (by decide)
  have hb : ∀ c < 8, (w.gpr .t3).getLsbD (56 + c) = !((idx.setWidth 64).getLsbD c) := fun c hc => by
    rw [w3, hv3]; exact notShift_bit _ hj hc
  obtain ⟨b0, b1, b2⟩ := bit012 (idx.setWidth 64)
  have hn : (idx.setWidth 64).toNat = idx.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := idx.isLt; omega)
  rw [hn] at b0 b1 b2
  have x3 : x.gpr .t3 = w.gpr .t3 := xk.gpr (r := .t3) (by decide)
  have y3 : y.gpr .t3 = w.gpr .t3 := (yk.gpr (r := .t3) (by decide)).trans x3
  have z3 : z.gpr .t3 = w.gpr .t3 := (zk.gpr (r := .t3) (by decide)).trans y3
  have y4 : y.gpr .t4 = x.gpr .t4 := yk.gpr (r := .t4) (by decide)
  have z'4 : z'.gpr .t4 = z.gpr .t4 := z'k.gpr (r := .t4) (by decide)
  have zy1 : z.gpr .t1 = y.gpr .t1 := zk.gpr (r := .t1) (by decide)
  have hK : a.gpr .t1 = BitVec.ofNat 64 (2 ^ (56 - 8 * (idx.toNat % 8))) := by
    rw [a1, z'4, z4, z'1, y4, x4, y1, z3, x3, hb 0 (by decide), hb 1 (by decide), hb 2 (by decide),
      b0, b1, b2]
    exact fac_prod' _
  have ka : Keep lookRegs v a :=
    ((((wk.trans xk).trans yk).trans zk).trans z'k).trans ak |>.mono (by decide)
  have hm : a.mem = s.mem := by rw [am, z'm, zm, ym, xm, wm, V.mem]
  have pa : ∀ r, r ∉ lookRegs → a.gpr r = v.gpr r := fun r hr => ka.gpr hr
  have g2 : a.gpr .t2 = v.gpr .t2 := by
    rw [ak.gpr (by decide), z'k.gpr (by decide), zk.gpr (by decide), yk.gpr (by decide),
      xk.gpr (by decide), wk.gpr (by decide)]
  have g5 : a.gpr .t5 = v.gpr .t5 := by
    rw [ak.gpr (by decide), z'k.gpr (by decide), zk.gpr (by decide), yk.gpr (by decide),
      xk.gpr (by decide), wk.gpr (by decide)]
  have g6 : a.gpr .t6 = v.gpr .t6 := by
    rw [ak.gpr (by decide), z'k.gpr (by decide), zk.gpr (by decide), yk.gpr (by decide),
      xk.gpr (by decide), wk.gpr (by decide)]
  have g0 : a.gpr .t0 = v.gpr .t0 := by
    rw [ak.gpr (by decide), z'k.gpr (by decide), zk.gpr (by decide), yk.gpr (by decide),
      xk.gpr (by decide), wk.gpr (by decide)]
  refine WP.mono (WP.keep [.t2, .t5, .t6, .t0] (pick_run a hK (g2.trans V.p0) (g5.trans V.p1)
    (g6.trans V.p2) (g0.trans V.p3)) (by rfl) rfl) fun t ⟨⟨t2, tm⟩, tk⟩ => ?_
  refine ⟨?_, (V.keep.trans ka).trans tk |>.mono (by decide), by rw [tm, hm]⟩
  have hL : idx.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [t2, scanPlane_all, scanPlane_all, scanPlane_all, scanPlane_all, mul_byte _ hL, mul_byte _ hL,
    mul_byte _ hL, mul_byte _ hL]
  refine word_ext fun c hc => ?_
  have e := pack_byte (fun b => (planeWord64 s.mem S j b (idx.toNat / 8)).extractLsb' (8 * (idx.toNat % 8)) 8) hc
  rw [e, planeWord64_byte _ _ hj hc]

end VG.Proof.Blowfish.RISCV64
