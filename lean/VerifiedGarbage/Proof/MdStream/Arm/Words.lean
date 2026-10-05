import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Impl.MdStream.Arm
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.Arm.Common`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on ARMv7: common lemmas

The contracts the generic proofs are written against, what they need of a hash
function's parameters (`Shape`) and of its compression function (`CalleeOk`),
the call of the compression function (`compressAt`), saving and restoring the
caller's registers, and weakest-precondition rules for the instruction forms
used (which the proofs of other ARMv7 code use too).
-/

namespace VG.Proof.MdStream.Arm

open VG VG.Arm VG.Impl.MdStream.Arm
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)

/-! ## Addresses and regions -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine hf _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, VG.Proof.MdStream.Arm.toNat_ofNat_lt (by omega)]
  omega

/-- Addresses within a region that does not wrap around the 32-bit space. -/
theorem addr_off {a : BitVec 32} {k : Nat} (h : a.toNat + k < 2 ^ 32) :
    State.addr (a + BitVec.ofNat 32 k) = State.addr a + BitVec.ofNat 64 k := addr_add h

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- Byte `k` of the `n` bytes of stack arguments. -/
theorem argByte_eq {s : State} {n : Nat} (hsp : s.sp.toNat + n ≤ 2 ^ 32) {k : Nat} (hk : k < n) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [VG.Proof.MdStream.Arm.addr_off (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : VG.Proof.MdStream.Arm.Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl, rfl⟩

theorem Upd.subs (s : State) (d : Reg) (x y v : BitVec 32) : VG.Proof.MdStream.Arm.Upd s ((subFlags s x y).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, subFlags, h], rfl, rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- `s'` is `s` with other flags. -/
structure Fupd (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem op2_imm {s : State} {v : BitVec 32} (h : encodable v = true) : (Op2.imm v).eval s = some v := by
  simp [Op2.eval, h]

theorem op2_reg (s : State) (r : Reg) : (Op2.reg r).eval s = some (s.gpr r) := rfl

theorem op2_lsr {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsr n).eval s = some (s.gpr r >>> n) := by
  simp [Op2.eval, h]

theorem op2_lsl {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .lsl n).eval s = some (s.gpr r <<< n) := by
  simp [Op2.eval, h]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', VG.Proof.MdStream.Arm.Upd s s' d v → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_add {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.MdStream.Arm.Upd s s' d (s.gpr n + y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_sub {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.MdStream.Arm.Upd s s' d (s.gpr n - y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .sub d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n - y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_and {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.MdStream.Arm.Upd s s' d (s.gpr n &&& y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .and d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n &&& y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_orr {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.MdStream.Arm.Upd s s' d (s.gpr n ||| y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .orr d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n ||| y)) (by simp [exec, ho]) (k _ (Upd.setReg _ _ _))

theorem wp_subs {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.MdStream.Arm.Upd s s' d (s.gpr n - y) → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp [exec, ho])
    (k _ (Upd.subs _ _ _ _ _) rfl)

theorem wp_cmp {n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.MdStream.Arm.Fupd s s' → s'.z = (s.gpr n - y == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.cmp n o :: is)) s Q :=
  WP.cons (s' := subFlags s (s.gpr n) y) (by simp [exec, ho]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_rev {d m : Reg} (k : ∀ s', VG.Proof.MdStream.Arm.Upd s s' d (rev (s.gpr m)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev d m :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.MdStream.Arm.Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_ldr ho hin) (k _ (Upd.setReg _ _ _))

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', VG.Proof.MdStream.Arm.Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_str ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', VG.Proof.MdStream.Arm.Upd s s' t ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t ((s.mem _).setWidth 32)) (by simp [exec, ho, State.load8, hin])
    (k _ (Upd.setReg _ _ _))

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', VG.Proof.MdStream.Arm.Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := { s with mem := s.mem.writeW _ ((s.gpr t).setWidth 8) })
    (by simp [exec, ho, State.store8, hout]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)

theorem wp_ldrSp {t : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.sp + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.MdStream.Arm.Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t (s.mem.readW _ 32)) (by simp [exec, ho, State.load32, hin])
    (k _ (Upd.setReg _ _ _))

end

/-! ## Arithmetic -/

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

theorem eval_eq (s : State) : eval .eq s = some s.z := rfl
theorem eval_ne (s : State) : eval .ne s = some !s.z := rfl

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  rw [show BitVec.ofNat 32 a = BitVec.ofNat 32 (a - b) + BitVec.ofNat 32 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

theorem ofNat_shr {a n : Nat} (h : a < 2 ^ 32) : BitVec.ofNat 32 a >>> n = BitVec.ofNat 32 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem shr6 {a : Nat} (h : a < 2 ^ 32) : BitVec.ofNat 32 a >>> 6 = BitVec.ofNat 32 (a / 64) :=
  VG.Proof.MdStream.Arm.ofNat_shr h

theorem cmp0 {a : Nat} (h : a < 2 ^ 32) : (BitVec.ofNat 32 a - 0 == 0) = decide (a = 0) := by
  rw [show BitVec.ofNat 32 a - 0 = BitVec.ofNat 32 a by simp]; exact VG.Proof.MdStream.Arm.ofNat_beq_zero h

theorem and_pow_sub_one (x : BitVec 32) {n : Nat} (hn : n ≤ 32) :
    x &&& BitVec.ofNat 32 (2 ^ n - 1) = BitVec.ofNat 32 (x.toNat % 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  have : 2 ^ n ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hn
  have : 0 < 2 ^ n := Nat.two_pow_pos n
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2 ^ n - 1 < 2 ^ 32 by omega), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))]

/-! ## Saving and restoring registers -/

export VG.Arm.Spill (saveMem saveList_ok saveMem_frame restoreList_ok)

theorem save_sep (B : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) : Mem.Sep (B + BitVec.ofNat 64 d) 4 (B + BitVec.ofNat 64 e) 4 := by
  exact Offset.sep _ h (by omega) (by omega)

theorem readW_writeW_save (m : Mem) (B : Addr) (v : BitVec 32) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 e) v).readW (B + BitVec.ofNat 64 d) 32 = m.readW (B + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (VG.Proof.MdStream.Arm.save_sep B hd he h) (by decide)

/-! Saves at `so + d`, with the conditions on the literal offsets `d`, `e`
alone, which `decide` discharges. -/
theorem readW_writeW_save_so {so : Nat} (hso : so ≤ 256) (m : Mem) (B : Addr) (v : BitVec 32)
    {d e : Nat} (hd : d ≤ 64) (he : e ≤ 64) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (B + BitVec.ofNat 64 (so + e)) v).readW (B + BitVec.ofNat 64 (so + d)) 32 =
      m.readW (B + BitVec.ofNat 64 (so + d)) 32 :=
  VG.Proof.MdStream.Arm.readW_writeW_save m B v (by omega) (by omega) (by omega)

theorem readW_writeW_save_so_l {so : Nat} (hso : so ≤ 256) (m : Mem) (B : Addr) (v : BitVec 32)
    {e : Nat} (he : e ≤ 64) (h : 4 ≤ e) :
    (m.writeW (B + BitVec.ofNat 64 (so + e)) v).readW (B + BitVec.ofNat 64 so) 32 =
      m.readW (B + BitVec.ofNat 64 so) 32 :=
  VG.Proof.MdStream.Arm.readW_writeW_save m B v (by omega) (by omega) (by omega)


/-! ## Sizes -/

/-- The sizes the generic proofs support, checked for each hash function by
`decide`. -/
structure Dims (P : Params) : Prop where
  B : P.B = 64 ∨ P.B = 128
  L : 0 < P.L ∧ P.L ≤ 16
  N : 0 < P.N ∧ P.N ≤ 64
  so : P.so % 4 = 0 ∧ P.so ≤ 256
  enc : encodable (BitVec.ofNat 32 P.N) = true
  /-- The immediates the code compares and masks with. -/
  encB : encodable (BitVec.ofNat 32 P.B) = true ∧ encodable (BitVec.ofNat 32 (P.B - 1)) = true ∧
    encodable (BitVec.ofNat 32 (P.B - P.L)) = true ∧ encodable (BitVec.ofNat 32 (P.L - 1)) = true

section
variable {P : Params}

theorem Dims.pos (hd : VG.Proof.MdStream.Arm.Dims P) : 0 < P.B := by rcases hd.B with h | h <;> omega

theorem Dims.le (hd : VG.Proof.MdStream.Arm.Dims P) : 64 ≤ P.B ∧ P.B ≤ 128 := by rcases hd.B with h | h <;> omega

/-- The shift count of `direct`, `fill` and `finalize`. -/
theorem Dims.lg (hd : VG.Proof.MdStream.Arm.Dims P) : 1 ≤ Nat.log2 P.B ∧ Nat.log2 P.B ≤ 31 ∧ 2 ^ Nat.log2 P.B = P.B := by
  rcases hd.B with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

/-- A block size divides `2³²`. -/
theorem Dims.mod (hd : VG.Proof.MdStream.Arm.Dims P) (h l : Nat) : (h * 2 ^ 32 + l) % P.B = l % P.B := by
  rcases hd.B with e | e <;> rw [e] <;> omega

/-- A block size divides `2⁶⁴`. -/
theorem Dims.mod64 (hd : VG.Proof.MdStream.Arm.Dims P) (n : Nat) : n % 2 ^ 64 % P.B = n % P.B := by
  rcases hd.B with e | e <;> rw [e] <;> omega

theorem Dims.div_eq_zero (hd : VG.Proof.MdStream.Arm.Dims P) {a : Nat} : a / P.B = 0 ↔ a < P.B := by
  rcases hd.B with e | e <;> rw [e] <;> omega

theorem shrB (hd : VG.Proof.MdStream.Arm.Dims P) {a : Nat} (h : a < 2 ^ 32) :
    BitVec.ofNat 32 a >>> Nat.log2 P.B = BitVec.ofNat 32 (a / P.B) := by
  rw [VG.Proof.MdStream.Arm.ofNat_shr h, hd.lg.2.2]

/-- Whether `a >>> log₂ B` is zero. -/
theorem cmp0_shrB (hd : VG.Proof.MdStream.Arm.Dims P) {a : Nat} (h : a < 2 ^ 32) :
    (BitVec.ofNat 32 a >>> Nat.log2 P.B - 0 == 0) = decide (a < P.B) := by
  rw [VG.Proof.MdStream.Arm.shrB hd h, VG.Proof.MdStream.Arm.cmp0 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]
  exact decide_eq_decide.mpr hd.div_eq_zero

theorem andB (hd : VG.Proof.MdStream.Arm.Dims P) (x : BitVec 32) :
    x &&& BitVec.ofNat 32 (P.B - 1) = BitVec.ofNat 32 (x.toNat % P.B) := by
  have := hd.lg
  have e := VG.Proof.MdStream.Arm.and_pow_sub_one x (n := Nat.log2 P.B) (by omega)
  rwa [this.2.2] at e

theorem op2_shrB (hd : VG.Proof.MdStream.Arm.Dims P) {s : State} {r : Reg} :
    (Op2.shifted r .lsr (Nat.log2 P.B)).eval s = some (s.gpr r >>> Nat.log2 P.B) :=
  VG.Proof.MdStream.Arm.op2_lsr ⟨hd.lg.1, hd.lg.2.1⟩

theorem ofNat_shlB (hd : VG.Proof.MdStream.Arm.Dims P) {a : Nat} (h : P.B * a < 2 ^ 32) :
    BitVec.ofNat 32 a <<< Nat.log2 P.B = BitVec.ofNat 32 (P.B * a) := by
  have := hd.pos
  have : a ≤ P.B * a := Nat.le_mul_of_pos_left a this
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, hd.lg.2.2,
    Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega), Nat.mul_comm, Nat.mod_eq_of_lt h]

theorem op2_shlB (hd : VG.Proof.MdStream.Arm.Dims P) {s : State} {r : Reg} :
    (Op2.shifted r .lsl (Nat.log2 P.B)).eval s = some (s.gpr r <<< Nat.log2 P.B) :=
  VG.Proof.MdStream.Arm.op2_lsl ⟨hd.lg.1, hd.lg.2.1⟩

end

/-! ## Saving the caller's registers -/

section
variable {P : Params}

theorem saved_bound (hd : VG.Proof.MdStream.Arm.Dims P) : ∀ p ∈ saved P, P.so ≤ p.2 ∧ p.2 + 4 ≤ P.so + 36 := by
  have := hd.so
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem saved_nodup (P : Params) : ((saved P).map Prod.fst).Nodup := by
  simp only [saved, List.map_cons, List.map_nil]; decide

theorem saved_ne_r3 {p : Reg × Nat} (hp : p ∈ saved P) : p.1 ≠ .r3 := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide

/-- Saving `r4`–`r11` and `lr` with the scratch pointer in `b`. -/
theorem save_ok (hd : VG.Proof.MdStream.Arm.Dims P) {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hfit : (s.gpr b).toNat + (P.so + 48) ≤ 2 ^ 32)
    (hin : ∀ d, P.so ≤ d → d + 4 ≤ P.so + 36 → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.Arm.Spill.saveMem s.mem (State.addr (s.gpr b)) s.gpr (saved P) → WP isa (.block rest) s' Q) :
    WP isa (.block (save P b ++ rest)) s Q := by
  have := hd.so
  refine VG.Arm.Spill.saveList_ok (saved P) s Q (fun p hp => ?_) k
  have := VG.Proof.MdStream.Arm.saved_bound hd p hp
  exact ⟨by omega, by omega, hin _ this.1 this.2⟩

set_option simprocs false in
theorem saveMem_saved (hd : VG.Proof.MdStream.Arm.Dims P) (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ saved P, (VG.Arm.Spill.saveMem m B g (saved P)).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 := by
  have := hd.so
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [saved, VG.Arm.Spill.saveMem, Mem.readW_writeW_self32,
    VG.Proof.MdStream.Arm.readW_writeW_save_so this.2, VG.Proof.MdStream.Arm.readW_writeW_save_so_l this.2]

/-- Restoring `r4`–`r11` and `lr` from the save area at `scratch`. -/
theorem restore_ok (hd : VG.Proof.MdStream.Arm.Dims P) {s : State} {scr : BitVec 32} (h3 : s.gpr .r3 = scr)
    (hfit : scr.toNat + (P.so + 48) ≤ 2 ^ 32)
    (hin : ∀ d, P.so ≤ d → d + 4 ≤ P.so + 36 → InRegions (s.rd ++ s.wr) (State.addr scr + BitVec.ofNat 64 d) 4)
    (g : Reg → BitVec 32) (hsv : ∀ p ∈ saved P, s.mem.readW (State.addr scr + BitVec.ofNat 64 p.2) 32 = g p.1)
    {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved P, s'.gpr p.1 = g p.1) → (∀ r, r ∉ (saved P).map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block (restore P)) s Q := by
  have := hd.so
  rw [restore, ← List.append_nil ((saved P).map _)]
  refine VG.Arm.Spill.restoreList_ok (saved P) s Q (VG.Proof.MdStream.Arm.saved_nodup P) (fun p hp => ?_)
    fun s' ho hr hm hrd hwr hsp => WP.block_nil (k s' (fun p hp => ?_) hr hm hrd hwr hsp)
  · have := VG.Proof.MdStream.Arm.saved_bound hd p hp
    rw [h3]
    exact ⟨VG.Proof.MdStream.Arm.saved_ne_r3 hp, by omega, by omega, hin _ this.1 this.2⟩
  · rw [ho p hp, h3, hsv p hp]

/-- The callee-saved registers are the caller's again once `restore` has run. -/
theorem preserved_of {s₀ s' : State} (hsv : ∀ p ∈ saved P, s'.gpr p.1 = s₀.gpr p.1) :
    ∀ r ∈ preserved, s'.gpr r = s₀.gpr r := by
  intro r hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsv (.r4, P.so) (by simp [saved])
  · exact hsv (.r5, P.so + 4) (by simp [saved])
  · exact hsv (.r6, P.so + 8) (by simp [saved])
  · exact hsv (.r7, P.so + 12) (by simp [saved])
  · exact hsv (.r8, P.so + 16) (by simp [saved])
  · exact hsv (.r9, P.so + 20) (by simp [saved])
  · exact hsv (.r10, P.so + 24) (by simp [saved])
  · exact hsv (.r11, P.so + 28) (by simp [saved])
  · exact hsv (.lr, P.so + 32) (by simp [saved])

end

/-! ## The contracts

The generic proofs are written against these; each hash function's own
contracts are these for its instance. -/

/-- The 64-bit `count` argument of `update`/`finalize`, in `r2:r3` (AAPCS: the
low word in `r2`). -/
def count (s : State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

section
variable {P : Params} (H : Md P.B P.N P.L)

/-- The contract of the compression function: updates the hash value at
`r0` with the `r2` blocks at `r1`, with scratch space `r3` (`so` bytes). -/
def compressK : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), P.N⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), P.B * (s.gpr .r2).toNat⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), P.so⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    (s.gpr .r0).toNat + P.N ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + P.B * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
    (s.gpr .r3).toNat + P.so ≤ 2 ^ 32
  post s s' :=
    H.stateAt s'.mem (State.addr (s.gpr .r0)) =
      H.compressBlocks (H.stateAt s.mem (State.addr (s.gpr .r0))) s.mem (State.addr (s.gpr .r1))
        (s.gpr .r2).toNat
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

/-- The contract of `update`: if the state at `r0` represents a message of
`count` bytes (modulo 2⁶⁴) from any initial hash value, it then represents
that message followed by the `len` bytes at `data`. -/
def updK : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), P.N + P.B⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), P.so + 48⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + (P.N + P.B) ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
    (stackArg s 2).toNat + (P.so + 48) ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ iv m, H.Repr iv s.mem (State.addr (s.gpr .r0)) m → VG.Proof.MdStream.Arm.count s = BitVec.ofNat 64 m.length →
    H.Repr iv s'.mem (State.addr (s.gpr .r0))
      (m ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

/-- The contract of `finalize`: if the state at `r0` represents a message of
`count` bytes, writes its final hash value to `out` (`N` bytes). -/
def finK : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), P.N + P.B⟩
    let out : Region := ⟨State.addr (stackArg s 0), P.N⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), P.so + 48⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + (P.N + P.B) ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + P.N ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + (P.so + 48) ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ iv m, H.Repr iv s.mem (State.addr (s.gpr .r0)) m → H.lenOk m.length →
    VG.Proof.MdStream.Arm.count s = BitVec.ofNat 64 m.length → bytesAt s'.mem (State.addr (stackArg s 0)) P.N = H.hash iv m
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end

/-! ## What each hash function's own code must do -/

/-- The length field and the digest: `P.len` stores the length field for the
byte count in `r4:r5` at `r0 + N + B - L`, writing only `r9`, and `P.out`
writes the digest of the hash value at `r0` to `r6`, writing only `r9` and
`r10`. -/
structure Shape {P : Params} (H : Md P.B P.N P.L) : Prop where
  len : ∀ s : State, (s.gpr .r0).toNat + (P.N + P.B) ≤ 2 ^ 32 →
    InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 (P.N + (P.B - P.L))) P.L →
    WP isa (.block P.len) s fun s' => (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (P.N + (P.B - P.L)))
        (H.lenOf (s.gpr .r5 ++ s.gpr .r4))
  out : ∀ s : State, (s.gpr .r0).toNat + P.N ≤ 2 ^ 32 → (s.gpr .r6).toNat + P.N ≤ 2 ^ 32 →
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0)) P.N → InRegions s.wr (State.addr (s.gpr .r6)) P.N →
    Region.Disjoint ⟨State.addr (s.gpr .r0), P.N⟩ ⟨State.addr (s.gpr .r6), P.N⟩ →
    WP isa (.block P.out) s fun s' => (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr (s.gpr .r6)) (H.digest (H.stateAt s.mem (State.addr (s.gpr .r0))))

/-- What `compressAt` needs of the compression function it calls: that it is
correct, makes no calls, and never writes `r0` or `r3`. -/
structure CalleeOk {P : Params} (H : Md P.B P.N P.L) (code : Prog isa) : Prop where
  verified : ∀ s, (VG.Proof.MdStream.Arm.compressK H).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MdStream.Arm.compressK H).post s s'
  noCalls : code.noCalls = true
  keeps : ((instrs code).all fun i => dstOf i != some .r0 && dstOf i != some .r3) = true

/-! ## The compression function -/

/-- `n` sets `r2` to `v`. -/
def SetsN (n : Instr) (s : State) (v : BitVec 32) : Prop :=
  ∀ (is : List Instr) (Q : State → Prop), (∀ s', VG.Proof.MdStream.Arm.Upd s s' .r2 v → WP isa (.block is) s' Q) →
    WP isa (.block (n :: is)) s Q

theorem setsN_one (s : State) : VG.Proof.MdStream.Arm.SetsN (.mov .r2 (.imm 1)) s 1 := fun _ _ k => VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_imm (by decide)) k

theorem setsN_r7 (s : State) : VG.Proof.MdStream.Arm.SetsN (.mov .r2 (.reg .r7)) s (s.gpr .r7) := fun _ _ k => VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) k

/-- Compressing the `k` blocks at `r1` (their number set in `r2` by `n`) into
the hash value at `r0`, with scratch space at `r3`. -/
theorem compressWith_ok {P : Params} {H : Md P.B P.N P.L} {n : Instr} {s : State} {v : BitVec 32}
    (hn : VG.Proof.MdStream.Arm.SetsN n s v) {k : Nat} (hkv : v.toNat = k) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.Arm.CalleeOk H code)
    {st scr src : BitVec 32}
    (h0 : s.gpr .r0 = st) (h3 : s.gpr .r3 = scr) (h1 : s.gpr .r1 = src)
    (f₀ : st.toNat + P.N ≤ 2 ^ 32) (f₁ : src.toNat + P.B * k ≤ 2 ^ 32) (f₃ : scr.toNat + P.so ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨State.addr st, P.N⟩ ⟨State.addr scr, P.so⟩)
    (d₂ : Region.Disjoint ⟨State.addr src, P.B * k⟩ ⟨State.addr st, P.N⟩)
    (d₃ : Region.Disjoint ⟨State.addr src, P.B * k⟩ ⟨State.addr scr, P.so⟩)
    (hc : Covers [⟨State.addr src, P.B * k⟩, ⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.gpr .r0 = st → s'.gpr .r3 = scr → s'.sp = s.sp →
      Frame [⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem (State.addr st) =
        H.compressBlocks (H.stateAt s.mem (State.addr st)) s.mem (State.addr src) k → Q s') :
    WP isa (compressWith n name code) s Q := by
  have hk : ∀ i ∈ instrs code, dstOf i ≠ some .r0 ∧ dstOf i ≠ some .r3 := by
    intro i hi
    have := List.all_eq_true.mp hf.keeps i hi
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact this
  unfold compressWith
  refine WP.seq (hn _ _ fun s₁ u₁ => WP.block_nil ?_)
  have e0 : s₁.gpr .r0 = st := by rw [u₁.other _ (by decide), h0]
  have e1 : s₁.gpr .r1 = src := by rw [u₁.other _ (by decide), h1]
  have e2 : s₁.gpr .r2 = v := u₁.gpr
  have e3 : s₁.gpr .r3 = scr := by rw [u₁.other _ (by decide), h3]
  have c : ∀ r, r ∉ linkRegs → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr s₁ h
  refine WP.call (k := VG.Proof.MdStream.Arm.compressK H) hf.verified
    (rd := [⟨State.addr src, P.B * k⟩]) (wr := [⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩]) ?_ ?_ ?_ ?_
    hf.noCalls
  · simp only [VG.Proof.MdStream.Arm.compressK, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c _ (show Reg.r0 ∉ linkRegs by decide), c _ (show Reg.r1 ∉ linkRegs by decide),
      c _ (show Reg.r2 ∉ linkRegs by decide), c _ (show Reg.r3 ∉ linkRegs by decide), e0, e1, e2, e3, hkv]
    exact ⟨trivial, trivial, d₁, d₂, d₃, f₀, f₁, f₃⟩
  · rw [u₁.rd, u₁.wr]; simpa using hc
  · rw [u₁.wr]; exact hw
  · intro s' hrd hwr hsp hf' hcs hg hpost
    simp only [VG.Proof.MdStream.Arm.compressK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
      c _ (show Reg.r0 ∉ linkRegs by decide), c _ (show Reg.r1 ∉ linkRegs by decide),
      c _ (show Reg.r2 ∉ linkRegs by decide), e0, e1, e2, u₁.mem, hkv] at hpost
    refine hQ s' (hrd.trans u₁.rd) (hwr.trans u₁.wr) (fun r hr hlr => ?_)
      (by rw [hg _ (fun i hi => (hk i hi).1) (by decide), e0])
      (by rw [hg _ (fun i hi => (hk i hi).2) (by decide), e3]) (hsp.trans u₁.sp) (u₁.mem ▸ hf') hpost
    have : r ≠ .r2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hcs r hr hlr, u₁.other r this]

/-- Compressing the block at `r1` into the hash value at `r0`, with scratch
space at `r3`. -/
theorem compressAt_ok {P : Params} {H : Md P.B P.N P.L} {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.Arm.CalleeOk H code)
    {s : State} {st scr src : BitVec 32}
    (h0 : s.gpr .r0 = st) (h3 : s.gpr .r3 = scr) (h1 : s.gpr .r1 = src)
    (f₀ : st.toNat + P.N ≤ 2 ^ 32) (f₁ : src.toNat + P.B ≤ 2 ^ 32) (f₃ : scr.toNat + P.so ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨State.addr st, P.N⟩ ⟨State.addr scr, P.so⟩)
    (d₂ : Region.Disjoint ⟨State.addr src, P.B⟩ ⟨State.addr st, P.N⟩)
    (d₃ : Region.Disjoint ⟨State.addr src, P.B⟩ ⟨State.addr scr, P.so⟩)
    (hc : Covers [⟨State.addr src, P.B⟩, ⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      s'.gpr .r0 = st → s'.gpr .r3 = scr → s'.sp = s.sp →
      Frame [⟨State.addr st, P.N⟩, ⟨State.addr scr, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem (State.addr st) =
        H.compress (H.stateAt s.mem (State.addr st)) (H.blockAt s.mem (State.addr src)) → Q s') :
    WP isa (compressAt name code) s Q := by
  have e : P.B * 1 = P.B := Nat.mul_one _
  refine VG.Proof.MdStream.Arm.compressWith_ok (VG.Proof.MdStream.Arm.setsN_one s) (k := 1) rfl hf h0 h3 h1 f₀ (by rw [e]; exact f₁) f₃ d₁
    (by rw [e]; exact d₂) (by rw [e]; exact d₃) (by rw [e]; exact hc) hw
    fun s' hrd hwr hcs h0' h3' hsp hf' hs => hQ s' hrd hwr hcs h0' h3' hsp hf' (by rw [hs, Md.compressBlocks_one])

end VG.Proof.MdStream.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.Arm.Finalize`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on ARMv7: `finalize`

The functional correctness of `finalize`, for any hash function (`Md`) whose
code stores the length field and writes the digest as `Shape` says, and any
correct compression function (`CalleeOk`). The same structure as the AArch64
proof (`VG.Proof.MdStream.AArch64.Finalize`), with `state` in `r0`, `scratch`
in `r3`, `out` in `r6`, `count` in `r4:r5` (low, high), the buffered bytes in
`r7`, and whether the block is not the last in `r8`. Constant time is proven
for each hash function's code by the taint analysis, calls included, from the
initial taint `τ₀`.
-/

namespace VG.Proof.MdStream.Arm.Finalize

open VG VG.Arm VG.Impl.MdStream.Arm
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame bytesAt_congr)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev cnt : Nat := (VG.Proof.MdStream.Arm.count s₀).toNat
abbrev out : BitVec 32 := stackArg s₀ 0
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev stA : Addr := State.addr (VG.Proof.MdStream.Arm.Finalize.st s₀)
abbrev outA : Addr := State.addr (VG.Proof.MdStream.Arm.Finalize.out s₀)
abbrev scA : Addr := State.addr (VG.Proof.MdStream.Arm.Finalize.scr s₀)
abbrev stR : Region := ⟨VG.Proof.MdStream.Arm.Finalize.stA s₀, P.N + P.B⟩
abbrev outR : Region := ⟨VG.Proof.MdStream.Arm.Finalize.outA s₀, P.N⟩
abbrev scR : Region := ⟨VG.Proof.MdStream.Arm.Finalize.scA s₀, P.so + 48⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
/-- The buffer. -/
abbrev buf : Addr := VG.Proof.MdStream.Arm.Finalize.stA s₀ + BitVec.ofNat 64 P.N

/-- The caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved P, m.readW (VG.Proof.MdStream.Arm.Finalize.scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

end

section
variable {P : Params} (H : Md P.B P.N P.L) (s₀ : State)

/-- The messages the initial state represents, from `iv`. -/
def R₀ (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀) m ∧ VG.Proof.MdStream.Arm.count s₀ = BitVec.ofNat 64 m.length

/-- The final hash value, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.compress (H.stateAt mem (VG.Proof.MdStream.Arm.Finalize.stA s₀))
    (H.parse fun t => (bytesAt mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀) n ++ List.replicate (P.B - n) 0).getD t 0))
    (H.parse fun t => (List.replicate (P.B - P.L) 0 ++ H.lenBytes m.length).getD t 0)

/-- The final hash value, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.stateAt mem (VG.Proof.MdStream.Arm.Finalize.stA s₀))
    (H.parse fun t => (bytesAt mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀) n ++ List.replicate (P.B - P.L - n) 0 ++
      H.lenBytes m.length).getD t 0)

end

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.MdStream.Arm.Finalize.argR s₀]
  wr : s₀.wr = [VG.Proof.MdStream.Arm.Finalize.stR P s₀, VG.Proof.MdStream.Arm.Finalize.outR P s₀, VG.Proof.MdStream.Arm.Finalize.scR P s₀]
  st_out : (VG.Proof.MdStream.Arm.Finalize.stR P s₀).Disjoint (VG.Proof.MdStream.Arm.Finalize.outR P s₀)
  st_scr : (VG.Proof.MdStream.Arm.Finalize.stR P s₀).Disjoint (VG.Proof.MdStream.Arm.Finalize.scR P s₀)
  out_scr : (VG.Proof.MdStream.Arm.Finalize.outR P s₀).Disjoint (VG.Proof.MdStream.Arm.Finalize.scR P s₀)
  a_st : (VG.Proof.MdStream.Arm.Finalize.argR s₀).Disjoint (VG.Proof.MdStream.Arm.Finalize.stR P s₀)
  a_out : (VG.Proof.MdStream.Arm.Finalize.argR s₀).Disjoint (VG.Proof.MdStream.Arm.Finalize.outR P s₀)
  a_scr : (VG.Proof.MdStream.Arm.Finalize.argR s₀).Disjoint (VG.Proof.MdStream.Arm.Finalize.scR P s₀)
  st_fit : (VG.Proof.MdStream.Arm.Finalize.st s₀).toNat + (P.N + P.B) ≤ 2 ^ 32
  out_fit : (VG.Proof.MdStream.Arm.Finalize.out s₀).toNat + P.N ≤ 2 ^ 32
  scr_fit : (VG.Proof.MdStream.Arm.Finalize.scr s₀).toNat + (P.so + 48) ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32

theorem pre_of {P : Params} {H : Md P.B P.N P.L} {s₀ : State} (h : (VG.Proof.MdStream.Arm.finK H).pre s₀) : VG.Proof.MdStream.Arm.Finalize.Pre P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-! ## Invariants -/

structure Common (P : Params) (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r0 : s.gpr .r0 = VG.Proof.MdStream.Arm.Finalize.st s₀
  r3 : s.gpr .r3 = VG.Proof.MdStream.Arm.Finalize.scr s₀
  r6 : s.gpr .r6 = VG.Proof.MdStream.Arm.Finalize.out s₀
  r4 : s.gpr .r4 = s₀.gpr .r2
  r5 : s.gpr .r5 = s₀.gpr .r3
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.MdStream.Arm.Finalize.stR P s₀, VG.Proof.MdStream.Arm.Finalize.scR P s₀] s₀.mem s.mem
  saved : VG.Proof.MdStream.Arm.Finalize.Saved P s₀ s.mem

/-- Where the zeros padding a block end: at the end of the buffer if `k = 1`
(the block is not the last one), otherwise where the length field starts. -/
def lim (P : Params) (k : Nat) : Nat := if k = 1 then P.B else P.B - P.L

theorem lim_one (P : Params) : VG.Proof.MdStream.Arm.Finalize.lim P 1 = P.B := by simp [VG.Proof.MdStream.Arm.Finalize.lim]

theorem lim_zero (P : Params) : VG.Proof.MdStream.Arm.Finalize.lim P 0 = P.B - P.L := by simp [VG.Proof.MdStream.Arm.Finalize.lim]

theorem lim_le (P : Params) (k : Nat) : VG.Proof.MdStream.Arm.Finalize.lim P k ≤ P.B := by
  unfold VG.Proof.MdStream.Arm.Finalize.lim; split <;> omega

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (k n : Nat) (s : State) : Prop
    extends VG.Proof.MdStream.Arm.Finalize.Common P s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ VG.Proof.MdStream.Arm.Finalize.lim P k
  r7 : s.gpr .r7 = BitVec.ofNat 32 n
  r8 : s.gpr .r8 = BitVec.ofNat 32 k
  hash : ∀ iv m, VG.Proof.MdStream.Arm.Finalize.R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m =
    H.digest (if k = 1 then VG.Proof.MdStream.Arm.Finalize.Fin1 H s₀ s.mem n m else VG.Proof.MdStream.Arm.Finalize.Fin0 H s₀ s.mem n m)

/-- All blocks are compressed. -/
def Done {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  VG.Proof.MdStream.Arm.Finalize.Common P s₀ s ∧ ∀ iv m, VG.Proof.MdStream.Arm.Finalize.R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m = H.digest (H.stateAt s.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀))

def keepRegs : List Reg := [.r0, .r3, .r6, .r4, .r5, .lr]

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem cnt_mod (hd : VG.Proof.MdStream.Arm.Dims P) (s₀ : State) : VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B = (s₀.gpr .r2).toNat % P.B := by
  simp only [VG.Proof.MdStream.Arm.Finalize.cnt, VG.Proof.MdStream.Arm.count]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (s₀.gpr .r2).isLt, Nat.shiftLeft_eq]
  exact hd.mod _ _

theorem R₀.length (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} {iv : H.HV} {m : List Byte} (h : VG.Proof.MdStream.Arm.Finalize.R₀ H s₀ iv m) :
    VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B = m.length % P.B := by
  rw [VG.Proof.MdStream.Arm.Finalize.cnt, h.2, BitVec.toNat_ofNat]
  exact hd.mod64 _

theorem buf_add (s₀ : State) (n : Nat) : VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 n = VG.Proof.MdStream.Arm.Finalize.stA s₀ + BitVec.ofNat 64 (P.N + n) :=
  VG.Proof.MdStream.Arm.add_ofNat _ _ _

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : VG.Proof.MdStream.Arm.Finalize.Common P s₀ s)
    (hg : ∀ r ∈ VG.Proof.MdStream.Arm.Finalize.keepRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    VG.Proof.MdStream.Arm.Finalize.Common P s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r0 := by rw [hg _ (by simp [VG.Proof.MdStream.Arm.Finalize.keepRegs])]; exact h.r0
  r3 := by rw [hg _ (by simp [VG.Proof.MdStream.Arm.Finalize.keepRegs])]; exact h.r3
  r6 := by rw [hg _ (by simp [VG.Proof.MdStream.Arm.Finalize.keepRegs])]; exact h.r6
  r4 := by rw [hg _ (by simp [VG.Proof.MdStream.Arm.Finalize.keepRegs])]; exact h.r4
  r5 := by rw [hg _ (by simp [VG.Proof.MdStream.Arm.Finalize.keepRegs])]; exact h.r5
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Common.of_upd {s₀ : State} {s s' : State} (h : VG.Proof.MdStream.Arm.Finalize.Common P s₀ s) {d : Reg} {v : BitVec 32}
    (u : VG.Proof.MdStream.Arm.Upd s s' d v) (hd : d ∉ VG.Proof.MdStream.Arm.Finalize.keepRegs) : VG.Proof.MdStream.Arm.Finalize.Common P s₀ s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem Common.of_flags {s₀ : State} {s s' : State} (h : VG.Proof.MdStream.Arm.Finalize.Common P s₀ s) (u : VG.Proof.MdStream.Arm.Fupd s s') : VG.Proof.MdStream.Arm.Finalize.Common P s₀ s' :=
  h.of_gpr (fun r _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp

/-- Where the caller's registers are saved. -/
theorem saved_sub (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved P) :
    Region.Sub ⟨VG.Proof.MdStream.Arm.Finalize.scA s₀ + BitVec.ofNat 64 p.2, 4⟩ (VG.Proof.MdStream.Arm.Finalize.scR P s₀) := by
  have := VG.Proof.MdStream.Arm.saved_bound hd p hp; have hd_so := hd.so
  exact VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega)

/-- Writing buffer bytes `[n, n + |xs|)` keeps `Common`'s memory facts. -/
theorem Common.writeBuf (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Finalize.Pre P s₀) {s : State} (h : VG.Proof.MdStream.Arm.Finalize.Common P s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ P.B) :
    Frame [VG.Proof.MdStream.Arm.Finalize.stR P s₀] s.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      Frame [VG.Proof.MdStream.Arm.Finalize.stR P s₀, VG.Proof.MdStream.Arm.Finalize.scR P s₀] s₀.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      VG.Proof.MdStream.Arm.Finalize.Saved P s₀ (VG.WriteBytes.writeBytes s.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) := by
  have hBle := hd.le
  have hd_N := hd.N
  have hf : Frame [VG.Proof.MdStream.Arm.Finalize.stR P s₀] s.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) := by
    refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
    rw [VG.Proof.MdStream.Arm.Finalize.buf_add]
    exact VG.Proof.MdStream.Arm.contains_offset (by omega) (by omega)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  refine hf.readW (r := ⟨VG.Proof.MdStream.Arm.Finalize.scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (VG.Proof.MdStream.Arm.Finalize.saved_sub hd hp')

/-- Byte `k` of the buffer, addressed as `[r0 + k, #N]`. -/
theorem buf_addr {s₀ : State} (hp : VG.Proof.MdStream.Arm.Finalize.Pre P s₀) {k : Nat} (hk : k < P.B) :
    State.addr (VG.Proof.MdStream.Arm.Finalize.st s₀ + BitVec.ofNat 32 k + BitVec.ofNat 32 P.N) = VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 k := by
  have hp_st_fit := hp.st_fit
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, VG.Proof.MdStream.Arm.addr_off (by omega), VG.Proof.MdStream.Arm.add_ofNat, Nat.add_comm]

end

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (P : Params) (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ .r8 :: VG.Proof.MdStream.Arm.Finalize.keepRegs, s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  r12 : s.gpr .r12 = 0
  r7 : s.gpr .r7 = BitVec.ofNat 32 (n + j)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (lim - n - j)
  mem : s.mem = VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 n) (List.replicate j 0)

/-- The zeroing loop's body. -/
def zeroBody (P : Params) : List Instr :=
  [.dp .add .r1 .r0 (.reg .r7), .strb .r12 .r1 P.N, .dp .add .r7 .r7 (.imm 1), .subs .r9 .r9 (.imm 1)]

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem zero_step (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Finalize.Pre P s₀) {sI : State} (hC : VG.Proof.MdStream.Arm.Finalize.Common P s₀ sI)
    {n lim j : Nat} (hlim : lim ≤ P.B) (hj : j < lim - n) {s : State} (h : VG.Proof.MdStream.Arm.Finalize.Zero P s₀ sI n lim j s) :
    WP isa (.block (VG.Proof.MdStream.Arm.Finalize.zeroBody P)) s fun s' =>
      VG.Proof.MdStream.Arm.Finalize.Zero P s₀ sI n lim (j + 1) s' ∧ s'.z = (BitVec.ofNat 32 (lim - n - (j + 1)) == 0) := by
  have hBle := hd.le
  have hd_N := hd.N; have hp_st_fit := hp.st_fit
  have hr0 : s.gpr .r0 = VG.Proof.MdStream.Arm.Finalize.st s₀ := by rw [h.keep _ (by simp [VG.Proof.MdStream.Arm.Finalize.keepRegs]), hC.r0]
  have hout : InRegions s.wr (VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨VG.Proof.MdStream.Arm.Finalize.stR P s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [VG.Proof.MdStream.Arm.Finalize.buf_add, VG.Proof.MdStream.Arm.add_ofNat]
    exact VG.Proof.MdStream.Arm.contains_offset (by omega) (by omega)
  unfold VG.Proof.MdStream.Arm.Finalize.zeroBody
  refine VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₁ u₁ =>
    VG.Proof.MdStream.Arm.wp_strb (a := VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) (by omega) ?_
      (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hr0, h.r7, VG.Proof.MdStream.Arm.Finalize.buf_addr hp (by omega), VG.Proof.MdStream.Arm.Finalize.buf]
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  refine VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₃ u₃ => VG.Proof.MdStream.Arm.wp_subs (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₄ u₄ z₄ =>
    WP.block_nil ⟨⟨by omega, fun r hr => ?_, by rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd],
    by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr], by rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp], ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .r9 ∧ r ≠ .r7 ∧ r ≠ .r1 := by
      simp only [VG.Proof.MdStream.Arm.Finalize.keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other r this.1, u₃.other r this.2.1, g₂.gpr, u₁.other r this.2.2, h.keep r hr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r12]
  · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r7,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r9,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Proof.MdStream.Arm.sub_ofNat (by omega), Nat.sub_sub]
  · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide), h.r12, h.mem, List.replicate_succ',
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [z₄, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r9,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Proof.MdStream.Arm.sub_ofNat (by omega), Nat.sub_sub, Nat.sub_sub]

theorem zero_ok (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Finalize.Pre P s₀) {sI : State} (hC : VG.Proof.MdStream.Arm.Finalize.Common P s₀ sI) {n lim : Nat}
    (hlim : lim ≤ P.B) (hn : n ≤ lim) {s : State} (h : VG.Proof.MdStream.Arm.Finalize.Zero P s₀ sI n lim 0 s)
    (hz : s.z = decide (lim - n = 0)) :
    WP isa (.ite .eq (.block []) (.loop (.block (VG.Proof.MdStream.Arm.Finalize.zeroBody P)) .ne)) s (VG.Proof.MdStream.Arm.Finalize.Zero P s₀ sI n lim (lim - n)) := by
  have hBle := hd.le
  refine WP.ite (decide (lim - n = 0)) (by show VG.Arm.eval .eq s = _; rw [VG.Proof.MdStream.Arm.eval_eq, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ VG.Proof.MdStream.Arm.Finalize.Zero P s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (VG.Proof.MdStream.Arm.Finalize.zero_step hd hp hC hlim hj hZ) fun s' ⟨hZ', hz'⟩ => ?_
    have hz'' : isa.eval .ne s' = some (decide (lim - n - (j + 1) ≠ 0)) := by
      show VG.Arm.eval .ne s' = _
      rw [VG.Proof.MdStream.Arm.eval_ne, hz', VG.Proof.MdStream.Arm.ofNat_beq_zero (by omega)]
      simp
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by rw [hz'', decide_eq_false fun h => h hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by rw [hz'', decide_eq_true hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The compression of the buffer. -/
theorem compress_buf (hd : VG.Proof.MdStream.Arm.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.Arm.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.Arm.Finalize.Pre P s₀) {s : State} (hC : VG.Proof.MdStream.Arm.Finalize.Common P s₀ s)
    (hr1 : s.gpr .r1 = VG.Proof.MdStream.Arm.Finalize.st s₀ + BitVec.ofNat 32 P.N) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MdStream.Arm.Finalize.Common P s₀ s' → (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      H.stateAt s'.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀) = H.compress (H.stateAt s.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀)) (H.blockAt s.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀)) → Q s') :
    WP isa (compressAt name code) s Q := by
  have hBle := hd.le
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hd_N := hd.N; have hd_so := hd.so
  have eN : Region.Sub ⟨VG.Proof.MdStream.Arm.Finalize.stA s₀, P.N⟩ (VG.Proof.MdStream.Arm.Finalize.stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.MdStream.Arm.Finalize.scA s₀, P.so⟩ (VG.Proof.MdStream.Arm.Finalize.scR P s₀) := Region.sub_prefix (by omega)
  have ha : State.addr (VG.Proof.MdStream.Arm.Finalize.st s₀ + BitVec.ofNat 32 P.N) = VG.Proof.MdStream.Arm.Finalize.buf P s₀ := VG.Proof.MdStream.Arm.addr_off (by omega)
  have eb : Region.Sub ⟨VG.Proof.MdStream.Arm.Finalize.buf P s₀, P.B⟩ (VG.Proof.MdStream.Arm.Finalize.stR P s₀) := VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega)
  have d₂ : Region.Disjoint ⟨State.addr (VG.Proof.MdStream.Arm.Finalize.st s₀ + BitVec.ofNat 32 P.N), P.B⟩ ⟨VG.Proof.MdStream.Arm.Finalize.stA s₀, P.N⟩ := by
    rw [ha]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  have d₃ : Region.Disjoint ⟨State.addr (VG.Proof.MdStream.Arm.Finalize.st s₀ + BitVec.ofNat 32 P.N), P.B⟩ ⟨VG.Proof.MdStream.Arm.Finalize.scA s₀, P.so⟩ := by
    rw [ha]; exact (hp.st_scr.sub_left eb).sub_right eso
  refine VG.Proof.MdStream.Arm.compressAt_ok hf hC.r0 hC.r3 hr1 (by omega_using [hst]) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hst])
    (by omega_using [hsc]) ((hp.st_scr.sub_left eN).sub_right eso) d₂ d₃
    ?_ ?_ fun s' hrd hwr hcs h0 h3 hsp hf' hstate => hQ s' ?_ hcs (by rw [hstate, ha])
  · rw [hC.rd, hC.wr, hp.rd, hp.wr, ha]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.MdStream.Arm.Finalize.stR P s₀, by simp, P.N, rfl, by simp⟩
    · exact ⟨VG.Proof.MdStream.Arm.Finalize.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.Arm.Finalize.scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.MdStream.Arm.Finalize.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.Arm.Finalize.scR P s₀, by simp, 0, by simp, by simp⟩
  · refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, h0, h3, by rw [hcs _ (by decide) (by decide)]; exact hC.r6,
      by rw [hcs _ (by decide) (by decide)]; exact hC.r4, by rw [hcs _ (by decide) (by decide)]; exact hC.r5,
      hsp.trans hC.sp, hC.frame.trans (hf'.sub ?_), fun p hp' => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.MdStream.Arm.Finalize.stR P s₀, by simp, eN⟩
      · exact ⟨VG.Proof.MdStream.Arm.Finalize.scR P s₀, by simp, eso⟩
    · rw [← hC.saved p hp']
      have := VG.Proof.MdStream.Arm.saved_bound hd p hp'
      refine hf'.readW (r := ⟨VG.Proof.MdStream.Arm.Finalize.scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (VG.Proof.MdStream.Arm.Finalize.saved_sub hd hp')).sub_right eN
      · exact Offset.disjoint_base _ this.1 (by omega_using [this.2, hd.so.2])

/-- The loop's postcondition for one iteration. -/
def Step {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (k : Nat) (s : State) : Prop :=
  (VG.Arm.eval .eq s = some false ∧ VG.Proof.MdStream.Arm.Finalize.Done H s₀ s) ∨ (VG.Arm.eval .eq s = some true ∧ k = 1 ∧ VG.Proof.MdStream.Arm.Finalize.LInv H s₀ 0 0 s)

theorem body_eq (name : String) (code : Prog isa) : finalizeBody P name code =
    .seq (.block [.mov .r9 (.imm (BitVec.ofNat 32 P.B)), .cmp .r8 (.imm 0)])
    (.seq (.ite .eq (.block [.mov .r9 (.imm (BitVec.ofNat 32 (P.B - P.L)))]) (.block []))
    (.seq (.block [.mov .r12 (.imm 0), .subs .r9 .r9 (.reg .r7)])
    (.seq (.ite .eq (.block []) (.loop (.block (VG.Proof.MdStream.Arm.Finalize.zeroBody P)) .ne))
    (.seq (.block [.cmp .r8 (.imm 0)])
    (.seq (.ite .eq (.block P.len) (.block []))
    (.seq (.block [.dp .add .r1 .r0 (.imm (BitVec.ofNat 32 P.N))])
    (.seq (compressAt name code) (.block [.mov .r7 (.imm 0), .subs .r8 .r8 (.imm 1)])))))))) := rfl

theorem body_ok (hd : VG.Proof.MdStream.Arm.Dims P) (hs : VG.Proof.MdStream.Arm.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.Arm.CalleeOk H code)
    {s₀ : State} (hp : VG.Proof.MdStream.Arm.Finalize.Pre P s₀) {k n : Nat} {s : State} (h : VG.Proof.MdStream.Arm.Finalize.LInv H s₀ k n s) :
    WP isa (finalizeBody P name code) s (VG.Proof.MdStream.Arm.Finalize.Step H s₀ k) := by
  have hk := h.k_le; have hn := h.n_le; have hst := hp.st_fit; have hd_N := hd.N; have hd_le := hd.le; have hd_L := hd.L
  have hlim := VG.Proof.MdStream.Arm.Finalize.lim_le P k
  have hC := h.toCommon
  rw [VG.Proof.MdStream.Arm.Finalize.body_eq]
  -- `r9 := B` or `B - L`: the end of the zeros.
  refine WP.seq (VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_imm hd.encB.1) fun s₁ u₁ => VG.Proof.MdStream.Arm.wp_cmp (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₂ f₂ z₂ =>
    WP.block_nil ?_)
  have hz₂ : s₂.z = decide (k = 0) := by rw [z₂, u₁.other _ (by decide), h.r8, VG.Proof.MdStream.Arm.cmp0 (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .r9 = BitVec.ofNat 32 (VG.Proof.MdStream.Arm.Finalize.lim P k) ∧
      (∀ r, r ≠ .r9 → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      s₃.sp = s.sp) ?_ fun s₃ ⟨h9₃, g₃, m₃, rd₃, wr₃, sp₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show VG.Arm.eval .eq s₂ = _; rw [VG.Proof.MdStream.Arm.eval_eq, hz₂])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_imm hd.encB.2.2.1) fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr, VG.Proof.MdStream.Arm.Finalize.lim_zero], fun r hr => ?_,
        by rw [u₃.mem, f₂.mem, u₁.mem], by rw [u₃.rd, f₂.rd, u₁.rd], by rw [u₃.wr, f₂.wr, u₁.wr],
        by rw [u₃.sp, f₂.sp, u₁.sp]⟩
      rw [u₃.other r hr, f₂.gpr, u₁.other r hr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [f₂.gpr, u₁.gpr, show k = 1 by omega, VG.Proof.MdStream.Arm.Finalize.lim_one], fun r hr => ?_,
        by rw [f₂.mem, u₁.mem], by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr], by rw [f₂.sp, u₁.sp]⟩
      rw [f₂.gpr, u₁.other r hr]
  -- Zero the rest of the buffer, up to `lim`.
  refine WP.seq (VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₄ u₄ => VG.Proof.MdStream.Arm.wp_subs (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₅ u₅ z₅ =>
    WP.block_nil ?_)
  have h9₅ : s₅.gpr .r9 = BitVec.ofNat 32 (VG.Proof.MdStream.Arm.Finalize.lim P k - n) := by
    rw [u₅.gpr, u₄.other _ (by decide), h9₃, u₄.other _ (by decide), g₃ _ (by decide), h.r7,
      VG.Proof.MdStream.Arm.sub_ofNat (by omega)]
  have hZ : VG.Proof.MdStream.Arm.Finalize.Zero P s₀ s n (VG.Proof.MdStream.Arm.Finalize.lim P k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => ?_, by rw [u₅.rd, u₄.rd, rd₃], by rw [u₅.wr, u₄.wr, wr₃],
      by rw [u₅.sp, u₄.sp, sp₃], ?_, ?_, by rw [h9₅, Nat.sub_zero], ?_⟩
    · have : r ≠ .r9 ∧ r ≠ .r12 := by
        simp only [VG.Proof.MdStream.Arm.Finalize.keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u₅.other r this.1, u₄.other r this.2, g₃ r this.1]
    · rw [u₅.other _ (by decide), u₄.gpr]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), h.r7, Nat.add_zero]
    · rw [u₅.mem, u₄.mem, m₃, List.replicate_zero, VG.WriteBytes.writeBytes_nil]
  have hz₅ : s₅.z = decide (VG.Proof.MdStream.Arm.Finalize.lim P k - n - 0 = 0) := by
    rw [z₅, ← u₅.gpr, h9₅, VG.Proof.MdStream.Arm.ofNat_beq_zero (by omega), Nat.sub_zero]
  refine WP.seq (WP.mono (VG.Proof.MdStream.Arm.Finalize.zero_ok hd hp hC (by omega) hn hZ hz₅) fun s₆ hZ₆ => ?_)
  obtain ⟨hf₆, hfr₆, hsv₆⟩ := hC.writeBuf hd hp (n := n) (xs := List.replicate (VG.Proof.MdStream.Arm.Finalize.lim P k - n) 0)
    (by simp only [List.length_replicate]; omega)
  have hC₆ : VG.Proof.MdStream.Arm.Finalize.Common P s₀ s₆ :=
    ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp [VG.Proof.MdStream.Arm.Finalize.keepRegs]), hC.r0],
      by rw [hZ₆.keep _ (by simp [VG.Proof.MdStream.Arm.Finalize.keepRegs]), hC.r3], by rw [hZ₆.keep _ (by simp [VG.Proof.MdStream.Arm.Finalize.keepRegs]), hC.r6],
      by rw [hZ₆.keep _ (by simp [VG.Proof.MdStream.Arm.Finalize.keepRegs]), hC.r4], by rw [hZ₆.keep _ (by simp [VG.Proof.MdStream.Arm.Finalize.keepRegs]), hC.r5],
      hZ₆.sp.trans hC.sp, by rw [hZ₆.mem]; exact hfr₆, by rw [hZ₆.mem]; exact hsv₆⟩
  have hst₆ : H.stateAt s₆.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀) = H.stateAt s.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀) := by
    rw [hZ₆.mem]
    apply H.stateAt_congr
    intro i hi
    rw [VG.Proof.MdStream.Arm.Finalize.buf_add]
    exact VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀) (VG.Proof.MdStream.Arm.Finalize.lim P k) =
      bytesAt s.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀) n ++ List.replicate (VG.Proof.MdStream.Arm.Finalize.lim P k - n) 0 := by
    rw [hZ₆.mem, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have h8₆ : s₆.gpr .r8 = BitVec.ofNat 32 k := by rw [hZ₆.keep _ (by simp [VG.Proof.MdStream.Arm.Finalize.keepRegs]), h.r8]
  -- In the last block, the length field.
  refine WP.seq (VG.Proof.MdStream.Arm.wp_cmp (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_)
  have hC₇ := hC₆.of_flags f₇
  have h8₇ : s₇.gpr .r8 = BitVec.ofNat 32 k := by rw [f₇.gpr, h8₆]
  have hz₇ : s₇.z = decide (k = 0) := by rw [z₇, h8₆, VG.Proof.MdStream.Arm.cmp0 (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => VG.Proof.MdStream.Arm.Finalize.Common P s₀ s₈ ∧ s₈.gpr .r8 = BitVec.ofNat 32 k ∧
      H.stateAt s₈.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀) = H.stateAt s.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀) ∧
      ∀ iv m, VG.Proof.MdStream.Arm.Finalize.R₀ H s₀ iv m → H.lenOk m.length → bytesAt s₈.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀) P.B = bytesAt s.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀) n ++
        (if k = 1 then List.replicate (P.B - n) 0 else List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)) ?_
    fun s₈ ⟨hC₈, h8₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show VG.Arm.eval .eq s₇ = _; rw [VG.Proof.MdStream.Arm.eval_eq, hz₇])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      have hout : InRegions s₇.wr (State.addr (s₇.gpr .r0) + BitVec.ofNat 64 (P.N + (P.B - P.L))) P.L :=
        ⟨VG.Proof.MdStream.Arm.Finalize.stR P s₀, by simp [hC₇.wr, hp.wr], by rw [hC₇.r0]; exact VG.Proof.MdStream.Arm.contains_offset (by omega_using [hd_L, hd_le]) (by omega)⟩
      refine WP.mono (hs.len s₇ (by rw [hC₇.r0]; omega) hout) fun s₈ ⟨g₈, rd₈, wr₈, sp₈, m₈⟩ => ?_
      have e : VG.Proof.MdStream.Arm.Finalize.stA s₀ + BitVec.ofNat 64 (P.N + (P.B - P.L)) = VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 (P.B - P.L) :=
        (VG.Proof.MdStream.Arm.Finalize.buf_add _ _).symm
      rw [hC₇.r0, hC₇.r5, hC₇.r4, e, f₇.mem] at m₈
      have hlen := H.lenOf_length (s₀.gpr .r3 ++ s₀.gpr .r2)
      obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hd hp (n := P.B - P.L) (xs := H.lenOf (s₀.gpr .r3 ++ s₀.gpr .r2))
        (by omega_using [hlen, hd_L, hd_le])
      refine ⟨⟨rd₈.trans hC₇.rd, wr₈.trans hC₇.wr, by rw [g₈ _ (by decide), hC₇.r0],
        by rw [g₈ _ (by decide), hC₇.r3], by rw [g₈ _ (by decide), hC₇.r6],
        by rw [g₈ _ (by decide), hC₇.r4], by rw [g₈ _ (by decide), hC₇.r5], sp₈.trans hC₇.sp,
        by rw [m₈]; exact hfr, by rw [m₈]; exact hsv⟩,
        by rw [g₈ _ (by decide), h8₇], ?_, fun iv m hm hok => ?_⟩
      · rw [m₈, ← hst₆]
        apply H.stateAt_congr
        intro i hi
        rw [VG.Proof.MdStream.Arm.Finalize.buf_add]
        exact VG.WriteBytes.writeBytes_before _ _ _ (by omega_using [hi]) (by omega)
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        rw [show s₀.gpr .r3 ++ s₀.gpr .r2 = VG.Proof.MdStream.Arm.count s₀ from rfl, hm.2, H.lenOf_eq _ hok] at m₈
        have e := bytesAt_writeBytes s₆.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀) (P.B - P.L) (H.lenBytes m.length)
          (by rw [H.lenBytes_length]; omega)
        rw [H.lenBytes_length, Nat.sub_add_cancel (by omega_using [hd_L, hd_le])] at e
        rw [VG.Proof.MdStream.Arm.Finalize.lim_zero] at hby₆
        rw [m₈, e, hby₆, List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₇, h8₇, by rw [f₇.mem, hst₆], fun iv m _ _ => ?_⟩
      rw [VG.Proof.MdStream.Arm.Finalize.lim_one] at hby₆
      rw [f₇.mem, hby₆]; simp
  -- Compress the block.
  refine WP.seq (VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_imm hd.enc) fun s₉ u₉ => WP.block_nil ?_)
  have hC₉ : VG.Proof.MdStream.Arm.Finalize.Common P s₀ s₉ := hC₈.of_upd u₉ (by decide)
  have hr1 : s₉.gpr .r1 = VG.Proof.MdStream.Arm.Finalize.st s₀ + BitVec.ofNat 32 P.N := by rw [u₉.gpr, hC₈.r0]
  refine WP.seq (VG.Proof.MdStream.Arm.Finalize.compress_buf hd hf hp hC₉ hr1 fun s₁₁ hC₁₁ cs₁₁ hst₁₁ => ?_)
  have h8₁₁ : s₁₁.gpr .r8 = BitVec.ofNat 32 k := by
    rw [cs₁₁ _ (by decide) (by decide), u₉.other _ (by decide), h8₈]
  have hblk : ∀ iv m, VG.Proof.MdStream.Arm.Finalize.R₀ H s₀ iv m → H.lenOk m.length → H.blockAt s₉.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀) = H.parse fun t =>
      (bytesAt s.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀) n ++
        (if k = 1 then List.replicate (P.B - n) 0 else List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)).getD t 0 := by
    intro iv m hm hok
    apply H.parse_congr
    intro t ht
    rw [u₉.mem]
    exact VG.Proof.MdStream.Arm.bytesAt_getD (hby₈ iv m hm hok) ht
  -- Next block, if any.
  refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₁₂ u₁₂ => VG.Proof.MdStream.Arm.wp_subs (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₁₃ u₁₃ z₁₃ =>
    WP.block_nil ?_
  have hC₁₃ : VG.Proof.MdStream.Arm.Finalize.Common P s₀ s₁₃ := (hC₁₁.of_upd u₁₂ (by decide)).of_upd u₁₃ (by decide)
  have h8₁₃ : s₁₃.gpr .r8 = BitVec.ofNat 32 k - 1 := by rw [u₁₃.gpr, u₁₂.other _ (by decide), h8₁₁]
  have hz : VG.Arm.eval .eq s₁₃ = some (decide (k = 1)) := by
    rw [VG.Proof.MdStream.Arm.eval_eq, z₁₃, u₁₂.other _ (by decide), h8₁₁, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      VG.Proof.MdStream.Arm.sub_beq (by omega) (by omega)]
  have hst : ∀ iv m, VG.Proof.MdStream.Arm.Finalize.R₀ H s₀ iv m → H.lenOk m.length →
      H.stateAt s₁₃.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀) = H.compress (H.stateAt s.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀)) (H.parse fun t =>
        (bytesAt s.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀) n ++
          (if k = 1 then List.replicate (P.B - n) 0 else List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)).getD t 0) := by
    intro iv m hm hok
    rw [u₁₃.mem, u₁₂.mem, hst₁₁, u₉.mem, hst₈, ← hblk iv m hm hok, u₉.mem]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by rw [hz]; simp, rfl, ⟨hC₁₃, by omega, by omega, ?_, ?_, fun iv m hm hok => ?_⟩⟩
    · rw [u₁₃.other _ (by decide), u₁₂.gpr]; rfl
    · rw [h8₁₃]; rfl
    · rw [h.hash iv m hm hok]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, VG.Proof.MdStream.Arm.Finalize.Fin1, VG.Proof.MdStream.Arm.Finalize.Fin0, hst iv m hm hok]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by rw [hz]; simp, hC₁₃, fun iv m hm hok => ?_⟩
    rw [h.hash iv m hm hok, hst iv m hm hok]
    simp only [show ¬ (0 = 1) by decide, ite_false, VG.Proof.MdStream.Arm.Finalize.Fin0, List.append_assoc]

end

/-! ## Prologue -/

/-- The prologue after saving. -/
def prologue (P : Params) : List Instr :=
  [.mov .r4 (.reg .r2), .mov .r5 (.reg .r3), .mov .r3 (.reg .r12), .ldrSp .r6 0,
    .dp .and .r7 .r4 (.imm (BitVec.ofNat 32 (P.B - 1))),
    .mov .r12 (.imm 0x80), .dp .add .r1 .r0 (.reg .r7), .strb .r12 .r1 P.N, .dp .add .r7 .r7 (.imm 1),
    .dp .add .r8 .r7 (.imm (BitVec.ofNat 32 (P.L - 1))), .mov .r8 (.shifted .r8 .lsr (Nat.log2 P.B))]

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem finalize_eq (name : String) (code : Prog isa) : finalize P name code =
    .seq (.block (([.ldrSp .r12 4] : List Instr) ++ save P .r12 ++ VG.Proof.MdStream.Arm.Finalize.prologue P))
    (.seq (.loop (finalizeBody P name code) .eq) (.block (P.out ++ restore P))) := rfl

theorem argAddr_eq {s₀ : State} (hp : VG.Proof.MdStream.Arm.Finalize.Pre P s₀) {k : Nat} (hk : k < 2) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have hp_sp_fit := hp.sp_fit
  simp only [stackArgAddr]
  rw [VG.Proof.MdStream.Arm.addr_off (by omega)]
  simp

theorem arg_in {s₀ : State} (hp : VG.Proof.MdStream.Arm.Finalize.Pre P s₀) {k : Nat} (hk : k < 2) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨VG.Proof.MdStream.Arm.Finalize.argR s₀, by simp [hp.rd], by rw [VG.Proof.MdStream.Arm.Finalize.argAddr_eq hp hk]; exact VG.Proof.MdStream.Arm.contains_offset (by omega) (by omega)⟩

theorem arg_sub {s₀ : State} (hp : VG.Proof.MdStream.Arm.Finalize.Pre P s₀) {k : Nat} (hk : k < 2) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (VG.Proof.MdStream.Arm.Finalize.argR s₀) := by
  rw [VG.Proof.MdStream.Arm.Finalize.argAddr_eq hp hk]; exact VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega)

theorem prologue_ok (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Finalize.Pre P s₀) :
    WP isa (.block (([.ldrSp .r12 4] : List Instr) ++ save P .r12 ++ VG.Proof.MdStream.Arm.Finalize.prologue P)) s₀
      fun s => ∃ k, VG.Proof.MdStream.Arm.Finalize.LInv H s₀ k (VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B + 1) s := by
  have hr : VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B < P.B := Nat.mod_lt _ hd.pos
  have hsc := hp.scr_fit; have hst := hp.st_fit; have hd_so := hd.so; have hd_N := hd.N; have hd_le := hd.le; have hd_L := hd.L
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.MdStream.Arm.wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (VG.Proof.MdStream.Arm.Finalize.arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = VG.Proof.MdStream.Arm.Finalize.scr s₀ := u₁.gpr
  refine VG.Proof.MdStream.Arm.save_ok hd (by rw [h12]; omega) (fun d hd₁ hd₂ => ⟨VG.Proof.MdStream.Arm.Finalize.scR P s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact VG.Proof.MdStream.Arm.contains_offset (by omega_using [hd₂]) (by omega_using [hd₂, hsc])⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  have hframe : Frame [VG.Proof.MdStream.Arm.Finalize.scR P s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]
    exact VG.Arm.Spill.saveMem_frame _ _ _ (by omega) _ fun p hp' => by have := VG.Proof.MdStream.Arm.saved_bound hd p hp'; omega_using [this]
  unfold VG.Proof.MdStream.Arm.Finalize.prologue
  refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₃ u₃ => VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₄ u₄ => VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₅ u₅ => ?_
  refine VG.Proof.MdStream.Arm.wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact VG.Proof.MdStream.Arm.Finalize.arg_in hp (by decide))
    fun s₆ u₆ => VG.Proof.MdStream.Arm.wp_and (VG.Proof.MdStream.Arm.op2_imm hd.encB.2.1) fun s₇ u₇ => ?_
  have hm₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have g₇ : ∀ r, r ∉ [Reg.r3, .r4, .r5, .r6, .r7, .r12] → s₇.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₇.other r hr.2.2.2.2.1, u₆.other r hr.2.2.2.1, u₅.other r hr.1, u₄.other r hr.2.2.1,
      u₃.other r hr.2.1, g₂, u₁.other r hr.2.2.2.2.2]
  have hC₇ : VG.Proof.MdStream.Arm.Finalize.Common P s₀ s₇ := by
    refine ⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
      by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
      g₇ _ (by decide), ?_, ?_, ?_, ?_, by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp],
      by rw [hm₇]; exact hframe.mono (by simp), fun p hp' => ?_⟩
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        u₃.other _ (by decide), g₂, h12]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem]
      exact hframe.readW (Region.contains_self _ _)
        (by simpa using (hp.a_scr.sub_left (VG.Proof.MdStream.Arm.Finalize.arg_sub hp (by decide)))) (by decide)
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, g₂, u₁.other _ (by decide)]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
    · rw [hm₇, m₂, u₁.mem, h12, VG.Proof.MdStream.Arm.saveMem_saved hd _ _ _ p hp', u₁.other _ (Ne.symm ?_)]
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  have hr7 : s₇.gpr .r7 = BitVec.ofNat 32 (VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B) := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂,
      u₁.other _ (by decide), VG.Proof.MdStream.Arm.andB hd, VG.Proof.MdStream.Arm.Finalize.cnt_mod hd]
  -- The `0x80` byte.
  have hout : InRegions s₇.wr (VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B)) 1 := by
    refine ⟨VG.Proof.MdStream.Arm.Finalize.stR P s₀, by simp [hC₇.wr, hp.wr], ?_⟩
    rw [VG.Proof.MdStream.Arm.Finalize.buf_add]; exact VG.Proof.MdStream.Arm.contains_offset (by omega) (by omega)
  refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₈ u₈ => VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₉ u₉ =>
    VG.Proof.MdStream.Arm.wp_strb (a := VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B)) (by omega) ?_
      (by rw [u₉.wr, u₈.wr]; exact hout) fun s₁₀ g₁₀ => ?_
  · rw [u₉.gpr, u₈.other _ (by decide), u₈.other _ (by decide), hC₇.r0, hr7, VG.Proof.MdStream.Arm.Finalize.buf_addr hp hr]
  obtain ⟨-, hfr, hsv⟩ := hC₇.writeBuf hd hp (n := VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B) (xs := [0x80]) (by simp; omega)
  have hm₁₀ : s₁₀.mem = VG.WriteBytes.writeBytes s₇.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B)) [0x80] := by
    rw [g₁₀.mem, u₉.mem, u₈.mem, u₉.other _ (by decide), u₈.gpr, ← List.nil_append [(0x80 : Byte)],
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp), VG.WriteBytes.writeBytes_nil]
    simp
  refine VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₁₁ u₁₁ => VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_imm hd.encB.2.2.2) fun s₁₂ u₁₂ =>
    VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_shrB hd) fun s₁₃ u₁₃ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → r ≠ .r1 → s₁₃.gpr r = s₇.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₁₃.other r h2, u₁₂.other r h2, u₁₁.other r h1, g₁₀.gpr, u₉.other r h4, u₈.other r h3]
  have hm₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have hC₁₃ : VG.Proof.MdStream.Arm.Finalize.Common P s₀ s₁₃ :=
    ⟨by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, g₁₀.rd, u₉.rd, u₈.rd, hC₇.rd],
      by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, hC₇.wr],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r0],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r3],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r6],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r4],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r5],
      by rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, g₁₀.sp, u₉.sp, u₈.sp, hC₇.sp],
      by rw [hm₁₃, hm₁₀]; exact hfr, by rw [hm₁₃, hm₁₀]; exact hsv⟩
  have hr7' : s₁₃.gpr .r7 = BitVec.ofNat 32 (VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B + 1) := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), hr7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
  have hr8 : s₁₃.gpr .r8 = BitVec.ofNat 32 ((VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B + 1 + (P.L - 1)) / P.B) := by
    rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), hr7,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, ← BitVec.ofNat_add, VG.Proof.MdStream.Arm.shrB hd (by omega_using [hd_L, hd_le, hr])]
  -- The facts about the buffer.
  have hbytes : ∀ iv m, VG.Proof.MdStream.Arm.Finalize.R₀ H s₀ iv m → bytesAt s₁₃.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀) (VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B + 1) =
      Md.rest P.B m ++ [0x80] := by
    intro iv m hm
    have := Nat.mod_lt m.length hd.pos
    have e := bytesAt_writeBytes s₇.mem (VG.Proof.MdStream.Arm.Finalize.buf P s₀) (VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₃, hm₁₀, e, hm₇]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length hd]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := VG.Proof.MdStream.Arm.frame_bytes hframe (R := VG.Proof.MdStream.Arm.Finalize.stR P s₀) (by simpa using hp.st_scr)
      (by show P.N + P.B ≤ 2 ^ 64; omega_using [hst]) (i := P.N + i) (by show P.N + i < P.N + P.B; omega)
    rwa [← VG.Proof.MdStream.Arm.Finalize.buf_add] at this
  have hstate : H.stateAt s₁₃.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀) = H.stateAt s₀.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀) := by
    apply H.stateAt_congr
    intro i hi
    rw [hm₁₃, hm₁₀, VG.Proof.MdStream.Arm.Finalize.buf_add, VG.WriteBytes.writeBytes_before _ _ _ (by omega_using [hi]) (by simp; omega), hm₇]
    exact VG.Proof.MdStream.Arm.frame_bytes hframe (R := VG.Proof.MdStream.Arm.Finalize.stR P s₀) (by simpa using hp.st_scr)
      (by show P.N + P.B ≤ 2 ^ 64; omega_using [hst]) (by show i < P.N + P.B; omega_using [hi])
  by_cases hb : P.B ≤ VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B + P.L
  · have hk : (VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B + 1 + (P.L - 1)) / P.B = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    refine ⟨1, hC₁₃, (Nat.le_refl _), by rw [VG.Proof.MdStream.Arm.Finalize.lim_one]; omega, hr7', by rw [hr8, hk], fun iv m hm _ => ?_⟩
    simp only [↓reduceIte]
    rw [Md.hash_two H hd.pos (by omega_using [hd_L, hd_le]) (by rw [← hm.length hd]; omega), VG.Proof.MdStream.Arm.Finalize.Fin1, hbytes iv m hm, hstate,
      hm.1.1, ← hm.length hd, show P.B - (VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B + 1) = P.B - 1 - VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B by omega]
  · have hk : (VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B + 1 + (P.L - 1)) / P.B = 0 := Nat.div_eq_of_lt (by omega_using [hb, hd_L])
    refine ⟨0, hC₁₃, by omega, by rw [VG.Proof.MdStream.Arm.Finalize.lim_zero]; omega, hr7', by rw [hr8, hk], fun iv m hm _ => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [Md.hash_one H hd.pos (by rw [← hm.length hd]; omega), VG.Proof.MdStream.Arm.Finalize.Fin0, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length hd, show P.B - P.L - (VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B + 1) = P.B - P.L - 1 - VG.Proof.MdStream.Arm.Finalize.cnt s₀ % P.B by omega]

/-! ## Output and epilogue -/

/-- The epilogue's postcondition. -/
def Post (P : Params) (H : Md P.B P.N P.L) (s₀ s' : State) : Prop := abiPreserved s₀ s' ∧ (VG.Proof.MdStream.Arm.finK H).post s₀ s'

theorem epilogue_ok (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Finalize.Pre P s₀) {sD : State} (hD : VG.Proof.MdStream.Arm.Finalize.Done H s₀ sD) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hkeep : ∀ r, r ≠ .r9 → r ≠ .r10 → s.gpr r = sD.gpr r)
    (hsp : s.sp = sD.sp) (hm : s.mem = VG.WriteBytes.writeBytes sD.mem (VG.Proof.MdStream.Arm.Finalize.outA s₀) (H.digest (H.stateAt sD.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀)))) :
    WP isa (.block (restore P)) s (VG.Proof.MdStream.Arm.Finalize.Post P H s₀) := by
  have hd_N := hd.N; have hd_so := hd.so
  have hC := hD.1
  have hdl := H.digest_length (H.stateAt sD.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀))
  have hfo : Frame [VG.Proof.MdStream.Arm.Finalize.outR P s₀] sD.mem (VG.WriteBytes.writeBytes sD.mem (VG.Proof.MdStream.Arm.Finalize.outA s₀) (H.digest (H.stateAt sD.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀)))) :=
    VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [show VG.Proof.MdStream.Arm.Finalize.outA s₀ = VG.Proof.MdStream.Arm.Finalize.outA s₀ + BitVec.ofNat 64 0 by simp]
      exact VG.Proof.MdStream.Arm.contains_offset (by omega) (by omega))
  refine VG.Proof.MdStream.Arm.restore_ok hd (scr := VG.Proof.MdStream.Arm.Finalize.scr s₀) (by rw [hkeep _ (by decide) (by decide), hC.r3]) hp.scr_fit
    (fun d hd₁ hd₂ => ⟨VG.Proof.MdStream.Arm.Finalize.scR P s₀, by simp [hrd, hwr, hp.wr], VG.Proof.MdStream.Arm.contains_offset (by omega_using [hd₂]) (by omega)⟩) s₀.gpr
    (fun p hp' => ?_) fun s' hs _ hmem _ _ hsp' => ⟨⟨VG.Proof.MdStream.Arm.preserved_of hs, by rw [hsp', hsp, hC.sp]⟩, ?_⟩
  · rw [hm, ← hC.saved p hp']
    refine hfo.readW (r := ⟨VG.Proof.MdStream.Arm.Finalize.scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.out_scr.symm.sub_left (VG.Proof.MdStream.Arm.Finalize.saved_sub hd hp')
  · intro iv m hr hok hc
    have e := bytesAt_writeBytes sD.mem (VG.Proof.MdStream.Arm.Finalize.outA s₀) 0 (H.digest (H.stateAt sD.mem (VG.Proof.MdStream.Arm.Finalize.stA s₀))) (by omega)
    rw [hdl, show VG.Proof.MdStream.Arm.Finalize.outA s₀ + BitVec.ofNat 64 0 = VG.Proof.MdStream.Arm.Finalize.outA s₀ by simp, Nat.zero_add,
      show bytesAt sD.mem (VG.Proof.MdStream.Arm.Finalize.outA s₀) 0 = [] from rfl, List.nil_append] at e
    rw [hmem, hm, e]
    exact (hD.2 iv m ⟨hr, hc⟩ hok).symm

theorem correct (hd : VG.Proof.MdStream.Arm.Dims P) (hs : VG.Proof.MdStream.Arm.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.Arm.CalleeOk H code)
    {s₀ : State} (hp : VG.Proof.MdStream.Arm.Finalize.Pre P s₀) : WP isa (finalize P name code) s₀ (VG.Proof.MdStream.Arm.Finalize.Post P H s₀) := by
  have hd_N := hd.N
  rw [VG.Proof.MdStream.Arm.Finalize.finalize_eq]
  refine WP.seq (WP.mono (VG.Proof.MdStream.Arm.Finalize.prologue_ok (H := H) hd hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.MdStream.Arm.Finalize.Done H s₀) ?_ fun sD hD => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n, VG.Proof.MdStream.Arm.Finalize.LInv H s₀ i n s) ?_ k s₁ ⟨_, hL⟩
    rintro i s ⟨n, hL⟩
    refine WP.mono (VG.Proof.MdStream.Arm.Finalize.body_ok hd hs hf hp hL) fun s' h => ?_
    rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by omega, 0, hL'⟩
  · have hC := hD.1
    have hst := hp.st_fit; have ho := hp.out_fit
    rw [WP.block_append_iff]
    refine WP.mono (hs.out sD (by rw [hC.r0]; omega) (by rw [hC.r6]; omega) ?_ ?_ ?_)
      fun s ⟨g, rd, wr, sp, m⟩ =>
        VG.Proof.MdStream.Arm.Finalize.epilogue_ok hd hp hD (rd.trans hC.rd) (wr.trans hC.wr) g sp (by rw [m, hC.r6, hC.r0])
    · refine ⟨VG.Proof.MdStream.Arm.Finalize.stR P s₀, by simp [hC.rd, hC.wr, hp.wr, hp.rd], ?_⟩
      rw [hC.r0]; simpa using VG.Proof.MdStream.Arm.contains_offset (base := VG.Proof.MdStream.Arm.Finalize.stA s₀) (off := 0) (n := P.N) (len := P.N + P.B)
        (by omega) (by omega)
    · refine ⟨VG.Proof.MdStream.Arm.Finalize.outR P s₀, by simp [hC.wr, hp.wr], ?_⟩
      rw [hC.r6]; simpa using VG.Proof.MdStream.Arm.contains_offset (base := VG.Proof.MdStream.Arm.Finalize.outA s₀) (off := 0) (n := P.N) (len := P.N)
        (by omega) (by omega)
    · rw [hC.r0, hC.r6]
      exact hp.st_out.sub_left (Region.sub_prefix (by omega))

end

/-! ## Constant time -/

/-- The initial taint: `r0` (`state`) and `r2:r3` (`count`) are public, `r0`
points at the state, and the 8 bytes of stack arguments are public, the
second one pointing at the scratch space. -/
def τ₀ (P : Params) : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r2, .r3], flags := false, lens := [P.N + P.B, P.N, P.so + 48], bases := [(.r0, 0)],
    argLen := 8, argBases := [(4, 2)] }

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem wf₀ {s : State} (h : (VG.Proof.MdStream.Arm.finK H).pre s) : VG.Arm.Taint.Wf (VG.Proof.MdStream.Arm.Finalize.τ₀ P) s := by
  have hp := VG.Proof.MdStream.Arm.Finalize.pre_of h
  have hst := hp.st_fit; have ho := hp.out_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.MdStream.Arm.Finalize.τ₀], ?_, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_out, hp.st_scr⟩, hp.out_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [VG.Proof.MdStream.Arm.addr_toNat] <;> omega
  · intro p hp'; simp only [VG.Proof.MdStream.Arm.Finalize.τ₀, List.mem_singleton] at hp'; subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 8⟩ : Region) = VG.Proof.MdStream.Arm.Finalize.argR s := by simp [stackArgAddr]
    simp only [VG.Proof.MdStream.Arm.Finalize.τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.a_st
    · exact hp.a_out
    · exact hp.a_scr
  · intro p hp'; simp only [VG.Proof.MdStream.Arm.Finalize.τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨Nat.le_refl 8, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : (VG.Proof.MdStream.Arm.finK H).pre s₁) (h₂ : (VG.Proof.MdStream.Arm.finK H).pre s₂)
    (hpub : (VG.Proof.MdStream.Arm.finK H).pub s₁ s₂) : VG.Arm.Taint.Agree (VG.Proof.MdStream.Arm.Finalize.τ₀ P) s₁ s₂ := by
  obtain ⟨psp, p0, p2, p3, a0, a1⟩ := hpub
  have hp₁ := VG.Proof.MdStream.Arm.Finalize.pre_of h₁; have hp₂ := VG.Proof.MdStream.Arm.Finalize.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.MdStream.Arm.Finalize.wf₀ h₁, VG.Proof.MdStream.Arm.Finalize.wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [VG.Proof.MdStream.Arm.Finalize.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.MdStream.Arm.Finalize.stR, VG.Proof.MdStream.Arm.Finalize.outR, VG.Proof.MdStream.Arm.Finalize.scR, VG.Proof.MdStream.Arm.Finalize.stA, VG.Proof.MdStream.Arm.Finalize.outA, VG.Proof.MdStream.Arm.Finalize.scA, VG.Proof.MdStream.Arm.Finalize.st, VG.Proof.MdStream.Arm.Finalize.out, VG.Proof.MdStream.Arm.Finalize.scr, p0, a0, a1]
  · simp only [VG.Proof.MdStream.Arm.Finalize.τ₀] at hk
    rw [VG.Proof.MdStream.Arm.argByte_eq hp₁.sp_fit hk, VG.Proof.MdStream.Arm.argByte_eq hp₂.sp_fit hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

end

/-- The stack arguments of `sat`: `out` at `0x2000` and the scratch space at
`0x3000`, passed on the stack at `0x5000`. -/
def satBase : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x20 else if a = 0x5005 then 0x30 else 0
  rd := [⟨0x5000, 8⟩]
  wr := []

/-- A state satisfying the precondition. -/
def sat (P : Params) : State :=
  { VG.Proof.MdStream.Arm.Finalize.satBase with
                 wr := [⟨0x1000, P.N + P.B⟩, ⟨0x2000, P.N⟩, ⟨0x3000, P.so + 48⟩] }

/-- `finalize` is verified, given that it is constant time (which the taint
analysis proves of each hash function's code). -/
theorem verified {P : Params} {H : Md P.B P.N P.L} (hd : VG.Proof.MdStream.Arm.Dims P) (hs : VG.Proof.MdStream.Arm.Shape H) {name : String}
    {code : Prog isa} (hf : VG.Proof.MdStream.Arm.CalleeOk H code)
    (hct : ConstantTime isa (VG.Proof.MdStream.Arm.finK H).pre (VG.Proof.MdStream.Arm.finK H).pub (finalize P name code)) :
    Verified Arm.target (finalize P name code) (VG.Proof.MdStream.Arm.finK H) := by
  have hBle := hd.le
  have hd_N := hd.N; have hd_so := hd.so
  refine ⟨fun s hs' => ?_, hct, ?_⟩
  · obtain ⟨t, s', he, h⟩ := VG.Proof.MdStream.Arm.Finalize.correct hd hs hf (VG.Proof.MdStream.Arm.Finalize.pre_of hs')
    exact ⟨t, s', he, h⟩
  · have e0 : stackArg (VG.Proof.MdStream.Arm.Finalize.sat P) 0 = 0x2000 := by show stackArg VG.Proof.MdStream.Arm.Finalize.satBase 0 = _; decide
    have e1 : stackArg (VG.Proof.MdStream.Arm.Finalize.sat P) 1 = 0x3000 := by show stackArg VG.Proof.MdStream.Arm.Finalize.satBase 1 = _; decide
    refine ⟨VG.Proof.MdStream.Arm.Finalize.sat P, ?_⟩
    simp only [VG.Proof.MdStream.Arm.finK, e0, e1]
    refine ⟨by simp [VG.Proof.MdStream.Arm.Finalize.sat, VG.Proof.MdStream.Arm.Finalize.satBase, stackArgAddr, State.addr], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [VG.Proof.MdStream.Arm.Finalize.sat, VG.Proof.MdStream.Arm.Finalize.satBase, stackArgAddr, State.addr]
    iterate 3 exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    iterate 3 exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    all_goals simp <;> omega

end VG.Proof.MdStream.Arm.Finalize

end

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.Arm.Update`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on ARMv7: `update`

The functional correctness of `update`, for any hash function (`Md`) and any
correct compression function (`CalleeOk`). The same structure as the AArch64
proof (`VG.Proof.MdStream.AArch64.Update`), with `state` in `r0`, `scratch` in
`r3`, `data` in `r5`, the bytes left in `r6`, the buffered bytes in `r4`, and
whether a block is pending in `r7`. Constant time is proven for each hash
function's code by the taint analysis, calls included, from the initial taint
`τ₀`.
-/

namespace VG.Proof.MdStream.Arm.Update

open VG VG.Arm VG.Impl.MdStream.Arm
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev cnt : Nat := (VG.Proof.MdStream.Arm.count s₀).toNat
abbrev dp : BitVec 32 := stackArg s₀ 0
abbrev len : Nat := (stackArg s₀ 1).toNat
abbrev scr : BitVec 32 := stackArg s₀ 2
abbrev stA : Addr := State.addr (VG.Proof.MdStream.Arm.Update.st s₀)
abbrev dA : Addr := State.addr (VG.Proof.MdStream.Arm.Update.dp s₀)
abbrev scA : Addr := State.addr (VG.Proof.MdStream.Arm.Update.scr s₀)
abbrev stR : Region := ⟨VG.Proof.MdStream.Arm.Update.stA s₀, P.N + P.B⟩
abbrev dR : Region := ⟨VG.Proof.MdStream.Arm.Update.dA s₀, VG.Proof.MdStream.Arm.Update.len s₀⟩
abbrev scR : Region := ⟨VG.Proof.MdStream.Arm.Update.scA s₀, P.so + 48⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 12⟩
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (VG.Proof.MdStream.Arm.Update.dA s₀) (VG.Proof.MdStream.Arm.Update.len s₀)
/-- The buffer. -/
abbrev buf : Addr := VG.Proof.MdStream.Arm.Update.stA s₀ + BitVec.ofNat 64 P.N

/-- The caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved P, m.readW (VG.Proof.MdStream.Arm.Update.scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

end

/-- The messages the initial state represents, from `iv`. -/
def R₀ {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (VG.Proof.MdStream.Arm.Update.stA s₀) m ∧ VG.Proof.MdStream.Arm.count s₀ = BitVec.ofNat 64 m.length

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.MdStream.Arm.Update.dR s₀, VG.Proof.MdStream.Arm.Update.argR s₀]
  wr : s₀.wr = [VG.Proof.MdStream.Arm.Update.stR P s₀, VG.Proof.MdStream.Arm.Update.scR P s₀]
  st_scr : (VG.Proof.MdStream.Arm.Update.stR P s₀).Disjoint (VG.Proof.MdStream.Arm.Update.scR P s₀)
  d_st : (VG.Proof.MdStream.Arm.Update.dR s₀).Disjoint (VG.Proof.MdStream.Arm.Update.stR P s₀)
  d_scr : (VG.Proof.MdStream.Arm.Update.dR s₀).Disjoint (VG.Proof.MdStream.Arm.Update.scR P s₀)
  a_st : (VG.Proof.MdStream.Arm.Update.argR s₀).Disjoint (VG.Proof.MdStream.Arm.Update.stR P s₀)
  a_scr : (VG.Proof.MdStream.Arm.Update.argR s₀).Disjoint (VG.Proof.MdStream.Arm.Update.scR P s₀)
  st_fit : (VG.Proof.MdStream.Arm.Update.st s₀).toNat + (P.N + P.B) ≤ 2 ^ 32
  d_fit : (VG.Proof.MdStream.Arm.Update.dp s₀).toNat + VG.Proof.MdStream.Arm.Update.len s₀ ≤ 2 ^ 32
  scr_fit : (VG.Proof.MdStream.Arm.Update.scr s₀).toNat + (P.so + 48) ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 12 ≤ 2 ^ 32

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem pre_of {s₀ : State} (h : (VG.Proof.MdStream.Arm.updK H).pre s₀) : VG.Proof.MdStream.Arm.Update.Pre P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem cnt_mod (hd : VG.Proof.MdStream.Arm.Dims P) (s₀ : State) : VG.Proof.MdStream.Arm.Update.cnt s₀ % P.B = (s₀.gpr .r2).toNat % P.B := by
  simp only [VG.Proof.MdStream.Arm.Update.cnt, VG.Proof.MdStream.Arm.count]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (s₀.gpr .r2).isLt, Nat.shiftLeft_eq]
  exact hd.mod _ _

theorem R₀.length (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} {iv : H.HV} {m : List Byte} (h : VG.Proof.MdStream.Arm.Update.R₀ H s₀ iv m) :
    VG.Proof.MdStream.Arm.Update.cnt s₀ % P.B = m.length % P.B := by
  rw [VG.Proof.MdStream.Arm.Update.cnt, h.2, BitVec.toNat_ofNat]
  exact hd.mod64 _

theorem len_lt (s₀ : State) : VG.Proof.MdStream.Arm.Update.len s₀ < 2 ^ 32 := (stackArg s₀ 1).isLt

theorem D_length (s₀ : State) : (VG.Proof.MdStream.Arm.Update.D s₀).length = VG.Proof.MdStream.Arm.Update.len s₀ := by simp [bytesAt]

end

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (P : Params) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ VG.Proof.MdStream.Arm.Update.len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r0 : s.gpr .r0 = VG.Proof.MdStream.Arm.Update.st s₀
  r3 : s.gpr .r3 = VG.Proof.MdStream.Arm.Update.scr s₀
  sp : s.sp = s₀.sp
  r5 : s.gpr .r5 = VG.Proof.MdStream.Arm.Update.dp s₀ + BitVec.ofNat 32 c
  r6 : s.gpr .r6 = BitVec.ofNat 32 (VG.Proof.MdStream.Arm.Update.len s₀ - c)
  frame : Frame [VG.Proof.MdStream.Arm.Update.stR P s₀, VG.Proof.MdStream.Arm.Update.scR P s₀] s₀.mem s.mem
  saved : VG.Proof.MdStream.Arm.Update.Saved P s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c : Nat) (s : State) : Prop
    extends VG.Proof.MdStream.Arm.Update.Common P s₀ c s where
  r4 : s.gpr .r4 = BitVec.ofNat 32 ((VG.Proof.MdStream.Arm.Update.cnt s₀ + c) % P.B)
  repr : ∀ iv m, VG.Proof.MdStream.Arm.Update.R₀ H s₀ iv m → H.Repr iv s.mem (VG.Proof.MdStream.Arm.Update.stA s₀) (m ++ (VG.Proof.MdStream.Arm.Update.D s₀).take c)

/-- `k ≥ 1` whole blocks are ready at `r1` (the buffer, or the data), and
compressing them absorbs the first `c` bytes of data. -/
structure Pending {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c k : Nat) (s : State) : Prop
    extends VG.Proof.MdStream.Arm.Update.Common P s₀ c s where
  r4 : s.gpr .r4 = 0
  r7 : s.gpr .r7 = BitVec.ofNat 32 k
  k_pos : 0 < k
  mod : (VG.Proof.MdStream.Arm.Update.cnt s₀ + c) % P.B = 0
  src : (s.gpr .r1 = VG.Proof.MdStream.Arm.Update.st s₀ + BitVec.ofNat 32 P.N ∧ k = 1) ∨
    ∃ c₀, s.gpr .r1 = VG.Proof.MdStream.Arm.Update.dp s₀ + BitVec.ofNat 32 c₀ ∧ c₀ + P.B * k ≤ VG.Proof.MdStream.Arm.Update.len s₀
  repr : ∀ iv m, VG.Proof.MdStream.Arm.Update.R₀ H s₀ iv m → ∀ mem', H.stateAt mem' (VG.Proof.MdStream.Arm.Update.stA s₀) =
      H.compressBlocks (H.stateAt s.mem (VG.Proof.MdStream.Arm.Update.stA s₀)) s.mem (State.addr (s.gpr .r1)) k →
    H.Repr iv mem' (VG.Proof.MdStream.Arm.Update.stA s₀) (m ++ (VG.Proof.MdStream.Arm.Update.D s₀).take c)

/-- All the data is absorbed, and nothing is pending. -/
def Done {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  VG.Proof.MdStream.Arm.Update.Inv H s₀ (VG.Proof.MdStream.Arm.Update.len s₀) s ∧ s.gpr .r7 = 0

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.MdStream.Arm.Update.Common P s₀ c s)
    (hg : ∀ r ∈ [Reg.r0, .r3, .r5, .r6, .lr], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    VG.Proof.MdStream.Arm.Update.Common P s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r0 := by rw [hg _ (by simp)]; exact h.r0
  r3 := by rw [hg _ (by simp)]; exact h.r3
  sp := hsp.trans h.sp
  r5 := by rw [hg _ (by simp)]; exact h.r5
  r6 := by rw [hg _ (by simp)]; exact h.r6
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.MdStream.Arm.Update.Inv H s₀ c s)
    (hg : ∀ r ∈ [Reg.r0, .r3, .r5, .r6, .lr, .r4], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    VG.Proof.MdStream.Arm.Update.Inv H s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_append_left [_] hr)) hm hrd hwr hsp with
    r4 := by rw [hg _ (by simp)]; exact h.r4
    repr := by rw [hm]; exact h.repr }

theorem Inv.of_upd {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.MdStream.Arm.Update.Inv H s₀ c s) {d : Reg} {v : BitVec 32}
    (u : VG.Proof.MdStream.Arm.Upd s s' d v) (hd : d ∉ [Reg.r0, .r3, .r5, .r6, .lr, .r4]) : VG.Proof.MdStream.Arm.Update.Inv H s₀ c s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem Inv.of_flags {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.MdStream.Arm.Update.Inv H s₀ c s) (u : VG.Proof.MdStream.Arm.Fupd s s') :
    VG.Proof.MdStream.Arm.Update.Inv H s₀ c s' :=
  h.of_gpr (fun r _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp

/-- Where the caller's registers are saved. -/
theorem saved_sub (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved P) :
    Region.Sub ⟨VG.Proof.MdStream.Arm.Update.scA s₀ + BitVec.ofNat 64 p.2, 4⟩ (VG.Proof.MdStream.Arm.Update.scR P s₀) := by
  have := VG.Proof.MdStream.Arm.saved_bound hd p hp; have hd_so := hd.so
  exact VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega)

/-- The saved registers survive a write to the state. -/
theorem Saved.of_frame (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {m m' : Mem}
    (hs : VG.Proof.MdStream.Arm.Update.Saved P s₀ m) (hf : Frame [VG.Proof.MdStream.Arm.Update.stR P s₀] m m') : VG.Proof.MdStream.Arm.Update.Saved P s₀ m' := by
  intro p hp'
  rw [← hs p hp']
  refine hf.readW (r := ⟨VG.Proof.MdStream.Arm.Update.scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (VG.Proof.MdStream.Arm.Update.saved_sub hd hp')

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < VG.Proof.MdStream.Arm.Update.len s₀) :
    (VG.Proof.MdStream.Arm.Update.D s₀).getD i 0 = s₀.mem (VG.Proof.MdStream.Arm.Update.dA s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {c : Nat} {s : State} (h : VG.Proof.MdStream.Arm.Update.Common P s₀ c s) {i : Nat}
    (hi : i < VG.Proof.MdStream.Arm.Update.len s₀) : s.mem (VG.Proof.MdStream.Arm.Update.dA s₀ + BitVec.ofNat 64 i) = (VG.Proof.MdStream.Arm.Update.D s₀).getD i 0 := by
  rw [VG.Proof.MdStream.Arm.Update.D_getD s₀ hi]
  exact VG.Proof.MdStream.Arm.frame_bytes h.frame (R := VG.Proof.MdStream.Arm.Update.dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩)
    (by have := VG.Proof.MdStream.Arm.Update.len_lt s₀; show VG.Proof.MdStream.Arm.Update.len s₀ ≤ 2 ^ 64; omega) hi

theorem length_mid (hd : VG.Proof.MdStream.Arm.Dims P) (s₀ : State) {iv : H.HV} {m : List Byte} (hm : VG.Proof.MdStream.Arm.Update.R₀ H s₀ iv m) {c : Nat}
    (hc : c ≤ VG.Proof.MdStream.Arm.Update.len s₀) : (m ++ (VG.Proof.MdStream.Arm.Update.D s₀).take c).length % P.B = (VG.Proof.MdStream.Arm.Update.cnt s₀ + c) % P.B := by
  simp only [List.length_append, List.length_take, VG.Proof.MdStream.Arm.Update.D_length, Nat.min_eq_left hc]
  rw [Nat.add_mod, ← hm.length hd, ← Nat.add_mod]

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (VG.Proof.MdStream.Arm.Update.D s₀).take c ++ ((VG.Proof.MdStream.Arm.Update.D s₀).drop c).take t = m ++ (VG.Proof.MdStream.Arm.Update.D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-! ## Compressing pending blocks -/

theorem Pending.k_lt (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} {c k : Nat} {s : State} (h : VG.Proof.MdStream.Arm.Update.Pending H s₀ c k s) :
    k < 2 ^ 32 := by
  have := VG.Proof.MdStream.Arm.Update.len_lt s₀
  have : k ≤ P.B * k := Nat.le_mul_of_pos_left k hd.pos
  rcases h.src with ⟨_, rfl⟩ | ⟨c₀, _, hc₀⟩ <;> omega

theorem Pending.compress_ok (hd : VG.Proof.MdStream.Arm.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.Arm.CalleeOk H code)
    {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {c k : Nat} {s : State} (h : VG.Proof.MdStream.Arm.Update.Pending H s₀ c k s) :
    WP isa (compressN name code) s (VG.Proof.MdStream.Arm.Update.Inv H s₀ c) := by
  have hBle := hd.le
  have hst := hp.st_fit; have hdf := hp.d_fit; have hsc := hp.scr_fit
  have hk0 := h.k_pos
  have hBk : k ≤ P.B * k := Nat.le_mul_of_pos_left k hd.pos
  have hd_N := hd.N; have hd_so := hd.so; have hd_le := hd.le
  have eN : Region.Sub ⟨VG.Proof.MdStream.Arm.Update.stA s₀, P.N⟩ (VG.Proof.MdStream.Arm.Update.stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.MdStream.Arm.Update.scA s₀, P.so⟩ (VG.Proof.MdStream.Arm.Update.scR P s₀) := Region.sub_prefix (by omega)
  -- The block's address.
  obtain ⟨hfit, hsub, hdisj⟩ : (s.gpr .r1).toNat + P.B * k ≤ 2 ^ 32 ∧
      (∃ R ∈ [VG.Proof.MdStream.Arm.Update.stR P s₀, VG.Proof.MdStream.Arm.Update.dR s₀], ∃ off, State.addr (s.gpr .r1) = R.base + BitVec.ofNat 64 off ∧
        off + P.B * k ≤ R.len) ∧
      Region.Disjoint ⟨State.addr (s.gpr .r1), P.B * k⟩ ⟨VG.Proof.MdStream.Arm.Update.stA s₀, P.N⟩ ∧
      Region.Disjoint ⟨State.addr (s.gpr .r1), P.B * k⟩ ⟨VG.Proof.MdStream.Arm.Update.scA s₀, P.so⟩ := by
    rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · have ha : State.addr (s.gpr .r1) = VG.Proof.MdStream.Arm.Update.stA s₀ + BitVec.ofNat 64 P.N := by rw [h', VG.Proof.MdStream.Arm.addr_off (by omega)]
      have hs : Region.Sub ⟨State.addr (s.gpr .r1), P.B * 1⟩ (VG.Proof.MdStream.Arm.Update.stR P s₀) :=
        ha ▸ VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega)
      refine ⟨by rw [h', BitVec.toNat_add, BitVec.toNat_ofNat]; omega,
        ⟨VG.Proof.MdStream.Arm.Update.stR P s₀, by simp, P.N, ha, by simp⟩, ?_, (hp.st_scr.sub_left hs).sub_right eso⟩
      rw [ha]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · have ha : State.addr (s.gpr .r1) = VG.Proof.MdStream.Arm.Update.dA s₀ + BitVec.ofNat 64 c₀ := by rw [h', VG.Proof.MdStream.Arm.addr_off (by omega)]
      have hs : Region.Sub ⟨State.addr (s.gpr .r1), P.B * k⟩ (VG.Proof.MdStream.Arm.Update.dR s₀) := ha ▸ VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega_using [hc₀, hdf])
      refine ⟨by rw [h', BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hc₀, hdf], ⟨VG.Proof.MdStream.Arm.Update.dR s₀, by simp, c₀, ha, hc₀⟩,
        (hp.d_st.sub_left hs).sub_right eN, (hp.d_scr.sub_left hs).sub_right eso⟩
  have hk : (s.gpr .r7).toNat = k := by rw [h.r7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h.k_lt hd)]
  refine VG.Proof.MdStream.Arm.compressWith_ok (VG.Proof.MdStream.Arm.setsN_r7 s) hk hf h.r0 h.r3 rfl (by omega) hfit (by omega_using [hsc])
    ((hp.st_scr.sub_left eN).sub_right eso)
    hdisj.1 hdisj.2 ?_ ?_ fun s' hrd hwr hcs h0 h3 hsp hf' hstate => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · obtain ⟨R, hR, off, ha, hl⟩ := hsub
      refine ⟨R, ?_, off, ha, hl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl <;> simp
    · exact ⟨VG.Proof.MdStream.Arm.Update.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.Arm.Update.scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.MdStream.Arm.Update.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.Arm.Update.scR P s₀, by simp, 0, by simp, by simp⟩
  · refine ⟨⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, h0, h3,
      hsp.trans h.sp, by rw [hcs _ (by decide) (by decide)]; exact h.r5,
      by rw [hcs _ (by decide) (by decide)]; exact h.r6,
      h.frame.trans (hf'.sub ?_), fun p hp' => ?_⟩, ?_, fun iv m hm => h.repr iv m hm _ hstate⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.MdStream.Arm.Update.stR P s₀, by simp, eN⟩
      · exact ⟨VG.Proof.MdStream.Arm.Update.scR P s₀, by simp, eso⟩
    · rw [← h.saved p hp']
      have := VG.Proof.MdStream.Arm.saved_bound hd p hp'
      refine hf'.readW (r := ⟨VG.Proof.MdStream.Arm.Update.scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (VG.Proof.MdStream.Arm.Update.saved_sub hd hp')).sub_right eN
      · exact Offset.disjoint_base _ this.1 (by omega_using [this.2, hd.so.2])
    · rw [hcs _ (by decide) (by decide), h.r4, h.mod]; rfl

/-! ## Whole blocks straight from the data -/

theorem direct_ok (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.Arm.Update.Inv H s₀ c s)
    (hr : (VG.Proof.MdStream.Arm.Update.cnt s₀ + c) % P.B = 0) (hl : P.B ≤ VG.Proof.MdStream.Arm.Update.len s₀ - c) :
    WP isa (.block (direct P)) s (VG.Proof.MdStream.Arm.Update.Pending H s₀ (c + P.B * ((VG.Proof.MdStream.Arm.Update.len s₀ - c) / P.B)) ((VG.Proof.MdStream.Arm.Update.len s₀ - c) / P.B)) := by
  have hBle := hd.le
  have hdf := hp.d_fit
  have hlen := VG.Proof.MdStream.Arm.Update.len_lt s₀
  have hq1 : 1 ≤ (VG.Proof.MdStream.Arm.Update.len s₀ - c) / P.B := Nat.div_pos hl hd.pos
  have hq2 : P.B * ((VG.Proof.MdStream.Arm.Update.len s₀ - c) / P.B) ≤ VG.Proof.MdStream.Arm.Update.len s₀ - c := Nat.mul_div_le _ _
  generalize hq : (VG.Proof.MdStream.Arm.Update.len s₀ - c) / P.B = q at hq1 hq2 ⊢
  unfold direct
  refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₁ u₁ => VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_shrB hd) fun s₂ u₂ =>
    VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_shlB hd) fun s₃ u₃ => VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₄ u₄ =>
    VG.Proof.MdStream.Arm.wp_sub (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r7 → r ≠ .r12 → r ≠ .r5 → r ≠ .r6 → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h1 : s₅.gpr .r1 = VG.Proof.MdStream.Arm.Update.dp s₀ + BitVec.ofNat 32 c := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, hI.r5]
  have h7 : s₅.gpr .r7 = BitVec.ofNat 32 q := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), hI.r6, VG.Proof.MdStream.Arm.shrB hd (by omega_using [hlen]), hq]
  have h12 : s₃.gpr .r12 = BitVec.ofNat 32 (P.B * q) := by
    rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), hI.r6, VG.Proof.MdStream.Arm.shrB hd (by omega), hq, VG.Proof.MdStream.Arm.ofNat_shlB hd (by omega)]
  have h12' : s₄.gpr .r12 = BitVec.ofNat 32 (P.B * q) := by rw [u₄.other _ (by decide), h12]
  refine ⟨⟨by omega, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.r0],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.r3],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, by rw [m₅]; exact hI.frame,
    by rw [m₅]; exact hI.saved⟩, ?_, h7, hq1, by rw [← Nat.add_assoc, Nat.add_mul_mod_self_left]; exact hr,
    .inr ⟨c, h1, by omega⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.gpr, h12, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r5, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₅.gpr, h12', u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r6, VG.Proof.MdStream.Arm.sub_ofNat (by omega), Nat.sub_sub]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.r4, hr]; rfl
  · intro iv m hm mem' hs
    have hmod := VG.Proof.MdStream.Arm.Update.length_mid hd s₀ hm (c := c) (by omega)
    rw [← VG.Proof.MdStream.Arm.Update.take_add_data]
    refine H.repr_append_blocks (n := q) hd.pos (hI.repr iv m hm) (by rw [hmod, hr])
      (by rw [List.length_take, List.length_drop, VG.Proof.MdStream.Arm.Update.D_length]; omega) ?_
    rw [hs, m₅, h1, VG.Proof.MdStream.Arm.addr_off (by omega)]
    apply H.compressBlocks_eq
    intro j hj
    rw [VG.Proof.MdStream.Arm.add_ofNat, hI.data hp (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hj]

/-! ## Buffering data -/

section
variable (P) (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (VG.Proof.MdStream.Arm.Update.cnt s₀ + c) % P.B
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (P.B - VG.Proof.MdStream.Arm.Update.rr P s₀ c) (VG.Proof.MdStream.Arm.Update.len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := VG.Proof.MdStream.Arm.Update.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.Arm.Update.rr P s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((VG.Proof.MdStream.Arm.Update.D s₀).drop c).take (VG.Proof.MdStream.Arm.Update.tt P s₀ c)
end

theorem rr_lt (hd : VG.Proof.MdStream.Arm.Dims P) (s₀ : State) (c : Nat) : VG.Proof.MdStream.Arm.Update.rr P s₀ c < P.B := Nat.mod_lt _ hd.pos
theorem tt_le (s₀ : State) (c : Nat) : VG.Proof.MdStream.Arm.Update.tt P s₀ c ≤ VG.Proof.MdStream.Arm.Update.len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : VG.Proof.MdStream.Arm.Update.tt P s₀ c ≤ P.B - VG.Proof.MdStream.Arm.Update.rr P s₀ c := Nat.min_le_left _ _
theorem rr_eq (s₀ : State) (c : Nat) : VG.Proof.MdStream.Arm.Update.rr P s₀ c = (VG.Proof.MdStream.Arm.Update.cnt s₀ + c) % P.B := rfl
theorem tt_eq (s₀ : State) (c : Nat) : VG.Proof.MdStream.Arm.Update.tt P s₀ c = min (P.B - VG.Proof.MdStream.Arm.Update.rr P s₀ c) (VG.Proof.MdStream.Arm.Update.len s₀ - c) := rfl

theorem q_eq (s₀ : State) (c : Nat) : VG.Proof.MdStream.Arm.Update.q P s₀ c = VG.Proof.MdStream.Arm.Update.stA s₀ + BitVec.ofNat 64 (P.N + VG.Proof.MdStream.Arm.Update.rr P s₀ c) :=
  VG.Proof.MdStream.Arm.add_ofNat _ _ _

theorem xs_length (s₀ : State) (c : Nat) : (VG.Proof.MdStream.Arm.Update.xs P s₀ c).length = VG.Proof.MdStream.Arm.Update.tt P s₀ c := by
  have := VG.Proof.MdStream.Arm.Update.tt_le (P := P) s₀ c
  simp only [VG.Proof.MdStream.Arm.Update.xs, List.length_take, List.length_drop, VG.Proof.MdStream.Arm.Update.D_length]; omega

/-- Byte `k` of the buffer, addressed as `[r0 + k, #N]`. -/
theorem buf_addr {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {k : Nat} (hk : k < P.B) :
    State.addr (VG.Proof.MdStream.Arm.Update.st s₀ + BitVec.ofNat 32 k + BitVec.ofNat 32 P.N) = VG.Proof.MdStream.Arm.Update.buf P s₀ + BitVec.ofNat 64 k := by
  have hp_st_fit := hp.st_fit
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, VG.Proof.MdStream.Arm.addr_off (by omega), VG.Proof.MdStream.Arm.add_ofNat, Nat.add_comm]

end

/-- The state while copying: `j` bytes copied, into memory otherwise as in `mI`. -/
structure Copy (P : Params) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ VG.Proof.MdStream.Arm.Update.tt P s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r0 : s.gpr .r0 = VG.Proof.MdStream.Arm.Update.st s₀
  r3 : s.gpr .r3 = VG.Proof.MdStream.Arm.Update.scr s₀
  sp : s.sp = s₀.sp
  r5 : s.gpr .r5 = VG.Proof.MdStream.Arm.Update.dp s₀ + BitVec.ofNat 32 (c + j)
  r6 : s.gpr .r6 = BitVec.ofNat 32 (VG.Proof.MdStream.Arm.Update.len s₀ - c - VG.Proof.MdStream.Arm.Update.tt P s₀ c)
  r4 : s.gpr .r4 = BitVec.ofNat 32 (VG.Proof.MdStream.Arm.Update.rr P s₀ c + j)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (VG.Proof.MdStream.Arm.Update.tt P s₀ c - j)
  r7 : s.gpr .r7 = 0
  mem : s.mem = VG.WriteBytes.writeBytes mI (VG.Proof.MdStream.Arm.Update.q P s₀ c) ((VG.Proof.MdStream.Arm.Update.xs P s₀ c).take j)

/-- The copy loop's body. -/
def copyBody (P : Params) : List Instr :=
  [.ldrb .r12 .r5 0, .dp .add .r1 .r0 (.reg .r4), .strb .r12 .r1 P.N, .dp .add .r5 .r5 (.imm 1),
    .dp .add .r4 .r4 (.imm 1), .subs .r8 .r8 (.imm 1)]

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem write_frame (hd : VG.Proof.MdStream.Arm.Dims P) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ VG.Proof.MdStream.Arm.Update.tt P s₀ c) :
    Frame [VG.Proof.MdStream.Arm.Update.stR P s₀] mI (VG.WriteBytes.writeBytes mI (VG.Proof.MdStream.Arm.Update.q P s₀ c) ((VG.Proof.MdStream.Arm.Update.xs P s₀ c).take j)) := by
  have hBle := hd.le
  have := VG.Proof.MdStream.Arm.Update.tt_le' (P := P) s₀ c; have := VG.Proof.MdStream.Arm.Update.rr_lt hd s₀ c; have hd_N := hd.N
  refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
  rw [VG.Proof.MdStream.Arm.Update.q_eq]
  exact VG.Proof.MdStream.Arm.contains_offset (by simp only [List.length_take]; omega) (by omega)

theorem copy_step (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.Arm.Update.Inv H s₀ c sI)
    {j : Nat} (hj : j < VG.Proof.MdStream.Arm.Update.tt P s₀ c) {s : State} (h : VG.Proof.MdStream.Arm.Update.Copy P s₀ c sI.mem j s) :
    WP isa (.block (VG.Proof.MdStream.Arm.Update.copyBody P)) s fun s' =>
      VG.Proof.MdStream.Arm.Update.Copy P s₀ c sI.mem (j + 1) s' ∧ s'.z = (BitVec.ofNat 32 (VG.Proof.MdStream.Arm.Update.tt P s₀ c - (j + 1)) == 0) := by
  have hBle := hd.le
  have hdf := hp.d_fit
  have hc := hI.c_le
  have hr := VG.Proof.MdStream.Arm.Update.rr_lt hd s₀ c
  have ht := VG.Proof.MdStream.Arm.Update.tt_le (P := P) s₀ c; have ht' := VG.Proof.MdStream.Arm.Update.tt_le' (P := P) s₀ c
  have hd_N := hd.N
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (VG.Proof.MdStream.Arm.Update.dA s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨VG.Proof.MdStream.Arm.Update.dR s₀, by simp [h.rd, hp.rd], VG.Proof.MdStream.Arm.contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (VG.Proof.MdStream.Arm.Update.dA s₀ + BitVec.ofNat 64 (c + j)) = (VG.Proof.MdStream.Arm.Update.D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega_using [ht, hj])]
    exact VG.Proof.MdStream.Arm.frame_bytes (VG.Proof.MdStream.Arm.Update.write_frame hd s₀ c sI.mem j h.j_le) (R := VG.Proof.MdStream.Arm.Update.dR s₀) (by simpa using hp.d_st)
      (by show VG.Proof.MdStream.Arm.Update.len s₀ ≤ 2 ^ 64; omega) (by show c + j < VG.Proof.MdStream.Arm.Update.len s₀; omega)
  -- The byte written.
  have hout : InRegions s.wr (VG.Proof.MdStream.Arm.Update.q P s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨VG.Proof.MdStream.Arm.Update.stR P s₀, by simp [h.wr, hp.wr], by
      rw [VG.Proof.MdStream.Arm.Update.q_eq, VG.Proof.MdStream.Arm.add_ofNat]; exact VG.Proof.MdStream.Arm.contains_offset (by omega) (by omega)⟩
  have hxs := VG.Proof.MdStream.Arm.Update.xs_length (P := P) s₀ c
  unfold VG.Proof.MdStream.Arm.Update.copyBody
  refine VG.Proof.MdStream.Arm.wp_ldrb (a := VG.Proof.MdStream.Arm.Update.dA s₀ + BitVec.ofNat 64 (c + j)) (by omega)
    (by rw [h.r5, BitVec.add_zero, VG.Proof.MdStream.Arm.addr_off (by omega_using [ht, hdf, hj])]) hin
    fun s₁ u₁ => ?_
  refine VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₂ u₂ => VG.Proof.MdStream.Arm.wp_strb (a := VG.Proof.MdStream.Arm.Update.q P s₀ c + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h.r0, h.r4, VG.Proof.MdStream.Arm.Update.buf_addr hp (by omega_using [ht', hj]), VG.Proof.MdStream.Arm.Update.q,
      VG.Proof.MdStream.Arm.add_ofNat, VG.Proof.MdStream.Arm.Update.buf]
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  refine VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₄ u₄ => VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₅ u₅ =>
    VG.Proof.MdStream.Arm.wp_subs (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r12 → r ≠ .r1 → r ≠ .r5 → r ≠ .r4 → r ≠ .r8 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have h8 : s₆.gpr .r8 = BitVec.ofNat 32 (VG.Proof.MdStream.Arm.Update.tt P s₀ c - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r8, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Proof.MdStream.Arm.sub_ofNat (by omega_using [hj]),
      Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h8, ?_, ?_⟩, ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .r0 (by decide) (by decide) (by decide) (by decide) (by decide), h.r0]
  · rw [g .r3 (by decide) (by decide) (by decide) (by decide) (by decide), h.r3]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r5, BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .r6 (by decide) (by decide) (by decide) (by decide) (by decide), h.r6]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r4, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add,
      Nat.add_assoc]
  · rw [g .r7 (by decide) (by decide) (by decide) (by decide) (by decide), h.r7]
  · have hj' : j < (VG.Proof.MdStream.Arm.Update.xs P s₀ c).length := by omega
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
      List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega)]
    have hl : (List.take j (VG.Proof.MdStream.Arm.Update.xs P s₀ c)).length = j := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl]
    have e : ((List.getD (VG.Proof.MdStream.Arm.Update.D s₀) (c + j) 0).setWidth 32).setWidth 8 = List.getD (VG.Proof.MdStream.Arm.Update.D s₀) (c + j) 0 := by
      ext i hi; simp
    rw [e]
    congr 1
    simp only [VG.Proof.MdStream.Arm.Update.xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (VG.Proof.MdStream.Arm.Update.D s₀).length by rw [VG.Proof.MdStream.Arm.Update.D_length]; omega_using [ht, hj]), Option.getD_some]
  · rw [z₆, ← u₆.gpr, h8]

theorem copy_loop_ok (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.Arm.Update.Inv H s₀ c sI)
    {s : State} (h : VG.Proof.MdStream.Arm.Update.Copy P s₀ c sI.mem 0 s) (ht : 0 < VG.Proof.MdStream.Arm.Update.tt P s₀ c) :
    WP isa (.loop (.block (VG.Proof.MdStream.Arm.Update.copyBody P)) .ne) s (VG.Proof.MdStream.Arm.Update.Copy P s₀ c sI.mem (VG.Proof.MdStream.Arm.Update.tt P s₀ c)) := by
  have hBle := hd.le
  refine WP.loop (M := isa) (fun n s => ∃ j, n = VG.Proof.MdStream.Arm.Update.tt P s₀ c - j ∧ j < VG.Proof.MdStream.Arm.Update.tt P s₀ c ∧ VG.Proof.MdStream.Arm.Update.Copy P s₀ c sI.mem j s)
    ?_ (VG.Proof.MdStream.Arm.Update.tt P s₀ c) s ⟨0, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (VG.Proof.MdStream.Arm.Update.copy_step hd hp hI hj hc) fun s' ⟨hc', hz'⟩ => ?_
  have hz : isa.eval .ne s' = some (decide (VG.Proof.MdStream.Arm.Update.tt P s₀ c - (j + 1) ≠ 0)) := by
    show VG.Arm.eval .ne s' = _
    rw [VG.Proof.MdStream.Arm.eval_ne, hz', VG.Proof.MdStream.Arm.ofNat_beq_zero (by have := VG.Proof.MdStream.Arm.Update.tt_le' (P := P) s₀ c; omega)]
    simp
  by_cases hl : VG.Proof.MdStream.Arm.Update.tt P s₀ c - (j + 1) = 0
  · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
    rwa [show j + 1 = VG.Proof.MdStream.Arm.Update.tt P s₀ c by omega] at hc'
  · exact .inr ⟨by rw [hz, decide_eq_true hl], _, by omega, j + 1, rfl, by omega_using [hl], hc'⟩

/-- The memory after copying `tt` bytes. -/
theorem copied_facts (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.Arm.Update.Inv H s₀ c sI) :
    let mem := VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.Arm.Update.q P s₀ c) (VG.Proof.MdStream.Arm.Update.xs P s₀ c)
    Frame [VG.Proof.MdStream.Arm.Update.stR P s₀, VG.Proof.MdStream.Arm.Update.scR P s₀] s₀.mem mem ∧ VG.Proof.MdStream.Arm.Update.Saved P s₀ mem ∧
      H.stateAt mem (VG.Proof.MdStream.Arm.Update.stA s₀) = H.stateAt sI.mem (VG.Proof.MdStream.Arm.Update.stA s₀) ∧
      bytesAt mem (VG.Proof.MdStream.Arm.Update.buf P s₀) (VG.Proof.MdStream.Arm.Update.rr P s₀ c + VG.Proof.MdStream.Arm.Update.tt P s₀ c) = bytesAt sI.mem (VG.Proof.MdStream.Arm.Update.buf P s₀) (VG.Proof.MdStream.Arm.Update.rr P s₀ c) ++ VG.Proof.MdStream.Arm.Update.xs P s₀ c := by
  have hBle := hd.le
  intro mem
  have hr := VG.Proof.MdStream.Arm.Update.rr_lt hd s₀ c; have ht' := VG.Proof.MdStream.Arm.Update.tt_le' (P := P) s₀ c; have hd_N := hd.N
  have hxs := VG.Proof.MdStream.Arm.Update.xs_length (P := P) s₀ c
  have hf : Frame [VG.Proof.MdStream.Arm.Update.stR P s₀] sI.mem mem := by
    have := VG.Proof.MdStream.Arm.Update.write_frame hd s₀ c sI.mem (VG.Proof.MdStream.Arm.Update.tt P s₀ c) (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega)] at this
  refine ⟨hI.frame.trans (hf.mono (by simp)), Saved.of_frame hd hp hI.saved hf, ?_, ?_⟩
  · apply H.stateAt_congr
    intro i hi
    simp only [mem, VG.Proof.MdStream.Arm.Update.q_eq]
    exact VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by omega)
  · rw [← hxs]
    exact bytesAt_writeBytes _ _ _ _ (by omega)

/-- A full buffer: compress it. -/
theorem fill_pending (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.Arm.Update.Inv H s₀ c sI)
    {s : State} (h : VG.Proof.MdStream.Arm.Update.Copy P s₀ c sI.mem (VG.Proof.MdStream.Arm.Update.tt P s₀ c) s) (hfull : VG.Proof.MdStream.Arm.Update.rr P s₀ c + VG.Proof.MdStream.Arm.Update.tt P s₀ c = P.B) :
    WP isa (.block [.dp .add .r1 .r0 (.imm (BitVec.ofNat 32 P.N)), .mov .r4 (.imm 0), .mov .r7 (.imm 1)]) s
      (VG.Proof.MdStream.Arm.Update.Pending H s₀ (c + VG.Proof.MdStream.Arm.Update.tt P s₀ c) 1) := by
  have hBle := hd.le
  have ht' := VG.Proof.MdStream.Arm.Update.tt_le' (P := P) s₀ c
  have hrr := VG.Proof.MdStream.Arm.Update.rr_eq (P := P) s₀ c; have htt := VG.Proof.MdStream.Arm.Update.tt_eq (P := P) s₀ c
  have hxs := VG.Proof.MdStream.Arm.Update.xs_length (P := P) s₀ c
  have hc := hI.c_le
  have hst := hp.st_fit
  have hd_N := hd.N
  obtain ⟨hfr, hsv, hstt, hby⟩ := VG.Proof.MdStream.Arm.Update.copied_facts hd hp hI
  have hmem : s.mem = VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.Arm.Update.q P s₀ c) (VG.Proof.MdStream.Arm.Update.xs P s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_imm hd.enc) fun s₁ u₁ => VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₂ u₂ =>
    VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r4 → r ≠ .r7 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hx1 : s₃.gpr .r1 = VG.Proof.MdStream.Arm.Update.st s₀ + BitVec.ofNat 32 P.N := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.r0]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₃, hmem]; exact hfr, by rw [m₃, hmem]; exact hsv⟩,
    by rw [u₃.other _ (by decide), u₂.gpr], by rw [u₃.gpr]; rfl, Nat.one_pos,
    by rw [← Nat.add_assoc]; exact Md.add_mod_of_eq hfull, .inl ⟨hx1, rfl⟩, ?_⟩
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .r0 (by decide) (by decide) (by decide), h.r0]
  · rw [g .r3 (by decide) (by decide) (by decide), h.r3]
  · rw [u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [g .r5 (by decide) (by decide) (by decide), h.r5]
  · rw [g .r6 (by decide) (by decide) (by decide), h.r6, Nat.sub_sub]
  · intro iv m hm mem' hs
    rw [Md.compressBlocks_one] at hs
    rw [← VG.Proof.MdStream.Arm.Update.take_add_data]
    have hmod := VG.Proof.MdStream.Arm.Update.length_mid hd s₀ hm hc
    refine H.repr_append_block hd.pos (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₃, hmem, hstt, hx1, VG.Proof.MdStream.Arm.addr_off (by omega_using [hst, hBle])]
    refine congrArg (H.compress _) (H.parse_congr fun k hk => ?_)
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show VG.Proof.MdStream.Arm.Update.rr P s₀ c + VG.Proof.MdStream.Arm.Update.tt P s₀ c = P.B from hfull] at hby
    exact VG.Proof.MdStream.Arm.bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.Arm.Update.Inv H s₀ c sI)
    {s : State} (h : VG.Proof.MdStream.Arm.Update.Copy P s₀ c sI.mem (VG.Proof.MdStream.Arm.Update.tt P s₀ c) s) (hnf : VG.Proof.MdStream.Arm.Update.rr P s₀ c + VG.Proof.MdStream.Arm.Update.tt P s₀ c ≠ P.B) : VG.Proof.MdStream.Arm.Update.Done H s₀ s := by
  have hBle := hd.le
  have hr := VG.Proof.MdStream.Arm.Update.rr_lt hd s₀ c; have ht' := VG.Proof.MdStream.Arm.Update.tt_le' (P := P) s₀ c
  have hrr := VG.Proof.MdStream.Arm.Update.rr_eq (P := P) s₀ c; have htt := VG.Proof.MdStream.Arm.Update.tt_eq (P := P) s₀ c
  have hxs := VG.Proof.MdStream.Arm.Update.xs_length (P := P) s₀ c
  have hc := hI.c_le
  have htl : VG.Proof.MdStream.Arm.Update.tt P s₀ c = VG.Proof.MdStream.Arm.Update.len s₀ - c := by omega
  obtain ⟨hfr, hsv, hstt, hby⟩ := VG.Proof.MdStream.Arm.Update.copied_facts hd hp hI
  have hmem : s.mem = VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.Arm.Update.q P s₀ c) (VG.Proof.MdStream.Arm.Update.xs P s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine ⟨⟨⟨(Nat.le_refl _), h.rd, h.wr, h.r0, h.r3, h.sp, ?_, ?_, by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩, h.r7⟩
  · rw [h.r5]; congr 2; omega_using [htl, hc]
  · rw [h.r6]; congr 1; omega_using [htl]
  · rw [h.r4]; congr 1
    rw [show VG.Proof.MdStream.Arm.Update.cnt s₀ + VG.Proof.MdStream.Arm.Update.len s₀ = VG.Proof.MdStream.Arm.Update.cnt s₀ + c + VG.Proof.MdStream.Arm.Update.tt P s₀ c by omega_using [htl, hc],
      Md.add_mod_of_lt (by omega_using [hrr, hr, ht', hnf]), ← hrr]
  · have hmod := VG.Proof.MdStream.Arm.Update.length_mid hd s₀ hm hc
    rw [show VG.Proof.MdStream.Arm.Update.len s₀ = c + VG.Proof.MdStream.Arm.Update.tt P s₀ c by omega_using [htl, hc], ← VG.Proof.MdStream.Arm.Update.take_add_data]
    refine H.repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega_using [hrr, ht', hr, hnf]) (by rw [hmem, hstt]) ?_
    rw [hmod, hxs, hmem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_eq : fill P =
    .seq (.block [.mov .r8 (.imm (BitVec.ofNat 32 P.B)), .dp .sub .r8 .r8 (.reg .r4),
      .mov .r12 (.shifted .r6 .lsr (Nat.log2 P.B)), .cmp .r12 (.imm 0)])
    (.seq (.ite .eq
        (.seq (.block [.dp .add .r12 .r6 (.reg .r4), .mov .r12 (.shifted .r12 .lsr (Nat.log2 P.B)),
            .cmp .r12 (.imm 0)])
          (.ite .eq (.block [.mov .r8 (.reg .r6)]) (.block [])))
        (.block []))
    (.seq (.block [.dp .sub .r6 .r6 (.reg .r8)])
    (.seq (.loop (.block (VG.Proof.MdStream.Arm.Update.copyBody P)) .ne)
    (.seq (.block [.cmp .r4 (.imm (BitVec.ofNat 32 P.B))])
      (.ite .eq (.block [.dp .add .r1 .r0 (.imm (BitVec.ofNat 32 P.N)), .mov .r4 (.imm 0), .mov .r7 (.imm 1)])
        (.block [])))))) := rfl

theorem fill_ok (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.Arm.Update.Inv H s₀ c s)
    (hcl : c < VG.Proof.MdStream.Arm.Update.len s₀) (h7 : s.gpr .r7 = 0) :
    WP isa (fill P) s fun s' => (∃ c' k, c < c' ∧ VG.Proof.MdStream.Arm.Update.Pending H s₀ c' k s') ∨ VG.Proof.MdStream.Arm.Update.Done H s₀ s' := by
  have ht' := VG.Proof.MdStream.Arm.Update.tt_le' (P := P) s₀ c
  have hrr := VG.Proof.MdStream.Arm.Update.rr_eq (P := P) s₀ c; have htt := VG.Proof.MdStream.Arm.Update.tt_eq (P := P) s₀ c
  have hlen := VG.Proof.MdStream.Arm.Update.len_lt s₀; have hr := VG.Proof.MdStream.Arm.Update.rr_lt hd s₀ c; have hd_le := hd.le
  rw [VG.Proof.MdStream.Arm.Update.fill_eq]
  -- `r8 := B - r; r12 := len >> log₂ B`
  refine WP.seq (VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_imm hd.encB.1) fun s₁ u₁ => VG.Proof.MdStream.Arm.wp_sub (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₂ u₂ =>
    VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_shrB hd) fun s₃ u₃ => VG.Proof.MdStream.Arm.wp_cmp (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_)
  have hI₄ : VG.Proof.MdStream.Arm.Update.Inv H s₀ c s₄ :=
    ((((hI.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide))).of_flags f₄
  have h8₄ : s₄.gpr .r8 = BitVec.ofNat 32 (P.B - VG.Proof.MdStream.Arm.Update.rr P s₀ c) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.r4, VG.Proof.MdStream.Arm.sub_ofNat (by omega)]
  have h7₄ : s₄.gpr .r7 = 0 := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h7]
  have hm₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hz₄ : s₄.z = decide (VG.Proof.MdStream.Arm.Update.len s₀ - c < P.B) := by
    rw [z₄, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.r6, VG.Proof.MdStream.Arm.cmp0_shrB hd (by omega)]
  -- `r8 := min(r8, len)`
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => VG.Proof.MdStream.Arm.Update.Inv H s₀ c s₅ ∧ s₅.gpr .r8 = BitVec.ofNat 32 (VG.Proof.MdStream.Arm.Update.tt P s₀ c) ∧
    s₅.gpr .r7 = 0 ∧ s₅.mem = s.mem) ?_ fun s₅ ⟨hI₅, h8₅, h7₅, hm₅⟩ => ?_)
  · refine WP.ite (decide (VG.Proof.MdStream.Arm.Update.len s₀ - c < P.B))
      (by show VG.Arm.eval .eq s₄ = _; rw [VG.Proof.MdStream.Arm.eval_eq, hz₄]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine WP.seq (VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₆ u₆ => VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_shrB hd) fun s₇ u₇ =>
        VG.Proof.MdStream.Arm.wp_cmp (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₈ f₈ z₈ => WP.block_nil ?_)
      have hI₈ : VG.Proof.MdStream.Arm.Update.Inv H s₀ c s₈ := ((hI₄.of_upd u₆ (by decide)).of_upd u₇ (by decide)).of_flags f₈
      have hz₈ : s₈.z = decide (VG.Proof.MdStream.Arm.Update.len s₀ - c + VG.Proof.MdStream.Arm.Update.rr P s₀ c < P.B) := by
        rw [z₈, u₇.gpr, u₆.gpr, hI₄.r6, hI₄.r4, ← BitVec.ofNat_add, VG.Proof.MdStream.Arm.cmp0_shrB hd (by omega_using [hb, hd_le, hr, hrr])]
      have e₈ : ∀ r, r ≠ .r12 → s₈.gpr r = s₄.gpr r := fun r h => by rw [f₈.gpr, u₇.other r h, u₆.other r h]
      have hm₈ : s₈.mem = s.mem := by rw [f₈.mem, u₇.mem, u₆.mem, hm₄]
      refine WP.ite (decide (VG.Proof.MdStream.Arm.Update.len s₀ - c + VG.Proof.MdStream.Arm.Update.rr P s₀ c < P.B))
        (by show VG.Arm.eval .eq s₈ = _; rw [VG.Proof.MdStream.Arm.eval_eq, hz₈]) (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₉ u₉ => WP.block_nil ⟨hI₈.of_upd u₉ (by decide), ?_,
          by rw [u₉.other _ (by decide), e₈ _ (by decide), h7₄], by rw [u₉.mem, hm₈]⟩
        rw [u₉.gpr, hI₈.r6]; congr 1; omega
      · simp only [decide_eq_false_iff_not] at hb'
        refine WP.block_nil ⟨hI₈, ?_, by rw [e₈ _ (by decide), h7₄], hm₈⟩
        rw [e₈ _ (by decide), h8₄]; congr 1; omega
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨hI₄, ?_, h7₄, hm₄⟩
      rw [h8₄]; congr 1; omega
  -- `r6 -= r8`
  refine WP.seq (VG.Proof.MdStream.Arm.wp_sub (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_)
  have hC₀ : VG.Proof.MdStream.Arm.Update.Copy P s₀ c s.mem 0 s₆ := by
    have e : ∀ r, r ≠ .r6 → s₆.gpr r = s₅.gpr r := fun r h => u₆.other r h
    refine ⟨Nat.zero_le _, by rw [u₆.rd, hI₅.rd], by rw [u₆.wr, hI₅.wr],
      by rw [e _ (by decide), hI₅.r0], by rw [e _ (by decide), hI₅.r3],
      by rw [u₆.sp, hI₅.sp], by rw [e _ (by decide), hI₅.r5, Nat.add_zero], ?_,
      by rw [e _ (by decide), hI₅.r4, Nat.add_zero], by rw [e _ (by decide), h8₅, Nat.sub_zero],
      by rw [e _ (by decide), h7₅], ?_⟩
    · rw [u₆.gpr, hI₅.r6, h8₅, VG.Proof.MdStream.Arm.sub_ofNat (by omega), Nat.sub_sub]
    · rw [u₆.mem, hm₅, List.take_zero, VG.WriteBytes.writeBytes_nil]
  -- Copy the bytes.
  refine WP.seq (WP.mono (VG.Proof.MdStream.Arm.Update.copy_loop_ok hd hp hI hC₀ (by omega)) fun s₇ hC => ?_)
  -- Is the buffer full?
  refine WP.seq (VG.Proof.MdStream.Arm.wp_cmp (VG.Proof.MdStream.Arm.op2_imm hd.encB.1) fun s₈ f₈ z₈ => WP.block_nil ?_)
  have hC₈ : VG.Proof.MdStream.Arm.Update.Copy P s₀ c s.mem (VG.Proof.MdStream.Arm.Update.tt P s₀ c) s₈ :=
    ⟨hC.j_le, by rw [f₈.rd, hC.rd], by rw [f₈.wr, hC.wr], by rw [f₈.gpr, hC.r0], by rw [f₈.gpr, hC.r3],
      by rw [f₈.sp, hC.sp], by rw [f₈.gpr, hC.r5], by rw [f₈.gpr, hC.r6],
      by rw [f₈.gpr, hC.r4], by rw [f₈.gpr, hC.r8], by rw [f₈.gpr, hC.r7], by rw [f₈.mem, hC.mem]⟩
  have hz : VG.Arm.eval .eq s₈ = some (decide (VG.Proof.MdStream.Arm.Update.rr P s₀ c + VG.Proof.MdStream.Arm.Update.tt P s₀ c = P.B)) := by
    rw [VG.Proof.MdStream.Arm.eval_eq, z₈, hC.r4, VG.Proof.MdStream.Arm.sub_beq (by omega_using [hd_le, hr, ht']) (by omega)]
  refine WP.ite (decide (VG.Proof.MdStream.Arm.Update.rr P s₀ c + VG.Proof.MdStream.Arm.Update.tt P s₀ c = P.B)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (VG.Proof.MdStream.Arm.Update.fill_pending hd hp hI hC₈ hb) fun s' h => .inl ⟨c + VG.Proof.MdStream.Arm.Update.tt P s₀ c, 1, by omega, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (VG.Proof.MdStream.Arm.Update.fill_done hd hp hI hC₈ hb))

/-! ## One iteration -/

theorem body_ok (hd : VG.Proof.MdStream.Arm.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.Arm.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.Arm.Update.Inv H s₀ c s) (hcl : c < VG.Proof.MdStream.Arm.Update.len s₀) :
    WP isa (updateBody P name code) s fun s' => ∃ c', c < c' ∧ VG.Proof.MdStream.Arm.Update.Inv H s₀ c' s' ∧ s'.z = decide (VG.Proof.MdStream.Arm.Update.len s₀ - c' = 0) := by
  have hBle := hd.le
  have hlen := VG.Proof.MdStream.Arm.Update.len_lt s₀; have hr := VG.Proof.MdStream.Arm.Update.rr_lt hd s₀ c
  unfold updateBody
  refine WP.seq (VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₁ u₁ => VG.Proof.MdStream.Arm.wp_cmp (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₂ f₂ z₂ =>
    WP.block_nil ?_)
  have hI₂ : VG.Proof.MdStream.Arm.Update.Inv H s₀ c s₂ := (hI.of_upd u₁ (by decide)).of_flags f₂
  have h7₂ : s₂.gpr .r7 = 0 := by rw [f₂.gpr, u₁.gpr]
  have hz₂ : s₂.z = decide (VG.Proof.MdStream.Arm.Update.rr P s₀ c = 0) := by
    rw [z₂, u₁.other _ (by decide), hI.r4, VG.Proof.MdStream.Arm.cmp0 (Nat.lt_of_lt_of_le hr (by omega))]
  refine WP.seq (WP.mono (Q := fun s' => (∃ c' k, c < c' ∧ VG.Proof.MdStream.Arm.Update.Pending H s₀ c' k s') ∨ VG.Proof.MdStream.Arm.Update.Done H s₀ s') ?_
    fun s' h => ?_)
  · refine WP.ite (decide (VG.Proof.MdStream.Arm.Update.rr P s₀ c = 0)) (by show VG.Arm.eval .eq s₂ = _; rw [VG.Proof.MdStream.Arm.eval_eq, hz₂])
      (fun hb => ?_) (fun _ => VG.Proof.MdStream.Arm.Update.fill_ok hd hp hI₂ hcl h7₂)
    simp only [decide_eq_true_eq] at hb
    refine WP.seq (VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_shrB hd) fun s₃ u₃ => VG.Proof.MdStream.Arm.wp_cmp (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₄ f₄ z₄ =>
      WP.block_nil ?_)
    have hI₄ : VG.Proof.MdStream.Arm.Update.Inv H s₀ c s₄ := (hI₂.of_upd u₃ (by decide)).of_flags f₄
    have h7₄ : s₄.gpr .r7 = 0 := by rw [f₄.gpr, u₃.other _ (by decide), h7₂]
    have hz₄ : s₄.z = decide (VG.Proof.MdStream.Arm.Update.len s₀ - c < P.B) := by
      rw [z₄, u₃.gpr, hI₂.r6, VG.Proof.MdStream.Arm.cmp0_shrB hd (by omega)]
    refine WP.ite (decide (VG.Proof.MdStream.Arm.Update.len s₀ - c < P.B)) (by show VG.Arm.eval .eq s₄ = _; rw [VG.Proof.MdStream.Arm.eval_eq, hz₄])
      (fun _ => VG.Proof.MdStream.Arm.Update.fill_ok hd hp hI₄ hcl h7₄) (fun hb' => ?_)
    simp only [decide_eq_false_iff_not, Nat.not_lt] at hb'
    have := Nat.mul_pos hd.pos (Nat.div_pos hb' hd.pos)
    exact WP.mono (VG.Proof.MdStream.Arm.Update.direct_ok hd hp hI₄ hb hb') fun s' h => .inl ⟨_, _, by omega, h⟩
  · refine WP.seq (WP.mono (Q := fun (s' : State) => ∃ c', c < c' ∧ VG.Proof.MdStream.Arm.Update.Inv H s₀ c' s') ?_ ?_)
    · refine WP.seq (VG.Proof.MdStream.Arm.wp_cmp (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_)
      rcases h with ⟨c', k, hc', hP⟩ | ⟨hD, h7⟩
      · have hP₅ : VG.Proof.MdStream.Arm.Update.Pending H s₀ c' k s₅ :=
          { hP.toCommon.of_gpr (fun r _ => by rw [f₅.gpr]) f₅.mem f₅.rd f₅.wr f₅.sp with
            r4 := by rw [f₅.gpr, hP.r4]
            r7 := by rw [f₅.gpr, hP.r7]
            k_pos := hP.k_pos
            mod := hP.mod
            src := by rw [f₅.gpr]; exact hP.src
            repr := by rw [f₅.mem, f₅.gpr]; exact hP.repr }
        refine WP.ite false (by
            show VG.Arm.eval .eq s₅ = _
            rw [VG.Proof.MdStream.Arm.eval_eq, z₅, hP.r7, VG.Proof.MdStream.Arm.cmp0 (hP.k_lt hd), decide_eq_false (Nat.pos_iff_ne_zero.mp hP.k_pos)])
          (fun h => by cases h) fun _ => WP.mono (hP₅.compress_ok hd hf hp) fun s'' h => ⟨c', hc', h⟩
      · refine WP.ite true (by show VG.Arm.eval .eq s₅ = _; rw [VG.Proof.MdStream.Arm.eval_eq, z₅, h7]; rfl)
          (fun _ => WP.block_nil ⟨VG.Proof.MdStream.Arm.Update.len s₀, hcl, hD.of_flags f₅⟩) fun h => by cases h
    · intro s' ⟨c', hc', hI'⟩
      refine VG.Proof.MdStream.Arm.wp_cmp (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s'' f'' z'' => WP.block_nil ⟨c', hc', hI'.of_flags f'', ?_⟩
      rw [z'', hI'.r6, VG.Proof.MdStream.Arm.cmp0 (by omega)]

end

/-! ## Prologue and epilogue -/

/-- The prologue after saving. -/
def prologue (P : Params) : List Instr :=
  [.mov .r3 (.reg .r12), .dp .and .r4 .r2 (.imm (BitVec.ofNat 32 (P.B - 1))), .ldrSp .r5 0, .ldrSp .r6 4,
    .cmp .r6 (.imm 0)]

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem update_eq (name : String) (code : Prog isa) : update P name code =
    .seq (.block (([.ldrSp .r12 8] : List Instr) ++ save P .r12 ++ VG.Proof.MdStream.Arm.Update.prologue P))
    (.seq (.ite .eq (.block []) (.loop (updateBody P name code) .ne)) (.block (restore P))) := rfl

/-- The stack arguments, word by word. -/
theorem argAddr_eq {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {k : Nat} (hk : k < 3) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have hp_sp_fit := hp.sp_fit
  simp only [stackArgAddr]
  rw [VG.Proof.MdStream.Arm.addr_off (by omega)]
  simp

theorem arg_in {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {k : Nat} (hk : k < 3) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨VG.Proof.MdStream.Arm.Update.argR s₀, by simp [hp.rd], by rw [VG.Proof.MdStream.Arm.Update.argAddr_eq hp hk]; exact VG.Proof.MdStream.Arm.contains_offset (by omega) (by omega)⟩

theorem arg_sub {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {k : Nat} (hk : k < 3) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (VG.Proof.MdStream.Arm.Update.argR s₀) := by
  rw [VG.Proof.MdStream.Arm.Update.argAddr_eq hp hk]; exact VG.Proof.MdStream.Arm.sub_offset (by omega) (by omega)

theorem prologue_ok (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) :
    WP isa (.block (([.ldrSp .r12 8] : List Instr) ++ save P .r12 ++ VG.Proof.MdStream.Arm.Update.prologue P)) s₀
      fun s => VG.Proof.MdStream.Arm.Update.Inv H s₀ 0 s ∧ s.z = decide (VG.Proof.MdStream.Arm.Update.len s₀ = 0) := by
  have hsc := hp.scr_fit; have hd_so := hd.so; have hd_N := hd.N
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.MdStream.Arm.wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (VG.Proof.MdStream.Arm.Update.arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = VG.Proof.MdStream.Arm.Update.scr s₀ := u₁.gpr
  refine VG.Proof.MdStream.Arm.save_ok hd (by rw [h12]; omega) (fun d hd₁ hd₂ => ⟨VG.Proof.MdStream.Arm.Update.scR P s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact VG.Proof.MdStream.Arm.contains_offset (by omega_using [hd₂]) (by omega_using [hd₂, hsc])⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  -- The stack arguments are unchanged by the save.
  have hframe : Frame [VG.Proof.MdStream.Arm.Update.scR P s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]
    exact VG.Arm.Spill.saveMem_frame _ _ _ (by omega) _ fun p hp' => by have := VG.Proof.MdStream.Arm.saved_bound hd p hp'; omega_using [this]
  have harg : ∀ k, k < 3 → s₂.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := fun k hk =>
    hframe.readW (Region.contains_self _ _) (by simpa using (hp.a_scr.sub_left (VG.Proof.MdStream.Arm.Update.arg_sub hp hk))) (by decide)
  unfold VG.Proof.MdStream.Arm.Update.prologue
  refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₃ u₃ => VG.Proof.MdStream.Arm.wp_and (VG.Proof.MdStream.Arm.op2_imm hd.encB.2.1) fun s₄ u₄ => ?_
  refine VG.Proof.MdStream.Arm.wp_ldrSp (a := stackArgAddr s₀ 0) (by decide)
    (by rw [u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact VG.Proof.MdStream.Arm.Update.arg_in hp (by decide)) fun s₅ u₅ => ?_
  refine VG.Proof.MdStream.Arm.wp_ldrSp (a := stackArgAddr s₀ 1) (by decide)
    (by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact VG.Proof.MdStream.Arm.Update.arg_in hp (by decide))
    fun s₆ u₆ => VG.Proof.MdStream.Arm.wp_cmp (VG.Proof.MdStream.Arm.op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_
  have mm : s₇.mem = s₂.mem := by rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have g : ∀ r, r ∉ [Reg.r3, .r4, .r5, .r6, .r12] → s₇.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f₇.gpr, u₆.other r hr.2.2.2.1, u₅.other r hr.2.2.1, u₄.other r hr.2.1, u₃.other r hr.1, g₂,
      u₁.other r hr.2.2.2.2]
  have h6' : s₆.gpr .r6 = stackArg s₀ 1 := by
    rw [u₆.gpr, u₅.mem, u₄.mem, u₃.mem, harg 1 (by decide)]
  have h6 : s₇.gpr .r6 = stackArg s₀ 1 := by rw [f₇.gpr, h6']
  refine ⟨⟨⟨Nat.zero_le _, by rw [f₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
    by rw [f₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr], g _ (by decide), ?_,
    by rw [f₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, h12]
  · rw [f₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, harg 0 (by decide)]; simp
  · rw [h6]; simp
  · rw [mm]; exact hframe.mono (by simp)
  · intro p hp'
    rw [mm, m₂, u₁.mem, h12, VG.Proof.MdStream.Arm.saveMem_saved hd _ _ _ p hp', u₁.other _ (Ne.symm ?_)]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂,
      u₁.other _ (by decide), VG.Proof.MdStream.Arm.andB hd, Nat.add_zero, VG.Proof.MdStream.Arm.Update.cnt_mod hd]
  · intro iv m hm
    rw [List.take_zero, List.append_nil, mm]
    exact H.repr_congr hd.pos (fun i hi => VG.Proof.MdStream.Arm.frame_bytes hframe (R := VG.Proof.MdStream.Arm.Update.stR P s₀)
      (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; have hd_le := hd.le; omega) hi) hm.1
  · rw [z₇, h6']
    have := VG.Proof.MdStream.Arm.cmp0 (a := VG.Proof.MdStream.Arm.Update.len s₀) (VG.Proof.MdStream.Arm.Update.len_lt s₀)
    simpa using this

theorem epilogue_ok (hd : VG.Proof.MdStream.Arm.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) {s : State} (hI : VG.Proof.MdStream.Arm.Update.Inv H s₀ (VG.Proof.MdStream.Arm.Update.len s₀) s) :
    WP isa (.block (restore P)) s fun s' => abiPreserved s₀ s' ∧ (VG.Proof.MdStream.Arm.updK H).post s₀ s' := by
  have hd_so := hd.so
  refine VG.Proof.MdStream.Arm.restore_ok hd hI.r3 hp.scr_fit
    (fun d hd₁ hd₂ => ⟨VG.Proof.MdStream.Arm.Update.scR P s₀, by simp [hI.rd, hI.wr, hp.wr], VG.Proof.MdStream.Arm.contains_offset (by omega_using [hd₂]) (by omega)⟩) s₀.gpr
    hI.saved fun s' hs _ hmem _ _ hsp => ⟨⟨VG.Proof.MdStream.Arm.preserved_of hs, by rw [hsp, hI.sp]⟩, fun iv m hr hc => ?_⟩
  have := hI.repr iv m ⟨hr, hc⟩
  rwa [List.take_of_length_le (Nat.le_of_eq (VG.Proof.MdStream.Arm.Update.D_length _)), ← hmem] at this

theorem correct (hd : VG.Proof.MdStream.Arm.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.Arm.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.Arm.Update.Pre P s₀) :
    WP isa (update P name code) s₀ fun s' => abiPreserved s₀ s' ∧ (VG.Proof.MdStream.Arm.updK H).post s₀ s' := by
  have hlen := VG.Proof.MdStream.Arm.Update.len_lt s₀
  rw [VG.Proof.MdStream.Arm.Update.update_eq]
  refine WP.seq (WP.mono (VG.Proof.MdStream.Arm.Update.prologue_ok (H := H) hd hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.MdStream.Arm.Update.Inv H s₀ (VG.Proof.MdStream.Arm.Update.len s₀)) ?_ fun s₂ hI₂ => VG.Proof.MdStream.Arm.Update.epilogue_ok hd hp hI₂)
  refine WP.ite (decide (VG.Proof.MdStream.Arm.Update.len s₀ = 0)) (by show VG.Arm.eval .eq s₁ = _; rw [VG.Proof.MdStream.Arm.eval_eq, hz])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = VG.Proof.MdStream.Arm.Update.len s₀ - c ∧ c < VG.Proof.MdStream.Arm.Update.len s₀ ∧ VG.Proof.MdStream.Arm.Update.Inv H s₀ c s) ?_ (VG.Proof.MdStream.Arm.Update.len s₀) s₁
      ⟨0, rfl, by omega, hI⟩
    rintro n s ⟨c, rfl, hcl, hI⟩
    refine WP.mono (VG.Proof.MdStream.Arm.Update.body_ok hd hf hp hI hcl) fun s' ⟨c', hc, hI', hz'⟩ => ?_
    have hc' := hI'.c_le
    have hz : isa.eval .ne s' = some (decide (VG.Proof.MdStream.Arm.Update.len s₀ - c' ≠ 0)) := by
      show VG.Arm.eval .ne s' = _
      rw [VG.Proof.MdStream.Arm.eval_ne, hz']
      simp
    by_cases hl : VG.Proof.MdStream.Arm.Update.len s₀ - c' = 0
    · refine .inl ⟨by rw [hz, decide_eq_false fun h => h hl], ?_⟩
      rwa [show c' = VG.Proof.MdStream.Arm.Update.len s₀ by omega] at hI'
    · exact .inr ⟨by rw [hz, decide_eq_true hl], VG.Proof.MdStream.Arm.Update.len s₀ - c', by omega, c', rfl, by omega_using [hl], hI'⟩

end

/-! ## Constant time -/

/-- The initial taint: `r0` (`state`) and `r2:r3` (`count`) are public, `r0`
points at the state, and the 12 bytes of stack arguments are public, the
third one pointing at the scratch space. -/
def τ₀ (P : Params) : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r2, .r3], flags := false, lens := [P.N + P.B, P.so + 48], bases := [(.r0, 0)],
    argLen := 12, argBases := [(8, 1)] }

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem wf₀ {s : State} (h : (VG.Proof.MdStream.Arm.updK H).pre s) : VG.Arm.Taint.Wf (VG.Proof.MdStream.Arm.Update.τ₀ P) s := by
  have hp := VG.Proof.MdStream.Arm.Update.pre_of h
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  refine ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.MdStream.Arm.Update.τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩, ?_, fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [VG.Proof.MdStream.Arm.addr_toNat] <;> omega
  · intro p hp'; simp only [VG.Proof.MdStream.Arm.Update.τ₀, List.mem_singleton] at hp'; subst hp'; simp [VG.Arm.Taint.region, hp.wr]
  · have e : (⟨State.addr s.sp, 12⟩ : Region) = VG.Proof.MdStream.Arm.Update.argR s := by simp [stackArgAddr]
    simp only [VG.Proof.MdStream.Arm.Update.τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.a_st
    · exact hp.a_scr
  · intro p hp'; simp only [VG.Proof.MdStream.Arm.Update.τ₀, List.mem_singleton] at hp'; subst hp'
    refine ⟨Nat.le_refl 12, ?_⟩
    simp only [VG.Arm.Taint.region, hp.wr]
    rfl

theorem agree₀ {s₁ s₂ : State} (h₁ : (VG.Proof.MdStream.Arm.updK H).pre s₁) (h₂ : (VG.Proof.MdStream.Arm.updK H).pre s₂)
    (hpub : (VG.Proof.MdStream.Arm.updK H).pub s₁ s₂) : VG.Arm.Taint.Agree (VG.Proof.MdStream.Arm.Update.τ₀ P) s₁ s₂ := by
  obtain ⟨psp, p0, p2, p3, a0, a1, a2⟩ := hpub
  have hp₁ := VG.Proof.MdStream.Arm.Update.pre_of h₁; have hp₂ := VG.Proof.MdStream.Arm.Update.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.MdStream.Arm.Update.wf₀ h₁, VG.Proof.MdStream.Arm.Update.wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp, fun k hk => ?_⟩
  · simp only [VG.Proof.MdStream.Arm.Update.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.MdStream.Arm.Update.stR, VG.Proof.MdStream.Arm.Update.scR, VG.Proof.MdStream.Arm.Update.stA, VG.Proof.MdStream.Arm.Update.scA, VG.Proof.MdStream.Arm.Update.st, VG.Proof.MdStream.Arm.Update.scr, p0, a2]
  · simp only [VG.Proof.MdStream.Arm.Update.τ₀] at hk
    rw [VG.Proof.MdStream.Arm.argByte_eq hp₁.sp_fit hk, VG.Proof.MdStream.Arm.argByte_eq hp₂.sp_fit hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    have : k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 := by omega
    rcases this with h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2

end

/-- A state satisfying the precondition (with no data, and the scratch space at 0). -/
def sat (P : Params) : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0, 0⟩, ⟨0x4000, 12⟩]
  wr := [⟨0x1000, P.N + P.B⟩, ⟨0, P.so + 48⟩]

/-- `update` is verified, given that it is constant time (which the taint
analysis proves of each hash function's code). -/
theorem verified {P : Params} {H : Md P.B P.N P.L} (hd : VG.Proof.MdStream.Arm.Dims P) {name : String} {code : Prog isa}
    (hf : VG.Proof.MdStream.Arm.CalleeOk H code) (hct : ConstantTime isa (VG.Proof.MdStream.Arm.updK H).pre (VG.Proof.MdStream.Arm.updK H).pub (update P name code)) :
    Verified Arm.target (update P name code) (VG.Proof.MdStream.Arm.updK H) := by
  have hBle := hd.le
  have hd_N := hd.N; have hd_so := hd.so
  refine ⟨fun s hs => ?_, hct, ?_⟩
  · obtain ⟨t, s', he, h⟩ := VG.Proof.MdStream.Arm.Update.correct hd hf (VG.Proof.MdStream.Arm.Update.pre_of hs)
    exact ⟨t, s', he, h⟩
  · have e : ∀ k, stackArg (VG.Proof.MdStream.Arm.Update.sat P) k = 0 := fun k => by
      simp [stackArg, VG.Proof.MdStream.Arm.Update.sat, Mem.readW, Mem.read]
    refine ⟨VG.Proof.MdStream.Arm.Update.sat P, ?_⟩
    simp only [VG.Proof.MdStream.Arm.updK, e]
    refine ⟨by simp [VG.Proof.MdStream.Arm.Update.sat, stackArgAddr, State.addr], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [VG.Proof.MdStream.Arm.Update.sat, stackArgAddr, State.addr]
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)).symm
    iterate 2 exact Offset.disjoint_of_le (by simp) (by simp <;> omega)
    iterate 2 exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    all_goals simp <;> omega

end VG.Proof.MdStream.Arm.Update

end

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.Arm.Words`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on ARMv7: length fields and digests

What the length fields (`len64`) and digests (`out32`) of
`Impl/MdStream/Arm.lean` write, for the hash functions' `Shape`s.
-/

namespace VG.Proof.MdStream.Arm

open VG VG.Arm VG.Impl.MdStream.Arm
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil write_eq_writeBytes writeBytes_append
  writeBytes_frame shl3 bits8)

/-! ## Byte order -/

/-- The bytes of a byte-reversed word, one by one. -/
theorem rev_byte_0 (x : BitVec 32) : (rev x).extractLsb' 0 8 = x.extractLsb' 24 8 := by
  unfold rev
  rw [BitVec.extractLsb'_append_eq_of_add_le (v := 24) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev_byte_1 (x : BitVec 32) : (rev x).extractLsb' 8 8 = x.extractLsb' 16 8 := by
  unfold rev
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 16) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev_byte_2 (x : BitVec 32) : (rev x).extractLsb' 16 8 = x.extractLsb' 8 8 := by
  unfold rev
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev_byte_3 (x : BitVec 32) : (rev x).extractLsb' 24 8 = x.extractLsb' 0 8 := by
  unfold rev
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self


theorem bytes32_store (be : Bool) (x : BitVec 32) :
    (List.range 4).map (fun j => (if be then rev x else x).extractLsb' (8 * j) 8) = bytes32 be x := by
  cases be
  · rfl
  · simp only [bytes32, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, Nat.reduceMul, VG.Proof.MdStream.Arm.rev_byte_0, VG.Proof.MdStream.Arm.rev_byte_1, VG.Proof.MdStream.Arm.rev_byte_2,
      VG.Proof.MdStream.Arm.rev_byte_3]


theorem writeW32 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 32) :
    m.writeW a (if be then rev x else x) = VG.WriteBytes.writeBytes m a (bytes32 be x) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes, ← VG.Proof.MdStream.Arm.bytes32_store]; rfl

theorem writeW_le (m : Mem) (a : Addr) (x : BitVec 32) :
    m.writeW a x = VG.WriteBytes.writeBytes m a (bytes32 false x) := VG.Proof.MdStream.Arm.writeW32 m a false x

theorem writeW_be (m : Mem) (a : Addr) (x : BitVec 32) :
    m.writeW a (rev x) = VG.WriteBytes.writeBytes m a (bytes32 true x) := VG.Proof.MdStream.Arm.writeW32 m a true x

theorem halves_lo (hi lo : BitVec 32) {s : Nat} (h : s + 8 ≤ 32) :
    (hi ++ lo : BitVec 64).extractLsb' s 8 = lo.extractLsb' s 8 :=
  BitVec.extractLsb'_append_eq_of_add_le (v := 32) (w := 32) h

theorem halves_hi (hi lo : BitVec 32) {s : Nat} (h : 32 ≤ s) :
    (hi ++ lo : BitVec 64).extractLsb' s 8 = hi.extractLsb' (s - 32) 8 :=
  BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 32) h

/-- A 64-bit word's bytes are its halves'. -/
theorem bytes64_halves (be : Bool) (hi lo : BitVec 32) :
    bytes64 be (hi ++ lo) =
      if be then bytes32 true hi ++ bytes32 true lo else bytes32 false lo ++ bytes32 false hi := by
  cases be <;>
  simp (disch := decide) only [bytes64, bytes32, Bool.false_eq_true, ite_false, ite_true, List.range_succ,
    List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append, List.reverse_cons,
    List.reverse_nil, Nat.reduceMul, VG.Proof.MdStream.Arm.halves_lo, VG.Proof.MdStream.Arm.halves_hi, Nat.reduceSub]


theorem InRegions.offset {rs : List Region} {a : Addr} {n off m : Nat} (h : InRegions rs a n)
    (hm : off + m ≤ n) (hn : n < 2 ^ 64) : InRegions rs (a + BitVec.ofNat 64 off) m := by
  obtain ⟨R, hR, hc⟩ := h
  refine ⟨R, hR, ?_⟩
  simp only [Region.Contains] at *
  have : (a + BitVec.ofNat 64 off - R.base).toNat ≤ (a - R.base).toNat + off := by
    rw [Offset.add_sub_comm,
      BitVec.toNat_add, VG.Proof.MdStream.Arm.toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

/-! ## The length field -/

/-- `len64 d be` stores `8 · (r5:r4)` at `r0 + d`. -/
theorem len64_ok {d : Nat} {be : Bool} {s : State} (hd : d + 4 < 4096)
    (hfit : (s.gpr .r0).toNat + d + 8 ≤ 2 ^ 32)
    (hout : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 d) 8) :
    WP isa (.block (len64 d be)) s fun s' => (∀ r, r ≠ .r9 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 d)
        (bytes64 be (BitVec.ofNat 64 (8 * (s.gpr .r5 ++ s.gpr .r4).toNat))) := by
  have hv : BitVec.ofNat 64 (8 * (s.gpr .r5 ++ s.gpr .r4).toNat) =
      (s.gpr .r5 <<< 3 ||| s.gpr .r4 >>> 29) ++ s.gpr .r4 <<< 3 := by rw [bits8, shl3]
  have a0 : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = State.addr (s.gpr .r0) + BitVec.ofNat 64 d :=
    VG.Proof.MdStream.Arm.addr_off (by omega)
  have a4 : State.addr (s.gpr .r0 + BitVec.ofNat 32 (d + 4)) =
      State.addr (s.gpr .r0) + BitVec.ofNat 64 d + BitVec.ofNat 64 4 := by
    rw [VG.Proof.MdStream.Arm.addr_off (by omega), VG.Proof.MdStream.Arm.add_ofNat]
  have o0 : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 d) 4 := by
    simpa using InRegions.offset hout (off := 0) (m := 4) (by omega) (by omega)
  have o4 : InRegions s.wr (State.addr (s.gpr .r0) + BitVec.ofNat 64 d + BitVec.ofNat 64 4) 4 :=
    InRegions.offset hout (by omega) (by omega)
  have hw : ∀ (m : Mem) (xs ys : List Byte), xs.length = 4 → ys.length = 4 →
      VG.WriteBytes.writeBytes (VG.WriteBytes.writeBytes m (State.addr (s.gpr .r0) + BitVec.ofNat 64 d) xs)
        (State.addr (s.gpr .r0) + BitVec.ofNat 64 d + BitVec.ofNat 64 4) ys =
      VG.WriteBytes.writeBytes m (State.addr (s.gpr .r0) + BitVec.ofNat 64 d) (xs ++ ys) := by
    intro m xs ys hx hy
    rw [← VG.WriteBytes.writeBytes_append _ _ _ _ (by omega), hx]
  cases be
  · simp only [len64, Bool.false_eq_true, ite_false]
    refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_lsl (by decide)) fun s₁ u₁ => VG.Proof.MdStream.Arm.wp_str (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 d)
      (by omega) (by rw [u₁.other _ (by decide), a0]) (by rw [u₁.wr]; exact o0) fun s₂ g₂ => ?_
    refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_lsl (by decide)) fun s₃ u₃ => VG.Proof.MdStream.Arm.wp_orr (VG.Proof.MdStream.Arm.op2_lsr (by decide)) fun s₄ u₄ =>
      VG.Proof.MdStream.Arm.wp_str (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 d + BitVec.ofNat 64 4) (by omega)
        (by rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), a4])
        (by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr]; exact o4) fun s₅ g₅ => WP.block_nil
          ⟨fun r h => by rw [g₅.gpr, u₄.other r h, u₃.other r h, g₂.gpr, u₁.other r h],
            by rw [g₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd], by rw [g₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr],
            by rw [g₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp], ?_⟩
    have e₄ : s₄.gpr .r9 = s.gpr .r5 <<< 3 ||| s.gpr .r4 >>> 29 := by
      rw [u₄.gpr, u₃.gpr, u₃.other .r4 (by decide), g₂.gpr, u₁.other .r5 (by decide), u₁.other .r4 (by decide)]
    rw [g₅.mem, e₄, u₄.mem, u₃.mem, g₂.mem, u₁.gpr, u₁.mem, hv, VG.Proof.MdStream.Arm.bytes64_halves]
    simp only [Bool.false_eq_true, ite_false]
    rw [VG.Proof.MdStream.Arm.writeW_le, VG.Proof.MdStream.Arm.writeW_le, hw _ _ _ (bytes32_length _ _) (bytes32_length _ _)]
  · simp only [len64, ite_true]
    refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_lsl (by decide)) fun s₁ u₁ => VG.Proof.MdStream.Arm.wp_orr (VG.Proof.MdStream.Arm.op2_lsr (by decide)) fun s₂ u₂ =>
      VG.Proof.MdStream.Arm.wp_rev fun s₃ u₃ => VG.Proof.MdStream.Arm.wp_str (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 d)
      (by omega) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), a0])
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact o0) fun s₄ g₄ => ?_
    refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_lsl (by decide)) fun s₅ u₅ => VG.Proof.MdStream.Arm.wp_rev fun s₆ u₆ =>
      VG.Proof.MdStream.Arm.wp_str (a := State.addr (s.gpr .r0) + BitVec.ofNat 64 d + BitVec.ofNat 64 4) (by omega)
        (by rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr, u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.other _ (by decide), a4])
        (by rw [u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact o4) fun s₇ g₇ => WP.block_nil
          ⟨fun r h => by rw [g₇.gpr, u₆.other r h, u₅.other r h, g₄.gpr, u₃.other r h, u₂.other r h,
              u₁.other r h],
            by rw [g₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd],
            by rw [g₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr],
            by rw [g₇.sp, u₆.sp, u₅.sp, g₄.sp, u₃.sp, u₂.sp, u₁.sp], ?_⟩
    have e₃ : s₃.gpr .r9 = rev (s.gpr .r5 <<< 3 ||| s.gpr .r4 >>> 29) := by
      rw [u₃.gpr, u₂.gpr, u₁.gpr, u₁.other .r4 (by decide)]
    have e₆ : s₆.gpr .r9 = rev (s.gpr .r4 <<< 3) := by
      rw [u₆.gpr, u₅.gpr, g₄.gpr, u₃.other .r4 (by decide), u₂.other .r4 (by decide), u₁.other .r4 (by decide)]
    rw [g₇.mem, e₆, u₆.mem, u₅.mem, g₄.mem, e₃, u₃.mem, u₂.mem, u₁.mem, hv, VG.Proof.MdStream.Arm.bytes64_halves]
    simp only [ite_true]
    rw [VG.Proof.MdStream.Arm.writeW_be, VG.Proof.MdStream.Arm.writeW_be, hw _ _ _ (bytes32_length _ _) (bytes32_length _ _)]

/-! ## The digest -/

/-- `out32 n be` writes the `n` 32-bit words at `r0` to `r6`. -/
theorem out32_ok {n : Nat} (be : Bool) (hn : 4 * n ≤ 64) {s₀ : State}
    (f₀ : (s₀.gpr .r0).toNat + 4 * n ≤ 2 ^ 32) (f₆ : (s₀.gpr .r6).toNat + 4 * n ≤ 2 ^ 32)
    (hin : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r0)) (4 * n))
    (hout : InRegions s₀.wr (State.addr (s₀.gpr .r6)) (4 * n))
    (hd : Region.Disjoint ⟨State.addr (s₀.gpr .r0), 4 * n⟩ ⟨State.addr (s₀.gpr .r6), 4 * n⟩) :
    WP isa (.block (out32 n be)) s₀ fun s' =>
      (∀ r, r ≠ .r9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s₀.mem (State.addr (s₀.gpr .r6))
        ((List.range n).flatMap fun k =>
          bytes32 be (s₀.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * k)) 32)) := by
  let f : Nat → List Byte := fun k =>
    bytes32 be (s₀.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * k)) 32)
  have hflat : ∀ k, ((List.range k).flatMap f).length = 4 * k := by
    intro k
    rw [List.length_flatMap, List.map_congr_left (fun x _ => bytes32_length _ _), List.map_const',
      List.sum_replicate_nat, List.length_range, Nat.mul_comm]
  -- Words `[n - j, n)` are left, the others written.
  suffices h : ∀ j ≤ n, ∀ s, (∀ r, r ≠ .r9 → s.gpr r = s₀.gpr r) → s.rd = s₀.rd → s.wr = s₀.wr →
      s.sp = s₀.sp → s.mem = VG.WriteBytes.writeBytes s₀.mem (State.addr (s₀.gpr .r6)) ((List.range (n - j)).flatMap f) →
      WP isa (.block (((List.range n).drop (n - j)).flatMap fun k =>
        [.ldr .r9 .r0 (4 * k)] ++ (if be then [.rev .r9 .r9] else []) ++ [.str .r9 .r6 (4 * k)]))
        s fun s' => (∀ r, r ≠ .r9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
          s'.sp = s₀.sp ∧ s'.mem = VG.WriteBytes.writeBytes s₀.mem (State.addr (s₀.gpr .r6)) ((List.range n).flatMap f) by
    have := h n (Nat.le_refl _) s₀ (fun _ _ => rfl) rfl rfl rfl
      (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, VG.WriteBytes.writeBytes_nil])
    rwa [Nat.sub_self, List.drop_zero] at this
  intro j
  induction j with
  | zero =>
    intro _ s g rd wr sp m
    rw [Nat.sub_zero, List.drop_of_length_le (by simp), List.flatMap_nil]
    exact WP.block_nil ⟨g, rd, wr, sp, m⟩
  | succ j ih =>
    intro hj s g rd wr sp m
    have hk : n - (j + 1) < n := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_range,
      List.append_assoc, List.append_assoc]
    rw [show n - (j + 1) + 1 = n - j by omega]
    have hoff : 4 * (n - (j + 1)) + 4 ≤ 4 * n := by omega
    have a0 : State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * (n - (j + 1)))) =
        State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1))) := by
      rw [g _ (by decide)]; exact VG.Proof.MdStream.Arm.addr_off (by omega)
    have a6 : ∀ t : State, t.gpr .r6 = s₀.gpr .r6 →
        State.addr (t.gpr .r6 + BitVec.ofNat 32 (4 * (n - (j + 1)))) =
          State.addr (s₀.gpr .r6) + BitVec.ofNat 64 (4 * (n - (j + 1))) :=
      fun t ht => by rw [ht]; exact VG.Proof.MdStream.Arm.addr_off (by omega)
    -- The word read is not yet overwritten.
    have hread : s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32 =
        s₀.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32 := by
      rw [m]
      refine (VG.WriteBytes.writeBytes_frame _ _ _ (R := ⟨State.addr (s₀.gpr .r6), 4 * n⟩) ?_).readW
        (r := ⟨State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1))), 4⟩) (Region.contains_self _ _) ?_
        (by decide)
      · rw [hflat]
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
        omega
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (VG.Proof.MdStream.Arm.sub_offset hoff (by omega))
    have hmem : ∀ (t : State), t.mem = s.mem →
        t.mem.writeW (State.addr (s₀.gpr .r6) + BitVec.ofNat 64 (4 * (n - (j + 1))))
          (if be then rev (s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32)
            else s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32) =
        VG.WriteBytes.writeBytes s₀.mem (State.addr (s₀.gpr .r6)) ((List.range (n - j)).flatMap f) := by
      intro t ht
      rw [ht, VG.Proof.MdStream.Arm.writeW32, hread, m, show n - j = n - (j + 1) + 1 by omega, List.range_succ,
        List.flatMap_append, List.flatMap_singleton,
        ← VG.WriteBytes.writeBytes_append _ _ _ _ (by rw [hflat, bytes32_length]; omega), hflat]
    refine VG.Proof.MdStream.Arm.wp_ldr (a := State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (n - (j + 1)))) (by omega) a0
      (by rw [rd, wr]; exact InRegions.offset hin hoff (by omega)) fun s₁ u₁ => ?_
    cases be
    · simp only [Bool.false_eq_true, ite_false, List.nil_append, List.cons_append]
      refine VG.Proof.MdStream.Arm.wp_str (by omega) (a6 s₁ (by rw [u₁.other _ (by decide), g _ (by decide)]))
        (by rw [u₁.wr, wr]; exact InRegions.offset hout hoff (by omega)) fun s₂ g₂ => ?_
      refine ih (by omega) s₂ (fun r h => by rw [g₂.gpr, u₁.other r h, g r h]) (by rw [g₂.rd, u₁.rd, rd])
        (by rw [g₂.wr, u₁.wr, wr]) (by rw [g₂.sp, u₁.sp, sp]) ?_
      rw [g₂.mem, u₁.gpr]
      exact hmem s₁ u₁.mem
    · simp only [ite_true, List.cons_append, List.nil_append]
      refine VG.Proof.MdStream.Arm.wp_rev fun s₂ u₂ => VG.Proof.MdStream.Arm.wp_str (by omega) (a6 s₂ (by rw [u₂.other _ (by decide),
                                                    u₁.other _ (by decide), g _ (by decide)])) (by rw [u₂.wr, u₁.wr, wr]; exact InRegions.offset hout hoff (by omega))
        fun s₃ g₃ => ?_
      refine ih (by omega) s₃ (fun r h => by rw [g₃.gpr, u₂.other r h, u₁.other r h, g r h])
        (by rw [g₃.rd, u₂.rd, u₁.rd, rd]) (by rw [g₃.wr, u₂.wr, u₁.wr, wr]) (by rw [g₃.sp, u₂.sp, u₁.sp, sp]) ?_
      rw [g₃.mem, u₂.mem, u₂.gpr, u₁.gpr]
      exact hmem s₁ u₁.mem

end VG.Proof.MdStream.Arm

end
