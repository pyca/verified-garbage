module

import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.MdStream.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Streaming Merkle–Damgård hash functions on PPC64LE: basic lemmas

Weakest-precondition rules for the instruction forms the streaming code uses,
and lemmas about addresses, regions, frames and registers saved at offsets:
those of `Common.lean` that need none of Mathlib's algebra, so that code
calling the streaming functions (HMAC's) can use them without importing it.
-/

@[expose] public section

namespace VG.Proof.MdStream.PPC64LE

open VG VG.PPC64LE VG.Impl.MdStream.PPC64LE
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
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.write (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write d v) d v :=
  ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addi {d n : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi hn h) (k _ (Upd.write _ _ _))

theorem wp_mov {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (mov d n :: is)) s Q :=
  wp_addi (by decide) (fun s' u => k s' (by simpa using u)) hn

theorem wp_subi {d n : Reg} {imm : Nat} (h : imm ≤ 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (.subi d n imm :: is)) s Q :=
  WP.cons (exec_subi hn h) (k _ (Upd.write _ _ _))

theorem wp_li {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  WP.cons (exec_li h) (k _ (Upd.write _ _ _))

theorem wp_add {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add d n m :: is)) s Q :=
  WP.cons exec_add (k _ (Upd.write _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub d n m :: is)) s Q :=
  WP.cons exec_sub (k _ (Upd.write _ _ _))

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .d d n sh :: is)) s Q :=
  WP.cons (exec_lsr_d h) (k _ (Upd.write _ _ _))

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl d n sh :: is)) s Q :=
  WP.cons (exec_lsl h) (k _ (Upd.write _ _ _))

theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_lbz hn ho (by rw [ha]; exact hin), ha, read_one]

theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (.stb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_stb hn ho (by rw [ha]; exact hout), ha]
  rfl

theorem wp_std {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

theorem wp_stw {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (.store .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_w hn ho (by rw [ha]; exact hout), ha]

theorem wp_ld {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t (s.mem.readW a 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_d hn ho (by rw [ha]; exact hin), ha]

theorem wp_lwz {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (.load .w t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem.readW a 32).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_w hn ho (by rw [ha]; exact hin), ha]

theorem wp_stwbrx {t n m : Reg} {a : Addr}
    (ha : s.gpr n + s.gpr m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (rev32 ((s.gpr t).setWidth 32))) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (.storeRev .w t n m :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (rev32 ((s.gpr t).setWidth 32)) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_w hn (by rw [ha]; exact hout), ha]

theorem wp_stdbrx {t n m : Reg} {a : Addr}
    (ha : s.gpr n + s.gpr m = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (rev64 (s.gpr t))) → WP isa (.block is) s' Q)
    (hn : n ≠ .r0 := by decide) :
    WP isa (.block (.storeRev .d t n m :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (rev64 (s.gpr t)) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_d hn (by rw [ha]; exact hout), ha]

end

/-! ## Arithmetic -/

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
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

/-- `x >>> n`, of a number below 2⁶⁴. -/
theorem ofNat_shr {a n : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> n = BitVec.ofNat 64 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

/-- `x <<< n`, of a number whose product with `2 ^ n` is below 2⁶⁴. -/
theorem ofNat_shl {a n : Nat} (h : 2 ^ n * a < 2 ^ 64) :
    BitVec.ofNat 64 a <<< n = BitVec.ofNat 64 (2 ^ n * a) := by
  have ha : a ≤ 2 ^ n * a := Nat.le_mul_of_pos_left a (Nat.two_pow_pos n)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mul_comm, Nat.mod_eq_of_lt h]

/-- `x &&& (2 ^ n - 1)`. -/
theorem and_mask {n : Nat} (hn : n ≤ 16) (x : BitVec 64) :
    x &&& BitVec.ofNat 64 (2 ^ n - 1) = BitVec.ofNat 64 (x.toNat % 2 ^ n) := by
  have hp : 2 ^ n ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hn
  have h1 : 1 ≤ 2 ^ n := Nat.two_pow_pos n
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ n - 1 < 2 ^ 64 by omega), Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.mod_lt x.toNat (Nat.two_pow_pos n)
  omega

/-- A 64-bit store is a store of its eight bytes. -/
theorem writeW_eq_writeBytes (m : Mem) (a : Addr) (v : BitVec 64) :
    m.writeW a v = writeBytes m a ((List.range 8).map fun k => v.extractLsb' (8 * k) 8) := by
  show m.write a 8 (v.setWidth 64) = _
  rw [BitVec.setWidth_eq]
  exact WriteBytes.write_eq_writeBytes m a 8 v

/-- Byte `k` of a 64-bit load. -/
theorem extractLsb'_readW (m : Mem) (a : Addr) {k : Nat} (hk : k < 8) :
    (m.readW a 64).extractLsb' (8 * k) 8 = m (a + BitVec.ofNat 64 k) := by
  show ((m.read a 8).setWidth 64).extractLsb' (8 * k) 8 = _
  rw [BitVec.setWidth_eq]
  exact Mem.extractLsb'_read m a hk

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-- `eval` of the branch conditions. -/
theorem eval_zero (s : State) (r : Reg) : eval (.zero .d r) s = some (s.gpr r == 0) := by
  simp [eval, State.read]

theorem eval_nonzero (s : State) (r : Reg) : eval (.nonzero .d r) s = some (s.gpr r != 0) := by
  simp [eval, State.read]

/-! ## Memory and registers -/

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine hf _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, toNat_ofNat_lt (by omega)]
  omega

/-- Registers that no instruction writes keep their values, as a postcondition. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ ∀ r ∈ rs, r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (hn.imp id fun h => h r hr)⟩

/-- The memory a frame's push writes: the back chain and the register. -/
abbrev pushMem (m : Mem) (sp v : BitVec 64) : Mem :=
  (m.write (sp - 48) 8 sp).write (sp - 48 + 32) 8 v

/-- A byte of a region disjoint from a frame is unchanged by the push. -/
theorem write_frame_apply {m : Mem} {sp v : BitVec 64} {R : Region}
    (hd : Region.Disjoint ⟨sp - 48, 48⟩ R) {x : Addr} (hx : R.Contains x 1) :
    pushMem m sp v x = m x := by
  simp only [pushMem]
  rw [Mem.write_apply fun h => hd x (by simp only [Region.Contains] at h ⊢; bv_omega) hx,
    Mem.write_apply fun h => hd x (by simp only [Region.Contains] at h ⊢; omega) hx]

/-- The bytes of a region disjoint from a frame are unchanged by the push. -/
theorem write_frame_bytes {m : Mem} {sp v : BitVec 64} {R : Region}
    (hd : Region.Disjoint ⟨sp - 48, 48⟩ R) (hR : R.len < 2 ^ 64) {i : Nat} (hi : i < R.len) :
    pushMem m sp v (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) :=
  write_frame_apply hd (by
    simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega)

/-- The frame's local variable space is in the frame. -/
theorem frame_sub (sp : Addr) : Region.Sub ⟨sp - 48 + 32, 16⟩ ⟨sp - 48, 48⟩ := by
  intro x h
  simp only [Region.Contains] at h ⊢
  bv_omega

/-! ## Saves at offsets -/

theorem save_sep (b : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) : Mem.Sep (b + BitVec.ofNat 64 d) 8 (b + BitVec.ofNat 64 e) 8 := by
  exact Offset.sep _ h (by omega) (by omega)

theorem readW_writeW_save (m : Mem) (b : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (save_sep b hd he h) (by decide)

/-! Saves at `so + d`, with the conditions on the literal offsets `d`, `e`
alone, which `decide` discharges. -/
theorem readW_writeW_save_so {so : Nat} (hso : so ≤ 1024) (m : Mem) (b : Addr) (v : BitVec 64)
    {d e : Nat} (hd : d ≤ 64) (he : e ≤ 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (b + BitVec.ofNat 64 (so + e)) v).readW (b + BitVec.ofNat 64 (so + d)) 64 =
      m.readW (b + BitVec.ofNat 64 (so + d)) 64 :=
  readW_writeW_save m b v (by omega) (by omega) (by omega)

theorem readW_writeW_save_so_l {so : Nat} (hso : so ≤ 1024) (m : Mem) (b : Addr) (v : BitVec 64)
    {e : Nat} (he : e ≤ 64) (h : 8 ≤ e) :
    (m.writeW (b + BitVec.ofNat 64 (so + e)) v).readW (b + BitVec.ofNat 64 so) 64 =
      m.readW (b + BitVec.ofNat 64 so) 64 :=
  readW_writeW_save m b v (by omega) (by omega) (by omega)

end VG.Proof.MdStream.PPC64LE
