import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.MdStream.AArch64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.AArch64.Common`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on AArch64: common lemmas

The contracts the generic proofs are written against, what they need of a hash
function's parameters (`Shape`) and of its compression function (`CalleeOk`),
the call of the compression function (`compressAt`), saving and restoring the
caller's registers, and weakest-precondition rules for the instruction forms
used (which the proofs of other AArch64 code use too).
-/

namespace VG.Proof.MdStream.AArch64

open VG VG.AArch64 VG.Impl.MdStream.AArch64
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

theorem Upd.write (s : State) (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    VG.Proof.MdStream.AArch64.Upd s (s.write sz d v) d (v.setWidth 64) :=
  ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl, rfl⟩

theorem Upd.write64 (s : State) (d : Reg) (v : BitVec 64) : VG.Proof.MdStream.AArch64.Upd s (s.write .x d v) d v := by
  simpa using Upd.write s .x d v

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

theorem wp_addImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_mov {d n : Reg} (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (mov d n :: is)) s Q :=
  VG.Proof.MdStream.AArch64.wp_addImm (by decide) fun s' u => k s' (by simpa using u)

theorem wp_subImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .x d n imm :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_movz {d : Reg} {imm : BitVec 16}
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' d (imm.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 0 :: is)) s Q :=
  WP.cons (s' := s.write .x d (imm.setWidth 64)) (by simp [exec]) (k _ (Upd.write64 _ _ _))

theorem wp_add {d n m : Reg}
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n + s.gpr m)) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n - s.gpr m)) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_and {d n m : Reg}
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .x d n m :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n &&& s.gpr m)) (by simp [exec, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .x d n sh :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n >>> sh)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.gpr n <<< sh)) (by simp [exec, h, State.read])
    (k _ (Upd.write64 _ _ _))

theorem wp_rev {d n : Reg}
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' d (rev64 (s.gpr n)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev d n :: is)) s Q :=
  WP.cons (s' := s.write .x d (rev64 (s.gpr n))) (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_rev32 {d n : Reg}
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' d ((rev32 ((s.gpr n).setWidth 32)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev32 d n :: is)) s Q :=
  WP.cons rfl (k _ (Upd.write s .w d _))

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (((s.mem a).setWidth 32))) ?_ (k _ ?_)
  · simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
      Option.bind_some, State.load, hin, Option.map_some, VG.Proof.MdStream.AArch64.read_one]
  · have := Upd.write s .w t ((s.mem a).setWidth 32)
    have e : ((s.mem a).setWidth 32).setWidth 64 = (s.mem a).setWidth 64 := by
      ext i hi; simp
    rwa [e] at this

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', VG.Proof.MdStream.AArch64.Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
    Option.bind_some, State.store, hout, Mem.writeW, State.read]
  congr 3
  ext i hi; simp [Size.bits]; try omega

theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', VG.Proof.MdStream.AArch64.Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .x t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_str32 {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', VG.Proof.MdStream.AArch64.Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .x t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .x t (s.mem.readW a 64)) ?_ (k _ (Upd.write64 _ _ _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

theorem wp_ldr32 {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.MdStream.AArch64.Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .w t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (s.mem.readW a 32)) ?_ (k _ (Upd.write s .w t _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

end

/-! ## Arithmetic -/

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, VG.Proof.MdStream.AArch64.ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

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
    x &&& BitVec.setWidth 64 (BitVec.ofNat 16 (2 ^ n - 1)) = BitVec.ofNat 64 (x.toNat % 2 ^ n) := by
  have hp : 2 ^ n ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hn
  have h1 : 1 ≤ 2 ^ n := Nat.two_pow_pos n
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ n - 1 < 2 ^ 16 by omega), Nat.mod_eq_of_lt (show 2 ^ n - 1 < 2 ^ 64 by omega),
    Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.mod_lt x.toNat (Nat.two_pow_pos n)
  omega

/-- A 16-bit immediate, zero-extended. -/
theorem setWidth_ofNat16 {n : Nat} (h : n < 2 ^ 16) :
    BitVec.setWidth 64 (BitVec.ofNat 16 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega)]

/-- A 64-bit store is a store of its eight bytes. -/
theorem writeW_eq_writeBytes (m : Mem) (a : Addr) (v : BitVec 64) :
    m.writeW a v = VG.WriteBytes.writeBytes m a ((List.range 8).map fun k => v.extractLsb' (8 * k) 8) := by
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
theorem eval_zero (s : State) (r : Reg) : eval (.zero .x r) s = some (s.gpr r == 0) := by
  simp [eval, State.read]

theorem eval_nonzero (s : State) (r : Reg) : eval (.nonzero .x r) s = some (s.gpr r != 0) := by
  simp [eval, State.read]

/-! ## Memory and registers -/

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine hf _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [Offset.add_sub_cancel_left, VG.Proof.MdStream.AArch64.toNat_ofNat_lt (by omega)]
  omega

/-- Registers that no instruction writes keep their values, as a postcondition. -/
theorem WP.gprs {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r)
    (hn : c.noCalls = true ∨ ∀ r ∈ rs, r ∉ linkRegs :=
      by first | exact .inr (by decide) | exact .inl (by decide +kernel)) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (hn.imp id fun h => h r hr)⟩

/-- The callee-saved registers our code never touches (but for `x30`, which
our calls change and the frame restores). -/
def untouched : List Reg := [.x25, .x26, .x27, .x28]

/-- A byte of a region disjoint from a frame is unchanged by the push. -/
theorem write_frame_apply {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {R : Region}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ R) {x : Addr} (hx : R.Contains x 1) :
    m.write (sp - 16) 8 v x = m x :=
  Mem.write_apply fun h => hd x (by simp only [Region.Contains]; omega) hx

/-- The bytes of a region disjoint from a frame are unchanged by the push. -/
theorem write_frame_bytes {m : Mem} {sp : Addr} {v : BitVec (8 * 8)} {R : Region}
    (hd : Region.Disjoint ⟨sp - 16, 16⟩ R) (hR : R.len < 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m.write (sp - 16) 8 v (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) :=
  VG.Proof.MdStream.AArch64.write_frame_apply hd (by
    simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega)

/-! ## Sizes -/

/-- The sizes the generic proofs support, checked for each hash function by
`decide`. -/
structure Dims (P : Params) : Prop where
  N : 0 < P.N ∧ P.N ≤ 64
  so : P.so % 8 = 0 ∧ P.so ≤ 1024
  B : P.B = 64 ∨ P.B = 128
  L : 0 < P.L ∧ P.L ≤ 16

theorem Dims.pos {P : Params} (hd : VG.Proof.MdStream.AArch64.Dims P) : 0 < P.B := by rcases hd.B with h | h <;> omega

/-- The shift count of the block size. -/
theorem Dims.log {P : Params} (hd : VG.Proof.MdStream.AArch64.Dims P) :
    1 ≤ Impl.MdStream.AArch64.lg P ∧ Impl.MdStream.AArch64.lg P ≤ 7 ∧ 2 ^ Impl.MdStream.AArch64.lg P = P.B := by
  unfold Impl.MdStream.AArch64.lg
  rcases hd.B with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

/-- `x >>> log₂ B`. -/
theorem Dims.shr {P : Params} (hd : VG.Proof.MdStream.AArch64.Dims P) {a : Nat} (h : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> Impl.MdStream.AArch64.lg P = BitVec.ofNat 64 (a / P.B) := by
  rw [VG.Proof.MdStream.AArch64.ofNat_shr h, hd.log.2.2]

/-- `x <<< log₂ B`. -/
theorem Dims.shl {P : Params} (hd : VG.Proof.MdStream.AArch64.Dims P) {a : Nat} (h : P.B * a < 2 ^ 64) :
    BitVec.ofNat 64 a <<< Impl.MdStream.AArch64.lg P = BitVec.ofNat 64 (P.B * a) := by
  rw [VG.Proof.MdStream.AArch64.ofNat_shl (by rw [hd.log.2.2]; exact h), hd.log.2.2]

/-- `x &&& (B - 1)`. -/
theorem Dims.and {P : Params} (hd : VG.Proof.MdStream.AArch64.Dims P) (x : BitVec 64) :
    x &&& BitVec.setWidth 64 (BitVec.ofNat 16 (P.B - 1)) = BitVec.ofNat 64 (x.toNat % P.B) := by
  have := VG.Proof.MdStream.AArch64.and_mask (n := Impl.MdStream.AArch64.lg P) (by have := hd.log; omega) x
  rwa [hd.log.2.2] at this

/-- `movz` of the block size. -/
theorem Dims.movB {P : Params} (hd : VG.Proof.MdStream.AArch64.Dims P) :
    BitVec.setWidth 64 (BitVec.ofNat 16 P.B) = BitVec.ofNat 64 P.B :=
  VG.Proof.MdStream.AArch64.setWidth_ofNat16 (by rcases hd.B with h | h <;> omega)

theorem Dims.mod {P : Params} (hd : VG.Proof.MdStream.AArch64.Dims P) (n : Nat) : n % 2 ^ 64 % P.B = n % P.B := by
  rcases hd.B with h | h <;> rw [h] <;> omega

/-! ## Saving the caller's registers -/

theorem save_sep (b : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) : Mem.Sep (b + BitVec.ofNat 64 d) 8 (b + BitVec.ofNat 64 e) 8 := by
  exact Offset.sep _ h (by omega) (by omega)

theorem readW_writeW_save (m : Mem) (b : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (VG.Proof.MdStream.AArch64.save_sep b hd he h) (by decide)

/-! Saves at `so + d`, with the conditions on the literal offsets `d`, `e`
alone, which `decide` discharges. -/
theorem readW_writeW_save_so {so : Nat} (hso : so ≤ 1024) (m : Mem) (b : Addr) (v : BitVec 64)
    {d e : Nat} (hd : d ≤ 64) (he : e ≤ 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (b + BitVec.ofNat 64 (so + e)) v).readW (b + BitVec.ofNat 64 (so + d)) 64 =
      m.readW (b + BitVec.ofNat 64 (so + d)) 64 :=
  VG.Proof.MdStream.AArch64.readW_writeW_save m b v (by omega) (by omega) (by omega)

theorem readW_writeW_save_so_l {so : Nat} (hso : so ≤ 1024) (m : Mem) (b : Addr) (v : BitVec 64)
    {e : Nat} (he : e ≤ 64) (h : 8 ≤ e) :
    (m.writeW (b + BitVec.ofNat 64 (so + e)) v).readW (b + BitVec.ofNat 64 so) 64 =
      m.readW (b + BitVec.ofNat 64 so) 64 :=
  VG.Proof.MdStream.AArch64.readW_writeW_save m b v (by omega) (by omega) (by omega)


section
variable (P : Params)

/-- The caller's callee-saved registers `g` are saved in the scratch space at `b`. -/
def Saved (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ p ∈ saved P, m.readW (b + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The memory after saving `x19`–`x24` (values `g`) at `b + so …`. -/
def saveMem (m : Mem) (b : Addr) (g : Reg → BitVec 64) : Mem :=
  (((((m.writeW (b + BitVec.ofNat 64 P.so) (g .x19)).writeW (b + BitVec.ofNat 64 (P.so + 8)) (g .x20)).writeW
    (b + BitVec.ofNat 64 (P.so + 16)) (g .x21)).writeW (b + BitVec.ofNat 64 (P.so + 24)) (g .x22)).writeW
    (b + BitVec.ofNat 64 (P.so + 32)) (g .x23)).writeW (b + BitVec.ofNat 64 (P.so + 40)) (g .x24)

theorem save_eq (b : Reg) : save P b = [.str .x .x19 b P.so, .str .x .x20 b (P.so + 8),
    .str .x .x21 b (P.so + 16), .str .x .x22 b (P.so + 24), .str .x .x23 b (P.so + 32),
    .str .x .x24 b (P.so + 40)] := rfl

end

section
variable {P : Params}

theorem saveMem_saved (hd : VG.Proof.MdStream.AArch64.Dims P) (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    VG.Proof.MdStream.AArch64.Saved P b g (VG.Proof.MdStream.AArch64.saveMem P m b g) := by
  have := hd.so
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [VG.Proof.MdStream.AArch64.saveMem, Mem.readW_writeW_self64,
    VG.Proof.MdStream.AArch64.readW_writeW_save_so this.2, VG.Proof.MdStream.AArch64.readW_writeW_save_so_l this.2]

theorem saveMem_frame (hd : VG.Proof.MdStream.AArch64.Dims P) (m : Mem) (b : Addr) (g : Reg → BitVec 64) :
    Frame [⟨b, P.so + 48⟩] m (VG.Proof.MdStream.AArch64.saveMem P m b g) := by
  have := hd.so
  have c : ∀ d : Nat, d + 8 ≤ P.so + 48 → (⟨b, P.so + 48⟩ : Region).Contains (b + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => VG.Proof.MdStream.AArch64.contains_offset hd (by omega)
  simp only [VG.Proof.MdStream.AArch64.saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega))).writeW (List.mem_singleton_self _) _
    (c _ (by omega))).writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c _ (by omega))

/-- The saved registers are outside the part of the scratch space the
compression function uses. -/
theorem saved_offset (hd : VG.Proof.MdStream.AArch64.Dims P) {p : Reg × Nat} (hp : p ∈ saved P) : P.so ≤ p.2 ∧ p.2 + 8 ≤ P.so + 48 := by
  have := hd.so
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- Saving `x19`–`x24` with the scratch pointer in `b`. -/
theorem save_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hin : ∀ d, P.so ≤ d → d + 8 ≤ P.so + 48 → InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = VG.Proof.MdStream.AArch64.saveMem P s.mem (s.gpr b) s.gpr → WP isa (.block rest) s' Q) :
    WP isa (.block (save P b ++ rest)) s Q := by
  have := hd.so
  rw [VG.Proof.MdStream.AArch64.save_eq]
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.MdStream.AArch64.wp_str (by omega) rfl (hin _ (by omega) (by omega)) fun s₁ g₁ => ?_
  refine VG.Proof.MdStream.AArch64.wp_str (by omega) (by rw [g₁.gpr]) (by rw [g₁.wr]; exact hin _ (by omega) (by omega))
    fun s₂ g₂ => ?_
  refine VG.Proof.MdStream.AArch64.wp_str (by omega) (by rw [g₂.gpr, g₁.gpr])
    (by rw [g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) fun s₃ g₃ => ?_
  refine VG.Proof.MdStream.AArch64.wp_str (by omega) (by rw [g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) fun s₄ g₄ => ?_
  refine VG.Proof.MdStream.AArch64.wp_str (by omega) (by rw [g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) fun s₅ g₅ => ?_
  refine VG.Proof.MdStream.AArch64.wp_str (by omega) (by rw [g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr]; exact hin _ (by omega) (by omega)) fun s₆ g₆ => ?_
  refine k s₆ (by rw [g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr])
    (by rw [g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd]) (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr])
    (by rw [g₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, g₁.sp]) ?_
  rw [g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem]
  simp only [VG.Proof.MdStream.AArch64.saveMem, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr]

/-- Restoring `x19`–`x24` from the save area at `scr`. -/
theorem restore_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s : State} {scr : Addr} (h20 : s.gpr .x20 = scr)
    (hin : ∀ d, P.so ≤ d → d + 8 ≤ P.so + 48 → InRegions (s.rd ++ s.wr) (scr + BitVec.ofNat 64 d) 8)
    (g : Reg → BitVec 64) (hsv : VG.Proof.MdStream.AArch64.Saved P scr g s.mem) {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved P, s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ (saved P).map Prod.fst → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block (restore P)) s Q := by
  have := hd.so
  have v : ∀ r d, (r, d) ∈ saved P → s.mem.readW (scr + BitVec.ofNat 64 d) 64 = g r :=
    fun r d h => hsv (r, d) h
  unfold restore
  refine VG.Proof.MdStream.AArch64.wp_ldr (by omega) (by rw [h20]) (hin _ (by omega) (by omega)) fun s₁ u₁ => ?_
  refine VG.Proof.MdStream.AArch64.wp_ldr (by omega) (by rw [u₁.other _ (by decide), h20])
    (by rw [u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega)) fun s₂ u₂ => ?_
  refine VG.Proof.MdStream.AArch64.wp_ldr (by omega) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h20])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega)) fun s₃ u₃ => ?_
  refine VG.Proof.MdStream.AArch64.wp_ldr (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h20])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine VG.Proof.MdStream.AArch64.wp_ldr (by omega)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h20])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin _ (by omega) (by omega))
    fun s₅ u₅ => ?_
  refine VG.Proof.MdStream.AArch64.wp_ldr (by omega)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h20])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin _ (by omega) (by omega))
    fun s₆ u₆ => WP.block_nil ?_
  have m5 : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine k s₆ (fun p hp => ?_) (fun r hr => ?_) (by rw [u₆.mem, m5]) (by rw [u₆.rd, u₅.rd, u₄.rd,
    u₃.rd, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp])
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, v .x19 _ (by simp [saved])]
    · rw [u₆.gpr, m5, v .x20 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.mem, v .x21 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem,
        v .x22 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem,
        v .x23 _ (by simp [saved])]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, v .x24 _ (by simp [saved])]
  · simp only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₆.other _ h2, u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, u₂.other _ h3, u₁.other _ h1]

/-- The callee-saved registers but `x30` are the caller's again once `restore`
has run and `untouched` were never written. -/
theorem preserved_of {s₀ s' : State} (hsv : ∀ p ∈ saved P, s'.gpr p.1 = s₀.gpr p.1)
    (hu : ∀ r ∈ VG.Proof.MdStream.AArch64.untouched, s'.gpr r = s₀.gpr r) : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r := by
  intro r hr h30
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsv (.x19, P.so) (by simp [saved])
  · exact hsv (.x20, P.so + 8) (by simp [saved])
  · exact hsv (.x21, P.so + 16) (by simp [saved])
  · exact hsv (.x22, P.so + 24) (by simp [saved])
  · exact hsv (.x23, P.so + 32) (by simp [saved])
  · exact hsv (.x24, P.so + 40) (by simp [saved])
  all_goals first | exact absurd rfl h30 | exact hu _ (by simp [VG.Proof.MdStream.AArch64.untouched])

end

/-! ## Storing a word in the buffer -/

/-- `storeWord` stores `x9` at `x19 + x23 + N`, writing only `x12`. -/
theorem storeWord_ok {P : Params} (hN : P.N < 4096) {rest : List Instr} {s : State} {Q : State → Prop}
    {a : Addr} (ha : s.gpr .x19 + s.gpr .x23 + BitVec.ofNat 64 P.N = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', (∀ r, r ≠ .x12 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = s.mem.writeW a (s.gpr .x9) → WP isa (.block rest) s' Q) :
    WP isa (.block (storeWord P ++ rest)) s Q := by
  unfold storeWord
  split
  · rename_i h8
    simp only [List.cons_append, List.nil_append]
    refine VG.Proof.MdStream.AArch64.wp_add fun s₁ u₁ => VG.Proof.MdStream.AArch64.wp_str (a := a) ⟨h8, by omega⟩ (by rw [u₁.gpr]; exact ha) (by rw [u₁.wr]; exact hout)
      fun s₂ g₂ => k s₂ (fun r hr => by rw [g₂.gpr, u₁.other r hr]) (by rw [g₂.rd, u₁.rd])
        (by rw [g₂.wr, u₁.wr]) (by rw [g₂.sp, u₁.sp]) (by rw [g₂.mem, u₁.mem, u₁.other _ (by decide)])
  · simp only [List.cons_append, List.nil_append]
    refine VG.Proof.MdStream.AArch64.wp_add fun s₁ u₁ => VG.Proof.MdStream.AArch64.wp_addImm hN fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_str (a := a) ⟨by decide, by decide⟩
      (by rw [u₂.gpr, u₁.gpr]; exact (BitVec.add_zero _).trans ha) (by rw [u₂.wr, u₁.wr]; exact hout)
      fun s₃ g₃ => k s₃ (fun r hr => by rw [g₃.gpr, u₂.other r hr, u₁.other r hr])
        (by rw [g₃.rd, u₂.rd, u₁.rd]) (by rw [g₃.wr, u₂.wr, u₁.wr]) (by rw [g₃.sp, u₂.sp, u₁.sp])
        (by rw [g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.other _ (by decide)])

/-! ## The contracts

The generic proofs are written against these; each hash function's own
contracts are these for its instance. -/

section
variable {P : Params} (H : Md P.B P.N P.L)

/-- The contract of the compression function: updates the hash value at
`x0` with the `x2` blocks at `x1`, with scratch space `x3` (`so` bytes). -/
def compressK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, P.N⟩
    let blocks : Region := ⟨s.gpr .x1, P.B * (s.gpr .x2).toNat⟩
    let scratch : Region := ⟨s.gpr .x3, P.so⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch
  post s s' :=
    H.stateAt s'.mem (s.gpr .x0) =
      H.compressBlocks (H.stateAt s.mem (s.gpr .x0)) s.mem (s.gpr .x1) (s.gpr .x2).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- The contract of `update`: if the state at `x0` represents a message of
`x1` bytes (modulo 2⁶⁴) from any initial hash value, it then represents that
message followed by the `x3` bytes at `x2`. -/
def updK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, P.N + P.B⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, P.so + 48⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, H.Repr iv s.mem (s.gpr .x0) m → s.gpr .x1 = BitVec.ofNat 64 m.length →
    H.Repr iv s'.mem (s.gpr .x0) (m ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- The contract of `finalize`: if the state at `x0` represents a message of
`x1` bytes, writes its final hash value to `x2` (`N` bytes). -/
def finK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, P.N + P.B⟩
    let out : Region := ⟨s.gpr .x2, P.N⟩
    let scratch : Region := ⟨s.gpr .x3, P.so + 48⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, H.Repr iv s.mem (s.gpr .x0) m → H.lenOk m.length →
    s.gpr .x1 = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .x2) P.N = H.hash iv m
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end

/-! ## What each hash function's own code must do -/

/-- The length field and the digest: `P.len` stores the length field for the
byte count in `x22` at `x19 + N + B - L`, writing only `x9` and `x12`, and
`P.out` writes the digest of the hash value at `x19` to `x21`, writing only
`x9`. -/
structure Shape {P : Params} (H : Md P.B P.N P.L) : Prop where
  lenKeepsV : P.len.all VG.AArch64.keepsV = true
  outKeepsV : P.out.all VG.AArch64.keepsV = true
  len : ∀ s : State, InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L →
    WP isa (.block P.len) s fun s' => (∀ r, r ≠ .x9 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .x19 + BitVec.ofNat 64 (P.N + P.B - P.L)) (H.lenOf (s.gpr .x22))
  out : ∀ s : State, InRegions (s.rd ++ s.wr) (s.gpr .x19) P.N → InRegions s.wr (s.gpr .x21) P.N →
    Region.Disjoint ⟨s.gpr .x19, P.N⟩ ⟨s.gpr .x21, P.N⟩ →
    WP isa (.block P.out) s fun s' => (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .x21) (H.digest (H.stateAt s.mem (s.gpr .x19)))

/-- What `compressAt` needs of the compression function it calls: that it is
correct, and pushes no frames. -/
structure CalleeOk {P : Params} (H : Md P.B P.N P.L) (code : Prog isa) : Prop where
  verified : ∀ s, (VG.Proof.MdStream.AArch64.compressK H).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MdStream.AArch64.compressK H).post s s'
  noFrames : code.noFrames = true
  keepsV : code.allInstrs VG.AArch64.keepsV = true

theorem storeWord_keepsV (P : Params) : (storeWord P).all VG.AArch64.keepsV = true := by
  unfold storeWord; split <;> rfl

/-- The stream wrapper itself writes no vector registers. -/
theorem update_keepsV {P : Params} {name : String} {code : Prog isa}
    (h : code.allInstrs VG.AArch64.keepsV = true) :
    (update P name code).allInstrs VG.AArch64.keepsV = true := by
  have hw := List.all_eq_true.mp (VG.Proof.MdStream.AArch64.storeWord_keepsV P)
  rw [Code.allInstrs_eq] at h ⊢
  have hc := List.all_eq_true.mp h
  simp [update, updateMain, updateStart, updateBody, fill, copy, copyWordBody, copyBody, direct,
    compressN, compressWith, save, saved, restore, instrs, lg, mov, VG.AArch64.keepsV, vdstOf]
  exact ⟨fun x hx => hw x hx, fun x hx => hc x hx⟩

/-- The finalizer adds only the parameterized length and digest stores. -/
theorem finalize_keepsV {P : Params} {H : Md P.B P.N P.L} {name : String} {code : Prog isa}
    (hs : VG.Proof.MdStream.AArch64.Shape H) (h : code.allInstrs VG.AArch64.keepsV = true) :
    (finalize P name code).allInstrs VG.AArch64.keepsV = true := by
  have hw := List.all_eq_true.mp (VG.Proof.MdStream.AArch64.storeWord_keepsV P)
  rw [Code.allInstrs_eq] at h ⊢
  simp [finalize, finalizeMain, finalizeStart, finalizeBody, zero, zeroWordBody, zeroBody,
    compressAt, compressWith, save, saved, restore, mov, instrs, lg,
    VG.AArch64.keepsV, vdstOf, h, hs.lenKeepsV, hs.outKeepsV]
  exact fun x hx => hw x hx

/-! ## The compression function -/

theorem one_toNat : (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 1 := rfl

/-- `n` sets `x2` to `v`, given that only `x0` changed since the state `s`. -/
def SetsN (n : Instr) (s : State) (v : BitVec 64) : Prop :=
  ∀ (s₁ : State) (is : List Instr) (Q : State → Prop), (∀ r, r ≠ .x0 → s₁.gpr r = s.gpr r) →
    (∀ s', VG.Proof.MdStream.AArch64.Upd s₁ s' .x2 v → WP isa (.block is) s' Q) → WP isa (.block (n :: is)) s₁ Q

theorem setsN_one (s : State) : VG.Proof.MdStream.AArch64.SetsN (.movz .x .x2 1 0) s (BitVec.setWidth 64 (1 : BitVec 16)) :=
  fun _ _ _ _ k => VG.Proof.MdStream.AArch64.wp_movz k

theorem setsN_x10 (s : State) : VG.Proof.MdStream.AArch64.SetsN (mov .x2 .x10) s (s.gpr .x10) :=
  fun _ _ _ he k => VG.Proof.MdStream.AArch64.wp_mov fun s' u => k s' (by rwa [he _ (by decide)] at u)

/-- Compressing the `k` blocks at `x1` (their number set in `x2` by `n`) into
the hash value at `x19`, with scratch space at `x20`: the callee-saved
registers other than `x30` are kept. -/
theorem compressWith_ok {P : Params} {H : Md P.B P.N P.L} {n : Instr} {s : State} {v : BitVec 64}
    (hn : VG.Proof.MdStream.AArch64.SetsN n s v) {k : Nat} (hk : v.toNat = k) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.AArch64.CalleeOk H code)
    {st scr src : Addr}
    (h19 : s.gpr .x19 = st) (h20 : s.gpr .x20 = scr) (h1 : s.gpr .x1 = src)
    (d₁ : Region.Disjoint ⟨st, P.N⟩ ⟨scr, P.so⟩) (d₂ : Region.Disjoint ⟨src, P.B * k⟩ ⟨st, P.N⟩)
    (d₃ : Region.Disjoint ⟨src, P.B * k⟩ ⟨scr, P.so⟩)
    (hc : Covers [⟨src, P.B * k⟩, ⟨st, P.N⟩, ⟨scr, P.so⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, P.N⟩, ⟨scr, P.so⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, P.N⟩, ⟨scr, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem st = H.compressBlocks (H.stateAt s.mem st) s.mem src k → Q s') :
    WP isa (compressWith n name code) s Q := by
  unfold compressWith
  refine WP.seq (VG.Proof.MdStream.AArch64.wp_mov fun s₁ u₁ => hn s₁ _ _ u₁.other fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_mov fun s₃ u₃ => WP.block_nil ?_)
  have e0 : s₃.gpr .x0 = st := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h19]
  have e1 : s₃.gpr .x1 = src := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h1]
  have e2 : s₃.gpr .x2 = v := by
    rw [u₃.other _ (by decide), u₂.gpr]
  have e3 : s₃.gpr .x3 = scr := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h20]
  have keep : ∀ r ∈ preserved, s₃.gpr r = s.gpr r := by
    intro r hr
    have : r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    rw [u₃.other _ this.2.2, u₂.other _ this.2.1, u₁.other _ this.1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  have c0 : s₃.callEntry.gpr .x0 = st := (State.callEntry_gpr _ (by decide)).trans e0
  have c1 : s₃.callEntry.gpr .x1 = src := (State.callEntry_gpr _ (by decide)).trans e1
  have c2 : s₃.callEntry.gpr .x2 = v := (State.callEntry_gpr _ (by decide)).trans e2
  have c3 : s₃.callEntry.gpr .x3 = scr := (State.callEntry_gpr _ (by decide)).trans e3
  refine WP.call (k := VG.Proof.MdStream.AArch64.compressK H) hf.verified
    (rd := [⟨src, P.B * k⟩]) (wr := [⟨st, P.N⟩, ⟨scr, P.so⟩]) ?_ ?_ ?_ ?_ hf.noFrames
  · simp only [VG.Proof.MdStream.AArch64.compressK, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1, c2, c3, hk]
    exact ⟨trivial, trivial, d₁, d₂, d₃⟩
  · rw [rd₃, wr₃]; simpa using hc
  · rw [wr₃]; exact hw
  · intro s' hrd hwr hsp hf' hcs _ hpost
    simp only [VG.Proof.MdStream.AArch64.compressK, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, hk, m₃] at hpost
    exact hQ s' (hrd.trans rd₃) (hwr.trans wr₃) (fun r hr h30 => (hcs r hr h30).trans (keep r hr))
      (hsp.trans sp₃) (m₃ ▸ hf') hpost

/-- Compressing the block at `x1` into the hash value at `x19`, with scratch
space at `x20`: the callee-saved registers other than `x30` are kept. -/
theorem compressAt_ok {P : Params} {H : Md P.B P.N P.L} {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.AArch64.CalleeOk H code)
    {s : State} {st scr src : Addr}
    (h19 : s.gpr .x19 = st) (h20 : s.gpr .x20 = scr) (h1 : s.gpr .x1 = src)
    (d₁ : Region.Disjoint ⟨st, P.N⟩ ⟨scr, P.so⟩) (d₂ : Region.Disjoint ⟨src, P.B⟩ ⟨st, P.N⟩)
    (d₃ : Region.Disjoint ⟨src, P.B⟩ ⟨scr, P.so⟩)
    (hc : Covers [⟨src, P.B⟩, ⟨st, P.N⟩, ⟨scr, P.so⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, P.N⟩, ⟨scr, P.so⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      s'.sp = s.sp → Frame [⟨st, P.N⟩, ⟨scr, P.so⟩] s.mem s'.mem →
      H.stateAt s'.mem st = H.compress (H.stateAt s.mem st) (H.blockAt s.mem src) → Q s') :
    WP isa (compressAt name code) s Q :=
  VG.Proof.MdStream.AArch64.compressWith_ok (VG.Proof.MdStream.AArch64.setsN_one s) VG.Proof.MdStream.AArch64.one_toNat hf h19 h20 h1 d₁ (by rwa [Nat.mul_one]) (by rwa [Nat.mul_one])
    (by rwa [Nat.mul_one]) hw
    fun s' hrd hwr hcs hsp hf' hs => hQ s' hrd hwr hcs hsp hf' (by rw [hs, Md.compressBlocks_one])

end VG.Proof.MdStream.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.AArch64.Finalize`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on AArch64: `finalize`

The functional correctness of `finalize`, for any hash function (`Md`) whose
code stores the length field and writes the digest as `Shape` says, and any
correct compression function (`CalleeOk`). The same structure as the x86-64
proof (`VG.Proof.MdStream.X86_64.Finalize`). Constant time is proven for each
hash function's code by the taint analysis, calls included.
-/

namespace VG.Proof.MdStream.AArch64.Finalize

open VG VG.AArch64 VG.Impl.MdStream.AArch64
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame bytesAt_congr)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev cnt : Nat := (s₀.gpr .x1).toNat
abbrev out : Addr := s₀.gpr .x2
abbrev scr : Addr := s₀.gpr .x3
abbrev stR : Region := ⟨VG.Proof.MdStream.AArch64.Finalize.st s₀, P.N + P.B⟩
abbrev outR : Region := ⟨VG.Proof.MdStream.AArch64.Finalize.out s₀, P.N⟩
abbrev scR : Region := ⟨VG.Proof.MdStream.AArch64.Finalize.scr s₀, P.so + 48⟩
/-- The buffer. -/
abbrev buf : Addr := VG.Proof.MdStream.AArch64.Finalize.st s₀ + BitVec.ofNat 64 P.N

/-- The end of the zeros in a block: before the length field in the last
block (`k = 0`). -/
def lim (k : Nat) : Nat := if k = 0 then P.B - P.L else P.B

end

section
variable {P : Params} (H : Md P.B P.N P.L) (s₀ : State)

/-- The messages the initial state represents, from `iv`. -/
def R₀ (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀) m ∧ s₀.gpr .x1 = BitVec.ofNat 64 m.length

/-- The final hash value, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.compress (H.stateAt mem (VG.Proof.MdStream.AArch64.Finalize.st s₀))
    (H.parse fun t => (bytesAt mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀) n ++ List.replicate (P.B - n) 0).getD t 0))
    (H.parse fun t => (List.replicate (P.B - P.L) 0 ++ H.lenBytes m.length).getD t 0)

/-- The final hash value, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.stateAt mem (VG.Proof.MdStream.AArch64.Finalize.st s₀))
    (H.parse fun t => (bytesAt mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀) n ++ List.replicate (P.B - P.L - n) 0 ++
      H.lenBytes m.length).getD t 0)

end

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.MdStream.AArch64.Finalize.stR P s₀, VG.Proof.MdStream.AArch64.Finalize.outR P s₀, VG.Proof.MdStream.AArch64.Finalize.scR P s₀]
  st_out : (VG.Proof.MdStream.AArch64.Finalize.stR P s₀).Disjoint (VG.Proof.MdStream.AArch64.Finalize.outR P s₀)
  st_scr : (VG.Proof.MdStream.AArch64.Finalize.stR P s₀).Disjoint (VG.Proof.MdStream.AArch64.Finalize.scR P s₀)
  out_scr : (VG.Proof.MdStream.AArch64.Finalize.outR P s₀).Disjoint (VG.Proof.MdStream.AArch64.Finalize.scR P s₀)

/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR (s₀ : State) : Region := ⟨s₀.sp - 16, 16⟩

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (P : Params) (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (VG.Proof.MdStream.AArch64.Finalize.stkR s₀).Disjoint (VG.Proof.MdStream.AArch64.Finalize.stR P s₀)
  out : (VG.Proof.MdStream.AArch64.Finalize.stkR s₀).Disjoint (VG.Proof.MdStream.AArch64.Finalize.outR P s₀)
  scr : (VG.Proof.MdStream.AArch64.Finalize.stkR s₀).Disjoint (VG.Proof.MdStream.AArch64.Finalize.scR P s₀)

theorem pre_of {P : Params} {H : Md P.B P.N P.L} {s₀ : State} (h : (VG.Proof.MdStream.AArch64.finK H).pre s₀) : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀ ∧ VG.Proof.MdStream.AArch64.Finalize.Stack P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

/-! ## Invariants -/

structure Common (P : Params) (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = VG.Proof.MdStream.AArch64.Finalize.st s₀
  x20 : s.gpr .x20 = VG.Proof.MdStream.AArch64.Finalize.scr s₀
  x21 : s.gpr .x21 = VG.Proof.MdStream.AArch64.Finalize.out s₀
  x22 : s.gpr .x22 = s₀.gpr .x1
  sp : s.sp = s₀.sp
  frame : Frame [VG.Proof.MdStream.AArch64.Finalize.stR P s₀, VG.Proof.MdStream.AArch64.Finalize.scR P s₀] s₀.mem s.mem
  saved : VG.Proof.MdStream.AArch64.Saved P (VG.Proof.MdStream.AArch64.Finalize.scr s₀) s₀.gpr s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (k n : Nat) (s : State) : Prop
    extends VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ VG.Proof.MdStream.AArch64.Finalize.lim P k
  x23 : s.gpr .x23 = BitVec.ofNat 64 n
  x24 : s.gpr .x24 = BitVec.ofNat 64 k
  hash : ∀ iv m, VG.Proof.MdStream.AArch64.Finalize.R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m =
    H.digest (if k = 1 then VG.Proof.MdStream.AArch64.Finalize.Fin1 H s₀ s.mem n m else VG.Proof.MdStream.AArch64.Finalize.Fin0 H s₀ s.mem n m)

/-- All blocks are compressed. -/
def Done {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s ∧ ∀ iv m, VG.Proof.MdStream.AArch64.Finalize.R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m = H.digest (H.stateAt s.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀))

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem R₀.length (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} {iv : H.HV} {m : List Byte} (h : VG.Proof.MdStream.AArch64.Finalize.R₀ H s₀ iv m) :
    VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B = m.length % P.B := by
  rw [VG.Proof.MdStream.AArch64.Finalize.cnt, h.2, BitVec.toNat_ofNat, hd.mod]

theorem lim_le (k : Nat) : VG.Proof.MdStream.AArch64.Finalize.lim P k ≤ P.B := by unfold VG.Proof.MdStream.AArch64.Finalize.lim; split <;> omega
theorem lim_ge (k : Nat) : P.B - P.L ≤ VG.Proof.MdStream.AArch64.Finalize.lim P k := by unfold VG.Proof.MdStream.AArch64.Finalize.lim; split <;> omega

theorem buf_add (s₀ : State) (n : Nat) : VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 n = VG.Proof.MdStream.AArch64.Finalize.st s₀ + BitVec.ofNat 64 (P.N + n) :=
  VG.Proof.MdStream.AArch64.add_ofNat _ _ _

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x22], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := by rw [hg _ (by simp)]; exact h.x19
  x20 := by rw [hg _ (by simp)]; exact h.x20
  x21 := by rw [hg _ (by simp)]; exact h.x21
  x22 := by rw [hg _ (by simp)]; exact h.x22
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- Where the caller's registers are saved. -/
theorem saved_sub (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved P) :
    Region.Sub ⟨VG.Proof.MdStream.AArch64.Finalize.scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (VG.Proof.MdStream.AArch64.Finalize.scR P s₀) := by
  have := VG.Proof.MdStream.AArch64.saved_offset hd hp; have := hd.so
  exact VG.Proof.MdStream.AArch64.sub_offset (by omega) (by omega)

/-- Writing buffer bytes `[n, n + |xs|)` keeps `Common`'s memory facts. -/
theorem Common.writeBuf (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀) {s : State} (h : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ P.B) :
    Frame [VG.Proof.MdStream.AArch64.Finalize.stR P s₀] s.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      Frame [VG.Proof.MdStream.AArch64.Finalize.stR P s₀, VG.Proof.MdStream.AArch64.Finalize.scR P s₀] s₀.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      VG.Proof.MdStream.AArch64.Saved P (VG.Proof.MdStream.AArch64.Finalize.scr s₀) s₀.gpr (VG.WriteBytes.writeBytes s.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) := by
  have := hd.N; have := hd.B
  have hf : Frame [VG.Proof.MdStream.AArch64.Finalize.stR P s₀] s.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) := by
    refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
    rw [VG.Proof.MdStream.AArch64.Finalize.buf_add]
    exact VG.Proof.MdStream.AArch64.contains_offset (by omega) (by omega)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  refine hf.readW (r := ⟨VG.Proof.MdStream.AArch64.Finalize.scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (VG.Proof.MdStream.AArch64.Finalize.saved_sub hd hp')

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (P : Params) (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x24], s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  x9 : s.gpr .x9 = 0
  x23 : s.gpr .x23 = BitVec.ofNat 64 (n + j)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (lim - n - j)
  mem : s.mem = VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀) {sI : State} (hC : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ sI)
    {n lim j : Nat} (hlim : lim ≤ P.B) (hj : j < lim - n) {s : State} (h : VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim j s) :
    WP isa (.block (zeroBody P)) s fun s' =>
      VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim (j + 1) s' ∧ s'.gpr .x11 = BitVec.ofNat 64 (lim - n - (j + 1)) := by
  have := hd.N; have := hd.B
  have hx19 : s.gpr .x19 = VG.Proof.MdStream.AArch64.Finalize.st s₀ := by rw [h.keep _ (by simp), hC.x19]
  have hout : InRegions s.wr (VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨VG.Proof.MdStream.AArch64.Finalize.stR P s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [VG.Proof.MdStream.AArch64.add_ofNat, VG.Proof.MdStream.AArch64.Finalize.buf_add]
    exact VG.Proof.MdStream.AArch64.contains_offset (by omega) (by omega)
  unfold zeroBody
  refine VG.Proof.MdStream.AArch64.wp_add fun s₁ u₁ => VG.Proof.MdStream.AArch64.wp_strb (a := VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) (by omega)
    ?_ (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hx19, h.x23, VG.Proof.MdStream.AArch64.Finalize.buf, BitVec.ofNat_add]
    ac_rfl
  refine VG.Proof.MdStream.AArch64.wp_addImm (by omega) fun s₃ u₃ => VG.Proof.MdStream.AArch64.wp_subImm (by omega) fun s₄ u₄ => WP.block_nil ⟨⟨by omega,
    fun r hr => ?_, by rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd], by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr],
    by rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp], ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .x11 ∧ r ≠ .x23 ∧ r ≠ .x12 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other r this.1, u₃.other r this.2.1, g₂.gpr, u₁.other r this.2.2, h.keep r hr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x9]
  · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x23, ← BitVec.ofNat_add,
      Nat.add_assoc]
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x11,
      VG.Proof.MdStream.AArch64.sub_ofNat (by omega), Nat.sub_sub]
  · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide), h.x9, h.mem, List.replicate_succ',
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x11,
      VG.Proof.MdStream.AArch64.sub_ofNat (by omega), Nat.sub_sub, Nat.sub_sub]

theorem zero_loop_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀) {sI : State} (hC : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ sI)
    {n lim j₀ : Nat} (hlim : lim ≤ P.B) (hj : j₀ < lim - n) {s : State} (h : VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim j₀ s) :
    WP isa (.loop (.block (zeroBody P)) (.nonzero .x .x11)) s (VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim (lim - n)) := by
  have := hd.B
  refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim j s)
    ?_ (lim - n - j₀) s ⟨j₀, rfl, hj, h⟩
  rintro k s ⟨j, rfl, hj, hZ⟩
  refine WP.mono (VG.Proof.MdStream.AArch64.Finalize.zero_step hd hp hC hlim hj hZ) fun s' ⟨hZ', h11⟩ => ?_
  have hz' : isa.eval (.nonzero .x .x11) s' = some (decide (lim - n - (j + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x11) s' = _
    rw [VG.Proof.MdStream.AArch64.eval_nonzero, h11, bne, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by omega)]
    simp
  by_cases hl : lim - n - (j + 1) = 0
  · refine .inl ⟨by rw [hz']; simp [hl], ?_⟩
    rwa [show j + 1 = lim - n by omega] at hZ'
  · exact .inr ⟨by rw [hz']; simp [hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

theorem Zero.of_gpr {s₀ sI : State} {n lim j : Nat} {s s' : State} (h : VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim j s)
    (hg : ∀ r, r ≠ .x13 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim j s' :=
  ⟨h.j_le, fun r hr => by
      have : r ≠ .x13 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hg r this, h.keep r hr],
    hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, by rw [hg _ (by decide), h.x9],
    by rw [hg _ (by decide), h.x23], by rw [hg _ (by decide), h.x11], by rw [hm, h.mem]⟩

theorem zero_word_step (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀) {sI : State} (hC : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ sI)
    {n lim j : Nat} (hlim : lim ≤ P.B) (hj : j + 8 ≤ lim - n) {s : State} (h : VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim j s) :
    WP isa (.block (zeroWordBody P)) s fun s' =>
      VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim (j + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((lim - n - (j + 8)) / 8) := by
  have := hd.N; have := hd.B
  have hx19 : s.gpr .x19 = VG.Proof.MdStream.AArch64.Finalize.st s₀ := by rw [h.keep _ (by simp), hC.x19]
  have hout : InRegions s.wr (VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 8 := by
    refine ⟨VG.Proof.MdStream.AArch64.Finalize.stR P s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [VG.Proof.MdStream.AArch64.add_ofNat, VG.Proof.MdStream.AArch64.Finalize.buf_add]
    exact VG.Proof.MdStream.AArch64.contains_offset (by omega) (by omega)
  unfold zeroWordBody
  refine VG.Proof.MdStream.AArch64.storeWord_ok (by omega) (a := VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) ?_ hout
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  · rw [hx19, h.x23, VG.Proof.MdStream.AArch64.Finalize.buf, BitVec.ofNat_add]
    ac_rfl
  refine VG.Proof.MdStream.AArch64.wp_addImm (by decide) fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_subImm (by decide) fun s₃ u₃ =>
    VG.Proof.MdStream.AArch64.wp_lsr (by decide) fun s₄ u₄ => WP.block_nil ?_
  have hx11₃ : s₃.gpr .x11 = BitVec.ofNat 64 (lim - n - (j + 8)) := by
    rw [u₃.gpr, u₂.other _ (by decide), g₁ _ (by decide), h.x11, VG.Proof.MdStream.AArch64.sub_ofNat (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, fun r hr => ?_, by rw [u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd],
    by rw [u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr], by rw [u₄.sp, u₃.sp, u₂.sp, sp₁, h.sp], ?_, ?_,
    by rw [u₄.other _ (by decide), hx11₃], ?_⟩, by rw [u₄.gpr, hx11₃, VG.Proof.MdStream.AArch64.ofNat_shr (by omega)]⟩
  · have : r ≠ .x13 ∧ r ≠ .x11 ∧ r ≠ .x23 ∧ r ≠ .x12 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other r this.1, u₃.other r this.2.1, u₂.other r this.2.2.1, g₁ r this.2.2.2, h.keep r hr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), h.x9]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁ _ (by decide), h.x23,
      ← BitVec.ofNat_add, Nat.add_assoc]
  · have hw : (List.range 8).map (fun k => (s.gpr .x9).extractLsb' (8 * k) 8) = List.replicate 8 0 := by
      rw [h.x9]; decide
    rw [u₄.mem, u₃.mem, u₂.mem, m₁, VG.Proof.MdStream.AArch64.writeW_eq_writeBytes, hw, h.mem, ← List.replicate_append_replicate,
      ← VG.WriteBytes.writeBytes_append _ _ _ _ (by simp only [List.length_replicate]; omega),
      List.length_replicate]

theorem zero_words_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀) {sI : State} (hC : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ sI)
    {n lim : Nat} (hlim : lim ≤ P.B) (hn : n ≤ lim) {s : State} (h : VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim 0 s)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 ((lim - n) / 8)) :
    WP isa (.ite (.zero .x .x13) (.block []) (.loop (.block (zeroWordBody P)) (.nonzero .x .x13))) s
      (VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim (8 * ((lim - n) / 8))) := by
  have := hd.B
  have hz : eval (.zero .x .x13) s = some (decide ((lim - n) / 8 = 0)) := by
    rw [VG.Proof.MdStream.AArch64.eval_zero, h13, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by omega)]
  refine WP.ite (decide ((lim - n) / 8 = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (by rw [hb]; exact h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa)
      (fun k s => ∃ i, k = (lim - n) / 8 - i ∧ i < (lim - n) / 8 ∧ VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim (8 * i) s)
      ?_ ((lim - n) / 8) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨i, rfl, hi, hZ⟩
    refine WP.mono (VG.Proof.MdStream.AArch64.Finalize.zero_word_step hd hp hC hlim (by omega) hZ) fun s' ⟨hZ', h13'⟩ => ?_
    have hz' : isa.eval (.nonzero .x .x13) s' = some (decide ((lim - n) / 8 - (i + 1) ≠ 0)) := by
      show VG.AArch64.eval (.nonzero .x .x13) s' = _
      rw [VG.Proof.MdStream.AArch64.eval_nonzero, h13', show (lim - n - (8 * i + 8)) / 8 = (lim - n) / 8 - (i + 1) by omega,
        bne, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by omega)]
      simp
    rw [show 8 * i + 8 = 8 * (i + 1) by omega] at hZ'
    by_cases hl : (lim - n) / 8 - (i + 1) = 0
    · refine .inl ⟨by rw [hz']; simp [hl], ?_⟩
      rwa [show i + 1 = (lim - n) / 8 by omega] at hZ'
    · exact .inr ⟨by rw [hz']; simp [hl], _, by omega, i + 1, rfl, by omega, hZ'⟩

theorem zero_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀) {sI : State} (hC : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ sI) {n lim : Nat}
    (hlim : lim ≤ P.B) (hn : n ≤ lim) {s : State} (h : VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim 0 s) :
    WP isa (zero P) s (VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim (lim - n)) := by
  have := hd.B
  unfold zero
  refine WP.seq (VG.Proof.MdStream.AArch64.wp_lsr (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hZ₁ : VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ sI n lim 0 s₁ := h.of_gpr u₁.other u₁.mem u₁.rd u₁.wr u₁.sp
  have h13 : s₁.gpr .x13 = BitVec.ofNat 64 ((lim - n) / 8) := by
    rw [u₁.gpr, h.x11, Nat.sub_zero, VG.Proof.MdStream.AArch64.ofNat_shr (by omega)]
  refine WP.seq (WP.mono (VG.Proof.MdStream.AArch64.Finalize.zero_words_ok hd hp hC hlim hn hZ₁ h13) fun s₂ hZ₂ => ?_)
  have hz : eval (.zero .x .x11) s₂ = some (decide (lim - n - 8 * ((lim - n) / 8) = 0)) := by
    rw [VG.Proof.MdStream.AArch64.eval_zero, hZ₂.x11, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by omega)]
  refine WP.ite (decide (lim - n - 8 * ((lim - n) / 8) = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (by rwa [show 8 * ((lim - n) / 8) = lim - n by omega] at hZ₂)
  · simp only [decide_eq_false_iff_not] at hb
    exact VG.Proof.MdStream.AArch64.Finalize.zero_loop_ok hd hp hC hlim (by omega) hZ₂

/-! ## One block -/

/-- The compression of the buffer. -/
theorem compress_buf (hd : VG.Proof.MdStream.AArch64.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.AArch64.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀) {s : State} (hC : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s) (hx1 : s.gpr .x1 = VG.Proof.MdStream.AArch64.Finalize.buf P s₀) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s' → (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) →
      H.stateAt s'.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀) = H.compress (H.stateAt s.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀)) (H.blockAt s.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀)) → Q s') :
    WP isa (compressAt name code) s Q := by
  have := hd.N; have := hd.so; have := hd.B
  have eN : Region.Sub ⟨VG.Proof.MdStream.AArch64.Finalize.st s₀, P.N⟩ (VG.Proof.MdStream.AArch64.Finalize.stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.MdStream.AArch64.Finalize.scr s₀, P.so⟩ (VG.Proof.MdStream.AArch64.Finalize.scR P s₀) := Region.sub_prefix (by omega)
  have eb : Region.Sub ⟨VG.Proof.MdStream.AArch64.Finalize.buf P s₀, P.B⟩ (VG.Proof.MdStream.AArch64.Finalize.stR P s₀) := VG.Proof.MdStream.AArch64.sub_offset (off := P.N) (by omega) (by omega)
  refine VG.Proof.MdStream.AArch64.compressAt_ok hf hC.x19 hC.x20 hx1 ((hp.st_scr.sub_left eN).sub_right eso) ?_
    ((hp.st_scr.sub_left eb).sub_right eso) ?_ ?_ fun s' hrd hwr hcs hsp hf' hstate =>
      hQ s' ?_ hcs hstate
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · rw [hC.rd, hC.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.MdStream.AArch64.Finalize.stR P s₀, by simp, P.N, rfl, by simp⟩
    · exact ⟨VG.Proof.MdStream.AArch64.Finalize.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.AArch64.Finalize.scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.MdStream.AArch64.Finalize.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.AArch64.Finalize.scR P s₀, by simp, 0, by simp, by simp⟩
  · have cs : ∀ r, r ∈ preserved → r ≠ .x30 → s'.gpr r = s.gpr r := hcs
    refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide) (by decide)]; exact hC.x19,
      by rw [cs _ (by decide) (by decide)]; exact hC.x20,
      by rw [cs _ (by decide) (by decide)]; exact hC.x21,
      by rw [cs _ (by decide) (by decide)]; exact hC.x22, hsp.trans hC.sp, hC.frame.trans (hf'.sub ?_),
      fun p hp' => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.MdStream.AArch64.Finalize.stR P s₀, by simp, eN⟩
      · exact ⟨VG.Proof.MdStream.AArch64.Finalize.scR P s₀, by simp, eso⟩
    · rw [← hC.saved p hp']
      have := VG.Proof.MdStream.AArch64.saved_offset hd hp'
      refine hf'.readW (r := ⟨VG.Proof.MdStream.AArch64.Finalize.scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (VG.Proof.MdStream.AArch64.Finalize.saved_sub hd hp')).sub_right eN
      · exact Offset.disjoint_base _ (by omega) (by omega)

/-- The loop's postcondition for one iteration. -/
def Step {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (k : Nat) (s : State) : Prop :=
  (eval (.zero .x .x24) s = some false ∧ VG.Proof.MdStream.AArch64.Finalize.Done H s₀ s) ∨
    (eval (.zero .x .x24) s = some true ∧ k = 1 ∧ VG.Proof.MdStream.AArch64.Finalize.LInv H s₀ 0 0 s)

theorem body_ok (hd : VG.Proof.MdStream.AArch64.Dims P) (hs : VG.Proof.MdStream.AArch64.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.AArch64.CalleeOk H code)
    {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀) {k n : Nat} {s : State} (h : VG.Proof.MdStream.AArch64.Finalize.LInv H s₀ k n s) :
    WP isa (finalizeBody P name code) s (VG.Proof.MdStream.AArch64.Finalize.Step H s₀ k) := by
  have hk := h.k_le; have hn := h.n_le
  have hC := h.toCommon
  have := hd.N; have := hd.B; have := hd.L
  have hlim := VG.Proof.MdStream.AArch64.Finalize.lim_le (P := P) k; have hlim' := VG.Proof.MdStream.AArch64.Finalize.lim_ge (P := P) k
  unfold finalizeBody
  -- `x11 := B` or `B - L`: the end of the zeros.
  refine WP.seq (VG.Proof.MdStream.AArch64.wp_movz fun s₁ u₁ => WP.block_nil ?_)
  have hz₁ : eval (.zero .x .x24) s₁ = some (decide (k = 0)) := by
    rw [VG.Proof.MdStream.AArch64.eval_zero, u₁.other _ (by decide), h.x24, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .x11 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Finalize.lim P k) ∧
      (∀ r, r ≠ .x11 → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      s₃.sp = s.sp) ?_ fun s₃ ⟨h11₃, g₃, m₃, rd₃, wr₃, sp₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) hz₁ (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine VG.Proof.MdStream.AArch64.wp_movz fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr, VG.Proof.MdStream.AArch64.setWidth_ofNat16 (by omega)]; rfl,
        fun r hr => ?_,
        by rw [u₃.mem, u₁.mem], by rw [u₃.rd, u₁.rd], by rw [u₃.wr, u₁.wr], by rw [u₃.sp, u₁.sp]⟩
      rw [u₃.other r hr, u₁.other r hr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [u₁.gpr, hd.movB]; simp [VG.Proof.MdStream.AArch64.Finalize.lim, hb], fun r hr => ?_,
        u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩
      rw [u₁.other r hr]
  -- Zero the rest of the buffer, up to `lim`.
  refine WP.seq (VG.Proof.MdStream.AArch64.wp_movz fun s₄ u₄ => VG.Proof.MdStream.AArch64.wp_sub fun s₅ u₅ => WP.block_nil ?_)
  have hZ : VG.Proof.MdStream.AArch64.Finalize.Zero P s₀ s n (VG.Proof.MdStream.AArch64.Finalize.lim P k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => ?_, by rw [u₅.rd, u₄.rd, rd₃], by rw [u₅.wr, u₄.wr, wr₃],
      by rw [u₅.sp, u₄.sp, sp₃], ?_, ?_, ?_, ?_⟩
    · have : r ≠ .x11 ∧ r ≠ .x9 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u₅.other r this.1, u₄.other r this.2, g₃ r this.1]
    · rw [u₅.other _ (by decide), u₄.gpr]; rfl
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), h.x23, Nat.add_zero]
    · rw [u₅.gpr, u₄.other _ (by decide), h11₃, u₄.other _ (by decide), g₃ _ (by decide), h.x23,
        VG.Proof.MdStream.AArch64.sub_ofNat (by omega), Nat.sub_zero]
    · rw [u₅.mem, u₄.mem, m₃, List.replicate_zero, VG.WriteBytes.writeBytes_nil]
  refine WP.seq (WP.mono (VG.Proof.MdStream.AArch64.Finalize.zero_ok hd hp hC (by omega) hn hZ) fun s₆ hZ₆ => ?_)
  obtain ⟨hf₆, hfr₆, hsv₆⟩ := hC.writeBuf hd hp (n := n) (xs := List.replicate (VG.Proof.MdStream.AArch64.Finalize.lim P k - n) 0)
    (by simp only [List.length_replicate]; omega)
  have hC₆ : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s₆ :=
    ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp), hC.x19],
      by rw [hZ₆.keep _ (by simp), hC.x20], by rw [hZ₆.keep _ (by simp), hC.x21],
      by rw [hZ₆.keep _ (by simp), hC.x22], hZ₆.sp.trans hC.sp,
      by rw [hZ₆.mem]; exact hfr₆, by rw [hZ₆.mem]; exact hsv₆⟩
  have hst₆ : H.stateAt s₆.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀) = H.stateAt s.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀) := by
    rw [hZ₆.mem]
    apply H.stateAt_congr
    intro i hi
    rw [VG.Proof.MdStream.AArch64.Finalize.buf_add]
    exact VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀) (VG.Proof.MdStream.AArch64.Finalize.lim P k) =
      bytesAt s.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀) n ++ List.replicate (VG.Proof.MdStream.AArch64.Finalize.lim P k - n) 0 := by
    rw [hZ₆.mem, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have h24₆ : s₆.gpr .x24 = BitVec.ofNat 64 k := by rw [hZ₆.keep _ (by simp), h.x24]
  -- In the last block, the length field.
  have hz₆ : eval (.zero .x .x24) s₆ = some (decide (k = 0)) := by
    rw [VG.Proof.MdStream.AArch64.eval_zero, h24₆, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s₈ ∧ s₈.gpr .x24 = BitVec.ofNat 64 k ∧
      H.stateAt s₈.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀) = H.stateAt s.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀) ∧
      ∀ iv m, VG.Proof.MdStream.AArch64.Finalize.R₀ H s₀ iv m → H.lenOk m.length → bytesAt s₈.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀) P.B = bytesAt s.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀) n ++
        (if k = 1 then List.replicate (P.B - n) 0 else List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)) ?_
    fun s₈ ⟨hC₈, h24₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) hz₆ (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      have e : VG.Proof.MdStream.AArch64.Finalize.st s₀ + BitVec.ofNat 64 (P.N + P.B - P.L) = VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 (P.B - P.L) := by
        rw [VG.Proof.MdStream.AArch64.Finalize.buf_add, show P.N + (P.B - P.L) = P.N + P.B - P.L by omega]
      have hout : InRegions s₆.wr (s₆.gpr .x19 + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L :=
        ⟨VG.Proof.MdStream.AArch64.Finalize.stR P s₀, by simp [hC₆.wr, hp.wr], by rw [hC₆.x19]; exact VG.Proof.MdStream.AArch64.contains_offset (by omega) (by omega)⟩
      refine WP.mono (hs.len s₆ hout) fun s₈ ⟨g₈, rd₈, wr₈, sp₈, m₈⟩ => ?_
      rw [hC₆.x19, hC₆.x22, e] at m₈
      have hlen := H.lenOf_length (s₀.gpr .x1)
      obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hd hp (n := P.B - P.L) (xs := H.lenOf (s₀.gpr .x1)) (by omega)
      have hl0 : VG.Proof.MdStream.AArch64.Finalize.lim P 0 = P.B - P.L := rfl
      refine ⟨⟨rd₈.trans hC₆.rd, wr₈.trans hC₆.wr, by rw [g₈ _ (by decide) (by decide), hC₆.x19],
        by rw [g₈ _ (by decide) (by decide), hC₆.x20], by rw [g₈ _ (by decide) (by decide), hC₆.x21],
        by rw [g₈ _ (by decide) (by decide), hC₆.x22], sp₈.trans hC₆.sp,
        by rw [m₈]; exact hfr, by rw [m₈]; exact hsv⟩,
        by rw [g₈ _ (by decide) (by decide), h24₆], ?_, fun iv m hm hok => ?_⟩
      · rw [m₈, ← hst₆]
        apply H.stateAt_congr
        intro i hi
        rw [VG.Proof.MdStream.AArch64.Finalize.buf_add]
        exact VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by omega)
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        rw [hm.2, H.lenOf_eq _ hok] at m₈
        have e := bytesAt_writeBytes s₆.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀) (P.B - P.L) (H.lenBytes m.length)
          (by rw [H.lenBytes_length]; omega)
        rw [H.lenBytes_length, show P.B - P.L + P.L = P.B by omega] at e
        rw [m₈, e, ← hl0, hby₆, List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      have e1 : VG.Proof.MdStream.AArch64.Finalize.lim P 1 = P.B := rfl
      refine WP.block_nil ⟨hC₆, h24₆, hst₆, fun iv m _ _ => ?_⟩
      have h' := hby₆
      rw [e1] at h'
      simpa using h'
  -- Compress the block.
  refine WP.seq (VG.Proof.MdStream.AArch64.wp_addImm (by omega) fun s₉ u₉ => WP.block_nil ?_)
  have hC₉ : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s₉ := hC₈.of_gpr (fun r hr => by
      have : r ≠ .x1 := by simp at hr; rcases hr with h | h | h | h <;> subst h <;> decide
      rw [u₉.other r this]) u₉.mem u₉.rd u₉.wr u₉.sp
  have hx1 : s₉.gpr .x1 = VG.Proof.MdStream.AArch64.Finalize.buf P s₀ := by rw [u₉.gpr, hC₈.x19]
  refine WP.seq (VG.Proof.MdStream.AArch64.Finalize.compress_buf hd hf hp hC₉ hx1 fun s₁₁ hC₁₁ cs₁₁ hst₁₁ => ?_)
  have h24₁₁ : s₁₁.gpr .x24 = BitVec.ofNat 64 k := by
    rw [cs₁₁ _ (by decide) (by decide), u₉.other _ (by decide), h24₈]
  have hblk : ∀ iv m, VG.Proof.MdStream.AArch64.Finalize.R₀ H s₀ iv m → H.lenOk m.length → H.blockAt s₉.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀) = H.parse fun t =>
      (bytesAt s.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀) n ++
        (if k = 1 then List.replicate (P.B - n) 0 else List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)).getD t 0 := by
    intro iv m hm hok
    apply H.parse_congr
    intro t ht
    rw [u₉.mem]
    exact VG.Proof.MdStream.AArch64.bytesAt_getD (hby₈ iv m hm hok) ht
  -- Next block, if any.
  refine VG.Proof.MdStream.AArch64.wp_movz fun s₁₂ u₁₂ => VG.Proof.MdStream.AArch64.wp_subImm (by decide) fun s₁₃ u₁₃ => WP.block_nil ?_
  have hC₁₃ : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s₁₃ := hC₁₁.of_gpr (fun r hr => by
      have : r ≠ .x24 ∧ r ≠ .x23 := by simp at hr; rcases hr with h | h | h | h <;> subst h <;> decide
      rw [u₁₃.other r this.1, u₁₂.other r this.2]) (by rw [u₁₃.mem, u₁₂.mem]) (by rw [u₁₃.rd, u₁₂.rd])
    (by rw [u₁₃.wr, u₁₂.wr]) (by rw [u₁₃.sp, u₁₂.sp])
  have hz : eval (.zero .x .x24) s₁₃ = some (decide (k = 1)) := by
    rw [VG.Proof.MdStream.AArch64.eval_zero, u₁₃.gpr, u₁₂.other _ (by decide), h24₁₁, VG.Proof.MdStream.AArch64.sub_beq (by omega) (by omega)]
  have hst : ∀ iv m, VG.Proof.MdStream.AArch64.Finalize.R₀ H s₀ iv m → H.lenOk m.length →
      H.stateAt s₁₃.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀) = H.compress (H.stateAt s.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀)) (H.parse fun t =>
        (bytesAt s.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀) n ++
          (if k = 1 then List.replicate (P.B - n) 0 else List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)).getD t 0) := by
    intro iv m hm hok
    rw [u₁₃.mem, u₁₂.mem, hst₁₁, u₉.mem, hst₈, ← hblk iv m hm hok, u₉.mem]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by rw [hz]; simp, rfl, ⟨hC₁₃, by omega, by omega, ?_, ?_, fun iv m hm hok => ?_⟩⟩
    · rw [u₁₃.other _ (by decide), u₁₂.gpr]; rfl
    · rw [u₁₃.gpr, u₁₂.other _ (by decide), h24₁₁]; rfl
    · rw [h.hash iv m hm hok]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, VG.Proof.MdStream.AArch64.Finalize.Fin1, VG.Proof.MdStream.AArch64.Finalize.Fin0, hst iv m hm hok]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by rw [hz]; simp, hC₁₃, fun iv m hm hok => ?_⟩
    rw [h.hash iv m hm hok, hst iv m hm hok]
    simp only [show ¬ (0 = 1) by decide, ite_false, VG.Proof.MdStream.AArch64.Finalize.Fin0, List.append_assoc]

/-! ## Prologue -/

theorem prologue_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀) :
    WP isa (.block (finalizeStart P)) s₀ fun s => ∃ k, VG.Proof.MdStream.AArch64.Finalize.LInv H s₀ k (VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B + 1) s := by
  have hr : VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B < P.B := Nat.mod_lt _ hd.pos
  have := hd.N; have := hd.so; have := hd.B; have := hd.L
  refine VG.Proof.MdStream.AArch64.save_ok hd (fun d hd₁ hd₂ => ⟨VG.Proof.MdStream.AArch64.Finalize.scR P s₀, by simp [hp.wr], VG.Proof.MdStream.AArch64.contains_offset hd₂ (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine VG.Proof.MdStream.AArch64.wp_mov fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_mov fun s₃ u₃ => VG.Proof.MdStream.AArch64.wp_mov fun s₄ u₄ => VG.Proof.MdStream.AArch64.wp_mov fun s₅ u₅ =>
    VG.Proof.MdStream.AArch64.wp_movz fun s₆ u₆ => VG.Proof.MdStream.AArch64.wp_and fun s₇ u₇ => ?_
  have hm₇ : s₇.mem = VG.Proof.MdStream.AArch64.saveMem P s₀.mem (VG.Proof.MdStream.AArch64.Finalize.scr s₀) s₀.gpr := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have hC₇ : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
    · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, g₁]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.other _ (by decide), g₁]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
    · rw [hm₇]; exact (VG.Proof.MdStream.AArch64.saveMem_frame hd _ _ _).mono (by simp)
    · rw [hm₇]; exact VG.Proof.MdStream.AArch64.saveMem_saved hd _ _ _
  have hr23 : s₇.gpr .x23 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B) := by
    rw [u₇.gpr, u₆.other .x22 (by decide), u₆.gpr, u₅.gpr, u₄.other .x1 (by decide),
      u₃.other .x1 (by decide), u₂.other .x1 (by decide), g₁]
    exact hd.and _
  -- The `0x80` byte.
  have hout : InRegions s₇.wr (VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B)) 1 := by
    refine ⟨VG.Proof.MdStream.AArch64.Finalize.stR P s₀, by simp [hC₇.wr, hp.wr], ?_⟩
    rw [VG.Proof.MdStream.AArch64.Finalize.buf_add]; exact VG.Proof.MdStream.AArch64.contains_offset (by omega) (by omega)
  refine VG.Proof.MdStream.AArch64.wp_movz fun s₈ u₈ => VG.Proof.MdStream.AArch64.wp_add fun s₉ u₉ =>
    VG.Proof.MdStream.AArch64.wp_strb (a := VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B)) (by omega) ?_
      (by rw [u₉.wr, u₈.wr]; exact hout) fun s₁₀ g₁₀ => ?_
  · rw [u₉.gpr, u₈.other _ (by decide), u₈.other _ (by decide), hC₇.x19, hr23, VG.Proof.MdStream.AArch64.Finalize.buf]
    ac_rfl
  obtain ⟨-, hfr, hsv⟩ := hC₇.writeBuf hd hp (n := VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B) (xs := [0x80]) (by simp; omega)
  have hm₁₀ : s₁₀.mem = VG.WriteBytes.writeBytes s₇.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B)) [0x80] := by
    rw [g₁₀.mem, u₉.mem, u₈.mem, u₉.other _ (by decide), u₈.gpr, ← List.nil_append [(0x80 : Byte)],
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp), VG.WriteBytes.writeBytes_nil]
    simp
  refine VG.Proof.MdStream.AArch64.wp_addImm (by decide) fun s₁₁ u₁₁ => VG.Proof.MdStream.AArch64.wp_addImm (by omega) fun s₁₂ u₁₂ =>
    VG.Proof.MdStream.AArch64.wp_lsr (by have := hd.log; omega) fun s₁₃ u₁₃ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .x23 → r ≠ .x24 → r ≠ .x9 → r ≠ .x12 → s₁₃.gpr r = s₇.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₁₃.other r h2, u₁₂.other r h2, u₁₁.other r h1, g₁₀.gpr, u₉.other r h4, u₈.other r h3]
  have hm₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have hC₁₃ : VG.Proof.MdStream.AArch64.Finalize.Common P s₀ s₁₃ :=
    ⟨by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, g₁₀.rd, u₉.rd, u₈.rd, hC₇.rd],
      by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, hC₇.wr],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.x19],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.x20],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.x21],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.x22],
      by rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, g₁₀.sp, u₉.sp, u₈.sp, hC₇.sp],
      by rw [hm₁₃, hm₁₀]; exact hfr, by rw [hm₁₃, hm₁₀]; exact hsv⟩
  have hr23' : s₁₃.gpr .x23 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B + 1) := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), hr23, ← BitVec.ofNat_add]
  have hr24 : s₁₃.gpr .x24 = BitVec.ofNat 64 ((VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B + 1 + (P.L - 1)) / P.B) := by
    rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), hr23,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, hd.shr (by omega)]
  -- The facts about the buffer.
  have hbytes : ∀ iv m, VG.Proof.MdStream.AArch64.Finalize.R₀ H s₀ iv m → bytesAt s₁₃.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀) (VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B + 1) =
      Md.rest P.B m ++ [0x80] := by
    intro iv m hm
    have e := bytesAt_writeBytes s₇.mem (VG.Proof.MdStream.AArch64.Finalize.buf P s₀) (VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₃, hm₁₀, e, hm₇]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length hd]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := VG.Proof.MdStream.AArch64.frame_bytes (VG.Proof.MdStream.AArch64.saveMem_frame hd s₀.mem (VG.Proof.MdStream.AArch64.Finalize.scr s₀) s₀.gpr) (R := VG.Proof.MdStream.AArch64.Finalize.stR P s₀)
      (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; omega) (i := P.N + i)
      (by have := Nat.mod_lt m.length hd.pos; show P.N + i < P.N + P.B; omega)
    rwa [← VG.Proof.MdStream.AArch64.Finalize.buf_add] at this
  have hstate : H.stateAt s₁₃.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀) = H.stateAt s₀.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀) := by
    apply H.stateAt_congr
    intro i hi
    rw [hm₁₃, hm₁₀, VG.Proof.MdStream.AArch64.Finalize.buf_add, VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by simp; omega), hm₇]
    exact VG.Proof.MdStream.AArch64.frame_bytes (VG.Proof.MdStream.AArch64.saveMem_frame hd s₀.mem (VG.Proof.MdStream.AArch64.Finalize.scr s₀) s₀.gpr) (R := VG.Proof.MdStream.AArch64.Finalize.stR P s₀) (by simpa using hp.st_scr)
      (by show P.N + P.B ≤ 2 ^ 64; omega) (by show i < P.N + P.B; omega)
  by_cases hb : P.B - P.L + 1 ≤ VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B + 1
  · have hk : (VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B + 1 + (P.L - 1)) / P.B = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    refine ⟨1, hC₁₃, (Nat.le_refl _), by simp [VG.Proof.MdStream.AArch64.Finalize.lim]; omega, hr23', by rw [hr24, hk], fun iv m hm _ => ?_⟩
    simp only [↓reduceIte]
    rw [Md.hash_two H hd.pos (by omega) (by rw [← hm.length hd]; omega), VG.Proof.MdStream.AArch64.Finalize.Fin1, hbytes iv m hm, hstate,
      hm.1.1, ← hm.length hd, show P.B - (VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B + 1) = P.B - 1 - VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B by omega]
  · have hk : (VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B + 1 + (P.L - 1)) / P.B = 0 := Nat.div_eq_of_lt (by omega)
    refine ⟨0, hC₁₃, by omega, by simp [VG.Proof.MdStream.AArch64.Finalize.lim]; omega, hr23', by rw [hr24, hk], fun iv m hm _ => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [Md.hash_one H hd.pos (by rw [← hm.length hd]; omega), VG.Proof.MdStream.AArch64.Finalize.Fin0, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length hd, show P.B - P.L - (VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B + 1) = P.B - P.L - 1 - VG.Proof.MdStream.AArch64.Finalize.cnt s₀ % P.B by omega]

/-! ## Output and epilogue -/

/-- The epilogue's postcondition. -/
def Post (P : Params) (H : Md P.B P.N P.L) (s₀ s' : State) : Prop :=
  (∀ p ∈ saved P, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧ (VG.Proof.MdStream.AArch64.finK H).post s₀ s'

theorem epilogue_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀) {sD : State} (hD : VG.Proof.MdStream.AArch64.Finalize.Done H s₀ sD) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hkeep : ∀ r, r ≠ .x9 → s.gpr r = sD.gpr r)
    (hsp : s.sp = sD.sp) (hm : s.mem = VG.WriteBytes.writeBytes sD.mem (VG.Proof.MdStream.AArch64.Finalize.out s₀) (H.digest (H.stateAt sD.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀)))) :
    WP isa (.block (restore P)) s (VG.Proof.MdStream.AArch64.Finalize.Post P H s₀) := by
  have := hd.N; have := hd.so; have := hd.B
  have hC := hD.1
  have hdl := H.digest_length (H.stateAt sD.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀))
  have hfo : Frame [VG.Proof.MdStream.AArch64.Finalize.outR P s₀] sD.mem (VG.WriteBytes.writeBytes sD.mem (VG.Proof.MdStream.AArch64.Finalize.out s₀) (H.digest (H.stateAt sD.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀)))) :=
    VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [show VG.Proof.MdStream.AArch64.Finalize.out s₀ = VG.Proof.MdStream.AArch64.Finalize.out s₀ + BitVec.ofNat 64 0 by simp]
      exact VG.Proof.MdStream.AArch64.contains_offset (by omega) (by omega))
  refine VG.Proof.MdStream.AArch64.restore_ok hd (scr := VG.Proof.MdStream.AArch64.Finalize.scr s₀) (by rw [hkeep _ (by decide), hC.x20])
    (fun d hd₁ hd₂ => ⟨VG.Proof.MdStream.AArch64.Finalize.scR P s₀, by simp [hrd, hwr, hp.wr], VG.Proof.MdStream.AArch64.contains_offset hd₂ (by omega)⟩) s₀.gpr
    (fun p hp' => ?_) fun s' hs _ hmem _ _ hsp' => ⟨hs, by rw [hsp', hsp, hC.sp], ?_⟩
  · rw [hm, ← hC.saved p hp']
    have := VG.Proof.MdStream.AArch64.saved_offset hd hp'
    refine hfo.readW (r := ⟨VG.Proof.MdStream.AArch64.Finalize.scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.out_scr.symm.sub_left (VG.Proof.MdStream.AArch64.Finalize.saved_sub hd hp')
  · intro iv m hr hok hc
    have e := bytesAt_writeBytes sD.mem (VG.Proof.MdStream.AArch64.Finalize.out s₀) 0 (H.digest (H.stateAt sD.mem (VG.Proof.MdStream.AArch64.Finalize.st s₀))) (by omega)
    rw [hdl, show VG.Proof.MdStream.AArch64.Finalize.out s₀ + BitVec.ofNat 64 0 = VG.Proof.MdStream.AArch64.Finalize.out s₀ by simp, Nat.zero_add,
      show bytesAt sD.mem (VG.Proof.MdStream.AArch64.Finalize.out s₀) 0 = [] from rfl, List.nil_append] at e
    rw [hmem, hm, e]
    exact (hD.2 iv m ⟨hr, hc⟩ hok).symm

/-- `finalize` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain (hd : VG.Proof.MdStream.AArch64.Dims P) (hs : VG.Proof.MdStream.AArch64.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.AArch64.CalleeOk H code)
    (hu : ∀ r ∈ VG.Proof.MdStream.AArch64.untouched, ∀ i ∈ instrs (finalizeMain P name code), dstOf i ≠ some r) {s₀ : State}
    (hp : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀) :
    WP isa (finalizeMain P name code) s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ (VG.Proof.MdStream.AArch64.finK H).post s₀ s' := by
  have := hd.N; have := hd.B
  refine WP.mono (WP.gprs (Q := VG.Proof.MdStream.AArch64.Finalize.Post P H s₀) ?_ hu) fun s' ⟨⟨hsv, hsp, hpost⟩, hu⟩ =>
    ⟨VG.Proof.MdStream.AArch64.preserved_of hsv hu, hsp, hpost⟩
  unfold finalizeMain
  refine WP.seq (WP.mono (VG.Proof.MdStream.AArch64.Finalize.prologue_ok (H := H) hd hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.MdStream.AArch64.Finalize.Done H s₀) ?_ fun sD hD => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n, VG.Proof.MdStream.AArch64.Finalize.LInv H s₀ i n s) ?_ k s₁ ⟨_, hL⟩
    rintro i s ⟨n, hL⟩
    refine WP.mono (VG.Proof.MdStream.AArch64.Finalize.body_ok hd hs hf hp hL) fun s' h => ?_
    rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by omega, 0, hL'⟩
  · have hC := hD.1
    rw [WP.block_append_iff]
    refine WP.mono (hs.out sD ?_ ?_ ?_) fun s ⟨g, rd, wr, sp, m⟩ =>
      VG.Proof.MdStream.AArch64.Finalize.epilogue_ok hd hp hD (rd.trans hC.rd) (wr.trans hC.wr) g sp (by rw [m, hC.x21, hC.x19])
    · refine ⟨VG.Proof.MdStream.AArch64.Finalize.stR P s₀, by simp [hC.rd, hC.wr, hp.wr, hp.rd], ?_⟩
      rw [hC.x19]; simpa using VG.Proof.MdStream.AArch64.contains_offset (base := VG.Proof.MdStream.AArch64.Finalize.st s₀) (off := 0) (n := P.N) (len := P.N + P.B)
        (by omega) (by omega)
    · refine ⟨VG.Proof.MdStream.AArch64.Finalize.outR P s₀, by simp [hC.wr, hp.wr], ?_⟩
      rw [hC.x21]; simpa using VG.Proof.MdStream.AArch64.contains_offset (base := VG.Proof.MdStream.AArch64.Finalize.out s₀) (off := 0) (n := P.N) (len := P.N)
        (by omega) (by omega)
    · rw [hC.x19, hC.x21]
      exact hp.st_out.sub_left (Region.sub_prefix (by omega))

/-- The state `finalizeMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct (hd : VG.Proof.MdStream.AArch64.Dims P) (hs : VG.Proof.MdStream.AArch64.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.AArch64.CalleeOk H code)
    (hu : ∀ r ∈ VG.Proof.MdStream.AArch64.untouched, ∀ i ∈ instrs (finalizeMain P name code), dstOf i ≠ some r)
    (hn : 16 * (finalizeMain P name code).aarch64Depth + 16 < 2 ^ 64) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Finalize.Pre P s₀)
    (hst : VG.Proof.MdStream.AArch64.Finalize.Stack P s₀) :
    WP isa (finalize P name code) s₀ fun s' => abiPreserved s₀ s' ∧ (VG.Proof.MdStream.AArch64.finK H).post s₀ s' := by
  apply WP.withPreservedV (hc := VG.Proof.MdStream.AArch64.finalize_keepsV hs hf.keepsV)
  have hpi : VG.Proof.MdStream.AArch64.Finalize.Pre P (VG.Proof.MdStream.AArch64.Finalize.inner s₀) := ⟨hp.rd, hp.wr, hp.st_out, hp.st_scr, hp.out_scr⟩
  refine WP.frameReg hst.sp16 (fun R hR => ?_)
    (WP.mono (VG.Proof.MdStream.AArch64.Finalize.correctMain hd hs hf hu hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_) hn
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact hst.st
    · exact hst.out
    · exact hst.scr
  · refine ⟨⟨fun r hr => ?_, rfl⟩, fun iv m hm hok hc => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · exact hpost iv m (H.repr_congr hd.pos (fun i hi => VG.Proof.MdStream.AArch64.write_frame_bytes (R := VG.Proof.MdStream.AArch64.Finalize.stR P s₀) hst.st
        (by have := hd.N; have := hd.B; show P.N + P.B < 2 ^ 64; omega) hi) hm) hok hc

/-- A state satisfying the precondition. -/
def sat (P : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, P.N + P.B⟩, ⟨0x2000, P.N⟩, ⟨0x3000, P.so + 48⟩]

/-- `finalize` is verified, given that it is constant time (which the taint
analysis proves of each hash function's code), never writes `untouched`, and
fits its frames in the address space. -/
theorem verified (hd : VG.Proof.MdStream.AArch64.Dims P) (hs : VG.Proof.MdStream.AArch64.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.AArch64.CalleeOk H code)
    (hct : ConstantTime isa (VG.Proof.MdStream.AArch64.finK H).pre (VG.Proof.MdStream.AArch64.finK H).pub (finalize P name code))
    (hu : ((instrs (finalizeMain P name code)).all fun i => untouched.all fun r => dstOf i != some r) = true)
    (hn : 16 * (finalizeMain P name code).aarch64Depth + 16 < 2 ^ 64) :
    Verified AArch64.target (finalize P name code) (VG.Proof.MdStream.AArch64.finK H) := by
  have := hd.N; have := hd.so; have := hd.B
  have hu' : ∀ r ∈ VG.Proof.MdStream.AArch64.untouched, ∀ i ∈ instrs (finalizeMain P name code), dstOf i ≠ some r := by
    intro r hr i hi
    have := List.all_eq_true.mp (List.all_eq_true.mp hu i hi) r hr
    simpa using this
  refine ⟨fun s hs' => ?_, hct, ?_⟩
  · obtain ⟨t, s', he, h⟩ := VG.Proof.MdStream.AArch64.Finalize.correct hd hs hf hu' hn (VG.Proof.MdStream.AArch64.Finalize.pre_of hs').1 (VG.Proof.MdStream.AArch64.Finalize.pre_of hs').2
    exact ⟨t, s', he, h⟩
  · refine ⟨VG.Proof.MdStream.AArch64.Finalize.sat P, rfl, rfl, ?_, ?_, ?_, by simp only [VG.Proof.MdStream.AArch64.Finalize.sat]; decide, ?_, ?_, ?_⟩
    all_goals try simp only [VG.Proof.MdStream.AArch64.Finalize.sat]
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm

/-- The initial taint agrees on the public arguments. -/
theorem agree₀ {s₁ s₂ : State} (hpub : (VG.Proof.MdStream.AArch64.finK H).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

end

end VG.Proof.MdStream.AArch64.Finalize

end

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.AArch64.Update`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on AArch64: `update`

The functional correctness of `update`, for any hash function (`Md`) and any
correct compression function (`CalleeOk`). The same structure as the x86-64
proof (`VG.Proof.MdStream.X86_64.Update`); the loop runs while data is left,
so every iteration consumes at least one byte. Constant time is proven for
each hash function's code by the taint analysis, calls included.
-/

namespace VG.Proof.MdStream.AArch64.Update

open VG VG.AArch64 VG.Impl.MdStream.AArch64
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame bytesAt_congr)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev cnt : Nat := (s₀.gpr .x1).toNat
abbrev dp : Addr := s₀.gpr .x2
abbrev len : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev stR : Region := ⟨VG.Proof.MdStream.AArch64.Update.st s₀, P.N + P.B⟩
abbrev dR : Region := ⟨VG.Proof.MdStream.AArch64.Update.dp s₀, VG.Proof.MdStream.AArch64.Update.len s₀⟩
abbrev scR : Region := ⟨VG.Proof.MdStream.AArch64.Update.scr s₀, P.so + 48⟩
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (VG.Proof.MdStream.AArch64.Update.dp s₀) (VG.Proof.MdStream.AArch64.Update.len s₀)
/-- The buffer. -/
abbrev buf : Addr := VG.Proof.MdStream.AArch64.Update.st s₀ + BitVec.ofNat 64 P.N

end

/-- The messages the initial state represents, from `iv`. -/
def R₀ {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (VG.Proof.MdStream.AArch64.Update.st s₀) m ∧ s₀.gpr .x1 = BitVec.ofNat 64 m.length

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.MdStream.AArch64.Update.dR s₀]
  wr : s₀.wr = [VG.Proof.MdStream.AArch64.Update.stR P s₀, VG.Proof.MdStream.AArch64.Update.scR P s₀]
  st_scr : (VG.Proof.MdStream.AArch64.Update.stR P s₀).Disjoint (VG.Proof.MdStream.AArch64.Update.scR P s₀)
  d_st : (VG.Proof.MdStream.AArch64.Update.dR s₀).Disjoint (VG.Proof.MdStream.AArch64.Update.stR P s₀)
  d_scr : (VG.Proof.MdStream.AArch64.Update.dR s₀).Disjoint (VG.Proof.MdStream.AArch64.Update.scR P s₀)

/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR (s₀ : State) : Region := ⟨s₀.sp - 16, 16⟩

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (P : Params) (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (VG.Proof.MdStream.AArch64.Update.stkR s₀).Disjoint (VG.Proof.MdStream.AArch64.Update.stR P s₀)
  d : (VG.Proof.MdStream.AArch64.Update.stkR s₀).Disjoint (VG.Proof.MdStream.AArch64.Update.dR s₀)
  scr : (VG.Proof.MdStream.AArch64.Update.stkR s₀).Disjoint (VG.Proof.MdStream.AArch64.Update.scR P s₀)

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem pre_of {s₀ : State} (h : (VG.Proof.MdStream.AArch64.updK H).pre s₀) : VG.Proof.MdStream.AArch64.Update.Pre P s₀ ∧ VG.Proof.MdStream.AArch64.Update.Stack P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

theorem R₀.length (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} {iv : H.HV} {m : List Byte} (h : VG.Proof.MdStream.AArch64.Update.R₀ H s₀ iv m) :
    VG.Proof.MdStream.AArch64.Update.cnt s₀ % P.B = m.length % P.B := by
  rw [VG.Proof.MdStream.AArch64.Update.cnt, h.2, BitVec.toNat_ofNat, hd.mod]

theorem len_lt (s₀ : State) : VG.Proof.MdStream.AArch64.Update.len s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt

theorem D_length (s₀ : State) : (VG.Proof.MdStream.AArch64.Update.D s₀).length = VG.Proof.MdStream.AArch64.Update.len s₀ := by simp [bytesAt]

end

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (P : Params) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ VG.Proof.MdStream.AArch64.Update.len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = VG.Proof.MdStream.AArch64.Update.st s₀
  x20 : s.gpr .x20 = VG.Proof.MdStream.AArch64.Update.scr s₀
  sp : s.sp = s₀.sp
  x21 : s.gpr .x21 = VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 c
  x22 : s.gpr .x22 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Update.len s₀ - c)
  frame : Frame [VG.Proof.MdStream.AArch64.Update.stR P s₀, VG.Proof.MdStream.AArch64.Update.scR P s₀] s₀.mem s.mem
  saved : VG.Proof.MdStream.AArch64.Saved P (VG.Proof.MdStream.AArch64.Update.scr s₀) s₀.gpr s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c : Nat) (s : State) : Prop
    extends VG.Proof.MdStream.AArch64.Update.Common P s₀ c s where
  x23 : s.gpr .x23 = BitVec.ofNat 64 ((VG.Proof.MdStream.AArch64.Update.cnt s₀ + c) % P.B)
  repr : ∀ iv m, VG.Proof.MdStream.AArch64.Update.R₀ H s₀ iv m → H.Repr iv s.mem (VG.Proof.MdStream.AArch64.Update.st s₀) (m ++ (VG.Proof.MdStream.AArch64.Update.D s₀).take c)

/-- `k ≥ 1` whole blocks are ready at `x1` (the buffer, or the data), and
compressing them absorbs the first `c` bytes of data. -/
structure Pending {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c k : Nat) (s : State) : Prop
    extends VG.Proof.MdStream.AArch64.Update.Common P s₀ c s where
  x23 : s.gpr .x23 = 0
  x10 : s.gpr .x10 = BitVec.ofNat 64 k
  k_pos : 0 < k
  mod : (VG.Proof.MdStream.AArch64.Update.cnt s₀ + c) % P.B = 0
  src : (s.gpr .x1 = VG.Proof.MdStream.AArch64.Update.buf P s₀ ∧ k = 1) ∨
    ∃ c₀, s.gpr .x1 = VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + P.B * k ≤ VG.Proof.MdStream.AArch64.Update.len s₀
  repr : ∀ iv m, VG.Proof.MdStream.AArch64.Update.R₀ H s₀ iv m → ∀ mem', H.stateAt mem' (VG.Proof.MdStream.AArch64.Update.st s₀) =
      H.compressBlocks (H.stateAt s.mem (VG.Proof.MdStream.AArch64.Update.st s₀)) s.mem (s.gpr .x1) k →
    H.Repr iv mem' (VG.Proof.MdStream.AArch64.Update.st s₀) (m ++ (VG.Proof.MdStream.AArch64.Update.D s₀).take c)

/-- All the data is absorbed, and nothing is pending. -/
def Done {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  VG.Proof.MdStream.AArch64.Update.Inv H s₀ (VG.Proof.MdStream.AArch64.Update.len s₀) s ∧ s.gpr .x10 = 0

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.MdStream.AArch64.Update.Common P s₀ c s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x22], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    VG.Proof.MdStream.AArch64.Update.Common P s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  x19 := by rw [hg _ (by simp)]; exact h.x19
  x20 := by rw [hg _ (by simp)]; exact h.x20
  sp := hsp.trans h.sp
  x21 := by rw [hg _ (by simp)]; exact h.x21
  x22 := by rw [hg _ (by simp)]; exact h.x22
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c s)
    (hg : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    VG.Proof.MdStream.AArch64.Update.Inv H s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_append_left [_] hr)) hm hrd hwr hsp with
    x23 := by rw [hg _ (by simp)]; exact h.x23
    repr := by rw [hm]; exact h.repr }

/-- Where the caller's registers are saved. -/
theorem saved_sub (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved P) :
    Region.Sub ⟨VG.Proof.MdStream.AArch64.Update.scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (VG.Proof.MdStream.AArch64.Update.scR P s₀) := by
  have := VG.Proof.MdStream.AArch64.saved_offset hd hp; have hd_so := hd.so
  exact VG.Proof.MdStream.AArch64.sub_offset (by omega_using [this]) (by omega)

/-- The saved registers survive a write to the state. -/
theorem Saved.of_frame (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {m m' : Mem}
    (hs : VG.Proof.MdStream.AArch64.Saved P (VG.Proof.MdStream.AArch64.Update.scr s₀) s₀.gpr m) (hf : Frame [VG.Proof.MdStream.AArch64.Update.stR P s₀] m m') : VG.Proof.MdStream.AArch64.Saved P (VG.Proof.MdStream.AArch64.Update.scr s₀) s₀.gpr m' := by
  intro p hp'
  rw [← hs p hp']
  refine hf.readW (r := ⟨VG.Proof.MdStream.AArch64.Update.scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (VG.Proof.MdStream.AArch64.Update.saved_sub hd hp')

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < VG.Proof.MdStream.AArch64.Update.len s₀) :
    (VG.Proof.MdStream.AArch64.Update.D s₀).getD i 0 = s₀.mem (VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c : Nat} {s : State} (h : VG.Proof.MdStream.AArch64.Update.Common P s₀ c s) {i : Nat}
    (hi : i < VG.Proof.MdStream.AArch64.Update.len s₀) : s.mem (VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 i) = (VG.Proof.MdStream.AArch64.Update.D s₀).getD i 0 := by
  rw [VG.Proof.MdStream.AArch64.Update.D_getD s₀ hi]
  exact VG.Proof.MdStream.AArch64.frame_bytes h.frame (R := VG.Proof.MdStream.AArch64.Update.dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (Nat.le_of_lt (VG.Proof.MdStream.AArch64.Update.len_lt s₀)) hi

theorem length_mid (hd : VG.Proof.MdStream.AArch64.Dims P) (s₀ : State) {iv : H.HV} {m : List Byte} (hm : VG.Proof.MdStream.AArch64.Update.R₀ H s₀ iv m) {c : Nat}
    (hc : c ≤ VG.Proof.MdStream.AArch64.Update.len s₀) : (m ++ (VG.Proof.MdStream.AArch64.Update.D s₀).take c).length % P.B = (VG.Proof.MdStream.AArch64.Update.cnt s₀ + c) % P.B := by
  have := hm.length hd
  simp only [List.length_append, List.length_take, VG.Proof.MdStream.AArch64.Update.D_length, Nat.min_eq_left hc]
  rw [Nat.add_mod, ← this, ← Nat.add_mod]

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (VG.Proof.MdStream.AArch64.Update.D s₀).take c ++ ((VG.Proof.MdStream.AArch64.Update.D s₀).drop c).take t = m ++ (VG.Proof.MdStream.AArch64.Update.D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-! ## Compressing pending blocks -/

theorem Pending.k_lt (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} {c k : Nat} {s : State} (h : VG.Proof.MdStream.AArch64.Update.Pending H s₀ c k s) :
    k < 2 ^ 64 := by
  have := VG.Proof.MdStream.AArch64.Update.len_lt s₀; have := Nat.le_mul_of_pos_left k hd.pos
  rcases h.src with ⟨_, rfl⟩ | ⟨c₀, _, hc₀⟩ <;> omega

theorem Pending.compress_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.AArch64.CalleeOk H code)
    {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c k : Nat} {s : State} (h : VG.Proof.MdStream.AArch64.Update.Pending H s₀ c k s) :
    WP isa (compressN name code) s (VG.Proof.MdStream.AArch64.Update.Inv H s₀ c) := by
  have hd_N := hd.N; have hd_so := hd.so; have hd_B := hd.B; have := VG.Proof.MdStream.AArch64.Update.len_lt s₀
  have eN : Region.Sub ⟨VG.Proof.MdStream.AArch64.Update.st s₀, P.N⟩ (VG.Proof.MdStream.AArch64.Update.stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.MdStream.AArch64.Update.scr s₀, P.so⟩ (VG.Proof.MdStream.AArch64.Update.scR P s₀) := Region.sub_prefix (by omega)
  have eSrc : Region.Sub ⟨s.gpr .x1, P.B * k⟩ (VG.Proof.MdStream.AArch64.Update.stR P s₀) ∨ Region.Sub ⟨s.gpr .x1, P.B * k⟩ (VG.Proof.MdStream.AArch64.Update.dR s₀) := by
    rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ VG.Proof.MdStream.AArch64.sub_offset (off := P.N) (by omega) (by omega))
    · exact .inr (h' ▸ VG.Proof.MdStream.AArch64.sub_offset (by omega) (by omega))
  have hk : (s.gpr .x10).toNat = k := by rw [h.x10, VG.Proof.MdStream.AArch64.toNat_ofNat_lt (h.k_lt hd)]
  refine VG.Proof.MdStream.AArch64.compressWith_ok (VG.Proof.MdStream.AArch64.setsN_x10 s) hk hf h.x19 h.x20 rfl ((hp.st_scr.sub_left eN).sub_right eso)
    ?_ ?_ ?_ ?_ ?_
  · rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · rw [h']; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hp.d_st.sub_left (h' ▸ VG.Proof.MdStream.AArch64.sub_offset (by omega) (by omega_using [hc₀, this]))).sub_right eN
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right eso
    · exact (hp.d_scr.sub_left e).sub_right eso
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
      · exact ⟨VG.Proof.MdStream.AArch64.Update.stR P s₀, by simp, P.N, h', by simp⟩
      · exact ⟨VG.Proof.MdStream.AArch64.Update.dR s₀, by simp, c₀, h', hc₀⟩
    · exact ⟨VG.Proof.MdStream.AArch64.Update.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.AArch64.Update.scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.MdStream.AArch64.Update.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.AArch64.Update.scR P s₀, by simp, 0, by simp, by simp⟩
  · intro s' hrd hwr hcs hsp hf' hstate
    have cs : ∀ r, r ∈ preserved → r ≠ .x30 → s'.gpr r = s.gpr r := hcs
    refine ⟨⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [cs _ (by decide) (by decide)]; exact h.x19,
      by rw [cs _ (by decide) (by decide)]; exact h.x20, hsp.trans h.sp,
      by rw [cs _ (by decide) (by decide)]; exact h.x21,
      by rw [cs _ (by decide) (by decide)]; exact h.x22,
      h.frame.trans (hf'.sub ?_), fun p hp' => ?_⟩, ?_, fun iv m hm => h.repr iv m hm _ hstate⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.MdStream.AArch64.Update.stR P s₀, by simp, eN⟩
      · exact ⟨VG.Proof.MdStream.AArch64.Update.scR P s₀, by simp, eso⟩
    · rw [← h.saved p hp']
      have := VG.Proof.MdStream.AArch64.saved_offset hd hp'
      refine hf'.readW (r := ⟨VG.Proof.MdStream.AArch64.Update.scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (VG.Proof.MdStream.AArch64.Update.saved_sub hd hp')).sub_right eN
      · exact Offset.disjoint_base _ (by omega_using [this]) (by omega)
    · rw [cs _ (by decide) (by decide), h.x23, h.mod]; rfl

/-! ## Whole blocks straight from the data -/

theorem direct_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c s)
    (hr : (VG.Proof.MdStream.AArch64.Update.cnt s₀ + c) % P.B = 0) (hl : P.B ≤ VG.Proof.MdStream.AArch64.Update.len s₀ - c) :
    WP isa (.block (direct P)) s
      (VG.Proof.MdStream.AArch64.Update.Pending H s₀ (c + P.B * ((VG.Proof.MdStream.AArch64.Update.len s₀ - c) / P.B)) ((VG.Proof.MdStream.AArch64.Update.len s₀ - c) / P.B)) := by
  have hlen := VG.Proof.MdStream.AArch64.Update.len_lt s₀; have hB := hd.pos; have hc := hI.c_le
  have hdm := Nat.div_add_mod (VG.Proof.MdStream.AArch64.Update.len s₀ - c) P.B
  have hq1 : 0 < (VG.Proof.MdStream.AArch64.Update.len s₀ - c) / P.B := Nat.div_pos hl hd.pos
  have hsh := hd.shr (a := VG.Proof.MdStream.AArch64.Update.len s₀ - c) (by omega)
  have hsl := hd.shl (a := (VG.Proof.MdStream.AArch64.Update.len s₀ - c) / P.B) (by omega)
  generalize (VG.Proof.MdStream.AArch64.Update.len s₀ - c) / P.B = q at *
  have hq2 : P.B * q ≤ VG.Proof.MdStream.AArch64.Update.len s₀ - c := by omega
  unfold direct
  have h63 : lg P < 64 := by have hd_log := hd.log; omega
  refine VG.Proof.MdStream.AArch64.wp_mov fun s₁ u₁ => VG.Proof.MdStream.AArch64.wp_lsr h63 fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_lsl h63 fun s₃ u₃ =>
    VG.Proof.MdStream.AArch64.wp_add fun s₄ u₄ => VG.Proof.MdStream.AArch64.wp_sub fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x1 → r ≠ .x10 → r ≠ .x9 → r ≠ .x21 → r ≠ .x22 → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h1 : s₅.gpr .x1 = VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 c := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, hI.x21]
  have h10 : s₅.gpr .x10 = BitVec.ofNat 64 q := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), hI.x22, hsh]
  have h9 : s₃.gpr .x9 = BitVec.ofNat 64 (P.B * q) := by
    rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), hI.x22, hsh, hsl]
  have h9' : s₄.gpr .x9 = BitVec.ofNat 64 (P.B * q) := by rw [u₄.other _ (by decide), h9]
  refine ⟨⟨by omega, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.x19],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.x20],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, by rw [m₅]; exact hI.frame,
    by rw [m₅]; exact hI.saved⟩, ?_, h10, hq1, ?_, .inr ⟨c, h1, by omega⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.gpr, h9, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.x21, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₅.gpr, h9', u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.x22, VG.Proof.MdStream.AArch64.sub_ofNat (by omega), Nat.sub_sub]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.x23, hr]; rfl
  · rw [← Nat.add_assoc, Nat.add_mul_mod_self_left]; exact hr
  · intro iv m hm mem' hs
    have hmod := VG.Proof.MdStream.AArch64.Update.length_mid hd s₀ hm (c := c) (by omega)
    rw [← VG.Proof.MdStream.AArch64.Update.take_add_data]
    refine H.repr_append_blocks (n := q) hd.pos (hI.repr iv m hm) (by rw [hmod, hr])
      (by rw [List.length_take, List.length_drop, VG.Proof.MdStream.AArch64.Update.D_length]; omega) ?_
    rw [hs, m₅, h1]
    apply H.compressBlocks_eq
    intro j hj
    rw [VG.Proof.MdStream.AArch64.add_ofNat, hI.data hp (by omega_using [hj, hdm])]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hj]

/-! ## Buffering data -/

section
variable (P) (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (VG.Proof.MdStream.AArch64.Update.cnt s₀ + c) % P.B
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (P.B - VG.Proof.MdStream.AArch64.Update.rr P s₀ c) (VG.Proof.MdStream.AArch64.Update.len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := VG.Proof.MdStream.AArch64.Update.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Update.rr P s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((VG.Proof.MdStream.AArch64.Update.D s₀).drop c).take (VG.Proof.MdStream.AArch64.Update.tt P s₀ c)
end

theorem rr_lt (hd : VG.Proof.MdStream.AArch64.Dims P) (s₀ : State) (c : Nat) : VG.Proof.MdStream.AArch64.Update.rr P s₀ c < P.B := Nat.mod_lt _ hd.pos
theorem tt_le (s₀ : State) (c : Nat) : VG.Proof.MdStream.AArch64.Update.tt P s₀ c ≤ VG.Proof.MdStream.AArch64.Update.len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : VG.Proof.MdStream.AArch64.Update.tt P s₀ c ≤ P.B - VG.Proof.MdStream.AArch64.Update.rr P s₀ c := Nat.min_le_left _ _
theorem rr_eq (s₀ : State) (c : Nat) : VG.Proof.MdStream.AArch64.Update.rr P s₀ c = (VG.Proof.MdStream.AArch64.Update.cnt s₀ + c) % P.B := rfl
theorem tt_eq (s₀ : State) (c : Nat) : VG.Proof.MdStream.AArch64.Update.tt P s₀ c = min (P.B - VG.Proof.MdStream.AArch64.Update.rr P s₀ c) (VG.Proof.MdStream.AArch64.Update.len s₀ - c) := rfl

theorem q_eq (s₀ : State) (c : Nat) : VG.Proof.MdStream.AArch64.Update.q P s₀ c = VG.Proof.MdStream.AArch64.Update.st s₀ + BitVec.ofNat 64 (P.N + VG.Proof.MdStream.AArch64.Update.rr P s₀ c) :=
  VG.Proof.MdStream.AArch64.add_ofNat _ _ _

theorem xs_length (s₀ : State) (c : Nat) : (VG.Proof.MdStream.AArch64.Update.xs P s₀ c).length = VG.Proof.MdStream.AArch64.Update.tt P s₀ c := by
  have := VG.Proof.MdStream.AArch64.Update.tt_le (P := P) s₀ c
  simp only [VG.Proof.MdStream.AArch64.Update.xs, List.length_take, List.length_drop, VG.Proof.MdStream.AArch64.Update.D_length]; omega

end

/-- The state while copying: `j` bytes copied, into memory otherwise as in `mI`. -/
structure Copy (P : Params) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ VG.Proof.MdStream.AArch64.Update.tt P s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  x19 : s.gpr .x19 = VG.Proof.MdStream.AArch64.Update.st s₀
  x20 : s.gpr .x20 = VG.Proof.MdStream.AArch64.Update.scr s₀
  sp : s.sp = s₀.sp
  x21 : s.gpr .x21 = VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 (c + j)
  x22 : s.gpr .x22 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Update.len s₀ - c - VG.Proof.MdStream.AArch64.Update.tt P s₀ c)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Update.rr P s₀ c + j)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Update.tt P s₀ c - j)
  x10 : s.gpr .x10 = 0
  mem : s.mem = VG.WriteBytes.writeBytes mI (VG.Proof.MdStream.AArch64.Update.q P s₀ c) ((VG.Proof.MdStream.AArch64.Update.xs P s₀ c).take j)

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem write_frame (hd : VG.Proof.MdStream.AArch64.Dims P) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ VG.Proof.MdStream.AArch64.Update.tt P s₀ c) :
    Frame [VG.Proof.MdStream.AArch64.Update.stR P s₀] mI (VG.WriteBytes.writeBytes mI (VG.Proof.MdStream.AArch64.Update.q P s₀ c) ((VG.Proof.MdStream.AArch64.Update.xs P s₀ c).take j)) := by
  have := VG.Proof.MdStream.AArch64.Update.tt_le' (P := P) s₀ c; have := VG.Proof.MdStream.AArch64.Update.rr_lt hd s₀ c; have hd_N := hd.N; have hd_B := hd.B
  refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
  rw [VG.Proof.MdStream.AArch64.Update.q_eq]
  exact VG.Proof.MdStream.AArch64.contains_offset (by simp only [List.length_take]; omega) (by omega)

theorem copy_step (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c sI)
    {j : Nat} (hj : j < VG.Proof.MdStream.AArch64.Update.tt P s₀ c) {s : State} (h : VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem j s) :
    WP isa (.block (copyBody P)) s fun s' =>
      VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem (j + 1) s' ∧ s'.gpr .x11 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Update.tt P s₀ c - (j + 1)) := by
  have hlen := VG.Proof.MdStream.AArch64.Update.len_lt s₀
  have hc := hI.c_le
  have hr := VG.Proof.MdStream.AArch64.Update.rr_lt hd s₀ c
  have ht := VG.Proof.MdStream.AArch64.Update.tt_le (P := P) s₀ c; have ht' := VG.Proof.MdStream.AArch64.Update.tt_le' (P := P) s₀ c
  have hd_N := hd.N; have hd_B := hd.B
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨VG.Proof.MdStream.AArch64.Update.dR s₀, by simp [h.rd, hp.rd], VG.Proof.MdStream.AArch64.contains_offset (by omega_using [ht, hj]) (by omega_using [ht, hlen, hj])⟩
  have hbyte : s.mem (VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 (c + j)) = (VG.Proof.MdStream.AArch64.Update.D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega_using [ht, hj])]
    exact VG.Proof.MdStream.AArch64.frame_bytes (VG.Proof.MdStream.AArch64.Update.write_frame hd s₀ c sI.mem j h.j_le) (R := VG.Proof.MdStream.AArch64.Update.dR s₀) (by simpa using hp.d_st)
      (by show VG.Proof.MdStream.AArch64.Update.len s₀ ≤ 2 ^ 64; omega) (by show c + j < VG.Proof.MdStream.AArch64.Update.len s₀; omega)
  -- The byte written.
  have hout : InRegions s.wr (VG.Proof.MdStream.AArch64.Update.q P s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨VG.Proof.MdStream.AArch64.Update.stR P s₀, by simp [h.wr, hp.wr], by
      rw [VG.Proof.MdStream.AArch64.Update.q_eq, VG.Proof.MdStream.AArch64.add_ofNat]; exact VG.Proof.MdStream.AArch64.contains_offset (by omega_using [ht', hj]) (by omega)⟩
  have hxs := VG.Proof.MdStream.AArch64.Update.xs_length (P := P) s₀ c
  unfold copyBody
  refine VG.Proof.MdStream.AArch64.wp_ldrb (a := VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 (c + j)) (by omega) (by rw [h.x21]; simp) hin
    fun s₁ u₁ => ?_
  refine VG.Proof.MdStream.AArch64.wp_add fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_strb (a := VG.Proof.MdStream.AArch64.Update.q P s₀ c + BitVec.ofNat 64 j) (by omega) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h.x19, h.x23, VG.Proof.MdStream.AArch64.Update.q, VG.Proof.MdStream.AArch64.Update.buf]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine VG.Proof.MdStream.AArch64.wp_addImm (by decide) fun s₄ u₄ => VG.Proof.MdStream.AArch64.wp_addImm (by decide) fun s₅ u₅ =>
    VG.Proof.MdStream.AArch64.wp_subImm (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x21 → r ≠ .x23 → r ≠ .x11 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have hx11 : s₆.gpr .x11 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Update.tt P s₀ c - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.x11, VG.Proof.MdStream.AArch64.sub_ofNat (by omega_using [hj]), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx11, ?_, ?_⟩, hx11⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by decide) (by decide) (by decide) (by decide) (by decide), h.x20]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.x21, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .x22 (by decide) (by decide) (by decide) (by decide) (by decide), h.x22]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.x23, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .x10 (by decide) (by decide) (by decide) (by decide) (by decide), h.x10]
  · have hj' : j < (VG.Proof.MdStream.AArch64.Update.xs P s₀ c).length := by omega
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
      List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega_using [ht, hlen])]
    have hl : (List.take j (VG.Proof.MdStream.AArch64.Update.xs P s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl]
    have e : ((List.getD (VG.Proof.MdStream.AArch64.Update.D s₀) (c + j) 0).setWidth 64).setWidth 8 = List.getD (VG.Proof.MdStream.AArch64.Update.D s₀) (c + j) 0 := by
      ext i hi; simp
    rw [e]
    congr 1
    simp only [VG.Proof.MdStream.AArch64.Update.xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (VG.Proof.MdStream.AArch64.Update.D s₀).length by rw [VG.Proof.MdStream.AArch64.Update.D_length]; omega_using [ht, hj]), Option.getD_some]

theorem copy_loop_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c sI)
    {j₀ : Nat} {s : State} (h : VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem j₀ s) (ht : j₀ < VG.Proof.MdStream.AArch64.Update.tt P s₀ c) :
    WP isa (.loop (.block (copyBody P)) (.nonzero .x .x11)) s (VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem (VG.Proof.MdStream.AArch64.Update.tt P s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = VG.Proof.MdStream.AArch64.Update.tt P s₀ c - j ∧ j < VG.Proof.MdStream.AArch64.Update.tt P s₀ c ∧ VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem j s)
    ?_ (VG.Proof.MdStream.AArch64.Update.tt P s₀ c - j₀) s ⟨j₀, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (VG.Proof.MdStream.AArch64.Update.copy_step hd hp hI hj hc) fun s' ⟨hc', h11⟩ => ?_
  have hz : isa.eval (.nonzero .x .x11) s' = some (decide (VG.Proof.MdStream.AArch64.Update.tt P s₀ c - (j + 1) ≠ 0)) := by
    show VG.AArch64.eval (.nonzero .x .x11) s' = _
    rw [VG.Proof.MdStream.AArch64.eval_nonzero, h11, bne, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by have := VG.Proof.MdStream.AArch64.Update.tt_le' (P := P) s₀ c; have hd_B := hd.B; omega)]
    simp
  by_cases hl : VG.Proof.MdStream.AArch64.Update.tt P s₀ c - (j + 1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [show j + 1 = VG.Proof.MdStream.AArch64.Update.tt P s₀ c by omega] at hc'
  · exact .inr ⟨by rw [hz]; simp [hl], _, by omega, j + 1, rfl, by omega, hc'⟩

theorem Copy.of_gpr {s₀ : State} {c : Nat} {mI : Mem} {j : Nat} {s s' : State} (h : VG.Proof.MdStream.AArch64.Update.Copy P s₀ c mI j s)
    (hg : ∀ r, r ≠ .x13 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : VG.Proof.MdStream.AArch64.Update.Copy P s₀ c mI j s' :=
  ⟨h.j_le, hrd.trans h.rd, hwr.trans h.wr, by rw [hg _ (by decide), h.x19],
    by rw [hg _ (by decide), h.x20], hsp.trans h.sp, by rw [hg _ (by decide), h.x21],
    by rw [hg _ (by decide), h.x22], by rw [hg _ (by decide), h.x23],
    by rw [hg _ (by decide), h.x11], by rw [hg _ (by decide), h.x10], by rw [hm, h.mem]⟩

theorem xs_chunk (s₀ : State) (c : Nat) {j : Nat} (hj : j + 8 ≤ VG.Proof.MdStream.AArch64.Update.tt P s₀ c) :
    ((VG.Proof.MdStream.AArch64.Update.xs P s₀ c).drop j).take 8 = (List.range 8).map fun k => (VG.Proof.MdStream.AArch64.Update.D s₀).getD (c + j + k) 0 := by
  have ht := VG.Proof.MdStream.AArch64.Update.tt_le (P := P) s₀ c
  have hxs := VG.Proof.MdStream.AArch64.Update.xs_length (P := P) s₀ c
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range, hxs]; omega
  · intro k h1 h2
    have hk : k < 8 := by simpa using h2
    simp only [VG.Proof.MdStream.AArch64.Update.xs, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD, Nat.add_assoc]
    rw [List.getElem?_eq_getElem (by rw [VG.Proof.MdStream.AArch64.Update.D_length]; omega), Option.getD_some]

theorem copy_word_step (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c : Nat} {sI : State}
    (hI : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c sI) {j : Nat} (hj : j + 8 ≤ VG.Proof.MdStream.AArch64.Update.tt P s₀ c) {s : State} (h : VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem j s) :
    WP isa (.block (copyWordBody P)) s fun s' =>
      VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem (j + 8) s' ∧ s'.gpr .x13 = BitVec.ofNat 64 ((VG.Proof.MdStream.AArch64.Update.tt P s₀ c - (j + 8)) / 8) := by
  have hlen := VG.Proof.MdStream.AArch64.Update.len_lt s₀
  have hc := hI.c_le
  have hr := VG.Proof.MdStream.AArch64.Update.rr_lt hd s₀ c
  have ht := VG.Proof.MdStream.AArch64.Update.tt_le (P := P) s₀ c; have ht' := VG.Proof.MdStream.AArch64.Update.tt_le' (P := P) s₀ c
  have hd_N := hd.N; have hd_B := hd.B
  -- The bytes read.
  have hin : InRegions (s.rd ++ s.wr) (VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 (c + j)) 8 :=
    ⟨VG.Proof.MdStream.AArch64.Update.dR s₀, by simp [h.rd, hp.rd], VG.Proof.MdStream.AArch64.contains_offset (by omega_using [ht, hj]) (by omega_using [ht, hlen, hj])⟩
  have hbyte : ∀ k, k < 8 →
      s.mem (VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 (c + j) + BitVec.ofNat 64 k) = (VG.Proof.MdStream.AArch64.Update.D s₀).getD (c + j + k) 0 := by
    intro k hk
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.mem, ← hI.data hp (by omega_using [hk, ht, hj])]
    exact VG.Proof.MdStream.AArch64.frame_bytes (VG.Proof.MdStream.AArch64.Update.write_frame hd s₀ c sI.mem j h.j_le) (R := VG.Proof.MdStream.AArch64.Update.dR s₀) (by simpa using hp.d_st)
      (by show VG.Proof.MdStream.AArch64.Update.len s₀ ≤ 2 ^ 64; omega) (by show c + j + k < VG.Proof.MdStream.AArch64.Update.len s₀; omega)
  -- The bytes written.
  have hout : InRegions s.wr (VG.Proof.MdStream.AArch64.Update.q P s₀ c + BitVec.ofNat 64 j) 8 :=
    ⟨VG.Proof.MdStream.AArch64.Update.stR P s₀, by simp [h.wr, hp.wr], by
      rw [VG.Proof.MdStream.AArch64.Update.q_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; exact VG.Proof.MdStream.AArch64.contains_offset (by omega_using [ht', hj]) (by omega)⟩
  have hxs := VG.Proof.MdStream.AArch64.Update.xs_length (P := P) s₀ c
  unfold copyWordBody
  rw [List.cons_append, List.nil_append]
  refine VG.Proof.MdStream.AArch64.wp_ldr (a := VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 (c + j)) (by decide) (by rw [h.x21]; simp) hin
    fun s₁ u₁ => ?_
  refine VG.Proof.MdStream.AArch64.storeWord_ok (by omega) (a := VG.Proof.MdStream.AArch64.Update.q P s₀ c + BitVec.ofNat 64 j) ?_ (by rw [u₁.wr]; exact hout)
    fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  · rw [u₁.other _ (by decide), u₁.other _ (by decide), h.x19, h.x23, VG.Proof.MdStream.AArch64.Update.q, VG.Proof.MdStream.AArch64.Update.buf]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine VG.Proof.MdStream.AArch64.wp_addImm (by decide) fun s₄ u₄ => VG.Proof.MdStream.AArch64.wp_addImm (by decide) fun s₅ u₅ =>
    VG.Proof.MdStream.AArch64.wp_subImm (by decide) fun s₆ u₆ => VG.Proof.MdStream.AArch64.wp_lsr (by decide) fun s₇ u₇ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x9 → r ≠ .x12 → r ≠ .x21 → r ≠ .x23 → r ≠ .x11 → r ≠ .x13 →
      s₇.gpr r = s.gpr r := fun r h1 h2 h3 h4 h5 h6 => by
    rw [u₇.other r h6, u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃ r h2, u₁.other r h1]
  have hx11₆ : s₆.gpr .x11 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Update.tt P s₀ c - (j + 8)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide),
      u₁.other _ (by decide), h.x11, VG.Proof.MdStream.AArch64.sub_ofNat (by omega_using [hj]), Nat.sub_sub]
  have hx11 : s₇.gpr .x11 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Update.tt P s₀ c - (j + 8)) := by
    rw [u₇.other _ (by decide), hx11₆]
  have hx13 : s₇.gpr .x13 = BitVec.ofNat 64 ((VG.Proof.MdStream.AArch64.Update.tt P s₀ c - (j + 8)) / 8) := by
    rw [u₇.gpr, hx11₆, VG.Proof.MdStream.AArch64.ofNat_shr (by omega_using [ht, hlen])]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx11, ?_, ?_⟩, hx13⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, u₁.rd, h.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, u₁.wr, h.wr]
  · rw [g .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x20]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃, u₁.sp, h.sp]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃ _ (by decide),
      u₁.other _ (by decide), h.x21, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x22]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃ _ (by decide),
      u₁.other _ (by decide), h.x23, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.x10]
  · have hl : (List.take j (VG.Proof.MdStream.AArch64.Update.xs P s₀ c)).length = j := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    have hw : (List.range 8).map (fun k => (s.mem.readW (VG.Proof.MdStream.AArch64.Update.dp s₀ + BitVec.ofNat 64 (c + j)) 64).extractLsb' (8 * k) 8) =
        ((VG.Proof.MdStream.AArch64.Update.xs P s₀ c).drop j).take 8 := by
      rw [VG.Proof.MdStream.AArch64.Update.xs_chunk s₀ c hj]
      refine List.map_congr_left fun k hk => ?_
      have hk' : k < 8 := List.mem_range.mp hk
      rw [VG.Proof.MdStream.AArch64.extractLsb'_readW _ _ hk', hbyte k hk']
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, u₁.mem, u₁.gpr, VG.Proof.MdStream.AArch64.writeW_eq_writeBytes, hw, h.mem,
      show VG.Proof.MdStream.AArch64.Update.q P s₀ c + BitVec.ofNat 64 j = VG.Proof.MdStream.AArch64.Update.q P s₀ c + BitVec.ofNat 64 (List.take j (VG.Proof.MdStream.AArch64.Update.xs P s₀ c)).length by
        rw [hl],
      VG.WriteBytes.writeBytes_append _ _ _ _ (by simp only [List.length_take, List.length_drop]; omega),
      ← List.take_add]

theorem copy_words_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c : Nat} {sI : State}
    (hI : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c sI) {s : State} (h : VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem 0 s)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8)) :
    WP isa (.ite (.zero .x .x13) (.block []) (.loop (.block (copyWordBody P)) (.nonzero .x .x13))) s
      (VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem (8 * (VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8))) := by
  have ht' := VG.Proof.MdStream.AArch64.Update.tt_le' (P := P) s₀ c; have hd_B := hd.B
  have hz : eval (.zero .x .x13) s = some (decide (VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8 = 0)) := by
    rw [VG.Proof.MdStream.AArch64.eval_zero, h13, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by omega)]
  refine WP.ite (decide (VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8 = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (by rw [hb]; exact h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa)
      (fun n s => ∃ i, n = VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8 - i ∧ i < VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8 ∧ VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem (8 * i) s)
      ?_ (VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8) s ⟨0, rfl, by omega, h⟩
    rintro n s ⟨i, rfl, hi, hC⟩
    refine WP.mono (VG.Proof.MdStream.AArch64.Update.copy_word_step hd hp hI (by omega) hC) fun s' ⟨hC', h13'⟩ => ?_
    have hz' : isa.eval (.nonzero .x .x13) s' = some (decide (VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8 - (i + 1) ≠ 0)) := by
      show VG.AArch64.eval (.nonzero .x .x13) s' = _
      rw [VG.Proof.MdStream.AArch64.eval_nonzero, h13', show (VG.Proof.MdStream.AArch64.Update.tt P s₀ c - (8 * i + 8)) / 8 = VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8 - (i + 1) by omega,
        bne, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by omega)]
      simp
    rw [show 8 * i + 8 = 8 * (i + 1) by omega] at hC'
    by_cases hl : VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8 - (i + 1) = 0
    · refine .inl ⟨by rw [hz']; simp [hl], ?_⟩
      rwa [show i + 1 = VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8 by omega] at hC'
    · exact .inr ⟨by rw [hz']; simp [hl], _, by omega, i + 1, rfl, by omega, hC'⟩

theorem copy_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c sI)
    {s : State} (h : VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem 0 s) : WP isa (copy P) s (VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem (VG.Proof.MdStream.AArch64.Update.tt P s₀ c)) := by
  have ht' := VG.Proof.MdStream.AArch64.Update.tt_le' (P := P) s₀ c; have hd_B := hd.B
  unfold copy
  refine WP.seq (VG.Proof.MdStream.AArch64.wp_lsr (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hC₁ : VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem 0 s₁ := h.of_gpr u₁.other u₁.mem u₁.rd u₁.wr u₁.sp
  have h13 : s₁.gpr .x13 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8) := by
    rw [u₁.gpr, h.x11, Nat.sub_zero, VG.Proof.MdStream.AArch64.ofNat_shr (by omega)]
  refine WP.seq (WP.mono (VG.Proof.MdStream.AArch64.Update.copy_words_ok hd hp hI hC₁ h13) fun s₂ hC₂ => ?_)
  have hz : eval (.zero .x .x11) s₂ = some (decide (VG.Proof.MdStream.AArch64.Update.tt P s₀ c - 8 * (VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8) = 0)) := by
    rw [VG.Proof.MdStream.AArch64.eval_zero, hC₂.x11, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by omega)]
  refine WP.ite (decide (VG.Proof.MdStream.AArch64.Update.tt P s₀ c - 8 * (VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8) = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (by rwa [show 8 * (VG.Proof.MdStream.AArch64.Update.tt P s₀ c / 8) = VG.Proof.MdStream.AArch64.Update.tt P s₀ c by omega] at hC₂)
  · simp only [decide_eq_false_iff_not] at hb
    exact VG.Proof.MdStream.AArch64.Update.copy_loop_ok hd hp hI hC₂ (by omega)

/-- The memory after copying `tt` bytes. -/
theorem copied_facts (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c sI) :
    let mem := VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.AArch64.Update.q P s₀ c) (VG.Proof.MdStream.AArch64.Update.xs P s₀ c)
    Frame [VG.Proof.MdStream.AArch64.Update.stR P s₀, VG.Proof.MdStream.AArch64.Update.scR P s₀] s₀.mem mem ∧ VG.Proof.MdStream.AArch64.Saved P (VG.Proof.MdStream.AArch64.Update.scr s₀) s₀.gpr mem ∧
      H.stateAt mem (VG.Proof.MdStream.AArch64.Update.st s₀) = H.stateAt sI.mem (VG.Proof.MdStream.AArch64.Update.st s₀) ∧
      bytesAt mem (VG.Proof.MdStream.AArch64.Update.buf P s₀) (VG.Proof.MdStream.AArch64.Update.rr P s₀ c + VG.Proof.MdStream.AArch64.Update.tt P s₀ c) = bytesAt sI.mem (VG.Proof.MdStream.AArch64.Update.buf P s₀) (VG.Proof.MdStream.AArch64.Update.rr P s₀ c) ++ VG.Proof.MdStream.AArch64.Update.xs P s₀ c := by
  intro mem
  have hr := VG.Proof.MdStream.AArch64.Update.rr_lt hd s₀ c; have ht' := VG.Proof.MdStream.AArch64.Update.tt_le' (P := P) s₀ c; have hd_N := hd.N; have hd_B := hd.B
  have hxs := VG.Proof.MdStream.AArch64.Update.xs_length (P := P) s₀ c
  have hf : Frame [VG.Proof.MdStream.AArch64.Update.stR P s₀] sI.mem mem := by
    have := VG.Proof.MdStream.AArch64.Update.write_frame hd s₀ c sI.mem (VG.Proof.MdStream.AArch64.Update.tt P s₀ c) (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega)] at this
  refine ⟨hI.frame.trans (hf.mono (by simp)), Saved.of_frame hd hp hI.saved hf, ?_, ?_⟩
  · apply H.stateAt_congr
    intro i hi
    simp only [mem, VG.Proof.MdStream.AArch64.Update.q_eq]
    exact VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by omega)
  · rw [← hxs]
    exact bytesAt_writeBytes _ _ _ _ (by omega_using [hxs, hd_B, ht', hr])

/-- A full buffer: compress it. -/
theorem fill_pending (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c sI)
    {s : State} (h : VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem (VG.Proof.MdStream.AArch64.Update.tt P s₀ c) s) (hfull : VG.Proof.MdStream.AArch64.Update.rr P s₀ c + VG.Proof.MdStream.AArch64.Update.tt P s₀ c = P.B) :
    WP isa (.block [.addImm .x .x1 .x19 P.N, .movz .x .x23 0 0, .movz .x .x10 1 0]) s
      (VG.Proof.MdStream.AArch64.Update.Pending H s₀ (c + VG.Proof.MdStream.AArch64.Update.tt P s₀ c) 1) := by
  have ht' := VG.Proof.MdStream.AArch64.Update.tt_le' (P := P) s₀ c
  have hrr := VG.Proof.MdStream.AArch64.Update.rr_eq (P := P) s₀ c; have htt := VG.Proof.MdStream.AArch64.Update.tt_eq (P := P) s₀ c
  have hxs := VG.Proof.MdStream.AArch64.Update.xs_length (P := P) s₀ c
  have hc := hI.c_le
  have hd_N := hd.N; have hd_B := hd.B
  obtain ⟨hfr, hsv, hst, hby⟩ := VG.Proof.MdStream.AArch64.Update.copied_facts hd hp hI
  have hmem : s.mem = VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.AArch64.Update.q P s₀ c) (VG.Proof.MdStream.AArch64.Update.xs P s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine VG.Proof.MdStream.AArch64.wp_addImm (by omega) fun s₁ u₁ => VG.Proof.MdStream.AArch64.wp_movz fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_movz fun s₃ u₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .x1 → r ≠ .x23 → r ≠ .x10 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hx1 : s₃.gpr .x1 = VG.Proof.MdStream.AArch64.Update.buf P s₀ := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x19]
  refine ⟨⟨by omega_using [hc, htt], ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₃, hmem]; exact hfr, by rw [m₃, hmem]; exact hsv⟩,
    by rw [u₃.other _ (by decide), u₂.gpr]; rfl, by rw [u₃.gpr]; rfl, Nat.one_pos,
    by rw [← Nat.add_assoc]; exact Md.add_mod_of_eq hfull, .inl ⟨hx1, rfl⟩,
    ?_⟩
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .x19 (by decide) (by decide) (by decide), h.x19]
  · rw [g .x20 (by decide) (by decide) (by decide), h.x20]
  · rw [u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [g .x21 (by decide) (by decide) (by decide), h.x21]
  · rw [g .x22 (by decide) (by decide) (by decide), h.x22, Nat.sub_sub]
  · intro iv m hm mem' hs
    rw [Md.compressBlocks_one] at hs
    rw [← VG.Proof.MdStream.AArch64.Update.take_add_data]
    have hmod := VG.Proof.MdStream.AArch64.Update.length_mid hd s₀ hm hc
    refine H.repr_append_block hd.pos (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₃, hmem, hst, hx1]
    refine congrArg (H.compress _) (H.parse_congr fun k hk => ?_)
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show VG.Proof.MdStream.AArch64.Update.rr P s₀ c + VG.Proof.MdStream.AArch64.Update.tt P s₀ c = P.B from hfull] at hby
    exact VG.Proof.MdStream.AArch64.bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c sI)
    {s : State} (h : VG.Proof.MdStream.AArch64.Update.Copy P s₀ c sI.mem (VG.Proof.MdStream.AArch64.Update.tt P s₀ c) s) (hnf : VG.Proof.MdStream.AArch64.Update.rr P s₀ c + VG.Proof.MdStream.AArch64.Update.tt P s₀ c ≠ P.B) : VG.Proof.MdStream.AArch64.Update.Done H s₀ s := by
  have hr := VG.Proof.MdStream.AArch64.Update.rr_lt hd s₀ c; have ht' := VG.Proof.MdStream.AArch64.Update.tt_le' (P := P) s₀ c
  have hrr := VG.Proof.MdStream.AArch64.Update.rr_eq (P := P) s₀ c; have htt := VG.Proof.MdStream.AArch64.Update.tt_eq (P := P) s₀ c
  have hxs := VG.Proof.MdStream.AArch64.Update.xs_length (P := P) s₀ c
  have hc := hI.c_le
  have htl : VG.Proof.MdStream.AArch64.Update.tt P s₀ c = VG.Proof.MdStream.AArch64.Update.len s₀ - c := by omega
  obtain ⟨hfr, hsv, hst, hby⟩ := VG.Proof.MdStream.AArch64.Update.copied_facts hd hp hI
  have hmem : s.mem = VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.AArch64.Update.q P s₀ c) (VG.Proof.MdStream.AArch64.Update.xs P s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine ⟨⟨⟨(Nat.le_refl _), h.rd, h.wr, h.x19, h.x20, h.sp, ?_, ?_, by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩, h.x10⟩
  · rw [h.x21]; congr 2; omega_using [htl, hc]
  · rw [h.x22]; congr 1; omega_using [htl]
  · rw [h.x23, show VG.Proof.MdStream.AArch64.Update.cnt s₀ + VG.Proof.MdStream.AArch64.Update.len s₀ = VG.Proof.MdStream.AArch64.Update.cnt s₀ + c + VG.Proof.MdStream.AArch64.Update.tt P s₀ c by omega_using [htl, hc],
      Md.add_mod_of_lt (by omega_using [hr, ht', hnf, hrr])]
  · have hmod := VG.Proof.MdStream.AArch64.Update.length_mid hd s₀ hm hc
    rw [show VG.Proof.MdStream.AArch64.Update.len s₀ = c + VG.Proof.MdStream.AArch64.Update.tt P s₀ c by omega_using [htl, hc], ← VG.Proof.MdStream.AArch64.Update.take_add_data]
    refine H.repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega_using [hrr, ht', hr, hnf]) (by rw [hmem, hst]) ?_
    rw [hmod, hxs, hmem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c s)
    (hcl : c < VG.Proof.MdStream.AArch64.Update.len s₀) (h10 : s.gpr .x10 = 0) :
    WP isa (fill P) s fun s' => (∃ c' k, c < c' ∧ VG.Proof.MdStream.AArch64.Update.Pending H s₀ c' k s') ∨ VG.Proof.MdStream.AArch64.Update.Done H s₀ s' := by
  have ht' := VG.Proof.MdStream.AArch64.Update.tt_le' (P := P) s₀ c; have hr := VG.Proof.MdStream.AArch64.Update.rr_lt hd s₀ c
  have hrr := VG.Proof.MdStream.AArch64.Update.rr_eq (P := P) s₀ c; have htt := VG.Proof.MdStream.AArch64.Update.tt_eq (P := P) s₀ c
  have ne : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], r ≠ .x9 ∧ r ≠ .x11 := by decide
  have hlen := VG.Proof.MdStream.AArch64.Update.len_lt s₀
  have hB := hd.B
  have h63 : lg P < 64 := by have hd_log := hd.log; omega
  unfold fill
  -- `x11 := B - r; x9 := len >> log₂ B`
  refine WP.seq (VG.Proof.MdStream.AArch64.wp_movz fun s₁ u₁ => VG.Proof.MdStream.AArch64.wp_sub fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_lsr h63 fun s₃ u₃ => WP.block_nil ?_)
  have e₃ : ∀ r, r ≠ .x9 → r ≠ .x11 → s₃.gpr r = s.gpr r := fun r h h' => by
    rw [u₃.other r h, u₂.other r h', u₁.other r h']
  have hI₃ : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c s₃ := hI.of_gpr (fun r hr => e₃ r (ne r hr).1 (ne r hr).2)
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp])
  have h11₃ : s₃.gpr .x11 = BitVec.ofNat 64 (P.B - VG.Proof.MdStream.AArch64.Update.rr P s₀ c) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.x23, hd.movB, VG.Proof.MdStream.AArch64.sub_ofNat (by omega)]
  have h9₃ : s₃.gpr .x9 = BitVec.ofNat 64 ((VG.Proof.MdStream.AArch64.Update.len s₀ - c) / P.B) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.x22, hd.shr (by omega)]
  -- `x11 := min(x11, len)`
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => VG.Proof.MdStream.AArch64.Update.Inv H s₀ c s₄ ∧ s₄.gpr .x11 = BitVec.ofNat 64 (VG.Proof.MdStream.AArch64.Update.tt P s₀ c) ∧
    s₄.gpr .x10 = 0 ∧ s₄.mem = s.mem) ?_ fun s₄ ⟨hI₄, h11₄, h10₄, hm₄⟩ => ?_)
  · have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    have h10₃ : s₃.gpr .x10 = 0 := by rw [e₃ _ (by decide) (by decide), h10]
    refine WP.ite (decide ((VG.Proof.MdStream.AArch64.Update.len s₀ - c) / P.B = 0))
      (by show VG.AArch64.eval (.zero .x .x9) s₃ = _
          rw [VG.Proof.MdStream.AArch64.eval_zero, h9₃, VG.Proof.MdStream.AArch64.ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq, Nat.div_eq_zero_iff_lt hd.pos] at hb
      refine WP.seq (VG.Proof.MdStream.AArch64.wp_add fun s₅ u₅ => VG.Proof.MdStream.AArch64.wp_lsr h63 fun s₆ u₆ => WP.block_nil ?_)
      have e₆ : ∀ r, r ≠ .x9 → s₆.gpr r = s₃.gpr r := fun r h => by rw [u₆.other r h, u₅.other r h]
      have hI₆ : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c s₆ := hI₃.of_gpr (fun r hr => e₆ r (ne r hr).1) (by rw [u₆.mem, u₅.mem])
        (by rw [u₆.rd, u₅.rd]) (by rw [u₆.wr, u₅.wr]) (by rw [u₆.sp, u₅.sp])
      have h9₆ : s₆.gpr .x9 = BitVec.ofNat 64 ((VG.Proof.MdStream.AArch64.Update.len s₀ - c + VG.Proof.MdStream.AArch64.Update.rr P s₀ c) / P.B) := by
        rw [u₆.gpr, u₅.gpr, hI₃.x22, hI₃.x23, ← BitVec.ofNat_add, hd.shr (by omega_using [hb, hB, hrr, hr])]
      refine WP.ite (decide ((VG.Proof.MdStream.AArch64.Update.len s₀ - c + VG.Proof.MdStream.AArch64.Update.rr P s₀ c) / P.B = 0))
        (by show VG.AArch64.eval (.zero .x .x9) s₆ = _
            rw [VG.Proof.MdStream.AArch64.eval_zero, h9₆, VG.Proof.MdStream.AArch64.ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hb, hB, hr]))])
        (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq, Nat.div_eq_zero_iff_lt hd.pos] at hb'
        refine VG.Proof.MdStream.AArch64.wp_mov fun s₇ u₇ => WP.block_nil ⟨hI₆.of_gpr (fun r hr => u₇.other r (ne r hr).2)
          u₇.mem u₇.rd u₇.wr u₇.sp,
          ?_, by rw [u₇.other _ (by decide), e₆ _ (by decide), h10₃], by rw [u₇.mem, u₆.mem, u₅.mem, hm₃]⟩
        rw [u₇.gpr, hI₆.x22]; congr 1; omega_using [hb', htt]
      · simp only [decide_eq_false_iff_not, Nat.div_eq_zero_iff_lt hd.pos] at hb'
        refine WP.block_nil ⟨hI₆, ?_, by rw [e₆ _ (by decide), h10₃], by rw [u₆.mem, u₅.mem, hm₃]⟩
        rw [e₆ _ (by decide), h11₃]; congr 1; omega
    · simp only [decide_eq_false_iff_not, Nat.div_eq_zero_iff_lt hd.pos] at hb
      refine WP.block_nil ⟨hI₃, ?_, h10₃, hm₃⟩
      rw [h11₃]; congr 1; omega_using [hb, htt]
  -- `x22 -= x11`
  refine WP.seq (VG.Proof.MdStream.AArch64.wp_sub fun s₅ u₅ => WP.block_nil ?_)
  have hC₀ : VG.Proof.MdStream.AArch64.Update.Copy P s₀ c s.mem 0 s₅ := by
    have e : ∀ r, r ≠ .x22 → s₅.gpr r = s₄.gpr r := fun r h => u₅.other r h
    refine ⟨Nat.zero_le _, by rw [u₅.rd, hI₄.rd], by rw [u₅.wr, hI₄.wr],
      by rw [e _ (by decide), hI₄.x19], by rw [e _ (by decide), hI₄.x20], by rw [u₅.sp, hI₄.sp],
      by rw [e _ (by decide), hI₄.x21, Nat.add_zero], ?_, by rw [e _ (by decide), hI₄.x23, Nat.add_zero],
      by rw [e _ (by decide), h11₄, Nat.sub_zero], by rw [e _ (by decide), h10₄], ?_⟩
    · rw [u₅.gpr, hI₄.x22, h11₄, VG.Proof.MdStream.AArch64.sub_ofNat (by omega), Nat.sub_sub]
    · rw [u₅.mem, hm₄, List.take_zero, VG.WriteBytes.writeBytes_nil]
  -- Copy the data.
  refine WP.seq (WP.mono (VG.Proof.MdStream.AArch64.Update.copy_ok hd hp hI hC₀) fun s₆ hC => ?_)
  -- Is the buffer full?
  refine WP.seq (VG.Proof.MdStream.AArch64.wp_subImm (by omega) fun s₇ u₇ => WP.block_nil ?_)
  have hC₇ : VG.Proof.MdStream.AArch64.Update.Copy P s₀ c s.mem (VG.Proof.MdStream.AArch64.Update.tt P s₀ c) s₇ :=
    ⟨hC.j_le, by rw [u₇.rd, hC.rd], by rw [u₇.wr, hC.wr], by rw [u₇.other _ (by decide), hC.x19],
      by rw [u₇.other _ (by decide), hC.x20], by rw [u₇.sp, hC.sp], by rw [u₇.other _ (by decide), hC.x21],
      by rw [u₇.other _ (by decide), hC.x22], by rw [u₇.other _ (by decide), hC.x23],
      by rw [u₇.other _ (by decide), hC.x11], by rw [u₇.other _ (by decide), hC.x10],
      by rw [u₇.mem, hC.mem]⟩
  have hz : eval (.zero .x .x9) s₇ = some (decide (VG.Proof.MdStream.AArch64.Update.rr P s₀ c + VG.Proof.MdStream.AArch64.Update.tt P s₀ c = P.B)) := by
    rw [VG.Proof.MdStream.AArch64.eval_zero, u₇.gpr, hC.x23, VG.Proof.MdStream.AArch64.sub_beq (by omega_using [hB, hr, ht']) (by omega)]
  refine WP.ite (decide (VG.Proof.MdStream.AArch64.Update.rr P s₀ c + VG.Proof.MdStream.AArch64.Update.tt P s₀ c = P.B)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (VG.Proof.MdStream.AArch64.Update.fill_pending hd hp hI hC₇ hb) fun s' h => .inl ⟨c + VG.Proof.MdStream.AArch64.Update.tt P s₀ c, 1, by omega, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (VG.Proof.MdStream.AArch64.Update.fill_done hd hp hI hC₇ hb))

/-! ## One iteration -/

theorem body_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.AArch64.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c s) (hcl : c < VG.Proof.MdStream.AArch64.Update.len s₀) :
    WP isa (updateBody P name code) s fun s' => ∃ c', c < c' ∧ VG.Proof.MdStream.AArch64.Update.Inv H s₀ c' s' := by
  have hlen := VG.Proof.MdStream.AArch64.Update.len_lt s₀; have hr := VG.Proof.MdStream.AArch64.Update.rr_lt hd s₀ c; have hB := hd.B
  have h63 : lg P < 64 := by have hd_log := hd.log; omega
  have ne : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], r ≠ .x10 ∧ r ≠ .x9 := by decide
  unfold updateBody
  refine WP.seq (VG.Proof.MdStream.AArch64.wp_movz fun s₁ u₁ => WP.block_nil ?_)
  have hI₁ : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c s₁ := hI.of_gpr (fun r hr => u₁.other r (ne r hr).1) u₁.mem u₁.rd u₁.wr u₁.sp
  have h10₁ : s₁.gpr .x10 = 0 := by rw [u₁.gpr]; rfl
  refine WP.seq (WP.mono (Q := fun s' => (∃ c' k, c < c' ∧ VG.Proof.MdStream.AArch64.Update.Pending H s₀ c' k s') ∨ VG.Proof.MdStream.AArch64.Update.Done H s₀ s') ?_
    fun s' h => ?_)
  · refine WP.ite (decide (VG.Proof.MdStream.AArch64.Update.rr P s₀ c = 0))
      (by show VG.AArch64.eval (.zero .x .x23) s₁ = _; rw [VG.Proof.MdStream.AArch64.eval_zero, hI₁.x23, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by have := VG.Proof.MdStream.AArch64.Update.rr_eq (P := P) s₀ c; omega)])
      (fun hb => ?_) (fun _ => VG.Proof.MdStream.AArch64.Update.fill_ok hd hp hI₁ hcl h10₁)
    simp only [decide_eq_true_eq] at hb
    refine WP.seq (VG.Proof.MdStream.AArch64.wp_lsr h63 fun s₂ u₂ => WP.block_nil ?_)
    have hI₂ : VG.Proof.MdStream.AArch64.Update.Inv H s₀ c s₂ := hI₁.of_gpr (fun r hr => u₂.other r (ne r hr).2) u₂.mem u₂.rd u₂.wr u₂.sp
    have h10₂ : s₂.gpr .x10 = 0 := by rw [u₂.other _ (by decide), h10₁]
    refine WP.ite (decide ((VG.Proof.MdStream.AArch64.Update.len s₀ - c) / P.B = 0))
      (by show VG.AArch64.eval (.zero .x .x9) s₂ = _
          rw [VG.Proof.MdStream.AArch64.eval_zero, u₂.gpr, hI₁.x22, hd.shr (by omega),
            VG.Proof.MdStream.AArch64.ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))])
      (fun _ => VG.Proof.MdStream.AArch64.Update.fill_ok hd hp hI₂ hcl h10₂) (fun hb' => ?_)
    simp only [decide_eq_false_iff_not, Nat.div_eq_zero_iff_lt hd.pos] at hb'
    have hq := Nat.mul_pos hd.pos (Nat.div_pos (Nat.le_of_not_lt hb') hd.pos)
    exact WP.mono (VG.Proof.MdStream.AArch64.Update.direct_ok hd hp hI₂ hb (by omega)) fun s' h => .inl ⟨_, _, by omega, h⟩
  · rcases h with ⟨c', k, hc', hP⟩ | ⟨hD, h10⟩
    · refine WP.ite false (by
        show VG.AArch64.eval (.zero .x .x10) s' = _
        rw [VG.Proof.MdStream.AArch64.eval_zero, hP.x10, VG.Proof.MdStream.AArch64.ofNat_beq_zero (hP.k_lt hd), decide_eq_false (Nat.pos_iff_ne_zero.mp hP.k_pos)])
        (fun h => by cases h) fun _ => WP.mono (hP.compress_ok hd hf hp) fun s'' h => ⟨c', hc', h⟩
    · refine WP.ite true (by show VG.AArch64.eval (.zero .x .x10) s' = _; rw [VG.Proof.MdStream.AArch64.eval_zero, h10]; rfl)
        (fun _ => WP.block_nil ⟨VG.Proof.MdStream.AArch64.Update.len s₀, hcl, hD⟩) fun h => by cases h

/-! ## Prologue and epilogue -/

theorem prologue_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) :
    WP isa (.block (updateStart P)) s₀ (VG.Proof.MdStream.AArch64.Update.Inv H s₀ 0) := by
  have hd_N := hd.N; have hd_B := hd.B; have hd_so := hd.so
  refine VG.Proof.MdStream.AArch64.save_ok hd (fun d hd₁ hd₂ => ⟨VG.Proof.MdStream.AArch64.Update.scR P s₀, by simp [hp.wr], VG.Proof.MdStream.AArch64.contains_offset hd₂ (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine VG.Proof.MdStream.AArch64.wp_mov fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_mov fun s₃ u₃ => VG.Proof.MdStream.AArch64.wp_mov fun s₄ u₄ => VG.Proof.MdStream.AArch64.wp_mov fun s₅ u₅ =>
    VG.Proof.MdStream.AArch64.wp_movz fun s₆ u₆ => VG.Proof.MdStream.AArch64.wp_and fun s₇ u₇ => WP.block_nil ?_
  have hm₇ : s₇.mem = VG.Proof.MdStream.AArch64.saveMem P s₀.mem (VG.Proof.MdStream.AArch64.Update.scr s₀) s₀.gpr := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun iv m hm => ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [hm₇]; exact (VG.Proof.MdStream.AArch64.saveMem_frame hd _ _ _).mono (by simp)
  · rw [hm₇]; exact VG.Proof.MdStream.AArch64.saveMem_saved hd _ _ _
  · rw [u₇.gpr, u₆.gpr, u₆.other .x1 (by decide), u₅.other .x1 (by decide), u₄.other .x1 (by decide),
      u₃.other .x1 (by decide), u₂.other .x1 (by decide), g₁, hd.and, Nat.add_zero]
  · rw [List.take_zero, List.append_nil, hm₇]
    exact H.repr_congr hd.pos (fun i hi => VG.Proof.MdStream.AArch64.frame_bytes (VG.Proof.MdStream.AArch64.saveMem_frame hd s₀.mem (VG.Proof.MdStream.AArch64.Update.scr s₀) s₀.gpr)
      (R := VG.Proof.MdStream.AArch64.Update.stR P s₀) (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; omega) hi) hm.1

/-- The epilogue's postcondition. -/
def Post (P : Params) (H : Md P.B P.N P.L) (s₀ s' : State) : Prop :=
  (∀ p ∈ saved P, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧ (VG.Proof.MdStream.AArch64.updK H).post s₀ s'

theorem epilogue_ok (hd : VG.Proof.MdStream.AArch64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) {s : State} (hI : VG.Proof.MdStream.AArch64.Update.Inv H s₀ (VG.Proof.MdStream.AArch64.Update.len s₀) s) :
    WP isa (.block (restore P)) s (VG.Proof.MdStream.AArch64.Update.Post P H s₀) := by
  have hd_so := hd.so
  refine VG.Proof.MdStream.AArch64.restore_ok hd (scr := VG.Proof.MdStream.AArch64.Update.scr s₀) hI.x20
    (fun d hd₁ hd₂ => ⟨VG.Proof.MdStream.AArch64.Update.scR P s₀, by simp [hI.rd, hI.wr, hp.wr], VG.Proof.MdStream.AArch64.contains_offset hd₂ (by omega)⟩) s₀.gpr
    hI.saved fun s' hs _ hmem _ _ hsp => ⟨hs, by rw [hsp, hI.sp], fun iv m hr hc => ?_⟩
  have := hI.repr iv m ⟨hr, hc⟩
  rwa [List.take_of_length_le (Nat.le_of_eq (VG.Proof.MdStream.AArch64.Update.D_length _)), ← hmem] at this

/-- `update` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain (hd : VG.Proof.MdStream.AArch64.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.AArch64.CalleeOk H code)
    (hu : ∀ r ∈ VG.Proof.MdStream.AArch64.untouched, ∀ i ∈ instrs (updateMain P name code), dstOf i ≠ some r) {s₀ : State}
    (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀) :
    WP isa (updateMain P name code) s₀ fun s' => (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ (VG.Proof.MdStream.AArch64.updK H).post s₀ s' := by
  have hlen := VG.Proof.MdStream.AArch64.Update.len_lt s₀
  refine WP.mono (WP.gprs (Q := VG.Proof.MdStream.AArch64.Update.Post P H s₀) ?_ hu) fun s' ⟨⟨hsv, hsp, hpost⟩, hu⟩ =>
    ⟨VG.Proof.MdStream.AArch64.preserved_of hsv hu, hsp, hpost⟩
  unfold updateMain
  refine WP.seq (WP.mono (VG.Proof.MdStream.AArch64.Update.prologue_ok (H := H) hd hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.MdStream.AArch64.Update.Inv H s₀ (VG.Proof.MdStream.AArch64.Update.len s₀)) ?_ fun s₂ hI₂ => VG.Proof.MdStream.AArch64.Update.epilogue_ok hd hp hI₂)
  refine WP.ite (decide (VG.Proof.MdStream.AArch64.Update.len s₀ = 0))
    (by show VG.AArch64.eval (.zero .x .x22) s₁ = _
        rw [VG.Proof.MdStream.AArch64.eval_zero, hI.x22, Nat.sub_zero, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by omega)])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ hI)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = VG.Proof.MdStream.AArch64.Update.len s₀ - c ∧ c < VG.Proof.MdStream.AArch64.Update.len s₀ ∧ VG.Proof.MdStream.AArch64.Update.Inv H s₀ c s) ?_ (VG.Proof.MdStream.AArch64.Update.len s₀) s₁
      ⟨0, rfl, by omega, hI⟩
    rintro n s ⟨c, rfl, hcl, hI⟩
    refine WP.mono (VG.Proof.MdStream.AArch64.Update.body_ok hd hf hp hI hcl) fun s' ⟨c', hc, hI'⟩ => ?_
    have hc' := hI'.c_le
    have hz : isa.eval (.nonzero .x .x22) s' = some (decide (VG.Proof.MdStream.AArch64.Update.len s₀ - c' ≠ 0)) := by
      show VG.AArch64.eval (.nonzero .x .x22) s' = _
      rw [VG.Proof.MdStream.AArch64.eval_nonzero, hI'.x22, bne, VG.Proof.MdStream.AArch64.ofNat_beq_zero (by omega_using [hlen])]
      simp
    by_cases hl : VG.Proof.MdStream.AArch64.Update.len s₀ - c' = 0
    · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
      rwa [show c' = VG.Proof.MdStream.AArch64.Update.len s₀ by omega] at hI'
    · exact .inr ⟨by rw [hz]; simp [hl], VG.Proof.MdStream.AArch64.Update.len s₀ - c', by omega, c', rfl, by omega, hI'⟩

/-- The state `updateMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct (hd : VG.Proof.MdStream.AArch64.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.AArch64.CalleeOk H code)
    (hu : ∀ r ∈ VG.Proof.MdStream.AArch64.untouched, ∀ i ∈ instrs (updateMain P name code), dstOf i ≠ some r)
    (hn : 16 * (updateMain P name code).aarch64Depth + 16 < 2 ^ 64) {s₀ : State} (hp : VG.Proof.MdStream.AArch64.Update.Pre P s₀)
    (hs : VG.Proof.MdStream.AArch64.Update.Stack P s₀) :
    WP isa (update P name code) s₀ fun s' => abiPreserved s₀ s' ∧ (VG.Proof.MdStream.AArch64.updK H).post s₀ s' := by
  apply WP.withPreservedV (hc := VG.Proof.MdStream.AArch64.update_keepsV hf.keepsV)
  have hpi : VG.Proof.MdStream.AArch64.Update.Pre P (VG.Proof.MdStream.AArch64.Update.inner s₀) := ⟨hp.rd, hp.wr, hp.st_scr, hp.d_st, hp.d_scr⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_) (WP.mono (VG.Proof.MdStream.AArch64.Update.correctMain hd hf hu hpi) fun s' ⟨hk, hsp, hpost⟩ => ?_)
    hn
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.st
    · exact hs.scr
  · refine ⟨⟨fun r hr => ?_, rfl⟩, fun iv m hm hc => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : bytesAt (VG.Proof.MdStream.AArch64.Update.inner s₀).mem (VG.Proof.MdStream.AArch64.Update.dp s₀) (VG.Proof.MdStream.AArch64.Update.len s₀) = bytesAt s₀.mem (VG.Proof.MdStream.AArch64.Update.dp s₀) (VG.Proof.MdStream.AArch64.Update.len s₀) :=
        bytesAt_congr fun i hi => VG.Proof.MdStream.AArch64.write_frame_bytes hs.d (VG.Proof.MdStream.AArch64.Update.len_lt s₀) hi
      have := hpost iv m (H.repr_congr hd.pos (fun i hi => VG.Proof.MdStream.AArch64.write_frame_bytes (R := VG.Proof.MdStream.AArch64.Update.stR P s₀) hs.st
        (by have hd_N := hd.N; have hd_B := hd.B; show P.N + P.B < 2 ^ 64; omega) hi) hm) hc
      rw [e] at this
      exact this

/-- A state satisfying the precondition (with no data). -/
def sat (P : Params) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x4 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, P.N + P.B⟩, ⟨0x3000, P.so + 48⟩]

/-- `update` is verified, given that it is constant time (which the taint
analysis proves of each hash function's code), never writes `untouched`, and
fits its frames in the address space. -/
theorem verified (hd : VG.Proof.MdStream.AArch64.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.AArch64.CalleeOk H code)
    (hct : ConstantTime isa (VG.Proof.MdStream.AArch64.updK H).pre (VG.Proof.MdStream.AArch64.updK H).pub (update P name code))
    (hu : ((instrs (updateMain P name code)).all fun i => untouched.all fun r => dstOf i != some r) = true)
    (hn : 16 * (updateMain P name code).aarch64Depth + 16 < 2 ^ 64) :
    Verified AArch64.target (update P name code) (VG.Proof.MdStream.AArch64.updK H) := by
  have hd_N := hd.N; have hd_B := hd.B; have hd_so := hd.so
  have hu' : ∀ r ∈ VG.Proof.MdStream.AArch64.untouched, ∀ i ∈ instrs (updateMain P name code), dstOf i ≠ some r := by
    intro r hr i hi
    have := List.all_eq_true.mp (List.all_eq_true.mp hu i hi) r hr
    simpa using this
  refine ⟨fun s hs' => ?_, hct, ?_⟩
  · obtain ⟨t, s', he, h⟩ := VG.Proof.MdStream.AArch64.Update.correct hd hf hu' hn (VG.Proof.MdStream.AArch64.Update.pre_of hs').1 (VG.Proof.MdStream.AArch64.Update.pre_of hs').2
    exact ⟨t, s', he, h⟩
  · refine ⟨VG.Proof.MdStream.AArch64.Update.sat P, rfl, rfl, ?_, ?_, ?_, by simp only [VG.Proof.MdStream.AArch64.Update.sat]; decide, ?_, ?_, ?_⟩
    all_goals try simp only [VG.Proof.MdStream.AArch64.Update.sat]
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact Offset.disjoint_of_le (by simp) (by simp <;> omega)
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm

/-- The initial taint agrees on the public arguments. -/
theorem agree₀ {s₁ s₂ : State} (hpub : (VG.Proof.MdStream.AArch64.updK H).pub s₁ s₂) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

end

end VG.Proof.MdStream.AArch64.Update

end

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.AArch64.Words`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on AArch64: length fields and digests

What the length fields (`len64`, `len128`) and digests (`out32`, `out64`) of
`Impl/MdStream/AArch64.lean` write, for the hash functions' `Shape`s.
-/

namespace VG.Proof.MdStream.AArch64

open VG VG.AArch64 VG.Impl.MdStream.AArch64
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil write_eq_writeBytes writeBytes_append
  writeBytes_frame)

/-! ## Byte order -/

/-- The bytes of a byte-reversed word, one by one. -/
theorem rev32_byte_0 (x : BitVec 32) : (rev32 x).extractLsb' 0 8 = x.extractLsb' 24 8 := by
  unfold rev32
  rw [BitVec.extractLsb'_append_eq_of_add_le (v := 24) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev32_byte_1 (x : BitVec 32) : (rev32 x).extractLsb' 8 8 = x.extractLsb' 16 8 := by
  unfold rev32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 16) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev32_byte_2 (x : BitVec 32) : (rev32 x).extractLsb' 16 8 = x.extractLsb' 8 8 := by
  unfold rev32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev32_byte_3 (x : BitVec 32) : (rev32 x).extractLsb' 24 8 = x.extractLsb' 0 8 := by
  unfold rev32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self


theorem rev64_byte_0 (x : BitVec 64) : (rev64 x).extractLsb' 0 8 = x.extractLsb' 56 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_add_le (v := 56) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_1 (x : BitVec 64) : (rev64 x).extractLsb' 8 8 = x.extractLsb' 48 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 48) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_2 (x : BitVec 64) : (rev64 x).extractLsb' 16 8 = x.extractLsb' 40 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 40) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_3 (x : BitVec 64) : (rev64 x).extractLsb' 24 8 = x.extractLsb' 32 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 32) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_4 (x : BitVec 64) : (rev64 x).extractLsb' 32 8 = x.extractLsb' 24 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 24) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_5 (x : BitVec 64) : (rev64 x).extractLsb' 40 8 = x.extractLsb' 16 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 16) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_6 (x : BitVec 64) : (rev64 x).extractLsb' 48 8 = x.extractLsb' 8 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem rev64_byte_7 (x : BitVec 64) : (rev64 x).extractLsb' 56 8 = x.extractLsb' 0 8 := by
  unfold rev64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self


theorem bytes32_store (be : Bool) (x : BitVec 32) :
    (List.range 4).map (fun j => (if be then rev32 x else x).extractLsb' (8 * j) 8) = bytes32 be x := by
  cases be
  · rfl
  · simp only [bytes32, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, Nat.reduceMul, VG.Proof.MdStream.AArch64.rev32_byte_0, VG.Proof.MdStream.AArch64.rev32_byte_1, VG.Proof.MdStream.AArch64.rev32_byte_2,
      VG.Proof.MdStream.AArch64.rev32_byte_3]


theorem bytes64_store (be : Bool) (x : BitVec 64) :
    (List.range 8).map (fun j => (if be then rev64 x else x).extractLsb' (8 * j) 8) = bytes64 be x := by
  cases be
  · rfl
  · simp only [bytes64, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, List.reverse_cons, List.reverse_nil, Nat.reduceMul,
      VG.Proof.MdStream.AArch64.rev64_byte_0, VG.Proof.MdStream.AArch64.rev64_byte_1, VG.Proof.MdStream.AArch64.rev64_byte_2, VG.Proof.MdStream.AArch64.rev64_byte_3, VG.Proof.MdStream.AArch64.rev64_byte_4, VG.Proof.MdStream.AArch64.rev64_byte_5, VG.Proof.MdStream.AArch64.rev64_byte_6,
      VG.Proof.MdStream.AArch64.rev64_byte_7]


theorem writeW32 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 32) :
    m.writeW a (if be then rev32 x else x) = VG.WriteBytes.writeBytes m a (bytes32 be x) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes, ← VG.Proof.MdStream.AArch64.bytes32_store]; rfl

theorem writeW64 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 64) :
    m.writeW a (if be then rev64 x else x) = VG.WriteBytes.writeBytes m a (bytes64 be x) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes, ← VG.Proof.MdStream.AArch64.bytes64_store]; rfl

/-! ## Regions -/

theorem InRegions.offset {rs : List Region} {a : Addr} {n off m : Nat} (h : InRegions rs a n)
    (hm : off + m ≤ n) (hn : n < 2 ^ 64) : InRegions rs (a + BitVec.ofNat 64 off) m := by
  obtain ⟨R, hR, hc⟩ := h
  refine ⟨R, hR, ?_⟩
  simp only [Region.Contains] at *
  have : (a + BitVec.ofNat 64 off - R.base).toNat ≤ (a - R.base).toNat + off := by
    rw [Offset.add_sub_comm,
      BitVec.toNat_add, VG.Proof.MdStream.AArch64.toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

/-! ## The length field -/

theorem times8 (x : BitVec 64) : x + x + (x + x) + (x + x + (x + x)) = BitVec.ofNat 64 (8 * x.toNat) := by
  bv_omega

/-- `len64 d be` stores `8 · x22` at `x19 + d`. -/
theorem len64_ok {d : Nat} {be : Bool} {s : State} (hd : d < 4096)
    (hout : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 8) :
    WP isa (.block (len64 d be)) s fun s' => (∀ r, r ≠ .x9 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .x19 + BitVec.ofNat 64 d)
        (bytes64 be (BitVec.ofNat 64 (8 * (s.gpr .x22).toNat))) := by
  unfold len64
  rw [List.append_assoc]
  refine VG.Proof.MdStream.AArch64.wp_add fun s₁ u₁ => VG.Proof.MdStream.AArch64.wp_add fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_add fun s₃ u₃ => ?_
  have g₃ : ∀ r, r ≠ .x9 → s₃.gpr r = s.gpr r := fun r h => by
    rw [u₃.other r h, u₂.other r h, u₁.other r h]
  have v₃ : s₃.gpr .x9 = BitVec.ofNat 64 (8 * (s.gpr .x22).toNat) := by
    rw [u₃.gpr, u₂.gpr, u₁.gpr, VG.Proof.MdStream.AArch64.times8]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  -- The value, reversed if big-endian, is in `x9` of a state `t` like `s₃`.
  have st : ∀ (t : State), (∀ r, r ≠ .x9 → t.gpr r = s.gpr r) → t.mem = s.mem → t.rd = s.rd →
      t.wr = s.wr → t.sp = s.sp →
      t.gpr .x9 = (if be then rev64 (BitVec.ofNat 64 (8 * (s.gpr .x22).toNat))
        else BitVec.ofNat 64 (8 * (s.gpr .x22).toNat)) →
      WP isa (.block (if d % 8 = 0 then [.str .x .x9 .x19 d] else [.addImm .x .x12 .x19 d, .str .x .x9 .x12 0]))
        t fun s' => (∀ r, r ≠ .x9 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
          s'.sp = s.sp ∧ s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .x19 + BitVec.ofNat 64 d)
            (bytes64 be (BitVec.ofNat 64 (8 * (s.gpr .x22).toNat))) := by
    intro t g m rd wr sp v
    have h19 : t.gpr .x19 = s.gpr .x19 := g _ (by decide)
    by_cases hd8 : d % 8 = 0
    · simp only [hd8, ite_true]
      refine VG.Proof.MdStream.AArch64.wp_str (a := s.gpr .x19 + BitVec.ofNat 64 d) ⟨hd8, by omega⟩ (by rw [h19])
        (by rw [wr]; exact hout) fun s' g' => WP.block_nil ⟨fun r h h' => by rw [g'.gpr, g r h],
          g'.rd.trans rd, g'.wr.trans wr, g'.sp.trans sp, ?_⟩
      rw [g'.mem, m, v, VG.Proof.MdStream.AArch64.writeW64]
    · simp only [hd8, ite_false]
      refine VG.Proof.MdStream.AArch64.wp_addImm hd fun t₁ u => VG.Proof.MdStream.AArch64.wp_str (a := s.gpr .x19 + BitVec.ofNat 64 d) (by decide)
        (by rw [u.gpr, h19]; simp) (by rw [u.wr, wr]; exact hout) fun s' g' => WP.block_nil
          ⟨fun r h h' => by rw [g'.gpr, u.other r h', g r h], by rw [g'.rd, u.rd, rd],
            by rw [g'.wr, u.wr, wr], by rw [g'.sp, u.sp, sp], ?_⟩
      rw [g'.mem, u.mem, m, u.other _ (by decide), v, VG.Proof.MdStream.AArch64.writeW64]
  cases be
  · simp only [Bool.false_eq_true, ite_false, List.nil_append]
    exact st s₃ g₃ m₃ rd₃ wr₃ sp₃ v₃
  · simp only [ite_true, List.cons_append, List.nil_append]
    refine VG.Proof.MdStream.AArch64.wp_rev fun s₄ u₄ => st s₄ (fun r h => by rw [u₄.other r h, g₃ r h]) (by rw [u₄.mem, m₃])
      (by rw [u₄.rd, rd₃]) (by rw [u₄.wr, wr₃]) (by rw [u₄.sp, sp₃]) (by rw [u₄.gpr, v₃]; rfl)

/-- `len128 d` stores the length in bits of the byte count in `x22`, as a
128-bit big-endian integer, at `x19 + d`. -/
theorem len128_ok {d : Nat} (hd : d % 8 = 0 ∧ d + 8 < 4096) {s : State}
    (hout : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 16) :
    WP isa (.block (len128 d)) s fun s' => (∀ r, r ≠ .x9 → r ≠ .x12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .x19 + BitVec.ofNat 64 d)
        (bytes64 true (s.gpr .x22 >>> 61) ++ bytes64 true (BitVec.ofNat 64 (8 * (s.gpr .x22).toNat))) := by
  have e8 : s.gpr .x19 + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = s.gpr .x19 + BitVec.ofNat 64 (d + 8) :=
    Offset.add_add _ _ _
  unfold len128
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.MdStream.AArch64.wp_lsr (by decide) fun s₁ u₁ => VG.Proof.MdStream.AArch64.wp_rev fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_str (a := s.gpr .x19 + BitVec.ofNat 64 d)
    ⟨hd.1, by omega⟩ (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.wr, u₁.wr]; simpa using InRegions.offset (off := 0) (m := 8) hout (by omega) (by omega))
    fun s₃ g₃ => ?_
  have h19 : s₃.gpr .x19 = s.gpr .x19 := by rw [g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  have h22 : s₃.gpr .x22 = s.gpr .x22 := by rw [g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  refine (VG.Proof.MdStream.AArch64.len64_ok (d := d + 8) (be := true) hd.2 (by
    rw [h19, g₃.wr, u₂.wr, u₁.wr, ← e8]; exact InRegions.offset hout (by omega) (by omega))).mono
    fun s' ⟨g, rd, wr, sp, m⟩ => ⟨fun r h h' => by rw [g r h h', g₃.gpr, u₂.other r h, u₁.other r h],
      by rw [rd, g₃.rd, u₂.rd, u₁.rd], by rw [wr, g₃.wr, u₂.wr, u₁.wr], by rw [sp, g₃.sp, u₂.sp, u₁.sp], ?_⟩
  rw [m, h19, h22, g₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr,
    show rev64 (s.gpr .x22 >>> 61) = (if true then rev64 (s.gpr .x22 >>> 61) else s.gpr .x22 >>> 61) from rfl,
    VG.Proof.MdStream.AArch64.writeW64, ← e8, show (8 : Nat) = (bytes64 true (s.gpr .x22 >>> 61)).length from rfl,
    VG.WriteBytes.writeBytes_append _ _ _ _ (by rw [bytes64_length, bytes64_length]; omega)]

/-! ## The digest -/

theorem setWidth32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `out32 n be` writes the `n` 32-bit words at `x19` to `x21`. -/
theorem out32_ok {n : Nat} (be : Bool) (hn : 4 * n ≤ 64) {s₀ : State}
    (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x19) (4 * n)) (hout : InRegions s₀.wr (s₀.gpr .x21) (4 * n))
    (hd : Region.Disjoint ⟨s₀.gpr .x19, 4 * n⟩ ⟨s₀.gpr .x21, 4 * n⟩) :
    WP isa (.block (out32 n be)) s₀ fun s' =>
      (∀ r, r ≠ .x9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .x21)
        ((List.range n).flatMap fun k => bytes32 be (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * k)) 32)) := by
  let f : Nat → List Byte := fun k => bytes32 be (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * k)) 32)
  have hflat : ∀ k, ((List.range k).flatMap f).length = 4 * k := by
    intro k
    rw [List.length_flatMap, List.map_congr_left (fun x _ => bytes32_length _ _), List.map_const',
      List.sum_replicate_nat, List.length_range, Nat.mul_comm]
  -- Words `[n - j, n)` are left, the others written.
  suffices h : ∀ j ≤ n, ∀ s, (∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r) → s.rd = s₀.rd → s.wr = s₀.wr →
      s.sp = s₀.sp → s.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .x21) ((List.range (n - j)).flatMap f) →
      WP isa (.block (((List.range n).drop (n - j)).flatMap fun k =>
        [.ldr .w .x9 .x19 (4 * k)] ++ (if be then [.rev32 .x9 .x9] else []) ++ [.str .w .x9 .x21 (4 * k)]))
        s fun s' => (∀ r, r ≠ .x9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
          s'.sp = s₀.sp ∧ s'.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .x21) ((List.range n).flatMap f) by
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
    -- The word read is not yet overwritten.
    have hread : s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32 =
        s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32 := by
      rw [m]
      refine (VG.WriteBytes.writeBytes_frame _ _ _ (R := ⟨s₀.gpr .x21, 4 * n⟩) ?_).readW
        (r := ⟨s₀.gpr .x19 + BitVec.ofNat 64 (4 * (n - (j + 1))), 4⟩) (Region.contains_self _ _) ?_ (by decide)
      · rw [hflat]
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
        omega
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (VG.Proof.MdStream.AArch64.sub_offset hoff (by omega))
    have hmem : ∀ (t : State), t.mem = s.mem →
        t.mem.writeW (s₀.gpr .x21 + BitVec.ofNat 64 (4 * (n - (j + 1))))
          (if be then rev32 (s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32)
            else s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (4 * (n - (j + 1)))) 32) =
        VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .x21) ((List.range (n - j)).flatMap f) := by
      intro t ht
      rw [ht, VG.Proof.MdStream.AArch64.writeW32, hread, m, show n - j = n - (j + 1) + 1 by omega, List.range_succ,
        List.flatMap_append, List.flatMap_singleton,
        ← VG.WriteBytes.writeBytes_append _ _ _ _ (by rw [hflat, bytes32_length]; omega), hflat]
    refine VG.Proof.MdStream.AArch64.wp_ldr32 (a := s₀.gpr .x19 + BitVec.ofNat 64 (4 * (n - (j + 1)))) (by omega)
      (by rw [g _ (by decide)]) (by rw [rd, wr]; exact InRegions.offset hin hoff (by omega)) fun s₁ u₁ => ?_
    have ea : ∀ t : State, t.gpr .x21 = s.gpr .x21 →
        t.gpr .x21 + BitVec.ofNat 64 (4 * (n - (j + 1))) = s₀.gpr .x21 + BitVec.ofNat 64 (4 * (n - (j + 1))) :=
      fun t ht => by rw [ht, g _ (by decide)]
    cases be
    · simp only [Bool.false_eq_true, ite_false, List.nil_append, List.cons_append]
      refine VG.Proof.MdStream.AArch64.wp_str32 (by omega) (ea s₁ (u₁.other _ (by decide)))
        (by rw [u₁.wr, wr]; exact InRegions.offset hout hoff (by omega)) fun s₂ g₂ => ?_
      refine ih (by omega) s₂ (fun r h => by rw [g₂.gpr, u₁.other r h, g r h]) (by rw [g₂.rd, u₁.rd, rd])
        (by rw [g₂.wr, u₁.wr, wr]) (by rw [g₂.sp, u₁.sp, sp]) ?_
      rw [g₂.mem, u₁.gpr, VG.Proof.MdStream.AArch64.setWidth32]
      exact hmem s₁ u₁.mem
    · simp only [ite_true, List.cons_append, List.nil_append]
      refine VG.Proof.MdStream.AArch64.wp_rev32 fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_str32 (by omega) (ea s₂ (by rw [u₂.other _ (by decide),
                                                            u₁.other _ (by decide)])) (by rw [u₂.wr, u₁.wr, wr]; exact InRegions.offset hout hoff (by omega))
        fun s₃ g₃ => ?_
      refine ih (by omega) s₃ (fun r h => by rw [g₃.gpr, u₂.other r h, u₁.other r h, g r h])
        (by rw [g₃.rd, u₂.rd, u₁.rd, rd]) (by rw [g₃.wr, u₂.wr, u₁.wr, wr]) (by rw [g₃.sp, u₂.sp, u₁.sp, sp]) ?_
      rw [g₃.mem, u₂.mem, u₂.gpr, u₁.gpr, VG.Proof.MdStream.AArch64.setWidth32, VG.Proof.MdStream.AArch64.setWidth32]
      exact hmem s₁ u₁.mem

/-- `out64 n` writes the `n` 64-bit words at `x19` to `x21`, big-endian. -/
theorem out64_ok {n : Nat} (hn : 8 * n ≤ 64) {s₀ : State}
    (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x19) (8 * n)) (hout : InRegions s₀.wr (s₀.gpr .x21) (8 * n))
    (hd : Region.Disjoint ⟨s₀.gpr .x19, 8 * n⟩ ⟨s₀.gpr .x21, 8 * n⟩) :
    WP isa (.block (out64 n)) s₀ fun s' =>
      (∀ r, r ≠ .x9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s₀.sp ∧
      s'.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .x21)
        ((List.range n).flatMap fun k => bytes64 true (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64)) := by
  let f : Nat → List Byte := fun k => bytes64 true (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64)
  have hflat : ∀ k, ((List.range k).flatMap f).length = 8 * k := by
    intro k
    rw [List.length_flatMap, List.map_congr_left (fun x _ => bytes64_length _ _), List.map_const',
      List.sum_replicate_nat, List.length_range, Nat.mul_comm]
  -- Words `[n - j, n)` are left, the others written.
  suffices h : ∀ j ≤ n, ∀ s, (∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r) → s.rd = s₀.rd → s.wr = s₀.wr →
      s.sp = s₀.sp → s.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .x21) ((List.range (n - j)).flatMap f) →
      WP isa (.block (((List.range n).drop (n - j)).flatMap fun k =>
        ([.ldr .x .x9 .x19 (8 * k), .rev .x9 .x9, .str .x .x9 .x21 (8 * k)] : List Instr)))
        s fun s' => (∀ r, r ≠ .x9 → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
          s'.sp = s₀.sp ∧ s'.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .x21) ((List.range n).flatMap f) by
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
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_range]
    rw [show n - (j + 1) + 1 = n - j by omega]
    have hoff : 8 * (n - (j + 1)) + 8 ≤ 8 * n := by omega
    -- The word read is not yet overwritten.
    have hread : s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64 =
        s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64 := by
      rw [m]
      refine (VG.WriteBytes.writeBytes_frame _ _ _ (R := ⟨s₀.gpr .x21, 8 * n⟩) ?_).readW
        (r := ⟨s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1))), 8⟩) (Region.contains_self _ _) ?_ (by decide)
      · rw [hflat]
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
        omega
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (VG.Proof.MdStream.AArch64.sub_offset hoff (by omega))
    simp only [List.cons_append, List.nil_append]
    refine VG.Proof.MdStream.AArch64.wp_ldr (a := s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1)))) ⟨by omega, by omega⟩
      (by rw [g _ (by decide)]) (by rw [rd, wr]; exact InRegions.offset hin hoff (by omega)) fun s₁ u₁ => ?_
    refine VG.Proof.MdStream.AArch64.wp_rev fun s₂ u₂ => VG.Proof.MdStream.AArch64.wp_str (a := s₀.gpr .x21 + BitVec.ofNat 64 (8 * (n - (j + 1))))
      ⟨by omega, by omega⟩ (by rw [u₂.other _ (by decide), u₁.other _ (by decide), g _ (by decide)])
      (by rw [u₂.wr, u₁.wr, wr]; exact InRegions.offset hout hoff (by omega)) fun s₃ g₃ => ?_
    refine ih (by omega) s₃ (fun r h => by rw [g₃.gpr, u₂.other r h, u₁.other r h, g r h])
      (by rw [g₃.rd, u₂.rd, u₁.rd, rd]) (by rw [g₃.wr, u₂.wr, u₁.wr, wr]) (by rw [g₃.sp, u₂.sp, u₁.sp, sp]) ?_
    rw [g₃.mem, u₂.mem, u₂.gpr, u₁.gpr, u₁.mem, hread,
      show rev64 (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64) =
        (if true then rev64 (s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64) else
          s₀.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (8 * (n - (j + 1)))) 64) from rfl,
      VG.Proof.MdStream.AArch64.writeW64, m, show n - j = n - (j + 1) + 1 by omega, List.range_succ,
      List.flatMap_append, List.flatMap_singleton,
      ← VG.WriteBytes.writeBytes_append _ _ _ _ (by simp only [hflat, f, bytes64_length]; omega), hflat]

end VG.Proof.MdStream.AArch64

end
