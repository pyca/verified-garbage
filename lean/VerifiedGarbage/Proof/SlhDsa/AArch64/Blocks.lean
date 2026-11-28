module

public import VerifiedGarbage.Proof.SlhDsa.Fld
public import VerifiedGarbage.Proof.Framework.AArch64.Steps
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Layout
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: the blocks the proofs of the code above `thash4` share (`wotsLeaves4`, `levels`, …).

/-!
# SLH-DSA on AArch64: the blocks of the code above `thash4`

The steps of the AArch64 instructions the SLH-DSA code uses that
`Proof/Framework/AArch64/Steps.lean` lacks, in its style (`Upd`, `Mupd`),
and the blocks of `Impl/SlhDsa/AArch64/Layout.lean` the functions are built
from, as the bytes they write (`bytesAt`) and the ranges they change
(`Frame`): a field of an address (`setField`, `setFieldR`: its value's four
bytes big-endian, `toByte`), a copy of words (`copyWords`), a masked copy,
the multiplication by `n` (`mulN`) and the mask of a comparison
(`maskZero`). As x86-64's (`Proof/SlhDsa/X86_64/WotsBlocks.lean`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Blocks

open VG VG.AArch64 VG.AArch64.Steps
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64

/-! ## Instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem Upd.writeW (s : State) (d : Reg) (v : BitVec 32) : Upd s (s.write .w d v) d (v.setWidth 64) :=
  ⟨RegUpd.gpr_write_self _ _ _ _, fun _ h => RegUpd.gpr_write_of_ne _ _ _ h,
    RegUpd.sp_write _ _ _ _, RegUpd.mem_write _ _ _ _, RegUpd.rd_write _ _ _ _, RegUpd.wr_write _ _ _ _, rfl⟩

/-- `eor d, n, m`. -/
theorem wp_eor {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  WP.cons rfl (by
    have := k _ (Upd.write s d (s.gpr n ^^^ s.gpr m))
    simpa only [State.read, Size.bits, BitVec.setWidth_eq] using this)

/-- `orr d, n, m`. -/
theorem wp_orr {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .orr .x d n m :: is)) s Q :=
  WP.cons rfl (by
    have := k _ (Upd.write s d (s.gpr n ||| s.gpr m))
    simpa only [State.read, Size.bits, BitVec.setWidth_eq] using this)

/-- `and d, n, m`. -/
theorem wp_and {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .x d n m :: is)) s Q :=
  WP.cons rfl (by
    have := k _ (Upd.write s d (s.gpr n &&& s.gpr m))
    simpa only [State.read, Size.bits, BitVec.setWidth_eq] using this)

/-- `sub d, n, #imm`. -/
theorem wp_subImm {d n : Reg} {imm : Nat} (hi : imm < 4096)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .x d n imm :: is)) s Q :=
  WP.cons (exec_subImm_x hi) (by
    have := k _ (Upd.write s d (s.gpr n - BitVec.ofNat 64 imm))
    simpa only [State.read, Size.bits, BitVec.setWidth_eq] using this)

/-- `lsr d, n, #sh`. -/
theorem wp_lsr {d n : Reg} {sh : Nat} (hs : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .x d n sh :: is)) s Q :=
  WP.cons (exec_lsr_x hs) (by
    have := k _ (Upd.write s d (s.gpr n >>> sh))
    simpa only [State.read, Size.bits, BitVec.setWidth_eq] using this)

/-- `lsl d, n, #sh`. -/
theorem wp_lsl {d n : Reg} {sh : Nat} (hs : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  WP.cons (s' := s.write .x d (s.read .x n <<< sh)) (by simp [reduceExec, Size.bits, hs]) (by
    have := k _ (Upd.write s d (s.gpr n <<< sh))
    simpa only [State.read, Size.bits, BitVec.setWidth_eq] using this)

/-- `rev32 d, n`: the low word of `n` byte-reversed, zero-extended. -/
theorem wp_rev32 {d n : Reg}
    (k : ∀ s', Upd s s' d ((rev32 ((s.gpr n).setWidth 32)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev32 d n :: is)) s Q :=
  WP.cons exec_rev32 (k _ (Upd.writeW _ _ _))

/-- `movz wd, #imm, lsl #16·hw`. -/
theorem wp_movzw {d : Reg} {imm : BitVec 16} {hw : Nat} (hh : 16 * hw < 32)
    (k : ∀ s', Upd s s' d ((imm.setWidth 32 <<< (16 * hw)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .w d imm hw :: is)) s Q :=
  WP.cons (by simp only [reduceExec, Size.bits, hh, ite_true]) (k _ (Upd.writeW _ _ _))

/-- `movk wd, #imm, lsl #16·hw`. -/
theorem wp_movkw {d : Reg} {imm : BitVec 16} {hw : Nat} (hh : 16 * hw < 32)
    (k : ∀ s', Upd s s' d ((((s.gpr d).setWidth 32 &&& ~~~((0xFFFF : BitVec 32) <<< (16 * hw))) |||
      (imm.setWidth 32 <<< (16 * hw))).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movk .w d imm hw :: is)) s Q :=
  WP.cons (by simp only [reduceExec, Size.bits, hh, ite_true, State.read]) (k _ (Upd.writeW _ _ _))

/-- `ldr wt, [n, #off]`, zero-extended. -/
theorem wp_ldrw {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 16384)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .w t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_ldr_w ho hin) (k _ (Upd.writeW _ _ _))

/-- `str wt, [n, #off]`. -/
theorem wp_strw {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 16384)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .w t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_str_w ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- `str xt, [n, #off]`. -/
theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 32768)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .x t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_str_x ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem read1 (m : Mem) (a : Addr) : ((m.read a 1).setWidth 32).setWidth 64 = (m a).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp [Mem.read, BitVec.toNat_setWidth]

/-- `ldrb wt, [n, #off]`, zero-extended. -/
theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  subst ha
  refine WP.cons (s' := s.write .w t ((s.mem.read (s.gpr n + BitVec.ofNat 64 off) 1).setWidth 32)) ?_ ?_
  · simp only [reduceExec, addr, Nat.mod_one, Nat.mul_one, ho, and_self, ite_true, Option.bind_some,
      State.load, hin, Option.map_some]
  · have u := Upd.writeW s t ((s.mem.read (s.gpr n + BitVec.ofNat 64 off) 1).setWidth 32)
    rw [read1] at u
    exact k _ u

/-- What a write of a vector register does. -/
structure VUpd (s s' : State) (d : VReg) (x : BitVec 128) : Prop where
  gpr : s'.gpr = s.gpr
  sp : s'.sp = s.sp
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  v : s'.v d = x

/-- `ldr qt, [n, #off]`. -/
theorem wp_ldrq {t : VReg} {n : Reg} {off : Nat} {a : Addr} (ho : off % 16 = 0 ∧ off < 65536)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', VUpd s s' t (s.mem.read a 16) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrq t n off :: is)) s Q := by
  subst ha
  refine WP.cons (s' := s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, RegUpd.v_setV_self _ _ _⟩)
  simp only [reduceExec, addr, ho, and_self, ite_true, Option.bind_some,
    State.load, hin, Option.map_some]

/-- `str qt, [n, #off]`. -/
theorem wp_strq {t : VReg} {n : Reg} {off : Nat} {a : Addr} (ho : off % 16 = 0 ∧ off < 65536)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', Mupd s s' (s.mem.write a 16 (s.v t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strq t n off :: is)) s Q := by
  subst ha
  refine WP.cons (s' := { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [reduceExec, addr, ho, and_self, ite_true, Option.bind_some,
    State.store, hout]

end

/-- A block that never writes v8–v15 keeps their low halves. -/
theorem wp_vk {is : List Instr} (h : is.all keepsV = true) {s : State} {Q : State → Prop}
    (hw : WP isa (.block is) s fun t =>
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) → Q t) :
    WP isa (.block is) s Q :=
  WP.mono (WP.preservedV hw (by rw [Code.allInstrs_eq]; simpa [instrs] using h)) fun _ h' => h'.1 h'.2


/-! ## Bytes of memory -/

theorem bytesAt_length' (m : Mem) (a : Addr) (n : Nat) : (bytesAt m a n).length = n := by simp [bytesAt]

theorem bytesAt_ext {m m' : Mem} {a a' : Addr} {n : Nat}
    (h : ∀ i < n, m' (a' + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) : bytesAt m' a' n = bytesAt m a n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- Bytes a frame does not meet are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' a n = bytesAt m a n :=
  bytesAt_ext fun _ hi => hf.bytes (R := ⟨a, n⟩) hd hn hi

theorem ofNat_add' (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Byte `q` of a write of `n` bytes. -/
theorem write_in (m : Mem) (a : Addr) {n : Nat} (v : BitVec (8 * n)) {q : Nat} (hq : q < n) (hn : n < 2 ^ 64) :
    (m.write a n v) (a + BitVec.ofNat 64 q) = v.extractLsb' (8 * q) 8 := by
  simp only [Mem.write, Mem.sub_ofNat_toNat a (show q < 2 ^ 64 by omega_using [hq, hn]), hq, ite_true]

/-- A byte outside a write of `n` bytes. -/
theorem write_out (m : Mem) (a : Addr) {n : Nat} (v : BitVec (8 * n)) {x : Addr} (h : n ≤ (x - a).toNat) :
    (m.write a n v) x = m x :=
  Mem.write_apply (by omega_using [h])

/-- Byte `j < 8` of the word at `a`. -/
theorem byte_readW64 (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    (m.readW a 64).extractLsb' (8 * j) 8 = m (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

/-- Byte `j < 8` of a word written. -/
theorem writeW64_in (m : Mem) (a : Addr) (v : BitVec 64) {j : Nat} (hj : j < 8) :
    (m.writeW a v) (a + BitVec.ofNat 64 j) = v.extractLsb' (8 * j) 8 := by
  rw [← byte_readW64 (m.writeW a v) a hj, Mem.readW_writeW_self64]

/-- The four bytes of a 32-bit write. -/
theorem bytesAt_writeW32 (m : Mem) (a : Addr) (v : BitVec 32) :
    bytesAt (m.writeW a v) a 4 = (List.range 4).map fun d => v.extractLsb' (8 * d) 8 := by
  simp only [bytesAt]
  refine List.map_congr_left fun d hd => ?_
  rw [Mem.readW_byte (m.writeW a v) a (List.mem_range.mp hd), Mem.readW_writeW_self32]

/-- A write's frame. -/
theorem frame_write (m : Mem) (a : Addr) {n : Nat} (v : BitVec (8 * n)) (hn : n < 2 ^ 64) :
    Frame [⟨a, n⟩] m (m.write a n v) :=
  (Frame.refl _ _).write (List.mem_singleton_self _) _ (by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hn])

theorem frame_writeW (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) (hw : w / 8 < 2 ^ 64) :
    Frame [⟨a, w / 8⟩] m (m.writeW a v) := frame_write m a _ hw

/-- A range at an offset of a range a region contains. -/
theorem contains_off {r : Region} {a : Addr} {n k l : Nat} (h : r.Contains a n) (hk : k + l ≤ n) :
    r.Contains (a + BitVec.ofNat 64 k) l := by
  unfold Region.Contains at h ⊢
  have e : a + BitVec.ofNat 64 k - r.base = (a - r.base) + BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add]
    omega
  rw [e, BitVec.toNat_add]
  have h₁ := Nat.mod_le ((a - r.base).toNat + (BitVec.ofNat 64 k).toNat) (2 ^ 64)
  have h₂ : (BitVec.ofNat 64 k).toNat ≤ k := by rw [BitVec.toNat_ofNat]; exact Nat.mod_le _ _
  omega

theorem inRegions_off {rs : List Region} {a : Addr} {n k l : Nat} (h : InRegions rs a n) (hk : k + l ≤ n) :
    InRegions rs (a + BitVec.ofNat 64 k) l := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, contains_off hc hk⟩

/-! ## Fields of an address -/

theorem setWidth_32_64_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- Byte `d` of a 32-bit value after `rev32` is its byte `3 - d`. -/
theorem rev32_byte (x : BitVec 32) : ∀ d < 4, (rev32 x).extractLsb' (8 * d) 8 = x.extractLsb' (8 * (3 - d)) 8 := by
  intro d hd
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega_using [hd]
  rcases this with rfl | rfl | rfl | rfl <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [rev32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi]
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega_using [hi]
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Byte `d` of a 32-bit value, as `toByte` writes byte `3 - d` of it. -/
theorem toByte4_getElem (x : BitVec 32) {d : Nat} (hd : d < 4) :
    (Spec.SlhDsa.toByte x.toNat 4)[d]'(by simp [Spec.SlhDsa.toByte, hd]) = x.extractLsb' (8 * (3 - d)) 8 := by
  simp only [Spec.SlhDsa.toByte, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (256 : Nat) ^ (4 - 1 - d) = 2 ^ (8 * (3 - d)) by rw [Nat.pow_mul]]

/-- The bytes of `rev32 x` little-endian are `x`'s big-endian. -/
theorem rev32_bytes (x : BitVec 32) :
    ((List.range 4).map fun d => (rev32 x).extractLsb' (8 * d) 8) = Spec.SlhDsa.toByte x.toNat 4 := by
  apply List.ext_getElem (by simp [Spec.SlhDsa.toByte])
  intro d h₁ _
  simp only [List.length_map, List.length_range] at h₁
  rw [List.getElem_map, List.getElem_range, rev32_byte _ _ h₁, toByte4_getElem _ h₁]

/-- What a store of a field (as `setField` and `setFieldR` make it) does. -/
structure FieldPost (s s' : State) (a : Addr) (v : Nat) : Prop where
  gpr : ∀ r, r ≠ .x9 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bytes : bytesAt s'.mem a 4 = Spec.SlhDsa.toByte v 4
  frame : Frame [⟨a, 4⟩] s.mem s'.mem

variable {is : List Instr} {s : State} {Q : State → Prop}

theorem toNat_setWidth32 {x : BitVec 64} (h : x.toNat < 2 ^ 32) : (x.setWidth 32).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

/-- `setFieldR b d r`: the field at `b + d` set to the register `r`, whose
value is below `2³²`. -/
theorem setFieldR_ok {b r : Reg} (hb : b ≠ .x9) {d : Nat} (hd : d % 4 = 0 ∧ d < 16384)
    (hr : (s.gpr r).toNat < 2 ^ 32) (hin : InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 4)
    (k : ∀ s', FieldPost s s' (s.gpr b + BitVec.ofNat 64 d) (s.gpr r).toNat → WP isa (.block is) s' Q) :
    WP isa (.block (setFieldR b d r ++ is)) s Q := by
  simp only [setFieldR, List.cons_append, List.nil_append]
  refine wp_rev32 fun s₁ u₁ => ?_
  refine wp_strw (a := s.gpr b + BitVec.ofNat 64 d) hd (by rw [u₁.other _ hb]) (by rw [u₁.wr]; exact hin)
    fun s₂ u₂ => k s₂ ⟨fun g h => by rw [u₂.gpr, u₁.other _ h], by rw [u₂.sp, u₁.sp], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr], ?_, ?_⟩
  · rw [u₂.mem, u₁.gpr, setWidth_32_64_32, u₁.mem, bytesAt_writeW32, rev32_bytes, toNat_setWidth32 hr]
  · rw [u₂.mem, u₁.mem]; exact frame_writeW (w := 32) _ _ _ (by decide)

theorem bswap32_lo {v : Nat} (hv : v < 65536) : bswap32 v % 65536 = 0 := by
  unfold bswap32
  rw [Nat.div_eq_of_lt (show v < 65536 from hv), Nat.div_eq_of_lt (show v < 2 ^ 24 by omega_using [hv]),
    show v % 256 * 2 ^ 24 + v / 256 % 256 * 2 ^ 16 + 0 % 256 * 256 + 0 % 256 =
      65536 * (v % 256 * 256 + v / 256 % 256) by omega_using []]
  exact Nat.mul_mod_right _ _

theorem setField_eq (b : Reg) (d : Nat) {v : Nat} (hv : v < 65536) :
    setField b d v = [.movz .w .x9 (BitVec.ofNat 16 (bswap32 v / 65536)) 1, .str .w .x9 b d] := by
  simp only [setField, movW9, bswap32_lo hv, ite_true, List.cons_append, List.nil_append]

/-- The values the code sets fields to with `setField`. -/
abbrev FieldV (v : Nat) : Prop := v = 0 ∨ v = 1 ∨ v = 5

theorem FieldV.lt {v : Nat} (h : FieldV v) : v < 65536 := by rcases h with rfl | rfl | rfl <;> decide

theorem field_bytes {v : Nat} (hv : FieldV v) :
    ((List.range 4).map fun d =>
      ((((BitVec.ofNat 16 (bswap32 v / 65536)).setWidth 32 <<< (16 * 1)).setWidth 64).setWidth 32).extractLsb'
        (8 * d) 8) = Spec.SlhDsa.toByte v 4 := by
  rcases hv with rfl | rfl | rfl <;> decide

/-- `setField b d v`: the field at `b + d` set to `v` (below `2¹⁶`). -/
theorem setField_ok {b : Reg} (hb : b ≠ .x9) {d v : Nat} (hd : d % 4 = 0 ∧ d < 16384) (hv : FieldV v)
    (hin : InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 4)
    (k : ∀ s', FieldPost s s' (s.gpr b + BitVec.ofNat 64 d) v → WP isa (.block is) s' Q) :
    WP isa (.block (setField b d v ++ is)) s Q := by
  rw [setField_eq b d hv.lt]
  simp only [List.cons_append, List.nil_append]
  refine wp_movzw (by decide) fun s₁ u₁ => ?_
  refine wp_strw (a := s.gpr b + BitVec.ofNat 64 d) hd (by rw [u₁.other _ hb]) (by rw [u₁.wr]; exact hin)
    fun s₂ u₂ => k s₂ ⟨fun g h => by rw [u₂.gpr, u₁.other _ h], by rw [u₂.sp, u₁.sp], by rw [u₂.rd, u₁.rd],
      by rw [u₂.wr, u₁.wr], ?_, ?_⟩
  · rw [u₂.mem, u₁.gpr, u₁.mem, bytesAt_writeW32, field_bytes hv]
  · rw [u₂.mem, u₁.mem]; exact frame_writeW (w := 32) _ _ _ (by decide)

/-! ## Copies -/

/-- What a copy of `len` bytes from `src` to `dst` does. -/
structure CopyPost (s s' : State) (dst src : Addr) (len : Nat) : Prop where
  gpr : ∀ r, r ≠ .x14 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bytes : ∀ q < len, s'.mem (dst + BitVec.ofNat 64 q) = s.mem (src + BitVec.ofNat 64 q)
  frame : Frame [⟨dst, len⟩] s.mem s'.mem

theorem CopyPost.refl (s : State) (dst src : Addr) : CopyPost s s dst src 0 :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩

theorem CopyPost.trans {s s₁ s₂ : State} {D Sr : Addr} {a b : Nat} (h₁ : CopyPost s s₁ D Sr a)
    (h₂ : CopyPost s₁ s₂ (D + BitVec.ofNat 64 a) (Sr + BitVec.ofNat 64 a) b)
    (hdis : Region.Disjoint ⟨D, a + b⟩ ⟨Sr, a + b⟩) (hab : a + b < 2 ^ 64) : CopyPost s s₂ D Sr (a + b) := by
  refine ⟨fun r h => by rw [h₂.gpr r h, h₁.gpr r h], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], fun q hq => ?_, ?_⟩
  · by_cases c : q < a
    · rw [h₂.frame.bytes (R := ⟨D, a⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint D (Nat.le_refl a) (by omega_using [hab])) (by show a ≤ 2 ^ 64; omega_using [hab]) c,
        h₁.bytes q c]
    · have e₁ : D + BitVec.ofNat 64 q = D + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a) := by
        rw [ofNat_add', Nat.add_sub_cancel' (by omega_using [c])]
      have e₂ : Sr + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a) = Sr + BitVec.ofNat 64 q := by
        rw [ofNat_add', Nat.add_sub_cancel' (by omega_using [c])]
      rw [e₁, h₂.bytes _ (by omega_using [hq, c]), e₂]
      exact h₁.frame.bytes (R := ⟨Sr, a + b⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdis.symm.sub_right (Region.sub_prefix (Nat.le_add_right a b))) (by show a + b ≤ 2 ^ 64; omega_using [hab]) hq
  · refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (Nat.le_add_right a b)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base D (Nat.le_refl _)⟩

/-- A word through `x14`. -/
theorem copy8_ok {t sr : Reg} (ht : t ≠ .x14) {e₁ e₂ : Nat} (h₁ : e₁ % 8 = 0 ∧ e₁ < 32768)
    (h₂ : e₂ % 8 = 0 ∧ e₂ < 32768) (hsrc : InRegions (s.rd ++ s.wr) (s.gpr sr + BitVec.ofNat 64 e₁) 8)
    (hdst : InRegions s.wr (s.gpr t + BitVec.ofNat 64 e₂) 8)
    (k : ∀ s', CopyPost s s' (s.gpr t + BitVec.ofNat 64 e₂) (s.gpr sr + BitVec.ofNat 64 e₁) 8 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .x .x14 sr e₁ :: .str .x .x14 t e₂ :: is)) s Q := by
  refine wp_ldr h₁ rfl hsrc fun s₁ u₁ => ?_
  refine wp_str h₂ (by rw [u₁.other _ ht]) (by rw [u₁.wr]; exact hdst) fun s₂ u₂ => k s₂ ?_
  refine ⟨fun r h => by rw [u₂.gpr, u₁.other _ h], by rw [u₂.sp, u₁.sp], by rw [u₂.rd, u₁.rd],
    by rw [u₂.wr, u₁.wr], fun q hq => ?_, ?_⟩
  · rw [u₂.mem, u₁.gpr, writeW64_in _ _ _ hq, byte_readW64 _ _ hq]
  · rw [u₂.mem, u₁.mem]; exact frame_writeW (w := 64) _ _ _ (by decide)

/-- Two words through `v16`. -/
theorem copy16_ok {t sr : Reg} {e₁ e₂ : Nat} (h₁ : e₁ % 16 = 0 ∧ e₁ < 65536)
    (h₂ : e₂ % 16 = 0 ∧ e₂ < 65536) (hsrc : InRegions (s.rd ++ s.wr) (s.gpr sr + BitVec.ofNat 64 e₁) 16)
    (hdst : InRegions s.wr (s.gpr t + BitVec.ofNat 64 e₂) 16)
    (k : ∀ s', CopyPost s s' (s.gpr t + BitVec.ofNat 64 e₂) (s.gpr sr + BitVec.ofNat 64 e₁) 16 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.ldrq .v16 sr e₁ :: .strq .v16 t e₂ :: is)) s Q := by
  refine wp_ldrq h₁ rfl hsrc fun s₁ u₁ => ?_
  refine wp_strq h₂ (by rw [u₁.gpr]) (by rw [u₁.wr]; exact hdst) fun s₂ u₂ => k s₂ ?_
  refine ⟨fun r _ => by rw [u₂.gpr, u₁.gpr], by rw [u₂.sp, u₁.sp], by rw [u₂.rd, u₁.rd],
    by rw [u₂.wr, u₁.wr], fun q hq => ?_, ?_⟩
  · rw [u₂.mem, u₁.v, write_in _ _ _ hq (by decide), Mem.extractLsb'_read _ _ hq]
  · rw [u₂.mem, u₁.mem]; exact frame_write _ _ _ (by decide)

theorem copyWords_go_zero (t : Reg) (d₂ : Nat) (sr : Reg) (d₁ i : Nat) : copyWords.go t d₂ sr d₁ 0 i = [] := by
  rw [copyWords.go]
theorem copyWords_go_one (t : Reg) (d₂ : Nat) (sr : Reg) (d₁ i : Nat) :
    copyWords.go t d₂ sr d₁ 1 i = [.ldr .x .x14 sr (d₁ + 8 * i), .str .x .x14 t (d₂ + 8 * i)] := by
  rw [copyWords.go]
theorem copyWords_go_two (t : Reg) (d₂ : Nat) (sr : Reg) (d₁ m i : Nat) :
    copyWords.go t d₂ sr d₁ (m + 2) i =
      if (d₁ + 8 * i) % 16 = 0 ∧ (d₂ + 8 * i) % 16 = 0 then
        ([.ldrq .v16 sr (d₁ + 8 * i), .strq .v16 t (d₂ + 8 * i)] : List Instr) ++ copyWords.go t d₂ sr d₁ m (i + 2)
      else ([.ldr .x .x14 sr (d₁ + 8 * i), .str .x .x14 t (d₂ + 8 * i)] : List Instr) ++ copyWords.go t d₂ sr d₁ (m + 1) (i + 1) := by
  rw [copyWords.go]

/-- The words `i` to `i + m` of a copy. -/
theorem copyWords_go_ok {t sr : Reg} (ht : t ≠ .x14) (hs : sr ≠ .x14) {d₁ d₂ : Nat} (hd₁ : d₁ % 8 = 0)
    (hd₂ : d₂ % 8 = 0) {A B : Addr} {R W : List Region} {w : Nat}
    (hsrc : InRegions (R ++ W) (B + BitVec.ofNat 64 d₁) (8 * w)) (hdst : InRegions W (A + BitVec.ofNat 64 d₂) (8 * w))
    (hdis : Region.Disjoint ⟨A + BitVec.ofNat 64 d₂, 8 * w⟩ ⟨B + BitVec.ofNat 64 d₁, 8 * w⟩)
    (hf₁ : d₁ + 8 * w ≤ 32768) (hf₂ : d₂ + 8 * w ≤ 32768) :
    ∀ m i, i + m ≤ w → ∀ s : State, s.gpr t = A → s.gpr sr = B → s.rd = R → s.wr = W →
      WP isa (.block (copyWords.go t d₂ sr d₁ m i)) s
        (fun s' => CopyPost s s' (A + BitVec.ofNat 64 (d₂ + 8 * i)) (B + BitVec.ofNat 64 (d₁ + 8 * i)) (8 * m)) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro i hi s hA hB hR hW
  have dis : ∀ {j l : Nat}, i ≤ j → j + l ≤ w → Region.Disjoint ⟨A + BitVec.ofNat 64 (d₂ + 8 * j), 8 * l⟩
      ⟨B + BitVec.ofNat 64 (d₁ + 8 * j), 8 * l⟩ := fun h₁ h₂ => by
    rw [← ofNat_add', ← ofNat_add']
    exact (hdis.sub_left (Offset.sub_base _ (by omega_using [h₂]))).sub_right (Offset.sub_base _ (by omega_using [h₂]))
  have src : ∀ {j l : Nat}, j + l ≤ w → InRegions (s.rd ++ s.wr) (s.gpr sr + BitVec.ofNat 64 (d₁ + 8 * j)) (8 * l) :=
    fun h => by rw [hB, hR, hW, ← ofNat_add']; exact inRegions_off hsrc (by omega_using [h])
  have dst : ∀ {j l : Nat}, j + l ≤ w → InRegions s.wr (s.gpr t + BitVec.ofNat 64 (d₂ + 8 * j)) (8 * l) :=
    fun h => by rw [hA, hW, ← ofNat_add']; exact inRegions_off hdst (by omega_using [h])
  match m, ih with
  | 0, _ =>
    rw [copyWords_go_zero]
    exact WP.block_nil (CopyPost.refl _ _ _)
  | 1, _ =>
    rw [copyWords_go_one]
    refine copy8_ok ht ⟨by omega_using [hd₁], by omega_using [hf₁, hi]⟩ ⟨by omega_using [hd₂], by omega_using [hf₂, hi]⟩
      (src (l := 1) hi) (dst (l := 1) hi) fun s' c => WP.block_nil ?_
    rw [hA, hB] at c; exact c
  | m + 2, ih =>
    rw [copyWords_go_two]
    split
    · rename_i ha
      simp only [List.cons_append, List.nil_append]
      refine copy16_ok ⟨ha.1, by omega_using [hf₁, hi]⟩ ⟨ha.2, by omega_using [hf₂, hi]⟩
        (src (l := 2) (by omega_using [hi])) (dst (l := 2) (by omega_using [hi])) fun s₁ c₁ => ?_
      rw [hA, hB] at c₁
      refine WP.mono (ih m (by omega_using []) (i + 2) (by omega_using [hi]) s₁ (by rw [c₁.gpr _ ht, hA])
        (by rw [c₁.gpr _ hs, hB]) (by rw [c₁.rd, hR]) (by rw [c₁.wr, hW])) fun s₂ c₂ => ?_
      rw [show A + BitVec.ofNat 64 (d₂ + 8 * (i + 2)) = A + BitVec.ofNat 64 (d₂ + 8 * i) + BitVec.ofNat 64 16 by
          rw [ofNat_add', show d₂ + 8 * i + 16 = d₂ + 8 * (i + 2) by omega_using []],
        show B + BitVec.ofNat 64 (d₁ + 8 * (i + 2)) = B + BitVec.ofNat 64 (d₁ + 8 * i) + BitVec.ofNat 64 16 by
          rw [ofNat_add', show d₁ + 8 * i + 16 = d₁ + 8 * (i + 2) by omega_using []]] at c₂
      have := CopyPost.trans c₁ c₂ (by rw [show 16 + 8 * m = 8 * (m + 2) by omega_using []]; exact dis (Nat.le_refl _) hi)
        (by omega_using [hf₁, hi])
      rwa [show 16 + 8 * m = 8 * (m + 2) by omega_using []] at this
    · simp only [List.cons_append, List.nil_append]
      refine copy8_ok ht ⟨by omega_using [hd₁], by omega_using [hf₁, hi]⟩ ⟨by omega_using [hd₂], by omega_using [hf₂, hi]⟩
        (src (l := 1) (by omega_using [hi])) (dst (l := 1) (by omega_using [hi])) fun s₁ c₁ => ?_
      rw [hA, hB] at c₁
      refine WP.mono (ih (m + 1) (by omega_using []) (i + 1) (by omega_using [hi]) s₁ (by rw [c₁.gpr _ ht, hA])
        (by rw [c₁.gpr _ hs, hB]) (by rw [c₁.rd, hR]) (by rw [c₁.wr, hW])) fun s₂ c₂ => ?_
      rw [show A + BitVec.ofNat 64 (d₂ + 8 * (i + 1)) = A + BitVec.ofNat 64 (d₂ + 8 * i) + BitVec.ofNat 64 8 by
          rw [ofNat_add', show d₂ + 8 * i + 8 = d₂ + 8 * (i + 1) by omega_using []],
        show B + BitVec.ofNat 64 (d₁ + 8 * (i + 1)) = B + BitVec.ofNat 64 (d₁ + 8 * i) + BitVec.ofNat 64 8 by
          rw [ofNat_add', show d₁ + 8 * i + 8 = d₁ + 8 * (i + 1) by omega_using []]] at c₂
      have := CopyPost.trans c₁ c₂ (by rw [show 8 + 8 * (m + 1) = 8 * (m + 2) by omega_using []]; exact dis (Nat.le_refl _) hi)
        (by omega_using [hf₁, hi])
      rwa [show 8 + 8 * (m + 1) = 8 * (m + 2) by omega_using []] at this

/-- `copyWords t d₂ sr d₁ w`: the `8 w` bytes at `sr + d₁` copied to `t + d₂`. -/
theorem copyWords_ok {t sr : Reg} (ht : t ≠ .x14) (hs : sr ≠ .x14) {d₁ d₂ w : Nat} (hd₁ : d₁ % 8 = 0)
    (hd₂ : d₂ % 8 = 0) (hsrc : InRegions (s.rd ++ s.wr) (s.gpr sr + BitVec.ofNat 64 d₁) (8 * w))
    (hdst : InRegions s.wr (s.gpr t + BitVec.ofNat 64 d₂) (8 * w))
    (hdis : Region.Disjoint ⟨s.gpr t + BitVec.ofNat 64 d₂, 8 * w⟩ ⟨s.gpr sr + BitVec.ofNat 64 d₁, 8 * w⟩)
    (hf₁ : d₁ + 8 * w ≤ 32768) (hf₂ : d₂ + 8 * w ≤ 32768) :
    WP isa (.block (copyWords t d₂ sr d₁ w)) s
      (fun s' => CopyPost s s' (s.gpr t + BitVec.ofNat 64 d₂) (s.gpr sr + BitVec.ofNat 64 d₁) (8 * w)) := by
  have := copyWords_go_ok ht hs hd₁ hd₂ hsrc hdst hdis hf₁ hf₂ w 0 (by omega_using []) s rfl rfl rfl rfl
  simpa only [copyWords, Nat.mul_zero, Nat.add_zero] using this

/-! ## Masks -/

/-- `-((x - 1) ≫ 63)`: all ones if `x` is 0, and 0 if it is positive and below `2⁶³`. -/
theorem mask_zero {x : BitVec 64} (hx : x.toNat < 2 ^ 63) :
    (0 : BitVec 64) - ((x - 1) >>> 63) = if x = 0 then BitVec.allOnes 64 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · simp only [h, ↓reduceIte]
    have h1 : (1 : BitVec 64) ≤ x := by
      rw [BitVec.le_def]
      have : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
      show 1 ≤ _; omega_using [this]
    have hs : (x - 1) >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub_of_le h1, Nat.shiftRight_eq_div_pow]
      show _ = 0
      exact Nat.div_eq_of_lt (by have : (1 : BitVec 64).toNat = 1 := rfl; omega_using [hx, this])
    rw [hs]; decide

/-- The mask selects. -/
theorem sel (b : Bool) (lw sw : BitVec 64) :
    sw ^^^ ((lw ^^^ sw) &&& (if b then BitVec.allOnes 64 else 0)) = if b then lw else sw := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm lw sw, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Blocks over `List.range`, one at a time. -/
theorem wp_range_flatMap {f : Nat → List Instr} {P : Nat → State → Prop} :
    ∀ (K : Nat) {s : State}, P 0 s → (∀ j < K, ∀ t, P j t → WP isa (.block (f j)) t (P (j + 1))) →
      WP isa (.block ((List.range K).flatMap f)) s (P K)
  | 0, _, h0, _ => WP.block_nil h0
  | K + 1, _, h0, hs => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (wp_range_flatMap K h0 fun j hj => hs j (by omega_using [hj]))
      fun t ht => hs K (by omega_using []) t ht)

/-- The masked copy of word `w` from `src + d₁` into `dst`, with the mask in `x12`. -/
def selWord (dst src : Reg) (d₁ w : Nat) : List Instr :=
  [.ldr .x .x13 dst (8 * w), .ldr .x .x14 src (d₁ + 8 * w), .logic .eor .x .x14 .x14 .x13,
    .logic .and .x .x14 .x14 .x12, .logic .eor .x .x13 .x13 .x14, .str .x .x13 dst (8 * w)]

/-- What the masked copy from `src` to `dst` does, for `len` bytes: the
bytes of `src` if `b`, and `dst`'s own otherwise. -/
structure SelPost (s s' : State) (b : Bool) (dst src : Addr) (len : Nat) : Prop where
  gpr : ∀ r, r ≠ .x13 → r ≠ .x14 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bytes : ∀ q < len, s'.mem (dst + BitVec.ofNat 64 q) =
    if b then s.mem (src + BitVec.ofNat 64 q) else s.mem (dst + BitVec.ofNat 64 q)
  frame : Frame [⟨dst, len⟩] s.mem s'.mem

theorem SelPost.trans {s s₁ s₂ : State} {b : Bool} {D Sr : Addr} {a c : Nat} (h₁ : SelPost s s₁ b D Sr a)
    (h₂ : SelPost s₁ s₂ b (D + BitVec.ofNat 64 a) (Sr + BitVec.ofNat 64 a) c)
    (hdis : Region.Disjoint ⟨D, a + c⟩ ⟨Sr, a + c⟩) (hac : a + c < 2 ^ 64) : SelPost s s₂ b D Sr (a + c) := by
  refine ⟨fun r h h' => by rw [h₂.gpr r h h', h₁.gpr r h h'], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], fun q hq => ?_, ?_⟩
  · by_cases cq : q < a
    · rw [h₂.frame.bytes (R := ⟨D, a⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint D (Nat.le_refl a) (by omega_using [hac])) (by show a ≤ 2 ^ 64; omega_using [hac]) cq,
        h₁.bytes q cq]
    · have e₁ : D + BitVec.ofNat 64 q = D + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a) := by
        rw [ofNat_add', Nat.add_sub_cancel' (by omega_using [cq])]
      have e₂ : Sr + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a) = Sr + BitVec.ofNat 64 q := by
        rw [ofNat_add', Nat.add_sub_cancel' (by omega_using [cq])]
      have fs : s₁.mem (Sr + BitVec.ofNat 64 q) = s.mem (Sr + BitVec.ofNat 64 q) :=
        h₁.frame.bytes (R := ⟨Sr, a + c⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hdis.symm.sub_right (Region.sub_prefix (Nat.le_add_right a c))) (by show a + c ≤ 2 ^ 64; omega_using [hac]) hq
      have fd : s₁.mem (D + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a)) =
          s.mem (D + BitVec.ofNat 64 a + BitVec.ofNat 64 (q - a)) :=
        h₁.frame.bytes (R := ⟨D + BitVec.ofNat 64 a, c⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint_base D (Nat.le_refl a) (by omega_using [hac])) (by show c ≤ 2 ^ 64; omega_using [hac])
          (by show q - a < c; omega_using [hq, cq])
      rw [e₁, h₂.bytes _ (by omega_using [hq, cq]), e₂, fs, fd]
  · refine (h₁.frame.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (Nat.le_add_right a c)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base D (Nat.le_refl _)⟩

/-- One word of the masked copy. -/
theorem sel8_ok {dst src : Reg} (hd : dst ≠ .x13 ∧ dst ≠ .x14) {b : Bool}
    (hm : s.gpr .x12 = if b then BitVec.allOnes 64 else 0) {d₁ w : Nat} (h₁ : (d₁ + 8 * w) % 8 = 0 ∧ d₁ + 8 * w < 32768)
    (h₂ : 8 * w < 32768) (hsrc : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 (d₁ + 8 * w)) 8)
    (hdst : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 (8 * w)) 8) (hs : src ≠ .x13) :
    WP isa (.block (selWord dst src d₁ w)) s
      (fun s' => SelPost s s' b (s.gpr dst + BitVec.ofNat 64 (8 * w)) (s.gpr src + BitVec.ofNat 64 (d₁ + 8 * w)) 8) := by
  have hdst' : InRegions (s.rd ++ s.wr) (s.gpr dst + BitVec.ofNat 64 (8 * w)) 8 := by
    obtain ⟨r, h, c⟩ := hdst; exact ⟨r, List.mem_append_right _ h, c⟩
  simp only [selWord]
  refine wp_ldr ⟨by omega_using [], h₂⟩ rfl hdst' fun s₁ u₁ => ?_
  refine wp_ldr h₁ (by rw [u₁.other _ hs]) (by rw [u₁.rd, u₁.wr]; exact hsrc) fun s₂ u₂ => ?_
  refine wp_eor fun s₃ u₃ => wp_and fun s₄ u₄ => wp_eor fun s₅ u₅ => ?_
  refine wp_str ⟨by omega_using [], h₂⟩ (by
      rw [u₅.other _ hd.1, u₄.other _ hd.2, u₃.other _ hd.2, u₂.other _ hd.2, u₁.other _ hd.1])
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hdst) fun s₆ u₆ => WP.block_nil ?_
  have hv : s₅.gpr .x13 = if b then s.mem.readW (s.gpr src + BitVec.ofNat 64 (d₁ + 8 * w)) 64
      else s.mem.readW (s.gpr dst + BitVec.ofNat 64 (8 * w)) 64 := by
    have a13 : s₂.gpr .x13 = s.mem.readW (s.gpr dst + BitVec.ofNat 64 (8 * w)) 64 := by
      rw [u₂.other _ (by decide), u₁.gpr]
    have a14 : s₂.gpr .x14 = s.mem.readW (s.gpr src + BitVec.ofNat 64 (d₁ + 8 * w)) 64 := by rw [u₂.gpr, u₁.mem]
    have a12 : s₂.gpr .x12 = if b then BitVec.allOnes 64 else 0 := by
      rw [u₂.other _ (by decide), u₁.other _ (by decide), hm]
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide),
      a13, a14, a12, sel]
  refine ⟨fun r h h' => by
      rw [u₆.gpr, u₅.other _ h, u₄.other _ h', u₃.other _ h', u₂.other _ h', u₁.other _ h],
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], fun q hq => ?_, ?_⟩
  · have hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    rw [u₆.mem, hm₅, writeW64_in _ _ _ hq, hv]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [byte_readW64 _ _ hq]
    · simp only [↓reduceIte]; rw [byte_readW64 _ _ hq]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact frame_writeW (w := 64) _ _ _ (by decide)

/-- The masked copy of `w` words from `src + d₁` into `dst`. -/
theorem selWords_ok {dst src : Reg} (hd : dst ≠ .x13 ∧ dst ≠ .x14) (hs : src ≠ .x13 ∧ src ≠ .x14) {b : Bool}
    (hm : s.gpr .x12 = if b then BitVec.allOnes 64 else 0) {d₁ w : Nat} (hd₁ : d₁ % 8 = 0)
    (hf₁ : d₁ + 8 * w ≤ 32768) (hf₂ : 8 * w ≤ 32768)
    (hsrc : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d₁) (8 * w))
    (hdst : InRegions s.wr (s.gpr dst) (8 * w))
    (hdis : Region.Disjoint ⟨s.gpr dst, 8 * w⟩ ⟨s.gpr src + BitVec.ofNat 64 d₁, 8 * w⟩) :
    WP isa (.block ((List.range w).flatMap (selWord dst src d₁))) s
      (fun s' => SelPost s s' b (s.gpr dst) (s.gpr src + BitVec.ofNat 64 d₁) (8 * w)) := by
  refine WP.mono (wp_range_flatMap (P := fun j t => j ≤ w → SelPost s t b (s.gpr dst) (s.gpr src + BitVec.ofNat 64 d₁) (8 * j))
    w (fun _ => ⟨fun _ _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩)
    fun j hj t ht => ?_) fun t h => h (Nat.le_refl _)
  have c := ht (by omega_using [hj])
  have hdt : t.gpr dst = s.gpr dst := c.gpr _ hd.1 hd.2
  have hst : t.gpr src = s.gpr src := c.gpr _ hs.1 hs.2
  refine WP.mono (sel8_ok (s := t) hd (b := b) (by rw [c.gpr _ (by decide) (by decide), hm])
      ⟨by omega_using [hd₁], by omega_using [hf₁, hj]⟩ (by omega_using [hf₂, hj])
      (by rw [hst, c.rd, c.wr, ← ofNat_add']; exact inRegions_off hsrc (by omega_using [hj]))
      (by rw [hdt, c.wr]
          have := inRegions_off (k := 8 * j) (l := 8) (show InRegions s.wr (s.gpr dst + BitVec.ofNat 64 0) (8 * w) by
            simpa using hdst) (by omega_using [hj])
          rwa [ofNat_add', Nat.zero_add] at this) hs.1) fun t' c' _ => ?_
  rw [hdt, hst, ← ofNat_add'] at c'
  have := SelPost.trans c c' (by
      rw [show 8 * j + 8 = 8 * (j + 1) by omega_using []]
      exact (hdis.sub_left (Region.sub_prefix (by omega_using [hj]))).sub_right (Region.sub_prefix (by omega_using [hj])))
    (by omega_using [hf₂, hj])
  rwa [show 8 * j + 8 = 8 * (j + 1) by omega_using []] at this

/-! ## The multiplication by `n` -/

theorem shl_ofNat (x k : Nat) : BitVec.ofNat 64 x <<< k = BitVec.ofNat 64 (x * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- `mulN n r tmp`: `r ← r·n`, for `n` 16, 24 or 32 and `tmp ≠ r`; it writes
only `r` and `tmp`. -/
theorem mulN_ok {n : Nat} (hn : n = 16 ∨ n = 24 ∨ n = 32) {r tmp : Reg} (hrt : r ≠ tmp) {x : Nat}
    (hx : s.gpr r = BitVec.ofNat 64 x)
    (k : ∀ s', s'.gpr r = BitVec.ofNat 64 (x * n) → (∀ g, g ≠ r → g ≠ tmp → s'.gpr g = s.gpr g) →
      s'.sp = s.sp → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (mulN n r tmp ++ is)) s Q := by
  rcases hn with rfl | rfl | rfl
  · simp only [mulN, show (16 : Nat) ≠ 24 by decide, ite_false, ite_true, List.cons_append, List.nil_append]
    refine wp_lsl (by decide) fun s₁ u₁ => k s₁ ?_ (fun g h _ => u₁.other _ h) u₁.sp u₁.mem u₁.rd u₁.wr
    rw [u₁.gpr, hx, shl_ofNat]
  · simp only [mulN, ite_true, List.cons_append, List.nil_append]
    refine wp_lsl (by decide) fun s₁ u₁ => wp_lsl (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ =>
      k s₃ ?_ (fun g h₁ h₂ => ?_) ?_ ?_ ?_ ?_
    · rw [u₃.gpr, u₂.gpr, u₂.other _ hrt.symm, u₁.gpr, u₁.other _ hrt, hx, shl_ofNat, shl_ofNat, ← BitVec.ofNat_add]
      congr 1; omega_using []
    · rw [u₃.other _ h₁, u₂.other _ h₁, u₁.other _ h₂]
    · rw [u₃.sp, u₂.sp, u₁.sp]
    · rw [u₃.mem, u₂.mem, u₁.mem]
    · rw [u₃.rd, u₂.rd, u₁.rd]
    · rw [u₃.wr, u₂.wr, u₁.wr]
  · simp only [mulN, show (32 : Nat) ≠ 24 by decide, show (32 : Nat) ≠ 16 by decide, ite_false,
      List.cons_append, List.nil_append]
    refine wp_lsl (by decide) fun s₁ u₁ => k s₁ ?_ (fun g h _ => u₁.other _ h) u₁.sp u₁.mem u₁.rd u₁.wr
    rw [u₁.gpr, hx, shl_ofNat]

/-! ## The blocks keep v8–v15 -/

theorem kv_setFieldR (b : Reg) (d : Nat) (r : Reg) : (setFieldR b d r).all keepsV = true := rfl

theorem kv_setField (b : Reg) (d : Nat) {v : Nat} (hv : v < 65536) : (setField b d v).all keepsV = true := by
  rw [setField_eq b d hv]; rfl

theorem kv_copyWords_go (t : Reg) (d₂ : Nat) (sr : Reg) (d₁ : Nat) :
    ∀ m i, (copyWords.go t d₂ sr d₁ m i).all keepsV = true := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro i
  match m, ih with
  | 0, _ => rw [copyWords_go_zero]; rfl
  | 1, _ => rw [copyWords_go_one]; rfl
  | m + 2, ih =>
    rw [copyWords_go_two]
    split
    · rw [List.all_append, ih m (by omega_using []) (i + 2)]; rfl
    · rw [List.all_append, ih (m + 1) (by omega_using []) (i + 1)]; rfl

theorem kv_copyWords (t : Reg) (d₂ : Nat) (sr : Reg) (d₁ w : Nat) : (copyWords t d₂ sr d₁ w).all keepsV = true :=
  kv_copyWords_go t d₂ sr d₁ w 0

theorem kv_mulN (n : Nat) (r t : Reg) : (mulN n r t).all keepsV = true := by
  unfold mulN; split <;> rfl

theorem kv_flatMap {f : Nat → List Instr} (K : Nat) (h : ∀ k, (f k).all keepsV = true) :
    ((List.range K).flatMap f).all keepsV = true := by
  simp only [List.all_flatMap, List.all_eq_true, List.mem_range]
  exact fun k _ => List.all_eq_true.mp (h k)

theorem kv_selWords (dst src : Reg) (d₁ w : Nat) : ((List.range w).flatMap (selWord dst src d₁)).all keepsV = true :=
  kv_flatMap w fun _ => rfl

end VG.Proof.SlhDsa.AArch64.Blocks
