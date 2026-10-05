import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Impl.MdStream.X86
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Inline

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.X86.Common`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on x86 (32-bit): common lemmas

The contracts the generic proofs are written against, what they need of a hash
function's parameters (`Dims`, `Shape`) and of its compression function
(`CalleeOk`), the call of the compression function (`compressAt_ok`),
weakest-precondition rules for the instructions used that expose only what
changes, and arithmetic on 32-bit values.
-/

namespace VG.Proof.MdStream.X86

open VG VG.X86 VG.Impl.MdStream.X86
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)

/-! ## Regions -/

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho]
  exact h

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := by
  intro a ha
  simp only [Region.Contains] at *
  have : (a - base).toNat ≤ (a - (base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by
        rw [VG.Offset.sub_add_eq, BitVec.sub_add_cancel],
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
    exact Nat.mod_le _ _
  omega

theorem frame_bytes {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {R : Region}
    (hd : ∀ r ∈ rs, R.Disjoint r) (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) := by
  refine hf _ fun r hr hc => hd r hr _ ?_ hc
  simp only [Region.Contains]
  rw [VG.Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem addr_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

/-- `[x + d]`, for a word within a region at `x` inside the 32-bit address space. -/
theorem contains_addr {x : BitVec 32} {d n len : Nat} (h : d + n ≤ len) (hn : 0 < n)
    (hx : x.toNat + len ≤ 2 ^ 32) :
    (⟨x.setWidth 64, len⟩ : Region).Contains (addr x d) n := by
  rw [addr_eq (by omega)]
  exact VG.Proof.MdStream.X86.contains_offset h (by omega)

/-- `[(x + k) + d]`, where nothing wraps around the 32-bit address space. -/
theorem addr_add_ofNat {x : BitVec 32} {k d : Nat} (h : x.toNat + k + d < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 k) d = x.setWidth 64 + BitVec.ofNat 64 (k + d) := by
  simp only [addr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k) (by omega), Nat.mod_eq_of_lt (a := x.toNat + k + d) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k + d) (by omega), Nat.mod_eq_of_lt (a := x.toNat) (by omega),
    Nat.mod_eq_of_lt (a := k + d) (by omega), Nat.mod_eq_of_lt (a := x.toNat + (k + d)) (by omega)]
  omega

/-- Two accesses `[x + d]` and `[x + e]` of `n` and `k` bytes that do not overlap. -/
theorem addr_sep {x : BitVec 32} {d e n k : Nat} (hd : x.toNat + d + n ≤ 2 ^ 32) (he : x.toNat + e + k ≤ 2 ^ 32)
    (h : d + n ≤ e ∨ e + k ≤ d) : Mem.Sep (addr x d) n (addr x e) k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact fun _ h₁ => absurd h₁ (Nat.not_lt_zero _)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact fun _ _ h₂ => absurd h₂ (Nat.not_lt_zero _)
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sep _ h (by omega) (by omega)

theorem readW_writeW_addr (m : Mem) {x : BitVec 32} (v : BitVec 32) {d e : Nat}
    (hd : x.toNat + d + 4 ≤ 2 ^ 32) (he : x.toNat + e + 4 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr x e) v).readW (addr x d) 32 = m.readW (addr x d) 32 :=
  Mem.readW_writeW_sep (VG.Proof.MdStream.X86.addr_sep hd he h) (by decide)

theorem add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-- A region within one of `rs'`, at offset `o`. -/
theorem within {r : Region} {rs' : List Region} (r' : Region) (hr' : r' ∈ rs') (o : Nat)
    (hb : r.base = r'.base + BitVec.ofNat 64 o) (hl : o + r.len ≤ r'.len) :
    ∃ r' ∈ rs', ∃ o, r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len :=
  ⟨r', hr', o, hb, hl⟩

/-! ## Arithmetic -/

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
  conv_lhs => rw [show a = (a - b) + b by omega, BitVec.ofNat_add]
  rw [BitVec.add_sub_cancel]

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

theorem ofNat_succ (k : Nat) : BitVec.ofNat 32 (k + 1) = BitVec.ofNat 32 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, VG.Proof.MdStream.X86.ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem ofNat_add_add (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem lit32 (n : Nat) : (OfNat.ofNat n : BitVec 32) = BitVec.ofNat 32 n := rfl

theorem toNat_ofNat_lt {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : VG.Proof.MdStream.X86.Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) (d : Reg) (x : BitVec 32) (c o : Bool) (v : BitVec 32) :
    VG.Proof.MdStream.X86.Upd s ((arithFlags s x c o).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.setFlags (s : State) (d : Reg) (c o z n : Option Bool) (v : BitVec 32) :
    VG.Proof.MdStream.X86.Upd s ((s.setFlags c o z n).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m` (the flags aside). -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `s'` is `s` with other flags. -/
structure Fupd (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', VG.Proof.MdStream.X86.Upd s s' d (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movi {d : Reg} {v : BitVec 32} (k : ∀ s', VG.Proof.MdStream.X86.Upd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.MdStream.X86.Upd s s' d (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d (s.mem.readW a 32)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc, State.load32, ha, hin]

theorem wp_store {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', VG.Proof.MdStream.X86.Mupd s s' (s.mem.writeW a (s.gpr r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store32, ha, hout]

theorem wp_addi {d : Reg} {v : BitVec 32} (k : ∀ s', VG.Proof.MdStream.X86.Upd s s' d (s.gpr d + v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_add {d r : Reg} (k : ∀ s', VG.Proof.MdStream.X86.Upd s s' d (s.gpr d + s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.MdStream.X86.Upd s s' d (s.gpr d - v) → s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_sub {d r : Reg}
    (k : ∀ s', VG.Proof.MdStream.X86.Upd s s' d (s.gpr d - s.gpr r) → s'.zf = some (s.gpr d - s.gpr r == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_andi {d : Reg} {v : BitVec 32} (k : ∀ s', VG.Proof.MdStream.X86.Upd s s' d (s.gpr d &&& v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_or {d r : Reg} (k : ∀ s', VG.Proof.MdStream.X86.Upd s s' d (s.gpr d ||| s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `cmp d, r`: CF is `d < r` (unsigned). -/
theorem wp_cmp {d r : Reg}
    (k : ∀ s', VG.Proof.MdStream.X86.Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.MdStream.X86.Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < v.toNat)) →
      s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem wp_test {d : Reg}
    (k : ∀ s', VG.Proof.MdStream.X86.Fupd s s' → s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_shr {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', VG.Proof.MdStream.X86.Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  WP.cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl) (k _ (Upd.setFlags _ _ _ _ _ _ _))

theorem wp_bswap {d : Reg} (k : ∀ s', VG.Proof.MdStream.X86.Upd s s' d (bswap (s.gpr d)) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', VG.Proof.MdStream.X86.Upd s s' d ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg8} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', VG.Proof.MdStream.X86.Mupd s s' (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ha, hout]

end

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem eval_e (s : State) : eval .e s = s.zf := rfl
theorem eval_ne (s : State) : eval .ne s = s.zf.map (!·) := rfl
theorem eval_b (s : State) : eval .b s = s.cf := rfl
theorem eval_ae (s : State) : eval .ae s = s.cf.map (!·) := rfl

theorem seq_assoc {M : ISA} {a b c : Prog M} {s : M.State} {Q : M.State → Prop} :
    WP M (.seq (.seq a b) c) s Q ↔ WP M (.seq a (.seq b c)) s Q := by
  simp only [WP.seq_iff]

/-! ## Sizes -/

/-- The sizes the generic proofs support, for blocks of `B` bytes, a hash
value of `N` bytes, a length field of `L` bytes, a compression function using
`so` bytes of scratch space, and `S` bytes of scratch space in all: checked for
each hash function by `decide`. -/
structure Dims (P : Params) (S : Nat) : Prop where
  B : P.B = 64 ∨ P.B = 128
  N : 0 < P.N ∧ P.N ≤ 64
  L : 0 < P.L ∧ P.L ≤ 16
  so : P.so + 28 ≤ S
  S : S ≤ 4096

section
variable {P : Params} {S : Nat} (hd : VG.Proof.MdStream.X86.Dims P S)
include hd

theorem Dims.pos : 0 < P.B := by rcases hd.B with h | h <;> omega

theorem Dims.le : P.B ≤ 128 := by rcases hd.B with h | h <;> omega

theorem Dims.ge : 64 ≤ P.B := by rcases hd.B with h | h <;> omega

theorem Dims.mod (n : Nat) : n % 2 ^ 64 % P.B = n % P.B := by
  rcases hd.B with h | h <;> rw [h] <;> omega

/-- A byte count modulo `B`, from its low word. -/
theorem Dims.mod_append (hi lo : BitVec 32) : (hi ++ lo).toNat % P.B = lo.toNat % P.B := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]
  rcases hd.B with h | h <;> rw [h] <;> omega

/-- `x mod B`, as `direct`, `update` and `finalize` compute it. -/
theorem Dims.and (x : BitVec 32) : x &&& BitVec.ofNat 32 (P.B - 1) = BitVec.ofNat 32 (x.toNat % P.B) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rcases hd.B with h | h <;> rw [h]
  · rw [show (64 - 1) % 2 ^ 32 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  · rw [show (128 - 1) % 2 ^ 32 = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

/-- The shift count of `direct`. -/
theorem Dims.lg : 1 ≤ Nat.log2 P.B ∧ Nat.log2 P.B ≤ 31 := by
  rcases hd.B with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

/-- `a / B`, as `direct` computes it. -/
theorem Dims.shr {a : Nat} (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a >>> Nat.log2 P.B = BitVec.ofNat 32 (a / P.B) := by
  have e : 2 ^ Nat.log2 P.B = P.B := by
    rcases hd.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.shiftRight_eq_div_pow, e, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

end

theorem restore_eq (P : Params) (b : Reg) : restore P b = [
    .mov .ebx (.mem (at_ b P.so)), .mov .esi (.mem (at_ b (P.so + 4))),
    .mov .edi (.mem (at_ b (P.so + 8))), .mov .ebp (.mem (at_ b (P.so + 12)))] :=
  rfl

theorem save_eq (P : Params) (b : Reg) : save P b = [
    .store (at_ b P.so) .ebx, .store (at_ b (P.so + 4)) .esi, .store (at_ b (P.so + 8)) .edi,
    .store (at_ b (P.so + 12)) .ebp] :=
  rfl

/-- The saved registers are outside the part of the scratch space the
compression function uses, before `count` and `out`. -/
theorem saved_offset {P : Params} {p : Reg × Nat} (hp : p ∈ saved P) : P.so ≤ p.2 ∧ p.2 + 4 ≤ P.so + 16 := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-! ## The contracts

The generic proofs are written against these; each hash function's own
contracts are these for its instance. -/

/-- The 64-bit `count` argument of `update`/`finalize`, in argument slots 1
and 2 (cdecl: the low word first). -/
def count (s : State) : BitVec 64 := VG.X86.arg s 2 ++ VG.X86.arg s 1

section
variable {P : Params} (H : Md P.B P.N P.L)

/-- The contract of the compression function
`compress(state, blocks, n, scratch)`: updates the hash value at `state`
with the `n` blocks at `blocks`, with `so` bytes of scratch space. -/
def compressK : Contract isa where
  pre s :=
    let state : Region := ⟨(VG.X86.arg s 0).setWidth 64, P.N⟩
    let blocks : Region := ⟨(VG.X86.arg s 1).setWidth 64, P.B * (VG.X86.arg s 2).toNat⟩
    let scratch : Region := ⟨(VG.X86.arg s 3).setWidth 64, P.so⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + P.N ≤ 2 ^ 32 ∧ (VG.X86.arg s 1).toNat + P.B * (VG.X86.arg s 2).toNat ≤ 2 ^ 32 ∧
    (VG.X86.arg s 3).toNat + P.so ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    H.stateAt s'.mem ((VG.X86.arg s 0).setWidth 64) =
      H.compressBlocks (H.stateAt s.mem ((VG.X86.arg s 0).setWidth 64)) s.mem ((VG.X86.arg s 1).setWidth 64) (VG.X86.arg s 2).toNat
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧
    VG.X86.arg s₁ 0 = VG.X86.arg s₂ 0 ∧ VG.X86.arg s₁ 1 = VG.X86.arg s₂ 1 ∧ VG.X86.arg s₁ 2 = VG.X86.arg s₂ 2 ∧ VG.X86.arg s₁ 3 = VG.X86.arg s₂ 3

variable (S : Nat)

/-- The contract of `update(state, count, data, len, scratch)`: if the state
represents a message of `count` bytes (modulo 2⁶⁴) from any initial hash
value, it then represents that message followed by the `len` bytes at
`data`. The arguments are only read (the taint analysis follows them in
memory only while nothing that may alias them is written). -/
def updK : Contract isa where
  pre s :=
    let state : Region := ⟨(VG.X86.arg s 0).setWidth 64, P.N + P.B⟩
    let data : Region := ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩
    let scratch : Region := ⟨(VG.X86.arg s 5).setWidth 64, S⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    stack.Disjoint data ∧
    (VG.X86.arg s 0).toNat + (P.N + P.B) ≤ 2 ^ 32 ∧ (VG.X86.arg s 3).toNat + (VG.X86.arg s 4).toNat ≤ 2 ^ 32 ∧
    (VG.X86.arg s 5).toNat + S ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ iv m, H.Repr iv s.mem ((VG.X86.arg s 0).setWidth 64) m → VG.Proof.MdStream.X86.count s = BitVec.ofNat 64 m.length →
    H.Repr iv s'.mem ((VG.X86.arg s 0).setWidth 64) (m ++ bytesAt s.mem ((VG.X86.arg s 3).setWidth 64) (VG.X86.arg s 4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- The contract of `finalize(state, count, out, scratch)`: if the state
represents a message of `count` bytes, writes its final hash value to `out`
(`N` bytes). The arguments are only read. -/
def finK : Contract isa where
  pre s :=
    let state : Region := ⟨(VG.X86.arg s 0).setWidth 64, P.N + P.B⟩
    let out : Region := ⟨(VG.X86.arg s 3).setWidth 64, P.N⟩
    let scratch : Region := ⟨(VG.X86.arg s 4).setWidth 64, S⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (VG.X86.arg s 0).toNat + (P.N + P.B) ≤ 2 ^ 32 ∧ (VG.X86.arg s 3).toNat + P.N ≤ 2 ^ 32 ∧
    (VG.X86.arg s 4).toNat + S ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ iv m, H.Repr iv s.mem ((VG.X86.arg s 0).setWidth 64) m → H.lenOk m.length →
    VG.Proof.MdStream.X86.count s = BitVec.ofNat 64 m.length → bytesAt s'.mem ((VG.X86.arg s 3).setWidth 64) P.N = H.hash iv m
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, VG.X86.arg s₁ i = VG.X86.arg s₂ i

/-- `finK`, but letting `finalize` write its arguments (as the contracts of the
hash functions whose `finalize` is only verified against this say). -/
def finKw : Contract isa :=
  { VG.Proof.MdStream.X86.finK H S with
    pre := fun s =>
      let state : Region := ⟨(VG.X86.arg s 0).setWidth 64, P.N + P.B⟩
      let out : Region := ⟨(VG.X86.arg s 3).setWidth 64, P.N⟩
      let scratch : Region := ⟨(VG.X86.arg s 4).setWidth 64, S⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [] ∧ s.wr = [state, out, scratch, args] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
      (VG.X86.arg s 0).toNat + (P.N + P.B) ≤ 2 ^ 32 ∧ (VG.X86.arg s 3).toNat + P.N ≤ 2 ^ 32 ∧
      (VG.X86.arg s 4).toNat + S ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

end

/-! ## What each hash function's own code must do -/

/-- The length field and the digest: `P.len` stores the length field for the
byte count in `[ebp + so + 16]` (low word) and `[ebp + so + 20]` (high word)
at `ebx + N + B - L`, writing only `eax`, `ecx` and `edx`, and `P.out` writes
the digest of the hash value at `ebx` to `eax`, writing only `ecx`. -/
structure Shape {P : Params} (H : Md P.B P.N P.L) : Prop where
  len : ∀ s : State, (s.gpr .ebx).toNat + (P.N + P.B) ≤ 2 ^ 32 →
    InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (P.so + 16)) 4 →
    InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (P.so + 20)) 4 →
    (∀ d, P.N + P.B - P.L ≤ d → d + 4 ≤ P.N + P.B → InRegions s.wr (addr (s.gpr .ebx) d) 4) →
    WP isa (.block P.len) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (P.N + P.B - P.L))
        (H.lenOf (s.mem.readW (addr (s.gpr .ebp) (P.so + 20)) 32 ++
          s.mem.readW (addr (s.gpr .ebp) (P.so + 16)) 32))
  out : ∀ s : State, (s.gpr .ebx).toNat + P.N ≤ 2 ^ 32 → (s.gpr .eax).toNat + P.N ≤ 2 ^ 32 →
    InRegions (s.rd ++ s.wr) ((s.gpr .ebx).setWidth 64) P.N → InRegions s.wr ((s.gpr .eax).setWidth 64) P.N →
    Region.Disjoint ⟨(s.gpr .ebx).setWidth 64, P.N⟩ ⟨(s.gpr .eax).setWidth 64, P.N⟩ →
    WP isa (.block P.out) s fun s' =>
      (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem ((s.gpr .eax).setWidth 64) (H.digest (H.stateAt s.mem ((s.gpr .ebx).setWidth 64)))

/-! ## The compression function -/

/-- What `compressAt` needs of the compression function it calls: that it is
correct, does not touch `esp` but to call, and calls nothing that uses the
stack. -/
structure CalleeOk {P : Params} (H : Md P.B P.N P.L) (code : Prog isa) : Prop where
  verified : ∀ s, (VG.Proof.MdStream.X86.compressK H).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MdStream.X86.compressK H).post s s'
  nosp : NoSp code
  stack : stackUse code = 0

/-- The 20 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 20 ≤ E.toNat) : below E 20 = ⟨E.setWidth 64 - 20, 20⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

theorem arg_eq (s : State) (i : Nat) : VG.X86.arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

section
variable {P : Params} {H : Md P.B P.N P.L}

/-- Compressing the `k` blocks at `eax` (`blk`, their number in `ecx`) into
the hash value at `st` (in register `sr`), with the scratch space at `scr`
(in register `cr`): a call of `compress(st, blk, k, scr)` in a frame of its
arguments, which uses the 20 bytes below `esp` (`E`) and writes only there,
the hash value and the first `so` bytes of the scratch space. -/
theorem compressFrame_ok {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86.CalleeOk H code) {sr cr : Reg}
    (hsr : sr ≠ .esp) (hcr : cr ≠ .esp) {s : State} {st scr blk E : BitVec 32} {k : Nat}
    (hesp : s.gpr .esp = E) (hS : s.gpr sr = st) (hC : s.gpr cr = scr) (heax : s.gpr .eax = blk)
    (hk : (s.gpr .ecx).toNat = k)
    (hE : 20 ≤ E.toNat) (f₀ : st.toNat + P.N ≤ 2 ^ 32) (f₁ : blk.toNat + P.B * k ≤ 2 ^ 32)
    (f₃ : scr.toNat + P.so ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨st.setWidth 64, P.N⟩ ⟨scr.setWidth 64, P.so⟩)
    (d₂ : Region.Disjoint ⟨blk.setWidth 64, P.B * k⟩ ⟨st.setWidth 64, P.N⟩)
    (d₃ : Region.Disjoint ⟨blk.setWidth 64, P.B * k⟩ ⟨scr.setWidth 64, P.so⟩)
    (dS : Region.Disjoint (below E 20) ⟨st.setWidth 64, P.N⟩)
    (dC : Region.Disjoint (below E 20) ⟨scr.setWidth 64, P.so⟩)
    (dB : Region.Disjoint (below E 20) ⟨blk.setWidth 64, P.B * k⟩)
    (hc : Covers [⟨blk.setWidth 64, P.B * k⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st.setWidth 64, P.N⟩, ⟨scr.setWidth 64, P.so⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st.setWidth 64, P.N⟩, ⟨scr.setWidth 64, P.so⟩, below E 20] s.mem s'.mem →
      H.stateAt s'.mem (st.setWidth 64) =
        H.compressBlocks (H.stateAt s.mem (st.setWidth 64)) s.mem (blk.setWidth 64) k → Q s') :
    WP isa (.frame (.push [cr, .ecx, .eax, sr]) (.call name code) (.pop .eax 4)) s Q := by
  have fit : 4 * [cr, Reg.ecx, .eax, sr].length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ [cr, Reg.ecx, .eax, sr] := by simp [Ne.symm hsr, Ne.symm hcr]
  set sE := (pushed [cr, Reg.ecx, .eax, sr] s).callEntry with hsE
  have a0 : VG.X86.arg sE 0 = st := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hS]
  have a1 : VG.X86.arg sE 1 = blk := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [heax]
  have a2 : (VG.X86.arg sE 2).toNat = k := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hk]
  have a3 : VG.X86.arg sE 3 = scr := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hC]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 16).setWidth 64 := by
    rw [hsE, callEntry_argAddr0, hesp]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 20 := by
    rw [hsE, callEntry_esp', hesp]; rfl
  have b16 : Region.Sub (below E 16) (below E 20) := below_sub (by omega) hE
  have r4 : Region.Sub ⟨(E - BitVec.ofNat 32 20).setWidth 64, 4⟩ (below E 20) := by
    have := below_inner (sp := E) (a := 4) (b := 20) (k := 16) (by omega) hE
    rw [show E - BitVec.ofNat 32 20 = E - BitVec.ofNat 32 16 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  refine WP.callWith (k := VG.Proof.MdStream.X86.compressK H) hf.verified hf.nosp (by simp) hrs
    (by rw [hf.stack, hesp]; simp only [List.length_cons, List.length_nil]; omega)
    (rd := [⟨blk.setWidth 64, P.B * k⟩, ⟨argAddr sE 0, 16⟩])
    (wr := [⟨st.setWidth 64, P.N⟩, ⟨scr.setWidth 64, P.so⟩])
    ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  · rw [← hsE]
    simp only [VG.Proof.MdStream.X86.compressK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
    refine ⟨trivial, trivial, d₁, d₂, d₃, dS.sub_left b16, dC.sub_left b16,
      dS.sub_left r4, dC.sub_left r4, f₀, f₁, f₃, ?_⟩
    rw [sub_toNat hE]; have := E.isLt; omega
  · rw [hesp]
    intro a n ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := hc a n ⟨_, List.mem_singleton_self _, by simpa using hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · refine InRegions_append_cons.mpr (.inl ?_)
      rw [eA] at hcn
      simp only [Region.Contains] at hcn ⊢
      simpa using hcn
    · obtain ⟨r', hr', hc'⟩ := hw a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := hw a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · rw [hesp]
    intro a n ⟨r, hr, hcn⟩
    obtain ⟨r', hr', hc'⟩ := hw a n ⟨r, hr, hcn⟩
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · rw [hf.stack, hesp] at f'
    have hsE' : Frame [below E 20] s.mem sE.mem := by
      have := callEntry_frame fit hrs
      rw [hesp] at this; exact this
    rw [← hsE] at post
    simp only [VG.Proof.MdStream.X86.compressK, arg_withRegions, State.withRegions_mem, a0, a1, a2, m₂] at post
    refine hQ s' rd' wr' cs' f' ?_
    have e₁ : H.stateAt sE.mem (st.setWidth 64) = H.stateAt s.mem (st.setWidth 64) :=
      H.stateAt_congr fun i hi =>
        hsE'.bytes (R := ⟨st.setWidth 64, P.N⟩) (by simpa using dS.symm) (by simp; omega) hi
    have e₂ : H.compressBlocks (H.stateAt s.mem (st.setWidth 64)) sE.mem (blk.setWidth 64) k =
        H.compressBlocks (H.stateAt s.mem (st.setWidth 64)) s.mem (blk.setWidth 64) k :=
      H.compressBlocks_congr fun j hj =>
        hsE'.bytes (R := ⟨blk.setWidth 64, P.B * k⟩) (by simpa using dB.symm) (by simp; omega) hj
    rw [post, e₁, e₂]

/-- Compressing the block at `eax` (`blk`) into the hash value at `st` (in
register `sr`), with the scratch space at `scr` (in register `cr`): a call of
`compress(st, blk, 1, scr)` in a frame of its arguments, which uses the 20
bytes below `esp` (`E`) and writes only there, the hash value and the first
`so` bytes of the scratch space. -/
theorem compressAt_ok {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86.CalleeOk H code) {sr cr : Reg}
    (hsr : sr ≠ .esp) (hcr : cr ≠ .esp) (hsr' : sr ≠ .ecx)
    (hcr' : cr ≠ .ecx) {s : State} {st scr blk E : BitVec 32}
    (hesp : s.gpr .esp = E) (hS : s.gpr sr = st) (hC : s.gpr cr = scr) (heax : s.gpr .eax = blk)
    (hE : 20 ≤ E.toNat) (f₀ : st.toNat + P.N ≤ 2 ^ 32) (f₁ : blk.toNat + P.B ≤ 2 ^ 32)
    (f₃ : scr.toNat + P.so ≤ 2 ^ 32)
    (d₁ : Region.Disjoint ⟨st.setWidth 64, P.N⟩ ⟨scr.setWidth 64, P.so⟩)
    (d₂ : Region.Disjoint ⟨blk.setWidth 64, P.B⟩ ⟨st.setWidth 64, P.N⟩)
    (d₃ : Region.Disjoint ⟨blk.setWidth 64, P.B⟩ ⟨scr.setWidth 64, P.so⟩)
    (dS : Region.Disjoint (below E 20) ⟨st.setWidth 64, P.N⟩)
    (dC : Region.Disjoint (below E 20) ⟨scr.setWidth 64, P.so⟩)
    (dB : Region.Disjoint (below E 20) ⟨blk.setWidth 64, P.B⟩)
    (hc : Covers [⟨blk.setWidth 64, P.B⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st.setWidth 64, P.N⟩, ⟨scr.setWidth 64, P.so⟩] s.wr)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st.setWidth 64, P.N⟩, ⟨scr.setWidth 64, P.so⟩, below E 20] s.mem s'.mem →
      H.stateAt s'.mem (st.setWidth 64) =
        H.compress (H.stateAt s.mem (st.setWidth 64)) (H.blockAt s.mem (blk.setWidth 64)) → Q s') :
    WP isa (compressAt name code sr cr) s Q := by
  rw [← Nat.mul_one P.B] at f₁ d₂ d₃ dB hc
  unfold compressAt compressWith
  refine WP.seq (WP.cons (s' := s.setReg .ecx 1) rfl (WP.block_nil ?_))
  set s₁ := s.setReg .ecx 1 with hs₁
  have g₁ : ∀ r, r ≠ .ecx → s₁.gpr r = s.gpr r := fun r h => by simp [hs₁, State.setReg, h]
  refine VG.Proof.MdStream.X86.compressFrame_ok (k := 1) hf hsr hcr (by rw [g₁ _ (by decide), hesp])
    (by rw [g₁ _ hsr', hS]) (by rw [g₁ _ hcr', hC]) (by rw [g₁ _ (by decide), heax])
    (by simp [hs₁, State.setReg]) hE f₀ f₁ f₃ d₁ d₂ d₃ dS dC dB (by rw [hs₁]; exact hc)
    (by rw [hs₁]; exact hw) fun s' rd' wr' cs' f' post => ?_
  have m₁ : s₁.mem = s.mem := by rw [hs₁]; rfl
  rw [m₁, Md.compressBlocks_one] at post
  rw [m₁] at f'
  refine hQ s' (by rw [rd']; rfl) (by rw [wr']; rfl) (fun r hr => ?_) f' post
  rw [cs' r hr, g₁ r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]

end

end VG.Proof.MdStream.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.X86.Finalize`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on x86 (32-bit): `update`

The correctness of `update`, for any hash function (`Md`) and any correct
compression function (`CalleeOk`), with `state` in `ebx`, `data` in `ebp`, the
bytes left in `esi`, the buffered bytes in `edi`, and `scratch` read from its
argument word (`[esp + 24]`, never written) for each call of the compression
function (`compressAt_ok`), which uses the 20 bytes below `esp`; and, from the
taint analysis of each hash function's code (which looks into the compression
function), that it is constant time.
-/

namespace VG.Proof.MdStream.X86.Update

open VG VG.X86 VG.Impl.MdStream.X86
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame)

/-! ## The precondition -/

section
variable (P : Params) (S : Nat) (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := VG.X86.arg s₀ 0
abbrev cnt : Nat := (VG.Proof.MdStream.X86.count s₀).toNat
abbrev dp : BitVec 32 := VG.X86.arg s₀ 3
abbrev len : Nat := (VG.X86.arg s₀ 4).toNat
abbrev scr : BitVec 32 := VG.X86.arg s₀ 5
abbrev stA : Addr := (VG.Proof.MdStream.X86.Update.st s₀).setWidth 64
abbrev dA : Addr := (VG.Proof.MdStream.X86.Update.dp s₀).setWidth 64
abbrev scA : Addr := (VG.Proof.MdStream.X86.Update.scr s₀).setWidth 64
abbrev stR : Region := ⟨VG.Proof.MdStream.X86.Update.stA s₀, P.N + P.B⟩
abbrev dR : Region := ⟨VG.Proof.MdStream.X86.Update.dA s₀, VG.Proof.MdStream.X86.Update.len s₀⟩
abbrev scR : Region := ⟨VG.Proof.MdStream.X86.Update.scA s₀, S⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(VG.Proof.MdStream.X86.Update.esp₀ s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (VG.Proof.MdStream.X86.Update.esp₀ s₀) 20
/-- The buffer. -/
abbrev buf : Addr := VG.Proof.MdStream.X86.Update.stA s₀ + BitVec.ofNat 64 P.N
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (VG.Proof.MdStream.X86.Update.dA s₀) (VG.Proof.MdStream.X86.Update.len s₀)

/-- Our caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop := ∀ p ∈ saved P, m.readW (addr (VG.Proof.MdStream.X86.Update.scr s₀) p.2) 32 = s₀.gpr p.1

end

/-- The messages the initial state represents, from `iv`. -/
def R₀ {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (VG.Proof.MdStream.X86.Update.stA s₀) m ∧ VG.Proof.MdStream.X86.count s₀ = BitVec.ofNat 64 m.length

structure Pre (P : Params) (S : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.MdStream.X86.Update.dR s₀, VG.Proof.MdStream.X86.Update.argR s₀]
  wr : s₀.wr = [VG.Proof.MdStream.X86.Update.stR P s₀, VG.Proof.MdStream.X86.Update.scR S s₀]
  st_scr : (VG.Proof.MdStream.X86.Update.stR P s₀).Disjoint (VG.Proof.MdStream.X86.Update.scR S s₀)
  d_st : (VG.Proof.MdStream.X86.Update.dR s₀).Disjoint (VG.Proof.MdStream.X86.Update.stR P s₀)
  d_scr : (VG.Proof.MdStream.X86.Update.dR s₀).Disjoint (VG.Proof.MdStream.X86.Update.scR S s₀)
  a_st : (VG.Proof.MdStream.X86.Update.argR s₀).Disjoint (VG.Proof.MdStream.X86.Update.stR P s₀)
  a_scr : (VG.Proof.MdStream.X86.Update.argR s₀).Disjoint (VG.Proof.MdStream.X86.Update.scR S s₀)
  ret_st : (VG.Proof.MdStream.X86.Update.retR s₀).Disjoint (VG.Proof.MdStream.X86.Update.stR P s₀)
  ret_scr : (VG.Proof.MdStream.X86.Update.retR s₀).Disjoint (VG.Proof.MdStream.X86.Update.scR S s₀)
  stk_st : (VG.Proof.MdStream.X86.Update.stkR s₀).Disjoint (VG.Proof.MdStream.X86.Update.stR P s₀)
  stk_scr : (VG.Proof.MdStream.X86.Update.stkR s₀).Disjoint (VG.Proof.MdStream.X86.Update.scR S s₀)
  stk_d : (VG.Proof.MdStream.X86.Update.stkR s₀).Disjoint (VG.Proof.MdStream.X86.Update.dR s₀)
  st_fit : (VG.Proof.MdStream.X86.Update.st s₀).toNat + (P.N + P.B) ≤ 2 ^ 32
  d_fit : (VG.Proof.MdStream.X86.Update.dp s₀).toNat + VG.Proof.MdStream.X86.Update.len s₀ ≤ 2 ^ 32
  scr_fit : (VG.Proof.MdStream.X86.Update.scr s₀).toNat + S ≤ 2 ^ 32
  sp_lo : 20 ≤ (VG.Proof.MdStream.X86.Update.esp₀ s₀).toNat
  sp_fit : (VG.Proof.MdStream.X86.Update.esp₀ s₀).toNat + 28 ≤ 2 ^ 32

section
variable {P : Params} {S : Nat} {H : Md P.B P.N P.L}

theorem pre_of {s₀ : State} (h : (VG.Proof.MdStream.X86.updK H S).pre s₀) : VG.Proof.MdStream.X86.Update.Pre P S s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  have e := VG.Proof.MdStream.X86.stk_eq h16
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by show (below _ _).Disjoint _; rw [e]; exact h10,
    by show (below _ _).Disjoint _; rw [e]; exact h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    h13, h14, h15, h16, h17⟩

theorem cnt_mod (hd : VG.Proof.MdStream.X86.Dims P S) (s₀ : State) : VG.Proof.MdStream.X86.Update.cnt s₀ % P.B = (VG.X86.arg s₀ 1).toNat % P.B :=
  hd.mod_append _ _

theorem R₀.length {s₀ : State} {iv : H.HV} {m : List Byte} (h : VG.Proof.MdStream.X86.Update.R₀ H s₀ iv m) (hd : VG.Proof.MdStream.X86.Dims P S) :
    VG.Proof.MdStream.X86.Update.cnt s₀ % P.B = m.length % P.B := by
  rw [VG.Proof.MdStream.X86.Update.cnt, h.2, BitVec.toNat_ofNat, hd.mod]

theorem len_lt (s₀ : State) : VG.Proof.MdStream.X86.Update.len s₀ < 2 ^ 32 := (VG.X86.arg s₀ 4).isLt

theorem D_length (s₀ : State) : (VG.Proof.MdStream.X86.Update.D s₀).length = VG.Proof.MdStream.X86.Update.len s₀ := by simp [bytesAt]

namespace Pre
variable {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ S) : (VG.Proof.MdStream.X86.Update.scR S s₀).Contains (addr (VG.Proof.MdStream.X86.Update.scr s₀) d) 4 :=
  VG.Proof.MdStream.X86.contains_addr hd (by decide) hp.scr_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : (VG.Proof.MdStream.X86.Update.argR s₀).Contains (addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) d) 4 := by
  have hp_sp_fit := hp.sp_fit
  show (⟨addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) 4, 24⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by decide)

/-- A word of the scratch space, as a region. -/
theorem scr_sub {d : Nat} (hd : d + 4 ≤ S) : Region.Sub ⟨addr (VG.Proof.MdStream.X86.Update.scr s₀) d, 4⟩ (VG.Proof.MdStream.X86.Update.scR S s₀) := by
  rw [addr_eq (by have hp_scr_fit := hp.scr_fit; omega)]
  exact VG.Proof.MdStream.X86.sub_offset hd (by have hp_scr_fit := hp.scr_fit; omega)

/-- An argument word, as a region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : Region.Sub ⟨addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) d, 4⟩ (VG.Proof.MdStream.X86.Update.argR s₀) := by
  have hp_sp_fit := hp.sp_fit
  show Region.Sub _ ⟨addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) 4, 24⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

theorem a_stk : (VG.Proof.MdStream.X86.Update.argR s₀).Disjoint (VG.Proof.MdStream.X86.Update.stkR s₀) := by
  have hp_sp_fit := hp.sp_fit; have hp_sp_lo := hp.sp_lo
  show Region.Disjoint ⟨addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) 4, 24⟩ ⟨(VG.Proof.MdStream.X86.Update.esp₀ s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩
  rw [addr_eq (by omega), Taint.sub_setWidth (by omega)]
  exact Offset.disjoint_below _ (by decide)

theorem ret_stk : (VG.Proof.MdStream.X86.Update.retR s₀).Disjoint (VG.Proof.MdStream.X86.Update.stkR s₀) := by
  have hp_sp_fit := hp.sp_fit; have hp_sp_lo := hp.sp_lo
  show Region.Disjoint ⟨(VG.Proof.MdStream.X86.Update.esp₀ s₀).setWidth 64, 4⟩ ⟨(VG.Proof.MdStream.X86.Update.esp₀ s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩
  rw [Taint.sub_setWidth (by omega)]
  exact Offset.base_disjoint_below _ (by decide)

end Pre

end

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (P : Params) (S : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ VG.Proof.MdStream.X86.Update.len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = VG.Proof.MdStream.X86.Update.st s₀
  esp : s.gpr .esp = VG.Proof.MdStream.X86.Update.esp₀ s₀
  ebp : s.gpr .ebp = VG.Proof.MdStream.X86.Update.dp s₀ + BitVec.ofNat 32 c
  esi : s.gpr .esi = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Update.len s₀ - c)
  frame : Frame [VG.Proof.MdStream.X86.Update.stR P s₀, VG.Proof.MdStream.X86.Update.scR S s₀, VG.Proof.MdStream.X86.Update.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.MdStream.X86.Update.Saved P s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv {P : Params} (S : Nat) (H : Md P.B P.N P.L) (s₀ : State) (c : Nat) (s : State) : Prop
    extends VG.Proof.MdStream.X86.Update.Common P S s₀ c s where
  edi : s.gpr .edi = BitVec.ofNat 32 ((VG.Proof.MdStream.X86.Update.cnt s₀ + c) % P.B)
  repr : ∀ iv m, VG.Proof.MdStream.X86.Update.R₀ H s₀ iv m → H.Repr iv s.mem (VG.Proof.MdStream.X86.Update.stA s₀) (m ++ (VG.Proof.MdStream.X86.Update.D s₀).take c)

/-- `k ≥ 1` whole blocks are ready at `eax` (the buffer, or the data), and
compressing them absorbs the first `c` bytes of data. -/
structure Pending {P : Params} (S : Nat) (H : Md P.B P.N P.L) (s₀ : State) (c k : Nat) (s : State) : Prop
    extends VG.Proof.MdStream.X86.Update.Common P S s₀ c s where
  edi : s.gpr .edi = 0
  ecx : s.gpr .ecx = BitVec.ofNat 32 k
  k_pos : 0 < k
  mod : (VG.Proof.MdStream.X86.Update.cnt s₀ + c) % P.B = 0
  src : (s.gpr .eax = VG.Proof.MdStream.X86.Update.st s₀ + BitVec.ofNat 32 P.N ∧ k = 1) ∨
    ∃ c₀, s.gpr .eax = VG.Proof.MdStream.X86.Update.dp s₀ + BitVec.ofNat 32 c₀ ∧ c₀ + P.B * k ≤ VG.Proof.MdStream.X86.Update.len s₀
  repr : ∀ iv m, VG.Proof.MdStream.X86.Update.R₀ H s₀ iv m → ∀ mem', H.stateAt mem' (VG.Proof.MdStream.X86.Update.stA s₀) =
      H.compressBlocks (H.stateAt s.mem (VG.Proof.MdStream.X86.Update.stA s₀)) s.mem ((s.gpr .eax).setWidth 64) k →
    H.Repr iv mem' (VG.Proof.MdStream.X86.Update.stA s₀) (m ++ (VG.Proof.MdStream.X86.Update.D s₀).take c)

/-- All the data is absorbed, and nothing is pending. -/
def Done {P : Params} (S : Nat) (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  VG.Proof.MdStream.X86.Update.Inv S H s₀ (VG.Proof.MdStream.X86.Update.len s₀) s ∧ s.gpr .ecx = 0

section
variable {P : Params} {S : Nat} {H : Md P.B P.N P.L}

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.MdStream.X86.Update.Common P S s₀ c s)
    (hg : ∀ r ∈ [Reg.ebx, .esp, .ebp, .esi], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.MdStream.X86.Update.Common P S s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  esp := by rw [hg _ (by simp)]; exact h.esp
  ebp := by rw [hg _ (by simp)]; exact h.ebp
  esi := by rw [hg _ (by simp)]; exact h.esi
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.MdStream.X86.Update.Inv S H s₀ c s)
    (hg : ∀ r ∈ [Reg.ebx, .esp, .ebp, .esi, .edi], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.MdStream.X86.Update.Inv S H s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (by simp at hr ⊢; grind)) hm hrd hwr with
    edi := by rw [hg _ (by simp)]; exact h.edi
    repr := by rw [hm]; exact h.repr }

/-- The argument words are never written. -/
theorem Common.arg {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c : Nat} {s : State} (h : VG.Proof.MdStream.X86.Update.Common P S s₀ c s) {d : Nat}
    (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 28) :
    s.mem.readW (addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) d) 32 = s₀.mem.readW (addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) d) 32 := by
  refine h.frame.readW (r := ⟨addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_st.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_scr.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_stk.sub_left (hp.arg_sub h₁ h₂)

/-! ## Prologue and epilogue -/

/-- The memory after saving our caller's registers. -/
def saveMem (P : Params) (s₀ : State) : Mem :=
  (((s₀.mem.writeW (addr (VG.Proof.MdStream.X86.Update.scr s₀) P.so) (s₀.gpr .ebx)).writeW (addr (VG.Proof.MdStream.X86.Update.scr s₀) (P.so + 4)) (s₀.gpr .esi)).writeW
    (addr (VG.Proof.MdStream.X86.Update.scr s₀) (P.so + 8)) (s₀.gpr .edi)).writeW (addr (VG.Proof.MdStream.X86.Update.scr s₀) (P.so + 12)) (s₀.gpr .ebp)

theorem saveMem_frame (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) : Frame [VG.Proof.MdStream.X86.Update.scR S s₀] s₀.mem (VG.Proof.MdStream.X86.Update.saveMem P s₀) := by
  have hd_so := hd.so
  have c : ∀ d, d + 4 ≤ S → (VG.Proof.MdStream.X86.Update.scR S s₀).Contains (addr (VG.Proof.MdStream.X86.Update.scr s₀) d) (32 / 8) := fun d hd => hp.scr_in hd
  simp only [VG.Proof.MdStream.X86.Update.saveMem]
  exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c P.so (by omega_using [hd.so]))).writeW
    (List.mem_singleton_self _) _ (c (P.so + 4) (by omega_using [hd.so]))).writeW (List.mem_singleton_self _) _
    (c (P.so + 8) (by omega_using [hd.so]))).writeW (List.mem_singleton_self _) _ (c (P.so + 12) (by omega_using [hd.so]))

theorem saveMem_saved (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) : VG.Proof.MdStream.X86.Update.Saved P s₀ (VG.Proof.MdStream.X86.Update.saveMem P s₀) := by
  have hs := hp.scr_fit; have hd_so := hd.so
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ S → e + 4 ≤ S → d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (VG.Proof.MdStream.X86.Update.scr s₀) e) v).readW (addr (VG.Proof.MdStream.X86.Update.scr s₀) d) 32 = m.readW (addr (VG.Proof.MdStream.X86.Update.scr s₀) d) 32 :=
    fun m v d e h₁ h₂ h => VG.Proof.MdStream.X86.readW_writeW_addr m v (by omega) (by omega) h
  intro p hp'
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl | rfl | rfl <;> simp only [VG.Proof.MdStream.X86.Update.saveMem]
  · rw [w _ _ P.so (P.so + 12) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]),
      w _ _ P.so (P.so + 8) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]),
      w _ _ P.so (P.so + 4) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]), Mem.readW_writeW_self32]
  · rw [w _ _ (P.so + 4) (P.so + 12) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]),
      w _ _ (P.so + 4) (P.so + 8) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]), Mem.readW_writeW_self32]
  · rw [w _ _ (P.so + 8) (P.so + 12) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

theorem prologue_ok (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) :
    WP isa (.block (([.mov .eax (.mem (at_ .esp 24))] : List Instr) ++ save P .eax ++
      ([.mov .ebx (.mem (at_ .esp 4)), .mov .ebp (.mem (at_ .esp 16)), .mov .esi (.mem (at_ .esp 20)),
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm (BitVec.ofNat 32 (P.B - 1)))] : List Instr))) s₀ (VG.Proof.MdStream.X86.Update.Inv S H s₀ 0) := by
  have hd_so := hd.so; have hd_N := hd.N; have hd_le := hd.le
  have rin : ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => ⟨VG.Proof.MdStream.X86.Update.argR s₀, by simp [hp.rd], hp.arg_in h₁ h₂⟩
  have sin : ∀ d, d + 4 ≤ S → InRegions s₀.wr (addr (VG.Proof.MdStream.X86.Update.scr s₀) d) 4 :=
    fun d hd => ⟨VG.Proof.MdStream.X86.Update.scR S s₀, by simp [hp.wr], hp.scr_in hd⟩
  -- The saves only touch the scratch space, so the arguments stay readable.
  have sepA : ∀ d e, P.so ≤ d → d + 4 ≤ P.so + 16 → 4 ≤ e → e + 4 ≤ 28 →
      Mem.Sep (addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) e) 4 (addr (VG.Proof.MdStream.X86.Update.scr s₀) d) 4 := by
    intro d e h₁ h₂ h₃ h₄ x hx hy
    exact hp.a_scr x (hp.arg_sub h₃ h₄ x (by simp only [Region.Contains]; omega))
      (hp.scr_sub (d := d) (by omega) x (by simp only [Region.Contains]; omega))
  have argSave : ∀ e, 4 ≤ e → e + 4 ≤ 28 →
      (VG.Proof.MdStream.X86.Update.saveMem P s₀).readW (addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) e) 32 = s₀.mem.readW (addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) e) 32 := by
    intro e h₁ h₂
    simp only [VG.Proof.MdStream.X86.Update.saveMem]
    rw [Mem.readW_writeW_sep (sepA (P.so + 12) e (by omega_using [hd.so]) (by omega_using [hd.so]) h₁ h₂) (by decide),
      Mem.readW_writeW_sep (sepA (P.so + 8) e (by omega_using [hd.so]) (by omega_using [hd.so]) h₁ h₂) (by decide),
      Mem.readW_writeW_sep (sepA (P.so + 4) e (by omega_using [hd.so]) (by omega_using [hd.so]) h₁ h₂) (by decide),
      Mem.readW_writeW_sep (sepA P.so e (by omega_using [hd.so]) (by omega_using [hd.so]) h₁ h₂) (by decide)]
  simp only [List.cons_append, VG.Proof.MdStream.X86.save_eq, List.nil_append]
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) 24) (VG.Proof.MdStream.X86.ea_at _ _ _) (rin 24 (by decide) (by decide)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = VG.Proof.MdStream.X86.Update.scr s₀ := u₁.gpr
  refine VG.Proof.MdStream.X86.wp_store (a := addr (VG.Proof.MdStream.X86.Update.scr s₀) P.so) (by rw [VG.Proof.MdStream.X86.ea_at, e₁]) (by rw [u₁.wr]; exact sin P.so (by omega_using [hd.so]))
    fun s₂ u₂ => ?_
  refine VG.Proof.MdStream.X86.wp_store (a := addr (VG.Proof.MdStream.X86.Update.scr s₀) (P.so + 4)) (by rw [VG.Proof.MdStream.X86.ea_at, u₂.gpr, e₁])
    (by rw [u₂.wr, u₁.wr]; exact sin (P.so + 4) (by omega_using [hd.so])) fun s₃ u₃ => ?_
  refine VG.Proof.MdStream.X86.wp_store (a := addr (VG.Proof.MdStream.X86.Update.scr s₀) (P.so + 8)) (by rw [VG.Proof.MdStream.X86.ea_at, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact sin (P.so + 8) (by omega_using [hd.so])) fun s₄ u₄ => ?_
  refine VG.Proof.MdStream.X86.wp_store (a := addr (VG.Proof.MdStream.X86.Update.scr s₀) (P.so + 12)) (by rw [VG.Proof.MdStream.X86.ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact sin (P.so + 12) (by omega_using [hd.so])) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have m₅ : s₅.mem = VG.Proof.MdStream.X86.Update.saveMem P s₀ := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem,
      u₁.other .ebx (by decide), u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
    rfl
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = VG.Proof.MdStream.X86.Update.esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  have rd' : ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions (s₅.rd ++ s₅.wr) (addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => by rw [rd₅, wr₅]; exact rin d h₁ h₂
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) 4) (by rw [VG.Proof.MdStream.X86.ea_at, sp₅]) (rd' 4 (by decide) (by decide)) fun s₆ u₆ => ?_
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) 16) (by rw [VG.Proof.MdStream.X86.ea_at, u₆.other _ (by decide), sp₅])
    (by rw [u₆.rd, u₆.wr]; exact rd' 16 (by decide) (by decide)) fun s₇ u₇ => ?_
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) 20) (by rw [VG.Proof.MdStream.X86.ea_at, u₇.other _ (by decide), u₆.other _ (by decide), sp₅])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr]; exact rd' 20 (by decide) (by decide)) fun s₈ u₈ => ?_
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) 8)
    (by rw [VG.Proof.MdStream.X86.ea_at, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), sp₅])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr]; exact rd' 8 (by decide) (by decide)) fun s₉ u₉ => ?_
  refine VG.Proof.MdStream.X86.wp_andi fun s₁₀ u₁₀ => WP.block_nil ?_
  have g : ∀ r, r ≠ .edi → r ≠ .esi → r ≠ .ebp → r ≠ .ebx → s₁₀.gpr r = s₅.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₁₀.other r h1, u₉.other r h1, u₈.other r h2, u₇.other r h3, u₆.other r h4]
  have m₁₀ : s₁₀.mem = VG.Proof.MdStream.X86.Update.saveMem P s₀ := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]
  have sp₁₀ : s₁₀.gpr .esp = VG.Proof.MdStream.X86.Update.esp₀ s₀ := by rw [g _ (by decide) (by decide) (by decide) (by decide), sp₅]
  have ld : ∀ e, 4 ≤ e → e + 4 ≤ 28 → s₅.mem.readW (addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) e) 32 = s₀.mem.readW (addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => by rw [m₅]; exact argSave e h₁ h₂
  have ebx₁₀ : s₁₀.gpr .ebx = VG.Proof.MdStream.X86.Update.st s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      ld 4 (by decide) (by decide)]; rfl
  have ebp₁₀ : s₁₀.gpr .ebp = VG.Proof.MdStream.X86.Update.dp s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.mem,
      ld 16 (by decide) (by decide)]; rfl
  have esi₁₀ : s₁₀.gpr .esi = VG.X86.arg s₀ 4 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.mem, u₆.mem, ld 20 (by decide) (by decide)]; rfl
  have edi₁₀ : s₁₀.gpr .edi = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Update.cnt s₀ % P.B) := by
    rw [u₁₀.gpr, u₉.gpr, u₈.mem, u₇.mem, u₆.mem, ld 8 (by decide) (by decide), hd.and, VG.Proof.MdStream.X86.Update.cnt_mod hd]; rfl
  have rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  refine ⟨⟨Nat.zero_le _, rd₁₀, wr₁₀, ebx₁₀, sp₁₀, by rw [ebp₁₀]; simp, ?_,
    by rw [m₁₀]; exact (VG.Proof.MdStream.X86.Update.saveMem_frame hd hp).mono (by simp), by rw [m₁₀]; exact VG.Proof.MdStream.X86.Update.saveMem_saved hd hp⟩,
    by rw [edi₁₀, Nat.add_zero], fun iv m hm => ?_⟩
  · rw [esi₁₀, Nat.sub_zero, VG.Proof.MdStream.X86.Update.len, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [List.take_zero, List.append_nil, m₁₀]
    exact H.repr_congr hd.pos (fun i hi => VG.Proof.MdStream.X86.frame_bytes (VG.Proof.MdStream.X86.Update.saveMem_frame hd hp) (R := VG.Proof.MdStream.X86.Update.stR P s₀)
      (by simpa using hp.st_scr) (by simp; omega) hi) hm.1

theorem epilogue_ok (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {s : State} (hI : VG.Proof.MdStream.X86.Update.Inv S H s₀ (VG.Proof.MdStream.X86.Update.len s₀) s) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 24)) :: restore P .eax)) s fun s' =>
      abiPreserved s₀ s' ∧ (VG.Proof.MdStream.X86.updK H S).post s₀ s' := by
  have hd_so := hd.so
  have rin : ∀ d, d + 4 ≤ S → InRegions (s.rd ++ s.wr) (addr (VG.Proof.MdStream.X86.Update.scr s₀) d) 4 :=
    fun d hd => ⟨VG.Proof.MdStream.X86.Update.scR S s₀, by simp [hI.rd, hI.wr, hp.wr], hp.scr_in hd⟩
  have ain : InRegions (s.rd ++ s.wr) (addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) 24) 4 :=
    ⟨VG.Proof.MdStream.X86.Update.argR s₀, by simp [hI.rd, hp.rd], hp.arg_in (by decide) (by decide)⟩
  rw [VG.Proof.MdStream.X86.restore_eq]
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) 24) (by rw [VG.Proof.MdStream.X86.ea_at, hI.esp]) ain fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = VG.Proof.MdStream.X86.Update.scr s₀ := by rw [u₁.gpr, hI.arg hp (by decide) (by decide)]; rfl
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Update.scr s₀) P.so) (by rw [VG.Proof.MdStream.X86.ea_at, e₁]) (by rw [u₁.rd, u₁.wr]; exact rin P.so (by omega_using [hd.so]))
    fun s₂ u₂ => ?_
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Update.scr s₀) (P.so + 4)) (by rw [VG.Proof.MdStream.X86.ea_at, u₂.other _ (by decide), e₁])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin (P.so + 4) (by omega_using [hd.so])) fun s₃ u₃ => ?_
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Update.scr s₀) (P.so + 8)) (by rw [VG.Proof.MdStream.X86.ea_at, u₃.other _ (by decide), u₂.other _ (by decide), e₁])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin (P.so + 8) (by omega_using [hd.so])) fun s₄ u₄ => ?_
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Update.scr s₀) (P.so + 12))
    (by rw [VG.Proof.MdStream.X86.ea_at, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), e₁])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin (P.so + 12) (by omega_using [hd.so]))
    fun s₅ u₅ => WP.block_nil ?_
  have hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun iv m hm hc => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]
      exact hI.saved (.ebx, P.so) (by simp [saved])
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]
      exact hI.saved (.esi, P.so + 4) (by simp [saved])
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
      exact hI.saved (.edi, P.so + 8) (by simp [saved])
    · rw [u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
      exact hI.saved (.ebp, P.so + 12) (by simp [saved])
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), hI.esp]
  · rw [hm₅]
    refine hI.frame.readW (r := VG.Proof.MdStream.X86.Update.retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.ret_st, hp.ret_scr, hp.ret_stk]
  · have := hI.repr iv m ⟨hm, hc⟩
    rw [List.take_of_length_le (by rw [VG.Proof.MdStream.X86.Update.D_length])] at this
    show H.Repr iv s₅.mem (VG.Proof.MdStream.X86.Update.stA s₀) (m ++ VG.Proof.MdStream.X86.Update.D s₀)
    rw [hm₅]; exact this

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < VG.Proof.MdStream.X86.Update.len s₀) :
    (VG.Proof.MdStream.X86.Update.D s₀).getD i 0 = s₀.mem (VG.Proof.MdStream.X86.Update.dA s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c : Nat} {s : State} (h : VG.Proof.MdStream.X86.Update.Common P S s₀ c s) {i : Nat}
    (hi : i < VG.Proof.MdStream.X86.Update.len s₀) : s.mem (VG.Proof.MdStream.X86.Update.dA s₀ + BitVec.ofNat 64 i) = (VG.Proof.MdStream.X86.Update.D s₀).getD i 0 := by
  rw [VG.Proof.MdStream.X86.Update.D_getD s₀ hi]
  exact VG.Proof.MdStream.X86.frame_bytes h.frame (R := VG.Proof.MdStream.X86.Update.dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
    (by simp only; have := VG.Proof.MdStream.X86.Update.len_lt s₀; omega) hi

theorem length_mid (hd : VG.Proof.MdStream.X86.Dims P S) (s₀ : State) {iv : H.HV} {m : List Byte} (hm : VG.Proof.MdStream.X86.Update.R₀ H s₀ iv m) {c : Nat}
    (hc : c ≤ VG.Proof.MdStream.X86.Update.len s₀) : (m ++ (VG.Proof.MdStream.X86.Update.D s₀).take c).length % P.B = (VG.Proof.MdStream.X86.Update.cnt s₀ + c) % P.B := by
  simp only [List.length_append, List.length_take, VG.Proof.MdStream.X86.Update.D_length, Nat.min_eq_left hc]
  rw [Nat.add_mod, ← hm.length hd, ← Nat.add_mod]

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (VG.Proof.MdStream.X86.Update.D s₀).take c ++ ((VG.Proof.MdStream.X86.Update.D s₀).drop c).take t = m ++ (VG.Proof.MdStream.X86.Update.D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-- Every whole block left, straight from the data. -/
theorem direct_ok (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.X86.Update.Inv S H s₀ c s)
    (hr : (VG.Proof.MdStream.X86.Update.cnt s₀ + c) % P.B = 0) (hl : P.B ≤ VG.Proof.MdStream.X86.Update.len s₀ - c) :
    WP isa (.block (direct P)) s (VG.Proof.MdStream.X86.Update.Pending S H s₀ (c + P.B * ((VG.Proof.MdStream.X86.Update.len s₀ - c) / P.B)) ((VG.Proof.MdStream.X86.Update.len s₀ - c) / P.B)) := by
  have hdf := hp.d_fit; have hc := hI.c_le; have hlen := VG.Proof.MdStream.X86.Update.len_lt s₀; have hB := hd.pos
  have hq1 : 1 ≤ (VG.Proof.MdStream.X86.Update.len s₀ - c) / P.B := (Nat.le_div_iff_mul_le hB).mpr (by omega)
  have hdm := Nat.div_add_mod (VG.Proof.MdStream.X86.Update.len s₀ - c) P.B
  have hml := Nat.mod_lt (VG.Proof.MdStream.X86.Update.len s₀ - c) hB
  generalize hq : (VG.Proof.MdStream.X86.Update.len s₀ - c) / P.B = q at hq1 hdm
  have hq2 : (VG.Proof.MdStream.X86.Update.len s₀ - c) - (VG.Proof.MdStream.X86.Update.len s₀ - c) % P.B = P.B * q := by omega_using [hdm]
  unfold direct
  refine VG.Proof.MdStream.X86.wp_mov fun s₁ u₁ => VG.Proof.MdStream.X86.wp_mov fun s₂ u₂ => VG.Proof.MdStream.X86.wp_andi fun s₃ u₃ => VG.Proof.MdStream.X86.wp_mov fun s₄ u₄ =>
    VG.Proof.MdStream.X86.wp_sub fun s₅ u₅ _ => VG.Proof.MdStream.X86.wp_add fun s₆ u₆ => VG.Proof.MdStream.X86.wp_mov fun s₇ u₇ => VG.Proof.MdStream.X86.wp_mov fun s₈ u₈ =>
    VG.Proof.MdStream.X86.wp_shr hd.lg fun s₉ u₉ => WP.block_nil ?_
  have g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .ebp → r ≠ .esi → s₉.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₉.other r h2, u₈.other r h2, u₇.other r h5, u₆.other r h4, u₅.other r h3, u₄.other r h3,
        u₃.other r h2, u₂.other r h2, u₁.other r h1]
  have hm : s₉.mem = s.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have heax : s₉.gpr .eax = VG.Proof.MdStream.X86.Update.dp s₀ + BitVec.ofNat 32 c := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      hI.ebp]
  have h3 : s₃.gpr .ecx = BitVec.ofNat 32 ((VG.Proof.MdStream.X86.Update.len s₀ - c) % P.B) := by
    rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), hI.esi, hd.and, VG.Proof.MdStream.X86.toNat_ofNat_lt (by omega_using [hlen])]
  have h5 : s₅.gpr .edx = BitVec.ofNat 32 (P.B * q) := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), h3, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.esi, VG.Proof.MdStream.X86.sub_ofNat (by omega_using [hml, hl]), hq2]
  have h6 : s₆.gpr .edx = BitVec.ofNat 32 (P.B * q) := by rw [u₆.other _ (by decide), h5]
  refine ⟨⟨by omega_using [hdm, hc], ?_, ?_,
      by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.ebx],
      by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.esp], ?_, ?_,
      by rw [hm]; exact hI.frame, by rw [hm]; exact hI.saved⟩,
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.edi, hr]; rfl,
    ?_, hq1, by rw [← Nat.add_assoc, Nat.add_mul_mod_self_left]; exact hr, .inr ⟨c, heax, by omega⟩,
    fun iv m hm₀ mem' hs => ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, h5,
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.ebp, VG.Proof.MdStream.X86.ofNat_add_add]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), h3]
    congr 1; omega
  · rw [u₉.gpr, u₈.gpr, u₇.other _ (by decide), h6, hd.shr (by omega_using [hdm, hlen]), Nat.mul_div_cancel_left q hB]
  · have hmod := VG.Proof.MdStream.X86.Update.length_mid hd s₀ hm₀ (c := c) (by omega)
    rw [← VG.Proof.MdStream.X86.Update.take_add_data]
    refine H.repr_append_blocks (n := q) hB (hI.repr iv m hm₀) (by rw [hmod, hr])
      (by rw [List.length_take, List.length_drop, VG.Proof.MdStream.X86.Update.D_length]; omega_using [hdm]) ?_
    rw [hs, hm, heax, show (VG.Proof.MdStream.X86.Update.dp s₀ + BitVec.ofNat 32 c).setWidth 64 = addr (VG.Proof.MdStream.X86.Update.dp s₀) c from rfl,
      addr_eq (by omega_using [hB, hdf, hl])]
    apply H.compressBlocks_eq
    intro j hj
    rw [show VG.Proof.MdStream.X86.Update.dA s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 j = VG.Proof.MdStream.X86.Update.dA s₀ + BitVec.ofNat 64 (c + j) by
      simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc], hI.data hp (by omega_using [hj, hdm])]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hj]

/-! ## Compressing -/

theorem Pending.k_lt (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} {c k : Nat} {s : State} (h : VG.Proof.MdStream.X86.Update.Pending S H s₀ c k s) :
    k < 2 ^ 32 := by
  have := VG.Proof.MdStream.X86.Update.len_lt s₀; have := Nat.le_mul_of_pos_left k hd.pos
  rcases h.src with ⟨_, rfl⟩ | ⟨c₀, _, hc₀⟩ <;> omega

/-- The blocks to compress. -/
theorem Pending.blk (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c k : Nat} {s : State} (h : VG.Proof.MdStream.X86.Update.Pending S H s₀ c k s) :
    (s.gpr .eax).toNat + P.B * k ≤ 2 ^ 32 ∧
      (((s.gpr .eax).setWidth 64 = VG.Proof.MdStream.X86.Update.stA s₀ + BitVec.ofNat 64 P.N ∧ k = 1) ∨
        ∃ c₀, (s.gpr .eax).setWidth 64 = VG.Proof.MdStream.X86.Update.dA s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + P.B * k ≤ VG.Proof.MdStream.X86.Update.len s₀) := by
  have hst := hp.st_fit; have hdf := hp.d_fit; have h_k_pos := h.k_pos; have hd_pos := hd.pos
  have := Nat.le_mul_of_pos_left k hd.pos
  rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
  · refine ⟨by rw [h', BitVec.toNat_add, VG.Proof.MdStream.X86.toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega,
      .inl ⟨?_, rfl⟩⟩
    rw [h']; exact addr_eq (by omega)
  · refine ⟨by rw [h', BitVec.toNat_add, VG.Proof.MdStream.X86.toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega,
      .inr ⟨c₀, ?_, hc₀⟩⟩
    rw [h']; exact addr_eq (by omega)

/-- The blocks lie in the state or in the data. -/
theorem Pending.blk_sub (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c k : Nat} {s : State} (h : VG.Proof.MdStream.X86.Update.Pending S H s₀ c k s) :
    Region.Sub ⟨(s.gpr .eax).setWidth 64, P.B * k⟩ (VG.Proof.MdStream.X86.Update.stR P s₀) ∨
      Region.Sub ⟨(s.gpr .eax).setWidth 64, P.B * k⟩ (VG.Proof.MdStream.X86.Update.dR s₀) := by
  rcases (h.blk hd hp).2 with ⟨he, rfl⟩ | ⟨c₀, he, hc₀⟩
  · exact .inl (by rw [he]; exact VG.Proof.MdStream.X86.sub_offset (by omega) (by have hp_st_fit := hp.st_fit; omega))
  · exact .inr (by rw [he]; exact VG.Proof.MdStream.X86.sub_offset hc₀ (by have := VG.Proof.MdStream.X86.Update.len_lt s₀; omega))

/-- The call of the compression function, once `edx` holds `scratch`. -/
theorem Pending.compress_ok (hd : VG.Proof.MdStream.X86.Dims P S) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86.CalleeOk H code)
    {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c k : Nat} {s s₁ : State} (h : VG.Proof.MdStream.X86.Update.Pending S H s₀ c k s)
    (u : VG.Proof.MdStream.X86.Upd s s₁ .edx (VG.Proof.MdStream.X86.Update.scr s₀)) : WP isa (compressN name code .ebx .edx) s₁ (VG.Proof.MdStream.X86.Update.Inv S H s₀ c) := by
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hd_so := hd.so; have hd_N := hd.N
  obtain ⟨hbf, hb⟩ := h.blk hd hp
  have hbs := h.blk_sub hd hp
  have eN : Region.Sub ⟨VG.Proof.MdStream.X86.Update.stA s₀, P.N⟩ (VG.Proof.MdStream.X86.Update.stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.MdStream.X86.Update.scA s₀, P.so⟩ (VG.Proof.MdStream.X86.Update.scR S s₀) := Region.sub_prefix (by omega_using [hd.so])
  have hk : (s₁.gpr .ecx).toNat = k := by rw [u.other _ (by decide), h.ecx, VG.Proof.MdStream.X86.toNat_ofNat_lt (h.k_lt hd)]
  unfold compressN compressWith
  refine WP.seq (WP.block_nil ?_)
  refine VG.Proof.MdStream.X86.compressFrame_ok hf (st := VG.Proof.MdStream.X86.Update.st s₀) (scr := VG.Proof.MdStream.X86.Update.scr s₀) (blk := s.gpr .eax) (E := VG.Proof.MdStream.X86.Update.esp₀ s₀)
    (by decide) (by decide) (by rw [u.other _ (by decide), h.esp])
    (by rw [u.other _ (by decide), h.ebx]) u.gpr (u.other _ (by decide)) hk hp.sp_lo (by omega) hbf (by omega)
    ((hp.st_scr.sub_left eN).sub_right eso) ?_ ?_ (hp.stk_st.sub_right eN) (hp.stk_scr.sub_right eso)
    ?_ ?_ ?_ ?_
  · rcases hb with ⟨he, rfl⟩ | ⟨c₀, he, hc₀⟩
    · rw [he]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hp.d_st.sub_left (by rw [he]; exact VG.Proof.MdStream.X86.sub_offset hc₀ (by have := VG.Proof.MdStream.X86.Update.len_lt s₀; omega_using [this, hc₀]))).sub_right eN
  · rcases hbs with hsub | hsub
    · exact (hp.st_scr.sub_left hsub).sub_right eso
    · exact (hp.d_scr.sub_left hsub).sub_right eso
  · rcases hbs with hsub | hsub
    · exact hp.stk_st.sub_right hsub
    · exact hp.stk_d.sub_right hsub
  · rw [u.rd, u.wr, h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    rcases hb with ⟨he, rfl⟩ | ⟨c₀, he, hc₀⟩
    · exact ⟨VG.Proof.MdStream.X86.Update.stR P s₀, by simp, P.N, he, by simp⟩
    · exact ⟨VG.Proof.MdStream.X86.Update.dR s₀, by simp, c₀, he, hc₀⟩
  · rw [u.wr, h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.MdStream.X86.Update.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.X86.Update.scR S s₀, by simp, 0, by simp, by simp; omega_using [hd.so]⟩
  · intro s' hrd hwr hcs hf hstate
    have cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := fun r hr => by
      rw [hcs r hr, u.other r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    rw [u.mem] at hf hstate
    refine ⟨⟨h.c_le, by rw [hrd, u.rd, h.rd], by rw [hwr, u.wr, h.wr], by rw [cs _ (by decide)]; exact h.ebx,
      by rw [cs _ (by decide)]; exact h.esp, by rw [cs _ (by decide)]; exact h.ebp,
      by rw [cs _ (by decide)]; exact h.esi, h.frame.trans (hf.sub ?_), fun p hp' => ?_⟩,
      by rw [cs _ (by decide), h.edi, h.mod]; rfl, fun iv m hm => h.repr iv m hm _ hstate⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.MdStream.X86.Update.stR P s₀, by simp, eN⟩
      · exact ⟨VG.Proof.MdStream.X86.Update.scR S s₀, by simp, eso⟩
      · exact ⟨VG.Proof.MdStream.X86.Update.stkR s₀, by simp, fun _ h => h⟩
    · have hd' := VG.Proof.MdStream.X86.saved_offset hp'
      rw [hf.readW (r := ⟨addr (VG.Proof.MdStream.X86.Update.scr s₀) p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      · exact h.saved p hp'
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (hp.st_scr.symm.sub_left (hp.scr_sub (by omega_using [hd', hd_so]))).sub_right eN
        · rw [addr_eq (by omega_using [hd', hd_so, hsc])]; exact Offset.disjoint_base _ (by omega) (by omega_using [hd', hd_so, hsc])
        · exact hp.stk_scr.symm.sub_left (hp.scr_sub (by omega))

theorem Pending.congr {s₀ : State} {c k : Nat} {s s' : State} (h : VG.Proof.MdStream.X86.Update.Pending S H s₀ c k s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.MdStream.X86.Update.Pending S H s₀ c k s' :=
  { h.toCommon.of_gpr (fun r _ => by rw [hg]) hm hrd hwr with
    edi := by rw [hg]; exact h.edi
    ecx := by rw [hg]; exact h.ecx
    k_pos := h.k_pos
    mod := h.mod
    src := by rw [hg]; exact h.src
    repr := by rw [hm, hg]; exact h.repr }

end

/-- The loop's postcondition for one iteration from `c` bytes. -/
def Step {P : Params} (S : Nat) (H : Md P.B P.N P.L) (s₀ : State) (c : Nat) (s : State) : Prop :=
  (eval .ne s = some false ∧ VG.Proof.MdStream.X86.Update.Inv S H s₀ (VG.Proof.MdStream.X86.Update.len s₀) s) ∨ (eval .ne s = some true ∧ ∃ c', c < c' ∧ VG.Proof.MdStream.X86.Update.Inv S H s₀ c' s)

section
variable {P : Params} {S : Nat} {H : Md P.B P.N P.L}

/-- The second half of the loop body: compress if a block is ready, and loop
back if so. -/
theorem tail_ok (hd : VG.Proof.MdStream.X86.Dims P S) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c : Nat} {s : State}
    (h : (∃ c' k, c < c' ∧ VG.Proof.MdStream.X86.Update.Pending S H s₀ c' k s) ∨ VG.Proof.MdStream.X86.Update.Done S H s₀ s) :
    WP isa (.seq (.block [.alu .test .ecx (.reg .ecx)])
      (.ite .ne (.seq (.block [.mov .edx (.mem (at_ .esp 24))])
          (.seq (compressN name code .ebx .edx) (.block [.mov .ecx (.imm 1), .alu .test .ecx (.reg .ecx)])))
        (.block []))) s (VG.Proof.MdStream.X86.Update.Step S H s₀ c) := by
  rcases h with ⟨c', k, hc, hP⟩ | ⟨hI, hecx⟩
  · refine WP.seq (VG.Proof.MdStream.X86.wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
    have hP₂ : VG.Proof.MdStream.X86.Update.Pending S H s₀ c' k s₂ := hP.congr f₂.gpr f₂.mem f₂.rd f₂.wr
    have hz : s₂.zf = some false := by
      rw [z₂, hP.ecx, BitVec.and_self, VG.Proof.MdStream.X86.ofNat_beq_zero (hP.k_lt hd), decide_eq_false (Nat.pos_iff_ne_zero.mp hP.k_pos)]
    refine WP.ite true (by show s₂.zf.map (!·) = _; rw [hz]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine WP.seq (VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Update.esp₀ s₀) 24) (by rw [VG.Proof.MdStream.X86.ea_at, hP₂.esp])
      ⟨VG.Proof.MdStream.X86.Update.argR s₀, by simp [hP₂.rd, hp.rd], hp.arg_in (by decide) (by decide)⟩ fun s₃ u₃ => WP.block_nil ?_)
    have u₃' : VG.Proof.MdStream.X86.Upd s₂ s₃ .edx (VG.Proof.MdStream.X86.Update.scr s₀) :=
      ⟨by rw [u₃.gpr, hP₂.toCommon.arg hp (by decide) (by decide)]; rfl, u₃.other, u₃.mem, u₃.rd, u₃.wr⟩
    refine WP.seq (WP.mono (hP₂.compress_ok hd hf hp u₃') fun s₄ hI₄ => ?_)
    refine VG.Proof.MdStream.X86.wp_movi fun s₅ u₅ => VG.Proof.MdStream.X86.wp_test fun s₆ f₆ z₆ => WP.block_nil ?_
    have hz₆ : s₆.zf = some false := by rw [z₆, u₅.gpr]; rfl
    refine .inr ⟨by rw [VG.Proof.MdStream.X86.eval_ne, hz₆]; rfl, c', hc, hI₄.of_gpr (fun r hr => ?_) (by rw [f₆.mem, u₅.mem])
      (by rw [f₆.rd, u₅.rd]) (by rw [f₆.wr, u₅.wr])⟩
    rw [f₆.gpr, u₅.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  · refine WP.seq (VG.Proof.MdStream.X86.wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
    have hz : s₂.zf = some true := by rw [z₂, hecx]; rfl
    refine WP.ite false (by show s₂.zf.map (!·) = _; rw [hz]; rfl) (fun h => by cases h) (fun _ => WP.block_nil ?_)
    exact .inl ⟨by rw [VG.Proof.MdStream.X86.eval_ne, hz]; rfl, hI.of_gpr (fun r _ => by rw [f₂.gpr]) f₂.mem f₂.rd f₂.wr⟩

end

/-! ## Buffering data -/

section
variable (P : Params) (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (VG.Proof.MdStream.X86.Update.cnt s₀ + c) % P.B
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (P.B - VG.Proof.MdStream.X86.Update.rr P s₀ c) (VG.Proof.MdStream.X86.Update.len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := VG.Proof.MdStream.X86.Update.stA s₀ + BitVec.ofNat 64 (P.N + VG.Proof.MdStream.X86.Update.rr P s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((VG.Proof.MdStream.X86.Update.D s₀).drop c).take (VG.Proof.MdStream.X86.Update.tt P s₀ c)
end

theorem rr_lt {P : Params} {S : Nat} (hd : VG.Proof.MdStream.X86.Dims P S) (s₀ : State) (c : Nat) : VG.Proof.MdStream.X86.Update.rr P s₀ c < P.B :=
  Nat.mod_lt _ hd.pos
theorem rr_eq (P : Params) (s₀ : State) (c : Nat) : VG.Proof.MdStream.X86.Update.rr P s₀ c = (VG.Proof.MdStream.X86.Update.cnt s₀ + c) % P.B := rfl
theorem tt_eq (P : Params) (s₀ : State) (c : Nat) : VG.Proof.MdStream.X86.Update.tt P s₀ c = min (P.B - VG.Proof.MdStream.X86.Update.rr P s₀ c) (VG.Proof.MdStream.X86.Update.len s₀ - c) := rfl
theorem tt_le (P : Params) (s₀ : State) (c : Nat) : VG.Proof.MdStream.X86.Update.tt P s₀ c ≤ VG.Proof.MdStream.X86.Update.len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (P : Params) (s₀ : State) (c : Nat) : VG.Proof.MdStream.X86.Update.tt P s₀ c ≤ P.B - VG.Proof.MdStream.X86.Update.rr P s₀ c := Nat.min_le_left _ _

theorem xs_length (P : Params) (s₀ : State) (c : Nat) : (VG.Proof.MdStream.X86.Update.xs P s₀ c).length = VG.Proof.MdStream.X86.Update.tt P s₀ c := by
  have := VG.Proof.MdStream.X86.Update.tt_le P s₀ c
  simp only [VG.Proof.MdStream.X86.Update.xs, List.length_take, List.length_drop, VG.Proof.MdStream.X86.Update.D_length]; omega

/-- The state while copying: `j` bytes copied, into memory `mI` otherwise unchanged. -/
structure Copy (P : Params) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ VG.Proof.MdStream.X86.Update.tt P s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = VG.Proof.MdStream.X86.Update.st s₀
  esp : s.gpr .esp = VG.Proof.MdStream.X86.Update.esp₀ s₀
  ebp : s.gpr .ebp = VG.Proof.MdStream.X86.Update.dp s₀ + BitVec.ofNat 32 (c + j)
  esi : s.gpr .esi = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Update.len s₀ - c - VG.Proof.MdStream.X86.Update.tt P s₀ c)
  edi : s.gpr .edi = VG.Proof.MdStream.X86.Update.st s₀ + BitVec.ofNat 32 (VG.Proof.MdStream.X86.Update.rr P s₀ c + j)
  eax : s.gpr .eax = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Update.tt P s₀ c - j)
  mem : s.mem = VG.WriteBytes.writeBytes mI (VG.Proof.MdStream.X86.Update.q P s₀ c) ((VG.Proof.MdStream.X86.Update.xs P s₀ c).take j)

section
variable {P : Params} {S : Nat} {H : Md P.B P.N P.L}

theorem write_frame (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) (c : Nat) (mI : Mem) (j : Nat)
    (hj : j ≤ VG.Proof.MdStream.X86.Update.tt P s₀ c) : Frame [VG.Proof.MdStream.X86.Update.stR P s₀] mI (VG.WriteBytes.writeBytes mI (VG.Proof.MdStream.X86.Update.q P s₀ c) ((VG.Proof.MdStream.X86.Update.xs P s₀ c).take j)) := by
  have := VG.Proof.MdStream.X86.Update.tt_le' P s₀ c; have := VG.Proof.MdStream.X86.Update.rr_lt hd s₀ c; have hp_st_fit := hp.st_fit; have hd_N := hd.N
  refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
  simp only [VG.Proof.MdStream.X86.Update.q]
  exact VG.Proof.MdStream.X86.contains_offset (by simp only [List.length_take]; omega) (by omega_using [hp_st_fit, this])

theorem copy_step (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.X86.Update.Inv S H s₀ c sI)
    {j : Nat} (hj : j < VG.Proof.MdStream.X86.Update.tt P s₀ c) {s : State} (h : VG.Proof.MdStream.X86.Update.Copy P s₀ c sI.mem j s) :
    WP isa (.block [.movzx8 .ecx (at_ .ebp 0), .store8 (at_ .edi P.N) .cl,
      .alu .add .ebp (.imm 1), .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) s fun s' =>
      VG.Proof.MdStream.X86.Update.Copy P s₀ c sI.mem (j + 1) s' ∧ s'.zf = some (decide (VG.Proof.MdStream.X86.Update.tt P s₀ c - (j + 1) = 0)) := by
  have hdf := hp.d_fit; have hst := hp.st_fit; have hd_N := hd.N
  have hc := hI.c_le
  have hr := VG.Proof.MdStream.X86.Update.rr_lt hd s₀ c
  have ht := VG.Proof.MdStream.X86.Update.tt_le P s₀ c; have ht' := VG.Proof.MdStream.X86.Update.tt_le' P s₀ c
  -- The byte read.
  have ea₁ : s.ea (at_ .ebp 0) = VG.Proof.MdStream.X86.Update.dA s₀ + BitVec.ofNat 64 (c + j) := by
    rw [VG.Proof.MdStream.X86.ea_at, h.ebp, VG.Proof.MdStream.X86.addr_add_ofNat (by omega), Nat.add_zero]
  have hin : InRegions (s.rd ++ s.wr) (VG.Proof.MdStream.X86.Update.dA s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨VG.Proof.MdStream.X86.Update.dR s₀, by simp [h.rd, hp.rd], VG.Proof.MdStream.X86.contains_offset (by omega_using [ht, hj]) (by omega_using [ht, hdf, hj])⟩
  have hbyte : s.mem (VG.Proof.MdStream.X86.Update.dA s₀ + BitVec.ofNat 64 (c + j)) = (VG.Proof.MdStream.X86.Update.D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega_using [ht, hj])]
    exact VG.Proof.MdStream.X86.frame_bytes (VG.Proof.MdStream.X86.Update.write_frame hd hp c sI.mem j h.j_le) (R := VG.Proof.MdStream.X86.Update.dR s₀) (by simpa using hp.d_st)
      (by show VG.Proof.MdStream.X86.Update.len s₀ ≤ 2 ^ 64; omega) (by show c + j < VG.Proof.MdStream.X86.Update.len s₀; omega)
  -- The byte written.
  have ea₂ : ∀ t : State, t.gpr .edi = VG.Proof.MdStream.X86.Update.st s₀ + BitVec.ofNat 32 (VG.Proof.MdStream.X86.Update.rr P s₀ c + j) →
      t.ea (at_ .edi P.N) = VG.Proof.MdStream.X86.Update.q P s₀ c + BitVec.ofNat 64 j := by
    intro t ht
    rw [VG.Proof.MdStream.X86.ea_at, ht, VG.Proof.MdStream.X86.addr_add_ofNat (by omega), VG.Proof.MdStream.X86.Update.q, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega_using []
  have hout : InRegions s.wr (VG.Proof.MdStream.X86.Update.q P s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨VG.Proof.MdStream.X86.Update.stR P s₀, by simp [h.wr, hp.wr], by
      simp only [VG.Proof.MdStream.X86.Update.q]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact VG.Proof.MdStream.X86.contains_offset (by omega_using [ht', hj]) (by omega)⟩
  have hxs := VG.Proof.MdStream.X86.Update.xs_length P s₀ c
  refine VG.Proof.MdStream.X86.wp_movzx8 (d := .ecx) ea₁ hin fun s₁ u₁ => ?_
  refine VG.Proof.MdStream.X86.wp_store8 (r := .cl) (a := VG.Proof.MdStream.X86.Update.q P s₀ c + BitVec.ofNat 64 j)
    (ea₂ s₁ (by rw [u₁.other _ (by decide), h.edi])) (by rw [u₁.wr]; exact hout) fun s₂ u₂ => ?_
  refine VG.Proof.MdStream.X86.wp_addi fun s₃ u₃ => VG.Proof.MdStream.X86.wp_addi fun s₄ u₄ => VG.Proof.MdStream.X86.wp_subi fun s₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ebp → r ≠ .ecx → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, u₂.gpr, u₁.other r h4]
  have hrax : s₅.gpr .eax = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Update.tt P s₀ c - (j + 1)) := by
    rw [u₅.gpr, u₄.other .eax (by decide), u₃.other .eax (by decide), u₂.gpr, u₁.other .eax (by decide), h.eax,
      VG.Proof.MdStream.X86.ofNat_pred (by omega_using [hj]), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrax, ?_⟩, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .ebx (by decide) (by decide) (by decide) (by decide), h.ebx]
  · rw [g .esp (by decide) (by decide) (by decide) (by decide), h.esp]
  · rw [u₅.other .ebp (by decide), u₄.other .ebp (by decide), u₃.gpr, u₂.gpr, u₁.other .ebp (by decide), h.ebp,
      VG.Proof.MdStream.X86.lit32, VG.Proof.MdStream.X86.ofNat_add_add, Nat.add_assoc]
  · rw [g .esi (by decide) (by decide) (by decide) (by decide), h.esi]
  · rw [u₅.other .edi (by decide), u₄.gpr, u₃.other .edi (by decide), u₂.gpr, u₁.other .edi (by decide), h.edi,
      VG.Proof.MdStream.X86.lit32, VG.Proof.MdStream.X86.ofNat_add_add, Nat.add_assoc]
  · have hj' : j < (VG.Proof.MdStream.X86.Update.xs P s₀ c).length := by omega
    have hv : BitVec.setWidth 8 (s₁.gpr Reg8.cl.reg) = (VG.Proof.MdStream.X86.Update.D s₀).getD (c + j) 0 := by
      rw [show Reg8.cl.reg = Reg.ecx from rfl, u₁.gpr, BitVec.setWidth_setWidth_of_le _ (by decide),
        BitVec.setWidth_eq, hbyte]
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hv, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some,
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega_using [ht, hdf])]
    have hl : (List.take j (VG.Proof.MdStream.X86.Update.xs P s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl]
    congr 1
    simp only [VG.Proof.MdStream.X86.Update.xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (VG.Proof.MdStream.X86.Update.D s₀).length by rw [VG.Proof.MdStream.X86.Update.D_length]; omega_using [ht, hj]), Option.getD_some]
  · rw [hz₅, u₄.other .eax (by decide), u₃.other .eax (by decide), u₂.gpr, u₁.other .eax (by decide), h.eax,
      VG.Proof.MdStream.X86.ofNat_pred (by omega), VG.Proof.MdStream.X86.ofNat_beq_zero (by omega_using [ht, hdf]), show VG.Proof.MdStream.X86.Update.tt P s₀ c - j - 1 = VG.Proof.MdStream.X86.Update.tt P s₀ c - (j + 1) by omega]

theorem copy_loop_ok (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.X86.Update.Inv S H s₀ c sI)
    {s : State} (h : VG.Proof.MdStream.X86.Update.Copy P s₀ c sI.mem 0 s) (ht : 0 < VG.Proof.MdStream.X86.Update.tt P s₀ c) :
    WP isa (.loop (.block [.movzx8 .ecx (at_ .ebp 0), .store8 (at_ .edi P.N) .cl,
      .alu .add .ebp (.imm 1), .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne) s
      (VG.Proof.MdStream.X86.Update.Copy P s₀ c sI.mem (VG.Proof.MdStream.X86.Update.tt P s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = VG.Proof.MdStream.X86.Update.tt P s₀ c - j ∧ j < VG.Proof.MdStream.X86.Update.tt P s₀ c ∧ VG.Proof.MdStream.X86.Update.Copy P s₀ c sI.mem j s)
    ?_ (VG.Proof.MdStream.X86.Update.tt P s₀ c) s ⟨0, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (VG.Proof.MdStream.X86.Update.copy_step hd hp hI hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : VG.Proof.MdStream.X86.Update.tt P s₀ c - (j + 1) = 0
  · refine .inl ⟨by show s'.zf.map (!·) = _; rw [hz]; simp [hl], ?_⟩
    rwa [show j + 1 = VG.Proof.MdStream.X86.Update.tt P s₀ c by omega] at hc'
  · exact .inr ⟨by show s'.zf.map (!·) = _; rw [hz]; simp [hl], _, by omega, j + 1, rfl, by omega, hc'⟩

/-- The memory after copying `tt` bytes. -/
theorem copied_facts (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.X86.Update.Inv S H s₀ c sI) :
    let mem := VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.X86.Update.q P s₀ c) (VG.Proof.MdStream.X86.Update.xs P s₀ c)
    Frame [VG.Proof.MdStream.X86.Update.stR P s₀, VG.Proof.MdStream.X86.Update.scR S s₀, VG.Proof.MdStream.X86.Update.stkR s₀] s₀.mem mem ∧ VG.Proof.MdStream.X86.Update.Saved P s₀ mem ∧
      H.stateAt mem (VG.Proof.MdStream.X86.Update.stA s₀) = H.stateAt sI.mem (VG.Proof.MdStream.X86.Update.stA s₀) ∧
      bytesAt mem (VG.Proof.MdStream.X86.Update.buf P s₀) (VG.Proof.MdStream.X86.Update.rr P s₀ c + VG.Proof.MdStream.X86.Update.tt P s₀ c) = bytesAt sI.mem (VG.Proof.MdStream.X86.Update.buf P s₀) (VG.Proof.MdStream.X86.Update.rr P s₀ c) ++ VG.Proof.MdStream.X86.Update.xs P s₀ c := by
  intro mem
  have hr := VG.Proof.MdStream.X86.Update.rr_lt hd s₀ c; have ht' := VG.Proof.MdStream.X86.Update.tt_le' P s₀ c; have hd_N := hd.N; have hd_so := hd.so; have hd_S := hd.S
  have hd_le := hd.le
  have hxs := VG.Proof.MdStream.X86.Update.xs_length P s₀ c
  have hf : Frame [VG.Proof.MdStream.X86.Update.stR P s₀] sI.mem mem := by
    have := VG.Proof.MdStream.X86.Update.write_frame hd hp c sI.mem (VG.Proof.MdStream.X86.Update.tt P s₀ c) (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega)] at this
  have word : ∀ (R : Region), R.Disjoint (VG.Proof.MdStream.X86.Update.stR P s₀) → R.Contains R.base 4 →
      mem.readW R.base 32 = sI.mem.readW R.base 32 := fun R hR hc =>
    hf.readW hc (by simpa using hR) (by decide)
  refine ⟨hI.frame.trans (hf.mono (by simp)), fun p hp' => ?_, ?_, ?_⟩
  · have hd' := VG.Proof.MdStream.X86.saved_offset hp'
    rw [word ⟨addr (VG.Proof.MdStream.X86.Update.scr s₀) p.2, 4⟩ (hp.st_scr.symm.sub_left (hp.scr_sub (by omega_using [hd', hd_so]))) (Region.contains_self _ _)]
    exact hI.saved p hp'
  · apply H.stateAt_congr
    intro i hi
    exact VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by omega)
  · show bytesAt (VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.X86.Update.q P s₀ c) (VG.Proof.MdStream.X86.Update.xs P s₀ c)) (VG.Proof.MdStream.X86.Update.buf P s₀) (VG.Proof.MdStream.X86.Update.rr P s₀ c + VG.Proof.MdStream.X86.Update.tt P s₀ c) = _
    rw [← hxs, show VG.Proof.MdStream.X86.Update.q P s₀ c = VG.Proof.MdStream.X86.Update.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.X86.Update.rr P s₀ c) by
      simp only [VG.Proof.MdStream.X86.Update.q, VG.Proof.MdStream.X86.Update.buf]; rw [VG.Proof.MdStream.X86.add_ofNat]]
    exact bytesAt_writeBytes _ _ _ _ (by omega)

/-- The state after copying, whatever `edi`, `eax` and `ecx` hold. -/
structure Copied (P : Params) (s₀ : State) (c : Nat) (mI : Mem) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = VG.Proof.MdStream.X86.Update.st s₀
  esp : s.gpr .esp = VG.Proof.MdStream.X86.Update.esp₀ s₀
  ebp : s.gpr .ebp = VG.Proof.MdStream.X86.Update.dp s₀ + BitVec.ofNat 32 (c + VG.Proof.MdStream.X86.Update.tt P s₀ c)
  esi : s.gpr .esi = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Update.len s₀ - c - VG.Proof.MdStream.X86.Update.tt P s₀ c)
  mem : s.mem = VG.WriteBytes.writeBytes mI (VG.Proof.MdStream.X86.Update.q P s₀ c) (VG.Proof.MdStream.X86.Update.xs P s₀ c)

theorem Copy.copied {s₀ : State} {c : Nat} {mI : Mem} {s : State} (h : VG.Proof.MdStream.X86.Update.Copy P s₀ c mI (VG.Proof.MdStream.X86.Update.tt P s₀ c) s) :
    VG.Proof.MdStream.X86.Update.Copied P s₀ c mI s :=
  ⟨h.rd, h.wr, h.ebx, h.esp, h.ebp, h.esi,
    by rw [h.mem, List.take_of_length_le (by rw [VG.Proof.MdStream.X86.Update.xs_length])]⟩

theorem Copied.of_gpr {s₀ : State} {c : Nat} {mI : Mem} {s s' : State} (h : VG.Proof.MdStream.X86.Update.Copied P s₀ c mI s)
    (hg : ∀ r ∈ [Reg.ebx, .esp, .ebp, .esi], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.MdStream.X86.Update.Copied P s₀ c mI s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, by rw [hg _ (by simp)]; exact h.ebx, by rw [hg _ (by simp)]; exact h.esp,
    by rw [hg _ (by simp)]; exact h.ebp,
    by rw [hg _ (by simp)]; exact h.esi, hm.trans h.mem⟩

/-- A full buffer: compress it. -/
theorem fill_pending (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.X86.Update.Inv S H s₀ c sI)
    {s : State} (h : VG.Proof.MdStream.X86.Update.Copied P s₀ c sI.mem s) (hfull : VG.Proof.MdStream.X86.Update.rr P s₀ c + VG.Proof.MdStream.X86.Update.tt P s₀ c = P.B) :
    WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 P.N)), .mov .edi (.imm 0),
      .mov .ecx (.imm 1)]) s (VG.Proof.MdStream.X86.Update.Pending S H s₀ (c + VG.Proof.MdStream.X86.Update.tt P s₀ c) 1) := by
  have ht := VG.Proof.MdStream.X86.Update.tt_le P s₀ c; have hrr := VG.Proof.MdStream.X86.Update.rr_eq P s₀ c
  have hxs := VG.Proof.MdStream.X86.Update.xs_length P s₀ c
  have hc := hI.c_le; have hd_N := hd.N
  obtain ⟨hfr, hsv, hst, hby⟩ := VG.Proof.MdStream.X86.Update.copied_facts hd hp hI
  refine VG.Proof.MdStream.X86.wp_mov fun s₁ u₁ => VG.Proof.MdStream.X86.wp_addi fun s₂ u₂ => VG.Proof.MdStream.X86.wp_movi fun s₃ u₃ => VG.Proof.MdStream.X86.wp_movi fun s₄ u₄ => WP.block_nil ?_
  have g : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ecx → s₄.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₄.other r h3, u₃.other r h2, u₂.other r h1, u₁.other r h1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have heax : s₄.gpr .eax = VG.Proof.MdStream.X86.Update.st s₀ + BitVec.ofNat 32 P.N := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, h.ebx]
  refine ⟨⟨by omega_using [hc, ht], ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₄, h.mem]; exact hfr, by rw [m₄, h.mem]; exact hsv⟩,
    by rw [u₄.other _ (by decide), u₃.gpr], by rw [u₄.gpr]; rfl, Nat.one_pos,
    by rw [← Nat.add_assoc]; exact Md.add_mod_of_eq hfull, .inl ⟨heax, rfl⟩, ?_⟩
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .ebx (by decide) (by decide) (by decide), h.ebx]
  · rw [g .esp (by decide) (by decide) (by decide), h.esp]
  · rw [g .ebp (by decide) (by decide) (by decide), h.ebp]
  · rw [g .esi (by decide) (by decide) (by decide), h.esi, Nat.sub_sub]
  · intro iv m hm mem' hs
    rw [Md.compressBlocks_one] at hs
    rw [← VG.Proof.MdStream.X86.Update.take_add_data]
    have hmod := VG.Proof.MdStream.X86.Update.length_mid hd s₀ hm hc
    refine H.repr_append_block hd.pos (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₄, h.mem, hst, heax, show (VG.Proof.MdStream.X86.Update.st s₀ + BitVec.ofNat 32 P.N).setWidth 64 = addr (VG.Proof.MdStream.X86.Update.st s₀) P.N from rfl,
      addr_eq (by have hp_st_fit := hp.st_fit; have hd_pos := hd.pos; omega_using [hd_pos, hp_st_fit])]
    refine congrArg (H.compress _) ?_
    apply H.parse_congr
    intro k hk
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show VG.Proof.MdStream.X86.Update.rr P s₀ c + VG.Proof.MdStream.X86.Update.tt P s₀ c = P.B from hfull] at hby
    exact VG.Proof.MdStream.X86.bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.X86.Update.Inv S H s₀ c sI)
    {s : State} (h : VG.Proof.MdStream.X86.Update.Copied P s₀ c sI.mem s) (hedi : s.gpr .edi = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Update.rr P s₀ c + VG.Proof.MdStream.X86.Update.tt P s₀ c))
    (hecx : s.gpr .ecx = 0) (hnf : VG.Proof.MdStream.X86.Update.rr P s₀ c + VG.Proof.MdStream.X86.Update.tt P s₀ c ≠ P.B) : VG.Proof.MdStream.X86.Update.Done S H s₀ s := by
  have hr := VG.Proof.MdStream.X86.Update.rr_lt hd s₀ c; have ht' := VG.Proof.MdStream.X86.Update.tt_le' P s₀ c
  have hrr := VG.Proof.MdStream.X86.Update.rr_eq P s₀ c; have htt := VG.Proof.MdStream.X86.Update.tt_eq P s₀ c
  have hxs := VG.Proof.MdStream.X86.Update.xs_length P s₀ c
  have hc := hI.c_le
  have htl : VG.Proof.MdStream.X86.Update.tt P s₀ c = VG.Proof.MdStream.X86.Update.len s₀ - c := by omega
  obtain ⟨hfr, hsv, hst, hby⟩ := VG.Proof.MdStream.X86.Update.copied_facts hd hp hI
  refine ⟨⟨⟨(Nat.le_refl _), h.rd, h.wr, h.ebx, h.esp, ?_, ?_, by rw [h.mem]; exact hfr,
    by rw [h.mem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩, hecx⟩
  · rw [h.ebp]; congr 2; omega_using [htl, hc]
  · rw [h.esi]; congr 1; omega_using [htl]
  · rw [hedi]; congr 1
    rw [show VG.Proof.MdStream.X86.Update.cnt s₀ + VG.Proof.MdStream.X86.Update.len s₀ = VG.Proof.MdStream.X86.Update.cnt s₀ + c + VG.Proof.MdStream.X86.Update.tt P s₀ c by omega_using [htl, hc],
      Md.add_mod_of_lt (by omega_using [hrr, hr, ht', hnf])]
  · have hmod := VG.Proof.MdStream.X86.Update.length_mid hd s₀ hm hc
    rw [show VG.Proof.MdStream.X86.Update.len s₀ = c + VG.Proof.MdStream.X86.Update.tt P s₀ c by omega_using [htl, hc], ← VG.Proof.MdStream.X86.Update.take_add_data]
    refine H.repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega_using [hrr, ht', hr, hnf]) (by rw [h.mem, hst]) ?_
    rw [hmod, hxs, h.mem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_ok (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.X86.Update.Inv S H s₀ c s) :
    WP isa (fill P) s fun s' => (∃ c' k, c < c' ∧ VG.Proof.MdStream.X86.Update.Pending S H s₀ c' k s') ∨ VG.Proof.MdStream.X86.Update.Done S H s₀ s' := by
  have hr := VG.Proof.MdStream.X86.Update.rr_lt hd s₀ c; have ht' := VG.Proof.MdStream.X86.Update.tt_le' P s₀ c
  have htt := VG.Proof.MdStream.X86.Update.tt_eq P s₀ c
  have hlen := VG.Proof.MdStream.X86.Update.len_lt s₀; have hd_le := hd.le
  unfold fill
  -- `eax := B - edi; cmp esi, eax`
  refine WP.seq (VG.Proof.MdStream.X86.wp_movi fun s₂ u₂ => VG.Proof.MdStream.X86.wp_sub fun s₃ u₃ _ => VG.Proof.MdStream.X86.wp_cmp fun s₄ f₄ cf₄ _ => WP.block_nil ?_)
  have e₄ : ∀ r, r ≠ .eax → s₄.gpr r = s.gpr r := fun r h => by
    rw [f₄.gpr, u₃.other r h, u₂.other r h]
  have hm₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem]
  have hrd₄ : s₄.rd = s.rd := by rw [f₄.rd, u₃.rd, u₂.rd]
  have hwr₄ : s₄.wr = s.wr := by rw [f₄.wr, u₃.wr, u₂.wr]
  have heax₃ : s₃.gpr .eax = BitVec.ofNat 32 (P.B - VG.Proof.MdStream.X86.Update.rr P s₀ c) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), hI.edi, ← VG.Proof.MdStream.X86.Update.rr_eq,
      VG.Proof.MdStream.X86.sub_ofNat (a := P.B) (b := VG.Proof.MdStream.X86.Update.rr P s₀ c) (by omega)]
  have hcf : s₄.cf = some (decide (VG.Proof.MdStream.X86.Update.len s₀ - c < P.B - VG.Proof.MdStream.X86.Update.rr P s₀ c)) := by
    rw [cf₄, heax₃, u₃.other _ (by decide), u₂.other _ (by decide), hI.esi,
      VG.Proof.MdStream.X86.toNat_ofNat_lt (by omega), VG.Proof.MdStream.X86.toNat_ofNat_lt (by omega_using [hd_le])]
  -- `eax := min(eax, esi)`
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => s₅.gpr .eax = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Update.tt P s₀ c) ∧
    (∀ r, r ≠ .eax → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr) ?_
    fun s₅ ⟨heax₅, g₅, m₅, rd₅, wr₅⟩ => ?_)
  · refine WP.ite (decide (VG.Proof.MdStream.X86.Update.len s₀ - c < P.B - VG.Proof.MdStream.X86.Update.rr P s₀ c)) (by show s₄.cf = _; rw [hcf]) (fun hb => ?_) (fun hb => ?_)
    · refine VG.Proof.MdStream.X86.wp_mov fun s₅ u₅ => WP.block_nil ⟨?_, u₅.other, u₅.mem, u₅.rd, u₅.wr⟩
      rw [u₅.gpr, e₄ _ (by decide), hI.esi]; congr 1; simp at hb; omega_using [hb, htt]
    · refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      rw [f₄.gpr, heax₃]; congr 1; simp at hb; omega
  -- `esi -= eax; edi += ebx; test eax, eax`
  refine WP.seq (VG.Proof.MdStream.X86.wp_sub fun s₆ u₆ _ => VG.Proof.MdStream.X86.wp_add fun s₇ u₇ => VG.Proof.MdStream.X86.wp_test fun s₈ f₈ z₈ => WP.block_nil ?_)
  have g₈ : ∀ r, r ≠ .esi → r ≠ .edi → r ≠ .eax → s₈.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [f₈.gpr, u₇.other r h2, u₆.other r h1, g₅ r h3, e₄ r h3]
  have hm₈ : s₈.mem = s.mem := by rw [f₈.mem, u₇.mem, u₆.mem, m₅, hm₄]
  have hC₀ : VG.Proof.MdStream.X86.Update.Copy P s₀ c s.mem 0 s₈ := by
    refine ⟨Nat.zero_le _, by rw [f₈.rd, u₇.rd, u₆.rd, rd₅, hrd₄, hI.rd], by rw [f₈.wr, u₇.wr, u₆.wr, wr₅, hwr₄, hI.wr],
      by rw [g₈ _ (by decide) (by decide) (by decide), hI.ebx],
      by rw [g₈ _ (by decide) (by decide) (by decide), hI.esp],
      by rw [g₈ _ (by decide) (by decide) (by decide), hI.ebp, Nat.add_zero], ?_, ?_, ?_,
      by rw [hm₈, List.take_zero, VG.WriteBytes.writeBytes_nil]⟩
    · rw [f₈.gpr, u₇.other _ (by decide), u₆.gpr, g₅ _ (by decide), e₄ _ (by decide), hI.esi,
        heax₅, VG.Proof.MdStream.X86.sub_ofNat (by omega)]
    · rw [f₈.gpr, u₇.gpr, u₆.other _ (by decide), g₅ _ (by decide), e₄ _ (by decide), hI.edi,
        u₆.other _ (by decide), g₅ _ (by decide), e₄ _ (by decide), hI.ebx, BitVec.add_comm,
        ← VG.Proof.MdStream.X86.Update.rr_eq, Nat.add_zero]
    · rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), heax₅, Nat.sub_zero]
  have hz₈ : s₈.zf = some (decide (VG.Proof.MdStream.X86.Update.tt P s₀ c = 0)) := by
    rw [z₈, u₇.other _ (by decide), u₆.other _ (by decide), heax₅, BitVec.and_self, VG.Proof.MdStream.X86.ofNat_beq_zero (by omega)]
  -- Copy the bytes.
  refine WP.seq (WP.mono (Q := VG.Proof.MdStream.X86.Update.Copy P s₀ c s.mem (VG.Proof.MdStream.X86.Update.tt P s₀ c)) ?_ fun s₉ hC => ?_)
  · refine WP.ite (decide (VG.Proof.MdStream.X86.Update.tt P s₀ c = 0)) (by show s₈.zf = _; rw [hz₈]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil (hb ▸ hC₀)
    · simp only [decide_eq_false_iff_not] at hb
      exact VG.Proof.MdStream.X86.Update.copy_loop_ok hd hp hI hC₀ (by omega)
  -- Is the buffer full?
  refine WP.seq (VG.Proof.MdStream.X86.wp_sub fun s₁₀ u₁₀ _ => VG.Proof.MdStream.X86.wp_movi fun s₁₁ u₁₁ => VG.Proof.MdStream.X86.wp_cmpi fun s₁₂ f₁₂ _ z₁₂ => WP.block_nil ?_)
  have hC₁₂ : VG.Proof.MdStream.X86.Update.Copied P s₀ c s.mem s₁₂ :=
    hC.copied.of_gpr (fun r hr => by
      rw [f₁₂.gpr, u₁₁.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
        u₁₀.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide)])
      (by rw [f₁₂.mem, u₁₁.mem, u₁₀.mem]) (by rw [f₁₂.rd, u₁₁.rd, u₁₀.rd]) (by rw [f₁₂.wr, u₁₁.wr, u₁₀.wr])
  have hedi₁₂ : s₁₂.gpr .edi = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Update.rr P s₀ c + VG.Proof.MdStream.X86.Update.tt P s₀ c) := by
    rw [f₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr, hC.edi, hC.ebx, BitVec.add_comm, BitVec.add_sub_cancel]
  have hz₁₂ : s₁₂.zf = some (decide (VG.Proof.MdStream.X86.Update.rr P s₀ c + VG.Proof.MdStream.X86.Update.tt P s₀ c = P.B)) := by
    rw [z₁₂, ← f₁₂.gpr, hedi₁₂, VG.Proof.MdStream.X86.sub_beq (a := VG.Proof.MdStream.X86.Update.rr P s₀ c + VG.Proof.MdStream.X86.Update.tt P s₀ c) (b := P.B) (by omega_using [hd_le, ht', hr]) (by omega)]
  have hecx : s₁₂.gpr .ecx = 0 := by rw [f₁₂.gpr, u₁₁.gpr]
  refine WP.ite (decide (VG.Proof.MdStream.X86.Update.rr P s₀ c + VG.Proof.MdStream.X86.Update.tt P s₀ c = P.B)) (by show s₁₂.zf = _; rw [hz₁₂]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (VG.Proof.MdStream.X86.Update.fill_pending hd hp hI hC₁₂ hb) fun s' h => .inl ⟨c + VG.Proof.MdStream.X86.Update.tt P s₀ c, 1, by omega_using [hb, hr], h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (VG.Proof.MdStream.X86.Update.fill_done hd hp hI hC₁₂ hedi₁₂ hecx hb))

theorem body_ok (hd : VG.Proof.MdStream.X86.Dims P S) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.X86.Update.Inv S H s₀ c s) :
    WP isa (updateBody P name code) s (VG.Proof.MdStream.X86.Update.Step S H s₀ c) := by
  have hlen := VG.Proof.MdStream.X86.Update.len_lt s₀; have hr : (VG.Proof.MdStream.X86.Update.cnt s₀ + c) % P.B < P.B := VG.Proof.MdStream.X86.Update.rr_lt hd s₀ c; have hd_le := hd.le
  unfold updateBody
  refine WP.seq (VG.Proof.MdStream.X86.wp_test fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hI₁ := hI.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr
  refine WP.seq (WP.mono (Q := fun s' => (∃ c' k, c < c' ∧ VG.Proof.MdStream.X86.Update.Pending S H s₀ c' k s') ∨ VG.Proof.MdStream.X86.Update.Done S H s₀ s') ?_
    fun s' h => VG.Proof.MdStream.X86.Update.tail_ok hd hf hp h)
  refine WP.ite (decide (VG.Proof.MdStream.X86.Update.rr P s₀ c = 0))
    (by show s₁.zf = _; rw [z₁, hI.edi, BitVec.and_self, VG.Proof.MdStream.X86.ofNat_beq_zero (by omega)])
    (fun hb => ?_) (fun _ => VG.Proof.MdStream.X86.Update.fill_ok hd hp hI₁)
  simp only [decide_eq_true_eq] at hb
  refine WP.seq (VG.Proof.MdStream.X86.wp_cmpi fun s₂ f₂ cf₂ _ => WP.block_nil ?_)
  have hI₂ := hI₁.of_gpr (fun r _ => by rw [f₂.gpr]) f₂.mem f₂.rd f₂.wr
  have hcf : s₂.cf = some (decide (VG.Proof.MdStream.X86.Update.len s₀ - c < P.B)) := by
    rw [cf₂, hI₁.esi, VG.Proof.MdStream.X86.toNat_ofNat_lt (k := VG.Proof.MdStream.X86.Update.len s₀ - c) (by omega), VG.Proof.MdStream.X86.toNat_ofNat_lt (k := P.B) (by omega)]
  refine WP.ite (!decide (VG.Proof.MdStream.X86.Update.len s₀ - c < P.B)) (by show s₂.cf.map (!·) = _; rw [hcf]; rfl)
    (fun hb' => ?_) (fun _ => VG.Proof.MdStream.X86.Update.fill_ok hd hp hI₂)
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb'
  have := Nat.mul_pos hd.pos (Nat.div_pos hb' hd.pos)
  exact WP.mono (VG.Proof.MdStream.X86.Update.direct_ok hd hp hI₂ hb hb') fun s' h => .inl ⟨_, _, by omega, h⟩

theorem correct (hd : VG.Proof.MdStream.X86.Dims P S) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.X86.Update.Pre P S s₀) :
    WP isa (update P name code) s₀ fun s' => abiPreserved s₀ s' ∧ (VG.Proof.MdStream.X86.updK H S).post s₀ s' := by
  unfold update
  refine WP.seq (WP.mono (VG.Proof.MdStream.X86.Update.prologue_ok (H := H) hd hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.MdStream.X86.Update.Inv S H s₀ (VG.Proof.MdStream.X86.Update.len s₀)) ?_ fun s₂ hI₂ => VG.Proof.MdStream.X86.Update.epilogue_ok hd hp hI₂)
  refine WP.loop (M := isa) (fun n s => ∃ c, n = VG.Proof.MdStream.X86.Update.len s₀ - c ∧ VG.Proof.MdStream.X86.Update.Inv S H s₀ c s) ?_ (VG.Proof.MdStream.X86.Update.len s₀) s₁ ⟨0, rfl, hI⟩
  rintro n s ⟨c, rfl, hI⟩
  refine WP.mono (VG.Proof.MdStream.X86.Update.body_ok hd hf hp hI) fun s' h => ?_
  rcases h with ⟨he, hI'⟩ | ⟨he, c', hc, hI'⟩
  · exact .inl ⟨he, hI'⟩
  · exact .inr ⟨he, VG.Proof.MdStream.X86.Update.len s₀ - c', by have := hI'.c_le; omega, c', rfl, hI'⟩

end

/-! ## Constant time -/

theorem argWord_eq {s : State} {n : Nat} (hsp : (s.gpr .esp).toNat + 4 + n ≤ 2 ^ 32) {k : Nat} (hk : k < n) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by omega), addr_eq (by omega), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega

/-- The initial taint: the stack arguments are public, the words holding
`state` and `scratch` are the base addresses of the writable regions, and the
20 bytes below `esp` are outside them. -/
def τ₀ (P : Params) (S : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [P.N + P.B, S], argLen := 28,
    argBases := [(4, 0), (24, 1)], room := 20 }

section
variable {P : Params} {S : Nat} {H : Md P.B P.N P.L}

theorem wf₀ (hd : VG.Proof.MdStream.X86.Dims P S) {s : State} (h : (VG.Proof.MdStream.X86.updK H S).pre s) : VG.X86.Taint.Wf (VG.Proof.MdStream.X86.Update.τ₀ P S) s := by
  have hp := VG.Proof.MdStream.X86.Update.pre_of h
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo; have hd_N := hd.N
  obtain ⟨-, -, -, -, -, -, -, -, -, k1, k2, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.MdStream.X86.Update.τ₀], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.st_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.a_st
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.a_scr
  · intro p hp'
    simp only [VG.Proof.MdStream.X86.Update.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp [VG.Proof.MdStream.X86.Update.τ₀], ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, VG.X86.arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [k1, k2]

theorem agree₀ (hd : VG.Proof.MdStream.X86.Dims P S) {s₁ s₂ : State} (h₁ : (VG.Proof.MdStream.X86.updK H S).pre s₁) (h₂ : (VG.Proof.MdStream.X86.updK H S).pre s₂)
    (hpub : (VG.Proof.MdStream.X86.updK H S).pub s₁ s₂) : VG.X86.Taint.Agree (VG.Proof.MdStream.X86.Update.τ₀ P S) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := VG.Proof.MdStream.X86.Update.pre_of h₁; have hp₂ := VG.Proof.MdStream.X86.Update.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.MdStream.X86.Update.wf₀ hd h₁, VG.Proof.MdStream.X86.Update.wf₀ hd h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.MdStream.X86.Update.τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [VG.Proof.MdStream.X86.Update.stR, VG.Proof.MdStream.X86.Update.scR, VG.Proof.MdStream.X86.Update.stA, VG.Proof.MdStream.X86.Update.scA, VG.Proof.MdStream.X86.Update.st, VG.Proof.MdStream.X86.Update.scr, ha 0 (by decide), ha 5 (by decide)]
  · simp only [VG.Proof.MdStream.X86.Update.τ₀] at hk
    rw [show VG.X86.Taint.depth (VG.Proof.MdStream.X86.Update.τ₀ P S).stk = 0 from rfl, Nat.zero_add]
    have f₁ : (s₁.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp₁.sp_fit
    have f₂ : (s₂.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp₂.sp_fit
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha _ (by omega))

end

/-- Memory holding the arguments `0x1000, 0, 0, 0x2000, 0, 0x3000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5019 then 0x30 else 0

/-- The registers and memory of a state satisfying the precondition (with no data). -/
def sat₀ : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.MdStream.X86.Update.satMem
  rd := []
  wr := []

/-- A state satisfying the precondition (with no data). -/
def sat (P : Params) (S : Nat) : State :=
  { VG.Proof.MdStream.X86.Update.sat₀ with
              rd := [⟨0x2000, 0⟩, ⟨0x5004, 24⟩], wr := [⟨0x1000, P.N + P.B⟩, ⟨0x3000, S⟩] }

section
variable {P : Params} {S : Nat} {H : Md P.B P.N P.L}

theorem sat_pre (hd : VG.Proof.MdStream.X86.Dims P S) : (VG.Proof.MdStream.X86.updK H S).pre (VG.Proof.MdStream.X86.Update.sat P S) := by
  have hd_N := hd.N; have hd_S := hd.S; have hd_le := hd.le
  have a0 : VG.X86.arg (VG.Proof.MdStream.X86.Update.sat P S) 0 = 0x1000 := show VG.X86.arg VG.Proof.MdStream.X86.Update.sat₀ 0 = _ by decide
  have a3 : VG.X86.arg (VG.Proof.MdStream.X86.Update.sat P S) 3 = 0x2000 := show VG.X86.arg VG.Proof.MdStream.X86.Update.sat₀ 3 = _ by decide
  have a4 : VG.X86.arg (VG.Proof.MdStream.X86.Update.sat P S) 4 = 0 := show VG.X86.arg VG.Proof.MdStream.X86.Update.sat₀ 4 = _ by decide
  have a5 : VG.X86.arg (VG.Proof.MdStream.X86.Update.sat P S) 5 = 0x3000 := show VG.X86.arg VG.Proof.MdStream.X86.Update.sat₀ 5 = _ by decide
  have e : argAddr (VG.Proof.MdStream.X86.Update.sat P S) 0 = 0x5004 := show argAddr VG.Proof.MdStream.X86.Update.sat₀ 0 = _ by decide
  have hsp : (VG.Proof.MdStream.X86.Update.sat P S).gpr .esp = 0x5000 := rfl
  simp only [VG.Proof.MdStream.X86.updK, a0, a3, a4, a5, e, hsp]
  have hs : ((0x5000 : BitVec 32).setWidth 64 - 20 : Addr) = 0x4FEC := by decide
  simp only [hs]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp; omega, by decide, by simp; omega,
    by decide, by decide⟩ <;>
  · first
    | exact Offset.disjoint_of_le (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)
        (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)
    | exact (Offset.disjoint_of_le (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)
        (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)).symm

/-- `update` is verified, given that it is constant time (by the taint analysis of each hash
function's code, from `τ₀` and `agree₀`). -/
theorem verified (hd : VG.Proof.MdStream.X86.Dims P S) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86.CalleeOk H code)
    (hct : ConstantTime isa (VG.Proof.MdStream.X86.updK H S).pre (VG.Proof.MdStream.X86.updK H S).pub (update P name code)) :
    Verified X86.target (update P name code) (VG.Proof.MdStream.X86.updK H S) := by
  refine ⟨fun s hs => ?_, hct, ⟨VG.Proof.MdStream.X86.Update.sat P S, VG.Proof.MdStream.X86.Update.sat_pre hd⟩⟩
  obtain ⟨t, s', he, h⟩ := VG.Proof.MdStream.X86.Update.correct hd hf (VG.Proof.MdStream.X86.Update.pre_of hs)
  exact ⟨t, s', he, h⟩

end

end VG.Proof.MdStream.X86.Update

/-!
# Streaming Merkle–Damgård hash functions on x86 (32-bit): `finalize`

The correctness of `finalize`, for any hash function (`Md`) whose code stores
the length field and writes the digest as `Shape` says, and any correct
compression function (`CalleeOk`), with `state` in `ebx`, `scratch` in `ebp`,
the buffered bytes in `edi`, whether the block being padded is not the last in
`esi`, and `count` and `out` in `scratch[so+16..so+28)`. Each compression
calls the compression function (`compressAt_ok`), which uses the 20 bytes
below `esp`. Constant time follows from the taint analysis of each hash
function's code (which looks into the compression function).
-/

namespace VG.Proof.MdStream.X86.Finalize

open VG VG.X86 VG.Impl.MdStream.X86
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.MdStream.X86.Update (argWord_eq)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame bytesAt_congr)

/-! ## The precondition -/

section
variable (P : Params) (S : Nat) (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := VG.X86.arg s₀ 0
abbrev cnt : Nat := (VG.Proof.MdStream.X86.count s₀).toNat
abbrev out : BitVec 32 := VG.X86.arg s₀ 3
abbrev scr : BitVec 32 := VG.X86.arg s₀ 4
abbrev stA : Addr := (VG.Proof.MdStream.X86.Finalize.st s₀).setWidth 64
abbrev outA : Addr := (VG.Proof.MdStream.X86.Finalize.out s₀).setWidth 64
abbrev scA : Addr := (VG.Proof.MdStream.X86.Finalize.scr s₀).setWidth 64
abbrev stR : Region := ⟨VG.Proof.MdStream.X86.Finalize.stA s₀, P.N + P.B⟩
abbrev outR : Region := ⟨VG.Proof.MdStream.X86.Finalize.outA s₀, P.N⟩
abbrev scR : Region := ⟨VG.Proof.MdStream.X86.Finalize.scA s₀, S⟩
abbrev argR : Region := ⟨addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) 4, 20⟩
abbrev retR : Region := ⟨(VG.Proof.MdStream.X86.Finalize.esp₀ s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) 20
/-- The buffer. -/
abbrev buf : Addr := VG.Proof.MdStream.X86.Finalize.stA s₀ + BitVec.ofNat 64 P.N

/-- Our caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop := ∀ p ∈ saved P, m.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) p.2) 32 = s₀.gpr p.1

end

section
variable {P : Params} (H : Md P.B P.N P.L) (s₀ : State)

/-- The messages the initial state represents, from `iv`. -/
def R₀ (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (VG.Proof.MdStream.X86.Finalize.stA s₀) m ∧ VG.Proof.MdStream.X86.count s₀ = BitVec.ofNat 64 m.length

/-- The final hash value, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.compress (H.stateAt mem (VG.Proof.MdStream.X86.Finalize.stA s₀))
    (H.parse fun t => (bytesAt mem (VG.Proof.MdStream.X86.Finalize.buf P s₀) n ++ List.replicate (P.B - n) 0).getD t 0))
    (H.parse fun t => (List.replicate (P.B - P.L) 0 ++ H.lenBytes m.length).getD t 0)

/-- The final hash value, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.stateAt mem (VG.Proof.MdStream.X86.Finalize.stA s₀))
    (H.parse fun t => (bytesAt mem (VG.Proof.MdStream.X86.Finalize.buf P s₀) n ++ List.replicate (P.B - P.L - n) 0 ++
      H.lenBytes m.length).getD t 0)

end

structure Pre (P : Params) (S : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.MdStream.X86.Finalize.argR s₀]
  wr : s₀.wr = [VG.Proof.MdStream.X86.Finalize.stR P s₀, VG.Proof.MdStream.X86.Finalize.outR P s₀, VG.Proof.MdStream.X86.Finalize.scR S s₀]
  st_out : (VG.Proof.MdStream.X86.Finalize.stR P s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.outR P s₀)
  st_scr : (VG.Proof.MdStream.X86.Finalize.stR P s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.scR S s₀)
  out_scr : (VG.Proof.MdStream.X86.Finalize.outR P s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.scR S s₀)
  a_st : (VG.Proof.MdStream.X86.Finalize.argR s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.stR P s₀)
  a_out : (VG.Proof.MdStream.X86.Finalize.argR s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.outR P s₀)
  a_scr : (VG.Proof.MdStream.X86.Finalize.argR s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.scR S s₀)
  ret_st : (VG.Proof.MdStream.X86.Finalize.retR s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.stR P s₀)
  ret_out : (VG.Proof.MdStream.X86.Finalize.retR s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.outR P s₀)
  ret_scr : (VG.Proof.MdStream.X86.Finalize.retR s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.scR S s₀)
  stk_st : (VG.Proof.MdStream.X86.Finalize.stkR s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.stR P s₀)
  stk_out : (VG.Proof.MdStream.X86.Finalize.stkR s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.outR P s₀)
  stk_scr : (VG.Proof.MdStream.X86.Finalize.stkR s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.scR S s₀)
  st_fit : (VG.Proof.MdStream.X86.Finalize.st s₀).toNat + (P.N + P.B) ≤ 2 ^ 32
  out_fit : (VG.Proof.MdStream.X86.Finalize.out s₀).toNat + P.N ≤ 2 ^ 32
  scr_fit : (VG.Proof.MdStream.X86.Finalize.scr s₀).toNat + S ≤ 2 ^ 32
  sp_lo : 20 ≤ (VG.Proof.MdStream.X86.Finalize.esp₀ s₀).toNat
  sp_fit : (VG.Proof.MdStream.X86.Finalize.esp₀ s₀).toNat + 24 ≤ 2 ^ 32

section
variable {P : Params} {S : Nat} {H : Md P.B P.N P.L}

theorem pre_of {s₀ : State} (h : (VG.Proof.MdStream.X86.finK H S).pre s₀) : VG.Proof.MdStream.X86.Finalize.Pre P S s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  have e := VG.Proof.MdStream.X86.stk_eq h18
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    by show (below _ _).Disjoint _; rw [e]; exact h13, by show (below _ _).Disjoint _; rw [e]; exact h14,
    h15, h16, h17, h18, h19⟩

theorem cnt_mod (hd : VG.Proof.MdStream.X86.Dims P S) (s₀ : State) : VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B = (VG.X86.arg s₀ 1).toNat % P.B :=
  hd.mod_append _ _

theorem R₀.length {s₀ : State} {iv : H.HV} {m : List Byte} (h : VG.Proof.MdStream.X86.Finalize.R₀ H s₀ iv m) (hd : VG.Proof.MdStream.X86.Dims P S) :
    VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B = m.length % P.B := by
  rw [VG.Proof.MdStream.X86.Finalize.cnt, h.2, BitVec.toNat_ofNat, hd.mod]

namespace Pre
variable {s₀ : State} (hp : VG.Proof.MdStream.X86.Finalize.Pre P S s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ S) : (VG.Proof.MdStream.X86.Finalize.scR S s₀).Contains (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) 4 :=
  VG.Proof.MdStream.X86.contains_addr hd (by decide) hp.scr_fit

theorem scr_sub {d : Nat} (hd : d + 4 ≤ S) : Region.Sub ⟨addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d, 4⟩ (VG.Proof.MdStream.X86.Finalize.scR S s₀) := by
  rw [addr_eq (by have hp_scr_fit := hp.scr_fit; omega)]
  exact VG.Proof.MdStream.X86.sub_offset hd (by have hp_scr_fit := hp.scr_fit; omega)

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : (VG.Proof.MdStream.X86.Finalize.argR s₀).Contains (addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) d) 4 := by
  have hp_sp_fit := hp.sp_fit
  show (⟨addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) 4, 20⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by decide)

theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : Region.Sub ⟨addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) d, 4⟩ (VG.Proof.MdStream.X86.Finalize.argR s₀) := by
  have hp_sp_fit := hp.sp_fit
  show Region.Sub _ ⟨addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) 4, 20⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

/-- The return address is below the arguments. -/
theorem ret_a : (VG.Proof.MdStream.X86.Finalize.retR s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.argR s₀) := by
  have hp_sp_fit := hp.sp_fit
  show Region.Disjoint ⟨(VG.Proof.MdStream.X86.Finalize.esp₀ s₀).setWidth 64, 4⟩ ⟨addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) 4, 20⟩
  rw [addr_eq (by omega)]
  exact Offset.base_disjoint _ (Nat.le_refl _) (by decide)

theorem ret_stk : (VG.Proof.MdStream.X86.Finalize.retR s₀).Disjoint (VG.Proof.MdStream.X86.Finalize.stkR s₀) := by
  have hp_sp_fit := hp.sp_fit; have hp_sp_lo := hp.sp_lo
  show Region.Disjoint ⟨(VG.Proof.MdStream.X86.Finalize.esp₀ s₀).setWidth 64, 4⟩ ⟨(VG.Proof.MdStream.X86.Finalize.esp₀ s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩
  rw [Taint.sub_setWidth (by omega)]
  exact Offset.base_disjoint_below _ (by decide)

end Pre

end

/-! ## Invariants -/

/-- Where the zeros end in the block being padded: at the length field in the
last block (`k = 0`), at its end in the one before (`k = 1`). -/
def lim (P : Params) (k : Nat) : Nat := if k = 0 then P.B - P.L else P.B

theorem lim_zero (P : Params) : VG.Proof.MdStream.X86.Finalize.lim P 0 = P.B - P.L := rfl
theorem lim_one (P : Params) : VG.Proof.MdStream.X86.Finalize.lim P 1 = P.B := rfl
theorem lim_le (P : Params) (k : Nat) : VG.Proof.MdStream.X86.Finalize.lim P k ≤ P.B := by unfold VG.Proof.MdStream.X86.Finalize.lim; split <;> omega
theorem lim_ge (P : Params) (k : Nat) : P.B - P.L ≤ VG.Proof.MdStream.X86.Finalize.lim P k := by unfold VG.Proof.MdStream.X86.Finalize.lim; split <;> omega

structure Common (P : Params) (S : Nat) (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = VG.Proof.MdStream.X86.Finalize.st s₀
  ebp : s.gpr .ebp = VG.Proof.MdStream.X86.Finalize.scr s₀
  esp : s.gpr .esp = VG.Proof.MdStream.X86.Finalize.esp₀ s₀
  frame : Frame [VG.Proof.MdStream.X86.Finalize.stR P s₀, VG.Proof.MdStream.X86.Finalize.scR S s₀, VG.Proof.MdStream.X86.Finalize.argR s₀, VG.Proof.MdStream.X86.Finalize.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.MdStream.X86.Finalize.Saved P s₀ s.mem
  lo : s.mem.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 16)) 32 = VG.X86.arg s₀ 1
  hi : s.mem.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 20)) 32 = VG.X86.arg s₀ 2
  outp : s.mem.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 24)) 32 = VG.Proof.MdStream.X86.Finalize.out s₀

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv {P : Params} (S : Nat) (H : Md P.B P.N P.L) (s₀ : State) (k n : Nat) (s : State) : Prop
    extends VG.Proof.MdStream.X86.Finalize.Common P S s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ VG.Proof.MdStream.X86.Finalize.lim P k
  edi : s.gpr .edi = BitVec.ofNat 32 n
  esi : s.gpr .esi = BitVec.ofNat 32 k
  hash : ∀ iv m, VG.Proof.MdStream.X86.Finalize.R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m =
    H.digest (if k = 1 then VG.Proof.MdStream.X86.Finalize.Fin1 H s₀ s.mem n m else VG.Proof.MdStream.X86.Finalize.Fin0 H s₀ s.mem n m)

/-- All blocks are compressed. -/
def Done {P : Params} (S : Nat) (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  VG.Proof.MdStream.X86.Finalize.Common P S s₀ s ∧ ∀ iv m, VG.Proof.MdStream.X86.Finalize.R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m = H.digest (H.stateAt s.mem (VG.Proof.MdStream.X86.Finalize.stA s₀))

section
variable {P : Params} {S : Nat} {H : Md P.B P.N P.L}

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : VG.Proof.MdStream.X86.Finalize.Common P S s₀ s)
    (hg : ∀ r ∈ [Reg.ebx, .ebp, .esp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.MdStream.X86.Finalize.Common P S s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  ebp := by rw [hg _ (by simp)]; exact h.ebp
  esp := by rw [hg _ (by simp)]; exact h.esp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  lo := by rw [hm]; exact h.lo
  hi := by rw [hm]; exact h.hi
  outp := by rw [hm]; exact h.outp

/-- A write within `stR` or the arguments keeps what `Common` says about memory. -/
theorem Common.frame_keep (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Finalize.Pre P S s₀) {s : State} (h : VG.Proof.MdStream.X86.Finalize.Common P S s₀ s)
    {m : Mem} (hf : Frame [VG.Proof.MdStream.X86.Finalize.stR P s₀, VG.Proof.MdStream.X86.Finalize.argR s₀] s.mem m) :
    Frame [VG.Proof.MdStream.X86.Finalize.stR P s₀, VG.Proof.MdStream.X86.Finalize.scR S s₀, VG.Proof.MdStream.X86.Finalize.argR s₀, VG.Proof.MdStream.X86.Finalize.stkR s₀] s₀.mem m ∧ VG.Proof.MdStream.X86.Finalize.Saved P s₀ m ∧
      m.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 16)) 32 = VG.X86.arg s₀ 1 ∧ m.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 20)) 32 = VG.X86.arg s₀ 2 ∧
      m.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 24)) 32 = VG.Proof.MdStream.X86.Finalize.out s₀ := by
  have hd_so := hd.so
  have word : ∀ d, d + 4 ≤ S → m.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) 32 = s.mem.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) 32 := by
    intro d h₂
    refine hf.readW (r := ⟨addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_scr.symm.sub_left (hp.scr_sub h₂)
    · exact hp.a_scr.symm.sub_left (hp.scr_sub h₂)
  refine ⟨h.frame.trans (hf.mono (by simp)), fun p hp' => ?_, by rw [word _ (by omega_using [hd.so])]; exact h.lo,
    by rw [word _ (by omega_using [hd.so])]; exact h.hi, by rw [word _ (by omega_using [hd.so])]; exact h.outp⟩
  have hd' := VG.Proof.MdStream.X86.saved_offset hp'
  rw [word p.2 (by omega)]
  exact h.saved p hp'

theorem buf_add (s₀ : State) (n : Nat) : VG.Proof.MdStream.X86.Finalize.buf P s₀ + BitVec.ofNat 64 n = VG.Proof.MdStream.X86.Finalize.stA s₀ + BitVec.ofNat 64 (P.N + n) :=
  VG.Proof.MdStream.X86.add_ofNat _ _ _

/-- Writing buffer bytes `[n, n + |xs|)`. -/
theorem buf_frame (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (m : Mem) {n : Nat} {xs : List Byte} (hn : n + xs.length ≤ P.B) :
    Frame [VG.Proof.MdStream.X86.Finalize.stR P s₀] m (VG.WriteBytes.writeBytes m (VG.Proof.MdStream.X86.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) := by
  have hd_N := hd.N; have hd_le := hd.le
  refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
  rw [VG.Proof.MdStream.X86.Finalize.buf_add]
  exact VG.Proof.MdStream.X86.contains_offset (by omega) (by omega)

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (P : Params) (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.ebx, .ebp, .esp, .esi, .ecx], s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  edi : s.gpr .edi = BitVec.ofNat 32 (n + j)
  eax : s.gpr .eax = BitVec.ofNat 32 (lim - n - j)
  mem : s.mem = VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.X86.Finalize.buf P s₀ + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Finalize.Pre P S s₀) {sI : State} (hC : VG.Proof.MdStream.X86.Finalize.Common P S s₀ sI)
    (hecx : sI.gpr .ecx = 0) {n lim j : Nat} (hlim : lim ≤ P.B) (hj : j < lim - n) {s : State}
    (h : VG.Proof.MdStream.X86.Finalize.Zero P s₀ sI n lim j s) :
    WP isa (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .store8 (at_ .edx P.N) .cl,
      .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) s fun s' =>
      VG.Proof.MdStream.X86.Finalize.Zero P s₀ sI n lim (j + 1) s' ∧ s'.zf = some (decide (lim - n - (j + 1) = 0)) := by
  have hst := hp.st_fit; have hd_N := hd.N
  have hebx : s.gpr .ebx = VG.Proof.MdStream.X86.Finalize.st s₀ := by rw [h.keep _ (by simp), hC.ebx]
  have ha : VG.Proof.MdStream.X86.Finalize.buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j = VG.Proof.MdStream.X86.Finalize.stA s₀ + BitVec.ofNat 64 (P.N + n + j) := by
    simp only [VG.Proof.MdStream.X86.Finalize.buf, BitVec.ofNat_add]; ac_rfl
  have hout : InRegions s.wr (VG.Proof.MdStream.X86.Finalize.buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨VG.Proof.MdStream.X86.Finalize.stR P s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [ha]
    exact VG.Proof.MdStream.X86.contains_offset (by omega) (by omega)
  refine VG.Proof.MdStream.X86.wp_mov fun s₁ u₁ => VG.Proof.MdStream.X86.wp_add fun s₂ u₂ => ?_
  refine VG.Proof.MdStream.X86.wp_store8 (r := .cl) (a := VG.Proof.MdStream.X86.Finalize.buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ u₃ => ?_
  · rw [VG.Proof.MdStream.X86.ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), hebx, h.edi, ha,
      VG.Proof.MdStream.X86.addr_add_ofNat (by omega)]
    congr 2; omega
  refine VG.Proof.MdStream.X86.wp_addi fun s₄ u₄ => VG.Proof.MdStream.X86.wp_subi fun s₅ u₅ hz₅ => WP.block_nil ⟨⟨by omega, fun r hr => ?_,
    by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .eax ∧ r ≠ .edi ∧ r ≠ .edx := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₅.other r this.1, u₄.other r this.2.1, u₃.gpr, u₂.other r this.2.2, u₁.other r this.2.2, h.keep r hr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.edi,
      ← VG.Proof.MdStream.X86.ofNat_succ, Nat.add_assoc]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.eax,
      VG.Proof.MdStream.X86.ofNat_pred (by omega), Nat.sub_sub]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, show Reg8.cl.reg = Reg.ecx from rfl, u₂.other _ (by decide),
      u₁.other _ (by decide), h.keep _ (by simp), hecx, h.mem, List.replicate_succ',
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [hz₅, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.eax,
      VG.Proof.MdStream.X86.ofNat_pred (by omega), VG.Proof.MdStream.X86.ofNat_beq_zero (by omega), Nat.sub_sub, Nat.sub_sub]

theorem zero_ok (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Finalize.Pre P S s₀) {sI : State} (hC : VG.Proof.MdStream.X86.Finalize.Common P S s₀ sI)
    (hecx : sI.gpr .ecx = 0) {n lim : Nat} (hlim : lim ≤ P.B) (hn : n ≤ lim) {s : State}
    (h : VG.Proof.MdStream.X86.Finalize.Zero P s₀ sI n lim 0 s) (hz : s.zf = some (decide (lim - n = 0))) :
    WP isa (.ite .e (.block []) (.loop (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi),
      .store8 (at_ .edx P.N) .cl, .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne)) s
      (VG.Proof.MdStream.X86.Finalize.Zero P s₀ sI n lim (lim - n)) := by
  refine WP.ite (decide (lim - n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ VG.Proof.MdStream.X86.Finalize.Zero P s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (VG.Proof.MdStream.X86.Finalize.zero_step hd hp hC hecx hlim hj hZ) fun s' ⟨hZ', hz'⟩ => ?_
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by show s'.zf.map (!·) = _; rw [hz']; simp [hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by show s'.zf.map (!·) = _; rw [hz']; simp [hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The compression of the buffer. -/
theorem compress_buf (hd : VG.Proof.MdStream.X86.Dims P S) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.X86.Finalize.Pre P S s₀) {s : State} (hC : VG.Proof.MdStream.X86.Finalize.Common P S s₀ s)
    (heax : s.gpr .eax = VG.Proof.MdStream.X86.Finalize.st s₀ + BitVec.ofNat 32 P.N) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MdStream.X86.Finalize.Common P S s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      H.stateAt s'.mem (VG.Proof.MdStream.X86.Finalize.stA s₀) = H.compress (H.stateAt s.mem (VG.Proof.MdStream.X86.Finalize.stA s₀)) (H.blockAt s.mem (VG.Proof.MdStream.X86.Finalize.buf P s₀)) → Q s') :
    WP isa (compressAt name code .ebx .ebp) s Q := by
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hd_N := hd.N; have hd_so := hd.so; have hd_pos := hd.pos; have hd_le := hd.le
  have eN : Region.Sub ⟨VG.Proof.MdStream.X86.Finalize.stA s₀, P.N⟩ (VG.Proof.MdStream.X86.Finalize.stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.MdStream.X86.Finalize.scA s₀, P.so⟩ (VG.Proof.MdStream.X86.Finalize.scR S s₀) := Region.sub_prefix (by omega_using [hd.so])
  have hb : (VG.Proof.MdStream.X86.Finalize.st s₀ + BitVec.ofNat 32 P.N).setWidth 64 = VG.Proof.MdStream.X86.Finalize.stA s₀ + BitVec.ofNat 64 P.N := addr_eq (by omega)
  have eb : Region.Sub ⟨(VG.Proof.MdStream.X86.Finalize.st s₀ + BitVec.ofNat 32 P.N).setWidth 64, P.B⟩ (VG.Proof.MdStream.X86.Finalize.stR P s₀) := by
    rw [hb]; exact VG.Proof.MdStream.X86.sub_offset (by omega) (by omega)
  refine VG.Proof.MdStream.X86.compressAt_ok hf (st := VG.Proof.MdStream.X86.Finalize.st s₀) (scr := VG.Proof.MdStream.X86.Finalize.scr s₀) (blk := VG.Proof.MdStream.X86.Finalize.st s₀ + BitVec.ofNat 32 P.N) (E := VG.Proof.MdStream.X86.Finalize.esp₀ s₀)
    (by decide) (by decide) (by decide) (by decide) hC.esp hC.ebx hC.ebp heax hp.sp_lo (by omega)
    (by rw [BitVec.toNat_add, VG.Proof.MdStream.X86.toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (by omega)
    ((hp.st_scr.sub_left eN).sub_right eso) ?_ ((hp.st_scr.sub_left eb).sub_right eso)
    (hp.stk_st.sub_right eN) (hp.stk_scr.sub_right eso) (hp.stk_st.sub_right eb) ?_ ?_ ?_
  · rw [hb]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · rw [hC.rd, hC.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨VG.Proof.MdStream.X86.Finalize.stR P s₀, by simp, P.N, hb, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.MdStream.X86.Finalize.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.X86.Finalize.scR S s₀, by simp, 0, by simp, by simp; omega_using [hd.so]⟩
  · intro s' hrd hwr hcs hf hstate
    have cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := hcs
    have word : ∀ d, P.so ≤ d → d + 4 ≤ S →
        s'.mem.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) 32 = s.mem.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) 32 := by
      intro d h₁ h₂
      refine hf.readW (r := ⟨addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.st_scr.symm.sub_left (hp.scr_sub h₂)).sub_right eN
      · rw [addr_eq (by omega)]; exact Offset.disjoint_base _ (by omega) (by omega_using [h₂, hsc])
      · exact hp.stk_scr.symm.sub_left (hp.scr_sub h₂)
    refine hQ s' ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide)]; exact hC.ebx,
      by rw [cs _ (by decide)]; exact hC.ebp, by rw [cs _ (by decide)]; exact hC.esp,
      hC.frame.trans (hf.sub ?_), fun p hp' => ?_, by rw [word _ (by omega_using [hd.so]) (by omega_using [hd.so])]; exact hC.lo,
      by rw [word _ (by omega_using [hd.so]) (by omega_using [hd.so])]; exact hC.hi, by rw [word _ (by omega_using [hd.so]) (by omega_using [hd.so])]; exact hC.outp⟩
      hcs (by rw [hstate, hb])
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.MdStream.X86.Finalize.stR P s₀, by simp, eN⟩
      · exact ⟨VG.Proof.MdStream.X86.Finalize.scR S s₀, by simp, eso⟩
      · exact ⟨VG.Proof.MdStream.X86.Finalize.stkR s₀, by simp, fun _ h => h⟩
    · have hd' := VG.Proof.MdStream.X86.saved_offset hp'
      rw [word p.2 hd'.1 (by omega_using [hd', hd_so])]
      exact hC.saved p hp'

/-- Point `eax` at the buffer. -/
theorem args_ok {s₀ : State} {s : State} (hC : VG.Proof.MdStream.X86.Finalize.Common P S s₀ s) :
    WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 P.N))]) s fun s' =>
      VG.Proof.MdStream.X86.Finalize.Common P S s₀ s' ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.gpr .eax = VG.Proof.MdStream.X86.Finalize.st s₀ + BitVec.ofNat 32 P.N ∧
        s'.mem = s.mem := by
  refine VG.Proof.MdStream.X86.wp_mov fun s₁ u₁ => VG.Proof.MdStream.X86.wp_addi fun s₂ u₂ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r h => by rw [u₂.other r h, u₁.other r h]
  have hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨hC.of_gpr (fun r hr => g₂ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) hm
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]), g₂, by rw [u₂.gpr, u₁.gpr, hC.ebx], hm⟩

end

/-- The loop's postcondition for one iteration. -/
def Step {P : Params} (S : Nat) (H : Md P.B P.N P.L) (s₀ : State) (k : Nat) (s : State) : Prop :=
  (eval .e s = some false ∧ VG.Proof.MdStream.X86.Finalize.Done S H s₀ s) ∨ (eval .e s = some true ∧ k = 1 ∧ VG.Proof.MdStream.X86.Finalize.LInv S H s₀ 0 0 s)

theorem regs3 {r : Reg} (hr : r ∈ [Reg.ebx, .ebp, .esp]) : r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx ∧ r ≠ .edi ∧ r ≠ .esi := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> decide

section
variable {P : Params} {S : Nat} {H : Md P.B P.N P.L}

theorem body_ok (hd : VG.Proof.MdStream.X86.Dims P S) (hs : VG.Proof.MdStream.X86.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86.CalleeOk H code)
    {s₀ : State} (hp : VG.Proof.MdStream.X86.Finalize.Pre P S s₀) {k n : Nat} {s : State} (h : VG.Proof.MdStream.X86.Finalize.LInv S H s₀ k n s) :
    WP isa (finalizeBody P name code) s (VG.Proof.MdStream.X86.Finalize.Step S H s₀ k) := by
  have hk := h.k_le; have hn := h.n_le; have hst := hp.st_fit; have hd_N := hd.N; have hd_so := hd.so; have hd_S := hd.S
  have hd_ge := hd.ge; have hd_le := hd.le; have hd_L := hd.L; have := VG.Proof.MdStream.X86.Finalize.lim_le P k; have := VG.Proof.MdStream.X86.Finalize.lim_ge P k
  have hC := h.toCommon
  unfold finalizeBody
  -- `eax := B` or `B - L`: the end of the zeros.
  refine WP.seq (VG.Proof.MdStream.X86.wp_movi fun s₁ u₁ => VG.Proof.MdStream.X86.wp_test fun s₂ f₂ z₂ => WP.block_nil ?_)
  have hz₂ : s₂.zf = some (decide (k = 0)) := by
    rw [z₂, u₁.other _ (by decide), h.esi, BitVec.and_self, VG.Proof.MdStream.X86.ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .eax = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Finalize.lim P k) ∧
      (∀ r, r ≠ .eax → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr) ?_
    fun s₃ ⟨heax₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show s₂.zf = _; rw [hz₂]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine VG.Proof.MdStream.X86.wp_movi fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr]; rfl, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [u₃.other r hr, f₂.gpr, u₁.other r hr]
      · rw [u₃.mem, f₂.mem, u₁.mem]
      · rw [u₃.rd, f₂.rd, u₁.rd]
      · rw [u₃.wr, f₂.wr, u₁.wr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [f₂.gpr, u₁.gpr, show k = 1 by omega]; rfl, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [f₂.gpr, u₁.other r hr]
      · rw [f₂.mem, u₁.mem]
      · rw [f₂.rd, u₁.rd]
      · rw [f₂.wr, u₁.wr]
  -- `ecx := 0; eax -= edi`: zero the rest of the buffer, up to `lim`.
  have hC₃ : VG.Proof.MdStream.X86.Finalize.Common P S s₀ s₃ := hC.of_gpr (fun r hr => g₃ r (VG.Proof.MdStream.X86.Finalize.regs3 hr).1) m₃ rd₃ wr₃
  refine WP.seq (VG.Proof.MdStream.X86.wp_movi fun s₄ u₄ => VG.Proof.MdStream.X86.wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  have hC₄ : VG.Proof.MdStream.X86.Finalize.Common P S s₀ s₄ := hC₃.of_gpr (fun r hr => u₄.other r (VG.Proof.MdStream.X86.Finalize.regs3 hr).2.1) u₄.mem u₄.rd u₄.wr
  have hecx₄ : s₄.gpr .ecx = 0 := u₄.gpr
  have hedi₄ : s₄.gpr .edi = BitVec.ofNat 32 n := by rw [u₄.other _ (by decide), g₃ _ (by decide), h.edi]
  have heax₅ : s₅.gpr .eax = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Finalize.lim P k - n) := by
    rw [u₅.gpr, u₄.other _ (by decide), heax₃, hedi₄, VG.Proof.MdStream.X86.sub_ofNat (a := VG.Proof.MdStream.X86.Finalize.lim P k) (b := n) (by omega)]
  have hZ : VG.Proof.MdStream.X86.Finalize.Zero P s₀ s₄ n (VG.Proof.MdStream.X86.Finalize.lim P k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => u₅.other r ?_, u₅.rd, u₅.wr,
      by rw [u₅.other _ (by decide), hedi₄, Nat.add_zero], by rw [heax₅, Nat.sub_zero],
      by rw [u₅.mem, List.replicate_zero, VG.WriteBytes.writeBytes_nil]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  have hz₅ : s₅.zf = some (decide (VG.Proof.MdStream.X86.Finalize.lim P k - n = 0)) := by
    rw [z₅, ← u₅.gpr, heax₅, VG.Proof.MdStream.X86.ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (VG.Proof.MdStream.X86.Finalize.zero_ok hd hp hC₄ hecx₄ (by omega) hn hZ hz₅) fun s₆ hZ₆ => ?_)
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃]
  have hf₆ : Frame [VG.Proof.MdStream.X86.Finalize.stR P s₀] s₄.mem s₆.mem := by
    rw [hZ₆.mem]; exact VG.Proof.MdStream.X86.Finalize.buf_frame hd _ (by simp only [List.length_replicate]; omega)
  obtain ⟨hfr₆, hsv₆, hlo₆, hhi₆, hout₆⟩ := hC₄.frame_keep hd hp (hf₆.mono (by simp))
  have hC₆ : VG.Proof.MdStream.X86.Finalize.Common P S s₀ s₆ := ⟨hZ₆.rd.trans hC₄.rd, hZ₆.wr.trans hC₄.wr, by rw [hZ₆.keep _ (by simp), hC₄.ebx],
    by rw [hZ₆.keep _ (by simp), hC₄.ebp], by rw [hZ₆.keep _ (by simp), hC₄.esp], hfr₆, hsv₆, hlo₆, hhi₆, hout₆⟩
  have hst₆ : H.stateAt s₆.mem (VG.Proof.MdStream.X86.Finalize.stA s₀) = H.stateAt s.mem (VG.Proof.MdStream.X86.Finalize.stA s₀) := by
    rw [hZ₆.mem, hm₄]
    apply H.stateAt_congr
    intro i hi
    rw [VG.Proof.MdStream.X86.Finalize.buf_add]
    exact VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (VG.Proof.MdStream.X86.Finalize.buf P s₀) (VG.Proof.MdStream.X86.Finalize.lim P k) =
      bytesAt s.mem (VG.Proof.MdStream.X86.Finalize.buf P s₀) n ++ List.replicate (VG.Proof.MdStream.X86.Finalize.lim P k - n) 0 := by
    rw [hZ₆.mem, hm₄, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega_using [hn]
  have hesi₆ : s₆.gpr .esi = BitVec.ofNat 32 k := by
    rw [hZ₆.keep _ (by simp), u₄.other _ (by decide), g₃ _ (by decide), h.esi]
  -- In the last block, the length field.
  refine WP.seq (VG.Proof.MdStream.X86.wp_test fun s₇ f₇ z₇ => WP.block_nil ?_)
  have hC₇ : VG.Proof.MdStream.X86.Finalize.Common P S s₀ s₇ := hC₆.of_gpr (fun r _ => by rw [f₇.gpr]) f₇.mem f₇.rd f₇.wr
  have hz₇ : s₇.zf = some (decide (k = 0)) := by
    rw [z₇, hesi₆, BitVec.and_self, VG.Proof.MdStream.X86.ofNat_beq_zero (by omega)]
  have hesi₇ : s₇.gpr .esi = BitVec.ofNat 32 k := by rw [f₇.gpr, hesi₆]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => VG.Proof.MdStream.X86.Finalize.Common P S s₀ s₈ ∧ s₈.gpr .esi = BitVec.ofNat 32 k ∧
      H.stateAt s₈.mem (VG.Proof.MdStream.X86.Finalize.stA s₀) = H.stateAt s.mem (VG.Proof.MdStream.X86.Finalize.stA s₀) ∧
      ∀ iv m, VG.Proof.MdStream.X86.Finalize.R₀ H s₀ iv m → H.lenOk m.length → bytesAt s₈.mem (VG.Proof.MdStream.X86.Finalize.buf P s₀) P.B = bytesAt s.mem (VG.Proof.MdStream.X86.Finalize.buf P s₀) n ++
        (if k = 1 then List.replicate (P.B - n) 0 else List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)) ?_
    fun s₈ ⟨hC₈, hesi₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by show s₇.zf = _; rw [hz₇]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      rw [VG.Proof.MdStream.X86.Finalize.lim_zero] at hby₆
      have hsc₇ : ∀ d, d + 4 ≤ S → InRegions (s₇.rd ++ s₇.wr) (addr (s₇.gpr .ebp) d) 4 :=
        fun d hd => ⟨VG.Proof.MdStream.X86.Finalize.scR S s₀, by simp [hC₇.rd, hC₇.wr, hp.wr], by rw [hC₇.ebp]; exact hp.scr_in hd⟩
      have hso₇ : ∀ d, d + 4 ≤ P.N + P.B → InRegions s₇.wr (addr (s₇.gpr .ebx) d) 4 :=
        fun d hd => ⟨VG.Proof.MdStream.X86.Finalize.stR P s₀, by simp [hC₇.wr, hp.wr], by rw [hC₇.ebx]; exact VG.Proof.MdStream.X86.contains_addr hd (by decide) hst⟩
      refine WP.mono (hs.len s₇ (by rw [hC₇.ebx]; exact hst) (hsc₇ _ (by omega_using [hd.so])) (hsc₇ _ (by omega_using [hd.so]))
        fun d _ h₂ => hso₇ d h₂) fun s₈ ⟨g₈, rd₈, wr₈, m₈⟩ => ?_
      rw [hC₇.ebx, hC₇.ebp, hC₇.lo, hC₇.hi, show P.N + P.B - P.L = P.N + (P.B - P.L) by omega, ← VG.Proof.MdStream.X86.Finalize.buf_add] at m₈
      have hlen := H.lenOf_length (VG.X86.arg s₀ 2 ++ VG.X86.arg s₀ 1)
      have hfL : Frame [VG.Proof.MdStream.X86.Finalize.stR P s₀] s₇.mem s₈.mem := by
        rw [m₈]; exact VG.Proof.MdStream.X86.Finalize.buf_frame hd _ (by omega_using [hlen, hd_L, hd_ge])
      obtain ⟨hfr, hsv, hlo, hhi, hout⟩ := hC₇.frame_keep hd hp (hfL.mono (by simp))
      refine ⟨⟨rd₈.trans hC₇.rd, wr₈.trans hC₇.wr, by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.ebx],
        by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.ebp],
        by rw [g₈ _ (by decide) (by decide) (by decide), hC₇.esp], hfr, hsv, hlo, hhi, hout⟩,
        by rw [g₈ _ (by decide) (by decide) (by decide), hesi₇], ?_, fun iv m hm hok => ?_⟩
      · rw [m₈, ← hst₆, ← f₇.mem]
        apply H.stateAt_congr
        intro i hi
        rw [VG.Proof.MdStream.X86.Finalize.buf_add]
        exact VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by omega)
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        rw [show VG.X86.arg s₀ 2 ++ VG.X86.arg s₀ 1 = VG.Proof.MdStream.X86.count s₀ from rfl, hm.2, H.lenOf_eq _ hok] at m₈
        have e := bytesAt_writeBytes s₇.mem (VG.Proof.MdStream.X86.Finalize.buf P s₀) (P.B - P.L) (H.lenBytes m.length)
          (by rw [H.lenBytes_length]; omega)
        rw [H.lenBytes_length, show P.B - P.L + P.L = P.B by omega_using [hd_L, hd_ge]] at e
        rw [m₈, e, f₇.mem, hby₆, List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₇, hesi₇, by rw [f₇.mem, hst₆], fun iv m _ _ => ?_⟩
      rw [VG.Proof.MdStream.X86.Finalize.lim_one] at hby₆
      rw [f₇.mem, hby₆]; simp
  -- Compress the block.
  refine WP.seq (WP.mono (VG.Proof.MdStream.X86.Finalize.args_ok hC₈) fun s₉ ⟨hC₉, g₉, heax₉, hm₉⟩ => ?_)
  refine WP.seq (VG.Proof.MdStream.X86.Finalize.compress_buf hd hf hp hC₉ heax₉ fun s₁₀ hC₁₀ cs₁₀ hst₁₀ => ?_)
  have hesi₁₀ : s₁₀.gpr .esi = BitVec.ofNat 32 k := by
    rw [cs₁₀ _ (by decide), g₉ _ (by decide), hesi₈]
  have hblk : ∀ iv m, VG.Proof.MdStream.X86.Finalize.R₀ H s₀ iv m → H.lenOk m.length → H.blockAt s₉.mem (VG.Proof.MdStream.X86.Finalize.buf P s₀) = H.parse fun t =>
      (bytesAt s.mem (VG.Proof.MdStream.X86.Finalize.buf P s₀) n ++
        (if k = 1 then List.replicate (P.B - n) 0 else List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)).getD t 0 := by
    intro iv m hm hok
    apply H.parse_congr
    intro t ht
    rw [hm₉]
    exact VG.Proof.MdStream.X86.bytesAt_getD (hby₈ iv m hm hok) ht
  -- Next block, if any.
  refine VG.Proof.MdStream.X86.wp_movi fun s₁₁ u₁₁ => VG.Proof.MdStream.X86.wp_subi fun s₁₂ u₁₂ z₁₂ => WP.block_nil ?_
  have hC₁₂ : VG.Proof.MdStream.X86.Finalize.Common P S s₀ s₁₂ := hC₁₀.of_gpr (fun r hr => by
      rw [u₁₂.other r (VG.Proof.MdStream.X86.Finalize.regs3 hr).2.2.2.2, u₁₁.other r (VG.Proof.MdStream.X86.Finalize.regs3 hr).2.2.2.1]) (by rw [u₁₂.mem, u₁₁.mem])
    (by rw [u₁₂.rd, u₁₁.rd]) (by rw [u₁₂.wr, u₁₁.wr])
  have hz : s₁₂.zf = some (decide (k = 1)) := by
    rw [z₁₂, u₁₁.other _ (by decide), hesi₁₀, VG.Proof.MdStream.X86.lit32 1, VG.Proof.MdStream.X86.sub_beq (a := k) (b := 1) (by omega) (by decide)]
  have hst : ∀ iv m, VG.Proof.MdStream.X86.Finalize.R₀ H s₀ iv m → H.lenOk m.length →
      H.stateAt s₁₂.mem (VG.Proof.MdStream.X86.Finalize.stA s₀) = H.compress (H.stateAt s.mem (VG.Proof.MdStream.X86.Finalize.stA s₀)) (H.parse fun t =>
        (bytesAt s.mem (VG.Proof.MdStream.X86.Finalize.buf P s₀) n ++
          (if k = 1 then List.replicate (P.B - n) 0 else List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)).getD t 0) := by
    intro iv m hm hok
    rw [u₁₂.mem, u₁₁.mem, hst₁₀, hm₉, hst₈, ← hblk iv m hm hok, hm₉]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨by show s₁₂.zf = _; rw [hz]; rfl, rfl, ⟨hC₁₂, by decide, by omega, ?_, ?_, fun iv m hm hok => ?_⟩⟩
    · rw [u₁₂.other _ (by decide), u₁₁.gpr]; rfl
    · rw [u₁₂.gpr, u₁₁.other _ (by decide), hesi₁₀]; rfl
    · rw [h.hash iv m hm hok]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, VG.Proof.MdStream.X86.Finalize.Fin1, VG.Proof.MdStream.X86.Finalize.Fin0, hst iv m hm hok]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨by show s₁₂.zf = _; rw [hz]; rfl, hC₁₂, fun iv m hm hok => ?_⟩
    rw [h.hash iv m hm hok, hst iv m hm hok]
    simp only [show ¬ (0 = 1) by decide, ite_false, VG.Proof.MdStream.X86.Finalize.Fin0, List.append_assoc]

/-! ## Prologue -/

/-- The memory after saving our caller's registers and copying `count` and `out` to scratch. -/
def proMem (P : Params) (s₀ : State) : Mem :=
  ((((((s₀.mem.writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) P.so) (s₀.gpr .ebx)).writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 4))
    (s₀.gpr .esi)).writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 8)) (s₀.gpr .edi)).writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 12))
    (s₀.gpr .ebp)).writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 16)) (VG.X86.arg s₀ 1)).writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 20))
    (VG.X86.arg s₀ 2)).writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 24)) (VG.Proof.MdStream.X86.Finalize.out s₀)

theorem proMem_frame (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Finalize.Pre P S s₀) : Frame [VG.Proof.MdStream.X86.Finalize.scR S s₀] s₀.mem (VG.Proof.MdStream.X86.Finalize.proMem P s₀) := by
  have hd_so := hd.so
  have c : ∀ d, d + 4 ≤ S → (VG.Proof.MdStream.X86.Finalize.scR S s₀).Contains (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) (32 / 8) := fun d hd => hp.scr_in hd
  simp only [VG.Proof.MdStream.X86.Finalize.proMem]
  exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c P.so (by omega_using [hd.so]))).writeW
    (List.mem_singleton_self _) _ (c (P.so + 4) (by omega_using [hd.so]))).writeW (List.mem_singleton_self _) _
    (c (P.so + 8) (by omega_using [hd.so]))).writeW (List.mem_singleton_self _) _ (c (P.so + 12) (by omega_using [hd.so]))).writeW
    (List.mem_singleton_self _) _ (c (P.so + 16) (by omega_using [hd.so]))).writeW (List.mem_singleton_self _) _
    (c (P.so + 20) (by omega_using [hd.so]))).writeW (List.mem_singleton_self _) _ (c (P.so + 24) (by omega_using [hd.so]))

theorem proMem_words (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Finalize.Pre P S s₀) :
    VG.Proof.MdStream.X86.Finalize.Saved P s₀ (VG.Proof.MdStream.X86.Finalize.proMem P s₀) ∧ (VG.Proof.MdStream.X86.Finalize.proMem P s₀).readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 16)) 32 = VG.X86.arg s₀ 1 ∧
      (VG.Proof.MdStream.X86.Finalize.proMem P s₀).readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 20)) 32 = VG.X86.arg s₀ 2 ∧
      (VG.Proof.MdStream.X86.Finalize.proMem P s₀).readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 24)) 32 = VG.Proof.MdStream.X86.Finalize.out s₀ := by
  have hs := hp.scr_fit; have hd_so := hd.so
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ S → e + 4 ≤ S → d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) e) v).readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) 32 = m.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) 32 :=
    fun m v d e h₁ h₂ h => VG.Proof.MdStream.X86.readW_writeW_addr m v (by omega) (by omega) h
  refine ⟨fun p hp' => ?_, ?_, ?_, ?_⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp only [VG.Proof.MdStream.X86.Finalize.proMem] <;>
      rw [w _ _ _ (P.so + 24) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]), w _ _ _ (P.so + 20) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]),
        w _ _ _ (P.so + 16) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so])]
    · rw [w _ _ P.so (P.so + 12) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]),
        w _ _ P.so (P.so + 8) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]),
        w _ _ P.so (P.so + 4) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]), Mem.readW_writeW_self32]
    · rw [w _ _ (P.so + 4) (P.so + 12) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]),
        w _ _ (P.so + 4) (P.so + 8) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]), Mem.readW_writeW_self32]
    · rw [w _ _ (P.so + 8) (P.so + 12) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]), Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_self32]
  · simp only [VG.Proof.MdStream.X86.Finalize.proMem]
    rw [w _ _ (P.so + 16) (P.so + 24) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]),
      w _ _ (P.so + 16) (P.so + 20) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]), Mem.readW_writeW_self32]
  · simp only [VG.Proof.MdStream.X86.Finalize.proMem]
    rw [w _ _ (P.so + 20) (P.so + 24) (by omega_using [hd.so]) (by omega_using [hd.so]) (by omega_using [hd.so]), Mem.readW_writeW_self32]
  · simp only [VG.Proof.MdStream.X86.Finalize.proMem]; rw [Mem.readW_writeW_self32]

/-- The arguments, in memory that differs only in the scratch space. -/
theorem arg_read {s₀ : State} (hp : VG.Proof.MdStream.X86.Finalize.Pre P S s₀) {m : Mem} (hf : Frame [VG.Proof.MdStream.X86.Finalize.scR S s₀] s₀.mem m) {e : Nat}
    (h₁ : 4 ≤ e) (h₂ : e + 4 ≤ 24) : m.readW (addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) e) 32 = s₀.mem.readW (addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) e) 32 :=
  hf.readW (Region.contains_self _ _) (by simpa using hp.a_scr.sub_left (hp.arg_sub h₁ h₂)) (by decide)

theorem prologue_ok (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Finalize.Pre P S s₀) :
    WP isa (.seq (.block (([.mov .eax (.mem (at_ .esp 20))] : List Instr) ++ save P .eax ++
      ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
       .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp (P.so + 16)) .ecx,
       .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp (P.so + 20)) .ecx,
       .mov .ecx (.mem (at_ .esp 16)), .store (at_ .ebp (P.so + 24)) .ecx,
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm (BitVec.ofNat 32 (P.B - 1))),
       .mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .edx P.N) .cl, .alu .add .edi (.imm 1),
       .mov .esi (.imm 0), .alu .cmp .edi (.imm (BitVec.ofNat 32 (P.B - P.L + 1)))] : List Instr)))
      (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))) s₀
      fun s => ∃ k, VG.Proof.MdStream.X86.Finalize.LInv S H s₀ k (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B + 1) s := by
  have hst := hp.st_fit; have hd_so := hd.so; have hd_N := hd.N; have hd_ge := hd.ge; have hd_le := hd.le; have hd_L := hd.L
  have hr : VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B < P.B := Nat.mod_lt _ hd.pos
  have ain : ∀ e, 4 ≤ e → e + 4 ≤ 24 → ∀ t : State, t.rd = s₀.rd → t.wr = s₀.wr →
      InRegions (t.rd ++ t.wr) (addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) e) 4 :=
    fun e h₁ h₂ t hrd hwr => ⟨VG.Proof.MdStream.X86.Finalize.argR s₀, by simp [hrd, hwr, hp.rd], hp.arg_in h₁ h₂⟩
  have sout : ∀ d, d + 4 ≤ S → ∀ t : State, t.wr = s₀.wr → InRegions t.wr (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) 4 :=
    fun d hd t hwr => ⟨VG.Proof.MdStream.X86.Finalize.scR S s₀, by simp [hwr, hp.wr], hp.scr_in hd⟩
  have fw : ∀ {m : Mem}, Frame [VG.Proof.MdStream.X86.Finalize.scR S s₀] s₀.mem m → ∀ d, d + 4 ≤ S → ∀ v : BitVec 32,
      Frame [VG.Proof.MdStream.X86.Finalize.scR S s₀] s₀.mem (m.writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) v) :=
    fun hf d hd v => hf.writeW (List.mem_singleton_self _) _ (hp.scr_in hd)
  simp only [List.cons_append, VG.Proof.MdStream.X86.save_eq, List.nil_append]
  refine WP.seq ?_
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) 20) (VG.Proof.MdStream.X86.ea_at _ _ _) (ain 20 (by decide) (by decide) s₀ rfl rfl) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = VG.Proof.MdStream.X86.Finalize.scr s₀ := u₁.gpr
  refine VG.Proof.MdStream.X86.wp_store (a := addr (VG.Proof.MdStream.X86.Finalize.scr s₀) P.so) (by rw [VG.Proof.MdStream.X86.ea_at, e₁]) (sout P.so (by omega_using [hd.so]) _ u₁.wr) fun s₂ u₂ => ?_
  refine VG.Proof.MdStream.X86.wp_store (a := addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 4)) (by rw [VG.Proof.MdStream.X86.ea_at, u₂.gpr, e₁])
    (sout (P.so + 4) (by omega_using [hd.so]) _ (by rw [u₂.wr, u₁.wr])) fun s₃ u₃ => ?_
  refine VG.Proof.MdStream.X86.wp_store (a := addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 8)) (by rw [VG.Proof.MdStream.X86.ea_at, u₃.gpr, u₂.gpr, e₁])
    (sout (P.so + 8) (by omega_using [hd.so]) _ (by rw [u₃.wr, u₂.wr, u₁.wr])) fun s₄ u₄ => ?_
  refine VG.Proof.MdStream.X86.wp_store (a := addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 12)) (by rw [VG.Proof.MdStream.X86.ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (sout (P.so + 12) (by omega_using [hd.so]) _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = VG.Proof.MdStream.X86.Finalize.esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  have m₅ : s₅.mem = (((s₀.mem.writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) P.so) (s₀.gpr .ebx)).writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 4))
      (s₀.gpr .esi)).writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 8)) (s₀.gpr .edi)).writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 12))
      (s₀.gpr .ebp) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
  have f₅ : Frame [VG.Proof.MdStream.X86.Finalize.scR S s₀] s₀.mem s₅.mem := by
    rw [m₅]; exact fw (fw (fw (fw (Frame.refl _ _) P.so (by omega_using [hd.so]) _) (P.so + 4) (by omega_using [hd.so]) _) (P.so + 8)
      (by omega_using [hd.so]) _) (P.so + 12) (by omega_using [hd.so]) _
  refine VG.Proof.MdStream.X86.wp_mov fun s₆ u₆ => VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) 4) (by rw [VG.Proof.MdStream.X86.ea_at, u₆.other _ (by decide), sp₅])
    (ain 4 (by decide) (by decide) s₆ (by rw [u₆.rd, rd₅]) (by rw [u₆.wr, wr₅])) fun s₇ u₇ => ?_
  have ebp₇ : s₇.gpr .ebp = VG.Proof.MdStream.X86.Finalize.scr s₀ := by rw [u₇.other _ (by decide), u₆.gpr, g₅, e₁]
  have sp₇ : s₇.gpr .esp = VG.Proof.MdStream.X86.Finalize.esp₀ s₀ := by rw [u₇.other _ (by decide), u₆.other _ (by decide), sp₅]
  have ebx₇ : s₇.gpr .ebx = VG.Proof.MdStream.X86.Finalize.st s₀ := by
    rw [u₇.gpr, u₆.mem, VG.Proof.MdStream.X86.Finalize.arg_read hp f₅ (by decide) (by decide)]; rfl
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, rd₅]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, wr₅]
  have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  -- `count` and `out` into scratch.
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) 8) (by rw [VG.Proof.MdStream.X86.ea_at, sp₇]) (ain 8 (by decide) (by decide) s₇ rd₇ wr₇)
    fun s₈ u₈ => ?_
  refine VG.Proof.MdStream.X86.wp_store (a := addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 16)) (by rw [VG.Proof.MdStream.X86.ea_at, u₈.other _ (by decide), ebp₇])
    (sout (P.so + 16) (by omega_using [hd.so]) _ (by rw [u₈.wr, wr₇])) fun s₉ u₉ => ?_
  have v₉ : s₉.mem = s₅.mem.writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 16)) (VG.X86.arg s₀ 1) := by
    rw [u₉.mem, u₈.gpr, u₈.mem, m₇, VG.Proof.MdStream.X86.Finalize.arg_read hp f₅ (by decide) (by decide)]; rfl
  have f₉ : Frame [VG.Proof.MdStream.X86.Finalize.scR S s₀] s₀.mem s₉.mem := by rw [v₉]; exact fw f₅ (P.so + 16) (by omega_using [hd.so]) _
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) 12) (by rw [VG.Proof.MdStream.X86.ea_at, u₉.gpr, u₈.other _ (by decide), sp₇])
    (ain 12 (by decide) (by decide) _ (by rw [u₉.rd, u₈.rd, rd₇]) (by rw [u₉.wr, u₈.wr, wr₇])) fun s₁₀ u₁₀ => ?_
  refine VG.Proof.MdStream.X86.wp_store (a := addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 20)) (by rw [VG.Proof.MdStream.X86.ea_at, u₁₀.other _ (by decide), u₉.gpr,
                                                         u₈.other _ (by decide), ebp₇]) (sout (P.so + 20) (by omega_using [hd.so]) _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, wr₇]))
    fun s₁₁ u₁₁ => ?_
  have v₁₁ : s₁₁.mem = s₉.mem.writeW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 20)) (VG.X86.arg s₀ 2) := by
    rw [u₁₁.mem, u₁₀.gpr, u₁₀.mem, VG.Proof.MdStream.X86.Finalize.arg_read hp f₉ (by decide) (by decide)]; rfl
  have f₁₁ : Frame [VG.Proof.MdStream.X86.Finalize.scR S s₀] s₀.mem s₁₁.mem := by rw [v₁₁]; exact fw f₉ (P.so + 20) (by omega_using [hd.so]) _
  have g₁₁ : ∀ r, r ≠ .ecx → s₁₁.gpr r = s₇.gpr r := fun r h => by
    rw [u₁₁.gpr, u₁₀.other r h, u₉.gpr, u₈.other r h]
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) 16) (by rw [VG.Proof.MdStream.X86.ea_at, g₁₁ _ (by decide), sp₇])
    (ain 16 (by decide) (by decide) _ (by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇])
      (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇])) fun s₁₂ u₁₂ => ?_
  refine VG.Proof.MdStream.X86.wp_store (a := addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 24)) (by rw [VG.Proof.MdStream.X86.ea_at, u₁₂.other _ (by decide), g₁₁ _ (by decide),
                                                         ebp₇]) (sout (P.so + 24) (by omega_using [hd.so]) _ (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇])) fun s₁₃ u₁₃ => ?_
  have m₁₃ : s₁₃.mem = VG.Proof.MdStream.X86.Finalize.proMem P s₀ := by
    rw [u₁₃.mem, u₁₂.gpr, u₁₂.mem, VG.Proof.MdStream.X86.Finalize.arg_read hp f₁₁ (by decide) (by decide), v₁₁, v₉, m₅]; rfl
  have g₁₃ : ∀ r, r ≠ .ecx → s₁₃.gpr r = s₇.gpr r := fun r h => by rw [u₁₃.gpr, u₁₂.other r h, g₁₁ r h]
  have rd₁₃ : s₁₃.rd = s₀.rd := by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇]
  -- The `0x80` byte.
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Finalize.esp₀ s₀) 8) (by rw [VG.Proof.MdStream.X86.ea_at, g₁₃ _ (by decide), sp₇])
    (ain 8 (by decide) (by decide) _ rd₁₃ wr₁₃) fun s₁₄ u₁₄ => VG.Proof.MdStream.X86.wp_andi fun s₁₅ u₁₅ => ?_
  have edi₁₅ : s₁₅.gpr .edi = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B) := by
    rw [u₁₅.gpr, u₁₄.gpr, m₁₃, VG.Proof.MdStream.X86.Finalize.arg_read hp (VG.Proof.MdStream.X86.Finalize.proMem_frame hd hp) (by decide) (by decide), hd.and, VG.Proof.MdStream.X86.Finalize.cnt_mod hd]
    rfl
  refine VG.Proof.MdStream.X86.wp_mov fun s₁₆ u₁₆ => VG.Proof.MdStream.X86.wp_add fun s₁₇ u₁₇ => VG.Proof.MdStream.X86.wp_movi fun s₁₈ u₁₈ => ?_
  have edx₁₈ : s₁₈.gpr .edx = VG.Proof.MdStream.X86.Finalize.st s₀ + BitVec.ofNat 32 (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B) := by
    rw [u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.gpr, u₁₆.other _ (by decide), edi₁₅, u₁₅.other _ (by decide),
      u₁₄.other _ (by decide), g₁₃ _ (by decide), ebx₇]
  have hq : addr (s₁₈.gpr .edx) P.N = VG.Proof.MdStream.X86.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B) := by
    rw [edx₁₈, VG.Proof.MdStream.X86.addr_add_ofNat (by omega), VG.Proof.MdStream.X86.Finalize.buf_add, Nat.add_comm]
  have hout : InRegions s₁₈.wr (VG.Proof.MdStream.X86.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B)) 1 :=
    ⟨VG.Proof.MdStream.X86.Finalize.stR P s₀, by simp [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, wr₁₃, hp.wr], by
      rw [VG.Proof.MdStream.X86.Finalize.buf_add]; exact VG.Proof.MdStream.X86.contains_offset (by omega) (by omega)⟩
  refine VG.Proof.MdStream.X86.wp_store8 (r := .cl) (a := VG.Proof.MdStream.X86.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B)) (by rw [VG.Proof.MdStream.X86.ea_at, hq]) hout
    fun s₁₉ u₁₉ => VG.Proof.MdStream.X86.wp_addi fun s₂₀ u₂₀ => VG.Proof.MdStream.X86.wp_movi fun s₂₁ u₂₁ => VG.Proof.MdStream.X86.wp_cmpi fun s₂₂ f₂₂ cf₂₂ _ => WP.block_nil ?_
  have hm₁₉ : s₁₉.mem = VG.WriteBytes.writeBytes (VG.Proof.MdStream.X86.Finalize.proMem P s₀) (VG.Proof.MdStream.X86.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B)) [0x80] := by
    rw [u₁₉.mem, show Reg8.cl.reg = Reg.ecx from rfl, u₁₈.gpr, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem, m₁₃,
      ← List.nil_append [(0x80 : Byte)], VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp), VG.WriteBytes.writeBytes_nil]
    simp
  have hm₂₂ : s₂₂.mem = s₁₉.mem := by rw [f₂₂.mem, u₂₁.mem, u₂₀.mem]
  have hfb : Frame [VG.Proof.MdStream.X86.Finalize.stR P s₀] (VG.Proof.MdStream.X86.Finalize.proMem P s₀) s₁₉.mem := by rw [hm₁₉]; exact VG.Proof.MdStream.X86.Finalize.buf_frame hd _ (by simp; omega)
  have keep : ∀ r, r ≠ .ecx → r ≠ .edi → r ≠ .edx → r ≠ .esi → s₂₂.gpr r = s₇.gpr r := fun r h1 h2 h3 h4 => by
    rw [f₂₂.gpr, u₂₁.other r h4, u₂₀.other r h2, u₁₉.gpr, u₁₈.other r h1, u₁₇.other r h3, u₁₆.other r h3,
      u₁₅.other r h2, u₁₄.other r h2, g₁₃ r h1]
  obtain ⟨hsv, hlo, hhi, hou⟩ := VG.Proof.MdStream.X86.Finalize.proMem_words hd hp
  have word : ∀ d, d + 4 ≤ S → s₂₂.mem.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) 32 = (VG.Proof.MdStream.X86.Finalize.proMem P s₀).readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) 32 :=
    fun d hd => by
      rw [hm₂₂]
      exact hfb.readW (Region.contains_self _ _) (by simpa using hp.st_scr.symm.sub_left (hp.scr_sub hd))
        (by decide)
  have hC : VG.Proof.MdStream.X86.Finalize.Common P S s₀ s₂₂ :=
    ⟨by rw [f₂₂.rd, u₂₁.rd, u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, rd₁₃],
      by rw [f₂₂.wr, u₂₁.wr, u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, wr₁₃],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), ebx₇],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), ebp₇],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), sp₇],
      by rw [hm₂₂]; exact ((VG.Proof.MdStream.X86.Finalize.proMem_frame hd hp).mono (by simp)).trans (hfb.mono (by simp)),
      fun p hp' => by
        have hd' := VG.Proof.MdStream.X86.saved_offset hp'
        rw [word _ (by omega)]; exact hsv p hp',
      by rw [word _ (by omega_using [hd.so])]; exact hlo, by rw [word _ (by omega_using [hd.so])]; exact hhi,
      by rw [word _ (by omega_using [hd.so])]; exact hou⟩
  have edi₂₂ : s₂₂.gpr .edi = BitVec.ofNat 32 (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B + 1) := by
    rw [f₂₂.gpr, u₂₁.other _ (by decide), u₂₀.gpr, u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), edi₁₅, VG.Proof.MdStream.X86.ofNat_succ]
  have hcf : s₂₂.cf = some (decide (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B + 1 < P.B - P.L + 1)) := by
    rw [cf₂₂, ← f₂₂.gpr, edi₂₂, VG.Proof.MdStream.X86.toNat_ofNat_lt (k := VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B + 1) (by omega),
      VG.Proof.MdStream.X86.toNat_ofNat_lt (k := P.B - P.L + 1) (by omega_using [hd_le])]
  -- The facts about the buffer.
  have hst' : H.stateAt s₂₂.mem (VG.Proof.MdStream.X86.Finalize.stA s₀) = H.stateAt s₀.mem (VG.Proof.MdStream.X86.Finalize.stA s₀) := by
    apply H.stateAt_congr
    intro i hi
    rw [hm₂₂, hm₁₉, VG.Proof.MdStream.X86.Finalize.buf_add, VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by simp; omega)]
    exact VG.Proof.MdStream.X86.frame_bytes (VG.Proof.MdStream.X86.Finalize.proMem_frame hd hp) (R := VG.Proof.MdStream.X86.Finalize.stR P s₀) (by simpa using hp.st_scr) (by simp; omega)
      (by show i < P.N + P.B; omega_using [hi])
  have hbytes : ∀ iv m, VG.Proof.MdStream.X86.Finalize.R₀ H s₀ iv m →
      bytesAt s₂₂.mem (VG.Proof.MdStream.X86.Finalize.buf P s₀) (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B + 1) = MdStream.Md.rest P.B m ++ [0x80] := by
    intro iv m hm
    have e := bytesAt_writeBytes (VG.Proof.MdStream.X86.Finalize.proMem P s₀) (VG.Proof.MdStream.X86.Finalize.buf P s₀) (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₂₂, hm₁₉, e]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length hd]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    rw [VG.Proof.MdStream.X86.Finalize.buf_add]
    exact VG.Proof.MdStream.X86.frame_bytes (VG.Proof.MdStream.X86.Finalize.proMem_frame hd hp) (R := VG.Proof.MdStream.X86.Finalize.stR P s₀) (by simpa using hp.st_scr) (by simp; omega)
      (by show P.N + i < P.N + P.B; have hm_length := hm.length hd; omega)
  have hesi : s₂₂.gpr .esi = 0 := by rw [f₂₂.gpr, u₂₁.gpr]
  refine WP.ite (!decide (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B + 1 < P.B - P.L + 1)) (by show s₂₂.cf.map (!·) = _; rw [hcf]; rfl)
    (fun hb => ?_) (fun hb => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb
    refine VG.Proof.MdStream.X86.wp_movi fun s₂₃ u₂₃ => WP.block_nil ⟨1, hC.of_gpr (fun r hr => u₂₃.other r (VG.Proof.MdStream.X86.Finalize.regs3 hr).2.2.2.2)
      u₂₃.mem u₂₃.rd u₂₃.wr, (Nat.le_refl _), by rw [VG.Proof.MdStream.X86.Finalize.lim_one]; omega, by rw [u₂₃.other _ (by decide), edi₂₂], by rw [u₂₃.gpr]; rfl,
      fun iv m hm _ => ?_⟩
    simp only [↓reduceIte]
    rw [H.hash_two hd.pos (by omega_using [hd_L, hd_ge]) (by rw [← hm.length hd]; omega_using [hb]), VG.Proof.MdStream.X86.Finalize.Fin1, u₂₃.mem, hbytes iv m hm, hst',
      hm.1.1, ← (hm.length hd), show P.B - (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B + 1) = P.B - 1 - VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B by omega]
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    refine WP.block_nil ⟨0, hC, Nat.zero_le _, by rw [VG.Proof.MdStream.X86.Finalize.lim_zero]; omega, edi₂₂, by rw [hesi]; rfl, fun iv m hm _ => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [H.hash_one hd.pos (by rw [← hm.length hd]; omega_using [hb]), VG.Proof.MdStream.X86.Finalize.Fin0, hbytes iv m hm, hst', hm.1.1,
      ← (hm.length hd), show P.B - P.L - (VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B + 1) = P.B - P.L - 1 - VG.Proof.MdStream.X86.Finalize.cnt s₀ % P.B by omega_using []]

/-! ## Output and epilogue -/

theorem finalize_eq {name : String} {code : Prog isa} : finalize P name code =
    .seq (.block (([.mov .eax (.mem (at_ .esp 20))] : List Instr) ++ save P .eax ++
      ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
       .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp (P.so + 16)) .ecx,
       .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp (P.so + 20)) .ecx,
       .mov .ecx (.mem (at_ .esp 16)), .store (at_ .ebp (P.so + 24)) .ecx,
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm (BitVec.ofNat 32 (P.B - 1))),
       .mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .edx P.N) .cl, .alu .add .edi (.imm 1),
       .mov .esi (.imm 0), .alu .cmp .edi (.imm (BitVec.ofNat 32 (P.B - P.L + 1)))] : List Instr)))
    (.seq (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))
    (.seq (.loop (finalizeBody P name code) .e)
      (.block (.mov .eax (.mem (at_ .ebp (P.so + 24))) :: (P.out ++ restore P .ebp))))) := rfl

theorem epilogue_ok (hd : VG.Proof.MdStream.X86.Dims P S) {s₀ : State} (hp : VG.Proof.MdStream.X86.Finalize.Pre P S s₀) {sD : State} (hD : VG.Proof.MdStream.X86.Finalize.Done S H s₀ sD) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hkeep : ∀ r ∈ [Reg.ebx, .ebp, .esp], s.gpr r = sD.gpr r)
    (hm : s.mem = VG.WriteBytes.writeBytes sD.mem (VG.Proof.MdStream.X86.Finalize.outA s₀) (H.digest (H.stateAt sD.mem (VG.Proof.MdStream.X86.Finalize.stA s₀)))) :
    WP isa (.block (restore P .ebp)) s fun s' => abiPreserved s₀ s' ∧ (VG.Proof.MdStream.X86.finK H S).post s₀ s' := by
  have hC := hD.1
  have hd_N := hd.N; have hd_so := hd.so
  have hdl := H.digest_length (H.stateAt sD.mem (VG.Proof.MdStream.X86.Finalize.stA s₀))
  have hfo : Frame [VG.Proof.MdStream.X86.Finalize.outR P s₀] sD.mem (VG.WriteBytes.writeBytes sD.mem (VG.Proof.MdStream.X86.Finalize.outA s₀) (H.digest (H.stateAt sD.mem (VG.Proof.MdStream.X86.Finalize.stA s₀)))) :=
    VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [show VG.Proof.MdStream.X86.Finalize.outA s₀ = VG.Proof.MdStream.X86.Finalize.outA s₀ + BitVec.ofNat 64 0 by simp]
      exact VG.Proof.MdStream.X86.contains_offset (by omega) (by decide))
  have hebp : s.gpr .ebp = VG.Proof.MdStream.X86.Finalize.scr s₀ := by rw [hkeep _ (by simp), hC.ebp]
  have rin : ∀ d, d + 4 ≤ S → InRegions (s.rd ++ s.wr) (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) d) 4 :=
    fun d hd => ⟨VG.Proof.MdStream.X86.Finalize.scR S s₀, by simp [hrd, hwr, hp.wr], hp.scr_in hd⟩
  have sv : ∀ p ∈ saved P, s.mem.readW (addr (VG.Proof.MdStream.X86.Finalize.scr s₀) p.2) 32 = s₀.gpr p.1 := by
    intro p hp'
    have hd' := VG.Proof.MdStream.X86.saved_offset hp'
    rw [hm, hfo.readW (r := ⟨addr (VG.Proof.MdStream.X86.Finalize.scr s₀) p.2, 4⟩) (Region.contains_self _ _)
      (by simpa using hp.out_scr.symm.sub_left (hp.scr_sub (by omega))) (by decide)]
    exact hC.saved p hp'
  rw [VG.Proof.MdStream.X86.restore_eq]
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Finalize.scr s₀) P.so) (by rw [VG.Proof.MdStream.X86.ea_at, hebp]) (rin P.so (by omega_using [hd.so])) fun s₁ u₁ => ?_
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 4)) (by rw [VG.Proof.MdStream.X86.ea_at, u₁.other _ (by decide), hebp])
    (by rw [u₁.rd, u₁.wr]; exact rin (P.so + 4) (by omega_using [hd.so])) fun s₂ u₂ => ?_
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 8)) (by rw [VG.Proof.MdStream.X86.ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hebp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin (P.so + 8) (by omega_using [hd.so])) fun s₃ u₃ => ?_
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 12))
    (by rw [VG.Proof.MdStream.X86.ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hebp])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rin (P.so + 12) (by omega_using [hd.so])) fun s₄ u₄ => WP.block_nil ?_
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun iv m hm' hok hc => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      exact sv (.ebx, P.so) (by simp [saved])
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem]
      exact sv (.esi, P.so + 4) (by simp [saved])
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]
      exact sv (.edi, P.so + 8) (by simp [saved])
    · rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]
      exact sv (.ebp, P.so + 12) (by simp [saved])
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
        hkeep _ (by simp), hC.esp]
  · rw [hm₄, hm, hfo.readW (r := VG.Proof.MdStream.X86.Finalize.retR s₀) (Region.contains_self _ _) (by simpa using hp.ret_out) (by decide)]
    refine hC.frame.readW (r := VG.Proof.MdStream.X86.Finalize.retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hp.ret_st, hp.ret_scr, hp.ret_a, hp.ret_stk]
  · have e := bytesAt_writeBytes sD.mem (VG.Proof.MdStream.X86.Finalize.outA s₀) 0 (H.digest (H.stateAt sD.mem (VG.Proof.MdStream.X86.Finalize.stA s₀))) (by omega)
    rw [hdl, show VG.Proof.MdStream.X86.Finalize.outA s₀ + BitVec.ofNat 64 0 = VG.Proof.MdStream.X86.Finalize.outA s₀ by simp, Nat.zero_add,
      show bytesAt sD.mem (VG.Proof.MdStream.X86.Finalize.outA s₀) 0 = [] from rfl, List.nil_append] at e
    show bytesAt s₄.mem (VG.Proof.MdStream.X86.Finalize.outA s₀) P.N = _
    rw [hm₄, hm, e, hD.2 iv m ⟨hm', hc⟩ hok]

theorem correct (hd : VG.Proof.MdStream.X86.Dims P S) (hs : VG.Proof.MdStream.X86.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86.CalleeOk H code)
    {s₀ : State} (hp : VG.Proof.MdStream.X86.Finalize.Pre P S s₀) :
    WP isa (finalize P name code) s₀ fun s' => abiPreserved s₀ s' ∧ (VG.Proof.MdStream.X86.finK H S).post s₀ s' := by
  have hd_N := hd.N; have hst := hp.st_fit; have ho := hp.out_fit
  rw [VG.Proof.MdStream.X86.Finalize.finalize_eq, ← VG.Proof.MdStream.X86.seq_assoc]
  refine WP.seq (WP.mono (VG.Proof.MdStream.X86.Finalize.prologue_ok (H := H) hd hp) fun s₁ ⟨k, hL⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.MdStream.X86.Finalize.Done S H s₀) ?_ fun sD hD => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n, VG.Proof.MdStream.X86.Finalize.LInv S H s₀ i n s) ?_ k s₁ ⟨_, hL⟩
    rintro i s ⟨n, hL⟩
    refine WP.mono (VG.Proof.MdStream.X86.Finalize.body_ok hd hs hf hp hL) fun s' h => ?_
    rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by decide, 0, hL'⟩
  · have hC := hD.1
    refine VG.Proof.MdStream.X86.wp_movm (a := addr (VG.Proof.MdStream.X86.Finalize.scr s₀) (P.so + 24)) (by rw [VG.Proof.MdStream.X86.ea_at, hC.ebp])
      ⟨VG.Proof.MdStream.X86.Finalize.scR S s₀, by simp [hC.rd, hC.wr, hp.wr], hp.scr_in (by have hd_so := hd.so; omega_using [hd.so])⟩ fun s₁ u₁ => ?_
    have heax : s₁.gpr .eax = VG.Proof.MdStream.X86.Finalize.out s₀ := by rw [u₁.gpr, hC.outp]
    have hebx : s₁.gpr .ebx = VG.Proof.MdStream.X86.Finalize.st s₀ := by rw [u₁.other _ (by decide), hC.ebx]
    rw [WP.block_append_iff]
    refine WP.mono (hs.out s₁ (by rw [hebx]; omega) (by rw [heax]; exact ho) ?_ ?_ ?_) fun s ⟨g, rd, wr, m⟩ =>
      VG.Proof.MdStream.X86.Finalize.epilogue_ok hd hp hD (by rw [rd, u₁.rd, hC.rd]) (by rw [wr, u₁.wr, hC.wr])
        (fun r hr => by rw [g r (VG.Proof.MdStream.X86.Finalize.regs3 hr).2.1, u₁.other r (VG.Proof.MdStream.X86.Finalize.regs3 hr).1]) (by rw [m, heax, hebx, u₁.mem])
    · refine ⟨VG.Proof.MdStream.X86.Finalize.stR P s₀, by simp [u₁.rd, u₁.wr, hC.rd, hC.wr, hp.wr, hp.rd], ?_⟩
      rw [hebx]; simpa using VG.Proof.MdStream.X86.contains_offset (base := VG.Proof.MdStream.X86.Finalize.stA s₀) (off := 0) (n := P.N) (len := P.N + P.B)
        (by omega) (by decide)
    · refine ⟨VG.Proof.MdStream.X86.Finalize.outR P s₀, by simp [u₁.wr, hC.wr, hp.wr], ?_⟩
      rw [heax]; simpa using VG.Proof.MdStream.X86.contains_offset (base := VG.Proof.MdStream.X86.Finalize.outA s₀) (off := 0) (n := P.N) (len := P.N)
        (by omega) (by decide)
    · rw [hebx, heax]
      exact hp.st_out.sub_left (Region.sub_prefix (by omega))

end

/-! ## Constant time -/

/-- The initial taint: the stack arguments are public, the words holding
`state`, `out` and `scratch` are the base addresses of the writable regions,
and the 20 bytes below `esp` are outside them. -/
def τ₀ (P : Params) (S : Nat) : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [P.N + P.B, P.N, S], argLen := 24,
    argBases := [(4, 0), (16, 1), (20, 2)], room := 20 }

section
variable {P : Params} {S : Nat} {H : Md P.B P.N P.L}

theorem wf₀ (hd : VG.Proof.MdStream.X86.Dims P S) {s : State} (h : (VG.Proof.MdStream.X86.finK H S).pre s) : VG.X86.Taint.Wf (VG.Proof.MdStream.X86.Finalize.τ₀ P S) s := by
  have hp := VG.Proof.MdStream.X86.Finalize.pre_of h
  have hst := hp.st_fit; have ho := hp.out_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo; have hd_N := hd.N
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, k1, k2, k3, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.MdStream.X86.Finalize.τ₀], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_out, hp.st_scr⟩, hp.out_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_st hp.a_st
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_out hp.a_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_scr hp.a_scr
  · intro p hp'
    simp only [VG.Proof.MdStream.X86.Finalize.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by simp [VG.Proof.MdStream.X86.Finalize.τ₀], ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, VG.X86.arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [k1, k2, k3]

theorem agree₀ (hd : VG.Proof.MdStream.X86.Dims P S) {s₁ s₂ : State} (h₁ : (VG.Proof.MdStream.X86.finK H S).pre s₁) (h₂ : (VG.Proof.MdStream.X86.finK H S).pre s₂)
    (hpub : (VG.Proof.MdStream.X86.finK H S).pub s₁ s₂) : VG.X86.Taint.Agree (VG.Proof.MdStream.X86.Finalize.τ₀ P S) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := VG.Proof.MdStream.X86.Finalize.pre_of h₁; have hp₂ := VG.Proof.MdStream.X86.Finalize.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.MdStream.X86.Finalize.wf₀ hd h₁, VG.Proof.MdStream.X86.Finalize.wf₀ hd h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.MdStream.X86.Finalize.τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [VG.Proof.MdStream.X86.Finalize.stR, VG.Proof.MdStream.X86.Finalize.outR, VG.Proof.MdStream.X86.Finalize.scR, VG.Proof.MdStream.X86.Finalize.stA, VG.Proof.MdStream.X86.Finalize.outA, VG.Proof.MdStream.X86.Finalize.scA, VG.Proof.MdStream.X86.Finalize.st, VG.Proof.MdStream.X86.Finalize.out, VG.Proof.MdStream.X86.Finalize.scr, ha 0 (by decide), ha 3 (by decide), ha 4 (by decide)]
  · simp only [VG.Proof.MdStream.X86.Finalize.τ₀] at hk
    rw [show VG.X86.Taint.depth (VG.Proof.MdStream.X86.Finalize.τ₀ P S).stk = 0 from rfl, Nat.zero_add]
    have f₁ : (s₁.gpr .esp).toNat + 24 ≤ 2 ^ 32 := hp₁.sp_fit
    have f₂ : (s₂.gpr .esp).toNat + 24 ≤ 2 ^ 32 := hp₂.sp_fit
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (ha _ (by omega))

end

/-- Memory holding the arguments `0x1000, 0, 0, 0x2000, 0x3000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5015 then 0x30 else 0

/-- The registers and memory of a state satisfying the preconditions. -/
def sat₀ : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.MdStream.X86.Finalize.satMem
  rd := []
  wr := []

/-- A state satisfying `finK`'s precondition. -/
def satR (P : Params) (S : Nat) : State :=
  { VG.Proof.MdStream.X86.Finalize.sat₀ with
              rd := [⟨0x5004, 20⟩], wr := [⟨0x1000, P.N + P.B⟩, ⟨0x2000, P.N⟩, ⟨0x3000, S⟩] }

/-- A state satisfying `finKw`'s precondition. -/
def sat (P : Params) (S : Nat) : State :=
  { VG.Proof.MdStream.X86.Finalize.sat₀ with
              wr := [⟨0x1000, P.N + P.B⟩, ⟨0x2000, P.N⟩, ⟨0x3000, S⟩, ⟨0x5004, 20⟩] }

section
variable {P : Params} {S : Nat} {H : Md P.B P.N P.L}

theorem satR_pre (hd : VG.Proof.MdStream.X86.Dims P S) : (VG.Proof.MdStream.X86.finK H S).pre (VG.Proof.MdStream.X86.Finalize.satR P S) := by
  have hd_N := hd.N; have hd_S := hd.S; have hd_le := hd.le
  have a0 : VG.X86.arg (VG.Proof.MdStream.X86.Finalize.satR P S) 0 = 0x1000 := show VG.X86.arg VG.Proof.MdStream.X86.Finalize.sat₀ 0 = _ by decide
  have a3 : VG.X86.arg (VG.Proof.MdStream.X86.Finalize.satR P S) 3 = 0x2000 := show VG.X86.arg VG.Proof.MdStream.X86.Finalize.sat₀ 3 = _ by decide
  have a4 : VG.X86.arg (VG.Proof.MdStream.X86.Finalize.satR P S) 4 = 0x3000 := show VG.X86.arg VG.Proof.MdStream.X86.Finalize.sat₀ 4 = _ by decide
  have e : argAddr (VG.Proof.MdStream.X86.Finalize.satR P S) 0 = 0x5004 := show argAddr VG.Proof.MdStream.X86.Finalize.sat₀ 0 = _ by decide
  have hsp : (VG.Proof.MdStream.X86.Finalize.satR P S).gpr .esp = 0x5000 := rfl
  simp only [VG.Proof.MdStream.X86.finK, a0, a3, a4, e, hsp]
  have hs : ((0x5000 : BitVec 32).setWidth 64 - 20 : Addr) = 0x4FEC := by decide
  simp only [hs]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp; omega, by simp; omega,
    by simp; omega, by decide, by decide⟩ <;>
  · first
    | exact Offset.disjoint_of_le (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)
        (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)
    | exact (Offset.disjoint_of_le (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; omega)
        (by simp only [BitVec.toNat_setWidth, BitVec.reduceToNat]; decide)).symm

theorem sat_pre (hd : VG.Proof.MdStream.X86.Dims P S) : (VG.Proof.MdStream.X86.finKw H S).pre (VG.Proof.MdStream.X86.Finalize.sat P S) := by
  have ⟨_, _, h⟩ := VG.Proof.MdStream.X86.Finalize.satR_pre (H := H) hd
  have a0 : VG.X86.arg (VG.Proof.MdStream.X86.Finalize.sat P S) 0 = 0x1000 := show VG.X86.arg VG.Proof.MdStream.X86.Finalize.sat₀ 0 = _ by decide
  have a3 : VG.X86.arg (VG.Proof.MdStream.X86.Finalize.sat P S) 3 = 0x2000 := show VG.X86.arg VG.Proof.MdStream.X86.Finalize.sat₀ 3 = _ by decide
  have a4 : VG.X86.arg (VG.Proof.MdStream.X86.Finalize.sat P S) 4 = 0x3000 := show VG.X86.arg VG.Proof.MdStream.X86.Finalize.sat₀ 4 = _ by decide
  have e : argAddr (VG.Proof.MdStream.X86.Finalize.sat P S) 0 = 0x5004 := show argAddr VG.Proof.MdStream.X86.Finalize.sat₀ 0 = _ by decide
  refine ⟨rfl, ?_, h⟩
  simp only [a0, a3, a4, e]; rfl

/-- `finalize` is verified, given that it is constant time (by the taint analysis of each hash
function's code, from `τ₀` and `agree₀`). -/
theorem verified_ro (hd : VG.Proof.MdStream.X86.Dims P S) (hs : VG.Proof.MdStream.X86.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86.CalleeOk H code)
    (hct : ConstantTime isa (VG.Proof.MdStream.X86.finK H S).pre (VG.Proof.MdStream.X86.finK H S).pub (finalize P name code)) :
    Verified X86.target (finalize P name code) (VG.Proof.MdStream.X86.finK H S) := by
  refine ⟨fun s hs' => ?_, hct, ⟨VG.Proof.MdStream.X86.Finalize.satR P S, VG.Proof.MdStream.X86.Finalize.satR_pre hd⟩⟩
  obtain ⟨t, s', he, h⟩ := VG.Proof.MdStream.X86.Finalize.correct hd hs hf (VG.Proof.MdStream.X86.Finalize.pre_of hs')
  exact ⟨t, s', he, h⟩

/-- `finalize` is also verified against `finKw`, which lets it write its arguments. -/
theorem verified (hd : VG.Proof.MdStream.X86.Dims P S) (hs : VG.Proof.MdStream.X86.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86.CalleeOk H code)
    (hct : ConstantTime isa (VG.Proof.MdStream.X86.finK H S).pre (VG.Proof.MdStream.X86.finK H S).pub (finalize P name code)) :
    Verified X86.target (finalize P name code) (VG.Proof.MdStream.X86.finKw H S) := by
  have pre : ∀ s, (VG.Proof.MdStream.X86.finKw H S).pre s → (VG.Proof.MdStream.X86.finK H S).pre (s.withRegions
      [⟨argAddr s 0, 20⟩] [⟨(VG.X86.arg s 0).setWidth 64, P.N + P.B⟩, ⟨(VG.X86.arg s 3).setWidth 64, P.N⟩,
        ⟨(VG.X86.arg s 4).setWidth 64, S⟩]) := by
    intro s h
    obtain ⟨_, _, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
    simp only [VG.Proof.MdStream.X86.finK, arg_withRegions, argAddr_withRegions, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
  refine Verified.narrowTo (VG.Proof.MdStream.X86.Finalize.verified_ro hd hs hf hct) _ _ pre (fun s h => ?_) (fun s h => ?_)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) ⟨VG.Proof.MdStream.X86.Finalize.sat P S, VG.Proof.MdStream.X86.Finalize.sat_pre hd⟩
  · obtain ⟨h1, h2, _⟩ := h
    rw [h1, h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)), 0,
        by simp, by simp⟩
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩
  · obtain ⟨_, h2, _⟩ := h
    rw [h2]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp, by simp⟩

end

end VG.Proof.MdStream.X86.Finalize

end

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.X86.Words`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on x86 (32-bit): length fields and digests

What the length fields (`len64`) and digests (`out32`) of
`Impl/MdStream/X86.lean` write, for the hash functions' `Shape`s.
-/

namespace VG.Proof.MdStream.X86

open VG VG.X86 VG.Impl.MdStream.X86
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil write_eq_writeBytes writeBytes_append
  writeBytes_frame shl3 bits8)

/-! ## Byte order -/

theorem bytes32_store (be : Bool) (x : BitVec 32) :
    (List.range 4).map (fun j => (if be then bswap x else x).extractLsb' (8 * j) 8) = bytes32 be x := by
  cases be
  · simp [bytes32, List.range_succ]
  · simp only [bytes32, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · refine byte_ext fun i hi => ?_
      rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
      all_goals first
        | exact absurd hi (by omega)
        | (simp only [bswap, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]; simp)

theorem writeW32 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 32) :
    m.writeW a (if be then bswap x else x) = VG.WriteBytes.writeBytes m a (bytes32 be x) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes, ← VG.Proof.MdStream.X86.bytes32_store]; rfl

/-- The bytes of a 64-bit word, from those of its halves. -/
theorem bytes64_halves (be : Bool) (hi lo : BitVec 32) :
    bytes64 be (hi ++ lo) = if be then bytes32 true hi ++ bytes32 true lo else bytes32 false lo ++ bytes32 false hi := by
  cases be <;>
  · simp only [bytes64, bytes32, Bool.false_eq_true, ite_true, ite_false, List.range_succ, List.range_zero,
      List.nil_append, List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil, List.cons_append,
      List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · ext i hi
      simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
      split <;> first | omega | (congr 1; omega) | rfl

/-! ## The length field -/

theorem times8 (x : BitVec 32) : x + x + (x + x) + (x + x + (x + x)) = x <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The bit count of a byte count, from its halves. -/
theorem bitCount (hi lo : BitVec 32) :
    (hi <<< 3 ||| lo >>> 29) ++ lo <<< 3 = BitVec.ofNat 64 (8 * (hi ++ lo).toNat) := by
  rw [shl3, bits8]

/-- `len64Of d be` stores `8 · count`, from `count` in `eax` (low word) and `ecx` (high word), at
`ebx + d`. -/
theorem len64Of_ok {d : Nat} {be : Bool} {s : State} {hi lo : BitVec 32}
    (hfit : (s.gpr .ebx).toNat + d + 8 ≤ 2 ^ 32) (hax : s.gpr .eax = lo) (hcx : s.gpr .ecx = hi)
    (ho₁ : InRegions s.wr (addr (s.gpr .ebx) d) 4) (ho₂ : InRegions s.wr (addr (s.gpr .ebx) (d + 4)) 4) :
    WP isa (.block (len64Of d be)) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 d)
        (bytes64 be (BitVec.ofNat 64 (8 * (hi ++ lo).toNat))) := by
  unfold len64Of
  refine VG.Proof.MdStream.X86.wp_add fun s₃ u₃ => VG.Proof.MdStream.X86.wp_add fun s₄ u₄ => VG.Proof.MdStream.X86.wp_add fun s₅ u₅ => VG.Proof.MdStream.X86.wp_mov fun s₆ u₆ =>
    VG.Proof.MdStream.X86.wp_shr (by decide) fun s₇ u₇ => VG.Proof.MdStream.X86.wp_or fun s₈ u₈ => VG.Proof.MdStream.X86.wp_add fun s₉ u₉ => VG.Proof.MdStream.X86.wp_add fun s₁₀ u₁₀ =>
    VG.Proof.MdStream.X86.wp_add fun s₁₁ u₁₁ => ?_
  have g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₁₁.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₁₁.other r h1, u₁₀.other r h1, u₉.other r h1, u₈.other r h2, u₇.other r h3,
      u₆.other r h3, u₅.other r h2, u₄.other r h2, u₃.other r h2]
  have m₁₁ : s₁₁.mem = s.mem := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have rd₁₁ : s₁₁.rd = s.rd := by
    rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd]
  have wr₁₁ : s₁₁.wr = s.wr := by
    rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]
  have c5 : s₅.gpr .ecx = hi <<< 3 := by rw [u₅.gpr, u₄.gpr, u₃.gpr, hcx, VG.Proof.MdStream.X86.times8]
  have a5 : s₅.gpr .eax = lo := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), hax]
  have d7 : s₇.gpr .edx = lo >>> 29 := by rw [u₇.gpr, u₆.gpr, a5]
  have c8 : s₈.gpr .ecx = (hi <<< 3) ||| (lo >>> 29) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), c5, d7]
  have a11 : s₁₁.gpr .eax = lo <<< 3 := by
    rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), a5,
      VG.Proof.MdStream.X86.times8]
  have c11 : s₁₁.gpr .ecx = (hi <<< 3) ||| (lo >>> 29) := by
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), c8]
  have ebx₁₁ : s₁₁.gpr .ebx = s.gpr .ebx := g _ (by decide) (by decide) (by decide)
  have e₁ : addr (s.gpr .ebx) d = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 d := addr_eq (by omega)
  have hx := VG.Proof.MdStream.X86.bitCount hi lo
  cases be
  · simp only [Bool.false_eq_true, ite_false]
    refine VG.Proof.MdStream.X86.wp_store (a := addr (s.gpr .ebx) d) (by rw [VG.Proof.MdStream.X86.ea_at, ebx₁₁]) (by rw [wr₁₁]; exact ho₁) fun s₁₂ u₁₂ => ?_
    refine VG.Proof.MdStream.X86.wp_store (a := addr (s.gpr .ebx) (d + 4)) (by rw [VG.Proof.MdStream.X86.ea_at, u₁₂.gpr, ebx₁₁])
      (by rw [u₁₂.wr, wr₁₁]; exact ho₂) fun s₁₃ u₁₃ => WP.block_nil ?_
    refine ⟨fun r h1 h2 h3 => by rw [u₁₃.gpr, u₁₂.gpr, g r h1 h2 h3], by rw [u₁₃.rd, u₁₂.rd, rd₁₁],
      by rw [u₁₃.wr, u₁₂.wr, wr₁₁], ?_⟩
    rw [u₁₃.mem, u₁₂.mem, u₁₂.gpr, a11, c11, m₁₁, ← hx, VG.Proof.MdStream.X86.bytes64_halves]
    simp only [Bool.false_eq_true, ite_false]
    have w := fun (m : Mem) (a : Addr) (x : BitVec 32) => VG.Proof.MdStream.X86.writeW32 m a false x
    simp only [Bool.false_eq_true, ite_false] at w
    rw [w, w, e₁, show addr (s.gpr .ebx) (d + 4) = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 d +
      BitVec.ofNat 64 (bytes32 false (lo <<< 3)).length by rw [addr_eq (by omega), VG.Proof.MdStream.X86.add_ofNat]; rfl,
      VG.WriteBytes.writeBytes_append _ _ _ _ (by simp [bytes32])]
  · simp only [ite_true]
    refine VG.Proof.MdStream.X86.wp_bswap fun s₁₂ u₁₂ => ?_
    refine VG.Proof.MdStream.X86.wp_store (a := addr (s.gpr .ebx) d) (by rw [VG.Proof.MdStream.X86.ea_at, u₁₂.other _ (by decide), ebx₁₁])
      (by rw [u₁₂.wr, wr₁₁]; exact ho₁) fun s₁₃ u₁₃ => VG.Proof.MdStream.X86.wp_bswap fun s₁₄ u₁₄ => ?_
    refine VG.Proof.MdStream.X86.wp_store (a := addr (s.gpr .ebx) (d + 4))
      (by rw [VG.Proof.MdStream.X86.ea_at, u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other _ (by decide), ebx₁₁])
      (by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁]; exact ho₂) fun s₁₅ u₁₅ => WP.block_nil ?_
    refine ⟨fun r h1 h2 h3 => by rw [u₁₅.gpr, u₁₄.other r h1, u₁₃.gpr, u₁₂.other r h2, g r h1 h2 h3],
      by rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, rd₁₁], by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, wr₁₁], ?_⟩
    have a14 : s₁₄.gpr .eax = bswap (lo <<< 3) := by
      rw [u₁₄.gpr, u₁₃.gpr, u₁₂.other _ (by decide), a11]
    have c12 : s₁₂.gpr .ecx = bswap ((hi <<< 3) ||| (lo >>> 29)) := by rw [u₁₂.gpr, c11]
    rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, a14, c12, m₁₁, ← hx, VG.Proof.MdStream.X86.bytes64_halves]
    simp only [ite_true]
    have w := fun (m : Mem) (a : Addr) (x : BitVec 32) => VG.Proof.MdStream.X86.writeW32 m a true x
    simp only [ite_true] at w
    rw [w, w, e₁, show addr (s.gpr .ebx) (d + 4) = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 d +
      BitVec.ofNat 64 (bytes32 true ((hi <<< 3) ||| (lo >>> 29))).length by
      rw [addr_eq (by omega), VG.Proof.MdStream.X86.add_ofNat]; rfl,
      VG.WriteBytes.writeBytes_append _ _ _ _ (by simp [bytes32])]

/-- `loadCount so` loads `count` into `eax` (low word) and `ecx` (high word). -/
theorem loadCount_ok {so : Nat} {s : State} {rest : List Instr} {Q : State → Prop}
    (hlo : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (so + 16)) 4)
    (hhi : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (so + 20)) 4)
    (k : ∀ s', (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.gpr .eax = s.mem.readW (addr (s.gpr .ebp) (so + 16)) 32 →
      s'.gpr .ecx = s.mem.readW (addr (s.gpr .ebp) (so + 20)) 32 → WP isa (.block rest) s' Q) :
    WP isa (.block (loadCount so ++ rest)) s Q := by
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (s.gpr .ebp) (so + 16)) (VG.Proof.MdStream.X86.ea_at _ _ _) hlo fun s₁ u₁ => ?_
  refine VG.Proof.MdStream.X86.wp_movm (a := addr (s.gpr .ebp) (so + 20)) (by rw [VG.Proof.MdStream.X86.ea_at, u₁.other _ (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact hhi) fun s₂ u₂ => k s₂ (fun r h1 h2 => by rw [u₂.other r h2, u₁.other r h1])
      (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      (by rw [u₂.other _ (by decide), u₁.gpr]) (by rw [u₂.gpr, u₁.mem])

/-- `len64 so d be` stores `8 · count`, from `count` in `[ebp + so + 16]` (low
word) and `[ebp + so + 20]` (high word), at `ebx + d`. -/
theorem len64_ok {so d : Nat} {be : Bool} {s : State} (hfit : (s.gpr .ebx).toNat + d + 8 ≤ 2 ^ 32)
    (hlo : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (so + 16)) 4)
    (hhi : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (so + 20)) 4)
    (ho₁ : InRegions s.wr (addr (s.gpr .ebx) d) 4) (ho₂ : InRegions s.wr (addr (s.gpr .ebx) (d + 4)) 4) :
    WP isa (.block (len64 so d be)) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 d)
        (bytes64 be (BitVec.ofNat 64 (8 * (s.mem.readW (addr (s.gpr .ebp) (so + 20)) 32 ++
          s.mem.readW (addr (s.gpr .ebp) (so + 16)) 32).toNat))) :=
  VG.Proof.MdStream.X86.loadCount_ok hlo hhi fun s' g m rd wr ha hc => by
    have hb : s'.gpr .ebx = s.gpr .ebx := g _ (by decide) (by decide)
    refine (VG.Proof.MdStream.X86.len64Of_ok (by rw [hb]; exact hfit) ha hc (by rw [wr, hb]; exact ho₁) (by rw [wr, hb]; exact ho₂)).mono
      fun s'' ⟨g', rd', wr', m'⟩ => ⟨fun r h1 h2 h3 => by rw [g' r h1 h2 h3, g r h1 h2], rd'.trans rd,
        wr'.trans wr, by rw [m', m, hb]⟩

/-! ## The digest -/

/-- The `w`-byte words `[k, n)` of the hash value at `ebx` are written to `eax` as `g` says, the
first `k` already written. -/
theorem out_words (n w : Nat) (hwn : w * n ≤ 64) (g : Nat → List Byte) (hg : ∀ k, (g k).length = w)
    (ins : Nat → List Instr) {s₀ : State}
    (hstep : ∀ k < n, ∀ (s : State) (rest : List Instr) (Q : State → Prop),
      s.gpr .ebx = s₀.gpr .ebx → s.gpr .eax = s₀.gpr .eax → s.rd = s₀.rd → s.wr = s₀.wr →
      Frame [⟨(s₀.gpr .eax).setWidth 64, w * n⟩] s₀.mem s.mem →
      (∀ s', (∀ r, r ≠ .ecx → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
        s'.mem = VG.WriteBytes.writeBytes s.mem ((s₀.gpr .eax).setWidth 64 + BitVec.ofNat 64 (w * k)) (g k) →
        WP isa (.block rest) s' Q) →
      WP isa (.block (ins k ++ rest)) s Q) :
    ∀ j ≤ n, ∀ s, (∀ r, r ≠ .ecx → s.gpr r = s₀.gpr r) → s.rd = s₀.rd → s.wr = s₀.wr →
      s.mem = VG.WriteBytes.writeBytes s₀.mem ((s₀.gpr .eax).setWidth 64) ((List.range (n - j)).flatMap g) →
      WP isa (.block (((List.range n).drop (n - j)).flatMap ins)) s fun s' =>
        (∀ r, r ≠ .ecx → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
        s'.mem = VG.WriteBytes.writeBytes s₀.mem ((s₀.gpr .eax).setWidth 64) ((List.range n).flatMap g) := by
  have hflat : ∀ k, ((List.range k).flatMap g).length = w * k := by
    intro k
    rw [List.length_flatMap, List.map_congr_left (fun x _ => hg _), List.map_const', List.sum_replicate_nat,
      List.length_range, Nat.mul_comm]
  intro j
  induction j with
  | zero =>
    intro _ s hg' rd wr m
    rw [Nat.sub_zero, List.drop_of_length_le (by simp), List.flatMap_nil]
    exact WP.block_nil ⟨hg', rd, wr, m⟩
  | succ j ih =>
    intro hj s hg' rd wr m
    have hk : n - (j + 1) < n := by omega
    have hle : w * (n - (j + 1)) + w ≤ w * n := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left w (by omega)
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_range]
    have hf : Frame [⟨(s₀.gpr .eax).setWidth 64, w * n⟩] s₀.mem s.mem := by
      rw [m]
      refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
      rw [hflat]
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      omega
    refine hstep _ hk s _ _ (by rw [hg' _ (by decide)]) (by rw [hg' _ (by decide)]) rd wr hf
      fun s' hg'' rd' wr' m' => ?_
    rw [show n - (j + 1) + 1 = n - j by omega]
    refine ih (by omega) s' (fun r h => by rw [hg'' r h, hg' r h]) (rd'.trans rd) (wr'.trans wr) ?_
    rw [m', m, show n - j = n - (j + 1) + 1 by omega, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, ← VG.WriteBytes.writeBytes_append _ _ _ _ (by rw [hflat, hg]; omega), hflat]

/-- A word of the hash value at `ebx`, while only the digest at `eax` is written. -/
theorem out_read {s₀ : State} {m : Mem} {n o : Nat}
    (hf : Frame [⟨(s₀.gpr .eax).setWidth 64, n⟩] s₀.mem m)
    (hd : Region.Disjoint ⟨(s₀.gpr .ebx).setWidth 64, n⟩ ⟨(s₀.gpr .eax).setWidth 64, n⟩)
    (h : o + 4 ≤ n) (hn : n ≤ 64) :
    m.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 o) 32 =
      s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 o) 32 :=
  hf.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) (fun r' hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hd.sub_left (VG.Proof.MdStream.X86.sub_offset h (by omega))) (by decide)

/-- `[x + o, x + o + 4)` lies in a region of `n` bytes at `x`. -/
theorem out_in {rs : List Region} {a : Addr} {n o : Nat} (h : InRegions rs a n) (ho : o + 4 ≤ n) (hn : n ≤ 64) :
    InRegions rs (a + BitVec.ofNat 64 o) 4 := by
  obtain ⟨R, hR, hc⟩ := h
  refine ⟨R, hR, ?_⟩
  simp only [Region.Contains] at *
  have : (a + BitVec.ofNat 64 o - R.base).toNat ≤ (a - R.base).toNat + o := by
    rw [show a + BitVec.ofNat 64 o - R.base = (a - R.base) + BitVec.ofNat 64 o by
      rw [VG.Offset.add_sub_comm],
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
    exact Nat.mod_le _ _
  omega

/-- `out32 n be` writes the `n` 32-bit words at `ebx` to `eax`. -/
theorem out32_ok {n : Nat} (be : Bool) (hn : 4 * n ≤ 64) {s₀ : State}
    (hbx : (s₀.gpr .ebx).toNat + 4 * n ≤ 2 ^ 32) (hax : (s₀.gpr .eax).toNat + 4 * n ≤ 2 ^ 32)
    (hin : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .ebx).setWidth 64) (4 * n))
    (hout : InRegions s₀.wr ((s₀.gpr .eax).setWidth 64) (4 * n))
    (hd : Region.Disjoint ⟨(s₀.gpr .ebx).setWidth 64, 4 * n⟩ ⟨(s₀.gpr .eax).setWidth 64, 4 * n⟩) :
    WP isa (.block (out32 n be)) s₀ fun s' =>
      (∀ r, r ≠ .ecx → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s₀.mem ((s₀.gpr .eax).setWidth 64)
        ((List.range n).flatMap fun k =>
          bytes32 be (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32)) := by
  have h := VG.Proof.MdStream.X86.out_words n 4 hn (fun k => bytes32 be (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 +
      BitVec.ofNat 64 (4 * k)) 32)) (fun _ => bytes32_length be _)
    (fun k => [.mov .ecx (.mem (at_ .ebx (4 * k)))] ++ (if be then [.bswap .ecx] else []) ++
      [.store (at_ .eax (4 * k)) .ecx]) (s₀ := s₀) ?_ n (Nat.le_refl _) s₀ (fun _ _ => rfl) rfl rfl
    (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, VG.WriteBytes.writeBytes_nil])
  · rw [Nat.sub_self, List.drop_zero] at h
    exact h
  intro k hk s rest Q hbx' hax' hrd hwr hf kk
  have hoff : 4 * k + 4 ≤ 4 * n := by omega
  have hread := VG.Proof.MdStream.X86.out_read hf hd hoff hn
  refine VG.Proof.MdStream.X86.wp_movm (a := (s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (4 * k))
    (by rw [VG.Proof.MdStream.X86.ea_at, hbx', addr_eq (by omega)])
    (by rw [hrd, hwr]; exact VG.Proof.MdStream.X86.out_in hin hoff hn) fun s₁ u₁ => ?_
  have ea₁ : ∀ t : State, t.gpr .eax = s₀.gpr .eax →
      t.ea (at_ .eax (4 * k)) = (s₀.gpr .eax).setWidth 64 + BitVec.ofNat 64 (4 * k) := fun t ht => by
    rw [VG.Proof.MdStream.X86.ea_at, ht, addr_eq (by omega)]
  cases be
  · refine VG.Proof.MdStream.X86.wp_store (ea₁ s₁ (by rw [u₁.other _ (by decide), hax']))
      (by rw [u₁.wr, hwr]; exact VG.Proof.MdStream.X86.out_in hout hoff hn) fun s₂ u₂ => ?_
    refine kk s₂ (fun r h => by rw [u₂.gpr, u₁.other r h]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) ?_
    rw [u₂.mem, u₁.mem, u₁.gpr, hread, ← VG.Proof.MdStream.X86.writeW32 _ _ false]; rfl
  · refine VG.Proof.MdStream.X86.wp_bswap fun s₂ u₂ => VG.Proof.MdStream.X86.wp_store (ea₁ s₂ (by rw [u₂.other _ (by decide),
                                                  u₁.other _ (by decide), hax'])) (by rw [u₂.wr, u₁.wr, hwr]; exact VG.Proof.MdStream.X86.out_in hout hoff hn)
      fun s₃ u₃ => ?_
    refine kk s₃ (fun r h => by rw [u₃.gpr, u₂.other r h, u₁.other r h]) (by rw [u₃.rd, u₂.rd, u₁.rd])
      (by rw [u₃.wr, u₂.wr, u₁.wr]) ?_
    rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, hread, ← VG.Proof.MdStream.X86.writeW32 _ _ true]; rfl

/-- `out64 n` writes the `n` 64-bit words at `ebx`, each stored little-endian (its low half
first), to `eax` big-endian: the high half, then the low half. -/
theorem out64_ok {n : Nat} (hn : 8 * n ≤ 64) {s₀ : State}
    (hbx : (s₀.gpr .ebx).toNat + 8 * n ≤ 2 ^ 32) (hax : (s₀.gpr .eax).toNat + 8 * n ≤ 2 ^ 32)
    (hin : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .ebx).setWidth 64) (8 * n))
    (hout : InRegions s₀.wr ((s₀.gpr .eax).setWidth 64) (8 * n))
    (hd : Region.Disjoint ⟨(s₀.gpr .ebx).setWidth 64, 8 * n⟩ ⟨(s₀.gpr .eax).setWidth 64, 8 * n⟩) :
    WP isa (.block (out64 n)) s₀ fun s' =>
      (∀ r, r ≠ .ecx → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s₀.mem ((s₀.gpr .eax).setWidth 64)
        ((List.range n).flatMap fun k =>
          bytes32 true (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k + 4)) 32) ++
          bytes32 true (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k)) 32)) := by
  have h := VG.Proof.MdStream.X86.out_words n 8 hn (fun k =>
      bytes32 true (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k + 4)) 32) ++
      bytes32 true (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k)) 32))
    (fun _ => by simp [bytes32_length])
    (fun k => [.mov .ecx (.mem (at_ .ebx (8 * k + 4))), .bswap .ecx, .store (at_ .eax (8 * k)) .ecx,
      .mov .ecx (.mem (at_ .ebx (8 * k))), .bswap .ecx, .store (at_ .eax (8 * k + 4)) .ecx])
    (s₀ := s₀) ?_ n (Nat.le_refl _) s₀ (fun _ _ => rfl) rfl rfl
    (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, VG.WriteBytes.writeBytes_nil])
  · rw [Nat.sub_self, List.drop_zero] at h
    exact h
  intro k hk s rest Q hbx' hax' hrd hwr hf kk
  have h₀ : 8 * k + 4 ≤ 8 * n := by omega
  have h₄ : 8 * k + 4 + 4 ≤ 8 * n := by omega
  have ea : ∀ (t : State) (r : Reg) (o : Nat), t.gpr r = s₀.gpr r → (s₀.gpr r).toNat + o < 2 ^ 32 →
      t.ea (at_ r o) = (s₀.gpr r).setWidth 64 + BitVec.ofNat 64 o := fun t r o ht ho => by
    rw [VG.Proof.MdStream.X86.ea_at, ht, addr_eq ho]
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.MdStream.X86.wp_movm (ea s .ebx _ hbx' (by omega)) (by rw [hrd, hwr]; exact VG.Proof.MdStream.X86.out_in hin h₄ hn) fun s₁ u₁ =>
    VG.Proof.MdStream.X86.wp_bswap fun s₂ u₂ => ?_
  refine VG.Proof.MdStream.X86.wp_store (ea s₂ .eax _ (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hax']) (by omega))
    (by rw [u₂.wr, u₁.wr, hwr]; exact VG.Proof.MdStream.X86.out_in hout h₀ hn) fun s₃ u₃ => ?_
  have hf₃ : Frame [⟨(s₀.gpr .eax).setWidth 64, 8 * n⟩] s₀.mem s₃.mem := by
    rw [u₃.mem, u₂.mem, u₁.mem]
    exact hf.writeW (List.mem_singleton_self _) _ (VG.Proof.MdStream.X86.contains_offset h₀ (by omega))
  refine VG.Proof.MdStream.X86.wp_movm (ea s₃ .ebx _ (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hbx'])
    (by omega)) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrd, hwr]; exact VG.Proof.MdStream.X86.out_in hin h₀ hn)
    fun s₄ u₄ => VG.Proof.MdStream.X86.wp_bswap fun s₅ u₅ => ?_
  refine VG.Proof.MdStream.X86.wp_store (ea s₅ .eax _ (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
                            u₂.other _ (by decide), u₁.other _ (by decide), hax']) (by omega))
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hwr]; exact VG.Proof.MdStream.X86.out_in hout h₄ hn) fun s₆ u₆ => ?_
  refine kk s₆ (fun r h => by rw [u₆.gpr, u₅.other r h, u₄.other r h, u₃.gpr, u₂.other r h, u₁.other r h])
    (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) ?_
  have v₂ : s₂.gpr .ecx = bswap (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k + 4)) 32) := by
    rw [u₂.gpr, u₁.gpr, VG.Proof.MdStream.X86.out_read hf hd h₄ hn]
  have v₅ : s₅.gpr .ecx = bswap (s₀.mem.readW ((s₀.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (8 * k)) 32) := by
    rw [u₅.gpr, u₄.gpr, VG.Proof.MdStream.X86.out_read hf₃ hd (by omega) hn]
  have w := fun (m : Mem) (a : Addr) (x : BitVec 32) => VG.Proof.MdStream.X86.writeW32 m a true x
  simp only [ite_true] at w
  rw [u₆.mem, u₅.mem, u₄.mem, v₅, u₃.mem, v₂, u₂.mem, u₁.mem, w, w,
    ← VG.WriteBytes.writeBytes_append _ _ _ _ (by simp [bytes32_length]), bytes32_length, VG.Proof.MdStream.X86.add_ofNat]

end VG.Proof.MdStream.X86

end
