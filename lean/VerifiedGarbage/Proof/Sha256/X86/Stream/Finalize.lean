import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Sha256.Scratch
import VerifiedGarbage.Impl.Sha256.X86.Stream
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Offset

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.Stream.Common`. -/
section

/-!
# Streaming SHA-256 on x86 (32-bit): common lemmas

Memory, state and constant-time facts shared by the x86 proofs that
import it. Per-instruction WP rules that expose only what changes, and
arithmetic on 32-bit values.
-/

namespace VG.Proof.Sha256.X86.Stream

open VG VG.X86 VG.Impl.Sha256.X86.Stream
open VG.Impl.Sha256.X86 (at_)
open VG.Proof.Sha256.X86 (compress_verified contains_offset)
open VG.Spec.Sha256 (HashValue stateAt blockAt compressBlocks compress parseBlock bytesAt)

/-! ## Regions -/

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

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
  exact contains_offset h (by omega)

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
  Mem.readW_writeW_sep (VG.Proof.Sha256.X86.Stream.addr_sep hd he h) (by decide)

/-! ## One instruction at a time -/

/-- `s'` is `s` with register `d` set to `v` (the flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : VG.Proof.Sha256.X86.Stream.Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) (d : Reg) (x : BitVec 32) (c o : Bool) (v : BitVec 32) :
    VG.Proof.Sha256.X86.Stream.Upd s ((arithFlags s x c o).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.setFlags (s : State) (d : Reg) (c o z n : Option Bool) (v : BitVec 32) :
    VG.Proof.Sha256.X86.Stream.Upd s ((s.setFlags c o z n).setReg d v) d v :=
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

theorem wp_mov {d r : Reg} (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movi {d : Reg} {v : BitVec 32} (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d (s.mem.readW a 32)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc, State.load32, ha, hin]

theorem wp_store {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Mupd s s' (s.mem.writeW a (s.gpr r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store32, ha, hout]

theorem wp_addi {d : Reg} {v : BitVec 32} (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (s.gpr d + v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_add {d r : Reg} (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (s.gpr d + s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (s.gpr d - v) → s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_sub {d r : Reg}
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (s.gpr d - s.gpr r) → s'.zf = some (s.gpr d - s.gpr r == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_andi {d : Reg} {v : BitVec 32} (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (s.gpr d &&& v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_or {d r : Reg} (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (s.gpr d ||| s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- `cmp d, r`: CF is `d < r` (unsigned). -/
theorem wp_cmp {d r : Reg}
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < v.toNat)) →
      s'.zf = some (s.gpr d - v == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem wp_test {d : Reg}
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Fupd s s' → s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)

theorem wp_shr {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  WP.cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl) (k _ (Upd.setFlags _ _ _ _ _ _ _))

theorem wp_bswap {d : Reg} (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d (bswap (s.gpr d)) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Upd s s' d ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg8} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', VG.Proof.Sha256.X86.Stream.Mupd s s' (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
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

/-! ## The call of the compression function -/

/-- The 20 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 20 ≤ E.toNat) : below E 20 = ⟨E.setWidth 64 - 20, 20⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

theorem compressBlocks_one (H : HashValue) (m : Mem) (p : Addr) :
    compressBlocks H m p 1 = compress H (blockAt m p) := by
  simp [compressBlocks]

theorem arg_eq (s : State) (i : Nat) : arg s i = s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 := rfl

theorem compress_nosp : NoSp Impl.Sha256.X86.compress := NoSp.of_all (by lit_decide)

theorem compress_stack : stackUse Impl.Sha256.X86.compress = 0 := by lit_decide

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
  rw [show k = (k - 1) + 1 by omega, VG.Proof.Sha256.X86.Stream.ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem and63 (x : BitVec 32) : x &&& 63 = BitVec.ofNat 32 (x.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (63 : BitVec 32).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem toNat_ofNat_lt {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

/-! ## Byte order -/

theorem bswap_bytes (w : BitVec 32) :
    (List.range 4).map (fun j => (bswap w).extractLsb' (8 * j) 8) = Spec.Sha256.wordBytes w := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, Spec.Sha256.wordBytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp (disch := decide) only [bswap, Nat.mul_zero, Nat.reduceMul, VG.extractLsb'_append_byte_lo,
      VG.extractLsb'_append_byte_hi, Nat.reduceSub, BitVec.extractLsb'_eq_self]

end VG.Proof.Sha256.X86.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha256.X86.Stream.Finalize`. -/
section

/-!
# Streaming SHA-256 on x86 (32-bit): the loop of `finalize`

The memory, state, prologue and constant-time facts that SHA-512's
`finalize` on x86 shares (`Proof/Sha512/X86/Stream/Finalize.lean`). The state
is in `ebx`, scratch in `ebp`, buffered bytes in `edi`, and the padding-loop
flag in `esi`; count and output are in `scratch[128..140)`. Each compression
call uses the 20 bytes below `esp`.
-/

namespace VG.Proof.Sha256.X86.Stream.Finalize

open VG VG.X86 VG.Impl.Sha256.X86.Stream
open VG.Impl.Sha256.X86 (at_)
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream
open VG.Proof.Sha256.Stream
open VG.Spec.Sha256 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes)
open VG.Proof.Sha256 (countX86)

theorem lit32 (n : Nat) : (OfNat.ofNat n : BitVec 32) = BitVec.ofNat 32 n := rfl

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev cnt : Nat := (countX86 s₀).toNat
abbrev out : BitVec 32 := arg s₀ 3
abbrev scr : BitVec 32 := arg s₀ 4
abbrev stA : Addr := (VG.Proof.Sha256.X86.Stream.Finalize.st s₀).setWidth 64
abbrev outA : Addr := (VG.Proof.Sha256.X86.Stream.Finalize.out s₀).setWidth 64
abbrev scA : Addr := (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀).setWidth 64
abbrev stR : Region := ⟨VG.Proof.Sha256.X86.Stream.Finalize.stA s₀, 96⟩
abbrev outR : Region := ⟨VG.Proof.Sha256.X86.Stream.Finalize.outA s₀, 32⟩
abbrev scR : Region := ⟨VG.Proof.Sha256.X86.Stream.Finalize.scA s₀, 160⟩
abbrev argR : Region := ⟨addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) 4, 20⟩
abbrev retR : Region := ⟨(VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) 20

/-- The messages the initial state represents. -/
def R₀ (m : List Byte) : Prop :=
  Spec.Sha256.Repr s₀.mem (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀) m ∧ countX86 s₀ = BitVec.ofNat 64 m.length

/-- Our caller's registers are saved in the scratch space. -/
def Saved (m : Mem) : Prop := ∀ p ∈ saved, m.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) p.2) 32 = s₀.gpr p.1

/-- The digest, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (compress (stateAt mem (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀))
    (parseBlock fun t => (bytesAt mem (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32) n ++ List.replicate (64 - n) 0).getD t 0))
    (parseBlock fun t => (List.replicate 56 0 ++ lenBytes m).getD t 0)

/-- The digest, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (stateAt mem (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀))
    (parseBlock fun t => (bytesAt mem (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32) n ++ List.replicate (56 - n) 0 ++ lenBytes m).getD t 0)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.Sha256.X86.Stream.Finalize.stR s₀, VG.Proof.Sha256.X86.Stream.Finalize.outR s₀, VG.Proof.Sha256.X86.Stream.Finalize.scR s₀, VG.Proof.Sha256.X86.Stream.Finalize.argR s₀]
  st_out : (VG.Proof.Sha256.X86.Stream.Finalize.stR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.outR s₀)
  st_scr : (VG.Proof.Sha256.X86.Stream.Finalize.stR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.scR s₀)
  out_scr : (VG.Proof.Sha256.X86.Stream.Finalize.outR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.scR s₀)
  a_st : (VG.Proof.Sha256.X86.Stream.Finalize.argR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.stR s₀)
  a_out : (VG.Proof.Sha256.X86.Stream.Finalize.argR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.outR s₀)
  a_scr : (VG.Proof.Sha256.X86.Stream.Finalize.argR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.scR s₀)
  ret_st : (VG.Proof.Sha256.X86.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.stR s₀)
  ret_out : (VG.Proof.Sha256.X86.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.outR s₀)
  ret_scr : (VG.Proof.Sha256.X86.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.scR s₀)
  stk_st : (VG.Proof.Sha256.X86.Stream.Finalize.stkR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.stR s₀)
  stk_out : (VG.Proof.Sha256.X86.Stream.Finalize.stkR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.outR s₀)
  stk_scr : (VG.Proof.Sha256.X86.Stream.Finalize.stkR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.scR s₀)
  st_fit : (VG.Proof.Sha256.X86.Stream.Finalize.st s₀).toNat + 96 ≤ 2 ^ 32
  out_fit : (VG.Proof.Sha256.X86.Stream.Finalize.out s₀).toNat + 32 ≤ 2 ^ 32
  scr_fit : (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀).toNat + 160 ≤ 2 ^ 32
  sp_lo : 20 ≤ (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀).toNat
  sp_fit : (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀).toNat + 24 ≤ 2 ^ 32

theorem cnt_mod (s₀ : State) : VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64 = (arg s₀ 1).toNat % 64 := by
  simp only [VG.Proof.Sha256.X86.Stream.Finalize.cnt, countX86]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (arg s₀ 1).isLt, Nat.shiftLeft_eq]
  omega

theorem R₀.length {s₀ : State} {m : List Byte} (h : VG.Proof.Sha256.X86.Stream.Finalize.R₀ s₀ m) : VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64 = m.length % 64 := by
  rw [VG.Proof.Sha256.X86.Stream.Finalize.cnt, h.2, BitVec.toNat_ofNat]
  omega

namespace Pre
variable {s₀ : State} (hp : VG.Proof.Sha256.X86.Stream.Finalize.Pre s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ 160) : (VG.Proof.Sha256.X86.Stream.Finalize.scR s₀).Contains (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d) 4 :=
  VG.Proof.Sha256.X86.Stream.contains_addr hd (by omega) hp.scr_fit

theorem scr_sub {d : Nat} (hd : d + 4 ≤ 160) : Region.Sub ⟨addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d, 4⟩ (VG.Proof.Sha256.X86.Stream.Finalize.scR s₀) := by
  rw [addr_eq (by have := hp.scr_fit; omega)]
  exact VG.Proof.Sha256.X86.Stream.sub_offset hd (by omega)

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : (VG.Proof.Sha256.X86.Stream.Finalize.argR s₀).Contains (addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) 4, 20⟩ : Region).Contains _ _
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.contains _ hd₁ (by omega) (by omega)

theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : Region.Sub ⟨addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) d, 4⟩ (VG.Proof.Sha256.X86.Stream.Finalize.argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) 4, 20⟩
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Offset.sub _ hd₁ (by omega)

end Pre

/-- The return address is below the arguments. -/
theorem ret_a {s₀ : State} (hp : VG.Proof.Sha256.X86.Stream.Finalize.Pre s₀) : (VG.Proof.Sha256.X86.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.argR s₀) := by
  have := hp.sp_fit
  show Region.Disjoint ⟨(VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀).setWidth 64, 4⟩ ⟨addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) 4, 20⟩
  rw [addr_eq (by omega)]
  exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)

theorem ret_stk {s₀ : State} (hp : VG.Proof.Sha256.X86.Stream.Finalize.Pre s₀) : (VG.Proof.Sha256.X86.Stream.Finalize.retR s₀).Disjoint (VG.Proof.Sha256.X86.Stream.Finalize.stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨(VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀).setWidth 64, 4⟩ ⟨(VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩
  rw [Taint.sub_setWidth (by omega)]
  exact Offset.base_disjoint_below _ (by omega)

/-! ## Invariants -/

structure Common (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = VG.Proof.Sha256.X86.Stream.Finalize.st s₀
  ebp : s.gpr .ebp = VG.Proof.Sha256.X86.Stream.Finalize.scr s₀
  esp : s.gpr .esp = VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀
  frame : Frame [VG.Proof.Sha256.X86.Stream.Finalize.stR s₀, VG.Proof.Sha256.X86.Stream.Finalize.scR s₀, VG.Proof.Sha256.X86.Stream.Finalize.argR s₀, VG.Proof.Sha256.X86.Stream.Finalize.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.Sha256.X86.Stream.Finalize.Saved s₀ s.mem
  lo : s.mem.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 128) 32 = arg s₀ 1
  hi : s.mem.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 132) 32 = arg s₀ 2
  outp : s.mem.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 136) 32 = VG.Proof.Sha256.X86.Stream.Finalize.out s₀

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv (s₀ : State) (k n : Nat) (s : State) : Prop extends VG.Proof.Sha256.X86.Stream.Finalize.Common s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 56 + 8 * k
  edi : s.gpr .edi = BitVec.ofNat 32 n
  esi : s.gpr .esi = BitVec.ofNat 32 k
  hash : ∀ m, VG.Proof.Sha256.X86.Stream.Finalize.R₀ s₀ m → Spec.Sha256.hash m =
    (if k = 1 then VG.Proof.Sha256.X86.Stream.Finalize.Fin1 s₀ s.mem n m else VG.Proof.Sha256.X86.Stream.Finalize.Fin0 s₀ s.mem n m).toList.flatMap wordBytes

/-- All blocks are compressed. -/
def Done (s₀ : State) (s : State) : Prop :=
  VG.Proof.Sha256.X86.Stream.Finalize.Common s₀ s ∧ ∀ m, VG.Proof.Sha256.X86.Stream.Finalize.R₀ s₀ m → Spec.Sha256.hash m = (stateAt s.mem (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀)).toList.flatMap wordBytes

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : VG.Proof.Sha256.X86.Stream.Finalize.Common s₀ s)
    (hg : ∀ r ∈ [Reg.ebx, .ebp, .esp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.Sha256.X86.Stream.Finalize.Common s₀ s' where
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
theorem Common.frame_keep {s₀ : State} (hp : VG.Proof.Sha256.X86.Stream.Finalize.Pre s₀) {s : State} (h : VG.Proof.Sha256.X86.Stream.Finalize.Common s₀ s) {m : Mem}
    (hf : Frame [VG.Proof.Sha256.X86.Stream.Finalize.stR s₀, VG.Proof.Sha256.X86.Stream.Finalize.argR s₀] s.mem m) :
    Frame [VG.Proof.Sha256.X86.Stream.Finalize.stR s₀, VG.Proof.Sha256.X86.Stream.Finalize.scR s₀, VG.Proof.Sha256.X86.Stream.Finalize.argR s₀, VG.Proof.Sha256.X86.Stream.Finalize.stkR s₀] s₀.mem m ∧ VG.Proof.Sha256.X86.Stream.Finalize.Saved s₀ m ∧
      m.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 128) 32 = arg s₀ 1 ∧ m.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 132) 32 = arg s₀ 2 ∧
      m.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 136) 32 = VG.Proof.Sha256.X86.Stream.Finalize.out s₀ := by
  have word : ∀ d, 112 ≤ d → d + 4 ≤ 160 → m.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d) 32 = s.mem.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d) 32 := by
    intro d h₁ h₂
    refine hf.readW (r := ⟨addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.st_scr.symm.sub_left (hp.scr_sub h₂)
    · exact hp.a_scr.symm.sub_left (hp.scr_sub h₂)
  refine ⟨h.frame.trans (hf.mono (by simp)), fun p hp' => ?_, by rw [word 128 (by omega) (by omega)]; exact h.lo,
    by rw [word 132 (by omega) (by omega)]; exact h.hi, by rw [word 136 (by omega) (by omega)]; exact h.outp⟩
  have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
    simp only [VG.Impl.Sha256.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp
  rw [word p.2 hd.1 (by omega)]
  exact h.saved p hp'

theorem st_add (s₀ : State) (n : Nat) : VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32 + BitVec.ofNat 64 n = VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + BitVec.ofNat 64 (32 + n) := by
  simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

/-- Writing buffer bytes `[n, n + |xs|)`. -/
theorem buf_frame {s₀ : State} (m : Mem) {n : Nat} {xs : List Byte} (hn : n + xs.length ≤ 64) :
    Frame [VG.Proof.Sha256.X86.Stream.Finalize.stR s₀] m (VG.WriteBytes.writeBytes m (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32 + BitVec.ofNat 64 n) xs) := by
  refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
  rw [VG.Proof.Sha256.X86.Stream.Finalize.st_add]
  exact contains_offset (by omega) (by omega)

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.ebx, .ebp, .esp, .esi, .ecx], s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  edi : s.gpr .edi = BitVec.ofNat 32 (n + j)
  eax : s.gpr .eax = BitVec.ofNat 32 (lim - n - j)
  mem : s.mem = VG.WriteBytes.writeBytes sI.mem (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32 + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step {s₀ : State} (hp : VG.Proof.Sha256.X86.Stream.Finalize.Pre s₀) {sI : State} (hC : VG.Proof.Sha256.X86.Stream.Finalize.Common s₀ sI) (hecx : sI.gpr .ecx = 0)
    {n lim j : Nat} (hlim : lim ≤ 64) (hj : j < lim - n) {s : State} (h : VG.Proof.Sha256.X86.Stream.Finalize.Zero s₀ sI n lim j s) :
    WP isa (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .store8 (at_ .edx 32) .cl,
      .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) s fun s' =>
      VG.Proof.Sha256.X86.Stream.Finalize.Zero s₀ sI n lim (j + 1) s' ∧ s'.zf = some (decide (lim - n - (j + 1) = 0)) := by
  have hst := hp.st_fit
  have hebx : s.gpr .ebx = VG.Proof.Sha256.X86.Stream.Finalize.st s₀ := by rw [h.keep _ (by simp), hC.ebx]
  have ha : VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j = VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + BitVec.ofNat 64 (32 + n + j) := by
    simp only [BitVec.ofNat_add]; ac_rfl
  have hout : InRegions s.wr (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨VG.Proof.Sha256.X86.Stream.Finalize.stR s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [ha]
    exact contains_offset (by omega) (by omega)
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_add fun s₂ u₂ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_store8 (r := .cl) (a := VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ u₃ => ?_
  · rw [VG.Proof.Sha256.X86.Stream.ea_at, u₂.gpr, u₁.gpr, u₁.other _ (by decide), hebx, h.edi, ha, VG.Proof.Sha256.X86.Stream.addr_add_ofNat (by omega)]
    congr 2; omega
  refine VG.Proof.Sha256.X86.Stream.wp_addi fun s₄ u₄ => VG.Proof.Sha256.X86.Stream.wp_subi fun s₅ u₅ hz₅ => WP.block_nil ⟨⟨by omega, fun r hr => ?_,
    by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .eax ∧ r ≠ .edi ∧ r ≠ .edx := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₅.other r this.1, u₄.other r this.2.1, u₃.gpr, u₂.other r this.2.2, u₁.other r this.2.2, h.keep r hr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.edi,
      ← VG.Proof.Sha256.X86.Stream.ofNat_succ, Nat.add_assoc]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.eax,
      VG.Proof.Sha256.X86.Stream.ofNat_pred (by omega), Nat.sub_sub]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, show Reg8.cl.reg = Reg.ecx from rfl, u₂.other _ (by decide),
      u₁.other _ (by decide), h.keep _ (by simp), hecx, h.mem, List.replicate_succ',
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [hz₅, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.eax,
      VG.Proof.Sha256.X86.Stream.ofNat_pred (by omega), VG.Proof.Sha256.X86.Stream.ofNat_beq_zero (by omega), Nat.sub_sub, Nat.sub_sub]

theorem zero_ok {s₀ : State} (hp : VG.Proof.Sha256.X86.Stream.Finalize.Pre s₀) {sI : State} (hC : VG.Proof.Sha256.X86.Stream.Finalize.Common s₀ sI) (hecx : sI.gpr .ecx = 0)
    {n lim : Nat} (hlim : lim ≤ 64) (hn : n ≤ lim) {s : State} (h : VG.Proof.Sha256.X86.Stream.Finalize.Zero s₀ sI n lim 0 s)
    (hz : s.zf = some (decide (lim - n = 0))) :
    WP isa (.ite .e (.block []) (.loop (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi),
      .store8 (at_ .edx 32) .cl, .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne)) s
      (VG.Proof.Sha256.X86.Stream.Finalize.Zero s₀ sI n lim (lim - n)) := by
  refine WP.ite (decide (lim - n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ VG.Proof.Sha256.X86.Stream.Finalize.Zero s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (VG.Proof.Sha256.X86.Stream.Finalize.zero_step hp hC hecx hlim hj hZ) fun s' ⟨hZ', hz'⟩ => ?_
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by show s'.zf.map (!·) = _; rw [hz']; simp [hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by show s'.zf.map (!·) = _; rw [hz']; simp [hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The compression of the buffer. -/
theorem times8 (x : BitVec 32) : x + x + (x + x) + (x + x + (x + x)) = x <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem writeW_bswap (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (bswap w) = VG.WriteBytes.writeBytes m a (wordBytes w) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes, ← VG.Proof.Sha256.X86.Stream.bswap_bytes]; rfl

/-- The two words of the message length in bits, in order of their bytes. -/
abbrev lenL (s₀ : State) : List Byte :=
  wordBytes ((arg s₀ 2 <<< 3) ||| (arg s₀ 1 >>> 29)) ++ wordBytes (arg s₀ 1 <<< 3)

/-- Storing the message length in bits, big-endian, at `state[88..96)`. -/
theorem len_ok {s₀ : State} (hp : VG.Proof.Sha256.X86.Stream.Finalize.Pre s₀) {s : State} (hC : VG.Proof.Sha256.X86.Stream.Finalize.Common s₀ s) :
    WP isa (.block lengthStore) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mem = VG.WriteBytes.writeBytes s.mem (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32 + BitVec.ofNat 64 56) (VG.Proof.Sha256.X86.Stream.Finalize.lenL s₀) := by
  have hst := hp.st_fit; have hsc := hp.scr_fit
  have rin : ∀ d, d + 4 ≤ 160 → InRegions (s.rd ++ s.wr) (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d) 4 :=
    fun d hd => ⟨VG.Proof.Sha256.X86.Stream.Finalize.scR s₀, by simp [hC.rd, hC.wr, hp.wr], hp.scr_in hd⟩
  have hout : ∀ o, o + 4 ≤ 96 → InRegions s.wr (addr (VG.Proof.Sha256.X86.Stream.Finalize.st s₀) o) 4 :=
    fun o ho => ⟨VG.Proof.Sha256.X86.Stream.Finalize.stR s₀, by simp [hC.wr, hp.wr], VG.Proof.Sha256.X86.Stream.contains_addr ho (by omega) hst⟩
  unfold lengthStore
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 128) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, hC.ebp]) (rin 128 (by omega)) fun s₁ u₁ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 132) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, u₁.other _ (by decide), hC.ebp])
    (by rw [u₁.rd, u₁.wr]; exact rin 132 (by omega)) fun s₂ u₂ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_add fun s₃ u₃ => VG.Proof.Sha256.X86.Stream.wp_add fun s₄ u₄ => VG.Proof.Sha256.X86.Stream.wp_add fun s₅ u₅ => VG.Proof.Sha256.X86.Stream.wp_mov fun s₆ u₆ =>
    VG.Proof.Sha256.X86.Stream.wp_shr (by decide) fun s₇ u₇ => VG.Proof.Sha256.X86.Stream.wp_or fun s₈ u₈ => VG.Proof.Sha256.X86.Stream.wp_add fun s₉ u₉ => VG.Proof.Sha256.X86.Stream.wp_add fun s₁₀ u₁₀ =>
    VG.Proof.Sha256.X86.Stream.wp_add fun s₁₁ u₁₁ => VG.Proof.Sha256.X86.Stream.wp_bswap fun s₁₂ u₁₂ => ?_
  have g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s₁₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₁₂.other r h2, u₁₁.other r h1, u₁₀.other r h1, u₉.other r h1, u₈.other r h2, u₇.other r h3,
      u₆.other r h3, u₅.other r h2, u₄.other r h2, u₃.other r h2, u₂.other r h2, u₁.other r h1]
  have m₁₂ : s₁₂.mem = s.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c2 : s₂.gpr .ecx = arg s₀ 2 := by rw [u₂.gpr, u₁.mem, hC.hi]
  have a2 : s₂.gpr .eax = arg s₀ 1 := by rw [u₂.other _ (by decide), u₁.gpr, hC.lo]
  have c5 : s₅.gpr .ecx = arg s₀ 2 <<< 3 := by rw [u₅.gpr, u₄.gpr, u₃.gpr, c2, VG.Proof.Sha256.X86.Stream.Finalize.times8]
  have a5 : s₅.gpr .eax = arg s₀ 1 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), a2]
  have d7 : s₇.gpr .edx = arg s₀ 1 >>> 29 := by rw [u₇.gpr, u₆.gpr, a5]
  have c8 : s₈.gpr .ecx = (arg s₀ 2 <<< 3) ||| (arg s₀ 1 >>> 29) := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), c5, d7]
  have a11 : s₁₁.gpr .eax = arg s₀ 1 <<< 3 := by
    rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), a5,
      VG.Proof.Sha256.X86.Stream.Finalize.times8]
  have c12 : s₁₂.gpr .ecx = bswap ((arg s₀ 2 <<< 3) ||| (arg s₀ 1 >>> 29)) := by
    rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), c8]
  have wr₁₂ : s₁₂.wr = s.wr := by
    rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have rd₁₂ : s₁₂.rd = s.rd := by
    rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have ebx₁₂ : s₁₂.gpr .ebx = VG.Proof.Sha256.X86.Stream.Finalize.st s₀ := by rw [g _ (by decide) (by decide) (by decide), hC.ebx]
  refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.st s₀) 88) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, ebx₁₂]) (by rw [wr₁₂]; exact hout 88 (by omega))
    fun s₁₃ u₁₃ => VG.Proof.Sha256.X86.Stream.wp_bswap fun s₁₄ u₁₄ => VG.Proof.Sha256.X86.Stream.wp_store (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.st s₀) 92)
      (by rw [VG.Proof.Sha256.X86.Stream.ea_at, u₁₄.other _ (by decide), u₁₃.gpr, ebx₁₂])
      (by rw [u₁₄.wr, u₁₃.wr, wr₁₂]; exact hout 92 (by omega)) fun s₁₅ u₁₅ => WP.block_nil ?_
  refine ⟨fun r h1 h2 h3 => by rw [u₁₅.gpr, u₁₄.other r h1, u₁₃.gpr, g r h1 h2 h3],
    by rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, rd₁₂], by rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, wr₁₂], ?_⟩
  have a14 : s₁₄.gpr .eax = bswap (arg s₀ 1 <<< 3) := by
    rw [u₁₄.gpr, u₁₃.gpr, u₁₂.other _ (by decide), a11]
  rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, a14, c12, m₁₂, VG.Proof.Sha256.X86.Stream.Finalize.writeW_bswap, VG.Proof.Sha256.X86.Stream.Finalize.writeW_bswap,
    addr_eq (show (VG.Proof.Sha256.X86.Stream.Finalize.st s₀).toNat + 88 < 2 ^ 32 by omega), addr_eq (show (VG.Proof.Sha256.X86.Stream.Finalize.st s₀).toNat + 92 < 2 ^ 32 by omega),
    show VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + BitVec.ofNat 64 92 = VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + BitVec.ofNat 64 88 +
      BitVec.ofNat 64 (wordBytes ((arg s₀ 2 <<< 3) ||| (arg s₀ 1 >>> 29))).length by
      rw [BitVec.add_assoc]; rfl, VG.WriteBytes.writeBytes_append _ _ _ _ (by simp [wordBytes]),
    show VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32 + BitVec.ofNat 64 56 = VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + BitVec.ofNat 64 88 by rw [BitVec.add_assoc]; rfl]

/-- Point `eax` at the buffer. -/
theorem args_ok {s₀ : State} {s : State} (hC : VG.Proof.Sha256.X86.Stream.Finalize.Common s₀ s) :
    WP isa (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 32)]) s fun s' =>
      VG.Proof.Sha256.X86.Stream.Finalize.Common s₀ s' ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.gpr .eax = VG.Proof.Sha256.X86.Stream.Finalize.st s₀ + BitVec.ofNat 32 32 ∧
        Frame [VG.Proof.Sha256.X86.Stream.Finalize.argR s₀] s.mem s'.mem := by
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₁ u₁ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₂ u₂ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r h => by rw [u₂.other r h, u₁.other r h]
  have hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨hC.of_gpr (fun r hr => g₂ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) hm
    (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]), g₂, by rw [u₂.gpr, u₁.gpr, hC.ebx]; rfl,
    by rw [hm]; exact Frame.refl _ _⟩

/-- The loop's postcondition for one iteration. -/
def Step (s₀ : State) (k : Nat) (s : State) : Prop :=
  (eval .e s = some false ∧ VG.Proof.Sha256.X86.Stream.Finalize.Done s₀ s) ∨ (eval .e s = some true ∧ k = 1 ∧ VG.Proof.Sha256.X86.Stream.Finalize.LInv s₀ 0 0 s)

theorem regs3 {r : Reg} (hr : r ∈ [Reg.ebx, .ebp, .esp]) : r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx ∧ r ≠ .edi ∧ r ≠ .esi := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> decide

def proMem (s₀ : State) : Mem :=
  ((((((s₀.mem.writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 112) (s₀.gpr .ebx)).writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 116) (s₀.gpr .esi)).writeW
    (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 120) (s₀.gpr .edi)).writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 124) (s₀.gpr .ebp)).writeW
    (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 128) (arg s₀ 1)).writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 132) (arg s₀ 2)).writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 136) (VG.Proof.Sha256.X86.Stream.Finalize.out s₀)

theorem proMem_frame {s₀ : State} (hp : VG.Proof.Sha256.X86.Stream.Finalize.Pre s₀) : Frame [VG.Proof.Sha256.X86.Stream.Finalize.scR s₀] s₀.mem (VG.Proof.Sha256.X86.Stream.Finalize.proMem s₀) := by
  have c : ∀ d, d + 4 ≤ 160 → (VG.Proof.Sha256.X86.Stream.Finalize.scR s₀).Contains (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d) (32 / 8) := fun d hd => hp.scr_in hd
  simp only [VG.Proof.Sha256.X86.Stream.Finalize.proMem]
  exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 112 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 116 (by omega))).writeW (List.mem_singleton_self _) _
    (c 120 (by omega))).writeW (List.mem_singleton_self _) _ (c 124 (by omega))).writeW
    (List.mem_singleton_self _) _ (c 128 (by omega))).writeW (List.mem_singleton_self _) _
    (c 132 (by omega))).writeW (List.mem_singleton_self _) _ (c 136 (by omega))

theorem proMem_words {s₀ : State} (hp : VG.Proof.Sha256.X86.Stream.Finalize.Pre s₀) :
    VG.Proof.Sha256.X86.Stream.Finalize.Saved s₀ (VG.Proof.Sha256.X86.Stream.Finalize.proMem s₀) ∧ (VG.Proof.Sha256.X86.Stream.Finalize.proMem s₀).readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 128) 32 = arg s₀ 1 ∧
      (VG.Proof.Sha256.X86.Stream.Finalize.proMem s₀).readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 132) 32 = arg s₀ 2 ∧ (VG.Proof.Sha256.X86.Stream.Finalize.proMem s₀).readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 136) 32 = VG.Proof.Sha256.X86.Stream.Finalize.out s₀ := by
  have hs := hp.scr_fit
  have w : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ 160 → e + 4 ≤ 160 → d + 4 ≤ e ∨ e + 4 ≤ d →
      (m.writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) e) v).readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d) 32 = m.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d) 32 :=
    fun m v d e h₁ h₂ h => VG.Proof.Sha256.X86.Stream.readW_writeW_addr m v (by omega) (by omega) h
  refine ⟨fun p hp' => ?_, ?_, ?_, ?_⟩
  · simp only [VG.Impl.Sha256.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp only [VG.Proof.Sha256.X86.Stream.Finalize.proMem] <;>
      rw [w _ _ _ 136 (by omega) (by omega) (by omega), w _ _ _ 132 (by omega) (by omega) (by omega),
        w _ _ _ 128 (by omega) (by omega) (by omega)]
    · rw [w _ _ 112 124 (by omega) (by omega) (by omega), w _ _ 112 120 (by omega) (by omega) (by omega),
        w _ _ 112 116 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
    · rw [w _ _ 116 124 (by omega) (by omega) (by omega), w _ _ 116 120 (by omega) (by omega) (by omega),
        Mem.readW_writeW_self32]
    · rw [w _ _ 120 124 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_self32]
  · simp only [VG.Proof.Sha256.X86.Stream.Finalize.proMem]
    rw [w _ _ 128 136 (by omega) (by omega) (by omega), w _ _ 128 132 (by omega) (by omega) (by omega),
      Mem.readW_writeW_self32]
  · simp only [VG.Proof.Sha256.X86.Stream.Finalize.proMem]
    rw [w _ _ 132 136 (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · simp only [VG.Proof.Sha256.X86.Stream.Finalize.proMem]; rw [Mem.readW_writeW_self32]

/-- The arguments, in memory that differs only in the scratch space. -/
theorem arg_read {s₀ : State} (hp : VG.Proof.Sha256.X86.Stream.Finalize.Pre s₀) {m : Mem} (hf : Frame [VG.Proof.Sha256.X86.Stream.Finalize.scR s₀] s₀.mem m) {e : Nat}
    (h₁ : 4 ≤ e) (h₂ : e + 4 ≤ 24) : m.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) e) 32 = s₀.mem.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) e) 32 :=
  hf.readW (Region.contains_self _ _) (by simpa using hp.a_scr.sub_left (hp.arg_sub h₁ h₂)) (by decide)

theorem prologue_ok {s₀ : State} (hp : VG.Proof.Sha256.X86.Stream.Finalize.Pre s₀) :
    WP isa (.seq (.block (([.mov .eax (.mem (at_ .esp 20))] : List Instr) ++ save .eax ++
      ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
       .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp 128) .ecx,
       .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp 132) .ecx,
       .mov .ecx (.mem (at_ .esp 16)), .store (at_ .ebp 136) .ecx,
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 63),
       .mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .edx 32) .cl, .alu .add .edi (.imm 1),
       .mov .esi (.imm 0), .alu .cmp .edi (.imm 57)] : List Instr)))
      (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))) s₀
      fun s => ∃ k, VG.Proof.Sha256.X86.Stream.Finalize.LInv s₀ k (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64 + 1) s := by
  have hst := hp.st_fit
  have hr : VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64 < 64 := Nat.mod_lt _ (by omega)
  have ain : ∀ e, 4 ≤ e → e + 4 ≤ 24 → ∀ t : State, t.rd = s₀.rd → t.wr = s₀.wr →
      InRegions (t.rd ++ t.wr) (addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) e) 4 :=
    fun e h₁ h₂ t hrd hwr => ⟨VG.Proof.Sha256.X86.Stream.Finalize.argR s₀, by simp [hrd, hwr, hp.wr], hp.arg_in h₁ h₂⟩
  have sout : ∀ d, d + 4 ≤ 160 → ∀ t : State, t.wr = s₀.wr → InRegions t.wr (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d) 4 :=
    fun d hd t hwr => ⟨VG.Proof.Sha256.X86.Stream.Finalize.scR s₀, by simp [hwr, hp.wr], hp.scr_in hd⟩
  have fw : ∀ {m : Mem}, Frame [VG.Proof.Sha256.X86.Stream.Finalize.scR s₀] s₀.mem m → ∀ d, d + 4 ≤ 160 → ∀ v : BitVec 32,
      Frame [VG.Proof.Sha256.X86.Stream.Finalize.scR s₀] s₀.mem (m.writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d) v) :=
    fun hf d hd v => hf.writeW (List.mem_singleton_self _) _ (hp.scr_in hd)
  simp only [List.cons_append, save, saved, List.map_cons, List.map_nil,
    List.nil_append]
  refine WP.seq ?_
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) 20) (VG.Proof.Sha256.X86.Stream.ea_at _ _ _) (ain 20 (by omega) (by omega) s₀ rfl rfl) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = VG.Proof.Sha256.X86.Stream.Finalize.scr s₀ := u₁.gpr
  refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 112) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, e₁]) (sout 112 (by omega) _ u₁.wr) fun s₂ u₂ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 116) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, u₂.gpr, e₁])
    (sout 116 (by omega) _ (by rw [u₂.wr, u₁.wr])) fun s₃ u₃ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 120) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, u₃.gpr, u₂.gpr, e₁])
    (sout 120 (by omega) _ (by rw [u₃.wr, u₂.wr, u₁.wr])) fun s₄ u₄ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 124) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, u₄.gpr, u₃.gpr, u₂.gpr, e₁])
    (sout 124 (by omega) _ (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := by rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₅ : s₅.gpr .esp = VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  have m₅ : s₅.mem = (((s₀.mem.writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 112) (s₀.gpr .ebx)).writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 116)
      (s₀.gpr .esi)).writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 120) (s₀.gpr .edi)).writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 124) (s₀.gpr .ebp) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₄.gpr, u₃.gpr, u₂.gpr, u₁.mem, u₁.other .ebx (by decide),
      u₁.other .esi (by decide), u₁.other .edi (by decide), u₁.other .ebp (by decide)]
  have f₅ : Frame [VG.Proof.Sha256.X86.Stream.Finalize.scR s₀] s₀.mem s₅.mem := by
    rw [m₅]; exact fw (fw (fw (fw (Frame.refl _ _) 112 (by omega) _) 116 (by omega) _) 120 (by omega) _)
      124 (by omega) _
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₆ u₆ => VG.Proof.Sha256.X86.Stream.wp_movm (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) 4) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, u₆.other _ (by decide), sp₅])
    (ain 4 (by omega) (by omega) s₆ (by rw [u₆.rd, rd₅]) (by rw [u₆.wr, wr₅])) fun s₇ u₇ => ?_
  have ebp₇ : s₇.gpr .ebp = VG.Proof.Sha256.X86.Stream.Finalize.scr s₀ := by rw [u₇.other _ (by decide), u₆.gpr, g₅, e₁]
  have sp₇ : s₇.gpr .esp = VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀ := by rw [u₇.other _ (by decide), u₆.other _ (by decide), sp₅]
  have ebx₇ : s₇.gpr .ebx = VG.Proof.Sha256.X86.Stream.Finalize.st s₀ := by
    rw [u₇.gpr, u₆.mem, VG.Proof.Sha256.X86.Stream.Finalize.arg_read hp f₅ (by omega) (by omega)]; rfl
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, rd₅]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, wr₅]
  have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  -- `count` and `out` into scratch.
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) 8) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, sp₇]) (ain 8 (by omega) (by omega) s₇ rd₇ wr₇)
    fun s₈ u₈ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 128) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, u₈.other _ (by decide), ebp₇])
    (sout 128 (by omega) _ (by rw [u₈.wr, wr₇])) fun s₉ u₉ => ?_
  have v₉ : s₉.mem = s₅.mem.writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 128) (arg s₀ 1) := by
    rw [u₉.mem, u₈.gpr, u₈.mem, m₇, VG.Proof.Sha256.X86.Stream.Finalize.arg_read hp f₅ (by omega) (by omega)]; rfl
  have f₉ : Frame [VG.Proof.Sha256.X86.Stream.Finalize.scR s₀] s₀.mem s₉.mem := by rw [v₉]; exact fw f₅ 128 (by omega) _
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) 12) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, u₉.gpr, u₈.other _ (by decide), sp₇])
    (ain 12 (by omega) (by omega) _ (by rw [u₉.rd, u₈.rd, rd₇]) (by rw [u₉.wr, u₈.wr, wr₇])) fun s₁₀ u₁₀ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 132) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide),
                                                                   ebp₇]) (sout 132 (by omega) _ (by rw [u₁₀.wr, u₉.wr, u₈.wr, wr₇])) fun s₁₁ u₁₁ => ?_
  have v₁₁ : s₁₁.mem = s₉.mem.writeW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 132) (arg s₀ 2) := by
    rw [u₁₁.mem, u₁₀.gpr, u₁₀.mem, VG.Proof.Sha256.X86.Stream.Finalize.arg_read hp f₉ (by omega) (by omega)]; rfl
  have f₁₁ : Frame [VG.Proof.Sha256.X86.Stream.Finalize.scR s₀] s₀.mem s₁₁.mem := by rw [v₁₁]; exact fw f₉ 132 (by omega) _
  have g₁₁ : ∀ r, r ≠ .ecx → s₁₁.gpr r = s₇.gpr r := fun r h => by
    rw [u₁₁.gpr, u₁₀.other r h, u₉.gpr, u₈.other r h]
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) 16) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, g₁₁ _ (by decide), sp₇])
    (ain 16 (by omega) (by omega) _ (by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇])
      (by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇])) fun s₁₂ u₁₂ => ?_
  refine VG.Proof.Sha256.X86.Stream.wp_store (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) 136) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, u₁₂.other _ (by decide), g₁₁ _ (by decide), ebp₇])
    (sout 136 (by omega) _ (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇])) fun s₁₃ u₁₃ => ?_
  have m₁₃ : s₁₃.mem = VG.Proof.Sha256.X86.Stream.Finalize.proMem s₀ := by
    rw [u₁₃.mem, u₁₂.gpr, u₁₂.mem, VG.Proof.Sha256.X86.Stream.Finalize.arg_read hp f₁₁ (by omega) (by omega), v₁₁, v₉, m₅]; rfl
  have g₁₃ : ∀ r, r ≠ .ecx → s₁₃.gpr r = s₇.gpr r := fun r h => by rw [u₁₃.gpr, u₁₂.other r h, g₁₁ r h]
  have rd₁₃ : s₁₃.rd = s₀.rd := by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇]
  have wr₁₃ : s₁₃.wr = s₀.wr := by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇]
  -- The `0x80` byte.
  refine VG.Proof.Sha256.X86.Stream.wp_movm (a := addr (VG.Proof.Sha256.X86.Stream.Finalize.esp₀ s₀) 8) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, g₁₃ _ (by decide), sp₇])
    (ain 8 (by omega) (by omega) _ rd₁₃ wr₁₃) fun s₁₄ u₁₄ => VG.Proof.Sha256.X86.Stream.wp_andi fun s₁₅ u₁₅ => ?_
  have edi₁₅ : s₁₅.gpr .edi = BitVec.ofNat 32 (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64) := by
    rw [u₁₅.gpr, u₁₄.gpr, m₁₃, VG.Proof.Sha256.X86.Stream.Finalize.arg_read hp (VG.Proof.Sha256.X86.Stream.Finalize.proMem_frame hp) (by omega) (by omega), VG.Proof.Sha256.X86.Stream.and63, VG.Proof.Sha256.X86.Stream.Finalize.cnt_mod]
    rfl
  refine VG.Proof.Sha256.X86.Stream.wp_mov fun s₁₆ u₁₆ => VG.Proof.Sha256.X86.Stream.wp_add fun s₁₇ u₁₇ => VG.Proof.Sha256.X86.Stream.wp_movi fun s₁₈ u₁₈ => ?_
  have edx₁₈ : s₁₈.gpr .edx = VG.Proof.Sha256.X86.Stream.Finalize.st s₀ + BitVec.ofNat 32 (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64) := by
    rw [u₁₈.other _ (by decide), u₁₇.gpr, u₁₆.gpr, u₁₆.other _ (by decide), edi₁₅, u₁₅.other _ (by decide),
      u₁₄.other _ (by decide), g₁₃ _ (by decide), ebx₇]
  have hq : addr (s₁₈.gpr .edx) 32 = VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32 + BitVec.ofNat 64 (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64) := by
    rw [edx₁₈, VG.Proof.Sha256.X86.Stream.addr_add_ofNat (by omega), VG.Proof.Sha256.X86.Stream.Finalize.st_add, Nat.add_comm]
  have hout : InRegions s₁₈.wr (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32 + BitVec.ofNat 64 (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64)) 1 :=
    ⟨VG.Proof.Sha256.X86.Stream.Finalize.stR s₀, by simp [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, wr₁₃, hp.wr], by
      rw [VG.Proof.Sha256.X86.Stream.Finalize.st_add]; exact contains_offset (by omega) (by omega)⟩
  refine VG.Proof.Sha256.X86.Stream.wp_store8 (r := .cl) (a := VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32 + BitVec.ofNat 64 (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64)) (by rw [VG.Proof.Sha256.X86.Stream.ea_at, hq]) hout
    fun s₁₉ u₁₉ => VG.Proof.Sha256.X86.Stream.wp_addi fun s₂₀ u₂₀ => VG.Proof.Sha256.X86.Stream.wp_movi fun s₂₁ u₂₁ => VG.Proof.Sha256.X86.Stream.wp_cmpi fun s₂₂ f₂₂ cf₂₂ _ => WP.block_nil ?_
  have hm₁₉ : s₁₉.mem = VG.WriteBytes.writeBytes (VG.Proof.Sha256.X86.Stream.Finalize.proMem s₀) (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32 + BitVec.ofNat 64 (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64)) [0x80] := by
    rw [u₁₉.mem, show Reg8.cl.reg = Reg.ecx from rfl, u₁₈.gpr, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem, m₁₃,
      ← List.nil_append [(0x80 : Byte)], VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp), VG.WriteBytes.writeBytes_nil]
    simp
  have hm₂₂ : s₂₂.mem = s₁₉.mem := by rw [f₂₂.mem, u₂₁.mem, u₂₀.mem]
  have hfb : Frame [VG.Proof.Sha256.X86.Stream.Finalize.stR s₀] (VG.Proof.Sha256.X86.Stream.Finalize.proMem s₀) s₁₉.mem := by rw [hm₁₉]; exact VG.Proof.Sha256.X86.Stream.Finalize.buf_frame _ (by simp; omega)
  have keep : ∀ r, r ≠ .ecx → r ≠ .edi → r ≠ .edx → r ≠ .esi → s₂₂.gpr r = s₇.gpr r := fun r h1 h2 h3 h4 => by
    rw [f₂₂.gpr, u₂₁.other r h4, u₂₀.other r h2, u₁₉.gpr, u₁₈.other r h1, u₁₇.other r h3, u₁₆.other r h3,
      u₁₅.other r h2, u₁₄.other r h2, g₁₃ r h1]
  obtain ⟨hsv, hlo, hhi, hou⟩ := VG.Proof.Sha256.X86.Stream.Finalize.proMem_words hp
  have word : ∀ d, d + 4 ≤ 160 → s₂₂.mem.readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d) 32 = (VG.Proof.Sha256.X86.Stream.Finalize.proMem s₀).readW (addr (VG.Proof.Sha256.X86.Stream.Finalize.scr s₀) d) 32 :=
    fun d hd => by
      rw [hm₂₂]
      exact hfb.readW (Region.contains_self _ _) (by simpa using hp.st_scr.symm.sub_left (hp.scr_sub hd))
        (by decide)
  have hC : VG.Proof.Sha256.X86.Stream.Finalize.Common s₀ s₂₂ :=
    ⟨by rw [f₂₂.rd, u₂₁.rd, u₂₀.rd, u₁₉.rd, u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, rd₁₃],
      by rw [f₂₂.wr, u₂₁.wr, u₂₀.wr, u₁₉.wr, u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, wr₁₃],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), ebx₇],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), ebp₇],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), sp₇],
      by rw [hm₂₂]; exact ((VG.Proof.Sha256.X86.Stream.Finalize.proMem_frame hp).mono (by simp)).trans (hfb.mono (by simp)),
      fun p hp' => by
        have hd : 112 ≤ p.2 ∧ p.2 + 4 ≤ 128 := by
          simp only [VG.Impl.Sha256.X86.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
          rcases hp' with rfl | rfl | rfl | rfl <;> simp
        rw [word _ (by omega)]; exact hsv p hp',
      by rw [word 128 (by omega)]; exact hlo, by rw [word 132 (by omega)]; exact hhi,
      by rw [word 136 (by omega)]; exact hou⟩
  have edi₂₂ : s₂₂.gpr .edi = BitVec.ofNat 32 (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64 + 1) := by
    rw [f₂₂.gpr, u₂₁.other _ (by decide), u₂₀.gpr, u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), edi₁₅, VG.Proof.Sha256.X86.Stream.ofNat_succ]
  have hcf : s₂₂.cf = some (decide (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64 + 1 < 57)) := by
    rw [cf₂₂, ← f₂₂.gpr, edi₂₂, VG.Proof.Sha256.X86.Stream.toNat_ofNat_lt (by omega)]; rfl
  -- The facts about the buffer.
  have hst : stateAt s₂₂.mem (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀) = stateAt s₀.mem (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀) := by
    apply stateAt_congr
    intro i hi
    rw [hm₂₂, hm₁₉, VG.Proof.Sha256.X86.Stream.Finalize.st_add, VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by simp; omega)]
    exact VG.Proof.Sha256.X86.Stream.frame_bytes (VG.Proof.Sha256.X86.Stream.Finalize.proMem_frame hp) (R := VG.Proof.Sha256.X86.Stream.Finalize.stR s₀) (by simpa using hp.st_scr) (by simp) (by show i < 96; omega)
  have hbytes : ∀ m, VG.Proof.Sha256.X86.Stream.Finalize.R₀ s₀ m → bytesAt s₂₂.mem (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32) (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64 + 1) = rest m ++ [0x80] := by
    intro m hm
    have e := bytesAt_writeBytes (VG.Proof.Sha256.X86.Stream.Finalize.proMem s₀) (VG.Proof.Sha256.X86.Stream.Finalize.stA s₀ + 32) (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₂₂, hm₁₉, e]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    rw [VG.Proof.Sha256.X86.Stream.Finalize.st_add]
    exact VG.Proof.Sha256.X86.Stream.frame_bytes (VG.Proof.Sha256.X86.Stream.Finalize.proMem_frame hp) (R := VG.Proof.Sha256.X86.Stream.Finalize.stR s₀) (by simpa using hp.st_scr) (by simp)
      (by show 32 + i < 96; have := hm.length; omega)
  have hesi : s₂₂.gpr .esi = 0 := by rw [f₂₂.gpr, u₂₁.gpr]
  refine WP.ite (!decide (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64 + 1 < 57)) (by show s₂₂.cf.map (!·) = _; rw [hcf]; rfl)
    (fun hb => ?_) (fun hb => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb
    refine VG.Proof.Sha256.X86.Stream.wp_movi fun s₂₃ u₂₃ => WP.block_nil ⟨1, hC.of_gpr (fun r hr => u₂₃.other r (VG.Proof.Sha256.X86.Stream.Finalize.regs3 hr).2.2.2.2)
      u₂₃.mem u₂₃.rd u₂₃.wr, (Nat.le_refl _), by omega, by rw [u₂₃.other _ (by decide), edi₂₂], by rw [u₂₃.gpr]; rfl,
      fun m hm => ?_⟩
    simp only [↓reduceIte]
    rw [hash_two (by rw [← hm.length]; omega), VG.Proof.Sha256.X86.Stream.Finalize.Fin1, u₂₃.mem, hbytes m hm, hst, hm.1.1,
      ← hm.length, show 64 - (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64 + 1) = 63 - VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64 by omega]
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    refine WP.block_nil ⟨0, hC, by omega, by omega, edi₂₂, by rw [hesi]; rfl, fun m hm => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [hash_one (by rw [← hm.length]; omega), VG.Proof.Sha256.X86.Stream.Finalize.Fin0, hbytes m hm, hst, hm.1.1,
      ← hm.length, show 56 - (VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64 + 1) = 55 - VG.Proof.Sha256.X86.Stream.Finalize.cnt s₀ % 64 by omega]

theorem seq_assoc {M : ISA} {a b c : Prog M} {s : M.State} {Q : M.State → Prop} :
    WP M (.seq (.seq a b) c) s Q ↔ WP M (.seq a (.seq b c)) s Q := by
  simp only [WP.seq_iff]

theorem argWord_eq {s : State} (hsp : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) {k : Nat} (hk : k < 20) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by omega), addr_eq (by omega), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega

end VG.Proof.Sha256.X86.Stream.Finalize

end
