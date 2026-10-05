import VerifiedGarbage.Impl.Mont.AArch64
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddVerified
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.AArch64.Words`. -/
section

/-!
# Montgomery arithmetic on AArch64: words in registers and in the working space

Numbers of several words: in registers (`regsVal`, little-endian over a list
of registers) and in the working space (`wordsVal`), which is `size` bytes at
`base`, the value of `x0` (`Scr`). The loads and stores of the arithmetic
(at offsets that are multiples of 8, as `ldr` and `str` encode them), and
what they leave unchanged.
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- The registers `rs` read as a little-endian number. -/
def regsVal (s : State) : List Reg → Nat
  | [] => 0
  | r :: rs => (s.gpr r).toNat + 2 ^ 64 * VG.Proof.Mont.AArch64.regsVal s rs

theorem regsVal_lt (s : State) (rs : List Reg) : VG.Proof.Mont.AArch64.regsVal s rs < 2 ^ (64 * rs.length) := by
  induction rs with
  | nil => exact Nat.one_pos
  | cons r rs ih =>
    rw [List.length_cons, pow64_succ]
    exact word_add_lt (s.gpr r).isLt ih

theorem regsVal_append (s : State) (rs qs : List Reg) :
    VG.Proof.Mont.AArch64.regsVal s (rs ++ qs) = VG.Proof.Mont.AArch64.regsVal s rs + 2 ^ (64 * rs.length) * VG.Proof.Mont.AArch64.regsVal s qs := by
  induction rs with
  | nil => simp only [List.nil_append, VG.Proof.Mont.AArch64.regsVal, List.length_nil, Nat.mul_zero, Nat.pow_zero,
      Nat.one_mul, Nat.zero_add]
  | cons r rs ih =>
    rw [List.cons_append, VG.Proof.Mont.AArch64.regsVal, ih, VG.Proof.Mont.AArch64.regsVal, List.length_cons, pow64_succ, Nat.mul_add,
      Nat.mul_assoc]
    omega

theorem regsVal_congr {s s' : State} {rs : List Reg} (h : ∀ r ∈ rs, s'.gpr r = s.gpr r) :
    VG.Proof.Mont.AArch64.regsVal s' rs = VG.Proof.Mont.AArch64.regsVal s rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [VG.Proof.Mont.AArch64.regsVal, h r (List.mem_cons_self ..), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

/-- The working space: `x0` holds its base `base`, it is writable, it does not
wrap around, and every offset in it can be encoded in a load or store. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  x0 : s.gpr .x0 = base
  wr : (⟨base, size⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 64
  enc : size ≤ 32768

theorem Scr.contains {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {d n : Nat}
    (h : d + n ≤ size) (hn : 0 < n) : (⟨base, size⟩ : Region).Contains (VG.Proof.Mont.off base d) n :=
  Offset.contains_base base h (by have := hs.nowrap; omega)

theorem Scr.ld {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8 := by
  rw [hs.x0]
  exact ⟨_, List.mem_append_right _ hs.wr, hs.contains hd (by decide)⟩

theorem Scr.st {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 8 := by
  rw [hs.x0]
  exact ⟨_, hs.wr, hs.contains hd (by decide)⟩

theorem Scr.enc8 {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (ha : d % 8 = 0) : d % 8 = 0 ∧ d < 32768 :=
  ⟨ha, by have := hs.enc; omega⟩

/-- A load of the word at offset `d`. -/
theorem exec_ld {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (ha : d % 8 = 0) (t : Reg) :
    exec (VG.Impl.Mont.AArch64.ld t d) s = some (s.write .x t (VG.Proof.Mont.word s.mem base d)) := by
  rw [VG.Impl.Mont.AArch64.ld, exec_ldr_x (hs.enc8 hd ha) (hs.ld hd), hs.x0]

/-- A store of a register at offset `d`. -/
theorem exec_st {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (ha : d % 8 = 0) (t : Reg) :
    exec (VG.Impl.Mont.AArch64.st t d) s = some { s with
                                    mem := s.mem.writeW (VG.Proof.Mont.off base d) (s.gpr t) } := by
  rw [VG.Impl.Mont.AArch64.st, exec_str_x (hs.enc8 hd ha) (hs.st hd), hs.x0]

/-- `t = [x0 + d]`. -/
theorem ld_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (ha : d % 8 = 0) (t : Reg) :
    WP isa (.block [VG.Impl.Mont.AArch64.ld t d]) s fun s' =>
      s'.gpr t = VG.Proof.Mont.word s.mem base d ∧ Keeps [t] s s' ∧ s'.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, VG.Proof.Mont.AArch64.exec_ld hs hd ha, runStep_some, runBlock_nil,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- `[x0 + d] = t`. -/
theorem st_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (ha : d % 8 = 0) (t : Reg) :
    WP isa (.block [VG.Impl.Mont.AArch64.st t d]) s fun s' => s' = { s with
                                                       mem := s.mem.writeW (VG.Proof.Mont.off base d) (s.gpr t) } := by
  apply WP.of_runBlock
  simp only [runBlock_cons, VG.Proof.Mont.AArch64.exec_st hs hd ha, runStep_some, runBlock_nil, Option.some.injEq,
    exists_eq_left']

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : VG.Proof.Mont.AArch64.Scr s base size) (h : Keeps rs s s') (hr : .x0 ∉ rs) : VG.Proof.Mont.AArch64.Scr s' base size :=
  ⟨(h.gpr _ hr).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap, hs.enc⟩

/-- What an operation keeps: the registers but `rs`, and the regions; memory
may change. -/
structure KeepRegs (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem KeepRegs.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Mont.AArch64.KeepRegs rs s₁ s₂)
    (h₂ : VG.Proof.Mont.AArch64.KeepRegs rs s₂ s₃) : VG.Proof.Mont.AArch64.KeepRegs rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem KeepRegs.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.Mont.AArch64.KeepRegs rs s s')
    (hr : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Mont.AArch64.KeepRegs rs' s s' :=
  ⟨fun r h' => h.gpr r fun hm => h' (hr r hm), h.rd, h.wr, h.sp⟩

theorem Keeps.regs {rs : List Reg} {s s' : State} (h : Keeps rs s s') : VG.Proof.Mont.AArch64.KeepRegs rs s s' :=
  ⟨h.gpr, h.rd, h.wr, h.sp⟩

theorem Scr.of_keepRegs {rs : List Reg} {s s' : State} {base : Addr} {size : Nat}
    (hs : VG.Proof.Mont.AArch64.Scr s base size) (h : VG.Proof.Mont.AArch64.KeepRegs rs s s') (hr : .x0 ∉ rs) : VG.Proof.Mont.AArch64.Scr s' base size :=
  ⟨(h.gpr _ hr).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap, hs.enc⟩

end VG.Proof.Mont.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.AArch64.Row`. -/
section

/-!
# Montgomery arithmetic on AArch64: rows of products

A piece of a row (`Piece`) puts the low or high word of `x w`, `x 2^k`'s
low word or `⌊x / 2^k⌋` into `x2`, or is `x` itself (`piece_ok`); a chain
adds pieces to consecutive words with the carry flag between them
(`chainCode_ok`, `chainSkip_ok`); and a row (`row_ok`) adds `x · W` to the
words `ts` with two chains, whose pieces add up to `x W`
(`pieceAB`, `pieces_sum`), if the sum fits.
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-- Registers the arithmetic can use for words: distinct, and none of the
registers it uses otherwise (`x0`–`x7`, `x16`, `x17`). -/
def Fresh (ts : List Reg) : Prop :=
  ts.Nodup ∧ ∀ t ∈ ts, t ∉ [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17]

theorem Fresh.tail {t : Reg} {ts : List Reg} (h : VG.Proof.Mont.AArch64.Fresh (t :: ts)) : VG.Proof.Mont.AArch64.Fresh ts :=
  ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

theorem Fresh.head {t : Reg} {ts : List Reg} (h : VG.Proof.Mont.AArch64.Fresh (t :: ts)) :
    t ∉ ts ∧ t ∉ [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17] :=
  ⟨(List.nodup_cons.mp h.1).1, h.2 t (List.mem_cons_self ..)⟩

/-- Closes `∀ r ∈ rs, r ∈ rs'` for literal lists of registers and variables. -/
macro "sub_regs" : tactic => `(tactic| (intro q hq; simp only [List.mem_cons, List.mem_append,
  List.mem_singleton, List.not_mem_nil, or_false] at hq ⊢; grind))

/-! ## Pieces -/

/-- The value of a source's word. -/
def _root_.VG.Impl.Mont.AArch64.Src.val (s : State) (base : Addr) : Src → Nat
  | .reg r => (s.gpr r).toNat
  | .mem d => (VG.Proof.Mont.word s.mem base d).toNat
  | .imm v => v.toNat

/-- A source the code can read: a register other than `x2` and `x3` (which
the pieces use), or an aligned word of the working space. -/
def _root_.VG.Impl.Mont.AArch64.Src.Ok (size : Nat) : Src → Prop
  | .reg r => r ≠ .x2 ∧ r ≠ .x3
  | .mem d => d + 8 ≤ size ∧ d % 8 = 0
  | .imm _ => True

/-- The register a source reads, if any. -/
def _root_.VG.Impl.Mont.AArch64.Src.reads : Src → Option Reg
  | .reg r => some r
  | _ => none

/-- The value of a piece of the multiplier `x`. -/
def _root_.VG.Impl.Mont.AArch64.Piece.val (x : Nat) (s : State) (base : Addr) : Piece → Nat
  | .lo src => x * src.val s base % 2 ^ 64
  | .hi src => x * src.val s base / 2 ^ 64
  | .shl k => x * 2 ^ k % 2 ^ 64
  | .shr k => x / 2 ^ k
  | .self => x

/-- A piece the code can compute. -/
def _root_.VG.Impl.Mont.AArch64.Piece.Ok (size : Nat) : Piece → Prop
  | .lo src => src.Ok size
  | .hi src => src.Ok size
  | .shl k => k < 64
  | .shr k => k < 64
  | .self => True

/-- The register a piece reads besides the multiplier, if any. -/
def _root_.VG.Impl.Mont.AArch64.Piece.reads : Piece → Option Reg
  | .lo src => src.reads
  | .hi src => src.reads
  | _ => none

/-- A piece's value, or zero. -/
def optVal (x : Nat) (s : State) (base : Addr) : Option Piece → Nat
  | none => 0
  | some p => p.val x s base

theorem _root_.VG.Impl.Mont.AArch64.Src.val_lt (s : State) (base : Addr) (src : Src) : src.val s base < 2 ^ 64 := by
  cases src with
  | reg r => exact (s.gpr r).isLt
  | mem d => exact (VG.Proof.Mont.word s.mem base d).isLt
  | imm v => exact v.isLt

theorem _root_.VG.Impl.Mont.AArch64.Src.val_congr {s s' : State} {base : Addr} {src : Src} (hm : s'.mem = s.mem)
    (hr : ∀ r ∈ src.reads, s'.gpr r = s.gpr r) : src.val s' base = src.val s base := by
  cases src with
  | reg r => simp only [Src.val, hr r rfl]
  | mem d => simp only [Src.val, hm]
  | imm v => rfl

theorem _root_.VG.Impl.Mont.AArch64.Piece.val_congr {s s' : State} {base : Addr} {p : Piece} (x : Nat) (hm : s'.mem = s.mem)
    (hr : ∀ r ∈ p.reads, s'.gpr r = s.gpr r) : p.val x s' base = p.val x s base := by
  cases p with
  | lo src => simp only [Piece.val, Src.val_congr hm hr]
  | hi src => simp only [Piece.val, Src.val_congr hm hr]
  | _ => rfl

theorem optVal_congr {s s' : State} {base : Addr} {o : Option Piece} (x : Nat)
    (hm : s'.mem = s.mem) (hr : ∀ p ∈ o, ∀ r ∈ p.reads, s'.gpr r = s.gpr r) :
    VG.Proof.Mont.AArch64.optVal x s' base o = VG.Proof.Mont.AArch64.optVal x s base o := by
  cases o with
  | none => rfl
  | some p => exact Piece.val_congr x hm (hr p rfl)

/-- `r = v`, keeping the carry flag. -/
theorem const64c_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (const64 r v)) s fun t => t.gpr r = v ∧ Keeps [r] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [const64, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨movz_movk64' v, ⟨?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  intro r' hr
  have h : r' ≠ r := by simpa only [List.mem_singleton] using hr
  simp only [RegUpd.gpr_write_of_ne _ _ _ h]

/-- The source's word, fetched. -/
theorem fetch_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {src : Src}
    (h : src.Ok size) :
    WP isa (.block src.fetch) s fun s' =>
      (s'.gpr src.out).toNat = src.val s base ∧ Keeps [.x3] s s' ∧ s'.c = s.c := by
  cases src with
  | reg r => exact WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  | mem d =>
    refine WP.mono (VG.Proof.Mont.AArch64.ld_ok hs h.1 h.2 .x3) fun s' ⟨e, k, c⟩ => ⟨?_, k, c⟩
    simp only [Src.out, Src.val, e]
  | imm v =>
    refine WP.mono (VG.Proof.Mont.AArch64.const64c_ok s .x3 v) fun s' ⟨e, k, c⟩ => ⟨?_, k, c⟩
    simp only [Src.out, Src.val, e]

theorem _root_.VG.Impl.Mont.AArch64.Src.out_ne {size : Nat} {src : Src} (h : src.Ok size) : src.out ≠ .x2 := by
  cases src with
  | reg r => exact h.1
  | mem _ => simp only [Src.out]; decide
  | imm _ => simp only [Src.out]; decide

/-- The piece of the multiplier `x`, into `p.reg x`. -/
theorem piece_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) {x : Reg}
    (hx3 : x ≠ .x3) {p : Piece} (hp : p.Ok size) :
    WP isa (.block (p.code x)) s fun s' =>
      (s'.gpr (p.reg x)).toNat = p.val (s.gpr x).toNat s base ∧ Keeps [.x2, .x3] s s' ∧
        s'.c = s.c := by
  cases p with
  | lo src =>
    rw [Piece.code, WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.AArch64.fetch_ok hs hp) fun s₁ ⟨e₁, k₁, c₁⟩ => ?_
    have hx : s₁.gpr x = s.gpr x := k₁.gpr x (by simpa using hx3)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Option.some.injEq,
      exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩, c₁⟩
    · simp only [Piece.reg, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.toNat_mul, hx, e₁,
        Piece.val]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [RegUpd.gpr_write_of_ne _ _ _ hr.1, k₁.gpr r (by simpa using hr.2)]
  | hi src =>
    rw [Piece.code, WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.AArch64.fetch_ok hs hp) fun s₁ ⟨e₁, k₁, c₁⟩ => ?_
    have hx : s₁.gpr x = s.gpr x := k₁.gpr x (by simpa using hx3)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩, c₁⟩
    · simp only [Piece.reg, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.toNat_ofNat, hx, e₁,
        Piece.val]
      have := (s.gpr x).isLt
      have := Src.val_lt s base src
      exact Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' ‹_› ‹_›))
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [RegUpd.gpr_write_of_ne _ _ _ hr.1, k₁.gpr r (by simpa using hr.2)]
  | shl k =>
    apply WP.of_runBlock
    simp only [Piece.code, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      show k < Size.x.bits from hp, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
    · simp only [Piece.reg, RegUpd.gpr_write_self, BitVec.setWidth_eq, Piece.val, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [RegUpd.gpr_write_of_ne _ _ _ hr.1]
  | shr k =>
    apply WP.of_runBlock
    simp only [Piece.code, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      show k < Size.x.bits from hp, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
    · simp only [Piece.reg, RegUpd.gpr_write_self, BitVec.setWidth_eq, Piece.val, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [RegUpd.gpr_write_of_ne _ _ _ hr.1]
  | self => exact WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-! ## Chains -/

/-- `t = t + r + c` by `adds` (`first`, with no carry in) or `adcs`. -/
theorem addOp_ok (s : State) (first : Bool) (t r : Reg) :
    WP isa (.block [addOp first t r]) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * s'.c.toNat =
        (s.gpr t).toNat + (s.gpr r).toNat + (if first then 0 else s.c.toNat) ∧
      Keeps [t] s s' := by
  apply WP.of_runBlock
  cases first <;>
  · simp only [addOp, runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Bool.false_eq_true,
      ite_true, ite_false, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
    · have := Word64.addCarry_value (s.gpr t) (s.gpr r)
      simp only [Word64.addCarry, Word64.carryOut] at this
      first
        | simpa only [Bool.toNat_false, Nat.add_zero] using this false
        | exact this s.c
    · simp only [List.mem_singleton] at hq
      simp only [RegUpd.gpr_addWithCarry, hq, ite_false]

/-- What a chain needs of its words `L`: distinct registers, none of `x0`,
`x2`, `x3`, `x7` or the multiplier `x`, and none read by a piece; and pieces
the code can compute. -/
structure ChainOk (size : Nat) (x : Reg) (L : List (Reg × Option Piece)) : Prop where
  nodup : (L.map Prod.fst).Nodup
  regs : ∀ t ∈ L.map Prod.fst, t ≠ .x0 ∧ t ≠ .x2 ∧ t ≠ .x3 ∧ t ≠ .x7 ∧ t ≠ x
  ok : ∀ e ∈ L, ∀ p ∈ e.2, p.Ok size
  reads : ∀ e ∈ L, ∀ p ∈ e.2, ∀ r ∈ p.reads, r ∉ L.map Prod.fst ∧ r ≠ .x2 ∧ r ≠ .x3

theorem ChainOk.tail {size : Nat} {x : Reg} {e : Reg × Option Piece} {L : List (Reg × Option Piece)}
    (h : VG.Proof.Mont.AArch64.ChainOk size x (e :: L)) : VG.Proof.Mont.AArch64.ChainOk size x L where
  nodup := (List.nodup_cons.mp h.nodup).2
  regs t ht := h.regs t (List.mem_cons_of_mem _ ht)
  ok e' he' := h.ok e' (List.mem_cons_of_mem _ he')
  reads e' he' p hp r hr := by
    have := h.reads e' (List.mem_cons_of_mem _ he') p hp r hr
    simp only [List.map_cons, List.mem_cons, not_or] at this
    exact ⟨this.1.2, this.2⟩

/-- The value a chain adds, little-endian. -/
def chainVal (x : Nat) (s : State) (base : Addr) : List (Reg × Option Piece) → Nat
  | [] => 0
  | (_, o) :: L => VG.Proof.Mont.AArch64.optVal x s base o + 2 ^ 64 * VG.Proof.Mont.AArch64.chainVal x s base L

theorem chainVal_congr {s s' : State} {base : Addr} (x : Nat) (hm : s'.mem = s.mem) :
    ∀ {L : List (Reg × Option Piece)}, (∀ e ∈ L, ∀ p ∈ e.2, ∀ r ∈ p.reads, s'.gpr r = s.gpr r) →
      VG.Proof.Mont.AArch64.chainVal x s' base L = VG.Proof.Mont.AArch64.chainVal x s base L
  | [], _ => rfl
  | (_, o) :: L, h => by
    simp only [VG.Proof.Mont.AArch64.chainVal, VG.Proof.Mont.AArch64.optVal_congr x hm (h _ (List.mem_cons_self ..)),
      VG.Proof.Mont.AArch64.chainVal_congr x hm fun e he => h e (List.mem_cons_of_mem _ he)]

/-- A word of a chain: `t + 2⁶⁴ c = t + piece + c_in`. -/
theorem step_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size)
    (hz : s.gpr .x7 = 0) {x t : Reg} (hx3 : x ≠ .x3) (first : Bool)
    (ht2 : t ≠ .x2) (ht3 : t ≠ .x3) {o : Option Piece} (hok : ∀ p ∈ o, p.Ok size) :
    WP isa (.block (stepCode x first t o)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * s'.c.toNat =
        (s.gpr t).toNat + VG.Proof.Mont.AArch64.optVal (s.gpr x).toNat s base o + (if first then 0 else s.c.toNat) ∧
      Keeps [.x2, .x3, t] s s' := by
  cases o with
  | none =>
    refine WP.mono (VG.Proof.Mont.AArch64.addOp_ok s first t .x7) fun s' ⟨e, k⟩ => ⟨?_, k.mono (by sub_regs)⟩
    rw [e, hz]; simp [VG.Proof.Mont.AArch64.optVal]
  | some p =>
    rw [stepCode, WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.AArch64.piece_ok hs hx3 (hok p rfl)) fun s₁ ⟨e₁, k₁, c₁⟩ => ?_
    refine WP.mono (VG.Proof.Mont.AArch64.addOp_ok s₁ first t (p.reg x)) fun s₂ ⟨e₂, k₂⟩ =>
      ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [e₂, e₁, c₁, k₁.gpr t (by simp [ht2, ht3])]
    rfl

/-- A chain after its first word: `T + 2^(64 k) c = T + V + c_in`. -/
theorem chainCode_ok {size : Nat} {base : Addr} {x : Reg} (hx2 : x ≠ .x2) (hx3 : x ≠ .x3) :
    ∀ (L : List (Reg × Option Piece)) {s : State}, VG.Proof.Mont.AArch64.Scr s base size → s.gpr .x7 = 0 →
      VG.Proof.Mont.AArch64.ChainOk size x L →
      WP isa (.block (chainCode x false L)) s fun s' =>
        VG.Proof.Mont.AArch64.regsVal s' (L.map Prod.fst) + 2 ^ (64 * L.length) * s'.c.toNat =
          VG.Proof.Mont.AArch64.regsVal s (L.map Prod.fst) + VG.Proof.Mont.AArch64.chainVal (s.gpr x).toNat s base L + s.c.toNat ∧
        Keeps (.x2 :: .x3 :: L.map Prod.fst) s s'
  | [], s, _, _, _ => WP.block_nil ⟨by simp [VG.Proof.Mont.AArch64.regsVal, VG.Proof.Mont.AArch64.chainVal], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | (t, o) :: L, s, hs, hz, hc => by
    have ht := hc.regs t (List.mem_cons_self ..)
    have htL : t ∉ L.map Prod.fst := (List.nodup_cons.mp hc.nodup).1
    rw [chainCode, WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.AArch64.step_ok hs hz hx3 false ht.2.1 ht.2.2.1 (hc.ok _ (List.mem_cons_self ..)))
      fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simp [Ne.symm ht.1])
    have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (by simp [Ne.symm ht.2.2.2.1]), hz]
    refine WP.mono (VG.Proof.Mont.AArch64.chainCode_ok hx2 hx3 L hs₁ hz₁ hc.tail) fun s₂ ⟨e₂, k₂⟩ => ?_
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.gpr t (by simp [ht.2.1, ht.2.2.1, htL])
    have hx₁ : s₁.gpr x = s.gpr x := k₁.gpr x (by simp [hx2, hx3, Ne.symm ht.2.2.2.2])
    have hL₁ : VG.Proof.Mont.AArch64.regsVal s₁ (L.map Prod.fst) = VG.Proof.Mont.AArch64.regsVal s (L.map Prod.fst) := VG.Proof.Mont.AArch64.regsVal_congr fun q hq =>
      k₁.gpr q (by
        have hq' := hc.regs q (List.mem_cons_of_mem _ hq)
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hq'.2.1, hq'.2.2.1, fun h => htL (h ▸ hq)⟩)
    have hV₁ : VG.Proof.Mont.AArch64.chainVal (s₁.gpr x).toNat s₁ base L = VG.Proof.Mont.AArch64.chainVal (s.gpr x).toNat s base L := by
      rw [hx₁]
      exact VG.Proof.Mont.AArch64.chainVal_congr _ k₁.mem fun e he p hp r hr => k₁.gpr r (by
        have := hc.reads e (List.mem_cons_of_mem _ he) p hp r hr
        simp only [List.map_cons, List.mem_cons, not_or] at this
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨this.2.1, this.2.2, this.1.1⟩)
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [hL₁, hV₁] at e₂
    simp only [Bool.false_eq_true, ite_false] at e₁
    simp only [List.map_cons, VG.Proof.Mont.AArch64.regsVal, VG.Proof.Mont.AArch64.chainVal, List.length_cons, ht₂, pow64_succ]
    rw [Nat.mul_assoc]
    omega

/-- A chain, skipping its words before the first piece: `T + 2^(64 k) c = T + V`
for a carry `c`. -/
theorem chainSkip_ok {size : Nat} {base : Addr} {x : Reg} (hx2 : x ≠ .x2) (hx3 : x ≠ .x3) :
    ∀ (L : List (Reg × Option Piece)) {s : State}, VG.Proof.Mont.AArch64.Scr s base size → s.gpr .x7 = 0 →
      VG.Proof.Mont.AArch64.ChainOk size x L →
      WP isa (.block (chainSkip x L)) s fun s' =>
        (∃ c ≤ 1, VG.Proof.Mont.AArch64.regsVal s' (L.map Prod.fst) + 2 ^ (64 * L.length) * c =
          VG.Proof.Mont.AArch64.regsVal s (L.map Prod.fst) + VG.Proof.Mont.AArch64.chainVal (s.gpr x).toNat s base L) ∧
        Keeps (.x2 :: .x3 :: L.map Prod.fst) s s'
  | [], s, _, _, _ => WP.block_nil ⟨⟨0, Nat.zero_le _, by simp [VG.Proof.Mont.AArch64.regsVal, VG.Proof.Mont.AArch64.chainVal]⟩,
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | (t, none) :: L, s, hs, hz, hc => by
    have ht := hc.regs t (List.mem_cons_self ..)
    have htL : t ∉ L.map Prod.fst := (List.nodup_cons.mp hc.nodup).1
    refine WP.mono (VG.Proof.Mont.AArch64.chainSkip_ok hx2 hx3 L hs hz hc.tail) fun s₁ ⟨⟨c, hc1, e₁⟩, k₁⟩ =>
      ⟨⟨c, hc1, ?_⟩, k₁.mono (by sub_regs)⟩
    have ht₁ : s₁.gpr t = s.gpr t := k₁.gpr t (by simp [ht.2.1, ht.2.2.1, htL])
    simp only [List.map_cons, VG.Proof.Mont.AArch64.regsVal, VG.Proof.Mont.AArch64.chainVal, List.length_cons, ht₁, pow64_succ, VG.Proof.Mont.AArch64.optVal]
    rw [Nat.mul_assoc]
    omega
  | (t, some p) :: L, s, hs, hz, hc => by
    have ht := hc.regs t (List.mem_cons_self ..)
    have htL : t ∉ L.map Prod.fst := (List.nodup_cons.mp hc.nodup).1
    rw [chainSkip, WP.block_append_iff]
    refine WP.mono (VG.Proof.Mont.AArch64.step_ok hs hz hx3 true ht.2.1 ht.2.2.1 (hc.ok _ (List.mem_cons_self ..)))
      fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simp [Ne.symm ht.1])
    have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (by simp [Ne.symm ht.2.2.2.1]), hz]
    refine WP.mono (VG.Proof.Mont.AArch64.chainCode_ok hx2 hx3 L hs₁ hz₁ hc.tail) fun s₂ ⟨e₂, k₂⟩ => ?_
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.gpr t (by simp [ht.2.1, ht.2.2.1, htL])
    have hx₁ : s₁.gpr x = s.gpr x := k₁.gpr x (by simp [hx2, hx3, Ne.symm ht.2.2.2.2])
    have hL₁ : VG.Proof.Mont.AArch64.regsVal s₁ (L.map Prod.fst) = VG.Proof.Mont.AArch64.regsVal s (L.map Prod.fst) := VG.Proof.Mont.AArch64.regsVal_congr fun q hq =>
      k₁.gpr q (by
        have hq' := hc.regs q (List.mem_cons_of_mem _ hq)
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hq'.2.1, hq'.2.2.1, fun h => htL (h ▸ hq)⟩)
    have hV₁ : VG.Proof.Mont.AArch64.chainVal (s₁.gpr x).toNat s₁ base L = VG.Proof.Mont.AArch64.chainVal (s.gpr x).toNat s base L := by
      rw [hx₁]
      exact VG.Proof.Mont.AArch64.chainVal_congr _ k₁.mem fun e he p hp r hr => k₁.gpr r (by
        have := hc.reads e (List.mem_cons_of_mem _ he) p hp r hr
        simp only [List.map_cons, List.mem_cons, not_or] at this
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨this.2.1, this.2.2, this.1.1⟩)
    refine ⟨⟨s₂.c.toNat, Bool.toNat_le _, ?_⟩, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [hL₁, hV₁] at e₂
    simp only [ite_true, Nat.add_zero] at e₁
    simp only [List.map_cons, VG.Proof.Mont.AArch64.regsVal, VG.Proof.Mont.AArch64.chainVal, List.length_cons, ht₂, pow64_succ]
    rw [Nat.mul_assoc]
    omega

/-! ## Rows -/

/-- The value of a multiplicand's word. -/
def _root_.VG.Impl.Mont.AArch64.RWord.val (s : State) (base : Addr) : RWord → Nat
  | .zero => 0
  | .one => 1
  | .pow2 k => 2 ^ k
  | .gen src => src.val s base

/-- A word the code can multiply by. -/
def _root_.VG.Impl.Mont.AArch64.RWord.Ok (size : Nat) : RWord → Prop
  | .pow2 k => 0 < k ∧ k < 64
  | .gen src => src.Ok size
  | _ => True

/-- The register a word reads, if any. -/
def _root_.VG.Impl.Mont.AArch64.RWord.reads : RWord → Option Reg
  | .gen src => src.reads
  | _ => none

/-- A multiplicand's value, little-endian. -/
def rwVal (s : State) (base : Addr) : List RWord → Nat
  | [] => 0
  | w :: ws => w.val s base + 2 ^ 64 * VG.Proof.Mont.AArch64.rwVal s base ws

/-- `x w` is its low word and `2⁶⁴` times its high word. -/
theorem word_split {s : State} {base : Addr} {size : Nat} (x : Nat) {w : RWord}
    (hw : w.Ok size) :
    VG.Proof.Mont.AArch64.optVal x s base w.lo + 2 ^ 64 * VG.Proof.Mont.AArch64.optVal x s base w.hi = x * w.val s base := by
  cases w with
  | zero => simp [RWord.lo, RWord.hi, VG.Proof.Mont.AArch64.optVal, RWord.val]
  | one => simp [RWord.lo, RWord.hi, VG.Proof.Mont.AArch64.optVal, RWord.val, Piece.val]
  | pow2 k =>
    obtain ⟨hk0, hk⟩ := hw
    simp only [RWord.lo, RWord.hi, VG.Proof.Mont.AArch64.optVal, Piece.val, RWord.val]
    have h64 : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
    have hd := Nat.div_add_mod x (2 ^ (64 - k))
    have hr := Nat.mod_lt x (Nat.two_pow_pos (64 - k))
    have hrk : x % 2 ^ (64 - k) * 2 ^ k < 2 ^ 64 := by
      rw [h64]; exact Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos k)
    have hx' : x * 2 ^ k = x % 2 ^ (64 - k) * 2 ^ k + 2 ^ 64 * (x / 2 ^ (64 - k)) := by
      conv => lhs; rw [← hd]
      rw [h64, Nat.add_mul, Nat.mul_right_comm, Nat.mul_comm (2 ^ (64 - k) * 2 ^ k), Nat.add_comm]
    rw [hx', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrk]
  | gen src => simp only [RWord.lo, RWord.hi, VG.Proof.Mont.AArch64.optVal, Piece.val, RWord.val, Nat.mod_add_div]

/-- Both chains' pieces at word `j`: the low word of `x w_j` and the high
word of `x w_{j-1}`. -/
theorem pieceAB (x : Nat) (s : State) (base : Addr) (ws : List RWord) (j : Nat) :
    VG.Proof.Mont.AArch64.optVal x s base (pieceA ws j) + VG.Proof.Mont.AArch64.optVal x s base (pieceB ws j) =
      VG.Proof.Mont.AArch64.optVal x s base (ws.getD j .zero).lo +
        (if j = 0 then 0 else VG.Proof.Mont.AArch64.optVal x s base (ws.getD (j - 1) .zero).hi) := by
  unfold pieceA pieceB
  by_cases hj : j = 0
  · cases (ws.getD j .zero).lo <;> simp only [hj, ite_true, VG.Proof.Mont.AArch64.optVal, Nat.add_zero]
  · cases (ws.getD j .zero).lo <;> cases (ws.getD (j - 1) .zero).hi <;>
      simp only [hj, ite_false, VG.Proof.Mont.AArch64.optVal, Nat.add_zero, Nat.zero_add]

theorem rwVal_drop (s : State) (base : Addr) : ∀ (ws : List RWord) (j : Nat),
    VG.Proof.Mont.AArch64.rwVal s base (ws.drop j) = (ws.getD j .zero).val s base + 2 ^ 64 * VG.Proof.Mont.AArch64.rwVal s base (ws.drop (j + 1))
  | [], _ => by simp [VG.Proof.Mont.AArch64.rwVal, RWord.val]
  | _ :: _, 0 => by simp [VG.Proof.Mont.AArch64.rwVal]
  | _ :: ws, j + 1 => by
    simp only [List.drop_succ_cons, List.getD_cons_succ]; exact VG.Proof.Mont.AArch64.rwVal_drop s base ws j

theorem getD_ok {size : Nat} {ws : List RWord} (hws : ∀ w ∈ ws, w.Ok size) (j : Nat) :
    (ws.getD j .zero).Ok size := by
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[j]? with
  | none => trivial
  | some w => exact hws w (List.mem_of_getElem? h)

theorem getD_hi_of_le {ws : List RWord} {j : Nat} (h : ws.length ≤ j) :
    (ws.getD j .zero).hi = none := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- The chains' values add up to `x W`, from word `j` of the row (with the
high word of `x w_{j-1}`). -/
theorem pieces_sum {s : State} {base : Addr} {size : Nat} (x : Nat) {ws : List RWord} (hws : ∀ w ∈ ws, w.Ok size) :
    ∀ (ts : List Reg) (j : Nat), ws.length < j + ts.length →
      VG.Proof.Mont.AArch64.chainVal x s base (pieces pieceA ws ts j) + VG.Proof.Mont.AArch64.chainVal x s base (pieces pieceB ws ts j) =
        (if j = 0 then 0 else VG.Proof.Mont.AArch64.optVal x s base (ws.getD (j - 1) .zero).hi) +
          x * VG.Proof.Mont.AArch64.rwVal s base (ws.drop j)
  | [], j, h => by
    simp only [List.length_nil, Nat.add_zero] at h
    have hj : j ≠ 0 := by omega
    simp only [pieces, VG.Proof.Mont.AArch64.chainVal, hj, ite_false, VG.Proof.Mont.AArch64.getD_hi_of_le (show ws.length ≤ j - 1 by omega),
      VG.Proof.Mont.AArch64.optVal, List.drop_eq_nil_of_le (show ws.length ≤ j by omega), VG.Proof.Mont.AArch64.rwVal, Nat.mul_zero]
  | t :: ts, j, h => by
    simp only [List.length_cons] at h
    have IH := VG.Proof.Mont.AArch64.pieces_sum (s := s) (base := base) x hws ts (j + 1) (by omega)
    simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at IH
    have hab := VG.Proof.Mont.AArch64.pieceAB x s base ws j
    have hsp := VG.Proof.Mont.AArch64.word_split (s := s) (base := base) x (VG.Proof.Mont.AArch64.getD_ok hws j)
    rw [VG.Proof.Mont.AArch64.rwVal_drop s base ws j]
    simp only [pieces, VG.Proof.Mont.AArch64.chainVal]
    rw [Nat.mul_add, Nat.mul_left_comm x (2 ^ 64)]
    omega

theorem pieces_fst (f : List RWord → Nat → Option Piece) (ws : List RWord) :
    ∀ (ts : List Reg) (j : Nat), (pieces f ws ts j).map Prod.fst = ts
  | [], _ => rfl
  | t :: ts, j => by simp only [pieces, List.map_cons, VG.Proof.Mont.AArch64.pieces_fst f ws ts (j + 1)]

theorem pieces_length (f : List RWord → Nat → Option Piece) (ws : List RWord) (ts : List Reg)
    (j : Nat) : (pieces f ws ts j).length = ts.length := by
  rw [← List.length_map (f := Prod.fst), VG.Proof.Mont.AArch64.pieces_fst]

theorem mem_pieces {f : List RWord → Nat → Option Piece} {ws : List RWord} :
    ∀ {ts : List Reg} {j : Nat} {e : Reg × Option Piece}, e ∈ pieces f ws ts j → ∃ k, e.2 = f ws k
  | [], _, _, h => absurd h List.not_mem_nil
  | t :: ts, j, e, h => by
    simp only [pieces, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨j, rfl⟩
    · exact VG.Proof.Mont.AArch64.mem_pieces h

/-- A piece of either chain is the low or the high word of a word of `W`. -/
theorem piece_word {ws : List RWord} {j : Nat} {p : Piece}
    (h : p ∈ pieceA ws j ∨ p ∈ pieceB ws j) : ∃ w ∈ ws, p ∈ w.lo ∨ p ∈ w.hi := by
  have hget : ∀ k, (p ∈ (ws.getD k .zero).lo ∨ p ∈ (ws.getD k .zero).hi) →
      ∃ w ∈ ws, p ∈ w.lo ∨ p ∈ w.hi := by
    intro k hk
    rw [List.getD_eq_getElem?_getD] at hk
    cases hw : ws[k]? with
    | none => rw [hw] at hk; simp [RWord.lo, RWord.hi] at hk
    | some w => rw [hw] at hk; exact ⟨w, List.mem_of_getElem? hw, hk⟩
  rcases h with h | h
  · unfold pieceA at h
    cases h1 : (ws.getD j .zero).lo with
    | some q =>
      rw [h1] at h
      exact hget j (Or.inl (by rw [h1]; exact h))
    | none =>
      rw [h1] at h
      by_cases hj : j = 0
      · simp only [hj, ite_true] at h; exact absurd h (by simp)
      · simp only [hj, ite_false] at h; exact hget (j - 1) (Or.inr h)
  · unfold pieceB at h
    by_cases hj : j = 0
    · simp only [hj, ite_true] at h; exact absurd h (by simp)
    · simp only [hj, ite_false] at h
      cases h1 : (ws.getD j .zero).lo <;> cases h2 : (ws.getD (j - 1) .zero).hi <;>
        rw [h1, h2] at h
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · exact hget (j - 1) (Or.inr (by rw [h2]; exact h))

theorem piece_of_word {size : Nat} {w : RWord} (hw : w.Ok size) {p : Piece}
    (h : p ∈ w.lo ∨ p ∈ w.hi) : p.Ok size ∧ ∀ r ∈ p.reads, r ∈ w.reads := by
  cases w with
  | zero => simp [RWord.lo, RWord.hi] at h
  | one =>
    simp only [RWord.lo, RWord.hi, Option.mem_def, Option.some.injEq, reduceCtorEq, or_false] at h
    subst h; exact ⟨trivial, fun _ h => by simp [Piece.reads] at h⟩
  | pow2 k =>
    simp only [RWord.lo, RWord.hi, Option.mem_def, Option.some.injEq] at h
    rcases h with rfl | rfl
    · exact ⟨hw.2, fun _ h => by simp [Piece.reads] at h⟩
    · exact ⟨show 64 - k < 64 by have := hw.1; omega, fun _ h => by simp [Piece.reads] at h⟩
  | gen src =>
    simp only [RWord.lo, RWord.hi, Option.mem_def, Option.some.injEq] at h
    rcases h with rfl | rfl <;> exact ⟨hw, fun r hr => hr⟩

/-- What a row `ts += x · W` needs: distinct words, none of `x0`, `x2`, `x3`,
`x7` or the multiplier `x`; words of `W` the code can multiply by, reading no
register of `ts`, `x2` or `x3`; and `x` neither `x2` nor `x3`. -/
structure RowOk (size : Nat) (x : Reg) (ts : List Reg) (ws : List RWord) : Prop where
  nodup : ts.Nodup
  regs : ∀ t ∈ ts, t ≠ .x0 ∧ t ≠ .x2 ∧ t ≠ .x3 ∧ t ≠ .x7 ∧ t ≠ x
  ok : ∀ w ∈ ws, w.Ok size
  reads : ∀ w ∈ ws, ∀ r ∈ w.reads, r ∉ ts ∧ r ≠ .x2 ∧ r ≠ .x3
  x2 : x ≠ .x2
  x3 : x ≠ .x3

theorem RowOk.chain {size : Nat} {x : Reg} {ts : List Reg} {ws : List RWord} (h : VG.Proof.Mont.AArch64.RowOk size x ts ws)
    {f : List RWord → Nat → Option Piece} (hf : f = pieceA ∨ f = pieceB) (j : Nat) :
    VG.Proof.Mont.AArch64.ChainOk size x (pieces f ws ts j) where
  nodup := by rw [VG.Proof.Mont.AArch64.pieces_fst]; exact h.nodup
  regs t ht := h.regs t (by rwa [VG.Proof.Mont.AArch64.pieces_fst] at ht)
  ok e he p hp := by
    obtain ⟨k, hk⟩ := VG.Proof.Mont.AArch64.mem_pieces he
    rw [hk] at hp
    obtain ⟨w, hw, hpw⟩ := VG.Proof.Mont.AArch64.piece_word (by rcases hf with rfl | rfl; exacts [Or.inl hp, Or.inr hp])
    exact (VG.Proof.Mont.AArch64.piece_of_word (h.ok w hw) hpw).1
  reads e he p hp r hr := by
    obtain ⟨k, hk⟩ := VG.Proof.Mont.AArch64.mem_pieces he
    rw [hk] at hp
    obtain ⟨w, hw, hpw⟩ := VG.Proof.Mont.AArch64.piece_word (by rcases hf with rfl | rfl; exacts [Or.inl hp, Or.inr hp])
    have := h.reads w hw r ((VG.Proof.Mont.AArch64.piece_of_word (h.ok w hw) hpw).2 r hr)
    rw [VG.Proof.Mont.AArch64.pieces_fst]; exact this

/-- `ts += x · W`, if the sum fits in `ts`. -/
theorem row_ok {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.AArch64.Scr s base size) (hz : s.gpr .x7 = 0)
    {x : Reg} {ts : List Reg} {ws : List RWord} (h : VG.Proof.Mont.AArch64.RowOk size x ts ws)
    (hlen : ws.length < ts.length)
    (hb : VG.Proof.Mont.AArch64.regsVal s ts + (s.gpr x).toNat * VG.Proof.Mont.AArch64.rwVal s base ws < 2 ^ (64 * ts.length)) :
    WP isa (.block (row x ts ws)) s fun s' =>
      VG.Proof.Mont.AArch64.regsVal s' ts = VG.Proof.Mont.AArch64.regsVal s ts + (s.gpr x).toNat * VG.Proof.Mont.AArch64.rwVal s base ws ∧
      Keeps (.x2 :: .x3 :: ts) s s' := by
  have hsum := VG.Proof.Mont.AArch64.pieces_sum (s := s) (base := base) (s.gpr x).toNat h.ok ts 0 (by omega)
  simp only [ite_true, Nat.zero_add, List.drop_zero] at hsum
  rw [row, WP.block_append_iff]
  have cA := h.chain (Or.inl rfl) 0
  have cB := h.chain (Or.inr rfl) 0
  refine WP.mono (VG.Proof.Mont.AArch64.chainSkip_ok h.x2 h.x3 _ hs hz cA) fun s₁ ⟨⟨c₁, hc₁, e₁⟩, k₁⟩ => ?_
  rw [VG.Proof.Mont.AArch64.pieces_fst, VG.Proof.Mont.AArch64.pieces_length] at e₁
  rw [VG.Proof.Mont.AArch64.pieces_fst] at k₁
  have hs₁ := hs.of_keeps k₁ (by
    simp only [List.mem_cons, not_or]
    exact ⟨by decide, by decide, fun h' => (h.regs _ h').1 rfl⟩)
  have hz₁ : s₁.gpr .x7 = 0 := by
    rw [k₁.gpr _ (by
      simp only [List.mem_cons, not_or]
      exact ⟨by decide, by decide, fun h' => (h.regs _ h').2.2.2.1 rfl⟩), hz]
  refine WP.mono (VG.Proof.Mont.AArch64.chainSkip_ok h.x2 h.x3 _ hs₁ hz₁ cB) fun s₂ ⟨⟨c₂, hc₂, e₂⟩, k₂⟩ => ?_
  rw [VG.Proof.Mont.AArch64.pieces_fst, VG.Proof.Mont.AArch64.pieces_length] at e₂
  rw [VG.Proof.Mont.AArch64.pieces_fst] at k₂
  have hx₁ : s₁.gpr x = s.gpr x := k₁.gpr x (by
    simp only [List.mem_cons, not_or]
    exact ⟨h.x2, h.x3, fun h' => (h.regs _ h').2.2.2.2 rfl⟩)
  have hV : VG.Proof.Mont.AArch64.chainVal (s₁.gpr x).toNat s₁ base (pieces pieceB ws ts 0) =
      VG.Proof.Mont.AArch64.chainVal (s.gpr x).toNat s base (pieces pieceB ws ts 0) := by
    rw [hx₁]
    exact VG.Proof.Mont.AArch64.chainVal_congr _ k₁.mem fun e he p hp r hr => k₁.gpr r (by
      have := cB.reads e he p hp r hr
      rw [VG.Proof.Mont.AArch64.pieces_fst] at this
      simp only [List.mem_cons, not_or]
      exact ⟨this.2.1, this.2.2, this.1⟩)
  rw [hV] at e₂
  refine ⟨?_, (k₁.trans k₂)⟩
  have hP := Nat.two_pow_pos (64 * ts.length)
  rcases (by omega : c₁ = 0 ∨ c₁ = 1) with rfl | rfl <;>
    rcases (by omega : c₂ = 0 ∨ c₂ = 1) with rfl | rfl <;> omega


end VG.Proof.Mont.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.AArch64.Blocks`. -/
section

/-!
# Montgomery arithmetic on AArch64: the small blocks of a round

Each run symbolically once, for any registers: a register cleared
(`movz0_ok`) and a constant built (`const64_ok`).
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-- `r = 0`. -/
theorem movz0_ok (s : State) (r : Reg) :
    WP isa (.block [.movz .x r 0 0]) s fun s' => s'.gpr r = 0 ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.x.bits by decide,
    ite_true, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  exact RegUpd.gpr_write_of_ne _ _ _ hq

/-- `r = v`. -/
theorem const64_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (const64 r v)) s fun t => t.gpr r = v ∧ Keeps [r] s t := by
  apply WP.of_runBlock
  simp only [const64, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits from by decide, show 16 * 1 < Size.x.bits from by decide,
    show 16 * 2 < Size.x.bits from by decide, show 16 * 3 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨movz_movk64' v, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r' hr
  have h : r' ≠ r := by simpa only [List.mem_singleton] using hr
  simp only [RegUpd.gpr_write_of_ne _ _ _ h]

end VG.Proof.Mont.AArch64

end
