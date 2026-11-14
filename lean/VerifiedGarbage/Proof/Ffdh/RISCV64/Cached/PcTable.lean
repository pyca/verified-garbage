module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.Comb
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMont
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.PreWrite
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.RISCV64.Li
-- separate module: the precompute's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # FFDH's context on RISC-V: the comb's table

`table_ok`: from p in array 0, `R² mod p` in array 1 and g's octets, the 32
entries of the comb, `g^(exponent bits a) R mod p`, into the context's rows
2 to 33: entries 0 and 1 (`initial`), then for each tooth `d = 2^k` its
entry, the `2^rows`-th power of the last tooth's (`squares`), and the
products of the entries below it with it (`product`). -/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Precompute
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum.RISCV64.Win (WCtx WinO A ctxRegs slot_lt slot24 copy_ok copyRegs)
open VG.Proof.Bignum (slot slot_sep)

theorem sub_bne {a c : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 c != (0 : BitVec 64)) = decide (a ≠ c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 64 a - BitVec.ofNat 64 c ≠ 0 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at this
      omega_arith
    rw [decide_eq_true h]
    exact bne_iff_ne.mpr this

theorem slot_le1 {w a : Nat} (ha : 1 ≤ a) : slot w 1 ≤ slot w a := by
  unfold slot; have := Nat.mul_le_mul_right (8 * (w + 2)) ha; omega_arith

/-- What the table's stages keep: the working space and its context, the
context's address, writable and apart, and p odd. -/
structure TS (s : State) (B C : Addr) (Z w P : Nat) (M : Mem) : Prop where
  win : WCtx s B Z w P
  h10 : s.gpr .s10 = C
  hc : Scr s C (8 * ctxWords w)
  sepCB : ∀ x, ofs C x < 8 * ctxWords w → Z ≤ ofs B x
  sepBC : ∀ x, ofs B x < Z → 8 * ctxWords w ≤ ofs C x
  odd : P % 2 = 1
  one : 1 < P
  low : ∀ y, ofs B y < slot w 1 → s.mem y = M y

/-- The registers `TS` reads. -/
def tsRegs : List Reg := ctxRegs ++ [.s10]

/-- `WCtx` after a change of registers apart from its own, `a7` as before, and
of memory keeping array 0. -/
theorem wctx_low7 {s t : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ ([.s5, .t0, .t1] : List Reg), r ∉ rs) (h7 : t.gpr .a7 = off B (slot w 0))
    (hlow : ∀ y, ofs B y < slot w 1 → t.mem y = s.mem y) : WCtx t B Z w N := by
  have o : Outside B (slot w 1) (2 ^ 64) s.mem t.mem := fun y hy => hlow y (hy.elim id fun h' => by
    have := (y - B).isLt; simp only [ofs] at h'; omega_arith)
  have hn := h.nw
  have s0 := slot_lt (w := w) (show 0 < 24 by decide)
  have e1 : slot w 1 = slot w 0 + 8 * (w + 2) := by unfold slot; omega_arith
  have g := fun r hr => k.gpr (r := r) (hrs r hr)
  refine ⟨h.scr.congr k.2.2, h.w2, h.w31, h.hZ, h7,
    (g .s5 (by decide)).trans h.s5, (g .t0 (by decide)).trans h.t0, ?_, ?_⟩
  · have hw0 : Mont.word t.mem B (slot w 0) = Mont.word s.mem B (slot w 0) :=
      Outside.word o (Or.inl (by omega_arith)) (by omega_arith)
    rw [g .t1 (by decide), hw0]
    exact h.inv
  · rw [← h.n]
    exact Outside.wordsVal o (Or.inl (by omega_arith)) (by omega_arith)

/-- `WCtx` after a change of registers apart from its own and of memory
keeping array 0. -/
theorem wctx_low {s t : State} {B : Addr} {Z w N : Nat} (h : WCtx s B Z w N) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ ctxRegs, r ∉ rs) (hlow : ∀ y, ofs B y < slot w 1 → t.mem y = s.mem y) : WCtx t B Z w N :=
  wctx_low7 h k (fun r hr => hrs r (by
    simp only [ctxRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
    ((k.gpr (hrs _ (by decide))).trans h.a7) hlow

theorem TS.keep {s t : State} {B C : Addr} {M : Mem} {Z w P : Nat} (h : TS s B C Z w P M) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ tsRegs, r ∉ rs) (hlow : ∀ y, ofs B y < slot w 1 → t.mem y = s.mem y) : TS t B C Z w P M :=
  ⟨wctx_low h.win k (fun r hr => hrs r (List.mem_append_left _ hr)) hlow,
    (k.gpr (hrs _ (by decide))).trans h.h10, h.hc.congr k.2.2, h.sepCB, h.sepBC, h.odd, h.one,
    fun y hy => (hlow y hy).trans (h.low y hy)⟩

theorem TS.same {s t : State} {B C : Addr} {M : Mem} {Z w P : Nat} (h : TS s B C Z w P M) {rs : List Reg} (k : Keep rs s t)
    (hrs : ∀ r ∈ tsRegs, r ∉ rs) (hm : t.mem = s.mem) : TS t B C Z w P M :=
  h.keep k hrs fun y _ => by rw [hm]

theorem TS.rd {s : State} {B C : Addr} {M : Mem} {Z w P : Nat} (h : TS s B C Z w P M) : CtxRd s B Z C w :=
  ⟨h.hc.nowrap, fun d hd => h.hc.ld (d := d) (n := 8) hd, h.hc.al, h.sepCB⟩

theorem TS.slZ {s : State} {B C : Addr} {M : Mem} {Z w P : Nat} (h : TS s B C Z w P M) {a : Nat} (ha : a < 24) :
    slot w a + 8 * (w + 2) ≤ Z := h.win.sl ha

/-- A change of an array keeps the context. -/
theorem TS.ctx_out {s : State} {B C : Addr} {M : Mem} {Z w P o n : Nat} {m m' : Mem} (h : TS s B C Z w P M)
    (out : Outside B o n m m') (hn : o + n ≤ Z) : Outside C (8 * ctxWords w) (2 ^ 64) m m' :=
  ctx_of_scr out hn h.sepCB

/-- `storeRow a`: row `j` (in `t2`) of the context `:=` array `a`. -/
theorem TS.store {s : State} {B C : Addr} {M : Mem} {Z w P j a : Nat} (h : TS s B C Z w P M) (ha : a < 24)
    (h2 : s.gpr .t2 = BitVec.ofNat 64 j) (hj : j < 34) :
    WP isa (storeRow a) s fun t =>
      (wordsVal t.mem C (rowOff w j) w = A s.mem B w a ∧ Outside C (rowOff w j) (8 * w) s.mem t.mem ∧
        Outside B Z (2 ^ 64) s.mem t.mem ∧ TS t B C Z w P M) ∧ Keep [.t2, .t3, .t4, .t5, .s0] s t := by
  have hw := h.win.w2; have hw' := h.win.w31
  have hrow := row_fits (w := w) hj
  have hsl := h.slZ ha
  have h1Z : slot w 1 ≤ Z := by have := h.slZ (show 1 < 24 by decide); omega_arith
  unfold storeRow
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowPtr_ok (rd := .t3) (.inl rfl) h.h10 h.win.t0 h2 hw' (by omega_arith))
    fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  have h1 := h.win.regs k1 (by decide) m1
  refine WP.mono (Pub.base_ok (rd := .t4) (by decide) h1.a7 h1.s5 a) fun t₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have h2' := h1.regs k2 (by decide) m2
  have hm : t₂.mem = s.mem := by rw [m2, m1]
  have k12 := k1.trans k2
  refine WP.mono (copyWords_ok (B := B) (P := C) (Z := Z) (Zp := 8 * ctxWords w) (dS := slot w a)
    (dD := rowOff w j) h2'.scr (h.hc.congr k12.2.2) a4 ((k2.gpr (by decide)).trans a3) h2'.t0 (by omega_arith) hw'
    (slot_al w a) (by unfold rowOff; omega_arith) (by omega_arith) hrow h.sepBC)
    fun t ⟨⟨_, hw₁, ho⟩, kt⟩ => ?_
  have far : Outside B Z (2 ^ 64) s.mem t.mem := by rw [← hm]; exact ctx_of_scr ho hrow h.sepBC
  refine ⟨⟨?_, by rw [← hm]; exact ho, far, h.keep (k12.trans kt) (by decide)
    fun y hy => far y (Or.inl (by omega_arith))⟩, (k12.trans kt).mono (by decide)⟩
  rw [show A s.mem B w a = A t₂.mem B w a by rw [hm]]
  exact wordsVal_of_words hw₁

/-- `loadRow a`: array `a := ` row `j` (in `t2`) of the context. -/
theorem TS.load {s : State} {B C : Addr} {M : Mem} {Z w P j a : Nat} (h : TS s B C Z w P M) (ha : a < 24) (ha1 : 1 ≤ a)
    (h2 : s.gpr .t2 = BitVec.ofNat 64 j) (hj : j < 34) :
    WP isa (loadRow a) s fun t =>
      (A t.mem B w a = wordsVal s.mem C (rowOff w j) w ∧ Outside B (slot w a) (8 * w) s.mem t.mem ∧
        Outside C (8 * ctxWords w) (2 ^ 64) s.mem t.mem ∧ TS t B C Z w P M) ∧
        Keep [.t2, .t3, .t4, .t5, .s0] s t := by
  have hsl := h.slZ ha
  refine WP.mono (loadRow_ok h.win h.rd h.h10 h2 ha hj) fun t ⟨⟨hv, ho⟩, kt⟩ =>
    ⟨⟨hv, ho, h.ctx_out ho (by omega_arith), h.keep kt (by decide) fun y hy => ho y (Or.inl
      (Nat.lt_of_lt_of_le hy (slot_le1 ha1)))⟩, kt⟩

/-- A Montgomery product in `TS`. -/
theorem TS.mont {s : State} {B C : Addr} {M : Mem} {Z w P : Nat} (h : TS s B C Z w P M) {o a b : Nat} (ho : o < 24) (ha : a < 24)
    (hb : b < 24) (ho1 : o ≠ 0) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (hb2 : b ≠ 2) (hB : A s.mem B w b < P) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (A t.mem B w o < P ∧ A t.mem B w o * 2 ^ (64 * w) % P = A s.mem B w a * A s.mem B w b % P ∧
        (∀ j < 24, j ≠ 2 → j ≠ 3 → j ≠ o → A t.mem B w j = A s.mem B w j) ∧
        Outside C (8 * ctxWords w) (2 ^ 64) s.mem t.mem ∧ TS t B C Z w P M ∧ WinO B w s.mem t.mem) ∧
        Keep Pub.montRegs s t := by
  refine WP.mono (h.win.mont ho ha hb ho1 ho2 ho3 ha2 hb2 hB) fun t ⟨⟨_, lt, eq, fr, out⟩, k⟩ =>
    ⟨⟨lt, eq, fr, h.ctx_out out (by have := h.win.hZ; have := slot24 w; omega_arith),
      h.keep k (by decide) fun y hy => out y (Or.inl hy), out⟩, k⟩

/-! ## Montgomery residues -/

/-- `x = y` from `x R ≡ y R`, both below `P`, `P` odd. -/
theorem mont_eq {x y P w : Nat} (hodd : P % 2 = 1) (hx : x < P) (hy : y < P)
    (h : x * 2 ^ (64 * w) % P = y * 2 ^ (64 * w) % P) : x = y := by
  have cop := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have := VG.Proof.Bignum.mont_cancel cop h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

/-- The comb's entries: `g^(exponent bits a) R mod p`. -/
abbrev entV (G P w bits a : Nat) : Nat := combM G P w (Spec.Rsa.FixedBaseComb.exponent bits a)

theorem combM_square {G P w E a c : Nat} (hodd : P % 2 = 1) (hc : c < P) (ha : a = combM G P w E)
    (h : c * 2 ^ (64 * w) % P = a * a % P) : c = combM G P w (E * 2) := by
  rw [Nat.mul_comm E 2]
  exact VG.Proof.Rsa.FixedBaseComb.mont_square_encoded (VG.Proof.Bignum.coprime_pow2 hodd (64 * w)) hc ha h

theorem combM_mul {G P w E F a b c : Nat} (hodd : P % 2 = 1) (hc : c < P) (ha : a = combM G P w E)
    (hb : b = combM G P w F) (h : c * 2 ^ (64 * w) % P = a * b % P) : c = combM G P w (E + F) :=
  VG.Proof.Rsa.FixedBaseComb.mont_product_encoded (VG.Proof.Bignum.coprime_pow2 hodd (64 * w)) hc ha hb h

theorem exponent_one (bits : Nat) : Spec.Rsa.FixedBaseComb.exponent bits 1 = 1 := by
  simpa using VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits 0 (by decide)

theorem combM_zero {G P w : Nat} (hP : 1 < P) : combM G P w 0 = 2 ^ (64 * w) % P := by
  rw [combM, VG.Proof.Bignum.powMod_eq, Nat.pow_zero, Nat.mod_eq_of_lt hP, Nat.one_mul]

theorem combM_one {G P w : Nat} (hG : G < P) : combM G P w 1 = G * 2 ^ (64 * w) % P := by
  rw [combM, VG.Proof.Bignum.powMod_eq, Nat.pow_one, Nat.mod_eq_of_lt hG]

/-! ## The entries -/

/-- Entries `a < n` of the context are the comb's. -/
def Ents (m : Mem) (C : Addr) (G P w bits n : Nat) : Prop := ∀ a < n, ent m C w a = entV G P w bits a

/-- The context below the table (its metadata, p and `R² mod p`) as in `m₀`. -/
def CtxKeep (C : Addr) (w : Nat) (m₀ m : Mem) : Prop := ∀ y, ofs C y < rowOff w 2 → m y = m₀ y

theorem CtxKeep.trans {C : Addr} {w : Nat} {m₀ m₁ m₂ : Mem} (h₁ : CtxKeep C w m₀ m₁) (h₂ : CtxKeep C w m₁ m₂) :
    CtxKeep C w m₀ m₂ := fun y hy => (h₂ y hy).trans (h₁ y hy)

theorem CtxKeep.of_far {C : Addr} {w : Nat} {m m' : Mem} (h : Outside C (8 * ctxWords w) (2 ^ 64) m m') :
    CtxKeep C w m m' := fun y hy => h y (Or.inl (by unfold rowOff ctxWords at *; omega_arith))

theorem CtxKeep.of_row {C : Addr} {w j : Nat} {m m' : Mem} (hj : 2 ≤ j)
    (h : Outside C (rowOff w j) (8 * w) m m') : CtxKeep C w m m' :=
  fun y hy => h y (Or.inl (Nat.lt_of_lt_of_le hy (by unfold rowOff; have := Nat.mul_le_mul_left w hj; omega_arith)))

theorem CtxKeep.of_eq {C : Addr} {w : Nat} {m m' : Mem} (h : m' = m) : CtxKeep C w m m' := fun _ _ => by rw [h]

theorem rowOff_le {w a b : Nat} (h : a ≤ b) : rowOff w a ≤ rowOff w b := by
  unfold rowOff; have := Nat.mul_le_mul_left w h; omega_arith

theorem rowOff_succ (w a : Nat) : rowOff w a + 8 * w = rowOff w (a + 1) := by
  unfold rowOff; rw [Nat.mul_succ]; omega_arith

theorem Ents.of_far {m m' : Mem} {C : Addr} {G P w bits n : Nat} (h : Ents m C G P w bits n)
    (hn : n ≤ 32) (out : Outside C (8 * ctxWords w) (2 ^ 64) m m') (hCn : C.toNat + 8 * ctxWords w ≤ 2 ^ 64) :
    Ents m' C G P w bits n := fun a ha => by
  have := row_fits (w := w) (show a + 2 < 34 by omega_arith)
  rw [ent, Outside.wordsVal out (Or.inl (by omega_arith)) (by omega_arith)]; exact h a ha

theorem Ents.store {m m' : Mem} {C : Addr} {G P w bits n : Nat} (h : Ents m C G P w bits n) (hn : n < 32)
    (out : Outside C (rowOff w (n + 2)) (8 * w) m m') (hv : wordsVal m' C (rowOff w (n + 2)) w = entV G P w bits n)
    (hCn : C.toNat + 8 * ctxWords w ≤ 2 ^ 64) : Ents m' C G P w bits (n + 1) := fun a ha => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | rfl
  · have := row_fits (w := w) (show a + 2 < 34 by omega_arith)
    have h1 := rowOff_le (w := w) (show a + 2 + 1 ≤ n + 2 by omega_arith)
    have h2 := rowOff_succ w (a + 2)
    rw [ent, Outside.wordsVal out (Or.inl (by omega_arith)) (by omega_arith)]; exact h a ha
  · exact hv

/-! ## The squares -/

/-- `squares`: array 6 `:=` its `2^rows`-th power, `rows` in `s9`. -/
theorem squares_ok {s : State} {B C : Addr} {M : Mem} {Z w P G E rows : Nat} (h : TS s B C Z w P M)
    (hx : A s.mem B w 6 = combM G P w E) (h9 : s.gpr .s9 = BitVec.ofNat 64 rows) (hr : 1 ≤ rows)
    (hr' : rows < 2 ^ 32) :
    WP isa squares s fun t =>
      (A t.mem B w 6 = combM G P w (E * 2 ^ rows) ∧
        (∀ c < 24, c ≠ 2 → c ≠ 3 → c ≠ 6 → A t.mem B w c = A s.mem B w c) ∧
        Outside C (8 * ctxWords w) (2 ^ 64) s.mem t.mem ∧ TS t B C Z w P M) ∧ Keep (.s8 :: Pub.montRegs) s t := by
  have hP : 0 < P := by have := h.one; omega_arith
  unfold squares
  refine WP.seq (WP.mono (WP.keep [.s8] (Q := fun t => t.gpr .s8 = BitVec.ofNat 64 rows ∧ t.mem = s.mem)
    (by brun [h9, add_ofNat_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a8, m1⟩, k1⟩ => ?_)
  have h1 := h.same k1 (by decide) m1
  refine WP.mono (wp_countdown (body := .seq (PublicChecked.montOp 6 6 6) (.block [.addi .s8 .s8 (-1)]))
    (cnt := .s8) (N := rows) (by omega_arith) (by omega_arith)
    (fun i t => (A t.mem B w 6 = combM G P w (E * 2 ^ i) ∧
        (∀ c < 24, c ≠ 2 → c ≠ 3 → c ≠ 6 → A t.mem B w c = A s.mem B w c) ∧
        Outside C (8 * ctxWords w) (2 ^ 64) s.mem t.mem ∧ TS t B C Z w P M) ∧ Keep (.s8 :: Pub.montRegs) s t)
    (fun i _ t ⟨⟨t6, tc, tctx, ht⟩, kt⟩ _ => ?_)
    ⟨⟨by rw [m1, hx, Nat.pow_zero, Nat.mul_one], fun c _ _ _ _ => by rw [m1],
      fun y _ => by rw [m1], h1⟩, k1.mono (by decide)⟩ a8) fun t h => h
  refine WP.seq (WP.mono (ht.mont (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [t6]; exact combM_lt hP _))
    fun u ⟨⟨ul, ue, uc, uctx, hu, _⟩, ku⟩ => ?_)
  refine WP.mono (WP.keep [.s8] (Q := fun v => v.gpr .s8 = u.gpr .s8 - BitVec.ofNat 64 1 ∧ v.mem = u.mem)
    (by brun [exec_addi_neg_lit (show 1 ≤ 2048 by decide)]) (by rfl) (by rfl))
    fun v ⟨⟨a8', mv⟩, kv⟩ => ⟨⟨⟨?_, fun c hc h2 h3 h6 => ?_, fun y hy => ?_, hu.same kv (by decide) mv⟩,
      (kt.trans (ku.trans kv)).mono (by decide)⟩, by rw [a8', ku.gpr (by decide)]⟩
  · rw [mv, combM_square h.odd ul t6 ue, Nat.pow_succ, Nat.mul_assoc]
  · rw [mv, uc c hc h2 h3 h6, tc c hc h2 h3 h6]
  · rw [mv, uctx y hy, tctx y hy]

/-! ## The products -/

/-- The registers the table writes. -/
def tabRegs : List Reg := [.t2, .s7, .s8, .a6] ++ Pub.montRegs ++ copyRegs ++ [.a0, .a1, .a7, .s0, .t3, .t4, .t5]

/-- Within the table: `TS`, the rows in `s9`. -/
structure TT (B C : Addr) (Z w P rows : Nat) (s₀ t : State) : Prop where
  ts : TS t B C Z w P s₀.mem
  h9 : t.gpr .s9 = BitVec.ofNat 64 rows
  keep : CtxKeep C w s₀.mem t.mem
  kr : Keep tabRegs s₀ t

theorem TT.next {B C : Addr} {Z w P rows : Nat} {s₀ t u : State} {rs : List Reg} (h : TT B C Z w P rows s₀ t)
    (hts : TS u B C Z w P s₀.mem) (k : Keep rs t u) (hr : ∀ r ∈ rs, r ∈ tabRegs)
    (hc : CtxKeep C w t.mem u.mem) : TT B C Z w P rows s₀ u :=
  ⟨hts, (k.gpr fun e => by have := hr _ e; revert this; decide).trans h.h9, h.keep.trans hc,
    (h.kr.trans k).mono fun r h' => (List.mem_append.mp h').elim id (hr r)⟩

/-- One product: entry `d + j :=` entry `j` times entry `d` (array 6). -/
theorem product_ok {B C : Addr} {Z w P G bits k j : Nat} {s₀ t : State}
    (h : TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ t) (hk : k < 5) (hj1 : 1 ≤ j) (hj : j < 2 ^ k)
    (h8 : t.gpr .s8 = BitVec.ofNat 64 j) (h7 : t.gpr .s7 = BitVec.ofNat 64 (2 ^ k))
    (h6 : A t.mem B w 6 = entV G P w bits (2 ^ k)) (he : Ents t.mem C G P w bits (2 ^ k + j)) :
    WP isa product t fun u => TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ u ∧
      u.gpr .s8 = BitVec.ofNat 64 (j + 1) ∧ u.gpr .s7 = BitVec.ofNat 64 (2 ^ k) ∧
      A u.mem B w 6 = entV G P w bits (2 ^ k) ∧ Ents u.mem C G P w bits (2 ^ k + j + 1) ∧
      isa.eval (.nonzero .t2) u = some (decide (j + 1 ≠ 2 ^ k)) := by
  have hP : 0 < P := by have := h.ts.one; omega_arith
  have hk32 : 2 ^ k ≤ 16 := by
    calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega_arith)
      _ = 16 := rfl
  have hCn := h.ts.hc.nowrap
  have hZ6 := h.ts.slZ (show 6 < 24 by decide)
  have hnw := h.ts.win.nw
  unfold product
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = BitVec.ofNat 64 (j + 2) ∧ u.mem = t.mem)
    (by brun [h8, ← BitVec.ofNat_add]) (by rfl) (by rfl)) fun t₁ ⟨⟨a2, m1⟩, k1⟩ => ?_)
  have h1 := h.next (h.ts.same k1 (by decide) m1) k1 (by decide) (CtxKeep.of_eq m1)
  refine WP.seq (WP.mono (h1.ts.load (j := j + 2) (a := 5) (by decide) (by decide) a2 (by omega_arith))
    fun t₂ ⟨⟨a5, o2, actx, ts2⟩, k2⟩ => ?_)
  have h2 := h1.next ts2 k2 (by decide) (CtxKeep.of_far actx)
  have e5 : A t₂.mem B w 5 = entV G P w bits j := by
    rw [a5, m1]; exact he j (by omega_arith)
  have e6 : A t₂.mem B w 6 = entV G P w bits (2 ^ k) := by
    have hZn := h.ts.win.scr.nowrap
    have := slot_lt (w := w) (show 5 < 6 by decide)
    show wordsVal t₂.mem B (slot w 6) w = _
    rw [Outside.wordsVal o2 (Or.inr (by omega_arith)) (by omega_arith), m1]
    exact h6
  refine WP.seq (WP.mono (ts2.mont (o := 5) (a := 5) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [e6]; exact combM_lt hP _))
    fun t₃ ⟨⟨l3, q3, c3, ctx3, ts3, _⟩, k3⟩ => ?_)
  have h3 := h2.next ts3 k3 (by decide) (CtxKeep.of_far ctx3)
  have v3 : A t₃.mem B w 5 = entV G P w bits (2 ^ k + j) := by
    rw [combM_mul h.ts.odd l3 e5 e6 q3]
    show combM G P w _ = combM G P w _
    rw [VG.Proof.Rsa.FixedBaseComb.exponent_add_tooth bits k j hk hj,
      VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits k hk]
  have k13 := (k1.trans k2).trans k3
  have g8 : t₃.gpr .s8 = BitVec.ofNat 64 j := (k13.gpr (by decide)).trans h8
  have g7 : t₃.gpr .s7 = BitVec.ofNat 64 (2 ^ k) := (k13.gpr (by decide)).trans h7
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = BitVec.ofNat 64 (2 ^ k + j + 2) ∧
      u.mem = t₃.mem)
    (by
      brun [g8, g7, ← BitVec.ofNat_add]
      congr 1; omega_arith) (by rfl) (by rfl)) fun t₄ ⟨⟨a2', m4⟩, k4⟩ => ?_)
  have h4 := h3.next (ts3.same k4 (by decide) m4) k4 (by decide) (CtxKeep.of_eq m4)
  refine WP.seq (WP.mono (h4.ts.store (j := 2 ^ k + j + 2) (a := 5) (by decide) a2' (by omega_arith))
    fun t₅ ⟨⟨r5, o5, b5, ts5⟩, k5⟩ => ?_)
  have h5 := h4.next ts5 k5 (by decide) (CtxKeep.of_row (by omega_arith) o5)
  have k15 := (k13.trans k4).trans k5
  have g8' : t₅.gpr .s8 = BitVec.ofNat 64 j := (k15.gpr (by decide)).trans h8
  have g7' : t₅.gpr .s7 = BitVec.ofNat 64 (2 ^ k) := (k15.gpr (by decide)).trans h7
  refine WP.mono (WP.keep [.t2, .s8] (Q := fun u => u.gpr .s8 = BitVec.ofNat 64 (j + 1) ∧
      u.gpr .t2 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 (2 ^ k) ∧ u.mem = t₅.mem)
    (by brun [g8', g7', BitVec.ofNat_add]) (by rfl) (by rfl)) fun u ⟨⟨u8, u2, mu⟩, ku⟩ => ?_
  have e6' : A t₅.mem B w 6 = entV G P w bits (2 ^ k) := by
    have hZn := h.ts.win.scr.nowrap
    show wordsVal t₅.mem B (slot w 6) w = _
    rw [Outside.wordsVal b5 (Or.inl (by omega_arith)) (by omega_arith), m4]
    exact (c3 6 (by decide) (by decide) (by decide) (by decide)).trans e6
  have ctx4 : Outside C (8 * ctxWords w) (2 ^ 64) t.mem t₄.mem := fun y hy => by
    rw [m4, ctx3 y hy, actx y hy, m1]
  have e5' := Ents.store (n := 2 ^ k + j) (Ents.of_far he (by omega_arith) ctx4 hCn) (by omega_arith) o5
    (by rw [r5, m4]; exact v3) hCn
  refine ⟨h5.next (ts5.same ku (by decide) mu) ku (by decide) (CtxKeep.of_eq mu), u8,
    by rw [ku.gpr (by decide), g7'], by rw [mu]; exact e6', fun a ha => by rw [ent, mu]; exact e5' a ha,
    (Steps.eval_nonzero u .t2).trans (by rw [u2, sub_bne (by omega_arith) (by omega_arith)])⟩

theorem two_pow_le16 {k : Nat} (hk : k < 5) : 2 ^ k ≤ 16 := by
  calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega_arith)
    _ = 16 := rfl

/-- The products of tooth `d = 2^k`: entries `d + 1` to `2 d - 1`. -/
theorem products_ok {B C : Addr} {Z w P G bits k : Nat} {s₀ t : State}
    (h : TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ t) (hk : k < 5) (hk1 : 1 ≤ k)
    (h8 : t.gpr .s8 = BitVec.ofNat 64 1) (h7 : t.gpr .s7 = BitVec.ofNat 64 (2 ^ k))
    (h6 : A t.mem B w 6 = entV G P w bits (2 ^ k)) (he : Ents t.mem C G P w bits (2 ^ k + 1)) :
    WP isa (.loop product (.nonzero .t2)) t fun u => TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ u ∧
      u.gpr .s7 = BitVec.ofNat 64 (2 ^ k) ∧ A u.mem B w 6 = entV G P w bits (2 ^ k) ∧
      Ents u.mem C G P w bits (2 ^ (k + 1)) := by
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk1
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ j, n = 2 ^ k - j ∧ 1 ≤ j ∧ j < 2 ^ k ∧
      TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ u ∧ u.gpr .s8 = BitVec.ofNat 64 j ∧
      u.gpr .s7 = BitVec.ofNat 64 (2 ^ k) ∧ A u.mem B w 6 = entV G P w bits (2 ^ k) ∧
      Ents u.mem C G P w bits (2 ^ k + j))
    (fun n u ⟨j, hn, hj1, hj, hu, u8, u7, u6, ue⟩ => WP.mono (product_ok hu hk hj1 hj u8 u7 u6 ue)
      fun v ⟨hv, v8, v7, v6, ve, vc⟩ => ?_) _ t ⟨1, rfl, Nat.le_refl _, by omega_arith, h, h8, h7, h6, he⟩
  by_cases hjk : j + 1 = 2 ^ k
  · refine Or.inl ⟨by rw [vc]; simp [hjk], hv, v7, v6, ?_⟩
    rw [Nat.pow_succ, Nat.mul_two]
    rw [show 2 ^ k + j + 1 = 2 ^ k + 2 ^ k by omega_arith] at ve
    exact ve
  · exact Or.inr ⟨by rw [vc]; simp [hjk], _, by omega_arith, j + 1, rfl, by omega_arith, by omega_arith, hv, v8,
      v7, v6, ve⟩

/-- Tooth `d = 2^k`: its entry, from the last tooth's, and its products. -/
theorem column_ok {B C : Addr} {Z w P G bits k : Nat} {s₀ t : State}
    (h : TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ t) (hk : k < 5) (hk1 : 1 ≤ k)
    (hr : 1 ≤ Spec.Rsa.FixedBaseComb.rows bits) (hr' : Spec.Rsa.FixedBaseComb.rows bits < 2 ^ 32)
    (h7 : t.gpr .s7 = BitVec.ofNat 64 (2 ^ k))
    (h6 : A t.mem B w 6 = combM G P w (2 ^ ((k - 1) * Spec.Rsa.FixedBaseComb.rows bits)))
    (he : Ents t.mem C G P w bits (2 ^ k)) :
    WP isa column t fun u => TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ u ∧
      u.gpr .s7 = BitVec.ofNat 64 (2 ^ (k + 1)) ∧
      A u.mem B w 6 = combM G P w (2 ^ (k * Spec.Rsa.FixedBaseComb.rows bits)) ∧
      Ents u.mem C G P w bits (2 ^ (k + 1)) ∧
      isa.eval (.nonzero .t2) u = some (decide (2 ^ (k + 1) ≠ 32)) := by
  have hk16 := two_pow_le16 hk
  have hCn := h.ts.hc.nowrap
  have hP : 0 < P := by have := h.ts.one; omega_arith
  have hZ6 := h.ts.slZ (show 6 < 24 by decide)
  have hnw := h.ts.win.nw
  have et : entV G P w bits (2 ^ k) = combM G P w (2 ^ (k * Spec.Rsa.FixedBaseComb.rows bits)) := by
    show combM G P w _ = _; rw [VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits k hk]
  unfold column
  simp only [seqs]
  refine WP.seq (WP.mono (squares_ok h.ts h6 h.h9 hr hr') fun t₁ ⟨⟨a6, ac, actx, ts1⟩, k1⟩ => ?_)
  have h1 := h.next ts1 k1 (by decide) (CtxKeep.of_far actx)
  have e6 : A t₁.mem B w 6 = entV G P w bits (2 ^ k) := by
    rw [a6, et, ← Nat.pow_add]; congr 2
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega_arith⟩
    rw [Nat.add_sub_cancel, Nat.succ_mul]
  have g7 : t₁.gpr .s7 = BitVec.ofNat 64 (2 ^ k) := (k1.gpr (by decide)).trans h7
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = BitVec.ofNat 64 (2 ^ k + 2) ∧ u.mem = t₁.mem)
    (by brun [g7, ← BitVec.ofNat_add]) (by rfl) (by rfl)) fun t₂ ⟨⟨a2, m2⟩, k2⟩ => ?_)
  have h2 := h1.next (ts1.same k2 (by decide) m2) k2 (by decide) (CtxKeep.of_eq m2)
  refine WP.seq (WP.mono (h2.ts.store (j := 2 ^ k + 2) (a := 6) (by decide) a2 (by omega_arith))
    fun t₃ ⟨⟨r3, o3, b3, ts3⟩, k3⟩ => ?_)
  have h3 := h2.next ts3 k3 (by decide) (CtxKeep.of_row (Nat.le_add_left 2 _) o3)
  have e6' : A t₃.mem B w 6 = entV G P w bits (2 ^ k) := by
    have hZn := h.ts.win.scr.nowrap
    show wordsVal t₃.mem B (slot w 6) w = _
    rw [Outside.wordsVal b3 (Or.inl (by omega_arith)) (by omega_arith), m2]
    exact e6
  have ctx2 : Outside C (8 * ctxWords w) (2 ^ 64) t.mem t₂.mem := fun y hy => by rw [m2, actx y hy]
  have e3 := Ents.store (n := 2 ^ k) (Ents.of_far he (by omega_arith) ctx2 hCn) (by omega_arith) o3
    (by rw [r3, m2]; exact e6) hCn
  refine WP.seq (WP.mono (WP.keep [.s8] (Q := fun u => u.gpr .s8 = BitVec.ofNat 64 1 ∧ u.mem = t₃.mem)
    (by brun [Pub.pub_li1]) (by rfl) (by rfl)) fun t₄ ⟨⟨a8, m4⟩, k4⟩ => ?_)
  have h4 := h3.next (ts3.same k4 (by decide) m4) k4 (by decide) (CtxKeep.of_eq m4)
  have k24 := (k2.trans k3).trans k4
  refine WP.seq (WP.mono (products_ok (G := G) h4 hk hk1 a8 ((k24.gpr (by decide)).trans g7)
      (by rw [m4]; exact e6') (fun a ha => by rw [ent, m4]; exact e3 a ha)) fun t₅ ⟨h5, g7', e65, ee⟩ => ?_)
  refine WP.mono (WP.keep [.t2, .s7] (Q := fun u => u.gpr .s7 = BitVec.ofNat 64 (2 ^ (k + 1)) ∧
      u.gpr .t2 = BitVec.ofNat 64 (2 ^ (k + 1)) - BitVec.ofNat 64 32 ∧ u.mem = t₅.mem)
    (by
      brun [g7', ← BitVec.ofNat_add, exec_addi_neg_lit (show 32 ≤ 2048 by decide)]
      rw [Nat.pow_succ, Nat.mul_two]; exact ⟨rfl, rfl⟩) (by rfl) (by rfl)) fun u ⟨⟨u7, u2, mu⟩, ku⟩ => ?_
  refine ⟨h5.next (h5.ts.same ku (by decide) mu) ku (by decide) (CtxKeep.of_eq mu), u7,
    by rw [mu, e65, et], fun a ha => by rw [ent, mu]; exact ee a ha,
    (Steps.eval_nonzero u .t2).trans (by
      have h5 : 2 ^ (k + 1) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega_arith)
      rw [u2, sub_bne (by omega_arith) (by decide)])⟩

/-- The teeth `2, 4, 8, 16`. -/
theorem columns_ok {B C : Addr} {Z w P G bits : Nat} {s₀ t : State}
    (h : TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ t)
    (hr : 1 ≤ Spec.Rsa.FixedBaseComb.rows bits) (hr' : Spec.Rsa.FixedBaseComb.rows bits < 2 ^ 32)
    (h7 : t.gpr .s7 = BitVec.ofNat 64 2) (h6 : A t.mem B w 6 = combM G P w 1)
    (he : Ents t.mem C G P w bits 2) :
    WP isa (.loop column (.nonzero .t2)) t fun u => TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ u ∧
      Ents u.mem C G P w bits 32 := by
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ k, n = 5 - k ∧ 1 ≤ k ∧ k < 5 ∧
      TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ u ∧ u.gpr .s7 = BitVec.ofNat 64 (2 ^ k) ∧
      A u.mem B w 6 = combM G P w (2 ^ ((k - 1) * Spec.Rsa.FixedBaseComb.rows bits)) ∧
      Ents u.mem C G P w bits (2 ^ k))
    (fun n u ⟨k, hn, hk1, hk, hu, u7, u6, ue⟩ => WP.mono (column_ok hu hk hk1 hr hr' u7 u6 ue)
      fun v ⟨hv, v7, v6, ve, vc⟩ => ?_) _ t ⟨1, rfl, Nat.le_refl _, by decide, h, h7,
        by rw [h6, Nat.sub_self, Nat.zero_mul, Nat.pow_zero], he⟩
  by_cases hk4 : k = 4
  · subst hk4
    exact Or.inl ⟨by rw [vc]; decide, hv, ve⟩
  · have hne : 2 ^ (k + 1) ≠ 32 := by
      intro e
      have : k + 1 = 5 := by
        have hk' : k < 4 := by omega_arith
        rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega_arith) with rfl | rfl | rfl <;> simp at e
      omega_arith
    exact Or.inr ⟨by rw [vc]; simp [hne], _, by omega_arith, k + 1, rfl, by omega_arith, by omega_arith, hv, v7,
      by rw [v6, Nat.add_sub_cancel], ve⟩

/-! ## The first two entries -/

/-- `loadG`: g's `k` octets (at `D + k`, `D` in `s7`) into array 4. -/
theorem loadG_ok {s : State} {B C D : Addr} {M : Mem} {Z w P k : Nat} (h : TS s B C Z w P M) (h6 : s.gpr .s6 = B)
    (h7 : s.gpr .s7 = off D 0) (h11 : s.gpr .s11 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D k) i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off (off D k) i ≠ x) :
    WP isa loadG s fun t =>
      (A t.mem B w 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ∧
        Outside B (slot w 4) (8 * (w + 1)) s.mem t.mem ∧ TS t B C Z w P M) ∧
      Keep [.a6, .a0, .a1, .a7, .s0, .s7, .s8, .t3, .t4, .t5] s t := by
  have hw := h.win.w2; have hw' := h.win.w31
  have hZ8 : slot w 8 ≤ Z := by have := h.slZ (show 8 < 24 by decide); have := slot_lt (w := w) (show 8 < 9 by decide); omega_arith
  have hsl4 := h.slZ (show 4 < 24 by decide)
  unfold loadG
  refine WP.seq (WP.mono (WP.keep [.a6] (Q := fun t => t.gpr .a6 = off D k ∧ t.mem = s.mem)
    (by
      brun [h7, h11]
      simp only [off, Nat.zero_add]) (by rfl) (by rfl)) fun t₁ ⟨⟨a6, m1⟩, k1⟩ => ?_)
  have h1 := h.same k1 (by decide) m1
  refine WP.mono (Pub.loadX_ok h1.win.scr ((k1.gpr (by decide)).trans h6) a6 ((k1.gpr (by decide)).trans h11)
    h1.win.a7 h1.win.s5 h1.win.t0 hk hkw hw' hZ8 (fun i hi => by rw [k1.2.1, k1.2.2]; exact hrd i hi) hsep)
    fun t ⟨⟨v4, _, o4, a7', _⟩, kt⟩ => ?_
  rw [m1] at v4 o4
  refine ⟨⟨v4, o4, ?_⟩, (k1.trans kt).mono (by decide)⟩
  have hlow : ∀ y, ofs B y < slot w 1 → t.mem y = s.mem y := fun y hy =>
    o4 y (Or.inl (Nat.lt_of_lt_of_le hy (slot_le1 (by decide))))
  have k1t := k1.trans kt
  exact ⟨wctx_low7 h.win k1t (by decide) a7' hlow, (k1t.gpr (by decide)).trans h.h10, h.hc.congr k1t.2.2,
    h.sepCB, h.sepBC, h.odd, h.one, fun y hy => (hlow y hy).trans (h.low y hy)⟩

/-- `initial`: entries 0 (Montgomery one) and 1 (g), and array 6 `:=` g. -/
theorem initial_ok {B C D : Addr} {Z w P k rows G bits : Nat} {s : State} (h : TT B C Z w P rows s s)
    (h1 : A s.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P) (h6 : s.gpr .s6 = B) (h7 : s.gpr .s7 = off D 0)
    (h11 : s.gpr .s11 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D k) i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off (off D k) i ≠ x)
    (hsepC : ∀ i < k, ∀ x, ofs C x < 8 * ctxWords w → off (off D k) i ≠ x)
    (hG : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) = G) (hGP : G < P) :
    WP isa initial s fun t => TT B C Z w P rows s t ∧ A t.mem B w 6 = combM G P w 1 ∧
      Ents t.mem C G P w bits 2 := by
  have hw := h.ts.win.w2; have hw' := h.ts.win.w31
  have hP : 0 < P := by have := h.ts.one; omega_arith
  have hCn := h.ts.hc.nowrap
  have hZn := h.ts.win.scr.nowrap
  have hZ := h.ts.win.hZ
  have e24 := slot24 w
  have a1 : ∀ c, c < 24 → slot w c + 8 * (w + 2) ≤ Z := fun c hc => h.ts.slZ hc
  have l17 := slot_lt (w := w) (show 1 < 7 by decide)
  have l14 := slot_lt (w := w) (show 1 < 4 by decide)
  have hZ8 : slot w 8 ≤ Z := by have := a1 8 (by decide); omega_arith
  have a11 := a1 1 (by decide); have a14 := a1 4 (by decide); have a15 := a1 5 (by decide)
  have a16 := a1 6 (by decide); have a17 := a1 7 (by decide)
  unfold initial
  simp only [seqs]
  -- 1 in array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok h.ts.win.scr (by omega_arith) hw' hZ8 h.ts.win.a7 h.ts.win.s5 h.ts.win.t0)
    fun t₁ ⟨⟨a7, o1⟩, k1⟩ => ?_)
  have ts1 := h.ts.keep k1 (by decide) fun y hy => o1 y (Or.inl (Nat.lt_of_lt_of_le hy (slot_le1 (by decide))))
  have c1 := h.ts.ctx_out o1 (by omega_arith)
  have h1' := h.next ts1 k1 (by decide) (CtxKeep.of_far c1)
  have g1 : A t₁.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P := by
    show wordsVal t₁.mem B (slot w 1) w = _
    rw [Outside.wordsVal o1 (Or.inl (by omega_arith)) (by omega_arith)]; exact h1
  have a7' : A t₁.mem B w 7 = 1 := a7
  -- Montgomery one in array 6.
  have hB7 : A t₁.mem B w 7 < P := by rw [a7']; exact h.ts.one
  refine WP.seq (WP.mono (ts1.mont (o := 6) (a := 1) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hB7) fun t₂ ⟨⟨l2, q2, c2a, ctx2, ts2, w2⟩, k2⟩ => ?_)
  have h2 := h1'.next ts2 k2 (by decide) (CtxKeep.of_far ctx2)
  have v2 : A t₂.mem B w 6 = entV G P w bits 0 := by
    rw [entV, VG.Proof.Rsa.FixedBaseComb.exponent_zero, combM_zero h.ts.one]
    refine mont_eq (w := w) h.ts.odd l2 (Nat.mod_lt _ hP) ?_
    rw [q2, g1, a7', Nat.mul_one, Nat.mod_mod, Nat.mod_mul_mod]
  -- Entry 0.
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = BitVec.ofNat 64 2 ∧ u.mem = t₂.mem)
    (by brun [fin64_exec_li_lit (show 2 < 2048 by decide)]) (by rfl) (by rfl)) fun t₃ ⟨⟨a3, m3⟩, k3⟩ => ?_)
  have h3 := h2.next (ts2.same k3 (by decide) m3) k3 (by decide) (CtxKeep.of_eq m3)
  refine WP.seq (WP.mono (h3.ts.store (j := 2) (a := 6) (by decide) a3 (by decide))
    fun t₄ ⟨⟨r4, o4, b4, ts4⟩, k4⟩ => ?_)
  have h4 := h3.next ts4 k4 (by decide) (CtxKeep.of_row (j := 2) (Nat.le_refl _) o4)
  have e4 : Ents t₄.mem C G P w bits 1 := Ents.store (n := 0) (fun _ h => absurd h (Nat.not_lt_zero _))
    (by decide) o4 (by rw [r4, m3]; exact v2) hCn
  have g4 : A t₄.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P := by
    show wordsVal t₄.mem B (slot w 1) w = _
    rw [Outside.wordsVal b4 (Or.inl (by omega_arith)) (by omega_arith), m3]
    exact (c2a 1 (by decide) (by decide) (by decide) (by decide)).trans g1
  -- g into array 4.
  have k14 := ((k1.trans k2).trans k3).trans k4
  have hb4 : Spec.Rsa.bytesAt t₄.mem (off D k) k = Spec.Rsa.bytesAt s.mem (off D k) k := by
    rw [Pub.bytes_apart (Z := 8 * ctxWords w) o4 (row_fits (w := w) (j := 2) (by decide)) hsepC, m3,
      Pub.bytes_apart (Z := Z) w2 (by omega_arith) hsep, Pub.bytes_apart (Z := Z) o1 (by omega_arith) hsep]
  refine WP.seq (WP.mono (loadG_ok h4.ts ((k14.gpr (by decide)).trans h6) ((k14.gpr (by decide)).trans h7)
    ((k14.gpr (by decide)).trans h11) hk hkw (fun i hi => by rw [k14.2.1, k14.2.2]; exact hrd i hi) hsep)
    fun t₅ ⟨⟨v5, o5, ts5⟩, k5⟩ => ?_)
  rw [hb4, hG] at v5
  have c5 := h4.ts.ctx_out o5 (by omega_arith)
  have h5 := h4.next ts5 k5 (by decide) (CtxKeep.of_far c5)
  have g5 : A t₅.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P := by
    show wordsVal t₅.mem B (slot w 1) w = _
    rw [Outside.wordsVal o5 (Or.inl (by omega_arith)) (by omega_arith)]; exact g4
  -- g R mod p into array 5.
  refine WP.seq (WP.mono (ts5.mont (o := 5) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [g5]; exact Nat.mod_lt _ hP))
    fun t₆ ⟨⟨l6, q6, c6a, ctx6, ts6, _⟩, k6⟩ => ?_)
  have h6' := h5.next ts6 k6 (by decide) (CtxKeep.of_far ctx6)
  have v6 : A t₆.mem B w 5 = entV G P w bits 1 := by
    rw [entV, exponent_one, combM_one hGP]
    refine mont_eq (w := w) h.ts.odd l6 (Nat.mod_lt _ hP) ?_
    rw [q6, v5, g5, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_assoc]
  -- Entry 1.
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = BitVec.ofNat 64 3 ∧ u.mem = t₆.mem)
    (by brun [fin64_exec_li_lit (show 3 < 2048 by decide)]) (by rfl) (by rfl)) fun t₇ ⟨⟨a3', m7⟩, k7⟩ => ?_)
  have h7' := h6'.next (ts6.same k7 (by decide) m7) k7 (by decide) (CtxKeep.of_eq m7)
  refine WP.seq (WP.mono (h7'.ts.store (j := 3) (a := 5) (by decide) a3' (by decide))
    fun t₈ ⟨⟨r8, o8, b8, ts8⟩, k8⟩ => ?_)
  have h8 := h7'.next ts8 k8 (by decide) (CtxKeep.of_row (j := 3) (by decide) o8)
  have c47 : Outside C (8 * ctxWords w) (2 ^ 64) t₄.mem t₇.mem := fun y hy => by
    rw [m7, ctx6 y hy, c5 y hy]
  have e8 : Ents t₈.mem C G P w bits 2 := Ents.store (n := 1) (Ents.of_far e4 (by decide) c47 hCn) (by decide) o8
    (by rw [r8, m7]; exact v6) hCn
  have g8 : A t₈.mem B w 5 = entV G P w bits 1 := by
    show wordsVal t₈.mem B (slot w 5) w = _
    rw [Outside.wordsVal b8 (Or.inl (by omega_arith)) (by omega_arith), m7]
    exact v6
  -- Array 6 := array 5.
  refine WP.mono (copy_ok h8.ts.win (o := 6) (a := 5) (by decide) (by decide) (by decide))
    fun t ⟨⟨v9, o9⟩, kt⟩ => ?_
  have ts9 := h8.ts.keep kt (by decide) fun y hy => o9 y (Or.inl (Nat.lt_of_lt_of_le hy (slot_le1 (by decide))))
  have c9 := h8.ts.ctx_out o9 (by omega_arith)
  refine ⟨h8.next ts9 kt (by decide) (CtxKeep.of_far c9), ?_, Ents.of_far e8 (by decide) c9 hCn⟩
  exact v9.trans (g8.trans (by rw [entV, exponent_one]))

/-- `table`: the 32 entries into rows 2 to 33. -/
theorem table_ok {B C D : Addr} {Z w P k G bits : Nat} {s : State}
    (h : TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s s)
    (hr : 1 ≤ Spec.Rsa.FixedBaseComb.rows bits) (hr' : Spec.Rsa.FixedBaseComb.rows bits < 2 ^ 32)
    (h1 : A s.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P) (h6 : s.gpr .s6 = B) (h7 : s.gpr .s7 = off D 0)
    (h11 : s.gpr .s11 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D k) i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off (off D k) i ≠ x)
    (hsepC : ∀ i < k, ∀ x, ofs C x < 8 * ctxWords w → off (off D k) i ≠ x)
    (hG : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) = G) (hGP : G < P) :
    WP isa table s fun t => TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s t ∧
      Ents t.mem C G P w bits 32 := by
  unfold table
  refine WP.seq (WP.mono (initial_ok (bits := bits) h h1 h6 h7 h11 hk hkw hrd hsep hsepC hG hGP)
    fun t₁ ⟨h1', a6, e1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = BitVec.ofNat 64 2 ∧ u.mem = t₁.mem)
    (by brun [fin64_exec_li_lit (show 2 < 2048 by decide)]) (by rfl) (by rfl)) fun t₂ ⟨⟨a7, m2⟩, k2⟩ => ?_)
  exact columns_ok (h1'.next (h1'.ts.same k2 (by decide) m2) k2 (by decide) (CtxKeep.of_eq m2)) hr hr' a7
    (by rw [m2]; exact a6) (fun a ha => by rw [ent, m2]; exact e1 a ha)

end VG.Proof.Ffdh.RISCV64.Cached
