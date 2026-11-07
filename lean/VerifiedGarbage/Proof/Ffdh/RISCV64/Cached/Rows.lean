module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.Cached
public import VerifiedGarbage.Proof.Bignum.RISCV64.ModExpWin
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSan
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreWrite
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH's context on RISC-V: its rows

The context is `3 + 34 w` words: three public words, then rows of `w`
words, row `j` at byte `rowOff w j` (`p`, `R² mod p`, then entry `e` at row
`2 + e`). `rowPtr_ok`: the address of a row; `loadRow_ok`: a row to an
array of the working space, by `copyWords`. `select_ok`: array 4 `:=` the
digit's entry, reading every entry under an equality mask.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.Cached
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum.RISCV64.Win (WCtx A mask selectAt_ok sub1_sign arr_eq arr1 slot_lt arrO arr_out)
open VG.Proof.Bignum (slot slot_sep Arrays)
open VG.Impl.Bignum.RISCV64.PublicChecked (base)

/-- The context's words. -/
abbrev ctxWords (w : Nat) : Nat := 3 + 34 * w

/-- The offset of row `j` in a context of `w`-word rows. -/
abbrev rowOff (w j : Nat) : Nat := 24 + 8 * (w * j)

/-- Entry `a` of the context at `C`, as a number. -/
abbrev ent (m : Mem) (C : Addr) (w a : Nat) : Nat := wordsVal m C (rowOff w (a + 2)) w

/-- The context at `C`: readable, aligned and apart from the working space. -/
structure CtxRd (s : State) (B : Addr) (Z : Nat) (C : Addr) (w : Nat) : Prop where
  hn : C.toNat + 8 * ctxWords w ≤ 2 ^ 64
  rd : ∀ d, d + 8 ≤ 8 * ctxWords w → InRegions (s.rd ++ s.wr) (off C d) 8
  al : C.toNat % 8 = 0
  sep : ∀ x, ofs C x < 8 * ctxWords w → Z ≤ ofs B x

theorem CtxRd.congr {s t : State} {B : Addr} {Z : Nat} {C : Addr} {w : Nat} (h : CtxRd s B Z C w)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : CtxRd t B Z C w :=
  ⟨h.hn, fun d hd => by rw [hrd, hwr]; exact h.rd d hd, h.al, h.sep⟩

theorem row_fits {w j : Nat} (hj : j < 34) : rowOff w j + 8 * w ≤ 8 * ctxWords w := by
  have h1 := Nat.mul_le_mul_left w (show j + 1 ≤ 34 by omega_arith)
  rw [Nat.mul_succ, Nat.mul_comm w 34] at h1
  unfold rowOff ctxWords; omega_arith

/-- Numbers of `k` words that agree word by word. -/
theorem wordsVal_of_words {m m' : Mem} {B B' : Addr} : ∀ {d d' k : Nat},
    (∀ i < k, word m B (d + 8 * i) = word m' B' (d' + 8 * i)) → wordsVal m B d k = wordsVal m' B' d' k
  | _, _, 0, _ => rfl
  | d, d', k + 1, h => by
    have h0 := h 0 (by omega_arith)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    simp only [wordsVal]
    rw [h0, wordsVal_of_words (d := d + 8) (d' := d' + 8) fun i hi => by
      have := h (i + 1) (by omega_arith)
      rwa [show d + 8 * (i + 1) = d + 8 + 8 * i by omega_arith,
        show d' + 8 * (i + 1) = d' + 8 + 8 * i by omega_arith] at this]

/-- A change of the working space keeps the context. -/
theorem ctx_of_scr {B C : Addr} {Z n o l : Nat} {m m' : Mem} (h : Outside B o l m m') (hl : o + l ≤ Z)
    (hsep : ∀ x, ofs C x < n → Z ≤ ofs B x) : Outside C n (2 ^ 64) m m' :=
  fun x hx => h x (Or.inr (by
    rcases hx with hx | hx
    · have := hsep x hx; omega_arith
    · have := (x - C).isLt; simp only [ofs] at hx; omega_arith))

theorem row_bv {w j : Nat} (hw : w < 2 ^ 31) (hj : j < 2 ^ 16) (C : Addr) :
    C + (BitVec.ofNat 64 j * BitVec.ofNat 64 w) <<< 3 + BitVec.ofNat 64 24 = off C (rowOff w j) := by
  have hwj : j * w < 2 ^ 47 := by
    calc j * w < 2 ^ 16 * 2 ^ 31 := Nat.mul_lt_mul_of_lt_of_lt hj hw
      _ = 2 ^ 47 := by rw [← Nat.pow_add]
  have e : (BitVec.ofNat 64 j * BitVec.ofNat 64 w) <<< 3 = BitVec.ofNat 64 (8 * (w * j)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega_arith),
      Nat.mod_eq_of_lt (show j * w < 2 ^ 64 by omega_arith), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (show j * w * 2 ^ 3 < 2 ^ 64 by omega_arith),
      Nat.mod_eq_of_lt (show 8 * (w * j) < 2 ^ 64 by rw [Nat.mul_comm w j]; omega_arith), Nat.mul_comm w j]
    omega_arith
  rw [e, BitVec.add_assoc, ← BitVec.ofNat_add, off, rowOff, Nat.add_comm]

/-- `rowPtr rd`: `rd :=` the address of row `j` (in `t2`) of the context at
`C` (`s10`), with `w` in `t0`. -/
theorem rowPtr_ok {s : State} {C : Addr} {w j : Nat} {rd : Reg} (hrd : rd = .t3 ∨ rd = .t4)
    (h10 : s.gpr .s10 = C) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (h2 : s.gpr .t2 = BitVec.ofNat 64 j)
    (hw : w < 2 ^ 31) (hj : j < 2 ^ 16) :
    WP isa (.block (rowPtr rd)) s fun t => (t.gpr rd = off C (rowOff w j) ∧ t.mem = s.mem) ∧ Keep [.t2, rd] s t := by
  rcases hrd with rfl | rfl <;>
  · refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold rowPtr
    brun [h10, h0, h2, row_bv hw hj]

/-- `loadRow a`: row `j` (in `t2`) of the context at `C` (`s10`) to array
`a`. -/
theorem loadRow_ok {s : State} {B C : Addr} {Z w N j a : Nat} (h : WCtx s B Z w N) (hc : CtxRd s B Z C w)
    (h10 : s.gpr .s10 = C) (h2 : s.gpr .t2 = BitVec.ofNat 64 j) (ha : a < 24) (hj : j < 34) :
    WP isa (loadRow a) s fun t =>
      (A t.mem B w a = wordsVal s.mem C (rowOff w j) w ∧ Outside B (slot w a) (8 * w) s.mem t.mem) ∧
        Keep [.t2, .t3, .t4, .t5, .s0] s t := by
  have hw := h.w2; have hw' := h.w31
  have hrow := row_fits (w := w) hj
  have hn := hc.hn
  have hsl := h.sl ha
  unfold loadRow
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (rowPtr_ok (rd := .t4) (.inr rfl) h10 h.t0 h2 hw' (by omega_arith)) fun t₁ ⟨⟨a4, m1⟩, k1⟩ => ?_
  have h1 := h.regs k1 (by decide) m1
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) h1.a7 h1.s5 a) fun t₂ ⟨⟨a3, m2⟩, k2⟩ => ?_
  have h2' := h1.regs k2 (by decide) m2
  have hm : t₂.mem = s.mem := by rw [m2, m1]
  refine WP.mono (Pub.copyIn_ok (P := C) (Zp := 8 * ctxWords w) (dS := rowOff w j) (dD := slot w a) h2'.scr hn
    (fun i hi => by rw [(k1.trans k2).2.1, (k1.trans k2).2.2]; exact hc.rd _ (by omega_arith))
    (fun i hi => by
      have : (off C (rowOff w j + 8 * i)).toNat = C.toNat + (rowOff w j + 8 * i) := by
        simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (a := rowOff w j + 8 * i) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
      rw [this]; have := hc.al; unfold rowOff; omega_arith)
    ((k2.gpr (by decide)).trans a4) a3 h2'.t0 (by omega_arith) hw' (slot_al w a) (by omega_arith) (by omega_arith)
    hc.sep) fun t ⟨⟨_, _, hw₁, ho⟩, kt⟩ => ⟨⟨?_, by rw [← hm]; exact ho⟩, ((k1.trans k2).trans kt).mono (by decide)⟩
  rw [← hm]
  exact wordsVal_of_words hw₁

/-! ## The selection -/

theorem mask_sub (b : Bool) : BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) = mask b := by
  cases b <;> decide

theorem wp_seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a b) s fun t => WP isa c t Q) : WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨_, _, he, _, _, he', hq⟩ := h
  cases he with
  | seq e1 e2 => exact ⟨_, _, .seq e1 (.seq e2 he'), hq⟩

theorem wp_seq_inv {a b : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq a b) s Q) :
    WP isa a s fun t => WP isa b t Q := by
  obtain ⟨_, _, he, hq⟩ := h
  cases he with
  | seq e1 e2 => exact ⟨_, _, e1, _, _, e2, hq⟩

theorem wp_block_prefix_seq {l₁ l₂ : List Instr} {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.block l₁) s fun t => WP isa (.seq (.block l₂) c) t Q) :
    WP isa (.seq (.block (l₁ ++ l₂)) c) s Q := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  exact WP.mono h fun _ h' => wp_seq_inv h'

theorem isEntry_ok {s : State} {e d : Nat} (h3 : s.gpr .a3 = BitVec.ofNat 64 e)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 d) (he : e < 32) (hd : d < 32) :
    WP isa (.block Generate.isEntry) s fun t => (t.gpr .s4 = mask (decide (e = d)) ∧ t.mem = s.mem) ∧
      Keep [.t2, .t3, .s4] s t := by
  have hx : (BitVec.ofNat 64 e ^^^ BitVec.ofNat 64 d).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    exact Nat.xor_lt_two_pow (by omega_arith) (by omega_arith)
  have hz : (BitVec.ofNat 64 e ^^^ BitVec.ofNat 64 d = 0) ↔ e = d := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
        at this
    · rintro rfl; rfl
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold Generate.isEntry
  brun [h3, h1, sub1_sign hx, Pub.pub_li0]
  rw [← mask_sub]
  by_cases h : e = d
  · simp [h]
  · simp [h, show ¬ (BitVec.ofNat 64 e ^^^ BitVec.ofNat 64 d = 0#64) from fun h' => h (hz.mp h')]

/-- The registers a choice of an entry writes. -/
def selERegs : List Reg := [.t2, .t3, .t4, .t5, .s0, .s2, .s3, .s4, .a0, .a2, .a3, .a5, .a6]

/-- `selEntry o t`: entry `e` (`a3`) to array `o` if it is the digit `d`
(`a1`), else array `t`; `e` advanced. -/
theorem selEntry_ok {s : State} {B C : Addr} {Z w N e d o t : Nat} (h : WCtx s B Z w N) (hc : CtxRd s B Z C w)
    (h10 : s.gpr .s10 = C) (h3 : s.gpr .a3 = BitVec.ofNat 64 e) (h1 : s.gpr .a1 = BitVec.ofNat 64 d)
    (he : e < 32) (hd : d < 32) (hot : o = 5 ∧ t = 4 ∨ o = 4 ∧ t = 5) :
    WP isa (Generate.selEntry o t) s fun u =>
      (A u.mem B w o = (if e = d then ent s.mem C w e else A s.mem B w t) ∧ Arrays B w [3, o] s.mem u.mem ∧
        u.gpr .a3 = BitVec.ofNat 64 (e + 1)) ∧ Keep selERegs s u := by
  have hn := h.nw
  have ho : o < 24 := by omega_arith
  have ht : t < 24 := by omega_arith
  unfold Generate.selEntry seqs
  rw [show ([.addi .t2 .a3 2] ++ rowPtr .t4 ++ base .t3 3 : List Instr) =
    ([.addi .t2 .a3 2] : List Instr) ++ (rowPtr .t4 ++ base .t3 3) from List.append_assoc _ _ _]
  refine wp_seq_assoc (wp_block_prefix_seq ?_)
  refine WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = BitVec.ofNat 64 (e + 2) ∧ u.mem = s.mem)
    (by brun [h3, ← BitVec.ofNat_add]) (by rfl) (by rfl)) fun s₁ ⟨⟨a2, m1⟩, k1⟩ => ?_
  have c1 := h.regs k1 (by decide) m1
  refine WP.mono (loadRow_ok (a := 3) c1 (hc.congr k1.2.1 k1.2.2) ((k1.gpr (by decide)).trans h10) a2 (by decide)
    (by omega_arith)) fun s₂ ⟨⟨v3, o3⟩, k2⟩ => ?_
  rw [m1] at v3 o3
  have c2 := c1.of k2 (by decide) (by rw [m1]; exact arrO o3 (by decide) (by decide))
  have k12 := k1.trans k2
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (isEntry_ok (e := e) (d := d) (by rw [k12.gpr (by decide), h3]) (by rw [k12.gpr (by decide), h1])
    he hd) fun t₁ ⟨⟨h4, n1⟩, j1⟩ => ?_
  have e1 := c2.regs j1 (by decide) n1
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) e1.a7 e1.s5 3) fun t₂ ⟨⟨a5, n2⟩, j2⟩ => ?_
  have e2 := e1.regs j2 (by decide) n2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) e2.a7 e2.s5 t) fun t₃ ⟨⟨a6, n3⟩, j3⟩ => ?_
  have e3 := e2.regs j3 (by decide) n3
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) e3.a7 e3.s5 o) fun t₄ ⟨⟨a2', n4⟩, j4⟩ => ?_
  have e4 := e3.regs j4 (by decide) n4
  have hm : t₄.mem = s₂.mem := by rw [n4, n3, n2, n1]
  have j14 := ((j1.trans j2).trans j3).trans j4
  refine WP.seq (WP.mono (selectAt_ok e4 (b := decide (e = d)) (o := o) (a := 3) (t := t) ho (by decide) ht
      (by omega_arith) (by omega_arith) a2' (by rw [j4.gpr (by decide), j3.gpr (by decide), a5])
      (by rw [j4.gpr (by decide), a6]) (by rw [j4.gpr (by decide), j3.gpr (by decide), j2.gpr (by decide), h4]))
    fun s₃ ⟨⟨hv, hout⟩, k3⟩ => ?_)
  rw [hm] at hv hout
  refine WP.mono (WP.keep [.a3] (Q := fun u => u.gpr .a3 = BitVec.ofNat 64 (e + 1) ∧ u.mem = s₃.mem)
    (by brun [(k3.gpr (r := .a3) (by decide)).trans ((j14.gpr (r := .a3) (by decide)).trans
      ((k12.gpr (r := .a3) (by decide)).trans h3)), ← BitVec.ofNat_add]) (by rfl) (by rfl))
    fun u ⟨⟨u3, um⟩, ku⟩ => ⟨⟨?_, ?_, u3⟩, (((k12.trans j14).trans k3).trans ku).mono (by decide)⟩
  · rw [um, hv, v3]
    by_cases hb : e = d
    · simp [hb]
    · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact arr_out o3 ht (by omega_arith) hn
  · rw [um]
    exact ((arr1 o3 (by omega_arith)).mono (by simp)).trans ((arr1 hout (by omega_arith)).mono (by simp))

/-- A change of arrays of the working space keeps the context. -/
theorem arrays_ctx {B C : Addr} {Z w n : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hjs : ∀ j ∈ js, j < 24) (hZ : slot w 24 ≤ Z) (hsep : ∀ x, ofs C x < n → Z ≤ ofs B x) :
    Outside C n (2 ^ 64) m m' := fun x hx => h x fun j hj => Or.inr (by
  have := slot_lt (w := w) (hjs j hj)
  show slot w j + 8 * (w + 2) ≤ (x - B).toNat
  rcases hx with hx | hx
  · have h' : Z ≤ (x - B).toNat := hsep x hx
    omega_arith
  · have := (x - C).isLt; simp only [ofs] at hx; omega_arith)

theorem ent_keep {C : Addr} {w a : Nat} {m m' : Mem} (h : Outside C (8 * ctxWords w) (2 ^ 64) m m')
    (hn : C.toNat + 8 * ctxWords w ≤ 2 ^ 64) (ha : a < 32) : ent m' C w a = ent m C w a :=
  Outside.wordsVal h (Or.inl (row_fits (w := w) (by omega_arith)))
    (by have := row_fits (w := w) (j := a + 2) (by omega_arith); omega_arith)

/-- The selection after the entries below `2 k`, from `s₀`. -/
structure SelI (s₀ : State) (B C : Addr) (Z w N d k : Nat) (u : State) : Prop where
  win : WCtx u B Z w N
  ctx : CtxRd u B Z C w
  h10 : u.gpr .s10 = C
  h1 : u.gpr .a1 = BitVec.ofNat 64 d
  h3 : u.gpr .a3 = BitVec.ofNat 64 (2 * k)
  acc : A u.mem B w 4 = if d < 2 * k then ent s₀.mem C w d else 0
  out : Arrays B w [3, 4, 5] s₀.mem u.mem
  keep : Keep selERegs s₀ u

/-- `select`: array 4 `:=` entry `d` (`a1`) of the context (`s10`). -/
theorem select_ok {s : State} {B C : Addr} {Z w N d : Nat} (h : WCtx s B Z w N) (hc : CtxRd s B Z C w)
    (h10 : s.gpr .s10 = C) (h1 : s.gpr .a1 = BitVec.ofNat 64 d) (hd : d < 32) :
    WP isa Generate.select s fun u =>
      (A u.mem B w 4 = ent s.mem C w d ∧ Arrays B w [3, 4, 5] s.mem u.mem) ∧ Keep selERegs s u := by
  have hn := h.nw
  have hZ := h.hZ
  have hw := h.w2; have hw' := h.w31
  have entK : ∀ {m m' : Mem}, Arrays B w [3, 4, 5] m m' → ∀ a < 32, ent m' C w a = ent m C w a :=
    fun hm a ha => ent_keep (arrays_ctx hm (by simp) hZ hc.sep) hc.hn ha
  unfold Generate.select seqs
  refine WP.seq (WP.mono (Pub.base_ok (rd := .t3) (by decide) h.a7 h.s5 4) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have c1 := h.regs k1 (by decide) m1
  refine WP.seq (WP.mono (zeroWords_ok c1.scr a3 c1.t0 (by omega_arith) hw' (slot_al w 4)
    (by have := h.sl (j := 4) (by decide); omega_arith)) fun s₂ ⟨⟨_, z2, o2⟩, k2⟩ => ?_)
  have c2 := c1.of k2 (by decide) (arrO o2 (by decide) (by decide))
  rw [m1] at o2
  refine WP.seq (WP.mono (WP.keep [.a3] (Q := fun u => u.gpr .a3 = BitVec.ofNat 64 (2 * 0) ∧ u.mem = s₂.mem)
    (by brun [Pub.pub_li0]) (by rfl) (by rfl)) fun s₃ ⟨⟨a33, m3⟩, k3⟩ => ?_)
  have k13 := (k1.trans k2).trans k3
  have o3 : Arrays B w [3, 4, 5] s.mem s₃.mem := by
    rw [m3]; exact (arr1 o2 (by omega_arith)).mono (by simp)
  have i0 : SelI s B C Z w N d 0 s₃ := by
    refine ⟨c2.regs k3 (by decide) m3, hc.congr k13.2.1 k13.2.2, (k13.gpr (by decide)).trans h10,
      (k13.gpr (by decide)).trans h1, a33, ?_, o3, k13.mono (by decide)⟩
    rw [ite_eq_right_iff.mpr fun h => absurd h (by omega_arith), m3]
    exact Pub.wsv_zero z2
  refine WP.mono (count_loop (n := 16) (cr := .t2) (by decide) (SelI s B C Z w N d)
    (fun k hk u hu => ?_) i0) fun u hu => ⟨⟨by rw [hu.acc, ite_eq_left_iff.mpr fun h => absurd (by omega_arith) h],
      hu.out⟩, hu.keep⟩
  unfold seqs
  refine WP.seq (WP.mono (selEntry_ok (e := 2 * k) (d := d) (o := 5) (t := 4) hu.win hu.ctx hu.h10 hu.h3 hu.h1
    (by omega_arith) hd (.inl ⟨rfl, rfl⟩)) fun v₁ ⟨⟨b5, o5, j3⟩, kv⟩ => ?_)
  have cv := hu.win.of kv (by decide) (Win.win_of_arrays o5 (by simp))
  refine WP.seq (WP.mono (selEntry_ok (e := 2 * k + 1) (d := d) (o := 4) (t := 5) cv (hu.ctx.congr kv.2.1 kv.2.2)
    ((kv.gpr (by decide)).trans hu.h10) j3 ((kv.gpr (by decide)).trans hu.h1) (by omega_arith) hd
    (.inr ⟨rfl, rfl⟩)) fun v₂ ⟨⟨b4, o4, j4⟩, kw⟩ => ?_)
  refine WP.mono (WP.keep [.t2] (Q := fun v => v.gpr .t2 = BitVec.ofNat 64 (2 * k + 1 + 1) - BitVec.ofNat 64 32 ∧
    v.mem = v₂.mem) (by brun [j4]) (by rfl) (by rfl)) fun v ⟨⟨v2, vm⟩, kx⟩ => ⟨?_, ?_⟩
  · have ov : Arrays B w [3, 4, 5] s.mem v.mem := by
      rw [vm]; exact (hu.out.trans (o5.mono (by simp))).trans (o4.mono (by simp))
    refine ⟨(cv.of kw (by decide) (Win.win_of_arrays o4 (by simp))).regs kx (by decide) vm,
      ((hu.ctx.congr kv.2.1 kv.2.2).congr kw.2.1 kw.2.2).congr kx.2.1 kx.2.2,
      (kx.gpr (by decide)).trans ((kw.gpr (by decide)).trans ((kv.gpr (by decide)).trans hu.h10)),
      (kx.gpr (by decide)).trans ((kw.gpr (by decide)).trans ((kv.gpr (by decide)).trans hu.h1)),
      by rw [kx.gpr (by decide), j4]; congr 1, ?_, ov, ((hu.keep.trans kv).trans kw).trans kx |>.mono (by decide)⟩
    rw [vm, b4, b5, entK hu.out _ (by omega_arith), entK (hu.out.trans (o5.mono (by simp))) _ (by omega_arith)]
    rw [hu.acc]
    by_cases e1 : 2 * k + 1 = d
    · subst e1; simp only [↓reduceIte, show 2 * k + 1 < 2 * (k + 1) by omega_arith]
    · by_cases e0 : 2 * k = d
      · subst e0; simp only [↓reduceIte, e1, show 2 * k < 2 * (k + 1) by omega_arith]
      · rw [ite_eq_right_iff.mpr fun h => absurd h e1, ite_eq_right_iff.mpr fun h => absurd h e0]
        by_cases hl : d < 2 * k
        · rw [ite_eq_left_iff.mpr fun h => absurd hl h, ite_eq_left_iff.mpr fun h => absurd (by omega_arith) h]
        · rw [ite_eq_right_iff.mpr fun h => absurd h hl, ite_eq_right_iff.mpr fun h => absurd h (by omega_arith)]
  · rw [v2, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith

end VG.Proof.Ffdh.RISCV64.Cached
