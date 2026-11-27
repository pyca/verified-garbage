module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.Cached
public import VerifiedGarbage.Proof.Bignum.RISCV64.ModExpWin
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
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
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Ffdh.CombBitBytes
import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.Scalar
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMont
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.RISCV64.MontFios
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Bignum.Math

/-!
# FFDH's comb on RISC-V

`step_ok`: a row of the comb, a square, the digit's entry and a product.
`comb_ok`: `g^x mod p` from the context's rows.
-/

@[expose] public section

/-! # FFDH's context on RISC-V: its rows

The context is `3 + 34 w` words: three public words, then rows of `w`
words, row `j` at byte `rowOff w j` (`p`, `R² mod p`, then entry `e` at row
`2 + e`). `rowPtr_ok`: the address of a row; `loadRow_ok`: a row to an
array of the working space, by `copyWords`. `select_ok`: array 4 `:=` the
digit's entry, reading every entry under an equality mask. -/

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

/-- `Win.mask`'s subtraction form (main's `MillerRabin.RISCV64.mask_sub` is
about its own `mask`). -/
theorem mask_sub (b : Bool) : BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) = mask b := by
  cases b <;> decide

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
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = BitVec.ofNat 64 (e + 2) ∧ u.mem = s.mem)
    (by brun [h3, ← BitVec.ofNat_add]) (by rfl) (by rfl)) fun s₁ ⟨⟨a2, m1⟩, k1⟩ => ?_
  have c1 := h.regs k1 (by decide) m1
  refine WP.mono (wp_seq_inv (WP.mono (loadRow_ok (a := 3) c1 (hc.congr k1.2.1 k1.2.2)
    ((k1.gpr (by decide)).trans h10) a2 (by decide) (by omega_arith)) fun s₂ ⟨⟨v3, o3⟩, k2⟩ => ?_))
    (fun _ h => WP.seq h)
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

/-! # FFDH's comb on RISC-V: a row's digit

`bit_ok`: bit `k` of x, from its octets, most significant first.
`digit_ok`: the five bits `i + j rows` of row `i`'s digit. -/

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Generate
open VG.Proof.Bignum.RISCV64

theorem eval_ltu' (s : State) (a b : Reg) : isa.eval (.ltu a b) s = some (decide (s.gpr a < s.gpr b)) := rfl

theorem ofNat_lt_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide (BitVec.ofNat 64 a < BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_shr3 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 3 = BitVec.ofNat 64 (a / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h]
  rw [Nat.mod_eq_of_lt (by omega_arith)]

theorem ofNat_and7 (a : Nat) : BitVec.ofNat 64 a &&& BitVec.ofNat 64 7 = BitVec.ofNat 64 (a % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_mod_of_dvd _ (by decide)]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))).symm

/-- A byte's bit `j`. -/
theorem bit_bv (b : Byte) {j : Nat} (hj : j < 8) :
    (b.setWidth 64 >>> ((BitVec.ofNat 64 j).toNat % 64)) &&& BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (b.toNat / 2 ^ j % 2) := by
  apply BitVec.eq_of_toNat_eq
  have hb := b.isLt
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show j < 64 by omega_arith),
    Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega_arith), Nat.shiftRight_eq_div_pow,
    show (1 : Nat) % 2 ^ 64 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have : b.toNat / 2 ^ j % 2 ^ 1 < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  rw [Nat.mod_eq_of_lt this]

/-- `bit`: `t5 :=` bit `k` (`t6`) of x, the `L` octets at `X` (`s8`), `L` in
`s11`; 0 from `8 L` up. -/
theorem bit_ok {s : State} {X : Addr} {xb : List Byte} {k : Nat}
    (h11 : s.gpr .s11 = BitVec.ofNat 64 xb.length) (h6 : s.gpr .t6 = BitVec.ofNat 64 k) (h8 : s.gpr .s8 = X)
    (hrd : ∀ n < xb.length, InRegions (s.rd ++ s.wr) (off X n) 1)
    (hval : ∀ n (h : n < xb.length), s.mem (off X n) = xb[n]) (hk : k < 2 ^ 31) (hL : 8 * xb.length < 2 ^ 31) :
    WP isa bit s fun t =>
      (t.gpr .t5 = BitVec.ofNat 64 (Spec.Rsa.os2ip xb / 2 ^ k % 2) ∧ t.mem = s.mem) ∧ Keep [.t2, .t5] s t := by
  unfold bit
  refine WP.seq (WP.mono (WP.keep [.t2] (Q := fun t => t.gpr .t2 = BitVec.ofNat 64 (8 * xb.length) ∧ t.mem = s.mem)
    (by brun [h11, Pre.ofNat_shl3]) (by rfl) (by rfl))
    fun s₁ ⟨⟨a2, m1⟩, k1⟩ => ?_)
  have g6 : s₁.gpr .t6 = BitVec.ofNat 64 k := (k1.gpr (by decide)).trans h6
  refine WP.ite (decide (k < 8 * xb.length)) (by
      rw [eval_ltu', g6, a2, ofNat_lt_ofNat (by omega_arith) (by omega_arith)]) (fun hb => ?_) (fun hb => ?_)
  · have hb' : k < 8 * xb.length := by simpa using hb
    obtain ⟨n, hn⟩ : ∃ n, n = xb.length - 1 - k / 8 := ⟨_, rfl⟩
    have hidx : n < xb.length := by omega_arith
    have l3 : InRegions (s₁.rd ++ s₁.wr) (X + BitVec.ofNat 64 n) 1 := by
      rw [k1.2.1, k1.2.2]; exact hrd _ hidx
    have v3 : (s₁.mem.read (X + BitVec.ofNat 64 n) 1).setWidth 64 = (xb[n]'hidx).setWidth 64 := by
      rw [Pub.read1_setWidth, m1]; exact congrArg (BitVec.setWidth 64) (hval _ hidx)
    refine WP.mono (WP.keep [.t2, .t5] (Q := fun t =>
        t.gpr .t5 = BitVec.ofNat 64 ((xb[n]'hidx).toNat / 2 ^ (k % 8) % 2) ∧ t.mem = s₁.mem) (by
      brun [g6, (k1.gpr (r := .s11) (by decide)).trans h11, (k1.gpr (r := .s8) (by decide)).trans h8,
        ofNat_shr3 (show k < 2 ^ 64 by omega_arith),
        Offset.ofNat_sub_ofNat (show k / 8 ≤ xb.length by omega_arith),
        Offset.ofNat_sub_ofNat (show 1 ≤ xb.length - k / 8 by omega_arith),
        show xb.length - k / 8 - 1 = n by omega_arith, add_ofNat_zero, l3, v3, ofNat_and7, exec_srl_reg,
        bit_bv _ (Nat.mod_lt k (show 0 < 8 by decide))]) (by rfl) (by rfl)) fun t ⟨⟨t5, tm⟩, kt⟩ =>
      ⟨⟨?_, tm.trans m1⟩, (k1.trans kt).mono (by decide)⟩
    rw [t5, CombBitBytes.os2ip_bit xb k hb']
    subst hn; rfl
  · have hb' : ¬ k < 8 * xb.length := by simpa using hb
    refine WP.mono (WP.keep [.t5] (Q := fun t => t.gpr .t5 = BitVec.ofNat 64 0 ∧ t.mem = s₁.mem)
      (by brun [Pub.pub_li0]) (by rfl) (by rfl)) fun t ⟨⟨t5, tm⟩, kt⟩ =>
        ⟨⟨?_, tm.trans m1⟩, (k1.trans kt).mono (by decide)⟩
    rw [t5]
    have hlt : Spec.Rsa.os2ip xb < 2 ^ k :=
      Nat.lt_of_lt_of_le (VG.Proof.Bignum.os2ip_lt xb) (by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega_arith))
    rw [Nat.div_eq_of_lt hlt]

theorem tooth_bv {acc b j : Nat} (hb : b < 2) (hj : j < 5) (ha : acc < 2 ^ j) :
    BitVec.ofNat 64 acc ||| BitVec.ofNat 64 b <<< j = BitVec.ofNat 64 (acc + 2 ^ j * b) := by
  have h2j : 2 ^ j ≤ 16 := Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) (show j ≤ 4 by omega_arith))
    (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show acc < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show b * 2 ^ j < 2 ^ 64 by
      have : b * 2 ^ j ≤ 1 * 16 := Nat.mul_le_mul (by omega_arith) h2j
      omega_arith),
    Nat.mod_eq_of_lt (show acc + 2 ^ j * b < 2 ^ 64 by
      have : 2 ^ j * b ≤ 16 * 1 := Nat.mul_le_mul h2j (by omega_arith)
      omega_arith),
    Nat.or_comm, Nat.mul_comm b, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.add_comm]

/-- What `bit` reads: the rows (`s7`), and the `L` octets of x at `X`
(`s8`), `L` in `s11`. -/
structure XCtx (s : State) (X : Addr) (xb : List Byte) (rows : Nat) : Prop where
  h11 : s.gpr .s11 = BitVec.ofNat 64 xb.length
  h7 : s.gpr .s7 = BitVec.ofNat 64 rows
  h8 : s.gpr .s8 = X
  hrd : ∀ n < xb.length, InRegions (s.rd ++ s.wr) (off X n) 1
  hval : ∀ n (h : n < xb.length), s.mem (off X n) = xb[n]
  hL : 8 * xb.length < 2 ^ 31

/-- The registers `digit` writes. -/
def digitRegs : List Reg := [.a1, .t2, .t5, .t6]

theorem XCtx.keep {s t : State} {X : Addr} {xb : List Byte} {rows : Nat} (h : XCtx s X xb rows)
    (hm : t.mem = s.mem) (k : Keep digitRegs s t) : XCtx t X xb rows :=
  ⟨(k.gpr (by decide)).trans h.h11, (k.gpr (by decide)).trans h.h7, (k.gpr (by decide)).trans h.h8,
    fun n hn => by rw [k.2.1, k.2.2]; exact h.hrd n hn, fun n hn => by rw [hm]; exact h.hval n hn, h.hL⟩

/-- `tooth j`: `a1 := acc + 2^j` bit `i + j rows` of x, for `acc < 2^j`; `t6`
on to the next tooth's bit. -/
theorem tooth_ok {s : State} {X : Addr} {xb : List Byte} {i rows j acc : Nat} (h : XCtx s X xb rows)
    (h6 : s.gpr .t6 = BitVec.ofNat 64 (i + j * rows)) (hj : j < 5) (hk : i + 5 * rows < 2 ^ 31)
    (h1 : s.gpr .a1 = BitVec.ofNat 64 acc) (ha : acc < 2 ^ j) :
    WP isa (tooth j) s fun t =>
      (t.gpr .a1 = BitVec.ofNat 64 (acc + 2 ^ j * Rsa.FixedBaseComb.bit (Spec.Rsa.os2ip xb) (i + j * rows)) ∧
        t.gpr .t6 = BitVec.ofNat 64 (i + (j + 1) * rows) ∧ XCtx t X xb rows ∧ t.mem = s.mem) ∧
        Keep digitRegs s t := by
  have hjr : j * rows ≤ 4 * rows := Nat.mul_le_mul_right _ (by omega_arith)
  unfold tooth
  refine WP.seq (WP.mono (bit_ok h.h11 h6 h.h8 h.hrd h.hval (by omega_arith) h.hL) fun t ⟨⟨a5, m⟩, k⟩ => ?_)
  have hb : Spec.Rsa.os2ip xb / 2 ^ (i + j * rows) % 2 < 2 := Nat.mod_lt _ (by decide)
  have g1 : t.gpr .a1 = BitVec.ofNat 64 acc := (k.gpr (by decide)).trans h1
  have g6 : t.gpr .t6 = BitVec.ofNat 64 (i + j * rows) := (k.gpr (by decide)).trans h6
  have g7 : t.gpr .s7 = BitVec.ofNat 64 rows := (k.gpr (by decide)).trans h.h7
  have e6 : BitVec.ofNat 64 (i + j * rows) + BitVec.ofNat 64 rows = BitVec.ofNat 64 (i + (j + 1) * rows) := by
    rw [← BitVec.ofNat_add, Nat.succ_mul, Nat.add_assoc]
  have post : ∀ u : State, (u.gpr .a1 = BitVec.ofNat 64 (acc + 2 ^ j *
      Rsa.FixedBaseComb.bit (Spec.Rsa.os2ip xb) (i + j * rows)) ∧
      u.gpr .t6 = BitVec.ofNat 64 (i + (j + 1) * rows) ∧ u.mem = t.mem) ∧ Keep [.t5, .a1, .t6] t u →
      (u.gpr .a1 = BitVec.ofNat 64 (acc + 2 ^ j * Rsa.FixedBaseComb.bit (Spec.Rsa.os2ip xb) (i + j * rows)) ∧
        u.gpr .t6 = BitVec.ofNat 64 (i + (j + 1) * rows) ∧ XCtx u X xb rows ∧ u.mem = s.mem) ∧
        Keep digitRegs s u :=
    fun u ⟨⟨b1, b6, bm⟩, bk⟩ => ⟨⟨b1, b6, h.keep (bm.trans m) ((k.trans bk).mono (by decide)), bm.trans m⟩,
      (k.trans bk).mono (by decide)⟩
  by_cases h0 : j = 0
  · subst h0
    have ha0 : acc = 0 := by omega_arith
    subst ha0
    simp only [ite_true, List.nil_append]
    refine WP.mono (WP.keep [.t5, .a1, .t6] ?_ (by rfl) (by rfl)) post
    brun [a5, g1, g6, g7, e6]
    rw [Nat.zero_add, Nat.one_mul]
    exact BitVec.zero_or
  · simp only [h0, ite_false, List.singleton_append]
    refine WP.mono (WP.keep [.t5, .a1, .t6] ?_ (by rfl) (by rfl)) post
    brun [a5, g1, g6, g7, e6, tooth_bv hb hj ha, show j < 64 by omega_arith]
    rfl

/-- The comb's digit of row `i`, for `rows` rows: `FixedBaseComb.digit` for
`rows = rows bits`. -/
def combDigit (x i rows : Nat) : Nat :=
  Rsa.FixedBaseComb.bit x i + 2 * Rsa.FixedBaseComb.bit x (i + rows) +
    4 * Rsa.FixedBaseComb.bit x (i + 2 * rows) + 8 * Rsa.FixedBaseComb.bit x (i + 3 * rows) +
    16 * Rsa.FixedBaseComb.bit x (i + 4 * rows)

theorem combDigit_eq (bits x i : Nat) :
    combDigit x i (Spec.Rsa.FixedBaseComb.rows bits) = Rsa.FixedBaseComb.digit bits x i := rfl

theorem seqs_teeth : seqs ((List.range 5).map tooth) =
    .seq (tooth 0) (.seq (tooth 1) (.seq (tooth 2) (.seq (tooth 3) (tooth 4)))) := rfl

/-- `digit`: `a1 :=` row `i`'s digit of x, for `i + 1` in `s9`. -/
theorem digit_ok {s : State} {X : Addr} {xb : List Byte} {i rows : Nat} (h : XCtx s X xb rows)
    (h9 : s.gpr .s9 = BitVec.ofNat 64 (i + 1)) (hk : i + 5 * rows < 2 ^ 31) :
    WP isa digit s fun t =>
      (t.gpr .a1 = BitVec.ofNat 64 (combDigit (Spec.Rsa.os2ip xb) i rows) ∧ t.mem = s.mem) ∧
        Keep digitRegs s t := by
  unfold digit
  rw [seqs_teeth]
  have hb := Rsa.FixedBaseComb.bit_lt (Spec.Rsa.os2ip xb)
  refine WP.seq (WP.mono (WP.keep [.a1, .t6] (Q := fun t => t.gpr .a1 = BitVec.ofNat 64 0 ∧
    t.gpr .t6 = BitVec.ofNat 64 (i + 0 * rows) ∧ t.mem = s.mem)
    (by brun [h9, Pub.pub_li0, exec_addi_neg_lit (show 1 ≤ 2048 by decide),
          Offset.ofNat_sub_ofNat (show 1 ≤ i + 1 by omega_arith), Nat.add_sub_cancel]
        rw [Nat.zero_mul, Nat.add_zero])
      (by rfl) (by rfl))
    fun t₀ ⟨⟨a0, b0, m0⟩, k0⟩ => ?_)
  have c0 := h.keep m0 (k0.mono (by decide))
  refine WP.seq (WP.mono (tooth_ok (j := 0) c0 b0 (by decide) hk a0 (by decide)) fun t₁ ⟨⟨a1, b1, c1, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (tooth_ok (j := 1) c1 b1 (by decide) hk a1 (by have := hb (i + 0 * rows); omega_arith))
    fun t₂ ⟨⟨a2, b2, c2, m2⟩, k2⟩ => ?_)
  refine WP.seq (WP.mono (tooth_ok (j := 2) c2 b2 (by decide) hk a2
    (by have := hb (i + 0 * rows); have := hb (i + 1 * rows); omega_arith)) fun t₃ ⟨⟨a3, b3, c3, m3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (tooth_ok (j := 3) c3 b3 (by decide) hk a3
    (by have := hb (i + 0 * rows); have := hb (i + 1 * rows); have := hb (i + 2 * rows); omega_arith))
    fun t₄ ⟨⟨a4, b4, c4, m4⟩, k4⟩ => ?_)
  refine WP.mono (tooth_ok (j := 4) c4 b4 (by decide) hk a4
    (by have := hb (i + 0 * rows); have := hb (i + 1 * rows); have := hb (i + 2 * rows)
        have := hb (i + 3 * rows); omega_arith)) fun t ⟨⟨a5, _, _, m5⟩, k5⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · rw [a5]
    unfold combDigit
    simp only [Nat.zero_add, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.pow_zero, Nat.pow_one,
      show (2 : Nat) ^ 2 = 4 from rfl, show (2 : Nat) ^ 3 = 8 from rfl, show (2 : Nat) ^ 4 = 16 from rfl]
  · rw [m5, m4, m3, m2, m1, m0]
  · have k05 := (((((k0.mono (rs' := digitRegs) (by decide)).trans k1).trans k2).trans k3).trans k4).trans k5
    exact k05.mono (by decide)

end VG.Proof.Ffdh.RISCV64.Cached

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Generate
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum.RISCV64.Win (WCtx WinO A arr_eq arr1 arrO slot_lt win_of_arrays)
open VG.Proof.Bignum (slot slot_sep Arrays)

/-- `g^E R mod p`, in Montgomery form. -/
abbrev combM (G P w E : Nat) : Nat := Spec.Rsa.powMod G E P * 2 ^ (64 * w) % P

theorem combM_lt {G P w : Nat} (hP : 0 < P) (E : Nat) : combM G P w E < P := Nat.mod_lt _ hP

/-- A change of arrays 1 to 23 keeps the context. -/
theorem win_ctx {B C : Addr} {Z w n : Nat} {m m' : Mem} (h : WinO B w m m') (hZ : slot w 24 ≤ Z)
    (hsep : ∀ x, ofs C x < n → Z ≤ ofs B x) : Outside C n (2 ^ 64) m m' :=
  ctx_of_scr h (by have := Win.slot24 w; omega_arith) hsep

/-- x's octets, apart from the working space, are kept by a change of
arrays 1 to 23. -/
theorem win_byte {B X : Addr} {Z w n : Nat} {m m' : Mem} (h : WinO B w m m') (hZ : slot w 24 ≤ Z)
    (hsep : ∀ y, ofs B y < Z → off X n ≠ y) : m' (off X n) = m (off X n) :=
  h _ (Or.inr (by
    have := Win.slot24 w
    show slot w 1 + 23 * (8 * (w + 2)) ≤ (off X n - B).toNat
    by_cases hl : (off X n - B).toNat < Z
    · exact absurd rfl (hsep _ hl)
    · omega_arith))

/-- The registers a row writes. -/
def stepRegs : List Reg := Pub.montRegs ++ digitRegs ++ selERegs ++ [.s9]

/-- The comb with `n` rows left (`s9`), from `s₀`, the accumulator (array 6)
`Acc`; the context at `C` (`s10`), x's octets at `X` (`s8`). -/
structure CS (s₀ : State) (B C X : Addr) (Z w : Nat) (xb : List Byte) (P G bits n Acc : Nat) (u : State) :
    Prop where
  win : WCtx u B Z w P
  h10 : u.gpr .s10 = C
  ctx : CtxRd u B Z C w
  ents : ∀ a < 32, ent u.mem C w a = combM G P w (Spec.Rsa.FixedBaseComb.exponent bits a)
  h9 : u.gpr .s9 = BitVec.ofNat 64 n
  xc : XCtx u X xb (Spec.Rsa.FixedBaseComb.rows bits)
  xsep : ∀ n < xb.length, ∀ y, ofs B y < Z → off X n ≠ y
  acc : A u.mem B w 6 = Acc
  one : A u.mem B w 7 = 1
  out : WinO B w s₀.mem u.mem
  keep : Keep stepRegs s₀ u

/-- `CS` after a change of arrays 1 to 23 but 7, and registers of a row
but `s9`. -/
theorem CS.frame {s₀ u v : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits n Acc n' Acc' : Nat}
    (h : CS s₀ B C X Z w xb P G bits n Acc u) {rs : List Reg} (ho : WinO B w u.mem v.mem)
    (h7 : A v.mem B w 7 = A u.mem B w 7) (k : Keep rs u v) (hrs : ∀ r ∈ rs, r ∈ stepRegs := by decide)
    (h9 : v.gpr .s9 = BitVec.ofNat 64 n') (hacc : A v.mem B w 6 = Acc') :
    CS s₀ B C X Z w xb P G bits n' Acc' v := by
  have hZ := h.win.hZ
  have hg : ∀ r ∈ ([.s10, .s11, .s7, .s8, .a7, .s5, .t0, .t1] : List Reg), r ∉ stepRegs := by decide
  have g : ∀ r ∈ ([.s10, .s11, .s7, .s8, .a7, .s5, .t0, .t1] : List Reg), v.gpr r = u.gpr r :=
    fun r hr => k.gpr fun h' => hg r hr (hrs r h')
  have hc' : ∀ r ∈ Win.ctxRegs, r ∉ stepRegs := by decide
  have hctx : Outside C (8 * ctxWords w) (2 ^ 64) u.mem v.mem := win_ctx ho hZ h.ctx.sep
  refine ⟨h.win.of k (fun r hr h' => hc' r hr (hrs r h')) ho, (g .s10 (by decide)).trans h.h10,
    h.ctx.congr k.2.1 k.2.2, fun a ha => by rw [ent_keep hctx h.ctx.hn ha]; exact h.ents a ha, h9,
    ⟨(g .s11 (by decide)).trans h.xc.h11, (g .s7 (by decide)).trans h.xc.h7, (g .s8 (by decide)).trans h.xc.h8,
      fun n hn => by rw [k.2.1, k.2.2]; exact h.xc.hrd n hn,
      fun n hn => by rw [win_byte ho hZ (h.xsep n hn)]; exact h.xc.hval n hn, h.xc.hL⟩,
    h.xsep, hacc, by rw [h7]; exact h.one, Outside.trans h.out ho,
    (h.keep.trans k).mono (fun r hr => by
      simp only [List.mem_append] at hr; rcases hr with hr | hr
      · exact hr
      · exact hrs r hr)⟩

/-- What a row needs besides `CS`. -/
structure RowP (P bits : Nat) : Prop where
  odd : P % 2 = 1
  one : 1 < P
  rows : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639

/-- One row: from `n + 1` rows left to `n`. -/
theorem step_ok {s₀ u : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits n : Nat} (hq : RowP P bits)
    (h : CS s₀ B C X Z w xb P G bits (n + 1)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (n + 1))) u)
    (hn : n < Spec.Rsa.FixedBaseComb.rows bits) :
    WP isa step u fun v =>
      CS s₀ B C X Z w xb P G bits n (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) n)) v := by
  have hZ := h.win.hZ
  have hnw := h.win.nw
  have hP : 0 < P := by have := hq.one; omega_arith
  have cop := VG.Proof.Bignum.coprime_pow2 hq.odd (64 * w)
  have h1 := hq.rows
  generalize hx : Spec.Rsa.os2ip xb = x at h ⊢
  unfold step
  simp only [seqs]
  -- The square.
  refine WP.seq (WP.mono (h.win.mont (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [h.acc]; exact combM_lt hP _))
    fun u₁ ⟨⟨_, lt1, eq1, fr1, o1⟩, k1⟩ => ?_)
  rw [h.acc] at eq1
  have a1 := Rsa.FixedBaseComb.mont_square_encoded cop lt1 rfl eq1
  have c1 := h.frame o1 (fr1 7 (by decide) (by decide) (by decide) (by decide)) k1 (by decide)
    (by rw [k1.gpr (by decide)]; exact h.h9) a1
  -- The digit.
  refine WP.seq (WP.mono (digit_ok c1.xc c1.h9 (by omega_arith)) fun u₂ ⟨⟨a2, m2⟩, k2⟩ => ?_)
  rw [hx, combDigit_eq] at a2
  have hd := Rsa.FixedBaseComb.digit_lt bits x n
  have c2 := c1.frame (Acc' := combM G P w (2 * Rsa.FixedBaseComb.high bits x (n + 1)))
    (by rw [m2]; exact Outside.refl _ _ _ _) (by rw [m2]) k2 (by decide) (by rw [k2.gpr (by decide)]; exact c1.h9)
    (by rw [m2]; exact c1.acc)
  -- The entry.
  refine WP.seq (WP.mono (select_ok c2.win c2.ctx c2.h10 a2 hd) fun u₃ ⟨⟨a3, o3⟩, k3⟩ => ?_)
  rw [c2.ents _ hd] at a3
  have c3 := c2.frame (Acc' := combM G P w (2 * Rsa.FixedBaseComb.high bits x (n + 1)))
    (win_of_arrays o3 (by simp)) (arr_eq o3 (by decide) (by simp) hnw) k3 (by decide)
    (by rw [k3.gpr (by decide)]; exact c2.h9) (by rw [arr_eq o3 (by decide) (by simp) hnw]; exact c2.acc)
  -- The product.
  refine WP.seq (WP.mono (c3.win.mont (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [a3]; exact combM_lt hP _))
    fun u₄ ⟨⟨_, lt4, eq4, fr4, o4⟩, k4⟩ => ?_)
  rw [c3.acc, a3] at eq4
  have a4 := Rsa.FixedBaseComb.mont_product_encoded cop lt4 rfl rfl eq4
  rw [← Rsa.FixedBaseComb.high_step bits x n hn] at a4
  have c4 := c3.frame o4 (fr4 7 (by decide) (by decide) (by decide) (by decide)) k4 (by decide)
    (by rw [k4.gpr (by decide)]; exact c3.h9) a4
  -- `n` rows left.
  refine WP.mono (WP.keep [.s9] (Q := fun v => v.gpr .s9 = BitVec.ofNat 64 n ∧ v.mem = u₄.mem) (by
    brun [c4.h9, exec_addi_neg_lit (show 1 ≤ 2048 by decide),
      Offset.ofNat_sub_ofNat (show 1 ≤ n + 1 by omega_arith), Nat.add_sub_cancel])
    (by rfl) (by rfl)) fun v ⟨⟨a5, m5⟩, k5⟩ => ?_
  exact c4.frame (by rw [m5]; exact Outside.refl _ _ _ _) (by rw [m5]) k5 (by decide) a5 (by rw [m5]; exact c4.acc)

/-- The rows, from `rows` left, by `wp_countdown` on `s9`. -/
theorem rows_ok {s₀ u : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits : Nat} (hq : RowP P bits)
    (h : CS s₀ B C X Z w xb P G bits (Spec.Rsa.FixedBaseComb.rows bits)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (Spec.Rsa.FixedBaseComb.rows bits))) u)
    (hpos : 0 < Spec.Rsa.FixedBaseComb.rows bits) :
    WP isa (.loop step (.nonzero .s9)) u
      (CS s₀ B C X Z w xb P G bits 0 (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0))) := by
  have h1 := hq.rows
  refine WP.mono (wp_countdown (body := step) (cnt := .s9) (N := Spec.Rsa.FixedBaseComb.rows bits)
    (by omega_arith) hpos
    (fun i v => CS s₀ B C X Z w xb P G bits (Spec.Rsa.FixedBaseComb.rows bits - i)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (Spec.Rsa.FixedBaseComb.rows bits - i))) v)
    (fun i hi v hv hc => ?_) (by simpa using h) h.h9) fun v hv => by simpa using hv
  have e : Spec.Rsa.FixedBaseComb.rows bits - i = Spec.Rsa.FixedBaseComb.rows bits - (i + 1) + 1 := by omega_arith
  rw [e] at hv hc
  refine WP.mono (step_ok hq hv (by omega_arith)) fun v' hv' => ⟨hv', ?_⟩
  rw [hv'.h9, hc, Offset.ofNat_sub_ofNat (by omega_arith), Nat.add_sub_cancel]

/-! ## The comb -/

/-- What the comb needs: the working space with p in array 0, the context
(its address in the header's word 4) and its entries, x's octets (at `a5`)
and the header's row count. -/
structure CombIn (s : State) (B C X : Addr) (Z w : Nat) (xb : List Byte) (P G bits : Nat) : Prop where
  scr : Scr s B Z
  w2 : 2 ≤ w
  w31 : w < 2 ^ 31
  hZ : slot w 24 ≤ Z
  a7 : s.gpr .a7 = off B (slot w 0)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))
  t0 : s.gpr .t0 = BitVec.ofNat 64 w
  s6 : s.gpr .s6 = B
  hX : word s.mem B 8 = X
  s11 : s.gpr .s11 = BitVec.ofNat 64 xb.length
  hC : word s.mem B 32 = C
  hRw : word s.mem B 56 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)
  ctx : CtxRd s B Z C w
  ents : ∀ a < 32, ent s.mem C w a = combM G P w (Spec.Rsa.FixedBaseComb.exponent bits a)
  r2 : wordsVal s.mem C (rowOff w 1) w = 2 ^ (64 * w) * 2 ^ (64 * w) % P
  hp : A s.mem B w 0 = P
  xrd : ∀ n < xb.length, InRegions (s.rd ++ s.wr) (off X n) 1
  xsep : ∀ n < xb.length, ∀ y, ofs B y < Z → off X n ≠ y
  xval : ∀ n (h : n < xb.length), s.mem (off X n) = xb[n]
  hL : 8 * xb.length < 2 ^ 31
  row : RowP P bits
  pos : 0 < bits

/-- The registers the comb writes. -/
def combRegs : List Reg := [.s10, .s8, .s7, .t2, .s0, .s1, .s2, .s3, .t1, .t3, .t4, .t5, .s9] ++ stepRegs

/-- `headBlock`: the context, x's address, the rows, and `t2 := 1`. -/
theorem head_ok {s : State} {B C X : Addr} {Z rows : Nat} (hs : Scr s B Z) (hZ : 64 ≤ Z) (h6 : s.gpr .s6 = B)
    (hX : word s.mem B 8 = X) (hC : word s.mem B 32 = C) (hRw : word s.mem B 56 = BitVec.ofNat 64 rows) :
    WP isa (.block headBlock) s fun u => (u.gpr .s10 = C ∧ u.gpr .s8 = X ∧
      u.gpr .s7 = BitVec.ofNat 64 rows ∧ u.gpr .t2 = BitVec.ofNat 64 1 ∧ u.mem = s.mem) ∧
      Keep [.s10, .s8, .s7, .t2] s u := by
  have h6' : s.gpr .s6 = off B 0 := by rw [h6]; simp [off]
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold headBlock hCtx hRows
  brun [h6', hs.ld (d := 32) (n := 8) (by omega_arith), hs.ld (d := 56) (n := 8) (by omega_arith),
    hs.ld (d := 8) (n := 8) (by omega_arith), hs.al8 (d := 8) (by omega_arith) (by decide),
    hs.al8 (d := 32) (by omega_arith) (by decide), hs.al8 (d := 56) (by omega_arith) (by decide),
    show (s.mem.readW (off B 32) 64) = C from hC, show s.mem.readW (off B 56) 64 = BitVec.ofNat 64 rows from hRw,
    show (s.mem.readW (off B 8) 64) = X from hX,
    Pub.pub_li1, BitVec.add_zero]

theorem low_odd {m : Mem} {B : Addr} {d w P : Nat} (hw : 1 ≤ w) (h : wordsVal m B d w = P) (hodd : P % 2 = 1) :
    (word m B d).toNat % 2 = 1 := by
  rw [fios_wordsVal_pred _ _ _ hw] at h
  omega_arith

theorem combRest_ok {s s₁ : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits : Nat}
    (h : CombIn s B C X Z w xb P G bits) (a10 : s₁.gpr .s10 = C) (a8 : s₁.gpr .s8 = X)
    (a7 : s₁.gpr .s7 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)) (a2 : s₁.gpr .t2 = BitVec.ofNat 64 1)
    (m1 : s₁.mem = s.mem) (k1 : Keep [.s10, .s8, .s7, .t2] s s₁) :
    WP isa combRest s₁ fun t =>
      (A t.mem B w 4 = Spec.Rsa.powMod G (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0) P ∧
        A t.mem B w 0 = P ∧ WinO B w s.mem t.mem) ∧ Keep combRegs s t := by
  have hZ := h.hZ
  have hnw : B.toNat + slot w 24 ≤ 2 ^ 64 := by have := h.scr.nowrap; omega_arith
  have hw := h.w2; have hw' := h.w31
  have hq := h.row
  have hP : 0 < P := by have := hq.one; omega_arith
  have cop := VG.Proof.Bignum.coprime_pow2 hq.odd (64 * w)
  have h256 : 256 ≤ Z := by
    have : slot w 24 = 256 + 24 * (8 * (w + 2)) := rfl
    omega_arith
  have h0 : slot w 0 + 8 ≤ Z := by
    have : slot w 24 = 256 + 24 * (8 * (w + 2)) := rfl
    have : slot w 0 = 256 := by simp [slot, hdrBytes]
    omega_arith
  unfold combRest
  simp only [seqs]
  -- `-p⁻¹ mod 2⁶⁴`.
  refine WP.seq (WP.mono (minv_ok (h.scr.congr k1.2.2) ((k1.gpr (by decide)).trans h.a7) (slot_al w 0)
    (by omega_arith) (by rw [m1]; exact low_odd (by omega_arith) h.hp hq.odd)) fun s₂ ⟨⟨inv2, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  have c2 : WCtx s₂ B Z w P := ⟨h.scr.congr k12.2.2, hw, hw', hZ, (k12.gpr (by decide)).trans h.a7,
    (k12.gpr (by decide)).trans h.s5, (k12.gpr (by decide)).trans h.t0, by rw [m2]; exact inv2,
    by rw [hm2]; exact h.hp⟩
  have hc2 : CtxRd s₂ B Z C w := h.ctx.congr k12.2.1 k12.2.2
  -- `R² mod p` into array 1.
  refine WP.seq (WP.mono (loadRow_ok (a := 1) (j := 1) c2 hc2 ((k2.gpr (by decide)).trans a10)
    ((k2.gpr (by decide)).trans a2) (by decide) (by decide)) fun s₃ ⟨⟨r3, o3⟩, k3⟩ => ?_)
  rw [hm2, h.r2] at r3
  have c3 := c2.of k3 (by decide) (arrO o3 (by decide) (by decide))
  -- 1 in array 7.
  have h8 := slot_lt (w := w) (show 8 < 24 by decide)
  refine WP.seq (WP.mono (Pub.oneP_ok c3.scr (by omega_arith) hw' (by omega_arith) c3.a7 c3.s5 c3.t0)
    fun s₄ ⟨⟨one4, o4⟩, k4⟩ => ?_)
  have c4 := c3.of k4 (by decide) (arrO o4 (by decide) (by decide))
  have r4 : A s₄.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P := by rw [Win.arr_out o4 (by decide) (by decide) hnw]; exact r3
  -- Montgomery one in array 6.
  refine WP.seq (WP.mono (c4.mont (o := 6) (a := 1) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [show A s₄.mem B w 7 = 1 from one4]; exact hq.one))
    fun s₅ ⟨⟨c5, lt5, eq5, fr5, o5⟩, k5⟩ => ?_)
  rw [r4, show A s₄.mem B w 7 = 1 from one4] at eq5
  have a5 : A s₅.mem B w 6 = combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb)
      (Spec.Rsa.FixedBaseComb.rows bits)) := by
    rw [Rsa.FixedBaseComb.high_top, combM, VG.Proof.Bignum.powMod_eq, Nat.pow_zero, Nat.mod_eq_of_lt hq.one,
      Nat.one_mul]
    rw [← Nat.mod_eq_of_lt lt5]
    exact VG.Proof.Bignum.mont_cancel cop (by rw [eq5, Nat.mul_one, Nat.mod_mod])
  have one5 : A s₅.mem B w 7 = 1 := by rw [fr5 7 (by decide) (by decide) (by decide) (by decide)]; exact one4
  -- `rows` rows left.
  have k15 := (((k12.trans k3).trans k4).trans k5)
  refine WP.seq (WP.mono (WP.keep [.s9] (Q := fun v => v.gpr .s9 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits) ∧
      v.mem = s₅.mem) (by brun [((((k2.trans k3).trans k4).trans k5).gpr (r := .s7) (by decide)).trans a7,
        BitVec.add_zero]) (by rfl) (by rfl)) fun s₆ ⟨⟨a9, m6⟩, k6⟩ => ?_)
  have k16 := k15.trans k6
  have hpos := Rsa.FixedBaseComb.rows_pos h.pos
  have o16 : WinO B w s.mem s₆.mem := by
    rw [m6, ← hm2]; exact ((Outside.trans (arrO o3 (by decide) (by decide)) (arrO o4 (by decide) (by decide)))).trans o5
  have c6 : CS s₆ B C X Z w xb P G bits (Spec.Rsa.FixedBaseComb.rows bits)
      (combM G P w (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) (Spec.Rsa.FixedBaseComb.rows bits))) s₆ := by
    have hctx : Outside C (8 * ctxWords w) (2 ^ 64) s.mem s₆.mem := win_ctx o16 hZ h.ctx.sep
    have g : ∀ r ∈ ([.s10, .s8, .s7] : List Reg), s₆.gpr r = s₁.gpr r := fun r hr =>
      ((((k2.trans k3).trans k4).trans k5).trans k6).gpr (by revert r hr; decide)
    refine ⟨c5.regs k6 (by decide) m6, (g .s10 (by decide)).trans a10, h.ctx.congr k16.2.1 k16.2.2,
      fun a ha => by rw [ent_keep hctx h.ctx.hn ha]; exact h.ents a ha, a9,
      ⟨(k16.gpr (by decide)).trans h.s11, (g .s7 (by decide)).trans a7, (g .s8 (by decide)).trans a8,
        fun n hn => by rw [k16.2.1, k16.2.2]; exact h.xrd n hn,
        fun n hn => by rw [win_byte o16 hZ (h.xsep n hn)]; exact h.xval n hn, h.hL⟩,
      h.xsep, by rw [m6]; exact a5, by rw [m6]; exact one5, Outside.refl _ _ _ _, Keep.refl _ _⟩
  -- The rows.
  refine WP.seq (WP.mono (rows_ok hq c6 hpos) fun v hv => ?_)
  -- Out of Montgomery form.
  refine WP.mono (hv.win.mont (o := 4) (a := 6) (b := 7) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [hv.one]; exact hq.one)) fun t ⟨⟨ct, lt7, eq7, fr7, o7⟩, k7⟩ =>
      ⟨⟨?_, ?_, o16.trans (hv.out.trans o7)⟩, ?_⟩
  · rw [hv.acc, hv.one, Nat.mul_one, Nat.mod_mod] at eq7
    rw [← Nat.mod_eq_of_lt lt7, ← Nat.mod_eq_of_lt (show Spec.Rsa.powMod G _ P < P from by
      rw [VG.Proof.Bignum.powMod_eq]; exact Nat.mod_lt _ hP)]
    exact VG.Proof.Bignum.mont_cancel cop (by rw [eq7, VG.Proof.Bignum.powMod_eq, Nat.mod_mul_mod])
  · exact ct.n
  · exact ((k16.trans hv.keep).trans k7).mono (by decide)

theorem comb_ok {s : State} {B C X : Addr} {Z w : Nat} {xb : List Byte} {P G bits : Nat}
    (h : CombIn s B C X Z w xb P G bits) :
    WP isa comb s fun t =>
      (A t.mem B w 4 = Spec.Rsa.powMod G (Rsa.FixedBaseComb.high bits (Spec.Rsa.os2ip xb) 0) P ∧
        A t.mem B w 0 = P ∧ WinO B w s.mem t.mem) ∧ Keep combRegs s t :=
  WP.seq (WP.mono (head_ok h.scr (by have := h.hZ; have : slot w 24 = 256 + 24 * (8 * (w + 2)) := rfl; omega_arith)
    h.s6 h.hX h.hC h.hRw) fun _ ⟨⟨a10, a8, a7, a2, m1⟩, k1⟩ => combRest_ok h a10 a8 a7 a2 m1 k1)

end VG.Proof.Ffdh.RISCV64.Cached
