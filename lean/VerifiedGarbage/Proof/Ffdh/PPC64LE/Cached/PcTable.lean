module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.Comb
public import VerifiedGarbage.Proof.Bignum.PPC64LE.WinBase
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Bignum.Math
-- separate module: the precompute's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # FFDH's context on PPC64LE: the comb's table

`table_ok`: from p in array 0, `R² mod p` in array 1 and g's octets, the 32
entries of the comb, `g^(exponent bits a) R mod p`, into the context's rows
2 to 33: entries 0 and 1 (`initial`), then for each tooth `d = 2^k` its
entry, the `2^rows`-th power of the last tooth's (`squares`), and the
products of the entries below it with it (`product`). -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Precompute
open VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (Env envRegs arr)
open VG.Proof.Bignum (slot slot_sep)

/-- A change outside the context's first `n` bytes, apart from the
working space, keeps the working space. -/
theorem out_far {B C : Addr} {Z o n : Nat} {m m' : Mem} (h : Outside C o n m m')
    (hsep : ∀ x, ofs B x < Z → o + n ≤ ofs C x) : Outside B Z (2 ^ 64) m m' := fun y hy => h y (Or.inr (by
  rcases hy with hy | hy
  · exact hsep y hy
  · have := (y - B).isLt; simp only [ofs] at hy; omega))

theorem slot_mono {w a b : Nat} (h : a ≤ b) : slot w a ≤ slot w b := by
  simp only [slot]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem slot_lt' {w a b : Nat} (h : a < b) : slot w a + 8 * (w + 2) ≤ slot w b := by
  have := Nat.mul_le_mul_right (8 * (w + 2)) (show a + 1 ≤ b from h)
  simp only [slot]; rw [Nat.succ_mul] at this; omega

/-- What the table's stages keep: the working space, the context's address,
writable and apart, the inverse and p. -/
structure TS (B C : Addr) (Z w P : Nat) (M : Mem) (s : State) : Prop where
  env : Env s B Z w
  h30 : s.gpr .r30 = C
  hc : Scr s C (8 * ctxWords w)
  sepCB : ∀ x, ofs C x < 8 * ctxWords w → Z ≤ ofs B x
  sepBC : ∀ x, ofs B x < Z → 8 * ctxWords w ≤ ofs C x
  h12 : (s.gpr .r12).toNat < 2 ^ 32
  hinv : (w32 s.mem B (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  hp : arr s.mem B w 0 = P
  odd : P % 2 = 1
  one : 1 < P
  low : ∀ x, ofs B x < slot w 1 → s.mem x = M x

/-- `TS` across a change of registers apart from its own and of memory
keeping array 0. -/
theorem TS.keep {B C : Addr} {Z w P : Nat} {M : Mem} {s t : State} {rs : List Reg} (h : TS B C Z w P M s) (k : Keep rs s t)
    (hr : ∀ r ∈ ([.r10, .r11, .r12, .r29, .r30, .r31] : List Reg), r ∉ rs)
    (hm : ∀ x, ofs B x < slot w 1 → t.mem x = s.mem x) : TS B C Z w P M t := by
  have hZ := h.env.hZ
  have hnw := h.env.hs.nowrap
  have hm0 : Outside B (slot w 1) (2 ^ 64) s.mem t.mem := fun y hy => hm y (by
    rcases hy with hy | hy
    · exact hy
    · have := (y - B).isLt; simp only [ofs] at hy; omega)
  refine ⟨h.env.keep k (fun r hr' => by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl <;> exact hr _ (by decide)),
    (k.gpr _ (hr _ (by decide))).trans h.h30, h.hc.congr k.wr, h.sepCB, h.sepBC,
    by rw [k.gpr _ (hr _ (by decide))]; exact h.h12, ?_, ?_, h.odd, h.one, fun x hx => (hm x hx).trans (h.low x hx)⟩
  · rw [k.gpr _ (hr _ (by decide)), hm0.w32 (Or.inl (by simp only [slot, hdrBytes]; omega)) (by simp only [slot, hdrBytes] at hZ ⊢; omega)]
    exact h.hinv
  · rw [arr, hm0.val32 (Or.inl (by simp only [slot, hdrBytes]; omega)) (by simp only [slot, hdrBytes] at hZ ⊢; omega)]; exact h.hp

theorem TS.fit {B C : Addr} {Z w P : Nat} {M : Mem} {s : State} (h : TS B C Z w P M s) : B.toNat + Z ≤ 2 ^ 64 :=
  h.env.hs.nowrap

/-- The Montgomery product `o := a b R⁻¹` in `TS`. -/
theorem TS.mont {B C : Addr} {Z w P : Nat} {M : Mem} {s : State} (h : TS B C Z w P M s) {o a b : Nat} (ho : o < 8)
    (ha : a < 8) (hb : b < 8) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (hb2 : b ≠ 2) (ho0 : o ≠ 0)
    (hB : arr s.mem B w b < P) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (arr t.mem B w o < P ∧ arr t.mem B w o * 2 ^ (64 * w) % P = arr s.mem B w a * arr s.mem B w b % P ∧
        (∀ c < 8, c ≠ 2 → c ≠ 3 → c ≠ o → arr t.mem B w c = arr s.mem B w c) ∧
        Outside C (8 * ctxWords w) (2 ^ 64) s.mem t.mem ∧ TS B C Z w P M t) ∧
      Keep Pub.montRegs s t := by
  have := h.env.hw; have := h.env.hw'; have hZ := h.env.hZ
  have hnw := h.fit
  refine WP.mono (Pub.montOp_ok h.env.hs ho ha hb ho2 ho3 ha2 hb2 (by omega) (by omega)
    (Nat.le_trans (by simp only [slot, hdrBytes]; omega) hZ) h.env.h10 h.env.h29 h.env.h11 h.h12 h.hinv
    (by rw [← arr, ← arr, h.hp]; exact hB)) fun t ⟨⟨lt, eq, out⟩, k⟩ => ⟨⟨?_, ?_, fun c hc h2 h3 hco => ?_,
      outs_ctx out (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact Env.arr h.env (by omega)) h.sepCB,
      h.keep k (by decide) fun x hx => out x fun r hr => Or.inl (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact Nat.lt_of_lt_of_le hx (slot_mono (by omega)))⟩, k⟩
  · rw [arr, ← h.hp]; exact lt
  · rw [arr, ← h.hp]; exact eq
  · rw [arr, arr, out.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact slot_sep (w := w) (j := c) (k := 2) h2 |>.imp (fun e => by omega) (fun e => by omega)
      · exact slot_sep (w := w) (j := c) (k := 3) h3 |>.imp (fun e => by omega) (fun e => by omega)
      · exact slot_sep (w := w) (j := c) (k := o) hco |>.imp (fun e => by omega) (fun e => by omega))
      (by have := Env.arr h.env (j := c) (by omega); omega)]

/-- Row `j` of the context, as a number. -/
abbrev rowv (m : Mem) (C : Addr) (w j : Nat) : Nat := val32 m C (rowOff w j) (2 * w)

/-- `storeRow a` in `TS`: row `j := ` array `a`. -/
theorem TS.store {B C : Addr} {Z w P : Nat} {M : Mem} {s : State} (h : TS B C Z w P M s) {j a : Nat} (ha : a < 8)
    (h3 : s.gpr .r3 = BitVec.ofNat 64 j) (hj : j < 34) :
    WP isa (storeRow a) s fun t =>
      (rowv t.mem C w j = arr s.mem B w a ∧ Outside C (rowOff w j) (8 * w) s.mem t.mem ∧
        Outside B Z (2 ^ 64) s.mem t.mem ∧ TS B C Z w P M t) ∧ Keep rowRegs s t := by
  have hrow : rowOff w j + 8 * w ≤ 8 * ctxWords w := by
    have h1 := Nat.mul_le_mul_left w (show j + 1 ≤ 34 by omega)
    rw [Nat.mul_succ, Nat.mul_comm w 34] at h1; unfold rowOff ctxWords; omega
  refine WP.mono (storeRow_ok h.env h.hc h3 h.h30 (by omega) (by omega) hrow h.sepBC)
    fun t ⟨⟨hw, out⟩, k⟩ => ?_
  have far := out_far (Z := Z) out fun x hx => Nat.le_trans hrow (h.sepBC x hx)
  have hZ := h.env.hZ
  refine ⟨⟨?_, out, far, h.keep k (by decide) fun x hx => far x (Or.inl (by
    simp only [slot, hdrBytes] at hx hZ ⊢; omega))⟩, k⟩
  exact val32_of_words hw

/-- `loadRow a` in `TS`: array `a := ` row `j`. -/
theorem TS.load {B C : Addr} {Z w P : Nat} {M : Mem} {s : State} (h : TS B C Z w P M s) {j a : Nat} (ha : a < 8) (ha0 : a ≠ 0)
    (h3 : s.gpr .r3 = BitVec.ofNat 64 j) (hj : j < 34) :
    WP isa (loadRow a) s fun t =>
      (arr t.mem B w a = rowv s.mem C w j ∧ (∀ c < 8, c ≠ a → arr t.mem B w c = arr s.mem B w c) ∧
        Outside C (8 * ctxWords w) (2 ^ 64) s.mem t.mem ∧ TS B C Z w P M t) ∧ Keep rowRegs s t := by
  have hrow : rowOff w j + 8 * w ≤ 8 * ctxWords w := by
    have h1 := Nat.mul_le_mul_left w (show j + 1 ≤ 34 by omega)
    rw [Nat.mul_succ, Nat.mul_comm w 34] at h1; unfold rowOff ctxWords; omega
  have hZ := h.env.hZ
  have hCn : C.toNat + 8 * ctxWords w ≤ 2 ^ 64 := h.hc.nowrap
  refine WP.mono (loadRow_ok h.env h.h30 h3 (by omega) (by omega) hrow hCn
    (fun i hi => h.hc.ld (d := rowOff w j + 8 * i) (n := 8) (by omega)) h.sepCB) fun t ⟨⟨hw, out⟩, k⟩ => ?_
  have far : Outside C (8 * ctxWords w) (2 ^ 64) s.mem t.mem := fun y hy => out y (Or.inr (by
    rcases hy with hy | hy
    · have := h.sepCB y hy; have := Env.arr h.env (j := a) (by omega); omega
    · have := (y - C).isLt; simp only [ofs] at hy; omega))
  refine ⟨⟨val32_of_words hw, fun c hc hca => ?_, far, h.keep k (by decide) fun x hx => out x (Or.inl
    (Nat.lt_of_lt_of_le hx (slot_mono (by omega))))⟩, k⟩
  rw [arr, arr, out.val32 (slot_sep (w := w) hca |>.imp (fun e => by omega) (fun e => by omega))
    (by have := Env.arr h.env (j := c) (by omega); have := h.fit; omega)]

/-! ## Montgomery residues -/

/-- `x = y` from `x R ≡ y R`, both below `P`, `P` odd. -/
theorem mont_eq {x y P w : Nat} (hodd : P % 2 = 1) (hx : x < P) (hy : y < P)
    (h : x * 2 ^ (64 * w) % P = y * 2 ^ (64 * w) % P) : x = y := by
  have cop := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have := VG.Proof.Bignum.mont_cancel cop h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

theorem combM_lt' {G P w : Nat} (hP : 0 < P) (E : Nat) : combM G P w E < P := Nat.mod_lt _ hP

/-- The comb's entries: `g^(exponent bits a) R mod p`. -/
abbrev entV (G P w bits a : Nat) : Nat := combM G P w (Spec.Rsa.FixedBaseComb.exponent bits a)

theorem combM_square {G P w E a c : Nat} (hodd : P % 2 = 1) (hc : c < P) (ha : a = combM G P w E)
    (h : c * 2 ^ (64 * w) % P = a * a % P) : c = combM G P w (E * 2) := by
  rw [Nat.mul_comm E 2]
  exact VG.Proof.Rsa.FixedBaseComb.mont_square_encoded (VG.Proof.Bignum.coprime_pow2 hodd (64 * w)) hc ha h

theorem combM_mul {G P w E F a b c : Nat} (hodd : P % 2 = 1) (hc : c < P) (ha : a = combM G P w E)
    (hb : b = combM G P w F) (h : c * 2 ^ (64 * w) % P = a * b % P) : c = combM G P w (E + F) :=
  VG.Proof.Rsa.FixedBaseComb.mont_product_encoded (VG.Proof.Bignum.coprime_pow2 hodd (64 * w)) hc ha hb h

/-! ## The squares -/

/-- The registers the squares write. -/
def sqRegs : List Reg := .r25 :: Pub.montRegs

/-- `squares`: array 6 `:=` its `2^rows`-th power, `rows` in `r24`. -/
theorem squares_ok {B C : Addr} {Z w P G E rows : Nat} {M : Mem} {s : State} (h : TS B C Z w P M s)
    (hx : arr s.mem B w 6 = combM G P w E) (h24 : s.gpr .r24 = BitVec.ofNat 64 rows) (hr : 1 ≤ rows)
    (hr' : rows < 2 ^ 32) :
    WP isa squares s fun t =>
      (arr t.mem B w 6 = combM G P w (E * 2 ^ rows) ∧
        (∀ c < 8, c ≠ 2 → c ≠ 3 → c ≠ 6 → arr t.mem B w c = arr s.mem B w c) ∧
        Outside C (8 * ctxWords w) (2 ^ 64) s.mem t.mem ∧ TS B C Z w P M t) ∧ Keep sqRegs s t := by
  have hP : 0 < P := by have := h.one; omega
  unfold squares
  refine WP.seq (WP.mono (WP.keep [.r25] (Q := fun t => t.gpr .r25 = BitVec.ofNat 64 rows ∧ t.mem = s.mem)
    (by prun [h24, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a25, m1⟩, k1⟩ => ?_)
  have h1 := h.keep k1 (by decide) fun x _ => by rw [m1]
  refine WP.mono (wp_countdown (body := .seq (PublicChecked.montOp 6 6 6) (.block [.subi .r25 .r25 1]))
    (cnt := .r25) (N := rows) (by omega) (by omega)
    (fun i t => (arr t.mem B w 6 = combM G P w (E * 2 ^ i) ∧
        (∀ c < 8, c ≠ 2 → c ≠ 3 → c ≠ 6 → arr t.mem B w c = arr s.mem B w c) ∧
        Outside C (8 * ctxWords w) (2 ^ 64) s.mem t.mem ∧ TS B C Z w P M t) ∧ Keep sqRegs s t)
    (fun i _ t ⟨⟨t6, tc, tctx, ht⟩, kt⟩ _ => ?_)
    ⟨⟨by rw [arr, m1]; rw [← arr, hx, Nat.pow_zero, Nat.mul_one], fun c _ _ _ _ => by rw [arr, arr, m1],
      fun y _ => by rw [m1], h1⟩, k1.mono (by decide)⟩ a25) fun t h => h
  refine WP.seq (WP.mono (ht.mont (o := 6) (a := 6) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [t6]; exact combM_lt' hP _))
    fun u ⟨⟨ul, ue, uc, uctx, hu⟩, ku⟩ => ?_)
  refine WP.mono (WP.keep [.r25] (Q := fun v => v.gpr .r25 = u.gpr .r25 - BitVec.ofNat 64 1 ∧ v.mem = u.mem)
    (by prun) (by decide)) fun v ⟨⟨a25', mv⟩, kv⟩ => ⟨⟨⟨?_, fun c hc h2 h3 h6 => ?_, fun y hy => ?_,
      hu.keep kv (by decide) fun x _ => by rw [mv]⟩, (kt.trans (ku.trans kv)).mono (by decide)⟩,
      by rw [a25', ku.gpr .r25 (by decide)]⟩
  · rw [arr, mv, ← arr, combM_square h.odd ul t6 ue, Nat.pow_succ, Nat.mul_assoc]
  · rw [arr, mv, ← arr, uc c hc h2 h3 h6, tc c hc h2 h3 h6]
  · rw [mv, uctx y hy, tctx y hy]

/-! ## The entries -/

/-- Entries `a < n` of the context are the comb's. -/
def Ents (m : Mem) (C : Addr) (G P w bits n : Nat) : Prop := ∀ a < n, ent m C w a = entV G P w bits a

/-- The context below the table (its metadata, p and `R² mod p`) as in `m₀`. -/
def CtxKeep (C : Addr) (w : Nat) (m₀ m : Mem) : Prop := ∀ y, ofs C y < rowOff w 2 → m y = m₀ y

theorem CtxKeep.trans {C : Addr} {w : Nat} {m₀ m₁ m₂ : Mem} (h₁ : CtxKeep C w m₀ m₁) (h₂ : CtxKeep C w m₁ m₂) :
    CtxKeep C w m₀ m₂ := fun y hy => (h₂ y hy).trans (h₁ y hy)

theorem CtxKeep.of_far {C : Addr} {w : Nat} {m₀ m₁ m₂ : Mem} (h₁ : CtxKeep C w m₀ m₁)
    (h₂ : Outside C (8 * ctxWords w) (2 ^ 64) m₁ m₂) : CtxKeep C w m₀ m₂ :=
  fun y hy => (h₂ y (Or.inl (by unfold rowOff ctxWords at *; omega))).trans (h₁ y hy)

theorem CtxKeep.of_row {C : Addr} {w j : Nat} {m₀ m₁ m₂ : Mem} (h₁ : CtxKeep C w m₀ m₁) (hj : 2 ≤ j)
    (h₂ : Outside C (rowOff w j) (8 * w) m₁ m₂) : CtxKeep C w m₀ m₂ :=
  fun y hy => (h₂ y (Or.inl (Nat.lt_of_lt_of_le hy (by
    unfold rowOff; have := Nat.mul_le_mul_left w hj; omega)))).trans (h₁ y hy)

theorem rowOff_le {w a b : Nat} (h : a ≤ b) : rowOff w a ≤ rowOff w b := by
  unfold rowOff; have := Nat.mul_le_mul_left w h; omega

theorem rowOff_succ (w a : Nat) : rowOff w a + 8 * w = rowOff w (a + 1) := by
  unfold rowOff; rw [Nat.mul_succ]; omega

theorem Ents.of_far {m m' : Mem} {C : Addr} {G P w bits n : Nat} (h : Ents m C G P w bits n)
    (hn : n ≤ 32) (out : Outside C (8 * ctxWords w) (2 ^ 64) m m') (hCn : C.toNat + 8 * ctxWords w ≤ 2 ^ 64) :
    Ents m' C G P w bits n := fun a ha => by
  have := row_fits (w := w) (show a < 32 by omega)
  rw [ent, out.val32 (Or.inl (by omega)) (by omega)]; exact h a ha

theorem Ents.store {m m' : Mem} {C : Addr} {G P w bits n : Nat} (h : Ents m C G P w bits n) (hn : n < 32)
    (out : Outside C (rowOff w (n + 2)) (8 * w) m m') (hv : rowv m' C w (n + 2) = entV G P w bits n)
    (hCn : C.toNat + 8 * ctxWords w ≤ 2 ^ 64) : Ents m' C G P w bits (n + 1) := fun a ha => by
  rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | rfl
  · have := row_fits (w := w) (show a < 32 by omega)
    have h1 := rowOff_le (w := w) (show a + 2 + 1 ≤ n + 2 by omega)
    have h2 := rowOff_succ w (a + 2)
    rw [ent, out.val32 (Or.inl (by omega)) (by omega)]; exact h a ha
  · exact hv

/-! ## The products -/

/-- The registers the table writes. -/
def tabRegs : List Reg := [.r3, .r25, .r26] ++ rowRegs ++ Pub.montRegs ++ sqRegs ++ Win.copyRegs ++
  [.r0, .r4, .r6, .r10, .r12, .r14, .r15, .r16, .r17]

/-- Within the table: `TS`, the rows in `r24`, the working space in `r23`. -/
structure TT (B C : Addr) (Z w P rows : Nat) (s₀ t : State) : Prop where
  ts : TS B C Z w P s₀.mem t
  h24 : t.gpr .r24 = BitVec.ofNat 64 rows
  h23 : t.gpr .r23 = B
  keep : CtxKeep C w s₀.mem t.mem
  kr : Keep tabRegs s₀ t

theorem TT.next {B C : Addr} {Z w P rows : Nat} {s₀ t u : State} {rs : List Reg} (h : TT B C Z w P rows s₀ t)
    (hts : TS B C Z w P s₀.mem u) (k : Keep rs t u) (hr : ∀ r ∈ rs, r ∈ tabRegs)
    (hc : CtxKeep C w t.mem u.mem) : TT B C Z w P rows s₀ u :=
  ⟨hts, (k.gpr .r24 fun e => by have := hr _ e; revert this; decide).trans h.h24,
    (k.gpr .r23 fun e => by have := hr _ e; revert this; decide).trans h.h23, h.keep.trans hc,
    h.kr.trans' (k.mono fun r h' => hr r h')⟩

theorem CtxKeep.of_far' {C : Addr} {w : Nat} {m m' : Mem} (h : Outside C (8 * ctxWords w) (2 ^ 64) m m') :
    CtxKeep C w m m' := CtxKeep.of_far (fun _ _ => rfl) h

theorem CtxKeep.refl (C : Addr) (w : Nat) (m : Mem) : CtxKeep C w m m := fun _ _ => rfl

/-- One product: entry `d + j :=` entry `j` times entry `d` (array 6). -/
theorem product_ok {B C : Addr} {Z w P G bits k j : Nat} {s₀ t : State}
    (h : TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ t) (hk : k < 5) (hj1 : 1 ≤ j) (hj : j < 2 ^ k)
    (h25 : t.gpr .r25 = BitVec.ofNat 64 j) (h26 : t.gpr .r26 = BitVec.ofNat 64 (2 ^ k))
    (h6 : arr t.mem B w 6 = entV G P w bits (2 ^ k)) (he : Ents t.mem C G P w bits (2 ^ k + j)) :
    WP isa product t fun u => TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ u ∧
      u.gpr .r25 = BitVec.ofNat 64 (j + 1) ∧ u.gpr .r26 = BitVec.ofNat 64 (2 ^ k) ∧
      arr u.mem B w 6 = entV G P w bits (2 ^ k) ∧ Ents u.mem C G P w bits (2 ^ k + j + 1) ∧
      isa.eval (.nonzero .d .r3) u = some (decide (j + 1 ≠ 2 ^ k)) := by
  have hP : 0 < P := by have := h.ts.one; omega
  have hk32 : 2 ^ k ≤ 16 := by
    have : k ≤ 4 := by omega
    calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) this
      _ = 16 := rfl
  have hCn := h.ts.hc.nowrap
  unfold product
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 (j + 2) ∧ u.mem = t.mem)
    (by prun [h25, BitVec.ofNat_add]) (by decide)) fun t₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have h1 := h.next (h.ts.keep k1 (by decide) fun x _ => by rw [m1]) k1 (by decide) (fun y _ => by rw [m1])
  refine WP.seq (WP.mono (h1.ts.load (j := j + 2) (a := 5) (by decide) (by decide) a3 (by omega))
    fun t₂ ⟨⟨a5, ac, actx, ts2⟩, k2⟩ => ?_)
  have h2 := h1.next ts2 k2 (by decide) (CtxKeep.of_far' actx)
  have e5 : arr t₂.mem B w 5 = entV G P w bits j := by
    rw [a5, show rowv t₁.mem C w (j + 2) = ent t.mem C w j by rw [m1]]; exact he j (by omega)
  have e6 : arr t₂.mem B w 6 = entV G P w bits (2 ^ k) := by
    rw [ac 6 (by decide) (by decide), arr, m1, ← arr]; exact h6
  refine WP.seq (WP.mono (ts2.mont (o := 5) (a := 5) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [e6]; exact combM_lt' hP _))
    fun t₃ ⟨⟨l3, q3, c3, ctx3, ts3⟩, k3⟩ => ?_)
  have h3 := h2.next ts3 k3 (by decide) (CtxKeep.of_far' ctx3)
  have v3 : arr t₃.mem B w 5 = entV G P w bits (2 ^ k + j) := by
    rw [combM_mul h.ts.odd l3 e5 e6 q3]
    show combM G P w _ = combM G P w _
    rw [VG.Proof.Rsa.FixedBaseComb.exponent_add_tooth bits k j hk hj,
      VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits k hk]
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 (2 ^ k + j + 2) ∧ u.mem = t₃.mem)
    (by
      have g25 : t₃.gpr .r25 = BitVec.ofNat 64 j := by
        rw [k3.gpr .r25 (by decide), k2.gpr .r25 (by decide), k1.gpr .r25 (by decide), h25]
      have g26 : t₃.gpr .r26 = BitVec.ofNat 64 (2 ^ k) := by
        rw [k3.gpr .r26 (by decide), k2.gpr .r26 (by decide), k1.gpr .r26 (by decide), h26]
      prun [g25, g26, ← BitVec.ofNat_add]
      congr 1; omega) (by decide)) fun t₄ ⟨⟨a3', m4⟩, k4⟩ => ?_)
  have h4 := h3.next (ts3.keep k4 (by decide) fun x _ => by rw [m4]) k4 (by decide) (fun y _ => by rw [m4])
  refine WP.seq (WP.mono (h4.ts.store (j := 2 ^ k + j + 2) (a := 5) (by decide) a3' (by omega))
    fun t₅ ⟨⟨r5, o5, b5, ts5⟩, k5⟩ => ?_)
  have h5 := h4.next ts5 k5 (by decide) (CtxKeep.of_row (CtxKeep.refl _ _ _) (by omega) o5)
  have g25 : t₅.gpr .r25 = BitVec.ofNat 64 j := by
    rw [k5.gpr .r25 (by decide), k4.gpr .r25 (by decide), k3.gpr .r25 (by decide), k2.gpr .r25 (by decide),
      k1.gpr .r25 (by decide), h25]
  have g26 : t₅.gpr .r26 = BitVec.ofNat 64 (2 ^ k) := by
    rw [k5.gpr .r26 (by decide), k4.gpr .r26 (by decide), k3.gpr .r26 (by decide), k2.gpr .r26 (by decide),
      k1.gpr .r26 (by decide), h26]
  refine WP.mono (WP.keep [.r3, .r25] (Q := fun u => u.gpr .r25 = BitVec.ofNat 64 (j + 1) ∧
      u.gpr .r3 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 (2 ^ k) ∧ u.mem = t₅.mem)
    (by prun [g25, g26, BitVec.ofNat_add]) (by decide)) fun u ⟨⟨u25, u3, mu⟩, ku⟩ => ?_
  have hZ := h.ts.env.hZ
  have e6' : arr t₅.mem B w 6 = entV G P w bits (2 ^ k) := by
    rw [arr, b5.val32 (Or.inl (by
      have := Env.arr h.ts.env (j := 6) (by decide); omega)) (by
      have := Env.arr h.ts.env (j := 6) (by decide); have := h.ts.fit; omega), ← arr]
    rw [arr, m4, ← arr, c3 6 (by decide) (by decide) (by decide) (by decide)]; exact e6
  have ctx4 : Outside C (8 * ctxWords w) (2 ^ 64) t.mem t₄.mem := fun y hy => by
    rw [m4, ctx3 y hy, actx y hy, m1]
  have e5' := Ents.store (n := 2 ^ k + j) (Ents.of_far he (by omega) ctx4 hCn) (by omega) o5
    (by rw [r5, arr, m4, ← arr]; exact v3) hCn
  refine ⟨h5.next (ts5.keep ku (by decide) fun x _ => by rw [mu]) ku (by decide) (fun y _ => by rw [mu]), u25,
    by rw [ku.gpr .r26 (by decide), g26], by rw [arr, mu, ← arr]; exact e6', fun a ha => by
      rw [ent, mu]; exact e5' a ha,
    (VG.Proof.Bignum.PPC64LE.eval_nonzero u .r3).trans (by rw [u3, ofNat_sub_bne (by omega) (by omega)])⟩

theorem two_pow_le16 {k : Nat} (hk : k < 5) : 2 ^ k ≤ 16 := by
  calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 16 := rfl

/-- The products of tooth `d = 2^k`: entries `d + 1` to `2 d - 1`. -/
theorem products_ok {B C : Addr} {Z w P G bits k : Nat} {s₀ t : State}
    (h : TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ t) (hk : k < 5) (hk1 : 1 ≤ k)
    (h25 : t.gpr .r25 = BitVec.ofNat 64 1) (h26 : t.gpr .r26 = BitVec.ofNat 64 (2 ^ k))
    (h6 : arr t.mem B w 6 = entV G P w bits (2 ^ k)) (he : Ents t.mem C G P w bits (2 ^ k + 1)) :
    WP isa (.loop product (.nonzero .d .r3)) t fun u => TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ u ∧
      u.gpr .r26 = BitVec.ofNat 64 (2 ^ k) ∧ arr u.mem B w 6 = entV G P w bits (2 ^ k) ∧
      Ents u.mem C G P w bits (2 ^ (k + 1)) := by
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk1
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ j, n = 2 ^ k - j ∧ 1 ≤ j ∧ j < 2 ^ k ∧
      TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ u ∧ u.gpr .r25 = BitVec.ofNat 64 j ∧
      u.gpr .r26 = BitVec.ofNat 64 (2 ^ k) ∧ arr u.mem B w 6 = entV G P w bits (2 ^ k) ∧
      Ents u.mem C G P w bits (2 ^ k + j))
    (fun n u ⟨j, hn, hj1, hj, hu, u25, u26, u6, ue⟩ => WP.mono (product_ok hu hk hj1 hj u25 u26 u6 ue)
      fun v ⟨hv, v25, v26, v6, ve, vc⟩ => ?_) _ t ⟨1, rfl, Nat.le_refl _, by omega, h, h25, h26, h6, he⟩
  by_cases hjk : j + 1 = 2 ^ k
  · refine Or.inl ⟨by rw [vc]; simp [hjk], hv, v26, v6, ?_⟩
    rw [Nat.pow_succ, Nat.mul_two]
    rw [show 2 ^ k + j + 1 = 2 ^ k + 2 ^ k by omega] at ve
    exact ve
  · exact Or.inr ⟨by rw [vc]; simp [hjk], _, by omega, j + 1, rfl, by omega, by omega, hv, v25, v26, v6, ve⟩

/-- Tooth `d = 2^k`: its entry, from the last tooth's, and its products. -/
theorem column_ok {B C : Addr} {Z w P G bits k : Nat} {s₀ t : State}
    (h : TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ t) (hk : k < 5) (hk1 : 1 ≤ k)
    (hr : 1 ≤ Spec.Rsa.FixedBaseComb.rows bits) (hr' : Spec.Rsa.FixedBaseComb.rows bits < 2 ^ 32)
    (h26 : t.gpr .r26 = BitVec.ofNat 64 (2 ^ k))
    (h6 : arr t.mem B w 6 = combM G P w (2 ^ ((k - 1) * Spec.Rsa.FixedBaseComb.rows bits)))
    (he : Ents t.mem C G P w bits (2 ^ k)) :
    WP isa column t fun u => TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ u ∧
      u.gpr .r26 = BitVec.ofNat 64 (2 ^ (k + 1)) ∧
      arr u.mem B w 6 = combM G P w (2 ^ (k * Spec.Rsa.FixedBaseComb.rows bits)) ∧
      Ents u.mem C G P w bits (2 ^ (k + 1)) ∧
      isa.eval (.nonzero .d .r3) u = some (decide (2 ^ (k + 1) ≠ 32)) := by
  have hk16 := two_pow_le16 hk
  have hCn := h.ts.hc.nowrap
  have hP : 0 < P := by have := h.ts.one; omega
  have et : entV G P w bits (2 ^ k) = combM G P w (2 ^ (k * Spec.Rsa.FixedBaseComb.rows bits)) := by
    show combM G P w _ = _; rw [VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits k hk]
  unfold column
  simp only [seqs]
  refine WP.seq (WP.mono (squares_ok h.ts h6 h.h24 hr hr') fun t₁ ⟨⟨a6, ac, actx, ts1⟩, k1⟩ => ?_)
  have h1 := h.next ts1 k1 (by decide) (CtxKeep.of_far' actx)
  have e6 : arr t₁.mem B w 6 = entV G P w bits (2 ^ k) := by
    rw [a6, et, ← Nat.pow_add]; congr 2
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.succ_mul]
  have g26 : t₁.gpr .r26 = BitVec.ofNat 64 (2 ^ k) := (k1.gpr .r26 (by decide)).trans h26
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 (2 ^ k + 2) ∧ u.mem = t₁.mem)
    (by prun [g26, BitVec.ofNat_add]) (by decide)) fun t₂ ⟨⟨a3, m2⟩, k2⟩ => ?_)
  have h2 := h1.next (ts1.keep k2 (by decide) fun x _ => by rw [m2]) k2 (by decide) (fun y _ => by rw [m2])
  refine WP.seq (WP.mono (h2.ts.store (j := 2 ^ k + 2) (a := 6) (by decide) a3 (by omega))
    fun t₃ ⟨⟨r3, o3, b3, ts3⟩, k3⟩ => ?_)
  have h3 := h2.next ts3 k3 (by decide) (CtxKeep.of_row (j := 2 ^ k + 2) (CtxKeep.refl _ _ _) (Nat.le_add_left 2 _) o3)
  have hZ := h.ts.env.hZ
  have e6' : arr t₃.mem B w 6 = entV G P w bits (2 ^ k) := by
    rw [arr, b3.val32 (Or.inl (by have := Env.arr h.ts.env (j := 6) (by decide); omega)) (by
      have := Env.arr h.ts.env (j := 6) (by decide); have := h.ts.fit; omega), ← arr, arr, m2, ← arr]
    exact e6
  have ctx2 : Outside C (8 * ctxWords w) (2 ^ 64) t.mem t₂.mem := fun y hy => by rw [m2, actx y hy]
  have e3 := Ents.store (n := 2 ^ k) (Ents.of_far he (by omega) ctx2 hCn) (by omega) o3
    (by rw [r3, arr, m2, ← arr]; exact e6) hCn
  refine WP.seq (WP.mono (WP.keep [.r25] (Q := fun u => u.gpr .r25 = BitVec.ofNat 64 1 ∧ u.mem = t₃.mem)
    (by prun) (by decide)) fun t₄ ⟨⟨a25, m4⟩, k4⟩ => ?_)
  have h4 := h3.next (ts3.keep k4 (by decide) fun x _ => by rw [m4]) k4 (by decide) (fun y _ => by rw [m4])
  refine WP.seq (WP.mono (products_ok (G := G) h4 hk hk1 a25 (by rw [k4.gpr .r26 (by decide), k3.gpr .r26 (by decide),
      k2.gpr .r26 (by decide), g26]) (by rw [arr, m4, ← arr]; exact e6')
      (fun a ha => by rw [ent, m4]; exact e3 a ha)) fun t₅ ⟨h5, g26', e65, ee⟩ => ?_)
  refine WP.mono (WP.keep [.r3, .r26] (Q := fun u => u.gpr .r26 = BitVec.ofNat 64 (2 ^ (k + 1)) ∧
      u.gpr .r3 = BitVec.ofNat 64 (2 ^ (k + 1)) - BitVec.ofNat 64 32 ∧ u.mem = t₅.mem)
    (by
      prun [g26', ← BitVec.ofNat_add]
      rw [Nat.pow_succ, Nat.mul_two]; exact ⟨rfl, rfl⟩) (by decide)) fun u ⟨⟨u26, u3, mu⟩, ku⟩ => ?_
  refine ⟨h5.next (h5.ts.keep ku (by decide) fun x _ => by rw [mu]) ku (by decide) (fun y _ => by rw [mu]), u26,
    by rw [arr, mu, ← arr, e65, et], fun a ha => by rw [ent, mu]; exact ee a ha,
    (VG.Proof.Bignum.PPC64LE.eval_nonzero u .r3).trans (by
      rw [u3, ofNat_sub_bne (by have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show k + 1 ≤ 5 by omega); omega)
        (by decide)])⟩

/-- The teeth `2, 4, 8, 16`. -/
theorem columns_ok {B C : Addr} {Z w P G bits : Nat} {s₀ t : State}
    (h : TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ t)
    (hr : 1 ≤ Spec.Rsa.FixedBaseComb.rows bits) (hr' : Spec.Rsa.FixedBaseComb.rows bits < 2 ^ 32)
    (h26 : t.gpr .r26 = BitVec.ofNat 64 2) (h6 : arr t.mem B w 6 = combM G P w 1)
    (he : Ents t.mem C G P w bits 2) :
    WP isa (.loop column (.nonzero .d .r3)) t fun u => TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ u ∧
      Ents u.mem C G P w bits 32 := by
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ k, n = 5 - k ∧ 1 ≤ k ∧ k < 5 ∧
      TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s₀ u ∧ u.gpr .r26 = BitVec.ofNat 64 (2 ^ k) ∧
      arr u.mem B w 6 = combM G P w (2 ^ ((k - 1) * Spec.Rsa.FixedBaseComb.rows bits)) ∧
      Ents u.mem C G P w bits (2 ^ k))
    (fun n u ⟨k, hn, hk1, hk, hu, u26, u6, ue⟩ => WP.mono (column_ok hu hk hk1 hr hr' u26 u6 ue)
      fun v ⟨hv, v26, v6, ve, vc⟩ => ?_) _ t ⟨1, rfl, Nat.le_refl _, by decide, h, h26,
        by rw [h6, Nat.sub_self, Nat.zero_mul, Nat.pow_zero], he⟩
  by_cases hk4 : k = 4
  · subst hk4
    exact Or.inl ⟨by rw [vc]; decide, hv, ve⟩
  · have hne : 2 ^ (k + 1) ≠ 32 := by
      intro e
      have : k + 1 = 5 := by
        have hk' : k < 4 := by omega
        rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl <;> simp at e
      omega
    exact Or.inr ⟨by rw [vc]; simp [hne], _, by omega, k + 1, rfl, by omega, by omega, hv, v26,
      by rw [v6, Nat.add_sub_cancel], ve⟩

/-! ## The first two entries -/

/-- `TS` after the inverse is computed again. -/
theorem TS.reinv {B C : Addr} {Z w P : Nat} {M : Mem} {s t : State} {rs : List Reg} (h : TS B C Z w P M s) (k : Keep rs s t)
    (hr : ∀ r ∈ ([.r11, .r29, .r30, .r31] : List Reg), r ∉ rs) (h10 : t.gpr .r10 = off B (slot w 0))
    (hm : ∀ x, ofs B x < slot w 1 → t.mem x = s.mem x) (h12 : (t.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem B (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0) : TS B C Z w P M t := by
  have hZ := h.env.hZ
  have hm0 : Outside B (slot w 1) (2 ^ 64) s.mem t.mem := fun y hy => hm y (by
    rcases hy with hy | hy
    · exact hy
    · have := (y - B).isLt; simp only [ofs] at hy; omega)
  have hnw := h.env.hs.nowrap
  have hw0 : w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0) :=
    hm0.w32 (Or.inl (by simp only [slot, hdrBytes]; omega)) (by simp only [slot, hdrBytes] at hZ ⊢; omega)
  refine ⟨⟨h.env.hs.congr k.wr, h10, (k.gpr _ (hr _ (by decide))).trans h.env.h29,
      (k.gpr _ (hr _ (by decide))).trans h.env.h11, (k.gpr _ (hr _ (by decide))).trans h.env.h31, h.env.hw,
      h.env.hw', h.env.hZ⟩,
    (k.gpr _ (hr _ (by decide))).trans h.h30, h.hc.congr k.wr, h.sepCB, h.sepBC, h12,
    by rw [hw0]; exact hinv, ?_, h.odd, h.one, fun x hx => (hm x hx).trans (h.low x hx)⟩
  rw [arr, hm0.val32 (Or.inl (by simp only [slot, hdrBytes]; omega)) (by simp only [slot, hdrBytes] at hZ ⊢; omega)]
  exact h.hp

/-- p's low word is odd. -/
theorem TS.lowWord {B C : Addr} {Z w P : Nat} {M : Mem} {s : State} (h : TS B C Z w P M s) :
    (word s.mem B (slot w 0)).toNat % 2 = 1 := by
  have hw := h.env.hw
  have h1 := word_eq_w32 s.mem B (slot w 0)
  have h2 : val32 s.mem B (slot w 0) (2 * w - 1 + 1) =
      w32 s.mem B (slot w 0) + 2 ^ 32 * val32 s.mem B (slot w 0 + 4) (2 * w - 1) := rfl
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * w)] at h2
  have := h.odd
  have hp := h.hp
  rw [arr] at hp
  omega

theorem exponent_one (bits : Nat) : Spec.Rsa.FixedBaseComb.exponent bits 1 = 1 := by
  simpa using VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits 0 (by decide)

theorem combM_zero {G P w : Nat} (hP : 1 < P) : combM G P w 0 = 2 ^ (64 * w) % P := by
  rw [combM, VG.Proof.Bignum.powMod_eq, Nat.pow_zero, Nat.mod_eq_of_lt hP, Nat.one_mul]

theorem combM_one {G P w : Nat} (hG : G < P) : combM G P w 1 = G * 2 ^ (64 * w) % P := by
  rw [combM, VG.Proof.Bignum.powMod_eq, Nat.pow_one, Nat.mod_eq_of_lt hG]

/-- A write within the working space keeps the context. -/
theorem ctx_of_ws {B C : Addr} {Z w P o n : Nat} {M : Mem} {s : State} {m m' : Mem} (h : TS B C Z w P M s)
    (out : Outside B o n m m') (hn : o + n ≤ Z) : Outside C (8 * ctxWords w) (2 ^ 64) m m' :=
  out_far out fun x hx => Nat.le_trans hn (h.sepCB x hx)

/-- `loadG`: g's `k` octets (at `D + k`) into array 4. -/
theorem loadG_ok {B C D : Addr} {Z w P k : Nat} {M : Mem} {s : State} (h : TS B C Z w P M s) (h23 : s.gpr .r23 = B)
    (h21 : s.gpr .r21 = D) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D k) i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off (off D k) i ≠ x) :
    WP isa loadG s fun t =>
      (arr t.mem B w 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ∧
        Outside B (slot w 4) (8 * w) s.mem t.mem ∧ t.gpr .r10 = off B (slot w 0)) ∧
      Keep [.r0, .r6, .r10, .r12, .r14, .r15, .r16, .r17] s t := by
  have hZ := h.env.hZ
  have hw := h.env.hw; have hw' := h.env.hw'
  unfold loadG
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r6, .r12] (Q := fun t => t.gpr .r12 = off (off D k) 0 ∧ t.gpr .r6 = BitVec.ofNat 64 k ∧
    t.mem = s.mem) (by prun [h21, h28, BitVec.add_zero]) (by decide)) fun t₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_
  refine WP.mono ((h.env.keep k1 (by decide)).base (rd := .r10) (by decide) (by decide) 4)
    fun t₂ ⟨⟨a10, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (loadN_ok (dA := slot w 4) (h.env.hs.congr k12.wr) a10
    ((k2.gpr .r12 (by decide)).trans a12) ((k2.gpr .r6 (by decide)).trans a6)
    ((k12.gpr .r11 (by decide)).trans h.env.h11) hk hkw (by omega) (by simp only [slot, hdrBytes]; omega)
    (by have := Env.arr h.env (j := 4) (by decide); omega)
    (fun i hi => by rw [k12.rd, k12.wr]; exact hrd i hi) hsep) fun t₃ ⟨v3, o3, k3⟩ => ?_)
  have g23 : t₃.gpr .r23 = B := by rw [k3.gpr .r23 (by decide), k12.gpr .r23 (by decide), h23]
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w 0) ∧ t.mem = t₃.mem)
    (by prun [g23, hdrBytes]; simp only [off, slot, hdrBytes, Nat.zero_mul, Nat.add_zero]) (by decide))
    fun t ⟨⟨a10', mt⟩, kt⟩ => ?_
  rw [m2, m1] at v3 o3
  refine ⟨⟨by rw [arr, mt]; exact v3, by rw [mt]; exact o3, a10'⟩, ((k12.trans k3).trans kt).mono (by decide)⟩

/-- Changes only in the working space and the context. -/
def WsOnly (B C : Addr) (Z n : Nat) (m m' : Mem) : Prop := ∀ y, Z ≤ ofs B y → n ≤ ofs C y → m' y = m y

theorem WsOnly.trans {B C : Addr} {Z n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : WsOnly B C Z n m₁ m₂)
    (h₂ : WsOnly B C Z n m₂ m₃) : WsOnly B C Z n m₁ m₃ := fun y a b => (h₂ y a b).trans (h₁ y a b)

theorem WsOnly.of_eq {B C : Addr} {Z n : Nat} {m m' : Mem} (h : m' = m) : WsOnly B C Z n m m' :=
  fun _ _ _ => by rw [h]

theorem WsOnly.of_ws {B C : Addr} {Z n o k : Nat} {m m' : Mem} (h : Outside B o k m m') (hk : o + k ≤ Z) :
    WsOnly B C Z n m m' := fun y a _ => h y (Or.inr (Nat.le_trans hk a))

theorem WsOnly.of_ctx {B C : Addr} {Z n o k : Nat} {m m' : Mem} (h : Outside C o k m m') (hk : o + k ≤ n) :
    WsOnly B C Z n m m' := fun y _ b => h y (Or.inr (Nat.le_trans hk b))

theorem WsOnly.of_outs {B C : Addr} {Z n : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z) : WsOnly B C Z n m m' :=
  fun y a _ => h y fun r hr' => Or.inr (Nat.le_trans (hr r hr') a)

/-- Octets apart from both keep their values. -/
theorem WsOnly.bytes {B C Q : Addr} {Z n k : Nat} {m m' : Mem} (h : WsOnly B C Z n m m')
    (hB : ∀ i < k, ∀ x, ofs B x < Z → off Q i ≠ x) (hC : ∀ i < k, ∀ x, ofs C x < n → off Q i ≠ x) :
    Spec.Rsa.bytesAt m' Q k = Spec.Rsa.bytesAt m Q k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  refine h _ ?_ ?_
  · by_contra hc; exact hB i hi' (Q + BitVec.ofNat 64 i) (Nat.lt_of_not_le hc) rfl
  · by_contra hc; exact hC i hi' (Q + BitVec.ofNat 64 i) (Nat.lt_of_not_le hc) rfl

/-- The working space's changes by `montOp`. -/
theorem TS.mont_ws {B C : Addr} {Z w P : Nat} {M : Mem} {s : State} (h : TS B C Z w P M s) {o a b : Nat} (ho : o < 8)
    (ha : a < 8) (hb : b < 8) (ho2 : o ≠ 2) (ho3 : o ≠ 3) (ha2 : a ≠ 2) (hb2 : b ≠ 2)
    (hB : arr s.mem B w b < P) (n : Nat) :
    WP isa (PublicChecked.montOp o a b) s fun t => WsOnly B C Z n s.mem t.mem := by
  have := h.env.hw; have := h.env.hw'; have hZ := h.env.hZ
  refine WP.mono (Pub.montOp_ok h.env.hs ho ha hb ho2 ho3 ha2 hb2 (by omega) (by omega)
    (Nat.le_trans (by simp only [slot]; omega) hZ) h.env.h10 h.env.h29 h.env.h11 h.h12 h.hinv
    (by rw [← arr, ← arr, h.hp]; exact hB)) fun t ⟨⟨_, _, out⟩, _⟩ => WsOnly.of_outs out fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact Env.arr h.env (by omega)

/-- `initial`: entries 0 (Montgomery one) and 1 (g), and array 6 `:=` g. -/
theorem initial_ok {B C D : Addr} {Z w P k rows G bits : Nat} {s : State} (h : TT B C Z w P rows s s)
    (h1 : arr s.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P) (h21 : s.gpr .r21 = D)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D k) i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off (off D k) i ≠ x)
    (hsepC : ∀ i < k, ∀ x, ofs C x < 8 * ctxWords w → off (off D k) i ≠ x)
    (hG : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) = G) (hGP : G < P) :
    WP isa initial s fun t => TT B C Z w P rows s t ∧ arr t.mem B w 6 = combM G P w 1 ∧
      Ents t.mem C G P w bits 2 := by
  have hZ := h.ts.env.hZ
  have hw := h.ts.env.hw; have hw' := h.ts.env.hw'
  have hP : 0 < P := by have := h.ts.one; omega
  have hCn := h.ts.hc.nowrap
  have hnw := h.ts.fit
  have a1 : ∀ c, c < 8 → slot w c + 8 * (w + 2) ≤ Z := fun c hc => Env.arr h.ts.env (by omega)
  unfold initial
  simp only [seqs]
  -- 1 in array 7.
  refine WP.seq (WP.mono (Pub.oneP_ok h.ts.env.hs (by omega) (by omega)
    (Nat.le_trans (slot_mono (show 8 ≤ 28 by decide)) hZ) h.ts.env.h10 h.ts.env.h29 h.ts.env.h11)
    fun t₁ ⟨⟨a7, o1⟩, k1⟩ => ?_)
  have ts1 := h.ts.keep k1 (by decide) fun x hx => o1 x (Or.inl (Nat.lt_of_lt_of_le hx (slot_mono (by decide))))
  have c1 := ctx_of_ws h.ts o1 (by have := a1 7 (by decide); omega)
  have w1 : WsOnly B C Z (8 * ctxWords w) s.mem t₁.mem := WsOnly.of_ws o1 (by have := a1 7 (by decide); omega)
  have h1' := h.next ts1 k1 (by decide) (CtxKeep.of_far' c1)
  have g1 : arr t₁.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P := by
    rw [arr, Outside.val32 o1 (Or.inl (by have := slot_lt' (w := w) (show 1 < 7 by decide); omega)) (by
      have := a1 1 (by decide); omega), ← arr]; exact h1
  -- Montgomery one in array 6.
  have hB7 : arr t₁.mem B w 7 < P := by rw [arr, a7]; exact h.ts.one
  refine WP.seq (WP.mono (WP.and (ts1.mont (o := 6) (a := 1) (b := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hB7)
    (ts1.mont_ws (o := 6) (a := 1) (b := 7) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hB7 (8 * ctxWords w)))
    fun t₂ ⟨⟨⟨l2, q2, c2a, ctx2, ts2⟩, k2⟩, w2⟩ => ?_)
  have h2 := h1'.next ts2 k2 (by decide) (CtxKeep.of_far' ctx2)
  have v2 : arr t₂.mem B w 6 = entV G P w bits 0 := by
    rw [entV, VG.Proof.Rsa.FixedBaseComb.exponent_zero, combM_zero h.ts.one]
    refine mont_eq (w := w) h.ts.odd l2 (Nat.mod_lt _ hP) ?_
    rw [q2, g1, show arr t₁.mem B w 7 = 1 from a7, Nat.mul_one, Nat.mod_mod, Nat.mod_mul_mod]
  -- Entry 0.
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 2 ∧ u.mem = t₂.mem)
    (by prun) (by decide)) fun t₃ ⟨⟨a3, m3⟩, k3⟩ => ?_)
  have h3 := h2.next (ts2.keep k3 (by decide) fun x _ => by rw [m3]) k3 (by decide) (fun y _ => by rw [m3])
  refine WP.seq (WP.mono (h3.ts.store (j := 2) (a := 6) (by decide) a3 (by decide))
    fun t₄ ⟨⟨r4, o4, b4, ts4⟩, k4⟩ => ?_)
  have h4 := h3.next ts4 k4 (by decide) (CtxKeep.of_row (j := 2) (CtxKeep.refl _ _ _) (Nat.le_refl _) o4)
  have e4 : Ents t₄.mem C G P w bits 1 := Ents.store (n := 0) (fun _ h => absurd h (Nat.not_lt_zero _))
    (by decide) o4 (by rw [r4, arr, m3, ← arr]; exact v2) hCn
  have w4 : WsOnly B C Z (8 * ctxWords w) s.mem t₄.mem :=
    ((w1.trans w2).trans (WsOnly.of_eq m3)).trans (WsOnly.of_ctx o4 (row_fits (w := w) (e := 0) (by decide)))
  have g4 : arr t₄.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P := by
    rw [arr, b4.val32 (Or.inl (by have := a1 1 (by decide); omega)) (by have := a1 1 (by decide); omega),
      m3, ← arr, c2a 1 (by decide) (by decide) (by decide) (by decide)]; exact g1
  -- g into array 4, and the inverse again.
  have hb4 : Spec.Rsa.bytesAt t₄.mem (off D k) k = Spec.Rsa.bytesAt s.mem (off D k) k := w4.bytes hsep hsepC
  have k04 := h4.kr
  refine WP.seq (WP.mono (loadG_ok h4.ts h4.h23 (by rw [k04.gpr .r21 (by decide), h21])
    (by rw [k04.gpr .r28 (by decide), h28]) hk hkw (fun i hi => by rw [k04.rd, k04.wr]; exact hrd i hi) hsep)
    fun t₅ ⟨⟨v5, o5, a10⟩, k5⟩ => ?_)
  rw [hb4, hG] at v5
  have low5 : (word t₅.mem B (slot w 0)).toNat % 2 = 1 := by
    rw [Outs.word (Outs.of_outside (rs := [(slot w 4, 8 * w)]) o5 (by simp)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      simp only [slot, hdrBytes]; omega) (by simp only [slot, hdrBytes] at hZ ⊢; omega)]
    exact h4.ts.lowWord
  refine WP.seq (WP.mono (Pub.minv_ok (h4.ts.env.hs.congr k5.wr) a10 (by simp only [slot, hdrBytes] at hZ ⊢; omega)
    low5) fun t₆ ⟨⟨r12a, r12b, m6⟩, k6⟩ => ?_)
  have w32eq : w32 t₅.mem B (slot w 0) = w32 t₄.mem B (slot w 0) :=
    Outside.w32 o5 (Or.inl (by simp only [slot, hdrBytes]; omega)) (by simp only [slot, hdrBytes] at hZ ⊢; omega)
  have ts6 : TS B C Z w P s.mem t₆ := h4.ts.reinv (k5.trans k6) (by decide)
    (by rw [k6.gpr .r10 (by decide)]; exact a10)
    (fun x hx => by rw [m6]; exact o5 x (Or.inl (Nat.lt_of_lt_of_le hx (slot_mono (by decide))))) r12a
    (by rw [← w32eq]; exact r12b)
  have c6 : Outside C (8 * ctxWords w) (2 ^ 64) t₄.mem t₆.mem := fun y hy => by
    rw [m6]; exact ctx_of_ws h4.ts o5 (by have := a1 4 (by decide); omega) y hy
  have h6 := h4.next ts6 (k5.trans k6) (by decide) (CtxKeep.of_far' c6)
  -- g R mod p into array 5.
  have g6a4 : arr t₆.mem B w 4 = G := by rw [arr, m6, ← arr]; exact v5
  have g6a1 : arr t₆.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P := by
    rw [arr, m6, Outside.val32 o5 (Or.inl (by have := slot_lt' (w := w) (show 1 < 4 by decide); omega)) (by
      have := a1 1 (by decide); omega), ← arr]; exact g4
  refine WP.seq (WP.mono (ts6.mont (o := 5) (a := 4) (b := 1) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [g6a1]; exact Nat.mod_lt _ hP))
    fun t₇ ⟨⟨l7, q7, c7a, ctx7, ts7⟩, k7⟩ => ?_)
  have h7 := h6.next ts7 k7 (by decide) (CtxKeep.of_far' ctx7)
  have v7 : arr t₇.mem B w 5 = entV G P w bits 1 := by
    rw [entV, exponent_one, combM_one hGP]
    refine mont_eq (w := w) h.ts.odd l7 (Nat.mod_lt _ hP) ?_
    rw [q7, g6a4, g6a1, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_assoc]
  -- Entry 1.
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 3 ∧ u.mem = t₇.mem)
    (by prun) (by decide)) fun t₈ ⟨⟨a3', m8⟩, k8⟩ => ?_)
  have h8 := h7.next (ts7.keep k8 (by decide) fun x _ => by rw [m8]) k8 (by decide) (fun y _ => by rw [m8])
  refine WP.seq (WP.mono (h8.ts.store (j := 3) (a := 5) (by decide) a3' (by decide))
    fun t₉ ⟨⟨r9, o9, b9, ts9⟩, k9⟩ => ?_)
  have h9 := h8.next ts9 k9 (by decide) (CtxKeep.of_row (j := 3) (CtxKeep.refl _ _ _) (by decide) o9)
  have c48 : Outside C (8 * ctxWords w) (2 ^ 64) t₄.mem t₈.mem := fun y hy => by
    rw [m8, ctx7 y hy, c6 y hy]
  have e9 : Ents t₉.mem C G P w bits 2 := Ents.store (n := 1) (Ents.of_far e4 (by decide) c48 hCn) (by decide) o9
    (by rw [r9, arr, m8, ← arr]; exact v7) hCn
  have g9a5 : arr t₉.mem B w 5 = entV G P w bits 1 := by
    rw [arr, b9.val32 (Or.inl (by have := a1 5 (by decide); omega)) (by have := a1 5 (by decide); omega), m8, ← arr]
    exact v7
  -- Array 6 := array 5.
  have wc : Win.WCtx t₉ B Z w P := ⟨ts9.env.hs, by omega, by omega, Nat.le_trans (slot_mono (by decide)) hZ,
    ts9.env.h10, ts9.env.h29, ts9.env.h11, ts9.h12, ts9.hinv, ts9.hp⟩
  refine WP.mono (Win.copy_ok wc (o := 6) (a := 5) (by decide) (by decide) (by decide))
    fun t ⟨⟨v6, o6⟩, kt⟩ => ?_
  have ts10 := ts9.keep kt (by decide) fun x hx => o6 x (Or.inl (Nat.lt_of_lt_of_le hx (slot_mono (by decide))))
  have c10 := ctx_of_ws ts9 o6 (by have := a1 6 (by decide); omega)
  refine ⟨h9.next ts10 kt (by decide) (CtxKeep.of_far' c10), ?_, Ents.of_far e9 (by decide) c10 hCn⟩
  exact v6.trans (g9a5.trans (by rw [entV, exponent_one]))

/-- `table`: the 32 entries into rows 2 to 33. -/
theorem table_ok {B C D : Addr} {Z w P k G bits : Nat} {s : State}
    (h : TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s s)
    (hr : 1 ≤ Spec.Rsa.FixedBaseComb.rows bits) (hr' : Spec.Rsa.FixedBaseComb.rows bits < 2 ^ 32)
    (h1 : arr s.mem B w 1 = 2 ^ (64 * w) * 2 ^ (64 * w) % P) (h21 : s.gpr .r21 = D)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D k) i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off (off D k) i ≠ x)
    (hsepC : ∀ i < k, ∀ x, ofs C x < 8 * ctxWords w → off (off D k) i ≠ x)
    (hG : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) = G) (hGP : G < P) :
    WP isa table s fun t => TT B C Z w P (Spec.Rsa.FixedBaseComb.rows bits) s t ∧
      Ents t.mem C G P w bits 32 := by
  unfold table
  refine WP.seq (WP.mono (initial_ok (bits := bits) h h1 h21 h28 hk hkw hrd hsep hsepC hG hGP)
    fun t₁ ⟨h1', a6, e1⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.r26] (Q := fun u => u.gpr .r26 = BitVec.ofNat 64 2 ∧ u.mem = t₁.mem)
    (by prun) (by decide)) fun t₂ ⟨⟨a26, m2⟩, k2⟩ => ?_)
  exact columns_ok (h1'.next (h1'.ts.keep k2 (by decide) fun x _ => by rw [m2]) k2 (by decide)
    (fun y _ => by rw [m2])) hr hr' a26 (by rw [arr, m2, ← arr]; exact a6) (fun a ha => by rw [ent, m2]; exact e1 a ha)

end VG.Proof.Ffdh.PPC64LE.Cached
