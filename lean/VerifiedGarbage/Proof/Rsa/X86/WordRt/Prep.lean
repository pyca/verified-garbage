module

public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Impl.Rsa.X86.WordModRt
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Ptr
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Recip
import VerifiedGarbage.Proof.Bignum.WordStep32
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power

/-! # `WordModRt` on i686: the divisor's top word and the reciprocal

The divisor `m` has `W' = ⌈m_len / 4⌉` words, `m_len` an argument (`MLen`).
`topPtr_ok`: a pointer to word `W' - i` of an array; `orTop_ok`: the top
bit of word `W' - 1` set, and that word `d` and the one below it `d₁` into
the header; `recip_ok`: the reciprocal `v = ⌊(2^64 - 1) / d⌋ - 2^32` into
the header, by `R2Words`' loop.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.WordRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc)
open VG.Impl.Rsa.X86.WordModRt (oD oV oD1 h0)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem oD_val : oD = 60 := rfl
theorem oV_val : oV = 64 := rfl
theorem oD1_val : oD1 = 88 := rfl

/-- The divisor's words: `⌈a / 4⌉`. -/
abbrev wq (a : Nat) : Nat := (a + 3) / 4

/-- The divisor's length `a`, argument `ml`. -/
structure MLen (s : State) (B : Addr) (Z ml a : Nat) : Prop where
  arg : CallArgument s B Z ml (BitVec.ofNat 32 a)
  le : a ≤ 1024

theorem MLen.keep {s t : State} {ml a : Nat} (h : MLen s B Z ml a) {rs : List Reg} (K : Keeps rs s t)
    (sp : .esp ∉ rs) (O : Outside B 0 Z s.mem t.mem) : MLen t B Z ml a :=
  ⟨h.arg.keep K sp O, h.le⟩

/-- `width4 ml r`: `r = 4 W'`. -/
theorem width4_ok {s : State} {is : List Instr} {Q : State → Prop} {ml a : Nat} {r : Reg}
    (hm : MLen s B Z ml a)
    (kk : ∀ t, Keeps [r] s t → t.mem = s.mem → t.gpr r = BitVec.ofNat 32 (4 * wq a) → WP isa (.block is) t Q) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.width4 ml r ++ is)) s Q :=
  VG.Proof.Bignum.X86.R2Words.width4_ok (op := argOp ml) hm.arg.readSrc hm.le kk

/-- `topPtr ml r j i t`: `r` at word `W' - i` of array `j`, `t = 4 W'`. -/
theorem topPtr_ok {s : State} {is : List Instr} {Q : State → Prop} (h : RtWs L s B Z len N) {ml a j i : Nat}
    {r t : Reg} (hm : MLen s B Z ml a) (hj : j < N) (hrt : r ≠ t) (hte : t ≠ .edi)
    (hrs : r ≠ .esp) (hts : t ≠ .esp) (hi : i ≤ wq a) (hw : wq a ≤ kw len + 2)
    (kk : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u B r (arr (kw len) j + 4 * wq a - 4 * i) →
      u.gpr t = BitVec.ofNat 32 (4 * wq a) → WP isa (.block is) u Q) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.topPtr L ml r j i t ++ is)) s Q := by
  have fit := h.ws.arr_fit hj
  have nw := h.ws.workspace.nowrap
  simp only [S] at fit
  simp only [VG.Impl.Rsa.X86.WordModRt.topPtr, List.append_assoc, List.cons_append, List.nil_append]
  refine arrPtr_ok (lenSrc h) h.lenLe h.edi hrt hte (by omega) fun u₁ K₁ m₁ p₁ _ => ?_
  have hm₁ : MLen u₁ B Z ml a :=
    hm.keep K₁ (by simp [hrs.symm, hts.symm]) (by rw [m₁]; exact Outside.refl _ _ _ _)
  refine width4_ok hm₁ fun u₂ K₂ m₂ e₂ => wp_addS rfl fun u₃ U₃ _ => wp_subS rfl fun u₄ U₄ _ => ?_
  have K : Keeps [r, t] s u₄ := (K₁.trans (K₂.mono (by simp))).trans
    ((U₃.keeps.mono (by simp)).trans (U₄.keeps.mono (by simp)))
  refine kk u₄ K (by rw [U₄.mem, U₃.mem, m₂, m₁]) ?_ (by rw [U₄.other _ hrt.symm, U₃.other _ hrt.symm, e₂])
  have hp₂ : PtrAt u₂ B r (arr (kw len) j) := by rw [PtrAt, K₂.1 _ (by simp [hrt])]; exact p₁
  rw [PtrAt, U₄.gpr, U₃.gpr, e₂]
  have h4 : (BitVec.ofNat 32 (4 * wq a)).toNat = 4 * wq a := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hm.le; omega)
  have hi4 : (BitVec.ofNat 32 (4 * i)).toNat = 4 * i := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hm.le; omega)
  rw [BitVec.toNat_sub, BitVec.toNat_add, hp₂, h4, hi4]
  have := B.isLt
  omega

theorem or_top {x : Nat} (hx : x < 2 ^ 32) : x ||| 2 ^ 31 = x % 2 ^ 31 + 2 ^ 31 := by
  have hy : x % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  have e : 2 ^ 31 + x % 2 ^ 31 = 2 ^ 31 ||| x % 2 ^ 31 := by
    have := Nat.shiftLeft_add_eq_or_of_lt (a := 1) (i := 31) hy
    simpa [Nat.shiftLeft_eq] using this
  generalize hl : x % 2 ^ 31 = l at hy e
  rcases (show x / 2 ^ 31 = 0 ∨ x / 2 ^ 31 = 1 by omega) with h | h
  · have hx' : x = l := by omega
    subst hx'
    rw [Nat.or_comm, ← e, Nat.add_comm]
  · have hx' : x = 2 ^ 31 + l := by omega
    rw [hx', e, Nat.or_assoc, Nat.or_comm l, ← Nat.or_assoc, Nat.or_self, ← e, Nat.add_comm]

/-- The divisor's word `i`. -/
abbrev mw (m : Mem) (B : Addr) (w j i : Nat) : Nat := w32 m B (arr w j + 4 * i)

/-- `orTop ml m`: the top bit of `m`'s word `W' - 1` set, and `d`, `d₁`, its words `W' - 1`
and `W' - 2`, into the header. -/
theorem orTop_ok {s : State} (h : RtWs L s B Z len N) {ml a m : Nat} (hm : MLen s B Z ml a) (hj : m < N)
    (h2 : 2 ≤ wq a) (hw : wq a ≤ kw len) :
    WP isa (.block (VG.Impl.Rsa.X86.WordModRt.orTop L ml m)) s fun t =>
      RtWs L t B Z len N ∧ Keep B (kw len) [m] [oD, oD1] s.mem t.mem ∧
      (∀ i, i < kw len + 2 → i ≠ wq a - 1 → mw t.mem B (kw len) m i = mw s.mem B (kw len) m i) ∧
      mw t.mem B (kw len) m (wq a - 1) = mw s.mem B (kw len) m (wq a - 1) % 2 ^ 31 + 2 ^ 31 ∧
      slot t.mem B oD = mw t.mem B (kw len) m (wq a - 1) ∧
      slot t.mem B oD1 = mw s.mem B (kw len) m (wq a - 2) ∧
      Keeps [.eax, .ebx, .ecx] s t := by
  have fit := h.ws.arr_fit hj
  have nw := h.ws.workspace.nowrap
  have hdr := h.ws.hdr_le
  simp only [S, VG.Impl.Rsa.X86.Keys.hdr] at fit hdr
  have ws := h.rt
  unfold VG.Impl.Rsa.X86.WordModRt.orTop
  refine topPtr_ok h hm hj (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
    fun u K mu p _ => ?_
  have wsu := ws.of_keeps K
  have pt : PtrAt u B .ebx (arr (kw len) m + 4 * (wq a - 2)) := by
    rw [show arr (kw len) m + 4 * (wq a - 2) = arr (kw len) m + 4 * wq a - 4 * 2 by omega]; exact p
  have e4 : arr (kw len) m + 4 * (wq a - 2) + 4 = arr (kw len) m + 4 * (wq a - 1) := by omega
  -- The top word, its bit set, back.
  refine wp_movS (readSrc_ptr wsu pt (d := 4) (by omega)) fun t₁ U₁ _ => wp_orS rfl fun t₂ U₂ => ?_
  have wt₂ := wsu.of_wr (U₂.wr.trans U₁.wr)
  have pt₂ : PtrAt t₂ B .ebx (arr (kw len) m + 4 * (wq a - 2)) := by
    rw [PtrAt, U₂.other _ (by decide), U₁.other _ (by decide)]; exact pt
  refine wp_storeS (ea_ptr wt₂ pt₂ (d := 4) (by omega)) (ws_write wt₂ (by omega)) fun t₃ M₃ => ?_
  rw [e4] at M₃
  have wt₃ := wt₂.of_wr (M₃.keeps []).2.2
  have di₃ : PtrAt t₃ B .edi 0 := by
    rw [PtrAt, (M₃.keeps []).1 _ (by decide), U₂.other _ (by decide), U₁.other _ (by decide), K.1 _ (by decide),
      h.edi, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  refine wp_storeS (ea_ptr wt₃ di₃ (d := oD) (by rw [oD_val]; omega)) (ws_write wt₃ (by rw [oD_val]; omega))
    fun t₄ M₄ => ?_
  have wt₄ := wt₃.of_wr (M₄.keeps []).2.2
  have pt₄ : PtrAt t₄ B .ebx (arr (kw len) m + 4 * (wq a - 2)) := by
    rw [PtrAt, (M₄.keeps []).1 _ (by decide), (M₃.keeps []).1 _ (by decide)]; exact pt₂
  refine wp_movS (readSrc_ptr wt₄ pt₄ (d := 0) (by omega)) fun t₅ U₅ _ => ?_
  have di₅ : PtrAt t₅ B .edi 0 := by
    rw [PtrAt, U₅.other _ (by decide), (M₄.keeps []).1 _ (by decide)]; exact di₃
  refine wp_storeS (ea_ptr (wt₄.of_wr U₅.wr) di₅ (d := oD1) (by rw [oD1_val]; omega))
    (ws_write (wt₄.of_wr U₅.wr) (by rw [oD1_val]; omega)) fun t₆ M₆ => WP.block_nil ?_
  -- The values.
  have top : (t₂.gpr .eax).toNat = mw s.mem B (kw len) m (wq a - 1) % 2 ^ 31 + 2 ^ 31 := by
    rw [U₂.gpr, U₁.gpr, mu, Nat.add_zero, e4, BitVec.toNat_or]
    exact or_top (s.mem.readW _ 32).isLt
  have m₆ : t₆.mem = ((s.mem.writeW (off B (arr (kw len) m + 4 * (wq a - 1))) (t₂.gpr .eax)).writeW
      (off B (0 + oD)) (t₂.gpr .eax)).writeW (off B (0 + oD1)) (t₅.gpr .eax) := by
    rw [M₆.mem, U₅.mem, M₄.mem, M₃.mem, (M₃.keeps []).1 _ (by decide), U₂.mem, U₁.mem, mu]
  rw [Nat.zero_add, Nat.zero_add] at m₆
  have hoD : oD + 4 ≤ arr (kw len) m := by rw [oD_val]; simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega
  have hoD1 : oD1 + 4 ≤ arr (kw len) m := by rw [oD1_val]; simp only [arr, VG.Impl.Rsa.X86.Keys.hdr]; omega
  have O₁ := writeW32_outside s.mem B (d := arr (kw len) m + 4 * (wq a - 1)) (t₂.gpr .eax) (by omega)
  have O₂ := writeW32_outside (s.mem.writeW (off B (arr (kw len) m + 4 * (wq a - 1))) (t₂.gpr .eax)) B
    (d := oD) (t₂.gpr .eax) (by rw [oD_val]; omega)
  have O₃ := writeW32_outside ((s.mem.writeW (off B (arr (kw len) m + 4 * (wq a - 1))) (t₂.gpr .eax)).writeW
    (off B oD) (t₂.gpr .eax)) B (d := oD1) (t₅.gpr .eax) (by rw [oD1_val]; omega)
  rw [← m₆] at O₃
  have K₆ : Keeps [.eax, .ebx, .ecx] s t₆ := (K.mono (by simp)).trans
    (((U₁.keeps.mono (by simp)).trans (U₂.keeps.mono (by simp))).trans
      ((((M₃.keeps _).trans (M₄.keeps _)).trans (U₅.keeps.mono (by simp))).trans (M₆.keeps _)))
  have wTop : mw t₆.mem B (kw len) m (wq a - 1) = (t₂.gpr .eax).toNat := by
    rw [mw, O₃.w32 (.inr (by omega)) (by omega), O₂.w32 (.inr (by omega)) (by omega),
      w32_write_self]
  have wOther : ∀ i, i < kw len + 2 → i ≠ wq a - 1 → mw t₆.mem B (kw len) m i = mw s.mem B (kw len) m i :=
    fun i hi hne => by
      rw [mw, O₃.w32 (.inr (by omega)) (by omega), O₂.w32 (.inr (by omega)) (by omega),
        O₁.w32 (by omega) (by omega)]
  refine ⟨h.keep K₆ (by decide) (by decide) ?_, ?_, wOther, by rw [wTop, top], ?_, ?_, K₆⟩
  · intro x hx
    have h1 := O₁ x (by omega)
    have h2 := O₂ x (by rw [oD_val]; omega)
    have h3 := O₃ x (by rw [oD1_val]; omega)
    exact h3.trans (h2.trans h1)
  · exact (Keep.of_arr (js := [m]) (ds := [oD, oD1]) (d := 4 * (wq a - 1)) (n := 4) O₁ (by simp only [S]; omega)
      (by simp)).trans ((Keep.of_slot (js := [m]) (ds := [oD, oD1]) O₂ (by simp)).trans
        (Keep.of_slot O₃ (by simp)))
  · rw [slot, O₃.w32 (.inl (by rw [oD_val, oD1_val]; decide)) (by rw [oD_val]; omega), w32_write_self, wTop]
  · have m₄ : t₄.mem = (s.mem.writeW (off B (arr (kw len) m + 4 * (wq a - 1))) (t₂.gpr .eax)).writeW
        (off B oD) (t₂.gpr .eax) := by
      rw [M₄.mem, M₃.mem, (M₃.keeps []).1 _ (by decide), U₂.mem, U₁.mem, mu, Nat.zero_add]
    rw [slot, m₆, w32_write_self, U₅.gpr, m₄, Nat.add_zero]
    exact (O₂.w32 (d := arr (kw len) m + 4 * (wq a - 2)) (.inr (by omega)) (by omega)).trans
      (O₁.w32 (.inl (by omega)) (by omega))

/-- `recip`: `v = ⌊(2^64 - 1) / d⌋ - 2^32` into the header, for `d ≥ 2^31` there. -/
theorem recip_ok {s : State} (h : RtWs L s B Z len N) {d : Nat} (hD : slot s.mem B oD = d) (hd1 : 2 ^ 31 ≤ d)
    (hd2 : d < 2 ^ 32) :
    WP isa (VG.Impl.Rsa.X86.WordModRt.recip L) s fun t => RtWs L t B Z len N ∧
      Keep B (kw len) [] [oV] s.mem t.mem ∧ slot t.mem B oV = (2 ^ 64 - 1) / d - 2 ^ 32 ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have hdr := h.ws.hdr_le
  simp only [VG.Impl.Rsa.X86.Keys.hdr] at hdr
  unfold VG.Impl.Rsa.X86.WordModRt.recip
  simp only [VG.Impl.Rsa.X86.WordModRt.seqs]
  refine WP.seq (wp_movS (readSrc_sc h.ws.workspace (d := oD) (by rw [oD_val]; omega)) fun u₁ U₁ _ =>
    wp_movS rfl fun u₂ U₂ _ => wp_logicS (Or.inr rfl) rfl fun u₃ U₃ => wp_movS rfl fun u₄ U₄ _ =>
      wp_movS rfl fun u₅ U₅ _ => WP.block_nil ?_)
  have si : u₅.gpr .esi = BitVec.ofNat 32 d := by
    rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide), U₁.gpr]
    exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd2]; exact hD)
  have dx : u₅.gpr .edx = BitVec.ofNat 32 (2 ^ 32 - 1 - d) := by
    rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, ite_eq_right (by decide), U₂.gpr,
      U₁.gpr]
    rw [← VG.Proof.Bignum.X86.R2Words.xor_m1 d hd2]
    congr 1
    exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd2]; exact hD)
  have cx : u₅.gpr .ecx = BitVec.ofNat 32 0 := by rw [U₅.other _ (by decide), U₄.gpr]; rfl
  have di : u₅.gpr .edi = BitVec.ofNat 32 32 := by rw [U₅.gpr]; rfl
  have K₅ : Keeps [.esi, .edx, .ecx, .edi] s u₅ := (((U₁.keeps.mono (by simp)).trans (U₂.keeps.mono (by simp))).trans
    (U₃.keeps.mono (by simp))).trans ((U₄.keeps.mono (by simp)).trans (U₅.keeps.mono (by simp)))
  have m₅ : u₅.mem = s.mem := by rw [U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.R2Words.recipLoop_ok hd1 hd2 dx si cx di) fun t ⟨hcx, hmt, Kt⟩ => ?_)
  have Kst : Keeps [.esi, .edx, .ecx, .edi, .eax, .ebx, .ebp] s t := (K₅.mono (by decide)).trans (Kt.mono (by decide))
  have A := h.wsArg.keep Kst (by decide) (by rw [hmt, m₅]; exact Outside.refl _ _ _ _)
  unfold restoreEdi
  refine wp_movS A.readSrc fun t₁ U₁ _ => ?_
  have K₁ : Keeps [.esi, .edx, .ecx, .eax, .ebx, .ebp] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.esi, .edx, .ecx, .eax, .ebx, .ebp])
      ((Kst.trans (U₁.keeps.mono (by simp))).mono (by simp)) (U₁.gpr.trans h.edi_eq.symm)
  have h₁ : RtWs L t₁ B Z len N := h.keep K₁ (by decide) (by decide) (by rw [U₁.mem, hmt, m₅]; exact Outside.refl _ _ _ _)
  refine WP.mono (VG.Proof.Rsa.X86.KeyRt.storeSlot_ok h₁ (d := oV) (by rw [oV_val]; simp only [VG.Impl.Rsa.X86.Keys.hdr]; omega) .ecx)
    fun t₂ ⟨h₂, k₂, e₂, r₂⟩ => ?_
  have hq : VG.Proof.Bignum.X86.R2Words.rdiv d 32 / d = (2 ^ 64 - 1) / d - 2 ^ 32 := by
    rw [← VG.Proof.Bignum.WordStep32.recip_eq hd2 (by omega)]; rfl
  have hv32 : (2 ^ 64 - 1) / d - 2 ^ 32 < 2 ^ 32 := by
    have : (2 ^ 64 - 1) / d < 2 ^ 33 := by rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    omega
  refine ⟨h₂, by rw [U₁.mem, hmt, m₅] at k₂; exact k₂, ?_, (K₁.mono (by simp)).trans (r₂.mono (by simp))⟩
  rw [e₂, U₁.other _ (by decide), hcx, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv32]

end VG.Proof.Rsa.X86.WordRt
