module

public import VerifiedGarbage.Proof.Rsa.X86_64.KeySteps
public import VerifiedGarbage.Impl.Rsa.X86_64.PrivPre
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.R2
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_private_precompute` on x86-64: the pieces

In `vg_rsa_check_key`'s context (`KCtx`): the powers of 2 in the
accumulator (`accTopK`, `accPrimeK`), and the copies of arrays to the words
past them (`copyOutK`), which keep the context (`KCtx.far`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey VG.Impl.Rsa.X86_64.PrivPre
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK)

/-- `[o] := v 2^(64 i)` over the `w + 2` words of the array, for `v` in
`rdx` and the word index `i < w + 2` in `ri`. -/
theorem setWordW_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {o : Nat} (ho : o < 8) {ri : Reg} (hri : ri ∉ [.rax, .r8, .r14])
    {i : Nat} (hi : i < w + 2) (hix : s.gpr ri = BitVec.ofNat 64 i) :
    WP isa (setWord o ri) s fun t =>
      wv t.mem B (slot w o) (w + 2) = (s.gpr .rdx).toNat * 2 ^ (64 * i) ∧
      Outside B (slot w o) (8 * (w + 2)) s.mem t.mem ∧ Keep [.rax, .r8, .r14] s t := by
  have hn := hs.nowrap
  have sl : slot w o + 8 * (w + 2) ≤ Z := Nat.le_trans (slot_le ho) hZ
  unfold setWord
  refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off B (slot w o) ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.ld (show 8 * sArr o + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show sArr o < 32 by unfold sArr; omega); omega), hH.harr o ho]) rfl)
    fun s₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroAccLoop_ok (hs.congr k₁.2.2) h8 ((k₁.gpr (by decide)).trans h12) hw hw' sl)
    fun s₂ ⟨hz, ho₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have s₂8 : s₂.gpr .r8 = off B (slot w o) := (k₂.gpr (by decide)).trans h8
  have s₂i : s₂.gpr ri = BitVec.ofNat 64 i :=
    (k12.gpr (fun h => hri ((List.Perm.swap Reg.rax Reg.r8 [Reg.r14]).mem_iff.1 h))).trans hix
  have s₂dx : s₂.gpr .rdx = s.gpr .rdx := k12.gpr (by decide)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₂.mem.writeW (off B (slot w o + 8 * i)) (s.gpr .rdx))
    (by xrun [State.ea, ix, addr0 s₂8 s₂i, (hs.congr (k12.2.2)).st (show slot w o + 8 * i + 8 ≤ Z by omega),
      s₂dx]) rfl) fun t ⟨hm, k⟩ => ⟨?_, ?_, (k12.trans k).mono (by decide)⟩
  · have hz' := (wv_eq_zero_iff _ _ _ _).mp hz
    rw [wv_single t.mem B (slot w o) (w + 2) hi fun q hq hne => by
      rw [hm, (writeW_outside s₂.mem B _ (by omega)).word (by omega) (by omega)]
      exact hz' q (by omega), hm, word_writeW_self]
  · rw [hm]
    intro x hx
    rw [writeW_outside _ B _ (by omega) x (by omega)]
    exact ho₂ x hx |>.trans (by rw [hm₁])

section
variable {s t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}

/-- A change past the arrays keeps the context. -/
theorem KCtx.far (h : KCtx s t B Z w minv N) {o n : Nat} (ho : Outside B o n t.mem t'.mem)
    (hlo : slot w 8 ≤ o) (hhi : o + n ≤ Z) (hk : Keep mmRegs t t') : KCtx s t' B Z w minv N := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have h08 := slot_le (w := w) (show 0 < 8 by decide)
  have hh : ∀ i < 32, Bignum.word t'.mem B (8 * i) = Bignum.word t.mem B (8 * i) := fun i hi =>
    ho.word (Or.inl (by have := hdr_lt_slot w 0 hi; omega)) (by have := hdr_lt_slot w 0 hi; omega)
  have ha : ∀ j < 8, wv t'.mem B (slot w j) w = wv t.mem B (slot w j) w := fun j hj =>
    ho.wv (Or.inl (by have := slot_le (w := w) hj; omega)) (by have := slot_le (w := w) hj; omega)
  exact ⟨⟨h.good.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.good.rdi,
      ⟨by rw [hh sW (by decide)]; exact h.good.hdr.hw, by rw [hh sMinv (by decide)]; exact h.good.hdr.hminv,
        fun j hj => by rw [hh (sArr j) (by unfold sArr; omega)]; exact h.good.hdr.harr j hj⟩⟩,
    h.hZ, h.w1, h.w2, fun i hi hi' => (hh i hi).trans (h.hdr i hi hi'),
    h.ins.trans (fun x hx => ho x (Or.inr (by omega))), hk.2.1.trans h.rd, hk.2.2.trans h.wr,
    (ha aN (by decide)).trans h.n, (ha aOne (by decide)).trans h.one, (h.keep.trans hk).mono (by decide)⟩

theorem KCtx.ld (h : KCtx s t B Z w minv N) {i : Nat} (hi : i < 32) :
    InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 :=
  h.good.scr.ld (by have := hdr_lt_slot w 8 hi; have := h.hZ; omega)

end

end VG.Proof.Rsa.X86_64.Key

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey VG.Impl.Rsa.X86_64.PrivPre
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK)

/-- `primeW`: `r12 := max(2, ⌈len / 8⌉)`. -/
theorem primeW_ok {u : State} {B : Addr} (hdi : u.gpr .rdi = B) {sl len : Nat}
    (hl : InRegions (u.rd ++ u.wr) (off B (8 * sl)) 8) (hv : Bignum.word u.mem B (8 * sl) = BitVec.ofNat 64 len)
    (h1 : 1 ≤ len) (h2 : len < 2 ^ 32) :
    WP isa (.block (primeW sl)) u fun u' => u'.gpr .r12 = BitVec.ofNat 64 (Spec.Rsa.primeWords len) ∧
      u'.mem = u.mem ∧ Keep [.r12] u u' := by
  refine WP.mono (WP.keep [.r12] (Q := fun u' => u'.gpr .r12 = BitVec.ofNat 64 (Spec.Rsa.primeWords len) ∧
      u'.mem = u.mem) (by
    xrun [primeW, State.ea, hdr, hdi, hdrOff, hl, hv]
    apply BitVec.eq_of_toNat_eq
    rw [show BitVec.signExtend 64 (7 : BitVec 32) = BitVec.ofNat 64 7 by decide,
      show BitVec.signExtend 64 (0 : BitVec 32) = 0 by decide, BitVec.ofNat_add_ofNat]
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
      BitVec.toNat_ofBool, Nat.shiftRight_eq_div_pow]
    rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl, show BitVec.toNat (2 : BitVec 64) = 2 from rfl,
      Nat.mod_eq_of_lt (show len + 7 < 2 ^ 64 by omega)]
    unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords
    by_cases h : (len + 7) / 2 ^ 3 < 2 <;> simp only [h, decide_true, decide_false] <;> simp <;> omega) rfl) fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩

/-- `dBase`: `rbx :=` the words past the arrays, `r12 := w`. -/
theorem dBase_ok {u : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good u B Z w minv)
    (hZ : slot w 8 ≤ Z) :
    WP isa (.block dBase) u fun u' => u'.gpr .rbx = off B (slot w 8) ∧ u'.gpr .r12 = BitVec.ofNat 64 w ∧
      u'.mem = u.mem ∧ Keep [.rax, .rbx, .r12] u u' := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (u.rd ++ u.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax, .rbx, .r12] (Q := fun u' => u'.gpr .rbx = off B (slot w 8) ∧
      u'.gpr .r12 = BitVec.ofNat 64 w ∧ u'.mem = u.mem) (by
    xrun [dBase, State.ea, hdr, hg.rdi, hdrOff, hl (sArr aOne) (by decide), hl sW (by decide),
      hg.hdr.harr aOne (by decide), hg.hdr.hw]
    rw [off, off, BitVec.add_assoc, show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl]
    simp only [BitVec.ofNat_add_ofNat]
    congr 2
    unfold slot aOne
    omega) rfl) fun _ ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩

/-- `skipW`: `rbx += 8 r12`. -/
theorem skipW_ok {u : State} {B : Addr} {e c : Nat} (hbx : u.gpr .rbx = off B e)
    (h12 : u.gpr .r12 = BitVec.ofNat 64 c) :
    WP isa (.block skipW) u fun u' => u'.gpr .rbx = off B (e + 8 * c) ∧ u'.gpr .r12 = BitVec.ofNat 64 c ∧
      u'.mem = u.mem ∧ Keep [.rax, .rbx] u u' := by
  refine WP.mono (WP.keep [.rax, .rbx] (Q := fun u' => u'.gpr .rbx = off B (e + 8 * c) ∧
      u'.gpr .r12 = BitVec.ofNat 64 c ∧ u'.mem = u.mem) (by
    simp only [skipW, Impl.Rsa.X86_64.eightW, List.cons_append, List.nil_append]
    xrun [hbx, h12]
    rw [off, off, BitVec.add_assoc]
    simp only [BitVec.ofNat_add_ofNat]
    congr 2
    omega) rfl) fun _ ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩

section
variable {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}

/-- `copyOut off j`: the `c` words of array `j` to the words past the arrays
at word `e`, for the offset and count `off` sets. -/
theorem copyOutK (h : KCtx s t B Z w minv N) {offI : List Instr} {j e c : Nat} (hj : j < 8)
    (hoff : ∀ u : State, Keep [.rax, .rbx, .r12] t u → u.mem = t.mem →
      u.gpr .rbx = off B (slot w 8) → u.gpr .r12 = BitVec.ofNat 64 w →
      WP isa (.block offI) u fun u' => u'.gpr .rbx = off B (slot w 8 + 8 * e) ∧
        u'.gpr .r12 = BitVec.ofNat 64 c ∧ u'.mem = u.mem ∧ Keep [.rax, .rbx, .r12] u u')
    (hc : 1 ≤ c) (hcw : c ≤ w + 2) (he : slot w 8 + 8 * (e + c) ≤ Z) :
    WP isa (seqs (copyOut offI j)) t fun t' => KCtx s t' B Z w minv N ∧
      (∀ i < c, Bignum.word t'.mem B (slot w 8 + 8 * e + 8 * i) = Bignum.word t.mem B (slot w j + 8 * i)) ∧
      Outside B (slot w 8 + 8 * e) (8 * c) t.mem t'.mem := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have hsj := slot_le (w := w) hj
  have hw2 := h.w2
  show WP isa (.seq (.block _) Impl.Rsa.X86_64.copyWords) t _
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (dBase_ok h.good hZ) fun u₁ ⟨hbx₁, h12₁, hm₁, k₁⟩ => ?_
  refine WP.mono (hoff u₁ k₁ hm₁ hbx₁ h12₁) fun u₂ ⟨hbx₂, h12₂, hm₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hdi₂ : u₂.gpr .rdi = B := (k12.gpr (by decide)).trans h.good.rdi
  refine WP.mono (WP.keep [.rsi] (Q := fun u => u.gpr .rsi = off B (slot w j) ∧ u.mem = u₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, show InRegions (u₂.rd ++ u₂.wr) (off B (8 * sArr j)) 8 by
      rw [k12.2.1, k12.2.2]; exact h.ld (by unfold sArr; omega),
      show Bignum.word u₂.mem B (8 * sArr j) = off B (slot w j) by rw [hm₂, hm₁]; exact h.good.hdr.harr j hj])
    rfl) fun u₃ ⟨⟨hsi₃, hm₃⟩, k₃⟩ => ?_
  have k13 := k12.trans k₃
  refine WP.mono (copyWords_ok hsi₃ ((k₃.gpr (by decide)).trans hbx₂) ((k₃.gpr (by decide)).trans h12₂) hc
    (by omega) (by omega) (fun i hi => by rw [k13.2.1, k13.2.2]; exact h.good.scr.ld (by omega))
    (fun i hi => by rw [k13.2.2]; exact h.good.scr.st (by omega))
    (fun i hi b hb => Or.inl (by rw [ofs_off B (by omega)]; omega))) fun t' ⟨_, hc', ho', k'⟩ => ?_
  rw [hm₃, hm₂, hm₁] at hc' ho'
  exact ⟨h.far ho' (by omega) (by omega) ((k13.trans k').mono (by decide)), hc', ho'⟩

/-- `accTop`: the accumulator's `2 w + 2` words `:= 2^(128 w)`. -/
theorem accTopK (h : KCtx s t B Z w minv N) (hw : 2 ≤ w) :
    WP isa (seqs accTop) t fun t' => KCtx s t' B Z w minv N ∧
      wv t'.mem B (slot w aAcc) (2 * w + 2) = 2 ^ (128 * w) ∧ Arrays B w [aAcc, aTmp] t.mem t'.mem := by
  have hn := h.good.scr.nowrap
  have hZ := h.hZ
  have hw2 := h.w2
  show WP isa (.seq _ (.seq (.block _) _)) t _
  refine WP.seq (WP.mono (zeroArr_ok h.good hZ h.w1 (by omega) (j := aAcc) (by decide))
    fun t₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have a₁ : Arrays B w [aAcc, aTmp] t.mem t₁.mem :=
    Arrays.of_outside (j := aAcc) (by simp) ho₁ (Nat.le_refl _) (by omega)
  have h₁ := h.arr a₁ (by decide) (by decide) (by decide) k₁
  refine WP.seq (WP.mono (WP.keep [.rcx, .rdx, .r12] (Q := fun u => u.gpr .rcx = BitVec.ofNat 64 (w - 2) ∧
      u.gpr .rdx = 1 ∧ u.gpr .r12 = BitVec.ofNat 64 w ∧ u.mem = t₁.mem) (by
    xrun [State.ea, hdr, h₁.good.rdi, hdrOff, h₁.ld (i := sW) (by decide), h₁.good.hdr.hw]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show BitVec.toNat (2 : BitVec 64) = 2 from rfl]
    omega) rfl)
    fun t₂ ⟨⟨hcx₂, hdx₂, h12₂, hm₂⟩, k₂⟩ => ?_)
  have hg₂ : Good t₂ B Z w minv := Good.of_arrays h₁.good (js := []) (fun _ _ => by rw [hm₂]) (k₂.mono (by decide))
    k₂.2.2
  refine WP.mono (setWord_ok hg₂.scr hg₂.rdi hg₂.hdr hZ h12₂ h.w1 (by omega) (o := aTmp) (by decide)
    (ri := .rcx) (by decide) (i := w - 2) (by omega) hcx₂) fun t' ⟨hv, ho, k'⟩ => ?_
  have ho' : Outside B (slot w aTmp) (8 * (w + 2)) t₁.mem t'.mem := by rw [← hm₂]; exact ho
  have a₂ : Arrays B w [aAcc, aTmp] t₁.mem t'.mem :=
    Arrays.of_outside (j := aTmp) (by simp) ho' (Nat.le_refl _) (Nat.le_refl _)
  have kk : Keep mmRegs t₁ t' := (k₂.trans k').mono (by decide)
  refine ⟨h₁.arr a₂ (by decide) (by decide) (by decide) kk, ?_, a₁.trans a₂⟩
  have e : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega
  rw [show 2 * w + 2 = (w + 2) + w by omega, wv_add, e, hv, hdx₂,
    ho.wv (Or.inl (by rw [← e])) (by have := slot_le (w := w) (show aAcc < 8 by decide); omega), hm₂, hz₁]
  rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.one_mul, Nat.zero_add, ← Nat.pow_add]
  congr 1
  omega

/-- `accPrime sl`: the accumulator's `w + 2` words `:= 2^(64 w_X)`, for the
length `len` in header slot `sl`. -/
theorem accPrimeK (h : KCtx s t B Z w minv N) {sl len : Nat} (hsl : sl < 32) (hsl' : sl ≠ sMask)
    (hl : Bignum.word s.mem B (8 * sl) = BitVec.ofNat 64 len) (h1 : 1 ≤ len) (hlw : len ≤ 8 * w)
    (hw : 2 ≤ w) :
    WP isa (seqs (accPrime sl)) t fun t' => KCtx s t' B Z w minv N ∧
      wv t'.mem B (slot w aAcc) (w + 2) = 2 ^ (64 * Spec.Rsa.primeWords len) ∧
      Arrays B w [aAcc, aTmp] t.mem t'.mem := by
  have hZ := h.hZ
  have hw2 := h.w2
  have hp : Spec.Rsa.primeWords len ≤ w := by unfold Spec.Rsa.primeWords Spec.Rsa.modulusWords; omega
  show WP isa (.seq (.block _) _) t _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (primeW_ok h.good.rdi (h.ld hsl) (by rw [h.hdr sl hsl hsl']; exact hl) h1 (by omega))
    fun u₁ ⟨h12₁, hm₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.rcx, .rdx, .r12] (Q := fun u =>
      u.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.primeWords len) ∧ u.gpr .rdx = 1 ∧
      u.gpr .r12 = BitVec.ofNat 64 w ∧ u.mem = t.mem) (by
    xrun [State.ea, hdr, (k₁.gpr (by decide)).trans h.good.rdi, hdrOff,
      show InRegions (u₁.rd ++ u₁.wr) (off B (8 * sW)) 8 by rw [k₁.2.1, k₁.2.2]; exact h.ld (by decide),
      h.good.hdr.hw, h12₁, hm₁])
    rfl) fun u₂ ⟨⟨hcx₂, hdx₂, h12₂, hm₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hg₂ : Good u₂ B Z w minv :=
    Good.of_arrays h.good (js := []) (fun _ _ => by rw [hm₂]) (k12.mono (by decide)) k12.2.2
  refine WP.mono (setWordW_ok hg₂.scr hg₂.rdi hg₂.hdr hZ h12₂ h.w1 (by omega) (o := aAcc) (by decide)
    (ri := .rcx) (by decide) (by omega) hcx₂) fun t' ⟨hv, ho, k'⟩ => ?_
  have ho' : Outside B (slot w aAcc) (8 * (w + 2)) t.mem t'.mem := by rw [← hm₂]; exact ho
  have a : Arrays B w [aAcc, aTmp] t.mem t'.mem :=
    Arrays.of_outside (j := aAcc) (by simp) ho' (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨h.arr a (by decide) (by decide) (by decide) ((k12.trans k').mono (by decide)), ?_, a⟩
  rw [hv, hdx₂, show (1 : BitVec 64).toNat = 1 from rfl, Nat.one_mul]

end

end VG.Proof.Rsa.X86_64.Key
