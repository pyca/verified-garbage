module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Pieces
public import VerifiedGarbage.Proof.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Div
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: the halvings

A step of the halvings (`twosBody_ok`) is `RecoverDet.twoStep` on `u`
(array 7), `x₂` (array 6) and `x` (wide array 2, narrow 4 and 5), through the
masks of `u` odd and both even (`twosFlags_ok`), a halving unless a mask
(`halfIf_ok`) and a doubling if one (`dblIf_ok`); the count in the header
(`countNext_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.RecoverDet (twoStep)

theorem sx_m1 : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 := by decide

theorem mask_xor1 (c : Bool) : mask c ^^^ BitVec.allOnes 64 = mask (!c) := by cases c <;> decide

theorem mask_or1 (a b : Bool) : mask a ||| mask b = mask (a || b) := by cases a <;> cases b <;> decide

theorem sub_one_ofNat' {c : Nat} (h1 : 1 ≤ c) (hc : c < 2 ^ 64) :
    BitVec.ofNat 64 c - 1#64 = BitVec.ofNat 64 (c - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

theorem beq_zero_sub1 {c : Nat} (h1 : 1 ≤ c) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 (c - 1) == 0) = decide (c = 1) := by
  by_cases e : c = 1
  · subst e; rfl
  · have : BitVec.ofNat 64 (c - 1) ≠ 0 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this
      exact e (by have : (0 : BitVec 64).toNat = 0 := rfl; omega_arith)
    simp only [e, decide_false]
    exact beq_false_of_ne this

theorem sub_one_ofNat {c : Nat} (h1 : 1 ≤ c) (hc : c < 2 ^ 64) :
    BitVec.ofNat 64 c - 1 = BitVec.ofNat 64 (c - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega_arith

/-- `countNext`: the count less one, and `ZF` if it was one. -/
theorem countNext_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {c : Nat}
    (hc : word s.mem B (8 * sCt) = BitVec.ofNat 64 c) (h1 : 1 ≤ c) (hc' : c < 2 ^ 64) :
    WP isa (.block countNext) s fun t => t.zf = some (decide (c = 1)) ∧
      t.mem = s.mem.writeW (off B (8 * sCt)) (BitVec.ofNat 64 (c - 1)) ∧ Keep [.rax] s t := by
  have h256 := h.h256
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (c = 1)) ∧
    t.mem = s.mem.writeW (off B (8 * sCt)) (BitVec.ofNat 64 (c - 1))) ?_ rfl) fun t ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩
  unfold countNext
  xrun [State.ea, hdr, h.rdi, hdrOff, h.scr.ld (d := 8 * sCt) (by simp only [sCt, sFn]; omega_arith),
    h.scr.st (d := 8 * sCt) (by simp only [sCt, sFn]; omega_arith), hc, sub_one_ofNat h1 hc', sub_one_ofNat' h1 hc', beq_zero_sub1 h1 hc',
    show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_sub_beq hc' (show 1 < 2 ^ 64 by decide)]

/-- A block that leaves the mask of `keep` in `rbp`, reading only the header. -/
def MaskPre (B : Addr) (Z : Nat) (m : Mem) (pre : List Instr) (keep : Bool) : Prop :=
  ∀ t : State, Scr t B Z → t.gpr .rdi = B → (∀ i < 32, word t.mem B (8 * i) = word m B (8 * i)) →
    WP isa (.block pre) t fun t' => (t'.gpr .rbp = mask keep ∧ t'.mem = t.mem) ∧ Keep [.rbp] t t'

/-- `rbp := ` a header slot holding a mask. -/
theorem maskLd {B : Addr} {Z : Nat} {m : Mem} {sl : Nat} {c : Bool} (hsl : sl < 32) (hZ : 8 * 32 ≤ Z)
    (hm : word m B (8 * sl) = mask c) : MaskPre B Z m [.mov .rbp (.mem (hdr sl))] c := fun t ht hdi hh =>
  WP.keep [.rbp] (Q := fun t' => t'.gpr .rbp = mask c ∧ t'.mem = t.mem) (by xrun [State.ea, hdr, hdi, hdrOff, ht.ld (d := 8 * sl) (by omega_arith), hh sl hsl, hm]) rfl

/-- `rbp := ` the complement of a header slot holding a mask. -/
theorem maskNot {B : Addr} {Z : Nat} {m : Mem} {sl : Nat} {c : Bool} (hsl : sl < 32) (hZ : 8 * 32 ≤ Z)
    (hm : word m B (8 * sl) = mask c) :
    MaskPre B Z m [.mov .rbp (.mem (hdr sl)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] (!c) :=
  fun t ht hdi hh => WP.keep [.rbp] (Q := fun t' => t'.gpr .rbp = mask (!c) ∧ t'.mem = t.mem) (by
    xrun [State.ea, hdr, hdi, hdrOff, ht.ld (d := 8 * sl) (by omega_arith), hh sl hsl, hm, sx_m1, mask_xor1]) rfl

/-- `rbp := 0`. -/
theorem maskZero {B : Addr} {Z : Nat} {m : Mem} : MaskPre B Z m [.mov32 .rbp (.imm 0)] false := fun t _ _ _ =>
  WP.keep [.rbp] (Q := fun t' => t'.gpr .rbp = mask false ∧ t'.mem = t.mem) (by xrun) rfl

/-- `rbp := -1`. -/
theorem maskOnes {B : Addr} {Z : Nat} {m : Mem} :
    MaskPre B Z m [.mov .rbp (.imm (BitVec.ofInt 32 (-1)))] true := fun t _ _ _ =>
  WP.keep [.rbp] (Q := fun t' => t'.gpr .rbp = mask true ∧ t'.mem = t.mem) (by xrun [sx_m1]) rfl

/-- `[o] := [j] / 2`, for a `[j]` whose word `w` is zero. -/
theorem shrTo_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j o : Nat} (hj : j < 16) (ho : o < 16)
    (hjo : j ≠ o) (hz : word s.mem B (slot w j + 8 * w) = 0) :
    WP isa (.seq (.block (ws ++ base j .r8 ++ base o .rsi)) (wordLoop 0 shrBody)) s fun s' =>
      wv s'.mem B (slot w o) w = wv s.mem B (slot w j) w / 2 ∧ Outside B (slot w o) (8 * w) s.mem s'.mem ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14] s s' := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have so := h.sl ho
  have pj := slot_sep (w := w) hjo
  have hw1 := h.w1
  have hw2 := h.w2
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.mono (base2_ok j o (r₁ := .r8) (r₂ := .rsi) (w := w) (by decide) (by decide) (by decide)
      ((k₁.gpr (by decide)).trans h.rdi) h9 (by decide)) fun s₂ ⟨h8, hsi, m₂, k₂⟩ => ?_))
  refine WP.mono (shr_ok (h.scr.congr (k₁.trans k₂).2.2) hsi h8 ((k₂.gpr (by decide)).trans h12) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨hv, ho', k₃⟩ => ?_
  rw [m₂, m₁, hz] at hv
  rw [m₂, m₁] at ho'
  refine ⟨?_, ho', ((k₁.trans k₂).trans k₃).mono (by simp)⟩
  have e : wv s.mem B (slot w j) w % 2 = (word s.mem B (slot w j)).toNat % 2 := by
    rw [wv_low (by omega_arith)]; omega_arith
  rw [show (0 : BitVec 64).toNat % 2 = 0 from rfl, Nat.mul_zero, Nat.add_zero] at hv
  omega_arith

/-- `[j] := keep ? [j] : [o]` over `w` words, or `2 w + 2` if `wide`, for the
mask `keep` that `pre` leaves. -/
theorem selPre_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (wide : Bool) {j o : Nat}
    (hj : j + (if wide then 2 else 1) ≤ 16) (ho : o + (if wide then 2 else 1) ≤ 16)
    (hjo : slot w j + 8 * shlN wide w ≤ slot w o ∨ slot w o + 8 * shlN wide w ≤ slot w j) {pre : List Instr}
    {keep : Bool} (hpre : MaskPre B Z s.mem pre keep) :
    WP isa (.seq (.block (ws ++ (if wide then wideR else []) ++ base j .r8 ++ base o .rsi ++ pre))
      (wordLoop 0 selBody)) s fun s' =>
      wv s'.mem B (slot w j) (shlN wide w) =
        (if keep then wv s.mem B (slot w j) (shlN wide w) else wv s.mem B (slot w o) (shlN wide w)) ∧
      Outside B (slot w j) (8 * shlN wide w) s.mem s'.mem ∧
      Keep [.r12, .r9, .r8, .rsi, .rbp, .rax, .rdx, .r14] s s' := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have sj : slot w j + 8 * shlN wide w ≤ Z := by
    have := slot_room (w := w) hj
    cases wide <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] at this hj ⊢ <;> omega_arith
  have so : slot w o + 8 * shlN wide w ≤ Z := by
    have := slot_room (w := w) ho
    cases wide <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] at this ho ⊢ <;> omega_arith
  have hN1 : 1 ≤ shlN wide w := by cases wide <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] <;> omega_arith
  have hN2 : shlN wide w < 2 ^ 31 := by
    cases wide <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] <;> omega_arith
  rw [show ws ++ (if wide then wideR else []) ++ base j .r8 ++ base o .rsi ++ pre =
    ws ++ ((if wide then wideR else []) ++ ((base j .r8 ++ base o .rsi) ++ pre)) by simp only [List.append_assoc]]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (wideIf_ok wide h12) fun s₂ ⟨⟨h12₂, m₂⟩, k₂⟩ =>
    WP.block_append_iff.mpr (WP.mono (base2_ok j o (r₁ := .r8) (r₂ := .rsi) (w := w) (by decide) (by decide)
      (by decide) (((k₁.trans k₂).gpr (by decide)).trans h.rdi) ((k₂.gpr (by decide)).trans h9) (by decide))
    fun s₃ ⟨h8, hsi, m₃, k₃⟩ => WP.mono (hpre s₃ (h.scr.congr ((k₁.trans k₂).trans k₃).2.2)
      ((((k₁.trans k₂).trans k₃).gpr (by decide)).trans h.rdi) (fun i _ => by rw [m₃, m₂, m₁]))
    fun s₄ ⟨⟨hbp, m₄⟩, k₄⟩ => ?_))))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  refine WP.mono (sel_ok (h.scr.congr k14.2.2) ((k₄.gpr (by decide)).trans h8) ((k₄.gpr (by decide)).trans hsi) hbp
    ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h12₂)) hN1 hN2 sj so hjo) fun t ⟨hv, ho', k₅⟩ => ?_
  rw [m₄, m₃, m₂, m₁] at hv ho'
  exact ⟨hv, ho', (k14.trans k₅).mono (by simp)⟩

/-- `halfIf j pre`: `[j] := [j] / 2` (through array 14) unless the mask `keep`
that `pre` leaves, for a `[j]` whose word `w` is zero. -/
theorem halfIf_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j : Nat} (hj : j < 14) {pre : List Instr}
    {keep : Bool} (hz : word s.mem B (slot w j + 8 * w) = 0) (hpre : MaskPre B Z s.mem pre keep) :
    WP isa (seqs (halfIf j pre)) s fun s' =>
      wv s'.mem B (slot w j) w = (if keep then wv s.mem B (slot w j) w else wv s.mem B (slot w j) w / 2) ∧
      Frm B [(slot w 14, 8 * w), (slot w j, 8 * w)] s.mem s'.mem ∧
      Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14, .rbp] s s' := by
  have hn := h.scr.nowrap
  have sj := h.sl (j := j) (by omega_arith)
  have pj := slot_sep (w := w) (show j ≠ 14 by omega_arith)
  simp only [halfIf, seqs]
  refine WP.seq (WP.mono (shrTo_ok h (j := j) (o := 14) (by omega_arith) (by decide) (by omega_arith) hz)
    fun s₁ ⟨v₁, o₁, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot w 14 _) k₁ (by decide)
  have vj : wv s₁.mem B (slot w j) w = wv s.mem B (slot w j) w := o₁.wv (by omega_arith) (by omega_arith)
  refine WP.mono (selPre_ok h₁ false (j := j) (o := 14) (by simp only [↓reduceIte, Bool.false_eq_true]; omega_arith)
    (by decide) (by simp only [shlN, ↓reduceIte, Bool.false_eq_true]; omega_arith)
    (fun t ht hdi hh => hpre t ht hdi fun i hi => (hh i hi).trans
      (o₁.word (Or.inl (by have := hdr_lt_slot w 14 hi; omega_arith)) (by omega_arith))))
    fun t ⟨v₂, o₂, k₂⟩ => ?_
  simp only [shlN, ↓reduceIte, Bool.false_eq_true] at v₂ o₂
  refine ⟨by rw [v₂, vj, v₁], fun x hx => ?_, (k₁.trans k₂).mono (by simp)⟩
  have a := hx _ List.mem_cons_self
  have b := hx _ (List.mem_cons_of_mem _ List.mem_cons_self)
  rw [o₂ x b, o₁ x a]

theorem add_ofInt0 (x : BitVec 64) : x + BitVec.ofInt 64 0 = x := by
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]

/-- A number's parity is its low word's. -/
theorem wv_mod2 {m : Mem} {B : Addr} {e w : Nat} (hw : 1 ≤ w) :
    wv m B e w % 2 = (word m B e).toNat % 2 := by
  rw [wv_low hw]; omega_arith

/-- `twosFlags`: the masks of `u` (array 7) odd into `sU`, and of `u` and `x₂`
(array 6) both even into `sB2`. -/
theorem twosFlags_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block twosFlags) s fun t =>
      t.mem = (s.mem.writeW (off B (8 * sU)) (mask (decide (wv s.mem B (slot w 7) w % 2 = 1)))).writeW
        (off B (8 * sB2)) (mask (!(decide (wv s.mem B (slot w 6) w % 2 = 1) ||
          decide (wv s.mem B (slot w 7) w % 2 = 1)))) ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx, .rcx] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have s7 := h.sl (j := 7) (by decide)
  have s6 := h.sl (j := 6) (by decide)
  have hw1 := h.w1
  rw [wv_mod2 (by omega_arith), wv_mod2 (by omega_arith)]
  unfold twosFlags
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (base_ok 7 (r := .rbx) (w := w) (by decide)
      ((k₁.gpr (by decide)).trans h.rdi) h9) fun s₂ ⟨hbx, m₂, k₂⟩ => ?_))
  have hs₂ := h.scr.congr (k₁.trans k₂).2.2
  have hdi₂ : s₂.gpr .rdi = B := ((k₁.trans k₂).gpr (by decide)).trans h.rdi
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rdx = mask (decide ((word s.mem B (slot w 7)).toNat % 2 = 1)) ∧
      t.mem = s.mem.writeW (off B (8 * sU)) (mask (decide ((word s.mem B (slot w 7)).toNat % 2 = 1)))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hbx, at0, add_ofInt0, hs₂.ld (d := slot w 7) (by omega_arith),
      hs₂.st (d := 8 * sU) (by simp only [sU, sFn]; omega_arith), m₂, m₁, mask_low]) rfl) fun s₃ ⟨⟨hdx, m₃⟩, k₃⟩ => ?_
  have hs₃ := hs₂.congr k₃.2.2
  have hdi₃ : s₃.gpr .rdi = B := (k₃.gpr (by decide)).trans hdi₂
  rw [WP.block_append_iff]
  refine WP.mono (base_ok 6 (r := .rbx) (w := w) (by decide) hdi₃ (((k₂.trans k₃).gpr (by decide)).trans h9))
    fun s₄ ⟨hbx₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.congr k₄.2.2
  have hdi₄ : s₄.gpr .rdi = B := (k₄.gpr (by decide)).trans hdi₃
  have hdx₄ : s₄.gpr .rdx = _ := (k₄.gpr (by decide)).trans hdx
  have w6 : word s₄.mem B (slot w 6) = word s.mem B (slot w 6) := by
    rw [m₄, m₃]
    exact (writeW_outside s.mem B _ (d := 8 * sU) (by simp only [sU, sFn]; omega_arith)).word
      (by simp only [sU, sFn]; have := hdr_lt_slot w 6 (show 26 < 32 by decide); omega_arith) (by omega_arith)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = s₄.mem.writeW (off B (8 * sB2))
      (mask (!(decide ((word s.mem B (slot w 6)).toNat % 2 = 1) || decide ((word s.mem B (slot w 7)).toNat % 2 = 1)))))
    (by
      xrun [State.ea, hdr, hdi₄, hdrOff, hbx₄, at0, add_ofInt0,
        hs₄.ld (d := slot w 6) (by omega_arith), hs₄.st (d := 8 * sB2) (by simp only [sB2, sFn]; omega_arith), w6,
        mask_low, hdx₄, mask_or1, sx_m1, mask_xor1]) rfl) fun t ⟨mt, k₅⟩ => ?_
  exact ⟨by rw [mt, m₄, m₃], ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by simp)⟩

/-- `dblIf`: `x := 2 x` (wide array 2 in the narrow layout, `2 w + 2` words,
modulo `2^(64 (2 w + 2))`) if the mask `sB2` is set, through wide array 7. -/
theorem dblIf_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {both : Bool}
    (hb : word s.mem B (8 * sB2) = mask both) :
    WP isa (seqs dblIf) s fun s' =>
      wv s'.mem B (slot w 4) (2 * w + 2) =
        (if both then 2 * wv s.mem B (slot w 4) (2 * w + 2) else wv s.mem B (slot w 4) (2 * w + 2)) %
          2 ^ (64 * (2 * w + 2)) ∧
      Frm B [(slot w 14, 8 * (2 * w + 2)), (slot w 4, 8 * (2 * w + 2))] s.mem s'.mem ∧
      Keep [.r12, .r9, .r15, .rbp, .r10, .r8, .rbx, .rsi, .rax, .rdx, .r14] s s' := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have r4 := slot_room (w := w) (j := 4) (c := 2) (by decide)
  have r14 := slot_room (w := w) (j := 14) (c := 2) (by decide)
  have e14 : slot w 14 = slot w 4 + 10 * (8 * (w + 2)) := slot_add w 4 10
  simp only [dblIf, seqs]
  rw [show ws ++ wideR ++ ([.mov .r15 (.mem (hdr sB2)), .mov32 .rbp (.imm 0)] : List Instr) ++ base 4 .r10 ++
      base 4 .r8 ++ base 14 .rbx = ws ++ (wideR ++ (([.mov .r15 (.mem (hdr sB2)), .mov32 .rbp (.imm 0)] : List Instr) ++
      (base 4 .r10 ++ (base 4 .r8 ++ base 14 .rbx)))) by simp only [List.append_assoc]]
  refine WP.seq (WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (wideIf_ok true h12) fun s₂ ⟨⟨h12₂, m₂⟩, k₂⟩ =>
    WP.block_append_iff.mpr (WP.mono (WP.keep [.r15, .rbp] (Q := fun t => t.gpr .r15 = mask both ∧
      t.gpr .rbp = mask false ∧ t.mem = s₂.mem) (by
        have hdi₂ : s₂.gpr .rdi = B := ((k₁.trans k₂).gpr (by decide)).trans h.rdi
        have hs₂ := h.scr.congr (k₁.trans k₂).2.2
        xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sB2) (by simp only [sB2, sFn]; omega_arith), m₂, m₁, hb])
      rfl) fun s₃ ⟨⟨h15, hbp, m₃⟩, k₃⟩ =>
    WP.mono (base3_ok 4 4 14 (r₁ := .r10) (r₂ := .r8) (r₃ := .rbx) (w := w) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) ((((k₁.trans k₂).trans k₃).gpr (by decide)).trans h.rdi)
      (((k₂.trans k₃).gpr (by decide)).trans h9) (by decide) (by decide)) fun s₄ ⟨h10, h8, hbx, m₄, k₄⟩ => ?_)))))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  refine WP.mono (addM_ok (c := both) (N := 2 * w + 2) (h.scr.congr k14.2.2) hbx h10 h8
    ((k₄.gpr (by decide)).trans h15) ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h12₂))
    ((k₄.gpr (by decide)).trans hbp) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₅ ⟨c', _, hv₅, o₅, k₅⟩ => ?_
  rw [m₄, m₃, m₂, m₁] at hv₅ o₅
  have k15 := k14
  have h₅ : Ws s₅ B Z w := h.congr (Frm.of_outside o₅ (List.mem_singleton_self _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact Mut.ofSlot w 14 _) (k15.trans k₅) (by simp)
  refine WP.mono (selPre_ok h₅ true (j := 4) (o := 14) (by decide) (by decide)
    (by simp only [shlN, ↓reduceIte]; omega_arith) maskZero) fun t ⟨v₆, o₆, k₆⟩ => ?_
  simp only [shlN, ↓reduceIte, Bool.false_eq_true] at v₆ o₆
  refine ⟨?_, fun x hx => ?_, ((k15.trans k₅).trans k₆).mono (by simp)⟩
  · rw [v₆]
    have := wv_lt s₅.mem B (slot w 14) (2 * w + 2)
    have hX := wv_lt s.mem B (slot w 4) (2 * w + 2)
    cases both
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hv₅ ⊢
      rw [Nat.mod_eq_of_lt hX]
      cases c' <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one] at hv₅ <;> omega_arith
    · simp only [↓reduceIte] at hv₅ ⊢
      rw [show 2 * wv s.mem B (slot w 4) (2 * w + 2) = wv s₅.mem B (slot w 14) (2 * w + 2) +
        2 ^ (64 * (2 * w + 2)) * c'.toNat by omega_arith, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this]
  · have a := hx _ List.mem_cons_self
    have b := hx _ (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [o₆ x b, o₅ x a]

/-! ## The loop -/

/-- What the halvings change: wide array 2, arrays 6 and 7 but their two top
words, wide array 7 and the header slots 25 to 27. -/
def TwosP (w y : Nat) : Prop :=
  (slot w 4 ≤ y ∧ y < slot w 4 + 8 * (2 * w + 2)) ∨ (slot w 6 ≤ y ∧ y < slot w 6 + 8 * w) ∨
    (slot w 7 ≤ y ∧ y < slot w 7 + 8 * w) ∨ (slot w 14 ≤ y ∧ y < slot w 14 + 8 * (2 * w + 2)) ∨
    (200 ≤ y ∧ y < 224)

/-- The registers the halvings change. -/
abbrev twosClob : List Reg := [.r12, .r9, .rbx, .rax, .rdx, .rcx, .r8, .rsi, .r14, .rbp, .r15, .r10]

/-- After `j` steps of the halvings from `s₀`, with `st` the values of
`u`, `x₂` and `x` there. -/
structure TwosInv (s₀ : State) (B : Addr) (Z w : Nat) (st : Nat × Nat × Nat) (j : Nat) (t : State) : Prop where
  ws : Ws t B Z w
  frm : FrmP B (TwosP w) s₀.mem t.mem
  keep : Keep twosClob s₀ t
  ct : word t.mem B (8 * sCt) = BitVec.ofNat 64 (64 * w - j)
  val : (wv t.mem B (slot w 7) w, wv t.mem B (slot w 6) w, wv t.mem B (slot w 4) (2 * w + 2)) =
    (twoStep (64 * (2 * w + 2)))^[j] st

macro "tw_omega" : tactic => `(tactic| (simp only [TwosP, DOk, Bignum.slot, hdrBytes, sU, sB2, sCt, sFn]; omega_arith))

/-- `twoStep` by the masks of the code. -/
theorem twoStep_eq {b U X X3 : Nat} (hX3 : X3 < 2 ^ b) : twoStep b (U, X, X3) =
    (if decide (U % 2 = 1) then U else U / 2, if (decide (X % 2 = 1) || decide (U % 2 = 1)) then X else X / 2,
      (if !(decide (X % 2 = 1) || decide (U % 2 = 1)) then 2 * X3 else X3) % 2 ^ b) := by
  unfold twoStep
  rcases Nat.mod_two_eq_zero_or_one U with hu | hu <;> rcases Nat.mod_two_eq_zero_or_one X with hx | hx <;>
    simp [hu, hx, Nat.mod_eq_of_lt hX3]

/-- A step of the halvings is `twoStep`. -/
theorem twosStep_ok {s₀ t : State} {B : Addr} {Z w : Nat} {st : Nat × Nat × Nat} {j : Nat}
    (hI : TwosInv s₀ B Z w st j t) (hj : j < 64 * w) (z7 : word s₀.mem B (slot w 7 + 8 * w) = 0)
    (z6 : word s₀.mem B (slot w 6 + 8 * w) = 0) :
    WP isa twosBody t fun t' => t'.zf = some (decide (j + 1 = 64 * w)) ∧ TwosInv s₀ B Z w st (j + 1) t' := by
  have h := hI.ws
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have r16 : slot w 14 + 8 * (2 * w + 2) ≤ slot w 16 := by simp only [slot, hdrBytes]; omega_arith
  have hZ' : 256 + 16 * (8 * (w + 2)) ≤ Z := hZ
  have z7t : word t.mem B (slot w 7 + 8 * w) = 0 := by
    rw [hI.frm.word_eq (fun y => by tw_omega) (by tw_omega)]; exact z7
  have z6t : word t.mem B (slot w 6 + 8 * w) = 0 := by
    rw [hI.frm.word_eq (fun y => by tw_omega) (by tw_omega)]; exact z6
  generalize hU : wv t.mem B (slot w 7) w = U
  generalize hX : wv t.mem B (slot w 6) w = X
  generalize hX3 : wv t.mem B (slot w 4) (2 * w + 2) = X3
  have hval := hI.val
  rw [hU, hX, hX3] at hval
  unfold twosBody
  simp only [List.cons_append, List.nil_append]
  -- The flags.
  refine wp_seqs_append (a := [.block twosFlags]) (by simp) (by simp [halfIf]) ?_
  simp only [seqs]
  refine WP.mono (twosFlags_ok h) fun t₁ ⟨m₁, k₁⟩ => ?_
  rw [hU, hX] at m₁
  have f₁ : FrmP B (fun y => 208 ≤ y ∧ y < 224) t.mem t₁.mem := by
    rw [m₁]; exact (FrmP.of_writeW _ (by tw_omega) (fun y => by tw_omega)).trans
      (FrmP.of_writeW _ (by tw_omega) (fun y => by tw_omega))
  have h₁ : Ws t₁ B Z w := h.congrP f₁ (fun y => by tw_omega) k₁ (by simp)
  have hhdr₁ : ∀ i < 32, i ≠ sU → i ≠ sB2 → word t₁.mem B (8 * i) = word t.mem B (8 * i) := fun i hi h1 h2 => by
    rw [m₁, (writeW_outside _ B _ (d := 8 * sB2) (by tw_omega)).word (by simp only [sB2, sFn] at h2 ⊢; omega_arith)
      (by omega_arith), (writeW_outside _ B _ (d := 8 * sU) (by tw_omega)).word
      (by simp only [sU, sFn] at h1 ⊢; omega_arith) (by omega_arith)]
  have hsU : word t₁.mem B (8 * sU) = mask (decide (U % 2 = 1)) := by
    rw [m₁, (writeW_outside _ B _ (d := 8 * sB2) (by tw_omega)).word (by tw_omega) (by tw_omega), word_writeW_self]
  have hsB : word t₁.mem B (8 * sB2) = mask (!(decide (X % 2 = 1) || decide (U % 2 = 1))) := by
    rw [m₁, word_writeW_self]
  have u₁ : wv t₁.mem B (slot w 7) w = U := by rw [f₁.wv_eq (fun y => by tw_omega) (by tw_omega), hU]
  have x₁ : wv t₁.mem B (slot w 6) w = X := by rw [f₁.wv_eq (fun y => by tw_omega) (by tw_omega), hX]
  have x3₁ : wv t₁.mem B (slot w 4) (2 * w + 2) = X3 := by
    rw [f₁.wv_eq (fun y => by tw_omega) (by tw_omega), hX3]
  have z7₁ : word t₁.mem B (slot w 7 + 8 * w) = 0 := by
    rw [f₁.word_eq (fun y => by tw_omega) (by tw_omega)]; exact z7t
  have z6₁ : word t₁.mem B (slot w 6 + 8 * w) = 0 := by
    rw [f₁.word_eq (fun y => by tw_omega) (by tw_omega)]; exact z6t
  -- `u := u / 2` unless it is odd.
  refine wp_seqs_append (by simp [halfIf]) (by simp) (WP.mono (halfIf_ok h₁ (j := 7) (by decide)
    z7₁ (maskLd (by decide) h256 hsU)) fun t₂ ⟨u₂, f₂', k₂⟩ => ?_)
  rw [u₁] at u₂
  have f₂ : FrmP B (fun y => (slot w 14 ≤ y ∧ y < slot w 14 + 8 * w) ∨ (slot w 7 ≤ y ∧ y < slot w 7 + 8 * w))
      t₁.mem t₂.mem := FrmP.of_frm2 f₂'
  have h₂ : Ws t₂ B Z w := h₁.congrP f₂ (fun y => by tw_omega) k₂ (by simp)
  have x₂ : wv t₂.mem B (slot w 6) w = X := by rw [f₂.wv_eq (fun y => by tw_omega) (by tw_omega), x₁]
  have x3₂ : wv t₂.mem B (slot w 4) (2 * w + 2) = X3 := by
    rw [f₂.wv_eq (fun y => by tw_omega) (by tw_omega), x3₁]
  have z6₂ : word t₂.mem B (slot w 6 + 8 * w) = 0 := by
    rw [f₂.word_eq (fun y => by tw_omega) (by tw_omega)]; exact z6₁
  have hsB₂ : word t₂.mem B (8 * sB2) = mask (!(decide (X % 2 = 1) || decide (U % 2 = 1))) := by
    rw [f₂.word_eq (fun y => by tw_omega) (by tw_omega)]; exact hsB
  -- `x₂ := x₂ / 2` if both are even.
  refine wp_seqs_append (by simp [halfIf]) (by simp) (WP.mono (halfIf_ok h₂ (j := 6) (by decide)
    z6₂ (maskNot (by decide) h256 hsB₂)) fun t₃ ⟨x₃, f₃', k₃⟩ => ?_)
  rw [x₂, Bool.not_not] at x₃
  have f₃ : FrmP B (fun y => (slot w 14 ≤ y ∧ y < slot w 14 + 8 * w) ∨ (slot w 6 ≤ y ∧ y < slot w 6 + 8 * w))
      t₂.mem t₃.mem := FrmP.of_frm2 f₃'
  have h₃ : Ws t₃ B Z w := h₂.congrP f₃ (fun y => by tw_omega) k₃ (by simp)
  have u₃ : wv t₃.mem B (slot w 7) w = (if decide (U % 2 = 1) then U else U / 2) := by rw [f₃.wv_eq (fun y => by tw_omega) (by tw_omega), u₂]
  have x3₃ : wv t₃.mem B (slot w 4) (2 * w + 2) = X3 := by
    rw [f₃.wv_eq (fun y => by tw_omega) (by tw_omega), x3₂]
  have hsB₃ : word t₃.mem B (8 * sB2) = mask (!(decide (X % 2 = 1) || decide (U % 2 = 1))) := by
    rw [f₃.word_eq (fun y => by tw_omega) (by tw_omega)]; exact hsB₂
  -- `x := 2 x` if both are even.
  refine wp_seqs_append (by simp [dblIf]) (by simp) (WP.mono (dblIf_ok h₃ hsB₃) fun t₄ ⟨x3₄, f₄', k₄⟩ => ?_)
  rw [x3₃] at x3₄
  have f₄ : FrmP B (fun y => (slot w 14 ≤ y ∧ y < slot w 14 + 8 * (2 * w + 2)) ∨
      (slot w 4 ≤ y ∧ y < slot w 4 + 8 * (2 * w + 2))) t₃.mem t₄.mem := FrmP.of_frm2 f₄'
  have h₄ : Ws t₄ B Z w := h₃.congrP f₄ (fun y => by tw_omega) k₄ (by simp)
  have u₄ : wv t₄.mem B (slot w 7) w = (if decide (U % 2 = 1) then U else U / 2) := by rw [f₄.wv_eq (fun y => by tw_omega) (by tw_omega), u₃]
  have x₄ : wv t₄.mem B (slot w 6) w =
      (if (decide (X % 2 = 1) || decide (U % 2 = 1)) then X else X / 2) := by rw [f₄.wv_eq (fun y => by tw_omega) (by tw_omega), x₃]
  -- The count.
  have hct : word t₄.mem B (8 * sCt) = BitVec.ofNat 64 (64 * w - j) := by
    rw [f₄.word_eq (fun y => by tw_omega) (by tw_omega), f₃.word_eq (fun y => by tw_omega)
      (by tw_omega), f₂.word_eq (fun y => by tw_omega) (by tw_omega),
      f₁.word_eq (fun y => by tw_omega) (by tw_omega)]; exact hI.ct
  simp only [seqs]
  refine WP.mono (countNext_ok h₄ hct (by omega_arith) (by omega_arith)) fun t₅ ⟨hz, m₅, k₅⟩ => ⟨?_, ?_⟩
  · rw [hz]; congr 1; simp only [decide_eq_decide]; omega_arith
  have f₅ : FrmP B (fun y => 200 ≤ y ∧ y < 208) t₄.mem t₅.mem := by
    rw [m₅]; exact FrmP.of_writeW _ (by tw_omega) (fun y => by tw_omega)
  have kk := ((((hI.keep.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅
  refine ⟨h₄.congrP f₅ (fun y => by tw_omega) k₅ (by simp),
    ((((hI.frm.trans (f₁.mono fun y => by tw_omega)).trans (f₂.mono fun y => by tw_omega)).trans
      (f₃.mono fun y => by tw_omega)).trans (f₄.mono fun y => by tw_omega)).trans (f₅.mono fun y => by tw_omega),
    kk.mono (by simp), by rw [m₅, word_writeW_self, Nat.sub_sub], ?_⟩
  have hX3lt : X3 < 2 ^ (64 * (2 * w + 2)) := hX3 ▸ wv_lt _ _ _ _
  rw [Function.iterate_succ_apply', ← hval, twoStep_eq hX3lt,
    f₅.wv_eq (fun y => by tw_omega) (by tw_omega), f₅.wv_eq (fun y => by tw_omega) (by tw_omega),
    f₅.wv_eq (fun y => by tw_omega) (by tw_omega), u₄, x₄, x3₄]

end VG.Proof.Rsa.X86_64.Rd

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.RecoverDet (twoStep)

/-- The halvings: `64 w` steps of `twoStep` from `u`, `x₂` and `x`, with the
count `64 w` in the header and the top words of `u` and `x₂` zero. -/
theorem twosLoop_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    (hct : word s.mem B (8 * sCt) = BitVec.ofNat 64 (64 * w)) (z7 : word s.mem B (slot w 7 + 8 * w) = 0)
    (z6 : word s.mem B (slot w 6 + 8 * w) = 0) :
    WP isa (.loop twosBody .ne) s fun t => TwosInv s B Z w
      (wv s.mem B (slot w 7) w, wv s.mem B (slot w 6) w, wv s.mem B (slot w 4) (2 * w + 2)) (64 * w) t := by
  have hw1 := h.w1
  exact wp_upto (a := 0) (N := 64 * w) (by omega_arith) _ (fun j _ hj t hI => twosStep_ok hI hj z7 z6)
    (fun _ h => h) ⟨h, FrmP.refl _ _ _, Keep.refl _ _, by rw [Nat.sub_zero]; exact hct, rfl⟩

end VG.Proof.Rsa.X86_64.Rd
