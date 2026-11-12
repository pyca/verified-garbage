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

The masks that a block leaves in `rbp` (`MaskPre`), a selection over an
array by one (`selPre_ok`), a halving into another array (`shrTo_ok`) and the
count in the header (`countNext_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Proof.Rsa.RecoverDet (twoStep)

theorem sx_m1 : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 := by decide

theorem mask_xor1 (c : Bool) : mask c ^^^ BitVec.allOnes 64 = mask (!c) := by cases c <;> decide

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

/-- `rbp := 0`. -/
theorem maskZero {B : Addr} {Z : Nat} {m : Mem} : MaskPre B Z m [.mov32 .rbp (.imm 0)] false := fun t _ _ _ =>
  WP.keep [.rbp] (Q := fun t' => t'.gpr .rbp = mask false ∧ t'.mem = t.mem) (by xrun) rfl

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

theorem add_ofInt0 (x : BitVec 64) : x + BitVec.ofInt 64 0 = x := by
  rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]

/-- A doubling with a carry in and out. -/
theorem dbl_val {X X' c₀ P : Nat} {c : Bool} (h : X' + P * c.toNat = 2 * X + c₀) (hX' : X' < P) :
    X' = (2 * X + c₀) % P ∧ c.toNat = (2 * X + c₀) / P := by
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX', Nat.add_mul_div_left _ _ (by omega_arith),
    Nat.div_eq_of_lt hX']
  exact ⟨rfl, by omega_arith⟩

/-- The carry in of a doubling, from a mask in a header slot. -/
theorem shlPre_mask {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {pre : List Instr} {c : Bool}
    (hm : MaskPre B Z s.mem pre c) :
    ∀ t : State, t.mem = s.mem → t.gpr .rbp = s.gpr .rbp → t.gpr .rdi = s.gpr .rdi → t.rd = s.rd → t.wr = s.wr →
      WP isa (.block pre) t fun t' => (t'.gpr .rbp = mask c ∧ t'.mem = t.mem) ∧ Keep [.rbp] t t' :=
  fun t hm' _ hdi _ hw => hm t (h.scr.congr hw) (hdi.trans h.rdi) fun i _ => by rw [hm']

end VG.Proof.Rsa.X86_64.Rd
