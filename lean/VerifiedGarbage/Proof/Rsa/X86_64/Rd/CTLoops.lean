module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTParts
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTParts
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time, the loops

The halvings (`twosLoop_ct`) and the square root (`sqrtLoop_ct`): `64 v`
and `64 (v + 1)` steps, their count in the header (`Fn`), each step's
pieces leaking the same in two runs whatever the count (`FB`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-! ## Frames of pieces whose lemmas assume more -/

/-- `[o] := [j] / 2`, for what it changes. -/
theorem shrTo_frm {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j o : Nat} (hj : j < 16) (ho : o < 16)
    (hjo : j ≠ o) :
    WP isa (.seq (.block (ws ++ base j .r8 ++ base o .rsi)) (wordLoop 0 shrBody)) s fun s' =>
      Outside B (slot w o) (8 * w) s.mem s'.mem ∧ Keep [.r12, .r9, .r8, .rsi, .rax, .rdx, .r14] s s' := by
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
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨_, ho', k₃⟩ => ?_
  rw [m₂, m₁] at ho'
  exact ⟨ho', ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- `dblIf`'s first loop, `[14] := [4] + (both ? [4] : 0)` over `2 w + 2`
words, for what it changes. -/
theorem dbl1_frm {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {both : Bool}
    (hb : word s.mem B (8 * sB2) = mask both) :
    WP isa (.seq (.block (ws ++ wideR ++ ([.mov .r15 (.mem (hdr sB2)), .mov32 .rbp (.imm 0)] : List Instr) ++
      base 4 .r10 ++ base 4 .r8 ++ base 14 .rbx)) (wordLoop 0 addMBody)) s fun t =>
      Outside B (slot w 14) (8 * (2 * w + 2)) s.mem t.mem ∧
      Keep [.r12, .r9, .r15, .rbp, .r10, .r8, .rbx, .rsi, .rax, .rdx, .r14] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  have r4 := slot_room (w := w) (j := 4) (c := 2) (by decide)
  have r14 := slot_room (w := w) (j := 14) (c := 2) (by decide)
  have e14 : slot w 14 = slot w 4 + 10 * (8 * (w + 2)) := slot_add w 4 10
  rw [show ws ++ wideR ++ ([.mov .r15 (.mem (hdr sB2)), .mov32 .rbp (.imm 0)] : List Instr) ++ base 4 .r10 ++
      base 4 .r8 ++ base 14 .rbx = ws ++ (wideR ++ (([.mov .r15 (.mem (hdr sB2)), .mov32 .rbp (.imm 0)] : List Instr) ++
      (base 4 .r10 ++ (base 4 .r8 ++ base 14 .rbx)))) by simp only [List.append_assoc]]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (wideIf_ok true h12) fun s₂ ⟨⟨h12₂, m₂⟩, k₂⟩ =>
    WP.block_append_iff.mpr (WP.mono (WP.keep [.r15, .rbp] (Q := fun t => t.gpr .r15 = mask both ∧
      t.gpr .rbp = mask false ∧ t.mem = s₂.mem) (by
        have hdi₂ : s₂.gpr .rdi = B := ((k₁.trans k₂).gpr (by decide)).trans h.rdi
        have hs₂ := h.scr.congr (k₁.trans k₂).2.2
        xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sB2) (by simp only [sB2, sFn]; omega_arith), m₂, m₁, hb])
      rfl) fun s₃ ⟨⟨h15, hbp, m₃⟩, k₃⟩ =>
    WP.mono (base3_ok 4 4 14 (r₁ := .r10) (r₂ := .r8) (r₃ := .rbx) (w := w) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) ((((k₁.trans k₂).trans k₃).gpr (by decide)).trans h.rdi)
      (((k₂.trans k₃).gpr (by decide)).trans h9) (by decide) (by decide)) fun s₄ ⟨h10, h8, hbx, m₄, k₄⟩ => ?_))))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  refine WP.mono (addM_ok (c := both) (N := 2 * w + 2) (h.scr.congr k14.2.2) hbx h10 h8
    ((k₄.gpr (by decide)).trans h15) ((k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans h12₂))
    ((k₄.gpr (by decide)).trans hbp) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₅ ⟨c', _, _, o₅, k₅⟩ => ?_
  rw [m₄, m₃, m₂, m₁] at o₅
  exact ⟨o₅, (k14.trans k₅).mono (by simp)⟩

/-! ## The count and the masks of a step -/

/-- The count, some number from 1. -/
def FB (I : RpIn) (s : State) : Prop :=
  ∃ c, 1 ≤ c ∧ c < 2 ^ 64 ∧ word s.mem I.B (8 * sCt) = BitVec.ofNat 64 c

/-- The count, `n` of the public data. -/
def Fn (n : RpP → Nat) (I : RpIn) (s : State) : Prop := word s.mem I.B (8 * sCt) = BitVec.ofNat 64 (n (pubD I))

theorem stab_FB {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 200 ∨ 208 ≤ y) : Stab FB Q :=
  fun I s t P ⟨c, a, b, e⟩ hf hP h1 h2 => ⟨c, a, b, stab_hdr (i := sCt) (by decide) (fun _ => BitVec.ofNat 64 c)
    (fun y hy => by have := hQ y hy; simp only [sCt, sFn]; omega_arith) I s t P e hf hP h1 h2⟩

theorem stab_Fn (n : RpP → Nat) {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 200 ∨ 208 ≤ y) : Stab (Fn n) Q :=
  stab_hdr (i := sCt) (by decide) (fun I => BitVec.ofNat 64 (n (pubD I)))
    (fun y hy => by have := hQ y hy; simp only [sCt, sFn]; omega_arith)

theorem Fn.fb {n : RpP → Nat} {I : RpIn} {s : State} (h : Fn n I s) (h1 : 1 ≤ n (pubD I))
    (h2 : n (pubD I) < 2 ^ 64) : FB I s := ⟨_, h1, h2, h⟩

/-- The masks of a halving step. -/
def MU (I : RpIn) (s : State) : Prop :=
  (∃ a, word s.mem I.B (8 * sU) = mask a) ∧ ∃ b, word s.mem I.B (8 * sB2) = mask b

theorem stab_MU {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 208 ∨ 224 ≤ y) : Stab MU Q :=
  fun I s t P ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hf hP h1 h2 =>
    ⟨⟨a, stab_hdr (i := sU) (by decide) (fun _ => mask a)
      (fun y hy => by have := hQ y hy; simp only [sU, sFn]; omega_arith) I s t P ha hf hP h1 h2⟩,
     ⟨b, stab_hdr (i := sB2) (by decide) (fun _ => mask b)
      (fun y hy => by have := hQ y hy; simp only [sB2, sFn]; omega_arith) I s t P hb hf hP h1 h2⟩⟩

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

theorem twosFlags_gd (hF : Stab F fun y => 208 ≤ y ∧ y < 224) (p : RpP) (s : State) (h : GD w F p s) :
    WP isa (.block twosFlags) s (GD w (fun I s => F I s ∧ MU I s) p) := by
  have hw := h.ws
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (twosFlags_ok hw) fun t ⟨hm, k⟩ => ?_
  have hf : FrmP p.B (fun y => 208 ≤ y ∧ y < 224) s.mem t.mem := by
    rw [hm]
    exact (FrmP.of_writeW _ (by simp only [sU, sFn]; omega_arith) fun y h1 h2 => by
      simp only [sU, sFn] at h1 h2; omega_arith).trans
      (FrmP.of_writeW _ (by simp only [sB2, sFn]; omega_arith) fun y h1 h2 => by
        simp only [sB2, sFn] at h1 h2; omega_arith)
  refine h.next hf (fun y hy => ⟨by unfold DOk; omega_arith, by omega_arith⟩) k (by decide)
    (fun c hc => ⟨c, (hf.word_eq (fun y h1 h2 hy => by
      simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith)
      (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith)).trans hc⟩) fun I e hFI => ?_
  subst e
  have hZI : 8 * 32 ≤ I.Z := h256
  have hnI : I.B.toNat + I.Z ≤ 2 ^ 64 := hn
  have hm' : t.mem = (s.mem.writeW (off I.B (8 * sU)) (mask (decide (wv s.mem I.B (slot (w I.k) 7) (w I.k) % 2 = 1)))).writeW
      (off I.B (8 * sB2)) (mask (!(decide (wv s.mem I.B (slot (w I.k) 6) (w I.k) % 2 = 1) ||
        decide (wv s.mem I.B (slot (w I.k) 7) (w I.k) % 2 = 1)))) := hm
  refine ⟨hF I s t _ hFI hf (fun y hy => ⟨hy, by omega_arith⟩) k.2.1 k.2.2,
    ⟨decide (wv s.mem I.B (slot (w I.k) 7) (w I.k) % 2 = 1), ?_⟩,
    ⟨!(decide (wv s.mem I.B (slot (w I.k) 6) (w I.k) % 2 = 1) ||
      decide (wv s.mem I.B (slot (w I.k) 7) (w I.k) % 2 = 1)), ?_⟩⟩
  · rw [hm', (writeW_outside _ I.B _ (d := 8 * sB2) (by simp only [sB2, sFn]; omega_arith)).word
      (by simp only [sU, sB2, sFn]; omega_arith) (by simp only [sU, sFn]; omega_arith), word_writeW_self]
  · rw [hm', word_writeW_self]

theorem twosFlags_eq : twosFlags = ws ++ (base 7 .rbx ++ (([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1),
    .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .store (hdr sU) .rdx] : List Instr) ++ (base 6 .rbx ++
    ([.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rax),
    .alu .or .rcx (.reg .rdx), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1))), .store (hdr sB2) .rcx] : List Instr)))) := by
  simp only [twosFlags, List.append_assoc]

theorem twosFlags_ct (hF : Stab F fun y => 208 ≤ y ∧ y < 224) :
    RelCT isa (Two (GD w F)) (.block twosFlags) (Two (GD w fun I s => F I s ∧ MU I s)) := by
  rw [twosFlags_eq]
  exact wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => by
    rw [← twosFlags_eq]; exact twosFlags_gd hF p s h

theorem shrTo_gd {j o : Nat} (hj : j < 16) (ho : o < 16) (hjo : j ≠ o) (hF : Arr F) (p : RpP) (s : State)
    (h : GD w F p s) : WP isa (.seq (.block (ws ++ base j .r8 ++ base o .rsi)) (wordLoop 0 shrBody)) s (GD w F p) :=
  WP.mono (shrTo_frm h.ws hj ho hjo) fun _ ⟨o', k⟩ =>
    h.out o' (slot_256 _ _) (by have := slot_Z h ho; omega_arith) k (by decide) hF

theorem shrTo_ct {j o : Nat} (hj : j < 16) (ho : o < 16) (hjo : j ≠ o) (hF : Arr F)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8 ++ base o .rsi))
      (wordLoop 0 shrBody)) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (.seq (.block (ws ++ base j .r8 ++ base o .rsi)) (wordLoop 0 shrBody)) (Two (GD w F)) := by
  rw [List.append_assoc]
  exact wsG_ct (fun _ _ h => h) ht fun p s h => by rw [← List.append_assoc]; exact shrTo_gd hj ho hjo hF p s h

theorem selN_gd {j o : Nat} (hj : j < 16) (ho : o < 16) (hjo : j ≠ o) {pre : List Instr} (hF : Arr F)
    (hpre : ∀ p s, GD w F p s → ∃ keep, MaskPre p.B p.Z s.mem pre keep) (p : RpP) (s : State) (h : GD w F p s) :
    WP isa (.seq (.block (ws ++ base j .r8 ++ base o .rsi ++ pre)) (wordLoop 0 selBody)) s (GD w F p) :=
  sel_gd (fun _ _ h => h) false (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_arith)
    (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_arith)
    (fun w => by have := slot_sep (w := w) hjo; simp only [shlN, Bool.false_eq_true, ↓reduceIte]; omega_arith)
    hF hpre p s h

theorem selN_ct {j o : Nat} (hj : j < 16) (ho : o < 16) (hjo : j ≠ o) {pre : List Instr} (hF : Arr F)
    (hpre : ∀ p s, GD w F p s → ∃ keep, MaskPre p.B p.Z s.mem pre keep) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8 ++ (base o .rsi ++ pre)))
      (wordLoop 0 selBody)) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (.seq (.block (ws ++ base j .r8 ++ base o .rsi ++ pre)) (wordLoop 0 selBody))
      (Two (GD w F)) := by
  rw [List.append_assoc, List.append_assoc]
  exact wsG_ct (fun _ _ h => h) ht fun p s h => by
    rw [← List.append_assoc, ← List.append_assoc]; exact selN_gd hj ho hjo hF hpre p s h

theorem selW_gd {j o : Nat} (hj : j + 2 ≤ 16) (ho : o + 2 ≤ 16)
    (hjo : ∀ w, slot w j + 8 * (2 * w + 2) ≤ slot w o ∨ slot w o + 8 * (2 * w + 2) ≤ slot w j) {pre : List Instr}
    (hF : Arr F) (hpre : ∀ p s, GD w F p s → ∃ keep, MaskPre p.B p.Z s.mem pre keep) (p : RpP) (s : State)
    (h : GD w F p s) :
    WP isa (.seq (.block (ws ++ wideR ++ base j .r8 ++ base o .rsi ++ pre)) (wordLoop 0 selBody)) s (GD w F p) :=
  sel_gd (fun _ _ h => h) true (by simp only [↓reduceIte]; omega_arith) (by simp only [↓reduceIte]; omega_arith)
    (fun w => by simp only [shlN, ↓reduceIte]; exact hjo w) hF hpre p s h

theorem selW_ct {j o : Nat} (hj : j + 2 ≤ 16) (ho : o + 2 ≤ 16)
    (hjo : ∀ w, slot w j + 8 * (2 * w + 2) ≤ slot w o ∨ slot w o + 8 * (2 * w + 2) ≤ slot w j) {pre : List Instr}
    (hF : Arr F) (hpre : ∀ p s, GD w F p s → ∃ keep, MaskPre p.B p.Z s.mem pre keep)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (wideR ++ (base j .r8 ++ (base o .rsi ++ pre))))
      (wordLoop 0 selBody)) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (.seq (.block (ws ++ wideR ++ base j .r8 ++ base o .rsi ++ pre)) (wordLoop 0 selBody))
      (Two (GD w F)) := by
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  exact wsG_ct (fun _ _ h => h) ht fun p s h => by
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc]; exact selW_gd hj ho hjo hF hpre p s h

theorem dbl1_gd (hF : Arr F) (hb : ∀ p s, GD w F p s → ∃ b, word s.mem p.B (8 * sB2) = mask b) (p : RpP)
    (s : State) (h : GD w F p s) :
    WP isa (.seq (.block (ws ++ wideR ++ ([.mov .r15 (.mem (hdr sB2)), .mov32 .rbp (.imm 0)] : List Instr) ++
      base 4 .r10 ++ base 4 .r8 ++ base 14 .rbx)) (wordLoop 0 addMBody)) s (GD w F p) := by
  obtain ⟨b, hb⟩ := hb p s h
  have r14 := slot_room (w := w p.k) (j := 14) (c := 2) (by decide)
  have hZ := h.ws.hZ
  exact WP.mono (dbl1_frm h.ws hb) fun _ ⟨o, k⟩ => h.out o (slot_256 _ _) (by omega_arith) k (by decide) hF

theorem dbl1_ct (hF : Arr F) (hb : ∀ p s, GD w F p s → ∃ b, word s.mem p.B (8 * sB2) = mask b) :
    RelCT isa (Two (GD w F)) (.seq (.block (ws ++ wideR ++ ([.mov .r15 (.mem (hdr sB2)), .mov32 .rbp (.imm 0)] :
      List Instr) ++ base 4 .r10 ++ base 4 .r8 ++ base 14 .rbx)) (wordLoop 0 addMBody)) (Two (GD w F)) := by
  rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  exact wsG_ct (fun _ _ h => h) (by taint_decide) fun p s h => by
    rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc]
    exact dbl1_gd hF hb p s h

theorem countNext_ct : RelCT isa (Two (GD w F)) (.block countNext) fun _ _ => True :=
  two_taint [.rdi] pins_GD (by taint_decide)

/-- `countNext`: the count less one, and `ZF` if it was one. -/
theorem countNext_gd (n : RpP → Nat) {G : RpIn → State → Prop} (p : RpP) (s : State)
    (h : GD w (fun I s => Fn n I s ∧ G I s) p s) (h1 : 1 ≤ n p) (h2 : n p < 2 ^ 64) :
    WP isa (.block countNext) s fun t => t.zf = some (decide (n p = 1)) ∧ GD w (Fn fun q => n q - 1) p t := by
  obtain ⟨I, m₀, e, h', L, O, he, hm, hc, -⟩ := id h
  subst e
  have h256 := h'.ws.h256
  refine WP.mono (countNext_ok h'.ws hc h1 h2) fun t ⟨hz, hm', k⟩ => ⟨hz, ?_⟩
  refine h.hdrW hm' (by unfold DOk; simp only [sCt, sFn]; omega_arith) (by decide) k (by decide)
    (fun e => absurd e (by decide)) fun J e _ => ?_
  have eB : J.B = I.B := congrArg RpP.B e
  simp only [Fn]
  rw [e, eB, hm', word_writeW_self]

end

/-! ## The halvings -/

theorem twosBody_eq : twosBody = seqs [.block twosFlags,
    .seq (.block (ws ++ base 7 .r8 ++ base 14 .rsi)) (wordLoop 0 shrBody),
    .seq (.block (ws ++ base 7 .r8 ++ base 14 .rsi ++ ([.mov .rbp (.mem (hdr sU))] : List Instr))) (wordLoop 0 selBody),
    .seq (.block (ws ++ base 6 .r8 ++ base 14 .rsi)) (wordLoop 0 shrBody),
    .seq (.block (ws ++ base 6 .r8 ++ base 14 .rsi ++ ([.mov .rbp (.mem (hdr sB2)),
      .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] : List Instr))) (wordLoop 0 selBody),
    .seq (.block (ws ++ wideR ++ ([.mov .r15 (.mem (hdr sB2)), .mov32 .rbp (.imm 0)] : List Instr) ++ base 4 .r10 ++
      base 4 .r8 ++ base 14 .rbx)) (wordLoop 0 addMBody),
    .seq (.block (ws ++ wideR ++ base 4 .r8 ++ base 14 .rsi ++ ([.mov32 .rbp (.imm 0)] : List Instr)))
      (wordLoop 0 selBody),
    .block countNext] := rfl

section
variable {F : RpIn → State → Prop}

theorem mu_arr (hF : Arr F) : Arr fun I s => F I s ∧ MU I s :=
  hF.and (stab_MU fun y hy => .inr (by omega_arith))

theorem mu_sU {p : RpP} {s : State} (h : GD nv (fun I s => F I s ∧ MU I s) p s) :
    ∃ keep, MaskPre p.B p.Z s.mem [.mov .rbp (.mem (hdr sU))] keep := by
  obtain ⟨I, m₀, rfl, h', -, -, -, -, -, ⟨a, ha⟩, -⟩ := h
  exact ⟨a, maskLd (by decide) h'.ws.h256 ha⟩

theorem mu_sB2 {p : RpP} {s : State} (h : GD nv (fun I s => F I s ∧ MU I s) p s) :
    ∃ keep, MaskPre p.B p.Z s.mem [.mov .rbp (.mem (hdr sB2)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] keep := by
  obtain ⟨I, m₀, rfl, h', -, -, -, -, -, -, ⟨b, hb⟩⟩ := h
  exact ⟨!b, maskNot (by decide) h'.ws.h256 hb⟩

theorem mu_b {p : RpP} {s : State} (h : GD nv (fun I s => F I s ∧ MU I s) p s) :
    ∃ b, word s.mem p.B (8 * sB2) = mask b := by
  obtain ⟨I, m₀, rfl, -, -, -, -, -, -, -, hb⟩ := h
  exact hb

theorem zero_pre {B : Addr} {Z : Nat} {m : Mem} : ∃ keep, MaskPre B Z m [.mov32 .rbp (.imm 0)] keep := ⟨_, maskZero⟩

theorem sep_4_14 (w : Nat) : slot w 4 + 8 * (2 * w + 2) ≤ slot w 14 ∨ slot w 14 + 8 * (2 * w + 2) ≤ slot w 4 :=
  .inl (by simp only [Bignum.slot, hdrBytes]; omega_arith)

/-- A step of the halvings leaks the same in two runs, whatever the count. -/
theorem twosBody_ct (hF : Arr F) (hF' : Stab F fun y => 208 ≤ y ∧ y < 224) :
    RelCT isa (Two (GD nv F)) twosBody fun _ _ => True := by
  have hA := mu_arr hF
  rw [twosBody_eq]
  simp only [seqs]
  exact RelCT.seq (twosFlags_ct hF') (RelCT.seq (shrTo_ct (by decide) (by decide) (by decide) hA (by taint_decide))
    (RelCT.seq (selN_ct (by decide) (by decide) (by decide) hA (fun _ _ h => mu_sU h) (by taint_decide))
    (RelCT.seq (shrTo_ct (by decide) (by decide) (by decide) hA (by taint_decide))
    (RelCT.seq (selN_ct (by decide) (by decide) (by decide) hA (fun _ _ h => mu_sB2 h) (by taint_decide))
    (RelCT.seq (dbl1_ct hA fun _ _ h => mu_b h)
    (RelCT.seq (selW_ct (by decide) (by decide) sep_4_14 hA (fun _ _ _ => zero_pre) (by taint_decide))
      countNext_ct))))))

end

/-- A step of the halvings: the count less one. -/
theorem twosBody_gd (n : RpP → Nat) (p : RpP) (s : State) (h : GD nv (Fn n) p s) (h1 : 1 ≤ n p)
    (h2 : n p < 2 ^ 64) :
    WP isa twosBody s fun t => t.zf = some (decide (n p = 1)) ∧ GD nv (Fn fun q => n q - 1) p t := by
  have hA := mu_arr (stab_Fn n fun y hy => .inr (by omega_arith))
  rw [twosBody_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (twosFlags_gd (stab_Fn n fun y hy => .inr (by omega_arith)) p s h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (shrTo_gd (j := 7) (o := 14) (by decide) (by decide) (by decide) hA p t₁ h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (selN_gd (j := 7) (o := 14) (by decide) (by decide) (by decide) hA
    (fun _ _ h => mu_sU h) p t₂ h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (shrTo_gd (j := 6) (o := 14) (by decide) (by decide) (by decide) hA p t₃ h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (selN_gd (j := 6) (o := 14) (by decide) (by decide) (by decide) hA
    (fun _ _ h => mu_sB2 h) p t₄ h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (dbl1_gd hA (fun _ _ h => mu_b h) p t₅ h₅) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (selW_gd (j := 4) (o := 14) (by decide) (by decide) sep_4_14 hA (fun _ _ _ => zero_pre)
    p t₆ h₆) fun t₇ h₇ => ?_)
  exact countNext_gd n p t₇ h₇ h1 h2

/-- The number of halving steps. -/
abbrev nT (p : RpP) : Nat := 64 * nv p.k

theorem twosLoop_ct :
    RelCT isa (Two fun p s => 0 < nT p ∧ GD nv (Fn fun q => nT q - 0) p s) (.loop twosBody .ne)
      (Two (GD nv fun _ _ => True)) :=
  two_loop (Φ := fun p j s => GD nv (Fn fun q => nT q - j) p s) nT
    (two_map Prod.fst (fun ⟨p, j⟩ s ⟨hj, h⟩ => h.mono fun I e hI => by
      have hw2 := h.ws.w2
      subst e
      dsimp only at hj hw2 ⊢
      exact hI.fb (by omega_arith) (by show nT (pubD I) - j < 2 ^ 64; unfold nT; omega_arith))
      (twosBody_ct (stab_FB fun y hy => .inr (by omega_arith)) (stab_FB fun y hy => .inr (by omega_arith))))
    fun p j s hj h => by
      have hw2 := h.ws.w2
      refine WP.mono (twosBody_gd (fun q => nT q - j) p s h (by show 1 ≤ nT p - j; omega_arith)
        (by show nT p - j < 2 ^ 64; unfold nT; omega_arith)) fun t ⟨hz, ht⟩ =>
        ⟨eval_ne_count hj (by rw [hz]; congr 1; simp only [decide_eq_decide]; omega_arith),
          fun _ => ht.mono fun I e hI => by simp only [Fn] at hI ⊢; rw [hI, e, Nat.sub_sub],
          fun _ => ht.mono fun _ _ _ => trivial⟩

/-! ## The square root -/

/-- The borrow's mask in `sC`. -/
def MC (I : RpIn) (s : State) : Prop := ∃ c, word s.mem I.B (8 * sC) = mask c

theorem stab_MC {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 240 ∨ 248 ≤ y) : Stab MC Q :=
  fun I s t P ⟨c, hc⟩ hf hP h1 h2 => ⟨c, stab_hdr (i := sC) (by decide) (fun _ => mask c)
    (fun y hy => by have := hQ y hy; simp only [sC, sFn]; omega_arith) I s t P hc hf hP h1 h2⟩

section
variable {F : RpIn → State → Prop}

theorem storeC_gd (hF : Stab F fun y => 240 ≤ y ∧ y < 248) (p : RpP) (s : State) (h : GR nv F p s) :
    WP isa (.block [.store (hdr sC) .rbp]) s (GD nv (fun I s => F I s ∧ MC I s) p) := by
  obtain ⟨g, c, hc⟩ := h
  refine WP.mono (storeC_ok g.ws) fun t ⟨hm, k⟩ => g.hdrW hm (by unfold DOk; simp only [sC, sFn]; omega_arith)
    (by decide) k (by decide) (fun e => absurd e (by decide)) fun I e hFI => ?_
  subst e
  have := stab_writeW (I := I) (i := sC) hF g.ws.h256 (by decide) hFI hm k.2.1 k.2.2
  exact ⟨this.1, c, this.2.trans hc⟩

theorem storeC_ct (hF : Stab F fun y => 240 ≤ y ∧ y < 248) :
    RelCT isa (Two (GR nv F)) (.block [.store (hdr sC) .rbp]) (Two (GD nv fun I s => F I s ∧ MC I s)) :=
  two_piece [.rdi] pins_GR (by taint_decide) (storeC_gd hF)

theorem mc_arr (hF : Arr F) : Arr fun I s => F I s ∧ MC I s :=
  hF.and (stab_MC fun y hy => .inr (by omega_arith))

theorem mc_ld {p : RpP} {s : State} (h : GD nv (fun I s => F I s ∧ MC I s) p s) :
    ∃ keep, MaskPre p.B p.Z s.mem [.mov .rbp (.mem (hdr sC))] keep := by
  obtain ⟨I, m₀, rfl, h', -, -, -, -, -, ⟨c, hc⟩⟩ := h
  exact ⟨c, maskLd (by decide) h'.ws.h256 hc⟩

theorem mc_not {p : RpP} {s : State} (h : GD nv (fun I s => F I s ∧ MC I s) p s) :
    ∃ c₀, ShlPre [.mov .rbp (.mem (hdr sC)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] c₀ s := by
  obtain ⟨I, m₀, rfl, h', -, -, -, -, -, ⟨c, hc⟩⟩ := id h
  exact ⟨!c, shlPre_mask h.ws (maskNot (by decide) h'.ws.h256 hc)⟩

theorem gr_nil {w : Nat → Nat} {p : RpP} {s : State} (h : GR w F p s) : ∃ c₀, ShlPre [] c₀ s :=
  let ⟨_, c, hc⟩ := h; ⟨c, shlPre_nil hc⟩

theorem sqrtBody_eq : sqrtBody = seqs [shlA true 14 [.mov32 .rbp (.imm 0)], shlA false 4 [],
    shlA true 14 [.mov32 .rbp (.imm 0)], shlA false 4 [],
    copyA 6 5, shlA false 6 [.mov32 .rbp (.imm 0)], shlA false 6 [.mov .rbp (.imm (BitVec.ofInt 32 (-1)))],
    subA 7 4 6, .block [.store (hdr sC) .rbp],
    .seq (.block (ws ++ base 4 .r8 ++ base 7 .rsi ++ ([.mov .rbp (.mem (hdr sC))] : List Instr))) (wordLoop 0 selBody),
    shlA false 5 [.mov .rbp (.mem (hdr sC)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))],
    .block countNext] := rfl

/-- A step of the square root leaks the same in two runs, whatever the count. -/
theorem sqrtBody_ct (hF : Arr F) (hF' : Stab F fun y => 240 ≤ y ∧ y < 248) :
    RelCT isa (Two (GD nv F)) sqrtBody fun _ _ => True := by
  have g : ∀ p s, GR nv F p s → GD nv F p s := fun _ _ h => h.1
  have hA := mc_arr hF
  rw [sqrtBody_eq]
  simp only [seqs]
  exact RelCT.seq (shlA_ct (fun _ _ h => h) true (by decide) hF (fun _ s _ => ⟨_, shlPre_zero s⟩) (by taint_decide))
    (RelCT.seq (shlA_ct g false (by decide) hF (fun _ _ h => gr_nil h) (by taint_decide))
    (RelCT.seq (shlA_ct g true (by decide) hF (fun _ s _ => ⟨_, shlPre_zero s⟩) (by taint_decide))
    (RelCT.seq (shlA_ct g false (by decide) hF (fun _ _ h => gr_nil h) (by taint_decide))
    (RelCT.seq ((copyA_ct (o := 6) (a := 5) (by decide) (by decide) (by decide) hF (by taint_decide)).mono
      (fun _ _ h => two_mono g h) fun _ _ h => h)
    (RelCT.seq (shlA_ct (fun _ _ h => h) false (by decide) hF (fun _ s _ => ⟨_, shlPre_zero s⟩) (by taint_decide))
    (RelCT.seq (shlA_ct g false (by decide) hF (fun _ s _ => ⟨_, shlPre_ones s⟩) (by taint_decide))
    (RelCT.seq ((subA_ct (t := 7) (a := 4) (b := 6) (by decide) (by decide) (by decide) (by decide) (by decide) hF
      (by taint_decide)).mono (fun _ _ h => two_mono g h) fun _ _ h => h)
    (RelCT.seq (storeC_ct hF')
    (RelCT.seq (selN_ct (j := 4) (o := 7) (by decide) (by decide) (by decide) hA (fun _ _ h => mc_ld h)
      (by taint_decide))
    (RelCT.seq (shlA_ct (fun _ _ h => h) false (by decide) hA (fun _ _ h => mc_not h) (by taint_decide))
      (countNext_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.1) h) fun _ _ h => h)))))))))))

end

/-- A step of the square root: the count less one. -/
theorem sqrtBody_gd (n : RpP → Nat) (p : RpP) (s : State) (h : GD nv (Fn n) p s) (h1 : 1 ≤ n p)
    (h2 : n p < 2 ^ 64) :
    WP isa sqrtBody s fun t => t.zf = some (decide (n p = 1)) ∧ GD nv (Fn fun q => n q - 1) p t := by
  have hF := stab_Fn n (Q := fun y => 256 ≤ y) fun y hy => .inr (by omega_arith)
  have hA := mc_arr hF
  have g : ∀ p s, GR nv (Fn n) p s → GD nv (Fn n) p s := fun _ _ h => h.1
  rw [sqrtBody_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (shlA_gd (fun _ _ h => h) true (j := 14) (by decide) hF
    (fun _ s _ => ⟨_, shlPre_zero s⟩) p s h) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (shlA_gd g false (j := 4) (by decide) hF (fun _ _ h => gr_nil h) p t₁ h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (shlA_gd g true (j := 14) (by decide) hF
    (fun _ s _ => ⟨_, shlPre_zero s⟩) p t₂ h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (shlA_gd g false (j := 4) (by decide) hF (fun _ _ h => gr_nil h) p t₃ h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (copyA_gd (o := 6) (a := 5) (by decide) (by decide) (by decide) hF p t₄ h₄.1)
    fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (shlA_gd (fun _ _ h => h) false (j := 6) (by decide) hF
    (fun _ s _ => ⟨_, shlPre_zero s⟩) p t₅ h₅) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (shlA_gd g false (j := 6) (by decide) hF
    (fun _ s _ => ⟨_, shlPre_ones s⟩) p t₆ h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (subA_gd (t := 7) (a := 4) (b := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) hF p t₇ h₇.1) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (storeC_gd (stab_Fn n fun y hy => .inr (by omega_arith)) p t₈ h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (selN_gd (j := 4) (o := 7) (by decide) (by decide) (by decide) hA (fun _ _ h => mc_ld h)
    p t₉ h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.seq (WP.mono (shlA_gd (fun _ _ h => h) false (j := 5) (by decide) hA (fun _ _ h => mc_not h) p t₁₀ h₁₀)
    fun t₁₁ h₁₁ => ?_)
  exact countNext_gd n p t₁₁ h₁₁.1 h1 h2

/-- The number of the square root's steps. -/
abbrev nS (p : RpP) : Nat := 64 * (nv p.k + 1)

theorem sqrtLoop_ct :
    RelCT isa (Two fun p s => 0 < nS p ∧ GD nv (Fn fun q => nS q - 0) p s) (.loop sqrtBody .ne)
      (Two (GD nv fun _ _ => True)) :=
  two_loop (Φ := fun p j s => GD nv (Fn fun q => nS q - j) p s) nS
    (two_map Prod.fst (fun ⟨p, j⟩ s ⟨hj, h⟩ => h.mono fun I e hI => by
      have hw2 := h.ws.w2
      subst e
      dsimp only at hj hw2 ⊢
      exact hI.fb (by omega_arith) (by show nS (pubD I) - j < 2 ^ 64; unfold nS; omega_arith))
      (sqrtBody_ct (stab_FB fun y hy => .inr (by omega_arith)) (stab_FB fun y hy => .inr (by omega_arith))))
    fun p j s hj h => by
      have hw2 := h.ws.w2
      refine WP.mono (sqrtBody_gd (fun q => nS q - j) p s h (by show 1 ≤ nS p - j; omega_arith)
        (by show nS p - j < 2 ^ 64; unfold nS; omega_arith)) fun t ⟨hz, ht⟩ =>
        ⟨eval_ne_count hj (by rw [hz]; congr 1; simp only [decide_eq_decide]; omega_arith),
          fun _ => ht.mono fun I e hI => by simp only [Fn] at hI ⊢; rw [hI, e, Nat.sub_sub],
          fun _ => ht.mono fun _ _ _ => trivial⟩

end VG.Proof.Rsa.X86_64.Rd
