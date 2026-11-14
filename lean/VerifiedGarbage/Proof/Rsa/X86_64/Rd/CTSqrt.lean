module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTDiv
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtFin
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtNorm
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtLoop
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtStep
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtRoot
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtLoops
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.WordLoops
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTDiv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtFin
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtNorm
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtLoop
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtStep
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtRoot
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.SqrtLoops
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.WordLoops
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time, the square root

The square root's pieces at the wide width `W = 2 h + 4`. The normalization
by stages, the first digit (its reciprocal needs the digit's top bit, which
`firstA_ok` gives), the digit loop (each step reloads the count, and its
estimate needs the loop's invariant `SqI`, which `stepXE_ok` gives), and the
root's shift by stages. Facts kept in the header: `sZ` a mask (`MZ`), `sK2`
below `2^63` (`MK`), `sC` below 64 (`MC`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Rsa.X86_64 (copyWords)

/-! ## Header facts -/

/-- A fact of header word `i`. -/
def HF (i : Nat) (P : BitVec 64 → Prop) (I : RpIn) (s : State) : Prop := P (word s.mem I.B (8 * i))

theorem stab_HF {i : Nat} (hi : i < 32) (P : BitVec 64 → Prop) {Q : Nat → Prop}
    (hQ : ∀ y, Q y → y < 8 * i ∨ 8 * i + 8 ≤ y) : Stab (HF i P) Q :=
  fun _ _ _ _ h hf hP _ _ => by
    unfold HF at h ⊢
    rw [hf.word_eq (fun y h1 h2 hy => by have := hQ y (hP y hy).1; omega_arith) (by omega_arith)]
    exact h

/-- What the square root's pieces write but `zeroX`: the arrays, the mask and
the header slots `sCt`, `sU`, `sB2`, `sC` and `sK2`. -/
def SqW (y : Nat) : Prop := 256 ≤ y ∨ (200 ≤ y ∧ y < 224) ∨ (240 ≤ y ∧ y < 256) ∨ (176 ≤ y ∧ y < 184)

abbrev ArrS (F : RpIn → State → Prop) : Prop := Stab F SqW

theorem stab_mono {F : RpIn → State → Prop} {Q Q' : Nat → Prop} (h : Stab F Q) (hQ : ∀ y, Q' y → Q y) :
    Stab F Q' := fun I s t P hF hf hP h1 h2 => h I s t P hF hf (fun y hy => ⟨hQ y (hP y hy).1, (hP y hy).2⟩) h1 h2

theorem ArrS.arr {F : RpIn → State → Prop} (h : ArrS F) : Arr F := stab_mono h fun _ hy => .inl hy
theorem ArrS.hdr {F : RpIn → State → Prop} (h : ArrS F) {i : Nat}
    (hi : 25 ≤ i ∧ i < 28 ∨ 30 ≤ i ∧ i < 32 ∨ i = 22) : Stab F fun y => 8 * i ≤ y ∧ y < 8 * i + 8 :=
  stab_mono h fun y hy => by unfold SqW; omega_arith
theorem ArrS.and {F G : RpIn → State → Prop} (hF : ArrS F) (hG : ArrS G) : ArrS fun I s => F I s ∧ G I s :=
  Stab.and hF hG

/-- `sZ` a mask. -/
abbrev MZ : RpIn → State → Prop := HF sZ fun v => ∃ b, v = mask b
/-- `sK2` below `2^63`. -/
abbrev MK : RpIn → State → Prop := HF sK2 fun v => v.toNat < 2 ^ 63

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

/-- `GD` after a store to a header slot, with a fact of what was stored. -/
theorem GD.setH {p : RpP} {s t : State} (h : GD w F p s) {i : Nat} (hi : DOk (8 * i)) (hi' : i < 32)
    (hne : i ≠ Impl.Bignum.X86_64.Public.sMask) {P : BitVec 64 → Prop} {v : BitVec 64} (hv : P v)
    (hm : t.mem = s.mem.writeW (off p.B (8 * i)) v) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : Stab F fun y => 8 * i ≤ y ∧ y < 8 * i + 8) :
    GD w (fun I s => F I s ∧ HF i P I s) p t :=
  h.hdrW hm hi hi' k hr (fun e => absurd e hne) fun I e hFI => by
    have eB : p.B = I.B := (congrArg RpP.B e).symm
    have eZ : p.Z = I.Z := (congrArg RpP.Z e).symm
    have hZ := h.ws.h256
    rw [eB] at hm
    rw [eZ] at hZ
    obtain ⟨a, b'⟩ := stab_writeW hF hZ hi' hFI hm k.2.1 k.2.2
    exact ⟨a, by unfold HF; rw [b']; exact hv⟩

theorem GD.hf {G : RpIn → State → Prop} {i : Nat} {P : BitVec 64 → Prop} {p : RpP} {s : State}
    (h : GD w (fun I s => G I s ∧ HF i P I s) p s) : P (word s.mem p.B (8 * i)) := by
  obtain ⟨I, m₀, rfl, -, -, -, -, -, -, hP⟩ := h
  exact hP

theorem GD.wkW {p : RpP} {s : State} (h : GD wW F p s) : wW p.k = 2 * wk p.k + 4 ∧ 8 ≤ wk p.k ∧ wk p.k ≤ 128 :=
  ⟨wW_eq _, h.kb⟩

/-! ## The normalization -/

theorem topX_ct (hF : Arr F) : RelCT isa (Two (GD wW F)) (.block topX) (Two (GD wW F)) := by
  have e : topX = ws ++ (base sqZ .rbx ++ ([.mov32 .rax (.imm 0), .store (ix .rbx .r12 (-32)) .rax,
      .store (ix .rbx .r12 (-24)) .rax, .store (ix .rbx .r12 (-16)) .rax, .store (ix .rbx .r12 (-8)) .rax] :
        List Instr)) := by simp only [topX, List.append_assoc]
  rw [e]
  refine wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  rw [← e]
  obtain ⟨hW, kb⟩ := h.wkW
  have hw := h.ws
  have hn := hw.scr.nowrap
  have sl := slot_Z h (j := sqZ) (by decide)
  refine WP.mono (topX_ok hw hW) fun t ⟨hm, k⟩ => h.out (o := slot (wW p.k) sqZ + 8 * (2 * wk p.k)) (n := 32)
    (fun x hx => ?_) (by have := slot_256 (wW p.k) sqZ; omega_arith) (by omega_arith) k (by decide) hF
  rw [hm, writeW_outside _ _ _ (d := slot (wW p.k) sqZ + 8 * (2 * wk p.k + 3)) (by omega_arith) x (by omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqZ + 8 * (2 * wk p.k + 2)) (by omega_arith) x (by omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqZ + 8 * (2 * wk p.k + 1)) (by omega_arith) x (by omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqZ + 8 * (2 * wk p.k)) (by omega_arith) x (by omega_arith)]

/-- The words of `X` or'ed into `rbp`. -/
theorem orX_ct (hF : Arr F) :
    RelCT isa (Two (GD wW F)) (.seq (.block (ws ++ base sqZ .rbx ++ ([.mov32 .rbp (.imm 0)] : List Instr)))
      (wordLoop 0 or1Body)) (Two (GD wW F)) := by
  rw [List.append_assoc]
  refine wsG_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  rw [← List.append_assoc]
  have hw := h.ws
  have hw2 := hw.w2
  have hw1 := hw.w1
  have sl := slot_Z h (j := sqZ) (by decide)
  refine WP.seq (WP.mono (orXHd_ok hw) fun u ⟨hbx, _, h12, mu, ku⟩ =>
    WP.mono (or1_ok (hw.scr.congr ku.2.2) hbx h12 (by omega_arith) (by omega_arith) (by omega_arith))
      fun t ⟨_, mt, kt⟩ => h.same (by rw [mt, mu]) (ku.trans kt) (by decide) hF)

theorem zeroX_ct (hF : Stab F fun y => SqW y ∨ (232 ≤ y ∧ y < 240)) : RelCT isa (Two (GD wW F)) (.block zeroX) (Two (GD wW fun I s => F I s ∧ MZ I s)) := by
  have e : zeroX = ws ++ (base sqZ .rbx ++ ([.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp), .store (hdr sZ) .rbp,
      .mov .rax (.reg .rbp), .alu .and .rax (.imm 1), .alu .or .rax (.mem (at0 .rbx)), .store (at0 .rbx) .rax,
      .mov32 .rax (.imm 0), .store (hdr sK2) .rax] : List Instr)) := by simp only [zeroX, List.append_assoc]
  rw [e]
  refine wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  rw [← e]
  have hw := h.ws
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  have sl := slot_Z h (j := sqZ) (by decide)
  have s256 := slot_256 (wW p.k) sqZ
  refine WP.mono (zeroX_ok hw (z := s.gpr .rbp = 0) Iff.rfl) fun t ⟨hm, k⟩ => ?_
  have hP : ∀ y, (232 ≤ y ∧ y < 240 ∨ slot (wW p.k) sqZ ≤ y ∧ y < slot (wW p.k) sqZ + 8 ∨ 248 ≤ y ∧ y < 256) →
      (SqW y ∨ (232 ≤ y ∧ y < 240)) ∧ y < p.Z := fun y hy => ⟨by unfold SqW; omega_arith, by omega_arith⟩
  have hf : FrmP p.B (fun y => 232 ≤ y ∧ y < 240 ∨ slot (wW p.k) sqZ ≤ y ∧ y < slot (wW p.k) sqZ + 8 ∨
      248 ≤ y ∧ y < 256) s.mem t.mem := by
    intro x hx
    simp only [not_or, not_and_or, Nat.not_le, Nat.not_lt] at hx
    rw [hm, writeW_outside _ _ _ (d := 8 * sK2) (by simp only [sK2, sFn]; omega_arith) x
        (by simp only [sK2, sFn]; omega_arith),
      writeW_outside _ _ _ (d := slot (wW p.k) sqZ) (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (d := 8 * sZ) (by simp only [sZ, sFn]; omega_arith) x (by simp only [sZ, sFn]; omega_arith)]
  refine h.next hf (fun y hy => ⟨?_, (hP y hy).2⟩) k (by decide) (fun c hc => ⟨c, ?_⟩) fun I e hFI => ⟨?_, ?_⟩
  · have := (hP y hy).1; unfold DOk; unfold SqW at this; omega_arith
  · unfold mw at hc ⊢
    rw [hf.word_eq (fun y h1 h2 hy => by simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith)
      (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith), hc]
  · subst e
    exact hF I s t _ hFI hf hP k.2.1 k.2.2
  · subst e
    refine ⟨decide (s.gpr .rbp = 0), ?_⟩
    have hz : 8 * sZ = 232 := rfl
    have hk : 8 * sK2 = 248 := rfl
    show word t.mem (pubD I).B (8 * sZ) = _
    rw [hm, (writeW_outside _ _ _ (d := 8 * sK2) (by omega_arith)).word (by omega_arith) (by omega_arith),
      (writeW_outside _ _ _ (d := slot (wW (pubD I).k) sqZ) (by omega_arith)).word (by omega_arith) (by omega_arith),
      word_writeW_self]

theorem clzX_ct (hFc : Stab F fun y => 8 * sC ≤ y ∧ y < 8 * sC + 8) :
    RelCT isa (Two (GD wW F)) (.block clzX) (Two (GD wW fun I s => F I s ∧ MC I s)) := by
  have e : clzX = ws ++ (base sqZ .rbx ++ (([.mov .rdx (.mem (ix .rbx .r12 (-40))), .mov32 .r11 (.imm 0)] : List Instr) ++
      (([32, 16, 8, 4, 2, 1].map clzStage).flatten ++
      ([.alu .and .r11 (.imm (BitVec.ofInt 32 (-2))), .store (hdr sC) .r11] : List Instr)))) := by
    simp only [clzX, List.append_assoc]
  rw [e]
  exact wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => by
    rw [← e]
    have kb := h.kb
    exact WP.mono (clzX_ok h.ws (by have := wW_eq p.k; omega_arith)) fun _ ⟨hm, k⟩ =>
      h.setC (by omega_arith) hm k (by decide) hFc

theorem testX_ct {c : Nat} (hc1 : 1 ≤ c) (hc128 : c ≤ 128)
    (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) (hw : ∀ p s, GD wW F p s → c ≤ 2 * wk p.k)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base sqZ .rbx ++
      ([.mov .rax (.reg .r12), .alu .sub .rax (.imm (BitVec.ofNat 32 (c + 4))), .shift .shl .rax 3,
        .alu .add .rbx (.reg .rax), .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr)))
      (.seq (wordLoop 0 or1Body) (.block keepOf))) hc).isSome = true) :
    RelCT isa (Two (GD wW F)) (seqs (testX c)) (Two (GD wW fun I s => F I s ∧ MB I s)) := by
  have e : seqs (testX c) = .seq (.seq (.block (ws ++ (base sqZ .rbx ++
      ([.mov .rax (.reg .r12), .alu .sub .rax (.imm (BitVec.ofNat 32 (c + 4))), .shift .shl .rax 3,
        .alu .add .rbx (.reg .rax), .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))))
      (wordLoop 0 or1Body)) (.block keepOf) := by
    simp only [testX, seqs, List.append_assoc]
  rw [e]
  refine RelCT.assoc' (wsG_ct (fun _ _ h => h) ht fun p s h => WP.assoc ?_)
  rw [← e]
  exact WP.mono (testX_ok h.ws (wW_eq p.k) hc1 (hw p s h) hc128) fun _ ⟨hm, k⟩ => h.setB hm k (by decide) hFb

/-- `addK c`: `sK2 := sK2 + c` unless `keep`. -/
theorem addK_ct {c : Nat} (hc128 : c ≤ 128) (hFk : Stab F fun y => 8 * sK2 ≤ y ∧ y < 8 * sK2 + 8)
    (hb : ∀ p s, GD wW F p s → ∃ b, word s.mem p.B (8 * sB2) = mask b) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (addK c)) hc).isSome = true) :
    RelCT isa (Two (GD wW F)) (.block (addK c)) (Two (GD wW F)) :=
  two_piece [.rdi] pins_GD ht fun p s h => by
    obtain ⟨b, hb⟩ := hb p s h
    refine WP.mono (addK_ok h.ws hc128 hb (K := (word s.mem p.B (8 * sK2)).toNat) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]))
      fun t ⟨hm, k⟩ => (h.setH (P := fun _ => True) (by unfold DOk; simp only [sK2, sFn]; omega_arith) (by decide)
        (by decide) trivial hm k (by decide) hFk).mono fun _ _ hI => hI.1

/-- A stage of `c` words of the normalization. -/
theorem stageX_ct {c : Nat} (hc1 : 1 ≤ c) (hc128 : c ≤ 128) (hF : ArrS F) {h₀ h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₀ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 5)))] :
      List Instr)) h₀).isSome = true)
    (t₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base sqZ .rbx ++
      ([.mov .rax (.reg .r12), .alu .sub .rax (.imm (BitVec.ofNat 32 (c + 4))), .shift .shl .rax 3,
        .alu .add .rbx (.reg .rax), .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr)))
      (.seq (wordLoop 0 or1Body) (.block keepOf))) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if false then wideR else []) ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base sqZ .rsi ++ (base sqT .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr)))))) copyWords) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rdi]) (.block (addK c)) h₃).isSome = true) :
    RelCT isa (Two (GD wW F)) (stageX c) (Two (GD wW F)) := by
  unfold stageX
  refine stage_ct (cnd := fun p => decide (2 * wk p.k < c + 1)) hF.arr t₀ (fun p s h => WP.mono
    (stageXHd_ok h.ws (wW_eq p.k) hc128) fun t ⟨⟨hcf, hm⟩, k⟩ => ⟨by simp only [eval, hcf], hm, _, k, by decide⟩)
    (RelCT.block_nil fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1, h₂.1⟩) ?_
  have hG : ArrS fun I s => F I s ∧ c + 1 ≤ 2 * wk I.k := hF.and (stab_const _)
  have hGB := arr_mb hG.arr
  refine ct_pre (Ψ := GD wW fun I s => F I s ∧ c + 1 ≤ 2 * wk I.k) ?_ fun p s ⟨h, hc⟩ => by
    obtain ⟨I, m₀, rfl, h', L, O, he, hm, hFI⟩ := h
    exact ⟨I, m₀, rfl, h', L, O, he, hm, hFI, by
      simp only [decide_eq_false_iff_not] at hc; change ¬ 2 * wk I.k < c + 1 at hc; show c + 1 ≤ 2 * wk I.k
      omega_arith⟩
  have hwk : ∀ p s, GD wW (fun I s => (F I s ∧ c + 1 ≤ 2 * wk I.k) ∧ MB I s) p s → c + 1 ≤ 2 * wk p.k :=
    fun p s h => by obtain ⟨I, m₀, rfl, -, -, -, -, -, hI, -⟩ := h; exact hI.2
  have hT := testX_ct (F := fun I s => F I s ∧ c + 1 ≤ 2 * wk I.k) hc1 hc128 (hG.hdr (by decide))
    (fun p s h => by obtain ⟨I, m₀, rfl, -, -, -, -, -, hI⟩ := h; have := hI.2; show c ≤ 2 * wk I.k; omega_arith) t₁
  have hS := shlWordsF_ct (j := sqZ) (t := sqT) (w := wW) (by decide) (by decide) (by decide) hc128 hGB
    (fun p s h => by have := hwk p s h; have := wW_eq p.k; omega_arith) (by taint_decide) t₂
  have hK := selK_ct (w := wW) false (j := sqZ) (t := sqT) (by decide) (by decide) (sel_far sqZ sqT (by decide)) hGB
    (fun _ _ h => h.mb) (by taint_decide)
  have hA := addK_ct (F := fun I s => (F I s ∧ c + 1 ≤ 2 * wk I.k) ∧ MB I s) hc128
    ((hG.hdr (by decide)).and (stab_MB fun y hy => by simp only [sK2, sFn] at hy; omega_arith)) (fun _ _ h => h.mb) t₃
  exact ct_post (ct_app (by simp [testX]) (List.cons_ne_nil _ _)
    (ct_app (by simp [testX]) (by simp [shlWords]) hT hS) (ct_cons (List.cons_ne_nil _ _) hK (ct_one hA)))
    fun p s h => h.mono fun I _ hI => hI.1.1

end

theorem arrS_mz {F : RpIn → State → Prop} (hF : ArrS F) : ArrS fun I s => F I s ∧ MZ I s :=
  hF.and (stab_HF (i := sZ) (by decide) _ fun y hy => by unfold SqW at hy; simp only [sZ, sFn]; omega_arith)

theorem stab_mz {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 232 ∨ 240 ≤ y) : Stab MZ Q :=
  stab_HF (i := sZ) (by decide) _ fun y hy => by simp only [sZ, sFn]; exact hQ y hy

theorem stab_mk {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 248 ∨ 256 ≤ y) : Stab MK Q :=
  stab_HF (i := sK2) (by decide) _ fun y hy => by simp only [sK2, sFn]; exact hQ y hy

section
variable {F : RpIn → State → Prop}

theorem normX_ct (hF : Stab F fun y => SqW y ∨ (232 ≤ y ∧ y < 240)) :
    RelCT isa (Two (GD wW F)) (seqs normX) (Two (GD wW fun I s => (F I s ∧ MZ I s) ∧ MC I s)) := by
  have hS : ArrS F := stab_mono hF fun y hy => .inl hy
  have hZ := arrS_mz hS
  have hSt : ∀ c ∈ 128 :: wordStages, RelCT isa (Two (GD wW fun I s => F I s ∧ MZ I s)) (stageX c)
      (Two (GD wW fun I s => F I s ∧ MZ I s)) := by
    intro c hc
    simp only [wordStages, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stageX_ct (by decide) (by decide) hZ (by taint_decide) (by taint_decide) (by taint_decide)
        (by taint_decide)
  unfold normX
  exact ct_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    (ct_app (List.cons_ne_nil _ _) (by simp)
      (ct_cons (List.cons_ne_nil _ _) (topX_ct hS.arr) (ct_cons (List.cons_ne_nil _ _) (orX_ct hS.arr)
        (ct_one (zeroX_ct hF))))
      (ct_map _ (128 :: wordStages) (List.cons_ne_nil _ _) hSt))
    (ct_cons (List.cons_ne_nil _ _) (clzX_ct (hZ.hdr (by decide)))
    (ct_cons (List.cons_ne_nil _ _) (shlZ_ct (a := sqZ) (d := sqT) (by decide) (by decide) (by decide) hZ.arr
      (by taint_decide))
    (ct_one (copyA_ct (o := sqZ) (a := sqT) (by decide) (by decide) (by decide) (arr_mc hZ.arr) (by taint_decide)))))

end

/-! ## A digit step, from a public count -/

/-- Before a step's pieces, at count `c` (`a = (p, c)`). -/
def SM (a : RpP × Nat) (s : State) : Prop :=
  Ws s a.1.B a.1.Z (wW a.1.k) ∧ word s.mem a.1.B (8 * sCt) = BitVec.ofNat 64 a.2 ∧ 1 ≤ a.2 ∧
    a.2 + 1 ≤ wk a.1.k ∧ wk a.1.k ≤ 128

/-- `winPtrs`' registers. -/
def winVal (a : RpP × Nat) : Reg → BitVec 64
  | .rdi => a.1.B
  | .rbx => off a.1.B (slot (wW a.1.k) sqZ + 16 * (a.2 - 1))
  | .r8 => off a.1.B (slot (wW a.1.k) sqZ + 16 * (a.2 - 1))
  | .r10 => off a.1.B (slot (wW a.1.k) sqD + 8 * (a.2 - 1))
  | .r12 => BitVec.ofNat 64 (wk a.1.k - (a.2 - 1) + 2)
  | .r9 => BitVec.ofNat 64 (8 * (wW a.1.k + 2))
  | _ => 0

theorem pins_SM : Pins SM [.rdi] := fun _ _ _ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.rdi, h₂.1.rdi]

theorem winPins_ok {a : RpP × Nat} {s : State} (h : SM a s) :
    WP isa (.block winPtrs) s fun t => ∀ r ∈ [.rdi, .rbx, .r8, .r10, .r12, .r9], t.gpr r = winVal a r := by
  obtain ⟨hw, hc, hc1, hch, -⟩ := h
  refine WP.mono (winPtrs_ok hw (wW_eq _) hc hc1 hch) fun t ⟨hbx, h8, h10, h12, h9, _, k⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (k.gpr (by decide)).trans hw.rdi
  · exact hbx
  · exact h8
  · exact h10
  · exact h12
  · exact h9

/-- The step's pieces from `winPtrs`, which loads the count. -/
theorem win_ct {c₂ : Prog isa} {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .rbx, .r8, .r10, .r12, .r9]) c₂ hc).isSome = true)
    (hw : ∀ a s, SM a s → WP isa (.seq (.block winPtrs) c₂) s (SM a)) :
    RelCT isa (Two SM) (.seq (.block winPtrs) c₂) (Two SM) :=
  pin_ct [.rdi] [.rdi, .rbx, .r8, .r10, .r12, .r9] winVal pins_SM (by taint_decide) (fun _ _ h => winPins_ok h) ht hw

/-- `SM` after writes within the arrays. -/
theorem SM.frm {a : RpP × Nat} {s t : State} (h : SM a s) {P : Nat → Prop} (hf : FrmP a.1.B P s.mem t.mem)
    (hP : ∀ y, P y → 256 ≤ y) {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs) : SM a t := by
  obtain ⟨hw, hc, hc1, hch, hh⟩ := h
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine ⟨hw.congrP hf (fun y hy => .inl (hP y hy)) k hr, ?_, hc1, hch, hh⟩
  rw [hf.word_eq (fun y h1 h2 hy => by have := hP y hy; simp only [sCt, sFn] at h1 h2; omega_arith)
    (by simp only [sCt, sFn]; omega_arith), hc]

theorem SM.lay {a : RpP × Nat} {s : State} (h : SM a s) :
    slot (wW a.1.k) sqZ + 16 * (a.2 - 1) + 8 * (wk a.1.k - (a.2 - 1) + 2) ≤ slot (wW a.1.k) sqZ + 8 * (wW a.1.k + 2) ∧
    slot (wW a.1.k) sqD + 8 * (a.2 - 1) + 16 ≤ slot (wW a.1.k) sqD + 8 * (wW a.1.k + 2) ∧
    256 ≤ slot (wW a.1.k) sqD ∧ slot (wW a.1.k) sqZ + 8 * (wW a.1.k + 2) ≤ a.1.Z ∧
    slot (wW a.1.k) sqD + 8 * (wW a.1.k + 2) ≤ slot (wW a.1.k) sqZ := by
  obtain ⟨hw, hc, hc1, hch, hh⟩ := h
  have hW := wW_eq a.1.k
  have hZ := hw.hZ
  rw [slotE] at hZ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [slotE, sqZ, sqD] <;> omega_arith

theorem mulSubX_ct : RelCT isa (Two SM) mulSubX (Two SM) := by
  have e : mulSubX = .seq (.block (winPtrs ++ ([.mov .rcx (.mem (hdr sU)), .store (at0 .r10) .rcx, .mov32 .r9 (.imm 0),
      .mov32 .rbp (.imm 0)] : List Instr))) (wordLoop 0 msBody) := rfl
  rw [e]
  refine RelCT.block_seq (win_ct (by taint_decide) fun a s h => WP.block_seq_iff.mp ?_)
  rw [← e]
  obtain ⟨l1, l2, l3, l4, l5⟩ := h.lay
  have hn := h.1.scr.nowrap
  refine WP.mono (mulSubX_ok h.1 (wW_eq _) h.2.1 h.2.2.1 h.2.2.2.1 (q := (word s.mem a.1.B (8 * sU)).toNat)
    (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) (BitVec.isLt _)) fun t ⟨_, _, o, k⟩ =>
    h.frm (P := fun y => slot (wW a.1.k) sqZ + 16 * (a.2 - 1) ≤ y ∧
      y < slot (wW a.1.k) sqZ + 16 * (a.2 - 1) + 8 * (wk a.1.k - (a.2 - 1) + 2) ∨
      slot (wW a.1.k) sqD + 8 * (a.2 - 1) ≤ y ∧ y < slot (wW a.1.k) sqD + 8 * (a.2 - 1) + 8)
      (fun x hx => ?_) (fun y hy => by omega_arith) k (by decide)
  simp only [not_or, not_and_or, Nat.not_le, Nat.not_lt] at hx
  rw [o x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith)]

theorem two_ct (blk : List Instr) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .rbx, .r8, .r10, .r12, .r9]) (.block blk) hc).isSome = true)
    (hok : ∀ a s, SM a s → WP isa (.block (winPtrs ++ blk)) s fun t => ∃ lo hi : BitVec 64,
      t.mem = (s.mem.writeW (off a.1.B (slot (wW a.1.k) sqD + 8 * (a.2 - 1))) lo).writeW
        (off a.1.B (slot (wW a.1.k) sqD + 8 * (a.2 - 1) + 8)) hi ∧ Keep mmRegs s t) :
    RelCT isa (Two SM) (.block (winPtrs ++ blk)) (Two SM) := by
  refine RelCT.block_append (win_ct ht fun a s h => WP.seq (WP.block_append_iff.mp ?_))
  obtain ⟨l1, l2, l3, l4, l5⟩ := h.lay
  have hn := h.1.scr.nowrap
  refine WP.mono (hok a s h) fun t ⟨lo, hi, hm, k⟩ =>
    h.frm (P := fun y => slot (wW a.1.k) sqD + 8 * (a.2 - 1) ≤ y ∧ y < slot (wW a.1.k) sqD + 8 * (a.2 - 1) + 16)
      (fun x hx => ?_) (fun y hy => by omega_arith) k (by simp [mmRegs])
  simp only [not_and_or, Nat.not_le, Nat.not_lt] at hx
  rw [hm, writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x
    (by omega_arith)]

theorem toE_ct : RelCT isa (Two SM) (.block toE) (Two SM) :=
  two_ct _ (by taint_decide) fun a s h => WP.mono (toE_ok h.1 (wW_eq _) h.2.1 h.2.2.1 h.2.2.2.1)
    fun _ ⟨lo, hi, hm, _, k⟩ => ⟨lo, hi, hm, k⟩

theorem updX_ct : RelCT isa (Two SM) (.block updX) (Two SM) :=
  two_ct _ (by taint_decide) fun a s h => WP.mono (updX_ok h.1 (wW_eq _) h.2.1 h.2.2.1 h.2.2.2.1)
    fun _ ⟨lo, hi, hm, _, k⟩ => ⟨lo, hi, hm, k⟩

theorem fixX_ct : RelCT isa (Two SM) fixX (Two SM) := by
  have e : fixX = .seq (.seq (.block (winPtrs ++ ([.mov .rax (.mem (ix .rbx .r12 (-8))), .alu .add .rax (.reg .rax),
      .alu .sbb .r15 (.reg .r15), .mov32 .rbp (.imm 0)] : List Instr))) (wordLoop 0 addMBody))
    (.block [.mov .r11 (.reg .r15), .alu .and .r11 (.imm 2), .mov .rax (.mem (at0 .r10)),
      .mov .rdx (.mem { base := .r10, disp := 8 }), .alu .sub .rax (.reg .r11), .alu .sbb .rdx (.imm 0),
      .store (at0 .r10) .rax, .store { base := .r10, disp := 8 } .rdx]) := rfl
  rw [e]
  refine RelCT.assoc' (RelCT.block_seq (win_ct (by taint_decide) fun a s h => ?_))
  have hfix := fixX_ok h.1 (wW_eq _) h.2.1 h.2.2.1 h.2.2.2.1
  rw [e] at hfix
  refine WP.block_seq_iff.mp (WP.assoc hfix) |> fun w => WP.mono w fun t ⟨m, _, lo, hi, _, o, hm, _, k⟩ => ?_
  obtain ⟨l1, l2, l3, l4, l5⟩ := h.lay
  have hn := h.1.scr.nowrap
  refine h.frm (P := fun y => slot (wW a.1.k) sqZ + 16 * (a.2 - 1) ≤ y ∧
      y < slot (wW a.1.k) sqZ + 16 * (a.2 - 1) + 8 * (wk a.1.k - (a.2 - 1) + 2) ∨
      slot (wW a.1.k) sqD + 8 * (a.2 - 1) ≤ y ∧ y < slot (wW a.1.k) sqD + 8 * (a.2 - 1) + 16)
      (fun x hx => ?_) (fun y hy => by omega_arith) k (by simp [mmRegs])
  simp only [not_or, not_and_or, Nat.not_le, Nat.not_lt] at hx
  rw [hm, writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x
    (by omega_arith), o x (by omega_arith)]

theorem countNext_sm : RelCT isa (Two SM) (.block countNext) (Two fun (_ : RpP × Nat) (_ : State) => True) :=
  two_post (two_taint [.rdi] pins_SM (by taint_decide)) fun _ s h =>
    WP.mono (countNext_ok h.1 h.2.1 h.2.2.1 (by have := h.2.2.2.1; have := h.2.2.2.2; omega_arith)) fun _ _ => trivial

/-- Before a step: the loop's invariant at count `c`. -/
def SE (a : RpP × Nat) (s : State) : Prop :=
  ∃ s₀ X, X < 2 ^ (64 * (2 * wk a.1.k)) ∧ 2 ^ 62 * 2 ^ (64 * (2 * wk a.1.k - 1)) ≤ X ∧
    SqI s₀ a.1.B a.1.Z (wW a.1.k) (wk a.1.k) X a.2 s ∧ 1 ≤ a.2 ∧ a.2 + 1 ≤ wk a.1.k ∧ wk a.1.k ≤ 128

theorem SE.sm {a : RpP × Nat} {s : State} (h : SE a s) : SM a s :=
  let ⟨_, _, _, _, hI, h1, h2, h3⟩ := h; ⟨hI.ws, hI.ct, h1, h2, h3⟩

/-- The estimate's registers, from its setup. -/
def estVal (a : RpP × Nat) : Reg → BitVec 64
  | .rsi => off a.1.B (slot (wW a.1.k) sqU)
  | .r11 => off a.1.B (slot (wW a.1.k) sqS)
  | r => winVal a r

theorem estA_ok {a : RpP × Nat} {s : State} (h : SM a s) :
    WP isa (.block (ws ++ base sqU .rsi ++ base sqS .r11 ++ winPtrs)) s fun t =>
      ∀ r ∈ [.rdi, .rbx, .r8, .r10, .r12, .r9, .rsi, .r11], t.gpr r = estVal a r := by
  obtain ⟨hw, hc, hc1, hch, -⟩ := h
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono hw.ws_ok fun s₁ ⟨h12, h9, m₁, k₁⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (base2_ok sqU sqS (r₁ := .rsi) (r₂ := .r11) (w := wW a.1.k) (by decide) (by decide) (by decide)
    ((k₁.gpr (by decide)).trans hw.rdi) h9 (by decide)) fun s₂ ⟨hsi, h11, m₂, k₂⟩ => ?_
  have hw₂ : Ws s₂ a.1.B a.1.Z (wW a.1.k) := hw.congrP (P := fun _ => False) (fun _ _ => by rw [m₂, m₁])
    (fun _ f => f.elim) (k₁.trans k₂) (by simp)
  refine WP.mono (winPtrs_ok hw₂ (wW_eq _) (by rw [m₂, m₁, hc]) hc1 hch) fun t ⟨hbx, h8, h10, h12', h9', _, k₃⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (k₃.gpr (by decide)).trans hw₂.rdi
  · exact hbx
  · exact h8
  · exact h10
  · exact h12'
  · exact h9'
  · exact (k₃.gpr (by decide)).trans hsi
  · exact (k₃.gpr (by decide)).trans h11

theorem estX_ct : RelCT isa (Two SE) (.block estX) (Two SM) := by
  have e : estX = (ws ++ base sqU .rsi ++ base sqS .r11 ++ winPtrs) ++
      (half .rbx .rsi (-4) 0 ++ half .rbx .rsi (-3) 1 ++ half .rbx .rsi (-2) 2 ++ half .r10 .r11 (-4) 1 ++
      half .r10 .r11 (-3) 2 ++
      ([.mov .rbx (.reg .rsi), .mov .r10 (.reg .r11), .mov .rbp (.reg .r11), .mov32 .r12 (.imm 3)] : List Instr) ++
      R2Words.quot ++ R2Words.refine3 ++ ([.store (hdr sU) .rcx] : List Instr)) := by
    simp only [estX, List.append_assoc]
  rw [e]
  refine RelCT.block_append (pin_ct [.rdi] [.rdi, .rbx, .r8, .r10, .r12, .r9, .rsi, .r11] estVal
    (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.sm.1.rdi, h₂.sm.1.rdi])
    (by taint_decide) (fun _ _ h => estA_ok h.sm) (by taint_decide) fun a s h => WP.seq (WP.block_append_iff.mp ?_))
  rw [← e]
  obtain ⟨s₀, X, hX, hXt, hI, h1, h2, h3⟩ := h
  exact WP.mono (stepXE_ok (wW_eq _) h3 hX hXt h1 h2 hI).2 fun t ⟨hw, hc⟩ => ⟨hw, hc, h1, h2, h3⟩

theorem stepX_ct : RelCT isa (Two SE) stepX fun _ _ => True := by
  change RelCT isa _ (seqs [.block estX, mulSubX, .block toE, fixX, fixX, fixX, .block updX, .block countNext]) _
  exact (ct_cons (List.cons_ne_nil _ _) estX_ct (ct_cons (List.cons_ne_nil _ _) mulSubX_ct
    (ct_cons (List.cons_ne_nil _ _) toE_ct (ct_cons (List.cons_ne_nil _ _) fixX_ct
    (ct_cons (List.cons_ne_nil _ _) fixX_ct (ct_cons (List.cons_ne_nil _ _) fixX_ct
    (ct_cons (List.cons_ne_nil _ _) updX_ct (ct_one countNext_sm)))))))).mono (fun _ _ h => h) fun _ _ _ => trivial

/-- What the digit loop writes: the arrays, the count and `sU`. -/
def LW (y : Nat) : Prop := 256 ≤ y ∨ (200 ≤ y ∧ y < 216)

abbrev ArrL (F : RpIn → State → Prop) : Prop := Stab F LW

/-- After the first digit: the loop's invariant at `h - 1`. -/
def SQ0 (G : RpIn → State → Prop) (p : RpP) (t : State) : Prop :=
  GD wW G p t ∧ ∃ X, X < 2 ^ (64 * (2 * wk p.k)) ∧ 2 ^ 62 * 2 ^ (64 * (2 * wk p.k - 1)) ≤ X ∧
    SqI t p.B p.Z (wW p.k) (wk p.k) X (wk p.k - 1) t

/-- Before step `j` of the digit loop. -/
def SL (G : RpIn → State → Prop) (p : RpP) (j : Nat) (t : State) : Prop :=
  ∃ s₀ X, GD wW G p s₀ ∧ X < 2 ^ (64 * (2 * wk p.k)) ∧ 2 ^ 62 * 2 ^ (64 * (2 * wk p.k - 1)) ≤ X ∧
    SqI s₀ p.B p.Z (wW p.k) (wk p.k) X (wk p.k - 1 - j) t

theorem sqLoop_ct {G : RpIn → State → Prop} (hG : ArrL G) :
    RelCT isa (Two (SQ0 G)) (.loop stepX .ne) (Two (GD wW G)) := by
  refine ct_pre (two_loop (Φ := SL G) (fun p => wk p.k - 1)
    (two_map (fun q => (q.1, wk q.1.k - 1 - q.2)) (fun q s ⟨hj, s₀, X, g, hX, hXt, hI⟩ => ?_) stepX_ct)
    fun p j s hj ⟨s₀, X, g, hX, hXt, hI⟩ => ?_) fun p s ⟨g, X, hX, hXt, hI⟩ =>
      ⟨by have := g.kb; omega_arith, s, X, g, hX, hXt, by rw [Nat.sub_zero]; exact hI⟩
  · have kb := g.kb
    refine WP.mono (stepX_ok (wW_eq _) kb.2 hX hXt (by omega_arith) (by omega_arith) hI)
      fun s' ⟨hz, hI'⟩ => ⟨?_, fun hl => ⟨s₀, X, g, hX, hXt, ?_⟩, fun he => ?_⟩
    · simp only [eval, hz, Option.map_some, Option.some.injEq]
      by_cases hl : j + 1 < wk p.k - 1
      · rw [decide_eq_true hl, decide_eq_false (by omega_arith)]; rfl
      · rw [decide_eq_false hl, decide_eq_true (by omega_arith)]; rfl
    · rwa [show wk p.k - 1 - (j + 1) = wk p.k - 1 - j - 1 by omega_arith]
    · have hn := hI'.ws.scr.nowrap
      have hZ := hI'.ws.hZ
      rw [slotE] at hZ
      have hP : ∀ y, SqLP (wW p.k) y → (DOk y ∧ LW y ∧ ¬ (176 ≤ y ∧ y < 184)) ∧ y < p.Z := fun y hy => by
        unfold SqLP at hy; unfold DOk LW; simp only [slotE, sqS, sqD, sqU, sqZ, sCt, sU, sFn] at hy; omega_arith
      refine g.next hI'.frm (fun y hy => ⟨(hP y hy).1.1, (hP y hy).2⟩) hI'.keep (by simp [mmRegs])
        (fun c hc => ⟨c, ?_⟩) fun I e hFI => by
          subst e; exact hG I s₀ s' _ hFI hI'.frm (fun y hy => ⟨(hP y hy).1.2.1, (hP y hy).2⟩) hI'.keep.2.1 hI'.keep.2.2
      unfold mw at hc ⊢
      rw [hI'.frm.word_eq (fun y h1 h2 hy => (hP y hy).1.2.2 (by
          simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith))
        (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith), hc]

  · obtain ⟨p, j⟩ := q
    have kb := g.kb
    simp only at hj hI kb ⊢
    exact ⟨s₀, X, hX, hXt, hI, by show 1 ≤ wk p.k - 1 - j; omega_arith,
      by show wk p.k - 1 - j + 1 ≤ wk p.k; omega_arith, kb.2⟩

/-! ## The first digit -/

section
variable {G : RpIn → State → Prop}

/-- `GD` after writes to the arrays, the count and `sU`. -/
theorem GD.sqlp {p : RpP} {s t : State} (h : GD wW G p s) (hf : FrmP p.B (SqLP (wW p.k)) s.mem t.mem)
    {regs : List Reg} (k : Keep regs s t) (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hG : ArrL G) : GD wW G p t := by
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  rw [slotE] at hZ
  have hP : ∀ y, SqLP (wW p.k) y → (DOk y ∧ LW y ∧ ¬ (176 ≤ y ∧ y < 184)) ∧ y < p.Z := fun y hy => by
    unfold SqLP at hy; unfold DOk LW; simp only [slotE, sqS, sqD, sqU, sqZ, sCt, sU, sFn] at hy; omega_arith
  refine h.next hf (fun y hy => ⟨(hP y hy).1.1, (hP y hy).2⟩) k hr (fun c hc => ⟨c, ?_⟩) fun I e hFI => by
    subst e; exact hG I s t _ hFI hf (fun y hy => ⟨(hP y hy).1.2.1, (hP y hy).2⟩) k.2.1 k.2.2
  unfold mw at hc ⊢
  rw [hf.word_eq (fun y h1 h2 hy => (hP y hy).1.2.2 (by
      simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith))
    (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith), hc]

/-- The first digit's loop, from `X`'s top two words. -/
theorem isqP_ct (hG : Arr G) :
    RelCT isa (Two (GD wW G)) (.seq (.block (ws ++ base sqZ .rbx ++ ([.mov .r8 (.mem (ix .rbx .r12 (-40))),
      .mov .r9 (.mem (ix .rbx .r12 (-48))), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0), .mov32 .r13 (.imm 0),
      .mov32 .rcx (.imm 64)] : List Instr))) (.loop (.block isqBody) .ne)) (Two (GD wW G)) := by
  rw [List.append_assoc]
  refine wsG_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  rw [← List.append_assoc]
  have kb := h.kb
  have hW := wW_eq p.k
  refine WP.seq (WP.mono (firstHd_ok h.ws (by omega_arith)) fun t₄ ⟨h8, h9, h10, h11, h13, hcx, m₄, k₄⟩ => ?_)
  generalize hw5 : word s.mem p.B (slot (wW p.k) sqZ + 8 * (wW p.k - 5)) = w5 at h8
  generalize hw6 : word s.mem p.B (slot (wW p.k) sqZ + 8 * (wW p.k - 6)) = w6 at h9
  have l5 := w5.isLt
  have l6 := w6.isLt
  have hT : w5.toNat * 2 ^ 64 + w6.toNat < 2 ^ 128 := by omega_arith
  have h8' : t₄.gpr .r8 = BitVec.ofNat 64 ((w5.toNat * 2 ^ 64 + w6.toNat) / 2 ^ 64) := by
    rw [h8, show (w5.toNat * 2 ^ 64 + w6.toNat) / 2 ^ 64 = w5.toNat by omega_arith, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have h9' : t₄.gpr .r9 = BitVec.ofNat 64 ((w5.toNat * 2 ^ 64 + w6.toNat) % 2 ^ 64) := by
    rw [h9, show (w5.toNat * 2 ^ 64 + w6.toNat) % 2 ^ 64 = w6.toNat by omega_arith, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  exact WP.mono (isq_ok hT (isqInv0 (t₀ := t₄) hT h10 h11 h13 h8' h9' hcx rfl (Keep.refl _ _)))
    fun t ⟨_, _, _, _, _, _, m₅, k₅⟩ => h.same (by rw [m₅, m₄]) (k₄.trans k₅) (by decide) hG

/-- The first digit's stores. -/
theorem firstSt_ct (hG : Arr G) :
    RelCT isa (Two (GD wW G)) (.block (ws ++ base sqZ .rbx ++ ([.store (ix .rbx .r12 (-40)) .r11,
      .store (ix .rbx .r12 (-48)) .r13] : List Instr) ++ base sqD .rsi ++ hOf ++ ([.mov .rax (.reg .r10),
      .alu .add .rax (.reg .rax), .store (ix .rsi .r12 (-8)) .rax, .mov .rax (.reg .r10), .shift .shr .rax 63,
      .store (ix .rsi .r12) .rax] : List Instr) ++ base sqS .rsi ++ ([.store { base := .rsi, disp := 16 } .r10] :
        List Instr))) (Two (GD wW G)) := by
  simp only [List.append_assoc]
  refine wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  simp only [← List.append_assoc]
  have kb := h.kb
  have hW := wW_eq p.k
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  rw [slotE] at hZ
  have s1 := slotE (wW p.k) sqS
  have s8 := slotE (wW p.k) 8
  have sD := slotE (wW p.k) sqD
  have sZ' := slotE (wW p.k) sqZ
  simp only [sqS, sqD, sqZ] at s1 sD sZ'
  refine WP.mono (firstSt_ok h.ws hW (by omega_arith)) fun t ⟨hm, k⟩ =>
    h.arr (P := fun y => slot (wW p.k) sqS ≤ y ∧ y < slot (wW p.k) 8) ?_
    (fun y hy => ⟨by simp only [sqS] at hy; omega_arith, by simp only [sqS] at hy; omega_arith⟩) k (by decide) hG
  intro x hx
  simp only [sqS, not_and_or, Nat.not_le, Nat.not_lt] at hx
  rw [hm, writeW_outside _ _ _ (d := slot (wW p.k) sqS + 16) (by simp only [sqS]; omega_arith) x
      (by simp only [sqS]; omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqD + 8 * wk p.k) (by simp only [sqD]; omega_arith) x
      (by simp only [sqD]; omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqD + 8 * (wk p.k - 1)) (by simp only [sqD]; omega_arith) x
      (by simp only [sqD]; omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqZ + 8 * (wW p.k - 6)) (by simp only [sqZ]; omega_arith) x
      (by simp only [sqZ]; omega_arith),
    writeW_outside _ _ _ (d := slot (wW p.k) sqZ + 8 * (wW p.k - 5)) (by simp only [sqZ]; omega_arith) x
      (by simp only [sqZ]; omega_arith)]

/-- The first digit's top bit set. -/
def FSq (p : RpP) (s : State) : Prop := 2 ^ 63 ≤ (word s.mem p.B (slot (wW p.k) sqS + 8 * (3 - 1))).toNat

/-- The first digit's reciprocal. -/
theorem recipS_ct (hG : Arr G) :
    RelCT isa (Two fun p s => GD wW G p s ∧ FSq p s)
      (.seq (.block (ws ++ base sqS .r10 ++ base sqS .r8 ++ ([.mov32 .r12 (.imm 3)] : List Instr))) R2Words.recip)
      (Two (GD wW G)) := by
  have e : ws ++ base sqS .r10 ++ base sqS .r8 ++ ([.mov32 .r12 (.imm 3)] : List Instr) =
      ws ++ (base sqS .r10 ++ (base sqS .r8 ++ ([.mov32 .r12 (.imm 3)] : List Instr))) := by simp only [List.append_assoc]
  rw [e]
  refine wsG_ct (w := wW) (F := G) (fun _ _ h => h.1) (by taint_decide) fun p s h => ?_
  rw [← e]
  have hw := h.1.ws
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  rw [slotE] at hZ
  refine WP.seq (WP.mono (firstRcp_ok hw) fun u ⟨h10, h8, h12, mu, ku⟩ =>
    WP.mono (R2w.recip_ok (hw.scr.congr ku.2.2) h10 h12 h8 (by decide) (by simp only [slotE, sqS]; omega_arith)
      (by simp only [slotE, sqS]; omega_arith) (by rw [mu]; exact h.2)) fun t ⟨m, k⟩ => ?_)
  rw [mu] at m
  have o : Outside p.B (slot (wW p.k) sqS) 8 s.mem t.mem := by
    rw [m]; exact writeW_outside _ _ _ (by simp only [slotE, sqS]; omega_arith)
  exact h.1.out o (slot_256 _ _) (by simp only [slotE, sqS]; omega_arith) (ku.trans k) (by decide) hG

theorem ctX_ct (hG : ArrL G) :
    RelCT isa (Two (GD wW G)) (.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr)))
      (Two (GD wW G)) := by
  rw [List.append_assoc]
  refine wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  rw [← List.append_assoc]
  have kb := h.kb
  refine WP.mono (ctX_ok h.ws (wW_eq p.k) (by omega_arith)) fun t ⟨hm, k⟩ =>
    h.hdrW hm (by unfold DOk; simp only [sCt, sFn]; omega_arith) (by decide) k (by decide)
      (fun e => absurd e (by decide)) fun I e hGI => ?_
  subst e
  have hn := h.ws.scr.nowrap
  have hZ := h.ws.hZ
  rw [slotE] at hZ
  have hct : 8 * sCt = 200 := rfl
  have hf : FrmP (pubD I).B (fun y => 8 * sCt ≤ y ∧ y < 8 * sCt + 8) s.mem t.mem := by
    rw [hm]; exact FrmP.of_writeW _ (by omega_arith) fun _ h1 h2 => ⟨h1, h2⟩
  exact hG I s t _ hGI hf (fun y hy => ⟨by unfold LW; omega_arith, by show y < (pubD I).Z; omega_arith⟩) k.2.1 k.2.2

end

/-- The normalized `X`. -/
def NXv (I : RpIn) (s : State) : Prop :=
  ∃ X, wv s.mem I.B (slot (wW I.k) sqZ) (wW I.k) = X ∧ 2 ^ 62 * 2 ^ (64 * (2 * wk I.k - 1)) ≤ X ∧
    X < 2 ^ (64 * (2 * wk I.k))

section
variable {G : RpIn → State → Prop}

theorem firstX_ct (hG : ArrL G) (hGa : Arr G) :
    RelCT isa (Two (GD wW fun I s => G I s ∧ NXv I s))
      (seqs (firstX ++ ([.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr))] :
      List (Prog isa))))
      (Two (SQ0 G)) := by
  have e : firstX ++ [.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr))] =
      firstX.take 5 ++ [.seq (.block (ws ++ base sqS .r10 ++ base sqS .r8 ++ ([.mov32 .r12 (.imm 3)] : List Instr)))
        R2Words.recip, .block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1), .store (hdr sCt) .r12] : List Instr))] := rfl
  have weakA : RelCT isa (Two (GD wW G)) (seqs (firstX.take 5)) (Two (GD wW G)) :=
    ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := sqD) (by decide) hGa (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := sqS) (by decide) hGa (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := sqU) (by decide) hGa (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (isqP_ct hGa) (ct_one (firstSt_ct hGa)))))
  have inner : RelCT isa (Two (GD wW fun I s => G I s ∧ NXv I s)) (seqs (firstX.take 5))
      (Two fun p s => GD wW G p s ∧ FSq p s) :=
    two_post ((ct_pre weakA fun p s h => h.mono fun _ _ h => h.1).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun p s h => by
        obtain ⟨I, m₀, e', h', L, O, he, hm, hGI, X, hX, hXt, hXh⟩ := id h
        subst e'
        have kb : 8 ≤ wk I.k := h.kb.1
        have hW := wW_eq I.k
        refine WP.mono (firstA_ok h'.ws hW (by omega_arith) (top_pair hW (by omega_arith) hX hXh)
          (top_pair_lo (by omega_arith) hXt)) fun t ⟨_, f, k, top⟩ =>
            ⟨(h.mono fun _ _ h => h.1).sqlp f k (by simp [mmRegs]) hG, top⟩
  refine two_post ?_ fun p s h => ?_
  · rw [e]
    exact (ct_app (by simp [firstX]) (List.cons_ne_nil _ _) inner (ct_cons (List.cons_ne_nil _ _) (recipS_ct hGa)
      (ct_one (ctX_ct hG)))).mono (fun _ _ h => h) fun _ _ _ => trivial
  · obtain ⟨I, m₀, e', h', L, O, he, hm, hGI, X, hX, hXt, hXh⟩ := id h
    subst e'
    have kb : 8 ≤ wk I.k := h.kb.1
    refine WP.mono (sqInit_ok h'.ws (wW_eq _) (by omega_arith) hX hXt hXh) fun t ⟨hI, f, k⟩ =>
      ⟨(h.mono fun _ _ h => h.1).sqlp f k (by simp [mmRegs]) hG, X, hXh, hXt, hI⟩

end

/-! ## The root's shift -/

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

section
variable {G : RpIn → State → Prop}

theorem halfA_ct {t j : Nat} (hj : j < 16) (ht : t < 16) (hjt : j ≠ t) (hG : Arr G)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (htc : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8 ++ base t .rsi))
      (wordLoop 0 shrBody)) hc).isSome = true) :
    RelCT isa (Two (GD wW G)) (halfA t j) (Two (GD wW G)) := by
  have e : halfA t j = .seq (.block (ws ++ (base j .r8 ++ base t .rsi))) (wordLoop 0 shrBody) := by
    simp only [halfA, List.append_assoc]
  rw [e]
  exact wsG_ct (fun _ _ h => h) htc fun p s h => by
    rw [← e]
    exact WP.mono (shrTo_frm h.ws hj ht hjt) fun _ ⟨o, k⟩ =>
      h.out o (slot_256 _ _) (by have := slot_Z h ht; omega_arith) k (by decide) hG

/-- The facts the root's shift keeps. -/
abbrev G1 (F : RpIn → State → Prop) : RpIn → State → Prop := fun I s => ((F I s ∧ MZ I s) ∧ MK I s) ∧ MC I s

theorem G1.arrL {F : RpIn → State → Prop} (hF : ArrS F) : ArrL (G1 F) :=
  ((((stab_mono hF fun y hy => by unfold LW at hy; unfold SqW; omega_arith)).and
    (stab_mz fun y hy => by unfold LW at hy; omega_arith)).and (stab_mk fun y hy => by unfold LW at hy; omega_arith)).and
    (stab_MC fun y hy => by unfold LW at hy; omega_arith)

theorem G1.arr {F : RpIn → State → Prop} (hF : ArrS F) : Arr (G1 F) :=
  stab_mono (G1.arrL hF) fun _ hy => .inl hy

theorem g1_facts {F : RpIn → State → Prop} {p : RpP} {s : State} (h : GD wW (G1 F) p s) :
    (∃ b, word s.mem p.B (8 * sZ) = mask b) ∧ (word s.mem p.B (8 * sK2)).toNat < 2 ^ 63 ∧
      ∃ z, z < 64 ∧ word s.mem p.B (8 * sC) = BitVec.ofNat 64 z := by
  obtain ⟨I, m₀, rfl, -, -, -, -, -, ⟨⟨⟨-, hz⟩, hk⟩, hc⟩⟩ := h
  exact ⟨hz, hk, hc⟩

theorem kBlk_ct {F : RpIn → State → Prop} (hF : ArrS F) :
    RelCT isa (Two (GD wW (G1 F))) (.block [.mov .rax (.mem (hdr sK2)), .mov .rdx (.reg .rax), .shift .shr .rax 1,
      .store (hdr sK2) .rax, .alu .and .rdx (.imm 1), .shift .shl .rdx 5, .mov .rax (.mem (hdr sC)),
      .shift .shr .rax 1, .alu .add .rax (.reg .rdx), .store (hdr sC) .rax]) (Two (GD wW (G1 F))) :=
  two_piece [.rdi] pins_GD (by taint_decide) fun p s h => by
    obtain ⟨-, hK, z, hz, hc⟩ := g1_facts h
    have hn := h.ws.scr.nowrap
    have hZ := h.ws.hZ
    rw [slotE] at hZ
    have e2 : 8 * sK2 = 248 := rfl
    have e3 : 8 * sC = 240 := rfl
    refine WP.mono (kBlk_ok h.ws hK hz (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]) hc) fun t ⟨hm, k⟩ => ?_
    generalize (word s.mem p.B (8 * sK2)).toNat = K at hK hm
    have hf : FrmP p.B (fun y => 240 ≤ y ∧ y < 256) s.mem t.mem := by
      intro x hx
      simp only [not_and_or, Nat.not_le, Nat.not_lt] at hx
      rw [hm, writeW_outside _ _ _ (d := 8 * sC) (by omega_arith) x (by omega_arith),
        writeW_outside _ _ _ (d := 8 * sK2) (by omega_arith) x (by omega_arith)]
    refine h.next hf (fun y hy => ⟨by unfold DOk; omega_arith, by omega_arith⟩) k (by decide)
      (fun c hc => ⟨c, by unfold mw at hc ⊢; rw [hf.word_eq (fun y h1 h2 hy => by
        simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith)
        (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith), hc]⟩) fun I e hI => ?_
    subst e
    obtain ⟨⟨⟨hFI, hZI⟩, -⟩, -⟩ := hI
    refine ⟨⟨⟨hF I s t _ hFI hf (fun y hy => ⟨by unfold SqW; omega_arith, by show y < (pubD I).Z; omega_arith⟩)
      k.2.1 k.2.2, stab_mz (Q := fun y => 240 ≤ y ∧ y < 256) (fun y hy => by omega_arith) I s t _ hZI hf
      (fun y hy => ⟨hy, by show y < (pubD I).Z; omega_arith⟩) k.2.1 k.2.2⟩, ?_⟩, ?_⟩
    · show (word t.mem (pubD I).B (8 * sK2)).toNat < 2 ^ 63
      rw [hm, (writeW_outside _ _ _ (d := 8 * sC) (by omega_arith)).word (by omega_arith) (by omega_arith),
        word_writeW_self, BitVec.toNat_ofNat]
      omega_arith
    · refine ⟨z / 2 + 32 * (K % 2), by omega_arith, ?_⟩
      show word t.mem (pubD I).B (8 * sC) = _
      rw [hm, word_writeW_self]

/-- `sB2 := ` the mask of `K`'s bit `c` clear. -/
theorem kSel_ct {c : Nat} (hc : c < 2 ^ 31) {F : RpIn → State → Prop} (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8)
    (hK : ∀ p s, GD wW F p s → (word s.mem p.B (8 * sK2)).toNat < 2 ^ 63)
    {hc' : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rax (.mem (hdr sK2)), .alu .and .rax (.imm (BitVec.ofNat 32 c)),
      .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .store (hdr sB2) .rax]) hc').isSome = true) :
    RelCT isa (Two (GD wW F)) (.block [.mov .rax (.mem (hdr sK2)), .alu .and .rax (.imm (BitVec.ofNat 32 c)),
      .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax), .store (hdr sB2) .rax])
      (Two (GD wW fun I s => F I s ∧ MB I s)) :=
  two_piece [.rdi] pins_GD ht fun p s h =>
    WP.mono (kSel_ok h.ws (hK p s h) hc (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])) fun _ ⟨hm, k⟩ =>
      h.setB hm k (by decide) hFb

/-- A stage of `c` words of the root's shift. -/
theorem stageR_ct {c : Nat} (hc1 : 1 ≤ c) (hc64 : c ≤ 64) {F : RpIn → State → Prop} (hF : ArrS F)
    {h₀ h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₀ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 4)))] :
      List Instr)) h₀).isSome = true)
    (t₁ : (taint.check (Taint.ofRegs [.rdi]) (.block [.mov .rax (.mem (hdr sK2)),
      .alu .and .rax (.imm (BitVec.ofNat 32 c)), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
      .store (hdr sB2) .rax]) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] :
      List Instr) ++ (base sqR .rsi ++ (([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++
        base sqT .rbx)))) copyWords) h₂).isSome = true) :
    RelCT isa (Two (GD wW (G1 F))) (stageR c) (Two (GD wW (G1 F))) := by
  unfold stageR
  have hA := G1.arr hF
  refine stage_ct (cnd := fun p => decide (wW p.k < c + 4)) hA t₀ (fun p s h => WP.mono
    (stageRHd_ok h.ws (by omega_arith)) fun t ⟨⟨hcf, hm⟩, k⟩ => ⟨by simp only [eval, hcf], hm, _, k, by decide⟩)
    (RelCT.block_nil fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1, h₂.1⟩) ?_
  have hG : Arr fun I s => G1 F I s ∧ c + 4 ≤ wW I.k := hA.and (stab_const _)
  have hGB := arr_mb hG
  refine ct_pre (Ψ := GD wW fun I s => G1 F I s ∧ c + 4 ≤ wW I.k) ?_ fun p s ⟨h, hc⟩ => by
    obtain ⟨I, m₀, rfl, h', L, O, he, hm, hFI⟩ := h
    exact ⟨I, m₀, rfl, h', L, O, he, hm, hFI, by
      simp only [decide_eq_false_iff_not] at hc; change ¬ wW I.k < c + 4 at hc; show c + 4 ≤ wW I.k; omega_arith⟩
  have hK := kSel_ct (F := fun I s => G1 F I s ∧ c + 4 ≤ wW I.k) (c := c) (by omega_arith)
    (((((stab_mono hF fun y hy => by unfold SqW; simp only [sB2, sFn] at hy; omega_arith).and
      (stab_mz fun y hy => by simp only [sB2, sFn] at hy; omega_arith)).and
      (stab_mk fun y hy => by simp only [sB2, sFn] at hy; omega_arith)).and
      (stab_MC fun y hy => by simp only [sB2, sFn] at hy; omega_arith)).and (stab_const _))
    (fun p s h => (g1_facts (GD.mono h fun _ _ h => h.1)).2.1) t₁
  have hS := shrWords_ct (j := sqR) (t := sqT) (w := wW) (by decide) (by decide) (by decide) hc64 hGB
    (fun p s h => by obtain ⟨I, m₀, rfl, -, -, -, -, -, hI, -⟩ := h; have := hI.2; show c + 1 ≤ wW I.k; omega_arith)
    (by taint_decide) t₂
  have hSel := selK_ct (w := wW) false (j := sqR) (t := sqT) (by decide) (by decide) (sel_far sqR sqT (by decide)) hGB
    (fun _ _ h => h.mb) (by taint_decide)
  exact ct_post (ct_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    (ct_app (List.cons_ne_nil _ _) (by simp [shrWords]) (ct_one hK) hS) (ct_one hSel))
    fun p s h => h.mono fun I _ hI => hI.1.1

end

section
variable {F : RpIn → State → Prop}

theorem lastR_ct (hF : ArrS F) :
    RelCT isa (Two (GD wW (G1 F))) (.block (ws ++ base sqR .rbx ++ ([.mov .rax (.mem (hdr sZ)), .alu .and .rax (.imm 1),
      .mov .rdx (.mem (at0 .rbx)), .alu .sub .rdx (.reg .rax), .store (at0 .rbx) .rdx] : List Instr)))
      (Two (GD wW (G1 F))) := by
  rw [List.append_assoc]
  refine wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => ?_
  rw [← List.append_assoc]
  obtain ⟨⟨b, hb⟩, -⟩ := g1_facts h
  have hn := h.ws.scr.nowrap
  have sl := slot_Z h (j := sqR) (by decide)
  refine WP.mono (lastR_ok h.ws hb) fun t ⟨hm, k⟩ => ?_
  have o : Outside p.B (slot (wW p.k) sqR) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by omega_arith)
  exact h.out o (slot_256 _ _) (by omega_arith) k (by decide) (G1.arr hF)

theorem finishX_ct (hF : ArrS F) : RelCT isa (Two (GD wW (G1 F))) (seqs finishX) (Two (GD wW (G1 F))) := by
  have hA := G1.arr hF
  have hS : ∀ c ∈ wordStages, RelCT isa (Two (GD wW (G1 F))) (stageR c) (Two (GD wW (G1 F))) := by
    intro c hc
    simp only [wordStages, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stageR_ct (by decide) (by decide) hF (by taint_decide) (by taint_decide) (by taint_decide)
  have hM : Stab (G1 F) fun y => 176 ≤ y ∧ y < 184 :=
    (((stab_mono hF fun y hy => by unfold SqW; omega_arith).and (stab_mz fun y hy => by omega_arith)).and
      (stab_mk fun y hy => by omega_arith)).and (stab_MC fun y hy => by omega_arith)
  unfold finishX
  exact ct_app (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    (ct_app (List.cons_ne_nil _ _) (by simp [wordStages])
      (ct_cons (List.cons_ne_nil _ _) (orX_ct hA) (ct_cons (List.cons_ne_nil _ _) (andZero_ct hM)
      (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := sqR) (by decide) hA (by taint_decide))
      (ct_cons (List.cons_ne_nil _ _) (halfA_ct (t := sqR) (j := sqD) (by decide) (by decide) (by decide) hA
        (by taint_decide)) (ct_one (kBlk_ct hF))))))
      (ct_map _ wordStages (by simp [wordStages]) hS))
    (ct_cons (List.cons_ne_nil _ _) (shrZ_ct (a := sqR) (d := sqT) (G := fun I s => (F I s ∧ MZ I s) ∧ MK I s)
      (by decide) (by decide) (by decide) ((hF.arr.and (stab_mz fun y hy => .inr (by omega_arith))).and (stab_mk fun y hy => .inr (by omega_arith)))
      (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (copyA_ct (o := sqR) (a := sqT) (by decide) (by decide) (by decide) hA
      (by taint_decide)) (ct_one (lastR_ct hF))))

end

section
variable {F : RpIn → State → Prop}

/-- `normX`, with what it establishes. -/
theorem normXs_ct (hF : Stab F fun y => SqW y ∨ (232 ≤ y ∧ y < 240)) :
    RelCT isa (Two (GD wW F)) (seqs normX) (Two (GD wW fun I s => G1 F I s ∧ NXv I s)) := by
  refine two_post ((normX_ct hF).mono (fun _ _ h => h) fun _ _ _ => trivial) fun p s h => ?_
  obtain ⟨I, m₀, e, h', L, O, he, hm, hFI⟩ := id h
  subst e
  have kb : 8 ≤ wk I.k ∧ wk I.k ≤ 128 := h.kb
  have hn := h'.ws.scr.nowrap
  have hZ := h'.ws.hZ
  rw [slotE] at hZ
  refine WP.mono (normX_ok h'.ws (wW_eq I.k) (by omega_arith) kb.2 rfl)
    fun t ⟨C, z, _, hz64, hC, hX, hlo, hhi, hK, hzC, hZm, f, k, hw⟩ => ?_
  have hP : ∀ y, NxP (wW I.k) y → (DOk y ∧ (SqW y ∨ (232 ≤ y ∧ y < 240)) ∧ ¬ (176 ≤ y ∧ y < 184)) ∧ y < I.Z :=
    fun y hy => by unfold NxP at hy; unfold DOk SqW; simp only [slotE, sqT] at hy; omega_arith
  refine h.next (F' := fun I s => G1 F I s ∧ NXv I s) f (fun y hy => ⟨(hP y hy).1.1, (hP y hy).2⟩) k
    (by simp [mmRegs]) (fun c hc => ⟨c, ?_⟩) fun J e hFJ => ?_
  · unfold mw at hc ⊢
    show word t.mem I.B _ = _
    rw [f.word_eq (fun y h1 h2 hy => (hP y hy).1.2.2 (by
        simp only [Impl.Bignum.X86_64.Public.sMask, sFn] at h1 h2; omega_arith))
      (by simp only [Impl.Bignum.X86_64.Public.sMask, sFn]; omega_arith)]
    exact hc
  · have eB : J.B = I.B := congrArg RpP.B e
    have eK : J.k = I.k := congrArg RpP.k e
    have eZ : J.Z = I.Z := congrArg RpP.Z e
    refine ⟨⟨⟨⟨hF J s t _ hFJ (by rw [eB]; exact f) (fun y hy => ⟨(hP y hy).1.2.1, by rw [eZ]; exact (hP y hy).2⟩)
      k.2.1 k.2.2, ?_⟩, ?_⟩, z, hz64, ?_⟩,
      Xn (wv s.mem I.B (slot (wW I.k) sqZ) (wW I.k)) (wk I.k) * 2 ^ (64 * C) * 2 ^ z, ?_, ?_, ?_⟩
    · show ∃ b, word t.mem J.B (8 * sZ) = mask b
      rw [eB, hZm]; exact ⟨_, rfl⟩
    · show (word t.mem J.B (8 * sK2)).toNat < 2 ^ 63
      rw [eB, hK, BitVec.toNat_ofNat]; omega_arith
    · show word t.mem J.B (8 * sC) = _; rw [eB, hzC]
    · rw [eB, eK]; exact hX
    · rw [eK]; exact hlo
    · rw [eK]; exact hhi
end

/-- The square root, at the wide width. -/
theorem sqrt_ct {F : RpIn → State → Prop} (hF : Stab F fun y => SqW y ∨ (232 ≤ y ∧ y < 240)) :
    RelCT isa (Two (GD wW F)) (seqs RecoverDet.sqrt) (Two (GD wW (G1 F))) := by
  have hS : ArrS F := stab_mono hF fun y hy => .inl hy
  have e : RecoverDet.sqrt = normX ++ ((firstX ++ [.block (ws ++ hOf ++ ([.alu .sub .r12 (.imm 1),
      .store (hdr sCt) .r12] : List Instr))]) ++ ([.loop stepX .ne] ++ finishX)) := by
    simp only [RecoverDet.sqrt, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  exact ct_app (by simp [normX]) (by simp) (normXs_ct hF)
    (ct_app (by simp) (by simp) (firstX_ct (G1.arrL hS) (G1.arr hS))
      (ct_cons (by simp [finishX]) (sqLoop_ct (G1.arrL hS)) (finishX_ct hS)))

end VG.Proof.Rsa.X86_64.Rd
