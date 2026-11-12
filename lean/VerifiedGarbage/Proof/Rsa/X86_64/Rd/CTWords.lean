module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTBase
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.TwoStages
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.WordLoops
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.TwoStages
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.WordLoops
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time, the word-level pieces

The stages of shifts by words and bits, their tests and selects, and the
copies through a temporary, each from `GD` (`CTBase`). A stage's branch is
on the width alone; its pieces keep the stage's mask `sB2` a mask (`MB`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Rsa.X86_64 (copyWords)

/-! ## Lists of pieces -/

theorem RelCT.assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [List.append_assoc] at ht ⊢
          exact ⟨ht, hq⟩

theorem ct_post {α : Type} {P : State → State → Prop} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (h : RelCT isa P c (Two Φ)) (hΦ : ∀ a s, Φ a s → Ψ a s) : RelCT isa P c (Two Ψ) :=
  h.mono (fun _ _ h => h) fun _ _ h => two_mono hΦ h

theorem ct_pre {α : Type} {Q : State → State → Prop} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (h : RelCT isa (Two Ψ) c Q) (hΦ : ∀ a s, Φ a s → Ψ a s) : RelCT isa (Two Φ) c Q :=
  h.mono (fun _ _ h => two_mono hΦ h) fun _ _ h => h

theorem ct_map {α : Type} {Φ : α → State → Prop} (f : Nat → Prog isa) :
    ∀ (l : List Nat), l ≠ [] → (∀ c ∈ l, RelCT isa (Two Φ) (f c) (Two Φ)) →
      RelCT isa (Two Φ) (seqs (l.map f)) (Two Φ)
  | [], h, _ => absurd rfl h
  | [c], _, h => ct_one (h c (by simp))
  | c :: d :: l, _, h => ct_cons (List.cons_ne_nil _ _) (h c (by simp))
      (ct_map f (d :: l) (List.cons_ne_nil _ _) fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem ct_flat {α : Type} {Φ : α → State → Prop} (g : Nat → List (Prog isa)) (hg : ∀ c, g c ≠ []) :
    ∀ (l : List Nat), l ≠ [] → (∀ c ∈ l, RelCT isa (Two Φ) (seqs (g c)) (Two Φ)) →
      RelCT isa (Two Φ) (seqs (l.map g).flatten) (Two Φ)
  | [], h, _ => absurd rfl h
  | [c], _, h => by simpa using h c (by simp)
  | c :: d :: l, _, h => by
      rw [List.map_cons, List.flatten_cons]
      exact ct_app (hg c) (by simp [hg d]) (h c (by simp))
        (ct_flat g hg (d :: l) (List.cons_ne_nil _ _) fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ## Facts of the header -/

/-- The stage's `keep` a mask. -/
def MB (I : RpIn) (s : State) : Prop := ∃ b, word s.mem I.B (8 * sB2) = mask b

theorem stab_MB {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 216 ∨ 224 ≤ y) : Stab MB Q :=
  fun I s t P ⟨b, hb⟩ hf hP h1 h2 => ⟨b, stab_hdr (i := sB2) (by decide) (fun _ => mask b)
    (fun y hy => by have := hQ y hy; simp only [sB2, sFn]; omega_arith) I s t P hb hf hP h1 h2⟩

theorem stab_const (P : RpIn → Prop) {Q : Nat → Prop} : Stab (fun I _ => P I) Q :=
  fun _ _ _ _ h _ _ _ _ => h

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

/-- `GD` after `sB2 := mask b`. -/
theorem GD.setB {p : RpP} {s t : State} (h : GD w F p s) {b : Bool}
    (hm : t.mem = s.mem.writeW (off p.B (8 * sB2)) (mask b)) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) :
    GD w (fun I s => F I s ∧ MB I s) p t :=
  h.hdrW hm (by unfold DOk; simp only [sB2, sFn]; omega_arith) (by decide) k hr (fun e => absurd e (by decide))
    fun I e hFI => by
      have eB : p.B = I.B := (congrArg RpP.B e).symm
      have eZ : p.Z = I.Z := (congrArg RpP.Z e).symm
      have hZ := h.ws.h256
      rw [eB] at hm
      rw [eZ] at hZ
      obtain ⟨a, b'⟩ := stab_writeW hF hZ (by decide) hFI hm k.2.1 k.2.2
      exact ⟨a, _, b'⟩

theorem GD.mb {G : RpIn → State → Prop} {p : RpP} {s : State} (h : GD w (fun I s => G I s ∧ MB I s) p s) :
    ∃ b, word s.mem p.B (8 * sB2) = mask b := by
  obtain ⟨I, m₀, rfl, -, -, -, -, -, -, hb⟩ := h
  exact hb

theorem GD.fact {G : RpIn → State → Prop} {p : RpP} {s : State} (h : GD w G p s) :
    ∃ I, pubD I = p ∧ G I s := by
  obtain ⟨I, m₀, e, -, -, -, -, -, hG⟩ := h
  exact ⟨I, e, hG⟩

/-- A stage: the header's compare, then a branch on the width. -/
theorem stage_ct {rest : List Instr} {th el : Prog isa} {Ψ : RpP → State → Prop} (cnd : RpP → Bool) (hF : Arr F)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block rest) hc).isSome = true)
    (hhd : ∀ p s, GD w F p s → WP isa (.block (ws ++ rest)) s fun t => isa.eval .b t = some (cnd p) ∧
      t.mem = s.mem ∧ ∃ regs, Keep regs s t ∧ .rdi ∉ regs ∧ .rsp ∉ regs)
    (hth : RelCT isa (Two fun p s => GD w F p s ∧ cnd p = true) th (Two Ψ))
    (hel : RelCT isa (Two fun p s => GD w F p s ∧ cnd p = false) el (Two Ψ)) :
    RelCT isa (Two (GD w F)) (.seq (.block (ws ++ rest)) (.ite .b th el)) (Two Ψ) := by
  refine RelCT.seq (R := Two fun p t => GD w F p t ∧ isa.eval .b t = some (cnd p))
    (wsG_block_ct (F := F) (w := w) (fun _ _ h => h) ht fun p s h =>
      WP.mono (hhd p s h) fun t ⟨e, hm, regs, k, h1, h2⟩ => ⟨h.same hm k ⟨h1, h2⟩ hF, e⟩)
    (two_ite (fun p s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm) (ct_pre hth ?_) (ct_pre hel ?_))
  · intro p s ⟨⟨h, e⟩, e'⟩
    exact ⟨h, Option.some.inj (e.symm.trans e')⟩
  · intro p s ⟨⟨h, e⟩, e'⟩
    exact ⟨h, Option.some.inj (e.symm.trans e')⟩

/-- A copy of `n` words through `rsi` to `rbx`, both within the arrays. -/
theorem copyP_gd {blk : List Instr} (hF : Arr F) (n od os : RpP → Nat)
    (hblk : ∀ p s, GD w F p s → WP isa (.block blk) s fun u => u.gpr .r12 = BitVec.ofNat 64 (n p) ∧
      u.gpr .rsi = off p.B (os p) ∧ u.gpr .rbx = off p.B (od p) ∧ u.mem = s.mem ∧
      Keep [.r12, .r9, .rsi, .rbx] s u)
    (hb : ∀ p s, GD w F p s → 1 ≤ n p ∧ 256 ≤ od p ∧ od p + 8 * n p ≤ slot (w p.k) 16 ∧ 256 ≤ os p ∧
      os p + 8 * n p ≤ slot (w p.k) 16 ∧ (os p + 8 * n p ≤ od p ∨ od p + 8 * n p ≤ os p))
    (p : RpP) (s : State) (h : GD w F p s) : WP isa (.seq (.block blk) copyWords) s (GD w F p) := by
  obtain ⟨n1, d1, d2, s1, s2, sep⟩ := hb p s h
  have hw := h.ws
  have hn := hw.scr.nowrap
  have hZ := hw.hZ
  have hw2 := hw.w2
  have e16 := slotE (w p.k) 16
  refine WP.seq (WP.mono (hblk p s h) fun u ⟨h12, hsi, hbx, m, k⟩ => ?_)
  have hs := hw.scr.congr k.2.2
  refine WP.mono (copyWords_ok hsi hbx h12 n1 (by omega_arith) (by omega_arith)
    (fun i hi => hs.ld (by omega_arith)) (fun i hi => hs.st (by omega_arith))
    (fun i hi b hb => by rw [ofs_off p.B (by omega_arith)]; omega_arith)) fun t ⟨_, _, o, k'⟩ => ?_
  rw [m] at o
  exact h.out o d1 (by omega_arith) (k.trans k') (by decide) hF

theorem copyP_ct {rest : List Instr} (hF : Arr F) (n od os : RpP → Nat)
    (hblk : ∀ p s, GD w F p s → WP isa (.block (ws ++ rest)) s fun u => u.gpr .r12 = BitVec.ofNat 64 (n p) ∧
      u.gpr .rsi = off p.B (os p) ∧ u.gpr .rbx = off p.B (od p) ∧ u.mem = s.mem ∧
      Keep [.r12, .r9, .rsi, .rbx] s u)
    (hb : ∀ p s, GD w F p s → 1 ≤ n p ∧ 256 ≤ od p ∧ od p + 8 * n p ≤ slot (w p.k) 16 ∧ 256 ≤ os p ∧
      os p + 8 * n p ≤ slot (w p.k) 16 ∧ (os p + 8 * n p ≤ od p ∨ od p + 8 * n p ≤ os p))
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block rest) copyWords) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (.seq (.block (ws ++ rest)) copyWords) (Two (GD w F)) :=
  wsG_ct (fun _ _ h => h) ht (copyP_gd hF n od os hblk hb)

/-- `selK wd j t`, for `sB2` a mask. -/
theorem selK_eq (wd : Bool) (j t : Nat) : selK wd j t = .seq (.block (ws ++ ((if wd then wideR else []) ++
    (base j .r8 ++ (base t .rsi ++ ([.mov .rbp (.mem (hdr sB2))] : List Instr)))))) (wordLoop 0 selBody) := by
  simp only [selK, wsW, List.append_assoc]

theorem selK_ct (wd : Bool) {j t : Nat} (hj : j + (if wd then 2 else 1) ≤ 16) (ht' : t + (if wd then 2 else 1) ≤ 16)
    (hjt : ∀ w, slot w j + 8 * shlN wd w ≤ slot w t ∨ slot w t + 8 * shlN wd w ≤ slot w j) (hF : Arr F)
    (hb : ∀ p s, GD w F p s → ∃ b, word s.mem p.B (8 * sB2) = mask b) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if wd then wideR else []) ++
      (base j .r8 ++ (base t .rsi ++ ([.mov .rbp (.mem (hdr sB2))] : List Instr))))) (wordLoop 0 selBody))
      hc).isSome = true) :
    RelCT isa (Two (GD w F)) (selK wd j t) (Two (GD w F)) := by
  rw [selK_eq]
  exact wsG_ct (fun _ _ h => h) ht fun p s h => by
    have e : ws ++ ((if wd then wideR else []) ++ (base j .r8 ++ (base t .rsi ++
        ([.mov .rbp (.mem (hdr sB2))] : List Instr)))) = ws ++ (if wd then wideR else []) ++ base j .r8 ++
        base t .rsi ++ ([.mov .rbp (.mem (hdr sB2))] : List Instr) := by simp only [List.append_assoc]
    rw [e]
    exact sel_gd (fun _ _ h => h) wd hj ht' hjt hF (fun p s h => by
      obtain ⟨b, hb⟩ := hb p s h
      exact ⟨b, maskLd (by decide) h.ws.h256 hb⟩) p s h

end

/-! ## Shifts by bits, for what they change -/

theorem shrClF_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {j t c : Nat} {pre : List Instr}
    (hj : j < 16) (ht : t < 16) (hjt : j ≠ t) (hc : c < 64) (hpre : ClPre B Z s.mem pre c) :
    WP isa (shrCl false j t pre) s fun u =>
      Outside B (slot w t) (8 * w) s.mem u.mem ∧ Keep [.r12, .r9, .r8, .rsi, .rcx, .rax, .rdx, .r14] s u := by
  have hn := h.scr.nowrap
  have sj := h.sl hj
  have st := h.sl ht
  have pj := slot_far (w := w) hjt
  have hw1 := h.w1
  have hw2 := h.w2
  unfold shrCl
  refine WP.seq (WP.mono (clBlk_ok h false hpre) fun s₁ ⟨h12, h8, hsi, hcx, m₁, k₁⟩ => ?_)
  simp only [shlN, Bool.false_eq_true, ↓reduceIte] at h12
  refine WP.mono (shrCl_ok hc (h.scr.congr k₁.2.2) hsi h8 h12 hcx (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun u ⟨_, o, k₂⟩ => ?_
  rw [m₁] at o
  exact ⟨o, (k₁.trans k₂).mono (by simp)⟩

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

theorem shrCl_ct {j t : Nat} {pre : List Instr} (hj : j < 16) (ht' : t < 16) (hjt : j ≠ t) (hF : Arr F)
    (hpre : ∀ p s, GD w F p s → ∃ c, c < 64 ∧ ClPre p.B p.Z s.mem pre c) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .r8 ++ (base t .rsi ++ pre)))
      (wordLoop 0 shrClBody)) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (shrCl false j t pre) (Two (GD w F)) := by
  have e : shrCl false j t pre = .seq (.block (ws ++ (base j .r8 ++ (base t .rsi ++ pre)))) (wordLoop 0 shrClBody) := by
    simp only [shrCl, wsW, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.append_assoc]
  rw [e]
  exact wsG_ct (fun _ _ h => h) ht fun p s h => by
    rw [← e]
    obtain ⟨c, hc, hp⟩ := hpre p s h
    exact WP.mono (shrClF_ok h.ws hj ht' hjt hc hp) fun _ ⟨o, k⟩ =>
      h.out o (slot_256 _ _) (by have := slot_Z h ht'; omega_arith) k (by decide) hF

theorem shlCl_ct (wd : Bool) {j t : Nat} {pre : List Instr} (hj : j + (if wd then 2 else 1) ≤ 16)
    (ht' : t + (if wd then 2 else 1) ≤ 16)
    (hjt : ∀ w, slot w j + 8 * shlN wd w ≤ slot w t ∨ slot w t + 8 * shlN wd w ≤ slot w j) (hF : Arr F)
    (hpre : ∀ p s, GD w F p s → ∃ c, c < 64 ∧ ClPre p.B p.Z s.mem pre c) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if wd then wideR else []) ++
      (base j .r8 ++ (base t .rsi ++ (pre ++ ([.mov .rax (.mem (at0 .r8)), .shiftCl .shl .rax, .store (at0 .rsi) .rax] :
        List Instr)))))) (wordLoop 1 shlClBody)) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (shlCl wd j t pre) (Two (GD w F)) := by
  have e : shlCl wd j t pre = .seq (.block (ws ++ ((if wd then wideR else []) ++ (base j .r8 ++ (base t .rsi ++
      (pre ++ ([.mov .rax (.mem (at0 .r8)), .shiftCl .shl .rax, .store (at0 .rsi) .rax] : List Instr)))))))
      (wordLoop 1 shlClBody) := by
    simp only [shlCl, wsW, List.append_assoc]
  rw [e]
  exact wsG_ct (fun _ _ h => h) ht fun p s h => by
    rw [← e]
    obtain ⟨c, hc, hp⟩ := hpre p s h
    refine WP.mono (shlClP_ok h.ws wd hj ht' (hjt _) hc hp) fun _ ⟨_, o, k⟩ =>
      h.out o (slot_256 _ _) ?_ k (by decide) hF
    have r1 := slot_room (w := w p.k) ht'
    have r2 := h.ws.hZ
    cases wd <;> simp only [shlN, ↓reduceIte, Bool.false_eq_true] at r1 ⊢ <;> omega_arith

theorem testW_ct (both : Bool) {c : Nat} (hc1 : 1 ≤ c) (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8)
    (hw : ∀ p s, GD w F p s → c ≤ w p.k) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base 7 .rbx ++ (base 6 .r10 ++
      ([.mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))))
      (.seq (wordLoop 0 (if both then or2Body else or1Body)) (.block keepOf))) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (testW both c)) (Two (GD w fun I s => F I s ∧ MB I s)) := by
  have e : seqs (testW both c) = .seq (.seq (.block (ws ++ (base 7 .rbx ++ (base 6 .r10 ++
      ([.mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr)))))
      (wordLoop 0 (if both then or2Body else or1Body))) (.block keepOf) := by
    simp only [testW, seqs, List.append_assoc]
  rw [e]
  refine RelCT.assoc' (wsG_ct (fun _ _ h => h) ht fun p s h => WP.assoc ?_)
  rw [← e]
  exact WP.mono (testW_ok h.ws both hc1 (hw p s h)) fun _ ⟨hm, k⟩ => h.setB hm k (by decide) hFb

theorem testB_ct (both : Bool) {b : Nat} (hb1 : 1 ≤ b) (hb32 : b ≤ 32)
    (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base 7 .rbx ++ (base 6 .r10 ++
      (([.mov .rax (.mem (at0 .rbx))] : List Instr) ++ ((if both then [.alu .or .rax (.mem (at0 .r10))] else []) ++
      (([.shift .shl .rax (64 - b), .mov .rbp (.reg .rax)] : List Instr) ++ keepOf)))))) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (testB both b)) (Two (GD w fun I s => F I s ∧ MB I s)) := by
  have e : seqs (testB both b) = .block (ws ++ (base 7 .rbx ++ (base 6 .r10 ++
      (([.mov .rax (.mem (at0 .rbx))] : List Instr) ++ ((if both then [.alu .or .rax (.mem (at0 .r10))] else []) ++
      (([.shift .shl .rax (64 - b), .mov .rbp (.reg .rax)] : List Instr) ++ keepOf)))))) := by
    simp only [testB, seqs, List.append_assoc]
  rw [e]
  exact wsG_block_ct (fun _ _ h => h) ht fun p s h => by
    rw [← e]
    exact WP.mono (testB_ok h.ws both hb1 hb32) fun _ ⟨hm, k⟩ => h.setB hm k (by decide) hFb

theorem shrWords_ct {j c t : Nat} (hj : j < 16) (ht' : t < 16) (hjt : j ≠ t) (hc64 : c ≤ 64) (hF : Arr F)
    (hw : ∀ p s, GD w F p s → c + 1 ≤ w p.k) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base t .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] :
      List Instr) ++ (base j .rsi ++ (([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base t .rbx))))
      copyWords) hc₂).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (shrWords j c t)) (Two (GD w F)) := by
  have e : shrWords j c t = [zeroA t, .seq (.block (ws ++ (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] :
      List Instr) ++ (base j .rsi ++ (([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base t .rbx)))))
      copyWords] := by
    simp only [shrWords, List.append_assoc]
  rw [e]
  refine ct_cons (List.cons_ne_nil _ _) (zeroA_ct ht' hF ht₁) (ct_one (copyP_ct hF (fun p => w p.k - c)
    (fun p => slot (w p.k) t) (fun p => slot (w p.k) j + 8 * c) (fun p s h => ?_) (fun p s h => ?_) ht₂))
  · have e' : ws ++ (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base j .rsi ++
        (([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base t .rbx))) =
        ws ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ base j .rsi ++
        ([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base t .rbx := by
      simp only [List.append_assoc]
    rw [e']
    exact shrWB_ok h.ws hc64 (by have := hw p s h; omega_arith)
  · have := hw p s h
    have r1 := slot_room (w := w p.k) (j := j) (c := 1) (by omega_arith)
    have r2 := slot_room (w := w p.k) (j := t) (c := 1) (by omega_arith)
    have sep := slot_far (w := w p.k) hjt
    have := slot_256 (w p.k) t
    have := slot_256 (w p.k) j
    refine ⟨by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith⟩

theorem shlWordsT_ct {j c t : Nat} (hj : j + 2 ≤ 16) (ht' : t + 2 ≤ 16) (hjt : j + 2 ≤ t ∨ t + 2 ≤ j)
    (hc64 : c ≤ 64) (hF : Arr F) (hw : ∀ p s, GD w F p s → c + 2 ≤ w p.k) {hc₁ hc₂ hc₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base t .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base (t + 1) .r8)) zeroAccLoop)
      hc₂).isSome = true)
    (ht₃ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (wideR ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base j .rsi ++ (base t .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr)))))) copyWords) hc₃).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (shlWords true j c t)) (Two (GD w F)) := by
  have e : shlWords true j c t = [zeroA t, zeroA (t + 1), .seq (.block (ws ++ (wideR ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base j .rsi ++ (base t .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr))))))) copyWords] := by
    simp only [shlWords, wsW, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  refine ct_cons (List.cons_ne_nil _ _) (zeroA_ct (by omega_arith) hF ht₁)
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (by omega_arith) hF ht₂) (ct_one (copyP_ct hF
    (fun p => 2 * w p.k + 2 - c) (fun p => slot (w p.k) t + 8 * c) (fun p => slot (w p.k) j)
    (fun p s h => ?_) (fun p s h => ?_) ht₃)))
  · have e' : ws ++ (wideR ++ (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base j .rsi ++
        (base t .rbx ++ ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr))))) =
        wsW true ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ base j .rsi ++
        base t .rbx ++ ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) := by
      simp only [wsW, ↓reduceIte, List.append_assoc]
    rw [e']
    exact shlWB_ok h.ws hc64 (by have := hw p s h; omega_arith)
  · have := hw p s h
    have r1 := slot_room (w := w p.k) hj
    have r2 := slot_room (w := w p.k) ht'
    have := slot_256 (w p.k) t
    have := slot_256 (w p.k) j
    have sep : slot (w p.k) j + 2 * (8 * (w p.k + 2)) ≤ slot (w p.k) t ∨
        slot (w p.k) t + 2 * (8 * (w p.k + 2)) ≤ slot (w p.k) j := by
      rcases hjt with h' | h'
      · left; have := slot_mono (w := w p.k) h'; rw [slot_add] at this; omega_arith
      · right; have := slot_mono (w := w p.k) h'; rw [slot_add] at this; omega_arith
    refine ⟨by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith⟩

end

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

theorem GD.wkf {G : RpIn → State → Prop} {P : Nat → Prop} {p : RpP} {s : State} (h : GD w G p s)
    (hG : ∀ I s, G I s → P (w I.k)) : P (w p.k) := by
  obtain ⟨I, m₀, rfl, -, -, -, -, -, hI⟩ := h
  exact hG I s hI

theorem GD.kIn {G : RpIn → State → Prop} {P : Nat → Prop} {p : RpP} {s : State} (h : GD w G p s)
    (hp : P (w p.k)) : GD w (fun I s => G I s ∧ P (w I.k)) p s := by
  obtain ⟨I, m₀, rfl, h', L, O, he, hm, hI⟩ := h
  exact ⟨I, m₀, rfl, h', L, O, he, hm, hI, hp⟩

theorem arr_k (hF : Arr F) (P : Nat → Prop) : Arr fun I s => F I s ∧ P (w I.k) :=
  hF.and (stab_const _)

theorem arr_mb {G : RpIn → State → Prop} (hG : Arr G) : Arr fun I s => G I s ∧ MB I s :=
  hG.and (stab_MB fun y hy => .inr (by omega_arith))

theorem sel_far (j t : Nat) (hjt : j ≠ t) : ∀ w, slot w j + 8 * shlN false w ≤ slot w t ∨
    slot w t + 8 * shlN false w ≤ slot w j := fun w => by
  have := slot_far (w := w) hjt
  simp only [shlN, Bool.false_eq_true, ↓reduceIte]
  omega_arith

theorem sel_4_14 : ∀ w, slot w 4 + 8 * shlN true w ≤ slot w 14 ∨ slot w 14 + 8 * shlN true w ≤ slot w 4 :=
  fun w => by
    simp only [shlN, ↓reduceIte, slotE]
    omega_arith

/-- A stage of `c` words of the twos. -/
theorem stageW_ct (both : Bool) {c : Nat} (hc1 : 1 ≤ c) (hc64 : c ≤ 64) (hF : Arr F)
    (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) {h₀ h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₀ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 2)))] :
      List Instr)) h₀).isSome = true)
    (t₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base 7 .rbx ++ (base 6 .r10 ++
      ([.mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))))
      (.seq (wordLoop 0 (if both then or2Body else or1Body)) (.block keepOf))) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] :
      List Instr) ++ (base 7 .rsi ++ (([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base 14 .rbx))))
      copyWords) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] :
      List Instr) ++ (base 6 .rsi ++ (([.alu .add .rsi (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) ++ base 14 .rbx))))
      copyWords) h₃).isSome = true)
    (t₄ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (wideR ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base 4 .rsi ++ (base 14 .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr)))))) copyWords) h₄).isSome = true) :
    RelCT isa (Two (GD w F)) (stageW both c) (Two (GD w F)) := by
  unfold stageW
  refine stage_ct (cnd := fun p => decide (w p.k < c + 2)) hF t₀ (fun p s h => WP.mono (stageHd_ok h.ws hc64)
    fun t ⟨⟨hcf, hm⟩, k⟩ => ⟨by simp only [eval, hcf], hm, _, k, by decide⟩)
    (RelCT.block_nil fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1, h₂.1⟩) ?_
  have hG := arr_k (w := w) hF (fun x => c + 2 ≤ x)
  have hGB := arr_mb hG
  have hGb : Stab (fun I s => F I s ∧ c + 2 ≤ w I.k) fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8 :=
    hFb.and (stab_const _)
  refine ct_pre (Ψ := GD w fun I s => F I s ∧ c + 2 ≤ w I.k) ?_ fun p s ⟨h, hc⟩ =>
    h.kIn (P := fun x => c + 2 ≤ x) (by simp only [decide_eq_false_iff_not] at hc; omega_arith)
  have hw1 : ∀ p s, GD w (fun I s => (F I s ∧ c + 2 ≤ w I.k) ∧ MB I s) p s → c + 1 ≤ w p.k := fun p s h =>
    h.wkf (P := fun x => c + 1 ≤ x) fun I s hI => by have := hI.1.2; omega_arith
  have hw2 : ∀ p s, GD w (fun I s => (F I s ∧ c + 2 ≤ w I.k) ∧ MB I s) p s → c + 2 ≤ w p.k := fun p s h =>
    h.wkf (P := fun x => c + 2 ≤ x) fun I s hI => hI.1.2
  have hT := testW_ct (w := w) both hc1 hGb (fun p s h => h.wkf (P := fun x => c ≤ x) fun I s hI => by
    have := hI.2; omega_arith) t₁
  have hS7 := shrWords_ct (j := 7) (t := 14) (w := w) (by decide) (by decide) (by decide) hc64 hGB hw1
    (by taint_decide) t₂
  have hK7 := selK_ct (w := w) false (j := 7) (t := 14) (by decide) (by decide) (sel_far 7 14 (by decide)) hGB
    (fun _ _ h => h.mb) (by taint_decide)
  cases both
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
    exact ct_post (ct_app (by simp [testW]) (List.cons_ne_nil _ _)
      (ct_app (by simp [testW]) (by simp [shrWords]) hT hS7) (ct_one hK7)) fun p s h => h.mono fun I _ hI => hI.1.1
  · simp only [↓reduceIte]
    have hS6 := shrWords_ct (j := 6) (t := 14) (w := w) (by decide) (by decide) (by decide) hc64 hGB hw1
      (by taint_decide) t₃
    have hK6 := selK_ct (w := w) false (j := 6) (t := 14) (by decide) (by decide) (sel_far 6 14 (by decide)) hGB
      (fun _ _ h => h.mb) (by taint_decide)
    have hL4 := shlWordsT_ct (j := 4) (t := 14) (w := w) (by decide) (by decide) (by decide) hc64 hGB hw2
      (by taint_decide) (by taint_decide) t₄
    have hK4 := selK_ct (w := w) true (j := 4) (t := 14) (by decide) (by decide) sel_4_14 hGB
      (fun _ _ h => h.mb) (by taint_decide)
    exact ct_post (ct_app (by simp [testW]) (by simp [shrWords])
      (ct_app (by simp [testW]) (List.cons_ne_nil _ _)
        (ct_app (by simp [testW]) (by simp [shrWords]) hT hS7) (ct_one hK7))
      (ct_app (by simp [shrWords]) (by simp)
        (ct_app (by simp [shrWords]) (List.cons_ne_nil _ _)
          (ct_app (by simp [shrWords]) (by simp) hS6 (ct_one hK6)) hL4) (ct_one hK4)))
      fun p s h => h.mono fun I _ hI => hI.1.1

end

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

/-- A stage of `b` bits of the twos. -/
theorem stageB_ct (both : Bool) {b : Nat} (hb1 : 1 ≤ b) (hb32 : b ≤ 32) (hF : Arr F)
    (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base 7 .rbx ++ (base 6 .r10 ++
      (([.mov .rax (.mem (at0 .rbx))] : List Instr) ++ ((if both then [.alu .or .rax (.mem (at0 .r10))] else []) ++
      (([.shift .shl .rax (64 - b), .mov .rbp (.reg .rax)] : List Instr) ++ keepOf)))))) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base 7 .r8 ++ (base 14 .rsi ++ clOf b)))
      (wordLoop 0 shrClBody)) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base 6 .r8 ++ (base 14 .rsi ++ clOf b)))
      (wordLoop 0 shrClBody)) h₃).isSome = true)
    (t₄ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if true then wideR else []) ++
      (base 4 .r8 ++ (base 14 .rsi ++ (clOf b ++ ([.mov .rax (.mem (at0 .r8)), .shiftCl .shl .rax, .store (at0 .rsi) .rax] :
        List Instr)))))) (wordLoop 1 shlClBody)) h₄).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (stageB both b)) (Two (GD w F)) := by
  have hGB := arr_mb hF
  have hpre : ∀ p s, GD w (fun I s => F I s ∧ MB I s) p s → ∃ c, c < 64 ∧ ClPre p.B p.Z s.mem (clOf b) c :=
    fun _ _ _ => ⟨b, by omega_arith, clOf_pre (by omega_arith)⟩
  have hT := testB_ct (w := w) both hb1 hb32 hFb t₁
  have hS7 := shrCl_ct (w := w) (j := 7) (t := 14) (by decide) (by decide) (by decide) hGB hpre t₂
  have hK7 := selK_ct (w := w) false (j := 7) (t := 14) (by decide) (by decide) (sel_far 7 14 (by decide)) hGB
    (fun _ _ h => h.mb) (by taint_decide)
  unfold stageB
  cases both
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
    exact ct_post (ct_app (by simp [testB]) (List.cons_ne_nil _ _) hT (ct_cons (List.cons_ne_nil _ _) hS7 (ct_one hK7)))
      fun p s h => h.mono fun I _ hI => hI.1
  · simp only [↓reduceIte]
    have hS6 := shrCl_ct (w := w) (j := 6) (t := 14) (by decide) (by decide) (by decide) hGB hpre t₃
    have hK6 := selK_ct (w := w) false (j := 6) (t := 14) (by decide) (by decide) (sel_far 6 14 (by decide)) hGB
      (fun _ _ h => h.mb) (by taint_decide)
    have hL4 := shlCl_ct (w := w) true (j := 4) (t := 14) (by decide) (by decide) sel_4_14 hGB hpre t₄
    have hK4 := selK_ct (w := w) true (j := 4) (t := 14) (by decide) (by decide) sel_4_14 hGB
      (fun _ _ h => h.mb) (by taint_decide)
    exact ct_post (ct_app (by simp [testB]) (List.cons_ne_nil _ _)
      (ct_app (by simp [testB]) (List.cons_ne_nil _ _) hT (ct_cons (List.cons_ne_nil _ _) hS7 (ct_one hK7)))
      (ct_cons (List.cons_ne_nil _ _) hS6 (ct_cons (List.cons_ne_nil _ _) hK6
        (ct_cons (List.cons_ne_nil _ _) hL4 (ct_one hK4)))))
      fun p s h => h.mono fun I _ hI => hI.1

end

/-- The twos' stages, at the narrow width. -/
theorem twos_ct {F : RpIn → State → Prop} (hF : Arr F) (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) :
    RelCT isa (Two (GD nv F)) (seqs twos) (Two (GD nv F)) := by
  have hg : ∀ (both : Bool) (c : Nat), stageB both c ≠ [] := fun _ _ => by simp [stageB, testB]
  have hW : ∀ both : Bool, ∀ c ∈ wordStages, RelCT isa (Two (GD nv F)) (stageW both c) (Two (GD nv F)) := by
    intro both c hc
    simp only [wordStages, List.mem_cons, List.not_mem_nil, or_false] at hc
    cases both <;> rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stageW_ct _ (by decide) (by decide) hF hFb (by taint_decide) (by taint_decide) (by taint_decide)
        (by taint_decide) (by taint_decide)
  have hB : ∀ both : Bool, ∀ c ∈ bitStages, RelCT isa (Two (GD nv F)) (seqs (stageB both c)) (Two (GD nv F)) := by
    intro both c hc
    simp only [bitStages, List.mem_cons, List.not_mem_nil, or_false] at hc
    cases both <;> rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stageB_ct _ (by decide) (by decide) hF hFb (by taint_decide) (by taint_decide) (by taint_decide)
        (by taint_decide)
  unfold twos
  exact ct_app (by simp [wordStages, bitStages, stageB, testB]) (by simp [bitStages, stageB, testB])
    (ct_app (by simp [wordStages, bitStages, stageB, testB]) (by simp [wordStages])
      (ct_app (by simp [wordStages]) (by simp [bitStages, stageB, testB])
        (ct_map _ wordStages (by simp [wordStages]) (hW true))
        (ct_flat _ (hg true) bitStages (by simp [bitStages]) (hB true)))
      (ct_map _ wordStages (by simp [wordStages]) (hW false)))
    (ct_flat _ (hg false) bitStages (by simp [bitStages]) (hB false))

end VG.Proof.Rsa.X86_64.Rd
