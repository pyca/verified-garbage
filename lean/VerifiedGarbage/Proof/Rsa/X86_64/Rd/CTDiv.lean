module

public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTWords
public import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Divs
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTParts
import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Prod
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTWords
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Divs
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.CTParts
meta import VerifiedGarbage.Proof.Rsa.X86_64.Rd.Prod
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_recover_primes_det` on x86-64: constant time, the divisions' pieces

The leading zeros (`clzTop`) into `sC`, below 64 (`MC`); the shifts by them;
`divB`'s normalization by stages, which ends with the divisor's top bit set
(`FD`); `b²` by rows of `v` words. All at the wide width `W = 2 h + 4`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Rd

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.RecoverDet
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Rsa.X86_64 (copyWords)

theorem wW_eq (k : Nat) : wW k = 2 * wk k + 4 := by simp only [wW, nv]; omega_arith

/-- `sC`, below 64. -/
def MC (I : RpIn) (s : State) : Prop := ∃ z, z < 64 ∧ word s.mem I.B (8 * sC) = BitVec.ofNat 64 z

theorem stab_MC {Q : Nat → Prop} (hQ : ∀ y, Q y → y < 240 ∨ 248 ≤ y) : Stab MC Q :=
  fun I s t P ⟨z, hz, e⟩ hf hP h1 h2 => ⟨z, hz, stab_hdr (i := sC) (by decide) (fun _ => BitVec.ofNat 64 z)
    (fun y hy => by have := hQ y hy; simp only [sC, sFn]; omega_arith) I s t P e hf hP h1 h2⟩

theorem arr_mc {G : RpIn → State → Prop} (hG : Arr G) : Arr fun I s => G I s ∧ MC I s :=
  hG.and (stab_MC fun y hy => .inr (by omega_arith))

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

theorem GD.kb {p : RpP} {s : State} (h : GD w F p s) : 8 ≤ wk p.k ∧ wk p.k ≤ 128 := by
  obtain ⟨I, m₀, rfl, -, L, -⟩ := h
  have := L.k1
  have := L.k2
  show 8 ≤ wk I.k ∧ wk I.k ≤ 128
  unfold wk; omega_arith

/-- `GD` after `sC := z`, `z < 64`. -/
theorem GD.setC {p : RpP} {s t : State} (h : GD w F p s) {z : Nat} (hz : z < 64)
    (hm : t.mem = s.mem.writeW (off p.B (8 * sC)) (BitVec.ofNat 64 z)) {regs : List Reg} (k : Keep regs s t)
    (hr : .rdi ∉ regs ∧ .rsp ∉ regs) (hF : Stab F fun y => 8 * sC ≤ y ∧ y < 8 * sC + 8) :
    GD w (fun I s => F I s ∧ MC I s) p t :=
  h.hdrW hm (by unfold DOk; simp only [sC, sFn]; omega_arith) (by decide) k hr (fun e => absurd e (by decide))
    fun I e hFI => by
      have eB : p.B = I.B := (congrArg RpP.B e).symm
      have eZ : p.Z = I.Z := (congrArg RpP.Z e).symm
      have hZ := h.ws.h256
      rw [eB] at hm
      rw [eZ] at hZ
      obtain ⟨a, b'⟩ := stab_writeW hF hZ (by decide) hFI hm k.2.1 k.2.2
      exact ⟨a, _, hz, b'⟩

theorem GD.mc {G : RpIn → State → Prop} {p : RpP} {s : State} (h : GD w (fun I s => G I s ∧ MC I s) p s) :
    ∃ c, c < 64 ∧ ClPre p.B p.Z s.mem [.mov .rcx (.mem (hdr sC))] c := by
  obtain ⟨I, m₀, rfl, h', -, -, -, -, -, z, hz, e⟩ := h
  exact ⟨z, hz, sC_pre h'.ws.h256 e⟩

theorem clzTop_ct {j : Nat} (hj : j < 16) (hFc : Stab F fun y => 8 * sC ≤ y ∧ y < 8 * sC + 8)
    (hw6 : ∀ p s, GD w F p s → 6 ≤ w p.k) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (base j .rbx ++ (hOf ++
      (([.mov .rdx (.mem (ix .rbx .r12 (-8))), .mov32 .r11 (.imm 0)] : List Instr) ++
      (([32, 16, 8, 4, 2, 1].map clzStage).flatten ++ ([.store (hdr sC) .r11] : List Instr)))))) hc).isSome = true) :
    RelCT isa (Two (GD w F)) (.block (clzTop j)) (Two (GD w fun I s => F I s ∧ MC I s)) := by
  have e : clzTop j = ws ++ (base j .rbx ++ (hOf ++ (([.mov .rdx (.mem (ix .rbx .r12 (-8))), .mov32 .r11 (.imm 0)] :
      List Instr) ++ (([32, 16, 8, 4, 2, 1].map clzStage).flatten ++ ([.store (hdr sC) .r11] : List Instr))))) := by
    simp only [clzTop, List.append_assoc]
  rw [e]
  exact wsG_block_ct (fun _ _ h => h) ht fun p s h => by
    rw [← e]
    exact WP.mono (clzTop_ok h.ws hj (hw6 p s h)) fun _ ⟨hm, k⟩ => h.setC (by omega_arith) hm k (by decide) hFc

theorem shlZ_ct {a d : Nat} (ha : a < 16) (hd : d < 16) (had : a ≠ d) {G : RpIn → State → Prop} (hG : Arr G)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if false then wideR else []) ++
      (base a .r8 ++ (base d .rsi ++ (([.mov .rcx (.mem (hdr sC))] : List Instr) ++
      ([.mov .rax (.mem (at0 .r8)), .shiftCl .shl .rax, .store (at0 .rsi) .rax] : List Instr))))))
      (wordLoop 1 shlClBody)) hc).isSome = true) :
    RelCT isa (Two (GD w fun I s => G I s ∧ MC I s)) (shlZ a d) (Two (GD w fun I s => G I s ∧ MC I s)) :=
  shlCl_ct false (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_arith)
    (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_arith) (sel_far a d had) (arr_mc hG)
    (fun _ _ h => h.mc) ht

theorem shrZ_ct {a d : Nat} (ha : a < 16) (hd : d < 16) (had : a ≠ d) {G : RpIn → State → Prop} (hG : Arr G)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base a .r8 ++ (base d .rsi ++
      ([.mov .rcx (.mem (hdr sC))] : List Instr)))) (wordLoop 0 shrClBody)) hc).isSome = true) :
    RelCT isa (Two (GD w fun I s => G I s ∧ MC I s)) (shrZ a d) (Two (GD w fun I s => G I s ∧ MC I s)) :=
  shrCl_ct ha hd had (arr_mc hG) (fun _ _ h => h.mc) ht

theorem shlWordsF_ct {j c t : Nat} (hj : j < 16) (ht' : t < 16) (hjt : j ≠ t) (hc64 : c ≤ 128) (hF : Arr F)
    (hw : ∀ p s, GD w F p s → c + 1 ≤ w p.k) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base t .r8)) zeroAccLoop) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if false then wideR else []) ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base j .rsi ++ (base t .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr)))))) copyWords) hc₂).isSome = true) :
    RelCT isa (Two (GD w F)) (seqs (shlWords false j c t)) (Two (GD w F)) := by
  have e : shlWords false j c t = [zeroA t, .seq (.block (ws ++ ((if false then wideR else []) ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base j .rsi ++ (base t .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr))))))) copyWords] := by
    simp only [shlWords, wsW, Bool.false_eq_true, ↓reduceIte, List.append_assoc, List.cons_append,
      List.nil_append, List.append_nil]
  rw [e]
  refine ct_cons (List.cons_ne_nil _ _) (zeroA_ct ht' hF ht₁) (ct_one (copyP_ct hF
    (fun p => w p.k - c) (fun p => slot (w p.k) t + 8 * c) (fun p => slot (w p.k) j)
    (fun p s h => ?_) (fun p s h => ?_) ht₂))
  · have e' : ws ++ ((if false then wideR else []) ++ (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++
        (base j .rsi ++ (base t .rbx ++ ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr))))) =
        wsW false ++ ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ base j .rsi ++
        base t .rbx ++ ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr) := by
      simp only [wsW, List.append_assoc]
    rw [e']
    exact shlWBN_ok h.ws hc64 (by have := hw p s h; omega_arith)
  · have := hw p s h
    have r1 := slot_room (w := w p.k) (j := j) (c := 1) (by omega_arith)
    have r2 := slot_room (w := w p.k) (j := t) (c := 1) (by omega_arith)
    have sep := slot_far (w := w p.k) hjt
    have := slot_256 (w p.k) t
    have := slot_256 (w p.k) j
    refine ⟨by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith⟩

theorem testTop_ct {j c : Nat} (hj : j < 16) (hc1 : 1 ≤ c) (hc64 : c ≤ 64)
    (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) (hw : ∀ p s, GD wW F p s → c ≤ wk p.k)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rbx ++ (hOf ++
      ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c)), .shift .shl .r12 3, .alu .add .rbx (.reg .r12),
        .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))))
      (.seq (wordLoop 0 or1Body) (.block keepOf))) hc).isSome = true) :
    RelCT isa (Two (GD wW F)) (seqs (testTop j c)) (Two (GD wW fun I s => F I s ∧ MB I s)) := by
  have e : seqs (testTop j c) = .seq (.seq (.block (ws ++ (base j .rbx ++ (hOf ++
      ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c)), .shift .shl .r12 3, .alu .add .rbx (.reg .r12),
        .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr)))))
      (wordLoop 0 or1Body)) (.block keepOf) := by
    simp only [testTop, seqs, List.append_assoc]
  rw [e]
  refine RelCT.assoc' (wsG_ct (fun _ _ h => h) ht fun p s h => WP.assoc ?_)
  rw [← e]
  exact WP.mono (testTop_ok h.ws (wW_eq p.k) hj hc1 (hw p s h) hc64) fun _ ⟨hm, k⟩ => h.setB hm k (by decide) hFb

/-- A stage of `c` words of `divB`'s normalization. -/
theorem stageD_ct {c : Nat} (hc1 : 1 ≤ c) (hc64 : c ≤ 64) (hF : Arr F)
    (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8) {h₀ h₁ h₂ h₃ : VG.Taint.Hint VG.X86_64.Taint.T}
    (t₀ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block (hOf ++
      ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 1)))] : List Instr))) h₀).isSome = true)
    (t₁ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base 2 .rbx ++ (hOf ++
      ([.alu .sub .r12 (.imm (BitVec.ofNat 32 c)), .shift .shl .r12 3, .alu .add .rbx (.reg .r12),
        .mov32 .rbp (.imm 0), .mov32 .r12 (.imm (BitVec.ofNat 32 c))] : List Instr))))
      (.seq (wordLoop 0 or1Body) (.block keepOf))) h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if false then wideR else []) ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base 2 .rsi ++ (base 3 .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr)))))) copyWords) h₂).isSome = true)
    (t₃ : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ((if false then wideR else []) ++
      (([.alu .sub .r12 (.imm (BitVec.ofNat 32 c))] : List Instr) ++ (base 5 .rsi ++ (base 3 .rbx ++
      ([.alu .add .rbx (.imm (BitVec.ofNat 32 (8 * c)))] : List Instr)))))) copyWords) h₃).isSome = true) :
    RelCT isa (Two (GD wW F)) (stageD c) (Two (GD wW F)) := by
  unfold stageD
  have e : ws ++ hOf ++ ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 1)))] : List Instr) =
      ws ++ (hOf ++ ([.alu .cmp .r12 (.imm (BitVec.ofNat 32 (c + 1)))] : List Instr)) := by
    simp only [List.append_assoc]
  rw [e]
  refine stage_ct (cnd := fun p => decide (wk p.k < c + 1)) hF t₀ (fun p s h => by
    rw [← e]
    exact WP.mono (stageDHd_ok h.ws (wW_eq p.k) hc64) fun t ⟨⟨hcf, hm⟩, k⟩ =>
      ⟨by simp only [eval, hcf], hm, _, k, by decide⟩)
    (RelCT.block_nil fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1, h₂.1⟩) ?_
  have hG := hF.and (stab_const (Q := fun y => 256 ≤ y) fun I => c + 1 ≤ wk I.k)
  have hGB := arr_mb hG
  have hGb : Stab (fun I s => F I s ∧ c + 1 ≤ wk I.k) fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8 :=
    hFb.and (stab_const _)
  refine ct_pre (Ψ := GD wW fun I s => F I s ∧ c + 1 ≤ wk I.k) ?_ fun p s ⟨h, hc⟩ => by
    obtain ⟨I, m₀, rfl, h', L, O, he, hm, hFI⟩ := h
    exact ⟨I, m₀, rfl, h', L, O, he, hm, hFI, by simp only [decide_eq_false_iff_not] at hc; change ¬ wk I.k < c + 1 at hc; show c + 1 ≤ wk I.k; omega_arith⟩
  have hwk : ∀ p s, GD wW (fun I s => (F I s ∧ c + 1 ≤ wk I.k) ∧ MB I s) p s → c + 1 ≤ wk p.k := fun p s h => by
    obtain ⟨I, m₀, rfl, -, -, -, -, -, hI, -⟩ := h
    exact hI.2
  have hT := testTop_ct (j := 2) (by decide) hc1 hc64 hGb (fun p s h => by
    obtain ⟨I, m₀, rfl, -, -, -, -, -, hI⟩ := h
    have := hI.2; show c ≤ wk I.k; omega_arith) t₁
  have hS2 := shlWordsF_ct (j := 2) (t := 3) (w := wW) (by decide) (by decide) (by decide) (by omega_arith) hGB
    (fun p s h => by have := hwk p s h; have := wW_eq p.k; omega_arith) (by taint_decide) t₂
  have hK2 := selK_ct (w := wW) false (j := 2) (t := 3) (by decide) (by decide) (sel_far 2 3 (by decide)) hGB
    (fun _ _ h => h.mb) (by taint_decide)
  have hS5 := shlWordsF_ct (j := 5) (t := 3) (w := wW) (by decide) (by decide) (by decide) (by omega_arith) hGB
    (fun p s h => by have := hwk p s h; have := wW_eq p.k; omega_arith) (by taint_decide) t₃
  have hK5 := selK_ct (w := wW) false (j := 5) (t := 3) (by decide) (by decide) (sel_far 5 3 (by decide)) hGB
    (fun _ _ h => h.mb) (by taint_decide)
  exact ct_post (ct_app (by simp [testTop]) (List.cons_ne_nil _ _)
    (ct_app (by simp [testTop]) (by simp [shlWords])
      (ct_app (by simp [testTop]) (List.cons_ne_nil _ _)
        (ct_app (by simp [testTop]) (by simp [shlWords]) hT hS2) (ct_one hK2)) hS5) (ct_one hK5))
    fun p s h => h.mono fun I _ hI => hI.1.1

end

/-- The divisor's top bit set: `qDiv`'s normalization. -/
def FD (I : RpIn) (s : State) : Prop := 2 ^ 63 ≤ (word s.mem I.B (slot (wW I.k) qD + 8 * (wk I.k - 1))).toNat

section
variable {w : Nat → Nat} {F : RpIn → State → Prop}

theorem GD.add {G : RpIn → State → Prop} {p : RpP} {s : State} (h : GD w F p s) (hG : ∀ I, pubD I = p → G I s) :
    GD w (fun I s => F I s ∧ G I s) p s := by
  obtain ⟨I, m₀, rfl, h', L, O, he, hm, hFI⟩ := h
  exact ⟨I, m₀, rfl, h', L, O, he, hm, hFI, hG I rfl⟩

/-- `normDN`'s last block: the divisor's top bit set. -/
theorem forceTop_ct (hF : Arr F) :
    RelCT isa (Two (GD wW F)) (.block (ws ++ base 8 .r10 ++ hOf ++ ([.mov .rax (.mem (ix .r10 .r12 (-8))),
      .movImm64 .rdx 9223372036854775808, .alu .or .rax (.reg .rdx), .store (ix .r10 .r12 (-8)) .rax] : List Instr)))
      (Two (GD wW fun I s => F I s ∧ FD I s)) := by
  have e : ws ++ base 8 .r10 ++ hOf ++ ([.mov .rax (.mem (ix .r10 .r12 (-8))),
      .movImm64 .rdx 9223372036854775808, .alu .or .rax (.reg .rdx), .store (ix .r10 .r12 (-8)) .rax] : List Instr) =
      ws ++ (base 8 .r10 ++ (hOf ++ ([.mov .rax (.mem (ix .r10 .r12 (-8))),
      .movImm64 .rdx 9223372036854775808, .alu .or .rax (.reg .rdx), .store (ix .r10 .r12 (-8)) .rax] :
        List Instr))) := by simp only [List.append_assoc]
  rw [e]
  exact wsG_block_ct (fun _ _ h => h) (by taint_decide) fun p s h => by
    rw [← e]
    have kb := h.kb
    have hw := h.ws
    have hn := hw.scr.nowrap
    have sl := slot_Z h (j := 8) (by decide)
    have e8 := slot_room (w := wW p.k) (j := 8) (c := 1) (by decide)
    have hWh := wW_eq p.k
    refine WP.mono (forceTop_ok hw hWh (by omega_arith)) fun t ⟨hm, k⟩ => ?_
    have o : Outside p.B (slot (wW p.k) 8 + 8 * (wk p.k - 1)) 8 s.mem t.mem := by
      rw [hm]; exact writeW_outside _ _ _ (by omega_arith)
    refine (h.out o (by have := slot_256 (wW p.k) 8; omega_arith) (by omega_arith) k (by decide) hF).add
      fun I e' => ?_
    subst e'
    show 2 ^ 63 ≤ (word t.mem I.B (slot (wW I.k) qD + 8 * (wk I.k - 1))).toNat
    rw [hm]
    show 2 ^ 63 ≤ (word (s.mem.writeW (off I.B (slot (wW I.k) 8 + 8 * (wk I.k - 1))) _) I.B
      (slot (wW I.k) 8 + 8 * (wk I.k - 1))).toNat
    rw [word_writeW_self]
    exact top_or _

theorem normDN_ct (hF : Arr F) (hFb : Stab F fun y => 8 * sB2 ≤ y ∧ y < 8 * sB2 + 8)
    (hFc : Stab F fun y => 8 * sC ≤ y ∧ y < 8 * sC + 8) :
    RelCT isa (Two (GD wW F)) (seqs normDN) (Two (GD wW fun I s => (F I s ∧ MC I s) ∧ FD I s)) := by
  have hS : ∀ c ∈ wordStages, RelCT isa (Two (GD wW F)) (stageD c) (Two (GD wW F)) := by
    intro c hc
    simp only [wordStages, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact stageD_ct (by decide) (by decide) hF hFb (by taint_decide) (by taint_decide) (by taint_decide)
        (by taint_decide)
  have hC := arr_mc hF
  unfold normDN
  exact ct_app (by simp [wordStages]) (List.cons_ne_nil _ _) (ct_map _ wordStages (by simp [wordStages]) hS)
    (ct_cons (List.cons_ne_nil _ _) (clzTop_ct (j := 2) (by decide) hFc (fun p s h => by
      have := h.kb; have := wW_eq p.k; omega_arith) (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 8) (by decide) hC (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (shlZ_ct (a := 2) (d := 8) (by decide) (by decide) (by decide) hF (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (zeroA_ct (j := 9) (by decide) hC (by taint_decide))
    (ct_cons (List.cons_ne_nil _ _) (shlZ_ct (a := 5) (d := 9) (by decide) (by decide) (by decide) hF (by taint_decide))
    (ct_one (forceTop_ct hC)))))))

end

open VG.Impl.Rsa.X86_64.Keys.Recover (aE aD aM prodInit rowHead rowNext) in
/-- `prodB`'s loop, from `M = 0`, for what it changes. -/
theorem prodBLoop_frm {s : State} {B : Addr} {Z w u : Nat} (h : Ws s B Z w) (hwu : w = 2 * u + 2) (hu : 1 ≤ u)
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (8 * u))
    (hz : wv s.mem B (slot w aM) (2 * (w + 2)) = 0) :
    WP isa (.seq (.block (prodInit ++ ([.shift .shr .r12 1, .alu .sub .r12 (.imm 1)] : List Instr)))
      (.loop (.seq (.block rowHead) (.seq mulAddRow (.block rowNext))) .ne)) s fun t =>
      Outside B (slot w aM) (16 * (w + 2)) s.mem t.mem ∧ Keep mmRegs s t := by
  have hZ := h.hZ
  have hw1 := h.w1
  have hw2 := h.w2
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (prodInit_ok h hel (by omega_arith))
    fun s₃ ⟨h12, hbx, h10, h15, h11, h13, hdi, m₃, k₃⟩ =>
    WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 u ∧ t.mem = s₃.mem)
      (by xrun [h12, half1_ofNat (W := w) (by omega_arith) (by omega_arith), show w / 2 - 1 = u by omega_arith])
      rfl) fun s₄ ⟨⟨h12', m₄⟩, k₄⟩ => (show WP isa (.loop _ .ne) s₄ _ from ?_)))
  have hs₄ := h.scr.congr (k₃.trans k₄).2.2
  rw [show (8 * u + 7) / 8 = u by omega_arith] at h11
  refine wp_upto (a := 0) (N := u) hu (ProdInv s₄ B Z w u)
    (fun j _ hj t hI => prodStep_ok hI hu (by omega_arith) (by omega_arith) hZ (by omega_arith) hj h12'
      ((k₄.gpr (by decide)).trans hbx) ((k₄.gpr (by decide)).trans h10) ((k₄.gpr (by decide)).trans h15)
      ((k₄.gpr (by decide)).trans h11))
    (fun t hI => ?_) ⟨hs₄, Keep.refl _ _, (k₄.gpr (by decide)).trans h13, Outside.refl _ _ _ _,
      by rw [m₄, m₃, hz, wv, Nat.mul_zero]⟩
  exact ⟨fun x hx => by rw [hI.out x hx, m₄, m₃], ((k₃.trans k₄).trans hI.keep).mono (by simp [mmRegs])⟩

/-- The registers `prodB`'s loop needs pinned. -/
def prodBVal (p : RpP) : Reg → BitVec 64
  | .rdi => p.B
  | .r12 => BitVec.ofNat 64 (nv p.k)
  | .rbx => off p.B (slot (wW p.k) Recover.aE)
  | .r10 => off p.B (slot (wW p.k) Recover.aM)
  | .r15 => off p.B (slot (wW p.k) Recover.aD)
  | .r11 => BitVec.ofNat 64 (nv p.k)
  | .r13 => BitVec.ofNat 64 0
  | _ => 0

section
variable {F : RpIn → State → Prop}

theorem prodB_ct (hF : Arr F)
    (hel : ∀ p s, GD wW F p s → word s.mem p.B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 (8 * nv p.k)) :
    RelCT isa (Two (GD wW F)) (seqs prodB) (Two (GD wW F)) := by
  simp only [prodB, seqs]
  refine RelCT.seq (zeroM_ct hF) (RelCT.seq (zeroM1_ct hF) ?_)
  refine pin_ct [.rdi] [.rdi, .r12, .rbx, .r10, .r15, .r11, .r13] prodBVal pins_GD (by taint_decide)
    (fun p s h => ?_) (by taint_decide) fun p s h => ?_
  · have e1 := hel p s (h.mono fun _ _ h => h.1)
    have hw := h.ws
    have hw2 := hw.w2
    have hWv : wW p.k = 2 * nv p.k + 2 := rfl
    rw [WP.block_append_iff]
    refine WP.mono (prodInit_ok hw e1 (by omega_arith)) fun s₃ ⟨h12, hbx, h10, h15, h11, h13, hdi, m₃, k₃⟩ => ?_
    refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (nv p.k))
      (by xrun [h12, half1_ofNat (W := wW p.k) (by omega_arith) (by omega_arith),
        show wW p.k / 2 - 1 = nv p.k by omega_arith]) rfl) fun t ⟨h12', k₄⟩ r hr => ?_
    rw [show (8 * nv p.k + 7) / 8 = nv p.k by omega_arith] at h11
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (k₄.gpr (by decide)).trans hdi
    · exact h12'
    · exact (k₄.gpr (by decide)).trans hbx
    · exact (k₄.gpr (by decide)).trans h10
    · exact (k₄.gpr (by decide)).trans h15
    · exact (k₄.gpr (by decide)).trans h11
    · exact (k₄.gpr (by decide)).trans h13
  · have e1 := hel p s (h.mono fun _ _ h => h.1)
    have hz : wv s.mem p.B (slot (wW p.k) Recover.aM) (2 * (wW p.k + 2)) = 0 := by
      obtain ⟨I, m₀, rfl, -, -, -, -, -, -, z⟩ := h; exact z
    have hw := h.ws
    have hWv : wW p.k = 2 * nv p.k + 2 := rfl
    have sl := hw.sl (j := Recover.aM + 1) (by decide)
    have eM1 : slot (wW p.k) (Recover.aM + 1) = slot (wW p.k) Recover.aM + 8 * (wW p.k + 2) := by
      simp only [Bignum.slot, hdrBytes, Recover.aM]; omega_arith
    exact WP.mono (prodBLoop_frm hw hWv (by simp only [nv]; omega_arith) e1 hz) fun t ⟨o, k⟩ =>
      (h.mono (F' := F) fun _ _ h => h.1).out o (slot_256 _ _) (by omega_arith) k (by decide) hF

end

end VG.Proof.Rsa.X86_64.Rd
