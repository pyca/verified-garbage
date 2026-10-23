module

import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedExp
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
public import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
import VerifiedGarbage.Proof.Rsa.X86_64.RpSq
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.X86_64.RpBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedExp
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpBase
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces

/-! # Timing of the folded recovery masks and comparisons -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Impl.Rsa.X86_64.Keys.Recover VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open VG.Impl.Bignum.X86_64.Public (aX aY sMask)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open Rp

/-- The initial comparison is secret arithmetic; `ws` then pins its public sizes. -/
theorem maskSetup_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block (([.alu .cmp .rbp (.imm 1), .alu .sbb .rdx (.reg .rdx)] : List Instr) ++ ws)) s
      fun u => ∀ r ∈ [Reg.rdi, .r12, .r9], u.gpr r = wsVal B w r := by
  rw [WP.block_append_iff]
  refine WP.mono (minusMask_ok (em := decide (s.gpr .rbp = 0)) rfl) fun s₁ ⟨_, m₁, k₁⟩ => ?_
  have h₁ := h.congrG (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) k₁ (by decide)
  refine WP.mono h₁.ws_ok fun u ⟨h12, h9, _, k₂⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (k₂.gpr (by decide)).trans h₁.rdi
  · exact h12
  · exact h9

/-- Indexed flag accesses and masked selection depend only on the public width. -/
theorem capturePrefix_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) (j : Option Nat)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.seq (.block (base aRoot .r8 ++ base aY .rsi ++ enabled j ++ captureCore)) (wordLoop 0 selBody)) hint).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (capturePrefix j) s (Ψ a)) :
    RelCT isa (Two Φ) (capturePrefix j) (Two Ψ) := by
  have e : capturePrefix j = .seq (.block (
      (([.alu .cmp .rbp (.imm 1), .alu .sbb .rdx (.reg .rdx)] : List Instr) ++ ws) ++
      (base aRoot .r8 ++ base aY .rsi ++ enabled j ++ captureCore))) (wordLoop 0 selBody) := by
    simp only [capturePrefix, captureMasks, List.append_assoc]
  rw [e]
  refine RelCT.block_seq (pin_ct [.rdi] [.rdi, .r12, .r9] (fun a => wsVal (B a) (w a))
    (fun a s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hws a s₁ h₁).rdi, (hws a s₂ h₂).rdi])
    (by taint_decide) (fun a s h => maskSetup_ok (hws a s h)) ht fun a s h => ?_)
  exact WP.block_seq_iff.mp (e ▸ hw a s h)

/-- Resetting on a secret digit changes masks, without changing addresses. -/
theorem resetMasks_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a))
    (hw : ∀ a s, Φ a s → WP isa (.block resetMasks) s (Ψ a)) :
    RelCT isa (Two Φ) (.block resetMasks) (Two Ψ) := by
  have e : resetMasks = (([.alu .cmp .rbp (.imm 1), .alu .sbb .rdx (.reg .rdx)] : List Instr) ++ ws) ++
      (base aRoot .r8 ++ resetCore) := by simp only [resetMasks, List.append_assoc]
  rw [e]
  refine RelCT.block_append (pin_ct [.rdi] [.rdi, .r12, .r9] (fun a => wsVal (B a) (w a))
    (fun a s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hws a s₁ h₁).rdi, (hws a s₂ h₂).rdi])
    (by taint_decide) (fun a s h => maskSetup_ok (hws a s h)) (by taint_decide) fun a s h => ?_)
  exact WP.seq_iff.mpr (WP.block_append_iff.mp (e ▸ hw a s h))

theorem eqWorkspace_gct {α : Type} (B : α → Addr) (Z w : α → Nat) {a b : Nat}
    (ha : a < 16) (hb : b < 16) {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.seq (.block (base a .rbx ++ (base b .r10 ++ ([.mov32 .rbp (.imm 0)] : List Instr)))) (wordLoop 0 xorBody)) hint).isSome = true) :
    RelCT isa (Two fun p s => Ws s (B p) (Z p) (w p)) (seqs (eqA a b))
      (Two fun p s => Ws s (B p) (Z p) (w p)) := by
  refine eqA_gct B Z w (fun _ _ h => h) ht fun p s h => ?_
  exact WP.mono (eqA_ok h ha hb) fun u ⟨_, m, k⟩ =>
    h.congrG (js := []) (hs := []) (by rw [m]; exact Frm.refl _ _ _) (by simp) k (by decide)

/-- Comparisons preserve the workspace, while their equality masks stay secret. -/
theorem comparisons_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ p s, Φ p s → Ws s (B p) (Z p) (w p)) {a : Nat} (ha : a = aX ∨ a = aY)
    (hw : ∀ p s, Φ p s → WP isa (comparisons a) s (Ψ p)) :
    RelCT isa (Two Φ) (comparisons a) (Two Ψ) := by
  apply two_post ?_ hw
  apply two_map (Φ' := fun p s => Ws s (B p) (Z p) (w p)) id (fun p s h => hws p s h)
  unfold comparisons
  rw [List.append_assoc]
  rcases ha with rfl | rfl
  all_goals
    refine RelCT.seqs_append (by simp [eqA]) (by simp [eqA]) (RelCT.seq
      (eqWorkspace_gct B Z w (by decide) (by decide) (by taint_decide)) ?_)
    refine RelCT.seqs_append (by simp) (by simp [eqA]) (RelCT.seq (R := Two fun p s => Ws s (B p) (Z p) (w p)) ?_ ?_)
    · simp only [seqs]
      refine blk_gct B Z w (fun _ _ h => h) (by taint_decide) fun p s h => ?_
      have h256 := h.h256
      exact WP.mono (eqStore_ok h (i := sMask) (by decide) (by decide)) fun u ⟨m, k⟩ =>
        h.congrG (js := []) (Frm.rg_of_hdr (m ▸ writeW_outside _ _ _ (by simp only [sMask, sFn]; omega))
          [] [sMask] (by decide)) (by decide) k (by decide)
    · exact (eqWorkspace_gct B Z w (by decide) (by decide) (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

/-- Compose the masked capture with its separate accumulator copy. -/
theorem capture_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) (j : Option Nat)
    {hint : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9])
      (.seq (.block (base aRoot .r8 ++ base aY .rsi ++ enabled j ++ captureCore)) (wordLoop 0 selBody)) hint).isSome = true)
    (hp : ∀ a s, Φ a s → WP isa (capturePrefix j) s fun u => Ws u (B a) (Z a) (w a))
    (hw : ∀ a s, Φ a s → WP isa (capture j) s (Ψ a)) :
    RelCT isa (Two Φ) (capture j) (Two Ψ) := by
  unfold capture
  refine RelCT.seq (capturePrefix_gct B Z w hws j ht (fun a s h =>
    WP.and (hp a s h) (WP.seq_iff.mp (hw a s h))))
    (copyA_gct B Z w (fun _ _ h => h.1) (by taint_decide) (fun _ _ h => h.2))

theorem reset_gct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a))
    (hp : ∀ a s, Φ a s → WP isa (comparisons aY) s fun u => Ws u (B a) (Z a) (w a))
    (hw : ∀ a s, Φ a s → WP isa reset s (Ψ a)) :
    RelCT isa (Two Φ) reset (Two Ψ) := by
  unfold reset
  refine RelCT.seq (comparisons_gct B Z w hws (Or.inr rfl) (fun a s h =>
    WP.and (hp a s h) (WP.seq_iff.mp (hw a s h))))
    (resetMasks_gct B Z w (fun _ _ h => h.1) (fun _ _ h => h.2))

end VG.Proof.Rsa.X86_64.RecoveryFolded
