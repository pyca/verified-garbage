module

public import VerifiedGarbage.Proof.Rsa.Arm.KcBody
public import VerifiedGarbage.Proof.Rsa.Arm.KcTaint
public import VerifiedGarbage.Proof.Rsa.Arm.DivCT
public import VerifiedGarbage.Proof.Framework.RelCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The checks of an RSA key on ARMv7: constant time

Two runs of the checks, each from its own state and numbers, are related at
every step by what correctness says of each (`LiftB`), for a caller's index
`a` (the function's initial state) related by `Pub` across the runs, which
determines the working space and the modulus' length `gf a`. The pieces the
taint analysis checks (`KcTaint.lean`) agree on the registers that
correctness determines from `gf a`, and the divisions start from the same
geometry (`Div.code_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.KeyCheck
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

/-- What the checks of `d` keep from `crtBody`. -/
def CrtKept (g : Geo) (v : Vals) (P : Bool → Prop) : Prop := ∃ X₁ X₂ R₁ R₂ R₃,
  (0 < v.p → X₂ = v.n % v.p ∧ X₁ = v.n / v.p) ∧ ProdsOk g v R₁ R₂ R₃ ∧ P (cMask v X₁ X₂ R₁ R₂ R₃)

section
variable {α : Type} (Pub : α → α → Prop)

/-- Two runs at the same step: each from its index `a`, the state `σ` the
checks started from, and its numbers `v`. -/
def LiftB (F : α → State → Vals → State → Prop) (s t : State) : Prop :=
  ∃ a₁ σ₁ v₁ a₂ σ₂ v₂, Pub a₁ a₂ ∧ F a₁ σ₁ v₁ s ∧ F a₂ σ₂ v₂ t

variable {Pub}

theorem LiftB.mono {F G : α → State → Vals → State → Prop} (h : ∀ a σ v s, F a σ v s → G a σ v s) {s t : State} :
    LiftB Pub F s t → LiftB Pub G s t :=
  fun ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ => ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h _ _ _ _ h₁, h _ _ _ _ h₂⟩

/-- A piece the taint analysis checks with the registers `rs` public. -/
theorem pieceB {F G : α → State → Vals → State → Prop} {c : Prog isa} (rs : List Reg)
    (hc : ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true)
    (regs : ∀ a₁ σ₁ v₁ a₂ σ₂ v₂ s t, Pub a₁ a₂ → F a₁ σ₁ v₁ s → F a₂ σ₂ v₂ t → ∀ r ∈ rs, s.gpr r = t.gpr r)
    (hw : ∀ a σ v s, F a σ v s → WP isa c s (G a σ v)) : RelCT isa (LiftB Pub F) c (LiftB Pub G) := by
  intro s t tr₁ tr₂ s' t' ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ e₁ e₂
  obtain ⟨_, hc⟩ := hc
  have r := ((RelCT.taint (A := taint) (P := fun s t => F a₁ σ₁ v₁ s ∧ F a₂ σ₂ v₂ t) (Taint.ofRegs rs)
    (fun s t h => Taint.agree_ofRegs (regs _ _ _ _ _ _ _ _ p h.1 h.2)) hc).wp
    (F₁ := G a₁ σ₁ v₁) (F₂ := G a₂ σ₂ v₂) fun s t h => ⟨hw _ _ _ _ h.1, hw _ _ _ _ h.2⟩)
    s t tr₁ tr₂ s' t' ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, a₁, σ₁, v₁, a₂, σ₂, v₂, p, r.2.2.1, r.2.2.2⟩

/-- A division, from the same geometry in both runs. -/
theorem divPieceB {gf : α → Geo} (hg : ∀ a₁ a₂, Pub a₁ a₂ → gf a₁ = gf a₂) {G : α → State → Vals → State → Prop} :
    RelCT isa (LiftB Pub fun a σ v u => VG.Proof.Rsa.Arm.Div.Context (gDiv (gf a)) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u (G a σ v)) VG.Impl.Rsa.Arm.Div.code (LiftB Pub G) := by
  intro s t tr₁ tr₂ s' t' ⟨a₁, σ₁, v₁, a₂, σ₂, v₂, p, h₁, h₂⟩ e₁ e₂
  have r := (((VG.Proof.Rsa.Arm.Div.code_ct (g := gDiv (gf a₁))).mono
    (P' := fun s t => (VG.Proof.Rsa.Arm.Div.Context (gDiv (gf a₁)) s ∧
        WP isa VG.Impl.Rsa.Arm.Div.code s (G a₁ σ₁ v₁)) ∧
      (VG.Proof.Rsa.Arm.Div.Context (gDiv (gf a₁)) t ∧ WP isa VG.Impl.Rsa.Arm.Div.code t (G a₂ σ₂ v₂)))
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h).wp
    (F₁ := G a₁ σ₁ v₁) (F₂ := G a₂ σ₂ v₂) fun _ _ h => ⟨h.1.2, h.2.2⟩) s t tr₁ tr₂ s' t'
    ⟨⟨h₁.1, h₁.2⟩, ⟨by rw [hg _ _ p]; exact h₂.1, h₂.2⟩⟩ e₁ e₂
  exact ⟨r.1, a₁, σ₁, v₁, a₂, σ₂, v₂, p, r.2.2.1, r.2.2.2⟩

/-- `r7`–`r9` in two states of `Ws` on the same working space. -/
theorem ws_regs {s t : State} {g : Geo} (h₁ : Ws s g.B g.Z g.w nArr) (h₂ : Ws t g.B g.Z g.w nArr) :
    ∀ r ∈ [Reg.r7, .r8, .r9], s.gpr r = t.gpr r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · rw [h₁.r7, h₂.r7]
  · rw [h₁.r8, h₂.r8]
  · rw [h₁.r9, h₂.r9]

variable {gf : α → Geo} (hg : ∀ a₁ a₂, Pub a₁ a₂ → gf a₁ = gf a₂) (X : α → State → Prop)
include hg

theorem crtBody_ct : RelCT isa (LiftB Pub fun a σ v s => s = σ ∧ X a σ ∧ BodyIn (gf a) v s) crtBody
    (LiftB Pub fun a σ v t => X a σ ∧ CrtOut (gf a) σ v t) := by
  unfold crtBody
  simp only [seqs]
  refine RelCT.seq (pieceB (G := fun a σ v u => X a σ ∧ VG.Proof.Rsa.Arm.Div.Context (gDiv (gf a)) u ∧
      WP isa VG.Impl.Rsa.Arm.Div.code u (DivN (gf a) σ v)) [.r8, .r11] start_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p h₁ h₂ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · rw [h₁.2.2.r8, h₂.2.2.r8, hg _ _ p]
      · rw [h₁.2.2.r11, h₂.2.2.r11, hg _ _ p])
    fun a σ v s ⟨e, x, h⟩ => by subst e; exact WP.mono (start_ok' h) fun u hu => ⟨x, hu⟩) ?_
  refine RelCT.seq ((divPieceB (G := fun a σ v t => X a σ ∧ DivN (gf a) σ v t) hg).mono
    (fun _ _ => LiftB.mono fun _ _ _ _ ⟨x, c, w⟩ => ⟨c, WP.mono w fun _ h => ⟨x, h⟩⟩) fun _ _ h => h) ?_
  refine RelCT.seq (pieceB (G := fun a σ v t => X a σ ∧ DivN' (gf a) σ v t) [.r8] ctxDiv_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, X₁, X₂, _, h₁⟩ ⟨_, Y₁, Y₂, _, h₂⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      rw [h₁.ws.r8, h₂.ws.r8, hg _ _ p])
    fun a σ v s ⟨x, h⟩ => WP.mono (divN_ctx_ok h) fun _ h' => ⟨x, h'⟩) ?_
  exact pieceB (G := fun a σ v t => X a σ ∧ CrtOut (gf a) σ v t) [.r7, .r8, .r9] crtChecks_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, X₁, X₂, _, h₁⟩ ⟨_, Y₁, Y₂, _, h₂⟩ =>
      ws_regs h₁.ws (by rw [hg _ _ p]; exact h₂.ws))
    fun a σ v s ⟨x, h⟩ => WP.mono (crtChecks_ok' h) fun _ h' => ⟨x, h'⟩

theorem keyBody_ct : RelCT isa (LiftB Pub fun a σ v s => s = σ ∧ X a σ ∧ BodyIn (gf a) v s) keyBody
    (LiftB Pub fun a σ v t => X a σ ∧ KeyOut (gf a) σ v t) := by
  unfold keyBody
  simp only [seqs]
  refine RelCT.seq (crtBody_ct hg X) ?_
  refine RelCT.seq (pieceB (G := fun a σ v u => X a σ ∧ CrtKept (gf a) v fun c =>
      VG.Proof.Rsa.Arm.Div.Context (gDiv (gf a)) u ∧ WP isa VG.Impl.Rsa.Arm.Div.code u (DivP (gf a) σ v c))
    [.r7, .r8, .r9] dChecks1_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, h₂⟩ =>
      ws_regs h₁.ws (by rw [hg _ _ p]; exact h₂.ws))
    fun a σ v s ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩ =>
      WP.mono (dChecks1_ok h) fun _ h' => ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h'⟩) ?_
  refine RelCT.seq ((divPieceB (G := fun a σ v t => X a σ ∧ CrtKept (gf a) v fun c => DivP (gf a) σ v c t)
    hg).mono (fun _ _ => LiftB.mono fun _ _ _ _ ⟨x, k⟩ => by
      obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, c, w⟩ := k
      exact ⟨c, WP.mono w fun _ h => ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩⟩) fun _ _ h => h) ?_
  refine RelCT.seq (pieceB (G := fun a σ v t => X a σ ∧ CrtKept (gf a) v fun c => DivP' (gf a) σ v c t) [.r8]
    ctxDiv_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, _, _, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, _, _, _, h₂⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      rw [h₁.ws.r8, h₂.ws.r8, hg _ _ p])
    fun a σ v s ⟨x, k⟩ => by
      obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩ := k
      exact WP.mono (divP_ctx_ok h) fun _ h' => ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h'⟩) ?_
  refine RelCT.seq (pieceB (G := fun a σ v u => X a σ ∧ CrtKept (gf a) v fun c =>
      VG.Proof.Rsa.Arm.Div.Context (gDiv (gf a)) u ∧ WP isa VG.Impl.Rsa.Arm.Div.code u (DivQ (gf a) σ v c))
    [.r7, .r8, .r9] dChecks2_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, _, _, _, _, _, _, _, _, _, h₁⟩ ⟨_, _, _, _, _, _, _, _, _, _, _, h₂⟩ =>
      ws_regs h₁.ws (by rw [hg _ _ p]; exact h₂.ws))
    fun a σ v s ⟨x, k⟩ => by
      obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩ := k
      exact WP.mono (dChecks2_ok h) fun _ h' => ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h'⟩) ?_
  refine RelCT.seq ((divPieceB (G := fun a σ v t => X a σ ∧ CrtKept (gf a) v fun c => DivQ (gf a) σ v c t)
    hg).mono (fun _ _ => LiftB.mono fun _ _ _ _ ⟨x, k⟩ => by
      obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, c, w⟩ := k
      exact ⟨c, WP.mono w fun _ h => ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩⟩) fun _ _ h => h) ?_
  refine RelCT.seq (pieceB (G := fun a σ v t => X a σ ∧ CrtKept (gf a) v fun c => DivQ' (gf a) σ v c t) [.r8]
    ctxDiv_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h₁⟩
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h₂⟩ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r rfl
      rw [h₁.ws.r8, h₂.ws.r8, hg _ _ p])
    fun a σ v s ⟨x, k⟩ => by
      obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩ := k
      exact WP.mono (divQ_ctx_ok h) fun _ h' => ⟨x, X₁, X₂, R₁, R₂, R₃, hX, hR, h'⟩) ?_
  exact pieceB (G := fun a σ v t => X a σ ∧ KeyOut (gf a) σ v t) [.r7, .r8, .r9] dChecks3_taint
    (fun a₁ σ₁ v₁ a₂ σ₂ v₂ s t p ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h₁⟩
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h₂⟩ => ws_regs h₁.ws (by rw [hg _ _ p]; exact h₂.ws))
    fun a σ v s ⟨x, k⟩ => by
      obtain ⟨X₁, X₂, R₁, R₂, R₃, hX, hR, h⟩ := k
      exact WP.mono (dChecks3_ok h) fun _ ⟨Y₁, Y₂, hY₁, hY₂, A, live, ht⟩ =>
        ⟨x, X₁, X₂, R₁, R₂, R₃, Y₁, Y₂, hX, hR, hY₁, hY₂, A, live, ht⟩

end

end VG.Proof.Rsa.Arm.KeyCheck
