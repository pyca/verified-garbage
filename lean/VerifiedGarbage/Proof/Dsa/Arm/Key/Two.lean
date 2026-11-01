module

public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Copy
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Impl.Dsa.Arm.Context

/-!
# Relating two runs of the randomized signer by their public data (32-bit ARM)

As on x86 (`Proof/Dsa/X86/RandomTwo.lean`): `Two Φ` relates two runs in
which both states satisfy `Φ a` for the same public data `a`. Straight code
is checked by the taint analysis from the registers `Φ` pins (`two_taint`),
what correctness gives after it is carried along (`two_post`), and branches
and loops on conditions `Φ` fixes are related case by case (`two_ite`,
`two_loop`).

`pubOf s₀`: the entry's stack pointer, its register and stack arguments and
q's bytes, which two runs with related entry states share. Everything the
code uses as an address or count is a function of it (`pub_*`); in
particular the frame's base, which `r11` holds (`pins_r11`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random

/-! ## Two runs -/

/-- Both runs satisfy `Φ a`, for the same `a`. -/
def Two {α : Type} (Φ : α → State → Prop) (s₁ s₂ : State) : Prop := ∃ a, Φ a s₁ ∧ Φ a s₂

theorem two_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw a s₁ h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, a, y₁, y₂⟩

/-- `Φ a` fixes the registers `rs`. -/
def Pins {α : Type} (Φ : α → State → Prop) (rs : List Reg) : Prop :=
  ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem two_taint {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨a, h₁, h₂⟩ => Taint.agree_ofRegs (hpin a _ _ h₁ h₂)) h

/-- A piece checked by the taint analysis, with what correctness gives after it. -/
theorem two_piece {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) : RelCT isa (Two Φ) c (Two Ψ) :=
  two_post (two_taint rs hpin h) hw

theorem two_map {α β : Type} {Φ : α → State → Prop} {Φ' : β → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (g : α → β) (h : ∀ a s, Φ a s → Φ' (g a) s) (hct : RelCT isa (Two Φ') c Q) :
    RelCT isa (Two Φ) c Q :=
  hct.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨g a, h _ _ h₁, h _ _ h₂⟩) fun _ _ h => h

/-- A branch whose condition `Φ a` fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {cond : isa.Cond} {th el : Prog isa}
    {Q : State → State → Prop}
    (hc : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval cond s₁ = isa.eval cond s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some true) th Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval cond s = some false) el Q) :
    RelCT isa (Two Φ) (.ite cond th el) Q := by
  refine RelCT.ite (fun _ _ ⟨a, h₁, h₂⟩ => hc a _ _ h₁ h₂) (ht.mono ?_ fun _ _ h => h)
    (he.mono ?_ fun _ _ h => h)
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩
  · rintro s₁ s₂ ⟨⟨a, h₁, h₂⟩, hb⟩
    exact ⟨a, ⟨h₁, hb⟩, h₂, by rw [← hc a _ _ h₁ h₂, hb]⟩

/-- A loop of `N a` iterations, its `j`-th from a state satisfying `Φ a j`,
whose condition after iteration `j` is whether `j + 1 < N a`. -/
theorem two_loop {α : Type} {Φ : α → Nat → State → Prop} {Ψ : α → State → Prop} (N : α → Nat)
    {body : Prog isa} {cond : isa.Cond}
    (hct : RelCT isa (Two fun (p : α × Nat) s => p.2 < N p.1 ∧ Φ p.1 p.2 s) body fun _ _ => True)
    (hw : ∀ a j s, j < N a → Φ a j s → WP isa body s fun s' =>
      isa.eval cond s' = some (decide (j + 1 < N a)) ∧ (j + 1 < N a → Φ a (j + 1) s') ∧
      (j + 1 = N a → Ψ a s')) :
    RelCT isa (Two fun a s => 0 < N a ∧ Φ a 0 s) (.loop body cond) (Two Ψ) := by
  have key := RelCT.loop (M := isa) (body := body) (c := cond) (Q := Two Ψ)
    (fun n s₁ s₂ => ∃ a j, n = N a - j ∧ j < N a ∧ Φ a j s₁ ∧ Φ a j s₂) (fun n => by
      have hp := two_post (Φ := fun (p : α × Nat) s => p.2 < N p.1 ∧ n = N p.1 - p.2 ∧ Φ p.1 p.2 s)
        (Ψ := fun p s' => p.2 < N p.1 ∧ n = N p.1 - p.2 ∧ isa.eval cond s' = some (decide (p.2 + 1 < N p.1)) ∧
          (p.2 + 1 < N p.1 → Φ p.1 (p.2 + 1) s') ∧ (p.2 + 1 = N p.1 → Ψ p.1 s'))
        (two_map id (fun p s h => ⟨h.1, h.2.2⟩) hct)
        fun p s h => WP.mono (hw p.1 p.2 s h.1 h.2.2) fun s' h' => ⟨h.1, h.2.1, h'⟩
      refine hp.mono (fun s₁ s₂ ⟨a, j, hn, hj, h₁, h₂⟩ => ⟨(a, j), ⟨hj, hn, h₁⟩, hj, hn, h₂⟩) ?_
      rintro s₁ s₂ ⟨⟨a, j⟩, ⟨hj, hn, e₁, f₁, g₁⟩, ⟨-, -, e₂, f₂, g₂⟩⟩
      refine ⟨by rw [e₁, e₂], fun h => ?_, fun h => ?_⟩
      · have : ¬ j + 1 < N a := by rw [e₁] at h; simpa using h
        have hjN : j + 1 = N a := by simp only at hj this; omega
        exact ⟨a, g₁ hjN, g₂ hjN⟩
      · have hlt : j + 1 < N a := by rw [e₁] at h; simpa using h
        exact ⟨N a - (j + 1), by simp only at hn; omega, a, j + 1, rfl, hlt, f₁ hlt, f₂ hlt⟩)
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨a, ⟨h0, h₁⟩, ⟨-, h₂⟩⟩ := hp
  exact key (N a - 0) _ _ _ _ _ _ ⟨a, 0, rfl, h0, h₁, h₂⟩ e₁ e₂

theorem nil_relCT {P : State → State → Prop} : RelCT isa P (.block []) fun _ _ => True :=
  RelCT.block_nil fun _ _ _ => trivial

/-! ## What two runs share -/

/-- The public data of an entry state. -/
structure Pub where
  sp : BitVec 32
  regs : List (BitVec 32)
  args : List (BitVec 32)
  qBytes : List Byte

def pubOf (s₀ : State) : Pub :=
  ⟨s₀.sp, [s₀.gpr .r0, s₀.gpr .r1, s₀.gpr .r2, s₀.gpr .r3], (List.range 7).map (stackArg s₀), rQBytes s₀⟩

/-- Some entry state with public data `a` relates to `t` by `P`. -/
def At (P : State → State → Prop) (a : Pub) (t : State) : Prop :=
  ∃ s₀, KeyABI s₀ ∧ pubOf s₀ = a ∧ P s₀ t

section
variable {s₁ s₂ : State} (h : pubOf s₁ = pubOf s₂)
include h

theorem pub_sp : s₁.sp = s₂.sp := congrArg Pub.sp h
theorem pub_reg (i : Nat) : [s₁.gpr .r0, s₁.gpr .r1, s₁.gpr .r2, s₁.gpr .r3][i]? =
    [s₂.gpr .r0, s₂.gpr .r1, s₂.gpr .r2, s₂.gpr .r3][i]? := congrArg (fun a => a.regs[i]?) h
theorem pub_r0 : s₁.gpr .r0 = s₂.gpr .r0 := Option.some.inj (pub_reg h 0)
theorem pub_r1 : s₁.gpr .r1 = s₂.gpr .r1 := Option.some.inj (pub_reg h 1)
theorem pub_r2 : s₁.gpr .r2 = s₂.gpr .r2 := Option.some.inj (pub_reg h 2)
theorem pub_r3 : s₁.gpr .r3 = s₂.gpr .r3 := Option.some.inj (pub_reg h 3)
theorem pub_arg (j : Nat) (hj : j < 7) : stackArg s₁ j = stackArg s₂ j := by
  have := congrArg (fun a => a.args[j]?) h
  simpa only [pubOf, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] using this
theorem pub_qBytes : rQBytes s₁ = rQBytes s₂ := congrArg Pub.qBytes h
theorem pub_rLow : rLow s₁ = rLow s₂ := by rw [rLow, rLow, pub_sp h]
theorem pub_rBase : rBase s₁ = rBase s₂ := by rw [rBase, rBase, pub_rLow h]
theorem pub_rQ : rQ s₁ = rQ s₂ := by rw [rQ, rQ, pub_r3 h, pub_arg h 1 (by decide)]
theorem pub_rWidth : rWidth s₁ = rWidth s₂ := by rw [rWidth, rWidth, pub_qBytes h]
theorem pub_rLead : rLead s₁ = rLead s₂ := by rw [rLead, rLead, pub_qBytes h]
theorem pub_rq : rq s₁ = rq s₂ := by rw [rq, rq, pub_qBytes h]
theorem pub_randLen : (rInput s₁).rand.length = (rInput s₂).rand.length := by
  simp only [rInput, rBytes_length, pub_arg h 4 (by decide)]
theorem pub_drawPlace : drawPlace s₁ = drawPlace s₂ := by
  simp only [drawPlace, pub_qBytes h, pub_rWidth h]
end

theorem addr_inj32 {a b : BitVec 32} (h : State.addr a = State.addr b) : a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [← VG.Proof.X25519.Arm.addr_toNat a, ← VG.Proof.X25519.Arm.addr_toNat b, h]

/-- Two states whose frames have the same base agree on `r11`. -/
theorem r11_of_rf {t₁ t₂ : State} {B : Addr} (h₁ : RF t₁ B) (h₂ : RF t₂ B) : t₁.gpr .r11 = t₂.gpr .r11 :=
  addr_inj32 (h₁.base.trans h₂.base.symm)

theorem At.r11 {P : State → State → Prop} (hr : ∀ s₀ t, P s₀ t → RReady s₀ t) {a : Pub} {t₁ t₂ : State}
    (h₁ : At P a t₁) (h₂ : At P a t₂) : t₁.gpr .r11 = t₂.gpr .r11 := by
  obtain ⟨s₁, -, e₁, p₁⟩ := h₁
  obtain ⟨s₂, -, e₂, p₂⟩ := h₂
  exact r11_of_rf (hr _ _ p₁).rf ((pub_rBase (e₁.trans e₂.symm)) ▸ (hr _ _ p₂).rf)

/-- `r11` is pinned. -/
theorem pins_r11 {α : Type} {Φ : α → State → Prop} (f : α → Pub) {P : α → State → State → Prop}
    (hΦ : ∀ a t, Φ a t → At (P a) (f a) t) (hr : ∀ a s₀ t, P a s₀ t → RReady s₀ t) : Pins Φ [.r11] := by
  intro a t₁ t₂ h₁ h₂ r hr'
  rw [List.mem_singleton] at hr'; subst hr'
  exact At.r11 (hr a) (hΦ a t₁ h₁) (hΦ a t₂ h₂)

/-- `r11` is pinned by a predicate about the frame. -/
theorem pins_at {α : Type} {P : α → State → State → Prop} (f : α → Pub)
    (hr : ∀ a s₀ t, P a s₀ t → RReady s₀ t) : Pins (fun a => At (P a) (f a)) [.r11] :=
  pins_r11 f (fun _ _ h => h) hr

/-- `r11` is pinned in a branch. -/
theorem pins_at' {α : Type} {P : α → State → State → Prop} {X : α → State → Prop} (f : α → Pub)
    (hr : ∀ a s₀ t, P a s₀ t → RReady s₀ t) : Pins (fun a s => At (P a) (f a) s ∧ X a s) [.r11] :=
  pins_r11 (P := P) f (fun _ _ h => h.1) hr

end VG.Proof.Dsa.Arm.Key
