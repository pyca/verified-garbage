import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCorrect
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncVerified
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm

/-!
# RSAES-OAEP decryption on AArch64: two runs

As for RSAES-PKCS1-v1_5 (`Proof/RsaPkcs1Enc/AArch64/DecCTBase.lean`): two
runs whose public data agree (the pointers and lengths, `n` and `e`) have
the same layout, so between the frames' pushes and pops they are related by
`Two`: both satisfy what correctness says of that point (`Φ`), with the same
layout, whatever their secrets.

Inside the decoding, two runs in a layout are related by `PW`: each is `In`
the frames (`Ctx`, the pieces' `Rep` with our arguments in their slots) and
satisfies `X`, which fixes the registers the next piece's addresses and
arguments depend on as functions of the layout. A block is checked by the
taint analysis from those registers (`pw_blk`); one that dereferences a
pointer it loads is split there (`pw_split`), the registers its second
part dereferences fixed by its first part.
-/

namespace VG.Proof.RsaOaep.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaOaep.AArch64

/-- `n` and `e` agree in the two runs' memories. -/
def LeakEq (L : DLay) (m₁ m₂ : Mem) : Prop :=
  Spec.Rsa.bytesAt m₁ L.n L.k.toNat = Spec.Rsa.bytesAt m₂ L.n L.k.toNat ∧
    Spec.Rsa.bytesAt m₁ L.e L.el.toNat = Spec.Rsa.bytesAt m₂ L.e L.el.toNat

/-- The layout of two runs, and what each has on entry. -/
structure Env where
  L : DLay
  g₁ : Reg → BitVec 64
  g₂ : Reg → BitVec 64
  v₁ : VReg → BitVec 128
  v₂ : VReg → BitVec 128
  m₁ : Mem
  m₂ : Mem

/-- What correctness says of a point of the code. -/
abbrev Inv := DLay → (Reg → BitVec 64) → (VReg → BitVec 128) → Mem → State → Prop

/-- Two runs in the layout of `e`, each satisfying `Φ`. -/
def TwoE (S : Nat) (Φ : Inv) (e : Env) (a b : State) : Prop :=
  e.L.Ok ∧ e.L.P = S + 1 ∧ LeakEq e.L e.m₁ e.m₂ ∧ Φ e.L e.g₁ e.v₁ e.m₁ a ∧ Φ e.L e.g₂ e.v₂ e.m₂ b

/-- Two runs with the same layout, each satisfying `Φ`. -/
def Two (S : Nat) (Φ : Inv) (a b : State) : Prop := ∃ e : Env, TwoE S Φ e a b

/-- A piece of code, from two runs each satisfying `Φ`: constant time for a
fixed layout, and establishing `Ψ` by correctness. -/
theorem two_wp {S : Nat} {c : Prog isa} {Φ Ψ : Inv} (hct : ∀ e, RelCT isa (TwoE S Φ e) c fun _ _ => True)
    (hw : ∀ (L : DLay) g vv m₀ (t : State), L.Ok → L.P = S + 1 → Φ L g vv m₀ t → WP isa c t (Ψ L g vv m₀)) :
    RelCT isa (Two S Φ) c (Two S Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨e, hp⟩ e₁ e₂
  obtain ⟨ht, -⟩ := hct e _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨hL, hP, hk, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ _ _ s₁ hL hP f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ _ _ s₂ hL hP f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, e, hL, hP, hk, y₁, y₂⟩

/-- Code checked by the taint analysis from the registers `rs`, which `Φ`
fixes as functions of the layout, with `sp`. -/
theorem two {S : Nat} {c : Prog isa} {Φ Ψ : Inv} (rs : List Reg) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ (L : DLay) g₁ g₂ v₁ v₂ m₁ m₂ (a b : State), L.Ok → Φ L g₁ v₁ m₁ a → Φ L g₂ v₂ m₂ b →
      a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r)
    (hw : ∀ (L : DLay) g vv m₀ (t : State), L.Ok → L.P = S + 1 → Φ L g vv m₀ t → WP isa c t (Ψ L g vv m₀)) :
    RelCT isa (Two S Φ) c (Two S Ψ) :=
  two_wp (fun _ => RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ ⟨hL, _, _, f₁, f₂⟩ => by
    obtain ⟨hsp, hr⟩ := hag _ _ _ _ _ _ _ _ _ hL f₁ f₂
    exact ⟨hsp, fun r hr' => hr r (Taint.mem_ofRegs.mp hr')⟩) h) hw

/-! ## Inside the frames -/

/-- `Ctx`, the pieces' `Rep` with our arguments in their slots, and `X` of
the frame's words and the state. -/
def In (L : DLay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem)
    (X : (Nat → BitVec 64) → State → Prop) (t : State) : Prop :=
  Ctx L g vv m₀ t ∧ ∃ V W, Rep t.mem L.Q L.scr V W ∧ Slots L W ∧ X W t

/-- Two runs in the layout of `e`, each `In` the frames with `X`. -/
def PW (S : Nat) (e : Env) (X : (Nat → BitVec 64) → State → Prop) (a b : State) : Prop :=
  e.L.Ok ∧ e.L.P = S + 1 ∧ In e.L e.g₁ e.v₁ e.m₁ X a ∧ In e.L e.g₂ e.v₂ e.m₂ X b

/-- What a piece establishes, by correctness. -/
abbrev PWStep (S : Nat) (e : Env) (c : Prog isa) (X X' : (Nat → BitVec 64) → State → Prop) : Prop :=
  ∀ g vv m₀ (t : State) V W, e.L.Ok → e.L.P = S + 1 → Ctx e.L g vv m₀ t → Rep t.mem e.L.Q e.L.scr V W →
    Slots e.L W → X W t → WP isa c t (In e.L g vv m₀ X')

theorem pw_wp {S : Nat} {e : Env} {c : Prog isa} {X X' : (Nat → BitVec 64) → State → Prop}
    (hct : RelCT isa (PW S e X) c fun _ _ => True) (hw : PWStep S e c X X') :
    RelCT isa (PW S e X) c (PW S e X') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨hL, hP, ⟨c₁, V₁, W₁, R₁, S₁, x₁⟩, ⟨c₂, V₂, W₂, R₂, S₂, x₂⟩⟩ := hp
  obtain ⟨_, u₁, y₁, z₁⟩ := hw _ _ _ s₁ _ _ hL hP c₁ R₁ S₁ x₁
  obtain ⟨_, u₂, y₂, z₂⟩ := hw _ _ _ s₂ _ _ hL hP c₂ R₂ S₂ x₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ y₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ y₂
  exact ⟨ht, hL, hP, z₁, z₂⟩

theorem pw_sp {S : Nat} {e : Env} {X : (Nat → BitVec 64) → State → Prop} {a b : State} (h : PW S e X a b) :
    a.sp = b.sp :=
  h.2.2.1.1.sp.trans h.2.2.2.1.sp.symm

/-- Code checked by the taint analysis from the registers `rs`, which `X` fixes. -/
theorem pw_taint {S : Nat} {e : Env} {c : Prog isa} {X : (Nat → BitVec 64) → State → Prop} (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ W₁ W₂ a b, X W₁ a → X W₂ b → ∀ r ∈ rs, a.gpr r = b.gpr r) :
    RelCT isa (PW S e X) c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ hp => by
    have hs := pw_sp hp
    obtain ⟨_, _, ⟨_, _, _, _, _, x₁⟩, ⟨_, _, _, _, _, x₂⟩⟩ := hp
    exact ⟨hs, fun r hr => hag _ _ _ _ x₁ x₂ r (Taint.mem_ofRegs.mp hr)⟩) h

/-- A block checked by the taint analysis from the registers `rs`, which `X` fixes. -/
theorem pw_blk {S : Nat} {e : Env} {c : Prog isa} {X X' : (Nat → BitVec 64) → State → Prop} (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ W₁ W₂ a b, X W₁ a → X W₂ b → ∀ r ∈ rs, a.gpr r = b.gpr r) (hw : PWStep S e c X X') :
    RelCT isa (PW S e X) c (PW S e X') :=
  pw_wp (pw_taint rs h hag) hw

/-- Code whose second part `c₂` dereferences the registers `rs`, which its
first part `c₁` sets to `pin` in both runs. -/
theorem pw_seq_tr {S : Nat} {e : Env} {c₁ c₂ : Prog isa} {X : (Nat → BitVec 64) → State → Prop}
    (rs : List Reg) (pin : Reg → BitVec 64) {h₁ h₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs []) c₁ h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs rs) c₂ h₂).isSome = true)
    (hA : ∀ g vv m₀ (t : State) V W, e.L.Ok → e.L.P = S + 1 → Ctx e.L g vv m₀ t → Rep t.mem e.L.Q e.L.scr V W →
      Slots e.L W → X W t → WP isa c₁ t fun u => u.sp = t.sp ∧ ∀ r ∈ rs, u.gpr r = pin r) :
    RelCT isa (PW S e X) (.seq c₁ c₂) fun _ _ => True := by
  have h1 : RelCT isa (PW S e X) c₁ fun a b => a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r := by
    have hw := (RelCT.taint (A := taint) (P := PW S e X) (Taint.ofRegs []) (fun _ _ hp =>
      ⟨pw_sp hp, fun r hr => absurd (Taint.mem_ofRegs.mp hr) List.not_mem_nil⟩) t₁).wpDep
      (F := fun (s u : State) => u.sp = s.sp ∧ ∀ r ∈ rs, u.gpr r = pin r) fun s₁ s₂ hp => by
        obtain ⟨hL, hP, ⟨c₁, V₁, W₁, R₁, S₁, x₁⟩, ⟨c₂, V₂, W₂, R₂, S₂, x₂⟩⟩ := hp
        exact ⟨hA _ _ _ _ _ _ hL hP c₁ R₁ S₁ x₁, hA _ _ _ _ _ _ hL hP c₂ R₂ S₂ x₂⟩
    refine hw.mono (fun _ _ h => h) fun a b ⟨_, σ₁, σ₂, hσ, ⟨sa, ra⟩, ⟨sb, rb⟩⟩ =>
      ⟨by rw [sa, sb]; exact pw_sp hσ, fun r hr => (ra r hr).trans (rb r hr).symm⟩
  have h2 : RelCT isa (fun a b => a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r) c₂ fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ ⟨hs, hr⟩ =>
      ⟨hs, fun r h => hr r (Taint.mem_ofRegs.mp h)⟩) t₂
  exact h1.seq h2

/-- `pw_seq_tr`, with what the whole establishes by correctness. -/
theorem pw_seq {S : Nat} {e : Env} {c₁ c₂ : Prog isa} {X X' : (Nat → BitVec 64) → State → Prop}
    (rs : List Reg) (pin : Reg → BitVec 64) {h₁ h₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (t₁ : (taint.check (Taint.ofRegs []) c₁ h₁).isSome = true)
    (t₂ : (taint.check (Taint.ofRegs rs) c₂ h₂).isSome = true)
    (hA : ∀ g vv m₀ (t : State) V W, e.L.Ok → e.L.P = S + 1 → Ctx e.L g vv m₀ t → Rep t.mem e.L.Q e.L.scr V W →
      Slots e.L W → X W t → WP isa c₁ t fun u => u.sp = t.sp ∧ ∀ r ∈ rs, u.gpr r = pin r)
    (hw : PWStep S e (.seq c₁ c₂) X X') :
    RelCT isa (PW S e X) (.seq c₁ c₂) (PW S e X') :=
  pw_wp (pw_seq_tr rs pin t₁ t₂ hA) hw

/-- A block whose second part dereferences the registers `rs`, which its
first part sets to `pin` in both runs. -/
theorem pw_split {S : Nat} {e : Env} {A B : List Instr} {X X' : (Nat → BitVec 64) → State → Prop}
    (rs : List Reg) (pin : Reg → BitVec 64) {h₁ h₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (tA : (taint.check (Taint.ofRegs []) (.block A) h₁).isSome = true)
    (tB : (taint.check (Taint.ofRegs rs) (.block B) h₂).isSome = true)
    (hA : ∀ g vv m₀ (t : State) V W, e.L.Ok → e.L.P = S + 1 → Ctx e.L g vv m₀ t → Rep t.mem e.L.Q e.L.scr V W →
      Slots e.L W → X W t → WP isa (.block A) t fun u => u.sp = t.sp ∧ ∀ r ∈ rs, u.gpr r = pin r)
    (hw : PWStep S e (.block (A ++ B)) X X') :
    RelCT isa (PW S e X) (.block (A ++ B)) (PW S e X') :=
  pw_wp (RelCT.block_append (pw_seq_tr rs pin tA tB hA)) hw

/-- Facts `X` fixes in both runs. -/
theorem pin {a b : State} {r : Reg} {x : BitVec 64} (ha : a.gpr r = x) (hb : b.gpr r = x) :
    a.gpr r = b.gpr r := ha.trans hb.symm

/-- `In`, from a piece's `Lay`, `Step` and `Rep`. -/
theorem In.of_step {L : DLay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t u : State}
    (hL : L.Ok) (hP : 16 ≤ L.P) (hc : Ctx L g vv m₀ t) {ws : List Region} (S : Step L.Q L.scr ws t u)
    (hws : ∀ r ∈ ws, r = L.OUT ∨ r = L.ML) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem L.Q L.scr V W)
    (hS : Slots L W) {X : (Nat → BitVec 64) → State → Prop} (hx : X W u) : In L g vv m₀ X u :=
  ⟨hc.step hL hP S hws, V, W, R, hS, hx⟩

theorem nil_ws {L : DLay} : ∀ r ∈ ([] : List Region), r = L.OUT ∨ r = L.ML :=
  fun _ h => absurd h List.not_mem_nil

end VG.Proof.RsaOaep.AArch64.Dec
