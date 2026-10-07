import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest

/-!
# RSA key routines on AArch64: relational constant time, piece by piece

The routines reload `w` and the stride from the header (`ws`) and compute
every array's base from them, so the taint analysis, to which the header's
words are secret once a secret is stored through such a base, cannot see
that their addresses are public. Each piece is checked from a state where
the registers it needs are pinned, by correctness, to values of the public
data (`pin_ct`, or `pin_seq` after a piece proven constant time otherwise):
`ws_ct` pins `x0`, `x12` and `x11` after `ws`, and checks the rest of the
piece with the taint analysis.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A block followed by code, as its two parts in sequence: it runs the same
and leaks the same trace. -/
theorem RelCT.block_seq {P Q : State → State → Prop} {l₁ l₂ : List Instr} {c : Prog isa}
    (h : RelCT isa P (.seq (.block l₁) (.seq (.block l₂) c)) Q) : RelCT isa P (.seq (.block (l₁ ++ l₂)) c) Q := by
  have split : ∀ {s t s'}, Exec isa (.seq (.block (l₁ ++ l₂)) c) s t s' →
      Exec isa (.seq (.block l₁) (.seq (.block l₂) c)) s t s' := by
    intro s t s' e
    cases e with
    | seq eb ec =>
      rw [Exec.block_iff, execBlock_append] at eb
      obtain ⟨⟨a, u⟩, ha, hb⟩ := Option.bind_eq_some_iff.mp eb
      obtain ⟨⟨b, v⟩, hc, he⟩ := Option.map_eq_some_iff.mp hb
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [List.append_assoc]
      exact .seq (.block ha) (.seq (.block hc) ec)
  exact fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (split e₁) (split e₂)

theorem WP.block_seq_iff {l₁ l₂ : List Instr} {c : Prog isa} {s : State} {Q : State → Prop} :
    WP isa (.seq (.block (l₁ ++ l₂)) c) s Q ↔ WP isa (.seq (.block l₁) (.seq (.block l₂) c)) s Q := by
  rw [WP.seq_iff, WP.block_append_iff, WP.seq_iff]
  exact ⟨fun h => WP.mono h fun t h' => WP.seq_iff.mpr h', fun h => WP.mono h fun t h' => WP.seq_iff.mp h'⟩

/-- Code leaking the same from `Φ a`, which leaves the registers `rs` with
values of `a`; then code checked by the taint analysis from `rs`. -/
theorem pin_seq {α : Type} {Φ Ψ : α → State → Prop} {c₁ c₂ : Prog isa} (rs : List Reg)
    (f : α → Reg → BitVec 64) (h₁ : RelCT isa (Two Φ) c₁ fun _ _ => True)
    (hp : ∀ a s, Φ a s → WP isa c₁ s fun t => ∀ r ∈ rs, t.gpr r = f a r)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T} (ht₂ : (taint.check (Taint.ofRegs rs) c₂ hc₂).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.seq c₁ c₂) s (Ψ a)) :
    RelCT isa (Two Φ) (.seq c₁ c₂) (Two Ψ) :=
  RelCT.seq (two_post (Ψ := fun a t => (∀ r ∈ rs, t.gpr r = f a r) ∧ WP isa c₂ t (Ψ a)) h₁
      fun a s h => WP.and (hp a s h) (WP.seq_iff.mp (hw a s h)))
    (two_post (two_taint rs (fun _ _ _ h₁ h₂ r hr => (h₁.1 r hr).trans (h₂.1 r hr).symm) ht₂)
      fun _ _ h => h.2)

/-- Code checked by the taint analysis from the registers `rs₁`, which `Φ a`
pins, and which leaves the registers `rs₂` with values of `a`; then code
checked from `rs₂`. -/
theorem pin_ct {α : Type} {Φ Ψ : α → State → Prop} {c₁ c₂ : Prog isa} (rs₁ rs₂ : List Reg)
    (f : α → Reg → BitVec 64) (hpin : Pins Φ rs₁) {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs rs₁) c₁ hc₁).isSome = true)
    (hp : ∀ a s, Φ a s → WP isa c₁ s fun t => ∀ r ∈ rs₂, t.gpr r = f a r)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T} (ht₂ : (taint.check (Taint.ofRegs rs₂) c₂ hc₂).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.seq c₁ c₂) s (Ψ a)) :
    RelCT isa (Two Φ) (.seq c₁ c₂) (Two Ψ) :=
  pin_seq rs₂ f (two_taint rs₁ hpin ht₁) hp ht₂ hw

/-- The registers `ws` pins: `x0`, `w` in `x12` and the stride in `x11`. -/
def wsVal (B : Addr) (w : Nat) : Reg → BitVec 64
  | .x0 => B
  | .x12 => BitVec.ofNat 64 w
  | .x11 => BitVec.ofNat 64 (8 * (w + 2))
  | _ => 0

/-- After code that leaves the working space's registers: they are pinned. -/
theorem wsVal_of {t : State} {B : Addr} {w : Nat} (h0 : t.gpr .x0 = B) (h12 : t.gpr .x12 = BitVec.ofNat 64 w)
    (h11 : t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) : ∀ r ∈ [Reg.x0, .x12, .x11], t.gpr r = wsVal B w r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h0
  · exact h12
  · exact h11

theorem pins_ws {α : Type} {Φ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) : Pins Φ [.x0] := fun a s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [(hws a s₁ h₁).x0, (hws a s₂ h₂).x0]

/-- `ws`'s registers. -/
theorem ws_pin {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block ws) s fun t => ∀ r ∈ [Reg.x0, .x12, .x11], t.gpr r = wsVal B w r :=
  WP.mono h.ws_ok fun _ ⟨⟨h12, h11, _⟩, k⟩ => wsVal_of ((k.gpr .x0 (by decide)).trans h.x0) h12 h11

/-- `ws` and then code checked by the taint analysis from `x0`, `x12` and
`x11`, from states with the working space of the public data `a`. -/
theorem ws_ct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat) {rest : List Instr}
    {body : Prog isa} (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block rest) body) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.seq (.block (ws ++ rest)) body) s (Ψ a)) :
    RelCT isa (Two Φ) (.seq (.block (ws ++ rest)) body) (Two Ψ) :=
  RelCT.block_seq (pin_ct [.x0] [.x0, .x12, .x11] (fun a => wsVal (B a) (w a)) (pins_ws B Z w hws)
    (by taint_decide) (fun a s h => ws_pin (hws a s h)) ht fun a s h => WP.block_seq_iff.mp (hw a s h))

/-- `ws_ct` for a block. -/
theorem ws_block_ct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat) {rest : List Instr}
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.block rest) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.block (ws ++ rest)) s (Ψ a)) :
    RelCT isa (Two Φ) (.block (ws ++ rest)) (Two Ψ) :=
  RelCT.block_append (pin_ct [.x0] [.x0, .x12, .x11] (fun a => wsVal (B a) (w a)) (pins_ws B Z w hws)
    (by taint_decide) (fun a s h => ws_pin (hws a s h)) ht
    fun a s h => WP.seq_iff.mpr (WP.block_append_iff.mp (hw a s h)))

end VG.Proof.Rsa.AArch64
