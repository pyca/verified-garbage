import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# RSA key routines on x86-64: relational constant time, piece by piece

The routines reload `w` and the stride from the header (`ws`) and compute
every array's base from them, so the taint analysis, to which the header's
words are secret once a secret is stored through such a base, cannot see
that their addresses are public. Each piece is checked from a state where
the registers it needs are pinned, by correctness, to values of the public
data (`pin_ct`): `ws_ct` pins `rdi`, `r12` and `r9` after `ws`, and checks
the rest of the piece with the taint analysis.
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

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

/-- Code checked by the taint analysis from the registers `rs₁`, which `Φ a`
pins, and which leaves the registers `rs₂` with values of `a`; then code
checked from `rs₂`. -/
theorem pin_ct {α : Type} {Φ Ψ : α → State → Prop} {c₁ c₂ : Prog isa} (rs₁ rs₂ : List Reg)
    (f : α → Reg → BitVec 64) (hpin : Pins Φ rs₁) {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs rs₁) c₁ hc₁).isSome = true)
    (hp : ∀ a s, Φ a s → WP isa c₁ s fun t => ∀ r ∈ rs₂, t.gpr r = f a r)
    {hc₂ : VG.Taint.Hint VG.X86_64.Taint.T} (ht₂ : (taint.check (Taint.ofRegs rs₂) c₂ hc₂).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.seq c₁ c₂) s (Ψ a)) :
    RelCT isa (Two Φ) (.seq c₁ c₂) (Two Ψ) :=
  RelCT.seq (two_piece (Ψ := fun a t => (∀ r ∈ rs₂, t.gpr r = f a r) ∧ WP isa c₂ t (Ψ a)) rs₁ hpin ht₁
      fun a s h => WP.and (hp a s h) (WP.seq_iff.mp (hw a s h)))
    (two_post (two_taint rs₂ (fun _ _ _ h₁ h₂ r hr => (h₁.1 r hr).trans (h₂.1 r hr).symm) ht₂)
      fun _ _ h => h.2)

/-- The registers `ws` pins: `rdi`, `w` in `r12` and the stride in `r9`. -/
def wsVal (B : Addr) (w : Nat) : Reg → BitVec 64
  | .rdi => B
  | .r12 => BitVec.ofNat 64 w
  | .r9 => BitVec.ofNat 64 (8 * (w + 2))
  | _ => 0

/-- `ws` and then code checked by the taint analysis from `rdi`, `r12` and
`r9`, from states with the working space of the public data `a`. -/
theorem ws_ct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat) {rest : List Instr}
    {body : Prog isa} (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block rest) body) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.seq (.block (ws ++ rest)) body) s (Ψ a)) :
    RelCT isa (Two Φ) (.seq (.block (ws ++ rest)) body) (Two Ψ) :=
  RelCT.block_seq (pin_ct [.rdi] [.rdi, .r12, .r9] (fun a => wsVal (B a) (w a))
    (fun a s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hws a s₁ h₁).rdi, (hws a s₂ h₂).rdi])
    (by taint_decide)
    (fun a s h => WP.mono (hws a s h).ws_ok fun t ⟨h12, h9, _, k⟩ => fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (k.gpr (by decide)).trans (hws a s h).rdi
      · exact h12
      · exact h9)
    ht fun a s h => WP.block_seq_iff.mp (hw a s h))

/-- `ws_ct` for a block. -/
theorem ws_block_ct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat) {rest : List Instr}
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.block rest) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (.block (ws ++ rest)) s (Ψ a)) :
    RelCT isa (Two Φ) (.block (ws ++ rest)) (Two Ψ) :=
  RelCT.block_append (pin_ct [.rdi] [.rdi, .r12, .r9] (fun a => wsVal (B a) (w a))
    (fun a s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(hws a s₁ h₁).rdi, (hws a s₂ h₂).rdi])
    (by taint_decide)
    (fun a s h => WP.mono (hws a s h).ws_ok fun t ⟨h12, h9, _, k⟩ => fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (k.gpr (by decide)).trans (hws a s h).rdi
      · exact h12
      · exact h9)
    ht fun a s h => WP.seq_iff.mpr (WP.block_append_iff.mp (hw a s h)))

end VG.Proof.Rsa.X86_64
