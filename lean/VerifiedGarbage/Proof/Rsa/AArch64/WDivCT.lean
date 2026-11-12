module

public import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Impl.Rsa.AArch64.Keys
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# RSA private keys on AArch64: division by words is constant time

`wdiv` loads `w` and the stride once (`ws`, at the start of its `zeroA`);
every other address and count comes from them by register arithmetic, so the
taint analysis checks all of it from `x0`, `x12` and `x11` (`wdiv_ct`).
-/

@[expose] public section

namespace VG

theorem RelCT.assoc' {M : ISA} {P Q : M.State → M.State → Prop} {a b c : Prog M}
    (h : RelCT M P (.seq a (.seq b c)) Q) : RelCT M P (.seq (.seq a b) c) Q := by
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

end VG

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum.AArch64

/-- `wdiv` after its first `ws`. -/
def wdivRest (iX iM iR iT : Nat) (wmI lenL xb : List Instr) : Prog isa :=
  .seq zeroAcc (seqs [
    .block (base iM .x16 ++ base iT .x6 ++ lenL ++ wmI ++
      ([.sub .x .x8 .x13 .x12, .addImm .x .x8 .x8 1, movi .x7 0, .addImm .x .x9 .x6 8, mov .x17 .x9] : List Instr)),
    copyWords,
    .block wdivSet,
    R2Div.recip,
    .block (base iX .x16 ++ ([.lsl .x .x3 .x8 3, .add .x .x16 .x16 .x3] : List Instr) ++ base iR .x17 ++
      ([.subImm .x .x12 .x12 1] : List Instr)),
    copyWords,
    .block (base iR .x16 ++ ([mov .x11 .x16, .addImm .x .x12 .x12 1] : List Instr)),
    .loop (seqs [.block (xb ++ ([.lsl .x .x3 .x8 3, .add .x .x16 .x16 .x3, ld .x10 .x16] : List Instr)),
      R2Div.stepU, .block [.subImm .x .x8 .x8 1]]) (.nonzero .x .x8)])

theorem wdiv_eq (iX iM iR iT : Nat) (wmI lenL xb : List Instr) :
    wdiv iX iM iR iT wmI lenL xb =
      .seq (.seq (.block (ws ++ (base iR .x8 ++ [movi .x7 0]))) zeroAcc) (match wdivRest iX iM iR iT wmI lenL xb with
        | .seq _ r => r | r => r) := rfl

/-- `wdiv` leaks the same in runs from the same working space: the taint
analysis checks all of it but its first `ws` (`ht`). -/
theorem wdiv_ct {α : Type} {Φ Ψ : α → State → Prop} (B : α → Addr) (Z w : α → Nat)
    (hws : ∀ a s, Φ a s → Ws s (B a) (Z a) (w a)) {iX iM iR iT : Nat} {wmI lenL xb : List Instr}
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base iR .x8 ++ [movi .x7 0]))
      (wdivRest iX iM iR iT wmI lenL xb)) hc).isSome = true)
    (hw : ∀ a s, Φ a s → WP isa (wdiv iX iM iR iT wmI lenL xb) s (Ψ a)) :
    RelCT isa (Two Φ) (wdiv iX iM iR iT wmI lenL xb) (Two Ψ) := by
  rw [wdiv_eq]
  refine RelCT.assoc' (ws_ct B Z w hws ht fun a s h => ?_)
  have := hw a s h
  rw [wdiv_eq] at this
  exact WP.assoc this

theorem read1_eq {m m' : Mem} {a a' : Addr} (h : m a = m' a') : m.read a 1 = m'.read a' 1 := by
  simp [Mem.read, h]

/-- `wordGuard`'s loads from the header, then the rest. -/
theorem wordGuard_eq (sPl sQl : Nat) : wordGuard sPl sQl =
    ([ldh .x13 Public.sK, ldh .x14 sPl, ldh .x15 sQl, ldh .x16 Public.sN] : List Instr) ++
    ([.ldrb .x16 .x16 0, movi .x3 15, .logic .and .x .x9 .x13 .x3, .add .x .x4 .x14 .x14, .logic .eor .x .x4 .x4 .x13,
      .logic .orr .x .x9 .x9 .x4, .logic .eor .x .x4 .x14 .x15, .logic .orr .x .x9 .x9 .x4, .lsr .x .x16 .x16 7, movi .x3 1,
      .logic .eor .x .x16 .x16 .x3, .logic .orr .x .x9 .x9 .x16] : List Instr) := rfl

end VG.Proof.Rsa.AArch64
