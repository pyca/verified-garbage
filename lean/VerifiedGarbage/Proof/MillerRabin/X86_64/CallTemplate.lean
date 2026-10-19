module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Bignum.X86_64.Template

/-!
# The round's body over a Montgomery multiplication with calls

The round's body has no calls of its own: it commutes with inlining
(`body_inline`), and its calls can be inlined if the multiplication's can
(`body_inlineOk`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.MillerRabin.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum.X86_64 (inlineOk_seqs inline_seqs inline_of_noCalls map_inline_of_noCalls)

private theorem k_seq (a b : Prog isa) : (Code.seq a b).InlineOk = (a.InlineOk && b.InlineOk) := rfl
private theorem k_ite (c : Cond) (a b : Prog isa) : (Code.ite c a b).InlineOk = (a.InlineOk && b.InlineOk) := rfl
private theorem k_loop (a : Prog isa) (c : Cond) : (Code.loop a c).InlineOk = a.InlineOk := rfl
private theorem k_empty : (Code.block ([] : List Instr) : Prog isa).InlineOk = true := rfl

theorem body_inlineOk (mul : Nat → Nat → Nat → Prog isa) (hm : ∀ o a b, (mul o a b).InlineOk = true) :
    (VG.Impl.MillerRabin.X86_64.body mul).InlineOk = true := by
  have hp : (VG.Impl.MillerRabin.X86_64.body (fun _ _ _ => .block [])).InlineOk = true := by decide +kernel
  unfold VG.Impl.MillerRabin.X86_64.body preparedRound tabBuild mrExpLoop mrWin mrSq mrLast at hp ⊢
  repeat' first
    | rw [inlineOk_seqs] at *
    | rw [k_seq] at *
    | rw [k_ite] at *
    | rw [k_loop] at *
    | rw [List.all_append] at *
    | rw [List.all_cons] at *
  repeat' rw [hm]
  repeat' rw [k_empty] at hp
  exact hp

theorem body_inline (mul : Nat → Nat → Nat → Prog isa) :
    (VG.Impl.MillerRabin.X86_64.body mul).inline =
      VG.Impl.MillerRabin.X86_64.body (fun o a b => (mul o a b).inline) := by
  unfold VG.Impl.MillerRabin.X86_64.body preparedRound tabBuild mrExpLoop mrWin mrSq mrLast
  simp only [Code.inline, inline_seqs, List.map_append, List.map_cons, List.map_nil]
  simp (disch := decide) only [inline_of_noCalls, map_inline_of_noCalls]

end VG.Proof.MillerRabin.X86_64
