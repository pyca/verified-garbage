module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTBase
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # The search's leaves are constant time (ARMv7)

Zeros at `out`, the terminal states and the request depend only on the
width and the pointers; `short` reads the tape's length, a stack argument,
then branches on public values.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search

variable {α : Type} {Φ : α → State → Prop}

theorem zeroOut_ct (h : Pins Φ [.r4, .r5]) : RelCT isa (Two Φ) zeroOut (fun _ _ => True) :=
  two_taint _ h (by taint_decide)

theorem exhausted_ct (h : Pins Φ [.r4, .r5]) : RelCT isa (Two Φ) exhausted (fun _ _ => True) :=
  two_taint _ h (by taint_decide)

theorem accept_ct : RelCT isa (Two Φ) (.block accept) (fun _ _ => True) :=
  two_taint [] (fun _ _ _ _ _ _ h => nomatch h) (by taint_decide)

theorem ldrSp_ct {Ψ : α → State → Prop} {r : Reg} {d : Nat} (hw : ∀ a s, Φ a s → WP isa (.block [.ldrSp r d]) s (Ψ a)) :
    RelCT isa (Two Φ) (.block [.ldrSp r d]) (Two Ψ) :=
  two_post ((VG.Proof.Bignum.Arm.loadStack_ct r d).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) fun _ _ _ => trivial) hw

/-- A state from which `short` runs: `used` octets consumed. -/
def ShortCT (p : SearchPublic) (used : Nat) (s : State) : Prop :=
  ∃ o, SearchBase p o s ∧ s.gpr .r8 = BitVec.ofNat 32 used

/-- After its load of the tape's length. -/
def ShortCT' (p : SearchPublic) (used : Nat) (s : State) : Prop :=
  ShortCT p used s ∧ s.gpr .r0 = BitVec.ofNat 32 p.randLen

theorem short_load (p : SearchPublic) (used : Nat) (s : State) (h : ShortCT p used s) :
    WP isa (.block [arg .r0 0 4]) s (ShortCT' p used) := by
  obtain ⟨o, hb, h8⟩ := h
  refine WP.mono (withRest_all [.r0] (Q := fun t => t.gpr .r0 = BitVec.ofNat 32 p.randLen ∧ t.mem = s.mem) ?_
    (by rfl) (by rfl)) fun t ⟨⟨h0, hm⟩, k⟩ => ⟨⟨o, hb.keep k hm, (k.gpr .r8 (by decide)).trans h8⟩, h0⟩
  unfold arg
  have c : pushBytes + 0 + 4 * 4 < 4096 := by decide
  ffrun [hb.arg_addr 4, hb.arg_read (j := 4) (by decide), hb.arg_value (j := 4) (by decide), randLen_arg hb.input, c]

theorem short_pins (p : SearchPublic) : Pins (ShortCT' p) [.r0, .r4, .r5, .r8] := by
  rintro a s₁ s₂ ⟨⟨_, h₁, e₁⟩, f₁⟩ ⟨⟨_, h₂, e₂⟩, f₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [f₁.trans f₂.symm, h₁.r4.trans h₂.r4.symm, h₁.r5.trans h₂.r5.symm, e₁.trans e₂.symm]

theorem short_ct (p : SearchPublic) : RelCT isa (Two (ShortCT p)) short (fun _ _ => True) := by
  unfold short
  refine RelCT.seq_block_append (RelCT.seq (ldrSp_ct (short_load p)) ?_)
  exact two_taint _ (short_pins p) (by taint_decide)

end VG.Proof.RsaKeyGen.Arm.Search
