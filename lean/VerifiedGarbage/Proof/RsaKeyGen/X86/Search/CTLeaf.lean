module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CTBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CTBase
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Taint

-- separate module: the search's constant-time proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # The search's leaves in constant time (i686)

Zeros at `out`, the terminal states, the request and the short tape depend
only on the public arguments, which they read from the stack: each load of
one is a piece the stack pointer fixes, after which the value it loaded is
the same in both runs, from the functional proofs (`zeroHead_ok`,
`shortHead_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)

/-- A state of the search's body, with the public data `P a`. -/
def BaseOf {α : Type} (P : α → SearchPublic) (a : α) (s : State) : Prop := ∃ o, SearchBase (P a) o s

theorem baseOf_pins {α : Type} (P : α → SearchPublic) : Pins (BaseOf P) [.esp] := by
  rintro a s₁ s₂ ⟨_, h₁⟩ ⟨_, h₂⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact h₁.sp.trans h₂.sp.symm

/-- `zeroOut`'s loads: the output's pointer and length. -/
theorem zeroHead_ok {p : SearchPublic} {o s : State} (hb : SearchBase p o s) :
    WP isa (.block [.mov .edx (.mem (param 0 0)), .mov .ecx (.mem (param 0 1)), .mov .eax (.imm 0)]) s
      fun t => t.gpr .edx = p.op ∧ t.gpr .ecx = BitVec.ofNat 32 p.len ∧ t.gpr .esp = p.S1 := by
  have hop : p.op = arg o 0 := by rw [← hb.input.2]; rfl
  simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 0) (d := 20) rfl, hb.arg_ea (i := 1) (d := 24) rfl,
    hb.arg_in (i := 0) (by decide), hb.arg_in (i := 1) (by decide), hb.arg_val (i := 0) (by decide),
    hb.arg_val (i := 1) (by decide), hb.input.len_arg, hop]
  exact hb.sp

theorem zeroOut_ct {α : Type} (P : α → SearchPublic) : RelCT isa (Two (BaseOf P)) zeroOut fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_piece (Ψ := fun a t => t.gpr .edx = (P a).op ∧ t.gpr .ecx = BitVec.ofNat 32 (P a).len ∧
    t.gpr .esp = (P a).S1) [.esp] (baseOf_pins P) (by taint_decide) fun a s ⟨o, hb⟩ => zeroHead_ok hb) ?_
  refine two_taint [.edx, .ecx, .esp] (fun a s₁ s₂ h₁ h₂ r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]

theorem exhausted_ct {α : Type} (P : α → SearchPublic) :
    RelCT isa (Two (BaseOf P)) exhausted fun _ _ => True := by
  unfold exhausted
  refine RelCT.seq (two_piece (Ψ := BaseOf P) [.esp] (baseOf_pins P) (by taint_decide) fun a s ⟨o, hb⟩ =>
    WP.mono (terminal_ok s 3) fun t ⟨⟨_, _, _, hm⟩, k, sy⟩ => ⟨o, hb.step k (by decide) sy hm⟩) (zeroOut_ct P)

theorem accept_ct {α : Type} {Φ : α → State → Prop} : RelCT isa (Two Φ) (.block accept) fun _ _ => True :=
  two_taint [] (fun _ _ _ _ _ _ h => nomatch h) (by taint_decide)

theorem request_ct {α : Type} (P : α → SearchPublic) : RelCT isa (Two (BaseOf P)) (.block request) fun _ _ => True :=
  two_taint [.esp] (baseOf_pins P) (by taint_decide)

/-- A state from which `short` runs: `used` octets consumed. -/
def ShortCT (p : SearchPublic) (used : Nat) (s : State) : Prop :=
  ∃ o, SearchBase p o s ∧ s.gpr .esi = BitVec.ofNat 32 used ∧ used ≤ p.randLen

/-- `short`'s comparison: the tape left with the budget. -/
theorem shortHead_ok {p : SearchPublic} {o s : State} {used : Nat} (hb : SearchBase p o s)
    (hsi : s.gpr .esi = BitVec.ofNat 32 used) (hu : used ≤ p.randLen) :
    WP isa (.block [.mov .ecx (.mem (param 0 1)), .mov .eax (.imm 32769), .mul .ecx, .mov .ebp (.reg .eax),
      .mov .eax (.mem (param 0 8)), .alu .sub .eax (.reg .esi), .alu .cmp .eax (.reg .ebp)]) s
      fun t => (∃ o, SearchBase p o t) ∧ t.zf = some (decide (p.randLen - used = 32769 * p.len)) := by
  have hi := hb.input
  have hv := hi.len_valid
  have rl := hi.facts.randLen
  unfold Spec.RsaKeyGen.primeEntropy at rl
  refine WP.mono (WP.blockKeep [.eax, .ecx, .edx, .ebp]
    (Q := fun t => t.zf = some (decide (p.randLen - used = 32769 * p.len)) ∧ t.mem = s.mem) ?_ (by rfl))
    fun t ⟨⟨he, hm⟩, k, sy⟩ => ⟨⟨o, hb.step k (by decide) sy hm⟩, he⟩
  simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 1) (d := 24) rfl, hb.arg_ea (i := 8) (d := 52) rfl,
    hb.arg_in (i := 1) (by decide), hb.arg_in (i := 8) (by decide), hb.arg_val (i := 1) (by decide),
    hb.arg_val (i := 8) (by decide), hi.len_arg, hi.randLen_arg, hsi, execMul,
    show (32769 : BitVec 32).toNat = 32769 from rfl, toNat_small32 (show p.len < 2 ^ 32 by omega),
    BitVec.ofNat_sub_ofNat_of_le _ _ (show used < 2 ^ 32 by omega) hu]
  rw [sub_eq_beq (by omega) (by omega), Nat.mul_comm]

theorem short_ct (p : SearchPublic) : RelCT isa (Two (ShortCT p)) short fun _ _ => True := by
  unfold short
  refine RelCT.seq (two_piece (Ψ := fun used t => (∃ o, SearchBase p o t) ∧
      t.zf = some (decide (p.randLen - used = 32769 * p.len))) [.esp, .esi]
    (fun used s₁ s₂ ⟨_, h₁, e₁, _⟩ ⟨_, h₂, e₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.sp.trans h₂.sp.symm, e₁.trans e₂.symm]) (by taint_decide)
    fun used s ⟨o, hb, hsi, hu⟩ => shortHead_ok hb hsi hu) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact two_map (fun _ => ()) (fun _ _ h => h.1.1) (exhausted_ct (fun (_ : Unit) => p))
  · exact two_map (fun _ => ()) (fun _ _ h => h.1.1) (request_ct (fun (_ : Unit) => p))

end VG.Proof.RsaKeyGen.X86.Search
