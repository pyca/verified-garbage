module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.CTZero
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Call
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.CTZero
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Call
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Ffdh.X86.ABI
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Frame
import VerifiedGarbage.Proof.Ffdh.X86.KeyGenVerified
meta import VerifiedGarbage.Proof.Ffdh.X86.KeyGenVerified
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Two runs of an attempt (x86)

Two runs with the same public descriptor, octets consumed and budgets, whose
attempts have the same status, pass `vg_ffdh_generate_key` the same
arguments and the same public data (`callee_pub`), so their attempts leak
the same (`attempt_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite argumentPointer)

/-- Two entry states with the same public descriptor have the same arguments but the state's
words. -/
theorem args_eq {o₁ o₂ : State} (e : ofState o₁ = ofState o₂) {i : Nat}
    (hi : i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) :
    arg o₁ i = arg o₂ i := by
  have ofn : ∀ {x y : BitVec 32}, x.toNat = y.toNat → x = y := BitVec.eq_of_toNat_eq
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact congrArg KPub.xp e
  · exact congrArg KPub.yp e
  · exact congrArg KPub.up e
  · exact congrArg KPub.dp e
  · exact ofn (congrArg KPub.dlen e)
  · exact ofn (congrArg KPub.len e)
  · exact congrArg KPub.rp e
  · exact ofn (congrArg KPub.randLen e)
  · exact congrArg KPub.B e
  · exact ofn (congrArg KPub.slen e)
  · exact congrArg KPub.S e

theorem callArg_eq {o₁ o₂ : State} (e : ofState o₁ = ofState o₂) (used j : Nat) :
    callArg o₁ used j = callArg o₂ used j := by
  unfold callArg
  rw [args_eq e (i := 0) (by omega), args_eq e (i := 2) (by omega), args_eq e (i := 5) (by omega),
    args_eq e (i := 6) (by omega), args_eq e (i := 7) (by omega), args_eq e (i := 8) (by omega),
    args_eq e (i := 10) (by omega), args_eq e (i := 11) (by omega)]

theorem callee_pub {o₁ o₂ t₁ t₂ : State} {ds₁ ds₂ : List Nat} {f₁ f₂ : Nat → BitVec 32} {used : Nat}
    (e : ofState o₁ = ofState o₂) (h₁ : Fr o₁ ds₁ f₁ t₁) (h₂ : Fr o₂ ds₂ f₂ t₂)
    (hu : used + (arg o₁ 7).toNat ≤ (arg o₁ 9).toNat) (a₁ : ArgsAt o₁ used 11 t₁.mem) (a₂ : ArgsAt o₂ used 11 t₂.mem)
    (hst : attemptStatus (ofState o₁).a (ofState o₁).len ((randOf o₁).drop used) =
      attemptStatus (ofState o₂).a (ofState o₂).len ((randOf o₂).drop used)) (rd wr : List Region) :
    (Spec.Ffdh.generateKeyContract abi Proof.Ffdh.X86.stack).pub (t₁.callEntry.withRegions rd wr)
      (t₂.callEntry.withRegions rd wr) := by
  have A₁ := h₁.abi
  have A₂ := h₂.abi
  have hu₂ : used + (arg o₂ 7).toNat ≤ (arg o₂ 9).toNat := by
    rw [← args_eq e (i := 7) (by omega), ← args_eq e (i := 9) (by omega)]; exact hu
  have sp : o₁.gpr .esp = o₂.gpr .esp := congrArg KPub.sp e
  sig_pub [Spec.Ffdh.generateKeyContract, Spec.Ffdh.generateKeySig, abi, argSlots, argVal, argBytes]
  refine ⟨by simp only [h₁.esp, h₂.esp, sp], ?_⟩
  have c₁ := fun j (hj : j < 11) => ce_arg A₁ h₁.esp a₁ rd wr hj
  have c₂ := fun j (hj : j < 11) => ce_arg A₂ h₂.esp a₂ rd wr hj
  simp only [c₁ 0 (by decide), c₁ 1 (by decide), c₁ 2 (by decide), c₁ 3 (by decide), c₁ 4 (by decide),
    c₁ 5 (by decide), c₁ 6 (by decide), c₁ 7 (by decide), c₁ 8 (by decide), c₁ 9 (by decide), c₁ 10 (by decide),
    c₂ 0 (by decide), c₂ 1 (by decide), c₂ 2 (by decide), c₂ 3 (by decide), c₂ 4 (by decide),
    c₂ 5 (by decide), c₂ 6 (by decide), c₂ 7 (by decide), c₂ 8 (by decide), c₂ 9 (by decide), c₂ 10 (by decide)]
  have ca := callArg_eq e used
  refine ⟨?_, ca 0, ca 1, ca 2, ca 3, ca 4, ca 5, ca 6, ca 7, ca 8, ca 9, ca 10⟩
  rw [ret_eq A₁ h₁.esp, ret_eq A₂ h₂.esp]
  have b₁ := entry_bytes h₁ hu (t₁.unknowns 0)
  have b₂ := entry_bytes h₂ hu₂ (t₂.unknowns 0)
  simp only [callArg, Nat.reduceEqDiff, ↓reduceIte, argumentPointer] at b₁ b₂ ⊢
  rw [b₁.1, b₁.2, b₂.1, b₂.2]
  have hd : (ofState o₁).dom = (ofState o₂).dom := congrArg KPub.dom e
  show List.map _ (ofState o₁).dom ++ [attemptStatus (ofState o₁).a (ofState o₁).len ((randOf o₁).drop used)] =
    List.map _ (ofState o₂).dom ++ [attemptStatus (ofState o₂).a (ofState o₂).len ((randOf o₂).drop used)]
  rw [hd, hst]

/-- Relating two runs for each public datum. -/
theorem two_of {α : Type} {Φ : α → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ a, RelCT isa (fun s₁ s₂ => Φ a s₁ ∧ Φ a s₂) c Q) : RelCT isa (Two Φ) c Q :=
  fun _ _ _ _ _ _ ⟨a, h₁, h₂⟩ e₁ e₂ => h a _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂

/-- An attempt's public data: the loop's, and the attempt's status. -/
abbrev Ap := Lp × Nat

def AttAt (k : Ap) (s : State) : Prop :=
  ∃ o, Live k.1.1 o k.1.2.1 k.1.2.2.1 k.1.2.2.2 s ∧ k.1.2.1 + k.1.1.len ≤ k.1.1.randLen ∧
    attemptStatus k.1.1.a k.1.1.len ((randOf o).drop k.1.2.1) = k.2

/-- In the attempt's frame. -/
def FrAt (k : Ap) (f : State) : Prop := ∃ s, AttAt k s ∧ f = allocFrame argsBytes s

/-- With the arguments in the frame. -/
def CallAt (k : Ap) (t : State) : Prop :=
  ∃ o, ofState o = k.1.1 ∧ Fr o liveDs (liveF k.1.1 (o.gpr .esi) k.1.2.1 k.1.2.2.1 k.1.2.2.2) t ∧
    ArgsAt o k.1.2.1 11 t.mem ∧ k.1.2.1 + k.1.1.len ≤ k.1.1.randLen ∧
    attemptStatus k.1.1.a k.1.1.len ((randOf o).drop k.1.2.1) = k.2

theorem frAt_pins : Pins FrAt [.esi, .esp] := by
  intro k f₁ f₂ ⟨s₁, ⟨o₁, L₁, _⟩, e₁⟩ ⟨s₂, ⟨o₂, L₂, _⟩, e₂⟩ r hr
  subst e₁ e₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide), L₁.esi, L₂.esi]
  · rw [allocFrame_esp, allocFrame_esp, L₁.esp, L₂.esp]

/-- What the callee reads and writes, from the public descriptor. -/
abbrev callRdK (p : KPub) (used : Nat) : List Region :=
  [⟨p.dp.setWidth 64, p.dlen⟩, ⟨(p.rp + BitVec.ofNat 32 used).setWidth 64, p.len⟩]
abbrev callWrK (p : KPub) : List Region :=
  [⟨p.xp.setWidth 64, p.len⟩, ⟨p.yp.setWidth 64, p.len⟩, ⟨p.B.setWidth 64, p.slen * 8⟩,
    ⟨p.sp.setWidth 64 - 220#64 + BitVec.ofNat 64 176, 44⟩]

theorem call_ct (k : Ap) :
    RelCT isa (fun t₁ t₂ => CallAt k t₁ ∧ CallAt k t₂)
      (.call Spec.Ffdh.generateKeyApi.name Impl.Ffdh.X86.GenerateKey.code) fun _ _ => True := by
  refine RelCT.call Proof.Ffdh.X86.KeyGen.verified.1 Proof.Ffdh.X86.KeyGen.verified.2.1
    (callRdK k.1.1 k.1.2.1) (callWrK k.1.1) fun t₁ t₂ ⟨⟨o₁, e₁, F₁, a₁, hu₁, st₁⟩, ⟨o₂, e₂, F₂, a₂, hu₂, st₂⟩⟩ => ?_
  obtain ⟨⟨p, used, keys, scalars⟩, st⟩ := k
  dsimp only at e₁ e₂ F₁ F₂ a₁ a₂ hu₁ hu₂ st₁ st₂ ⊢
  subst e₁
  have r₁ : callRdK (ofState o₁) used = callRd o₁ used := rfl
  have w₁ : callWrK (ofState o₁) = callWr o₁ := rfl
  have r₂ : callRdK (ofState o₂) used = callRd o₂ used := rfl
  have w₂ : callWrK (ofState o₂) = callWr o₂ := rfl
  have c₁ := call_covers (t := t₁) F₁.abi hu₁ F₁.rd F₁.wr
  have hu₂' : used + (arg o₂ 7).toNat ≤ (arg o₂ 9).toNat := by have := hu₂; rw [← e₂] at this; exact this
  have c₂ := call_covers (t := t₂) F₂.abi hu₂' F₂.rd F₂.wr
  have eqR : callRd o₂ used = callRd o₁ used := by rw [← r₁, ← r₂, e₂]
  have eqW : callWr o₂ = callWr o₁ := by rw [← w₁, ← w₂, e₂]
  rw [r₁, w₁]
  rw [eqR, eqW] at c₂
  refine ⟨call_pre F₁.abi hu₁ F₁.esp a₁, ?_, callee_pub e₂.symm F₁ F₂ hu₁ a₁ a₂ (st₁.trans (by rw [e₂]; exact st₂.symm)) _ _,
    c₁.1, c₁.2, c₂.1, c₂.2, ?_⟩
  · rw [← eqR, ← eqW]
    exact call_pre F₂.abi hu₂' F₂.esp a₂
  · rw [F₁.esp, F₂.esp, show o₁.gpr .esp = o₂.gpr .esp from (congrArg KPub.sp e₂).symm]

theorem attempt_ct : RelCT isa (Two AttAt) attempt fun _ _ => True := by
  unfold attempt
  refine RelCT.frameAlloc ((RelCT.seq (two_piece (Ψ := CallAt) [.esi, .esp] frAt_pins (by taint_decide)
    fun k f ⟨s, ⟨o, L, hu, st⟩, e⟩ => ?_) (two_of call_ct)).mono
      (fun a b ⟨s₁, s₂, ⟨k, h₁, h₂⟩, e₁, e₂⟩ => ⟨k, ⟨s₁, h₁, e₁⟩, ⟨s₂, h₂, e₂⟩⟩) fun _ _ h => h)
  subst e
  have S := L.st
  obtain ⟨A, e⟩ := L.input
  obtain ⟨⟨p, used, keys, scalars⟩, sta⟩ := k
  dsimp only at e S hu st ⊢
  subst e
  exact WP.mono (arguments_ok S.alloc) fun t ⟨F, a⟩ => ⟨o, rfl, F, a, hu, st⟩

end VG.Proof.Ffdh.X86.KeySearch
