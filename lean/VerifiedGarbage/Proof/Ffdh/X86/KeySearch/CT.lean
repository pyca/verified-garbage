module

public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.CTLoop
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Correct
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.CTLoop
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Entry
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Loop
meta import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Loop

/-! # The key search in constant time (x86)

Two runs whose public data agree start at the same loop point: the
arguments, the domain, the budgets and the statuses of the search's
attempts (`pub_point`). The entry is checked by the taint analysis from
`esp`, then from `esp` and the state's pointer (`entry_ct`); the loop leaks
its points alone (`loop_ct`); `finish` stores through `used`, which the
descriptor fixes (`finish_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.KeySearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.KeySearch
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite argumentPointer)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The loop point an entry state starts at. -/
def entryPt (s : State) : Kp :=
  ((ofState s, 0, (ofState s).keys, (ofState s).scalars), (searchOf s).statuses)

/-- An entry state at the point `q`. -/
def EntAt (q : Kp) (s : State) : Prop := KeySearchABI s ∧ entryPt s = q

theorem entAt_live {q : Kp} {s : State} (h : EntAt q s) :
    WP isa (.block entry) s (LiveCT q) := by
  obtain ⟨A, rfl⟩ := h
  refine WP.mono (entry_ok A) fun t L => ⟨s, L, ?_⟩
  simp only [entryPt, KPub.tail, keyTail, after, List.drop_zero]

theorem entry_ct : RelCT isa (Two EntAt) (.block entry) (Two LiveCT) := by
  refine two_post ?_ fun q s h => entAt_live h
  rw [show entry = [.mov .eax (.mem (argAt 0 12))] ++ entry.drop 1 from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece
    (Ψ := fun (q : Kp) t => t.gpr .eax = q.1.1.S ∧ t.gpr .esp = q.1.1.sp) [.esp]
    (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact congrArg (fun q : Kp => q.1.1.sp) (h₁.2.trans h₂.2.symm)) (by taint_decide) fun q s ⟨A, e⟩ => ?_)
    (two_taint [.eax, .esp] (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2, h₂.2]) (by taint_decide)))
  subst e
  have e12 : argAt 0 12 = ⟨.esp, 4 + 4 * 12⟩ := by simp [argAt, at_]
  have r12 : readSrc s (.mem (argAt 0 12)) = some (arg s 12) := by
    rw [e12, readSrc_mem rfl ⟨_, List.mem_append_right _ (aR_mem A), arg_in A (i := 12) (by decide)⟩]; rfl
  exact wp_movS r12 fun t U _ => WP.block_nil ⟨U.gpr, by rw [U.other _ (by decide)]; rfl⟩

/-- A finished search with the public descriptor `p`. -/
def DoneAt (p : KPub) (s : State) : Prop := ∃ o r, Done p o r s

theorem finish_ct : RelCT isa (Two fun (q : Kp) s => DoneAt q.1.1 s) (.block finish) fun _ _ => True := by
  have pin : Pins (fun (q : Kp) t => Any q.1.1 t ∧ t.gpr .ecx = q.1.1.up) [.esi, .esp] :=
    any_pins (fun q => q.1.1) fun _ _ h => h.1
  rw [show finish = [.mov .ecx (.mem (st upOff))] ++ finish.drop 1 from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece
    (Ψ := fun (q : Kp) t => Any q.1.1 t ∧ t.gpr .ecx = q.1.1.up) [.esi, .esp]
    (any_pins (fun (q : Kp) => q.1.1) fun q s ⟨_, _, D⟩ => D.any) (by taint_decide) fun q s ⟨o, r, D⟩ => ?_)
    (two_taint [.ecx, .esi, .esp] (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.2, h₂.2]
      · exact pin q s₁ s₂ h₁ h₂ .esi (by decide)
      · exact pin q s₁ s₂ h₁ h₂ .esp (by decide))
      (by taint_decide)))
  obtain ⟨⟨p, x⟩, sts⟩ := q
  dsimp only at D ⊢
  obtain ⟨A, rfl⟩ := D.input
  have S : St o doneDs (doneF (ofState o) (o.gpr .esi) r) s :=
    ⟨A, D.rd, D.wr, D.esp, D.esi, D.saved, D.frame, D.words⟩
  exact S.ld (Or.inr (Or.inl rfl)) (d := upOff) (by decide) (by decide) fun t St g _ _ _ =>
    WP.block_nil ⟨⟨o, _, _, rfl, St⟩, by rw [g]; rfl⟩

theorem wordsAt4 (m : Mem) (p : Addr) : Spec.Rsa.wordsAt m p 4 =
    [m.readW (p + BitVec.ofNat 64 0) 64, m.readW (p + BitVec.ofNat 64 8) 64, m.readW (p + BitVec.ofNat 64 16) 64,
      m.readW (p + BitVec.ofNat 64 24) 64] := rfl

/-- Two entry states whose public data agree start at the same loop point. -/
theorem pub_point {s t : State} (H : (Spec.Ffdh.keySearchContract abi stack).pub s t) : entryPt s = entryPt t := by
  sig_pub [Spec.Ffdh.keySearchContract, Spec.Ffdh.keySearchSig, abi, argSlots, argVal, argBytes] at H
  obtain ⟨SP, L, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁₂, L₃⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, Spec.Rsa.wordsAt, a6])
  obtain ⟨L₁, L₂⟩ := List.append_inj L₁₂ (by simp [Spec.Rsa.bytesAt, a6])
  have D := inj L₁
  rw [wordsAt4, wordsAt4] at L₂
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at L₂
  obtain ⟨k, c, _, _⟩ := L₂
  rw [BitVec.add_zero, BitVec.add_zero] at k
  have e : ofState s = ofState t := by
    simp only [ofState, KPub.mk.injEq]
    exact ⟨SP, a12, a0, a2, a4, a5, a8, a10, congrArg BitVec.toNat a7, congrArg BitVec.toNat a6,
      congrArg BitVec.toNat a9, congrArg BitVec.toNat a11, k, c, D⟩
  simp only [entryPt, e]
  exact congrArg _ L₃

theorem code_ct : RelCT isa (Two EntAt) Impl.Ffdh.X86.KeySearch.code fun _ _ => True := by
  unfold Impl.Ffdh.X86.KeySearch.code
  exact RelCT.seq entry_ct (RelCT.seq (two_post (Ψ := fun (q : Kp) s => DoneAt q.1.1 s) loop_ct
    fun q s ⟨o, L, _⟩ => WP.mono (loop_ok L) fun t D => ⟨o, _, D⟩) finish_ct)

theorem constantTime : ConstantTime isa (Spec.Ffdh.keySearchContract abi stack).pre
    (Spec.Ffdh.keySearchContract abi stack).pub Impl.Ffdh.X86.KeySearch.code := by
  intro s t tr ur sf tf S T H E F
  exact (code_ct _ _ _ _ _ _ ⟨entryPt s, ⟨keySearchABI_of S, rfl⟩, ⟨keySearchABI_of T, (pub_point H).symm⟩⟩
    E F).1

end VG.Proof.Ffdh.X86.KeySearch
