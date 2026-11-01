module

import VerifiedGarbage.Proof.Ffdh.X86.PSearch.CTAttempt
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Entry
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Loop
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.CTAttempt
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Entry
meta import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Loop
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Finish
public import VerifiedGarbage.Impl.Ffdh.X86.ParamSearch
public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.CTExits
public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Classify
public import VerifiedGarbage.Proof.Ffdh.X86.PSearch.Data
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # The parameter search in constant time (x86)

The tape, the arguments, the attempts and the table's address are public,
so two runs whose public data agree start at the same loop point
(`pub_point`), and the search from there, all its branches included, is a
function of that point. The entry is checked by the taint analysis from
`esp`, then from `esp` and the state's pointer (`entry_ct`); an iteration
branches alike in both runs and leaves them at the same next point
(`ct_step`), so the loop leaks the points alone (`loop_ct`); `finish` stores
through `used`, which the descriptor fixes (`finish_ct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.PSearch

open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Spec.Ffdh
open VG.Impl.Ffdh.X86.ParamSearch
open VG.Proof.Ffdh.X86.KeySearch (Ctl Aligned upd Scratch)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite argumentPointer)
open VG.Impl.Bignum.X86.PublicRt (argAt)

theorem Done.any {p : PPub} {o s : State} {r : ParameterSearchResult} (h : Done p o r s) : Any p s := by
  obtain ⟨A, rfl⟩ := h.input
  exact ⟨o, _, _, rfl, h.st⟩

theorem Rej.any {p : PPub} {o s : State} {used n : Nat} (h : Rej p o used n s) : Any p s :=
  LiveAt.any (q := (p, used, n)) ⟨o, h.1⟩

theorem branch_ct : RelCT isa (Two LiveAt) branch fun _ _ => True := by
  unfold branch
  refine RelCT.seq (two_piece (Ψ := fun q t => LiveAt q t ∧ isa.eval .e t = some (decide (q.2.2 = 0)))
    [.esi, .esp] liveAt_pins (by taint_decide)
    fun q s ⟨o, L⟩ => WP.mono (attempts_ok L) fun t ⟨L', e⟩ => ⟨⟨o, L'⟩, e⟩) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) (two_map id (fun _ _ h => h.1.1) exhausted_ct) ?_
  unfold attemptOrRequest
  refine RelCT.seq (two_piece (Ψ := fun q t => LiveAt q t ∧
      isa.eval .b t = some (decide (q.1.randLen - q.2.1 < q.1.len)))
    [.esi, .esp] (any_pins (fun q => q.1) fun _ _ h => h.1.1.any) (by taint_decide)
    fun q s ⟨⟨⟨o, L⟩, _⟩, _⟩ => WP.mono (room_ok L) fun t ⟨L', e⟩ => ⟨⟨o, L'⟩, e⟩) ?_
  refine two_ite (fun q _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) (two_map id (fun _ _ h => h.1.1) request_ct) ?_
  -- The attempt, from a tape that holds a candidate's octets.
  have hatt : ∀ (q : Lp) s, (LiveAt q s ∧ isa.eval .b s = some (decide (q.1.randLen - q.2.1 < q.1.len))) ∧
      isa.eval .b s = some false → LiveAt q s ∧ q.2.1 < q.1.randLen := by
    intro q s ⟨⟨⟨o, L⟩, e⟩, hf⟩
    rw [e] at hf
    simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at hf
    have A := L.input.1
    have hp := L.input.2
    have hl : 64 ≤ q.1.len := by rw [← hp]; exact (len_pos A).1
    exact ⟨⟨o, L⟩, by omega⟩
  refine RelCT.seq (two_post (Ψ := ClsAt) (two_map id hatt attempt_ct) fun q s h => ?_) classify_ct
  obtain ⟨⟨o, L⟩, hu⟩ := hatt q s h
  obtain ⟨p, used, n⟩ := q
  have hp := L.input.2
  dsimp only at hp L hu
  subst hp
  exact WP.mono (attempt_ok L hu) fun u ⟨Su, eu, _, cu⟩ => ⟨o, s, rfl, L, Su, eu, cu⟩

theorem iteration_ct : RelCT isa (Two LiveAt) iteration fun _ _ => True := by
  unfold iteration
  refine RelCT.seq (two_post (Ψ := fun q t => Any q.1 t) branch_ct fun q s ⟨o, L⟩ => WP.mono (branch_ok L)
    fun v hv => ?_) (two_taint [.esi, .esp] (any_pins (fun q => q.1) fun _ _ h => h) (by taint_decide))
  rcases hv with ⟨D, _⟩ | ⟨_, R⟩
  · exact D.any
  · exact R.any

/-- The loop point after a rejection. -/
abbrev Lp.next (q : Lp) : Lp := (q.1, q.2.1 + q.1.cu q.2.1, q.2.2 - 1)

def CTStep (q : Lp) (s : State) : Prop :=
  (q.1.cont q.2.1 q.2.2 ∧ isa.eval .e s = some true ∧ LiveAt q.next s) ∨
    (¬ q.1.cont q.2.1 q.2.2 ∧ isa.eval .e s = some false)

theorem ct_step (q : Lp) (s : State) (h : LiveAt q s) : WP isa iteration s (CTStep q) := by
  obtain ⟨p, used, n⟩ := q
  obtain ⟨o, L⟩ := h
  unfold iteration
  refine WP.seq (WP.mono (branch_ok L) fun v hv => ?_)
  rcases hv with ⟨D, stop⟩ | ⟨co, R⟩
  · exact WP.mono (guard_done D) fun t ⟨he, _⟩ => Or.inr ⟨stop, he⟩
  · exact WP.mono (guard_rej R) fun t ⟨he, Lt⟩ => Or.inl ⟨co, he, o, Lt⟩

private def LoopPair (n : Nat) (s t : State) : Prop := ∃ q : Lp, n = q.2.2 ∧ LiveAt q s ∧ LiveAt q t

private theorem iteration_pair (n : Nat) :
    RelCT isa (LoopPair n) iteration fun s t =>
      isa.eval .e s = isa.eval .e t ∧ (isa.eval .e s = some false → True) ∧
      (isa.eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hc := two_post (Φ := fun (q : Lp) s => n = q.2.2 ∧ LiveAt q s)
    (Ψ := fun q t => n = q.2.2 ∧ CTStep q t) (iteration_ct.mono
    (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.2, h₂.2⟩) fun _ _ h => h) fun q s h =>
      WP.mono (ct_step q s h.2) fun _ ht => ⟨h.1, ht⟩
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂⟩ => ⟨q, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, _, h₂⟩
  rcases h₁ with ⟨co, e₁, L₁⟩ | ⟨nc, e₁⟩
  · rcases h₂ with ⟨_, e₂, L₂⟩ | ⟨nc, _⟩
    · refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun _ => ⟨q.next.2.2, ?_, q.next, rfl, L₁, L₂⟩⟩
      have := co.1
      show q.2.2 - 1 < n
      omega
    · exact absurd co nc
  · rcases h₂ with ⟨co, _, _⟩ | ⟨_, e₂⟩
    · exact absurd co nc
    · refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun ht => ?_⟩
      rw [e₁] at ht
      cases ht

theorem loop_ct : RelCT isa (Two LiveAt) (.loop iteration .e) fun _ _ => True := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration) (c := .e) (Q := fun _ _ => True) LoopPair iteration_pair
    q.2.2 _ _ _ _ _ _ ⟨q, rfl, hs, ht⟩ he₁ he₂

/-- The loop point an entry state starts at. -/
def entryPt (s : State) : Lp := (ofState s, 0, (ofState s).attempts)

/-- An entry state at the point `q`. -/
def EntAt (q : Lp) (s : State) : Prop := PSearchABI s ∧ entryPt s = q

theorem entry_ct : RelCT isa (Two EntAt) (.block entry) (Two LiveAt) := by
  refine two_post ?_ fun q s ⟨A, e⟩ => WP.mono (entry_ok A) fun t L => ⟨s, by rw [← e]; exact L⟩
  rw [show entry = [.mov .eax (.mem (argAt 0 9))] ++ entry.drop 1 from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece
    (Ψ := fun (q : Lp) t => t.gpr .eax = q.1.S ∧ t.gpr .esp = q.1.sp) [.esp]
    (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact congrArg (fun q : Lp => q.1.sp) (h₁.2.trans h₂.2.symm)) (by taint_decide) fun q s ⟨A, e⟩ => ?_)
    (two_taint [.eax, .esp] (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2, h₂.2]) (by taint_decide)))
  subst e
  have e9 : argAt 0 9 = ⟨.esp, 4 + 4 * 9⟩ := by simp [argAt, at_]
  have r9 : readSrc s (.mem (argAt 0 9)) = some (arg s 9) := by
    rw [e9, readSrc_mem rfl ⟨_, List.mem_append_right _ (aR_mem A), arg_in A (i := 9) (by decide)⟩]; rfl
  exact wp_movS r9 fun t U _ => WP.block_nil ⟨U.gpr, by rw [U.other _ (by decide)]; rfl⟩

/-- A finished search with the public descriptor `p`. -/
def DoneAt (p : PPub) (s : State) : Prop := ∃ o r, Done p o r s

theorem finish_ct : RelCT isa (Two DoneAt) (.block finish) fun _ _ => True := by
  have pin : Pins (fun (p : PPub) t => Any p t ∧ t.gpr .ecx = p.up) [.esi, .esp] :=
    any_pins id fun _ _ h => h.1
  rw [show finish = [.mov .ecx (.mem (st upOff))] ++ finish.drop 1 from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece
    (Ψ := fun (p : PPub) t => Any p t ∧ t.gpr .ecx = p.up) [.esi, .esp]
    (any_pins id fun p s ⟨_, _, D⟩ => D.any) (by taint_decide) fun p s ⟨o, r, D⟩ => ?_)
    (two_taint [.ecx, .esi, .esp] (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.2, h₂.2]
      · exact pin q s₁ s₂ h₁ h₂ .esi (by decide)
      · exact pin q s₁ s₂ h₁ h₂ .esp (by decide))
      (by taint_decide)))
  obtain ⟨A, rfl⟩ := D.input
  exact D.st.ld (Or.inr (Or.inl rfl)) (d := upOff) (by decide) (by decide) fun t St g _ _ _ =>
    WP.block_nil ⟨⟨o, _, _, rfl, St⟩, by rw [g]; rfl⟩

theorem wordsAt4 (m : Mem) (p : Addr) : Spec.Rsa.wordsAt m p 4 =
    [m.readW (p + BitVec.ofNat 64 0) 64, m.readW (p + BitVec.ofNat 64 8) 64, m.readW (p + BitVec.ofNat 64 16) 64,
      m.readW (p + BitVec.ofNat 64 24) 64] := rfl

/-- Two entry states whose public data agree start at the same loop point. -/
theorem pub_point {s t : State} (H : contract.pub s t) : entryPt s = entryPt t := by
  sig_pub [contract, Spec.Ffdh.sievedParameterSearchContract, Spec.Ffdh.parameterSearchSig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at H
  obtain ⟨SP, sy, L, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁, L₂⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, a6])
  have D := inj L₁
  rw [wordsAt4, wordsAt4] at L₂
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at L₂
  obtain ⟨k, _, _, _⟩ := L₂
  rw [BitVec.add_zero, BitVec.add_zero] at k
  have e : ofState s = ofState t := by
    simp only [ofState, PPub.mk.injEq]
    exact ⟨SP, a9, a0, a2, a5, a7, congrArg BitVec.toNat a1, congrArg BitVec.toNat a3, congrArg BitVec.toNat a4,
      congrArg BitVec.toNat a6, congrArg BitVec.toNat a8, k, D, sy⟩
  simp only [entryPt, e]

theorem code_ct : RelCT isa (Two EntAt) Impl.Ffdh.X86.ParamSearch.code fun _ _ => True := by
  unfold Impl.Ffdh.X86.ParamSearch.code
  exact RelCT.seq entry_ct (RelCT.seq (two_post (Ψ := fun (q : Lp) s => DoneAt q.1 s) loop_ct
    fun q s ⟨o, L⟩ => WP.mono (loop_ok L) fun t D => ⟨o, _, D⟩) (two_map (fun q : Lp => q.1) (fun _ _ h => h)
      finish_ct))

theorem constantTime : ConstantTime isa contract.pre contract.pub Impl.Ffdh.X86.ParamSearch.code := by
  intro s t tr ur sf tf S T H E F
  exact (code_ct _ _ _ _ _ _ ⟨entryPt s, ⟨pSearchABI_of S, rfl⟩, ⟨pSearchABI_of T, (pub_point H).symm⟩⟩
    E F).1

end VG.Proof.Ffdh.X86.PSearch
