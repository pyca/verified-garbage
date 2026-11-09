module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTLeaf
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFrames
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.CTLeaf
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFrames
meta import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Ffdh.Arm.Block
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract
meta import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract

/-! # A candidate call is constant time (ARMv7)

Its arguments are the public data's, and its leak is the next one of the
trace (`leak_of`): the candidate's own constant time gives the same trace
in both runs.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two Pins two_taint two_post two_piece)
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search

/-- The candidate's inputs, from its arguments. -/
theorem call_inputs {p : SearchPublic} {o s a u : State} {used k : Nat} (h : SearchLive p o used k s)
    (ha : a = allocated 32 s) (hd : ArgDone p o a used u) (hroom : used < p.randLen) :
    Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 p.ep) p.elen = p.eB ∧
      Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 p.pp) p.plen = searchP o ∧
      Spec.Rsa.bytesAt u.mem (BitVec.setWidth 64 (p.rp + BitVec.ofNat 32 used)) (p.randLen - used) =
        (searchRand o).drop used := by
  have hi := h.input
  have f := hi.facts
  have hargs : Frame [⟨State.addr p.S2, 32⟩] s.mem u.mem := by
    rw [hd.1.mem, ha]
    exact writeSlots_frame _ _ (N := 8) (by decide) _ fun e he => callArgs_bound p used e (List.mem_of_mem_take he)
  have hfu : Frame (changes o) o.mem u.mem := h.frame.trans (hargs.sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact ⟨_, by simp [changes], S2_sub hi⟩)
  refine ⟨?_, ?_, ?_⟩
  · change Spec.Rsa.bytesAt u.mem (State.addr p.ep) p.elen = _
    rw [hi.e_frame hfu, ← hi.2]; rfl
  · change Spec.Rsa.bytesAt u.mem (State.addr p.pp) p.plen = _
    rw [hi.p_frame hfu, ← hi.2]; rfl
  · change Spec.Rsa.bytesAt u.mem (State.addr (p.rp + BitVec.ofNat 32 used)) (p.randLen - used) = _
    rw [VG.Arm.addr_add (by have := f.nR; omega), bytesAt_drop, hi.random_frame hfu, ← hi.2]; rfl

/-- A state about to call the candidate, at the point `q`. -/
def CallCT (p : SearchPublic) (T : List Nat) (q : Pt) (u : State) : Prop :=
  ∃ o s, (searchResult o).trace = T ∧ SearchLive p o q.1 q.2.1 s ∧
    searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2 ∧ q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen ∧
    ArgDone p o (allocated 32 s) q.1 u

theorem call_pub {p : SearchPublic} {T : List Nat} {q : Pt} {u₁ u₂ : State}
    (h₁ : CallCT p T q u₁) (h₂ : CallCT p T q u₂) (sp : u₁.sp = u₂.sp) :
    (Proof.RsaKeyGen.candidateContract abi 112).pub (u₁.callEntry.withRegions (callRd p q.1) (callWr p))
      (u₂.callEntry.withRegions (callRd p q.1) (callWr p)) := by
  obtain ⟨o₁, s₁, T₁, l₁, f₁, hk, hroom, d₁⟩ := h₁
  obtain ⟨o₂, s₂, T₂, l₂, f₂, -, -, d₂⟩ := h₂
  have hl := l₁.input.facts.valid
  unfold Spec.RsaKeyGen.primeLenValid at hl
  have e1 := l₁.input.facts.e8
  have rl := l₁.input.facts.randLen
  unfold Spec.RsaKeyGen.primeEntropy at rl
  obtain ⟨eB₁, pB₁, rB₁⟩ := call_inputs l₁ rfl d₁ (by omega)
  obtain ⟨eB₂, pB₂, rB₂⟩ := call_inputs l₂ rfl d₂ (by omega)
  have lk₁ := leak_of T₁ f₁ hk
  have lk₂ := leak_of T₂ f₂ hk
  sig_pub [Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig, abi, argRegs, reduceClassify, Loc.val]
  simp only [d₁.sa0, d₁.sa1, d₁.sa2, d₁.sa3, d₁.sa4, d₁.sa5, d₁.sa6, d₂.sa0, d₂.sa1, d₂.sa2, d₂.sa3, d₂.sa4,
    d₂.sa5, d₂.sa6, d₁.2.1, d₁.2.2.1, d₁.2.2.2.1, d₁.2.2.2.2, d₂.2.1, d₂.2.2.1, d₂.2.2.2.1, d₂.2.2.2.2,
    toNat_small (n := p.len) (by omega), toNat_small (n := p.elen) (by omega),
    toNat_small (n := p.plen) (by rcases l₁.input.facts.plen with e | e <;> omega),
    toNat_diff (a := p.randLen) (b := q.1) (by omega) (by omega), eB₁, pB₁, rB₁, eB₂, pB₂, rB₂, ← lk₁, ← lk₂]
  exact ⟨sp, by simp only [and_self]⟩

/-- A state before the candidate, at the point `q`. -/
def CandCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  LiveCT p T q s ∧ q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen

/-- The candidate's frame allocated. -/
def AllocCT (p : SearchPublic) (T : List Nat) (q : Pt) (a : State) : Prop :=
  ∃ s, CandCT p T q s ∧ a = allocated 32 s

/-- `j` of the candidate's arguments stored. -/
def ArgCT (p : SearchPublic) (T : List Nat) (j : Nat) (q : Pt) (u : State) : Prop :=
  ∃ o s, (searchResult o).trace = T ∧ SearchLive p o q.1 q.2.1 s ∧
    searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2 ∧ q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen ∧
    ArgCtx p o (allocated 32 s) q.1 j u ∧ ArgRegs p u

theorem arg_pins (p : SearchPublic) (T : List Nat) (j : Nat) : Pins (ArgCT p T j) [.lr] := by
  rintro q s₁ s₂ ⟨_, _, _, _, _, _, _, c₁, _⟩ ⟨_, _, _, _, _, _, _, c₂, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact c₁.lr.trans c₂.lr.symm

theorem argHead_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (AllocCT p T)) (.block argHead) (Two (ArgCT p T 0)) :=
  two_piece [] (fun _ _ _ _ _ _ h => nomatch h) (by taint_decide) fun q a ⟨s, ⟨⟨o, hT, hl, hf⟩, hk, hr⟩, ha⟩ => by
    subst ha
    exact WP.mono (argHead_ok hl) fun u ⟨⟨c, r⟩, _⟩ => ⟨o, s, hT, hl, hf, hk, hr, c, r⟩

theorem argWord_ct (p : SearchPublic) (T : List Nat) {j : Nat} (hj : j < 7) {adjust : List Instr}
    {f : Nat → BitVec 32 → BitVec 32}
    (hadj : ∀ used t, t.gpr .r8 = BitVec.ofNat 32 used →
      WP isa (.block adjust) t fun t' => (t'.gpr .r12 = f used (t.gpr .r12) ∧ t'.mem = t.mem) ∧ Rest [.r12] t t')
    (hv : ∀ o used, SearchInput p o → (callArgs p used)[j]? = some (j, f used (stackArg o j)))
    {hc : VG.Taint.Hint VG.Arm.Taint.T}
    (htaint : (taint.check (Taint.ofRegs [.lr]) (.block (adjust ++ ([.str .r12 .lr (4 * j)] : List Instr))) hc).isSome = true) :
    RelCT isa (Two (ArgCT p T j)) (.block (argWord j adjust)) (Two (ArgCT p T (j + 1))) := by
  refine two_post ?_ fun q u ⟨o, s, hT, hl, hf, hk, hr, c, r⟩ =>
    WP.mono (argWord_ok hj (hadj q.1) (hv o q.1 hl.input) c) fun t ⟨c', k⟩ => ⟨o, s, hT, hl, hf, hk, hr, c', r.keep k⟩
  change RelCT isa _ (.block ([arg .r12 32 j] ++ (adjust ++ [.str .r12 .lr (4 * j)]))) _
  refine RelCT.block_append (RelCT.seq (ldrSp_ct (Ψ := ArgCT p T j) fun q u ⟨o, s, hT, hl, hf, hk, hr, c, r⟩ => ?_)
    (two_taint _ (arg_pins p T j) htaint))
  have c1 : pushBytes + 32 + 4 * j < 4096 := by unfold pushBytes; omega
  refine WP.mono (withRest_all [.r12] (Q := fun t => t.mem = u.mem) ?_ (by rfl) (by rfl))
    fun t ⟨hm, k⟩ => ⟨o, s, hT, hl, hf, hk, hr, c.keep k hm, r.keep k⟩
  ffrun [c.arg_addr j, c.arg_read (j := j) (by omega), c1]

theorem args_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (AllocCT p T)) (.block arguments) (Two (ArgCT p T 7)) := by
  have w0 := argWord_ct p T (j := 0) (f := fun _ => id) (by decide) adjust_none
    (fun o used hi => hv_of hi used 0 id (by simp [callArgs, searchOfState])) (by taint_decide)
  have w1 := argWord_ct p T (j := 1) (f := fun _ => id) (by decide) adjust_none
    (fun o used hi => hv_of hi used 1 id (by simp [callArgs, searchOfState])) (by taint_decide)
  have w2 := argWord_ct p T (j := 2) (f := fun _ => id) (by decide) adjust_none
    (fun o used hi => hv_of hi used 2 id (by simp [callArgs, searchOfState])) (by taint_decide)
  have w3 := argWord_ct p T (j := 3) (f := fun used => (· + BitVec.ofNat 32 used)) (by decide) adjust_add
    (fun o used hi => hv_of hi used 3 (· + BitVec.ofNat 32 used) (by simp [callArgs, searchOfState])) (by taint_decide)
  have w4 := argWord_ct p T (j := 4) (f := fun used => (· - BitVec.ofNat 32 used)) (by decide) adjust_sub
    (fun o used hi => hv_of hi used 4 (· - BitVec.ofNat 32 used) (by simp [callArgs, searchOfState])) (by taint_decide)
  have w5 := argWord_ct p T (j := 5) (f := fun _ => id) (by decide) adjust_none
    (fun o used hi => hv_of hi used 5 id (by simp [callArgs, searchOfState])) (by taint_decide)
  have w6 := argWord_ct p T (j := 6) (f := fun _ => id) (by decide) adjust_none
    (fun o used hi => hv_of hi used 6 id (by simp [callArgs, searchOfState])) (by taint_decide)
  rw [arguments_eq]
  exact RelCT.block_append ((argHead_ct p T).seq (RelCT.block_append (w0.seq (RelCT.block_append (w1.seq
    (RelCT.block_append (w2.seq (RelCT.block_append (w3.seq (RelCT.block_append (w4.seq
      (RelCT.block_append (w5.seq w6)))))))))))))

theorem call_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (ArgCT p T 7)) c.call (fun _ _ => True) := by
  intro s t traceS traceT u v ⟨q, hs, ht, sp⟩ runS runT
  have ready {w : State} (hw : ArgCT p T 7 q w) : CallCT p T q w := by
    obtain ⟨o, s', hT, hl, hf, hk, hr, cx, rg⟩ := hw
    exact ⟨o, s', hT, hl, hf, hk, hr, cx, rg⟩
  have ct : RelCT isa (fun a b => ArgCT p T 7 q a ∧ ArgCT p T 7 q b ∧ a.sp = s.sp ∧ b.sp = s.sp) c.call
      (fun _ _ => True) := by
    refine VG.Arm.RelCT.call c.verified.1 c.verified.2.1 (callRd p q.1) (callWr p) ?_
    intro a b ⟨ha, hb, spA, spB⟩
    obtain ⟨oa, sa, _, la, _, _, hra, da, ra⟩ := ha
    obtain ⟨ob, sb, _, lb, _, _, hrb, db, rb⟩ := hb
    have hla := la.input.facts.valid
    unfold Spec.RsaKeyGen.primeLenValid at hla
    obtain ⟨cova, covWa⟩ := call_covers la rfl ⟨da, ra⟩ (by omega)
    obtain ⟨covb, covWb⟩ := call_covers lb rfl ⟨db, rb⟩ (by omega)
    exact ⟨call_pre ⟨da, ra⟩ la.used_le, call_pre ⟨db, rb⟩ lb.used_le,
      call_pub (ready ⟨oa, sa, by assumption, la, by assumption, by assumption, hra, da, ra⟩)
        (ready ⟨ob, sb, by assumption, lb, by assumption, by assumption, hrb, db, rb⟩) (spA.trans spB.symm),
      cova, covWa, covb, covWb⟩
  exact ct _ _ _ _ _ _ ⟨hs, ht, rfl, sp.symm⟩ runS runT

/-- After the candidate: what it left. -/
def AfterCT (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  ∃ o, (searchResult o).trace = T ∧ SearchLive p o q.1 q.2.1 t ∧
    searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2 ∧ q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen ∧
    CandPost p (searchP o) (searchRand o) q.1 t

theorem candidateRun_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (CandCT p T)) (candidateRun c.call) (Two (AfterCT p T)) := by
  refine two_post ?_ fun q s ⟨⟨o, hT, hl, hf⟩, hk, hr⟩ =>
    WP.mono (candidateRun_ok c hl hr) fun t ⟨ht, hp⟩ => ⟨o, hT, ht, hf, hk, hr, hp⟩
  unfold candidateRun
  refine VG.Proof.Ffdh.Arm.KeySearch.alloc_ct (R := fun _ _ => True) ?_
  refine (RelCT.seq (args_ct p T) (call_ct c p T)).mono ?_ fun _ _ h => h
  rintro _ _ ⟨s, t, ⟨q, hs, ht, sp⟩, rfl, rfl⟩
  refine ⟨q, ⟨s, hs, rfl⟩, ⟨t, ht, rfl⟩, ?_⟩
  change s.sp - BitVec.ofNat 32 32 = t.sp - BitVec.ofNat 32 32
  rw [sp]

end VG.Proof.RsaKeyGen.Arm.Search
