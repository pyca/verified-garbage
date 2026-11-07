module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CTStep
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Correct
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.CTStep
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Correct
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.Framework.X86.Taint

-- separate module: the search's constant-time proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # The search in constant time (i686)

Two runs whose public data agree have the same arguments, `e`, counted
candidates and trace (`pub_same`), so they start at the same loop point. The
entry loads the state's pointer from the stack, then reads through it
(`entry_ct`); an iteration branches alike in both runs and leaves them at
the same next point, from the trace (`ct_step`), so the loop leaks the
points alone (`loop_ct`), the octets consumed its measure; `finish` stores
through the state's and `used`'s pointers, which it loads from the stack
(`finish_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Proof.Dsa.X86 (Two Pins two_post two_taint two_piece two_map two_mono two_ite)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)

/-! ## The loop -/

/-- What an iteration from the point `q` leaves. -/
def CTNext (p : SearchPublic) (T : List Nat) (q : Pt) (t : State) : Prop :=
  (pubCont p T q ∧ isa.eval .e t = some true ∧ LiveCT p T (nextPt p T q) t) ∨
    (¬pubCont p T q ∧ isa.eval .e t = some false)

theorem entryOf_eq {p : SearchPublic} {T : List Nat} {q : Pt} {o : State}
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2)
    (hk : q.2.1 ≠ 0) : entryOf p o q.1 = (nextLeak T q.2.2).length :: nextLeak T q.2.2 := by
  rw [leak_of hT hfin hk]

theorem ct_step (c : Cand) (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) (h : LiveCT p T q s) :
    WP isa (iteration c.call) s (CTNext p T q) := by
  obtain ⟨o, hT, L, hf⟩ := h
  have ci := cont_iff L.input hT hf
  refine WP.mono (iteration_ok c L hf) fun t ht => ?_
  unfold IterPost at ht
  split at ht
  · rename_i hc
    have hk := hc.1
    have e : nextPt p T q = (q.1 + candUsed p o q.1, nextK p o q.1 q.2.1, q.2.2 ++ entryOf p o q.1) := by
      unfold nextPt nextK
      rw [← used_eq L.input hT hf hk, ← status_eq hT hf hk, entryOf_eq hT hf hk]
    refine .inl ⟨ci.mp hc, ht.1, ?_⟩
    rw [e]
    exact ⟨o, hT, ht.2.1, ht.2.2⟩
  · rename_i hc
    exact .inr ⟨fun h => hc (ci.mpr h), ht.1⟩

/-- Two loop states at the same point, `n` octets of the tape left. -/
def LoopPair (p : SearchPublic) (T : List Nat) (n : Nat) (s t : State) : Prop :=
  ∃ q : Pt, n = p.randLen - q.1 ∧ LiveCT p T q s ∧ LiveCT p T q t

theorem iteration_pair (c : Cand) (p : SearchPublic) (T : List Nat) (n : Nat) :
    RelCT isa (LoopPair p T n) (iteration c.call) fun s t =>
      isa.eval .e s = isa.eval .e t ∧ (isa.eval .e s = some false → True) ∧
      (isa.eval .e s = some true → ∃ m < n, LoopPair p T m s t) := by
  have hc := two_post (Φ := fun (q : Pt) s => n = p.randLen - q.1 ∧ LiveCT p T q s)
    (Ψ := fun q t => n = p.randLen - q.1 ∧ CTNext p T q t) ((iteration_ct c p T).mono
    (fun _ _ ⟨q, h₁, h₂⟩ => ⟨q, h₁.2, h₂.2⟩) fun _ _ h => h) fun q s h =>
      WP.mono (ct_step c p T q s h.2) fun _ ht => ⟨h.1, ht⟩
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂⟩ => ⟨q, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, _, h₂⟩
  rcases h₁ with ⟨co, e₁, L₁⟩ | ⟨nc, e₁⟩
  · rcases h₂ with ⟨_, e₂, L₂⟩ | ⟨nc, _⟩
    · refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun _ => ⟨p.randLen - (nextPt p T q).1, ?_, _, rfl, L₁, L₂⟩⟩
      obtain ⟨_, _, L, _⟩ := L₁
      have hle := L.used_le
      have h0 := co.2.2.2
      simp only [nextPt] at hle ⊢
      omega
    · exact absurd co nc
  · rcases h₂ with ⟨co, _, _⟩ | ⟨_, e₂⟩
    · exact absurd co nc
    · refine ⟨e₁.trans e₂.symm, fun _ => trivial, fun ht => ?_⟩
      rw [e₁] at ht
      cases ht

theorem loop_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (LiveCT p T)) (.loop (iteration c.call) .e) fun _ _ => True := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration c.call) (c := .e) (Q := fun _ _ => True) (LoopPair p T)
    (iteration_pair c p T) (p.randLen - q.1) _ _ _ _ _ _ ⟨q, rfl, hs, ht⟩ he₁ he₂

/-! ## The entry and the results -/

/-- An entry state, with the public data `p` and the trace `T`, after the push. -/
def EntryAt (p : SearchPublic) (T : List Nat) (_ : Unit) (s : State) : Prop :=
  ∃ o, SearchInput p o ∧ (searchResult o).trace = T ∧ s = pushed pushRegs o

/-- `mov eax, [state]`. -/
theorem stLoad_ok {p : SearchPublic} {o s : State} (hb : SearchBase p o s) :
    WP isa (.block [.mov .eax (.mem (param 0 11))]) s fun t => t.gpr .eax = p.stp ∧ t.gpr .esp = p.S1 := by
  have hst : p.stp = arg o 11 := by rw [← hb.input.2]; rfl
  simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 11) (d := 64) rfl, hb.arg_in (i := 11) (by decide),
    hb.arg_val (i := 11) (by decide), hst]
  exact hb.sp

theorem entry_ct (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (EntryAt p T)) (.block entry) (Two (LiveCT p T)) := by
  refine (two_post (Ψ := fun _ s => LiveCT p T (0, p.remaining, []) s) ?_ fun _ s ⟨o, hi, hT, e⟩ => ?_).mono
    (fun _ _ h => h) fun _ _ ⟨_, h₁, h₂⟩ => ⟨_, h₁, h₂⟩
  · rw [show entry = [.mov .eax (.mem (param 0 11))] ++ entry.drop 1 from rfl]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun (_ : Unit) t => t.gpr .eax = p.stp ∧ t.gpr .esp = p.S1)
      [.esp] (fun _ s₁ s₂ ⟨o₁, i₁, _, e₁⟩ ⟨o₂, i₂, _, e₂⟩ r hr => by
        obtain rfl := List.mem_singleton.mp hr
        subst e₁ e₂
        exact (push_base i₁).sp.trans (push_base i₂).sp.symm) (by taint_decide)
      fun _ s ⟨o, hi, _, e⟩ => by subst e; exact stLoad_ok (push_base hi))
      (two_taint [.eax, .esp] (fun _ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.1, h₂.1]
        · rw [h₁.2, h₂.2]) (by taint_decide)))
  · subst e
    have L := entry_ok hi
    obtain ⟨_, rfl⟩ := hi
    exact WP.mono L fun t L => ⟨o, hT, L, (consume_zero _).symm⟩

/-- A finished search with the public data `p`. -/
def DoneAt (p : SearchPublic) (_ : Unit) (s : State) : Prop := ∃ o r, SearchDone p o r s

/-- The results' head: `out_len`'s budget, and the state's pointer in `edx`. -/
theorem finHead_ok {p : SearchPublic} {o s : State} (hb : SearchBase p o s) :
    WP isa (.block (results.take 4)) s fun t => t.gpr .edx = p.stp ∧ t.gpr .esp = p.S1 := by
  have hi := hb.input
  have hv := hi.len_valid
  have hs : p.stp = arg o 11 := by rw [← hi.2]; rfl
  simp only [results, List.take, param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 1) (d := 24) rfl, hb.arg_ea (i := 11) (d := 64) rfl,
    hb.arg_in (i := 1) (by decide), hb.arg_in (i := 11) (by decide), hb.arg_val (i := 1) (by decide),
    hb.arg_val (i := 11) (by decide), execMul, hs]
  exact hb.sp

/-- After `used`'s pointer is loaded. -/
def FinB (p : SearchPublic) (v : State) : Prop := v.gpr .edx = p.up ∧ v.gpr .esp = p.S1

/-- After the state's words. -/
def FinA (p : SearchPublic) (u : State) : Prop :=
  u.gpr .esp = p.S1 ∧ WP isa (.block ((results.drop 13).take 1)) u (FinB p)

/-- With the state's pointer in `edx`. -/
def FinH (p : SearchPublic) (t : State) : Prop :=
  t.gpr .edx = p.stp ∧ t.gpr .esp = p.S1 ∧ WP isa (.block ((results.take 13).drop 4)) t (FinA p)

theorem finish_ct (p : SearchPublic) : RelCT isa (Two (DoneAt p)) (.block finish) fun _ _ => True := by
  rw [show finish = results.take 4 ++ ((results.take 13).drop 4 ++ ((results.drop 13).take 1 ++
    (results.drop 14 ++ Impl.Mont.X86.Compact.restoreRegs))) from rfl]
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun _ => FinH p) [.esp]
    (fun _ s₁ s₂ ⟨_, _, D₁⟩ ⟨_, _, D₂⟩ r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact D₁.sp.trans D₂.sp.symm) (by taint_decide)
    fun _ s ⟨o, r, D⟩ => ?_) ?_)
  · have hb := D.toSearchBase
    have H := results_head_ok D
    rw [show results.take 13 = results.take 4 ++ (results.take 13).drop 4 from rfl, WP.block_append_iff] at H
    exact WP.mono (WP.block_and H (finHead_ok hb)) fun t ⟨ht, he, hs⟩ => ⟨he, hs, WP.mono ht
      fun u ⟨⟨_, _, hbu⟩, ku, _⟩ => ⟨(ku.gpr (by decide)).trans hb.sp,
        WP.mono (WP.blockKeep [.edx] (upLoad_ok hbu) (by rfl)) fun v ⟨⟨he', _⟩, kv, _⟩ =>
          ⟨he', (kv.gpr (by decide)).trans hbu.sp⟩⟩⟩
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun _ => FinA p) [.edx, .esp]
    (fun _ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm]) (by taint_decide) fun _ _ h => h.2.2) ?_)
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun _ => FinB p) [.esp]
    (fun _ s₁ s₂ h₁ h₂ r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact h₁.1.trans h₂.1.symm) (by taint_decide) fun _ _ h => h.2) ?_)
  exact two_taint [.edx, .esp] (fun _ s₁ s₂ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

/-! ## The search -/

/-- An entry state with the public data and trace `pt`. -/
def EntCT (pt : SearchPublic × List Nat) (o : State) : Prop := SearchInput pt.1 o ∧ (searchResult o).trace = pt.2

theorem body_ct (c : Cand) (p : SearchPublic) (T : List Nat) :
    RelCT isa (Two (EntryAt p T)) (body c.call) fun _ _ => True := by
  unfold body
  exact RelCT.seq (entry_ct p T) (RelCT.seq (two_post (Ψ := fun _ s => DoneAt p () s) (loop_ct c p T)
    fun q s ⟨o, hT, L, hf⟩ => WP.mono (search_loop c L hf) fun t D => ⟨o, _, D⟩)
    (two_map (fun _ => ()) (fun _ _ h => h) (finish_ct p)))

theorem code_ct (c : Cand) : RelCT isa (Two EntCT) (code c.call) fun _ _ => True := by
  unfold code
  refine RelCT.frame (R := fun _ _ => True) (fun s₁ s₂ ⟨pt, h₁, h₂⟩ => h₁.1.sp_eq.symm.trans h₂.1.sp_eq) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, ⟨pt, h₁, h₂⟩, e₁, e₂⟩ x₁ x₂
  exact body_ct c pt.1 pt.2 _ _ _ _ _ _ ⟨(), ⟨s₁, h₁.1, h₁.2, e₁⟩, ⟨s₂, h₂.1, h₂.2, e₂⟩⟩ x₁ x₂

theorem wordsAt4 (m : Mem) (p : Addr) : Spec.Rsa.wordsAt m p 4 =
    [m.readW (p + BitVec.ofNat 64 0) 64, m.readW (p + BitVec.ofNat 64 8) 64, m.readW (p + BitVec.ofNat 64 16) 64,
      m.readW (p + BitVec.ofNat 64 24) 64] := rfl

/-- Two entry states whose public data agree have the same public data and trace. -/
theorem pub_same {s t : State} (H : contract.pub s t) :
    searchOfState s = searchOfState t ∧ (searchResult s).trace = (searchResult t).trace := by
  sig_pub [contract, Proof.RsaKeyGen.primeSearchContract, Proof.RsaKeyGen.primeSearchSig, abi, argSlots, argVal,
    argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at H
  obtain ⟨SP, sy, L, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := H
  have inj : ∀ {l l' : List Byte}, l.map (fun x => x.toNat) = l'.map (fun x => x.toNat) → l = l' :=
    fun h => (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp h
  obtain ⟨L₁, L₂⟩ := List.append_inj L (by simp [Spec.Rsa.bytesAt, Spec.Rsa.wordsAt, a4])
  obtain ⟨L₃, -⟩ := List.append_inj L₁ (by simp [Spec.Rsa.bytesAt, Spec.Rsa.wordsAt, a4])
  obtain ⟨L₄, L₅⟩ := List.append_inj L₃ (by simp [Spec.Rsa.bytesAt, a4])
  have D := inj L₄
  rw [wordsAt4, wordsAt4] at L₅
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at L₅
  obtain ⟨k, _, _, _⟩ := L₅
  rw [BitVec.add_zero, BitVec.add_zero] at k
  refine ⟨?_, L₂⟩
  simp only [searchOfState, SearchPublic.mk.injEq]
  exact ⟨a0, a2, a3, a5, a7, a9, a11, SP, congrArg BitVec.toNat a1, congrArg BitVec.toNat a4,
    congrArg BitVec.toNat a6, congrArg BitVec.toNat a8, congrArg BitVec.toNat a10, k, D, sy⟩

theorem constantTime (c : Cand) : ConstantTime isa contract.pre contract.pub (code c.call) := by
  intro s t tr ur sf tf S T H E F
  have P := pub_same H
  exact (code_ct c _ _ _ _ _ _ ⟨(searchOfState s, (searchResult s).trace), ⟨⟨S, rfl⟩, rfl⟩,
    ⟨⟨T, P.1.symm⟩, P.2.symm⟩⟩ E F).1

end VG.Proof.RsaKeyGen.X86.Search
