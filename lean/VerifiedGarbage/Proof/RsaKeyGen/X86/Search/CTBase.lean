module

public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Step
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Step

/-! ### `RsaKeyGen.X86.Search.Loop`, which this module and modules that import it used -/

section

/-! # The search's loop (i686)

Each iteration ends the search or goes on past a rejected candidate, which
consumed some of the tape (`iteration_ok`); the loop runs until the search
ends (`search_loop`), its measure the tape left.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult candidateOp)

theorem cmp_ok {u : State} {r : Reg} {n c : Nat} (hr : u.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32)
    (hc : c < 2 ^ 32) :
    WP isa (.block [.alu .cmp r (.imm (BitVec.ofNat 32 c))]) u fun t =>
      (t.zf = some (decide (n = c)) ∧ t.gpr r = u.gpr r ∧ t.mem = u.mem) ∧ Keep [r] u t ∧ t.syms = u.syms := by
  refine WP.blockKeep _ ?_ (by cases r <;> rfl)
  xrun [hr]
  exact sub_eq_beq hn hc

/-- A register a block wrote with its own value: kept. -/
theorem Keep.drop1 {r : Reg} {s t : State} (k : Keep [r] s t) (hr : t.gpr r = s.gpr r) : Keep [] s t :=
  ⟨fun q _ => by by_cases e : q = r
                 · subst e; exact hr
                 · exact k.gpr (by simpa using e), k.2.1, k.2.2⟩

theorem toNat_small' {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := toNat_small32 h

/-- The candidate, or the short tape without it. -/
theorem candidateStep_ok (c : Cand) {p : SearchPublic} {o s : State} {final : PrimeSearchResult} {used k : Nat}
    {tr : List Nat} (hl : SearchLive p o used k s) (hfin : final = (tailOf p o used k).consume used tr) (hk : k ≠ 0) :
    WP isa (candidateStep c.call) s (StepPost p o final used k tr) := by
  have hi := hl.input
  have f := hi.facts
  have hv := hi.len_valid
  have rl := f.randLen
  unfold primeEntropy at rl
  have hu := hl.used_le
  have hlen := rand_length hi
  have hb := hl.toSearchBase
  unfold candidateStep
  refine WP.seq (WP.mono (WP.blockKeep (is := [.mov .eax (.mem (param 0 8)), .alu .sub .eax (.reg .esi),
      .alu .cmp .eax (.mem (param 0 1))]) [.eax]
    (Q := fun t => t.cf = some (decide (p.randLen - used < p.len)) ∧ t.mem = s.mem) ?_ (by rfl))
    fun u ⟨⟨he, hm⟩, ku, sy⟩ => ?_)
  · simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
    xrun [State.ea, at_, hb.arg_ea (i := 8) (d := 52) rfl, hb.arg_ea (i := 1) (d := 24) rfl,
      hb.arg_in (i := 8) (by decide), hb.arg_in (i := 1) (by decide), hb.arg_val (i := 8) (by decide),
      hb.arg_val (i := 1) (by decide), hi.randLen_arg, hi.len_arg, hl.esi,
      BitVec.ofNat_sub_ofNat_of_le _ _ (show used < 2 ^ 32 by omega_using [hv, rl, hu]) hu,
      toNat_small' (n := p.len) (by omega_using [hv]), toNat_small' (n := p.randLen - used) (by omega_using [hv, rl])]
  have hu' := hl.keep ku sy hm
  refine WP.ite _ he (fun z => ?_) (fun z => ?_)
  · have z := of_decide_eq_true z
    refine WP.seq (WP.mono (zeroOut_ok hu'.toSearchBase) fun t ⟨⟨hf, hz⟩, kt, syt⟩ => ?_)
    have A := hi.abi
    have hbt := hu'.toSearchBase.keep kt (by decide) syt (frame_apart hi A.lowO hf hu'.saved) (out_changes hf)
    have ht : SearchLive p o used k t := ⟨hbt, hu'.used_le, hu'.remaining_le, (kt.gpr (by decide)).trans hu'.esi,
      (kt.gpr (by decide)).trans hu'.edi, (kt.gpr (by decide)).trans hu'.ebx⟩
    have hop : candidateOp p.len p.eB (searchP o) ((searchRand o).drop used) = none :=
      op_short (by rw [List.length_drop, hlen]; exact z)
    have e : final = if primeEntropy p.len ≤ p.randLen - used then
        ⟨.exhausted, used, tr ++ Search.entry p.len p.eB (searchP o) ((searchRand o).drop used)⟩
        else ⟨.entropy k (p.randLen - used), used,
          tr ++ Search.entry p.len p.eB (searchP o) ((searchRand o).drop used)⟩ := by
      rw [hfin, tailOf, Search.search_short hk hop, List.length_drop, hlen]
      split <;> rfl
    rw [e]
    exact WP.mono (short_ok ht.toSearchBase ht.esi ht.edi hu ht.remaining_le hz _) fun t ht =>
      done_post (fun hc => by have := hc.2.1; omega_using [z, this]) ht
  · have z := of_decide_eq_false z
    exact WP.seq (WP.mono (candidateRun_ok c hu' (by omega_using [hv, z])) fun t ⟨ht, hp⟩ => classify_ok ht hp hk hfin (by omega_using [hv, z]))

theorem status_lt (r : PrimeSearchResult) : r.status < 4 ∧ r.status ≠ 2 := by
  unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide

/-- What an iteration leaves. -/
def IterPost (p : SearchPublic) (o : State) (final : PrimeSearchResult) (used k : Nat) (tr : List Nat)
    (t : State) : Prop :=
  if Cont p o used k then
    isa.eval .e t = some true ∧ SearchLive p o (used + candUsed p o used) (nextK p o used k) t ∧
      final = (tailOf p o (used + candUsed p o used) (nextK p o used k)).consume (used + candUsed p o used)
        (tr ++ entryOf p o used)
  else isa.eval .e t = some false ∧ SearchDone p o final t

/-- One iteration: the search ends (the status is not 4), or goes on from
later in the tape (it is). -/
theorem iteration_ok (c : Cand) {p : SearchPublic} {o s : State} {final : PrimeSearchResult} {used k : Nat}
    {tr : List Nat} (hl : SearchLive p o used k s) (hfin : final = (tailOf p o used k).consume used tr) :
    WP isa (iteration c.call) s (IterPost p o final used k tr) := by
  have rem := hl.input.remaining_le
  have hk32 : k < 2 ^ 32 := by have := hl.remaining_le; omega_using [rem, this]
  unfold iteration
  refine WP.seq (WP.mono (cmp0_ok hl.edi hk32) fun u ⟨⟨he, hr, hm⟩, ku, sy⟩ => ?_)
  have hu := hl.keep (Keep.drop1 ku hr) sy hm
  refine WP.seq (WP.mono (Q := StepPost p o final used k tr) (WP.ite _ he (fun z => ?_) (fun z => ?_)) fun t ht => ?_)
  · have z := of_decide_eq_true z
    subst z
    have e : final = ⟨.exhausted, used, tr ++ []⟩ := by rw [hfin, tailOf, Search.search_zero]; rfl
    rw [e]
    exact WP.mono (exhausted_ok hu.toSearchBase hu.esi hu.used_le _) fun t ht =>
      done_post (fun hc => hc.1 rfl) ht
  · exact candidateStep_ok c hu hfin (of_decide_eq_false z)
  unfold StepPost at ht
  unfold IterPost
  split at ht
  · rename_i hc
    simp only [hc, ↓reduceIte]
    refine WP.mono (cmp_ok (c := 4) (n := 4) ht.1.ebx (by decide) (by decide)) fun t ⟨⟨et, hr, hmt⟩, kt, syt⟩ =>
      ⟨et, ht.1.keep (Keep.drop1 kt hr) syt hmt, ht.2⟩
  · rename_i hc
    simp only [hc, ↓reduceIte]
    have st := status_lt final
    refine WP.mono (cmp_ok (c := 4) ht.ebx (by omega_using [st]) (by decide)) fun t ⟨⟨et, hr, hmt⟩, kt, syt⟩ => ⟨?_, ?_⟩
    · change t.zf = some false
      rw [et, decide_eq_false (by omega_using [st])]
    · exact ⟨ht.toSearchBase.step kt (by decide) syt hmt, (kt.gpr (by decide)).trans ht.esi,
        (kt.gpr (by decide)).trans ht.edi, (kt.gpr (by decide)).trans ht.ebp,
        hr.trans ht.ebx, by rw [hmt]; exact ht.output, ht.bounds⟩

theorem candUsed_le {p : SearchPublic} {o : State} {used : Nat} (h : SearchInput p o) (hu : used ≤ p.randLen) :
    used + candUsed p o used ≤ p.randLen := by
  unfold candUsed
  split
  · rename_i x rest hop
    obtain ⟨m, hm, -, hum, -⟩ := used_bound h hu hop
    omega_using [hu]
  · omega_using [hu]

theorem search_loop (c : Cand) {p : SearchPublic} {o s : State} {final : PrimeSearchResult} {used k : Nat}
    {tr : List Nat} (hl : SearchLive p o used k s) (hfin : final = (tailOf p o used k).consume used tr) :
    WP isa (.loop (iteration c.call) .e) s (SearchDone p o final) := by
  refine WP.loop (fun m t => ∃ u k' tr', m = p.randLen - u ∧ u ≤ p.randLen ∧ SearchLive p o u k' t ∧
      final = (tailOf p o u k').consume u tr')
    (fun m t ⟨u, k', tr', hm, hle, ht, hf⟩ => WP.mono (iteration_ok c ht hf) fun t' ht' => ?_) _ s
    ⟨used, k, tr, rfl, hl.used_le, hl, hfin⟩
  unfold IterPost at ht'
  split at ht'
  · rename_i hc
    have hb := candUsed_le hl.input hle
    exact .inr ⟨ht'.1, _, by have := hc.2.2.2; omega_using [hm, hb, this], _, _, _, rfl, hb, ht'.2.1, ht'.2.2⟩
  · exact .inl ht'

end VG.Proof.RsaKeyGen.X86.Search

end

end

-- separate module: the search's constant-time proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # The search's loop points (i686)

Two runs of the search whose public data agree are at the same point of
the loop (`Pt`: the octets consumed, the counted candidates left and the
trace so far), from which the next candidate's leak, its status and the
octets it consumes are public (`leak_of`, `status_eq`, `used_eq`); the loop
state fixes the stack pointer and the registers of the point
(`live_pins`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.Dsa.X86 (Two Pins)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult candidateOp)

/-- A block's head, then its tail and what follows. -/
theorem RelCT.seq_block_append {M : ISA} {P Q : M.State → M.State → Prop} {l₁ l₂ : List M.Instr} {c : Prog M}
    (h : RelCT M P (.seq (.block l₁) (.seq (.block l₂) c)) Q) : RelCT M P (.seq (.block (l₁ ++ l₂)) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq b₁ c₁ =>
    cases e₂ with
    | seq b₂ c₂ =>
      rw [Exec.block_iff, execBlock_append] at b₁ b₂
      obtain ⟨⟨a₁, u₁⟩, ha₁, hb₁⟩ := Option.bind_eq_some_iff.mp b₁
      obtain ⟨⟨d₁, w₁⟩, hc₁, he₁⟩ := Option.map_eq_some_iff.mp hb₁
      obtain ⟨⟨a₂, u₂⟩, ha₂, hb₂⟩ := Option.bind_eq_some_iff.mp b₂
      obtain ⟨⟨d₂, w₂⟩, hc₂, he₂⟩ := Option.map_eq_some_iff.mp hb₂
      simp only [Prod.mk.injEq] at he₁ he₂
      obtain ⟨rfl, rfl⟩ := he₁
      obtain ⟨rfl, rfl⟩ := he₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.block ha₁) (.seq (.block hc₁) c₁))
        (.seq (.block ha₂) (.seq (.block hc₂) c₂))
      simp only [List.append_assoc] at ht ⊢
      exact ⟨ht, hq⟩

/-- Two postconditions of a block, which runs one way. -/
theorem WP.block_and {M : ISA} {is : List M.Instr} {s : M.State} {Q₁ Q₂ : M.State → Prop}
    (h₁ : WP M (.block is) s Q₁) (h₂ : WP M (.block is) s Q₂) : WP M (.block is) s fun t => Q₁ t ∧ Q₂ t := by
  induction is generalizing s with
  | nil => exact WP.block_nil_iff.mpr ⟨WP.block_nil_iff.mp h₁, WP.block_nil_iff.mp h₂⟩
  | cons i is ih =>
    obtain ⟨a, ea, ha⟩ := WP.block_cons_iff.mp h₁
    obtain ⟨b, eb, hb⟩ := WP.block_cons_iff.mp h₂
    rw [ea] at eb
    cases eb
    exact WP.block_cons_iff.mpr ⟨a, ea, ih ha hb⟩

/-- A point of the loop: octets consumed, counted candidates left, trace so far. -/
abbrev Pt := Nat × Nat × List Nat

/-- A loop state of a run whose public data is `p` and whose search's trace is `T`. -/
def LiveCT (p : SearchPublic) (T : List Nat) (q : Pt) (s : State) : Prop :=
  ∃ o, (searchResult o).trace = T ∧ SearchLive p o q.1 q.2.1 s ∧
    searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2

/-- The next candidate's leak, from the trace. -/
def nextLeak (T tr : List Nat) : List Nat :=
  ((T.drop tr.length).drop 1).take ((T.drop tr.length).headD 0)

def pubStatus (T tr : List Nat) : Nat := Search.statusOfLeak (nextLeak T tr)
def pubUsed (p : SearchPublic) (T tr : List Nat) : Nat := Search.usedOfLeak p.len (nextLeak T tr)

/-- Whether the search goes on past the next candidate, from public data. -/
def pubCont (p : SearchPublic) (T : List Nat) (q : Pt) : Prop :=
  q.2.1 ≠ 0 ∧ q.1 + p.len ≤ p.randLen ∧ (pubStatus T q.2.2 = 2 ∨ pubStatus T q.2.2 = 3) ∧
    pubUsed p T q.2.2 ≠ 0

instance (p : SearchPublic) (T : List Nat) (q : Pt) : Decidable (pubCont p T q) := by
  unfold pubCont; infer_instance

/-- The point past the next candidate. -/
def nextPt (p : SearchPublic) (T : List Nat) (q : Pt) : Pt :=
  (q.1 + pubUsed p T q.2.2, if pubStatus T q.2.2 = 3 then q.2.1 - 1 else q.2.1,
    q.2.2 ++ ((nextLeak T q.2.2).length :: nextLeak T q.2.2))

/-- With candidates left, the next leak is the candidate's. -/
theorem leak_of {p : SearchPublic} {T : List Nat} {q : Pt} {o : State}
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2)
    (hk : q.2.1 ≠ 0) :
    nextLeak T q.2.2 = Spec.RsaKeyGen.candidateLeak p.len p.eB (searchP o) ((searchRand o).drop q.1) := by
  obtain ⟨rest, hr⟩ := Search.search_trace (L := p.len) (eB := p.eB) (pB := searchP o) hk
    ((searchRand o).drop q.1)
  have e : T = q.2.2 ++ (Search.entry p.len p.eB (searchP o) ((searchRand o).drop q.1) ++ rest) := by
    rw [← hT, hfin]
    change q.2.2 ++ (tailOf p o q.1 q.2.1).trace = _
    rw [tailOf, hr]
  unfold nextLeak
  rw [e, List.drop_left]
  simp only [Search.entry, List.cons_append, List.drop_succ_cons, List.drop_zero, List.headD_cons]
  exact List.take_left' rfl

theorem status_eq {p : SearchPublic} {T : List Nat} {q : Pt} {o : State}
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2)
    (hk : q.2.1 ≠ 0) : candStatus p o q.1 = pubStatus T q.2.2 := by
  rw [pubStatus, leak_of hT hfin hk, candStatus, candOp, Search.status_of_leak]

theorem used_eq {p : SearchPublic} {T : List Nat} {q : Pt} {o : State} (hi : SearchInput p o)
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2)
    (hk : q.2.1 ≠ 0) : candUsed p o q.1 = pubUsed p T q.2.2 := by
  rw [pubUsed, leak_of hT hfin hk, ← Search.used_of_leak, List.length_drop, rand_length hi]
  rfl

theorem cont_iff {p : SearchPublic} {T : List Nat} {q : Pt} {o : State} (hi : SearchInput p o)
    (hT : (searchResult o).trace = T) (hfin : searchResult o = (tailOf p o q.1 q.2.1).consume q.1 q.2.2) :
    Cont p o q.1 q.2.1 ↔ pubCont p T q := by
  by_cases hk : q.2.1 = 0
  · exact ⟨fun h => absurd hk h.1, fun h => absurd hk h.1⟩
  · unfold Cont pubCont
    rw [status_eq hT hfin hk, used_eq hi hT hfin hk]

/-- The registers a loop state fixes. -/
theorem live_pins (p : SearchPublic) (T : List Nat) :
    Pins (LiveCT p T) [.esp, .esi, .edi, .ebx] := by
  rintro q s₁ s₂ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h₁.sp.trans h₂.sp.symm, h₁.esi.trans h₂.esi.symm, h₁.edi.trans h₂.edi.symm, h₁.ebx.trans h₂.ebx.symm]

end VG.Proof.RsaKeyGen.X86.Search
