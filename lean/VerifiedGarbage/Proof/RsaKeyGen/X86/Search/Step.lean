module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Call
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Call
meta import VerifiedGarbage.Proof.Framework.Offset

-- separate module: the search's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-! # One candidate of the search (i686)

`classify`, after a candidate: the search ends (`SearchDone`), or goes on
past a rejected candidate from a later offset (`SearchIter`), as
`VG.Spec.RsaKeyGen.primeSearch` does (`Proof/RsaKeyGen/SearchSpec.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86.Search

open VG VG.X86
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly)
open VG.Impl.RsaKeyGen.X86.Search
open VG.Impl.Mont.X86 (at_)
open VG.Spec.RsaKeyGen (primeSearch primeEntropy PrimeSearchResult candidateOp)

/-- The search from octet `used` of the tape, with `remaining` counted
candidates left. -/
abbrev tailOf (p : SearchPublic) (o : State) (used remaining : Nat) : PrimeSearchResult :=
  primeSearch p.len p.eB (searchP o) remaining ((searchRand o).drop used)

/-- A loop state, whose search from there finishes as `final`. -/
def SearchIter (p : SearchPublic) (o : State) (final : PrimeSearchResult) (used remaining : Nat)
    (s : State) : Prop :=
  SearchLive p o used remaining s ∧ ∃ tr, final = (tailOf p o used remaining).consume used tr

/-- The candidate from `used`. -/
abbrev candOp (p : SearchPublic) (o : State) (used : Nat) : Option (Spec.RsaKeyGen.Candidate × List Byte) :=
  candidateOp p.len p.eB (searchP o) ((searchRand o).drop used)

/-- Its status, and the octets it consumed. -/
def candStatus (p : SearchPublic) (o : State) (used : Nat) : Nat :=
  Spec.RsaKeyGen.candidateStatus (candOp p o used)

def candUsed (p : SearchPublic) (o : State) (used : Nat) : Nat :=
  match candOp p o used with
  | some (_, rest) => (p.randLen - used) - rest.length
  | none => 0

/-- Whether the search goes on past the candidate from `used`: one was run,
rejected (too close, or counted), and it consumed something. -/
def Cont (p : SearchPublic) (o : State) (used k : Nat) : Prop :=
  k ≠ 0 ∧ used + p.len ≤ p.randLen ∧ (candStatus p o used = 2 ∨ candStatus p o used = 3) ∧
    candUsed p o used ≠ 0

instance (p : SearchPublic) (o : State) (used k : Nat) : Decidable (Cont p o used k) := by
  unfold Cont; infer_instance

/-- The counted candidates left past it. -/
def nextK (p : SearchPublic) (o : State) (used k : Nat) : Nat := if candStatus p o used = 3 then k - 1 else k

/-- Its entry in the trace. -/
abbrev entryOf (p : SearchPublic) (o : State) (used : Nat) : List Nat :=
  Search.entry p.len p.eB (searchP o) ((searchRand o).drop used)

/-- What a candidate leaves: the search going on from past it, or finished. -/
def StepPost (p : SearchPublic) (o : State) (final : PrimeSearchResult) (used k : Nat) (tr : List Nat)
    (t : State) : Prop :=
  if Cont p o used k then
    SearchLive p o (used + candUsed p o used) (nextK p o used k) t ∧
      final = (tailOf p o (used + candUsed p o used) (nextK p o used k)).consume (used + candUsed p o used)
        (tr ++ entryOf p o used)
  else SearchDone p o final t

theorem done_post {p : SearchPublic} {o t : State} {final : PrimeSearchResult} {used k : Nat} {tr : List Nat}
    (hc : ¬Cont p o used k) (hd : SearchDone p o final t) : StepPost p o final used k tr t := by
  unfold StepPost; rw [ite_eq_right hc]; exact hd

theorem rand_length {p : SearchPublic} {o : State} (h : SearchInput p o) : (searchRand o).length = p.randLen := by
  rw [← h.2]; simp [searchRand, Spec.Rsa.bytesAt, searchOfState]

theorem op_short {L : Nat} {eB pB r : List Byte} (h : r.length < L) : candidateOp L eB pB r = none := by
  unfold candidateOp Spec.RsaKeyGen.candidateStep Spec.RsaKeyGen.draw
  have : (r.take (8 * L / 8)).length ≠ 8 * L / 8 := by rw [List.length_take]; omega
  simp only [this, ite_false]
  rfl

theorem status_ofNat {t : State} {n : Nat} (h : (t.gpr .eax).toNat = n) :
    t.gpr .eax = BitVec.ofNat 32 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The octets a candidate consumed, the low half of `used`. -/
theorem used_low {s : State} {p : SearchPublic} {n : Nat}
    (hw : Spec.Rsa.wordsAt s.mem (p.up.setWidth 64) 1 = [BitVec.ofNat 64 n]) :
    s.mem.readW (p.up.setWidth 64) 32 = BitVec.ofNat 32 n := by
  have e : s.mem.readW (p.up.setWidth 64) 64 = BitVec.ofNat 64 n := by
    have := congrArg List.head? hw
    simpa [Spec.Rsa.wordsAt] using this
  exact low_half e

theorem SearchLive.keep {p : SearchPublic} {o s t : State} {used k : Nat} (h : SearchLive p o used k s)
    {ws : List Reg} (kt : Keep ws s t) (sy : t.syms = s.syms) (hm : t.mem = s.mem)
    (hws : ∀ r ∈ [Reg.esp, .esi, .edi, .ebx], r ∉ ws := by decide) : SearchLive p o used k t :=
  ⟨h.toSearchBase.step kt (hws _ (by simp)) sy hm, h.used_le, h.remaining_le,
    (kt.gpr (hws _ (by simp))).trans h.esi, (kt.gpr (hws _ (by simp))).trans h.edi,
    (kt.gpr (hws _ (by simp))).trans h.ebx⟩

/-- The candidate's head: the octets it consumed into `ecx`, and its status
compared with 1. -/
theorem head_ok {p : SearchPublic} {o s : State} {used remaining : Nat}
    (h : SearchLive p o used remaining s) {n st : Nat}
    (hw : Spec.Rsa.wordsAt s.mem (p.up.setWidth 64) 1 = [BitVec.ofNat 64 n])
    (hst : st < 4) (h0 : s.gpr .eax = BitVec.ofNat 32 st) :
    WP isa (.block [.mov .edx (.mem (param 0 2)), .mov .ecx (.mem (at_ .edx 0)), .alu .cmp .eax (.imm 1)]) s
      fun t => (t.gpr .ecx = BitVec.ofNat 32 n ∧ t.gpr .eax = BitVec.ofNat 32 st ∧ t.zf = some (decide (st = 1)) ∧
        t.mem = s.mem) ∧ Keep [.eax, .ecx, .edx] s t ∧ t.syms = s.syms := by
  have hi := h.input
  have A := hi.abi
  have hb := h.toSearchBase
  have hup : p.up = arg o 2 := by rw [← hi.2]; rfl
  refine WP.blockKeep _ ?_ (by rfl)
  have a : (arg o 2 + BitVec.ofNat 32 0).setWidth 64 = p.up.setWidth 64 := by rw [BitVec.add_zero, hup]
  have r : InRegions (s.rd ++ s.wr) (p.up.setWidth 64) 4 := by
    refine ⟨uR o, List.mem_append_right _ ?_, ?_⟩
    · rw [hb.wr, A.wr]; simp
    · rw [hup]; simpa using Offset.contains_base ((arg o 2).setWidth 64) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  simp only [param_eq, pushWords, Nat.reduceMul, Nat.reduceAdd]
  xrun [State.ea, at_, hb.arg_ea (i := 2) (d := 28) rfl, hb.arg_in (i := 2) (by decide),
    hb.arg_val (i := 2) (by decide), a, r, used_low hw, h0]
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_eq_beq (by omega) (by omega)]

theorem dec32 {k : Nat} (h1 : 1 ≤ k) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h1]

/-- After a rejected candidate of `n > 0` octets: its octets consumed, one
counted candidate fewer if counted (status 3). -/
theorem advance_ok {p : SearchPublic} {o s : State} {used k n st : Nat} (h : SearchLive p o used k s)
    (hc : s.gpr .ecx = BitVec.ofNat 32 n) (h0 : s.gpr .eax = BitVec.ofNat 32 st) (hst : st = 2 ∨ st = 3)
    (hk : k ≠ 0) (hu : used + n ≤ p.randLen) :
    WP isa (.seq (.block [.alu .add .esi (.reg .ecx), .alu .cmp .eax (.imm 3)])
      (.ite .e (.block [.alu .sub .edi (.imm 1)]) (.block []))) s
      (SearchLive p o (used + n) (if st = 3 then k - 1 else k)) := by
  have rem := h.input.remaining_le
  have hrl : k < 2 ^ 32 := by have := h.remaining_le; omega
  have rl := h.input.facts.randLen
  unfold primeEntropy at rl
  refine WP.seq (WP.mono (WP.blockKeep (is := [.alu .add .esi (.reg .ecx), .alu .cmp .eax (.imm 3)]) [.esi, .eax]
    (Q := fun t => t.gpr .esi = BitVec.ofNat 32 (used + n) ∧ t.zf = some (decide (st = 3)) ∧
      t.mem = s.mem) ?_ (by rfl)) fun u ⟨⟨h8, he, hm⟩, ku, sy⟩ => ?_)
  · xrun [h.esi, hc, h0, add_ofNat32]
    rw [show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, sub_eq_beq (by omega) (by omega)]
  have hb := h.toSearchBase.step ku (by decide) sy hm
  refine WP.ite _ he (fun h3 => ?_) (fun h3 => ?_)
  · have h3 := of_decide_eq_true h3
    rw [ite_eq_left h3]
    refine WP.mono (WP.blockKeep (is := [.alu .sub .edi (.imm 1)]) [.edi]
      (Q := fun t => t.gpr .edi = BitVec.ofNat 32 (k - 1) ∧ t.mem = u.mem) ?_ (by rfl))
      fun t ⟨⟨h9, hmt⟩, kt, syt⟩ => ⟨hb.step kt (by decide) syt hmt, by omega, by have := h.remaining_le; omega,
        (kt.gpr (by decide)).trans h8, h9, (kt.gpr (by decide)).trans ((ku.gpr (by decide)).trans h.ebx)⟩
    xrun [(ku.gpr (by decide)).trans h.edi, dec32 (Nat.pos_of_ne_zero hk)]
  · have h3 := of_decide_eq_false h3
    rw [ite_eq_right h3]
    exact WP.block_nil ⟨hb, by omega, h.remaining_le, h8, (ku.gpr (by decide)).trans h.edi,
      (ku.gpr (by decide)).trans h.ebx⟩

theorem cmp0_ok {u : State} {r : Reg} {n : Nat} (hr : u.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    WP isa (.block [.alu .cmp r (.imm 0)]) u fun t =>
      (t.zf = some (decide (n = 0)) ∧ t.gpr r = u.gpr r ∧ t.mem = u.mem) ∧ Keep [r] u t ∧ t.syms = u.syms := by
  refine WP.blockKeep _ ?_ (by cases r <;> rfl)
  xrun [hr]
  exact sub_eq_beq (c := 0) hn (by decide)

theorem used_bound {p : SearchPublic} {o : State} {used : Nat} {x : Spec.RsaKeyGen.Candidate} {rest : List Byte}
    (h : SearchInput p o) (hu : used ≤ p.randLen)
    (hop : candidateOp p.len p.eB (searchP o) ((searchRand o).drop used) = some (x, rest)) :
    ∃ m, m = (p.randLen - used) - rest.length ∧ p.len ≤ m ∧ used + m ≤ p.randLen ∧
      rest = (searchRand o).drop (used + m) := by
  obtain ⟨m, hm, hL, hr⟩ := Search.candidateOp_suffix hop
  have hlen := rand_length h
  rw [List.length_drop, hlen] at hm
  refine ⟨m, ?_, hL, by omega, by rw [hr, List.drop_drop]⟩
  rw [hr, List.length_drop, List.length_drop, hlen]
  omega


/-- A rejected candidate, too close (2) or counted (3), of `m` octets. -/
theorem rejected_ok {p : SearchPublic} {o u : State} {final : PrimeSearchResult} {used k m st : Nat}
    {rest : List Byte} {tr : List Nat}
    (h : SearchLive p o used k u) (h0 : u.gpr .eax = BitVec.ofNat 32 st) (hst : st = 2 ∨ st = 3)
    (hc : u.gpr .ecx = BitVec.ofNat 32 m) (hk : k ≠ 0) (hum : used + m ≤ p.randLen)
    (hrest : rest = (searchRand o).drop (used + m)) (hm : m = (p.randLen - used) - rest.length)
    (htail : tailOf p o used k = if rest.length < ((searchRand o).drop used).length then
      (primeSearch p.len p.eB (searchP o) (if st = 3 then k - 1 else k) rest).consume
        (((searchRand o).drop used).length - rest.length) (entryOf p o used)
      else ⟨.exhausted, 0, entryOf p o used⟩)
    (hfin : final = (tailOf p o used k).consume used tr) (hcs : candStatus p o used = st)
    (hcu : candUsed p o used = m) (hroom : used + p.len ≤ p.randLen) :
    WP isa (.seq (.block [.alu .cmp .eax (.imm 0)]) (.ite .e short reject)) u (StepPost p o final used k tr) := by
  have hlen := rand_length h.input
  have rl := h.input.facts.randLen
  have hlL := h.input.facts.valid
  unfold primeEntropy at rl
  unfold Spec.RsaKeyGen.primeLenValid at hlL
  refine WP.seq (WP.mono (cmp0_ok (n := st) h0 (by omega)) fun u2 ⟨⟨he2, hr2, hm2⟩, k2, sy2⟩ => ?_)
  refine WP.ite _ he2 (fun c => by have := of_decide_eq_true c; omega) (fun _ => ?_)
  have hu2 := h.keep k2 sy2 hm2
  unfold reject
  have hc2 : u2.gpr .ecx = BitVec.ofNat 32 m := (k2.gpr (by decide)).trans hc
  refine WP.seq (WP.mono (cmp0_ok (n := m) hc2 (by omega)) fun u3 ⟨⟨he3, hr3, hm3⟩, k3, sy3⟩ => ?_)
  have hu3 := hu2.keep k3 sy3 hm3
  rw [List.length_drop, hlen] at htail
  refine WP.ite _ he3 (fun z => ?_) (fun z => ?_)
  · have z := of_decide_eq_true z
    have e' : final = ⟨.exhausted, used, tr ++ entryOf p o used⟩ := by
      rw [hfin, htail, ite_eq_right (by omega)]; rfl
    rw [e']
    exact WP.mono (exhausted_ok hu3.toSearchBase hu3.esi hu3.used_le _) fun t ht =>
      done_post (fun hc => hc.2.2.2 (by rw [hcu]; exact z)) ht
  · have z := of_decide_eq_false z
    have hcont : Cont p o used k := ⟨hk, hroom, by rw [hcs]; exact hst, by rw [hcu]; exact z⟩
    refine WP.mono (advance_ok hu3 (hr3.trans hc2) ((k3.gpr (by decide)).trans (hr2.trans h0)) hst hk hum)
      fun t ht => ?_
    unfold StepPost nextK
    rw [ite_eq_left hcont, hcu, hcs]
    refine ⟨ht, ?_⟩
    rw [hfin, htail, ite_eq_left (by omega), Search.consume_consume, ← hm, tailOf, ← hrest]

/-- After a candidate, from `used`, with `k` counted candidates left. -/
theorem classify_ok {p : SearchPublic} {o s : State} {final : PrimeSearchResult} {used k : Nat}
    (h : SearchLive p o used k s) (hp : CandPost p (searchP o) (searchRand o) used s) (hk : k ≠ 0)
    {tr : List Nat} (hfin : final = (tailOf p o used k).consume used tr) (hroom : used + p.len ≤ p.randLen) :
    WP isa Impl.RsaKeyGen.X86.Search.classify s (StepPost p o final used k tr) := by
  have hi := h.input
  have hu := h.used_le
  have hlen := rand_length hi
  have rl := hi.facts.randLen
  unfold primeEntropy at rl
  have hlenL := hi.facts.valid
  unfold Spec.RsaKeyGen.primeLenValid at hlenL
  obtain ⟨h0', hout, hw⟩ := hp
  unfold Impl.RsaKeyGen.X86.Search.classify
  cases hop : candidateOp p.len p.eB (searchP o) ((searchRand o).drop used) with
  | none =>
    simp only [hop] at h0' hout hw
    refine WP.seq (WP.mono (head_ok h hw (st := 0) (by decide) (status_ofNat h0'))
      fun u ⟨⟨hc, ha, he, hm⟩, ku, sy⟩ => ?_)
    have hu' := h.keep ku sy hm
    refine WP.ite _ he (fun c => by cases c) (fun _ => ?_)
    refine WP.seq (WP.mono (cmp0_ok (n := 0) ha (by decide)) fun u2 ⟨⟨he2, _, hm2⟩, k2, sy2⟩ => ?_)
    refine WP.ite _ he2 (fun _ => ?_) (fun c => by cases c)
    have hu2 := hu'.keep k2 sy2 hm2
    have e : final = if primeEntropy p.len ≤ p.randLen - used then
        ⟨.exhausted, used, tr ++ Search.entry p.len p.eB (searchP o) ((searchRand o).drop used)⟩
        else ⟨.entropy k (p.randLen - used), used,
          tr ++ Search.entry p.len p.eB (searchP o) ((searchRand o).drop used)⟩ := by
      rw [hfin, tailOf, Search.search_short hk hop, List.length_drop, hlen]
      split <;> rfl
    rw [e]
    have nc : ¬Cont p o used k := fun hc => by
      have := hc.2.2.1; simp only [candStatus, candOp, hop, Spec.RsaKeyGen.candidateStatus] at this; omega
    exact WP.mono (short_ok hu2.toSearchBase hu2.esi hu2.edi hu hu2.remaining_le (by rw [hm2, hm]; exact hout) _)
      fun t ht => done_post nc ht
  | some pair =>
    obtain ⟨x, rest⟩ := pair
    obtain ⟨m, hm', hLm, hum, hrest⟩ := used_bound hi hu hop
    simp only [hop] at h0' hout hw
    have hn : (p.randLen - used) - rest.length = m := hm'.symm
    rw [hn] at hw
    cases x with
    | prime c =>
      simp only at h0' hout
      refine WP.seq (WP.mono (head_ok h hw (st := 1) (by decide) (status_ofNat h0'))
        fun u ⟨⟨hc, ha, he, hm⟩, ku, sy⟩ => ?_)
      have hu' := h.keep ku sy hm
      refine WP.ite _ he (fun _ => ?_) (fun c => by cases c)
      have e : final = ⟨.accepted c, used + m, tr ++ Search.entry p.len p.eB (searchP o) ((searchRand o).drop used)⟩ := by
        rw [hfin, tailOf, Search.search_prime hk hop, List.length_drop, hlen, ← hn]; rfl
      rw [e]
      have nc : ¬Cont p o used k := fun hc => by
        have := hc.2.2.1; simp only [candStatus, candOp, hop, Spec.RsaKeyGen.candidateStatus] at this; omega
      exact WP.mono (accept_ok hu'.toSearchBase hu'.esi hc hum (by rw [hm]; exact hout) _) fun t ht => done_post nc ht
    | close =>
      refine WP.seq (WP.mono (head_ok h hw (st := 2) (by decide) (status_ofNat h0'))
        fun u ⟨⟨hc, ha, he, hm⟩, ku, sy⟩ => ?_)
      have hu' := h.keep ku sy hm
      refine WP.ite _ he (fun c => by cases c) (fun _ => ?_)
      refine rejected_ok hu' ha (.inl rfl) hc hk hum hrest hm' ?_ hfin ?_ ?_ hroom
      · rw [tailOf, Search.search_close hk hop]; rfl
      · simp only [candStatus, candOp, hop, Spec.RsaKeyGen.candidateStatus]
      · simp only [candUsed, candOp, hop, hn]
    | rejected =>
      refine WP.seq (WP.mono (head_ok h hw (st := 3) (by decide) (status_ofNat h0'))
        fun u ⟨⟨hc, ha, he, hm⟩, ku, sy⟩ => ?_)
      have hu' := h.keep ku sy hm
      refine WP.ite _ he (fun c => by cases c) (fun _ => ?_)
      refine rejected_ok hu' ha (.inr rfl) hc hk hum hrest hm' ?_ hfin ?_ ?_ hroom
      · rw [tailOf, Search.search_rejected hk hop]; rfl
      · simp only [candStatus, candOp, hop, Spec.RsaKeyGen.candidateStatus]
      · simp only [candUsed, candOp, hop, hn]

end VG.Proof.RsaKeyGen.X86.Search
