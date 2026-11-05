module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Ends
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-! # One candidate of the search (ARMv7)

`classify`, after a candidate: the search ends (`SearchDone`), or goes on
past a rejected candidate from a later offset (`SearchIter`), as
`VG.Spec.RsaKeyGen.primeSearch` does (`Proof/RsaKeyGen/SearchSpec.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeRequest PrimeSearchResult candidateOp)

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

theorem status_ofNat {t : State} {n : Nat} (h : (t.gpr .r0).toNat = n) :
    t.gpr .r0 = BitVec.ofNat 32 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The octets a candidate consumed, the low half of `used`. -/
theorem used_low {s : State} {p : SearchPublic} {n : Nat}
    (hw : Spec.Rsa.wordsAt s.mem (State.addr p.up) 1 = [BitVec.ofNat 64 n]) :
    s.mem.readW (State.addr p.up) 32 = BitVec.ofNat 32 n := by
  have e : s.mem.readW (State.addr p.up) 64 = BitVec.ofNat 64 n := by
    have := congrArg List.head? hw
    simpa [Spec.Rsa.wordsAt] using this
  exact low_half e

/-- The candidate's head: the octets it consumed into `r12`, and its
status compared with 1. -/
theorem head_ok {p : SearchPublic} {o s : State} {used remaining : Nat}
    (h : SearchLive p o used remaining s) {n st : Nat} (hw : Spec.Rsa.wordsAt s.mem (State.addr p.up) 1 = [BitVec.ofNat 64 n])
    (hst : st < 4) (h0 : s.gpr .r0 = BitVec.ofNat 32 st) :
    WP isa (.block [.ldr .r12 .r6 0, .cmp .r0 (.imm 1)]) s fun t =>
      (t.gpr .r12 = BitVec.ofNat 32 n ∧ isa.eval .eq t = some (decide (st = 1)) ∧ t.mem = s.mem) ∧
        Rest [.r12] s t := by
  have hi := h.input
  have f := hi.facts
  refine withRest_all [.r12] ?_ (by rfl) (by rfl)
  have a : State.addr (s.gpr .r6 + BitVec.ofNat 32 0) = State.addr p.up := by rw [h.r6, BitVec.add_zero]
  have r : InRegions (s.rd ++ s.wr) (State.addr p.up) 4 := by
    refine ⟨rU p, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, hi.wr, ← hi.regions.2.1]; simp [inWrites]
    · simpa using Offset.contains_base (State.addr p.up) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  ffrun [a, r, used_low hw, h0]
  change some (BitVec.ofNat 32 st - 1 == 0) = _
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_eq_beq (by omega) (by omega)]

theorem dec32 {k : Nat} (h1 : 1 ≤ k) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h1]

/-- After a rejected candidate of `n > 0` octets: its octets consumed, one
counted candidate fewer if counted (status 3). -/
theorem advance_ok {p : SearchPublic} {o s : State} {used k n st : Nat} (h : SearchLive p o used k s)
    (h12 : s.gpr .r12 = BitVec.ofNat 32 n) (h0 : s.gpr .r0 = BitVec.ofNat 32 st) (hst : st = 2 ∨ st = 3)
    (hk : k ≠ 0) (hu : used + n ≤ p.randLen) :
    WP isa (.seq (.block [.dp .add .r8 .r8 (.reg .r12), .cmp .r0 (.imm 3)])
      (.ite .eq (.block [.dp .sub .r9 .r9 (.imm 1)]) (.block []))) s
      (SearchLive p o (used + n) (if st = 3 then k - 1 else k)) := by
  have rem := h.input.facts.remaining
  have hrl : k < 2 ^ 32 := by
    have := h.remaining_le; have := h.input.remaining_le; omega
  refine WP.seq (WP.mono (withRest_all (c := .block [.dp .add .r8 .r8 (.reg .r12), .cmp .r0 (.imm 3)]) [.r8]
    (Q := fun t => t.gpr .r8 = BitVec.ofNat 32 (used + n) ∧ isa.eval .eq t = some (decide (st = 3)) ∧
      t.mem = s.mem) ?_ (by rfl) (by rfl)) fun u ⟨⟨h8, he, hm⟩, ku⟩ => ?_)
  · ffrun [h.r8, h12, h0, add_ofNat32]
    change some (BitVec.ofNat 32 st - 3 == 0) = _
    rw [show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, sub_eq_beq (by omega) (by omega)]
  have hb := h.toSearchBase.keep ku hm
  refine WP.ite _ he (fun h3 => ?_) (fun h3 => ?_)
  · have h3 := of_decide_eq_true h3
    rw [ite_eq_left h3]
    refine WP.mono (withRest_all (c := .block [.dp .sub .r9 .r9 (.imm 1)]) [.r9]
      (Q := fun t => t.gpr .r9 = BitVec.ofNat 32 (k - 1) ∧ t.mem = u.mem) ?_ (by rfl) (by rfl))
      fun t ⟨⟨h9, hmt⟩, kt⟩ => ⟨hb.keep kt hmt, by omega, by have := h.remaining_le; omega,
        (kt.gpr .r8 (by decide)).trans h8, h9, (kt.gpr .r11 (by decide)).trans ((ku.gpr .r11 (by decide)).trans h.r11)⟩
    ffrun [(ku.gpr .r9 (by decide)).trans h.r9, dec32 (Nat.pos_of_ne_zero hk)]
  · have h3 := of_decide_eq_false h3
    rw [ite_eq_right h3]
    exact WP.block_nil ⟨hb, by omega, h.remaining_le, h8, (ku.gpr .r9 (by decide)).trans h.r9,
      (ku.gpr .r11 (by decide)).trans h.r11⟩

theorem SearchLive.keep {p : SearchPublic} {o s t : State} {used k : Nat} (h : SearchLive p o used k s)
    {ws : List Reg} (kt : Rest ws s t) (hm : t.mem = s.mem)
    (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r11], r ∉ ws := by decide) : SearchLive p o used k t :=
  ⟨h.toSearchBase.keep kt hm (fun r hr => hws r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)), h.used_le, h.remaining_le,
    (kt.gpr .r8 (hws _ (by simp))).trans h.r8, (kt.gpr .r9 (hws _ (by simp))).trans h.r9,
    (kt.gpr .r11 (hws _ (by simp))).trans h.r11⟩

theorem cmp0_ok {u : State} {r : Reg} {n : Nat} (hr : u.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) :
    WP isa (.block [.cmp r (.imm 0)]) u fun t =>
      (isa.eval .eq t = some (decide (n = 0)) ∧ t.mem = u.mem) ∧ Rest [] u t := by
  refine withRest_all [] ?_ (by cases r <;> rfl) (by rfl)
  ffrun [hr]
  exact congrArg some (sub_eq_beq (c := 0) hn (by decide))

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
    (h : SearchLive p o used k u) (h0 : u.gpr .r0 = BitVec.ofNat 32 st) (hst : st = 2 ∨ st = 3)
    (h12 : u.gpr .r12 = BitVec.ofNat 32 m) (hk : k ≠ 0) (hum : used + m ≤ p.randLen)
    (hrest : rest = (searchRand o).drop (used + m)) (hm : m = (p.randLen - used) - rest.length)
    (htail : tailOf p o used k = if rest.length < ((searchRand o).drop used).length then
      (primeSearch p.len p.eB (searchP o) (if st = 3 then k - 1 else k) rest).consume
        (((searchRand o).drop used).length - rest.length) (entryOf p o used)
      else ⟨.exhausted, 0, entryOf p o used⟩)
    (hfin : final = (tailOf p o used k).consume used tr) (hcs : candStatus p o used = st)
    (hcu : candUsed p o used = m) (hroom : used + p.len ≤ p.randLen) :
    WP isa (.seq (.block [.cmp .r0 (.imm 0)]) (.ite .eq short reject)) u (StepPost p o final used k tr) := by
  have hlen := rand_length h.input
  have rl := h.input.facts.randLen
  have hlL := h.input.facts.valid
  unfold primeEntropy at rl
  unfold Spec.RsaKeyGen.primeLenValid at hlL
  refine WP.seq (WP.mono (cmp0_ok (n := st) h0 (by omega)) fun u2 ⟨⟨he2, hm2⟩, k2⟩ => ?_)
  refine WP.ite _ he2 (fun c => by have := of_decide_eq_true c; omega) (fun _ => ?_)
  have hu2 := h.keep k2 hm2
  unfold reject
  refine WP.seq (WP.mono (cmp0_ok (n := m) ((k2.gpr .r12 (by decide)).trans h12) (by omega))
    fun u3 ⟨⟨he3, hm3⟩, k3⟩ => ?_)
  have hu3 := hu2.keep k3 hm3
  rw [List.length_drop, hlen] at htail
  refine WP.ite _ he3 (fun z => ?_) (fun z => ?_)
  · have z := of_decide_eq_true z
    have e' : final = ⟨.exhausted, used, tr ++ entryOf p o used⟩ := by
      rw [hfin, htail, ite_eq_right (by omega)]; rfl
    rw [e']
    exact WP.mono (exhausted_ok hu3.toSearchBase hu3.r8 hu3.used_le _) fun t ht =>
      done_post (fun hc => hc.2.2.2 (by rw [hcu]; exact z)) ht
  · have z := of_decide_eq_false z
    have hc : Cont p o used k := ⟨hk, hroom, by rw [hcs]; exact hst, by rw [hcu]; exact z⟩
    refine WP.mono (advance_ok hu3 ((k3.gpr .r12 (by decide)).trans ((k2.gpr .r12 (by decide)).trans h12))
      ((k3.gpr .r0 (by decide)).trans ((k2.gpr .r0 (by decide)).trans h0)) hst hk hum) fun t ht => ?_
    unfold StepPost nextK
    rw [ite_eq_left hc, hcu, hcs]
    refine ⟨ht, ?_⟩
    rw [hfin, htail, ite_eq_left (by omega), Search.consume_consume, ← hm, tailOf, ← hrest]

/-- After a candidate, from `used`, with `k` counted candidates left. -/
theorem classify_ok {p : SearchPublic} {o s : State} {final : PrimeSearchResult} {used k : Nat}
    (h : SearchLive p o used k s) (hp : CandPost p (searchP o) (searchRand o) used s) (hk : k ≠ 0)
    {tr : List Nat} (hfin : final = (tailOf p o used k).consume used tr) (hroom : used + p.len ≤ p.randLen) :
    WP isa Impl.RsaKeyGen.Arm.Search.classify s (StepPost p o final used k tr) := by
  have hi := h.input
  have hu := h.used_le
  have hlen := rand_length hi
  have rl := hi.facts.randLen
  unfold primeEntropy at rl
  have hlenL := hi.facts.valid
  unfold Spec.RsaKeyGen.primeLenValid at hlenL
  obtain ⟨h0', hout, hw⟩ := hp
  unfold Impl.RsaKeyGen.Arm.Search.classify
  cases hop : candidateOp p.len p.eB (searchP o) ((searchRand o).drop used) with
  | none =>
    simp only [hop] at h0' hout hw
    refine WP.seq (WP.mono (head_ok h hw (st := 0) (by decide) (status_ofNat h0')) fun u ⟨⟨h12, he, hm⟩, ku⟩ => ?_)
    have hu' := h.keep ku hm
    refine WP.ite _ he (fun c => by cases c) (fun _ => ?_)
    refine WP.seq (WP.mono (cmp0_ok (n := 0) ((ku.gpr .r0 (by decide)).trans (status_ofNat h0')) (by decide))
      fun u2 ⟨⟨he2, hm2⟩, k2⟩ => ?_)
    refine WP.ite _ he2 (fun _ => ?_) (fun c => by cases c)
    have hu2 := hu'.keep k2 hm2
    have e : final = if primeEntropy p.len ≤ p.randLen - used then ⟨.exhausted, used, tr ++ Search.entry p.len p.eB (searchP o) ((searchRand o).drop used)⟩
        else ⟨.entropy k (primeRequest p.len (p.randLen - used)), used, tr ++ Search.entry p.len p.eB (searchP o) ((searchRand o).drop used)⟩ := by
      rw [hfin, tailOf, Search.search_short hk hop, List.length_drop, hlen]
      split <;> rfl
    rw [e]
    have nc : ¬Cont p o used k := fun hc => by
      have := hc.2.2.1; simp only [candStatus, candOp, hop, Spec.RsaKeyGen.candidateStatus] at this; omega
    exact WP.mono (short_ok hu2.toSearchBase hu2.r8 hu2.r9 hu hu2.remaining_le (by rw [hm2, hm]; exact hout) _)
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
      refine WP.seq (WP.mono (head_ok h hw (st := 1) (by decide) (status_ofNat h0')) fun u ⟨⟨h12, he, hm⟩, ku⟩ => ?_)
      have hu' := h.keep ku hm
      refine WP.ite _ he (fun _ => ?_) (fun c => by cases c)
      have e : final = ⟨.accepted c, used + m, tr ++ Search.entry p.len p.eB (searchP o) ((searchRand o).drop used)⟩ := by
        rw [hfin, tailOf, Search.search_prime hk hop, List.length_drop, hlen, ← hn]; rfl
      rw [e]
      have nc : ¬Cont p o used k := fun hc => by
        have := hc.2.2.1; simp only [candStatus, candOp, hop, Spec.RsaKeyGen.candidateStatus] at this; omega
      exact WP.mono (accept_ok hu'.toSearchBase hu'.r8 h12 hum (by rw [hm]; exact hout) _) fun t ht => done_post nc ht
    | close =>
      refine WP.seq (WP.mono (head_ok h hw (st := 2) (by decide) (status_ofNat h0')) fun u ⟨⟨h12, he, hm⟩, ku⟩ => ?_)
      have hu' := h.keep ku hm
      refine WP.ite _ he (fun c => by cases c) (fun _ => ?_)
      refine rejected_ok hu' ((ku.gpr .r0 (by decide)).trans (status_ofNat h0')) (.inl rfl) h12 hk hum hrest hm'
        ?_ hfin ?_ ?_ ?_
      · rw [tailOf, Search.search_close hk hop]; rfl
      · simp only [candStatus, candOp, hop, Spec.RsaKeyGen.candidateStatus]
      · simp only [candUsed, candOp, hop, hn]
      · exact hroom
    | rejected =>
      refine WP.seq (WP.mono (head_ok h hw (st := 3) (by decide) (status_ofNat h0')) fun u ⟨⟨h12, he, hm⟩, ku⟩ => ?_)
      have hu' := h.keep ku hm
      refine WP.ite _ he (fun c => by cases c) (fun _ => ?_)
      refine rejected_ok hu' ((ku.gpr .r0 (by decide)).trans (status_ofNat h0')) (.inr rfl) h12 hk hum hrest hm'
        ?_ hfin ?_ ?_ ?_
      · rw [tailOf, Search.search_rejected hk hop]; rfl
      · simp only [candStatus, candOp, hop, Spec.RsaKeyGen.candidateStatus]
      · simp only [candUsed, candOp, hop, hn]
      · exact hroom

end VG.Proof.RsaKeyGen.Arm.Search
