module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Step
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Entry
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-! # The search's loop (ARMv7)

Each iteration runs the next candidate (unless no counted one is left, or
the tape left cannot hold one) and goes on past it, or ends the search; the
octets consumed grow on every iteration that goes on, so the loop ends.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeRequest PrimeSearchResult candidateOp)

theorem cmp_ok {u : State} {r : Reg} {n c : Nat} (hr : u.gpr r = BitVec.ofNat 32 n) (hn : n < 2 ^ 32)
    (hc : c < 256) :
    WP isa (.block [.cmp r (.imm (BitVec.ofNat 32 c))]) u fun t =>
      (isa.eval .eq t = some (decide (n = c)) ∧ t.mem = u.mem) ∧ Rest [] u t := by
  refine withRest_all [] ?_ (by cases r <;> rfl) (by rfl)
  ffrun [hr, VG.Proof.Ffdh.Arm.encodable_byte (v := BitVec.ofNat 32 c) (by rw [BitVec.toNat_ofNat]; omega)]
  exact congrArg some (sub_eq_beq hn (by omega))

theorem SearchLive.step {p : SearchPublic} {o s t : State} {used k : Nat} (h : SearchLive p o used k s)
    {ws : List Reg} (kt : Rest ws s t) (hws : ∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r11], r ∉ ws := by decide)
    {rs : List Region} (hf : Frame rs s.mem t.mem) (hsub : ∀ r ∈ rs, ∃ q ∈ changes o, Region.Sub r q)
    (happ : ∀ r ∈ rs, Region.Disjoint ⟨State.addr p.S1 + BitVec.ofNat 64 0, 40 - 0⟩ r) :
    SearchLive p o used k t :=
  ⟨h.toSearchBase.step kt (fun r hr => hws r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)) hf hsub happ, h.used_le, h.remaining_le,
    (kt.gpr .r8 (hws _ (by simp))).trans h.r8, (kt.gpr .r9 (hws _ (by simp))).trans h.r9,
    (kt.gpr .r11 (hws _ (by simp))).trans h.r11⟩

/-- The candidate, or the short tape without it. -/
theorem candidateStep_ok (c : Cand) {p : SearchPublic} {o s : State} {final : PrimeSearchResult} {used k : Nat}
    {tr : List Nat} (hl : SearchLive p o used k s) (hfin : final = (tailOf p o used k).consume used tr) (hk : k ≠ 0) :
    WP isa (candidateStep c.call) s (StepPost p o final used k tr) := by
  have hi := hl.input
  have f := hi.facts
  have hv := f.valid
  unfold Spec.RsaKeyGen.primeLenValid at hv
  have rl := f.randLen
  unfold primeEntropy at rl
  have hu := hl.used_le
  have hlen := rand_length hi
  unfold candidateStep
  refine WP.seq (WP.mono (withRest_all (c := .block [arg .r0 0 4, .dp .sub .r0 .r0 (.reg .r8), .cmp .r0 (.reg .r5),
      .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)]) [.r0, .r12]
    (Q := fun t => isa.eval .eq t = some (decide (p.randLen - used < p.len)) ∧ t.mem = s.mem) ?_ (by rfl) (by rfl))
    fun u ⟨⟨he, hm⟩, ku⟩ => ?_)
  · unfold arg
    have c4 : pushBytes + 0 + 4 * 4 < 4096 := by decide
    ffrun [hl.arg_addr 4, hl.arg_read (j := 4) (by decide), hl.arg_value (j := 4) (by decide), randLen_arg hi,
      hl.r8, hl.r5, BitVec.ofNat_sub_ofNat_of_le _ _ (show used < 2 ^ 32 by omega) hu, c4,
      toNat_small (n := p.len) (by omega), toNat_small (n := p.randLen - used) (by omega)]
    exact carry_eval (P := p.randLen - used < p.len) (not_decide_le _ _)
  have hu' := hl.keep ku hm
  refine WP.ite _ he (fun z => ?_) (fun z => ?_)
  · have z := of_decide_eq_true z
    refine WP.seq (WP.mono (zeroOut_ok hu'.toSearchBase) fun t ⟨⟨hz, hf⟩, kt⟩ => ?_)
    have ht := hu'.step kt (by decide) hf (out_changes hi) (out_apart hi)
    have hop : candidateOp p.len p.eB (searchP o) ((searchRand o).drop used) = none :=
      op_short (by rw [List.length_drop, hlen]; exact z)
    have e : final = if primeEntropy p.len ≤ p.randLen - used then ⟨.exhausted, used, tr ++ Search.entry p.len p.eB (searchP o) ((searchRand o).drop used)⟩
        else ⟨.entropy k (primeRequest p.len (p.randLen - used)), used, tr ++ Search.entry p.len p.eB (searchP o) ((searchRand o).drop used)⟩ := by
      rw [hfin, tailOf, Search.search_short hk hop, List.length_drop, hlen]
      split <;> rfl
    rw [e]
    exact WP.mono (short_ok ht.toSearchBase ht.r8 ht.r9 hu ht.remaining_le hz _) fun t ht =>
      done_post (fun hc => by have := hc.2.1; omega) ht
  · have z := of_decide_eq_false z
    exact WP.seq (WP.mono (candidateRun_ok c hu' (by omega)) fun t ⟨ht, hp⟩ => classify_ok ht hp hk hfin (by omega))

theorem status_lt (r : PrimeSearchResult) : r.status < 4 ∧ r.status ≠ 2 := by
  unfold Spec.Entropy.Result.status Spec.Entropy.Outcome.status; split <;> decide

/-- What an iteration leaves. -/
def IterPost (p : SearchPublic) (o : State) (final : PrimeSearchResult) (used k : Nat) (tr : List Nat)
    (t : State) : Prop :=
  if Cont p o used k then
    isa.eval .eq t = some true ∧ SearchLive p o (used + candUsed p o used) (nextK p o used k) t ∧
      final = (tailOf p o (used + candUsed p o used) (nextK p o used k)).consume (used + candUsed p o used)
        (tr ++ entryOf p o used)
  else isa.eval .eq t = some false ∧ SearchDone p o final t

/-- One iteration: the search ends (the status is not 4), or goes on from
later in the tape (it is). -/
theorem iteration_ok (c : Cand) {p : SearchPublic} {o s : State} {final : PrimeSearchResult} {used k : Nat}
    {tr : List Nat} (hl : SearchLive p o used k s) (hfin : final = (tailOf p o used k).consume used tr) :
    WP isa (iteration c.call) s (IterPost p o final used k tr) := by
  have rem := hl.input.remaining_le
  have hk32 : k < 2 ^ 32 := by have := hl.remaining_le; omega
  unfold iteration
  refine WP.seq (WP.mono (cmp0_ok hl.r9 hk32) fun u ⟨⟨he, hm⟩, ku⟩ => ?_)
  have hu := hl.keep ku hm
  refine WP.seq (WP.mono (Q := StepPost p o final used k tr) (WP.ite _ he (fun z => ?_) (fun z => ?_)) fun t ht => ?_)
  · have z := of_decide_eq_true z
    subst z
    have e : final = ⟨.exhausted, used, tr ++ []⟩ := by rw [hfin, tailOf, Search.search_zero]; rfl
    rw [e]
    exact WP.mono (exhausted_ok hu.toSearchBase hu.r8 hu.used_le _) fun t ht =>
      done_post (fun hc => hc.1 rfl) ht
  · exact candidateStep_ok c hu hfin (of_decide_eq_false z)
  unfold StepPost at ht
  unfold IterPost
  split at ht
  · rename_i hc
    simp only [hc, ↓reduceIte]
    refine WP.mono (cmp_ok (c := 4) (n := 4) ht.1.r11 (by decide) (by decide)) fun t ⟨⟨et, hmt⟩, kt⟩ =>
      ⟨et, ht.1.keep kt hmt, ht.2⟩
  · rename_i hc
    simp only [hc, ↓reduceIte]
    have st := status_lt final
    refine WP.mono (cmp_ok (c := 4) ht.r11 (by omega) (by decide)) fun t ⟨⟨et, hmt⟩, kt⟩ => ⟨?_, ?_⟩
    · change isa.eval .eq t = some false
      rw [et, decide_eq_false (by omega)]
    · exact ⟨ht.toSearchBase.keep kt hmt, (kt.gpr .r8 (by decide)).trans ht.r8,
        (kt.gpr .r9 (by decide)).trans ht.r9, (kt.gpr .r10 (by decide)).trans ht.r10,
        (kt.gpr .r11 (by decide)).trans ht.r11, by rw [hmt]; exact ht.output, ht.bounds⟩

theorem candUsed_le {p : SearchPublic} {o : State} {used : Nat} (h : SearchInput p o) (hu : used ≤ p.randLen) :
    used + candUsed p o used ≤ p.randLen := by
  unfold candUsed
  split
  · rename_i x rest hop
    obtain ⟨m, hm, -, hum, -⟩ := used_bound h hu hop
    omega
  · omega

theorem search_loop (c : Cand) {p : SearchPublic} {o s : State} {final : PrimeSearchResult} {used k : Nat}
    {tr : List Nat} (hl : SearchLive p o used k s) (hfin : final = (tailOf p o used k).consume used tr) :
    WP isa (.loop (iteration c.call) .eq) s (SearchDone p o final) := by
  refine WP.loop (fun m t => ∃ u k' tr', m = p.randLen - u ∧ u ≤ p.randLen ∧ SearchLive p o u k' t ∧
      final = (tailOf p o u k').consume u tr')
    (fun m t ⟨u, k', tr', hm, hle, ht, hf⟩ => WP.mono (iteration_ok c ht hf) fun t' ht' => ?_) _ s
    ⟨used, k, tr, rfl, hl.used_le, hl, hfin⟩
  unfold IterPost at ht'
  split at ht'
  · rename_i hc
    have hb := candUsed_le hl.input hle
    exact .inr ⟨ht'.1, _, by have := hc.2.2.2; omega, _, _, _, rfl, hb, ht'.2.1, ht'.2.2⟩
  · exact .inl ht'

end VG.Proof.RsaKeyGen.Arm.Search
