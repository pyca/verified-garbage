module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Step
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaKeyGen.X86.Search.Step
meta import VerifiedGarbage.Proof.Framework.Offset

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
      BitVec.ofNat_sub_ofNat_of_le _ _ (show used < 2 ^ 32 by omega) hu,
      toNat_small' (n := p.len) (by omega), toNat_small' (n := p.randLen - used) (by omega)]
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
      done_post (fun hc => by have := hc.2.1; omega) ht
  · have z := of_decide_eq_false z
    exact WP.seq (WP.mono (candidateRun_ok c hu' (by omega)) fun t ⟨ht, hp⟩ => classify_ok ht hp hk hfin (by omega))

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
  have hk32 : k < 2 ^ 32 := by have := hl.remaining_le; omega
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
    refine WP.mono (cmp_ok (c := 4) ht.ebx (by omega) (by decide)) fun t ⟨⟨et, hr, hmt⟩, kt, syt⟩ => ⟨?_, ?_⟩
    · change t.zf = some false
      rw [et, decide_eq_false (by omega)]
    · exact ⟨ht.toSearchBase.step kt (by decide) syt hmt, (kt.gpr (by decide)).trans ht.esi,
        (kt.gpr (by decide)).trans ht.edi, (kt.gpr (by decide)).trans ht.ebp,
        hr.trans ht.ebx, by rw [hmt]; exact ht.output, ht.bounds⟩

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
    WP isa (.loop (iteration c.call) .e) s (SearchDone p o final) := by
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

end VG.Proof.RsaKeyGen.X86.Search
