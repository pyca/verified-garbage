module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Search.Step
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # The search's loop: an iteration, and the loop to its end -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.Search

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Impl.RsaKeyGen.X86_64.Search
open VG.Spec.RsaKeyGen (primeSearch PrimeSearchResult)

/-- The candidate's status, zero-extended, compared with 1. -/
theorem classify_head (s : State) {st : Nat} (hst : ((s.gpr .rax).setWidth 32).toNat = st) (h4 : st < 4) :
    WP isa (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 1)]) s fun t =>
      (t.gpr .rax = BitVec.ofNat 64 st ∧ eval .e t = some (decide (st = 1)) ∧ t.mem = s.mem) ∧
        Keep [.rax] s t := by
  have hr : (s.gpr .rax).setWidth 32 = BitVec.ofNat 32 st := by
    apply BitVec.eq_of_toNat_eq; rw [hst, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hz : ((BitVec.ofNat 32 st).setWidth 64 - BitVec.signExtend 64 (1 : BitVec 32) == 0) = decide (st = 1) := by
    rcases (show st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 by omega) with rfl | rfl | rfl | rfl <;> decide
  have he : (BitVec.ofNat 32 st).setWidth 64 = BitVec.ofNat 64 st := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine WP.keep [.rax] ?_ rfl
  xrun [eval, hr, hz]
  refine ⟨he, ?_⟩
  rcases (show st = 0 ∨ st = 1 ∨ st = 2 ∨ st = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

theorem test_rax (s : State) {st : Nat} (hra : s.gpr .rax = BitVec.ofNat 64 st) (h4 : st < 4) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t =>
      (t.gpr .rax = s.gpr .rax ∧ eval .e t = some (decide (st = 0)) ∧ t.mem = s.mem) ∧ Keep [.rax] s t := by
  have hz : (BitVec.ofNat 64 st == 0) = decide (st = 0) := ofNat64_beq_zero (by omega)
  refine WP.keep [.rax] ?_ rfl
  xrun [eval, hra, BitVec.and_self, hz]

theorem SearchIter.keep {p : SearchPublic} {original s t : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s) {rs : List Reg}
    (k : Keep rs s t) (hm : t.mem = s.mem) (hregs : ∀ reg ∈ calleeSaved, reg ∉ rs) :
    SearchIter p original final used remaining t := ⟨h.1.keep k hm hregs, h.2⟩

theorem search_classify {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s)
    (hc : CandPost p (searchP original) (searchRand original) used s) (hr : remaining ≠ 0) :
    WP isa classify s (IterPost p original final used remaining) := by
  have hst := hc.1
  have h4 : Spec.RsaKeyGen.candidateStatus
      (Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used)) < 4 := by
    unfold Spec.RsaKeyGen.candidateStatus; split <;> decide
  unfold classify
  refine WP.seq (WP.mono (classify_head s hst h4) fun u ⟨⟨hra, he1, hmu⟩, ku⟩ => ?_)
  have hu := h.keep ku hmu (by decide)
  have hlow : (u.gpr .rax).setWidth 32 = (s.gpr .rax).setWidth 32 := by
    rw [hra]; apply BitVec.eq_of_toNat_eq
    have hst' : (s.gpr .rax).toNat % 2 ^ 32 = Spec.RsaKeyGen.candidateStatus
        (Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used)) := by
      rw [← BitVec.toNat_setWidth]; exact hst
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hst', Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hcu := hc.keep hmu hlow
  refine WP.ite _ he1 (fun h1 => ?_) (fun h1 => ?_)
  · have h1 := of_decide_eq_true h1
    cases hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) with
    | none => rw [hres] at h1; cases h1
    | some pr =>
      obtain ⟨x, rest⟩ := pr
      cases x with
      | prime c =>
        exact WP.mono (search_accept hu hcu hr hres) fun t hd =>
          .inr ⟨hd.status_ne, fun ⟨_, hs, _⟩ => by simp [candStatus, hres, Spec.RsaKeyGen.candidateStatus] at hs, hd⟩
      | close => rw [hres] at h1; cases h1
      | rejected => rw [hres] at h1; cases h1
  · refine WP.seq (WP.mono (test_rax u hra h4) fun v ⟨⟨hrv, he0, hmv⟩, kv⟩ => ?_)
    have hv := hu.keep kv hmv (by decide)
    have hcv := hcu.keep hmv (by rw [hrv])
    refine WP.ite _ he0 (fun h0 => ?_) (fun h0 => ?_)
    · have h0 := of_decide_eq_true h0
      cases hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) with
      | none =>
        refine WP.mono (search_short hv hcv hr hres) fun t hd => .inr ⟨hd.status_ne, fun ⟨_, hs, _⟩ => ?_, hd⟩
        simp [candStatus, hres, Spec.RsaKeyGen.candidateStatus] at hs
      | some pr =>
        obtain ⟨x, rest⟩ := pr
        cases x <;> (rw [hres] at h0; cases h0)
    · have h0 := of_decide_eq_false h0
      have h1 := of_decide_eq_false h1
      cases hres : Spec.RsaKeyGen.candidateOp p.len p.eB (searchP original) ((searchRand original).drop used) with
      | none => rw [hres] at h0; exact absurd rfl h0
      | some pr =>
        obtain ⟨x, rest⟩ := pr
        cases x with
        | prime c => rw [hres] at h1; exact absurd rfl h1
        | close =>
          refine search_reject hv hcv hr hres (.inl rfl) ?_
          rw [hrv, hra, hres]; rfl
        | rejected =>
          refine search_reject hv hcv hr hres (.inr rfl) ?_
          rw [hrv, hra, hres]; rfl

/-! ## An iteration -/

/-- What an iteration leaves, with the loop's condition. -/
def LoopStep (p : SearchPublic) (original : State) (final : PrimeSearchResult) (used remaining : Nat)
    (t : State) : Prop :=
  (eval .e t = some true ∧ ContinuePost p original final used remaining t) ∨
    (eval .e t = some false ∧ ¬Continues p original used remaining ∧ SearchDone p original final t)

theorem iter_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (.block [.mov .rax (.mem (field 0)), .alu .test .rax (.reg .rax)]) s fun t =>
      (eval .e t = some (decide (remaining = 0)) ∧ t.mem = s.mem) ∧ Keep [.rax] s t := by
  obtain ⟨hl, -, -⟩ := h.frame_in (t := s) rfl
  have hl0 : InRegions (s.rd ++ s.wr) p.F 8 := by simpa only [BitVec.add_zero] using hl 0 (by decide)
  have h0 := h.slot (j := 0) (v := BitVec.ofNat 64 remaining) (by simp [SearchPublic.headers])
  simp only [Bignum.word, off, Nat.reduceMul, BitVec.add_zero] at h0
  have hz : (BitVec.ofNat 64 remaining == 0) = decide (remaining = 0) :=
    ofNat64_beq_zero (Nat.lt_of_le_of_lt h.remaining_le (by rw [← h.input.2]; exact BitVec.isLt _))
  refine WP.keep [.rax] ?_ rfl
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, BitVec.add_zero, eval,
    h.r12, hl0, h0, BitVec.and_self, hz]

theorem iter_test {p : SearchPublic} {original s : State} {final : PrimeSearchResult} {used : Nat}
    {remaining : Nat} (h : IterPost p original final used remaining s) :
    WP isa (.block [.mov .rax (.mem (field 17)), .alu .cmp .rax (.imm 4)]) s (LoopStep p original final used remaining) := by
  have hregs : s.gpr .r12 = p.F ∧ ∃ o : State, SearchInput p o ∧ s.wr = p.frame :: o.wr := by
    rcases h with ⟨-, -, _, _, -, ⟨hi, -⟩, -⟩ | ⟨-, -, hd⟩
    · exact ⟨hi.r12, _, hi.input, hi.wr⟩
    · exact ⟨hd.r12, _, hd.input, hd.wr⟩
  obtain ⟨hr12, o, hi, hw⟩ := hregs
  have scr := hi.frame_scr hw
  have hl : InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 136) 8 :=
    let ⟨r, hr, hc⟩ := scr.st (d := 136) (by decide); ⟨r, List.mem_append_right _ hr, hc⟩
  have h4 : BitVec.signExtend 64 (4 : BitVec 32) = (4 : BitVec 64) := by decide
  refine WP.mono (WP.keep [.rax] (Q := fun t => eval .e t = some (word s.mem p.F (8 * 17) - 4 == 0) ∧
    t.mem = s.mem) (by
      xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, eval, hr12, hl, h4]) rfl) fun t ⟨⟨he, hm⟩, k⟩ => ?_
  rw [sub_beq_zero] at he
  rcases h with ⟨h17, hc⟩ | ⟨h17, hn, hd⟩
  · exact .inl ⟨by rw [he, h17]; rfl, hc.keep k hm (by decide)⟩
  · refine .inr ⟨by rw [he]; simp only [beq_eq_false_iff_ne.mpr h17], hn, ?_⟩
    exact ⟨hd.input, k.2.1.trans hd.rd, k.2.2.trans hd.wr, (k.gpr (by decide)).trans hd.rsp,
      (k.gpr (by decide)).trans hd.r12, fun r hr hn hs => (k.gpr (by cases r <;> simp_all [calleeSaved])).trans
        (hd.saved r hr hn hs), by rw [hm]; exact hd.savedR12, by rw [hm]; exact hd.usedPtr,
      by rw [hm]; exact hd.stp, by rw [hm]; exact hd.len, by rw [hm]; exact hd.cap, by rw [hm]; exact hd.remaining,
      by rw [hm]; exact hd.request, by rw [hm]; exact hd.used, by rw [hm]; exact hd.status,
      by rw [hm]; exact hd.output⟩

theorem search_iteration (v : RoundImpl) {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s) :
    WP isa (iteration (candidateCall v)) s (LoopStep p original final used remaining) := by
  unfold iteration
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (iter_guard h.1) fun u ⟨⟨he, hmu⟩, ku⟩ => ?_)
  have hu := h.keep ku hmu (by decide)
  refine WP.seq (WP.ite _ he (fun hz => ?_) (fun hz => ?_))
  · have hz := of_decide_eq_true hz
    subst hz
    obtain ⟨hl, tr, hfinal⟩ := hu
    unfold tailOf at hfinal
    rw [VG.Proof.RsaKeyGen.Search.search_zero] at hfinal
    exact WP.mono (search_exhausted hl (result := final) (by rw [hfinal]; rfl)) fun t hd =>
      iter_test (.inr ⟨hd.status_ne, fun ⟨h, _⟩ => h rfl, hd⟩)
  · have hz := of_decide_eq_false hz
    refine WP.seq (WP.mono (search_candidate_run v hu.1) fun t ⟨ht, hc⟩ => ?_)
    exact WP.mono (search_classify ⟨ht, hu.2⟩ hc hz) fun _ hp => iter_test hp

theorem search_loop (v : RoundImpl) {p : SearchPublic} {original s : State} {final : PrimeSearchResult}
    {used remaining : Nat} (h : SearchIter p original final used remaining s) :
    WP isa (.loop (iteration (candidateCall v)) .e) s (SearchDone p original final) := by
  refine WP.loop (M := isa)
    (fun n t => ∃ u k, n = p.randLen - u + 1 ∧ SearchIter p original final u k t) ?_
    (p.randLen - used + 1) s ⟨used, remaining, rfl, h⟩
  rintro n t ⟨u, k, rfl, ht⟩
  refine WP.mono (search_iteration v ht) fun t' hs => ?_
  rcases hs with ⟨he, -, u', k', hlt, ht', -⟩ | ⟨he, -, hd⟩
  · have hle := ht'.1.used_le
    exact .inr ⟨he, _, by omega, u', k', rfl, ht'⟩
  · exact .inl ⟨he, hd⟩

end VG.Proof.RsaKeyGen.X86_64.Search
