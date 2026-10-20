module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMrRound
public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.SharedCandidate
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedMid
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel

/-! # Constant time of RSA's witness policy with the callable shared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64

private theorem hp_shared_used {p : MrPub} {i u u' : Nat} {s t : State} {sp : Addr} {mi : BitVec 64} {rs : List (Nat × Nat)}
    (h : HP p.B p.wr (p.vs i u) s) (hg : Good t p.B p.Z p.w mi) (hw : t.wr = s.wr)
    (hZ : slot p.w 28 ≤ p.Z) (henv : SharedEnv p.B p.Z sp s) (hf : SharedFrame p.B sp rs s.mem t.mem)
    (hd : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], ∀ r ∈ rs, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k)
    (hu : word t.mem p.B (8 * kUsed) = BitVec.ofNat 64 u') : HP p.B p.wr (p.vs i u') t := by
  have hm := (hp0 h).mrh
  have e : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI], word t.mem p.B (8 * k) = word s.mem p.B (8 * k) :=
    fun k hk => SharedFrame.word hf henv (hd k hk) (by
      have hk32 : k < 32 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have := hdr_lt_slot p.w 28 hk32
      omega_arith) hg.scr.nowrap
  have := mr_hp (ex := []) hg (hw.trans h.wr) ⟨(e _ (by simp)).trans hm.out, (e _ (by simp)).trans hm.len,
    (e _ (by simp)).trans hm.usedP, (e _ (by simp)).trans hm.rand, (e _ (by simp)).trans hm.rlen,
    (e _ (by simp)).trans hm.chk, (e _ (by simp)).trans hm.ki, hu⟩ (by simp)
  rwa [List.append_nil] at this

def SharedR0 (q : RPub × Addr) (s : State) : Prop :=
  R0 q.1 s ∧ slot q.1.p.w 28 ≤ q.1.p.Z ∧ SharedEnv q.1.p.B q.1.p.Z q.2 s

private def roundPublic (q : RPub × Addr) : Caller.Public :=
  ⟨⟨q.1.p.B, q.1.p.Z, q.1.p.w⟩, q.2⟩

private def RoundReady (q : RPub × Addr) (s : State) : Prop := Caller.Before (roundPublic q) s

private theorem witness_run (M : Mont) {q : RPub × Addr} {s : State} (h : SharedR0 q s) :
    ∃ t s', Exec isa (seqs (mrWitness ++ [M.mm aXm aX aR2])) s t s' := by
  obtain ⟨⟨hk, hp, hd, mi, c, bm, r, uni, hc, he, hR2, hc1, hsh, hsrc, _, hlen, _⟩, hz, henv⟩ := h
  have hm := (hp0 hp).mrh
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by have := hd.w4; omega_arith) hsh
  obtain ⟨t, s', he, -⟩ := sharedWitness_ok M hd hc hR2 hsh.1 hc1 hb hm.rand hm.used hm.len hsrc hlen
  exact ⟨t, s', he⟩

private theorem prefix_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) : RelCT isa (Two SharedR0)
    (seqs (mrWitness ++ [mm aXm aX aR2])) (Two RoundReady) := by
  refine two_post ?_ ?_
  · have ht : RelCT isa (Two R0) (seqs (mrWitness ++ [M.mm aXm aX aR2])) (fun _ _ => True) := by
      refine RelCT.seqs_app (by simp [mrWitness]) (by simp) (RelCT.seq mrWitness_ct ?_)
      simp only [seqs]
      exact two_map (fun q : RPub => (⟨q.p.B, q.p.Z, q.p.w⟩ : Ws))
        (fun _ _ h => let ⟨_, hd, mi, _, _, hc, _⟩ := h; ⟨mi, hc.good, hd.z⟩)
        (M.ct (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))))
    refine RelCT.of_inline (witness_inlineOk hmc.ok) ?_ ?_ ?_ ?_
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      rw [hmc.witness]
      exact ⟨witness_run M h₁, witness_run M h₂⟩
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      exact ⟨h₁.2.2.hole_clear, h₂.2.2.hole_clear⟩
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      exact h₁.2.2.rsp.trans h₂.2.2.rsp.symm
    · rw [hmc.witness]
      exact ht.mono (fun _ _ ⟨q, hs, ht⟩ => ⟨q.1, hs.1, ht.1⟩) (fun _ _ _ => trivial)
  · rintro q s ⟨⟨hk, hp, hd, mi, c, bm, r, uni, hc, he, hR2, hc1, hsh, hsrc, _, hlen, _⟩, hz, henv⟩
    have hm := (hp0 hp).mrh
    have hnw := hc.good.scr.nowrap
    obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by have := hd.w4; omega_arith) hsh
    refine WP.mono (sharedWitness_call_ok M hmc henv hd hc hR2 hsh.1 hc1 hb hm.rand hm.used hm.len hsrc hlen) ?_
    rintro t ⟨hct, hx, hr2, hu, hus, hf, ht⟩
    have hex : ∀ r ∈ witnessRanges q.1.p.w, slot q.1.p.w aE + 8 * (q.1.p.w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot q.1.p.w aE := by
      intro r hr
      refine Or.inr ?_
      simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | (rfl | rfl | rfl)
      all_goals simp only [slot, hdrBytes, aX, aAcc, aTmp, aXm, aE, kUsed, kU, sFn]; omega_arith
    have het : ECtx t.mem q.1.p.B q.1.p.w c :=
      ⟨by rw [SharedFrame.array hf henv (fun r hr => by have := hex r hr; omega_arith) (by have := aE_fits hd; omega_arith) hnw]; exact he.e,
        by rw [SharedFrame.word hf henv (fun r hr => by have := hex r hr; omega_arith) (by have := aE_fits hd; omega_arith) hnw]; exact he.l⟩
    exact ⟨mi, c, bm, (wtOf c q.1.p.w q.1.u r).1, hct, het, hd, hz,
      (henv.kept ht (by decide)).room, (henv.kept ht (by decide)).rsp, hsh.1, by have := hsh.1; omega_arith, hx⟩

private theorem mid_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) : RelCT isa (Two SharedR0)
    (seqs ((mrWitness ++ [mm aXm aX aR2]) ++ [R.run])) (Two fun (q : RPub × Addr) s => Rmid q.1 s) := by
  refine two_post (RelCT.seqs_app (by simp [mrWitness]) (by simp)
    (RelCT.seq (prefix_ct M hmc) ?_)) ?_
  · change RelCT isa (Two fun q => Caller.Before (roundPublic q)) R.run (fun _ _ => True)
    exact two_map roundPublic (fun _ _ h => h) R.ct
  · rintro q s ⟨⟨hk, hp, hd, mi, c, bm, r, uni, hc, he, hR2, hc1, hsh, hsrc, _, hlen,
        hun, _, huni, _, hpass⟩, hz, henv⟩
    have hm := (hp0 hp).mrh
    refine WP.mono (sharedMid_ok M hmc R hd hz henv hc he hR2 hc1 hsh hm.rand hm.used hm.len hsrc hlen
      hm.ki hun hm.chk) ?_
    rintro t ⟨⟨bm', hct⟩, het, hf, hi, huni', hchk, hu, hus, hr2, hfr, ht⟩
    refine ⟨hk, hp_shared_used hp hct.good ht.2.2 hz henv hfr ?_ hus, hd, mi, uni, _,
      hct.good, by rw [hf, hpass], huni', hu, huni⟩
    intro k hmem r hr
    rcases List.mem_append.mp hr with hw | hc
    · simp only [witnessRanges, witRanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with (rfl | rfl | rfl) | (rfl | rfl | rfl)
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rng_disj
    · apply sharedKernel_hdr _ k ?_ r hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kE, kElen, sFn]

theorem sharedRound_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) :
    RelCT isa (Two SharedR0) (seqs (mrRoundWith mm R.run)) fun _ _ => True := by
  unfold mrRoundWith
  exact RelCT.seqs_app (by simp [mrWitness]) (by simp) (RelCT.seq (mid_ct M hmc R)
    (two_map Prod.fst (fun _ _ h => h) roundTail_ct))

end VG.Proof.RsaKeyGen.X86_64
