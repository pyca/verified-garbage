module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCTMain
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedCTResult
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineRel
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift

/-! # Constant time of setup and the callable RSA witness loop -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen (shapeOf)

structure SharedTPub extends TPub where
  sp : Addr
  z28 : slot w 28 ≤ Z

abbrev SharedTPub.lp (q : SharedTPub) : SharedLPub := ⟨q.toTPub.lp, q.sp, q.z28⟩

def SharedMsPre (q : SharedTPub) (s : State) : Prop :=
  MsPre q.toTPub s ∧ SharedEnv q.B q.Z q.sp s

def SharedMrPre0 (a : SharedLPub) (s : State) : Prop :=
  MrPre0 a.toLPub s ∧ SharedEnv a.p.B a.p.Z a.sp s

private theorem setup_run (M : Mont) {q : TPub} {s : State} (h : MsPre q s) :
    ∃ t s', Exec isa (seqs (montSetup M.mm)) s t s' := by
  obtain ⟨⟨-, -, hd, -⟩, -, mi, c, r, hg, hn, hsh, -⟩ := h
  obtain ⟨hodd, hlo, -⟩ := hsh
  have htop : 2 ^ (64 * q.w - 1) ≤ c := by
    have : 2 ^ (64 * q.w - 1) = 2 ^ (64 * q.w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; have := hd.w4; omega_arith
    omega_arith
  obtain ⟨t, s', he, -⟩ := montSetup_ok M hg hd.z hd.x hd.w4 hd.w64 hn hodd htop
  exact ⟨t, s', he⟩

private theorem setup_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) : RelCT isa (Two SharedMsPre) (seqs (montSetup mm))
    (Two fun q : SharedTPub => SharedMrPre0 q.lp) := by
  refine two_post ?_ ?_
  · refine RelCT.of_inline (montSetup_inlineOk hmc.ok) ?_ ?_ ?_ ?_
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      rw [hmc.montSetup]
      exact ⟨setup_run M h₁.1, setup_run M h₂.1⟩
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      exact ⟨h₁.2.hole_clear, h₂.2.hole_clear⟩
    · rintro s₁ s₂ ⟨q, h₁, h₂⟩
      exact h₁.2.rsp.trans h₂.2.rsp.symm
    · rw [hmc.montSetup]
      exact (two_map SharedTPub.toTPub (fun _ _ h => h.1) (montSetup_ct M)).mono
        (fun _ _ h => h) (fun _ _ _ => trivial)
  · rintro q s ⟨⟨⟨hk, hw, hd, -⟩, hrl, mi, c, r, hg, hn, hsh, hO, hU, hR, hK, hRL, hUs, hsrc, hrlen, hrk, hS⟩, henv⟩
    obtain ⟨hodd, hlo, hhi⟩ := hsh
    have hw4 := hd.w4
    have hnw := hg.scr.nowrap
    have htop : 2 ^ (64 * q.w - 1) ≤ c := by
      have : 2 ^ (64 * q.w - 1) = 2 ^ (64 * q.w - 2) * 2 := by rw [← Nat.pow_succ]; congr 1; omega_arith
      omega_arith
    refine WP.mono (montSetup_call_ok M hmc henv hg hd.z hd.x hw4 hd.w64 hn hodd htop)
      fun t ⟨mi', hg', hinv, hr2, hr1, hrm1, hchk, hf, k⟩ => ?_
    have e : ∀ x, x = kOut ∨ x = kUsedP ∨ x = kRand ∨ x = kLen ∨ x = kRandLen ∨ x = kUsed →
        word t.mem q.B (8 * x) = word s.mem q.B (8 * x) := fun x hx => SharedFrame.word hf henv (msRanges_hdr _ x (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hx)) (by
          have := hd.z
          have hk32 : x < 32 := by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          have := hdr_lt_slot q.w 8 hk32
          omega_arith) hnw
    have hn' : wv t.mem q.B (slot q.w aN) q.w = c := by
      rw [SharedFrame.array hf henv (d := slot q.w aN) (k := q.w) (by simp only [msRanges]; rng_disj)
        (by have := slot_le (w := q.w) (show aN < 8 by decide); have := hd.z; omega_arith) hnw]; exact hn
    have hle : ∀ r ∈ msRanges q.w, r.1 + r.2 ≤ q.Z := fun r hr => by
      have : r.1 + r.2 ≤ slot q.w aRm1 + 8 * (q.w + 2) := by revert r hr; simp only [msRanges]; rng_le
      have := hd.x; omega_arith
    have hc1 : 1 < c := by have := Nat.two_pow_pos (64 * q.w - 2); omega_arith
    have hch : Proof.RsaKeyGen.checksW q.w < 2 ^ 62 := by
      unfold Proof.RsaKeyGen.checksW; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
        (try split) <;> decide
    exact ⟨⟨hk, ⟨hg'.rdi, k.2.2.trans hw, fun _ he => absurd he List.not_mem_nil⟩, hd.mr, hch, hrl, mi', c,
      wv t.mem q.B (slot q.w aB) q.w, r, ⟨hg', hinv, hn', rfl, hr1, hrm1⟩, hr2, hc1, ⟨hodd, hlo, hhi⟩,
      by rw [e _ (Or.inl rfl)]; exact hO, by rw [e _ (Or.inr (Or.inl rfl))]; exact hU,
      by rw [e _ (Or.inr (Or.inr (Or.inl rfl)))]; exact hR, by rw [e _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact hK,
      by rw [e _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact hRL, hrlen, hchk,
      hsrc.shared henv hf hle k, by rw [e _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]; exact hUs,
      Nat.le_refl _, hrk, hS⟩, henv.kept k (by decide)⟩

private theorem exponent_ct : RelCT isa (Two SharedMrPre0) (seqs expSetup) (Two SharedMrPre) := by
  refine two_post ?_ ?_
  · exact (two_map SharedLPub.toLPub (fun _ _ h => h.1) expSetup_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)
  · rintro a s ⟨h, henv⟩
    have ht := expSetup_pre h
    obtain ⟨hk, hp, hd, hch, hrl, mi, c, bm, r, hc, hr2, hc1, hsh, _⟩ := h
    refine WP.mono (WP.and' ht (WP.mono (expSetup_ok hc.good hd hc.n hsh.1 hc1)
      (fun t ⟨_, _, _, k⟩ => henv.kept k (by decide)))) ?_
    rintro t ⟨⟨hk, hp, hd, hch, hrl, mi, c, bm, r, hc, he, hr2, hc1, hsh, ho, hup, hR, hK, hRL, hrlen, hC,
      hsrc, hU, hu1, hu2, hS⟩, henv⟩
    exact ⟨hk, hp, hd, hch, hrl, mi, c, bm, r, hc, he, hr2, hc1, hsh, ho, hup, hR, hK, hRL, hrlen, hC,
      hsrc, hU, hu1, hu2, hS, henv⟩

theorem sharedTail_ct (M : Mont) {mm : Nat → Nat → Nat → Prog isa} (hmc : MmCalls M mm) (R : Kernel) :
    RelCT isa (Two SharedMsPre)
      (seqs (montSetup mm ++ expSetup ++ millerRabinWith mm R.run ++ [mrResult]))
      (fun _ _ => True) :=
  RelCT.seqs_app (by simp [montSetup]) (List.cons_ne_nil _ _)
    (RelCT.seq (RelCT.seqs_app (by simp [montSetup]) (by simp [millerRabinWith])
      (RelCT.seq (RelCT.seqs_app (by simp [montSetup]) (by simp [expSetup, lowWord])
        (RelCT.seq (setup_ct M hmc) (two_map SharedTPub.lp (fun _ _ h => h) exponent_ct)))
        (sharedMillerRabin_ct M hmc R))) sharedResult_ct)

end VG.Proof.RsaKeyGen.X86_64
