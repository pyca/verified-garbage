module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvSq
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.RecoverTries
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvExp

/-!
# `vg_rsa_recover_primes` on PPC64LE: a candidate

`candBody_ok`: the candidate `j` from its set-up to the squarings' result
(`CP s0 j`), and whether to try the next one.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Spec.Rsa (recoverPrimes recoverStep recoverTries)
open VG.Impl.Rsa.PPC64LE.Recover (candLoop candBody candNext candSet mmul expLoop sqInit sqLoop mY aO aNg nArr sOk sE1 sE2
  iG iR2)
open VG.Impl.Rsa.PPC64LE.Keys (seqs eqS)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

/-- The sizes the candidates need: `c > 0` bits for `r`, and `1 ≤ t ≤ c`. -/
structure Par (s0 : State) : Prop where
  c0 : 0 < cB s0
  c31 : cB s0 < 2 ^ 31
  r : rR s0 < 2 ^ cB s0
  t1 : 1 ≤ tT s0
  tc : tT s0 ≤ cB s0

/-- After the candidate `j`. -/
structure CP (s0 : State) (j : Nat) (t : State) : Prop where
  cf : CF s0 t
  r24 : t.gpr .r24 = BitVec.ofNat 64 (j + 1)
  vY : num t.mem (rvB s0) (ww (kK s0)) mY = (sqst s0 j (cB s0)).1 * RR s0 % nV s0
  ok : slot t.mem (rvB s0) sOk = b2n (sqst s0 j (cB s0)).2.2

theorem b64_and (a b : Bool) : b64 a &&& (b64 b ^^^ 1#64) = b64 (a && !b) := by
  cases a <;> cases b <;> decide

/-- A candidate. -/
theorem candBody_ok {s0 u : State} (hn : NOk s0) (hp : Par s0) {j : Nat} (hj : j < 100) (h : CF s0 u)
    (h24 : u.gpr .r24 = BitVec.ofNat 64 j) :
    WP isa candBody u fun t => CP s0 j t ∧
      t.gpr .r0 = b64 (decide (j + 1 < 100) && !(sqst s0 j (cB s0)).2.2) := by
  have ht : tT s0 < 2 ^ 31 := by have := hp.tc; have := hp.c31; omega
  unfold candBody
  rw [wp_seqs_append (by simp) (by simp)]
  refine WP.mono (cand0_ok h hn hj h24) fun u1 ⟨e1, a27⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (expLoop_ok hn e1 a27 hp.c0 hp.c31) fun u2 e2 => ?_
  rw [show ∀ (l : List (Prog isa)), (eqS sE1 mY aO :: eqS sE2 mY aNg :: .block sqInit :: l) =
      [eqS sE1 mY aO, eqS sE2 mY aNg, .block sqInit] ++ l from fun _ => rfl,
    wp_seqs_append (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)]
  refine WP.mono (sqStart_ok hn e2 hp.r) fun u3 ⟨e3, a27'⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sqLoop_ok hn e3 a27' hp.c0 hp.c31 ht) fun u4 e4 => ?_
  rw [show seqs [Code.block candNext] = .block candNext from rfl]
  have c := e4.cf
  have hz : 160 ≤ rvZ s0 := c.ws.hdr_le
  have L := lt64 (a := j + 1) (b := 100) (by omega) (by decide)
  refine WP.mono (WP.keep [.r0, .r3, .r4, .r24] (Q := fun x => x.mem = u4.mem ∧ x.gpr .r24 = BitVec.ofNat 64 j + 1#64 ∧
    x.gpr .r0 = (BitVec.ofNat 64 j + 1#64 - 100#64) >>> 63 &&&
      (BitVec.ofNat 64 (b2n (sqst s0 j (cB s0)).2.2) ^^^ 1#64)) ?_ (by decide)) fun t ⟨⟨mt, a24, a0⟩, kt⟩ => ?_
  · prun [candNext, c.ws.r31, e4.r24, c.ws.scr.ld (show sOk + 4 ≤ rvZ s0 by simp only [sOk]; omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sOk < 2 ^ 15 by decide), ld_slot e4.ok]
  have e1 : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e1] at a24 a0
  rw [L, show BitVec.ofNat 64 (b2n (sqst s0 j (cB s0)).2.2) = b64 (sqst s0 j (cB s0)).2.2 from rfl, b64_and] at a0
  have kk : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [] u4.mem t.mem := by
    rw [mt]; exact KeyWorkspace.Keep.refl _ _ _ _ _
  refine ⟨⟨c.of_keep kk (by simp) (by simp) kt (c.ws.of_keep kt) (by decide), a24, by rw [mt]; exact e4.vY,
    by rw [mt]; exact e4.ok⟩, a0⟩

/-- `recoverPrimes`'s candidates from the `k`-th last. -/
abbrev gos (s0 : State) (k : Nat) : Option (Nat × Nat) × Nat := recoverPrimes.go (nV s0) (tT s0) (rR s0) k

/-- The candidates `recoverPrimes` tries. -/
abbrev nt (s0 : State) : Nat := (gos s0 recoverTries).2

theorem ok_eq {s0 : State} (hp : Par s0) (j : Nat) :
    (sqst s0 j (cB s0)).2.2 = (recoverStep (nV s0) (tT s0) (rR s0) (j + 2)).isSome := by
  rw [← VG.Proof.Rsa.sq_result (n := nV s0) (r := rR s0) (g := j + 2) hp.t1 hp.tc]
  show _ = (sqRes (sqst s0 j (cB s0))).isSome
  simp only [sqRes]
  cases (sqst s0 j (cB s0)).2.2 <;> rfl

theorem nt_pos (s0 : State) : 1 ≤ nt s0 := by
  have := VG.Proof.Rsa.go_ge1 (nV s0) (tT s0) (rR s0) (k := 99) (by decide)
  exact this

theorem nt_le (s0 : State) : nt s0 ≤ 100 := VG.Proof.Rsa.go_le _ _ _ _ (Nat.le_refl _)

/-- The candidates: as many as `recoverPrimes` tries, the last one's result. -/
theorem candLoop_ok {s0 u : State} (hn : NOk s0) (hp : Par s0) (h : CF s0 u) :
    WP isa candLoop u fun t => CP s0 (nt s0 - 1) t ∧ gos s0 recoverTries = gos s0 (recoverTries - (nt s0 - 1)) := by
  have n1 := nt_pos s0; have n2 := nt_le s0
  unfold candLoop
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r24] (Q := fun x => x.gpr .r24 = BitVec.ofNat 64 0 ∧ x.mem = u.mem) (by prun)
    (by decide)) fun u1 ⟨⟨a24, m1⟩, k1⟩ => ?_
  have c1 := h.of_keep (show KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [] u.mem u1.mem by
    rw [m1]; exact KeyWorkspace.Keep.refl _ _ _ _ _) (by simp) (by simp) k1 (h.ws.of_keep k1)
  refine WP.loop (M := isa) (fun m s => ∃ j, m = nt s0 - 1 - j ∧ j < nt s0 ∧ CF s0 s ∧ s.gpr .r24 = BitVec.ofNat 64 j ∧
    gos s0 recoverTries = gos s0 (recoverTries - j)) ?_ (nt s0 - 1) u1 ⟨0, rfl, by omega, c1, a24, rfl⟩
  rintro m s ⟨j, rfl, hj, cs, s24, hg⟩
  refine WP.mono (candBody_ok hn hp (by omega) cs s24) fun t ⟨cp, r0⟩ => ?_
  have cc := VG.Proof.Rsa.cand_cond (nV s0) (tT s0) (rR s0) (j := j) hj hg
  rw [← ok_eq hp] at cc
  have ev : isa.eval (.nonzero .d .r0) t = some (decide (j + 1 < nt s0)) := by
    rw [eval_nonzero_ofNat' t .r0 (by have := b2n_le (decide (j + 1 < 100) && !(sqst s0 j (cB s0)).2.2); omega) r0,
      ← cc, Bool.not_not]
    cases (decide (j + 1 < 100) && !(sqst s0 j (cB s0)).2.2) <;> rfl
  by_cases hl : j + 1 < nt s0
  · -- The candidate failed: the next one.
    refine .inr ⟨by rw [ev]; simp [hl], nt s0 - 1 - (j + 1), by omega, j + 1, rfl, hl, cp.cf, cp.r24, ?_⟩
    have hok : (sqst s0 j (cB s0)).2.2 = false := by
      have : (decide (j + 1 < 100) && !(sqst s0 j (cB s0)).2.2) = true := by
        rw [← Bool.not_not (decide _ && _), cc]; simpa using hl
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      exact this.2
    have hs : recoverStep (nV s0) (tT s0) (rR s0) (j + 2) = none := by
      rw [ok_eq hp] at hok
      exact Option.not_isSome_iff_eq_none.mp (by rw [hok]; decide)
    rw [hg]; show recoverPrimes.go _ _ _ _ = recoverPrimes.go _ _ _ _
    rw [VG.Proof.Rsa.go_eq _ _ _ (show j < recoverTries by unfold recoverTries; omega), hs]
  · refine .inl ⟨by rw [ev]; simp [hl], ?_, ?_⟩
    · rw [show nt s0 - 1 = j by omega]; exact cp
    · rw [show nt s0 - 1 = j by omega]; exact hg

end VG.Proof.Rsa.PPC64LE.Recover
