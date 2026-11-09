module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndContract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomCT
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndContract
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RandomCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndScan
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.RndScan

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on AArch64: the scan in constant time

Two runs from entry states that agree with an anchor `a` on the public data
(`PR`) read the same octets of the tape and keep as many of them: the scan
reads `scanLen` octets of `a`'s tape in both (`N`), each read octet is zero in
one run exactly when it is in the other, and so is each count of kept octets
(`Proof/RsaPkcs1Enc/RandomCT.lean`). So the branch on each octet, the address
of each load and store and the end of the loop are the same in both runs;
the taint analysis checks the rest, with these registers public.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Rnd

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Random
open VG.Proof.Bignum.AArch64 (Two two_post two_taint two_piece two_ite two_loop)

variable {P : Nat}

/-- An entry state meeting the precondition with the anchor's public data. -/
def PR (P : Nat) (a s : State) : Prop := (contract P).pre s ∧ pub a s

theorem PR.pre {a s : State} (h : PR P a s) : RPre P s := pre_of h.1

theorem PR.gprEq {a s : State} (h : PR P a s) {r : Reg}
    (hr : r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7]) : s.gpr r = a.gpr r := (h.2.2.1 r hr).symm

theorem PR.spEq {a s : State} (h : PR P a s) : s.sp = a.sp := h.2.1.symm

theorem PR.argEq {a s : State} (h : PR P a s) {j : Nat} (hj : j < 7) : stackArg s j = stackArg a j :=
  (h.2.2.2.1 j hj).symm

theorem PR.QEq {a s : State} (h : PR P a s) : Q s = Q a := by
  show s.sp - _ = a.sp - _; rw [h.spEq]

theorem PR.psEq {a s : State} (h : PR P a s) : psLen s = psLen a := by
  unfold psLen kOf; rw [h.gprEq (r := .x4) (by decide), h.argEq (j := 0) (by decide)]

theorem PR.lenEq {a s : State} (h : PR P a s) : (stackArg s 2).toNat = (stackArg a 2).toNat := by
  rw [h.argEq (by decide)]

theorem PR.traceEq {a s : State} (h : PR P a s) :
    (Spec.RsaPkcs1Enc.padSearch (psLen a) (randB s)).trace =
      (Spec.RsaPkcs1Enc.padSearch (psLen a) (randB a)).trace := by
  have := h.2.2.2.2.2.2.2
  simp only [trace, h.psEq] at this
  exact this.symm

/-- The octets the scan reads, the anchor's. -/
abbrev N (a : State) : Nat := VG.Proof.RsaPkcs1Enc.scanLen (psLen a) (randB a)

theorem PR.scanEq {a s : State} (h : PR P a s) :
    VG.Proof.RsaPkcs1Enc.scanLen (psLen s) (randB s) = N a := by
  rw [h.psEq]; exact VG.Proof.RsaPkcs1Enc.scanLen_eq h.traceEq

theorem PR.keptEq {a s : State} (h : PR P a s) {j : Nat} (hj : j ≤ N a) :
    (kept s j).length = (kept a j).length :=
  VG.Proof.RsaPkcs1Enc.nz_take_length_eq h.traceEq j (by rw [← h.psEq, h.scanEq]; exact hj)

theorem PR.zeroIff {a s : State} (h : PR P a s) {j : Nat} (hj : j < N a) :
    (randB s).getD j 0 = 0 ↔ (randB a).getD j 0 = 0 :=
  VG.Proof.RsaPkcs1Enc.zero_iff h.traceEq (by rw [← h.psEq, h.scanEq]; exact hj)

/-! ## The loop -/

/-- Before octet `j` of the scan. -/
def LoopPt (P : Nat) (a : State) (j : Nat) (u : State) : Prop :=
  ∃ s t₀, PR P a s ∧ Before s t₀ ∧ At s t₀ j u ∧ j < (stackArg s 2).toNat ∧ (kept s j).length < psLen s

/-- After the load of octet `j`. -/
def LoadPtA (P : Nat) (p : State × Nat) (v : State) : Prop :=
  ∃ s t₀ u, PR P p.1 s ∧ Before s t₀ ∧ At s t₀ p.2 u ∧ LoadStep u v ∧ p.2 < (stackArg s 2).toNat ∧
    (kept s p.2).length < psLen s ∧ p.2 < N p.1

/-- After octet `j`, before `x9`. -/
def NextPt (P : Nat) (p : State × Nat) (w : State) : Prop :=
  ∃ s t₀, PR P p.1 s ∧ Before s t₀ ∧ At s t₀ (p.2 + 1) w ∧ p.2 < N p.1

theorem x11_eq {a s t₀ u : State} (S : PR P a s) {j : Nat} (I : At s t₀ j u) :
    u.gpr .x11 = stackArg a 1 + BitVec.ofNat 64 j := by
  rw [I.x11, S.argEq (by decide)]

theorem load_two :
    RelCT isa (Two fun (p : State × Nat) s => p.2 < N p.1 ∧ LoopPt P p.1 p.2 s) (.block load) (Two (LoadPtA P)) := by
  refine two_piece [.x11] (fun p u₁ u₂ ⟨_, s₁, t₁, S₁, _, I₁, _⟩ ⟨_, s₂, t₂, S₂, _, I₂, _⟩ r hr => ?_)
    (by taint_decide) fun p u ⟨hN, s, t₀, S, B, I, hi, hc⟩ => ?_
  · rw [List.mem_singleton.mp hr, x11_eq S₁ I₁, x11_eq S₂ I₂]
  · have hwR := S.pre.wR
    have hr : InRegions (u.rd ++ u.wr) (u.gpr .x11 + BitVec.ofNat 64 0) 1 :=
      ⟨randR s, by rw [I.fr.rd, S.pre.hrd]; simp, by
        rw [add_zero', I.x11]; exact Offset.contains_base _ (by omega) (by omega)⟩
    exact WP.mono (load_ok hr) fun v h => ⟨s, t₀, u, S, B, I, h, hi, hc, hN⟩

theorem x14_eq {a s t₀ u : State} (S : PR P a s) {j : Nat} (hj : j ≤ N a) (I : At s t₀ j u) :
    u.gpr .x14 = off (Q a) (oBuf + (kept a j).length) := by
  rw [I.x14, S.QEq, S.keptEq hj]

theorem x17_eq {a s t₀ u v : State} (S : PR P a s) {j : Nat} (I : At s t₀ j u) (L : LoadStep u v)
    (hi : j < (stackArg s 2).toNat) : v.gpr .x17 = ((randB s).getD j 0).setWidth 64 := by
  rw [L.x17, I.x11, rand_byte' S.pre I.fr hi]

theorem branch_two :
    RelCT isa (Two (LoadPtA P)) (.ite (.zero .x .x17) (.block []) (.block keep)) (Two (NextPt P)) := by
  refine two_post (two_ite (fun p v₁ v₂ ⟨s₁, t₁, u₁, S₁, _, I₁, L₁, hi₁, _, hN⟩
      ⟨s₂, t₂, u₂, S₂, _, I₂, L₂, hi₂, _, _⟩ => ?_) ?_ ?_) ?_
  · rw [eval_zero, eval_zero, x17_eq S₁ I₁ L₁ hi₁, x17_eq S₂ I₂ L₂ hi₂, zero_byte, zero_byte]
    rw [decide_eq_decide.mpr ((S₁.zeroIff hN).trans (S₂.zeroIff hN).symm)]
  · exact two_taint [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
  · refine two_taint [.x14] (fun p v₁ v₂ ⟨⟨s₁, t₁, u₁, S₁, _, I₁, L₁, _, _, hN⟩, _⟩
        ⟨⟨s₂, t₂, u₂, S₂, _, I₂, L₂, _, _, _⟩, _⟩ r hr => ?_) (by taint_decide)
    rw [List.mem_singleton.mp hr, L₁.other _ (by decide) (by decide) (by decide),
      L₂.other _ (by decide) (by decide) (by decide), x14_eq S₁ (Nat.le_of_lt hN) I₁,
      x14_eq S₂ (Nat.le_of_lt hN) I₂]
  · intro p v ⟨s, t₀, u, S, B, I, L, hi, hc, hN⟩
    exact WP.mono (branch_ok S.pre I L hi hc) fun w h => ⟨s, t₀, S, B, h, hN⟩

theorem mul_two : RelCT isa (Two (NextPt P)) (.block [.mul .x .x9 .x12 .x16]) fun _ _ => True :=
  two_taint [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)

theorem step_two :
    RelCT isa (Two fun (p : State × Nat) s => p.2 < N p.1 ∧ LoopPt P p.1 p.2 s) step fun _ _ => True :=
  RelCT.seq load_two (RelCT.seq branch_two mul_two)

/-- At the end of the scan: all `N a` octets read. -/
def ScanDone (P : Nat) (a u : State) : Prop := ∃ s t₀, PR P a s ∧ Before s t₀ ∧ At s t₀ (N a) u

theorem loop_two :
    RelCT isa (Two fun a s => 0 < N a ∧ LoopPt P a 0 s) (.loop step (.nonzero .x .x9)) (Two (ScanDone P)) := by
  refine two_loop (Φ := LoopPt P) N step_two ?_
  intro a j u hj ⟨s, t₀, S, B, I, hi, hc⟩
  have hs : VG.Proof.RsaPkcs1Enc.scanLen (psLen s) (randB s) = N a := S.scanEq
  refine WP.mono (step_ok S.pre I hi hc) fun u' ⟨I', hz⟩ => ?_
  have hst : ((kept s (j + 1)).length = psLen s ∨ j + 1 = (stackArg s 2).toNat) ↔ N a = j + 1 := by
    have := VG.Proof.RsaPkcs1Enc.stop_iff (n := psLen s) (r := randB s) (j := j) (by rw [hs]; exact hj) hc
    rw [randB_length, hs] at this; exact this
  have hk := I'.hc
  refine ⟨?_, fun hlt => ⟨s, t₀, S, B, I', ?_, ?_⟩, fun he => ⟨s, t₀, S, B, he ▸ I'⟩⟩
  · rw [Bytes.eval_nonzero, hz]
    by_cases h : (kept s (j + 1)).length = psLen s ∨ j + 1 = (stackArg s 2).toNat
    · rw [decide_eq_false (not_not_intro h), decide_eq_false (by have := hst.mp h; omega)]
    · rw [decide_eq_true h, decide_eq_true (by
        have : N a ≠ j + 1 := fun e => h (hst.mpr e)
        omega)]
  · have := VG.Proof.RsaPkcs1Enc.scanLen_le (psLen s) (randB s)
    rw [randB_length, hs] at this; omega
  · by_cases hn : (kept s (j + 1)).length = psLen s
    · have := hst.mp (.inl hn); omega
    · omega

/-- Before the scan. -/
def ScanPt (P : Nat) (a t : State) : Prop := ∃ s, PR P a s ∧ Before s t

theorem scan_two : RelCT isa (Two (ScanPt P)) scan (Two (ScanDone P)) := by
  refine two_ite (fun a t₁ t₂ ⟨s₁, S₁, B₁⟩ ⟨s₂, S₂, B₂⟩ => by
    rw [Bytes.eval_nonzero, Bytes.eval_nonzero, B₁.x12, B₂.x12, S₁.argEq (by decide), S₂.argEq (by decide)])
    ?_ ?_
  · refine loop_two.mono (fun t₁ t₂ ⟨a, ⟨⟨s₁, S₁, B₁⟩, e₁⟩, ⟨⟨s₂, S₂, B₂⟩, _⟩, hsp⟩ => ?_) fun _ _ h => h
    have hl : stackArg s₁ 2 ≠ 0 := by
      intro h0; rw [Bytes.eval_nonzero, B₁.x12, h0] at e₁; cases e₁
    have hl' : 0 < (stackArg s₁ 2).toNat := by
      rcases Nat.eq_zero_or_pos (stackArg s₁ 2).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hl
      · exact h
    have hP₁ := S₁.pre.ps
    have hP₂ := S₂.pre.ps
    have hN : 0 < N a := by
      rw [← S₁.scanEq]
      exact VG.Proof.RsaPkcs1Enc.lt_scanLen (i := 0)
        (show (kept s₁ 0).length < psLen s₁ by rw [kept_zero, List.length_nil]; omega)
        (by rw [randB_length]; exact hl')
    refine ⟨a, ⟨hN, s₁, t₁, S₁, B₁, at_zero S₁.pre B₁, hl', by rw [kept_zero, List.length_nil]; omega⟩,
      ⟨hN, s₂, t₂, S₂, B₂, at_zero S₂.pre B₂, by rw [S₂.lenEq, ← S₁.lenEq]; exact hl',
        by rw [kept_zero, List.length_nil]; omega⟩, hsp⟩
  · refine two_piece [] (fun _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
      fun a t ⟨⟨s, S, B⟩, e⟩ => WP.block_nil ⟨s, t, S, B, ?_⟩
    have h0 : stackArg s 2 = 0 := by
      rw [Bytes.eval_nonzero, B.x12] at e
      by_cases h : stackArg s 2 = 0
      · exact h
      · rw [bne_iff_ne.mpr h] at e; cases e
    have : N a = 0 := by
      rw [← S.scanEq]
      have := VG.Proof.RsaPkcs1Enc.scanLen_le (psLen s) (randB s)
      rw [randB_length, h0] at this
      simpa using this
    rw [this]; exact at_zero S.pre B

end VG.Proof.RsaPkcs1Enc.AArch64.Rnd
