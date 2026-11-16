module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PublicRoundCT
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Backend
public import VerifiedGarbage.Impl.MillerRabin.AArch64.Caller
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerResult
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerSave
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerContext
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerBoundaryCT
import VerifiedGarbage.Proof.MillerRabin.AArch64.Prepared
import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA parameter generation on AArch64: the kernel of its round

`PublicKernel` is `MillerRabin.AArch64.Kernel` for a public candidate: its
runs leak the same when they agree on the working space and the candidate
(`BeforeC`), not on the working space alone. `PublicKernel.called` calls
`publicRound` as `Kernel.called` calls the shared round.
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.Generation

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Dsa.AArch64.Generation
open VG.Impl.MillerRabin.AArch64 VG.Impl.MillerRabin.AArch64.Caller
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64 VG.Proof.MillerRabin.AArch64.Caller
open VG.Proof.MlKem.AArch64 (Keep)

/-- Before the call (`Caller.Before`), for the candidate of the public data. -/
def BeforeC (p : CPub) (s : State) : Prop :=
  4 ≤ p.1.w ∧ p.1.w ≤ 128 ∧ slot p.1.w aE + 8 * (p.1.w + 2) ≤ p.1.Z ∧
    ∃ bm b : Nat, MrCtx s p.1.B p.1.Z p.1.w p.2 bm ∧ ECtx s.mem p.1.B p.1.w p.2 ∧
      p.2 % 2 = 1 ∧ 3 ≤ p.2 ∧ wv s.mem p.1.B (slot p.1.w aXm) p.1.w = b % p.2 * 2 ^ (64 * p.1.w) % p.2

theorem BeforeC.before {p : CPub} {s : State} (h : BeforeC p s) : Before p.1 s := by
  obtain ⟨h4, h128, hEZ, bm, b, hc, he, ho, h3, hx⟩ := h
  exact ⟨h4, h128, hEZ, _, bm, b, hc, he, ho, h3, hx⟩

/-- After the registers are saved (`Caller.Ready`). -/
def ReadyC (p : CPub) (s : State) : Prop :=
  BeforeC p s ∧ s.gpr .x19 = p.1.B ∧ s.gpr .x1 = BitVec.ofNat 64 (callWords p.1.w)

theorem ReadyC.ready {p : CPub} {s : State} (h : ReadyC p s) : Ready p.1 s := ⟨h.1.before, h.2⟩

theorem save_readyC {p : CPub} {s : State} (h : BeforeC p s) : WP isa (.block save) s (ReadyC p) := by
  obtain ⟨h4, h128, hEZ, bm, b, hc, he, ho, h3, hx⟩ := h
  refine WP.mono (save_ok hc.good.1 hc.good.2 h128) ?_
  rintro t ⟨hm, h19, h1, hk⟩
  obtain ⟨hct, het⟩ := save_context hc he hEZ hm hk
  refine ⟨⟨h4, h128, hEZ, bm, b, hct, het, ho, h3, ?_⟩, h19, h1⟩
  rw [hm, (saved_outside s p.1.B p.1.w (by
    have hz : slot p.1.w 16 ≤ p.1.Z := hc.ws.hZ
    have hn := hc.ws.scr.nowrap
    simp only [pad, slot, hdrBytes, aOne] at hz ⊢
    omega_arith)).wv (Or.inl (by simp only [pad, slot, hdrBytes, aOne, aXm]; omega_arith))
      (by
        have hsX := slot_le (w := p.1.w) (show aXm < 8 by decide)
        have hsZ := hc.good.2
        have hsN := hc.ws.scr.nowrap
        omega_arith)]
  exact hx

/-- The candidate the call's callee sees. -/
theorem ready_candidate {p : CPub} {s : State} (h : ReadyC p s) :
    candidateOf (narrowed s p.1.B p.1.w) = p.2 := by
  have h0 : (narrowed s p.1.B p.1.w).gpr .x0 = p.1.B := (s.callEntry_gpr (by decide)).trans (ready_base h.ready)
  obtain ⟨⟨_, _, _, bm, b, hc, _⟩, _⟩ := h
  have hw : Proof.Rsa.Mont.wOf s.mem p.1.B = p.1.w := ctx_width hc
  unfold candidateOf
  rw [h0]
  change Proof.Rsa.Mont.numAt s.mem p.1.B (Proof.Rsa.Mont.wOf s.mem p.1.B) 0 = p.2
  rw [hw, VG.Proof.Bignum.AArch64.MontFn.numAt_eq]
  exact hc.n

theorem publicPrepared_call_ct (M : Mont) (name : String) :
    RelCT isa (Two ReadyC) (.call name (publicRound M.mm)) fun _ _ => True := by
  apply RelCT.callEx (k := publicRoundContract) (publicRound_correct M) (publicRound_ct M)
  rintro s t ⟨p, hs, ht, hsp⟩
  have hcs := ready_covers hs.ready
  have hct := ready_covers ht.ready
  exact ⟨[], [⟨p.1.B, 8 * callWords p.1.w⟩], [], [⟨p.1.B, 8 * callWords p.1.w⟩],
    ready_pre hs.ready, ready_pre ht.ready,
    ⟨ready_pub hs.ready ht.ready hsp, (ready_candidate hs).trans (ready_candidate ht).symm⟩,
    Covers.right hcs, hcs, Covers.right hct, hct⟩

/-- A call of the round for public candidates leaks the same in runs that
agree on the working space and the candidate. -/
theorem publicCall_ct (M : Mont) (name : String) (hnf : (publicRound M.mm).noFrames = true) :
    RelCT isa (Two BeforeC) (call name (publicRound M.mm)) fun _ _ => True := by
  unfold VG.Impl.MillerRabin.AArch64.Caller.call
  refine RelCT.seq (two_post (Ψ := ReadyC) ?_ (fun _ _ h => save_readyC h)) ?_
  · exact save_ct.mono (fun _ _ ⟨p, hs, ht, hsp⟩ => ⟨p.1, before_good hs.before, before_good ht.before, hsp⟩)
      (fun _ _ h => h)
  · exact RelCT.seq (two_post (Ψ := fun p s => RestorePre p.1 s) (publicPrepared_call_ct M name)
      (fun _ _ h => call_restore_pre (publicRound_correct M) name hnf h.ready))
      (two_map (fun p : CPub => p.1) (fun _ _ h => h) restore_ct)

/-- The round for public candidates has no frames where the shared round has none:
they differ in the selection, which is blocks and a loop. -/
theorem publicRound_noFrames {mul : Nat → Nat → Nat → Prog isa}
    (h : (VG.Impl.MillerRabin.AArch64.round mul).noFrames = true) : (publicRound mul).noFrames = true := by
  simp only [VG.Impl.MillerRabin.AArch64.round, roundW, preparedRoundW, mrExpLoopW, mrWin, mrWinS, mrSq, mrLast,
    tabBuild, toEnt, eqMask, VG.Impl.Rsa.AArch64.Keys.eqA, mrSel, VG.Impl.Rsa.AArch64.Keys.copyA, copyWords,
    countLoop, VG.Impl.Rsa.AArch64.Crt.selLoop,
    List.cons_append, List.nil_append, List.append_assoc, seqs, Code.noFrames, Bool.and_eq_true, true_and,
    and_true, and_self] at h
  simp only [publicRound, publicWin, roundW, preparedRoundW, mrExpLoopW, mrWinS, mrSq, mrLast,
    tabBuild, toEnt, eqMask, VG.Impl.Rsa.AArch64.Keys.eqA, publicSel, VG.Impl.Rsa.AArch64.Keys.copyA, copyWords,
    countLoop,
    List.cons_append, List.nil_append, List.append_assoc, seqs, Code.noFrames, Bool.and_eq_true, true_and,
    and_true, and_self]
  exact h

/-- A prepared round for a public candidate: `Kernel`, but its runs agree on
the candidate too. -/
structure PublicKernel where
  run : List (Prog isa)
  nonempty : run ≠ []
  ok : ∀ {s : State} {B : Addr} {Z w c bm b : Nat},
    MrCtx s B Z w c bm → ECtx s.mem B w c → 4 ≤ w → w ≤ 128 →
    slot w aE + 8 * (w + 2) ≤ Z → c % 2 = 1 → 3 ≤ c →
    wv s.mem B (slot w aXm) w = b % c * 2 ^ (64 * w) % c →
    WP isa (seqs run) s fun t =>
      (∃ bm', MrCtx t B Z w c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kFlag) = mask (Proof.MillerRabin.Round.round c b) ∧
      Frm B (Caller.callRanges w) s.mem t.mem ∧ Keep mmRegs s t
  ct : RelCT isa (Two BeforeC) (seqs run) fun _ _ => True

/-- A call of the round for public candidates, keeping its workspace for the policy. -/
def PublicKernel.called (M : Mont) (name : String) (hnf : (publicRound M.mm).noFrames = true) :
    PublicKernel where
  run := [call name (publicRound M.mm)]
  nonempty := by simp
  ok := by exact Caller.call_result_ok (publicRound_correct M) name hnf
  ct := by exact publicCall_ct M name hnf

/-- The name of the round for public candidates that goes with a shared round. -/
def publicRoundName (v : RoundImpl) : String := "vg_dsa_miller_rabin_round" ++ v.suffix

/-- The kernel of DSA's parameter search for an implementation of the shared
round: the round for public candidates over the same multiplication. -/
def publicKernel (v : RoundImpl) : PublicKernel :=
  PublicKernel.called v.roundMont (publicRoundName v) (publicRound_noFrames v.noFrames)

end VG.Proof.Dsa.AArch64.Generation
