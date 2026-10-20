module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundResultCT
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRoundCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundStatus
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundCall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundResultCT
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRoundCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundStatus
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundCall
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of an optional sampled round -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

def SampleAt (d : RunPublic) (s : State) : Prop := match d.sample with
  | none => word s.mem d.p.O (8 * oStatus) = 0
  | some a => word s.mem d.p.O (8 * oStatus) = 1 ∧ wv s.mem d.p.I (slot d.p.w aXm) d.p.w = a

def RunBefore (d : RunPublic) (s : State) : Prop := RunContext d s ∧ SampleAt d s

def RunFlagged (d : RunPublic) (s : State) : Prop := RunBefore d s ∧ s.zf = some d.sample.isNone

def LiveRun (d : RunPublic) (s : State) : Prop := RunBefore d s ∧ d.sample.isSome = true

private theorem status_after (d : RunPublic) (s : State) (h : RunBefore d s) :
    WP isa (.block statusTest) s (RunFlagged d) := by
  obtain ⟨rp, used, bs, ht, hroom, hsp, hw, hk, hi, hc, hi32, hc32⟩ := h.1
  have houter : Scr s d.p.O 256 := by
    simpa [off] using ht.scr.sub (o := 0) (n := 256) d.p.space_bounds.1 (by decide)
  have hstatus : word s.mem d.p.O (8 * oStatus) = BitVec.ofNat 64 (if d.sample.isSome then 1 else 0) := by
    cases he : d.sample with
    | none => simpa [SampleAt, he] using h.2
    | some a =>
      have hh := h.2
      simp only [SampleAt, he] at hh
      simpa [he] using hh.1
  have hsmall : (if d.sample.isSome then 1 else 0) < 2 ^ 64 := by split <;> decide
  refine WP.mono (statusTest_ok ht.ready.good.scr d.p.space_bounds.2.1 houter ht.ready.good.rdi
    ht.link hstatus hsmall) fun t ⟨hz, hm, k⟩ => ?_
  have hst : t.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨⟨rp, used, bs, ht.same_mem hm k ((k.gpr (by decide)).trans ht.ready.good.rdi),
    hroom.congr hst, hst.trans hsp, k.2.2.trans hw, hk, by rw [hm]; exact hi, by rw [hm]; exact hc, hi32, hc32⟩, ?_⟩, ?_⟩
  · simpa only [SampleAt, hm] using h.2
  · have he : decide ((if d.sample.isSome then 1 else 0) = 0) = d.sample.isNone := by
      cases d.sample <;> rfl
    simpa only [he] using hz

private theorem live_witness {d : RunPublic} {s : State} (h : LiveRun d s) :
    wv s.mem d.p.I (slot d.p.w aXm) d.p.w = d.sample.getD 0 := by
  cases he : d.sample with
  | none =>
    have hx := h.2
    simp only [he, Option.isSome_none, Bool.false_eq_true] at hx
  | some a =>
    have hx := h.1.2
    simp only [SampleAt, he] at hx
    simpa only [he, Option.getD_some] using hx.2

private theorem live_before {d : RunPublic} {s : State} (h : LiveRun d s) :
    BeforeRound ⟨⟨d.p.I, d.p.IZ, d.p.w⟩, d.p.N, d.sample.getD 0, d.sp⟩ s := by
  obtain ⟨_, _, _, ht, hroom, hsp, _, _, _⟩ := h.1.1
  refine ⟨d.p.mi, ht.ready, d.p.dims, ?_, hroom.call, hsp, d.p.odd, d.p.n3, live_witness h⟩
  change slot d.p.w 28 ≤ d.p.Z - 256
  omega_using [d.p.room]

private theorem live_round (M : Mont) (K : Kernel) (d : RunPublic) (s : State) (h : LiveRun d s) :
    WP isa (witnessRound M.mm K.run) s (FlagBefore d) := by
  obtain ⟨rp, used, bs, ht, hroom, hsp, hw, hk, hi, hc, hi32, hc32⟩ := h.1.1
  refine WP.mono (witnessRound_state_ok M K ht hroom (live_witness h))
    fun t ⟨ht', hflag, hwords, _, k⟩ => ?_
  have hst : t.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  exact ⟨⟨rp, used, bs, ht', hroom.congr hst, hst.trans hsp, k.2.2.trans hw, hk,
    (hwords _ (by decide)).trans hi, (hwords _ (by decide)).trans hc, hi32, hc32⟩, hflag⟩

theorem roundRun_ct (M : Mont) (K : Kernel) :
    RelCT isa (Two RunBefore) (roundRun M.mm K.run)
      (Two fun (d : RunPublic) s => LinkHeader ⟨d.p.O, d.wr⟩ s) := by
  unfold roundRun
  refine RelCT.seq (two_post
    (two_map (fun d : RunPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.link) statusTest_ct)
    status_after) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2])
    (two_piece [] (VG.Proof.RsaKeyGen.X86_64.pins_nil _) (by taint_decide)
      (fun _ _ h => WP.block_nil h.1.1.1.link)) ?_
  have hc : RelCT isa (Two LiveRun) (.seq (witnessRound M.mm K.run) roundResult)
      (Two fun (d : RunPublic) s => LinkHeader ⟨d.p.O, d.wr⟩ s) :=
    RelCT.seq (two_post
      (two_map (fun d : RunPublic => (⟨⟨d.p.I, d.p.IZ, d.p.w⟩, d.p.N, d.sample.getD 0, d.sp⟩ : RoundPublic))
        (fun _ _ h => live_before h) (witnessRound_ct M K)) (live_round M K)) (two_post roundResult_ct roundResult_link)
  refine hc.mono ?_ (fun _ _ h => h)
  rintro s₁ s₂ ⟨d, h₁, h₂⟩
  have hs : d.sample.isSome = true := by
    have hx : d.sample.isNone = false := by simpa only [eval, h₁.1.2, Option.some.injEq] using h₁.2
    cases he : d.sample <;> simp_all
  exact ⟨d, ⟨h₁.1.1, hs⟩, ⟨h₂.1.1, hs⟩⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
