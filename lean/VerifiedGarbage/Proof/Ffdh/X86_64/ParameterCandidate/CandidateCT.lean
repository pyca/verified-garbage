module

public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Consume
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckGenerator
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckPrime
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LoadOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LeavePhase
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestQCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrimeCheckCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Screen
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.OuterCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrimeCheckCT
meta import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ffdh.X86_64.ParameterCandidate.GeneratorCT`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: timing of the requested generator policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (sLink ws)
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64

private theorem generator_header (d : CandidatePublic) (s : State) (h : PhaseLoaded false .all d s) :
    WP isa (.block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (ws .rax oGen))]) s
      (fun t => InnerHeader (d.inner false) t ∧ t.gpr .rdx = (d.inner false).gen) := by
  obtain ⟨mi, hg, hp, _⟩ := h.2
  have hb := h.1.1.base
  have hgen := hb.hdr (oGen, BitVec.ofNat 64 d.p.gen) (by simp [CandidateP.headers])
  have hrd := hb.scr.ld (show 8 * oGen + 8 ≤ d.p.Z by change 88 ≤ d.p.Z; omega_using [hb.header_room])
  have hlinkrd := hg.scr.ld (show 8 * sLink + 8 ≤ d.p.Z - 256 by
    have hz := (hb.phase_dims false).z
    change 136 ≤ d.p.Z - 256; unfold slot hdrBytes at hz; omega_using [hz])
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 d.p.gen ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, ws, hdrOff, hg.rdi, hp.link, hgen, hrd, hlinkrd]) rfl)
    fun t ⟨⟨hdx, hm⟩, k⟩ => ?_
  have hgt : Good t (off d.p.B 256) (d.p.Z - 256) (d.p.phaseWords false) mi :=
    ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  exact ⟨⟨h.1.2.2, good_hp hgt (k.2.2.trans h.1.2.1)⟩, hdx⟩

theorem generatorPolicy_ct : RelCT isa (Two (PhaseLoaded false .all)) generatorPolicy fun _ _ => True := by
  unfold generatorPolicy
  exact RelCT.seq (two_post
    (two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.link) generatorHead_ct)
    generator_header) (two_map (fun d : CandidatePublic => d.inner false) (fun _ _ h => h) inner_generator_ct)

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! ### `Ffdh.X86_64.ParameterCandidate.InitialStages`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: retain the initial candidate through trial checks -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64

def CandidatePublic.afterCandidate (d : CandidatePublic) : CandidatePublic := { d with used := d.p.k }

theorem consume_initial (d : CandidatePublic) (s : State) (h : OuterValue false d s ∧ d.used = 0) :
    WP isa (.block consumeCandidate) s (OuterValue false d.afterCandidate) := by
  have ht : CandidateTape d.p 0 s := by simpa only [h.2] using h.1.1.1.1
  exact WP.mono (consumeCandidate_ok ht h.1.1.2 d.available)
    fun t ⟨ht', _, _, k, hv⟩ => ⟨⟨⟨ht', k.2.2.trans h.1.1.1.2.1, h.1.1.1.2.2⟩,
      (k.gpr (by decide)).trans h.1.1.2⟩, by
        change Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem d.p.op d.p.k) = d.p.P
        rw [hv]; exact h.1.2⟩

def InitialLoaded (d : CandidatePublic) (s : State) : Prop :=
  PhaseLoaded false .all d s ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.p.op d.p.k) = d.p.P

theorem load_initial (d : CandidatePublic) (s : State) (h : PhaseSet false .all d s) :
    WP isa loadOutput s (InitialLoaded d) := by
  obtain ⟨mi, hg, hp, hv⟩ := h.2
  exact WP.mono (loadOutput_ok h.1.1 hg hp hv)
    fun _ ⟨ht, hgt, hpt, hnt, _, _, k, hbytes⟩ =>
      ⟨⟨⟨ht, k.2.2.trans h.1.2.1, h.1.2.2⟩, mi, hgt, hpt, hnt⟩, by rw [hbytes]; exact hv⟩

def InitialGenerator (d : CandidatePublic) (s : State) : Prop :=
  InitialLoaded d s ∧ s.zf = some d.p.congruent

theorem generator_initial (d : CandidatePublic) (s : State) (h : InitialLoaded d s) :
    WP isa generatorPolicy s (InitialGenerator d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.1.2
  exact WP.mono (generatorCheck_state_ok h.1.1.1 hg hp hn)
    fun _ ⟨ht, hgt, hpt, hnt, hz, hm, k⟩ =>
      ⟨⟨⟨⟨ht, k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩, mi, hgt, hpt, hnt⟩,
        by rw [hm]; exact h.2⟩, hz⟩

def InitialEarly (d : CandidatePublic) (s : State) : Prop :=
  InitialLoaded d s ∧ s.zf = some (earlyOk d.p.P)

theorem early_initial (d : CandidatePublic) (s : State) (h : InitialLoaded d s) :
    WP isa earlyCheck s (InitialEarly d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.1.2
  exact WP.mono (earlyCheck_state_ok h.1.1.1 hg hp hn)
    fun _ ⟨ht, hgt, hpt, hnt, hz, _, _, k, hbytes⟩ =>
      ⟨⟨⟨⟨ht, k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩, mi, hgt, hpt, hnt⟩,
        by rw [hbytes]; exact h.2⟩, hz⟩

theorem leave_initial (d : CandidatePublic) (s : State) (h : InitialLoaded d s) :
    WP isa (.block [VG.Impl.Rsa.X86_64.Crt.leave]) s (OuterValue false d) := by
  obtain ⟨_, hg, hp, _⟩ := h.1.2
  exact WP.mono (leavePhase_ok h.1.1.1 hg.rdi hp.link)
    fun _ ⟨ht, hd, hm, _, _, k⟩ => ⟨⟨⟨ht, k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩, hd⟩,
      by rw [hm]; exact h.2⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: timing of the complete candidate flow -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

theorem candidateFilter_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two (OuterValue false)) (candidateFilter M.mm R.code K.run) fun _ _ => True := by
  unfold candidateFilter
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.header) (phaseSetup_ct false .all)) (setup_phase false .all)) ?_
  refine RelCT.seq (two_post (loadOutput_ct false .all) load_initial) ?_
  refine RelCT.seq (two_post
    (two_map (fun d : CandidatePublic => d) (fun _ _ h => h.1) generatorPolicy_ct) generator_initial) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
  · refine RelCT.seq (two_post
      (two_map (fun d : CandidatePublic => d) (fun _ _ h => h.1.1.1) (earlyCheck_ct false .all))
      (fun d s h => early_initial d s h.1.1)) ?_
    refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
    · exact RelCT.seq (two_post
        (two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1.1.link) leave_ct)
        (fun d s h => leave_initial d s h.1.1)) (sieveQ_ct M R K)
    · exact two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1.1.link) innerReject_ct
  · exact two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1.1.link) innerReject_ct

/-- The candidate's state after the generator's comparison. -/
private theorem screen_head (d : CandidatePublic) (s : State) (h : OuterValue false d s) :
    WP isa (.block [.mov .rdx (.mem (VG.Impl.Bignum.X86_64.hdr oGen)), .alu .cmp .rdx (.imm 2)]) s
      fun t => OuterValue false d t ∧ t.zf = some (decide (d.p.gen = 2)) := by
  have ht := h.1.1.1
  have hrdh : ∀ j < 32, InRegions (s.rd ++ s.wr) (VG.Proof.Bignum.off d.p.B (8 * j)) 8 :=
    fun j hj => ht.base.scr.ld (by omega_using [hj, ht.base.header_room])
  have hGen := ht.base.hdr (oGen, BitVec.ofNat 64 d.p.gen) (by simp [CandidateP.headers])
  refine WP.mono (WP.keep [.rdx] (Q := fun u => u.zf = some (decide (d.p.gen = 2)) ∧ u.mem = s.mem)
    (by
      xrun [State.ea, VG.Impl.Bignum.X86_64.hdr, h.1.2, hdrOff, hGen, hrdh oGen (by decide)]
      exact ofNat_sub_beq (N := 2) (by rcases ht.base.gen with h | h <;> rw [h] <;> decide) (by decide)) rfl)
    fun u ⟨⟨hz, hm⟩, k⟩ => ⟨⟨⟨⟨(ht.same_mem hm k (by decide)).1, k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩,
      (k.gpr (by decide)).trans h.1.2⟩, by rw [hm]; exact h.2⟩, hz⟩

/-- The screen's flag, for the public candidate. -/
private theorem screen_value (d : CandidatePublic) (s : State) (h : OuterValue false d s) :
    WP isa outerScreen s fun t => OuterValue false d t ∧ t.zf = some (screen d.p.gen d.p.P) := by
  have ht := h.1.1.1
  refine WP.mono (outerScreen_ok ht h.1.2) fun u ⟨hz, hm, k⟩ => ⟨⟨⟨⟨(ht.same_mem hm k (by decide)).1,
    k.2.2.trans h.1.1.2.1, h.1.1.2.2⟩, (k.gpr (by decide)).trans h.1.2⟩, by rw [hm]; exact h.2⟩, ?_⟩
  rw [hz]; congr 2; exact h.2

theorem outerScreen_ct : RelCT isa (Two (OuterValue false)) outerScreen fun _ _ => True := by
  unfold outerScreen
  refine RelCT.seq (two_post (two_map CandidatePublic.outer (fun _ _ h => h.1.header) screenHead_ct)
    screen_head) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
  · exact two_map CandidatePublic.outer (fun _ _ h => h.1.1.1.header) byteScreen2_ct
  · exact two_map CandidatePublic.outer (fun _ _ h => h.1.1.1.header) byteScreen5_ct

private theorem shape_initial (d : CandidatePublic) (s : State) (h : OuterState d s ∧ d.used = 0) :
    WP isa shapeOriginal s (fun t => OuterValue false d t ∧ d.used = 0) :=
  WP.mono (shape_outer d s h.1) fun _ ht => ⟨ht, h.2⟩

theorem testCandidate_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two fun d s => OuterState d s ∧ d.used = 0) (testCandidate M.mm R.code K.run) fun _ _ => True := by
  unfold testCandidate
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.header) shapeOriginal_ct)
    shape_initial) ?_
  refine RelCT.seq (two_post
    (two_map CandidatePublic.outer (fun _ _ h => h.1.1.header) consumeCandidate_ct) consume_initial) ?_
  refine two_map CandidatePublic.afterCandidate (fun _ _ h => h) ?_
  refine RelCT.seq (two_post outerScreen_ct screen_value) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_ ?_
  · exact two_map id (fun _ _ h => h.1.1) (candidateFilter_ct M R K)
  · exact two_map CandidatePublic.outer (fun _ _ h => h.1.1.1.header) screenReject_ct

end VG.Proof.Ffdh.X86_64.ParameterCandidate
