module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawLoop
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundResult
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundCall
import Mathlib.Basic.IsEmpty.Defs

/-! ### `Ffdh.X86_64.ParameterCandidate.RoundBody`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.RoundRun`, which this module and modules that import it used -/

section

/-! # FFDH parameter generation on x86-64: run only an accepted witness -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

def runStatus (p : WitnessParams) (i checks : Nat) : Option Nat → Nat
  | none => 0
  | some a => if Spec.Ffdh.mrRound p.N a then passStatus i checks else 2

def runIndex (p : WitnessParams) (i : Nat) : Option Nat → Nat
  | none => i
  | some a => if Spec.Ffdh.mrRound p.N a then i + 1 else i

theorem runStatus_bound (p : WitnessParams) (i checks : Nat) (sample : Option Nat) :
    runStatus p i checks sample ≤ 4 := by
  cases sample with
  | none => change 0 ≤ 4; omega_using []
  | some a =>
    change (if Spec.Ffdh.mrRound p.N a then (if i + 1 < checks then 4 else 1) else 2) ≤ 4
    split
    · split <;> omega_using []
    · omega_using []

theorem roundRun_ok (M : Mont) (K : Kernel)
    {p : WitnessParams} {rp : Addr} {used i checks : Nat} {sample : Option Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (hroom : RoundRoom p rp bs s)
    (hi : word s.mem p.O (8 * oIndex) = BitVec.ofNat 64 i)
    (hc : word s.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks)
    (hi32 : i < 2 ^ 31) (hc32 : checks < 2 ^ 31)
    (hsample : match sample with
      | none => word s.mem p.O (8 * oStatus) = 0
      | some a => word s.mem p.O (8 * oStatus) = 1 ∧ wv s.mem p.I (slot p.w aXm) p.w = a) :
    WP isa (roundRun M.mm K.run) s fun t => DrawState p rp used bs t ∧
      word t.mem p.O (8 * oStatus) = BitVec.ofNat 64 (runStatus p i checks sample) ∧
      word t.mem p.O (8 * oIndex) = BitVec.ofNat 64 (runIndex p i sample) ∧
      RoundSaved p s.mem t.mem ∧ RoundFrame p (s.gpr .rsp) s.mem t.mem ∧ Keep mmRegs s t := by
  have houter : Scr s p.O 256 := by
    simpa [off] using h.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  unfold roundRun
  cases sample with
  | none =>
    refine WP.seq (WP.mono (statusTest_ok h.ready.good.scr p.space_bounds.2.1 houter h.ready.good.rdi
      h.link hsample (by decide : 0 < 2 ^ 64)) fun u ⟨hz, hm, k⟩ => ?_)
    have hu := h.same_mem hm k ((k.gpr (by decide)).trans h.ready.good.rdi)
    refine WP.ite true (by simp only [eval, hz, decide_true]) (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨hu, ?_, ?_, ?_, ?_, k.mono (by decide)⟩
    · rw [hm]; exact hsample
    · rw [hm]; exact hi
    · rw [hm]; exact RoundSaved.refl _ _
    · rw [hm]; exact RoundFrame.refl _ _ _
  | some a =>
    refine WP.seq (WP.mono (statusTest_ok h.ready.good.scr p.space_bounds.2.1 houter h.ready.good.rdi
      h.link hsample.1 (by decide : 1 < 2 ^ 64)) fun u ⟨hz, hm, k⟩ => ?_)
    have hu := h.same_mem hm k ((k.gpr (by decide)).trans h.ready.good.rdi)
    have hsp : u.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
    refine WP.ite false (by simp only [eval, hz, show ¬(1 : Nat) = 0 by decide, decide_false]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (witnessRound_state_ok M K (a := a) hu (hroom.congr hsp)
      (by rw [hm]; exact hsample.2)) fun v ⟨hv, hflag, hh, hf, kv⟩ => ?_)
    have hiv : word v.mem p.O (8 * oIndex) = BitVec.ofNat 64 i := by
      rw [hh _ (by decide), hm]; exact hi
    have hcv : word v.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks := by
      rw [hh _ (by decide), hm]; exact hc
    refine WP.mono (roundResult_ok hv hflag hiv hcv hi32 hc32) fun t ⟨ht, hstatus, hindex, hsaved, hframe, kt⟩ => ?_
    refine ⟨ht, hstatus, hindex, ?_, ?_, ((k.trans kv).trans kt).mono (by decide)⟩
    · intro j hj h12 h13 h14 h18 h19
      rw [hsaved j hj h12 h13 h14 h18 h19, hh j hj, hm]
    · simpa only [hm, hsp] using hf.trans hframe.round

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: one complete uniform primality round -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

def RoundStep (p : WitnessParams) (rp : Addr) (used : Nat) (bs : List Byte) (i checks : Nat) (s t : State) : Prop :=
  let sample := (Spec.Ffdh.drawWitness p.N bs).map Prod.fst
  ∃ n, n ≤ bs.length ∧ DrawState p (off rp n) (used + n) (bs.drop n) t ∧
    word t.mem p.O (8 * oStatus) = BitVec.ofNat 64 (runStatus p i checks sample) ∧
    word t.mem p.O (8 * oIndex) = BitVec.ofNat 64 (runIndex p i sample) ∧
    (∀ a rest, Spec.Ffdh.drawWitness p.N bs = some (a, rest) → rest = bs.drop n) ∧
    t.zf = some (decide (runStatus p i checks sample = 4)) ∧
    RoundSaved p s.mem t.mem ∧ RoundFrame p (s.gpr .rsp) s.mem t.mem ∧ Keep mmRegs s t

theorem roundBody_ok (M : Mont) (K : Kernel)
    {p : WitnessParams} {rp : Addr} {used i checks : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (hroom : RoundRoom p rp bs s)
    (hi : word s.mem p.O (8 * oIndex) = BitVec.ofNat 64 i)
    (hc : word s.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks)
    (hi32 : i < 2 ^ 31) (hc32 : checks < 2 ^ 31) :
    WP isa (roundBody M.mm K.run) s (RoundStep p rp used bs i checks s) := by
  unfold roundBody
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (drawWitness_ok h) fun u ⟨n, hn, hu, hres, _, hs, hf, k⟩ => ?_)
  let sample := (Spec.Ffdh.drawWitness p.N bs).map Prod.fst
  have hsample : match sample with
      | none => word u.mem p.O (8 * oStatus) = 0
      | some a => word u.mem p.O (8 * oStatus) = 1 ∧ wv u.mem p.I (slot p.w aXm) p.w = a := by
    cases he : Spec.Ffdh.drawWitness p.N bs with
    | none => simpa only [sample, he, Option.map_none] using hres
    | some ar =>
      obtain ⟨a, rest⟩ := ar
      rw [he] at hres
      simp only [sample, he, Option.map_some]
      exact ⟨hres.1, hres.2.2⟩
  have hrest : ∀ a rest, Spec.Ffdh.drawWitness p.N bs = some (a, rest) → rest = bs.drop n := by
    intro a rest he
    rw [he] at hres
    exact hres.2.1
  have hiu : word u.mem p.O (8 * oIndex) = BitVec.ofNat 64 i :=
    (hs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi
  have hcu : word u.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks :=
    (hs _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc
  have hsp : u.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine WP.seq (WP.mono (roundRun_ok M K hu (hroom.after_draw k (by decide) n) hiu hcu hi32 hc32 hsample)
    fun v ⟨hv, hstatus, hindex, hs', hf', kv⟩ => ?_)
  have houter : Scr v p.O 256 := by
    simpa [off] using hv.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  refine WP.mono (statusMore_ok hv.ready.good.scr p.space_bounds.2.1 houter hv.ready.good.rdi hv.link hstatus
    (by omega_using [runStatus_bound p i checks sample])) fun t ⟨hz, hm, kt⟩ => ?_
  refine ⟨n, hn, hv.same_mem hm kt ((kt.gpr (by decide)).trans hv.ready.good.rdi), ?_, ?_, hrest, hz,
    ?_, ?_, ((k.trans kv).trans kt).mono (by decide)⟩
  · rw [hm]; exact hstatus
  · rw [hm]; exact hindex
  · rw [hm]; exact hs.round.trans hs'
  · rw [hm]
    rw [hsp] at hf'
    exact hf.round.trans hf'

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! ### `Ffdh.X86_64.ParameterCandidate.PrepareState`, which the modules that import this one used -/

section

/-! # FFDH parameter generation on x86-64: prepare the shared primality modulus -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem CandidateBase.modulus_ranges {p : CandidateP} {s : State} (h : CandidateBase p s) (q : Bool) :
    ∀ r ∈ modulusRanges (p.phaseWords q),
      r.1 + r.2 ≤ p.Z - 256 ∧ (136 ≤ r.1 ∨ r.1 + r.2 ≤ 128) := by
  intro r hr
  simp only [modulusRanges, prepareRanges, constantRanges, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  have hz := (h.phase_dims q).z
  have hx := (h.phase_dims q).x
  rcases hr with (((rfl | rfl) | hr) | (rfl | rfl | rfl | rfl | rfl)) | rfl
  · constructor
    · change 64 ≤ p.Z - 256
      unfold slot hdrBytes at hz; omega_using [hz]
    · right; decide
  · constructor
    · have hs := slot_le (w := p.phaseWords q) (show aOne < 8 by decide)
      omega_using [hs, hz]
    · left; unfold slot hdrBytes; omega_using []
  · refine ⟨Nat.le_trans (r2Ranges_le _ r hr) hz, Or.inl ?_⟩
    simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [slot, hdrBytes, aAcc, aTmp, aR2, sCnt, sFn] <;> omega_using []
  all_goals refine ⟨?_, Or.inl (by simp only [slot, hdrBytes]; omega_using [])⟩
  all_goals
    simp only [slot, hdrBytes, aAcc, aTmp, aY, aR1, aRm1, aE] at hz hx ⊢
    omega_using [hz, hx]

theorem prepareModulus_state_ok (M : Mont) (R : R2Impl M)
    {p : CandidateP} {used : Nat} {q : Bool} {c : Checks} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s)
    (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi)
    (hp : PhaseHeader p q c s)
    (hn : wv s.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q)
    (ho : p.phaseValue q % 2 = 1) :
    WP isa (prepareModulus M.mm R.code) s fun t => ∃ mi', CandidateTape p used t ∧
      ModulusReady t (off p.B 256) (p.Z - 256) (p.phaseWords q) mi' (p.phaseValue q) ∧
      PhaseHeader p q c t ∧ CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (prepareModulus_ok M R hg (h.base.phase_dims q) hn ho
    (by omega_using [h.base.phase_large q]) (h.base.phase_wordshape q).1)
    fun t ⟨mi', ht, hf, k⟩ => ?_
  have hrs := fun r hr => (h.base.modulus_ranges q r hr).1
  exact ⟨mi', h.keep_inner hf hrs k (by decide), ht,
    hp.of_inner h.base hf hrs (fun r hr => (h.base.modulus_ranges q r hr).2),
    fun j hj => h.base.inner_header hf hrs j (by omega_using [hj]),
    CandidateFrame.of_scr (h.base.inner_changes hf hrs), k⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! ### `Ffdh.X86_64.ParameterCandidate.Rounds`, which the modules that import this one used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.RoundLoop`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: the uniform Miller–Rabin policy loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

def RoundsPost (p : WitnessParams) (rp : Addr) (used : Nat) (bs : List Byte) (n : Nat) (s t : State) : Prop :=
  ∃ consumed, consumed ≤ bs.length ∧ DrawState p (off rp consumed) (used + consumed) (bs.drop consumed) t ∧
    (match checkWitnesses p.N n bs with
      | none => word t.mem p.O (8 * oStatus) = 0
      | some (pass, rest) => word t.mem p.O (8 * oStatus) = BitVec.ofNat 64 (if pass then 1 else 2) ∧
          rest = bs.drop consumed) ∧
    RoundSaved p s.mem t.mem ∧ RoundFrame p (s.gpr .rsp) s.mem t.mem ∧ Keep mmRegs s t

/-- The counter advances only on accepted passing witnesses, and the first
composite witness or exhausted tape terminates the policy immediately. -/
theorem roundsLoop_ok (M : Mont) (K : Kernel)
    {p : WitnessParams} {rp : Addr} {used i checks n : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (hroom : RoundRoom p rp bs s)
    (hi : word s.mem p.O (8 * oIndex) = BitVec.ofNat 64 i)
    (hc : word s.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks)
    (hpos : 0 < n) (hcount : i + n = checks) (hc32 : checks < 2 ^ 31) :
    WP isa (.loop (roundBody M.mm K.run) .e) s (RoundsPost p rp used bs n s) := by
  induction n generalizing i rp used bs s with
  | zero => omega
  | succ n ih =>
    obtain ⟨trace, u, he, consumed, hcons, hu, hstatus, hindex, hrest, hz, hs, hf, k⟩ :=
      roundBody_ok M K h hroom hi hc (by omega_using [hcount, hc32]) hc32
    have hcu : word u.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks :=
      (hs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc
    cases hdraw : Spec.Ffdh.drawWitness p.N bs with
    | none =>
      simp only [hdraw, Option.map_none, runStatus, runIndex] at hstatus hindex hz
      have hz' : isa.eval .e u = some false := by simpa [eval] using hz
      refine ⟨_, u, Exec.loopExit he hz', consumed, hcons, hu, ?_, hs, hf, k⟩
      simpa [checkWitnesses, hdraw] using hstatus
    | some ar =>
      obtain ⟨a, rest⟩ := ar
      have htail := hrest a rest hdraw
      simp only [hdraw, Option.map_some, runStatus, runIndex] at hstatus hindex hz
      by_cases hm : Spec.Ffdh.mrRound p.N a = true
      · simp only [hm, ↓reduceIte] at hstatus hindex hz
        by_cases hn : 0 < n
        · have hmore : i + 1 < checks := by omega_using [hcount, hn]
          have hstatus4 : passStatus i checks = 4 := by simp only [passStatus, ite_eq_left hmore]
          have hz' : isa.eval .e u = some true := by
            simpa only [eval, hstatus4, decide_true] using hz
          obtain ⟨trace', t, he', consumed', hcons', ht, hr, hs', hf', k'⟩ :=
            ih hu (hroom.after_draw k (by decide) consumed) hindex hcu hn (by omega_using [hcount])
          have hsp : u.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
          rw [hsp] at hf'
          refine ⟨_, t, Exec.loopNext he hz' he', consumed + consumed', ?_, ?_, ?_, hs.trans hs', hf.trans hf',
            (k.trans k').mono (by decide)⟩
          · rw [List.length_drop] at hcons'
            omega_using [hcons, hcons']
          · simpa only [off_off, Nat.add_assoc, List.drop_drop] using ht
          · have hcheck : checkWitnesses p.N (n + 1) bs = checkWitnesses p.N n (bs.drop consumed) := by
              simp [checkWitnesses, hdraw, hm, htail]
            rw [hcheck]
            simpa only [List.drop_drop] using hr
        · have hn0 : n = 0 := by omega_using [hn]
          subst hn0
          have hlast : ¬i + 1 < checks := by omega_using [hcount]
          have hstatus1 : passStatus i checks = 1 := by simp only [passStatus, ite_eq_right hlast]
          have hz' : isa.eval .e u = some false := by simpa [eval, hstatus1] using hz
          refine ⟨_, u, Exec.loopExit he hz', consumed, hcons, hu, ?_, hs, hf, k⟩
          have hcheck : checkWitnesses p.N 1 bs = some (true, rest) := by simp [checkWitnesses, hdraw, hm]
          rw [hcheck]
          exact ⟨by simpa only [hstatus1, ite_true] using hstatus, htail⟩
      · have hmf : Spec.Ffdh.mrRound p.N a = false := Bool.eq_false_iff.mpr hm
        simp only [hmf, Bool.false_eq_true, ↓reduceIte] at hstatus hindex hz
        have hz' : isa.eval .e u = some false := by simpa [eval] using hz
        refine ⟨_, u, Exec.loopExit he hz', consumed, hcons, hu, ?_, hs, hf, k⟩
        have hcheck : checkWitnesses p.N (n + 1) bs = some (false, rest) := by simp [checkWitnesses, hdraw, hmf]
        rw [hcheck]
        exact ⟨hstatus, htail⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end


/-! # FFDH parameter generation on x86-64: the complete uniform primality policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64 (hdr)
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

theorem roundInit_ok {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) :
    WP isa (.block roundInit) s fun t => t.mem = s.mem.writeW (off p.O (8 * oIndex)) (0#64) ∧
      Keep [.rax, .rcx] s t := by
  have houter : Scr s p.O 256 := by
    simpa [off] using h.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = s.mem.writeW (off p.O (8 * oIndex)) (0#64))
    ?_ rfl) fun t ⟨hm, k⟩ => ⟨hm, k⟩
  xrun [roundInit, State.ea, hdr, h.ready.good.rdi, hdrOff, ws, h.link,
    h.ready.good.scr.ld (d := 8 * sLink) p.space_bounds.2.1, houter.st (d := 8 * oIndex) (by decide)]
  rfl

theorem rounds_ok (M : Mont) (K : Kernel)
    {p : WitnessParams} {rp : Addr} {used checks : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (hroom : RoundRoom p rp bs s)
    (hc : word s.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks)
    (hpos : 0 < checks) (hc32 : checks < 2 ^ 31) :
    WP isa (rounds M.mm K.run) s (RoundsPost p rp used bs checks s) := by
  unfold rounds
  refine WP.seq (WP.mono (roundInit_ok h) fun u ⟨hm, k⟩ => ?_)
  have hf : Frm p.O [(8 * oIndex, 8)] s.mem u.mem := by
    rw [hm]
    exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
  have hlo : ∀ r ∈ [(8 * oIndex, 8)], 136 ≤ r.1 := by simp [oIndex]
  have hhi : ∀ r ∈ [(8 * oIndex, 8)], r.1 + r.2 ≤ 256 := by simp [oIndex]
  have hu := h.outer_frame hf hlo hhi k ((k.gpr (by decide)).trans h.ready.good.rdi)
  have hi : word u.mem p.O (8 * oIndex) = BitVec.ofNat 64 0 := by
    rw [hm]; exact word_writeW_self _ _ _ _
  have hcu : word u.mem p.O (8 * oChecks) = BitVec.ofNat 64 checks := by
    rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
    exact hc
  have hsp : u.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have hs : RoundSaved p s.mem u.mem := by
    intro j hj _ _ _ h18 _
    rw [hm]
    exact hdrStore_hdr _ _ _ (by decide) hj (Ne.symm h18)
  have hfr : RoundFrame p (s.gpr .rsp) s.mem u.mem :=
    (DrawFrame.of_scr (InScr.of_frm hf (fun r hr => Nat.le_trans (hhi r hr) p.space_bounds.1))).round
  refine WP.mono (roundsLoop_ok M K hu (hroom.congr hsp) hi hcu hpos (by omega_using []) hc32)
    fun t ⟨consumed, hcons, ht, hr, hs', hf', kt⟩ => ?_
  rw [hsp] at hf'
  exact ⟨consumed, hcons, ht, hr, hs.trans hs', hfr.trans hf', (k.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: instantiate the shared witness policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.Ffdh.X86_64

def CandidateBase.witnessParams {p : CandidateP} {s : State} (h : CandidateBase p s)
    (q : Bool) (mi : BitVec 64) (ho : p.phaseValue q % 2 = 1) : WitnessParams where
  O := p.B
  Z := p.Z
  op := p.op
  bits := p.phaseBits q
  w := p.phaseWords q
  N := p.phaseValue q
  mi := mi
  bits1 := by cases q <;> simp only [CandidateP.phaseBits] <;> simp <;> omega_using [h.bits1]
  bits2 := by cases q <;> simp only [CandidateP.phaseBits] <;> simp <;> omega_using [h.bits2]
  width := rfl
  room := (h.phase_room q).2.2
  predBits := (h.phase_bitLength q ho).2
  odd := ho
  n3 := by omega_using [h.phase_large q]

theorem CandidateTape.drawState {p : CandidateP} {used : Nat} {q : Bool} {c : Checks} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s) (hp : PhaseHeader p q c s) (ho : p.phaseValue q % 2 = 1)
    (hr : ModulusReady s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi (p.phaseValue q)) :
    DrawState (h.base.witnessParams q mi ho) (off p.rp used) used (p.rand.drop used) s := by
  refine ⟨h.base.scr, hr, hp.link,
    h.base.hdr (oOut, p.op) (by simp [CandidateP.headers]), hp.bits, hp.len,
    h.ptr, ?_, h.usedWord, ?_, source_drop h.base.rand used, ?_, ?_⟩
  · change word s.mem p.B (8 * oRandLeft) = BitVec.ofNat 64 (p.rand.drop used).length
    simpa only [List.length_drop] using h.left
  · simp only [List.length_drop]
    omega_using [h.bound, h.base.randLen]
  · exact ⟨fun i hi => h.base.out.wr i (Nat.lt_of_lt_of_le hi (h.base.phase_load_widths q).2.2),
      fun i hi => h.base.out.sep i (Nat.lt_of_lt_of_le hi (h.base.phase_load_widths q).2.2)⟩
  · intro i hi j hj he
    have hij : i < p.k := Nat.lt_of_lt_of_le hi (h.base.phase_load_widths q).2.2
    change off p.op i = off (off p.rp used) j at he
    rw [off_off] at he
    exact h.base.outRand i hij (used + j) (by rw [List.length_drop] at hj; omega_using [hj]) he

theorem CandidateTape.roundRoom {p : CandidateP} {used : Nat} {q : Bool} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s) (ho : p.phaseValue q % 2 = 1) :
    RoundRoom (h.base.witnessParams q mi ho) (off p.rp used) (p.rand.drop used) s := by
  refine ⟨by rw [h.base.sp]; exact h.base.stackSize, by rw [h.base.sp]; exact h.base.stackRoot, ?_⟩
  intro i hi
  rw [h.base.sp, off_off]
  exact h.base.stackRand (used + i) (by rw [List.length_drop] at hi; omega_using [hi])

end VG.Proof.Ffdh.X86_64.ParameterCandidate
