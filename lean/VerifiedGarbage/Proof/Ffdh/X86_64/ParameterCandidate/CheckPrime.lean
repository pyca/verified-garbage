module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: trial division of either modulus phase -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64

/-- Includes the candidate's oddness test, so this is exactly the sieved
shape for either p or q, with the requested width read through the link. -/
theorem primeCheck_ok {s : State} {B O : Addr} {Z w bits : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hp : 8161 < wv s.mem B (slot w aN) w) (hb : bits < 2 ^ 32)
    (hlink : word s.mem B (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = O)
    (hlr : InRegions (s.rd ++ s.wr) (off B (8 * VG.Impl.Rsa.X86_64.Crt.sLink)) 8)
    (hbr : InRegions (s.rd ++ s.wr) (off O (8 * oBits)) 8)
    (hbits : word s.mem O (8 * oBits) = BitVec.ofNat 64 bits) :
    WP isa primeCheck s fun t =>
      t.zf = some (Spec.Ffdh.primeShape (wv s.mem B (slot w aN) w) &&
        !Spec.RsaKeyGen.obviouslyComposite bits (wv s.mem B (slot w aN) w)) ∧ Good t B Z w minv ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
  unfold primeCheck
  refine WP.seq (WP.mono (oddTest_ok hg hZ hw) fun u ⟨hz, hm, k⟩ => ?_)
  have hgu : Good u B Z w minv := ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    by rw [hm]; exact hg.hdr⟩
  refine WP.ite (decide (wv s.mem B (slot w aN) w % 2 = 1)) (by simp [eval, hz]) ?_ ?_
  · intro ho
    have ho' : wv s.mem B (slot w aN) w % 2 = 1 := of_decide_eq_true ho
    refine WP.seq (WP.mono (WP.keep [.rax, .rdx] (Q := fun v => v.gpr .rdx = BitVec.ofNat 64 bits ∧ v.mem = u.mem)
      (by
        have hlr' : InRegions (u.rd ++ u.wr) (off B (8 * VG.Impl.Rsa.X86_64.Crt.sLink)) 8 := by
          rw [k.2.1, k.2.2]; exact hlr
        have hbr' : InRegions (u.rd ++ u.wr) (off O (8 * oBits)) 8 := by rw [k.2.1, k.2.2]; exact hbr
        xrun [sieveBits, State.ea, hdr, VG.Impl.Rsa.X86_64.Crt.ws, hgu.rdi, hdrOff, hm, hlink, hlr', hbr', hbits])
      rfl) fun v ⟨⟨hdx, hmv⟩, kv⟩ => ?_)
    have hgv : Good v B Z w minv := ⟨hgu.scr.congr kv.2.2, (kv.gpr (by decide)).trans hgu.rdi,
      by rw [hmv]; exact hgu.hdr⟩
    have hmvs : v.mem = s.mem := hmv.trans hm
    refine WP.mono (sieve_ok hgv hZ hTZ hw hw' hb hdx) fun t ⟨hz', hg', hf, k'⟩ => ?_
    rw [hmvs] at hz' hf
    refine ⟨?_, hg', hf, ((k.trans kv).trans k').mono (by decide)⟩
    rw [hz', sieve_shape hp ho']
  · intro ho
    have ho' : ¬ wv s.mem B (slot w aN) w % 2 = 1 := of_decide_eq_false ho
    exact WP.block_nil ⟨by simpa [Spec.Ffdh.primeShape, Bool.beq_eq_decide_eq, ho', ho] using hz,
      hgu, by rw [hm]; exact Frm.refl _ _ _, k.mono (by decide)⟩

theorem primeCheck_state_ok {p : CandidateP} {used : Nat} {q : Bool} {c : Checks} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s)
    (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi)
    (hp : PhaseHeader p q c s)
    (hn : wv s.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q) :
    WP isa primeCheck s fun t => CandidateTape p used t ∧
      Good t (off p.B 256) (p.Z - 256) (p.phaseWords q) mi ∧ PhaseHeader p q c t ∧
      wv t.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q ∧
      t.zf = some (Spec.Ffdh.primeShape (p.phaseValue q) &&
        !Spec.RsaKeyGen.obviouslyComposite p.bits (p.phaseValue q)) ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t ∧
      Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k := by
  refine WP.mono (primeCheck_ok hg (h.base.phase_dims q).z (h.base.phase_table_room q)
    (by omega_using [(h.base.phase_room q).1])
    (by omega_using [(h.base.phase_room q).2.1])
    (by rw [hn]; exact h.base.phase_large q) (by omega_using [h.base.bits2]) hp.link
    (hg.scr.ld (show 8 * VG.Impl.Rsa.X86_64.Crt.sLink + 8 ≤ p.Z - 256 by
      have hz := (h.base.phase_dims q).z
      change 136 ≤ p.Z - 256
      unfold slot hdrBytes at hz
      omega))
    (h.base.scr.ld (by unfold oBits; omega_using [h.base.header_room]))
    (h.base.hdr (oBits, BitVec.ofNat 64 p.bits) (by simp [CandidateP.headers]))) fun t ⟨hz, hgt, hf, k⟩ => ?_
  have hrs : ∀ r ∈ [(slot (p.phaseWords q) aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)],
      r.1 + r.2 ≤ p.Z - 256 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.base.phase_table_room q
    all_goals
      have hd := (h.base.phase_dims q).z
      change _ ≤ p.Z - 256
      unfold slot hdrBytes at hd
      simp only [kT0, kT1, kT2, sFn]
      omega
  have hl : ∀ r ∈ [(slot (p.phaseWords q) aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)],
      136 ≤ r.1 ∨ r.1 + r.2 ≤ 128 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · left; unfold slot hdrBytes; omega
    all_goals dsimp only; decide
  have kk : Keep mmRegs s t := k.mono (by decide)
  refine ⟨h.keep_inner hf hrs kk (by decide), hgt, hp.of_inner h.base hf hrs hl,
    ?_, by simpa only [hn] using hz,
    fun j hj => h.base.inner_header hf hrs j (by omega),
    CandidateFrame.of_scr (h.base.inner_changes hf hrs), kk,
    h.base.output_eq (h.base.inner_changes hf hrs)⟩
  rw [hf.wv_eq (by rng_disj) (by
    have hz := (h.base.phase_dims q).z
    have hs := slot_le (w := p.phaseWords q) (show aN < 8 by decide)
    omega_using [hz, hs, h.base.size64])]
  exact hn

/-- What `earlyCheck` accepts: odd, and none of the table's first
`4 firstWords` entries divides it. -/
def earlyOk (v : Nat) : Bool := v % 2 == 1 && !anyPre v (4 * firstWords)

/-- The sieved shape implies `earlyOk`: `earlyCheck` rejects only what the
whole sieve rejects. -/
theorem earlyOk_of_sieved {p : CandidateP} {v : Nat} (hv : 8161 < v) (h : p.sieved v = true) :
    earlyOk v = true := by
  have ho := odd_of_sieved h
  unfold CandidateP.sieved at h
  rw [← sieve_shape hv ho] at h
  unfold earlyOk
  have hN : 4 * firstWords ≤ 4 * sieveCount p.bits := by
    unfold firstWords sieveCount; split <;> omega
  cases ha : anyPre v (4 * firstWords)
  · simp [ho]
  · rw [anyPre_mono hN ha] at h; simp at h

/-- `earlyCheck`: oddness, then the table's first words. -/
theorem earlyCheck_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa earlyCheck s fun t =>
      t.zf = some (earlyOk (wv s.mem B (slot w aN) w)) ∧ Good t B Z w minv ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
  unfold earlyCheck
  refine WP.seq (WP.mono (oddTest_ok hg hZ hw) fun u ⟨hz, hm, k⟩ => ?_)
  have hgu : Good u B Z w minv := ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    by rw [hm]; exact hg.hdr⟩
  refine WP.ite (decide (wv s.mem B (slot w aN) w % 2 = 1)) (by simp [eval, hz]) ?_ ?_
  · intro ho
    have ho' : wv s.mem B (slot w aN) w % 2 = 1 := of_decide_eq_true ho
    refine WP.mono (sieveFirst_ok hgu hZ hTZ hw hw') fun t ⟨hz', hg', hf, k'⟩ => ?_
    rw [hm] at hz' hf
    refine ⟨?_, hg', hf, (k.trans k').mono (by decide)⟩
    rw [hz']; simp [earlyOk, ho']
  · intro ho
    have ho' : ¬ wv s.mem B (slot w aN) w % 2 = 1 := of_decide_eq_false ho
    exact WP.block_nil ⟨by simpa [earlyOk, Bool.beq_eq_decide_eq, ho', ho] using hz,
      hgu, by rw [hm]; exact Frm.refl _ _ _, k.mono (by decide)⟩

theorem earlyCheck_state_ok {p : CandidateP} {used : Nat} {q : Bool} {c : Checks} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s)
    (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi)
    (hp : PhaseHeader p q c s)
    (hn : wv s.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q) :
    WP isa earlyCheck s fun t => CandidateTape p used t ∧
      Good t (off p.B 256) (p.Z - 256) (p.phaseWords q) mi ∧ PhaseHeader p q c t ∧
      wv t.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q ∧
      t.zf = some (earlyOk (p.phaseValue q)) ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t ∧
      Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k := by
  refine WP.mono (earlyCheck_ok hg (h.base.phase_dims q).z (h.base.phase_table_room q)
    (by omega_using [(h.base.phase_room q).1])
    (by omega_using [(h.base.phase_room q).2.1])) fun t ⟨hz, hgt, hf, k⟩ => ?_
  have hrs : ∀ r ∈ [(slot (p.phaseWords q) aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)],
      r.1 + r.2 ≤ p.Z - 256 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.base.phase_table_room q
    all_goals
      have hd := (h.base.phase_dims q).z
      change _ ≤ p.Z - 256
      unfold slot hdrBytes at hd
      simp only [kT0, kT1, kT2, sFn]
      omega
  have hl : ∀ r ∈ [(slot (p.phaseWords q) aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)],
      136 ≤ r.1 ∨ r.1 + r.2 ≤ 128 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · left; unfold slot hdrBytes; omega
    all_goals dsimp only; decide
  have kk : Keep mmRegs s t := k.mono (by decide)
  refine ⟨h.keep_inner hf hrs kk (by decide), hgt, hp.of_inner h.base hf hrs hl,
    ?_, by simpa only [hn] using hz,
    fun j hj => h.base.inner_header hf hrs j (by omega),
    CandidateFrame.of_scr (h.base.inner_changes hf hrs), kk,
    h.base.output_eq (h.base.inner_changes hf hrs)⟩
  rw [hf.wv_eq (by rng_disj) (by
    have hz := (h.base.phase_dims q).z
    have hs := slot_le (w := p.phaseWords q) (show aN < 8 by decide)
    omega_using [hz, hs, h.base.size64])]
  exact hn

end VG.Proof.Ffdh.X86_64.ParameterCandidate
