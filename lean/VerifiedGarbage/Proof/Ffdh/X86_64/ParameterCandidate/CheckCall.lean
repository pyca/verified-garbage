module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareCall
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrimeCheckCT
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Framework.X86_64.CallBody
import VerifiedGarbage.Proof.Framework.X86_64.CallInline

/-! # Shared FFDH candidate checks

The leaf checks do not use RSP. Their caller's existing stack allowance
holds the return address; the workspace-only frame preserves it.
-/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Bignum.X86_64.Public VG.Impl.MillerRabin.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate

private theorem exec_set_rsp {code : Prog isa} (hc : code.noCalls = true)
    (hi : ∀ i ∈ instrs code, i.rspFree = true) {s t : State} {trace : List Leak}
    (h : Exec isa code s trace t) (sp : Addr) :
    Exec isa code (s.setReg .rsp sp) trace (t.setReg .rsp sp) := by
  apply VG.X86_64.Exec.F (H := ⟨0, 0⟩) hc
    (fun i hm s _ => ⟨exec_setRsp (hi i hm), addrs_setRsp (hi i hm)⟩)
    (fun k s => eval_setRsp k) h
  intro r hr x hx hx0
  have hx : (x - (0 : Addr)).toNat + 1 ≤ 0 := hx0
  omega_using [hx]

private def normalized (s : State) : State := s.callEntry.setReg .rsp (s.gpr .rsp)

private theorem entry_phase {p : CandidateP} {used : Nat} {q : Bool} {c : Checks} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s) (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi)
    (hp : PhaseHeader p q c s)
    (hn : wv s.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q) :
    CandidateTape p used (normalized s) ∧
      Good (normalized s) (off p.B 256) (p.Z - 256) (p.phaseWords q) mi ∧
      PhaseHeader p q c (normalized s) ∧
      wv (normalized s).mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q := by
  have hb := h.base
  have he := call_entry_root hb
  have hi := call_entry_inner hb
  have hz := (hb.phase_dims q).z
  have hw (j : Nat) (hj : j < 32) :
      word (normalized s).mem p.B (8 * j) = word s.mem p.B (8 * j) :=
    call_root_word hb.size64 he (by omega_using [hb.header_room, hj])
  have k : Keep ([] : List Reg) s (normalized s) := by
    refine ⟨fun r _ => ?_, rfl, rfl⟩
    by_cases hr : r = .rsp
    · subst r; rfl
    · simpa only [normalized, State.setReg, ite_eq_right hr] using State.callEntry_gpr s hr
  have hf : CandidateFrame p s.mem (normalized s).mem := by
    intro a ha ho hs
    exact call_entry_frame hb a (by simpa only [List.forall_mem_singleton] using hs)
  have ht := h.keep hf (fun j hj => hw j (by omega_using [hj])) k (by exact hb.sp)
  have hg' : Good (normalized s) (off p.B 256) (p.Z - 256) (p.phaseWords q) mi :=
    Good.of_inScr hg hz hi rfl (k.gpr (by decide) |>.trans hg.rdi)
  have hp' : PhaseHeader p q c (normalized s) := by
    refine ⟨(hw _ (by decide)).trans hp.bits, (hw _ (by decide)).trans hp.len,
      (hw _ (by decide)).trans hp.checks, ?_⟩
    change word s.callEntry.mem (off p.B 256) 128 = p.B
    rw [call_root_word (Nat.le_trans (Nat.sub_le _ _) hb.size64) hi (by
      change 136 ≤ p.Z - 256
      unfold slot VG.Impl.Bignum.hdrBytes at hz; omega_using [hz])]
    exact hp.link
  refine ⟨ht, hg', hp', ?_⟩
  change wv s.callEntry.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = _
  rw [call_root_wv (Nat.le_trans (Nat.sub_le _ _) hb.size64) hi (by
    have hh := slot_le (w := p.phaseWords q) (show aN < 8 by decide)
    omega_using [hh, hz])]
  exact hn

private def CheckPost (p : CandidateP) (used : Nat) (q : Bool) (c : Checks) (mi : BitVec 64)
    (accept : Bool) (s t : State) : Prop :=
  CandidateTape p used t ∧ Good t (off p.B 256) (p.Z - 256) (p.phaseWords q) mi ∧
  PhaseHeader p q c t ∧ wv t.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q ∧
  t.zf = some accept ∧ CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧
  Keep mmRegs s t ∧ Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k

private def checkRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)]

private theorem check_call_ok (name : String) (code : Prog isa)
    (hc : code.noCalls = true) (hi : ∀ i ∈ instrs code, i.rspFree = true)
    {p : CandidateP} {used : Nat} {q : Bool} {c : Checks} {s : State} {mi : BitVec 64} (accept : Bool)
    (body_ok : ∀ {s : State}, CandidateTape p used s →
      Good s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi → PhaseHeader p q c s →
      wv s.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q →
      WP isa code s fun t => CheckPost p used q c mi accept s t ∧
        Frm (off p.B 256) (checkRanges (p.phaseWords q)) s.mem t.mem)
    (h : CandidateTape p used s) (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi)
    (hp : PhaseHeader p q c s)
    (hn : wv s.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q) :
    WP isa (.call name code) s (CheckPost p used q c mi accept s) := by
  obtain ⟨ht, hgt, hpt, hnt⟩ := entry_phase h hg hp hn
  obtain ⟨trace, t, he, ⟨hT, hG, hP, hN, hZ, hSaved, hFrame, k, hOut⟩, hf⟩ := body_ok ht hgt hpt hnt
  have hrs : ∀ r ∈ checkRanges (p.phaseWords q), r.1 + r.2 ≤ p.Z - 256 := by
    intro r hr
    simp only [checkRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.base.phase_table_room q
    all_goals
      have hd := (h.base.phase_dims q).z
      change _ ≤ p.Z - 256
      unfold slot VG.Impl.Bignum.hdrBytes at hd
      simp only [kT0, kT1, kT2, VG.Impl.Bignum.sFn]
      omega_using [hd]
  have hfroot := call_inner_frame h.base hf hrs
  have hentry : CandidateFrame p s.mem (normalized s).mem := by
    intro a ha ho hs
    exact call_entry_frame h.base a (by simpa only [List.forall_mem_singleton] using hs)
  have hsaved : CandidateSaved p s.mem (normalized s).mem := by
    intro j hj
    exact call_root_word h.base.size64 (call_entry_root h.base) (by omega_using [hj, h.base.header_room])
  have ke : Keep mmRegs s (normalized s) := by
    refine ⟨fun r _ => ?_, rfl, rfl⟩
    by_cases hr : r = .rsp
    · subst r; rfl
    · simpa only [normalized, State.setReg, ite_eq_right hr] using State.callEntry_gpr s hr
  have kt : Keep mmRegs s t := ⟨fun r hr => (k.gpr hr).trans (ke.gpr hr),
    k.2.1.trans ke.2.1, k.2.2.trans ke.2.2⟩
  have hm : t.mem.readW (s.gpr .rsp - 8) 64 = s.unknowns 0 := by
    have hm' : t.mem.readW (s.gpr .rsp - 8) 64 = s.callEntry.mem.readW (s.gpr .rsp - 8) 64 := by
      apply Mem.readW_congr
      intro i hi8
      apply hfroot
      by_contra hn
      have hs : (below p.sp 128).Contains (s.gpr .rsp - 8 + BitVec.ofNat 64 i) 1 :=
        (show (below p.sp 128).Contains (s.gpr .rsp - 8) 8 by
          rw [h.base.sp]; exact below_call _ (by decide) (by decide)).byte
            (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hi8])]; exact hi8)
      exact h.base.stackRoot _ (by change ofs p.B _ + 1 ≤ p.Z; omega_using [hn]) hs
    rw [hm', State.callEntry_mem, Mem.readW_writeW_self64]
  apply WP.callBody
  have he' := exec_set_rsp hc hi he (s.gpr .rsp - 8)
  have hin : (normalized s).setReg .rsp (s.gpr .rsp - 8) = s.callEntry := by
    rw [normalized, setReg_setReg, ← State.callEntry_rsp s, setReg_self]
  rw [hin] at he'
  refine ⟨trace, _, he', rfl, hm, ?_⟩
  have hout : (t.setReg .rsp (s.gpr .rsp - 8)).setReg .rsp (s.gpr .rsp) = t := by
    rw [setReg_setReg, ← kt.gpr (by decide), setReg_self]
  rw [hout]
  exact ⟨hT, hG, hP, hN, hZ, hsaved.trans hSaved, hentry.trans hFrame, kt,
    hOut.trans (by
      unfold Spec.Rsa.bytesAt
      apply List.map_congr_left
      intro i hi
      apply call_entry_frame h.base
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact h.base.stackOut i (List.mem_range.mp hi))⟩


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
  apply check_call_ok _ primeCheckInline (by lit_decide) (by lit_decide)
    (Spec.Ffdh.primeShape (p.phaseValue q) && !Spec.RsaKeyGen.obviouslyComposite p.bits (p.phaseValue q)) ?_ h hg hp hn
  intro s h hg hp hn
  simpa only [CheckPost, checkRanges, and_assoc] using primeCheck_state_ok_inline h hg hp hn

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
  apply check_call_ok _ earlyCheckInline (by lit_decide) (by lit_decide)
    (earlyOk (p.phaseValue q)) ?_ h hg hp hn
  intro s h hg hp hn
  simpa only [CheckPost, checkRanges, and_assoc] using earlyCheck_state_ok_inline h hg hp hn

private theorem check_call_ct (name : String) (code : Prog isa)
    (hc : code.noCalls = true) (hi : ∀ i ∈ instrs code, i.rspFree = true)
    (q : Bool) (c : Checks)
    (hct : RelCT isa (Two (PhaseLoaded q c)) code fun _ _ => True) :
    RelCT isa (Two (PhaseLoaded q c)) (.call name code) fun _ _ => True := by
  apply RelCT.callBody (R := fun s t => ∃ d : CandidatePublic,
    PhaseLoaded q c d (s.setReg .rsp d.p.sp) ∧ PhaseLoaded q c d (t.setReg .rsp d.p.sp))
  · rintro s t ts tt s' t' ⟨d, hs, ht⟩ es et
    exact hct _ _ _ _ _ _ ⟨d, hs, ht⟩ (exec_set_rsp hc hi es d.p.sp) (exec_set_rsp hc hi et d.p.sp)
  · rintro s t ⟨d, hs, ht⟩
    have hs' := entry_phase hs.1.1 hs.2.choose_spec.1 hs.2.choose_spec.2.1 hs.2.choose_spec.2.2
    have ht' := entry_phase ht.1.1 ht.2.choose_spec.1 ht.2.choose_spec.2.1 ht.2.choose_spec.2.2
    refine ⟨d, ?_, ?_⟩
    · have hn : s.callEntry.setReg .rsp d.p.sp = normalized s := by rw [← hs.1.1.base.sp]; rfl
      rw [hn]
      exact ⟨⟨hs'.1, hs.1.2.1, hs.1.2.2⟩, hs.2.choose, hs'.2⟩
    · have hn : t.callEntry.setReg .rsp d.p.sp = normalized t := by rw [← ht.1.1.base.sp]; rfl
      rw [hn]
      exact ⟨⟨ht'.1, ht.1.2.1, ht.1.2.2⟩, ht.2.choose, ht'.2⟩
  · rintro s t ⟨d, hs, ht⟩
    exact hs.1.1.base.sp.trans ht.1.1.base.sp.symm

theorem primeCheck_ct (q : Bool) (c : Checks) : RelCT isa (Two (PhaseLoaded q c)) primeCheck fun _ _ => True :=
  check_call_ct _ primeCheckInline (by lit_decide) (by lit_decide) q c (primeCheck_ct_inline q c)

theorem earlyCheck_ct (q : Bool) (c : Checks) : RelCT isa (Two (PhaseLoaded q c)) earlyCheck fun _ _ => True :=
  check_call_ct _ earlyCheckInline (by lit_decide) (by lit_decide) q c (earlyCheck_ct_inline q c)

theorem prime_checked (q : Bool) (c : Checks) (d : CandidatePublic) (s : State) (h : PhaseLoaded q c d s) :
    WP isa primeCheck s (PhaseChecked q c d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.2
  exact WP.mono (primeCheck_state_ok h.1.1 hg hp hn)
    fun t ⟨ht, hgt, hpt, hnt, hz, _, _, k, _⟩ =>
      ⟨⟨⟨ht, k.2.2.trans h.1.2.1, h.1.2.2⟩, mi, hgt, hpt, hnt⟩, hz⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
