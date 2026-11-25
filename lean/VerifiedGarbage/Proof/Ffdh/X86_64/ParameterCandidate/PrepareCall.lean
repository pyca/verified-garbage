module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseWitness
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Framework.X86_64.CallBody
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # Sharing FFDH's modulus preparation across witness phases

The return address is below the candidate's stack pointer, disjoint from
its entire workspace. Preparation preserves that slot and the existing
128-byte stack allowance includes it.
-/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public

private theorem entry_frame {p : CandidateP} {s : State} (h : CandidateBase p s) :
    Frame [below p.sp 128] s.mem s.callEntry.mem := by
  exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
    (by rw [h.sp]; exact below_call _ (by decide) (by decide))

private theorem entry_root {p : CandidateP} {s : State} (h : CandidateBase p s) :
    ∀ x, ofs p.B x < p.Z → s.callEntry.mem x = s.mem x := by
  intro x hx
  exact entry_frame h x (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact h.stackRoot x (by change ofs p.B x + 1 ≤ p.Z; omega_using [hx]))

private theorem root_word {B : Addr} {Z d : Nat} {m m' : Mem}
    (hZ : Z ≤ 2 ^ 64) (he : ∀ x, ofs B x < Z → m' x = m x) (hd : d + 8 ≤ Z) :
    word m' B d = word m B d := by
  apply Mem.readW_congr
  intro i hi
  apply he
  rw [ofs_off B (d := d) (i := i) (by omega_using [hd, hZ, hi])]
  omega_using [hd, hi]

private theorem root_wv {B : Addr} {Z d w : Nat} {m m' : Mem}
    (hZ : Z ≤ 2 ^ 64) (he : ∀ x, ofs B x < Z → m' x = m x) (hd : d + 8 * w ≤ Z) :
    wv m' B d w = wv m B d w :=
  wv_congr fun i hi => root_word hZ he (by omega_using [hd, hi])

private theorem entry_inner {p : CandidateP} {s : State} (h : CandidateBase p s) :
    ∀ x, ofs (off p.B 256) x < p.Z - 256 → s.callEntry.mem x = s.mem x := by
  intro x hx
  apply entry_root h
  rcases ofs_rebase p.B x (o := 256) (by decide) with ⟨_, he⟩ | ⟨_, he⟩
  · omega_using [hx, he]
  · omega_using [hx, he, h.size64]

private theorem inner_frame {p : CandidateP} {s : State} {m m' : Mem} {rs : List (Nat × Nat)}
    (h : CandidateBase p s) (hf : Frm (off p.B 256) rs m m')
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z - 256) : InScr p.B p.Z m m' := by
  apply InScr.of_frm (hf.rebase (by decide : 256 < 2 ^ 64) (fun r hr => by
    have hb := hrs r hr
    omega_using [hb, h.size64]))
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  have hb := hrs r' hr'
  dsimp only
  omega_using [hb, h.header_room]

/-- Calling preparation preserves the candidate's tape and header, and
changes only its modulus data and the existing stack allowance. -/
theorem prepareCall_state_ok (name : String) (M : Mont) (R : R2Impl M)
    {p : CandidateP} {used : Nat} {q : Bool} {c : Checks} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s)
    (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi)
    (hp : PhaseHeader p q c s)
    (hn : wv s.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q)
    (ho : p.phaseValue q % 2 = 1) :
    WP isa (.call name (prepareModulus M.mm R.code)) s fun t => ∃ mi', CandidateTape p used t ∧
      ModulusReady t (off p.B 256) (p.Z - 256) (p.phaseWords q) mi' (p.phaseValue q) ∧
      PhaseHeader p q c t ∧ CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  have hd := h.base.phase_dims q
  have hz : slot (p.phaseWords q) 8 ≤ p.Z - 256 := hd.z
  have hi := entry_inner h.base
  have he := entry_root h.base
  have hw (d : Nat) (hd : d + 8 ≤ p.Z) := root_word h.base.size64 he hd
  have hg' := Good.of_inScr hg hz hi rfl (by rw [State.callEntry_gpr _ (by decide)]; exact hg.rdi)
  have hn' : wv s.callEntry.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q := by
    rw [root_wv (Nat.le_trans (Nat.sub_le _ _) h.base.size64) hi (by
      have hh := slot_le (w := p.phaseWords q) (show aN < 8 by decide)
      omega_using [hh, hz])]
    exact hn
  apply WP.callBody
  refine WP.mono (prepareModulus_ok M R hg' hd hn' ho
    (by omega_using [h.base.phase_large q]) (h.base.phase_wordshape q).1)
    fun u ⟨mi', hu, hf, ku⟩ => ?_
  have hrs := fun r hr => (h.base.modulus_ranges q r hr).1
  have hfroot := inner_frame h.base hf hrs
  have hh : ∀ j < 32, word u.mem p.B (8 * j) = word s.mem p.B (8 * j) := by
    intro j hj
    rw [hf.word_below hrs (by omega_using [h.base.header_room, h.base.size64]) (by decide) (by omega_using [hj])]
    exact hw _ (by omega_using [hj, h.base.header_room])
  let t := u.setReg .rsp (s.gpr .rsp)
  have kt : Keep mmRegs s t := by
    refine ⟨fun r hr => ?_, ku.2.1, ku.2.2⟩
    by_cases hrsp : r = .rsp
    · subst r; simp [t, State.setReg]
    · rw [show t.gpr r = u.gpr r by simp [t, State.setReg, hrsp], ku.gpr hr, State.callEntry_gpr _ hrsp]
  have hfr : CandidateFrame p s.mem t.mem := by
    intro a ha hout hstack
    exact (hfroot a ha).trans (entry_frame h.base a (by simpa only [List.forall_mem_singleton] using hstack))
  have ht := h.keep hfr (fun j hj => hh j (by omega_using [hj])) kt
    (by simp [t, State.setReg, h.base.sp])
  have hu' : ModulusReady t (off p.B 256) (p.Z - 256) (p.phaseWords q) mi' (p.phaseValue q) := by
    refine ⟨⟨hu.good.scr.congr rfl, ?_, hu.good.hdr⟩, hu.inv, hu.n, hu.one, hu.r2, hu.r1, hu.rm1, hu.exponent⟩
    simpa [t, State.setReg] using hu.good.rdi
  have hp' : PhaseHeader p q c t := by
    refine ⟨(hh _ (by decide)).trans hp.bits, (hh _ (by decide)).trans hp.len,
      (hh _ (by decide)).trans hp.checks, ?_⟩
    change word u.mem (off p.B 256) (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.B
    rw [hf.word_eq (d := 8 * VG.Impl.Rsa.X86_64.Crt.sLink)
      (fun r hr => (h.base.modulus_ranges q r hr).2) (by decide)]
    have hl : word s.callEntry.mem (off p.B 256) (8 * VG.Impl.Rsa.X86_64.Crt.sLink) =
        word s.mem (off p.B 256) (8 * VG.Impl.Rsa.X86_64.Crt.sLink) :=
      root_word (Nat.le_trans (Nat.sub_le _ _) h.base.size64) hi (by
        change 136 ≤ p.Z - 256
        have hh := hdr_lt_slot (p.phaseWords q) 8 (i := 31) (by decide)
        omega_using [hz, hh])
    exact hl.trans hp.link
  refine ⟨(ku.gpr (by decide)).trans (State.callEntry_rsp s), ?_, mi', ht, hu', hp',
    fun j hj => hh j (by omega_using [hj]), hfr, kt⟩
  have hfout : u.mem.readW (s.gpr .rsp - 8) 64 = s.callEntry.mem.readW (s.gpr .rsp - 8) 64 := by
    apply Mem.readW_congr
    intro i hi8
    apply hfroot
    by_contra hn
    have hs : (below p.sp 128).Contains (s.gpr .rsp - 8 + BitVec.ofNat 64 i) 1 :=
      (show (below p.sp 128).Contains (s.gpr .rsp - 8) 8 by
        rw [h.base.sp]; exact below_call _ (by decide) (by decide)).byte
          (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hi8])]; exact hi8)
    exact h.base.stackRoot _ (by change ofs p.B _ + 1 ≤ p.Z; omega_using [hn]) hs
  rw [hfout, State.callEntry_mem, Mem.readW_writeW_self64]

def PhasePrime (q : Bool) (c : Checks) (d : CandidatePublic) (s : State) : Prop :=
  PhaseLoaded q c d s ∧ d.p.phaseValue q % 2 = 1

private theorem entry_prepare {q : Bool} {c : Checks} {d : CandidatePublic} {s : State}
    (h : PhasePrime q c d s) : PrepareBefore (d.prep q) s.callEntry := by
  have hp := h.1.prepare h.2
  obtain ⟨mi, hg, hd, hz, hw, hk⟩ := hp.1
  have hi := entry_inner h.1.1.1.base
  have hz8 : slot (d.prep q).w 8 ≤ (d.prep q).IZ := hd.z
  refine ⟨⟨mi, Good.of_inScr hg hz8 hi rfl ?_, hd, hz, hw, hk⟩, ?_, hp.2.2⟩
  · rw [State.callEntry_gpr _ (by decide)]; exact hg.rdi
  · change wv s.callEntry.mem (off d.p.B 256) (slot (d.p.phaseWords q) aN) (d.p.phaseWords q) = d.p.phaseValue q
    change slot (d.p.phaseWords q) 8 ≤ d.p.Z - 256 at hz8
    rw [root_wv (Nat.le_trans (Nat.sub_le _ _) h.1.1.1.base.size64) hi (by
      have hh := slot_le (w := d.p.phaseWords q) (show aN < 8 by decide)
      omega_using [hh, hz8])]
    exact hp.2.1

theorem prepareCall_ct (name : String) (M : Mont) (R : R2Impl M) (q : Bool) (c : Checks) :
    RelCT isa (Two (PhasePrime q c)) (.call name (prepareModulus M.mm R.code)) fun _ _ => True := by
  apply RelCT.callBody (prepareModulus_ct M R)
  · rintro s t ⟨d, hs, ht⟩
    exact ⟨d.prep q, entry_prepare hs, entry_prepare ht⟩
  · rintro s t ⟨d, hs, ht⟩
    exact hs.1.1.1.base.sp.trans ht.1.1.1.base.sp.symm

/-- The modulus preparation used by all witness phases. Its contract
includes the caller's tape, headers, memory frame and timing policy. -/
structure Preparation (M : Mont) where
  code : Prog isa
  ok : ∀ {p : CandidateP} {used : Nat} {q : Bool} {c : Checks} {s : State} {mi : BitVec 64},
    CandidateTape p used s → Good s (off p.B 256) (p.Z - 256) (p.phaseWords q) mi →
    PhaseHeader p q c s →
    wv s.mem (off p.B 256) (slot (p.phaseWords q) aN) (p.phaseWords q) = p.phaseValue q →
    p.phaseValue q % 2 = 1 →
    WP isa code s fun t => ∃ mi', CandidateTape p used t ∧
      ModulusReady t (off p.B 256) (p.Z - 256) (p.phaseWords q) mi' (p.phaseValue q) ∧
      PhaseHeader p q c t ∧ CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t
  ct : ∀ q c, RelCT isa (Two (PhasePrime q c)) code fun _ _ => True

def Preparation.called (name : String) (M : Mont) (R : R2Impl M) : Preparation M where
  code := .call name (prepareModulus M.mm R.code)
  ok := prepareCall_state_ok name M R
  ct := prepareCall_ct name M R

end VG.Proof.Ffdh.X86_64.ParameterCandidate
