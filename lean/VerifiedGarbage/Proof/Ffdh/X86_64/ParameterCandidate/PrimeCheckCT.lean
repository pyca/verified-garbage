module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LinkCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckPrime
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.StageCTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Sieve
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckPrime
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of either modulus's sieve -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64
open VG.Impl.Bignum.X86_64.Public VG.Impl.RsaKeyGen.X86_64.Candidate

theorem PhaseLoaded.header {q : Bool} {c : Checks} {d : CandidatePublic} {s : State} (h : PhaseLoaded q c d s) :
    InnerHeader (d.inner q) s := by
  obtain ⟨_, hg, _, _⟩ := h.2
  exact ⟨h.1.2.2, good_hp hg h.1.2.1⟩

def OddChecked (q : Bool) (c : Checks) (d : CandidatePublic) (s : State) : Prop :=
  PhaseLoaded q c d s ∧ s.zf = some (decide (d.p.phaseValue q % 2 = 1))

private theorem odd_checked (q : Bool) (c : Checks) (d : CandidatePublic) (s : State) (h : PhaseLoaded q c d s) :
    WP isa (.block oddTest) s (OddChecked q c d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.2
  refine WP.mono (oddTest_ok hg (h.1.1.base.phase_dims q).z
    (by omega_using [(h.1.1.base.phase_room q).1])) fun t ⟨hz, hm, k⟩ => ?_
  have ht := (h.1.1.same_mem hm k (by decide)).1
  have hgt : Good t (off d.p.B 256) (d.p.Z - 256) (d.p.phaseWords q) mi :=
    ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  exact ⟨⟨⟨ht, k.2.2.trans h.1.2.1, h.1.2.2⟩, mi, hgt,
    ⟨by rw [hm]; exact hp.bits, by rw [hm]; exact hp.len,
      by rw [hm]; exact hp.checks, by rw [hm]; exact hp.link⟩,
    by rw [hm]; exact hn⟩, by simpa only [hn] using hz⟩

theorem PhaseLoaded.link {q : Bool} {c : Checks} {d : CandidatePublic} {s : State} (h : PhaseLoaded q c d s) :
    LinkHeader ⟨d.p.B, d.wr⟩ s := by
  obtain ⟨_, hg, hp, _⟩ := h.2
  exact ⟨h.1.2.2, hg.rdi, h.1.2.1, fun e he => by
    simp only [List.mem_singleton] at he; subst e; exact hp.link⟩

/-- The sieve's state: the phase, and the requested width in RDX. -/
def SieveIn (q : Bool) (c : Checks) (d : CandidatePublic) (s : State) : Prop :=
  PhaseLoaded q c d s ∧ s.gpr .rdx = BitVec.ofNat 64 d.p.bits

/-- The requested width, for the sieve's count, through the link. -/
private theorem bits_header (q : Bool) (c : Checks) (d : CandidatePublic) (s : State) (h : PhaseLoaded q c d s) :
    WP isa (.block sieveBits) s (SieveIn q c d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.2
  have hb := h.1.1.base
  have hbits := hb.hdr (oBits, BitVec.ofNat 64 d.p.bits) (by simp [CandidateP.headers])
  have hrd := hb.scr.ld (show 8 * oBits + 8 ≤ d.p.Z by change 80 ≤ d.p.Z; omega_using [hb.header_room])
  have hlinkrd := hg.scr.ld (show 8 * VG.Impl.Rsa.X86_64.Crt.sLink + 8 ≤ d.p.Z - 256 by
    have hz := (hb.phase_dims q).z
    change 136 ≤ d.p.Z - 256; unfold slot VG.Impl.Bignum.hdrBytes at hz; omega)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rdx = BitVec.ofNat 64 d.p.bits ∧ t.mem = s.mem)
    (by xrun [sieveBits, State.ea, VG.Impl.Bignum.X86_64.hdr, VG.Impl.Rsa.X86_64.Crt.ws, hdrOff, hg.rdi,
      hp.link, hbits, hrd, hlinkrd]) rfl)
    fun t ⟨⟨hdx, hm⟩, k⟩ => ?_
  have ht := (h.1.1.same_mem hm k (by decide)).1
  have hgt : Good t (off d.p.B 256) (d.p.Z - 256) (d.p.phaseWords q) mi :=
    ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  exact ⟨⟨⟨ht, k.2.2.trans h.1.2.1, h.1.2.2⟩, mi, hgt,
    ⟨by rw [hm]; exact hp.bits, by rw [hm]; exact hp.len,
      by rw [hm]; exact hp.checks, by rw [hm]; exact hp.link⟩, by rw [hm]; exact hn⟩, hdx⟩

/-! ## The sieve, which stops at the candidate's first divisor

The candidate is the tape's, which the contract makes public, so both runs
divide by the same number of the table's words (`firstHit`). -/

/-- The sizes the sieve's lemmas need, for phase `q`. -/
def SieveRoom (q : Bool) (d : CandidatePublic) : Prop :=
  slot (d.p.phaseWords q) 8 ≤ d.p.Z - 256 ∧ slot (d.p.phaseWords q) aTab + 2048 ≤ d.p.Z - 256 ∧
    1 ≤ d.p.phaseWords q ∧ d.p.phaseWords q < 2 ^ 31 ∧ d.p.bits < 2 ^ 32

/-- The sieve's loop after `j` words of the table, for the public candidate. -/
def SieveAt (q : Bool) (d : CandidatePublic) (j : Nat) (s : State) : Prop :=
  SieveRoom q d ∧ InnerHeader (d.inner q) s ∧ s.wr = d.wr ∧ ∃ mi,
    TLInv s (off d.p.B 256) (d.p.Z - 256) (d.p.phaseWords q) (slot (d.p.phaseWords q) aTab)
      (sieveCount d.p.bits) mi j s ∧
    VG.Proof.Bignum.word s.mem (off d.p.B 256) (8 * kT2) = mask (anyPre (d.p.phaseValue q) (4 * j)) ∧
    wv s.mem (off d.p.B 256) (slot (d.p.phaseWords q) aN) (d.p.phaseWords q) = d.p.phaseValue q

/-- The words the sieve divides by. -/
noncomputable def sieveWords (q : Bool) (d : CandidatePublic) : Nat :=
  firstHit (d.p.phaseValue q) (sieveCount d.p.bits)

private theorem sieveCount_le (bits : Nat) : sieveCount bits ≤ 256 ∧ 1 ≤ sieveCount bits := by
  unfold sieveCount; split <;> omega

private theorem prefix_at (q : Bool) (c : Checks) (d : CandidatePublic) (s : State) (h : SieveIn q c d s) :
    WP isa sievePrefix s fun t => 0 < sieveWords q d ∧ SieveAt q d 0 t := by
  obtain ⟨mi, hg, _, hn⟩ := h.1.2
  have hb := h.1.1.1.base
  have room : SieveRoom q d := ⟨(hb.phase_dims q).z, hb.phase_table_room q,
    by omega_using [(hb.phase_room q).1], by omega_using [(hb.phase_room q).2.1],
    by omega_using [hb.bits2]⟩
  refine WP.mono (sievePrefix_ok hg room.1 room.2.1 room.2.2.2.1 room.2.2.2.2 h.2) fun t hS => ?_
  have hwr : t.wr = d.wr := hS.keep.2.2.trans h.1.1.2.1
  have hpos := firstHit_pos (c := d.p.phaseValue q) (sieveCount_le d.p.bits).2
  refine ⟨by unfold sieveWords; omega, room, ⟨h.1.1.2.2, good_hp hS.inv.good hwr⟩, hwr, mi, hS.inv, ?_, ?_⟩
  · rw [hS.flag, hS.c, hn]
  · rw [hS.c, hn]

private theorem word_at (q : Bool) (d : CandidatePublic) (j : Nat) (s : State) (hj : j < sieveWords q d)
    (h : SieveAt q d j s) :
    WP isa (VG.Impl.Bignum.X86_64.seqs sieveWord) s fun t =>
      isa.eval .ne t = some (decide (j + 1 < sieveWords q d)) ∧
      (j + 1 < sieveWords q d → SieveAt q d (j + 1) t) ∧
      (j + 1 = sieveWords q d → InnerHeader (d.inner q) t) := by
  obtain ⟨room, hh, hwr, mi, hI, hf, hc⟩ := h
  have hle := firstHit_le (d.p.phaseValue q) (sieveCount d.p.bits)
  have hN := sieveCount_le d.p.bits
  refine WP.mono (eeIter_ok room.1 room.2.2.1 room.2.2.2.1 room.2.1 hN.1 (by unfold sieveWords at hj; omega)
    hI (by rw [hf, hc])) fun t ⟨hz, hI', hf'⟩ => ?_
  have hz' : t.zf = some (decide (j + 1 = sieveWords q d)) := by
    rw [hz, hc]; unfold sieveWords; rw [firstHit_exit hj]
  have hwr' : t.wr = d.wr := hI'.keep.2.2.trans hwr
  have hht : InnerHeader (d.inner q) t := ⟨hh.1, good_hp hI'.good hwr'⟩
  refine ⟨?_, fun hlt => ⟨room, hht, hwr', mi, ⟨hI'.good, hI'.r13, hI'.n, hI'.tab, rfl, Frm.refl _ _ _,
    Keep.refl _ _⟩, by rw [hf', hc], by rw [hI'.c, hc]⟩, fun _ => hht⟩
  simp only [eval, hz', Option.map_some]
  congr 1
  by_cases h1 : j + 1 = sieveWords q d
  · simp [h1]
  · have : j + 1 < sieveWords q d := by omega
    simp [h1, this]

/-- The sieve takes the same time in both runs: its loop stops at the same
word of the table, the public candidate's first divisor's. -/
theorem sieve_ct (q : Bool) (c : Checks) : RelCT isa (Two (SieveIn q c)) sieve fun _ _ => True := by
  unfold sieve
  refine RelCT.seq (two_post (two_map (fun d : CandidatePublic => (d.inner q, BitVec.ofNat 64 d.p.bits))
    (fun _ _ h => ⟨h.1.header, h.2⟩) inner_sievePrefix_ct) (prefix_at q c)) ?_
  refine RelCT.seq ((two_loop (Φ := fun d j s => SieveAt q d j s) (Ψ := fun d s => InnerHeader (d.inner q) s)
    (sieveWords q) (two_map (fun p : CandidatePublic × Nat => (p.1.inner q, p.2))
      (fun _ _ h => by obtain ⟨_, hh, _, _, hI, _⟩ := h.2; exact ⟨hh, hI.r13⟩) inner_sieveWord_ct)
    (fun d j s hj h => word_at q d j s hj h)).mono (fun _ _ ⟨d, h₁, h₂⟩ => ⟨d, h₁, h₂⟩) fun _ _ h => h) ?_
  exact two_map (fun d : CandidatePublic => d.inner q) (fun _ _ h => h) inner_sieveTail_ct

theorem primeCheck_ct (q : Bool) (c : Checks) : RelCT isa (Two (PhaseLoaded q c)) primeCheck fun _ _ => True := by
  unfold primeCheck
  refine RelCT.seq (two_post
    (two_map (fun d : CandidatePublic => d.inner q) (fun _ _ h => h.header) inner_oddTest_ct)
    (odd_checked q c)) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2]) ?_
    (two_taint [] (pins_nil _) (by taint_decide))
  refine RelCT.seq (two_post
    (two_map (fun d : CandidatePublic => (⟨d.p.B, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.1.link) sieveBits_ct)
    (fun d s h => bits_header q c d s h.1.1)) ?_
  exact sieve_ct q c

def PhaseChecked (q : Bool) (c : Checks) (d : CandidatePublic) (s : State) : Prop :=
  PhaseLoaded q c d s ∧ s.zf = some (d.p.sieved (d.p.phaseValue q))

theorem prime_checked (q : Bool) (c : Checks) (d : CandidatePublic) (s : State) (h : PhaseLoaded q c d s) :
    WP isa primeCheck s (PhaseChecked q c d) := by
  obtain ⟨mi, hg, hp, hn⟩ := h.2
  exact WP.mono (primeCheck_state_ok h.1.1 hg hp hn)
    fun t ⟨ht, hgt, hpt, hnt, hz, _, _, k, _⟩ =>
      ⟨⟨⟨ht, k.2.2.trans h.1.2.1, h.1.2.2⟩, mi, hgt, hpt, hnt⟩, hz⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
