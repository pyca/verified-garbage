module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTMr
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Tests
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTMr
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Tests
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Shape

/-!
# An FFDH parameter candidate on PPC64LE: a test in constant time

A modulus's working space (`phase`) depends on the public bit length alone;
the loop of `topMask` counts down from a number it fixes, pinned once its
first block has computed it. p's shape loads the tape's address and length
from the header, pinned once loaded. The Montgomery set-up runs on the
working space's addresses, then the witnesses as in `millerRabin_ct`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

/-- The candidate's state, whatever the registers saved on entry. -/
def PS (q : PP) (s : State) : Prop := ∃ sv toc, St (q.with sv toc) s

theorem pins_PS : Pins PS [.r31] := by
  rintro q s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.r31, h₂.r31]; rfl

/-- After `phase b`'s head: the bit length and words in the header. -/
def PH1 (b : Bool) (q : PP) (s : State) : Prop :=
  ∃ sv toc, St (q.with sv toc) s ∧ word s.mem q.B (8 * hMb) = BitVec.ofNat 64 (mbOf q b) ∧
    word s.mem q.B (8 * hW) = BitVec.ofNat 64 (wOf (mbOf q b))

theorem pins_PH1 (b : Bool) : Pins (PH1 b) [.r31] := by
  rintro q s₁ s₂ ⟨_, _, h₁, -⟩ ⟨_, _, h₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; rw [h₁.r31, h₂.r31]; rfl

/-- After `topMask`'s first block: its count. -/
def PT (b : Bool) (q : PP) (s : State) : Prop :=
  s.gpr .r31 = q.B ∧ s.gpr .r3 = BitVec.ofNat 64 (mbOf q b + 64 - 64 * wOf (mbOf q b))

theorem pins_PT (b : Bool) : Pins (PT b) [.r3, .r31] := by
  rintro q s₁ s₂ ⟨a31, a3⟩ ⟨b31, b3⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a3, b3]
  · rw [a31, b31]

theorem phaseHead_ct (b : Bool) : RelCT isa (Two PS) (.block (phaseHead b)) fun _ _ => True := by
  cases b
  · exact two_taint _ pins_PS (by taint_decide)
  · exact two_taint _ pins_PS (by taint_decide)

theorem phase_ct (b : Bool) : RelCT isa (Two PS) (phase b) fun _ _ => True := by
  unfold phase topMask
  refine RelCT.seq (two_post (phaseHead_ct b) (Ψ := PH1 b) fun q s ⟨sv, toc, h⟩ => ?_)
    (RelCT.seq (two_post (two_taint _ (pins_PH1 b) (by taint_decide)) (Ψ := PT b)
      fun q s ⟨sv, toc, h, hm, hw⟩ => ?_) (two_taint _ (pins_PT b) (by taint_decide)))
  · exact WP.mono (phaseHead_ok h b) fun u ⟨⟨_, _, _, um, _, uw, _, _, _, uf⟩, ku⟩ =>
      ⟨sv, toc, h.step (Frm.toMut (uf.mono fun r hr => List.mem_append_left _ hr) (phRanges_mut _)) ku, um, uw⟩
  · exact WP.mono (topT1_ok h hm hw) fun u ⟨⟨u3, _, _⟩, ku⟩ => ⟨(ku.gpr .r31 (by decide)).trans h.r31, u3⟩

/-- In a modulus's working space. -/
def PA (b : Bool) (q : PP) (s : State) : Prop := ∃ sv toc, St (q.with sv toc) s ∧ Ph (q.with sv toc) (mbOf q b) s

theorem pins_PA (b : Bool) : Pins (PA b) [.r10, .r11, .r29, .r31] := by
  rintro q s₁ s₂ ⟨_, _, h₁, p₁⟩ ⟨_, _, h₂, p₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [p₁.r10, p₂.r10]; rfl
  · rw [p₁.r11, p₂.r11]
  · rw [p₁.r29, p₂.r29]
  · rw [h₁.r31, h₂.r31]; rfl

/-- After `shapeP`'s first block. -/
def SH1 (q : PP) (s : State) : Prop :=
  s.gpr .r31 = q.B ∧ s.gpr .r10 = off q.B (slot (wOf q.bits) 0) ∧ s.gpr .r11 = BitVec.ofNat 64 (2 * wOf q.bits) ∧
    s.gpr .r12 = off q.rp 0 ∧ s.gpr .r6 = BitVec.ofNat 64 q.L

theorem pins_SH1 : Pins SH1 [.r6, .r10, .r11, .r12, .r31] := by
  rintro q s₁ s₂ ⟨a31, a10, a11, a12, a6⟩ ⟨b31, b10, b11, b12, b6⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a6, b6]
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a12, b12]
  · rw [a31, b31]

theorem shapeP_ct : RelCT isa (Two (PA false)) shapeP fun _ _ => True := by
  unfold shapeP
  refine RelCT.seq (two_post (two_taint _ (pins_PA false) (by taint_decide)) (Ψ := SH1) fun q s ⟨sv, toc, h, hp⟩ =>
    WP.mono (shapeHead_ok h) fun u ⟨⟨u12, u6, _⟩, ku⟩ => ⟨(ku.gpr .r31 (by decide)).trans h.r31,
      (ku.gpr .r10 (by decide)).trans hp.r10, (ku.gpr .r11 (by decide)).trans hp.r11, u12, u6⟩)
    (two_taint _ pins_SH1 (by taint_decide))

theorem phasePA_ct (b : Bool) : RelCT isa (Two PS) (phase b) (Two (PA b)) :=
  two_post (phase_ct b) fun _ _ ⟨sv, toc, h⟩ => WP.mono (phase_ok h b) fun _ ⟨⟨ht, hp, _⟩, _⟩ => ⟨sv, toc, ht, hp⟩

/-- A test's public data, once its modulus is in place. -/
structure TD where
  q : PP
  mb : Nat
  N : Nat
  u : Nat

/-- Before a test's Montgomery set-up. -/
def TC (d : TD) (s : State) : Prop := ∃ sv toc, TCPre (d.q.with sv toc) d.mb d.N d.u s

theorem pins_TC : Pins TC [.r10, .r11, .r29, .r31] := by
  rintro d s₁ s₂ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.ph.r10, h₂.ph.r10]; rfl
  · rw [h₁.ph.r11, h₂.ph.r11]
  · rw [h₁.ph.r29, h₂.ph.r29]
  · rw [h₁.st.r31, h₂.st.r31]; rfl

/-- The witness loop's data. -/
def mrOf (d : TD) : MrD :=
  ⟨d.q, d.mb, d.N, checkWitnesses d.N (Spec.Ffdh.primeChecks d.mb) (d.q.r.drop d.u), 0, d.u⟩

theorem testCore_ct (R : RoundImpl) :
    RelCT isa (Two TC) (.seq montPrep (millerRabin R.name R.code)) (Two ME) :=
  RelCT.seq (two_post (two_taint _ pins_TC (by taint_decide)) (Ψ := fun d => MI0 (mrOf d)) fun _ _ ⟨sv, toc, h⟩ =>
      WP.mono (montPrep_mst h.st h.ph h.mb1 h.mb2 h.n h.odd h.n3) fun _ ⟨M, _, h152⟩ =>
        ⟨⟨sv, toc, M, h152.trans h.used⟩, h.ul, rfl, rfl, h.bl⟩)
    (two_map mrOf (fun _ _ h => h) (millerRabin_ct R))

/-- A test's public data: the candidate and the tape's offset. -/
structure TQD where
  q : PP
  c : Nat
  u : Nat

/-- Before q's test. -/
def TQ (d : TQD) (s : State) : Prop :=
  ∃ sv toc, St (d.q.with sv toc) s ∧ d.c = Spec.Ffdh.candidateOf d.q.bits (Spec.Rsa.os2ip (d.q.r.take d.q.L)) ∧
    wv s.mem d.q.B (slot (wOf d.q.bits) 0) (wOf d.q.bits) = (d.c - 1) / 2 ∧ ((d.c - 1) / 2) % 2 = 1 ∧
    word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧ d.u ≤ d.q.r.length

/-- q's test leaks the same from the same candidate and tape. -/
theorem testQ_ct (R : RoundImpl) : RelCT isa (Two TQ) (test true R.name R.code) (Two ME) := by
  unfold test
  simp only [↓reduceIte]
  refine RelCT.assoc (RelCT.seq (two_post ?_ (Ψ := fun d => TC ⟨d.q, d.q.bits - 1, (d.c - 1) / 2, d.u⟩)
    fun _ _ ⟨sv, toc, h, hc, hq, hqo, hu, hul⟩ => WP.mono (qPrep_ok h hc hq hqo hu hul) fun _ ht => ⟨sv, toc, ht⟩)
    (two_map _ (fun _ _ h => h) (testCore_ct R)))
  exact two_map TQD.q (fun _ _ ⟨sv, toc, h, _⟩ => ⟨sv, toc, h⟩)
    (RelCT.seq (phasePA_ct true) (two_taint _ (pins_PA true) (by taint_decide)))

/-- Before p's test. -/
def TP (d : TQD) (s : State) : Prop :=
  ∃ sv toc, St (d.q.with sv toc) s ∧ d.c = Spec.Ffdh.candidateOf d.q.bits (Spec.Rsa.os2ip (d.q.r.take d.q.L)) ∧
    word s.mem d.q.B 152 = BitVec.ofNat 64 d.u ∧ d.u ≤ d.q.r.length ∧ d.q.L ≤ d.q.r.length

/-- p's test leaks the same from the same candidate and tape. -/
theorem testP_ct (R : RoundImpl) : RelCT isa (Two TP) (test false R.name R.code) (Two ME) := by
  unfold test
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine RelCT.assoc (RelCT.seq (two_post ?_ (Ψ := fun d => TC ⟨d.q, d.q.bits, d.c, d.u⟩)
    fun _ _ ⟨sv, toc, h, hc, hu, hul, hL⟩ => WP.mono (pPrep_ok h hc hu hul hL) fun _ ht => ⟨sv, toc, ht⟩)
    (two_map _ (fun _ _ h => h) (testCore_ct R)))
  exact two_map TQD.q (fun _ _ ⟨sv, toc, h, _⟩ => ⟨sv, toc, h⟩) (RelCT.seq (phasePA_ct false) shapeP_ct)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
