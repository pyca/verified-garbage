module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Residue
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseData
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Memory

/-! ### `Ffdh.X86_64.ParameterCandidate.CheckGenerator`, which the modules that import this one used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.Consume`, which the modules that import this one used -/

section

/-! # FFDH parameter generation on x86-64: consume the candidate's initial prefix -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem consumeCandidate_ok {p : CandidateP} {s : State}
    (h : CandidateTape p 0 s) (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length) :
    WP isa (.block consumeCandidate) s fun t => CandidateTape p p.k t ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep mmRegs s t ∧
      Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k := by
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hwr : ∀ j < 32, InRegions s.wr (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.st (by omega_using [hj, h.base.header_room])
  have hlen := h.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  have hptr : word s.mem p.B (8 * oRandPtr) = p.rp := by simpa [off] using h.ptr
  have hleft : word s.mem p.B (8 * oRandLeft) = BitVec.ofNat 64 p.rand.length := by simpa using h.left
  have hsub : BitVec.ofNat 64 p.rand.length - BitVec.ofNat 64 p.k = BitVec.ofNat 64 (p.rand.length - p.k) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [h.base.widths.2]) havail
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = advanceMem s.mem p.B p.rp p.k p.rand.length 0)
    (by
      xrun [consumeCandidate, advanceMem, State.ea, hdr, hdi, hdrOff, hlen, hptr, hleft,
        hrd oLen (by decide), hrd oRandPtr (by decide), hrd oRandLeft (by decide),
        hwr oRandPtr (by decide), hwr oRandLeft (by decide), hwr oUsed (by decide),
        hdrStore_hdr _ _ _ (i := oRandPtr) (k := oRandLeft) (by decide) (by decide) (by decide), hsub]
      simp only [Nat.zero_add, off]) rfl) fun t ⟨hm, k⟩ => ?_
  have hf : Frm p.B [(8 * oRandPtr, 24)] s.mem t.mem := by rw [hm]; exact advanceMem_frame _ _ _ _ _ _
  have hscr : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    change 120 ≤ p.Z
    omega_using [h.base.header_room])
  have hs : CandidateSaved p s.mem t.mem := by
    intro j hj
    exact hf.word_eq (by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      left
      change 8 * j + 8 ≤ 96
      omega_using [hj]) (by omega_using [hj])
  have hbase := h.base.keep (CandidateFrame.of_scr hscr) hs k ((k.gpr (by decide)).trans h.base.sp)
  refine ⟨⟨hbase, havail, ?_, ?_, ?_⟩, hs, CandidateFrame.of_scr hscr, k.mono (by decide), h.base.output_eq hscr⟩
  · rw [hm]; exact advanceMem_ptr _ _ _ _ _ _
  · rw [hm]; exact advanceMem_left _ _ _ _ _ _
  · rw [hm]; simpa only [Nat.zero_add] using advanceMem_used s.mem p.B p.rp p.k p.rand.length 0

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: generator policy at the p phase

The check accepts p only if, besides the generator's congruence, q =
(p − 1)/2 is odd and neither 3, 5 nor 17 divides p or q, all of which the
trial division of p and q that follows would reject: `congruent_sieved`. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

/-- What the generator check accepts: the generator's congruence (`screen`
implies it) and `screen`. -/
def CandidateP.congruent (p : CandidateP) : Bool :=
  Spec.Ffdh.generationShape p.bits p.gen p.P && screen p.gen p.P

private theorem fin2 : ∀ r < 255, r % 3 = 2 ∧ 2 ≤ r % 5 ∧ 2 ≤ r % 17 → r ∈ allowed2 := by
  decide +kernel

private theorem fin5 : ∀ r < 255, r % 3 = 2 ∧ (r % 5 = 2 ∨ r % 5 = 3) ∧ 2 ≤ r % 17 → r ∈ allowed5 := by
  decide +kernel

private theorem tab_small : VG.Impl.RsaKeyGen.tabEntry 0 = 3 ∧ VG.Impl.RsaKeyGen.tabEntry 1 = 5 ∧
    VG.Impl.RsaKeyGen.tabEntry 5 = 17 := by
  unfold VG.Impl.RsaKeyGen.tabEntry VG.Impl.RsaKeyGen.slots
  rw [VG.Impl.RsaKeyGen.primes.lit_eq]
  exact ⟨rfl, rfl, rfl⟩

private theorem small_of_primeShape {v : Nat} (hv : 8161 < v) (ho : v % 2 = 1)
    (h : Spec.Ffdh.primeShape v = true) : v % 3 ≠ 0 ∧ v % 5 ≠ 0 ∧ v % 17 ≠ 0 := by
  rw [VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve hv ho] at h
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false, List.mem_range, beq_iff_eq] at h
  obtain ⟨h3, h5, h17⟩ := tab_small
  exact ⟨by simpa only [h3] using h 0 (by decide), by simpa only [h5] using h 1 (by decide),
    by simpa only [h17] using h 5 (by decide)⟩

private theorem odd_of_primeShape {v : Nat} (h : Spec.Ffdh.primeShape v = true) : v % 2 = 1 := by
  unfold Spec.Ffdh.primeShape at h
  exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp h).1).2

/-- q = (p − 1)/2 is divisible by an odd s exactly when p ≡ 1 mod s. -/
private theorem half3 {P : Nat} (h : P % 2 = 1) (hq : (P - 1) / 2 % 3 ≠ 0) : P % 3 ≠ 1 := by omega_using [h, hq]
private theorem half5 {P : Nat} (h : P % 2 = 1) (hq : (P - 1) / 2 % 5 ≠ 0) : P % 5 ≠ 1 := by omega_using [h, hq]
private theorem half17 {P : Nat} (h : P % 2 = 1) (hq : (P - 1) / 2 % 17 ≠ 0) : P % 17 ≠ 1 := by omega_using [h, hq]
private theorem half2 {P : Nat} (h : P % 2 = 1) (hq : (P - 1) / 2 % 2 = 1) : P % 4 = 3 := by omega_using [h, hq]

/-- A candidate with the generator's congruence whose p and q have the
sieved shape passes `screen`. -/
theorem screen_of_shape {bits generator P : Nat} (hgen : generator = 2 ∨ generator = 5)
    (hodd : P % 2 = 1) (hP : 8161 < P) (hQ : 8161 < (P - 1) / 2)
    (hs : Spec.Ffdh.generationShape bits generator P = true)
    (hp : Spec.Ffdh.primeShape P = true) (hq : Spec.Ffdh.primeShape ((P - 1) / 2) = true) :
    screen generator P = true := by
  obtain ⟨p3, p5, p17⟩ := small_of_primeShape hP hodd hp
  have qodd := odd_of_primeShape hq
  obtain ⟨q3, q5, q17⟩ := small_of_primeShape hQ qodd hq
  have e3 := half3 hodd q3
  have e5 := half5 hodd q5
  have e17 := half17 hodd q17
  have e4 := half2 hodd qodd
  have hr : P % 255 < 255 := Nat.mod_lt _ (by decide)
  have m3 : P % 255 % 3 = P % 3 := Nat.mod_mod_of_dvd P (by decide)
  have m5 : P % 255 % 5 = P % 5 := Nat.mod_mod_of_dvd P (by decide)
  have m17 : P % 255 % 17 = P % 17 := Nat.mod_mod_of_dvd P (by decide)
  rcases hgen with rfl | rfl
  · have h24 : P % 24 = 11 := by
      unfold Spec.Ffdh.generationShape at hs
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ite_true] at hs
      exact hs.2
    have h8 : P % 8 = 3 := by omega_using [h24]
    have hscreen : screen 2 P = (decide (P % 8 = 3) && decide (P % 255 ∈ allowed2)) :=
      ite_eq_left_of_eq_true _ _ (eq_true rfl)
    rw [hscreen, h8, show decide ((3 : Nat) = 3) = true from rfl, Bool.true_and]
    exact decide_eq_true <| fin2 (P % 255) hr ⟨by omega_using [m3, p3, e3], by omega_using [m5, p5, e5],
      by omega_using [m17, p17, e17]⟩
  · have h10 : P % 10 = 3 ∨ P % 10 = 7 := by
      unfold Spec.Ffdh.generationShape at hs
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
        show ((5 : Nat) == 2) = false from rfl, Bool.false_eq_true, ite_false, true_and] at hs
      exact hs.2
    have hscreen : screen 5 P = (decide (P % 4 = 3) && decide (P % 255 ∈ allowed5)) :=
      ite_eq_right_of_eq_false _ _ (eq_false (by decide))
    rw [hscreen, e4, show decide ((3 : Nat) = 3) = true from rfl, Bool.true_and]
    exact decide_eq_true <| fin5 (P % 255) hr ⟨by omega_using [m3, p3, e3], by omega_using [m5, h10],
      by omega_using [m17, p17, e17]⟩

/-- Rejecting by `screen` before the sieve rejects nothing the sieve accepts. -/
theorem congruent_sieved {p : CandidateP} (hb : 512 ≤ p.bits) (hgen : p.gen = 2 ∨ p.gen = 5) :
    ((p.congruent && p.sieved p.P) && p.sieved p.Q) =
      ((Spec.Ffdh.generationShape p.bits p.gen p.P && p.sieved p.P) && p.sieved p.Q) := by
  obtain ⟨hodd, hl, hu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_using [hb])
    (Spec.Rsa.os2ip p.prefix)
  obtain ⟨hql, -⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by omega_using [hb]) hodd hl hu
  have h13 : 2 ^ 13 ≤ 2 ^ (p.bits - 2) := Nat.pow_le_pow_right (by decide) (by omega_using [hb])
  have h14 : 2 ^ 13 ≤ 2 ^ (p.bits - 1) := Nat.pow_le_pow_right (by decide) (by omega_using [hb])
  change p.P % 2 = 1 at hodd
  change 2 ^ (p.bits - 1) ≤ p.P at hl
  change 2 ^ (p.bits - 2) ≤ (p.P - 1) / 2 at hql
  unfold CandidateP.congruent
  cases hs : Spec.Ffdh.generationShape p.bits p.gen p.P <;>
    cases hsp : p.sieved p.P <;> cases hsq : p.sieved p.Q <;> simp only [Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true]
  unfold CandidateP.sieved at hsp hsq
  exact screen_of_shape hgen hodd (by omega_using [h14, hl]) (by unfold CandidateP.Q at hsq; omega_using [h13, hql]) hs
    ((Bool.and_eq_true _ _).mp hsp).1 ((Bool.and_eq_true _ _).mp hsq).1

theorem generatorCheck_state_ok {p : CandidateP} {used : Nat} {c : Checks} {s : State} {mi : BitVec 64}
    (h : CandidateTape p used s)
    (hg : Good s (off p.B 256) (p.Z - 256) (p.phaseWords false) mi)
    (hp : PhaseHeader p false c s)
    (hn : wv s.mem (off p.B 256) (slot (p.phaseWords false) aN) (p.phaseWords false) = p.P) :
    WP isa (.seq (.block [.mov .rax (.mem (hdr sLink)), .mov .rdx (.mem (ws .rax oGen))]) generatorCheck) s
      fun t => CandidateTape p used t ∧
        Good t (off p.B 256) (p.Z - 256) (p.phaseWords false) mi ∧ PhaseHeader p false c t ∧
        wv t.mem (off p.B 256) (slot (p.phaseWords false) aN) (p.phaseWords false) = p.P ∧
        t.zf = some p.congruent ∧
        t.mem = s.mem ∧ Keep mmRegs s t := by
  have hgen := h.base.hdr (oGen, BitVec.ofNat 64 p.gen) (by simp [CandidateP.headers])
  have hrd := h.base.scr.ld (show 8 * oGen + 8 ≤ p.Z by
    change 88 ≤ p.Z
    omega_using [h.base.header_room])
  have hlinkrd := hg.scr.ld (show 8 * sLink + 8 ≤ p.Z - 256 by
    have hz := (h.base.phase_dims false).z
    change 136 ≤ p.Z - 256
    unfold slot hdrBytes at hz
    omega_using [hz])
  refine WP.seq (WP.mono (WP.keep [.rax, .rdx] (Q := fun u =>
    u.gpr .rdx = BitVec.ofNat 64 p.gen ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, ws, hg.rdi, hdrOff, hp.link, hgen, hrd, hlinkrd]) rfl)
    fun u ⟨⟨hdx, hm⟩, ku⟩ => ?_)
  have hgu : Good u (off p.B 256) (p.Z - 256) (p.phaseWords false) mi :=
    ⟨hg.scr.congr ku.2.2, (ku.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  have hbit : Spec.RsaKeyGen.bitLength p.P = p.bits :=
    VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega_using [h.base.bits1]) _ |>.1
  refine WP.mono (generatorCheck_ok hgu (h.base.phase_dims false).z
    (by omega_using [(h.base.phase_room false).1]) (by omega_using [(h.base.phase_room false).2.1])
    h.base.bits1 h.base.bits2 (by rw [hm, hn]; exact hbit) h.base.gen hdx)
    fun t ⟨hz, hmt, kt⟩ => ?_
  have hmem : t.mem = s.mem := hmt.trans hm
  have kk : Keep mmRegs s t := (ku.trans kt).mono (by decide)
  have hf : CandidateFrame p s.mem t.mem := by rw [hmem]; exact CandidateFrame.refl _ _
  have hh : ∀ j < 15, word t.mem p.B (8 * j) = word s.mem p.B (8 * j) := fun _ _ => by rw [hmem]
  refine ⟨h.keep hf hh kk ((kk.gpr (by decide)).trans h.base.sp),
    ⟨hg.scr.congr kk.2.2, (kk.gpr (by decide)).trans hg.rdi, by rw [hmem]; exact hg.hdr⟩,
    ⟨by rw [hmem]; exact hp.bits, by rw [hmem]; exact hp.len,
      by rw [hmem]; exact hp.checks, by rw [hmem]; exact hp.link⟩, by simpa only [hmem] using hn,
    by simpa only [hm, hn, CandidateP.congruent] using hz, hmem, kk⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter candidates on x86-64: the screen on p's octets

`outerScreen` decides `screen` from the octets of p in the output buffer,
before any workspace is set up: their sum is p modulo 255 (256 ≡ 1), and the
last octet is p modulo 256. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 (hdr at0)
open VG.Impl.Ffdh.X86_64.ParameterCandidate

private theorem bytesAt_snoc (m : Mem) (p : Addr) (n : Nat) :
    Spec.Rsa.bytesAt m p (n + 1) = Spec.Rsa.bytesAt m p n ++ [m (off p n)] := by
  simp [Spec.Rsa.bytesAt, List.range_succ, off]

private theorem os2ip_snoc' (l : List Byte) (b : Byte) :
    Spec.Rsa.os2ip (l ++ [b]) = 256 * Spec.Rsa.os2ip l + b.toNat := by
  simp only [Spec.Rsa.os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- After `j` octets of the sum. -/
structure SumInv (s₀ : State) (op : Addr) (n j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .rsi, .r10, .rcx] s₀ t
  mem : t.mem = s₀.mem
  ptr : t.gpr .r10 = off op j
  count : t.gpr .rcx = BitVec.ofNat 64 (n - j)
  sum : (t.gpr .rsi).toNat % 255 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem op j) % 255
  small : (t.gpr .rsi).toNat ≤ 255 * j

theorem sumStep_ok {s₀ t : State} {op : Addr} {n j : Nat} (hn : n < 2 ^ 31) (hj : j < n)
    (hrd : ∀ i < n, InRegions (s₀.rd ++ s₀.wr) (off op i) 1) (h : SumInv s₀ op n j t) :
    WP isa (.block sumByte) t fun u => u.zf = some (decide (j + 1 = n)) ∧ SumInv s₀ op n (j + 1) u := by
  have hrd' : InRegions (t.rd ++ t.wr) (off op j) 1 := by rw [h.keep.2.1, h.keep.2.2]; exact hrd j hj
  have hb := (s₀.mem (off op j)).isLt
  refine WP.mono (WP.keep [.rax, .rsi, .r10, .rcx] (Q := fun u =>
    u.zf = some (decide (j + 1 = n)) ∧ u.gpr .r10 = off op (j + 1) ∧
      u.gpr .rcx = BitVec.ofNat 64 (n - (j + 1)) ∧
      (u.gpr .rsi).toNat = (t.gpr .rsi).toNat + (s₀.mem (off op j)).toNat ∧ u.mem = t.mem) ?_ rfl)
    fun u ⟨⟨hz, hp, hc, hs, hm⟩, k⟩ => ⟨hz, (h.keep.trans k).mono (by decide), hm.trans h.mem, hp, hc, ?_, ?_⟩
  · unfold sumByte
    have hsmall := h.small
    have hp1 : off op j + 1 = off op (j + 1) := by
      simp only [off, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    have hz0 : BitVec.ofInt 64 0 = 0#64 := rfl
    xrun [State.ea, at0, h.ptr, hz0, BitVec.add_zero, hrd', h.mem, h.count, sx1, hp1]
    have hsub : BitVec.ofNat 64 (n - j) - 1 = BitVec.ofNat 64 (n - (j + 1)) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have : (1 : BitVec 64).toNat = 1 := rfl
      rw [this]; omega_using [hj]
    rw [hsub]
    refine ⟨?_, rfl, ?_⟩
    · rw [show (BitVec.ofNat 64 (n - (j + 1)) == 0) = (BitVec.ofNat 64 (n - (j + 1)) - BitVec.ofNat 64 0 == 0)
        by rw [BitVec.sub_zero], ofNat_sub_beq (by omega_using [hn]) (by omega_using [])]
      simp only [decide_eq_decide]
      omega_using [hj]
    · rw [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_using [] : BitVec.toNat (s₀.mem (off op j)) < 2 ^ 64)]
      have := (t.gpr .rsi).isLt
      omega_using [hn, hj, hsmall]
  · rw [hs, bytesAt_snoc, os2ip_snoc', Nat.add_mod, h.sum, ← Nat.add_mod]
    omega_using []
  · rw [hs]; have := h.small; omega_using [this]

theorem sumLoop_ok {s : State} {op : Addr} {n : Nat} (hn1 : 1 ≤ n) (hn : n < 2 ^ 31)
    (hp : s.gpr .r10 = op) (hc : s.gpr .rcx = BitVec.ofNat 64 n) (hsi : s.gpr .rsi = 0)
    (hrd : ∀ i < n, InRegions (s.rd ++ s.wr) (off op i) 1) :
    WP isa (.loop (.block sumByte) .ne) s (SumInv s op n n) :=
  wp_upto (a := 0) (by omega_using [hn1]) (SumInv s op n)
    (fun j _ hj t ht => sumStep_ok hn hj hrd ht) (fun _ h => h)
    ⟨Keep.refl _ _, rfl, by rw [hp]; simp [off], by rw [hc, Nat.sub_zero],
      by rw [hsi]; simp [Spec.Rsa.bytesAt, Spec.Rsa.os2ip], by rw [hsi]; simp⟩

private theorem os2ip_low {m : Mem} {op : Addr} {n k : Nat} (hn : 1 ≤ n) (hk : k ≤ 8) :
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt m op n) % 2 ^ k = (m (off op (n - 1))).toNat % 2 ^ k := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega_using [hn]⟩
  rw [bytesAt_snoc, os2ip_snoc', Nat.add_sub_cancel]
  have hd : 2 ^ k ∣ 256 := by
    have := Nat.pow_dvd_pow 2 hk; simpa using this
  obtain ⟨c, hc⟩ := hd
  rw [hc, Nat.mul_assoc, Nat.mul_add_mod]

/-- `lowByte (2 ^ k - 1)`: ZF iff RAX is 1 and the octet before R10 is 3
modulo `2 ^ k`. -/
theorem lowByte_ok {s : State} {op : Addr} {n : Nat} {b : Bool} (k : Nat) (hk : 2 ≤ k) (hk' : k ≤ 8)
    (hn : 1 ≤ n) (hn' : n < 2 ^ 31) (hp : s.gpr .r10 = off op n)
    (hrd : InRegions (s.rd ++ s.wr) (off op (n - 1)) 1) (hax : s.gpr .rax = if b then 1 else 0) :
    WP isa (.block (lowByte (2 ^ k - 1))) s fun t =>
      t.zf = some (b && decide ((s.mem (off op (n - 1))).toNat % 2 ^ k = 3)) ∧ t.mem = s.mem ∧
        Keep [.rax, .rcx, .rdx] s t := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t =>
    t.zf = some (b && decide ((s.mem (off op (n - 1))).toNat % 2 ^ k = 3)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hz, hm⟩, kk⟩ => ⟨hz, hm, kk⟩
  have hm1 : BitVec.ofNat 64 n + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (n - 1) := by
    have : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := by decide
    rw [this]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_allOnes]; omega
  have hea : off op n + BitVec.ofInt 64 (-1) = off op (n - 1) := by
    rw [off, BitVec.add_assoc, hm1]
  have h4 : 4 ≤ 2 ^ k := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hk; simpa using this
  have h8 : 2 ^ k ≤ 256 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hk'; simpa using this
  have hmask : 2 ^ k - 1 < 2 ^ 31 := by omega_using [h8]
  generalize hx : s.mem (off op (n - 1)) = x
  have hlow : ((x.setWidth 64 &&& BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ k - 1))) -
      (3 : BitVec 64) == 0) = decide (x.toNat % 2 ^ k = 3) := by
    have hand : (x.setWidth 64 &&& BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ k - 1))).toNat = x.toNat % 2 ^ k := by
      rw [sx_ofNat hmask, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := x.isLt; omega_using []), Nat.mod_eq_of_lt (by omega_using [h8]),
        Nat.and_two_pow_sub_one_eq_mod]
    rw [sub_beq_zero]
    by_cases h : x.toNat % 2 ^ k = 3
    · simp only [h, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq; rw [hand, h]; rfl
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro he; apply h; rw [← hand, he]; rfl
  unfold lowByte
  cases b <;> by_cases h : x.toNat % 2 ^ k = 3 <;>
    xrun [State.ea, hp, hea, hrd, hx, hax, sx_ofNat (show 3 < 2 ^ 31 by decide), hlow, h, execCmov, eval,
      Bool.not_true, Bool.not_false]

/-- p's octets in the output buffer: `outerScreen` decides `screen` from them. -/
abbrev outP (p : CandidateP) (m : Mem) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt m p.op p.k)

theorem byteScreen_ok {p : CandidateP} {used : Nat} {s : State} {vals : List Nat} {k : Nat}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (hvals : ∀ v ∈ vals, v < 2 ^ 31)
    (hk : 2 ≤ k) (hk' : k ≤ 8) :
    WP isa (byteScreen vals k) s fun t =>
      t.zf = some (decide (outP p s.mem % 255 ∈ vals) && decide (outP p s.mem % 2 ^ k = 3)) ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx, .rdx, .rsi, .r10] s t := by
  have hrdh : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hOut := h.base.hdr (oOut, p.op) (by simp [CandidateP.headers])
  have hLen := h.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  have hw := h.base.widths
  have hout : ∀ i < p.k, InRegions (s.rd ++ s.wr) (off p.op i) 1 := fun i hi =>
    let ⟨r, hr, hc⟩ := h.base.out.wr i hi; ⟨r, List.mem_append_right _ hr, hc⟩
  unfold byteScreen
  refine WP.seq (WP.mono (WP.keep [.r10, .rcx, .rsi] (Q := fun u =>
    u.gpr .r10 = p.op ∧ u.gpr .rcx = BitVec.ofNat 64 p.k ∧ u.gpr .rsi = 0 ∧ u.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hOut, hLen, hrdh oOut (by decide), hrdh oLen (by decide)]) rfl)
    fun u ⟨⟨hp, hc, hsi, hm⟩, k₁⟩ => ?_)
  have hout' : ∀ i < p.k, InRegions (u.rd ++ u.wr) (off p.op i) 1 := fun i hi => by
    rw [k₁.2.1, k₁.2.2]; exact hout i hi
  refine WP.seq (WP.mono (sumLoop_ok (by omega_using [hw]) (by omega_using [hw]) hp hc hsi hout') fun v hv => ?_)
  refine WP.block_append (WP.block_append (WP.mono (reduce255_ok v) fun x ⟨hx, hmx, kx⟩ => ?_))
  have hr : (x.gpr .rsi).toNat = outP p s.mem % 255 := by
    rw [hx, hv.sum, hm]
  have hsi' : x.gpr .rsi = BitVec.ofNat 64 (outP p s.mem % 255) := by
    rw [← hr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (memberFlag_ok (by omega_arith) hvals hsi') fun y ⟨hy, hmy, ky⟩ => ?_
  have hp' : y.gpr .r10 = off p.op p.k := by rw [ky.gpr (by decide), kx.gpr (by decide), hv.ptr]
  have hrd' : InRegions (y.rd ++ y.wr) (off p.op (p.k - 1)) 1 := by
    rw [ky.2.1, ky.2.2, kx.2.1, kx.2.2, hv.keep.2.1, hv.keep.2.2]; exact hout' _ (by omega_using [hw])
  refine WP.mono (lowByte_ok k hk hk' (by omega_using [hw]) (by omega_using [hw]) hp' hrd' hy) fun t ⟨hz, hmt, kt⟩ =>
    ⟨?_, hmt.trans (hmy.trans (hmx.trans (hv.mem.trans hm))), ?_⟩
  · rw [hz, hmy, hmx, hv.mem, hm, ← os2ip_low (by omega_using [hw]) hk']
  · exact ((((k₁.trans hv.keep).trans kx).trans ky).trans kt).mono (by decide)

/-- `outerScreen`: ZF is `screen` of p's octets. -/
theorem outerScreen_ok {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) :
    WP isa outerScreen s fun t => t.zf = some (screen p.gen (outP p s.mem)) ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .rdx, .rsi, .r10] s t := by
  have hrdh : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => h.base.scr.ld (by omega_using [hj, h.base.header_room])
  have hGen := h.base.hdr (oGen, BitVec.ofNat 64 p.gen) (by simp [CandidateP.headers])
  unfold outerScreen
  refine WP.seq (WP.mono (WP.keep [.rdx] (Q := fun u => u.zf = some (decide (p.gen = 2)) ∧ u.mem = s.mem)
    (by
      xrun [State.ea, hdr, hdi, hdrOff, hGen, hrdh oGen (by decide)]
      exact ofNat_sub_beq (N := 2) (by rcases h.base.gen with h | h <;> rw [h] <;> decide) (by decide)) rfl)
    fun u ⟨⟨hz, hm⟩, k₁⟩ => ?_)
  have hu : CandidateTape p used u := (h.same_mem hm k₁ (by decide)).1
  have hdu : u.gpr .rdi = p.B := (k₁.gpr (by decide)).trans hdi
  refine WP.ite (decide (p.gen = 2)) (by simp [eval, hz]) (fun hg => ?_) (fun hg => ?_)
  · have hg' : p.gen = 2 := of_decide_eq_true hg
    refine WP.mono (byteScreen_ok hu hdu allowed2_lt (by decide) (by decide)) fun t ⟨hz', hmt, kt⟩ =>
      ⟨?_, hmt.trans hm, (k₁.trans kt).mono (by decide)⟩
    rw [hz', hm]; simp only [screen, hg', ite_true, Bool.and_comm, show (2 : Nat) ^ 3 = 8 from rfl]
  · have hg' : ¬ p.gen = 2 := of_decide_eq_false hg
    refine WP.mono (byteScreen_ok hu hdu allowed5_lt (by decide) (by decide)) fun t ⟨hz', hmt, kt⟩ =>
      ⟨?_, hmt.trans hm, (k₁.trans kt).mono (by decide)⟩
    rw [hz', hm]; simp only [screen, hg', ite_false, Bool.and_comm, show (2 : Nat) ^ 2 = 4 from rfl]

end VG.Proof.Ffdh.X86_64.ParameterCandidate
