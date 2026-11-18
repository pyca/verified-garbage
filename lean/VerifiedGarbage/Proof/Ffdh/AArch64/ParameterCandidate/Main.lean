module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Sieve
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Phase
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Stream
public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Mr
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieved
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.MrDraw
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Rsa.AArch64.Div
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Base
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.TrialTable
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Trial
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Fin
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Test
import VerifiedGarbage.Proof.RsaKeyGen.Slots

/-! ### `Ffdh.AArch64.ParameterCandidate.Tests`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on AArch64: the tests of `q` and `p`

`testQ_ok`: `q` (in `aN`, of `⌈bits / 64⌉` words) tested with its own word
count; `testP1_ok` and `testPR_ok`: `p` loaded again and tested by its first
witness, and by the others (`firstCheck_ok`, `restChecks_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Impl.RsaKeyGen.AArch64.Candidate (expSetup)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The low `k` words of a number below `2^(64 k)` are the number. -/
theorem wv_low {m : Mem} {B : Addr} {o w k v : Nat} (h : wv m B o w = v) (hk : k ≤ w)
    (hv : v < 2 ^ (64 * k)) : wv m B o k = v := by
  have e := wv_add m B o k (w - k)
  rw [show k + (w - k) = w by omega_arith, h] at e
  generalize 2 ^ (64 * k) = P at e hv
  generalize wv m B (o + 8 * k) (w - k) = hi at e
  rcases Nat.eq_zero_or_pos hi with h0 | hpos
  · rw [h0, Nat.mul_zero, Nat.add_zero] at e; exact e.symm
  · have := Nat.le_mul_of_pos_right P hpos; omega_arith

/-- The test of `q`. -/
theorem qPhase_ok {p : PP} {s : State} {c u : Nat} (h : PSt p (mW p.bits) s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (mW p.bits) aN) (mW p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (seqs (phase true)) s fun t =>
      TT p (p.bits - 1) ((c - 1) / 2) u (Spec.Ffdh.primeChecks (p.bits - 1)) t ∧ InScr p.B p.Z s.mem t.mem ∧
        Keep mmRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hws := h.ws
  have hn := hws.scr.nowrap
  have sN := hws.sl (show aN < 16 by decide)
  obtain ⟨hpo, hl, hu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hpo hl hu
  obtain ⟨hql, hqu⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by omega_arith) hpo hl hu
  have hbl := VG.Proof.Ffdh.ParameterCandidate.half_pred_bitLength (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L)) (by rw [← hc]; exact hqo)
  rw [← hc] at hbl
  refine WP.mono (phase_ok h.ph true) fun t ht => ?_
  have hmb : p.mb true = p.bits - 1 := by simp only [PP.mb, ↓reduceIte]
  have st := ht.st
  rw [hmb] at st
  have hEZ := h.dims.eZ true
  rw [hmb] at hEZ
  have hwq : mW (p.bits - 1) ≤ mW p.bits := by simp only [mW]; omega_arith
  have iq : InScr p.B p.Z s.mem t.mem := InScr.of_frm ht.frm fun r hr => by
    have := phaseRanges_kmut r hr; have := hws.h256; omega_arith
  refine ⟨⟨st, by omega_arith, by omega_arith, hEZ, by rw [← hmb]; exact ht.len, by rw [← hmb]; exact ht.top,
    by rw [← hmb]; exact ht.checks, primeChecks_pos _, primeChecks_lt _, ht.mask, ?_, hqo, ?_, hbl, ?_, hul, hL,
    by omega_arith⟩, iq, ht.keep⟩
  · refine wv_low (w := mW p.bits) ?_ hwq (Nat.lt_of_lt_of_le hqu (Nat.pow_le_pow_right (by decide) (by
      simp only [mW]; omega_arith)))
    rw [show slot (mW (p.bits - 1)) aN = slot (mW p.bits) aN by simp only [slot, aN, Nat.zero_mul]]
    rw [ht.frm.wv_eq (fun r hr => .inr (Nat.le_trans (phaseRanges_kmut r hr)
      (by simp only [slot, hdrBytes, aN]; omega_arith))) (by omega_arith)]
    exact hq
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show p.bits - 1 - 1 ≤ p.bits - 2 by omega_arith)
    omega_arith
  · rw [ht.frm.word_eq (fun r hr => by
      have := phaseRanges_kmut r hr
      simp only [phaseRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [kUsed, sK, fChecks, sW, sArr, sStride, Public.sMask, fTop, sFn] <;> omega_arith)
      (by simp only [kUsed, sFn]; have := hws.h256; omega_arith)]
    exact hU

/-- The test of `p`, loaded again. -/
theorem pPhase_ok {p : PP} {s : State} {c u : Nat} (h : PH p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (seqs (phase false ++ shapeP)) s fun t =>
      TT p p.bits c u (Spec.Ffdh.primeChecks p.bits) t ∧ InScr p.B p.Z s.mem t.mem ∧ Keep mmRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have h256 : 8 * 32 ≤ p.Z := by have := h.dims.z; omega_arith
  obtain ⟨hpo, hl, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  have hbl := (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))).2
  rw [← hc] at hpo hl hbl
  refine wp_seqs_append (by simp [phase]) (by simp [shapeP, loadA]) ?_
  refine WP.mono (phase_ok h false) fun t ht => ?_
  have hmb : p.mb false = p.bits := by simp only [PP.mb, Bool.false_eq_true, ↓reduceIte]
  have st := ht.st
  rw [hmb] at st
  have hEZ := h.dims.eZ false
  rw [hmb] at hEZ
  have hlen : word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.L := by have := ht.len; rw [hmb] at this; exact this
  have htop : word t.mem p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK p.bits - 1) := by
    have := ht.top; rw [hmb] at this; exact this
  have hUt : word t.mem p.B (8 * kUsed) = BitVec.ofNat 64 u := by
    rw [ht.frm.word_eq (fun r hr => by
      simp only [phaseRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [kUsed, sK, fChecks, sW, sArr, sStride, Public.sMask, fTop, sFn] <;> omega_arith)
      (by simp only [kUsed, sFn]; have := st.ws.scr.nowrap; omega_arith)]
    exact hU
  refine WP.mono (shapeP_ok st hlen htop hL) fun t₂ ⟨st₂, hn₂, f₂, k₂⟩ => ?_
  have hn := st₂.ws.scr.nowrap
  have hH : ∀ {k : Nat}, k < 32 → word t₂.mem p.B (8 * k) = word t.mem p.B (8 * k) := fun {k} hk =>
    f₂.word_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, aN]; omega_arith)) (by omega_arith)
  have ip : InScr p.B p.Z s.mem t₂.mem := (InScr.of_frm ht.frm fun r hr => by
    have := phaseRanges_kmut r hr; omega_arith).trans (InScr.of_frm f₂ fun r hr => by
      rw [List.mem_singleton.mp hr]; exact st₂.ws.sl (show aN < 16 by decide))
  exact ⟨⟨st₂, by omega_arith, by omega_arith, hEZ, by rw [hH (by decide)]; exact hlen,
    by rw [hH (by decide)]; exact htop, by rw [hH (by decide)]; have := ht.checks; rw [hmb] at this; exact this,
    primeChecks_pos _, primeChecks_lt _, by rw [hH (by decide)]; exact ht.mask, by rw [hn₂, hc], hpo, hl, hbl, by rw [hH (by decide)]; exact hUt, hul, hL, Nat.le_refl _⟩,
    ip, (ht.keep.trans k₂).mono (by decide)⟩

/-- `fChecks := K'`: the test's other data stay. -/
theorem TT.setChecks {p : PP} {mb N u K K' : Nat} {s t : State} (h : TT p mb N u K s)
    (hm : t.mem = s.mem.writeW (off p.B (8 * fChecks)) (BitVec.ofNat 64 K')) {regs : List Reg} (k : Keep regs s t)
    (h0 : .x0 ∉ regs) (h1 : 1 ≤ K') (h2 : K' < 2 ^ 62) : TT p mb N u K' t := by
  have hws := h.st.ws
  have hn := hws.scr.nowrap
  have h256 := hws.h256
  have f : Frm p.B [(8 * fChecks, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [fChecks]; omega_arith)) (by simp)
  have hH : ∀ {i : Nat}, 1 ≤ i → i < 32 → word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun {i} hi hi' =>
    f.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only [fChecks]; omega_arith))
      (by omega_arith)
  have sN := hws.sl (show aN < 16 by decide)
  exact ⟨h.st.step (hws.congr' f (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.hdr (by decide)) k h0) f
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fChecks]; omega_arith) k,
    h.mb1, h.mb2, h.eZ, by rw [hH (by decide) (by decide)]; exact h.len, by rw [hH (by decide) (by decide)]; exact h.top,
    by rw [hm, word_writeW_self], h1, h2, by rw [hH (by decide) (by decide)]; exact h.msk,
    by rw [f.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inr (by simp only [slot, hdrBytes, fChecks]; omega_arith))
      (by omega_arith)]; exact h.n, h.odd, h.lo, h.bl,
    by rw [hH (by simp only [kUsed, sFn]; omega_arith) (by simp only [kUsed, sFn]; omega_arith)]; exact h.used, h.ul, h.hL, h.mbb⟩

/-- `firstCheck`: one witness. -/
theorem firstCheck_ok {p : PP} {mb N u K : Nat} {s : State} (h : TT p mb N u K s) :
    WP isa firstCheck s fun t => TT p mb N u 1 t ∧ InScr p.B p.Z s.mem t.mem ∧ Keep mmRegs s t := by
  have hws := h.st.ws
  have hn := hws.scr.nowrap
  have h256 := hws.h256
  unfold firstCheck
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off p.B (8 * fChecks)) (BitVec.ofNat 64 1))
    (by brun [hws.x0, hdr_enc (show fChecks < 32 by decide), imm16 (show 1 < 65536 by decide),
      hws.scr.st (d := 8 * fChecks) (by simp only [fChecks]; omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  refine ⟨h.setChecks hm k (by decide) (Nat.le_refl _) (by decide), ?_, k.mono (by decide)⟩
  have f : Frm p.B [(8 * fChecks, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [fChecks]; omega_arith)) (by simp)
  exact InScr.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fChecks]; omega_arith)

/-- `restChecks`: the witnesses but one. -/
theorem restChecks_ok {p : PP} {mb N u K : Nat} {s : State} (h : TT p mb N u K s) (hK : 2 ≤ K) :
    WP isa restChecks s fun t => TT p mb N u (K - 1) t ∧ InScr p.B p.Z s.mem t.mem ∧ Keep mmRegs s t := by
  have hws := h.st.ws
  have hn := hws.scr.nowrap
  have h256 := hws.h256
  have k2 := h.k2
  have hK' : BitVec.ofNat 64 K - BitVec.ofNat 64 1 = BitVec.ofNat 64 (K - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  have hc : s.mem.readW (off p.B (8 * fChecks)) 64 = BitVec.ofNat 64 K := h.chk
  unfold restChecks
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off p.B (8 * fChecks)) (BitVec.ofNat 64 (K - 1)))
    (by brun [hws.x0, hdr_enc (show fChecks < 32 by decide), hc, hK',
      hws.scr.ld (d := 8 * fChecks) (by simp only [fChecks]; omega_arith),
      hws.scr.st (d := 8 * fChecks) (by simp only [fChecks]; omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k⟩ => ?_
  refine ⟨h.setChecks hm k (by decide) (by omega_arith) (by omega_arith), ?_, k.mono (by decide)⟩
  have f : Frm p.B [(8 * fChecks, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [fChecks]; omega_arith)) (by simp)
  exact InScr.of_frm f (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fChecks]; omega_arith)

theorem test_true (M : Mont) (R : Kernel) :
    test true [] M.mm R.run = phase true ++
      (montPrep M.mm ++ expSetup ++ VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin M.mm R.run) := by
  simp only [test, ↓reduceIte, List.append_nil, List.append_assoc]

theorem test_false' (M : Mont) (R : Kernel) (adjust : Prog isa) :
    test false [adjust] M.mm R.run = (phase false ++ shapeP) ++ ([adjust] ++
      (montPrep M.mm ++ expSetup ++ VG.Impl.Ffdh.AArch64.ParameterCandidate.millerRabin M.mm R.run)) := by
  simp only [test, Bool.false_eq_true, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]

/-- The test of `q`. -/
theorem testQ_ok (M : Mont) (R : Kernel) {p : PP} {s : State} {c u : Nat} (h : PSt p (mW p.bits) s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (mW p.bits) aN) (mW p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (seqs (test true [] M.mm R.run)) s
      (MrEnd p (mW (p.bits - 1)) ((c - 1) / 2) (p.bits - 1) (Spec.Ffdh.primeChecks (p.bits - 1)) s
        (checkWitnesses ((c - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1)) (p.r.drop u))) := by
  rw [test_true]
  refine wp_seqs_append (by simp [phase]) (by simp [montPrep]) ?_
  refine WP.mono (qPhase_ok h hc hq hqo hU hul hL) fun t ⟨ht, i₁, k₁⟩ => ?_
  exact WP.mono (testTail_ok M R ht) fun t' ⟨a, b, c, d, e⟩ => ⟨a, b, c, i₁.trans d, (k₁.trans e).mono (by decide)⟩

/-- A test of `p`, loaded again, with its witness count changed by `adjust`. -/
theorem testP_of (M : Mont) (R : Kernel) {p : PP} {adjust : Prog isa} {K : Nat}
    (hadj : ∀ {u : Nat} {s : State}, TT p p.bits (Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L))) u
      (Spec.Ffdh.primeChecks p.bits) s →
      WP isa adjust s fun t => TT p p.bits (Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L))) u K t ∧
        InScr p.B p.Z s.mem t.mem ∧ Keep mmRegs s t)
    {s : State} {w c u : Nat} (h : PSt p w s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (seqs (test false [adjust] M.mm R.run)) s
      (MrEnd p (mW p.bits) c p.bits K s (checkWitnesses c K (p.r.drop u))) := by
  subst hc
  rw [test_false']
  refine wp_seqs_append (by simp [phase]) (by simp) ?_
  refine WP.mono (pPhase_ok h.ph rfl hU hul hL) fun t ⟨ht, i₁, k₁⟩ => ?_
  refine wp_seqs_append (by simp) (by simp [montPrep]) ?_
  rw [seqs_one]
  refine WP.mono (hadj ht) fun t₂ ⟨ht₂, i₂, k₂⟩ => ?_
  exact WP.mono (testTail_ok M R ht₂) fun t' ⟨a, b, c, d, e⟩ =>
    ⟨a, b, c, (i₁.trans i₂).trans d, ((k₁.trans k₂).trans e).mono (by decide)⟩

/-- The test of `p`'s first witness. -/
theorem testP1_ok (M : Mont) (R : Kernel) {p : PP} {s : State} {w c u : Nat} (h : PSt p w s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (seqs (test false [firstCheck] M.mm R.run)) s
      (MrEnd p (mW p.bits) c p.bits 1 s (checkWitnesses c 1 (p.r.drop u))) :=
  testP_of M R (fun ht => firstCheck_ok ht) h hc hU hul hL

/-- The test of `p`'s other witnesses. -/
theorem testPR_ok (M : Mont) (R : Kernel) {p : PP} {s : State} {w c u : Nat} (h : PSt p w s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (seqs (test false [restChecks] M.mm R.run)) s
      (MrEnd p (mW p.bits) c p.bits (Spec.Ffdh.primeChecks p.bits - 1) s
        (checkWitnesses c (Spec.Ffdh.primeChecks p.bits - 1) (p.r.drop u))) :=
  testP_of M R (fun ht => restChecks_ok ht (by unfold Spec.Ffdh.primeChecks; split <;> decide)) h hc hU hul hL

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-! ### `Ffdh.AArch64.ParameterCandidate.Result`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on AArch64: the results of the tests

`pResult_ok` and `qResult_ok`: the status and `used` from how Miller–Rabin
ended (`MrEnd`), and `p` to `out` (`finPrimeL_ok`, RSA's `finPrime` for
`out_len` octets of fewer than `8 w`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- `finPrime`: `c` (`aN`) to the `L` octets of `out`, `kUsed` to `used`,
status 1. -/
theorem finPrimeL_ok {s : State} {B : Addr} {Z w : Nat} {op up : Addr} {u c L : Nat} (h : Ws s B Z w)
    (hL1 : 1 ≤ L) (hLw : L ≤ 8 * w) (hu : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hO : word s.mem B (8 * kOut) = op) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 L)
    (hU : word s.mem B (8 * kUsedP) = up) (hM : word s.mem B (8 * Public.sMask) = mask true)
    (ho : OutUp s B Z op up L) (hn : wv s.mem B (slot w aN) ((L + 7) / 8) = c) :
    WP isa finPrime s fun t => KEnd s t op up L 1 u (some c) := by
  have hs := h.scr
  have hnw := hs.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [h256, hi])
  unfold finPrime
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [storeA]) ?_
  rw [seqs_one]
  refine WP.mono (WP.keep [.x3, .x2] (Q := fun t => t.mem = s.mem.writeW up (BitVec.ofNat 64 u)) (by
    have hup : up + BitVec.ofNat 64 0 = up := off_zero up
    brun [h.x0, hdr_enc (show kUsed < 32 by decide), hdr_enc (show kUsedP < 32 by decide), hl kUsed (by decide),
      hl kUsedP (by decide), hu, hU, hup, ho.upw]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨hm₁, k₁⟩ => ?_
  have f₁ : Frm B [(Z, 2 ^ 64)] s.mem s₁.mem := by rw [hm₁]; exact frm_up ho.upZ _ _
  have h₁ : Ws s₁ B Z w := h.congr' f₁ (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact KMut.past h256 _) k₁ (by decide)
  have hw₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    f₁.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact Or.inl (by omega)) (by omega_using [hi])
  have hn₁ : wv s₁.mem B (slot w aN) ((L + 7) / 8) = c := by
    rw [f₁.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Or.inl (by have := h₁.sl (show aN < 16 by decide); omega_using [hLw, this]))
      (by have := h₁.sl (show aN < 16 by decide); omega_using [hLw, hnw, this])]; exact hn
  refine wp_seqs_append (by simp [storeA]) (by simp) ?_
  refine WP.mono (storeA_ok h₁ (j := aN) (sPtr := kOut) (sLen := kLen) (sMsk := Public.sMask) (c := true)
    (by decide) (by decide) (by decide) (by decide) (by rw [hw₁ _ (by decide)]; exact hO)
    (by rw [hw₁ _ (by decide)]; exact hK) (by rw [hw₁ _ (by decide)]; exact hM) hL1 hLw
    (fun i hi => by rw [k₁.wr]; exact ho.outw i hi) ho.outZ) fun s₂ ⟨hb₂, hx₂, hwr₂, _, k₂⟩ => ?_
  rw [seqs_one]
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 1 ∧ t.mem = s₂.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨hx, hm⟩, k₃⟩ => ?_
  simp only [hn₁, ↓reduceIte] at hb₂
  refine ⟨hx, ?_, by rw [hm]; exact hb₂, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [hm]
  refine (Mem.readW_congr fun b hb => hx₂ _ fun i hi he => ho.ou i hi b hb ?_).trans ?_
  · exact he.symm
  · rw [hm₁]; exact Mem.readW_writeW_self64 _ _ _

/-- How a test ended, from `s`. -/
def PTEnd (s t : State) (op up : Addr) (k : Nat) (r : List Byte) (c : Nat) :
    Option (Bool × List Byte) → Prop
  | none => KEnd s t op up k 0 0 none
  | some (true, rest) => KEnd s t op up k 1 (r.length - rest.length) (some c)
  | some (false, rest) => KEnd s t op up k 2 (r.length - rest.length) none

/-- The status words of `MrEnd`. -/
theorem MrEnd.stat {p : PP} {w N mb K : Nat} {s₀ s : State} {res : Option (Bool × List Byte)}
    (h : MrEnd p w N mb K s₀ res s) :
    (res = none → word s.mem p.B (8 * kStat) = BitVec.ofNat 64 0) ∧
    (∀ b rest, res = some (b, rest) → word s.mem p.B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
      word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 (p.r.length - rest.length)) := by
  refine ⟨h.2.1, fun b rest hr => ?_⟩
  obtain ⟨hs, u, hu, rfl, hU⟩ := h.2.2.1 b rest hr
  refine ⟨hs, ?_⟩
  rw [hU, List.length_drop]; congr 1; omega_using [hu]

/-- `pResult`, after `p`'s Miller–Rabin ended with `res`. -/
theorem pResult_ok {s : State} {B : Addr} {Z w c L : Nat} {op up : Addr} {r : List Byte}
    {res : Option (Bool × List Byte)} (h : Ws s B Z w) (hL1 : 1 ≤ L) (hLw : L ≤ 8 * w)
    (hn : wv s.mem B (slot w aN) ((L + 7) / 8) = c) (ho : OutUp s B Z op up L)
    (hO : word s.mem B (8 * kOut) = op) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 L)
    (hU : word s.mem B (8 * kUsedP) = up) (hM : word s.mem B (8 * Public.sMask) = mask true)
    (h0 : res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0)
    (h1 : ∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
      word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) :
    WP isa pResult s fun t => PTEnd s t op up L r c res := by
  have hs := h.scr
  have hnw := hs.nowrap
  have h256 := h.h256
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kStat)) 8 := hs.ld (by simp only [kStat, sFn]; omega_using [h256])
  unfold pResult
  have hfirst : ∀ v : Nat, word s.mem B (8 * kStat) = BitVec.ofNat 64 v →
      WP isa (.block [ldh .x3 kStat]) s fun t => (t.gpr .x3 = BitVec.ofNat 64 v ∧ t.mem = s.mem) ∧ Keep [.x3] s t :=
    fun v hv => WP.keep [.x3] (by brun [h.x0, hdr_enc (show kStat < 32 by decide), hl, hv]) (by decide) (by decide)
      (by decide +kernel)
  rcases hres : res with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (hfirst 0 (h0 hres)) fun s₁ ⟨⟨h3, hm⟩, k₁⟩ => ?_)
    refine WP.ite true (by rw [eval_zero, h3]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (finNone_ok (up := up) (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h.x0) h256 (by rw [hm]; exact hU)
      (by rw [k₁.wr]; exact ho.upw)) fun t ht => ?_
    exact (KEnd.of_fin (ho.congr k₁.wr) ht).trans_pre (by rw [hm]) (k₁.mono (by decide))
  · obtain ⟨hS, hu⟩ := h1 b rest hres
    refine WP.seq (WP.mono (hfirst _ hS) fun s₁ ⟨⟨h3, hm⟩, k₁⟩ => ?_)
    refine WP.ite false (by rw [eval_zero, h3]; cases b <;> rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (if b then 0 else 1) ∧
      t.mem = s₁.mem) (by brun [h3]; cases b <;> rfl) (by decide) (by decide) (by decide +kernel))
      fun s₂ ⟨⟨h3₂, hm₂⟩, k₂⟩ => ?_)
    have k12 := k₁.trans k₂
    have hm12 : s₂.mem = s.mem := hm₂.trans hm
    have ho₂ := ho.congr k12.wr
    refine WP.ite b (by rw [eval_zero, h3₂]; cases b <;> rfl) (fun hb => ?_) (fun hb => ?_)
    · subst hb
      have h₂ : Ws s₂ B Z w := h.congr' (rs := []) (fun x _ => by rw [hm12]) (by simp) k12 (by decide)
      refine WP.mono (finPrimeL_ok (u := r.length - rest.length) (c := c) (up := up) (op := op) h₂ hL1 hLw
        (by rw [hm12]; exact hu) (by rw [hm12]; exact hO) (by rw [hm12]; exact hK) (by rw [hm12]; exact hU)
        (by rw [hm12]; exact hM) ho₂ (by rw [hm12]; exact hn)) fun t ht => ?_
      exact ht.trans_pre (by rw [hm12]) (k12.mono (by decide))
    · subst hb
      refine WP.mono (finUsed_ok (u := r.length - rest.length) (up := up) (hs.congr k12.wr)
        ((k12.gpr .x0 (by decide)).trans h.x0) h256 (by decide) (by rw [hm12]; exact hu) (by rw [hm12]; exact hU)
        ho₂.upw) fun t ht => ?_
      exact (KEnd.of_fin ho₂ ht).trans_pre (by rw [hm12]) (k12.mono (by decide))

/-- `qResult`, after `q`'s Miller–Rabin ended with `res`, not passing. -/
theorem qResult_ok {s : State} {B : Addr} {Z w c L : Nat} {op up : Addr} {r : List Byte}
    {res : Option (Bool × List Byte)} (h : Ws s B Z w) (ho : OutUp s B Z op up L)
    (hU : word s.mem B (8 * kUsedP) = up)
    (hnp : ∀ rest, res ≠ some (true, rest))
    (h0 : res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0)
    (h1 : ∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 2) ∧
      word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) :
    WP isa qResult s fun t => PTEnd s t op up L r c res := by
  have hs := h.scr
  have hnw := hs.nowrap
  have h256 := h.h256
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kStat)) 8 := hs.ld (by simp only [kStat, sFn]; omega_using [h256])
  unfold qResult
  have hfirst : ∀ v : Nat, word s.mem B (8 * kStat) = BitVec.ofNat 64 v →
      WP isa (.block [ldh .x3 kStat]) s fun t => (t.gpr .x3 = BitVec.ofNat 64 v ∧ t.mem = s.mem) ∧ Keep [.x3] s t :=
    fun v hv => WP.keep [.x3] (by brun [h.x0, hdr_enc (show kStat < 32 by decide), hl, hv]) (by decide) (by decide)
      (by decide +kernel)
  rcases hres : res with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (hfirst 0 (h0 hres)) fun s₁ ⟨⟨h3, hm⟩, k₁⟩ => ?_)
    refine WP.ite true (by rw [eval_zero, h3]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (finNone_ok (up := up) (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h.x0) h256 (by rw [hm]; exact hU)
      (by rw [k₁.wr]; exact ho.upw)) fun t ht => ?_
    exact (KEnd.of_fin (ho.congr k₁.wr) ht).trans_pre (by rw [hm]) (k₁.mono (by decide))
  · cases b
    · obtain ⟨hS, hu⟩ := h1 false rest hres
      refine WP.seq (WP.mono (hfirst _ hS) fun s₁ ⟨⟨h3, hm⟩, k₁⟩ => ?_)
      refine WP.ite false (by rw [eval_zero, h3]; rfl) (fun h => absurd h (by decide)) (fun _ => ?_)
      refine WP.mono (finUsed_ok (u := r.length - rest.length) (up := up) (hs.congr k₁.wr)
        ((k₁.gpr .x0 (by decide)).trans h.x0) h256 (by decide) (by rw [hm]; exact hu) (by rw [hm]; exact hU)
        (by rw [k₁.wr]; exact ho.upw)) fun t ht => ?_
      exact (KEnd.of_fin (ho.congr k₁.wr) ht).trans_pre (by rw [hm]) (k₁.mono (by decide))
    · exact absurd hres (hnp rest)

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-! ### `Ffdh.AArch64.ParameterCandidate.ShapeOk`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.ParameterCandidate.Residue`, which only this module used -/

section

/-!
# An FFDH parameter candidate on AArch64: the generator's congruence

`residue` (`residue_ok`): `r = c mod e`, `e` 24 for the generator 2 and 10
for 5, and `fBad := resFlag g r`, zero exactly for `r = 11` (generator 2)
or `r ∈ {3, 7}` (generator 5). The sum `S` of the halves of 32 bits of
`aN`'s words (`hsum`, `halfSum_ok`) is congruent to `c` modulo 3 and 5,
which divide `2³² − 1` (`wv_hsum_mod`), so `T = 105 (c mod 8) + 16 S` is
congruent to `c` modulo 24 and 10, and `reduce` (`reduce_ok`) takes `T`'s
remainder by `umulh` with `e`'s reciprocal (`redBV_24`, `redBV_10`), which
`modSelect` (`modSelect_ok`) chose with `e`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The modulus of the congruence: 10 for the generator 5, 24 for 2. -/
def resMod (g : Nat) : Nat := if 3 ≤ g then 10 else 24

/-- The congruence's flag for the remainder `r`. -/
def resFlag (g : Nat) (r : BitVec 64) : BitVec 64 :=
  if 3 ≤ g then (r ||| BitVec.ofNat 64 4) ^^^ BitVec.ofNat 64 7 else r ^^^ BitVec.ofNat 64 11

theorem resFlag_two {r : Nat} (hr : r < 24) : resFlag 2 (BitVec.ofNat 64 r) = 0 ↔ r = 11 := by
  unfold resFlag
  simp only [show ¬ 3 ≤ 2 by decide, ite_false]
  revert r; decide

theorem resFlag_five {r : Nat} (hr : r < 10) : resFlag 5 (BitVec.ofNat 64 r) = 0 ↔ r = 3 ∨ r = 7 := by
  unfold resFlag
  simp only [show 3 ≤ 5 by decide, ite_true]
  revert r; decide

/-- The congruence's flag is zero exactly for the generator's congruence. -/
theorem resFlag_zero {g c : Nat} (hg : g = 2 ∨ g = 5) :
    resFlag g (BitVec.ofNat 64 (c % resMod g)) = 0 ↔
      (if g = 2 then c % 24 = 11 else g = 5 ∧ (c % 10 = 3 ∨ c % 10 = 7)) := by
  rcases hg with rfl | rfl
  · rw [resFlag_two (by unfold resMod; simp only [show ¬ 3 ≤ 2 by decide, ite_false]; omega_arith)]
    simp [resMod]
  · rw [resFlag_five (by unfold resMod; simp only [show 3 ≤ 5 by decide, ite_true]; omega_arith)]
    simp [resMod]

/-! ### The sum of the words' halves -/

/-- The sum of the halves of 32 bits of the `k` words at `o`. -/
def hsum (m : Mem) (B : Addr) (o : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => hsum m B o k + ((word m B (o + 8 * k)).toNat / 2 ^ 32 + (word m B (o + 8 * k)).toNat % 2 ^ 32)

theorem hsum_le (m : Mem) (B : Addr) (o : Nat) : ∀ k, hsum m B o k ≤ k * 2 ^ 33
  | 0 => Nat.le_refl _
  | k + 1 => by
    have h1 := hsum_le m B o k
    have h2 := (word m B (o + 8 * k)).isLt
    show hsum m B o k + ((word m B (o + 8 * k)).toNat / 2 ^ 32 + (word m B (o + 8 * k)).toNat % 2 ^ 32) ≤
      (k + 1) * 2 ^ 33
    rw [Nat.add_mul, Nat.one_mul]
    omega_using [h1, h2]

/-- Modulo a divisor of `2³² − 1`, a number is the sum of its words' halves. -/
theorem wv_hsum_mod {d : Nat} (hd : 2 ^ 32 % d = 1) (m : Mem) (B : Addr) (o : Nat) :
    ∀ k, wv m B o k % d = hsum m B o k % d
  | 0 => rfl
  | k + 1 => by
    have hd1 : 1 % d = 1 := by
      rcases Nat.lt_or_ge d 2 with h | h
      · have : d = 0 ∨ d = 1 := by omega_using [h]
        rcases this with rfl | rfl <;> simp at hd
      · exact Nat.mod_eq_of_lt h
    have hp : 2 ^ (64 * k) % d = 1 := by
      rw [show 64 * k = 32 * (2 * k) by omega_using [], Nat.pow_mul, Nat.pow_mod, hd, Nat.one_pow, hd1]
    rw [wv, hsum]
    generalize (word m B (o + 8 * k)).toNat = W
    have hW : W % d = (W / 2 ^ 32 + W % 2 ^ 32) % d := by
      conv => lhs; rw [← Nat.div_add_mod W (2 ^ 32), Nat.add_mod, Nat.mul_mod, hd, Nat.one_mul, Nat.mod_mod,
        ← Nat.add_mod]
    have e1 : (wv m B o k + 2 ^ (64 * k) * W) % d = (hsum m B o k + W) % d := by
      conv => lhs; rw [Nat.add_mod, Nat.mul_mod, hp, Nat.one_mul, Nat.mod_mod, wv_hsum_mod hd m B o k,
        ← Nat.add_mod]
    have e2 : (hsum m B o k + (W / 2 ^ 32 + W % 2 ^ 32)) % d = (hsum m B o k + W) % d := by
      conv => lhs; rw [Nat.add_mod, ← hW, ← Nat.add_mod]
    rw [e1, e2]

/-- A word's halves, as `halfSum` takes them. -/
theorem halves_bv (x : BitVec 64) :
    x >>> 32 + (x - (x >>> 32) <<< 32) = BitVec.ofNat 64 (x.toNat / 2 ^ 32 + x.toNat % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega_using [hx]

/-- The sum's start: `aN`'s base, its low word, the count and the sum. -/
theorem residueHead_ok {s : State} {p : PP} {w : Nat} (h : PSt p w s) :
    WP isa (.block (ws ++ base aN .x16 ++ ([ld .x2 .x16, mov .x14 .x12, movi .x3 0] : List Instr))) s fun t =>
      (t.gpr .x16 = off p.B (slot w aN) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x3 = 0 ∧
        t.gpr .x2 = word s.mem p.B (slot w aN) ∧ t.mem = s.mem) ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have sN := hws.sl (show aN < 16 by decide)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono hws.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aN .x16 ((k₁.gpr .x0 (by decide)).trans hws.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have e12 : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  have hm₂ : s₂.mem = s.mem := m₂.trans m₁
  refine WP.mono (WP.keep [.x2, .x14, .x3] (Q := fun t =>
      t.gpr .x16 = off p.B (slot w aN) ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x3 = 0 ∧
        t.gpr .x2 = word s.mem p.B (slot w aN) ∧ t.mem = s.mem) (by
    brun [h16, e12, hm₂, hs₂.ld (d := slot w aN) (by omega_arith), imm16 (show 0 < 65536 by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hq, k₃⟩ => ⟨hq, (k12.trans k₃).mono (by decide)⟩

/-- `countLoop .x14 halfSum`: the sum of the halves of the `n` words at
`x16` into `x3`. -/
theorem halfSum_ok {s : State} {B : Addr} {Z d n : Nat} (hs : Scr s B Z) (h16 : s.gpr .x16 = off B d)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 n) (h3 : s.gpr .x3 = 0) (hn : 1 ≤ n) (hn' : n < 2 ^ 24)
    (hZ : d + 8 * n ≤ Z) :
    WP isa (countLoop .x14 halfSum) s fun t =>
      t.mem = s.mem ∧ t.gpr .x3 = BitVec.ofNat 64 (hsum s.mem B d n) ∧
        Keep [.x3, .x4, .x5, .x6, .x14, .x16] s t := by
  have hnw := hs.nowrap
  let Inv : Nat → State → Prop := fun i t => t.mem = s.mem ∧ t.gpr .x16 = off B (d + 8 * i) ∧
    t.gpr .x3 = BitVec.ofNat 64 (hsum s.mem B d i) ∧ Keep [.x3, .x4, .x5, .x6, .x14, .x16] s t
  unfold halfSum
  refine WP.mono (wp_countdown (N := n) (by omega_using [hn']) (by omega_using [hn]) Inv
    (fun i hi t ⟨jm, j16, j3, jk⟩ _ => ?_) ⟨rfl, by rw [h16]; rfl, by rw [h3]; rfl, Keep.refl _ _⟩ h14)
    fun t ⟨tm, _, t3, tk⟩ => ⟨tm, t3, tk⟩
  have hst := hs.congr jk.wr
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x14, .x16] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .x16 = off B (d + 8 * (i + 1)) ∧
      t'.gpr .x3 = t.gpr .x3 + word s.mem B (d + 8 * i) >>> 32 +
        (word s.mem B (d + 8 * i) - (word s.mem B (d + 8 * i) >>> 32) <<< 32) ∧
      t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1) (by
    brun [j16, jm, hst.ld (show d + 8 * i + 8 ≤ Z by omega_using [hZ, hi]), off_add,
      show d + 8 * i + 8 = d + 8 * (i + 1) by omega_using []])
    (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨m', a16, a3, a14⟩, k'⟩ =>
      ⟨⟨by rw [m', jm], a16, ?_, (jk.trans k').mono⟩, a14⟩
  rw [a3, j3, BitVec.add_assoc, halves_bv, ← BitVec.ofNat_add]
  rfl

/-! ### The remainder by the reciprocal -/

/-- `reduce`'s value, for the divisor `e` and its reciprocal `M`. -/
def redBV (e M : Nat) (L : BitVec 64) (S : Nat) : BitVec 64 :=
  BitVec.ofNat 64 S * BitVec.ofNat 64 16 + (L &&& BitVec.ofNat 64 7) * BitVec.ofNat 64 105 -
    BitVec.ofNat 64 ((BitVec.ofNat 64 S * BitVec.ofNat 64 16 + (L &&& BitVec.ofNat 64 7) * BitVec.ofNat 64 105).toNat *
      (BitVec.ofNat 64 M).toNat / 2 ^ 64) * BitVec.ofNat 64 e

/-- `T = 105 (L mod 8) + 16 S`, as `reduce` computes it. -/
theorem redT (L : BitVec 64) (S : Nat) :
    BitVec.ofNat 64 S * BitVec.ofNat 64 16 + (L &&& BitVec.ofNat 64 7) * BitVec.ofNat 64 105 =
      BitVec.ofNat 64 (105 * (L.toNat % 8) + 16 * S) := by
  have h7 : (L &&& BitVec.ofNat 64 7).toNat = L.toNat % 8 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (7 : Nat) % 2 ^ 64 = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h7, Nat.reducePow, Nat.reduceMod]
  omega_using []

/-- The remainder modulo 24 by `⌈2⁶⁴ / 24⌉`. -/
theorem redBV_24 (L : BitVec 64) {S : Nat} (hS : 16 * S + 735 < 2 ^ 61) :
    redBV 24 recip24 L S = BitVec.ofNat 64 ((105 * (L.toNat % 8) + 16 * S) % 24) := by
  have h8 := Nat.mod_lt L.toNat (show 0 < 8 by decide)
  have hT : 105 * (L.toNat % 8) + 16 * S < 2 ^ 61 := by omega_using [hS, h8]
  unfold redBV
  rw [redT L S]
  generalize 105 * (L.toNat % 8) + 16 * S = T at hT ⊢
  have hq : T * 768614336404564651 / 18446744073709551616 = T / 24 := by omega_using [hT]
  have hp : BitVec.ofNat 64 (T / 24) * BitVec.ofNat 64 24 = BitVec.ofNat 64 (T / 24 * 24) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega_using [hT]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hT]),
    show (BitVec.ofNat 64 recip24).toNat = 768614336404564651 from rfl, show (2 : Nat) ^ 64 = 18446744073709551616 from rfl, hq, hp,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hT]) (Nat.div_mul_le_self T 24),
    show T - T / 24 * 24 = T % 24 by omega_using []]

/-- The remainder modulo 10 by `⌈2⁶⁴ / 10⌉`. -/
theorem redBV_10 (L : BitVec 64) {S : Nat} (hS : 16 * S + 735 < 2 ^ 61) :
    redBV 10 recip10 L S = BitVec.ofNat 64 ((105 * (L.toNat % 8) + 16 * S) % 10) := by
  have h8 := Nat.mod_lt L.toNat (show 0 < 8 by decide)
  have hT : 105 * (L.toNat % 8) + 16 * S < 2 ^ 61 := by omega_using [hS, h8]
  unfold redBV
  rw [redT L S]
  generalize 105 * (L.toNat % 8) + 16 * S = T at hT ⊢
  have hq : T * 1844674407370955162 / 18446744073709551616 = T / 10 := by omega_using [hT]
  have hp : BitVec.ofNat 64 (T / 10) * BitVec.ofNat 64 10 = BitVec.ofNat 64 (T / 10 * 10) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega_using [hT]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hT]),
    show (BitVec.ofNat 64 recip10).toNat = 1844674407370955162 from rfl, show (2 : Nat) ^ 64 = 18446744073709551616 from rfl, hq, hp,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using [hT]) (Nat.div_mul_le_self T 10),
    show T - T / 10 * 10 = T % 10 by omega_using []]

/-- The reciprocals, into `x7` and `x6`. -/
theorem recips_ok (s : State) :
    WP isa (.block (loadWord .x7 recip10 ++ loadWord .x6 recip24)) s fun t =>
      (t.gpr .x7 = BitVec.ofNat 64 recip10 ∧ t.gpr .x6 = BitVec.ofNat 64 recip24 ∧ t.mem = s.mem) ∧
        Keep [.x6, .x7] s t := by
  unfold loadWord
  -- Kept opaque: `simp` would otherwise evaluate the pieces.
  generalize recip10 = W₁
  generalize recip24 = W₂
  refine WP.keep [.x6, .x7] ?_ rfl rfl rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, List.cons_append, List.nil_append,
    exec_movz_x' (show 0 < 4 by decide), exec_movk_x (show 1 < 4 by decide), exec_movk_x (show 2 < 4 by decide),
    exec_movk_x (show 3 < 4 by decide), RegUpd.gpr_write, RegUpd.mem_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left', BitVec.setWidth_eq, movk_word, and_true]

/-- The generator's reciprocal. -/
def resRecip (g : Nat) : Nat := if 3 ≤ g then recip10 else recip24

/-- `modSelect`: the generator's modulus and its reciprocal. -/
theorem modSelect_ok {s : State} {p : PP} {w : Nat} (h : PSt p w s) (h7 : s.gpr .x7 = BitVec.ofNat 64 recip10)
    (h6 : s.gpr .x6 = BitVec.ofNat 64 recip24) :
    WP isa (.block modSelect) s fun t =>
      (t.gpr .x7 = BitVec.ofNat 64 (resRecip p.g) ∧ t.gpr .x13 = BitVec.ofNat 64 (resMod p.g) ∧ t.mem = s.mem) ∧
        Keep [.x6, .x7, .x8, .x9, .x10, .x13] s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have hg := h.dims.g
  have h256 := hws.h256
  have hgen := h.args.gen
  unfold modSelect
  refine WP.keep [.x6, .x7, .x8, .x9, .x10, .x13] ?_ (by decide) (by decide) (by decide +kernel)
  rcases hg with hg | hg <;> rw [hg] at hgen ⊢ <;>
  brun [hws.x0, h7, h6, hdr_enc (show fGen < 32 by decide),
    hs.ld (d := 8 * fGen) (by simp only [fGen, sFn]; omega_arith), hgen, resRecip, resMod,
    imm16 (show 3 < 65536 by decide), imm16 (show 10 < 65536 by decide), imm16 (show 24 < 65536 by decide)]

/-- `reduce`: `T = 105 (L mod 8) + 16 S` less `e` times its quotient by the
reciprocal `M`. -/
theorem reduce_ok {s : State} {S e M : Nat} {L : BitVec 64} (h2 : s.gpr .x2 = L)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 S) (h7 : s.gpr .x7 = BitVec.ofNat 64 M)
    (h13 : s.gpr .x13 = BitVec.ofNat 64 e) :
    WP isa (.block reduce) s fun t =>
      (t.gpr .x3 = redBV e M L S ∧ t.mem = s.mem) ∧ Keep [.x2, .x3, .x4] s t := by
  unfold reduce
  refine WP.keep [.x2, .x3, .x4] ?_ (by decide) (by decide) (by decide +kernel)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, movi, exec_movz_x, exec_logic_x, exec_mul_x, exec_add_x,
    exec_umulh, exec_sub_x, RegUpd.gpr_write, RegUpd.mem_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left', BitVec.setWidth_eq, h2, h3, h7, h13, redBV,
    imm16 (show 7 < 65536 by decide), imm16 (show 105 < 65536 by decide), imm16 (show 16 < 65536 by decide),
    and_true]

/-- The flag, from the remainder in `x3`. -/
theorem residueTail_ok {s : State} {p : PP} {w : Nat} {X : BitVec 64} (h : PSt p w s) (h3 : s.gpr .x3 = X) :
    WP isa (.block [ldh .x9 fGen, movi .x6 3, .subs .x .x8 .x9 .x6, movi .x4 4, .logic .orr .x .x5 .x3 .x4,
      .csel .x .x5 .x5 .x3, movi .x6 7, movi .x7 11, .csel .x .x6 .x6 .x7, .logic .eor .x .x5 .x5 .x6,
      sth .x5 fBad]) s fun t =>
      t.mem = s.mem.writeW (off p.B (8 * fBad)) (resFlag p.g X) ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have hg := h.dims.g
  have h256 := hws.h256
  have hgen := h.args.gen
  refine WP.mono (WP.keep [.x9, .x6, .x8, .x4, .x5, .x7] (Q := fun t =>
      t.mem = s.mem.writeW (off p.B (8 * fBad)) (resFlag p.g X)) (by
    rcases hg with hg | hg <;> rw [hg] at hgen ⊢ <;>
    brun [hws.x0, h3, hdr_enc (show fGen < 32 by decide), hdr_enc (show fBad < 32 by decide),
      hs.ld (d := 8 * fGen) (by simp only [fGen, sFn]; omega_arith), hs.st (d := 8 * fBad) (by simp only [fBad]; omega_arith),
      hgen, resFlag, imm16 (show 3 < 65536 by decide), imm16 (show 4 < 65536 by decide),
      imm16 (show 7 < 65536 by decide), imm16 (show 11 < 65536 by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨hm, k⟩ => ⟨hm, k.mono (by decide)⟩

/-- `residue`: the congruence's flag into `fBad`. -/
theorem residue_ok {s : State} {p : PP} {w c : Nat} (h : PSt p w s) (hc : wv s.mem p.B (slot w aN) w = c) :
    WP isa (seqs residue) s fun t =>
      PSt p w t ∧ word t.mem p.B (8 * fBad) = resFlag p.g (BitVec.ofNat 64 (c % resMod p.g)) ∧
      Frm p.B [(8 * fBad, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hws := h.ws
  have hs := hws.scr
  have hn := hs.nowrap
  have hw1 := hws.w1
  have hw2 := hws.w2
  have sN := hws.sl (show aN < 16 by decide)
  have h256 := hws.h256
  simp only [residue, seqs]
  -- The low word and the sum of the halves.
  refine WP.seq (WP.mono (residueHead_ok h) fun s₁ ⟨⟨h16, h14, h3, h2, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (halfSum_ok hs₁ h16 h14 h3 (by omega_arith) hw2 (by omega_arith))
    fun s₂ ⟨hm₂, h3₂, k₂⟩ => ?_)
  rw [hm₁] at h3₂
  -- The reciprocals.
  refine WP.seq (WP.mono (recips_ok s₂) fun s₃ ⟨⟨h7, h6, hm₃⟩, k₃⟩ => ?_)
  have k13 := (k₁.trans k₂).trans k₃
  have mem₃ : s₃.mem = s.mem := by rw [hm₃, hm₂, hm₁]
  have st₃ : PSt p w s₃ := h.step (rs := []) (hws.congr' (rs := []) (by rw [mem₃]; exact Frm.refl _ _ _)
    (by simp) k13 (by decide)) (by rw [mem₃]; exact Frm.refl _ _ _) (by simp) (by simp) k13
  -- The modulus and its reciprocal, and the remainder.
  refine WP.seq (WP.mono (modSelect_ok st₃ h7 h6) fun s₃' ⟨⟨h7', h13', hm₃'⟩, k₃'⟩ => ?_)
  have hS := hsum_le s.mem p.B (slot w aN) w
  have hS' : 16 * hsum s.mem p.B (slot w aN) w + 735 < 2 ^ 61 := by omega_arith
  refine WP.seq (WP.mono (reduce_ok
    ((k₃'.gpr .x2 (by decide)).trans ((k₃.gpr .x2 (by decide)).trans ((k₂.gpr .x2 (by decide)).trans h2)))
    ((k₃'.gpr .x3 (by decide)).trans ((k₃.gpr .x3 (by decide)).trans h3₂)) h7' h13')
    fun s₄ ⟨⟨h3₄, hm₄⟩, k₄⟩ => ?_)
  have k14 := (k13.trans k₃').trans k₄
  have mem₄ : s₄.mem = s.mem := hm₄.trans (hm₃'.trans mem₃)
  have st₄ : PSt p w s₄ := h.step (rs := []) (hws.congr' (rs := []) (by rw [mem₄]; exact Frm.refl _ _ _)
    (by simp) k14 (by decide)) (by rw [mem₄]; exact Frm.refl _ _ _) (by simp) (by simp) k14
  have h3' : s₄.gpr .x3 = BitVec.ofNat 64 (c % resMod p.g) := by
    have hl : (word s.mem p.B (slot w aN)).toNat = c % 2 ^ 64 := by rw [← hc, wv_mod64 _ _ _ (by omega_arith)]
    have m3 : c % 3 = hsum s.mem p.B (slot w aN) w % 3 := by rw [← hc]; exact wv_hsum_mod (by decide) _ _ _ _
    have m5 : c % 5 = hsum s.mem p.B (slot w aN) w % 5 := by rw [← hc]; exact wv_hsum_mod (by decide) _ _ _ _
    rw [h3₄]
    rcases h.dims.g with hg | hg
    · rw [hg, show resMod 2 = 24 from rfl, show resRecip 2 = recip24 from rfl, redBV_24 _ hS']
      refine congrArg (BitVec.ofNat 64) ?_
      omega_using [hl, m3]
    · rw [hg, show resMod 5 = 10 from rfl, show resRecip 5 = recip10 from rfl, redBV_10 _ hS']
      refine congrArg (BitVec.ofNat 64) ?_
      omega_using [hl, m5]
  refine WP.mono (residueTail_ok st₄ h3') fun t ⟨hm, k₅⟩ => ?_
  have hf : Frm p.B [(8 * fBad, 8)] s.mem t.mem := by
    rw [hm, mem₄]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [fBad]; omega_arith)) (by simp)
  refine ⟨h.step (hws.congr' hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.hdr (by decide))
      (k14.trans k₅) (by decide)) hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact PMut.hdr (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; simp only [fBad]; omega_arith) (k14.trans k₅), ?_, hf,
    (k14.trans k₅).mono (by decide)⟩
  rw [hm, word_writeW_self]

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end


/-!
# An FFDH parameter candidate on AArch64: the shape's flag

`shapeFlag g w c`, the value `fBad` ends with for the candidate `c` in `w`
words: zero exactly when `c` has the generator's shape and `c` and
`(c − 1) / 2` pass `primeShape` and RSA's trial division,
`obviouslyComposite` (`shapeFlag_zero`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.Proof.Bignum VG.Proof.RsaKeyGen.AArch64 VG.Spec.Ffdh VG.Impl.RsaKeyGen

/-- The flag of the shape checks of `c`. -/
def shapeFlag (g w c : Nat) : BitVec 64 :=
  resFlag g (BitVec.ofNat 64 (c % resMod g)) ||| mask (anyPre c (4 * trialN w)) ||| evenFlag (c / 2) |||
    mask (anyPre (c / 2) (4 * trialN w))

theorem mask_eq_zero (b : Bool) : mask b = 0 ↔ b = false := by cases b <;> decide

/-- Above the table's largest prime, the sieve of `4 (trialN (mW bits))`
entries is `primeShape` and RSA's trial division for `bits`. -/
theorem sieved_sieve {bits c : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hc : 8161 < c) (ho : c % 2 = 1) :
    (primeShape c && !Spec.RsaKeyGen.obviouslyComposite bits c) = !anyPre c (4 * trialN (mW bits)) := by
  rw [VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve hc ho]
  have ht : anyPre c (4 * trialN (mW bits)) = Spec.RsaKeyGen.obviouslyComposite bits c := by
    have e := VG.Proof.RsaKeyGen.trialAny_eq (w := mW bits) hc
    have e2 : Spec.RsaKeyGen.obviouslyComposite (64 * mW bits) c = Spec.RsaKeyGen.obviouslyComposite bits c := by
      unfold Spec.RsaKeyGen.obviouslyComposite Spec.RsaKeyGen.trialPrimes
      have : (1024 < 64 * mW bits) = (1024 < bits) := propext (by simp only [mW]; omega)
      simp only [this]
    rw [← e2, ← e]
    rfl
  rw [← ht]
  have h53 : ((List.range 53).any fun i => c % tabEntry i == 0) = anyPre c 53 := rfl
  rw [h53]
  have hle : 53 ≤ 4 * trialN (mW bits) := by unfold trialN; split <;> omega_using []
  cases h4 : anyPre c (4 * trialN (mW bits))
  · cases h5 : anyPre c 53
    · rfl
    · exact absurd (anyPre_mono hle h5) (by rw [h4]; decide)
  · cases anyPre c 53 <;> rfl

theorem shapeFlag_zero {bits g x : Nat} (hb1 : 512 ≤ bits) (hb2 : bits ≤ 8192) (hg : g = 2 ∨ g = 5) :
    shapeFlag g (mW bits) (candidateOf bits x) = 0 ↔
      (generationShape bits g (candidateOf bits x) && primeShape (candidateOf bits x) &&
        primeShape ((candidateOf bits x - 1) / 2) &&
        !Spec.RsaKeyGen.obviouslyComposite bits (candidateOf bits x) &&
        !Spec.RsaKeyGen.obviouslyComposite bits ((candidateOf bits x - 1) / 2)) = true := by
  obtain ⟨ho, hl, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := bits) (by omega_using [hb1]) x
  have hlen := (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := bits) (by omega_using [hb1]) x).1
  generalize candidateOf bits x = c at ho hl hlen ⊢
  have hbig : 2 ^ 14 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega_using [hb1])
  have hq : (c - 1) / 2 = c / 2 := by omega_using [ho]
  rw [hq]
  have reorder (a b c d e : Bool) : (a && b && c && !d && !e) = (a && (b && !d) && (c && !e)) := by
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl
  rw [reorder, sieved_sieve hb1 hb2 (by omega) ho]
  have hgen : generationShape bits g c = (if g = 2 then decide (c % 24 = 11) else
      decide (g = 5 ∧ (c % 10 = 3 ∨ c % 10 = 7))) := by
    unfold generationShape
    rcases hg with rfl | rfl <;> simp only [hb1, hb2, hlen, decide_true, beq_self_eq_true, Bool.and_true,
      Bool.true_and, ite_true, show ¬ (5 = 2) by decide, ite_false, true_and,
      Bool.decide_or, Nat.reduceBEq, Bool.false_eq_true] <;> simp only [trial_decide_beq]
  simp only [shapeFlag, VG.Proof.Rsa.AArch64.or_eq_zero, mask_eq_zero, evenFlag_zero, resFlag_zero hg]
  rw [hgen]
  rcases Nat.mod_two_eq_zero_or_one (c / 2) with hq2 | hq2
  · have hpq : primeShape (c / 2) = false := by
      unfold primeShape; simp [hq2]
    rw [hpq]
    simp only [hq2, Bool.false_and, Bool.and_false]
    simp
  · rw [sieved_sieve hb1 hb2 (by omega) hq2]
    rcases hg with rfl | rfl <;> simp [hq2]

/-! ### The flag, as the code's checks build it -/

/-- The flag after the congruence. -/
abbrev scr1 (g c : Nat) : BitVec 64 := resFlag g (BitVec.ofNat 64 (c % resMod g))

/-- After the sieve of `c` by the table's first words. -/
abbrev scr2 (g w c : Nat) : BitVec 64 := scr1 g c ||| mask (anyPre c (4 * sieveWords true w))

/-- After the oddness of `c / 2`. -/
abbrev scr3 (g w c : Nat) : BitVec 64 := scr2 g w c ||| evenFlag (c / 2)

/-- After the sieve of `c / 2`. -/
abbrev scr4 (g w c : Nat) : BitVec 64 := scr3 g w c ||| mask (anyPre (c / 2) (4 * sieveWords false w))

/-- After the whole sieve of `c`. -/
abbrev scr5 (g w c : Nat) : BitVec 64 := scr4 g w c ||| mask (anyPre c (4 * sieveWords false w))

/-- The last is the shape's flag, but for the first words, which are among
the whole sieve's. -/
theorem scr5_zero {g w c : Nat} : scr5 g w c = 0 ↔ shapeFlag g w c = 0 := by
  simp only [scr5, scr4, scr3, scr2, scr1, shapeFlag, VG.Proof.Rsa.AArch64.or_eq_zero, mask_eq_zero,
    sieveWords_false]
  constructor
  · rintro ⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩
    exact ⟨⟨⟨h1, h5⟩, h3⟩, h4⟩
  · rintro ⟨⟨⟨h1, h5⟩, h3⟩, h4⟩
    refine ⟨⟨⟨⟨h1, ?_⟩, h3⟩, h4⟩, h5⟩
    cases h : anyPre c (4 * sieveWords true w)
    · rfl
    · rw [anyPre_mono (Nat.mul_le_mul_left 4 (sieveWords_trialN true w)) h] at h5
      cases h5

theorem or_ne_zero {x : BitVec 64} (y : BitVec 64) (h : x ≠ 0) : x ||| y ≠ 0 :=
  fun h0 => h ((VG.Proof.Rsa.AArch64.or_eq_zero _ _).mp h0).1

/-- A check that fails: the shape's flag is not zero. -/
theorem shape_ne {g w c : Nat}
    (h : scr1 g c ≠ 0 ∨ scr2 g w c ≠ 0 ∨ scr3 g w c ≠ 0 ∨ scr4 g w c ≠ 0 ∨ scr5 g w c ≠ 0) :
    shapeFlag g w c ≠ 0 := by
  have h5 : scr5 g w c ≠ 0 := by
    rcases h with h | h | h | h | h
    · exact or_ne_zero _ (or_ne_zero _ (or_ne_zero _ (or_ne_zero _ h)))
    · exact or_ne_zero _ (or_ne_zero _ (or_ne_zero _ h))
    · exact or_ne_zero _ (or_ne_zero _ h)
    · exact or_ne_zero _ h
    · exact h
  exact fun h0 => h5 (scr5_zero.mpr h0)

end VG.Proof.Ffdh.AArch64.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on AArch64: `main`

`tests_ok`: one witness of `p`, all of `q`'s, then `p`'s others
(`Proof.Ffdh.ParameterCandidate.sievedTests`); `main_ok`: `p`, its shape's checks, and the tests, as
`Spec.Ffdh.sievedParameterCandidate` (`PEnd`): the candidate ends at the first
of the shape's checks that fails (the congruence, `p`'s sieve by the
table's first words, `q`'s oddness, `q`'s sieve, then `p`'s whole sieve),
each a part of the flag so far (`scr1` to `scr5`, `ShapeOk.lean`), which
is then not zero, as the shape's flag (`shapeFlag`) then is. The checks'
pieces are the stages `stgA_ok` to `stgTests_ok`, each from the state
between two of them (`Stg`), which `CTMain.lean` runs too.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eq_zero_iff)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses onPass sievedTests sieved_eq)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- How the candidate ends, from `s`, for the specification's result. -/
def PEnd (s t : State) (p : PP) : Option (Option Nat × List Byte) → Prop
  | none => KEnd s t p.op p.up p.L 0 0 none
  | some (some c, rest) => KEnd s t p.op p.up p.L 1 (p.r.length - rest.length) (some c)
  | some (none, rest) => KEnd s t p.op p.up p.L 2 (p.r.length - rest.length) none

theorem PEnd.trans_pre {s₀ s t : State} {p : PP} {res : Option (Option Nat × List Byte)} (h : PEnd s t p res)
    (hout : outBytes s.mem p.op p.L = outBytes s₀.mem p.op p.L) (k₀ : Keep mmRegs s₀ s) : PEnd s₀ t p res := by
  rcases res with _ | ⟨_ | _, _⟩ <;> exact KEnd.trans_pre h hout (k₀.mono (by decide))

/-- `kStat` against 1. -/
theorem stat1_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {v : Nat} (hv : v < 2 ^ 63) (hS : word s.mem B (8 * kStat) = BitVec.ofNat 64 v) :
    WP isa (.block [ldh .x3 kStat, .subImm .x .x3 .x3 1]) s fun t =>
      isa.eval (.zero .x .x3) t = some (decide (v = 1)) ∧ t.mem = s.mem ∧ Keep [.x3] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hS' : s.mem.readW (B + BitVec.ofNat 64 (8 * kStat)) 64 = BitVec.ofNat 64 v := hS
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 v - BitVec.ofNat 64 1 ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kStat < 32 by decide), h.scr.ld (d := 8 * kStat) (by simp only [kStat, sFn]; omega_arith),
      hS']) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ?_
  refine ⟨?_, hm, k⟩
  rw [eval_zero, h3, eq_zero_iff, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact congrArg some (decide_eq_decide.mpr (by omega_arith))

/-- After a test that ended with `res` from `t₁`: the end of the candidate
when it did not pass (`qResult`), else `cont`, from octet `u` of the tape. -/
theorem stage_ok {p : PP} {w N mb K : Nat} {s s₀ t₁ : State} {res : Option (Bool × List Byte)}
    {k : List Byte → Option (Option Nat × List Byte)} {cont : Prog isa}
    (e₁ : MrEnd p w N mb K s₀ res t₁) (hEZ : slot w aE + 8 * (w + 2) ≤ p.Z)
    (ho : outBytes t₁.mem p.op p.L = outBytes s.mem p.op p.L) (hk : Keep mmRegs s t₁)
    (hcont : ∀ u t₂, u ≤ p.r.length → res = some (true, p.r.drop u) → MrFix p w N mb K t₂ → t₂.mem = t₁.mem →
      Keep [.x3] t₁ t₂ → word t₂.mem p.B (8 * kUsed) = BitVec.ofNat 64 u →
      WP isa cont t₂ fun t => PEnd s t p (k (p.r.drop u))) :
    WP isa (seqs [.block [ldh .x3 kStat, .subImm .x .x3 .x3 1], .ite (.zero .x .x3) cont qResult]) t₁
      fun t => PEnd s t p (onPass res k) := by
  obtain stt := MrEnd.stat e₁
  obtain ⟨fix₁, -, hrest₁, -, -⟩ := e₁
  have ho₁ := fix₁.st.ou
  simp only [seqs]
  obtain hv : ∀ v, word t₁.mem p.B (8 * kStat) = BitVec.ofNat 64 v → v ≤ 2 →
      WP isa (.block [ldh .x3 kStat, .subImm .x .x3 .x3 1]) t₁ fun t =>
        isa.eval (.zero .x .x3) t = some (decide (v = 1)) ∧ MrFix p w N mb K t ∧ t.mem = t₁.mem ∧
          Keep [.x3] t₁ t :=
    fun v hS hv2 => WP.mono (stat1_ok fix₁.st.ws (by omega_arith) hS) fun t ⟨hz, hm, k⟩ =>
      ⟨hz, fix₁.same hEZ hm k (by decide), hm, k⟩
  obtain fail : ∀ {t₂ : State}, t₂.mem = t₁.mem → Keep [.x3] t₁ t₂ → (∀ rest, res ≠ some (true, rest)) →
      WP isa qResult t₂ fun t => PEnd s t p (onPass res k) := by
    intro t₂ hm kk hnp
    obtain ws₂ := fix₁.st.ws.congr' (rs := []) (by rw [hm]; exact Frm.refl _ _ _) (by simp) kk (by decide)
    refine WP.mono (qResult_ok (c := 0) (L := p.L) (r := p.r) ws₂ (ho₁.congr kk.wr)
      (by rw [hm]; exact fix₁.st.args.usedP) hnp (by rw [hm]; exact stt.1)
      (fun b rest hr => by rw [hm]; exact stt.2 b rest hr)) fun t ht => ?_
    obtain hk₂ : Keep mmRegs s t₂ := (hk.trans kk).mono (by decide)
    obtain ho₂ : outBytes t₂.mem p.op p.L = outBytes s.mem p.op p.L := by rw [hm]; exact ho
    rcases res with _ | ⟨_ | _, rest⟩
    · exact PEnd.trans_pre (p := p) (res := none) ht ho₂ hk₂
    · exact PEnd.trans_pre (p := p) (res := some (none, rest)) ht ho₂ hk₂
    · exact absurd rfl (hnp rest)
  rcases hQ : res with _ | ⟨b, rest⟩
  · refine WP.seq (WP.mono (hv 0 (stt.1 hQ) (by decide)) fun t₂ ⟨hz, _, hm, kk⟩ => ?_)
    refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
    rw [← hQ]; exact fail hm kk (fun rest h' => by rw [hQ] at h'; cases h')
  · obtain ⟨hS, _⟩ := stt.2 b rest hQ
    refine WP.seq (WP.mono (hv (if b then 1 else 2) hS (by cases b <;> decide)) fun t₂ ⟨hz, fix₂, hm, kk⟩ => ?_)
    cases b
    · refine WP.ite false hz (fun h => absurd h (by decide)) (fun _ => ?_)
      rw [← hQ]; exact fail hm kk (fun rest' h' => by rw [hQ] at h'; cases h')
    · refine WP.ite true hz (fun _ => ?_) (fun h => absurd h (by decide))
      obtain ⟨u, hul, rfl, hUu⟩ := (hrest₁ true _ hQ).2
      exact hcont u t₂ hul hQ fix₂ hm kk (by rw [hm]; exact hUu)

/-- The tests, once the shape passed. -/
theorem tests_ok (M : Mont) (R : Kernel) {p : PP} {s : State} {c : Nat} (h : PSt p (mW p.bits) s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L))) (hqo : ((c - 1) / 2) % 2 = 1)
    (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (tests M.mm R.run) s fun t => PEnd s t p (sievedTests c (p.r.drop p.L)) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have h256 := h.ws.h256
  obtain hbq : Spec.RsaKeyGen.bitLength ((c - 1) / 2) = p.bits - 1 := by
    rw [hc]; exact VG.Proof.Ffdh.ParameterCandidate.half_bitLength (by omega_arith) _
  obtain hbp : Spec.RsaKeyGen.bitLength c = p.bits := by
    rw [hc]; exact (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (by omega_arith) _).1
  obtain ⟨hpo, _, hcu⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hcu hpo
  obtain hEZq := h.dims.eZ true
  obtain hmbq : p.mb true = p.bits - 1 := by simp only [PP.mb, ↓reduceIte]
  rw [hmbq] at hEZq
  obtain hEZp := h.dims.eZ false
  obtain hmbp : p.mb false = p.bits := by simp only [PP.mb, Bool.false_eq_true, ↓reduceIte]
  rw [hmbp] at hEZp
  obtain hout : ∀ {t : State}, InScr p.B p.Z s.mem t.mem → outBytes t.mem p.op p.L = outBytes s.mem p.op p.L :=
    fun hi => outBytes_inScr hi h.ou.outZ
  unfold sievedTests
  rw [hbq, hbp]
  unfold tests
  refine wp_seqs_append (by simp [test, phase]) (by simp) ?_
  -- `p`'s first witness.
  refine WP.mono (testP1_ok M R h hc hU hL hL) fun t₁ e₁ => ?_
  refine stage_ok e₁ hEZp (hout e₁.2.2.2.1) e₁.2.2.2.2 fun u₁ t₂ hu₁ _ fix₂ hm₂ k₂ hU₂ => ?_
  obtain isc₂ : InScr p.B p.Z s.mem t₂.mem := by rw [hm₂]; exact e₁.2.2.2.1
  obtain kk₂ : Keep mmRegs s t₂ := (e₁.2.2.2.2.trans k₂).mono (by decide)
  -- `q`, from `p` in `aN`.
  unfold testQ
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [halveQ]) (by simp [test, phase]) ?_
  obtain ⟨_, hc₂⟩ := fix₂.ctx
  have hws₂ := fix₂.st.ws
  have hn₂ := hws₂.scr.nowrap
  refine WP.mono (halveQ_ok fix₂.st hc₂.n rfl) fun t₃ ⟨st₃, hq₃, _, f₃, k₃⟩ => ?_
  obtain hq : (c - 1) / 2 = c / 2 := by omega_arith
  obtain hT₃ : slot (mW p.bits) aN + 8 * (mW p.bits + 2) ≤ p.Z := hws₂.sl (show aN < 16 by decide)
  obtain isc₃ : InScr p.B p.Z s.mem t₃.mem := isc₂.trans (InScr.of_frm f₃ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hT₃
    · simp only [fBad]; omega_arith)
  obtain hU₃ : word t₃.mem p.B (8 * kUsed) = BitVec.ofNat 64 u₁ := by
    rw [f₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl (by simp only [slot, hdrBytes, kUsed, sFn]; omega_arith)
      · exact .inr (by decide)) (by simp only [kUsed, sFn]; omega_arith)]
    exact hU₂
  refine wp_seqs_append (by simp [test, phase]) (by simp) ?_
  refine WP.mono (testQ_ok M R st₃ hc (by rw [hq₃, hq]) hqo hU₃ hu₁ hL) fun t₄ e₄ => ?_
  obtain isc₄ : InScr p.B p.Z s.mem t₄.mem := isc₃.trans e₄.2.2.2.1
  obtain kk₄ : Keep mmRegs s t₄ := ((kk₂.trans k₃).trans e₄.2.2.2.2).mono (by decide)
  refine stage_ok e₄ hEZq (hout isc₄) kk₄ fun u₂ t₅ hu₂ _ fix₅ hm₅ k₅ hU₅ => ?_
  -- `p`'s other witnesses.
  unfold testRest
  refine wp_seqs_append (by simp [test, phase]) (by simp) ?_
  refine WP.mono (testPR_ok M R fix₅.st hc hU₅ hu₂ hL) fun t₆ e₆ => ?_
  obtain stp := MrEnd.stat e₆
  obtain ⟨fix₆, -, -, isc₆, k₆⟩ := e₆
  rw [seqs_one]
  obtain hn₆ : wv t₆.mem p.B (slot (mW p.bits) aN) ((p.L + 7) / 8) = c := by
    obtain ⟨_, hc₆⟩ := fix₆.ctx
    refine wv_low hc₆.n (by simp only [PP.L, mW]; omega_arith)
      (Nat.lt_of_lt_of_le hcu (Nat.pow_le_pow_right (by decide) (by simp only [PP.L]; omega_arith)))
  refine WP.mono (pResult_ok (c := c) (r := p.r) fix₆.st.ws (by simp only [PP.L]; omega_arith)
    (by simp only [PP.L, mW]; omega_arith) hn₆ fix₆.st.ou fix₆.st.args.out fix₆.len fix₆.st.args.usedP fix₆.msk
    stp.1 stp.2) fun t ht => ?_
  obtain hk : Keep mmRegs s t₆ := ((kk₄.trans k₅).trans k₆).mono (by decide)
  obtain ho : outBytes t₆.mem p.op p.L = outBytes s.mem p.op p.L :=
    hout (isc₄.trans ((show InScr p.B p.Z t₄.mem t₅.mem by rw [hm₅]; exact InScr.refl _ _ _).trans isc₆))
  generalize checkWitnesses c (Spec.Ffdh.primeChecks p.bits - 1) (p.r.drop u₂) = resP at ht ⊢
  rcases resP with _ | ⟨_ | _, rest'⟩
  · exact PEnd.trans_pre (p := p) (res := none) ht ho hk
  · exact PEnd.trans_pre (p := p) (res := some (none, rest')) ht ho hk
  · exact PEnd.trans_pre (p := p) (res := some (some c, rest')) ht ho hk

/-- RSA's table survives changes below it. -/
theorem TabOk.frm {m m' : Mem} {B : Addr} {w : Nat} {rs : List (Nat × Nat)} (h : TabOk m B w)
    (hf : Frm B rs m m') (hd : ∀ r ∈ rs, r.1 + r.2 ≤ slot w aTab) (hn : slot w aTab + 2048 ≤ 2 ^ 64) :
    TabOk m' B w := fun i hi => by
  rw [hf.word_eq (fun r hr => Or.inr (by have := hd r hr; omega_arith)) (by omega_arith)]; exact h i hi

/-! ## The shape's checks, stage by stage -/

/-- The candidate. -/
abbrev cOf (p : PP) : Nat := Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L))

/-- RSA's table is in the working space. -/
theorem pTab {p : PP} (h : PDims p) : slot (mW p.bits) aTab + 2048 ≤ p.Z := by
  have := h.z
  have := h.b1
  simp only [slot, hdrBytes, aTab, mW, PP.L] at *
  omega_arith

/-- Between the shape's checks: `n` in `aN`, and the header's words that
`shapeP` and the candidate's end read. -/
structure Stg (p : PP) (n : Nat) (t : State) : Prop where
  st : PSt p (mW p.bits) t
  an : wv t.mem p.B (slot (mW p.bits) aN) (mW p.bits) = n
  used : word t.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L
  len : word t.mem p.B (8 * sK) = BitVec.ofNat 64 p.L
  top : word t.mem p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK p.bits - 1)
  hl : p.L ≤ p.r.length

/-- With the flag `v` so far. -/
def StgF (p : PP) (n : Nat) (v : BitVec 64) (t : State) : Prop := Stg p n t ∧ word t.mem p.B (8 * fBad) = v

/-- With the flag and RSA's table. -/
def StgT (p : PP) (n : Nat) (v : BitVec 64) (t : State) : Prop := StgF p n v t ∧ TabOk t.mem p.B (mW p.bits)

/-- What the shape's checks write: `aN`, the flag and the table. -/
def stgRanges (w : Nat) : List (Nat × Nat) := [(slot w aN, 8 * (w + 2)), (8 * fBad, 8), (slot w aTab, 2048)]

/-- A stage after a piece that writes in `stgRanges` alone and leaves `n'`
in `aN`. -/
theorem Stg.frm {p : PP} {n n' : Nat} {t t' : State} (h : Stg p n t) (st' : PSt p (mW p.bits) t')
    {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem) (hrs : ∀ r ∈ rs, r ∈ stgRanges (mW p.bits))
    (hn : wv t'.mem p.B (slot (mW p.bits) aN) (mW p.bits) = n') :
    Stg p n' t' ∧ InScr p.B p.Z t.mem t'.mem := by
  obtain hT := pTab h.st.dims
  have hn64 := h.st.ws.scr.nowrap
  have h256 := h.st.ws.h256
  obtain hd : ∀ r ∈ rs, ∀ k, k < 32 → k ≠ fBad → 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := fun r hr k hk hkb => by
    have := hrs r hr
    simp only [stgRanges, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact .inl (by simp only [slot, hdrBytes]; omega_arith)
    · simp only [fBad] at hkb ⊢; omega_arith
    · exact .inl (by simp only [slot, hdrBytes]; omega_arith)
  obtain hw : ∀ k, k < 32 → k ≠ fBad → word t'.mem p.B (8 * k) = word t.mem p.B (8 * k) := fun k hk hkb =>
    hf.word_eq (fun r hr => hd r hr k hk hkb) (by omega_arith)
  refine ⟨⟨st', hn, ?_, ?_, ?_, h.hl⟩, InScr.of_frm hf fun r hr => ?_⟩
  · rw [hw kUsed (by decide) (by decide)]; exact h.used
  · rw [hw sK (by decide) (by decide)]; exact h.len
  · rw [hw fTop (by decide) (by decide)]; exact h.top
  · have := hrs r hr
    simp only [stgRanges, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl
    · exact h.st.ws.sl (show aN < 16 by decide)
    · simp only [fBad]; omega_arith
    · exact hT

/-- `p` and its working space. -/
theorem stgA_ok {p : PP} {s : State} (h : PH p s) (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L)
    (hL : p.L ≤ p.r.length) :
    WP isa (seqs (phase false ++ shapeP)) s fun t =>
      Stg p (cOf p) t ∧ InScr p.B p.Z s.mem t.mem ∧ Keep mmRegs s t :=
  WP.mono (pPhase_ok h rfl hU hL hL) fun _ ⟨ht, i, k⟩ => ⟨⟨ht.st, ht.n, ht.used, ht.len, ht.top, hL⟩, i, k⟩

/-- The generator's congruence. -/
theorem stgB_ok {p : PP} {t : State} (h : Stg p (cOf p) t) :
    WP isa (seqs residue) t fun t' =>
      StgF p (cOf p) (scr1 p.g (cOf p)) t' ∧ InScr p.B p.Z t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain sN := h.st.ws.sl (show aN < 16 by decide)
  have hn64 := h.st.ws.scr.nowrap
  refine WP.mono (residue_ok h.st h.an) fun t' ⟨st', hr, f, k⟩ => ?_
  obtain ⟨g, i⟩ := h.frm (n' := cOf p) st' f (fun r hr => by rw [List.mem_singleton.mp hr]; simp [stgRanges]) (by
    rw [f.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (by simp only [slot, hdrBytes, fBad]; omega_arith)) (by omega_arith)]
    exact h.an)
  exact ⟨⟨g, hr⟩, i, k⟩

/-- The flag's load. -/
theorem stgFlag_ok {p : PP} {n : Nat} {v : BitVec 64} {t : State} (h : StgF p n v t) :
    WP isa (.block [ldh .x5 fBad]) t fun t' =>
      (StgF p n v t' ∧ t'.gpr .x5 = v) ∧ t'.mem = t.mem ∧ Keep mmRegs t t' := by
  have hw := h.1.st.ws
  have hn := hw.scr.nowrap
  have h256 := hw.h256
  refine WP.mono (WP.keep [.x5] (Q := fun t' => t'.gpr .x5 = v ∧ t'.mem = t.mem)
    (by brun [hw.x0, hdr_enc (show fBad < 32 by decide), hw.scr.ld (d := 8 * fBad) (by simp only [fBad]; omega_arith),
      h.2]) (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨h5, hm⟩, k⟩ => ?_
  obtain st' : PSt p (mW p.bits) t' := h.1.st.step (rs := []) (hw.congr' (rs := [])
    (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide)) (by rw [hm]; exact Frm.refl _ _ _) (by simp)
    (by simp) k
  exact ⟨⟨⟨⟨st', by rw [hm]; exact h.1.an, by rw [hm]; exact h.1.used, by rw [hm]; exact h.1.len,
    by rw [hm]; exact h.1.top, h.1.hl⟩, by rw [hm]; exact h.2⟩, h5⟩, hm, k.mono (by decide)⟩

/-- RSA's table. -/
theorem stgTab_ok {p : PP} {n : Nat} {v : BitVec 64} {t : State} (h : StgF p n v t) :
    WP isa tableWrite t fun t' => StgT p n v t' ∧ InScr p.B p.Z t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain hT := pTab h.1.st.dims
  obtain sN := h.1.st.ws.sl (show aN < 16 by decide)
  have hn64 := h.1.st.ws.scr.nowrap
  refine WP.mono (tableWrite_ok h.1.st hT) fun t' ⟨st', tab, f, k⟩ => ?_
  obtain ⟨g, i⟩ := h.1.frm (n' := n) st' f (fun r hr => by rw [List.mem_singleton.mp hr]; simp [stgRanges]) (by
    rw [f.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, aN, aTab]; omega_arith))
      (by omega_arith)]
    exact h.1.an)
  refine ⟨⟨⟨g, ?_⟩, tab⟩, i, k⟩
  rw [f.word_eq (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, fBad]; omega_arith))
    (by simp only [fBad]; omega_arith)]
  exact h.2

/-- A sieve of the number in `aN`. -/
theorem stgSieve_ok (first : Bool) {p : PP} {n : Nat} {v : BitVec 64} {t : State} (h : StgT p n v t) :
    WP isa (seqs (sieve first)) t fun t' =>
      StgT p n (v ||| mask (anyPre n (4 * sieveWords first (mW p.bits)))) t' ∧ InScr p.B p.Z t.mem t'.mem ∧
        Keep mmRegs t t' := by
  obtain hT := pTab h.1.1.st.dims
  obtain sN := h.1.1.st.ws.sl (show aN < 16 by decide)
  have hn64 := h.1.1.st.ws.scr.nowrap
  refine WP.mono (sieve_ok first h.1.1.st hT h.2 h.1.1.an h.1.2) fun t' ⟨st', hb, f, k⟩ => ?_
  obtain ⟨g, i⟩ := h.1.1.frm (n' := n) st' f (fun r hr => by rw [List.mem_singleton.mp hr]; simp [stgRanges]) (by
    rw [f.wv_eq (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inr (by simp only [slot, hdrBytes, fBad]; omega_arith)) (by omega_arith)]
    exact h.1.1.an)
  exact ⟨⟨⟨g, hb⟩, h.2.frm f (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [slot, hdrBytes, fBad]; omega_arith) (by omega_arith)⟩, i, k⟩

/-- `q` in `aN`, and its oddness. -/
theorem stgHalve_ok {p : PP} {n : Nat} {v : BitVec 64} {t : State} (h : StgT p n v t) :
    WP isa (seqs halveQ) t fun t' =>
      StgT p (n / 2) (v ||| evenFlag (n / 2)) t' ∧ InScr p.B p.Z t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain hT := pTab h.1.1.st.dims
  obtain sN := h.1.1.st.ws.sl (show aN < 16 by decide)
  have hn64 := h.1.1.st.ws.scr.nowrap
  refine WP.mono (halveQ_ok h.1.1.st h.1.1.an h.1.2) fun t' ⟨st', hq, hb, f, k⟩ => ?_
  obtain ⟨g, i⟩ := h.1.1.frm st' f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [stgRanges]) hq
  exact ⟨⟨⟨g, hb⟩, h.2.frm f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [slot, hdrBytes, aN, aTab]; omega_arith
    · simp only [slot, hdrBytes, fBad]; omega_arith) (by omega_arith)⟩, i, k⟩

/-- `p` in `aN` again. -/
theorem stgShape_ok {p : PP} {n : Nat} {v : BitVec 64} {t : State} (h : StgT p n v t) :
    WP isa (seqs shapeP) t fun t' =>
      StgT p (cOf p) v t' ∧ InScr p.B p.Z t.mem t'.mem ∧ Keep mmRegs t t' := by
  obtain hT := pTab h.1.1.st.dims
  obtain sN := h.1.1.st.ws.sl (show aN < 16 by decide)
  have hn64 := h.1.1.st.ws.scr.nowrap
  refine WP.mono (shapeP_ok h.1.1.st h.1.1.len h.1.1.top h.1.1.hl) fun t' ⟨st', hc, f, k⟩ => ?_
  obtain ⟨g, i⟩ := h.1.1.frm st' f (fun r hr => by rw [List.mem_singleton.mp hr]; simp [stgRanges]) hc
  refine ⟨⟨⟨g, ?_⟩, h.2.frm f (fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [slot, hdrBytes, aN, aTab]; omega_arith) (by omega_arith)⟩, i, k⟩
  rw [f.word_eq (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (by simp only [slot, hdrBytes, fBad]; omega_arith))
    (by simp only [fBad]; omega_arith)]
  exact h.1.2

/-- A candidate whose shape's flag is not zero ends. -/
theorem stgReject_ok {p : PP} {s t : State} {n : Nat} (h : Stg p n t)
    (hz : shapeFlag p.g (mW p.bits) (cOf p) ≠ 0) (i : InScr p.B p.Z s.mem t.mem) (k : Keep mmRegs s t) :
    WP isa (finUsed 2) t fun t' => PEnd s t' p (Spec.Ffdh.sievedParameterCandidate p.bits p.g p.r) := by
  have hL := h.hl
  have h256 := h.st.ws.h256
  obtain hshape := Bool.eq_false_iff.mpr fun h' => hz
    ((shapeFlag_zero (x := Spec.Rsa.os2ip (p.r.take p.L)) h.st.dims.b1 h.st.dims.b2 h.st.dims.g).mpr h')
  rw [sieved_eq hL, hshape]
  simp only [Bool.not_false, ↓reduceIte]
  refine WP.mono (finUsed_end (s := s) h.st.ws.scr h.st.ws.x0 (by omega_arith) (by decide) h.used
    h.st.args.usedP h.st.ou i k) fun t' ht => ?_
  show KEnd s t' p.op p.up p.L 2 (p.r.length - (p.r.drop ((p.bits + 7) / 8)).length) none
  rw [List.length_drop, show p.r.length - (p.r.length - (p.bits + 7) / 8) = p.L by simp only [PP.L] at hL ⊢; omega_arith]
  exact ht

/-- `q` is odd when the shape's flag is zero. -/
theorem qOdd_of_shape {p : PP} (hd : PDims p) (hz : shapeFlag p.g (mW p.bits) (cOf p) = 0) :
    ((cOf p - 1) / 2) % 2 = 1 := by
  obtain hsh := (shapeFlag_zero (x := Spec.Rsa.os2ip (p.r.take p.L)) hd.b1 hd.b2 hd.g).mp hz
  obtain hqs : Spec.Ffdh.primeShape ((cOf p - 1) / 2) = true := by
    simp only [Bool.and_eq_true] at hsh; exact hsh.1.1.2
  unfold Spec.Ffdh.primeShape at hqs
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hqs
  exact hqs.1.2

/-- The tests, once the shape's flag is zero. -/
theorem stgTests_ok (M : Mont) (R : Kernel) {p : PP} {s t : State} {n : Nat} (hs : PH p s) (h : Stg p n t)
    (hz : shapeFlag p.g (mW p.bits) (cOf p) = 0) (i : InScr p.B p.Z s.mem t.mem) (k : Keep mmRegs s t) :
    WP isa (tests M.mm R.run) t fun t' => PEnd s t' p (Spec.Ffdh.sievedParameterCandidate p.bits p.g p.r) := by
  have hL := h.hl
  obtain hshape := (shapeFlag_zero (x := Spec.Rsa.os2ip (p.r.take p.L)) h.st.dims.b1 h.st.dims.b2 h.st.dims.g).mp hz
  rw [sieved_eq hL, hshape]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact WP.mono (tests_ok M R (c := cOf p) h.st rfl (qOdd_of_shape h.st.dims hz) h.used hL) fun t' ht =>
    PEnd.trans_pre ht (outBytes_inScr i hs.ou.outZ) k

/-- `main`: `p`, its shape, and the tests. -/
theorem main_ok (M : Mont) (R : Kernel) {p : PP} {s : State} (h : PH p s)
    (hU : word s.mem p.B (8 * kUsed) = BitVec.ofNat 64 p.L) (hL : p.L ≤ p.r.length) :
    WP isa (main M.mm R.run) s fun t => PEnd s t p (Spec.Ffdh.sievedParameterCandidate p.bits p.g p.r) := by
  obtain nz : ∀ {x : BitVec 64}, (x == 0) = false → x ≠ 0 := fun h => by simpa using h
  obtain ez : ∀ {x : BitVec 64}, (x == 0) = true → x = 0 := fun h => by simpa using h
  unfold main
  simp only [List.append_assoc]
  rw [← List.append_assoc]
  -- `p` and its working space.
  refine wp_seqs_append (by simp [phase]) (by simp [residue]) ?_
  refine WP.mono (stgA_ok h hU hL) fun t₁ ⟨g₁, i₁, k₁⟩ => ?_
  -- The generator's congruence, rejected at once.
  refine wp_seqs_append (by simp [residue]) (by simp) ?_
  refine WP.mono (stgB_ok g₁) fun t₂ ⟨g₂, i₂, k₂⟩ => ?_
  refine WP.seq (WP.mono (stgFlag_ok g₂) fun t₃ ⟨⟨g₃, h5₃⟩, hm₃, k₃⟩ => ?_)
  obtain i₃ : InScr p.B p.Z s.mem t₃.mem := by rw [hm₃]; exact i₁.trans i₂
  obtain kk₃ : Keep mmRegs s t₃ := ((k₁.trans k₂).trans k₃).mono (by decide)
  refine WP.ite (scr1 p.g (cOf p) == 0) (by rw [eval_zero, h5₃]) (fun _ => ?_)
    (fun hb => stgReject_ok g₃.1 (shape_ne (.inl (nz hb))) i₃ kk₃)
  -- The table, and the sieve of `p` by its first words: a small factor is rejected before `q`.
  refine wp_seqs_append (a := [_]) (by simp) (by simp [sieve]) ?_
  rw [seqs_one]
  refine WP.mono (stgTab_ok g₃) fun t₄ ⟨g₄, i₄, k₄⟩ => ?_
  refine wp_seqs_append (by simp [sieve]) (by simp) ?_
  refine WP.mono (stgSieve_ok true g₄) fun t₅ ⟨g₅, i₅, k₅⟩ => ?_
  refine WP.seq (WP.mono (stgFlag_ok g₅.1) fun t₆ ⟨⟨g₆, h5₆⟩, hm₆, k₆⟩ => ?_)
  obtain tab₆ : TabOk t₆.mem p.B (mW p.bits) := by rw [hm₆]; exact g₅.2
  obtain i₆ : InScr p.B p.Z s.mem t₆.mem := by rw [hm₆]; exact (i₃.trans i₄).trans i₅
  obtain kk₆ : Keep mmRegs s t₆ := (((kk₃.trans k₄).trans k₅).trans k₆).mono (by decide)
  refine WP.ite (scr2 p.g (mW p.bits) (cOf p) == 0) (by rw [eval_zero, h5₆]) (fun _ => ?_)
    (fun hb => stgReject_ok g₆.1 (shape_ne (.inr (.inl (nz hb)))) i₆ kk₆)
  -- `q`, rejected at once if it is even.
  unfold mainQ
  refine wp_seqs_append (by simp [halveQ]) (by simp) ?_
  refine WP.mono (stgHalve_ok ⟨g₆, tab₆⟩) fun t₇ ⟨g₇, i₇, k₇⟩ => ?_
  refine WP.seq (WP.mono (stgFlag_ok g₇.1) fun t₈ ⟨⟨g₈, h5₈⟩, hm₈, k₈⟩ => ?_)
  obtain tab₈ : TabOk t₈.mem p.B (mW p.bits) := by rw [hm₈]; exact g₇.2
  obtain i₈ : InScr p.B p.Z s.mem t₈.mem := by rw [hm₈]; exact i₆.trans i₇
  obtain kk₈ : Keep mmRegs s t₈ := ((kk₆.trans k₇).trans k₈).mono (by decide)
  refine WP.ite (scr3 p.g (mW p.bits) (cOf p) == 0) (by rw [eval_zero, h5₈]) (fun _ => ?_)
    (fun hb => stgReject_ok g₈.1 (shape_ne (.inr (.inr (.inl (nz hb))))) i₈ kk₈)
  -- The sieve of `q`: a small factor is rejected before `p`'s whole sieve.
  refine wp_seqs_append (by simp [sieve]) (by simp) ?_
  refine WP.mono (stgSieve_ok false ⟨g₈, tab₈⟩) fun t₉ ⟨g₉, i₉, k₉⟩ => ?_
  refine WP.seq (WP.mono (stgFlag_ok g₉.1) fun t₁₀ ⟨⟨g₁₀, h5₁₀⟩, hm₁₀, k₁₀⟩ => ?_)
  obtain tab₁₀ : TabOk t₁₀.mem p.B (mW p.bits) := by rw [hm₁₀]; exact g₉.2
  obtain i₁₀ : InScr p.B p.Z s.mem t₁₀.mem := by rw [hm₁₀]; exact i₈.trans i₉
  obtain kk₁₀ : Keep mmRegs s t₁₀ := ((kk₈.trans k₉).trans k₁₀).mono (by decide)
  refine WP.ite (scr4 p.g (mW p.bits) (cOf p) == 0) (by rw [eval_zero, h5₁₀]) (fun _ => ?_)
    (fun hb => stgReject_ok g₁₀.1 (shape_ne (.inr (.inr (.inr (.inl (nz hb)))))) i₁₀ kk₁₀)
  -- `p` again, and its whole sieve.
  unfold mainP
  simp only [List.append_assoc]
  refine wp_seqs_append (by simp [shapeP, loadA]) (by simp [sieve]) ?_
  refine WP.mono (stgShape_ok ⟨g₁₀, tab₁₀⟩) fun t₁₁ ⟨g₁₁, i₁₁, k₁₁⟩ => ?_
  refine wp_seqs_append (by simp [sieve]) (by simp) ?_
  refine WP.mono (stgSieve_ok false g₁₁) fun t₁₂ ⟨g₁₂, i₁₂, k₁₂⟩ => ?_
  refine WP.seq (WP.mono (stgFlag_ok g₁₂.1) fun t₁₃ ⟨⟨g₁₃, h5₁₃⟩, hm₁₃, k₁₃⟩ => ?_)
  obtain i₁₃ : InScr p.B p.Z s.mem t₁₃.mem := by rw [hm₁₃]; exact (i₁₀.trans i₁₁).trans i₁₂
  obtain kk₁₃ : Keep mmRegs s t₁₃ := (((kk₁₀.trans k₁₁).trans k₁₂).trans k₁₃).mono (by decide)
  refine WP.ite (scr5 p.g (mW p.bits) (cOf p) == 0) (by rw [eval_zero, h5₁₃])
    (fun hb => stgTests_ok M R h g₁₃.1 (scr5_zero.mp (ez hb)) i₁₃ kk₁₃)
    (fun hb => stgReject_ok g₁₃.1 (shape_ne (.inr (.inr (.inr (.inr (nz hb)))))) i₁₃ kk₁₃)

end VG.Proof.Ffdh.AArch64.ParameterCandidate
