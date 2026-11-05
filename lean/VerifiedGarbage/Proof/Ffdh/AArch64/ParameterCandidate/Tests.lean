module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Test
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Rsa.AArch64.Div
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain

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
