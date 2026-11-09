module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Test
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# An FFDH parameter candidate on PPC64LE: the tests of q and p

`testQ_ok`: the test of q, halved in place from p's width; `testP_ok`: the
test of p, loaded again from the tape.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

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

/-- `Ph` survives a change of memory that keeps the header. -/
theorem Ph.keepHdr {C : Nat} {p : PP} {mb : Nat} {s t : State} (h : Ph p mb C s)
    (r10 : t.gpr .r10 = s.gpr .r10) (r11 : t.gpr .r11 = s.gpr .r11) (r29 : t.gpr .r29 = s.gpr .r29)
    (hw : ∀ d, d + 8 ≤ 256 → word t.mem p.B d = word s.mem p.B d) : Ph p mb C t :=
  ⟨r10.trans h.r10, r11.trans h.r11, r29.trans h.r29, (hw 248 (by decide)).trans h.mbW,
    (hw 216 (by decide)).trans h.kW, (hw 48 (by decide)).trans h.wW, (hw 224 (by decide)).trans h.strideW,
    fun j hj => (hw _ (by omega_arith)).trans (h.arrW j hj), (hw 168 (by decide)).trans h.checksW, h.k1, h.k2,
    (hw 192 (by decide)).trans h.topW⟩

theorem slot_zero (w : Nat) : slot w 0 = 256 := by simp [slot, hdrBytes]

theorem phR_low : ∀ r ∈ phRanges ++ [(8 * hTop, 8)], r.1 + r.2 ≤ 256 := by
  intro r hr
  simp only [phRanges, hTop, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

theorem phR_used : ∀ r ∈ phRanges ++ [(8 * hTop, 8)], 152 + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 152 := by
  intro r hr
  simp only [phRanges, hTop, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The set-up of q's test: its working space. -/
theorem qPrep_ok {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (.seq (phase true) (.block [])) s (TCPre p (p.bits - 1) ((c - 1) / 2) u (Spec.Ffdh.primeChecks (p.bits - 1))) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hdn := h.dims.n
  have hn' := h.dims.n'
  obtain ⟨hpo, hl, hu'⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  rw [← hc] at hpo hl hu'
  obtain ⟨hql, hqu⟩ := VG.Proof.Ffdh.ParameterCandidate.half_shape (by omega_arith) hpo hl hu'
  have hbl := VG.Proof.Ffdh.ParameterCandidate.half_pred_bitLength (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L)) (by rw [← hc]; exact hqo)
  rw [← hc] at hbl
  refine WP.seq (WP.mono (phase_ok h true) fun t ⟨⟨st, ph, hf⟩, _⟩ => ?_)
  simp only [mbOf, ↓reduceIte] at ph
  rw [WP.block_nil_iff]
  have hL : p.L = (p.bits + 7) / 8 := rfl
  have hwq : wOf (p.bits - 1) ≤ wOf p.bits := by simp only [wOf]; omega_arith
  refine ⟨st, ph, by omega_arith, by omega_arith, ?_, hbl, hqo, ?_, ?_, hul⟩
  · rw [slot_zero] at hq ⊢
    refine wv_low (w := wOf p.bits) ?_ hwq (Nat.lt_of_lt_of_le hqu (Nat.pow_le_pow_right (by decide) (by
      simp only [wOf]; omega_arith)))
    rw [hf.wv_eq (fun r hr => .inr (phR_low r hr)) (by simp only [wOf]; omega_arith)]
    exact hq
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 2 ≤ p.bits - 2 by omega_arith)
    omega_arith
  · rw [hf.word_eq phR_used (by decide)]; exact hu

/-- The test of q, halved in array 0 in p's width. -/
theorem testQ_ok (R : RoundImpl) {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hq : wv s.mem p.B (slot (wOf p.bits) 0) (wOf p.bits) = (c - 1) / 2) (hqo : ((c - 1) / 2) % 2 = 1)
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) :
    WP isa (test true (.block []) R.name R.code) s
      (MrEnd p (p.bits - 1) ((c - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1))
        (checkWitnesses ((c - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1)) (p.r.drop u))) := by
  unfold test
  simp only [↓reduceIte]
  exact WP.assoc (WP.seq (WP.mono (qPrep_ok h hc hq hqo hu hul) fun _ ht =>
    WP.seq (WP.block_nil_iff.mpr (ht.core R))))

/-- The set-up of p's test: its working space, and p from the tape. -/
theorem pPrep_ok {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (.seq (phase false) shapeP) s (TCPre p p.bits c u (Spec.Ffdh.primeChecks p.bits)) := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  have hdn := h.dims.n
  obtain ⟨hpo, hl, _⟩ := VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))
  have hbl := (VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength (bits := p.bits) (by omega_arith)
    (Spec.Rsa.os2ip (p.r.take p.L))).2
  rw [← hc] at hpo hl hbl
  refine WP.seq (WP.mono (phase_ok h false) fun t ⟨⟨st, ph, hf⟩, _⟩ => ?_)
  simp only [mbOf, Bool.false_eq_true, ↓reduceIte] at ph
  refine WP.mono (shapeP_ok st ph hL) fun t₂ ⟨⟨hn₂, f₂⟩, k₂⟩ => ?_
  have hLe : p.L = (p.bits + 7) / 8 := rfl
  have hw : wOf p.bits = (p.bits + 63) / 64 := rfl
  have hsl : slot (wOf p.bits) 0 = 256 := slot_zero _
  have hlow : ∀ d, d + 8 ≤ 256 → word t₂.mem p.B d = word t.mem p.B d := fun d hd =>
    f₂.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (by rw [hsl]; exact hd)) (by omega_arith)
  have st₂ : St p t₂ := st.step (Frm.toMut f₂ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact InMut.arrays (by rw [hsl]) (by rw [hsl]; simp only [saveBytes]; omega_arith)) k₂ (by decide)
  have ph₂ : Ph p p.bits (Spec.Ffdh.primeChecks p.bits) t₂ := ph.keepHdr (k₂.gpr _ (by decide)) (k₂.gpr _ (by decide)) (k₂.gpr _ (by decide)) hlow
  refine ⟨st₂, ph₂, by omega_arith, Nat.le_refl _, by rw [hn₂, hc], hbl, hpo, ?_, ?_, hul⟩
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 2 ≤ p.bits - 1 by omega_arith)
    omega_arith
  · rw [hlow 152 (by decide), hf.word_eq phR_used (by decide)]; exact hu

/-- `hChecks := C'`: the test's other data stay. -/
theorem TCPre.setChecks {C C' : Nat} {p : PP} {mb N u : Nat} {s t : State} (h : TCPre p mb N u C s)
    (hm : t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 168) (BitVec.ofNat 64 C')) {regs : List Reg}
    (k : Keep regs s t) (h31 : Reg.r31 ∉ regs) (h2 : Reg.r2 ∉ regs) (h10 : Reg.r10 ∉ regs)
    (h11 : Reg.r11 ∉ regs) (h29 : Reg.r29 ∉ regs) (c1 : 1 ≤ C') (c2 : C' ≤ 128) : TCPre p mb N u C' t := by
  have hdn := h.st.dims.n
  have hf : Frm p.B [(168, 8)] s.mem t.mem := by
    rw [hm]; exact frm_writeW (a := 168) (Frm.refl _ _ _) _ ⟨_, List.mem_singleton_self _, by decide, by decide⟩
      (by decide)
  have st := h.st.step (Frm.toMut hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact InMut.hdr (i := 21) (by decide)) k h31 h2
  have ew : ∀ d, d + 8 ≤ 168 ∨ 176 ≤ d → d + 8 ≤ 2 ^ 64 → word t.mem p.B d = word s.mem p.B d := fun d hd hd' =>
    hf.word_eq (fun r hr => by rw [List.mem_singleton.mp hr]; dsimp only; omega_arith) hd'
  have hp := h.ph
  have ph : Ph p mb C' t := ⟨(k.gpr _ h10).trans hp.r10, (k.gpr _ h11).trans hp.r11, (k.gpr _ h29).trans hp.r29,
    (ew _ (by simp only [hMb]; omega_arith) (by simp only [hMb]; omega_arith)).trans hp.mbW,
    (ew _ (by simp only [Impl.MillerRabin.PPC64LE.Search.hK]; omega_arith)
      (by simp only [Impl.MillerRabin.PPC64LE.Search.hK]; omega_arith)).trans hp.kW,
    (ew _ (by simp only [hW]; omega_arith) (by simp only [hW]; omega_arith)).trans hp.wW,
    (ew _ (by simp only [hStride]; omega_arith) (by simp only [hStride]; omega_arith)).trans hp.strideW,
    fun j hj => (ew _ (by omega_arith) (by omega_arith)).trans (hp.arrW j hj),
    by show t.mem.readW (p.B + BitVec.ofNat 64 168) 64 = _; rw [hm, rw_self], c1, c2,
    (ew _ (by simp only [hTop]; omega_arith) (by simp only [hTop]; omega_arith)).trans hp.topW⟩
  refine ⟨st, ph, h.mb1, h.mb2, ?_, h.bl, h.odd, h.n3, (ew 152 (by decide) (by decide)).trans h.used, h.ul⟩
  have hb2 := h.st.dims.b2
  have hm2 := h.mb2
  rw [hf.wv_eq (fun r hr => by rw [List.mem_singleton.mp hr, slot_zero]; exact .inr (by decide))
    (by rw [slot_zero]; simp only [wOf]; omega_arith)]
  exact h.n

/-- `firstCheck`: one witness. -/
theorem firstCheck_ok {C : Nat} {p : PP} {mb N u : Nat} {s : State} (h : TCPre p mb N u C s) :
    WP isa firstCheck s (TCPre p mb N u 1) := by
  have l168 : InRegions s.wr (p.B + BitVec.ofNat 64 168) 8 := h.st.st (d := 168) (by decide)
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 168) (BitVec.ofNat 64 1))
    (by simp only [firstCheck, sth, hChecks]; prun [h.st.r31, l168]) (by decide)) fun t ⟨tm, kt⟩ => ?_
  exact h.setChecks tm kt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `restChecks`: the witnesses but one. -/
theorem restChecks_ok {C : Nat} {p : PP} {mb N u : Nat} {s : State} (h : TCPre p mb N u C s) (hC : 2 ≤ C) :
    WP isa restChecks s (TCPre p mb N u (C - 1)) := by
  have l168 : InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 168) 8 := h.st.ld (d := 168) (by decide)
  have s168 : InRegions s.wr (p.B + BitVec.ofNat 64 168) 8 := h.st.st (d := 168) (by decide)
  have hc : s.mem.readW (p.B + BitVec.ofNat 64 168) 64 = BitVec.ofNat 64 C := h.ph.checksW
  have c2 := h.ph.k2
  have hC' : BitVec.ofNat 64 C - BitVec.ofNat 64 1 = BitVec.ofNat 64 (C - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.mem = s.mem.writeW (p.B + BitVec.ofNat 64 168)
      (BitVec.ofNat 64 (C - 1)))
    (by simp only [restChecks, ldh, sth, hChecks]; prun [h.st.r31, l168, s168, hc, hC']) (by decide))
    fun t ⟨tm, kt⟩ => ?_
  exact h.setChecks tm kt (by decide) (by decide) (by decide) (by decide) (by decide) (by omega_arith) (by omega_arith)

/-- A test of p, loaded again from the tape, its witness count changed by
`adjust` to `K`. -/
theorem testP_of {K : Nat} (R : RoundImpl) {adjust : Prog isa} {p : PP} {s : State} {c u : Nat}
    (hadj : ∀ {t : State}, TCPre p p.bits c u (Spec.Ffdh.primeChecks p.bits) t →
      WP isa adjust t (TCPre p p.bits c u K))
    (h : St p s) (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (test false adjust R.name R.code) s (MrEnd p p.bits c K (checkWitnesses c K (p.r.drop u))) := by
  unfold test
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact WP.assoc (WP.seq (WP.mono (pPrep_ok h hc hu hul hL) fun _ ht =>
    WP.seq (WP.mono (hadj ht) fun _ ht' => ht'.core R)))

/-- The test of p's first witness. -/
theorem testP1_ok (R : RoundImpl) {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (test false firstCheck R.name R.code) s (MrEnd p p.bits c 1 (checkWitnesses c 1 (p.r.drop u))) :=
  testP_of R (fun ht => firstCheck_ok ht) h hc hu hul hL

/-- The test of p's other witnesses. -/
theorem testPR_ok (R : RoundImpl) {p : PP} {s : State} {c u : Nat} (h : St p s)
    (hc : c = Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip (p.r.take p.L)))
    (hu : word s.mem p.B 152 = BitVec.ofNat 64 u) (hul : u ≤ p.r.length) (hL : p.L ≤ p.r.length) :
    WP isa (test false restChecks R.name R.code) s
      (MrEnd p p.bits c (Spec.Ffdh.primeChecks p.bits - 1)
        (checkWitnesses c (Spec.Ffdh.primeChecks p.bits - 1) (p.r.drop u))) :=
  testP_of R (fun ht => restChecks_ok ht (by unfold Spec.Ffdh.primeChecks; split <;> decide)) h hc hu hul hL

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
