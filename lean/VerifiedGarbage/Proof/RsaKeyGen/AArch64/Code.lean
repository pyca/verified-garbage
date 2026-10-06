import VerifiedGarbage.Proof.RsaKeyGen.AArch64.KMain

/-!
# A candidate on AArch64: correctness

`code`, from a state `candContract` allows, ends as `candidateOp`
(`code_correct`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- The postcondition, from how the candidate ended after the entry and the
zeros to `out` (at `t₃`). -/
theorem candEnd_post {s t₃ t : State}
    (hz : ∀ i < (s.gpr .x1).toNat, t₃.mem (s.gpr .x0 + BitVec.ofNat 64 i) = 0)
    (kk : Keep (.x0 :: mmRegs) s t₃)
    (h : CandEnd t₃ t (s.gpr .x0) (s.gpr .x2) (s.gpr .x1).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat) (candRes s)) :
    abiPreserved s t ∧ candPost s t := by
  have key : ∀ {st u : Nat} {outv : Option Nat}, st < 4 →
      KEnd t₃ t (s.gpr .x0) (s.gpr .x2) (s.gpr .x1).toNat st u outv →
      abiPreserved s t ∧ ((t.gpr .x0).setWidth 32).toNat = st ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat = (match outv with
        | some c => Spec.Rsa.i2osp c (s.gpr .x1).toNat
        | none => List.replicate (s.gpr .x1).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .x2) 1 = [BitVec.ofNat 64 u] := by
    intro st u outv hst hk
    refine ⟨abiPreserved_of_keep ((kk.trans hk.keep).mono (by decide)), ?_, ?_, ?_⟩
    · rw [hk.x0, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    · show outBytes t.mem _ _ = _
      have := hk.out
      cases outv
      · rw [this]
        show List.map _ _ = _
        rw [List.map_congr_left fun i hi => hz i (List.mem_range.mp hi)]; simp [List.map_const']
      · exact this
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
        hk.used]
  unfold candPost
  rcases hres : candRes s with _ | ⟨_ | _ | _, rest⟩ <;> rw [hres] at h <;> simp only [CandEnd] at h
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, hw⟩
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, by rw [hw, bytesAt_length]⟩
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, by rw [hw, bytesAt_length]⟩
  · obtain ⟨hg, hst, hb, hw⟩ := key (by decide) h
    exact ⟨hg, by rw [hst]; rfl, hb, by rw [hw, bytesAt_length]⟩

/-- A buffer whose octets did not change. -/
theorem Src.congr' {s t : State} {B : Addr} {Z : Nat} {p : Addr} {bs : List Byte} (h : Src s B Z p bs)
    (hm : ∀ i < bs.length, t.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i)) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : Src t B Z p bs :=
  ⟨fun i hi => by rw [hrd, hwr]; exact h.rd i hi, fun i hi => by rw [hm i hi]; exact h.val i hi, h.out⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `vg_rsa_keygen_candidate` ends as the specification says. -/
theorem code_correct (M : Mont) (s : State) (h : candContract.pre s) :
    ∃ t s', Exec isa (code M.mm) s t s' ∧ abiPreserved s s' ∧ candContract.post s s' := by
  have c := kctx_of h
  suffices hwp : WP isa (code M.mm) s fun s' => abiPreserved s s' ∧ candPost s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  have hk2 := c.k2
  have hk8 := c.k8
  have h256 : 8 * 32 ≤ (stackArg s 2).toNat * 8 := by omega
  obtain ⟨w, hw⟩ : ∃ w, (s.gpr .x1).toNat = 8 * w := ⟨(s.gpr .x1).toNat / 8, by omega⟩
  have hhw : ∀ i < 32, InRegions s.wr (off (stackArg s 1) (8 * i)) 8 := fun i hi => hs.st (by omega)
  unfold code
  simp only [seqs]
  refine WP.seq (WP.mono (kEntry_ok rfl hhw c.ha c.hsep) fun t₁ ⟨h0₁, ka₁, o₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (zeroOut_ok (len := (s.gpr .x1).toNat) hs₁ h0₁ h256 (sPtr := kOut) (sLen := kLen)
    (by decide) (by decide) ka₁.out (by rw [ka₁.len, ofNat_toNat64]) (by omega) (by omega)
    ⟨fun j hj => by rw [k₁.wr]; exact c.ou.outw j hj, c.ou.outZ⟩) fun t₂ ⟨hz₂, hf₂, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.wr
  have h0₂ : t₂.gpr .x0 = stackArg s 1 := (k₂.gpr .x0 (by decide)).trans h0₁
  have hw₂ : ∀ i < 32, word t₂.mem (stackArg s 1) (8 * i) = word t₁.mem (stackArg s 1) (8 * i) := fun i hi =>
    Mem.readW_congr fun b hb => hf₂ _ fun j hj he' => by
      have := c.ou.outZ j hj; rw [← he', ofs_off _ (by omega)] at this; omega
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off (stackArg s 1) (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = stackArg s 0 ∧ t.gpr .x4 = s.gpr .x1 ∧
      t.mem = t₂.mem) (by
    brun [h0₂, hdr_enc (show kRandLen < 32 by decide), hdr_enc (show kLen < 32 by decide), hl₂ kRandLen (by decide),
      hl₂ kLen (by decide), hw₂ kRandLen (by decide), hw₂ kLen (by decide), ka₁.rlen, ka₁.len])
    (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h3₃, h4₃, hm₃⟩, k₃⟩ =>
    WP.mono (geFlag_ok t₃) fun t₄ ⟨⟨h5₄, hm₄⟩, k₄⟩ => ?_))
  rw [h3₃, h4₃] at h5₄
  have kk : Keep (.x0 :: mmRegs) s t₄ := (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)
  have hm4 : t₄.mem = t₂.mem := hm₄.trans hm₃
  have hs₄ := hs.congr kk.wr
  have h0₄ : t₄.gpr .x0 = stackArg s 1 := ((k₃.trans k₄).gpr .x0 (by decide)).trans h0₂
  have hz₄ : ∀ i < (s.gpr .x1).toNat, t₄.mem (s.gpr .x0 + BitVec.ofNat 64 i) = 0 := fun i hi => by
    rw [hm4]; exact hz₂ i hi
  have hw₄ : ∀ i < 32, word t₄.mem (stackArg s 1) (8 * i) = word t₁.mem (stackArg s 1) (8 * i) := fun i hi => by
    rw [hm4]; exact hw₂ i hi
  have ho₄ := c.ou.congr kk.wr
  refine WP.ite (!decide ((s.gpr .x1).toNat ≤ (stackArg s 0).toNat))
    (by rw [eval_zero, h5₄]; cases decide ((s.gpr .x1).toNat ≤ (stackArg s 0).toNat) <;> rfl) (fun hlt => ?_) (fun hlt => ?_)
  · -- Too few octets.
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at hlt
    refine WP.mono (finNone_ok (up := s.gpr .x2) hs₄ h0₄ h256 (by rw [hw₄ _ (by decide)]; exact ka₁.usedP) ho₄.upw)
      fun t ht => candEnd_post hz₄ kk ?_
    have hnone : candRes s = none := by
      unfold candRes Spec.RsaKeyGen.candidateOp
      rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega), VG.Proof.RsaKeyGen.ite_f (by rw [bytesAt_length]; omega)]
    rw [hnone, hw]; exact KEnd.of_fin (by rw [← hw]; exact ho₄) ht
  · -- `kMain`.
    simp only [Bool.not_eq_false', decide_eq_true_eq] at hlt
    have hhi : ∀ x, 8 * 32 ≤ ofs (stackArg s 1) x → (∀ j < (s.gpr .x1).toNat, x ≠ s.gpr .x0 + BitVec.ofNat 64 j) →
        t₄.mem x = s.mem x := fun x hx hx' => by
      rw [hm4, hf₂ x hx', o₁ x (Or.inr (by omega))]
    have hsrc : ∀ {p : Addr} {bs : List Byte}, Src s (stackArg s 1) ((stackArg s 2).toNat * 8) p bs →
        (∀ i < bs.length, ∀ j < (s.gpr .x1).toNat, p + BitVec.ofNat 64 i ≠ s.gpr .x0 + BitVec.ofNat 64 j) →
        Src t₄ (stackArg s 1) ((stackArg s 2).toNat * 8) p bs := fun {p bs} h hd =>
      Src.congr' h (fun i hi => hhi _ (by have := h.out i hi; omega) (hd i hi)) kk.rd kk.wr
    have hctx : MainCtx t₄ (stackArg s 1) ((stackArg s 2).toNat * 8) w (s.gpr .x0) (s.gpr .x2) (s.gpr .x3)
        (s.gpr .x5) (s.gpr .x7) (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat) :=
      { scr := hs₄, x0 := h0₄, z := by omega, w4 := by omega, w64 := by omega,
        out := by rw [hw₄ _ (by decide)]; exact ka₁.out,
        len := by rw [hw₄ _ (by decide), ka₁.len, ← hw, ofNat_toNat64],
        usedP := by rw [hw₄ _ (by decide)]; exact ka₁.usedP,
        e := by rw [hw₄ _ (by decide)]; exact ka₁.e,
        elen := by rw [hw₄ _ (by decide), ka₁.elen, bytesAt_length, ofNat_toNat64],
        p := by rw [hw₄ _ (by decide)]; exact ka₁.p,
        plen := by rw [hw₄ _ (by decide), ka₁.plen, bytesAt_length, ofNat_toNat64],
        rand := by rw [hw₄ _ (by decide)]; exact ka₁.rand,
        rlen := by rw [hw₄ _ (by decide), ka₁.rlen, bytesAt_length, ofNat_toNat64],
        esrc := hsrc c.esrc (fun i hi => c.doe i (by rwa [bytesAt_length] at hi)),
        psrc := hsrc c.psrc (fun i hi => c.dop i (by rwa [bytesAt_length] at hi)),
        rsrc := hsrc c.rsrc (fun i hi => c.dor i (by rwa [bytesAt_length] at hi)),
        el1 := by rw [bytesAt_length]; exact c.el1, el8 := by rw [bytesAt_length]; exact c.el8,
        pl := by rw [bytesAt_length, ← hw]; exact c.pl, rl := by rw [bytesAt_length]; exact (stackArg s 0).isLt,
        rk := by rw [bytesAt_length, ← hw]; exact hlt, ou := by rw [← hw]; exact ho₄ }
    refine WP.mono (kMain_ok M hctx) fun t ht => candEnd_post hz₄ kk ?_
    have hres : candRes s = VG.Proof.RsaKeyGen.afterDraw (64 * w)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat))
        (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat))
        (Spec.RsaKeyGen.candidate (64 * w)
          (Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat).take (8 * w))))
        ((Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat).drop (8 * w)) := by
      unfold candRes Spec.RsaKeyGen.candidateOp
      rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega),
        VG.Proof.RsaKeyGen.ite_t (by rw [bytesAt_length]; omega), show 8 * (8 * w) = 64 * w by omega]
      simp only [VG.Proof.RsaKeyGen.seg, List.drop_zero]
    rw [hres, hw]
    exact ht

end VG.Proof.RsaKeyGen.AArch64
