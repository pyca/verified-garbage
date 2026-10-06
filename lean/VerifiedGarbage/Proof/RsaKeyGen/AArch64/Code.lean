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

theorem KArgs.congr {m m' : Mem} {B : Addr} {v0 v1 v2 v3 v4 v5 v6 v7 vr : BitVec 64}
    (h : KArgs m B v0 v1 v2 v3 v4 v5 v6 v7 vr) (hw : ∀ i < 32, word m' B (8 * i) = word m B (8 * i)) :
    KArgs m' B v0 v1 v2 v3 v4 v5 v6 v7 vr :=
  ⟨(hw _ (by decide)).trans h.out, (hw _ (by decide)).trans h.len, (hw _ (by decide)).trans h.usedP,
    (hw _ (by decide)).trans h.e, (hw _ (by decide)).trans h.elen, (hw _ (by decide)).trans h.p,
    (hw _ (by decide)).trans h.plen, (hw _ (by decide)).trans h.rand, (hw _ (by decide)).trans h.rlen⟩

/-- After `kEntry`, from the state `s` on entry. -/
structure EntryPost (s t : State) : Prop where
  x0 : t.gpr .x0 = stackArg s 1
  args : KArgs t.mem (stackArg s 1) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)
    (s.gpr .x6) (s.gpr .x7) (stackArg s 0)
  out : Outside (stackArg s 1) 0 (8 * 32) s.mem t.mem
  keep : Keep [.x0, .x8, .x9] s t

theorem entry_ok {s : State} (c : KCtx s) : WP isa (.block kEntry) s (EntryPost s) := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  exact WP.mono (kEntry_ok rfl (fun i hi => hs.st (by omega)) c.ha c.hsep) fun _ ⟨a, b, d, e⟩ => ⟨a, b, d, e⟩

/-- After the zeros to `out`. -/
structure Zeroed (s t₁ t : State) : Prop where
  zero : ∀ i < (s.gpr .x1).toNat, t.mem (s.gpr .x0 + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ j < (s.gpr .x1).toNat, x ≠ s.gpr .x0 + BitVec.ofNat 64 j) → t.mem x = t₁.mem x
  keep : Keep [.x1, .x2, .x3] t₁ t

theorem zeros_ok {s t₁ : State} (c : KCtx s) (he : EntryPost s t₁) :
    WP isa (zeroOut kOut kLen) t₁ (Zeroed s t₁) := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  have hk2 := c.k2
  exact WP.mono (zeroOut_ok (len := (s.gpr .x1).toNat) (hs.congr he.keep.wr) he.x0 (by omega) (sPtr := kOut)
    (sLen := kLen) (by decide) (by decide) he.args.out (by rw [he.args.len, ofNat_toNat64]) (by omega) (by omega)
    ⟨fun j hj => by rw [he.keep.wr]; exact c.ou.outw j hj, c.ou.outZ⟩) fun _ ⟨a, b, d⟩ => ⟨a, b, d⟩

/-- The header words survive the zeros to `out`. -/
theorem Zeroed.word {s t₁ t : State} (c : KCtx s) (h : Zeroed s t₁ t) {i : Nat} (hi : i < 32) :
    word t.mem (stackArg s 1) (8 * i) = word t₁.mem (stackArg s 1) (8 * i) := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  exact Mem.readW_congr fun b hb => h.frame _ fun j hj he' => by
    have := c.ou.outZ j hj; rw [← he', ofs_off _ (by omega)] at this; omega

/-- After the length check, from the state `s` on entry. -/
structure Front (s t : State) : Prop where
  x0 : t.gpr .x0 = stackArg s 1
  x5 : t.gpr .x5 = BitVec.ofNat 64 (decide ((s.gpr .x1).toNat ≤ (stackArg s 0).toNat)).toNat
  zero : ∀ i < (s.gpr .x1).toNat, t.mem (s.gpr .x0 + BitVec.ofNat 64 i) = 0
  args : KArgs t.mem (stackArg s 1) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)
    (s.gpr .x6) (s.gpr .x7) (stackArg s 0)
  hi : ∀ x, 8 * 32 ≤ ofs (stackArg s 1) x → (∀ j < (s.gpr .x1).toNat, x ≠ s.gpr .x0 + BitVec.ofNat 64 j) →
    t.mem x = s.mem x
  keep : Keep (.x0 :: mmRegs) s t

theorem lenCheck_ok {s t₁ t₂ : State} (c : KCtx s) (he : EntryPost s t₁) (hz : Zeroed s t₁ t₂) :
    WP isa (.block ([ldh .x3 kRandLen, ldh .x4 kLen] ++ geFlag)) t₂ (Front s) := by
  have hs := c.hs
  have hn := hs.nowrap
  have hZ := c.hZ
  have hk1 := c.k1
  have hs₂ := (hs.congr he.keep.wr).congr hz.keep.wr
  have h0₂ : t₂.gpr .x0 = stackArg s 1 := (hz.keep.gpr .x0 (by decide)).trans he.x0
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off (stackArg s 1) (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = stackArg s 0 ∧
      t.gpr .x4 = s.gpr .x1 ∧ t.mem = t₂.mem) (by
    brun [h0₂, hdr_enc (show kRandLen < 32 by decide), hdr_enc (show kLen < 32 by decide), hl₂ kRandLen (by decide),
      hl₂ kLen (by decide), hz.word c (show kRandLen < 32 by decide), hz.word c (show kLen < 32 by decide),
      he.args.rlen, he.args.len])
    (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h3₃, h4₃, hm₃⟩, k₃⟩ =>
    WP.mono (geFlag_ok t₃) fun t₄ ⟨⟨h5₄, hm₄⟩, k₄⟩ => ?_)
  rw [h3₃, h4₃] at h5₄
  have hm4 : t₄.mem = t₂.mem := hm₄.trans hm₃
  exact ⟨((k₃.trans k₄).gpr .x0 (by decide)).trans h0₂, h5₄, fun i hi => by rw [hm4]; exact hz.zero i hi,
    he.args.congr fun i hi => by rw [hm4]; exact hz.word c hi,
    fun x hx hx' => by rw [hm4, hz.frame x hx', he.out x (Or.inr (by omega))],
    (((he.keep.trans hz.keep).trans k₃).trans k₄).mono (by decide)⟩

/-- A buffer apart from `out` keeps its octets through the front. -/
theorem Front.src {s t : State} (c : KCtx s) (h : Front s t) {p : Addr} {bs : List Byte}
    (hp : Src s (stackArg s 1) ((stackArg s 2).toNat * 8) p bs)
    (hd : ∀ i < bs.length, ∀ j < (s.gpr .x1).toNat, p + BitVec.ofNat 64 i ≠ s.gpr .x0 + BitVec.ofNat 64 j) :
    Src t (stackArg s 1) ((stackArg s 2).toNat * 8) p bs := by
  have hZ := c.hZ
  have hk1 := c.k1
  exact Src.congr' hp (fun i hi => h.hi _ (by have := hp.out i hi; omega) (hd i hi)) h.keep.rd h.keep.wr

/-- What `kMain` needs, after the front with enough octets. -/
theorem mainCtx_of {s t : State} {w : Nat} (c : KCtx s) (h : Front s t) (hw : (s.gpr .x1).toNat = 8 * w)
    (hlt : (s.gpr .x1).toNat ≤ (stackArg s 0).toNat) :
    MainCtx t (stackArg s 1) ((stackArg s 2).toNat * 8) w (s.gpr .x0) (s.gpr .x2) (s.gpr .x3)
      (s.gpr .x5) (s.gpr .x7) (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat) := by
  have hZ := c.hZ
  have hk1 := c.k1
  have hk2 := c.k2
  exact
    { scr := c.hs.congr h.keep.wr, x0 := h.x0, z := by omega, w4 := by omega, w64 := by omega,
      out := h.args.out, len := by rw [h.args.len, ← hw, ofNat_toNat64], usedP := h.args.usedP,
      e := h.args.e, elen := by rw [h.args.elen, bytesAt_length, ofNat_toNat64], p := h.args.p,
      plen := by rw [h.args.plen, bytesAt_length, ofNat_toNat64], rand := h.args.rand,
      rlen := by rw [h.args.rlen, bytesAt_length, ofNat_toNat64],
      esrc := h.src c c.esrc (fun i hi => c.doe i (by rwa [bytesAt_length] at hi)),
      psrc := h.src c c.psrc (fun i hi => c.dop i (by rwa [bytesAt_length] at hi)),
      rsrc := h.src c c.rsrc (fun i hi => c.dor i (by rwa [bytesAt_length] at hi)),
      el1 := by rw [bytesAt_length]; exact c.el1, el8 := by rw [bytesAt_length]; exact c.el8,
      pl := by rw [bytesAt_length, ← hw]; exact c.pl, rl := by rw [bytesAt_length]; exact (stackArg s 0).isLt,
      rk := by rw [bytesAt_length, ← hw]; exact hlt, ou := by rw [← hw]; exact c.ou.congr h.keep.wr }

/-- The candidate's result after the front, with enough octets. -/
theorem candRes_main {s : State} {w : Nat} (hw : (s.gpr .x1).toNat = 8 * w) (hw4 : 4 ≤ w)
    (hlt : (s.gpr .x1).toNat ≤ (stackArg s 0).toNat) :
    candRes s = VG.Proof.RsaKeyGen.afterDraw (64 * w)
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat))
      (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (s.gpr .x5) (s.gpr .x6).toNat))
      (Spec.RsaKeyGen.candidate (64 * w)
        (Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat).take (8 * w))))
      ((Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat).drop (8 * w)) := by
  unfold candRes Spec.RsaKeyGen.candidateOp
  rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega),
    VG.Proof.RsaKeyGen.ite_t (by rw [bytesAt_length]; omega), show 8 * (8 * w) = 64 * w by omega]
  simp only [VG.Proof.RsaKeyGen.seg, List.drop_zero]

/-- With too few octets: status 0. -/
theorem front_none {s t : State} (c : KCtx s) (h : Front s t) (hlt : (stackArg s 0).toNat < (s.gpr .x1).toNat) :
    WP isa finNone t fun t' => abiPreserved s t' ∧ candPost s t' := by
  have hZ := c.hZ
  have hk1 := c.k1
  have ho := c.ou.congr h.keep.wr
  refine WP.mono (finNone_ok (up := s.gpr .x2) (c.hs.congr h.keep.wr) h.x0 (by omega) h.args.usedP ho.upw)
    fun t' ht => candEnd_post h.zero h.keep ?_
  have hnone : candRes s = none := by
    unfold candRes Spec.RsaKeyGen.candidateOp
    have hk8 := c.k8
    obtain ⟨w, hw⟩ : ∃ w, (s.gpr .x1).toNat = 8 * w := ⟨(s.gpr .x1).toNat / 8, by omega⟩
    rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega),
      VG.Proof.RsaKeyGen.ite_f (by rw [bytesAt_length]; omega)]
  rw [hnone]; exact KEnd.of_fin ho ht

/-- `vg_rsa_keygen_candidate` ends as the specification says. -/
theorem code_correct (M : Mont) (s : State) (h : candContract.pre s) :
    ∃ t s', Exec isa (code M.mm) s t s' ∧ abiPreserved s s' ∧ candContract.post s s' := by
  have c := kctx_of h
  suffices hwp : WP isa (code M.mm) s fun s' => abiPreserved s s' ∧ candPost s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  have hk1 := c.k1
  have hk8 := c.k8
  obtain ⟨w, hw⟩ : ∃ w, (s.gpr .x1).toNat = 8 * w := ⟨(s.gpr .x1).toNat / 8, by omega⟩
  unfold code
  simp only [seqs]
  refine WP.seq (WP.mono (entry_ok c) fun t₁ he => ?_)
  refine WP.seq (WP.mono (zeros_ok c he) fun t₂ hz => ?_)
  refine WP.seq (WP.mono (lenCheck_ok c he hz) fun t₄ hf => ?_)
  refine WP.ite (!decide ((s.gpr .x1).toNat ≤ (stackArg s 0).toNat))
    (by rw [eval_zero, hf.x5]; cases decide ((s.gpr .x1).toNat ≤ (stackArg s 0).toNat) <;> rfl)
    (fun hlt => ?_) (fun hlt => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at hlt
    exact front_none c hf hlt
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hlt
    refine WP.mono (kMain_ok M (mainCtx_of c hf hw hlt)) fun t ht => candEnd_post hf.zero hf.keep ?_
    rw [candRes_main hw (by omega) hlt, hw]
    exact ht

end VG.Proof.RsaKeyGen.AArch64
