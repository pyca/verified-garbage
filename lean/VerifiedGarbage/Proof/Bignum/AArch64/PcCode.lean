import VerifiedGarbage.Proof.Bignum.AArch64.PcMain

/-!
# `vg_rsa_public_precompute` on AArch64: correctness

The entry (`pcEntry_ok`) and the whole function (`pcCode_correct`), against
`pcContract`, which states the shared contract's precondition on the
registers.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-! ## The contract on the registers -/

/-- `vg_rsa_public_precompute(pre = x0, pre_len = x1, n = x2, n_len = x3,
scratch = x4, scratch_len = x5)`. -/
def pcContract : Contract isa where
  pre s :=
    let pre : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩
    let n : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scr : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat * 8⟩
    s.rd = [n] ∧ s.wr = [pre, scr] ∧ pre.Disjoint n ∧ pre.Disjoint scr ∧ n.Disjoint scr ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat * 8 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat * 8 ≤ 2 ^ 64 ∧ Spec.Rsa.lenValid (s.gpr .x3).toNat ∧
      (s.gpr .x1).toNat = Spec.Rsa.precomputedWords (s.gpr .x3).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .x3).toNat ≤ (s.gpr .x5).toNat
  post s s' :=
    match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) with
    | some ws => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Rsa.wordsAt s'.mem (s.gpr .x0) (s.gpr .x1).toNat = ws
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
      Spec.Rsa.wordsAt s'.mem (s.gpr .x0) (s.gpr .x1).toNat = List.replicate (s.gpr .x1).toNat 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat).map (·.toNat) ∧
      s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5

/-- What keeps `x0` to `x17` keeps what the calling convention preserves. -/
theorem abiPreserved_of_keep {s t : State} (k : Keep (.x0 :: mmRegs) s t) : abiPreserved s t :=
  ⟨fun r hr => k.gpr r (by revert r; decide), k.sp, k.vcs⟩

/-! ## The entry -/

/-- The entry: the arguments in the header at `scratch` (`x4`), and its base
in `x0`. -/
theorem pcEntry_ok {s : State} {B : Addr} (hB : s.gpr .x4 = B)
    (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8) :
    WP isa (.block Precompute.entry) s fun t => t.gpr .x0 = B ∧
      word t.mem B (8 * sOut) = s.gpr .x0 ∧ word t.mem B (8 * sN) = s.gpr .x2 ∧
      word t.mem B (8 * sK) = s.gpr .x3 ∧ Outside B 0 (8 * 22) s.mem t.mem ∧ Keep [.x0] s t := by
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧
      t.mem = ((s.mem.writeW (off B (8 * sOut)) (s.gpr .x0)).writeW (off B (8 * sN)) (s.gpr .x2)).writeW
        (off B (8 * sK)) (s.gpr .x3)) (by
    unfold Precompute.entry
    brun [hB, hdr_enc (show sOut < 32 by decide), hdr_enc (show sN < 32 by decide),
      hdr_enc (show sK < 32 by decide), hw sOut (by decide), hw sN (by decide), hw sK (by decide)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k⟩ => ?_
  have hK : sK = 18 := rfl
  have hN : sN = 17 := rfl
  have hO : sOut = 16 := rfl
  refine ⟨h0, ?_, ?_, ?_, ?_, k⟩ <;> rw [hm]
  · rw [(writeW_outside _ B _ (by omega)).word (by omega) (by omega),
      (writeW_outside _ B _ (by omega)).word (by omega) (by omega), word_writeW_self]
  · rw [(writeW_outside _ B _ (by omega)).word (by omega) (by omega), word_writeW_self]
  · rw [word_writeW_self]
  · intro x hx
    rw [writeW_outside _ B _ (by omega) x (by omega), writeW_outside _ B _ (by omega) x (by omega),
      writeW_outside _ B _ (by omega) x (by omega)]

/-! ## The whole function -/

/-- What `code` uses of its contract's precondition, for the working space
`B = scratch` (`x4`) of `Z` bytes, `m`'s length `k` and `pre`'s `2 w`
words. -/
structure PcCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .x3).toNat
  hk2 : (s.gpr .x3).toNat ≤ 1024
  hpl : (s.gpr .x1).toNat = 2 * (((s.gpr .x3).toNat + 7) / 8)
  hZ : 128 * (s.gpr .x3).toNat ≤ (s.gpr .x5).toNat * 8
  hs : Scr s (s.gpr .x4) ((s.gpr .x5).toNat * 8)
  hnb : Src s (s.gpr .x4) ((s.gpr .x5).toNat * 8) (s.gpr .x2)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  hpw : ∀ i < 2 * (((s.gpr .x3).toNat + 7) / 8), InRegions s.wr (off (s.gpr .x0) (8 * i)) 8
  hps : ∀ j < 16 * (((s.gpr .x3).toNat + 7) / 8),
    (s.gpr .x5).toNat * 8 ≤ ofs (s.gpr .x4) (s.gpr .x0 + BitVec.ofNat 64 j)

theorem pcCtx_of {s : State} (h : pcContract.pre s) : PcCtx s := by
  simp only [pcContract] at h
  obtain ⟨hrd, hwr, dPn, dPs, dns, wP, wN, wS, hk, hpl, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords at hpl
  have hs : Scr s (s.gpr .x4) ((s.gpr .x5).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hpre : (⟨s.gpr .x0, (s.gpr .x1).toNat * 8⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  exact ⟨hk1, hk2, hpl, by omega, hs, src_of_region (by rw [hrd]; simp) (by omega) dns,
    fun i hi => ⟨_, hpre, Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj => out_scr dPs (contains_byte _ (by omega) (by omega))⟩

theorem pcCode_correct (M : Mont) (s : State) (h : pcContract.pre s) :
    ∃ t s', Exec isa (Precompute.code M.mm) s t s' ∧ abiPreserved s s' ∧ pcContract.post s s' := by
  have c := pcCtx_of h
  have hZ := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  suffices hwp : WP isa (Precompute.code M.mm) s fun s' => abiPreserved s s' ∧ pcContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold Precompute.code
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pcEntry_ok rfl (fun i hi => c.hs.st (by omega)))
    fun t₁ ⟨h0, hO, hN, hK, ho₁, k₁⟩ => ?_
  have i₁ : InScr (s.gpr .x4) ((s.gpr .x5).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega)
  have hnb₁ := c.hnb.congrK i₁ k₁
  refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok (k₁.gpr .x2 (by decide))
    (by rw [k₁.gpr .x3 (by decide), ofNat_toNat64]) hk1 hk2
    (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi))
    (fun i hi => hnb₁.val i _)) (by decide) (by decide) (by decide +kernel))
    fun t₂ ⟨⟨hz₂, hm₂, _⟩, k₂⟩ => ?_
  have kk := k₁.trans k₂
  have i₂ : InScr (s.gpr .x4) ((s.gpr .x5).toNat * 8) s.mem t₂.mem := by rw [hm₂]; exact i₁
  have hs₂ := c.hs.congr kk.wr
  have h0₂ : t₂.gpr .x0 = s.gpr .x4 := (k₂.gpr .x0 (by decide)).trans h0
  have hw : ∀ i < 2 * (((s.gpr .x3).toNat + 7) / 8), InRegions t₂.wr (off (s.gpr .x0) (8 * i)) 8 :=
    fun i hi => by rw [kk.wr]; exact c.hpw i hi
  have hz : slot (((s.gpr .x3).toNat + 7) / 8) 8 ≤ (s.gpr .x5).toNat * 8 := by unfold slot hdrBytes; omega
  -- What either branch leaves.
  have fin : ∀ t (ws : List (BitVec 64)) (cb : Bool),
      PcPost t₂ t (s.gpr .x4) ((s.gpr .x5).toNat * 8) (((s.gpr .x3).toNat + 7) / 8) (s.gpr .x0) ws cb →
      (Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) =
        if cb then some ws else none) →
      (cb = false → ws = List.replicate (2 * (((s.gpr .x3).toNat + 7) / 8)) 0) →
      abiPreserved s t ∧ pcContract.post s t := by
    intro t ws cb hp hpc hws
    refine ⟨abiPreserved_of_keep ((kk.trans hp.keep).mono (by decide)), ?_⟩
    simp only [pcContract]
    rw [hpc, c.hpl]
    cases cb
    · simp only [Bool.false_eq_true, ite_false]
      exact ⟨by rw [hp.x0]; rfl, by rw [hp.words, hws rfl]⟩
    · simp only [ite_true]
      exact ⟨by rw [hp.x0]; rfl, hp.words⟩
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
    (s.gpr .x3).toNat) (by rw [eval_zero, hz₂]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = false := by simpa using hb
    refine WP.mono (pcFail_ok hs₂ h0₂ (by omega) (by omega) (by omega) (by rw [hm₂]; exact hO)
      (by rw [hm₂, hK, ofNat_toNat64]) hw)
      fun t hp => fin t _ false hp ?_ fun _ => rfl
    simp only [Spec.Rsa.publicPrecompute, bytesAt_length, hv, Bool.false_eq_true, ite_false]
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = true := by simpa using hb
    refine WP.mono (pcMain_ok M hs₂ h0₂ hz hk1 hk2 (by rw [hm₂]; exact hO) (by rw [hm₂, hK, ofNat_toNat64])
      (by rw [hm₂]; exact hN) (c.hnb.congrK i₂ kk) (bytesAt_length _ _ _) hv hw c.hps)
      fun t ⟨ws, hws, hp⟩ => fin t ws true hp (by rw [hws]; rfl) fun h => absurd h (by decide)

end VG.Proof.Bignum.AArch64
