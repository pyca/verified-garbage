import VerifiedGarbage.Proof.Bignum.AArch64.PdRest

/-!
# `vg_rsa_public_precomputed` on AArch64: correctness

The entry (`pdEntry_ok`), and the whole function without the check of `e`
(`pdCode_correct`), against `pdContract`, which states the shared contract's
precondition on the registers and the stack.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

variable {M : Mont}

/-! ## The contract on the registers and the stack -/

/-- The two arguments on the stack. -/
abbrev pdArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- `vg_rsa_public_precomputed(out = x0, out_len = x1, pre = x2,
pre_len = x3, e = x4, e_len = x5, input = x6, input_len = x7,
scratch = [sp], scratch_len = [sp + 8])`. -/
def pdContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let pre : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 8⟩
    let e : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let inp : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    s.sp.toNat + 16 ≤ 2 ^ 64 ∧ s.rd = [pre, e, inp, pdArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint pre ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint scr ∧ out.Disjoint (pdArgs s) ∧
      pre.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ scr.Disjoint (pdArgs s) ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat * 8 ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x1).toNat ∧ (s.gpr .x3).toNat = Spec.Rsa.precomputedWords (s.gpr .x1).toNat ∧
      (s.gpr .x7).toNat = (s.gpr .x1).toNat ∧ 1 ≤ (s.gpr .x5).toNat ∧
      (s.gpr .x5).toNat ≤ (s.gpr .x1).toNat ∧ Spec.Rsa.scratchWords (s.gpr .x1).toNat ≤ (stackArg s 1).toNat
  post s s' :=
    ∀ nB : List Byte, nB.length = (s.gpr .x1).toNat →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) →
      Spec.Rsa.written s'.mem (s.gpr .x0) (s.gpr .x1).toNat ((s'.gpr .x0).setWidth 32)
        (Spec.Rsa.publicOp nB (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x1).toNat))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
      s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧
      Spec.Rsa.wordsAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
        Spec.Rsa.wordsAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x4) (s₂.gpr .x5).toNat

/-! ## The entry -/

theorem exec_ldrSp_x' (s : State) {t : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8) :
    exec (.ldrSp t off) s = some (s.write .x t (s.mem.readW (s.sp + BitVec.ofNat 64 off) 64)) := by
  simp only [exec, ho, and_self, ite_true, State.load, h, Option.map_some, Mem.readW]

/-- `entry`: the header, from the arguments (`out_len` for `k`), and the
working space's base (the first stack argument) in `x0`. -/
theorem pdEntry_ok {s : State} {B : Addr} (hB : stackArg s 0 = B)
    (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8)
    (ha0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) :
    WP isa (.block (Precomputed.entry false)) s fun t => t.gpr .x0 = B ∧
      word t.mem B (8 * sOut) = s.gpr .x0 ∧ word t.mem B (8 * sN) = s.gpr .x2 ∧
      word t.mem B (8 * sK) = s.gpr .x1 ∧ word t.mem B (8 * sE) = s.gpr .x4 ∧
      word t.mem B (8 * sElen) = s.gpr .x5 ∧ word t.mem B (8 * sIn) = s.gpr .x6 ∧
      Outside B 0 (8 * 22) s.mem t.mem ∧ Keep [.x0, .x8] s t := by
  have ha0' : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := ha0
  have hB' : s.mem.readW s.sp 64 = B := by
    rw [← hB]; simp only [stackArg, stackArgAddr, Nat.mul_zero, off_zero]
  refine WP.mono (WP.keep [.x0, .x8] (Q := fun t => t.gpr .x0 = B ∧
      t.mem = (((((s.mem.writeW (off B (8 * sOut)) (s.gpr .x0)).writeW (off B (8 * sN)) (s.gpr .x2)).writeW
        (off B (8 * sK)) (s.gpr .x1)).writeW (off B (8 * sE)) (s.gpr .x4)).writeW (off B (8 * sElen))
          (s.gpr .x5)).writeW (off B (8 * sIn)) (s.gpr .x6)) (by
    unfold Precomputed.entry
    brun [exec_ldrSp_x' _ (show 0 % 8 = 0 ∧ 0 < 32768 by decide) ha0', hB',
      hdr_enc (show sOut < 32 by decide), hdr_enc (show sN < 32 by decide), hdr_enc (show sK < 32 by decide),
      hdr_enc (show sE < 32 by decide), hdr_enc (show sElen < 32 by decide), hdr_enc (show sIn < 32 by decide),
      hw sOut (by decide), hw sN (by decide), hw sK (by decide), hw sE (by decide), hw sElen (by decide),
      hw sIn (by decide)]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k⟩ => ?_
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, k⟩
  all_goals try (rw [hm]; simp (disch := decide) only [hdrStore_hdr, word_writeW_self]; done)
  rw [hm]
  intro x hx
  have e : ∀ i, i < 22 → ∀ (m : Mem) (v : BitVec 64), (m.writeW (off B (8 * i)) v) x = m x := fun i hi m v =>
    writeW_outside m B v (d := 8 * i) (by omega) x (by omega)
  rw [e sIn (by decide), e sElen (by decide), e sE (by decide), e sK (by decide), e sN (by decide),
    e sOut (by decide)]

/-! ## The whole function -/

/-- What `code` uses of its contract's precondition, for the working space
`B` (the first stack argument) of `Z` bytes, the modulus' length `k` and
`pre`'s `2 w` words. -/
structure PdCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .x1).toNat
  hk2 : (s.gpr .x1).toNat ≤ 1024
  hL1 : 1 ≤ (s.gpr .x5).toNat
  hL2 : (s.gpr .x5).toNat ≤ (s.gpr .x1).toNat
  hpl : (s.gpr .x3).toNat = 2 * (((s.gpr .x1).toNat + 7) / 8)
  hZ : 128 * (s.gpr .x1).toNat ≤ (stackArg s 1).toNat * 8
  hs : Scr s (stackArg s 0) ((stackArg s 1).toNat * 8)
  ha0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8
  hpr : ∀ i < 2 * (((s.gpr .x1).toNat + 7) / 8), InRegions (s.rd ++ s.wr) (off (s.gpr .x2) (8 * i)) 8
  hps : ∀ j < 16 * (((s.gpr .x1).toNat + 7) / 8),
    (stackArg s 1).toNat * 8 ≤ ofs (stackArg s 0) (s.gpr .x2 + BitVec.ofNat 64 j)
  heb : Src s (stackArg s 0) ((stackArg s 1).toNat * 8) (s.gpr .x4)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
  hxb : Src s (stackArg s 0) ((stackArg s 1).toNat * 8) (s.gpr .x6)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x1).toNat)
  hout : ∀ j < (s.gpr .x1).toNat, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 j) 1
  houts : ∀ j < (s.gpr .x1).toNat, (stackArg s 1).toNat * 8 ≤ ofs (stackArg s 0) (s.gpr .x0 + BitVec.ofNat 64 j)

theorem pdCtx_of {s : State} (h : pdContract.pre s) : PdCtx s := by
  simp only [pdContract] at h
  obtain ⟨hsp, hrd, hwr, dOp, dOe, dOi, dOs, dOa, dps, des, dis, dsa,
    wO, wP, wE, wI, wS, hk, hpl, hil, hL1, hL2, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords at hpl
  have hs : Scr s (stackArg s 0) ((stackArg s 1).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hpre : (⟨s.gpr .x2, (s.gpr .x3).toNat * 8⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨hk1, hk2, hL1, hL2, hpl, by omega, hs,
    ⟨pdArgs s, by rw [hrd]; simp, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩,
    fun i hi => ⟨_, hpre, Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj => out_scr dps (contains_byte _ (by omega) (by omega)),
    src_of_region (by rw [hrd]; simp) (by omega) des,
    src_of_region (by rw [hrd, ← hil]; simp) (by omega) (by rw [← hil]; exact dis),
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., contains_byte _ (by omega) (by omega)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega) (by omega))⟩

/-- `pre`'s words after the entry, as before it. -/
theorem pre_wv_entry {s t₁ : State} (c : PdCtx s)
    (i₁ : InScr (stackArg s 0) ((stackArg s 1).toNat * 8) s.mem t₁.mem) {e : Nat}
    (he : e + 8 * (((s.gpr .x1).toNat + 7) / 8) ≤ 16 * (((s.gpr .x1).toNat + 7) / 8)) :
    wv t₁.mem (s.gpr .x2) e (((s.gpr .x1).toNat + 7) / 8) = wv s.mem (s.gpr .x2) e (((s.gpr .x1).toNat + 7) / 8) :=
  wv_congr fun i hi => Mem.readW_congr fun b hb => i₁ _ (by
    have := c.hps (e + 8 * i + b) (by omega); rwa [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat])

/-- `rest`'s hypotheses, after the entry and the load, for values that pass
the checks. -/
theorem pdPre_of {s t₁ t₂ : State} (c : PdCtx s) (h0 : t₁.gpr .x0 = stackArg s 0)
    (hO : word t₁.mem (stackArg s 0) (8 * sOut) = s.gpr .x0) (hK : word t₁.mem (stackArg s 0) (8 * sK) = s.gpr .x1)
    (hE : word t₁.mem (stackArg s 0) (8 * sE) = s.gpr .x4) (hL : word t₁.mem (stackArg s 0) (8 * sElen) = s.gpr .x5)
    (hIn : word t₁.mem (stackArg s 0) (8 * sIn) = s.gpr .x6)
    (ho₁ : Outside (stackArg s 0) 0 (8 * 22) s.mem t₁.mem) (k₁ : Keep [.x0, .x8] s t₁)
    (hW₂ : word t₂.mem (stackArg s 0) (8 * sW) = BitVec.ofNat 64 (((s.gpr .x1).toNat + 7) / 8))
    (hb₂ : ∀ j < 8, word t₂.mem (stackArg s 0) (8 * sArr j) = off (stackArg s 0) (slot (((s.gpr .x1).toNat + 7) / 8) j))
    (f₂ : Frm (stackArg s 0) (pdLoadRanges (((s.gpr .x1).toNat + 7) / 8)) t₁.mem t₂.mem) (k₂ : Keep mmRegs t₁ t₂)
    (hodd : wv t₂.mem (stackArg s 0) (slot (((s.gpr .x1).toNat + 7) / 8) aN) (((s.gpr .x1).toNat + 7) / 8) % 2 = 1)
    (hN1 : 1 < wv t₂.mem (stackArg s 0) (slot (((s.gpr .x1).toNat + 7) / 8) aN) (((s.gpr .x1).toNat + 7) / 8))
    (hRN : wv t₂.mem (stackArg s 0) (slot (((s.gpr .x1).toNat + 7) / 8) aR2) (((s.gpr .x1).toNat + 7) / 8) <
      wv t₂.mem (stackArg s 0) (slot (((s.gpr .x1).toNat + 7) / 8) aN) (((s.gpr .x1).toNat + 7) / 8)) :
    PdPre t₂ (stackArg s 0) ((stackArg s 1).toNat * 8) (s.gpr .x1).toNat (s.gpr .x0) (s.gpr .x4)
      (s.gpr .x6) (s.gpr .x5).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x1).toNat)
      (wv t₂.mem (stackArg s 0) (slot (((s.gpr .x1).toNat + 7) / 8) aN) (((s.gpr .x1).toNat + 7) / 8))
      (wv t₂.mem (stackArg s 0) (slot (((s.gpr .x1).toNat + 7) / 8) aR2) (((s.gpr .x1).toNat + 7) / 8)) := by
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  have hz : slot (((s.gpr .x1).toNat + 7) / 8) 8 ≤ (stackArg s 1).toNat * 8 := by unfold slot hdrBytes; omega
  have x₂ := Fixed.of_frm f₂ (pdLoadRanges_fixed _)
  have i₂ : InScr (stackArg s 0) ((stackArg s 1).toNat * 8) s.mem t₂.mem :=
    (InScr.of_outside ho₁ (by omega)).trans (InScr.of_frm f₂ fun r hr => Nat.le_trans (pdLoadRanges_le _ r hr) hz)
  have kk := k₁.trans k₂
  exact
    { scr := c.hs.congr kk.wr, x0 := (k₂.gpr .x0 (by decide)).trans h0, z := hz, k1 := hk1, k2 := hk2,
      hO := by rw [x₂ sOut (by decide)]; exact hO, hK := by rw [x₂ sK (by decide), hK, ofNat_toNat64],
      hE := by rw [x₂ sE (by decide)]; exact hE, hL := by rw [x₂ sElen (by decide), hL, ofNat_toNat64],
      hIn := by rw [x₂ sIn (by decide)]; exact hIn, hW := hW₂, hb := hb₂, n := rfl, r := rfl, odd := hodd,
      n1 := hN1, rlt := hRN, x := c.hxb.congrK i₂ kk, e := c.heb.congrK i₂ kk, xl := bytesAt_length _ _ _,
      el := bytesAt_length _ _ _, L1 := c.hL1, L2 := c.hL2, out := fun j hj => by rw [kk.wr]; exact c.hout j hj,
      outSep := c.houts }

theorem pdCode_correct (M : Mont) (s : State) (h : pdContract.pre s) :
    ∃ t s', Exec isa (Precomputed.code M.mm) s t s' ∧ abiPreserved s s' ∧ pdContract.post s s' := by
  have c := pdCtx_of h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  suffices hwp : WP isa (Precomputed.code M.mm) s fun s' => abiPreserved s s' ∧ pdContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold Precomputed.code
  have hw : ∀ i < 22, InRegions s.wr (off (stackArg s 0) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  refine WP.seq (WP.mono (pdEntry_ok rfl hw c.ha0) fun t₁ ⟨h0, hO, hN, hK, hE, hL, hIn, ho₁, k₁⟩ => ?_)
  have i₁ : InScr (stackArg s 0) ((stackArg s 1).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega)
  have hz : slot (((s.gpr .x1).toNat + 7) / 8) 8 ≤ (stackArg s 1).toNat * 8 := by unfold slot hdrBytes; omega
  refine WP.seq (WP.mono (pdLoad_ok (c.hs.congr k₁.wr) h0 hz (by omega) (by omega) (by rw [hK, ofNat_toNat64])
    hN (fun i hi => by rw [k₁.rd, k₁.wr]; exact c.hpr i hi) c.hps)
    fun t₂ ⟨hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩ => ?_)
  rw [pre_wv_entry c i₁ (by omega)] at hN₂
  rw [pre_wv_entry c i₁ (by omega)] at hR₂
  have x₂ := Fixed.of_frm f₂ (pdLoadRanges_fixed _)
  have i₂ : InScr (stackArg s 0) ((stackArg s 1).toNat * 8) s.mem t₂.mem :=
    i₁.trans (InScr.of_frm f₂ fun r hr => Nat.le_trans (pdLoadRanges_le _ r hr) hz)
  have kk := k₁.trans k₂
  have hs₂ := c.hs.congr kk.wr
  have h0₂ : t₂.gpr .x0 = stackArg s 0 := (k₂.gpr .x0 (by decide)).trans h0
  have hO₂ : word t₂.mem (stackArg s 0) (8 * sOut) = s.gpr .x0 := by rw [x₂ sOut (by decide)]; exact hO
  have hK₂ : word t₂.mem (stackArg s 0) (8 * sK) = BitVec.ofNat 64 (s.gpr .x1).toNat := by
    rw [x₂ sK (by decide), hK, ofNat_toNat64]
  have hout₂ : ∀ j < (s.gpr .x1).toNat, InRegions t₂.wr (s.gpr .x0 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [kk.wr]; exact c.hout j hj
  -- What either branch leaves.
  have fin : ∀ t r (cb : Bool),
      MainPost t₂ t (stackArg s 0) ((stackArg s 1).toNat * 8) (s.gpr .x1).toNat (s.gpr .x0) r cb →
      (∀ nB : List Byte, nB.length = (s.gpr .x1).toNat →
        Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) (s.gpr .x1).toNat = true →
        wv s.mem (s.gpr .x2) 0 (((s.gpr .x1).toNat + 7) / 8) = Spec.Rsa.os2ip nB →
        wv s.mem (s.gpr .x2) (8 * (((s.gpr .x1).toNat + 7) / 8)) (((s.gpr .x1).toNat + 7) / 8) =
          2 ^ (128 * (((s.gpr .x1).toNat + 7) / 8)) % Spec.Rsa.os2ip nB →
        cb = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x1).toNat) < Spec.Rsa.os2ip nB) ∧
        r = if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x1).toNat) < Spec.Rsa.os2ip nB then
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x1).toNat) ^
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) % Spec.Rsa.os2ip nB else 0) →
      abiPreserved s t ∧ pdContract.post s t := by
    intro t r cb hp H
    refine ⟨abiPreserved_of_keep ((kk.trans hp.keep).mono (by decide)), fun nB hl hpp => ?_⟩
    rw [c.hpl] at hpp
    obtain ⟨hv, hNv, hRv⟩ := pre_of_some hl hk1 hpp
    exact written_of hl hp.bytes hp.x0 (fun _ => H nB hl hv hNv hRv) fun h => absurd h (by rw [hv]; decide)
  generalize hcb : (decide ((word t₂.mem (stackArg s 0) (slot (((s.gpr .x1).toNat + 7) / 8) aN)).toNat % 2 = 1) &&
      decide (wv t₂.mem (stackArg s 0) (slot (((s.gpr .x1).toNat + 7) / 8) aR2) (((s.gpr .x1).toNat + 7) / 8) <
        wv t₂.mem (stackArg s 0) (slot (((s.gpr .x1).toNat + 7) / 8) aN) (((s.gpr .x1).toNat + 7) / 8)) &&
      decide (word t₂.mem (stackArg s 0) (slot (((s.gpr .x1).toNat + 7) / 8) aN + 8 * ((((s.gpr .x1).toNat + 7) / 8) - 1)) ≠ 0))
    = cb
  have hz₂' : t₂.gpr .x9 = BitVec.ofNat 64 cb.toNat := by
    rw [hz₂, ← hcb, Bool.and_comm (decide (wv _ _ _ _ < _))]
  refine WP.ite (!cb) (by rw [eval_zero, hz₂']; cases cb <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · -- Values of no modulus.
    have hcf : cb = false := by simpa using hb
    refine WP.mono (pdFail_ok hs₂ h0₂ (by omega) (by omega) (by omega) hO₂ hK₂ hout₂)
      fun t ⟨hbz, hx0, hfr, kf⟩ => fin t 0 false ⟨?_, by rw [hx0]; rfl,
        fun x _ hx => hfr x hx, kf⟩ fun nB hl hv hNv hRv => ?_
    · rw [← bytesAt_eq, hbz, i2osp_zero']
    obtain ⟨hodd, -, hlo⟩ := valid_facts hv hk1
    have := checks_true (by omega) (hN₂.trans hNv) hodd hlo
      (by rw [hR₂, hRv]; exact Nat.mod_lt _ (by omega))
    rw [hcb, hcf] at this
    exact absurd this (by decide)
  · have hct : cb = true := by simpa using hb
    rw [hct] at hcb
    obtain ⟨hodd, hN1, hRN⟩ := checks_facts (by omega) hcb
    have hpre := pdPre_of c h0 hO hK hE hL hIn ho₁ k₁ hW₂ hb₂ f₂ k₂ hodd hN1 hRN
    refine WP.mono (pdRest_ok (M := M) hpre) fun t ⟨x, hx, hp⟩ => fin t _ _ hp fun nB hl hv hNv hRv => ?_
    rw [hN₂.trans hNv] at hx hp ⊢
    have hxX := hx (by
      rw [hR₂, hRv, Nat.mod_mod, ← Nat.pow_add, show 128 * (((s.gpr .x1).toNat + 7) / 8) =
        64 * (((s.gpr .x1).toNat + 7) / 8) + 64 * (((s.gpr .x1).toNat + 7) / 8) by omega])
    refine ⟨rfl, ?_⟩
    rw [Nat.pow_mod, hxX, ← Nat.pow_mod]

end VG.Proof.Bignum.AArch64
