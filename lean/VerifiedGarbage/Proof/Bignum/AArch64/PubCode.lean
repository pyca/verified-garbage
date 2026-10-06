import VerifiedGarbage.Proof.Bignum.AArch64.PdCode

/-!
# RSAEP from the modulus on AArch64: correctness

`Public.code` checks the modulus as `vg_rsa_public_precompute` does, then
runs `Precompute`'s steps but for writing the values out, and
`Precomputed.rest` (`pubCode_correct`), against `pubContract`, which states
the shared contract's precondition on the registers and the stack.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-! ## The contract on the registers and the stack -/

/-- `vg_rsa_public(out = x0, out_len = x1, n = x2, n_len = x3, e = x4,
e_len = x5, input = x6, input_len = x7, scratch = [sp],
scratch_len = [sp + 8])`. -/
def pubContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let n : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let e : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let inp : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    s.sp.toNat + 16 ≤ 2 ^ 64 ∧ s.rd = [n, e, inp, pdArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint scr ∧ out.Disjoint (pdArgs s) ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ scr.Disjoint (pdArgs s) ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x3).toNat ∧ (s.gpr .x1).toNat = (s.gpr .x3).toNat ∧
      (s.gpr .x7).toNat = (s.gpr .x3).toNat ∧ 1 ≤ (s.gpr .x5).toNat ∧
      (s.gpr .x5).toNat ≤ (s.gpr .x3).toNat ∧ Spec.Rsa.scratchWords (s.gpr .x3).toNat ≤ (stackArg s 1).toNat
  post s s' :=
    Spec.Rsa.written s'.mem (s.gpr .x0) (s.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
      (Spec.Rsa.publicOp (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x3).toNat))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
      s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x4) (s₂.gpr .x5).toNat

/-- What `Public.code` uses of its contract's precondition, for the working
space `B` (the first stack argument) of `Z` bytes and the modulus' length
`k`. -/
structure PubCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .x3).toNat
  hk2 : (s.gpr .x3).toNat ≤ 1024
  hL1 : 1 ≤ (s.gpr .x5).toNat
  hL2 : (s.gpr .x5).toNat ≤ (s.gpr .x3).toNat
  hZ : 128 * (s.gpr .x3).toNat ≤ (stackArg s 1).toNat * 8
  hs : Scr s (stackArg s 0) ((stackArg s 1).toNat * 8)
  ha0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8
  hnb : Src s (stackArg s 0) ((stackArg s 1).toNat * 8) (s.gpr .x2)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  heb : Src s (stackArg s 0) ((stackArg s 1).toNat * 8) (s.gpr .x4)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
  hxb : Src s (stackArg s 0) ((stackArg s 1).toNat * 8) (s.gpr .x6)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x3).toNat)
  hout : ∀ j < (s.gpr .x3).toNat, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 j) 1
  houts : ∀ j < (s.gpr .x3).toNat, (stackArg s 1).toNat * 8 ≤ ofs (stackArg s 0) (s.gpr .x0 + BitVec.ofNat 64 j)

theorem pubCtx_of {s : State} (h : pubContract.pre s) : PubCtx s := by
  simp only [pubContract] at h
  obtain ⟨hsp, hrd, hwr, dOn, dOe, dOi, dOs, dOa, dns, des, dis, dsa,
    wO, wN, wE, wI, wS, hk, hol, hil, hL1, hL2, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 0) ((stackArg s 1).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  refine ⟨hk1, hk2, hL1, hL2, by omega, hs,
    ⟨pdArgs s, by rw [hrd]; simp, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩,
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd]; simp) (by omega) des,
    src_of_region (by rw [hrd, ← hil]; simp) (by omega) (by rw [← hil]; exact dis),
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., contains_byte _ (by omega) (by omega)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega) (by omega))⟩

/-! ## The entry -/

/-- `entry true`: the header, from the arguments (`n_len` for `k`), and the
working space's base (the first stack argument) in `x0`. -/
theorem pubEntry_ok {s : State} {B : Addr} (hB : stackArg s 0 = B)
    (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8)
    (ha0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) :
    WP isa (.block (Precomputed.entry true)) s fun t => t.gpr .x0 = B ∧
      word t.mem B (8 * sOut) = s.gpr .x0 ∧ word t.mem B (8 * sN) = s.gpr .x2 ∧
      word t.mem B (8 * sK) = s.gpr .x3 ∧ word t.mem B (8 * sE) = s.gpr .x4 ∧
      word t.mem B (8 * sElen) = s.gpr .x5 ∧ word t.mem B (8 * sIn) = s.gpr .x6 ∧
      Outside B 0 (8 * 22) s.mem t.mem ∧ Keep [.x0, .x8] s t := by
  have ha0' : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := ha0
  have hB' : s.mem.readW s.sp 64 = B := by
    rw [← hB]; simp only [stackArg, stackArgAddr, Nat.mul_zero, off_zero]
  refine WP.mono (WP.keep [.x0, .x8] (Q := fun t => t.gpr .x0 = B ∧
      t.mem = (((((s.mem.writeW (off B (8 * sOut)) (s.gpr .x0)).writeW (off B (8 * sN)) (s.gpr .x2)).writeW
        (off B (8 * sK)) (s.gpr .x3)).writeW (off B (8 * sE)) (s.gpr .x4)).writeW (off B (8 * sElen))
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

/-- `abiPreserved` from registers kept. -/
theorem abi_of_keep {rs : List Reg} {s t : State} (k : Keep rs s t) (h : ∀ r ∈ preserved, r ∉ rs) :
    abiPreserved s t :=
  ⟨fun r hr => k.gpr r (h r hr), k.sp, k.vcs⟩

theorem pubCode_correct (s : State) (h : pubContract.pre s) :
    ∃ t s', Exec isa Public.code s t s' ∧ abiPreserved s s' ∧ pubContract.post s s' := by
  have c := pubCtx_of h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  suffices hwp : WP isa Public.code s fun s' => abiPreserved s s' ∧ pubContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold Public.code
  have hw : ∀ i < 22, InRegions s.wr (off (stackArg s 0) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pubEntry_ok rfl hw c.ha0) fun t₁ ⟨h0, hO, hN, hK, hE, hL, hIn, ho₁, k₁⟩ => ?_
  have i₁ : InScr (stackArg s 0) ((stackArg s 1).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega)
  have hnb₁ := c.hnb.congrK i₁ k₁
  refine WP.mono (invalid_ok (k₁.gpr .x2 (by decide)) (by rw [k₁.gpr .x3 (by decide), ofNat_toNat64]) hk1 hk2
    (bytesAt_length _ _ _) (fun i hi => hnb₁.rd i (by rw [bytesAt_length]; exact hi)) (fun i hi => hnb₁.val i _))
    fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_
  have kk := k₁.trans k₂
  have hs₂ := c.hs.congr kk.wr
  have h0₂ : t₂.gpr .x0 = stackArg s 0 := (k₂.gpr .x0 (by decide)).trans h0
  have hz : slot (((s.gpr .x3).toNat + 7) / 8) 8 ≤ (stackArg s 1).toNat * 8 := by unfold slot hdrBytes; omega
  have i₂ : InScr (stackArg s 0) ((stackArg s 1).toNat * 8) s.mem t₂.mem := by rw [hm₂]; exact i₁
  have hO₂ : word t₂.mem (stackArg s 0) (8 * sOut) = s.gpr .x0 := by rw [hm₂]; exact hO
  have hK₂ : word t₂.mem (stackArg s 0) (8 * sK) = BitVec.ofNat 64 (s.gpr .x3).toNat := by
    rw [hm₂, hK, ofNat_toNat64]
  have hout₂ : ∀ j < (s.gpr .x3).toNat, InRegions t₂.wr (s.gpr .x0 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [kk.wr]; exact c.hout j hj
  -- What either branch leaves.
  have fin : ∀ {rs : List Reg} (t : State) (r : Nat) (cb : Bool), Keep rs t₂ t → (∀ r ∈ preserved, r ∉ rs) →
      Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x3).toNat = Spec.Rsa.i2osp r (s.gpr .x3).toNat →
      t.gpr .x0 = BitVec.ofNat 64 cb.toNat →
      (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
          (s.gpr .x3).toNat = true →
        cb = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x3).toNat) <
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)) ∧
        r = if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x3).toNat) <
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) then
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x3).toNat) ^
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat) %
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) else 0) →
      (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
          (s.gpr .x3).toNat = false → cb = false ∧ r = 0) →
      abiPreserved s t ∧ pubContract.post s t := by
    intro rs t r cb kt hrs hb hx hc hf
    refine ⟨⟨fun r hr => (kt.gpr r (hrs r hr)).trans (kk.gpr r (by revert r; decide)), kt.sp.trans kk.sp,
      fun r hr => (kt.vcs r hr).trans (kk.vcs r hr)⟩, ?_⟩
    exact written_of (bytesAt_length _ _ _) hb hx hc hf
  refine WP.ite (!Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
    (s.gpr .x3).toNat) (by rw [eval_zero, hz₂]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb => ?_) (fun hb => ?_)
  · -- Not a valid modulus.
    have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = false := by simpa using hb
    refine WP.mono (pdFail_ok hs₂ h0₂ (by omega) (by omega) (by omega) hO₂ hK₂ hout₂)
      fun t ⟨hbz, hx0, _, kf⟩ => fin t 0 false kf (by decide) (by rw [hbz, i2osp_zero'])
        (by rw [hx0]; rfl) (fun h => absurd h (by rw [hv]; decide)) fun _ => ⟨rfl, rfl⟩
  · have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (s.gpr .x3).toNat = true := by simpa using hb
    obtain ⟨hodd, hN1, hlo⟩ := valid_facts hv hk1
    have hn' : (stackArg s 0).toNat + slot (((s.gpr .x3).toNat + 7) / 8) 8 ≤ 2 ^ 64 := by omega
    refine wp_seqs_append (by simp [pcLoad]) (by simp [r2Steps])
      (WP.mono (pcLoad_ok hs₂ h0₂ hz (by omega) (by omega) hK₂ (by rw [hm₂]; exact hN)
        (c.hnb.congrK i₂ kk) (bytesAt_length _ _ _) hodd) fun t₃ ⟨minv, hg₃, hn₃, hinv₃, f₃, k₃⟩ => ?_)
    refine wp_seqs_append (by simp [r2Steps]) (by simp)
      (WP.mono (r2_ok Mont.base hg₃ hz (by omega) (by omega) hn₃ hinv₃ hodd hlo)
        fun t₄ ⟨hg₄, hlt₄, hr₄, f₄, k₄⟩ => ?_)
    rw [seqs_one]
    have x₂₄ := (Fixed.of_frm f₃ (pcLoadRanges_fixed _)).trans (Fixed.of_frm f₄ (r2Ranges_fixed _))
    have i₂₄ : InScr (stackArg s 0) ((stackArg s 1).toNat * 8) s.mem t₄.mem := i₂.trans
      ((InScr.of_frm f₃ fun r hr => Nat.le_trans (pcLoadRanges_le _ r hr) hz).trans
        (InScr.of_frm f₄ fun r hr => Nat.le_trans (r2Ranges_le _ r hr) hz))
    have k₂₄ := kk.trans (k₃.trans k₄)
    have hpre : PdPre t₄ (stackArg s 0) ((stackArg s 1).toNat * 8) (s.gpr .x3).toNat (s.gpr .x0) (s.gpr .x4)
        (s.gpr .x6) (s.gpr .x5).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x3).toNat)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat))
        (wv t₄.mem (stackArg s 0) (slot (((s.gpr .x3).toNat + 7) / 8) aR2) (((s.gpr .x3).toNat + 7) / 8)) :=
      { scr := hg₄.scr, x0 := hg₄.x0, z := hz, k1 := hk1, k2 := hk2,
        hO := by rw [x₂₄ sOut (by decide)]; exact hO₂, hK := by rw [x₂₄ sK (by decide)]; exact hK₂,
        hE := by rw [x₂₄ sE (by decide), hm₂]; exact hE,
        hL := by rw [x₂₄ sElen (by decide), hm₂, hL, ofNat_toNat64],
        hIn := by rw [x₂₄ sIn (by decide), hm₂]; exact hIn, hW := hg₄.hdr.hw, hb := hg₄.hdr.harr,
        n := by rw [f₄.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact hn₃, r := rfl,
        odd := hodd, n1 := hN1, rlt := hlt₄, x := c.hxb.congrK i₂₄ k₂₄, e := c.heb.congrK i₂₄ k₂₄,
        xl := bytesAt_length _ _ _, el := bytesAt_length _ _ _, L1 := c.hL1, L2 := c.hL2,
        out := fun j hj => by rw [k₂₄.wr]; exact c.hout j hj, outSep := c.houts }
    refine WP.mono (pdRest_ok (M := Mont.base) hpre) fun t ⟨x, hx, hp⟩ =>
      fin t _ _ ((k₃.trans k₄).trans hp.keep) (by decide) hp.bytes hp.x0 (fun _ => ⟨rfl, ?_⟩)
        fun h => absurd h (by rw [hv]; decide)
    rw [Nat.pow_mod, hx hr₄, ← Nat.pow_mod]

end VG.Proof.Bignum.AArch64
