import VerifiedGarbage.Proof.Rsa.AArch64.CkCode
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyMain

/-!
# `vg_rsa_check_crt_key` on AArch64: correctness

`CheckCrtKey.code`, from a state its contract allows, returns 1 exactly when
`checkCrtKey` accepts its inputs (`ckcCode_correct`), against `ckcA`, which
states the shared contract's precondition on the registers and the stack.
The inputs of `main` are `CkIn`'s with `p` as `d` (`ckcIn`): the entry
stores `p` and `p_len` in `d`'s slots too.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey (sE sElen sD sDlen sP sPlen sQ sQlen sDP sDQ sQI)
open VG.Impl.Rsa.AArch64.CheckCrtKey (entry)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

/-- `checkCrtKey` of the inputs of a state. -/
def ckcKeyOf (s : State) : Bool :=
  Spec.Rsa.checkCrtKey (Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat) (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .x5).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 4) (s.gpr .x5).toNat)

/-- `vg_rsa_check_crt_key(n = x0, n_len = x1, e = x2, e_len = x3, p = x4,
p_len = x5, q = x6, q_len = x7, dp = [sp], dp_len = [sp + 8],
dq = [sp + 16], dq_len = [sp + 24], qinv = [sp + 32], qinv_len = [sp + 40],
scratch = [sp + 48], scratch_len = [sp + 56])`. -/
def ckcA : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let e : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let p : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let q : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let dp : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let dq : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let qi : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let scr : Region := ⟨stackArg s 6, (stackArg s 7).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 64⟩
    s.sp.toNat + 64 ≤ 2 ^ 64 ∧
      s.rd = [n, e, p, q, dp, dq, qi, args] ∧ s.wr = [scr] ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧ (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x1).toNat ∧ 1 ≤ (s.gpr .x3).toNat ∧ (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat ∧
      1 ≤ (s.gpr .x5).toNat ∧ (s.gpr .x5).toNat < (s.gpr .x1).toNat ∧
      1 ≤ (s.gpr .x7).toNat ∧ (s.gpr .x7).toNat < (s.gpr .x1).toNat ∧
      (stackArg s 1).toNat = (s.gpr .x5).toNat ∧ (stackArg s 5).toNat = (s.gpr .x5).toNat ∧
      (stackArg s 3).toNat = (s.gpr .x7).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .x1).toNat ≤ (stackArg s 7).toNat
  post s s' := (s'.gpr .x0).setWidth 32 = if ckcKeyOf s then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 8).map (stackArg s₁) = (List.range 8).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x0) (s₁.gpr .x1).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x0) (s₂.gpr .x1).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat

/-! ## The entry -/

theorem ckcEntry_eq : entry = ([.ldrSp .x8 48, .str .x .x0 .x8 (8 * Public.sN), .str .x .x1 .x8 (8 * Public.sK),
    .str .x .x2 .x8 (8 * sE), .str .x .x3 .x8 (8 * sElen), .str .x .x4 .x8 (8 * sD), .str .x .x5 .x8 (8 * sDlen),
    .str .x .x4 .x8 (8 * sP), .str .x .x5 .x8 (8 * sPlen), .str .x .x6 .x8 (8 * sQ), .str .x .x7 .x8 (8 * sQlen)] :
    List Instr) ++ (hdrPairs [(0, sDP), (2, sDQ), (4, sQI)] ++ ([mov .x0 .x8, mov .x4 .x2, mov .x5 .x3] : List Instr)) :=
  rfl

/-- The header after the stores from registers. -/
def ckcEntryMemA (m : Mem) (B : Addr) (vn vk ve vel vp vpl vq vql : BitVec 64) : Mem :=
  (((((((((m.writeW (off B (8 * Public.sN)) vn).writeW (off B (8 * Public.sK)) vk).writeW (off B (8 * sE)) ve).writeW
    (off B (8 * sElen)) vel).writeW (off B (8 * sD)) vp).writeW (off B (8 * sDlen)) vpl).writeW
    (off B (8 * sP)) vp).writeW (off B (8 * sPlen)) vpl).writeW (off B (8 * sQ)) vq).writeW (off B (8 * sQlen)) vql

/-- The header after the entry's stores. -/
def ckcEntryMem (m : Mem) (B : Addr) (vn vk ve vel vp vpl vq vql vdp vdq vqi : BitVec 64) : Mem :=
  (((ckcEntryMemA m B vn vk ve vel vp vpl vq vql).writeW (off B (8 * sDP)) vdp).writeW
    (off B (8 * sDQ)) vdq).writeW (off B (8 * sQI)) vqi

theorem ckcEntryMemA_outside (m : Mem) (B : Addr) (vn vk ve vel vp vpl vq vql : BitVec 64) :
    Outside B 0 (8 * 32) m (ckcEntryMemA m B vn vk ve vel vp vpl vq vql) := by
  unfold ckcEntryMemA
  repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _)

theorem ckcEntryMem_facts (m : Mem) (B : Addr) (vn vk ve vel vp vpl vq vql vdp vdq vqi : BitVec 64) :
    let m' := ckcEntryMem m B vn vk ve vel vp vpl vq vql vdp vdq vqi
    word m' B (8 * Public.sN) = vn ∧ word m' B (8 * Public.sK) = vk ∧ word m' B (8 * sE) = ve ∧
    word m' B (8 * sElen) = vel ∧ word m' B (8 * sD) = vp ∧ word m' B (8 * sDlen) = vpl ∧
    word m' B (8 * sP) = vp ∧ word m' B (8 * sPlen) = vpl ∧ word m' B (8 * sQ) = vq ∧
    word m' B (8 * sQlen) = vql ∧ word m' B (8 * sDP) = vdp ∧ word m' B (8 * sDQ) = vdq ∧
    word m' B (8 * sQI) = vqi ∧ Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' ckcEntryMem ckcEntryMemA
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, the working space's base
(stack argument 6) in `x0`, and `e` and `e_len` in `x4` and `x5`. -/
theorem ckcEntry_ok {s : State} {B : Addr} (hB : stackArg s 6 = B)
    (hw : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8)
    (ha : ∀ j < 8, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8)
    (hsep : ∀ j < 8, ∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s j) 64 = stackArg s j) :
    WP isa (.block entry) s fun t => t.gpr .x0 = B ∧ t.gpr .x4 = s.gpr .x2 ∧ t.gpr .x5 = s.gpr .x3 ∧
      t.mem = ckcEntryMem s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)
        (s.gpr .x6) (s.gpr .x7) (stackArg s 0) (stackArg s 2) (stackArg s 4) ∧
      Keep [.x0, .x4, .x5, .x8, .x9] s t := by
  have hB' : s.mem.readW (s.sp + BitVec.ofNat 64 48) 64 = B := hB
  have ha6 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 48) 8 := ha 6 (by decide)
  have ho : 48 % 8 = 0 ∧ 48 < 32768 := ⟨rfl, by decide⟩
  rw [ckcEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = B ∧
      t.mem = ckcEntryMemA s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)
        (s.gpr .x6) (s.gpr .x7)) ?_ (by decide) (by decide) (by decide +kernel))
    fun t₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_
  · brun [exec_ldrSp ho ha6, hB', hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
      hdr_enc (show sE < 32 by decide), hdr_enc (show sElen < 32 by decide), hdr_enc (show sD < 32 by decide),
      hdr_enc (show sDlen < 32 by decide), hdr_enc (show sP < 32 by decide), hdr_enc (show sPlen < 32 by decide),
      hdr_enc (show sQ < 32 by decide), hdr_enc (show sQlen < 32 by decide),
      hw Public.sN (by decide), hw Public.sK (by decide), hw sE (by decide), hw sElen (by decide), hw sD (by decide),
      hw sDlen (by decide), hw sP (by decide), hw sPlen (by decide), hw sQ (by decide), hw sQlen (by decide)]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (hdrPairs_ok _ t₁ ?_ h8 k₁.sp k₁.rd k₁.wr
    (by rw [hm₁]; exact ckcEntryMemA_outside _ _ _ _ _ _ _ _ _ _)) fun t₂ ⟨hm₂, k₂⟩ => ?_
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      exact ⟨by decide, by decide, ha _ (by decide), hsep _ (by decide), hw _ (by decide)⟩
  have h8₂ : t₂.gpr .x8 = B := (k₂.gpr .x8 (by decide)).trans h8
  have k12 := k₁.trans k₂
  refine WP.mono (WP.keep [.x0, .x4, .x5] (Q := fun t => t.gpr .x0 = B ∧ t.gpr .x4 = s.gpr .x2 ∧
      t.gpr .x5 = s.gpr .x3 ∧ t.mem = t₂.mem)
    (by brun [h8₂, k12.gpr .x2 (by decide), k12.gpr .x3 (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h0, h4, h5, hm⟩, k₃⟩ => ⟨h0, h4, h5, by rw [hm, hm₂, hm₁]; rfl, (k12.trans k₃).mono (by decide)⟩

/-! ## The precondition, as the code uses it -/

/-- The inputs of `main`, from the entry state: `p` also as `d`. -/
def ckcIn (s : State) : CkIn where
  B := stackArg s 6
  Z := (stackArg s 7).toNat * 8
  k := (s.gpr .x1).toNat
  el := (s.gpr .x3).toNat
  dl := (s.gpr .x5).toNat
  pl := (s.gpr .x5).toNat
  ql := (s.gpr .x7).toNat
  pN := s.gpr .x0
  pE := s.gpr .x2
  pD := s.gpr .x4
  pP := s.gpr .x4
  pQ := s.gpr .x6
  pDp := stackArg s 0
  pDq := stackArg s 2
  pQi := stackArg s 4
  nb := Spec.Rsa.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat
  eb := Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat
  db := Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
  pb := Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat
  qb := Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat
  dpb := Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .x5).toNat
  dqb := Spec.Rsa.bytesAt s.mem (stackArg s 2) (s.gpr .x7).toNat
  qib := Spec.Rsa.bytesAt s.mem (stackArg s 4) (s.gpr .x5).toNat
  W := s.wr

/-- What `CheckCrtKey.code` uses of its contract's precondition. -/
structure CkcCtx (s : State) : Prop where
  L : CkLens (ckcIn s)
  hs : Scr s (stackArg s 6) ((stackArg s 7).toNat * 8)
  ha : ∀ j < 8, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hsep : ∀ j < 8, ∀ m', Outside (stackArg s 6) 0 (8 * 32) s.mem m' →
    m'.readW (stackArgAddr s j) 64 = stackArg s j
  n : Src s (stackArg s 6) ((stackArg s 7).toNat * 8) (s.gpr .x0) (ckcIn s).nb
  e : Src s (stackArg s 6) ((stackArg s 7).toNat * 8) (s.gpr .x2) (ckcIn s).eb
  p : Src s (stackArg s 6) ((stackArg s 7).toNat * 8) (s.gpr .x4) (ckcIn s).pb
  q : Src s (stackArg s 6) ((stackArg s 7).toNat * 8) (s.gpr .x6) (ckcIn s).qb
  dp : Src s (stackArg s 6) ((stackArg s 7).toNat * 8) (stackArg s 0) (ckcIn s).dpb
  dq : Src s (stackArg s 6) ((stackArg s 7).toNat * 8) (stackArg s 2) (ckcIn s).dqb
  qi : Src s (stackArg s 6) ((stackArg s 7).toNat * 8) (stackArg s 4) (ckcIn s).qib

theorem ckcCtx_of {s : State} (h : ckcA.pre s) : CkcCtx s := by
  simp only [ckcA] at h
  obtain ⟨hsp, hrd, hwr, dns, des, dps, dqs, ddps, ddqs, dqis, dsa, wN, wE, wP, wQ, wDp, wDq, wQi, wS, hk,
    hel1, hel2, hpl1, hpl2, hql1, hql2, hdpl, hqil, hdql, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 6) ((stackArg s 7).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 64⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  rw [hdpl] at ddps wDp hrd
  rw [hqil] at dqis wQi hrd
  rw [hdql] at ddqs wDq hrd
  refine ⟨⟨hk1, hk2, hel1, hel2, hpl1, Nat.le_of_lt hpl2, hpl1, hpl2, hql1, hql2, bytesAt_length _ _ _,
      bytesAt_length _ _ _, bytesAt_length _ _ _, bytesAt_length _ _ _, bytesAt_length _ _ _, bytesAt_length _ _ _,
      bytesAt_length _ _ _, bytesAt_length _ _ _, by simp only [ckcIn]; omega⟩, hs,
    fun j hj => ⟨_, hargs, by rw [stkAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := 8 * j + b) (len := 64) (by omega) (by omega))
      rw [← stkAddr_add s j b] at this; omega)),
    src_of_region (by rw [hrd]; simp) (by omega) dns,
    src_of_region (by rw [hrd]; simp) (by omega) des,
    src_of_region (by rw [hrd]; simp) (by omega) dps,
    src_of_region (by rw [hrd]; simp) (by omega) dqs,
    src_of_region (by rw [hrd]; simp) (by omega) ddps,
    src_of_region (by rw [hrd]; simp) (by omega) ddqs,
    src_of_region (by rw [hrd]; simp) (by omega) dqis⟩

/-- After `entry`, from `s`. -/
structure CkcHeadPost (s t : State) : Prop where
  scr : Scr t (stackArg s 6) ((stackArg s 7).toNat * 8)
  x0 : t.gpr .x0 = stackArg s 6
  x4 : t.gpr .x4 = s.gpr .x2
  x5 : t.gpr .x5 = BitVec.ofNat 64 (s.gpr .x3).toNat
  args : CkArgs t.mem (ckcIn s).B (ckcIn s).k (ckcIn s).el (ckcIn s).dl (ckcIn s).pl (ckcIn s).ql (ckcIn s).pN
    (ckcIn s).pE (ckcIn s).pD (ckcIn s).pP (ckcIn s).pQ (ckcIn s).pDp (ckcIn s).pDq (ckcIn s).pQi
  inScr : InScr (stackArg s 6) ((stackArg s 7).toNat * 8) s.mem t.mem
  keep : Keep [.x0, .x4, .x5, .x8, .x9] s t

/-- `entry`. -/
theorem ckcHead_ok' {s : State} (c : CkcCtx s) : WP isa (.block entry) s (CkcHeadPost s) := by
  have hn := c.hs.nowrap
  have hZ : 128 * (s.gpr .x1).toNat ≤ (stackArg s 7).toNat * 8 := c.L.z
  have hk1 : 64 ≤ (s.gpr .x1).toNat := c.L.k1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 6) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  refine WP.mono (ckcEntry_ok rfl hw c.ha c.hsep) fun t ⟨h0, h4, h5, hm, k⟩ => ?_
  obtain ⟨hN, hK, hE, hEl, hD, hDl, hP, hPl, hQ, hQl, hDP, hDQ, hQI, ho⟩ :=
    ckcEntryMem_facts s.mem (stackArg s 6) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (s.gpr .x3) (s.gpr .x4) (s.gpr .x5)
      (s.gpr .x6) (s.gpr .x7) (stackArg s 0) (stackArg s 2) (stackArg s 4)
  rw [← hm] at hN hK hE hEl hD hDl hP hPl hQ hQl hDP hDQ hQI ho
  refine ⟨c.hs.congr k.wr, h0, h4, by rw [h5, ofNat_toNat64],
    ⟨hN, show word _ (stackArg s 6) _ = BitVec.ofNat 64 (s.gpr .x1).toNat by rw [hK, ofNat_toNat64], hE,
      show word _ (stackArg s 6) _ = BitVec.ofNat 64 (s.gpr .x3).toNat by rw [hEl, ofNat_toNat64], hD,
      show word _ (stackArg s 6) _ = BitVec.ofNat 64 (s.gpr .x5).toNat by rw [hDl, ofNat_toNat64], hP,
      show word _ (stackArg s 6) _ = BitVec.ofNat 64 (s.gpr .x5).toNat by rw [hPl, ofNat_toNat64], hQ,
      show word _ (stackArg s 6) _ = BitVec.ofNat 64 (s.gpr .x7).toNat by rw [hQl, ofNat_toNat64], hDP, hDQ,
      hQI⟩,
    InScr.of_outside ho (by omega), k⟩

/-- `main`'s hypotheses after the head and the checks of `e` and `n`. -/
theorem ckcPre_of {s t₁ t : State} (c : CkcCtx s) (h : CkcHeadPost s t₁) (hm : t.mem = t₁.mem)
    (k : Keep [.x2, .x3, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] t₁ t) :
    CkPre (ckcIn s) t := by
  have kk := h.keep.trans k
  have hi : InScr (stackArg s 6) ((stackArg s 7).toNat * 8) s.mem t.mem := by rw [hm]; exact h.inScr
  exact
    { scr := h.scr.congr k.wr, x0 := (k.gpr .x0 (by decide)).trans h.x0, args := by rw [hm]; exact h.args,
      n := c.n.congrK hi kk, e := c.e.congrK hi kk, d := c.p.congrK hi kk, p := c.p.congrK hi kk,
      q := c.q.congrK hi kk, dp := c.dp.congrK hi kk, dq := c.dq.congrK hi kk, qi := c.qi.congrK hi kk,
      L := c.L, wr := kk.wr }

theorem ckcKeyOf_eq (s : State) : ckcKeyOf s = Spec.Rsa.crtKeyValid (ckcIn s).k (ckcIn s).N (ckcIn s).E
    (ckcIn s).P (ckcIn s).Q (ckcIn s).DP (ckcIn s).DQ (ckcIn s).QI := by
  simp only [ckcKeyOf, Spec.Rsa.checkCrtKey, bytesAt_length]
  rfl

theorem ckcKeyValid_false {k N E P Q DP DQ QI : Nat}
    (h : Spec.Rsa.modulusValid N k = false ∨ Spec.Rsa.exponentValid E = false) :
    Spec.Rsa.crtKeyValid k N E P Q DP DQ QI = false := by
  unfold Spec.Rsa.crtKeyValid
  rcases h with h | h <;> simp [h]

/-- `vg_rsa_check_crt_key`. -/
theorem ckcCode_correct (s : State) (h : ckcA.pre s) :
    ∃ t s', Exec isa CheckCrtKey.code s t s' ∧ abiPreserved s s' ∧ ckcA.post s s' := by
  have c := ckcCtx_of h
  clear h
  have hk1 : 64 ≤ (s.gpr .x1).toNat := c.L.k1
  have hk2 : (s.gpr .x1).toNat ≤ 1024 := c.L.k2
  have hel1 : 1 ≤ (s.gpr .x3).toNat := c.L.el1
  have hel2 : (s.gpr .x3).toNat ≤ (s.gpr .x1).toNat := c.L.el2
  suffices hwp : WP isa CheckCrtKey.code s fun s' => abiPreserved s s' ∧ ckcA.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, hg, hp⟩
  unfold CheckCrtKey.code
  refine WP.seq (WP.mono (ckcHead_ok' c) fun t₁ h₁ => ?_)
  have heb₁ := c.e.congrK h₁.inScr h₁.keep
  have hel : (ckcIn s).eb.length = (s.gpr .x3).toNat := bytesAt_length _ _ _
  refine WP.seq (WP.mono (expCheck_ok (eb := (ckcIn s).eb) h₁.x4 h₁.x5 hel1 (by omega)
    (fun i hi => heb₁.rd i (by rw [hel]; exact hi)) ?_) fun t₂ ⟨hz₂, hm₂, k₂⟩ => ?_)
  · rw [← hel]
    refine List.ext_getElem (by simp [Spec.Rsa.bytesAt]) fun i h1 h2 => ?_
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact (heb₁.val i h1).symm
  have kk₂ := h₁.keep.trans k₂
  refine WP.ite (!Spec.Rsa.exponentValid (ckcIn s).E) (by rw [eval_zero, hz₂]; cases Spec.Rsa.exponentValid _ <;> rfl)
    (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.exponentValid (ckcIn s).E = false := by simpa using hb
    refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0) (by brun [CheckKey.fail]) (by decide) (by decide)
      (by decide +kernel)) fun t ⟨h0, kt⟩ => ⟨abiPreserved_of_keep ((kk₂.trans kt).mono (by decide)), ?_⟩
    show (t.gpr .x0).setWidth 32 = if ckcKeyOf s then 1 else 0
    rw [ckcKeyOf_eq, ckcKeyValid_false (.inr hv), h0]
    rfl
  · have hv : Spec.Rsa.exponentValid (ckcIn s).E = true := by simpa using hb
    have hs₂ := h₁.scr.congr k₂.wr
    have hn := hs₂.nowrap
    have hZ : 128 * (s.gpr .x1).toNat ≤ (stackArg s 7).toNat * 8 := c.L.z
    have h0₂ : t₂.gpr .x0 = stackArg s 6 := (k₂.gpr .x0 (by decide)).trans h₁.x0
    have hl : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off (stackArg s 6) (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
    have aN : word t₂.mem (stackArg s 6) (8 * Public.sN) = s.gpr .x0 := by rw [hm₂]; exact h₁.args.n
    have aK : word t₂.mem (stackArg s 6) (8 * Public.sK) = BitVec.ofNat 64 (s.gpr .x1).toNat := by
      rw [hm₂]; exact h₁.args.k
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (WP.keep [.x2, .x3] (Q := fun t => t.gpr .x2 = s.gpr .x0 ∧
        t.gpr .x3 = BitVec.ofNat 64 (s.gpr .x1).toNat ∧ t.mem = t₂.mem) (by
      brun [h0₂, hdr_enc (show Public.sN < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
        hl Public.sN (by decide), hl Public.sK (by decide), aN, aK])
      (by decide) (by decide) (by decide +kernel)) fun t₃ ⟨⟨h2, h3, hm₃⟩, k₃⟩ => ?_
    have kk₃ := kk₂.trans k₃
    have hnb₃ := c.n.congrK (by rw [hm₃, hm₂]; exact h₁.inScr) kk₃
    have hnl : (ckcIn s).nb.length = (s.gpr .x1).toNat := bytesAt_length _ _ _
    refine WP.mono (WP.keep [.x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12] (invalid_ok h2 h3 hk1 hk2 hnl
      (fun i hi => hnb₃.rd i (by rw [hnl]; exact hi)) (fun i hi => hnb₃.val i _))
      (by decide) (by decide) (by decide +kernel)) fun t₄ ⟨⟨hz₄, hm₄, _⟩, k₄⟩ => ?_
    have kk₄ := kk₃.trans k₄
    refine WP.ite (!Spec.Rsa.modulusValid (ckcIn s).N (s.gpr .x1).toNat)
      (by rw [eval_zero, hz₄]; cases Spec.Rsa.modulusValid _ _ <;> rfl) (fun hb' => ?_) (fun hb' => ?_)
    · have hv' : Spec.Rsa.modulusValid (ckcIn s).N (s.gpr .x1).toNat = false := by simpa using hb'
      refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0) (by brun [CheckKey.fail]) (by decide) (by decide)
        (by decide +kernel)) fun t ⟨h0, kt⟩ => ⟨abiPreserved_of_keep ((kk₄.trans kt).mono (by decide)), ?_⟩
      show (t.gpr .x0).setWidth 32 = if ckcKeyOf s then 1 else 0
      rw [ckcKeyOf_eq, ckcKeyValid_false (k := (ckcIn s).k) (.inl hv'), h0]
      rfl
    · have hv' : Spec.Rsa.modulusValid (ckcIn s).N (s.gpr .x1).toNat = true := by simpa using hb'
      have hpre := ckcPre_of c h₁ (by rw [hm₄, hm₃, hm₂]) ((k₂.trans (k₃.trans k₄)).mono (by decide))
      refine WP.mono (WP.keep (.x0 :: mmRegs) (ckcMain_ok hpre hv' hv) (by decide +kernel)
        (by decide) (by decide +kernel)) fun t ⟨hx, kt⟩ =>
        ⟨abiPreserved_of_keep ((kk₄.trans kt).mono (by decide)), ?_⟩
      show (t.gpr .x0).setWidth 32 = if ckcKeyOf s then 1 else 0
      rw [ckcKeyOf_eq, hx, setWidth_flag]

end VG.Proof.Rsa.AArch64
