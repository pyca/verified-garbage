import VerifiedGarbage.Proof.Rsa.AArch64.PrivCall

/-!
# `vg_rsa_private_checked` on AArch64: the call of the CRT

From `CrtArgs`, the CRT reads `n`, the input, the private key and its stack
arguments at `B`, and writes `M` and `scratch` (`crt_call`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

theorem gpr_ce (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- The regions the CRT reads and writes. -/
abbrev crtRd (L : Lay) : List Region :=
  [L.N, ⟨L.inp, L.k.toNat⟩, L.P, L.Q, L.DP, L.DQ, L.QI, ⟨L.B, 80⟩]
abbrev crtWr (L : Lay) : List Region := [L.M, L.SC]

theorem low_sub (L : Lay) {n : Nat} (h : n ≤ stackBytes) : Region.Sub ⟨L.B, n⟩ L.STK := Region.sub_prefix h

namespace Lay.Ok
variable (hL : L.Ok)
include hL

/-- A range of the stack misses every buffer. -/
theorem stk_sub {r : Region} (h : Region.Sub r L.STK) :
    r.Disjoint L.OUT ∧ r.Disjoint L.N ∧ r.Disjoint L.E ∧ r.Disjoint L.IN ∧ r.Disjoint L.P ∧
      r.Disjoint L.Q ∧ r.Disjoint L.DP ∧ r.Disjoint L.DQ ∧ r.Disjoint L.QI ∧ r.Disjoint L.SC :=
  ⟨hL.ko.sub_left h, hL.kn.sub_left h, hL.ke.sub_left h, hL.ki.sub_left h, hL.kp.sub_left h,
    hL.kq.sub_left h, hL.kdp.sub_left h, hL.kdq.sub_left h, hL.kqi.sub_left h, hL.ksc.sub_left h⟩

theorem M_sub : Region.Sub L.M L.STK := Offset.sub_base _ (by have := hL.khi; simp only [oM, stackBytes]; omega)

theorem PRE_sub : Region.Sub L.PRE L.STK := by
  have := hL.khi
  refine Offset.sub_base _ ?_
  simp only [oPre, stackBytes, Lay.pw]; omega

theorem M_HI : Within L.M L.HI := ⟨0, by simp, by have := hL.khi; simp only [oM, frameBytes]; omega⟩

theorem PRE_HI : Within L.PRE L.HI :=
  ⟨oPre - oM, by rw [add_add]; rfl, by have := hL.khi; simp only [oPre, oM, frameBytes, Lay.pw]; omega⟩

theorem IN_k : Within ⟨L.inp, L.k.toNat⟩ L.IN := within_base _ (by rw [hL.ilk])

end Lay.Ok

theorem crtCall_pre (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (ha : CrtArgs L t) :
    crtA.pre (t.callEntry.withRegions (crtRd L) (crtWr L)) := by
  have hnB := hL.nB
  have hk := hL.khi
  have sa : ∀ i < 10, stackArg (t.callEntry.withRegions (crtRd L) (crtWr L)) i = L.argv (i + 2) := by
    intro i hi
    simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
      State.callEntry_sp, hc.sp]
    exact ha.stk i hi
  have hM := hL.stk_sub hL.M_sub
  have hA := hL.stk_sub (low_sub L (n := 80) (by decide))
  have hMA : L.M.Disjoint ⟨L.B, 80⟩ :=
    Offset.disjoint_base _ (by decide) (by simp only [oM]; omega)
  simp only [crtA, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    hc.sp, sa 0 (by omega), sa 1 (by omega), sa 2 (by omega), sa 3 (by omega), sa 4 (by omega),
    sa 5 (by omega), sa 6 (by omega), sa 7 (by omega), sa 8 (by omega), sa 9 (by omega), Lay.argv,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
  have hdp := hL.dpl
  have hqi := hL.qil
  have hdq := hL.dql
  have hIk : (⟨L.inp, L.k.toNat⟩ : Region).Disjoint L.SC := hL.isc.sub_left hL.IN_k.sub
  obtain ⟨-, hMn, -, hMi, hMp, hMq, hMdp, hMdq, hMqi, hMsc⟩ := hM
  have hMk : BitVec.toNat (L.B + BitVec.ofNat 64 oM) + L.k.toNat ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat]; simp only [oM]; omega
  exact ⟨by omega, trivial, trivial, hMn, hMi.sub_right hL.IN_k.sub, hMp, hMq, hMdp, hMdq, hMqi, hMsc, hMA,
    hL.nsc, hIk, hL.psc, hL.qsc, hL.dpsc, hL.dqsc, hL.qisc, hA.2.2.2.2.2.2.2.2.2.symm, hMk, hL.bn,
    by have := hL.bi; rw [hL.ilk] at this; exact this, hL.bp, hL.bq, hL.bdp, hL.bdq, hL.bqi, hL.bsc,
    ⟨hL.klo, hL.khi⟩, trivial, trivial, hL.pl1, hL.plk, hL.ql1, hL.qlk, hdp, hqi, hdq, hL.slk⟩

theorem crt_sub (hL : L.Ok) : ∀ r ∈ crtRd L ++ crtWr L, ∃ R ∈ L.regions, Within r R := by
  have hk := hL.khi
  simp only [crtRd, crtWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨L.N, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.IN, by simp, hL.IN_k⟩
  · exact ⟨L.P, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.Q, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.DP, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.DQ, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.QI, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.FR, by simp, within_base _ (by decide)⟩
  · exact ⟨L.FR, by simp, within_off _ (by simp only [oM, frameBytes]; omega)⟩
  · exact ⟨L.SC, by simp, within_base _ (Nat.le_refl _)⟩

theorem crt_wsub (hL : L.Ok) : ∀ r ∈ crtWr L, InW L r := by
  simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr (.inr hL.M_HI)
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))

/-- What the CRT writes to `M` and returns, from the memory `m` at the call. -/
abbrev CrtOut (L : Lay) (m m' : Mem) (r : BitVec 64) : Prop :=
  Spec.Rsa.written m' (L.B + BitVec.ofNat 64 oM) L.k.toNat (r.setWidth 32)
    (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt m L.n L.k.toNat) (Spec.Rsa.bytesAt m L.inp L.k.toNat)
      (Spec.Rsa.bytesAt m L.p L.pl.toNat) (Spec.Rsa.bytesAt m L.q L.ql.toNat)
      (Spec.Rsa.bytesAt m L.dp L.pl.toNat) (Spec.Rsa.bytesAt m L.dq L.ql.toNat)
      (Spec.Rsa.bytesAt m L.qi L.pl.toNat))

/-- The call of the CRT. -/
theorem crt_call (v : CrtImpl) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem)
    (ha : CrtArgs L t) :
    WP isa (.call v.name v.code) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧
      Frame (crtWr L) t.mem t'.mem ∧ CrtOut L t.mem t'.mem (t'.gpr .x0) := by
  refine call_ok hL v.crt_ok v.noFrames hc hs (crtCall_pre hL hc ha) (crt_sub hL) (crt_wsub hL)
    fun s' hc' hs' hf hpost => ⟨hc', hs', hf, ?_⟩
  have sa : ∀ i < 10, stackArg (t.callEntry.withRegions (crtRd L) (crtWr L)) i = L.argv (i + 2) := by
    intro i hi
    simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
      State.callEntry_sp, hc.sp]
    exact ha.stk i hi
  have h := hpost
  simp only [crtA, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.x0, ha.x2, ha.x3, ha.x4, ha.x6, ha.x7, sa 0 (by omega), sa 1 (by omega), sa 2 (by omega),
    sa 4 (by omega), sa 6 (by omega), Lay.argv] at h
  exact h

end

end VG.Proof.Rsa.AArch64
