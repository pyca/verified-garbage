import VerifiedGarbage.Proof.Rsa.AArch64.PrivCrt

/-!
# `vg_rsa_private_checked` on AArch64: the calls of the public operation

`pcArgs` keeps `r₁` and sets the arguments of `vg_rsa_public_precompute`
(`pcArgs_ok`), which writes `n`'s values to `PRE` (`pc_call`); `pdArgs`
keeps `r₃` and sets those of `vg_rsa_public_precomputed_checked`
(`pdArgs_ok`), which writes `M^e mod n` to `out` (`pd_call`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- `2 ⌈k / 8⌉`, as `preWords` computes it. -/
theorem preWords_eq (k : BitVec 64) (hk : k.toNat ≤ 1024) :
    (k + BitVec.ofNat 64 7) >>> 3 + (k + BitVec.ofNat 64 7) >>> 3 =
      BitVec.ofNat 64 (2 * ((k.toNat + 7) / 8)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := k.toNat + 7 % 2 ^ 64) (by omega)]
  have : (k.toNat + 7) / 2 ^ 3 < 2 ^ 63 := by omega
  rw [Nat.mod_eq_of_lt (a := (k.toNat + 7 % 2 ^ 64) / 2 ^ 3 + (k.toNat + 7 % 2 ^ 64) / 2 ^ 3) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem pw_le {L : Lay} (hL : L.Ok) : L.pw ≤ 256 := by have := hL.khi; unfold Lay.pw; omega

theorem toNat_pw {L : Lay} (hL : L.Ok) : (BitVec.ofNat 64 L.pw).toNat = L.pw := by
  have := pw_le hL
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-! ## `vg_rsa_public_precompute` -/

/-- The arguments of `vg_rsa_public_precompute`. -/
structure PcArgs (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.B + BitVec.ofNat 64 oPre
  x1 : t.gpr .x1 = BitVec.ofNat 64 L.pw
  x2 : t.gpr .x2 = L.n
  x3 : t.gpr .x3 = L.k
  x4 : t.gpr .x4 = L.scr
  x5 : t.gpr .x5 = L.sl

theorem pcArgs_ok (hL : L.Ok) (ha : ArgsAt L m₀) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem) :
    WP isa (.block pcArgs) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ PcArgs L t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 oR1) 64 = t.gpr .x0 ∧
      Frame [⟨L.B + BitVec.ofNat 64 oR1, 8⟩] t.mem t'.mem := by
  have hnB := hL.nB
  have lK := hc.inFr hL (d := oK) (n := 8) (by decide)
  have lN := hc.inFr hL (d := oN) (n := 8) (by decide)
  have w := hc.inFrW hL (d := oR1) (n := 8) (by decide)
  have l10 := hc.inArgs hL (j := 10) (by omega)
  have l11 := hc.inArgs hL (j := 11) (by omega)
  have a10 := (hc.argW hL (j := 10) (by omega)).trans (ha 10 (by omega))
  have a11 := (hc.argW hL (j := 11) (by omega)).trans (ha 11 (by omega))
  have hf : Frame [⟨L.B + BitVec.ofNat 64 oR1, 8⟩] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 oR1) (t.gpr .x0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hsl := hs.frame hf (fun R hR => by
    simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint L.B (d := oOut) (n := 48) (e := oR1) (k := 8) (by decide) (by simp only [oOut]; omega)
      (by simp only [oR1]; omega)) (by omega)
  have k' : (t.mem.writeW (L.B + BitVec.ofNat 64 oR1) (t.gpr .x0)).readW (L.B + BitVec.ofNat 64 oK) 64 = L.k :=
    hsl.k
  have n' : (t.mem.writeW (L.B + BitVec.ofNat 64 oR1) (t.gpr .x0)).readW (L.B + BitVec.ofNat 64 oN) 64 = L.n :=
    hsl.n
  have hfr : Frame [L.FR] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 oR1) (t.gpr .x0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have ea : ∀ j < 12, ((t.mem.writeW (L.B + BitVec.ofNat 64 oR1) (t.gpr .x0)).readW
      (L.B + BitVec.ofNat 64 (arg j)) 64) = t.mem.readW (L.B + BitVec.ofNat 64 (arg j)) 64 := fun j hj =>
    Mem.readW_writeW_sep (Offset.sep _ (d := arg j) (n := 8) (e := oR1) (k := 8)
      (by simp only [oR1, arg, frameBytes]; omega) (by simp only [arg, frameBytes]; omega)
      (by simp only [oR1]; omega)) (by decide)
  apply WP.of_runBlock
  simp only [pcArgs, preWords, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load,
    State.store, State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.map_some, Option.bind_some, reduceCtorEq,
    ite_false, ite_true, hc.sp, w, read8, write8, BitVec.add_zero, Option.some.injEq, exists_eq_left',
    show oR1 % 8 = 0 by decide, show oR1 < 4096 * 8 by decide, show oPre < 4096 by decide,
    show (0 : Nat) < 4096 by decide, show oK % 8 = 0 by decide, show oK < 32768 by decide,
    show oN % 8 = 0 by decide, show oN < 32768 by decide, show arg 10 % 8 = 0 by decide,
    show arg 10 < 32768 by decide, show arg 11 % 8 = 0 by decide, show arg 11 < 32768 by decide,
    show (7 : Nat) < 4096 by decide, show (3 : Nat) < 64 by decide, and_self, lK, lN, l10, l11,
    k', n', ea 10 (by omega), ea 11 (by omega), a10, a11, Lay.argv]
  refine ⟨hc.store hL rfl rfl hc.sp.symm rfl (by priv_cs_tac) hfr, hsl, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩,
    Mem.readW_writeW_self64 _ _ _, hf⟩
  all_goals simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
  exact preWords_eq _ hL.khi

/-- The regions `vg_rsa_public_precompute` reads and writes. -/
abbrev pcRd (L : Lay) : List Region := [L.N]
abbrev pcWr (L : Lay) : List Region := [L.PRE, L.SC]

theorem pcCall_pre (hL : L.Ok) {t : State} (_hc : Ctx L g vv m₀ t) (ha : PcArgs L t) :
    pcA.pre (t.callEntry.withRegions (pcRd L) (pcWr L)) := by
  have hnB := hL.nB
  have hk := hL.khi
  have hP := hL.stk_sub hL.PRE_sub
  simp only [pcA, State.withRegions_rd, State.withRegions_wr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, toNat_pw hL]
  have hPk : BitVec.toNat (L.B + BitVec.ofNat 64 oPre) + L.pw * 8 ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat]; have := pw_le hL; simp only [oPre]; omega
  exact ⟨trivial, trivial, hP.2.1, hP.2.2.2.2.2.2.2.2.2, hL.nsc, hPk, hL.bn, hL.bsc, ⟨hL.klo, hL.khi⟩, rfl,
    hL.slk⟩

theorem pc_sub (hL : L.Ok) : ∀ r ∈ pcRd L ++ pcWr L, ∃ R ∈ L.regions, Within r R := by
  have hk := hL.khi
  simp only [pcRd, pcWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.N, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.FR, by simp, within_off _ (by simp only [oPre, frameBytes, Lay.pw]; omega)⟩
  · exact ⟨L.SC, by simp, within_base _ (Nat.le_refl _)⟩

theorem pc_wsub (hL : L.Ok) : ∀ r ∈ pcWr L, InW L r := by
  simp only [pcWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr (.inr hL.PRE_HI)
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))

/-- What `vg_rsa_public_precompute` writes and returns, from the memory `m`
at the call. -/
abbrev PcOut (L : Lay) (m m' : Mem) (r : BitVec 64) : Prop :=
  match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt m L.n L.k.toNat) with
  | some ws => r.setWidth 32 = 1 ∧ Spec.Rsa.wordsAt m' (L.B + BitVec.ofNat 64 oPre) L.pw = ws
  | none => r.setWidth 32 = 0 ∧
    Spec.Rsa.wordsAt m' (L.B + BitVec.ofNat 64 oPre) L.pw = List.replicate L.pw 0

theorem pc_call (v : CrtImpl) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem)
    (ha : PcArgs L t) :
    WP isa (.call v.pcName v.pc) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧
      Frame (pcWr L) t.mem t'.mem ∧ PcOut L t.mem t'.mem (t'.gpr .x0) := by
  refine call_ok hL v.pc_ok v.pcNoFrames hc hs (pcCall_pre hL hc ha) (pc_sub hL) (pc_wsub hL)
    fun s' hc' hs' hf hpost => ⟨hc', hs', hf, ?_⟩
  have h := hpost
  simp only [pcA, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, toNat_pw hL] at h
  exact h

/-! ## `vg_rsa_public_precomputed_checked` -/

/-- The arguments of `vg_rsa_public_precomputed_checked`, in registers and
on the stack at `B`. -/
structure PdArgs (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.out
  x1 : t.gpr .x1 = L.k
  x2 : t.gpr .x2 = L.B + BitVec.ofNat 64 oPre
  x3 : t.gpr .x3 = BitVec.ofNat 64 L.pw
  x4 : t.gpr .x4 = L.e
  x5 : t.gpr .x5 = L.el
  x6 : t.gpr .x6 = L.B + BitVec.ofNat 64 oM
  x7 : t.gpr .x7 = L.k
  s0 : t.mem.readW L.B 64 = L.scr
  s1 : t.mem.readW (L.B + BitVec.ofNat 64 8) 64 = L.sl

theorem pdArgs_ok (hL : L.Ok) (ha : ArgsAt L m₀) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem) :
    WP isa (.block pdArgs) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ PdArgs L t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 oR3) 64 = t.gpr .x0 ∧
      Frame [⟨L.B + BitVec.ofNat 64 oR3, 8⟩, ⟨L.B, 16⟩] t.mem t'.mem := by
  have hnB := hL.nB
  have lK := hc.inFr hL (d := oK) (n := 8) (by decide)
  have lO := hc.inFr hL (d := oOut) (n := 8) (by decide)
  have lE := hc.inFr hL (d := oE) (n := 8) (by decide)
  have lEl := hc.inFr hL (d := oEl) (n := 8) (by decide)
  have w3 := hc.inFrW hL (d := oR3) (n := 8) (by decide)
  have w0 := hc.inFrW hL (d := 0) (n := 8) (by decide)
  have w8 := hc.inFrW hL (d := 8) (n := 8) (by decide)
  simp only [BitVec.add_zero] at w0
  have l10 := hc.inArgs hL (j := 10) (by omega)
  have l11 := hc.inArgs hL (j := 11) (by omega)
  have a10 := (hc.argW hL (j := 10) (by omega)).trans (ha 10 (by omega))
  have a11 := (hc.argW hL (j := 11) (by omega)).trans (ha 11 (by omega))
  -- The three stores.
  have sepA : ∀ j < 12, ∀ d, d + 8 ≤ frameBytes → Mem.Sep (L.B + BitVec.ofNat 64 (arg j)) (64 / 8)
      (L.B + BitVec.ofNat 64 d) (64 / 8) := fun j hj d hd =>
    Offset.sep _ (d := arg j) (n := 8) (e := d) (k := 8) (by simp only [arg, frameBytes] at hd ⊢; omega)
      (by simp only [arg, frameBytes]; omega) (by simp only [frameBytes] at hd; omega)
  have f1 : Frame [⟨L.B + BitVec.ofNat 64 oR3, 8⟩] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 oR3) (t.gpr .x0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have s1 := hs.frame f1 (fun R hR => by
    simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint L.B (d := oOut) (n := 48) (e := oR3) (k := 8) (by decide) (by simp only [oOut]; omega)
      (by simp only [oR3]; omega)) (by omega)
  have e10 : (t.mem.writeW (L.B + BitVec.ofNat 64 oR3) (t.gpr .x0)).readW (L.B + BitVec.ofNat 64 (arg 10)) 64 = L.scr :=
    (Mem.readW_writeW_sep (sepA 10 (by omega) oR3 (by decide)) (by decide)).trans a10
  have e11 : ((t.mem.writeW (L.B + BitVec.ofNat 64 oR3) (t.gpr .x0)).writeW L.B L.scr).readW (L.B + BitVec.ofNat 64 (arg 11)) 64 = L.sl := by
    have := sepA 11 (by omega) 0 (by decide)
    simp only [BitVec.add_zero] at this
    exact (Mem.readW_writeW_sep this (by decide)).trans
      ((Mem.readW_writeW_sep (sepA 11 (by omega) oR3 (by decide)) (by decide)).trans a11)
  apply WP.of_runBlock
  simp only [pdArgs, preWords, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.load, State.store, State.read, Size.bits, Size.bytes, BitVec.setWidth_eq,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.map_some,
    Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.sp, read8, write8, BitVec.add_zero,
    Option.some.injEq, exists_eq_left', show oR3 % 8 = 0 by decide, show oR3 < 4096 * 8 by decide,
    show oPre < 4096 by decide, show oM < 4096 by decide, show (0 : Nat) < 4096 by decide,
    show oK % 8 = 0 by decide, show oK < 32768 by decide, show oOut % 8 = 0 by decide,
    show oOut < 32768 by decide, show oE % 8 = 0 by decide, show oE < 32768 by decide,
    show oEl % 8 = 0 by decide, show oEl < 32768 by decide, show arg 10 % 8 = 0 by decide,
    show arg 10 < 32768 by decide, show arg 11 % 8 = 0 by decide, show arg 11 < 32768 by decide,
    show (0 : Nat) % 8 = 0 by decide, show (0 : Nat) < 4096 * 8 by decide,
    show (8 : Nat) < 4096 * 8 by decide, show (7 : Nat) < 4096 by decide, show (3 : Nat) < 64 by decide,
    and_self, lK, lO, lE, lEl, l10, l11, w3, w0, w8, s1.out, s1.k, s1.e, s1.el, e10, e11]
  have hc3 : (⟨L.B + BitVec.ofNat 64 oR3, 8⟩ : Region).Contains (L.B + BitVec.ofNat 64 oR3) (64 / 8) :=
    Region.contains_self _ _
  have hc0 : (⟨L.B, 16⟩ : Region).Contains L.B (64 / 8) := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
  have hc8 : (⟨L.B, 16⟩ : Region).Contains (L.B + BitVec.ofNat 64 8) (64 / 8) :=
    Offset.contains_base _ (by decide) (by decide)
  have f3 : Frame [⟨L.B + BitVec.ofNat 64 oR3, 8⟩, ⟨L.B, 16⟩] t.mem
      (((t.mem.writeW (L.B + BitVec.ofNat 64 oR3) (t.gpr .x0)).writeW L.B L.scr).writeW
        (L.B + BitVec.ofNat 64 8) L.sl) :=
    (((Frame.refl _ _).writeW (by simp) _ hc3).writeW (by simp) _ hc0).writeW (by simp) _ hc8
  have fFR : Frame [L.FR] t.mem
      (((t.mem.writeW (L.B + BitVec.ofNat 64 oR3) (t.gpr .x0)).writeW L.B L.scr).writeW
        (L.B + BitVec.ofNat 64 8) L.sl) := Frame.sub f3 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.FR, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨L.FR, by simp, Region.sub_prefix (by decide)⟩
  have s3 := hs.frame f3 (fun R hR => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact Offset.disjoint L.B (d := oOut) (n := 48) (e := oR3) (k := 8) (by decide)
        (by simp only [oOut]; omega) (by simp only [oR3]; omega)
    · exact Offset.disjoint_base _ (by decide) (by simp only [oOut]; omega)) (by omega)
  have sep08 : Mem.Sep L.B (64 / 8) (L.B + BitVec.ofNat 64 8) (64 / 8) := by
    have := Offset.sep L.B (d := 0) (n := 8) (e := 8) (k := 8) (by decide) (by decide) (by omega)
    simpa using this
  have sepR : ∀ d, d + 8 ≤ oR3 → Mem.Sep (L.B + BitVec.ofNat 64 oR3) (64 / 8) (L.B + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => Offset.sep L.B (d := oR3) (n := 8) (e := d) (k := 8) (by omega) (by simp only [oR3]; omega)
      (by simp only [oR3] at hd; omega)
  have sepR0 : Mem.Sep (L.B + BitVec.ofNat 64 oR3) (64 / 8) L.B (64 / 8) := by
    have := sepR 0 (by decide); simpa using this
  refine ⟨hc.store hL rfl rfl hc.sp.symm rfl (by priv_cs_tac) fFR, s3, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, f3⟩
  all_goals try simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
  · exact preWords_eq _ hL.khi
  · rw [Mem.readW_writeW_sep sep08 (by decide), Mem.readW_writeW_self64]
  · exact Mem.readW_writeW_self64 _ _ _
  · rw [Mem.readW_writeW_sep (sepR 8 (by decide)) (by decide), Mem.readW_writeW_sep sepR0 (by decide),
      Mem.readW_writeW_self64]

theorem OUT_k (hL : L.Ok) : (⟨L.out, L.k.toNat⟩ : Region) = L.OUT := by rw [Lay.OUT, hL.olk]

/-- The regions `vg_rsa_public_precomputed_checked` reads and writes. -/
abbrev pdRd (L : Lay) : List Region := [L.PRE, L.E, L.M, ⟨L.B, 16⟩]
abbrev pdWr (L : Lay) : List Region := [⟨L.out, L.k.toNat⟩, L.SC]

theorem pdCall_pre (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (ha : PdArgs L t) :
    pdA.pre (t.callEntry.withRegions (pdRd L) (pdWr L)) := by
  have hnB := hL.nB
  have hk := hL.khi
  have sa0 : stackArg (t.callEntry.withRegions (pdRd L) (pdWr L)) 0 = L.scr := by
    simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
      State.callEntry_sp, hc.sp, Nat.mul_zero, BitVec.add_zero]
    exact ha.s0
  have sa1 : stackArg (t.callEntry.withRegions (pdRd L) (pdWr L)) 1 = L.sl := by
    simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
      State.callEntry_sp, hc.sp]
    exact ha.s1
  have hP := hL.stk_sub hL.PRE_sub
  have hM := hL.stk_sub hL.M_sub
  have hA := hL.stk_sub (low_sub L (n := 16) (by decide))
  simp only [pdRd, pdWr, OUT_k hL] at sa0 sa1
  simp only [pdA, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    hc.sp, sa0, sa1, stackArgAddr, Nat.mul_zero, BitVec.add_zero,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, ha.x7, toNat_pw hL, OUT_k hL, pdRd, pdWr]
  have hPk : BitVec.toNat (L.B + BitVec.ofNat 64 oPre) + L.pw * 8 ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat]; have := pw_le hL; simp only [oPre]; omega
  have hMk : BitVec.toNat (L.B + BitVec.ofNat 64 oM) + L.k.toNat ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat]; simp only [oM]; omega
  exact ⟨by omega, trivial, trivial, hP.1.symm, hL.oe, hM.1.symm, hL.osc, hA.1.symm, hP.2.2.2.2.2.2.2.2.2,
    hL.esc, hM.2.2.2.2.2.2.2.2.2, hA.2.2.2.2.2.2.2.2.2.symm, by rw [← hL.olk]; exact hL.bo, hPk, hL.be, hMk,
    hL.bsc, ⟨hL.klo, hL.khi⟩, rfl, trivial, hL.el1, hL.elk, hL.slk⟩

theorem pd_sub (hL : L.Ok) : ∀ r ∈ pdRd L ++ pdWr L, ∃ R ∈ L.regions, Within r R := by
  have hk := hL.khi
  simp only [pdRd, pdWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, within_off _ (by simp only [oPre, frameBytes, Lay.pw]; omega)⟩
  · exact ⟨L.E, by simp, within_base _ (Nat.le_refl _)⟩
  · exact ⟨L.FR, by simp, within_off _ (by simp only [oM, frameBytes]; omega)⟩
  · exact ⟨L.FR, by simp, within_base _ (by decide)⟩
  · exact ⟨L.OUT, by simp, within_base _ (by rw [hL.olk])⟩
  · exact ⟨L.SC, by simp, within_base _ (Nat.le_refl _)⟩

theorem pd_wsub (hL : L.Ok) : ∀ r ∈ pdWr L, InW L r := by
  simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (within_base _ (by rw [hL.olk]))
  · exact .inr (.inl (within_base _ (Nat.le_refl _)))

/-- What `vg_rsa_public_precomputed_checked` writes and returns, from the
memory `m` at the call. -/
abbrev PdOut (L : Lay) (m m' : Mem) (r : BitVec 64) : Prop :=
  ∀ nB : List Byte, nB.length = L.k.toNat →
    Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt m (L.B + BitVec.ofNat 64 oPre) L.pw) →
    Spec.Rsa.written m' L.out L.k.toNat (r.setWidth 32)
      (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt m L.e L.el.toNat)
        (Spec.Rsa.bytesAt m (L.B + BitVec.ofNat 64 oM) L.k.toNat))

theorem pd_call (v : CrtImpl) (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem)
    (ha : PdArgs L t) :
    WP isa (.call v.pdName v.pd) t fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧
      Frame (pdWr L) t.mem t'.mem ∧ PdOut L t.mem t'.mem (t'.gpr .x0) := by
  refine call_ok hL v.pd_ok v.pdNoFrames hc hs (pdCall_pre hL hc ha) (pd_sub hL) (pd_wsub hL)
    fun s' hc' hs' hf hpost => ⟨hc', hs', hf, ?_⟩
  have h := hpost
  simp only [pdA, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
    gpr_ce _ _ _ (by decide : Reg.x0 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x1 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x4 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x5 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs),
    ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.x6, toNat_pw hL] at h
  exact h

end

end VG.Proof.Rsa.AArch64
