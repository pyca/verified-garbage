import VerifiedGarbage.Proof.Rsa.AArch64.PrivTail

/-!
# `vg_rsa_private_checked` on AArch64: the tail

`tail_ok` runs the check and the release from the frames, after the calls:
whatever `M` and `out` hold and the calls returned.
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

theorem Keep.mono {rs rs' : List Reg} {a b : State} (h : Keep rs a b) (hs : ∀ r ∈ rs, r ∈ rs') :
    Keep rs' a b := ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp, h.v⟩

theorem bytesAt_ext {m m' : Mem} {p q : Addr} {k : Nat} {c : Prop} [Decidable c]
    (h : ∀ i < k, m' (p + BitVec.ofNat 64 i) = if c then m (q + BitVec.ofNat 64 i) else 0) :
    Spec.Rsa.bytesAt m' p k = if c then Spec.Rsa.bytesAt m q k else List.replicate k 0 := by
  split
  · rename_i hc
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi => by rw [h i (List.mem_range.mp hi), ite_pos' hc]
  · rename_i hc
    simp only [Spec.Rsa.bytesAt, List.eq_replicate_iff, List.length_map, List.length_range, List.mem_map,
      List.mem_range, true_and]
    rintro _ ⟨i, hi, rfl⟩
    rw [h i hi, ite_neg' hc]

theorem contains_of_lt (p : Addr) {k i : Nat} (hk : k ≤ 2 ^ 64) (hi : i < k) :
    (⟨p, k⟩ : Region).Contains (p + BitVec.ofNat 64 i) 1 :=
  Offset.contains_base _ (by omega) (by omega)

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- `Ctx` survives code that changes only the tail's registers, `out` and
`M`. -/
theorem Ctx.outM (hL : L.Ok) {t t' : State} (hc : Ctx L g vv m₀ t) (hk : Keep tailRegs t t')
    (hf : Frame [L.OUT, L.M] t.mem t'.mem) : Ctx L g vv m₀ t' := by
  have hnB := hL.nB
  have hk' := hL.khi
  refine ⟨hk.rd.trans hc.rd, hk.wr.trans hc.wr, hk.sp.trans hc.sp, fun r hr hr' => (hk.gpr r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans
      (hc.cs r hr hr'), fun r hr => by rw [hk.v]; exact hc.vs r hr, ?_,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · have hlr : L.LR.Contains (L.B + BitVec.ofNat 64 frameBytes) (64 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    rw [hf.readW hlr (fun R hR => ?_) (by decide)]
    · exact hc.lr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl
      · exact (hL.ko.sub_left (Offset.sub_base _ (by decide))).symm.symm
      · exact Offset.disjoint L.B (d := frameBytes) (n := 16) (e := oM) (k := L.k.toNat) (by
          simp only [frameBytes, oM]; omega) (by simp only [frameBytes]; omega) (by simp only [oM]; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, fun _ h => h⟩
    · exact ⟨L.STK, by simp, hL.M_sub⟩

/-- The comparison's registers. -/
theorem cmpArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem) {r1 r3 : BitVec 64}
    (h1 : t.mem.readW (L.B + BitVec.ofNat 64 oR1) 64 = r1) (h3 : t.mem.readW (L.B + BitVec.ofNat 64 oR3) 64 = r3) :
    WP isa (.block cmpArgs) t fun t' => t'.mem = t.mem ∧ Keep tailRegs t t' ∧
      t'.gpr .x9 = Proof.Rsa.gOf (t.gpr .x0) r1 r3 ∧ t'.gpr .x11 = L.out ∧ t'.gpr .x12 = L.inp ∧
      t'.gpr .x13 = L.k ∧ t'.gpr .x14 = 0 := by
  have l1 := hc.inFr hL (d := oR1) (n := 8) (by decide)
  have l3 := hc.inFr hL (d := oR3) (n := 8) (by decide)
  have lO := hc.inFr hL (d := oOut) (n := 8) (by decide)
  have lI := hc.inFr hL (d := oIn) (n := 8) (by decide)
  have lK := hc.inFr hL (d := oK) (n := 8) (by decide)
  apply WP.of_runBlock
  simp only [cmpArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write,
    RegUpd.sp_write, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.sp, l1, l3, lO, lI, lK, read8,
    h1, h3, hs.out, hs.inp, hs.k, Option.some.injEq, exists_eq_left', show oR1 % 8 = 0 by decide,
    show oR1 < 32768 by decide, show oR3 % 8 = 0 by decide, show oR3 < 32768 by decide,
    show oOut % 8 = 0 by decide, show oOut < 32768 by decide, show oIn % 8 = 0 by decide,
    show oIn < 32768 by decide, show oK % 8 = 0 by decide, show oK < 32768 by decide, and_self,
    Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero]
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl, trivial, trivial, trivial, rfl⟩
  simp only [tailRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨-, -, h9, h10, h11, h12, h13, h14, -⟩ := hr
  simp only [RegUpd.gpr_write, h9, h10, h11, h12, h13, h14, ite_false]

theorem tail_eq : seqs tail = .seq (.block cmpArgs) (.seq cmpLoop (.seq (.block masks)
    (.seq releaseLoop (.block [.addImm .x .x0 .x13 0])))) := rfl

/-- The check and the release, after the calls, from `t`: whatever `M`,
`out` and the values returned hold. -/
theorem tail_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (hs : Slots L t.mem) {r1 r3 : BitVec 64}
    (h1 : t.mem.readW (L.B + BitVec.ofNat 64 oR1) 64 = r1) (h3 : t.mem.readW (L.B + BitVec.ofNat 64 oR3) 64 = r3) :
    WP isa (seqs tail) t fun t' => Ctx L g vv m₀ t' ∧
      t'.gpr .x0 = Proof.Rsa.result (Proof.Rsa.gOf (t.gpr .x0) r1 r3)
        (decide (Spec.Rsa.bytesAt t.mem L.out L.k.toNat = Spec.Rsa.bytesAt t.mem L.inp L.k.toNat)) ∧
      Spec.Rsa.bytesAt t'.mem L.out L.k.toNat =
        (if Proof.Rsa.gOf (t.gpr .x0) r1 r3 = 1 ∧
            Spec.Rsa.bytesAt t.mem L.out L.k.toNat = Spec.Rsa.bytesAt t.mem L.inp L.k.toNat then
          Spec.Rsa.bytesAt t.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat
        else List.replicate L.k.toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (L.B + BitVec.ofNat 64 oM) L.k.toNat = List.replicate L.k.toNat 0 := by
  have hnB := hL.nB
  have hkk := hL.khi
  have hk1 : 1 ≤ L.k.toNat := by have := hL.klo; omega
  have hk64 : L.k.toNat < 2 ^ 63 := by omega
  have hok : L.out.toNat + L.k.toNat ≤ 2 ^ 64 := hL.olk ▸ hL.bo
  have hik : L.inp.toNat + L.k.toNat ≤ 2 ^ 64 := hL.ilk ▸ hL.bi
  have hOk : L.OUT = ⟨L.out, L.k.toNat⟩ := by rw [Lay.OUT, hL.olk]
  have hdisj : L.OUT.Disjoint L.M := (hL.ko.sub_left hL.M_sub).symm
  rw [tail_eq]
  refine WP.seq (WP.mono (cmpArgs_ok hL hc hs h1 h3) fun t₁ ⟨hm₁, k₁, x9, x11, x12, x13, x14⟩ => ?_)
  have hc₁ := hc.keep k₁ hm₁
  refine WP.seq (WP.mono (cmpLoop_ok (op := L.out) (ip := L.inp) hk1 hk64 x11 x12
    (by rw [x13, BitVec.ofNat_toNat, BitVec.setWidth_eq]) x14
    (fun i hi => ⟨L.OUT, by rw [hc₁.rd, hc₁.wr]; simp, hOk ▸ contains_of_lt _ (by omega) hi⟩)
    (fun i hi => ⟨L.IN, by rw [hc₁.rd, hc₁.wr]; simp, by rw [Lay.IN, hL.ilk]; exact contains_of_lt _ (by omega) hi⟩))
    fun t₂ hI => ?_)
  have hc₂ := hc₁.keep (Keep.trans ⟨fun r hr => (hI.keep.gpr r (by simp_all)), hI.keep.rd, hI.keep.wr,
    hI.keep.sp, hI.keep.v⟩ (Keep.refl _ _)) hI.mem
  have hs₂ : Slots L t₂.mem := by rw [hI.mem, hm₁]; exact hs
  have g9 : t₂.gpr .x9 = Proof.Rsa.gOf (t.gpr .x0) r1 r3 := (hI.keep.gpr _ (by decide)).trans x9
  have heq : t₂.gpr .x14 = 0 ↔
      decide (Spec.Rsa.bytesAt t.mem L.out L.k.toNat = Spec.Rsa.bytesAt t.mem L.inp L.k.toNat) = true := by
    rw [hI.x14, decide_eq_true_eq, Proof.Rsa.bytesAt_eq_iff, hm₁]
  refine WP.seq (WP.mono (masks_ok hL hc₂ hs₂ g9 (Proof.Rsa.gOf_cases _ _ _) heq)
    fun t₃ ⟨hm₃, k₃, y13, y12, y10, y11, y14, y15⟩ => ?_)
  have hc₃ := hc₂.keep k₃ hm₃
  have hMk : ∀ i < L.k.toNat, InRegions t₃.wr (L.B + BitVec.ofNat 64 oM + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨L.FR, by rw [hc₃.wr]; simp, by
      rw [add_add]; exact Offset.contains_base _ (by simp only [oM, frameBytes]; omega) (by simp only [oM]; omega)⟩
  refine WP.seq (WP.mono (releaseLoop_ok (op := L.out) (Mb := L.B + BitVec.ofNat 64 oM) hk1 hk64 y10 y12 y11 y14
    (by rw [y15, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun i hi i' hi' h => hdisj _ (by rw [hOk]; exact contains_of_lt _ (by omega) hi)
      (by rw [h]; exact contains_of_lt _ (by omega) hi'))
    (add_ofNat_inj _ (by omega)) (add_ofNat_inj _ (by omega))
    (fun i hi => ⟨L.OUT, by rw [hc₃.wr]; simp, hOk ▸ contains_of_lt _ (by omega) hi⟩) hMk)
    fun t₄ hR => ?_)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq,
    show (0 : Nat) < 4096 by decide, ite_true, Option.some.injEq, exists_eq_left', BitVec.add_zero]
  have z13 : t₄.gpr .x13 = Proof.Rsa.result (Proof.Rsa.gOf (t.gpr .x0) r1 r3)
      (decide (Spec.Rsa.bytesAt t.mem L.out L.k.toNat = Spec.Rsa.bytesAt t.mem L.inp L.k.toNat)) :=
    (hR.keep.gpr _ (by decide)).trans y13
  have m₃ : t₃.mem = t.mem := hm₃.trans (hI.mem.trans hm₁)
  have kk : Keep tailRegs t t₄ := ((k₁.trans (hI.keep.mono (by decide))).trans k₃).trans (hR.keep.mono (by decide))
  have hf : Frame [L.OUT, L.M] t.mem t₄.mem := fun x hx => by
    rw [hR.frame x (fun i hi h => hx L.OUT (by simp) (by rw [h, hOk]; exact contains_of_lt _ (by omega) hi))
      (fun i hi h => hx L.M (by simp) (by
        rw [h, add_add]
        exact Offset.contains _ (by omega) (by omega) (by simp only [oM]; omega))), m₃]
  refine ⟨Ctx.outM hL hc ⟨fun r hr => ?_, kk.rd, kk.wr, kk.sp, kk.v⟩ hf, ?_, ?_, ?_⟩
  · rw [RegUpd.gpr_write]
    split
    · rename_i h; subst h; simp at hr
    · exact kk.gpr r hr
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, z13]
  · simp only [RegUpd.mem_write]
    refine bytesAt_ext fun i hi => ?_
    rw [hR.out i hi, m₃]; simp only [decide_eq_true_eq]
  · simp only [RegUpd.mem_write, Spec.Rsa.bytesAt, List.eq_replicate_iff, List.length_map,
      List.length_range, List.mem_map, List.mem_range, true_and]
    rintro _ ⟨i, hi, rfl⟩
    exact hR.m i hi

end

end VG.Proof.Rsa.AArch64
