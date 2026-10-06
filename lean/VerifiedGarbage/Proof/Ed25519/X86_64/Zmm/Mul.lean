import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Tail
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombMul

/-!
# The `zmm` comb: the multiplication

`Zmm.combMultiply` leaves `[s]B` in slots 0–3, as `combMultiply` does: the
constants (`zConstOps`, `vload`'s, and the rows of the `zmm` code, `zconsts`,
which also puts `[G]B` into both halves of the lanes), the 26 steps
(`zstep_ok`) with MXCSR `0x1FBF`, and `32 A + B` (`ztail_ok`).
-/

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Zmm VG.Proof.Ed25519.X86_64.Ifma
  VG.Proof.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Impl.Ed25519.X86_64.Ifma (EMX withMx vload)
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr consts_wp cregs mq)
open VG.Proof.X25519.X86_64 (Outside F off ofs clob)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

variable {fld : Arith} [EdArith fld]

/-! ## Frames -/

theorem outside_readW {m m' : Mem} {b : Addr} {o n : Nat} (h : Outside b o n m m') {d w : Nat}
    (hd : d + w / 8 ≤ o ∨ o + n ≤ d) (hd' : d + w / 8 < 2 ^ 64) :
    m'.readW (b + BitVec.ofNat 64 d) w = m.readW (b + BitVec.ofNat 64 d) w :=
  Mem.readW_congr fun i hi => by
    rw [Offset.add_ofNat_add_ofNat]
    exact h _ (by simp only [ofs]; rw [off_ofNat _ (by omega)]; omega)

/-- The halves see no change at `EMX`, which is in the window. -/
theorem hmem_mx {b : Addr} {m m' : Mem} (h : Outside b EMX 8 m m') {h' : Nat}
    (hh : h' < 2) : hmem b h' m' = hmem b h' m := by
  funext a
  simp only [hmem]
  split
  · rename_i hw
    simp only [InWin] at hw
    exact h _ (by
      simp only [ofs]; rw [off_ofNat _ (by unfold zoff ZB; have := (a - b).isLt; omega)]
      unfold zoff ZB EMX; omega)
  · rename_i hw
    simp only [InWin] at hw
    exact h _ (by simp only [ofs]; unfold EMX; omega)

theorem ZFrame.outside {s₀ s : State} {b : Addr} (h : ZFrame s₀ b s) : Outside b 1152 5424 s₀.mem s.mem :=
  fun a ha => h.mem a (by unfold ZChg InZ DigOff SGA SGB combSignMask ZMASK ZB; omega)

theorem half_lanes {s t : State} (b : Addr) (hz : ∀ r i, i < 4 → t.zlane r i = s.zlane r i) {h : Nat}
    (hh : h < 2) (r l i : Nat) (hl : l < 4) : lanes (Zmm.half b h t) r l i = lanes (Zmm.half b h s) r l i := by
  simp only [lanes]; rw [qw_half b t _ hl, qw_half b s _ hl]; simp only [zq]; rw [hz _ _ (by omega)]

/-! ## Before the loop -/

theorem zConst_env (e : Env) : point (evalOps zConstOps e) 0 1 2 3 = combG ∧
    evalOps zConstOps e 12 = 1 ∧ evalOps zConstOps e 13 = 1 ∧
    evalOps zConstOps e 14 = Spec.Ed25519.d + Spec.Ed25519.d ∧ evalOps zConstOps e 15 = 2 := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  rw [← constPoint_eval combG e]
  rfl

/-- The constants, the rows of the `zmm` code, and `[G]B` in both halves. -/
theorem zprep_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (fieldCode fld zConstOps ++ VG.Impl.X25519.X86_64.Ifma.consts ++ vload ++ zconsts)) s
      fun t => Scratch t base ∧ (∀ r, r ∉ clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      TableFrame base 56 7368 s.mem t.mem ∧ EConsts t.mem base ∧ ZOK base t ∧
      (∀ h < 2, EConsts (Zmm.half base h t).mem base) ∧ (∀ h < 2, Small (Zmm.half base h t)) ∧
      (∀ h < 2, lanePt (Zmm.half base h t) = combG) ∧ (∀ h < 2, F t.mem base (ZK2 + 32 * h) = 2) ∧
      F t.mem base (offset 12) = 1 ∧ F t.mem base (offset 13) = 1 ∧
      F t.mem base (offset 14) = Spec.Ed25519.d + Spec.Ed25519.d ∧ F t.mem base (offset 15) = 2 ∧
      (∀ q < 256, t.mem (off base (768 + q)) = s.mem (off base (768 + q))) := by
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (fld := fld) hs zConstOps) fun s₁ ⟨k₁, v₁⟩ => ?_
  have hs₁ := hs.of_keep k₁
  rw [WP.block_append_iff]
  refine WP.mono (consts_wp s₁) fun s₂ ⟨ha, hc, hd, hb, h8, h9, h10, _, _, g₂, m₂, rd₂, wr₂, _, _, _⟩ => ?_
  have hs₂ : Scratch s₂ base :=
    ⟨by rw [g₂ _ (by decide)]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hs₁.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (vload_wp hs₂.rdi (ctx_of hs₂) ha hc hd hb h8 h9 h10) fun s₃ ⟨g₃, rd₃, wr₃, o₃, k₃, u₃⟩ => ?_
  have hs₃ : Scratch s₃ base := ⟨by rw [g₃]; exact hs₂.rdi, by rw [wr₃]; exact hs₂.wr, hs.nowrap⟩
  refine WP.mono (zconsts_ok hs₃ k₃) fun t ⟨hk, mk, k2, ft, qt, gt, rdt, wrt, _⟩ => ?_
  have ot : Outside base ZB 1856 s₃.mem t.mem := fun a ha => ft a (by unfold ZB at *; omega)
  have fs₃ : ∀ (i : Slot), i.val < 16 → F s₃.mem base (offset i) = evalOps zConstOps (env s.mem base) i :=
    fun i hi => by
      rw [Outside_F o₃ (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)), m₂, ← v₁]
      rfl
  have fs : ∀ (i : Slot), i.val < 16 → F t.mem base (offset i) = evalOps zConstOps (env s.mem base) i :=
    fun i hi => by
      rw [Outside_F ot (by simp only [offset]; omega) (Or.inl (by simp only [offset, ZB]; omega)), fs₃ i hi]
  have lt : ∀ h < 2, ∀ l < 4, ∀ i < 5, lanes (Zmm.half base h t) 0 l i = lanes s₃ 0 l i :=
    fun h hh l hl i hi => by simp only [lanes, Nat.zero_add]; rw [qt h hh i hi l hl]
  have pt : lanePt s₃ = combG := by
    have e : ∀ l (hl : l < 4), fe5 (lanes s₃ 0 l) = env s₁.mem base ⟨l, by omega⟩ := fun l hl => by
      rw [fe5_congr (fun i hi => (u₃ l hl i hi).1), fe5_load, m₂]; rfl
    simp only [lanePt]
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide),
      ← (zConst_env (env s.mem base)).1, ← v₁]
    rfl
  have cz := zConst_env (env s.mem base)
  refine ⟨⟨by rw [gt]; exact hs₃.rdi, by rw [wrt]; exact hs₃.wr, hs.nowrap⟩, fun r hr => ?_,
    by rw [rdt, rd₃, rd₂, k₁.rd], by rw [wrt, wr₃, wr₂, k₁.wr], ?_,
    k₃.of_mq fun d _ h2 => outside_mq ot (Or.inl (by unfold ZB; omega)) (by omega),
    ⟨by rw [gt]; exact hs₃.rdi, by rw [wrt]; exact hs₃.wr, hs.nowrap, mk⟩, hk,
    fun h hh l hl i hi => by rw [lt h hh l hl i hi]; have := (u₃ l hl i hi).2; omega,
    fun h hh => by rw [lanePt_eq_of (lt h hh)]; exact pt,
    fun h hh => by rw [k2 h hh, fs₃ 15 (by decide)]; exact cz.2.2.2.2,
    by rw [fs 12 (by decide)]; exact cz.2.1, by rw [fs 13 (by decide)]; exact cz.2.2.1,
    by rw [fs 14 (by decide)]; exact cz.2.2.2.1, by rw [fs 15 (by decide)]; exact cz.2.2.2.2, fun q hq => ?_⟩
  · rw [gt, g₃, g₂ r (fun h => hr (VG.Proof.Ed25519.X86_64.Ifma.cregs_clob r h)), k₁.gpr r hr]
  · rw [m₂] at o₃
    exact (TableFrame.workspace k₁.mem).trans (((TableFrame.table o₃).mono (by decide) (by decide)).trans
      ((TableFrame.table ot).mono (by decide) (by decide)))
  · rw [ot _ (Or.inl (by rw [bits_far hq]; unfold ZB; omega)), o₃ _ (Or.inl (by rw [bits_far hq]; omega)), m₂,
      k₁.mem _ (Or.inr (by rw [bits_far hq]; omega))]

/-! ## The multiplication -/

/-- `A`'s value after `c` steps: `[G]B` plus the odd digits'. -/
def zvA (S c : Nat) : ℤ := (VG.Proof.Ed25519.X86_64.combGVal : ℤ) + VG.Proof.Ed25519.X86_64.oddSumZ S c

/-- `B`'s value after `c` steps: `[G]B` plus the even digits'. -/
def zvB (S c : Nat) : ℤ := (VG.Proof.Ed25519.X86_64.combGVal : ℤ) + VG.Proof.Ed25519.X86_64.evenSumZ S c

theorem zvA_succ (S j : Nat) :
    zvA S (j + 1) = VG.Proof.Ed25519.X86_64.sdig S (2 * j + 1) * 1024 ^ j + zvA S j := by
  simp only [zvA, VG.Proof.Ed25519.X86_64.oddSumZ]
  rw [Int.add_comm _ ((VG.Proof.Ed25519.X86_64.combGVal : ℤ) + _), Int.add_assoc]

theorem zvB_succ (S j : Nat) :
    zvB S (j + 1) = VG.Proof.Ed25519.X86_64.sdig S (2 * j) * 1024 ^ j + zvB S j := by
  simp only [zvB, VG.Proof.Ed25519.X86_64.evenSumZ]
  rw [Int.add_comm _ ((VG.Proof.Ed25519.X86_64.combGVal : ℤ) + _), Int.add_assoc]

theorem zv_sum {S : Nat} (hS : S < 2 ^ 256) : ((32 : Nat) : ℤ) * zvA S 26 + zvB S 26 = S := by
  rw [← VG.Proof.Ed25519.X86_64.comb_sum hS]
  simp only [zvA, zvB, VG.Proof.Ed25519.X86_64.combVal, show ¬ 52 ≤ 26 by decide, ↓reduceIte,
    show 52 - 26 = 26 from rfl, Nat.cast_ofNat]
  rw [Int.add_assoc]

/-- `Zmm.combMultiply`: `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768
onward, as `vcomb_ok`. -/
theorem zcomb_ok {s : State} {base T : Addr} (hs : Scratch s base) {S : Nat}
    (hS : S < 2 ^ (16 * 16)) (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (ht : CombTbl s T) (hfar : TblFar base T) :
    WP isa (Zmm.combMultiply fld) s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ PowersKeep base 56 7368 s t := by
  rw [Zmm.combMultiply, withMx]
  refine WP.seq (WP.mono_syms (zprep_ok (fld := fld) hs)
    fun s₁ ⟨hs₁, g₁, rd₁, wr₁, m₁, k₁, z₁, hk₁, sm₁, p₁, k2₁, f12, f13, f14, f15, b₁⟩ sy₁ => ?_)
  refine WP.seq (WP.mono_syms (save_wp hs₁) fun s₂ ⟨g₂, r11₂, k₂⟩ sy₂ => ?_)
  have hs₂ : Scratch s₂ base := ⟨by rw [g₂ _ (by decide)]; exact hs₁.rdi, by rw [k₂.wr]; exact hs₁.wr, hs.nowrap⟩
  refine WP.seq (WP.seq (WP.mono_syms (load_wp hs₂) fun s₃ ⟨g₃, k₃⟩ sy₃ => ?_))
  have hs₃ : Scratch s₃ base := ⟨by rw [g₃ _ (by decide)]; exact hs₂.rdi, by rw [k₃.wr]; exact hs₂.wr, hs.nowrap⟩
  have o₃ : Outside base EMX 8 s₁.mem s₃.mem := k₂.mem.trans k₃.mem
  have zl₃ : ∀ r i, i < 4 → s₃.zlane r i = s₁.zlane r i := fun r i _ => by
    rw [zlane_of k₃.xmm k₃.ymm k₃.zmm, zlane_of k₂.xmm k₂.ymm k₂.zmm]
  have keep₃ : PowersKeep base 56 7368 s s₃ :=
    (⟨fun r _ _ hr => g₁ r hr, rd₁, wr₁, m₁⟩ : PowersKeep base 56 7368 s s₁).trans
      ⟨fun r _ _ hr => by rw [g₃ r (fun e => hr (e ▸ by decide)), g₂ r (fun e => hr (e ▸ by decide))],
        by rw [k₃.rd, k₂.rd], by rw [k₃.wr, k₂.wr], (TableFrame.table o₃).mono (by decide) (by decide)⟩
  have hmr : ∀ sel ∈ blendSels, ZMASK ≤ maskRow sel ∧ maskRow sel + 64 ≤ 6016 := by decide
  have hp : ZLoopPre s₃ base T S :=
    { scratch := hs₃
      zok := ⟨hs₃.rdi, hs₃.wr, hs.nowrap, fun sel hsel i hi => by
        have := hmr sel hsel
        rw [outside_readW o₃ (Or.inr (by unfold ZMASK EMX at *; omega)) (by omega)]
        exact z₁.masks sel hsel i hi⟩
      hconsts := fun h hh => by
        show EConsts (hmem base h s₃.mem) base
        rw [hmem_mx o₃ hh]; exact hk₁ h hh
      consts := (k₁.outsideMx k₂.mem).outsideMx k₃.mem
      k2 := fun h hh => by
        rw [Outside_F o₃ (by unfold ZK2; omega) (Or.inr (by unfold ZK2 EMX; omega))]; exact k2₁ h hh
      bits := fun q hq => by
        rw [o₃ _ (Or.inl (by rw [bits_far hq]; simp only [EMX]; omega)), b₁ q hq]; exact hb q hq
      tbl := ht.keep hfar keep₃ (by rw [sy₃, sy₂, sy₁])
      far := hfar }
  refine WP.seq (WP.seq (WP.mono_syms (zscal rfl (mov32_wp s₃ .rbx 0))
    fun s₄ ⟨⟨r₄, g₄, m₄, rd₄, wr₄, _⟩, zl₄⟩ sy₄ => ?_))
  have zl : ∀ r i, i < 4 → s₄.zlane r i = s₁.zlane r i := fun r i hi => by rw [zl₄, zl₃ r i hi]
  have i₄ : ZInv s₃ base 0 (zvA S 0) (zvB S 0) s₄ := by
    have g0 : Rep combG ((zvA S 0) • baseAff) := by
      rw [show zvA S 0 = (VG.Proof.Ed25519.X86_64.combGVal : ℤ) by simp [zvA, VG.Proof.Ed25519.X86_64.oddSumZ],
        natCast_zsmul]
      exact VG.Proof.Ed25519.X86_64.combG_ok
    refine ⟨by decide, by rw [g₄ _ (by decide)]; exact hs₃.rdi, by rw [r₄]; rfl,
      ⟨fun r h1 _ _ => g₄ r h1, g₄ _ (by decide), rd₄, wr₄, fun a _ => by rw [m₄], sy₄⟩,
      fun h hh => by show EConsts (hmem base h s₄.mem) base; rw [m₄]; exact hp.hconsts h hh,
      fun h hh l hl i hi => by rw [half_lanes base zl hh 0 l i hl]; exact sm₁ h hh l hl i hi, ?_, ?_⟩
    · rw [lanePt_eq_of (fun l hl i hi => half_lanes base zl (by decide) 0 l i hl), p₁ 0 (by decide)]
      exact g0
    · rw [lanePt_eq_of (fun l hl i hi => half_lanes base zl (by decide) 0 l i hl), p₁ 1 (by decide),
        show zvB S 0 = zvA S 0 by simp [zvA, zvB, VG.Proof.Ed25519.X86_64.oddSumZ,
          VG.Proof.Ed25519.X86_64.evenSumZ]]
      exact g0
  have fin : ∀ w, ZInv s₃ base 26 (zvA S 26) (zvB S 26) w →
      WP isa (.seq (.block ztail1) (.seq Impl.Ed25519.X86_64.Ifma.vdbl5
        (.block (ztail2 ++ Impl.Ed25519.X86_64.Ifma.vstore)))) w fun y =>
      WP isa (.block [.lfence]) y fun z =>
        WP isa (.block [.store32 (VG.Impl.X25519.X86_64.sc EMX) .r11, .ldmxcsr (VG.Impl.X25519.X86_64.sc EMX)]) z
          fun t => Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ PowersKeep base 56 7368 s t := by
    intro w hw
    have hsw : Scratch w base := hw.frame.scratch hp hw.rdi
    have ow := hw.frame.outside
    have fw : ∀ (i : Slot), 12 ≤ i.val → i.val < 16 → F w.mem base (offset i) = F s₁.mem base (offset i) :=
      fun i h1 h2 => by
        rw [Outside_F ow (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)),
          Outside_F o₃ (by simp only [offset]; omega) (Or.inl (by simp only [offset, EMX]; omega))]
    refine WP.mono (ztail_ok hsw (hw.frame.consts hp) (hw.small 0 (by decide)) (hw.small 1 (by decide))
      hw.valA hw.valB (by rw [fw 12 (by decide) (by decide)]; exact f12)
      (by rw [fw 13 (by decide) (by decide)]; exact f13) (by rw [fw 14 (by decide) (by decide)]; exact f14)
      (by rw [fw 15 (by decide) (by decide)]; exact f15)) fun y ⟨yg, yrd, ywr, yo, yp⟩ => ?_
    refine WP.mono (lfence_wp y) fun z₀ e₀ => ?_
    subst e₀
    have hs₀ : Scratch z₀ base := ⟨by rw [yg _ (by decide)]; exact hw.rdi, by rw [ywr]; exact hsw.wr, hs.nowrap⟩
    have r11 : z₀.gpr .r11 = s₂.gpr .r11 := by rw [yg _ (by decide), hw.frame.r11, g₃ _ (by decide)]
    refine WP.mono (restore_wp hs₀ (by rw [r11, r11₂]; exact and_ffff _)) fun t ⟨g₈, k₈⟩ => ?_
    have pt : point (env t.mem base) 0 1 2 3 = point (env z₀.mem base) 0 1 2 3 := by
      simp only [point, env, VG.Impl.Ed25519.X86_64.offset]
      rw [Outside_F k₈.mem (by decide) (Or.inl (by decide)), Outside_F k₈.mem (by decide) (Or.inl (by decide)),
        Outside_F k₈.mem (by decide) (Or.inl (by decide)), Outside_F k₈.mem (by decide) (Or.inl (by decide))]
    refine ⟨?_, keep₃.trans (hw.frame.keep.trans ⟨fun r _ h2 _ => by rw [g₈, yg r h2], by rw [k₈.rd, yrd],
      by rw [k₈.wr, ywr], ((TableFrame.table yo).mono (by decide) (by decide)).trans
        ((TableFrame.table k₈.mem).mono (by decide) (by decide))⟩)⟩
    rw [pt]
    rw [← natCast_zsmul, smul_smul, ← add_smul, zv_sum hS, natCast_zsmul] at yp
    exact yp
  refine WP.seq ?_
  apply WP.loop (fun n t => ZInv s₃ base (26 - n) (zvA S (26 - n)) (zvB S (26 - n)) t ∧ 0 < n ∧ n ≤ 26) (n := 26)
  · intro n t ⟨ht', hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono (zstep_ok hp hS ht' (by omega)) fun u ⟨uz, hu⟩ => ?_
    rw [← zvA_succ, ← zvB_succ] at hu
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨by simp only [eval, uz, show 26 - (0 + 1) + 1 = 26 from rfl, decide_true,
        Option.map_some, Bool.not_true], fin u hu⟩
    · refine Or.inr ⟨by simp only [eval, uz, show ¬ (26 - (k + 1) + 1 = 26) by omega, decide_false,
        Option.map_some, Bool.not_false], k, by omega, ?_, by omega, by omega⟩
      rw [show 26 - k = 26 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨i₄, by decide, by decide⟩

end VG.Proof.Ed25519.X86_64.Zmm
