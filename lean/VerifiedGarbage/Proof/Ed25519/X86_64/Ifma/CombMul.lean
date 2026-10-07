import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLoop

/-!
# Ed25519's comb with AVX512_IFMA: the multiplication

`Ifma.combMultiply` leaves `[s]B` in slots 0–3, as `combMultiply` does: the
constants (`combConstOps`, then `vload`'s, which puts `[G]B` into the lanes),
the 64 steps (`vstep_ok`) with MXCSR `0x1FBF`, and the lanes back into slots
0–3 (`vstore`).
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519
  VG.Proof.Ed25519.X86_64 Edwards
open VG.Proof.X25519.X86_64.Ifma (lanes fe5 fe5_congr consts_wp cregs)
open VG.Proof.X25519.X86_64 (Outside F off clob)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

variable {fld : Arith} [EdArith fld]

theorem combConst_point (e : Env) : point (evalOps combConstOps e) 0 1 2 3 = combG := by
  show point (evalOps [.const 11 combGCached.Z] (evalOps [.const 10 combGCached.Y]
    (evalOps [.const 9 combGCached.X] (evalOps [.const 7 2] (evalOps (constPointOps combG) e))))) 0 1 2 3 = _
  rw [← constPoint_eval combG e]
  rfl

theorem combConst_slots (e : Env) : evalOps combConstOps e 7 = 2 ∧ evalOps combConstOps e 9 = combGCached.X ∧
    evalOps combConstOps e 10 = combGCached.Y ∧ evalOps combConstOps e 11 = combGCached.Z :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Before the loop: the constants, and `[G]B` in the lanes. -/
theorem vprep_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block (fieldCode fld combConstOps ++ VG.Impl.X25519.X86_64.Ifma.consts ++ vload)) s fun t =>
      t.gpr .rdi = base ∧ (∀ r, r ∉ clob → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      TableFrame base 56 7368 s.mem t.mem ∧ EConsts t.mem base ∧ Small t ∧ lanePt t = combG ∧
      F t.mem base K2 = 2 ∧ F t.mem base (offset 9) = combGCached.X ∧
      F t.mem base (offset 10) = combGCached.Y ∧ F t.mem base (offset 11) = combGCached.Z ∧
      (∀ q < 256, t.mem (off base (768 + q)) = s.mem (off base (768 + q))) := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (fld := fld) hs combConstOps) fun s₁ ⟨k₁, v₁⟩ => ?_
  have hs₁ := hs.of_keep k₁
  rw [WP.block_append_iff]
  refine WP.mono (consts_wp s₁) fun s₂ ⟨ha, hc, hd, hb, h8, h9, h10, _, _, g₂, m₂, rd₂, wr₂, _, _, _⟩ => ?_
  have hs₂ : Scratch s₂ base :=
    ⟨by rw [g₂ _ (by decide)]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hs₁.nowrap⟩
  refine WP.mono (vload_wp hs₂.rdi (ctx_of hs₂) ha hc hd hb h8 h9 h10) fun t ⟨g₃, rd₃, wr₃, o₃, k₃, u₃⟩ => ?_
  have fs : ∀ (i : Slot), i.val < 16 → F t.mem base (offset i) = evalOps combConstOps (env s.mem base) i :=
    fun i hi => by
      rw [Outside_F o₃ (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega)), m₂, ← v₁]
      rfl
  refine ⟨by rw [g₃]; exact hs₂.rdi, fun r hr => by
      rw [g₃, g₂ r (fun h => hr (VG.Proof.Ed25519.X86_64.Ifma.cregs_clob r h)), k₁.gpr r hr],
    by rw [rd₃, rd₂, k₁.rd], by rw [wr₃, wr₂, k₁.wr], ?_, k₃,
    fun l hl i hi => by have := (u₃ l hl i hi).2; omega, ?_,
    by rw [show K2 = offset 7 from rfl, fs 7 (by decide)]; exact (combConst_slots _).1,
    by rw [fs 9 (by decide)]; exact (combConst_slots _).2.1,
    by rw [fs 10 (by decide)]; exact (combConst_slots _).2.2.1,
    by rw [fs 11 (by decide)]; exact (combConst_slots _).2.2.2, fun q hq => ?_⟩
  · rw [m₂] at o₃
    exact (TableFrame.workspace k₁.mem).trans ((TableFrame.table o₃).mono (by decide) (by decide))
  · have e : ∀ l (hl : l < 4), fe5 (lanes t 0 l) = env s₁.mem base ⟨l, by omega⟩ := fun l hl => by
      rw [fe5_congr (fun i hi => (u₃ l hl i hi).1), fe5_load, m₂]; rfl
    simp only [lanePt]
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), ← combConst_point (env s.mem base),
      ← v₁]
    rfl
  · rw [o₃ _ (Or.inl (by rw [bits_far hq]; omega)), m₂, k₁.mem _ (Or.inr (by rw [bits_far hq]; omega))]

/-- `Ifma.combMultiply`: `[s]B` into slots 0–3, for the scalar bits expanded into bytes 768
onward, as `combMultiply_ok`. -/
theorem vcomb_ok {s : State} {base T : Addr} (hs : Scratch s base) {S : Nat}
    (hS : S < 2 ^ (16 * 16)) (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (ht : CombTbl s T) (hfar : TblFar base T) :
    WP isa (Impl.Ed25519.X86_64.Ifma.combMultiply fld) s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ PowersKeep base 56 7368 s t := by
  rw [Impl.Ed25519.X86_64.Ifma.combMultiply, withMx]
  refine WP.seq (WP.mono_syms (vprep_ok (fld := fld) hs)
    fun s₁ ⟨r₁, g₁, rd₁, wr₁, m₁, k₁, sm₁, p₁, k2₁, ga₁, gb₁, gc₁, b₁⟩ sy₁ => ?_)
  have hs₁ : Scratch s₁ base := ⟨r₁, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono_syms (save_wp hs₁) fun s₂ ⟨g₂, r11₂, k₂⟩ sy₂ => ?_)
  have hs₂ : Scratch s₂ base := ⟨by rw [g₂ _ (by decide)]; exact r₁, by rw [k₂.wr]; exact hs₁.wr, hs.nowrap⟩
  refine WP.seq (WP.seq (WP.mono_syms (load_wp hs₂) fun s₃ ⟨g₃, k₃⟩ sy₃ => ?_))
  have hs₃ : Scratch s₃ base := ⟨by rw [g₃ _ (by decide)]; exact hs₂.rdi, by rw [k₃.wr]; exact hs₂.wr, hs.nowrap⟩
  have q₃ : ∀ x l, qw s₃ x l = qw s₁ x l := fun x l => by rw [k₃.qw_eq, k₂.qw_eq]
  have o₃ : Outside base EMX 8 s₁.mem s₃.mem := k₂.mem.trans k₃.mem
  have hp : LoopPre s₃ base T S :=
    { scratch := hs₃
      consts := (k₁.outsideMx k₂.mem).outsideMx k₃.mem
      k2 := by rw [Outside_F o₃ (by decide) (Or.inl (by decide))]; exact k2₁
      g0 := by rw [Outside_F o₃ (by decide) (Or.inl (by decide))]; exact ga₁
      g1 := by rw [Outside_F o₃ (by decide) (Or.inl (by decide))]; exact gb₁
      g2 := by rw [Outside_F o₃ (by decide) (Or.inl (by decide))]; exact gc₁
      bits := fun q hq => by
        rw [o₃ _ (Or.inl (by rw [bits_far hq]; simp only [EMX]; omega)), b₁ q hq]; exact hb q hq
      tbl := ht.keep hfar ((⟨fun r _ _ hr => g₁ r hr, rd₁, wr₁, m₁⟩ : PowersKeep base 56 7368 s s₁).trans
        ⟨fun r _ _ hr => by rw [g₃ r (fun e => hr (e ▸ by decide)), g₂ r (fun e => hr (e ▸ by decide))],
          by rw [k₃.rd, k₂.rd], by rw [k₃.wr, k₂.wr], (TableFrame.table o₃).mono (by decide) (by decide)⟩)
        (by rw [sy₃, sy₂, sy₁])
      far := hfar }
  refine WP.seq (WP.seq (WP.mono_syms (mov32_wp s₃ .rbx 0) fun s₄ ⟨r₄, g₄, m₄, rd₄, wr₄, q₄⟩ sy₄ => ?_))
  have i₄ : VInv s₃ base 0 (combVal S 0) s₄ := by
    refine ⟨by decide, by rw [g₄ _ (by decide)]; exact hs₃.rdi, by rw [r₄]; rfl,
      VFrame.refl s₃ base |>.step (rs := [.rbx]) (by decide) (fun r hr => g₄ r (by simpa using hr)) rd₄ wr₄
        (by rw [m₄]; exact Outside.refl _ _ _ _) sy₄,
      fun l hl i hi => by rw [lanes_qw q₄, lanes_qw q₃]; exact sm₁ l hl i hi, ?_⟩
    rw [lanePt_qw q₄, lanePt_qw q₃, p₁, show combVal S 0 = (combGVal : ℤ) by simp [combVal, oddSumZ],
      natCast_zsmul]
    exact combG_ok
  have fin : ∀ w, VInv s₃ base 52 (combVal S 52) w → WP isa (.block vstore) w fun y =>
      WP isa (.block [.lfence]) y fun z =>
        WP isa (.block [.store32 (Impl.X25519.X86_64.sc EMX) .r11, .ldmxcsr (Impl.X25519.X86_64.sc EMX)]) z
          fun t => Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ PowersKeep base 56 7368 s t := by
    intro w hw
    rw [comb_sum hS] at hw
    have hsw : Scratch w base := hw.frame.scratch hp hw.rdi
    refine WP.mono (vstore_wp hw.rdi (ctx_of hsw) (hw.frame.consts hp) hw.small)
      fun t₀ ⟨tg, trd, twr, tou, tf⟩ => ?_
    refine WP.mono (lfence_wp t₀) fun t₁ e₁ => ?_
    subst e₁
    have hs₀ : Scratch t₁ base := ⟨by rw [tg]; exact hw.rdi, by rw [twr]; exact hsw.wr, hs.nowrap⟩
    have r11 : t₁.gpr .r11 = s₂.gpr .r11 := by rw [tg, hw.frame.r11, g₃ _ (by decide)]
    refine WP.mono (restore_wp hs₀ (by rw [r11, r11₂]; exact and_ffff _)) fun t ⟨g₈, k₈⟩ => ?_
    have pt : point (env t.mem base) 0 1 2 3 = lanePt w := by
      simp only [point, lanePt, env, VG.Impl.Ed25519.X86_64.offset]
      rw [← tf 0 (by decide), ← tf 1 (by decide), ← tf 2 (by decide), ← tf 3 (by decide),
        Outside_F k₈.mem (by decide) (Or.inl (by decide)), Outside_F k₈.mem (by decide) (Or.inl (by decide)),
        Outside_F k₈.mem (by decide) (Or.inl (by decide)), Outside_F k₈.mem (by decide) (Or.inl (by decide))]
      rfl
    refine ⟨by rw [pt, ← natCast_zsmul]; exact hw.value, ?_⟩
    refine (⟨fun r _ _ hr => g₁ r hr, rd₁, wr₁, m₁⟩ : PowersKeep base 56 7368 s s₁).trans ?_
    refine ⟨fun r h1 h2 hr => ?_, by rw [k₈.rd, trd, hw.frame.rd, k₃.rd, k₂.rd],
      by rw [k₈.wr, twr, hw.frame.wr, k₃.wr, k₂.wr], ?_⟩
    · rw [g₈, tg, hw.frame.gpr r h1 h2 hr, g₃ r (fun e => hr (e ▸ by decide)), g₂ r (fun e => hr (e ▸ by decide))]
    · exact ((TableFrame.table o₃).mono (by decide) (by decide)).trans
        (((TableFrame.table hw.frame.mem).mono (by decide) (by decide)).trans
          (((TableFrame.table tou).mono (by decide) (by decide)).trans
            ((TableFrame.table k₈.mem).mono (by decide) (by decide))))
  refine WP.seq ?_
  apply WP.loop (fun n t => VInv s₃ base (52 - n) (combVal S (52 - n)) t ∧ 0 < n ∧ n ≤ 52) (n := 52)
  · intro n t ⟨ht', hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono (vstep_ok hp hS ht' (by omega)) fun u ⟨uz, hu⟩ => ?_
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨by simp only [eval, uz, show 52 - (0 + 1) + 1 = 52 from rfl, decide_true,
        Option.map_some, Bool.not_true], fin u hu⟩
    · refine Or.inr ⟨by simp only [eval, uz, show ¬ (52 - (k + 1) + 1 = 52) by omega, decide_false,
        Option.map_some, Bool.not_false], k, by omega, ?_, by omega, by omega⟩
      rw [show 52 - k = 52 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨i₄, by decide, by decide⟩

end VG.Proof.Ed25519.X86_64.Ifma
