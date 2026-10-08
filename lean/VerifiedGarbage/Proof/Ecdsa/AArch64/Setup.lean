import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen

/-!
# ECDSA on AArch64: the setup

`Cfg.setupWith hs` saves `x19`–`x25` at the start of the working space
(`setupSaves_ok`), keeps `out` in `x20` and moves the working space's base
to `x0` (`setupMovs_ok`), reads `k`, `d` and the hash (`len` bytes each)
big-endian into their slots (`setupLoad_ok`, once each), shifts the slot
`hs` holding a hash (`setupShift_ok`), stores the constants
(`setupConsts_ok`, by induction on the list) and sets the flag to all ones:
`setup_ok`, the state `SetupPost` describes.
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (read_x)
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

/-! ## Saving the callee-saved registers -/

theorem setupSaved_lt : ∀ rd ∈ Cfg.saved, rd.2 + 8 ≤ 64 := by decide

theorem setupSaves_ok {s : State} {base : Addr} (hb : s.gpr .x4 = base)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) :
    WP isa (.block (Spill.saveCode .x4 Cfg.saved)) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Outside base 0 64 s.mem s'.mem ∧
      Spill.Saved base s.gpr Cfg.saved s'.mem := by
  refine WP.mono (Spill.save_wp (by decide) fun p hp => ?_) fun s' h => ⟨h.gpr, h.rd, h.wr, h.sp, ?_, ?_⟩
  · have := setupSaved_lt p hp
    have hsz : size = 8192 := rfl
    rw [hb]; exact ⟨_, hw, Offset.contains_base base (by omega) (by omega)⟩
  · rw [h.mem, hb]
    intro x hx
    refine Spill.saveMem_frame_base setupSaved_lt (by decide) _ _ _ x fun r hr hx' => ?_
    rw [List.mem_singleton.mp hr] at hx'
    simp only [Region.Contains, ofs] at hx hx'
    omega
  · rw [h.mem, hb]; exact Spill.saveMem_saved (by decide) _ _ _

/-! ## `out` to `x20`, the working space to `x0` -/

theorem setupMovs_ok (s : State) :
    WP isa (.block ([.addImm .x .x20 .x0 0, .addImm .x .x0 .x4 0] : List Instr)) s fun s' =>
      s'.gpr .x20 = s.gpr .x0 ∧ s'.gpr .x0 = s.gpr .x4 ∧ KeepRegs [.x0, .x20] s s' ∧
      s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, show (0 : Nat) < 4096 by decide,
    ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero, reduceCtorEq, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-! ## Reading `k`, `d` and the hash -/

/-- The `len` bytes at `p` (readable, outside the working space, and so
unchanged since `s`) to slot `i`. -/
theorem setupLoad_ok {c : Cfg} (hc : BaseCfgOk c) {s t : State} {base p : Addr} {src : Reg} {i : Nat}
    (hs : Scr t base size) (hsrc : src ≠ .x5) (hsrc' : src ≠ .x17) (hi : i < 45) (hp : t.gpr src = p)
    (hin : ∀ e, e + 8 ≤ c.C.len → InRegions (t.rd ++ t.wr) (p + BitVec.ofNat 64 e) 8)
    (hd : Region.Disjoint ⟨p, c.C.len⟩ ⟨base, size⟩) (ho : Outside base 0 size s.mem t.mem) :
    WP isa (.block (loadBytes c.C.len c.n (c.sl i) src)) t fun t' =>
      wordsVal t'.mem base (c.sl i) c.n = ofBytes (Spec.Ecdsa.bytesAt s.mem p c.C.len) ∧
      KeepRegs [.x5, .x17] t t' ∧ Outside base (c.sl i) (8 * c.n) t.mem t'.mem := by
  have hl := sl_le c hc.n10 hi
  have h7 := hc.n10
  have := hc.len_hi
  have hsz : size = 8192 := rfl
  refine WP.mono (loadBytes_ok hs hsrc hsrc' hl (sl_mod8 c i) hc.len8 hc.len_lo hc.len_hi (by omega)
    (by rw [hp]; exact hin) (by rw [hp]; exact hd.sub_right (Offset.sub_base base hl)))
    fun t' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  have hb : Spec.Ecdsa.bytesAt t.mem p c.C.len = Spec.Ecdsa.bytesAt s.mem p c.C.len :=
    List.map_congr_left fun j hj =>
      keep_of_disjoint' ho hd (by decide) (List.mem_range.mp hj) (by omega)
  rw [e, hp, hb]

/-! ## The hash's shift -/

/-- The shift of slot `hs`, if any, by the bits of a hash that are not
`e`'s: only the slots of `k`, `d` and the hash change. -/
theorem setupShift_ok {c : Cfg} (hc : BaseCfgOk c) {hs : Option Nat} (hhs : ShiftOk hs) {t : State}
    {base : Addr} (hs' : Scr t base size) :
    WP isa (.block (c.shiftCode hs)) t fun t' =>
      wordsVal t'.mem base (c.sl K) c.n = wordsVal t.mem base (c.sl K) c.n >>> shAt c hs K ∧
      wordsVal t'.mem base (c.sl D) c.n = wordsVal t.mem base (c.sl D) c.n >>> shAt c hs D ∧
      wordsVal t'.mem base (c.sl E) c.n = wordsVal t.mem base (c.sl E) c.n >>> shAt c hs E ∧
      KeepRegs [.x1, .x2] t t' ∧ Outside base (c.sl K) (24 * c.n) t.mem t'.mem := by
  have hn := hs'.nowrap
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have hKl := sl_le c h7 (i := K) (by decide)
  have hDl := sl_le c h7 (i := D) (by decide)
  have hEl := sl_le c h7 (i := E) (by decide)
  have hKD : c.sl D = c.sl K + 8 * c.n := by simp (disch := decide) only [sl_eq]; show _ = _ + 8 * c.n; simp only [D, K]; omega
  have hKE : c.sl E = c.sl K + 16 * c.n := by simp (disch := decide) only [sl_eq]; show _ = _ + 16 * c.n; simp only [E, K]; omega
  have nil : WP isa (.block ([] : List Instr)) t fun t' =>
      wordsVal t'.mem base (c.sl K) c.n = wordsVal t.mem base (c.sl K) c.n >>> 0 ∧
      wordsVal t'.mem base (c.sl D) c.n = wordsVal t.mem base (c.sl D) c.n >>> 0 ∧
      wordsVal t'.mem base (c.sl E) c.n = wordsVal t.mem base (c.sl E) c.n >>> 0 ∧
      KeepRegs [.x1, .x2] t t' ∧ Outside base (c.sl K) (24 * c.n) t.mem t'.mem :=
    WP.block_nil ⟨Nat.shiftRight_zero.symm, Nat.shiftRight_zero.symm, Nat.shiftRight_zero.symm,
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  rcases hhs with rfl | rfl | rfl
  · exact nil
  · by_cases h0 : c.sh = 0
    · simp only [Cfg.shiftCode, h0, ite_true]
      rw [shAt_self, h0, shAt_D_K, shAt_D_E]; exact nil
    · simp only [Cfg.shiftCode, h0, ite_false]
      refine WP.mono (shrWords_ok hs' hDl (sl_mod8 c D) (by omega) hc.sh) fun t' ⟨e, k, O⟩ =>
        ⟨?_, ?_, ?_, k, O.mono (by omega) (by omega)⟩
      · rw [shAt_D_K, Nat.shiftRight_zero]; exact O.wordsVal (by omega) (by omega)
      · rw [shAt_self]; exact e
      · rw [shAt_D_E, Nat.shiftRight_zero]; exact O.wordsVal (by omega) (by omega)
  · by_cases h0 : c.sh = 0
    · simp only [Cfg.shiftCode, h0, ite_true]
      rw [shAt_self, h0, shAt_E_D, shAt_E_K]; exact nil
    · simp only [Cfg.shiftCode, h0, ite_false]
      refine WP.mono (shrWords_ok hs' hEl (sl_mod8 c E) (by omega) hc.sh) fun t' ⟨e, k, O⟩ =>
        ⟨?_, ?_, ?_, k, O.mono (by omega) (by omega)⟩
      · rw [shAt_E_K, Nat.shiftRight_zero]; exact O.wordsVal (by omega) (by omega)
      · rw [shAt_E_D, Nat.shiftRight_zero]; exact O.wordsVal (by omega) (by omega)
      · rw [shAt_self]; exact e

/-! ## The constants -/

/-- The constants of `l`, apart slots below `17`, each in its slot; only their
slots change. -/
theorem setupConsts_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} : ∀ (l : List (Nat × Nat)) {t : State},
    Scr t base size → (∀ ix ∈ l, ix.1 < 17 ∧ ix.2 < 2 ^ (64 * c.n)) → (l.map Prod.fst).Nodup →
    WP isa (.block (l.flatMap (fun (i, x) => setConst c.n (c.sl i) x))) t fun t' =>
      (∀ ix ∈ l, wordsVal t'.mem base (c.sl ix.1) c.n = ix.2) ∧ KeepRegs [.x1] t t' ∧
      Unch base (l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem
  | [], _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Unch.refl _ _ _⟩
  | (i, x) :: l, t, hs, hb, hnd => by
    rw [List.flatMap_cons, WP.block_append_iff]
    have hi := hb (i, x) List.mem_cons_self
    have hl := sl_le c hc.n10 (i := i) (by omega)
    have hsz : size = 8192 := rfl
    refine WP.mono (setConst_ok hs hl (sl_mod8 c i) hi.2) fun t₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [List.map_cons, List.nodup_cons] at hnd
    refine WP.mono (setupConsts_ok hc l hs₁ (fun ix h => hb ix (List.mem_cons_of_mem _ h)) hnd.2)
      fun t' ⟨e', k', U'⟩ => ⟨fun ix h => ?_, k₁.trans k',
        show Unch base ([(c.sl i, 8 * c.n)] ++ l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem from
          O₁.unch.trans U'⟩
    rcases List.mem_cons.mp h with rfl | h
    · refine (U'.wordsVal (fun w hw => ?_) (by dsimp only; omega)).trans e₁
      obtain ⟨jy, hjy, rfl⟩ := List.mem_map.mp hw
      have hj17 := (hb _ (List.mem_cons_of_mem _ hjy)).1
      exact sl_apart c (fun heq => hnd.1 (heq ▸ List.mem_map_of_mem hjy)) (.inr (by omega))
        (.inr (by omega))
    · exact e' ix h

theorem consts_fst (c : Cfg) :
    c.consts.map Prod.fst = [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16] := rfl

theorem consts_ne_tmp (c : Cfg) : ∀ ix ∈ c.consts, ix.1 ≠ TMP := by
  intro ix hix
  have : ix.1 ∈ c.consts.map Prod.fst := List.mem_map_of_mem hix
  rw [consts_fst] at this
  revert this; generalize ix.1 = i; decide +revert

theorem consts_nodup (c : Cfg) : (c.consts.map Prod.fst).Nodup := by
  rw [consts_fst]; decide

theorem consts_bounds {c : Cfg} (hc : BaseCfgOk c) :
    ∀ ix ∈ c.consts, ix.1 < 17 ∧ ix.2 < 2 ^ (64 * c.n) := by
  intro ix h
  refine ⟨?_, ?_⟩
  · have := List.mem_map_of_mem (f := Prod.fst) h
    rw [consts_fst] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  · have hp0 : 0 < c.C.p := by have := hc.p_ge; omega
    have hn0 : 0 < c.C.n := by have := hc.n_ge; omega
    have hR : 1 < 2 ^ (64 * c.n) := Nat.one_lt_two_pow (by have := hc.n0; omega)
    have hm : ∀ x, c.mont x < 2 ^ (64 * c.n) := fun x =>
      Nat.lt_trans (Nat.mod_lt (x * c.R) hp0) hc.p_lt
    have hn : ∀ x, x % c.C.n < 2 ^ (64 * c.n) := fun x => Nat.lt_trans (Nat.mod_lt x hn0) hc.n_lt
    simp only [Cfg.consts, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hc.p_lt
    · exact hc.n_lt
    · exact Nat.lt_trans Nat.one_pos hR
    · exact hR
    · exact hm 1
    · exact hm _
    · exact hm _
    · exact hm _
    · exact hm _
    · exact hn _
    · exact hn _
    · exact Nat.lt_trans Nat.one_pos hR
    · exact hm 1
    · exact Nat.lt_trans Nat.one_pos hR

/-! ## The flag -/

theorem setupFlag_ok {c : Cfg} (hc : BaseCfgOk c) {t : State} {base : Addr} (hs : Scr t base size) :
    WP isa (.block (setConst 1 (c.sl FLAG) (2 ^ 64 - 1))) t fun t' =>
      word t'.mem base (c.sl FLAG) = BitVec.allOnes 64 ∧ KeepRegs [.x1] t t' ∧
      Outside base (c.sl FLAG) (8 * 1) t.mem t'.mem := by
  have hl := sl_le c hc.n10 (i := FLAG) (by decide)
  have := hc.n0
  refine WP.mono (setConst_ok hs (by omega) (sl_mod8 c FLAG) (by decide)) fun t' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  have e' : (word t'.mem base (c.sl FLAG)).toNat = 2 ^ 64 - 1 := by
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at e
    exact e
  exact BitVec.eq_of_toNat_eq (by rw [e', BitVec.toNat_allOnes])

/-! ## The whole setup -/

theorem setup_eq (c : Cfg) (hs : Option Nat) : c.setupWith hs = Spill.saveCode .x4 Cfg.saved ++
    (([.addImm .x .x20 .x0 0, .addImm .x .x0 .x4 0] : List Instr) ++
    (loadBytes c.C.len c.n (c.sl K) .x3 ++ (loadBytes c.C.len c.n (c.sl D) .x1 ++
    (loadBytes c.C.len c.n (c.sl E) .x2 ++ (c.shiftCode hs ++
    (c.consts.flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
    setConst 1 (c.sl FLAG) (2 ^ 64 - 1))))))) := by
  simp only [Cfg.setupWith, List.append_assoc]; rfl

theorem setup_ok {c : Cfg} (hc : BaseCfgOk c) {hs : Option Nat} (hhs : ShiftOk hs) {s : State}
    (hp : SetupPre c s) :
    WP isa (.block (c.setupWith hs)) s (SetupPost c hs s (s.gpr .x4)) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hsz : size = 8192 := rfl
  have hw : (⟨s.gpr .x4, size⟩ : Region) ∈ s.wr := hp.wr
  rw [setup_eq c hs, WP.block_append_iff]
  refine WP.mono (setupSaves_ok rfl hw) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, O₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setupMovs_ok s₁) fun s₂ ⟨x20₂, x0₂, k₂, m₂⟩ => ?_
  have hs₂ : Scr s₂ (s.gpr .x4) size :=
    ⟨by rw [x0₂, g₁], by rw [k₂.wr, wr₁]; exact hw, hp.sc_fit, by decide⟩
  have G₂ : ∀ r, r ≠ .x20 → r ≠ .x0 → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [k₂.gpr r (by simp [h₁, h₂]), g₁]
  have RD₂ : s₂.rd ++ s₂.wr = s.rd ++ s.wr := by rw [k₂.rd, k₂.wr, rd₁, wr₁]
  have O₂ : Outside (s.gpr .x4) 0 size s.mem s₂.mem := by
    rw [m₂]; exact O₁.mono (Nat.le_refl _) (by omega)
  have hK : c.sl K = 64 + 8 * c.n * 31 := rfl
  have hD : c.sl D = 64 + 8 * c.n * 32 := rfl
  have hE : c.sl E = 64 + 8 * c.n * 33 := rfl
  have hF : c.sl FLAG = 64 + 8 * c.n * 44 := rfl
  have h17 : c.sl 17 = 64 + 8 * c.n * 17 := rfl
  -- `k`
  rw [WP.block_append_iff]
  refine WP.mono (setupLoad_ok hc (s := s) hs₂ (by decide) (by decide) (i := K) (by decide)
    (G₂ _ (by decide) (by decide)) (by rw [RD₂]; exact hp.k_in) hp.k_sc O₂)
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  -- `d`
  rw [WP.block_append_iff]
  refine WP.mono (setupLoad_ok hc (s := s) hs₃ (by decide) (by decide) (i := D) (by decide)
    (by rw [k₃.gpr _ (by decide)]; exact G₂ _ (by decide) (by decide))
    (by rw [k₃.rd, k₃.wr, RD₂]; exact hp.d_in) hp.d_sc
    (O₂.trans (O₃.mono (Nat.zero_le _) (by omega)))) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  -- the hash
  rw [WP.block_append_iff]
  refine WP.mono (setupLoad_ok hc (s := s) hs₄ (by decide) (by decide) (i := E) (by decide)
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide)]; exact G₂ _ (by decide) (by decide))
    (by rw [k₄.rd, k₄.wr, k₃.rd, k₃.wr, RD₂]; exact hp.digest_in) hp.digest_sc
    ((O₂.trans (O₃.mono (Nat.zero_le _) (by omega))).trans (O₄.mono (Nat.zero_le _) (by omega))))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  -- the shift
  rw [WP.block_append_iff]
  refine WP.mono (setupShift_ok hc hhs hs₅) fun sS ⟨fK, fD, fE, kS, OS⟩ => ?_
  have hsS := hs₅.of_keepRegs kS (by decide)
  -- the constants
  rw [WP.block_append_iff]
  refine WP.mono (setupConsts_ok hc c.consts hsS (consts_bounds hc) (consts_nodup c))
    fun s₆ ⟨e₆, k₆, U₆⟩ => ?_
  have hs₆ := hsS.of_keepRegs k₆ (by decide)
  have O₆ : Outside (s.gpr .x4) (c.sl 0) (8 * c.n * 17) sS.mem s₆.mem := U₆.outside fun w hw => by
    obtain ⟨ix, hix, rfl⟩ := List.mem_map.mp hw
    have := sl_lt c (consts_bounds hc ix hix).1 (consts_ne_tmp c ix hix)
    have h0' : c.sl 0 = 64 := by simp (disch := decide) only [sl_eq]; omega
    have : c.sl 0 ≤ c.sl ix.1 := by rw [h0', sl_eq c ix.1 (consts_ne_tmp c ix hix)]; omega
    exact ⟨this, by omega⟩
  have hsl0 : c.sl 0 = 64 := by simp (disch := decide) only [sl_eq]; omega
  -- the flag
  refine WP.mono (setupFlag_ok hc hs₆) fun s' ⟨f', k', O'⟩ => ?_
  have K₃ : KeepRegs [.x1, .x2, .x5, .x17] s₂ s' :=
    ((((k₃.mono (by sub_regs)).trans (k₄.mono (by sub_regs))).trans (k₅.mono (by sub_regs))).trans
      (kS.mono (by sub_regs))).trans ((k₆.mono (by sub_regs)).trans (k'.mono (by sub_regs)))
  -- Everything after the moves writes only in `[64, size)`.
  have Ol : Outside (s.gpr .x4) 64 (size - 64) s₂.mem s'.mem :=
    (((((O₃.mono (by omega) (by omega)).trans (O₄.mono (by omega) (by omega))).trans
      (O₅.mono (by omega) (by omega))).trans (OS.mono (by omega) (by omega))).trans
      (O₆.mono (by omega) (by omega))).trans (O'.mono (by omega) (by omega))
  refine ⟨hs₆.of_keepRegs k' (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun ix hix => ?_, f'⟩
  · rw [K₃.gpr _ (by decide), x20₂, g₁]
  · refine ⟨fun r hr => ?_, by rw [K₃.rd, k₂.rd, rd₁], by rw [K₃.wr, k₂.wr, wr₁],
      by rw [K₃.sp, k₂.sp, sp₁]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [K₃.gpr r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1]), G₂ r hr.2.2.2.2.2 hr.1]
  · exact (O₂.trans (Ol.mono (Nat.zero_le _) (by omega))).unch
  · intro rd hrd
    have := setupSaved_lt rd hrd
    exact (Ol.word (d := rd.2) (by omega) (by omega)).trans
      ((congrArg (fun m => Mem.readW m _ 64) m₂).trans (sv₁ rd hrd))
  · show wordsVal s'.mem _ _ _ = _
    rw [O'.wordsVal (by omega) (by omega), O₆.wordsVal (by omega) (by omega), fK,
      O₅.wordsVal (by omega) (by omega), O₄.wordsVal (by omega) (by omega), e₃]
  · show wordsVal s'.mem _ _ _ = _
    rw [O'.wordsVal (by omega) (by omega), O₆.wordsVal (by omega) (by omega), fD,
      O₅.wordsVal (by omega) (by omega), e₄]
  · show wordsVal s'.mem _ _ _ = _
    rw [O'.wordsVal (by omega) (by omega), O₆.wordsVal (by omega) (by omega), fE, e₅]
  · have := sl_lt c (consts_bounds hc ix hix).1 (consts_ne_tmp c ix hix)
    have := sl_le c hc.n10 (i := 17) (by decide)
    show wordsVal s'.mem _ _ _ = _
    rw [O'.wordsVal (by omega) (by omega), e₆ ix hix]

end VG.Proof.Ecdsa.AArch64
