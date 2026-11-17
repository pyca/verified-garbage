module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJP
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.AArch64.InterleaveTable
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Weierstrass.AArch64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
public import VerifiedGarbage.Proof.Weierstrass.Booth

/-! ### `Weierstrass.AArch64.TCombSelectV2`, which only this module used -/

section

/-!
# The comb from tables in memory on AArch64: the selection in two passes

For an entry of `n` pairs, `n` even with `n / 2 ≤ 3` (P-384's six words a
coordinate), `TCombCfg.selPass2` selects `x`'s pairs in one pass, moves them
to `selKeep` (`keepMovs_ok`), which the second pass does not write, and
selects `y`'s in another (`pass2_ok`); after it, `y` is set to `R` if the
magnitude is zero, and both are stored, `x` from `selKeep` (`selXY2Fin_ok`),
then `Z` (`tselectFin2_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

theorem selKeep_ne : ∀ c ≤ 3, ∀ i < c, ∀ i' < c, i ≠ i' → selKeep.getD i .v3 ≠ selKeep.getD i' .v3 := by
  decide
theorem selKeep_acc : ∀ c ≤ 3, ∀ i < c, ∀ i' < c, selKeep.getD i .v3 ≠ (selA c).acc.getD i' .v0 := by
  decide
theorem selKeep_AB : ∀ c ≤ 3, ∀ i < c, selKeep.getD i .v3 ∉ (selA c).wr ++ (selB c).wr := by decide
theorem selKeep_o : ∀ c ≤ 3, ∀ i < c, selKeep.getD i .v3 ∉ [VReg.v16, .v18, .v19, .v20, .v28] := by decide

/-- The first pass's accumulators moved to `selKeep`. -/
theorem keepMovs_ok {c : Nat} (hc : c ≤ 3) {s : State} : ∀ k ≤ c,
    WP isa (.block ((List.range k).map fun i =>
      Instr.vop (.mov (selKeep.getD i .v3) ((selA c).acc.getD i .v0)))) s fun t =>
      (∀ i < k, t.v (selKeep.getD i .v3) = s.v ((selA c).acc.getD i .v0)) ∧
      VKeep [] ((List.range k).map fun i => selKeep.getD i .v3) s t
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), VKeep.refl _ _ _⟩
  | k + 1, hk => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [WP.block_append_iff]
    refine WP.mono (keepMovs_ok hc k (by omega_using [hk])) fun s₁ ⟨v₁, k₁⟩ => ?_
    obtain e1 : s₁.v ((selA c).acc.getD k .v0) = s.v ((selA c).acc.getD k .v0) :=
      k₁.v _ (not_mem_map_range fun i hi e => selKeep_acc c hc i (by omega_using [hk, hi]) k
        (by omega_using [hk]) e)
    refine wp_vop (d := selKeep.getD k .v3) (x := s.v ((selA c).acc.getD k .v0))
      (by simp only [VOp.eval, e1]) (WP.block_nil ⟨fun i hi => ?_,
        (k₁.mono (fun _ h => h) fun _ h => List.mem_append_left _ h).trans
        ((VKeep.setV _ _ _).mono (fun _ h => h) fun _ h => List.mem_append_right _ h)⟩)
    rcases Nat.lt_or_ge i k with h | h
    · rw [RegUpd.v_setV_of_ne _ _ (selKeep_ne c hc i (by omega_using [hk, h]) k (by omega_using [hk])
        (by omega_using [h])), v₁ i h]
    · obtain rfl : i = k := by omega_using [hi, h]
      rw [RegUpd.v_setV_self]

/-- The two passes of an entry of `n` pairs (`n` even, `n / 2 ≤ 3`) from the
table at `x30`: `x`'s pairs of entry `a` in `selKeep` and `y`'s in `selA`'s
accumulators if `a ≥ 1`, else zeros. -/
theorem pass2_ok (K : TCombCfg) (hn6 : K.M.n / 2 ≤ 3) (hn2 : K.M.n % 2 = 0) {a : Nat} (ha : a ≤ K.H)
    (hH2 : K.H % 2 = 0) (hH : 16 * K.M.n * K.H ≤ 65536) (hHlt : K.H < 2 ^ 64) {s : State}
    (h18 : s.v .v18 = dup2 2) (h19 : s.v .v19 = dup2 (BitVec.ofNat 64 a)) (h28 : s.v .v28 = dup2 1)
    (hreg : InRegions (s.rd ++ s.wr) (s.gpr .x30) (16 * K.M.n * K.H)) :
    WP isa (.block K.selPass2) s fun t =>
      (∀ i < K.M.n / 2, t.v (selKeep.getD i .v3) = if 1 ≤ a then ldE K.M.n 0 s a i .x30 else 0) ∧
      (∀ i < K.M.n / 2, t.v ((selA (K.M.n / 2)).acc.getD i .v0) =
        if 1 ≤ a then ldE K.M.n (8 * K.M.n) s a i .x30 else 0) ∧
      t.v .v18 = s.v .v18 ∧ t.v .v19 = s.v .v19 ∧ t.v .v28 = s.v .v28 ∧
      VKeep [] ((selA (K.M.n / 2)).wr ++ (selB (K.M.n / 2)).wr ++ selKeep) s t := by
  obtain hc : K.M.n / 2 ≤ 4 := by omega_using [hn6]
  obtain hn16 : 16 * (K.M.n / 2) = 8 * K.M.n := by omega_using [hn2]
  unfold TCombCfg.selPass2
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (passV_ok K (tb := .x30) (o := 0) (c := K.M.n / 2) hc (by omega_using [hn16]) (by decide)
    ha hH2 hH hHlt h18 h19 h28 (tbl_region hreg (by omega_using [hn16])))
    fun s₁ ⟨v₁, a18, a19, a28, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (keepMovs_ok (c := K.M.n / 2) (s := s₁) hn6 _ (Nat.le_refl _)) fun s₂ ⟨v₂, k₂⟩ => ?_
  obtain hsub : ∀ r ∈ (List.range (K.M.n / 2)).map fun i => selKeep.getD i .v3, r ∈ selKeep :=
    map_range_sub fun i hi =>
      (by decide : ∀ i < 3, selKeep.getD i .v3 ∈ selKeep) i (by omega_using [hi, hn6])
  obtain k₁₂ : VKeep [] ((selA (K.M.n / 2)).wr ++ (selB (K.M.n / 2)).wr ++ selKeep) s s₂ :=
    (k₁.mono (fun _ h => h) fun _ h => List.mem_append_left _ h).trans
      (k₂.mono (fun _ h => h) fun r h => List.mem_append_right _ (hsub r h))
  obtain ko : ∀ r ∈ [VReg.v16, .v18, .v19, .v20, .v28], s₂.v r = s₁.v r := fun r hr =>
    k₂.v _ (not_mem_map_range fun i hi e => selKeep_o _ hn6 i hi (by rw [e]; exact hr))
  obtain hreg₂ : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x30) (16 * K.M.n * K.H) := by
    rw [k₁₂.rd, k₁₂.wr, k₁₂.gpr _ List.not_mem_nil]; exact hreg
  refine WP.mono (passV_ok K (tb := .x30) (o := 8 * K.M.n) (c := K.M.n / 2) hc (by omega_using [hn16])
    (by omega_using [hn2]) ha hH2 hH hHlt (by rw [ko _ (by simp), a18, h18]) (by rw [ko _ (by simp), a19, h19])
    (by rw [ko _ (by simp), a28, h28]) (tbl_region hreg₂ (by omega_using [hn16])))
    fun t ⟨v₃, b18, b19, b28, k₃⟩ => ?_
  obtain eL : ∀ o i, ldE K.M.n o s₂ a i .x30 = ldE K.M.n o s a i .x30 := fun o i => by
    simp only [ldE, k₁₂.mem, k₁₂.gpr _ List.not_mem_nil]
  refine ⟨fun i hi => ?_, fun i hi => by rw [v₃ i hi, eL], ?_, ?_, ?_, ?_⟩
  · rw [k₃.v _ (selKeep_AB _ hn6 i hi), v₂ i hi, v₁ i hi]
  · rw [b18, ko _ (by simp), a18]
  · rw [b19, ko _ (by simp), a19]
  · rw [b28, ko _ (by simp), a28]
  · rw [← List.append_assoc]
    exact k₁₂.trans (k₃.mono (fun _ h => h) fun _ h => List.mem_append_left _ h)

/-- After the two passes (`x`'s pairs of entry `a` of the table at `tb` in
`r` in `selKeep`, `y`'s in `selA`'s accumulators, if `a ≥ 1`, else zeros):
`y = R` if `a = 0`, and both stored. -/
theorem selXY2Fin_ok (K : TCombCfg) (hn6 : K.M.n / 2 ≤ 3) (hn2 : K.M.n % 2 = 0) {s : State} {base : Addr}
    {size : Nat} (hs : Scr s base size) {a : Nat} (ha64 : a < 2 ^ 64) {r : State} {tb : Reg}
    (h19 : s.v .v19 = dup2 (BitVec.ofNat 64 a))
    (hkx : ∀ i < K.M.n / 2, s.v (selKeep.getD i .v3) = if 1 ≤ a then ldE K.M.n 0 r a i tb else 0)
    (hay : ∀ i < K.M.n / 2, s.v ((selA (K.M.n / 2)).acc.getD i .v0) =
      if 1 ≤ a then ldE K.M.n (8 * K.M.n) r a i tb else 0)
    (hEx : K.E.x + 8 * K.M.n ≤ size) (hEy : K.E.y + 8 * K.M.n ≤ size)
    (hE16 : K.E.x % 16 = 0 ∧ K.E.y % 16 = 0)
    (axy : K.E.x + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ K.E.x) (hone : K.one < 2 ^ (64 * K.M.n)) :
    WP isa (.block (TCombCfg.selOne K.one (K.M.n / 2) 0 (K.M.n / 2) ++
      ((List.range (K.M.n / 2)).map fun i => Instr.strq (selKeep.getD i .v3) .x0 (K.E.x + 16 * i)) ++
      selStore (K.M.n / 2) 0 (K.M.n / 2) K.E.y)) s fun t =>
      wordsVal t.mem base K.E.x K.M.n =
        (if 1 ≤ a then wordsVal r.mem (r.gpr tb) (16 * K.M.n * (a - 1)) K.M.n else 0) ∧
      wordsVal t.mem base K.E.y K.M.n =
        (if 1 ≤ a then wordsVal r.mem (r.gpr tb) (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n else K.one) ∧
      KeepRegs [.x6] s t ∧ Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n)] s.mem t.mem ∧
      Scr t base size := by
  have hnw := hs.nowrap
  obtain hc : K.M.n / 2 ≤ 4 := by omega_using [hn6]
  iterate 2 rw [WP.block_append_iff]
  refine WP.mono (selOneV_ok K.one (c := K.M.n / 2) (h := 0) (k := K.M.n / 2) hc (by omega_using []) ha64
    h19) fun s₂ ⟨f₂, k₂⟩ => ?_
  have K02 : Keeps [.x6] s s₂ := k₂.keeps
  obtain hs₂ : Scr s₂ base size := hs.of_keeps K02 (by decide)
  refine WP.mono (qstoresV_ok (fun i => selKeep.getD i .v3) hs₂ hE16.1 (K.M.n / 2)
    (by omega_using [hEx, hn2])) fun s₃ ⟨w₃, kr₃, v₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs kr₃ (by decide)
  refine WP.mono (qstoresV_ok (fun i => (selA (K.M.n / 2)).acc.getD (0 + i) .v0) hs₃ hE16.2
    (K.M.n / 2) (by omega_using [hEy, hn2])) fun t ⟨w₄, kr₄, v₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs kr₄ (by decide)
  obtain hn16 : 16 * (K.M.n / 2) = 8 * K.M.n := by omega_using [hn2]
  rw [hn16] at O₃ O₄
  obtain vx : ∀ i < K.M.n / 2, s₂.v (selKeep.getD i .v3) = if 1 ≤ a then ldE K.M.n 0 r a i tb else 0 :=
    fun i hi => by
      obtain ho := selKeep_o _ hn6 i hi
      rw [k₂.v _ (by
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => ho (by rw [e]; simp), fun e => ho (by rw [e]; simp),
          not_mem_map_range fun i' hi' e => selKeep_acc _ hn6 i hi _ (by omega_using [hi']) e.symm⟩),
        hkx i hi]
  obtain vy : ∀ i < K.M.n / 2, s₂.v ((selA (K.M.n / 2)).acc.getD (0 + i) .v0) =
      if 1 ≤ a then ldE K.M.n (8 * K.M.n) r a i tb
      else ofVDwords (wordOf K.one (2 * i)) (wordOf K.one (2 * i + 1)) := fun i hi => by
    rw [f₂ i hi, Nat.zero_add, hay i hi]
    by_cases h : 1 ≤ a
    · rw [ite_f (show ¬ a = 0 by omega_using [h]), ite_t h, ite_t h]
    · rw [ite_t (show a = 0 by omega_using [h]), ite_f h]
  obtain wx : ∀ j < K.M.n, word t.mem base (K.E.x + 8 * j) =
      if 1 ≤ a then word r.mem (r.gpr tb) (16 * K.M.n * (a - 1) + 8 * j) else 0 := fun j hj => by
    rw [O₄.word (by omega_using [axy, hj]) (by omega_using [hEx, hnw, hj]), w₃ j (by omega_using [hn16, hj]),
      vx _ (by omega_using [hn16, hj])]
    by_cases h : 1 ≤ a
    · rw [ite_t h, ite_t h, vdword_ldE _ _ _ _ _ (Nat.mod_lt _ (by decide)),
        show 16 * K.M.n * (a - 1) + 0 + 16 * (j / 2) + 8 * (j % 2) = 16 * K.M.n * (a - 1) + 8 * j by omega_using []]
    · rw [ite_f h, ite_f h, vdword_zero]
  obtain wy : ∀ j < K.M.n, word t.mem base (K.E.y + 8 * j) =
      if 1 ≤ a then word r.mem (r.gpr tb) (16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * j) else wordOf K.one j :=
    fun j hj => by
      rw [w₄ j (by omega_using [hn16, hj]), v₃, vy _ (by omega_using [hn16, hj])]
      by_cases h : 1 ≤ a
      · rw [ite_t h, ite_t h, vdword_ldE _ _ _ _ _ (Nat.mod_lt _ (by decide)),
          show 16 * K.M.n * (a - 1) + 8 * K.M.n + 16 * (j / 2) + 8 * (j % 2) =
            16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * j by omega_using []]
      · rw [ite_f h, ite_f h]
        rcases Nat.mod_two_eq_zero_or_one j with e | e
        · rw [e, vdword_ofVDwords_0, show 2 * (j / 2) = j by omega_using [e]]
        · rw [e, vdword_ofVDwords_1, show 2 * (j / 2) + 1 = j by omega_using [e]]
  obtain ⟨ex, ey⟩ := selXY_vals K hone wx wy
  refine ⟨ex, ey, ((Keeps.regs K02).trans (kr₃.mono fun _ h => absurd h List.not_mem_nil)).trans
    (kr₄.mono fun _ h => absurd h List.not_mem_nil), fun x hx => ?_, hs₄⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
  rw [O₄ x (by omega_using [hx]), O₃ x (by omega_using [hx]), K02.mem]

/-- `tselectFin_ok`, after the two passes. -/
theorem tselectFin2_ok (K : TCombCfg) (hn6 : K.M.n / 2 ≤ 3) (hn2 : K.M.n % 2 = 0) {s : State} {base : Addr}
    {size : Nat} (hs : Scr s base size) {a : Nat} (ha64 : a < 2 ^ 64) (hx2 : s.gpr .x2 = BitVec.ofNat 64 a)
    {r : State} {tb : Reg} (h19 : s.v .v19 = dup2 (BitVec.ofNat 64 a))
    (hkx : ∀ i < K.M.n / 2, s.v (selKeep.getD i .v3) = if 1 ≤ a then ldE K.M.n 0 r a i tb else 0)
    (hay : ∀ i < K.M.n / 2, s.v ((selA (K.M.n / 2)).acc.getD i .v0) =
      if 1 ≤ a then ldE K.M.n (8 * K.M.n) r a i tb else 0)
    (hE : ∀ d ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ size ∧ d % 8 = 0)
    (hE16 : K.E.x % 16 = 0 ∧ K.E.y % 16 = 0)
    (hap : (K.E.x + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.x + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.y + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.y))
    (hone : K.one < 2 ^ (64 * K.M.n)) :
    WP isa (.block ([zero7, .movz .x .x5 1 0] ++ TCombCfg.selOne K.one (K.M.n / 2) 0 (K.M.n / 2) ++
      ((List.range (K.M.n / 2)).map fun i => Instr.strq (selKeep.getD i .v3) .x0 (K.E.x + 16 * i)) ++
      selStore (K.M.n / 2) 0 (K.M.n / 2) K.E.y ++ K.selZ)) s fun t =>
      wordsVal t.mem base K.E.x K.M.n = (if 1 ≤ a then
        wordsVal r.mem (r.gpr tb) (16 * K.M.n * (a - 1)) K.M.n else 0) ∧
      wordsVal t.mem base K.E.y K.M.n = (if 1 ≤ a then
        wordsVal r.mem (r.gpr tb) (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n else K.one) ∧
      wordsVal t.mem base K.E.z K.M.n = (if 1 ≤ a then K.one else 0) ∧
      KeepRegs (.x1 :: .x2 :: .x3 :: .x4 :: .x5 :: .x6 :: .x7 :: .x16 :: .x17 :: entryRegs K.M.n) s t ∧
      Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem := by
  have hnw := hs.nowrap
  obtain hEx := hE K.E.x (by simp)
  obtain hEy := hE K.E.y (by simp)
  obtain hEz := hE K.E.z (by simp)
  obtain ⟨axy, axz, ayz⟩ := hap
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero7One5_ok s) fun s₁ ⟨e7, e5, k₁⟩ => ?_
  obtain hs₁ : Scr s₁ base size := hs.of_keeps k₁.keeps (by decide)
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (selXY2Fin_ok K hn6 hn2 hs₁ ha64 (r := r) (tb := tb) (by rw [k₁.v _ List.not_mem_nil, h19])
    (fun i hi => by rw [k₁.v _ List.not_mem_nil, hkx i hi])
    (fun i hi => by rw [k₁.v _ List.not_mem_nil, hay i hi]) hEx.1 hEy.1 hE16 axy hone)
    fun s₃ ⟨ex₃, ey₃, kk₃, U₃, hs₃⟩ => ?_
  obtain g₃ : ∀ q ∈ [Reg.x2, .x5, .x7], s₃.gpr q = s₁.gpr q := fun q hq => by
    have : q ≠ .x6 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [kk₃.gpr q (by simpa using this)]
  rw [TCombCfg.selZ, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (selZ_carry s₃ ha64 (by rw [g₃ _ (by simp), k₁.gpr _ (by decide), hx2])
    (by rw [g₃ _ (by simp), e5])) fun s₄ ⟨c₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (zWords_ok K hs₄ (by rw [k₄.gpr _ (by decide), g₃ _ (by simp), e7]) hEz.1 hEz.2
    K.M.n (Nat.le_refl _)) fun t ⟨wt, _, kt, Ot⟩ => ?_
  have hm₄ : s₄.mem = s₃.mem := k₄.mem
  obtain b64 : ∀ d ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ 2 ^ 64 := fun d hd => by
    have := (hE d hd).1; omega_using [hnw, this]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Ot.wordsVal axz (b64 _ (by simp)), hm₄, ex₃]
  · rw [Ot.wordsVal ayz (b64 _ (by simp)), hm₄, ey₃]
  · refine wordsVal_of_shifts _ _ _ _ _ (by split <;> [exact hone; exact Nat.two_pow_pos _])
      fun i hi => ?_
    rw [wt i hi, c₄]
    by_cases h : 1 ≤ a <;> simp only [h, decide_true, decide_false, ↓reduceIte] <;> [rfl; simp]
  · have cl : ∀ q ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17],
        q ∈ (.x1 :: .x2 :: .x3 :: .x4 :: .x5 :: .x6 :: .x7 :: .x16 :: .x17 :: entryRegs K.M.n) :=
      fun q hq => List.mem_append_left (as := [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17]) _ hq
    exact (((((Keeps.regs k₁.keeps).mono fun q hq => cl q (by revert q; decide)).trans
      (kk₃.mono fun q hq => cl q (by revert q; decide))).trans
      ((Keeps.regs k₄).mono fun q hq => cl q (by revert q; decide))).trans
      (kt.mono fun q hq => cl q (by revert q; decide)))
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    obtain hxy' : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n)], ofs base x < w.1 ∨ w.1 + w.2 ≤ ofs base x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hx.1, hx.2.1⟩
    rw [Ot x (by omega_using [hx]), hm₄, U₃ x hxy', k₁.mem]

end VG.Proof.Weierstrass.AArch64

end

end


/-!
# The pipelined comb in two passes on AArch64

`TCombCfg.combJP2` (`Impl/Weierstrass/AArch64/TCombJ.lean`): `combJP` for an
entry of `n` pairs a coordinate, `n` even with `n / 2 ≤ 3`, whose selection
takes two passes (`pass2_ok`), both woven into the addition, with the table's
address in `x30` (`prepNext2_ok`); the first pass's accumulators wait in
`selKeep` until both are stored (`tentryJFin2_ok`). `tcombJP2_ok`: it
computes `[k]G`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.AArch64.Interleave (scalOk vecOk TabApart)
open Spec.Weierstrass

/-- What the two-pass pipelined comb's code must satisfy, checked by
evaluation for a curve: `JPChecks`, with the table's address in `x30` and the
two passes. -/
structure JPChecks2 (K : TCombCfg) (size : Nat) (mc : List Instr) : Prop where
  n6 : K.M.n / 2 ≤ 3
  n2 : K.M.n % 2 = 0
  J3 : 3 ≤ K.J
  scal : mc.all (scalOk .x0 .x30 size) = true
  vec : K.selPass2.all (vecOk .x30 K.tblBytes) = true
  mcv : mc.all (fun i => (vdstOf i).isNone) = true
  fixv : (instrs K.fixJ).all (fun i => (vdstOf i).isNone) = true
  bdv : (K.bdigit true).all (fun i => (vdstOf i).isNone) = true

/-- `x19 = j` from `j + 1`, `x30` = table `j + 1`'s address and `x5 = 1`. -/
theorem setupNext2_ok (K : TCombCfg) (s : State) {j : Nat} {T : Addr}
    (h19 : s.gpr .x19 = BitVec.ofNat 64 (j + 1)) (hT : s.syms K.tsym = T) (htb : K.tblBytes < 65536) :
    WP isa (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ K.selSetupNext2 ++ ([.movz .x .x5 1 0] : List Instr))) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 j ∧ t.gpr .x30 = T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) ∧
      t.gpr .x5 = 1 ∧ Keeps [.x5, .x17, .x19, .x30] s t := by
  subst hT
  apply WP.of_runBlock
  simp only [TCombCfg.selSetupNext2, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, read_x, Size.bits, show 1 < 4096 by decide, show 16 * 0 < Size.x.bits from by decide,
    ite_true, RegUpd.gpr_write, BitVec.setWidth_eq, ite_false, reduceCtorEq, h19, dec_ofNat,
    BitVec.ofNat_add_ofNat, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, by decide, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · show s.syms K.tsym + _ = _
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.shiftLeft_eq, Nat.mul_zero, Nat.pow_zero, Nat.mul_one,
      Nat.mod_eq_of_lt (show K.tblBytes < 2 ^ 16 by omega_using [htb]), Nat.mod_mod]
    rw [← Nat.mul_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem prep2_tcombClob (n : Nat) (hn : n ≤ 9) :
    ∀ r ∈ [Reg.x2, .x3, .x4, .x5, .x7, .x9, .x16, .x17, .x19, .x30], r ∈ tcombClob n := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact combClob_tcombClob _ (List.mem_cons_self ..)
    | exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    | exact tcombClob_sub _ hn _ (List.mem_append_left _ (by decide))

/-- Before window `j`'s addition (`1 ≤ j`, `j + 2 ≤ J`): digit `j + 1`'s
magnitude broadcast for its selection (`v19`, with one in `v28` and two in
`v18`) and its table's address in `x30`, the rest as it was. -/
theorem prepNext2_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {ws : List (BitVec 64)} (hL : TCombLay K size) (hb1 : 1 ≤ K.bits) {s₀ s : State} {j : Nat}
    (hjn : j + 2 ≤ K.J) (hI : TCombJInv K C base size k T ws s₀ s j) :
    WP isa (.block K.prepNext2) s fun t => TCombJInv K C base size k T ws s₀ t j ∧ t.mem = s.mem ∧
      t.syms = s.syms ∧ KeepRegs (tcombClob K.M.n) s t ∧
      t.gpr .x30 = T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) ∧
      t.v .v19 = dup2 (BitVec.ofNat 64 (bmag K.w k (j + 1))) ∧ t.v .v18 = dup2 2 ∧ t.v .v28 = dup2 1 := by
  have hs := hI.scr
  have hw := hL.w
  obtain hwi : K.w * (j + 1) + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show j + 1 + 1 ≤ K.J by omega_using [hjn]); rwa [Nat.mul_succ] at this
  obtain hb : K.bits + K.w * K.J ≤ size := by
    have := hL.bits
    have := hL.kbytes
    unfold TCombCfg.zw at *
    omega_arith
  obtain hwb : K.bits + K.w ≤ 4096 := by
    have := hL.bitsw
    omega_using [hwi, this]
  obtain hcl := prep2_tcombClob K.M.n hL.n8
  unfold TCombCfg.prepNext2
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (inc19_ok s hI.x19) fun s₁ ⟨b₁, k₁⟩ sy₁ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono_syms (bdigit_ok K hs₁ (k := k) (j := j + 1) (N := K.w * K.J) (by omega_using [hw])
    (by omega_using [hw]) hwi (by omega_using [hb, hwi]) hb1 hwb b₁ (fun t ht => by rw [k₁.mem]; exact hI.bits t ht)
    (Or.inl ⟨rfl, by omega_using []⟩)) fun s₂ ⟨r₂, k₂⟩ sy₂ => ?_
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (setupNext2_ok K s₂ (j := j) (T := T) (by rw [k₂.gpr _ (by decide), b₁])
    (by rw [sy₂, sy₁]; exact hI.tsym) hL.tbl.2) fun s₃ ⟨b₃, x₃, e₃, k₃⟩ sy₃ => ?_
  refine WP.mono_syms (bcastV_ok s₃) fun t ⟨v19, v28, v18, k₄⟩ sy₄ => ?_
  obtain hm : t.mem = s.mem := by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem]
  obtain hsy : t.syms = s.syms := by rw [sy₄, sy₃, sy₂, sy₁]
  obtain hk : KeepRegs (tcombClob K.M.n) s t :=
    (((Keeps.regs k₁).mono fun r hr => hcl r (by simp only [List.mem_singleton] at hr; simp [hr])).trans
      ((Keeps.regs k₂).mono fun r hr => hcl r (by revert r; decide))).trans
      (((Keeps.regs k₃).mono fun r hr => hcl r (by revert r; decide)).trans
        ((Keeps.regs k₄.keeps).mono fun _ h => absurd h List.not_mem_nil))
  obtain hst : Scr t base size :=
    ((hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)).of_keeps k₄.keeps (by decide)
  refine ⟨hI.of_keep hk hm (by rw [k₄.gpr _ List.not_mem_nil, b₃]) hsy hst, hm, hsy, hk,
    by rw [k₄.gpr _ List.not_mem_nil, x₃], by rw [v19, k₃.gpr _ (by decide), r₂], ?_, by rw [v28, e₃]⟩
  rw [v18, e₃]; rfl

/-- After window `i - 1`'s corrections (`1 ≤ i < J`, `x19 = i`), with the
pass of window `i`'s selection in the accumulators (of the table at `x30` in
`r`, whose bytes the memory keeps) and its magnitude in `v19`: the digit
again, its entry stored to `E`, and negated (`tentryJ_ok` for the pipelined
selection). -/
theorem tentryJFin2_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k i : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n)) (hn6 : K.M.n / 2 ≤ 3) (hn2 : K.M.n % 2 = 0)
    (hbdv : (K.bdigit true).all (fun i => (vdstOf i).isNone) = true) {u : State} (hs : Scr u base size)
    (hM : ModOkA K.M size C.p u.mem base) (hi : i < K.J) (hi1 : 1 ≤ i) (hx : u.gpr .x19 = BitVec.ofNat 64 i)
    (hb1 : 1 ≤ K.bits)
    (hbits : ∀ t < K.w * K.J, u.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0)
    (hz : wordsVal u.mem base K.zero K.M.n = 0)
    (hTM : TblMem u T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    {r : State} (hr30 : r.gpr .x30 = T + BitVec.ofNat 64 (i * K.tblBytes))
    (hrm : ∀ b < K.tblBytes, r.mem (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 b) =
      u.mem (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 b))
    (h19 : u.v .v19 = dup2 (BitVec.ofNat 64 (bmag K.w k i)))
    (hkx : ∀ i' < K.M.n / 2, u.v (selKeep.getD i' .v3) =
      if 1 ≤ bmag K.w k i then ldE K.M.n 0 r (bmag K.w k i) i' .x30 else 0)
    (hay : ∀ i' < K.M.n / 2, u.v ((selA (K.M.n / 2)).acc.getD i' .v0) =
      if 1 ≤ bmag K.w k i then ldE K.M.n (8 * K.M.n) r (bmag K.w k i) i' .x30 else 0)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', TEntryPostJ K C base size k i u s' → s'.syms = u.syms → WP isa rest s' Q) :
    WP isa (.block K.finNext2) u fun s₂ => WP isa (.seq (.block K.bnegY) rest) s₂ Q := by
  have hw := hL.w
  obtain hwi : K.w * i + K.w ≤ K.w * K.J := by
    have := Nat.mul_le_mul_left K.w (show i + 1 ≤ K.J from hi)
    rwa [Nat.mul_succ] at this
  obtain hb : K.bits + K.w * K.J ≤ size := by
    have := hL.bits
    have := hL.kbytes
    unfold TCombCfg.zw at *
    omega_arith
  obtain hwb : K.bits + K.w ≤ 4096 := by
    have := hL.bitsw
    omega_using [hwi, this]
  obtain hmag : bmag K.w k i ≤ K.H := bmag_le (by omega_using [hw]) k i
  obtain hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw]))
      (by decide)
  obtain ⟨hE, hap⟩ := combLay_E hL.comb hA
  dsimp only [TCombCfg.toComb] at hE hap
  unfold TCombCfg.finNext2
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono_syms (WP.novec (bdigit_ok K hs (k := k) (j := i) (N := K.w * K.J)
    (by omega_using [hw]) (by omega_using [hw]) hwi hb hb1 hwb hx hbits (Or.inl ⟨rfl, hi1⟩)) hbdv)
    fun t ⟨⟨hm, hk⟩, hv⟩ hsy => ?_
  obtain hs' := hs.of_keeps hk (by decide)
  obtain hM' : ModOkA K.M size C.p t.mem base := hk.mem ▸ hM
  obtain W := tselectFin2_ok K hn6 hn2 hs' (a := bmag K.w k i) (by omega_using [hmag, hHle]) hm (r := r) (tb := .x30)
    (by rw [hv, h19]) (fun i' hi' => by rw [hv, hkx i' hi'])
    (fun i' hi' => by rw [hv, hay i' hi']) hE ⟨hL.e16.1, hL.e16.2 hn2⟩ hap
    (Nat.lt_trans hV.one_lt hpn)
  simp only [List.append_assoc] at W
  refine WP.mono_syms W fun s₂ ⟨ex, ey, ez, k₂, U₂⟩ sy₂ => ?_
  obtain hrt : ∀ b < 16 * K.M.n * K.H, t.mem (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 b) =
      r.mem (T + BitVec.ofNat 64 (i * K.tblBytes) + BitVec.ofNat 64 b) := fun b hb' => by
    rw [hk.mem]; exact (hrm b hb').symm
  rw [hr30] at ex ey
  obtain ex' : wordsVal s₂.mem base K.E.x K.M.n = if 1 ≤ bmag K.w k i then
      wordsVal t.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (bmag K.w k i - 1)) K.M.n else 0 := by
    rw [ex]; split
    · next h1 => exact (wordsVal_tbl (o := 0) hmag h1 (by omega_using []) hrt).symm
    · rfl
  obtain ey' : wordsVal s₂.mem base K.E.y K.M.n = if 1 ≤ bmag K.w k i then
      wordsVal t.mem (T + BitVec.ofNat 64 (i * K.tblBytes)) (16 * K.M.n * (bmag K.w k i - 1) + 8 * K.M.n) K.M.n
      else K.one := by
    rw [ey]; split
    · next h1 => exact (wordsVal_tbl hmag h1 (Nat.le_refl _) hrt).symm
    · rfl
  refine tentryJ_of_sel hL hA hC hV hpn hs' hM' hi (by rw [hk.gpr _ (by decide)]; exact hx)
    (fun q hq => by rw [hk.mem]; exact hbits q hq) (by rw [hk.mem]; exact hz)
    (hTM.unch (by rw [hk.rd,hk.wr]) (fun _ _ _ _ => by rw [hk.mem])) ⟨ex', ey', ez, k₂, U₂⟩ sy₂
    fun s' hu syu => h s' ?_ (by rw [syu, hsy])
  refine ⟨hu.scr,?_,?_,?_,hu.lt,hu.z,hu.rep⟩
  · rw [hu.x19,hk.gpr _ (by decide)]
  · exact ((Keeps.regs hk).mono (fun r hr => tcombClob_sub _ hL.n8 r (by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
      grind))).trans hu.keep
  · rw [← hk.mem]; exact hu.unch

/-- `tabApart_of`, for the table at `x30`. -/
theorem tabApart30_of {s : State} {base X : Addr} {size Tb : Nat} (hs : Scr s base size)
    (hx : s.gpr .x30 = X) (hout : ∀ b < Tb, size ≤ ofs base (X + BitVec.ofNat 64 b)) :
    TabApart .x0 .x30 size Tb s := by
  intro o ho o' ho' he
  obtain h := hout o' ho'
  rw [← hx, ← he, hs.x0] at h
  have hn := hs.nowrap
  have : ofs base (base + BitVec.ofNat 64 o) = o := ofs_off0 base (by omega_using [hn, ho])
  omega_using [h, this, ho]

/-- Pipelined window `j` (`1 ≤ j`, `j + 2 ≤ J`), its entry in `E`: window
`j + 1`'s selection woven into the addition `mc`, whose code runs as the
selection's pass and then the addition; then `x19 = j + 1`, its entry in
`E`, and `x4 = j + 1 - (J - 1)`. -/
theorem stepJP2_ok {arithmetic : Mod → List FOp → Prog isa} {mc : List Instr} {K : TCombCfg} {C : Curve}
    {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb)
    {X : List Reg} (hcompiler : FieldCompilerOn K.M C X arithmetic size)
    (hX : ∀ r ∈ X, r ∈ tcombClob K.M.n ∧ r ≠ .x19) (hJenc : K.J<4096) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hblk : arithmetic K.M (maddJ K.S K.A K.E K.D) = .block mc) (hck : JPChecks2 K size mc)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j + 2 ≤ K.J)
    (hI : TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s j)
    (E : TEntryPostJ K C base size k j s s) :
    WP isa (K.stepJP2 mc) s fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j + 1) ∧
      TEntryPostJ K C base size k (j + 1) s' s' ∧
      s'.gpr .x4 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 (K.J - 1) := by
  have hw := hL.w
  obtain hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  obtain hmag : bmag K.w k (j + 1) ≤ K.H := bmag_le (by omega_using [hw]) k (j + 1)
  obtain hHle : K.H ≤ 128 := by
    unfold TCombCfg.H; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (show K.w - 1 ≤ 7 by omega_using [hw]))
      (by decide)
  obtain hHe : K.H % 2 = 0 := by
    unfold TCombCfg.H; rw [show K.w - 1 = (K.w - 2) + 1 by omega_using [hw], Nat.pow_succ]; omega_using []
  obtain hlen := tbl_len hV
  obtain hout := row_out (K := K) hF.out hlen (j := j + 1) (by omega_using [hjn])
  unfold TCombCfg.stepJP2
  refine WP.seq (WP.mono_syms (prepNext2_ok hL hb1 hjn hI)
    fun p ⟨Ip, hmp, syp, kp, x30p, v19p, v18p, v28p⟩ _ => ?_)
  refine WP.seq (VG.AArch64.Interleave.WP.weave_tab hck.scal hck.vec (tabApart30_of Ip.scr x30p hout) ?_)
  -- The table of window `j + 1`, in the regions.
  obtain hreg : InRegions (p.rd ++ p.wr) (T + BitVec.ofNat 64 ((j + 1) * K.tblBytes)) (16 * K.M.n * K.H) := by
    obtain ⟨r, hr, hc⟩ := Ip.tbl.rd
    refine ⟨r, hr, Region.contains_off hc ?_⟩
    obtain h2 := Nat.mul_le_mul_right K.tblBytes (show j + 1 + 1 ≤ K.J by omega_using [hjn])
    rw [Nat.succ_mul] at h2
    exact Nat.le_trans (by unfold TCombCfg.tblBytes at h2 ⊢; omega_using [h2]) hlen
  refine WP.mono_syms (pass2_ok K hck.n6 hck.n2 hmag hHe (by have := hL.tbl.1; omega_using [this])
    (by omega_using [hHle]) v18p v19p v28p (by rw [x30p]; exact hreg))
    fun q ⟨vkq, vaq, _, q19, _, kq⟩ syq => ?_
  obtain kq' : KeepRegs (tcombClob K.M.n) p q :=
    (Keeps.regs kq.keeps).mono fun _ h => absurd h List.not_mem_nil
  obtain hsq : Scr q base size := Ip.scr.of_keeps kq.keeps (by decide)
  obtain Iq := Ip.of_keep kq' kq.mem (by rw [kq.gpr _ List.not_mem_nil]; exact Ip.x19) syq hsq
  obtain Eq : TEntryPostJ K C base size k j q q := E.self (by rw [kq.mem, hmp]) hsq
  obtain hT := tailJ_ok hL hA hcompiler hX hJenc hC hM3 hG hV hb1 hB hk hF hj (by omega_using [hjn]) Iq Eq rfl
  rw [hblk] at hT
  obtain hT' := WP.mono_syms (WP.novec hT (by
    simp only [instrs, List.all_append, hck.mcv, hck.fixv, Bool.and_self])) fun u hu syu => And.intro hu syu
  refine WP.mono (WP.seq_iff.mp hT') fun t ht => WP.seq (WP.mono ht fun u ⟨⟨⟨Iu, _⟩, vu⟩, syu⟩ => ?_)
  -- Window `j + 1`'s entry, from the pass's accumulators.
  obtain hz : wordsVal u.mem base K.zero K.M.n = 0 := by
    rw [Iu.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); have := Iu.scr.nowrap; omega_arith), hF.zero]
  obtain hrm : ∀ b < K.tblBytes, p.mem (T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) + BitVec.ofNat 64 b) =
      u.mem (T + BitVec.ofNat 64 ((j + 1) * K.tblBytes) + BitVec.ofNat 64 b) := fun b hb => by
    rw [Ip.far hL (hout b hb), Iu.far hL (hout b hb)]
  refine WP.seq (WP.mono (tentryJFin2_ok hL hA hC hV hpn hck.n6 hck.n2 hck.bdv Iu.scr Iu.mod (i := j + 1)
    (by omega_using [hjn]) (by omega_using []) Iu.x19 hb1 Iu.bits hz Iu.tbl (r := p) x30p hrm
    (by rw [vu, q19, v19p]) (fun i' hi' => by rw [vu, vkq i' hi']) (fun i' hi' => by rw [vu, vaq i' hi']) (rest := .block [.subImm .x .x4 .x19 (K.J - 1)])
    (Q := fun s' => TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (j + 1) ∧
      TEntryPostJ K C base size k (j + 1) s' s' ∧
      s'.gpr .x4 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 (K.J - 1)) fun e E' sy' => ?_)
    fun s₂ h₂ => WP.block_append_iff.mpr (WP.seq_iff.mp h₂))
  refine WP.mono_syms (sub4_ok e (c := K.J - 1) (by omega_using [hJenc])) fun f ⟨x4f, kf⟩ syf => ?_
  obtain Ie := Iu.after_entry hL hF E' sy'
  obtain hsf : Scr f base size := E'.scr.of_keeps kf (by decide)
  obtain kf' : KeepRegs (tcombClob K.M.n) e f :=
    (Keeps.regs kf).mono fun r hr => by
      simp only [List.mem_singleton] at hr; rw [hr]; exact tcombClob_sub _ hL.n8 _ (by simp)
  refine ⟨Ie.of_keep kf' kf.mem (by rw [kf.gpr _ (by decide)]; exact Ie.x19) syf hsf, E'.self kf.mem hsf, ?_⟩
  rw [x4f, Ie.x19]

/-- The pipelined loop: windows `1 … J - 2`, each selecting the next one's entry. -/
theorem combJP2Loop_ok {arithmetic : Mod → List FOp → Prog isa} {mc : List Instr} {K : TCombCfg} {C : Curve}
    {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb)
    {X : List Reg} (hcompiler : FieldCompilerOn K.M C X arithmetic size)
    (hX : ∀ r ∈ X, r ∈ tcombClob K.M.n ∧ r ≠ .x19) (hJenc : K.J<4096) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax) {s₀ : State}
    (hF : TCombFixed K C base size s₀ k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl))
    (hblk : arithmetic K.M (maddJ K.S K.A K.E K.D) = .block mc) (hck : JPChecks2 K size mc) {s : State}
    (hI : TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s 1)
    (E : TEntryPostJ K C base size k 1 s s) :
    WP isa (.loop (K.stepJP2 mc) (.nonzero .x .x4)) s fun s' =>
      TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (K.J - 1) ∧
      TEntryPostJ K C base size k (K.J - 1) s' s' := by
  have hJ3 := hck.J3
  refine WP.loop (M:=isa) (fun r s' => 1≤r ∧ r≤K.J-2 ∧
    TCombJInv K C base size k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl) s₀ s' (K.J-1-r) ∧
    TEntryPostJ K C base size k (K.J-1-r) s' s')
    (fun r s' ⟨hr,hrJ,hi,he⟩ => ?_) (K.J-2) s
    ⟨by omega_arith,by omega_arith,by simpa [show K.J-1-(K.J-2)=1 by omega_arith] using hI,
      by simpa [show K.J-1-(K.J-2)=1 by omega_arith] using E⟩
  refine WP.mono (stepJP2_ok hL hA hcompiler hX hJenc hC hM3 hG hV hpn hb1 hB hk hF hblk hck
    (j:=K.J-1-r) (by omega_arith) (by omega_arith) hi he) fun t ⟨ht,et,hx⟩ => ?_
  obtain hz : (t.read .x .x4 != 0)=decide (r-1≠0) := by
    rw [read_x,hx]
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne,decide_eq_true_eq,ne_eq,BitVec.sub_eq_iff_eq_add]
    obtain eqn : BitVec.ofNat 64 (K.J-1-r+1)=BitVec.ofNat 64 (K.J-1) ↔ K.J-1-r+1=K.J-1 := by
      constructor
      · intro h
        have := congrArg BitVec.toNat h
        simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_arith : K.J-1-r+1<2^64),
          Nat.mod_eq_of_lt (by omega_arith : K.J-1<2^64)] using this
      · exact congrArg (BitVec.ofNat 64)
    change (¬BitVec.ofNat 64 (K.J-1-r+1) = (0#64) + BitVec.ofNat 64 (K.J-1)) ↔ ¬r-1=0
    rw [BitVec.zero_add, eqn]
    omega_arith
  by_cases hr1 : r-1=0
  · refine Or.inl ⟨?_,?_,?_⟩
    · show some (t.read .x .x4 != 0)=some false
      rw [hz,hr1]; rfl
    · simpa only [show K.J-1-r+1=K.J-1 by omega_arith] using ht
    · simpa only [show K.J-1-r+1=K.J-1 by omega_arith] using et
  · refine Or.inr ⟨?_,r-1,by omega_arith,by omega_arith,by omega_arith,?_,?_⟩
    · show some (t.read .x .x4 != 0)=some true
      rw [hz,decide_eq_true hr1]
    · simpa only [show K.J-1-(r-1)=K.J-1-r+1 by omega_arith] using ht
    · simpa only [show K.J-1-(r-1)=K.J-1-r+1 by omega_arith] using et

/-- The pipelined comb computes `[k]G`. -/
theorem tcombJP2_ok {arithmetic : Mod → List FOp → Prog isa} {mc : List Instr} {K : TCombCfg} {C : Curve}
    {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb)
    {X : List Reg} (hcompiler : FieldCompilerOn K.M C X arithmetic size)
    (hX : ∀ r ∈ X, r ∈ tcombClob K.M.n ∧ r ≠ .x19) (hJenc : K.J<4096) (hC : Law C) (hM3 : AM3 C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl) (hpn : C.p < 2 ^ (64 * K.M.n))
    (hb1 : 1 ≤ K.bits) {kmax : Nat} (hB : BoothOk C K.w K.J kmax) (hk : k < kmax)
    (hblk : arithmetic K.M (maddJ K.S K.A K.E K.D) = .block mc) (hck : JPChecks2 K size mc) {s : State}
    (hs : Scr s base size) (hM : ModOkA K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2 ^ (64 * K.M.n)) C.p tbl)) :
    WP isa (K.combJP2 arithmetic mc) s fun s' => KeepRegs (tcombClob K.M.n) s s' ∧
      Unch base (tcombW K) s.mem s'.mem ∧ ModOkA K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.A.x, K.A.y, K.A.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.A.x) (tmv C K.M.n base s' K.A.y) (tmv C K.M.n base s' K.A.z)
        (mul k (G C)) := by
  have hJ3 := hck.J3
  obtain hle : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ size := fun x hx => hL.comb.lay.le x hx
  unfold TCombCfg.combJP2
  refine WP.seq (WP.mono (firstJ_ok hL hA hC hG hV hpn hb1 hs hM hF) fun s₁ I₁ => ?_)
  obtain hz : wordsVal s₁.mem base K.zero K.M.n = 0 := by
    rw [I₁.unch.wordsVal (tcombW_ro hL (x := K.zero) (by simp [combRo, TCombCfg.toComb]))
      (by have := hle K.zero (by tcomb_mem); have := I₁.scr.nowrap; omega_arith), hF.zero]
  refine WP.seq (tentryJ_ok hL hA hC hV hpn I₁.scr I₁.mod (i := 1) (by omega_arith) I₁.x19 hb1 (c := true)
    (Or.inl ⟨rfl, Nat.le_refl _⟩) I₁.bits hz I₁.tsym I₁.tbl hF.out fun s₂ E₂ sy₂ => ?_)
  obtain I₂ := I₁.after_entry hL hF E₂ sy₂
  refine WP.seq (WP.mono (combJP2Loop_ok hL hA hcompiler hX hJenc hC hM3 hG hV hpn hb1 hB hk hF hblk hck I₂
    (E₂.self rfl E₂.scr)) fun s₃ ⟨I₃, E₃⟩ => ?_)
  obtain hT := tailJ_ok hL hA hcompiler hX hJenc hC hM3 hG hV hb1 hB hk hF (j := K.J - 1) (by omega_arith)
    (by omega_arith) I₃ E₃ rfl
  rw [hblk] at hT
  refine WP.seq (WP.mono hT fun s₄ ⟨I₄, _⟩ => ?_)
  rw [show K.J - 1 + 1 = K.J by omega_arith] at I₄
  exact tcombJOut_ok hL hA hcompiler hX hJenc hC hV hpn hB hk hs hM hF I₄

end VG.Proof.Weierstrass.AArch64
