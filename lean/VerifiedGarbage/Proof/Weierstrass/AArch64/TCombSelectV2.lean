module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
public import VerifiedGarbage.Impl.Weierstrass.AArch64.TCombJ
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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
    have e1 : s₁.v ((selA c).acc.getD k .v0) = s.v ((selA c).acc.getD k .v0) :=
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
  have hc : K.M.n / 2 ≤ 4 := by omega_using [hn6]
  have hn16 : 16 * (K.M.n / 2) = 8 * K.M.n := by omega_using [hn2]
  unfold TCombCfg.selPass2
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (passV_ok K (tb := .x30) (o := 0) (c := K.M.n / 2) hc (by omega_using [hn16]) (by decide)
    ha hH2 hH hHlt h18 h19 h28 (tbl_region hreg (by omega_using [hn16])))
    fun s₁ ⟨v₁, a18, a19, a28, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (keepMovs_ok (c := K.M.n / 2) (s := s₁) hn6 _ (Nat.le_refl _)) fun s₂ ⟨v₂, k₂⟩ => ?_
  have hsub : ∀ r ∈ (List.range (K.M.n / 2)).map fun i => selKeep.getD i .v3, r ∈ selKeep :=
    map_range_sub fun i hi =>
      (by decide : ∀ i < 3, selKeep.getD i .v3 ∈ selKeep) i (by omega_using [hi, hn6])
  have k₁₂ : VKeep [] ((selA (K.M.n / 2)).wr ++ (selB (K.M.n / 2)).wr ++ selKeep) s s₂ :=
    (k₁.mono (fun _ h => h) fun _ h => List.mem_append_left _ h).trans
      (k₂.mono (fun _ h => h) fun r h => List.mem_append_right _ (hsub r h))
  have ko : ∀ r ∈ [VReg.v16, .v18, .v19, .v20, .v28], s₂.v r = s₁.v r := fun r hr =>
    k₂.v _ (not_mem_map_range fun i hi e => selKeep_o _ hn6 i hi (by rw [e]; exact hr))
  have hreg₂ : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x30) (16 * K.M.n * K.H) := by
    rw [k₁₂.rd, k₁₂.wr, k₁₂.gpr _ List.not_mem_nil]; exact hreg
  refine WP.mono (passV_ok K (tb := .x30) (o := 8 * K.M.n) (c := K.M.n / 2) hc (by omega_using [hn16])
    (by omega_using [hn2]) ha hH2 hH hHlt (by rw [ko _ (by simp), a18, h18]) (by rw [ko _ (by simp), a19, h19])
    (by rw [ko _ (by simp), a28, h28]) (tbl_region hreg₂ (by omega_using [hn16])))
    fun t ⟨v₃, b18, b19, b28, k₃⟩ => ?_
  have eL : ∀ o i, ldE K.M.n o s₂ a i .x30 = ldE K.M.n o s a i .x30 := fun o i => by
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
  have hc : K.M.n / 2 ≤ 4 := by omega_using [hn6]
  iterate 2 rw [WP.block_append_iff]
  refine WP.mono (selOneV_ok K.one (c := K.M.n / 2) (h := 0) (k := K.M.n / 2) hc (by omega_using []) ha64
    h19) fun s₂ ⟨f₂, k₂⟩ => ?_
  have K02 : Keeps [.x6] s s₂ := k₂.keeps
  have hs₂ : Scr s₂ base size := hs.of_keeps K02 (by decide)
  refine WP.mono (qstoresV_ok (fun i => selKeep.getD i .v3) hs₂ hE16.1 (K.M.n / 2)
    (by omega_using [hEx, hn2])) fun s₃ ⟨w₃, kr₃, v₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs kr₃ (by decide)
  refine WP.mono (qstoresV_ok (fun i => (selA (K.M.n / 2)).acc.getD (0 + i) .v0) hs₃ hE16.2
    (K.M.n / 2) (by omega_using [hEy, hn2])) fun t ⟨w₄, kr₄, v₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs kr₄ (by decide)
  have hn16 : 16 * (K.M.n / 2) = 8 * K.M.n := by omega_using [hn2]
  rw [hn16] at O₃ O₄
  have vx : ∀ i < K.M.n / 2, s₂.v (selKeep.getD i .v3) = if 1 ≤ a then ldE K.M.n 0 r a i tb else 0 :=
    fun i hi => by
      have ho := selKeep_o _ hn6 i hi
      rw [k₂.v _ (by
        simp only [List.mem_cons, not_or]
        exact ⟨fun e => ho (by rw [e]; simp), fun e => ho (by rw [e]; simp),
          not_mem_map_range fun i' hi' e => selKeep_acc _ hn6 i hi _ (by omega_using [hi']) e.symm⟩),
        hkx i hi]
  have vy : ∀ i < K.M.n / 2, s₂.v ((selA (K.M.n / 2)).acc.getD (0 + i) .v0) =
      if 1 ≤ a then ldE K.M.n (8 * K.M.n) r a i tb
      else ofVDwords (wordOf K.one (2 * i)) (wordOf K.one (2 * i + 1)) := fun i hi => by
    rw [f₂ i hi, Nat.zero_add, hay i hi]
    by_cases h : 1 ≤ a
    · rw [ite_f (show ¬ a = 0 by omega_using [h]), ite_t h, ite_t h]
    · rw [ite_t (show a = 0 by omega_using [h]), ite_f h]
  have wx : ∀ j < K.M.n, word t.mem base (K.E.x + 8 * j) =
      if 1 ≤ a then word r.mem (r.gpr tb) (16 * K.M.n * (a - 1) + 8 * j) else 0 := fun j hj => by
    rw [O₄.word (by omega_using [axy, hj]) (by omega_using [hEx, hnw, hj]), w₃ j (by omega_using [hn16, hj]),
      vx _ (by omega_using [hn16, hj])]
    by_cases h : 1 ≤ a
    · rw [ite_t h, ite_t h, vdword_ldE _ _ _ _ _ (Nat.mod_lt _ (by decide)),
        show 16 * K.M.n * (a - 1) + 0 + 16 * (j / 2) + 8 * (j % 2) = 16 * K.M.n * (a - 1) + 8 * j by omega_using []]
    · rw [ite_f h, ite_f h, vdword_zero]
  have wy : ∀ j < K.M.n, word t.mem base (K.E.y + 8 * j) =
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
  have hEx := hE K.E.x (by simp)
  have hEy := hE K.E.y (by simp)
  have hEz := hE K.E.z (by simp)
  obtain ⟨axy, axz, ayz⟩ := hap
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zero7One5_ok s) fun s₁ ⟨e7, e5, k₁⟩ => ?_
  have hs₁ : Scr s₁ base size := hs.of_keeps k₁.keeps (by decide)
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (selXY2Fin_ok K hn6 hn2 hs₁ ha64 (r := r) (tb := tb) (by rw [k₁.v _ List.not_mem_nil, h19])
    (fun i hi => by rw [k₁.v _ List.not_mem_nil, hkx i hi])
    (fun i hi => by rw [k₁.v _ List.not_mem_nil, hay i hi]) hEx.1 hEy.1 hE16 axy hone)
    fun s₃ ⟨ex₃, ey₃, kk₃, U₃, hs₃⟩ => ?_
  have g₃ : ∀ q ∈ [Reg.x2, .x5, .x7], s₃.gpr q = s₁.gpr q := fun q hq => by
    have : q ≠ .x6 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> decide
    rw [kk₃.gpr q (by simpa using this)]
  rw [TCombCfg.selZ, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (selZ_carry s₃ ha64 (by rw [g₃ _ (by simp), k₁.gpr _ (by decide), hx2])
    (by rw [g₃ _ (by simp), e5])) fun s₄ ⟨c₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (zWords_ok K hs₄ (by rw [k₄.gpr _ (by decide), g₃ _ (by simp), e7]) hEz.1 hEz.2
    K.M.n (Nat.le_refl _)) fun t ⟨wt, _, kt, Ot⟩ => ?_
  have hm₄ : s₄.mem = s₃.mem := k₄.mem
  have b64 : ∀ d ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ 2 ^ 64 := fun d hd => by
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
    have hxy' : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n)], ofs base x < w.1 ∨ w.1 + w.2 ≤ ofs base x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hx.1, hx.2.1⟩
    rw [Ot x (by omega_using [hx]), hm₄, U₃ x hxy', k₁.mem]

end VG.Proof.Weierstrass.AArch64
