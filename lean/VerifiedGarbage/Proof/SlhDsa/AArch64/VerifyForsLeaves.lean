module

-- separate module: a stage of forsPk's proof, rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyForsLane
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `forsPk`: a group's leaves

The state of a group at a height (`GS`), and the group's leaves
(`forsLeaves_ok`): each lane's message the `F` of its tree's private key
value, its fields those of its leaf.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.ForsPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase (in_scr in_scr' disj_scr bytesAt_frame readW_frame)
open VG.Proof.MlKem.AArch64 (Only Keep)

variable {p : Params}

/-- A group from `t₀` at height `z`, from the group's start `u₀`: each lane's
node `X k`, its index `⌊L / 2^z⌋`. -/
structure GS (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (I : Nat → Nat) (t₀ z : Nat)
    (X : Nat → List Byte) (u₀ t : State) : Prop where
  fk : FK p σ S sig pk a I t
  x22 : t.gpr .x22 = BitVec.ofNat 64 t₀
  lanes : ∀ k' < 4, Lane p S (σ.gpr .x2).toNat z (lOf p I t₀ k' / 2 ^ z) (X k') t k'
  frame : Frame (gwL p S) u₀.mem t.mem

/-- The fields of the lanes `A` past a call of `thash4` on them. -/
theorem fld_acall (hF : FP p) {m m' : Mem} {S : Addr} (hf : Frame (Wots4.t4ch p.n S Layout.oA Layout.strideA) m m')
    {j : Nat} (hj : j < 4) :
    bytesAt m' (at' S (Layout.laneA j + p.n + 16)) 16 = bytesAt m (at' S (Layout.laneA j + p.n + 16)) 16 := by
  have hn := hF.n32
  refine bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [Wots4.t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
  rcases hr with ⟨i, hi, rfl⟩ | rfl
  · simp only [laneA_eq, Layout.oA, Layout.strideA]
    exact disj_scr S (by omega) (by omega) (by omega)
  · have := disj_scr (o := Layout.laneA j + p.n + 16) (l := 16) (o' := 0) (l' := workUsed) S
      (by rw [laneA_eq]; simp only [workUsed]; omega) (by rw [laneA_eq]; omega) (by simp only [workUsed]; omega)
    simpa using this

/-- The registers the leaves' block may change. -/
abbrev allR : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x24, .x25, .x26, .x27]

theorem laneRegs_allR : ∀ j < 4, ∀ r ∈ laneRegs j, r ∈ allR := by decide

theorem idx_notin : ∀ k' < 4, ∀ j < 4, k' ≠ j → Impl.SlhDsa.AArch64.Verify.idxReg k' ∉ laneRegs j := by decide

theorem leavesBlock_ok (hF : FP p) {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {pk a : List Byte}
    {I : Nat → Nat} (hIa : ∀ i < p.k, I i < 2 ^ p.a)     {t₀ : Nat} (ht₀ : t₀ < 2 ^ 32) {t : State} (hK : FK p σ S sig pk a I t)
    (h22 : t.gpr .x22 = BitVec.ofNat 64 t₀) :
    WP isa (.block ((List.range 4).flatMap (leafL p))) t fun u => FK p σ S sig pk a I u ∧ Keep allR t u ∧
      Frame (gwL p S) t.mem u.mem ∧
      ∀ k' < 4, Lane p S (σ.gpr .x2).toNat 0 (lOf p I t₀ k') (skOf p σ.mem sig t₀ k') u k' := by
  have hn32 := hF.n32
  have hn8 := hF.n8
  let P : Nat → State → Prop := fun j u => FK p σ S sig pk a I u ∧ Keep allR t u ∧ Frame (gwL p S) t.mem u.mem ∧
    ∀ k' < j, Lane p S (σ.gpr .x2).toNat 0 (lOf p I t₀ k') (skOf p σ.mem sig t₀ k') u k'
  rw [← List.append_nil (List.flatMap _ _)]
  refine Fors.wp_flatRange (f := leafL p) (P := P) 4 ⟨hK, Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
    (fun j hj u is' ⟨hu, ku, fu, lu⟩ k' => ?_) fun u h => WP.block_nil h
  · refine leafLane_ok hF c hIa hj ht₀ hu (by rw [ku.get .x22, h22]) fun u' k₁ f₁ l₁ => k' u' ⟨?_, ?_, ?_, ?_⟩
    · exact hu.keep hF k₁ (by rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide)
        (by rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide)
        (by rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide)
        (by rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide)
        (f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact tailA_gw S hj)
    · exact (ku.trans k₁).mono fun r hr => by
        rcases List.mem_append.mp hr with h | h
        · exact h
        · exact laneRegs_allR j hj r h
    · exact fu.trans (f₁.mono fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
    · intro i hi
      by_cases e : i = j
      · subst e; exact l₁
      · exact (lu i (by omega)).keep hn32 (by omega) hj e (k₁.get _ (idx_notin i (by omega) j hj e)) f₁

theorem forsLeaves_ok (hF : FP p) {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {pk a : List Byte}
    {I : Nat → Nat} (hIa : ∀ i < p.k, I i < 2 ^ p.a) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (ht : f.t4 = T.code) {t₀ : Nat} (ht₀ : t₀ < 2 ^ 32) {t : State} (hK : FK p σ S sig pk a I t)
    (h22 : t.gpr .x22 = BitVec.ofNat 64 t₀) :
    WP isa (Impl.SlhDsa.AArch64.Verify.forsLeaves p f) t fun t' =>
      GS p σ S sig pk a I t₀ 0 (fun k' => F p pk (adrsOf a 3 (σ.gpr .x2).toNat 0 (lOf p I t₀ k'))
        (skOf p σ.mem sig t₀ k')) t t' ∧ t'.gpr .x23 = t.gpr .x23 := by
  have hn32 := hF.n32
  have hn8 := hF.n8
  unfold Impl.SlhDsa.AArch64.Verify.forsLeaves
  refine WP.seq (WP.mono (leavesBlock_ok hF c hIa ht₀ hK h22) fun u ⟨hu, ku, fu, lu⟩ => ?_)
  rw [ht]
  refine acall_ok hF.sz T f.t4name (len := 2 * p.n + 32) (by omega) (by omega) (by omega) hu.x19
    (by rw [hu.wr]; exact c.scr) c.fit fun u' hc => ⟨⟨hu.acall hF hc, by rw [hc.cs _ (by decide) (by decide),
      ku.get .x22, h22], fun k' hk' => ⟨?_, ?_, ?_⟩, fu.trans ((hc.frame.sub (t4ch_gw hF S)))⟩, ?_⟩
  · rw [hc.cs _ (idxReg_cs k' hk').1 (idxReg_cs k' hk').2.1, (lu k' hk').idx, Nat.pow_zero, Nat.div_one]
  · rw [fld_acall hF hc.frame hk', (lu k' hk').fld, Nat.pow_zero, Nat.div_one]
  · rw [hc.out k' hk', show 2 * p.n + 32 = p.n + 32 + p.n by omega, lane_msg hu.env hk' (lu k' hk').fld (lu k' hk').msg]
    simp only [F, hF.sz.shake, shakeAdrs, adrsOf, ufld, List.append_assoc]
  · rw [hc.cs _ (by decide) (by decide), ku.get .x23]

end VG.Proof.SlhDsa.AArch64.ForsPk
