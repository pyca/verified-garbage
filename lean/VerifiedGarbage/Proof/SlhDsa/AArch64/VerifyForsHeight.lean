module

-- separate module: a stage of forsPk's proof, rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyForsUp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `forsPk`: a height of a group

`forsUp` at height `z` (`forsUp_ok`): the four lanes (`upStep`), then
`thash4` on the lanes `A`, each lane's node the `H` of its message.
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

/-- A lane done at height `z`: its message `Y` for `H`. -/
structure LU (p : Params) (S : Addr) (kp z L : Nat) (Y : List Byte) (t : State) (k' : Nat) : Prop where
  idx : t.gpr (Impl.SlhDsa.AArch64.Verify.idxReg k') = BitVec.ofNat 64 (L / 2 ^ (z + 1))
  fld : bytesAt t.mem (at' S (Layout.laneA k' + p.n + 16)) 16 = ufld 3 kp (z + 1) (L / 2 ^ (z + 1))
  msg : bytesAt t.mem (at' S (Layout.laneA k' + p.n + 32)) (2 * p.n) = Y

theorem LU.keep {S : Addr} {kp z L : Nat} {Y : List Byte} {t t' : State} {j k : Nat} (hn : p.n ≤ 32)
    (h : LU p S kp z L Y t j) (hj : j < 4) (hk : k < 4) (hjk : j ≠ k)
    (hr : t'.gpr (Impl.SlhDsa.AArch64.Verify.idxReg j) = t.gpr (Impl.SlhDsa.AArch64.Verify.idxReg j))
    (hf : Frame [tailA p S k] t.mem t'.mem) : LU p S kp z L Y t' j := by
  have := ForsPk.laneA_eq j
  have := ForsPk.laneA_eq k
  refine ⟨by rw [hr, h.idx], ?_, ?_⟩
  · rw [k1 hf (by simp only [Layout.strideA]; omega) (by omega) (by simp only [Layout.strideA]; omega), h.fld]
  · rw [k1 hf (by simp only [Layout.strideA]; omega) (by omega) (by simp only [Layout.strideA]; omega), h.msg]

/-- Lane `k`'s message at height `z`, from its node `X`. -/
abbrev yOf (p : Params) (m : Mem) (sig : Addr) (I : Nat → Nat) (t₀ z k' : Nat) (X : List Byte) : List Byte :=
  if lOf p I t₀ k' / 2 ^ z % 2 = 0 then X ++ authOf p m sig t₀ k' z else authOf p m sig t₀ k' z ++ X

/-- After the first `j` lanes of height `z`. -/
structure UP (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (I : Nat → Nat) (t₀ z : Nat)
    (X : Nat → List Byte) (u₀ : State) (j : Nat) (u : State) : Prop where
  fk : FK p σ S sig pk a I u
  x22 : u.gpr .x22 = BitVec.ofNat 64 t₀
  x23 : u.gpr .x23 = BitVec.ofNat 64 z
  frame : Frame (gwL p S) u₀.mem u.mem
  done : ∀ k' < j, LU p S (σ.gpr .x2).toNat z (lOf p I t₀ k') (yOf p σ.mem sig I t₀ z k' (X k')) u k'
  todo : ∀ k' < 4, j ≤ k' → Lane p S (σ.gpr .x2).toNat z (lOf p I t₀ k' / 2 ^ z) (X k') u k'

theorem upStep (hF : FP p) {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {pk a : List Byte}
    {I : Nat → Nat} (hIa : ∀ i < p.k, I i < 2 ^ p.a) {t₀ z : Nat} (ht₀ : t₀ < 2 ^ 32) (hz : z < p.a)
    {X : Nat → List Byte} {u₀ : State} {j : Nat} (hj : j < 4) {u : State}
    (h : UP p σ S sig pk a I t₀ z X u₀ j u) :
    WP isa (Impl.SlhDsa.AArch64.Verify.forsUpLane p j) u (UP p σ S sig pk a I t₀ z X u₀ (j + 1)) := by
  have hn32 := hF.n32
  have hjc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  refine WP.mono (upLane_ok hF c hIa hj ht₀ hz h.fk h.x22 h.x23 (h.todo j hj (Nat.le_refl _))) fun u' ul => ?_
  have ft : Frame (gw p S) u.mem u'.mem := ul.frame.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact tailA_gw S hj
  refine ⟨h.fk.keep hF ul.keep (by rcases hjc with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hjc with rfl | rfl | rfl | rfl <;> decide) (by rcases hjc with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hjc with rfl | rfl | rfl | rfl <;> decide) ft,
    by rw [ul.keep.get .x22 (by rcases hjc with rfl | rfl | rfl | rfl <;> decide), h.x22],
    by rw [ul.keep.get .x23 (by rcases hjc with rfl | rfl | rfl | rfl <;> decide), h.x23],
    h.frame.trans (ul.frame.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)), fun k' hk' => ?_,
    fun k' hk₄ hk' => (h.todo k' hk₄ (by omega)).keep hn32 hk₄ hj (by omega)
      (ul.keep.get _ (idx_notin k' hk₄ j hj (by omega))) ul.frame⟩
  by_cases e : k' = j
  · subst e; exact ⟨ul.idx, ul.fld, ul.msg⟩
  · exact (h.done k' (by omega)).keep hn32 (by omega) hj e (ul.keep.get _ (idx_notin k' (by omega) j hj e)) ul.frame

/-- `forsUp` at height `z`: each lane's node the `H` of its message. -/
theorem forsUp_ok (hF : FP p) {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {pk a : List Byte}
    {I : Nat → Nat} (hIa : ∀ i < p.k, I i < 2 ^ p.a) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (ht : f.t4 = T.code) {t₀ z : Nat} (ht₀ : t₀ < 2 ^ 32) (hz : z < p.a) {X : Nat → List Byte} {u₀ t : State}
    (hg : GS p σ S sig pk a I t₀ z X u₀ t) (h23 : t.gpr .x23 = BitVec.ofNat 64 z) :
    WP isa (Impl.SlhDsa.AArch64.Verify.forsUp p f) t fun t' =>
      GS p σ S sig pk a I t₀ (z + 1) (fun k' => H p pk (adrsOf a 3 (σ.gpr .x2).toNat (z + 1) (lOf p I t₀ k' / 2 ^ (z + 1)))
        (yOf p σ.mem sig I t₀ z k' (X k'))) u₀ t' ∧ t'.gpr .x23 = BitVec.ofNat 64 (z + 1) ∧
      t'.gpr .x9 = BitVec.ofNat 64 (z + 1) - BitVec.ofNat 64 p.a := by
  have hn32 := hF.n32
  have hn8 := hF.n8
  have u0 : UP p σ S sig pk a I t₀ z X u₀ 0 t :=
    ⟨hg.fk, hg.x22, h23, hg.frame, fun _ h => absurd h (by omega), fun k' hk _ => hg.lanes k' hk⟩
  unfold Impl.SlhDsa.AArch64.Verify.forsUp
  refine WP.seq (WP.mono (upStep hF c hIa ht₀ hz (by decide) u0) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (upStep hF c hIa ht₀ hz (by decide) h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (upStep hF c hIa ht₀ hz (by decide) h₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (upStep hF c hIa ht₀ hz (by decide) h₃) fun t₄ h₄ => ?_)
  refine WP.seq ?_
  rw [ht]
  refine acall_ok hF.sz T f.t4name (len := 3 * p.n + 32) (by omega) (by omega) (by omega) h₄.fk.x19
    (by rw [h₄.fk.wr]; exact c.scr) c.fit fun t₅ hc => ?_
  refine MlKem.AArch64.wp_addImm (by decide) fun t₆ o₆ e₆ => MlKem.AArch64.wp_subImm (by have := hF.a; omega)
    fun t₇ o₇ e₇ => WP.block_nil ?_
  have hm : t₇.mem = t₅.mem := by rw [o₇.mem, o₆.mem]
  have fk₅ := h₄.fk.acall hF hc
  have h23₅ : t₅.gpr .x23 = BitVec.ofNat 64 z := by rw [hc.cs _ (by decide) (by decide), h₄.x23]
  refine ⟨⟨fk₅.keep hF ((o₆.trans o₇).keep) (by decide) (by decide) (by decide) (by decide)
      (by rw [hm]; exact Frame.refl _ _), by rw [o₇.get .x22, o₆.get .x22, hc.cs _ (by decide) (by decide), h₄.x22],
    fun k' hk' => ⟨?_, ?_, ?_⟩, by rw [hm]; exact h₄.frame.trans (hc.frame.sub (t4ch_gw hF S))⟩, ?_, ?_⟩
  · rw [o₇.get _ (by rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;> decide),
      o₆.get _ (by rcases (show k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 by omega) with rfl | rfl | rfl | rfl <;> decide),
      hc.cs _ (idxReg_cs k' hk').1 (idxReg_cs k' hk').2.1, (h₄.done k' hk').idx]
  · rw [hm, fld_acall hF hc.frame hk', (h₄.done k' hk').fld]
  · rw [hm, hc.out k' hk', show 3 * p.n + 32 = p.n + 32 + 2 * p.n by omega,
      lane_msg h₄.fk.env hk' (h₄.done k' hk').fld (h₄.done k' hk').msg]
    simp only [H, hF.sz.shake, shakeAdrs, adrsOf, ufld, List.append_assoc]
  · rw [o₇.get .x23, e₆, h23₅, BitVec.ofNat_add_ofNat]
  · rw [e₇, e₆, h23₅, BitVec.ofNat_add_ofNat]

end VG.Proof.SlhDsa.AArch64.ForsPk
