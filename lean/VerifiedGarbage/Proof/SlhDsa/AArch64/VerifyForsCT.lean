module

-- separate module: a stage of forsPk's proof, rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyForsMain
public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyForsCTBase
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsPk` is constant time

Two runs of `forsPk` from states of its precondition that agree on its
public data, which include the digest and so the FORS indices, leak the
same trace (`forsPk_ct`). Each run keeps the facts of its own correctness
(with the indices `I` of the first run, which are the second's too); the
registers the taint analysis needs public hold the same values in both,
functions of the indices and of the counters: so do the conditions of the
branches and loops.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.ForsPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase (relSeq relLoop wpLoop)
open VG.Proof.SlhDsa.AArch64.Fors (Agree As)
open VG.Proof.MlKem.AArch64 (Only Keep)

variable {p : Params}

/-- `FK` with other indices that agree on the trees. -/
theorem FK.ofI {σ : State} {S sig : Addr} {pk a : List Byte} {I I' : Nat → Nat} {t : State}
    (h : FK p σ S sig pk a I t) (hI : ∀ i < p.k, I i = I' i) : FK p σ S sig pk a I' t :=
  ⟨h.x19, h.x20, h.x21, h.x28, h.sp, h.rd, h.wr, h.vcs, h.env, h.saved, fun i hi => by rw [h.fidx i hi, hI i hi],
    h.frame⟩

section
variable (hF : FP p) (hA : As p) {σ₁ σ₂ : State} {S sig : Addr} (c₁ : Ctx p σ₁ S sig) (c₂ : Ctx p σ₂ S sig)
  {pk₁ a₁ pk₂ a₂ : List Byte} {I : Nat → Nat} (hIa : ∀ i < p.k, I i < 2 ^ p.a)
  (hsp : σ₁.sp = σ₂.sp) (hkp : σ₁.gpr .x2 = σ₂.gpr .x2) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns}
  (ht : f.t4 = T.code)

/-! ## A height -/

include hA hsp in
theorem lane_rel {t₀ z : Nat} {X₁ X₂ : Nat → List Byte} {u₁ u₂ : State} {j : Nat} (hj : j < 4) :
    RelCT isa (fun a b => UP p σ₁ S sig pk₁ a₁ I t₀ z X₁ u₁ j a ∧ UP p σ₂ S sig pk₂ a₂ I t₀ z X₂ u₂ j b)
      (Impl.SlhDsa.AArch64.Verify.forsUpLane p j) fun _ _ => True :=
  ct_upLane hA hj fun x y ⟨hx, hy⟩ => ⟨by rw [hx.fk.sp, hy.fk.sp, hsp], fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [hx.fk.x19, hy.fk.x19]
    · rw [hx.fk.x21, hy.fk.x21]
    · rw [hx.x22, hy.x22]
    · rw [hx.x23, hy.x23]
    · rw [(hx.todo j hj (Nat.le_refl _)).idx, (hy.todo j hj (Nat.le_refl _)).idx]⟩

theorem up0 {σ : State} {pk a : List Byte} {t₀ m : Nat} {u₀ u : State}
    (h : HI p σ S sig pk a I t₀ u₀ m u) :
    UP p σ S sig pk a I t₀ (p.a - m) (fun k' => rootZ p σ.mem sig pk a (σ.gpr .x2).toNat I (tOf p t₀ k') (p.a - m))
      u₀ 0 u :=
  ⟨h.2.2.1.fk, h.2.2.1.x22, h.2.2.2, h.2.2.1.frame, fun _ h' => absurd h' (by omega),
    fun k' hk _ => h.2.2.1.lanes k' hk⟩

include hF hA c₁ c₂ hIa hsp ht in
theorem up_rel {t₀ : Nat} (ht₀ : t₀ < 2 ^ 32) {u₁ u₂ : State} (m : Nat) :
    RelCT isa (fun a b => HI p σ₁ S sig pk₁ a₁ I t₀ u₁ m a ∧ HI p σ₂ S sig pk₂ a₂ I t₀ u₂ m b)
      (Impl.SlhDsa.AArch64.Verify.forsUp p f) fun _ _ => True := by
  have hn32 := hF.n32
  have hn8 := hF.n8
  by_cases hm : 1 ≤ m ∧ m ≤ p.a
  swap
  · exact RelCT.of_false fun a b ⟨h, _⟩ => hm ⟨h.1, h.2.1⟩
  have hz : p.a - m < p.a := by omega
  let X₁ := fun k' => rootZ p σ₁.mem sig pk₁ a₁ (σ₁.gpr .x2).toNat I (tOf p t₀ k') (p.a - m)
  let X₂ := fun k' => rootZ p σ₂.mem sig pk₂ a₂ (σ₂.gpr .x2).toNat I (tOf p t₀ k') (p.a - m)
  unfold Impl.SlhDsa.AArch64.Verify.forsUp
  refine RelCT.mono (P := fun a b => UP p σ₁ S sig pk₁ a₁ I t₀ (p.a - m) X₁ u₁ 0 a ∧
    UP p σ₂ S sig pk₂ a₂ I t₀ (p.a - m) X₂ u₂ 0 b) ?_ (fun a b ⟨ha, hb⟩ => ⟨up0 ha, up0 hb⟩) fun _ _ h => h
  refine relSeq (lane_rel hA hsp (by decide)) (fun a h => upStep hF c₁ hIa ht₀ hz (by decide) h)
    (fun b h => upStep hF c₂ hIa ht₀ hz (by decide) h) ?_
  refine relSeq (lane_rel hA hsp (by decide)) (fun a h => upStep hF c₁ hIa ht₀ hz (by decide) h)
    (fun b h => upStep hF c₂ hIa ht₀ hz (by decide) h) ?_
  refine relSeq (lane_rel hA hsp (by decide)) (fun a h => upStep hF c₁ hIa ht₀ hz (by decide) h)
    (fun b h => upStep hF c₂ hIa ht₀ hz (by decide) h) ?_
  refine relSeq (lane_rel hA hsp (by decide)) (fun a h => upStep hF c₁ hIa ht₀ hz (by decide) h)
    (fun b h => upStep hF c₂ hIa ht₀ hz (by decide) h) ?_
  rw [ht]
  refine relSeq (B₁ := fun w => w.sp = σ₁.sp) (B₂ := fun w => w.sp = σ₂.sp)
    (Fors.tcall_ct T f.t4name ⟨p.n, p.len⟩ rfl hn32 (fun h => ct_argsH hA h) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by simp only [Layout.strideA]; omega) (by simp only [Layout.strideA]; omega) c₁.fit
      (fun a h => ⟨h.fk.x19, by rw [h.fk.wr]; exact c₁.scr⟩) (fun b h => ⟨h.fk.x19, by rw [h.fk.wr]; exact c₂.scr⟩)
      fun a b ha hb => by rw [ha.fk.sp, hb.fk.sp, hsp])
    (fun a h => WP.mono (Fors.tcall_wp T f.t4name ⟨p.n, p.len⟩ rfl hn32 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by simp only [Layout.strideA]; omega) (by simp only [Layout.strideA]; omega) h.fk.x19
      (by rw [h.fk.wr]; exact c₁.scr) c₁.fit) fun w hw => by rw [hw.1, h.fk.sp])
    (fun b h => WP.mono (Fors.tcall_wp T f.t4name ⟨p.n, p.len⟩ rfl hn32 (by decide) (by decide) (by decide)
      (by omega) (by omega) (by simp only [Layout.strideA]; omega) (by simp only [Layout.strideA]; omega) h.fk.x19
      (by rw [h.fk.wr]; exact c₂.scr) c₂.fit) fun w hw => by rw [hw.1, h.fk.sp]) ?_
  exact ct_utail hA fun x y ⟨hx, hy⟩ => ⟨by rw [hx, hy, hsp], fun _ h => absurd h List.not_mem_nil⟩

include hF hA c₁ c₂ hIa hsp ht in
theorem heights_rel {t₀ : Nat} (ht₀ : t₀ < 2 ^ 32) {u₁ u₂ : State} :
    RelCT isa (fun a b => HI p σ₁ S sig pk₁ a₁ I t₀ u₁ p.a a ∧ HI p σ₂ S sig pk₂ a₂ I t₀ u₂ p.a b)
      (.loop (Impl.SlhDsa.AArch64.Verify.forsUp p f) (.nonzero .x .x9)) fun a b =>
      GS p σ₁ S sig pk₁ a₁ I t₀ p.a (fun k' => rootZ p σ₁.mem sig pk₁ a₁ (σ₁.gpr .x2).toNat I (tOf p t₀ k') p.a) u₁ a ∧
      GS p σ₂ S sig pk₂ a₂ I t₀ p.a (fun k' => rootZ p σ₂.mem sig pk₂ a₂ (σ₂.gpr .x2).toNat I (tOf p t₀ k') p.a) u₂ b :=
  relLoop (fun m => decide (m ≠ 1)) (· - 1) (up_rel hF hA c₁ c₂ hIa hsp T ht ht₀)
    (heights_step hF c₁ hIa T ht ht₀) (heights_step hF c₂ hIa T ht ht₀) p.a

/-- The start of the heights. -/
theorem heights_start {σ : State} {S sig : Addr} {pk a : List Byte} {t₀ : Nat} {u t : State}
    (hF : FP p) (hg : GS p σ S sig pk a I t₀ 0 (fun k' => F p pk (adrsOf a 3 (σ.gpr .x2).toNat 0 (lOf p I t₀ k'))
      (skOf p σ.mem sig t₀ k')) u t) :
    WP isa (.block [.movz .x .x23 0 0]) t (HI p σ S sig pk a I t₀ u p.a) := by
  refine MlKem.AArch64.wp_movz fun t₂ o₂ e₂ => WP.block_nil ⟨hF.a1, Nat.le_refl _, ?_, ?_⟩
  · rw [Nat.sub_self]
    exact ⟨hg.fk.keep hF o₂.keep (by decide) (by decide) (by decide) (by decide) (by rw [o₂.mem]; exact Frame.refl _ _),
      by rw [o₂.get .x22, hg.x22], fun k' hk' => ⟨by rw [o₂.get _ (fun h => idx_ne' k' hk' .x23 (by decide)
        (List.mem_singleton.mpr (List.mem_singleton.mp h).symm)), (hg.lanes k' hk').idx],
        by rw [o₂.mem, (hg.lanes k' hk').fld], by rw [o₂.mem, (hg.lanes k' hk').msg]; rfl⟩,
      by rw [o₂.mem]; exact hg.frame⟩
  · rw [e₂, Nat.sub_self]; rfl

include hF hA c₁ c₂ hIa hsp hkp ht in
theorem leaves_rel {t₀ : Nat} (ht₀ : t₀ < 2 ^ 32) :
    RelCT isa (fun a b => GP p σ₁ S sig pk₁ a₁ I t₀ a ∧ GP p σ₂ S sig pk₂ a₂ I t₀ b)
      (Impl.SlhDsa.AArch64.Verify.forsLeaves p f) fun _ _ => True := by
  have hn32 := hF.n32
  have hn8 := hF.n8
  unfold Impl.SlhDsa.AArch64.Verify.forsLeaves
  refine relSeq (B₁ := fun u => FK p σ₁ S sig pk₁ a₁ I u) (B₂ := fun u => FK p σ₂ S sig pk₂ a₂ I u)
    (ct_leaves hA fun x y ⟨hx, hy⟩ => ⟨by rw [hx.fk.sp, hy.fk.sp, hsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hx.fk.x19, hy.fk.x19]
      · rw [hx.fk.x20, hy.fk.x20, hkp]
      · rw [hx.fk.x21, hy.fk.x21]
      · rw [hx.x22, hy.x22]⟩)
    (fun a h => WP.mono (leavesBlock_ok hF c₁ hIa ht₀ h.fk h.x22) fun _ h' => h'.1)
    (fun b h => WP.mono (leavesBlock_ok hF c₂ hIa ht₀ h.fk h.x22) fun _ h' => h'.1) ?_
  rw [ht]
  exact Fors.tcall_ct T f.t4name ⟨p.n, p.len⟩ rfl hn32 (fun h => Fors.ct_argsA hF.sz hA h) (by decide) (by decide)
    (by decide) (by omega) (by omega) (by simp only [Layout.strideA]; omega) (by simp only [Layout.strideA]; omega)
    c₁.fit (fun a h => ⟨h.x19, by rw [h.wr]; exact c₁.scr⟩) (fun b h => ⟨h.x19, by rw [h.wr]; exact c₂.scr⟩)
    fun a b ha hb => by rw [ha.sp, hb.sp, hsp]

include hF hA c₁ c₂ hIa hsp hkp ht in
theorem group_rel (t₀ : Nat) :
    RelCT isa (fun a b => GP p σ₁ S sig pk₁ a₁ I t₀ a ∧ GP p σ₂ S sig pk₂ a₂ I t₀ b)
      (Impl.SlhDsa.AArch64.Verify.forsGroup p f) fun _ _ => True := by
  by_cases hk : t₀ < p.k
  swap
  · exact RelCT.of_false fun a b ⟨h, _⟩ => hk h.lt
  have ht₀ : t₀ < 2 ^ 32 := by have := hF.k; omega
  unfold Impl.SlhDsa.AArch64.Verify.forsGroup
  refine relSeq (B₁ := fun t => ∃ u, GP p σ₁ S sig pk₁ a₁ I t₀ u ∧ GS p σ₁ S sig pk₁ a₁ I t₀ 0
      (fun k' => F p pk₁ (adrsOf a₁ 3 (σ₁.gpr .x2).toNat 0 (lOf p I t₀ k')) (skOf p σ₁.mem sig t₀ k')) u t)
    (B₂ := fun t => ∃ u, GP p σ₂ S sig pk₂ a₂ I t₀ u ∧ GS p σ₂ S sig pk₂ a₂ I t₀ 0
      (fun k' => F p pk₂ (adrsOf a₂ 3 (σ₂.gpr .x2).toNat 0 (lOf p I t₀ k')) (skOf p σ₂.mem sig t₀ k')) u t)
    (leaves_rel hF hA c₁ c₂ hIa hsp hkp T ht ht₀)
    (fun a h => WP.mono (forsLeaves_ok hF c₁ hIa T ht ht₀ h.fk h.x22) fun t h' => ⟨a, h, h'.1⟩)
    (fun b h => WP.mono (forsLeaves_ok hF c₂ hIa T ht ht₀ h.fk h.x22) fun t h' => ⟨b, h, h'.1⟩) ?_
  refine RelCT.mono (P := fun a b => ∃ u₁ u₂, (GP p σ₁ S sig pk₁ a₁ I t₀ u₁ ∧ GS p σ₁ S sig pk₁ a₁ I t₀ 0
      (fun k' => F p pk₁ (adrsOf a₁ 3 (σ₁.gpr .x2).toNat 0 (lOf p I t₀ k')) (skOf p σ₁.mem sig t₀ k')) u₁ a) ∧
      (GP p σ₂ S sig pk₂ a₂ I t₀ u₂ ∧ GS p σ₂ S sig pk₂ a₂ I t₀ 0
      (fun k' => F p pk₂ (adrsOf a₂ 3 (σ₂.gpr .x2).toNat 0 (lOf p I t₀ k')) (skOf p σ₂.mem sig t₀ k')) u₂ b))
    ?_ (fun a b ⟨⟨u₁, h₁⟩, ⟨u₂, h₂⟩⟩ => ⟨u₁, u₂, h₁, h₂⟩) fun _ _ h => h
  refine RelCT.exists_ fun u₁ => RelCT.exists_ fun u₂ => ?_
  refine relSeq (ct_x23 fun x y ⟨hx, hy⟩ => ⟨by rw [hx.2.fk.sp, hy.2.fk.sp, hsp], fun _ h => absurd h List.not_mem_nil⟩)
    (fun a h => heights_start hF h.2) (fun b h => heights_start hF h.2) ?_
  refine relSeq (RelCT.mono (heights_rel hF hA c₁ c₂ hIa hsp T ht ht₀) (fun _ _ h => h) fun _ _ _ => trivial)
    (fun a h => wpLoop _ _ (heights_step hF c₁ hIa T ht ht₀) _ h)
    (fun b h => wpLoop _ _ (heights_step hF c₂ hIa T ht ht₀) _ h) ?_
  exact ct_roots hA fun x y ⟨hx, hy⟩ => ⟨by rw [hx.fk.sp, hy.fk.sp, hsp], fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.fk.x19, hy.fk.x19]
    · rw [hx.x22, hy.x22]⟩

end

end VG.Proof.SlhDsa.AArch64.ForsPk
