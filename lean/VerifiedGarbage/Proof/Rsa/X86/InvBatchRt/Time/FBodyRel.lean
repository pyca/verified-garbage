module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.FBatchRel
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.FBatchRel
meta import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2

/-! # The fused batched inverse in both runs, in `crt_values`' layout

`relBody`: its trace depends only on what `Pre0` makes public, as the batches' count, kept in
the header, is the same in both runs.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Impl.Rsa.X86.CrtValuesRt (lay)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)
open VG.Impl.Rsa.X86.Keys (seqs)

variable {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}

local notation "T2" => fun _ : Reg → BitVec 32 => True ∧ True

theorem checks₀ : BatchChecks lay 0 8 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨_, by taint_decide⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩⟩

theorem checks₈ : BatchChecks lay 8 0 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨_, by taint_decide⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩,
    ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩⟩

theorem relBatchF (F : Fits Z len) (h : Bool) :
    RelCT isa (Both lay B Z len N args sp C T2) (batchF lay h) (Both lay B Z len N args sp C T2) := by
  rw [VG.Proof.Rsa.X86.InvBatchRt.F.batchF_eq]
  cases h
  · exact relBatchCodeF F (.inr ⟨rfl, rfl⟩) checks₈
  · exact relBatchCodeF F (.inl ⟨rfl, rfl⟩) checks₀

/-- Two batches, then their count down by one. -/
theorem relDouble {k : Nat} (F : Fits Z len) (hk : 1 ≤ k) (hk32 : k < 2 ^ 32) :
    RelCT isa (Both lay B Z len N args sp (· = k) T2)
      (seqs [batchF lay true, batchF lay false,
        .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter]])
      (fun s t => Both lay B Z len N args sp (· = k - 1) T2 s t ∧
        s.zf = some (decide (k - 1 = 0)) ∧ t.zf = some (decide (k - 1 = 0))) := by
  simp only [seqs]
  exact RelCT.seq (relBatchF F true) (RelCT.seq (relBatchF F false) (relCountDown hk hk32 (by taint_decide)))

/-- The double batches, from the count `K`. -/
theorem relLoopF (F : Fits Z len) (K : Nat) :
    RelCT isa (fun s t => Both lay B Z len N args sp (· = K) T2 s t ∧ 1 ≤ K ∧ K < 2 ^ 32)
      (.loop (seqs [batchF lay true, batchF lay false,
        .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter]]) .ne)
      (Both lay B Z len N args sp (· = 0) T2) := by
  refine RelCT.loop (M := isa) (fun k s t => Both lay B Z len N args sp (· = k) T2 s t ∧
    1 ≤ k ∧ k < 2 ^ 32) (fun k => ?_) K
  by_cases hk : 1 ≤ k ∧ k < 2 ^ 32
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2
  refine (relDouble F hk.1 hk.2).mono (fun _ _ h => h.1) fun s t ⟨hb, zs, zt⟩ => ?_
  have es : isa.eval .ne s = s.zf.map (!·) := rfl
  have et : isa.eval .ne t = t.zf.map (!·) := rfl
  refine ⟨by rw [es, et, zs, zt], fun hf => ?_, fun ht => ⟨k - 1, by omega, hb, ?_, by omega⟩⟩
  · rw [es, zs] at hf
    have h0 : k - 1 = 0 := by by_contra h0; simp_all
    rw [h0] at hb
    exact hb
  · rw [es, zs] at ht
    by_contra h0
    simp_all

theorem relInitF (F : Fits Z len) :
    RelCT isa (fun s t => Pre0 lay B Z len N args sp s ∧ Pre0 lay B Z len N args sp t) (initF lay)
      (Both lay B Z len N args sp (· = (3 * nw len + 2) / 2) T2) := by
  have F1 := F.fit
  have F2 := F.two
  have r0 := rv_a len 0; have r2 := rv_a len 2; have r3 := rv_a len 3; have r7 := rv_a len 7
  have r8 := rv_a len 8; have r12 := rv_a len 12
  have r4 : rv (kw len) { arr := fgArr } = 160 + 4 * (8 * nw len + 8) := rv_a len 4
  have r11 : rv (kw len) { arr := deArr } = 160 + 11 * (8 * nw len + 8) := rv_a len 11
  have h21 := rv_half1' len 2; have h71 := rv_half1' len 7
  have f1 : fgSz * (nw len + 1) = 16 * (nw len + 1) := rfl
  have f2 : fgSz * (nw len + 2) = 16 * (nw len + 2) := rfl
  have d1 : deSz * (nw len + 1) = 20 * (nw len + 1) := rfl
  have d2 : deSz * (nw len + 2) = 20 * (nw len + 2) := rfl
  have efs : fgSz = 16 := rfl; have eds : deSz = 20 := rfl; have eP : sP = 176 := rfl
  unfold initF
  simp only [seqs]
  refine RelCT.seq (relSlots (by taint_decide)) ?_
  refine RelCT.seq (relCopy (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relVirtualize (stable_true _) F2 F1 (by taint_decide)) ?_
  refine RelCT.seq (relZeroWord (stable_true _) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relCopy (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relZeroWord (stable_true _) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relZeros (stable_true _) (fun _ hb => countN hb) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relEvenMask (stable_true _) (by taint_decide)) ?_
  refine RelCT.seq (relSelIn (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relChainAdd (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
    (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relScatter (by decide) (by omega) (by omega) (by omega) (by omega) ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relScatter (by decide) (by omega) (by omega) (by omega) (by omega) ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relZeros (stable_true _) (fun _ hb => countN hb) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relScatter (by decide) (by omega) (by omega) (by omega) (by omega) ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relScatter (by decide) (by omega) (by omega) (by omega) (by omega) ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relScatter (by decide) (by omega) (by omega) (by omega) (by omega) ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relEOne F1 ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relWinOne (stable_true _) F1 (by taint_decide)) ?_
  refine RelCT.seq (relInverse (stable_true _) F1 (by taint_decide)) ?_
  exact relCountF F ⟨_, by taint_decide⟩

theorem relFinishF (F : Fits Z len) :
    RelCT isa (Both lay B Z len N args sp C T2) (finishF lay) (Both lay B Z len N args sp C T2) := by
  have F1 := F.fit
  have F2 := F.two
  have ke := kw_eq len
  have r1 := rv_a len 1; have r2 := rv_a len 2; have r3 := rv_a len 3; have r7 := rv_a len 7
  have r12 := rv_a len 12; have r14 := rv_a len 14
  have r4 : rv (kw len) { arr := fgArr } = 160 + 4 * (8 * nw len + 8) := rv_a len 4
  have r11 : rv (kw len) { arr := deArr } = 160 + 11 * (8 * nw len + 8) := rv_a len 11
  have h71 := rv_half1' len 7; have h141 := rv_half1' len 14
  have h71' : rv (kw len) { arr := (a 7).arr, half := 1, byte := (a 7).byte } = rv (kw len) (a 7) + 4 * nw len := h71
  have rt : rv (kw len) tmp = rv (kw len) (a 12) := rfl
  have rmo : rv (kw len) mo = rv (kw len) (a 2) := rfl
  have f1 : fgSz * (nw len + 1) = 16 * (nw len + 1) := rfl
  have f2 : fgSz * (nw len + 2) = 16 * (nw len + 2) := rfl
  have d1 : deSz * (nw len + 1) = 20 * (nw len + 1) := rfl
  have d2 : deSz * (nw len + 2) = 20 * (nw len + 2) := rfl
  have efs : fgSz = 16 := rfl; have eds : deSz = 20 := rfl
  unfold finishF addIfNegF
  simp only [seqs]
  refine RelCT.seq (relGather (by decide) (by omega) (by omega) (by omega) ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relGather (by decide) (by omega) (by omega) (by omega) ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relZeros (stable_true _) (fun _ hb => countN hb) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relChainSub (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
    (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (.inr (by omega)) (by taint_decide)) ?_
  refine RelCT.seq (relMaskAt (stable_true _) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relSelIn (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (RelCT.seq (relChainAdd (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
      (by omega) (by omega) (by omega) (.inr (by omega)) (.inr (by omega)) (by taint_decide))
    (RelCT.seq (relMaskAt (stable_true _) (by omega) (by taint_decide))
      (relSelIn (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)))) ?_
  refine RelCT.seq (RelCT.seq (relChainAdd (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
      (by omega) (by omega) (by omega) (.inr (by omega)) (.inr (by omega)) (by taint_decide))
    (RelCT.seq (relMaskAt (stable_true _) (by omega) (by taint_decide))
      (relSelIn (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)))) ?_
  refine RelCT.seq (relCsub (src := a 7) (o := a 7) (stable_true _) F.toRoom rfl rfl (by omega) (by omega) (.inr (by omega))
    (fun h => absurd rfl h) (.inl (by omega)) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relZeros (stable_true _) (fun _ hb => countW hb) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relChainSub (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
    (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (.inl (by omega)) (by taint_decide)) ?_
  refine RelCT.seq (relMaskAtNot (stable_true _) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relSelIn (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relZeros (stable_true _) (fun _ hb => countW hb) (by omega) (by omega) (by taint_decide)) ?_
  exact relCopy (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)

theorem relBody (F : Fits Z len) :
    RelCT isa (fun s t => Pre0 lay B Z len N args sp s ∧ Pre0 lay B Z len N args sp t) (body lay)
      (Both lay B Z len N args sp (· = 0) T2) := by
  have F2 := F.two
  have F4 := F.small
  unfold body
  simp only [seqs]
  refine RelCT.seq (relInitF F) ?_
  refine RelCT.seq ((relLoopF F ((3 * nw len + 2) / 2)).mono (fun _ _ h => ⟨h, by omega, by omega⟩)
    fun _ _ h => h) ?_
  exact RelCT.seq (relBatchF F true) (relFinishF F)

end VG.Proof.Rsa.X86.InvBatchRt.Time
