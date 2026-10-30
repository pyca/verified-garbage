module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Comp
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Comp
meta import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2

/-! # The batched inverse's correction in both runs, in `crt_values`' layout

`normalize`, the doublings (whose count `esi` both runs share) and `finish`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Impl.Rsa.X86.CrtValuesRt (lay)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)

variable {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}

theorem relNormalize (F : Fits Z len) :
    RelCT isa (Both lay B Z len N args sp C fun _ => True ∧ True) (normalize lay)
      (Both lay B Z len N args sp C fun _ => True ∧ True) := by
  have F1 := F.fit
  have r2 := rv_a len 2; have r4 := rv_a len 4; have r6 := rv_a len 6; have r12 := rv_a len 12
  have h41 := rv_half1' len 4
  have rt : rv (kw len) tmp = rv (kw len) (a 12) := rfl
  unfold normalize
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine RelCT.seq (relCopy (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relChainSub (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
    (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relMaskAt (stable_true _) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relSelIn (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  exact relCsub (stable_true _) F.toRoom rfl rfl (by omega) (by omega) (by omega) (fun h => absurd rfl h) (by omega)
    ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩

/-- One doubling, then the count down by one. -/
theorem relDouble {k : Nat} (F : Fits Z len) (hk : 1 ≤ k) (hk32 : k < 2 ^ 32) :
    RelCT isa (Both lay B Z len N args sp C fun g => g .esi = BitVec.ofNat 32 k ∧ True)
      (.seq (twice lay) (.block [decCounter, testCounter]))
      (fun s t => Both lay B Z len N args sp C (fun g => g .esi = BitVec.ofNat 32 (k - 1) ∧ True) s t ∧
        s.zf = some (decide (k - 1 = 0)) ∧ t.zf = some (decide (k - 1 = 0))) := by
  have F1 := F.fit
  have r2 := rv_a len 2; have r6 := rv_a len 6; have r12 := rv_a len 12
  have h61 := rv_half1' len 6
  have rt : rv (kw len) tmp = rv (kw len) (a 12) := rfl
  unfold twice
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine RelCT.seq (RelCT.seq (relChainAdd (X := fun _ => True) (stable_esi (by decide) _) (fun _ _ => trivial)
    (by decide) rfl (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (.inl (Nat.le_refl _))
    (by taint_decide)) (RelCT.seq (relCsub (stable_esi (by decide) _) F.toRoom rfl rfl (by omega) (by omega)
      (by omega) (fun h => absurd rfl h) (by omega) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩)
    (relZeroWord (stable_esi (by decide) _) (by omega) (by taint_decide)))) ?_
  exact relDecTest hk hk32 (by taint_decide)

/-- The doublings, from the count `esi = K`. -/
theorem relDoubleLoop (F : Fits Z len) (K : Nat) :
    RelCT isa (fun s t => Both lay B Z len N args sp C (fun g => g .esi = BitVec.ofNat 32 K ∧ True) s t ∧
        1 ≤ K ∧ K < 2 ^ 32)
      (.loop (.seq (twice lay) (.block [decCounter, testCounter])) .ne)
      (Both lay B Z len N args sp C fun _ => True ∧ True) := by
  refine RelCT.loop (M := isa) (fun k s t => Both lay B Z len N args sp C (fun g => g .esi = BitVec.ofNat 32 k ∧ True) s t ∧
    1 ≤ k ∧ k < 2 ^ 32) (fun k => ?_) K
  by_cases hk : 1 ≤ k ∧ k < 2 ^ 32
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2
  refine (relDouble F hk.1 hk.2).mono (fun _ _ h => h.1) fun s t ⟨hb, zs, zt⟩ => ?_
  have es : isa.eval .ne s = s.zf.map (!·) := rfl
  have et : isa.eval .ne t = t.zf.map (!·) := rfl
  refine ⟨by rw [es, et, zs, zt], fun hf => ?_, fun ht => ⟨k - 1, by omega, hb, ?_, by omega⟩⟩
  · obtain ⟨⟨b, p, c, _, x⟩, ⟨b', p', c', _, x'⟩⟩ := hb
    exact ⟨⟨b, p, c, trivial, x⟩, ⟨b', p', c', trivial, x'⟩⟩
  · rw [es, zs] at ht
    by_contra h0
    simp_all

theorem relFinish (F : Fits Z len) :
    RelCT isa (Both lay B Z len N args sp C fun _ => True ∧ True) (finish lay)
      (Both lay B Z len N args sp C fun _ => True ∧ True) := by
  have F1 := F.fit
  have r1 := rv_a len 1; have r3 := rv_a len 3; have r4 := rv_a len 4; have r6 := rv_a len 6
  have h41 := rv_half1' len 4
  have ke := kw_eq len
  have F2 := F.two
  unfold finish
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine RelCT.seq (relZeros (stable_true _) (fun _ hb => countW hb) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relChainSub (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
    (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relMaskAtNot (stable_true _) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relSelIn (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relZeros (stable_true _) (fun _ hb => countW hb) (by omega) (by omega) (by taint_decide)) ?_
  exact relCopy (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)

end VG.Proof.Rsa.X86.InvBatchRt.Time
