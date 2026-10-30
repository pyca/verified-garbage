module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.TimeInit
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.TimeUpdate
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.TimeTail
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Comp
meta import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2

/-! # The batched inverse in both runs, in `crt_values`' layout

Its trace depends only on what `Pre0` makes public: the batches' count, kept in the header and
equal in both runs, and the doublings' count in `esi`, likewise.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Impl.Rsa.X86.CrtValuesRt (lay)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)

variable {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}

/-- One batch, then its count down by one. -/
theorem relBatch {k : Nat} (F : Fits Z len) (hk : 1 ≤ k) (hk32 : k < 2 ^ 32) :
    RelCT isa (Both lay B Z len N args sp (· = k) fun _ => True ∧ True)
      (VG.Impl.Rsa.X86.Keys.seqs [.block (start lay), VG.Impl.Weierstrass.X86.Inv.wordSteps win 30, update lay,
        .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter]])
      (fun s t => Both lay B Z len N args sp (· = k - 1) (fun _ => True ∧ True) s t ∧
        s.zf = some (decide (k - 1 = 0)) ∧ t.zf = some (decide (k - 1 = 0))) := by
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  exact RelCT.seq (relStart (stable_true _) F.fit (by taint_decide))
    (RelCT.seq (relWordSteps (stable_true _) F.fit (by taint_decide))
      (RelCT.seq (relUpdate F) (relCountDown hk hk32 (by taint_decide))))

/-- The batches, from the count `K`. -/
theorem relBatchLoop (F : Fits Z len) (K : Nat) :
    RelCT isa (fun s t => Both lay B Z len N args sp (· = K) (fun _ => True ∧ True) s t ∧ 1 ≤ K ∧ K < 2 ^ 32)
      (.loop (VG.Impl.Rsa.X86.Keys.seqs [.block (start lay), VG.Impl.Weierstrass.X86.Inv.wordSteps win 30, update lay,
        .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter]]) .ne)
      (Both lay B Z len N args sp (· = 0) fun _ => True ∧ True) := by
  refine RelCT.loop (M := isa) (fun k s t => Both lay B Z len N args sp (· = k) (fun _ => True ∧ True) s t ∧
    1 ≤ k ∧ k < 2 ^ 32) (fun k => ?_) K
  by_cases hk : 1 ≤ k ∧ k < 2 ^ 32
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2
  refine (relBatch F hk.1 hk.2).mono (fun _ _ h => h.1) fun s t ⟨hb, zs, zt⟩ => ?_
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

theorem relBody (F : Fits Z len) :
    RelCT isa (fun s t => Pre0 lay B Z len N args sp s ∧ Pre0 lay B Z len N args sp t) (body lay)
      (Both lay B Z len N args sp (· = 0) fun _ => True ∧ True) := by
  have F2 := F.two
  have F4 := F.small
  unfold body
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine RelCT.seq (relInit F) ?_
  refine RelCT.seq ((relBatchLoop F (3 * (nw len + 1))).mono (fun _ _ h => ⟨h, by omega, by omega⟩)
    fun _ _ h => h) ?_
  refine RelCT.seq (relNormalize F) ?_
  refine RelCT.seq (relDoublings (by taint_decide)) ?_
  refine RelCT.seq ((relDoubleLoop F (6 * (nw len + 1))).mono (fun _ _ h => ⟨h, by omega, by omega⟩)
    fun _ _ h => h) ?_
  exact relFinish F

end VG.Proof.Rsa.X86.InvBatchRt.Time
