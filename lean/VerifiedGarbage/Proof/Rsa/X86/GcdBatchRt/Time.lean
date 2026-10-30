module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Comp
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2
public import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
import VerifiedGarbage.Proof.Rsa.X86.GcdBatchRt.Init
import VerifiedGarbage.Proof.Rsa.X86.GcdBatchRt.Shr
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Arrays
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Comp
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Kinds2
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Step
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob

/-! # The batched GCD in both runs, in prime recovery's wide layout

`InvBatchRt.Time`'s leaves, joined as `GcdBatchRt.body` runs them, and two leaves of its own: the
shift `shr30o` and the copy of `n - 1` words. Its trace depends only on what `Pre0` makes
public: the batches' count, kept in the header and equal in both runs.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.GcdBatchRt.Time

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Impl.Rsa.X86.GcdBatchRt (shr30o res)
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Rsa.X86.InvBatchRt.Time
open VG.Proof.Rsa.X86.GcdBatchRt (shr30o_ok copyC_ok countLess countN0 rv_res)
open VG.Impl.Rsa.X86.RecoverRt (wid)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)

section
variable {L : Lay} {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}
  {G : (Reg → BitVec 32) → Prop}

theorem relShr30o {dst src : Ref} (hG : Stable VG.Proof.Weierstrass.X86.Inv.wordClob G)
    (hdh : dst.half = 0) (hodd : nw len % 2 = 1) (h3 : 3 ≤ nw len) (hsz : rv (kw len) src + 4 * (nw len + 1) ≤ Z)
    (hdz : rv (kw len) dst + 4 * (nw len + 1) ≤ Z)
    (sep : rv (kw len) dst + 4 * (nw len + 1) ≤ rv (kw len) src ∨ rv (kw len) src + 4 * (nw len + 1) ≤ rv (kw len) dst)
    {hc : VG.Taint.Hint VG.X86.Taint.T} (h : (VG.Taint.check sseTaint (τS L) (shr30o L dst src) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (shr30o L dst src)
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp (by decide) hG (ws1 (by have := rv_ge (kw len) dst; omega) hdz)
    (fun s hb _ => WP.mono (shr30o_ok hb hdh hodd h3 hsz hdz sep) fun _ ⟨H, _, K, O⟩ => ⟨H, K, O.unch, trivial⟩) h

theorem relCopyLess {o a : Ref} (hG : Stable [.eax, .ebx, .ecx, .edx, .ebp] G) (h3 : 3 ≤ nw len)
    (hoz : rv (kw len) o + 4 * (nw len - 1) ≤ Z) (haz : rv (kw len) a + 4 * (nw len - 1) ≤ Z)
    (sep : rv (kw len) o + 4 * (nw len - 1) ≤ rv (kw len) a ∨ rv (kw len) a + 4 * (nw len - 1) ≤ rv (kw len) o)
    {hc : VG.Taint.Hint VG.X86.Taint.T}
    (h : (VG.Taint.check sseTaint (τS L) (VG.Impl.Rsa.X86.InvBatchRt.copy L o a (nBytesLess .edi)) hc).isSome = true) :
    RelCT isa (Both L B Z len N args sp C fun g => G g ∧ True) (VG.Impl.Rsa.X86.InvBatchRt.copy L o a (nBytesLess .edi))
      (Both L B Z len N args sp C fun g => G g ∧ True) :=
  relOp (by decide) hG (ws1 (by have := rv_ge (kw len) o; omega) hoz)
    (fun s hb _ => WP.mono (copyC_ok hb (countLess hb (by omega)) (by omega) hoz haz sep)
      fun _ ⟨H, O, _, K⟩ => ⟨H, K, O.unch, trivial⟩) h

end

/-- What the GCD needs of the lengths: `Room`, and `n` odd, at least 3, and small enough to count
its batches in a word. -/
structure GFits (Z len : Nat) : Prop extends Room Z len where
  odd : nw len % 2 = 1
  three : 3 ≤ nw len
  small : nw len ≤ 1024

variable {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {C : Nat → Prop}

theorem relInit (F : GFits Z len) :
    RelCT isa (fun s t => Pre0 wid B Z len N args sp s ∧ Pre0 wid B Z len N args sp t)
      (VG.Impl.Rsa.X86.GcdBatchRt.init wid)
      (Both wid B Z len N args sp (· = 3 * (nw len + 1)) fun _ => True ∧ True) := by
  have F1 := F.fit
  have F3 := F.three
  have r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r12 := rv_a len 12
  unfold VG.Impl.Rsa.X86.GcdBatchRt.init
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine RelCT.seq (relSlots (by taint_decide)) ?_
  refine RelCT.seq (relZeros (stable_true _) (fun _ hb => countN hb) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relCopyLess (stable_true _) F3 (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relCopy (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relZeros (stable_true _) (fun _ hb => countN hb) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relCopyLess (stable_true _) F3 (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relZeros (stable_true _) (fun _ hb => countN hb) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relEvenMask (stable_true _) (by taint_decide)) ?_
  refine RelCT.seq (relSelIn (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relChainAdd (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
    (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relWinOne (stable_true _) F1 (by taint_decide)) ?_
  exact relBatches (stable_true _) (by taint_decide)

theorem relUpdate (F : GFits Z len) :
    RelCT isa (Both wid B Z len N args sp C fun _ => True ∧ True) (VG.Impl.Rsa.X86.GcdBatchRt.update wid)
      (Both wid B Z len N args sp C fun _ => True ∧ True) := by
  have F1 := F.fit
  have r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r11 := rv_a len 11
  unfold VG.Impl.Rsa.X86.GcdBatchRt.update
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine RelCT.seq (relLinear F.toRoom (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relShr30o (stable_true _) rfl F.odd F.three (by omega) (by omega) (by omega)
    (by taint_decide)) ?_
  refine RelCT.seq (relLinear F.toRoom (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩) ?_
  refine RelCT.seq (relShr30o (stable_true _) rfl F.odd F.three (by omega) (by omega) (by omega)
    (by taint_decide)) ?_
  exact relCopy (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)

/-- One batch, then its count down by one. -/
theorem relBatch {k : Nat} (F : GFits Z len) (hk : 1 ≤ k) (hk32 : k < 2 ^ 32) :
    RelCT isa (Both wid B Z len N args sp (· = k) fun _ => True ∧ True)
      (VG.Impl.Rsa.X86.Keys.seqs [.block (start wid), VG.Impl.Weierstrass.X86.Inv.wordSteps win 30,
        VG.Impl.Rsa.X86.GcdBatchRt.update wid,
        .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter]])
      (fun s t => Both wid B Z len N args sp (· = k - 1) (fun _ => True ∧ True) s t ∧
        s.zf = some (decide (k - 1 = 0)) ∧ t.zf = some (decide (k - 1 = 0))) := by
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  exact RelCT.seq (relStart (stable_true _) F.fit (by taint_decide))
    (RelCT.seq (relWordSteps (stable_true _) F.fit (by taint_decide))
      (RelCT.seq (relUpdate F) (relCountDown hk hk32 (by taint_decide))))

/-- The batches, from the count `K`. -/
theorem relBatchLoop (F : GFits Z len) (K : Nat) :
    RelCT isa (fun s t => Both wid B Z len N args sp (· = K) (fun _ => True ∧ True) s t ∧ 1 ≤ K ∧ K < 2 ^ 32)
      (.loop (VG.Impl.Rsa.X86.Keys.seqs [.block (start wid), VG.Impl.Weierstrass.X86.Inv.wordSteps win 30,
        VG.Impl.Rsa.X86.GcdBatchRt.update wid,
        .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter]]) .ne)
      (Both wid B Z len N args sp (· = 0) fun _ => True ∧ True) := by
  refine RelCT.loop (M := isa) (fun k s t => Both wid B Z len N args sp (· = k) (fun _ => True ∧ True) s t ∧
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

theorem relFinish (F : GFits Z len) :
    RelCT isa (Both wid B Z len N args sp C fun _ => True ∧ True) (VG.Impl.Rsa.X86.GcdBatchRt.finish wid)
      (Both wid B Z len N args sp C fun _ => True ∧ True) := by
  have F1 := F.fit
  have F3 := F.three
  have r0 := rv_a len 0; have r4 := rv_a len 4; have r5 := rv_a len 5; have r12 := rv_a len 12
  have h41 := rv_half1' len 4
  have rr := rv_res len
  unfold VG.Impl.Rsa.X86.GcdBatchRt.finish
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine RelCT.seq (relZeros (stable_true _) (fun _ hb => countN0 hb) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relChainSub (X := fun _ => True) (stable_true _) (fun _ _ => trivial) (by decide) rfl
    (by omega) (by omega) (by omega) (.inl (Nat.le_refl _)) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relMaskAtNot (stable_true _) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relSelIn (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  refine RelCT.seq (relCopy (stable_true _) (by decide) (by omega) (by omega) (by omega) (by taint_decide)) ?_
  exact relZeros (stable_true _) (fun _ hb => countN0 hb) (by omega) (by omega) (by taint_decide)

theorem relBody (F : GFits Z len) :
    RelCT isa (fun s t => Pre0 wid B Z len N args sp s ∧ Pre0 wid B Z len N args sp t)
      (VG.Impl.Rsa.X86.GcdBatchRt.body wid) (Both wid B Z len N args sp (· = 0) fun _ => True ∧ True) := by
  have F4 := F.small
  unfold VG.Impl.Rsa.X86.GcdBatchRt.body
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine RelCT.seq (relInit F) ?_
  refine RelCT.seq ((relBatchLoop F (3 * (nw len + 1))).mono (fun _ _ h => ⟨h, by omega, by omega⟩)
    fun _ _ h => h) ?_
  exact relFinish F

end VG.Proof.Rsa.X86.GcdBatchRt.Time
