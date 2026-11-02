module

import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupMainCT
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupStages
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupPrimeCT
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupMainCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupStages
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupPrimeCT
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Complete three-workspace CRT setup is constant time -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (arrAt)

theorem crt_setupP_ct {base : BitVec 32} {len w : Nat} (fit : 256 ≤ 8 * len) :
    RelCT isa (fun s t => CrtAtMain base len w s ∧ CrtAtMain base len w t) (setupPrime 224)
      (fun s t => CrtAtPrime base (crtP base w) len w s ∧ CrtAtPrime base (crtP base w) len w t) := by
  let P := CrtAtMain base len w
  have input (s : State) (h : P s) : CrtSetupPrimeInput base (crtP base w) len 224 w s :=
    ⟨⟨h.context.main, h.ptr, h.main.toCrtLayoutState.nativeCount h.context.main, h.main.p⟩, h.context.p⟩
  have ct := (crt_setupPrime_ct (base := base) (child := crtP base w) (len := len) (slot := 224) (w := w)
    (by omega) (by omega) (by decide)).mono (P' := fun s t => P s ∧ P t)
    (fun s t h => ⟨input s h.1, input t h.2⟩) (fun _ _ _ => trivial)
  exact pair_posts ct (fun s h => crt_setupPrime_ready s h h.context.p (by omega) (by decide) h.context.sepMP h.main.p)

theorem crt_setupQ_ct {base : BitVec 32} {len w : Nat} (fit : 256 ≤ 8 * len) :
    RelCT isa (fun s t => CrtAtMain base len w s ∧ CrtAtMain base len w t) (setupPrime 228)
      (fun s t => CrtAtPrime base (crtQ base w) len w s ∧ CrtAtPrime base (crtQ base w) len w t) := by
  let P := CrtAtMain base len w
  have input (s : State) (h : P s) : CrtSetupPrimeInput base (crtQ base w) len 228 w s :=
    ⟨⟨h.context.main, h.ptr, h.main.toCrtLayoutState.nativeCount h.context.main, h.main.q⟩, h.context.q⟩
  have ct := (crt_setupPrime_ct (base := base) (child := crtQ base w) (len := len) (slot := 228) (w := w)
    (by omega) (by omega) (by decide)).mono (P' := fun s t => P s ∧ P t)
    (fun s t h => ⟨input s h.1, input t h.2⟩) (fun _ _ _ => trivial)
  exact pair_posts ct (fun s h => crt_setupPrime_ready s h h.context.q (by omega) (by decide) h.context.sepMQ h.main.q)

theorem crt_leavePrime_ct {base child : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => CrtAtPrime base child len w s ∧ CrtAtPrime base child len w t) (.block leavePrime)
      (fun s t => CrtAtMain base len w s ∧ CrtAtMain base len w t) := by
  have ct : RelCT isa (fun s t => CrtAtPrime base child len w s ∧ CrtAtPrime base child len w t)
      (.block leavePrime) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  exact pair_posts ct (fun s h => crt_leavePrime_ready s h)

theorem crt_setupAll_ct {base : BitVec 32} {len w : Nat} (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (fits : arrAt w 8 ≤ 8 * len) :
    RelCT isa (fun s t => CrtSetupInput base len w s ∧ CrtSetupInput base len w t) setupAll (fun _ _ => True) := by
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have first := (crt_setupMain_ct (base := base) hw hw' fits).mono
    (P' := fun s t => CrtSetupInput base len w s ∧ CrtSetupInput base len w t)
    (fun _ _ h => ⟨⟨h.1.context.main, h.1.ptr, h.1.count, h.1.zero⟩,
      ⟨h.2.context.main, h.2.ptr, h.2.count, h.2.zero⟩⟩) (fun _ _ _ => trivial)
  exact ((pair_posts first (fun s h => crt_setupMain_ready s h)).seq ((crt_setupP_ct size).seq
    (crt_leavePrime_ct.seq ((crt_setupQ_ct size).seq crt_leavePrime_ct)))).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
