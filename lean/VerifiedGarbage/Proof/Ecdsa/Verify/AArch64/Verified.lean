module

public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.GContract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.AArch64

import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacContract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPointsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.CachedChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedLit
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Jacobian
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafPoints
import VerifiedGarbage.Proof.Ecdh.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
/-! ## `JacAbi` -/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/NafMain.lean`, which only this module imported.
section

/-! The Jacobian verifier satisfies the existing complete verification postcondition. -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

variable {c : Cfg}

theorem nafVerify_eq (c : Cfg) : Impl.Ecdsa.Verify.AArch64.Cfg.nafVerify c =
    .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) (.seq (.seq (.block (c.setupWith (some D)))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.block [])))
      (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.AArch64.Cfg.peer c))
      (.seq (Impl.Ecdh.AArch64.Cfg.validate c) (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c)
      (.seq c.nPow (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv c)
      (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.nafPoints c) (Impl.Ecdsa.Verify.AArch64.Cfg.tail c))))))))) := rfl

/-- `vg_ecdsa_<curve>_verify` returns whether the specification's
verification holds, and restores the callee-saved registers. -/
theorem nafVerify_ok (hc : CfgOk c) (hn : c.n=4) (hC : Law c.C) (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start)
    {s₀ : State} (hp : VPre c s₀) :
    WP isa (Impl.Ecdsa.Verify.AArch64.Cfg.nafVerify c) s₀ fun s' =>
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s₀.gpr r) ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [nafVerify_eq]
  refine front_ok hc hp fun g s₁ hg hF => mid_ok hc hF fun s₂ hM => ?_
  have F₂ := hM.fixed
  have h1 := onep_tmv hc F₂
  -- The point the window method multiplies.
  let P := peerPt c (s₀.mem (s₀.gpr .x0) = 4) (keyX c s₀) (keyY c s₀)
  have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  have hG : Rep c.C (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl GX)) (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl GY))
      (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s₂.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s₂.mem _ (c.sl GY) c.n))
      (toM _ _ (wordsVal s₂.mem _ (c.sl ONEP) c.n)) (G c.C)
    rw [F₂.gx, F₂.gy, toM_cmont hc, toM_cmont hc, show toM c.C.p (2 ^ (64 * c.n))
      (wordsVal s₂.mem (s₀.gpr .x3) (c.sl ONEP) c.n) = 1 from h1]
    exact rep_affine' hC _ _
  have hQ : Rep c.C (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PX)) (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PY))
      (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  have hu : sv c (s₀.gpr .x3) s₂ U < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  have hv : sv c (s₀.gpr .x3) s₂ V < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  refine nafPoints_ok hc hn hM
    (Q₁ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (s₀.gpr .x3) s₂ U >>> j) (G c.C)))
    (Q₂ := fun j X Y Z => Rep c.C X Y Z (mul (sv c (s₀.gpr .x3) s₂ V >>> j) P))
    hC hT hp.tbl (fun X Y Z h => by simp only [Nat.shiftRight_zero]; exact h) hPc hQ
    (fun X Y Z h => by simp only [Nat.shiftRight_zero]; exact h) fun s₃ hP => ?_
  refine WP.mono (tail_dispatch_ok hc hC hP.toFinalState) fun s' ⟨saved, xo, hxo, hx, ret⟩ =>
    ⟨fun r hr => (saved r hr).trans (hg r hr), ?_⟩
  obtain ⟨X1, Y1, Z1, X2, Y2, Z2, q1, q2, hsum⟩ := hP.pt
  have q1' : Rep c.C X1 Y1 Z1 (mul (sv c (s₀.gpr .x3) s₂ U) (G c.C)) := by
    have := q1; simp only [Nat.shiftRight_zero] at this; exact this
  have q2' : Rep c.C X2 Y2 Z2 (mul (sv c (s₀.gpr .x3) s₂ V) P) := by
    have := q2; simp only [Nat.shiftRight_zero] at this; exact this
  have hR := Rep.add hC (hC.onCurve_mul hc.onG _) (hC.onCurve_mul hPc _) q1' q2' hsum.symm
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .x0)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .x0)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  have hiff : (Ecdh.Valid c.C (s₀.mem (s₀.gpr .x0)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      tmv c.C c.n (s₀.gpr .x3) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (s₀.gpr .x3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq c, hspec, ret]
  by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
      sv c (s₀.gpr .x3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
  · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]

end VG.Proof.Ecdsa.Verify.AArch64
end

end

@[expose] public section

section

/-! Production P-256 Jacobian verification preserves the existing ABI and result contract. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jacPre_of {s : State} (h : verifyAArch64.pre s) : VPre p256 s := by
  obtain ⟨h1,h2,h3,h4,h5,h6,held,fit,hdw⟩ := h
  exact ⟨h1,h2,h3,h4,h5,h6,⟨by rw [h1]; simp,held,fit,hdw _ (by simp)⟩⟩

theorem jacVerify_callsKeep : CallsKeep verifyP256 := by lit_decide

theorem jacVerify_untouched : KeepsUntouched verifyP256 := by lit_decide

theorem jacVerify_keepsV : verifyP256.allInstrs keepsV=true := by lit_decide

theorem jacVerify_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (s : State) (hs : verifyAArch64.pre s) :
    ∃ t s', Exec isa verifyP256 s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := nafVerify_ok (p256_ok hI) (by decide) hL hT (jacPre_of hs)
  exact ⟨t,s',he,abiPreserved_of he jacVerify_callsKeep jacVerify_untouched jacVerify_keepsV hsv,hpost⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointAbi` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jointVerify_callsKeep : CallsKeep P256Joint.verify := by lit_decide

theorem jointVerify_untouched : KeepsUntouched P256Joint.verify := by lit_decide

theorem jointVerify_keepsV : P256Joint.verify.allInstrs keepsV=true := by lit_decide

theorem jointVerify_a64_of_wp
    (correct : ∀ s,VPreG s → WP isa P256Joint.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t)
    (s : State) (hs : verifyGAArch64.pre s) :
    ∃ t s',Exec isa P256Joint.verify s t s' ∧ abiPreserved s s' ∧ verifyGAArch64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := correct s (vpreG_of hs)
  exact ⟨t,s',he,abiPreserved_of he jointVerify_callsKeep jointVerify_untouched jointVerify_keepsV hsv,hpost⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `AllocatedAbi` -/

section

/-! The allocated verifier temporarily uses x26–x28 and x30. Its ABI proof
uses the actual save/restore contracts, rather than declaring those registers
syntactically untouched by the optimized arithmetic. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass.AArch64

private structure OldSafe (c : Prog isa) : Prop where
  untouched : KeepsUntouched c
  callsKeep : CallsKeep c

private theorem callsKeep_seq {a b : Prog isa} : CallsKeep (.seq a b) ↔ CallsKeep a ∧ CallsKeep b := by
  simp only [CallsKeep, Code.calls, List.all_append, Bool.and_eq_true]

private theorem OldSafe.left {a b : Prog isa} (h : OldSafe (.seq a b)) : OldSafe a :=
  ⟨(Bool.and_eq_true_iff.mp h.untouched).1,(callsKeep_seq.mp h.callsKeep).1⟩

private theorem OldSafe.right {a b : Prog isa} (h : OldSafe (.seq a b)) : OldSafe b :=
  ⟨(Bool.and_eq_true_iff.mp h.untouched).2,(callsKeep_seq.mp h.callsKeep).2⟩

private theorem OldSafe.seq {a b : Prog isa} (ha : OldSafe a) (hb : OldSafe b) : OldSafe (.seq a b) :=
  ⟨Bool.and_eq_true_iff.mpr ⟨ha.untouched,hb.untouched⟩,callsKeep_seq.mpr ⟨ha.callsKeep,hb.callsKeep⟩⟩

private theorem oldSafe : OldSafe P256Joint.verify := ⟨jointVerify_untouched,jointVerify_callsKeep⟩

private theorem before_safe : OldSafe (beforeInverse p256) := by
  have h := oldSafe
  exact h.left.seq (h.right.left.seq (h.right.right.left.seq (h.right.right.right.left.seq
    (h.right.right.right.right.left.seq (h.right.right.right.right.right.left.seq ⟨rfl,rfl⟩)))))

private theorem uv_safe : OldSafe (Cfg.uv p256) := oldSafe.right.right.right.right.right.right.right.left

private theorem tail_safe : OldSafe (Cfg.tail p256) := oldSafe.right.right.right.right.right.right.right.right.right

private theorem OldSafe.keeps {c : Prog isa} {s t : State} {tr : List Leak} (h : OldSafe c)
    (he : Exec isa c s tr t) : ∀ r∈VG.Proof.Ecdsa.AArch64.untouched,t.gpr r=s.gpr r :=
  untouched_keep he h.callsKeep h.untouched

 theorem allocatedVerify_keepsV : P256Allocated.verify.allInstrs keepsV=true := by lit_decide

/-- Actual restoration, together with the existing saved-register result, suffices for the ABI. -/
theorem allocated_abiPreserved_of {s t : State} {tr : List Leak}
    (he : Exec isa P256Allocated.verify s tr t)
    (hsv : ∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r)
    (hu : ∀ r∈untouched,t.gpr r=s.gpr r) : abiPreserved s t := by
  refine ⟨fun r hr => ?_,Exec.sp he,Exec.preservedV he allocatedVerify_keepsV⟩
  by_cases hh : r∈untouched
  · exact hu r hh
  · apply hsv r
    revert hh
    revert r
    decide

/-- Compose the two restored arithmetic stages with the unchanged surrounding code. -/
theorem allocatedVerify_extra_preserved (hc : CfgOk p256)
    (hprefix : ∀ s,VPreG s → WP isa allocatedPrefix s fun t => ∃ g,Mid p256 s (s.gpr .x3) g t)
    (hinverse : ∀ s₀ s,InverseInput p256 s₀ (s₀.gpr .x3) s →
      WP isa P256Allocated.inverse s fun t => ∀ r∈untouched,t.gpr r=s.gpr r)
    (hpoints : ∀ s₀ g s,VPreG s₀ → Mid p256 s₀ (s₀.gpr .x3) g s →
      WP isa P256Allocated.points s fun t => ∀ r∈untouched,t.gpr r=s.gpr r)
    {s s' : State} {tr : List Leak} (hp : VPreG s)
    (he : Exec isa P256Allocated.verify s tr s') : ∀ r∈untouched,s'.gpr r=s.gpr r := by
  obtain ⟨a,b,tp,tq,tt,ep,eq,et,_⟩ := allocatedVerify_cut he
  obtain ⟨i,j,ti,tj,tu,ei,ej,eu,_⟩ := allocatedPrefix_cut ep
  obtain ⟨_,_,ebi,ib⟩ := beforeInverse_ok hc hp
  obtain ⟨_,rfl⟩ := ei.det ebi
  obtain ⟨_,_,einv,ki⟩ := hinverse s i ib
  obtain ⟨_,rfl⟩ := ej.det einv
  obtain ⟨_,_,em,g,hm⟩ := hprefix s hp
  obtain ⟨_,rfl⟩ := ep.det em
  obtain ⟨_,_,ept,kp⟩ := hpoints s g a hp hm
  obtain ⟨_,rfl⟩ := eq.det ept
  intro r hr
  exact (tail_safe.keeps et r hr).trans ((kp r hr).trans ((uv_safe.keeps eu r hr).trans
    ((ki r hr).trans (before_safe.keeps ei r hr))))

 theorem allocatedVerify_a64_of_wp
    (correct : ∀ s,VPreG s → WP isa P256Allocated.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t)
    (restored : ∀ {s t : State} {tr : List Leak},VPreG s →
      Exec isa P256Allocated.verify s tr t → ∀ r∈untouched,t.gpr r=s.gpr r)
    (s : State) (hs : verifyGAArch64.pre s) :
    ∃ tr t,Exec isa P256Allocated.verify s tr t ∧ abiPreserved s t ∧ verifyGAArch64.post s t := by
  have hp := vpreG_of hs
  obtain ⟨tr,t,he,hsv,hpost⟩ := correct s hp
  exact ⟨tr,t,he,allocated_abiPreserved_of he hsv (restored hp he),hpost⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointCorrect` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jointVerify_ok (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start)
    {s : State} (h : VPreG s) :
    WP isa P256Joint.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t :=
  verify_of_joint (p256_ok hI) hL P256Joint.points P256Joint.verify rfl
    (by
      intro s₀ base g s hm ht P hp hr
      exact jointPoints_ok (p256_ok hI) hL hT hm ht hp hr) h

theorem jointVerify_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start)
    (s : State) (hs : verifyGAArch64.pre s) :
    ∃ t s',Exec isa P256Joint.verify s t s' ∧ abiPreserved s s' ∧ verifyGAArch64.post s s' :=
  jointVerify_a64_of_wp (fun _ hp => jointVerify_ok hL hI hT hp) s hs

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointVerified` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

/-- Joint verification satisfies the existing correctness, ABI, and public-input contract. -/
theorem jointVerify_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start)
    :
    Verified AArch64.target P256Joint.verify
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts P256Joint.p256v.combConsts)) := by
  refine ⟨fun s hs => ?_,?_,impliesG.sat⟩
  · obtain ⟨t,s',he,ha,hp⟩ := jointVerify_a64 hL hI hT s (impliesG.pre _ hs)
    exact ⟨t,s',he,ha,impliesG.post s s' hs hp⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
    exact jointVerify_ct_of_points (p256_ok hI) jointPrefix_ct
      (fun _ _ ps pt => jointPoints_relCT (p256_ok hI) hL hT ps pt) jointTail_ct
      _ _ _ _ _ _ (vpreG_of (impliesG.pre _ pre₁)) (vpreG_of (impliesG.pre _ pre₂))
      (jacPublicG_of_spec pub) e₁ e₂

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `Verified` -/

section

/-!
# Verified Jacobian P-256 verification on AArch64

The Jacobian comb and sparse signed-window multiplications satisfy the existing
verification contract. Table addresses and exceptional-point branches depend
only on the public key, digest and signature declared public by that contract.
-/

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

/-- Use the public inputs declared by the shared specification directly. -/
theorem verify_ct (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    ConstantTime isa
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)).pre
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)).pub verifyP256 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  apply nafVerify_public_ct (p256_ok hI) (by decide) hL hT nafVerify_checks
    _ _ _ _ _ _ (jacPre_of (implies.pre _ pre₁)) (jacPre_of (implies.pre _ pre₂)) (jacPublic_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    Verified AArch64.target verifyP256
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct hL hI hT, implies.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := jacVerify_a64 hL hI hT s (implies.pre _ hs)
  exact ⟨t, s', he, ha, implies.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.AArch64

end
