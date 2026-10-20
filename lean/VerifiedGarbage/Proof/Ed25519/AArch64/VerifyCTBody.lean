module

import VerifiedGarbage.Proof.Ed25519.AArch64.WindowCT
public import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyContext
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import VerifiedGarbage.Proof.Ed25519.Recover
public import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverPoint
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
public import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
meta import VerifiedGarbage.Proof.Ed25519.AArch64.WindowCT
meta import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyContext
meta import VerifiedGarbage.Proof.Ed25519.Group.Extended
meta import VerifiedGarbage.Proof.Ed25519.Recover
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyPoints
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverPoint
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointEncode
meta import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block

/-! Merged from `Proof.Ed25519.AArch64.VerifyCTPublic`. -/

@[expose] public section

section
/-! The verification inputs are public, and the equation's trace depends on them alone. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

structure VerifyPublic (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr) (s : State) : Prop where
  context : VerifyContext s base pk sig challenge
  pkBytes : Spec.Ed25519.bytesAt s.mem pk 32 = pkbs
  rBytes : Spec.Ed25519.bytesAt s.mem sig 32 = rbs
  sBytes : Spec.Ed25519.bytesAt s.mem (off sig 32) 32 = sbs
  kBytes : Spec.Ed25519.bytesAt s.mem challenge 64 = kbs
  /-- The static's address, the same in both runs. -/
  sym : s.syms bSym = T

theorem VerifyPublic.of_keep {base pk sig challenge : Addr} {pkbs rbs sbs kbs : List Byte} {T : Addr} {s t : State}
    (h : VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s) (kt : VerifyKeep base s t)
    (hy : t.syms = s.syms) :
    VerifyPublic base pk sig challenge pkbs rbs sbs kbs T t :=
  ⟨h.context.of_keep kt hy, (verifyKeep_bytes kt h.context.pkFar).trans h.pkBytes,
    (verifyKeep_bytes kt h.context.rFar).trans h.rBytes,
    (verifyKeep_bytes kt h.context.scalarFar).trans h.sBytes,
    (verifyKeep_bytes kt h.context.challengeFar).trans h.kBytes, by rw [hy]; exact h.sym⟩

def PointsCTPre (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr)
    (a r : Spec.Ed25519.Point) (s : State) : Prop :=
  VerifyPublic base pk sig challenge pkbs rbs sbs kbs T s ∧
    tablePoint s.mem base 7424 = a ∧ tablePoint s.mem base 7552 = r

theorem verifyEquationPoints_ct (base pk sig challenge : Addr) (pkbs rbs sbs kbs : List Byte) (T : Addr)
    (a r : Spec.Ed25519.Point) {Aa Ra : EPoint dZ} (hA : Rep a Aa) (hR : Rep r Ra) :
    CT (fun s t => PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r s ∧
      PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r t) verifyEquationPoints (fun _ _ => True) := by
  let K := Spec.Ed25519.decodeLE kbs
  let S := Spec.Ed25519.decodeLE sbs
  let R₀ : State → Prop := fun s₀ => tablePoint s₀.mem base 7552 = r
  have w (x : State) (h : PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r x) :
      WP isa (.seq windowPrep (.block nibbles)) x (SkipRun R₀ base Aa K S 64) := by
    have c := h.1.context
    refine WP.mono (windowStart_ok (Aa := Aa) c.scratch c.sigHeader c.challengeHeader c.scalarQ
      c.scalarFar c.challengeQ c.challengeFar (by rw [h.2.1]; exact hA) c.tbl) fun e ⟨we, _, eR⟩ => ?_
    rw [h.1.kBytes, h.1.sBytes] at we
    exact ⟨e, eR.trans h.2.2, we, Nat.div_eq_of_lt we.kLt, by decide, by decide⟩
  have wp (x : State) (h : PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r x) :
      WP isa windowPrep x (NibPre base sig challenge) := by
    have c := h.1.context
    refine WP.mono (windowPrep_ok (Aa := Aa) c.scratch c.sigHeader c.challengeHeader
      (by rw [h.2.1]; exact hA) c.tbl) fun e he => ?_
    exact ⟨he.scratch, he.kHeader, he.sHeader, by rw [he.keep.rd, he.keep.wr]; exact c.challengeQ,
      by rw [he.keep.rd, he.keep.wr]; exact c.scalarQ, c.challengeFar, c.scalarFar⟩
  have wn (x : State) (h : LoopRun R₀ base Aa K S 0 x) :
      WP isa (.block negR) x (EqRepPre base (K • Aa + S • (-baseAff)) (-Ra)) := by
    obtain ⟨s₀, r₀, hx⟩ := h
    have gv := hx.value
    simp only [pow_zero, Nat.div_one] at gv
    refine WP.mono (negR_ok hx.ctx.scratch) fun u ⟨ku, u0, u4⟩ =>
      ⟨ku.scr hx.ctx.scratch, by rw [u0]; exact gv, ?_⟩
    rw [u4, win_tablePoint hx.keep.mem (by decide) (by decide), r₀]
    exact hR.neg.proj
  have prepCT : CT (fun x y => PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r x ∧
      PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r y) windowPrep (fun _ _ => True) := by
    rw [windowPrep]
    refine CT.taintS (L := [bSym]) (Taint.ofRegs [.x0]) (fun x y h => ⟨agree_x0
      (h.1.1.context.scratch.x0.trans h.2.1.context.scratch.x0.symm), fun n hn => ?_⟩) (by taint_decide)
    simp only [List.mem_singleton] at hn
    subst hn
    exact h.1.1.sym.trans h.2.1.sym.symm
  have startCT : CT (fun x y => PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r x ∧
      PointsCTPre base pk sig challenge pkbs rbs sbs kbs T a r y) (.seq windowPrep (.block nibbles))
      (fun _ _ => True) :=
    seq_same prepCT wp nibbles_ct
  have negRCT : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block negR) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)
  rw [verifyEquationPoints]
  apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc; apply RelCT.assoc
  refine CT.seq ((CT.wp startCT fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h)
    (fun _ _ h => h.2)) ?_
  refine CT.seq skipZero_ct ?_
  refine CT.seq (fun x y tx ty x' y' ⟨hsp, c, hc64, hc128, hx, hy⟩ ex ey =>
    windowsA_ct hc64 hc128 x y tx ty x' y' ⟨hsp, hx, hy⟩ ex ey) ?_
  refine CT.seq loopB_ct ?_
  exact seq_same (x0_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.x0) negRCT) wn
    (pointEqualRep_ct base _ _)

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.RecoverCTRoot`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.RecoverCTSign`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.RecoverCTAdjust`. -/
section
/-! Sign adjustment branches only on the shared public coordinate and sign. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def SignCTPre (base : Addr) (b : Bool) (x : Spec.X25519.Fe) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = signWord b ∧ env s.mem base 0 = x

theorem parityBlock_ok {s : State} {base : Addr} (hs : Scr s base)
    (b : Bool) (hb : s.gpr .x1 = signWord b) :
    WP isa (.block (freeze (offset 0) ++ recoverParity)) s fun t =>
      Keep base s t ∧ eval (.zero .x .x8) t = some (((env s.mem base 0).val % 2 == 1) == b) := by
  rw [WP.block_append_iff]
  refine WP.mono (freezeField_ok hs 0) fun a ⟨ax, ka⟩ => ?_
  refine WP.mono (recoverParity_ok b ((ka.gpr _ (by decide)).trans hb)) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(Keep.of_keeps ka (by decide)).trans (Keep.of_keeps kt (by decide)), ?_⟩
  change some (t.gpr .x8 == 0) = _
  rw [tz, ax]

theorem adjustTail_ct (base : Addr) :
    CT (fun x y => Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y)
      (.seq (.ite (.zero .x .x8) (.block []) (.block (fieldCode [.const 5 0, .sub 0 5 0])))
        (.block recoverSuccess)) (fun _ _ => True) := by
  refine CT.seq (R := fun x y => x.gpr .x0 = base ∧ y.gpr .x0 = base)
    (CT.ite (fun _ _ h => h.2.2) ?_ ?_) (successBlock_ct base)
  · have ht : CT (fun _ _ => True) (.block []) (fun _ _ => True) := by
      apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
      exact fun _ _ _ => agree_ofRegs (by simp)
    have hw := CT.wp (ht.mono (fun _ _ _ => trivial) (fun _ _ h => h))
      (fun x y (h : (Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y) ∧ isa.eval (.zero .x .x8) x = some true) =>
        And.intro (WP.block_nil h.1.1.x0) (WP.block_nil h.1.2.1.x0))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)
  · have ht := (negateBlock_ct base).mono
      (fun x y (h : (Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y) ∧ isa.eval (.zero .x .x8) x = some false) =>
        ⟨h.1.1.x0, h.1.2.1.x0⟩) (fun _ _ h => h)
    have hw := CT.wp ht
      (fun x y (h : (Scr x base ∧ Scr y base ∧ eval (.zero .x .x8) x = eval (.zero .x .x8) y) ∧ isa.eval (.zero .x .x8) x = some false) =>
        And.intro (WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.1) fun _ k => (k.1.scr h.1.1).x0)
          (WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] h.1.2.1) fun _ k => (k.1.scr h.1.2.1).x0))
    exact hw.mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem recoverAdjustSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      recoverAdjustSign (fun _ _ => True) := by
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (freeze (offset 0) ++ recoverParity)) s fun t =>
        Scr t base ∧ eval (.zero .x .x8) t = some ((x.val % 2 == 1) == b) := by
    refine WP.mono (parityBlock_ok h.1 b h.2.1) fun t ⟨kt, tz⟩ => ?_
    exact ⟨kt.scr h.1, by rw [tz, h.2.2]⟩
  have ht := (parityBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.x0, h.2.1.x0⟩)
    (fun _ _ h => h)
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverAdjustSign]
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h =>
    ⟨h.2.1.1, h.2.2.1, h.2.1.2.trans h.2.2.2.symm⟩)) (adjustTail_ct base)

end VG.Proof.Ed25519.AArch64
end

/-! The negative-zero check leaks only the public coordinate and sign. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem testThenSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.ite (.nonzero .x .x1) recoverInvalid recoverAdjustSign) (fun _ _ => True) := by
  refine CT.ite ?_ ?_ ?_
  · intro s t h
    simp only [eval, read_x, h.1.2.1, h.2.2.1]
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono (fun _ _ h => h.1) (fun _ _ h => h)

theorem recoverSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      recoverSign (fun _ _ => True) := by
  have ht := (zeroBlock_ct base).mono
    (fun _ _ (h : SignCTPre base b x _ ∧ SignCTPre base b x _) => ⟨h.1.1.x0, h.2.1.x0⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (fieldZero 0)) s fun t =>
        SignCTPre base b x t ∧ eval (.zero .x .x8) t = some (decide (x = 0)) := by
    refine WP.mono (fieldZero_ok h.1 0) fun t ⟨tz, kt, tm⟩ => ?_
    refine ⟨⟨kt.scr h.1, (kt.gpr _ (by decide)).trans h.2.1, ?_⟩, ?_⟩
    · rw [tm]; exact h.2.2
    · change some (t.gpr .x8 == 0) = _
      rw [tz, h.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverSign]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · intro s t h
    exact h.2.1.2.trans h.2.2.2.symm
  · exact (testThenSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact (recoverAdjustSign_ct base b x).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64
end

/-! The two square-root checks branch on public field values. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def RootCTState (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  SignCTPre base b (rootX y) s ∧
    env s.mem base 11 = rootV y * rootX y * rootX y ∧
    env s.mem base 6 = rootU y ∧ env s.mem base 12 = 0 - rootU y

def rootCheckValue (y : Spec.X25519.Fe) (minus : Bool) : Bool :=
  decide (rootV y * rootX y * rootX y = if minus then 0 - rootU y else rootU y)

theorem rootCheck_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (minus : Bool) :
    CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.block (fieldEqual 11 (if minus then 12 else 6)))
      (fun s t => (RootCTState base b y s ∧ eval (.zero .x .x8) s = some (rootCheckValue y minus)) ∧
        (RootCTState base b y t ∧ eval (.zero .x .x8) t = some (rootCheckValue y minus))) := by
  have ht : CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.block (fieldEqual 11 (if minus then 12 else 6))) (fun _ _ => True) := by
    cases minus
    · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
      exact fun _ _ h => x0_agree h.1.1.1.x0 h.2.1.1.x0
    · apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
      exact fun _ _ h => x0_agree h.1.1.1.x0 h.2.1.1.x0
  have hw (s : State) (h : RootCTState base b y s) :
      WP isa (.block (fieldEqual 11 (if minus then 12 else 6))) s fun t =>
        RootCTState base b y t ∧ eval (.zero .x .x8) t = some (rootCheckValue y minus) := by
    refine WP.mono (fieldEqual_ok h.1.1 11 (if minus then 12 else 6)) fun t ⟨tz, kt, te⟩ => ?_
    refine ⟨⟨⟨kt.scr h.1.1, (kt.gpr _ (by decide)).trans h.1.2.1,
      (te 0 (by decide)).trans h.1.2.2⟩, (te 11 (by decide)).trans h.2.1,
      (te 6 (by decide)).trans h.2.2.1, (te 12 (by decide)).trans h.2.2.2⟩, ?_⟩
    change some (t.gpr .x8 == 0) = _
    rw [tz, rootCheckValue, h.2.1]
    cases minus <;> simp only [Bool.false_eq_true, ite_false, ite_true, h.2.2.1, h.2.2.2]
  exact (CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem rootAdjustSign_ct (base : Addr) (b : Bool) (x : Spec.X25519.Fe) :
    CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign)
      (fun _ _ => True) := by
  have ht : CT (fun s t => SignCTPre base b x s ∧ SignCTPre base b x t)
      (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0
  have hw (s : State) (h : SignCTPre base b x s) :
      WP isa (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) s fun t =>
        SignCTPre base b (x * Spec.Ed25519.sqrtM1) t := by
    refine WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18] h.1) fun t ⟨kt, te⟩ => ?_
    refine ⟨kt.scr h.1, (kt.gpr _ (by decide)).trans h.2.1, ?_⟩
    rw [te]
    change env s.mem base 0 * Spec.Ed25519.sqrtM1 = _
    rw [h.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2))
    (recoverSign_ct base b (x * Spec.Ed25519.sqrtM1))

theorem recoverMinus_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (.block (fieldEqual 11 12)) (.ite (.zero .x .x8)
        (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign) recoverInvalid))
      (fun _ _ => True) := by
  refine CT.seq (rootCheck_ct base b y true) (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (rootAdjustSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem recoverChecks_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => RootCTState base b y s ∧ RootCTState base b y t)
      (.seq (.block (fieldEqual 11 6)) (.ite (.zero .x .x8) recoverSign
        (.seq (.block (fieldEqual 11 12)) (.ite (.zero .x .x8)
          (.seq (.block (fieldCode [.const 18 Spec.Ed25519.sqrtM1, .mul 0 0 18])) recoverSign) recoverInvalid))))
      (fun _ _ => True) := by
  refine CT.seq (rootCheck_ct base b y false) (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.1.2.trans h.2.2.symm
  · exact (recoverSign_ct base b (rootX y)).mono
      (fun _ _ h => ⟨h.1.1.1.1, h.1.2.1.1⟩) (fun _ _ h => h)
  · exact (recoverMinus_ct base b y).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ _ h => h)

def RecoverCTPre (base : Addr) (b : Bool) (y : Spec.X25519.Fe) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x1 = signWord b ∧ env s.mem base 1 = y

theorem recoverPoint_ct (base : Addr) (b : Bool) (y : Spec.X25519.Fe) :
    CT (fun s t => RecoverCTPre base b y s ∧ RecoverCTPre base b y t)
      recoverPoint (fun _ _ => True) := by
  have ht := (recoverCandidate_ct base).mono
    (fun _ _ (h : RecoverCTPre base b y _ ∧ RecoverCTPre base b y _) => ⟨h.1.1.x0, h.2.1.x0⟩)
    (fun _ _ h => h)
  have hw (s : State) (h : RecoverCTPre base b y s) :
      WP isa recoverCandidate s (RootCTState base b y) := by
    refine WP.mono (recoverCandidate_ok h.1) fun t ⟨kt, tx, _, _, tu, _, tv, tn⟩ => ?_
    refine ⟨⟨kt.scr h.1, (kt.gpr _ (by decide) (by decide)).trans h.2.1, ?_⟩, ?_, ?_, ?_⟩
    · rw [tx, h.2.2]
    · rw [tv, h.2.2]
    · rw [tu, h.2.2]
    · rw [tn, h.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [recoverPoint]
  exact CT.seq (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) (recoverChecks_ct base b y)

end VG.Proof.Ed25519.AArch64
end

/-! Merged from `Proof.Ed25519.AArch64.VerifyCTDecodeA`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.VerifyCTDecodeR`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.DecodedThenCT`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.PointDecodeCT`. -/
section
/-! Canonical point decoding leaks only its public bytes. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


def DecodeCTPre (base p : Addr) (bs : List Byte) (s : State) : Prop :=
  Scr s base ∧ s.gpr .x2 = p ∧
    (∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) ∧ Spec.Ed25519.bytesAt s.mem p 32 = bs

theorem pointDecode_ct (base p : Addr) (bs : List Byte) :
    CT (fun s t => DecodeCTPre base p bs s ∧ DecodeCTPre base p bs t)
      pointDecode (fun _ _ => True) := by
  let b := Spec.Ed25519.decodeLE bs / 2 ^ 255 == 1
  let y := Proof.X25519.toFe (Spec.Ed25519.decodeLE bs % 2 ^ 255)
  have ht : CT (fun s t => DecodeCTPre base p bs s ∧ DecodeCTPre base p bs t)
      (.block pointDecodeLoad) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x2]) _ (by taint_decide)
    intro s t h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.x0.trans h.2.1.x0.symm
    · exact h.1.2.1.trans h.2.2.1.symm
  have hw (s : State) (h : DecodeCTPre base p bs s) :
      WP isa (.block pointDecodeLoad) s fun t => RecoverCTPre base b y t ∧
        eval (.zero .x .x8) t = some (decide (Spec.Ed25519.decodeLE bs % 2 ^ 255 < Spec.X25519.P)) := by
    refine WP.mono (pointDecodeLoad_ok h.1 h.2.1 h.2.2.1) fun t ⟨kt, tb, ty, tz⟩ => ?_
    refine ⟨⟨kt.scratch h.1, ?_, ?_⟩, ?_⟩
    · rw [tb, h.2.2.2]
    · rw [ty, h.2.2.2]
    · change some (t.gpr .x8 == 0) = _
      rw [tz, h.2.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [pointDecode]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.trans h.2.2.2.symm
  · exact (recoverPoint_ct base b y).mono
      (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem decodeResult_flag {base : Addr} {p : Option Spec.Ed25519.Point} {s : State}
    (h : DecodeResult base p s) : s.gpr .x8 = signWord p.isSome := by
  cases p with
  | none => exact h
  | some p => exact h.1

end VG.Proof.Ed25519.AArch64
end

/-! The canonical scalar check depends only on the public signature. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


theorem verifyScalar_ct (base pk sig challenge : Addr) :
    CT (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block verifyScalar) (fun _ _ => True) := by
  have ht : CT (fun s t => VerifyContext s base pk sig challenge ∧ VerifyContext t base pk sig challenge)
      (.block [ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0])
      (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.scratch.x0 h.2.scratch.x0
  have hw (s : State) (h : VerifyContext s base pk sig challenge) :
      WP isa (.block [ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0]) s
        (fun t => t.gpr .x2 = off sig 32) := by
    change WP isa (.block (([ld .x2 7944] : List Instr) ++
      ([.addImm .x .x2 .x2 32] : List Instr) ++ ([.movz .w .x10 0 0] : List Instr))) s _
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (loadPointer_ok h.scratch .x2 7944 (by decide) (by decide)) fun a ⟨ap, _⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (add32_ok a .x2) fun b ⟨bp, _⟩ => ?_
    refine WP.mono (setZeroX10_ok b) fun t ⟨_, kt⟩ => ?_
    have tp := (kt.gpr .x2 (by decide)).trans bp
    rw [tp, ap, h.sigHeader]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have tailCT : CT (fun s t => s.gpr .x2 = off sig 32 ∧ t.gpr .x2 = off sig 32)
      (.block (loadScalarWords ++ scalarSubtract ++ ([.sbcs .x .x8 .x10 .x10] : List Instr))) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x2]) _ (by taint_decide)
    intro s t h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h.1.trans h.2.symm
  change CT _ (.block (([ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0] : List Instr) ++
    (loadScalarWords ++ scalarSubtract ++ ([.sbcs .x .x8 .x10 .x10] : List Instr)))) _
  exact blockAppend_ct (hp.mono (fun _ _ h => h) (fun _ _ h => h.2)) tailCT

end VG.Proof.Ed25519.AArch64
