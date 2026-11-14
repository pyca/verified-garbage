module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtCoefficient
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtBothPowers
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStages
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedFrame
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowHalfCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopyCT
import VerifiedGarbage.Proof.Bignum.Arm.SubModArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT

import VerifiedGarbage.Proof.Bignum.Arm.CrtCoefficientMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.Bignum.Arm.R2
import VerifiedGarbage.Impl.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.MontOp
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.MontEncode
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperand
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Arm.CrtImportQResidue
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowEnter
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtSavedSources
import VerifiedGarbage.Proof.Bignum.Arm.CrtAcceptedFactors
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowCopy
import VerifiedGarbage.Proof.Bignum.Arm.SubModArray
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.CrtLayout
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
/-! # The CRT recombination coefficient, at p's own width, matches the signed RSA specification -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/MontMixedProduct.lean`, which only this module imported.
section

/-! # Multiply an ordinary operand by a Montgomery-encoded operand -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem montMixedProduct_ok (s : State) {base : BitVec 32} {len w o a b M x y : Nat}
    (h : ArithmeticReady base len w s) (ho : Operand o) (ha : Operand a) (hb : Operand b) (ho0 : o ≠ 0)
    (modulus : numAt s.mem (State.addr base) w 0 = M) (odd : M % 2 = 1)
    (first : numAt s.mem (State.addr base) w a = x)
    (second : numAt s.mem (State.addr base) w b = y * 2 ^ (64 * w) % M) :
    WP isa (montOp o a b) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = M ∧ numAt t.mem (State.addr base) w o = x * y % M ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have positive : 0 < M := by have := h.modulus; rw [modulus] at this; omega
  refine WP.mono (montOp_ok s h ho ha hb ho0 (by rw [modulus, second]; exact Nat.mod_lt _ positive)) ?_
  rintro t ⟨ready, modT, bound, value, keeps, frame, rest⟩
  rw [modulus] at modT bound value
  rw [first, second, Nat.mul_mod_mod, ← Nat.mul_assoc] at value
  have result := mont_cancel (coprime_pow2 odd (64 * w)) value
  rw [Nat.mod_eq_of_lt bound] at result
  exact ⟨ready, modT, result, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt arrAt Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

/-- p prepared at its own width in the narrow workspace, and in p's full-width
workspace `m_p` (array 6), `m_q` (array 1), `qInv` (array 4) and a cleared array 5. -/
structure CrtCoefficientInput (g : CrtGeometry) (bs : Fin 7 → List Byte) (v P a b qi : Nat) (s : State) : Prop where
  ctx : CrtCopyCtx g bs (crtP g.base g.words) 224 v s
  modulus : numAt s.mem (State.addr (crtN g.base g.words)) v 0 = P
  odd : P % 2 = 1
  r2 : numAt s.mem (State.addr (crtN g.base g.words)) v 4 = 2 ^ (128 * v) % P
  half : g.words ≤ 2 * v
  residue : numAt s.mem (State.addr (crtP g.base g.words)) g.words 6 = a
  bound : a < P
  other : numAt s.mem (State.addr (crtP g.base g.words)) g.words 1 = b
  inverse : numAt s.mem (State.addr (crtP g.base g.words)) g.words 4 = qi
  cleared : val32 s.mem (State.addr (crtP g.base g.words)) (arrAt g.words 5) (2 * g.words + 2) = 0

theorem crt_coefficient_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {v P a b qi : Nat}
    (h : CrtCoefficientInput g bs v P a b qi s) :
    WP isa coefficient s fun t => CrtShared g bs t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 5 = ((((a : Int) - b) * qi) % (P : Int)).toNat ∧
      Frame [⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩,
        ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have kind : CrtChild g (crtP g.base g.words) 224 := Or.inl ⟨rfl, rfl⟩
  have ctx := h.ctx
  have le := ctx.le
  have fitsN : arrAt v 8 ≤ 8 * workspaceWords g.words := ctx.ready.width ▸ ctx.ready.layout.2.2.1
  have fitsC : arrAt g.words 8 ≤ 8 * workspaceWords g.words := ctx.shared.buffers.context.arraysFit
  have end5 := Nat.le_trans (array_end_le (w := g.words) (by decide : 5 < 8)) fitsC
  have words : g.words ≤ 128 := (crt_width_valid ctx.shared.buffers.lengthValid).2.1
  have wsSmall : workspaceWords g.words ≤ 16 * 128 + 64 := by simp only [workspaceWords]; omega_using [words]
  have op : ∀ q, q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 5 ∨ q = 6 → Operand q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have positive : 0 < P := by have := ctx.ready.modulus; rw [h.modulus] at this; omega_using [this]
  have pSmall : P < 2 ^ (64 * v) := by rw [← h.modulus]; exact numAt_lt_pow _ _ _ _
  -- `qInv mod p`, kept in the full array 4.
  rw [coefficient, inverseHalf, WP.seq_iff, WP.seq_iff]
  refine WP.mono (crt_reduceHalf_ok s ctx (j := 4) (by decide) h.half h.modulus h.odd h.r2) ?_
  rintro s1 ⟨ready1, mod1, r21, _, inv1, frame1, rest1⟩
  rw [h.inverse] at inv1
  have ctx1 := ctx.after_narrow ready1 frame1 rest1
  have eq1 := ctx.child_eq frame1
  refine WP.mono (crt_copyOut_ok s1 ctx1 (j := 4) (a := 1) (by decide) (by decide)) ?_
  rintro s2 ⟨ready2, copied2, outside2, rest2⟩
  obtain ⟨ctx2, keeps2, frame2, eqN2⟩ := ctx1.after_copyOut kind (by decide) ready2 outside2 rest2
  have mod2 := (eqN2.number fitsN (by decide)).trans mod1
  have r22 := (eqN2.number fitsN (by decide)).trans r21
  -- `m_p - m_q mod p` in the narrow array 6.
  rw [differenceHalf, WP.seq_iff, WP.seq_iff]
  refine WP.mono (crt_reduceHalf_ok s2 ctx2 (j := 1) (by decide) h.half mod2 h.odd r22) ?_
  rintro s3 ⟨ready3, mod3, r23, _, other3, frame3, rest3⟩
  rw [keeps_array_num keeps2 fitsC (op 1 (by simp)) (by decide), eq1.number fitsC (by decide), h.other] at other3
  have ctx3 := ctx2.after_narrow ready3 frame3 rest3
  have eq3 := ctx2.child_eq frame3
  rw [WP.seq_iff]
  refine WP.mono (crt_copyLow_ok s3 ctx3 (j := 6) (d := 5) (by decide) (by decide) (by decide)) ?_
  rintro s4 ⟨ready4, residue4, keeps4, frame4, rest4⟩
  rw [eq3.number fitsC (by decide), keeps_array_num keeps2 fitsC (op 6 (by simp)) (by decide),
    eq1.number fitsC (by decide), h.residue, Nat.mod_eq_of_lt (Nat.lt_trans h.bound pSmall)] at residue4
  have mod4 := (keeps_array_num keeps4 fitsN (op 0 (by simp)) (by decide)).trans mod3
  have other4 := (keeps_array_num keeps4 fitsN (op 1 (by simp)) (by decide)).trans other3
  refine WP.mono (subModArray_ok s4 ready4 (o := 6) (a := 5) (b := 1) (op 6 (by simp)) (op 5 (by simp))
    (op 1 (by simp)) (by decide) (by decide) (by decide) (by rw [residue4, mod4]; exact h.bound)
    (by rw [other4, mod4]; exact Nat.mod_lt _ positive)) ?_
  rintro s5 ⟨ready5, diff5, keeps5, frame5, rest5⟩
  rw [residue4, mod4, other4] at diff5
  have mod5 := (keeps_array_num keeps5 fitsN (op 0 (by simp)) (by decide)).trans mod4
  have r25 := (keeps_array_num keeps5 fitsN (op 4 (by simp)) (by decide)).trans
    ((keeps_array_num keeps4 fitsN (op 4 (by simp)) (by decide)).trans r23)
  have frame35 : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s3.mem s5.mem :=
    frame4.trans frame5
  have ctx5 := ctx3.after_narrow ready5 frame35 (rest4.trans rest5)
  have eq35 := ctx3.child_eq frame35
  -- The product with `qInv mod p` in Montgomery form, into the full array 5.
  rw [productHalf, WP.seq_iff]
  refine WP.mono (crt_copyLow_ok s5 ctx5 (j := 4) (d := 1) (by decide) (by decide) (by decide)) ?_
  rintro s6 ⟨ready6, inv6, keeps6, frame6, rest6⟩
  have inv6' : numAt s6.mem (State.addr (crtN g.base g.words)) v 1 = qi % P := by
    rw [inv6, eq35.number fitsC (by decide), eq3.number fitsC (by decide)]
    change (s2.mem.read (off (State.addr (crtP g.base g.words)) (arrAt g.words 4)) (8 * g.words)).toNat % _ = _
    rw [← (read_split le).1, copied2]
    exact inv1
  have mod6 := (keeps_array_num keeps6 fitsN (op 0 (by simp)) (by decide)).trans mod5
  have r26 := (keeps_array_num keeps6 fitsN (op 4 (by simp)) (by decide)).trans r25
  have diff6 := (keeps_array_num keeps6 fitsN (op 6 (by simp)) (by decide)).trans diff5
  rw [WP.seq_iff]
  refine WP.mono (montEncode_ok s6 ready6 (op 1 (by simp)) (op 1 (by simp)) (by decide) mod6 h.odd r26) ?_
  rintro s7 ⟨ready7, mod7, enc7, keeps7, frame7, rest7⟩
  rw [inv6'] at enc7
  have diff7 := (keeps_array_num keeps7 fitsN (op 6 (by simp)) (by decide)).trans diff6
  rw [WP.seq_iff]
  refine WP.mono (montMixedProduct_ok s7 ready7 (op 5 (by simp)) (op 6 (by simp)) (op 1 (by simp)) (by decide)
    mod7 h.odd diff7 enc7) ?_
  rintro s8 ⟨ready8, _, value8, _, frame8, rest8⟩
  have frame58 : Frame [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s5.mem s8.mem :=
    frame6.trans (frame7.trans frame8)
  have ctx8 := ctx5.after_narrow ready8 frame58 (rest6.trans (rest7.trans rest8))
  have eq58 := ctx5.child_eq frame58
  refine WP.mono (crt_copyOut_ok s8 ctx8 (j := 5) (a := 5) (by decide) (by decide)) ?_
  rintro t ⟨_, copied, outside, restT⟩
  obtain ⟨ctxT, _, frameT, _⟩ := ctx8.after_copyOut kind (by decide) (by assumption) outside restT
  have cleared8 : val32 s8.mem (State.addr (crtP g.base g.words)) (arrAt g.words 5) (2 * g.words + 2) = 0 := by
    rw [← read_eq_val32, eq58.read _ _ (by omega_using [end5]), eq35.read _ _ (by omega_using [end5]), eq3.read _ _ (by omega_using [end5]), read_eq_val32,
      outside2.val32 (Or.inr (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_using [le])) (by omega_using [end5, wsSmall])]
    rw [← read_eq_val32, eq1.read _ _ (by omega_using [end5]), read_eq_val32]
    exact h.cleared
  refine ⟨ctxT.shared, ?_, ?_, ?_⟩
  · rw [numAt_of_copied le cleared8 outside (by omega_using [end5, wsSmall]), copied]
    change numAt s8.mem _ v 5 = _
    rw [value8, Nat.mul_mod_mod, crt_coefficient_value positive]
  · exact (frame1.mono (by simp)).trans ((frame2.mono (by simp)).trans ((frame3.mono (by simp)).trans
      ((frame35.mono (by simp)).trans ((frame58.mono (by simp)).trans (frameT.mono (by simp))))))
  · exact rest1.trans (rest2.trans (rest3.trans ((rest4.trans rest5).trans ((rest6.trans (rest7.trans rest8)).trans restT))))

section
variable (g : CrtGeometry) (bs : Fin 7 → List Byte) (v : Nat)

/-- The coefficient's stages in one run, for its timing: p prepared at its width, with `m_p` below it. -/
def CoeffHalf (s : State) : Prop :=
  ∃ M, CrtHalfReady g bs (crtP g.base g.words) 224 v M s ∧ numAt s.mem (State.addr (crtP g.base g.words)) g.words 6 < M
/-- The same, with the reduced `m_q` in the narrow array 1. -/
def CoeffOther (s : State) : Prop :=
  CoeffHalf g bs v s ∧ numAt s.mem (State.addr (crtN g.base g.words)) v 1 < numAt s.mem (State.addr (crtN g.base g.words)) v 0
/-- `m_p` and the reduced `m_q` in the narrow arrays 5 and 1. -/
def CoeffBoth (s : State) : Prop :=
  (∃ M, CrtHalfReady g bs (crtP g.base g.words) 224 v M s) ∧
    numAt s.mem (State.addr (crtN g.base g.words)) v 1 < numAt s.mem (State.addr (crtN g.base g.words)) v 0 ∧
    numAt s.mem (State.addr (crtN g.base g.words)) v 5 < numAt s.mem (State.addr (crtN g.base g.words)) v 0
/-- p prepared at its width. -/
def CoeffReady (s : State) : Prop := ∃ M, CrtHalfReady g bs (crtP g.base g.words) 224 v M s
/-- The same, with an operand below p in the narrow array 1. -/
def CoeffEncoded (s : State) : Prop :=
  CoeffReady g bs v s ∧
    numAt s.mem (State.addr (crtN g.base g.words)) v 1 < numAt s.mem (State.addr (crtN g.base g.words)) v 0

end

theorem crt_coefficient_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} {v : Nat} :
    RelCT isa (fun s t => CoeffHalf g bs1 v s ∧ CoeffHalf g bs2 v t ∧ s.sp = t.sp) coefficient (fun _ _ => True) := by
  have kind : CrtChild g (crtP g.base g.words) 224 := Or.inl ⟨rfl, rfl⟩
  have op : ∀ q, q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 5 ∨ q = 6 → Operand q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  let N := State.addr (crtN g.base g.words)
  let Pf := State.addr (crtP g.base g.words)
  have fitsC (s : State) {bs : Fin 7 → List Byte} {M : Nat} (h : CrtHalfReady g bs (crtP g.base g.words) 224 v M s) :
      arrAt g.words 8 ≤ 8 * workspaceWords g.words := h.1.shared.buffers.context.arraysFit
  have fitsN (s : State) {bs : Fin 7 → List Byte} {M : Nat} (h : CrtHalfReady g bs (crtP g.base g.words) 224 v M s) :
      arrAt v 8 ≤ 8 * workspaceWords g.words := h.1.ready.width ▸ h.1.ready.layout.2.2.1
  -- The steps in each run.
  have w1 (s : State) {bs : Fin 7 → List Byte} (h : CoeffHalf g bs v s) : WP isa (reduceHalf 224 4) s (CoeffHalf g bs v) := by
    obtain ⟨M, h, lt⟩ := h
    refine (crt_reduceHalf_ok s h.1 (j := 4) (by decide) h.2.2.2.2 h.2.1 h.2.2.1 h.2.2.2.1).mono ?_
    rintro t ⟨ready, mod, r2, _, _, frame, rest⟩
    exact ⟨M, ⟨h.1.after_narrow ready frame rest, mod, h.2.2.1, r2, h.2.2.2.2⟩,
      by rw [h.1.child_num (by decide) frame]; exact lt⟩
  have w2 (s : State) {bs : Fin 7 → List Byte} (h : CoeffHalf g bs v s) : WP isa (copyOut 224 4 1) s (CoeffHalf g bs v) := by
    obtain ⟨M, h, lt⟩ := h
    refine (crt_copyOut_ok s h.1 (j := 4) (a := 1) (by decide) (by decide)).mono ?_
    rintro t ⟨ready, _, outside, rest⟩
    obtain ⟨ctx, keeps, _, eqN⟩ := h.1.after_copyOut kind (by decide) ready outside rest
    exact ⟨M, ⟨ctx, (eqN.number (fitsN s h) (by decide)).trans h.2.1, h.2.2.1,
      (eqN.number (fitsN s h) (by decide)).trans h.2.2.2.1, h.2.2.2.2⟩,
      by rw [keeps_array_num keeps (fitsC s h) (op 6 (by simp)) (by decide)]; exact lt⟩
  have w3 (s : State) {bs : Fin 7 → List Byte} (h : CoeffHalf g bs v s) : WP isa (reduceHalf 224 1) s (CoeffOther g bs v) := by
    obtain ⟨M, h, lt⟩ := h
    have positive : 0 < M := by have := h.1.ready.modulus; rw [h.2.1] at this; omega_using [lt]
    refine (crt_reduceHalf_ok s h.1 (j := 1) (by decide) h.2.2.2.2 h.2.1 h.2.2.1 h.2.2.2.1).mono ?_
    rintro t ⟨ready, mod, r2, _, value, frame, rest⟩
    exact ⟨⟨M, ⟨h.1.after_narrow ready frame rest, mod, h.2.2.1, r2, h.2.2.2.2⟩,
      by rw [h.1.child_num (by decide) frame]; exact lt⟩, by rw [value, mod]; exact Nat.mod_lt _ positive⟩
  have w4 (s : State) {bs : Fin 7 → List Byte} (h : CoeffOther g bs v s) : WP isa (copyLow 224 6 5) s (CoeffBoth g bs v) := by
    obtain ⟨⟨M, h, lt⟩, other⟩ := h
    refine (crt_copyLow_ok s h.1 (j := 6) (d := 5) (by decide) (by decide) (by decide)).mono ?_
    rintro t ⟨ready, value, keeps, frame, rest⟩
    have mod := (keeps_array_num keeps (fitsN s h) (op 0 (by simp)) (by decide)).trans h.2.1
    refine ⟨⟨M, ⟨h.1.after_narrow ready frame rest, mod, h.2.2.1,
      (keeps_array_num keeps (fitsN s h) (op 4 (by simp)) (by decide)).trans h.2.2.2.1, h.2.2.2.2⟩⟩,
      by rw [keeps_array_num keeps (fitsN s h) (op 1 (by simp)) (by decide),
        keeps_array_num keeps (fitsN s h) (op 0 (by simp)) (by decide)]; exact other, ?_⟩
    rw [value, mod]
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) lt
  have w5 (s : State) {bs : Fin 7 → List Byte} (h : CoeffBoth g bs v s) : WP isa (subModArray 6 5 1) s (CoeffReady g bs v) := by
    obtain ⟨⟨M, h⟩, one, five⟩ := h
    refine (subModArray_ok s h.1.ready (o := 6) (a := 5) (b := 1) (op 6 (by simp)) (op 5 (by simp)) (op 1 (by simp))
      (by decide) (by decide) (by decide) five one).mono ?_
    rintro t ⟨ready, _, keeps, frame, rest⟩
    exact ⟨M, h.after ready keeps (by simp) frame rest⟩
  have w6 (s : State) {bs : Fin 7 → List Byte} (h : CoeffReady g bs v s) : WP isa (copyLow 224 4 1) s (CoeffReady g bs v) := by
    obtain ⟨M, h⟩ := h
    refine (crt_copyLow_ok s h.1 (j := 4) (d := 1) (by decide) (by decide) (by decide)).mono ?_
    rintro t ⟨ready, _, keeps, frame, rest⟩
    exact ⟨M, h.after ready keeps (by simp) frame rest⟩
  have w7 (s : State) {bs : Fin 7 → List Byte} (h : CoeffReady g bs v s) : WP isa (montOp 1 1 4) s (CoeffEncoded g bs v) := by
    obtain ⟨M, h⟩ := h
    refine (montOp_ok s h.1.ready (op 1 (by simp)) (op 1 (by simp)) (op 4 (by simp)) (by decide) h.r2_lt).mono ?_
    rintro t ⟨ready, mod, bound, _, keeps, frame, rest⟩
    exact ⟨⟨M, h.after ready keeps (by simp) frame rest⟩, by rw [mod]; exact bound⟩
  have w8 (s : State) {bs : Fin 7 → List Byte} (h : CoeffEncoded g bs v s) :
      WP isa (montOp 5 6 1) s (CrtCopyCtx g bs (crtP g.base g.words) 224 v) := by
    obtain ⟨⟨M, h⟩, one⟩ := h
    refine (montOp_ok s h.1.ready (op 5 (by simp)) (op 6 (by simp)) (op 1 (by simp)) (by decide) one).mono ?_
    rintro t ⟨ready, _, _, _, _, frame, rest⟩
    exact h.1.after_narrow ready frame rest
  -- Each step in both runs.
  have half (P : State → Prop) (hP : ∀ s, P s → ∃ M, CrtHalfReady g bs1 (crtP g.base g.words) 224 v M s)
      (Q : State → Prop) (hQ : ∀ s, Q s → ∃ M, CrtHalfReady g bs2 (crtP g.base g.words) 224 v M s) (j : Nat) (hj : j < 8) :
      RelCT isa (fun s t => P s ∧ Q t ∧ s.sp = t.sp) (reduceHalf 224 j) (fun _ _ => True) := by
    intro s t tr1 tr2 u w h e1 e2
    obtain ⟨M1, h1⟩ := hP s h.1
    obtain ⟨M2, h2⟩ := hQ t h.2.1
    exact crt_reduceHalf_ct hj s t tr1 tr2 u w ⟨h1, h2, h.2.2⟩ e1 e2
  have ctxOf {bs : Fin 7 → List Byte} (s : State) (h : ∃ M, CrtHalfReady g bs (crtP g.base g.words) 224 v M s) :
      CrtCopyCtx g bs (crtP g.base g.words) 224 v s := by obtain ⟨_, h⟩ := h; exact h.1
  have size : ∀ s, CoeffReady g bs1 v s → 128 ≤ 8 * workspaceWords g.words := by
    intro s h
    obtain ⟨M, h⟩ := h
    have := fitsN s h
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega_using [this]
  have fit3 : ∀ s, CoeffReady g bs1 v s → arrAt v 3 + 32 ≤ 8 * workspaceWords g.words := by
    intro s h
    obtain ⟨M, h⟩ := h
    have := Nat.le_trans (array_end_le (w := v) (by decide : 3 < 8)) (fitsN s h)
    have := h.1.ready.width ▸ h.1.ready.layout.1
    omega_arith
  intro s₁ s₂ tr1 tr2 u₁ u₂ hh e1 e2
  have r0 : CoeffReady g bs1 v s₁ := by obtain ⟨M, h, _⟩ := hh.1; exact ⟨M, h⟩
  have sz := size s₁ r0
  have f3 := fit3 s₁ r0
  have c1 := half (CoeffHalf g bs1 v) (fun s h => by obtain ⟨M, h, _⟩ := h; exact ⟨M, h⟩)
    (CoeffHalf g bs2 v) (fun s h => by obtain ⟨M, h, _⟩ := h; exact ⟨M, h⟩) 4 (by decide)
  have c2 : RelCT isa (fun s t => CoeffHalf g bs1 v s ∧ CoeffHalf g bs2 v t ∧ s.sp = t.sp) (copyOut 224 4 1)
      (fun _ _ => True) :=
    (crt_copyOut_ct (by decide) (by decide)).mono
      (fun s t h => ⟨ctxOf s (by obtain ⟨M, h, _⟩ := h.1; exact ⟨M, h⟩),
        ctxOf t (by obtain ⟨M, h, _⟩ := h.2.1; exact ⟨M, h⟩), h.2.2⟩) (fun _ _ _ => trivial)
  have c3 := half (CoeffHalf g bs1 v) (fun s h => by obtain ⟨M, h, _⟩ := h; exact ⟨M, h⟩)
    (CoeffHalf g bs2 v) (fun s h => by obtain ⟨M, h, _⟩ := h; exact ⟨M, h⟩) 1 (by decide)
  have c4 : RelCT isa (fun s t => CoeffOther g bs1 v s ∧ CoeffOther g bs2 v t ∧ s.sp = t.sp) (copyLow 224 6 5)
      (fun _ _ => True) :=
    (crt_copyLow_ct (by decide) (by decide)).mono
      (fun s t h => ⟨ctxOf s (by obtain ⟨⟨M, h, _⟩, _⟩ := h.1; exact ⟨M, h⟩),
        ctxOf t (by obtain ⟨⟨M, h, _⟩, _⟩ := h.2.1; exact ⟨M, h⟩), h.2.2⟩) (fun _ _ _ => trivial)
  have c5 : RelCT isa (fun s t => CoeffBoth g bs1 v s ∧ CoeffBoth g bs2 v t ∧ s.sp = t.sp) (subModArray 6 5 1)
      (fun _ _ => True) :=
    (subModArray_ct (by decide) (by decide) (by decide) (by decide) sz).mono
      (fun s t h => ⟨(ctxOf s h.1.1).ready, (ctxOf t h.2.1.1).ready, h.2.2⟩) (fun _ _ _ => trivial)
  have c6 : RelCT isa (fun s t => CoeffReady g bs1 v s ∧ CoeffReady g bs2 v t ∧ s.sp = t.sp) (copyLow 224 4 1)
      (fun _ _ => True) :=
    (crt_copyLow_ct (by decide) (by decide)).mono (fun s t h => ⟨ctxOf s h.1, ctxOf t h.2.1, h.2.2⟩)
      (fun _ _ _ => trivial)
  have c7 : RelCT isa (fun s t => CoeffReady g bs1 v s ∧ CoeffReady g bs2 v t ∧ s.sp = t.sp) (montOp 1 1 4)
      (fun _ _ => True) :=
    (montOp_ct (op 1 (by simp)) (op 1 (by simp)) (op 4 (by simp)) f3).mono
      (fun s t h => ⟨by obtain ⟨M, h⟩ := h.1; exact ⟨h.1.ready, h.r2_lt⟩,
        by obtain ⟨M, h⟩ := h.2.1; exact ⟨h.1.ready, h.r2_lt⟩, h.2.2⟩) (fun _ _ _ => trivial)
  have c8 : RelCT isa (fun s t => CoeffEncoded g bs1 v s ∧ CoeffEncoded g bs2 v t ∧ s.sp = t.sp) (montOp 5 6 1)
      (fun _ _ => True) :=
    (montOp_ct (op 5 (by simp)) (op 6 (by simp)) (op 1 (by simp)) f3).mono
      (fun s t h => ⟨⟨(ctxOf s h.1.1).ready, h.1.2⟩, ⟨(ctxOf t h.2.1.1).ready, h.2.1.2⟩, h.2.2⟩)
      (fun _ _ _ => trivial)
  have c9 : RelCT isa (fun s t => CrtCopyCtx g bs1 (crtP g.base g.words) 224 v s ∧
      CrtCopyCtx g bs2 (crtP g.base g.words) 224 v t ∧ s.sp = t.sp) (copyOut 224 5 5) (fun _ _ => True) :=
    crt_copyOut_ct (by decide) (by decide)
  have inverse := crt_seq_ct c1 (fun s h => w1 s h) (fun s h => w1 s h) c2
  have inverseWP (s : State) {bs : Fin 7 → List Byte} (h : CoeffHalf g bs v s) : WP isa inverseHalf s (CoeffHalf g bs v) :=
    WP.seq_iff.mpr ((w1 s h).mono fun _ k => w2 _ k)
  have difference := crt_seq_ct c3 (fun s h => w3 s h) (fun s h => w3 s h)
    (crt_seq_ct c4 (fun s h => w4 s h) (fun s h => w4 s h) c5)
  have differenceWP (s : State) {bs : Fin 7 → List Byte} (h : CoeffHalf g bs v s) :
      WP isa differenceHalf s (CoeffReady g bs v) :=
    WP.seq_iff.mpr ((w3 s h).mono fun _ k => WP.seq_iff.mpr ((w4 _ k).mono fun _ k' => w5 _ k'))
  have product := crt_seq_ct c6 (fun s h => w6 s h) (fun s h => w6 s h)
    (crt_seq_ct c7 (fun s h => w7 s h) (fun s h => w7 s h) (crt_seq_ct c8 (fun s h => w8 s h) (fun s h => w8 s h) c9))
  have all := crt_seq_ct inverse (fun s h => inverseWP s h) (fun s h => inverseWP s h)
    (crt_seq_ct difference (fun s h => differenceWP s h) (fun s h => differenceWP s h) product)
  exact all s₁ s₂ tr1 tr2 u₁ u₂ hh e1 e2

theorem CrtPoweredState.after_keeps {m m' : Mem} {base : BitVec 32} {len w M value o : Nat}
    (h : CrtPoweredState base len w M value m) (keeps : Keeps (State.addr base) len w o m m')
    (ho0 : 0 ≠ o) (ho6 : 6 ≠ o) : CrtPoweredState base len w M value m' := by
  have fit : arrAt w 8 ≤ 8 * len := h.layout.width ▸ h.layout.layout.2.2.1
  have kl := keeps_layout h.layout.layout (by rw [h.layout.width]; exact keeps)
  exact ⟨⟨kl.2, kl.1.trans h.layout.width⟩, h.positive,
    (keeps_array_num keeps fit (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) ho0).trans h.modulus,
    (keeps_array_num keeps fit (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) ho6).trans h.result⟩

/-- The coefficient phase: p's full workspace takes `m_q` and `qInv`, p is
prepared at its own width, and `h` returns to p's full array 5. -/
theorem crt_coefficientStage_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {Q v1 v2 : Nat}
    (h : CrtShared g bs s) (ready : LayoutFrameReady g.base (workspaceWords g.words) g.words s)
    (p : CrtPoweredState (crtP g.base g.words) (workspaceWords g.words) g.words (crtFactor bs 2) v1 s.mem)
    (q : CrtPoweredState (crtQ g.base g.words) (workspaceWords g.words) g.words Q v2 s.mem)
    (bound : v1 < crtFactor bs 2)
    (flag : s.mem.readW (off (State.addr s.sp) 48) 32 = (if crtAccepted bs then 1 else 0))
    (st : CrtStages) (hst : st.ok g bs) :
    WP isa (CrtFn.coefficientPhaseOf st.prime) s fun t => CrtShared g bs t ∧
      LayoutFrameReady g.base (workspaceWords g.words) g.words t ∧
      numAt t.mem (State.addr (crtP g.base g.words)) g.words 5 =
        ((((v1 : Int) - v2) * Spec.Rsa.os2ip (bs 6)) % (crtFactor bs 2 : Int)).toNat ∧
      CrtPoweredState (crtQ g.base g.words) (workspaceWords g.words) g.words Q v2 t.mem ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame (crtLiveMutable g s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have kind : CrtChild g (crtP g.base g.words) 224 := Or.inl ⟨rfl, rfl⟩
  have memberP : (⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩ : Region) ∈
      crtRegions g.base (workspaceWords g.words) g.words := by simp [crtRegions]
  have memberQ : (⟨State.addr (crtQ g.base g.words), 8 * workspaceWords g.words⟩ : Region) ∈
      crtRegions g.base (workspaceWords g.words) g.words := by simp [crtRegions]
  have fitsC : arrAt g.words 8 ≤ 8 * workspaceWords g.words := h.buffers.context.arraysFit
  have op : ∀ q, q = 0 ∨ q = 1 ∨ q = 4 ∨ q = 6 → Operand q := by
    intro q hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  obtain ⟨two, le, kfit, kpos, _, arrays, half⟩ := h.narrow_fits 1 (Or.inl rfl)
  have words : g.words ≤ 128 := (crt_width_valid h.buffers.lengthValid).2.1
  let v := narrowWords (g.sourceLength (1 : Fin 6).succ) g.words
  have pqFit : g.sourceLength (5 : Fin 6).succ ≤ 8 * g.words := by
    have := h.buffers.pShort; have := (crt_width_valid h.buffers.lengthValid).2.2
    change g.pLength ≤ 8 * Spec.Rsa.modulusWords g.length; omega_arith
  -- p's full workspace selected.
  rw [CrtFn.coefficientPhaseOf, WP.seq_iff]
  refine WP.mono (crt_selectLinked_ready s h h.buffers.context.p h.p memberP
    (by have := h.buffers.context.size; omega_using [this] : 224 + 4 ≤ 8 * workspaceWords g.words)
    (by decide) ready.ptr h.main.p) ?_
  rintro u ⟨sharedU, readyU, frameU, restU⟩
  have pU := p.congr (h.workspace_eq_after_base h.buffers.context.p memberP frameU)
  have qU := q.congr (h.workspace_eq_after_base h.buffers.context.q memberQ frameU)
  have flagU := acceptance_after_base_save frameU restU
  -- `m_q`, `qInv` and a cleared array 5 in p's full workspace.
  rw [WP.seq_iff, CrtFn.coefficientInput]
  apply WP.assoc
  rw [WP.seq_iff]
  refine WP.mono (crt_importQResidue_ok u sharedU readyU pU) ?_
  rintro x1 ⟨shared1, ready1, p1, residue1, frame1, rest1⟩
  rw [qU.result] at residue1
  rw [WP.seq_iff]
  refine WP.mono (savedOperandLayout_ok x1 ready1 (shared1.savedOperand 5 memberP) (o := 4) (by decide)
    h.buffers.pPositive pqFit) ?_
  rintro x2 ⟨ready2, inv2, keeps2, frame2, rest2⟩
  refine WP.mono (clearLayout_ok x2 ready2 (o := 5) (by decide)) ?_
  rintro x3 ⟨ready3, cleared3, keeps3, frame3, rest3⟩
  have frame13 : Frame [⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩] u.mem x3.mem :=
    frame1.trans (frame2.trans frame3)
  have restU3 : Rest roundClobbers u x3 := rest1.trans (rest2.trans rest3)
  have shared3 : CrtShared g bs x3 :=
    sharedU.after_p ((frame1.trans (frame2.trans frame3)).mono (by simp)) restU3 ⟨ready3.layout, ready3.width⟩
  have flag3 := sharedU.acceptance_after_workspace memberP frame13 restU3
  have p6 : numAt x3.mem (State.addr (crtP g.base g.words)) g.words 6 = v1 := by
    rw [keeps_array_num keeps3 fitsC (op 6 (by simp)) (by decide), keeps_array_num keeps2 fitsC (op 6 (by simp))
      (by decide)]; exact p1.result
  have p1' : numAt x3.mem (State.addr (crtP g.base g.words)) g.words 1 = v2 := by
    rw [keeps_array_num keeps3 fitsC (op 1 (by simp)) (by decide), keeps_array_num keeps2 fitsC (op 1 (by simp))
      (by decide)]; exact residue1
  have p4 : numAt x3.mem (State.addr (crtP g.base g.words)) g.words 4 = Spec.Rsa.os2ip (bs 6) := by
    rw [keeps_array_num keeps3 fitsC (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)]
    exact inv2
  have cleared5 := cleared3
  -- p prepared at its own width.
  have sepN : ∀ r ∈ [(⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩ : Region)],
      (⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.buffers.context.sepPN
  rw [WP.seq_iff]
  refine WP.mono (crt_enterNarrow_ok x3 shared3 1 (Or.inl rfl)) ?_
  rintro y1 ⟨sharedY1, selected, flagY1, frameY1, restY1⟩
  have eqY1 := shared3.eq_of_frame shared3.buffers.context.p memberP
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩]) (frameY1.mono (by simp)) sepN
  have flagS : y1.mem.readW (off (State.addr y1.sp) 48) 32 = (if crtAccepted bs then 1 else 0) := by
    rw [flagY1, flag3, flagU, flag]
  have primeIn : NarrowPrimeInput (crtN g.base g.words) (g.source (1 : Fin 6).succ) (workspaceWords g.words) v
      (g.sourceLength (1 : Fin 6).succ) (56 + 8 * (1 : Fin 6).val) (bs (1 : Fin 6).succ) y1 := by
    refine ⟨selected, sharedY1.savedOperand 1 sharedY1.narrow_member, kpos, kfit,
      by have := sharedY1.stack.nowrap; omega_using [this], sharedY1.stack.read (by decide), ?_, ?_⟩
    · rw [flagS]; split <;> decide
    · rw [flagS]
      by_cases accepted : crtAccepted bs
      · intro _; exact (h.accepted_factors accepted).1
      · simp [accepted]
  rw [WP.seq_iff]
  refine WP.mono (st.primeOk 1 y1 (Or.inl rfl) hst ⟨sharedY1, primeIn⟩) ?_
  intro y hy
  obtain ⟨readyY, modY, oddY, r2Y, flagY, frameY, restY⟩ :
    NarrowPrimePost (crtN g.base g.words) (workspaceWords g.words) v (bs (1 : Fin 6).succ) y1 y := hy
  rw [flagS] at modY oddY r2Y
  change numAt _ _ _ 0 = safePrime _ (Spec.Rsa.os2ip (bs 2)) at modY
  rw [crt_safeFactor] at modY oddY r2Y
  have sharedY := sharedY1.after_narrow (frameY.mono (by simp)) restY
  have eqY := sharedY1.eq_of_frame (sharedY1.child kind).2.1 memberP
    (regions := [⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩]) (frameY.mono (by simp)) sepN
  -- The coefficient.
  have input : CrtCoefficientInput g bs v (crtFactor bs 2) v1 v2 (Spec.Rsa.os2ip (bs 6)) y := by
    refine ⟨sharedY.copyCtx kind readyY le, modY, oddY, r2Y, half, ?_, bound, ?_, ?_, ?_⟩
    · rw [eqY.number fitsC (by decide), eqY1.number fitsC (by decide)]; exact p6
    · rw [eqY.number fitsC (by decide), eqY1.number fitsC (by decide)]; exact p1'
    · rw [eqY.number fitsC (by decide), eqY1.number fitsC (by decide)]; exact p4
    · have f5 := Nat.le_trans (array_end_le (w := g.words) (by decide : 5 < 8)) fitsC
      rw [← read_eq_val32, eqY.read _ _ (by omega_using [f5]), eqY1.read _ _ (by omega_using [f5]), read_eq_val32]
      exact cleared5
  rw [WP.seq_iff]
  refine WP.mono (crt_coefficient_ok y input) ?_
  rintro z ⟨sharedZ, valueZ, frameZ, restZ⟩
  refine WP.mono (crt_selectMain_ready z sharedZ) ?_
  rintro t ⟨sharedT, readyT, frameT, restT⟩
  -- What the other workspaces and the stack keep.
  have sepS (r : Region) (hr : r ∈ crtRegions g.base (workspaceWords g.words) g.words) (k : State) (hk : CrtShared g bs k) :
      Region.Disjoint ⟨State.addr k.sp, 112⟩ r :=
    hk.stack.separate.sub_right (crt_region_sub_workspace hk.buffers.workspace hk.buffers.storageFits hr)
  have flagZ : z.mem.readW (off (State.addr z.sp) 48) 32 = y.mem.readW (off (State.addr y.sp) 48) 32 := by
    have eq : WorkspaceEq (State.addr y.sp) 112 y.mem z.mem := WorkspaceEq.of_frame (by decide) frameZ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sepS _ memberP y sharedY
      · exact sepS _ sharedY.narrow_member y sharedY)
    rw [restZ.sp]
    exact eq.word (d := 48) (bits := 32) (by decide)
  have flagT := acceptance_after_base_save frameT restT
  have pEqT := sharedZ.workspace_eq_after_base sharedZ.buffers.context.p memberP frameT
  have rs1 : u.sp = s.sp := restU.sp
  have rs3 : x3.sp = s.sp := restU3.sp.trans rs1
  have rsY1 : y1.sp = s.sp := restY1.sp.trans rs3
  have rsY : y.sp = s.sp := restY.sp.trans rsY1
  have rsZ : z.sp = s.sp := restZ.sp.trans rsY
  rw [rs3] at frameY1
  rw [rsZ] at frameT
  have frameAll : Frame [⟨State.addr s.sp, 4⟩, ⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩,
      ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩] s.mem t.mem :=
    (frameU.mono (by simp)).trans ((frame13.mono (by simp)).trans ((frameY1.mono (by simp)).trans
      ((frameY.mono (by simp)).trans ((frameZ.mono (by simp)).trans (frameT.mono (by simp))))))
  have qEq := h.eq_of_frame h.buffers.context.q memberQ
    (regions := [⟨State.addr (crtP g.base g.words), 8 * workspaceWords g.words⟩,
      ⟨State.addr (crtN g.base g.words), 8 * workspaceWords g.words⟩]) frameAll (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.buffers.context.sepPQ.symm
      · exact h.buffers.context.sepQN)
  refine ⟨sharedT, readyT, (pEqT.number fitsC (by decide)).trans valueZ, q.congr qEq,
    flagT.trans (flagZ.trans (flagY.trans (flagY1.trans (flag3.trans flagU)))), ?_,
    (restU.mono (by decide)).trans (restU3.trans (restY1.trans (restY.trans (restZ.trans (restT.mono (by decide))))))⟩
  apply frameAll.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨State.addr s.sp, 4⟩, by simp [crtLiveMutable], fun _ h => h⟩
  · exact ⟨_, by simp [crtLiveMutable], crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits memberP⟩
  · exact ⟨_, by simp [crtLiveMutable], crt_region_sub_workspace h.buffers.workspace h.buffers.storageFits h.narrow_member⟩

end VG.Proof.Bignum.Arm
