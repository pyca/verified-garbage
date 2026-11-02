module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSquare
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontFnVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! The callable Montgomery primitive shares RSA's accumulator-square kernel.
The dispatch depends only on the three public, 32-bit array indices. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.MontFn
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Impl.Bignum
open VG.Impl.Bignum.AArch64 VG.Impl.Bignum.AArch64.MontFn
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Rsa.Mont (numAt wOf wordAt minvWord)

def tag (o a b : Nat) : BitVec 32 :=
  ((BitVec.ofNat 32 o ^^^ 5#32) ||| (BitVec.ofNat 32 a ^^^ 5#32)) ||| (BitVec.ofNat 32 b ^^^ 5#32)

theorem tag_zero {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8) :
    tag o a b = 0#32 ↔ o = 5 ∧ a = 5 ∧ b = 5 := by
  simp only [tag, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  have eq5 : ∀ n < 8, (BitVec.ofNat 32 n = 5#32 ↔ n = 5) := by
    intro n hn
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      omega
    · rintro rfl; rfl
  rw [eq5 o ho, eq5 a ha, eq5 b hb]
  exact and_assoc

structure TestView (s t : State) : Prop where
  mem : t.mem = s.mem
  x0 : t.gpr .x0 = s.gpr .x0
  x1 : t.gpr .x1 = s.gpr .x1
  x2 : t.gpr .x2 = s.gpr .x2
  x3 : t.gpr .x3 = s.gpr .x3
  x4 : t.gpr .x4 = s.gpr .x4
  flag : (t.gpr .x5).setWidth 32 = tag (idx s .x2) (idx s .x3) (idx s .x4)

theorem test_ok (s : State) : WP isa (.block squareTest) s fun t =>
    TestView s t ∧ Keep [.x5, .x6, .x7] s t := by
  refine WP.keep [.x5, .x6, .x7] ?_ rfl rfl rfl
  unfold squareTest
  brun [exec]
  constructor <;> try rfl
  simp only [tag, ← idx_eq s .x2, ← idx_eq s .x3, ← idx_eq s .x4]
  simp [State.write]


theorem TestView.pre {s t : State} (v : TestView s t) (k : Keep [.x5, .x6, .x7] s t)
    (h : fnContract.pre s) : fnContract.pre t := by
  simpa only [fnContract, idx, k.rd, k.wr, v.mem, v.x0, v.x1, v.x2, v.x3, v.x4] using h

theorem TestView.post {s t u : State} (v : TestView s t)
    (h : fnContract.post t u) : fnContract.post s u := by
  simpa only [fnContract, idx, v.mem, v.x0, v.x1, v.x2, v.x3, v.x4] using h

theorem square_correct (s : State) (h : fnContract.pre s)
    (ho : idx s .x2 = 5) (ha : idx s .x3 = 5) (hb : idx s .x4 = 5) :
    ∃ tr t, Exec isa (VG.Impl.Bignum.AArch64.SquareEightDispatch.mm 5 5 5) s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  obtain ⟨hs, hH, hZ, hw, hw'⟩ := fn_good h
  obtain ⟨-, -, hnw, -, -, -, -, hinv, hB⟩ := h
  rw [hb, numAt_eq, numAt_eq] at hB
  have hp := Mont.squareEight.ok ⟨hs, rfl, hH⟩ hZ hw hw'
    (o := 5) (a := 5) (b := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hinv hB
  obtain ⟨tr, t, he, _, hlt, heq, har, hk⟩ := hp
  refine ⟨tr, t, he, ⟨?_, hk.sp, hk.vcs⟩, ?_, ?_, ?_⟩
  · intro r hr
    exact hk.gpr r (by revert r; decide)
  · rw [ho, numAt_eq, numAt_eq]; exact hlt
  · rw [ho, ha, hb, numAt_eq, numAt_eq, numAt_eq]; exact heq
  · intro i hi hj
    apply har
    intro j hj'
    rw [show ofs (s.gpr .x0) (s.gpr .x0 + BitVec.ofNat 64 i) = i by
      simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
    exact hj j (by simpa only [ho, Public.aAcc, Public.aTmp, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] using hj')

theorem mul_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa mul s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  change WP isa mul s (fun t => abiPreserved s t ∧ fnContract.post s t)
  unfold mul
  refine WP.seq (WP.mono (test_ok s) fun u ⟨v, k⟩ => ?_)
  have hu := v.pre k h
  have finish : ∀ c, WP isa c u (fun t => abiPreserved u t ∧ fnContract.post u t) →
      WP isa c u (fun t => abiPreserved s t ∧ fnContract.post s t) := by
    intro c hc
    refine WP.mono hc fun t ⟨ht, hp⟩ => ⟨?_, v.post hp⟩
    exact ⟨fun r hr => (ht.1 r hr).trans (k.gpr r (by revert r; decide)),
      ht.2.1.trans k.sp, fun r hr => (ht.2.2 r hr).trans (k.vcs r hr)⟩
  have eval : isa.eval (.zero .w .x5) u = some (decide (tag (idx s .x2) (idx s .x3) (idx s .x4) = 0)) := by
    simp only [VG.AArch64.eval, State.read, Size.bits, v.flag]
    congr 1
  refine WP.ite _ eval (fun ht => ?_) (fun _ => finish _ (fn_correct u hu))
  have ht' := of_decide_eq_true ht
  have he := (tag_zero h.2.2.2.2.1.1 h.2.2.2.2.2.1.1 h.2.2.2.2.2.2.1.1).mp ht'
  exact finish _ (square_correct u hu
    (by simpa only [idx, v.x2] using he.1)
    (by simpa only [idx, v.x3] using he.2.1)
    (by simpa only [idx, v.x4] using he.2.2))

/-- The shared guarded kernel is constant time at this valid slot tuple too. -/
theorem row_square_rel : RelCT isa (Two GoodW) (VG.Impl.Bignum.AArch64.Square.montMul 5 5 5) (fun _ _ => True) := by
  unfold VG.Impl.Bignum.AArch64.Square.montMul
  rw [ite_eq_left rfl]
  refine RelCT.seq (two_piece [.x0] pins_goodW (by taint_decide) Square.guard_ctx) ?_
  refine two_ite (Φ := Square.GuardCtx) ?_ ?_ ?_
  · intro L s t hs ht
    rw [VG.Proof.MlKem.AArch64.eval_nonzero, hs.test,
      VG.Proof.MlKem.AArch64.eval_nonzero, ht.test]
  · exact two_map id (fun L s h => ⟨h.1.good, Square.guard_width h.1 h.2⟩)
      (Square.square_ct (by decide) (by decide) (by decide) (by decide)
        (by taint_decide) (by taint_decide))
  · exact two_map id (fun _ _ h => h.1.good)
      (mm_ct (by decide) (by decide) (by decide) (by taint_decide))

/-- The published blocked reducer shares the same workspace and slot contract. -/
theorem blocked_square_rel : RelCT isa (Two GoodW) (VG.Impl.Bignum.AArch64.BlockedRedc.mm 5 5 5) (fun _ _ => True) := by
  unfold VG.Impl.Bignum.AArch64.BlockedRedc.mm
  rw [ite_eq_left (by decide)]
  refine RelCT.seq (two_piece _ pins_goodW (by taint_decide) BlockedRedc.guard_ctx) ?_
  refine two_ite (Φ := BlockedRedc.GuardCtx) ?_ ?_ ?_
  · intro L s t hs ht
    rw [VG.Proof.MlKem.AArch64.eval_nonzero, VG.Proof.MlKem.AArch64.eval_nonzero, hs.width, ht.width]
  · refine two_ite ?_ ?_ ?_
    · intro L s t hs ht
      rw [VG.Proof.MlKem.AArch64.eval_zero, VG.Proof.MlKem.AArch64.eval_zero, hs.1.rem, ht.1.rem]
    · exact two_map id (fun _ _ h => ⟨h.1.1.good, BlockedRedc.guard_width h.1.1 h.1.2,
        BlockedRedc.guard_rem h.1.1 h.2⟩)
        (BlockedRedc.square_ct (by decide) (by decide) (by decide) (by decide)
          (by taint_decide) (by taint_decide) (by taint_decide))
    · exact two_map id (fun _ _ h => h.1.1.good) row_square_rel
  · exact two_map id (fun _ _ h => h.1.good) row_square_rel

/-- Slot 5 uses the scheduled square under the same public width guards. -/
theorem square_rel : RelCT isa (Two GoodW)
    (VG.Impl.Bignum.AArch64.SquareEightDispatch.mm 5 5 5) (fun _ _ => True) := by
  unfold VG.Impl.Bignum.AArch64.SquareEightDispatch.mm
  rw [ite_eq_left (by decide)]
  unfold VG.Impl.Bignum.AArch64.SquareEightDispatch.guarded
  refine RelCT.seq (two_piece _ pins_goodW (by taint_decide) BlockedRedc.guard_ctx) ?_
  refine two_ite (Φ := BlockedRedc.GuardCtx) ?_ ?_ ?_
  · intro L s t hs ht
    rw [VG.Proof.MlKem.AArch64.eval_nonzero, VG.Proof.MlKem.AArch64.eval_nonzero, hs.width, ht.width]
  · refine two_ite ?_ ?_ ?_
    · intro L s t hs ht
      rw [VG.Proof.MlKem.AArch64.eval_zero, VG.Proof.MlKem.AArch64.eval_zero, hs.1.rem, ht.1.rem]
    · exact two_map id (fun _ _ h => ⟨h.1.1.good, BlockedRedc.guard_width h.1.1 h.1.2,
        BlockedRedc.guard_rem h.1.1 h.2⟩)
        (SquareEight.square_ct (by decide) (by decide) (by decide) (by decide)
          (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
          (by taint_decide) (by taint_decide) (by taint_decide))
    · exact two_map id (fun _ _ h => h.1.1.good) blocked_square_rel
  · exact two_map id (fun _ _ h => h.1.good) blocked_square_rel

def Ready (d : FnData) (s : State) : Prop :=
  FnPhi d s ∧ (s.gpr .x5).setWidth 32 = tag d.o d.a d.b

theorem test_ctx (d : FnData) (s : State) (h : FnPhi d s) :
    WP isa (.block squareTest) s (Ready d) := by
  refine WP.mono (test_ok s) fun t ⟨v, k⟩ => ?_
  obtain ⟨hp, h0, h1, hw, ho, ha, hb⟩ := h
  refine ⟨⟨v.pre k hp, v.x0.trans h0, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [v.x1]; exact h1
  · rw [v.mem]; exact hw
  · simpa only [idx, v.x2] using ho
  · simpa only [idx, v.x3] using ha
  · simpa only [idx, v.x4] using hb
  · rw [v.flag, ho, ha, hb]

theorem mul_rel : RelCT isa (Two FnPhi) mul (fun _ _ => True) := by
  unfold mul
  refine RelCT.seq (two_post (two_taint [] (fun _ _ _ _ _ _ h => by cases h)
    (by taint_decide)) test_ctx) ?_
  refine two_ite (Φ := Ready) ?_ ?_ ?_
  · intro d s t hs ht
    simp only [VG.AArch64.eval, State.read, Size.bits, hs.2, ht.2]
  · refine two_map (fun d => (⟨d.B, d.Z, d.w⟩ : Ws)) (fun d s h => ?_) square_rel
    obtain ⟨hp, h0, h1, hw, -⟩ := h.1.1
    obtain ⟨hs, hH, hz, -⟩ := fn_good hp
    refine ⟨wordAt s.mem (s.gpr .x0) minvWord, ?_, ?_⟩
    · exact ⟨by simpa only [h0, h1] using hs, h0, by simpa only [h0, hw] using hH⟩
    · simpa only [h0, h1, hw] using hz
  · exact two_map id (fun _ _ h => h.1.1) fn_rel

theorem mul_ct : ConstantTime isa fnContract.pre fnContract.pub mul :=
  RelCT.constantTime (mul_rel.mono (fun s t ⟨hs, ht, hsp, h0, h1, h2, h3, h4, hw⟩ =>
    ⟨⟨s.gpr .x0, (s.gpr .x1).toNat * 8, wOf s.mem (s.gpr .x0), idx s .x2, idx s .x3, idx s .x4⟩,
      ⟨hs, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨ht, h0.symm, by rw [h1], (congrArg (wOf t.mem) h0).trans hw.symm,
        by simp only [idx, h2], by simp only [idx, h3], by simp only [idx, h4]⟩, hsp⟩) fun _ _ h => h)

theorem mul_verified : Verified target mul (Proof.Rsa.Mont.mulContract abi) :=
  Verified.of_correct mul_correct mul_ct fn_implies

end VG.Proof.Bignum.AArch64.MontFn
