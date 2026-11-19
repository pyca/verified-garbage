module

public import VerifiedGarbage.Proof.Dsa.X86.SignLayout
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.LayoutAgreement
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatchCT
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.OutputBytes
public import VerifiedGarbage.Impl.Dsa.X86.Prevalidated
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Dsa.X86.Installed
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Dsa.X86.ScheduleFrame
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.InstallArguments
import VerifiedGarbage.Proof.Dsa.X86.PrivateKey
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import VerifiedGarbage.Proof.Dsa.X86.Result
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.Validation
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.StagePower
import VerifiedGarbage.Proof.Dsa.X86.StageArithmetic
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.StageMinus

/-! ### `Dsa.X86.Prevalidated`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.VerifyArithmetic`, which only this module used -/

section

/-! ### `Dsa.X86.VerifyPowers`, which only this module used -/

section

/-! # The product of two powers and the final reduction of x86 DSA verification -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem verifyPowers_ok {base : Addr} {size pLen qLen p q g y uv vv : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hu : operandValue s0 base (.local u) qLen = uv)
    (hv : operandValue s0 base (.local v) qLen = vv) :
    WP isa (Core.verifyPowers pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local u) qLen = (g ^ uv % p * (y ^ vv % p) % p) % q ∧
      Execution base s0 sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 := by
  have L := M.lengths
  have np : (pLen + 7) / 8 ≤ 48 := by omega_using [L]
  have nq : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  have qp : 0 < q := by have := M.qLarge; omega_using [this]
  have pp : 0 < p := by have := M.pLarge; omega_using [this]
  unfold Core.verifyPowers Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stagePower2P_ok M (G.ready (M.context np)) (M.scalarReady (by decide) np)
    (Y.ready (M.context np)) (M.scalarReady (by decide) np) (by decide) (M.wideFit (by decide)))
    fun s1 ⟨M1, R1⟩ => ?_)
  have E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.wideFit (by decide)⟩)
  have T1 : operandValue s1 base (.local VG.Impl.Dsa.Layout.t) pLen = g ^ uv * y ^ vv % p := by
    have V := R1.wide_value M (by decide) (Nat.lt_trans (Nat.mod_lt _ pp) M.valueBounds.1)
    rw [hg, hu, hy, hv] at V
    exact V
  refine WP.seq (WP.mono (stageReduce_ok (LenOperand.imm _ _ _ _ _) M1 (M1.wideStream (by decide) nq) (M1.wideStack (by decide)) (by omega_using [L])
    (by decide) (M1.scalarFit (by decide))) fun sf ⟨Mf, R4⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, ⟨E1.trans (R4.toStageFrame.execution (.inl ⟨by decide, M1.scalarFit (by decide)⟩)), ?_⟩⟩
  · have V := R4.scalar_value M1 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [T1] at V
    rw [V, Nat.mul_mod]
  · rw [R4.toStageFrame.mask_keep (by decide), R1.toStageFrame.mask_keep (by decide)]


end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.VerifyScalars`, which only this module used -/

section

/-! # The inverse and scalar exponents of x86 DSA verification -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem verifyScalars_ok {base : Addr} {size pLen qLen p q digestLen digest rv sv : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (R : CallerBuffer s0 base size (.input .signature) qLen)
    (S : CallerBuffer s0 base size .signatureS qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hr : operandValue s0 base (.input .signature) qLen = rv)
    (hs : operandValue s0 base .signatureS qLen = sv)
    (hD : operandValue s0 base (.input .digest) digestLen = digest)
    (hq2 : operandValue s0 base (.local qMinusTwo) qLen = q - 2) :
    WP isa (Core.verifyScalars qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local u) qLen = digest % q * (sv ^ (q - 2) % q) % q ∧
      operandValue sf base (.local v) qLen = rv * (sv ^ (q - 2) % q) % q ∧
      Execution base s0 sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 := by
  have L := M.lengths
  have nq : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  have qp : 0 < q := by have := M.qLarge; omega_using [this]
  unfold Core.verifyScalars Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stagePowerQ_ok M (S.ready (M.context nq)) (M.scalarReady (by decide) nq)
    (by decide) (M.scalarFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  have E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.scalarFit (by decide)⟩)
  have I1 : operandValue s1 base (.local VG.Impl.Dsa.Layout.inverse) qLen = sv ^ (q - 2) % q := by
    have V := R1.scalar_value M (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [hs, hq2] at V
    exact V
  have D1 := E1.buffer D (by decide)
  refine WP.seq (WP.mono (stageReduce_ok (LenOperand.prefix M1.saved nq (E1.prefixLen.trans hP)) M1 (D1.stream (M1.context nq)) D1.stack (by omega_using [hd])
    (by decide) (M1.scalarFit (by decide))) fun s2 ⟨M2, R2⟩ => ?_)
  have E2 := R2.toStageFrame.execution (.inl ⟨by decide, M1.scalarFit (by decide)⟩)
  have E12 := E1.trans E2
  have Z2 : operandValue s2 base (.local z) qLen = digest % q := by
    have V := R2.scalar_value M1 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [E1.value D (by decide) M.extent, hD] at V
    exact V
  have I2 : operandValue s2 base (.local VG.Impl.Dsa.Layout.inverse) qLen = sv ^ (q - 2) % q := by
    rw [R2.toStageFrame.scalar_keep M1 (by decide) (by decide) (by decide), I1]
  refine WP.seq (WP.mono (stageProduct_ok M2 (M2.scalarReady (by decide) nq) (M2.scalarReady (by decide) nq)
    (by decide) (M2.scalarFit (by decide))) fun s3 ⟨M3, R3⟩ => ?_)
  have E3 := R3.toStageFrame.execution (.inl ⟨by decide, M2.scalarFit (by decide)⟩)
  have E123 := E12.trans E3
  have U3 : operandValue s3 base (.local u) qLen = digest % q * (sv ^ (q - 2) % q) % q := by
    have V := R3.scalar_value M2 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [Z2, I2] at V
    exact V
  have I3 : operandValue s3 base (.local VG.Impl.Dsa.Layout.inverse) qLen = sv ^ (q - 2) % q := by
    rw [R3.toStageFrame.scalar_keep M2 (by decide) (by decide) (by decide), I2]
  have Rbuf := E123.buffer R (by decide)
  refine WP.seq (WP.mono (stageProduct_ok M3 (Rbuf.ready (M3.context nq)) (M3.scalarReady (by decide) nq)
    (by decide) (M3.scalarFit (by decide))) fun sf ⟨Mf, R4⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, ?_, ⟨E123.trans (R4.toStageFrame.execution (.inl ⟨by decide, M3.scalarFit (by decide)⟩)), ?_⟩⟩
  · rw [R4.toStageFrame.scalar_keep M3 (by decide) (by decide) (by decide), U3]
  · have V := R4.scalar_value M3 (by decide) (Nat.lt_trans (Nat.mod_lt _ qp) M.valueBounds.2)
    rw [E123.value R (by decide) M.extent, hr, I3] at V
    exact V

  · rw [R4.toStageFrame.mask_keep (by decide), R3.toStageFrame.mask_keep (by decide), R2.toStageFrame.mask_keep (by decide), R1.toStageFrame.mask_keep (by decide)]

end VG.Proof.Dsa.X86

end

end


/-! # Complete arithmetic schedule of x86 DSA verification -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem verifyArithmetic_ok {base : Addr} {size pLen qLen p q g y digestLen digest rv sv : Nat} {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (R : CallerBuffer s0 base size (.input .signature) qLen)
    (S : CallerBuffer s0 base size .signatureS qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hr : operandValue s0 base (.input .signature) qLen = rv)
    (hs : operandValue s0 base .signatureS qLen = sv)
    (hD : operandValue s0 base (.input .digest) digestLen = digest)
    (hq2 : operandValue s0 base (.local qMinusTwo) qLen = q - 2) :
    WP isa (Core.verify pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local u) qLen =
        (g ^ (digest % q * (sv ^ (q - 2) % q) % q) % p *
          (y ^ (rv * (sv ^ (q - 2) % q) % q) % p) % p) % q ∧
      Execution base s0 sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 := by
  unfold Core.verify
  refine WP.seq (WP.mono (verifyScalars_ok M R S D hd hP hr hs hD hq2) fun s1 ⟨M1, U1, V1, E1, F1⟩ => ?_)
  refine WP.mono (verifyPowers_ok M1 (E1.buffer G (by decide)) (E1.buffer Y (by decide))
    ((E1.value G (by decide) M.extent).trans hg)
    ((E1.value Y (by decide) M.extent).trans hy) U1 V1) ?_
  intro sf H
  exact ⟨H.1, H.2.1, E1.trans H.2.2.1, H.2.2.2.trans F1⟩

end VG.Proof.Dsa.X86

end

end


/-! # Functional correctness of i686 DSA verification for a validated public key

The verifier's body with its checks of the domain and public value replaced
by rebuilding q−2. Validation of the exact key bytes, the precondition, makes
the replaced checks hold, so the result is still `verifyBytes`. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem prevalidatedCompute_ok {base : Addr} {size pLen qLen p q g y digestLen digest rv sv : Nat}
    {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (R : CallerBuffer s0 base size (.input .signature) qLen)
    (S : CallerBuffer s0 base size .signatureS qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hr : operandValue s0 base (.input .signature) qLen = rv)
    (hs : operandValue s0 base .signatureS qLen = sv)
    (hD : operandValue s0 base (.input .digest) digestLen = digest) :
    let computed := (g ^ (digest % q * (sv ^ (q - 2) % q) % q) % p *
      (y ^ (rv * (sv ^ (q - 2) % q) % q) % p) % p) % q
    WP isa (Prevalidated.compute pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 &&&
        mask32 ((0 < rv ∧ rv < q) ∧ (0 < sv ∧ sv < q) ∧ computed = rv) ∧
      Execution base s0 sf := by
  dsimp only
  have L := M.lengths
  have A := M.aligned
  have nq : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  unfold Prevalidated.compute Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stageMinusQ_ok M (by have := M.qLarge; omega_using [this])
    (by decide) (M.scalarFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  have E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.scalarFit (by decide)⟩)
  have Q1 : operandValue s1 base (.local qMinusTwo) qLen = q - 2 :=
    R1.scalar_value M (by decide) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) M.valueBounds.2)
  have F1 := R1.toStageFrame.mask_keep (by decide)
  have R1' := E1.buffer R (by decide)
  refine WP.seq (WP.seq (WP.mono (stageRange_ok M1 (by omega_using [L]) (by omega_using [L]) (by omega_using [A])
    M1.qReady (R1'.ready (M1.context nq)) false) fun s2 ⟨M2, F2, A2⟩ => ?_))
  have E2 := A2.execution (.inr ⟨rfl, rfl⟩)
  have E12 := E1.trans E2
  have S2 := E12.buffer S (by decide)
  refine WP.mono (stageRange_ok M2 (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) M2.qReady (S2.ready (M2.context nq)) false)
    fun s3 ⟨M3, F3, A3⟩ => ?_
  have E3 := A3.execution (.inr ⟨rfl, rfl⟩)
  have E123 := E12.trans E3
  have Q3 : operandValue s3 base (.local qMinusTwo) qLen = q - 2 := by
    rw [A3.scalar_keep_mask M2 (by decide), A2.scalar_keep_mask M1 (by decide), Q1]
  refine WP.seq (WP.mono (verifyArithmetic_ok M3 (E123.buffer G (by decide)) (E123.buffer Y (by decide))
    (E123.buffer R (by decide)) (E123.buffer S (by decide)) (E123.buffer D (by decide)) hd (E123.prefixLen.trans hP)
    ((E123.value G (by decide) M.extent).trans hg) ((E123.value Y (by decide) M.extent).trans hy)
    ((E123.value R (by decide) M.extent).trans hr) ((E123.value S (by decide) M.extent).trans hs)
    ((E123.value D (by decide) M.extent).trans hD) Q3) fun s4 ⟨M4, U4, E4, F4⟩ => ?_)
  have E1234 := E123.trans E4
  have R4 := E1234.buffer R (by decide)
  refine WP.seq (WP.mono (stageEqual_ok M4 (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) (M4.scalarReady (by decide) nq)
    (R4.ready (M4.context nq))) fun sf ⟨Mf, F5, A5⟩ => ?_)
  refine WP.block_nil ⟨Mf, ?_, E1234.trans (A5.execution (.inr ⟨rfl, rfl⟩))⟩
  rw [F5, F4, F3, F2, F1, U4, E1234.value R (by decide) M.extent,
    E12.value S (by decide) M.extent, E1.value R (by decide) M.extent, hr, hs, M1.qValue, M2.qValue]
  simp only [Bool.false_eq_true, ite_false, BitVec.and_assoc, mask32_and, and_assoc]

theorem prevalidatedBody_spec {base : Addr} {size pLen qLen p q g y digestLen rv sv n : Nat} {s0 : State}
    {key signature digest : List Byte}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (R : CallerBuffer s0 base size (.input .signature) qLen)
    (S : CallerBuffer s0 base size .signatureS qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hr : operandValue s0 base (.input .signature) qLen = rv)
    (hs : operandValue s0 base .signatureS qLen = sv)
    (hD : operandValue s0 base (.input .digest) digestLen = Spec.Dsa.decodeBE (digest.take n))
    (hm : flagW base (Layout.field .mask) s0 = BitVec.allOnes 32)
    (shape : shapeValid p q) (pub : publicChecks p q g y)
    (keyLen : key.length = 3 * pLen + qLen) (sigLen : signature.length = 2 * qLen)
    (keyValue : Spec.Dsa.publicKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, none⟩)
    (rValue : Spec.Dsa.decodeBE (signature.take qLen) = rv)
    (sValue : Spec.Dsa.decodeBE (signature.drop qLen) = sv)
    (qBits : Spec.Dsa.bitLength q = 8 * n) :
    WP isa (Prevalidated.body pLen qLen) s0 fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.verifyBytes pLen qLen key signature digest then 1 else 0) ∧
      Execution base s0 sf := by
  have spec := verifyBytes_compute M.widths shape keyLen sigLen keyValue rValue sValue qBits (digest := digest)
  unfold Prevalidated.body
  refine WP.seq (WP.mono (prevalidatedCompute_ok M G Y R S D hd hP hg hy hr hs hD)
    fun s1 ⟨M1, F1, E1⟩ => ?_)
  have mask1 := F1
  rw [hm, BitVec.allOnes_and] at mask1
  refine WP.mono (result_ok M1.scr M1.saved _ mask1) fun sf ⟨Vf, Kf, Of⟩ => ?_
  refine ⟨?_, ⟨E1.keeps.trans (Kf.mono (by decide)), by rw [Of]; exact E1.mem⟩⟩
  rw [spec, Vf]
  simp only [pub, true_and, decide_eq_true_eq]
  split <;> rfl

theorem prevalidatedSized_spec {base : Addr} {size pLen qLen p q g y total rv sv : Nat}
    {s : State} {key signature digest : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (Y : CallerBuffer s base size (.input .y) pLen)
    (R : CallerBuffer s base size (.input .signature) qLen)
    (S : CallerBuffer s base size .signatureS qLen)
    (D : CallerBuffer s base size (.input .digest) total)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (hy : operandValue s base (.input .y) pLen = y)
    (hr : operandValue s base (.input .signature) qLen = rv)
    (hs : operandValue s base .signatureS qLen = sv)
    (hd : (pointerValue base s (.input .digestLen)).toNat = total)
    (hD : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .digest)).setWidth 64) total = digest)
    (keyLen : key.length = 3 * pLen + qLen) (sigLen : signature.length = 2 * qLen)
    (keyValue : Spec.Dsa.publicKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, none⟩)
    (rValue : Spec.Dsa.decodeBE (signature.take qLen) = rv)
    (sValue : Spec.Dsa.decodeBE (signature.drop qLen) = sv)
    (valid : Spec.Dsa.validatePublicKeyBytes pLen qLen key = true) :
    WP isa (Prevalidated.sized pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.verifyBytes pLen qLen key signature digest then 1 else 0) ∧
      Keeps powerClob s sf ∧ StackOutside (s.gpr .esp) base usedBytes s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  have bound : 8248 ≤ size := by have H : 15712 ≤ size := extent; omega_using [H]
  have checks : shapeValid p q ∧ publicChecks p q g y := by
    rw [VG.Proof.Dsa.validatePublicKeyBytes_eq widths keyLen keyValue] at valid
    exact of_decide_eq_true valid
  unfold Prevalidated.sized
  refine WP.seq (WP.mono (shapeModuli_ok scr extent widths P Q hp hq) fun t ⟨F, Z, Mt, K, O⟩ => ?_)
  by_cases shape : shapeValid p q
  · refine WP.ite false (by simp only [eval, Z, shape, decide_true, Bool.not_true])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    obtain ⟨M, Dp⟩ := Mt shape
    rw [hd] at Dp
    have hP : pointerValue base t (.input .digestPrefixLen) =
        BitVec.ofNat 32 (min total (Spec.Dsa.bitLength q / 8)) :=
      BitVec.eq_of_toNat_eq (by rw [Dp, BitVec.toNat_ofNat]; have B := shape_digest_width shape; omega_using [hd])
    have Dt := D.keep_shape O K (by decide) (by decide)
    have Db := D.bytes_keep_shape O K (by decide) (by decide) bound
    have digestValue : operandValue t base (.input .digest)
        (min total (Spec.Dsa.bitLength q / 8)) = Spec.Dsa.decodeBE (digest.take (Spec.Dsa.bitLength q / 8)) := by
      unfold operandValue
      rw [bytesAt_prefix, Db, hD]
    refine WP.mono (prevalidatedBody_spec M
      (G.keep_shape O K (by decide) (by decide))
      (Y.keep_shape O K (by decide) (by decide))
      (R.keep_shape O K (by decide) (by decide))
      (S.keep_shape O K (by decide) (by decide))
      (Dt.prefix (Nat.min_le_left _ _))
      (by have B := shape_digest_width shape; omega_using [B]) hP
      ((G.value_keep_shape O K (by decide) (by decide) bound).trans hg)
      ((Y.value_keep_shape O K (by decide) (by decide) bound).trans hy)
      ((R.value_keep_shape O K (by decide) (by decide) bound).trans hr)
      ((S.value_keep_shape O K (by decide) (by decide) bound).trans hs)
      digestValue (by simpa only [flagW, mask32, shape, decide_true, ite_true] using F) shape checks.2
      keyLen sigLen keyValue rValue sValue (shape_digest_width shape).1)
      fun sf ⟨V, E⟩ => ?_
    exact ⟨V, (K.mono (by decide)).trans E.keeps,
      (fun a ha hstack => ((execution_outside E) a ha (by rw [K.1 .esp (by decide)]; exact hstack)).trans
        ((shapeFrame_outside O) a (.inr (by change 15712 ≤ ofs base a at ha; omega_using [ha])))),
      fun regs saved => E.saved (shapeFrame_saved O saved)⟩
  · exact absurd checks.1 shape

theorem prevalidatedInstalled_spec {s t : State} (A : VerifyingABI s)
    (I : Installed (argumentPointer s 8) ((arg s 9).toNat * 8) Entry.verifyArguments 0 2 3 s t)
    (valid : Spec.Dsa.validatePublicKeyBytes (arg s 2).toNat (arg s 3).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) = true) :
    WP isa (Prevalidated.sized (arg s 2).toNat (arg s 3).toNat) t fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.verifyBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat) then 1 else 0) ∧
      Keeps powerClob t sf ∧ StackOutside (t.gpr .esp) (argumentPointer s 8) usedBytes t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 8)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 8)) regs Entry.savedRegisters := by
  have L : 0 < (arg s 2).toNat ∧ 0 < (arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega_using [H]
  obtain ⟨Key, KeyBytes⟩ := I.input (by decide : (0, .p) ∈ Entry.verifyArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Sig, SigBytes⟩ := I.input (by decide : (4, .signature) ∈ Entry.verifyArguments) A.signatureBound
    (by rw [A.rd, A.wr]; simp) A.signatureScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowSignature.symm)
  obtain ⟨D, DigestBytes⟩ := I.input (by decide : (6, .digest) ∈ Entry.verifyArguments) A.digestBound
    (by rw [A.rd, A.wr]; simp) A.digestScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowDigest.symm)
  obtain ⟨Qptr, Gptr, Yptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Y, KeyValue⟩ := publicKey_buffers Key L.1 L.2 (by have := A.keyLength; omega_using [this]) KeyBytes
    Qptr Gptr Yptr
  have qPtr := I.arguments (3, .qLen) (by decide)
  have Sptr : pointerValue (argumentPointer s 8) t .signatureS =
      pointerValue (argumentPointer s 8) t (.input .signature) + BitVec.ofNat 32 (arg s 3).toNat := by
    change pointerValue (argumentPointer s 8) t (.input .signature) +
      pointerValue (argumentPointer s 8) t (.input .qLen) = _
    rw [qPtr]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have S := Sig.slice L.2 (by have := A.signatureLength; omega_using [this]) Sptr
  have R := Sig.prefix (by have := A.signatureLength; omega_using [this] : (arg s 3).toNat ≤ (arg s 5).toNat)
  have Rbytes := Sig.slice_bytes (dest := .input .signature) (offset := 0) L.2
    (by have := A.signatureLength; omega_using [this]) (by simp)
  have Sbytes := Sig.slice_bytes L.2 (by have := A.signatureLength; omega_using [this]) Sptr
  rw [SigBytes, List.drop_zero] at Rbytes
  rw [SigBytes, List.take_of_length_le (by
    simp only [List.length_drop, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    have := A.signatureLength; omega_using [this])] at Sbytes
  apply prevalidatedSized_spec I.scr A.used A.lengths P Q G Y R S D rfl rfl rfl rfl rfl rfl
    (congrArg BitVec.toNat (I.arguments (7, .digestLen) (by decide))) DigestBytes
    (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.keyLength)
    (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.signatureLength)
    KeyValue (congrArg Spec.Dsa.decodeBE Rbytes.symm) (congrArg Spec.Dsa.decodeBE Sbytes.symm) valid

theorem prevalidatedOperation_spec {s : State} (A : VerifyingABI s)
    (valid : Spec.Dsa.validatePublicKeyBytes (arg s 2).toNat (arg s 3).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) = true) :
    WP isa Prevalidated.verify s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.verifyBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat)
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 6) (arg s 7).toNat) then 1 else 0) ∧
      abiPreserved s sf ∧
      StackOutside (s.gpr .esp) (argumentPointer s 8) ((arg s 9).toNat * 8) s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  have sz : 8272 ≤ (arg s 9).toNat * 8 := by have H : 15712 ≤ (arg s 9).toNat * 8 := A.used; omega_using [H]
  unfold Prevalidated.verify Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (verifyingEntry_ok A) fun t I => ?_)
  refine WP.seq (generationDispatch_ok Prevalidated.sized _ I.scr (by change 8256 ≤ _; omega_using [sz])
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (2, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (3, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (prevalidatedInstalled_spec A J valid) fun v ⟨Value, K, O, Saved⟩ => ?_
  have Ov : StackOutside (s.gpr .esp) (argumentPointer s 8) ((arg s 9).toNat * 8) s.mem v.mem :=
    fun a ha hstack => (O a (by have := A.used; omega_using [ha, this])
      (by rw [J.keeps.1 .esp (by decide)]; exact hstack)).trans
        (J.outside a (.inr (by simpa only [Nat.zero_add] using ha)))
  have Esp : v.gpr .esp = s.gpr .esp := (K.1 _ (by decide)).trans (J.keeps.1 _ (by decide))
  refine WP.seq (WP.mono (entryRestore_ok (J.scr.of_keeps K (by decide)) sz (Saved s.gpr J.saved))
    fun sf R => WP.block_nil ?_)
  refine ⟨?_, restored_abi R Esp (outside_return Ov A.retScratch A.stackLow), ?_, ?_, ?_⟩
  · rw [R.other .eax (by decide)]; exact Value
  · rw [R.mem]; exact Ov
  · rw [R.rd, K.2.1, J.keeps.2.1]
  · rw [R.wr, K.2.2, J.keeps.2.2]

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.Validating`, which this module and modules that import it used -/

section

/-! # Functional correctness of the i686 DSA public-key validator

The domain checker's cdecl entry and width dispatch, whose packed buffer is
now a public key (`3 p_len + q_len` bytes), around the verifier's checks of
the domain and public value. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

structure ValidatingABI (s : State) : Prop where
  stackLow : 108 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 0, (arg s 1).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 4, (arg s 5).toNat * 8⟩, ⟨argAddr s 0, 24⟩]
  keyScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 4, (arg s 5).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 24⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 108#64, 108⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  belowKey : (⟨(s.gpr .esp).setWidth 64 - 108#64, 108⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat⟩
  keyBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  scratchBound : (arg s 4).toNat + (arg s 5).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Dsa.lengthsValid (arg s 2).toNat (arg s 3).toNat
  keyLength : (arg s 1).toNat = 3 * (arg s 2).toNat + (arg s 3).toNat
  scratchLength : Spec.Dsa.scratchWords (arg s 2).toNat ≤ (arg s 5).toNat

theorem validatingABI_of {s : State} (h : (Spec.Dsa.validatePublicKeyContract abi 108).pre s) :
    ValidatingABI s := by
  sig_pre [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argSlots, argVal, argBytes,
    stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

theorem ValidatingABI.used {s : State} (A : ValidatingABI s) : usedBytes ≤ (arg s 5).toNat * 8 := by
  have L := A.lengths
  have H := A.scratchLength
  unfold Spec.Dsa.lengthsValid at L
  unfold Spec.Dsa.scratchWords at H
  change 15712 ≤ _
  omega_using [L, H]

theorem ValidatingABI.stackArgument {s : State} (A : ValidatingABI s) {i : Nat} (hi : i < 6) :
    StackArgument s (argumentPointer s 4) ((arg s 5).toNat * 8) i := by
  apply stackArgument_of (count := 6) (by have := A.stackBound; omega_using [this]) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem ValidatingABI.stack {s : State} (A : ValidatingABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 108) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (arg s 4).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega_using [H]
  · exact A.belowScratch

theorem ValidatingABI.room {s : State} (A : ValidatingABI s) :
    Pow.Room (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) := by
  apply room_of A.stackLow
  · have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega_using [H]
  · exact A.belowScratch

theorem validatingEntry_ok {s : State} (A : ValidatingABI s) :
    WP isa (.block Generate.checkEntry) s fun t =>
      Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s t := by
  have sz : 8272 ≤ (arg s 5).toNat * 8 := by have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega_using [H]
  apply WP.mono (installArguments_ok Generate.checkArguments (scratchArg := 4)
    (keyArg := 0) (pLenArg := 2) (qLenArg := 3)
    (A.stackArgument (by decide : 4 < 6)).readSrc rfl A.scratchBound sz
    (by rw [A.wr]; simp [stackValue_arg]) A.stack (by decide) ?_ (by decide) (by decide) (by decide) (by decide))
  · intro t ⟨Scr, Saved, Args, Q, G, Y, X, K, O⟩
    exact ⟨Scr, Saved, Args, Q, G, Y, X, K, O⟩
  · intro a ha
    apply A.stackArgument
    simp only [Generate.checkArguments, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide

theorem validatingSized_spec {base : Addr} {size pLen qLen p q g y : Nat}
    {s : State} {key : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (Y : CallerBuffer s base size (.input .y) pLen)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (hy : operandValue s base (.input .y) pLen = y)
    (keyLen : key.length = 3 * pLen + qLen)
    (keyValue : Spec.Dsa.publicKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, none⟩) :
    WP isa (Generate.checkSizedWith Validate.publicKey pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.validatePublicKeyBytes pLen qLen key then 1 else 0) ∧
      Keeps powerClob s sf ∧ StackOutside (s.gpr .esp) base usedBytes s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  have bound : 8248 ≤ size := by have H : 15712 ≤ size := extent; omega_using [H]
  have value := VG.Proof.Dsa.validatePublicKeyBytes_eq widths keyLen keyValue
  unfold Generate.checkSizedWith
  refine WP.seq (WP.mono (shapeModuli_ok scr extent widths P Q hp hq) fun t ⟨F, Z, M, K, O⟩ => ?_)
  by_cases valid : shapeValid p q
  · refine WP.ite false (by simp only [eval, Z, valid, decide_true, Bool.not_true])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    obtain ⟨Mt, _⟩ := M valid
    refine WP.seq (WP.mono (publicKey_ok Mt
      (G.keep_shape O K (by decide) (by decide)) (Y.keep_shape O K (by decide) (by decide))
      ((G.value_keep_shape O K (by decide) (by decide) bound).trans hg)
      ((Y.value_keep_shape O K (by decide) (by decide) bound).trans hy))
      fun u ⟨Mu, Fu, _, E⟩ => ?_)
    have mask : flagW base (Layout.field .mask) u = mask32 (shapeValid p q ∧ publicChecks p q g y) := by
      rw [Fu, F, mask32_and]
    refine WP.mono (result_ok Mu.scr Mu.saved _ mask) fun sf ⟨V, Kf, Of⟩ => ?_
    refine ⟨?_, ((K.mono (by decide)).trans E.keeps).trans (Kf.mono (by decide)), ?_, ?_⟩
    · rw [V, value]
      by_cases h : shapeValid p q ∧ publicChecks p q g y
      · simp only [h]; rfl
      · simp only [h, decide_false, ite_false]; rfl
    · rw [Of]
      intro a ha hstack
      exact (execution_outside E a ha (by rw [K.1 .esp (by decide)]; exact hstack)).trans
        ((shapeFrame_outside O) a (.inr (by change 15712 ≤ ofs base a at ha; omega_using [ha])))
    · intro regs saved
      rw [Of]
      exact E.saved (shapeFrame_saved O saved)
  · refine WP.ite true (by simp only [eval, Z, valid, decide_false, Bool.not_false])
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (verifyFailure_ok t) fun sf ⟨V, Kf, Of⟩ => ?_
    refine ⟨?_, (K.mono (by decide)).trans (Kf.mono (by decide)), ?_, ?_⟩
    · rw [V, value]
      simp only [valid, false_and, decide_false]
      rfl
    · rw [Of]
      intro a ha _
      exact (shapeFrame_outside O) a (.inr (by change 15712 ≤ ofs base a at ha; omega_using [ha]))
    · intro regs saved
      rw [Of]
      exact shapeFrame_saved O saved

theorem validatingInstalled_spec {s t : State} (A : ValidatingABI s)
    (I : Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s t) :
    WP isa (Generate.checkSizedWith Validate.publicKey (arg s 2).toNat (arg s 3).toNat) t fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.validatePublicKeyBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      Keeps powerClob t sf ∧ StackOutside (t.gpr .esp) (argumentPointer s 4) usedBytes t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 4)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 4)) regs Entry.savedRegisters := by
  have L : 0 < (arg s 2).toNat ∧ 0 < (arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega_using [H]
  obtain ⟨Key, Bytes⟩ := I.input (by decide : (0, .p) ∈ Generate.checkArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr, Gptr, Yptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Y, Value⟩ := publicKey_buffers Key L.1 L.2
    (by have := A.keyLength; omega_using [this]) Bytes Qptr Gptr Yptr
  exact validatingSized_spec I.scr A.used A.lengths P Q G Y rfl rfl rfl rfl
    (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.keyLength) Value

theorem validatingOperation_spec {s : State} (A : ValidatingABI s) :
    WP isa Prevalidated.validate s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.validatePublicKeyBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      abiPreserved s sf ∧
      StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  have sz : 8272 ≤ (arg s 5).toNat * 8 := by have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega_using [H]
  unfold Prevalidated.validate Generate.checkParametersWith Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (validatingEntry_ok A) fun t I => ?_)
  refine WP.seq (generationDispatch_ok _ _ I.scr (by change 8256 ≤ _; omega_using [sz])
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (2, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (3, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (validatingInstalled_spec A J) fun v ⟨Value, K, O, Saved⟩ => ?_
  have Ov : StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) s.mem v.mem :=
    fun a ha hstack => (O a (by have := A.used; omega_using [ha, this])
      (by rw [J.keeps.1 .esp (by decide)]; exact hstack)).trans
        (J.outside a (.inr (by simpa only [Nat.zero_add] using ha)))
  have Esp : v.gpr .esp = s.gpr .esp := (K.1 _ (by decide)).trans (J.keeps.1 _ (by decide))
  refine WP.seq (WP.mono (entryRestore_ok (J.scr.of_keeps K (by decide)) sz (Saved s.gpr J.saved))
    fun sf R => WP.block_nil ?_)
  refine ⟨?_, restored_abi R Esp (outside_return Ov A.retScratch A.stackLow), ?_, ?_, ?_⟩
  · rw [R.other .eax (by decide)]; exact Value
  · rw [R.mem]; exact Ov
  · rw [R.rd, K.2.1, J.keeps.2.1]
  · rw [R.wr, K.2.2, J.keeps.2.2]

end VG.Proof.Dsa.X86

end

end

-- separate module: the constant-time proofs cost more than their imports, and the contract
-- module's satisfiability witnesses should not re-check them.

/-! # Whole i686 validation and prevalidated verification traces from public arguments

Both branch only on the public widths and the shape of the public domain. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem prevalidatedSized_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (R : (.input .signature, L.qLen) ∈ L.inputs) (S : (.signatureS, L.qLen) ∈ L.inputs)
    (D : (.input .digest, digestLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t)
      (Prevalidated.sized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Prevalidated.sized
  refine RelCT.seq (shapeCall_relCT L digestLen P Q stable hd)
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  by_cases valid : shapeValid L.p L.q
  · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have B := shape_digest_width valid
    have W := L.lengths
    have Pc : CallOperand L (.input .p) L.pLen := .inl ⟨_, P, Nat.le_refl _⟩
    have Qc : CallOperand L (.input .q) L.qLen := .inl ⟨_, Q, Nat.le_refl _⟩
    have Gc : CallOperand L (.input .g) L.pLen := .inl ⟨_, G, Nat.le_refl _⟩
    have Yc : CallOperand L (.input .y) L.pLen := .inl ⟨_, Y, Nat.le_refl _⟩
    have Rc : CallOperand L (.input .signature) L.qLen := .inl ⟨_, R, Nat.le_refl _⟩
    have Sc : CallOperand L .signatureS L.qLen := .inl ⟨_, S, Nat.le_refl _⟩
    have Dc : CallOperand L (.input .digest) L.digestPrefix :=
      .inl ⟨_, D, by rw [hd]; exact Nat.min_le_left _ _⟩
    have U := CallOperand.localBuffer L u L.qLen (by decide) (by change 14816 + L.qLen ≤ 15712; omega_using [W])
    have Compute : RelCT isa (CallPair L) (Prevalidated.compute L.pLen L.qLen) (CallPair L) := by
      unfold Prevalidated.compute Core.sequence
      dsimp only [List.foldr]
      exact RelCT.seq (callMinusQ_relCT L qMinusTwo Qc (by decide) (by change 14912 + L.qLen ≤ 15712; omega_using [W]))
        (RelCT.seq (RelCT.seq
          (callRange_relCT L L.qLen .q (.input .signature) false Qc Rc (by omega_using [W]) (by omega_using [W]) L.aligned.2)
          (callRange_relCT L L.qLen .q .signatureS false Qc Sc (by omega_using [W]) (by omega_using [W]) L.aligned.2))
        (RelCT.seq (callVerify_relCT L Pc Qc Gc Yc Rc Sc Dc (by rw [hd]; omega_using [B]))
        (RelCT.seq (callEqual_relCT L L.qLen (.local u) (.input .signature) U Rc (by omega_using [W]) (by omega_using [W])
          L.aligned.2)
        (RelCT.block_nil (fun _ _ h => h)))))
    have CT := RelCT.seq Compute (result_relCT.mono (fun _ _ H => H.workspace) (fun _ _ h => h))
    exact CT.mono (fun _ _ H => ⟨(H.2 True.intro).1.ready, (H.2 True.intro).2.ready⟩) (fun _ _ h => h)
  · simp only [valid, decide_false, Bool.not_false, ite_true]
    exact verifyFailure_relCT.mono (fun _ _ H => H.1) (fun _ _ h => h)

theorem prevalidatedOperation_agrees {s t : State} (A : VerifyingABI s) (B : VerifyingABI t)
    (args : ∀ i < 10, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (verifyKey s).params.p = (verifyKey t).params.p)
    (Q : (verifyKey s).params.q = (verifyKey t).params.q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa Prevalidated.verify s tr sf) (F : Exec isa Prevalidated.verify t ur tf) : tr = ur := by
  let L := verifyLayout s A
  have LayoutEq := verifyLayout_eq A B args SP P Q
  have Size := args 9 (by decide)
  have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 8 (by decide))
  have PL := args 2 (by decide)
  have QL := args 3 (by decide)
  have DL := args 7 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 8) ((arg s 9).toNat * 8) Entry.verifyArguments 0 2 3 s u ∧
    Installed (argumentPointer t 8) ((arg t 9).toNat * 8) Entry.verifyArguments 0 2 3 t v
  have Invariant : CompareInvariant L.base L.size R := by
    refine ⟨?_, fun _ _ _ _ H K1 K2 O1 O2 => ⟨H.1.compare K1 O1, H.2.compare K2 O2⟩⟩
    intro u v H
    refine ⟨H.1.scr, ?_⟩
    simpa only [L, verifyLayout, Base, Size] using H.2.scr
  have hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (2, .pLen) (by decide)), ?_⟩
    simpa only [L, verifyLayout, Base, PL] using congrArg BitVec.toNat (H.2.arguments (2, .pLen) (by decide))
  have hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (3, .qLen) (by decide)), ?_⟩
    simpa only [L, verifyLayout, Base, QL] using congrArg BitVec.toNat (H.2.arguments (3, .qLen) (by decide))
  have Sized : RelCT isa R (Prevalidated.sized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (prevalidatedSized_relCT L (arg s 7).toNat (by simp [L, verifyLayout, verifyInputs])
      (by simp [L, verifyLayout, verifyInputs]) (by simp [L, verifyLayout, verifyInputs])
      (by simp [L, verifyLayout, verifyInputs]) (by simp [L, verifyLayout, verifyInputs])
      (by simp [L, verifyLayout, verifyInputs]) (by simp [L, verifyLayout, verifyInputs])
      (verifyInputs_shape _ _ _) rfl).mono ?_ (fun _ _ h => h)
    intro u v H
    refine ⟨verifyingInstalled_ready A H.1, ?_⟩
    simpa only [L, LayoutEq, DL] using verifyingInstalled_ready B H.2
  have Dispatch := generationDispatch_relCT Prevalidated.sized
    [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
    L.pLen L.qLen L.base L.size R (VG.X86.Taint.Agree (workspaceTaint false)) Invariant L.saved
    (supportedWidths_member A.lengths) (by decide) hp hq Sized
  have Tail := RelCT.seq restore_relCT (RelCT.block_nil (M := isa) (P := fun _ _ => True) (fun _ _ h => h))
  change Exec isa (.seq (.block Entry.verifyEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) s tr sf at E
  change Exec isa (.seq (.block Entry.verifyEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) t ur tf at F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      obtain ⟨T1, _⟩ := installEntry_relCT 8 Entry.verifyArguments _ _ _ _ _ _
        ⟨SP, args 8 (by decide), (A.stackArgument (by decide : 8 < 10)).readSrc,
          (B.stackArgument (by decide : 8 < 10)).readSrc⟩ E1 F1
      have I := wp_result (verifyingEntry_ok A) E1
      have J := wp_result (verifyingEntry_ok B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J⟩ E2 F2
          have T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]

def validatingInputs (pLen qLen : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .y, pLen)]

def validatingPointers (s : State) : Pointer → BitVec 32
  | .input .p => arg s 0
  | .input .q => arg s 0 + arg s 2
  | .input .g => arg s 0 + arg s 2 + arg s 3
  | .input .y => arg s 0 + arg s 2 + arg s 3 + arg s 2
  | _ => 0

def validatingKey (s : State) : Spec.Dsa.Key := Spec.Dsa.publicKeyBytes (arg s 2).toNat (arg s 3).toNat
  (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)

/-- The checker's entry stores p_len as the digest length (`checkArguments`),
so the shape checks' digest prefix is computed from it. -/
def validatingLayout (s : State) (A : ValidatingABI s) : CallLayout where
  sp := s.gpr .esp
  base := argumentPointer s 4
  size := (arg s 5).toNat * 8
  pLen := (arg s 2).toNat
  qLen := (arg s 3).toNat
  p := (validatingKey s).params.p
  q := (validatingKey s).params.q
  widths := A.lengths
  extent := A.used
  inputs := validatingInputs (arg s 2).toNat (arg s 3).toNat
  pointers := validatingPointers s
  stable := by
    intro input hi
    simp only [validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide
  digestPrefix := min (arg s 2).toNat (Spec.Dsa.bitLength (validatingKey s).params.q / 8)

theorem validatingInputs_shape (pLen qLen : Nat) :
    ∀ input ∈ validatingInputs pLen qLen, ShapePointer input.1 := by
  intro input hi
  simp only [validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide

theorem validatingInstalled_ready {s t : State} (A : ValidatingABI s)
    (I : Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s t) :
    ShapeCallReady (validatingLayout s A) (arg s 2).toNat t := by
  have L : 0 < (arg s 2).toNat ∧ 0 < (arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega_using [H]
  obtain ⟨Key, Bytes⟩ := I.input (by decide : (0, .p) ∈ Generate.checkArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr, Gptr, Yptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Y, Value⟩ := publicKey_buffers Key L.1 L.2
    (by have := A.keyLength; omega_using [this]) Bytes Qptr Gptr Yptr
  refine ⟨I.keeps.1 .esp (by decide), I.scr, ?_, ?_, ?_, ?_,
    congrArg BitVec.toNat (I.arguments (2, .digestLen) (by decide))⟩
  · intro input hi
    simp only [validatingLayout, validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact P
    · exact Q
    · exact G
    · exact Y
  · intro input hi
    simp only [validatingLayout, validatingInputs, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact I.arguments (0, .p) (by decide)
    · exact I.qPointer
    · exact I.gPointer
    · exact I.yPointer
  · exact (congrArg (fun k : Spec.Dsa.Key => k.params.p) Value).symm
  · exact (congrArg (fun k : Spec.Dsa.Key => k.params.q) Value).symm

theorem validatingLayout_eq {s t : State} (A : ValidatingABI s) (B : ValidatingABI t)
    (args : ∀ i < 6, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (validatingKey s).params.p = (validatingKey t).params.p)
    (Q : (validatingKey s).params.q = (validatingKey t).params.q) :
    validatingLayout s A = validatingLayout t B := by
  have A0 := args 0 (by decide)
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A4 := args 4 (by decide)
  have A5 := args 5 (by decide)
  have pointers : validatingPointers s = validatingPointers t := by
    funext p
    cases p with
    | input f => cases f <;> simp only [validatingPointers, A0, A2, A3]
    | «local» d => rfl
    | signatureS => rfl
  simp only [validatingLayout, SP, argumentPointer, A2, A3, A4, A5, P, Q, pointers]

theorem validatingSized_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t)
      (Generate.checkSizedWith Validate.publicKey L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Generate.checkSizedWith
  refine RelCT.seq (shapeCall_relCT L digestLen P Q stable hd)
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  by_cases valid : shapeValid L.p L.q
  · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have CT := RelCT.seq (callPublicKey_relCT L (.inl ⟨_, P, Nat.le_refl _⟩)
      (.inl ⟨_, Q, Nat.le_refl _⟩) (.inl ⟨_, G, Nat.le_refl _⟩) (.inl ⟨_, Y, Nat.le_refl _⟩))
      (result_relCT.mono (fun _ _ H => H.workspace) (fun _ _ h => h))
    exact CT.mono (fun _ _ H => ⟨(H.2 True.intro).1.ready, (H.2 True.intro).2.ready⟩) (fun _ _ h => h)
  · simp only [valid, decide_false, Bool.not_false, ite_true]
    exact verifyFailure_relCT.mono (fun _ _ H => H.1) (fun _ _ h => h)

theorem validatingOperation_agrees {s t : State} (A : ValidatingABI s) (B : ValidatingABI t)
    (args : ∀ i < 6, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (validatingKey s).params.p = (validatingKey t).params.p)
    (Q : (validatingKey s).params.q = (validatingKey t).params.q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa Prevalidated.validate s tr sf) (F : Exec isa Prevalidated.validate t ur tf) : tr = ur := by
  let L := validatingLayout s A
  have LayoutEq := validatingLayout_eq A B args SP P Q
  have Size := args 5 (by decide)
  have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 4 (by decide))
  have PL := args 2 (by decide)
  have QL := args 3 (by decide)
  have DL := args 2 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s u ∧
    Installed (argumentPointer t 4) ((arg t 5).toNat * 8) Generate.checkArguments 0 2 3 t v
  have Invariant : CompareInvariant L.base L.size R := by
    refine ⟨?_, fun _ _ _ _ H K1 K2 O1 O2 => ⟨H.1.compare K1 O1, H.2.compare K2 O2⟩⟩
    intro u v H
    refine ⟨H.1.scr, ?_⟩
    simpa only [L, validatingLayout, Base, Size] using H.2.scr
  have hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (2, .pLen) (by decide)), ?_⟩
    simpa only [L, validatingLayout, Base, PL] using
      congrArg BitVec.toNat (H.2.arguments (2, .pLen) (by decide))
  have hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (3, .qLen) (by decide)), ?_⟩
    simpa only [L, validatingLayout, Base, QL] using
      congrArg BitVec.toNat (H.2.arguments (3, .qLen) (by decide))
  have Sized : RelCT isa R (Generate.checkSizedWith Validate.publicKey L.pLen L.qLen)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (validatingSized_relCT L (arg s 2).toNat (by simp [L, validatingLayout, validatingInputs])
      (by simp [L, validatingLayout, validatingInputs]) (by simp [L, validatingLayout, validatingInputs])
      (by simp [L, validatingLayout, validatingInputs]) (validatingInputs_shape _ _) rfl).mono ?_
      (fun _ _ h => h)
    intro u v H
    refine ⟨validatingInstalled_ready A H.1, ?_⟩
    simpa only [L, LayoutEq, DL] using validatingInstalled_ready B H.2
  have Dispatch := generationDispatch_relCT (Generate.checkSizedWith Validate.publicKey)
    [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
    L.pLen L.qLen L.base L.size R (VG.X86.Taint.Agree (workspaceTaint false)) Invariant L.saved
    (supportedWidths_member A.lengths) (by decide) hp hq Sized
  have Tail := RelCT.seq restore_relCT (RelCT.block_nil (M := isa) (P := fun _ _ => True) (fun _ _ h => h))
  change Exec isa (.seq (.block Generate.checkEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) s tr sf at E
  change Exec isa (.seq (.block Generate.checkEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) t ur tf at F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      obtain ⟨T1, _⟩ := installEntry_relCT 4 Generate.checkArguments _ _ _ _ _ _
        ⟨SP, args 4 (by decide), (A.stackArgument (by decide : 4 < 6)).readSrc,
          (B.stackArgument (by decide : 4 < 6)).readSrc⟩ E1 F1
      have I := wp_result (validatingEntry_ok A) E1
      have J := wp_result (validatingEntry_ok B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J⟩ E2 F2
          have T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Dsa.X86
