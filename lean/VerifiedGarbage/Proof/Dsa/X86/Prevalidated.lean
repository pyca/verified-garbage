module

public import VerifiedGarbage.Impl.Dsa.X86.Prevalidated
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import VerifiedGarbage.Proof.Dsa.X86.VerifyArithmetic
import VerifiedGarbage.Proof.Dsa.X86.StageMinus
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.Result
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatch
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Dsa.X86.ReturnFrame
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.Failure
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
public import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
import VerifiedGarbage.Proof.Dsa.X86.CallerSlice
import VerifiedGarbage.Proof.Dsa.Validation

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
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  unfold Prevalidated.compute Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stageMinusQ_ok M (by have := M.qLarge; omega)
    (by decide) (M.scalarFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  have E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.scalarFit (by decide)⟩)
  have Q1 : operandValue s1 base (.local qMinusTwo) qLen = q - 2 :=
    R1.scalar_value M (by decide) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) M.valueBounds.2)
  have F1 := R1.toStageFrame.mask_keep (by decide)
  have R1' := E1.buffer R (by decide)
  refine WP.seq (WP.seq (WP.mono (stageRange_ok M1 (by omega) (by omega) (by omega)
    M1.qReady (R1'.ready (M1.context nq)) false) fun s2 ⟨M2, F2, A2⟩ => ?_))
  have E2 := A2.execution (.inr ⟨rfl, rfl⟩)
  have E12 := E1.trans E2
  have S2 := E12.buffer S (by decide)
  refine WP.mono (stageRange_ok M2 (by omega) (by omega) (by omega) M2.qReady (S2.ready (M2.context nq)) false)
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
  refine WP.seq (WP.mono (stageEqual_ok M4 (by omega) (by omega) (by omega) (M4.scalarReady (by decide) nq)
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
  have bound : 8248 ≤ size := by have H : 15712 ≤ size := extent; omega
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
      BitVec.eq_of_toNat_eq (by rw [Dp, BitVec.toNat_ofNat]; have B := shape_digest_width shape; omega)
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
      (by have B := shape_digest_width shape; omega) hP
      ((G.value_keep_shape O K (by decide) (by decide) bound).trans hg)
      ((Y.value_keep_shape O K (by decide) (by decide) bound).trans hy)
      ((R.value_keep_shape O K (by decide) (by decide) bound).trans hr)
      ((S.value_keep_shape O K (by decide) (by decide) bound).trans hs)
      digestValue (by simpa only [flagW, mask32, shape, decide_true, ite_true] using F) shape checks.2
      keyLen sigLen keyValue rValue sValue (shape_digest_width shape).1)
      fun sf ⟨V, E⟩ => ?_
    exact ⟨V, (K.mono (by decide)).trans E.keeps,
      (fun a ha hstack => ((execution_outside E) a ha (by rw [K.1 .esp (by decide)]; exact hstack)).trans
        ((shapeFrame_outside O) a (.inr (by change 15712 ≤ ofs base a at ha; omega)))),
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
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
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
  obtain ⟨P, Q, G, Y, KeyValue⟩ := publicKey_buffers Key L.1 L.2 (by have := A.keyLength; omega) KeyBytes
    Qptr Gptr Yptr
  have qPtr := I.arguments (3, .qLen) (by decide)
  have Sptr : pointerValue (argumentPointer s 8) t .signatureS =
      pointerValue (argumentPointer s 8) t (.input .signature) + BitVec.ofNat 32 (arg s 3).toNat := by
    change pointerValue (argumentPointer s 8) t (.input .signature) +
      pointerValue (argumentPointer s 8) t (.input .qLen) = _
    rw [qPtr]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have S := Sig.slice L.2 (by have := A.signatureLength; omega) Sptr
  have R := Sig.prefix (by have := A.signatureLength; omega : (arg s 3).toNat ≤ (arg s 5).toNat)
  have Rbytes := Sig.slice_bytes (dest := .input .signature) (offset := 0) L.2
    (by have := A.signatureLength; omega) (by simp)
  have Sbytes := Sig.slice_bytes L.2 (by have := A.signatureLength; omega) Sptr
  rw [SigBytes, List.drop_zero] at Rbytes
  rw [SigBytes, List.take_of_length_le (by
    simp only [List.length_drop, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    have := A.signatureLength; omega)] at Sbytes
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
  have sz : 8272 ≤ (arg s 9).toNat * 8 := by have H : 15712 ≤ (arg s 9).toNat * 8 := A.used; omega
  unfold Prevalidated.verify Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (verifyingEntry_ok A) fun t I => ?_)
  refine WP.seq (generationDispatch_ok Prevalidated.sized _ I.scr (by change 8256 ≤ _; omega)
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (2, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (3, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (prevalidatedInstalled_spec A J valid) fun v ⟨Value, K, O, Saved⟩ => ?_
  have Ov : StackOutside (s.gpr .esp) (argumentPointer s 8) ((arg s 9).toNat * 8) s.mem v.mem :=
    fun a ha hstack => (O a (by have := A.used; omega)
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
