module

public import VerifiedGarbage.Impl.Dsa.X86.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Execution
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.SigningABI
public import VerifiedGarbage.Proof.Dsa.X86.Installed
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Dsa.X86.SignCompute
import VerifiedGarbage.Proof.Dsa.X86.StageMinus
import VerifiedGarbage.Proof.Dsa.X86.StageChecks
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.Result
import VerifiedGarbage.Proof.Dsa.X86.WriteSignature
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatch
import VerifiedGarbage.Proof.Dsa.X86.ReturnFrame
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.Failure
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import VerifiedGarbage.Proof.Dsa.X86.PackedKeyBuffers
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Dsa.X86.ValidatePrivate
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Framework.Offset

/-! # Functional correctness of i686 DSA signing for a validated private key

The signer's body with its checks of the domain and key replaced by
rebuilding q−2 and the nonce's range check. Validation of the exact key
bytes, the precondition, makes the replaced checks hold, so the result is
still `signBytes`. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem prevalidatedSignCompute_ok {base : Addr} {size pLen qLen p q g x k digestLen digest : Nat}
    {s0 : State}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hD : operandValue s0 base (.input .digest) digestLen = digest) :
    let rv := g ^ k % p % q
    let sv := k ^ (q - 2) % q * ((digest % q + x * rv % q) % q) % q
    WP isa (PrevalidatedSign.compute pLen qLen) s0 fun sf =>
      Moduli base size pLen qLen p q sf ∧
      operandValue sf base (.local r) qLen = rv ∧
      operandValue sf base (.local VG.Impl.Dsa.Layout.s) qLen = sv ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 &&&
        mask32 ((0 < k ∧ k < q) ∧ rv ≠ 0 ∧ sv ≠ 0) ∧ Execution base s0 sf := by
  dsimp only
  have L := M.lengths
  have A := M.aligned
  have nq : (qLen + 7) / 8 ≤ 48 := by omega
  unfold PrevalidatedSign.compute Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (stageMinusQ_ok M (by have := M.qLarge; omega)
    (by decide) (M.scalarFit (by decide))) fun s1 ⟨M1, R1⟩ => ?_)
  have E1 := R1.toStageFrame.execution (.inl ⟨by decide, M.scalarFit (by decide)⟩)
  have Q1 : operandValue s1 base (.local qMinusTwo) qLen = q - 2 :=
    R1.scalar_value M (by decide) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) M.valueBounds.2)
  have F1 := R1.toStageFrame.mask_keep (by decide)
  have K1 := E1.buffer K (by decide)
  refine WP.seq (WP.mono (stageRange_ok M1 (by omega) (by omega) (by omega)
    M1.qReady (K1.ready (M1.context nq)) false) fun s2 ⟨M2, F2, A2⟩ => ?_)
  have E2 := A2.execution (.inr ⟨rfl, rfl⟩)
  have E12 := E1.trans E2
  have Q2 : operandValue s2 base (.local qMinusTwo) qLen = q - 2 := by
    rw [A2.scalar_keep_mask M1 (by decide), Q1]
  refine WP.seq (WP.mono (signArithmetic_ok M2 (E12.buffer G (by decide)) (E12.buffer K (by decide))
    (E12.buffer X (by decide)) (E12.buffer D (by decide)) hd (E12.prefixLen.trans hP)
    ((E12.value G (by decide) M.extent).trans hg) ((E12.value K (by decide) M.extent).trans hk)
    ((E12.value X (by decide) M.extent).trans hx) ((E12.value D (by decide) M.extent).trans hD)
    Q2) fun s3 ⟨M3, R3, S3, E3, F3⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (stageZero_ok M3 (by omega) (by omega) (by omega)
    (M3.scalarReady (by decide) nq) true) fun s4 ⟨M4, F4, A4⟩ => ?_))
  have E4 := A4.execution (.inr ⟨rfl, rfl⟩)
  refine WP.mono (stageZero_ok M4 (by omega) (by omega) (by omega) (M4.scalarReady (by decide) nq) true)
    fun sf ⟨Mf, F5, A5⟩ => ?_
  refine WP.block_nil ⟨Mf, ?_, ?_, ?_, (((E12.trans E3).trans E4).trans (A5.execution (.inr ⟨rfl, rfl⟩)))⟩
  · rw [A5.scalar_keep_mask M4 (by decide), A4.scalar_keep_mask M3 (by decide), R3]
  · rw [A5.scalar_keep_mask M4 (by decide), A4.scalar_keep_mask M3 (by decide), S3]
  · rw [F5, F4, F3, F2, F1, A4.scalar_keep_mask M3 (by decide), R3, S3, E1.value K (by decide) M.extent, hk,
      M1.qValue]
    simp only [Bool.false_eq_true, ite_false, ite_true, BitVec.and_assoc, mask32_and, and_assoc]

theorem prevalidatedSignBody_ok {base : Addr} {size pLen qLen p q g x k digestLen digest : Nat} {s0 : State}
    {out : BitVec 32}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hD : operandValue s0 base (.input .digest) digestLen = digest)
    (hm : flagW base (Layout.field .mask) s0 = BitVec.allOnes 32)
    (hp : pointerValue base s0 (.input .out) = out)
    (hf : out.toNat + 2 * qLen ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ 2 * qLen → InRegions s0.wr (out.setWidth 64 + BitVec.ofNat 64 e) k)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 2 * qLen⟩) :
    let rv := g ^ k % p % q
    let sv := k ^ (q - 2) % q * ((digest % q + x * rv % q) % q) % q
    let accepted := (0 < k ∧ k < q) ∧ rv ≠ 0 ∧ sv ≠ 0
    WP isa (PrevalidatedSign.body pLen qLen) s0 fun sf =>
      sf.gpr .eax = (if accepted then 1 else 0) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) qLen =
        (if accepted then Spec.Dsa.encodeBE qLen rv else List.replicate qLen 0) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64 + BitVec.ofNat 64 qLen) qLen =
        (if accepted then Spec.Dsa.encodeBE qLen sv else List.replicate qLen 0) ∧
      Keeps powerClob s0 sf ∧
      StackOutputFrame (s0.gpr .esp) base (out.setWidth 64) usedBytes (2 * qLen) s0.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s0.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  dsimp only
  let accepted := (0 < k ∧ k < q) ∧ g ^ k % p % q ≠ 0 ∧
      k ^ (q - 2) % q * ((digest % q + x * (g ^ k % p % q) % q) % q) % q ≠ 0
  unfold PrevalidatedSign.body
  refine WP.seq (WP.mono (prevalidatedSignCompute_ok M G X K D hd hP hg hx hk hD)
    fun s1 ⟨M1, R1, S1, F1, E1⟩ => ?_)
  have mask1 : flagW base (Layout.field .mask) s1 = mask32 accepted := by
    simpa only [hm, BitVec.allOnes_and] using F1
  have ptr1 : pointerValue base s1 (.input .out) = out := by
    rw [runFrame_pointer E1.mem E1.keeps (by decide) (by decide), hp]
  refine wp_seq_assoc (WP.seq (WP.mono (writeSignature_ok M1 (decide accepted)
    (by simpa only [mask32, decide_eq_true_eq] using mask1) R1 S1 ptr1 hf
    (by intro e k h; rw [E1.keeps.2.2]; exact hw e k h) ha)
    fun s2 ⟨R2, S2, F2, K2, O2⟩ => ?_))
  refine WP.mono (result_ok (M1.scr.of_keeps K2 (by decide)) M1.saved accepted (F2.trans mask1))
    fun sf ⟨Vf, Kf, Of⟩ => ?_
  refine ⟨Vf, ?_, ?_, (E1.keeps.trans (K2.mono (by decide))).trans (Kf.mono (by decide)), ?_, ?_⟩
  · simpa only [Of, decide_eq_true_eq] using R2
  · simpa only [Of, decide_eq_true_eq] using S2
  · intro a ha hb hstack
    have C := VG.Proof.Dsa.X86.Layout.context_bound (by have := M.lengths; omega : (qLen + 7) / 8 ≤ 48)
    rw [Of, O2 a (by change 15712 ≤ ofs base a at ha; omega) hb]
    apply E1.mem a ?_ (.inr hstack)
    intro pair hp
    simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      change 15712 ≤ ofs base a at ha <;> right <;> change _ ≤ ofs base a <;>
      simp only [VG.Impl.Mont.X86.Dynamic.contextBytes, VG.Impl.Mont.X86.Dynamic.slot,
        VG.Impl.Mont.X86.Dynamic.stride, Layout.field, r, usedBytes] <;> omega
  · intro regs saved
    rw [Of]
    exact O2.saved ha
      (by have C := VG.Proof.Dsa.X86.Layout.context_bound (by have := M.lengths; omega : (qLen + 7) / 8 ≤ 48); omega)
      (by have H : 15712 ≤ size := M.extent; omega)
      (by have := M.scr.nowrap; omega) (E1.saved saved)

theorem prevalidatedSignBody_spec {base : Addr} {size pLen qLen p q g y x k digestLen n : Nat} {s0 : State}
    {out : BitVec 32} {key nonce digest : List Byte}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hD : operandValue s0 base (.input .digest) digestLen = Spec.Dsa.decodeBE (digest.take n))
    (hm : flagW base (Layout.field .mask) s0 = BitVec.allOnes 32)
    (hp : pointerValue base s0 (.input .out) = out)
    (hf : out.toNat + 2 * qLen ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ 2 * qLen → InRegions s0.wr (out.setWidth 64 + BitVec.ofNat 64 e) k)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 2 * qLen⟩)
    (shape : shapeValid p q)
    (keyLen : key.length = 3 * pLen + 2 * qLen) (nonceLen : nonce.length = qLen)
    (keyValue : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, some x⟩)
    (nonceValue : Spec.Dsa.decodeBE nonce = k) (qBits : Spec.Dsa.bitLength q = 8 * n)
    (valid : Spec.Dsa.validatePrivateKeyBytes pLen qLen key = true) :
    WP isa (PrevalidatedSign.body pLen qLen) s0 fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus (Spec.Dsa.signBytes pLen qLen key nonce digest) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (2 * qLen) =
        (Spec.Dsa.signBytes pLen qLen key nonce digest).getD (List.replicate (2 * qLen) 0) ∧
      Keeps powerClob s0 sf ∧
      StackOutputFrame (s0.gpr .esp) base (out.setWidth 64) usedBytes (2 * qLen) s0.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s0.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  have spec := signBytes_compute M.widths shape keyLen nonceLen keyValue nonceValue qBits (digest := digest)
  have checks : publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ g ^ x % p = y := by
    rw [validatePrivateKeyBytes_eq M.widths keyLen keyValue] at valid
    have V := of_decide_eq_true valid
    exact ⟨V.2.1, V.2.2.1, V.2.2.2⟩
  refine WP.mono (prevalidatedSignBody_ok M G X K D hd hP hg hx hk hD hm hp hf hw ha)
    fun sf ⟨V, R, S, Keep, Frame, Saved⟩ => ?_
  have B := signatureBytes _ R S
  have iff : (publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧ g ^ x % p = y ∧
      g ^ k % p % q ≠ 0 ∧ k ^ (q - 2) % q *
        ((Spec.Dsa.decodeBE (digest.take n) % q + x * (g ^ k % p % q) % q) % q) % q ≠ 0) ↔
      ((0 < k ∧ k < q) ∧ g ^ k % p % q ≠ 0 ∧ k ^ (q - 2) % q *
        ((Spec.Dsa.decodeBE (digest.take n) % q + x * (g ^ k % p % q) % q) % q) % q ≠ 0) :=
    ⟨fun H => ⟨H.2.2.1, H.2.2.2.2⟩, fun H => ⟨checks.1, checks.2.1, H.1, checks.2.2, H.2⟩⟩
  simp only [iff] at spec
  refine ⟨?_, ?_, Keep, Frame, Saved⟩
  · rw [spec]
    split
    · rename_i H
      rw [ite_eq_left H] at V
      rw [V]
      rfl
    · rename_i H
      rw [ite_eq_right H] at V
      rw [V]
      rfl
  · rw [spec]
    split
    · rename_i H
      rw [ite_eq_left H] at B
      exact B
    · rename_i H
      rw [ite_eq_right H] at B
      exact B

theorem prevalidatedSignSized_spec {base : Addr} {size pLen qLen p q g y x k total : Nat}
    {s : State} {out : BitVec 32} {key nonce digest : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (X : CallerBuffer s base size (.input .x) qLen)
    (N : CallerBuffer s base size (.input .nonce) qLen)
    (D : CallerBuffer s base size (.input .digest) total)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (hx : operandValue s base (.input .x) qLen = x)
    (hk : operandValue s base (.input .nonce) qLen = k)
    (hd : (pointerValue base s (.input .digestLen)).toNat = total)
    (hD : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .digest)).setWidth 64) total = digest)
    (ho : pointerValue base s (.input .out) = out)
    (hc : pointerValue base s (.input .qLen) = BitVec.ofNat 32 qLen)
    (hf : out.toNat + 2 * qLen ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ 2 * qLen → InRegions s.wr (out.setWidth 64 + BitVec.ofNat 64 e) k)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 2 * qLen⟩)
    (keyLen : key.length = 3 * pLen + 2 * qLen) (nonceLen : nonce.length = qLen)
    (keyValue : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, some x⟩)
    (nonceValue : Spec.Dsa.decodeBE nonce = k)
    (valid : Spec.Dsa.validatePrivateKeyBytes pLen qLen key = true) :
    WP isa (PrevalidatedSign.sized pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus (Spec.Dsa.signBytes pLen qLen key nonce digest) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (2 * qLen) =
        (Spec.Dsa.signBytes pLen qLen key nonce digest).getD (List.replicate (2 * qLen) 0) ∧
      Keeps powerClob s sf ∧
      StackOutputFrame (s.gpr .esp) base (out.setWidth 64) usedBytes (2 * qLen) s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  have bound : 8248 ≤ size := by have H : 15712 ≤ size := extent; omega
  have sz : 8272 ≤ size := by have H : 15712 ≤ size := extent; omega
  have L : 20 ≤ qLen ∧ qLen ≤ 32 := by unfold Spec.Dsa.lengthsValid at widths; omega
  unfold PrevalidatedSign.sized
  refine WP.seq (WP.mono (shapeModuli_ok scr extent widths P Q hp hq) fun t ⟨F, Z, Mt, K, O⟩ => ?_)
  by_cases shape : shapeValid p q
  · refine WP.ite false (by simp only [eval, Z, shape, decide_true, Bool.not_true])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    obtain ⟨M, Dp⟩ := Mt shape
    have mask : flagW base (Layout.field .mask) t = BitVec.allOnes 32 := by
      simpa only [flagW, mask32, shape, decide_true, ite_true] using F
    rw [hd] at Dp
    have Bw := shape_digest_width shape
    have hP : pointerValue base t (.input .digestPrefixLen) =
        BitVec.ofNat 32 (min total (Spec.Dsa.bitLength q / 8)) :=
      BitVec.eq_of_toNat_eq (by rw [Dp, BitVec.toNat_ofNat]; omega)
    have Dt := D.keep_shape O K (by decide) (by decide)
    have Db := D.bytes_keep_shape O K (by decide) (by decide) bound
    have digestValue : operandValue t base (.input .digest)
        (min total (Spec.Dsa.bitLength q / 8)) =
          Spec.Dsa.decodeBE (digest.take (Spec.Dsa.bitLength q / 8)) := by
      unfold operandValue
      rw [bytesAt_prefix, Db, hD]
    refine WP.mono (prevalidatedSignBody_spec M
      (G.keep_shape O K (by decide) (by decide))
      (X.keep_shape O K (by decide) (by decide))
      (N.keep_shape O K (by decide) (by decide))
      (Dt.prefix (Nat.min_le_left _ _))
      (by omega) hP
      ((G.value_keep_shape O K (by decide) (by decide) bound).trans hg)
      ((X.value_keep_shape O K (by decide) (by decide) bound).trans hx)
      ((N.value_keep_shape O K (by decide) (by decide) bound).trans hk)
      digestValue mask ((shapeFrame_field O (by decide)).trans ho) hf
      (by intro e k he; rw [K.2.2]; exact hw e k he) ha
      shape keyLen nonceLen keyValue nonceValue Bw.1 valid)
      fun sf ⟨V, B, Kf, F, Saved⟩ => ?_
    refine ⟨V, B, (K.mono (by decide)).trans Kf, ?_, fun regs saved => Saved regs (shapeFrame_saved O saved)⟩
    intro a hbase hout hstack
    exact (F a hbase hout (by rw [K.1 .esp (by decide)]; exact hstack)).trans
      (shapeFrame_outside O a (.inr (by change 15712 ≤ ofs base a at hbase; omega)))
  · refine WP.ite true (by simp only [eval, Z, shape, decide_false, Bool.not_false])
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    have rejected : Spec.Dsa.signBytes pLen qLen key nonce digest = none :=
      signBytes_invalid_shape (by simpa only [keyValue] using shape)
    refine WP.mono (signFailure_ok (scr.of_keeps K (by decide)) (by change 8256 ≤ size; omega)
      (by omega) L.2 ((shapeFrame_field O (by decide)).trans ho)
      ((shapeFrame_field O (by decide)).trans hc) hf
      (by intro i hi; rw [K.2.2]; exact hw i 1 (by omega))) fun sf ⟨B, V, Of, Kf⟩ => ?_
    have F : OutputFrame base (out.setWidth 64) 0 (2 * qLen) t.mem sf.mem :=
      fun a _ hb => Of a (.inr (by omega))
    refine ⟨by rw [V, rejected]; rfl, by rw [rejected]; exact B,
      (K.mono (by decide)).trans (Kf.mono (by decide)), ?_, ?_⟩
    · intro a hbase hout hstack
      exact (F a (by omega) hout).trans
        (shapeFrame_outside O a (.inr (by change 15712 ≤ ofs base a at hbase; omega)))
    · intro regs saved
      exact F.saved ha (by decide) sz (by have := scr.nowrap; omega) (shapeFrame_saved O saved)

theorem prevalidatedSigningInstalled_spec {s t : State} (A : SigningABI s)
    (I : Installed (argumentPointer s 9) ((arg s 10).toNat * 8) Entry.signArguments 2 4 6 s t)
    (valid : Spec.Dsa.validatePrivateKeyBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat) = true) :
    let result := Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)
    WP isa (PrevalidatedSign.sized (arg s 4).toNat (arg s 6).toNat) t fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (2 * (arg s 6).toNat) =
        result.getD (List.replicate (2 * (arg s 6).toNat) 0) ∧
      Keeps powerClob t sf ∧
      StackOutputFrame (t.gpr .esp) (argumentPointer s 9) (argumentPointer s 0) usedBytes
        (2 * (arg s 6).toNat) t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 9)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 9)) regs Entry.savedRegisters := by
  dsimp only
  have L : 0 < (arg s 4).toNat ∧ 0 < (arg s 6).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Key, KeyBytes⟩ := I.input (by decide : (2, .p) ∈ Entry.signArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Nonce, NonceBytes⟩ := I.input (by decide : (5, .nonce) ∈ Entry.signArguments) A.nonceBound
    (by rw [A.rd, A.wr]; simp) A.nonceScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowNonce.symm)
  obtain ⟨D, DigestBytes⟩ := I.input (by decide : (7, .digest) ∈ Entry.signArguments) A.digestBound
    (by rw [A.rd, A.wr]; simp) A.digestScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowDigest.symm)
  obtain ⟨Qptr, Gptr, Yptr, Xptr⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Y, X, KeyValue⟩ := privateKey_buffers Key L.1 L.2
    (by have := A.keyLength; omega) KeyBytes Qptr Gptr Yptr Xptr
  apply prevalidatedSignSized_spec (out := arg s 0) I.scr A.used A.lengths P Q G X Nonce D rfl rfl rfl rfl rfl
    (congrArg BitVec.toNat (I.arguments (8, .digestLen) (by decide))) DigestBytes
    (I.arguments (0, .out) (by decide))
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using I.arguments (6, .qLen) (by decide))
    (by have := A.outBound; have := A.outLength; omega)
    ?_ (by rw [← A.outLength]; exact A.outScratch.symm)
    (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.keyLength)
    (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]) KeyValue
    (congrArg Spec.Dsa.decodeBE NonceBytes.symm) valid
  intro e k he
  rw [I.keeps.2.2, A.wr]
  refine ⟨_, List.mem_cons_self, Offset.contains_base _ (by have := A.outLength; omega) ?_⟩
  have := A.outBound
  have := A.outLength
  omega

theorem prevalidatedSigningOperation_spec {s : State} (A : SigningABI s)
    (valid : Spec.Dsa.validatePrivateKeyBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat) = true) :
    let result := Spec.Dsa.signBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 7) (arg s 8).toNat)
    WP isa PrevalidatedSign.sign s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (arg s 1).toNat =
        result.getD (List.replicate (arg s 1).toNat 0) ∧
      abiPreserved s sf ∧
      StackOutputFrame (s.gpr .esp) (argumentPointer s 9) (argumentPointer s 0) ((arg s 10).toNat * 8)
        (arg s 1).toNat s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  dsimp only
  have sz : 8272 ≤ (arg s 10).toNat * 8 := by have H : 15712 ≤ (arg s 10).toNat * 8 := A.used; omega
  unfold PrevalidatedSign.sign Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (signingEntry_ok A) fun t I => ?_)
  refine WP.seq (generationDispatch_ok _ _ I.scr (by change 8256 ≤ _; omega)
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (4, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (6, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (prevalidatedSigningInstalled_spec A J valid) fun v ⟨Value, Bytes, K, O, Saved⟩ => ?_
  have Ov : StackOutputFrame (s.gpr .esp) (argumentPointer s 9) (argumentPointer s 0)
      ((arg s 10).toNat * 8) (arg s 1).toNat s.mem v.mem := by
    intro a hb ho hstack
    have H := A.used
    exact (O a (by omega) (by rw [← A.outLength]; exact ho)
      (by rw [J.keeps.1 .esp (by decide)]; exact hstack)).trans (J.outside a (.inr (by omega)))
  have Esp : v.gpr .esp = s.gpr .esp := (K.1 _ (by decide)).trans (J.keeps.1 _ (by decide))
  refine WP.seq (WP.mono (entryRestore_ok (J.scr.of_keeps K (by decide)) sz (Saved s.gpr J.saved))
    fun sf R => WP.block_nil ?_)
  refine ⟨?_, ?_, restored_abi R Esp (outputFrame_return Ov A.retScratch A.retOut A.stackLow), ?_, ?_, ?_⟩
  · rw [R.other .eax (by decide)]; exact Value
  · rw [R.mem, A.outLength]; exact Bytes
  · rw [R.mem]; exact Ov
  · rw [R.rd, K.2.1, J.keeps.2.1]
  · rw [R.wr, K.2.2, J.keeps.2.2]

end VG.Proof.Dsa.X86
