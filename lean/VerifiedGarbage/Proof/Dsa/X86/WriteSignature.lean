module

public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.WriteScalar
import VerifiedGarbage.Proof.Dsa.X86.Persistent
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
public import VerifiedGarbage.Proof.Dsa.X86.OutputCall
import VerifiedGarbage.Proof.Dsa.X86.BodyTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! ### `Dsa.X86.SignSizedTiming`, which the modules that import this one used -/

section

/-! # Public shape rejection for signing -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem signingShape_relCT (L : CallLayout) (digestLen : Nat) (out : BitVec 32)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => (ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t) ∧
      OutputCallReady L out s ∧ OutputCallReady L out t)
      (Shape.check L.pLen L.qLen)
      (fun s t => ((VG.X86.Taint.Agree (workspaceTaint false) s t ∧
        (shapeValid L.p L.q → ShapedCall L digestLen s ∧ ShapedCall L digestLen t)) ∧
        OutputCallReady L out s ∧ OutputCallReady L out t) ∧
        s.zf = some (!decide (shapeValid L.p L.q)) ∧ t.zf = some (!decide (shapeValid L.p L.q))) := by
  intro s t tr ur sf tf ⟨H, S, T⟩ E F
  obtain ⟨trace, A, Z1, Z2⟩ := shapeCall_relCT L digestLen P Q stable hd _ _ _ _ _ _ H E F
  obtain ⟨_, _, K1, O1⟩ := wp_result (shapeCall_ok H.1 P Q stable hd) E
  obtain ⟨_, _, K2, O2⟩ := wp_result (shapeCall_ok H.2 P Q stable hd) F
  exact ⟨trace, ⟨A, S.keepShape K1 (by decide) (by decide) O1,
    T.keepShape K2 (by decide) (by decide) O2⟩, Z1, Z2⟩

theorem signSized_relCT (L : CallLayout) (digestLen : Nat) (out : BitVec 32)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (X : (.input .x, L.qLen) ∈ L.inputs) (K : (.input .nonce, L.qLen) ∈ L.inputs)
    (D : (.input .digest, digestLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => (ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t) ∧
      OutputCallReady L out s ∧ OutputCallReady L out t)
      (Entry.sized true L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold Entry.sized
  refine RelCT.seq (signingShape_relCT L digestLen out P Q stable hd)
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  by_cases valid : shapeValid L.p L.q
  · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have B := shape_digest_width valid
    have CT := callSignBody_relCT L out (.inl ⟨_, P, Nat.le_refl _⟩) (.inl ⟨_, Q, Nat.le_refl _⟩)
      G Y X K ⟨_, D, by rw [hd]; exact Nat.min_le_left _ _⟩ (by rw [hd]; omega_using [B])
    exact CT.mono (fun _ _ H => ⟨⟨(H.1.2 True.intro).1.ready, (H.1.2 True.intro).2.ready⟩,
      H.2.1.signature (H.1.2 True.intro).1, H.2.2.signature (H.1.2 True.intro).2⟩) (fun _ _ h => h)
  · simp only [valid, decide_false, Bool.not_false, ite_true]
    exact (signFailure_relCT L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.2.1.scr, H.2.2.scr, H.2.1.pointer.trans H.2.2.pointer.symm,
        H.2.1.qLength.trans H.2.2.qLength.symm⟩) (fun _ _ h => h)

end VG.Proof.Dsa.X86

end

end

/-! # Both signature scalar writes preserve the acceptance mask -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem writeSignature_ok {s0 : State} {base : Addr} {size pLen qLen p q rv sv : Nat} {out : BitVec 32}
    (M : Moduli base size pLen qLen p q s0) (accepted : Bool)
    (hm : flagW base (Layout.field .mask) s0 = if accepted then BitVec.allOnes 32 else 0)
    (hr : operandValue s0 base (.local r) qLen = rv)
    (hs : operandValue s0 base (.local VG.Impl.Dsa.Layout.s) qLen = sv)
    (hp : pointerValue base s0 (.input .out) = out)
    (hf : out.toNat + 2 * qLen ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ 2 * qLen → InRegions s0.wr (out.setWidth 64 + BitVec.ofNat 64 e) k)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 2 * qLen⟩) :
    WP isa (.seq (SignVerify.writeScalar qLen r false) (SignVerify.writeScalar qLen VG.Impl.Dsa.Layout.s true)) s0 fun sf =>
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) qLen =
        (if accepted then Spec.Dsa.encodeBE qLen rv else List.replicate qLen 0) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64 + BitVec.ofNat 64 qLen) qLen =
        (if accepted then Spec.Dsa.encodeBE qLen sv else List.replicate qLen 0) ∧
      flagW base (Layout.field .mask) sf = flagW base (Layout.field .mask) s0 ∧
      Keeps powerClob s0 sf ∧
      OutputFrame base (out.setWidth 64) (contextBytes ((qLen + 7) / 8)) (2 * qLen) s0.mem sf.mem := by
  have L := M.lengths
  let n := (qLen + 7) / 8
  have N : n ≤ 48 := by dsimp [n]; omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have B := slot_bound (n := n) (i := 5) (by decide)
  simp only [stride] at B
  have bound : size ≤ 2 ^ 64 := by have := M.scr.nowrap; omega_using [this]
  have hctx := M.context N
  have slotSub : Region.Sub ⟨off base (slot n 5), 8 * n⟩ ⟨base, size⟩ := Offset.sub_base base (by omega_using [B, hctx])
  have firstSub : Region.Sub ⟨out.setWidth 64, qLen⟩ ⟨out.setWidth 64, 2 * qLen⟩ := by
    simpa only [BitVec.add_zero] using Offset.sub_base (out.setWidth 64) (d := 0) (by omega_using [] : 0 + qLen ≤ 2 * qLen)
  have secondSub : Region.Sub ⟨out.setWidth 64 + BitVec.ofNat 64 qLen, qLen⟩ ⟨out.setWidth 64, 2 * qLen⟩ :=
    Offset.sub_base _ (by omega_using [])
  have A1 := ha.sub_right firstSub
  have A2 := ha.sub_right secondSub
  have A := M.aligned
  refine WP.seq (WP.mono (writeScalar_ok M.scr M.saved rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) hctx
    (M.scalarReady (by decide) N) false accepted hm
    (by simpa using hp.symm) (by omega_using [hf]) (by intro e k h; exact hw e k (by omega_using [h]))
    (A1.sub_left slotSub)) fun s1 ⟨V1, K1, F1⟩ => ?_)
  have H1 : OutputFrame base (out.setWidth 64) (contextBytes n) qLen s0.mem s1.mem := F1
  have Scr1 := M.scr.of_keeps K1 (by decide)
  have mask1 : flagW base (Layout.field .mask) s1 = flagW base (Layout.field .mask) s0 :=
    H1.scratch_word A1 (by change contextBytes n ≤ 8244; omega_using [C])
      (by have H : 8256 ≤ size := M.saved; change 8248 ≤ size; omega_using [H]) bound
  have ptr1 : pointerValue base s1 (.input .out) = out := by
    change s1.mem.readW (off base (Layout.field .out)) 32 = out
    rw [H1.scratch_word A1 (by change contextBytes n ≤ 8224; omega_using [C])
      (by have H : 8256 ≤ size := M.saved; change 8228 ≤ size; omega_using [H]) bound]
    exact hp
  have sfit := M.scalarFit (d := VG.Impl.Dsa.Layout.s) (by decide)
  have sLow : contextBytes n ≤ VG.Impl.Dsa.Layout.s := by change contextBytes n ≤ 14752; omega_using [C]
  have S1 : operandValue s1 base (.local VG.Impl.Dsa.Layout.s) qLen = sv := by
    unfold operandValue
    rw [local_pointer Scr1 (by omega_using [L]) (Nat.le_trans sfit M.extent),
      H1.scratch_bytes A1 sLow (Nat.le_trans sfit M.extent) bound,
      ← local_pointer M.scr (by omega_using [L]) (Nat.le_trans sfit M.extent)]
    exact hs
  let out2 := out + BitVec.ofNat 32 qLen
  have out2Addr : out2.setWidth 64 = out.setWidth 64 + BitVec.ofNat 64 qLen :=
    addr_eq (x := out) (k := qLen) (by omega_using [hf])
  have out2Nat : out2.toNat = out.toNat + qLen := by
    dsimp [out2]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hf] : qLen < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [hf])]
  refine WP.mono (writeScalar_ok (out := out2) Scr1 M.saved rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) hctx
    (localReady Scr1 (by omega_using [L]) (Nat.le_trans sfit M.extent) sLow) true accepted (mask1.trans hm)
    (by simp only [ptr1, ite_true]; rfl) (by rw [out2Nat]; omega_using [hf])
    (by
      intro e k h
      rw [out2Addr, K1.2.2, Offset.add_add]
      exact hw (qLen + e) k (by omega_using [h]))
    (by rw [out2Addr]; exact A2.sub_left slotSub)) fun sf ⟨V2, K2, F2⟩ => ?_
  have H2 : OutputFrame base (out.setWidth 64 + BitVec.ofNat 64 qLen) (contextBytes n) qLen s1.mem sf.mem := by
    simpa only [OutputFrame, n, out2Addr] using F2
  have ctxSub : Region.Sub ⟨base, contextBytes n⟩ ⟨base, size⟩ := by
    simpa only [BitVec.add_zero] using Offset.sub_base base (d := 0) (n := contextBytes n) (k := size) (by omega_using [hctx])
  refine ⟨?_, ?_, ?_, K1.trans K2, ?_⟩
  · rw [H2.other_bytes (A1.symm.sub_right ctxSub)
      (Offset.base_disjoint _ (by omega_using []) (by omega_using [hf])) (by omega_using [hf]), V1, hr]
  · simpa only [out2Addr, S1] using V2
  · exact (H2.scratch_word A2 (by change contextBytes n ≤ 8244; omega_using [C])
      (by have H : 8256 ≤ size := M.saved; change 8248 ≤ size; omega_using [H]) bound).trans mask1

  · simpa only [Nat.two_mul] using H1.join H2 (by omega_using [hf])

end VG.Proof.Dsa.X86
