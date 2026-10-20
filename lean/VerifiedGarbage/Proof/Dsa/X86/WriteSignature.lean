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
  have N : n ≤ 48 := by dsimp [n]; omega
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have B := slot_bound (n := n) (i := 5) (by decide)
  simp only [stride] at B
  have bound : size ≤ 2 ^ 64 := by have := M.scr.nowrap; omega
  have hctx := M.context N
  have slotSub : Region.Sub ⟨off base (slot n 5), 8 * n⟩ ⟨base, size⟩ := Offset.sub_base base (by omega)
  have firstSub : Region.Sub ⟨out.setWidth 64, qLen⟩ ⟨out.setWidth 64, 2 * qLen⟩ := by
    simpa only [BitVec.add_zero] using Offset.sub_base (out.setWidth 64) (d := 0) (by omega : 0 + qLen ≤ 2 * qLen)
  have secondSub : Region.Sub ⟨out.setWidth 64 + BitVec.ofNat 64 qLen, qLen⟩ ⟨out.setWidth 64, 2 * qLen⟩ :=
    Offset.sub_base _ (by omega)
  have A1 := ha.sub_right firstSub
  have A2 := ha.sub_right secondSub
  have A := M.aligned
  refine WP.seq (WP.mono (writeScalar_ok M.scr M.saved rfl (by omega) (by omega) (by omega) hctx
    (M.scalarReady (by decide) N) false accepted hm
    (by simpa using hp.symm) (by omega) (by intro e k h; exact hw e k (by omega))
    (A1.sub_left slotSub)) fun s1 ⟨V1, K1, F1⟩ => ?_)
  have H1 : OutputFrame base (out.setWidth 64) (contextBytes n) qLen s0.mem s1.mem := F1
  have Scr1 := M.scr.of_keeps K1 (by decide)
  have mask1 : flagW base (Layout.field .mask) s1 = flagW base (Layout.field .mask) s0 :=
    H1.scratch_word A1 (by change contextBytes n ≤ 8244; omega)
      (by have H : 8256 ≤ size := M.saved; change 8248 ≤ size; omega) bound
  have ptr1 : pointerValue base s1 (.input .out) = out := by
    change s1.mem.readW (off base (Layout.field .out)) 32 = out
    rw [H1.scratch_word A1 (by change contextBytes n ≤ 8224; omega)
      (by have H : 8256 ≤ size := M.saved; change 8228 ≤ size; omega) bound]
    exact hp
  have sfit := M.scalarFit (d := VG.Impl.Dsa.Layout.s) (by decide)
  have sLow : contextBytes n ≤ VG.Impl.Dsa.Layout.s := by change contextBytes n ≤ 14752; omega
  have S1 : operandValue s1 base (.local VG.Impl.Dsa.Layout.s) qLen = sv := by
    unfold operandValue
    rw [local_pointer Scr1 (by omega) (Nat.le_trans sfit M.extent),
      H1.scratch_bytes A1 sLow (Nat.le_trans sfit M.extent) bound,
      ← local_pointer M.scr (by omega) (Nat.le_trans sfit M.extent)]
    exact hs
  let out2 := out + BitVec.ofNat 32 qLen
  have out2Addr : out2.setWidth 64 = out.setWidth 64 + BitVec.ofNat 64 qLen :=
    addr_eq (x := out) (k := qLen) (by omega)
  have out2Nat : out2.toNat = out.toNat + qLen := by
    dsimp [out2]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qLen < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (writeScalar_ok (out := out2) Scr1 M.saved rfl (by omega) (by omega) (by omega) hctx
    (localReady Scr1 (by omega) (Nat.le_trans sfit M.extent) sLow) true accepted (mask1.trans hm)
    (by simp only [ptr1, ite_true]; rfl) (by rw [out2Nat]; omega)
    (by
      intro e k h
      rw [out2Addr, K1.2.2, Offset.add_add]
      exact hw (qLen + e) k (by omega))
    (by rw [out2Addr]; exact A2.sub_left slotSub)) fun sf ⟨V2, K2, F2⟩ => ?_
  have H2 : OutputFrame base (out.setWidth 64 + BitVec.ofNat 64 qLen) (contextBytes n) qLen s1.mem sf.mem := by
    simpa only [OutputFrame, n, out2Addr] using F2
  have ctxSub : Region.Sub ⟨base, contextBytes n⟩ ⟨base, size⟩ := by
    simpa only [BitVec.add_zero] using Offset.sub_base base (d := 0) (n := contextBytes n) (k := size) (by omega)
  refine ⟨?_, ?_, ?_, K1.trans K2, ?_⟩
  · rw [H2.other_bytes (A1.symm.sub_right ctxSub)
      (Offset.base_disjoint _ (by omega) (by omega)) (by omega), V1, hr]
  · simpa only [out2Addr, S1] using V2
  · exact (H2.scratch_word A2 (by change contextBytes n ≤ 8244; omega)
      (by have H : 8256 ≤ size := M.saved; change 8248 ≤ size; omega) bound).trans mask1

  · simpa only [Nat.two_mul] using H1.join H2 (by omega)

end VG.Proof.Dsa.X86
