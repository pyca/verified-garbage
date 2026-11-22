module

public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByte
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpState
public import VerifiedGarbage.Impl.Bignum.Arm.Exp
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteHeadCT
public import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBitsCT
import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteHead
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpState
meta import VerifiedGarbage.Impl.Bignum.Arm.Exp
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteHeadCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpBitsCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ConditionalExp.ExpByteHead
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Bignum.Arm.ConditionalExp.ExpByteCT`, which only this module used -/

section

/-! # Processing one exponent byte reveals only that public byte and its address -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)

structure ExpByteInput (ok : Prop) (base ep : BitVec 32) (len w M x E : Nat) (b : Byte) (s : State) : Prop where
  power : ExpState ok base len w M x E s
  pointer : s.mem.readW (VG.Proof.Mont.off (State.addr base) 128) 32 = ep
  read : InRegions (s.rd ++ s.wr) (State.addr ep) 1
  byte : s.mem (State.addr ep) = b

theorem expByte_ct {base ep : BitVec 32} {len w M1 M2 x1 x2 E : Nat} {b : Byte}
    {Q : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w Q regions) (ct : TwoExp.MontgomeryTiming K) :
    RelCT isa (fun s t => (ExpByteInput ok base ep len w M1 x1 E b s ∧ Q s) ∧
      (ExpByteInput ok base ep len w M2 x2 E b t ∧ Q t) ∧ s.sp = t.sp)
      (.seq expByteHead (.seq (expBitsWith K.op) (.block expByteNext))) (fun _ _ => True) := by
  let P := fun (s t : State) => (ExpByteInput ok base ep len w M1 x1 E b s ∧ Q s) ∧
    (ExpByteInput ok base ep len w M2 x2 E b t ∧ Q t) ∧ s.sp = t.sp
  have wpHead (s : State) {M x : Nat} (h : ExpByteInput ok base ep len w M x E b s ∧ Q s) :
      WP isa expByteHead s fun t => ExpBitState ok base len w M x E b.toNat 0 t ∧ Q t := by
    have head := expByteHead_ok s h.1.power h.1.pointer h.1.read
    rw [h.1.byte] at head
    exact WP.mono head (fun _ j => ⟨j.1, K.stable j.2.2.1 (j.2.2.2.mono (by decide)) h.2⟩)
  have head := (relCT_keep_sp (expByteHead_ct.mono (P' := P)
    (fun _ _ h => ⟨⟨h.1.1.power.ready, h.1.1.pointer⟩, ⟨h.2.1.1.power.ready, h.2.1.1.pointer⟩⟩)
    (fun _ _ h => h)) (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨wpHead s h.1, wpHead t h.2.1⟩)
  have wpBits (s : State) {M x : Nat} (h : ExpBitState ok base len w M x E b.toNat 0 s ∧ Q s) :
      WP isa (expBitsWith K.op) s fun t => ExpState ok base len w M x (256 * E + b.toNat) t ∧ Q t :=
    WP.mono (expBits_ok s K h.1 h.2 b.isLt) (fun _ h => ⟨h.1, h.2.1⟩)
  have bits := ((expBits_ct (M1 := M1) (M2 := M2) (x1 := x1) (x2 := x2) (E := E) K ct b.isLt).mono
    (P' := fun (s t : State) => s.sp = t.sp ∧ (ExpBitState ok base len w M1 x1 E b.toNat 0 s ∧ Q s) ∧
      (ExpBitState ok base len w M2 x2 E b.toNat 0 t ∧ Q t))
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h)).wp
    (fun s t h => ⟨wpBits s h.2.1, wpBits t h.2.2⟩)
  have next : RelCT isa (fun s t => True ∧ (ExpState ok base len w M1 x1 (256 * E + b.toNat) s ∧ Q s) ∧
      (ExpState ok base len w M2 x2 (256 * E + b.toNat) t ∧ Q t)) (.block expByteNext) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.2.1.1.ready.ptr.trans h.2.2.1.ready.ptr.symm
  exact head.seq (bits.seq next)

end VG.Proof.Bignum.Arm.ConditionalExp

end

end

/-! # Public buffer invariants for the exponent-byte timing proof -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.ConditionalExp

variable {ok : Prop}
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure ExpByteState (ok : Prop) (base ep : BitVec 32) (len w M x : Nat) (eb : List Byte) (j : Nat) (s : State) : Prop where
  power : ExpState ok base len w M x (pre eb j) s
  pointer : s.mem.readW (VG.Proof.Mont.off (State.addr base) 128) 32 = ep + BitVec.ofNat 32 j
  count : s.mem.readW (VG.Proof.Mont.off (State.addr base) 132) 32 = BitVec.ofNat 32 (eb.length - j)
  countFit : eb.length < 2 ^ 32
  sourceFit : ep.toNat + eb.length ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr ep) eb.length
  separate : Region.Disjoint ⟨State.addr ep, eb.length⟩ ⟨State.addr base, 8 * len⟩
  bytes : ∀ i (hi : i < eb.length), s.mem (State.addr ep + BitVec.ofNat 64 i) = eb[i]

theorem ExpByteState.input {s : State} {base ep : BitVec 32} {len w M x j : Nat} {eb : List Byte}
    (h : ExpByteState ok base ep len w M x eb j s) (hj : j < eb.length) :
    ExpByteInput ok base (ep + BitVec.ofNat 32 j) len w M x (pre eb j) eb[j] s := by
  have address : State.addr (ep + BitVec.ofNat 32 j) = State.addr ep + BitVec.ofNat 64 j :=
    addr_add (by have := h.sourceFit; omega_using [hj, this])
  refine ⟨h.power, h.pointer, ?_, ?_⟩
  · rw [address]
    exact CallLay.inRegions_sub h.read (by omega_using [hj]) (by have := h.countFit; omega_using [this])
  · rw [address]; exact h.bytes j hj

theorem expByteState_step (s : State) {base ep : BitVec 32} {len w M x j : Nat} {eb : List Byte}
    {Q : State → Prop} {regions : List Region} (K : TwoExp.Montgomery base len w Q regions)
    (h : ExpByteState ok base ep len w M x eb j s) (q : Q s) (hj : j < eb.length)
    (sepR : ∀ r ∈ regions, Region.Disjoint ⟨State.addr ep, eb.length⟩ r) :
    WP isa (.seq expByteHead (.seq (expBitsWith K.op) (.block expByteNext))) s fun t =>
      (ExpByteState ok base ep len w M x eb (j + 1) t ∧ Q t) ∧ t.z = decide (j + 1 = eb.length) := by
  have input := h.input hj
  refine WP.mono (expByte_ok s K h.power q (by omega_using [hj]) (by have := h.countFit; omega_using [this])
    h.pointer h.count input.read) ?_
  rintro t ⟨power, qt, pointer, count, zero, frame, rest⟩
  rw [input.byte] at power
  have prefixEq : 256 * pre eb j + (eb[j]).toNat = pre eb (j + 1) := by
    rw [pre_succ eb hj, Nat.mul_comm]
  rw [prefixEq] at power
  refine ⟨⟨⟨power, ?_, ?_, h.countFit, h.sourceFit, ?_, h.separate, ?_⟩, qt⟩, ?_⟩
  · rw [pointer]
    change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [count]; congr 1
  · rw [rest.rd, rest.wr]; exact h.read
  · intro i hi
    rw [frame.bytes (R := ⟨State.addr ep, eb.length⟩) (fun r hr => sepR r hr)
      (by change eb.length ≤ 2 ^ 64; have := h.countFit; omega_using [this]) hi]
    exact h.bytes i hi
  · rw [zero]; exact decide_eq_decide.mpr (by omega_using [])

end VG.Proof.Bignum.Arm.ConditionalExp
