module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Sized
public import VerifiedGarbage.Proof.Bignum.X86.PublicFailurePost
public import VerifiedGarbage.Proof.Bignum.X86.PublicExponentArgs
public import VerifiedGarbage.Proof.Bignum.X86.PublicControls
public import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
public import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
public import VerifiedGarbage.Proof.Bignum.X86.PublicInstalled
public import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
public import VerifiedGarbage.Proof.Bignum.PublicWritten
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # Public RSA at a run-time width, from the entry to the return

The checks of `PublicFn` around `sized` (`Sized.lean`): the exponent saved
(`valid_ok`), checked (`checkExponent_ok`) after the modulus (`body_ok`),
with the room for the multiplications' calls below `esp` (`Room`), which
the contract's 96 bytes of stack give (`TopABI`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicContext
open VG.Proof.Dsa.X86 (argumentPointer)

/-- What the calls need beyond `PublicInputs`. -/
structure Room (base : Addr) (bytes : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  hbase : (args 8).toNat = base.toNat
  hbytes : bytes = (args 9).toNat * 8
  room : CallRoom (s.gpr .esp) base bytes
  top : (s.gpr .esp).toNat + 44 ≤ 2 ^ 32

theorem Room.keep {base : Addr} {bytes : Nat} {args : Nat → BitVec 32} {s t : State} (X : Room base bytes args s)
    {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs) : Room base bytes args t :=
  ⟨X.hbase, X.hbytes, by rw [K.1 _ sp]; exact X.room, by rw [K.1 _ sp]; exact X.top⟩

/-- `PublicResult`, with the stack below `sp` changed. -/
def Result (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (mem : Mem) (e : Nat)
    (t : State) : Prop :=
  let m := Spec.Rsa.os2ip (Spec.Rsa.bytesAt mem (byteAddr (args 2)) len)
  let x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt mem (byteAddr (args 6)) len)
  Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = Spec.Rsa.i2osp (if x < m then x ^ e % m else 0) len ∧
  t.gpr .eax = BitVec.ofNat 32 (decide (x < m)).toNat ∧
  Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩, below sp 96] mem t.mem

/-- `PublicPost`, with the stack below `sp` changed. -/
def Post (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (mem : Mem) (t : State) : Prop :=
  Spec.Rsa.written t.mem (byteAddr (args 0)) len (t.gpr .eax)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt mem (byteAddr (args 2)) len)
      (Spec.Rsa.bytesAt mem (byteAddr (args 4)) (args 5).toNat)
      (Spec.Rsa.bytesAt mem (byteAddr (args 6)) len)) ∧
  Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩, below sp 96] mem t.mem

theorem Post.of_public {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {mem : Mem}
    {t : State} (P : PublicPost base bytes len args mem t) : Post base bytes len args sp mem t :=
  ⟨P.1, P.2.mono (by simp)⟩

theorem Result.written {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {mem : Mem}
    {t : State}
    (R : Result base bytes len args sp mem
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt mem (byteAddr (args 4)) (args 5).toNat)) t)
    (modulus : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt mem (byteAddr (args 2)) len)) len = true)
    (exponent : Spec.Rsa.exponentValid
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt mem (byteAddr (args 4)) (args 5).toNat)) = true) :
    Post base bytes len args sp mem t := by
  obtain ⟨Y, B, F⟩ := R
  refine ⟨publicOutput_written (bytesAt_length _ _ _) modulus exponent ?_ B, F⟩
  rw [powMod_eq]
  split <;> simp_all only [ite_true, ite_false, i2osp_zero']

theorem valid_ok {s : State} {base : Addr} {bytes len e : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s) (X : Room base bytes args s)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true)
    (he : e < 2 ^ 33) (lo : s.gpr .ebx = BitVec.ofNat 32 (e % 2 ^ 32))
    (hi : s.gpr .edx = BitVec.ofNat 32 (VG.Proof.Bignum.exponentHigh e)) :
    WP isa PublicRt.valid s fun t => Result base bytes len args (s.gpr .esp) s.mem e t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have sz := PublicContext.size_eq (Spec.Rsa.modulusWords len)
  have space := h.space
  have nw := h.scratch.nowrap
  unfold PublicRt.valid
  refine WP.seq (WP.mono (saveExponent_ok h.scratch (by omega) he lo hi) fun v ⟨E, O, K⟩ => ?_)
  have O' : Outside base 0 bytes s.mem v.mem := O.mono (by omega) (by omega)
  have hv := h.keep K (by decide) (by decide) O'
  have ns := scratch_bytes O' (by have := h.upper; omega) h.nApart
  have xs := scratch_bytes O' (by have := h.upper; omega) h.inApart
  have sp : v.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  refine WP.mono (sized_ok hv X.hbase X.hbytes (by rw [sp]; exact X.room) (by rw [sp]; exact X.top)
    (by rw [ns]; exact valid) E) fun t ⟨R, B, F, Kt⟩ => ?_
  rw [sp] at F
  refine ⟨⟨by simpa only [ns, xs] using R, by simpa only [ns, xs] using B, ?_⟩, (K.mono (by decide)).trans Kt⟩
  have Os : Outside base 16 (bytes - 16) s.mem v.mem := O.mono (by omega) (by omega)
  exact ((outside_frame Os (by omega)).mono (by simp)).trans F

theorem checkExponent_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s) (X : Room base bytes args s)
    (modulus : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true) :
    WP isa PublicRt.checkExponent s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold PublicRt.checkExponent
  refine WP.seq (WP.mono (publicExponent_ok h) fun u ⟨E, Lo, Hi, M, K⟩ => ?_)
  refine WP.seq (WP.mono (exponentFlag_ok _ E) fun v ⟨Z, Mv, Kv⟩ => ?_)
  have Msv : v.mem = s.mem := Mv.trans M
  have Ksv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := K.trans (Kv.mono (by decide))
  have hv := h.keep Ksv (by decide) (by decide) (by rw [Msv]; exact Outside.refl _ _ _ _)
  have sp : v.gpr .esp = s.gpr .esp := Ksv.1 _ (by decide)
  refine WP.ite (!Spec.Rsa.exponentValid
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat))) Z ?_ ?_
  · intro bad
    have invalid : Spec.Rsa.exponentValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = false := by
      simpa using bad
    refine WP.mono (publicFailure_post hv (by simp only [Msv, Spec.Rsa.publicOpChecked, invalid,
      Bool.false_eq_true, ite_false])) fun t ⟨P, T⟩ => ?_
    exact ⟨Post.of_public (by simpa only [Msv] using P), Ksv.trans T⟩
  · intro good
    have valid : Spec.Rsa.exponentValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)) = true := by
      simpa using good
    have bound : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat) < 2 ^ 33 := by
      have H := valid
      simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq] at H
      exact H.2
    refine WP.mono (valid_ok hv (X.keep Ksv (by decide)) (by rw [Msv]; exact modulus) bound
      ((Kv.1 .ebx (by decide)).trans Lo) ((Kv.1 .edx (by decide)).trans Hi))
      fun t ⟨R, T⟩ => ?_
    rw [Msv, sp] at R
    exact ⟨R.written modulus valid, Ksv.trans T⟩

theorem body_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s) (X : Room base bytes args s) :
    WP isa PublicRt.body s fun t => Post base bytes len args (s.gpr .esp) s.mem t ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold PublicRt.body
  refine WP.seq (WP.mono (argumentPair_ok (c := BitVec.ofNat 32 len) (by decide) (by decide)
    ((h.stack 2 (by decide)).readSrc) (by rw [← h.nLen]; exact (h.stack 3 (by decide)).readSrc))
    fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.seq (WP.mono (modulusCheck_ok u h.lower h.upper (by rw [P]; exact h.nFit)
    (by rw [P, K.2.1, K.2.2]; exact h.nRead) C) fun v ⟨Z, Mv, Kv⟩ => ?_)
  rw [P, M] at Z
  have Msv : v.mem = s.mem := Mv.trans M
  have Ksv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v :=
    (K.mono (by decide)).trans (Kv.mono (by decide))
  have hv := h.keep Ksv (by decide) (by decide) (by rw [Msv]; exact Outside.refl _ _ _ _)
  have sp : v.gpr .esp = s.gpr .esp := Ksv.1 _ (by decide)
  refine WP.ite (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len)
    Z ?_ ?_
  · intro valid
    refine WP.mono (checkExponent_ok hv (X.keep Ksv (by decide)) (by rw [Msv]; exact valid)) fun t ⟨R, T⟩ => ?_
    rw [Msv, sp] at R
    exact ⟨R, Ksv.trans T⟩
  · intro invalid
    have failed : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt v.mem (byteAddr (args 2)) len)
        (Spec.Rsa.bytesAt v.mem (byteAddr (args 4)) (args 5).toNat)
        (Spec.Rsa.bytesAt v.mem (byteAddr (args 6)) len) = none := by
      simp only [Msv, Spec.Rsa.publicOpChecked, Spec.Rsa.publicOp, bytesAt_length, invalid,
        Bool.false_eq_true, ite_false, ite_self]
    refine WP.mono (publicFailure_post hv failed) fun t ⟨R, T⟩ => ?_
    exact ⟨Post.of_public (by simpa only [Msv] using R), Ksv.trans T⟩

/-- The contract's resources with 96 bytes of stack: those of the copies per width, and the room for calls. -/
structure TopABI (s : State) : Prop where
  abi : PublicABI s
  room : CallRoom (s.gpr .esp) (argumentPointer s 8) ((arg s 9).toNat * 8)
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 40⟩

theorem topABI_of {s : State} (h : (Proof.Rsa.publicCheckedContract abi 96).pre s) : TopABI s := by
  sig_pre [Proof.Rsa.publicCheckedContract, Proof.Rsa.publicSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  have low : 96 ≤ (s.gpr .esp).toNat := by with_reducible assumption
  have bs : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - 96#64, 96⟩
      ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩ := by with_reducible assumption
  refine ⟨?_, ⟨low, ?_⟩, by with_reducible assumption⟩
  · constructor <;> first
      | with_reducible assumption
      | omega
      | exact bs.sub_left (VG.X86.Taint.below_sub (by decide) (by decide))
  · simp only [below]
    rw [VG.X86.Taint.sub_setWidth low]
    exact bs

end VG.Proof.Bignum.X86.PublicRt
