module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeSized
public import VerifiedGarbage.Proof.Bignum.X86.CrtEntryTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtModulusTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtFailureTiming
public import VerifiedGarbage.Proof.Bignum.X86.CrtObservations
public import VerifiedGarbage.Proof.Bignum.X86.CrtArgumentsEq
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.X86.CrtResources
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Rsa.Contract

/-! # Private CRT RSA at a run-time width on i686 against its contract

The entry, the modulus's check, the failure and the return are the fixed
widths' (`Crt.entry_relCT`, `Crt.modulus_relCT`, `Crt.failure_relCT`,
`Crt.restore_relCT`), with `sized` related by `sizedNarrow_relCT` from what
each run keeps (`Side`): constant time but for the modulus
(`constantTime`), and with `correct`, `verified`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.Crt (componentValue Pair)
open VG.Proof.Dsa.X86 (argumentPointer wp_result)
open VG.Proof.Bignum.X86.PublicRt (setWidth_toNat)

/-- The contract's resources, and the output apart from the arguments. -/
structure TopABI (s : State) : Prop where
  abi : CrtABI s
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 72⟩

theorem topABI_of {s : State} (h : (Proof.Rsa.privateCrtContract abi 96).pre s) : TopABI s := by
  refine ⟨crtABI_of h, ?_⟩
  sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  with_reducible assumption

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- What each run keeps from the entry on: its inputs, `esp`, and the arguments apart from the output and
the working space. -/
def Side (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  RIn base bytes len args s ∧ s.gpr .esp = sp ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ ⟨byteAddr (args 0), len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ ⟨base, bytes⟩

theorem Side.keep {sp : BitVec 32} {s t : State} (S : Side base bytes len args sp s) {regs : List Reg}
    (K : Keeps regs s t) (di : .edi ∉ regs) (sp' : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) :
    Side base bytes len args sp t :=
  ⟨S.1.keep K di sp' O, (K.1 _ sp').trans S.2.1, by rw [K.1 _ sp']; exact S.2.2.1,
    by rw [K.1 _ sp']; exact S.2.2.2⟩

theorem Side.pair {sp : BitVec 32} {s t : State} (S₁ : Side base bytes len args sp s)
    (S₂ : Side base bytes len args sp t) : Pair base bytes len args s t :=
  ⟨S₁.1.crt, S₂.1.crt, S₁.2.1.trans S₂.2.1.symm⟩

theorem body_relCT (sp : BitVec 32) :
    RelCT isa (fun s t => Side base bytes len args sp s ∧ Side base bytes len args sp t ∧
      Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)
      CrtRt.body (fun _ _ => True) := by
  let R := fun s t => (Side base bytes len args sp s ∧ Side base bytes len args sp t) ∧
    ∃ b : Bool, s.zf = some b ∧ t.zf = some b ∧
      (b = true → Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true ∧
        Spec.Rsa.modulusValid (componentValue t.mem args 2) len = true)
  have Branch : RelCT isa R (.ite .e CrtRt.sized PublicFn.failure) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (P := R)
    · intro s t ⟨_, b, Zs, Zt, _⟩
      exact Zs.trans Zt.symm
    · intro s t tr ur sf tf ⟨⟨⟨S₁, S₂⟩, b, Zs, _, V⟩, Z⟩ E F
      have B : b = true := by
        change s.zf = some true at Z
        exact Option.some.inj (Zs.symm.trans Z)
      exact sizedNarrow_relCT sp _ _ _ _ _ _ ⟨⟨S₁.1, S₁.2.1, (V B).1, S₁.2.2⟩,
        ⟨S₂.1, S₂.2.1, (V B).2, S₂.2.2⟩⟩ E F
    · exact (Crt.failure_relCT base bytes len args).mono (fun _ _ H => H.1.1.1.pair H.1.1.2) (fun _ _ h => h)
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨S₁, S₂, N⟩ E F
  have modulus : ∀ {m : Mem} {x : State}, Side base bytes len args sp x →
      componentValue m args 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 2)) len) := by
    intro m x S
    unfold componentValue
    change Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 2)) (args 3).toNat) = _
    rw [S.1.crt.modulus_length]
  cases E with
  | @seq _ _ _ u _ _ _ E1 E2 =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 F2 =>
      have T1 := (Crt.modulus_relCT base bytes len args _ _ _ _ _ _ (S₁.pair S₂) E1 F1).1
      obtain ⟨Zs, Ms, Ks⟩ := wp_result (Crt.modulus_ok S₁.1.crt) E1
      obtain ⟨Zt, Mt, Kt⟩ := wp_result (Crt.modulus_ok S₂.1.crt) F1
      have U₁ := S₁.keep Ks (by decide) (by decide) (by rw [Ms]; exact Outside.refl _ _ _ _)
      have U₂ := S₂.keep Kt (by decide) (by decide) (by rw [Mt]; exact Outside.refl _ _ _ _)
      have Relation : R u v := ⟨⟨U₁, U₂⟩, _, Zs, by rw [N]; exact Zt, fun hb => ⟨?_, ?_⟩⟩
      · have T2 := (Branch _ _ _ _ _ _ Relation E2 F2).1
        exact ⟨by rw [T1, T2], trivial⟩
      · rw [modulus U₁, Ms]; exact hb
      · rw [modulus U₂, Mt, ← N]; exact hb

end

/-- The arguments' bytes lie apart from the output and the working space. -/
theorem args_apart {s : State} (A : TopABI s) {r : Region}
    (hret : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r) (hargs : Region.Disjoint ⟨argAddr s 0, 72⟩ r) :
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ r :=
  VG.X86.Taint.frame_disjoint (n := 72) (by have := A.abi.stackBound; omega) hret hargs

theorem operation_trace {s t : State} (A : TopABI s) (B : TopABI t)
    (args : ∀ i < 18, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (N : Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa CrtRt.code s tr sf) (F : Exec isa CrtRt.code t ur tf) : tr = ur := by
  have A0 := args 0 (by decide)
  have A1 := args 1 (by decide)
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A8 := args 16 (by decide)
  have A9 := args 17 (by decide)
  have hb : (arg s 16).toNat = (argumentPointer s 16).toNat := (setWidth_toNat _).symm
  cases E with
  | @seq _ _ _ u _ _ _ E1 Erest =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 Frest =>
      have T1 := (Crt.entry_relCT _ _ _ _ _ _
        ⟨SP, A8, (A.abi.stackArgument (by decide : 16 < 18)).readSrc,
          (B.abi.stackArgument (by decide : 16 < 18)).readSrc⟩ E1 F1).1
      obtain ⟨Is, _, Ks, Os⟩ := wp_result (Crt.installed_ok A.abi) E1
      obtain ⟨It, _, Kt, Ot⟩ := wp_result (Crt.installed_ok B.abi) F1
      have Iv : Crt.Inputs (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) v := by
        have J := It.argsEq (fun i hi => (args i hi).symm)
        simpa only [argumentPointer, ← A8, ← A9, ← A3] using J
      have Ov : VG.Proof.Mont.Outside (argumentPointer s 16) 0 ((arg s 17).toNat * 8) t.mem v.mem := by
        simpa only [argumentPointer, ← A8, ← A9] using Ot
      have need := need_le A.abi.lengths.1 A.abi.scratchLength
      have espu : u.gpr .esp = s.gpr .esp := Ks.1 _ (by decide)
      have espv : v.gpr .esp = s.gpr .esp := (Kt.1 _ (by decide)).trans SP.symm
      have Su : Side (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) (s.gpr .esp) u := by
        refine ⟨In.ofInputs Is need hb rfl, espu, ?_, ?_⟩
        · rw [espu, ← A.abi.outLength]; exact args_apart A A.abi.retOut A.outArgs.symm
        · rw [espu]; exact args_apart A A.abi.retScratch A.abi.scratchArgs.symm
      have Sv : Side (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) (s.gpr .esp) v := by
        refine ⟨In.ofInputs Iv need hb rfl, espv, ?_, ?_⟩
        · rw [espv]
          have D := args_apart B B.abi.retOut B.outArgs.symm
          simp only [argumentPointer, ← A0, ← A1, ← SP] at D
          rw [← A.abi.outLength]; exact D
        · rw [espv]
          have D := args_apart B B.abi.retScratch B.abi.scratchArgs.symm
          simp only [argumentPointer, ← A8, ← A9, ← SP] at D
          exact D
      have Ns := scratch_bytes Os (by have := A.abi.lengths.2; omega) (Is.apart 2 (by decide))
      have Nt := scratch_bytes Ov (by have := A.abi.lengths.2; omega) (Iv.apart 2 (by decide))
      have NN : Spec.Rsa.bytesAt u.mem (byteAddr (arg s 2)) (arg s 3).toNat =
          Spec.Rsa.bytesAt v.mem (byteAddr (arg s 2)) (arg s 3).toNat := by
        rw [Ns, Nt]
        simpa only [argumentPointer, byteAddr, ← A2, ← A3] using N
      cases Erest with
      | @seq _ _ _ w _ _ _ E2 E3 =>
        cases Frest with
        | @seq _ _ _ z _ _ _ F2 F3 =>
          have T2 := (body_relCT (s.gpr .esp) _ _ _ _ _ _ ⟨Su, Sv, NN⟩ E2 F2).1
          obtain ⟨_, Ksu⟩ := wp_result (body_ok Su.1) E2
          obtain ⟨_, Ktv⟩ := wp_result (body_ok Sv.1) F2
          have Agree : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) w z :=
            agree_regs (by
              intro r hr
              obtain rfl := List.mem_singleton.mp hr
              rw [Ksu.1 _ (by decide), Ktv.1 _ (by decide)]
              exact (Su.pair Sv).agree.rf.1 _ (by decide))
          have T3 := (Crt.restore_relCT _ _ _ _ _ _ Agree E3 F3).1
          rw [T1, T2, T3]

theorem constantTime : ConstantTime isa (Proof.Rsa.privateCrtContract abi 96).pre
    (Proof.Rsa.privateCrtContract abi 96).pub CrtRt.code := by
  intro s t tr ur sf tf S T H E F
  have Args := Crt.arguments H
  exact operation_trace (topABI_of S) (topABI_of T) Args.2 Args.1 (Crt.modulusBytes H) E F

/-- Disjoint minimum-length buffers with a runtime-rejected zero modulus. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 64
    else if a = 0x2000d then 32
    else if a = 0x20010 then 64
    else if a = 0x20015 then 48
    else if a = 0x20018 then 64
    else if a = 0x2001d then 64
    else if a = 0x20020 then 1
    else if a = 0x20025 then 80
    else if a = 0x20028 then 1
    else if a = 0x2002d then 96
    else if a = 0x20030 then 1
    else if a = 0x20035 then 112
    else if a = 0x20038 then 1
    else if a = 0x2003d then 128
    else if a = 0x20040 then 1
    else if a = 0x20045 then 144
    else if a = 0x20048 then 32
    else if a = 0x20049 then 4 else 0
  rd := [⟨8192, 64⟩, ⟨12288, 64⟩, ⟨16384, 1⟩, ⟨20480, 1⟩, ⟨24576, 1⟩, ⟨28672, 1⟩, ⟨32768, 1⟩]
  wr := [⟨4096, 64⟩, ⟨36864, 8448⟩, ⟨0x20004, 72⟩]

theorem satisfiable : ∃ s, (Proof.Rsa.privateCrtContract abi 96).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 64 := by decide
  have a6 : arg satState 6 = 16384 := by decide
  have a7 : arg satState 7 = 1 := by decide
  have a8 : arg satState 8 = 20480 := by decide
  have a9 : arg satState 9 = 1 := by decide
  have a10 : arg satState 10 = 24576 := by decide
  have a11 : arg satState 11 = 1 := by decide
  have a12 : arg satState 12 = 28672 := by decide
  have a13 : arg satState 13 = 1 := by decide
  have a14 : arg satState 14 = 32768 := by decide
  have a15 : arg satState 15 = 1 := by decide
  have a16 : arg satState 16 = 36864 := by decide
  have a17 : arg satState 17 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, e, esp, satState, Spec.Rsa.lenValid,
      Spec.Rsa.scratchWords] using satState

theorem verified : Verified target CrtRt.code (Proof.Rsa.privateCrtContract abi 96) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Bignum.X86.CrtRt
