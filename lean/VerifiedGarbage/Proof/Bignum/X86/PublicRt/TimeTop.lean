module

public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeSized
meta import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeSized
public import VerifiedGarbage.Proof.Bignum.X86.PublicExponentTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicFailureTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicModulusTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicEntryTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentsEq
meta import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicObservations
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.X86.PublicResources
public import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.Proof.Rsa.Contract

/-! # The trace of public RSA at a run-time width, from the entry to the return

The checks around `sized` are `PublicFn`'s, related by their own lemmas
(`publicExponent_trace`, `publicModulus_relCT`, `publicFailure_relCT`,
`publicEntry_relCT`), with `sized` related by `sizedNarrow_relCT` from
what each run keeps (`Side`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PublicRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Dsa.X86

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- What each run keeps from the entry on: its inputs, the room for calls, `esp`, and the arguments apart
from the output and the working space. -/
def Side (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  PublicInputs base bytes len args s ∧ Room base bytes args s ∧ s.gpr .esp = sp ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 44⟩ ⟨byteAddr (args 0), len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 44⟩ ⟨base, bytes⟩

/-- The modulus is valid. -/
abbrev ValidAt (len : Nat) (args : Nat → BitVec 32) (s : State) : Prop :=
  Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true

theorem Side.keep {sp : BitVec 32} {s t : State} (S : Side base bytes len args sp s) {regs : List Reg}
    (K : Keeps regs s t) (di : .edi ∉ regs) (sp' : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) :
    Side base bytes len args sp t :=
  ⟨S.1.keep K di sp' O, S.2.1.keep K sp', (K.1 _ sp').trans S.2.2.1, by rw [K.1 _ sp']; exact S.2.2.2.1,
    by rw [K.1 _ sp']; exact S.2.2.2.2⟩

theorem Side.pair {sp : BitVec 32} {s t : State} (S₁ : Side base bytes len args sp s)
    (S₂ : Side base bytes len args sp t) : PublicPair base bytes len args s t :=
  ⟨S₁.1, S₂.1, S₁.2.2.1.trans S₂.2.2.1.symm⟩

theorem valid_relCT (sp : BitVec 32) :
    RelCT isa (fun s t => ((Side base bytes len args sp s ∧ ValidAt len args s) ∧
      (Side base bytes len args sp t ∧ ValidAt len args t)) ∧ s.gpr .ebx = t.gpr .ebx ∧ s.gpr .edx = t.gpr .edx)
      PublicRt.valid fun _ _ => True := by
  unfold PublicRt.valid
  intro s t tr ur sf tf ⟨⟨⟨S₁, V₁⟩, ⟨S₂, V₂⟩⟩, Rb, Rd⟩ E F
  have sz := PublicContext.size_eq (Spec.Rsa.modulusWords len)
  have space := S₁.1.space
  have nw := S₁.1.scratch.nowrap
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (RelCT.taint (A := taint) argumentTaint (fun _ _ h => h) (hc := .block []) (by taint_decide)
        _ _ _ _ _ _ (S₁.pair S₂).agree E1 F1).1
      obtain ⟨Ws, Os, Ks⟩ := wp_result (saveExponent_value S₁.1.scratch (by omega)) E1
      obtain ⟨Wt, Ot, Kt⟩ := wp_result (saveExponent_value S₂.1.scratch (by omega)) F1
      have Os' : Outside base 0 bytes s.mem _ := Os.mono (by omega) (by omega)
      have Ot' : Outside base 0 bytes t.mem _ := Ot.mono (by omega) (by omega)
      have U₁ := S₁.keep Ks (by decide) (by decide) Os'
      have U₂ := S₂.keep Kt (by decide) (by decide) Ot'
      have ns := scratch_bytes Os' (by have := S₁.1.upper; omega) S₁.1.nApart
      have nt := scratch_bytes Ot' (by have := S₁.1.upper; omega) S₁.1.nApart
      have T2 := (sizedNarrow_relCT S₁.2.1.hbytes sp _ _ _ _ _ _ _
        ⟨⟨U₁.1, U₁.2.1, U₁.2.2.1, by rw [ns]; exact V₁, Ws, U₁.2.2.2⟩,
          ⟨U₂.1, U₂.2.1, U₂.2.2.1, by rw [nt]; exact V₂, by rw [Wt, Rb, Rd], U₂.2.2.2⟩⟩ E2 F2).1
      exact ⟨by rw [T1, T2], trivial⟩

theorem checkExponent_trace (sp : BitVec 32) {s t : State} (S₁ : Side base bytes len args sp s)
    (S₂ : Side base bytes len args sp t) (V₁ : ValidAt len args s) (V₂ : ValidAt len args t)
    (same : Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat =
      Spec.Rsa.bytesAt t.mem (byteAddr (args 4)) (args 5).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa PublicRt.checkExponent s tr sf) (F : Exec isa PublicRt.checkExponent t ur tf) : tr = ur := by
  have Branch : RelCT isa (fun s t => (((Side base bytes len args sp s ∧ ValidAt len args s) ∧
      (Side base bytes len args sp t ∧ ValidAt len args t)) ∧ s.gpr .ebx = t.gpr .ebx ∧ s.gpr .edx = t.gpr .edx) ∧
      s.zf = t.zf)
      (.ite .e PublicFn.failure PublicRt.valid) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (fun _ _ h => h.2)
    · exact (publicFailure_relCT base bytes len args).mono (fun _ _ h => h.1.1.1.1.1.pair h.1.1.1.2.1)
        (fun _ _ h => h)
    · exact (valid_relCT sp).mono (fun _ _ h => h.1.1) (fun _ _ h => h)
  have Compare : RelCT isa (fun _ _ => True) (.block [.alu .cmp .eax (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
    rfl
  unfold PublicRt.checkExponent at E F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      have T1 := publicExponent_trace (S₁.pair S₂) same E1 F1
      obtain ⟨Vs, Bs, Ds, Ms, Ks⟩ := wp_result (publicExponent_ok S₁.1) E1
      obtain ⟨Vt, Bt, Dt, Mt, Kt⟩ := wp_result (publicExponent_ok S₂.1) F1
      rw [same] at Vs Bs Ds
      have U₁ := S₁.keep Ks (by decide) (by decide) (by rw [Ms]; exact Outside.refl _ _ _ _)
      have U₂ := S₂.keep Kt (by decide) (by decide) (by rw [Mt]; exact Outside.refl _ _ _ _)
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          have T2 := (Compare _ _ _ _ _ _ trivial E2 F2).1
          obtain ⟨Zs, Mvs, Kvs⟩ := wp_result (exponentFlag_ok _ Vs) E2
          obtain ⟨Zt, Mvt, Kvt⟩ := wp_result (exponentFlag_ok _ Vt) F2
          have W₁ := U₁.keep Kvs (by decide) (by decide) (by rw [Mvs]; exact Outside.refl _ _ _ _)
          have W₂ := U₂.keep Kvt (by decide) (by decide) (by rw [Mvt]; exact Outside.refl _ _ _ _)
          have T3 := (Branch _ _ _ _ _ _ ⟨⟨⟨⟨W₁, by show Spec.Rsa.modulusValid _ _ = true; rw [Mvs, Ms]; exact V₁⟩,
            ⟨W₂, by show Spec.Rsa.modulusValid _ _ = true; rw [Mvt, Mt]; exact V₂⟩⟩,
            by rw [Kvs.1 _ (by decide), Kvt.1 _ (by decide), Bs, Bt],
            by rw [Kvs.1 _ (by decide), Kvt.1 _ (by decide), Ds, Dt]⟩,
            Zs.trans Zt.symm⟩ E3 F3).1
          rw [T1, T2, T3]

theorem body_relCT (sp : BitVec 32) :
    RelCT isa (fun s t => Side base bytes len args sp s ∧ Side base bytes len args sp t ∧
      Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len ∧
      Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat =
        Spec.Rsa.bytesAt t.mem (byteAddr (args 4)) (args 5).toNat)
      PublicRt.body (fun _ _ => True) := by
  let R := fun s t => (Side base bytes len args sp s ∧ Side base bytes len args sp t) ∧
    Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat =
      Spec.Rsa.bytesAt t.mem (byteAddr (args 4)) (args 5).toNat ∧
    ∃ b : Bool, s.zf = some b ∧ t.zf = some b ∧ (b = true → ValidAt len args s ∧ ValidAt len args t)
  have Branch : RelCT isa R (.ite .e PublicRt.checkExponent PublicFn.failure) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (P := R)
    · intro s t ⟨_, _, b, Zs, Zt, _⟩
      exact Zs.trans Zt.symm
    · intro s t tr ur sf tf ⟨H, Z⟩ E F
      obtain ⟨b, Zs, _, Valid⟩ := H.2.2
      have B : b = true := by
        change s.zf = some true at Z
        exact Option.some.inj (Zs.symm.trans Z)
      exact ⟨checkExponent_trace sp H.1.1 H.1.2 (Valid B).1 (Valid B).2 H.2.1 E F, trivial⟩
    · exact (publicFailure_relCT base bytes len args).mono (fun _ _ H => H.1.1.1.pair H.1.1.2) (fun _ _ h => h)
  unfold PublicRt.body
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨S₁, S₂, N, Exp⟩ E F
  cases E with
  | @seq _ _ _ u _ _ _ E1 E2 =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 F2 =>
      have T1 := (publicModulus_relCT base bytes len args _ _ _ _ _ _ (S₁.pair S₂) E1 F1).1
      obtain ⟨Zs, Ms, Ks⟩ := wp_result (publicModulus_ok S₁.1) E1
      obtain ⟨Zt, Mt, Kt⟩ := wp_result (publicModulus_ok S₂.1) F1
      have U₁ := S₁.keep Ks (by decide) (by decide) (by rw [Ms]; exact Outside.refl _ _ _ _)
      have U₂ := S₂.keep Kt (by decide) (by decide) (by rw [Mt]; exact Outside.refl _ _ _ _)
      have Relation : R u v := by
        refine ⟨⟨U₁, U₂⟩, by rw [Ms, Mt]; exact Exp, _, Zs, ?_, ?_⟩
        · rw [N]; exact Zt
        · intro V
          refine ⟨?_, ?_⟩
          · show Spec.Rsa.modulusValid _ _ = true; rw [Ms]; exact V
          · show Spec.Rsa.modulusValid _ _ = true; rw [Mt, ← N]; exact V
      have T2 := (Branch _ _ _ _ _ _ Relation E2 F2).1
      exact ⟨by rw [T1, T2], trivial⟩

end

/-- The arguments' bytes lie apart from the output and the working space. -/
theorem args_apart {s : State} (A : TopABI s) {r : Region}
    (hret : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r) (hargs : Region.Disjoint ⟨argAddr s 0, 40⟩ r) :
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 44⟩ r :=
  VG.X86.Taint.frame_disjoint (n := 40) (by have := A.abi.stackBound; omega) hret hargs

theorem operation_trace {s t : State} (A : TopABI s) (B : TopABI t)
    (args : ∀ i < 10, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (N : Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat)
    (Ex : Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa PublicRt.code s tr sf) (F : Exec isa PublicRt.code t ur tf) : tr = ur := by
  have A0 := args 0 (by decide)
  have A1 := args 1 (by decide)
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A4 := args 4 (by decide)
  have A5 := args 5 (by decide)
  have A8 := args 8 (by decide)
  have A9 := args 9 (by decide)
  have aEq : argAddr t 0 = argAddr s 0 := by simp only [argAddr, SP]
  cases E with
  | @seq _ _ _ u _ _ _ E1 Erest =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 Frest =>
      have T1 := (publicEntry_relCT _ _ _ _ _ _
        ⟨SP, A8, (A.abi.stackArgument (by decide : 8 < 10)).readSrc,
          (B.abi.stackArgument (by decide : 8 < 10)).readSrc⟩ E1 F1).1
      obtain ⟨Is, _, Ks, Os⟩ := wp_result (publicInstalled_ok A.abi) E1
      obtain ⟨It, _, Kt, Ot⟩ := wp_result (publicInstalled_ok B.abi) F1
      have Iv : PublicInputs (argumentPointer s 8) ((arg s 9).toNat * 8) (arg s 3).toNat (arg s) v := by
        have J := It.argsEq (fun i hi => (args i hi).symm)
        simpa only [argumentPointer, ← A8, ← A9, ← A3] using J
      have Ov : VG.Proof.Mont.Outside (argumentPointer s 8) 0 ((arg s 9).toNat * 8) t.mem v.mem := by
        simpa only [argumentPointer, ← A8, ← A9] using Ot
      have espu : u.gpr .esp = s.gpr .esp := Ks.1 _ (by decide)
      have espv : v.gpr .esp = s.gpr .esp := (Kt.1 _ (by decide)).trans SP.symm
      have Su : Side (argumentPointer s 8) ((arg s 9).toNat * 8) (arg s 3).toNat (arg s) (s.gpr .esp) u := by
        refine ⟨Is, ⟨(setWidth_toNat _).symm, rfl, by rw [espu]; exact A.room, by rw [espu]; exact A.abi.stackBound⟩,
          espu, ?_, ?_⟩
        · rw [espu, byteAddr, ← A.abi.outLength]
          exact args_apart A A.abi.retOut A.outArgs.symm
        · rw [espu]; exact args_apart A A.abi.retScratch A.abi.scratchArgs.symm
      have Sv : Side (argumentPointer s 8) ((arg s 9).toNat * 8) (arg s 3).toNat (arg s) (s.gpr .esp) v := by
        refine ⟨Iv, ⟨(setWidth_toNat _).symm, rfl, ?_, by rw [espv]; exact A.abi.stackBound⟩, espv, ?_, ?_⟩
        · rw [espv]
          have R := B.room
          simp only [argumentPointer, ← A8, ← A9, ← SP] at R
          exact R
        · rw [espv, byteAddr, ← A.abi.outLength]
          have D := args_apart B B.abi.retOut B.outArgs.symm
          simp only [argumentPointer, ← A0, ← A1, ← SP] at D
          exact D
        · rw [espv]
          have D := args_apart B B.abi.retScratch B.abi.scratchArgs.symm
          simp only [argumentPointer, ← A8, ← A9, ← SP] at D
          exact D
      have Ns := scratch_bytes Os (by have := A.abi.lengths.2; omega) Is.nApart
      have Nt := scratch_bytes Ov (by have := A.abi.lengths.2; omega) Iv.nApart
      have Es := scratch_bytes Os (by have := (arg s 5).isLt; omega) Is.eApart
      have Et := scratch_bytes Ov (by have := (arg s 5).isLt; omega) Iv.eApart
      have NN : Spec.Rsa.bytesAt u.mem (byteAddr (arg s 2)) (arg s 3).toNat =
          Spec.Rsa.bytesAt v.mem (byteAddr (arg s 2)) (arg s 3).toNat := by
        rw [Ns, Nt]
        simpa only [argumentPointer, byteAddr, ← A2, ← A3] using N
      have EE : Spec.Rsa.bytesAt u.mem (byteAddr (arg s 4)) (arg s 5).toNat =
          Spec.Rsa.bytesAt v.mem (byteAddr (arg s 4)) (arg s 5).toNat := by
        rw [Es, Et]
        simpa only [argumentPointer, byteAddr, ← A4, ← A5] using Ex
      cases Erest with
      | @seq _ _ _ w _ _ _ E2 E3 =>
        cases Frest with
        | @seq _ _ _ z _ _ _ F2 F3 =>
          have T2 := (body_relCT (s.gpr .esp) _ _ _ _ _ _ ⟨Su, Sv, NN, EE⟩ E2 F2).1
          obtain ⟨_, Ksu⟩ := wp_result (body_ok Is Su.2.1) E2
          obtain ⟨_, Ktv⟩ := wp_result (body_ok Iv Sv.2.1) F2
          have Agree : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) w z :=
            agree_regs (by
              intro r hr
              obtain rfl := List.mem_singleton.mp hr
              rw [Ksu.1 _ (by decide), Ktv.1 _ (by decide)]
              exact (Su.pair Sv).agree.rf.1 _ (by decide))
          have T3 := (publicRestore_relCT _ _ _ _ _ _ Agree E3 F3).1
          rw [T1, T2, T3]

theorem publicArgs {s t : State} (H : (Proof.Rsa.publicCheckedContract abi 96).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 10, arg s i = arg t i := by
  sig_pub [Proof.Rsa.publicCheckedContract, Proof.Rsa.publicSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · with_reducible assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem keyBytes {s t : State} (H : (Proof.Rsa.publicCheckedContract abi 96).pub s t) :
    Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat ∧
    Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat :=
  publicKeyBytes H

theorem constantTime : ConstantTime isa (Proof.Rsa.publicCheckedContract abi 96).pre
    (Proof.Rsa.publicCheckedContract abi 96).pub PublicRt.code := by
  intro s t tr ur sf tf S T H E F
  have Args := publicArgs H
  have Key := keyBytes H
  exact operation_trace (topABI_of S) (topABI_of T) Args.2 Args.1 Key.1 Key.2 E F

end VG.Proof.Bignum.X86.PublicRt
