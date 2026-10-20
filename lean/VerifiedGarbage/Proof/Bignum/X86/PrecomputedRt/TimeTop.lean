module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.TimeSized
meta import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.TimeSized
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedExponentTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedFailureTiming
public import VerifiedGarbage.Proof.Bignum.X86.PublicEntryTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedArgumentsEq
meta import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.X86.PrecomputedResources
import VerifiedGarbage.Proof.Bignum.WordsFrame

/-! # The trace of precomputed public RSA at a run-time width, from the entry to the return

The exponent's scan and the failure are `PublicFn`'s, related by their own
lemmas (`precomputedExponent_trace`, `precomputedFailure_relCT`,
`publicEntry_relCT`), with `sized` related by `sizedNarrow_relCT` from what
each run keeps (`Side`) and the exponent it saved (`VExp`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrecomputedRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicRt
open VG.Impl.Bignum.X86.PrecomputedRt VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.PublicRt VG.Proof.Dsa.X86

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- What each run keeps from the entry on: its inputs, the room for calls, `esp`, and the arguments apart
from the output and the working space. -/
def Side (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  PrecomputedInputs base bytes len args s ∧ Room base bytes args s ∧ s.gpr .esp = sp ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 44⟩ ⟨byteAddr (args 0), len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 44⟩ ⟨base, bytes⟩

theorem Side.keep {sp : BitVec 32} {s t : State} (S : Side base bytes len args sp s) {regs : List Reg}
    (K : Keeps regs s t) (di : .edi ∉ regs) (sp' : .esp ∉ regs) (O : Outside base 0 bytes s.mem t.mem) :
    Side base bytes len args sp t :=
  ⟨S.1.keep K di sp' O, S.2.1.keep K sp', (K.1 _ sp').trans S.2.2.1, by rw [K.1 _ sp']; exact S.2.2.2.1,
    by rw [K.1 _ sp']; exact S.2.2.2.2⟩

theorem Side.pair {sp : BitVec 32} {s t : State} (S₁ : Side base bytes len args sp s)
    (S₂ : Side base bytes len args sp t) : PrecomputedPair base bytes len args s t :=
  ⟨S₁.1, S₂.1, S₁.2.2.1.trans S₂.2.2.1.symm⟩

/-- The exponent. -/
abbrev expOf (args : Nat → BitVec 32) (s : State) : Nat :=
  Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat)

/-- The exponent is valid, its words in `ebx` and `edx`. -/
def VExp (args : Nat → BitVec 32) (s : State) : Prop :=
  Spec.Rsa.exponentValid (expOf args s) = true ∧ s.gpr .ebx = BitVec.ofNat 32 (expOf args s % 2 ^ 32) ∧
    s.gpr .edx = BitVec.ofNat 32 (VG.Proof.Bignum.exponentHigh (expOf args s))

theorem VExp.bound {s : State} (V : VExp args s) : expOf args s < 2 ^ 33 := by
  have H := V.1
  simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq] at H
  exact H.2

theorem valid_relCT (sp : BitVec 32) :
    RelCT isa (fun s t => (Side base bytes len args sp s ∧ VExp args s) ∧
      (Side base bytes len args sp t ∧ VExp args t) ∧
      preM len args s = preM len args t ∧ preT len args s = preT len args t ∧
      Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat =
        Spec.Rsa.bytesAt t.mem (byteAddr (args 4)) (args 5).toNat) PrecomputedRt.valid
      fun _ _ => True := by
  unfold PrecomputedRt.valid
  intro s t tr ur sf tf ⟨⟨S₁, V₁⟩, ⟨S₂, V₂⟩, eM, eT, same⟩ E F
  have sz := PublicContext.size_eq (Spec.Rsa.modulusWords len)
  have space := S₁.1.space
  have nw' := S₁.1.scratch.nowrap
  have wbe := wb_eq len
  have P₁ := S₁.1.pre
  have P₂ := S₂.1.pre
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (RelCT.taint (A := taint) argumentTaint (fun _ _ h => h) (hc := .block []) (by taint_decide)
        _ _ _ _ _ _ (S₁.pair S₂).agree E1 F1).1
      obtain ⟨Xs, Os, Ks⟩ := wp_result (saveExponent_ok S₁.1.scratch (by omega) V₁.bound V₁.2.1 V₁.2.2) E1
      obtain ⟨Xt, Ot, Kt⟩ := wp_result (saveExponent_ok S₂.1.scratch (by omega) V₂.bound V₂.2.1 V₂.2.2) F1
      have Os' : Outside base 0 bytes s.mem _ := Os.mono (by omega) (by omega)
      have Ot' : Outside base 0 bytes t.mem _ := Ot.mono (by omega) (by omega)
      have U₁ := S₁.keep Ks (by decide) (by decide) Os'
      have U₂ := S₂.keep Kt (by decide) (by decide) Ot'
      have es := scratch_bytes Os' (by have := S₁.1.eBound; have := S₁.1.upper; omega) S₁.1.eApart
      have et := scratch_bytes Ot' (by have := S₁.1.eBound; have := S₁.1.upper; omega) S₁.1.eApart
      have ms := val32_apart (d := 0) (k := nw len) Os (by omega) P₁.apart (by simp only [nw, wb]; omega)
      have mt := val32_apart (d := 0) (k := nw len) Ot (by omega) P₂.apart (by simp only [nw, wb]; omega)
      have ts := val32_apart (d := wb len) (k := nw len) Os (by omega) P₁.apart (by simp only [nw, wb]; omega)
      have tt := val32_apart (d := wb len) (k := nw len) Ot (by omega) P₂.apart (by simp only [nw, wb]; omega)
      have T2 := (sizedNarrow_relCT S₁.2.1.hbytes sp _ _ _ _ _ _
        ⟨⟨U₁.1, U₁.2.1, U₁.2.2.1, ⟨by rw [Xs, es], by rw [es]; exact V₁.1⟩, U₁.2.2.2⟩,
          ⟨U₂.1, U₂.2.1, U₂.2.2.1, ⟨by rw [Xt, et], by rw [et]; exact V₂.1⟩, U₂.2.2.2⟩,
          by simp only [preM]; rw [ms, mt]; exact eM, by simp only [preT]; rw [ts, tt]; exact eT,
          by rw [Xs, Xt]; simp only [expOf]; rw [same]⟩ E2 F2).1
      exact ⟨by rw [T1, T2], trivial⟩

theorem body_relCT (sp : BitVec 32) :
    RelCT isa (fun s t => Side base bytes len args sp s ∧ Side base bytes len args sp t ∧
      preM len args s = preM len args t ∧ preT len args s = preT len args t ∧
      Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat =
        Spec.Rsa.bytesAt t.mem (byteAddr (args 4)) (args 5).toNat)
      PrecomputedRt.body (fun _ _ => True) := by
  let R := fun s t => (Side base bytes len args sp s ∧ Side base bytes len args sp t) ∧
    (preM len args s = preM len args t ∧ preT len args s = preT len args t ∧
      Spec.Rsa.bytesAt s.mem (byteAddr (args 4)) (args 5).toNat =
        Spec.Rsa.bytesAt t.mem (byteAddr (args 4)) (args 5).toNat) ∧
    ∃ b : Bool, s.zf = some b ∧ t.zf = some b ∧ (b = false → VExp args s ∧ VExp args t)
  have Branch : RelCT isa R (.ite .e PublicFn.failure PrecomputedRt.valid) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (P := R)
    · intro s t ⟨_, _, b, Zs, Zt, _⟩
      exact Zs.trans Zt.symm
    · exact (precomputedFailure_relCT base bytes len args).mono (fun _ _ H => H.1.1.1.pair H.1.1.2)
        (fun _ _ h => h)
    · intro s t tr ur sf tf ⟨H, Z⟩ E F
      obtain ⟨b, Zs, _, Valid⟩ := H.2.2
      have B : b = false := by
        change s.zf = some false at Z
        exact Option.some.inj (Zs.symm.trans Z)
      exact valid_relCT sp _ _ _ _ _ _ ⟨⟨H.1.1, (Valid B).1⟩, ⟨H.1.2, (Valid B).2⟩, H.2.1.1, H.2.1.2.1,
        H.2.1.2.2⟩ E F
  have Compare : RelCT isa (fun _ _ => True) (.block [.alu .cmp .eax (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
    rfl
  intro s t tr ur sf tf ⟨S₁, S₂, eM, eT, same⟩ E F
  unfold PrecomputedRt.body at E F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      have T1 := precomputedExponent_trace (S₁.pair S₂) same E1 F1
      obtain ⟨Vs, Ls, Hs, Ms, Ks⟩ := wp_result (precomputedExponentScan_ok S₁.1) E1
      obtain ⟨Vt, Lt, Ht, Mt, Kt⟩ := wp_result (precomputedExponentScan_ok S₂.1) F1
      have U₁ := S₁.keep Ks (by decide) (by decide) (by rw [Ms]; exact Outside.refl _ _ _ _)
      have U₂ := S₂.keep Kt (by decide) (by decide) (by rw [Mt]; exact Outside.refl _ _ _ _)
      cases Erest with
      | @seq _ _ _ w _ _ _ E2 E3 =>
        cases Frest with
        | @seq _ _ _ z _ _ _ F2 F3 =>
          have T2 := (Compare _ _ _ _ _ _ trivial E2 F2).1
          obtain ⟨Zs, Mvs, Kvs⟩ := wp_result (exponentFlag_ok _ Vs) E2
          obtain ⟨Zt, Mvt, Kvt⟩ := wp_result (exponentFlag_ok _ Vt) F2
          have W₁ := U₁.keep Kvs (by decide) (by decide) (by rw [Mvs]; exact Outside.refl _ _ _ _)
          have W₂ := U₂.keep Kvt (by decide) (by decide) (by rw [Mvt]; exact Outside.refl _ _ _ _)
          have ms : w.mem = s.mem := Mvs.trans Ms
          have mt : z.mem = t.mem := Mvt.trans Mt
          have Rel : R w z := by
            refine ⟨⟨W₁, W₂⟩, ⟨by simp only [preM]; rw [ms, mt]; exact eM,
              by simp only [preT]; rw [ms, mt]; exact eT, by rw [ms, mt]; exact same⟩, _, Zs, by rw [Zt, same], fun hb => ⟨?_, ?_⟩⟩
            · refine ⟨?_, ?_, ?_⟩
              · simp only [expOf, ms]; simpa using hb
              · simp only [expOf, ms]; rw [Kvs.1 _ (by decide)]; exact Ls
              · simp only [expOf, ms]; rw [Kvs.1 _ (by decide)]; exact Hs
            · refine ⟨?_, ?_, ?_⟩
              · simp only [expOf, mt, ← same]; simpa using hb
              · simp only [expOf, mt]; rw [Kvt.1 _ (by decide)]; exact Lt
              · simp only [expOf, mt]; rw [Kvt.1 _ (by decide)]; exact Ht
          have T3 := (Branch _ _ _ _ _ _ Rel E3 F3).1
          exact ⟨by rw [T1, T2, T3], trivial⟩

end

/-- The arguments' bytes lie apart from the output and the working space. -/
theorem args_apart {s : State} (A : TopABI s) {r : Region}
    (hret : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r) (hargs : Region.Disjoint ⟨argAddr s 0, 40⟩ r) :
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 44⟩ r :=
  VG.X86.Taint.frame_disjoint (n := 40) (by have := A.abi.stackBound; omega) hret hargs

theorem operation_trace {s t : State} (A : TopABI s) (B : TopABI t)
    (args : ∀ i < 10, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (N : Spec.Rsa.wordsAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.wordsAt t.mem (argumentPointer t 2) (arg t 3).toNat)
    (Ex : Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa PrecomputedRt.code s tr sf) (F : Exec isa PrecomputedRt.code t ur tf) : tr = ur := by
  have A0 := args 0 (by decide)
  have A1 := args 1 (by decide)
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A4 := args 4 (by decide)
  have A5 := args 5 (by decide)
  have A8 := args 8 (by decide)
  have A9 := args 9 (by decide)
  cases E with
  | @seq _ _ _ u _ _ _ E1 Erest =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 Frest =>
      have T1 := (publicEntry_relCT _ _ _ _ _ _
        ⟨SP, A8, (A.abi.stackArgument (by decide : 8 < 10)).readSrc,
          (B.abi.stackArgument (by decide : 8 < 10)).readSrc⟩ E1 F1).1
      obtain ⟨Is, _, Ks, Os⟩ := wp_result (precomputedInstalled_ok A.abi) E1
      obtain ⟨It, _, Kt, Ot⟩ := wp_result (precomputedInstalled_ok B.abi) F1
      have Iv : PrecomputedInputs (argumentPointer s 8) ((arg s 9).toNat * 8) (arg s 1).toNat (arg s) v := by
        have J := It.argsEq (fun i hi => (args i hi).symm)
        simpa only [argumentPointer, ← A8, ← A9, ← A1] using J
      have Ov : VG.Proof.Mont.Outside (argumentPointer s 8) 0 ((arg s 9).toNat * 8) t.mem v.mem := by
        simpa only [argumentPointer, ← A8, ← A9] using Ot
      have espu : u.gpr .esp = s.gpr .esp := Ks.1 _ (by decide)
      have espv : v.gpr .esp = s.gpr .esp := (Kt.1 _ (by decide)).trans SP.symm
      have Su : Side (argumentPointer s 8) ((arg s 9).toNat * 8) (arg s 1).toNat (arg s) (s.gpr .esp) u := by
        refine ⟨Is, ⟨(setWidth_toNat _).symm, rfl, by rw [espu]; exact A.room, by rw [espu]; exact A.abi.stackBound⟩,
          espu, ?_, ?_⟩
        · rw [espu]; exact args_apart A A.abi.retOut A.outArgs.symm
        · rw [espu]; exact args_apart A A.abi.retScratch A.abi.scratchArgs.symm
      have Sv : Side (argumentPointer s 8) ((arg s 9).toNat * 8) (arg s 1).toNat (arg s) (s.gpr .esp) v := by
        refine ⟨Iv, ⟨(setWidth_toNat _).symm, rfl, ?_, by rw [espv]; exact A.abi.stackBound⟩, espv, ?_, ?_⟩
        · rw [espv]
          have R := B.room
          simp only [argumentPointer, ← A8, ← A9, ← SP] at R
          exact R
        · rw [espv]
          have D := args_apart B B.abi.retOut B.outArgs.symm
          simp only [argumentPointer, ← A0, ← A1, ← SP] at D
          exact D
        · rw [espv]
          have D := args_apart B B.abi.retScratch B.abi.scratchArgs.symm
          simp only [argumentPointer, ← A8, ← A9, ← SP] at D
          exact D
      have Ns := scratch_words Os (by have := A.abi.scratchBound; omega)
        (n := 2 * Spec.Rsa.modulusWords (arg s 1).toNat) (by have := Is.rt.dimensions; omega)
        (by simpa only [show 8 * (2 * Spec.Rsa.modulusWords (arg s 1).toNat) =
          16 * Spec.Rsa.modulusWords (arg s 1).toNat by omega] using Is.preApart)
      have Nt := scratch_words Ov (by have := A.abi.scratchBound; omega)
        (n := 2 * Spec.Rsa.modulusWords (arg s 1).toNat) (by have := Iv.rt.dimensions; omega)
        (by simpa only [show 8 * (2 * Spec.Rsa.modulusWords (arg s 1).toNat) =
          16 * Spec.Rsa.modulusWords (arg s 1).toNat by omega] using Iv.preApart)
      have Es := scratch_bytes Os (by have := (arg s 5).isLt; omega) Is.eApart
      have Et := scratch_bytes Ov (by have := (arg s 5).isLt; omega) Iv.eApart
      have NN : Spec.Rsa.wordsAt u.mem (byteAddr (arg s 2)) (2 * Spec.Rsa.modulusWords (arg s 1).toNat) =
          Spec.Rsa.wordsAt v.mem (byteAddr (arg s 2)) (2 * Spec.Rsa.modulusWords (arg s 1).toNat) := by
        rw [Ns, Nt]
        simpa only [argumentPointer, byteAddr, ← A2, ← A3, A.abi.preLength, Spec.Rsa.precomputedWords] using N
      have EE : Spec.Rsa.bytesAt u.mem (byteAddr (arg s 4)) (arg s 5).toNat =
          Spec.Rsa.bytesAt v.mem (byteAddr (arg s 4)) (arg s 5).toNat := by
        rw [Es, Et]
        simpa only [argumentPointer, byteAddr, ← A4, ← A5] using Ex
      have PM : preM (arg s 1).toNat (arg s) u = preM (arg s 1).toNat (arg s) v := by
        simp only [preM, nw]
        rw [val32_eq_wv, val32_eq_wv]
        simpa only [Nat.mul_zero] using
          VG.Proof.Bignum.wv_of_wordsAt NN (c := 0) (w := Spec.Rsa.modulusWords (arg s 1).toNat) (by omega)
      have PT : preT (arg s 1).toNat (arg s) u = preT (arg s 1).toNat (arg s) v := by
        simp only [preT, nw, wb]
        rw [val32_eq_wv, val32_eq_wv]
        exact VG.Proof.Bignum.wv_of_wordsAt NN (by omega)
      cases Erest with
      | @seq _ _ _ w _ _ _ E2 E3 =>
        cases Frest with
        | @seq _ _ _ z _ _ _ F2 F3 =>
          have T2 := (body_relCT (s.gpr .esp) _ _ _ _ _ _ ⟨Su, Sv, PM, PT, EE⟩ E2 F2).1
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

theorem publicArgs {s t : State} (H : (Spec.Rsa.publicPrecomputedCheckedContract abi 40).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 10, arg s i = arg t i := by
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal,
    argBytes] at H
  sig_split H
  constructor
  · with_reducible assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem keyLeak {s t : State} (H : (Spec.Rsa.publicPrecomputedCheckedContract abi 40).pub s t) :
    (Spec.Rsa.wordsAt s.mem (argumentPointer s 2) (arg s 3).toNat).map (·.toNat) ++
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat).map (·.toNat) =
    (Spec.Rsa.wordsAt t.mem (argumentPointer t 2) (arg t 3).toNat).map (·.toNat) ++
      (Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat).map (·.toNat) := by
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal,
    argBytes] at H
  exact H.2.1

theorem keyBytes {s t : State} (H : (Spec.Rsa.publicPrecomputedCheckedContract abi 40).pub s t) :
    Spec.Rsa.wordsAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.wordsAt t.mem (argumentPointer t 2) (arg t 3).toNat ∧
    Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat := by
  have Leak := keyLeak H
  have Length : ((Spec.Rsa.bytesAt s.mem (argumentPointer s 4) (arg s 5).toNat).map (·.toNat)).length =
      ((Spec.Rsa.bytesAt t.mem (argumentPointer t 4) (arg t 5).toNat).map (·.toNat)).length := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
    exact congrArg (fun x : BitVec 32 => x.toNat) ((publicArgs H).2 5 (by decide))
  have Both := List.append_inj' Leak Length
  exact ⟨(List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp Both.1,
    (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp Both.2⟩

theorem constantTime : ConstantTime isa (Spec.Rsa.publicPrecomputedCheckedContract abi 40).pre
    (Spec.Rsa.publicPrecomputedCheckedContract abi 40).pub PrecomputedRt.code := by
  intro s t tr ur sf tf S T H E F
  have Args := publicArgs H
  have Key := keyBytes H
  exact operation_trace (topABI_of S) (topABI_of T) Args.2 Args.1 Key.1 Key.2 E F

end VG.Proof.Bignum.X86.PrecomputedRt
