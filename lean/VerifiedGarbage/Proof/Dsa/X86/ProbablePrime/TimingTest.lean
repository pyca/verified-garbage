module

import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Test
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.TimingFront
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateResultTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCoreTiming
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Width
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Sieve
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Parameters
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Load

/-! # The prepared test leaks only the candidate, the tape and public pointers -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86 VG.Impl.Mont.X86

/-- The private frame's input to RSA's prepared test. -/
theorem private_input {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s t : State}
    (L : Loaded E c entropy s) (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits)
    (S : Scr t E.base E.size) (C : Caller E.geometry E.capacity (E.p - 28#32) t)
    (F : Frame [below E.p 28] s.mem t.mem) (K : Keeps [.edx] (allocFrame 28 s) t) :
    CandidatePrepare.Input (E.parameters c entropy) t := by
  have shape := candidate_shape odd length (by have := v.bits.low; omega)
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 28) :=
    (v.stackFar _ List.mem_cons_self).sub_right (below_sub (by decide) v.low)
  have randFar : E.randRegion.Disjoint (below E.p 28) :=
    (v.stackFar _ (List.mem_cons_of_mem _ List.mem_cons_self)).sub_right (below_sub (by decide) v.low)
  have fit : E.base.toNat + E.size ≤ 2 ^ 32 := by rw [v.baseNat]; exact v.workspaceFit
  have W : WorkspaceFrame E.geometry [] s.mem t.mem := workspace_of_frame F fit
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
  have header := v.header
  have big : 2 ^ 63 ≤ 2 ^ (E.bits - 1) := Nat.pow_le_pow_right (by decide) (by have := v.bits.low; omega)
  refine ⟨⟨S, C, ?_, ?_, odd, by change 1 < c; omega, Nat.le_of_lt shape.2.1⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (W.val32 (v.geometry.arrayFit (j := 0) (by decide)) (by intro r mem; cases mem)).trans L.value
  · exact (W.val32 (v.geometry.arrayFit (j := 5) (by decide)) (by intro r mem; cases mem)).trans L.minusOne
  · rw [K.2.1, K.2.2]
    obtain ⟨r, mem, contains⟩ := L.input.memory.randRead
    refine ⟨r, ?_, contains⟩
    change r ∈ s.rd ++ (⟨(s.gpr .esp - 28#32).setWidth 64, 28⟩ :: s.wr)
    exact (List.mem_append.mp mem).elim (List.mem_append_left _)
      (fun known => List.mem_append_right _ (List.mem_cons_of_mem _ known))
  · change Spec.Rsa.bytesAt t.mem (E.rand.setWidth 64) E.randLength = entropy
    rw [VG.Proof.RsaKeyGen.frame_bytesAt F
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact randFar) (by have := v.randLengthFit; omega)]
    exact L.input.memory.entropy
  · exact (W.read32 (d := 28) (by change 28 + 4 ≤ E.size; omega) (by intro r mem; cases mem)).trans L.input.randPtr
  · exact (congrArg BitVec.toNat (W.read32 (d := 32) (by change 32 + 4 ≤ E.size; omega)
      (by intro r mem; cases mem))).trans L.input.randLength
  · exact (congrArg BitVec.toNat (W.read32 (d := 152) (by change 152 + 4 ≤ E.size; omega)
      (by intro r mem; cases mem))).trans L.count

theorem core_pair {E : Environment} {c : Nat} {entropy : List Byte} {s t : State}
    (I : CandidatePrepare.Input (E.parameters c entropy) s) (J : CandidatePrepare.Input (E.parameters c entropy) t) :
    CandidateTest.CorePair (E.parameters c entropy) c entropy s t := by
  refine ⟨?_, I, J, rfl⟩
  apply agree_regs
  intro r mem
  change r ∈ [.esp, .edi] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact I.prepare.caller.sp.trans J.prepare.caller.sp.symm
  · exact BitVec.eq_of_toNat_eq (I.prepare.scratch.edi_toNat.trans J.prepare.scratch.edi_toNat.symm)

theorem capacity_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (space : 44 ≤ size) :
    WP isa (.block [.mov .edx (.mem (sc 40))]) s fun t => Upd s t .edx (s.mem.readW (off base 40) 32) :=
  wp_movS (readSrc_sc S space) fun _ U _ => WP.block_nil U

theorem Loaded.capacityWord {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) : s.mem.readW (off E.base 40) 32 = BitVec.ofNat 32 E.capacity := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.workspaceFit; unfold Environment.size at this; omega)]
  exact L.input.capacity

theorem tested_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (odd : c % 2 = 1)
    (length : Spec.Dsa.bitLength c = E.bits) :
    RelCT isa (LoadedPair E c entropy)
      (VG.Impl.RsaKeyGen.X86.CandidateTest.codeWith (E.bits - 1) (Spec.Dsa.primeChecks E.bits)
        (8 * ((E.bits + 63) / 64)) E.words E.width montName mont roundName round) (fun _ _ => True) := by
  intro s t tr ur u z H A B
  have space := v.header
  have P := v.parameters_valid odd length H.1.input.memory.entropyLength
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block [.mov .edx (.mem (sc 40))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  cases A with
  | seq argsA frameA =>
    cases B with
    | seq argsB frameB =>
      have argsTrace := (raw _ _ _ _ _ _ (H.1.input.agree H.2.input) argsA argsB).1
      have Ua := wp_result (capacity_ok H.1.input.scratch (by omega)) argsA
      have Ub := wp_result (capacity_ok H.2.input.scratch (by omega)) argsB
      obtain ⟨Da, _, _⟩ := H.1.keepStack v (by rw [Ua.mem]; exact Frame.refl _ _) Ua.keeps (by decide) (by decide)
        (by rw [Ua.syms])
      obtain ⟨Db, _, _⟩ := H.2.keepStack v (by rw [Ub.mem]; exact Frame.refl _ _) Ub.keeps (by decide) (by decide)
        (by rw [Ub.syms])
      have capA := Ua.gpr.trans (H.1.capacityWord v)
      have capB := Ub.gpr.trans (H.2.capacityWord v)
      cases frameA with
      | frame pushA bodyA popA =>
        cases frameB with
        | frame pushB bodyB popB =>
          have ea := alloc_some pushA
          have eb := alloc_some pushB
          subst ea eb
          cases bodyA with
          | seq storeA coreA =>
            cases bodyB with
            | seq storeB coreB =>
              have separate (q : State) (D : Loaded E c entropy q) :
                  (q.gpr .esp).toNat ≤ E.geometry.W.toNat ∨ E.geometry.W.toNat + E.geometry.L + 136 ≤ (q.gpr .esp).toNat := by
                rw [D.input.stack]; rcases v.workspaceStack with h | h; exact Or.inl h; exact Or.inr h
              obtain ⟨Sa, Ca, _, Fa, Ka⟩ := wp_result (CandidateFrame.slot_ok (g := E.geometry) (capacity := E.capacity)
                Da.input.scratch (by rw [Da.input.stack]; exact v.low) (separate _ Da) capA) storeA
              obtain ⟨Sb, Cb, _, Fb, Kb⟩ := wp_result (CandidateFrame.slot_ok (g := E.geometry) (capacity := E.capacity)
                Db.input.scratch (by rw [Db.input.stack]; exact v.low) (separate _ Db) capB) storeB
              rw [CandidateFrame.privateSp, Da.input.stack] at Ca
              rw [CandidateFrame.privateSp, Db.input.stack] at Cb
              rw [Da.input.stack] at Fa
              rw [Db.input.stack] at Fb
              have Ia := private_input v Da odd length Sa Ca Fa (Keeps.mono Ka (rs' := [.edx]) (by decide))
              have Ib := private_input v Db odd length Sb Cb Fb (Keeps.mono Kb (rs' := [.edx]) (by decide))
              have coreTrace := (CandidateTest.core_trace montVerified montNoSp montStack roundVerified roundNoSp
                roundStack P v.width_high (other := c) (entropy := entropy) P (Nat.zero_le _)
                _ _ _ _ _ _ (core_pair Ia Ib) coreA coreB).1
              have storeRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.store (at_ .esp 24) .edx])
                  (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
              have storeTrace := (storeRaw _ _ _ _ _ _ (by
                apply agree_regs
                intro r mem
                obtain rfl := List.mem_singleton.mp mem
                rw [allocFrame_esp, allocFrame_esp, Da.input.stack, Db.input.stack]) storeA storeB).1
              refine ⟨?_, trivial⟩
              change _ ++ ([] ++ (_ ++ _) ++ []) = _ ++ ([] ++ (_ ++ _) ++ [])
              rw [argsTrace, storeTrace, coreTrace]

/-- What the finish reads, equal on both sides. -/
structure FinishPair (E : Environment) (s t : State) : Prop where
  left : Scr s E.base E.size
  right : Scr t E.base E.size
  stack : s.gpr .esp = t.gpr .esp
  used : s.mem.readW (off E.base 44) 32 = t.mem.readW (off E.base 44) 32
  status : s.mem.readW (off E.base 168) 32 = t.mem.readW (off E.base 168) 32

def ControlPair (E : Environment) (s t : State) : Prop :=
  FinishPair E s t ∧ s.gpr .eax = t.gpr .eax ∧ isa.eval .e s = isa.eval .e t

theorem FinishPair.keep {E : Environment} {s t u z : State} (P : FinishPair E s t)
    (mu : u.mem = s.mem) (mz : z.mem = t.mem) {rs : List Reg} (Ku : Keeps rs s u) (Kz : Keeps rs t z)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : FinishPair E u z :=
  ⟨P.left.of_keeps Ku edi esp, P.right.of_keeps Kz edi esp,
    by rw [Ku.1 .esp esp, Kz.1 .esp esp]; exact P.stack, by rw [mu, mz]; exact P.used, by rw [mu, mz]; exact P.status⟩

theorem FinishPair.agree {E : Environment} {s t : State} (P : FinishPair E s t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact P.stack
  · exact BitVec.eq_of_toNat_eq (P.left.edi_toNat.trans P.right.edi_toNat.symm)

theorem status_trace {E : Environment} (v : E.Valid) :
    RelCT isa (FinishPair E) (.block Candidate.statusArgs) (ControlPair E) := by
  intro s t tr ur u z P A B
  have space : 172 ≤ E.size := by have := v.header; omega
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block Candidate.statusArgs)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  obtain ⟨valueU, flagU, memU, KU⟩ := wp_result (Candidate.statusArgs_ok P.left space) A
  obtain ⟨valueZ, flagZ, memZ, KZ⟩ := wp_result (Candidate.statusArgs_ok P.right space) B
  exact ⟨(raw _ _ _ _ _ _ P.agree A B).1, P.keep memU memZ KU KZ, valueU.trans (P.status.trans valueZ.symm),
    by rw [flagU, flagZ, P.status]⟩

theorem compare_trace {E : Environment} :
    RelCT isa (ControlPair E) (.block [.alu .cmp .eax (.imm 0)]) (ControlPair E) := by
  intro s t tr ur u z P A B
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .eax])) (.block [.alu .cmp .eax (.imm 0)])
      (VG.X86.Taint.Agree (τr [.esp, .edi, .eax])) := checkedBlockInvariant rfl rfl
  have agree : VG.X86.Taint.Agree (τr [.esp, .edi, .eax]) s t := by
    apply agree_regs
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact P.1.stack
    · exact BitVec.eq_of_toNat_eq (P.1.left.edi_toNat.trans P.1.right.edi_toNat.symm)
    · exact P.2.1
  obtain ⟨U, flagU⟩ := wp_result Candidate.compareZero_ok A
  obtain ⟨Z, flagZ⟩ := wp_result Candidate.compareZero_ok B
  refine ⟨(raw _ _ _ _ _ _ agree A B).1, P.1.keep U.mem Z.mem (U.keeps []) (Z.keeps []), ?_, ?_⟩
  · rw [U.gpr, Z.gpr]; exact P.2.1
  · rw [flagU, flagZ, P.2.1]

theorem finish_trace {E : Environment} (v : E.Valid) :
    RelCT isa (FinishPair E) VG.Impl.Dsa.X86.ProbablePrime.finish (fun _ _ => True) := by
  have pair {s t : State} (P : ControlPair E s t) : CandidateFinish.FinishPair E.base E.size s t :=
    ⟨P.1.left, P.1.right, P.1.used⟩
  have space : 156 ≤ E.size := by have := v.header; omega
  unfold VG.Impl.Dsa.X86.ProbablePrime.finish
  refine RelCT.seq (status_trace v) (VG.RelCT.ite (fun _ _ P => P.2.2) ?_ ?_)
  · exact (CandidateFinish.used_trace space 1).mono (fun _ _ P => pair P.1) (fun _ _ _ => trivial)
  · refine RelCT.seq (compare_trace.mono (fun _ _ P => P.1) (fun _ _ P => P))
      (VG.RelCT.ite (fun _ _ P => P.2.2) ?_ ?_)
    · exact (CandidateFinish.none_trace space).mono (fun _ _ P => pair P.1) (fun _ _ _ => trivial)
    · exact (CandidateFinish.used_trace space 2).mono (fun _ _ P => pair P.1) (fun _ _ _ => trivial)

theorem test_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (odd : c % 2 = 1)
    (length : Spec.Dsa.bitLength c = E.bits) :
    RelCT isa (LoadedPair E c entropy) (VG.Impl.Dsa.X86.ProbablePrime.test E.bits montName mont roundName round)
      (fun _ _ => True) := by
  unfold VG.Impl.Dsa.X86.ProbablePrime.test
  refine RelCT.seq (R := FinishPair E) ?_ (finish_trace v)
  intro s t tr ur u z H A B
  have trace := (tested_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v odd length
    _ _ _ _ _ _ H A B).1
  obtain ⟨Iu, statusU, _, _, _, _⟩ := wp_result
    (tested_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v H.1 odd length) A
  obtain ⟨Iz, statusZ, _, _, _, _⟩ := wp_result
    (tested_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v H.2 odd length) B
  refine ⟨trace, Iu.scratch, Iz.scratch, Iu.stack.trans Iz.stack.symm, Iu.usedPtr.trans Iz.usedPtr.symm, ?_⟩
  exact BitVec.eq_of_toNat_eq (statusU.trans statusZ.symm)

end VG.Proof.Dsa.X86.ProbablePrime
