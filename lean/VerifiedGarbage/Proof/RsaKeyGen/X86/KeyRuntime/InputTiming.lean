module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StartPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Readonly
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CoreReadonlyTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadInputsPublic
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadInputs

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ArgumentTaint
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextArgument
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadInputs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ClearInputs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadPrime
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyScratchFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadFrames
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Framework.Offset
/-! # The inputs load in time that depends only on the arguments -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/LoadInputsRuns.lean`, which only this module imported.
section

/-! # The inputs load from any state that can read them: the read-only view of the arithmetic -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa kEv)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

/-- `loadInputs` runs from a state that reads the primes and the exponent, wherever it may write. -/
theorem loadInputs_runs {E : Environment} {p : BitVec 32} {s : State} (valid : E.Valid)
    (H : Ws s E.base E.size E.n 32) (C : Context E.base E.size p E.argument s)
    (primes : ∀ i, i = 2 ∨ i = 3 → InRegions (s.rd ++ s.wr) (E.outputRegion i).base (E.outputRegion i).len)
    (exponent : InRegions (s.rd ++ s.wr) E.exponentRegion.base E.exponentRegion.len) :
    WP isa loadInputs s fun _ => True := by
  have widths := valid.widths
  have small : E.k ≤ E.n := by omega
  have head := H.hdr_le
  unfold loadInputs VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (clearInputs_ok H) fun u ⟨Hu, Ou, _, _, Ku⟩ => ?_)
  have Fu : Frame [E.workspaceRegion] s.mem u.mem :=
    VG.Proof.RsaKeyGen.X86.Key.outs_scratch_frame (by have := H.old.workspace.nowrap; omega) Ou
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact H.old.fits)
  have Cu := C.keep Ku Fu
  have prime {a : State} (Ha : Ws a E.base E.size E.n 32) (Ca : Context E.base E.size p E.argument a)
      (ra : a.rd ++ a.wr = s.rd ++ s.wr) {i out : Nat} (index : i = 2 ∨ i = 3) (ho : out < 32)
      (persistent : 15 ≤ out) :
      WP isa (loadPrime (2 * i) out) a fun t => Ws t E.base E.size E.n 32 ∧
        Frame [E.workspaceRegion] a.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] a t := by
    have hi : i < 7 := by omega
    have len : E.outputLength i = 4 * E.k := by
      unfold Environment.outputLength
      split <;> omega
    have A : VG.Proof.Bignum.X86.CallArgument a E.base E.size (2 * i + 4) (E.out i) := by
      have H := context_argument Ca (i := 2 * i) (by omega)
      rcases index with rfl | rfl <;> exact H
    have readable : InRegions (a.rd ++ a.wr) ((E.out i).setWidth 64) (4 * E.k) := by
      rw [ra]
      have R := primes i index
      change InRegions _ ((E.out i).setWidth 64) (E.outputLength i) at R
      rwa [len] at R
    refine WP.mono (loadPrime_ok Ha widths.2.2.1 widths.2.2.2.1 ho persistent A
      (by rw [← len]; exact valid.outFit i hi) readable
      (by simpa only [Environment.outputRegion, Environment.workspaceRegion, len] using valid.outputScratch i hi))
      fun t ⟨ht, O, _, _, K⟩ => ?_
    exact ⟨ht, VG.Proof.RsaKeyGen.X86.Key.stage_scratch_frame Ha.old
      (by simp only [List.mem_singleton]; rintro j rfl; exact ho)
      (VG.Proof.RsaKeyGen.X86.Key.loadPrime_stage_frame small O), K⟩
  have ru : u.rd ++ u.wr = s.rd ++ s.wr := by rw [Ku.2.1, Ku.2.2]
  refine WP.seq (WP.mono (prime Hu Cu ru (i := 2) (out := aPa) (Or.inl rfl) (by decide) (by decide))
    fun v ⟨Hv, Fv, Kv⟩ => ?_)
  have rv : v.rd ++ v.wr = s.rd ++ s.wr := by rw [Kv.2.1, Kv.2.2, ru]
  have Cv := Cu.keep Kv Fv
  refine WP.seq (WP.mono (prime Hv Cv rv (i := 3) (out := aQa) (Or.inr rfl) (by decide) (by decide))
    fun w ⟨Hw, Fw, Kw⟩ => ?_)
  have rw' : w.rd ++ w.wr = s.rd ++ s.wr := by rw [Kw.2.1, Kw.2.2, rv]
  have Cw := Cv.keep Kw Fw
  refine WP.mono (loadExponent_ok Hw valid.exponentLength.1 valid.exponentLength.2
    (context_argument Cw (i := 14) (by decide)) (context_argument Cw (i := 15) (by decide)) valid.exponentFit
    (by rw [rw']; exact exponent)
    (valid.exponentScratch.sub_right (Offset.sub_base _ (by unfold kEv VG.Impl.Rsa.X86.Keys.hdr at *; omega))))
    fun _ _ => trivial

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (Environment SizedStart ImportedPair InputPair)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

/-- `readonly_agree` before the inputs, whose `esi` may differ. -/
theorem input_agree {s t : State} {B : Addr} {Z : Nat} {p : BitVec 32} {args : Nat → BitVec 32}
    (S : Context B Z p args s) (T : Context B Z p args t) (large : 160 ≤ Z) :
    VG.X86.Taint.Agree inputTaint (readonly s B Z) (readonly t B Z) := by
  have sp : s.gpr .esp = t.gpr .esp := S.sp.trans T.sp.symm
  have fitS : (s.gpr .esp).toNat + 92 ≤ 2 ^ 32 := by rw [S.sp]; exact S.fit
  have fitT : (t.gpr .esp).toNat + 92 ≤ 2 ^ 32 := by rw [T.sp]; exact T.fit
  refine {
    rf := ⟨?_, by intro h; cases h⟩
    wr := fun h => False.elim (h rfl)
    wf₁ := (readonly_wf S large).mono (Or.inl rfl) (fun _ h => h) (fun _ h => ⟨h, rfl⟩)
      (Or.inr ⟨rfl, rfl⟩) (fun _ h => ⟨h, rfl, rfl⟩) (Or.inl ⟨rfl, Nat.le_refl _⟩)
    wf₂ := (readonly_wf T large).mono (Or.inl rfl) (fun _ h => h) (fun _ h => ⟨h, rfl⟩)
      (Or.inr ⟨rfl, rfl⟩) (fun _ h => ⟨h, rfl, rfl⟩) (Or.inl ⟨rfl, Nat.le_refl _⟩)
    ok := VG.X86.Taint.slotsOk_empty
    slots := VG.X86.Taint.slotsAgree_empty
    sp := fun _ => sp
    argMem := ?_ }
  · intro r hr
    simp only [inputTaint, runtimeTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (S.scratch.edi_toNat.trans T.scratch.edi_toNat.symm)
    · exact sp
  · intro k h4 hk
    change k < 76 at hk
    change s.mem (VG.X86.Taint.argByte s (16 + k)) = t.mem (VG.X86.Taint.argByte t (16 + k))
    rw [VG.X86.Taint.argByte_eq fitS (by omega) (by omega),
      VG.X86.Taint.argByte_eq fitT (by omega) (by omega),
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide : 0 < 4)),
      Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide : 0 < 4))]
    have index : (16 + k - 4) / 4 = (k - 4) / 4 + 4 := by omega
    have same := (context_argument S (i := (k - 4) / 4) (by omega)).value.trans
      (context_argument T (i := (k - 4) / 4) (by omega)).value.symm
    change arg s ((k - 4) / 4 + 4) = arg t ((k - 4) / 4 + 4) at same
    rw [index]
    exact congrArg _ same

theorem readonly_inputs {E : Environment} {s : State} (h : VG.Proof.RsaKeyGen.X86.Key.Input E s)
    (H : Ws s E.base E.size E.n 32) {p : BitVec 32} (C : Context E.base E.size p E.argument s) :
    WP isa loadInputs (readonly s E.base E.size) fun _ => True := by
  have widen {b : Addr} {l : Nat} (R : InRegions (s.rd ++ s.wr) b l) :
      InRegions ((readonly s E.base E.size).rd ++ (readonly s E.base E.size).wr) b l := by
    obtain ⟨r, hr, contains⟩ := R
    exact ⟨r, List.mem_append_left _ hr, contains⟩
  refine loadInputs_runs h.valid H.readonly (context_readonly C) ?_ (widen h.exponentRead)
  intro i hi
  obtain ⟨r, hr, contains⟩ := h.outWrite i (by omega)
  exact widen ⟨r, List.mem_append_right _ hr, contains⟩

theorem loaded_core {E : Environment} {m : Mem} {s : State} {e p q : Nat} (L : Loaded E m s)
    (H : Ws s E.base E.size E.n 32) (he : VG.Proof.RsaKeyGen.X86.Key.inputExponent E m = e)
    (hp : VG.Proof.RsaKeyGen.X86.Key.inputPrime E m 2 = p) (hq : VG.Proof.RsaKeyGen.X86.Key.inputPrime E m 3 = q) :
    VG.Proof.RsaKeyGen.X86.Key.CoreStart E.base E.size E.n E.k e p q s :=
  ⟨⟨H.old, L.pBound, L.qBound, L.zero, L.one, L.eValue.trans he, L.loaded.trans (L.eValue.trans he)⟩,
    L.pValue.trans hp, L.qValue.trans hq⟩

theorem runtime_input_trace (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) :
    RelCT isa (RuntimeStart E sp e p q p' q') loadInputs (RuntimeImported E sp e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨u', AS⟩ := trace_readonly_of_wp P.left (readonly_inputs P.start.inputs.left P.left P.leftArgs) A
  obtain ⟨v', CT⟩ := trace_readonly_of_wp P.right (readonly_inputs P.start.inputs.right P.right P.rightArgs) C
  obtain ⟨hint, out, checked, lower⟩ := loadInputs_public
  obtain ⟨trace, agreeOut⟩ := VG.Taint.check_sound checked
    (input_agree P.leftArgs P.rightArgs P.left.hdr_le) AS CT
  have agreeRt := sseTaint.le_sound lower agreeOut
  obtain ⟨sRead, sWrite⟩ := readonly_covers P.left
  obtain ⟨tRead, tWrite⟩ := readonly_covers P.right
  have widenedS := VG.X86.Exec.widen AS sRead sWrite
  have widenedT := VG.X86.Exec.widen CT tRead tWrite
  simp only [readonly, State.withRegions_withRegions, State.withRegions_self] at widenedS widenedT
  have endS := (Exec.det A widenedS).2
  have endT := (Exec.det C widenedT).2
  have publicOut : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint true) u v := by
    change VG.X86.Taint.Agree (τr [.edi, .esi]) u v
    apply agree_regs
    intro r hr
    rw [endS, endT]
    change u'.gpr r = v'.gpr r
    apply agreeRt.reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rfl
  obtain ⟨LS, HS, FS, KS⟩ := wp_result (loadInputs_ok P.start.inputs.left P.left P.leftArgs) A
  obtain ⟨LT, HT, FT, KT⟩ := wp_result (loadInputs_ok P.start.inputs.right P.right P.rightArgs) C
  have stack : u.gpr .esp = v.gpr .esp := by
    rw [KS.1 .esp (by decide), KT.1 .esp (by decide)]
    exact P.start.inputs.stack
  exact ⟨trace, ⟨⟨LS.input, LT.input, stack⟩,
      loaded_core LS HS P.start.leftExponent P.start.leftP P.start.leftQ,
      loaded_core LT HT P.start.rightExponent P.start.rightP P.start.rightQ, publicOut⟩,
    HS, HT, P.leftArgs.keep KS FS, P.rightArgs.keep KT FT⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
