module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StartPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Readonly
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CoreReadonlyTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadInputsPublic
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadInputs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.LoadInputsRuns
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ArgumentTaint
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextArgument
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyLoadInputs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The inputs load in time that depends only on the arguments -/

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
