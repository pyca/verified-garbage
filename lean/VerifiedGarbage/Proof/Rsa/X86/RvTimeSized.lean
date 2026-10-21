module

public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase
public import VerifiedGarbage.Proof.Rsa.X86.RvResult
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Rsa.X86.RvTimeCheck
import VerifiedGarbage.Proof.Rsa.X86.RvTimeFusedDispatch
import VerifiedGarbage.Proof.Rsa.X86.RvSized
import VerifiedGarbage.Proof.Rsa.X86.RvFailureTiming
import VerifiedGarbage.Proof.Rsa.X86.RvPublicFacts
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeBase
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.TCB.Mem

/-! # Both branches after the modulus check leak only the declared attempt count

The pieces' taint checks take the arguments public, which needs every
writable region apart from them: runs from states whose writable regions are
narrowed to the working space and the outputs (`narrowG`) leak the same
traces (`sized_relCT`), and so do the runs from the states themselves
(`sizedNarrow_relCT`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (relCT_narrow)
open VG.Spec.Rsa (recoverPrimes)

/-- What the body writes but the stack: the working space and the outputs. -/
def narrowW (g : CallGeometry) : List Region := [⟨g.B, g.Z⟩, g.buffer 0, g.buffer 2]

/-- The geometry with its writable regions narrowed to `narrowW`. -/
def narrowG (g : CallGeometry) : CallGeometry := ⟨{ g.toGeo with wr := narrowW g }⟩

theorem inputs_agree {g : CallGeometry} {s t : State} (pg : PubG g.toGeo) (h : Inputs g s) (j : Inputs g t) :
    VG.X86.Taint.Agree τA s t := by
  have a₁ : ArgsOk s := by unfold ArgsOk; rw [h.esp, h.wrEq]; exact pg
  have a₂ : ArgsOk t := by unfold ArgsOk; rw [j.esp, j.wrEq]; exact pg
  have f₁ := a₁.1
  have f₂ := a₂.1
  have sp : s.gpr .esp = t.gpr .esp := h.esp.trans j.esp.symm
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τA_wf a₁, τA_wf a₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τA, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h.ws.workspace.edi_toNat.trans j.ws.workspace.edi_toNat.symm)
    · exact sp
  · simp only [τA] at hk
    have C₁ := h.arguments ((k - 4) / 4) (by omega)
    have C₂ := j.arguments ((k - 4) / 4) (by omega)
    rw [show VG.X86.Taint.depth τA.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (show arg s _ = arg t _ from C₁.value.trans C₂.value.symm)

/-- Two runs of `sized` over the same geometry, its writable regions apart from the arguments. -/
def SizedPair (g : CallGeometry) (s t : State) : Prop :=
  Inputs g s ∧ Inputs g t ∧ PubG g.toGeo ∧ inputValue g s.mem 0 = inputValue g t.mem 0 ∧
  Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true ∧
  Spec.Rsa.modulusValid (inputValue g t.mem 0) (inputBytes g t.mem 0).length = true ∧
  (calculated g s.mem).2 = (calculated g t.mem).2

theorem sized_relCT (g : CallGeometry) (len : Lengths g) :
    RelCT isa (SizedPair g) VG.Impl.Rsa.X86.RecoverRt.sized (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨hs, ht, pg, modulus, vs, vt, attempts⟩ es et
  have tries : (recoverPrimes (inputValue g s.mem 0) (inputValue g s.mem 1) (inputValue g s.mem 2)).2 =
      (recoverPrimes (inputValue g t.mem 0) (inputValue g t.mem 1) (inputValue g t.mem 2)).2 := by
    rw [← calculated_tries_valid vs, ← calculated_tries_valid vt]
    exact attempts
  have sameGo : decide (GoOn (product g s.mem)) = decide (GoOn (product g t.mem)) := by
    have ls := recover_tries_positive (inputValue g s.mem 0) (inputValue g s.mem 1) (inputValue g s.mem 2)
    have lt := recover_tries_positive (inputValue g t.mem 0) (inputValue g t.mem 1) (inputValue g t.mem 2)
    rw [tries] at ls
    apply decide_eq_decide.mpr
    exact ls.symm.trans lt
  obtain ⟨bs, os, gs⟩ := hs.modulusFacts vs
  obtain ⟨bt, ot, gt⟩ := ht.modulusFacts vt
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      have eq1 := (VG.RelCT.taint (A := taint) τA (fun _ _ h => h) numbersCheck _ _ _ _ _ _
        (inputs_agree pg hs ht) e1 f1).1
      obtain ⟨cs, zs⟩ := wp_result (numbers_ok hs len) e1
      obtain ⟨ct, zt⟩ := wp_result (numbers_ok ht len) f1
      have flag : isa.eval .e u = isa.eval .e v := by change u.zf = v.zf; rw [zs, zt, sameGo]
      cases er with
      | iteT condS es =>
        cases fr with
        | iteT condT et =>
          have goS : GoOn (product g s.mem) := of_decide_eq_true (Option.some.inj (zs.symm.trans condS))
          have goT : GoOn (product g t.mem) := of_decide_eq_true (Option.some.inj (zt.symm.trans condT))
          have eq2 := (selectedRest_relCT g pg s t hs ht goS goT bs bt os ot gs gt
            modulus tries _ _ _ _ _ _ ⟨cs, ct⟩ es et).1
          exact ⟨by rw [eq1, eq2], trivial⟩
        | iteF condT _ => rw [flag, condT] at condS; cases condS
      | iteF condS es =>
        cases fr with
        | iteT condT _ => rw [flag, condT] at condS; cases condS
        | iteF _ et =>
          have next : Pair g u v := ⟨hs.of_KS cs, ht.of_KS ct,
            (cs.rest.1 _ (by decide)).trans ((hs.esp.trans ht.esp.symm).trans (ct.rest.1 _ (by decide)).symm)⟩
          have eq2 := (failure_relCT g _ _ _ _ _ _ next es et).1
          exact ⟨by rw [eq1, eq2], trivial⟩

theorem narrow_inputs {g : CallGeometry} {s : State} (h : Inputs g s) :
    Inputs (narrowG g) (s.withRegions (s.rd ++ s.wr) (narrowW g)) := by
  refine ⟨⟨⟨h.ws.workspace.edi, by simp [State.withRegions, narrowW, narrowG], h.ws.workspace.nowrap,
      h.ws.workspace.stk⟩, h.ws.fits, h.ws.wpos, h.ws.wle⟩, h.lower, h.upper, h.esp, h.room, h.top,
    fun i hi => ⟨⟨?_, (h.arguments i hi).stack.apart⟩, (h.arguments i hi).value⟩, h.stackApart, h.inputPositive,
    h.inputBound, h.inputFit, fun j => ?_, h.inputApart, h.outputPositive, h.outputBound, h.outputFit,
    fun j => ?_, h.outputScratch, h.outputSeparate, rfl⟩
  · obtain ⟨r, hr, hc⟩ := (h.arguments i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.inputRead j
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · refine ⟨g.buffer (2 * j.val), ?_, Region.contains_self _ _⟩
    show _ ∈ narrowW g
    match j with
    | ⟨0, _⟩ => simp [narrowW]
    | ⟨1, _⟩ => simp [narrowW]

/-- Two runs of `sized` from the states themselves: the arguments apart from the working space and the
outputs. -/
def SizedAt (g : CallGeometry) (s t : State) : Prop :=
  Inputs g s ∧ Inputs g t ∧ (∀ r ∈ narrowW g, Region.Disjoint ⟨g.sp.setWidth 64, 52⟩ r) ∧
  inputValue g s.mem 0 = inputValue g t.mem 0 ∧
  Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true ∧
  Spec.Rsa.modulusValid (inputValue g t.mem 0) (inputBytes g t.mem 0).length = true ∧
  (calculated g s.mem).2 = (calculated g t.mem).2

theorem sizedNarrow_relCT (g : CallGeometry) (len : Lengths g) :
    RelCT isa (SizedAt g) VG.Impl.Rsa.X86.RecoverRt.sized (fun _ _ => True) := by
  have len' : Lengths (narrowG g) :=
    ⟨len.lower, len.upper, len.width, len.scratch, len.bytes, len.pLen, len.qLen⟩
  refine relCT_narrow (Pn := SizedPair (narrowG g)) (fun s => s.rd ++ s.wr)
    (fun _ => narrowW g) (fun s₁ s₂ ⟨h₁, h₂, apart, modulus, v₁, v₂, attempts⟩ => ?_)
    (sized_relCT (narrowG g) len')
  have cov : ∀ {s : State}, Inputs g s → Covers (narrowW g) s.wr := by
    intro s h
    refine Covers.cons (Covers.of_mem fun r hr => ?_) (Covers.cons (Covers.one (h.outputWrite 0))
      (Covers.cons (Covers.one (h.outputWrite 1)) Covers.nil))
    rw [List.mem_singleton.mp hr]
    exact h.ws.workspace.wr
  have pLen : (g.buffer 0).len = (g.args 5).toNat := congrArg BitVec.toNat len.pLen
  have qLen : (g.buffer 2).len = (g.args 5).toNat := congrArg BitVec.toNat len.qLen
  have wp : ∀ {s : State}, Inputs g s →
      Spec.Rsa.modulusValid (inputValue g s.mem 0) (inputBytes g s.mem 0).length = true →
      ∃ F, WP isa VG.Impl.Rsa.X86.RecoverRt.sized (s.withRegions (s.rd ++ s.wr) (narrowW g)) F :=
    fun h v => ⟨_, sized_ok (narrow_inputs h) len' v
      (by simp only [inputBytes, VG.Proof.Bignum.bytesAt_length, CallGeometry.buffer] at pLen ⊢; exact pLen)
      (by simp only [inputBytes, VG.Proof.Bignum.bytesAt_length, CallGeometry.buffer] at qLen ⊢; exact qLen)⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov h₁)), cov h₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov h₂)), cov h₂, wp h₁ v₁, wp h₂ v₂,
    narrow_inputs h₁, narrow_inputs h₂, ⟨h₁.top, apart⟩, modulus, v₁, v₂, attempts⟩

end VG.Proof.Rsa.X86.Recover
