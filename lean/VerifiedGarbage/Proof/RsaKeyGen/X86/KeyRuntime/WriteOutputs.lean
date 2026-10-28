module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePorts
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExport
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEnvironment
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.WriteArray
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextFar
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Zero
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! # The seven masked key outputs and the status, at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key (kOk kStatus outputIndex)
open VG.Proof.RsaKeyGen.X86.Key (Environment ExportProgress OutputInput portResult portFrame_global
  portFrame_other outputIndex_bound outputIndex_zero outputIndex_injective WrittenCore CoreOutcome)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context argsRegion)

/-- What the outputs need beyond `ExportProgress`: the arguments, and outputs apart from them. -/
structure OutputArgs (E : Environment) (sp : BitVec 32) (s : State) : Prop where
  valid : E.Valid
  context : Context E.base E.size sp E.argument s
  apart : ∀ i < 7, (argsRegion sp).Disjoint (E.outputs.region i)

theorem port_ok {E : Environment} {sp : BitVec 32} {m : Mem} {accept : Bool} {i : Nat} {s : State}
    (P : ExportProgress E.outputs m accept i s) (A : OutputArgs E sp s) (hi : i < 7) :
    WP isa (writePort i) s fun t =>
      ExportProgress E.outputs m accept (i + 1) t ∧ OutputArgs E sp t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have h := P.input
  refine WP.mono (writeArray_ok (p := E.outputs.pointer i) (len := E.outputs.length i) A.valid h.ws A.context
    (outputIndex_bound hi) (Ne.symm (outputIndex_zero hi)) (by omega) (by omega) rfl
    (by simp only [VG.Proof.RsaKeyGen.X86.Key.OutputGeometry.length, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl)
    (h.valid.lengthPositive i hi) (h.valid.lengthBound i hi) (h.valid.fit i hi)
    (h.writable i hi) (h.valid.scratchApart i hi) (A.apart i hi) P.zero accept P.mask)
    fun t ⟨ht, Ct, value, F, header, other, K⟩ => ?_
  refine ⟨⟨h.after ht K header, (other aZero (by decide) (outputIndex_zero hi)).trans P.zero,
    (header kOk (by decide)).trans P.mask, ?_, ?_, ?_⟩, ⟨A.valid, Ct, A.apart⟩,
    portFrame_global h hi F, K⟩
  · intro d hd
    exact (header d hd).trans (P.header d hd)
  · intro j lower upper
    exact (other (outputIndex j) (outputIndex_bound upper)
      (outputIndex_injective upper hi (by omega))).trans (P.pending j (by omega) upper)
  · intro j lower upper
    by_cases last : j = i
    · subst j
      unfold portResult
      rw [← P.pending i (Nat.le_refl _) hi]
      exact value
    · exact (portFrame_other h hi upper (by omega) F).trans (P.done j (by omega) upper)

theorem ports_ok {E : Environment} {sp : BitVec 32} {m : Mem} {accept : Bool} {i count : Nat} {s : State}
    (P : ExportProgress E.outputs m accept i s) (A : OutputArgs E sp s) (bound : i + count ≤ 7) :
    WP isa (writePorts i count) s fun t =>
      ExportProgress E.outputs m accept (i + count) t ∧ OutputArgs E sp t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  induction count generalizing i s with
  | zero => exact WP.block_nil ⟨P, A, Frame.refl _ _, Keeps.refl _ _⟩
  | succ count ih =>
    unfold writePorts
    refine WP.seq (WP.mono (port_ok P A (by omega)) fun u ⟨Pu, Au, Fu, Ku⟩ => ?_)
    refine WP.mono (ih Pu Au (by omega)) fun t ⟨Pt, At, Ft, Kt⟩ => ?_
    have index : i + 1 + count = i + (count + 1) := by omega
    rw [index] at Pt
    exact ⟨Pt, At, Fu.trans Ft, Ku.trans Kt⟩

theorem writeOutputs_ok {E : Environment} {sp : BitVec 32} {s : State} (h : OutputInput E.outputs s)
    (A : OutputArgs E sp s) (accept : Bool) (mask : slot s.mem E.base kOk = if accept then 1 else 0) :
    WP isa writeOutputs s fun t =>
      VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ (t.gpr .eax).toNat = slot s.mem E.base kStatus ∧
      (∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (E.outputs.region i).base (E.outputs.region i).len =
        portResult E.outputs s.mem accept i) ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have H := context_workspace A.valid A.context h.ws
  have fits := h.ws.arr_fit (j := aZero) (by decide)
  have fit64 := h.ws.fit64 (j := aZero) (by decide)
  unfold writeOutputs seqs
  refine WP.seq (WP.mono (zero_ok H .modulus (arr aZero) (by change arr E.n aZero + _ ≤ E.size; exact fits))
    fun u ⟨Hu, Ou, zero, Ku⟩ => ?_)
  change Outside E.base (arr E.n aZero) (S E.n) s.mem u.mem at Ou
  change val32 u.mem E.base (arr E.n aZero) (E.n + 2) = 0 at zero
  have clear : Keep E.base E.n [aZero] [] s.mem u.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ou) (by unfold S; omega) (by simp)
  have header : ∀ d, d + 4 ≤ hdr → slot u.mem E.base d = slot s.mem E.base d :=
    fun d hd => clear.slot hd (by simp)
  have Pu : ExportProgress E.outputs s.mem accept 0 u := by
    refine ⟨h.after Hu.old Ku header, ?_, (header kOk (by decide)).trans mask, header, ?_, ?_⟩
    · change val32 u.mem E.base (arr E.n aZero) E.n = 0
      have Z := VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 0) (c := E.n) (by omega)
      simpa only [Nat.mul_zero, Nat.add_zero] using Z
    · intro i _ hi
      exact clear.num (by intro a ha; obtain rfl := List.mem_singleton.mp ha; exact outputIndex_zero hi)
        (by simp) (h.ws.fit64 (outputIndex_bound hi))
    · intro i hi
      omega
  have ownFrame := VG.Proof.Bignum.outside_frame Ou fit64
  have Fu : Frame E.outputs.writes s.mem u.mem := by
    apply ownFrame.sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨E.outputs.scratch, List.mem_cons_self, Offset.sub_base E.base fits⟩
  have Au : OutputArgs E sp u := ⟨A.valid, A.context.keepFar Ku ownFrame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact A.context.separate.sub_right (Offset.sub_base E.base fits)), A.apart⟩
  refine WP.seq (WP.mono (ports_ok Pu Au (by decide : 0 + 7 ≤ 7)) fun v ⟨Pv, _, Fv, Kv⟩ => ?_)
  have head := Pv.input.ws.hdr_le
  refine wp_movS (readSrc_sc Pv.input.ws.workspace (by unfold kStatus hdr at *; omega))
    fun t T _ => WP.block_nil ?_
  refine ⟨Pv.input.ws.rest T.keeps, ?_, ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans (T.keeps.mono (by decide)))⟩
  · rw [T.gpr]
    exact Pv.header kStatus (by decide)
  · intro i hi
    rw [T.mem]
    exact Pv.done i hi hi
  · rw [T.mem]
    exact Fu.trans Fv

theorem writeCore_ok {E : Environment} {sp : BitVec 32} {s : State} {e p q : Nat}
    (h : OutputInput E.outputs s) (A : OutputArgs E sp s) (result : CoreOutcome E.base E.n e p q s.mem) :
    WP isa writeOutputs s fun t =>
      VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ WrittenCore E.outputs e p q t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
  VG.Proof.RsaKeyGen.X86.Key.writeCore_of (g := E.outputs) (fun accept mask => writeOutputs_ok h A accept mask) result

end VG.Proof.RsaKeyGen.X86.KeyRuntime
