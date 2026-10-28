module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.WriteOutputs
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyExportState
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePortTiming
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OutputPublic
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ReadonlyTrace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Readonly
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.WriteArray
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextFar
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextArgument
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Zero
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.Offset

/-! # The outputs' trace depends only on the arguments and the declared retry bit -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key (kOk kStatus outputIndex)
open VG.Proof.Mont.X86.Dynamic (workspaceTaint)
open VG.Proof.RsaKeyGen.X86.Key (Environment Input ExportState OutputPair outputIndex_bound outputIndex_zero)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context argsRegion)

theorem zero_runs {E : Environment} {sp : BitVec 32} {s : State} (A : OutputArgs E sp s)
    (h : VG.Proof.Rsa.X86.Keys.Ws s E.base E.size E.n 32) :
    WP isa (zero .modulus (arr aZero)) (readonly s E.base E.size) fun _ => True := by
  have fits := h.arr_fit (j := aZero) (by decide)
  exact WP.mono (zero_ok (context_workspace A.valid A.context h).readonly .modulus (arr aZero)
    (by change arr E.n aZero + _ ≤ E.size; exact fits)) fun _ _ => trivial

theorem setup_runs {E : Environment} {sp : BitVec 32} {s : State} {j pointer length : Nat}
    (A : OutputArgs E sp s) (h : VG.Proof.Rsa.X86.Keys.Ws s E.base E.size E.n 32)
    (hj : j < 32) (nonzero : j ≠ aZero) (hp : pointer < 18) (hl : length < 18)
    (bit : slot s.mem E.base kOk ≤ 1) :
    WP isa (arraySetup j pointer length) (readonly s E.base E.size) fun _ => True := by
  have H := (context_workspace A.valid A.context h).readonly
  have C := context_readonly A.context
  have fits := h.arr_fit hj
  have fit64 := h.fit64 hj
  have head := h.hdr_le
  have nowrap := h.workspace.nowrap
  unfold S at fits fit64
  unfold arraySetup
  refine WP.seq (WP.mono (sel_ok H hj (by decide) hj (by decide) bit (Or.inl nonzero))
    fun u ⟨Hu, Ou, _, Ku⟩ => ?_)
  have raw : Outside E.base (arr E.n j) (S E.n) (readonly s E.base E.size).mem u.mem := by
    intro a ha
    apply Ou a
    intro r hr
    change r ∈ [(arr E.n j, S E.n)] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact ha
  have ownFrame := VG.Proof.Bignum.outside_frame raw (by unfold S; exact fit64)
  have Cu := C.keepFar Ku ownFrame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact A.context.separate.sub_right (Offset.sub_base E.base (by unfold S; exact fits)))
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (context_argument Cu (i := pointer) hp).readSrc fun a Aa _ => ?_
  refine wp_movS ((context_argument Cu (i := length) hl).keep Aa.keeps (by decide)
    (by rw [Aa.mem]; exact Outside.refl _ _ _ _)).readSrc fun b Bb _ => ?_
  have Hb := Hu.keep ((Aa.keeps.mono (rs' := [.ebx, .ecx]) (by decide)).trans (Bb.keeps.mono (by decide)))
    (by rw [Bb.mem, Aa.mem]; exact Outside.refl _ _ _ _)
  refine Hb.ptr_ok (arr j) (r := .esi) (t := .edx) (by decide) (by decide)
    (by change arr E.n j < _; omega) fun c _ _ _ => ?_
  exact wp_addS rfl fun d _ _ => wp_subS rfl fun e _ _ => WP.block_nil trivial

/-- One run's state between outputs. -/
structure RtExport (E : Environment) (sp : BitVec 32) (s : State) : Prop where
  state : ExportState E s
  args : OutputArgs E sp s

theorem zeroExport_ok {E : Environment} {sp : BitVec 32} {s : State} (h : Input E s)
    (bit : slot s.mem E.base kOk ≤ 1) (A : OutputArgs E sp s) :
    WP isa (zero .modulus (arr aZero)) s fun t => RtExport E sp t ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have H := context_workspace A.valid A.context h.ws
  have fits := h.ws.arr_fit (j := aZero) (by decide)
  have fit64 := h.ws.fit64 (j := aZero) (by decide)
  refine WP.mono (zero_ok H .modulus (arr aZero) (by change arr E.n aZero + _ ≤ E.size; exact fits))
    fun t ⟨Ht, O, zero, K⟩ => ?_
  change Outside E.base (arr E.n aZero) (S E.n) s.mem t.mem at O
  change val32 t.mem E.base (arr E.n aZero) (E.n + 2) = 0 at zero
  have clear : Keep E.base E.n [aZero] [] s.mem t.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using O) (by unfold S; omega) (by simp)
  have header : ∀ d, d + 4 ≤ hdr → slot t.mem E.base d = slot s.mem E.base d :=
    fun d hd => clear.slot hd (by simp)
  have input : Input E t := h.keep Ht.old K (by
    intro d hd
    apply BitVec.eq_of_toNat_eq
    exact header d (by unfold hdr; omega))
  have lowZero : num t.mem E.base E.n aZero = 0 := by
    have Z := VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 0) (c := E.n) (by omega)
    simpa only [Nat.mul_zero, Nat.add_zero] using Z
  have ownFrame := VG.Proof.Bignum.outside_frame O fit64
  refine ⟨⟨⟨input, lowZero, by rw [header kOk (by decide)]; exact bit⟩,
    ⟨A.valid, A.context.keepFar K ownFrame ?_, A.apart⟩⟩, K⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact A.context.separate.sub_right (Offset.sub_base E.base fits)

theorem RtExport.port_ok {E : Environment} {sp : BitVec 32} {s : State} (h : RtExport E sp s)
    {i : Nat} (hi : i < 7) :
    WP isa (writePort i) s fun t => RtExport E sp t ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let accept := decide (slot s.mem E.base kOk = 1)
  have mask : slot s.mem E.base kOk = if accept then 1 else 0 := by
    unfold accept
    split <;> have := h.state.bit <;> simp_all <;> omega
  have g := h.state.input.outputs
  refine WP.mono (writeArray_ok (p := E.outputs.pointer i) (len := E.outputs.length i) h.args.valid
    h.state.input.ws h.args.context (outputIndex_bound hi) (Ne.symm (outputIndex_zero hi)) (by omega) (by omega)
    rfl
    (by simp only [VG.Proof.RsaKeyGen.X86.Key.OutputGeometry.length, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl)
    (g.valid.lengthPositive i hi) (g.valid.lengthBound i hi) (g.valid.fit i hi)
    (g.writable i hi) (g.valid.scratchApart i hi) (h.args.apart i hi) h.state.zero accept mask)
    fun t ⟨ht, Ct, _, _, header, other, K⟩ => ?_
  have input : Input E t := h.state.input.keep ht K (by
    intro d hd
    apply BitVec.eq_of_toNat_eq
    exact header d (by unfold hdr; omega))
  refine ⟨⟨⟨input, (other aZero (by decide) (outputIndex_zero hi)).trans h.state.zero, ?_⟩,
    ⟨h.args.valid, Ct, h.args.apart⟩⟩, K⟩
  rw [header kOk (by decide)]
  exact h.state.bit

structure RtExportPair (E : Environment) (sp : BitVec 32) (s t : State) : Prop where
  left : RtExport E sp s
  right : RtExport E sp t
  stack : s.gpr .esp = t.gpr .esp
  source : s.gpr .esi = t.gpr .esi

def OutputStart (E : Environment) (sp : BitVec 32) (s t : State) : Prop :=
  OutputPair E s t ∧ OutputArgs E sp s ∧ OutputArgs E sp t

theorem zeroOutputs_trace (E : Environment) (sp : BitVec 32) :
    RelCT isa (OutputStart E sp) (zero .modulus (arr aZero)) (RtExportPair E sp) := by
  intro s t tr ur u v P A C
  obtain ⟨⟨inputs, agree, leftBit, rightBit⟩, leftArgs, rightArgs⟩ := P
  have trace := (readonly_trace zeroOutputs_public
    (context_workspace leftArgs.valid leftArgs.context inputs.left.ws)
    (context_workspace rightArgs.valid rightArgs.context inputs.right.ws) leftArgs.context rightArgs.context
    (zero_runs leftArgs inputs.left.ws) (zero_runs rightArgs inputs.right.ws) A C).1
  obtain ⟨left, KS⟩ := wp_result (zeroExport_ok inputs.left leftBit leftArgs) A
  obtain ⟨right, KT⟩ := wp_result (zeroExport_ok inputs.right rightBit rightArgs) C
  refine ⟨trace, left, right, ?_, ?_⟩
  · rw [KS.1 .esp (by decide), KT.1 .esp (by decide)]
    exact inputs.stack
  · rw [KS.1 .esi (by decide), KT.1 .esi (by decide)]
    exact agree.reg (by rfl : VG.X86.Taint.pub (workspaceTaint true) .esi = true)

theorem setup_checked {i : Nat} (hi : i < 7) :
    FromInputs (arraySetup (outputIndex i) (2 * i) (2 * i + 1)) portTaint := by
  obtain _ | _ | _ | _ | _ | _ | _ | i := i
  · exact setup0_public
  · exact setup1_public
  · exact setup2_public
  · exact setup3_public
  · exact setup4_public
  · exact setup5_public
  · exact setup6_public
  · omega

theorem port_trace (E : Environment) (sp : BitVec 32) {i : Nat} (hi : i < 7) :
    RelCT isa (RtExportPair E sp) (writePort i) (RtExportPair E sp) := by
  intro s t tr ur u v P A C
  obtain ⟨left, KS⟩ := wp_result (P.left.port_ok hi) A
  obtain ⟨right, KT⟩ := wp_result (P.right.port_ok hi) C
  have stack : u.gpr .esp = v.gpr .esp := by
    rw [KS.1 .esp (by decide), KT.1 .esp (by decide)]
    exact P.stack
  unfold writePort writeArray at A C
  cases A with
  | seq A1 A2 =>
  cases C with
  | seq C1 C2 =>
  obtain ⟨setupTrace, regs⟩ := readonly_trace (setup_checked hi)
    (context_workspace P.left.args.valid P.left.args.context P.left.state.input.ws)
    (context_workspace P.right.args.valid P.right.args.context P.right.state.input.ws)
    P.left.args.context P.right.args.context
    (setup_runs (pointer := 2 * i) (length := 2 * i + 1) P.left.args P.left.state.input.ws (outputIndex_bound hi) (Ne.symm (outputIndex_zero hi))
      (by omega) (by omega) P.left.state.bit)
    (setup_runs (pointer := 2 * i) (length := 2 * i + 1) P.right.args P.right.state.input.ws (outputIndex_bound hi) (Ne.symm (outputIndex_zero hi))
      (by omega) (by omega) P.right.state.bit) A1 C1
  have start : VG.X86.Taint.Agree (τr [.edi, .esp, .ebx, .ecx, .esi]) _ _ := agree_regs (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact regs _ rfl)
  obtain ⟨hint, out, checked, lower⟩ := reverse_public
  obtain ⟨copyTrace, copied⟩ := VG.Taint.check_sound checked start A2 C2
  have final := sseTaint.le_sound lower copied
  refine ⟨by rw [setupTrace, copyTrace], left, right, stack, final.reg (by rfl)⟩

theorem ports_trace (E : Environment) (sp : BitVec 32) (i count : Nat) (bound : i + count ≤ 7) :
    RelCT isa (RtExportPair E sp) (writePorts i count) (RtExportPair E sp) := by
  induction count generalizing i with
  | zero => exact RelCT.block_nil (fun _ _ P => P)
  | succ count ih =>
    exact RelCT.seq (port_trace E sp (by omega)) (ih (i + 1) (by omega))

theorem status_trace (E : Environment) (sp : BitVec 32) :
    RelCT isa (RtExportPair E sp) (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc kStatus))])
      (VG.X86.Taint.Agree (workspaceTaint true)) := by
  have checked : VG.Proof.Rsa.X86.Keys.KeyPublic (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc kStatus))]) :=
    ⟨.block [], workspaceTaint true, rfl, rfl⟩
  refine (VG.Proof.RsaKeyGen.X86.Key.key_public_trace checked).mono (fun s t P => ?_) (fun _ _ P => P)
  change VG.X86.Taint.Agree (τr [.edi, .esi]) s t
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact BitVec.eq_of_toNat_eq (P.left.state.input.ws.workspace.edi_toNat.trans
      P.right.state.input.ws.workspace.edi_toNat.symm)
  · exact P.source

theorem writeOutputs_trace (E : Environment) (sp : BitVec 32) :
    RelCT isa (OutputStart E sp) writeOutputs (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold writeOutputs seqs
  exact RelCT.seq (zeroOutputs_trace E sp) (RelCT.seq (ports_trace E sp 0 7 (by decide)) (status_trace E sp))

end VG.Proof.RsaKeyGen.X86.KeyRuntime
