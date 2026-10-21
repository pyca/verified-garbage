module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentTimingInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentGeneralTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentClass
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Complete exponent filtering branches only on the public exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.ExponentFilter

def TimingPair (workspace p : BitVec 32) (size w c d exponent : Nat) (s t : State) : Prop :=
  TimingInput workspace p size w c exponent s ∧ TimingInput workspace p size w d exponent t

theorem timing_agree {workspace p : BitVec 32} {size w c d exponent : Nat} {s t : State}
    (H : TimingPair workspace p size w c d exponent s t) : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact H.1.stack.trans H.2.stack.symm
  · exact H.1.workspace.trans H.2.workspace.symm

def Classified (P : State → State → Prop) (b : Bool) (s t : State) : Prop :=
  P s t ∧ isa.eval .e s = some b ∧ isa.eval .e t = some b

theorem choice {P : State → State → Prop} {b : Bool} {left right : Prog isa}
    (L : b = true → RelCT isa P left (fun _ _ => True))
    (R : b = false → RelCT isa P right (fun _ _ => True)) :
    RelCT isa (Classified P b) (.ite .e left right) (fun _ _ => True) := by
  refine VG.RelCT.ite (fun _ _ H => H.2.1.trans H.2.2.symm) ?_ ?_
  · intro s t tr ur u z ⟨H, yes⟩ E G
    have hb : b = true := by have same := H.2.1.symm.trans yes; exact Option.some.inj same
    exact L hb _ _ _ _ _ _ H.1 E G
  · intro s t tr ur u z ⟨H, no⟩ E G
    have hb : b = false := by have same := H.2.1.symm.trans no; exact Option.some.inj same
    exact R hb _ _ _ _ _ _ H.1 E G

theorem classify {workspace p : BitVec 32} {size w c d exponent : Nat} {is : List Instr} {b : Bool}
    (raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block is) (VG.X86.Taint.Agree (τr [.esp, .edi])))
    (run : ∀ {candidate : Nat} {s : State}, TimingInput workspace p size w candidate exponent s →
      WP isa (.block is) s fun t => isa.eval .e t = some b ∧ t.mem = s.mem ∧ Keeps [.eax] s t) :
    RelCT isa (TimingPair workspace p size w c d exponent) (.block is)
      (Classified (TimingPair workspace p size w c d exponent) b) := by
  intro s t tr ur u z H E G
  obtain ⟨Zu, Mu, Ku⟩ := wp_result (run H.1) E
  obtain ⟨Zz, Mz, Kz⟩ := wp_result (run H.2) G
  exact ⟨(raw _ _ _ _ _ _ (timing_agree H) E G).1,
    ⟨H.1.keepReadonly Mu Ku, H.2.keepReadonly Mz Kz⟩, Zu, Zz⟩

theorem equal_trace {workspace p : BitVec 32} {size w c d exponent value : Nat} (bound : value < 2 ^ 32) :
    RelCT isa (TimingPair workspace p size w c d exponent) (.block (equal value))
      (Classified (TimingPair workspace p size w c d exponent) (decide (exponent = value))) := by
  refine classify ?_ ?_
  · exact erased_relCT _ (.block (equal 0)) (.block []) rfl rfl rfl (by decide +kernel)
  · intro candidate s S
    refine WP.mono (equal_ok S.input.scratch S.input.header bound) fun t ⟨Z, M, K⟩ => ⟨?_, M, K⟩
    change t.zf = _
    rw [Z, S.input.exponentEq]

theorem parity_trace {workspace p : BitVec 32} {size w c d exponent : Nat} :
    RelCT isa (TimingPair workspace p size w c d exponent) (.block parity)
      (Classified (TimingPair workspace p size w c d exponent) (decide (exponent % 2 = 0))) := by
  refine classify (checkedBlockInvariant rfl rfl) ?_
  intro candidate s S
  refine WP.mono (parity_ok S.input.scratch S.input.header) fun t ⟨Z, M, K⟩ => ⟨?_, M, K⟩
  change t.zf = _
  rw [Z, S.input.exponentEq]

theorem literal_trace {workspace p : BitVec 32} {size w c d exponent : Nat} (value : Nat) :
    RelCT isa (TimingPair workspace p size w c d exponent)
      (.block [.mov .eax (.imm (BitVec.ofNat 32 value))]) (fun _ _ => True) := by
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block [.mov .eax (.imm (BitVec.ofNat 32 value))]) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    erased_relCT _ (.block [.mov .eax (.imm 0)]) (.block []) rfl rfl rfl (by decide +kernel)
  exact raw.mono (fun _ _ H => timing_agree H) (fun _ _ _ => trivial)

theorem fast_pair_trace {workspace p : BitVec 32} {size w c d exponent : Nat} :
    RelCT isa (TimingPair workspace p size w c d exponent) (fast w) (fun _ _ => True) := by
  intro s t tr ur u z H E G
  exact fast_trace_bounded (g := fastGeometry workspace p w)
    (by change 0 < w; have := H.1.input.width; omega) H.1.input.widthBound H.1.fastFit rfl
    _ _ _ _ _ _ ⟨H.1.fastEntry, H.2.fastEntry⟩ E G

theorem general_pair_trace {workspace p : BitVec 32} {size w c d exponent : Nat} (positive : 0 < exponent) :
    RelCT isa (TimingPair workspace p size w c d exponent) (general w) (fun _ _ => True) := by
  intro s t tr ur u z H E G
  exact ⟨(general_trace H.1.modValid (candidate := c - 1) (other := d - 1) rfl rfl rfl positive positive
    _ _ _ _ _ _ ⟨H.1.modInput, H.2.modInput⟩ E G).1, trivial⟩

theorem nontrivial_trace {workspace p : BitVec 32} {size w c d exponent : Nat} (positive : 0 < exponent) :
    RelCT isa (TimingPair workspace p size w c d exponent)
      (.seq (.block (equal 65537)) (.ite .e (fast w) (general w))) (fun _ _ => True) :=
  RelCT.seq (equal_trace (by decide)) (choice (fun _ => fast_pair_trace) (fun _ => general_pair_trace positive))

theorem odd_trace {workspace p : BitVec 32} {size w c d exponent : Nat} (odd : exponent % 2 = 1) :
    RelCT isa (TimingPair workspace p size w c d exponent)
      (.seq (.block (equal 1)) (.ite .e (.block [.mov .eax (.imm 1)])
        (.seq (.block (equal 65537)) (.ite .e (fast w) (general w))))) (fun _ _ => True) :=
  RelCT.seq (equal_trace (by decide)) (choice (fun _ => literal_trace 1) (fun _ => nontrivial_trace (by omega)))

theorem code_trace {workspace p : BitVec 32} {size w c d exponent : Nat} :
    RelCT isa (TimingPair workspace p size w c d exponent) (code w) (fun _ _ => True) := by
  unfold code
  refine RelCT.seq parity_trace (choice (fun _ => literal_trace 0) ?_)
  intro odd
  have notEven : ¬ exponent % 2 = 0 := of_decide_eq_false odd
  exact odd_trace (by omega)

end VG.Proof.RsaKeyGen.X86.ExponentFilter
