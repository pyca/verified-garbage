module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateFinish
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Finishing a candidate exposes neither the consumed-count value nor scratch data -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateFinish
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Mont.X86
open VG.Impl.RsaKeyGen.X86.CandidateFinish

def finishArgs (hasCount : Bool) : List Instr :=
  [.mov .edx (.mem (sc 44)), .mov .eax (if hasCount then .mem (sc 152) else .imm 0)]

theorem finishArgs_ok {s : State} {base : Addr} {size : Nat}
    (S : Scr s base size) (header : 156 ≤ size) (hasCount : Bool) :
    WP isa (.block (finishArgs hasCount)) s fun t => t.gpr .edx = s.mem.readW (off base 44) 32 := by
  cases hasCount
  · unfold finishArgs
    refine wp_movS (readSrc_sc S (d := 44) (by omega)) fun a A _ => wp_movS rfl fun t T _ => WP.block_nil ?_
    exact (T.other .edx (by decide)).trans A.gpr
  · unfold finishArgs
    refine wp_movS (readSrc_sc S (d := 44) (by omega)) fun a A _ =>
      wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 152) (by omega)) fun t T _ => WP.block_nil ?_
    exact (T.other .edx (by decide)).trans A.gpr

def FinishPair (base : Addr) (size : Nat) (s t : State) : Prop :=
  Scr s base size ∧ Scr t base size ∧ s.mem.readW (off base 44) 32 = t.mem.readW (off base 44) 32

theorem finishArgs_trace {base : Addr} {size : Nat} (header : 156 ≤ size) (hasCount : Bool) :
    RelCT isa (FinishPair base size) (.block (finishArgs hasCount)) (VG.X86.Taint.Agree (τr [.edx])) := by
  intro s t tr ur u z ⟨S, T, pointer⟩ E G
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.edi])) (.block (finishArgs hasCount))
      (VG.X86.Taint.Agree (τr [.edi])) := by cases hasCount <;> exact checkedBlockInvariant rfl rfl
  have A : VG.X86.Taint.Agree (τr [.edi]) s t := by
    apply agree_regs
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  refine ⟨(raw _ _ _ _ _ _ A E G).1, agree_regs ?_⟩
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  rw [wp_result (finishArgs_ok S header hasCount) E, wp_result (finishArgs_ok T header hasCount) G]
  exact pointer

theorem writeUsed_trace :
    RelCT isa (VG.X86.Taint.Agree (τr [.edx])) (.block writeUsed)
      (VG.X86.Taint.Agree (τr [.edx])) := checkedBlockInvariant rfl rfl

theorem used_trace {base : Addr} {size : Nat} (header : 156 ≤ size) (status : Nat) :
    RelCT isa (FinishPair base size) (used status) (fun _ _ => True) := by
  unfold used
  have last : RelCT isa (VG.X86.Taint.Agree (τr [.edx])) (.block [.mov .eax (.imm (BitVec.ofNat 32 status))])
      (VG.X86.Taint.Agree (τr [.edx])) :=
    erased_relCT _ (.block [.mov .eax (.imm 0)]) (.block []) rfl rfl rfl (by decide +kernel)
  exact (RelCT.seq (finishArgs_trace header true) (RelCT.seq writeUsed_trace last)).mono
    (fun _ _ H => H) (fun _ _ _ => trivial)

theorem none_trace {base : Addr} {size : Nat} (header : 156 ≤ size) :
    RelCT isa (FinishPair base size) VG.Impl.RsaKeyGen.X86.CandidateFinish.none (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateFinish.none
  exact (RelCT.seq (finishArgs_trace header false) writeUsed_trace).mono
    (fun _ _ H => H) (fun _ _ _ => trivial)

end VG.Proof.RsaKeyGen.X86.CandidateFinish
