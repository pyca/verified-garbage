module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClear
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Clearing leaks only the public output address and length -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateClear
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.CandidateClear

theorem args_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (header : 8 ≤ size) :
    WP isa (.block args) s fun t =>
      t.gpr .esi = s.mem.readW (off base 0) 32 ∧ t.gpr .ecx = s.mem.readW (off base 4) 32 := by
  unfold args
  refine wp_movS (readSrc_sc S (d := 0) (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 4) (by omega)) fun b B _ =>
    wp_movS rfl fun t T _ => WP.block_nil ?_
  exact ⟨by rw [T.other .esi (by decide), B.other .esi (by decide), A.gpr],
    by rw [T.other .ecx (by decide), B.gpr, A.mem]⟩

def InputPair (base : Addr) (size : Nat) (s t : State) : Prop :=
  Scr s base size ∧ Scr t base size ∧
    s.mem.readW (off base 0) 32 = t.mem.readW (off base 0) 32 ∧
    s.mem.readW (off base 4) 32 = t.mem.readW (off base 4) 32

theorem args_trace {base : Addr} {size : Nat} (header : 8 ≤ size) :
    RelCT isa (InputPair base size) (.block args) (VG.X86.Taint.Agree (τr [.esi, .ecx])) := by
  intro s t tr ur u z ⟨S, T, outEq, lenEq⟩ E G
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.edi])) (.block args)
      (VG.X86.Taint.Agree (τr [.edi])) := checkedBlockInvariant rfl rfl
  have A : VG.X86.Taint.Agree (τr [.edi]) s t := by
    apply agree_regs
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  have trace := (raw _ _ _ _ _ _ A E G).1
  obtain ⟨outU, lenU⟩ := wp_result (args_ok S header) E
  obtain ⟨outZ, lenZ⟩ := wp_result (args_ok T header) G
  refine ⟨trace, agree_regs ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · rw [outU, outZ]; exact outEq
  · rw [lenU, lenZ]; exact lenEq

theorem code_trace {base : Addr} {size : Nat} (header : 8 ≤ size) :
    RelCT isa (InputPair base size) code (fun _ _ => True) := by
  unfold code
  refine RelCT.seq (args_trace header) ?_
  apply RelCT.taint (A := taint) (τr [.esi, .ecx]) (fun _ _ H => H)
    (hc := VG.Taint.hintOf taint (τr [.esi, .ecx]) (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne))
  rfl

end VG.Proof.RsaKeyGen.X86.CandidateClear
