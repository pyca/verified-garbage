module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentImport
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.Bignum.X86.PublicDataTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Exponent import exposes only its public pointer and byte count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentImport
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

open VG.Impl.RsaKeyGen.X86.ExponentImport

theorem args_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (header : 20 ≤ size) :
    WP isa (.block args) s fun t =>
      t.gpr .esi = s.mem.readW (off base 12) 32 ∧ t.gpr .ecx = s.mem.readW (off base 16) 32 := by
  unfold args
  refine wp_movS (readSrc_sc S (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 16) (by omega)) fun t T _ => WP.block_nil ?_
  exact ⟨(T.other .esi (by decide)).trans A.gpr, by rw [T.gpr, A.mem]⟩

def InputPair (base : Addr) (size : Nat) (s t : State) : Prop :=
  Scr s base size ∧ Scr t base size ∧ VG.X86.Taint.Agree (roundTaint [.edi]) s t ∧
    s.mem.readW (off base 12) 32 = t.mem.readW (off base 12) 32 ∧
    s.mem.readW (off base 16) 32 = t.mem.readW (off base 16) 32

theorem args_pair {base : Addr} {size : Nat} (header : 20 ≤ size) :
    RelCT isa (InputPair base size) (.block args) (VG.X86.Taint.Agree VG.Proof.Bignum.X86.loadTaint) := by
  have raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block args)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := checkedBlockInvariant rfl rfl
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := raw _ _ _ _ _ _ H.2.2.1 E G
  obtain ⟨sourceU, countU⟩ := wp_result (args_ok H.1 header) E
  obtain ⟨sourceZ, countZ⟩ := wp_result (args_ok H.2.1 header) G
  have regs : ∀ r ∈ ([.edi, .esi, .ecx] : List Reg), u.gpr r = z.gpr r := by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact round_regs agree (by decide)
    · rw [sourceU, sourceZ]; exact H.2.2.2.1
    · rw [countU, countZ]; exact H.2.2.2.2
  have full := round_add_regs (round_forget agree) regs
  exact ⟨trace, taint.le_sound (by decide +kernel) full⟩

theorem code_trace {base : Addr} {size : Nat} (header : 20 ≤ size) :
    RelCT isa (InputPair base size) VG.Impl.RsaKeyGen.X86.ExponentImport.code
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.ExponentImport.code
  refine RelCT.seq (args_pair header) ?_
  apply erased_relCT (VG.Impl.Bignum.X86.loadBE 1 128) (VG.Impl.Bignum.X86.loadBE 1 0)
    (VG.Taint.hintOf taint VG.Proof.Bignum.X86.loadTaint (VG.Impl.Bignum.X86.loadBE 1 0)) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)
  kernel_rfl

end VG.Proof.RsaKeyGen.X86.ExponentImport
