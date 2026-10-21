module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateLoad
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateImportTiming
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.Mont.X86
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportTiming

/-! # Native candidate loading keeps every random byte private -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateLoad
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Mont.X86 VG.Impl.Bignum.X86.PublicContext

def LoadPair (base : Addr) (size : Nat) (s t : State) : Prop :=
  Scr s base size ∧ Scr t base size ∧ s.gpr .esp = t.gpr .esp ∧
    s.mem.readW (off base 28) 32 = t.mem.readW (off base 28) 32

theorem source_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (header : 32 ≤ size) :
    WP isa (.block [.mov .esi (.mem (sc 28))]) s fun t =>
      t.gpr .esi = s.mem.readW (off base 28) 32 ∧ Keeps [.esi] s t := by
  refine wp_movS (readSrc_sc S (d := 28) (by omega)) fun t T _ => WP.block_nil ⟨T.gpr, T.keeps⟩

theorem source_trace {base : Addr} {size : Nat} (header : 32 ≤ size) :
    RelCT isa (LoadPair base size) (.block [.mov .esi (.mem (sc 28))])
      (VG.X86.Taint.Agree (τr [.esp, .edi, .esi])) := by
  intro s t tr ur u z ⟨S, T, stack, source⟩ E G
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.edi])) (.block [.mov .esi (.mem (sc 28))])
      (VG.X86.Taint.Agree (τr [.edi])) := checkedBlockInvariant rfl rfl
  have A : VG.X86.Taint.Agree (τr [.edi]) s t := by
    apply agree_regs
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  obtain ⟨valueU, Ku⟩ := wp_result (source_ok S header) E
  obtain ⟨valueZ, Kz⟩ := wp_result (source_ok T header) G
  refine ⟨(raw _ _ _ _ _ _ A E G).1, agree_regs ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · rw [Ku.1 .esp (by decide), Kz.1 .esp (by decide)]; exact stack
  · rw [Ku.1 .edi (by decide), Kz.1 .edi (by decide)]
    exact BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  · rw [valueU, valueZ]; exact source

theorem code_trace {base : Addr} {size : Nat} (header : 32 ≤ size) (w : Nat) :
    RelCT isa (LoadPair base size) (VG.Impl.RsaKeyGen.X86.CandidateLoad.code w)
      (VG.X86.Taint.Agree Import.publicState) := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateLoad.code
  refine RelCT.seq (source_trace header) (RelCT.seq (CandidateImport.code_trace w (slot w 0)) ?_)
  exact erased_relCT (.block (VG.Impl.RsaKeyGen.X86.CandidateLoad.count w))
    (.block (VG.Impl.RsaKeyGen.X86.CandidateLoad.count 0)) (.block []) rfl rfl rfl (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.CandidateLoad
