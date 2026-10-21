module

public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Publishing a public source pointer copied into the candidate header -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HeaderSource
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Mont.X86

structure Pair (base : Addr) (size offset : Nat) (s t : State) : Prop where
  left : Scr s base size
  right : Scr t base size
  stack : s.gpr .esp = t.gpr .esp
  pointer : s.mem.readW (off base offset) 32 = t.mem.readW (off base offset) 32

theorem Pair.agree {base : Addr} {size offset : Nat} {s t : State} (P : Pair base size offset s t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact P.stack
  · exact BitVec.eq_of_toNat_eq (P.left.edi_toNat.trans P.right.edi_toNat.symm)

theorem source_ok {base : Addr} {size offset : Nat} {s : State}
    (S : Scr s base size) (header : offset + 4 ≤ size) :
    WP isa (.block [.mov .esi (.mem (sc offset))]) s fun t =>
      t.gpr .esi = s.mem.readW (off base offset) 32 ∧ Keeps [.esi] s t := by
  refine wp_movS (readSrc_sc S header) fun t T _ => WP.block_nil ⟨T.gpr, T.keeps⟩

theorem source_trace {base : Addr} {size offset : Nat} (header : offset + 4 ≤ size) :
    RelCT isa (Pair base size offset) (.block [.mov .esi (.mem (sc offset))])
      (VG.X86.Taint.Agree (τr [.esp, .edi, .esi])) := by
  intro s t tr ur u z P E G
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block [.mov .esi (.mem (sc offset))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    erased_relCT _ (.block [.mov .esi (.mem (sc 0))]) (.block []) rfl rfl rfl (by decide +kernel)
  obtain ⟨valueU, Ku⟩ := wp_result (source_ok P.left header) E
  obtain ⟨valueZ, Kz⟩ := wp_result (source_ok P.right header) G
  refine ⟨(raw _ _ _ _ _ _ P.agree E G).1, agree_regs ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · rw [Ku.1 .esp (by decide), Kz.1 .esp (by decide)]; exact P.stack
  · rw [Ku.1 .edi (by decide), Kz.1 .edi (by decide)]
    exact BitVec.eq_of_toNat_eq (P.left.edi_toNat.trans P.right.edi_toNat.symm)
  · rw [valueU, valueZ]; exact P.pointer

end VG.Proof.RsaKeyGen.X86.HeaderSource
