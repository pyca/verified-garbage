module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateBits
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Force a native word's candidate bits without touching other memory -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateBits
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.CandidateBits

theorem forceWord_ok {s : State} {base : Addr} {size offset : Nat} (mask : BitVec 32)
    (scratch : Scr s base size) (fit : offset + 4 ≤ size) :
    WP isa (.block (forceWord offset mask)) s fun t =>
      w32 t.mem base offset = w32 s.mem base offset ||| mask.toNat ∧
      Outside base offset 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold forceWord
  refine wp_movS (readSrc_sc scratch fit) fun a A _ => wp_orS rfl fun b B => ?_
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  have Sb := scratch.of_keeps K (by decide)
  refine wp_storeS (Sb.ea (by omega)) (Sb.write fit) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, K.widen (T.keeps [])⟩
  · rw [T.mem, w32_write_self, B.gpr, A.gpr, BitVec.toNat_or]
  · rw [T.mem, B.mem, A.mem]
    exact writeW32_outside _ _ _ (by have := scratch.nowrap; omega)

end VG.Proof.RsaKeyGen.X86.CandidateBits
