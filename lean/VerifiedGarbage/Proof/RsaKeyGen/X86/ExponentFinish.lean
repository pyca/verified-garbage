module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Exponent
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr
public import Init.Prelude
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # Store the complete paired alignment marker after the prepared exponent -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Exponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Exponent

theorem finish_ok {s : State} {base : Addr} {size n out : Nat} (scratch : Scr s base size)
    (markerFit : markerOffset + 8 ≤ size) (outFit : out + 4 * n + 8 ≤ size) :
    WP isa (.block (finish n out)) s fun t =>
      word t.mem base (out + 4 * n) = word s.mem base markerOffset ∧
      Outside base (out + 4 * n) 8 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  unfold finish
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (scratch.of_keeps A.keeps (by decide)) (by omega)) fun b B _ => ?_
  have K : Keeps [.eax, .edx] s b := (A.keeps.mono (by decide)).widen B.keeps
  refine WP.mono (Header.storePair_ok (scratch.of_keeps K (by decide)) outFit) fun t ⟨M, O, Kt⟩ => ?_
  have pair : b.gpr .edx ++ b.gpr .eax = word s.mem base markerOffset := by
    rw [B.gpr, B.other .eax (by decide), A.gpr, A.mem,
      VG.Proof.Mont.word, VG.Proof.Rc2.Word32.read64_pair, VG.Offset.add_add]
  refine ⟨?_, ?_, K.widen Kt⟩
  · rw [VG.Proof.Mont.word, M, Mem.readW_writeW_self64, pair]
  · rw [B.mem, A.mem] at O
    exact O

end VG.Proof.RsaKeyGen.X86.Exponent
