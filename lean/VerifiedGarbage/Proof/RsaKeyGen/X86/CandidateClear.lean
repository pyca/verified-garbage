module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateClear
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Output clearing is complete even when candidate entropy is exhausted -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateClear
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86

theorem code_ok {s : State} {base : Addr} {size len : Nat} {out : BitVec 32}
    (S : Scr s base size) (header : 8 ≤ size) (positive : 0 < len) (lengthBound : len < 2 ^ 32)
    (outEq : s.mem.readW (off base 0) 32 = out)
    (lenEq : s.mem.readW (off base 4) 32 = BitVec.ofNat 32 len)
    (fit : out.toNat + len ≤ 2 ^ 32) (write : InRegions s.wr (out.setWidth 64) len) :
    WP isa VG.Impl.RsaKeyGen.X86.CandidateClear.code s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) len = List.replicate len 0 ∧
      t.gpr .eax = 0#32 ∧ Outside (out.setWidth 64) 0 len s.mem t.mem ∧
      Keeps [.esi, .ecx, .eax] s t := by
  unfold VG.Impl.RsaKeyGen.X86.CandidateClear.code VG.Impl.RsaKeyGen.X86.CandidateClear.args
  refine WP.seq (wp_movS (readSrc_sc S (d := 0) (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (S.of_keeps A.keeps (by decide)) (d := 4) (by omega)) fun b B _ =>
    wp_movS rfl fun c C _ => WP.block_nil ?_)
  have K : Keeps [.esi, .ecx, .eax] s c := ((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps
  have M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  refine WP.mono (VG.Proof.Dsa.X86.failureLoop_ok positive lengthBound fit
    (by rw [C.other .esi (by decide), B.other .esi (by decide), A.gpr, outEq])
    (by rw [C.other .ecx (by decide), B.gpr, A.mem, lenEq]) C.gpr ?_) fun t ⟨V, Z, O, T⟩ => ?_
  · intro i index
    rw [K.2.2]
    obtain ⟨r, mem, contains⟩ := write
    exact ⟨r, mem, contains.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  · exact ⟨V, Z, M ▸ O, K.trans (T.mono (by decide))⟩

end VG.Proof.RsaKeyGen.X86.CandidateClear
