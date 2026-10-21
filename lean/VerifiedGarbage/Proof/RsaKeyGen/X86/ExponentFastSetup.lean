module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentFilter
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
import VerifiedGarbage.Proof.Mont.Words32

/-! # A single fast-exponent frame saves the workspace and the candidate end -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentFilter
open VG.Impl.Bignum.X86.PublicContext

theorem fastArgs_ok {p : BitVec 32} {w : Nat} {s : State} (C : Sieve.StackContext p s) :
    WP isa (.block (.store (at_ .esp 0) .edi :: fastArgs w)) s fun t =>
      t.gpr .edi = s.gpr .edi + BitVec.ofNat 32 (slot w 5) ∧
      t.mem.readW (off (p.setWidth 64) 4) 32 = s.gpr .edi + BitVec.ofNat 32 (slot w 5) + BitVec.ofNat 32 (8 * w) ∧
      t.mem.readW (off (p.setWidth 64) 0) 32 = s.gpr .edi ∧
      Outside (p.setWidth 64) 0 8 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  unfold fastArgs
  refine wp_storeS (C.address 0 (by decide)) (ws_write C.ws (by decide)) fun a A => ?_
  have Ca := C.keep (A.keeps []) (by decide)
  refine wp_addS rfl fun b B _ => wp_movS rfl fun c D _ => wp_addS rfl fun d E _ => ?_
  have K : Keeps [.eax, .edi] s d := (((A.keeps [.eax, .edi]).widen B.keeps).widen D.keeps).widen E.keeps
  have Cd := C.keep K (by decide)
  refine wp_storeS (Cd.address 4 (by decide)) (ws_write Cd.ws (by decide)) fun t T => WP.block_nil ?_
  have value : d.gpr .eax = s.gpr .edi + BitVec.ofNat 32 (slot w 5) + BitVec.ofNat 32 (8 * w) := by
    rw [E.gpr, D.gpr, B.gpr, (A.keeps []).1 .edi (by decide)]
  have memD : d.mem = a.mem := E.mem.trans (D.mem.trans B.mem)
  have Oa : Outside (p.setWidth 64) 0 4 s.mem a.mem := by
    rw [A.mem]
    exact writeW32_outside _ _ _ (by decide)
  have Ot : Outside (p.setWidth 64) 4 4 a.mem t.mem := by
    rw [T.mem, memD]
    exact writeW32_outside _ _ _ (by decide)
  refine ⟨?_, ?_, ?_, (Oa.mono (by decide) (by decide)).trans (Ot.mono (by decide) (by decide)), K.widen (T.keeps [])⟩
  · rw [(T.keeps []).1 .edi (by decide), E.other .edi (by decide), D.other .edi (by decide), B.gpr, (A.keeps []).1 .edi (by decide)]
  · rw [T.mem, Mem.readW_writeW_self32, value]
  · rw [BitVec.eq_of_toNat_eq (Ot.w32 (d := 0) (by decide) (by decide)), A.mem, Mem.readW_writeW_self32]

end VG.Proof.RsaKeyGen.X86.ExponentFilter
