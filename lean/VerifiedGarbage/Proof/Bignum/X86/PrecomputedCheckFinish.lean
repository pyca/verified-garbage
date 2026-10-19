module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputedChecks
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Merge the two range checks and the public modulus parity -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86.PublicContext

theorem precomputedCheckFinish_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (space : size n ≤ bytes) :
    WP isa (.block (precomputedCheckFinish n)) s fun t =>
      t.gpr .ecx = s.gpr .ecx &&& s.mem.readW (off base 148) 32 &&&
        (s.mem.readW (off base (VG.Impl.Bignum.X86.PublicContext.slot n 0)) 32 &&& 1) ∧
      t.zf = some (t.gpr .ecx == 0) ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have hd := slot_header n 0
  simp only [stride] at b0
  unfold precomputedCheckFinish
  refine wp_movS (readSrc_sc hs (by change 148 + 4 ≤ bytes; omega)) fun u A _ => ?_
  refine wp_logicS (.inl rfl) rfl fun v B => ?_
  have hv := (hs.of_keeps A.keeps (by decide)).of_keeps B.keeps (by decide)
  refine wp_movS (readSrc_sc hv (by omega)) fun w C _ => ?_
  refine wp_logicS (.inl rfl) rfl fun x D => ?_
  refine wp_logicS (.inl rfl) rfl fun y E => ?_
  refine wp_cmpS rfl fun t F Z => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [F.gpr, E.gpr, D.other .ecx (by decide), C.other .ecx (by decide), B.gpr,
      A.other .ecx (by decide), A.gpr, D.gpr, C.gpr, B.mem, A.mem]
    rfl
  · have zero : y.gpr .ecx - (0 : BitVec 32) = y.gpr .ecx := BitVec.sub_zero _
    rw [Z, zero, F.gpr]
  · rw [F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]
  · exact (((((A.keeps.mono (by decide)).widen B.keeps).widen C.keeps).widen D.keeps).widen E.keeps).trans (F.keeps _)

end VG.Proof.Bignum.X86.PublicContext
