module

public import VerifiedGarbage.Impl.Bignum.X86.ImportArray
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Point the byte-copy destination at a packed workspace array -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86

theorem importArrayArgs_ok (n dst : Nat) (s : State) :
    WP isa (.block (importArrayArgs n dst)) s fun t =>
      t.gpr .ebx = s.gpr .edi + BitVec.ofNat 32 dst ∧ t.gpr .ecx = BitVec.ofNat 32 (8 * n) ∧
      t.mem = s.mem ∧ Keeps [.ebx, .ecx] s t := by
  unfold importArrayArgs
  refine wp_movS rfl fun u A _ => ?_
  refine wp_addS rfl fun v B _ => ?_
  refine wp_movS rfl fun t C _ => WP.block_nil ?_
  exact ⟨by rw [C.other .ebx (by decide), B.gpr, A.gpr], C.gpr,
    C.mem.trans (B.mem.trans A.mem), ((A.keeps.trans B.keeps).mono (by decide)).trans (C.keeps.mono (by decide))⟩

end VG.Proof.Bignum.X86
