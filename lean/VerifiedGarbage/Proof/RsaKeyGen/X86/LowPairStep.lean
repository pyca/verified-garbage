module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowPair
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPair
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Each public scan position reads one native pair, without modifying memory -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowPair

def pairAt (m : Mem) (base : Addr) (offset : Nat) : BitVec 32 × BitVec 32 :=
  (m.readW (VG.Proof.Mont.off base offset) 32, m.readW (VG.Proof.Mont.off base (offset + 4)) 32)

def select (before next : BitVec 32 × BitVec 32) : BitVec 32 × BitVec 32 :=
  if before.1 = 0#32 ∧ before.2 = 0#32 then next else before

theorem step_ok {s : State} {base : Addr} {size src index : Nat} (scratch : Scr s base size)
    (fit : src + 8 * index + 8 ≤ size) :
    WP isa (.block (step src index)) s fun t =>
      (t.gpr .ebx, t.gpr .esi) = select (s.gpr .ebx, s.gpr .esi) (pairAt s.mem base (src + 8 * index)) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  unfold step
  refine WP.block_append (wp_movS (readSrc_sc scratch (by omega)) fun a A _ =>
    wp_movS (readSrc_sc (scratch.of_keeps A.keeps (by decide)) (by omega)) fun b B _ => WP.block_nil ?_)
  have K : Keeps [.eax, .ecx] s b := (A.keeps.mono (by decide)).widen B.keeps
  have M : b.mem = s.mem := B.mem.trans A.mem
  refine WP.mono (choose_ok b) fun t ⟨V, Mt, Kt⟩ => ?_
  rw [K.1 .ebx (by decide), K.1 .esi (by decide), B.gpr, B.other .eax (by decide), A.gpr, A.mem] at V
  exact ⟨V, Mt.trans M, (K.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.LowPair
