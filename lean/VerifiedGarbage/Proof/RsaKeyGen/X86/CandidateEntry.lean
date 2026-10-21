module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArgs
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArgContext

/-! # The cdecl candidate entry establishes its workspace from argument nine -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateArgs
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.RsaKeyGen.X86.CandidateArgs

structure Entry (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s : State) : Prop where
  workspace : Ws s base size
  header : 48 ≤ size
  pointer : (inputs 9).setWidth 64 = base
  stack : StkOk p base size
  sp : s.gpr .esp = p
  fit : p.toNat + 64 ≤ 2 ^ 32
  separate : (argsRegion p).Disjoint ⟨base, size⟩
  read : ∀ i < 11, readSrc s (.mem (arg i)) = some (inputs i)

theorem enter_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (E : Entry base size p inputs s) :
    WP isa enter s fun t =>
      Context base size p inputs t ∧ (∀ i < 11, t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
      t.mem.readW (off base 44) 32 = inputs 2 ∧ Outside base 0 48 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  unfold enter
  refine WP.seq (wp_movS (E.read 9 (by decide)) fun a A _ => WP.block_nil ?_)
  have Sa : Scr a base size := by
    refine ⟨?_, ?_, E.workspace.nowrap, ?_⟩
    · rw [A.gpr]; exact E.pointer
    · rw [A.keeps.2.2]; exact E.workspace.wr
    · rw [A.other .esp (by decide), E.sp]; exact E.stack
  have C : Context base size p inputs a := by
    refine ⟨Sa, E.header, (A.other .esp (by decide)).trans E.sp, E.fit, E.separate, ?_⟩
    intro i index
    have address : a.ea (arg i) = s.ea (arg i) := by
      change addr (a.gpr .esp) _ = addr (s.gpr .esp) _
      rw [A.other .esp (by decide)]
    have same : readSrc a (.mem (arg i)) = readSrc s (.mem (arg i)) := by
      show a.load32 (a.ea (arg i)) = s.load32 (s.ea (arg i))
      simp only [State.load32, address, A.keeps.2.1, A.keeps.2.2, A.mem]
    exact same.trans (E.read i index)
  refine WP.mono (code_ok C) fun t ⟨T, values, usedPtr, O, K⟩ => ?_
  rw [A.mem] at O
  exact ⟨T, values, usedPtr, O, (A.keeps.mono (by decide)).widen K⟩

end VG.Proof.RsaKeyGen.X86.CandidateArgs
