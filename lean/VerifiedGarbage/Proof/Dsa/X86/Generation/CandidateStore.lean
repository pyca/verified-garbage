module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateStore
import VerifiedGarbage.Proof.Mont.X86.Instr
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Bytes

/-! # Public candidate serialization retains the exact big-endian value -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem storePublic_ok {s : State} {base : Addr} {size len n input : Nat}
    (S : Scr s base size) (room : input + 8 * n ≤ size)
    (h4 : 4 ≤ len) (hlen : len ≤ 8 * n) (hw4 : len % 4 = 0)
    (fit : (s.gpr .esi).toNat + len ≤ 2 ^ 32)
    (write : ∀ e k, e + k ≤ len → InRegions s.wr ((s.gpr .esi).setWidth 64 + BitVec.ofNat 64 e) k)
    (apart : Region.Disjoint ⟨off base input, 8 * n⟩ ⟨(s.gpr .esi).setWidth 64, len⟩) :
    WP isa (storePublic len input) s fun t =>
      Spec.Rsa.bytesAt t.mem ((s.gpr .esi).setWidth 64) len =
        Spec.Dsa.encodeBE len (wordsVal s.mem base input n) ∧
      Outside ((s.gpr .esi).setWidth 64) 0 len s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold storePublic
  refine WP.seq (wp_movS rfl fun a sa _ => WP.block_nil ?_)
  have si := sa.other .esi (by decide)
  refine WP.mono (storeComponent_ok (S.of_keeps sa.keeps (by decide)) true sa.gpr room h4 hlen hw4
    (by rw [si]; exact fit) (by intro e k hk; rw [sa.wr, si]; exact write e k hk)
    (by rw [si]; exact apart)) fun t ⟨value, K, O⟩ => ?_
  simp only [ite_true, si, sa.mem] at value O
  exact ⟨value, O, (sa.keeps.mono (by decide)).trans (K.mono (by decide))⟩
end VG.Proof.Dsa.X86.Generation
