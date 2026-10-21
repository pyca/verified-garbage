module

import VerifiedGarbage.Proof.Dsa.X86.Comb.Select
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! Private selection preserves the modulus and Montgomery inverse. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem private_select_context {s : State} {base : Addr} {n e m : Nat}
    (h : Supported n e) (C : Context n m base (layout n e).size s) (hw : w32 s.mem base 4 < 32) :
    WP isa (VG.Impl.Mont.X86.Comb.wordSelect n (context n+16*n) (slot n 7)) s fun t =>
      Context n m base (layout n e).size t ∧
      Outs base [(slot n 1, 128), (slot n 7, 8*n)] s.mem t.mem ∧
      wordsVal t.mem base (slot n 7) n =
        wordsVal s.mem base (entry n (context n+16*n) (w32 s.mem base 4)) n ∧
      Keeps [.eax, .ebx, .ecx, .ebp] s t := by
  refine WP.mono (private_select_ok h C.scr hw) fun t ⟨O, V, K⟩ => ⟨?_, O, V, K⟩
  apply C.outs_keep K (by decide) (by decide) O
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

end VG.Proof.Dsa.X86.Comb
