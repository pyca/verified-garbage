module

public import VerifiedGarbage.Proof.Mont.X86.CombTableState
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Layout
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame

import VerifiedGarbage.Proof.Mont.X86.CombScan
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Words
/-! Public and private lookups return the same canonical table value. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/Select.lean`, which only this module imported.
section

/-! Instantiate the shared private lookup in the five DSA working layouts. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem scan_layout {n e : Nat} (h : Supported n e) :
    CombScanLay n (context n+16*n) (slot n 7) (slot n 1) (layout n e).size ∧
    8 ≤ slot n 1 ∧ slot n 1+128 ≤ context n+16*n := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    constructor
  all_goals first
    | exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    | decide

theorem private_select_ok {s : State} {base : Addr} {n e : Nat}
    (h : Supported n e) (hs : Scr s base (layout n e).size) (hw : w32 s.mem base 4 < 32) :
    WP isa (VG.Impl.Mont.X86.Comb.wordSelect n (context n+16*n) (slot n 7)) s fun t =>
      Outs base [(slot n 1, 128), (slot n 7, 8*n)] s.mem t.mem ∧
      wordsVal t.mem base (slot n 7) n =
        wordsVal s.mem base (entry n (context n+16*n) (w32 s.mem base 4)) n ∧
      Keeps [.eax, .ebx, .ecx, .ebp] s t := by
  obtain ⟨L, header, sep⟩ := scan_layout h
  exact wordSelectBody_ok hs L header hw (.inl sep)

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/SelectContext.lean`, which only this module imported.
section

/-! Private selection preserves the modulus and Montgomery inverse. -/

section
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
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Mont.X86.Comb (TableAt tableValue)

theorem table_layout {n e : Nat} (h : Supported n e) :
    VG.Proof.Mont.X86.Comb.Layout n (context n) (layout n e).size := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
    constructor <;> decide

theorem select_table_ok {s : State} {base : Addr} {n e m g : Nat}
    (h : Supported n e) (pub : Bool) (C : Context n m base (layout n e).size s)
    (T : TableAt n (context n) m g (32*e) base (fun _ => True) s.mem)
    (hw : w32 s.mem base 4 < 32) :
    WP isa (if pub then VG.Impl.Mont.X86.Comb.publicSelect n (context n+16*n) (slot n 7)
      else VG.Impl.Mont.X86.Comb.wordSelect n (context n+16*n) (slot n 7)) s fun t =>
      Context n m base (layout n e).size t ∧
      TableAt n (context n) m g (32*e) base (fun _ => True) t.mem ∧
      wordsVal t.mem base (slot n 7) n = tableValue n m g (32*e) (w32 s.mem base 4) ∧
      Outs base [(slot n 1,128),(slot n 7,8*n)] s.mem t.mem ∧
      Keeps [.eax,.ebx,.ecx,.edx,.ebp] s t := by
  cases pub with
  | true =>
    refine WP.mono (VG.Proof.Mont.X86.Comb.select_table_ok (table_layout h) C T (by decide) (by decide) hw trivial)
      fun t ⟨Ct,Tt,V,O,K⟩ => ?_
    exact ⟨Ct,Tt,V,Outs.of_outside O (by simp),K⟩
  | false =>
    refine WP.mono (private_select_context h C hw) fun t ⟨Ct,O,V,K⟩ => ?_
    refine ⟨Ct,T.outs (table_layout h) C.scr O ?_,V.trans (T _ hw trivial),O,K.mono (by decide)⟩
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    all_goals
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide

end VG.Proof.Dsa.X86.Comb
