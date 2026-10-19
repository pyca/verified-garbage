module

import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchDone
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout

/-! # Only a native rejection continues the search loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem done_loop_guard {p : SearchPublic} {original s : State} {result : Spec.Ffdh.ParameterSearchResult}
    (h : SearchDone p original result s) :
    WP isa (.block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]) s fun t =>
      eval .e t = some false ∧ SearchDone p original result t := by
  have hb : result.status < 2 ^ 64 := by cases result <;> dsimp only [Spec.Ffdh.ParameterSearchResult.status] <;> decide
  refine WP.mono (loop_guard (h.input.control_scr h.wr) h.r12 h.status hb)
    fun t ⟨⟨he, hm⟩, k⟩ => ?_
  refine ⟨?_, h.keep k hm (by decide)⟩
  cases result <;> exact he

theorem live_loop_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]) s fun t =>
      eval .e t = some true ∧ SearchLive p original used remaining t := by
  refine WP.mono (loop_guard (status := 4) (h.input.control_scr h.wr) h.r12 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨he, h.keep k hm (by decide)⟩

end VG.Proof.Ffdh.X86_64.Generation
