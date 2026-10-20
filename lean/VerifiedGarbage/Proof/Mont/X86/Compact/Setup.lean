module

import VerifiedGarbage.Proof.Mont.X86.Compact.Length
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingPair
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args

/-! # Public counters and pointers for one paired-word row -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem setup_ok {g : Geometry} (v : g.Valid) {s : State} (C : Context g s)
    (ptr : List Instr) (bx w : Nat)
    (edi : PtrAt s g.W .edi g.S) (ebp : PtrAt s g.W .ebp w)
    (pointer : ∀ t, t.mem = s.mem → Ws t g.W g.L → Args t g.W g.L g.A →
      WP isa (.block ptr) t fun u => PtrAt u g.W .ecx bx ∧ u.mem = t.mem ∧ Keeps [.ecx, .edx] t u) :
    WP isa (.block ([.mov .ebx (.imm 0)] ++ ptr ++ Compact.lenTimes .esi .eax 0)) s fun t =>
      RowPointers g bx w t ∧ t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi] s t := by
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun a A _ => ?_
  refine WP.block_append (WP.mono (pointer a A.mem (C.ws.of_keeps A.keeps) (C.args.of_upd A (by decide)))
    fun b ⟨P, M, K⟩ => ?_)
  have args := (C.args.of_upd A (by decide)).of_keeps K (by decide) (by rw [M]; exact Outs.refl _ _ _)
  refine WP.mono (lenTimes_ok ((C.ws.of_keeps A.keeps).of_keeps K) args v.base
    (by have := v.lay.header; have := v.lay.scr; omega) 0) fun t ⟨len, Mt, Kt⟩ => ?_
  have keep : Keeps [.eax, .ebx, .ecx, .edx, .esi] s t :=
    ((A.keeps.mono (by decide)).widen K).widen Kt
  refine ⟨⟨?_, ?_, ?_, ?_⟩, Mt.trans (M.trans A.mem), keep⟩
  · rw [PtrAt, keep.1 .edi (by decide)]; exact edi
  · rw [PtrAt, keep.1 .ebp (by decide)]; exact ebp
  · rw [PtrAt, Kt.1 .ecx (by decide)]; exact P
  · rw [len, M, A.mem, show 2 ^ (3 + 0) = 8 from rfl, C.metadata.width,
      Nat.mod_eq_of_lt v.n32]

end VG.Proof.Mont.X86.Compact
