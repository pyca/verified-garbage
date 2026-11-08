module
public import VerifiedGarbage.Proof.Scrypt.X86_64.PackedBody
import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Tactic.DefEqTransformations
meta import VerifiedGarbage.Proof.Scrypt.X86_64.PackedBody
meta import VerifiedGarbage.Proof.Framework.Contract
meta import Mathlib.Tactic.DefEqTransformations

@[expose] public section
namespace VG.Proof.Scrypt.X86_64.Packed.BM
open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Impl.Scrypt.X86_64.Packed
open VG.Proof.Scrypt.X86_64.BlockMix

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

theorem body_rel {k : Nat} (hk : k < rr s₀) :
 RelCT isa (fun s t => Inv s₀ k s ∧ Inv s₀' k t) body fun s t =>
  (Inv s₀ (k+1) s ∧ s.zf=some (BitVec.ofNat 64 (rr s₀-k)-1==0)) ∧
  (Inv s₀' (k+1) t ∧ t.zf=some (BitVec.ofNat 64 (rr s₀'-k)-1==0)) := by
 have ct : RelCT isa (fun s t => Inv s₀ k s ∧ Inv s₀' k t) body (fun _ _ => True) :=
  RelCT.taint (A:=taint) (Taint.ofRegs [.rbx,.rbp,.r12,.r14]) (fun s t h =>
   Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    · rw [h.1.rbx,h.2.rbx,bB,bB,bP,bP,hq.rdi]
    · rw [h.1.rbp,h.2.rbp,yE,yE,yP,yP,hq.rdx]
    · rw [h.1.r12,h.2.r12,yO,yO,yP,yP,hq.rdx,hq.rr]
    · rw [h.1.r14,h.2.r14,hq.rr]) (by taint_decide)
 exact (ct.wp fun _ _ h => ⟨body_ok hp hk h.1,body_ok hp' (hq.rr ▸ hk) h.2⟩).mono
  (fun _ _ h => h) (fun _ _ h => h.2)

theorem loop_rel :
    RelCT isa (fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s') (.loop body .ne) fun s s' =>
      Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := body) (c := .ne)
    (Q := fun s s' => Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s')
    (fun n s s' => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s ∧ Inv s₀' k s') (fun n => by
      intro s s' t t' u u' ⟨k, hn, hk, h, h'⟩ e e'
      have hk' : k < rr s₀' := hq.rr ▸ hk
      obtain ⟨ht, ⟨i, z⟩, ⟨i', z'⟩⟩ := body_rel hp hp' hq hk _ _ _ _ _ _ ⟨h, h'⟩ e e'
      beta_reduce
      rw [eval_ne hp hk z, eval_ne hp' hk' z', ← hq.rr]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : k + 1 = rr s₀ := by simpa using hf
        exact ⟨hl ▸ i, hl ▸ i'⟩
      · have hl : k + 1 ≠ rr s₀ := by simpa using ht'
        exact ⟨rr s₀ - (k + 1), by omega, k + 1, rfl, by omega, i, i'⟩) (rr s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, hp.pos, h.1, h.2⟩) fun _ _ h => h

theorem blockMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') Packed.blockMix fun _ _ => True := by
  unfold Packed.blockMix
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block (bmPrologue ++ Packed.load))
      fun s s' => Inv s₀ 0 s ∧ Inv s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.r8
        · exact hq.rsp) (c := .block (bmPrologue ++ Packed.load)) (by taint_decide)).wp
      (F₁ := Inv s₀ 0) (F₂ := Inv s₀' 0) fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨prologue_ok hp, prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => Inv s₀ (rr s₀) s ∧ Inv s₀' (rr s₀') s') (.block bmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r13]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r13, h.2.r13, sc, sc, hq.r8]) (by taint_decide)
  exact pro.seq ((loop_rel hp hp' hq).seq epi)

end
end VG.Proof.Scrypt.X86_64.Packed.BM
