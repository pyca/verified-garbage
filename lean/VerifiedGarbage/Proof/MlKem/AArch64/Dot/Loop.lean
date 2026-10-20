module
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopState

import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopInput
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

theorem loop_step {s₀ s : State} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat} {c : Nat}
    (hd : LoopData s₀ p t terms F G Γ) (hc : c < 32)
    (h : LoopInv s₀ p t (result terms F G Γ) c s) :
    WP isa (.block (body terms)) s fun s' =>
      LoopInv s₀ p t (result terms F G Γ) (c+1) s' ∧
      ((s'.gpr .x11).toNat ≠ 0 ↔ c+1 ≠ 32) := by
  refine WP.mono (step_ok terms h.constants hd.count (fun _ hf => loop_input hd hc h hf)
    (by rw [h.keep.rd,h.keep.wr,h.x3,BitVec.add_zero]; exact hd.tableRead c hc)
    (loop_gamma hd hc h) (fun e he => hd.tableBound _ (by omega)) h.x0 (by omega)
    (fun i hi => by rw [h.keep.wr]; exact hd.write _ (by omega)) h.out
    (fun e he => result_block terms F G Γ c he)) fun s' hs => ?_
  have counter : (s'.gpr .x11).toNat = 32-(c+1) := by
    rw [hs.x11,toNat_sub_n (by rw [h.x11]; simp only [BitVec.toNat_ofNat]; omega),h.x11]
    simp only [BitVec.toNat_ofNat]
    omega
  refine ⟨⟨(h.keep.trans hs.keep).mono, h.frame.trans hs.frame, hs.constants, ?_, ?_, ?_,
    counter, ?_⟩, by rw [counter]; omega⟩
  · rw [hs.x0,h.x0,coeffAddr,ptr_add,show 4*(8*c)+32 = 4*(8*(c+1)) by omega]
  · rw [hs.x3,h.x3,ptr_add,show 16*c+16 = 16*(c+1) by omega]
  · rw [hs.x12,h.x12,←BitVec.ofNat_add,show 32*c+32 = 32*(c+1) by omega]
  · simpa only [show 8*c+8 = 8*(c+1) by omega] using hs.out

theorem loop_ok {s₀ s : State} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat}
    (hd : LoopData s₀ p t terms F G Γ)
    (h : LoopInv s₀ p t (result terms F G Γ) 0 s) :
    WP isa (.loop (.block (body terms)) (.nonzero .x .x11)) s
      (LoopInv s₀ p t (result terms F G Γ) 32) :=
  count_loop (by decide) (LoopInv s₀ p t (result terms F G Γ))
    (fun _ hc _ hi => loop_step hd hc hi) h

end VG.Proof.MlKem.AArch64.Dot
