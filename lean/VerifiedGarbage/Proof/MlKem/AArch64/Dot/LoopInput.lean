module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.LoopState
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

theorem coeffAt_shift (m : Mem) (p : Addr) (j e : Nat) :
    coeffAt m (coeffAddr p j) e = coeffAt m p (j+e) := by
  change m.readW (coeffAddr p j + BitVec.ofNat 64 (4*e)) 32 = _
  rw [coeffAddr_off]; rfl

theorem loop_input {s₀ s : State} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat} {O : Nat → BitVec 32} {c : Nat}
    (hd : LoopData s₀ p t terms F G Γ) (hc : c < 32) (h : LoopInv s₀ p t O c s)
    {fg : Nat × Nat} (hf : fg ∈ terms) :
    TermInput s fg (blockValues F c fg) (blockValues G c fg) := by
  have addr (off : Nat) : s.gpr .x28 + BitVec.ofNat 64 off + s.gpr .x12 =
      coeffAddr (s₀.gpr .x28 + BitVec.ofNat 64 off) (8*c) := by
    rw [h.keep.get .x28,h.x12,coeffAddr, show 4*(8*c) = 32*c by omega]
  refine ⟨hd.offF fg hf, hd.offG fg hf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he; exact hd.boundF fg hf _ (by omega)
  · intro e he; exact hd.boundG fg hf _ (by omega)
  · intro e he
    rw [addr, coeffAt_shift, coeffAt_frame h.frame (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hd.apartF fg hf).symm) (by omega)]
    exact hd.valueF fg hf _ (by omega)
  · intro e he
    rw [addr, coeffAt_shift, coeffAt_frame h.frame (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hd.apartG fg hf).symm) (by omega)]
    exact hd.valueG fg hf _ (by omega)
  · intro i hi
    rw [h.keep.rd,h.keep.wr,addr,show 16*i = 4*(4*i) by omega,coeffAddr_off]
    exact hd.readF fg hf _ (by omega)
  · intro i hi
    rw [h.keep.rd,h.keep.wr,addr,show 16*i = 4*(4*i) by omega,coeffAddr_off]
    exact hd.readG fg hf _ (by omega)

theorem loop_gamma {s₀ s : State} {p t : Addr} {terms : List (Nat × Nat)}
    {F G : (Nat × Nat) → Nat → Nat} {Γ : Nat → Nat} {O : Nat → BitVec 32} {c : Nat}
    (hd : LoopData s₀ p t terms F G Γ) (hc : c < 32) (h : LoopInv s₀ p t O c s) :
    Lanes (s.mem.read (s.gpr .x3 + BitVec.ofNat 64 0) 16) (blockGamma Γ c) := by
  rw [h.x3,BitVec.add_zero,h.frame.read (r := ⟨t,512⟩) (contains_off (by omega) (by decide))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.tableApart.symm) (by decide)]
  exact hd.tableValue c hc

end VG.Proof.MlKem.AArch64.Dot
