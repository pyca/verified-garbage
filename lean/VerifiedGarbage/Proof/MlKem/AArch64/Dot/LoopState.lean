module

public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Step

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Dot
open VG.AArch64 VG.Spec.MlKem

def blockValues (F : (Nat × Nat) → Nat → Nat) (c : Nat) : (Nat × Nat) → Nat → Nat :=
  fun fg e => F fg (8*c+e)

def blockGamma (Γ : Nat → Nat) (c : Nat) : Nat → Nat := fun e => Γ (4*c+e)

def result (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat)
    (j : Nat) : BitVec 32 :=
  interleave (evenResult terms (blockValues F (j/8)) (blockValues G (j/8)) (blockGamma Γ (j/8)))
    (oddResult terms (blockValues F (j/8)) (blockValues G (j/8))) (j%8)

theorem result_block (terms : List (Nat × Nat)) (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat)
    (c : Nat) {e : Nat} (he : e < 8) :
    result terms F G Γ (8*c+e) =
      interleave (evenResult terms (blockValues F c) (blockValues G c) (blockGamma Γ c))
        (oddResult terms (blockValues F c) (blockValues G c)) e := by
  unfold result
  rw [show (8*c+e)/8 = c by omega, show (8*c+e)%8 = e by omega]

structure LoopInv (s₀ : State) (p t : Addr) (O : Nat → BitVec 32) (c : Nat) (s : State) : Prop where
  keep : Keep clob s₀ s
  frame : Frame [polyRegion p] s₀.mem s.mem
  constants : VConsts s
  x0 : s.gpr .x0 = coeffAddr p (8*c)
  x3 : s.gpr .x3 = t + BitVec.ofNat 64 (16*c)
  x12 : s.gpr .x12 = BitVec.ofNat 64 (32*c)
  x11 : (s.gpr .x11).toNat = 32-c
  out : CoeffsUpTo s.mem p (8*c) O (fun i => coeffAt s₀.mem p i)

structure LoopData (s₀ : State) (p t : Addr) (terms : List (Nat × Nat))
    (F G : (Nat × Nat) → Nat → Nat) (Γ : Nat → Nat) : Prop where
  count : terms.length ≤ 4
  offF : ∀ fg ∈ terms, fg.1 < 65536
  offG : ∀ fg ∈ terms, fg.2 < 65536
  boundF : ∀ fg ∈ terms, ∀ i < 256, F fg i < 3329
  boundG : ∀ fg ∈ terms, ∀ i < 256, G fg i < 3329
  valueF : ∀ fg ∈ terms, ∀ i < 256,
    (coeffAt s₀.mem (s₀.gpr .x28 + BitVec.ofNat 64 fg.1) i).toNat = F fg i
  valueG : ∀ fg ∈ terms, ∀ i < 256,
    (coeffAt s₀.mem (s₀.gpr .x28 + BitVec.ofNat 64 fg.2) i).toNat = G fg i
  apartF : ∀ fg ∈ terms, (polyRegion p).Disjoint (polyRegion (s₀.gpr .x28 + BitVec.ofNat 64 fg.1))
  apartG : ∀ fg ∈ terms, (polyRegion p).Disjoint (polyRegion (s₀.gpr .x28 + BitVec.ofNat 64 fg.2))
  readF : ∀ fg ∈ terms, ∀ j, j+4 ≤ 256 →
    InRegions (s₀.rd ++ s₀.wr) (coeffAddr (s₀.gpr .x28 + BitVec.ofNat 64 fg.1) j) 16
  readG : ∀ fg ∈ terms, ∀ j, j+4 ≤ 256 →
    InRegions (s₀.rd ++ s₀.wr) (coeffAddr (s₀.gpr .x28 + BitVec.ofNat 64 fg.2) j) 16
  write : ∀ j, j+4 ≤ 256 → InRegions s₀.wr (coeffAddr p j) 16
  tableApart : (polyRegion p).Disjoint ⟨t,512⟩
  tableRead : ∀ c < 32, InRegions (s₀.rd ++ s₀.wr) (t+BitVec.ofNat 64 (16*c)) 16
  tableValue : ∀ c < 32, Lanes (s₀.mem.read (t+BitVec.ofNat 64 (16*c)) 16) (blockGamma Γ c)
  tableBound : ∀ i < 128, Γ i < 3329

end VG.Proof.MlKem.AArch64.Dot
