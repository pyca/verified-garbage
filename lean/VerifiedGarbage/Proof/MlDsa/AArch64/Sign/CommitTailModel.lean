import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailPadding
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMemory

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.Vector (xorWords)
open VG.Proof.MlDsa.AArch64.Optimized.Resident (permuted RateBlock StreamOutput)

/-- Low-lane absorb performed after permutation `i`. The last permutation
has no following absorb; only its digest is serialized. -/
def absorbAfter (wlen : Nat) (m : Mem) (w1 : Addr) (i : Nat) (A : Spec.Sha3.State) : Spec.Sha3.State :=
  let n := (64+wlen)/136
  if i<n-1 then xorWords A m (w1+BitVec.ofNat 64 (72+136*i)) 17
  else if i=n-1 then
    if wlen=768 then paddedState (xorWords A m (w1+BitVec.ofNat 64 (72+136*i)) 2) 2
    else paddedState A 0
  else A

def lowRun (wlen : Nat) (m : Mem) (w1 : Addr) (A : Spec.Sha3.State) : Nat → Spec.Sha3.State
  | 0 => A
  | i+1 => absorbAfter wlen m w1 i (Spec.Sha3.keccakF (lowRun wlen m w1 A i))

def fullCount (wlen i : Nat) : Nat := min i ((64+wlen)/136-1)

def inputPtr (wlen : Nat) (w1 : Addr) (i : Nat) : Addr :=
  w1+BitVec.ofNat 64 (72+136*fullCount wlen i)

/-- One newly serialized high-lane block leaves previous blocks unchanged. -/
theorem streamOutput_append {m m' : Mem} {p : Addr} {j : Nat} {B : Spec.Sha3.State}
    (hj : j<5) (h : StreamOutput m p 8 j B)
    (hn : RateBlock m' (p+BitVec.ofNat 64 (136*j)) 8 (permuted B (j+1)))
    (hf : Frame [⟨p+BitVec.ofNat 64 (136*j),136⟩] m m') :
    StreamOutput m' p 8 (j+1) B := by
  intro i hi
  by_cases he : i=j
  · subst i; exact hn
  · refine (h i (by omega)).keep (by decide) hf ?_
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact VG.Proof.MlDsa.AArch64.Optimized.Resident.block_disjoint (by decide) (by omega) (by omega)

/-- Absorbs depend only on the words in their readable input slice. -/
theorem xorWords_congr {A : Spec.Sha3.State} {m m' : Mem} {p : Addr} {n : Nat}
    (h : ∀j<n,m'.readW (p+BitVec.ofNat 64 (8*j)) 64=m.readW (p+BitVec.ofNat 64 (8*j)) 64) :
    xorWords A m' p n=xorWords A m p n := by
  apply Vector.ext
  intro i hi
  rw [VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords_get,
    VG.Proof.Sha3.AArch64.Sha3.Vector.xorWords_get]
  by_cases hn : i<n
  · rw [ite_eq_left hn,ite_eq_left hn]
    exact congrArg (fun x=>A[i] ^^^ x) (h i hn)
  · rw [ite_eq_right hn,ite_eq_right hn]

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
