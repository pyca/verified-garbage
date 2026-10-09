import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableWords
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem

namespace VG.Proof.MlDsa.AArch64.Optimized.PairedTable
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (z bar)

/-- The immutable inverse table's actual packed artifact data. -/
def Artifact (m : Mem) (p : Addr) : Prop :=
  ∀ i<512, m.readW (p+BitVec.ofNat 64 (8*i)) 64=expandedWords[i]!

def Words (m : Mem) (p : Addr) : Prop :=
  ∀ k<1024, m.readW (p+BitVec.ofNat 64 (4*k)) 32=BitVec.ofNat 32 expandedVals[k]!

theorem Artifact.words {m : Mem} {p : Addr} (h : Artifact m p) : Words m p := by
  intro k hk
  have hi : k/2<512 := by omega
  have hv := h (k/2) hi
  have hr : k%2=0 ∨ k%2=1 := by omega
  rcases hr with hr | hr
  · have he : k=2*(k/2) := by omega
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 0 32) hv
    rw [readW64_lo,expandedWords_low hi] at hx
    simpa only [show 8*(k/2)=4*k by omega,← he] using hx
  · have he : k=2*(k/2)+1 := by omega
    have hx := congrArg (fun v : BitVec 64 => v.extractLsb' 32 32) hv
    rw [readW64_hi,expandedWords_high hi,BitVec.add_assoc,
      ← BitVec.ofNat_add (8*(k/2)) 4] at hx
    simpa only [show 8*(k/2)+4=4*k by omega,← he] using hx

theorem Words.vector {m : Mem} {p : Addr} (h : Words m p)
    {k e : Nat} (hk : k+4≤1024) (he : e<4) :
    vword (m.read (p+BitVec.ofNat 64 (4*k)) 16) e=BitVec.ofNat 32 expandedVals[k+e]! := by
  rw [VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,
    BitVec.add_assoc,← BitVec.ofNat_add,← Nat.mul_add]
  exact h _ (by omega)

/-- A pair of SIMD loads selects a root and its reciprocal from one row. -/
theorem Words.row {m : Mem} {p : Addr} (h : Words m p)
    {u off g e root : Nat} (ho : off%4=0) (he : e<4)
    (hb : 480*u+off+32*g+32≤4096)
    (hv : expandedVals[120*u+off/4+8*g+e]! = z root ∧
      expandedVals[120*u+off/4+8*g+e+4]! = bar (z root)) :
    vword (m.read (p+BitVec.ofNat 64 (480*u+off+32*g)) 16) e=BitVec.ofNat 32 (z root) ∧
    vword (m.read (p+BitVec.ofNat 64 (480*u+off+32*g+16)) 16) e=BitVec.ofNat 32 (bar (z root)) := by
  have h0 : 480*u+off+32*g=4*(120*u+off/4+8*g) := by omega
  have h1 : 480*u+off+32*g+16=4*(120*u+off/4+8*g+4) := by omega
  constructor
  · rw [h0,h.vector (by omega) he,hv.1]
  · rw [h1,h.vector (by omega) he]
    rw [show 120*u+off/4+8*g+4+e=120*u+off/4+8*g+e+4 by omega,hv.2]

end VG.Proof.MlDsa.AArch64.Optimized.PairedTable
