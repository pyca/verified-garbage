module

public import VerifiedGarbage.Proof.MillerRabin.X86.WorkspaceFrame
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Mont.X86.Compact.Prepared
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic

/-! # Read-only full-width modulus metadata across prepared i686 rounds -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.Mont (wordAt wOf numAt arrWord)

structure Modulus (g : Geometry) (c : Nat) (m : Mem) : Prop where
  width : wOf m g.W = g.w
  pointers : ∀ j < 8, wordAt m g.W (arrWord j) = g.W + BitVec.ofNat 64 (g.array j)
  candidate : val32 m g.W (g.array 0) g.words = c
  inverse : ((m.readW (off g.W (g.array 0)) 64).toNat * (wordAt m g.W 7).toNat + 1) % 2 ^ 64 = 0

theorem Modulus.layout {g : Geometry} (v : g.Valid) {c : Nat} {m : Mem} (M : Modulus g c m)
    (aligned : g.L % 8 = 0) : VG.Proof.Rsa.Mont.Layout m g.W (g.L / 8) := by
  rw [VG.Proof.Rsa.Mont.Layout, M.width]
  refine ⟨by have := v.minWidth; omega, by have := v.maxWidth; omega, ?_, M.pointers⟩
  have fit := v.arrayFit (j := 7) (by decide)
  have all := v.arraysFit
  have order := Nat.mul_le_mul_right (8 * (g.w + 2)) (show 8 ≤ 28 by decide)
  have alignedL := Nat.mod_add_div g.L 8
  unfold VG.Proof.Rsa.Mont.arrAt VG.Proof.Rsa.Mont.hdrBytes at *
  omega

theorem Modulus.keep {g : Geometry} (v : g.Valid) {c : Nat} {m m' : Mem}
    (M : Modulus g c m) {rs : List (Nat × Nat)} (O : WorkspaceFrame g rs m m')
    (header : ∀ r ∈ rs, 128 ≤ r.1 ∨ r.1 + r.2 ≤ 48)
    (candidate : ∀ r ∈ rs, g.array 0 + 4 * g.words ≤ r.1 ∨ r.1 + r.2 ≤ g.array 0) :
    Modulus g c m' := by
  have fit := v.headerFit
  have hread {d : Nat} (lo : 48 ≤ d) (hi : d + 8 ≤ 128) :
      m'.readW (off g.W d) 64 = m.readW (off g.W d) 64 :=
    O.read64 (by omega) (fun r hr => by have := header r hr; omega)
  have modFit := v.arrayFit (j := 0) (by decide)
  refine ⟨?_, ?_, (O.val32 modFit candidate).trans M.candidate, ?_⟩
  · change (m'.readW (off g.W 48) 64).toNat = g.w
    rw [hread (by decide) (by decide)]
    exact M.width
  · intro j index
    change m'.readW (off g.W (8 * arrWord j)) 64 = _
    rw [hread (by unfold arrWord; omega) (by unfold arrWord; omega)]
    exact M.pointers j index
  · rw [O.read64 (by have := v.minWidth; unfold Geometry.words at modFit; omega)
      (fun r hr => by have := candidate r hr; have := v.minWidth; unfold Geometry.words at *; omega)]
    change (_ * (m'.readW (off g.W 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [hread (by decide) (by decide)]
    exact M.inverse

end VG.Proof.MillerRabin.X86
