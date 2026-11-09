module
public import VerifiedGarbage.Impl.X448.PPC64LE
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
public import VerifiedGarbage.Proof.X448.PPC64LE.Limbs
import VerifiedGarbage.Proof.X448.PPC64LE.Pass
public import VerifiedGarbage.Proof.X448.Field

import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Proof.X25519.PPC64LE.Limbs

/-!
# X448 on PPC64LE: field elements in the working space

A field element is 14 words at an offset `o` of the working space at `B`
(X25519's `limb`), for the number `V` and its residue `FS`.
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P Fe)

/-- The number of the element at `o`. -/
def V (m : Mem) (B : Addr) (o : Nat) : Nat := val32 (limb m B o) 14

/-- The element at `o`. -/
def FS (m : Mem) (B : Addr) (o : Nat) : Fe := Proof.X448.toFe (V m B o)

theorem V_lt (m : Mem) (B : Addr) (o : Nat) : V m B o < 2 ^ 224 * 2 ^ 224 := by
  have := val32_lt (f := limb m B o) (n := 14) fun k _ => limb_lt m B o k
  rwa [pow448] at this

/-- The limbs of an element in a frame that does not overlap it. -/
theorem limb_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {B : Addr} {o : Nat}
    (hd : ∀ r ∈ rs, ∀ k < 14, (⟨B + BitVec.ofNat 64 (o + 4 * k), 4⟩ : Region).Disjoint r) :
    ∀ k < 14, limb m' B o k = limb m B o k := fun k hk => wd_frame hf fun r hr => hd r hr k hk

section
variable {b : Addr}

/-- A word the pass has not written yet (the pass writes `[o, o + 4k)`). -/
theorem wd_pass {s0 s : State} (hc : Ctx b s0) {o k d : Nat}
    (hf : Frame [⟨s0.gpr .r6 + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem)
    (hd : d + 4 ≤ o ∨ o + 4 * k ≤ d) (hd' : d + 4 ≤ 4096) (ho : o + 4 * k ≤ 4096) :
    wd s.mem b d = wd s0.mem b d := by
  rw [hc.r6] at hf
  exact wd_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd (by omega_using [hd']) (by omega_using [ho])

end

end VG.Proof.X448.PPC64LE
