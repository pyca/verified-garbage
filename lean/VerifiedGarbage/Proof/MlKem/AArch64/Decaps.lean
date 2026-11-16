module
public import VerifiedGarbage.Proof.MlKem.Scrubbed
public import VerifiedGarbage.Proof.MlKem.AArch64.KemB
public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
public import VerifiedGarbage.Proof.MlKem.AArch64.DecapsA

import VerifiedGarbage.Proof.MlKem.AArch64.DecapsCmp
import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.Block

/-!
# ML-KEM on AArch64: what the proofs of `decaps` share

The arguments of K-PKE.Encrypt in `decaps` (`encArgs`), `t̂` decoded from
`dk` (`ekT_eq`), `K̄ = J(z ‖ c)` (`jD`), the buffers of `scratch` apart from
what K-PKE.Encrypt writes (`far_encW`), and a state satisfying the
precondition (`sat`), for the functions of `Kem16/` and `Kem16P/`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Decaps

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

variable {P : KemLay}

theorem encArgs (hP : P.Wf) : EncArgs P (deL P) 0 (384 * P.k) 3 (CB P) :=
  ⟨by decide, by dek, by simp only [deL, List.getD_cons_zero]; lom, by decide, by dek,
    by simp only [deL, List.getD_cons_succ, List.getD_cons_zero]; lom, .inr rfl⟩

theorem drop_take_slice (L : List Byte) {a n b c : Nat} (h : b + c ≤ n) :
    (((L.drop a).take n).drop b).take c = (L.drop (a + b)).take c := by
  rw [slice_take _ h, List.drop_drop]

theorem ekT_eq (s₀ : State) : ∀ j < P.k,
    decode12 (bytesAt s₀.mem (kA s₀ ((deL P).slot 0) + BitVec.ofNat 64 (384 * P.k + 384 * j)) 384) =
      ekT (KPke.dkEk P.params (dkD P s₀)) j := fun j hj => by
  have := mul_succ_le (a := 384) hj
  rw [ekT, KPke.dkEk, drop_take_slice _ (show 384 * j + 384 ≤ 384 * P.params.k + 32 by
      show _ ≤ 384 * P.k + 32; omega_using [hj]), show 384 * P.params.k = 384 * P.k from rfl,
    bytesAt_slice _ _ (show 384 * P.k + 384 * j + 384 ≤ P.dkLen by simp only [KemLay.dkLen]; omega_using [hj])]
  rfl

/-- `K̄ = J(z ‖ c)`. -/
abbrev jD (P : KemLay) (s₀ : State) : List Byte := J (KPke.dkZ P.params (dkD P s₀) ++ cD P s₀)

/-- A buffer of `scratch` below `ŷ` apart from what `K-PKE.Encrypt` writes. -/
theorem far_encW {s₀ : State} (hp : Pre P (deL P) s₀) {o l : Nat} (h1 : 840 ≤ o)
    (h2 : o + l ≤ RB + 32 ∨ RB + 33 ≤ o) (h3 : o + l ≤ PB) :
    ∀ r ∈ encW P (deL P) s₀ 3 (CB P), (R (kA s₀) (deL P).sc o l).Disjoint r := by
  have hw := hp.wf
  have f : o + l ≤ SV P + 48 := by lom
  intro r hr
  rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
  · exact sdisj hp f (by lom) (.inr (by omega_using [h1]))
  · exact sdisj hp f (by lom) (by simp only [RB] at h2 ⊢; omega_using [h2])
  · exact sdisj hp f (by lom) (.inl h3)
  · exact below_R hp hp.scb (hp.fs f)
  · exact sdisj hp f (by lom) (.inl (by lom))

/-! ## ML-KEM-768 -/

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x10000 | _ => 0
  sp := 0x100000
  mem _ := 0
  rd := [⟨0x1000, 2400⟩, ⟨0x2000, 1088⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 32768⟩]

end VG.Proof.MlKem.AArch64.Decaps
