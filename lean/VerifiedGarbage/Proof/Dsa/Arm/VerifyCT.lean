module
public import VerifiedGarbage.Proof.Dsa.Arm.KeyTrace
public import VerifiedGarbage.Proof.Dsa.Arm.Env

import VerifiedGarbage.Proof.Dsa.Arm.VerifyCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.OpTrace
import VerifiedGarbage.Proof.Dsa.Arm.ShapeTrace
import VerifiedGarbage.Proof.Dsa.Arm.BodyTrace
import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.PackedBytes

/-!
# DSA on 32-bit ARM: verification is constant time

As signing (`SignCT.lean`): two runs whose public data agree
(`verifyArm.pub`: the arguments, the key and the result) leak the same trace.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.X25519.Arm (Rest eval_eq)
open VG.Proof.Ecdsa.Arm (mask32)

/-- The caller's operands of verification. -/
def verifyIns (pLen qLen c : Nat) : List (Pointer × Nat) :=
  [(.input .p, pLen), (.input .q, qLen), (.input .g, pLen), (.input .y, pLen), (.input .signature, qLen),
    (.signatureS, qLen), (.input .digest, c)]

/-- Their values. -/
def verifyVal (s : State) (c : Nat) : Pointer → Nat
  | .input .p => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat)
  | .input .q => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
      (s.gpr .r3).toNat)
  | .input .g => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)
  | .input .y => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (State.addr (s.gpr .r0) + BitVec.ofNat 64 (2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)
  | .input .signature => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 0)) (s.gpr .r3).toNat)
  | .signatureS => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 0) + BitVec.ofNat 64 (s.gpr .r3).toNat)
      (s.gpr .r3).toNat)
  | .input .digest => Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 2)) c)
  | _ => 0

/-- Their pointers. -/
def verifyPtr (s : State) : Pointer → BitVec 32
  | .input .p => s.gpr .r0
  | .input .q => s.gpr .r0 + s.gpr .r2
  | .input .g => s.gpr .r0 + s.gpr .r2 + s.gpr .r3
  | .input .y => s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2
  | .input .signature => arg s 0
  | .signatureS => arg s 0 + s.gpr .r3
  | .input .digest => arg s 2
  | _ => 0

theorem verifyCtx {s t : State} {base : Addr} {size pLen qLen c : Nat} (h : verifyPre s)
    (hb : State.addr (arg s 4) = base) (hsz : (arg s 5).toNat * 8 = size)
    (E : Env s base size (verifyFields s) t) (hpl : (s.gpr .r2).toNat = pLen) (hql : (s.gpr .r3).toNat = qLen)
    (hc : c ≤ (arg s 3).toNat) :
    Ctx base size pLen qLen ((pLen + 7) / 8) ((qLen + 7) / 8) (verifyIns pLen qLen c) (verifyVal s c) t := by
  have hv := h.2.2.2.2.2.2.2.2.2.2.2.1
  have hsw := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  subst hpl hql
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have big : 15712 < size := by rw [← hsz]; unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨Ip, Iq, Ig, Iy⟩ := verifyKeyIn h hb hsz E
  refine ⟨⟨E.ws, big, wp, wq, qp, q32⟩, fun i hi => ?_⟩
  simp only [verifyIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Ip
  · exact Iq
  · exact Ig
  · exact Iy
  · exact verifySigIn h hb hsz E
  · exact verifySigSIn h hb hsz E
  · exact verifyDigestIn h hb hsz E hc

theorem verifyPtrs {s t : State} {base : Addr} {size pLen qLen c : Nat} (E : Env s base size (verifyFields s) t) :
    ∀ i ∈ verifyIns pLen qLen c, pointerValue base t i.1 = verifyPtr s i.1 := by
  intro i hi
  simp only [verifyIns, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact E.field (d := 64) (v := s.gpr .r0) (by simp)
  · exact E.field (d := 68) (v := s.gpr .r0 + s.gpr .r2) (by simp)
  · exact E.field (d := 72) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3) (by simp)
  · exact E.field (d := 76) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2) (by simp)
  · exact E.field (d := 84) (v := arg s 0) (by simp)
  · show hdr base t 84 + hdr base t 104 = _
    rw [E.field (d := 84) (v := arg s 0) (by simp), E.field (d := 104) (v := s.gpr .r3) (by simp)]
    rfl
  · exact E.field (d := 92) (v := arg s 2) (by simp)

/-- The key's bytes, the same in two runs that leak the same. -/
theorem verify_keyBytes {s₁ s₂ : State} (h₁ : verifyPre s₁) (hl : verifyLeak s₁ = verifyLeak s₂)
    (hr0 : s₁.gpr .r0 = s₂.gpr .r0) (hr1 : s₁.gpr .r1 = s₂.gpr .r1) (hr2 : s₁.gpr .r2 = s₂.gpr .r2)
    (hr3 : s₁.gpr .r3 = s₂.gpr .r3) {o l : Nat} (hol : o + l ≤ 3 * (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat) :
    Spec.Rsa.bytesAt s₁.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 o) l =
      Spec.Rsa.bytesAt s₂.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 o) l := by
  have r1 := h₁.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [verifyLeak, Spec.Dsa.publicBytesLeak] at hl
  rw [← hr0, ← hr1, ← hr2, ← hr3] at hl
  have E := List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h) |>.mp
    (List.append_inj hl (by simp [Spec.Rsa.bytesAt])).1
  rw [← VG.Proof.Dsa.bytesAt_prefix, ← VG.Proof.Dsa.bytesAt_prefix,
    show min (s₁.gpr .r1).toNat (3 * (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat) =
      3 * (s₁.gpr .r2).toNat + (s₁.gpr .r3).toNat by omega] at E
  rw [← VG.Proof.Dsa.bytesAt_slice _ _ hol, ← VG.Proof.Dsa.bytesAt_slice _ _ hol, E]

end VG.Proof.Dsa.Arm
