module
public import VerifiedGarbage.Proof.Dsa.Arm.Env

import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.PackedBytes

/-!
# DSA on 32-bit ARM: verification is correct

`verify_correct`: from `verifyArm`'s precondition, `vg_dsa_verify` returns
whether `Spec.Dsa.verifyBytes` accepts, and restores the registers the ABI
preserves.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem verifyFields_ok (s : State) : FieldsOk (verifyFields s) := by
  intro f hf
  simp only [verifyFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem verifyKey (m : Mem) (A : Addr) {pLen qLen total : Nat} (h : 3 * pLen + qLen ≤ total) :
    Spec.Dsa.publicKeyBytes pLen qLen (Spec.Rsa.bytesAt m A total) =
      ⟨⟨Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m A pLen),
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (A + BitVec.ofNat 64 pLen) qLen),
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (A + BitVec.ofNat 64 (pLen + qLen)) pLen)⟩,
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (A + BitVec.ofNat 64 (2 * pLen + qLen)) pLen), none⟩ :=
  VG.Proof.Dsa.publicKeyBytes_at m A h

/-- A verification, by the checks the body computes. -/
theorem verifyBytes_eq {pLen qLen P Q G Y : Nat} {key : List Byte} (m : Mem) (A : Addr) (digest : List Byte)
    (hv : Spec.Dsa.lengthsValid pLen qLen) (valid : shapeValid P Q)
    (hk : key.length = 3 * pLen + qLen)
    (kv : Spec.Dsa.publicKeyBytes pLen qLen key = ⟨⟨P, Q, G⟩, Y, none⟩) :
    Spec.Dsa.verifyBytes pLen qLen key (Spec.Rsa.bytesAt m A (2 * qLen)) digest =
      decide (verifyChecks P Q G Y (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m A qLen))
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (A + BitVec.ofNat 64 qLen) qLen))
        (Spec.Dsa.decodeBE (digest.take (Spec.Dsa.bitLength Q / 8)))) := by
  have r := VG.Proof.Dsa.bytesAt_slice m A (offset := 0) (len := qLen) (total := 2 * qLen) (by omega_arith)
  have s' := VG.Proof.Dsa.bytesAt_slice m A (offset := qLen) (len := qLen) (total := 2 * qLen) (by omega_arith)
  rw [List.drop_zero, BitVec.add_zero] at r
  rw [List.take_of_length_le (by simp [Spec.Rsa.bytesAt]; omega_arith)] at s'
  rw [VG.Proof.Dsa.verifyBytes_compute hv valid hk (by simp [Spec.Rsa.bytesAt]) kv (congrArg _ r)
    (congrArg _ s') (VG.Proof.Dsa.shape_digest_width valid).1]

/-- The key's components, at a state with the environment of verification. -/
theorem verifyKeyIn {s t : State} {base : Addr} {size : Nat} (h : verifyPre s) (hb : State.addr (arg s 4) = base)
    (hsz : (arg s 5).toNat * 8 = size) (E : Env s base size (verifyFields s) t) :
    Input t base size (.input .p) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat)) ∧
      Input t base size (.input .q) (s.gpr .r3).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
          (s.gpr .r3).toNat)) ∧
      Input t base size (.input .g) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)) ∧
      Input t base size (.input .y) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 (2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat))
          (s.gpr .r2).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, dKS, _, _, _, fK, _, _, _, hv, hr1, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 4960 ≤ (arg s 5).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have kr : (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have ip := input_of E (p := .input .p) (by decide : Impl.Dsa.Layout.Field.p ≠ .mask) (o := 0)
    (len := (s.gpr .r2).toNat)
    (by rw [BitVec.add_zero]; exact E.field (d := 64) (v := s.gpr .r0) (by simp)) kr fK (by omega_arith) (.inr rfl) dKS hz
  rw [BitVec.add_zero] at ip
  have cg := fun {a : Nat} {xs : List (BitVec 32)} (h : (xs.map BitVec.toNat).sum = a) =>
    (sum_ofNat (s.gpr .r0) xs).trans (congrArg (fun n => s.gpr .r0 + BitVec.ofNat 32 n) h)
  refine ⟨ip, input_of E (p := .input .q) (by decide : Impl.Dsa.Layout.Field.q ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz,
    input_of E (p := .input .g) (by decide : Impl.Dsa.Layout.Field.g ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz,
    input_of E (p := .input .y) (by decide : Impl.Dsa.Layout.Field.y ≠ .mask) ?_ kr fK (by omega_arith)
      (.inl (by omega_arith)) dKS hz⟩
  · exact (E.field (d := 68) (v := s.gpr .r0 + s.gpr .r2) (by simp)).trans
      (cg (xs := [s.gpr .r2]) (by simp))
  · exact (E.field (d := 72) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3) (by simp)).trans
      (cg (xs := [s.gpr .r2, s.gpr .r3]) (by simp))
  · exact (E.field (d := 76) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2) (by simp)).trans
      (cg (xs := [s.gpr .r2, s.gpr .r3, s.gpr .r2]) (by simp; omega_arith))

theorem verifySigIn {s t : State} {base : Addr} {size : Nat} (h : verifyPre s) (hb : State.addr (arg s 4) = base)
    (hsz : (arg s 5).toNat * 8 = size) (E : Env s base size (verifyFields s) t) :
    Input t base size (.input .signature) (s.gpr .r3).toNat
      (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 0)) (s.gpr .r3).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, _, dSS, _, _, _, fS, _, _, hv, _, hs1, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 4960 ≤ (arg s 5).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have sr : (⟨State.addr (arg s 0), (arg s 1).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have Ir := input_of E (p := .input .signature) (by decide : Impl.Dsa.Layout.Field.signature ≠ .mask) (o := 0)
    (len := (s.gpr .r3).toNat) (by rw [BitVec.add_zero]; exact E.field (d := 84) (v := arg s 0) (by simp))
    sr fS (by omega_arith) (.inr rfl) dSS hz
  rwa [BitVec.add_zero] at Ir

theorem verifySigSIn {s t : State} {base : Addr} {size : Nat} (h : verifyPre s) (hb : State.addr (arg s 4) = base)
    (hsz : (arg s 5).toNat * 8 = size) (E : Env s base size (verifyFields s) t) :
    Input t base size .signatureS (s.gpr .r3).toNat
      (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 0) + BitVec.ofNat 64 (s.gpr .r3).toNat)
        (s.gpr .r3).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, _, dSS, _, _, _, fS, _, _, hv, _, hs1, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 4960 ≤ (arg s 5).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have sr : (⟨State.addr (arg s 0), (arg s 1).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  exact input_of E (p := .signatureS) trivial (o := (s.gpr .r3).toNat) (len := (s.gpr .r3).toNat)
    (by
      show hdr (State.addr (arg s 4)) t 84 + hdr (State.addr (arg s 4)) t 104 = _
      rw [E.field (d := 84) (v := arg s 0) (by simp), E.field (d := 104) (v := s.gpr .r3) (by simp),
        BitVec.ofNat_toNat, BitVec.setWidth_eq])
    sr fS (by omega_arith) (.inl (by omega_arith)) dSS hz

theorem verifyDigestIn {s t : State} {base : Addr} {size : Nat} (h : verifyPre s) (hb : State.addr (arg s 4) = base)
    (hsz : (arg s 5).toNat * 8 = size) (E : Env s base size (verifyFields s) t) {c : Nat}
    (hc : c ≤ (arg s 3).toNat) :
    Input t base size (.input .digest) c
      (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 2)) c)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, _, _, dDS, _, _, _, fD, _, hv, _, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 4960 ≤ (arg s 5).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega_arith
  have dr : (⟨State.addr (arg s 2), (arg s 3).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have Id := input_of E (p := .input .digest) (by decide : Impl.Dsa.Layout.Field.digest ≠ .mask) (o := 0)
    (len := c) (by rw [BitVec.add_zero]; exact E.field (d := 92) (v := arg s 2) (by simp))
    dr fD (by omega_arith) (.inr rfl) dDS hz
  rwa [BitVec.add_zero] at Id

end VG.Proof.Dsa.Arm
