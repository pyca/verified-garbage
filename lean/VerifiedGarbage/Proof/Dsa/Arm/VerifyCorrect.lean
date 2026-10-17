module

public import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega

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
  have r := VG.Proof.Dsa.bytesAt_slice m A (offset := 0) (len := qLen) (total := 2 * qLen) (by omega)
  have s' := VG.Proof.Dsa.bytesAt_slice m A (offset := qLen) (len := qLen) (total := 2 * qLen) (by omega)
  rw [List.drop_zero, BitVec.add_zero] at r
  rw [List.take_of_length_le (by simp [Spec.Rsa.bytesAt]; omega)] at s'
  rw [VG.Proof.Dsa.verifyBytes_compute hv valid hk (by simp [Spec.Rsa.bytesAt]) kv (congrArg _ r)
    (congrArg _ s') (VG.Proof.Dsa.shape_digest_width valid).1]

theorem verify_correct {s : State} (h : verifyPre s) :
    WP isa (Entry.operation false) s fun t => abiPreserved s t ∧ verifyArm.post s t := by
  obtain ⟨hsp, hrd, hwr, dKS, dSS, dDS, _, fK, fS, fD, fW, hv, hr1, hs1, hsw⟩ := id h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (s.gpr .r2).toNat ≤ (arg s 5).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  simp only [Entry.operation, Core.sequence, List.foldr, Bool.false_eq_true, ↓reduceIte]
  refine WP.seq (WP.mono (verifyEntry_ok h) fun u I => ?_)
  have E₀ := Env.of_installed I (by omega)
  have fok := verifyFields_ok s
  refine WP.seq (widthDispatch_ok false _ E₀.ws (by omega) (widths_mem hv) (by decide)
    (by rw [E₀.field (d := 100) (v := s.gpr .r2) (by simp)]) (by rw [E₀.field (d := 104) (v := s.gpr .r3) (by simp)])
    fun t₁ R₁ M₁ => ?_)
  have E₁ := E₀.of_mem R₁ (by decide) M₁
  have hz : 4960 ≤ (arg s 5).toNat * 8 := by omega
  have kr : (⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have keyIn : ∀ {t} (E : Env s (State.addr (arg s 4)) ((arg s 5).toNat * 8) (verifyFields s) t),
      Input t (State.addr (arg s 4)) ((arg s 5).toNat * 8) (.input .p) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat)) ∧
      Input t (State.addr (arg s 4)) ((arg s 5).toNat * 8) (.input .q) (s.gpr .r3).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat)
          (s.gpr .r3).toNat)) ∧
      Input t (State.addr (arg s 4)) ((arg s 5).toNat * 8) (.input .g) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 ((s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)) ∧
      Input t (State.addr (arg s 4)) ((arg s 5).toNat * 8) (.input .y) (s.gpr .r2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 (2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat)) (s.gpr .r2).toNat)) := by
    intro t E
    have ip := input_of E (p := .input .p) (by decide : Impl.Dsa.Layout.Field.p ≠ .mask) (o := 0)
      (len := (s.gpr .r2).toNat)
      (by rw [BitVec.add_zero]; exact E.field (d := 64) (v := s.gpr .r0) (by simp)) kr fK (by omega) (.inr rfl) dKS hz
    rw [BitVec.add_zero] at ip
    have cg := fun {a : Nat} {xs : List (BitVec 32)} (h : (xs.map BitVec.toNat).sum = a) =>
      (sum_ofNat (s.gpr .r0) xs).trans (congrArg (fun n => s.gpr .r0 + BitVec.ofNat 32 n) h)
    refine ⟨ip, input_of E (p := .input .q) (by decide : Impl.Dsa.Layout.Field.q ≠ .mask) ?_ kr fK (by omega)
        (.inl (by omega)) dKS hz,
      input_of E (p := .input .g) (by decide : Impl.Dsa.Layout.Field.g ≠ .mask) ?_ kr fK (by omega)
        (.inl (by omega)) dKS hz,
      input_of E (p := .input .y) (by decide : Impl.Dsa.Layout.Field.y ≠ .mask) ?_ kr fK (by omega)
        (.inl (by omega)) dKS hz⟩
    · exact (E.field (d := 68) (v := s.gpr .r0 + s.gpr .r2) (by simp)).trans
        (cg (xs := [s.gpr .r2]) (by simp))
    · exact (E.field (d := 72) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3) (by simp)).trans
        (cg (xs := [s.gpr .r2, s.gpr .r3]) (by simp))
    · exact (E.field (d := 76) (v := s.gpr .r0 + s.gpr .r2 + s.gpr .r3 + s.gpr .r2) (by simp)).trans
        (cg (xs := [s.gpr .r2, s.gpr .r3, s.gpr .r2]) (by simp; omega))
  obtain ⟨Ip₁, Iq₁, -, -⟩ := keyIn E₁
  refine sized_ok false E₁.ws hz wp wq Ip₁.toReady Iq₁.toReady Ip₁.value Iq₁.value ?_ ?_
  · intro t₂ nv R₂ O₂
    have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
      simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega)
    have rej : verifyRes s = false :=
      VG.Proof.Dsa.verifyBytes_invalid_shape (by rw [verifyKey _ _ (by omega)]; exact nv)
    simp only [Entry.failure, Bool.false_eq_true, ↓reduceIte]
    refine wp_mov (op2_imm (by decide)) fun t₃ v₃ => WP.block_nil ?_
    refine finish_ok (E₂.ws.of_upd v₃ (by decide)) (by omega) (fun i hi => by rw [v₃.mem]; exact E₂.saved i hi)
      (v₃.sp.trans E₂.sp) fun u A r0 M => ⟨A, ?_⟩
    show (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = _
    rw [BitVec.setWidth_append_eq_right, r0, v₃.gpr, rej]
    rfl
  · intro t₂ valid hm D₂ R₂ O₂
    have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
      simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega)
    obtain ⟨Ip, Iq, Ig, Iy⟩ := keyIn E₂
    have sr : (⟨State.addr (arg s 0), (arg s 1).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
    have dr : (⟨State.addr (arg s 2), (arg s 3).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
    have Ir := input_of E₂ (p := .input .signature) (by decide : Impl.Dsa.Layout.Field.signature ≠ .mask) (o := 0)
      (len := (s.gpr .r3).toNat) (by rw [BitVec.add_zero]; exact E₂.field (d := 84) (v := arg s 0) (by simp))
      sr fS (by omega) (.inr rfl) dSS hz
    rw [BitVec.add_zero] at Ir
    have Is := input_of E₂ (p := .signatureS) trivial (o := (s.gpr .r3).toNat) (len := (s.gpr .r3).toNat)
      (by
        show hdr (State.addr (arg s 4)) t₂ 84 + hdr (State.addr (arg s 4)) t₂ 104 = _
        rw [E₂.field (d := 84) (v := arg s 0) (by simp), E₂.field (d := 104) (v := s.gpr .r3) (by simp),
          BitVec.ofNat_toNat, BitVec.setWidth_eq])
      sr fS (by omega) (.inl (by omega)) dSS hz
    have Id := input_of E₂ (p := .input .digest) (by decide : Impl.Dsa.Layout.Field.digest ≠ .mask) (o := 0)
      (len := min (arg s 3).toNat (qWidth (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
        (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat) (s.gpr .r3).toNat))))
      (by rw [BitVec.add_zero]; exact E₂.field (d := 92) (v := arg s 2) (by simp))
      dr fD (by omega) (.inr rfl) dDS hz
    have hc : countValue (State.addr (arg s 4)) t₂ Core.digestPrefix = min (arg s 3).toNat (qWidth
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r0) + BitVec.ofNat 64 (s.gpr .r2).toNat) (s.gpr .r3).toNat))) := by
      refine D₂.trans ?_
      rw [E₁.field (d := 108) (v := arg s 3) (by simp)]
    rw [BitVec.add_zero, VG.Proof.Dsa.bytesAt_prefix, qWidth_of_shape valid] at Id
    rw [qWidth_of_shape valid] at hc
    obtain ⟨hP, hPo, hQ, hQo⟩ := shape_bounds valid
    refine WP.mono (verifyBody_ok ⟨E₂.ws, by omega, wp, wq, qp, q32⟩ Ip Iq Ig Iy Ir Is Id hc hP hPo hQ hQo hm)
      fun t₃ ⟨Z₃, Rn₃⟩ => ?_
    have E₃ := E₂.keep fok Rn₃.rest (by decide) Rn₃.mem (fun r hr => by
      simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega)
    have e := verifyBytes_eq s.mem (State.addr (arg s 0))
        (Spec.Rsa.bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat) hv valid
      (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr1) (verifyKey _ _ (by omega))
    rw [← hs1] at e
    refine finish_ok E₃.ws (by omega) E₃.saved E₃.sp fun u A r0 M => ⟨A, ?_⟩
    show (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = _
    rw [BitVec.setWidth_append_eq_right, r0, Z₃, show verifyRes s = _ from e]
    split <;> simp_all

end VG.Proof.Dsa.Arm
