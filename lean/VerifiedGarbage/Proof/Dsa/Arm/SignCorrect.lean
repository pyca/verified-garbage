module

public import VerifiedGarbage.Proof.Dsa.Arm.Env
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Dispatch
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA on 32-bit ARM: signing is correct

`sign_correct`: from `signArm`'s precondition, `vg_dsa_sign` returns the
status of `Spec.Dsa.signBytes` and writes its signature (or zeros), and
restores the registers the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32)
open VG.Proof.X25519.Arm (Rest)

theorem qWidth_of_shape {P Q : Nat} (h : shapeValid P Q) : qWidth Q = Spec.Dsa.bitLength Q / 8 := by
  have S := h.1
  unfold Spec.Dsa.supportedSizes at S
  unfold qWidth
  rcases S with ⟨_, h₁⟩ | ⟨_, h₁ | h₁ | h₁⟩ | ⟨_, h₁⟩ <;> simp [h₁]

theorem shape_bounds {P Q : Nat} (h : shapeValid P Q) : 1 < P ∧ P % 2 = 1 ∧ 255 < Q ∧ Q % 2 = 1 := by
  have B := VG.Proof.Dsa.supported_bounds h.1
  exact ⟨B.1, h.2.2, B.2.1, h.2.1⟩

theorem width_of {pLen qLen : Nat} (h : Spec.Dsa.lengthsValid pLen qLen) :
    Width pLen ((pLen + 7) / 8) ∧ Width qLen ((qLen + 7) / 8) ∧ qLen ≤ pLen ∧ qLen ≤ 32 ∧ 0 < qLen ∧
      128 ≤ pLen := by
  unfold Spec.Dsa.lengthsValid at h
  refine ⟨⟨rfl, by omega, by omega, by omega⟩, ⟨rfl, by omega, by omega, by omega⟩, by omega, by omega, by omega,
    by omega⟩

theorem widths_mem {pLen qLen : Nat} (h : Spec.Dsa.lengthsValid pLen qLen) :
    (pLen, qLen) ∈ [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)] := by
  unfold Spec.Dsa.lengthsValid at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem signFields_ok (s : State) : FieldsOk (signFields s) := by
  intro f hf
  simp only [signFields, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sum_ofNat (K : BitVec 32) (xs : List (BitVec 32)) :
    xs.foldl (· + ·) K = K + BitVec.ofNat 32 (xs.map BitVec.toNat).sum := by
  induction xs generalizing K with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem signKey (m : Mem) (A : Addr) {pLen qLen total : Nat} (h : 3 * pLen + 2 * qLen ≤ total) :
    Spec.Dsa.privateKeyBytes pLen qLen (Spec.Rsa.bytesAt m A total) =
      ⟨⟨Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m A pLen),
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (A + BitVec.ofNat 64 pLen) qLen),
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (A + BitVec.ofNat 64 (pLen + qLen)) pLen)⟩,
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (A + BitVec.ofNat 64 (2 * pLen + qLen)) pLen),
        some (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (A + BitVec.ofNat 64 (3 * pLen + qLen)) qLen))⟩ := by
  rw [VG.Proof.Dsa.privateKeyBytes_at m A h, VG.Proof.Dsa.publicKeyBytes_at m A (by omega)]

/-- A signing attempt, by the checks and values the body computes. -/
theorem signBytes_eq {pLen qLen P Q G Y X K : Nat} {key nonce digest : List Byte}
    (hv : Spec.Dsa.lengthsValid pLen qLen) (valid : shapeValid P Q)
    (hk : key.length = 3 * pLen + 2 * qLen) (hn : nonce.length = qLen)
    (kv : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨P, Q, G⟩, Y, some X⟩) (nv : Spec.Dsa.decodeBE nonce = K) :
    Spec.Dsa.signBytes pLen qLen key nonce digest =
      if signChecks P Q G Y X K (Spec.Dsa.decodeBE (digest.take (Spec.Dsa.bitLength Q / 8))) then
        some (Spec.Dsa.encodeBE qLen (rValue P Q G K) ++
          Spec.Dsa.encodeBE qLen (sValue P Q G X K (Spec.Dsa.decodeBE (digest.take (Spec.Dsa.bitLength Q / 8)))))
      else none := by
  rw [VG.Proof.Dsa.signBytes_compute hv valid hk hn kv nv (VG.Proof.Dsa.shape_digest_width valid).1]
  simp only [signChecks, rValue, sValue, and_assoc]

/-- The status word of a result in `r0`. -/
theorem status_toNat {u : State} {b : Prop} [Decidable b] (h : u.gpr .r0 = if b then 1 else 0) :
    (BitVec.setWidth 32 (u.gpr .r1 ++ u.gpr .r0)).toNat = if b then 1 else 0 := by
  rw [BitVec.setWidth_append_eq_right, h]
  by_cases hb : b <;> simp [hb]

/-- The key's components, at a state with the environment of signing. -/
theorem signKeyIn {s t : State} {base : Addr} {size : Nat} (h : signPre s) (hb : State.addr (arg s 5) = base)
    (hsz : (arg s 6).toNat * 8 = size) (E : Env s base size (signFields s) t) :
    Input t base size (.input .p) (arg s 0).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (arg s 0).toNat)) ∧
      Input t base size (.input .q) (arg s 2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat)
          (arg s 2).toNat)) ∧
      Input t base size (.input .g) (arg s 0).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r2) + BitVec.ofNat 64 ((arg s 0).toNat + (arg s 2).toNat)) (arg s 0).toNat)) ∧
      Input t base size (.input .y) (arg s 0).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r2) + BitVec.ofNat 64 (2 * (arg s 0).toNat + (arg s 2).toNat)) (arg s 0).toNat)) ∧
      Input t base size (.input .x) (arg s 2).toNat
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r2) + BitVec.ofNat 64 (3 * (arg s 0).toNat + (arg s 2).toNat)) (arg s 2).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, _, _, _, _, _, dKS, _, _, _, _, fK, _, _, _, hv, _, hr3, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 4960 ≤ (arg s 6).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  have kr : (⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have ip := input_of E (p := .input .p) (by decide : Impl.Dsa.Layout.Field.p ≠ .mask) (o := 0)
    (len := (arg s 0).toNat) (by rw [BitVec.add_zero]; exact E.field (d := 64) (v := s.gpr .r2) (by simp))
    kr fK (by omega) (.inr rfl) dKS hz
  rw [BitVec.add_zero] at ip
  have cg := fun {a : Nat} {xs : List (BitVec 32)} (h : (xs.map BitVec.toNat).sum = a) =>
    (sum_ofNat (s.gpr .r2) xs).trans (congrArg (fun n => s.gpr .r2 + BitVec.ofNat 32 n) h)
  refine ⟨ip, input_of E (p := .input .q) (by decide : Impl.Dsa.Layout.Field.q ≠ .mask) ?_ kr fK (by omega)
      (.inl (by omega)) dKS hz,
    input_of E (p := .input .g) (by decide : Impl.Dsa.Layout.Field.g ≠ .mask) ?_ kr fK (by omega)
      (.inl (by omega)) dKS hz,
    input_of E (p := .input .y) (by decide : Impl.Dsa.Layout.Field.y ≠ .mask) ?_ kr fK (by omega)
      (.inl (by omega)) dKS hz,
    input_of E (p := .input .x) (by decide : Impl.Dsa.Layout.Field.x ≠ .mask) ?_ kr fK (by omega)
      (.inl (by omega)) dKS hz⟩
  · exact (E.field (d := 68) (v := s.gpr .r2 + arg s 0) (by simp)).trans (cg (xs := [arg s 0]) (by simp))
  · exact (E.field (d := 72) (v := s.gpr .r2 + arg s 0 + arg s 2) (by simp)).trans
      (cg (xs := [arg s 0, arg s 2]) (by simp))
  · exact (E.field (d := 76) (v := s.gpr .r2 + arg s 0 + arg s 2 + arg s 0) (by simp)).trans
      (cg (xs := [arg s 0, arg s 2, arg s 0]) (by simp; omega))
  · exact (E.field (d := 80) (v := s.gpr .r2 + arg s 0 + arg s 2 + arg s 0 + arg s 0) (by simp)).trans
      (cg (xs := [arg s 0, arg s 2, arg s 0, arg s 0]) (by simp; omega))

theorem signNonceIn {s t : State} {base : Addr} {size : Nat} (h : signPre s) (hb : State.addr (arg s 5) = base)
    (hsz : (arg s 6).toNat * 8 = size) (E : Env s base size (signFields s) t) :
    Input t base size (.input .nonce) (arg s 2).toNat
      (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, _, _, _, _, _, _, dNS, _, _, _, _, fN, _, _, hv, _, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 4960 ≤ (arg s 6).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  have nr : (⟨State.addr (arg s 1), (arg s 2).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have In := input_of E (p := .input .nonce) (by decide : Impl.Dsa.Layout.Field.nonce ≠ .mask) (o := 0)
    (len := (arg s 2).toNat) (by rw [BitVec.add_zero]; exact E.field (d := 88) (v := arg s 1) (by simp))
    nr fN (by omega) (.inr rfl) dNS hz
  rwa [BitVec.add_zero] at In

theorem signDigestIn {s t : State} {base : Addr} {size : Nat} (h : signPre s) (hb : State.addr (arg s 5) = base)
    (hsz : (arg s 6).toNat * 8 = size) (E : Env s base size (signFields s) t) {c : Nat}
    (hc : c ≤ (arg s 4).toNat) :
    Input t base size (.input .digest) c
      (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (arg s 3)) c)) := by
  subst hb hsz
  obtain ⟨_, hrd, _, _, _, _, _, _, _, _, dDS, _, _, _, _, fD, _, hv, _, _, hsw⟩ := h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hz : 4960 ≤ (arg s 6).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  have dr : (⟨State.addr (arg s 3), (arg s 4).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  have Id := input_of E (p := .input .digest) (by decide : Impl.Dsa.Layout.Field.digest ≠ .mask) (o := 0)
    (len := c) (by rw [BitVec.add_zero]; exact E.field (d := 92) (v := arg s 3) (by simp))
    dr fD (by omega) (.inr rfl) dDS hz
  rwa [BitVec.add_zero] at Id

theorem signOutput {s t : State} {base : Addr} {size : Nat} (h : signPre s) (hb : State.addr (arg s 5) = base)
    (hsz : (arg s 6).toNat * 8 = size) (E : Env s base size (signFields s) t) :
    Output t base size (2 * (arg s 2).toNat) := by
  subst hb hsz
  obtain ⟨_, _, hwr, _, _, _, dOS, _, _, _, _, _, fO, _, _, _, _, _, hr1, _, _⟩ := h
  have po : pointerValue (State.addr (arg s 5)) t (.input .out) = s.gpr .r0 :=
    E.field (d := 96) (v := s.gpr .r0) (by simp)
  refine ⟨by rw [po]; omega, fun e k hek => ?_, by rw [po, ← hr1]; exact dOS⟩
  rw [po, E.wr, hwr]
  exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem sign_correct {s : State} (h : signPre s) :
    WP isa (Entry.operation true) s fun t => abiPreserved s t ∧ signArm.post s t := by
  obtain ⟨hsp, hrd, hwr, _, _, _, dOS, _, dKS, dNS, dDS, _, fO, fK, fN, fD, fS, hv, hr1, hr3, hsw⟩ := id h
  have v := hv
  unfold Spec.Dsa.lengthsValid at v
  have hs16 : 128 * (arg s 0).toNat ≤ (arg s 6).toNat * 8 := by unfold Spec.Dsa.scratchWords at hsw; omega
  obtain ⟨wp, wq, qp, q32, q0, p128⟩ := width_of hv
  simp only [Entry.operation, Core.sequence, List.foldr, ↓reduceIte]
  refine WP.seq (WP.mono (signEntry_ok h) fun u I => ?_)
  have E₀ := Env.of_installed I (by omega)
  have fok := signFields_ok s
  refine WP.seq (widthDispatch_ok true _ E₀.ws (by omega) (widths_mem hv) (by decide)
    (by rw [E₀.field (d := 100) (v := arg s 0) (by simp)]) (by rw [E₀.field (d := 104) (v := arg s 2) (by simp)]) fun t₁ R₁ M₁ => ?_)
  have E₁ := E₀.of_mem R₁ (by decide) M₁
  have hz : 4960 ≤ (arg s 6).toNat * 8 := by omega
  have kr : (⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  obtain ⟨Ip₁, Iq₁, -, -, -⟩ := signKeyIn h rfl rfl E₁
  refine sized_ok true E₁.ws hz wp wq Ip₁.toReady Iq₁.toReady Ip₁.value Iq₁.value ?_ ?_
  · intro t₂ nv R₂ O₂
    have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
      simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega)
    have po : pointerValue (State.addr (arg s 5)) t₂ (.input .out) = s.gpr .r0 :=
      E₂.field (d := 96) (v := s.gpr .r0) (by simp)
    refine WP.mono (failure_ok E₂.ws (by omega) (signOutput h rfl rfl E₂) (by rw [E₂.field (d := 104) (v := arg s 2) (by simp)])
      q0 q32) fun t₃ ⟨Z₃, B₃, R₃, O₃⟩ => ?_
    rw [po] at B₃ O₃
    have none : signRes s = none :=
      VG.Proof.Dsa.signBytes_invalid_shape (by rw [signKey _ _ (by omega)]; exact nv)
    refine finish_ok (E₂.ws.of_rest R₃ (by decide)) (by omega) (E₂.saved_outside O₃ (hr1 ▸ dOS) (by omega))
      (R₃.sp.trans E₂.sp) fun u A r0 M => ⟨A, ?_, ?_⟩
    · rw [BitVec.setWidth_append_eq_right, r0, Z₃, none]; rfl
    · rw [M, hr1, B₃, none]; rfl
  · intro t₂ valid hm D₂ R₂ O₂
    have E₂ := E₁.keep fok R₂ (by decide) O₂ (fun r hr => by
      simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega)
    have po : pointerValue (State.addr (arg s 5)) t₂ (.input .out) = s.gpr .r0 :=
      E₂.field (d := 96) (v := s.gpr .r0) (by simp)
    obtain ⟨Ip, Iq, Ig, Iy, Ix⟩ := signKeyIn h rfl rfl E₂
    have In := signNonceIn h rfl rfl E₂
    have Id := signDigestIn h rfl rfl E₂ (Nat.min_le_left (arg s 4).toNat (qWidth (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
        (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat) (arg s 2).toNat))))
    have hc : countValue (State.addr (arg s 5)) t₂ Core.digestPrefix = min (arg s 4).toNat (qWidth
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
          (State.addr (s.gpr .r2) + BitVec.ofNat 64 (arg s 0).toNat) (arg s 2).toNat))) := by
      refine D₂.trans ?_
      rw [E₁.field (d := 108) (v := arg s 4) (by simp)]
    rw [VG.Proof.Dsa.bytesAt_prefix, qWidth_of_shape valid] at Id
    rw [qWidth_of_shape valid] at hc
    obtain ⟨hP, hPo, hQ, hQo⟩ := shape_bounds valid
    refine WP.mono (signBody_ok ⟨E₂.ws, by omega, wp, wq, qp, q32⟩ Ip Iq Ig Iy Ix In Id hc hP hPo hQ hQo hm
      (signOutput h rfl rfl E₂)) fun t₃ ⟨Z₃, B₃, Bd₃⟩ => ?_
    rw [po] at B₃ Bd₃
    have SR : signRes s = _ := signBytes_eq (nonce := Spec.Rsa.bytesAt s.mem (State.addr (arg s 1)) (arg s 2).toNat) (digest := Spec.Rsa.bytesAt s.mem (State.addr (arg s 3)) (arg s 4).toNat) hv valid
      (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; exact hr3)
      (by simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]) (signKey _ _ (by omega)) rfl
    refine finish_ok (E₂.ws.of_rest Bd₃.rest (by decide)) (by omega) (E₂.saved_body Bd₃ (hr1 ▸ dOS) (by omega))
      (Bd₃.rest.sp.trans E₂.sp) fun u A r0 M => ⟨A, ?_, ?_⟩
    · rw [BitVec.setWidth_append_eq_right, r0, Z₃, SR]
      split <;> rfl
    · rw [M, hr1, B₃, SR]
      split <;> rfl

end VG.Proof.Dsa.Arm
