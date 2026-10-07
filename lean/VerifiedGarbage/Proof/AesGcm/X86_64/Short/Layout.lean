import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Mid

/-!
# AES-GCM's short path on x86-64: what `G` holds

Untrusted: everything here is checked by Lean. `G` (512 bytes) is zeroed,
then the additional data `a` is written after `lead` zero blocks, the text
`c` after the additional data's blocks, and the lengths block last: its
first `M = lead + na + nc + 1` blocks are then `lead` zero blocks, `a` and
`c` each padded with zeros to whole blocks, and the lengths block
(`gLayout`), whatever is written elsewhere (`K`, the data) in between.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)

/-- The bytes of a part of a zeroed buffer. -/
theorem bytesAt_zeros {m : Mem} {G : Addr} {o k N : Nat} (hz : bytesAt m G N = zeros N) (h : o + k ≤ N) :
    bytesAt m (G + BitVec.ofNat 64 o) k = zeros k := by
  have e := congrArg (fun l => (l.drop o).take k) hz
  rw [show N = o + (k + (N - o - k)) by omega, bytesAt_add, bytesAt_add, List.drop_left' (length_bytesAt _ _ _),
    List.take_left' (length_bytesAt _ _ _)] at e
  rw [e]; simp [zeros]

theorem disjG {G : Addr} {o k e j : Nat} (h : o + k ≤ e ∨ e + j ≤ o) (h₁ : o + k ≤ 512) (h₂ : e + j ≤ 512) :
    (⟨G + BitVec.ofNat 64 o, k⟩ : Region).Disjoint ⟨G + BitVec.ofNat 64 e, j⟩ :=
  Offset.disjoint G h (by omega) (by omega)

/-- What `G` holds. -/
theorem gLayout {G : Addr} {lead na nc : Nat} {a c lens : List Byte} {mZ mK mX mL : Mem} {rs : List Region}
    (ha : a.length ≤ 16 * na) (hc : c.length ≤ 16 * nc)
    (hM : 16 * (lead + na + nc + 1) ≤ 512)
    (hZ : bytesAt mZ G 512 = zeros 512)
    (f₁ : Frame rs (writeBytes mZ (G + BitVec.ofNat 64 (16 * lead)) a) mK)
    (hrs : ∀ r ∈ rs, (⟨G, 512⟩ : Region).Disjoint r)
    {rsX : List Region} (fX : Frame rsX mK mX)
    (hX : ∀ r ∈ rsX, r = ⟨G + BitVec.ofNat 64 (16 * (lead + na)), c.length⟩ ∨ (⟨G, 512⟩ : Region).Disjoint r)
    (hXc : bytesAt mX (G + BitVec.ofNat 64 (16 * (lead + na))) c.length = c)
    (f₂ : Frame [⟨G + BitVec.ofNat 64 (16 * (lead + na + nc)), 16⟩] mX mL)
    (hL : bytesAt mL (G + BitVec.ofNat 64 (16 * (lead + na + nc))) 16 = lens) :
    bytesAt mL G (16 * (lead + na + nc + 1)) =
      zeros (16 * lead) ++ a ++ zeros (16 * na - a.length) ++ c ++ zeros (16 * nc - c.length) ++ lens := by
  -- A part of `G` before the lengths block, in `mL` as in `mK` unless it meets `c`'s blocks.
  have kL : ∀ o k, o + k ≤ 16 * (lead + na + nc) → bytesAt mL (G + BitVec.ofNat 64 o) k = bytesAt mX (G + BitVec.ofNat 64 o) k :=
    fun o k h => bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact disjG (.inl h) (by omega) (by omega)) (by omega)
  have kX : ∀ o k, o + k ≤ 512 → (o + k ≤ 16 * (lead + na) ∨ 16 * (lead + na) + c.length ≤ o) →
      bytesAt mX (G + BitVec.ofNat 64 o) k = bytesAt mK (G + BitVec.ofNat 64 o) k := fun o k h h' => by
    refine bytesAt_frame fX (fun r hr => ?_) (by omega)
    rcases hX r hr with rfl | hd
    · exact disjG h' (by omega) (by omega)
    · exact hd.sub_left (Offset.sub_base G h)
  have kK : ∀ o k, o + k ≤ 512 → bytesAt mK (G + BitVec.ofNat 64 o) k =
      bytesAt (writeBytes mZ (G + BitVec.ofNat 64 (16 * lead)) a) (G + BitVec.ofNat 64 o) k := fun o k h =>
    bytesAt_frame f₁ (fun r hr => (hrs r hr).sub_left (Offset.sub_base G h)) (by omega)
  have kA : ∀ o k, o + k ≤ 512 → (o + k ≤ 16 * lead ∨ 16 * lead + a.length ≤ o) →
      bytesAt (writeBytes mZ (G + BitVec.ofNat 64 (16 * lead)) a) (G + BitVec.ofNat 64 o) k = zeros k :=
    fun o k h h' => by
      rw [bytesAt_frame (writeBytes_frame' _ rfl) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact disjG h' (by omega) (by omega)) (by omega)]
      exact bytesAt_zeros hZ h
  -- The six parts.
  have e : 16 * (lead + na + nc + 1) = 16 * lead + (a.length + ((16 * na - a.length) + (c.length +
      ((16 * nc - c.length) + 16)))) := by omega
  rw [e, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add]
  simp only [add_ofNat_ofNat]
  rw [show 16 * lead + a.length + (16 * na - a.length) = 16 * (lead + na) by omega,
    show 16 * (lead + na) + c.length + (16 * nc - c.length) = 16 * (lead + na + nc) by omega, hL]
  have s₁ : bytesAt mL G (16 * lead) = zeros (16 * lead) := by
    have := kL 0 (16 * lead) (by omega)
    rw [kX 0 _ (by omega) (.inl (by omega)), kK 0 _ (by omega), kA 0 _ (by omega) (.inl (by omega))] at this
    simpa using this
  have s₂ : bytesAt mL (G + BitVec.ofNat 64 (16 * lead)) a.length = a := by
    rw [kL _ _ (by omega), kX _ _ (by omega) (.inl (by omega)), kK _ _ (by omega)]
    exact bytesAt_writeBytes_self _ _ _ (by omega)
  have s₃ : bytesAt mL (G + BitVec.ofNat 64 (16 * lead + a.length)) (16 * na - a.length) =
      zeros (16 * na - a.length) := by
    rw [kL _ _ (by omega), kX _ _ (by omega) (.inl (by omega)), kK _ _ (by omega),
      kA _ _ (by omega) (.inr (by omega))]
  have s₄ : bytesAt mL (G + BitVec.ofNat 64 (16 * (lead + na))) c.length = c := by
    rw [kL _ _ (by omega)]; exact hXc
  have s₅ : bytesAt mL (G + BitVec.ofNat 64 (16 * (lead + na) + c.length)) (16 * nc - c.length) =
      zeros (16 * nc - c.length) := by
    rw [kL _ _ (by omega), kX _ _ (by omega) (.inr (by omega)), kK _ _ (by omega),
      kA _ _ (by omega) (.inr (by omega))]
  rw [s₁, s₂, s₃, s₄, s₅]
  simp only [List.append_assoc]

end VG.Proof.AesGcm.X86_64.Short
