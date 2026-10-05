import VerifiedGarbage.Proof.AesSiv.CtrPart

/-!
# AES-SIV: the key context

The context `vg_aes_siv_init` leaves is that of the key (`Spec.Siv.KeyRepr`)
when its three parts are where the calls of `vg_aes_expand_key_scratch` and
`vg_cmac_aes_subkeys` left them (`keyRepr_of`), on any target.
-/

namespace VG.Proof.AesSiv

open VG

/-- The context `init` leaves is that of the key: the schedule of `K1`, its
subkeys and the schedule of `K2`, each where the calls left it. -/
theorem keyRepr_of {m m₀ : Mem} {Ct Kp : Addr} {KL : Nat} (hl : KL = 32 ∨ KL = 48 ∨ KL = 64)
    (h1 : Spec.Aes.bytesAt m Ct (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2)))
    (hs : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 240) 32 =
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))))
        16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))))
        16).2)
    (h2 : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 272) (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ (Kp + BitVec.ofNat 64 (KL / 2)) (KL / 2))) :
    Spec.Siv.KeyRepr m Ct (Spec.Aes.bytesAt m₀ Kp KL) := by
  have hKL : KL = KL / 2 + KL / 2 := by omega
  have hlen := Proof.Cmac.bytesAt_length m₀ Kp KL
  have e8 : KL / 8 = KL / 2 / 4 := by omega
  have k1 : (Spec.Aes.bytesAt m₀ Kp KL).take (KL / 2) = Spec.Aes.bytesAt m₀ Kp (KL / 2) := by
    have := take_bytesAt m₀ Kp (a := KL / 2) (b := KL / 2)
    rwa [← hKL] at this
  have k2 : (Spec.Aes.bytesAt m₀ Kp KL).drop (KL / 2) =
      Spec.Aes.bytesAt m₀ (Kp + BitVec.ofNat 64 (KL / 2)) (KL / 2) := by
    have := drop_bytesAt m₀ Kp (a := KL / 2) (b := KL / 2)
    rwa [← hKL] at this
  have hs' : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 240) 32 =
      Spec.Aes.bytesAt m (Ct + 240) 16 ++ Spec.Aes.bytesAt m (Ct + 256) 16 := by
    rw [show (32 : Nat) = 16 + 16 from rfl, Proof.Cmac.Stream.bytesAt_append, Offset.add_add]; rfl
  have ka : Spec.Cmac.aes (Spec.Aes.bytesAt m₀ Kp (KL / 2)) =
      Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))) := by
    rw [Spec.Cmac.aes, Proof.Cmac.bytesAt_length, Spec.Aes.rounds, e8]
  rw [hs', ← ka] at hs
  obtain ⟨hs1, hs2⟩ := List.append_inj hs (by
    rw [Proof.Cmac.bytesAt_length, Spec.Cmac.aes]; exact (Proof.Cmac.subkeys_aes_length _ _).symm)
  refine ⟨by rw [hlen]; exact hl, ?_, ?_, ?_, ?_⟩
  · rw [hlen, k1, e8]; exact h1
  · rw [hlen, k1]; exact hs1
  · rw [hlen, k1]; exact hs2
  · rw [hlen, k2, e8]; exact h2

end VG.Proof.AesSiv
