import VerifiedGarbage.Proof.Gcm.Compose

/-!
# GCM streaming, out of place: whole blocks on the state

Untrusted: everything here is checked by Lean. A streaming state that
represents a message whose ciphertext so far is a whole number of blocks
(nonempty, or after additional data of whole blocks) keeps representing it
with more whole blocks of ciphertext when its counter block (`St + 48`) and
GHASH accumulator (`St + 16`) are advanced over them, as
`vg_aes_gcm_encrypt_blocks_to` does, reading the plaintext from one buffer
and writing the ciphertext to another (`streamRepr_blocksTo`).
-/

namespace VG.Proof.Gcm

open VG VG.Spec.Gcm
open VG.Spec.Aes (bytesAt)

/-- `ctr_whole`, out of place: the plaintext at `sp`, the ciphertext written
to `dp`. -/
theorem ctr_wholeTo {m m' : Mem} {cb ks sp dp : Addr} {ciph : Block → Block} {icb : Block} {n nb : Nat}
    (h : Ctr m cb ks ciph icb n) (h0 : n % 16 = 0)
    (hd : blocksAt m' dp nb = ctr32 ciph (blockAt m cb) (blocksAt m sp nb))
    (hc : blockAt m' cb = Nat.repeat inc32 nb (blockAt m cb)) :
    bytesAt m' dp (16 * nb) = xorKs ciph icb n (bytesAt m sp (16 * nb)) ∧ Ctr m' cb ks ciph icb (n + 16 * nb) := by
  have hcb : blockAt m cb = Nat.repeat inc32 (n / 16) icb := by rw [h.1]; congr 1; omega
  refine ⟨?_, ?_, fun h1 => absurd (by omega) h1⟩
  · refine list_ext (by simp [length_xorKs, Cmac.bytesAt_length]) fun k hk => ?_
    simp only [Cmac.bytesAt_length] at hk
    rw [getD_xorKs _ _ _ _ (by rw [Cmac.bytesAt_length]; exact hk), getD_bytesAt' _ _ hk,
      getD_bytesAt' _ _ hk]
    have hq : k / 16 < nb := by omega
    have e₁ := congrArg (fun L => L.getD (k / 16) 0) hd
    rw [ctr32_getD _ _ _ (by rw [length_blocksAt]; exact hq), blocksAt_getD _ _ _ hq,
      blocksAt_getD _ _ _ hq] at e₁
    have ea : ∀ p : Addr, p + BitVec.ofNat 64 k = p + BitVec.ofNat 64 (16 * (k / 16)) + BitVec.ofNat 64 (k % 16) :=
      fun p => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [ea dp, ea sp, bytes_toBytes_blockAt m' _ (by omega), bytes_toBytes_blockAt m _ (by omega), e₁,
      Proof.Aes.toBytes_xor _ _ (by omega), ksByte, hcb, ← repeat_add,
      show (n + k) / 16 = k / 16 + n / 16 by omega, show (n + k) % 16 = k % 16 by omega]
  · rw [hc, hcb, ← repeat_add]; congr 1; omega

theorem length_ghashInput_mod {a c : List Byte} (hc : c ≠ [] ∨ a.length % 16 = 0) (h0 : c.length % 16 = 0) :
    (ghashInput a c).length % 16 = 0 := by
  by_cases e : c = []
  · subst e; simp only [ghashInput, ite_true]; exact hc.resolve_left (fun h => h rfl)
  · rw [ghashInput_of_ne e]
    simp only [List.length_append, zeros, List.length_replicate, padLen]
    omega

/-- The input to GHASH of `c ++ e`, for `e ≠ []`, after a nonempty `c` or
additional data `a` of whole blocks, which need no padding. -/
theorem ghashInput_append' {a c e : List Byte} (hc : c ≠ [] ∨ a.length % 16 = 0) (he : e ≠ []) :
    ghashInput a (c ++ e) = ghashInput a c ++ e := by
  rw [ghashInput_append _ _ _ he]
  by_cases h : c = []
  · subst h
    simp [ghashInput, zeros, padLen_of_mod (hc.resolve_left (fun h => h rfl))]
  · simp only [h, ite_false]

/-- A state whose ciphertext so far `c` is a whole number of blocks, and
nonempty or after additional data of whole blocks (so that GHASH has absorbed
all of its input, with no padding to come), its counter block and GHASH accumulator advanced over `nb ≥ 1` blocks
encrypted from `sp` to `dp` (and `J₀` kept): it represents the message with
their ciphertext appended, the plaintext at `sp` encrypted as the
continuation of `c`. -/
theorem streamRepr_blocksTo {m m' : Mem} {St sp dp : Addr} {ciph : Block → Block} {h : Block}
    {iv a c : List Byte} {nb : Nat} (hr : StreamRepr m St ciph h iv a c) (hc : c ≠ [] ∨ a.length % 16 = 0)
    (h0 : c.length % 16 = 0)
    (hnb : nb ≠ 0) (hJ : blockAt m' St = blockAt m St)
    (hd : blocksAt m' dp nb = ctr32 ciph (blockAt m (St + 48)) (blocksAt m sp nb))
    (hC : blockAt m' (St + 48) = Nat.repeat inc32 nb (blockAt m (St + 48)))
    (hY : blockAt m' (St + 16) = ghashFrom h (blockAt m (St + 16)) (blocksAt m' dp nb)) :
    bytesAt m' dp (16 * nb) = xorKs ciph (inc32 (j0 h iv)) c.length (bytesAt m sp (16 * nb)) ∧
      StreamRepr m' St ciph h iv a (c ++ bytesAt m' dp (16 * nb)) := by
  obtain ⟨hj, habs, hctr⟩ := streamRepr_iff.mp hr
  obtain ⟨e₁, c₁⟩ := ctr_wholeTo hctr h0 hd hC
  have hx0 := length_ghashInput_mod (a := a) hc h0
  have hne : bytesAt m' dp (16 * nb) ≠ [] := by
    intro e; have := congrArg List.length e; rw [Cmac.bytesAt_length] at this; simp at this; omega
  refine ⟨e₁, streamRepr_iff.mpr ⟨hJ.trans hj, ?_, ?_⟩⟩
  · rw [ghashInput_append' hc hne]
    exact absorb_whole habs hx0 (by rw [Cmac.bytesAt_length]; omega) (by rw [hY, blocksAt_eq])
  · rw [List.length_append, Cmac.bytesAt_length]; exact c₁

end VG.Proof.Gcm
