module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Layout
public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Secret
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay

/-! # Preparing all secret-key polynomials -/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.PreparedKey
open VG.Impl.MlDsa.AArch64.Call (Ptr seqR)
open VG.Spec.Sha3 (bytesAt)

def secretWrites (p : Params) : List (Ptr × Nat) :=
  [((.x26, 0), p.skLen), ((.x28, 0), 1024)] ++
    (List.range (p.ℓ + 2 * p.k)).map fun i => ((.x26, p.skLen + 1024 * i), 1024)

structure SecretInv (p : Params) (σ : State) (key : List Byte) (done : Nat) (s : State) : Prop where
  lay : Lay 16 (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k)) s
  post : PPostB 16 σ s (secretWrites p)
  source : bytesAt s.mem (pa s (.x25, 0)) p.skLen = key
  encoded : bytesAt s.mem (pa s (.x26, 0)) p.skLen = key
  polys : ∀ i < done, PolyIs s.mem (pa s (.x26, p.skLen + 1024 * i))
    (preparedSecretPolys p key)[i]!

theorem secret_step {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    {σ s : State} {key : List Byte} {i : Nat} (hi : i < (p.ℓ + 2 * p.k))
    (h : SecretInv p σ key i s) :
    WP isa (secretPoly p i) s (SecretInv p σ key (i + 1)) := by
  refine WP.mono (secretPoly_ok hp h.lay h.source hi) fun t ⟨ht, _, hpoly⟩ => ?_
  refine ⟨h.lay.post ht, ?_, ?_, ?_, ?_⟩
  · refine h.post.trans ht (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact show Reg.x26 ∈ keptRegs by decide
      · exact show Reg.x28 ∈ keptRegs by decide)
      (fun _ hw => hw) ?_
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.mpr hi))
    · simp [secretWrites]
  · rw [h.lay.keepBytes ht (row_keep_source p.skLen (p.ℓ + 2 * p.k) hi)]
    exact h.source
  · rw [h.lay.keepBytes ht (row_keep_prefix p.skLen (p.ℓ + 2 * p.k) hi)]
    exact h.encoded
  · intro j hj
    by_cases he : j = i
    · subst j
      rw [ht.pa (p := (.x26, p.skLen + 1024 * i)) (show Reg.x26 ∈ keptRegs by decide)]
      exact hpoly
    · exact h.lay.keepPoly ht (row_keep_prior p.skLen (p.ℓ + 2 * p.k) hi (by omega)) (h.polys j (by omega))

theorem secret_polys {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    {σ s : State} {key : List Byte} (h : SecretInv p σ key 0 s) :
    WP isa (seqR (secretPoly p) 0 (p.ℓ + 2 * p.k)) s (SecretInv p σ key (p.ℓ + 2 * p.k)) := by
  simpa only [Nat.zero_add] using seqR_ok (p.ℓ + 2 * p.k) 0
    (fun i _ hi s h => secret_step hp (by omega) h) s h

theorem secret_body {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (s : State)
    (L : Lay 16 (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k)) s) :
    WP isa (.seq (copy (.x26, 0) (.x25, 0) p.skLen)
      (seqR (secretPoly p) 0 (p.ℓ + 2 * p.k))) s fun t =>
      SecretInv p s (bytesAt s.mem (pa s (.x25, 0)) p.skLen) (p.ℓ + 2 * p.k) t ∧
      PreparedSecretKey p t.mem (pa t (.x26, 0)) := by
  refine WP.seq (WP.mono (copy_ok L (secret_copy_check hp)) fun u ⟨hu, _, hc⟩ => ?_)
  have hkeep : keepB (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k))
      [((.x26, 0), p.skLen)] (.x25, 0) p.skLen = true := by
    simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sep25_26, in25,
      Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hinit : SecretInv p s (bytesAt s.mem (pa s (.x25, 0)) p.skLen) 0 u := by
    refine ⟨L.post hu, hu.mono (by simp [secretWrites]), L.keepBytes hu hkeep, ?_, ?_⟩
    · rwa [hu.pa (p := (.x26, 0)) (by decide)]
    · intro i hi
      omega
  refine WP.mono (secret_polys hp hinit) fun t ht => ⟨ht, ?_⟩
  intro i hi
  rw [ht.encoded]
  have hpoly := ht.polys i hi
  simpa only [pa, BitVec.add_zero, n] using hpoly

end VG.Proof.MlDsa.AArch64.PreparedKey
