module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.Layout
public import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay

/-! # Preparing all public-key polynomials -/

-- separate module: isolates the public-polynomial loop invariant from secret decoding and generic ABI framing.

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.PreparedKey
open VG.Impl.MlDsa.AArch64.Call (Ptr seqR)
open VG.Spec.Sha3 (bytesAt)

def publicWrites (p : Params) : List (Ptr × Nat) :=
  [((.x26, 0), p.pkLen), ((.x28, 0), 1024)] ++
    (List.range p.k).map fun i => ((.x26, p.pkLen + 1024 * i), 1024)

structure PublicInv (p : Params) (σ : State) (key : List Byte) (done : Nat) (s : State) : Prop where
  lay : Lay 16 (input p.pkLen) (output p.pkLen p.k) s
  post : PPostB 16 σ s (publicWrites p)
  x24 : s.gpr .x24 = σ.gpr .x24
  source : bytesAt s.mem (pa s (.x25, 0)) p.pkLen = key
  encoded : bytesAt s.mem (pa s (.x26, 0)) p.pkLen = key
  polys : ∀ i < done, PolyIs s.mem (pa s (.x26, p.pkLen + 1024 * i))
    (VG.Proof.MlDsa.Verify.t1Hat key i)

theorem public_step {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    {σ s : State} {key : List Byte} {i : Nat} (hi : i < p.k)
    (h : PublicInv p σ key i s) :
    WP isa (publicPoly p i) s (PublicInv p σ key (i + 1)) := by
  obtain ⟨hc, hi'⟩ := public_checks hp hi
  refine WP.mono (publicPoly_ok h.lay hc hi') fun t ⟨ht, h24, hpoly⟩ => ?_
  have hslice : bytesAt s.mem (pa s (.x25, 32 + 320 * i)) 320 =
      (key.drop (32 + 320 * i)).take 320 := by
    rw [← h.source, MlKem.bytesAt_slice _ _ (by have := (KeyGen.pfacts hp).pk; omega)]
    simp only [pa, BitVec.add_zero]
  rw [hslice] at hpoly
  refine ⟨h.lay.post ht, ?_, h24.trans h.x24, ?_, ?_, ?_⟩
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
    · simp [publicWrites]
  · rw [h.lay.keepBytes ht (public_keep_source hp hi)]
    exact h.source
  · rw [h.lay.keepBytes ht (public_keep_prefix hp hi)]
    exact h.encoded
  · intro j hj
    by_cases he : j = i
    · subst j
      rw [ht.pa (p := (.x26, p.pkLen + 1024 * i)) (show Reg.x26 ∈ keptRegs by decide)]
      exact hpoly
    · exact h.lay.keepPoly ht (public_keep_prior hp hi (by omega)) (h.polys j (by omega))

theorem public_polys {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87)
    {σ s : State} {key : List Byte} (h : PublicInv p σ key 0 s) :
    WP isa (seqR (publicPoly p) 0 p.k) s (PublicInv p σ key p.k) := by
  simpa only [Nat.zero_add] using seqR_ok p.k 0
    (fun i _ hi s h => public_step hp (by omega) h) s h

theorem public_body {p : Params}
    (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) (s : State)
    (L : Lay 16 (input p.pkLen) (output p.pkLen p.k) s) :
    WP isa (.seq (copy (.x26, 0) (.x25, 0) p.pkLen)
      (seqR (publicPoly p) 0 p.k)) s fun t =>
      PublicInv p s (bytesAt s.mem (pa s (.x25, 0)) p.pkLen) p.k t ∧
      PreparedPublicKey p t.mem (pa t (.x26, 0)) := by
  refine WP.seq (WP.mono (copy_ok L (public_copy_check hp)) fun u ⟨hu, h24, hc⟩ => ?_)
  have hkeep : keepB (input p.pkLen) (output p.pkLen p.k)
      [((.x26, 0), p.pkLen)] (.x25, 0) p.pkLen = true := by
    simp only [keepB, List.all_cons, List.all_nil, Bool.and_true, sep25_26, in25,
      Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hinit : PublicInv p s (bytesAt s.mem (pa s (.x25, 0)) p.pkLen) 0 u := by
    refine ⟨L.post hu, hu.mono (by simp [publicWrites]), h24, L.keepBytes hu hkeep, ?_, ?_⟩
    · rwa [hu.pa (p := (.x26, 0)) (by decide)]
    · intro i hi
      omega
  refine WP.mono (public_polys hp hinit) fun t ht => ⟨ht, ?_⟩
  intro i hi
  rw [ht.encoded, VG.Proof.MlDsa.PreparedKey.public_poly p _ hi]
  have hpoly := ht.polys i hi
  simpa only [pa, BitVec.add_zero, n] using hpoly

end VG.Proof.MlDsa.AArch64.PreparedKey
