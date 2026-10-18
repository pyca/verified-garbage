module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeR2
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
public import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-! Montgomery initialization has a public trace for full and padded candidates. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64

def PrimeSetupBefore (p : PrimeParams) (s : State) : Prop :=
  VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w ∧ wv s.mem p.B (slot p.w aN) p.w = p.N ∧ p.w ≤ 48

def PrimeParams.product (p : PrimeParams) (mi : BitVec 64) : ProductPublic :=
  ⟨⟨p.B, p.Z, p.w, mi⟩, p.N,
    Nat.le_trans (VG.Proof.Rsa.slot_mono (w := p.w) (by decide : 8 ≤ 28)) p.room,
    by change 2 ≤ p.w; have := p.w4; omega,
    by change p.w < 2 ^ 31; have := p.w128; omega⟩

def PrimeInverse (p : PrimeParams) (s : State) : Prop := ∃ mi, SetupPre (p.product mi) s

theorem primeHeadArgs_state {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (.block [ldh .x8 (sArr aN)]) s
      (fun t => t.gpr .x0 = p.B ∧ t.gpr .x8 = off p.B (slot p.w aN)) := by
  have hw := h.1
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = off p.B (slot p.w aN)) (by
    brun [hw.x0, hdr_enc (show sArr aN < 32 by decide), hw.harr aN (by decide),
      hw.scr.ld (show 8 * sArr aN + 8 ≤ p.Z by have := hw.h256; simp only [sArr, aN]; omega)]) rfl rfl rfl)
    fun _ ⟨h8, hk⟩ => ⟨(hk.gpr .x0 (by decide)).trans hw.x0, h8⟩

theorem primeHead_ct : RelCT isa (Two PrimeSetupBefore)
    (.block Impl.Dsa.AArch64.Generation.primeHead) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.primeHead
  change RelCT isa (Two PrimeSetupBefore) (.block
    (([ldh .x8 (sArr aN)] : List Instr) ++ ([ld .x3 .x8] ++ minv ++
      [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]))) _
  apply RelCT.block_append (M := isa)
  refine RelCT.seq (two_post (two_taint [.x0] ?_ (by taint_decide))
    (fun _ _ h => primeHeadArgs_state h)) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.1.x0.trans ht.1.x0.symm
  · exact two_taint [.x0, .x8] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm) (by taint_decide)

theorem primeHead_inverse {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (.block Impl.Dsa.AArch64.Generation.primeHead) s (PrimeInverse p) := by
  have hw := h.1
  have hodd : (word s.mem p.B (slot p.w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by have := p.w4; omega), h.2.1,
      Nat.mod_mod_of_dvd _ (by decide)]
    exact p.odd
  refine WP.mono (msHead_ok hw hodd) fun t ⟨⟨hi, hm, _, _, _⟩, hk⟩ => ?_
  have ho : Outside p.B (8 * sMinv) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  have hf : Frm p.B [(8 * sMinv, 8)] s.mem t.mem := Frm.of_outside ho (by simp)
  have ht := hw.congr' hf (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact KMut.hdr (Or.inr (Or.inl rfl))) hk (by decide)
  have hn : wv t.mem p.B (slot p.w aN) p.w = p.N := by
    rw [ho.wv (by simp only [sMinv, slot, hdrBytes, aN]; omega) (by have := hw.hZ; have := hw.scr.nowrap; simp only [slot, hdrBytes, aN] at *; omega)]
    exact h.2.1
  have hinv : ((word t.mem p.B (slot p.w aN)).toNat * (word t.mem p.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 := by
    rw [ho.word (by simp only [sMinv, slot, hdrBytes, aN]; omega) (by simp only [slot, hdrBytes, aN]; omega)]
    exact hi
  exact ⟨word t.mem p.B (8 * sMinv), ⟨ht.good.1, hn, hinv⟩, h.2.2, by change 1 < p.N; have := p.n3; omega, p.odd⟩

theorem primeInverse_public {s t : State} (h : Two PrimeInverse s t) : Two SetupPre s t := by
  obtain ⟨p, ⟨mi, hs⟩, ⟨mi', ht⟩, hsp⟩ := h
  have low₁ : (word s.mem p.B (slot p.w aN)).toNat = p.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by have := p.w4; omega), show wv s.mem p.B (slot p.w aN) p.w = p.N from hs.1.modulus]
  have low₂ : (word t.mem p.B (slot p.w aN)).toNat = p.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by have := p.w4; omega), show wv t.mem p.B (slot p.w aN) p.w = p.N from ht.1.modulus]
  have hi := hs.1.inverse
  have hi' := ht.1.inverse
  change ((word s.mem p.B (slot p.w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 at hi
  change ((word t.mem p.B (slot p.w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 at hi'
  rw [low₁] at hi
  rw [low₂] at hi'
  have he := minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact p.odd) hi hi'
  subst mi'
  exact ⟨p.product mi, hs, ht, hsp⟩

theorem primeR2_ct (M : Mont) : RelCT isa (Two PrimeSetupBefore)
    (Impl.Dsa.AArch64.Generation.primeR2 M.mm) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.primeR2
  exact RelCT.seq (two_post primeHead_ct (fun _ _ h => primeHead_inverse h))
    ((constants_ct M).mono (fun _ _ h => primeInverse_public h) (fun _ _ h => h))

end VG.Proof.Dsa.AArch64.Generation
