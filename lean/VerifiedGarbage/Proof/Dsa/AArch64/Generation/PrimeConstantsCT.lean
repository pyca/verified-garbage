module

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTMs
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.CTFront
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
public import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeState
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MontSetup
meta import VerifiedGarbage.Proof.Rsa.Ranges
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Rsa.Ranges

/-! ### `Dsa.AArch64.Generation.PrimeR2CT`, which this module and modules that import it used -/

section

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
    by change 2 ≤ p.w; have := p.w4; omega_using [this],
    by change p.w < 2 ^ 31; have := p.w128; omega_using [this]⟩

def PrimeInverse (p : PrimeParams) (s : State) : Prop := ∃ mi, SetupPre (p.product mi) s

theorem primeHeadArgs_state {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (.block [ldh .x8 (sArr aN)]) s
      (fun t => t.gpr .x0 = p.B ∧ t.gpr .x8 = off p.B (slot p.w aN)) := by
  have hw := h.1
  refine WP.mono (WP.keep [.x8] (Q := fun t => t.gpr .x8 = off p.B (slot p.w aN)) (by
    brun [hw.x0, hdr_enc (show sArr aN < 32 by decide), hw.harr aN (by decide),
      hw.scr.ld (show 8 * sArr aN + 8 ≤ p.Z by have := hw.h256; simp only [sArr, aN]; omega_using [this])]) rfl rfl rfl)
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
    rw [← wv_mod64 (n := p.w) _ _ _ (by have := p.w4; omega_using [this]), h.2.1,
      Nat.mod_mod_of_dvd _ (by decide)]
    exact p.odd
  refine WP.mono (msHead_ok hw hodd) fun t ⟨⟨hi, hm, _, _, _⟩, hk⟩ => ?_
  have ho : Outside p.B (8 * sMinv) 8 s.mem t.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  have hf : Frm p.B [(8 * sMinv, 8)] s.mem t.mem := Frm.of_outside ho (by simp)
  have ht := hw.congr' hf (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact KMut.hdr (Or.inr (Or.inl rfl))) hk (by decide)
  have hn : wv t.mem p.B (slot p.w aN) p.w = p.N := by
    rw [ho.wv (by simp only [sMinv, slot, hdrBytes, aN]; omega_using []) (by have := hw.hZ; have := hw.scr.nowrap; simp only [slot, hdrBytes, aN] at *; omega_arith)]
    exact h.2.1
  have hinv : ((word t.mem p.B (slot p.w aN)).toNat * (word t.mem p.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 := by
    rw [ho.word (by simp only [sMinv, slot, hdrBytes, aN]; omega_using []) (by simp only [slot, hdrBytes, aN]; omega_using [])]
    exact hi
  exact ⟨word t.mem p.B (8 * sMinv), ⟨ht.good.1, hn, hinv⟩, h.2.2, by change 1 < p.N; have := p.n3; omega_using [this], p.odd⟩

theorem primeInverse_public {s t : State} (h : Two PrimeInverse s t) : Two SetupPre s t := by
  obtain ⟨p, ⟨mi, hs⟩, ⟨mi', ht⟩, hsp⟩ := h
  have low₁ : (word s.mem p.B (slot p.w aN)).toNat = p.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by have := p.w4; omega_using [this]), show wv s.mem p.B (slot p.w aN) p.w = p.N from hs.1.modulus]
  have low₂ : (word t.mem p.B (slot p.w aN)).toNat = p.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.w) _ _ _ (by have := p.w4; omega_using [this]), show wv t.mem p.B (slot p.w aN) p.w = p.N from ht.1.modulus]
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

end

end

/-! Derive the remaining Montgomery constants with a public trace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64

def PrimeGood (p : PrimeParams) (s : State) : Prop := VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w

def PrimeR2Ready (p : PrimeParams) (s : State) : Prop :=
  VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w ∧
    ((word s.mem p.B (slot p.w aN)).toNat * (word s.mem p.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem p.B (slot p.w aN) p.w = p.N ∧ wv s.mem p.B (slot p.w aOne) p.w = 1 ∧
    wv s.mem p.B (slot p.w aR2) p.w = 2 ^ (64 * p.w) * 2 ^ (64 * p.w) % p.N

theorem primeR2_ready (M : Mont) {p : PrimeParams} {s : State} (h : PrimeSetupBefore p s) :
    WP isa (Impl.Dsa.AArch64.Generation.primeR2 M.mm) s (PrimeR2Ready p) :=
  WP.mono (primeR2_ok M h.1 h.2.2 h.2.1 p.odd (by have := p.n3; omega_using [this]))
    (fun _ ⟨ws, inv, hn, hone, hr2, _, _⟩ => ⟨ws, inv, hn, hone, hr2⟩)

theorem primeMontOne_good (M : Mont) {p : PrimeParams} {s : State} (h : PrimeR2Ready p s) :
    WP isa (M.mm aY aR2 aOne) s (PrimeGood p) := by
  obtain ⟨hw, hi, hn, hone, _⟩ := h
  refine WP.mono (M.mm_ok hw.good.1 hw.good.2 hw.w1 (by have := hw.w2; omega_using [this])
    (o := aY) (a := aR2) (b := aOne) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hi (by rw [hone, hn]; have := p.n3; omega_using [this]))
    fun t ⟨_, _, _, ha, hk⟩ => ?_
  have hf : Frm p.B (VG.Proof.Ffdh.AArch64.ParameterCandidate.mpTail p.w) s.mem t.mem :=
    Frm.of_arrays ha (by simp [VG.Proof.Ffdh.AArch64.ParameterCandidate.mpTail])
  exact hw.congr' hf (VG.Proof.Ffdh.AArch64.ParameterCandidate.mpTail_kmut p.w) hk (by decide)

theorem copyR1_ct : RelCT isa (Two PrimeGood) (copyA aR1 aY) (fun _ _ => True) := by
  change RelCT isa (Two PrimeGood)
    (.seq (.block (ws ++ (base aY .x16 ++ base aR1 .x17))) copyWords) _
  exact ws_ct0 PrimeParams.B PrimeParams.Z PrimeParams.w (fun _ _ h => h) (by taint_decide)

theorem copyR1_good {p : PrimeParams} {s : State} (h : PrimeGood p s) :
    WP isa (copyA aR1 aY) s (PrimeGood p) := by
  refine WP.mono (copyA_ok h (o := aR1) (a := aY) (by decide) (by decide) (by decide))
    fun t ⟨_, ho, _, _, hk⟩ => ?_
  have hf : Frm p.B [(slot p.w aR1, 8 * p.w)] s.mem t.mem := Frm.of_outside ho (by simp)
  exact h.congr' hf
    (by intro r hr; rcases List.mem_singleton.mp hr with rfl; exact KMut.ofSlot _ _ _) hk (by decide)

theorem negateR1_ct : RelCT isa (Two PrimeGood) (seqs (subA aRm1 aN aR1)) (fun _ _ => True) := by
  rw [subA_eq']
  exact ws_ct0 PrimeParams.B PrimeParams.Z PrimeParams.w (fun _ _ h => h) (by taint_decide)

theorem primeConstants_ct (M : Mont) : RelCT isa (Two PrimeR2Ready)
    (seqs (Impl.Dsa.AArch64.Generation.primeConstants M.mm)) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.primeConstants
  apply RelCT.seqs_append (by simp) (by simp [subA])
  simp only [seqs]
  refine RelCT.seq (RelCT.seq (two_post
    (two_map (fun p : PrimeParams => (⟨p.B, p.Z, p.w⟩ : VG.Proof.Bignum.AArch64.Ws))
      (fun _ _ h => ⟨_, h.1.good⟩) (M.ct (o := aY) (a := aR2) (b := aOne) (by unfold MmUse; decide)))
    (fun _ _ h => primeMontOne_good M h))
    (two_post copyR1_ct (fun _ _ h => copyR1_good h))) negateR1_ct

end VG.Proof.Dsa.AArch64.Generation
