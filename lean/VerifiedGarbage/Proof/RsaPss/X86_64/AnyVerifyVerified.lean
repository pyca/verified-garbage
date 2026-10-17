module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyTier
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSASSA-PSS verification with the hash functions as arguments on x86-64: `Verified`

For a tier `t` (`Proof/Pbkdf2/Md/X86_64/Tier.lean`) and a precomputed
public-key operation, `verify` with the tier's hash functions meets
`Spec.RsaPss.verifyAnyContract` (`verifyAny_verified`): for the hash
functions `hash` and `mgf1_hash` name, it is correct (`verifyAny_correct`)
and constant time (`verifyAny_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink Tier MdHash)

/-- `verify_okA` for the `g`th hash function given as `Gh`. -/
theorem verify_okW {hs : List Hash} {kh g : Nat} (hkh : kh < hs.length) (hg : g < hs.length)
    (hl : hs.length ≤ 2 ^ 31) (ht : TierOk hs) {H : Hash} (hkH : hs[kh] = H) (hH : HashOK H) (K : Callees H)
    (lk : MgfLink H hH) {Gh : Hash} (hgG : hs[g] = Gh) (hG : HashOK Gh) (KG : Callees Gh) (lkG : MgfLink Gh hG)
    (v : PublicImpl) (s : State) (h : verifyAnyK.pre s) (hsk : vhsel s = kh) (hsg : vmsel s = g)
    (hHs : Spec.HashId.mgf1 kh = some lk.G) (hGs : Spec.HashId.mgf1 g = some lkG.G) :
    ∃ t s', Exec isa (AnyHash.verify hs v.name v.code) s t s' ∧ abiPreserved s s' ∧ verifyAnyK.post s s' := by
  subst hgG
  exact verify_okA hkh hg hl ht hkH hH K lk hG KG lkG v s h hsk hsg hHs hGs

theorem code_ctW {k g : Nat} {hs : List Hash} (hkh : k < hs.length) (hg : g < hs.length) (hl : hs.length ≤ 2 ^ 31)
    {H : Hash} (hkH : hs[k] = H) (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)
    (hc : PssChecks H.P H.D) {Gh : Hash} (hgG : hs[g] = Gh) (hG : HashOK Gh) (KG : Callees Gh) (lkG : MgfLink Gh hG)
    (hcg : PssChecks Gh.P Gh.D) (v : PublicImpl) (hGk : Spec.HashId.mgf1 k = some lk.G) :
    RelCT isa (fun s₁ s₂ => (verifyAnyK.pre s₁ ∧ verifyAnyK.pre s₂ ∧ verifyAnyK.pub s₁ s₂) ∧ vhsel s₁ = k ∧
      vmsel s₁ = g) (AnyHash.verify hs v.name v.code) fun _ _ => True := by
  subst hgG
  exact code_ctA hH K lk hc v hkh hg hl hkH hG KG lkG hcg hGk

theorem verifyAny_correct (t : Tier) (v : PublicImpl) (s : State) (h : verifyAnyK.pre s) :
    ∃ tr s', Exec isa (AnyHash.verify (tierHashes t) v.name v.code) s tr s' ∧ abiPreserved s s' ∧
      verifyAnyK.post s s' := by
  have hsl := tierHashes_length t
  have ht8 := tier_length t
  obtain ⟨hk, hg⟩ := VPreA.sel h
  have hk' : vhsel s < t.hashes.length := by omega
  have hg' : vmsel s < t.hashes.length := by omega
  generalize hkq : vhsel s = kh at hk'
  generalize hgq : vmsel s = g at hg'
  have hkh : kh < (tierHashes t).length := by omega
  have hgh : g < (tierHashes t).length := by omega
  have hkH : (tierHashes t)[kh] = (t.hashes[kh]'hk').H := tierHashes_get t hkh
  have hgH : (tierHashes t)[g] = (t.hashes[g]'hg').H := tierHashes_get t hgh
  exact verify_okW hkh hgh (by omega) (tier_ok t) hkH (t.hashes[kh]'hk').ok (t.hashes[kh]'hk').K
    (t.hashes[kh]'hk').mgf hgH (t.hashes[g]'hg').ok (t.hashes[g]'hg').K (t.hashes[g]'hg').mgf v s h hkq hgq
    (tier_mgf1 t hk') (tier_mgf1 t hg')

theorem verifyAny_ct (t : Tier) (v : PublicImpl) :
    ConstantTime isa verifyAnyK.pre verifyAnyK.pub (AnyHash.verify (tierHashes t) v.name v.code) := by
  have hsl := tierHashes_length t
  have ht8 := tier_length t
  refine RelCT.constantTime ((RelCT.exists_ (Q := fun _ _ => True) (P := fun (p : Fin 8 × Fin 8) s₁ s₂ =>
      (verifyAnyK.pre s₁ ∧ verifyAnyK.pre s₂ ∧ verifyAnyK.pub s₁ s₂) ∧ vhsel s₁ = p.1 ∧ vmsel s₁ = p.2)
    fun p => ?_).mono (fun (s₁ s₂ : State) h => ?_) fun _ _ h => h)
  · have hk' : p.1.val < t.hashes.length := by omega
    have hg' : p.2.val < t.hashes.length := by omega
    have hkh : p.1.val < (tierHashes t).length := by omega
    have hgh : p.2.val < (tierHashes t).length := by omega
    have hkH : (tierHashes t)[p.1.val] = (t.hashes[p.1.val]'hk').H := tierHashes_get t hkh
    have hgH : (tierHashes t)[p.2.val] = (t.hashes[p.2.val]'hg').H := tierHashes_get t hgh
    exact code_ctW hkh hgh (by omega) hkH (t.hashes[p.1.val]'hk').ok (t.hashes[p.1.val]'hk').K
      (t.hashes[p.1.val]'hk').mgf (t.hashes[p.1.val]'hk').pss hgH (t.hashes[p.2.val]'hg').ok
      (t.hashes[p.2.val]'hg').K (t.hashes[p.2.val]'hg').mgf (t.hashes[p.2.val]'hg').pss v (tier_mgf1 t hk')
  · obtain ⟨hk, hg⟩ := VPreA.sel h.1
    exact ⟨(⟨vhsel s₁, hk⟩, ⟨vmsel s₁, hg⟩), h, rfl, rfl⟩

/-- `verify` with a tier's hash functions meets `Spec.RsaPss.verifyAnyContract`. -/
theorem verifyAny_verified (t : Tier) (v : PublicImpl) :
    Verified X86_64.target (AnyHash.verify (tierHashes t) v.name v.code)
      (Spec.RsaPss.verifyAnyContract abi verifyStack) :=
  Verified.of_correct (k := verifyAnyK) (verifyAny_correct t v) (verifyAny_ct t v) verifyAny_implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem verifyAny_spAll (t : Tier) (v : PublicImpl) :
    (AnyHash.verify (tierHashes t) v.name v.code).all (fun i => !isa.writesSp i) = true := by
  have h := verifyAny_safe (tier_ok t) v
  rw [safeI_eq, allInstrs_and, Bool.and_eq_true] at h
  exact Code.all_of_allInstrs h.1

end VG.Proof.RsaPss.X86_64.Any
