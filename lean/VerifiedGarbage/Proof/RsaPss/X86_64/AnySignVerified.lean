module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySignCt
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyTier
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# RSASSA-PSS signing with the hash functions as arguments on x86-64: `Verified`

For a tier `t` (`Proof/Pbkdf2/Md/X86_64/Tier.lean`), `sign` with its hash
functions (`tierHashes t`) meets `Spec.RsaPss.signAnyContract`
(`signAny_verified`): for the hash functions `hash` and `mgf1_hash` name, the
`hash`th and the `mgf1_hash`th of the tier (`Tier.mgf_ok`), it is correct
(`signAny_correct`) and constant time (`signAny_ct`), its return address and
MXCSR's control bits kept.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.RsaPss.X86_64
open VG.Proof.Rsa.X86_64 (chkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink Tier MdHash)

theorem signAnyK_sel {s : State} (h : signAnyK.pre s) : hsel s < 8 ∧ msel s < 8 := by
  simp only [signAnyK] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr dOn dOe dOp dOq dOdp dOdq dOqi dOdg dOsa dOs dOa dns des dps dqs ddps
    ddqs dqis ddgs dsas dsa dRo dRn dRe dRp dRq dRdp dRdq dRqi dRdg dRsa dRs dRa dKo dKn dKe dKp dKq
    dKdp dKdq dKqi dKdg dKsa dKs dKa wO wN wE wP wQ wDp wDq wQi wDg wSa wS hh hm hdl _ob1 hsi L1 L2 pl1 pl2
    ql1 ql2 hdpl hqil hdql
  exact ⟨sel_lt hh, sel_lt hm⟩

/-! ## What the code may do -/

theorem signAny_spAll (hs : List Hash) (ht : TierOk hs) {privN : String} {privC : Prog isa} (hC : SpSafe privC) :
    (AnyHash.sign hs privN privC).allInstrs (fun i => !isa.writesSp i) = true := by
  have he := signEncAny_safe ht
  rw [safeI_eq, allInstrs_and, Bool.and_eq_true] at he
  have hC' : privC.allInstrs (fun i => !isa.writesSp i) = true := by
    rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by rw [hC i hi]; rfl
  simp only [AnyHash.sign, AnyHash.signBody, seqs, AnyHash.signMain, Code.allInstrs, he.1, hC', rec_all,
    List.all_append, signFail, AnyHash.emLenAny, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

theorem signAny_sp (hs : List Hash) (ht : TierOk hs) {privN : String} {privC : Prog isa} (hC : SpSafe privC) :
    SpSafe (AnyHash.sign hs privN privC) := by
  have h := signAny_spAll hs ht (privN := privN) hC
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem signAny_xd (hs : List Hash) (ht : TierOk hs) {privN : String} {privC : Prog isa}
    (hd : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) :
    (AnyHash.sign hs privN privC).x86_64Depth ≤ signStack := by
  have he := signEncAny_xd ht
  simp only [AnyHash.sign, AnyHash.signBody, seqs, AnyHash.signMain, Code.x86_64Depth, signFail,
    AnyHash.emLenAny, byteLoop, X86_64.Instr.frameBytes, Nat.zero_max, Nat.max_zero]
  unfold signStack Rsa.X86_64.stackBytes frameBytes at *
  omega

/-! ## Correctness -/

/-- `sign_okA` for the `g`th hash function given as `Gh`. -/
theorem sign_okW {hs : List Hash} {kh g : Nat} (hkh : kh < hs.length) (hg : g < hs.length)
    (hl : hs.length ≤ 2 ^ 31) (ht : TierOk hs) {H : Hash} (hkH : hs[kh] = H) (hH : HashOK H) (K : Callees H)
    (lk : MgfLink H hH) {Gh : Hash} (hgG : hs[g] = Gh) (hG : HashOK Gh) (KG : Callees Gh) (lkG : MgfLink Gh hG)
    {privN : String} {privC : Prog isa}
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hspC : SpSafe privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) {s : State}
    (h : signAnyK.pre s) (hsk : hsel s = kh) (hsg : msel s = g) (hHs : Spec.HashId.mgf1 kh = some lk.G)
    (hGs : Spec.HashId.mgf1 g = some lkG.G) :
    WP isa (AnyHash.sign hs privN privC) s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ signAnyK.post s s' ∧
      s'.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10 := by
  subst hgG
  exact sign_okA hkh hg hl ht hkH hH K lk hG KG lkG hv hspC hdC h hsk hsg hHs hGs

theorem signAny_correct (t : Tier) {privN : String} {privC : Prog isa}
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hC : SpSafe privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes)
    (s : State) (h : signAnyK.pre s) :
    ∃ tr s', Exec isa (AnyHash.sign (tierHashes t) privN privC) s tr s' ∧ abiPreserved s s' ∧
      signAnyK.post s s' := by
  have hsl := tierHashes_length t
  have ht8 := tier_length t
  obtain ⟨hk, hg⟩ := signAnyK_sel h
  have hk' : hsel s < t.hashes.length := by omega
  have hg' : msel s < t.hashes.length := by omega
  have hp := SPreA.of _ h (tier_mgf1 t hk')
  have ht := tier_ok t
  generalize hkq : hsel s = kh at hk'
  generalize hgq : msel s = g at hg'
  have hkh : kh < (tierHashes t).length := by omega
  have hgh : g < (tierHashes t).length := by omega
  have hkH : (tierHashes t)[kh] = (t.hashes[kh]'hk').H := tierHashes_get t hkh
  have hgH : (tierHashes t)[g] = (t.hashes[g]'hg').H := tierHashes_get t hgh
  have hW := X86_64.WP.stackFrame (signAny_sp _ ht (privN := privN) hC)
    (by have := signAny_xd _ ht (privN := privN) hdC; unfold signStack Rsa.X86_64.stackBytes at this; omega)
    (sign_okW hkh hgh (by omega) ht hkH (t.hashes[kh]'hk').ok (t.hashes[kh]'hk').K (t.hashes[kh]'hk').mgf hgH
      (t.hashes[g]'hg').ok (t.hashes[g]'hg').K (t.hashes[g]'hg').mgf hv hC hdC h hkq hgq (tier_mgf1 t hk')
      (tier_mgf1 t hg'))
  obtain ⟨tr, s', he, ⟨hcs, hpost, hmx⟩, hf⟩ := hW
  refine ⟨tr, s', he, ⟨hcs, ?_, hmx⟩, hpost⟩
  -- The return address.
  have hd := signAny_xd _ ht (privN := privN) hdC
  refine Mem.readW_congr fun i hi => hf _ fun r hr hc => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [hp.hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dRo _ (Offset.contains_base _ (by omega) (by omega)) hc
    · exact hp.dRs _ (Offset.contains_base _ (by omega) (by omega)) hc
  · simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp1; have := hp.sp2
    exact Offset.base_disjoint_below (s.gpr .rsp) (n := (AnyHash.sign (tierHashes t) privN privC).x86_64Depth) (k := 8)
      (by unfold signStack at *; omega) _ (Offset.contains_base _ (by omega) (by omega)) hc

/-! ## Constant time -/

theorem sign_ctW {k g : Nat} {hs : List Hash} (hkh : k < hs.length) (hg : g < hs.length) (hl : hs.length ≤ 2 ^ 31)
    (ht : TierOk hs) {H : Hash} (hkH : hs[k] = H) (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)
    (hc : PssChecks H.P H.D) {Gh : Hash} (hgG : hs[g] = Gh) (hG : HashOK Gh) (KG : Callees Gh) (lkG : MgfLink Gh hG)
    (hcg : PssChecks Gh.P Gh.D) {privN : String} {privC : Prog isa}
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hct : ConstantTime isa chkContract.pre chkContract.pub privC) (hspC : SpSafe privC)
    (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) (hGk : Spec.HashId.mgf1 k = some lk.G) :
    RelCT isa (fun s₁ s₂ => (signAnyK.pre s₁ ∧ signAnyK.pre s₂ ∧ signAnyK.pub s₁ s₂) ∧ hsel s₁ = k ∧ msel s₁ = g)
      (AnyHash.sign hs privN privC) fun _ _ => True := by
  subst hgG
  exact sign_ctA hv hct hspC hdC hH K lk hc hkh hg hl ht hkH hG KG lkG hcg hGk

theorem signAny_ct (t : Tier) {privN : String} {privC : Prog isa}
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hct : ConstantTime isa chkContract.pre chkContract.pub privC) (hC : SpSafe privC)
    (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes) :
    ConstantTime isa signAnyK.pre signAnyK.pub (AnyHash.sign (tierHashes t) privN privC) := by
  have hsl := tierHashes_length t
  have ht8 := tier_length t
  have ht := tier_ok t
  refine RelCT.constantTime ((RelCT.exists_ (Q := fun _ _ => True) (P := fun (p : Fin 8 × Fin 8) s₁ s₂ =>
      (signAnyK.pre s₁ ∧ signAnyK.pre s₂ ∧ signAnyK.pub s₁ s₂) ∧ hsel s₁ = p.1 ∧ msel s₁ = p.2)
    fun p => ?_).mono (fun (s₁ s₂ : State) h => ?_) fun _ _ h => h)
  · have hk' : p.1.val < t.hashes.length := by omega
    have hg' : p.2.val < t.hashes.length := by omega
    have hkh : p.1.val < (tierHashes t).length := by omega
    have hgh : p.2.val < (tierHashes t).length := by omega
    have hkH : (tierHashes t)[p.1.val] = (t.hashes[p.1.val]'hk').H := tierHashes_get t hkh
    have hgH : (tierHashes t)[p.2.val] = (t.hashes[p.2.val]'hg').H := tierHashes_get t hgh
    exact sign_ctW hkh hgh (by omega) ht hkH
      (t.hashes[p.1.val]'hk').ok (t.hashes[p.1.val]'hk').K (t.hashes[p.1.val]'hk').mgf (t.hashes[p.1.val]'hk').pss
      hgH (t.hashes[p.2.val]'hg').ok (t.hashes[p.2.val]'hg').K (t.hashes[p.2.val]'hg').mgf
      (t.hashes[p.2.val]'hg').pss hv hct hC hdC (tier_mgf1 t hk')
  · obtain ⟨hk, hg⟩ := signAnyK_sel h.1
    exact ⟨(⟨hsel s₁, hk⟩, ⟨msel s₁, hg⟩), h, rfl, rfl⟩

/-! ## `Verified` -/

/-- `sign` with a tier's hash functions meets `Spec.RsaPss.signAnyContract`. -/
theorem signAny_verified (t : Tier) {privN : String} {privC : Prog isa}
    (hct : ConstantTime isa chkContract.pre chkContract.pub privC) (hdC : privC.x86_64Depth ≤ Rsa.X86_64.stackBytes)
    (hv : ∀ s, chkContract.pre s → ∃ t s', Exec isa privC s t s' ∧ abiPreserved s s' ∧ chkContract.post s s')
    (hC : SpSafe privC) :
    Verified X86_64.target (AnyHash.sign (tierHashes t) privN privC) (Spec.RsaPss.signAnyContract abi signStack) :=
  Verified.of_correct (k := signAnyK) (signAny_correct t hv hC hdC) (signAny_ct t hv hct hC hdC) signAny_implies

end VG.Proof.RsaPss.X86_64.Any
