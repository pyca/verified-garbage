module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySignCtEnc
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyDispatch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# RSASSA-PSS signing with the hash functions as arguments on x86-64: the encoding in two runs

Both runs dispatch to the same hash function `hs[k]` (the selector is public
data of the entry states), whose part of the encoding (`signPre`) is
constant time as `signEnc`'s pieces are, and MGF1 with `hs[g]` is constant
time (`mgfXorAny_ct`): `signEncAny_ct`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64 VG.Impl.RsaPss.X86_64.AnyHash
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)
open VG.Proof.Dispatch.X86_64 (FlagsOnly)

variable {G : Spec.Mgf1.Hash} {k g : Nat} {H : Hash}

theorem sea_flags {ks : List Nat} {X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop} {a t t' : State}
    (h : SAtA G k g (SEA H ks X) a t) (hf : FlagsOnly t t') : SAtA G k g (SEA H ks X) a t' := by
  obtain ⟨s, S, v, hrd, hM, hok⟩ := h
  have kk : Keep [] t t' := ⟨fun r _ => hf.gpr r, hf.rd, hf.wr⟩
  exact ⟨s, S, v.keep kk hf.mem (by decide) (fun _ hp => by cases hp), hf.rd.trans hrd, hf.mem ▸ hM, hok⟩

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH)

include hH K in
theorem signPre_ct (hc : PssChecks H.P H.D) :
    RelCT isa (Two (SAtA lk.G k g (SEA H KSMA fun _ _ _ => True))) (signPre H)
      (Two (SAtA lk.G k g (SEA H KSMA fun _ _ _ => True))) := by
  unfold signPre
  simp only [seqs]
  exact RelCT.assoc ((scyd_ctA hH lk hc.sign).seq ((copySaltY_ctA hH lk hc.sign).seq
    ((signLen_ctA hH hc.sign).seq ((shash_ctA hH K hc.hash2).seq (sclearEm_ctA.seq ((sputSalt_ctA hH lk).seq
      (sputH_ctA hH hc.sign)))))))

include hH K in
/-- The dispatch on the digest's hash function. -/
theorem signPreD_ct {hs : List Hash} (hkh : k < hs.length) (hl : hs.length ≤ 2 ^ 31) (hkH : hs[k] = H)
    (hc : PssChecks H.P H.D) :
    RelCT isa (Two (SAtA lk.G k g (SEA H KSMA fun _ _ _ => True))) (dispatch sHsel signPre hs)
      (Two (SAtA lk.G k g (SEA H KSMA fun _ _ _ => True))) := by
  obtain ⟨_, hsel⟩ := sFixedA.selH
  refine dispatch_relCT (Ψ := SAtA lk.G k g (SEA H KSMA fun _ _ _ => True)) hkh hl
    (stwoA (G := lk.G) (H := H) [47] [] (fun _ => []) (fun a t h => se_ssA h _) (fun _ => rfl) (by decide) hsel)
    (fun a t h => ?_) ?_
  · obtain ⟨s, S, v, hrd, hM, hok⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    have h47 : W 47 = BitVec.ofNat 64 k := (hw 47 (by decide)).trans (by simp only [swA, S.hsel_eq])
    have L := v.L
    have hr : t.mem.readW (off (fb s) sHsel) 64 = BitVec.ofNat 64 k := by
      rw [R.rd (d := sHsel) 47 rfl (by decide), h47]
    refine WP.mono (WP.keep [.rax] (Q := fun u => u.gpr .rax = BitVec.ofNat 64 k ∧ u.mem = t.mem) ?_ rfl)
      fun u ⟨⟨hax, hm⟩, kk⟩ => ⟨⟨s, S, v.keep kk hm (by decide) (fun _ hp => by cases hp), kk.2.1.trans hrd,
        hm ▸ hM, hok⟩, hax⟩
    xrun [ea_sp, L.rsp, L.ld (d := sHsel) (by decide), hr]
  · rw [hkH]
    exact (signPre_ct hH K lk hc).mono (fun _ _ ⟨a, ⟨_, h₁, f₁⟩, ⟨_, h₂, f₂⟩⟩ =>
      ⟨a, sea_flags h₁ f₁, sea_flags h₂ f₂⟩) fun _ _ h => h

include hH in
/-- MGF1, with the hash function `hs[g]`. -/
theorem smgfAny_ct {hs : List Hash} (hg : g < hs.length) (hl : hs.length ≤ 2 ^ 31) (ht : TierOk hs) (hG : HashOK hs[g])
    (KG : Callees hs[g]) (lkG : MgfLink hs[g] hG) (hcg : PssChecks hs[g].P hs[g].D) :
    RelCT isa (Two (SAtA lk.G k g (SEA H KSMA fun _ _ _ => True))) (mgfXorAny hs)
      (Two (SAtA lk.G k g (SEA H KSMA fun _ _ _ => True))) := by
  have hD := hH.hD0
  have hDN := hH.hDN
  have hN := hH.N_le
  have hGv := validG hG lkG.hash lkG.len
  refine two_post (two_map (smgfAnyA H) (fun a t h => se_mea hD (by omega) lk.len h)
    (mgfXorAny_ct 2 H.D lkG.G hg hG KG hl lkG.hash lkG.len hGv hcg.hash2 (fixedChecks (.inr rfl))
      (anyMgfChecks (.inr rfl)))) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have := slo_le s
  have h15 : W 15 = BitVec.ofNat 64 H.D := (hw 15 (by decide)).trans (by
    simp only [swA]; rw [← lk.len, ← hp.hdl, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have h48 : W 48 = BitVec.ofNat 64 g := (hw 48 (by decide)).trans (by simp only [swA, S.msel_eq])
  exact WP.mono (WP.keepIn (mgfXorAny_safe ht) (mgfXorAny_xd ht)
    (mgfXorAny_ok hg hl hG KG lkG.hash lkG.len hGv v.L R (e := oEm + slo s) (db := sdb H.D s)
      ⟨by omega_arith, by unfold sdb; omega_arith, by unfold sdb seml at *; unfold oEm; omega_arith⟩ hD
      (by omega) (hw 23 (by decide)) (hw 24 (by decide)) h15 h48)) fun u ⟨⟨L', rd', wr', _, V', W', R', hW', _⟩, f⟩ =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (ksm_ltA hk) (by
      simp only [KSMA, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_arith)).trans (hw k hk), trivial⟩,
      fun _ hp => by cases hp⟩, rd'.trans hrd, frame_keepA hp v.wr v.L.rsp hM f, hok⟩

include hH K in
theorem signEncAny_ct {hs : List Hash} (hkh : k < hs.length) (hg : g < hs.length) (hl : hs.length ≤ 2 ^ 31)
    (ht : TierOk hs) (hkH : hs[k] = H) (hc : PssChecks H.P H.D) (hG : HashOK hs[g]) (KG : Callees hs[g])
    (lkG : MgfLink hs[g] hG) (hcg : PssChecks hs[g].P hs[g].D) :
    RelCT isa (Two fun a t => SAtA lk.G k g (SJ6A H) a t ∧ isa.eval .b t = some false) (AnyHash.signEnc hs)
      (Two (SAtA lk.G k g (SEA H KSMA fun _ _ _ => True))) := by
  unfold AnyHash.signEnc
  simp only [seqs]
  exact sdb_ctA.seq ((signPreD_ct hH K lk hkh hl hkH hc).seq ((smgfAny_ct hH lk hg hl ht hG KG lkG hcg).seq
    sclearTop_ctA))

end VG.Proof.RsaPss.X86_64.Any
