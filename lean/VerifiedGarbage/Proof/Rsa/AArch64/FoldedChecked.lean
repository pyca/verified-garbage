module

public import VerifiedGarbage.Proof.Rsa.AArch64.PdChecked
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
public import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedPhaseCT
public import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.PdCT
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedFinish
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedDispatch
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedFixed
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedExp

/-! ### `Bignum.AArch64.FoldedCode`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.FoldedMain`, which this module and modules that import it used -/

section

/-! ### `Bignum.AArch64.FoldedPhase`, which this module and modules that import it used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Both routes finish in ordinary form. The equality of the encoded base
with the ordinary input is only needed for the arithmetic result, not for
safety on malformed cached Montgomery data. -/
theorem phase_ok (M : Mont) {s : State} {B ep : Addr} {Z w N X x u L : Nat} {mi : BitVec 64}
    {eb : List Byte} (hc : ExpCtx s B Z w mi N X) (hZ : slot w 8 ≤ Z)
    (hw : 2 ≤ w) (hw' : w < 2^31) (hR : Nat.Coprime (2^(64*w)) N) (hN : 1 < N)
    (hX : X < N) (hx : X % N = x * 2^(64*w) % N)
    (hu : wv s.mem B (slot w aX) w = u) (hone : wv s.mem B (slot w aOne) w = 1)
    (he : word s.mem B (8*sE) = ep) (hlen : word s.mem B (8*sElen) = BitVec.ofNat 64 L)
    (hs : Src s B Z ep eb) (hel : eb.length = L) (hL1 : 1 ≤ L) (hL : L < 2^31) :
    WP isa (.seq (Folded.fastLoop M.mm) (Folded.finishFused M.mm)) s fun t =>
      Good t B Z w mi ∧ wv t.mem B (slot w aY) w < N ∧
      (x % N = u % N → wv t.mem B (slot w aY) w = u^Spec.Rsa.os2ip eb % N) ∧
      Frm B (pExpRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hMod (r : Nat) : r % N < N := Nat.mod_lt r (by omega_using [hN])
  have hFactor (e : Nat) (hxu : x % N = u % N) :
      x^e * u % N = u^(e+1) % N := factor_congr hxu
  have hb : B.toNat + slot w 8 ≤ 2^64 := by have := hc.good.scr.nowrap; omega_using [hZ, this]
  apply WP.seq
  apply fastLoop_dispatch M hc.good hZ hL he hlen hs hel
  · intro a hm ka _ h65
    have ca := hc.mem hm ka (by decide)
    refine WP.mono (fixedLoop_ok M (x := x) (u := u) ca hZ hw hw' hR hX hx (by rw [hm]; exact hu))
      fun b ⟨cb,yb,mb,fb,kb⟩ => ?_
    refine WP.mono (finish_fast_ok M cb.good hZ mb) fun t ⟨mt,kt⟩ => ?_
    have ct := cb.mem mt kt (by decide)
    refine ⟨ct.good, ?_, ?_, ?_, ((ka.trans kb).trans kt).mono (by decide)⟩
    · rw [mt,yb]; exact hMod (x^65536*u)
    · intro hxu
      rw [mt,yb,h65]
      have hf := hFactor 65536 hxu
      simp only [show (65536:Nat)+1=65537 from rfl] at hf
      exact hf
    · rw [hm] at fb
      rw [mt]
      exact fb
  · intro a hm ka _
    have ca := hc.mem hm ka (by decide)
    have hsa := hs.congrK (by rw [hm]; exact InScr.refl _ _ _) ka
    refine WP.mono (pExpLoop_ok (M := M) (x := x) ca hZ hw hw' hR hX hx
      (by rw [hm]; exact he) (by rw [hm]; exact hlen) hel hL1 hL
      (fun i hi => hsa.rd i (by omega_using [hel, hi])) (fun i hi => hsa.val i (by omega_using [hel, hi]))
      (fun i hi => hsa.out i (by omega_using [hel, hi]))) fun b ⟨cb,yb,fb,kb⟩ => ?_
    have ob : wv b.mem B (slot w aOne) w = 1 := by
      rw [one_preserved fb hb,hm]; exact hone
    refine WP.mono (finish_slow_ok M cb hZ hw hw' hR hN ob yb) fun t ⟨gt,yt,ft,kt⟩ => ?_
    refine ⟨gt, ?_, ?_, ?_, ((ka.trans kb).trans kt).mono (by decide)⟩
    · rw [yt]; exact hMod _
    · intro hxu
      rw [yt,Nat.pow_mod,hxu,← Nat.pow_mod]
    · rw [hm] at fb
      exact fb.trans (ft.mono (by simp [finRanges,pExpRanges,pBitRanges,bitRanges]))

end VG.Proof.Bignum.AArch64.FoldedPublic

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def phases (M : Mont) : List (Prog isa) :=
  [M.mm aXm aX aR2, Folded.fastLoop M.mm, Folded.finishFused M.mm]

theorem rest_eq (M : Mont) : Folded.rest M.mm =
    seqs ((([.block [ldh .x1 sIn, ldh .x2 sK, ldh .x8 (sArr aX)], loadW] : List (Prog isa)) ++ setupSteps) ++
      (phases M ++ outSteps)) := rfl

/-- Every accepted cache is memory-safe. A valid cache additionally gives the
specified numerical result, including the existing invalid-input mask. -/
theorem rest_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op ep ip : Addr}
    {L : Nat} {eb xb : List Byte} {N R : Nat}
    (h : PdPre s B Z k op ep ip L eb xb N R) :
    WP isa (Folded.rest M.mm) s fun t => ∃ y : Nat,
      (R % N = 2^(64*((k+7)/8)) * 2^(64*((k+7)/8)) % N →
        y = Spec.Rsa.os2ip xb ^ Spec.Rsa.os2ip eb % N) ∧
      MainPost s t B Z k op (if Spec.Rsa.os2ip xb < N then y else 0)
        (decide (Spec.Rsa.os2ip xb < N)) := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hL2 := h.L2
  have hZ := h.z
  have hs := h.scr
  have hn := hs.nowrap
  obtain hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
  obtain hw : 2 ≤ (k + 7) / 8 := by omega_using [hk1]
  obtain hR : Nat.Coprime (2 ^ (64 * ((k + 7) / 8))) N := VG.Proof.Bignum.coprime_pow2 h.odd _
  obtain hle := pdAll_le ((k + 7) / 8)
  obtain hle' : ∀ r ∈ pdAll ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr => Nat.le_trans (hle r hr) hZ
  rw [rest_eq]
  refine wp_seqs_append (by simp) (by simp [phases])
    (WP.mono (pdSetupAll_ok h) fun t₂ ⟨minv, so, f₂, k₂, hR₂⟩ => ?_)
  refine wp_seqs_append (by simp [phases]) (by simp [outSteps]) ?_
  unfold phases
  -- `X = input R`.
  refine WP.seq (WP.mono (M.mm_ok (o := aXm) (a := aX) (b := aR2) so.good hZ hw (by omega_using [hk2]) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) so.inv (by rw [hR₂, so.n]; exact h.rlt))
    fun t₃ ⟨hg₃, hlt₃, hm₃, ha₃, k₃⟩ => ?_)
  rw [so.n] at hlt₃ hm₃
  rw [so.x, hR₂] at hm₃
  obtain hn₃ : wv t₃.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = N := by
    rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact so.n
  obtain hinv₃ : ((word t₃.mem B (slot ((k + 7) / 8) aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [ha₃.word0_of_not_mem (by decide) (by decide) hn' (by omega_using [hw])]; exact so.inv
  obtain f₃ : Frm B (pdAll ((k + 7) / 8)) t₂.mem t₃.mem :=
    Frm.of_arrays ha₃ (by simp [pdAll, pExpRanges, pBitRanges, bitRanges])
  obtain f₁₃ := f₂.trans f₃
  obtain x₁₃ := Fixed.of_frm f₁₃ (pdAll_fixed _)
  obtain ⟨x, hx⟩ := exists_mont hR h.n1 (wv t₃.mem B (slot ((k + 7) / 8) aXm) ((k + 7) / 8))
  obtain he₃ := h.e.congrK (InScr.of_frm f₁₃ hle') (k₂.trans k₃)
  obtain input3 : wv t₃.mem B (slot ((k+7)/8) aX) ((k+7)/8) = Spec.Rsa.os2ip xb := by
    rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact so.x
  obtain one3 : wv t₃.mem B (slot ((k+7)/8) aOne) ((k+7)/8) = 1 := by
    rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact so.one
  change WP isa (.seq (Folded.fastLoop M.mm) (Folded.finishFused M.mm)) t₃ _
  refine WP.mono (phase_ok M (x := x) ⟨hg₃,hn₃,hinv₃,rfl⟩ hZ hw (by omega_using [hk2]) hR h.n1 hlt₃ hx
    input3 one3 (by rw [x₁₃ sE (by decide)]; exact h.hE)
    (by rw [x₁₃ sElen (by decide)]; exact h.hL) he₃ h.el h.L1 (by omega_using [hk2, hL2]))
    fun t₄ ⟨hg₄,hy₄,y₄,f₄',k₄⟩ => ?_
  obtain f₄ : Frm B (pdAll ((k+7)/8)) t₃.mem t₄.mem :=
    f₄'.mono fun _ hr => List.mem_append_right _ hr
  obtain f₁₄ := f₁₃.trans f₄
  obtain x₁₄ := Fixed.of_frm f₁₄ (pdAll_fixed _)
  obtain k₁₄ := (k₂.trans k₃).trans k₄
  obtain mask4 : word t₄.mem B (8*sMask) = mask (decide (Spec.Rsa.os2ip xb < N)) := by
    rw [f₄'.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (by unfold sMask sFn; omega_using []),ha₃.hslot (by decide)]
    exact so.mask
  refine WP.mono (outPhase_ok hg₄ hZ (by omega_using [hk1]) (by omega_using [hk2]) rfl
    (by rw [x₁₄ sOut (by decide)]; exact h.hO)
    (by rw [x₁₄ sK (by decide)]; exact h.hK) mask4
    (by rw [k₁₄.wr]; exact h.out) h.outSep)
    fun t ⟨bytes,ret,frame,kt⟩ => ⟨wv t₄.mem B (slot ((k+7)/8) aY) ((k+7)/8),?_,⟨?_,ret,
      fun a ha ha' => by rw [frame a ha',InScr.of_frm f₁₄ hle' a ha],
      (k₁₄.trans kt).mono (by decide)⟩⟩
  · intro hRR
    exact y₄ (encoded_base hR hx hm₃ hRR)
  · rw [bytes]
    by_cases hc : Spec.Rsa.os2ip xb < N <;> simp [hc]

end VG.Proof.Bignum.AArch64.FoldedPublic

end

end

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Rsa.AArch64

theorem code_correct (M : Mont) (s : State) (h : pdContract.pre s) :
    ∃ t s', Exec isa (Folded.code M.mm) s t s' ∧ abiPreserved s s' ∧ pdContract.post s s' :=
  pdCodeWith_correct (Folded.rest M.mm) (rest_ok M) s h

end VG.Proof.Bignum.AArch64.FoldedPublic

end

end

/-! ### `Bignum.AArch64.FoldedCodeCT`, which only this module used -/

section

/-! ### `Bignum.AArch64.FoldedRestCT`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem publicPhase_ct (M : Mont) : RelCT isa (Two DB)
    (.seq (Folded.fastLoop M.mm) (Folded.finishFused M.mm)) (Two DD) := by
  refine two_post (two_map DPub.E (fun _ _ h => db_pre h) (phase_ct M)) ?_
  intro q s h
  obtain ⟨X,x,hc,hf,he,hl,hL,hs⟩ := db_pre h
  obtain ⟨xb,σ,g,_,_,_,_,hone⟩ := h
  have src : Src s q.1.B q.1.Z q.1.ep q.1.eb :=
    ⟨fun i hi => hs.2.2.1 i (by rw [← hs.1]; exact hi),
     fun i hi => hs.bytes i (by rw [← hs.1]; exact hi),
     fun i hi => hs.2.2.2.2 i (by rw [← hs.1]; exact hi)⟩
  refine WP.mono (phase_ok M hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 g.1.n1
    hf.2.2.2.2.1 hf.2.2.2.2.2 rfl hone he hl src hs.1 hL hs.2.1)
    fun t ⟨gt,_,_,ft,kt⟩ => ?_
  exact ⟨xb,σ,g.step (ft.mono (pExpRanges_pdAll _)) kt
    (ft.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (by unfold sMask sFn; omega_using [])),gt⟩

theorem rest_ct (M : Mont) : RelCT isa (Two DRel) (Folded.rest M.mm) (fun _ _ => True) := by
  rw [rest_eq]
  refine RelCT.seqs_append (by simp) (by simp [phases]) (RelCT.seq pdSetup_ct ?_)
  refine RelCT.seqs_append (by simp [phases]) (by simp [outSteps]) (RelCT.seq (R := Two DD) ?_ ?_)
  · exact RelCT.seq pdMm_ct (publicPhase_ct M)
  · exact two_map (fun q => (⟨DPub.L q,q.1.k,q.1.op⟩ : OPub)) (fun _ _ h => dd_oPre h) out_ct

end VG.Proof.Bignum.AArch64.FoldedPublic

end

end


@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Rsa.AArch64

theorem code_constantTime (M : Mont) :
    ConstantTime isa pdContract.pre pdContract.pub (Folded.code M.mm) :=
  pdCodeWith_constantTime (Folded.code M.mm) (pdCodeWith_ct (Folded.rest M.mm) (rest_ct M))

end VG.Proof.Bignum.AArch64.FoldedPublic

end

end


@[expose] public section
namespace VG.Proof.Rsa.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Checked
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64

theorem checked_correct (M : Mont) (s : State) (h : pdContract.pre s) :
    ∃ t s', Exec isa (Folded.checked M.mm) s t s' ∧ abiPreserved s s' ∧ pdChkContract.post s s' := by
  refine guarded_correct (VG.Proof.Bignum.AArch64.FoldedPublic.code_correct M) (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h)
    ?_ ?_ s h
  · intro s t s' _ hs hv hp nB hl hpre
    simp only [pdContract, hs.x0, hs.x1, hs.x2, hs.x3, hs.x4, hs.x5, hs.x6, hs.mem] at hp
    simp only [eValid, eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, ↓reduceIte]
    exact hp nB hl hpre
  · intro s s' h hv hb hax nB _ _
    simp only [eValid, eBytes] at hv
    simp only [Spec.Rsa.publicOpChecked, hv, Bool.false_eq_true, ite_false, Spec.Rsa.written, hax]
    exact ⟨rfl, hb⟩

theorem checked_constantTime (M : Mont) :
    ConstantTime isa pdContract.pre pdContract.pub (Folded.checked M.mm) :=
  guarded_ct (VG.Proof.Bignum.AArch64.FoldedPublic.code_constantTime M) (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h)
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.2.1
      · exact hp.2.2.1
      · exact hp.2.2.2.2.2.1
      · exact hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    fun _ _ _ _ h₁ h₂ hp => pdPub_same h₁ h₂ hp

theorem checked_verified (M : Mont) :
    Verified target (Folded.checked M.mm) (Proof.Rsa.publicPrecomputedCheckedContract abi) :=
  have hct : ConstantTime isa pdChkContract.pre pdChkContract.pub (Folded.checked M.mm) :=
    checked_constantTime M
  Verified.of_correct (k := pdChkContract) (checked_correct M) hct precomputedChecked_implies

end VG.Proof.Rsa.AArch64.FoldedPublic
