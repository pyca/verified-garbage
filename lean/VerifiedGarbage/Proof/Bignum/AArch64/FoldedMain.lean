module

import VerifiedGarbage.Proof.Bignum.AArch64.FoldedPhase
public import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def phases (M : Mont) : List (Prog isa) :=
  [M.mm aXm aX aR2, Folded.fastLoop M.mm, Folded.finishFused M.mm]

theorem rest_eq (M : Mont) : Folded.rest M.mm =
    seqs ((([.block [ldh .x1 sIn, ldh .x2 sK, ldh .x8 (sArr aX)], loadBE] : List (Prog isa)) ++ setupSteps) ++
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
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_using [hZ, hn]
  have hw : 2 ≤ (k + 7) / 8 := by omega_using [hk1]
  have hR : Nat.Coprime (2 ^ (64 * ((k + 7) / 8))) N := VG.Proof.Bignum.coprime_pow2 h.odd _
  have hle := pdAll_le ((k + 7) / 8)
  have hle' : ∀ r ∈ pdAll ((k + 7) / 8), r.1 + r.2 ≤ Z := fun r hr => Nat.le_trans (hle r hr) hZ
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
  have hn₃ : wv t₃.mem B (slot ((k + 7) / 8) aN) ((k + 7) / 8) = N := by
    rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact so.n
  have hinv₃ : ((word t₃.mem B (slot ((k + 7) / 8) aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [ha₃.word0_of_not_mem (by decide) (by decide) hn' (by omega_using [hw])]; exact so.inv
  have f₃ : Frm B (pdAll ((k + 7) / 8)) t₂.mem t₃.mem :=
    Frm.of_arrays ha₃ (by simp [pdAll, pExpRanges, pBitRanges, bitRanges])
  have f₁₃ := f₂.trans f₃
  have x₁₃ := Fixed.of_frm f₁₃ (pdAll_fixed _)
  obtain ⟨x, hx⟩ := exists_mont hR h.n1 (wv t₃.mem B (slot ((k + 7) / 8) aXm) ((k + 7) / 8))
  have he₃ := h.e.congrK (InScr.of_frm f₁₃ hle') (k₂.trans k₃)
  have input3 : wv t₃.mem B (slot ((k+7)/8) aX) ((k+7)/8) = Spec.Rsa.os2ip xb := by
    rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact so.x
  have one3 : wv t₃.mem B (slot ((k+7)/8) aOne) ((k+7)/8) = 1 := by
    rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact so.one
  change WP isa (.seq (Folded.fastLoop M.mm) (Folded.finishFused M.mm)) t₃ _
  refine WP.mono (phase_ok M (x := x) ⟨hg₃,hn₃,hinv₃,rfl⟩ hZ hw (by omega) hR h.n1 hlt₃ hx
    input3 one3 (by rw [x₁₃ sE (by decide)]; exact h.hE)
    (by rw [x₁₃ sElen (by decide)]; exact h.hL) he₃ h.el h.L1 (by omega))
    fun t₄ ⟨hg₄,hy₄,y₄,f₄',k₄⟩ => ?_
  have f₄ : Frm B (pdAll ((k+7)/8)) t₃.mem t₄.mem :=
    f₄'.mono fun _ hr => List.mem_append_right _ hr
  have f₁₄ := f₁₃.trans f₄
  have x₁₄ := Fixed.of_frm f₁₄ (pdAll_fixed _)
  have k₁₄ := (k₂.trans k₃).trans k₄
  have mask4 : word t₄.mem B (8*sMask) = mask (decide (Spec.Rsa.os2ip xb < N)) := by
    rw [f₄'.word_eq (pExpRanges_hdr _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (by unfold sMask sFn; omega),ha₃.hslot (by decide)]
    exact so.mask
  refine WP.mono (outPhase_ok hg₄ hZ (by omega) (by omega) rfl
    (by rw [x₁₄ sOut (by decide)]; exact h.hO)
    (by rw [x₁₄ sK (by decide)]; exact h.hK) mask4
    (fun j hj => by rw [k₁₄.wr]; exact h.out j hj) h.outSep)
    fun t ⟨bytes,ret,frame,kt⟩ => ⟨wv t₄.mem B (slot ((k+7)/8) aY) ((k+7)/8),?_,⟨?_,ret,
      fun a ha ha' => by rw [frame a ha',InScr.of_frm f₁₄ hle' a ha],
      (k₁₄.trans kt).mono (by decide)⟩⟩
  · intro hRR
    exact y₄ (encoded_base hR hx hm₃ hRR)
  · rw [bytes]
    by_cases hc : Spec.Rsa.os2ip xb < N <;> simp [hc]

end VG.Proof.Bignum.AArch64.FoldedPublic
