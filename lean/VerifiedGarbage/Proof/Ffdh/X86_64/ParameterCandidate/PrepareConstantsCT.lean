module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareCTData
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Constants
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Montgomery
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Montgomery
public import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontSetup
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! ### `Ffdh.X86_64.ParameterCandidate.PrepareR2CT`, which the modules that import this one used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.PreparePrefix`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: public entry to the selected R² implementation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.RsaKeyGen.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem preparePrefix_ok {s : State} {B : Addr} {Z w N : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (seqs [.block prepareHead, setWord aOne .rcx, .block [.mov .r10 (.mem (hdr (sArr aN)))]]) s
      fun t => ∃ mi', R2Pre ⟨⟨B, Z, w, mi'⟩, N⟩ t ∧ Keep mmRegs s t := by
  have hnw := hg.scr.nowrap
  have hO8 := Nat.le_trans (slot_le (w := w) (show aOne < 8 by decide)) hZ
  have hw31 : w < 2 ^ 31 := by omega_using [hw']
  have hN8 := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hodd0 : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 (n := w) _ _ _ (by omega_using [hw]), hn, Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide)]
    exact hodd
  simp only [seqs]
  refine WP.seq (WP.mono (msHead_ok hg hZ hodd0) fun s₁ ⟨hg₁, hinv₁, _, hcx₁, h12₁, hm₁, k₁⟩ => ?_)
  generalize hmi : s₁.gpr .r15 = mi' at hg₁ hinv₁ hm₁
  have hn₁ : wv s₁.mem B (slot w aN) w = N := by
    rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) (by omega_using [hZ, hnw])]; exact hn
  have hw0₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [hm₁, hdrStore_word _ _ _ (by decide) (by decide) (by omega_using [hZ, hnw])]
  refine WP.seq (WP.mono (setWord_ok hg₁.scr hg₁.rdi hg₁.hdr hZ h12₁ (by omega_using [hw]) hw31 (o := aOne) (by decide) (ri := .rcx)
    (by decide) (i := 0) (by omega_using [hw]) hcx₁) fun s₂ ⟨_, ho₂, k₂⟩ => ?_)
  have ha₂ : Arrays B w [aOne] s₁.mem s₂.mem := Arrays.of_outside (List.mem_singleton_self _) ho₂ (Nat.le_refl _) (Nat.le_refl _)
  have hg₂ : Good s₂ B Z w mi' := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, ha₂.hdr hg₁.hdr⟩
  have hn₂ : wv s₂.mem B (slot w aN) w = N := by rw [ha₂.wv_of_not_mem (by decide) (by decide) (by omega_using [hZ, hnw])]; exact hn₁
  have hw0₂ : word s₂.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [ha₂.word0_of_not_mem (by decide) (by decide) (by omega_using [hZ, hnw]) (by omega_using [hw])]; exact hw0₁
  have hl : InRegions (s₂.rd ++ s₂.wr) (off B (8 * sArr aN)) 8 :=
    hg₂.scr.ld (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega_using [hZ, this])
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w aN) ∧ t.mem = s₂.mem)
    (by xrun [State.ea, hdr, hg₂.rdi, hdrOff, hl, hg₂.hdr.harr aN (by decide)]) rfl)
    fun t ⟨⟨h10, hm⟩, k⟩ => ?_
  have hgt : Good t B Z w mi' := ⟨hg₂.scr.congr k.2.2, (k.gpr (by decide)).trans hg₂.rdi, by rw [hm]; exact hg₂.hdr⟩
  exact ⟨mi', ⟨⟨hgt, hZ⟩, hw, hw', by rw [hm]; exact hn₂,
    by rw [hm, hw0₂]; exact hinv₁,
    ((k.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12₁)), h10, hodd, hlo⟩,
    ((k₁.trans k₂).trans k).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: timing of inverse and R² setup -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.MlKem.X86_64

def R2Entry (d : PreparePublic) (s : State) : Prop := ∃ mi, R2Pre ⟨⟨d.I, d.IZ, d.w, mi⟩, d.N⟩ s

private theorem prefix_entry (d : PreparePublic) (s : State) (h : PrepareBefore d s) :
    WP isa (seqs [.block prepareHead, setWord aOne .rcx, .block [.mov .r10 (.mem (hdr (sArr aN)))]]) s (R2Entry d) := by
  obtain ⟨⟨mi, hg, hd, _, _, _⟩, hn, ho, _, hlo⟩ := h
  exact WP.mono (preparePrefix_ok hg hd.z (by omega_using [hd.w4]) (by omega_using [hd.w128]) hn ho hlo)
    fun _ ⟨mi', hp, _⟩ => ⟨mi', hp⟩

private theorem entry_r2 {s₁ s₂ : State} (h : Two R2Entry s₁ s₂) : Two R2Pre s₁ s₂ := by
  refine two_bind (fun d t₁ t₂ h₁ h₂ => ?_) h
  obtain ⟨mi₁, hr₁⟩ := h₁
  obtain ⟨mi₂, hr₂⟩ := h₂
  have hr₁keep := hr₁
  have hr₂keep := hr₂
  obtain ⟨_, hw, _, hn₁, hi₁, _, _, ho, _⟩ := hr₁
  obtain ⟨_, _, _, hn₂, hi₂, _, _, _, _⟩ := hr₂
  change 2 ≤ d.w at hw
  have he₁ : (word t₁.mem d.I (slot d.w aN)).toNat = d.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := d.w) _ _ _ (by omega_using [hw]), hn₁]
  have he₂ : (word t₂.mem d.I (slot d.w aN)).toNat = d.N % 2 ^ 64 := by
    rw [← wv_mod64 (n := d.w) _ _ _ (by omega_using [hw]), hn₂]
  rw [he₁] at hi₁
  rw [he₂] at hi₂
  have heq := minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact ho) hi₁ hi₂
  cases heq
  exact ⟨_, hr₁keep, hr₂keep⟩

theorem prepareR2_ct (M : Mont) (R : R2Impl M) :
    RelCT isa (Two PrepareBefore) (prepareR2 R.code) fun _ _ => True := by
  unfold prepareR2
  refine RelCT.seqs_append (a := [.block prepareHead, setWord aOne .rcx,
      .block [.mov .r10 (.mem (hdr (sArr aN)))]]) (b := [R.code]) (by simp) (by simp) ?_
  exact RelCT.seq (two_post
    (two_map PreparePublic.inner (fun _ _ h => h.1.header) inner_preparePrefix_ct) prefix_entry)
    (R.ct.mono (fun _ _ h => entry_r2 h) (fun _ _ h => h))

theorem prepareR2_ready (M : Mont) (R : R2Impl M) (d : PreparePublic) (s : State) (h : PrepareBefore d s) :
    WP isa (prepareR2 R.code) s (R2Ready d) := by
  obtain ⟨⟨mi, hg, hd, hz, hw, hk⟩, hn, ho, hN, hlo⟩ := h
  refine WP.mono (prepareR2_ok M R hg hd.z (by omega_using [hd.w4])
    (by omega_using [hd.w128]) hn ho hlo) fun t ⟨mi', ht, hinv, hnt, hone, hr2, _, _, k⟩ => ?_
  exact ⟨mi', ht, hd, hz, k.2.2.trans hw, hk, hinv, hnt, hone, hr2, ho, hN⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! # FFDH parameter generation on x86-64: timing of Montgomery constants -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen.X86_64

private theorem multiply_header (M : Mont) (d : PreparePublic) (s : State) (h : R2Ready d s) :
    WP isa (M.mm aY aR2 aOne) s (HeaderGood d) := by
  obtain ⟨mi, hg, hd, hz, hw, hk, hi, hn, hone, _, _, hN⟩ := h
  refine WP.mono (M.mm_ok hg hd.z (by omega_using [hd.w4]) (by omega_using [hd.w128])
    (o := aY) (a := aR2) (b := aOne) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hi (by rw [hone, hn]; exact hN))
    fun t ⟨ht, _, _, _, k⟩ => ?_
  exact ⟨mi, ht, hd, hz, k.2.2.trans hw, hk⟩

private theorem copy_header (d : PreparePublic) (s : State) (h : HeaderGood d s) :
    WP isa copyR1 s (HeaderGood d) := by
  obtain ⟨mi, hg, hd, hz, hw, hk⟩ := h
  have hfit : slot d.w aR1 + 8 * (d.w + 2) ≤ d.IZ := by
    simp only [slot, aR1] at hz ⊢; omega_using [hz]
  refine WP.mono (copyToExt_ok hg hd.z (by omega_using [hd.w4]) (by omega_using [hd.w128])
    (a := aY) (d := aR1) (by decide) (by decide) hfit) fun t ⟨_, hf, k⟩ => ?_
  exact ⟨mi, ⟨hg.scr.congr k.2.2, (k.gpr (by decide)).trans hg.rdi,
    hg.hdr.outside hf (by unfold slot; omega_using [])⟩, hd, hz, k.2.2.trans hw, hk⟩

theorem prepareConstants_ct (M : Mont) :
    RelCT isa (Two R2Ready) (prepareConstants M.mm) fun _ _ => True := by
  unfold prepareConstants
  refine RelCT.seq (two_post
    (two_map (fun d : PreparePublic => (⟨d.I, d.IZ, d.w⟩ : Ws)) (fun _ _ h => by
      obtain ⟨mi, hg, hd, _, _, _, _⟩ := h; exact ⟨mi, hg, hd.z⟩)
      (M.ct (o := aY) (a := aR2) (b := aOne) (by unfold MmUse; decide))) (multiply_header M)) ?_
  exact RelCT.seq (two_post
    (two_map PreparePublic.inner (fun _ _ h => h.header) inner_copyR1_ct) copy_header)
    (two_map PreparePublic.inner (fun _ _ h => h.header) inner_negateR1_ct)

theorem prepareConstants_header (M : Mont) (d : PreparePublic) (s : State) (h : R2Ready d s) :
    WP isa (prepareConstants M.mm) s (HeaderGood d) := by
  obtain ⟨mi, hg, hd, hz, hw, hk, hi, hn, hone, hr2, ho, hN⟩ := h
  have hfit : slot d.w aRm1 + 8 * (d.w + 2) ≤ d.IZ := by simp only [slot, aRm1] at hz ⊢; omega_using [hz]
  refine WP.mono (prepareConstants_ok M hg hd.z hfit (by omega_using [hd.w4])
    (by omega_using [hd.w128]) hn hi hone ho hN hr2) fun t ⟨ht, _, _, _, k⟩ => ?_
  exact ⟨mi, ht, hd, hz, k.2.2.trans hw, hk⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
