module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PrepareCTData
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PreparePrefix
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Montgomery
import VerifiedGarbage.Proof.Bignum.Octets

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
