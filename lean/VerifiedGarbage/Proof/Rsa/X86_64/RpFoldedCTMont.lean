module

public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT3
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedCTPrepare
public import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCst
import VerifiedGarbage.Proof.Rsa.X86_64.RpMont
import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCT2
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpCst
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpMont
meta import VerifiedGarbage.Proof.Rsa.X86_64.RpFrame
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.X86_64.RpCT4
import VerifiedGarbage.Proof.Rsa.X86_64.RpFoldedPrepare
public import VerifiedGarbage.Impl.Rsa.X86_64.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.RecoverFolded
public import VerifiedGarbage.Proof.Rsa.X86_64.RpCT2

/-! # Preparation and Montgomery constants for folded recovery -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.RecoveryFolded

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aR2 aXm aY aOne sCnt)
open VG.Spec.Rsa (splitTwos)

open VG.Impl.Rsa.X86_64.Keys.Recover.Folded
open Rp

def GR1 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RpS I m₀ s ∧ RpLens I ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true ∧ I.N % 2 = 1 ∧ 2 ^ (64 * (wk I.k - 1)) ≤ I.N ∧
    wv s.mem I.B (slot (wk I.k) aN) (wk I.k) = I.N ∧
    ((word s.mem I.B (slot (wk I.k) aN)).toNat * (word s.mem I.B (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem I.B (slot (wk I.k) aM) (2 * (wk I.k + 2)) = (I.D * I.E - 1) / 2 ^ VG.Proof.Rsa.RecoveryFolded.sigma (splitTwos (I.D * I.E - 1)).1 ∧
    word s.mem I.B (8 * sT) = BitVec.ofNat 64 (VG.Proof.Rsa.RecoveryFolded.sigma (splitTwos (I.D * I.E - 1)).1) ∧
    0 < I.D * I.E - 1 ∧ (I.D * I.E - 1) % 2 = 0 ∧ I.D * I.E - 1 < 2 ^ (64 * (wk I.k + (I.el + 7) / 8))

theorem prepare_ct : RelCT isa (Two GR0) prepare (Two GR1) :=
  two_post prepareT_ct fun p s h => by
    obtain ⟨I, m₀, rfl, h, O, hv⟩ := h
    have L := h.L
    have hz : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := h.S.ws.scr.nowrap; have := h.S.ws.hZ; omega_arith
    refine WP.mono (prepare_ok h.S.ws h.S.args.el L.el1 (by have := L.el2; unfold wk; omega_arith)
      h.M h.m0 h.even h.mlt) fun t ⟨hM, hT, f, k⟩ => ?_
    refine ⟨I, m₀, rfl, h.S.step f (by decide) (by decide) k (by decide), L, O, hv, h.odd, h.lo,
      ?_, ?_, hM, hT, h.m0, h.even, h.mlt⟩
    · rw [f.rg_wv hz (by decide) (by decide) (by decide) (by omega_arith)]; exact h.n
    · rw [f.rg_word0 hz (by decide) (by decide) (by decide), f.rg_word (by decide) (by decide)]; exact h.inv

theorem montR2_ct (M : Mont) :
    RelCT isa (Two GR1) (.seq (.block [.mov .r12 (.mem (hdr sW)), .mov .r10 (.mem (hdr (sArr aN)))])
      (seqs (r2Steps M))) (Two MW) := by
  refine RelCT.seq (R := Two MR) ((two_piece (Ψ := fun p s => ∃ minv,
      MR ⟨⟨p.B, p.Z, wk p.k, minv⟩, Spec.Rsa.os2ip p.nb⟩ s) [.rdi]
    (fun _ _ _ ⟨_, _, e₁, h₁, _⟩ ⟨_, _, e₂, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ws.rdi, h₂.ws.rdi]
      exact (congrArg RpP.B e₁).trans (congrArg RpP.B e₂).symm) (by taint_decide) fun p s h => ?_).mono
    (fun _ _ h => h) fun _ _ h => two_bind mr_bind h) ?_
  · obtain ⟨I, m₀, rfl, S, L, O, hv, hodd, hlo, hn, hinv, -⟩ := h
    dsimp only [RpIn.pub]
    have hw := S.ws
    have hn0 := hw.scr.nowrap
    have h256 := hw.h256
    have hZ := hw.hZ
    have hw1 := hw.w1
    have hw2 := hw.w2
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off I.B (8 * i)) 8 := fun i hi => hw.scr.ld (by omega_arith)
    refine WP.mono (WP.keep [.r12, .r10] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 (wk I.k) ∧
        t.gpr .r10 = off I.B (slot (wk I.k) aN) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hw.rdi, hdrOff, hl _ (show sW < 32 by decide), hl _ (show sArr aN < 32 by decide),
        hw.hw, hw.harr aN (by decide)]) rfl) fun t ⟨⟨h12, h10, m₁⟩, k₁⟩ => ⟨word t.mem I.B (8 * sMinv), ?_⟩
    have hw₁ : Ws t I.B I.Z (wk I.k) :=
      hw.congrG (js := []) (hs := []) (by rw [m₁]; exact Frm.refl _ _ _) (by simp) k₁ (by decide)
    exact ⟨⟨hw₁.good, hw1, show wk I.k < 2 ^ 30 by omega_arith, by rw [m₁]; exact hn, by rw [m₁]; exact hinv, h12, h10, hodd, hlo⟩, hw₁, rfl⟩
  · refine two_post ((two_map id (fun _ _ h => h.1) (r2_ct M)).mono (fun _ _ h => h) fun _ _ _ => trivial)
      fun q s ⟨⟨hg, hw1, hw30, hn, hinv, h12, h10, hodd, hlo⟩, hw, hmv⟩ => ?_
    have hZ16 : slot q.L.w 16 ≤ 2 ^ 64 := by have := hw.scr.nowrap; have := hw.hZ; omega_arith
    have hN1 : 1 < q.N := by
      have : 2 ^ 64 ≤ 2 ^ (64 * (q.L.w - 1)) := Nat.pow_le_pow_right (by decide) (by omega_arith)
      omega_arith
    refine WP.mono (r2_ok M hg.1 hg.2 hw1 hw30 hn hinv h12 h10 hodd hlo) fun t ⟨hg₂, _, _, hf₂, k₂⟩ => ?_
    have hf₂' : Frm q.L.B (rg q.L.w [aAcc, aTmp, aR2] [sCnt]) s.mem t.mem := hf₂
    exact ⟨hw.congrG hf₂' (by decide) k₂ (by decide), hg₂.hdr.hminv,
      by rw [hf₂'.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_arith)]; exact hn,
      by rw [hf₂'.rg_word0 hZ16 (by decide) (by decide) (by decide)]; exact hinv, hN1⟩

theorem montT_ct (M : Mont) : RelCT isa (Two GR1) (seqs (mont M.mm)) fun _ _ => True := by
  rw [show mont M.mm = ([.block [.mov .r12 (.mem (hdr sW)), .mov .r10 (.mem (hdr (sArr aN)))]] ++ r2Steps M) ++
    [.block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0), .mov .r12 (.mem (hdr sW))],
      setWord aOne .rcx, M.mm aY aR2 aOne, copyA aO aY,
      .block (ws ++ base aN .r8 ++ base aO .r10 ++ base aNg .rsi ++ [.mov32 .rbp (.imm 0)]),
      wordLoop 0 subBody] from rfl]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (montR2_ct M) ?_)
  simp only [seqs]
  exact RelCT.seq montB_ct (RelCT.seq montSet_ct (RelCT.seq (montY_ct M) (RelCT.seq montO_ct montNg_ct)))

/-- After Montgomery form: what the candidates need. -/
def GR2 (p : RpP) (s : State) : Prop :=
  ∃ (I : RpIn) (m₀ : Mem), I.pub = p ∧ RpS I m₀ s ∧ RpLens I ∧ RpOuts I ∧
    Spec.Rsa.modulusValid I.N I.k = true ∧
    Cst s I.B I.Z (wk I.k) (word s.mem I.B (8 * sMinv)) I.N I.el ((I.D * I.E - 1) / 2 ^ VG.Proof.Rsa.RecoveryFolded.sigma (splitTwos (I.D * I.E - 1)).1)
      (VG.Proof.Rsa.RecoveryFolded.sigma (splitTwos (I.D * I.E - 1)).1) ∧ 0 < I.D * I.E - 1 ∧ (I.D * I.E - 1) % 2 = 0

theorem mont_ct (M : Mont) : RelCT isa (Two GR1) (seqs (mont M.mm)) (Two GR2) :=
  two_post (montT_ct M) fun p s h => by
    obtain ⟨I, m₀, rfl, S₁, L, O, hv, hodd, hlo, hn₁, hi₁, hr₁, ht₁, hm0, heven, hmlt⟩ := h
    have hk1 := L.k1
    have hel1 := L.el1
    have hel2 := L.el2
    have hZ16 : slot (wk I.k) 16 ≤ 2 ^ 64 := by have := S₁.ws.scr.nowrap; have := S₁.ws.hZ; omega_arith
    refine WP.mono (mont_ok M S₁.ws hi₁ hn₁ hodd hlo)
      fun s₂ ⟨_, hr2lt, hr2, hone, ho, hng, hf₂, k₂⟩ => ⟨I, m₀, rfl, ?_⟩
    have S₂ := S₁.step hf₂ (by decide) (by decide) k₂ (by decide)
    have hspl := VG.Proof.Rsa.splitTwos_spec hm0
    have hrlt : (I.D * I.E - 1) / 2 ^ VG.Proof.Rsa.RecoveryFolded.sigma (splitTwos (I.D * I.E - 1)).1 <
        2 ^ (64 * (wk I.k + (I.el + 7) / 8)) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hmlt
    have ht1 : 1 ≤ (splitTwos (I.D * I.E - 1)).1 := by
      rcases Nat.eq_zero_or_pos (splitTwos (I.D * I.E - 1)).1 with h0 | h0
      · have := hspl.1; rw [h0, Nat.pow_zero, Nat.one_mul] at this; have := hspl.2; omega_arith
      · exact h0
    have hsigma := VG.Proof.Rsa.RecoveryFolded.sigma_bounds (splitTwos (I.D * I.E - 1)).1
    refine ⟨S₂, L, O, hv, ⟨S₂.ws, rfl, ?_, ?_, hr2lt, hr2, hone, ho, hng, S₂.args.el, ?_, ?_, hodd, hlo, hel1,
      by unfold wk; omega_arith, hsigma.1, by omega_arith⟩, hm0, heven⟩
    · rw [hf₂.rg_word0 hZ16 (by decide) (by decide) (by decide), hf₂.rg_word (by decide) (by decide)]; exact hi₁
    · rw [hf₂.rg_wv hZ16 (by decide) (by decide) (by decide) (by omega_arith)]; exact hn₁
    · rw [hf₂.rg_wv2 hZ16 (by decide) (by decide) (by decide) (by decide) (by unfold wk; omega_arith)]
      rw [wv_low_of_lt (v := wk I.k + (I.el + 7) / 8) (w := 2 * (wk I.k + 2)) (by unfold wk; omega_arith)
        (by rw [hr₁]; exact hrlt), hr₁]
    · rw [hf₂.rg_word (by decide) (by decide)]; exact ht₁

end VG.Proof.Rsa.X86_64.RecoveryFolded
