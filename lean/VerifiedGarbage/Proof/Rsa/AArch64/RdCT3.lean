module

public import VerifiedGarbage.Proof.Rsa.AArch64.RdCT2
public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
import VerifiedGarbage.Proof.Rsa.AArch64.RdPieces
import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdCT2
meta import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdPieces
meta import VerifiedGarbage.Proof.Rsa.AArch64.RdHead
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_recover_primes_det` on AArch64: constant time, the GCD

`gcdHead_ok`: the start of `gcd` gives `inverse` its inputs (`XInv`), whose
correctness then gives the rest.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64.Rd

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.RecoverDet
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.Recover (zeroMask)

/-- `inverse`'s inputs. -/
def XInv (a : Pub) (s : State) : Prop :=
  word s.mem a.1.B (slot (vk a.1.k) nXn + 8 * vk a.1.k) = 0 ∧
    wv s.mem a.1.B (slot (vk a.1.k) nU) (vk a.1.k) = wv s.mem a.1.B (slot (vk a.1.k) gM) (vk a.1.k) ∧
    wv s.mem a.1.B (slot (vk a.1.k) gX₁) (vk a.1.k) = 1 ∧ wv s.mem a.1.B (slot (vk a.1.k) gX₂) (vk a.1.k) = 0

/-- The start of `gcd`. -/
abbrev gcdHead : List (Prog isa) := [zeroA gM, copyA gM nU] ++ oneA gX₁ ++ [zeroA gX₂]

theorem gcdHead_ok {I : RpIn} {m₀ : Mem} {c : Bool} {s : State} (h : G I m₀ (vk I.k) c s) (L : RpLens I)
    (hz : word s.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0) (i : Nat) :
    WP isa (seqs gcdHead) s fun t => G I m₀ (vk I.k) c t ∧ XInv (dpub I, i) t := by
  have hv1 : 1 ≤ vk I.k := by have := L.k1; simp only [vk]; omega
  have hb32 : slot (vk I.k) 32 ≤ 2 ^ 64 := by
    have := h.bndv L (j := 31) (k := vk I.k + 2) (by decide) (Nat.le_refl _)
    have : slot (vk I.k) 32 = _ := slot_succ (vk I.k) 31; omega
  have s2 := slot_lt (w := vk I.k) (show nU < 32 by decide)
  have s3 := slot_lt (w := vk I.k) (show nXn < 32 by decide)
  have s4 := slot_lt (w := vk I.k) (show gM < 32 by decide)
  have s5 := slot_lt (w := vk I.k) (show gX₁ < 32 by decide)
  have s6 := slot_lt (w := vk I.k) (show gX₂ < 32 by decide)
  refine wp_seqs_append (by simp) (by simp) ?_
  refine wp_seqs_append (by simp) (by simp [oneA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h.ws (j := gM) (by decide)) fun s₁ ⟨_, o₁, _, _, _, k₁⟩ => ?_)
  have g₁ := h.out (by decide) (Nat.le_refl _) o₁ k₁ (by decide)
  refine WP.mono (copyA_ok g₁.ws (o := gM) (a := nU) (by decide) (by decide) (by decide))
    fun s₂ ⟨v₂, o₂, _, _, k₂⟩ => ?_
  have g₂ := g₁.out (by decide) (by omega) o₂ k₂ (by decide)
  refine WP.mono (oneA_ok g₂ (j := gX₁) (by decide)) fun s₃ ⟨g₃, v₃, o₃, k₃⟩ => ?_
  refine WP.mono (zeroA_ok g₃.ws (j := gX₂) (by decide)) fun s₄ ⟨z₄, o₄, _, _, _, k₄⟩ => ?_
  refine ⟨g₃.out (by decide) (Nat.le_refl _) o₄ k₄ (by decide), ?_, ?_, ?_, ?_⟩
  · show word s₄.mem I.B (slot (vk I.k) nXn + 8 * vk I.k) = 0
    rw [o₄.word (wd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.word (wd_sep (by decide) (by omega) (by omega)) (by omega),
      o₂.word (wd_sep (by decide) (by omega) (by omega)) (by omega),
      o₁.word (wd_sep (by decide) (by omega) (by omega)) (by omega), hz]
  · show wv s₄.mem I.B (slot (vk I.k) nU) (vk I.k) = wv s₄.mem I.B (slot (vk I.k) gM) (vk I.k)
    rw [o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₂.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      o₃.wv (rd_sep (by decide) (by omega) (by omega)) (by omega), v₂,
      o₁.wv (rd_sep (by decide) (by omega) (by omega)) (by omega)]
  · show wv s₄.mem I.B (slot (vk I.k) gX₁) (vk I.k) = 1
    rw [o₄.wv (rd_sep (by decide) (by omega) (by omega)) (by omega),
      wv_low_of_lt (w := vk I.k + 2) (by omega) (by rw [v₃]; exact Nat.one_lt_two_pow (by omega)), v₃]
  · show wv s₄.mem I.B (slot (vk I.k) gX₂) (vk I.k) = 0
    rw [wv_low_of_lt (w := vk I.k + 2) (by omega) (by rw [z₄]; exact Nat.two_pow_pos _), z₄]

theorem gcdHead_ct : CTW (GC vk fun a s => zX a.1 s) (GC vk XInv) (seqs gcdHead) := by
  refine CTW.wp (Φ := GC vk fun a s => zX a.1 s) (Ψ := GC vk XT) ?_ (fun _ _ h => h)
    fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L x => by
      subst e
      exact WP.mono (gcdHead_ok g L.1 x i) fun t ⟨g', xi⟩ => ⟨I, m₀, c, rfl, g', L, xi⟩
  simp only [gcdHead, oneA, List.cons_append, List.nil_append]
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (copyA_w (Y := XT) (by decide) (by decide) (by decide) (by intros; trivial)
    (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (setOneA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  exact CTW.one (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide))

theorem inverse_w [InvLaw] : CTW (GC vk XInv) (GC vk XT) (inverse nXn nU gX₁ gX₂ gM gT) :=
  wsop rfl (by taint_decide) fun ⟨P, i⟩ s h => h.elim fun I m₀ c e g L x => by
    subst e
    have hw := g.ws
    obtain ⟨zx, vm, x1, x2⟩ := x
    exact WP.mono (InvLaw.inverse_ok hw (iU := nXn) (iV := nU) (iX₁ := gX₁) (iX₂ := gX₂) (iM := gM) (iT := gT)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) zx vm x1 x2) fun t ⟨_, f, k, _⟩ =>
      ⟨I, m₀, c, rfl, g.step f (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact slot_ge _ _)
      (fun r hr => by
        simp only [ar, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hw.sl (by decide)) k (by decide), L, trivial⟩

theorem gcd_ct [InvLaw] : CTW (GC vk fun a s => zX a.1 s) (GC vk XT) gcd := by
  have e : gcd = seqs (gcdHead ++ ([inverse nXn nU gX₁ gX₂ gM gT] ++
      (eqA gM nOne ++ [.block zeroMask, selA nU nOne, zeroA gT, copyA gT nU]))) := by
    simp only [gcd, gcdHead, List.append_assoc, List.cons_append, List.nil_append]
  rw [e]
  refine CTW.app (by simp) (by simp) gcdHead_ct (CTW.cons (by simp) inverse_w ?_)
  refine CTW.app (a := eqA gM nOne) (by simp [eqA]) (by simp) (eqA_w (b₁ := gM) (b₂ := nOne) (Y := XT) (by decide) (by decide) (by intros; trivial)
    (by taint_decide)) ?_
  refine CTW.cons (by simp) (regs_w (Y := fun _ s => MR .x15 s) (by taint_decide) (rs := [.x3, .x4, .x7, .x15])
    (by decide) fun a s h => WP.mono (zeroMask_ok s) fun t ⟨⟨h15, _, hm⟩, k⟩ => ⟨⟨hm, _, h15⟩, k⟩) ?_
  refine CTW.cons (by simp) (selA_w (Y := XT) (by decide) (by decide) (by decide) (fun _ _ h => h.x)
    (by intros; trivial) (by taint_decide)) ?_
  refine CTW.cons (by simp) (zeroA_w (Y := XT) (by decide) (by intros; trivial) (by taint_decide)) ?_
  exact CTW.one (copyA_w (Y := XT) (by decide) (by decide) (by decide) (by intros; trivial) (by taint_decide))

end VG.Proof.Rsa.AArch64.Rd
