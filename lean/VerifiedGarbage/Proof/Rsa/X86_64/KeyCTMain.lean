module

public import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTReduce
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTReduce
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_check_key` on x86-64: constant time of `main`

The setup (`setupK_ct`), then each check from `KK` (`KeyCTPieces.lean`),
then the result from `rdi` (`main_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

theorem modChecks_ct {sX sXlen sDX : Nat} (hsXl : sXlen < 32) (nXl : sXlen ≠ sMask) (fl : KPub → Nat)
    (hX : ∀ p s, KS p s → word s.mem p.B (8 * sXlen) = BitVec.ofNat 64 (fl p) ∧ 1 ≤ fl p ∧ fl p ≤ 8 * p.w)
    (hM : RelCT isa (Two KK) (seqs (loadNum aM sX sXlen)) (Two KK))
    (hDX : RelCT isa (Two KK) (seqs (loadNum aX sDX sXlen)) (Two KK))
    {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Impl.Rsa.X86_64.CheckCrtKey.lenWords sXlen ++
      Impl.Rsa.X86_64.CheckCrtKey.topE ++
      ([.mov .rax (.reg .r13), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .mov .rsi (.mem (hdr (sArr aAcc))), .alu .add .rsi (.reg .rax),
        .mov .rbx (.mem (hdr (sArr aR)))] : List Instr))) hc₁).isSome = true)
    :
    RelCT isa (Two KK) (seqs (modChecks sX sXlen sDX)) (Two KK) := by
  unfold modChecks
  have hR : RelCT isa (Two KK) (seqs (Impl.Rsa.X86_64.CheckCrtKey.reduceTop sXlen
      Impl.Rsa.X86_64.CheckCrtKey.topE)) (Two KK) :=
    reduceTopK_ct fl (fun _ => 1) hsXl nXl hX (fun p s h => by have := (hX p s h).2.2; omega) (fun _ t _ => topE_ok t)
      (fun p s h => by
        obtain ⟨s₀, minv, N, c, hs⟩ := h
        obtain ⟨a, c1, c2⟩ := hX p s₀ hs
        have := c.w2
        exact WP.mono (reduceTopK c (Nx := p.w + 2) hsXl nXl a c1 c2 (fun t _ _ => topE_ok t) (Nat.le_refl _) (by omega)
          (by omega)) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩) hT
  refine kk_app (by simp [loadNum]) (by simp [eqOne]) (kk_app (by simp [loadNum]) (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop])
    (kk_app (by simp [loadNum]) (by simp [mulE]) (kk_app (by simp [loadNum]) (by simp [loadNum])
    (kk_app (by simp [loadNum]) (by simp [eqOne]) (kk_app (by simp [loadNum]) (by simp [reduce])
    (kk_app (by simp [loadNum]) (by simp [mulE]) (kk_app (by simp [loadNum]) (by simp [loadNum])
    (kk_app (by simp [loadNum]) (by simp [ltMask]) (kk_app (by simp [loadNum]) (by simp [loadNum])
    (kk_app (by simp [loadNum]) (by simp [decM]) hM decMK_ct) hDX) ltXM) ld_D) mulEK_ct) reduceEK_ct) eqOneK_ct) hDX)
    mulEK_ct) hR) eqOneK_ct

/-- `main` is constant time from `M0`. -/
theorem main_ct : RelCT isa (Two M0) main fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp) (by simp [loadNum]) (RelCT.seq setupK_ct
    ((RelCT.seqs_append (by simp [loadNum]) (by simp [loadNum]) (RelCT.seq
      (kk_app (by simp [loadNum]) (by simp [ltMask]) ld_D ltXN) ?_)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a.kp, h₁, h₂⟩) fun _ _ h => h))
  refine RelCT.seqs_append (by simp [loadNum]) (by simp [modChecks, loadNum]) (RelCT.seq
    (kk_app (by simp [loadNum]) (by simp [VG.Impl.Rsa.X86_64.Crt.eqCheck]) (kk_app (by simp [loadNum])
      (by simp [mulXR, VG.Impl.Rsa.X86_64.Crt.zeroAccs]) (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PX ld_QR)
      mulXRK_ct) eqCheckK_ct) ?_)
  refine RelCT.seqs_append (by simp [modChecks, loadNum]) (by simp [modChecks, loadNum]) (RelCT.seq
    (modChecks_ct (by decide) (by decide) (·.pl) (fun _ _ h => ⟨h.hPl, h.pl1, h.pl2⟩) ld_PM ld_DP (by taint_decide)) ?_)
  refine RelCT.seqs_append (by simp [modChecks, loadNum]) (by simp [loadNum]) (RelCT.seq
    (modChecks_ct (by decide) (by decide) (·.ql) (fun _ _ h => ⟨h.hQl, h.ql1, h.ql2⟩) ld_QM ld_DQ (by taint_decide)) ?_)
  refine RelCT.seqs_append (by simp [loadNum]) (by simp) (RelCT.seq
    (kk_app (by simp [loadNum]) (by simp [eqOne]) (kk_app (by simp [loadNum]) (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop])
      (kk_app (by simp [loadNum]) (by simp [mulXR, VG.Impl.Rsa.X86_64.Crt.zeroAccs])
      (kk_app (by simp [loadNum]) (by simp [loadNum]) (kk_app (by simp [loadNum]) (by simp [ltMask])
      (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PM ld_QI) ltXM) ld_QR) mulXRK_ct) reduceTopQK_ct) eqOneK_ct)
    ?_)
  exact outK_ct

end VG.Proof.Rsa.X86_64.Key
