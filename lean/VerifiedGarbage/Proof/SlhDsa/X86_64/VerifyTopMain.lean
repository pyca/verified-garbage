module

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopTail
public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyTopPro
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# SLH-DSA (SHAKE) on x86-64, `verify`: the frame's body

Untrusted: everything here is checked by Lean. From the frame's push
(`Pushed`), `verifyBody` returns, in `rax`, 1 if the root the signature gives
is `PK.root` and 0 if not (`vOk`), with the callee-saved registers restored
(`body_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.VerifyTop

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout)

/-- The digest of a run. -/
abbrev vDigest (p : Params) (L : VL) (m₀ : Mem) : List Byte := Spec.Sha3.shake256 (hIn L m₀) p.m

/-- Whether the signature of a run is valid, as the code computes it. -/
def vOk (p : Params) (L : VL) (m₀ : Mem) : Bool :=
  let sd := splitDigest p (vDigest p L m₀)
  (htFold p (forsPkFromSig p (bytesAt m₀ (L.sig + BitVec.ofNat 64 p.n) p.forsSigLen) sd.1 (bytesAt m₀ L.pk L.n)
      (forsAdrs (Proof.SlhDsa.layerTree 0 sd.2.1) sd.2.2))
    (sigHt p L m₀) (bytesAt m₀ L.pk L.n) sd.2.1 sd.2.2 p.d).1 == bytesAt m₀ (L.pk + BitVec.ofNat 64 L.n) L.n

variable {L : VL} {g : Reg → BitVec 64} {m₀ : Mem}

theorem body_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T4 : Thash4Impl p.n) (ht : f.t4 = T4.code)
    (hp : VPar p) (hmx : (Impl.SlhDsa.X86_64.Verify.forsPk p f).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (Impl.SlhDsa.X86_64.Verify.forsPk p f)) (hst : T4.stack + 16 ≤ L.st) (hL : L.Ok) (hn : L.n = p.n)
    (hsl : L.sigL = p.sigLen) (gv : Impl.SlhDsa.X86_64.Verify.VFns) {u : State} (hu : Pushed L g m₀ u) :
    WP isa (Impl.SlhDsa.X86_64.Verify.verifyBody p f gv) u (TailPost L g m₀ (if vOk p L m₀ then 1 else 0)) := by
  have hsl1 : L.n ≤ L.sigL := by rw [hsl, hp.sigLen, hn]; omega
  have hsl2 : p.n + p.forsSigLen ≤ L.sigL := by rw [hsl, hp.sigLen]; omega
  unfold Impl.SlhDsa.X86_64.Verify.verifyBody
  refine WP.seq (WP.mono (pro_ok hL hn hu) fun t₁ hc₁ => ?_)
  refine WP.seq (WP.mono (hash_ok hL hn hsl1 hp.m64 hc₁) fun t₂ ⟨hc₂, hd₂⟩ => ?_)
  refine WP.assoc (WP.seq (WP.mono (fors_ok T4 ht hp hmx hsp hst hL hn hsl2 gv.forsPkName hc₂)
    fun t₃ ⟨hc₃, v0, v1, hm₃⟩ => ?_))
  refine WP.seq (WP.mono (start_ok hp hL hc₃ v0 v1 hm₃) fun t₄ hI₄ => ?_)
  refine WP.seq (WP.mono (loop_ok T4 ht hp hst hL hn hsl gv (dTree_lt hp _ _) (dLeaf_lt hp _ _) hI₄) fun t₅ hI₅ => ?_)
  refine WP.seq (WP.mono (cmp_ok hp hI₅.ctx) fun t₆ ⟨hc₆, hz⟩ => ?_)
  refine WP.mono (result_ok hc₆ _ hz) fun t' h => ?_
  have e : decide (bytesAt t₅.mem (at' L.S Layout.oMsg) p.n = bytesAt t₅.mem (at' L.S Layout.oPkRoot) p.n) =
      vOk p L m₀ := by
    rw [hI₅.msg, show p.n = L.n from hn.symm, hI₅.ctx.kRoot]
    simp only [vOk, dTree, dLeaf, hd₂, vDigest, hn]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]
  rw [e] at h
  exact h

end VG.Proof.SlhDsa.X86_64.VerifyTop
