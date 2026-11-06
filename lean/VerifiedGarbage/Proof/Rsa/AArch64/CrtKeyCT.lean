module
public import VerifiedGarbage.Proof.Rsa.AArch64.CkCT
public import VerifiedGarbage.Proof.Rsa.AArch64.CkMain

import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCTReduce
import VerifiedGarbage.Proof.Rsa.AArch64.CkCTPieces
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkCT
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCTReduce
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkCTPieces
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_rsa_check_crt_key` on AArch64: constant time

Compose the shared pieces from `CkCTPieces.lean` and bounded reductions
from `CrtKeyCTReduce.lean` into the CRT checks and their main routine.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey (sP sPlen sQ sQlen sQI aX aR aM aA aRem aT aOne aE ltA mulE mulXR)
open VG.Impl.Rsa.AArch64.CheckCrtKey (aQ hiTail loTail cntTail reduceTop topE topQ modOne modChecks)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- `qInv < p` and `q qInv ≡ 1 (mod p)`. -/
theorem ckQIC_ct : RelCT isa (Two GK) (seqs (loadA aM sP sPlen ++ (loadA aX sQI sPlen ++ (ltA aX aM ++
    (loadA aR sQ sQlen ++ (mulXR ++ modOne topQ)))))) (Two GK) :=
  ct_app (by simp [loadA]) (by simp [loadA]) (toGK (ofGK (ld_ct (by decide) (by decide) (by decide) CkP.pP CkP.pl
    (by decide) (fun I m₀ s hs L => ⟨hs.args.p, hs.args.pl, ⟨_, hs.p, L.pbl⟩, L.pl1, L.pcap⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))))
  (ofGK (ct_app (by simp [loadA]) (by simp [ltA]) (ld_ct (by decide) (by decide) (by decide) CkP.pQi CkP.pl
    (by decide) (fun I m₀ s hs L => ⟨hs.args.qi, hs.args.pl, ⟨_, hs.qi, L.qibl⟩, L.pl1, L.pcap⟩)
    (by taint_decide) (by taint_decide) (by taint_decide))
  (ct_app (by simp [ltA]) (by simp [loadA]) (ltA_ckct (a := aX) (b := aM) (js := [aX]) (by decide) (by decide)
    (by decide) (by taint_decide))
  (ct_app (by simp [loadA]) (by simp [mulXR]) (toGKb (ld_ct (by decide) (by decide) (by decide) CkP.pQ CkP.ql
    (js := [aX]) (by decide) (fun I m₀ s hs L => ⟨hs.args.q, hs.args.ql, ⟨_, hs.q, L.qbl⟩, L.ql1, L.qcap⟩)
    (by taint_decide) (by taint_decide) (by taint_decide)) (js' := [aX, aR]) (by decide))
  (ct_app (by simp [mulXR]) (by simp [modOne]) (mulXR_ckct (by taint_decide) (by taint_decide))
    (modOneTop_ckct (fun p => (p.ql + 7) / 8) (fun p s h => by
        obtain ⟨I, m₀, c, rfl, hs, L, -⟩ := h
        exact topQ_ok hs.args.ql (by simp only [CkIn.pub]; have := L.ql2; have := L.k2; omega)
          (by simp only [CkIn.pub]; have := hs.ws.h256; omega_using [this]))
      (fun p s h => by
        obtain ⟨I, m₀, c, rfl, -, L, -⟩ := h
        have := L.ql1; have := L.qcap
        exact ⟨by simp only [CkIn.pub]; omega, by simp only [CkIn.pub, wW, wk]; omega⟩) (by taint_decide) (by taint_decide) (by taint_decide)))))))

end VG.Proof.Rsa.AArch64
