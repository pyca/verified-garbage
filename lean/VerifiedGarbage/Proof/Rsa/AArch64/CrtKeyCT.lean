module
public import VerifiedGarbage.Proof.Rsa.AArch64.CkCT
public import VerifiedGarbage.Proof.Rsa.AArch64.CkMain

import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCTReduce
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCTReduce
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyMain
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyHead
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyHead
import VerifiedGarbage.Proof.Rsa.AArch64.CkCTPieces
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkCTPieces
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyPhase
import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCTMain
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Rsa.AArch64.CkCode
import VerifiedGarbage.Proof.Rsa.AArch64.CkPhase
import VerifiedGarbage.Proof.Rsa.AArch64.CkPieces
import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCode
import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
import VerifiedGarbage.Proof.Rsa.AArch64.ExpCheck
import VerifiedGarbage.Proof.Rsa.AArch64.Guarded
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCTRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkCode
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkPhase
meta import VerifiedGarbage.Proof.Rsa.AArch64.CkPieces
meta import VerifiedGarbage.Proof.Rsa.AArch64.CrtKeyCode
meta import VerifiedGarbage.Proof.Rsa.AArch64.CvCode
meta import VerifiedGarbage.Proof.Rsa.AArch64.ExpCheck
meta import VerifiedGarbage.Proof.Rsa.AArch64.Guarded
meta import VerifiedGarbage.Proof.Rsa.AArch64.Inv
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops

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

/-- The checks modulo `X - 1`. -/
theorem ckModC_ct {sX sXlen sDX : Nat} (hsX : sX < 32) (hsL : sXlen < 32) (hsD : sDX < 32) (pX pDX : CkP → Addr)
    (xl : CkP → Nat)
    (hX : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sX) = pX I.pub ∧
      word s.mem I.B (8 * sXlen) = BitVec.ofNat 64 (xl I.pub) ∧
      (∃ bs, Src s I.B I.Z (pX I.pub) bs ∧ bs.length = xl I.pub) ∧ 1 ≤ xl I.pub ∧ xl I.pub ≤ I.cap)
    (hDX : ∀ (I : CkIn) (m₀ : Mem) (s : State), CkS I m₀ s → CkLens I → word s.mem I.B (8 * sDX) = pDX I.pub ∧
      word s.mem I.B (8 * sXlen) = BitVec.ofNat 64 (xl I.pub) ∧
      (∃ bs, Src s I.B I.Z (pDX I.pub) bs ∧ bs.length = xl I.pub) ∧ 1 ≤ xl I.pub ∧ xl I.pub ≤ I.cap)
    {hc₁ : VG.Taint.Hint VG.AArch64.Taint.T}
    (htX : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base aM .x8 ++ [ldh .x1 sX, ldh .x2 sXlen]))
      hc₁).isSome = true)
    {hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (htDX : (taint.check (Taint.ofRegs [.x0]) (.block (ws ++ base aX .x8 ++ [ldh .x1 sDX, ldh .x2 sXlen]))
      hc₂).isSome = true) :
    RelCT isa (Two GK) (seqs (modChecks sX sXlen sDX)) (Two GK) := by
  rw [ckcModChecks_eq]
  have ldX := toGK (ofGK (ld_ct (j := aM) (by decide) hsX hsL pX xl (by decide) hX (by taint_decide) htX (by taint_decide)))
  have ldDX := ofGK (ld_ct (j := aX) (by decide) hsD hsL pDX xl (by decide) hDX (by taint_decide) htDX (by taint_decide))
  have mE := mulE_ckct (by taint_decide) (by taint_decide)
  exact ct_app (by simp [loadA]) (by simp) ldX (ct_app (a := [.block (decA aM)]) (by simp) (by simp [loadA])
    (ct_one (decA_ckct (by decide) (by taint_decide)))
    (ct_app (by simp [loadA]) (by simp [ltA]) ldDX
    (ct_app (by simp [ltA]) (by simp [mulE]) (ltA_ckct (a := aX) (b := aM) (js := [aX]) (by decide)
      (by decide) (by decide) (by taint_decide))
    (ct_app (by simp [mulE]) (by simp [modOne]) mE
      (modOneTop_ckct (fun _ => 1) (fun p _ _ => topE_ok _ _ _)
        (fun p _ _ => ⟨Nat.le_refl _, by simp only [wW, wk]; omega_using []⟩) (by taint_decide) (by taint_decide) (by taint_decide))))))

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

/-! ## `main` -/

/-- The CRT entry chooses capacity from public lengths. -/
def GKCM (p : CkP) (s : State) : Prop := ∃ I : CkIn, I.pub = p ∧ CkPre I s ∧
  I.cap = VG.Impl.Rsa.AArch64.CheckCrtKey.capacity I.k I.pl I.ql

theorem ckcHead_ct : RelCT isa (Two GKCM) (.block VG.Impl.Rsa.AArch64.CheckCrtKey.head) (Two GK) :=
  two_piece [.x0] (fun _ _ _ ⟨_, e₁, h₁, _⟩ ⟨_, e₂, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.x0, h₂.x0]
    exact (congrArg CkP.B e₁).trans (congrArg CkP.B e₂).symm)
    (by taint_decide) fun _ s ⟨I, e, h, hc⟩ =>
      WP.mono (ckcHeadS_ok h hc) fun _ ⟨ht, hm⟩ => ⟨I, s.mem, true, e, ht, h.L, hm⟩

/-- `main` leaks the same in two runs with the same public data. -/
theorem ckcMain_ct : RelCT isa (Two GKCM) VG.Impl.Rsa.AArch64.CheckCrtKey.main fun _ _ => True := by
  rw [ckcMain_eq]
  refine (ct_app (by simp) (by simp [loadA]) (ct_one ckcHead_ct)
    (ct_app (by simp [loadA]) (by simp [loadA]) (toGK (ofGK (ldWide_ct (by decide) (by decide) (by decide) CkP.pN CkP.k
      (by decide) (fun I m₀ s hs L => ⟨hs.args.n, hs.args.k, ⟨_, hs.n, L.nl⟩, show 1 ≤ I.k by have := L.k1; omega_using [this], Nat.le_refl _⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))))
    (ct_app (by simp [loadA]) (by simp) (toGK (ofGK (ldWide_ct (by decide) (by decide) (by decide) CkP.pE CkP.el
      (by decide) (fun I m₀ s hs L => ⟨hs.args.e, hs.args.el, ⟨_, hs.e, L.ebl⟩, L.el1, L.el2⟩)
      (by taint_decide) (by taint_decide) (by taint_decide))))
    (ct_app (by simp) (by simp [loadA]) (ct_cons (by simp) (zeroA_ckct (by decide) (by taint_decide))
      (ct_one (setOneA_ckct (by decide) (by taint_decide))))
    (ct_app (by simp [loadA]) (by simp [modChecks]) ckPQ_ct
    (ct_app (by simp [modChecks]) (by simp [modChecks]) (ckModC_ct (by decide) (by decide) (by decide) CkP.pP CkP.pDp
      CkP.pl (fun I m₀ s hs L => ⟨hs.args.p, hs.args.pl, ⟨_, hs.p, L.pbl⟩, L.pl1, L.pcap⟩)
      (fun I m₀ s hs L => ⟨hs.args.dp, hs.args.pl, ⟨_, hs.dp, L.dpbl⟩, L.pl1, L.pcap⟩)
      (by taint_decide) (by taint_decide))
    (ct_app (by simp [modChecks]) (by simp [loadA]) (ckModC_ct (by decide) (by decide) (by decide) CkP.pQ CkP.pDq
      CkP.ql (fun I m₀ s hs L => ⟨hs.args.q, hs.args.ql, ⟨_, hs.q, L.qbl⟩, L.ql1, L.qcap⟩)
      (fun I m₀ s hs L => ⟨hs.args.dq, hs.args.ql, ⟨_, hs.dq, L.dqbl⟩, L.ql1, L.qcap⟩)
      (by taint_decide) (by taint_decide))
    (ct_app (by simp [loadA]) (by simp) ckQIC_ct (ct_one retMaskK_ct))))))))).mono
    (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.Rsa.AArch64
