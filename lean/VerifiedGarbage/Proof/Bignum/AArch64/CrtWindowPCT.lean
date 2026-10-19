module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTP
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPowCT
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowPhases
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPow
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPowCT
meta import VerifiedGarbage.Impl.Rsa.AArch64.WindowPhases
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# RSA with the CRT on AArch64: constant time, `p`'s phase

`pPhase` is constant time (`pPhase_ct`) given its pieces' claims: before
each piece, a predicate (`PO0` … `PO4`, then `hSteps`' `H0`) carries the
piece's hypotheses and what correctness gives after it; `o0_of` proves the
first from `PPre`, as `pPhase_ok` runs the pieces.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

def PPreWide (p : PPhasePub) (s : State) : Prop := PPre p s ∧ Wide p.pw.x

def PPhaseCT (W : Window) (M : Mont) (S : Selector) : Prop :=
  RelCT isa (Two PPreWide)
    (seqs (VG.Impl.Rsa.AArch64.WindowFive.pPhase W.code S.code M.mm)) (fun _ _ => True)

/-- Before the way back to the modulus' workspace. -/
def PO4 (M : Mont) (p : PPhasePub) (s : State) : Prop :=
  s.gpr .x0 = off p.ph.B p.ph.o ∧ WP isa (.block [leave]) s (H0 M p.h)

/-- Before the exponentiation. -/
def PO3 (W : Window) (M : Mont) (S : Selector) (p : PPhasePub) (s : State) : Prop :=
  PwPreWide sWsP sDp sPlen p.pw s ∧ WP isa (seqs (powSteps W.code S.code M.mm sWsP sDp sPlen)) s (PO4 M p)

/-- Before `c G mod N`. -/
def PO2 (W : Window) (M : Mont) (S : Selector) (p : PPhasePub) (s : State) : Prop :=
  GoodW p.nw s ∧ WP isa (M.mm Public.aY Public.aXm Public.aY) s (PO3 W M S p)

/-- Before `m_q G mod N`. -/
def PO1 (W : Window) (M : Mont) (S : Selector) (p : PPhasePub) (s : State) : Prop :=
  Mq0 M p.mq s ∧ WP isa (seqs (mqSteps M.mm)) s (PO2 W M S p)

/-- Before `pPhase`. -/
def PO0 (W : Window) (M : Mont) (S : Selector) (p : PPhasePub) (s : State) : Prop :=
  UPre sWsP p.u s ∧ WP isa (seqs (unitSteps M.mm sWsP)) s (PO1 W M S p)

/-- From before the exponentiation: `PO3`, as `pPhase_ok` runs the rest. -/
theorem o3_of (W : Window) (M : Mont) (S : Selector) {s : State} {B : Addr} {Z w : Nat} {minv mx : BitVec 64}
    {N X C o wx oq wq : Nat} {ep qp : Addr} {eb qib : List Byte} {c : Bool}
    (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ o) (hhi : o + slot wx 8 + wsTab wx ≤ Z)
    (hwide : o + slot wx 8 + CrtWindowFive.tabBytes32 wx ≤ Z)
    (hwx2 : 2 ≤ wx) (hwx : wx ≤ w) (hslv : word s.mem B (8 * sWsP) = off B o) (hws : WsAt s.mem B o wx mx)
    (hX : XVals s B o wx mx X) (hX1 : 1 < X) (hXodd : X % 2 = 1)
    (hcg : wv s.mem B (slot w Public.aY) w % N = C * 2 ^ (64 * wx * (nChunks w wx + 1)) % N)
    (hpl : wv s.mem (off B o) (slot wx Public.aY) wx < X)
    (hpy : X ∣ N → wv s.mem (off B o) (slot wx Public.aY) wx % X = 2 ^ (64 * wx) % X)
    (hep : word s.mem B (8 * sDp) = ep) (hel : word s.mem B (8 * sPlen) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb)
    (hmask : word s.mem (off B o) (8 * sMaskX) = mask c)
    (hqp : word s.mem B (8 * sQinv) = qp) (hql : qib.length = eb.length) (hqs : Src s B Z qp qib)
    (hqw : (qib.length + 7) / 8 ≤ wx) (hqi : c = true → Spec.Rsa.os2ip qib < X) :
    PO3 W M S ⟨⟨B, Z, w, minv, N, o, wx, ep, eb.length⟩, oq, wq, qp⟩ s := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  have hX8 : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega
  have ho64 : o < 2 ^ 64 := by omega
  -- `c^dP R_p mod p`.
  refine ⟨⟨⟨minv, mx, N, X, C, eb, hg, hw28, hlo, hhi, hwx2, hwx, by decide, hslv, hws, hX, hX1, hXodd, hcg, hpl,
      hpy, by decide, by decide, hep, hel, rfl, hL1, hL2, he⟩,hwide⟩,
    WP.mono (powPhase_ok W M S hg hw28 hlo hwide hwx2 hwx (sl := sWsP) (by decide) hslv hws hX hX1 hXodd hcg hpl hpy
      (sd := sDp) (slen := sPlen) (by decide) (by decide) hep hel hL1 hL2 he)
      fun s₄ ⟨hc₄, hX₄, hlt₄, _, hM₄, fx₄, k₄⟩ => ?_⟩
  -- Back to the modulus'.
  refine ⟨hc₄.x0, WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = s₄.mem)
    (by brun [leave, hc₄.x0, hdr_enc (show sLink < 32 by decide), hc₄.ld' (show sLink < 32 by decide), hc₄.link'])
    (by decide) (by decide) (by decide +kernel)) fun s₅ ⟨⟨hdi₅, hm₅⟩, k₅⟩ => ?_⟩
  have fx₅ : Frm B [CrtWindowFive.xRange32 o wx] s.mem s₅.mem := by rw [hm₅]; exact fx₄
  have k05 := k₄.trans k₅
  have hb₅ : ∀ d, d + 8 ≤ o → word s₅.mem B d = word s.mem B d := fun d hd => CrtWindowFive.x_below32 fx₅ hd ho64
  have hg₅ : Good s₅ B Z w minv := ⟨hs.congr k05.wr, hdi₅, ⟨(hb₅ _ (by unfold sW; omega)).trans hg.hdr.hw,
    (hb₅ _ (by unfold sMinv; omega)).trans hg.hdr.hminv,
    fun j hj => (hb₅ _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega); omega)).trans
      (hg.hdr.harr j hj)⟩⟩
  have hX₅ : XVals s₅ B o wx mx X := ⟨by rw [hm₅]; exact hX₄.n, by rw [hm₅]; exact hX₄.inv, by rw [hm₅]; exact hX₄.one⟩
  have i05 : InScr B Z s.mem s₅.mem := InScr.of_frm fx₅ fun r hr => by
    rw [List.mem_singleton.mp hr]; simp only [CrtWindowFive.xRange32]; omega
  -- `h`.
  have a1 : word s₅.mem B (8 * sWsP) = off B o := by rw [hb₅ _ (by unfold sWsP sFn; omega)]; exact hslv
  have a2 : WsAt s₅.mem B o wx mx := by rw [hm₅]; exact hc₄.ws
  have a3 : wv s₅.mem (off B o) (slot wx Public.aY) wx < X := by rw [hm₅]; exact hlt₄
  have a5 : word s₅.mem (off B o) (8 * sMaskX) = mask c := by rw [hm₅, hM₄]; exact hmask
  have a6 : word s₅.mem B (8 * sQinv) = qp := by rw [hb₅ _ (by unfold sQinv sFn; omega)]; exact hqp
  have a7 : word s₅.mem B (8 * sPlen) = BitVec.ofNat 64 qib.length := by
    rw [hb₅ _ (by unfold sPlen sFn; omega), hql]; exact hel
  have := h_chain M hg₅ hw28 hlo hhi hwx2 hwx a1 a2 hX₅ hX1 a3 a5 a6 a7 (hqs.congrK i05 k05) (by omega)
    (by omega) hqw hqi
  rw [hql] at this
  exact this

/-- `pPhase_ok`'s hypotheses give `PO0`. -/
theorem o0_of (W : Window) (M : Mont) (S : Selector) {p : PPhasePub} {s : State} (h : PPreWide p s) : PO0 W M S p s :=
  -- `o0_of`'s proof with this exponentiation, whose `o3_of` also takes `Wide`: `tabBytes32` is `wsTab`.
  o0_gen M (PO3 W M S) (fun hg hw28 hlo hhi hwx2 hwx hslv hws hX hX1 hXodd hcg hpl hpy hep hel hL1 hL2 he hmask hqp
    hql hqs hqw hqi => o3_of W M S hg hw28 hlo hhi hhi hwx2 hwx hslv hws hX hX1 hXodd hcg hpl hpy hep hel hL1 hL2 he
      hmask hqp hql hqs hqw hqi) h.1

/-- `p`'s phase is constant time, given its pieces' claims. -/
theorem pPhase_ct (W : Window) (M : Mont) (S : Selector) (hU : UnitCT M sWsP) (hP : PowCT W M S sWsP sDp sPlen) (hRX : RedcCT M Public.aX)
    (hL : LoadCT aChunk sQinv sPlen) : PPhaseCT W M S := by
  unfold PPhaseCT
  refine two_map id (fun _ _ h => o0_of W M S h) ?_
  rw [pPhase_eq]
  refine ct_steps (by simp [unitSteps]) (by simp [mqSteps]) PPhasePub.u (fun _ _ h => h.1) (fun _ _ h => h.2)
    hU ?_
  refine ct_steps (by simp [mqSteps]) (by simp) PPhasePub.mq (fun _ _ h => h.1) (fun _ _ h => h.2) (mq_ct M) ?_
  refine ct_steps (by simp) (by simp [powSteps]) PPhasePub.nw (fun _ _ h => h.1) (fun _ _ h => h.2)
    (M.ct (by unfold MmUse; decide)) ?_
  refine ct_steps (by simp [powSteps]) (by simp) PPhasePub.pw (fun _ _ h => h.1) (fun _ _ h => h.2) hP ?_
  refine RelCT.seqs_append (by simp) (by simp [hSteps]) (ct_taint [.x0] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) (by taint_decide) (fun _ _ h => h.2) ?_)
  exact two_map PPhasePub.h (fun _ _ h => h) (h_ct M hRX hL)

end VG.Proof.Bignum.AArch64.WindowFive
