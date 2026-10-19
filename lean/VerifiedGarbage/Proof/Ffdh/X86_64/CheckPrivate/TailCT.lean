module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.R2CT
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Tail
public import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.R2CT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Main
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarBound
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarLess
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.StagesCT
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Entry
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Main
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Math
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarBound
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarLess
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Tail
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # FFDH private-key validation on x86-64: the key-consistency check is constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (loadArr)

abbrev KpP.pw (p : KpP) : PowPub := ⟨⟨p.B, p.Z, inner p.w, p.w, p.w⟩, off p.dp p.k, p.k, p.xp, p.xl⟩
abbrev KpP.yl (p : KpP) : BPub := ⟨⟨p.B, p.Z, inner p.w, p.w, p.w⟩, p.yp, p.k⟩

def C3 (p : KpP) (s : State) : Prop := ∃ xb, Value p xb s
def C4 (p : KpP) (s : State) : Prop := ∃ xb, Checked p xb s
def C5 (p : KpP) (s : State) : Prop := ∃ xb, PairReady p xb s

private theorem c2_ps0 (p : KpP) (s : State) (h : C2 p s) : PS0 sG sK sX sXl p.pw s := by
  obtain ⟨xb, mi, hb, hc, hG⟩ := h
  have hk := hb.k1
  have hk' := hb.k2
  have hgl : p.gb.length = p.k := by
    simp only [KpP.gb, List.length_take, List.length_drop, hb.doml]
    rcases hb.dl with hd | hd <;> rw [hd] <;> omega
  have hg : Src s p.B p.Z (off p.dp p.k) p.gb := (hb.dom.drop p.k).take p.k
  simpa only [KpP.pw, hgl, hb.xlen] using ps0_of hc
    (bp := sG) (bl := sK) (ep := sX) (el := sXl) (pb := off p.dp p.k) (pe := p.xp) (bb := p.gb) (eb := xb)
    (by decide) (by decide) (by decide) (by decide) hG
    (by rw [hgl]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers])) hg
    (by rw [hgl]; omega) (by rw [hgl]) (hb.hdr (sX, p.xp) (by simp [KpP.headers]))
    (by rw [hb.xlen]; exact hb.hdr (sXl, BitVec.ofNat 64 p.xl) (by simp [KpP.headers]))
    hb.x (by rw [hb.xlen]; exact hb.xl1) (by rw [hb.xlen]; exact hb.xl2.trans hk')

private theorem c2_c3 (M : Mont) (E : CrtExpL M) (p : KpP) (s : State) (h : C2 p s) :
    WP isa (seqs (pow M.mm E.code sG sK sX sXl)) s (C3 p) := by
  obtain ⟨xb, hh⟩ := h
  exact WP.mono (ready_value M E hh) fun _ ⟨hv, _⟩ => ⟨xb, hv⟩

private theorem c3_good (p : KpP) (s : State) (h : C3 p s) : GoodW1 p.ws s := by
  obtain ⟨xb, ⟨mi, hb, hc, _⟩, _⟩ := h
  have hw := hc.w2
  have hw' := hc.w28
  exact ⟨⟨mi, hc.sub.good, Nat.le_refl _⟩, show 1 ≤ p.w by omega, show p.w < 2 ^ 31 by omega⟩

private theorem c3_c4 (p : KpP) (s : State) (h : C3 p s) : WP isa (seqs (range aY)) s (C4 p) := by
  obtain ⟨xb, hh⟩ := h
  exact WP.mono (value_checked hh) fun _ ⟨hv, _⟩ => ⟨xb, hv⟩

private theorem c4_lpre (p : KpP) (s : State) (h : C4 p s) : LPre aXm sY sK p.yl s := by
  obtain ⟨xb, mi, hb, hc, _⟩ := h
  have hk := hb.k1
  have hk' := hb.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega
  exact ⟨mi, p.yb, hc, show 2 ≤ p.w by omega, Nat.le_refl _, show p.w < 2 ^ 30 by omega,
    by decide, by decide, by decide, hb.hdr (sY, p.yp) (by simp [KpP.headers]),
    by rw [hb.ylen]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers]), hb.ylen,
    hb.y, by rw [hb.ylen]; omega, by rw [hb.ylen]; omega, by rw [hb.ylen]⟩

private theorem c4_c5 (p : KpP) (s : State) (h : C4 p s) : WP isa (seqs (loadArr aXm sY sK)) s (C5 p) := by
  obtain ⟨xb, hh⟩ := h
  exact WP.mono (checked_pair hh) fun _ ⟨hv, _⟩ => ⟨xb, hv⟩

private theorem c5_good (p : KpP) (s : State) (h : C5 p s) : GoodW1 p.ws s := by
  obtain ⟨xb, mi, hb, hc, _⟩ := h
  have hk := hb.k1
  have hk' := hb.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega
  exact ⟨⟨mi, hc.good, Nat.le_refl _⟩, show 1 ≤ p.w by omega, show p.w < 2 ^ 31 by omega⟩

private theorem eq_keep (L : Ws) (s : State) (h : GoodW1 L s) : WP isa (seqs (eqArr aY aXm)) s (GoodW1 L) := by
  obtain ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ := h
  exact WP.mono (eqArr_ok hg hZ hw hw' (show aY < 8 by decide) (show aXm < 8 by decide))
    fun t ⟨_, hmem, k⟩ => GoodW1.keep ⟨⟨mi, hg, hZ⟩, hw, hw'⟩ hmem (k.gpr (by decide)) k.2.2

/-- Shared timing proof for powers of the domain's generator. -/
theorem generator_power_ct (M : Mont) (E : CrtExpL M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two C2) (seqs (pow M.mm E.code sG sK sX sXl)) (Two C3) :=
  two_post (two_map KpP.pw c2_ps0
    (pow_ct M E (loadArr_ct (by decide) (by taint_decide) (by taint_decide)) hE
      (by taint_decide) (by taint_decide) (by taint_decide))) (c2_c3 M E)

private theorem tail_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail M.mm E.code (.seq (.block r2Head) R.code) =
      .seq (.block r2Head) R.code :: (pow M.mm E.code sG sK sX sXl ++ (range aY ++
        (loadArr aXm sY sK ++ (eqArr aY aXm ++ ([.block finish] : List (Prog isa)))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail, finish, List.append_assoc, List.cons_append, List.nil_append]

theorem tail_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two Inner) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.tail M.mm E.code (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  rw [tail_eq]
  refine seqs_cons_ct (by simp [pow]) (RelCT.seq (r2_ct M R) ?_)
  refine RelCT.seqs_append (a := pow M.mm E.code sG sK sX sXl) (by simp [pow]) (by simp [range, gt1, ltArr, cmpArr])
    (RelCT.seq (R := Two C3) (generator_power_ct M E hE) ?_)
  refine RelCT.seqs_append (a := range aY) (by simp [range, gt1, ltArr, cmpArr]) (by simp [loadArr])
    (RelCT.seq (R := Two C4) (two_post (two_map KpP.ws c3_good
      (range_ct (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))) c3_c4) ?_)
  refine RelCT.seqs_append (a := loadArr aXm sY sK) (by simp [loadArr]) (by simp [eqArr])
    (RelCT.seq (R := Two C5) (two_post (two_map KpP.yl c4_lpre
      (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) c4_c5) ?_)
  exact two_map KpP.ws c5_good (RelCT.seqs_append (by simp [eqArr]) (by simp) (RelCT.seq
    (two_post (two_map id (fun _ _ h => h.1) (eqArr_ct (by decide) (by decide) (by taint_decide))) eq_keep)
    (two_taint [.rdi] pins_goodW1 (by taint_decide))))

end VG.Proof.Ffdh.X86_64.CheckPrivate
