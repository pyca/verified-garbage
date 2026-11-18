module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Tail
public import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Tail
meta import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import Mathlib.Tactic.TermCongr
import Mathlib.Tactic.TermCongr
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Contract
meta import Mathlib.Data.Int.ModEq
meta import Mathlib.Tactic.Set
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Ffdh.X86_64.CheckPrivate.R2CT`, which this module and modules that import it used -/

section

/-! # FFDH private-key validation on x86-64: public precomputation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def C2 (p : KpP) (s : State) : Prop := ∃ xb, Ready p xb s

private def CH (p : KpP) (s : State) : Prop :=
  Inner p s ∧ s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .r10 = off (off p.B (inner p.w)) (slot p.w aN)

private theorem head_ok (p : KpP) (s : State) (h : Inner p s) : WP isa (.block r2Head) s (CH p) := by
  obtain ⟨xb, mi, hw, hd, hm⟩ := h
  exact WP.mono (r2Head_ok (hw.mem.ctx hd).good (Nat.le_refl _)) fun t ⟨h12, h10, hmem, k⟩ =>
    ⟨⟨xb, mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm⟩, h12, h10⟩

private theorem work_r2 {p : KpP} {s : State} {xb : List Byte} {mi : BitVec 64}
    (hw : Work p xb mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hm : p.mv = true)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 p.w) (h10 : s.gpr .r10 = off (off p.B (inner p.w)) (slot p.w aN)) :
    R2Pre ⟨⟨off p.B (inner p.w), slot p.w 8, p.w, mi⟩, p.P⟩ s := by
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega_using []
  have hk := hw.base.k1
  have hk' := hw.base.k2
  obtain ⟨ho, _, hlo⟩ := valid_facts hm hk
  exact ⟨⟨(hw.mem.ctx hd).good, Nat.le_refl _⟩, show 2 ≤ p.w by omega_using [ew, hk], show p.w < 2 ^ 30 by omega_using [ew, hk'],
    hw.xv.n, hw.xv.inv, h12, h10, ho, hlo⟩

private theorem ch_r2 {s₁ s₂ : State} (h : Two CH s₁ s₂) : Two R2Pre s₁ s₂ := by
  refine two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h
  obtain ⟨⟨xb₁, mi₁, hw₁, hd₁, hm⟩, h12₁, h10₁⟩ := h₁
  obtain ⟨⟨xb₂, mi₂, hw₂, hd₂, _⟩, h12₂, h10₂⟩ := h₂
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega_using []
  have hk := hw₁.base.k1
  have ho := (valid_facts hm hk).1
  obtain rfl := xvals_minv (show 1 ≤ p.w by omega_using [ew, hk]) ho hw₁.xv hw₂.xv
  exact ⟨_, work_r2 hw₁ hd₁ hm h12₁ h10₁, work_r2 hw₂ hd₂ hm h12₂ h10₂⟩

theorem r2_ct (M : Mont) (R : R2Impl M) : RelCT isa (Two Inner) (.seq (.block r2Head) R.code) (Two C2) := by
  refine two_post (RelCT.seq (R := Two CH)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, _, _, hd, _⟩ := h; exact hd) (by taint_decide) head_ok)
    (R.ct.mono (fun _ _ h => ch_r2 h) fun _ _ h => h)) ?_
  intro p s h
  obtain ⟨xb, mi, hw, hd, hm⟩ := h
  exact WP.mono (work_ready M R hw hd hm) fun _ ⟨hr, _⟩ => ⟨xb, hr⟩

end VG.Proof.Ffdh.X86_64.CheckPrivate

end

end

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
    rcases hb.dl with hd | hd <;> rw [hd] <;> omega_using []
  have hg : Src s p.B p.Z (off p.dp p.k) p.gb := (hb.dom.drop p.k).take p.k
  simpa only [KpP.pw, hgl, hb.xlen] using ps0_of hc
    (bp := sG) (bl := sK) (ep := sX) (el := sXl) (pb := off p.dp p.k) (pe := p.xp) (bb := p.gb) (eb := xb)
    (by decide) (by decide) (by decide) (by decide) hG
    (by rw [hgl]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers])) hg
    (by rw [hgl]; omega_using [hk]) (by rw [hgl]) (hb.hdr (sX, p.xp) (by simp [KpP.headers]))
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
  exact ⟨⟨mi, hc.sub.good, Nat.le_refl _⟩, show 1 ≤ p.w by omega_using [hw], show p.w < 2 ^ 31 by omega_using [hw']⟩

private theorem c3_c4 (p : KpP) (s : State) (h : C3 p s) : WP isa (seqs (range aY)) s (C4 p) := by
  obtain ⟨xb, hh⟩ := h
  exact WP.mono (value_checked hh) fun _ ⟨hv, _⟩ => ⟨xb, hv⟩

private theorem c4_lpre (p : KpP) (s : State) (h : C4 p s) : LPre aXm sY sK p.yl s := by
  obtain ⟨xb, mi, hb, hc, _⟩ := h
  have hk := hb.k1
  have hk' := hb.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega_using []
  exact ⟨mi, p.yb, hc, show 2 ≤ p.w by omega_using [hk, ew], Nat.le_refl _, show p.w < 2 ^ 30 by omega_using [hk', ew],
    by decide, by decide, by decide, hb.hdr (sY, p.yp) (by simp [KpP.headers]),
    by rw [hb.ylen]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers]), hb.ylen,
    hb.y, by rw [hb.ylen]; omega_using [hk], by rw [hb.ylen]; omega_using [hk'], by rw [hb.ylen]⟩

private theorem c4_c5 (p : KpP) (s : State) (h : C4 p s) : WP isa (seqs (loadArr aXm sY sK)) s (C5 p) := by
  obtain ⟨xb, hh⟩ := h
  exact WP.mono (checked_pair hh) fun _ ⟨hv, _⟩ => ⟨xb, hv⟩

private theorem c5_good (p : KpP) (s : State) (h : C5 p s) : GoodW1 p.ws s := by
  obtain ⟨xb, mi, hb, hc, _⟩ := h
  have hk := hb.k1
  have hk' := hb.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega_using []
  exact ⟨⟨mi, hc.good, Nat.le_refl _⟩, show 1 ≤ p.w by omega_using [hk, ew], show p.w < 2 ^ 31 by omega_using [hk', ew]⟩

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
