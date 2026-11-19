module

public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QSetup
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QSetup
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
public import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Divides
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
public import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Divides
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Ffdh.X86_64.R2
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Start
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Start
public import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Checks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Checks
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Setup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Setup

/-! ### `Ffdh.X86_64.CheckDomain.StagesCT`, which this module and modules that import it used -/

section

/-! # FFDH domain validation on x86-64: public stages for constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev CdP.d (p : CdP) : DPub := ⟨p.B, p.Z, p.k, p.dp⟩
abbrev CdP.x (p : CdP) : XPub := ⟨p.B, p.Z, inner p.w, p.w, p.w⟩
abbrev CdP.ws (p : CdP) : Ws := p.x.ws
abbrev CdP.gl (p : CdP) : BPub := ⟨p.x, off p.dp p.k, p.k⟩
abbrev CdP.ql (p : CdP) : BPub := ⟨p.x, off p.dp (2 * p.k), p.k⟩

def CR (p : CdP) (s : State) : Prop := cdPre s ∧ cdOf s = p

def E1 (p : CdP) (s : State) : Prop := Base p s ∧ s.gpr .rdi = p.B

def CE (p : CdP) (s : State) : Prop := E1 p s ∧ s.zf = some p.mv ∧
  word s.mem p.B (8 * sG) = off p.dp p.k ∧ word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)

def Inner (p : CdP) (s : State) : Prop := ∃ mi,
  Work p mi s ∧ s.gpr .rdi = off p.B (inner p.w) ∧ p.mv = true

def Generator (p : CdP) (s : State) : Prop := Inner p s ∧
  wv s.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = p.G

def GeneratorChecked (p : CdP) (s : State) : Prop := Inner p s ∧ s.zf = some (!decide p.gr)

theorem entry_ct : RelCT isa (Two CR) (.block VG.Impl.Ffdh.X86_64.Domain.CheckDomain.entry) (Two E1) := by
  refine two_piece [.rcx] (pins_of (fun p _ => p.B) (fun p s h r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact congrArg CdP.B h.2)) (by taint_decide) ?_
  intro p s h
  exact WP.mono (entry_base (cdCtx_of h.1)) fun t ⟨hb, hd, _⟩ => by
    rw [h.2] at hb hd
    exact ⟨hb, hd⟩

theorem e1_dhp (p : CdP) (s : State) (h : E1 p s) : DHP p.d s := by
  have hz := h.1.hZ
  exact ⟨h.1.scr, h.2, by change 256 ≤ p.Z; omega_using [hz],
    h.1.hdr (sDom, p.dp) (by simp [CdP.headers]), h.1.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers])⟩

theorem e1_ce (p : CdP) (s : State) (h : E1 p s) : WP isa (.block domHead) s (CE p) :=
  WP.mono (dom_base h.1 h.2) fun _ ⟨hb, hz, hd, hG, hQ, _⟩ => ⟨⟨hb, hd⟩, hz, hG, hQ⟩

theorem ce_valid {p : CdP} {s : State} (h : CE p s) (he : isa.eval .ne s = some false) : p.mv = true := by
  simpa only [eval, h.2.1, Option.map_some, Option.some.injEq, Bool.not_eq_false'] using he

theorem ce_setup (p : CdP) (s : State) (h : CE p s ∧ isa.eval .ne s = some false) : SetupP p.d s := by
  have hb := h.1.1.1
  exact ⟨p.pb, hb.scr, h.1.1.2, hb.k1, hb.k2, hb.hZ,
    hb.hdr (sDom, p.dp) (by simp [CdP.headers]), hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]),
    hb.dom.take p.k, hb.plen, (valid_facts (ce_valid h.1 h.2) hb.k1).1⟩

theorem ce_inner (p : CdP) (s : State) (h : CE p s ∧ isa.eval .ne s = some false) :
    WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s (Inner p) :=
  WP.mono (setup_work h.1.1.1 h.1.1.2 h.1.2.2.1 h.1.2.2.2 (ce_valid h.1 h.2))
    fun _ ⟨⟨mi, hw, hd⟩, _⟩ => ⟨mi, hw, hd, ce_valid h.1 h.2⟩

theorem inner_good (p : CdP) (s : State) (h : Inner p s) : GoodW1 p.ws s := by
  obtain ⟨mi, hw, hd, _⟩ := h
  have hk := hw.base.k1
  have hk' := hw.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  exact ⟨⟨mi, (hw.mem.ctx hd).good, Nat.le_refl _⟩, show 1 ≤ p.w by omega_using [hk, ew], show p.w < 2 ^ 31 by omega_using [hk', ew]⟩

theorem inner_load (p : CdP) (s : State) (h : Inner p s) : LPre aXm sG sK p.gl s := by
  obtain ⟨mi, hw, hd, _⟩ := h
  have hb := hw.base
  have hk := hb.k1
  have hk' := hb.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  exact ⟨mi, p.gb, hw.mem.ctx hd, show 2 ≤ p.w by omega_using [hk, ew], Nat.le_refl _, show p.w < 2 ^ 30 by omega_using [hk', ew],
    by decide, by decide, by decide, hw.g,
    by rw [hb.glen]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]),
    hb.glen, (hb.dom.drop p.k).take p.k, by rw [hb.glen]; omega_using [hk],
    by rw [hb.glen]; omega_using [hk'], by rw [hb.glen]⟩

theorem inner_generator (p : CdP) (s : State) (h : Inner p s) :
    WP isa (seqs (VG.Impl.Rsa.X86_64.Crt.loadArr aXm sG sK)) s (Generator p) := by
  obtain ⟨mi, hw, hd, hm⟩ := h
  exact WP.mono (load_generator hw hd) fun t ⟨⟨hw', hd', hx⟩, _⟩ => ⟨⟨mi, hw', hd', hm⟩, hx⟩

theorem generator_checked (p : CdP) (s : State) (h : Generator p s) :
    WP isa (seqs (rangeTest aXm)) s (GeneratorChecked p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hx⟩ := h
  exact WP.mono (generator_range hw hd hx) fun t ⟨⟨hw', hd', hz⟩, _⟩ => ⟨⟨mi, hw', hd', hm⟩, hz⟩

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! ### `Ffdh.X86_64.CheckDomain.DividesCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.CheckDomain.DividesStagesCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.CheckDomain.QRangeCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.CheckDomain.OddCT`, which only this module used -/

section

/-! # FFDH domain validation on x86-64: parity uses public addresses -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64

theorem odd_ct :
    RelCT isa (Two GoodW1) (seqs (isOdd aXm)) fun _ _ => True := by
  change RelCT isa (Two GoodW1)
    (.block (([.mov .rbx (.mem (hdr (sArr aXm)))] : List Instr) ++
      [.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1)])) _
  refine RelCT.block_append ((pin_ct (Φ := GoodW1) (Ψ := fun (_ : Ws) (_ : State) => True)
    [.rdi] [.rbx] (fun L _ => off L.B (slot L.w aXm)) pins_goodW1
    (by taint_decide) ?_ (by taint_decide) ?_).mono (fun _ _ h => h) (fun _ _ _ => trivial))
  · intro L s h
    obtain ⟨⟨mi, hg, hZ⟩, _, _⟩ := h
    have hh := hdr_lt_slot L.w 8 (show sArr aXm < 32 by decide)
    refine WP.mono (WP.keep [.rbx] (Q := fun t => t.gpr .rbx = off L.B (slot L.w aXm))
      (by xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * sArr aXm) (by omega_using [hZ, hh]), hg.hdr.harr aXm (by decide)]) rfl)
      fun t ⟨hb, _⟩ r hr => ?_
    simp only [List.mem_singleton] at hr
    subst hr
    exact hb
  · intro L s h
    obtain ⟨⟨mi, hg, hZ⟩, hw, _⟩ := h
    have hp := WP.mono (isOdd_ok hg hZ hw (show aXm < 8 by decide)) (fun _ _ => True.intro)
    change WP isa (.block (([.mov .rbx (.mem (hdr (sArr aXm)))] : List Instr) ++
      [.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1)])) s (fun _ => True) at hp
    exact WP.seq_iff.mpr (WP.block_append_iff.mp hp)

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! # FFDH domain validation on x86-64: subgroup range in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def QInner (p : CdP) (s : State) : Prop := Inner p s ∧ p.dl = 3 * p.k

def QChecked (p : CdP) (s : State) : Prop := QInner p s ∧ s.zf = some (!decide p.qr)

theorem qinner_load (p : CdP) (s : State) (h : QInner p s) : LPre aXm sQ sK p.ql s := by
  obtain ⟨⟨mi, hw, hd, _⟩, hq⟩ := h
  have hb := hw.base
  have hk := hb.k1
  have hk' := hb.k2
  have hl := hb.qlen hq
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  exact ⟨mi, p.qb, hw.mem.ctx hd, show 2 ≤ p.w by omega_using [hk, ew], Nat.le_refl _, show p.w < 2 ^ 30 by omega_using [hk', ew],
    by decide, by decide, by decide, hw.q,
    by rw [hl]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]),
    hl, (hb.dom.drop (2 * p.k)).take p.k, by rw [hl]; omega_using [hk],
    by rw [hl]; omega_using [hk'], by rw [hl]⟩

private theorem qinner_loaded (p : CdP) (s : State) (h : QInner p s) :
    WP isa (seqs (VG.Impl.Rsa.X86_64.Crt.loadArr aXm sQ sK)) s (QInner p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hq⟩ := h
  exact WP.mono (load_order hw hd hq) fun _ ⟨⟨hw', hd', _⟩, _⟩ => ⟨⟨mi, hw', hd', hm⟩, hq⟩

private theorem qinner_ranged (p : CdP) (s : State) (h : QInner p s) :
    WP isa (seqs (range aXm)) s (QInner p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hq⟩ := h
  exact WP.mono (component_range hw hd rfl) fun _ ⟨⟨hw', hd', _⟩, _⟩ => ⟨⟨mi, hw', hd', hm⟩, hq⟩

private theorem qinner_odd (p : CdP) (s : State) (h : QInner p s) :
    WP isa (seqs (isOdd aXm)) s (QInner p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hq⟩ := h
  have hk := hw.base.k1
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  exact WP.mono (isOdd_ok (hw.mem.ctx hd).good (Nat.le_refl _) (by omega_using [hk, ew]) (show aXm < 8 by decide))
    fun _ ⟨_, hmem, k⟩ => ⟨⟨mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm⟩, hq⟩

private theorem qinner_checked (p : CdP) (s : State) (h : QInner p s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange) s (QChecked p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hq⟩ := h
  exact WP.mono (order_range hw hd hq) fun _ ⟨⟨hw', hd', hz⟩, _⟩ => ⟨⟨⟨mi, hw', hd', hm⟩, hq⟩, hz⟩

theorem qrange_ct : RelCT isa (Two QInner)
    (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange) (Two QChecked) := by
  refine two_post ?_ qinner_checked
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp [range, gt1, ltArr, cmpArr])
    (RelCT.seq (R := Two QInner)
      (two_post (two_map CdP.ql qinner_load (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) qinner_loaded) ?_)
  refine RelCT.seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp [isOdd])
    (RelCT.seq (R := Two QInner)
      (two_post (two_map CdP.ws (fun p s h => inner_good p s h.1)
        (range_ct (a := aXm) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))) qinner_ranged) ?_)
  refine RelCT.seqs_append (by simp [isOdd]) (by simp)
    (RelCT.seq (R := Two QInner)
      (two_post (two_map CdP.ws (fun p s h => inner_good p s h.1) odd_ct) qinner_odd) ?_)
  exact two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
    fun _ _ ⟨⟨_, _, hd, _⟩, _⟩ => hd) (by taint_decide)

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! ### `Ffdh.X86_64.CheckDomain.SubgroupCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.CheckDomain.R2CT`, which only this module used -/

section

/-! # FFDH domain validation on x86-64: public precomputation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private def CH (p : CdP) (s : State) : Prop :=
  Inner p s ∧ s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .r10 = off (off p.B (inner p.w)) (slot p.w aN)

private theorem head_ok (p : CdP) (s : State) (h : Inner p s) : WP isa (.block r2Head) s (CH p) := by
  obtain ⟨mi, hw, hd, hm⟩ := h
  exact WP.mono (r2Head_ok (hw.mem.ctx hd).good (Nat.le_refl _)) fun t ⟨h12, h10, hmem, k⟩ =>
    ⟨⟨mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm⟩, h12, h10⟩

private theorem work_r2 {p : CdP} {s : State} {mi : BitVec 64}
    (hw : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hm : p.mv = true)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 p.w) (h10 : s.gpr .r10 = off (off p.B (inner p.w)) (slot p.w aN)) :
    R2Pre ⟨⟨off p.B (inner p.w), slot p.w 8, p.w, mi⟩, p.P⟩ s := by
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  have hk := hw.base.k1
  have hk' := hw.base.k2
  obtain ⟨ho, _, hlo⟩ := valid_facts hm hk
  exact ⟨⟨(hw.mem.ctx hd).good, Nat.le_refl _⟩, show 2 ≤ p.w by omega_using [ew, hk], show p.w < 2 ^ 30 by omega_using [ew, hk'],
    hw.xv.n, hw.xv.inv, h12, h10, ho, hlo⟩

private theorem ch_r2 {s₁ s₂ : State} (h : Two CH s₁ s₂) : Two R2Pre s₁ s₂ := by
  refine two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h
  obtain ⟨⟨mi₁, hw₁, hd₁, hm⟩, h12₁, h10₁⟩ := h₁
  obtain ⟨⟨mi₂, hw₂, hd₂, _⟩, h12₂, h10₂⟩ := h₂
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  have hk := hw₁.base.k1
  have ho := (valid_facts hm hk).1
  obtain rfl := xvals_minv (show 1 ≤ p.w by omega_using [ew, hk]) ho hw₁.xv hw₂.xv
  exact ⟨_, work_r2 hw₁ hd₁ hm h12₁ h10₁, work_r2 hw₂ hd₂ hm h12₂ h10₂⟩

theorem r2_ct (M : Mont) (R : R2Impl M) :
    RelCT isa (Two Inner) (.seq (.block r2Head) R.code) fun _ _ => True := by
  refine RelCT.seq (R := Two CH)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, _, hd, _⟩ := h; exact hd) (by taint_decide) head_ok)
    (R.ct.mono (fun _ _ h => ch_r2 h) fun _ _ h => h)

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! ### `Ffdh.X86_64.CheckDomain.SubgroupStagesCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.CheckDomain.QTestCT`, which this module and modules that import it used -/

section

/-! ### `Ffdh.X86_64.CheckDomain.FrontCT`, which this module and modules that import it used -/

section

/-! # FFDH domain validation on x86-64: constant-time front end -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem pins_nil {α : Type} (Φ : α → State → Prop) : Pins Φ [] :=
  fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

private theorem rangeXm_ct : RelCT isa (Two GoodW1) (seqs (rangeTest aXm)) fun _ _ => True := by
  unfold rangeTest
  refine RelCT.seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp)
    (RelCT.seq (R := Two fun (_ : Unit) (_ : State) => True)
      ((range_ct (a := aXm) (by decide) (by decide) (by taint_decide) (by taint_decide)
        (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => ⟨(), trivial, trivial⟩)) ?_)
  exact two_taint [] (pins_nil _) (by taint_decide)

theorem front_ct :
    RelCT isa (Two fun p s => CE p s ∧ isa.eval .ne s = some false)
      (seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
        (VG.Impl.Rsa.X86_64.Crt.loadArr aXm sG sK ++ rangeTest aXm))) (Two GeneratorChecked) := by
  refine RelCT.seqs_append (by simp [pSetup]) (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr])
    (RelCT.seq (R := Two Inner)
      (two_post (two_map CdP.d ce_setup setup_ct) ce_inner) ?_)
  refine RelCT.seqs_append (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp [rangeTest])
    (RelCT.seq (R := Two Generator)
      (two_post (two_map CdP.gl inner_load (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) inner_generator) ?_)
  exact two_post (two_map CdP.ws (fun p s h => inner_good p s h.1) rangeXm_ct) generator_checked

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! ### `Ffdh.X86_64.CheckDomain.QPrepareCT`, which this module and modules that import it used -/

section

/-! # FFDH domain validation on x86-64: public reduction workspace -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev CdP.qx (p : CdP) : XPub := ⟨p.B, p.Z, inner p.w, p.w, p.wq⟩
abbrev CdP.qm (p : CdP) : MPub := ⟨p.B, p.Z, p.w, p.nq, p.eqp⟩

def ScanReady (p : CdP) (s : State) : Prop := Scanned p s ∧ p.mv = true ∧ p.dl = 3 * p.k ∧ p.qr

def BeforeQ (p : CdP) (s : State) : Prop := ScanReady p s ∧ wv s.mem p.B (slot p.w aX) p.w = p.P - 1

def QData (p : CdP) (s : State) : Prop := ∃ mi, QWork p mi s ∧ p.mv = true ∧ p.dl = 3 * p.k ∧ p.qr

def QResidue (p : CdP) (s : State) : Prop := QData p s ∧ Residue p s

def QDivided (p : CdP) (s : State) : Prop := QData p s ∧ s.zf = some (!decide ((p.P - 1) % p.Q = 0))

theorem beforeQ_m1 (p : CdP) (s : State) (h : BeforeQ p s) : M1 sEp sEl p.qm s := by
  have hb := h.1.1.parent.base
  have hk := hb.k1
  have hk' := hb.k2
  have hl := hb.qlen h.1.2.2.1
  have hne : p.qb ≠ [] := by intro he; simp [he] at hl; omega_using [hk, hl]
  have hld : p.ld < p.k := by have := lead_lt hne; change lead p.qb < p.k; omega_using [hl, this]
  have hew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  have hnl : p.eqb.length = p.nq := by simp only [CdP.eqb, List.length_drop, hl]
  exact ⟨p.eqb, h.1.1.parent.outer, h.1.1.el, h.1.1.ep, ((hb.dom.drop (2 * p.k)).take p.k).drop p.ld,
    hnl, show 1 ≤ p.nq by unfold CdP.nq; omega_using [hld], show p.nq ≤ 8 * p.w by unfold CdP.nq; omega_using [hew],
    by rw [os2ip_drop_lead p.qb]; exact h.1.2.2.2.1⟩

theorem beforeQ_data (p : CdP) (s : State) (h : BeforeQ p s) :
    WP isa (seqs (wsSetup sEl ++ ([.block [enter]] : List (Prog isa)) ++ modSetup sEp sEl)) s (QData p) :=
  WP.mono (setup_order h.1.1 h.1.2.2.1 h.1.2.2.2.1 h.2) fun _ ⟨⟨mi, hw⟩, _⟩ =>
    ⟨mi, hw, h.1.2.1, h.1.2.2⟩

theorem qdata_rpre (p : CdP) (s : State) (h : QData p s) : RPre aX p.qx s := by
  obtain ⟨mi, hw, _, _, hq⟩ := h
  have hk := hw.base.k1
  have hk' := hw.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  have h2 : 2 ≤ p.wq := Nat.le_max_left _ _
  have hwq : p.wq ≤ p.w := by unfold CdP.wq CdP.nq wsWords; omega_using [hk, ew]
  exact ⟨mi, p.Q, hw.ctx, hw.xv, h2, hwq, show p.w < 2 ^ 30 by omega_using [hk', ew], hq.2.1, by decide⟩

theorem qdata_residue (M : Mont) (p : CdP) (s : State) (h : QData p s) :
    WP isa (seqs (VG.Impl.Rsa.X86_64.Crt.redc M.mm aX)) s (QResidue p) := by
  obtain ⟨mi, hw, hm, hdl, hq⟩ := h
  exact WP.mono (reduce_order M hw hq.1 hq.2.1) fun _ ⟨hr, _⟩ => by
    obtain ⟨mi', hw', hz⟩ := hr
    exact ⟨⟨mi', hw', hm, hdl, hq⟩, mi', hw', hz⟩

theorem prepare_q_ct : RelCT isa (Two BeforeQ)
    (seqs (wsSetup sEl ++ ([.block [enter]] : List (Prog isa)) ++ modSetup sEp sEl)) (Two QData) :=
  two_post (two_map CdP.qm beforeQ_m1
    (wsMod_ct (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))) beforeQ_data

theorem reduce_q_ct (M : Mont) : RelCT isa (Two QData)
    (seqs (VG.Impl.Rsa.X86_64.Crt.redc M.mm aX)) (Two QResidue) :=
  two_post (two_map CdP.qx qdata_rpre (redc_ct_X M)) (qdata_residue M)

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! # FFDH domain validation on x86-64: testing the shared reduction -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (aXc)

private theorem zero_keep (p : CdP) (s : State) (h : QResidue p s) :
    WP isa (seqs (isZero aXc)) s (QResidue p) := by
  obtain ⟨⟨mi, hw, hm, hdl, hq⟩, hr⟩ := h
  have hk := hw.base.k1
  have hk' := hw.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  have h2 : 2 ≤ p.wq := Nat.le_max_left _ _
  have hwq : p.wq ≤ p.w := by unfold CdP.wq CdP.nq wsWords; omega_using [hk, ew]
  refine WP.mono (ltArr_ok hw.ctx.good (Nat.le_refl _) (by omega_using [h2]) (by omega_using [hk', ew, hwq])
    (show aXc < 8 by decide) (show aOne < 8 by decide)) fun t ⟨_, hmem, k⟩ => ?_
  refine ⟨⟨mi, hw.keep hmem k (k.gpr (by decide)), hm, hdl, hq⟩, ?_⟩
  obtain ⟨mi', hw', hz⟩ := hr
  exact ⟨mi', hw'.keep hmem k (k.gpr (by decide)), by rw [hmem]; exact hz⟩

private theorem tested (p : CdP) (s : State) (h : QResidue p s) :
    WP isa (seqs (isZero aXc ++ ([.block [.alu .test .rax (.reg .rax)]] : List (Prog isa)))) s (QDivided p) :=
  WP.mono (residue_test h.2) fun _ ⟨⟨⟨mi, hw, _⟩, hz⟩, _⟩ =>
    ⟨⟨mi, hw, h.1.choose_spec.2⟩, hz⟩

theorem test_q_ct : RelCT isa (Two QResidue)
    (seqs (isZero aXc ++ ([.block [.alu .test .rax (.reg .rax)]] : List (Prog isa)))) (Two QDivided) := by
  refine two_post ?_ tested
  refine RelCT.seqs_append (by simp [isZero, ltArr, cmpArr]) (by simp)
    (RelCT.seq (R := Two QResidue) ?_ ?_)
  · simpa only [isZero] using
      (two_post (two_map (fun p : CdP => p.qx.ws) (fun _ _ h => by
        obtain ⟨mi, hw, _⟩ := h.1
        exact ⟨mi, hw.ctx.good, Nat.le_refl _⟩)
        (ltArr_ct (a := aXc) (b := aOne) (by decide) (by decide) (by taint_decide))) zero_keep)
  · exact two_taint [] (pins_nil _) (by taint_decide)

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! # FFDH domain validation on x86-64: public subgroup exponentiation stages -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev CdP.pm (p : CdP) : MPub := ⟨p.B, p.Z, p.w, p.k, p.dp⟩
abbrev CdP.pw (p : CdP) : PowPub := ⟨p.x, off p.dp p.k, p.k, p.eqp, p.nq⟩

def PStart (p : CdP) (s : State) : Prop := Inner p s ∧ p.dl = 3 * p.k ∧
  word s.mem p.B (8 * sEp) = p.eqp ∧ word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.nq

def Ready (p : CdP) (s : State) : Prop := ∃ mi, PReady p mi s ∧ p.dl = 3 * p.k

def Powered (p : CdP) (s : State) : Prop := Ready p s ∧
  wv s.mem (off p.B (inner p.w)) (slot p.w aY) p.w = p.G ^ p.Q % p.P

theorem qdata_leave (p : CdP) (s : State) (h : QData p s) :
    WP isa (.block [VG.Impl.Rsa.X86_64.Crt.leave]) s (ScanReady p) := by
  obtain ⟨mi, hw, hm, hdl, hq⟩ := h
  exact WP.mono (order_leave hw) fun _ ⟨hs, _⟩ => ⟨hs, hm, hdl, hq⟩

theorem scanready_pm (p : CdP) (s : State) (h : ScanReady p s) : M1 sDom sK p.pm s := by
  have hb := h.1.parent.base
  have hk := hb.k1
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  exact ⟨p.pb, h.1.parent.outer, hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]),
    hb.hdr (sDom, p.dp) (by simp [CdP.headers]), hb.dom.take p.k, hb.plen,
    show 1 ≤ p.k by omega_using [hk], show p.k ≤ 8 * p.w by omega_using [ew], (valid_facts h.2.1 hk).1⟩

theorem scanready_start (p : CdP) (s : State) (h : ScanReady p s) : WP isa (seqs pSetup) s (PStart p) :=
  WP.mono (scanned_reset h.1 h.2.1) fun _ ⟨⟨mi, hw, hd, hep, hel⟩, _⟩ =>
    ⟨⟨mi, hw, hd, h.2.1⟩, h.2.2.1, hep, hel⟩

theorem start_ready (M : Mont) (R : R2Impl M) (p : CdP) (s : State) (h : PStart p s) :
    WP isa (.seq (.block r2Head) R.code) s (Ready p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hdl, hep, hel⟩ := h
  exact WP.mono (subgroup_r2 M R hw hd hm hep hel) fun _ ⟨hr, _⟩ => ⟨mi, hr, hdl⟩

theorem ready_ps0 (p : CdP) (s : State) (h : Ready p s) : PS0 sG sK sEp sEl p.pw s := by
  obtain ⟨mi, hr, hq⟩ := h
  have hb := hr.base
  have hk := hb.k1
  have hk' := hb.k2
  have hl := hb.qlen hq
  have hne : p.qb ≠ [] := by intro he; simp [he] at hl; omega_using [hk, hl]
  have hld : p.ld < p.k := by have := lead_lt hne; change lead p.qb < p.k; omega_using [hl, this]
  have hnl : p.eqb.length = p.nq := by simp only [CdP.eqb, List.length_drop, hl]
  have hp := ps0_of hr.ctx (bp := sG) (bl := sK) (ep := sEp) (el := sEl)
    (pb := off p.dp p.k) (pe := p.eqp) (bb := p.gb) (eb := p.eqb)
    (by decide) (by decide) (by decide) (by decide) hr.g
    (by rw [hb.glen]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]))
    ((hb.dom.drop p.k).take p.k) (by rw [hb.glen]; omega_using [hk]) (by rw [hb.glen]) hr.ep
    (by rw [hnl]; exact hr.el) (((hb.dom.drop (2 * p.k)).take p.k).drop p.ld)
    (by rw [hnl]; unfold CdP.nq; omega_using [hld]) (by rw [hnl]; unfold CdP.nq; omega_using [hk'])

  simpa only [hb.glen, hnl] using hp

theorem ready_powered (M : Mont) (E : CrtExpL M) (p : CdP) (s : State) (h : Ready p s) :
    WP isa (seqs (pow M.mm E.code sG sK sEp sEl)) s (Powered p) := by
  obtain ⟨mi, hr, hq⟩ := h
  exact WP.mono (subgroup_power M E hr hq) fun _ ⟨⟨hr', hy⟩, _⟩ => ⟨⟨mi, hr', hq⟩, hy⟩

theorem powered_good (p : CdP) (s : State) (h : Powered p s) : GoodW p.ws s := by
  obtain ⟨⟨mi, hr, _⟩, _⟩ := h
  exact ⟨mi, hr.ctx.sub.good, Nat.le_refl _⟩

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! # FFDH domain validation on x86-64: subgroup exponentiation in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

private theorem subgroup_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code) =
      .block [leave] :: (pSetup ++ (.seq (.block r2Head) R.code ::
        (pow M.mm E.code sG sK sEp sEl ++ (isOne aY ++ ([.block [leave]] : List (Prog isa)))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup, List.append_assoc, List.cons_append, List.nil_append]

private theorem finish_ct : RelCT isa (Two Powered) (seqs (isOne aY ++ ([.block [leave]] : List (Prog isa))))
    fun _ _ => True := by
  refine RelCT.seqs_append (by simp [isOne, eqArr]) (by simp)
    (RelCT.seq (R := Two fun (p : CdP) s => GoodW p.ws s) ?_ ?_)
  · simpa only [isOne] using two_post
      (two_map CdP.ws powered_good (eqArr_ct (a := aY) (b := aOne) (by decide) (by decide) (by taint_decide)))
      (fun p s h => by
        obtain ⟨⟨mi, hr, _⟩, _⟩ := h
        exact WP.mono (eqArr_ok hr.ctx.sub.good (Nat.le_refl _)
          (by have := hr.ctx.w2; omega_using [this]) (by have := hr.ctx.w28; omega_using [this])
          (show aY < 8 by decide) (show aOne < 8 by decide)) fun _ ⟨_, hm, k⟩ =>
            GoodW.keep ⟨mi, hr.ctx.sub.good, Nat.le_refl _⟩ hm (k.gpr (by decide)) k.2.2)
  · exact two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ ⟨_, hg, _⟩ => hg.rdi) (by taint_decide)

private theorem reset_ct : RelCT isa (Two ScanReady) (seqs pSetup) (Two PStart) := by
  simpa only [pSetup] using two_post (two_map CdP.pm scanready_pm
    (wsMod_ct (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide))) scanready_start

theorem subgroup_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two QData)
      (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  rw [subgroup_eq]
  refine seqs_cons_ct (by simp [pSetup]) (RelCT.seq (R := Two ScanReady)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ ⟨_, hw, _⟩ => hw.ctx.rdi) (by taint_decide) qdata_leave) ?_)
  refine RelCT.seqs_append (by simp [pSetup]) (by simp)
    (RelCT.seq (R := Two PStart)
      reset_ct ?_)
  refine seqs_cons_ct (by simp [pow]) (RelCT.seq (R := Two Ready)
    (two_post (two_map id (fun _ _ h => h.1) (r2_ct M R)) (start_ready M R)) ?_)
  refine RelCT.seqs_append (by simp [pow]) (by simp [isOne, eqArr])
    (RelCT.seq (R := Two Powered)
      (two_post (two_map CdP.pw ready_ps0
        (pow_ct M E (loadArr_ct (by decide) (by taint_decide) (by taint_decide)) hE
          (by taint_decide) (by taint_decide) (by taint_decide))) (ready_powered M E)) ?_)
  exact finish_ct

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! # FFDH domain validation on x86-64: public stages before reduction -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev CdP.qs (p : CdP) : ScanPub := ⟨p.B, p.Z, p.w, off p.dp (2 * p.k), p.qb⟩

def DivStart (p : CdP) (s : State) : Prop := QInner p s ∧ p.qr

def DivOuter (p : CdP) (s : State) : Prop := Parent p s ∧ p.mv = true ∧ p.dl = 3 * p.k ∧ p.qr

theorem qchecked_start (p : CdP) (s : State) (h : QChecked p s ∧ isa.eval .e s = some false) : DivStart p s := by
  refine ⟨h.1.1, ?_⟩
  have he : (!decide p.qr) = false := by simpa only [eval, h.1.2, Option.some.injEq] using h.2
  exact of_decide_eq_true (by simpa only [Bool.not_eq_false'] using he)

theorem divstart_leave (p : CdP) (s : State) (h : DivStart p s) :
    WP isa (.block [VG.Impl.Rsa.X86_64.Crt.leave]) s (DivOuter p) := by
  obtain ⟨⟨⟨mi, hw, hd, hm⟩, hdl⟩, hq⟩ := h
  exact WP.mono (prime_leave hw hd) fun _ ⟨hp, _⟩ => ⟨hp, hm, hdl, hq⟩

theorem divouter_scan (p : CdP) (s : State) (h : DivOuter p s) : ScanPre sQ p.qs s := by
  have hl := h.1.base.qlen h.2.2.1
  have hk := h.1.base.k1
  have hk' := h.1.base.k2
  have hne : p.qb ≠ [] := by intro he; simp [he] at hl; omega_using [hk, hl]
  exact ⟨h.1.outer, h.1.q,
    by rw [hl]; exact h.1.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]),
    hne, show p.qb.length < 2 ^ 32 by rw [hl]; omega_using [hk'],
    (h.1.base.dom.drop (2 * p.k)).take p.k, by decide⟩

theorem divouter_scanned (p : CdP) (s : State) (h : DivOuter p s) :
    WP isa (seqs (scan sQ)) s (ScanReady p) :=
  WP.mono (scan_order h.1 h.2.2.1) fun _ ⟨hs, _⟩ => ⟨hs, h.2⟩

theorem scanready_minus (p : CdP) (s : State) (h : ScanReady p s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1) s (BeforeQ p) :=
  WP.mono (scanned_minus h.1 (valid_facts h.2.1 h.1.parent.base.k1).1)
    fun _ ⟨⟨hs, hx⟩, _⟩ => ⟨⟨hs, h.2⟩, hx⟩

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! ### `Ffdh.X86_64.CheckDomain.MinusCT`, which only this module used -/

section

/-! # FFDH domain validation on x86-64: constructing p minus one in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt (zeroArr)

abbrev CdP.ows (p : CdP) : Ws := ⟨p.B, p.Z, p.w⟩

private def loads : List Instr :=
  [.mov .rsi (.mem (hdr sDom)), .mov .rcx (.mem (hdr sK)), .mov .rbx (.mem (hdr (sArr aX)))]

private def decLow : List Instr :=
  [.mov .rax (.mem (at0 .rbx)), .alu .sub .rax (.imm 1), .store (at0 .rbx) .rax]

private def ML (p : CdP) (s : State) : Prop := Parent p s ∧ s.gpr .rsi = p.dp ∧
  s.gpr .rcx = BitVec.ofNat 64 p.k ∧ s.gpr .rbx = off p.B (slot p.w aX)

private theorem loads_ok (p : CdP) (s : State) (h : Parent p s) : WP isa (.block loads) s (ML p) := by
  refine WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t =>
      t.gpr .rsi = p.dp ∧ t.gpr .rcx = BitVec.ofNat 64 p.k ∧
      t.gpr .rbx = off p.B (slot p.w aX) ∧ t.mem = s.mem)
    (by unfold loads; xrun [State.ea, hdr, hdrOff, h.outer.rdi,
      h.outer.ld (show sDom < 32 by decide), h.outer.ld (show sK < 32 by decide),
      h.outer.ld (show sArr aX < 32 by decide), h.base.hdr (sDom, p.dp) (by simp [CdP.headers]),
      h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]), h.outer.harr aX (by decide)]) rfl)
    fun _ ⟨⟨hsi, hcx, hbx, hm⟩, k⟩ => ⟨h.keep hm k (k.gpr (by decide)), hsi, hcx, hbx⟩

private theorem tail_ok (p : CdP) (s : State) (h : ML p s) :
    WP isa (.seq loadBE (.block decLow)) s fun _ => True := by
  obtain ⟨hp, hsi, hcx, hbx⟩ := h
  have hk := hp.base.k1
  have hk' := hp.base.k2
  have hX := slot_le (w := p.w) (show aX < 8 by decide)
  have hZ := hp.good.2
  have hs := hp.base.dom.take p.k
  refine WP.seq (WP.mono (loadBE_ok (w := p.w) hp.outer.scr hsi hcx hbx hp.base.plen
    (by omega_using [hk]) (by omega_using [hk']) rfl (by omega_using [hX, hZ])
    (fun i hi => hs.rd i (by rw [hp.base.plen]; exact hi)) (fun i hi => hs.val i _)
    (fun i hi => Or.inr (by have := hs.out i (by rw [hp.base.plen]; exact hi); omega_using [hX, hZ, this])))
    fun u ⟨_, _, k⟩ => ?_)
  have hbx' : u.gpr .rbx = off p.B (slot p.w aX) := (k.gpr (by decide)).trans hbx
  have scr := hp.outer.scr.congr k.2.2
  exact WP.mono (WP.keep [.rax]
    (Q := fun t => t.mem = u.mem.writeW (off p.B (slot p.w aX)) (word u.mem p.B (slot p.w aX) - 1))
    (by unfold decLow; xrun [State.ea, at0, hbx',
      show off p.B (slot p.w aX) + BitVec.ofInt 64 0 = off p.B (slot p.w aX) from by simp,
      scr.ld (show slot p.w aX + 8 ≤ p.Z by omega_using [hX, hZ]), scr.st (show slot p.w aX + 8 ≤ p.Z by omega_using [hX, hZ])]) rfl)
    (fun _ _ => True.intro)

private theorem zero_parent (p : CdP) (s : State) (h : Parent p s) : WP isa (zeroArr aX) s (Parent p) := by
  have hk := h.base.k1
  have hk' := h.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  have hX := slot_le (w := p.w) (show aX < 8 by decide)
  have hX0 := hdr_lt_slot p.w aX (show 31 < 32 by decide)
  have hZ := h.good.2
  refine WP.mono (zeroArr_ok h.good.1 hZ (by omega_using [hk, ew]) (by omega_using [hk', ew]) (show aX < 8 by decide))
    fun _ ⟨_, ho, k⟩ => ?_
  have hf : Frm p.B [(slot p.w aX, 8 * (p.w + 2))] _ _ := Frm.of_outside ho (by simp)
  exact (h.array hf (fun r he => by rw [List.mem_singleton.mp he]; exact ⟨by omega, by omega_using [hX, hZ]⟩)
    k (k.gpr (by decide))).1

private def regs (p : CdP) (r : Reg) : BitVec 64 :=
  if r = .rdi then p.B else if r = .rsi then p.dp else if r = .rcx then BitVec.ofNat 64 p.k else off p.B (slot p.w aX)

theorem minus_ct : RelCT isa (Two Parent)
    (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1) fun _ _ => True := by
  change RelCT isa (Two Parent) (.seq (zeroArr aX) (.seq (.block loads) (.seq loadBE (.block decLow)))) _
  refine RelCT.seq (R := Two Parent)
    (two_post (two_map CdP.ows (fun _ _ h => ⟨_, h.good.1, h.good.2⟩)
      (zeroArr_ct (by decide) (by taint_decide))) zero_parent) ?_
  exact (pin_ct (Ψ := fun (_ : CdP) (_ : State) => True) [.rdi] [.rdi, .rsi, .rcx, .rbx] regs
    (pins_rdiB CdP.B fun _ _ h => h.outer.rdi) (by taint_decide)
    (fun p s h => WP.mono (loads_ok p s h) fun t ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ht.1.outer.rdi
      · exact ht.2.1
      · exact ht.2.2.1
      · exact ht.2.2.2)
    (by taint_decide)
    (fun p s h => WP.seq (WP.mono (loads_ok p s h) fun u hu => tail_ok p u hu))).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! # FFDH domain validation on x86-64: divisibility in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave redc aXc)

private theorem divides_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides M.mm E.code (.seq (.block r2Head) R.code) =
      .block [leave] :: (scan sQ ++ (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1 ++
        ((wsSetup sEl ++ ([.block [enter]] : List (Prog isa)) ++ modSetup sEp sEl) ++
          (redc M.mm aX ++ ((isZero aXc ++ ([.block [.alu .test .rax (.reg .rax)]] : List (Prog isa))) ++
            ([.ite .e (retInner 0) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code)))] : List (Prog isa))))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides, List.append_assoc, List.cons_append, List.nil_append]

theorem divides_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two DivStart)
      (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides M.mm E.code (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  rw [divides_eq]
  refine seqs_cons_ct (by simp [scan]) (RelCT.seq (R := Two DivOuter)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ ⟨⟨⟨_, _, hd, _⟩, _⟩, _⟩ => hd) (by taint_decide) divstart_leave) ?_)
  refine RelCT.seqs_append (by simp [scan]) (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1])
    (RelCT.seq (R := Two ScanReady)
      (two_post (two_map CdP.qs divouter_scan (scan_ct (by taint_decide) (by taint_decide))) divouter_scanned) ?_)
  refine RelCT.seqs_append (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1]) (by simp [wsSetup])
    (RelCT.seq (R := Two BeforeQ)
      (two_post (two_map id (fun _ _ h => h.1.parent) minus_ct) scanready_minus) ?_)
  refine RelCT.seqs_append
    (by simp [wsSetup]) (by simp [redc])
    (RelCT.seq (R := Two QData) prepare_q_ct ?_)
  refine RelCT.seqs_append (by simp [redc]) (by simp [isZero, ltArr, cmpArr])
    (RelCT.seq (R := Two QResidue) (reduce_q_ct M) ?_)
  refine RelCT.seqs_append (by simp [isZero, ltArr, cmpArr]) (by simp)
    (RelCT.seq (R := Two QDivided) test_q_ct ?_)
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2])
    (two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ h => h.1.1.choose_spec.1.ctx.rdi) (by taint_decide)) ?_
  exact two_map id (fun _ _ h => h.1.1) (subgroup_ct M E R hE)

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end

/-! # FFDH domain validation on x86-64: optional-order control flow -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

def Optional (p : CdP) (s : State) : Prop := ∃ mi,
  Work p mi s ∧ s.gpr .rdi = p.B ∧ p.mv = true ∧ s.zf = some (decide (p.dl = 2 * p.k))

theorem checked_optional (p : CdP) (s : State) (h : GeneratorChecked p s ∧ isa.eval .e s = some false) :
    WP isa (.block (leave :: qTest)) s (Optional p) := by
  obtain ⟨⟨⟨mi, hw, hd, hm⟩, _⟩, _⟩ := h
  have hb := hw.base
  have hk := hb.k1
  have hk' := hb.k2
  have hdl := hb.dl
  exact WP.mono (leaveQ_ok (hw.mem.ctx hd)
    (hb.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [CdP.headers]))
    (hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]))
    (by rcases hdl with h | h <;> omega_using [h]) (by rcases hdl with h | h <;> omega_using [hk', h]))
    fun _ ⟨hd', _, hz, hmem, k⟩ => ⟨mi, hw.keep hmem k, hd', hm, hz⟩

theorem optional_inner (p : CdP) (s : State) (h : Optional p s ∧ isa.eval .e s = some false) :
    WP isa (.block [enter]) s (QInner p) := by
  obtain ⟨⟨mi, hw, hd, hm, hz⟩, he⟩ := h
  have hn : ¬p.dl = 2 * p.k := by
    have hb : decide (p.dl = 2 * p.k) = false := by simpa only [eval, hz, Option.some.injEq] using he
    exact of_decide_eq_false hb
  have hq : p.dl = 3 * p.k := by rcases hw.base.dl with h | h <;> omega_arith
  exact WP.mono (hw.enter hd) fun _ ⟨hw', hd', _⟩ => ⟨⟨mi, hw', hd', hm⟩, hq⟩

private theorem withQ_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code) =
      .block [enter] :: (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange ++
        ([.ite .e (retInner 0) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides M.mm E.code (.seq (.block r2Head) R.code)))] : List (Prog isa))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ, List.cons_append, List.nil_append]

theorem optional_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two fun p s => Optional p s ∧ isa.eval .e s = some false)
      (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  rw [withQ_eq]
  refine seqs_cons_ct (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange, VG.Impl.Rsa.X86_64.Crt.loadArr])
    (RelCT.seq (R := Two QInner)
      (two_piece [.rdi] (pins_rdiB CdP.B fun _ _ h => h.1.choose_spec.2.1)
        (by taint_decide) optional_inner) ?_)
  refine RelCT.seqs_append
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange, VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp)
    (RelCT.seq (R := Two QChecked) qrange_ct ?_)
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2])
    (two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ h => h.1.1.1.choose_spec.2.1) (by taint_decide)) ?_
  exact two_map id qchecked_start (divides_ct M E R hE)

end VG.Proof.Ffdh.X86_64.CheckDomain
