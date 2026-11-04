module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeCorrect
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.TableCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ScanRawCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bound
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
public import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.ScanTiming
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeCorrect
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.TableCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ScanRawCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # FFDH's context on x86-64: constant time

Everything the precomputation computes is public: its addresses, counts and
branches are functions of the domain, its length, `p_len`, the context's
and the working space's addresses, and the table's. -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached

open VG VG.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.Domain
open VG.Impl.Ffdh.X86_64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64 (ModCtx Slots)

/-! ## The bound and the width -/

theorem MainPre.of_mem {p : PcP} {s t : State} (h : MainPre p s) (hm : t.mem = s.mem) {rs : List Reg}
    (k : Keep rs s t) (hr : .rdi ∉ rs) : MainPre p t :=
  ⟨h.k1, h.k2, h.dl, h.doml, h.hZ, h.scr.congr k.2.2, (k.gpr hr).trans h.rdi,
    h.dom.congrK (by rw [hm]; exact InScr.refl _ _ _) k, h.ctx.congr k.2.1 k.2.2, h.dsep, hm ▸ h.hdr, h.valid⟩

theorem pins_main : Pins MainPre [.rdi] := VG.Proof.Ffdh.X86_64.pins_rdiB PcP.B fun _ _ h => h.rdi

/-- The bound scan's public data. -/
abbrev PcP.scan (p : PcP) : VG.Proof.Ffdh.X86_64.ScanPub :=
  ⟨p.B, p.Z, p.w, GenerateKey.boundPtr p.dp p.k p.dom, VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom⟩

private theorem scan_pre (p : PcP) (s : State) (h : MainPre p s) (sp : Nat)
    (he : (if p.dl = 3 * p.k then sQ else sDom) = sp) : VG.Proof.Ffdh.X86_64.ScanRawPre sp p.scan s := by
  have hk := h.k1
  have hk' := h.k2
  have hZ := h.hZ
  have size : p.dom.length = 2 * p.k ∨ p.dom.length = 3 * p.k := by rw [h.doml]; exact h.dl
  have hl := VG.Proof.Ffdh.KeyScalar.bnd_length size
  have hn : VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom ≠ [] := by intro he; rw [he] at hl; simp at hl; omega
  obtain ⟨hDom, _, hK, _, hQ, _, _⟩ := h.slots
  refine ⟨h.scr, h.rdi, show 256 ≤ p.Z by omega, ?_, ?_, hn, by change (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom).length < 2 ^ 32; omega,
    ?_, ?_⟩
  · change word s.mem p.B (8 * sp) = GenerateKey.boundPtr p.dp p.k p.dom
    unfold GenerateKey.boundPtr
    rw [h.doml]
    by_cases h3 : p.dl = 3 * p.k
    · rw [ite_eq_left h3] at he ⊢
      rw [← he]; exact hQ
    · rw [ite_eq_right h3] at he ⊢
      rw [← he]; exact hDom
  · change word s.mem p.B (8 * sK) = BitVec.ofNat 64 (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom).length
    rw [hl]; exact hK
  · change Src s p.B p.Z (GenerateKey.boundPtr p.dp p.k p.dom) (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)
    unfold GenerateKey.boundPtr VG.Proof.Ffdh.KeyScalar.bnd
    rw [h.doml]
    split
    · exact (h.dom.drop (2 * p.k)).take p.k
    · exact h.dom.take p.k
  · by_cases h3 : p.dl = 3 * p.k <;>
      simp only [h3, ↓reduceIte] at he <;> rw [← he] <;> decide

private def IQ (p : PcP) (s : State) : Prop := MainPre p s ∧ s.zf = some (decide (p.dl = 2 * p.k))

private theorem iq_eval {p : PcP} {s : State} (h : IQ p s) :
    isa.eval .e s = some (decide (p.dl = 2 * p.k)) := by simp [eval, h.2]

theorem bound_ct : RelCT isa (Two MainPre) (seqs GenerateKey.bound) fun _ _ => True := by
  change RelCT isa (Two MainPre) (.seq (.block qTest) (.ite .e (seqs (scan sDom)) (seqs (scan sQ)))) _
  refine RelCT.seq (R := Two IQ) (two_piece [.rdi] pins_main (by taint_decide) fun p s h => ?_) ?_
  · have hk := h.k1
    have hk' := h.k2
    have hZ := h.hZ
    obtain ⟨_, hDl, hK, _⟩ := h.slots
    exact WP.mono (qTest_ok h.scr h.rdi (by omega) hDl hK (by rcases h.dl with e | e <;> omega)
      (by rcases h.dl with e | e <;> omega)) fun t ⟨_, hz, hm, k⟩ => ⟨h.of_mem hm k (by decide), hz⟩
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [iq_eval h₁, iq_eval h₂]) ?_ ?_
  · refine two_map PcP.scan (fun p s h => scan_pre p s h.1.1 sDom ?_)
      (VG.Proof.Ffdh.X86_64.scan_raw_ct (sp := sDom) (by taint_decide) (by taint_decide))
    have hd : p.dl = 2 * p.k := of_decide_eq_true (Option.some.inj ((iq_eval h.1).symm.trans h.2))
    have hk := h.1.1.k1
    exact ite_eq_right (by omega)
  · refine two_map PcP.scan (fun p s h => scan_pre p s h.1.1 sQ ?_)
      (VG.Proof.Ffdh.X86_64.scan_raw_ct (sp := sQ) (by taint_decide) (by taint_decide))
    have hd : p.dl ≠ 2 * p.k := of_decide_eq_false (Option.some.inj ((iq_eval h.1).symm.trans h.2))
    have hd' : p.dl = 3 * p.k := by rcases h.1.1.dl with h | h <;> omega
    exact ite_eq_left hd'

/-- After the bound: its first significant byte in `rax`. -/
def F1 (p : PcP) (t : State) : Prop := ∃ s₀, MainPre p s₀ ∧
  ∃ hne : VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom ≠ [],
    t.gpr .rax = ((VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)[VG.Proof.Ffdh.lead
      (VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom)]'(VG.Proof.Ffdh.lead_lt hne)).setWidth 64 ∧
    word t.mem p.B (8 * sCtx) = p.cp ∧ Scr t p.B p.Z ∧ t.gpr .rdi = p.B

/-- After its bit length. -/
def F2 (p : PcP) (t : State) : Prop :=
  word t.mem p.B (8 * sCtx) = p.cp ∧ Scr t p.B p.Z ∧ t.gpr .rdi = p.B ∧ 256 ≤ p.Z

theorem front_ct :
    RelCT isa (Two MainPre) (seqs (GenerateKey.bound ++ [Precompute.byteBits,
      .block (Precompute.width ++ Precompute.metadata)])) fun _ _ => True := by
  refine RelCT.seqs_append (a := GenerateKey.bound) (by simp [GenerateKey.bound]) (by simp)
    (RelCT.seq (R := Two F1) (two_post bound_ct fun p s h => ?_) ?_)
  · have hk1 := h.k1
    have hk2 := h.k2
    have hZ := h.hZ
    obtain ⟨hDom, hDl, hK, _, hQ, hCtx, _⟩ := h.slots
    refine WP.mono (VG.Proof.Ffdh.X86_64.GenerateKey.bound_ok h.scr h.rdi (by omega) (by omega) (by omega) h.dl
      h.doml hDom hQ hK hDl h.dom) fun t ⟨hne, _, _, hax, hf, k⟩ => ⟨s, h, hne, hax, ?_, h.scr.congr k.2.2,
        (k.gpr (by decide)).trans h.rdi⟩
    rw [hf.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide) (by unfold sCtx sXe sFn; omega)]
    exact hCtx
  show RelCT isa (Two F1) (.seq Precompute.byteBits (.block (Precompute.width ++ Precompute.metadata))) _
  refine RelCT.seq (R := Two F2) (two_post (two_taint [.rax] (fun p s₁ s₂ h₁ h₂ r hr => by
      obtain ⟨_, _, hne₁, hax₁, _⟩ := h₁
      obtain ⟨_, _, hne₂, hax₂, _⟩ := h₂
      simp only [List.mem_singleton] at hr
      subst hr
      rw [hax₁, hax₂]) (by taint_decide)) fun p s h => ?_) ?_
  · obtain ⟨s₀, h₀, hne, hax, hC, hs, hd⟩ := h
    exact WP.mono (byteBits_ok (h₀.lead_ne hne) hax) fun t ⟨_, hm, k⟩ =>
      ⟨by rw [hm]; exact hC, hs.congr k.2.2, (k.gpr (by decide)).trans hd, by have := h₀.hZ; omega⟩
  show RelCT isa (Two F2) (.block ([.mov .rsi (.mem (hdr sCtx))] ++
    (List.tail Precompute.width ++ Precompute.metadata))) _
  refine RelCT.block_append (RelCT.seq (R := Two fun p t => t.gpr .rdi = p.B ∧ t.gpr .rsi = p.cp)
    (two_piece [.rdi] (VG.Proof.Ffdh.X86_64.pins_rdiB PcP.B fun _ _ h => h.2.2.1) (by taint_decide)
      fun p s ⟨hC, hs, hd, hZ⟩ => ?_)
    (two_taint [.rdi, .rsi] (pins_of (fun (p : PcP) r => if r = .rdi then p.B else p.cp) fun p s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2) (by taint_decide)))
  have hC8 : InRegions (s.rd ++ s.wr) (off p.B (8 * sCtx)) 8 := hs.ld (by
    unfold sCtx sXe sFn; omega)
  exact WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = p.cp) (by xrun [State.ea, hdr, hd, hdrOff, hC8, hC]) rfl)
    fun t ⟨hsi, k⟩ => ⟨(k.gpr (by decide)).trans hd, hsi⟩

/-! ## The workspace for `p` and `R² mod p` -/

/-- After the front. -/
def G0 (p : PcP) (t : State) : Prop := ∃ s₀, MainPre p s₀ ∧ FrontPost p s₀ t

theorem front_post_ct :
    RelCT isa (Two MainPre) (seqs (GenerateKey.bound ++ [Precompute.byteBits,
      .block (Precompute.width ++ Precompute.metadata)])) (Two G0) :=
  two_post front_ct fun _ s h => WP.mono (front_ok h) fun _ ht => ⟨s, h, ht⟩

/-- `p`'s bytes, at `dp`, from the front's state. -/
theorem G0.src {p : PcP} {s₀ s : State} (h : MainPre p s₀) (hf : FrontPost p s₀ s) :
    Src s p.B p.Z p.dp p.dom :=
  Src.of_pcOnly h.dom hf.only (fun i hi => h.dsep i (by rw [← h.doml]; exact hi)) hf.keep.2.1 hf.keep.2.2

theorem G0.setup {p : PcP} {s : State} (h : G0 p s) : VG.Proof.Ffdh.X86_64.SetupP ⟨p.B, p.Z, p.k, p.dp⟩ s := by
  obtain ⟨s₀, h, hf⟩ := h
  have hk1 := h.k1
  obtain ⟨hodd, _, _⟩ := valid_facts h.modValid hk1
  obtain ⟨hDom, _, hK, _⟩ := slots_of hf.hdr
  have hpl : (p.dom.take p.k).length = p.k := by
    simp only [List.length_take, h.doml]; rcases h.dl with e | e <;> omega
  exact ⟨p.dom.take p.k, h.scr.congr hf.keep.2.2, (hf.keep.gpr (by decide)).trans h.rdi, hk1, h.k2, h.hZ,
    hDom, hK, (G0.src h hf).take p.k, hpl, hodd⟩

/-- After the setup: `p`'s workspace. -/
def PS (p : PcP) (s₁ : State) : Prop := ∃ (mi : BitVec 64) (s₀ s : State), MainPre p s₀ ∧ FrontPost p s₀ s ∧
  SubCtx s₁ p.B p.Z (VG.Proof.Ffdh.X86_64.inner p.w) p.w p.w mi ∧
  XVals s₁ p.B (VG.Proof.Ffdh.X86_64.inner p.w) p.w mi (Spec.Rsa.os2ip (p.dom.take p.k)) ∧
  Frm p.B (VG.Proof.Ffdh.X86_64.setupR p.w) s.mem s₁.mem ∧ Keep (.rdi :: mmRegs) s s₁

theorem setup_post_ct :
    RelCT isa (Two G0) (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) (Two PS) := by
  refine two_post (two_map (fun p => (⟨p.B, p.Z, p.k, p.dp⟩ : VG.Proof.Ffdh.X86_64.DPub)) (fun _ _ h => h.setup)
    VG.Proof.Ffdh.X86_64.setup_ct) fun p s h => ?_
  obtain ⟨s₀, h₀, hf⟩ := h
  have hk1 := h₀.k1
  obtain ⟨hodd, _, _⟩ := valid_facts h₀.modValid hk1
  obtain ⟨hDom, _, hK, _⟩ := slots_of hf.hdr
  have hpl : (p.dom.take p.k).length = p.k := by
    simp only [List.length_take, h₀.doml]; rcases h₀.dl with e | e <;> omega
  exact WP.mono (VG.Proof.Ffdh.X86_64.setup_ok (h₀.scr.congr hf.keep.2.2) ((hf.keep.gpr (by decide)).trans h₀.rdi)
    hk1 h₀.k2 h₀.hZ hDom hK ((G0.src h₀ hf).take p.k) hpl hodd)
    fun t ⟨mi, hc, hv, _, hfr, k⟩ => ⟨mi, s₀, s, h₀, hf, hc, hv, hfr, k⟩

theorem pins_ps : Pins PS [.rdi] :=
  VG.Proof.Ffdh.X86_64.pins_rdiB (fun p => off p.B (VG.Proof.Ffdh.X86_64.inner p.w)) fun _ _ h => by
    obtain ⟨_, _, _, _, _, hc, _⟩ := h; exact hc.rdi

/-- After `r2Head`. -/
def PH (p : PcP) (t : State) : Prop := PS p t ∧ t.gpr .r12 = BitVec.ofNat 64 p.w ∧
  t.gpr .r10 = off (off p.B (VG.Proof.Ffdh.X86_64.inner p.w)) (slot p.w aN)

/-- After `R² mod p`. -/
def PR (p : PcP) (s₂ : State) : Prop := ∃ (mi : BitVec 64) (s₀ s s₁ : State), MainPre p s₀ ∧ FrontPost p s₀ s ∧
  SubCtx s₁ p.B p.Z (VG.Proof.Ffdh.X86_64.inner p.w) p.w p.w mi ∧
  Frm p.B (VG.Proof.Ffdh.X86_64.setupR p.w) s.mem s₁.mem ∧ Keep (.rdi :: mmRegs) s s₁ ∧
  ModCtx s₂ p.B p.Z (VG.Proof.Ffdh.X86_64.inner p.w) p.w mi (Spec.Rsa.os2ip (p.dom.take p.k)) ∧
  Frm (off p.B (VG.Proof.Ffdh.X86_64.inner p.w)) (r2Ranges p.w) s₁.mem s₂.mem ∧ Keep mmRegs s₁ s₂

private theorem ph_r2 {s₁ s₂ : State} (h : Two PH s₁ s₂) : Two R2Pre s₁ s₂ := by
  refine two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h
  obtain ⟨⟨mi₁, s₀, _, hm, _, hc₁, hv₁, _⟩, h12₁, h10₁⟩ := h₁
  obtain ⟨⟨mi₂, _, _, _, _, hc₂, hv₂, _⟩, h12₂, h10₂⟩ := h₂
  have hk := hm.k1
  have hk' := hm.k2
  have ew : p.w = (p.k + 7) / 8 := rfl
  obtain ⟨ho, _, hlo⟩ := valid_facts hm.modValid hk
  obtain rfl := VG.Proof.Ffdh.X86_64.xvals_minv (show 1 ≤ p.w by omega) ho hv₁ hv₂
  refine ⟨⟨⟨off p.B (VG.Proof.Ffdh.X86_64.inner p.w), slot p.w 8, p.w, mi₁⟩,
    Spec.Rsa.os2ip (p.dom.take p.k)⟩, ?_, ?_⟩
  · exact ⟨⟨hc₁.good, Nat.le_refl _⟩, show 2 ≤ p.w by omega, show p.w < 2 ^ 30 by omega,
      hv₁.n, hv₁.inv, h12₁, h10₁, ho, hlo⟩
  · exact ⟨⟨hc₂.good, Nat.le_refl _⟩, show 2 ≤ p.w by omega, show p.w < 2 ^ 30 by omega,
      hv₂.n, hv₂.inv, h12₂, h10₂, ho, hlo⟩

theorem r2_stage_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two PS) (.seq (.block r2Head) R.code) (Two PR) := by
  refine two_post (RelCT.seq (R := Two PH) (two_piece [.rdi] pins_ps (by taint_decide) fun p s h => ?_)
    (R.ct.mono (fun _ _ h => ph_r2 h) fun _ _ h => h)) fun p s h => ?_
  · obtain ⟨mi, s₀, s', hm, hf, hc, hv, hfr, k⟩ := h
    exact WP.mono (r2Head_ok hc.good (Nat.le_refl _)) fun t ⟨h12, h10, hmt, kt⟩ =>
      ⟨⟨mi, s₀, s', hm, hf, hc.mem hmt kt (by decide),
        ⟨by rw [hmt]; exact hv.n, by rw [hmt]; exact hv.inv, by rw [hmt]; exact hv.one⟩, hmt ▸ hfr, (k.trans kt).mono (by decide)⟩,
        h12, h10⟩
  · obtain ⟨mi, s₀, s', hm, hf, hc, hv, hfr, k⟩ := h
    exact WP.mono (VG.Proof.Ffdh.X86_64.r2_ctx Mo R hc hv hm.modValid hm.k1 hm.k2 hm.hZ)
      fun t ⟨hmc, hf₂, k₂⟩ => ⟨mi, s₀, s', s, hm, hf, hc, hfr, k, hmc, hf₂, k₂⟩

/-! ## The context's pointer and rows in the inner header -/

/-- Before the inner header's stores: the link in `rax`. -/
def E1 (p : PcP) (t : State) : Prop := ∃ mi, SubCtx t p.B p.Z (VG.Proof.Ffdh.X86_64.inner p.w) p.w p.w mi ∧
  t.gpr .rax = p.B

theorem pins_E1 : Pins E1 [.rdi, .rax] :=
  pins_of (fun (p : PcP) r => if r = .rdi then off p.B (VG.Proof.Ffdh.X86_64.inner p.w) else p.B)
    fun p s h r hr => by
      obtain ⟨_, hc, hax⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hc.rdi
      · exact hax

theorem link_ok {p : PcP} {s : State} {mi : BitVec 64}
    (hc : SubCtx s p.B p.Z (VG.Proof.Ffdh.X86_64.inner p.w) p.w p.w mi) :
    WP isa (.block [.mov .rax (.mem (hdr Crt.sLink))]) s fun t => E1 p t := by
  have hg := hc.good
  have hl : InRegions (s.rd ++ s.wr) (off (off p.B (VG.Proof.Ffdh.X86_64.inner p.w)) (8 * Crt.sLink)) 8 :=
    hg.scr.ld (hdr_lt_slot _ 8 (by decide))
  exact WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.B ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hc.link]) rfl)
    fun t ⟨⟨hax, hm⟩, k⟩ => ⟨mi, hc.mem hm k (by decide), hax⟩

theorem fromOuter_link_ok {p : PcP} {t : State} (h : E1 p t) {o i : Nat} (ho : o < 32) (hi : 17 ≤ i) (hi' : i < 32) :
    WP isa (.block [.mov .rdx (.mem (Crt.ws .rax o)), .store (hdr i) .rdx, .mov .rax (.mem (hdr Crt.sLink))]) t
      (E1 p) := by
  obtain ⟨mi, hc, hax⟩ := h
  have hg := hc.good
  have hn := hc.scr.nowrap
  have hlo := hc.lo
  have hhi := hc.hi
  have hO : InRegions (t.rd ++ t.wr) (off p.B (8 * o)) 8 := hc.scr.ld (by
    have := hdr_lt_slot p.w 8 ho; omega)
  have hI : InRegions t.wr (off (off p.B (VG.Proof.Ffdh.X86_64.inner p.w)) (8 * i)) 8 :=
    hg.scr.st (hdr_lt_slot _ 8 hi')
  have hl : InRegions (t.rd ++ t.wr) (off (off p.B (VG.Proof.Ffdh.X86_64.inner p.w)) (8 * Crt.sLink)) 8 :=
    hg.scr.ld (hdr_lt_slot _ 8 (by decide))
  have hL : ∀ v : BitVec 64, (t.mem.writeW (off (off p.B (VG.Proof.Ffdh.X86_64.inner p.w)) (8 * i)) v).readW
      (off (off p.B (VG.Proof.Ffdh.X86_64.inner p.w)) (8 * Crt.sLink)) 64 = p.B := fun v => by
    change word _ _ (8 * Crt.sLink) = _
    rw [(writeW_outside t.mem _ (d := 8 * i) v (by omega)).word (by unfold Crt.sLink sFn; omega)
      (by unfold Crt.sLink sFn; omega)]
    exact hc.link
  refine WP.mono (WP.keep [.rdx, .rax] (Q := fun u => u.gpr .rax = p.B ∧
      u.mem = t.mem.writeW (off (off p.B (VG.Proof.Ffdh.X86_64.inner p.w)) (8 * i))
        (t.mem.readW (off p.B (8 * o)) 64))
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, Crt.ws, hax, hO, hI, hl, hL]) rfl) fun u ⟨⟨hau, hmu⟩, ku⟩ => ?_
  have hf : Frm (off p.B (VG.Proof.Ffdh.X86_64.inner p.w)) [(8 * i, 8)] t.mem u.mem := by
    rw [hmu]; exact Frm.of_outside (writeW_outside t.mem _ (d := 8 * i) _ (by omega)) (by simp)
  exact ⟨mi, hc.of_frm hf (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨by simp only; omega, hdr_lt_slot _ 8 hi'⟩) ku.2.2 (ku.gpr (by decide)), hau⟩

theorem envBlock_ct :
    RelCT isa (Two fun (p : PcP) t => ∃ mi, SubCtx t p.B p.Z (VG.Proof.Ffdh.X86_64.inner p.w) p.w p.w mi)
      (.block (fromOuter sCtx iCtx ++ fromOuter sRows iRows)) fun _ _ => True := by
  show RelCT isa _ (.block ([.mov .rax (.mem (hdr Crt.sLink))] ++
    ([.mov .rdx (.mem (Crt.ws .rax sCtx)), .store (hdr iCtx) .rdx, .mov .rax (.mem (hdr Crt.sLink))] ++
      [.mov .rdx (.mem (Crt.ws .rax sRows)), .store (hdr iRows) .rdx]))) _
  refine RelCT.block_append (RelCT.seq (R := Two E1) (two_piece [.rdi]
    (VG.Proof.Ffdh.X86_64.pins_rdiB (fun p => off p.B (VG.Proof.Ffdh.X86_64.inner p.w)) fun _ _ h => by
      obtain ⟨_, hc⟩ := h; exact hc.rdi) (by taint_decide) fun p s h => ?_) ?_)
  · obtain ⟨mi, hc⟩ := h; exact link_ok hc
  refine RelCT.block_append (RelCT.seq (R := Two E1) (two_piece [.rdi, .rax] pins_E1 (by taint_decide)
    fun p s h => fromOuter_link_ok h (by decide) (by decide) (by decide)) ?_)
  exact two_taint [.rdi, .rax] pins_E1 (by taint_decide)

/-- `g`'s bytes. -/
abbrev PcP.gb (p : PcP) : List Byte := (p.dom.drop p.k).take p.k

/-- The table's data, once the inner header holds the context's pointer and rows. -/
def PE (p : PcP) (t : State) : Prop := ∃ mi, TbAt (p.T mi, p.dp + BitVec.ofNat 64 p.k, p.k) t

theorem envBlock_post_ct :
    RelCT isa (Two PR) (.block (fromOuter sCtx iCtx ++ fromOuter sRows iRows)) (Two PE) := by
  refine two_post (two_map id (fun _ _ h => by
    obtain ⟨mi, _, _, _, _, _, _, _, _, hm₂, _⟩ := h; exact ⟨mi, hm₂.sub⟩) envBlock_ct) fun p s₂ h => ?_
  obtain ⟨mi, s₀, s, s₁, h, hf, hc₁, hf₁, k₁, hm₂, hf₂, k₂⟩ := h
  have hk1 := h.k1
  have hk2 := h.k2
  have hZ := h.hZ
  have hn := h.scr.nowrap
  have hroom := VG.Proof.Ffdh.X86_64.room_k hk1 hZ
  obtain ⟨hDom, hDl, hK, hG, hQ, hCtx, hRec⟩ := slots_of hf.hdr
  have hsrc := G0.src h hf
  have hsR : ∀ r ∈ VG.Proof.Ffdh.X86_64.setupR p.w, r.1 + r.2 ≤ p.Z := by
    intro r hr
    simp only [VG.Proof.Ffdh.X86_64.setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · show 8 * 6 + 8 ≤ p.Z; omega
    · show 8 * 8 + 64 ≤ p.Z; omega
    · show 8 * 29 + 8 ≤ p.Z; omega
    · show VG.Proof.Ffdh.X86_64.inner ((p.k + 7) / 8) + slot ((p.k + 7) / 8) 8 ≤ p.Z
      have := Nat.le_add_right (VG.Proof.Ffdh.X86_64.inner ((p.k + 7) / 8) + slot ((p.k + 7) / 8) 8)
        (tabBytes ((p.k + 7) / 8) 32)
      omega
  have hin₁ : InScr p.B p.Z s.mem s₁.mem := InScr.of_frm hf₁ hsR
  have hb₁ : ∀ i < 32, i ≠ sW → i ≠ sWs → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word s₁.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi h1 h2 h3 =>
    hf₁.word_eq (fun r hr => by
      simp only [VG.Proof.Ffdh.X86_64.setupR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp only <;>
        unfold sW sWs sArr sFn VG.Proof.Ffdh.X86_64.inner slot hdrBytes at * <;> omega) (by omega)
  obtain ⟨hb₂, hin₂⟩ := VG.Proof.Ffdh.X86_64.child_frm hc₁ hm₂.wide hf₂
    (fun r hr => Nat.le_trans (r2Ranges_le p.w r hr) (Nat.le_add_right _ _))
  have hCtx₂ : word s₂.mem p.B (8 * sCtx) = p.cp := by
    rw [hb₂ _ (by decide), hb₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hCtx
  have hRows₂ : word s₂.mem p.B (8 * sRows) = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.bits) := by
    rw [hb₂ _ (by decide), hb₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hf.rowsH
  refine WP.mono (envBlock_ok hm₂ hCtx₂ hRows₂) fun s₃ ⟨hm₃, hC₃, hR₃, hf₃, k₃⟩ => ?_
  obtain ⟨hb₃, hin₃⟩ := VG.Proof.Ffdh.X86_64.child_frm hm₂.sub hm₂.wide hf₃
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Nat.le_trans (hdr_lt_slot p.w 8 (show iCtx < 32 by decide)) (Nat.le_add_right _ _)
      · exact Nat.le_trans (hdr_lt_slot p.w 8 (show iRows < 32 by decide)) (Nat.le_add_right _ _))
  have k13 := (k₁.trans k₂).trans k₃
  have hrd : s₃.rd = s₀.rd := by rw [k13.2.1, hf.keep.2.1]
  have hwr : s₃.wr = s₀.wr := by rw [k13.2.2, hf.keep.2.2]
  have he₃ : Env (p.T mi) s₃ := ⟨hm₃, hC₃, hR₃, h.ctx.congr hrd hwr⟩
  have hin₁₃ : InScr p.B p.Z s.mem s₃.mem := (hin₁.trans hin₂).trans hin₃
  have hout₁₃ : ∀ i < 32, i ≠ sW → i ≠ sWs → (i < sArr 0 ∨ sArr 0 + 8 ≤ i) →
      word s₃.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi h1 h2 h3 => by
    rw [hb₃ i hi, hb₂ i hi, hb₁ i hi h1 h2 h3]
  have hgl : p.gb.length = p.k := by
    simp only [List.length_take, List.length_drop, h.doml]; rcases h.dl with e | e <;> omega
  have hgsep : ∀ i < p.gb.length, 8 * (p.T mi).n ≤ ofs p.cp (p.dp + BitVec.ofNat 64 p.k + BitVec.ofNat 64 i) :=
    fun i hi => by
      rw [hgl] at hi
      have := h.dsep (p.k + i) (by rcases h.dl with e | e <;> omega)
      rwa [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine ⟨mi, p.gb, he₃, ?_, ?_, rfl, ?_, ?_, hgl, ?_, hgsep, by omega, by rw [hgl]⟩
  · have := h.bits_pos
    show 1 ≤ Spec.Rsa.FixedBaseComb.rows p.bits
    unfold Spec.Rsa.FixedBaseComb.rows Spec.Rsa.FixedBaseComb.teeth; omega
  · have := h.bits_le
    show Spec.Rsa.FixedBaseComb.rows p.bits < 2 ^ 63
    unfold Spec.Rsa.FixedBaseComb.rows Spec.Rsa.FixedBaseComb.teeth; omega
  · exact (hout₁₃ _ (by decide) (by decide) (by decide) (by decide)).trans hG
  · rw [hout₁₃ _ (by decide) (by decide) (by decide) (by decide), hgl]; exact hK
  · exact Src.of_pcOnly ((hsrc.drop p.k).take p.k) (PcP.Only.of_inScr hin₁₃) hgsep
      (by rw [k13.2.1]) (by rw [k13.2.2])

/-! ## The prefix, the table and the return -/

theorem prefix_ct : RelCT isa (Two TbAt) (seqs Precompute.storePrefix) (Two TbAt) := by
  unfold Precompute.storePrefix
  simp only [seqs]
  refine RelCT.seq (R := Two fun (q : TabP × Addr × Nat) t => TbAt q t ∧ t.gpr .rax = BitVec.ofNat 64 0)
    (two_piece [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide) fun q s h =>
      WP.mono (rax_imm_ok h.choose_spec.1 0 (by decide)) fun t ⟨hax, hm, het, k⟩ =>
        ⟨h.kept het (Kept.of_eq hm) k.2.1 k.2.2, hax⟩) ?_
  refine RelCT.seq (R := Two TbAt) (two_post (two_map (fun (q : TabP × Addr × Nat) => (q.1, 0))
    (fun _ _ h => ⟨h.1.choose_spec.1, h.2⟩) (storeRow_ct₂ (Or.inl rfl))) fun q s h' => ?_) ?_
  · obtain ⟨h, hax⟩ := h'
    exact WP.mono (store_env h.choose_spec.1 hax (by decide) (by decide)) fun t ⟨het, _, _, _, kp, k⟩ =>
      h.kept het kp k.2.1 k.2.2
  refine RelCT.seq (R := Two fun (q : TabP × Addr × Nat) t => TbAt q t ∧ t.gpr .rax = BitVec.ofNat 64 1)
    (two_piece [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide) fun q s h =>
      WP.mono (rax_imm_ok h.choose_spec.1 1 (by decide)) fun t ⟨hax, hm, het, k⟩ =>
        ⟨h.kept het (Kept.of_eq hm) k.2.1 k.2.2, hax⟩) ?_
  refine two_post (two_map (fun (q : TabP × Addr × Nat) => (q.1, 1))
    (fun _ _ h => ⟨h.1.choose_spec.1, h.2⟩) (storeRow_ct₂ (Or.inr rfl))) fun q s h' => ?_
  obtain ⟨h, hax⟩ := h'
  exact WP.mono (store_env h.choose_spec.1 hax (by decide) (by decide)) fun t ⟨het, _, _, _, kp, k⟩ =>
    h.kept het kp k.2.1 k.2.2

theorem tail_ct (Mo : Mont) : RelCT isa (Two TbAt)
    (seqs (Precompute.storePrefix ++ (Precompute.table Mo.mm ++
      [.block [VG.Impl.Rsa.X86_64.Crt.leave, .mov32 .rax (.imm 1)]]))) fun _ _ => True := by
  refine RelCT.seqs_append (by simp [Precompute.storePrefix]) (by simp [Precompute.table, Precompute.initial])
    (RelCT.seq prefix_ct ?_)
  refine RelCT.seqs_append (by simp [Precompute.table, Precompute.initial]) (by simp)
    (RelCT.seq (R := Two fun (q : TabP × Addr × Nat) t => Env q.1 t) (two_post (table_ct Mo) fun q s h => ?_) ?_)
  · obtain ⟨gb, he, hr, hr', hG, hsG, hsK, hl, hsrc, hgsep, hgl, hgw⟩ := h
    exact WP.mono (table_ok Mo he hr hr' hG hsG hsK hsrc hgsep hgl hgw) fun t ht => ht.1
  exact two_taint [.rdi] (pins_env (fun (q : TabP × Addr × Nat) => q.1) fun _ _ h => h) (by taint_decide)

/-- Both runs have the same `-p⁻¹ mod 2^64`. -/
theorem pe_tb {s₁ s₂ : State} (h : Two PE s₁ s₂) : Two TbAt s₁ s₂ := by
  refine two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h
  obtain ⟨mi₁, h₁⟩ := h₁
  obtain ⟨mi₂, h₂⟩ := h₂
  have he₁ := h₁.choose_spec.1
  have he₂ := h₂.choose_spec.1
  obtain rfl := VG.Proof.Ffdh.X86_64.xvals_minv (Nat.le_trans (by decide) he₁.mc.w2) he₁.mc.odd
    he₁.mc.xv he₂.mc.xv
  exact ⟨_, h₁, h₂⟩

theorem main_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two MainPre) (VG.Impl.Ffdh.X86_64.Cached.Precompute.main Mo.mm (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Precompute.main
  rw [show GenerateKey.bound ++ [Precompute.byteBits, .block (Precompute.width ++ Precompute.metadata),
      .block VG.Impl.Rsa.X86_64.head] ++ pSetup ++
      [.seq (.block r2Head) R.code, .block (fromOuter sCtx iCtx ++ fromOuter sRows iRows)] ++
      Precompute.storePrefix ++ Precompute.table Mo.mm ++
        [.block [VG.Impl.Rsa.X86_64.Crt.leave, .mov32 .rax (.imm 1)]] =
    (GenerateKey.bound ++ [Precompute.byteBits, .block (Precompute.width ++ Precompute.metadata)]) ++
      (([.block VG.Impl.Rsa.X86_64.head] ++ pSetup) ++
        ([.seq (.block r2Head) R.code, .block (fromOuter sCtx iCtx ++ fromOuter sRows iRows)] ++
          (Precompute.storePrefix ++ (Precompute.table Mo.mm ++
            [.block [VG.Impl.Rsa.X86_64.Crt.leave, .mov32 .rax (.imm 1)]]))))
    by simp only [List.append_assoc, List.cons_append, List.nil_append]]
  refine RelCT.seqs_append (by simp [GenerateKey.bound]) (by simp) (RelCT.seq front_post_ct ?_)
  refine RelCT.seqs_append (by simp [pSetup]) (by simp) (RelCT.seq setup_post_ct ?_)
  simp only [List.cons_append]
  refine seqs_cons_ct (by simp) (RelCT.seq (r2_stage_ct Mo R) ?_)
  refine seqs_cons_ct (by simp [Precompute.storePrefix]) (RelCT.seq envBlock_post_ct ?_)
  exact (tail_ct Mo).mono (fun _ _ h => pe_tb h) fun _ _ h => h

/-! ## The recognition, the modulus check and the exit -/

/-- On entry, with the public data `(pcOf s, table)`. -/
def CR (q : PcP × Addr) (s : State) : Prop :=
  pcContract.pre s ∧ pcOf s = q.1 ∧ s.syms VG.Impl.Ffdh.X86_64.VettedValidation.tableSym = q.2

def S1 (q : PcP × Addr) (u : State) : Prop := ∃ s, CR q s ∧ EntryDone s u
def S2 (q : PcP × Addr) (t : State) : Prop := ∃ s u, CR q s ∧ EntryDone s u ∧ ScanDone s u t
def S3 (q : PcP × Addr) (v : State) : Prop := ∃ s, CR q s ∧ StartPost s v

theorem scan_stage_ct : RelCT isa (Two S1)
    (VG.Impl.Ffdh.X86_64.VettedValidation.scan VG.Impl.Ffdh.VettedGroups.groups 0) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, ⟨a₁, h₁, hu₁⟩, ⟨a₂, h₂, hu₂⟩⟩ e₁ e₂
  have g₁ := pcG_of h₁.1
  have g₂ := pcG_of h₂.1
  obtain ⟨c₁, t₁'⟩ := hu₁.scan g₁
  obtain ⟨c₂, t₂'⟩ := hu₂.scan g₂
  rw [h₁.2.1] at c₁
  rw [h₂.2.1] at c₂
  rw [hu₁.2.2.2, h₁.2.2] at t₁'
  rw [hu₂.2.2.2, h₂.2.2] at t₂'
  exact VG.Proof.Ffdh.X86_64.VettedValidation.scan_ct (table := q.2) _ 0
    (by simpa only [Nat.zero_add, VG.Impl.Ffdh.VettedGroups.tableBytes] using
      (Nat.le_of_eq VG.Proof.Ffdh.VettedTableFacts.tableBytes_length))
    (fun g hg => by
      simp only [VG.Impl.Ffdh.VettedGroups.groups, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    _ _ _ _ _ _ ⟨⟨c₁, by rw [hu₁.2.2.2, h₁.2.2], t₁'⟩, ⟨c₂, by rw [hu₂.2.2.2, h₂.2.2], t₂'⟩⟩ e₁ e₂

theorem body_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two CR) (Precompute.body Mo.mm (.seq (.block r2Head) R.code)) fun _ _ => True := by
  unfold Precompute.body
  refine RelCT.seq (R := Two S1) (two_piece [.r9] (pins_of (fun (q : PcP × Addr) _ => q.1.B)
    fun q s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [← h.2.1]; rfl) (by taint_decide)
    fun q s h => WP.mono (entry_done (pcG_of h.1)) fun u hu => ⟨s, h, hu⟩) ?_
  refine RelCT.seq (R := Two S2) (two_post scan_stage_ct fun q u h => ?_) ?_
  · obtain ⟨s, h, hu⟩ := h
    exact WP.mono (scan_done (pcG_of h.1) hu) fun t ht => ⟨s, u, h, hu, ht⟩
  refine RelCT.seq (R := Two S3) (two_post (RelCT.block_append (RelCT.seq
    (R := Two fun (q : PcP × Addr) w => VG.Proof.Ffdh.X86_64.DHP ⟨q.1.B, q.1.Z, q.1.k, q.1.dp⟩ w)
    (two_piece [.r9] (pins_of (fun (q : PcP × Addr) _ => q.1.B) fun q t h r hr => by
      obtain ⟨s, u, h, hu, ht⟩ := h
      simp only [List.mem_singleton] at hr; subst hr
      rw [← h.2.1]
      exact (ht.2.2.gpr (by decide)).trans (hu.2.2.1.gpr (by decide))) (by taint_decide) fun q t h => ?_)
    (two_map (fun (q : PcP × Addr) => (⟨q.1.B, q.1.Z, q.1.k, q.1.dp⟩ : VG.Proof.Ffdh.X86_64.DPub)) (fun _ _ h => h)
      VG.Proof.Ffdh.X86_64.domHead_ct))) fun q t h => ?_) ?_
  · obtain ⟨s, u, h, hu, ht⟩ := h
    have := afterScan_dhp (pcG_of h.1) hu ht
    rw [h.2.1] at this
    exact this
  · obtain ⟨s, u, h, hu, ht⟩ := h
    exact WP.mono (after_done (pcG_of h.1) hu ht) fun v hv => ⟨s, h, hv⟩
  refine two_ite (fun q v₁ v₂ h₁ h₂ => ?_) (two_taint [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil)
    (by taint_decide)) (two_map (fun q => q.1) (fun q v h => ?_) (main_ct Mo R))
  · obtain ⟨s₁, c₁, hv₁⟩ := h₁
    obtain ⟨s₂, c₂, hv₂⟩ := h₂
    simp only [eval, hv₁.zf, hv₂.zf, c₁.2.1, c₂.2.1]
  · obtain ⟨⟨s, c, hv⟩, _⟩ := h
    rw [← c.2.1]
    exact hv.main

theorem code_ct (Mo : Mont) (R : R2Impl Mo) :
    RelCT isa (Two CR) (VG.Impl.Ffdh.X86_64.Cached.Precompute.code Mo.mm (.seq (.block r2Head) R.code)) fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Cached.Precompute.code
  refine RelCT.seq (R := Two fun (q : PcP × Addr) t => t.gpr .rdi = q.1.B)
    (two_post (body_ct Mo R) fun q s h => WP.mono (body_ok Mo R (pcG_of h.1)) fun t ht => by
      rw [← h.2.1]; exact ht.2.1) ?_
  exact two_taint [.rdi] (VG.Proof.Ffdh.X86_64.pins_rdiB (fun (q : PcP × Addr) => q.1.B) fun _ _ h => h)
    (by taint_decide)

theorem pcOf_pub {s₁ s₂ : State} (hp : pcPub s₁ s₂) : pcOf s₁ = pcOf s₂ := by
  obtain ⟨_, hd, h0, _, h2, h3, h4, h5, h6⟩ := hp
  have hdom : pcDom s₁ = pcDom s₂ := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd
  unfold pcOf
  rw [h0, h2, h3, h4, h5, h6, hdom]

theorem pc_constantTime (Mo : Mont) (R : R2Impl Mo) :
    ConstantTime isa pcContract.pre pcContract.pub (VG.Impl.Ffdh.X86_64.Cached.Precompute.code Mo.mm (.seq (.block r2Head) R.code)) :=
  RelCT.constantTime ((code_ct Mo R).mono (fun s₁ _ ⟨h₁, h₂, hp⟩ =>
    ⟨(pcOf s₁, s₁.syms VG.Impl.Ffdh.X86_64.VettedValidation.tableSym), ⟨h₁, rfl, rfl⟩, h₂,
      (pcOf_pub hp.1).symm, hp.2.symm⟩) fun _ _ h => h)

end VG.Proof.Ffdh.X86_64.Cached
