module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeCorrect
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.TableCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ScanRawCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bound
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
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

end VG.Proof.Ffdh.X86_64.Cached
