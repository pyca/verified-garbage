module

import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Work
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarBound
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarLess
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
meta import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Work
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarBound
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarLess
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH private-key validation on x86-64: scalar checks in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (loadArr leave)

abbrev KpP.ws (p : KpP) : Ws := ⟨off p.B (inner p.w), slot p.w 8, p.w⟩

def Inner (p : KpP) (s : State) : Prop := ∃ xb mi, Work p xb mi s ∧ s.gpr .rdi = off p.B (inner p.w) ∧ p.mv = true

def Outer (p : KpP) (s : State) : Prop := ∃ xb mi, Work p xb mi s ∧ s.gpr .rdi = p.B ∧ p.mv = true

def OQ (p : KpP) (s : State) : Prop := Outer p s ∧ s.zf = some (decide (p.dl = 2 * p.k))

theorem inner_good (p : KpP) (s : State) (h : Inner p s) : GoodW1 p.ws s := by
  obtain ⟨xb, mi, hw, hd, _⟩ := h
  have hc := hw.mem.ctx hd
  have hk := hw.base.k1
  have hk' := hw.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega
  exact ⟨⟨mi, hc.good, Nat.le_refl _⟩, show 1 ≤ p.w by omega, show p.w < 2 ^ 31 by omega⟩

private theorem inner_nonzero (p : KpP) (s : State) (h : Inner p s) :
    WP isa (seqs (isNonzero aXm)) s (Inner p) := by
  obtain ⟨xb, mi, hw, hd, hm⟩ := h
  exact WP.mono (nonzero_ok hw hd) fun t ⟨_, hmem, k⟩ =>
    ⟨xb, mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm⟩

private theorem inner_store (p : KpP) (s : State) (h : Inner p s) :
    WP isa (.block [.store (hdr sF) .rax]) s (Inner p) := by
  obtain ⟨xb, mi, hw, hd, hm⟩ := h
  exact WP.mono (storeF_ok hw hd) fun t ⟨⟨hw', hd', _⟩, _⟩ => ⟨xb, mi, hw', hd', hm⟩

private theorem inner_leave (p : KpP) (s : State) (h : Inner p s) : WP isa (.block [leave]) s (Outer p) := by
  obtain ⟨xb, mi, hw, hd, hm⟩ := h
  exact WP.mono (leave_ok (hw.mem.ctx hd)) fun t ⟨hd', hmem, k⟩ => ⟨xb, mi, hw.keep hmem k, hd', hm⟩

private theorem outer_test (p : KpP) (s : State) (h : Outer p s) : WP isa (.block qTest) s (OQ p) := by
  obtain ⟨xb, mi, hw, hd, hm⟩ := h
  have hb := hw.base
  have hk := hb.k1
  have hk' := hb.k2
  have hZ := hb.hZ
  have hdl := hb.dl
  exact WP.mono (qTest_ok hb.scr hd (by omega)
    (hb.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [KpP.headers]))
    (hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers]))
    (by rcases hdl with h | h <;> omega) (by rcases hdl with h | h <;> omega))
    fun t ⟨_, hz, hmem, k⟩ => ⟨⟨xb, mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm⟩, hz⟩

private theorem outer_enter (p : KpP) (s : State) (h : Outer p s) : WP isa (.block [enter]) s (Inner p) := by
  obtain ⟨xb, mi, hw, hd, hm⟩ := h
  exact WP.mono (hw.enter hd) fun t ⟨hw', hd', _⟩ => ⟨xb, mi, hw', hd', hm⟩

private theorem oq_eval {p : KpP} {s : State} (h : OQ p s) : isa.eval .e s = some (decide (p.dl = 2 * p.k)) := by
  simp [eval, h.2]

private def IQ (p : KpP) (s : State) : Prop := Inner p s ∧ p.dl = 3 * p.k

private theorem oq_enterQ (p : KpP) (s : State) (h : OQ p s ∧ isa.eval .e s = some false) :
    WP isa (.block [enter]) s (IQ p) := by
  have hq : p.dl = 3 * p.k := by
    have he := h.2
    rw [oq_eval h.1] at he
    have hn := of_decide_eq_false (Option.some.inj he)
    obtain ⟨xb, mi, hw, _⟩ := h.1.1
    rcases hw.base.dl with h | h <;> omega
  exact WP.mono (outer_enter p s h.1.1) fun _ hi => ⟨hi, hq⟩

abbrev KpP.ql (p : KpP) : BPub := ⟨⟨p.B, p.Z, inner p.w, p.w, p.w⟩, off p.dp (2 * p.k), p.k⟩

private theorem iq_load (p : KpP) (s : State) (h : IQ p s) : LPre aY sQ sK p.ql s := by
  obtain ⟨⟨xb, mi, hw, hd, _⟩, hdl⟩ := h
  have hc := hw.mem.ctx hd
  have hb := hw.base
  have hk := hb.k1
  have hk' := hb.k2
  have hlen : p.qb.length = p.k := by simp only [KpP.qb, List.length_take, List.length_drop, hb.doml, hdl]; omega
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega
  exact ⟨mi, p.qb, hc, show 2 ≤ p.w by omega, Nat.le_refl _, show p.w < 2 ^ 30 by omega,
    by decide, by decide, by decide, hw.hQ,
    by rw [hlen]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers]), hlen,
    (hb.dom.drop (2 * p.k)).take p.k, by rw [hlen]; omega, by rw [hlen]; omega, by rw [hlen]⟩

private theorem iq_loaded (p : KpP) (s : State) (h : IQ p s) : WP isa (seqs (loadArr aY sQ sK)) s (Inner p) := by
  obtain ⟨⟨xb, mi, hw, hd, hm⟩, hdl⟩ := h
  exact WP.mono (loadQ_work hw hd hdl) fun t ⟨⟨hw', hd', _⟩, _⟩ => ⟨xb, mi, hw', hd', hm⟩

private theorem bound_ct : RelCT isa (Two OQ)
    (.ite .e (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm))
      (seqs (([.block [enter]] : List (Prog isa)) ++ loadArr aY sQ sK ++ ltArr aXm aY))) fun _ _ => True := by
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [oq_eval h₁, oq_eval h₂]) ?_ ?_
  · change RelCT isa _ (.seq (.block [enter]) (seqs (ltP aXm))) _
    refine RelCT.seq (R := Two Inner) (two_piece [.rdi] (pins_rdiB KpP.B fun _ _ h => by
      obtain ⟨_, _, _, hd, _⟩ := h.1.1; exact hd) (by taint_decide) fun p s h => outer_enter p s h.1.1) ?_
    exact two_map KpP.ws inner_good (ltP_ct (by decide) (by decide) (by taint_decide) (by taint_decide))
  · change RelCT isa _ (.seq (.block [enter]) (seqs (loadArr aY sQ sK ++ ltArr aXm aY))) _
    refine RelCT.seq (R := Two IQ) (two_piece [.rdi] (pins_rdiB KpP.B fun _ _ h => by
      obtain ⟨_, _, _, hd, _⟩ := h.1.1; exact hd) (by taint_decide) oq_enterQ) ?_
    exact RelCT.seqs_append (by simp [loadArr]) (by simp [ltArr, cmpArr]) (RelCT.seq (R := Two Inner)
      (two_post (two_map KpP.ql iq_load (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) iq_loaded)
      (two_map KpP.ws (fun p s h => (inner_good p s h).1) (ltArr_ct (by decide) (by decide) (by taint_decide))))

private theorem oq_bound (p : KpP) (s : State) (h : OQ p s) :
    WP isa (.ite .e (seqs (([.block [enter]] : List (Prog isa)) ++ ltP aXm))
      (seqs (([.block [enter]] : List (Prog isa)) ++ loadArr aY sQ sK ++ ltArr aXm aY))) s (Inner p) := by
  obtain ⟨⟨xb, mi, hw, hd, hm⟩, hz⟩ := h
  exact WP.mono (bound_ok hw hd hz (valid_facts hm hw.base.k1).1)
    fun t ⟨⟨hw', hd', _⟩, _⟩ => ⟨xb, mi, hw', hd', hm⟩

private theorem leave_test_ct : RelCT isa (Two Inner) (.block (leave :: qTest)) (Two OQ) := by
  change RelCT isa (Two Inner) (.block (([leave] : List Instr) ++ qTest)) (Two OQ)
  exact RelCT.block_append (RelCT.seq (R := Two Outer)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, _, _, hd, _⟩ := h; exact hd) (by taint_decide) inner_leave)
    (two_piece [.rdi] (pins_rdiB KpP.B fun _ _ h => by obtain ⟨_, _, _, hd, _⟩ := h; exact hd)
      (by taint_decide) outer_test))

theorem scalar_ct : RelCT isa (Two Inner) (seqs VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange) fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange isNonzero
  refine RelCT.seqs_append (by simp [geArr, cmpArr]) (by simp) (RelCT.seq (R := Two Inner)
    (two_post (two_map KpP.ws (fun p s h => (inner_good p s h).1) (geArr_ct (by decide) (by decide)
      (by taint_decide))) inner_nonzero) ?_)
  simp only [seqs]
  refine RelCT.seq (R := Two Inner) (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
    fun _ _ h => by obtain ⟨_, _, _, hd, _⟩ := h; exact hd) (by taint_decide) inner_store) ?_
  refine RelCT.seq (R := Two OQ) leave_test_ct ?_
  exact RelCT.seq (two_post bound_ct oq_bound)
    (two_map KpP.ws inner_good (two_taint [.rdi] pins_goodW1 (by taint_decide)))

end VG.Proof.Ffdh.X86_64.CheckPrivate
