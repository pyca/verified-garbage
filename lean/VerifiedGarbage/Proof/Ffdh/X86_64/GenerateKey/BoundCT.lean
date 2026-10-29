module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scan
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bound
public import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ScanRawCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scan
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Bound
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ScanRawCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH on x86-64: bound selection depends only on the public domain -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Secret random bytes are existential; domain data is shared between runs. -/
def I (p : GkP) (s : State) : Prop := ∃ rb, Inputs p rb s

private def IQ (p : GkP) (s : State) : Prop := I p s ∧ s.zf = some (decide (p.dl = 2 * p.k))

abbrev GkP.scan (p : GkP) : ScanPub := ⟨p.B, p.Z, p.w, boundPtr p.dp p.k p.dom, p.bb⟩

private theorem scan_pre (p : GkP) (s : State) (h : I p s) (sp : Nat)
    (he : (if p.dl = 3 * p.k then sQ else sDom) = sp) : ScanRawPre sp p.scan s := by
  obtain ⟨rb, h⟩ := h
  have hk := h.base.k1
  have hk' := h.base.k2
  have hZ := h.base.hZ
  have hl := h.base.bb_length
  have hn : p.bb ≠ [] := by intro he; rw [he] at hl; simp at hl; omega
  refine ⟨h.base.scr, h.rdi, by change 256 ≤ p.Z; omega, ?_, ?_, hn, by change p.bb.length < 2 ^ 32; omega, ?_, ?_⟩
  · change word s.mem p.B (8 * sp) = boundPtr p.dp p.k p.dom
    unfold boundPtr
    rw [h.base.doml]
    by_cases h3 : p.dl = 3 * p.k
    · rw [ite_eq_left h3] at he ⊢
      rw [← he]; exact h.q
    · rw [ite_eq_right h3] at he ⊢
      rw [← he]; exact h.base.hdr (sDom, p.dp) (by simp [GkP.headers])
  · change word s.mem p.B (8 * sK) = BitVec.ofNat 64 p.bb.length
    rw [hl]; exact h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers])
  · change Src s p.B p.Z (boundPtr p.dp p.k p.dom) (KeyScalar.bnd p.k p.dom)
    unfold boundPtr KeyScalar.bnd
    rw [h.base.doml]
    split
    · exact (h.base.dom.drop (2 * p.k)).take p.k
    · exact h.base.dom.take p.k
  · by_cases h3 : p.dl = 3 * p.k <;>
      simp only [h3, ↓reduceIte] at he <;> rw [← he] <;> decide

private theorem test_ok (p : GkP) (s : State) (h : I p s) : WP isa (.block qTest) s (IQ p) := by
  obtain ⟨rb, h⟩ := h
  have hk := h.base.k1
  have hk' := h.base.k2
  have hd := h.base.dl
  have hZ := h.base.hZ
  exact WP.mono (qTest_ok h.base.scr h.rdi (by omega)
    (h.base.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [GkP.headers]))
    (h.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers]))
    (by rcases hd with h | h <;> omega) (by rcases hd with h | h <;> omega))
    fun t ⟨_, hz, hm, k⟩ => ⟨⟨rb, h.keep (by intro a _; rw [hm]) k (by decide)⟩, hz⟩

private theorem iq_eval {p : GkP} {s : State} (h : IQ p s) :
    isa.eval .e s = some (decide (p.dl = 2 * p.k)) := by simp [eval, h.2]

theorem bound_ct : RelCT isa (Two I) (seqs VG.Impl.Ffdh.X86_64.Domain.GenerateKey.bound) fun _ _ => True := by
  change RelCT isa (Two I) (.seq (.block qTest) (.ite .e (seqs (scan sDom)) (seqs (scan sQ)))) _
  refine RelCT.seq (R := Two IQ)
    (two_piece [.rdi] (pins_rdiB GkP.B fun _ _ h => by obtain ⟨_, h⟩ := h; exact h.rdi)
      (by taint_decide) test_ok) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [iq_eval h₁, iq_eval h₂]) ?_ ?_
  · refine two_map GkP.scan (fun p s h => scan_pre p s h.1.1 sDom ?_)
      (scan_raw_ct (by taint_decide) (by taint_decide))
    have hd : p.dl = 2 * p.k := of_decide_eq_true (Option.some.inj ((iq_eval h.1).symm.trans h.2))
    obtain ⟨_, hi⟩ := h.1.1
    have hk := hi.base.k1
    exact ite_eq_right (by omega)
  · refine two_map GkP.scan (fun p s h => scan_pre p s h.1.1 sQ ?_)
      (scan_raw_ct (by taint_decide) (by taint_decide))
    have hd : p.dl ≠ 2 * p.k := of_decide_eq_false (Option.some.inj ((iq_eval h.1).symm.trans h.2))
    obtain ⟨_, hi⟩ := h.1.1
    have hd' : p.dl = 3 * p.k := by rcases hi.base.dl with h | h <;> omega
    exact ite_eq_left hd'

end VG.Proof.Ffdh.X86_64.GenerateKey
