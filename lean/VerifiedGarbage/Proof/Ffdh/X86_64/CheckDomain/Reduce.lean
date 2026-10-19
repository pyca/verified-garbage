module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QSetup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.Domain

/-! # FFDH domain validation on x86-64: shared RSA reduction -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (redc aXc)

/-- The Montgomery residue is zero exactly when q divides p minus one. -/
def Residue (p : CdP) (s : State) : Prop := ∃ mi, QWork p mi s ∧
  (wv s.mem (off p.B (inner p.w)) (slot p.wq aXc) p.wq = 0 ↔ (p.P - 1) % p.Q = 0)

theorem reduce_order (M : Mont) {p : CdP} {mi : BitVec 64} {s : State}
    (h : QWork p mi s) (ho : p.Q % 2 = 1) (hq : 1 < p.Q) :
    WP isa (seqs (redc M.mm aX)) s (StepPost p s (Residue p)) := by
  have hk := h.base.k1
  have hk' := h.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  have h2 : 2 ≤ p.wq := Nat.le_max_left _ _
  have hwq : p.wq ≤ p.w := by unfold CdP.wq CdP.nq wsWords; omega
  refine WP.mono (redc_ok M h.ctx h.xv h2 hwq (by omega) hq (show aX < 8 by decide))
    fun t ⟨hc, hv, hlt, he, hf, k⟩ => ?_
  rw [h.x] at he
  have hr := fun r he => (redcRanges_ok p.wq r he).2
  have hL : inner p.w + slot p.wq 8 ≤ p.Z := by have := h.ctx.hi; omega
  obtain ⟨hb, hi, hh⟩ := h.base.child h.ctx hL hf hr k
  have h256 : 256 ≤ slot p.wq 8 := by unfold slot hdrBytes; omega
  have hn := h.ctx.scr.nowrap
  have hX := slot_le (w := p.w) (show aX < 8 by decide)
  have hInner : slot p.w 8 ≤ inner p.w := Nat.le_refl _
  have hx : wv t.mem p.B (slot p.w aX) p.w = p.P - 1 :=
    (hf.wv_below hr (by omega) (by omega) (by omega)).trans h.x
  exact ⟨⟨mi, ⟨hb, hc, hv, (hh _ (by decide)).trans h.ep, (hh _ (by decide)).trans h.el,
    (hh _ (by decide)).trans h.g, (hh _ (by decide)).trans h.q, hx⟩, redc_zero ho hlt he⟩,
    hi, fun i hi => hh i (by omega), k.mono (by decide)⟩

theorem QWork.keep {p : CdP} {mi : BitVec 64} {s t : State} {rs : List Reg}
    (h : QWork p mi s) (hm : t.mem = s.mem) (k : Keep rs s t) (hd : t.gpr .rdi = s.gpr .rdi) : QWork p mi t :=
  ⟨h.base.keep (by rw [hm]; exact InScr.refl _ _ _) k (fun _ _ => by rw [hm]),
    (h.ctx.toMem.congr hm k.2.2).ctx (hd.trans h.ctx.rdi),
    ⟨by rw [hm]; exact h.xv.n, by rw [hm]; exact h.xv.inv, by rw [hm]; exact h.xv.one⟩,
    by rw [hm]; exact h.ep, by rw [hm]; exact h.el, by rw [hm]; exact h.g,
    by rw [hm]; exact h.q, by rw [hm]; exact h.x⟩

theorem residue_test {p : CdP} {s : State} (h : Residue p s) :
    WP isa (seqs (isZero aXc ++ ([.block [.alu .test .rax (.reg .rax)]] : List (Prog isa)))) s
      (StepPost p s fun t => Residue p t ∧ t.zf = some (!decide ((p.P - 1) % p.Q = 0))) := by
  obtain ⟨mi, hw, hz⟩ := h
  have hk := hw.base.k1
  have hk' := hw.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  have h2 : 2 ≤ p.wq := Nat.le_max_left _ _
  have hwq : p.wq ≤ p.w := by unfold CdP.wq CdP.nq wsWords; omega
  refine wp_seqs_append (a := isZero aXc) (by simp [isZero, ltArr, cmpArr]) (by simp)
    (WP.mono (ltArr_ok hw.ctx.good (Nat.le_refl _) (by omega) (by omega)
      (show aXc < 8 by decide) (show aOne < 8 by decide)) fun u ⟨ha, hm, k⟩ => ?_)
  rw [hw.xv.one] at ha
  have he : (wv s.mem (off p.B (inner p.w)) (slot p.wq aXc) p.wq < 1) = ((p.P - 1) % p.Q = 0) :=
    propext (by omega)
  have ha' : u.gpr .rax = bit ((p.P - 1) % p.Q = 0) := by simpa only [bit, he] using ha
  simp only [seqs]
  refine WP.mono (test_bit_ok ha') fun t ⟨hz', hm', kk⟩ => ?_
  have hm'' := hm'.trans hm
  have kt := keep_trans k (kk.mono (by decide))
  refine ⟨⟨⟨mi, hw.keep hm'' kt (kt.gpr (by decide)), ?_⟩, hz'⟩,
    by rw [hm'']; exact InScr.refl _ _ _, (fun _ _ => by rw [hm'']), kt.mono (by decide)⟩
  rw [hm'']; exact hz

end VG.Proof.Ffdh.X86_64.CheckDomain
