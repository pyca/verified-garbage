module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.WithQ
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Divides
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Loads
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves

/-! # FFDH domain validation on x86-64: the main computation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave loadArr)

private theorem bit_true {P : Prop} [Decidable P] (hp : P) : bit P = 1 := by
  simp only [bit, ite_eq_left hp]

abbrev CdP.accept (p : CdP) : Prop := p.gr ∧ (p.dl = 2 * p.k ∨ p.relation)

private theorem main_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main M.mm E.code (.seq (.block r2Head) R.code) =
      seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++ (loadArr aXm sG sK ++
        (rangeTest aXm ++ ([.ite .e (retInner 0) (.seq (.block (leave :: qTest))
          (.ite .e (ret 1) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code)))))] : List (Prog isa))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main, List.append_assoc]

theorem main_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : CdP} {s : State}
    (h : Base p s) (hd : s.gpr .rdi = p.B) (hG : word s.mem p.B (8 * sG) = off p.dp p.k)
    (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)) (hm : p.mv = true) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.main M.mm E.code (.seq (.block r2Head) R.code)) s
      (StepPost p s fun t => t.gpr .rdi = p.B ∧ t.gpr .rax = bit p.accept) := by
  rw [main_eq]
  refine wp_seqs_append (a := ([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)
    (b := loadArr aXm sG sK ++ (rangeTest aXm ++ ([.ite .e (retInner 0) (.seq (.block (leave :: qTest))
      (.ite .e (ret 1) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code)))))] : List (Prog isa))))
    (by simp) (by simp [loadArr])
    (WP.mono (setup_work h hd hG hQ hm) fun u₁ S₁ => ?_)
  obtain ⟨mi, hw₁, hd₁⟩ := S₁.1
  refine wp_seqs_append (a := loadArr aXm sG sK) (by simp [loadArr]) (by simp [rangeTest])
    (WP.mono (load_generator hw₁ hd₁) fun u₂ S₂ => ?_)
  refine wp_seqs_append (a := rangeTest aXm) (by simp [rangeTest, range, gt1, ltArr, cmpArr]) (by simp)
    (WP.mono (generator_range S₂.1.1 S₂.1.2.1 S₂.1.2.2) fun u₃ S₃ => ?_)
  have H := (S₁.trans S₂).trans S₃
  obtain ⟨hw₃, hd₃, hz₃⟩ := S₃.1
  simp only [seqs]
  refine WP.ite (!decide p.gr) (by simp [eval, hz₃]) (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬p.gr := of_decide_eq_false (by simpa only [Bool.not_eq_true'] using hn)
    exact WP.mono (ret_inner (hw₃.mem.ctx hd₃) (r := 0) (by decide)) fun t ⟨hdi, ha, hmem, k⟩ =>
      ⟨⟨hdi, by simpa [bit, CdP.accept, hn'] using ha⟩, by rw [hmem]; exact H.2.1,
        (fun i hi => by rw [hmem]; exact H.2.2.1 i hi), keep_trans H.2.2.2 (k.mono (by decide))⟩
  · have hy' : p.gr := of_decide_eq_true (by simpa only [Bool.not_eq_false'] using hy)
    have hb₃ := hw₃.base
    have hk := hb₃.k1
    have hk' := hb₃.k2
    have hdl := hb₃.dl
    refine WP.seq (WP.mono (leaveQ_ok (hw₃.mem.ctx hd₃)
      (hb₃.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [CdP.headers]))
      (hb₃.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]))
      (by rcases hdl with h | h <;> omega) (by rcases hdl with h | h <;> omega))
      fun u₄ ⟨hd₄, _, hz₄, hm₄, k₄⟩ => ?_)
    have hw₄ := hw₃.keep hm₄ k₄
    have H₄ : StepPost p s (fun _ => True) u₄ := ⟨trivial,
      by rw [hm₄]; exact H.2.1, (fun i hi => by rw [hm₄]; exact H.2.2.1 i hi),
      keep_trans H.2.2.2 (k₄.mono (by decide))⟩
    refine WP.ite (decide (p.dl = 2 * p.k)) (by simp [eval, hz₄]) (fun hq => ?_) (fun hq => ?_)
    · have hq' := of_decide_eq_true hq
      exact WP.mono (ret_ok u₄ (r := 1) (by decide)) fun t ⟨ha, hm', k⟩ =>
        ⟨⟨(k.gpr (by decide)).trans hd₄, ha.trans (bit_true (show p.accept from ⟨hy', Or.inl hq'⟩)).symm⟩,
          by rw [hm']; exact H₄.2.1,
          (fun i hi => by rw [hm']; exact H₄.2.2.1 i hi), keep_trans H₄.2.2.2 (k.mono (by decide))⟩
    · have hn' := of_decide_eq_false hq
      have hq' : p.dl = 3 * p.k := by rcases hdl with h | h <;> omega
      refine WP.mono (withQ_ok M E R hw₄ hd₄ hm hq') fun t S₅ => ?_
      have he : p.relation = p.accept := propext (by simp only [CdP.accept]; grind)
      exact ⟨⟨S₅.1.1, by simpa only [bit, he] using S₅.1.2⟩, (H₄.trans S₅).2⟩

end VG.Proof.Ffdh.X86_64.CheckDomain
