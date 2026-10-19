module
public import VerifiedGarbage.Impl.Ffdh.X86_64.Exchange
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Arithmetic

import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PubMain

/-! # FFDH exchange on x86-64: compose the arithmetic and output -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

theorem StepPost.trans {p : ExP} {s u t : State} {P Q : State → Prop}
    (h : StepPost p s P u) (h' : StepPost p u Q t) : StepPost p s Q t :=
  ⟨h'.1, h.2.1.trans h'.2.1, fun i hi => (h'.2.2.1 i hi).trans (h.2.2.1 i hi),
    keep_trans h.2.2.2 h'.2.2.2⟩

def RunFrame (p : ExP) (m m' : Mem) : Prop :=
  ∀ x, p.Z ≤ ofs p.B x → (∀ i < p.k, x ≠ p.op + BitVec.ofNat 64 i) → m' x = m x

def MainPost (p : ExP) (xb : List Byte) (s t : State) : Prop :=
  Spec.Rsa.bytesAt t.mem p.op p.k = Spec.Rsa.i2osp (if p.fl xb then p.z xb else 0) p.k ∧
    t.gpr .rax = bit (p.fl xb) ∧ t.gpr .rdi = p.B ∧ RunFrame p s.mem t.mem ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧
    Keep (.rdi :: mmRegs) s t

private theorem main_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.Exchange.main M.mm E.code (.seq (.block r2Head) R.code) =
      seqs ((([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup) ++
        (([.seq (.block r2Head) R.code] : List (Prog isa)) ++
          (pow M.mm E.code sY sK sX sXl ++ (range aY ++
            ([.block VG.Impl.Ffdh.X86_64.Domain.Exchange.finBlk, storeBE,
              .block [.mov .rax (.mem (hdr sF)), leave]] : List (Prog isa)))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.Exchange.main, List.append_assoc]

theorem main_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : ExP} {xb : List Byte} {s : State}
    (hb : Base p xb s) (hdi : s.gpr .rdi = p.B) (hm : p.mv = true) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.Exchange.main M.mm E.code (.seq (.block r2Head) R.code)) s
      (MainPost p xb s) := by
  rw [main_eq]
  refine wp_seqs_append (by simp [pSetup]) (by simp) (WP.mono (setup_entered hb hdi hm) fun u₁ h₁ => ?_)
  refine wp_seqs_cons (by simp [pow]) (WP.mono (entered_ready M R h₁.1 hm) fun u₂ h₂ => ?_)
  refine wp_seqs_append (a := pow M.mm E.code sY sK sX sXl) (by simp [pow]) (by simp [range, gt1, ltArr, cmpArr])
    (WP.mono (ready_value M E h₂.1) fun u₃ h₃ => ?_)
  refine wp_seqs_append (a := range aY) (by simp [range, gt1, ltArr, cmpArr]) (by simp)
    (WP.mono (value_checked h₃.1) fun u₄ h₄ => ?_)
  have H := ((h₁.trans h₂).trans h₃).trans h₄
  exact WP.mono (output_ok h₄.1) fun t ⟨hb, ha, hd, hf, hs, k⟩ =>
    ⟨hb, ha, hd, fun x hx hi => (hf x hi).trans (H.2.1 x hx),
      fun i hi => (hs i hi).trans (H.2.2.1 i hi), keep_trans H.2.2.2 k⟩

end VG.Proof.Ffdh.X86_64.Exchange
