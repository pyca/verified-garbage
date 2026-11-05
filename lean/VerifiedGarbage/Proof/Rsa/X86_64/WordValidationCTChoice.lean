module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordValidationCTMain
public import VerifiedGarbage.Proof.Rsa.X86_64.WordValidationGuard
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordValidationCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordValidationGuard
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyCTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Public dispatch for CRT-key validation -/

@[expose] public section
namespace VG.Proof.Rsa.X86_64.Key
open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Retain the public modulus until the algorithm has been selected. -/
def MFixed (a : MPub × List Byte) (s : State) : Prop :=
  ∃ db pb qb dpb dqb qib ev, MainPre s a.1.kp.B a.1.kp.Z a.1.k a.1.np a.1.kp.pd a.1.kp.pp a.1.kp.pq
    a.1.kp.pdp a.1.kp.pdq a.1.kp.pqi a.2 db pb qb dpb dqb qib ev ∧
    a.1.kp.w = (a.1.k + 7) / 8 ∧ db.length = a.1.kp.dl ∧ pb.length = a.1.kp.pl ∧ qb.length = a.1.kp.ql

theorem MFixed.toM {a : MPub × List Byte} {s : State} (h : MFixed a s) : M0 a.1 s := by
  obtain ⟨db, pb, qb, dpb, dqb, qib, ev, hp, hw, hd, hpl, hql⟩ := h
  exact ⟨a.2, db, pb, qb, dpb, dqb, qib, ev, hp, hw, hd, hpl, hql⟩

def ValidationHead (a : MPub × List Byte) (s : State) : Prop :=
  MFixed a s ∧ s.gpr .r12 = BitVec.ofNat 64 ((a.1.k + 7) / 8) ∧ s.gpr .rdx = a.1.np

def validationPublicGuard (a : MPub × List Byte) : BitVec 64 :=
  VG.Proof.Rsa.X86_64.WordDivide.guardVal ((a.1.k + 7) / 8) a.1.k a.1.kp.pl a.1.kp.ql ((a.2[0]?).getD 0)

def ValidationTest (a : MPub × List Byte) (s : State) : Prop :=
  MFixed a s ∧ s.zf = some (validationPublicGuard a == 0)

theorem validationHead_ct : RelCT isa (Two MFixed) (.block WordValidation.guardHead) (Two ValidationHead) := by
  refine two_piece [.rdi] ?_ (by taint_decide) ?_
  · rintro a s₁ s₂ ⟨_, _, _, _, _, _, _, h₁, _⟩ ⟨_, _, _, _, _, _, _, h₂, _⟩ r hr
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi]
  · rintro a s ⟨db, pb, qb, dpb, dqb, qib, ev, h, hw, hd, hpl, hql⟩
    exact WP.mono (validationGuardHead_ok h) fun t ⟨ht, _, h12, hdx, _⟩ =>
      ⟨⟨db, pb, qb, dpb, dqb, qib, ev, ht, hw, hd, hpl, hql⟩, h12, hdx⟩

theorem validationTail_ct : RelCT isa (Two ValidationHead) (.block WordValidation.guardTail) (Two ValidationTest) := by
  refine two_piece [.rdi, .rdx] ?_ (by taint_decide) ?_
  · rintro a s₁ s₂ ⟨⟨_, _, _, _, _, _, _, h₁, _⟩, _, d₁⟩ ⟨⟨_, _, _, _, _, _, _, h₂, _⟩, _, d₂⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.rdi, h₂.rdi]
    · rw [d₁, d₂]
  · rintro a s ⟨⟨db, pb, qb, dpb, dqb, qib, ev, h, hw, hd, hpl, hql⟩, h12, hdx⟩
    refine WP.mono (validationGuardTail_ok h h12 hdx) fun t ⟨ht, _, hz, _⟩ => ?_
    refine ⟨⟨db, pb, qb, dpb, dqb, qib, ev, ht, hw, hd, hpl, hql⟩, ?_⟩
    have hnl : 0 < a.2.length := by rw [h.nl]; have := h.k1; omega
    simpa only [validationPublicGuard, hpl, hql, List.getElem?_eq_getElem hnl, Option.getD_some] using hz

theorem validationChoice_ct : RelCT isa (Two MFixed)
    (WordValidation.choice CheckCrtKey.mainFast CheckCrtKey.main) (fun _ _ => True) := by
  unfold WordValidation.choice
  refine RelCT.seq validationHead_ct (RelCT.seq validationTail_ct ?_)
  refine two_ite (fun a s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · exact ckMainFast_ct.mono (fun _ _ h => two_bind (fun a s₁ s₂ h₁ h₂ =>
      ⟨a.1, h₁.1.1.toM, h₂.1.1.toM⟩) h) (fun _ _ h => h)
  · exact ckMain_ct.mono (fun _ _ h => two_bind (fun a s₁ s₂ h₁ h₂ =>
      ⟨a.1, h₁.1.1.toM, h₂.1.1.toM⟩) h) (fun _ _ h => h)

end VG.Proof.Rsa.X86_64.Key
