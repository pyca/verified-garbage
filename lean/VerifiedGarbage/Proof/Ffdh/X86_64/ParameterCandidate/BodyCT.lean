module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.EntryCTData

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.EntryCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CandidateCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.EntryCTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.EntryCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CandidateCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import Mathlib.Algebra.Group.Nat.Defs

/-! # FFDH parameter generation on x86-64: timing of the callable body -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 (hdr)
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.RsaKeyGen.X86_64

def EntryGuard (p : CandidateP) (s : State) : Prop := Entered p s ∧ s.cf = some (decide (p.rand.length < p.k))

private theorem guard_after (p : CandidateP) (s : State) (h : Entered p s) :
    WP isa (.block [.mov .rax (.mem (hdr oRandLeft)), .alu .cmp .rax (.mem (hdr oLen))]) s (EntryGuard p) := by
  obtain ⟨ht, hd, hw, hk⟩ := h
  have hlen := ht.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  have hleft : word s.mem p.B (8 * oRandLeft) = BitVec.ofNat 64 p.rand.length := by simpa using ht.left
  have hrd : ∀ j < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * j)) 8 :=
    fun j hj => ht.base.scr.ld (by omega_using [hj, ht.base.header_room])
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.cf = some (decide (p.rand.length < p.k)) ∧ t.mem = s.mem)
    (by
      xrun [State.ea, hdr, hdrOff, hd, hlen, hleft, hrd oRandLeft (by decide), hrd oLen (by decide)]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht.base.randLen,
        Nat.mod_eq_of_lt (show p.k < 2 ^ 64 by omega_using [ht.base.widths.2])]) rfl)
    fun t ⟨⟨hz, hm⟩, k⟩ => ?_
  exact ⟨⟨(ht.same_mem hm k (by decide)).1, (k.gpr (by decide)).trans hd, k.2.2.trans hw, hk⟩, hz⟩

private theorem guard_full {s₁ s₂ : State}
    (h : Two (fun p s => EntryGuard p s ∧ isa.eval .b s = some false) s₁ s₂) :
    Two (fun d s => OuterState d s ∧ d.used = 0) s₁ s₂ := by
  refine two_bind (fun p t₁ t₂ h₁ h₂ => ?_) h
  have ha : p.k ≤ p.rand.length := by
    have hx : decide (p.rand.length < p.k) = false := by simpa only [eval, h₁.1.2, Option.some.injEq] using h₁.2
    omega_using [of_decide_eq_false hx]
  let d : CandidatePublic := ⟨p, 0, candidateWr p, ha⟩
  exact ⟨d, ⟨⟨⟨h₁.1.1.1, h₁.1.1.2.2.1, h₁.1.1.2.2.2⟩, h₁.1.1.2.1⟩, rfl⟩,
    ⟨⟨⟨h₂.1.1.1, h₂.1.1.2.2.1, h₂.1.1.2.2.2⟩, h₂.1.1.2.1⟩, rfl⟩⟩

theorem body_ct (M : Mont) (R : R2Impl M) (K : Kernel) :
    RelCT isa (Two CR) (body M.mm R.code K.run) fun _ _ => True := by
  unfold body
  refine RelCT.seq (RelCT.block_append (RelCT.seq entry_ct
    (two_piece [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst r; exact h₁.2.1.trans h₂.2.1.symm)
      (by taint_decide) guard_after))) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by simp [eval, h₁.2, h₂.2])
    (two_taint [] (pins_nil _) (by taint_decide)) ?_
  exact (testCandidate_ct M R K).mono (fun _ _ h => guard_full h) (fun _ _ h => h)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
