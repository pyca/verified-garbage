module

public import VerifiedGarbage.Proof.RsaPss.AArch64.EncPre
import VerifiedGarbage.Proof.Framework.Contract

/-!
# EMSA-PSS's encoding on AArch64: constant time, the public data

The pointers and the lengths are public (`PubE`, from `encodeContract.pub`);
the digest and the salt are secret. Two runs with the same public data as an
anchor `a` (`E`) are related at each point of the code by what correctness
says there.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (fb)

/-- The working space. -/
abbrev scr (s : State) : Addr := s.gpr .x6

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths. -/
structure PubE (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r

theorem PubE.refl (s : State) : PubE s s := ⟨rfl, fun _ _ => rfl⟩

theorem pubE_of (G : Spec.Mgf1.Hash) {S : Nat} {s₁ s₂ : State}
    (h : (Proof.RsaPss.encodeContract G G abi S).pub s₁ s₂) : PubE s₁ s₂ := by
  sig_pub [Proof.RsaPss.encodeContract, Proof.RsaPss.encodeSig, abi, argRegs, List.append_eq] at h
  obtain ⟨hsp, h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨hsp.symm, fun r hr => ?_⟩
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm]

/-- An entry state with the anchor's public data. -/
def E (D : Nat) (a s : State) : Prop := PreE D s ∧ PubE a s

namespace E
variable {D : Nat} {a s : State} (h : E D a s)
include h

theorem gpr {r : Reg} (hr : r ∈ argRegs) : s.gpr r = a.gpr r := h.2.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.sp]

theorem scr : scr s = scr a := h.gpr (r := .x6) (by decide)

end E

end VG.Proof.RsaPss.AArch64.Enc
