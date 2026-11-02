module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkPre
public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkFrame
import VerifiedGarbage.Proof.Framework.Contract

/-!
# EMSA-PSS's check of an encoding on AArch64: constant time, the public data

The pointers, the lengths, the salt length and `any_salt_len` are public
(`PubC`, from `checkEncodingContract.pub`); the digest and the encoding are
secret. Two runs with the same public data as an anchor `a` (`E`) are
related at each point of the code by what correctness says there.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (fb)

/-- The working space. -/
abbrev scr (s : State) : Addr := s.gpr .x6

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers, the lengths and the salt length's arguments. -/
structure PubC (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x6, .x7], s.gpr r = a.gpr r
  a5 : (s.gpr .x5).setWidth 32 = (a.gpr .x5).setWidth 32

theorem PubC.refl (s : State) : PubC s s := ⟨rfl, fun _ _ => rfl, rfl⟩

theorem pubC_of (G : Spec.Mgf1.Hash) {S : Nat} {s₁ s₂ : State}
    (h : (Proof.RsaPss.checkEncodingContract G G abi S).pub s₁ s₂) : PubC s₁ s₂ := by
  sig_pub [Proof.RsaPss.checkEncodingContract, Proof.RsaPss.checkEncodingSig, abi, argRegs, List.append_eq] at h
  obtain ⟨hsp, h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨hsp.symm, fun r hr => ?_, h5.symm⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h6.symm, h7.symm]

/-- An entry state with the anchor's public data. -/
def E (D : Nat) (a s : State) : Prop := PreC D s ∧ PubC a s

namespace E
variable {D : Nat} {a s : State} (h : E D a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x6, .x7]) : s.gpr r = a.gpr r := h.2.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.sp]

theorem scr : scr s = scr a := h.gpr (r := .x6) (by decide)

theorem any : anyC s = anyC a := by rw [anyC, anyC, h.2.a5]

theorem z : zC s = zC a := by rw [zC, zC, h.gpr (r := .x2) (by decide), h.gpr (r := .x3) (by decide)]

end E

end VG.Proof.RsaPss.AArch64.Chk
