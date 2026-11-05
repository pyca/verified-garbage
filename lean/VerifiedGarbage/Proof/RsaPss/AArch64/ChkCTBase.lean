module

public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkPre
public import VerifiedGarbage.Proof.RsaPss.AArch64.ChkFrame
public import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf

/-!
# EMSA-PSS's check of an encoding on AArch64: constant time, the public data

The pointers, the lengths, the salt length, `any_salt_len` and the tables'
addresses are public (`PubC`), and so are the addresses of the tables'
functions; the digest and the encoding are secret. Two runs with the same
public data as an anchor `a` (`E`) are related at each point of the code by
what correctness says there.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Chk

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (fb)

/-- The working space. -/
abbrev scr (s : State) : Addr := s.gpr .x6

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers, the lengths, the salt length's arguments and the tables'
addresses. -/
structure PubC (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x6, .x7], s.gpr r = a.gpr r
  a5 : (s.gpr .x5).setWidth 32 = (a.gpr .x5).setWidth 32
  sa : ∀ j < 2, stackArg s j = stackArg a j

theorem PubC.refl (s : State) : PubC s s := ⟨rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

/-- An entry state with the anchor's public data, whose tables name `T`'s
functions at the anchor's addresses. -/
def E (T : Tabs) (a s : State) : Prop :=
  PreC T.H.D T.tsH T.tsG s ∧ PubC a s ∧ T.At s ∧ ∀ n ∈ T.names, s.syms n = a.syms n

namespace E
variable {T : Tabs} {a s : State} (h : E T a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x6, .x7]) : s.gpr r = a.gpr r := h.2.1.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.1.sp]

theorem scr : scr s = scr a := h.gpr (r := .x6) (by decide)

theorem any : anyC s = anyC a := by rw [anyC, anyC, h.2.1.a5]

theorem arg {j : Nat} (hj : j < 2) : stackArg s j = stackArg a j := h.2.1.sa j hj

theorem sym {n : String} (hn : n ∈ T.names) : s.syms n = a.syms n := h.2.2.2 n hn

theorem z : zC s = zC a := by rw [zC, zC, h.gpr (r := .x2) (by decide), h.gpr (r := .x3) (by decide)]

end E

end VG.Proof.RsaPss.AArch64.Chk
