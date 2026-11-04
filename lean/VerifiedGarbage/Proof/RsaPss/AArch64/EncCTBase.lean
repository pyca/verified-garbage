module

public import VerifiedGarbage.Proof.RsaPss.AArch64.EncPre
public import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf
import VerifiedGarbage.Proof.Framework.Contract

/-!
# EMSA-PSS's encoding on AArch64: constant time, the public data

The pointers, the lengths and the tables' addresses are public (`PubE`),
and so are the addresses of the tables' functions; the digest and the salt
are secret. Two runs with the same public data as an anchor `a` (`E`), whose
tables name the same functions (`Tabs`), are related at each point of the
code by what correctness says there.
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.RsaPss.AArch64.Sgn (fb)

/-- The working space. -/
abbrev scr (s : State) : Addr := s.gpr .x6

/-- The functions the tables name: the hash function `H` (whose digest is
`dn`) and MGF1's `G`, the calls' lists `f` and `g`, and the tables of the
precondition. -/
structure Tabs where
  H : Impl.Pbkdf2.Md.AArch64.Hash
  dn : String
  f : MdFns
  G : Impl.Pbkdf2.Md.AArch64.Stream
  g : Impl.RsaOaep.AArch64.Mgf1.Table.Fns
  tsH : List FnTable
  tsG : List FnTable

/-- The tables at the stack arguments 0 and 1 of `s` name `T`'s functions. -/
abbrev Tabs.At (T : Tabs) (s : State) : Prop := TabsAt T.H T.dn T.f T.G T.g (stackArg s 0) (stackArg s 1) s

/-- The names of `T`'s functions the code calls. -/
def Tabs.names (T : Tabs) : List String := [T.H.initN, T.H.compN, T.dn, T.G.initN, T.G.updN, T.G.finN]

/-- The public data of an entry state `s` is the anchor `a`'s: the
pointers and lengths, and the tables' addresses. -/
structure PubE (a s : State) : Prop where
  sp : s.sp = a.sp
  g : ∀ r ∈ argRegs, s.gpr r = a.gpr r
  sa : ∀ j < 2, stackArg s j = stackArg a j

theorem PubE.refl (s : State) : PubE s s := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- An entry state with the anchor's public data, whose tables name `T`'s
functions at the anchor's addresses. -/
def E (T : Tabs) (a s : State) : Prop :=
  PreE T.H.D T.tsH T.tsG s ∧ PubE a s ∧ T.At s ∧ ∀ n ∈ T.names, s.syms n = a.syms n

namespace E
variable {T : Tabs} {a s : State} (h : E T a s)
include h

theorem gpr {r : Reg} (hr : r ∈ argRegs) : s.gpr r = a.gpr r := h.2.1.g r hr

theorem fb : fb s = fb a := by show s.sp - _ = a.sp - _; rw [h.2.1.sp]

theorem scr : scr s = scr a := h.gpr (r := .x6) (by decide)

theorem arg {j : Nat} (hj : j < 2) : stackArg s j = stackArg a j := h.2.1.sa j hj

theorem sym {n : String} (hn : n ∈ T.names) : s.syms n = a.syms n := h.2.2.2 n hn

end E

end VG.Proof.RsaPss.AArch64.Enc
