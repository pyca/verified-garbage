module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTBlocks
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTTab
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.CTFixed
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Hash
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBase
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTCalls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.CTBlocks
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid

/-!
# RSASSA-PSS verification on PPC64LE: hashing `M'` for a given salt length, twice

Untrusted: everything here is checked by Lean. After the public operation,
two runs are compared through the anchor `a` with `BL`: `Base` from entry
states whose encoding parameters are those of their registers and that hold
the tables of the hash functions (`PreL`: the hash function's of `MdHash`
and MGF1's of `Hash`, as `Tabs` names them), that agree with the anchor on
what `Base` fixes and on the tables and the addresses of their functions
(`PubL`), with the entry's addresses of statics. `hashFixed_ct`: the hash of
`M'` for a given salt length, its blocks by the taint analysis and its calls
through the table by `tcall_twoM`, `init_ct`, `upd_ct` and `fin_ct`, with
arguments from the anchor.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oSt oDig oW oRsa Fns)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off fx hiRegs Agree Ok B BT BT.b B.agree B.only pins_of st_wp
  two_seq UpdArgs FinArgs init_ct upd_ct fin_ct HashCT sdis sc_cov cR_dis hfits offs st_taint TabS TabA)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep Two Pins two_post wp_li wp_addi wp_subi wp_add wp_mov wp_nil
  eval_nonzero)

/-- The tables' hash functions and their functions, which the proofs take:
MGF1's `G` with the functions `g` of the tables of `Hash`, and the hash
function `H`, whose compression function `cn` (of code `cc`) and digest `dn`
(of code `dc`) its table names, with the functions `f` of the tables of
`MdHash`. -/
structure Tabs where
  G : Hash
  g : Fns
  H : Hash
  cn : String
  cc : Prog isa
  dn : String
  dc : Prog isa
  f : MdFns

/-- The tables on entry. -/
def TabsOn (Z : Tabs) (s : State) : Prop :=
  TabS Z.G Z.g gArg Sp s (stackArg s 7) ∧ MdTabS Z.H Z.cn Z.cc Z.dn Z.dc Z.f hArg Sp s (stackArg s 6)

/-- The tables at the anchor's addresses, with its addresses of their functions. -/
def TabsAg (Z : Tabs) (a s : State) : Prop :=
  stackArg s 7 = stackArg a 7 ∧ s.syms Z.G.initN = a.syms Z.G.initN ∧ s.syms Z.G.updN = a.syms Z.G.updN ∧
    s.syms Z.G.finN = a.syms Z.G.finN ∧ stackArg s 6 = stackArg a 6 ∧ s.syms Z.H.initN = a.syms Z.H.initN ∧
    s.syms Z.H.updN = a.syms Z.H.updN ∧ s.syms Z.H.finN = a.syms Z.H.finN ∧ s.syms Z.cn = a.syms Z.cn ∧
    s.syms Z.dn = a.syms Z.dn

/-- An entry state whose encoding parameters are those of its registers, with
the tables. -/
abbrev PreL (D : Nat) (Z : Tabs) (s : State) : Prop :=
  Lay D s (lo s).toNat (dbLen D s).toNat ((cm s).setWidth 8) ∧ TabsOn Z s

/-- What it agrees on with the anchor. -/
abbrev PubL (D : Nat) (Z : Tabs) (a s : State) : Prop := Agree Sp (vP D) a s ∧ TabsAg Z a s

theorem Lay.canon {D lN dN : Nat} {c : Byte} {s : State} (L : Lay D s lN dN c) :
    Lay D s (lo s).toNat (dbLen D s).toNat ((cm s).setWidth 8) := by
  have h1 : (lo s).toNat = lN := by rw [L.hlo, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := L.l1; omega_arith)]
  have h2 : (dbLen D s).toNat = dN := by
    rw [L.hdb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := L.hk; have := L.k2; omega_arith)]
  have h3 : (cm s).setWidth 8 = c := by rw [L.hc, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  rw [h1, h2, h3]; exact L

theorem lOk (D : Nat) (Z : Tabs) : Ok Sp (vP D) (PreL D Z) (PubL D Z) := ⟨fun P => P.1.F, fun p => p.1⟩

theorem tabG (D : Nat) (Z : Tabs) : TabA Z.G Z.g gArg Sp (PreL D Z) (PubL D Z) :=
  ⟨fun P => P.2.1, fun p => p.2.1, fun p => p.2.2.1, fun p => p.2.2.2.1, fun p => p.2.2.2.2.1⟩

theorem tabH (D : Nat) (Z : Tabs) : MdTabA Z.H Z.cn Z.cc Z.dn Z.dc Z.f hArg Sp (PreL D Z) (PubL D Z) :=
  ⟨fun P => P.2.2, fun p => p.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.1,
    fun p => p.2.2.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.2.2.1, fun p => p.2.2.2.2.2.2.2.2.2.2⟩

/-- `Base` from such an entry state agreeing with the anchor, with its
addresses of statics. -/
abbrev BL (D : Nat) (Z : Tabs) : State → State → Prop := BT Sp (vP D) (PreL D Z) (PubL D Z)

section
variable {D : Nat} {Z : Tabs}

theorem BL.r14 {a t : State} (h : BL D Z a t) : t.gpr .r14 = Sp a := ((h.b.agree (lOk D Z)).2.1)
theorem BL.v {a t : State} (h : BL D Z a t) {r : Reg} (hr : r ∈ fx := by decide) : t.gpr r = vP D a r :=
  (h.b.agree (lOk D Z)).2.2 r hr
theorem BL.only' {a t t' : State} {rs : List Reg} (h : BL D Z a t) (o : Only rs t t') (y : t'.syms = t.syms)
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs := by decide) : BL D Z a t' :=
  let ⟨s, P, p, b, sy⟩ := h; ⟨s, P, p, b.only P.1.F o hrs, y.trans sy⟩

theorem bl_pins {α : Type} {Φ : α → State → Prop} {an : α → State} (h : ∀ x t, Φ x t → BL D Z (an x) t)
    (rs : List Reg) (hrs : ∀ r ∈ rs, r ∈ Reg.r14 :: fx := by decide) : Pins Φ rs :=
  pins_of (lOk D Z) (fun x t hx => (h x t hx).b) rs hrs

/-- The anchor's numbers, from an entry state with `PreL` agreeing with it. -/
theorem agree_lay {a s : State} (P : PreL D Z s) (g : PubL D Z a s) :
    Lay D s (lo a).toNat (dbLen D a).toNat ((cm a).setWidth 8) := by
  have e17 : lo s = lo a := g.1.v .r17 (by decide)
  have e18 : cm s = cm a := g.1.v .r18 (by decide)
  have e21 : dbLen D s = dbLen D a := g.1.v .r21 (by decide)
  rw [← e17, ← e18, ← e21]; exact P.1

theorem BL.dn {a t : State} (h : BL D Z a t) :
    1 ≤ (dbLen D a).toNat ∧ (lo a).toNat + (dbLen D a).toNat + D + 1 ≤ 1024 ∧ 0 < D ∧ D ≤ 64 := by
  obtain ⟨s, P, g, -, -⟩ := h
  have L := agree_lay P g
  have := L.hk; have := L.k2
  exact ⟨L.d1, by omega_arith, L.D0, L.D64⟩

end

/-! ## `hashFixed`, through the table -/

theorem hashFixed_ct {D : Nat} {Z : Tabs} (hH : HashOK Z.H) (cH : HashCT hH) (hD : Z.H.D = D) :
    RelCT isa (Two fun a t => BL D Z a t ∧ (stackArg a 0).toNat + 8 + D ≤ 2048) (hashFixed Z.H Z.f hArg)
      fun _ _ => True :=
  hashFixedG_ct (lOk D Z) hH cH (tabH D Z) hD (fun a => (stackArg a 0).toNat) fun a => by
    show stackArg a 0 = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

end VG.Proof.RsaPss.PPC64LE
