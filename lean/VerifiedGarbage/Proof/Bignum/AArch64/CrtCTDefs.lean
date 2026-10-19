module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtUnit
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup

import Mathlib.Data.Int.ModEq
meta import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-!
# RSA with the CRT on AArch64: constant time, the pieces

Two runs agree on the public data (the pointers, the lengths and `n`) but
not on the input or the private key. Each piece of `main` is constant time
for the hypotheses of its correctness lemma, with what is public fixed (a
`…Pub` structure) and the rest (`-p⁻¹`, `p`, the exponents, the values in
the arrays) existential (a `…Pre` predicate).

The small pieces are proven here; the others are stated (`…CT`) so that
the phases can be proven from them before them.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-! ## Clearing, copying and masking an array -/

theorem GoodW.hl {L : Ws} {s : State} (h : GoodW L s) :
    ∀ i < 32, InRegions (s.rd ++ s.wr) (off L.B (8 * i)) 8 := fun i hi => by
  obtain ⟨_, hg, hZ⟩ := h
  exact hg.ld hZ hi

theorem pins_of {α : Type} {Φ : α → State → Prop} {rs : List Reg} (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs :=
  fun a s₁ s₂ h₁ h₂ r hr => (h a s₁ h₁ r hr).trans (h a s₂ h₂ r hr).symm

/-- Two facts about one run. -/
theorem wp_and {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁) (h₂ : WP isa c s Q₂) :
    WP isa c s fun t => Q₁ t ∧ Q₂ t := by
  obtain ⟨t₁, s₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, q₁, q₂⟩

/-- `Φ a` fixes `x0`. -/
theorem pins_x0B {α : Type} {Φ : α → State → Prop} (B : α → Addr) (h : ∀ a s, Φ a s → s.gpr .x0 = B a) :
    Pins Φ [.x0] :=
  pins_of (fun a _ => B a) fun a s hs r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h a s hs

/-- `zeroArr j`, given that the taint analysis checks its header loads from
`x0` (`by taint_decide` for a given `j`). -/
theorem zeroArr_ct {j : Nat} (hj : j < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x8 (sArr j), ldh .x12 sW, movi .x7 0])
      hc).isSome = true) :
    RelCT isa (Two GoodW) (zeroArr j) fun _ _ => True := by
  unfold zeroArr
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .x8 = off L.B (slot L.w j) ∧
      t.gpr .x12 = BitVec.ofNat 64 L.w) [.x0] pins_goodW hT fun L s h => ?_)
    (two_taint [.x8, .x12] (pins_of (fun L r => if r = .x8 then off L.B (slot L.w j) else BitVec.ofNat 64 L.w)
      fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.x7, .x8, .x12] (Q := fun t => t.gpr .x8 = off L.B (slot L.w j) ∧
      t.gpr .x12 = BitVec.ofNat 64 L.w)
    (by brun [hg.x0, hdr_enc (sArr_lt hj), hdr_enc (show sW < 32 by decide), hl (sArr j) (sArr_lt hj),
      hl sW (by decide), hg.hdr.harr j hj, hg.hdr.hw]) rfl rfl rfl) fun _ h => h.1

/-- `copyArr o a`, given that the taint analysis checks its header loads. -/
theorem copyArr_ct {o a : Nat} (ho : o < 8) (ha : a < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 (sArr o)])
      hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (copyArr o a)) fun _ _ => True := by
  unfold copyArr
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .x12 = BitVec.ofNat 64 L.w ∧
      t.gpr .x16 = off L.B (slot L.w a) ∧ t.gpr .x17 = off L.B (slot L.w o)) [.x0] pins_goodW hT fun L s h => ?_)
    (two_taint [.x12, .x16, .x17] (pins_of (fun L r => if r = .x12 then BitVec.ofNat 64 L.w else
        if r = .x16 then off L.B (slot L.w a) else off L.B (slot L.w o))
      fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.x12, .x16, .x17] (Q := fun t => t.gpr .x12 = BitVec.ofNat 64 L.w ∧
      t.gpr .x16 = off L.B (slot L.w a) ∧ t.gpr .x17 = off L.B (slot L.w o))
    (by brun [hg.x0, hdr_enc (sArr_lt ha), hdr_enc (sArr_lt ho), hdr_enc (show sW < 32 by decide),
      hl (sArr a) (sArr_lt ha), hl (sArr o) (sArr_lt ho), hl sW (by decide), hg.hdr.harr a ha, hg.hdr.harr o ho,
      hg.hdr.hw]) rfl rfl rfl) fun _ h => h.1

/-- `maskArr j`, given that the taint analysis checks its header loads. -/
theorem maskArr_ct {j : Nat} (hj : j < 8) {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x15 sMaskX, ldh .x12 sW, ldh .x16 (sArr j),
      mov .x14 .x12]) hc).isSome = true) :
    RelCT isa (Two GoodW) (seqs (maskArr j)) fun _ _ => True := by
  unfold maskArr
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := fun L t => t.gpr .x14 = BitVec.ofNat 64 L.w ∧
      t.gpr .x16 = off L.B (slot L.w j)) [.x0] pins_goodW hT fun L s h => ?_)
    (two_taint [.x14, .x16] (pins_of (fun L r => if r = .x14 then BitVec.ofNat 64 L.w else off L.B (slot L.w j))
      fun L s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2) (by taint_decide))
  have hl := h.hl
  obtain ⟨_, hg, -⟩ := h
  exact WP.mono (WP.keep [.x12, .x14, .x15, .x16] (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 L.w ∧
      t.gpr .x16 = off L.B (slot L.w j))
    (by brun [hg.x0, hdr_enc (sArr_lt hj), hdr_enc (show sW < 32 by decide), hdr_enc (show sMaskX < 32 by decide),
      hl (sArr j) (sArr_lt hj), hl sW (by decide), hl sMaskX (by decide), hg.hdr.harr j hj, hg.hdr.hw])
    rfl rfl rfl) fun _ h => h.1

/-! ## The other pieces, as claims

Each `…Pre` is the hypotheses of the piece's correctness lemma (named in its
documentation), with the public data fixed by its `…Pub` and the secrets
existential. -/

/-- `gPow_ok`'s data, all public: it computes in `n`'s workspace with `n`
and the prime's length. -/
structure GPub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  Bx : Addr
  wx : Nat

/-- `gPow_ok`'s hypotheses, for the workspace base in slot `sl`. -/
def GPre (sl : Nat) (p : GPub) (s : State) : Prop :=
  Good s p.B p.Z p.w p.minv ∧ slot p.w 8 ≤ p.Z ∧ 2 ≤ p.w ∧ p.w < 2 ^ 30 ∧
    wv s.mem p.B (slot p.w Public.aN) p.w = p.N ∧
    ((word s.mem p.B (slot p.w Public.aN)).toNat * p.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    p.N % 2 = 1 ∧ 1 < p.N ∧
    wv s.mem p.B (slot p.w Public.aR2) p.w % p.N = 2 ^ (64 * p.w) * 2 ^ (64 * p.w) % p.N ∧
    wv s.mem p.B (slot p.w Public.aOne) p.w = 1 ∧ sl < 32 ∧ word s.mem p.B (8 * sl) = p.Bx ∧
    word s.mem p.Bx (8 * sW) = BitVec.ofNat 64 p.wx ∧ InRegions (s.rd ++ s.wr) (off p.Bx (8 * sW)) 8 ∧
    1 ≤ p.wx ∧ p.wx ≤ p.w

/-- `gPow M.mm sl` is constant time. -/
def GPowCT (M : Mont) (sl : Nat) : Prop :=
  RelCT isa (Two (GPre sl)) (seqs (gPow M.mm sl)) fun _ _ => True

/-- The public data of a prime's workspace at `off B o`: `n`'s workspace
(`B`, `Z`, `w`) and the prime's size `wx`. -/
structure XPub where
  B : Addr
  Z : Nat
  o : Nat
  w : Nat
  wx : Nat

/-- A prime's workspace, as Montgomery multiplication sees it. -/
abbrev XPub.ws (p : XPub) : Ws := ⟨off p.B p.o, slot p.wx 8, p.wx⟩

/-- `redc_ok`'s hypotheses. -/
def RPre (j : Nat) (p : XPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X : Nat), SubCtx s p.B p.Z p.o p.w p.wx minv ∧ XVals s p.B p.o p.wx minv X ∧
    2 ≤ p.wx ∧ p.wx ≤ p.w ∧ p.w < 2 ^ 30 ∧ 1 < X ∧ j < 8

/-- `redc M.mm j` is constant time. -/
def RedcCT (M : Mont) (j : Nat) : Prop :=
  RelCT isa (Two (RPre j)) (seqs (redc M.mm j)) fun _ _ => True

/-- The public data of a byte string read from a prime's workspace: its
pointer and length. -/
structure BPub where
  x : XPub
  ptr : Addr
  len : Nat

/-- `crtExpLoop_ok`'s hypotheses, for the exponent's pointer and length in
`n`'s slots `sp` and `sl`. -/
def EPre (sp sl : Nat) (p : BPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (X x y : Nat) (eb : List Byte),
    SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv ∧ 2 ≤ p.x.wx ∧ p.x.wx ≤ p.x.w ∧ p.x.w < 2 ^ 30 ∧
    wv s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aN) p.x.wx = X ∧
    ((word s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
    X % 2 = 1 ∧ wv s.mem (off p.x.B p.x.o) (slot p.x.wx aXc) p.x.wx < X ∧
    wv s.mem (off p.x.B p.x.o) (slot p.x.wx aXc) p.x.wx % X = x * 2 ^ (64 * p.x.wx) % X ∧
    wv s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx < X ∧
    wv s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx % X = y * 2 ^ (64 * p.x.wx) % X ∧
    sp < 32 ∧ sl < 32 ∧ word s.mem p.x.B (8 * sp) = p.ptr ∧
    word s.mem p.x.B (8 * sl) = BitVec.ofNat 64 eb.length ∧ eb.length = p.len ∧ 1 ≤ eb.length ∧
    eb.length ≤ 1024 ∧ Src s p.x.B p.x.Z p.ptr eb

/-- `expLoop M.mm sp sl` is constant time. -/
def ExpCT (M : Mont) (sp sl : Nat) : Prop :=
  RelCT isa (Two (EPre sp sl)) (seqs (expLoop M.mm sp sl)) fun _ _ => True

/-- `primeLoad_ok`'s hypotheses. -/
def LPre (j sp sl : Nat) (p : BPub) (s : State) : Prop :=
  ∃ (minv : BitVec 64) (bs : List Byte), SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx minv ∧ 2 ≤ p.x.wx ∧
    p.x.wx ≤ p.x.w ∧ p.x.w < 2 ^ 30 ∧ j < 8 ∧ sp < 32 ∧ sl < 32 ∧ word s.mem p.x.B (8 * sp) = p.ptr ∧
    word s.mem p.x.B (8 * sl) = BitVec.ofNat 64 bs.length ∧ bs.length = p.len ∧ Src s p.x.B p.x.Z p.ptr bs ∧
    1 ≤ bs.length ∧ bs.length < 2 ^ 31 ∧ (bs.length + 7) / 8 ≤ p.x.wx

/-- `loadArr j sp sl` is constant time. -/
def LoadCT (j sp sl : Nat) : Prop :=
  RelCT isa (Two (LPre j sp sl)) (seqs (loadArr j sp sl)) fun _ _ => True

/-- The public data of the setup: `n`'s workspace, `-n⁻¹`, the primes'
lengths and the pointers to `p`, `q` and `qInv`. -/
structure SetupPub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  pl : Nat
  ql : Nat
  pp : Addr
  qp : Addr
  ip : Addr

/-- `primesSetup_ok`'s hypotheses. -/
def SetupPre (p : SetupPub) (s : State) : Prop :=
  ∃ pb qb ib : List Byte, Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    offQ p.w p.pl + slot (wsWords p.ql) 8 + wsTab (wsWords p.ql) ≤ p.Z ∧
    word s.mem p.B (8 * sPlen) = BitVec.ofNat 64 p.pl ∧ word s.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql ∧
    word s.mem p.B (8 * sP) = p.pp ∧ word s.mem p.B (8 * sQ) = p.qp ∧ word s.mem p.B (8 * sQinv) = p.ip ∧
    Src s p.B p.Z p.pp pb ∧ Src s p.B p.Z p.qp qb ∧ Src s p.B p.Z p.ip ib ∧ pb.length = p.pl ∧
    qb.length = p.ql ∧ ib.length = p.pl ∧ 1 ≤ p.pl ∧ p.pl < 8 * p.w ∧ 1 ≤ p.ql ∧ p.ql < 8 * p.w

/-- `primesSetup` is constant time. -/
def SetupCT : Prop := RelCT isa (Two SetupPre) (seqs primesSetup) fun _ _ => True

/-- The public data of the checks: `n`'s workspace, `-n⁻¹`, `n` and the
primes' workspaces. -/
structure ChecksPub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  op : Nat
  oq : Nat
  wp : Nat
  wq : Nat

/-- `checks_ok`'s hypotheses. -/
def ChecksPre (p : ChecksPub) (s : State) : Prop :=
  ∃ (mp mq : BitVec 64) (P Q QI : Nat) (m0 : Bool), Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    slot p.w 8 ≤ p.op ∧ p.op + slot p.wp 8 + wsTab p.wp ≤ p.oq ∧ p.oq + slot p.wq 8 + wsTab p.wq ≤ p.Z ∧
    2 ≤ p.wp ∧ p.wp ≤ p.w ∧ 2 ≤ p.wq ∧ p.wq ≤ p.w ∧ word s.mem p.B (8 * sWsP) = off p.B p.op ∧
    word s.mem p.B (8 * sWsQ) = off p.B p.oq ∧ WsAt s.mem p.B p.op p.wp mp ∧ WsAt s.mem p.B p.oq p.wq mq ∧
    wv s.mem p.B (slot p.w Public.aN) p.w = p.N ∧ word s.mem p.B (8 * Public.sMask) = mask m0 ∧
    wv s.mem (off p.B p.op) (slot p.wp Public.aN) p.wp = P ∧
    wv s.mem (off p.B p.oq) (slot p.wq Public.aN) p.wq = Q ∧
    wv s.mem (off p.B p.op) (slot p.wp aChunk) p.wp = QI ∧ p.N % 2 = 1

/-- `checks` is constant time. -/
def ChecksCT : Prop := RelCT isa (Two ChecksPre) (seqs checks) fun _ _ => True

/-- The public data of the phases' parts: `n`'s workspace, `-n⁻¹`, `n`, the
prime's workspace (its base in slot `sl`). -/
structure UPub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  o : Nat
  wx : Nat

/-- `unitPhase_ok`'s hypotheses. -/
def UPre (sl : Nat) (p : UPub) (s : State) : Prop :=
  ∃ (mx : BitVec 64) (X : Nat), Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧ slot p.w 8 ≤ p.o ∧
    p.o + slot p.wx 8 + wsTab p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧ sl < 32 ∧ sl ≠ sD ∧ sl ≠ Public.sCnt ∧
    word s.mem p.B (8 * sl) = off p.B p.o ∧ WsAt s.mem p.B p.o p.wx mx ∧ NVals s p.B p.w p.minv p.N ∧
    p.N % 2 = 1 ∧ 1 < p.N ∧ XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1

/-- The phases' first part (`unitPhase_ok`) is constant time. -/
def UnitCT (M : Mont) (sl : Nat) : Prop :=
  RelCT isa (Two (UPre sl)) (seqs (gPow M.mm sl ++ [.block [ldh .x0 sl]] ++
    redc M.mm Public.aY ++ copyArr Public.aY aXc ++ [.block [leave]])) fun _ _ => True

/-- `powPhase_ok`'s hypotheses, for the exponent's pointer and length in
slots `sd` and `slen`. -/
def PwPre (sl sd slen : Nat) (p : BPub) (s : State) : Prop :=
  ∃ (minv mx : BitVec 64) (N X C : Nat) (eb : List Byte), Good s p.x.B p.x.Z p.x.w minv ∧ p.x.w < 2 ^ 28 ∧
    slot p.x.w 8 ≤ p.x.o ∧ p.x.o + slot p.x.wx 8 + wsTab p.x.wx ≤ p.x.Z ∧ 2 ≤ p.x.wx ∧ p.x.wx ≤ p.x.w ∧ sl < 32 ∧
    word s.mem p.x.B (8 * sl) = off p.x.B p.x.o ∧ WsAt s.mem p.x.B p.x.o p.x.wx mx ∧
    XVals s p.x.B p.x.o p.x.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧
    wv s.mem p.x.B (slot p.x.w Public.aY) p.x.w % N = C * 2 ^ (64 * p.x.wx * (nChunks p.x.w p.x.wx + 1)) % N ∧
    wv s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx < X ∧
    (X ∣ N → wv s.mem (off p.x.B p.x.o) (slot p.x.wx Public.aY) p.x.wx % X = 2 ^ (64 * p.x.wx) % X) ∧
    sd < 32 ∧ slen < 32 ∧ word s.mem p.x.B (8 * sd) = p.ptr ∧
    word s.mem p.x.B (8 * slen) = BitVec.ofNat 64 eb.length ∧ eb.length = p.len ∧ 1 ≤ eb.length ∧
    eb.length ≤ 1024 ∧ Src s p.x.B p.x.Z p.ptr eb

/-- The phases' exponentiation (`powPhase_ok`) is constant time. -/
def PowCT (M : Mont) (sl sd slen : Nat) : Prop :=
  RelCT isa (Two (PwPre sl sd slen)) (seqs ([.block [ldh .x0 sl]] ++ redc M.mm Public.aY ++
    expLoop M.mm sd slen)) fun _ _ => True

/-- The public data of a prime's phase: `n`'s workspace, `-n⁻¹`, `n`, the
prime's workspace and the exponent's pointer and length. -/
structure PhasePub where
  B : Addr
  Z : Nat
  w : Nat
  minv : BitVec 64
  N : Nat
  o : Nat
  wx : Nat
  ep : Addr
  len : Nat

/-- `qPhase_ok`'s hypotheses. -/
def QPre (p : PhasePub) (s : State) : Prop :=
  ∃ (mx : BitVec 64) (X C : Nat) (eb : List Byte), Good s p.B p.Z p.w p.minv ∧ 8 ≤ p.w ∧ p.w < 2 ^ 28 ∧
    slot p.w 8 ≤ p.o ∧ p.o + slot p.wx 8 + wsTab p.wx ≤ p.Z ∧ 2 ≤ p.wx ∧ p.wx ≤ p.w ∧
    word s.mem p.B (8 * sWsQ) = off p.B p.o ∧ WsAt s.mem p.B p.o p.wx mx ∧ NVals s p.B p.w p.minv p.N ∧
    p.N % 2 = 1 ∧ 1 < p.N ∧ wv s.mem p.B (slot p.w Public.aXm) p.w % p.N = C * 2 ^ (64 * p.w) % p.N ∧
    XVals s p.B p.o p.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧ word s.mem p.B (8 * sDq) = p.ep ∧
    word s.mem p.B (8 * sQlen) = BitVec.ofNat 64 eb.length ∧ eb.length = p.len ∧ 1 ≤ eb.length ∧
    eb.length ≤ 1024 ∧ Src s p.B p.Z p.ep eb

/-- `qPhase M.mm` is constant time. -/
def QPhaseCT (M : Mont) : Prop := RelCT isa (Two QPre) (seqs (qPhase M.mm)) fun _ _ => True

/-- The public data of `p`'s phase: also `q`'s workspace and `qInv`'s
pointer. -/
structure PPhasePub where
  ph : PhasePub
  oq : Nat
  wq : Nat
  qp : Addr

/-- `pPhase_ok`'s hypotheses. -/
def PPre (p : PPhasePub) (s : State) : Prop :=
  ∃ (mx mq : BitVec 64) (X C : Nat) (eb qib : List Byte) (c : Bool), Good s p.ph.B p.ph.Z p.ph.w p.ph.minv ∧
    8 ≤ p.ph.w ∧ p.ph.w < 2 ^ 28 ∧ slot p.ph.w 8 ≤ p.ph.o ∧
    p.ph.o + slot p.ph.wx 8 + wsTab p.ph.wx ≤ p.oq ∧ p.oq + slot p.wq 8 + wsTab p.wq ≤ p.ph.Z ∧
    2 ≤ p.ph.wx ∧ p.ph.wx ≤ p.ph.w ∧ 1 ≤ p.wq ∧ p.wq ≤ p.ph.w ∧
    word s.mem p.ph.B (8 * sWsP) = off p.ph.B p.ph.o ∧ WsAt s.mem p.ph.B p.ph.o p.ph.wx mx ∧
    word s.mem p.ph.B (8 * sWsQ) = off p.ph.B p.oq ∧ WsAt s.mem p.ph.B p.oq p.wq mq ∧
    NVals s p.ph.B p.ph.w p.ph.minv p.ph.N ∧ p.ph.N % 2 = 1 ∧ 1 < p.ph.N ∧
    wv s.mem p.ph.B (slot p.ph.w Public.aXm) p.ph.w % p.ph.N = C * 2 ^ (64 * p.ph.w) % p.ph.N ∧
    XVals s p.ph.B p.ph.o p.ph.wx mx X ∧ 1 < X ∧ X % 2 = 1 ∧
    word s.mem (off p.ph.B p.ph.o) (8 * sMaskX) = mask c ∧ (c = true → X ∣ p.ph.N) ∧
    word s.mem p.ph.B (8 * sDp) = p.ph.ep ∧ word s.mem p.ph.B (8 * sPlen) = BitVec.ofNat 64 eb.length ∧
    eb.length = p.ph.len ∧ 1 ≤ eb.length ∧ eb.length ≤ 1024 ∧ Src s p.ph.B p.ph.Z p.ph.ep eb ∧
    word s.mem p.ph.B (8 * sQinv) = p.qp ∧ qib.length = eb.length ∧ Src s p.ph.B p.ph.Z p.qp qib ∧
    (qib.length + 7) / 8 ≤ p.ph.wx ∧ (c = true → Spec.Rsa.os2ip qib < X)

/-- `pPhase M.mm` is constant time. -/
def PPhaseCT (M : Mont) : Prop := RelCT isa (Two PPre) (seqs (pPhase M.mm)) fun _ _ => True

end VG.Proof.Bignum.AArch64
