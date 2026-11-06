module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Body
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.CT
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Body
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.CT
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Front
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Front
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key` on PPC64LE: constant time

The public data `GD` is `vg_ffdh_derive_public`'s (`Derive.DD`) for x's and
`y`'s buffers, the bound and whether x is within it, and `rand`'s address.
x's mask runs without a branch (`KM1`, `KM2`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Ffdh.PPC64LE.Domain VG.Proof.Ffdh.PPC64LE.Derive
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

/-- The exchange's data of a run: the domain and g, x's and `y`'s buffers. -/
def gxOf (s : State) : XD := ⟨gcOf s, s.gpr .r5, s.gpr .r3, (s.gpr .r9).toNat⟩

/-- The public data of a run. -/
structure GD where
  d : DD
  R : Addr

/-! ## The predicates -/

/-! ## Pins -/

/-! ## The front and p's check -/

/-! ## x's cut -/

/-! ## After x's cut -/

/-- After `vg_ffdh_derive_public`'s body: the registers and the header's word
of x's mask, and the status. -/
def K6 (g : GD) (s : State) : Prop :=
  (s.gpr .r23 = g.d.x.c.S ∧ s.gpr .r28 = BitVec.ofNat 64 g.d.x.c.k) ∧
    s.mem.readW (off g.d.x.c.S 64) 64 = off g.d.x.X 0 ∧ InRegions (s.rd ++ s.wr) (off g.d.x.c.S 64) 8 ∧
    Scr s g.d.x.X g.d.x.c.k ∧ (1 ≤ g.d.x.c.k ∧ g.d.x.c.k < 2 ^ 32) ∧
    ∃ st, s.gpr .r3 = BitVec.ofNat 64 st ∧ 1 ≤ st ∧ st < 4

/-- Before x's masked loop. -/
def K7 (g : GD) (s : State) : Prop :=
  (s.gpr .r25 = off g.d.x.X 0 ∧ s.gpr .r6 = BitVec.ofNat 64 g.d.x.c.k) ∧ s.gpr .r23 = g.d.x.c.S ∧
    Scr s g.d.x.X g.d.x.c.k ∧ (1 ≤ g.d.x.c.k ∧ g.d.x.c.k < 2 ^ 32) ∧ ∃ c, s.gpr .r17 = mask c

theorem pins_K6 : Pins K6 [.r23, .r28] := by
  intro g s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.1.1, h₂.1.1]
  · rw [h₁.1.2, h₂.1.2]

theorem pins_K7 : Pins K7 [.r25, .r6] := by
  intro g s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.1.1, h₂.1.1]
  · rw [h₁.1.2, h₂.1.2]

theorem KM1 {g : GD} {s : State} (h : K6 g s) :
    WP isa (.block (statusMask ++ ([.load .d .r25 .r23 64, .addi .r6 .r28 0] : List Instr))) s (K7 g) := by
  obtain ⟨⟨h23, h28⟩, hX, hrd, hx, hk, st, h3, hst1, hst⟩ := h
  refine WP.mono (WP.keep [.r0, .r6, .r12, .r17, .r25] (Q := fun t => t.gpr .r25 = off g.d.x.X 0 ∧
      t.gpr .r17 = mask (decide (st = 1)) ∧ t.gpr .r6 = BitVec.ofNat 64 g.d.x.c.k ∧ t.mem = s.mem) (by
    unfold statusMask
    prun [h3, h23, h28, hrd, hX, BitVec.add_zero, status_mask st hst hst1]) (by decide))
    fun t ⟨⟨a25, a17, a6, _⟩, k⟩ => ⟨⟨a25, a6⟩, (k.gpr .r23 (by decide)).trans h23, hx.congr k.wr, hk, _, a17⟩

theorem KM2 {g : GD} {s : State} (h : K7 g s) :
    WP isa (countLoop .r6 [.lbz .r16 .r25 0, .logic .and .r16 .r16 .r17, .stb .r16 .r25 0, .addi .r25 .r25 1]) s
      (fun t => CF g.d.x.c t) := by
  obtain ⟨⟨h25, h6⟩, h23, hx, hk, c, h17⟩ := h
  exact WP.mono (masked_ok hk.1 hk.2 hx h25 h17 h6) fun t ⟨_, kt⟩ => (kt.gpr .r23 (by decide)).trans h23

/-! ## Constant time -/

end VG.Proof.Ffdh.PPC64LE.GenerateKey
