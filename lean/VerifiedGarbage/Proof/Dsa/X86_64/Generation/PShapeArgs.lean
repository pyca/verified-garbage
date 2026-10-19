module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PShape
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
public import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-! # Native arguments for the full-width candidate shaper -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

theorem pShapeArgs_ok {s : State} {F S op hp : Addr} {len count plen : Nat}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep s.mem F S V W)
    (hop : W 0 = op) (hhp : W 4 = hp) (hn : (count + 1) * len < 2 ^ 31) (hl : plen ≤ 1024) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.pShapeArgs len count plen)) s fun t =>
      t.gpr .rdi = op ∧ t.gpr .rsi = off hp ((count + 1) * len - plen) ∧
      t.gpr .rcx = BitVec.ofNat 64 plen ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * plen) ∧
      t.mem = s.mem ∧ Keep [.rdi, .rsi, .rcx, .rdx] s t := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rcx, .rdx] (Q := fun t =>
      t.gpr .rdi = op ∧ t.gpr .rsi = off hp ((count + 1) * len - plen) ∧
      t.gpr .rcx = BitVec.ofNat 64 plen ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * plen) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨a, b, c, d, e⟩, hk⟩ => ⟨a, b, c, d, e, hk⟩
  have hld0 : InRegions (s.rd ++ s.wr) F 8 := by simpa [off] using L.ld (d := 0) (by decide)
  have hv0 : s.mem.readW F 64 = op := by
    simpa [off] using R.slot (d := 0) (k := 0) rfl (by decide) hop
  xrun [Impl.Dsa.X86_64.Generation.pShapeArgs, ea_sp, L.rsp,
    hld0, hv0, L.ld (d := 32) (by decide), R.slot (d := 32) (k := 4) rfl (by decide) hhp,
    sx_ofNat (show (count + 1) * len - plen < 2 ^ 31 by omega)]
  change BitVec.setWidth 64 (BitVec.ofNat 32 plen) = BitVec.ofNat 64 plen ∧
    BitVec.setWidth 64 (BitVec.ofNat 32 (8 * plen)) = BitVec.ofNat 64 (8 * plen)
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] <;>
    simp only [Nat.mod_eq_of_lt (by omega : plen < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : 8 * plen < 2 ^ 32)]

end VG.Proof.Dsa.X86_64.Generation
