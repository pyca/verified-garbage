module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PShape
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Dsa.AArch64.Run

/-! Prepare the hash suffix and full-width candidate buffer. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

theorem pShapeArgs_ok {s : State} {F S op hp : Addr} {len count plen : Nat}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep s.mem F S V W)
    (hop : W 0 = op) (hhp : W 4 = hp) (hn : (count + 1) * len < 4096) (hl : plen ≤ 1024) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.pShapeArgs len count plen)) s fun t =>
      t.gpr .x2 = op ∧ t.gpr .x12 = off hp ((count + 1) * len - plen) ∧
      t.gpr .x9 = BitVec.ofNat 64 plen ∧ t.mem = s.mem ∧ Keep [.x2, .x12, .x9] s t := by
  have h0 : s.mem.readW F 64 = op := by
    have h := (R.fr 0 (by decide)).trans hop
    change s.mem.readW (F + 0#64) 64 = op at h
    simpa only [BitVec.add_zero] using h
  have h4 : s.mem.readW (F + BitVec.ofNat 64 32) 64 = hp := (R.fr 4 (by decide)).trans hhp
  have hperm : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 0) 8 := by
    rw [L.sp]
    exact L.ld (d := 0) (n := 8) (by decide)
  have hload := exec_ldrSp (t := .x2) (off := 0) (by decide) hperm
  have hoff : (count + 1) * len - plen < 4096 := by omega
  refine WP.mono (WP.keep [.x2, .x12, .x9] (Q := fun t =>
    t.gpr .x2 = op ∧ t.gpr .x12 = off hp ((count + 1) * len - plen) ∧
    t.gpr .x9 = BitVec.ofNat 64 plen ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨⟨a, b, c, d⟩, hk⟩ => ⟨a, b, c, d, hk⟩
  unfold Impl.Dsa.AArch64.Generation.pShapeArgs
  brun [hload, exec_ldrSp (off := 32) (by decide), L.sp,
    L.ld (d := 32) (n := 8) (by decide), h0, h4, exec_addImm_x' hoff, off]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : plen < 2 ^ 16), Nat.mod_eq_of_lt (by omega : plen < 2 ^ 64)]

end VG.Proof.Dsa.AArch64.Generation
