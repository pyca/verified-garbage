module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PHash
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Prepare the wrapped seed, offset and digest-copy arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64

theorem seedInputArgs_ok {s : State} {F S rp op : Addr} {offset j : Nat}
    (hj : j < 4096) (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (hrp : W 1 = rp) (hop : W 3 = op)
    (hoff : W 2 = BitVec.ofNat 64 offset) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.seedInputArgs j)) s fun t =>
      t.gpr .x1 = rp ∧ t.gpr .x2 = op ∧ t.gpr .x0 = BitVec.ofNat 64 (offset + j) ∧
      t.mem = s.mem ∧ Keep [.x1, .x2, .x0] s t := by
  refine WP.mono (WP.keep [.x1, .x2, .x0] (Q := fun t =>
    t.gpr .x1 = rp ∧ t.gpr .x2 = op ∧ t.gpr .x0 = BitVec.ofNat 64 (offset + j) ∧ t.mem = s.mem)
    ?_ rfl rfl rfl) fun _ ⟨⟨a, b, c, d⟩, hk⟩ => ⟨a, b, c, d, hk⟩
  have h1 : s.mem.readW (F + BitVec.ofNat 64 8) 64 = rp := (R.fr 1 (by decide)).trans hrp
  have h3 : s.mem.readW (F + BitVec.ofNat 64 24) 64 = op := (R.fr 3 (by decide)).trans hop
  have h2 : s.mem.readW (F + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 offset :=
    (R.fr 2 (by decide)).trans hoff
  unfold Impl.Dsa.AArch64.Generation.seedInputArgs
  brun [exec_ldrSp (off := 8) (by decide), exec_ldrSp (off := 24) (by decide),
    exec_ldrSp (off := 16) (by decide), L.sp, L.ld (d := 8) (n := 8) (by decide),
    L.ld (d := 24) (n := 8) (by decide), L.ld (d := 16) (n := 8) (by decide),
    h1, h2, h3, exec_addImm_x' hj, BitVec.ofNat_add]

theorem hashCopyArgs_ok {s : State} {F S op : Addr} {len count j : Nat}
    (hlen : len = 20 ∨ len = 32) (hcount : count ≤ 11)
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep s.mem F S V W) (hop : W 4 = op) :
    WP isa (.block (Impl.Dsa.AArch64.Generation.hashCopyArgs len count j)) s fun t =>
      t.gpr .x12 = off S oDig ∧ t.gpr .x2 = off op ((count - j) * len) ∧
      t.gpr .x9 = BitVec.ofNat 64 len ∧ t.mem = s.mem ∧ Keep [.x12, .x2, .x9] s t := by
  have hoff : (count - j) * len < 4096 := by rcases hlen with rfl | rfl <;> omega
  have h4 : s.mem.readW (F + BitVec.ofNat 64 32) 64 = op := (R.fr 4 (by decide)).trans hop
  have hs : s.mem.readW (F + BitVec.ofNat 64 sScr) 64 = S := L.slot
  refine WP.mono (WP.keep [.x12, .x2, .x9] (Q := fun t =>
    t.gpr .x12 = off S oDig ∧ t.gpr .x2 = off op ((count - j) * len) ∧
    t.gpr .x9 = BitVec.ofNat 64 len ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun _ ⟨⟨a, b, c, d⟩, hk⟩ => ⟨a, b, c, d, hk⟩
  unfold Impl.Dsa.AArch64.Generation.hashCopyArgs
  brun [exec_ldrSp (off := sScr) (by decide), exec_ldrSp (off := 32) (by decide),
    L.sp, L.ld (d := sScr) (n := 8) (by decide), L.ld (d := 32) (n := 8) (by decide),
    hs, h4, exec_addImm_x' hoff, off]
  rcases hlen with rfl | rfl <;> rfl

end VG.Proof.Dsa.AArch64.Generation
