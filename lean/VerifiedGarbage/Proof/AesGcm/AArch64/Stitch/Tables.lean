module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tbl
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Front
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay

/-!
# AES-GCM on AArch64, interleaved: the code that writes the table of keys

Untrusted: everything here is checked by Lean. Both ways of writing the
table of keys of `H` at `W + 512` meet `TblSpec`: `powTbl`, from `H'` kept at
`W + hO` (`KeyAt`), computing the powers as `vg_ghash_aes` does, for any `mul`
of prepared powers that is one (`PrepPow`); and `pwTbl k`, from the powers in
the buffer at `[sp + k]` (`Spec.Gcm.Powers8Repr`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (gpr_write gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly pp PrepPow)
open VG.Proof.Gcm.AArch64.Stitch (TblOk)
open VG.Spec.Gcm (Block)

/-- What the code `tb` that writes the table of keys of `H` at `W + 512` does. -/
def TblPost (W : Addr) (H : Block) (u t : State) : Prop :=
  TblOk t.mem W H ∧ Frame [tblR W] u.mem t.mem ∧ (∀ r, r ≠ .x5 → t.gpr r = u.gpr r) ∧
    t.sp = u.sp ∧ t.rd = u.rd ∧ t.wr = u.wr

theorem tbl_post {W : Addr} {H : Block} {u s t : State} (hW : s.gpr .x19 = W)
    (hT : TS s H 8 4 t) (g : ∀ r, r ≠ .x5 → s.gpr r = u.gpr r) (hm : s.mem = u.mem) (hsp : s.sp = u.sp)
    (hrd : s.rd = u.rd) (hwr : s.wr = u.wr) : TblPost W H u t := by
  subst hW
  exact ⟨hT.tblOk, hm ▸ hT.frame, fun r hr => by rw [hT.gpr, g r hr], by rw [hT.sp, hsp], by rw [hT.rd, hrd],
    by rw [hT.wr, hwr]⟩

/-- `powTbl`: `H'` reloaded, its powers computed, and the table written. -/
theorem powTbl_ok (hP : PrepPow) {Ctx St W SP : Addr} {H : Block} {u : State} (he : Env Ctx St W SP u)
    (key : Fast.KeyAt H u.mem W) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.powTbl) u (TblPost W H u) := by
  unfold Impl.AesGcm.AArch64.Stitch.powTbl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Fast.reload_ok (H := H) (by rw [he.x19]; exact he.perm.wR (by decide))
    (by rw [he.x19]; exact he.perm.wR (by decide)) (by rw [he.x19]) (by rw [he.x19]; exact key.2) key.1)
    fun s₁ ⟨hk₁, g₁, _, m₁, rd₁, wr₁, sp₁⟩ => ?_
  have hI₁ : PInv H 1 s₁ := ⟨hk₁.c, fun k h1 h2 => by
      obtain rfl : k = 1 := by omega
      rw [hk₁.t, hP.key], fun k h1 h2 => by
      obtain rfl : k = 1 := by omega
      rw [hk₁.sw, hk₁.t, hP.key]⟩
  refine WP.mono (powers_ok hP hI₁) fun s₂ ⟨hI₂, o₂⟩ => ?_
  have hw : InRegions s₂.wr (s₂.gpr .x19 + BitVec.ofNat 64 512) 192 := by
    rw [o₂.wr, o₂.gpr, wr₁, g₁ _ (by decide), he.x19]; exact he.perm.wW (by decide)
  exact WP.mono (tbl_ok hI₂.pt hw) fun t hT => tbl_post (by rw [o₂.gpr, g₁ _ (by decide), he.x19]) hT
    (fun r hr => by rw [o₂.gpr, g₁ r hr]) (by rw [o₂.mem, m₁]) (by rw [o₂.sp, sp₁]) (by rw [o₂.rd, rd₁])
    (by rw [o₂.wr, wr₁])

/-- `pwTbl k`: the powers loaded from the buffer at `[sp + k]`, and the table written. -/
theorem pwTbl_ok {Ctx St W SP : Addr} {H : Block} {pw : Addr} {k : Nat} (hk : k % 8 = 0 ∧ k < 32768)
    {u : State} (he : Env Ctx St W SP u) (hpw : u.mem.readW (u.sp + BitVec.ofNat 64 k) 64 = pw)
    (hsl : InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 k) 8)
    (hin : Covers [⟨pw, 128⟩] (u.rd ++ u.wr))
    (hrep : Spec.Gcm.Powers8Repr u.mem pw H) :
    WP isa (.block (Impl.AesGcm.AArch64.Stitch.pwTbl k)) u (TblPost W H u) := by
  unfold Impl.AesGcm.AArch64.Stitch.pwTbl
  rw [WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, x5₁, g₁, sp₁, m₁, rd₁, wr₁⟩ := ldrSp_ok (t := .x5) hk hpw hsl
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  refine WP.mono (loadPws_ok (u := s₁) (H := H) (by rw [m₁, x5₁]; exact hrep) (fun j h1 h8 => by
      rw [rd₁, wr₁, x5₁]
      exact in_off hin (by unfold Impl.Gcm.AArch64.Pmull.pwOff; split <;> omega) (by omega)) 8 (Nat.le_refl _))
    fun s₂ ⟨hI₂, g₂, m₂, rd₂, wr₂, sp₂⟩ => ?_
  have hw : InRegions s₂.wr (s₂.gpr .x19 + BitVec.ofNat 64 512) 192 := by
    rw [wr₂, g₂, wr₁, g₁ _ (by decide), he.x19]; exact he.perm.wW (by decide)
  exact WP.mono (tbl_ok hI₂ hw) fun t hT => tbl_post (by rw [g₂, g₁ _ (by decide), he.x19]) hT
    (fun r hr => by rw [g₂, g₁ r hr]) (by rw [m₂, m₁]) (by rw [sp₂, sp₁]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])

end VG.Proof.AesGcm.AArch64.Stitch
