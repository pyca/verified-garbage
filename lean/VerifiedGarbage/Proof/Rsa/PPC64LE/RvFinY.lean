module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFF
import VerifiedGarbage.Proof.Rsa.PPC64LE.InvParts
import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Rsa.RecoverFusedBounds
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.RvSlots

/-!
# `vg_rsa_recover_primes` on PPC64LE: `y` out of Montgomery form

`finY_ok`: the mask `:= ok`, and `y` (the last candidate's) in `[mY]`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys VG.Proof.Rsa
open VG.Impl.Rsa.PPC64LE.Recover (finY mmul mBase mY mXm aOne nArr sOk sMask iY iXm)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num slot)

theorem yV_lt {s0 : State} (hn : NOk s0) : yV s0 < nV s0 := by
  have hn0 : 0 < nV s0 := by have := hn.big; omega
  exact Fused.root_getD_lt hn0 (Fused.bounded_eval (by have := hn.big; omega))

/-- `finY`. -/
theorem finY_ok {s0 u : State} (hn : NOk s0) (h : CP s0 (jL s0) u) :
    WP isa finY u fun t => FF s0 t ∧ num t.mem (rvB s0) (ww (kK s0)) mY = yV s0 := by
  have c := h.cf
  have hz : 160 ≤ rvZ s0 := c.ws.hdr_le
  have hn0 : 0 < nV s0 := by have := hn.big; omega
  have hn1 : 1 < nV s0 := by have := hn.big; omega
  have fit : ∀ j < nArr, arr (ww (kK s0)) j + S (ww (kK s0)) ≤ 2 ^ 64 := fun _ hj => c.ws.fit64 hj
  unfold finY
  rw [List.cons_append, List.cons_append, List.nil_append, wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (WP.keep [.r0] (Q := fun x => x.mem = u.mem.writeW (off (rvB s0) sMask)
    ((BitVec.ofNat 64 (b2n (okB s0))).setWidth 32)) ?_ (by decide)) fun u1 ⟨m1, k1⟩ => ?_
  · prun [c.ws.r31, c.ws.scr.ld (show sOk + 4 ≤ rvZ s0 by simp only [sOk]; omega),
      c.ws.scr.st (show sMask + 4 ≤ rvZ s0 by simp only [sMask, VG.Impl.Rsa.PPC64LE.CrtValues.sMask]; omega),
      exec_load_w (show Reg.r31 ≠ .r0 by decide) (show sOk < 2 ^ 15 by decide),
      exec_store_w (show Reg.r31 ≠ .r0 by decide) (show sMask < 2 ^ 15 by decide), ld_slot h.ok]
  have kk1 : KeyWorkspace.Keep (rvB s0) (ww (kK s0)) [] [sMask] u.mem u1.mem := by
    rw [m1]; exact keep_slot _ _ (by simp) (by decide)
  have ws1 := c.ws.of_keep k1
  have M1 : slot u1.mem (rvB s0) sMask = b2n (okB s0) := by rw [m1, slot_write_self, b64_w32, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := b2n_le (okB s0); omega)]
  -- `X := 1`.
  rw [wp_seqs_cons (by simp [mmul])]
  refine WP.mono (copy_ok ws1 (o := mXm) (a := aOne) (by decide) (by decide) (by decide) (by decide))
    fun u2 ⟨ws2, kk2, v2, k2, _⟩ => ?_
  have one2 : num u2.mem (rvB s0) (ww (kK s0)) mXm = 1 := by
    rw [v2, kk1.num (by simp) (by simp [sMask, VG.Impl.Rsa.PPC64LE.CrtValues.sMask, KeyWorkspace.hdr])
      (fit aOne (by decide))]
    exact c.vOne
  have c1 := c.of_keep kk1 (by simp) (by decide) k1 ws1
  have c2 := c1.of_keep kk2 (by decide) (by simp) k2 ws2
  have Y2 : num u2.mem (rvB s0) (ww (kK s0)) mY = yV s0 * RR s0 % nV s0 := by
    rw [kk2.num (by decide) (by simp) (fit mY (by decide)),
      kk1.num (by simp) (by simp [sMask, VG.Impl.Rsa.PPC64LE.CrtValues.sMask, KeyWorkspace.hdr]) (fit mY (by decide))]
    exact h.vY
  have Yl : num u2.mem (rvB s0) (ww (kK s0)) mY < nV s0 := by rw [Y2]; exact Nat.mod_lt _ hn0
  refine WP.mono (mmul_ok c2.base c2.ws (o := iY) (a := iY) (b := iXm) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) c2.r12 c2.inv
    (by rw [c2.vMN]; change lowV u2.mem s0 mXm < _; rw [low_of_lt (by rw [one2]; exact hn1), one2]; exact hn1))
    fun t ⟨_, ws3, kk3, lt3, eq3, k3⟩ => ?_
  have c3 := c2.of_keep kk3 (by decide) (by simp) k3 ws3
  change num t.mem (rvB s0) (ww (kK s0)) mY < lowV u2.mem s0 mBase at lt3
  change num t.mem (rvB s0) (ww (kK s0)) mY * RR s0 % lowV u2.mem s0 mBase =
    lowV u2.mem s0 mY * lowV u2.mem s0 mXm % lowV u2.mem s0 mBase at eq3
  rw [c2.vMN, low_of_lt Yl, low_of_lt (by rw [one2]; exact hn1), one2, Y2, Nat.mul_one, Nat.mod_mod] at eq3
  rw [c2.vMN] at lt3
  have := VG.Proof.Bignum.mont_cancel hn.coprime eq3
  rw [Nat.mod_eq_of_lt lt3, Nat.mod_eq_of_lt (yV_lt hn)] at this
  refine ⟨⟨c3.base, c3.ws, c3.r21, c3.r23, c3.r25, c3.vN, c3.vOne, c3.zZ, ?_⟩, this⟩
  rw [kk3.slot (e := sMask) (by decide) (by simp), kk2.slot (e := sMask) (by decide) (by simp)]
  exact M1

end VG.Proof.Rsa.PPC64LE.Recover
