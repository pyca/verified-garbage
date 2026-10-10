import VerifiedGarbage.Impl.Ed25519.Arm.PointTableIO
import VerifiedGarbage.Proof.Ed25519.Arm.PointTableLoad
import VerifiedGarbage.Proof.Ed25519.Arm.PointPowers

/-!
# Ed25519 on ARMv7: addresses past 4096, and `lr` saved

`scratchAddr_ok`: a pointer to an offset of the working space that a load's
immediate cannot reach. The functions that call `vg_gf25519_r16_mul`, which
overwrites `lr`, save it at `LRS` on entry (`saveLr_ok`) and reload it before
returning (`loadLr_ok`).
-/

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scratchAddr_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (o : Nat) (ho : o < 8192) :
    WP isa (.block (scratchAddr o)) s fun t => Rest [.r12] s t ∧ t.mem = s.mem ∧
      t.gpr .r12 = b + BitVec.ofNat 32 o := by
  refine wp_movw fun u hu => wp_dp (op2_reg _ _) fun t ht => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (ht.rest (by decide)), by rw [ht.mem, hu.mem], ?_⟩
  rw [ht.gpr]
  change u.gpr .r0 + u.gpr .r12 = _
  rw [hu.other _ (by decide), hc.r0, hu.gpr]
  refine congrArg (b + ·) (BitVec.eq_of_toNat_eq ?_)
  rw [movw_nat (by omega), toNat_imm (by omega)]

/-- `lr` stored at `LRS`. -/
theorem saveLr_ok {b : BitVec 32} {s : State} (hc : Ctx b s) :
    WP isa (.block (scratchAddr LRS ++ ([.str .lr .r12 0] : List Instr))) s fun t => Rest [.r12] s t ∧
      t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 LRS) (s.gpr .lr) := by
  refine WP.append (scratchAddr_ok hc LRS (by decide)) fun u ⟨ur, um, up⟩ => ?_
  refine wp_str (a := State.addr b + BitVec.ofNat 64 LRS) (by decide)
    (by rw [up]; exact (congrArg State.addr (BitVec.add_zero _)).trans (hc.ptr_addr (by decide)))
    (by rw [ur.wr]; exact in_base hc.wr (by decide) (by decide)) fun t ht => WP.block_nil ⟨ur.trans (ht.rest _), ?_⟩
  rw [ht.mem, um, ur.gpr _ (by decide)]

/-- `lr` reloaded from `LRS`. -/
theorem loadLr_ok {b : BitVec 32} {s : State} (hc : Ctx b s) :
    WP isa (.block (scratchAddr LRS ++ ([.ldr .lr .r12 0] : List Instr))) s fun t => Rest [.r12, .lr] s t ∧
      t.mem = s.mem ∧ t.gpr .lr = s.mem.readW (State.addr b + BitVec.ofNat 64 LRS) 32 := by
  refine WP.append (scratchAddr_ok hc LRS (by decide)) fun u ⟨ur, um, up⟩ => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 LRS) (by decide)
    (by rw [up]; exact (congrArg State.addr (BitVec.add_zero _)).trans (hc.ptr_addr (by decide)))
    (by rw [ur.rd, ur.wr]; exact in_base (List.mem_append_right _ hc.wr) (by decide) (by decide))
    fun t ht => WP.block_nil ⟨(ur.mono (by decide)).trans (ht.rest (by decide)), ht.mem.trans um, ?_⟩
  rw [ht.gpr, um]

end VG.Proof.Ed25519.Arm
