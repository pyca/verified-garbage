module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Run
public import VerifiedGarbage.Impl.Blowfish.Table
public import VerifiedGarbage.Impl.Blowfish.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-!
# Blowfish on RISC-V, key expansion: the initial schedule

`initSteps_run`: the 1042 words of the initial schedule's image, as
immediates, into the frame at `t0`; `table_byte`: its bytes are the image's.
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64

theorem initWord32_byte (i : Nat) {b : Nat} (hb : b < 4) :
    (initWord32 i).extractLsb' (8 * b) 8 = Impl.Blowfish.initByte (4 * i + b) := by
  simp only [initWord32, List.range, List.range.loop, List.foldl_cons, List.foldl_nil]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := omega) [hj, decide_eq_true, decide_eq_false, BitVec.getLsbD_of_ge]

theorem flatMap_range_succ {α : Type} (f : Nat → List α) (k : Nat) :
    (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- An aligned word's offset of an aligned base. -/
theorem al4 {p : Addr} (hp : p.toNat % 4 = 0) (d : Nat) (hd : 4 * d < 2 ^ 64) :
    (p + BitVec.ofNat 64 (4 * d)).toNat % 4 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * d) hd]
  have := p.isLt
  omega

theorem initStep_run (u : State) {S : Addr} {i : Nat} (hi : i < 1042)
    (h0 : u.gpr .t0 = S + BitVec.ofNat 64 (4 * i)) (hal : S.toNat % 4 = 0)
    (hw : InRegions u.wr (S + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (initStep i)) u fun t =>
      t.mem = u.mem.writeW (S + BitVec.ofNat 64 (4 * i)) (initWord32 i) ∧
      t.gpr .t0 = S + BitVec.ofNat 64 (4 * (i + 1)) ∧ Keep [.t4, .t0] u t := by
  have ha := al4 hal i (by omega)
  refine WP.mono (WP.keep [.t4, .t0] (Q := fun t =>
    t.mem = u.mem.writeW (S + BitVec.ofNat 64 (4 * i)) (initWord32 i) ∧
      t.gpr .t0 = S + BitVec.ofNat 64 (4 * (i + 1))) ?_ (by rfl) rfl)
    fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold initStep
  rw [WP.block_append_iff]
  refine WP.mono (ByteLoad.li32_ok (d := .t4) (initWord32 i)) fun v e => ?_
  subst e
  brun [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, h0, hw, ha, lo_sext]
  rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, Offset.add_add, show 4 * i + 4 = 4 * (i + 1) by omega]

/-- The first `k` words. -/
theorem initSteps_run {S : Addr} {t : State} (h0 : t.gpr .t0 = S) (hal : S.toNat % 4 = 0)
    (hW : ∀ i < 1042, InRegions t.wr (S + BitVec.ofNat 64 (4 * i)) 4) :
    ∀ k ≤ 1042, WP isa (.block ((List.range k).flatMap initStep)) t fun t' =>
      (∀ i < k, t'.mem.readW (S + BitVec.ofNat 64 (4 * i)) 32 = initWord32 i) ∧
      t'.gpr .t0 = S + BitVec.ofNat 64 (4 * k) ∧
      Frame [⟨S, 4168⟩] t.mem t'.mem ∧ Keep [.t4, .t0] t t'
  | 0, _ => WP.block_nil ⟨fun i hi => absurd hi (by omega), by rw [h0]; simp, Frame.refl _ _, Keep.refl _ _⟩
  | k + 1, hk => by
    rw [flatMap_range_succ, WP.block_append_iff]
    refine WP.mono (initSteps_run h0 hal hW k (by omega)) fun u ⟨d, p, f, kp⟩ => ?_
    refine WP.mono (initStep_run u (i := k) (by omega) p hal (by rw [kp.2.2]; exact hW k (by omega)))
      fun v ⟨m, pv, kv⟩ => ⟨fun i hi => ?_, pv, ?_, (kp.trans kv).mono (by decide)⟩
    · rw [m]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [Mem.readW_writeW_sep (Offset.sep S (by omega) (by omega) (by omega)) (by decide)]
        exact d i hi
      · exact Mem.readW_writeW_self32 _ _ _
    · rw [m]
      exact f.writeW (List.mem_singleton_self _) _ (Offset.contains_base S (by omega) (by omega))

/-- The table's bytes are the initial schedule's. -/
theorem table_byte {m : Mem} {T : Addr}
    (held : ∀ i < 1042, m.readW (T + BitVec.ofNat 64 (4 * i)) 32 = initWord32 i)
    {o : Nat} (ho : o < 4168) : m (T + BitVec.ofNat 64 o) = Impl.Blowfish.initByte o := by
  have e := initWord32_byte (o / 4) (b := o % 4) (Nat.mod_lt _ (by decide))
  rw [show 4 * (o / 4) + o % 4 = o by omega] at e
  rw [← e, ← held _ (by omega), ← Mem.readW_byte _ _ (Nat.mod_lt _ (by decide)), Offset.add_add,
    show 4 * (o / 4) + o % 4 = o by omega]

end VG.Proof.Blowfish.RISCV64
