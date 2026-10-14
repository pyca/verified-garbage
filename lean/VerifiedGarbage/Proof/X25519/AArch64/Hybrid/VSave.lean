module

public import VerifiedGarbage.Proof.X25519.AArch64.Hybrid.Step
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# X25519 on AArch64: the hybrid ladder's setup and teardown

Untrusted: everything here is checked by Lean. The products use `v8`–`v15`,
whose low halves are callee-saved, so the function saves them at `VSAVE`
(`vsave_ok`) and restores them last (`vrestore_ok`); before the ladder it
writes the products' constants at `CONST` (`consts_ok`).
-/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Hybrid

open VG VG.AArch64
open VG.Impl.X25519.AArch64.Hybrid (VSAVE vsave vrestore consts)
open VG.Impl.X25519.AArch64.Neon (V ldq stq CONST M26 M25 C19)
open VG.Proof.Ed25519.AArch64 (Outside ofs off word Scr store_sc)
open VG.Proof.Curve448.AArch64.Neon (setMem setMem_mem)

theorem outside_read16 {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 16 ≤ o ∨ o + n ≤ d) (hd' : d + 16 ≤ 4096) :
    m'.read (off base d) 16 = m.read (off base d) 16 :=
  (Mem.read_congr fun i hi => (h _ (by rw [VG.Proof.Ed25519.AArch64.ofs_off base (by omega)]; omega)).symm).symm

theorem read16_write (m : Mem) (p : Addr) (v : BitVec 128) : (m.write p 16 v).read p 16 = v := by
  have := Mem.readW_writeW_self m p 16 v (by decide)
  simpa [Mem.readW, Mem.writeW] using this

/-- The low halves of `v8`–`v15` of `v`, saved in the working space. -/
def SavedV (base : Addr) (v : VReg → BitVec 128) (m : Mem) : Prop :=
  ∀ k < 8, (m.read (off base (VSAVE + 16 * k)) 16).extractLsb' 0 64 = (v (V (8 + k))).extractLsb' 0 64

theorem SavedV.outside {base : Addr} {v : VReg → BitVec 128} {m m' : Mem} (h : SavedV base v m)
    {o n : Nat} (ho : Outside base o n m m') (hx : o + n ≤ VSAVE ∨ VSAVE + 128 ≤ o) : SavedV base v m' := by
  intro k hk
  have hV : VSAVE = 1152 := rfl
  rw [outside_read16 ho (by omega) (by omega)]
  exact h k hk

theorem vsave_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block vsave) s fun t =>
      SavedV base s.v t.mem ∧ Outside base VSAVE 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.v = s.v ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hV : VSAVE = 1152 := rfl
  have e : vsave = (List.range 8).flatMap fun k => [stq (8 + k) (VSAVE + 16 * k)] := by
    simp only [vsave]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, t.mem.read (off base (VSAVE + 16 * k)) 16 = s.v (V (8 + k))) ∧
    Outside base VSAVE 128 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tO, tg, tvv, tr, tw, tsp⟩ => ?_) 8
    (by decide) s ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl, rfl, rfl, rfl⟩)
    fun t ⟨tv, tO, tg, tvv, tr, tw, tsp⟩ => ⟨fun k hk => by rw [tv k hk], tO, tg, tvv, tr, tw, tsp⟩
  have ts : Scratch t base := scratch_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_stq ts (8 + n) (d := VSAVE + 16 * n) (by omega) (by omega),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, tO.trans ((st_outside _ _ _ (by omega)).mono (by omega) (by omega)),
      tg, tvv, tr, tw, tsp⟩⟩
  simp only [setMem_mem]
  by_cases h : k = n
  · subst h; rw [read16_write, tvv]
  · rw [outside_read16 (st_outside t.mem base (t.v (V (8 + n))) (d := VSAVE + 16 * n) (by omega)) (by omega)
      (by omega)]
    exact tv k (by omega)

theorem vrestore_ok {s : State} {base : Addr} (hs : Scratch s base) {v : VReg → BitVec 128}
    (hsv : SavedV base v s.mem) :
    WP isa (.block vrestore) s fun t =>
      (∀ k < 8, (t.v (V (8 + k))).extractLsb' 0 64 = (v (V (8 + k))).extractLsb' 0 64) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hV : VSAVE = 1152 := rfl
  have e : vrestore = (List.range 8).flatMap fun k => [ldq (8 + k) (VSAVE + 16 * k)] := by
    simp only [vrestore]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, (t.v (V (8 + k))).extractLsb' 0 64 = (v (V (8 + k))).extractLsb' 0 64) ∧ t.mem = s.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tg, tr, tw, tsp⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl, rfl⟩
  have ts : Scratch t base := scratch_of hs tg tw
  refine WP.block_cons_iff.mpr ⟨_, exec_ldq ts (8 + n) (d := VSAVE + 16 * n) (by omega) (by omega),
    WP.block_nil_iff.mpr ⟨fun k hk => ?_, by rw [RegUpd.mem_setV, tm], by rw [RegUpd.gpr_setV, tg],
      by rw [RegUpd.rd_setV, tr], by rw [RegUpd.wr_setV, tw], by rw [RegUpd.sp_setV, tsp]⟩⟩
  by_cases h : k = n
  · subst h; rw [RegUpd.v_setV_self, tm]; exact hsv k hn
  · rw [RegUpd.v_setV_of_ne _ _ (V_ne _ (by omega) _ (by omega) (by omega))]
    exact tv k (by omega)

/-! ## The products' constants -/

theorem readW_writeW_inside (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) {k n : Nat}
    (h : 8 * (k + n) ≤ w) (hw : w < 2 ^ 64) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 k) (8 * n) = v.extractLsb' (8 * k) (8 * n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ _ _ (by omega)]
  simp only [Mem.writeW, Mem.write]
  rw [show a + BitVec.ofNat 64 k + BitVec.ofNat 64 (i / 8) - a = BitVec.ofNat 64 (k + i / 8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show k + i / 8 < w / 8 by omega, ite_true, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_setWidth]
  rw [decide_eq_true (by omega), decide_eq_true (by omega), Bool.true_and, Bool.true_and]
  exact congrArg _ (by omega)

/-- Two stores of the same word, after it is built by `movz` and `movk`. -/
theorem quad_ok {s : State} {base : Addr} (hs : Scratch s base) (a b : BitVec 16) {hw : Nat}
    (hh : 16 * hw < 64) {c : BitVec 64}
    (hc : (a.setWidth 64 &&& ~~~((0xFFFF : BitVec 64) <<< (16 * hw))) ||| (b.setWidth 64 <<< (16 * hw)) = c)
    {d : Nat} (ha : d % 8 = 0) (hd : d + 16 ≤ 4096) :
    WP isa (.block [.movz .x .x2 a 0, .movk .x .x2 b hw, VG.Impl.Ed25519.AArch64.st .x2 d,
      VG.Impl.Ed25519.AArch64.st .x2 (d + 8)]) s fun t =>
      t.mem = (s.mem.writeW (off base d) c).writeW (off base (d + 8)) c ∧
      (∀ r, r ≠ .x2 → t.gpr r = s.gpr r) ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hW : VG.Proof.Ed25519.AArch64.workSize false = 4096 := rfl
  have e1 : isa.exec (.movz .x .x2 a 0) s = some (s.write .x .x2 (a.setWidth 64)) := by
    simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true,
      BitVec.shiftLeft_zero]
  have s1 : Scratch (s.write .x .x2 (a.setWidth 64)) base := hs.write (by decide) _
  have e2 : isa.exec (.movk .x .x2 b hw) (s.write .x .x2 (a.setWidth 64)) =
      some ((s.write .x .x2 (a.setWidth 64)).write .x .x2 c) := by
    simp only [exec, Size.bits, hh, ite_true, State.read, BitVec.setWidth_eq, RegUpd.gpr_write_self]
    rw [hc]
  have s2 : Scratch ((s.write .x .x2 (a.setWidth 64)).write .x .x2 c) base := s1.write (by decide) _
  have g2 : ((s.write .x .x2 (a.setWidth 64)).write .x .x2 c).gpr .x2 = c := by
    rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  refine WP.block_cons_iff.mpr ⟨_, e1, WP.block_cons_iff.mpr ⟨_, e2, WP.block_cons_iff.mpr
    ⟨_, store_sc s2 ha (by omega) .x2, WP.block_cons_iff.mpr
    ⟨_, store_sc (s2.setMem _) (show (d + 8) % 8 = 0 by omega) (by omega) .x2, WP.block_nil_iff.mpr ?_⟩⟩⟩⟩
  refine ⟨by simp only [g2]; rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem nw_writeW_in (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) {j : Nat} (hj : j < 2) :
    nw (m.writeW (off base d) v) base (d + 4 * j) = (v.extractLsb' (32 * j) 32).toNat := by
  rw [nw, ← off_add]
  have := readW_writeW_inside m (off base d) v (k := 4 * j) (n := 4) (by omega) (by decide)
  rw [show (32 : Nat) = 8 * 4 from rfl, this, show 8 * (4 * j) = 32 * j by omega]

theorem consts_ok {s : State} {base : Addr} (hs : Scratch s base) :
    WP isa (.block consts) s fun t => Consts t.mem base ∧ Outside base CONST 48 s.mem t.mem ∧
      (∀ r, r ≠ .x2 → t.gpr r = s.gpr r) ∧ t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hC : CONST = 1104 := rfl
  have h26 : M26 = 1104 := rfl
  have h25 : M25 = 1120 := rfl
  have h19 : C19 = 1136 := rfl
  change WP isa (.block (([.movz .x .x2 0xffff 0, .movk .x .x2 0x03ff 1, VG.Impl.Ed25519.AArch64.st .x2 M26,
      VG.Impl.Ed25519.AArch64.st .x2 (M26 + 8)] : List Instr) ++
    (([.movz .x .x2 0xffff 0, .movk .x .x2 0x01ff 1, VG.Impl.Ed25519.AArch64.st .x2 M25,
      VG.Impl.Ed25519.AArch64.st .x2 (M25 + 8)] : List Instr) ++
    ([.movz .x .x2 19 0, .movk .x .x2 19 2, VG.Impl.Ed25519.AArch64.st .x2 C19,
      VG.Impl.Ed25519.AArch64.st .x2 (C19 + 8)] : List Instr)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (quad_ok hs 0xffff 0x03ff (hw := 1) (by decide) (c := 0x3ffffff) (by decide)
    (d := M26) (by decide) (by decide)) fun a ⟨am, ag, av, ar, aw, asp⟩ => ?_
  have ha : Scratch a base := ⟨(ag _ (by decide)).trans hs.x0, aw ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (quad_ok ha 0xffff 0x01ff (hw := 1) (by decide) (c := 0x1ffffff) (by decide)
    (d := M25) (by decide) (by decide)) fun b ⟨bm, bg, bv, br, bw, bsp⟩ => ?_
  have hb : Scratch b base := ⟨(bg _ (by decide)).trans ha.x0, bw ▸ ha.wr, ha.nowrap⟩
  refine WP.mono (quad_ok hb 19 19 (hw := 2) (by decide) (c := 0x0000001300000013) (by decide)
    (d := C19) (by decide) (by decide)) fun t ⟨tm, tg, tv, tr, tw, tsp⟩ => ?_
  refine ⟨⟨fun e he => ?_, fun e he => ?_, fun c hc => ?_⟩, ?_, fun r hr => by rw [tg r hr, bg r hr, ag r hr],
    by rw [tv, bv, av], by rw [tr, br, ar], by rw [tw, bw, aw], by rw [tsp, bsp, asp]⟩
  · rw [tm, bm, am]
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;>
    simp (disch := omega) only [h26, h25, h19, VG.Proof.Ed25519.AArch64.word_writeW_sep,
      VG.Proof.Ed25519.AArch64.word_writeW_self, Nat.mul_zero, Nat.add_zero, Nat.mul_one] <;> decide
  · rw [tm, bm]
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;>
    simp (disch := omega) only [h25, h19, VG.Proof.Ed25519.AArch64.word_writeW_sep,
      VG.Proof.Ed25519.AArch64.word_writeW_self, Nat.mul_zero, Nat.add_zero, Nat.mul_one] <;> decide
  · rw [tm]
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [Outside.nw (VG.Proof.Ed25519.AArch64.writeW_outside _ base _ (d := C19 + 8) (by omega))
        (by omega) (by omega), nw_writeW_in _ _ _ _ (by decide)]
      decide
    · rw [Outside.nw (VG.Proof.Ed25519.AArch64.writeW_outside _ base _ (d := C19 + 8) (by omega))
        (by omega) (by omega), nw_writeW_in _ _ _ _ (by decide)]
      decide
    · rw [show C19 + 4 * 2 = C19 + 8 + 4 * 0 from rfl, nw_writeW_in _ _ _ _ (by decide)]
      decide
    · rw [show C19 + 4 * 3 = C19 + 8 + 4 * 1 from rfl, nw_writeW_in _ _ _ _ (by decide)]
      decide
  · rw [tm, bm, am]
    exact ((((((Outside.refl _ _ _ _).writeW (by omega) (by omega) (by omega) _).writeW (by omega) (by omega)
      (by omega) _).writeW (by omega) (by omega) (by omega) _).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _).writeW (by omega) (by omega) (by omega) _

end VG.Proof.X25519.AArch64.Hybrid
