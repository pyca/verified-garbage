import VerifiedGarbage.Impl.Ed448.AArch64.Whole
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Sha3

/-!
# Ed448's complete operations on AArch64: the Keccak state zeroed

`zeroStores`, with `x15` the state's address: the 25 words zeroed
(`zstores_ok`), so the state is `Spec.Sha3.zero` (`zero_state`).
-/

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64
open VG.Spec.Sha3 (stateAt)

theorem movz14_ok (s : State) :
    WP isa (.block [.movz .x .x14 0 0]) s fun t => t.gpr .x14 = 0 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v ∧ ∀ r, r ≠ .x14 → t.gpr r = s.gpr r := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr⟩

/-- After the first `n` stores of zero. -/
structure ZInv (scr : Addr) (s : State) (n : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : t.v = s.v
  gpr : t.gpr = s.gpr
  frame : Frame [⟨scr, 200⟩] s.mem t.mem
  words : ∀ j < n, t.mem.readW (scr + BitVec.ofNat 64 (8 * j)) 64 = 0

theorem zstores_ok {s : State} {scr : Addr} (h15 : s.gpr .x15 = scr) (h14 : s.gpr .x14 = 0)
    (hw : (⟨scr, 8192⟩ : Region) ∈ s.wr) :
    ∀ n ≤ 25, WP isa (.block ((List.range n).map fun k => Instr.str .x .x14 .x15 (8 * k))) s (ZInv scr s n)
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => by omega⟩
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zstores_ok h15 h14 hw n (by omega)) fun u hu => ?_
    have dest : InRegions u.wr (u.gpr .x15 + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [hu.gpr, hu.wr, h15]
      exact ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩
    apply WP.of_runBlock
    have e15 : u.gpr .x15 = scr := by rw [hu.gpr, h15]
    have e14 : u.gpr .x14 = 0 := by rw [hu.gpr, h14]
    simp only [runBlock_cons]
    rw [exec_str_x ⟨by omega, by omega⟩ dest]
    simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
    rw [e15, e14]
    refine ⟨hu.rd, hu.wr, hu.sp, hu.v, hu.gpr, ?_, fun j hj => ?_⟩
    · exact hu.frame.writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by omega) (by omega))
    · show (u.mem.writeW (scr + BitVec.ofNat 64 (8 * n)) (0 : BitVec 64)).readW
        (scr + BitVec.ofNat 64 (8 * j)) 64 = 0
      by_cases hjn : j = n
      · subst j; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact hu.words j (by omega)

theorem zero_state {m : Mem} {p : Addr} (h : ∀ j < 25, m.readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0) :
    stateAt m p = Spec.Sha3.zero := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Sha3.stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

end VG.Proof.Ed448.AArch64.Whole

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Spec.Sha3 (stateAt)

/-- `zeroStores`, with `x15` the state's address. -/
theorem zeroStores_run {s : State} {scr : Addr} (h15 : s.gpr .x15 = scr)
    (hw : (⟨scr, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block zeroStores) s fun t => t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.v = s.v ∧
      (∀ r, r ≠ .x14 → t.gpr r = s.gpr r) ∧ Frame [⟨scr, 200⟩] s.mem t.mem ∧
      stateAt t.mem scr = Spec.Sha3.zero := by
  rw [zeroStores, show ∀ (i : Instr) is, i :: is = [i] ++ is from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (movz14_ok s) fun w ⟨w14, wm, wrd, wwr, wsp, wv, wg⟩ => ?_
  refine WP.mono (zstores_ok ((wg _ (by decide)).trans h15) w14 (by rw [wwr]; exact hw) 25 (by omega))
    fun x hx => ⟨hx.rd.trans wrd, hx.wr.trans wwr, hx.sp.trans wsp, hx.v.trans wv,
      fun r hr => by rw [hx.gpr]; exact wg r hr, by rw [← wm]; exact hx.frame, zero_state hx.words⟩

end VG.Proof.Ed448.AArch64.Whole
