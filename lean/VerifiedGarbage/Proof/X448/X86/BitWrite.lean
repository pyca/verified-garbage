module
public import VerifiedGarbage.Proof.X448.X86.Instr

import VerifiedGarbage.Proof.X448.X86.ByteMem
import VerifiedGarbage.Proof.X448.X86.Args
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# X448 on x86 (32-bit): expanding a scalar byte

Public shifts select each bit and write it to its own byte in the working
space, through `ebp`, which `bitsLoop` keeps at `edi + 8 i` for byte `i`.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

theorem bitShift_ok {s : State} {j : Nat} (hj : j < 8) :
    WP isa (.block (([.mov .edx (.reg .eax)] : List Instr) ++
      if j = 0 then [] else [.shift .shr .edx j])) s fun t =>
      t.gpr .edx = s.gpr .eax >>> j ∧ t.mem = s.mem ∧ Keeps [.edx] s t := by
  refine wp_mov rfl fun t ht => ?_
  by_cases hz : j = 0
  · subst j
    exact WP.block_nil ⟨ht.gpr, ht.mem, ht.rest (by decide)⟩
  · rw [ite_eq_right hz]
    refine wp_shift (by omega) fun u hu => WP.block_nil ⟨?_, hu.mem.trans ht.mem,
      (ht.rest (by decide)).trans (hu.rest (by decide))⟩
    rw [hu.gpr, ht.gpr]

/-- Bit `j` of the byte `b` in `eax` to byte `d + (o + j)` of the working space, for
`ebp = edi + d`. -/
theorem bitP_ok {s : State} {base : Addr} (hs : Scr s base) {o d : Nat} (hd : d + o + 8 ≤ 8192)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 d)
    {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32) {j : Nat} (hj : j < 8) :
    WP isa (.block (bitP o j)) s fun t =>
      t.mem = s.mem.writeW (off base (d + (o + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
        Keeps [.edx] s t := by
  rw [bitP, WP.block_append_iff]
  refine WP.mono (bitShift_ok hj) fun t ⟨tv, tm, tk⟩ => ?_
  refine wp_alu (by simp [plain]) rfl fun u hu _ => ?_
  have us := (hs.of_keeps tk (by decide)).of_upd hu (by decide)
  have up : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 d := by
    rw [hu.other _ (by decide), hu.other _ (by decide), tk.1 _ (by decide), tk.1 _ (by decide), hp]
  refine wp_store8 (us.ea_ptr up (by omega)) (us.write (d := d + (o + j)) (n := 1) (by omega))
    fun v hv => WP.block_nil ⟨?_, tk.trans ?_⟩
  · rw [hv.mem, hu.mem, tm, Reg8.reg, hu.gpr]
    change s.mem.writeW _ ((t.gpr .edx &&& (1 : BitVec 32)).setWidth 8) = _
    rw [tv, ha, bit_byte b j hj]
  · exact (hu.rest (by decide)).trans (hv.rest _)

/-- The eight bits of the byte `b` in `eax` to bytes `d + o`, …, `d + o + 7`, for `ebp = edi + d`. -/
theorem byteP_ok {s : State} {base : Addr} (hs : Scr s base) {o d : Nat} (hd : d + o + 8 ≤ 8192)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 d)
    {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap (bitP o))) s fun t =>
      (∀ j < 8, t.mem (off base (d + (o + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Outside base (d + o) 8 s.mem t.mem ∧ Keeps [.edx] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (d + (o + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    Outside base (d + o) 8 s.mem t.mem ∧ Keeps [.edx] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (bitP o n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (bitP_ok (hs.of_keeps tk (by decide)) hd
      ((tk.1 _ (by decide)).trans (hp.trans (by rw [tk.1 _ (by decide)])))
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      have eq : off base (d + (o + j)) = off base (d + (o + n)) ↔ j = n := by
        rw [off_eq_iff base (by omega) (by omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86
