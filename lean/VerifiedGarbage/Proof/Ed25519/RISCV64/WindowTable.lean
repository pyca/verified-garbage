module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
public import VerifiedGarbage.Impl.Ed25519.RISCV64.VerifyWindow
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.ReadHalves

/-!
# Points into slots 4–7 on RISC-V, from any table

`pointFromTableQ` with `s0` at `q` reads the 128 bytes there, a table entry
of the working space or of a static outside it, into slots 4–7
(`pointFromTableQ_ok`), as `pointFromTable` reads one into slots 0–3. An
entry at offset `o` of the working space is the point at `b + o`
(`tableAt_shift`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519 (val32_congr)
open VG.Impl.Ed25519 (negBaseCached)

theorem wd_shift' (m : Mem) (b : Addr) (o d : Nat) : wd m (b + BitVec.ofNat 64 o) d = wd m b (o + d) := by
  unfold wd; rw [Offset.add_add]

theorem FS_shift (m : Mem) (b : Addr) (o d : Nat) : FS m (b + BitVec.ofNat 64 o) d = FS m b (o + d) := by
  unfold FS V limb
  simp only [wd_shift', Nat.add_assoc]

theorem tableAt_shift (m : Mem) (b : Addr) (o : Nat) : tableAt m (b + BitVec.ofNat 64 o) 0 = tableAt m b o := by
  simp only [tableAt, FS_shift, Nat.add_zero]

section
variable {b : Addr}

/-- After `j` coordinates of `pointFromTableQ` from `s0 = q`. -/
structure FromTableQInv (b q : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 192, 32 * j⟩] s0.mem s.mem
  outs : ∀ i < j, V s.mem b (192 + 32 * i) = V s0.mem q (32 * i)

theorem pointFromTableQ_ok {s : State} (hc : Ctx8 b s) {q : Addr} (h14 : s.gpr .s0 = q)
    (hr : ∀ k < 128, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 k) 4)
    (hd : (⟨q, 128⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 192, 128⟩) :
    WP isa (.block pointFromTableQ) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [⟨b + BitVec.ofNat 64 192, 128⟩] s.mem t.mem ∧
      point (env t.mem b) 4 5 6 7 = tableAt s.mem q 0 ∧
      ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env t.mem b i = env s.mem b i := by
  refine WP.mono (wp_range_flatMap (M := isa) (FromTableQInv b q s) (fun j t hj h => ?_) 4 (Nat.le_refl _) s
    ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => by omega⟩) fun t h => ⟨h.rest, h.frame, ?_, fun i hi => ?_⟩
  · have hct : Ctx8 b t := hc.of_rest h.rest (by decide)
    refine WP.mono (unpackField_ok hct.ctx (p := .s0) (by decide) (q := q)
      (o := 64 + 32 * (4 + j)) (src := 32 * j)
      (by rw [h.rest.gpr _ (by decide), h14]) (by omega) (by omega) (by omega)
      (fun k hk => by rw [h.rest.rd, h.rest.wr]; exact hr _ (by omega))
      (hd.sub_left (Offset.sub_base q (by omega)) |>.sub_right (by
        rw [show 64 + 32 * (4 + j) = 192 + 32 * j by omega, ← Offset.add_add]
        exact Offset.sub_base _ (by omega))))
      fun u ⟨ru, fu, lu⟩ => ?_
    have hsrc : V t.mem q (32 * j) = V s.mem q (32 * j) := by
      unfold V
      refine val32_congr (limb_frame h.frame fun r hr k hk => ?_)
      rw [List.mem_singleton.mp hr]
      exact (hd.sub_left (Offset.sub_base q (d := 32 * j + 4 * k) (n := 4) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    refine ⟨h.rest.trans ru, ?_, fun i hi => ?_⟩
    · refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)
      · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [← h.outs i hi]
        unfold V
        exact val32_congr (limb_frame fu fun r hr k hk => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
      · rw [← hsrc, V, V]
        refine val32_congr fun k hk => ?_
        rw [show 192 + 32 * i = 64 + 32 * (4 + i) by omega, lu k hk, limb]
  · have e0 := h.outs 0 (by decide)
    have e1 := h.outs 1 (by decide)
    have e2 := h.outs 2 (by decide)
    have e3 := h.outs 3 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3
    simp only [tableAt, point, env, FS]
    rw [show offset 4 = 192 from rfl, show offset 5 = 224 from rfl, show offset 6 = 256 from rfl,
      show offset 7 = 288 from rfl, e0, e1, e2, e3]
  · have hs := slot_range i
    unfold env FS V
    refine congrArg _ (val32_congr (limb_frame h.frame fun r hr k hk => ?_))
    rw [List.mem_singleton.mp hr]
    rcases hi with hi | hi
    · exact Offset.disjoint _ (.inl (by simp only [offset]; omega)) (by omega) (by omega)
    · exact Offset.disjoint _ (.inr (by simp only [offset]; omega)) (by omega) (by omega)

/-! ## The static of `-[1]B … -[15]B` -/

private theorem lo_digit (v k' : Nat) :
    v / 2 ^ (64 * k') % 2 ^ 64 % 2 ^ 32 = v / 2 ^ (32 * (2 * k')) % 2 ^ 32 := by
  rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64), show 32 * (2 * k') = 64 * k' by omega]

private theorem hi_digit (v k' : Nat) :
    (v / 2 ^ (64 * k') % 2 ^ 64) >>> 32 % 2 ^ 32 = v / 2 ^ (32 * (2 * k' + 1)) % 2 ^ 32 := by
  rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mod_mul_right_div_self,
    Nat.mod_mod, Nat.div_div_eq_div_mul, ← Nat.pow_add, show 64 * k' + 32 = 32 * (2 * k' + 1) by omega]

/-- Limb `k` of coordinate `c` of the static's entry `j`. -/
theorem limb_static {m : Mem} {T : Addr}
    (hw : ∀ q < 240, m.readW (T + BitVec.ofNat 64 (8 * q)) 64 = bWord q) {j c k : Nat}
    (hj : j < 15) (hc : c < 4) (hk : k < 8) :
    limb m (T + BitVec.ofNat 64 (128 * j)) (32 * c) k =
      (pointCoord (negBaseCached j) c).val / 2 ^ (32 * k) % 2 ^ 32 := by
  unfold limb wd
  rw [Offset.add_add]
  obtain ⟨k', hk'⟩ : ∃ k', k = 2 * k' ∨ k = 2 * k' + 1 := ⟨k / 2, by omega⟩
  rcases hk' with rfl | rfl
  · have hq : 16 * j + 4 * c + k' < 240 := by omega
    rw [show 128 * j + (32 * c + 4 * (2 * k')) = 8 * (16 * j + 4 * c + k') by omega,
      Mem.readW_lo32 (hw _ hq), BitVec.toNat_setWidth, bWord, BitVec.toNat_ofNat,
      show (16 * j + 4 * c + k') / 16 = j by omega, show (16 * j + 4 * c + k') / 4 % 4 = c by omega,
      show (16 * j + 4 * c + k') % 4 = k' by omega, lo_digit]
  · have hq : 16 * j + 4 * c + k' < 240 := by omega
    rw [show 128 * j + (32 * c + 4 * (2 * k' + 1)) = 8 * (16 * j + 4 * c + k') + 4 by omega,
      ← Offset.add_add, Mem.readW_hi32 (hw _ hq), BitVec.extractLsb'_toNat, bWord, BitVec.toNat_ofNat,
      show (16 * j + 4 * c + k') / 16 = j by omega, show (16 * j + 4 * c + k') / 4 % 4 = c by omega,
      show (16 * j + 4 * c + k') % 4 = k' by omega, hi_digit]

/-- **The static's entry `j`** is `negBaseCached j`. -/
theorem tableAt_static {m : Mem} {T : Addr}
    (hw : ∀ q < 240, m.readW (T + BitVec.ofNat 64 (8 * q)) 64 = bWord q) {j : Nat} (hj : j < 15) :
    tableAt m (T + BitVec.ofNat 64 (128 * j)) 0 = negBaseCached j := by
  have hf : ∀ c < 4, FS m (T + BitVec.ofNat 64 (128 * j)) (32 * c) = pointCoord (negBaseCached j) c := by
    intro c hc
    unfold FS V
    rw [val32_congr (g := fun k => (pointCoord (negBaseCached j) c).val / 2 ^ (32 * k) % 2 ^ 32)
      fun k hk => limb_static hw hj hc hk, val32_digits,
      Nat.mod_eq_of_lt (Nat.lt_trans (pointCoord (negBaseCached j) c).isLt (by decide))]
    exact Fin.ext (Nat.mod_eq_of_lt (pointCoord (negBaseCached j) c).isLt)
  have e0 := hf 0 (by decide)
  have e1 := hf 1 (by decide)
  have e2 := hf 2 (by decide)
  have e3 := hf 3 (by decide)
  simp only [Nat.mul_zero, Nat.reduceMul] at e0 e1 e2 e3
  simp only [tableAt, Nat.zero_add, e0, e1, e2, e3, pointCoord]

end

end VG.Proof.Ed25519.RISCV64
