import VerifiedGarbage.Proof.X448.X86.AddSub

/-!
# X448 on x86 (32-bit): multiplication by a24

`vg_gf448_r16_mul_a24`'s arithmetic (`mulA24Fn`): `esi` points at the
operand, whose 16-bit limbs keep multiplication by 39081 within a 32-bit word.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem smallStep_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (hp : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 a)
    (ha : Slot a) (hi : i < 28) (hc : (s.gpr .ecx).toNat = 39081) :
    WP isa (.block [.mov .eax (.mem (at_ .esi (4 * i))), .mul .ecx, st .eax (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i)) (BitVec.ofNat 32 (39081 * limbs s.mem base a i)) ∧
      Keeps [.eax, .edx] s t := by
  have ha' : a + 112 ≤ 3584 := ha
  refine wp_load (hs.ea_ptr (k := 4 * i) hp (by omega)) (hs.read (by omega)) fun t ht => ?_
  have ts := hs.of_upd ht (by decide)
  refine wp_mul fun u uv um uk => ?_
  refine store_ok (ts.of_keeps uk (by decide)) (by simp only [TMP]; omega) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, um, ht.mem, uv, ht.gpr, ht.other .ecx (by decide), hc, Nat.mul_comm _ 39081]
  · exact (ht.rest (by decide)).trans (uk.trans (hv.rest _))

theorem a24Body_ok {s : State} {base : Addr} {o a : Nat} (hc : FnCtx s base 3 o a)
    (ab : Bounded s.mem base a) :
    WP isa (.block (argPtr .esi 2 ++ a24Cols ++ normalize)) s fun t =>
      FnPost base o s t ∧ F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  have ha' : a + 112 ≤ 3584 := hc.slotA
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (argPtr_ok hc.args (by decide) (by decide) hc.argA) fun t ⟨tp, tm, tk⟩ => ?_
  have tc := hc.keep tk (by decide) (by decide) (by rw [tm]; exact Outside.refl _ _ _ _)
  rw [← tm] at ab
  let f := fun i => 39081 * limbs t.mem base a i
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - radix := by
    intro i hi
    have h := Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))
    have hr : 39081 * radix ≤ 2 ^ 32 - radix := by decide
    exact Nat.le_trans h hr
  refine WP.mono (columns_normalize tc fb ?_) fun u ⟨op, ub, uv⟩ =>
    ⟨⟨(tk.mono (by decide)).trans (op.1.mono (by decide)), by rw [← tm]; exact op.2, ub⟩,
      toFe_a24 ?_⟩
  · unfold a24Cols
    refine wp_mov rfl fun u hu => ?_
    have us := tc.scr.of_upd hu (by decide)
    have up : u.gpr .esi = u.gpr .edi + BitVec.ofNat 32 a := by
      rw [hu.other .esi (by decide), hu.other .edi (by decide)]; exact tp
    have uc : (u.gpr .ecx).toNat = 39081 := by rw [hu.gpr]; rfl
    refine WP.mono (columns_ok us (by decide : Reg.edi ∉ [Reg.eax, Reg.edx]) fb ?_) fun v ⟨vf, vm, vk⟩ =>
      ⟨vf, by rw [← hu.mem]; exact vm, (hu.rest (by decide)).trans (vk.mono (by decide))⟩
    intro i hi v vs vm vk
    have vp : v.gpr .esi = v.gpr .edi + BitVec.ofNat 32 a := by
      rw [vk.1 _ (by decide), vk.1 _ (by decide)]; exact up
    have vc : (v.gpr .ecx).toNat = 39081 := by rw [vk.1 _ (by decide), uc]
    refine WP.mono (smallStep_ok vs vp tc.slotA hi vc) fun w ⟨wm, wk⟩ => ⟨?_, wk⟩
    rw [input_limb vm tc.slotA hi, hu.mem] at wm
    exact wm
  · rw [uv, valN_scale, tm]

end VG.Proof.X448.X86
