module

public import VerifiedGarbage.Proof.Ed25519.X86.Field
import VerifiedGarbage.Proof.X25519.X86.Freeze
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.X86.PointEncode
public import VerifiedGarbage.Proof.Ed25519.X86.PowerEnv
import VerifiedGarbage.Proof.Ed25519.X86.ScalarCodec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ed25519.RootPower
public import VerifiedGarbage.Impl.Ed25519.X86.Power
import VerifiedGarbage.Proof.X25519.X86.Field32.Call
import VerifiedGarbage.Proof.X25519.X86.Field32.Lit

/-! ### `Ed25519.X86.PointEncodeSign`, which the modules that import this one used -/

section

/-! ### `Ed25519.X86.Power`, which this module and modules that import it used -/

section

/-! The shared addition chain, by calls of `vg_gf25519_r32_mul` and
`vg_gf25519_r32_sqn` (`power250_ok`), computes the inversion and square-root powers with a few
squarings and a product each (`invert_ok`, `rootPower_ok`). -/

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Proof.X25519 (pw pw_mul pw_one sqn_pw pow_pw)

theorem power250_ok {s : State} {base : BitVec 32} (hs : Ctx base s) :
    WP isa power250 s fun t => IKeep base s t ∧
      env t.mem base 15 = pw (env s.mem base 2) (2 ^ 250 - 1) ∧
      env t.mem base 14 = pw (env s.mem base 2) 11 ∧
      ∀ i : Slot, i.val < 14 → env t.mem base i = env s.mem base i := by
  have hfit := hs.fit
  refine WP.mono (VG.Proof.X25519.X86.Field32.pow250Call_ok hs) fun t ⟨hk, hf, h1, h0⟩ =>
    ⟨⟨hk.edi, hk.esp, hk.rd, hk.wr, frameWidenS hf hfit (by decide) (by decide) (by decide)⟩, h1, h0,
      fun i hi => ?_⟩
  apply congrArg VG.Proof.X25519.toFe
  exact fe_frame1s hs hf (by decide) (by simp only [offset]; omega_using []) (.inl (by simp only [offset]; omega_using [hi]))

/-- The chain's tail for the inversion: five squarings, and `z^11`. -/
theorem invert_tail (z : Spec.X25519.Fe) :
    VG.Proof.X25519.sqn (pw z (2 ^ 250 - 1)) 5 * pw z 11 = VG.Proof.X25519.invert z := by
  rw [VG.Proof.X25519.invert_eq, pow_pw, sqn_pw, pw_mul]
  exact congrArg (pw z) (by decide)

/-- The chain's tail for the square root: two squarings, and `z`. -/
theorem root_tail (z : Spec.X25519.Fe) :
    VG.Proof.X25519.sqn (pw z (2 ^ 250 - 1)) 2 * z = VG.Proof.Ed25519.rootPower z := by
  have e := pw_mul z ((2 ^ 250 - 1) * 2 ^ 2) 1
  rw [pw_one] at e
  rw [VG.Proof.Ed25519.rootPower_eq, pow_pw, sqn_pw, e]
  exact congrArg (pw z) (by decide)

theorem invert_ok {s : State} {base : BitVec 32} (hs : Ctx base s) :
    WP isa invert s fun t => IKeep base s t ∧
      env t.mem base 15 = VG.Proof.X25519.invert (env s.mem base 2) ∧
      ∀ i : Slot, i.val < 14 → env t.mem base i = env s.mem base i := by
  refine WP.seq (WP.mono (power250_ok hs) fun t ⟨kt, h15, h14, hlow⟩ => ?_)
  have h : ISpec base _ _ := (sqnI base 15 ⟨by decide, by decide⟩ 5 (by decide) (by decide)).seq
    (mulI base 15 15 14 ⟨by decide, by decide⟩)
  refine WP.mono (h t (kt.ctx hs)) fun u ⟨ku, eu⟩ => ⟨kt.trans ku, ?_, fun i hi => ?_⟩
  · rw [eu]
    simp only [opMul, opSqn, Function.update_self, Function.update_of_ne (show (14 : Slot) ≠ 15 by decide)]
    rw [h15, h14, invert_tail]
  · have h15 : i ≠ 15 := fun h => by subst h; exact absurd hi (by decide)
    rw [eu]
    simp only [opMul, opSqn, Function.update_of_ne h15]
    exact hlow i hi

theorem rootPower_ok {s : State} {base : BitVec 32} (hs : Ctx base s) :
    WP isa Impl.Ed25519.X86.rootPower s fun t => IKeep base s t ∧
      env t.mem base 15 = VG.Proof.Ed25519.rootPower (env s.mem base 2) ∧
      ∀ i : Slot, i.val < 14 → env t.mem base i = env s.mem base i := by
  refine WP.seq (WP.mono (power250_ok hs) fun t ⟨kt, h15, _, hlow⟩ => ?_)
  have h : ISpec base _ _ := (sqnI base 15 ⟨by decide, by decide⟩ 2 (by decide) (by decide)).seq
    (mulI base 15 15 2 ⟨by decide, by decide⟩)
  refine WP.mono (h t (kt.ctx hs)) fun u ⟨ku, eu⟩ => ⟨kt.trans ku, ?_, fun i hi => ?_⟩
  · rw [eu]
    simp only [opMul, opSqn, Function.update_self, Function.update_of_ne (show (2 : Slot) ≠ 15 by decide)]
    rw [h15, hlow 2 (by decide), root_tail]
  · have h15 : i ≠ 15 := fun h => by subst h; exact absurd hi (by decide)
    rw [eu]
    simp only [opMul, opSqn, Function.update_of_ne h15]
    exact hlow i hi

end VG.Proof.Ed25519.X86

end

end

/-! Merged from `Proof.Ed25519.X86.PointAffine`. -/

@[expose] public section

section
/-! Convert extended coordinates with the verified inversion chain. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem affine_eval (e : Env) :
    evalOps affineOps e 0 = e 0 * e 15 ∧ evalOps affineOps e 1 = e 1 * e 15 := ⟨rfl, rfl⟩
theorem pointAffine_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa pointAffine s fun t => IKeep x s t ∧
      env t.mem x 0 = env s.mem x 0 * Spec.X25519.pow (env s.mem x 2) (Spec.X25519.P - 2) ∧
      env t.mem x 1 = env s.mem x 1 * Spec.X25519.pow (env s.mem x 2) (Spec.X25519.P - 2) := by
  refine WP.seq (WP.mono (invert_ok hc) fun u ⟨ku, eu, el⟩ => ?_)
  refine WP.mono (fieldCode_ok affineOps (ku.ctx hc)) fun t ⟨kt, et⟩ => ?_
  refine ⟨ku.trans (IKeep.of_field kt), ?_, ?_⟩
  · rw [et, (affine_eval _).1, eu, el 0 (by decide), VG.Proof.X25519.invert_eq]
  · rw [et, (affine_eval _).2, eu, el 1 (by decide), VG.Proof.X25519.invert_eq]

end VG.Proof.Ed25519.X86
end

/-! Place the affine x parity in the high bit of the canonical y encoding. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem sign_word (w : BitVec 32) :
    (w &&& 1).rotateRight 1 = BitVec.ofNat 32 ((w.toNat % 2) * 2 ^ 31) := by
  have he : w &&& 1 = BitVec.ofNat 32 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 32 by omega_using [])]
  rw [he]
  rcases Nat.mod_two_eq_zero_or_one w.toNat with h | h <;> rw [h] <;> decide

theorem field_parity (m : Mem) (x : BitVec 32) (o : Nat) : fe m x o % 2 = wv m x o % 2 := by
  rw [fe, num_shift]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.add_mod, Nat.mul_mod,
    show 2 ^ 32 % 2 = 0 from by decide, Nat.zero_mul, Nat.mod_mod]

theorem pointSign_ok {x : BitVec 32} {s : State} (hc : Ctx x s) :
    WP isa (.block pointSign) s fun t => IKeep x s t ∧ t.mem = s.mem ∧
      t.gpr .esi = BitVec.ofNat 32 ((fe s.mem x 64 % 2) * 2 ^ 31) := by
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha =>
    Wp.wp_andi fun b hb => Wp.wp_ror (by decide) fun t ht => WP.block_nil ?_
  refine ⟨(IKeep.of_counter ha).trans ((IKeep.of_counter hb).trans (IKeep.of_counter ht)),
    by rw [ht.mem, hb.mem, ha.mem], ?_⟩
  rw [ht.gpr, hb.gpr, ha.gpr, field_parity]
  exact sign_word _

theorem fe_last_write {x : BitVec 32} (m : Mem) (w : BitVec 32) (hx : x.toNat + 8192 ≤ 2 ^ 32) :
    fe (m.writeW (addr x 124) w) x 96 =
      num (fun k => wv m x (96 + 4 * k)) 7 + 2 ^ 224 * w.toNat := by
  rw [fe, num_succ]
  have h : num (fun k => wv (m.writeW (addr x 124) w) x (96 + 4 * k)) 7 =
      num (fun k => wv m x (96 + 4 * k)) 7 := num_congr fun k hk => by
    apply congrArg BitVec.toNat
    exact wd_write_ne _ _ (by omega_using [hx, hk]) (by omega_using [hx]) (Or.inl (by omega_using [hk]))
  rw [h]
  change _ + 2 ^ 224 * (wd (m.writeW (addr x 124) w) x 124).toNat = _
  rw [wd_write_self]

theorem encodeSign_ok {x : BitVec 32} {s : State} (hc : Ctx x s)
    (parity y : Nat) (hp : parity ≤ 1) (hy : y < 2 ^ 255) (hv : fe s.mem x 96 = y)
    (hs : s.gpr .esi = BitVec.ofNat 32 (parity * 2 ^ 31)) :
    WP isa (.block encodeSign) s fun t => FieldKeep x s t ∧ fe t.mem x 96 = y + parity * 2 ^ 255 := by
  have top : wv s.mem x 124 < 2 ^ 31 := by
    have h := num_digit 7 (f := fun k => wv s.mem x (96 + 4 * k)) (n := 8)
      (fun k _ => BitVec.isLt _) (by decide)
    change fe s.mem x 96 / 2 ^ 224 % 2 ^ 32 = wv s.mem x 124 at h
    rw [hv] at h
    omega_using [hy, h]
  change (s.mem.readW (addr x 124) 32).toNat < 2 ^ 31 at top
  refine Wp.wp_ldm hc.edi (hc.inRW (by decide) (by decide)) fun a ha => ?_
  refine Wp.wp_add fun b hb _ => ?_
  have kb := (updKeep ha).trans (updKeep hb)
  have cb := kb.ctx hc
  refine Wp.wp_stm cb.edi (cb.inW (by decide) (by decide)) fun t ht => WP.block_nil ?_
  have val : (b.gpr .eax).toNat = wv s.mem x 124 + parity * 2 ^ 31 := by
    rw [hb.gpr, ha.gpr, ha.other .esi (by decide), hs, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show parity * 2 ^ 31 < 2 ^ 32 by omega_using [hp]), Nat.mod_eq_of_lt (by omega_using [hp, top])]
  refine ⟨⟨kb.trans ⟨by rw [ht.gpr], by rw [ht.gpr], by rw [ht.gpr], ht.rd, ht.wr⟩, ?_⟩, ?_⟩
  · rw [ht.mem, hb.mem, ha.mem]
    exact frame_write1 (Frame.refl _ _) hc.fit (by decide) (by decide) (by decide) _
  · rw [ht.mem, hb.mem, ha.mem, fe_last_write _ _ hc.fit, val]
    have hsum : fe s.mem x 96 = num (fun k => wv s.mem x (96 + 4 * k)) 7 + 2 ^ 224 * wv s.mem x 124 := rfl
    rw [hsum] at hv
    omega_using [hv]

end VG.Proof.Ed25519.X86

end

end

/-! Canonical reduction preserves the field environment. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86
open VG.Impl.X25519.X86 (freeze T)
open VG.Proof.X25519 (toFe toFe_mod)

theorem freezeField_ok {x : BitVec 32} {s : State} (hc : Ctx x s) (a : Slot) :
    WP isa (.block (freeze (offset a))) s fun t => FieldKeep x s t ∧
      env t.mem x = env s.mem x ∧ fe t.mem x (offset a) = (env s.mem x a).val := by
  refine WP.mono (freeze_ok hc (slot_valid a)) fun t ⟨hk, hf, hv⟩ => ?_
  have fit := hc.fit
  refine ⟨⟨hk, frame_wide hc.fit4 (slot_valid a) (by decide) hf⟩, ?_, hv⟩
  funext i
  by_cases hi : i = a
  · subst i
    change toFe (fe t.mem x (offset a)) = _
    rw [hv]; exact toFe_mod _
  · apply congrArg toFe
    apply fe_frame
    intro k hk'
    apply wd_frame hf
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hs := slot_ne (slot_valid a) (slot_valid i) (fun h => hi (offset_inj h))
      exact sub_disj (by simp only [offset]; omega_using [fit, i.isLt, hk'])
        (by simp only [offset]; omega_using [fit, a.isLt]) (by omega_using [hs, hk'])
    · exact sub_disj (by simp only [offset]; omega_using [fit, i.isLt, hk'])
        (by simp only [T]; omega_using [fit]) (Or.inl (by simp only [offset, T]; omega_using [hk']))

end VG.Proof.Ed25519.X86
