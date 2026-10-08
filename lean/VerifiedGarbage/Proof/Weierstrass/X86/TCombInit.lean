import VerifiedGarbage.Proof.Weierstrass.X86.TCombInv
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont
open Spec.Weierstrass

theorem tcombW_ptr {K : TCombCfg} {size : Nat} (hL : TCombLay K size) :
    ∀ w ∈ combWx K ++ [(K.bits + K.kbytes, 4 * K.zw)], K.ptr + 4 ≤ w.1 ∨ w.1 + w.2 ≤ K.ptr := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact combW_ptr hL w hw
  · simp only [List.mem_singleton] at hw; subst hw
    have := hL.ptr_bits; dsimp only; omega

/-- Zero stored to the `m` words at `o`, from `rax = 0`. -/
theorem zstores_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hz : s.gpr .eax = 0)
    {o : Nat} : ∀ m, o + 4 * m ≤ size →
    WP isa (.block ((List.range m).map fun i => .store (sc (o + 4 * i)) .eax)) s fun s' =>
      KeepRegs [] s s' ∧ Outside base o (4 * m) s.mem s'.mem ∧
        ∀ d < 4 * m, s'.mem (off base (o + d)) = 0
  | 0, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _,
      fun d hd => absurd hd (by omega)⟩
  | m + 1, hm => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zstores_ok hs hz m (by omega)) fun s₁ ⟨k₁, O₁, z₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by simp)
    have hrax : s₁.gpr .eax = 0 := (k₁.gpr _ (by simp)).trans hz
    simp only [List.map_cons, List.map_nil]
    refine wp_storeS (hs₁.ea (d := o + 4 * m) (by omega)) (hs₁.write (d := o + 4 * m) (n := 4) (by omega))
      fun s₂ u₂ => WP.block_nil ?_
    have Ow : Outside base (o + 4 * m) 4 s₁.mem s₂.mem := by
      rw [u₂.mem]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨k₁.trans (u₂.keeps _), fun x hx => (Ow x (by omega)).trans (O₁ x (by omega)),
      fun d hd => ?_⟩
    by_cases hd' : d < 4 * m
    · rw [Ow _ (by rw [ofs_off0 base (by omega)]; omega)]; exact z₁ d hd'
    · have e : off base (o + d) - off base (o + 4 * m) = BitVec.ofNat 64 (d - 4 * m) := by
        simp only [off]; rw [show o + d = o + 4 * m + (d - 4 * m) by omega, Offset.add_ofNat_add_sub]
      rw [u₂.mem, hrax]
      simp only [Mem.writeW, Mem.write, e, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show d - 4 * m < 2 ^ 64 by omega), show d - 4 * m < 32 / 8 by omega,
        ↓reduceIte]
      simp

theorem zeroEax_ok (s : State) :
    WP isa (.block [.mov .eax (.imm 0)]) s fun t => t.gpr .eax = 0 ∧ CKeeps [.eax] s t :=
  wp_movS rfl fun _t u _ => WP.block_nil ⟨u.gpr, u.keeps.1, u.mem, u.keeps.2⟩

theorem movEsi_ok (s : State) {j : Nat} (_hj : j < 2^31) :
    WP isa (.block [.mov .esi (.imm (BitVec.ofNat 32 j))]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 j ∧ CKeeps [.esi] s t :=
  wp_movS rfl fun _t u _ => WP.block_nil ⟨u.gpr, u.keeps.1, u.mem, u.keeps.2⟩

end VG.Proof.Weierstrass.X86
