module

public import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Impl.Mont.X86.Window

/-! # Copying a number to the words at a moving pointer (`esi`) -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

/-- `[esi]`, with `esi` at `d` bytes into the working space. -/
theorem Scr.ea_esi {s : State} {base : Addr} {size d : Nat} (hs : Scr s base size)
    (he : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 d) (hd : d < size) :
    s.ea { base := .esi } = off base d := by
  change ((s.gpr .esi + BitVec.ofNat 32 0).setWidth 64) = _
  rw [he]
  simp only [BitVec.add_zero]
  exact hs.ea hd

theorem esi_step (x : BitVec 32) (d : Nat) :
    x + BitVec.ofNat 32 d + 4 = x + BitVec.ofNat 32 (d + 4) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (4 : BitVec 32).toNat = 4 from rfl]
  omega

theorem ptr_cmp (x : BitVec 32) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (x + BitVec.ofNat 32 a - (x + BitVec.ofNat 32 b) == 0) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
      show (0 : BitVec 32).toNat = 0 from rfl] at h'
    have := x.isLt
    omega
  · rintro rfl
    exact BitVec.sub_self _

/-- The `k` words at `src` to the `k` words at `dst`, where `esi` points. -/
theorem copyOut_ok {s : State} {base : Addr} {size k src dst : Nat} (hs : Scr s base size)
    (hk : 0 < k) (hsrc : src + 4 * k ≤ size) (hdst : dst + 4 * k ≤ size)
    (apart : dst + 4 * k ≤ src ∨ src + 4 * k ≤ dst)
    (he : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 dst) :
    WP isa (copyOut k src) s fun t =>
      val32 t.mem base dst k = val32 s.mem base src k ∧
      Outside base dst (4 * k) s.mem t.mem ∧
      t.gpr .esi = t.gpr .edi + BitVec.ofNat 32 (dst + 4 * k) ∧
      Keeps [.eax, .edx, .ebp, .esi] s t := by
  have hn := hs.nowrap
  unfold copyOut
  refine wordLoop_ok (fun j t => Keeps [.eax, .edx, .ebp, .esi] s t ∧
      Outside base dst (4 * j) s.mem t.mem ∧ val32 t.mem base dst j = val32 s.mem base src j ∧
      t.gpr .esi = t.gpr .edi + BitVec.ofNat 32 (dst + 4 * j)) hk
    (by have := hs.size_lt; omega)
    (fun j u u' ⟨K, O, V, E⟩ ⟨hm, hr, hw, hg⟩ =>
      ⟨⟨fun r h => (hg r (by simp_all) (by simp_all)).trans (K.1 r h), hr.trans K.2.1, hw.trans K.2.2⟩,
        hm ▸ O, hm ▸ V, by rw [hg _ (by decide) (by decide), hg _ (by decide) (by decide)]; exact E⟩)
    ⟨Keeps.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _, rfl, by simpa only [Nat.mul_zero, Nat.add_zero] using he⟩
    (fun j hj t ⟨K, O, V, E⟩ ej => ?_) (fun u ⟨K, O, V, E⟩ => ⟨V, O, E, K⟩)
  have ht := hs.of_keeps K (by decide)
  refine wp_movS (readSrc_at' ht ej (d := src) (by omega)) fun s₁ u₁ _ => ?_
  have hs₁ := ht.of_keeps u₁.keeps (by decide)
  have e₁ : s₁.gpr .esi = s₁.gpr .edi + BitVec.ofNat 32 (dst + 4 * j) := by
    rw [u₁.other _ (by decide), u₁.other _ (by decide)]; exact E
  refine wp_storeS (Scr.ea_esi hs₁ e₁ (by omega)) (hs₁.write (d := dst + 4 * j) (n := 4) (by omega))
    fun s₂ m₂ => ?_
  refine wp_addS rfl fun u u₃ _ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (K.trans (u₁.keeps.mono (by decide))).trans ((m₂.keeps _).trans (u₃.keeps.mono (by decide)))
  · rw [u₃.mem, m₂.mem, u₁.mem]
    exact (O.mono (Nat.le_refl _) (by omega)).trans
      ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · rw [u₃.mem, m₂.mem, u₁.mem, val32_store hn (by omega), V, u₁.gpr, val32_succ]
    exact congrArg (val32 s.mem base src j + 2 ^ (32 * j) * ·)
      (O.w32 (d := src + 4 * j) (by omega) (by omega))
  · rw [u₃.gpr, u₃.other _ (by decide), m₂.gpr, e₁, esi_step]
    congr 2
  · rw [u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide)]
  · rw [u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide)]

end VG.Proof.Mont.X86.Dynamic
