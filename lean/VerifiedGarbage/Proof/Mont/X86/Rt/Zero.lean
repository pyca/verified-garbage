module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Csub
import VerifiedGarbage.Proof.Framework.Omega

/-! # Zeroing the accumulator of the run-time width multiplication

`zeroAcc`'s loop: `K` words from `ebp` zeroed, `esi` counting `4 K` bytes
down (`zeroLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

/-- The body of the zeroing loop. -/
def zeroBody : List Instr := [.store (at_ .ebp 0) .eax, .alu .add .ebp (.imm 4), .alu .sub .esi (.imm 4)]

theorem zeroLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {x K : Nat} (hK : 0 < K)
    (hx : x + 4 * K ≤ L) (hebp : PtrAt t₀ W .ebp x) (hesi : (t₀.gpr .esi).toNat = 4 * K)
    (heax : t₀.gpr .eax = 0) :
    WP isa (.loop (.block zeroBody) .ne) t₀ fun u =>
      Outside W x (4 * K) t₀.mem u.mem ∧ val32 u.mem W x K = 0 ∧ Keeps [.ebp, .esi] t₀ u := by
  have hn := hw.nowrap
  let I : Nat → State → Prop := fun j t =>
    Keeps [.ebp, .esi] t₀ t ∧ PtrAt t W .ebp (x + 4 * j) ∧ (t.gpr .esi).toNat = 4 * (K - j) ∧
    Outside W x (4 * j) t₀.mem t.mem ∧ val32 t.mem W x j = 0
  have I₀ : I 0 t₀ := ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hesi, Outside.refl _ _ _ _, rfl⟩
  refine WP.mono (WP.loop (M := isa) (Q := I K) (fun m t => ∃ j, m = K - j ∧ j < K ∧ I j t) ?_ K t₀
    ⟨0, by omega_using [hK], hK, I₀⟩) fun u ⟨Ku, _, _, O, V⟩ => ⟨O, V, Ku⟩
  rintro m t ⟨j, rfl, hj, Kt, ebp, esi, O, V⟩
  have ht := hw.of_keeps Kt
  have eax : t.gpr .eax = 0 := by rw [Kt.1 _ (by decide)]; exact heax
  simp only [zeroBody]
  refine wp_storeS (ea_ptr ht ebp (d := 0) (by omega_using [hx, hj]))
    (ws_write ht (y := x + 4 * j + 0) (n := 4) (by omega_using [hx, hj])) fun s₁ m₁ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => ?_
  refine wp_subZ rfl fun s₃ u₃ z₃ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf esi hj
  have esi₂ : s₂.gpr .esi = t.gpr .esi := by rw [u₂.other _ (by decide), m₁.gpr]
  have I' : I (j + 1) s₃ := by
    refine ⟨((Kt.widen (m₁.keeps [])).widen u₂.keeps).widen u₃.keeps, ?_, by rw [u₃.gpr, esi₂]; exact c₁, ?_, ?_⟩
    · rw [PtrAt, u₃.other _ (by decide), u₂.gpr, m₁.gpr, ptr_add ebp]
      rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega_using []
    · rw [u₃.mem, u₂.mem, m₁.mem, Nat.add_zero]
      exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
        ((writeW32_outside _ _ _ (by omega_using [hx, hj, hn])).mono (by omega_using []) (by omega_using []))
    · rw [u₃.mem, u₂.mem, m₁.mem, Nat.add_zero, val32_store hn (by omega_using [hx, hj]), V, eax]; rfl
  by_cases hjN : j + 1 = K
  · exact .inl ⟨by simp only [eval, z₃, esi₂, c₂, hjN, decide_true, Option.map_some, Bool.not_true], hjN ▸ I'⟩
  · exact .inr ⟨by simp only [eval, z₃, esi₂, c₂, decide_eq_false hjN, Option.map_some, Bool.not_false],
      K - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hjN], I'⟩

end VG.Proof.Mont.X86.Rt
