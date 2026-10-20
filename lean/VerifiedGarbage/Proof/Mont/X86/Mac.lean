module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Step

/-! # The shared x86 multiply-accumulate word -/

@[expose] public section
namespace VG.Proof.Mont.X86.Rt
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- One shared multiply-accumulate word, with independently placed operands. -/
theorem macWord_ok {mo input output : Nat} {t : State} {W : Addr} {L : Nat} (hw : Ws t W L) {S c p : Nat}
    (hedi : PtrAt t W .edi S) (hecx : PtrAt t W .ecx c) (hebp : PtrAt t W .ebp p)
    (hm : S + mo + 4 ≤ L) (hb : c + input + 4 ≤ L) (ht : p + output + 4 ≤ L) :
    WP isa (.block (macWord output input mo)) t fun u =>
      u.mem = t.mem.writeW (off W (p + output)) (BitVec.ofNat 32
        (w32 t.mem W (S + mo) * w32 t.mem W (c + input) + (t.gpr .ebx).toNat + w32 t.mem W (p + output))) ∧
      (u.gpr .ebx).toNat = (w32 t.mem W (S + mo) * w32 t.mem W (c + input) + (t.gpr .ebx).toNat +
          w32 t.mem W (p + output)) / 2 ^ 32 ∧
      Keeps [.eax, .ebx, .edx] t u := by
  have hn := hw.nowrap
  simp only [macWord]
  refine wp_movS (readSrc_ptr hw hedi (d := mo) (by omega)) fun s₀ u₀ _ => ?_
  have hw₀ := hw.of_keeps u₀.keeps
  have hecx₀ : PtrAt s₀ W .ecx c := by rw [PtrAt, u₀.other _ (by decide)]; exact hecx
  refine wp_movS (readSrc_ptr hw₀ hecx₀ (d := input) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_mul fun s₂ m₂ => ?_
  have K₂ : Keeps [.eax, .edx] t s₂ := ((u₀.keeps.mono (by decide)).widen u₁.keeps).widen m₂.keeps
  have hw₂ := hw.of_keeps K₂
  have hp₂ : PtrAt s₂ W .ebp p := by rw [PtrAt, K₂.1 _ (by decide)]; exact hebp
  refine wp_addS (readSrc_ptr hw₂ hp₂ (d := output) (by omega)) fun s₃ u₃ c₃ => ?_
  refine wp_adcS rfl c₃ fun s₄ u₄ c₄ => ?_
  refine wp_addS rfl fun s₅ u₅ c₅ => ?_
  refine wp_adcS rfl c₅ fun s₆ u₆ c₆ => ?_
  have K₄ : Keeps [.eax, .edx] t s₄ := (K₂.widen u₃.keeps).widen u₄.keeps
  have K₆ : Keeps [.eax, .edx] t s₆ := (K₄.widen u₅.keeps).widen u₆.keeps
  have hw₆ := hw.of_keeps K₆
  have hp₆ : PtrAt s₆ W .ebp p := by rw [PtrAt, K₆.1 _ (by decide)]; exact hebp
  refine wp_storeS (ea_ptr hw₆ hp₆ (d := output) (by omega)) (ws_write hw₆ (y := p + output) (n := 4) (by omega))
    fun s₇ m₇ => ?_
  refine wp_movS rfl fun s₈ u₈ _ => WP.block_nil ?_
  -- The registers and memory along the way.
  have m₂' : s₂.mem = t.mem := by rw [m₂.mem, u₁.mem, u₀.mem]
  have m₄ : s₄.mem = t.mem := by rw [u₄.mem, u₃.mem, m₂']
  have m₆ : s₆.mem = t.mem := by rw [u₆.mem, u₅.mem, m₄]
  have eax₁ : s₁.gpr .eax = t.mem.readW (off W (S + mo)) 32 := by rw [u₁.other _ (by decide), u₀.gpr]
  have eax₂ := m₂.eax
  have edx₂ := m₂.edx
  rw [eax₁, u₁.gpr, u₀.mem] at eax₂ edx₂
  have ebx₂ : s₂.gpr .ebx = t.gpr .ebx := by
    rw [m₂.other _ (by decide) (by decide), u₁.other _ (by decide), u₀.other _ (by decide)]
  have eax₃ : s₃.gpr .eax = s₂.gpr .eax + t.mem.readW (off W (p + output)) 32 := by
    rw [u₃.gpr, m₂']
  have edx₄ : s₄.gpr .edx = s₃.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₄.gpr
  have eax₄ : s₄.gpr .eax = s₃.gpr .eax := u₄.other _ (by decide)
  have edx₃ : s₃.gpr .edx = s₂.gpr .edx := u₃.other _ (by decide)
  have ebx₄ : s₄.gpr .ebx = t.gpr .ebx := by rw [u₄.other _ (by decide), u₃.other _ (by decide), ebx₂]
  have eax₅ : s₅.gpr .eax = s₄.gpr .eax + s₄.gpr .ebx := u₅.gpr
  have edx₆ : s₆.gpr .edx = s₅.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₆.gpr
  have eax₆ : s₆.gpr .eax = s₅.gpr .eax := u₆.other _ (by decide)
  have edx₅ : s₅.gpr .edx = s₄.gpr .edx := u₅.other _ (by decide)
  have hpost := step_regs (t.mem.readW (off W (c + input)) 32) (t.mem.readW (off W (S + mo)) 32)
    (t.mem.readW (off W (p + output)) 32) (t.gpr .ebx) _ _ rfl rfl
  rw [Nat.mul_comm (t.mem.readW (off W (c + input)) 32).toNat] at hpost
  have ex₆ : s₆.gpr .eax = BitVec.ofNat 32 ((t.mem.readW (off W (S + mo)) 32).toNat *
      (t.mem.readW (off W (c + input)) 32).toNat) + t.mem.readW (off W (p + output)) 32 + t.gpr .ebx := by
    rw [eax₆, eax₅, ebx₄, eax₄, eax₃, eax₂]
  have dx₆ := edx₆
  rw [edx₅, edx₄, edx₃, edx₂, ebx₄, eax₄, eax₃, eax₂, m₂'] at dx₆
  have hx : s₆.gpr .eax = BitVec.ofNat 32 (w32 t.mem W (S + mo) * w32 t.mem W (c + input) +
      (t.gpr .ebx).toNat + w32 t.mem W (p + output)) := by
    apply BitVec.eq_of_toNat_eq
    rw [ex₆, hpost.1, BitVec.toNat_ofNat, Nat.add_right_comm]
  have K₇ : Keeps [.eax, .ebx, .edx] t s₇ := (K₆.mono (by decide)).widen (m₇.keeps [])
  refine ⟨by rw [u₈.mem, m₇.mem, m₆, hx], ?_, K₇.widen u₈.keeps⟩
  rw [u₈.gpr, m₇.gpr, dx₆, hpost.2, Nat.add_right_comm]

end VG.Proof.Mont.X86.Rt
