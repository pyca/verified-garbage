import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
import VerifiedGarbage.Proof.Mont.X86.Ops

/-! # Unsigned rows used by the divstep matrix updates -/
namespace VG.Proof.Weierstrass.X86.Inv
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Inv
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem rowAdd_ok {s : State} {base : Addr} {size coefficient acc src n : Nat}
    (hs : Scr s base size) (hc : coefficient + 4 ≤ size) (ha : acc + 4 * (n + 2) ≤ size)
    (hb : src + 4 * n ≤ size) (sep : src + 4 * n ≤ acc ∨ acc + 4 * (n + 2) ≤ src)
    (hlt : val32 s.mem base acc (n + 2) + w32 s.mem base coefficient * val32 s.mem base src n <
      2 ^ (32 * (n + 2))) :
    WP isa (.block (rowAdd coefficient acc src n)) s fun u =>
      Outside base acc (4 * (n + 2)) s.mem u.mem ∧
      val32 u.mem base acc (n + 2) = val32 s.mem base acc (n + 2) +
        w32 s.mem base coefficient * val32 s.mem base src n ∧ Keeps clob s u := by
  simp only [rowAdd, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs hc) fun s₁ U₁ _ => ?_
  refine wp_movS rfl fun s₂ U₂ _ => ?_
  have K : Keeps clob s s₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  have hs₂ := hs.of_keeps K (by decide)
  have M : s₂.mem = s.mem := U₂.mem.trans U₁.mem
  have C : s₂.gpr .ecx = s.mem.readW (off base coefficient) 32 := by
    rw [U₂.other _ (by decide), U₁.gpr]
  have P : s₂.gpr .ebp = s₂.gpr .edi + BitVec.ofNat 32 (4 * 0) := by
    change s₂.gpr .ebp = s₂.gpr .edi + 0
    simpa using U₂.gpr.trans (U₂.other .edi (by decide)).symm
  refine WP.mono (mulRow_ok hs₂ P (acc := acc) (b := src) (N := n) (w := acc) (by omega)
    hb (by omega) (by omega) (by rw [M, C]; exact hlt)) fun u ⟨O, V, K'⟩ => ?_
  rw [show 4 * n + 8 = 4 * (n + 2) by omega, M] at O
  rw [M, C] at V
  exact ⟨O, V, K.trans (K'.mono (by decide))⟩

end VG.Proof.Weierstrass.X86.Inv
