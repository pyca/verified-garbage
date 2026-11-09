module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointMul
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed25519 on RISC-V: the field area cleared

`initFields_ok`: the slots cleared.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (decodeLE bytesAt)

section
variable {b : Addr}

theorem initFields_ok {s : State} (hc : Ctx b s) :
    WP isa (.block initFields) s fun t => Rest [.a4] s t ∧ Frame [FA b] s.mem t.mem := by
  unfold initFields
  refine wp_li (by decide) fun s1 u1 => ?_
  refine WP.mono (stores_ok (r := .a4) (o := 64) (n := 176) (by omega) (by omega)
    (hc.of_rest (u1.rest (ws := [.a4]) (by decide)) (by decide))) fun t ⟨_, h2, _, h4⟩ =>
      ⟨(u1.rest (by decide)).trans (h4.mono (by decide)), ?_⟩
  rw [← u1.mem]
  exact h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩

end

end VG.Proof.Ed25519.RISCV64
