module
public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Frame
public import VerifiedGarbage.Impl.Argon2.RISCV64.HPrime
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Length
import VerifiedGarbage.Proof.Argon2.RISCV64.Ops
import VerifiedGarbage.Proof.Framework.Contract

/-! # H′: a bounded public length comparison -/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.HPrime

open VG VG.RISCV64
open VG.RISCV64.Wp (wp_subi)

structure Compared (s t : State) : Prop where
  value : t.gpr .a7 = if (s.gpr .s3).toNat < 65 then 1 else 0
  other : ∀ r, r ≠ .a7 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem compare_ok (s : State) (hb : (s.gpr .s3).toNat < 2 ^ 32) :
    WP isa (.block Impl.Argon2.RISCV64.HPrime.cmpLeft) s (Compared s) := by
  unfold Impl.Argon2.RISCV64.HPrime.cmpLeft
  refine wp_subi (by decide) fun a ha => wp_srl (by decide) fun t ht => WP.block_nil ?_
  refine ⟨?_, fun r hr => (ht.other r hr).trans (ha.other r hr), ht.mem.trans ha.mem,
    ht.rd.trans ha.rd, ht.wr.trans ha.wr, ht.sp.trans ha.sp⟩
  rw [ht.gpr, ha.gpr]
  exact below65 _ hb

theorem Compared.keeps {s t : State} (h : Compared s t) : Keeps s t := by
  refine ⟨fun r hr => h.other r ?_, h.rd, h.wr, h.sp, ?_⟩
  · exact fun h => by subst h; exact absurd hr (by decide)
  · rw [h.mem]; exact Frame.refl _ _

end VG.Proof.Argon2.RISCV64.HPrime
