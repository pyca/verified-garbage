module
public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Frame
public import VerifiedGarbage.Impl.Argon2.PPC64LE.HPrime

import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Length
import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-! # H′: a bounded public length comparison -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (wp_subi wp_lsr)

structure Compared (s t : State) : Prop where
  value : t.gpr .r10 = if (s.gpr .r30).toNat < 65 then 1 else 0
  other : ∀ r, r ≠ .r10 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem compare_ok (s : State) (hb : (s.gpr .r30).toNat < 2 ^ 32) :
    WP isa (.block Impl.Argon2.PPC64LE.HPrime.cmpLeft) s (Compared s) := by
  unfold Impl.Argon2.PPC64LE.HPrime.cmpLeft
  refine wp_subi (by decide) fun a ha => wp_lsr (by decide) fun t ht => WP.block_nil ?_
  refine ⟨?_, fun r hr => (ht.other r hr).trans (ha.other r hr), ht.mem.trans ha.mem,
    ht.rd.trans ha.rd, ht.wr.trans ha.wr, ht.sp.trans ha.sp⟩
  rw [ht.gpr, ha.gpr]
  exact below65 _ hb

theorem Compared.keeps {s t : State} (h : Compared s t) : Keeps s t := by
  refine ⟨fun r hr => h.other r ?_, h.rd, h.wr, h.sp, ?_⟩
  · exact fun h => by subst h; exact absurd hr (by decide)
  · rw [h.mem]; exact Frame.refl _ _

end VG.Proof.Argon2.PPC64LE.HPrime
