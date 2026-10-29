module

public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load

import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Framework.Block
/-! # Duplicate the shared 32-byte seed into the paired sponge -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Noise/Word.lean`, which only this module imported.
section

section

namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq)

/-- Duplicate one seed word into the two interleaved sponge states. -/
theorem seedWord_ok {s : State} {p a : Addr} {sb j : Nat} (hj : j < 4)
    (hoff : sb + 8*j < 32768) (halign : (sb + 8*j) % 8 = 0)
    (hp : s.gpr .x19 = p) (ha : s.gpr .x28 + BitVec.ofNat 64 (sb+8*j) = a)
    (hin : InRegions (s.rd++s.wr) a 8)
    (hw : InRegions s.wr (wordAddr p j) 16) :
    WP isa (.block ([.ldr .x .x6 .x28 (sb+8*j), .vop (.dup .d2 .v0 .x6),
      .strq .v0 .x19 (16*j)] : List Instr)) s fun t => RegKeep [.x6] s t ∧
      t.mem = s.mem.write (wordAddr p j) 16 (ofVDwords (s.mem.readW a 64) (s.mem.readW a 64)) := by
  refine wp_ldr ⟨halign,hoff⟩ ha hin fun s1 h1 => ?_
  refine wp_vop (d := .v0) rfl fun s2 h2 => ?_
  refine wp_strq (a := wordAddr p j) (by omega)
    (by rw [h2.gpr,h1.other .x19 (by decide),hp]; rfl)
    (by rw [h2.wr,h1.wr]; exact hw) fun t h3 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact ((RegKeep.upd h1).trans (RegKeep.vupd h2)).trans (RegKeep.vmem h3) |>.mono (by simp)
  · rw [h3.mem,h2.v,h1.gpr,h2.mem,h1.mem]

end VG.Proof.MlKem.AArch64.Noise
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem seedWords_ok {s : State} {p a : Addr} {sb : Nat}
    (hoff : sb + 32 ≤ 32768) (halign : sb % 8 = 0)
    (hp : s.gpr .x19 = p) (ha : s.gpr .x28 + BitVec.ofNat 64 sb = a)
    (hin : ∀ j < 4, InRegions (s.rd++s.wr) (a+BitVec.ofNat 64 (8*j)) 8)
    (hw : ∀ j < 4, InRegions s.wr (wordAddr p j) 16)
    (hsep : (Region.mk a 32).Disjoint ⟨p,64⟩) :
    WP isa (.block ((List.range 4).flatMap fun j =>
      [.ldr .x .x6 .x28 (sb+8*j), .vop (.dup .d2 .v0 .x6), .strq .v0 .x19 (16*j)])) s fun t =>
      RegKeep [.x6] s t ∧ Frame [⟨p,64⟩] s.mem t.mem ∧
      ∀ j < 4, t.mem.read (wordAddr p j) 16 =
        ofVDwords (s.mem.readW (a+BitVec.ofNat 64 (8*j)) 64)
          (s.mem.readW (a+BitVec.ofNat 64 (8*j)) 64) := by
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x6] s t ∧ Frame [⟨p,64⟩] s.mem t.mem ∧
      ∀ j < k, t.mem.read (wordAddr p j) 16 =
        ofVDwords (s.mem.readW (a+BitVec.ofNat 64 (8*j)) 64)
          (s.mem.readW (a+BitVec.ofNat 64 (8*j)) 64))
    (fun k t hk ⟨ht,hf,hvals⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (seedWord_ok (a := a+BitVec.ofNat 64 (8*k)) hk (by omega) (by omega)
    ((ht.gpr .x19 (by simp)).trans hp)
    (by rw [ht.gpr .x28 (by simp),← ha,BitVec.add_assoc,← BitVec.ofNat_add])
    (by rw [ht.rd,ht.wr]; exact hin k hk)
    (by rw [ht.wr]; exact hw k hk)) fun u ⟨hu,hm⟩ => ?_
  have hs : t.mem.readW (a+BitVec.ofNat 64 (8*k)) 64 =
      s.mem.readW (a+BitVec.ofNat 64 (8*k)) 64 := by
    exact hf.read (r := ⟨a,32⟩) (Offset.contains_base a (d := 8*k) (n := 8) (k := 32) (by omega) (by omega))
      (by intro r hr; rw [List.mem_singleton.mp hr]; exact hsep) (by decide)
  refine ⟨(ht.trans hu).mono (by simp),?_,?_⟩
  · rw [hm]
    exact hf.write (List.mem_singleton_self _) _ (Offset.contains_base p (by omega) (by omega))
  · intro j hj
    rw [hm,hs]
    by_cases he : j = k
    · subst j; rw [read_write16]
    · have hd : Mem.Sep (wordAddr p j) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*j) (e := 16*k) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hd (by decide)]
      exact hvals j (by omega)

end VG.Proof.MlKem.AArch64.Noise
