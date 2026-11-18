module

public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store

/-! ### `MlKem.AArch64.Noise.Words`, which the modules that import this one used -/

section

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
  refine WP.mono (seedWord_ok (a := a+BitVec.ofNat 64 (8*k)) hk (by omega_using [hoff, hk]) (by omega_using [halign])
    ((ht.gpr .x19 (by simp)).trans hp)
    (by rw [ht.gpr .x28 (by simp),← ha,BitVec.add_assoc,← BitVec.ofNat_add])
    (by rw [ht.rd,ht.wr]; exact hin k hk)
    (by rw [ht.wr]; exact hw k hk)) fun u ⟨hu,hm⟩ => ?_
  have hs : t.mem.readW (a+BitVec.ofNat 64 (8*k)) 64 =
      s.mem.readW (a+BitVec.ofNat 64 (8*k)) 64 := by
    exact hf.read (r := ⟨a,32⟩) (Offset.contains_base a (d := 8*k) (n := 8) (k := 32) (by omega_using [hk]) (by omega_using [hk]))
      (by intro r hr; rw [List.mem_singleton.mp hr]; exact hsep) (by decide)
  refine ⟨(ht.trans hu).mono (by simp),?_,?_⟩
  · rw [hm]
    exact hf.write (List.mem_singleton_self _) _ (Offset.contains_base p (by omega_using [hk]) (by omega_using [hk]))
  · intro j hj
    rw [hm,hs]
    by_cases he : j = k
    · subst j; rw [read_write16]
    · have hd : Mem.Sep (wordAddr p j) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*j) (e := 16*k) (n := 16) (k := 16) (by omega_using [he]) (by omega_using [hk, hj]) (by omega_using [hk])
      rw [Mem.read_write_sep hd (by decide)]
      exact hvals j (by omega_using [hj, he])

end VG.Proof.MlKem.AArch64.Noise

end

end

/-! ### `MlKem.AArch64.Noise.Zero`, which the modules that import this one used -/

section

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq VMem)
/-- Initialize the 25 interleaved state words used by paired SHAKE. -/
def zeroStates : List Instr :=
 [.vop (.movi0 .v0)] ++ (List.range 25).map fun i => .strq .v0 .x19 (16*i)

def statesR (p : Addr) : Region := ⟨p,400⟩

theorem zeros_ok {s : State} {p : Addr} (hp : s.gpr .x19 = p)
    (hw : ∀ i < 25, InRegions s.wr (wordAddr p i) 16) :
    WP isa (.block zeroStates) s fun t => RegKeep [] s t ∧
      Frame [statesR p] s.mem t.mem ∧ ∀ i < 25, t.mem.read (wordAddr p i) 16 = 0 := by
  unfold zeroStates
  rw [List.cons_append,WP.block_cons_iff]
  refine ⟨s.setV .v0 0,rfl,?_⟩
  have hz := VG.Proof.MlKem.AArch64.vupd_setV s .v0 0
  rw [List.nil_append,List.map_eq_flatMap]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => RegKeep [] s t ∧ t.v .v0 = 0 ∧ Frame [statesR p] s.mem t.mem ∧
      ∀ i < k, t.mem.read (wordAddr p i) 16 = 0)
    (fun k t hk ⟨ht,hv,hf,hvals⟩ => ?_) 25 (Nat.le_refl _) (s.setV .v0 0)
    ⟨RegKeep.vupd hz,hz.v,by rw [hz.mem]; exact Frame.refl _ _,
      fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
    fun t ⟨ht,_,hf,hvals⟩ => ⟨ht,hf,hvals⟩
  refine wp_strq (a := wordAddr p k) (by omega_using [hk])
    (by rw [ht.gpr .x19 (by simp),hp]; rfl)
    (by rw [ht.wr]; exact hw k hk) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact (ht.trans (RegKeep.vmem hu)).mono (by simp)
  · rw [hu.v]; exact hv
  · rw [hu.mem]
    exact hf.write (List.mem_singleton_self _) _ (Offset.contains_base p (by omega_using [hk]) (by omega_using [hk]))
  · intro i hi
    rw [hu.mem,hv]
    by_cases he : i = k
    · subst i; rw [read_write16]
    · have hsep : Mem.Sep (wordAddr p i) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*i) (e := 16*k) (n := 16) (k := 16) (by omega_using [he]) (by omega_using [hk, hi]) (by omega_using [hk])
      rw [Mem.read_write_sep hsep (by decide)]
      exact hvals i (by omega_using [hi, he])
end VG.Proof.MlKem.AArch64.Noise

end

end

/-! # Insert noise nonces and SHAKE256 padding in an interleaved state -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_movz wp_vop wp_strq)

def tailWords (n : Nat) : List Instr :=
 [.movz .x .x6 (BitVec.ofNat 16 (n+0x1f00)) 0,
  .movz .x .x7 (BitVec.ofNat 16 (n+1+0x1f00)) 0,
  .vop (.dup .d2 .v0 .x6), .vop (.ins .d2 .v0 1 .x7), .strq .v0 .x19 64]

theorem tailWords_ok {s : State} {p : Addr} {n : Nat}
    (hp : s.gpr .x19 = p) (hw : InRegions s.wr (p+64) 16) :
    WP isa (.block (tailWords n)) s fun t => RegKeep [.x6,.x7] s t ∧
      t.mem = s.mem.write (p+64) 16 (ofVDwords
        ((BitVec.ofNat 16 (n+0x1f00)).setWidth 64)
        ((BitVec.ofNat 16 (n+1+0x1f00)).setWidth 64)) := by
  unfold tailWords
  refine wp_movz fun s1 h1 e1 => wp_movz fun s2 h2 e2 => ?_
  refine wp_vop (d := .v0) rfl fun s3 h3 => wp_vop (d := .v0) rfl fun s4 h4 => ?_
  refine wp_strq (a := p+64) (by decide)
    (by rw [h4.gpr,h3.gpr,h2.get .x19,h1.get .x19,hp]; rfl)
    (by rw [h4.wr,h3.wr,h2.wr,h1.wr]; exact hw) fun t h5 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact ((((RegKeep.only h1).trans (RegKeep.only h2)).trans (RegKeep.vupd h3)).trans
      (RegKeep.vupd h4)).trans (RegKeep.vmem h5) |>.mono (by simp)
  · rw [h5.mem,h4.v,h3.v,h3.gpr,e2,h2.get .x6,e1,
      h4.mem,h3.mem,h2.mem,h1.mem,setLane_pair_hi]

/-- Insert the final SHAKE padding bit in either rate's last lane. -/
theorem padWord_ok {s : State} {p : Addr} {j : Nat} (hj : j < 256)
    (hp : s.gpr .x19 = p) (hw : InRegions s.wr (wordAddr p j) 16) :
    WP isa (.block ([.movz .x .x6 0x8000 3, .vop (.dup .d2 .v0 .x6),
      .strq .v0 .x19 (16*j)] : List Instr)) s fun t => RegKeep [.x6] s t ∧
      t.mem = s.mem.write (wordAddr p j) 16
        (ofVDwords 0x8000000000000000 0x8000000000000000) := by
  refine VG.Proof.MlKem.AArch64.wp_x (d := .x6) (v := 0x8000000000000000) (by rfl)
    fun s1 h1 e1 => ?_
  refine wp_vop (d := .v0) rfl fun s2 h2 => ?_
  refine wp_strq (a := wordAddr p j) (by omega_using [hj])
    (by rw [h2.gpr,h1.get .x19,hp]; rfl)
    (by rw [h2.wr,h1.wr]; exact hw) fun t h3 => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · exact ((RegKeep.only h1).trans (RegKeep.vupd h2)).trans (RegKeep.vmem h3) |>.mono (by simp)
  · rw [h3.mem,h2.v,e1,h2.mem,h1.mem]

end VG.Proof.MlKem.AArch64.Noise
