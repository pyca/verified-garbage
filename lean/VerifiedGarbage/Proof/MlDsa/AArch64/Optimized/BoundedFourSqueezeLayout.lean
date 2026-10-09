import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeLoop

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def squeezeCfg (b : Addr) (off : Nat) : SqueezeCfg :=
 ⟨b,b+400#64,b+BitVec.ofNat 64 (840+off),b+BitVec.ofNat 64 (1384+off),
  b+BitVec.ofNat 64 (1928+off),b+BitVec.ofNat 64 (2472+off)⟩

theorem squeezeCfg_out (b : Addr) (off : Nat) {i : Nat} (hi : i<4) :
    (squeezeCfg b off).out i=b+BitVec.ofNat 64 (840+544*i+off) := by
  rcases (show i=0∨i=1∨i=2∨i=3 by omega) with rfl|rfl|rfl|rfl <;> rfl

theorem squeezeCfg_at (b : Addr) (off : Nat) {i : Nat} (hi : i<4) (j : Nat) :
    (squeezeCfg b off).at i j=b+BitVec.ofNat 64 (840+544*i+off+136*j) := by
  rw [SqueezeCfg.at,squeezeCfg_out b off hi,BitVec.add_assoc,←BitVec.ofNat_add]

theorem pairLayout_offsets {s : State} {b : Addr} {d a e : Nat}
    (hd : d+400≤8192) (ha : a+136≤e) (he : e+136≤8192) (hda : d+400≤a)
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    PairLayout s (b+BitVec.ofNat 64 d) (b+BitVec.ofNat 64 a) (b+BitVec.ofNat 64 e) := by
  constructor
  · intro i hi
    obtain ⟨r,hr,hh⟩:=hw (d+16*i) 16 (by omega)
    refine ⟨r,List.mem_append_right _ hr,?_⟩
    simpa only [wordAddr,Offset.add_add] using hh
  · intro i hi
    simpa only [wordAddr,Offset.add_add] using hw (d+16*i) 16 (by omega)
  · intro i hi
    simpa only [outAddr,Offset.add_add] using hw (a+8*i) 8 (by omega)
  · intro i hi
    simpa only [outAddr,Offset.add_add] using hw (e+8*i) 8 (by omega)
  · exact Offset.disjoint b (Or.inl ha) (by omega) (by omega)
  · exact Offset.disjoint b (Or.inl hda) (by omega) (by omega)
  · exact Offset.disjoint b (Or.inl (by omega)) (by omega) (by omega)

theorem squeezeLayout_left {s : State} {b : Addr} {off j : Nat} (ho : off≤272) (hj : j<2)
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    PairLayout s (squeezeCfg b off).p ((squeezeCfg b off).at 0 j) ((squeezeCfg b off).at 1 j) := by
  rw [squeezeCfg_at _ _ (by decide),squeezeCfg_at _ _ (by decide)]
  have hp : (squeezeCfg b off).p=b+BitVec.ofNat 64 0 := by simp [squeezeCfg]
  rw [hp]
  exact pairLayout_offsets (by decide) (by omega) (by omega) (by omega) hw

theorem squeezeLayout_right {s : State} {b : Addr} {off j : Nat} (ho : off≤272) (hj : j<2)
    (hw : ∀o n,o+n≤8192→InRegions s.wr (b+BitVec.ofNat 64 o) n) :
    PairLayout s (squeezeCfg b off).q ((squeezeCfg b off).at 2 j) ((squeezeCfg b off).at 3 j) := by
  rw [squeezeCfg_at _ _ (by decide),squeezeCfg_at _ _ (by decide)]
  change PairLayout s (b+BitVec.ofNat 64 400) _ _
  exact pairLayout_offsets (by decide) (by omega) (by omega) (by omega) hw

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
