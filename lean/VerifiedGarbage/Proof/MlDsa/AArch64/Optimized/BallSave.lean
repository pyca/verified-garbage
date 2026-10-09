import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSponge
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallChunk

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample

abbrev parserSaves (p : Addr) : List Region :=
  [⟨p+1800,8⟩,⟨p+1808,8⟩,⟨p+1816,8⟩]

structure Saved (p : Addr) (w9 w10 w11 : BitVec 64) (s : State) : Prop where
  r9 : s.mem.readW (p+1800) 64=w9
  r10 : s.mem.readW (p+1808) 64=w10
  r11 : s.mem.readW (p+1816) 64=w11

theorem save_ok {s : State} {p : Addr} (h25 : s.gpr .x25=p)
    (hin : ∀ d∈[1800,1808,1816],InRegions s.wr (p+BitVec.ofNat 64 d) 8) :
    WP isa (.block [.str .x .x9 .x25 1800,.str .x .x10 .x25 1808,.str .x .x11 .x25 1816]) s fun u =>
      Keep [] s u ∧ Frame (parserSaves p) s.mem u.mem ∧ Saved p (s.gpr .x9) (s.gpr .x10) (s.gpr .x11) u := by
  refine wp_strx (a := p+1800) (by decide) (by rw [h25]; rfl) (hin _ (by simp)) fun s₁ h₁ =>
    wp_strx (a := p+1808) (by decide) (by rw [h₁.gpr,h25]; rfl) (by rw [h₁.wr]; exact hin _ (by simp)) fun s₂ h₂ =>
    wp_strx (a := p+1816) (by decide) (by rw [h₂.gpr,h₁.gpr,h25]; rfl)
      (by rw [h₂.wr,h₁.wr]; exact hin _ (by simp)) fun u hu => wp_nil ?_
  have m : u.mem=((s.mem.writeW (p+1800) (s.gpr .x9)).writeW (p+1808) (s.gpr .x10)).writeW
      (p+1816) (s.gpr .x11) := by rw [hu.mem,h₂.mem,h₁.mem,h₂.gpr,h₁.gpr]
  have sep (a b : Nat) (h : a+8≤b ∨ b+8≤a) (ha : a+8≤2048) (hb : b+8≤2048) :
      Mem.Sep (p+BitVec.ofNat 64 a) 8 (p+BitVec.ofNat 64 b) 8 :=
    Offset.sep p h (by omega) (by omega)
  refine ⟨((h₁.keep.trans h₂.keep).trans hu.keep).mono (by simp),?_,?_,?_,?_⟩
  · rw [m]
    exact (((Frame.refl _ _).writeW (by simp [parserSaves]) _ (Region.contains_self _ _)).writeW
      (by simp [parserSaves]) _ (Region.contains_self _ _)).writeW (by simp [parserSaves]) _ (Region.contains_self _ _)
  · rw [m,Mem.readW_writeW_sep (sep 1800 1816 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 1800 1808 (by omega) (by omega) (by omega)) (by decide),Mem.readW_writeW_self64]
  · rw [m,Mem.readW_writeW_sep (sep 1808 1816 (by omega) (by omega) (by omega)) (by decide),Mem.readW_writeW_self64]
  · rw [m,Mem.readW_writeW_self64]

/-- The exact parser values survive any disjoint scratch/stack call. -/
theorem Saved.keep {p : Addr} {w9 w10 w11 : BitVec 64} {s u : State} {rs : List Region}
    (h : Saved p w9 w10 w11 s) (hf : Frame rs s.mem u.mem)
    (hd : ∀ d∈[1800,1808,1816],∀ r∈rs,(⟨p+BitVec.ofNat 64 d,8⟩ : Region).Disjoint r) :
    Saved p w9 w10 w11 u := by
  have e (d : Nat) (hd' : d∈[1800,1808,1816]) :
      u.mem.readW (p+BitVec.ofNat 64 d) 64=s.mem.readW (p+BitVec.ofNat 64 d) 64 :=
    hf.readW (r := ⟨p+BitVec.ofNat 64 d,8⟩) (Region.contains_self _ _) (hd d hd') (by decide)
  exact ⟨(e 1800 (by simp)).trans h.r9,(e 1808 (by simp)).trans h.r10,(e 1816 (by simp)).trans h.r11⟩
end VG.Proof.MlDsa.AArch64.Optimized.Ball
