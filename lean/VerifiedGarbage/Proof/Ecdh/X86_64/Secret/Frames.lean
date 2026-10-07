import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Prep

/-! Memory ranges written by secret multiplication, including its larger cached table. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64.Window5
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64

def windowW (c : Cfg) : List (Nat × Nat) :=
  (writes (cfg c)).map (·,8*c.n)++[(c.sl TMP,8*c.n)]

theorem windowW_eq {c : Cfg} (hn : c.n=4) : windowW c=windowW p256 := by
  simp only [windowW,writes,localWrites,winOther,tableSlots,consecutiveFields,
    cfg,Cfg.winCfg,Cfg.rcbSlots,Cfg.pt,Cfg.winTbl,Cfg.sl,hn]
  rfl

theorem fixedOk_windowW {c : Cfg} (hn : c.n=4) : FixedOk c (windowW c) := by
  rw [windowW_eq hn]
  change ∀ w∈windowW p256,(w.1=c.sl TMP ∧ w.2=8*c.n) ∨ c.sl 12≤w.1
  simp only [Cfg.sl,hn]
  decide +kernel

/-- Numbered slots still read by finalization are disjoint from the window's writes. -/
theorem apart_windowW {c : Cfg} (hn : c.n=4) {i : Nat} (hi : i∈[D,FLAG]) :
    ∀ w∈windowW c,c.sl i+8*c.n≤w.1 ∨ w.1+w.2≤c.sl i := by
  rw [windowW_eq hn]
  simp only [Cfg.sl,hn]
  have h : ∀ i∈[D,FLAG],∀ w∈windowW p256,
      slot 4 i+32≤w.1 ∨ w.1+w.2≤slot 4 i := by decide +kernel
  exact h i hi

theorem bits_apart_windowW {c : Cfg} (hn : c.n=4) {j t : Nat} (hj : j<3) (ht : t<64*c.n) :
    ∀ w∈windowW c,bitsAt c.n j+t+1≤w.1 ∨ w.1+w.2≤bitsAt c.n j+t := by
  rw [windowW_eq hn]
  rw [hn] at ht ⊢
  have h : ∀ j<3,∀ w∈windowW p256,
      bitsAt 4 j+256≤w.1 ∨ w.1+w.2≤bitsAt 4 j := by decide +kernel
  intro w hw
  rcases h j hj w hw with hh|hh
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end VG.Proof.Ecdh.X86_64.Secret
