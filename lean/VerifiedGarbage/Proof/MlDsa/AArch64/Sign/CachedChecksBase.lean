import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedChecksCorrect

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)

structure Roots (p : Params) (S : Nat) (f : Poly) (s : State) : Prop where
  roots : PairedRoots S s
  cache : PolyIs s.mem (pa s t4P) f

theorem Roots.step_layout {p : Params} {S : Nat} {f : Poly} {s t : State}
    {ws : List (Ptr × Nat)} (h : Roots p S f s) (L : Lay S (sgR p) (sgW p) s)
    (hp : PPostB S s t ws) (hy : t.syms=s.syms)
    (hw : ∀w∈ws,inB (sgW p) w.1 w.2=true)
    (hc : keepB (sgR p) (sgW p) ws t4P 1024=true) : Roots p S f t :=
  ⟨h.roots.step_layout L hp hy hw,L.keepPoly hp hc h.cache⟩

theorem keep_nil {p : Params} (hp : Ok3 p) :
    keepB (sgR p) (sgW p) [] t4P 1024=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem keep_zpair {p : Params} {r : Nat} (hp : Ok3 p) (hr : r+1<p.ℓ) :
    keepB (sgR p) (sgW p) (pairedZWrites p r) t4P 1024=true := by
  have hh : ∀r<p.ℓ, keepB (sgR p) (sgW p) (pairedZWrites p r) t4P 1024=true := by
    rcases hp with rfl|rfl|rfl <;> decide
  exact hh r (by omega)

theorem keep_lowpair {p : Params} {i : Nat} (hp : Ok3 p) (hi : i+1<p.k) :
    keepB (sgR p) (sgW p) (pairedLowWrites p i) t4P 1024=true := by
  have hh : ∀i<p.k, keepB (sgR p) (sgW p) (pairedLowWrites p i) t4P 1024=true := by
    rcases hp with rfl|rfl|rfl <;> decide
  exact hh i (by omega)

theorem keep_hintpair {p : Params} {i : Nat} (hp : Ok3 p) (hi : i+1<p.k) :
    keepB (sgR p) (sgW p) (pairedHintWrites i) t4P 1024=true := by
  have hh : ∀i<p.k, keepB (sgR p) (sgW p) (pairedHintWrites i) t4P 1024=true := by
    rcases hp with rfl|rfl|rfl <;> decide
  exact hh i (by omega)

theorem keep_product {p : Params} (hp : Ok3 p) :
    keepB (sgR p) (sgW p) [(t1P,1024),(sc oPS,1024)] t4P 1024=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem keep_z {p : Params} {r : Nat} (hp : Ok3 p) (hr : r<p.ℓ) :
    keepB (sgR p) (sgW p) [(yP p r,1024)] t4P 1024=true := by
  revert r; rcases hp with rfl|rfl|rfl <;> decide

theorem keep_ones {p : Params} (hp : Ok3 p) :
    keepB (sgR p) (sgW p) [(sc oONES,8)] t4P 1024=true := by
  rcases hp with rfl|rfl|rfl <;> decide

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks
