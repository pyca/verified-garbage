module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega

/-! Convert bounded workspace writes into a region frame. -/

@[expose] public section
namespace VG.Proof.Mont
open VG

theorem Outs.frame {base : Addr} {size : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (O : Outs base rs m m') (fits : ∀ r∈rs, r.1+r.2≤size) :
    Frame [⟨base,size⟩] m m' := by
  intro x hx
  apply O x
  intro r hr
  have H := hx _ (List.mem_singleton_self _)
  have B := fits r hr
  simp only [Region.Contains,ofs] at H ⊢
  omega

end VG.Proof.Mont
