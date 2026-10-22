module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! Convert bounded workspace writes into a region frame. -/

@[expose] public section
namespace VG.Proof.Mont
open VG

theorem Outs.enclose {base : Addr} {d n : Nat} {rs : List (Nat × Nat)} {m m' : Mem}
    (O : Outs base rs m m') (fits : ∀ r ∈ rs, d ≤ r.1 ∧ r.1 + r.2 ≤ d + n) :
    Outside base d n m m' := by
  intro x hx
  apply O x
  intro r hr
  have bound := fits r hr
  rcases hx with hx | hx <;> omega

theorem Outside.frameAt {base : Addr} {d n : Nat} {m m' : Mem}
    (O : Outside base d n m m') (bound : d + n < 2 ^ 64) :
    Frame [⟨off base d, n⟩] m m' := by
  intro x hx
  apply O x
  by_cases lower : ofs base x < d
  · exact .inl lower
  · right
    by_cases upper : d + n ≤ ofs base x
    · exact upper
    · exfalso
      have inside := Offset.contains base (d := ofs base x) (n := 1) (e := d) (k := n)
        (by omega) (by omega) bound
      have address : off base (ofs base x) = x := by
        simp only [off, ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rw [BitVec.add_comm, BitVec.sub_add_cancel]
      change (⟨off base d, n⟩ : Region).Contains (off base (ofs base x)) 1 at inside
      rw [address] at inside
      exact hx _ (List.mem_singleton_self _) inside

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
