module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! # The symbol-address prefix preserves candidate bytes and the static table -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Context.keepFrame {g : Geometry} (v : g.Valid) {c : Nat} {s t : State} (C : Context g c s)
    {rs : List Reg} (K : Keeps rs s t) (sp : .esp ∉ rs) {writes : List Region}
    (F : Frame writes s.mem t.mem)
    (candidateFar : ∀ r ∈ writes, g.candidateRegion.Disjoint r)
    (tableFar : ∀ r ∈ writes, g.tableRegion.Disjoint r) : Context g c t := by
  refine ⟨C.stack.keep K sp, ?_, ?_, ?_, ?_⟩
  · intro i bound
    rw [K.2.1, K.2.2]
    exact C.candidateRead i bound
  · intro i bound d mem
    rw [K.2.1, K.2.2]
    exact C.tableRead i bound d mem
  · intro i bound
    have read := F.readW (r := g.tableRegion) (w := 64)
      (Offset.contains_base _ (by omega : 8 * i + 8 ≤ 8192) (by omega)) tableFar (by decide)
    exact read.trans (C.tableWords i bound)
  · rw [← C.candidateValue]
    apply val32_congr
    intro i bound
    apply congrArg BitVec.toNat
    exact F.readW (r := g.candidateRegion) (w := 32)
      (Offset.contains_base _ (by omega) (by have := v.candidateFit; omega)) candidateFar (by decide)

theorem Context.keepSymbol {g : Geometry} (v : g.Valid) {c : Nat} {s t : State} (C : Context g c s)
    {name : String} (R : SymAddrPost name s t)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) : Context g c t := by
  refine C.keepFrame v ⟨R.gpr, R.rd, R.wr⟩ (by decide) R.frame ?_ ?_
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    rw [C.stack.sp]
    exact candidateFar
  · intro r mem
    obtain rfl := List.mem_singleton.mp mem
    rw [C.stack.sp]
    exact tableFar

theorem symbol_stack_word {g : Geometry} {c : Nat} {s t : State} (C : Context g c s)
    {name : String} (R : SymAddrPost name s t) (low : 4 ≤ g.sp.toNat) {d : Nat} (fit : d + 4 ≤ 20) :
    t.mem.readW (off (g.sp.setWidth 64) d) 32 = s.mem.readW (off (g.sp.setWidth 64) d) 32 := by
  apply R.frame.readW (r := g.stackRegion) (Offset.contains_base _ fit (by omega)) ?_ (by decide)
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  rw [C.stack.sp]
  unfold Geometry.stackRegion below
  rw [Taint.sub_setWidth low]
  exact Offset.base_disjoint_below _ (by decide : 20 + 4 ≤ 2 ^ 64)

end VG.Proof.RsaKeyGen.X86.Sieve
