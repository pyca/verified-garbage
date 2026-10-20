module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass1
public import VerifiedGarbage.Proof.Framework.Covers

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem.AArch64

/-- Internal transform entry requirements with an immutable table. -/
structure Input (s : State) (symbol : String) (H : List Nat) : Prop extends Ntt16.Pre s where
  table : ∀ j < 64, s.mem.readW (s.syms symbol + BitVec.ofNat 64 (8*j)) 64 = hw4 H j
  readable : Covers [⟨s.syms symbol,512⟩] (s.rd++s.wr)
  apartOutput : (polyRegion (fP s)).Disjoint ⟨s.syms symbol,512⟩
  apartScratch : (polyRegion (sP s)).Disjoint ⟨s.syms symbol,512⟩

theorem Input.read {s : State} {symbol : String} {H : List Nat} (h : Input s symbol H)
    {o : Nat} (ho : o+16≤512) : InRegions (s.rd++s.wr) (s.syms symbol+BitVec.ofNat 64 o) 16 :=
  h.readable _ _ (in_regions (List.mem_singleton_self _) (contains_off ho (by decide)))

theorem Input.table_frame {s : State} {symbol : String} {H : List Nat} (h : Input s symbol H)
    {m : Mem} (hf : Frame [polyRegion (sP s)] s.mem m) :
    ∀ j < 64, m.readW (s.syms symbol+BitVec.ofNat 64 (8*j)) 64 = hw4 H j := by
  intro j hj
  rw [hf.readW (r:=⟨s.syms symbol,512⟩) (contains_off (by omega) (by decide))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.apartScratch.symm) (by decide)]
  exact h.table j hj

theorem wp_movS {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d=s.gpr n → s'.syms=s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.MlKem.AArch64.mov d n :: is)) s Q := by
  refine WP.cons (s':=s.write .x d (s.gpr n)) ?_ (k _ (only_write _ _ _ _) (write_x_gpr _ _ _) rfl)
  simp only [Impl.MlKem.AArch64.mov,exec,State.read,Size.bits,BitVec.setWidth_eq,
    show 0<4096 by decide,ite_true,BitVec.add_zero]

end VG.Proof.MlKem.AArch64.Ntt16.Readonly
