module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombTable
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The standard ABI constants contract supplies the comb's ROM view. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm

theorem tableMem_of_consts {s : State} {K : List (String × List (BitVec 64))} {st : Nat}
    (h : ConstsOk K st s) {name : String} {ws : List (BitVec 64)} (hc : (name,ws)∈K) :
    TableMem s (State.addr (s.syms name)) ws := by
  have hr : (⟨symAddr s name,8*ws.length⟩ : Region)∈constRegs K s :=
    List.mem_map_of_mem (f := fun c => (⟨symAddr s c.1,8*c.2.length⟩ : Region)) hc
  have rd : (⟨symAddr s name,8*ws.length⟩ : Region)∈s.rd :=
    List.mem_of_mem_drop (h.1 ▸ hr)
  refine ⟨?_,⟨_,List.mem_append_left _ rd,Region.contains_self _ _⟩,?_⟩
  · rw [VG.Proof.X25519.Arm.addr_toNat]; exact h.fit hc
  · exact fun i hi => h.2.1 _ hc i hi

theorem table_disjoint_of_consts {s : State} {K : List (String × List (BitVec 64))} {st : Nat}
    (h : ConstsOk K st s) {name : String} {ws : List (BitVec 64)} (hc : (name,ws)∈K)
    {r : Region} (hr : r∈s.wr) : Region.Disjoint ⟨State.addr (s.syms name),8*ws.length⟩ r :=
  (h.2.2.1 _ (List.mem_map_of_mem (f := fun c => (⟨symAddr s c.1,8*c.2.length⟩ : Region)) hc)).2.1 r hr

end VG.Proof.Weierstrass.Arm.TComb
