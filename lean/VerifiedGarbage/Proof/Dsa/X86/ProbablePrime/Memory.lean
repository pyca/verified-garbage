module

public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Environment
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Spec.Rsa.Contract

/-! # The tape, the table and the candidate outlive every stage -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

/-- The regions a stage may write: the workspace and the stack below the
saved registers. -/
def WorkFrame (E : Environment) (m m' : Mem) : Prop := Frame [E.workspaceRegion, below E.p 136] m m'

theorem WorkFrame.refl (E : Environment) (m : Mem) : WorkFrame E m m := fun _ _ => rfl

theorem WorkFrame.trans {E : Environment} {a b c : Mem} (A : WorkFrame E a b) (B : WorkFrame E b c) :
    WorkFrame E a c := fun x out => (B x out).trans (A x out)

/-- The regions the test may write. -/
def MutableFrame (E : Environment) (m m' : Mem) : Prop :=
  Frame [E.workspaceRegion, below E.p 136, E.usedRegion] m m'

theorem MutableFrame.trans {E : Environment} {a b c : Mem} (A : MutableFrame E a b) (B : MutableFrame E b c) :
    MutableFrame E a c := fun x out => (B x out).trans (A x out)

theorem WorkFrame.mutable {E : Environment} {m m' : Mem} (F : WorkFrame E m m') : MutableFrame E m m' :=
  F.mono (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self)

theorem MutableFrame.of_used {E : Environment} {m m' : Mem} (F : Frame [E.usedRegion] m m') : MutableFrame E m m' :=
  F.mono (by
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem Environment.Valid.randFar {E : Environment} (v : E.Valid) :
    ∀ r ∈ [E.workspaceRegion, below E.p 136], E.randRegion.Disjoint r := by
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact v.randWorkspace
  · exact v.stackFar _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem Environment.Valid.tableFar {E : Environment} (v : E.Valid) :
    ∀ r ∈ [E.workspaceRegion, below E.p 136], E.tableRegion.Disjoint r := by
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact v.tableWorkspace
  · exact v.stackFar _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem Tail.candidate {E : Environment} (v : E.Valid) {m m' : Mem} (T : Tail E m m') :
    E.candidate m' = E.candidate m := by
  unfold Environment.candidate Spec.Rsa.bytesAt
  congr 1
  apply List.map_congr_left
  intro i hi
  have index := List.mem_range.mp hi
  have room := v.room
  rw [off, Offset.add_add]
  exact T _ (by omega) (by omega)

theorem Memory.keep {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s t : State}
    (M : Memory E c entropy s) {regs : List Reg} (K : Keeps regs s t) (F : WorkFrame E s.mem t.mem)
    (T : Tail E s.mem t.mem)
    (symbol : t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) :
    Memory E c entropy t := by
  refine ⟨M.usedWrite.of_keeps K, ?_, ?_, ?_, ?_, symbol.trans M.symbol, (T.candidate v).trans M.candidate⟩
  · rw [K.2.1, K.2.2]; exact M.randRead
  · rw [VG.Proof.RsaKeyGen.frame_bytesAt F v.randFar (by have := v.randLengthFit; omega)]
    exact M.entropy
  · rw [K.2.1, K.2.2]; exact M.tableRead
  · intro i index
    rw [F.readW (r := E.tableRegion)
      (Offset.contains_base _ (by change 8 * i + 8 ≤ 8192; omega) (by omega)) v.tableFar (by decide)]
    exact M.table i index

end VG.Proof.Dsa.X86.ProbablePrime
