module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Tactic.ToDual
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReadyMemory

/-! # Prepared modulus data survives temporary use of EDI by search controllers -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

/-- The reusable setup is memory state; a controller may temporarily use EDI
for its own counters before restoring the arithmetic base. -/
def PrimePrepared (G : PrimeConfig) (s : State) : Prop :=
  ∃ t, PrimeReady G t ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .esp = s.gpr .esp

theorem PrimeReady.prepared {G : PrimeConfig} {s : State} (R : PrimeReady G s) : PrimePrepared G s :=
  ⟨s, R, rfl, rfl, rfl, rfl⟩

theorem PrimePrepared.restore {G : PrimeConfig} {s : State} (R : PrimePrepared G s)
    (di : (s.gpr .edi).setWidth 64 = G.base) : PrimeReady G s := by
  obtain ⟨t, Rt, mem, rd, wr, sp⟩ := R
  have S : Scr s G.base G.size := ⟨di, wr ▸ Rt.context.scr.wr, Rt.context.scr.nowrap, sp ▸ Rt.context.scr.stk⟩
  have C : Context G.n G.modulus G.base G.size s := ⟨S, Rt.context.size_le,
    by rw [← mem]; exact Rt.context.modulus, Rt.context.gt_one,
    by rw [← mem]; exact Rt.context.inverse⟩
  exact ⟨C, by rw [← mem]; exact Rt.one, by rw [← mem]; exact Rt.r2,
    by rw [← mem]; exact Rt.exponent, by rw [← mem]; exact Rt.twos,
    by rw [← mem]; exact Rt.tape, by rw [← mem]; exact Rt.tapeLen,
    by rw [← mem]; exact Rt.witness,
    by intro i hi; rw [← rd, ← wr]; exact Rt.tapeRead i hi,
    by intro i hi; rw [← rd, ← wr]; exact Rt.witnessRead i hi,
    by intro i hi; rw [← rd, ← wr]; exact Rt.witnessReadByte i hi,
    by intro i hi; rw [← wr]; exact Rt.witnessWrite i hi⟩

theorem PrimePrepared.keep {G : PrimeConfig} {s t : State} {regs : List Reg}
    (R : PrimePrepared G s)
    (O : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem)
    (K : Keeps regs s t) (sp : .esp ∉ regs) : PrimePrepared G t := by
  obtain ⟨u, Ru, mem, rd, wr, usp⟩ := R
  let v : State := {u with mem := t.mem}
  have Kv : Keeps [] u v := ⟨fun _ _ => rfl, rfl, rfl⟩
  have Ov : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len u.mem v.mem := by
    change PrimeFrame G.base G.n (G.witness.setWidth 64) G.len u.mem t.mem
    rw [mem]; exact O
  exact ⟨v, Ru.keep Ov Kv (by decide) (by decide), rfl,
    rd.trans K.2.1.symm, wr.trans K.2.2.symm, usp.trans (K.1 _ sp).symm⟩

theorem PrimePrepared.frame {G : PrimeConfig} {s t : State} {regs : List Reg} {rs : List Region}
    (R : PrimePrepared G s) (O : Frame rs s.mem t.mem)
    (apart : ∀ r ∈ rs, (⟨G.base, G.size⟩ : Region).Disjoint r)
    (K : Keeps regs s t) (sp : .esp ∉ regs) : PrimePrepared G t := by
  obtain ⟨u, Ru, mem, rd, wr, usp⟩ := R
  let v : State := {u with mem := t.mem}
  have Kv : Keeps [] u v := ⟨fun _ _ => rfl, rfl, rfl⟩
  have Ov : Frame rs u.mem v.mem := by change Frame rs u.mem t.mem; rw [mem]; exact O
  exact ⟨v, Ru.frame Ov apart Kv (by decide) (by decide), rfl,
    rd.trans K.2.1.symm, wr.trans K.2.2.symm, usp.trans (K.1 _ sp).symm⟩
end VG.Proof.Dsa.X86.Generation
