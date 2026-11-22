module

public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Mem

/-! # Calls whose body is verified in its caller's memory regions

A call of an internal function (`Code.call`) whose code is proven as part of
its caller: the body runs from the state the call instruction leaves
(`State.callEntry`), and the return finds the return address where the
call stored it. -/

@[expose] public section
namespace VG.X86

theorem WP.callBody {name : String} {body : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa body s.callEntry fun u =>
      u.gpr .esp = s.gpr .esp - 4 ∧
      u.mem.readW ((s.gpr .esp - 4).setWidth 64) 32 = s.unknowns 0 ∧
      Q (u.setReg .esp (s.gpr .esp))) :
    WP isa (.call name body) s Q := by
  obtain ⟨trace, u, he, hsp, hm, hq⟩ := h
  refine ⟨_, _, Exec.call (call_callEntry s) he ?_, hq⟩
  simp only [isa, ret]
  have hr : u.mem.readW ((u.gpr .esp).setWidth 64) 32 =
      s.callEntry.mem.readW ((s.callEntry.gpr .esp).setWidth 64) 32 := by
    rw [hsp, State.callEntry_esp, State.callEntry_mem, Mem.readW_writeW_self32]
    exact hm
  rw [ite_eq_left ⟨by simpa using hsp, hr⟩]
  congr 1
  rw [hsp, BitVec.sub_add_cancel]

theorem RelCT.callBody {name : String} {body : Prog isa}
    {P : State → State → Prop} {R : State → State → Prop}
    (h : RelCT isa R body (fun _ _ => True))
    (hpre : ∀ s t, P s t → R s.callEntry t.callEntry)
    (hsp : ∀ s t, P s t → s.gpr .esp = t.gpr .esp) :
    RelCT isa P (.call name body) (fun _ _ => True) := by
  intro s t ts tt s' t' hp es et
  cases es with
  | call cs bs rs =>
    cases et with
    | call ct bt rt =>
      have hs := Option.some.inj ((call_callEntry s).symm.trans cs)
      have ht := Option.some.inj ((call_callEntry t).symm.trans ct)
      subst hs
      subst ht
      have hb := (h _ _ _ _ _ _ (hpre s t hp) bs bt).1
      simp only [isa, ret] at rs rt
      split at rs <;> try contradiction
      split at rt <;> try contradiction
      rename_i hrs hrt
      refine ⟨?_, trivial⟩
      change [Leak.addr ((s.gpr .esp - 4).setWidth 64)] ++ _ ++ [Leak.addr _] =
        [Leak.addr ((t.gpr .esp - 4).setWidth 64)] ++ _ ++ [Leak.addr _]
      rw [hb, hrs.1, hrt.1, State.callEntry_esp, State.callEntry_esp, hsp s t hp]

end VG.X86
