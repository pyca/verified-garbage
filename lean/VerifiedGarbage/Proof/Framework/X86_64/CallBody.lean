module

public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.RelCT

/-! # Calls whose body is verified in its caller's memory regions -/

@[expose] public section
namespace VG.X86_64

theorem WP.callBody {name : String} {body : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa body s.callEntry fun u =>
      u.gpr .rsp = s.gpr .rsp - 8 ∧
      u.mem.readW (s.gpr .rsp - 8) 64 = s.unknowns 0 ∧
      Q (u.setReg .rsp (s.gpr .rsp))) :
    WP isa (.call name body) s Q := by
  obtain ⟨trace, u, he, hsp, hm, hq⟩ := h
  refine ⟨_, _, Exec.call (call_callEntry s) he ?_, hq⟩
  simp only [isa, ret]
  have hr : u.mem.readW (u.gpr .rsp) 64 =
      s.callEntry.mem.readW (s.callEntry.gpr .rsp) 64 := by
    rw [hsp, State.callEntry_rsp, State.callEntry_mem, Mem.readW_writeW_self64]
    exact hm
  rw [ite_eq_left ⟨by simpa using hsp, hr⟩]
  congr 1
  rw [hsp, BitVec.sub_add_cancel]

theorem RelCT.callBody {name : String} {body : Prog isa}
    {P : State → State → Prop} {R : State → State → Prop}
    (h : RelCT isa R body (fun _ _ => True))
    (hpre : ∀ s t, P s t → R s.callEntry t.callEntry)
    (hsp : ∀ s t, P s t → s.gpr .rsp = t.gpr .rsp) :
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
      change [Leak.addr (s.gpr .rsp - 8)] ++ _ ++ [Leak.addr _] =
        [Leak.addr (t.gpr .rsp - 8)] ++ _ ++ [Leak.addr _]
      rw [hb, hrs.1, hrt.1, State.callEntry_rsp, State.callEntry_rsp, hsp s t hp]

end VG.X86_64
