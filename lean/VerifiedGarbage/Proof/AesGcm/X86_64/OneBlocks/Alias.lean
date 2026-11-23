module

public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.TCB.X86_64.Residue
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks
public import VerifiedGarbage.Impl.AesGcm.X86_64

/-! # Passing an equal destination to the two-pointer seal block helper

The caller sets r10 to the source before calling the shared leaf. Its proof
can use the in-place contract for the leaf preceded by the same move. These
two executions have the same state and the same leakage trace. -/

@[expose] public section
namespace VG.Proof.AesGcm.X86_64.OneBlocks
open VG.X86_64

def aliasDst : Prog isa := .block [.mov .r10 (.reg .r8)]

def aliasState (s : State) : State := s.setReg .r10 (s.gpr .r8)

theorem alias_run (s : State) : execBlock isa [.mov .r10 (.reg .r8)] s=some (aliasState s,[]) := rfl

theorem alias_exec (s : State) : Exec isa aliasDst s [] (aliasState s) := .block (alias_run s)

theorem alias_exec_iff {s t : State} {tr : List Leak} : Exec isa aliasDst s tr t ↔ t=aliasState s ∧ tr=[] := by
  constructor
  · intro e; cases e with
    | block a => rw [alias_run] at a; cases a; exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩; exact alias_exec s

theorem alias_entry (s : State) : (aliasState s).callEntry=aliasState s.callEntry := by
  simp only [aliasState,State.callEntry,State.setReg,State.mk.injEq,reduceCtorEq,ite_false,
    and_true]
  funext r
  cases r <;> rfl

theorem alias_call {name : String} {body : Prog isa} {s t : State} {tr : List Leak} :
    Exec isa (.call name (.seq aliasDst body)) s tr t ↔
      Exec isa (.seq aliasDst (.call name body)) s tr t := by
  constructor
  · intro e
    cases e with
    | call hcall w ret =>
      cases w with
      | seq m b =>
        rw [call_callEntry] at hcall
        cases hcall
        obtain ⟨rfl,rfl⟩ := alias_exec_iff.mp m
        rw [← alias_entry] at b
        have c := Exec.call (name := name) (call_callEntry (aliasState s)) b ret
        have e := Exec.seq (alias_exec s) c
        simp only [List.nil_append] at e ⊢
        change Exec isa _ s (([s.gpr .rsp - 8].map Leak.addr ++ _) ++ _) _ at e
        exact e
  · intro e
    cases e with
    | seq m c =>
      cases c with
      | call hcall b ret =>
        obtain ⟨rfl,rfl⟩ := alias_exec_iff.mp m
        rw [call_callEntry] at hcall
        cases hcall
        rw [alias_entry] at b
        exact .call (call_callEntry _) (.seq (alias_exec _) b) ret

theorem callBlocks_iff (f : Impl.AesGcm.X86_64.Fn) {s t : State} {tr : List Leak} :
    Exec isa (.call f.name f.code) s tr t ↔ Exec isa f.callBlocks s tr t := by
  unfold Impl.AesGcm.X86_64.Fn.callBlocks
  split
  · rename_i body h
    rw [h]
    exact alias_call
  · exact Iff.rfl

theorem place_exec {c : Prog isa} {s t : State} {tr : List Leak} (target : String)
    (e : Exec isa c s tr t) : Exec isa (Impl.AesGcm.X86_64.placeSealArgs target c) s tr t := by
  induction e with
  | block h => exact .block h
  | seq _ _ a b => exact .seq a b
  | iteT x _ a => exact .iteT x a
  | iteF x _ a => exact .iteF x a
  | loopExit _ x a => exact .loopExit a x
  | loopNext _ x _ a b => exact .loopNext a x b
  | call h b r _ =>
    rw [Impl.AesGcm.X86_64.placeSealArgs]
    split
    · exact (callBlocks_iff _).mp (.call h b r)
    · exact .call h b r
  | frame i _ j b => exact .frame i b j
  | icall h c b r _ => exact .icall h c b r
  | icallNext h n b _ => exact .icallNext h n b

theorem place_verified {k : Contract isa} {bits : Nat} {p : Prog isa} (target : String)
    (h : VerifiedScrubbed VG.X86_64.target p k bits) :
    VerifiedScrubbed VG.X86_64.target (Impl.AesGcm.X86_64.placeSealArgs target p) k bits := by
  obtain ⟨⟨ok,ct,nonempty⟩,scrub⟩ := h
  have old {s t : State} {tr : List Leak} (pre : k.pre s)
      (e : Exec isa (Impl.AesGcm.X86_64.placeSealArgs target p) s tr t) : Exec isa p s tr t := by
    obtain ⟨tr',t',e',_,_⟩ := ok s pre
    obtain ⟨rfl,rfl⟩ := Exec.det e (place_exec target e')
    exact e'
  refine ⟨⟨?_,?_,nonempty⟩,?_⟩
  · intro s pre
    obtain ⟨tr,t,e,abi,post⟩ := ok s pre
    exact ⟨tr,t,place_exec target e,abi,post⟩
  · intro a b t u x y ha hb hp ea eb
    exact ct _ _ _ _ _ _ ha hb hp (old ha ea) (old hb eb)
  · change NoResidue _ k bits
    intro a b t u x y ha hb hp outside unknown ea eb
    exact scrub _ _ _ _ _ _ ha hb hp outside unknown (old ha ea) (old hb eb)

theorem place_instrs (target : String) (p : Prog isa) :
    instrs (Impl.AesGcm.X86_64.placeSealArgs target p)=instrs p := by
  induction p with
  | block => rfl
  | seq a b ha hb => simp only [Impl.AesGcm.X86_64.placeSealArgs,instrs,ha,hb]
  | ite c a b ha hb => simp only [Impl.AesGcm.X86_64.placeSealArgs,instrs,ha,hb]
  | loop b c h => exact h
  | call n b _ =>
    rw [Impl.AesGcm.X86_64.placeSealArgs]
    split
    · unfold Impl.AesGcm.X86_64.Fn.callBlocks
      split
      · rename_i body h; change b=_ at h; rw [h]; rfl
      · rfl
    · rfl
  | frame i b j h => simp only [Impl.AesGcm.X86_64.placeSealArgs,instrs,h]
  | icall => rfl

theorem place_spSafe (target : String) {p : Prog isa} (h : SpSafe p) :
    SpSafe (Impl.AesGcm.X86_64.placeSealArgs target p) :=
  fun i hi => h i ((place_instrs target p) ▸ hi)

end VG.Proof.AesGcm.X86_64.OneBlocks
