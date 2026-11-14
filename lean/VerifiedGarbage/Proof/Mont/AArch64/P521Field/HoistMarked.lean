module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.Hoist

/-! Selectively hoist loads whose destination registers are never reused. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.AArch64.Interleave

def hoistMarked (pick : Instr → Bool) (xb : Reg) : List Instr → Option (List Instr × List Instr)
  | [] => some ([],[])
  | i::is =>
    match hoistMarked pick xb is with
    | none => none
    | some (ls,rs) =>
      if pick i then some (i::ls,rs)
      else if independent xb ls [i] = some true then some (ls,i::rs)
      else none

theorem hoistMarked_run {pick : Instr → Bool} {xb : Reg} {code ls rs : List Instr}
    (h : hoistMarked pick xb code = some (ls,rs)) :
    ∀ s, runBlock isa code s = runBlock isa (ls++rs) s := by
  induction code generalizing ls rs with
  | nil =>
    simp only [hoistMarked,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    intro s
    rfl
  | cons i code ih =>
    cases ht : hoistMarked pick xb code with
    | none => simp only [hoistMarked,ht] at h; cases h
    | some p =>
      rcases p with ⟨l,r⟩
      have he : runBlock isa code = runBlock isa (l++r) := funext (ih ht)
      simp only [hoistMarked,ht] at h
      by_cases hi : pick i = true
      · simp only [hi,ite_true,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨hL,hR⟩
        subst ls
        subst rs
        intro s
        change (exec i s).bind (runBlock isa code) = (exec i s).bind (runBlock isa (l++r))
        rw [he]
      · simp only [hi] at h
        by_cases hc : independent xb l [i] = some true
        · simp only [hc,ite_true] at h
          have hpair := Option.some.inj h
          have hL : l = ls := congrArg Prod.fst hpair
          have hR : i::r = rs := congrArg Prod.snd hpair
          rw [←hL,←hR]
          have hind : Indeps xb l [i] := indeps_of_check hc
          have comm : ∀ s, (exec i s).bind (runBlock isa l) =
              (runBlock isa l s).bind (exec i) :=
            comm_block (fun x hx => hind x hx i List.mem_cons_self)
          have app : runBlock isa (l++r) =
              fun s => (runBlock isa l s).bind (runBlock isa r) :=
            funext (runBlock_append l r)
          intro s
          change (exec i s).bind (runBlock isa code) = _
          rw [he,app,←Option.bind_assoc,comm s,Option.bind_assoc,runBlock_append]
          rfl
        · simp only [hc,ite_false] at h
          cases h

theorem WP.hoistMarked {pick : Instr → Bool} {xb : Reg} {code ls rs : List Instr}
    (h : hoistMarked pick xb code = some (ls,rs)) {s : State} {Q : State → Prop}
    (hq : VG.WP isa (.block (ls++rs)) s Q) : VG.WP isa (.block code) s Q := by
  obtain ⟨t,ht,hq⟩ := runBlock_of_WP hq
  exact VG.WP.of_runBlock ⟨t,(hoistMarked_run h s).trans ht,hq⟩

end VG.Proof.Mont.AArch64.P521Field
