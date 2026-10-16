module

public import VerifiedGarbage.Impl.AArch64Pair
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.AArch64.Target

/-!
# Paired loads and stores run as the loads and stores they replace

A `fuse`d pair runs to the state the two instructions run to (or faults where
they do) and leaks the same addresses (`fuse_execBlock`), so a block paired by
`pairUp` runs exactly as the block (`execBlock_pairUp`), code paired by
`pairCode` has the executions of the code (`exec_pairCode`), and what is
proven of the code holds of the paired code (`Verified.pairCode`).
-/

@[expose] public section

namespace VG.Proof.AArch64Pair

open VG VG.AArch64 VG.Impl.AArch64Pair

theorem load_write (s : State) (sz : Size) (r : Reg) (v : BitVec sz.bits) (a : Addr) (k : Nat) :
    (s.write sz r v).load a k = s.load a k := rfl

theorem store_gpr {s s' : State} {a : Addr} {k : Nat} {v : BitVec (8 * k)} (h : s.store a k v = some s') :
    s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold State.store at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl⟩
  · cases h

theorem fuse_execBlock {i j p : Instr} (h : fuse i j = some p) (tl : List Instr) (s : State) :
    execBlock isa (p :: tl) s = execBlock isa (i :: j :: tl) s := by
  unfold fuse at h
  split at h
  · rename_i a n o b n' o'
    split at h
    · rename_i hc
      obtain ⟨hn', ho', hab, han, h8, h504⟩ := hc
      subst n' o'
      cases h
      have hA : s.gpr n + BitVec.ofNat 64 (o + 8) = s.gpr n + BitVec.ofNat 64 o + 8 := by
        rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl
      simp only [execBlock, isa, exec, addr, Size.bytes, Size.bits, hab, h8, h504,
        show o < 4096 * 8 by omega, show (o + 8) % 8 = 0 by omega, show o + 8 < 4096 * 8 by omega,
        ne_eq, not_false_eq_true, and_self, ite_true, Option.bind_some]
      rcases h1 : s.load (s.gpr n + BitVec.ofNat 64 o) 8 with _ | v₁
      · simp only [Option.bind_none, Option.map_none]
      · have hn : (s.write .x a (BitVec.setWidth 64 v₁)).gpr n = s.gpr n := by
          simp only [State.write, Ne.symm han, ite_false]
        simp only [Option.bind_some, Option.map_some, hn, hA]
        rcases h2 : s.load (s.gpr n + BitVec.ofNat 64 o + 8) 8 with _ | v₂
        · simp only [load_write, h2, Option.map_none]
        · simp only [load_write, h2, Option.map_some, Option.map_map, Function.comp_def, addrs, hn, hA,
            List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    · cases h
  · rename_i a n o b n' o'
    split at h
    · rename_i hc
      obtain ⟨hn', ho', h8, h504⟩ := hc
      subst n' o'
      cases h
      have hA : s.gpr n + BitVec.ofNat 64 (o + 8) = s.gpr n + BitVec.ofNat 64 o + 8 := by
        rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl
      simp only [execBlock, isa, exec, addr, Size.bytes, h8, h504,
        show o < 4096 * 8 by omega, show (o + 8) % 8 = 0 by omega, show o + 8 < 4096 * 8 by omega,
        and_self, ite_true, Option.bind_some]
      rcases h1 : s.store (s.gpr n + BitVec.ofNat 64 o) 8 ((s.read .x a).setWidth 64) with _ | s₁
      · simp only [Option.bind_none]
      · obtain ⟨g1, -, -⟩ := store_gpr h1
        have hr : s₁.read .x b = s.read .x b := by simp only [State.read, g1]
        simp only [Option.bind_some, g1, hA, hr]
        rcases h2 : s₁.store (s.gpr n + BitVec.ofNat 64 o + 8) 8 ((s.read .x b).setWidth 64) with _ | s₂
        · rfl
        · simp only [addrs, g1, hA, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
            Option.map_map, Function.comp_def]
    · cases h
  · cases h

theorem execBlock_cons_congr (i : Instr) {l l' : List Instr}
    (h : ∀ s, execBlock isa l s = execBlock isa l' s) (s : State) :
    execBlock isa (i :: l) s = execBlock isa (i :: l') s := by
  simp only [execBlock, h]

/-- A paired block runs exactly as the block. -/
theorem execBlock_pairUp : ∀ (l : List Instr) (s : State), execBlock isa (pairUp l) s = execBlock isa l s
  | [], _ => by simp only [pairUp]
  | [_], _ => by simp only [pairUp]
  | i :: j :: rest, s => by
    simp only [pairUp]
    split
    · rename_i p hp
      rw [fuse_execBlock hp]
      exact execBlock_cons_congr i (execBlock_cons_congr j (execBlock_pairUp rest)) s
    · exact execBlock_cons_congr i (execBlock_pairUp (j :: rest)) s
termination_by l => l.length

/-- The code's executions are executions of the paired code. -/
theorem exec_pairCode {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    Exec isa (pairCode c) s t s' := by
  induction h with
  | block hb => exact .block (by rw [execBlock_pairUp]; exact hb)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteT hc _ ih => exact .iteT hc ih
  | iteF hc _ ih => exact .iteF hc ih
  | loopExit _ hc ih => exact .loopExit ih hc
  | loopNext _ hc _ ih₁ ih₂ => exact .loopNext ih₁ hc ih₂
  | call hc hb hr => exact .call hc hb hr
  | frame hp _ hq ih => exact .frame hp ih hq

/-- The paired code's executions are executions of the code. -/
theorem exec_of_pairCode {c : Prog isa} {s s' : State} {t : List Leak}
    (h : Exec isa (pairCode c) s t s') : Exec isa c s t s' := by
  generalize hc : pairCode c = c' at h
  induction h generalizing c with
  | block hb =>
    cases c <;> simp only [pairCode, reduceCtorEq] at hc
    cases hc
    exact .block (by rw [← execBlock_pairUp]; exact hb)
  | seq _ _ ih₁ ih₂ =>
    cases c <;> simp only [pairCode, reduceCtorEq, Code.seq.injEq] at hc
    exact .seq (ih₁ hc.1) (ih₂ hc.2)
  | iteT hc' _ ih =>
    cases c <;> simp only [pairCode, reduceCtorEq, Code.ite.injEq] at hc
    obtain ⟨rfl, ht, -⟩ := hc
    exact .iteT hc' (ih ht)
  | iteF hc' _ ih =>
    cases c <;> simp only [pairCode, reduceCtorEq, Code.ite.injEq] at hc
    obtain ⟨rfl, -, he⟩ := hc
    exact .iteF hc' (ih he)
  | loopExit _ hc' ih =>
    cases c <;> simp only [pairCode, reduceCtorEq, Code.loop.injEq] at hc
    obtain ⟨hb, rfl⟩ := hc
    exact .loopExit (ih hb) hc'
  | loopNext _ hc' _ ih₁ ih₂ =>
    cases c <;> simp only [pairCode, reduceCtorEq, Code.loop.injEq] at hc
    obtain ⟨hb, rfl⟩ := hc
    exact .loopNext (ih₁ hb) hc' (ih₂ (by simp only [pairCode, hb]))
  | call hc' hb hr =>
    cases c <;> simp only [pairCode, reduceCtorEq, Code.call.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact .call hc' hb hr
  | frame hp _ hq ih =>
    cases c <;> simp only [pairCode, reduceCtorEq, Code.frame.injEq] at hc
    obtain ⟨rfl, hb, rfl⟩ := hc
    exact .frame hp (ih hb) hq

/-- What is proven of code holds of the paired code. -/
theorem Verified.pairCode {c : Prog isa} {k : Contract isa} (h : Verified AArch64.target c k) :
    Verified AArch64.target (Impl.AArch64Pair.pairCode c) k := by
  obtain ⟨hr, hct, hsat⟩ := h
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
    hct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp (exec_of_pairCode e₁) (exec_of_pairCode e₂), hsat⟩
  obtain ⟨t, s', he, ha, hk⟩ := hr s hs
  exact ⟨t, s', exec_pairCode he, ha, hk⟩

end VG.Proof.AArch64Pair
