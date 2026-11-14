module

import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Kernel
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Concrete
import Mathlib.Tactic.SplitIfs
import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Forward
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Weierstrass.AArch64.Forward.WellFormed`, which only this module used -/

section

/-! A syntactic check that the interpreter over concrete words runs a block:
every instruction decodes, writes a register other than `x0`, uses a valid
operation and an aligned slot inside the scratch area, and reads only
registers (and the carry) that an earlier instruction of the block wrote.
It tracks a register set and a flag, so the kernel checks it in time linear
in the block. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64

/-- Whether an operand the operation may read is defined. -/
noncomputable def useOk (m : RegSet Reg) (use : Bool) (r : Reg) : Bool := !use || m.mem r

/-- One instruction, then the rest (`k`), on the defined registers and carry. -/
noncomputable def wfThen (size : Nat) (s : RegSet Reg × Bool) (i : Instr)
    (k : RegSet Reg × Bool → Bool) : Bool :=
  Option.rec false (fun v => Decoded.rec (motive := fun _ => Bool)
    (fun op d a b c => (!Nat.beq (regKeyK d) 0 && op.valid && useOk s.1 op.useA a &&
        useOk s.1 op.useB b && useOk s.1 op.useC c && useOk s.1 op.useD d && (!op.useCarry || s.2)) &&
      k (s.1.insert d,s.2 || op.flags))
    (fun d off => (!Nat.beq (regKeyK d) 0 && FastEnv.okOff size off) && k (s.1.insert d,s.2))
    (fun r off => (FastEnv.okOff size off && s.1.mem r) && k s) v.val) (decode i)

/-- The check of a block, from the registers and carry `s` defined. -/
noncomputable def wfK (size : Nat) (is : List Instr) (s : RegSet Reg × Bool) : Bool :=
  List.rec (motive := fun _ => RegSet Reg × Bool → Bool) (fun _ => true)
    (fun i _ ih s => wfThen size s i ih) is s

/-- What `s` promises of an environment. -/
def Defined (s : RegSet Reg × Bool) (e : Env CVal) : Prop :=
  (∀ r,r∈s.1 → (e.reg r).isSome) ∧ (s.2=true → e.carry.isSome)

private theorem arg_some {s : RegSet Reg × Bool} {e : Env CVal} (h : Defined s e) {use : Bool} {r : Reg}
    (hu : useOk s.1 use r=true) : ∃ v,arg concDom e use r=some v := by
  unfold useOk at hu
  cases use with
  | false => exact ⟨_,rfl⟩
  | true =>
    simp only [Bool.not_true,Bool.false_or] at hu
    exact Option.isSome_iff_exists.mp (h.1 r hu)

theorem eval_of_wfK {size : Nat} (is : List Instr) :
    ∀ {s : RegSet Reg × Bool} {e : Env CVal},wfK size is s=true → Defined s e →
      ∃ l,eval concDom size is e=some l := by
  induction is with
  | nil => intro s e _ _; exact ⟨e,rfl⟩
  | cons i is ih =>
    intro s e h hd
    change wfThen size s i (wfK size is)=true at h
    unfold wfThen at h
    simp only [eval,step,bind,Option.bind]
    cases hdec : decode i with
    | none => rw [hdec] at h; cases h
    | some v =>
      rw [hdec] at h
      dsimp only
      obtain ⟨v,hv⟩ := v
      cases v with
      | scalar op d a b c =>
        change ((!Nat.beq (regKeyK d) 0 && op.valid && useOk s.1 op.useA a &&
          useOk s.1 op.useB b && useOk s.1 op.useC c && useOk s.1 op.useD d && (!op.useCarry || s.2)) &&
          wfK size is (s.1.insert d,s.2 || op.flags))=true at h
        simp only [Bool.and_eq_true,Bool.not_eq_true',regKeyK_eq,FastEnv.x0_key,decide_eq_false_iff_not] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨hx0,hval⟩,ha⟩,hb⟩,hc⟩,hdd⟩,hcar⟩,hk⟩ := h
        obtain ⟨va,hva⟩ := arg_some hd ha
        obtain ⟨vb,hvb⟩ := arg_some hd hb
        obtain ⟨vc,hvc⟩ := arg_some hd hc
        obtain ⟨vd,hvd⟩ := arg_some hd hdd
        obtain ⟨cf,hcf⟩ : ∃ cf,carryArg concDom e op=some cf := by
          unfold carryArg
          cases hu : op.useCarry with
          | false => exact ⟨_,rfl⟩
          | true =>
            rw [hu] at hcar
            exact Option.isSome_iff_exists.mp (hd.2 (by simpa using hcar))
        let u := op.eval va.1 vb.1 vc.1 vd.1 cf.2
        have hs : decodedStep concDom size e (.scalar op d a b c)=
            some {e.setReg d u with carry:=if op.flags then some u else e.carry} := by
          simp only [decodedStep,hx0,hval,decide_false,Bool.not_true,Bool.or_false,Bool.false_eq_true,
            ite_false,bind,Option.bind,hva,hvb,hvc,hvd,hcf,pure]
          rfl
        rw [hs]
        refine ih hk ⟨fun r hr => ?_,fun hcr => ?_⟩
        · simp only [Env.setReg]
          rw [RegSet.mem_insert] at hr
          split
          · rfl
          · rename_i hne
            exact hd.1 r (hr.resolve_left hne)
        · dsimp only
          split
          · rfl
          · rename_i hf
            simp only [hf,Bool.or_false] at hcr
            exact hd.2 hcr
      | load d off =>
        change ((!Nat.beq (regKeyK d) 0 && FastEnv.okOff size off) && wfK size is (s.1.insert d,s.2))=true at h
        simp only [Bool.and_eq_true,Bool.not_eq_true',regKeyK_eq,FastEnv.x0_key,decide_eq_false_iff_not,
          FastEnv.okOff_eq,decide_eq_true_eq] at h
        obtain ⟨⟨hx0,⟨ho1,ho2⟩,ho3⟩,hk⟩ := h
        have hs : decodedStep concDom size e (.load d off)=some (e.setReg d (e.slot off)) := by
          simp [decodedStep,hx0,ho1,ho2,ho3]
        rw [hs]
        refine ih hk ⟨fun r hr => ?_,hd.2⟩
        simp only [Env.setReg]
        rw [RegSet.mem_insert] at hr
        split
        · rfl
        · rename_i hne
          exact hd.1 r (hr.resolve_left hne)
      | store r off =>
        change ((FastEnv.okOff size off && s.1.mem r) && wfK size is s)=true at h
        simp only [Bool.and_eq_true,FastEnv.okOff_eq,decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨ho1,ho2⟩,ho3⟩,hr⟩,hk⟩ := h
        obtain ⟨y,hy⟩ := Option.isSome_iff_exists.mp (hd.1 r hr)
        have hs : decodedStep concDom size e (.store r off)=some (e.setSlot off y) := by
          simp [decodedStep,ho1,ho2,ho3,hy]
        rw [hs]
        exact ih hk ⟨hd.1,hd.2⟩

end VG.Proof.Weierstrass.AArch64.Forward

end

end


/-! `optimize` is proved correct once, for every block the interpreter over
concrete words runs: the optimized block runs too and leaves the same word in
every slot. A block refines to its optimization when it passes the syntactic
check `wfK` and both blocks' accesses fit the scratch area, all evaluated in
time linear in the block, with no certificate to build or check. -/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Forward
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Impl.Weierstrass.AArch64.Forward

theorem optimize_ok {size : Nat} {is : List Instr} {e l : Env CVal} (h : eval concDom size is e=some l) :
    ∃ r,eval concDom size (optimize is) e=some r ∧ ∀ off,(l.slot off).1=(r.slot off).1 := by
  obtain ⟨r₁,h₁,e₁⟩ := forward_ok h
  obtain ⟨r₂,h₂,e₂⟩ := foldMoves_ok (forward is) ⟨fun _ _ => rfl,fun _ => rfl,rfl⟩ h₁
  obtain ⟨r₃,h₃,e₃⟩ := deadStores_ok h₂
  exact ⟨r₃,h₃,fun off => (e₁.slot off).trans ((e₂.slot off).trans (e₃ off))⟩

/-- `optimized` is `optimize original`, which the interpreter runs, and both
blocks' accesses fit `size` bytes. -/
structure OptChecked (size : Nat) (original optimized : List Instr) : Prop where
  opt : optimized=optimize original
  wf : wfK size original (RegSet.empty,false)=true
  boundLeft : ∀ w∈original.flatMap instrWrites,w.1+w.2≤size
  boundRight : ∀ w∈optimized.flatMap instrWrites,w.1+w.2≤size

theorem OptChecked.refine {size : Nat} {original optimized : List Instr}
    (cert : OptChecked size original optimized) (ha : size%8=0) (hsize : size≤2^64)
    {s : State} {base : Addr} {cap : Nat} (hs : Scr s base cap)
    (hci : ∀ i∈original,instrBound i≤cap) (hcj : ∀ i∈optimized,instrBound i≤cap) {Q : State → Prop}
    (hq : WP isa (.block original) s Q) :
    WP isa (.block optimized) s fun t => ∃ u,Q u ∧ t.mem=u.mem ∧
      KeepRegs (optimized.flatMap instrClob) s t := by
  obtain ⟨l,hl⟩ := eval_of_wfK original cert.wf (e := concEnv s base)
    ⟨fun _ h => absurd h (RegSet.not_mem_empty _),fun h => by cases h⟩
  obtain ⟨r,hr,hsl⟩ := optimize_ok hl
  rw [← cert.opt] at hr
  exact refine_words concDom_sound hs ha hsize (concEnv_rel s base size) hl hr
    (fun off _ _ => hsl off) cert.boundLeft cert.boundRight hci hcj hq

end VG.Proof.Weierstrass.AArch64.Forward
