module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTextS
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTextSCT
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.Call
/-!
# AES-GCM on x86-64: `stream_encrypt` and `stream_decrypt`, clearing by path

Untrusted: everything here is checked by Lean. `streamEncryptS` and
`streamDecryptS` (the additional data padded in the state) verified as
`streamEncrypt` and `streamDecrypt` are, for the whole-blocks functions `B`
of a key context of either kind (`streamEncryptSB_framed`,
`streamEncryptSPrepared16_framed`). Over callees that clear the registers
before they return (`GcmImpl.wrapC`, `BlkFn.wrapC`), and with that clearing
then moved out of each call (`hoist`, which changes no run), that is the
code that clears the registers only on the paths that call
(`streamEncryptClr`): `streamEncryptClrB_framed`, `streamEncryptClr16_framed`.

`clrAfter v` touches neither memory nor the stack pointer
(`execBlock_clrAfter`). So a call whose body ends with it runs as the call
of the rest of the body followed by it (`exec_swap`), with the same trace:
`hoist` changes no run of the code (`exec_hoist`), and so neither its
contract (`Verified.hoist`) nor what it leaves.
-/

-- separate module: its one importer, `Instances`, is rebuilt whenever a proof of AES-GCM on x86-64 changes; these proofs need no re-checking then

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.X86_64

open VG.Impl.AesGcm.X86_64 VG.Impl.Scrub.X86_64 VG.X86_64.Scrub

/-- What `clrAfter v` leaves. -/
def clrState (v : VecLevel) (s : State) : State := clearedG scratchRegs (clearedV v xregs s)

@[simp] theorem clrState_mem (v : VecLevel) (s : State) : (clrState v s).mem = s.mem := rfl
@[simp] theorem clrState_rd (v : VecLevel) (s : State) : (clrState v s).rd = s.rd := rfl
@[simp] theorem clrState_wr (v : VecLevel) (s : State) : (clrState v s).wr = s.wr := rfl
@[simp] theorem clrState_mxcsr (v : VecLevel) (s : State) : (clrState v s).mxcsr = s.mxcsr := rfl
@[simp] theorem clrState_unknowns (v : VecLevel) (s : State) : (clrState v s).unknowns = s.unknowns := rfl

theorem clrState_gpr (v : VecLevel) (s : State) {r : Reg} (hr : r ∉ scratchRegs) :
    (clrState v s).gpr r = s.gpr r := by
  simp [clrState, clearedG, clearedV, hr]

theorem clrState_gpr_scratch (v : VecLevel) (s : State) {r : Reg} (hr : r ∈ scratchRegs) :
    (clrState v s).gpr r = 0 := by
  simp [clrState, clearedG, hr]

theorem clrState_xmm (v : VecLevel) (s : State) (x : XReg) : (clrState v s).xmm x = 0 := by
  simp [clrState, clearedG, clearedV, mem_xregs]

theorem clrState_setRsp (v : VecLevel) (s : State) (a : Addr) :
    clrState v (s.setReg .rsp a) = (clrState v s).setReg .rsp a := by
  simp only [clrState, clearedG, clearedV, State.setReg, State.mk.injEq, and_true]
  funext r
  by_cases h : r = .rsp
  · subst h; simp [scratchRegs]
  · simp [h]

theorem execBlock_app {M : ISA} (l₁ l₂ : List M.Instr) (s : M.State) :
    execBlock M (l₁ ++ l₂) s = (execBlock M l₁ s).bind fun p =>
      (execBlock M l₂ p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction l₁ generalizing s with
  | nil => simp [execBlock]
  | cons i is ih =>
    simp only [List.cons_append, execBlock]
    split
    · rfl
    · rw [ih]
      cases execBlock M is _ with
      | none => rfl
      | some p => simp [Function.comp_def, List.append_assoc]

theorem execBlock_clrAfter (v : VecLevel) (s : State) :
    execBlock isa (clrAfter v) s = some (clrState v s, []) := by
  rw [clrAfter, execBlock_app, clearVec, execBlock_vecs]
  simp only [Option.bind_some]
  rw [execBlock_gprs scratchRegs (by decide)]
  rfl

theorem ret_clrState (v : VecLevel) (s₁ s₂ : State) :
    isa.ret s₁ (clrState v s₂) = (isa.ret s₁ s₂).map (clrState v) := by
  have hr : (clrState v s₂).gpr .rsp = s₂.gpr .rsp := clrState_gpr v s₂ (by decide)
  simp only [isa, ret, hr, clrState_mem]
  split
  · simp only [Option.map_some, clrState_setRsp]
  · rfl

/-- A call whose body ends with `clrAfter v` runs as the call of the rest
of the body followed by `clrAfter v`. -/
theorem exec_swap (v : VecLevel) (n : String) (b : Prog isa) {s u : State} {t : List Leak} :
    Exec isa (.call n (.seq b (.block (clrAfter v)))) s t u ↔
      Exec isa (.seq (.call n b) (.block (clrAfter v))) s t u := by
  constructor
  · intro h
    cases h with
    | call hc hb hr =>
      cases hb with
      | seq ha hk =>
        cases hk with
        | block hkb =>
          rw [execBlock_clrAfter] at hkb
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hkb.symm)
          rw [ret_clrState] at hr
          obtain ⟨u', hr', rfl⟩ := Option.map_eq_some_iff.mp hr
          have e := Exec.seq (Exec.call (name := n) hc ha hr') (Exec.block (execBlock_clrAfter v u'))
          have hsp : ∀ w : State, (clrState v w).gpr .rsp = w.gpr .rsp := fun w => clrState_gpr v w (by decide)
          simp only [isa, List.append_nil, hsp] at e ⊢
          exact e
  · intro h
    cases h with
    | seq ha hk =>
      cases ha with
      | call hc hb hr =>
        cases hk with
        | block hkb =>
          rw [execBlock_clrAfter] at hkb
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hkb.symm)
          have hr' := (ret_clrState v _ _).trans (congrArg (Option.map (clrState v)) hr)
          rw [Option.map_some] at hr'
          have e := Exec.call (name := n) hc (Exec.seq hb (Exec.block (execBlock_clrAfter v _))) hr'
          have hsp : ∀ w : State, (clrState v w).gpr .rsp = w.gpr .rsp := fun w => clrState_gpr v w (by decide)
          simp only [isa, List.append_nil, hsp] at e ⊢
          exact e

theorem exec_hoistCall (v : VecLevel) (n : String) (b : Prog isa) {s u : State} {t : List Leak} :
    Exec isa (hoistCall (clrAfter v) n b) s t u ↔ Exec isa (.call n b) s t u := by
  unfold hoistCall
  split
  · rename_i b' k'
    split
    · rename_i hk; subst hk; exact (exec_swap v n b').symm
    · exact Iff.rfl
  · exact Iff.rfl

theorem exec_loop_of {b b' : Prog isa} {c : Cond} (h : ∀ s t u, Exec isa b' s t u → Exec isa b s t u)
    {s u : State} {t : List Leak} (e : Exec isa (.loop b' c) s t u) : Exec isa (.loop b c) s t u := by
  generalize hp : Code.loop b' c = p at e
  induction e with
  | loopExit hb hc => cases hp; exact .loopExit (h _ _ _ hb) hc
  | loopNext hb hc _ _ ih => cases hp; exact .loopNext (h _ _ _ hb) hc (ih rfl)
  | _ => cases hp

/-- Code with the same runs as `b`, looped. -/
theorem exec_loop_congr {b b' : Prog isa} {c : Cond} (h : ∀ s t u, Exec isa b' s t u ↔ Exec isa b s t u)
    {s u : State} {t : List Leak} : Exec isa (.loop b' c) s t u ↔ Exec isa (.loop b c) s t u :=
  ⟨exec_loop_of fun _ _ _ => (h _ _ _).mp, exec_loop_of fun _ _ _ => (h _ _ _).mpr⟩

/-- `hoist` changes no run. -/
theorem exec_hoist (v : VecLevel) : ∀ (c : Prog isa) (s : State) (t : List Leak) (u : State),
    Exec isa (hoist (clrAfter v) c) s t u ↔ Exec isa c s t u
  | .block _, _, _, _ => Iff.rfl
  | .seq a b, s, t, u => by
    have ha := exec_hoist v a
    have hb := exec_hoist v b
    constructor
    · intro e; cases e with | seq e₁ e₂ => exact .seq ((ha _ _ _).mp e₁) ((hb _ _ _).mp e₂)
    · intro e; cases e with | seq e₁ e₂ => exact .seq ((ha _ _ _).mpr e₁) ((hb _ _ _).mpr e₂)
  | .ite c a b, s, t, u => by
    have ha := exec_hoist v a
    have hb := exec_hoist v b
    constructor
    · intro e
      cases e with
      | iteT hc e => exact .iteT hc ((ha _ _ _).mp e)
      | iteF hc e => exact .iteF hc ((hb _ _ _).mp e)
    · intro e
      cases e with
      | iteT hc e => exact .iteT hc ((ha _ _ _).mpr e)
      | iteF hc e => exact .iteF hc ((hb _ _ _).mpr e)
  | .loop b c, s, t, u => exec_loop_congr (exec_hoist v b)
  | .call n b, s, t, u => exec_hoistCall v n b
  | .frame i b j, s, t, u => by
    have hb := exec_hoist v b
    constructor
    · intro e; cases e with | frame h₁ e h₂ => exact .frame h₁ ((hb _ _ _).mp e) h₂
    · intro e; cases e with | frame h₁ e h₂ => exact .frame h₁ ((hb _ _ _).mpr e) h₂
  | .icall .., _, _, _ => Iff.rfl

theorem Verified.hoist (v : VecLevel) {c : Prog isa} {k : Contract isa} (h : Verified target c k) :
    Verified target (hoist (clrAfter v) c) k := by
  obtain ⟨hc, hct, hs⟩ := h
  refine ⟨fun s hp => ?_, fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp e₁ e₂ => ?_, hs⟩
  · obtain ⟨t, u, e, ha, hq⟩ := hc s hp
    exact ⟨t, u, (exec_hoist v c s t u).mpr e, ha, hq⟩
  · exact hct s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ((exec_hoist v c _ _ _).mp e₁) ((exec_hoist v c _ _ _).mp e₂)

/-! ## What the checks of code see of `hoist` -/

theorem hoist_all (v : VecLevel) (p : Instr → Bool) : ∀ c : Prog isa,
    (hoist (clrAfter v) c).all p = c.all p
  | .block _ => rfl
  | .seq a b => by simp only [hoist, Code.all, hoist_all v p a, hoist_all v p b]
  | .ite _ a b => by simp only [hoist, Code.all, hoist_all v p a, hoist_all v p b]
  | .loop b _ => by simp only [hoist, Code.all, hoist_all v p b]
  | .call n b => by
    simp only [hoist, hoistCall]
    split
    · split
      · rename_i hk; subst hk; simp only [Code.all]
      · rfl
    · rfl
  | .frame _ b _ => by simp only [hoist, Code.all, hoist_all v p b]
  | .icall .. => rfl

theorem hoist_allInstrs (v : VecLevel) (p : Instr → Bool) : ∀ c : Prog isa,
    (hoist (clrAfter v) c).allInstrs p = c.allInstrs p
  | .block _ => rfl
  | .seq a b => by simp only [hoist, Code.allInstrs, hoist_allInstrs v p a, hoist_allInstrs v p b]
  | .ite _ a b => by simp only [hoist, Code.allInstrs, hoist_allInstrs v p a, hoist_allInstrs v p b]
  | .loop b _ => by simp only [hoist, Code.allInstrs, hoist_allInstrs v p b]
  | .call n b => by
    simp only [hoist, hoistCall]
    split
    · split
      · rename_i hk; subst hk; simp only [Code.allInstrs]
      · rfl
    · rfl
  | .frame _ b _ => by simp only [hoist, Code.allInstrs, hoist_allInstrs v p b]
  | .icall .. => rfl

theorem hoist_x86_64Depth (v : VecLevel) : ∀ c : Prog isa,
    (hoist (clrAfter v) c).x86_64Depth = c.x86_64Depth
  | .block _ => rfl
  | .seq a b => by simp only [hoist, Code.x86_64Depth, hoist_x86_64Depth v a, hoist_x86_64Depth v b]
  | .ite _ a b => by simp only [hoist, Code.x86_64Depth, hoist_x86_64Depth v a, hoist_x86_64Depth v b]
  | .loop b _ => by simp only [hoist, Code.x86_64Depth, hoist_x86_64Depth v b]
  | .call n b => by
    simp only [hoist, hoistCall]
    split
    · split
      · rename_i hk; subst hk; simp only [Code.x86_64Depth, Nat.max_zero]
      · rfl
    · rfl
  | .frame _ b _ => by simp only [hoist, Code.x86_64Depth, hoist_x86_64Depth v b]
  | .icall .. => rfl

/-! ## Code that clears the registers before it returns -/

theorem exec_wrap (v : VecLevel) {c : Prog isa} {s u : State} {t : List Leak} (e : Exec isa c s t u) :
    Exec isa (.seq c (.block (clrAfter v))) s t (clrState v u) := by
  simpa using Exec.seq e (Exec.block (execBlock_clrAfter v u))

theorem exec_wrap_inv (v : VecLevel) {c : Prog isa} {s u : State} {t : List Leak}
    (e : Exec isa (.seq c (.block (clrAfter v))) s t u) : ∃ u', Exec isa c s t u' ∧ u = clrState v u' := by
  cases e with
  | seq a b =>
    cases b with
    | block h =>
      rw [execBlock_clrAfter] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h.symm)
      exact ⟨_, by simpa using a, rfl⟩

theorem abiPreserved_clr (v : VecLevel) {s u : State} (h : abiPreserved s u) : abiPreserved s (clrState v u) :=
  ⟨fun r hr => by rw [clrState_gpr v u (by revert hr; revert r; decide)]; exact h.1 r hr, h.2.1, h.2.2⟩

/-- Correctness, for a postcondition on the memory alone. -/
theorem wrap_ok (v : VecLevel) {c : Prog isa} {pre : State → Prop} {post : State → State → Prop}
    (hpost : ∀ s u, post s u → post s (clrState v u))
    (h : ∀ s, pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ post s s') :
    ∀ s, pre s → ∃ t s', Exec isa (.seq c (.block (clrAfter v))) s t s' ∧ abiPreserved s s' ∧ post s s' :=
  fun s hs =>
    let ⟨t, u, e, ha, hq⟩ := h s hs
    ⟨t, _, exec_wrap v e, abiPreserved_clr v ha, hpost s u hq⟩

theorem wrap_ct (v : VecLevel) {c : Prog isa} {pre : State → Prop} {pub : State → State → Prop}
    (h : ConstantTime isa pre pub c) : ConstantTime isa pre pub (.seq c (.block (clrAfter v))) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp e₁ e₂
  obtain ⟨_, a₁, -⟩ := exec_wrap_inv v e₁
  obtain ⟨_, a₂, -⟩ := exec_wrap_inv v e₂
  exact h s₁ s₂ t₁ t₂ _ _ h₁ h₂ hp a₁ a₂

theorem clrAfter_nosp (v : VecLevel) : ∀ i ∈ clrAfter v, Taint.clobbers i .rsp = false := by
  cases v <;> decide

theorem wrap_nosp (v : VecLevel) {c : Prog isa} (h : NoSp c) : NoSp (.seq c (.block (clrAfter v))) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact h i hi
  · exact clrAfter_nosp v i hi

theorem wrap_allInstrs (v : VecLevel) {p : Instr → Bool} (hp : (Code.block (clrAfter v) : Prog isa).allInstrs p = true)
    {c : Prog isa} (h : c.allInstrs p = true) : (Code.seq c (.block (clrAfter v)) : Prog isa).allInstrs p = true := by
  simp only [Code.allInstrs] at hp ⊢; rw [h, Bool.true_and]; exact hp

theorem wrap_all (v : VecLevel) {p : Instr → Bool} (hp : (clrAfter v).all p = true)
    {c : Prog isa} (h : c.all p = true) : (Code.seq c (.block (clrAfter v)) : Prog isa).all p = true := by
  simp only [Code.all, h, hp, Bool.true_and]

theorem clrAfter_mx (v : VecLevel) : (Code.block (clrAfter v) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases v <;> rfl

theorem clrAfter_sp (v : VecLevel) : (clrAfter v).all (fun i => !isa.writesSp i) = true := by
  cases v <;> rfl

end VG.X86_64

namespace VG.Proof.Aes.X86_64

open VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.Scrub.X86_64

/-- `c`, clearing the registers before it returns (`clrAfter v`). -/
def ctr32Wrap (v : VecLevel) (c : Impl.Aes.X86_64.Ctr32) : Impl.Aes.X86_64.Ctr32 :=
  { c with code := .seq c.code (.block (clrAfter v)) }

def Ctr32Free.wrapC (v : VecLevel) {c : Impl.Aes.X86_64.Ctr32} (f : Ctr32Free c) : Ctr32Free (ctr32Wrap v c) where
  ok := wrap_ok v (fun _ _ h => h) f.ok
  ct := wrap_ct v f.ct

def Ctr32Small.wrapC (v : VecLevel) {c : Impl.Aes.X86_64.Ctr32} (f : Ctr32Small c) : Ctr32Small (ctr32Wrap v c) where
  ok := wrap_ok v (fun _ _ h => h) f.ok
  ct := wrap_ct v f.ct
  off := f.off

/-- `c`, its `vg_aes_ctr32` clearing the registers before it returns. -/
def Ctr32Impl.wrapC (v : VecLevel) (c : Ctr32Impl) : Ctr32Impl :=
  { c with
    callee := ctr32Wrap v c.callee
    depth := by simp only [ctr32Wrap, Code.depth, c.depth]; rfl
    ok := wrap_ok v (fun _ _ h => h) c.ok
    ct := wrap_ct v c.ct
    nosp := wrap_nosp v c.nosp
    mxcsr := wrap_allInstrs v (clrAfter_mx v) c.mxcsr
    spSafe := wrap_all v (clrAfter_sp v) c.spSafe
    noStack := by simp only [ctr32Wrap, Code.x86_64Depth, c.noStack]; rfl
    free := c.free.map (·.wrapC v)
    small := c.small.map (·.wrapC v)
    scr := fun h => c.scr (by cases hs : c.small <;> simp_all)
    gcmInitRes := none
    cmacFinishRes := none }

end VG.Proof.Aes.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.Scrub.X86_64

def GhashFree.wrapC (v : VecLevel) {c : Prog isa} (f : GhashFree c) : GhashFree (.seq c (.block (clrAfter v))) where
  ok := wrap_ok v (fun _ _ h => h) f.ok
  ct := wrap_ct v f.ct

/-- `g`, clearing the registers before it returns. -/
def GhashImpl.wrapC (v : VecLevel) (g : GhashImpl) : GhashImpl :=
  { g with
    fn := g.fn.wrapC (clrAfter v)
    depth := by simp only [Fn.wrapC, Code.depth, g.depth]; rfl
    noStack := by simp only [Fn.wrapC, Code.x86_64Depth, g.noStack]; rfl
    ok := wrap_ok v (fun _ _ h => h) g.ok
    ct := wrap_ct v g.ct
    nosp := wrap_nosp v g.nosp
    mxcsr := wrap_allInstrs v (clrAfter_mx v) g.mxcsr
    spSafe := wrap_all v (clrAfter_sp v) g.spSafe
    free := g.free.map (·.wrapC v) }

/-- `i`, its `vg_aes_ctr32` and `vg_ghash` clearing the registers before they return. -/
def GcmImpl.wrapC (v : VecLevel) (i : GcmImpl) : GcmImpl :=
  { i with ctr := i.ctr.wrapC v, gh := i.gh.wrapC v }

open Gcm.X86_64.Stitch (CtxMode) in
/-- `B`, clearing the registers before it returns. -/
def BlkFn.wrapC (v : VecLevel) {M : CtxMode} (B : BlkFn M) : BlkFn M where
  enc := B.enc.wrapC (clrAfter v)
  dec := B.dec.wrapC (clrAfter v)
  encOk := wrap_ok v (fun _ _ h => h) B.encOk
  decOk := wrap_ok v (fun _ _ h => h) B.decOk
  encCt := wrap_ct v B.encCt
  decCt := wrap_ct v B.decCt
  encNosp := wrap_nosp v B.encNosp
  decNosp := wrap_nosp v B.decNosp
  encDepth := by simp only [Fn.wrapC, Code.depth, B.encDepth]; rfl
  decDepth := by simp only [Fn.wrapC, Code.depth, B.decDepth]; rfl
  encMx := wrap_allInstrs v (clrAfter_mx v) B.encMx
  decMx := wrap_allInstrs v (clrAfter_mx v) B.decMx
  encSp := wrap_all v (clrAfter_sp v) B.encSp
  decSp := wrap_all v (clrAfter_sp v) B.decSp
  encXd := by simp only [Fn.wrapC, Code.x86_64Depth, Nat.max_le]; exact ⟨B.encXd, Nat.zero_le _⟩
  decXd := by simp only [Fn.wrapC, Code.x86_64Depth, Nat.max_le]; exact ⟨B.decXd, Nat.zero_le _⟩

open Gcm.X86_64.Stitch (CtxMode) in
/-- The callees of `i.wrapC v` with `B.wrapC v`: those of `i` with `B`, each
clearing the registers before it returns. -/
theorem withBlk_wrapC (v : VecLevel) (i : GcmImpl) {M : CtxMode} (B : BlkFn M) :
    (i.wrapC v).withBlk (B.wrapC v) = (i.withBlk B).wrapC (clrAfter v) := rfl

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.Scrub.X86_64
open Gcm.X86_64.Stitch (CtxMode)

section
variable (v : GcmImpl) {M : CtxMode} (B : BlkFn M)

theorem streamEncryptSM_mx : (streamEncryptS (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, firstFlushS, flushS, streamTextS, streamEncryptS, streamDecryptS, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncryptSM_spSafe : (streamEncryptS (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, firstFlushS, flushS, streamTextS, streamEncryptS, streamDecryptS, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamEncryptSM_xdepth : (streamEncryptS (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, j0hash, j0, firstFlush, streamText, firstFlushS, flushS, streamTextS, streamEncryptS, streamDecryptS, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, oneAad, copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [e]

theorem streamEncryptSM_correct (s : State) (hs : (Proof.AesGcm.streamEncryptX86_64M M).pre s) :
    ∃ t s', Exec isa (streamEncryptS (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamEncryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamEncryptSM_wp v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamEncryptSM_mx v B) he hg, hp⟩

theorem streamDecryptSM_mx : (streamDecryptS (v.withBlk B)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have e := B.encMx
  have d := B.decMx
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, firstFlushS, flushS, streamTextS, streamEncryptS, streamDecryptS, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, Code.allInstrs, GcmImpl.withBlk, GcmImpl.callees, v.ctr.mxcsr, v.key.mxcsr, v.gh.mxcsr, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecryptSM_spSafe : (streamDecryptS (v.withBlk B)).all (fun i => !X86_64.isa.writesSp i) = true := by
  have e := B.encSp
  have d := B.decSp
  simp only [e, d, ↓reduceIte, Bool.false_eq_true, init, streamInit, streamAad, streamEncrypt, streamDecrypt, streamFinish, streamVerify, «seal», «open», openBody, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, tag, j0hash, j0, firstFlush, streamText, firstFlushS, flushS, streamTextS, streamEncryptS, streamDecryptS, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, finTag, oneAad, oneTag, oneCrypt, oneCryptG, oneCryptBlk, Code.all, GcmImpl.withBlk, GcmImpl.callees, v.ctr.spSafe, v.key.spSafe, v.gh.spSafe, Bool.true_and,
    Bool.and_true]
  decide +kernel

theorem streamDecryptSM_xdepth : (streamDecryptS (v.withBlk B)).x86_64Depth ≤ 24 := by
  have e := B.encXd
  have d := B.decXd
  simp only [init, streamInit, streamAad, streamEncrypt, streamDecrypt, ghash1, absorbHead, absorbWhole, absorbTail, absorb, absorbPad, padTail, flush, lens, cryptHead, cryptWhole, cryptTail, cryptTailG, crypt, cryptAl, j0hash, j0, firstFlush, streamText, firstFlushS, flushS, streamTextS, streamEncryptS, streamDecryptS, streamLoad, streamSmall, streamHead, headPart, partWith, streamNext, streamBlocks, oneAad, copyLoop, xorLoop, xorLoopG, minLen, j012, initState, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons, List.length_nil, GcmImpl.withBlk, GcmImpl.callees,
    v.ctr.noStack, v.key.noStack, v.gh.noStack, Nat.max_le, ↓reduceIte, Bool.false_eq_true]
  omega_using [d]

theorem streamDecryptSM_correct (s : State) (hs : (Proof.AesGcm.streamDecryptX86_64M M).pre s) :
    ∃ t s', Exec isa (streamDecryptS (v.withBlk B)) s t s' ∧ abiPreserved s s' ∧ Proof.AesGcm.streamDecryptX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := streamDecryptSM_wp v B hs
  exact ⟨t, s', he, abiPreserved_of_exec (streamDecryptSM_mx v B) he hg, hp⟩

end

section
variable (v : GcmImpl)

theorem streamEncryptSB_verified (B : BlkFn CtxMode.base) :
    Verified X86_64.target (streamEncryptS (v.withBlk B)) (Proof.AesGcm.streamEncryptScratchContract X86_64.abi 24) :=
  Verified.of_correct (fun s hs => streamEncryptSM_correct v B s ⟨hs, trivial⟩)
    (fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => streamEncryptSM_ct v B _ _ _ _ _ _ ⟨h₁, trivial⟩ ⟨h₂, trivial⟩ hp e₁ e₂) (by
    sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using crSat)

theorem streamDecryptSB_verified (B : BlkFn CtxMode.base) :
    Verified X86_64.target (streamDecryptS (v.withBlk B)) (Proof.AesGcm.streamDecryptScratchContract X86_64.abi 24) :=
  Verified.of_correct (fun s hs => streamDecryptSM_correct v B s ⟨hs, trivial⟩)
    (fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => streamDecryptSM_ct v B _ _ _ _ _ _ ⟨h₁, trivial⟩ ⟨h₂, trivial⟩ hp e₁ e₂) (by
    sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using crSat)


theorem streamEncryptSPrepared16_verified (B : BlkFn CtxMode.prepared16) :
    Verified X86_64.target (streamEncryptS (v.withBlk B))
      (Proof.AesGcm.streamEncryptPrepared16ScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamEncryptSM_correct v B) (streamEncryptSM_ct v B)
    { pre := by sig_implies_pre [Proof.AesGcm.streamEncryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPrepared16Pre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.streamEncryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPrepared16Pre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by sig_implies_pub [Proof.AesGcm.streamEncryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPrepared16Pre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨crSatP, by
        sig_pre [Proof.AesGcm.streamEncryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPrepared16Pre, X86_64.abi, X86_64.argRegs, crSatP, crSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact preparedPowers16Repr_of_zero fun _ _ => rfl⟩ }

theorem streamDecryptSPrepared16_verified (B : BlkFn CtxMode.prepared16) :
    Verified X86_64.target (streamDecryptS (v.withBlk B))
      (Proof.AesGcm.streamDecryptPrepared16ScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamDecryptSM_correct v B) (streamDecryptSM_ct v B)
    { pre := by sig_implies_pre [Proof.AesGcm.streamDecryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPrepared16Pre, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.streamDecryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPrepared16Pre, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by sig_implies_pub [Proof.AesGcm.streamDecryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPrepared16Pre, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared16, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowers16Repr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨crSatP, by
        sig_pre [Proof.AesGcm.streamDecryptPrepared16ScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPrepared16Pre, X86_64.abi, X86_64.argRegs, crSatP, crSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact preparedPowers16Repr_of_zero fun _ _ => rfl⟩ }

/-! ### With their working space on the stack -/


theorem streamEncryptSB_framed (B : BlkFn CtxMode.base) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptS (v.withBlk B)))
      (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamEncryptSB_verified v B) (by decide) (by decide) (by decide)
    (streamEncryptSM_spSafe v B) (streamEncryptSM_xdepth v B) (streamTextPre_local _) (streamEncryptPost_local _)
    streamEncryptFrameSat_pre

theorem streamDecryptSB_framed (B : BlkFn CtxMode.base) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptS (v.withBlk B)))
      (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamDecryptSB_verified v B) (by decide) (by decide) (by decide)
    (streamDecryptSM_spSafe v B) (streamDecryptSM_xdepth v B) (streamTextPre_local _) (streamDecryptPost_local _)
    streamDecryptFrameSat_pre

theorem streamEncryptSPrepared16_framed (B : BlkFn CtxMode.prepared16) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptS (v.withBlk B)))
      (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Proof.Gcm.streamCryptPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamEncryptSPrepared16_verified v B) (by decide) (by decide) (by decide)
    (streamEncryptSM_spSafe v B) (streamEncryptSM_xdepth v B) (Proof.AesGcm.streamCryptPrepared16Pre_local _)
    (Proof.AesGcm.streamEncryptPrecomputedPost_local _) streamEncryptFrameSatPrepared16_pre

theorem streamDecryptSPrepared16_framed (B : BlkFn CtxMode.prepared16) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptS (v.withBlk B)))
      (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Proof.Gcm.streamCryptPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamDecryptSPrepared16_verified v B) (by decide) (by decide) (by decide)
    (streamDecryptSM_spSafe v B) (streamDecryptSM_xdepth v B) (Proof.AesGcm.streamCryptPrepared16Pre_local _)
    (Proof.AesGcm.streamDecryptPrecomputedPost_local _) streamDecryptFrameSatPrepared16_pre

end

/-! ## Clearing the registers on the paths that call -/

section
variable (lv : VecLevel) (v : GcmImpl)

theorem streamEncryptClrB_framed (B : BlkFn CtxMode.base) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv))
      (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608) :=
  Verified.hoist lv (streamEncryptSB_framed (v.wrapC lv) (B.wrapC lv))

theorem streamDecryptClrB_framed (B : BlkFn CtxMode.base) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv))
      (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608) :=
  Verified.hoist lv (streamDecryptSB_framed (v.wrapC lv) (B.wrapC lv))

theorem streamEncryptClr16_framed (B : BlkFn CtxMode.prepared16) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv))
      (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608) :=
  Verified.hoist lv (streamEncryptSPrepared16_framed (v.wrapC lv) (B.wrapC lv))

theorem streamDecryptClr16_framed (B : BlkFn CtxMode.prepared16) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv))
      (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608) :=
  Verified.hoist lv (streamDecryptSPrepared16_framed (v.wrapC lv) (B.wrapC lv))

theorem streamEncryptClr_spSafe {M : CtxMode} (B : BlkFn M) :
    (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)).all
      (fun i => !X86_64.isa.writesSp i) = true := by
  have h := X86_64.withStackArgScratch_spSafe (bytes := 2584) (m := 1) (streamEncryptSM_spSafe (v.wrapC lv) (B.wrapC lv))
  rw [← hoist_all lv] at h
  exact h

theorem streamDecryptClr_spSafe {M : CtxMode} (B : BlkFn M) :
    (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv)).all
      (fun i => !X86_64.isa.writesSp i) = true := by
  have h := X86_64.withStackArgScratch_spSafe (bytes := 2584) (m := 1) (streamDecryptSM_spSafe (v.wrapC lv) (B.wrapC lv))
  rw [← hoist_all lv] at h
  exact h

theorem streamEncryptClr_xdepth {M : CtxMode} (B : BlkFn M) :
    (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)).x86_64Depth ≤ 2608 := by
  have h := StreamTo.framed_xdepth (bytes := 2584) (m := 1) (streamEncryptSM_xdepth (v.wrapC lv) (B.wrapC lv))
  rw [← hoist_x86_64Depth lv] at h
  exact h

theorem streamEncryptClr_mx {M : CtxMode} (B : BlkFn M) :
    (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)).allInstrs
      (fun i => !loadsMxcsr i) = true := by
  have h := StreamTo.framed_mx (bytes := 2584) (m := 1) (streamEncryptSM_mx (v.wrapC lv) (B.wrapC lv))
  rw [← hoist_allInstrs lv] at h
  exact h

end

end VG.Proof.AesGcm.X86_64
