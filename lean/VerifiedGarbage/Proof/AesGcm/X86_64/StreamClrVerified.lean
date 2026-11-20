module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared16.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTextSCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Verified
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.CalleeSide
import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubPart
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


/-! ## Zeroing a working space with 16-byte stores -/

/-- The trace of `zeroXs r o k` from `r = p`. -/
def zeroXsTr (p : Addr) (o : Nat) : Nat → List Leak
  | 0 => []
  | k + 1 => .addr (p + BitVec.ofNat 64 (o + 16 * k)) :: zeroXsTr p o k

/-- The trace of `wipeX r o n` from `r = p`. -/
def wipeXTr (p : Addr) (o n : Nat) : List Leak :=
  (if n % 16 = 0 then [] else [.addr (p + BitVec.ofNat 64 (o + n - 16))]) ++ zeroXsTr p o (n / 16)

theorem ea_atX (u : State) (r : Reg) (n : Nat) : u.ea (at_ r n) = u.gpr r + BitVec.ofNat 64 n := by
  simp [at_, State.ea, BitVec.ofInt_natCast]

/-- One 16-byte store of `xmm0`, zero, within a region it may write. -/
theorem zeroX_exec (u : State) (r : Reg) (d : Nat)
    (hin : InRegions u.wr (u.gpr r + BitVec.ofNat 64 d) 16) (hx : u.xmm .xmm0 = 0) :
    isa.exec (.movdquStore (at_ r d) .xmm0) u =
        some { u with mem := u.mem.writeW (u.gpr r + BitVec.ofNat 64 d) (0 : BitVec 128) } ∧
      addrs (.movdquStore (at_ r d) .xmm0) u = [u.gpr r + BitVec.ofNat 64 d] := by
  refine ⟨?_, ?_⟩
  · simp only [reduceExec, ea_atX, State.store128, hin, hx, ↓reduceIte]
  · simp [addrs, ea_atX]

/-- `zeroXs r o k` zeroes the `16 k` bytes at `r + o`, within a region it may
write, from `xmm0` zero. -/
theorem covers_of_mem {R : Region} {rs : List Region} (h : R ∈ rs) : Covers [R] rs := fun _ _ ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, h, hc⟩

theorem zeroXs_run {r : Reg} {o : Nat} {p : Addr} {b : Nat} (hb : b < 2 ^ 64) : ∀ (k : Nat) (u : State),
    Covers [⟨p, b⟩] u.wr → u.gpr r = p → u.xmm .xmm0 = 0 → o + 16 * k ≤ b →
    ∃ m', execBlock isa (zeroXs r o k) u = some ({ u with mem := m' }, zeroXsTr p o k) ∧
      ∀ x, m' x = if o ≤ (x - p).toNat ∧ (x - p).toNat < o + 16 * k then 0 else u.mem x
  | 0, u, _, _, _, _ => ⟨u.mem, rfl, fun x => by rw [ite_f (by omega)]⟩
  | k + 1, u, hR, hr, hx, hk => by
    have hin : InRegions u.wr (u.gpr r + BitVec.ofNat 64 (o + 16 * k)) 16 := by
      refine hR _ _ ⟨_, List.mem_singleton_self _, ?_⟩
      rw [hr]
      exact Offset.contains_base (n := 16) _ (by omega) (by omega)
    obtain ⟨ex, ea⟩ := zeroX_exec u r (o + 16 * k) hin hx
    obtain ⟨m', he, hm⟩ := zeroXs_run (r := r) (o := o) hb k
      { u with mem := u.mem.writeW (u.gpr r + BitVec.ofNat 64 (o + 16 * k)) (0 : BitVec 128) } hR hr hx (by omega)
    refine ⟨m', ?_, fun x => ?_⟩
    · show execBlock isa (.movdquStore (at_ r (o + 16 * k)) .xmm0 :: zeroXs r o k) u = _
      rw [execBlock, ex]
      dsimp only
      rw [he, ea, hr]
      rfl
    · rw [hm x]
      show (if o ≤ (x - p).toNat ∧ (x - p).toNat < o + 16 * k then 0 else
        u.mem.writeW (u.gpr r + BitVec.ofNat 64 (o + 16 * k)) (0 : BitVec 128) x) = _
      rw [writeW_zero128, hr]
      simp only [off_lt _ _ _ _ (show o + 16 * k + 16 < 2 ^ 64 by omega)]
      generalize (x - p).toNat = d
      by_cases h1 : o ≤ d ∧ d < o + 16 * k
      · rw [ite_t h1, ite_t (by omega)]
      · rw [ite_f h1]
        by_cases h2 : o + 16 * k ≤ d ∧ d < o + 16 * k + 16
        · rw [ite_t h2, ite_t (by omega)]
        · rw [ite_f h2, ite_f (by omega)]

/-- `wipeX r o n` zeroes the `n` bytes at `r + o`, within a region it may
write, and changes no register but `xmm0`, which it zeroes. -/
theorem wipeX_run {r : Reg} {o n : Nat} {p : Addr} {b : Nat} (hb : b < 2 ^ 64) (u : State)
    (hR : Covers [⟨p, b⟩] u.wr) (hr : u.gpr r = p) (hn : o + n ≤ b) (h16 : n % 16 = 0 ∨ 16 ≤ n) :
    ∃ m', execBlock isa (wipeX r o n) u = some ({ u.setXmm .xmm0 0 with mem := m' }, wipeXTr p o n) ∧
      ∀ x, m' x = if o ≤ (x - p).toNat ∧ (x - p).toNat < o + n then 0 else u.mem x := by
  have hx : XOp.exec (.bin .pxor .xmm0 .xmm0) u = u.setXmm .xmm0 0 := by
    simp [XOp.exec, reduceXBinOpEval]
  let u₀ := u.setXmm .xmm0 0
  have hR₀ : Covers [⟨p, b⟩] u₀.wr := hR
  have hr₀ : u₀.gpr r = p := hr
  have hx₀ : u₀.xmm .xmm0 = 0 := by simp [u₀, State.setXmm]
  have hdiv := Nat.div_add_mod n 16
  have hmod := Nat.mod_lt n (show 16 > 0 by decide)
  by_cases h0 : n % 16 = 0
  · obtain ⟨m', he, hm⟩ := zeroXs_run (r := r) (o := o) hb (n / 16) u₀ hR₀ hr₀ hx₀ (by omega)
    refine ⟨m', ?_, fun x => ?_⟩
    · simp only [wipeX, wipeXTr, h0, ↓reduceIte, List.nil_append]
      rw [execBlock, show isa.exec (.xop (.bin .pxor .xmm0 .xmm0)) u = some u₀ by
        simp only [reduceExec, hx]; rfl]
      dsimp only
      rw [he]
      simp [addrs, u₀]
    · rw [hm x, show 16 * (n / 16) = n by omega]
      rfl
  · have h16' : 16 ≤ n := h16.resolve_left h0
    have hin : InRegions u₀.wr (u₀.gpr r + BitVec.ofNat 64 (o + n - 16)) 16 := by
      refine hR₀ _ _ ⟨_, List.mem_singleton_self _, ?_⟩
      rw [hr₀]
      exact Offset.contains_base (n := 16) _ (by omega) (by omega)
    obtain ⟨ex, ea⟩ := zeroX_exec u₀ r (o + n - 16) hin hx₀
    obtain ⟨m', he, hm⟩ := zeroXs_run (r := r) (o := o) hb (n / 16)
      { u₀ with mem := u₀.mem.writeW (u₀.gpr r + BitVec.ofNat 64 (o + n - 16)) (0 : BitVec 128) } hR₀ hr₀ hx₀
      (by omega)
    refine ⟨m', ?_, fun x => ?_⟩
    · simp only [wipeX, wipeXTr, h0, ↓reduceIte, List.cons_append, List.nil_append]
      rw [execBlock, show isa.exec (.xop (.bin .pxor .xmm0 .xmm0)) u = some u₀ by
        simp only [reduceExec, hx]; rfl]
      dsimp only
      rw [execBlock, ex]
      dsimp only
      rw [he, ea, hr₀]
      simp [addrs, u₀]
    · rw [hm x]
      show (if o ≤ (x - p).toNat ∧ (x - p).toNat < o + 16 * (n / 16) then 0 else
        u₀.mem.writeW (u₀.gpr r + BitVec.ofNat 64 (o + n - 16)) (0 : BitVec 128) x) = _
      rw [writeW_zero128, hr₀]
      simp only [off_lt _ _ _ _ (show o + n - 16 + 16 < 2 ^ 64 by omega)]
      show _ = if o ≤ (x - p).toNat ∧ (x - p).toNat < o + n then 0 else u.mem x
      generalize (x - p).toNat = d
      by_cases h1 : o ≤ d ∧ d < o + n
      · rw [ite_t h1]
        by_cases h2 : o ≤ d ∧ d < o + 16 * (n / 16)
        · rw [ite_t h2]
        · rw [ite_f h2, ite_t (by omega)]
      · rw [ite_f h1, ite_f (by omega), ite_f (by omega)]
        rfl

theorem mem_zeroXs {r : Reg} {o : Nat} {i : Instr} : ∀ {k : Nat}, i ∈ zeroXs r o k →
    ∃ d, i = .movdquStore (at_ r d) .xmm0
  | 0, h => absurd h (List.not_mem_nil)
  | k + 1, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, rfl⟩
    · exact mem_zeroXs h

theorem mem_wipeX {r : Reg} {o n : Nat} {i : Instr} (h : i ∈ wipeX r o n) :
    i = .xop (.bin .pxor .xmm0 .xmm0) ∨ ∃ d, i = .movdquStore (at_ r d) .xmm0 := by
  rcases List.mem_cons.mp h with rfl | h
  · exact .inl rfl
  rcases List.mem_append.mp h with h | h
  · split at h
    · exact absurd h List.not_mem_nil
    · rcases List.mem_singleton.mp h with rfl; exact .inr ⟨_, rfl⟩
  · exact .inr (mem_zeroXs h)

theorem wipeX_clobbers {r : Reg} {o n : Nat} (g : Reg) : ∀ i ∈ wipeX r o n, Taint.clobbers i g = false := by
  intro i hi
  rcases mem_wipeX hi with rfl | ⟨d, rfl⟩ <;> rfl

theorem wipeX_nosp (r : Reg) (o n : Nat) : ∀ i ∈ wipeX r o n, Taint.clobbers i .rsp = false :=
  wipeX_clobbers .rsp

theorem wipeX_mx (r : Reg) (o n : Nat) : (Code.block (wipeX r o n) : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_eq]
  exact List.all_eq_true.mpr fun i hi => by rcases mem_wipeX hi with rfl | ⟨d, rfl⟩ <;> rfl

theorem wipeX_sp (r : Reg) (o n : Nat) : (wipeX r o n).all (fun i => !isa.writesSp i) = true :=
  List.all_eq_true.mpr fun i hi => by rcases mem_wipeX hi with rfl | ⟨d, rfl⟩ <;> rfl

/-- The registers `wipeX` changes: `xmm0` alone. -/
theorem abiPreserved_wipeX {s u : State} (m : Mem) (h : abiPreserved s u)
    (hm : m.readW (s.gpr .rsp) 64 = u.mem.readW (s.gpr .rsp) 64) :
    abiPreserved s { u.setXmm .xmm0 0 with mem := m } :=
  ⟨fun r hr => h.1 r hr, hm.trans h.2.1, h.2.2⟩


/-- What `wipeX r 0 n` leaves, as a frame: it writes only the region of `b`
bytes at `r`. -/
theorem wipeX_frame {p : Addr} {n b : Nat} (hn : n ≤ b) {m m' : Mem}
    (hm : ∀ x, m' x = if 0 ≤ (x - p).toNat ∧ (x - p).toNat < 0 + n then 0 else m x) :
    Frame [⟨p, b⟩] m m' := fun x hx => by
  rw [hm x, ite_f]
  intro hl
  exact hx _ (List.mem_singleton_self _) (show (x - p).toNat + 1 ≤ b by omega)

/-- Code that never writes `r`, followed by `wipeX r 0 n`, which zeroes the
first `n` bytes of a region of `b` at `r` it may write, apart from the return
address: correct if the postcondition holds through writes to that region. -/
theorem wipeR_ok {c : Prog isa} {r : Reg} {n b : Nat} (hb : b < 2 ^ 64) (hn : n ≤ b) (h16 : n % 16 = 0 ∨ 16 ≤ n)
    (hr : ∀ i ∈ instrs c, Taint.clobbers i r = false) {pre : State → Prop} {post : State → State → Prop}
    (hR : ∀ s, pre s → (⟨s.gpr r, b⟩ : Region) ∈ s.wr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr r, b⟩)
    (hpost : ∀ s u m, pre s → Frame [⟨s.gpr r, b⟩] u.mem m → post s u →
      post s { u.setXmm .xmm0 0 with mem := m })
    (h : ∀ s, pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ post s s') :
    ∀ s, pre s → ∃ t s', Exec isa (.seq c (.block (wipeX r 0 n))) s t s' ∧ abiPreserved s s' ∧ post s s' := by
  intro s hs
  obtain ⟨t, u, e, ha, hq⟩ := h s hs
  obtain ⟨-, hwr⟩ := Exec.rdwr e
  obtain hg := Exec.gpr hr e
  obtain ⟨hin, hd⟩ := hR s hs
  obtain ⟨m', ew, hm⟩ := wipeX_run (o := 0) hb u (by rw [hwr]; exact covers_of_mem hin) hg (by omega) h16
  obtain hf := wipeX_frame hn hm
  refine ⟨_, _, .seq e (.block ew), abiPreserved_wipeX m' ha ?_, hpost s u m' hs hf hq⟩
  exact hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd) (by decide)

/-- `wipeR_ok`, for constant time: the wipe's trace is a function of `r`,
which two runs agree on. -/
theorem wipeR_ct {c : Prog isa} {r : Reg} {n b : Nat} (hb : b < 2 ^ 64) (hn : n ≤ b) (h16 : n % 16 = 0 ∨ 16 ≤ n)
    (hr : ∀ i ∈ instrs c, Taint.clobbers i r = false) {pre : State → Prop} {pub : State → State → Prop}
    (hR : ∀ s, pre s → (⟨s.gpr r, b⟩ : Region) ∈ s.wr)
    (hp : ∀ s₁ s₂, pub s₁ s₂ → s₁.gpr r = s₂.gpr r)
    (h : ConstantTime isa pre pub c) : ConstantTime isa pre pub (.seq c (.block (wipeX r 0 n))) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hq e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      cases b₁ with
      | block w₁ =>
        cases b₂ with
        | block w₂ =>
          obtain ⟨-, hwr₁⟩ := Exec.rdwr a₁
          obtain ⟨-, hwr₂⟩ := Exec.rdwr a₂
          obtain ⟨_, ew₁, -⟩ := wipeX_run (o := 0) hb _ (by rw [hwr₁]; exact covers_of_mem (hR _ h₁)) (Exec.gpr hr a₁) (by omega) h16
          obtain ⟨_, ew₂, -⟩ := wipeX_run (o := 0) hb _ (by rw [hwr₂]; exact covers_of_mem (hR _ h₂)) (Exec.gpr hr a₂) (by omega) h16
          rw [ew₁] at w₁
          rw [ew₂] at w₂
          obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj w₁)
          obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj w₂)
          rw [h s₁ s₂ _ _ _ _ h₁ h₂ hq a₁ a₂, hp _ _ hq]

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

theorem calleeSide_seqBlock {c : Prog isa} {b : List Instr} {k n : Nat}
    (h : X86_64.Scrub.calleeSide c k n = true)
    (hb : (Code.block b : Prog isa).allInstrs (fun i => decide (i.vecLevelR ≤ k) && !loadsMxcsr i) = true) :
    X86_64.Scrub.calleeSide (.seq c (.block b)) k n = true := by
  simp only [X86_64.Scrub.calleeSide, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Code.x86_64Depth]; exact Nat.max_le.mpr ⟨h.1.1, Nat.zero_le _⟩
  · show c.allInstrs _ && (Code.block b : Prog isa).allInstrs _ = true
    rw [h.1.2, hb]; rfl
  · simpa [UpperLock.inames] using h.2

theorem ctr32Wrap_side (v : VecLevel) (c : Ctr32Impl) :
    X86_64.Scrub.calleeSide (ctr32Wrap v c.callee).code (c.level.join v).level 0 = true :=
  calleeSide_seqBlock (X86_64.Scrub.calleeSide_mono (X86_64.Scrub.level_join_left c.level v) (Nat.le_refl 0) c.side)
    (X86_64.Scrub.side_mono (X86_64.Scrub.level_join_right c.level v) (by cases v <;> decide))

theorem ctr32Wrap_expandSide (v : VecLevel) (c : Ctr32Impl) :
    X86_64.Scrub.calleeSide c.expand.code (c.level.join v).level 0 = true :=
  X86_64.Scrub.calleeSide_mono (X86_64.Scrub.level_join_left c.level v) (Nat.le_refl 0) c.expandSide

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
    level := c.level.join v
    side := ctr32Wrap_side v c
    expandSide := ctr32Wrap_expandSide v c
    free := c.free.map (·.wrapC v)
    small := c.small.map (·.wrapC v)
    scr := fun h => c.scr (by cases hs : c.small <;> simp_all)
    gcmInitRes := none
    cmacFinishRes := none }


/-- `vg_aes_ctr32`, as `vg_aes_ctr32_w`, zeroing the `n` bytes of its
working space it may write before it returns (`Fn.wipeR`). -/
def ctr32Wipe (n : Nat) (c : Impl.Aes.X86_64.Ctr32) : Impl.Aes.X86_64.Ctr32 :=
  { c with name := c.name ++ "_w", code := .seq c.code (.block (wipeX .r9 0 n)) }

/-- `Ctr32Small` of `ctr32Wipe 1480`. -/
def Ctr32Small.wipe {c : Impl.Aes.X86_64.Ctr32} (h9 : ∀ i ∈ instrs c.code, Taint.clobbers i .r9 = false)
    (f : Ctr32Small c) : Ctr32Small (ctr32Wipe 1480 c) where
  ok := wipeR_ok (b := 1480) (by decide) (by decide) (.inr (by decide)) h9
    (fun s hs => ⟨by rw [hs.2.1]; simp, hs.2.2.2.2.2.2.2.2.2.2.1⟩)
    (fun s u m hs hf hq => by
      obtain ⟨-, -, -, -, -, h₁, h₂, h₃, -, -, -, hl, -⟩ := hs
      simp only [Proof.Aes.ctr32X86_64S, Proof.Aes.ctr32X86_64] at hq ⊢
      rw [AesGcm.X86_64.blocksAt_frame hf (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact h₃) (by omega),
        AesGcm.X86_64.blockAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h₂)]
      exact hq) f.ok
  ct := wipeR_ct (b := 1480) (by decide) (by decide) (.inr (by decide)) h9
    (fun s hs => by rw [hs.2.1]; simp) (fun _ _ h => h.2.2.2.2.2.1) f.ct
  off := f.off

theorem ctr32Wipe_side (c : Ctr32Impl) :
    X86_64.Scrub.calleeSide (ctr32Wipe 1480 c.callee).code c.level.level 0 = true :=
  calleeSide_seqBlock c.side (X86_64.Scrub.side_mono (Nat.zero_le _) (by decide))

/-- `c`'s `vg_aes_ctr32`, as `vg_aes_ctr32_w`, zeroing the 1480 bytes of its
working space it may write before it returns, for an implementation that
never writes `r9` (`h9`) and uses no more (`f`). -/
def Ctr32Impl.wipe (c : Ctr32Impl) (h9 : ∀ i ∈ instrs c.callee.code, Taint.clobbers i .r9 = false)
    (f : Ctr32Small c.callee) : Ctr32Impl :=
  { c with
    callee := ctr32Wipe 1480 c.callee
    depth := by simp only [ctr32Wipe, Code.depth, c.depth]; rfl
    ok := wipeR_ok (b := 2048) (by decide) (by decide) (.inr (by decide)) h9
      (fun s hs => ⟨by rw [hs.2.1]; simp, hs.2.2.2.2.2.2.2.2.2.2.1⟩)
      (fun s u m hs hf hq => by
        obtain ⟨-, -, -, -, -, h₁, h₂, h₃, -, -, -, hl, -⟩ := hs
        simp only [Proof.Aes.ctr32X86_64] at hq ⊢
        rw [AesGcm.X86_64.blocksAt_frame hf (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact h₃) (by omega),
          AesGcm.X86_64.blockAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h₂)]
        exact hq) c.ok
    ct := wipeR_ct (b := 2048) (by decide) (by decide) (.inr (by decide)) h9
      (fun s hs => by rw [hs.2.1]; simp) (fun _ _ h => h.2.2.2.2.2.1) c.ct
    nosp := fun i hi => by
      rcases List.mem_append.mp hi with hi | hi
      · exact c.nosp i hi
      · exact wipeX_nosp .r9 0 1480 i hi
    mxcsr := by simp only [ctr32Wipe, Code.allInstrs, c.mxcsr, Bool.true_and]; exact wipeX_mx .r9 0 1480
    spSafe := by simp only [ctr32Wipe, Code.all, c.spSafe, Bool.true_and]; exact wipeX_sp .r9 0 1480
    noStack := by simp only [ctr32Wipe, Code.x86_64Depth, c.noStack]; rfl
    side := ctr32Wipe_side c
    free := none
    small := some (f.wipe h9)
    scr := nofun
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


/-- `g`, as `vg_ghash_w`, zeroing the 256 bytes of its working space before it
returns (`Fn.wipeR`), for an implementation that never writes `r8` (`h8`). -/
def GhashImpl.wipe (g : GhashImpl) (h8 : ∀ i ∈ instrs g.fn.code, Taint.clobbers i .r8 = false) : GhashImpl :=
  { g with
    fn := g.fn.wipeR .r8 256
    depth := by simp only [Fn.wipeR, Code.depth, g.depth]; rfl
    noStack := by simp only [Fn.wipeR, Code.x86_64Depth, g.noStack]; rfl
    ok := wipeR_ok (b := 256) (by decide) (by decide) (.inl rfl) h8
      (fun s hs => ⟨by rw [hs.2.1]; simp, hs.2.2.2.2.2.2.2.2⟩)
      (fun s u m hs hf hq => by
        obtain ⟨-, -, -, -, -, h₁, -, -, -⟩ := hs
        simp only [Proof.Gcm.ghashX86_64] at hq ⊢
        rw [blockAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h₁)]
        exact hq) g.ok
    ct := wipeR_ct (b := 256) (by decide) (by decide) (.inl rfl) h8
      (fun s hs => by rw [hs.2.1]; simp) (fun _ _ h => h.2.2.2.2) g.ct
    nosp := fun i hi => by
      rcases List.mem_append.mp hi with hi | hi
      · exact g.nosp i hi
      · exact wipeX_nosp .r8 0 256 i hi
    mxcsr := by simp only [Fn.wipeR, Code.allInstrs, g.mxcsr, Bool.true_and]; exact wipeX_mx .r8 0 256
    spSafe := by simp only [Fn.wipeR, Code.all, g.spSafe, Bool.true_and]; exact wipeX_sp .r8 0 256
    free := none }

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

theorem streamEncryptS_implies :
    (Proof.AesGcm.streamEncryptX86_64).Implies (Proof.AesGcm.streamEncryptScratchContract X86_64.abi 24) := by
  sig_implies [Proof.AesGcm.streamEncryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using crSat

theorem streamEncryptSB_verified (B : BlkFn CtxMode.base) :
    Verified X86_64.target (streamEncryptS (v.withBlk B)) (Proof.AesGcm.streamEncryptScratchContract X86_64.abi 24) :=
  Verified.of_correct (fun s hs => streamEncryptSM_correct v B s ⟨hs, trivial⟩)
    (fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => streamEncryptSM_ct v B _ _ _ _ _ _ ⟨h₁, trivial⟩ ⟨h₂, trivial⟩ hp e₁ e₂) streamEncryptS_implies

theorem streamDecryptS_implies :
    (Proof.AesGcm.streamDecryptX86_64).Implies (Proof.AesGcm.streamDecryptScratchContract X86_64.abi 24) := by
  sig_implies [Proof.AesGcm.streamDecryptScratchContract, Proof.AesGcm.streamCryptScratchSig, Spec.Gcm.streamTextPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24,
      Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below,
      X86_64.argRegs] [crSat] using crSat

theorem streamDecryptSB_verified (B : BlkFn CtxMode.base) :
    Verified X86_64.target (streamDecryptS (v.withBlk B)) (Proof.AesGcm.streamDecryptScratchContract X86_64.abi 24) :=
  Verified.of_correct (fun s hs => streamDecryptSM_correct v B s ⟨hs, trivial⟩)
    (fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => streamDecryptSM_ct v B _ _ _ _ _ _ ⟨h₁, trivial⟩ ⟨h₂, trivial⟩ hp e₁ e₂) streamDecryptS_implies


theorem streamEncryptSPrepared16_implies :
    (Proof.AesGcm.streamEncryptX86_64M CtxMode.prepared16).Implies
      (Proof.AesGcm.streamEncryptPrepared16ScratchContract X86_64.abi 24) :=
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

theorem streamEncryptSPrepared16_verified (B : BlkFn CtxMode.prepared16) :
    Verified X86_64.target (streamEncryptS (v.withBlk B))
      (Proof.AesGcm.streamEncryptPrepared16ScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamEncryptSM_correct v B) (streamEncryptSM_ct v B)
    streamEncryptSPrepared16_implies

theorem streamDecryptSPrepared16_implies :
    (Proof.AesGcm.streamDecryptX86_64M CtxMode.prepared16).Implies
      (Proof.AesGcm.streamDecryptPrepared16ScratchContract X86_64.abi 24) :=
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

theorem streamDecryptSPrepared16_verified (B : BlkFn CtxMode.prepared16) :
    Verified X86_64.target (streamDecryptS (v.withBlk B))
      (Proof.AesGcm.streamDecryptPrepared16ScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamDecryptSM_correct v B) (streamDecryptSM_ct v B)
    streamDecryptSPrepared16_implies

theorem streamEncryptSPrepared_implies :
    (Proof.AesGcm.streamEncryptX86_64M CtxMode.prepared).Implies
      (Proof.AesGcm.streamEncryptPreparedScratchContract X86_64.abi 24) :=
    { pre := by sig_implies_pre [Proof.AesGcm.streamEncryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPowersPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.streamEncryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPowersPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by sig_implies_pub [Proof.AesGcm.streamEncryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPowersPre, Proof.AesGcm.streamEncryptRoundsPost, Proof.AesGcm.streamEncryptX86_64M,
          Proof.AesGcm.streamEncryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨crSatP, by
        sig_pre [Proof.AesGcm.streamEncryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPowersPre, X86_64.abi, X86_64.argRegs, crSatP, crSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact preparedPowersRepr_of_zero fun _ _ => rfl⟩ }

theorem streamEncryptSPrepared_verified (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target (streamEncryptS (v.withBlk B))
      (Proof.AesGcm.streamEncryptPreparedScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamEncryptSM_correct v B) (streamEncryptSM_ct v B)
    streamEncryptSPrepared_implies

theorem streamDecryptSPrepared_implies :
    (Proof.AesGcm.streamDecryptX86_64M CtxMode.prepared).Implies
      (Proof.AesGcm.streamDecryptPreparedScratchContract X86_64.abi 24) :=
    { pre := by sig_implies_pre [Proof.AesGcm.streamDecryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPowersPre, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      post := by sig_implies_post [Proof.AesGcm.streamDecryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPowersPre, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      pub := by sig_implies_pub [Proof.AesGcm.streamDecryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPowersPre, Proof.AesGcm.streamDecryptRoundsPost, Proof.AesGcm.streamDecryptX86_64M,
          Proof.AesGcm.streamDecryptX86_64, Proof.AesGcm.streamCryptPre, Proof.AesGcm.streamCryptPub, CtxMode.prepared, CtxMode.preparedN, VG.Proof.Gcm.X86_64.Stitch.PowersN, Spec.Gcm.PreparedPowersRepr,
          X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.stk24, Proof.AesGcm.ret, Proof.AesGcm.rounds,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, VG.X86_64.below,
          X86_64.argRegs]
      sat := ⟨crSatP, by
        sig_pre [Proof.AesGcm.streamDecryptPreparedScratchContract, Proof.AesGcm.streamCryptPreparedScratchSig, Proof.AesGcm.streamCryptPrecomputedScratchSig,
          Proof.Gcm.streamCryptPowersPre, X86_64.abi, X86_64.argRegs, crSatP, crSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact preparedPowersRepr_of_zero fun _ _ => rfl⟩ }

theorem streamDecryptSPrepared_verified (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target (streamDecryptS (v.withBlk B))
      (Proof.AesGcm.streamDecryptPreparedScratchContract X86_64.abi 24) :=
  Verified.of_correct (streamDecryptSM_correct v B) (streamDecryptSM_ct v B)
    streamDecryptSPrepared_implies

/-! ### With their working space on the stack -/


theorem streamEncryptSB_framed (B : BlkFn CtxMode.base) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptS (v.withBlk B)))
      (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (hpostOut := streamEncryptPostOut_local _) (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamEncryptSB_verified v B) (by decide) (by decide) (by decide)
    (streamEncryptSM_spSafe v B) (streamEncryptSM_xdepth v B) (streamTextPre_local _) (streamEncryptPost_local _)
    streamEncryptFrameSat_pre

theorem streamDecryptSB_framed (B : BlkFn CtxMode.base) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptS (v.withBlk B)))
      (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (hpostOut := streamDecryptPostOut_local _) (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamDecryptSB_verified v B) (by decide) (by decide) (by decide)
    (streamDecryptSM_spSafe v B) (streamDecryptSM_xdepth v B) (streamTextPre_local _) (streamDecryptPost_local _)
    streamDecryptFrameSat_pre

theorem streamEncryptSPrepared16_framed (B : BlkFn CtxMode.prepared16) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptS (v.withBlk B)))
      (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcm.streamEncryptPrecomputedPostOut_local _) (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Proof.Gcm.streamCryptPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamEncryptSPrepared16_verified v B) (by decide) (by decide) (by decide)
    (streamEncryptSM_spSafe v B) (streamEncryptSM_xdepth v B) (Proof.AesGcm.streamCryptPrepared16Pre_local _)
    (Proof.AesGcm.streamEncryptPrecomputedPost_local _) streamEncryptFrameSatPrepared16_pre

theorem streamDecryptSPrepared16_framed (B : BlkFn CtxMode.prepared16) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptS (v.withBlk B)))
      (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcm.streamDecryptPrecomputedPostOut_local _) (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Proof.Gcm.streamCryptPrepared16Pre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamDecryptSPrepared16_verified v B) (by decide) (by decide) (by decide)
    (streamDecryptSM_spSafe v B) (streamDecryptSM_xdepth v B) (Proof.AesGcm.streamCryptPrepared16Pre_local _)
    (Proof.AesGcm.streamDecryptPrecomputedPost_local _) streamDecryptFrameSatPrepared16_pre

theorem streamEncryptSPrepared_framed (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptS (v.withBlk B)))
      (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcm.streamEncryptPrecomputedPostOut_local _) (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Proof.Gcm.streamCryptPowersPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamEncryptSPrepared_verified v B) (by decide) (by decide) (by decide)
    (streamEncryptSM_spSafe v B) (streamEncryptSM_xdepth v B) (Proof.AesGcm.streamCryptPreparedPre_local _)
    (Proof.AesGcm.streamEncryptPrecomputedPost_local _) streamEncryptFrameSatPrepared_pre

theorem streamDecryptSPrepared_framed (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptS (v.withBlk B)))
      (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratch (hpostOut := Proof.AesGcm.streamDecryptPrecomputedPostOut_local _) (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Proof.Gcm.streamCryptPowersPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) (streamDecryptSPrepared_verified v B) (by decide) (by decide) (by decide)
    (streamDecryptSM_spSafe v B) (streamDecryptSM_xdepth v B) (Proof.AesGcm.streamCryptPreparedPre_local _)
    (Proof.AesGcm.streamDecryptPrecomputedPost_local _) streamDecryptFrameSatPrepared_pre

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

theorem streamEncryptClr48_framed (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv))
      (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608) :=
  Verified.hoist lv (streamEncryptSPrepared_framed (v.wrapC lv) (B.wrapC lv))

theorem streamDecryptClr48_framed (B : BlkFn CtxMode.prepared) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv))
      (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608) :=
  Verified.hoist lv (streamDecryptSPrepared_framed (v.wrapC lv) (B.wrapC lv))

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

theorem plain_wrap {c : Prog isa} (h : StackLock.Plain c) : StackLock.Plain (.seq c (.block (clrAfter lv))) :=
  ⟨wrap_nosp lv h.1, by simp only [UpperLock.inames, h.2, List.append_nil]⟩

/-! ### The stack below the frame, in two runs -/

open StackLock in
/-- Two runs of `vg_aes_gcm_stream_encrypt` clearing the registers after
each call, from states with the same stack pointer that agree on the
stack below it, end agreeing on the 24 bytes
below its frame: the return addresses its calls leave there and the stack
argument of the whole blocks (`streamS_same`, `framed_same`). -/
theorem streamEncryptClrB_below (B : BlkFn CtxMode.base) (hct : Plain v.callees.ctr.code)
    (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.enc.code = []) {s₁ s₂ : State}
    (h₁ : (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pre s₁)
    (h₂ : (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pre s₂)
    (hp : (Proof.AesGcm.streamEncryptRoundsContract X86_64.abi 2608).pub s₁ s₂) (hrsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (hm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 (24 + 2584), 24 + 2584⟩ : Region).Contains x 1 →
      s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1 → u₁.mem x = u₂.mem x := by
  have hsp := streamEncryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamEncryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framed_same (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2584) (leak := none) (Verified.hoist lv (streamEncryptSB_verified (v.wrapC lv) (B.wrapC lv)))
    (fun a b _ _ _ _ h₁ h₂ hp hs e₁ e₂ =>
      have k₁ := streamEncryptS_implies.pre a h₁
      have k₂ := streamEncryptS_implies.pre b h₂
      have hq := streamEncryptS_implies.pub a b h₁ h₂ hp
      streamS_same (v.wrapC lv) (B.wrapC lv) true k₁ trivial k₂ trivial hq
      (plain_wrap lv hct) (plain_wrap lv hgh)
      (show UpperLock.inames (.seq B.enc.code (.block (clrAfter lv))) = [] by
        simp only [UpperLock.inames, hn, List.append_nil]) hs
      ((exec_hoist lv _ _ _ _).mp e₁) ((exec_hoist lv _ _ _ _).mp e₂))
    (by decide) (by decide) (by decide) hsp hd (streamTextPre_local _) trivial h₁ h₂ hp hrsp hm hu e₁ e₂


open StackLock in
/-- `streamEncryptClrB_below` for `vg_aes_gcm_stream_decrypt`. -/
theorem streamDecryptClrB_below (B : BlkFn CtxMode.base) (hct : Plain v.callees.ctr.code)
    (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.dec.code = []) {s₁ s₂ : State}
    (h₁ : (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608).pre s₁)
    (h₂ : (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608).pre s₂)
    (hp : (Proof.AesGcm.streamDecryptRoundsContract X86_64.abi 2608).pub s₁ s₂) (hrsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (hm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 (24 + 2584), 24 + 2584⟩ : Region).Contains x 1 →
      s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1 → u₁.mem x = u₂.mem x := by
  have hsp := streamDecryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamDecryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framed_same (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2584) (leak := none) (Verified.hoist lv (streamDecryptSB_verified (v.wrapC lv) (B.wrapC lv)))
    (fun a b _ _ _ _ h₁ h₂ hp hs e₁ e₂ =>
      have k₁ := streamDecryptS_implies.pre a h₁
      have k₂ := streamDecryptS_implies.pre b h₂
      have hq := streamDecryptS_implies.pub a b h₁ h₂ hp
      streamS_same (v.wrapC lv) (B.wrapC lv) false k₁ trivial k₂ trivial hq
      (plain_wrap lv hct) (plain_wrap lv hgh)
      (show UpperLock.inames (.seq B.dec.code (.block (clrAfter lv))) = [] by
        simp only [UpperLock.inames, hn, List.append_nil]) hs
      ((exec_hoist lv _ _ _ _).mp e₁) ((exec_hoist lv _ _ _ _).mp e₂))
    (by decide) (by decide) (by decide) hsp hd (streamTextPre_local _) trivial h₁ h₂ hp hrsp hm hu e₁ e₂


open StackLock in
/-- `streamEncryptClrB_below`, on 16 powers of the hash subkey. -/
theorem streamEncryptClr16_below (B : BlkFn CtxMode.prepared16) (hct : Plain v.callees.ctr.code)
    (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.enc.code = []) {s₁ s₂ : State}
    (h₁ : (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608).pre s₁)
    (h₂ : (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608).pre s₂)
    (hp : (Proof.AesGcm.streamEncryptPrepared16RoundsContract X86_64.abi 2608).pub s₁ s₂) (hrsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (hm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 (24 + 2584), 24 + 2584⟩ : Region).Contains x 1 →
      s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1 → u₁.mem x = u₂.mem x := by
  have hsp := streamEncryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamEncryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framed_same (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Proof.Gcm.streamCryptPrepared16Pre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2584) (leak := none) (Verified.hoist lv (streamEncryptSPrepared16_verified (v.wrapC lv) (B.wrapC lv)))
    (fun a b _ _ _ _ h₁ h₂ hp hs e₁ e₂ =>
      have k₁ := streamEncryptSPrepared16_implies.pre a h₁
      have k₂ := streamEncryptSPrepared16_implies.pre b h₂
      have hq := streamEncryptSPrepared16_implies.pub a b h₁ h₂ hp
      streamS_same (v.wrapC lv) (B.wrapC lv) true k₁.1 k₁.2 k₂.1 k₂.2 hq
      (plain_wrap lv hct) (plain_wrap lv hgh)
      (show UpperLock.inames (.seq B.enc.code (.block (clrAfter lv))) = [] by
        simp only [UpperLock.inames, hn, List.append_nil]) hs
      ((exec_hoist lv _ _ _ _).mp e₁) ((exec_hoist lv _ _ _ _).mp e₂))
    (by decide) (by decide) (by decide) hsp hd (Proof.AesGcm.streamCryptPrepared16Pre_local _) trivial h₁ h₂ hp hrsp hm hu e₁ e₂


open StackLock in
/-- `streamDecryptClrB_below`, on 16 powers of the hash subkey. -/
theorem streamDecryptClr16_below (B : BlkFn CtxMode.prepared16) (hct : Plain v.callees.ctr.code)
    (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.dec.code = []) {s₁ s₂ : State}
    (h₁ : (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608).pre s₁)
    (h₂ : (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608).pre s₂)
    (hp : (Proof.AesGcm.streamDecryptPrepared16RoundsContract X86_64.abi 2608).pub s₁ s₂) (hrsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (hm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 (24 + 2584), 24 + 2584⟩ : Region).Contains x 1 →
      s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1 → u₁.mem x = u₂.mem x := by
  have hsp := streamDecryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamDecryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framed_same (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Proof.Gcm.streamCryptPrepared16Pre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2584) (leak := none) (Verified.hoist lv (streamDecryptSPrepared16_verified (v.wrapC lv) (B.wrapC lv)))
    (fun a b _ _ _ _ h₁ h₂ hp hs e₁ e₂ =>
      have k₁ := streamDecryptSPrepared16_implies.pre a h₁
      have k₂ := streamDecryptSPrepared16_implies.pre b h₂
      have hq := streamDecryptSPrepared16_implies.pub a b h₁ h₂ hp
      streamS_same (v.wrapC lv) (B.wrapC lv) false k₁.1 k₁.2 k₂.1 k₂.2 hq
      (plain_wrap lv hct) (plain_wrap lv hgh)
      (show UpperLock.inames (.seq B.dec.code (.block (clrAfter lv))) = [] by
        simp only [UpperLock.inames, hn, List.append_nil]) hs
      ((exec_hoist lv _ _ _ _).mp e₁) ((exec_hoist lv _ _ _ _).mp e₂))
    (by decide) (by decide) (by decide) hsp hd (Proof.AesGcm.streamCryptPrepared16Pre_local _) trivial h₁ h₂ hp hrsp hm hu e₁ e₂

open StackLock in
/-- `streamEncryptClrB_below`, on 48 powers of the hash subkey. -/
theorem streamEncryptClr48_below (B : BlkFn CtxMode.prepared) (hct : Plain v.callees.ctr.code)
    (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.enc.code = []) {s₁ s₂ : State}
    (h₁ : (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608).pre s₁)
    (h₂ : (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608).pre s₂)
    (hp : (Proof.AesGcm.streamEncryptPreparedRoundsContract X86_64.abi 2608).pub s₁ s₂) (hrsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (hm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 (24 + 2584), 24 + 2584⟩ : Region).Contains x 1 →
      s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamEncryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1 → u₁.mem x = u₂.mem x := by
  have hsp := streamEncryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamEncryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framed_same (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Proof.Gcm.streamCryptPowersPre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamEncryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2584) (leak := none) (Verified.hoist lv (streamEncryptSPrepared_verified (v.wrapC lv) (B.wrapC lv)))
    (fun a b _ _ _ _ h₁ h₂ hp hs e₁ e₂ =>
      have k₁ := streamEncryptSPrepared_implies.pre a h₁
      have k₂ := streamEncryptSPrepared_implies.pre b h₂
      have hq := streamEncryptSPrepared_implies.pub a b h₁ h₂ hp
      streamS_same (v.wrapC lv) (B.wrapC lv) true k₁.1 k₁.2 k₂.1 k₂.2 hq
      (plain_wrap lv hct) (plain_wrap lv hgh)
      (show UpperLock.inames (.seq B.enc.code (.block (clrAfter lv))) = [] by
        simp only [UpperLock.inames, hn, List.append_nil]) hs
      ((exec_hoist lv _ _ _ _).mp e₁) ((exec_hoist lv _ _ _ _).mp e₂))
    (by decide) (by decide) (by decide) hsp hd (Proof.AesGcm.streamCryptPreparedPre_local _) trivial h₁ h₂ hp hrsp hm hu e₁ e₂


open StackLock in
/-- `streamDecryptClrB_below`, on 48 powers of the hash subkey. -/
theorem streamDecryptClr48_below (B : BlkFn CtxMode.prepared) (hct : Plain v.callees.ctr.code)
    (hgh : Plain v.callees.gh.code) (hn : UpperLock.inames B.dec.code = []) {s₁ s₂ : State}
    (h₁ : (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608).pre s₁)
    (h₂ : (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608).pre s₂)
    (hp : (Proof.AesGcm.streamDecryptPreparedRoundsContract X86_64.abi 2608).pub s₁ s₂) (hrsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (hm : ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 (24 + 2584), 24 + 2584⟩ : Region).Contains x 1 →
      s₁.mem x = s₂.mem x)
    (hu : s₁.unknowns = s₂.unknowns) {t₁ t₂ : List Leak} {u₁ u₂ : State}
    (e₁ : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv)) s₁ t₁ u₁)
    (e₂ : Exec isa (Impl.StackScratch.X86_64.withStackArgScratch 2584 1 (streamDecryptClr (v.withBlk B) lv)) s₂ t₂ u₂) :
    ∀ x, (below (s₁.gpr .rsp - BitVec.ofNat 64 2584) 24).Contains x 1 → u₁.mem x = u₂.mem x := by
  have hsp := streamDecryptSM_spSafe (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_all lv] at hsp
  have hd := streamDecryptSM_xdepth (v.wrapC lv) (B.wrapC lv)
  rw [← hoist_x86_64Depth lv] at hd
  exact framed_same (sig := Proof.Gcm.streamCryptPrecomputedSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Proof.Gcm.streamCryptPowersPre X86_64.abi.ptrBits) (post := Proof.AesGcm.streamDecryptRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 24) (bytes := 2584) (leak := none) (Verified.hoist lv (streamDecryptSPrepared_verified (v.wrapC lv) (B.wrapC lv)))
    (fun a b _ _ _ _ h₁ h₂ hp hs e₁ e₂ =>
      have k₁ := streamDecryptSPrepared_implies.pre a h₁
      have k₂ := streamDecryptSPrepared_implies.pre b h₂
      have hq := streamDecryptSPrepared_implies.pub a b h₁ h₂ hp
      streamS_same (v.wrapC lv) (B.wrapC lv) false k₁.1 k₁.2 k₂.1 k₂.2 hq
      (plain_wrap lv hct) (plain_wrap lv hgh)
      (show UpperLock.inames (.seq B.dec.code (.block (clrAfter lv))) = [] by
        simp only [UpperLock.inames, hn, List.append_nil]) hs
      ((exec_hoist lv _ _ _ _).mp e₁) ((exec_hoist lv _ _ _ _).mp e₂))
    (by decide) (by decide) (by decide) hsp hd (Proof.AesGcm.streamCryptPreparedPre_local _) trivial h₁ h₂ hp hrsp hm hu e₁ e₂

end

end VG.Proof.AesGcm.X86_64
