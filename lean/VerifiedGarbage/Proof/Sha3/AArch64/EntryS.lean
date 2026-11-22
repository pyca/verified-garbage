module

public import VerifiedGarbage.Proof.Sha3.AArch64.Entry
public import VerifiedGarbage.Impl.Sha3.AArch64.ViaD8
public import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave

/-!
# Calling a function with stack arguments with an address in `d8` (AArch64)

`Verified.entryD8S`: `Verified.entryD8` for a function whose arguments do
not all fit the eight argument registers. `entryD8S n name k body` copies the
caller's `k` stack words into the bottom of its frame (`copyArg`, as
`withStackArgScratch` does), so that `body` finds its own stack arguments at
its `sp`, then saves the return address and `d8` above them and calls `body`
with `n`'s address in `d8`. `body` runs from the state after the call with
the permissions of its contract (`eEntryS`): the caller's buffers, and the
copies, read-only, in place of the caller's argument area; its run there is
its run from the state after the call (`WP.callFV`).
-/

-- separate module: the entry for functions with stack arguments, which only some callers of `d8`
-- functions need, apart from `Entry.lean`, which every one imports.

@[expose] public section

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64 VG.Impl.Sha3.AArch64 VG.Impl.StackScratch.AArch64

/-! ## The frame -/

/-- The state after the frame's allocation and the copies of `k` stack
words. -/
abbrev sCopied (k : Nat) (s : State) : State :=
  copiedState (frameS k) (baseState (allocated (frameS k) s)) k

/-- The address `off` bytes into the frame of `s`'s caller. -/
abbrev sslot (k : Nat) (s : State) (off : Nat) : Addr :=
  s.sp - BitVec.ofNat 64 (frameS k) + BitVec.ofNat 64 off

/-- The states after each instruction of `enterD8S n k` after the copies. -/
abbrev sS₁ (k : Nat) (s : State) : State := (sCopied k s).write .x .x16 (laneOf (sCopied k s) .v8 0)
abbrev sS₂ (k : Nat) (s : State) : State :=
  { sS₁ k s with mem := (sS₁ k s).mem.write ((sS₁ k s).sp + BitVec.ofNat 64 (saveOff k)) 8 ((sS₁ k s).gpr .x30) }
abbrev sS₃ (k : Nat) (s : State) : State :=
  { sS₂ k s with
    mem := (sS₂ k s).mem.write ((sS₂ k s).sp + BitVec.ofNat 64 (saveOff k + 8)) 8 ((sS₂ k s).gpr .x16) }
abbrev sS₄ (n : String) (k : Nat) (s : State) : State := (sS₃ k s).write .x .x16 ((sS₃ k s).syms n)

/-- The state after the frame's allocation and `enterD8S n k`. -/
def sSave (n : String) (k : Nat) (s : State) : State :=
  (sS₄ n k s).setV .v8 (setLane ((sS₄ n k s).v .v8) 64 0 ((sS₄ n k s).gpr .x16))

theorem sCopied_sp (k : Nat) (s : State) : (sCopied k s).sp = s.sp - BitVec.ofNat 64 (frameS k) := by
  rw [copiedState_sp]; rfl

@[simp] theorem sSave_sp (n : String) (k : Nat) (s : State) :
    (sSave n k s).sp = s.sp - BitVec.ofNat 64 (frameS k) := sCopied_sp k s
@[simp] theorem sSave_rd (n : String) (k : Nat) (s : State) : (sSave n k s).rd = s.rd := by
  show (sCopied k s).rd = _; rw [copiedState_rd]; rfl
@[simp] theorem sSave_wr (n : String) (k : Nat) (s : State) :
    (sSave n k s).wr = ⟨s.sp - BitVec.ofNat 64 (frameS k), frameS k⟩ :: s.wr := by
  show (sCopied k s).wr = _; rw [copiedState_wr]; rfl
theorem copiedState_syms (b : Nat) (w : State) : ∀ m, (copiedState b w m).syms = w.syms
  | 0 => rfl
  | m + 1 => copiedState_syms b w m

@[simp] theorem sSave_syms (n : String) (k : Nat) (s : State) : (sSave n k s).syms = s.syms := by
  show (sCopied k s).syms = _; rw [copiedState_syms]; rfl
@[simp] theorem sSave_dit (n : String) (k : Nat) (s : State) : (sSave n k s).dit = s.dit := by
  show (sCopied k s).dit = _; rw [copiedState_dit]; rfl

theorem sCopied_gpr (k : Nat) (s : State) {q : Reg} (h₁ : q ≠ .x16) (h₂ : q ≠ .x17) :
    (sCopied k s).gpr q = s.gpr q := by
  rw [copiedState_gpr _ _ h₂, RegUpd.gpr_write_of_ne _ _ _ h₁]; rfl

theorem sSave_gpr (n : String) (k : Nat) (s : State) {q : Reg} (h₁ : q ≠ .x16) (h₂ : q ≠ .x17) :
    (sSave n k s).gpr q = s.gpr q := by
  rw [sSave, RegUpd.gpr_setV, RegUpd.gpr_write_of_ne _ _ _ h₁]
  show ((sCopied k s).write .x .x16 _).gpr q = _
  rw [RegUpd.gpr_write_of_ne _ _ _ h₁, sCopied_gpr k s h₁ h₂]

theorem sCopied_v (k : Nat) (s : State) : (sCopied k s).v = s.v := by
  rw [copiedState_v]; rfl

theorem sSave_v (n : String) (k : Nat) (s : State) {q : VReg} (h : q ≠ .v8) : (sSave n k s).v q = s.v q := by
  rw [sSave, RegUpd.v_setV_of_ne _ _ h, RegUpd.v_write]
  show ((sCopied k s).write .x .x16 (laneOf (sCopied k s) .v8 0)).v q = _
  rw [RegUpd.v_write, sCopied_v]

theorem sSave_d8 (n : String) (k : Nat) (s : State) : D8 n (sSave n k s) := by
  unfold D8
  rw [sSave_syms, sSave, RegUpd.v_setV_self, RegUpd.gpr_write_self, BitVec.setWidth_eq]
  exact (extract_setLane64 _ _ (i := 0) (j := 0) (by decide) (by decide)).trans (ite_eq_left rfl) |>.trans
    (congrFun (sSave_syms n k s) n)

theorem frameS_mod (k : Nat) : frameS k % 8 = 0 := by unfold frameS saveOff; omega

theorem saveOff_ge (k : Nat) : 8 * k ≤ saveOff k := by unfold saveOff; omega

theorem saveOff_mod (k : Nat) : saveOff k % 8 = 0 := by unfold saveOff; omega

theorem frameS_mod16 (k : Nat) : frameS k % 16 = 0 := by unfold frameS saveOff; omega

/-- The frame's slot at `off` holds the 8 bytes there. -/
theorem sslot_in (k : Nat) (s : State) {off : Nat} (h : off + 8 ≤ frameS k) (hE : frameS k ≤ 32768) :
    InRegions (⟨s.sp - BitVec.ofNat 64 (frameS k), frameS k⟩ :: s.wr) (sslot k s off) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by omega)⟩

theorem sCopied_sp' (k : Nat) (s : State) (off : Nat) :
    (sCopied k s).sp + BitVec.ofNat 64 off = sslot k s off := by
  rw [sCopied_sp]

/-- The instructions of `enterD8S n k` after the copies. -/
theorem enterS_tail_run (n : String) (k : Nat) (s : State) (hE : frameS k ≤ 32768) :
    execBlock isa [.umov .x .x16 .v8 0, .strSp .x30 (saveOff k), .strSp .x16 (saveOff k + 8), .adrSym .x16 n,
        .vop (.ins .d2 .v8 0 .x16)] (sCopied k s) =
      some (sSave n k s, [.addr (sslot k s (saveOff k)), .addr (sslot k s (saveOff k + 8))]) := by
  have hb : saveOff k + 8 + 8 ≤ frameS k := by unfold frameS; omega
  have e₀ : exec (.umov .x .x16 .v8 0) (sCopied k s) = some (sS₁ k s) := exec_umov (by decide)
  have e₁ : exec (.strSp .x30 (saveOff k)) (sS₁ k s) = some (sS₂ k s) :=
    exec_strSp' ⟨saveOff_mod k, by omega⟩ (by
      show InRegions (sCopied k s).wr ((sCopied k s).sp + _) 8
      rw [copiedState_wr, sCopied_sp' k s]; exact sslot_in k s (by omega) hE)
  have e₂ : exec (.strSp .x16 (saveOff k + 8)) (sS₂ k s) = some (sS₃ k s) :=
    exec_strSp' ⟨by have := saveOff_mod k; omega, by omega⟩ (by
      show InRegions (sCopied k s).wr ((sCopied k s).sp + _) 8
      rw [copiedState_wr, sCopied_sp' k s]; exact sslot_in k s (by omega) hE)
  have e₃ : exec (.adrSym .x16 n) (sS₃ k s) = some (sS₄ n k s) := exec_adrSym
  have e₄ : exec (.vop (.ins .d2 .v8 0 .x16)) (sS₄ n k s) = some (sSave n k s) := exec_ins (by decide)
  simp only [execBlock, isa, e₀, e₁, e₂, e₃, e₄, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rw [show (sS₁ k s).sp = (sCopied k s).sp from rfl, sCopied_sp' k s, sCopied_sp' k s]

/-- A run of `enterD8S n k` from the caller's state `s`, whose `k` stack
words are readable. -/
theorem enterS_run (n : String) (k : Nat) (s : State) (hb : frameS k + 8 * k ≤ 32768)
    (hr : ∀ j < k, InRegions s.rd (stackArgAddr s j) 8) :
    execBlock isa (enterD8S n k) (allocated (frameS k) s) =
      some (sSave n k s, copyTrace (frameS k) (s.sp - BitVec.ofNat 64 (frameS k)) k ++
        [.addr (sslot k s (saveOff k)), .addr (sslot k s (saveOff k + 8))]) := by
  have e_add : exec (.addSp .x16 0) (allocated (frameS k) s) = some (baseState (allocated (frameS k) s)) :=
    exec_addSp (by decide)
  have hsk := saveOff_ge k
  have hc := copies_run (bytes := frameS k) (w := baseState (allocated (frameS k) s))
    (baseState_x16 _) (frameS_mod k) k (by omega)
    (fun j hj => by
      obtain ⟨R, hR, hcR⟩ := hr j hj
      refine ⟨R, List.mem_append_left _ hR, ?_⟩
      show R.Contains (s.sp - BitVec.ofNat 64 (frameS k) + BitVec.ofNat 64 (frameS k + 8 * j)) 8
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      exact hcR)
    (fun j hj => by
      show InRegions (⟨s.sp - BitVec.ofNat 64 (frameS k), frameS k⟩ :: s.wr)
        (s.sp - BitVec.ofNat 64 (frameS k) + BitVec.ofNat 64 (8 * j)) 8
      exact sslot_in k s (by unfold frameS; omega) (by omega))
  rw [enterD8S, execBlock_append, execBlock_cons_of e_add, hc]
  simp only [Option.map_some, Option.bind_some]
  rw [enterS_tail_run n k s (by omega)]
  simp only [Option.map_some, addrs, List.map_nil, List.nil_append]
  rfl

end VG.Proof.Sha3.AArch64
