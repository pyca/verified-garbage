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

theorem laneOf_sCopied (k : Nat) (s : State) : laneOf (sCopied k s) .v8 0 = laneOf s .v8 0 := by
  unfold laneOf; rw [sCopied_v]

theorem sSave_mem (n : String) (k : Nat) (s : State) :
    (sSave n k s).mem = ((sCopied k s).mem.write (sslot k s (saveOff k)) 8 (s.gpr .x30)).write
      (sslot k s (saveOff k + 8)) 8 (laneOf s .v8 0) := by
  have h30 : (sS₁ k s).gpr .x30 = s.gpr .x30 :=
    (RegUpd.gpr_write_of_ne _ _ _ (by decide)).trans (sCopied_gpr k s (by decide) (by decide))
  have h16 : (sS₂ k s).gpr .x16 = laneOf s .v8 0 := by
    show (sS₁ k s).gpr .x16 = _
    rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, laneOf_sCopied]
  show ((sS₁ k s).mem.write ((sS₁ k s).sp + _) 8 ((sS₁ k s).gpr .x30)).write
    ((sS₂ k s).sp + _) 8 ((sS₂ k s).gpr .x16) = _
  rw [h30, h16, show (sS₂ k s).sp = (sCopied k s).sp from rfl, sCopied_sp' k s, sCopied_sp' k s]
  rfl

theorem sslot_contains (k : Nat) (s : State) {off : Nat} (h : off + 8 ≤ frameS k) (hE : frameS k ≤ 32768) :
    (below s.sp (frameS k)).Contains (sslot k s off) 8 :=
  Offset.contains_base _ h (by omega)

/-- The entry writes only its frame, the `frameS k` bytes below `sp`. -/
theorem sSave_frame (n : String) (k : Nat) (s : State) (hE : frameS k ≤ 32768) :
    Frame [below s.sp (frameS k)] s.mem (sSave n k s).mem := by
  have hsk := saveOff_ge k
  have hb : saveOff k + 16 ≤ frameS k := by unfold frameS; omega
  obtain ⟨f, -⟩ := copiedState_mem (bytes := frameS k) (w := baseState (allocated (frameS k) s))
    (baseState_x16 _) k (by omega) (by omega)
  rw [sSave_mem]
  refine Frame.write (Frame.write (Frame.sub f fun r hr => ?_) (List.mem_singleton_self _) _
    (sslot_contains k s (by omega) hE)) (List.mem_singleton_self _) _ (sslot_contains k s (by omega) hE)
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩

/-- The frame's bottom holds the caller's stack words. -/
theorem sSave_args (n : String) (k : Nat) (s : State) (hE : frameS k ≤ 32768) {j : Nat} (hj : j < k) :
    (sSave n k s).mem.readW (sslot k s (8 * j)) 64 = s.mem.readW (stackArgAddr s j) 64 := by
  have hsk := saveOff_ge k
  have hb : saveOff k + 16 ≤ frameS k := by unfold frameS; omega
  obtain ⟨-, hv⟩ := copiedState_mem (bytes := frameS k) (w := baseState (allocated (frameS k) s))
    (baseState_x16 _) k (by omega) (by omega)
  rw [sSave_mem]
  simp only [Mem.readW]
  rw [Mem.read_write_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
    Mem.read_write_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
  have h := hv j hj
  simp only [Mem.readW] at h
  rw [show (baseState (allocated (frameS k) s)).sp = s.sp - BitVec.ofNat 64 (frameS k) from rfl] at h
  rw [h, stackArgAddr]
  show (s.mem.read _ (64 / 8)).setWidth 64 = _
  rw [show s.sp - BitVec.ofNat 64 (frameS k) + BitVec.ofNat 64 (frameS k + 8 * j) =
      s.sp + BitVec.ofNat 64 (8 * j) by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]]

theorem sSave_read_x30 (n : String) (k : Nat) (s : State) (hE : frameS k ≤ 32768) :
    (sSave n k s).mem.read (sslot k s (saveOff k)) 8 = s.gpr .x30 := by
  have hb : saveOff k + 16 ≤ frameS k := by unfold frameS; omega
  rw [sSave_mem, Mem.read_write_sep (Offset.sep _ (.inl (by omega)) (by omega) (by omega)) (by decide),
    read_write_self]

theorem sSave_read_d8 (n : String) (k : Nat) (s : State) :
    (sSave n k s).mem.read (sslot k s (saveOff k + 8)) 8 = laneOf s .v8 0 := by
  rw [sSave_mem, read_write_self]

/-- The state after `leaveD8S k`, from `g`. -/
def sRestore (k : Nat) (g : State) : State :=
  let g₁ := g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 (saveOff k + 8)) 8)
  let g₂ := g₁.setV .v8 (setLane (g₁.v .v8) 64 0 (g₁.gpr .x16))
  g₂.write .x .x30 (g₂.mem.read (g₂.sp + BitVec.ofNat 64 (saveOff k)) 8)

theorem leaveS_run {k : Nat} {g : State} (hE : frameS k ≤ 32768)
    (h8 : InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 (saveOff k + 8)) 8)
    (h0 : InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 (saveOff k)) 8) :
    execBlock isa (leaveD8S k) g =
      some (sRestore k g, [.addr (g.sp + BitVec.ofNat 64 (saveOff k + 8)), .addr (g.sp + BitVec.ofNat 64 (saveOff k))]) := by
  have hb : saveOff k + 16 ≤ frameS k := by unfold frameS; omega
  have hm := saveOff_mod k
  have e₁ : exec (.ldrSp .x16 (saveOff k + 8)) g =
      some (g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 (saveOff k + 8)) 8)) :=
    exec_ldrSp' ⟨by omega, by omega⟩ h8
  have e₂ := exec_ins (s := g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 (saveOff k + 8)) 8))
    (r := .x16) (v := .v8) (l := 0) (by decide)
  have e₃ := exec_ldrSp' (t := .x30) (off := saveOff k)
    (s := (g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 (saveOff k + 8)) 8)).setV .v8
      (setLane ((g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 (saveOff k + 8)) 8)).v .v8) 64 0
        ((g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 (saveOff k + 8)) 8)).gpr .x16)))
    ⟨hm, by omega⟩ h0
  simp only [leaveD8S, execBlock, isa, e₁, e₂, e₃, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, RegUpd.sp_write, RegUpd.sp_setV]
  rfl

theorem sRestore_gpr {k : Nat} {g : State} {q : Reg} (h16 : q ≠ .x16) (h30 : q ≠ .x30) :
    (sRestore k g).gpr q = g.gpr q := by
  simp only [sRestore, RegUpd.gpr_write_of_ne _ _ _ h30, RegUpd.gpr_setV, RegUpd.gpr_write_of_ne _ _ _ h16]

theorem sRestore_x30 (k : Nat) (g : State) :
    (sRestore k g).gpr .x30 = g.mem.read (g.sp + BitVec.ofNat 64 (saveOff k)) 8 := by
  simp only [sRestore, RegUpd.gpr_write_self, BitVec.setWidth_eq]; rfl

theorem sRestore_sp (k : Nat) (g : State) : (sRestore k g).sp = g.sp := rfl

theorem sRestore_v {k : Nat} {g : State} {q : VReg} (h : q ≠ .v8) : (sRestore k g).v q = g.v q := by
  simp only [sRestore, RegUpd.v_write, RegUpd.v_setV_of_ne _ _ h]

theorem sRestore_d8 (k : Nat) (g : State) :
    ((sRestore k g).v .v8).extractLsb' 0 64 = g.mem.read (g.sp + BitVec.ofNat 64 (saveOff k + 8)) 8 := by
  simp only [sRestore, RegUpd.v_write, RegUpd.v_setV_self]
  refine (extract_setLane64 _ _ (i := 0) (j := 0) (by decide) (by decide)).trans (ite_eq_left rfl) |>.trans ?_
  simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq]

/-! ## The function's contract at its entry -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The state the function runs from, with the permissions of its contract:
after the call, with the caller's buffers and the copies of its stack words
in place of its argument area. -/
def eEntryS (sig : Sig) (n : String) (s : State) : State :=
  ((sSave n (nStack sig) s).callEntry).withRegions
    (((allRegions sig (sSave n (nStack sig) s).callEntry).filter (!·.2)).map (·.1))
    (((allRegions sig (sSave n (nStack sig) s).callEntry).filter (·.2)).map (·.1))

@[simp] theorem eEntryS_sp (sig : Sig) (n : String) (s : State) :
    (eEntryS sig n s).sp = s.sp - BitVec.ofNat 64 (frameS (nStack sig)) := sSave_sp n _ s
@[simp] theorem eEntryS_mem (sig : Sig) (n : String) (s : State) :
    (eEntryS sig n s).mem = (sSave n (nStack sig) s).mem := rfl
@[simp] theorem eEntryS_syms (sig : Sig) (n : String) (s : State) : (eEntryS sig n s).syms = s.syms :=
  sSave_syms n _ s
@[simp] theorem eEntryS_dit (sig : Sig) (n : String) (s : State) : (eEntryS sig n s).dit = s.dit :=
  sSave_dit n _ s

theorem eEntryS_gpr (sig : Sig) (n : String) (s : State) {q : Reg} (h : q ∉ linkRegs) :
    (eEntryS sig n s).gpr q = s.gpr q := by
  rw [eEntryS, State.withRegions_gpr, State.callEntry_gpr _ h]
  exact sSave_gpr n _ s (fun e => h (by rw [e]; decide)) (fun e => h (by rw [e]; decide))

theorem eEntryS_d8 (sig : Sig) (n : String) (s : State) : D8 n (eEntryS sig n s) := sSave_d8 n _ s

theorem allRegions_eEntryS (sig : Sig) (n : String) (s : State) :
    allRegions sig (eEntryS sig n s) = allRegions sig (sSave n (nStack sig) s).callEntry := rfl

/-- The function's arguments at its entry are the caller's. -/
theorem allArgs_eEntryS (n : String) (s : State) (hE : frameS (nStack sig) ≤ 32768) :
    allArgs sig (eEntryS sig n s) = allArgs sig s := by
  have h1 : (argRegs.take (sig.words abi.ptrBits).length).map (eEntryS sig n s).gpr =
      (argRegs.take (sig.words abi.ptrBits).length).map s.gpr :=
    List.map_congr_left fun q hq => eEntryS_gpr sig n s (argRegs_not_link q (List.mem_of_mem_take hq))
  have h2 : (List.range (nStack sig)).map (stackArg (eEntryS sig n s)) =
      (List.range (nStack sig)).map (stackArg s) := List.map_congr_left fun j hj => by
    have hj' := List.mem_range.mp hj
    show (eEntryS sig n s).mem.readW ((eEntryS sig n s).sp + BitVec.ofNat 64 (8 * j)) 64 = _
    rw [eEntryS_mem, eEntryS_sp]
    exact sSave_args n _ s hE hj'
  rw [allArgs, allArgs, h1, h2]

theorem frameS_pos (k : Nat) : 0 < frameS k := by unfold frameS; omega

/-- What the caller's precondition gives the entry. -/
theorem s_facts (hA : ArgsOk sig) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + frameS (nStack sig)) leak).pre s) :
    stack + frameS (nStack sig) ≤ s.sp.toNat ∧ s.sp.toNat + 8 * nStack sig ≤ 2 ^ 64 ∧
      (∀ j < nStack sig, InRegions s.rd (stackArgAddr s j) 8) ∧
      ∀ a ∈ allRegions sig s, (below s.sp (stack + frameS (nStack sig))).Disjoint a.1 := by
  have hE := frameS_pos (nStack sig)
  rw [pre_args hA hl] at hs
  obtain ⟨⟨hst, hfit⟩, hrd, -, -, hres, -, -⟩ := hs
  have hsb : stack + frameS (nStack sig) ≤ s.sp.toNat := by rcases hst with h | h <;> omega
  refine ⟨hsb, hfit, fun j hj => ?_, fun a ha =>
    hres _ (by rw [stackBelow_pos _ (by omega)]; exact List.mem_singleton_self _) a ha⟩
  have h0 : nStack sig ≠ 0 := by omega
  have hmem : (⟨stackArgAddr s 0, 8 * nStack sig⟩, false) ∈ allRegions sig s := by
    simp [allRegions, argArea, h0]
  refine ⟨⟨stackArgAddr s 0, 8 * nStack sig⟩, ?_, ?_⟩
  · rw [hrd]; exact List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  · simp only [stackArgAddr]
    exact Offset.contains _ (d := 8 * j) (n := 8) (e := 8 * 0) (k := 8 * nStack sig)
      (by omega) (by omega) (by omega)

/-- The function's regions at its entry: the caller's buffers, and the
copies. -/
theorem allRegions_eEntryS' (n : String) (s : State) (hE : frameS (nStack sig) ≤ 32768) :
    allRegions sig (eEntryS sig n s) = Sig.bufs sig.params (allArgs sig s) ++ argArea sig (eEntryS sig n s) := by
  rw [allRegions, allArgs_eEntryS n s hE]

/-- The copies lie in the stack below the caller's `sp` its contract reserves. -/
theorem argArea_eEntryS_sub (n : String) (s : State) :
    ∀ b ∈ argArea sig (eEntryS sig n s), Region.Sub b.1 (below s.sp (stack + frameS (nStack sig))) := by
  intro b hb
  unfold argArea at hb
  split at hb
  · cases hb
  · simp only [List.mem_singleton] at hb; subst hb
    have hsk := saveOff_ge (nStack sig)
    have hfs : saveOff (nStack sig) + 16 = frameS (nStack sig) := rfl
    show Region.Sub ⟨stackArgAddr (eEntryS sig n s) 0, 8 * nStack sig⟩ _
    rw [stackArgAddr, eEntryS_sp, Nat.mul_zero, BitVec.add_zero]
    exact Offset.sub_below _ (by omega) (by omega)

/-- The caller's precondition gives the function's at its entry. -/
theorem s_bodyPre (hA : ArgsOk sig) (hl : Sig.noLists sig.params = true) {n : String}
    (hE : frameS (nStack sig) ≤ 32768)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + frameS (nStack sig)) leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre (eEntryS sig n s) := by
  obtain ⟨hsb, hfit, -, hout⟩ := s_facts hA hl hs
  have hF := frameS_pos (nStack sig)
  have hsk := saveOff_ge (nStack sig)
  have hfs : saveOff (nStack sig) + 16 = frameS (nStack sig) := rfl
  rw [pre_args hA hl] at hs
  obtain ⟨-, -, -, hpw, -, hnw, hpr⟩ := hs
  have hbufs : ∀ a ∈ Sig.bufs sig.params (allArgs sig s), (below s.sp (stack + frameS (nStack sig))).Disjoint a.1 :=
    fun a ha => hout a (List.mem_append_left _ ha)
  refine (pre_args hA hl).mpr ⟨⟨.inr ?_, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [eEntryS_sp, toNat_sub_ofNat' (by omega)]; omega
  · rw [eEntryS_sp, toNat_sub_ofNat' (by omega)]; omega
  · rw [allRegions_eEntryS' n s hE]
    refine List.pairwise_append.mpr ⟨(List.pairwise_append.mp hpw).1, ?_, fun a ha b hb _ => ?_⟩
    · unfold argArea; split <;> simp
    · exact ((hbufs a ha).sub_left (argArea_eEntryS_sub (stack := stack) n s b hb)).symm
  · intro r hr a ha
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hr
    rw [stackBelow_pos _ h0, List.mem_singleton] at hr; subst hr
    rw [allRegions_eEntryS' n s hE] at ha
    rcases List.mem_append.mp ha with ha | ha
    · rw [eEntryS_sp]
      exact (hbufs a ha).sub_left (by
        have := below_below s.sp (frameS (nStack sig)) stack
        exact this)
    · unfold argArea at ha
      split at ha
      · cases ha
      · simp only [List.mem_singleton] at ha; subst ha
        show (below (eEntryS sig n s).sp stack).Disjoint ⟨stackArgAddr (eEntryS sig n s) 0, 8 * nStack sig⟩
        rw [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
        exact (Offset.base_disjoint_below _ (by omega)).symm
  · rw [allArgs_eEntryS n s hE]; exact hnw
  · rw [allArgs_eEntryS n s hE, eEntryS_mem]
    refine hpre _ _ _ (allArgs_length sig s) (fun b hb x hx => ?_) hpr
    refine (sSave_frame n _ s hE x fun R hR hc => ?_).symm
    simp only [List.mem_singleton] at hR; subst hR
    exact hbufs b hb x (below_sub (by omega) (by omega) x hc) hx

end

end VG.Proof.Sha3.AArch64
