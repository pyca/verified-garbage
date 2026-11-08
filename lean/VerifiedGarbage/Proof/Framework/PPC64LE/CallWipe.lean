module

public import VerifiedGarbage.Impl.CallWipe.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Spec.Zeroize.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Sig

/-!
# A call that wipes part of a buffer afterwards (PPC64LE)

`Verified.callWipe`: a function verified against `sig.contract` with `stack`
bytes of stack (`sdepth body ≤ stack`), whose arguments are all in
registers, one of them (in `argRegs[i]`) a writable array of `k` elements
`e`, is verified against the same contract with `stack + fs` bytes when
called by `callWipe` with a frame of `fs` bytes (`FrameOk fs`), which then zeroes the first `n ≤ k * e.size` bytes of
the array with a function verified against `Spec.Zeroize.zeroizeContract`,
and returns the first function's result; `Verified.callWipe'` adds to the
postcondition that those bytes are zero on return.

`callWipe` saves the link register in `r0`, allocates its frame (`cwPush`,
`alloc fs`), and saves `r0` and `r31` in the frame's first two doublewords
above its header (`cwSave`); `r31`
holds the array's address across the first call and the first function's
result across the second. Each callee runs from the state after its call
with the permissions of its own contract: the buffers for the first, the
`n` bytes for the zeroize function (`WP.callAny`). The frame is memory the
first function's contract reads on entry, which the caller's says nothing
of: the precondition, postcondition and leak must read the memory on entry
only within the function's buffers (`hpre`, `hpost`, `hleak`). The zeroize
function writes the array after the first function returned: the
postcondition must read the memory on return only within the buffers apart
from the array (`hpostOut`), which the precondition keeps apart from the
others (it is writable).

Constant time: the frame's accesses depend on the stack pointer alone, each
callee is constant time, and the zeroize function's arguments, the array's
address and `n`, are public.
-/

@[expose] public section

namespace VG.PPC64LE

open VG.Impl.CallWipe.PPC64LE

/-! ## Argument registers -/

theorem argRegs_not_frame : ∀ q ∈ argRegs, q ≠ .r0 ∧ q ≠ .r11 ∧ q ≠ .r12 ∧ q ≠ .r31 := by decide

theorem regArgs_congr (sig : Sig) {s s' : State}
    (h : ∀ q, q ≠ .r0 → q ≠ .r11 → q ≠ .r12 → q ≠ .r31 → s'.gpr q = s.gpr q) :
    regArgs sig s' = regArgs sig s :=
  List.map_congr_left fun q hq =>
    let h' := argRegs_not_frame q (List.mem_of_mem_take hq)
    h q h'.1 h'.2.1 h'.2.2.1 h'.2.2.2

theorem regArgs_getD (g : Reg → BitVec 64) {L i : Nat} (hL : L ≤ 8) (hi : i < L) :
    ((argRegs.take L).map g).getD i 0 = g (argRegs.getD i .r3) := by
  have hi8 : i < argRegs.length := by simp only [argRegs, List.length_cons, List.length_nil]; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take, hi, ite_true,
    List.getElem?_eq_getElem hi8, Option.map_some, Option.getD_some]

/-! ## The array among the parameters -/

theorem Sig.bufs_mem_array {w : Bool} {e : Elem} {k : Nat} {nm : String} (ps₂ : List (String × Param)) :
    ∀ (ps₁ : List (String × Param)) (vs : List (BitVec 64)),
      (ps₁.flatMap fun p => p.2.words 64).length < vs.length →
      (⟨vs.getD (ps₁.flatMap fun p => p.2.words 64).length 0, k * e.size⟩, w) ∈
        Sig.bufs (ps₁ ++ (nm, .array w e k) :: ps₂) vs
  | [], p :: vs, _ => List.mem_cons_self ..
  | (_, .int ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_1, List.length_append, List.length_cons,
      List.length_nil] at h ⊢
    simp only [List.cons_append, Sig.bufs, show 0 + 1 + (ps.flatMap fun p => p.2.words 64).length =
      (ps.flatMap fun p => p.2.words 64).length + 1 by omega, List.getD_cons_succ]
    exact Sig.bufs_mem_array ps₂ ps vs (by omega)
  | (_, .array ..) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_2, List.length_append, List.length_cons,
      List.length_nil] at h ⊢
    simp only [List.cons_append, Sig.bufs, show 0 + 1 + (ps.flatMap fun p => p.2.words 64).length =
      (ps.flatMap fun p => p.2.words 64).length + 1 by omega, List.getD_cons_succ]
    exact List.mem_cons_of_mem _ (Sig.bufs_mem_array ps₂ ps vs (by omega))
  | (_, .slice ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_3, List.length_append, List.length_cons,
      List.length_nil] at h ⊢
    simp only [List.cons_append, Sig.bufs, show 0 + 1 + 1 + (ps.flatMap fun p => p.2.words 64).length =
      (ps.flatMap fun p => p.2.words 64).length + 1 + 1 by omega, List.getD_cons_succ]
    exact List.mem_cons_of_mem _ (Sig.bufs_mem_array ps₂ ps vs (by omega))
  | (_, .slices ..) :: ps, v :: l :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_4, List.length_append, List.length_cons,
      List.length_nil] at h ⊢
    simp only [List.cons_append, Sig.bufs, show 0 + 1 + 1 + (ps.flatMap fun p => p.2.words 64).length =
      (ps.flatMap fun p => p.2.words 64).length + 1 + 1 by omega, List.getD_cons_succ]
    exact Sig.bufs_mem_array ps₂ ps vs (by omega)
  | (_, .table _) :: ps, v :: vs, h => by
    simp only [List.flatMap_cons, Param.words.eq_5, List.length_append, List.length_cons,
      List.length_nil] at h ⊢
    simp only [List.cons_append, Sig.bufs, show 0 + 1 + (ps.flatMap fun p => p.2.words 64).length =
      (ps.flatMap fun p => p.2.words 64).length + 1 by omega, List.getD_cons_succ]
    exact Sig.bufs_mem_array ps₂ ps vs (by omega)
  | [], [], h => by simp at h
  | (_, .int ..) :: _, [], h => by simp at h
  | (_, .array ..) :: _, [], h => by simp at h
  | (_, .slice ..) :: _, [], h => by simp at h
  | (_, .slice ..) :: _, [_], h => by simp [Param.words.eq_3] at h
  | (_, .slices ..) :: _, [], h => by simp at h
  | (_, .slices ..) :: _, [_], h => by simp [Param.words.eq_4] at h
  | (_, .table _) :: _, [], h => by simp at h

/-- The array's address is a public argument, of 64 bits. -/
theorem Sig.pub_array {w : Bool} {e : Elem} {k : Nat} {nm : String} (ps₁ ps₂ : List (String × Param)) :
    ((ps₁ ++ (nm, .array w e k) :: ps₂).flatMap (·.2.pubs)).getD
        (ps₁.flatMap fun p => p.2.words 64).length false = true ∧
      (((ps₁ ++ (nm, .array w e k) :: ps₂).flatMap fun p => p.2.words 64).map (·.bits 64)).getD
        (ps₁.flatMap fun p => p.2.words 64).length 64 = 64 := by
  rw [← Sig.pubs_length ps₁ 64]
  simp only [List.flatMap_append, List.flatMap_cons, List.getD_eq_getElem?_getD, List.map_append]
  constructor
  · rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  · rw [List.getElem?_append_right (by rw [List.length_map, Sig.pubs_length]), List.length_map,
      Sig.pubs_length, Nat.sub_self]; rfl

/-! ## The frame -/

/-- The frame's sizes: a multiple of 16 (the ABI's alignment of the stack
pointer), at least 48 bytes (the 32-byte header and the two saved
doublewords), and less than a page (`alloc`). -/
abbrev FrameOk (fs : Nat) : Prop := 48 ≤ fs ∧ fs < 4096 ∧ fs % 16 = 0

theorem FrameOk.alloc {fs : Nat} (h : FrameOk fs) : 32 < fs ∧ fs < 4096 ∧ fs % 16 = 0 :=
  ⟨by omega, h.2.1, h.2.2⟩

/-- The stack pointer in the frame. -/
abbrev fsp (fs : Nat) (s : State) : Addr := s.sp - BitVec.ofNat 64 fs

/-- The frame's doubleword that saves the link register. -/
abbrev slotLr (fs : Nat) (s : State) : Addr := fsp fs s + BitVec.ofNat 64 32

/-- The frame's doubleword that saves `r31`. -/
abbrev slot31 (fs : Nat) (s : State) : Addr := slotLr fs s + BitVec.ofNat 64 8

theorem slot31_eq (fs : Nat) (s : State) : slot31 fs s = fsp fs s + BitVec.ofNat 64 40 :=
  Offset.add_add _ 32 8

/-- `off` bytes above the frame's stack pointer, within the `n + fs` bytes
below the stack pointer. -/
theorem frame_below_contains (sp : Addr) {n fs off k : Nat} (hst : n + fs < 2 ^ 64) (ho : off + k ≤ fs) :
    (below sp (n + fs)).Contains (sp - BitVec.ofNat 64 fs + BitVec.ofNat 64 off) k := by
  rw [Offset.sub_ofNat_eq sp (show fs ≤ n + fs by omega), Offset.add_add]
  exact Offset.contains_base _ (by omega) (by omega)

/-- The back chain, within the `n + fs` bytes below the stack pointer. -/
theorem chain_below_contains (sp : Addr) {n fs : Nat} (hst : n + fs < 2 ^ 64) (h : 8 ≤ fs) :
    (below sp (n + fs)).Contains (sp - BitVec.ofNat 64 fs) 8 :=
  Offset.contains_below sp (a := fs) (b := n + fs) (by omega) (by omega) hst

/-- The frame's local variable space, within the `n + fs` bytes below the
stack pointer. -/
theorem frameR_below (s : State) {n fs : Nat} (h : 32 ≤ fs) :
    Region.Sub (frameR fs s) (below s.sp (n + fs)) := by
  show Region.Sub ⟨s.sp - BitVec.ofNat 64 fs + 32, fs - 32⟩ _
  rw [sub_add_header _ h]
  exact Offset.sub_below _ (by omega) (by omega)

/-- `off` bytes above the frame's stack pointer, within its local variable
space. -/
theorem frameR_contains (s : State) {fs off k : Nat} (h₁ : 32 ≤ off) (h₂ : off + k ≤ fs)
    (h₃ : fs < 2 ^ 64) : (frameR fs s).Contains (fsp fs s + BitVec.ofNat 64 off) k :=
  Offset.contains (fsp fs s) (e := 32) (d := off) (k := fs - 32) (n := k) h₁ (by omega) (by omega)

/-- The frame's local variable space is not below the frame. -/
theorem frameR_not_below (s : State) {n fs : Nat} (h : 32 ≤ fs) (hn : n + fs < 2 ^ 64) :
    Region.Disjoint (frameR fs s) (below (fsp fs s) n) :=
  Offset.disjoint_below (fsp fs s) (n := n) (d := 32) (k := fs - 32) (by omega)

theorem slotLr_contains {fs : Nat} (hfs : FrameOk fs) (s : State) : (frameR fs s).Contains (slotLr fs s) 8 :=
  frameR_contains s (Nat.le_refl _) (by omega) (by omega)

theorem slot31_contains {fs : Nat} (hfs : FrameOk fs) (s : State) : (frameR fs s).Contains (slot31 fs s) 8 := by
  rw [slot31_eq]; exact frameR_contains s (by decide) (by omega) (by omega)

/-! ## The blocks -/

/-- The state after `mflr r0` and the frame's push. -/
def cwPush (fs : Nat) (s : State) : State := allocated fs (s.write .r0 s.lr)

section
variable {fs : Nat}

@[simp] theorem cwPush_sp (s : State) : (cwPush fs s).sp = fsp fs s := rfl
@[simp] theorem cwPush_rd (s : State) : (cwPush fs s).rd = s.rd := rfl
@[simp] theorem cwPush_wr (s : State) : (cwPush fs s).wr = frameR fs s :: s.wr := rfl
@[simp] theorem cwPush_lr (s : State) : (cwPush fs s).lr = s.lr := rfl
theorem cwPush_mem (s : State) : (cwPush fs s).mem = s.mem.write (fsp fs s) 8 s.sp := rfl
theorem cwPush_gpr (s : State) {q : Reg} (h : q ≠ .r0) : (cwPush fs s).gpr q = s.gpr q := by
  show (s.write .r0 s.lr).gpr q = s.gpr q
  exact RegUpd.gpr_write_of_ne _ _ h
theorem cwPush_r0 (s : State) : (cwPush fs s).gpr .r0 = s.lr := by
  show (s.write .r0 s.lr).gpr .r0 = s.lr
  exact RegUpd.gpr_write_self _ _ _

/-- The state after `addi r12, r1, 32`. -/
def cwLr (fs : Nat) (s : State) : State := (cwPush fs s).write .r12 (slotLr fs s)

/-- The state after `saveArg r`: the link register and `r31` saved, the
array's address in `r31`. -/
def cwSave (fs : Nat) (r : Reg) (s : State) : State :=
  ({ cwLr fs s with mem := ((cwPush fs s).mem.writeW (slotLr fs s) s.lr).writeW (slot31 fs s) (s.gpr .r31) }).write
    .r31 (s.gpr r)

@[simp] theorem cwSave_sp (r : Reg) (s : State) : (cwSave fs r s).sp = fsp fs s := rfl
@[simp] theorem cwSave_rd (r : Reg) (s : State) : (cwSave fs r s).rd = s.rd := rfl
@[simp] theorem cwSave_wr (r : Reg) (s : State) : (cwSave fs r s).wr = frameR fs s :: s.wr := rfl
@[simp] theorem cwSave_lr (r : Reg) (s : State) : (cwSave fs r s).lr = s.lr := rfl
theorem cwSave_mem (r : Reg) (s : State) :
    (cwSave fs r s).mem = ((cwPush fs s).mem.writeW (slotLr fs s) s.lr).writeW (slot31 fs s) (s.gpr .r31) := rfl
theorem cwSave_r31 (r : Reg) (s : State) : (cwSave fs r s).gpr .r31 = s.gpr r :=
  RegUpd.gpr_write_self _ _ _
theorem cwSave_gpr (r : Reg) (s : State) {q : Reg} (h0 : q ≠ .r0) (h12 : q ≠ .r12) (h31 : q ≠ .r31) :
    (cwSave fs r s).gpr q = s.gpr q := by
  show (State.write _ .r31 (s.gpr r)).gpr q = _
  rw [RegUpd.gpr_write_of_ne _ _ h31]
  show ((cwPush fs s).write .r12 (slotLr fs s)).gpr q = _
  rw [RegUpd.gpr_write_of_ne _ _ h12, cwPush_gpr s h0]

theorem cwLr_r12 (s : State) : (cwLr fs s).gpr .r12 = slotLr fs s := RegUpd.gpr_write_self _ _ _

end

theorem mflr_run (s : State) : execBlock isa [.mflr .r0] s = some (s.write .r0 s.lr, []) := rfl

theorem addSp_run (d : Reg) {imm : Nat} (h : imm < 2 ^ 15) (s : State) :
    exec (.addSp d imm) s = some (s.write d (s.sp + BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ite_true]

theorem saveArg_run {fs : Nat} (hfs : FrameOk fs) {r : Reg} (hr0 : r ≠ .r0) (hr12 : r ≠ .r12) (s : State) :
    execBlock isa (saveArg r) (cwPush fs s) =
      some (cwSave fs r s, [.addr (slotLr fs s + BitVec.ofNat 64 0), .addr (slot31 fs s)]) := by
  have ha : exec (.addSp .r12 32) (cwPush fs s) = some (cwLr fs s) :=
    addSp_run (s := cwPush fs s) .r12 (show 32 < 2 ^ 15 by decide)
  have hin0 : InRegions (cwLr fs s).wr ((cwLr fs s).gpr .r12 + BitVec.ofNat 64 0) 8 := by
    rw [cwLr_r12, BitVec.add_zero]; exact ⟨_, List.mem_cons_self .., slotLr_contains hfs s⟩
  have hs0 := exec_std (t := .r0) (off := 0) (by decide) hin0
  have hin8 : ∀ m : Mem, InRegions ({ cwLr fs s with mem := m } : State).wr
      (({ cwLr fs s with mem := m } : State).gpr .r12 + BitVec.ofNat 64 8) 8 := fun m => by
    show InRegions (cwLr fs s).wr ((cwLr fs s).gpr .r12 + BitVec.ofNat 64 8) 8
    rw [cwLr_r12]; exact ⟨_, List.mem_cons_self .., slot31_contains hfs s⟩
  have hs8 := fun m => exec_std (s := { cwLr fs s with mem := m }) (t := .r31) (off := 8) (by decide) (hin8 m)
  have g0 : (cwLr fs s).gpr .r0 = s.lr := by
    rw [cwLr, RegUpd.gpr_write_of_ne _ _ (by decide), cwPush_r0]
  have g31 : (cwLr fs s).gpr .r31 = s.gpr .r31 := by
    rw [cwLr, RegUpd.gpr_write_of_ne _ _ (by decide), cwPush_gpr _ (by decide)]
  have gr : (cwLr fs s).gpr r = s.gpr r := by
    rw [cwLr, RegUpd.gpr_write_of_ne _ _ hr12, cwPush_gpr _ hr0]
  simp only [saveArg, mov, execBlock, isa, ha, hs0, hs8, exec_or_self, Option.map_some, addrs, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, cwLr_r12, BitVec.add_zero, g0, g31, gr]
  rfl

/-- `li r4, 0; oris r4, r4, n >> 16; ori r4, r4, n` leaves `n`. -/
theorem li32 {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 0 ||| (BitVec.ofNat 16 (n / 2 ^ 16)).setWidth 64 <<< 16) |||
      (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have key : (n / 2 ^ 16) <<< 16 ||| n % 2 ^ 16 = n := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)), Nat.shiftLeft_eq]; omega
  have e1 : n / 2 ^ 16 % 2 ^ 16 = n / 2 ^ 16 := Nat.mod_eq_of_lt (by omega)
  have e2 : n % 2 ^ 16 % 2 ^ 64 = n % 2 ^ 16 := Nat.mod_eq_of_lt (by omega)
  have e3 : n / 2 ^ 16 % 2 ^ 64 = n / 2 ^ 16 := Nat.mod_eq_of_lt (by omega)
  have e4 : (n / 2 ^ 16) <<< 16 % 2 ^ 64 = (n / 2 ^ 16) <<< 16 := Nat.mod_eq_of_lt (by
    rw [Nat.shiftLeft_eq]; omega)
  have e5 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.zero_mod, Nat.zero_or, e1, e2, e3, e4, e5, key]

/-- The state after `zeroArgs n`: the result in `r31`, the array's address in
`r3`, `n` in `r4`. -/
def cwZero (n : Nat) (c : State) : State :=
  (((c.write .r11 (c.gpr .r3)).write .r3 (c.gpr .r31)).write .r4 (BitVec.ofNat 64 n)).write .r31 (c.gpr .r3)

@[simp] theorem cwZero_rd (n : Nat) (c : State) : (cwZero n c).rd = c.rd := rfl
@[simp] theorem cwZero_wr (n : Nat) (c : State) : (cwZero n c).wr = c.wr := rfl
@[simp] theorem cwZero_sp (n : Nat) (c : State) : (cwZero n c).sp = c.sp := rfl
@[simp] theorem cwZero_lr (n : Nat) (c : State) : (cwZero n c).lr = c.lr := rfl
@[simp] theorem cwZero_mem (n : Nat) (c : State) : (cwZero n c).mem = c.mem := rfl
theorem cwZero_r3 (n : Nat) (c : State) : (cwZero n c).gpr .r3 = c.gpr .r31 := by
  rw [cwZero, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide),
    RegUpd.gpr_write_self]
theorem cwZero_r4 (n : Nat) (c : State) : (cwZero n c).gpr .r4 = BitVec.ofNat 64 n := by
  rw [cwZero, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_self]
theorem cwZero_r31 (n : Nat) (c : State) : (cwZero n c).gpr .r31 = c.gpr .r3 := by
  rw [cwZero, RegUpd.gpr_write_self]
theorem cwZero_gpr (n : Nat) (c : State) {q : Reg} (h3 : q ≠ .r3) (h4 : q ≠ .r4) (h11 : q ≠ .r11)
    (h31 : q ≠ .r31) : (cwZero n c).gpr q = c.gpr q := by
  simp only [cwZero, RegUpd.gpr_write, h3, h4, h11, h31, ↓reduceIte]

theorem zeroArgs_run {n : Nat} (hn : n < 2 ^ 32) (c : State) :
    execBlock isa (zeroArgs n) c = some (cwZero n c, []) := by
  simp only [zeroArgs, mov, execBlock, isa, exec_or_self, exec_li (show 0 < 2 ^ 15 by decide), exec_oris,
    exec_ori, Option.map_some, addrs, List.map_nil, List.nil_append]
  simp only [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (show ¬Reg.r11 = .r4 by decide),
    RegUpd.gpr_write_of_ne _ _ (show ¬Reg.r11 = .r3 by decide), li32 hn]
  simp only [cwZero, State.write, Option.some.injEq, Prod.mk.injEq, and_true]
  congr 1; funext q; by_cases h : q = .r4 <;> simp [h]


/-- The state after `restoreRet`, from `g`: the result in `r3`, `r31` and
the saved link register (in `r0`) restored from their slots. -/
def cwRestore (g : State) : State :=
  (((g.write .r3 (g.gpr .r31)).write .r12 (g.sp + BitVec.ofNat 64 32)).write .r31
    (g.mem.readW (g.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) 64)).write .r0
    (g.mem.readW (g.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 0) 64)

theorem restoreRet_run {g : State}
    (h₀ : InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 0) 8)
    (h₈ : InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) 8) :
    execBlock isa restoreRet g = some (cwRestore g, [.addr (g.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 8),
      .addr (g.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 0)]) := by
  have ha := addSp_run (s := g.write .r3 (g.gpr .r31)) .r12 (show 32 < 2 ^ 15 by decide)
  have h12 : ((g.write .r3 (g.gpr .r31)).write .r12 (g.sp + BitVec.ofNat 64 32)).gpr .r12 =
      g.sp + BitVec.ofNat 64 32 := RegUpd.gpr_write_self _ _ _
  have h12' : (((g.write .r3 (g.gpr .r31)).write .r12 (g.sp + BitVec.ofNat 64 32)).write .r31
      (g.mem.readW (g.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) 64)).gpr .r12 = g.sp + BitVec.ofNat 64 32 := by
    rw [RegUpd.gpr_write_of_ne _ _ (by decide), h12]
  have hl8 := exec_ld (s := (g.write .r3 (g.gpr .r31)).write .r12 (g.sp + BitVec.ofNat 64 32))
    (t := .r31) (off := 8) (by decide) (by rw [h12]; exact h₈)
  have hl0 := exec_ld (s := ((g.write .r3 (g.gpr .r31)).write .r12 (g.sp + BitVec.ofNat 64 32)).write .r31
      (g.mem.readW (g.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) 64))
    (t := .r0) (off := 0) (by decide) (by rw [h12']; exact h₀)
  simp only [RegUpd.mem_write, h12, h12'] at hl8 hl0
  simp only [restoreRet, mov, execBlock, isa, exec_or_self, ha, hl8, hl0, Option.map_some, addrs, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, h12, h12', RegUpd.sp_write]
  rfl

theorem mtlr_run (g : State) :
    execBlock isa [.mtlr .r0] g = some ({ g with lr := g.gpr .r0 }, []) := rfl

/-! ## What the frame keeps -/

theorem preserved_ne : ∀ q ∈ preserved, q ≠ .r0 ∧ q ≠ .r3 ∧ q ≠ .r4 ∧ q ≠ .r11 ∧ q ≠ .r12 := by decide

section
variable {fs : Nat}

/-- What `mflr`, the push and `saveArg` write: the frame's back chain, the
link register and `r31`. -/
theorem cwSave_frame (hfs : FrameOk fs) (r : Reg) (s : State) {n : Nat} (hn : n + fs < 2 ^ 64) :
    Frame [below s.sp (n + fs)] s.mem (cwSave fs r s).mem := by
  rw [cwSave_mem, cwPush_mem, slot31_eq]
  exact Frame.writeW (Frame.writeW (Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _
    (chain_below_contains s.sp hn (by omega))) (List.mem_singleton_self _) _
    (frame_below_contains s.sp hn (off := 32) (by omega))) (List.mem_singleton_self _) _
    (frame_below_contains s.sp hn (off := 40) (by omega))

/-- The saved link register, in the frame. -/
theorem cwSave_lr_slot (r : Reg) (s : State) : (cwSave fs r s).mem.readW (slotLr fs s) 64 = s.lr := by
  rw [cwSave_mem, slot31_eq, Mem.readW_writeW_sep (Offset.sep (fsp fs s) (d := 32) (n := 8) (e := 40) (k := 8)
    (.inl (by decide)) (by decide) (by decide) : Mem.Sep (slotLr fs s) 8 (fsp fs s + BitVec.ofNat 64 40) 8)
    (by decide)]
  exact Mem.readW_writeW_self64 _ _ _

/-- The saved `r31`, in the frame. -/
theorem cwSave_r31_slot (r : Reg) (s : State) : (cwSave fs r s).mem.readW (slot31 fs s) 64 = s.gpr .r31 := by
  rw [cwSave_mem]; exact Mem.readW_writeW_self64 _ _ _

end

/-! ## The caller's contract -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack fs : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- What the caller's contract gives of the stack. -/
theorem cw_sp (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + fs) leak).pre s) : stack + fs ≤ s.sp.toNat := by
  rw [pre_regs hk hl] at hs
  rcases hs.1 with h | h <;> omega_using [h]

/-- The stack below the stack pointer that the caller's contract reserves
lies apart from the buffers. -/
theorem cw_res (hfs : FrameOk fs) (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {s : State} (hs : (sig.contract abi pre post wa (stack + fs) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (regArgs sig s), (below s.sp (stack + fs)).Disjoint b.1 := by
  rw [pre_regs hk hl] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  exact hres _ (by rw [stackBelow_pos _ (by omega_using [hfs.1])]; exact List.mem_singleton_self _)

/-- So do the writable regions. -/
theorem cw_resW (hfs : FrameOk fs) (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {s : State} (hs : (sig.contract abi pre post wa (stack + fs) leak).pre s) :
    ∀ x ∈ s.wr, (below s.sp (stack + fs)).Disjoint x := by
  have hres := cw_res hfs hk hl hs
  rw [pre_regs hk hl] at hs
  intro x hx
  rw [hs.2.2.1] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact hres b (List.mem_filter.mp hb).1

/-- The state the first function runs from, with the permissions of its
contract: after the call. -/
def cwEntry (fs : Nat) (r : Reg) (s : State) : State := (cwSave fs r s).callEntry.withRegions s.rd s.wr

theorem cwEntry_gpr (r : Reg) (s : State) {q : Reg} (h0 : q ≠ .r0) (h11 : q ≠ .r11) (h12 : q ≠ .r12)
    (h31 : q ≠ .r31) : (cwEntry fs r s).gpr q = s.gpr q := by
  have hl : q ∉ linkRegs := by
    simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h0, h11, h12⟩
  rw [cwEntry, State.withRegions_gpr, State.callEntry_gpr _ hl, cwSave_gpr r s h0 h12 h31]

theorem cwEntry_sp (r : Reg) (s : State) : (cwEntry fs r s).sp = fsp fs s := rfl
theorem cwEntry_mem (r : Reg) (s : State) : (cwEntry fs r s).mem = (cwSave fs r s).mem := rfl

theorem cwEntry_regArgs (sig : Sig) (r : Reg) (s : State) : regArgs sig (cwEntry fs r s) = regArgs sig s :=
  regArgs_congr sig fun _ h0 h11 h12 h31 => cwEntry_gpr r s h0 h11 h12 h31

/-- The entry's memory is the caller's in the buffers. -/
theorem cw_agree (hfs : FrameOk fs) (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hst : stack + fs < 2 ^ 64) (r : Reg) {s : State}
    (hs : (sig.contract abi pre post wa (stack + fs) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (regArgs sig s), ∀ x, b.1.Contains x 1 → (cwEntry fs r s).mem x = s.mem x :=
  fun b hb x hx => cwSave_frame hfs r s hst x fun R hR hc => by
    simp only [List.mem_singleton] at hR; subst hR
    exact cw_res hfs hk hl hs b hb x hc hx

/-- The caller's precondition gives the first function's at its entry. -/
theorem cw_bodyPre (hfs : FrameOk fs) (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hst : stack + fs < 2 ^ 64) {r : Reg}
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + fs) leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre (cwEntry fs r s) := by
  have hsb := cw_sp hk hl hs
  have hag := cw_agree hfs hk hl hst r hs
  have hres := cw_res hfs hk hl hs
  rw [pre_regs hk hl] at hs
  obtain ⟨-, hrd, hwr, hpw, -, hnw, hpr⟩ := hs
  refine (pre_regs hk hl).mpr ?_
  rw [cwEntry_regArgs, cwEntry_sp]
  refine ⟨.inr ?_, hrd, hwr, hpw, fun x hx a ha => ?_, hnw, ?_⟩
  · show stack ≤ (s.sp - BitVec.ofNat 64 fs).toNat
    rw [toNat_sub_ofNat' (by omega_using [hsb])]; omega_using [hsb]
  · rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hx
    · rw [stackBelow_pos _ h0, List.mem_singleton] at hx; subst hx
      exact (hres a ha).sub_left (below_below s.sp fs stack)
  · exact hpre _ _ _ (regArgs_length sig s hk) (fun b hb x hx => (hag b hb x hx).symm) hpr

/-- The caller's public data is the first function's at its entry. -/
theorem cw_bodyPub (hfs : FrameOk fs) (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hst : stack + fs < 2 ^ 64) (r : Reg) {s₁ s₂ : State}
    (h₁ : (sig.contract abi pre post wa (stack + fs) leak).pre s₁)
    (h₂ : (sig.contract abi pre post wa (stack + fs) leak).pre s₂)
    (hp : (sig.contract abi pre post wa (stack + fs) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak) :
    (sig.contract abi pre post wa stack leak).pub (cwEntry fs r s₁) (cwEntry fs r s₂) := by
  rw [pub_regsL hk hl] at hp ⊢
  obtain ⟨⟨hsp, hlk⟩, hpa⟩ := hp
  rw [cwEntry_regArgs, cwEntry_regArgs, cwEntry_sp, cwEntry_sp, fsp, fsp, hsp]
  refine ⟨⟨rfl, ?_⟩, hpa⟩
  cases leak with
  | none => trivial
  | some f =>
    show Curry.apply _ f (regArgs sig s₁) (cwEntry fs r s₁).mem = Curry.apply _ f (regArgs sig s₂) (cwEntry fs r s₂).mem
    rw [hleak _ _ _ (regArgs_length sig s₁ hk) (cw_agree hfs hk hl hst r h₁),
      hleak _ _ _ (regArgs_length sig s₂ hk) (cw_agree hfs hk hl hst r h₂)]
    exact hlk

/-- What the run of the first function leaves, from the caller's state `s`. -/
def AfterBody (sig : Sig) (post : sig.Post abi.ptrBits) (fs : Nat) (r : Reg) (stack : Nat) (s c : State) : Prop :=
  c.rd = s.rd ∧ c.wr = frameR fs s :: s.wr ∧ c.sp = fsp fs s ∧
  c.gpr .r31 = s.gpr r ∧ (∀ q ∈ preserved, q ≠ .r31 → c.gpr q = s.gpr q) ∧
  Frame (s.wr ++ [below (fsp fs s) stack]) (cwSave fs r s).mem c.mem ∧
  Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem c.mem ((c.gpr .r3).setWidth _)

/-- The call of the first function. -/
theorem cw_body_wp {name : String} {body : Prog isa} (hfs : FrameOk fs)
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) {r : Reg}
    (hd : sdepth body ≤ stack) (hst : stack + fs < 2 ^ 64)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {s : State} (hs : (sig.contract abi pre post wa (stack + fs) leak).pre s) :
    WP isa (.call name body) (cwSave fs r s) (AfterBody sig post fs r stack s) := by
  have hag := cw_agree hfs hk hl hst r hs
  refine WP.callAny (k := sig.contract abi pre post wa stack leak) h.1 (rd := s.rd) (wr := s.wr)
    (cw_bodyPre hfs hk hl hst hpre hs)
    (Covers.append (Covers.refl _) (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx))
    (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx) ?_ (by omega_using [hd, hst])
  intro c hrd hwr hsp hfr hcs hq
  refine ⟨hrd, hwr, hsp, by rw [hcs .r31 (by decide), cwSave_r31], fun q hq hq31 => ?_,
    Frame.below_mono hfr hd (by omega_using [hst]), ?_⟩
  · obtain ⟨h0, -, -, -, h12⟩ := preserved_ne q hq
    rw [hcs q hq, cwSave_gpr r s h0 h12 hq31]
  · rw [post_regs hk, show (cwSave fs r s).callEntry.withRegions s.rd s.wr = cwEntry fs r s from rfl,
      cwEntry_regArgs, cwEntry_mem, State.withRegions_mem, State.withRegions_gpr] at hq
    exact hpost _ _ _ _ _ (regArgs_length sig s hk) hag hq

end
/-! ## The zeroize function's contract -/

/-- The zeroize function's arguments. -/
theorem zeroize_regArgs {X : State} : regArgs Spec.Zeroize.zeroizeSig X = [X.gpr .r3, X.gpr .r4] := rfl

/-- The zeroize function's precondition, from what it says of the state. -/
theorem zeroize_pre_of {zst n : Nat} {X : State} (hn : (X.gpr .r4).toNat = n)
    (hwf : zst = 0 ∨ zst ≤ X.sp.toNat) (hrd : X.rd = []) (hwr : X.wr = [⟨X.gpr .r3, n⟩])
    (hres : ∀ x ∈ stackBelow X.sp zst, x.Disjoint ⟨X.gpr .r3, n⟩)
    (hb : (X.gpr .r3).toNat + n ≤ 2 ^ 64) :
    (Spec.Zeroize.zeroizeContract abi zst).pre X := by
  unfold Spec.Zeroize.zeroizeContract
  refine (pre_regs (by decide) (by decide)).mpr ?_
  have hbz : Sig.bufs Spec.Zeroize.zeroizeSig.params (regArgs Spec.Zeroize.zeroizeSig X) =
      [(⟨X.gpr .r3, n⟩, true)] := by
    show [((⟨X.gpr .r3, (X.gpr .r4).toNat * 1⟩ : Region), true)] = _
    rw [hn, Nat.mul_one]
  rw [hbz]
  refine ⟨hwf, hrd, hwr, List.pairwise_singleton _ _, fun x hx a ha => ?_, fun a ha => ?_, ?_⟩
  · simp only [List.mem_singleton] at ha; subst ha; exact hres x hx
  · simp only [List.mem_singleton] at ha; subst ha; exact hb
  · rw [Curry.apply_const]; trivial

/-- The zeroize function's postcondition. -/
theorem zeroize_post_iff {zst : Nat} {X Y : State} :
    (Spec.Zeroize.zeroizeContract abi zst).post X Y ↔
      Spec.Zeroize.bytesAt Y.mem (X.gpr .r3) ((X.gpr .r4).setWidth 64).toNat =
        Spec.Zeroize.zeros ((X.gpr .r4).setWidth 64).toNat := Iff.rfl

/-- The zeroize function's public data. -/
theorem zeroize_pub_of {zst : Nat} {X₁ X₂ : State} (hsp : X₁.sp = X₂.sp)
    (h3 : X₁.gpr .r3 = X₂.gpr .r3) (h4 : X₁.gpr .r4 = X₂.gpr .r4) :
    (Spec.Zeroize.zeroizeContract abi zst).pub X₁ X₂ := by
  unfold Spec.Zeroize.zeroizeContract
  refine (pub_regs (by decide) (by decide)).mpr ⟨hsp, fun i _ => ?_⟩
  rw [zeroize_regArgs, zeroize_regArgs, h3, h4]

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack fs : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {r : Reg}

/-- What the caller's contract gives of the array: its region is within the
writable ones. -/
theorem cw_array (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k : Nat} {s : State} (hs : (sig.contract abi pre post wa (stack + fs) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s)) :
    (⟨s.gpr r, k * e.size⟩ : Region) ∈ s.wr ∧ (s.gpr r).toNat + k * e.size ≤ 2 ^ 64 := by
  rw [pre_regs hk hl] at hs
  obtain ⟨-, -, hwr, -, -, hnw, -⟩ := hs
  exact ⟨hwr ▸ List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨harr, rfl⟩, rfl⟩, hnw _ harr⟩

theorem toNat_ofNat32 {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn])]

/-- The zeroize function's entry state. -/
theorem cwZeroEntry_gpr {s c : State} (hc : AfterBody sig post fs r stack s c) (n : Nat) (R : Region) :
    ((cwZero n c).callEntry.withRegions [] [R]).gpr .r3 = s.gpr r ∧
      ((cwZero n c).callEntry.withRegions [] [R]).gpr .r4 = BitVec.ofNat 64 n ∧
      ((cwZero n c).callEntry.withRegions [] [R]).sp = fsp fs s := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    cwZero_r3, cwZero_r4, hc.2.2.2.1]
  exact ⟨rfl, rfl, hc.2.2.1⟩

/-- The zeroize function's precondition, at its entry. -/
theorem cw_zeroPre (hfs : FrameOk fs) (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hst : stack + fs < 2 ^ 64)
    {e : Elem} {k n zst : Nat} {s c : State} (hs : (sig.contract abi pre post wa (stack + fs) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hzs : zst ≤ stack) (hc : AfterBody sig post fs r stack s c) :
    (Spec.Zeroize.zeroizeContract abi zst).pre
      ((cwZero n c).callEntry.withRegions [] [⟨s.gpr r, n⟩]) := by
  have hsb := cw_sp hk hl hs
  have hA := cw_res hfs hk hl hs _ harr
  have hnw := (cw_array hk hl hs harr).2
  have hsubA : Region.Sub ⟨s.gpr r, n⟩ ⟨s.gpr r, k * e.size⟩ := Region.sub_prefix hn
  obtain ⟨hdi, hsi, hsp⟩ := cwZeroEntry_gpr hc n ⟨s.gpr r, n⟩
  refine zeroize_pre_of (n := n) (by rw [hsi]; exact toNat_ofNat32 hn32) (.inr ?_) rfl
    (by rw [hdi]; rfl) ?_ (by rw [hdi]; omega_using [hnw, hn])
  · rw [hsp]
    show zst ≤ (s.sp - BitVec.ofNat 64 fs).toNat
    rw [toNat_sub_ofNat' (by omega_using [hsb])]; omega_using [hsb, hzs]
  · rw [hsp, hdi]
    intro x hx
    rcases Nat.eq_zero_or_pos zst with h0 | h0
    · subst h0; simp [stackBelow] at hx
    · rw [stackBelow_pos _ h0, List.mem_singleton] at hx; subst hx
      exact ((hA.sub_left (below_sub (a := zst + fs) (by omega_using [hzs]) hst)).sub_left
        (below_below s.sp fs zst)).sub_right hsubA

/-- The zeroize function's public data, at its entry, if the array's
address is public. -/
theorem cw_zeroPub {n zst : Nat} {s₁ s₂ c₁ c₂ : State} (hsp : s₁.sp = s₂.sp)
    (hpp : s₁.gpr r = s₂.gpr r) (hc₁ : AfterBody sig post fs r stack s₁ c₁)
    (hc₂ : AfterBody sig post fs r stack s₂ c₂) :
    (Spec.Zeroize.zeroizeContract abi zst).pub ((cwZero n c₁).callEntry.withRegions [] [⟨s₁.gpr r, n⟩])
      ((cwZero n c₂).callEntry.withRegions [] [⟨s₂.gpr r, n⟩]) := by
  obtain ⟨d₁, i₁, p₁⟩ := cwZeroEntry_gpr hc₁ n ⟨s₁.gpr r, n⟩
  obtain ⟨d₂, i₂, p₂⟩ := cwZeroEntry_gpr hc₂ n ⟨s₂.gpr r, n⟩
  exact zeroize_pub_of (by rw [p₁, p₂, fsp, fsp, hsp]) (by rw [d₁, d₂, hpp]) (by rw [i₁, i₂])

/-- What the zeroize function's run leaves, from the caller's state `s`: the
first function's, but for the first `n` bytes of the array, which are zero,
and its result, in `r31`. -/
def AfterZero (sig : Sig) (post : sig.Post abi.ptrBits) (fs : Nat) (r : Reg) (stack n : Nat) (s g : State) : Prop :=
  ∃ c, AfterBody sig post fs r stack s c ∧
    g.rd = s.rd ∧ g.wr = frameR fs s :: s.wr ∧ g.sp = fsp fs s ∧
    g.gpr .r31 = c.gpr .r3 ∧ (∀ q ∈ preserved, q ≠ .r31 → g.gpr q = s.gpr q) ∧
    Frame (s.wr ++ [below (fsp fs s) stack]) (cwSave fs r s).mem g.mem ∧
    Frame [⟨s.gpr r, n⟩, below (fsp fs s) stack] c.mem g.mem ∧
    Spec.Zeroize.bytesAt g.mem (s.gpr r) n = Spec.Zeroize.zeros n

/-- The zeroize function may write only the first `n` bytes of the array. -/
theorem cw_zeroCovers (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n : Nat} {s c : State} (hs : (sig.contract abi pre post wa (stack + fs) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hn : n ≤ k * e.size) (hc : AfterBody sig post fs r stack s c) :
    Covers [⟨s.gpr r, n⟩] (cwZero n c).wr :=
  Covers.one ⟨_, by rw [cwZero_wr, hc.2.1]; exact List.mem_cons_of_mem _ (cw_array hk hl hs harr).1, by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact hn⟩

/-- The call of the zeroize function. -/
theorem cw_zero_wp {zname : String} {zcode : Prog isa} {zst : Nat} (hfs : FrameOk fs)
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hzd : sdepth zcode ≤ zst) (hzs : zst ≤ stack) (hst : stack + fs < 2 ^ 64)
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {e : Elem} {k n : Nat} {s c : State} (hs : (sig.contract abi pre post wa (stack + fs) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hc : AfterBody sig post fs r stack s c) :
    WP isa (.call zname zcode) (cwZero n c) (AfterZero sig post fs r stack n s) := by
  obtain ⟨hAw, -⟩ := cw_array hk hl hs harr
  have hsubA : Region.Sub ⟨s.gpr r, n⟩ ⟨s.gpr r, k * e.size⟩ := Region.sub_prefix hn
  obtain ⟨hrdc, hwrc, hspc, -, hcsc, hfc, -⟩ := id hc
  have hcw := cw_zeroCovers hk hl hs harr hn hc
  refine WP.callAny (k := Spec.Zeroize.zeroizeContract abi zst) hz.1
    (cw_zeroPre hfs hk hl hst hs harr hn hn32 hzs hc) (Covers.right hcw) hcw ?_ (by omega_using [hzd, hzs, hst])
  intro g hrd hwr hsp hfr hcs hq
  rw [cwZero_sp, hspc, cwZero_mem] at hfr
  have hbz : Region.Sub (below (fsp fs s) (sdepth zcode)) (below (fsp fs s) stack) :=
    below_sub (by omega_using [hzd, hzs]) (by omega_using [hst])
  refine ⟨c, hc, by rw [hrd, cwZero_rd, hrdc], by rw [hwr, cwZero_wr, hwrc], by rw [hsp, cwZero_sp, hspc],
    by rw [hcs .r31 (by decide), cwZero_r31], fun q hq hq31 => ?_, ?_, ?_, ?_⟩
  · obtain ⟨-, h3, h4, h11, -⟩ := preserved_ne q hq
    rw [hcs q hq, cwZero_gpr n c h3 h4 h11 hq31, hcsc q hq hq31]
  · refine Frame.trans hfc (Frame.sub hfr fun x hx => ?_)
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_append_left _ hAw, hsubA⟩
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hbz⟩
  · refine Frame.sub hfr fun x hx => ?_
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hbz⟩
  · obtain ⟨hdi, hsi, -⟩ := cwZeroEntry_gpr hc n ⟨s.gpr r, n⟩
    rw [zeroize_post_iff, hdi, hsi, State.withRegions_mem, BitVec.setWidth_eq, toNat_ofNat32 hn32] at hq
    exact hq

end

/-! ## The whole call -/

/-- The state `callWipe` returns in, from the state `g` the zeroize call
leaves: `restoreRet`, the frame's pop and `mtlr r0`. -/
def cwFinal (fs : Nat) (g : State) : State :=
  { freed fs (cwRestore g) with lr := (cwRestore g).gpr .r0 }

section
variable {fs : Nat}

theorem cwFinal_gpr (g : State) {q : Reg} (h0 : q ≠ .r0) (h3 : q ≠ .r3) (h12 : q ≠ .r12) (h31 : q ≠ .r31) :
    (cwFinal fs g).gpr q = g.gpr q := by
  show (cwRestore g).gpr q = _
  rw [cwRestore, RegUpd.gpr_write_of_ne _ _ h0, RegUpd.gpr_write_of_ne _ _ h31,
    RegUpd.gpr_write_of_ne _ _ h12, RegUpd.gpr_write_of_ne _ _ h3]

theorem cwFinal_r3 (g : State) : (cwFinal fs g).gpr .r3 = g.gpr .r31 := by
  show (cwRestore g).gpr .r3 = _
  rw [cwRestore, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide),
    RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_self]

theorem cwFinal_r31 (g : State) :
    (cwFinal fs g).gpr .r31 = g.mem.readW (g.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) 64 := by
  show (cwRestore g).gpr .r31 = _
  rw [cwRestore, RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_self]

theorem cwFinal_sp (g : State) : (cwFinal fs g).sp = g.sp + BitVec.ofNat 64 fs := rfl
theorem cwFinal_mem (g : State) : (cwFinal fs g).mem = g.mem := rfl
theorem cwFinal_lr (g : State) :
    (cwFinal fs g).lr = g.mem.readW (g.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 0) 64 := by
  show (cwRestore g).gpr .r0 = _
  rw [cwRestore, RegUpd.gpr_write_self]

end

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack fs : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {r : Reg}

/-- The frame's local variable space, which the callees may not change, lies
apart from what they may. -/
theorem cw_slots (hfs : FrameOk fs) (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hst : stack + fs < 2 ^ 64) {s : State} (hs : (sig.contract abi pre post wa (stack + fs) leak).pre s) :
    ∀ x ∈ s.wr ++ [below (fsp fs s) stack], Region.Disjoint (frameR fs s) x := by
  have hresW := cw_resW hfs hk hl hs
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (hresW x hx).sub_left (frameR_below s (by omega))
  · simp only [List.mem_singleton] at hx; subst hx; exact frameR_not_below s (by omega) hst

/-- The slots, at the frame's stack pointer. -/
theorem slots_in {g : State} (s : State) (hfs : FrameOk fs) (hw : g.wr = frameR fs s :: s.wr)
    (he : g.sp = fsp fs s) :
    InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 0) 8 ∧
      InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 32 + BitVec.ofNat 64 8) 8 := by
  rw [he, hw, BitVec.add_zero]
  exact ⟨⟨_, List.mem_append_right _ (List.mem_cons_self ..), slotLr_contains hfs s⟩,
    ⟨_, List.mem_append_right _ (List.mem_cons_self ..), slot31_contains hfs s⟩⟩

/-- A run of `callWipe` from the caller's state `s`: it keeps what the
calling convention requires, its postcondition is the first function's if
that reads the memory on return only within the buffers apart from the
array (`hout`), and the first `n` bytes of the array are zero. -/
theorem cw_wp {name zname : String} {body zcode : Prog isa} {zst : Nat} (hfs : FrameOk fs)
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hr0 : r ≠ .r0) (hr12 : r ≠ .r12)
    (hd : sdepth body ≤ stack) (hzd : sdepth zcode ≤ zst) (hzs : zst ≤ stack) (hst : stack + fs < 2 ^ 64)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {e : Elem} {k n : Nat} (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32)
    {s : State} (hs : (sig.contract abi pre post wa (stack + fs) leak).pre s)
    (harr : (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s))
    (hout : ∀ m₁ m₂ x, (∀ b ∈ Sig.bufs sig.params (regArgs sig s), b.1.Disjoint ⟨s.gpr r, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₂ x) :
    WP isa (callWipe fs r n name body zname zcode) s fun G =>
      abiPreserved s G ∧ (sig.contract abi pre post wa (stack + fs) leak).post s G ∧
        Spec.Zeroize.bytesAt G.mem (s.gpr r) n = Spec.Zeroize.zeros n := by
  have hsb := cw_sp hk hl hs
  have hres := cw_res hfs hk hl hs
  have hslots := cw_slots hfs hk hl hst hs
  refine WP.seq (WP.block ⟨_, mflr_run s, ?_⟩)
  refine WP.seq (WP.alloc hfs.alloc (show fs ≤ s.sp.toNat by omega_using [hsb]) ?_)
  refine WP.seq (WP.block ⟨_, saveArg_run hfs hr0 hr12 s, ?_⟩)
  refine WP.seq (WP.mono (cw_body_wp hfs h hk hl hd hst hpre hpost hs) fun c hc => ?_)
  refine WP.seq (WP.block ⟨_, zeroArgs_run hn32 c, ?_⟩)
  refine WP.seq (WP.mono (cw_zero_wp hfs hz hzd hzs hst hk hl hs harr hn hn32 hc) fun g hg => ?_)
  obtain ⟨c', hc', -, hwrg, hspg, h31g, hcsg, hfr, hfc, hz0⟩ := hg
  have hlr : g.mem.readW (slotLr fs s) 64 = s.lr := by
    rw [hfr.readW (r := frameR fs s) (slotLr_contains hfs s) hslots (by decide)]
    exact cwSave_lr_slot r s
  have h31 : g.mem.readW (slot31 fs s) 64 = s.gpr .r31 := by
    rw [hfr.readW (r := frameR fs s) (slot31_contains hfs s) hslots (by decide)]
    exact cwSave_r31_slot r s
  obtain ⟨hin₀, hin₈⟩ := slots_in s hfs hwrg hspg
  refine WP.block ⟨_, restoreRet_run hin₀ hin₈, ?_⟩
  refine WP.block ⟨_, mtlr_run _, ?_⟩
  show abiPreserved s (cwFinal fs g) ∧ (sig.contract abi pre post wa (stack + fs) leak).post s (cwFinal fs g) ∧
    Spec.Zeroize.bytesAt (cwFinal fs g).mem (s.gpr r) n = Spec.Zeroize.zeros n
  refine ⟨⟨fun q hq => ?_, by rw [cwFinal_sp, hspg, BitVec.sub_add_cancel], ?_⟩, ?_, ?_⟩
  · -- The callee-saved registers.
    obtain ⟨h0, h3, -, -, h12⟩ := preserved_ne q hq
    by_cases hq31 : q = .r31
    · subst hq31; rw [cwFinal_r31, hspg]; exact h31
    · rw [cwFinal_gpr g h0 h3 h12 hq31, hcsg q hq hq31]
  · rw [cwFinal_lr, hspg, BitVec.add_zero]; exact hlr
  · -- The postcondition, which reads the memory on return only within the buffers apart from the array.
    rw [post_regs hk, cwFinal_r3, h31g, cwFinal_mem]
    refine hout c'.mem _ _ (fun b hb hbA x hx => ?_) hc'.2.2.2.2.2.2
    refine (hfc x fun R hR hc => ?_).symm
    rcases List.mem_cons.mp hR with rfl | hR
    · exact hbA x hx (Region.sub_prefix hn x hc)
    · simp only [List.mem_singleton] at hR; subst hR
      exact hres b hb x (below_below s.sp fs stack x hc) hx
  · rw [cwFinal_mem]; exact hz0

end

/-- Two runs of a block, whose traces agree. -/
theorem RelCT.block_of {P Q : State → State → Prop} {l : List Instr}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ u₁ u₂ t, execBlock isa l s₁ = some (u₁, t) ∧
      execBlock isa l s₂ = some (u₂, t) ∧ Q u₁ u₂) :
    RelCT isa P (.block l) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨u₁, u₂, t, h₁, h₂, hq⟩ := h _ _ hp
  rw [Exec.block_iff, h₁, Option.some.injEq, Prod.mk.injEq] at e₁
  rw [Exec.block_iff, h₂, Option.some.injEq, Prod.mk.injEq] at e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, hq⟩

theorem argRegs_getD_ne : ∀ i < 8, argRegs.getD i .r3 ≠ .r0 ∧ argRegs.getD i .r3 ≠ .r12 := by decide

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack fs : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- Code verified against `sig.contract` with `stack` bytes of stack, for a
function whose arguments are all in registers, the one in `argRegs[i]` a
writable array of `k` elements `e`, is verified with `stack + fs` bytes when
called by `callWipe` with a frame of `fs` bytes (`FrameOk fs`), which then zeroes the first `n` bytes of the array with
code verified against `Spec.Zeroize.zeroizeContract` (with `zst ≤ stack`
bytes of stack), against the contract whose postcondition `post'` follows
from the function's and those bytes being zero (`hwiped`). Each callee uses
no more stack than its contract gives it (`hd`, `hzd`). The precondition,
postcondition and leak must read the memory on entry only within the
function's buffers (`hpre`, `hpost`, `hleak`), and the postcondition the
memory on return only within those apart from the array (`hpostOut`). -/
theorem Verified.callWipe' {post' : sig.Post abi.ptrBits} {name zname : String}
    {body zcode : Prog isa} {zst : Nat} {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem}
    {k n i : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hps : sig.params = ps₁ ++ (nm, .array true e k) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 64).length)
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hst : stack + fs < 2 ^ 64)
    (hd : sdepth body ≤ stack) (hzd : sdepth zcode ≤ zst) (hzs : zst ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    (hpostOut : ∀ vs m m₁ m₂ x, vs.length = (sig.words abi.ptrBits).length →
      (Sig.bufs sig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs sig.params vs, b.1.Disjoint ⟨vs.getD i 0, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ x →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ x)
    (hwiped : ∀ vs m m' x, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) post vs m m' x →
      Spec.Zeroize.bytesAt m' (vs.getD i 0) n = Spec.Zeroize.zeros n →
        Curry.apply (sig.words abi.ptrBits) post' vs m m' x)
    (hsat : ∃ s, (sig.contract abi pre post' wa (stack + fs) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) (hfs : FrameOk fs := by decide) :
    Verified target (Impl.CallWipe.PPC64LE.callWipe fs (argRegs.getD i .r3) n name body zname zcode)
      (sig.contract abi pre post' wa (stack + fs) leak) := by
  subst hi
  have hL : (sig.words abi.ptrBits).length = (ps₁.flatMap fun p => p.2.words 64).length + 1 +
      (ps₂.flatMap fun p => p.2.words 64).length := by
    show (sig.params.flatMap fun p => p.2.words 64).length = _
    rw [hps, List.flatMap_append, List.flatMap_cons]
    simp only [List.length_append, Param.words.eq_2, List.length_cons, List.length_nil]
    omega
  have hiL : (ps₁.flatMap fun p => p.2.words 64).length < (sig.words abi.ptrBits).length := by
    rw [hL]; omega
  obtain ⟨hr0, hr12⟩ := argRegs_getD_ne (ps₁.flatMap fun p => p.2.words 64).length
    (by omega_using [hiL, hk])
  generalize hr' : argRegs.getD (ps₁.flatMap fun p => p.2.words 64).length .r3 = r at hr0 hr12 ⊢
  have hget : ∀ s : State, (regArgs sig s).getD (ps₁.flatMap fun p => p.2.words 64).length 0 = s.gpr r :=
    fun s => by rw [← hr']; exact regArgs_getD s.gpr hk hiL
  -- The array, among the buffers.
  have harr : ∀ s : State, (⟨s.gpr r, k * e.size⟩, true) ∈ Sig.bufs sig.params (regArgs sig s) := by
    intro s
    rw [← hget s, hps]
    exact Sig.bufs_mem_array ps₂ ps₁ (regArgs sig s) (by rw [regArgs_length sig s hk, hL]; omega)
  -- Its address is public.
  have hpubA : ∀ s₁ s₂, (sig.contract abi pre post wa (stack + fs) leak).pub s₁ s₂ → s₁.gpr r = s₂.gpr r := by
    intro s₁ s₂ hp
    have hP : (sig.params.flatMap (·.2.pubs)).getD (ps₁.flatMap fun p => p.2.words 64).length false = true := by
      rw [hps]; exact (Sig.pub_array ps₁ ps₂).1
    have hW : ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)).getD
        (ps₁.flatMap fun p => p.2.words 64).length 64 = 64 := by
      show ((sig.params.flatMap fun p => p.2.words 64).map (·.bits 64)).getD _ 64 = 64
      rw [hps]; exact (Sig.pub_array ps₁ ps₂).2
    have h2 := congrArg BitVec.toNat (((pub_regsL hk hl).mp hp).2 _ hP)
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, hW, hget, hget, Nat.mod_eq_of_lt (BitVec.isLt _),
      Nat.mod_eq_of_lt (BitVec.isLt _)] at h2
    exact BitVec.eq_of_toNat_eq h2
  -- The postcondition reads the memory on return only within the buffers apart from the array.
  have hout : ∀ s, (sig.contract abi pre post wa (stack + fs) leak).pre s → ∀ m₁ m₂ x,
      (∀ b ∈ Sig.bufs sig.params (regArgs sig s), b.1.Disjoint ⟨s.gpr r, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₂ x := by
    intro s hs m₁ m₂ x hag hq
    rw [pre_regs hk hl] at hs
    exact hpostOut _ _ _ _ _ (regArgs_length sig s hk) hs.2.2.2.1 (by rw [hget]; exact hag) hq
  refine ⟨fun s hs => ?_, ?_, hsat⟩
  · obtain ⟨t, g, he, habi, hq, hz0⟩ :=
      cw_wp hfs h hz hk hl hr0 hr12 hd hzd hzs hst hpre hpost hn hn32 hs (harr s) (hout s hs)
    refine ⟨t, g, he, habi, ?_⟩
    rw [post_regs hk] at hq ⊢
    exact hwiped _ _ _ _ (regArgs_length sig s hk) hq (by rw [hget]; exact hz0)
  · refine RelCT.constantTime (Q := fun _ _ => True) ?_
    refine RelCT.mono (P := fun a b => ∃ σ₁ σ₂, ((sig.contract abi pre post' wa (stack + fs) leak).pre σ₁ ∧
        (sig.contract abi pre post' wa (stack + fs) leak).pre σ₂ ∧
        (sig.contract abi pre post' wa (stack + fs) leak).pub σ₁ σ₂) ∧ a = σ₁ ∧ b = σ₂) ?_
      (fun a b hab => ⟨a, b, hab, rfl, rfl⟩) (fun _ _ h => h)
    refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_
    by_cases hP0 : (sig.contract abi pre post' wa (stack + fs) leak).pre σ₁ ∧
        (sig.contract abi pre post' wa (stack + fs) leak).pre σ₂ ∧
        (sig.contract abi pre post' wa (stack + fs) leak).pub σ₁ σ₂
    swap
    · exact RelCT.of_false fun a b hab => hP0 hab.1
    obtain ⟨h₁, h₂, hp⟩ := hP0
    have h₁' : (sig.contract abi pre post wa (stack + fs) leak).pre σ₁ := h₁
    have h₂' : (sig.contract abi pre post wa (stack + fs) leak).pre σ₂ := h₂
    have hp' : (sig.contract abi pre post wa (stack + fs) leak).pub σ₁ σ₂ := hp
    have hsp12 : σ₁.sp = σ₂.sp := ((pub_regsL hk hl).mp hp').1.1
    have hpp := hpubA _ _ hp'
    have hcov : ∀ σ : State, Covers (σ.rd ++ σ.wr) ((cwSave fs r σ).rd ++ (cwSave fs r σ).wr) ∧
        Covers σ.wr (cwSave fs r σ).wr := fun σ =>
      ⟨Covers.append (Covers.refl _) (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx),
        Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx⟩
    refine RelCT.mono (P := fun a b => a = σ₁ ∧ b = σ₂) ?_ (fun a b hab => hab.2) (fun _ _ h => h)
    -- `mflr r0`.
    refine RelCT.seq (R := fun a b => a = σ₁.write .r0 σ₁.lr ∧ b = σ₂.write .r0 σ₂.lr)
      (RelCT.block_of fun a b hab => ?_) ?_
    · obtain ⟨rfl, rfl⟩ := hab
      exact ⟨_, _, _, mflr_run a, mflr_run b, rfl, rfl⟩
    -- The frame, then `mtlr r0`.
    refine RelCT.seq (R := fun _ _ => True) ?_
      (RelCT.block_of fun a b _ => ⟨_, _, _, mtlr_run a, mtlr_run b, trivial⟩)
    refine RelCT.alloc (R := fun _ _ => True) (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab; exact hsp12) ?_
    refine RelCT.mono (P := fun a b => a = cwPush fs σ₁ ∧ b = cwPush fs σ₂) ?_
      (fun a b hab => by obtain ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩ := hab; exact ⟨rfl, rfl⟩) (fun _ _ h => h)
    -- `r31` is saved, and the array's address kept in it.
    refine RelCT.seq (R := fun a b => a = cwSave fs r σ₁ ∧ b = cwSave fs r σ₂)
      (RelCT.block_of fun a b hab => ?_) ?_
    · obtain ⟨rfl, rfl⟩ := hab
      have e : slotLr fs σ₂ = slotLr fs σ₁ := by simp only [slotLr, fsp, hsp12]
      exact ⟨cwSave fs r σ₁, cwSave fs r σ₂, _, saveArg_run hfs hr0 hr12 σ₁,
        by rw [saveArg_run hfs hr0 hr12 σ₂, slot31, slot31, e], rfl, rfl⟩
    -- The first function.
    refine RelCT.seq (R := fun c₁ c₂ => AfterBody sig post fs r stack σ₁ c₁ ∧ AfterBody sig post fs r stack σ₂ c₂)
      ?_ ?_
    · refine RelCT.mono (RelCT.wp (F₁ := AfterBody sig post fs r stack σ₁) (F₂ := AfterBody sig post fs r stack σ₂)
        (RelCT.callEx h.1 h.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
      · obtain ⟨rfl, rfl⟩ := hab
        exact ⟨σ₁.rd, σ₁.wr, σ₂.rd, σ₂.wr, cw_bodyPre hfs hk hl hst hpre h₁', cw_bodyPre hfs hk hl hst hpre h₂',
          cw_bodyPub hfs hk hl hst r h₁' h₂' hp' hleak, (hcov σ₁).1, (hcov σ₁).2, (hcov σ₂).1, (hcov σ₂).2⟩
      · obtain ⟨rfl, rfl⟩ := hab
        exact ⟨cw_body_wp hfs h hk hl hd hst hpre hpost h₁', cw_body_wp hfs h hk hl hd hst hpre hpost h₂'⟩
    -- The zeroize function's arguments.
    refine RelCT.seq (R := fun d₁ d₂ => (∃ c, AfterBody sig post fs r stack σ₁ c ∧ d₁ = cwZero n c) ∧
      (∃ c, AfterBody sig post fs r stack σ₂ c ∧ d₂ = cwZero n c))
      (RelCT.block_of fun c₁ c₂ hc => ⟨_, _, _, zeroArgs_run hn32 c₁, zeroArgs_run hn32 c₂,
        ⟨c₁, hc.1, rfl⟩, ⟨c₂, hc.2, rfl⟩⟩) ?_
    -- The zeroize function.
    refine RelCT.seq (R := fun g₁ g₂ => AfterZero sig post fs r stack n σ₁ g₁ ∧ AfterZero sig post fs r stack n σ₂ g₂)
      ?_ ?_
    · refine RelCT.mono (RelCT.wp (F₁ := AfterZero sig post fs r stack n σ₁) (F₂ := AfterZero sig post fs r stack n σ₂)
        (RelCT.callEx hz.1 hz.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
      · obtain ⟨⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩ := hab
        exact ⟨[], [⟨σ₁.gpr r, n⟩], [], [⟨σ₂.gpr r, n⟩], cw_zeroPre hfs hk hl hst h₁' (harr σ₁) hn hn32 hzs hc₁,
          cw_zeroPre hfs hk hl hst h₂' (harr σ₂) hn hn32 hzs hc₂, cw_zeroPub hsp12 hpp hc₁ hc₂,
          Covers.right (cw_zeroCovers hk hl h₁' (harr σ₁) hn hc₁), cw_zeroCovers hk hl h₁' (harr σ₁) hn hc₁,
          Covers.right (cw_zeroCovers hk hl h₂' (harr σ₂) hn hc₂), cw_zeroCovers hk hl h₂' (harr σ₂) hn hc₂⟩
      · obtain ⟨⟨c₁, hc₁, rfl⟩, ⟨c₂, hc₂, rfl⟩⟩ := hab
        exact ⟨cw_zero_wp hfs hz hzd hzs hst hk hl h₁' (harr σ₁) hn hn32 hc₁,
          cw_zero_wp hfs hz hzd hzs hst hk hl h₂' (harr σ₂) hn hn32 hc₂⟩
    -- The result and `r31` are restored.
    · refine RelCT.block_of fun g₁ g₂ hg => ?_
      obtain ⟨⟨_, _, _, hw₁, hs₁, _⟩, ⟨_, _, _, hw₂, hs₂, _⟩⟩ := hg
      obtain ⟨i₀, i₈⟩ := slots_in σ₁ hfs hw₁ hs₁
      obtain ⟨j₀, j₈⟩ := slots_in σ₂ hfs hw₂ hs₂
      refine ⟨_, cwRestore g₂, _, restoreRet_run i₀ i₈, ?_, trivial⟩
      rw [restoreRet_run j₀ j₈, hs₁, hs₂, fsp, fsp, hsp12]

/-- `Verified.callWipe'`, with the function's postcondition. -/
theorem Verified.callWipe {name zname : String} {body zcode : Prog isa} {zst : Nat}
    {ps₁ ps₂ : List (String × Param)} {nm : String} {e : Elem} {k n i : Nat}
    (h : Verified target body (sig.contract abi pre post wa stack leak))
    (hz : Verified target zcode (Spec.Zeroize.zeroizeContract abi zst))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hps : sig.params = ps₁ ++ (nm, .array true e k) :: ps₂)
    (hi : i = (ps₁.flatMap fun p => p.2.words 64).length)
    (hn : n ≤ k * e.size) (hn32 : n < 2 ^ 32) (hst : stack + fs < 2 ^ 64)
    (hd : sdepth body ≤ stack) (hzd : sdepth zcode ≤ zst) (hzs : zst ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    (hpostOut : ∀ vs m m₁ m₂ x, vs.length = (sig.words abi.ptrBits).length →
      (Sig.bufs sig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs sig.params vs, b.1.Disjoint ⟨vs.getD i 0, k * e.size⟩ →
        ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ x →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ x)
    (hsat : ∃ s, (sig.contract abi pre post wa (stack + fs) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) (hfs : FrameOk fs := by decide) :
    Verified target (Impl.CallWipe.PPC64LE.callWipe fs (argRegs.getD i .r3) n name body zname zcode)
      (sig.contract abi pre post wa (stack + fs) leak) :=
  Verified.callWipe' h hz hk hl hps hi hn hn32 hst hd hzd hzs hpre hpost hpostOut
    (fun _ _ _ _ _ hq _ => hq) hsat hleak hfs

end

/-- The stack `callWipe` and its callees use: its frame, and the larger of
its callees'. -/
theorem sdepth_callWipe {fs : Nat} {r : Reg} {n : Nat} {name zname : String} {body zcode : Prog isa} :
    sdepth (Impl.CallWipe.PPC64LE.callWipe fs r n name body zname zcode) =
      fs + max (sdepth body) (sdepth zcode) := by
  simp only [Impl.CallWipe.PPC64LE.callWipe, sdepth, Instr.frameBytes, Nat.zero_max, Nat.max_zero]

end VG.PPC64LE
