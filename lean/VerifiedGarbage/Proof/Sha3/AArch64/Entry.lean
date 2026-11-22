module

public import VerifiedGarbage.Proof.Sha3.AArch64.CallD8
public import VerifiedGarbage.Proof.Framework.AArch64.CallWipeConsts
public import VerifiedGarbage.TCB.Registration
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig

/-!
# The function that calls a function with a permutation's address in `d8`

`Verified.entryD8C`: code verified against `Contract.d8 n` of `sig.contract`
under `abi.withConsts`, with `stack` bytes of stack, for a function whose
arguments are all in registers, is verified against `sig.contract` under
`(abi.withConsts …).withFns [n]` with `stack + 16` bytes when called by
`entryD8 n`, which puts `n`'s address in `d8` around the call: the address
is public there (`Abi.withFns`), as `Contract.d8` needs. As
`Verified.callWipeC'` (`Proof/Framework/AArch64/CallWipe.lean`), for a frame
of 16 bytes and one call: the precondition must read the memory on entry,
and the postcondition the memory on entry and on return, only within the
function's buffers (`hpre`, `hpost`, `hpostR`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64 VG.Impl.Sha3.AArch64

/-! ## The frame -/

/-- The address `off` bytes into the frame of `s`'s caller. -/
abbrev eslot (s : State) (off : Nat) : Addr := s.sp - BitVec.ofNat 64 16 + BitVec.ofNat 64 off

/-- The state after the frame's allocation and `umov x16, v8.d[0]`. -/
abbrev eSave₁ (s : State) : State := (allocated 16 s).write .x .x16 (laneOf s .v8 0)

/-- The state after the frame's allocation and `enterD8 n`. -/
def eSave (n : String) (s : State) : State :=
  ((({ eSave₁ s with
      mem := (s.mem.write (eslot s 0) 8 (s.gpr .x30)).write (eslot s 8) 8 (laneOf s .v8 0) } : State).write
    .x .x16 (s.syms n)).setV .v8 (setLane (s.v .v8) 64 0 (s.syms n)))

@[simp] theorem eSave_sp (n : String) (s : State) : (eSave n s).sp = s.sp - BitVec.ofNat 64 16 := rfl
@[simp] theorem eSave_rd (n : String) (s : State) : (eSave n s).rd = s.rd := rfl
@[simp] theorem eSave_wr (n : String) (s : State) :
    (eSave n s).wr = ⟨s.sp - BitVec.ofNat 64 16, 16⟩ :: s.wr := rfl
@[simp] theorem eSave_syms (n : String) (s : State) : (eSave n s).syms = s.syms := rfl
@[simp] theorem eSave_dit (n : String) (s : State) : (eSave n s).dit = s.dit := rfl

theorem eSave_gpr (n : String) (s : State) {q : Reg} (h : q ≠ .x16) : (eSave n s).gpr q = s.gpr q := by
  rw [eSave, RegUpd.gpr_setV, RegUpd.gpr_write_of_ne _ _ _ h]
  exact RegUpd.gpr_write_of_ne _ _ _ h

theorem eSave_v (n : String) (s : State) {q : VReg} (h : q ≠ .v8) : (eSave n s).v q = s.v q := by
  rw [eSave, RegUpd.v_setV_of_ne _ _ h]; rfl

theorem eSave_d8 (n : String) (s : State) : D8 n (eSave n s) := by
  unfold D8
  rw [eSave, RegUpd.v_setV_self]
  exact (extract_setLane64 (s.v .v8) (s.syms n) (i := 0) (j := 0) (by decide) (by decide)).trans (ite_eq_left rfl)

/-- The frame's slot at `off < 16` is in its region. -/
theorem eslot_in (s : State) {off : Nat} (h : off + 8 ≤ 16) :
    InRegions (⟨s.sp - BitVec.ofNat 64 16, 16⟩ :: s.wr) (eslot s off) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by omega_using [h])⟩

theorem eslot_in' (s : State) (rd : List Region) {off : Nat} (h : off + 8 ≤ 16) :
    InRegions (rd ++ ⟨s.sp - BitVec.ofNat 64 16, 16⟩ :: s.wr) (eslot s off) 8 :=
  ⟨_, List.mem_append_right _ (List.mem_cons_self ..), Offset.contains_base _ h (by omega_using [h])⟩

theorem enter_run (n : String) (s : State) :
    execBlock isa (enterD8 n) (allocated 16 s) =
      some (eSave n s, [.addr (eslot s 0), .addr (eslot s 8)]) := by
  have e₀ : exec (.umov .x .x16 .v8 0) (allocated 16 s) = some (eSave₁ s) := exec_umov (by decide)
  have e₁ : exec (.strSp .x30 0) (eSave₁ s) =
      some { eSave₁ s with mem := s.mem.write (eslot s 0) 8 (s.gpr .x30) } :=
    exec_strSp' (s := eSave₁ s) (by decide) (eslot_in s (by decide))
  have e₂ : exec (.strSp .x16 8) { eSave₁ s with mem := s.mem.write (eslot s 0) 8 (s.gpr .x30) } =
      some { eSave₁ s with
        mem := (s.mem.write (eslot s 0) 8 (s.gpr .x30)).write (eslot s 8) 8 (laneOf s .v8 0) } :=
    exec_strSp' (s := { eSave₁ s with mem := s.mem.write (eslot s 0) 8 (s.gpr .x30) }) (by decide)
      (eslot_in s (by decide))
  have e₃ := exec_adrSym (s := { eSave₁ s with
        mem := (s.mem.write (eslot s 0) 8 (s.gpr .x30)).write (eslot s 8) 8 (laneOf s .v8 0) })
    (d := .x16) (name := n)
  have e₄ := exec_ins (s := ({ eSave₁ s with
        mem := (s.mem.write (eslot s 0) 8 (s.gpr .x30)).write (eslot s 8) 8 (laneOf s .v8 0) } : State).write
      .x .x16 (s.syms n)) (r := .x16) (v := .v8) (l := 0) (by decide)
  simp only [enterD8, execBlock, isa, e₀, e₁, e₂, e₃, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  rfl

/-- The frame's slot at `off` holds the 8 bytes there. -/
theorem eslot_contains (s : State) {off : Nat} (h : off + 8 ≤ 16) :
    (below s.sp 16).Contains (eslot s off) 8 :=
  Offset.contains_base _ h (by omega_using [h])

/-- The frame's slots are separate. -/
theorem eslot_sep (s : State) {a b : Nat} (h : a + 8 ≤ b ∨ b + 8 ≤ a) (ha : a + 8 ≤ 16)
    (hb : b + 8 ≤ 16) : Mem.Sep (eslot s a) 8 (eslot s b) 8 :=
  Offset.sep _ h (by omega_using [ha]) (by omega_using [hb])

theorem eSave_mem (n : String) (s : State) :
    (eSave n s).mem = (s.mem.write (eslot s 0) 8 (s.gpr .x30)).write (eslot s 8) 8 (laneOf s .v8 0) := rfl

theorem eSave_read0 (n : String) (s : State) : (eSave n s).mem.read (eslot s 0) 8 = s.gpr .x30 := by
  rw [eSave_mem, Mem.read_write_sep (eslot_sep s (a := 0) (b := 8) (.inl (by decide)) (by decide) (by decide))
    (by decide), read_write_self]

theorem eSave_read8 (n : String) (s : State) : (eSave n s).mem.read (eslot s 8) 8 = laneOf s .v8 0 := by
  rw [eSave_mem, read_write_self]

/-- The save writes only the frame, the 16 bytes below `sp`. -/
theorem eSave_frame (n : String) (s : State) : Frame [below s.sp 16] s.mem (eSave n s).mem := by
  rw [eSave_mem]
  exact Frame.write (Frame.write (Frame.refl _ _) (List.mem_singleton_self _) _ (eslot_contains s (by decide)))
    (List.mem_singleton_self _) _ (eslot_contains s (by decide))

/-- The state after `leaveD8`, from `g`. -/
def eRestore (g : State) : State :=
  let g₁ := g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 8) 8)
  let g₂ := g₁.setV .v8 (setLane (g₁.v .v8) 64 0 (g₁.gpr .x16))
  g₂.write .x .x30 (g₂.mem.read (g₂.sp + BitVec.ofNat 64 0) 8)

theorem leave_run {g : State} (h8 : InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 8) 8)
    (h0 : InRegions (g.rd ++ g.wr) (g.sp + BitVec.ofNat 64 0) 8) :
    execBlock isa leaveD8 g =
      some (eRestore g, [.addr (g.sp + BitVec.ofNat 64 8), .addr (g.sp + BitVec.ofNat 64 0)]) := by
  have e₁ : exec (.ldrSp .x16 8) g = some (g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 8) 8)) :=
    exec_ldrSp' (by decide) h8
  have e₂ := exec_ins (s := g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 8) 8)) (r := .x16) (v := .v8)
    (l := 0) (by decide)
  have e₃ := exec_ldrSp' (t := .x30) (off := 0)
    (s := (g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 8) 8)).setV .v8
      (setLane ((g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 8) 8)).v .v8) 64 0
        ((g.write .x .x16 (g.mem.read (g.sp + BitVec.ofNat 64 8) 8)).gpr .x16))) (by decide) h0
  simp only [leaveD8, execBlock, isa, e₁, e₂, e₃, Option.map_some, addrs, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, RegUpd.sp_write, RegUpd.sp_setV]
  rfl

theorem eRestore_gpr {g : State} {q : Reg} (h16 : q ≠ .x16) (h30 : q ≠ .x30) : (eRestore g).gpr q = g.gpr q := by
  simp only [eRestore, RegUpd.gpr_write_of_ne _ _ _ h30, RegUpd.gpr_setV, RegUpd.gpr_write_of_ne _ _ _ h16]

theorem eRestore_x30 (g : State) : (eRestore g).gpr .x30 = g.mem.read (g.sp + BitVec.ofNat 64 0) 8 := by
  simp only [eRestore, RegUpd.gpr_write_self, BitVec.setWidth_eq]; rfl

theorem eRestore_x0 (g : State) : (eRestore g).gpr .x0 = g.gpr .x0 := eRestore_gpr (by decide) (by decide)

theorem eRestore_sp (g : State) : (eRestore g).sp = g.sp := rfl

theorem eRestore_v (g : State) {q : VReg} (h : q ≠ .v8) : (eRestore g).v q = g.v q := by
  simp only [eRestore, RegUpd.v_write, RegUpd.v_setV_of_ne _ _ h]

theorem eRestore_d8 (g : State) :
    ((eRestore g).v .v8).extractLsb' 0 64 = g.mem.read (g.sp + BitVec.ofNat 64 8) 8 := by
  simp only [eRestore, RegUpd.v_write, RegUpd.v_setV_self]
  refine (extract_setLane64 _ _ (i := 0) (j := 0) (by decide) (by decide)).trans (ite_eq_left rfl) |>.trans ?_
  simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq]

/-! ## The caller's contract -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

theorem e_sp (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) : stack + 16 ≤ s.sp.toNat := by
  rw [pre_regs' hk hl] at hs
  rcases hs.1 with h | h <;> omega_using [h]

theorem e_below (s : State) : below s.sp (stack + 16) ∈ stackBelow s.sp (stack + 16) := by
  rw [stackBelow_pos _ (by omega_using [])]; exact List.mem_singleton_self _

/-- The buffers lie apart from the stack below `sp` that the caller's
contract reserves. -/
theorem e_out (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (regArgs sig s), ∀ (a n : Nat), n ≤ a → a ≤ stack + 16 →
      b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 a, n⟩ := by
  rw [pre_regs' hk hl] at hs
  obtain ⟨-, -, -, -, hres, -, -⟩ := hs
  intro b hb a n hn ha
  exact (Region.Disjoint.symm (hres _ (e_below s) b hb)).sub_right
    (Offset.sub_below _ ha (by omega_using [hn, ha]))

/-- So do the writable regions. -/
theorem e_outW (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true) {s : State}
    (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) :
    ∀ x ∈ s.wr, ∀ (a n : Nat), n ≤ a → a ≤ stack + 16 → x.Disjoint ⟨s.sp - BitVec.ofNat 64 a, n⟩ := by
  have hout := e_out hk hl hs
  rw [pre_regs' hk hl] at hs
  intro x hx a n hn ha
  rw [hs.2.2.1] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact hout b (List.mem_filter.mp hb).1 a n hn ha

/-- The state the function runs from, with the permissions of its
contract: after the call. -/
def eEntry (n : String) (s : State) : State := (eSave n s).callEntry.withRegions s.rd s.wr

theorem eEntry_gpr (n : String) (s : State) {q : Reg} (h : q ∉ linkRegs) : (eEntry n s).gpr q = s.gpr q := by
  rw [eEntry, State.withRegions_gpr, State.callEntry_gpr _ h]
  exact eSave_gpr n s (fun e => h (by rw [e]; decide))

@[simp] theorem eEntry_sp (n : String) (s : State) : (eEntry n s).sp = s.sp - BitVec.ofNat 64 16 := rfl
@[simp] theorem eEntry_mem (n : String) (s : State) : (eEntry n s).mem = (eSave n s).mem := rfl
@[simp] theorem eEntry_rd (n : String) (s : State) : (eEntry n s).rd = s.rd := rfl
@[simp] theorem eEntry_wr (n : String) (s : State) : (eEntry n s).wr = s.wr := rfl
@[simp] theorem eEntry_syms (n : String) (s : State) : (eEntry n s).syms = s.syms := rfl

theorem eEntry_d8 (n : String) (s : State) : D8 n (eEntry n s) := eSave_d8 n s

theorem regArgs_eEntry (n : String) (s : State) : regArgs sig (eEntry n s) = regArgs sig s :=
  List.map_congr_left fun q hq => eEntry_gpr n s (argRegs_not_link q (List.mem_of_mem_take hq))

/-- The entry's memory is the caller's in the buffers. -/
theorem e_agree (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (n : String) {s : State} (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) :
    ∀ b ∈ Sig.bufs sig.params (regArgs sig s), ∀ x, b.1.Contains x 1 → (eEntry n s).mem x = s.mem x :=
  fun b hb x hx => eSave_frame n s x fun R hR hc => by
    simp only [List.mem_singleton] at hR; subst hR
    exact e_out hk hl hs b hb (a := 16) (n := 16) (by decide) (by omega_using []) x hx hc

/-- The caller's precondition gives the function's at its entry. -/
theorem e_bodyPre (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {n : String} (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) :
    (sig.contract abi pre post wa stack leak).pre (eEntry n s) := by
  have hsb := e_sp hk hl hs
  have hag := e_agree hk hl n hs
  rw [pre_regs' hk hl] at hs
  obtain ⟨-, hrd, hwr, hpw, hres, hnw, hpr⟩ := hs
  refine (pre_regs' hk hl).mpr ?_
  rw [regArgs_eEntry, eEntry_sp, eEntry_rd, eEntry_wr]
  refine ⟨.inr ?_, hrd, hwr, hpw, ?_, hnw, ?_⟩
  · rw [toNat_sub_ofNat' (by omega_using [hsb])]; omega_using [hsb]
  · intro x hx a ha
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hx
    · rw [stackBelow_pos _ h0, List.mem_singleton] at hx; subst hx
      exact (hres _ (e_below s) a ha).sub_left (below_below _ 16 stack)
  · exact hpre _ _ _ (regArgs_length sig s hk) (fun b hb x hx => (hag b hb x hx).symm) hpr

/-- The caller's public data is the function's at its entry. -/
theorem e_bodyPub (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (n : String) {s₁ s₂ : State} {rd₁ rd₂ : List Region}
    (h₁ : (sig.contract abi pre post wa (stack + 16) leak).pre (s₁.withRegions rd₁ s₁.wr))
    (h₂ : (sig.contract abi pre post wa (stack + 16) leak).pre (s₂.withRegions rd₂ s₂.wr))
    (hp : (sig.contract abi pre post wa (stack + 16) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak) :
    (sig.contract abi pre post wa stack leak).pub (eEntry n s₁) (eEntry n s₂) := by
  have ag₁ : ∀ b ∈ Sig.bufs sig.params (regArgs sig s₁), ∀ x, b.1.Contains x 1 →
      (eEntry n s₁).mem x = s₁.mem x := e_agree (s := s₁.withRegions rd₁ s₁.wr) hk hl n h₁
  have ag₂ : ∀ b ∈ Sig.bufs sig.params (regArgs sig s₂), ∀ x, b.1.Contains x 1 →
      (eEntry n s₂).mem x = s₂.mem x := e_agree (s := s₂.withRegions rd₂ s₂.wr) hk hl n h₂
  rw [pub_regs hk] at hp ⊢
  obtain ⟨⟨⟨hsp, hdit⟩, hlk⟩, hpa, -⟩ := hp
  rw [regArgs_eEntry, regArgs_eEntry, eEntry_sp, eEntry_sp, hsp]
  refine ⟨⟨⟨rfl, hdit⟩, ?_⟩, hpa, fun R hR => ?_⟩
  · cases leak with
    | none => trivial
    | some f =>
      show Curry.apply _ f (regArgs sig s₁) (eEntry n s₁).mem =
        Curry.apply _ f (regArgs sig s₂) (eEntry n s₂).mem
      rw [hleak _ _ _ (regArgs_length sig s₁ hk) ag₁, hleak _ _ _ (regArgs_length sig s₂ hk) ag₂]
      exact hlk
  · rw [Sig.descs_of_noLists 64 _ _ hl] at hR
    exact absurd hR List.not_mem_nil

/-- What the run of the function leaves, from the caller's state `s`. -/
def AfterE (sig : Sig) (post : sig.Post abi.ptrBits) (stack : Nat) (s c : State) : Prop :=
  c.wr = ⟨s.sp - BitVec.ofNat 64 16, 16⟩ :: s.wr ∧ c.sp = s.sp - BitVec.ofNat 64 16 ∧
  (∀ q ∈ preserved, q ≠ .x30 → c.gpr q = s.gpr q) ∧
  (∀ q ∈ preservedV, q ≠ .v8 → (c.v q).extractLsb' 0 64 = (s.v q).extractLsb' 0 64) ∧
  c.mem.read (eslot s 0) 8 = s.gpr .x30 ∧ c.mem.read (eslot s 8) 8 = laneOf s .v8 0 ∧
  Frame (s.wr ++ [below s.sp (stack + 16)]) s.mem c.mem ∧
  Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem c.mem ((c.gpr .x0).setWidth _)

/-- The frame lies apart from the writable regions and from the stack below it. -/
theorem e_frameApart (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {s : State} (hs : (sig.contract abi pre post wa (stack + 16) leak).pre s) {d : Nat} (hd : d ≤ stack) :
    ∀ x ∈ s.wr ++ [below (s.sp - BitVec.ofNat 64 16) d], (below s.sp 16).Disjoint x := by
  have hsb := e_sp hk hl hs
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (e_outW hk hl hs x hx (a := 16) (n := 16) (by decide) (by omega_using [])).symm
  · simp only [List.mem_singleton] at hx; subst hx
    exact Offset.base_disjoint_below _ (by omega_using [hd, hsb])

/-- The call of the function, from a caller's state `s` whose precondition
holds with the readable regions `rd`, for code verified against a contract
`kb` whose precondition holds at its entry (`hentry`) and whose
postcondition gives the function's (`hkb`). -/
theorem e_body_wpOf {n name : String} {body : Prog isa} {kb : Contract isa}
    (hv : ∀ s, kb.pre s → ∃ t s', Exec isa body s t s' ∧ abiPreserved s s' ∧ kb.post s s')
    (hkb : ∀ x y, kb.post x y → (sig.contract abi pre post wa stack leak).post x y)
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hd : 16 * body.aarch64Depth ≤ stack)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    {s : State} {rd : List Region}
    (hs : (sig.contract abi pre post wa (stack + 16) leak).pre (s.withRegions rd s.wr))
    (hentry : kb.pre (eEntry n s)) :
    WP isa (.call name body) (eSave n s) (AfterE sig post stack s) := by
  have hsb : stack + 16 ≤ s.sp.toNat := e_sp (s := s.withRegions rd s.wr) hk hl hs
  have hag : ∀ b ∈ Sig.bufs sig.params (regArgs sig s), ∀ x, b.1.Contains x 1 →
      (eEntry n s).mem x = s.mem x := e_agree (s := s.withRegions rd s.wr) hk hl n hs
  have hap : ∀ x ∈ s.wr ++ [below (s.sp - BitVec.ofNat 64 16) (16 * body.aarch64Depth)],
      (below s.sp 16).Disjoint x := e_frameApart (s := s.withRegions rd s.wr) hk hl hs hd
  refine WP.callFV (k := kb) hv (rd := s.rd) (wr := s.wr) hentry
    (Covers.append (Covers.refl _) (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx))
    (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx) ?_ (by omega_using [hd, hsb])
  intro c _ hwr hsp hfr hcs hv hq
  rw [eSave_sp] at hfr hsp
  refine ⟨hwr, hsp, fun q hq hq30 => (hcs q hq hq30).trans (eSave_gpr n s (fun e => by subst e; simp [preserved] at hq)),
    fun q hq hq8 => (hv q hq).trans (by rw [eSave_v n s hq8]), ?_, ?_, ?_, ?_⟩
  · rw [hfr.read (eslot_contains s (by decide)) hap (by decide), eSave_read0]
  · rw [hfr.read (eslot_contains s (by decide)) hap (by decide), eSave_read8]
  · -- Memory changes only within the writable buffers and the stack below `sp`.
    refine Frame.trans (Frame.sub (eSave_frame n s) fun x hx => ?_) (Frame.sub hfr fun x hx => ?_)
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        Offset.sub_below _ (by omega_using []) (by omega_using [])⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact ⟨x, List.mem_append_left _ hx, fun _ h => h⟩
      · simp only [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          fun y hy => below_sub (sp := s.sp) (a := 16 * body.aarch64Depth + 16) (b := stack + 16)
            (by omega_using [hd]) (by omega_using [hd, hsb]) y (below_below _ 16 _ y hy)⟩
  · -- The postcondition, which reads the memory on entry only within the buffers.
    have hq' := hkb _ _ hq
    rw [post_regs hk] at hq'
    rw [show (eSave n s).callEntry.withRegions s.rd s.wr = eEntry n s from rfl, regArgs_eEntry,
      eEntry_mem, State.withRegions_mem, State.withRegions_gpr] at hq'
    exact hpost _ _ _ _ _ (regArgs_length sig s hk) (fun b hb x hx => hag b hb x hx) hq'

/-- A run of `entryD8 n`, from the caller's state `s`, whose precondition
holds of `s` with the readable regions `rd`, from the run of the call of the
function (`hb`): it keeps what the calling convention requires, and its
postcondition is the function's if that reads the memory on return only
within the buffers (`hout`). -/
theorem e_wp {n name : String} {body : Prog isa}
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {s : State} {rd : List Region}
    (hs : (sig.contract abi pre post wa (stack + 16) leak).pre (s.withRegions rd s.wr))
    (hb : WP isa (.call name body) (eSave n s) (AfterE sig post stack s))
    (hout : ∀ m₁ m₂ x, (∀ b ∈ Sig.bufs sig.params (regArgs sig s), ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₂ x) :
    WP isa (entryD8 n name body) s fun g =>
      abiPreserved s g ∧ (sig.contract abi pre post wa (stack + 16) leak).post s g := by
  have hsb : stack + 16 ≤ s.sp.toNat := e_sp (s := s.withRegions rd s.wr) hk hl hs
  have hout' : ∀ b ∈ Sig.bufs sig.params (regArgs sig s), ∀ (a n : Nat), n ≤ a → a ≤ stack + 16 →
      b.1.Disjoint ⟨s.sp - BitVec.ofNat 64 a, n⟩ := e_out (s := s.withRegions rd s.wr) hk hl hs
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by omega_using [hsb]) ?_
  refine WP.seq (WP.block ⟨_, enter_run n s, ?_⟩)
  refine WP.seq (WP.mono hb fun c hc => ?_)
  obtain ⟨hwrc, hspc, hcs, hvc, h0, h8, -, hq⟩ := hc
  refine WP.block ⟨_, leave_run (by rw [hwrc, hspc]; exact eslot_in' s c.rd (by decide))
    (by rw [hwrc, hspc]; exact eslot_in' s c.rd (by decide)), ?_⟩
  intro m u f
  refine ⟨⟨fun q hq => ?_, ?_, fun q hq => ?_⟩, ?_⟩
  · show (eRestore c).gpr q = s.gpr q
    by_cases hq30 : q = .x30
    · subst hq30; rw [eRestore_x30, hspc]; exact h0
    · rw [eRestore_gpr (fun e => by subst e; simp [preserved] at hq) hq30]
      exact hcs q hq hq30
  · show (eRestore c).sp + BitVec.ofNat 64 16 = s.sp
    rw [eRestore_sp, hspc, BitVec.sub_add_cancel]
  · show ((eRestore c).v q).extractLsb' 0 64 = (s.v q).extractLsb' 0 64
    by_cases hq8 : q = .v8
    · subst hq8; rw [eRestore_d8, hspc]; exact h8
    · rw [eRestore_v c hq8]; exact hvc q hq hq8
  · -- The postcondition, which reads the memory on return only within the buffers.
    rw [post_regs hk]
    show Curry.apply _ post (regArgs sig s) s.mem m (((eRestore c).gpr .x0).setWidth _)
    rw [eRestore_x0]
    refine hout c.mem _ _ (fun b hb x hx => ?_) hq
    refine (f x fun R hR hc => ?_).symm
    simp only [List.mem_singleton] at hR; subst hR
    exact hout' b hb 16 16 (Nat.le_refl _) (by omega_using []) x hx hc

/-- Two runs of the frame's body from callers' states `σ₁` and `σ₂` which
agree on `sp` leak the same, if the two calls of the function do (`hbody`). -/
theorem e_ct {n name : String} {body : Prog isa} {σ₁ σ₂ : State} (hsp12 : σ₁.sp = σ₂.sp)
    (hbody : RelCT isa (fun a b => a = eSave n σ₁ ∧ b = eSave n σ₂) (.call name body)
      fun c₁ c₂ => AfterE sig post stack σ₁ c₁ ∧ AfterE sig post stack σ₂ c₂) :
    RelCT isa (fun a b => a = allocated 16 σ₁ ∧ b = allocated 16 σ₂)
      (.seq (.block (enterD8 n)) (.seq (.call name body) (.block leaveD8))) fun _ _ => True := by
  refine RelCT.seq (R := fun a b => a = eSave n σ₁ ∧ b = eSave n σ₂)
    (RelCT.block_of fun a b hab => ?_) ?_
  · obtain ⟨rfl, rfl⟩ := hab
    exact ⟨_, _, _, enter_run n σ₁, by rw [enter_run n σ₂]; simp only [eslot, hsp12], rfl, rfl⟩
  refine RelCT.seq (R := fun c₁ c₂ => AfterE sig post stack σ₁ c₁ ∧ AfterE sig post stack σ₂ c₂) hbody ?_
  refine RelCT.block_of fun g₁ g₂ hg => ?_
  obtain ⟨⟨hw₁, hs₁, -⟩, ⟨hw₂, hs₂, -⟩⟩ := hg
  have i₁ : ∀ off, off + 8 ≤ 16 → InRegions (g₁.rd ++ g₁.wr) (g₁.sp + BitVec.ofNat 64 off) 8 :=
    fun off h => by rw [hw₁, hs₁]; exact eslot_in' σ₁ g₁.rd h
  have i₂ : ∀ off, off + 8 ≤ 16 → InRegions (g₂.rd ++ g₂.wr) (g₂.sp + BitVec.ofNat 64 off) 8 :=
    fun off h => by rw [hw₂, hs₂]; exact eslot_in' σ₂ g₂.rd h
  refine ⟨_, eRestore g₂, _, leave_run (i₁ 8 (by decide)) (i₁ 0 (by decide)), ?_, trivial⟩
  rw [leave_run (i₂ 8 (by decide)) (i₂ 0 (by decide)), hs₁, hs₂, hsp12]

end

/-! ## Under `abi.withConsts`, with the permutation's address public -/

section
variable {sig : Sig} {c₀ : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
  {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post : sig.Post abi.ptrBits}
  {wa : Bool} {stack : Nat} {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}

/-- The public data under `A.withFns [n]`: that under `A`, and `n`'s address. -/
theorem pub_fns {A : Abi isa} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)} {post : sig.Post A.ptrBits}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {st : Nat} {n : String} {s₁ s₂ : State}
    (h : (sig.contract (A.withFns [n]) pre post wa st leak).pub s₁ s₂) :
    (sig.contract A pre post wa st leak).pub s₁ s₂ ∧ s₁.syms n = s₂.syms n := by
  simp only [Sig.contract, Abi.withFns] at h ⊢
  revert h
  split
  · exact fun h => h.elim
  · intro h
    cases leak with
    | none => exact ⟨⟨h.1.1, h.2⟩, h.1.2 n (List.mem_singleton_self _)⟩
    | some f => exact ⟨⟨⟨h.1.1.1, h.1.2⟩, h.2⟩, h.1.1.2 n (List.mem_singleton_self _)⟩

/-- What `abi.withConsts` says of the tables holds at the function's entry. -/
theorem constsOk_eEntry (n : String) {s : State} (hsb : stack + 16 ≤ s.sp.toNat)
    (hc : ConstsOk (c₀ :: cs) (stack + 16) s) : ConstsOk (c₀ :: cs) stack (eEntry n s) := by
  obtain ⟨hd, hh, ht, hal⟩ := hc
  have hR : below s.sp (stack + 16) ∈ abi.reserved (stack + 16) s := reserved_below (by omega_using []) s
  refine ⟨hd, ?_, fun t ht' => ⟨(ht t ht').1, (ht t ht').2.1, fun q hq => ?_⟩, hal⟩
  · intro c hc i hi
    have htc : (⟨s.syms c.1, 8 * c.2.length⟩ : Region) ∈ constRegs (c₀ :: cs) s :=
      List.mem_map.mpr ⟨c, hc, rfl⟩
    have hfr : Frame [below s.sp 16] s.mem (eEntry n s).mem := eSave_frame n s
    have hb : (s.syms c.1).toNat + 8 * c.2.length ≤ 2 ^ 64 := (ht _ htc).1
    show (eEntry n s).mem.readW (s.syms c.1 + BitVec.ofNat 64 (8 * i)) 64 = c.2.getD i 0
    rw [hfr.readW (r := ⟨s.syms c.1, 8 * c.2.length⟩)
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hb]))
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ((ht _ htc).2.2 _ hR).sub_right (below_sub (by omega_using []) (by omega_using [hsb])))
      (by decide)]
    exact hh c hc i hi
  · have hq' : q ∈ stackBelow (s.sp - BitVec.ofNat 64 16) stack := hq
    rcases Nat.eq_zero_or_pos stack with h0 | h0
    · subst h0; simp [stackBelow] at hq'
    · rw [stackBelow_pos _ h0, List.mem_singleton] at hq'; subst hq'
      exact ((ht t ht').2.2 _ hR).sub_right (below_below _ 16 stack)

theorem stripConsts_eEntry (K : List (String × List (BitVec 64))) (n : String) (s : State) :
    stripConsts K (eEntry n s) = eEntry n (stripConsts K s) := rfl

theorem e_bodyPreK (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    {n : String} (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    {s : State} (hs : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 16) leak).pre s) :
    (Contract.d8 n (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa stack leak)).pre (eEntry n s) := by
  obtain ⟨hs₀, hc⟩ := pre_consts.mp hs
  have hsb : stack + 16 ≤ s.sp.toNat := e_sp (s := stripConsts (c₀ :: cs) s) hk hl hs₀
  refine ⟨pre_consts.mpr ⟨?_, constsOk_eEntry n hsb hc⟩, eEntry_d8 n s⟩
  rw [stripConsts_eEntry]
  exact e_bodyPre hk hl hpre hs₀

theorem e_bodyPubK (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (n : String) {s₁ s₂ : State}
    (h₁ : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 16) leak).pre s₁)
    (h₂ : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 16) leak).pre s₂)
    (hp : (sig.contract ((abi.withConsts (c₀ :: cs)).withFns [n]) pre post wa (stack + 16) leak).pub s₁ s₂)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak) :
    (Contract.d8 n (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa stack leak)).pub
      (eEntry n s₁) (eEntry n s₂) := by
  obtain ⟨hp', hn⟩ := pub_fns hp
  obtain ⟨hp₀, hsy⟩ := pub_consts.mp hp'
  exact ⟨pub_consts.mpr ⟨e_bodyPub hk hl n (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 hp₀ hleak, hsy⟩, hn⟩

/-- Code verified against `Contract.d8 n` of a contract under
`abi.withConsts (c₀ :: cs)` with `stack` bytes of stack, for a function
whose arguments are all in registers, is verified against the contract
under `(abi.withConsts (c₀ :: cs)).withFns [n]` with `stack + 16` bytes when
called by `entryD8 n`. The precondition must read the memory on entry
(`hpre`), and the postcondition the memory on entry and on return
(`hpost`, `hpostR`), only within the function's buffers. -/
theorem Verified.entryD8C {n name : String} {body : Prog isa}
    (h : Verified target body (Contract.d8 n (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa stack leak)))
    (hk : (sig.words abi.ptrBits).length ≤ 8) (hl : Sig.noLists sig.params = true)
    (hd : 16 * body.aarch64Depth ≤ stack)
    (hpre : ∀ vs m₁ m₂, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) pre vs m₁ → Curry.apply (sig.words abi.ptrBits) pre vs m₂)
    (hpost : ∀ vs m₁ m₂ m' x, vs.length = (sig.words abi.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m₁ m' x →
        Curry.apply (sig.words abi.ptrBits) post vs m₂ m' x)
    (hpostR : ∀ vs m m₁ m₂ x, vs.length = (sig.words abi.ptrBits).length →
      (Sig.bufs sig.params vs).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ x →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ x)
    (hsat : ∃ s, (sig.contract ((abi.withConsts (c₀ :: cs)).withFns [n]) pre post wa (stack + 16) leak).pre s)
    (hleak : Sig.LeakLocal abi.ptrBits sig leak := by trivial) :
    Verified target (entryD8 n name body)
      (sig.contract ((abi.withConsts (c₀ :: cs)).withFns [n]) pre post wa (stack + 16) leak) := by
  -- The postcondition reads the memory on return only within the buffers.
  have hout : ∀ s, (sig.contract abi pre post wa (stack + 16) leak).pre (stripConsts (c₀ :: cs) s) →
      ∀ m₁ m₂ x, (∀ b ∈ Sig.bufs sig.params (regArgs sig s), ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₁ x →
        Curry.apply (sig.words abi.ptrBits) post (regArgs sig s) s.mem m₂ x := by
    intro s hs m₁ m₂ x hag hq
    have hpw : (Sig.bufs sig.params (regArgs sig s)).Pairwise (fun a b => (a.2 || b.2) → a.1.Disjoint b.1) :=
      ((pre_regs' hk hl).mp hs).2.2.2.1
    exact hpostR _ _ _ _ _ (regArgs_length sig s hk) hpw hag hq
  -- The function's run, from the caller's state.
  have hbody : ∀ s, (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 16) leak).pre s →
      WP isa (.call name body) (eSave n s) (AfterE sig post stack s) := fun s hs =>
    e_body_wpOf (rd := (stripConsts (c₀ :: cs) s).rd) h.1 (fun _ _ h => post_consts.mp h) hk hl hd hpost
      (pre_consts.mp hs).1 (e_bodyPreK hk hl hpre hs)
  refine ⟨fun s hs => ?_, ?_, hsat⟩
  · have hs' : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 16) leak).pre s := hs
    have hs₀ := (pre_consts.mp hs').1
    obtain ⟨t, g, he, habi, hq⟩ :=
      e_wp (n := n) (post := post) (leak := leak) (rd := (stripConsts (c₀ :: cs) s).rd) hk hl hs₀
        (hbody s hs') (hout s hs₀)
    exact ⟨t, g, he, habi, (post_consts (c₀ := c₀) (cs := cs)).mpr hq⟩
  · refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.alloc (R := fun _ _ => True) ?_)
    refine RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_
    by_cases hP0 :
        (sig.contract ((abi.withConsts (c₀ :: cs)).withFns [n]) pre post wa (stack + 16) leak).pre σ₁ ∧
        (sig.contract ((abi.withConsts (c₀ :: cs)).withFns [n]) pre post wa (stack + 16) leak).pre σ₂ ∧
        (sig.contract ((abi.withConsts (c₀ :: cs)).withFns [n]) pre post wa (stack + 16) leak).pub σ₁ σ₂
    swap
    · exact RelCT.of_false fun a b hab => hP0 hab.1
    obtain ⟨h₁, h₂, hp⟩ := hP0
    have h₁' : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 16) leak).pre σ₁ := h₁
    have h₂' : (sig.contract (abi.withConsts (c₀ :: cs)) pre post wa (stack + 16) leak).pre σ₂ := h₂
    have hp₀ := (pub_consts.mp (pub_fns hp).1).1
    have hsp12 : σ₁.sp = σ₂.sp := ((pub_regs hk).mp hp₀).1.1.1
    refine RelCT.mono (P := fun a b => a = allocated 16 σ₁ ∧ b = allocated 16 σ₂)
      (e_ct (post := post) (stack := stack) hsp12 ?_) (fun a b hab => hab.2) (fun _ _ h => h)
    have hcov : ∀ σ : State, Covers (σ.rd ++ σ.wr) ((eSave n σ).rd ++ (eSave n σ).wr) ∧
        Covers σ.wr (eSave n σ).wr := fun σ =>
      ⟨Covers.append (Covers.refl _) (Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx),
        Covers.of_mem fun x hx => List.mem_cons_of_mem _ hx⟩
    refine RelCT.mono (RelCT.wp (F₁ := AfterE sig post stack σ₁) (F₂ := AfterE sig post stack σ₂)
      (RelCT.callEx h.1 h.2.1 fun a b hab => ?_) fun a b hab => ?_) (fun _ _ h => h) (fun _ _ h => h.2)
    · obtain ⟨rfl, rfl⟩ := hab
      exact ⟨σ₁.rd, σ₁.wr, σ₂.rd, σ₂.wr, e_bodyPreK hk hl hpre h₁', e_bodyPreK hk hl hpre h₂',
        e_bodyPubK hk hl n h₁' h₂' hp hleak, (hcov σ₁).1, (hcov σ₁).2, (hcov σ₂).1, (hcov σ₂).2⟩
    · obtain ⟨rfl, rfl⟩ := hab
      exact ⟨hbody σ₁ h₁', hbody σ₂ h₂'⟩

end

end VG.Proof.Sha3.AArch64
