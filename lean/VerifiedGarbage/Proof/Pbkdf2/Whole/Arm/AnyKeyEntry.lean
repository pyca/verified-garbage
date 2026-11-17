module

import VerifiedGarbage.Proof.Framework.EntryBranch
public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.Arm
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Loop
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.CT
public import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Proof.Hmac.Scratch
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Pbkdf2.Whole.Arm.AnyKeyCT`, which only this module used -/

section

/-! ### `Pbkdf2.Whole.Arm.AnyKey`, which only this module used -/

section

/-!
# HMAC's `init` for a key of any length on 32-bit ARM: correct

`initAny` (`Impl/Pbkdf2/Md/AnyKey/Arm.lean`) saves our caller's registers in
`scratch` (`prologue_ok`), makes the key as `pbkdf2` makes it from a password
(`key_ok`: the key, or its digest, hashed into `scratch` with the streaming
functions, if it is longer than a block), calls HMAC's `init` with it
(`call_ok`, through its shared contract), and loads our caller's registers
back. Each step is `pbkdf2`'s (`Key.lean`, `Setup.lean`), for this function's
arguments: `inner` (`r0`), `outer` (`r1`), `key` (`r2`), `key_len` (`r3`)
and `scratch` (`[sp]`). `anyScratchContract` is the contract it is verified
against: `VG.Spec.Hmac.initAnyKeyContract` with its working space as an
argument, with 24 bytes of stack.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.Arm.Any

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Pbkdf2.Stream.Arm (Hash scrAt)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK SavedRegs saveR FinArgs init_call fin_frame count savedRegs)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_ldrSp op2_imm op2_reg eval_eq)
open VG.Proof.Hmac.Generic.Common (bytes_keep bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (StreamingHash blockKey xorPad ipad opad)

/-! ## The contract -/

/-- `VG.Spec.Hmac.initAnyKeyContract` with its working space (`W` words) as
an argument (as `Proof.Hmac.initScratchContract` is `initContract`'s), and
24 bytes of stack: the contract that the function allocating the working
space follows from (`Verified.stackScratchWiped`). -/
def anyScratchContract (S : StreamingHash) (W : Nat) : Contract isa :=
  (Proof.Hmac.initScratchSig S W).contract Arm.abi
    (post := fun inner outer key keyLen _scratch => Spec.Hmac.initPost S Arm.abi.ptrBits inner outer key keyLen)
    (writeArgs := true) (stack := 24)

variable {F : Fns}

/-! ## The arguments and the regions -/

section
variable (s₀ : State)

abbrev inn : BitVec 32 := s₀.gpr .r0
abbrev out : BitVec 32 := s₀.gpr .r1
abbrev key : BitVec 32 := s₀.gpr .r2
abbrev kln : Nat := (s₀.gpr .r3).toNat
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev keyR : Region := ⟨State.addr (key s₀), kln s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
abbrev stkR : Region := stk s₀
/-- An address in `scratch`, as a register holds it and as an address, and a part of it. -/
abbrev dO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o
abbrev A (o : Nat) : Addr := State.addr (scr s₀) + BitVec.ofNat 64 o
abbrev sR (o n : Nat) : Region := ⟨A s₀ o, n⟩
/-- The working space of the functions we call. -/
abbrev lowR (k : Nat) : Region := ⟨State.addr (scr s₀), k⟩

end

section
variable (F) (s₀ : State)
abbrev innR : Region := ⟨State.addr (inn s₀), F.H.S⟩
abbrev outR : Region := ⟨State.addr (out s₀), F.H.S⟩
abbrev scR : Region := ⟨State.addr (scr s₀), F.L8⟩
/-- The save area of our caller's registers. -/
abbrev svR : Region := saveR F.L (scr s₀)
/-- The regions everything writes: the states, `scratch` and the stack below the stack pointer. -/
abbrev wrs : List Region := [innR F s₀, outR F s₀, scR F s₀, stkR s₀]
end

/-- The precondition. -/
structure Pre (F : Fns) (s₀ : State) : Prop where
  sp24 : 24 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 4 ≤ 2 ^ 32
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [innR F s₀, outR F s₀, scR F s₀]
  i_o : (innR F s₀).Disjoint (outR F s₀)
  i_k : (innR F s₀).Disjoint (keyR s₀)
  i_s : (innR F s₀).Disjoint (scR F s₀)
  i_a : (innR F s₀).Disjoint (argR s₀)
  o_k : (outR F s₀).Disjoint (keyR s₀)
  o_s : (outR F s₀).Disjoint (scR F s₀)
  o_a : (outR F s₀).Disjoint (argR s₀)
  k_s : (keyR s₀).Disjoint (scR F s₀)
  s_a : (scR F s₀).Disjoint (argR s₀)
  b_i : (stkR s₀).Disjoint (innR F s₀)
  b_o : (stkR s₀).Disjoint (outR F s₀)
  b_k : (stkR s₀).Disjoint (keyR s₀)
  b_s : (stkR s₀).Disjoint (scR F s₀)
  b_a : (stkR s₀).Disjoint (argR s₀)
  ni : (inn s₀).toNat + F.H.S ≤ 2 ^ 32
  no : (out s₀).toNat + F.H.S ≤ 2 ^ 32
  nk : (key s₀).toNat + kln s₀ ≤ 2 ^ 32
  nsc : (scr s₀).toNat + F.L8 ≤ 2 ^ 32

theorem pre_of (hF : FnsOK F) {s₀ : State}
    (h : (anyScratchContract hF.hH.SH (F.W + F.H.S)).pre s₀) : Pre F s₀ := by
  sig_pre [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  have hS := hF.hH.hS
  simp only [hS] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩

/-! ## The layout of `scratch` -/

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

omit hz in
theorem dO_addr {o : Nat} (ho : o < F.L8) : State.addr (dO s₀ o) = A s₀ o := by
  have := hp.nsc; exact addr_add (by omega_arith)

omit hz in
theorem dO_toNat {o : Nat} (ho : o < F.L8) : (dO s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nsc
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

omit hp hz in
theorem part_sub {o n : Nat} (h : o + n ≤ F.L8) : Region.Sub (sR s₀ o n) (scR F s₀) :=
  Offset.sub_base _ h

omit hp in
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ F.L8) (hb : b + n ≤ F.L8) :
    Region.Disjoint (sR s₀ a m) (sR s₀ b n) := by
  have := hz.reach; exact Offset.disjoint _ h (by omega_arith) (by omega_arith)

omit hp in
theorem low_disj {k b n : Nat} (hk : k ≤ b) (hbn : b + n ≤ F.L8) :
    Region.Disjoint (lowR s₀ k) (sR s₀ b n) := by
  have := hz.reach; exact Offset.base_disjoint _ hk (by omega_arith)

omit hp hz in
theorem low_sub {k : Nat} (hk : k ≤ F.L8) : Region.Sub (lowR s₀ k) (scR F s₀) := Region.sub_prefix hk

omit hp in
theorem sv_sub : Region.Sub (svR F s₀) (scR F s₀) := by
  have := end_le hz; have := layout (F := F)
  exact Offset.sub_base _ (by show 8 * F.W + 36 ≤ F.L8; omega_arith)

omit hp in
/-- A part of `scratch` after the save area is apart from it. -/
theorem sv_disj {o n : Nat} (ho : 8 * F.W + 36 ≤ o) (hon : o + n ≤ F.L8) : (svR F s₀).Disjoint (sR s₀ o n) := by
  have := hz.reach
  exact Offset.disjoint _ (Or.inl (by simp only [Fns.L]; omega_arith)) (by simp only [Fns.L]; omega_arith) (by omega_arith)

omit hp in
/-- The working space is apart from the save area. -/
theorem sv_low {k : Nat} (hk : k ≤ 8 * F.W) : (svR F s₀).Disjoint (lowR s₀ k) := by
  have := hz.reach; have := end_le hz; have := layout (F := F)
  exact (Offset.base_disjoint _ (k := k) (e := 8 * F.L.W) (n := 36) (by simp only [Fns.L]; omega_arith)
    (by simp only [Fns.L]; omega_arith)).symm

omit hz in
theorem sc_mem : scR F s₀ ∈ s₀.wr := by rw [hp.wr]; simp

end

/-! ## What every piece keeps -/

/-- The registers and memory kept from the prologue on. -/
structure KR (F : Fns) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r5 : s.gpr .r5 = inn s₀
  r6 : s.gpr .r6 = out s₀
  r11 : s.gpr .r11 = scr s₀
  saved : SavedRegs F.L (scr s₀) s₀ s.mem
  frame : Frame (wrs F s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r5, .r6, .r11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .lr := by decide

/-- The 24 bytes below the stack pointer, while `KR` holds. -/
theorem KR.stkE {s₀ s : State} (h : KR F s₀ s) : stk s = stkR s₀ := by
  show (⟨State.addr s.sp - 24, 24⟩ : Region) = ⟨State.addr s₀.sp - 24, 24⟩; rw [h.sp]

/-- `KR` survives changes to other registers, and to memory in the states,
`scratch` (away from the save area) and the stack. -/
theorem KR.keep {s₀ s s' : State} (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (svR F s₀).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs F s₀, Region.Sub r r') :
    KR F s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r5, (hg _ (by simp)).trans h.r6,
    (hg _ (by simp)).trans h.r11, h.saved.frame F.L hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.same {s₀ s s' : State} (h : KR F s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR F s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem KR.upd {s₀ s s' : State} (h : KR F s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR F s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

theorem KR.upd12 {s₀ s s' : State} (h : KR F s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd12 s s' d v) : KR F s₀ s' :=
  h.same u.rd u.wr u.sp (fun r hr => u.other r (fun e => hd (e ▸ hr)) (by
    simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    u.mem

/-- What a call leaves, writing the states, parts of `scratch` after the
save area, or the working space, and the stack below the stack pointer. -/
theorem KR.call {s₀ s s' : State} (hp : Pre F s₀) (hz : Sizes F) (h : KR F s₀ s) {ws : List Region}
    (ha : After s ws s')
    (hw : ∀ r ∈ ws, r = innR F s₀ ∨ r = outR F s₀ ∨ (∃ k, r = lowR s₀ k ∧ k ≤ 8 * F.W) ∨
      ∃ o n, r = sR s₀ o n ∧ 8 * F.W + 36 ≤ o ∧ o + n ≤ F.L8) : KR F s₀ s' := by
  have hL := end_le hz; have := layout (F := F)
  have f := ha.frame
  rw [h.stkE] at f
  refine h.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f
    (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with rfl | rfl | ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact (hp.i_s.sub_right (sv_sub hz)).symm
      · exact (hp.o_s.sub_right (sv_sub hz)).symm
      · exact sv_low hz hk
      · exact sv_disj hz h₁ h₂
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hp.b_s.sub_right (sv_sub hz)).symm
  · rcases List.mem_append.mp hr with hr | hr
    · rcases hw r hr with rfl | rfl | ⟨k, rfl, hk⟩ | ⟨o, n, rfl, h₁, h₂⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨scR F s₀, by simp, low_sub (F := F) (by omega_arith)⟩
      · exact ⟨_, by simp, part_sub h₂⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, fun _ h => h⟩

/-! ## The stack argument and the key, while `KR` holds -/

section
variable {s₀ : State} (hp : Pre F s₀)
include hp

theorem KR.stackArg0 {s : State} (hk : KR F s₀ s) : stackArg s 0 = stackArg s₀ 0 := by
  have ea : stackArgAddr s 0 = stackArgAddr s₀ 0 := by simp only [stackArgAddr, hk.sp]
  show s.mem.readW (stackArgAddr s 0) 32 = s₀.mem.readW (stackArgAddr s₀ 0) 32
  rw [ea]
  refine hk.frame.readW (r := argR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.i_a.symm
  · exact hp.o_a.symm
  · exact hp.s_a.symm
  · exact hp.b_a.symm

omit hp in
/-- The bytes of a region only read are those on entry. -/
theorem KR.bytes {s : State} (hk : KR F s₀ s) {p : Addr} {n : Nat} (hd : ∀ r ∈ wrs F s₀, Region.Disjoint ⟨p, n⟩ r)
    (hn : n ≤ 2 ^ 64) : bytesAt s.mem p n = bytesAt s₀.mem p n :=
  bytes_keep hk.frame hd hn

theorem KR.keyBytes {s : State} (hk : KR F s₀ s) :
    bytesAt s.mem (State.addr (key s₀)) (kln s₀) = bytesAt s₀.mem (State.addr (key s₀)) (kln s₀) :=
  hk.bytes (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.i_k.symm
    · exact hp.o_k.symm
    · exact hp.k_s
    · exact hp.b_k.symm) (by have := hp.nk; omega_arith)

end

/-- `d ← scratch + o` (through `r12`), while `KR` holds. -/
theorem scr_ok {s₀ s : State} (hk : KR F s₀ s) {d : Reg} {o : Nat} (ho : o < 2 ^ 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd12 s s' d (dO s₀ o) → WP isa (.block rest) s' Q) :
    WP isa (.block (scrAt d o ++ rest)) s Q := by
  simp only [scrAt, List.cons_append, List.nil_append]
  refine Pbkdf2.Stream.Arm.wp_movw fun s₁ u₁ => VG.Proof.MdStream.Arm.wp_add (VG.Proof.MdStream.Arm.op2_reg _ _)
    fun s₂ u₂ => k s₂ ⟨?_, fun r h₁ h₂ => by rw [u₂.other r h₁, u₁.other r h₂], by rw [u₂.mem, u₁.mem],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.sp, u₁.sp]⟩
  rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hk.r11, Pbkdf2.Stream.Arm.movw_ofNat ho]

/-! ## The prologue -/

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F)
include hp hz

/-- After the prologue: `KR`, and the key in `r8` and `r9`. -/
structure KK (F : Fns) (s₀ s : State) : Prop where
  kr : KR F s₀ s
  r8 : s.gpr .r8 = key s₀
  r9 : s.gpr .r9 = s₀.gpr .r3

theorem prologue_ok : WP isa (.block F.anyPrologue) s₀ (KK F s₀) := by
  have hL := end_le hz; have := layout (F := F); have hr := hz.reach
  have hsc := sc_mem hp
  simp only [Fns.anyPrologue, List.cons_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl (by
      rw [hp.rd, hp.wr]
      exact ⟨argR s₀, by simp, Region.contains_self _ _⟩) fun s₁ u₁ => ?_
  refine save_ok F.L (sc := scr s₀) (L := F.L8) u₁.gpr (by simp only [Fns.L]; omega_arith) (by rw [u₁.wr]; exact hsc)
    (by show 8 * F.W + 36 ≤ F.L8; omega_arith) hp.nsc fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      g₂, u₁.gpr]; rfl
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
    exact sv₂.of_eq F.L fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, ← u₁.mem]
    exact f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR F s₀, by simp, sv_sub hz⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      e₂ _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)]

/-! ## The stack and `scratch`, while `KR` holds -/

omit hp hz in
theorem below_sub {s : State} (hk : KR F s₀ s) : Region.Sub (Pbkdf2.Stream.Arm.below s) (stkR s₀) := by
  rw [← hk.stkE]; exact below_stk (n := 16) (by decide)

omit hz in
/-- A region of `scratch` is apart from the stack below the stack pointer. -/
theorem b24 {s : State} (hk : KR F s₀ s) {R : Region} (hR : Region.Sub R (scR F s₀)) : (stk s).Disjoint R := by
  rw [hk.stkE]; exact hp.b_s.sub_right hR

omit hz in
theorem b16 {s : State} (hk : KR F s₀ s) {R : Region} (hR : Region.Sub R (scR F s₀)) :
    (Pbkdf2.Stream.Arm.below s).Disjoint R :=
  (hp.b_s.sub_left (below_sub hk)).sub_right hR

omit hz in
/-- A part of `scratch` is in a region the code may write. -/
theorem cov_part {s : State} (hk : KR F s₀ s) {o n : Nat} (h : o + n ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (sR s₀ o n).base = r'.base + BitVec.ofNat 64 off ∧ off + (sR s₀ o n).len ≤ r'.len :=
  ⟨scR F s₀, by rw [hk.wr]; exact sc_mem hp, o, rfl, h⟩

omit hz in
theorem cov_low {s : State} (hk : KR F s₀ s) {k : Nat} (h : k ≤ F.L8) :
    ∃ r' ∈ s.wr, ∃ off, (lowR s₀ k).base = r'.base + BitVec.ofNat 64 off ∧ off + (lowR s₀ k).len ≤ r'.len :=
  ⟨scR F s₀, by rw [hk.wr]; exact sc_mem hp, 0, by simp, by simp only [Nat.zero_add]; exact h⟩

omit hz in
theorem cov_key {s : State} (hk : KR F s₀ s) : Covers [keyR s₀] (s.rd ++ s.wr) :=
  Pbkdf2.Stream.Arm.covers_one (List.mem_append_left _ (by rw [hk.rd, hp.rd]; simp))

/-! ## Hashing a key longer than a block -/

variable (hH : HashOK F.H)
include hH

omit hp hz hH in
/-- `r4 ← scratch + stWO`. -/
theorem hk1_ok {s : State} (hk : KK F s₀ s) (ho : F.stWO < 2 ^ 16) :
    WP isa (.block (scrAt .r4 F.stWO)) s fun t => KK F s₀ t ∧ t.gpr .r4 = dO s₀ F.stWO ∧ t.mem = s.mem := by
  rw [← List.append_nil (scrAt .r4 F.stWO)]
  exact scr_ok hk.kr ho fun s₁ u₁ => WP.block_nil ⟨⟨hk.kr.upd12 (by decide) u₁,
    by rw [u₁.other _ (by decide) (by decide), hk.r8], by rw [u₁.other _ (by decide) (by decide), hk.r9]⟩, u₁.gpr, u₁.mem⟩

omit hp hz hH in
/-- `r0 ← r4`, before `init`. -/
theorem hk2a_ok {s : State} (hk : KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) :
    WP isa (.block [.mov .r0 (.reg .r4)]) s fun t => KK F s₀ t ∧ t.gpr .r4 = dO s₀ F.stWO ∧
      t.gpr .r0 = dO s₀ F.stWO := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ⟨⟨hk.kr.upd (by decide) u₁, ?_, ?_⟩, ?_, ?_⟩
  · rw [u₁.other _ (by decide), hk.r8]
  · rw [u₁.other _ (by decide), hk.r9]
  · rw [u₁.other _ (by decide), h4]
  · rw [u₁.gpr, h4]

/-- `init` on the working state. -/
theorem hk2b_ok {s : State} (hk : KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) (h0 : s.gpr .r0 = dO s₀ F.stWO) :
    WP isa (.call F.H.initN F.H.initC) s fun t => KK F s₀ t ∧ hH.SH.Repr t.mem (A s₀ F.stWO) [] ∧
      t.gpr .r4 = dO s₀ F.stWO := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.reach
  have ea := dO_addr hp (o := F.stWO) hz.stWO_lt
  have cw : Covers [⟨State.addr (dO s₀ F.stWO), F.H.S⟩] s.wr := by
    rw [ea]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp hk.kr hz.stWO_S
  refine init_call hH (st := dO s₀ F.stWO) h0 (by rw [dO_toNat hp hz.stWO_lt]; have := hp.nsc; omega_arith)
    cw fun s' a r => ?_
  have a' := After.of_hmac a
  refine ⟨⟨hk.kr.call hp hz a' fun r hr => ?_, ?_, ?_⟩, by rw [← ea]; exact r, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact .inr (.inr (.inr ⟨_, _, by rw [ea], by omega_arith, by omega_arith⟩))
  · rw [a.cs _ (by decide) (by decide), hk.r8]
  · rw [a.cs _ (by decide) (by decide), hk.r9]
  · rw [a.cs _ (by decide) (by decide), h4]

/-- `init` on the working state. -/
theorem hk2_ok {s : State} (hk : KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) :
    WP isa (F.H.callInit .r4) s fun t => KK F s₀ t ∧ hH.SH.Repr t.mem (A s₀ F.stWO) [] ∧
      t.gpr .r4 = dO s₀ F.stWO := by
  unfold Hash.callInit
  exact WP.seq (WP.mono (hk2a_ok hk h4) fun s₁ ⟨k₁, d₁, a₁⟩ => hk2b_ok hp hz hH k₁ d₁ a₁)

omit hp hz hH in
/-- `update`'s arguments: the key. -/
theorem hk3_ok {s : State} (hk : KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) :
    WP isa (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r8), .mov .r7 (.reg .r9), .mov .r10 (.reg .r11),
      .mov .r2 (.imm 0), .mov .r3 (.imm 0)]) s fun t => KK F s₀ t ∧ t.gpr .r4 = dO s₀ F.stWO ∧
        t.gpr .r0 = dO s₀ F.stWO ∧ t.gpr .r1 = key s₀ ∧ t.gpr .r7 = s₀.gpr .r3 ∧ t.gpr .r10 = scr s₀ ∧
        count t = BitVec.ofNat 64 0 ∧ t.mem = s.mem := by
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_imm (by decide))
    fun s₆ u₆ => WP.block_nil ?_
  have k₆ := (((((hk.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
    (by decide) u₅).upd (by decide) u₆
  refine ⟨⟨k₆, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hk.r8]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hk.r9]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, h4]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), hk.r8]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hk.r9]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hk.kr.r11]
  · simp only [count]; rw [u₆.gpr, u₆.other .r2 (by decide), u₅.gpr]; rfl

theorem hk4_args {s : State} (hk : KK F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stWO) (h1 : s.gpr .r1 = key s₀)
    (h7 : s.gpr .r7 = s₀.gpr .r3) (h10 : s.gpr .r10 = scr s₀) :
    UpdL hH s (dO s₀ F.stWO) (key s₀) (scr s₀) (kln s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hH.hWb
  have k := hk.kr
  have ea := dO_addr hp (o := F.stWO) hz.stWO_lt
  exact
    { r0 := h0
      r1 := h1
      r7 := by rw [h7, ofNat_toNat32]
      r10 := h10
      hlen := (s₀.gpr .r3).isLt
      sp16 := by rw [k.sp]; have := hp.sp24; omega_arith
      cd := cov_key hp k
      cw := by
        rw [ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact cov_part hp k hz.stWO_S
          · exact cov_low hp k (by omega_arith)
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega_arith) hz.stWO_S).symm
      d_st := by rw [ea]; exact hp.k_s.sub_right (part_sub hz.stWO_S)
      d_sc := hp.k_s.sub_right (low_sub (by omega_arith))
      b_st := by rw [ea]; exact b16 hp k (part_sub hz.stWO_S)
      b_d := hp.b_k.sub_left (below_sub k)
      b_sc := b16 hp k (low_sub (by omega_arith))
      nst := by rw [dO_toNat hp hz.stWO_lt]; have := hp.nsc; omega_arith
      nd := hp.nk
      nsc := by have := hp.nsc; omega_arith }

theorem hk4_ok {s : State} (hk : KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) (h0 : s.gpr .r0 = dO s₀ F.stWO)
    (h1 : s.gpr .r1 = key s₀) (h7 : s.gpr .r7 = s₀.gpr .r3) (h10 : s.gpr .r10 = scr s₀)
    (hc : count s = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (A s₀ F.stWO) []) :
    WP isa (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16)) s
      fun t => KK F s₀ t ∧ t.gpr .r4 = dO s₀ F.stWO ∧
        hH.SH.Repr t.mem (A s₀ F.stWO) (bytesAt s₀.mem (State.addr (key s₀)) (kln s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) hz.stWO_lt
  refine upd_frame hH (hk4_args hp hz hH hk h0 h1 h7 h10) fun s' a r => ⟨⟨hk.kr.call hp hz (After.of_hmac a)
    fun r hr => ?_, by rw [a.cs _ (by decide) (by decide), hk.r8], by rw [a.cs _ (by decide) (by decide), hk.r9]⟩,
    by rw [a.cs _ (by decide) (by decide), h4], ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inr (.inr ⟨_, _, by rw [ea], by omega_arith, by omega_arith⟩))
    · exact .inr (.inr (.inl ⟨_, rfl, by omega_arith⟩))
  · have := r [] (by rw [ea]; exact hr) hc
    rwa [List.nil_append, ea, hk.kr.keyBytes hp] at this

omit hp hz hH in
/-- `finalize`'s arguments: the digest into `scratch`. -/
theorem hk5_ok {s : State} (hk : KK F s₀ s) (h4 : s.gpr .r4 = dO s₀ F.stWO) (ho : F.hkO < 2 ^ 16) :
    WP isa (.block (([.mov .r0 (.reg .r4)] : List Instr) ++ scrAt .r1 F.hkO ++
      ([.mov .r12 (.reg .r11), .mov .r2 (.reg .r9), .mov .r3 (.imm 0)] : List Instr))) s fun t =>
        KK F s₀ t ∧ t.gpr .r0 = dO s₀ F.stWO ∧ t.gpr .r1 = dO s₀ F.hkO ∧
        t.gpr .r12 = scr s₀ ∧ count t = BitVec.ofNat 64 (kln s₀) ∧ t.mem = s.mem := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have k₁ := hk.kr.upd (by decide) u₁
  refine scr_ok k₁ ho fun s₂ u₂ => ?_
  have k₂ := k₁.upd12 (by decide) u₂
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_imm (by decide))
    fun s₅ u₅ => WP.block_nil ?_
  have k₅ := ((k₂.upd (by decide) u₃).upd (by decide) u₄).upd (by decide) u₅
  have e8 : s₂.gpr .r8 = key s₀ := by rw [u₂.other _ (by decide) (by decide), u₁.other _ (by decide), hk.r8]
  have e9 : s₂.gpr .r9 = s₀.gpr .r3 := by rw [u₂.other _ (by decide) (by decide), u₁.other _ (by decide), hk.r9]
  refine ⟨⟨k₅, ?_, ?_⟩, ?_, ?_, ?_, ?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e8]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e9]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide) (by decide),
      u₁.gpr, h4]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide) (by decide),
      u₁.other _ (by decide), hk.kr.r11]
  · simp only [count]; rw [u₅.gpr, u₅.other .r2 (by decide), u₄.gpr, u₃.other _ (by decide), e9, zero_append]

theorem hk6_args {s : State} (hk : KK F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stWO) (h1 : s.gpr .r1 = dO s₀ F.hkO)
    (h12 : s.gpr .r12 = scr s₀) : FinArgs hH s (dO s₀ F.stWO) (dO s₀ F.hkO) (scr s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hH.hWb
  have k := hk.kr
  have ea := dO_addr hp (o := F.stWO) hz.stWO_lt
  have eh := dO_addr hp (o := F.hkO) hz.hkO_lt
  exact
    { r0 := h0
      r1 := h1
      r12 := h12
      sp16 := by rw [k.sp]; have := hp.sp24; omega_arith
      cw := by
        rw [ea, eh]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact cov_part hp k hz.stWO_S
          · exact cov_part hp k hz.hkO_F
          · exact cov_low hp k (by omega_arith)
      st_o := by rw [ea, eh]; exact part_disj hz (Or.inl (by omega_arith)) hz.stWO_S hz.hkO_F
      st_sc := by rw [ea]; exact (low_disj hz (k := hH.Wb) (by omega_arith) hz.stWO_S).symm
      o_sc := by rw [eh]; exact (low_disj hz (k := hH.Wb) (by omega_arith) hz.hkO_F).symm
      b_st := by rw [ea]; exact b16 hp k (part_sub hz.stWO_S)
      b_o := by rw [eh]; exact b16 hp k (part_sub hz.hkO_F)
      b_sc := b16 hp k (low_sub (by omega_arith))
      nst := by rw [dO_toNat hp hz.stWO_lt]; have := hp.nsc; omega_arith
      no := by rw [dO_toNat hp hz.hkO_lt]; have := hp.nsc; omega_arith
      nsc := by have := hp.nsc; omega_arith }

theorem hk6_ok {s : State} (hk : KK F s₀ s) (h0 : s.gpr .r0 = dO s₀ F.stWO) (h1 : s.gpr .r1 = dO s₀ F.hkO)
    (h12 : s.gpr .r12 = scr s₀) (hc : count s = BitVec.ofNat 64 (kln s₀))
    (hr : hH.SH.Repr s.mem (A s₀ F.stWO) (bytesAt s₀.mem (State.addr (key s₀)) (kln s₀))) :
    WP isa (.frame (.push [.r1, .r12]) (.call F.H.finN F.H.finC) (.pop .r1 8)) s
      fun t => KR F s₀ t ∧
        bytesAt t.mem (A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem (State.addr (key s₀)) (kln s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hH.hWb
  have ea := dO_addr hp (o := F.stWO) hz.stWO_lt
  have eh := dO_addr hp (o := F.hkO) hz.hkO_lt
  refine fin_frame hH (hk6_args hp hz hH hk h0 h1 h12) fun s' a r => ⟨hk.kr.call hp hz (After.of_hmac a)
    fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inr (.inr ⟨_, _, by rw [ea], by omega_arith, by omega_arith⟩))
    · exact .inr (.inr (.inr ⟨_, _, by rw [eh], by omega_arith, by omega_arith⟩))
    · exact .inr (.inr (.inl ⟨_, rfl, by omega_arith⟩))
  · rw [bytesAt_take _ _ hz.D.2.1, ← eh]
    exact r _ (by rw [ea]; exact hr) (by rw [bytesAt_length]; exact Nat.lt_trans (s₀.gpr .r3).isLt (by decide))
      (by rw [bytesAt_length]; exact hc)

omit hp hz hH in
theorem hk7_ok {s : State} (hk : KR F s₀ s) (ho : F.hkO < 2 ^ 16) (hD : F.H.D < 2 ^ 16) :
    WP isa (.block (scrAt .r2 F.hkO ++ ([.movw .r3 (BitVec.ofNat 16 F.H.D)] : List Instr))) s
      fun t => KR F s₀ t ∧ t.gpr .r2 = dO s₀ F.hkO ∧ t.gpr .r3 = BitVec.ofNat 32 F.H.D ∧ t.mem = s.mem :=
  scr_ok hk ho fun s₁ u₁ => Pbkdf2.Stream.Arm.wp_movw fun s₂ u₂ => WP.block_nil
    ⟨(hk.upd12 (by decide) u₁).upd (by decide) u₂, by rw [u₂.other _ (by decide), u₁.gpr],
      by rw [u₂.gpr, Pbkdf2.Stream.Arm.movw_ofNat hD], by rw [u₂.mem, u₁.mem]⟩

theorem hashKey_ok {s : State} (hk : KK F s₀ s) :
    WP isa F.hashKey s fun t => KR F s₀ t ∧ t.gpr .r2 = dO s₀ F.hkO ∧ t.gpr .r3 = BitVec.ofNat 32 F.H.D ∧
      bytesAt t.mem (A s₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt s₀.mem (State.addr (key s₀)) (kln s₀)) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.reach
  unfold Fns.hashKey
  refine WP.seq (WP.mono (hk1_ok hk hz.stWO_lt16) fun s₁ ⟨k₁, d₁, _⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hp hz hH k₁ d₁) fun s₂ ⟨k₂, r₂, e₂⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok k₂ e₂) fun s₃ ⟨k₃, d₃, a₀, a₁, a₇, a₁₀, c₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hp hz hH k₃ d₃ a₀ a₁ a₇ a₁₀ c₃ (by rw [m₃]; exact r₂)) fun s₄ ⟨k₄, d₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok k₄ d₄ hz.hkO_lt16) fun s₅ ⟨k₅, a₀', a₁', a₁₂, c₅, m₅⟩ => ?_)
  refine WP.seq (WP.mono (hk6_ok hp hz hH k₅ a₀' a₁' a₁₂ c₅ (by rw [m₅]; exact r₄)) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact WP.mono (hk7_ok k₆ hz.hkO_lt16 hz.D_lt16) fun t ⟨k, d, c, m⟩ => ⟨k, d, c, by rw [m]; exact b₆⟩

end

/-! ## The key -/

section
variable {s₀ : State} (hz : Sizes F)
include hz

theorem cmp_ok {s : State} (hk : KK F s₀ s) :
    WP isa (.block F.cmpPw) s fun t => KK F s₀ t ∧ t.z = decide (kln s₀ < F.H.B + 1) ∧ t.mem = s.mem := by
  have := hz.B
  unfold Fns.cmpPw
  rw [← List.append_nil [Instr.subs .r12 .r9 (.imm (BitVec.ofNat 32 (F.H.B + 1))), .mov .r12 (.imm 0),
    .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)]]
  refine wp_lt hz.encB1 fun s' g m rd wr sp z => WP.block_nil ⟨⟨hk.kr.same rd wr sp (fun r hr => g r (by
    simp only [kregs, List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) m,
    by rw [g _ (by decide), hk.r8], by rw [g _ (by decide), hk.r9]⟩, ?_, m⟩
  rw [z, hk.r9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := F.H.B + 1) (by omega_arith)]

end

/-- Where the key is, and its length. -/
abbrev kp (F : Fns) (s₀ : State) : BitVec 32 := if kln s₀ < F.H.B + 1 then key s₀ else dO s₀ F.hkO
abbrev kl (F : Fns) (s₀ : State) : Nat := if kln s₀ < F.H.B + 1 then kln s₀ else F.H.D

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F) (hH : HashOK F.H)
include hp hz hH

theorem key_ok {s : State} (hk : KK F s₀ s) :
    WP isa F.key s fun t => KR F s₀ t ∧ t.gpr .r2 = kp F s₀ ∧ t.gpr .r3 = BitVec.ofNat 32 (kl F s₀) ∧
      blockKey hH.SH.H (bytesAt t.mem (State.addr (kp F s₀)) (kl F s₀)) =
        blockKey hH.SH.H (bytesAt s₀.mem (State.addr (key s₀)) (kln s₀)) := by
  unfold Fns.key
  refine WP.seq (WP.mono (cmp_ok hz hk) fun s₁ ⟨k₁, z₁, _⟩ => ?_)
  refine WP.ite (decide (kln s₀ < F.H.B + 1)) (by show eval .eq s₁ = _; rw [eval_eq, z₁]) (fun hT => ?_) fun hF => ?_
  · have hlt : kln s₀ < F.H.B + 1 := of_decide_eq_true hT
    simp only [kp, kl, hlt, ↓reduceIte]
    refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil
      ⟨(k₁.kr.upd (by decide) u₂).upd (by decide) u₃, ?_, ?_, ?_⟩
    · rw [u₃.other _ (by decide), u₂.gpr, k₁.r8]
    · rw [u₃.gpr, u₂.other _ (by decide), k₁.r9, ofNat_toNat32]
    · rw [u₃.mem, u₂.mem, k₁.kr.keyBytes hp]
  · have hlt : ¬ kln s₀ < F.H.B + 1 := of_decide_eq_false hF
    simp only [kp, kl, hlt, ↓reduceIte]
    refine WP.mono (hashKey_ok hp hz hH k₁) fun t ⟨k, d, c, b⟩ => ⟨k, d, c, ?_⟩
    have := hz.D; have := hz.reach
    rw [dO_addr hp (by have := end_le hz; have := layout (F := F); omega_arith),
      b, blockKey_hash hz hH (by rw [bytesAt_length]; omega_arith) (hash_len hH b)]

omit hH in
/-- The key's region is the key, or its digest in `scratch`. -/
theorem key_cases : (kp F s₀ = key s₀ ∧ kl F s₀ = kln s₀ ∧ kln s₀ ≤ F.H.B) ∨
    (State.addr (kp F s₀) = A s₀ F.hkO ∧ kl F s₀ = F.H.D) := by
  by_cases h : kln s₀ < F.H.B + 1
  · exact .inl ⟨by simp [kp, h], by simp [kl, h], by omega_arith⟩
  · refine .inr ⟨?_, by simp [kl, h]⟩
    simp only [kp, h, ↓reduceIte]
    exact dO_addr hp (by have := end_le hz; have := layout (F := F); have := hz.D; omega_arith)

omit hH in
theorem kl_le : kl F s₀ ≤ F.H.B := by
  have := hz.DB
  rcases key_cases hp hz with ⟨-, h, h'⟩ | ⟨-, h⟩ <;> omega_arith

omit hH in
theorem key_toNat : (kp F s₀).toNat + kl F s₀ ≤ 2 ^ 32 := by
  by_cases h : kln s₀ < F.H.B + 1
  · simp only [kp, kl, h, ↓reduceIte]; exact hp.nk
  · simp only [kp, kl, h, ↓reduceIte]
    have := end_le hz; have := layout (F := F); have := hz.D
    rw [dO_toNat hp hz.hkO_lt]
    have := hp.nsc; omega_arith

omit hH in
/-- The key is apart from the parts of `scratch` but its digest. -/
theorem key_disj {R : Region} (hR : Region.Sub R (scR F s₀))
    (hd : R.Disjoint (sR s₀ F.hkO F.H.D)) : Region.Disjoint ⟨State.addr (kp F s₀), kl F s₀⟩ R := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.k_s.sub_right hR
  · rw [h, h']; exact hd.symm

omit hH in
theorem key_inn : Region.Disjoint ⟨State.addr (kp F s₀), kl F s₀⟩ (innR F s₀) := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.i_k.symm
  · rw [h, h']; exact (hp.i_s.sub_right (part_sub (hz.hkO_D))).symm

omit hH in
theorem key_out : Region.Disjoint ⟨State.addr (kp F s₀), kl F s₀⟩ (outR F s₀) := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.o_k.symm
  · rw [h, h']; exact (hp.o_s.sub_right (part_sub (hz.hkO_D))).symm

omit hH in
theorem key_stk {s : State} (hk : KR F s₀ s) : (stk s).Disjoint ⟨State.addr (kp F s₀), kl F s₀⟩ := by
  rw [hk.stkE]
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact hp.b_k
  · rw [h, h']; exact hp.b_s.sub_right (part_sub hz.hkO_D)

omit hH in
theorem key_cov {s : State} (hk : KR F s₀ s) : Covers [⟨State.addr (kp F s₀), kl F s₀⟩] (s.rd ++ s.wr) := by
  rcases key_cases hp hz with ⟨h, h', -⟩ | ⟨h, h'⟩
  · rw [h, h']; exact cov_key hp hk
  · rw [h, h']
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', off, e, l⟩ := cov_part hp hk (o := F.hkO) (n := F.H.D) hz.hkO_D
      exact ⟨r', List.mem_append_right _ hr', off, e, l⟩

end

/-! ## HMAC's `init` -/

/-- `K₀`, the key padded (or hashed and padded) to a block. -/
abbrev K0 (hF : FnsOK F) (s₀ : State) : List Byte :=
  blockKey hF.hH.SH.H (bytesAt s₀.mem (State.addr (key s₀)) (kln s₀))

/-- After the key: where it is, and its `K₀`. -/
structure Keyed (hF : FnsOK F) (s₀ s : State) : Prop where
  kr : KR F s₀ s
  r2 : s.gpr .r2 = kp F s₀
  r3 : s.gpr .r3 = BitVec.ofNat 32 (kl F s₀)
  k0 : blockKey hF.hH.SH.H (bytesAt s.mem (State.addr (kp F s₀)) (kl F s₀)) = K0 hF s₀

section
variable {s₀ : State} (hp : Pre F s₀) (hz : Sizes F) (hF : FnsOK F)
include hp hz hF

theorem keyed_ok {s : State} (hk : KK F s₀ s) : WP isa F.key s (Keyed hF s₀) :=
  WP.mono (key_ok hp hz hF.hH hk) fun _ ⟨k, d, c, b⟩ => ⟨k, d, c, b⟩

omit hp hz in
theorem args_ok {s : State} (h : Keyed hF s₀ s) :
    WP isa (.block Fns.anyArgs) s
      fun t => Keyed hF s₀ t ∧ t.gpr .r0 = inn s₀ ∧ t.gpr .r1 = out s₀ ∧ t.gpr .r12 = scr s₀ := by
  unfold Fns.anyArgs
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    WP.block_nil ⟨⟨((h.kr.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r2]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r3]
  · rw [u₃.mem, u₂.mem, u₁.mem]; exact h.k0
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.kr.r5]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.kr.r6]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.kr.r11]

theorem call_args {s : State} (h : Keyed hF s₀ s) (h0 : s.gpr .r0 = inn s₀) (h1 : s.gpr .r1 = out s₀)
    (h12 : s.gpr .r12 = scr s₀) :
    HiArgs hF.hH.SH hF.Wi s (inn s₀) (out s₀) (kp F s₀) (scr s₀) (kl F s₀) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W; have := hz.reach
  have := hF.hWi; have hS := hF.hH.hS
  have hk := h.kr
  have kls : Region.Disjoint ⟨State.addr (kp F s₀), kl F s₀⟩ (lowR s₀ (hF.Wi * 8)) :=
    key_disj hp hz (low_sub (by omega_arith)) (low_disj hz (by omega_arith) hz.hkO_D)
  exact
    { r0 := h0
      r1 := h1
      r2 := h.r2
      r3 := h.r3
      r12 := h12
      klB := by rw [hF.hH.hB]; exact kl_le hp hz
      kl32 := by have := kl_le hp hz; have := hz.B; omega_arith
      sp := by rw [hk.sp]; exact hp.sp24
      cr := key_cov hp hz hk
      cw := by
        rw [hS]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ⟨innR F s₀, by rw [hk.wr, hp.wr]; simp, 0, by simp, by simp⟩
          · exact ⟨outR F s₀, by rw [hk.wr, hp.wr]; simp, 0, by simp, by simp⟩
          · exact cov_low hp hk (by omega_arith)
      i_o := by rw [hS]; exact hp.i_o
      i_k := by rw [hS]; exact (key_inn hp hz).symm
      i_s := by rw [hS]; exact hp.i_s.sub_right (low_sub (by omega_arith))
      o_k := by rw [hS]; exact (key_out hp hz).symm
      o_s := by rw [hS]; exact hp.o_s.sub_right (low_sub (by omega_arith))
      k_s := kls
      b_i := by rw [hS, hk.stkE]; exact hp.b_i
      b_o := by rw [hS, hk.stkE]; exact hp.b_o
      b_k := key_stk hp hz hk
      b_s := b24 hp hk (low_sub (by omega_arith))
      ni := by rw [hS]; exact hp.ni
      no := by rw [hS]; exact hp.no
      nk := key_toNat hp hz
      nsc := by have := hp.nsc; omega_arith }

theorem call_ok {s : State} (h : Keyed hF s₀ s) (h0 : s.gpr .r0 = inn s₀) (h1 : s.gpr .r1 = out s₀)
    (h12 : s.gpr .r12 = scr s₀) :
    WP isa (.frame (.push [.r12, .lr]) (.call F.hiN F.hiC) (.pop .r12 8)) s fun t => KR F s₀ t ∧
      hF.hH.SH.Repr t.mem (State.addr (inn s₀)) (xorPad (K0 hF s₀) ipad) ∧
      hF.hH.SH.Repr t.mem (State.addr (out s₀)) (xorPad (K0 hF s₀) opad) := by
  have hl := layout (F := F); have he := end_le hz; have := hz.S; have := hz.D; have := hz.W
  have := hF.hWi; have hS := hF.hH.hS
  refine hi_frame hF.hi hF.hiSt (call_args hp hz hF h h0 h1 h12) fun s' a r0 r1 => ⟨?_, ?_, ?_⟩
  · refine h.kr.call hp hz a fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (by rw [hS])
    · exact .inr (.inl (by rw [hS]))
    · exact .inr (.inr (.inl ⟨_, rfl, by omega_arith⟩))
  · rw [h.k0] at r0; exact r0
  · rw [h.k0] at r1; exact r1

/-! ## The function -/

theorem correct : WP isa F.hmacInitAny s₀ fun s' =>
    abiPreserved s₀ s' ∧ (anyScratchContract hF.hH.SH (F.W + F.H.S)).post s₀ s' := by
  unfold Fns.hmacInitAny
  refine WP.seq (WP.mono (prologue_ok hp hz) fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (keyed_ok hp hz hF k₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (args_ok hF h₂) fun s₃ ⟨h₃, a₀, a₁, a₁₂⟩ => ?_)
  refine WP.seq (WP.mono (call_ok hp hz hF h₃ a₀ a₁ a₁₂) fun s₄ ⟨k₄, r0, r1⟩ => ?_)
  have hr := hz.reach; have := end_le hz; have := layout (F := F)
  refine WP.mono (restore_ok F.L k₄.r11 (by simp only [Fns.L]; omega_arith) k₄.saved
    (by rw [k₄.wr]; exact sc_mem hp) (show 8 * F.W + 36 ≤ F.L8 by omega_arith) hp.nsc)
    fun s' ⟨hm, _, _, hsp, hg⟩ => ⟨⟨fun r hr => hg r (Pbkdf2.Stream.Arm.preserved_saved r hr), by rw [hsp, k₄.sp]⟩,
      ?_⟩
  sig_post [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]
  rw [hm]; exact ⟨r0, r1⟩

end

end VG.Proof.Pbkdf2.Whole.Arm.Any

end

end


/-!
# HMAC's `init` for a key of any length on 32-bit ARM: constant time, and in a frame of its own

As for `pbkdf2` (`CT.lean`): the pieces of code between the calls are checked
by the taint analysis (`AnyChecks`, which the kernel evaluates for each hash
function), with the stack argument and the registers holding pointers and
lengths public (`piece`); the calls are related by their contracts
(`init_rel`, `upd_rel`, `fin_rel`, `hi_rel`), whose public arguments are the
same in two runs with the same public arguments (`PubEq`). The only branch,
whether the key is hashed, depends only on `key_len`.

The function that allocates the working space in a frame of its own and
wipes it (`withStackScratchWiped`) is verified against
`VG.Spec.Hmac.initAnyKeyContract` (`anyFramed`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.Arm.Any

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Impl.Pbkdf2.Stream.Arm (Hash scrAt)
open VG.Proof.Pbkdf2.Stream.Arm (HashOK count FinArgs init_rel fin_rel)
open VG.Proof.MdStream.Arm (eval_eq)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad)
open VG.Proof.Hmac.Common (bytesAt_length)

/-- A piece of code the taint analysis accepts with the stack argument and `rs` public. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check taint (argTaint rs 4) c hc).isSome = true

/-- The taint checks of the pieces of `initAny` between its calls. -/
structure AnyChecks (F : Fns) : Prop where
  pro : Ck inRegs (.block F.anyPrologue)
  cmp : Ck kkRegs (.block F.cmpPw)
  hk1 : Ck kkRegs (.block (scrAt .r4 F.stWO))
  hk2 : Ck hkRegs (.block [.mov .r0 (.reg .r4)])
  hk3 : Ck hkRegs (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r8), .mov .r7 (.reg .r9), .mov .r10 (.reg .r11),
    .mov .r2 (.imm 0), .mov .r3 (.imm 0)])
  hk5 : Ck hkRegs (.block ([.mov .r0 (.reg .r4)] ++ scrAt .r1 F.hkO ++ [.mov .r12 (.reg .r11), .mov .r2 (.reg .r9),
    .mov .r3 (.imm 0)]))
  hk7 : Ck krRegs (.block (scrAt .r2 F.hkO ++ [.movw .r3 (BitVec.ofNat 16 F.H.D)]))
  short : Ck kkRegs (.block [.mov .r2 (.reg .r8), .mov .r3 (.reg .r9)])
  args : Ck krRegs (.block Fns.anyArgs)
  restore : Ck krRegs (.block F.L.restore)

/-- The public arguments of two runs are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  sp : s₀.sp = s₀'.sp
  r0 : s₀.gpr .r0 = s₀'.gpr .r0
  r1 : s₀.gpr .r1 = s₀'.gpr .r1
  r2 : s₀.gpr .r2 = s₀'.gpr .r2
  r3 : s₀.gpr .r3 = s₀'.gpr .r3
  a0 : stackArg s₀ 0 = stackArg s₀' 0

variable {F : Fns}

section
variable {s₀ s₀' : State} (hq : PubEq s₀ s₀')
include hq

theorem PubEq.scrEq : scr s₀' = scr s₀ := hq.a0.symm
theorem PubEq.keyEq : key s₀' = key s₀ := hq.r2.symm
theorem PubEq.innEq : inn s₀' = inn s₀ := hq.r0.symm
theorem PubEq.outEq : out s₀' = out s₀ := hq.r1.symm
theorem PubEq.klnEq : kln s₀' = kln s₀ := by show (s₀'.gpr .r3).toNat = _; rw [← hq.r3]
theorem PubEq.dOEq (o : Nat) : dO s₀' o = dO s₀ o := by show scr s₀' + _ = _; rw [hq.scrEq]
theorem PubEq.kpEq : kp F s₀' = kp F s₀ := by
  show (if kln s₀' < F.H.B + 1 then key s₀' else dO s₀' F.hkO) = _
  rw [hq.klnEq, hq.keyEq, hq.dOEq]
theorem PubEq.klEq : kl F s₀' = kl F s₀ := by
  show (if kln s₀' < F.H.B + 1 then kln s₀' else F.H.D) = _
  rw [hq.klnEq]

end

/-- The stack argument lies outside the writable regions. -/
theorem args_out {t : State} (h : Pre F t) {s : State} (hsp : s.sp = t.sp) (hwr : s.wr = t.wr) :
    s.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 4⟩ r := by
  have e : (⟨State.addr s.sp, 4⟩ : Region) = argR t := by simp [stackArgAddr, hsp]
  refine ⟨by rw [hsp]; exact h.spf, ?_⟩
  rw [e, hwr, h.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact h.i_a.symm
  · exact h.o_a.symm
  · exact h.s_a.symm

section
variable {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀')
include hp hp' hq

/-- Two states agree on the taint `argTaint rs 4`. -/
theorem agree {rs : List Reg} {s s' : State} (hk : KR F s₀ s) (hk' : KR F s₀' s')
    (hag : ∀ r ∈ rs, s.gpr r = s'.gpr r) : VG.Arm.Taint.Agree (argTaint rs 4) s s' :=
  agree_argTaint hag (by rw [hk.sp, hk'.sp, hq.sp]) (args_out hp hk.sp hk.wr) (args_out hp' hk'.sp hk'.wr)
    (argMem_of (j := 1) (by rw [hk.sp, hk'.sp, hq.sp]) (by rw [hk.sp]; exact hp.spf) fun i hi => by
      obtain rfl : i = 0 := by omega_arith
      rw [hk.stackArg0 hp, hk'.stackArg0 hp', hq.a0])

/-- A piece of code the taint analysis accepts, between states that keep `KR`. -/
theorem piece {rs : List Reg} {c : Prog isa} (P G : State → State → Prop)
    (hk : ∀ {t₀ s}, P t₀ s → KR F t₀ s)
    (hag : ∀ s s', P s₀ s → P s₀' s' → ∀ r ∈ rs, s.gpr r = s'.gpr r)
    (hc : Ck rs c) (hw : ∀ {t₀}, Pre F t₀ → ∀ s, P t₀ s → WP isa c s (G t₀)) :
    RelCT isa (fun s s' => P s₀ s ∧ P s₀' s') c fun s s' => G s₀ s ∧ G s₀' s' :=
  rel_agree _ (fun s s' h h' => agree hp hp' hq (hk h) (hk h') (hag s s' h h')) hc (hw hp) (hw hp')

omit hp hp' in
theorem ag_kr {s s' : State} (h : KR F s₀ s) (h' : KR F s₀' s') : ∀ r ∈ krRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r5, h'.r5, hq.innEq]
  · rw [h.r6, h'.r6, hq.outEq]
  · rw [h.r11, h'.r11, hq.scrEq]

omit hp hp' in
theorem ag_kk {s s' : State} (h : KK F s₀ s) (h' : KK F s₀' s') : ∀ r ∈ kkRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ag_kr hq h.kr h'.kr _ (by simp)
  · exact ag_kr hq h.kr h'.kr _ (by simp)
  · rw [h.r8, h'.r8, hq.keyEq]
  · rw [h.r9, h'.r9, hq.r3]
  · exact ag_kr hq h.kr h'.kr _ (by simp)

omit hp hp' in
theorem ag_hk {s s' : State} (h : KK F s₀ s) (h' : KK F s₀' s') (h4 : s.gpr .r4 = dO s₀ F.stWO)
    (h4' : s'.gpr .r4 = dO s₀' F.stWO) : ∀ r ∈ hkRegs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [hkRegs, List.mem_cons] at hr
  rcases hr with rfl | hr
  · rw [h4, h4', hq.dOEq]
  · exact ag_kk hq h h' _ (by simpa using hr)

end

/-! ## The key -/

/-- The key is longer than a block. -/
abbrev Long (F : Fns) (t₀ : State) : Prop := F.H.B + 1 ≤ kln t₀

/-- The pieces of hashing the key. -/
abbrev Hk1 (F : Fns) (t₀ s : State) : Prop := (KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk2a (F : Fns) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO ∧ s.gpr .r0 = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk2 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ hH.SH.Repr s.mem (A t₀ F.stWO) [] ∧ s.gpr .r4 = dO t₀ F.stWO) ∧ Long F t₀
abbrev Hk3 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO ∧ s.gpr .r0 = dO t₀ F.stWO ∧ s.gpr .r1 = key t₀ ∧
    s.gpr .r7 = t₀.gpr .r3 ∧ s.gpr .r10 = scr t₀ ∧ count s = BitVec.ofNat 64 0 ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) []) ∧ Long F t₀
abbrev Hk4 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ s.gpr .r4 = dO t₀ F.stWO ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem (State.addr (key t₀)) (kln t₀))) ∧ Long F t₀
abbrev Hk5 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KK F t₀ s ∧ s.gpr .r0 = dO t₀ F.stWO ∧ s.gpr .r1 = dO t₀ F.hkO ∧ s.gpr .r12 = scr t₀ ∧
    count s = BitVec.ofNat 64 (kln t₀) ∧
    hH.SH.Repr s.mem (A t₀ F.stWO) (bytesAt t₀.mem (State.addr (key t₀)) (kln t₀))) ∧ Long F t₀
abbrev Hk6 (hH : HashOK F.H) (t₀ s : State) : Prop :=
  (KR F t₀ s ∧ bytesAt s.mem (A t₀ F.hkO) F.H.D = hH.SH.H.hash (bytesAt t₀.mem (State.addr (key t₀)) (kln t₀))) ∧
    Long F t₀

/-- After `cmp`. -/
abbrev Cmp (F : Fns) (t₀ s : State) : Prop := KK F t₀ s ∧ s.z = decide (kln t₀ < F.H.B + 1)

section
variable {hF : FnsOK F} {s₀ s₀' : State} (hp : Pre F s₀) (hp' : Pre F s₀') (hq : PubEq s₀ s₀')
  (hc : AnyChecks F)
include hp hp' hq hc

theorem hashKey_rel :
    RelCT isa (fun s s' => (KK F s₀ s ∧ Long F s₀) ∧ (KK F s₀' s' ∧ Long F s₀')) F.hashKey
      fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' := by
  have hz := hF.sizes
  have hl := layout (F := F); have he := end_le hz; have := hz.D; have := hz.S; have := hz.reach
  unfold Fns.hashKey Hash.callInit
  have r1 := piece hp hp' hq (fun t₀ s => KK F t₀ s ∧ Long F t₀) (Hk1 F) (fun h => h.1.kr)
    (fun s s' h h' => ag_kk hq h.1 h'.1) hc.hk1
    (fun _ s h => WP.mono (hk1_ok h.1 hz.stWO_lt16) fun t ⟨k, d, _⟩ => ⟨⟨k, d⟩, h.2⟩)
  have r2a := piece hp hp' hq (Hk1 F) (Hk2a F) (fun h => h.1.1.kr)
    (fun s s' h h' => ag_hk hq h.1.1 h'.1.1 h.1.2 h'.1.2) hc.hk2
    (fun _ s h => WP.mono (hk2a_ok h.1.1 h.1.2) fun t ⟨k, d, a⟩ => ⟨⟨k, d, a⟩, h.2⟩)
  have cw : ∀ {t₀ : State}, Pre F t₀ → ∀ {s : State}, KR F t₀ s →
      Covers [⟨State.addr (dO t₀ F.stWO), F.H.S⟩] s.wr := fun {t₀} hp₀ {s} k => by
    rw [dO_addr hp₀ hz.stWO_lt]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp₀ k hz.stWO_S
  have r2 : RelCT isa (fun s s' => Hk2a F s₀ s ∧ Hk2a F s₀' s') (.call F.H.initN F.H.initC)
      fun s s' => Hk2 hF.hH s₀ s ∧ Hk2 hF.hH s₀' s' :=
    rel_wp (init_rel hF.hH (st := dO s₀ F.stWO) fun s s' ⟨⟨⟨k, _, a⟩, _⟩, ⟨⟨k', _, a'⟩, _⟩⟩ =>
        ⟨a, by rw [a', hq.dOEq], by rw [dO_toNat hp hz.stWO_lt]; have := hp.nsc; omega_arith, cw hp k.kr,
          by have := cw hp' k'.kr; rw [hq.dOEq] at this; exact this⟩)
      (fun s ⟨⟨k, d, a⟩, l⟩ => WP.mono (hk2b_ok hp hz hF.hH k d a) fun t h => ⟨h, l⟩)
      (fun s ⟨⟨k, d, a⟩, l⟩ => WP.mono (hk2b_ok hp' hz hF.hH k d a) fun t h => ⟨h, l⟩)
  have r3 := piece hp hp' hq (Hk2 hF.hH) (Hk3 hF.hH) (fun h => h.1.1.kr)
    (fun s s' h h' => ag_hk hq h.1.1 h'.1.1 h.1.2.2 h'.1.2.2) hc.hk3
    (fun hp₀ s ⟨⟨k, r, d⟩, l⟩ => WP.mono (hk3_ok k d) fun t ⟨k', d', a₀, a₁, a₇, a₁₀, c, m⟩ =>
      ⟨⟨k', d', a₀, a₁, a₇, a₁₀, c, by rw [m]; exact r⟩, l⟩)
  have r4 : RelCT isa (fun s s' => Hk3 hF.hH s₀ s ∧ Hk3 hF.hH s₀' s')
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16))
      fun s s' => Hk4 hF.hH s₀ s ∧ Hk4 hF.hH s₀' s' :=
    rel_wp (upd_rel hF.hH (sp := s₀.sp)
        fun s s' ⟨⟨⟨k, _, a₀, a₁, a₇, a₁₀, c, _⟩, _⟩, ⟨⟨k', _, a₀', a₁', a₇', a₁₀', c', _⟩, _⟩⟩ =>
        ⟨hk4_args hp hz hF.hH k a₀ a₁ a₇ a₁₀,
          by have := hk4_args hp' hz hF.hH k' a₀' a₁' a₇' a₁₀'; rwa [hq.dOEq, hq.keyEq, hq.scrEq, hq.klnEq] at this,
          by rw [c, c'], k.kr.sp, by rw [k'.kr.sp, hq.sp]⟩)
      (fun s ⟨⟨k, d, a₀, a₁, a₇, a₁₀, c, r⟩, l⟩ => WP.mono (hk4_ok hp hz hF.hH k d a₀ a₁ a₇ a₁₀ c r) fun t h =>
        ⟨h, l⟩)
      (fun s ⟨⟨k, d, a₀, a₁, a₇, a₁₀, c, r⟩, l⟩ => WP.mono (hk4_ok hp' hz hF.hH k d a₀ a₁ a₇ a₁₀ c r) fun t h =>
        ⟨h, l⟩)
  have r5 := piece hp hp' hq (Hk4 hF.hH) (Hk5 hF.hH) (fun h => h.1.1.kr)
    (fun s s' h h' => ag_hk hq h.1.1 h'.1.1 h.1.2.1 h'.1.2.1) hc.hk5
    (fun hp₀ s ⟨⟨k, d, r⟩, l⟩ => WP.mono (hk5_ok k d hz.hkO_lt16) fun t ⟨k', a₀, a₁, a₁₂, c, m⟩ =>
      ⟨⟨k', a₀, a₁, a₁₂, c, by rw [m]; exact r⟩, l⟩)
  have r6 : RelCT isa (fun s s' => Hk5 hF.hH s₀ s ∧ Hk5 hF.hH s₀' s')
      (.frame (.push [.r1, .r12]) (.call F.H.finN F.H.finC) (.pop .r1 8))
      fun s s' => Hk6 hF.hH s₀ s ∧ Hk6 hF.hH s₀' s' :=
    rel_wp (fin_rel hF.hH (sp := s₀.sp) fun s s' ⟨⟨⟨k, a₀, a₁, a₁₂, c, _⟩, _⟩, ⟨⟨k', a₀', a₁', a₁₂', c', _⟩, _⟩⟩ =>
        ⟨hk6_args hp hz hF.hH k a₀ a₁ a₁₂,
          by have := hk6_args hp' hz hF.hH k' a₀' a₁' a₁₂'; rwa [hq.dOEq, hq.dOEq, hq.scrEq] at this,
          by rw [c, c', hq.klnEq], k.kr.sp, by rw [k'.kr.sp, hq.sp]⟩)
      (fun s ⟨⟨k, a₀, a₁, a₁₂, c, r⟩, l⟩ => WP.mono (hk6_ok hp hz hF.hH k a₀ a₁ a₁₂ c r) fun t h => ⟨h, l⟩)
      (fun s ⟨⟨k, a₀, a₁, a₁₂, c, r⟩, l⟩ => WP.mono (hk6_ok hp' hz hF.hH k a₀ a₁ a₁₂ c r) fun t h => ⟨h, l⟩)
  have r7 := piece hp hp' hq (Hk6 hF.hH) (Keyed hF) (fun h => h.1.1) (fun s s' h h' => ag_kr hq h.1.1 h'.1.1) hc.hk7
    (fun {t₀} hp₀ s ⟨⟨k, b⟩, l⟩ => WP.mono (hk7_ok k hz.hkO_lt16 hz.D_lt16) fun t ⟨k', d, c, m⟩ => by
      have hlt : ¬ kln t₀ < F.H.B + 1 := by omega
      have ekp : kp F t₀ = dO t₀ F.hkO := by simp only [kp, hlt, ↓reduceIte]
      have ekl : kl F t₀ = F.H.D := by simp only [kl, hlt, ↓reduceIte]
      refine ⟨k', by rw [ekp]; exact d, by rw [ekl]; exact c, ?_⟩
      rw [ekp, ekl, dO_addr hp₀ hz.hkO_lt, m, b, blockKey_hash hz hF.hH (by rw [bytesAt_length]; omega_arith)
        (hash_len hF.hH b)])
  exact (r1.seq ((r2a.seq r2).seq (r3.seq (r4.seq (r5.seq (r6.seq r7)))))).mono (fun _ _ h => h) fun _ _ h => h

theorem key_rel :
    RelCT isa (fun s s' => KK F s₀ s ∧ KK F s₀' s') F.key fun s s' => Keyed hF s₀ s ∧ Keyed hF s₀' s' := by
  have hz := hF.sizes
  unfold Fns.key
  have rc := piece hp hp' hq (fun t₀ s => KK F t₀ s) (Cmp F) (fun h => h.kr) (fun s s' h h' => ag_kk hq h h') hc.cmp
    (fun hp₀ s k => WP.mono (cmp_ok hz k) fun t ⟨k', z, _⟩ => ⟨k', z⟩)
  have ev : ∀ {t₀ t : State}, Cmp F t₀ t → isa.eval .eq t = some (decide (kln t₀ < F.H.B + 1)) := by
    intro t₀ t h
    show eval .eq t = _
    rw [eval_eq, h.2]
  refine rc.seq (RelCT.ite (fun s s' h => by rw [ev h.1, ev h.2, hq.klnEq]) ?_ ?_)
  · refine (piece hp hp' hq (fun t₀ s => Cmp F t₀ s ∧ kln t₀ < F.H.B + 1) (Keyed hF) (fun h => h.1.1.kr)
      (fun s s' h h' => ag_kk hq h.1.1 h'.1.1) hc.short (fun {t₀} hp₀ s ⟨⟨k, _⟩, hlt⟩ => ?_)).mono
      (fun s s' h => ?_) fun _ _ h => h
    · have ekp : kp F t₀ = key t₀ := by simp only [kp, hlt, ↓reduceIte]
      have ekl : kl F t₀ = kln t₀ := by simp only [kl, hlt, ↓reduceIte]
      refine VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₂ u₂ =>
        VG.Proof.MdStream.Arm.wp_mov (VG.Proof.MdStream.Arm.op2_reg _ _) fun s₃ u₃ => WP.block_nil
          ⟨(k.kr.upd (by decide) u₂).upd (by decide) u₃, ?_, ?_, ?_⟩
      · rw [u₃.other _ (by decide), u₂.gpr, k.r8, ekp]
      · rw [u₃.gpr, u₂.other _ (by decide), k.r9, ekl, ofNat_toNat32]
      · rw [u₃.mem, u₂.mem, ekp, ekl, k.kr.keyBytes hp₀]
    · have := of_decide_eq_true ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
      exact ⟨⟨h.1.1, this⟩, h.1.2, by rw [hq.klnEq]; exact this⟩
  · refine (hashKey_rel hp hp' hq hc).mono (fun s s' h => ?_) fun _ _ h => h
    have := of_decide_eq_false ((ev h.1.1).symm.trans h.2 |> Option.some.inj)
    exact ⟨⟨h.1.1.1, by omega_arith⟩, h.1.2.1, by show F.H.B + 1 ≤ kln s₀'; rw [hq.klnEq]; omega_arith⟩

/-- After `anyArgs`. -/
abbrev Ag (hF : FnsOK F) (t₀ t : State) : Prop :=
  Keyed hF t₀ t ∧ t.gpr .r0 = inn t₀ ∧ t.gpr .r1 = out t₀ ∧ t.gpr .r12 = scr t₀

/-- After HMAC's `init`. -/
abbrev Done (hF : FnsOK F) (t₀ t : State) : Prop :=
  KR F t₀ t ∧ hF.hH.SH.Repr t.mem (State.addr (inn t₀)) (xorPad (K0 hF t₀) ipad) ∧
    hF.hH.SH.Repr t.mem (State.addr (out t₀)) (xorPad (K0 hF t₀) opad)

include hF in
/-- `initAny` in two runs with the same public arguments. -/
theorem ct : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') F.hmacInitAny fun _ _ => True := by
  have hz := hF.sizes
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := KK F s₀) (G' := KK F s₀')
    (argTaint inRegs 4) (fun s s' e e' => by
        subst e e'
        refine agree_argTaint (fun r hr => ?_) hq.sp (args_out hp rfl rfl) (args_out hp' rfl rfl)
          (argMem_of (j := 1) hq.sp hp.spf fun i hi => by obtain rfl : i = 0 := by omega_arith
                                                          exact hq.a0)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.r0
        · exact hq.r1
        · exact hq.r2
        · exact hq.r3) hc.pro
    (fun _ e => by rw [e]; exact prologue_ok hp hz) (fun _ e => by rw [e]; exact prologue_ok hp' hz)
  have ra := piece hp hp' hq (Keyed hF) (Ag hF) (fun h => h.kr) (fun s s' h h' => ag_kr hq h.kr h'.kr) hc.args
    (fun _ s h => args_ok hF h)
  have rc : RelCT isa (fun s s' => Ag hF s₀ s ∧ Ag hF s₀' s')
      (.frame (.push [.r12, .lr]) (.call F.hiN F.hiC) (.pop .r12 8))
      fun s s' => Done hF s₀ s ∧ Done hF s₀' s' :=
    rel_wp (hi_rel hF.hi (sp := s₀.sp) fun s s' ⟨⟨h, a₀, a₁, a₁₂⟩, ⟨h', a₀', a₁', a₁₂'⟩⟩ =>
        ⟨call_args hp hz hF h a₀ a₁ a₁₂,
          by have := call_args hp' hz hF h' a₀' a₁' a₁₂'
             rwa [hq.innEq, hq.outEq, hq.kpEq, hq.scrEq, hq.klEq] at this,
          h.kr.sp, by rw [h'.kr.sp, hq.sp]⟩)
      (fun s ⟨h, a₀, a₁, a₁₂⟩ => call_ok hp hz hF h a₀ a₁ a₁₂)
      (fun s ⟨h, a₀, a₁, a₁₂⟩ => call_ok hp' hz hF h a₀ a₁ a₁₂)
  obtain ⟨_, hr⟩ := hc.restore
  have restore : RelCT isa (fun s s' => Done hF s₀ s ∧ Done hF s₀' s') (.block F.L.restore)
      fun _ _ => True :=
    RelCT.taint (A := taint) (argTaint krRegs 4)
      (fun s s' h => agree hp hp' hq h.1.1 h.2.1 (ag_kr hq h.1.1 h.2.1)) hr
  unfold Fns.hmacInitAny
  exact pro.seq ((key_rel hp hp' hq hc).seq (ra.seq (rc.seq restore)))

end

/-- The public arguments of the contract. -/
theorem pub_of {S : Spec.Hmac.StreamingHash} {W : Nat} {s₁ s₂ : State}
    (h : (anyScratchContract S W).pub s₁ s₂) : PubEq s₁ s₂ := by
  sig_pub [anyScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- `initAny` is verified against `anyScratchContract`, given the taint
checks and a state satisfying it. -/
theorem verified (hF : FnsOK F) (hc : AnyChecks F) {S : Spec.Hmac.StreamingHash} {W : Nat} (hS : hF.hH.SH = S)
    (hW : F.W + F.H.S = W) (hsat : ∃ s, (anyScratchContract S W).pre s) :
    Verified Arm.target F.hmacInitAny (anyScratchContract S W) := by
  subst hS hW
  exact ⟨fun s hs => correct (pre_of hF hs) hF.sizes hF,
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ =>
      (ct (hF := hF) (pre_of hF h₁) (pre_of hF h₂) (pub_of hpub) hc _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, hsat⟩

/-! ## In a frame of its own, wiped -/

/-- The bytes of `init`'s frame: the saved registers and the working space,
rounded up to a multiple of 32, which an ARM immediate encodes. -/
def anyFrame (I : Spec.Hmac.Instance) : Nat := (8 + 8 * I.initAnyKeyScratch + 31) / 32 * 32

/-- `initAny` in a frame holding its working space, which it wipes before
returning: verified against `initAnyKeyContract`, from the locality of its
postcondition (`Proof/Hmac/AnyKey.lean`). -/
theorem anyFramed {I : Spec.Hmac.Instance} {c : Prog isa}
    (h : Verified Arm.target c (anyScratchContract I.S I.initAnyKeyScratch))
    (hR : Hmac.ReprLocal I.S) (hS : I.S.stateBytes < 2 ^ 64)
    (hsat : ∃ s, (I.initAnyKeyContract Arm.abi (24 + anyFrame I)).pre s)
    (hb : Fits 0 (anyFrame I) .u64 I.initAnyKeyScratch := by decide) :
    Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped (anyFrame I) 0 (2 * I.initAnyKeyScratch) c)
      (I.initAnyKeyContract Arm.abi (24 + anyFrame I)) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.initAnyKeyScratch) (post := Spec.Hmac.initPost I.S Arm.abi.ptrBits) (wa := true) (stack := 24)
    (m := 0) (words := 2 * I.initAnyKeyScratch) h rfl rfl rfl hb
    (by change 4 * (2 * I.initAnyKeyScratch) ≤ I.initAnyKeyScratch * 8; omega_arith)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Hmac.initPost_local I.S _) (Hmac.initPostOut_local I.S _ hR hS) hsat rfl

end VG.Proof.Pbkdf2.Whole.Arm.Any

end

end

/-! ### `Pbkdf2.Md.Arm.Frame`, which only this module used -/

section

/-!
# HMAC's `init` and `finalize` on ARMv7, with their working space on the stack

`init` and `finalize` run their `_scratch` forms (`Instances.lean`,
`Sha256.lean`, `Sha224.lean`) in a frame that allocates the working space and
copies the arguments passed on the stack (`Verified.stackScratch`):
`initFramed` and `finFramed`, for any instance, from the locality of HMAC's
pre- and postconditions (`Proof/Hmac/Scratch.lean`). `init` has no arguments
on the stack, `finalize` one (`out`). Both frames are `frame I` bytes: the
working space, the copied arguments and the saved registers, rounded up to a
multiple of 32 bytes, which an ARM immediate encodes. `initFrameSat` and
`finFrameSat` satisfy the preconditions of the contracts without the
working space.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.Arm

open VG.Arm

/-- The bytes of `init`'s and `finalize`'s frames: `finalize`'s copy of its
one stack argument, the saved registers and the working space, rounded up to
a multiple of 32. -/
def frame (I : Spec.Hmac.Instance) : Nat := (4 + 8 + 8 * I.scratch + 31) / 32 * 32

theorem initFramed {I : Spec.Hmac.Instance} {c : Prog isa} {bytes : Nat}
    (h : Verified Arm.target c (Proof.Hmac.Instance.initScratchContract I Arm.abi 16))
    (hsat : ∃ s, (I.initContract Arm.abi (16 + bytes)).pre s)
    (hb : Fits 0 bytes .u64 I.scratch := by decide) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch bytes 0 c)
      (I.initContract Arm.abi (16 + bytes)) :=
  Arm.Verified.stackScratch (sig := Spec.Hmac.initSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (pre := Spec.Hmac.initPre I.S Arm.abi.ptrBits)
    (post := Spec.Hmac.initPost I.S Arm.abi.ptrBits) (wa := true) (stack := 16) (m := 0) h
    rfl rfl rfl hb
    (Hmac.initPre_local I.S _) (Hmac.initPost_local I.S _) hsat

theorem finFramed {I : Spec.Hmac.Instance} {c : Prog isa} {bytes : Nat}
    (h : Verified Arm.target c (Proof.Hmac.Instance.finalizeScratchContract I Arm.abi 16))
    (hR : Hmac.ReprLocal I.S)
    (hsat : ∃ s, (I.finalizeContract Arm.abi (16 + bytes)).pre s)
    (hb : Fits 1 bytes .u64 I.scratch := by decide) (hS : I.S.stateBytes < 2 ^ 64 := by decide) :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch bytes 1 c)
      (I.finalizeContract Arm.abi (16 + bytes)) :=
  Arm.Verified.stackScratch (sig := Spec.Hmac.finalizeSig I.S) (nm := "scratch") (e := .u64)
    (n := I.scratch) (post := Spec.Hmac.finalizePost I.S Arm.abi.ptrBits) (wa := true)
    (stack := 16) (m := 1) h
    rfl rfl rfl hb
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Hmac.finalizePost_local I.S _ hR hS) hsat

/-- A state satisfying `init`'s precondition without the working space, with
states of `S` bytes (and a one-byte key). -/
def initFrameSat (S : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 1
    | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x3000, 1⟩]
  wr := [⟨0x1000, S⟩, ⟨0x2000, S⟩]

/-- A state satisfying `finalize`'s precondition without the working space,
with states of `S` bytes and a digest of `D` bytes; `out`, at `0x3000`, is
the stack argument. -/
def finFrameSat (S D : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000
    | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x30 else 0
  rd := [⟨0x2000, S⟩, ⟨0x6000, 4⟩]
  wr := [⟨0x1000, S⟩, ⟨0x3000, D⟩]

theorem md5_initFrameSat :
    ∃ s, (Spec.Hmac.md5I.initContract Arm.abi (16 + frame Spec.Hmac.md5I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 80

theorem md5_finFrameSat :
    ∃ s, (Spec.Hmac.md5I.finalizeContract Arm.abi (16 + frame Spec.Hmac.md5I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 80 16

theorem sha1_initFrameSat :
    ∃ s, (Spec.Hmac.sha1I.initContract Arm.abi (16 + frame Spec.Hmac.sha1I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 84

theorem sha1_finFrameSat :
    ∃ s, (Spec.Hmac.sha1I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha1I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 84 20

theorem sha224_initFrameSat :
    ∃ s, (Spec.Hmac.sha224I.initContract Arm.abi (16 + frame Spec.Hmac.sha224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 96

theorem sha224_finFrameSat :
    ∃ s, (Spec.Hmac.sha224I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 96 28

theorem sha256_initFrameSat :
    ∃ s, (Spec.Hmac.sha256I.initContract Arm.abi (16 + frame Spec.Hmac.sha256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 96

theorem sha256_finFrameSat :
    ∃ s, (Spec.Hmac.sha256I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 96 32

theorem sha384_initFrameSat :
    ∃ s, (Spec.Hmac.sha384I.initContract Arm.abi (16 + frame Spec.Hmac.sha384I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 192

theorem sha384_finFrameSat :
    ∃ s, (Spec.Hmac.sha384I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha384I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 192 48

theorem sha512_initFrameSat :
    ∃ s, (Spec.Hmac.sha512I.initContract Arm.abi (16 + frame Spec.Hmac.sha512I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 192

theorem sha512_finFrameSat :
    ∃ s, (Spec.Hmac.sha512I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha512I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 192 64

theorem sha512_224_initFrameSat :
    ∃ s, (Spec.Hmac.sha512_224I.initContract Arm.abi (16 + frame Spec.Hmac.sha512_224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 192

theorem sha512_224_finFrameSat :
    ∃ s, (Spec.Hmac.sha512_224I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha512_224I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 192 28

theorem sha512_256_initFrameSat :
    ∃ s, (Spec.Hmac.sha512_256I.initContract Arm.abi (16 + frame Spec.Hmac.sha512_256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig,
      Spec.Hmac.initPre, Spec.Hmac.initPost, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using initFrameSat 192

theorem sha512_256_finFrameSat :
    ∃ s, (Spec.Hmac.sha512_256I.finalizeContract Arm.abi (16 + frame Spec.Hmac.sha512_256I)).pre s := by
  implies_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig,
      Spec.Hmac.finalizePost, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, frame,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finFrameSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using finFrameSat 192 32

end VG.Proof.Pbkdf2.Md.Arm

end

end


/-!
# HMAC's `init` for a key of any length on 32-bit ARM, choosing on entry

`initEntry B short long` sets `Z` to whether `key_len` (`r3`) is at most `B`
(through `r12`, as `pbkdf2`'s `cmpPw`) and runs `long`, verified against
`VG.Spec.Hmac.Instance.initAnyKeyContract`, for a key longer than a block,
and `short`, verified against `initContract` (a key of at most a block),
otherwise (`Verified.entryBranch`). The comparison writes only `r12` and the
flags, which no contract reads, and leaks nothing; the branch depends only
on `key_len`, which is public.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm

/-- The comparison on entry. -/
abbrev entryB (B : Nat) : List Instr :=
  [.subs .r12 .r3 (.imm (BitVec.ofNat 32 (B + 1))), .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0),
    .cmp .r12 (.imm 0)]

theorem entry_run {B : Nat} (hB : B + 1 < 2 ^ 32) (hk : encodable (BitVec.ofNat 32 (B + 1)) = true) (s : State) :
    ∃ u, execBlock isa (entryB B) s = some (u, []) ∧ (∀ r, r ≠ .r12 → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ eval .ne u = some (decide (B + 1 ≤ (s.gpr .r3).toNat)) := by
  obtain ⟨t, u, e, g, m, rd, wr, sp, z⟩ := wp_lt (s := s) (is := []) (x := .r3) (Q := fun u =>
      (∀ r, r ≠ .r12 → u.gpr r = s.gpr r) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
        u.z = decide ((s.gpr .r3).toNat < (BitVec.ofNat 32 (B + 1)).toNat)) hk
    fun s' g m rd wr sp z => WP.block_nil ⟨g, m, rd, wr, sp, z⟩
  have x := Exec.block_eq (T := Arm.target) e
  have ht := execBlock_trace_nil (M := isa) (b := entryB B) (fun i hi s => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl) x
  subst ht
  refine ⟨u, x, g, m, rd, wr, sp, ?_⟩
  show some (!u.z) = _
  rw [z, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hB]
  simp only [← decide_not, Nat.not_lt]

theorem initEntry_verified {I : Spec.Hmac.Instance} {short long : Prog isa} {n₁ n₂ : Nat}
    (hS : Verified Arm.target short (I.initContract Arm.abi n₁))
    (hL : Verified Arm.target long (I.initAnyKeyContract Arm.abi n₂))
    (h₁ : 0 < n₁) (hn : n₁ ≤ n₂) (hB : I.S.H.blockSize + 1 < 2 ^ 32)
    (hk : encodable (BitVec.ofNat 32 (I.S.H.blockSize + 1)) = true)
    (hsat : ∃ s, (I.initAnyKeyContract Arm.abi n₂).pre s) :
    Verified Arm.target (Impl.Pbkdf2.Whole.Arm.initEntry I.S.H.blockSize short long)
      (I.initAnyKeyContract Arm.abi n₂) := by
  have hp : ∀ r ∈ preserved, r ≠ .r12 := by decide
  refine Verified.entryBranch (p := fun s => decide (I.S.H.blockSize + 1 ≤ (s.gpr .r3).toNat))
    (fun _ => []) hL hS (fun s hs => ?_) ?_ hsat
  · obtain ⟨u, e, g, hm, hrd, hwr, hsp, ev⟩ := entry_run hB hk s
    have g0 := g .r0 (by decide)
    have g1 := g .r1 (by decide)
    have g2 := g .r2 (by decide)
    have g3 := g .r3 (by decide)
    have abi : ∀ s', Arm.target.abiPreserved u s' → Arm.target.abiPreserved s s' := fun s' a =>
      ⟨fun x hx => by rw [a.1 x hx, g x (hp x hx)], by rw [a.2, hsp]⟩
    refine ⟨u, e, ev, fun _ => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩, fun hp => ⟨?_, fun s' a q => ⟨abi s' a, ?_⟩⟩⟩
    · sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hs ⊢
      rw [g0, g1, g2, g3, hsp, hrd, hwr]; exact hs
    · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at q ⊢
      rw [g0, g1, g2, g3, hm] at q; exact q
    · have hk : (s.gpr .r3).toNat ≤ I.S.H.blockSize := by have := of_decide_eq_false hp; omega_using [this]
      sig_pre [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hs
      sig_pre [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      rw [g0, g1, g2, g3, hsp, hrd, hwr]
      obtain ⟨m₁, rfl⟩ : ∃ m, n₁ = m + 1 := ⟨n₁ - 1, by omega_using [h₁]⟩
      obtain ⟨m₂, rfl⟩ : ∃ m, n₂ = m + 1 := ⟨n₂ - 1, by omega_using [hn]⟩
      simp only [Sig.conj, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil] at hs ⊢
      obtain ⟨⟨h0, h0'⟩, h1, h2, h3, h4, h5, ⟨c1, c2, c3⟩, n1, n2, n3⟩ := hs
      have sb := Offset.sub_below (State.addr s.sp) (a := m₁ + 1) (n := m₁ + 1) (b := m₂ + 1) (m := m₂ + 1)
        (by omega_using [hn]) (by omega_using [hn])
      exact ⟨⟨by omega_using [hn, h0], h0'⟩, h1, h2, h3, h4, h5, ⟨c1.sub_left sb, c2.sub_left sb, c3.sub_left sb⟩, n1, n2, n3, hk⟩
    · sig_post [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_post [Spec.Hmac.Instance.initContract, Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.initPre,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at q
      rw [g0, g1, g2, g3, hm] at q; exact q
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨u₀, e₀, g, -, -, -, hsp, -⟩ := entry_run hB hk s
    obtain ⟨u₀', e₀', g', -, -, -, hsp', -⟩ := entry_run hB hk s'
    rw [e₀] at e; rw [e₀'] at e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have hq' := hq
    sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
      Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq'
    obtain ⟨q0, q1, q2, q3, q4⟩ := hq'
    have pu : (I.initAnyKeyContract Arm.abi n₂).pub u₀ u₀' := by
      sig_pub [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig,
        Spec.Hmac.initPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      rw [hsp, hsp', g .r0 (by decide), g' .r0 (by decide), g .r1 (by decide), g' .r1 (by decide),
        g .r2 (by decide), g' .r2 (by decide), g .r3 (by decide), g' .r3 (by decide)]
      exact ⟨q0, q1, q2, q3, q4⟩
    exact ⟨rfl, by rw [q4], fun _ => pu, fun _ => pu⟩

/-- HMAC's `init` for a key of any length, `vg_hmac_<hash>_init`, of instance
`I`: for a key of at most a block, `init_scratch` (`hmacInit`) in a frame
holding its working space; for a longer key (cold), `F.hmacInitAny`, in a
frame holding its larger working space, which it wipes. -/
def initCode (I : Spec.Hmac.Instance) (hmacInit : Prog isa) (F : Impl.Pbkdf2.Whole.Arm.Fns) : Prog isa :=
  Impl.Pbkdf2.Whole.Arm.initEntry I.S.H.blockSize
    (Impl.StackScratch.Arm.withStackScratch (Md.Arm.frame I) 0 hmacInit)
    (Impl.StackScratch.Arm.withStackScratchWiped (Any.anyFrame I) 0 (2 * I.initAnyKeyScratch) F.hmacInitAny)

theorem initCode_verified {I : Spec.Hmac.Instance} {c : Prog isa} {F : Impl.Pbkdf2.Whole.Arm.Fns}
    (hS : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch (Md.Arm.frame I) 0 c)
      (I.initContract Arm.abi (16 + Md.Arm.frame I)))
    (hL : Verified Arm.target
      (Impl.StackScratch.Arm.withStackScratchWiped (Any.anyFrame I) 0 (2 * I.initAnyKeyScratch) F.hmacInitAny)
      (I.initAnyKeyContract Arm.abi (24 + Any.anyFrame I)))
    (hn : 16 + Md.Arm.frame I ≤ 24 + Any.anyFrame I) (hB : I.S.H.blockSize + 1 < 2 ^ 32)
    (hk : encodable (BitVec.ofNat 32 (I.S.H.blockSize + 1)) = true)
    (hsat : ∃ s, (I.initAnyKeyContract Arm.abi (24 + Any.anyFrame I)).pre s) :
    Verified Arm.target (initCode I c F) (I.initAnyKeyContract Arm.abi (24 + Any.anyFrame I)) :=
  initEntry_verified hS hL (by omega_using []) hn hB hk hsat

end VG.Proof.Pbkdf2.Whole.Arm
