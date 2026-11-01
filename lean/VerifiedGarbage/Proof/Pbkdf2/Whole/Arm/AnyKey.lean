module

public import VerifiedGarbage.Impl.Pbkdf2.Md.AnyKey.Arm
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Common
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Loop
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

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
