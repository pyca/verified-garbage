module

import VerifiedGarbage.Proof.Argon2.Initial
public import VerifiedGarbage.Proof.Argon2.HPrime
public import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.Rc2.Select
public import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Blake2.Arm.Blake2b
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Proof.Framework.OmegaLit
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rc2.Memory32
import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Isa
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import VerifiedGarbage.Spec.Blake2
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.TCB.Mem
public import Init.Core
public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.Impl.Argon2.Arm.HPrime
public import VerifiedGarbage.Proof.Blake2.Arm.Stream.Update
public import VerifiedGarbage.Proof.Argon2.Arm.Push
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Argon2.Contract

/-! ### `Argon2.Arm.HPrime.Hash`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.HPrime.Calls`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.HPrime.Contract`, which this module and modules that import it used -/

section

/-!
# Argon2 H′ on ARMv7: the contract of the proof

`hPrimeArm`: `vg_argon2_hprime(input = r0, input_len = r1, out = r2,
out_len = r3, scratch = [sp])` with its stack argument only read. H′ uses the 32 bytes of stack below the stack pointer: a call of
`vg_blake2b_update` pushes four words, and `update` itself uses 16 bytes.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm
open VG.Proof.Argon2.Arm (stkR)
open VG.Spec.Blake2 (bytesAt)

def hPrimeArm : Contract Arm.isa where
  pre s :=
    let input : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let out : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 16384⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    let stack : Region := stkR s.sp 32
    s.rd = [input, args] ∧ s.wr = [out, scratch] ∧
    input.Disjoint scratch ∧ out.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    stack.Disjoint input ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + 16384 ≤ 2 ^ 32 ∧ 32 ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
    1 ≤ (s.gpr .r3).toNat
  post s s' := bytesAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
    Spec.Argon2.hPrime (s.gpr .r3).toNat (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

section
variable (s₀ : State)

abbrev inp : BitVec 32 := s₀.gpr .r0
abbrev inl : Nat := (s₀.gpr .r1).toNat
abbrev op : BitVec 32 := s₀.gpr .r2
abbrev ol : Nat := (s₀.gpr .r3).toNat
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev sp₀ : BitVec 32 := s₀.sp
/-- `scratch`, as an address. -/
abbrev P : Addr := State.addr (scr s₀)
abbrev inR : Region := ⟨State.addr (inp s₀), inl s₀⟩
abbrev outR : Region := ⟨State.addr (op s₀), ol s₀⟩
abbrev scrR : Region := ⟨P s₀, 16384⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
abbrev stk : Region := stkR (sp₀ s₀) 32

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [inR s₀, argR s₀]
  wr : s₀.wr = [outR s₀, scrR s₀]
  in_scr : (inR s₀).Disjoint (scrR s₀)
  out_scr : (outR s₀).Disjoint (scrR s₀)
  arg_out : (argR s₀).Disjoint (outR s₀)
  arg_scr : (argR s₀).Disjoint (scrR s₀)
  stk_in : (stk s₀).Disjoint (inR s₀)
  stk_out : (stk s₀).Disjoint (outR s₀)
  stk_scr : (stk s₀).Disjoint (scrR s₀)
  in_fits : (inp s₀).toNat + inl s₀ ≤ 2 ^ 32
  out_fits : (op s₀).toNat + ol s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 16384 ≤ 2 ^ 32
  sp_lo : 32 ≤ (sp₀ s₀).toNat
  sp_hi : (sp₀ s₀).toNat + 4 ≤ 2 ^ 32
  ol_pos : 1 ≤ ol s₀

theorem pre_of (s₀ : State) (h : hPrimeArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- `[scratch + d]`, as the code addresses it. -/
theorem scr_addr {s₀ : State} (hp : Pre s₀) {d : Nat} (hd : d < 16384) :
    State.addr (scr s₀ + BitVec.ofNat 32 d) = P s₀ + BitVec.ofNat 64 d := addr_add (by have := hp.scr_fits; omega_using [hd, this])

end VG.Proof.Argon2.Arm.HPrime

end

end

/-!
# Argon2 H′ on ARMv7: the calls of the BLAKE2b functions

`init_ok`, `update_ok`, `finalize_ok`: H′'s macros (`Impl.Argon2.Arm.HPrime`)
call the ARMv7 BLAKE2b streaming functions with the state at `scratch` (in
`r4`, at `B`), their scratch at `scratch + 192`, and the stack below the
stack pointer (`SP`). Each is stated for any `B` and `SP`, so that the
derivation can use them too: they write only the state, their scratch, the
digest (`finalize`) and the 32 bytes below `SP`, and keep `r4`–`r11`.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Arm.FrameStack
open VG.Impl.Argon2.Arm.HPrime (init update finalize initCode updateCode finalizeCode initName updateName
  finalizeName)
open VG.Proof.Blake2 (initArm updateArm finalizeArm countArm)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_reg op2_imm)

/-! ## The callees -/

theorem init_correct : ∀ s, (initArm b).pre s →
    ∃ t s', Exec isa initCode s t s' ∧ abiPreserved s s' ∧ (initArm b).post s s' :=
  (Proof.Blake2.Arm.Stream.init_verified Proof.Blake2.Arm.Stream.okB Proof.Blake2.Arm.Stream.init_check_b
    (Contract.Implies.refl Proof.Blake2.Arm.Stream.initB_implies.sat_left)).1

theorem init_ct : ConstantTime isa (initArm b).pre (initArm b).pub initCode :=
  (Proof.Blake2.Arm.Stream.init_verified Proof.Blake2.Arm.Stream.okB Proof.Blake2.Arm.Stream.init_check_b
    (Contract.Implies.refl Proof.Blake2.Arm.Stream.initB_implies.sat_left)).2.1

theorem update_v : Verified Arm.target updateCode (updateArm b) :=
  Proof.Blake2.Arm.Stream.update_verified Proof.Blake2.Arm.Stream.okB Proof.Blake2.ArmB.calleeB
    (Contract.Implies.refl Proof.Blake2.Arm.Stream.updateB_implies.sat_left)

theorem finalize_v : Verified Arm.target finalizeCode (finalizeArm b) :=
  Proof.Blake2.Arm.Stream.finalize_verified Proof.Blake2.Arm.Stream.okB Proof.Blake2.ArmB.calleeB
    (Contract.Implies.refl Proof.Blake2.Arm.Stream.finalizeB_implies.sat_left)

theorem update_stack : armStack updateCode = 16 := by lit_decide
theorem finalize_stack : armStack finalizeCode = 16 := by lit_decide

/-! ## Regions -/

/-- What every call needs: `r4` holds `B`, the stack pointer is `SP`, the
state, the callees' scratch and the digest (`scratch[0, 832)`) are writable,
and the 32 bytes below `SP` are outside them. -/
structure Ctx (B SP : BitVec 32) (s : State) : Prop where
  r4 : s.gpr .r4 = B
  sp : s.sp = SP
  fits : B.toNat + 832 ≤ 2 ^ 32
  lo : 32 ≤ SP.toNat
  wr : Covers [⟨State.addr B, 832⟩] s.wr
  stk : (stkR SP 32).Disjoint ⟨State.addr B, 832⟩

theorem Ctx.of_regs {B SP : BitVec 32} {s t : State} (h : Ctx B SP s) (hb : t.gpr .r4 = s.gpr .r4)
    (hs : t.sp = s.sp) (hw : t.wr = s.wr) : Ctx B SP t :=
  ⟨hb.trans h.r4, hs.trans h.sp, h.fits, h.lo, hw ▸ h.wr, h.stk⟩

section
variable {B SP : BitVec 32} {s : State}

theorem Ctx.sub (_h : Ctx B SP s) {d n : Nat} (hd : d + n ≤ 832) :
    Region.Sub ⟨State.addr B + BitVec.ofNat 64 d, n⟩ ⟨State.addr B, 832⟩ :=
  Offset.sub_base _ hd

theorem Ctx.cov (h : Ctx B SP s) {d n : Nat} (hd : d + n ≤ 832) :
    Covers [⟨State.addr B + BitVec.ofNat 64 d, n⟩] s.wr :=
  (Covers.of_sub (rs' := [⟨State.addr B, 832⟩]) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, d, rfl, hd⟩).trans h.wr

theorem Ctx.cov0 (h : Ctx B SP s) {n : Nat} (hn : n ≤ 832) : Covers [⟨State.addr B, n⟩] s.wr :=
  (Covers.of_sub (rs' := [⟨State.addr B, 832⟩]) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp; omega_arith⟩).trans h.wr

theorem Ctx.stk_sub (h : Ctx B SP s) {d n : Nat} (hd : d + n ≤ 832) :
    (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 d, n⟩ :=
  h.stk.sub_right (h.sub hd)

theorem Ctx.stk0 (h : Ctx B SP s) {n : Nat} (hn : n ≤ 832) :
    (stkR SP 32).Disjoint ⟨State.addr B, n⟩ :=
  h.stk.sub_right (Region.sub_prefix hn)

theorem Ctx.addr_add (h : Ctx B SP s) {d : Nat} (hd : d < 832) :
    State.addr (B + BitVec.ofNat 32 d) = State.addr B + BitVec.ofNat 64 d :=
  VG.Arm.addr_add (by have := h.fits; omega_arith)

end

theorem covers_ins {rs a b : List Region} (f : Region) (h : Covers rs (a ++ b)) :
    Covers rs (a ++ f :: b) := fun x n hi => InRegions_append_cons.mpr (.inr (h x n hi))

theorem covers_cons {rs b : List Region} (f : Region) (h : Covers rs b) : Covers rs (f :: b) :=
  fun x n hi => let ⟨r, hr, hc⟩ := h x n hi; ⟨r, List.mem_cons_of_mem _ hr, hc⟩

/-- A region of length 0 is apart from everything. -/
theorem disjoint_nil (a : Addr) (r : Region) : Region.Disjoint ⟨a, 0⟩ r :=
  fun _ h₁ _ => by simp [Region.Contains] at h₁

/-- The callee's state and scratch, and the frames' words, below `SP`. -/
theorem stk_args {SP : BitVec 32} (hlo : 32 ≤ SP.toNat) {k : Nat} (hk : k ≤ 16) :
    Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 16), k⟩ (stkR SP 32) := by
  have := stkR_inner (sp := SP) (a := 16) (k := 0) (b := 32) (by omega_arith) hlo
  intro x hx
  refine stkR_sub (a := 16) (b := 32) (sp := SP) (by omega_arith) hlo x ?_
  obtain e : State.addr (SP - BitVec.ofNat 32 16) = State.addr SP - BitVec.ofNat 64 16 := addr_sub' (by omega_arith)
  simp only [Region.Contains] at hx ⊢
  rw [e] at hx; omega_arith

theorem stk_args8 {SP : BitVec 32} (hlo : 32 ≤ SP.toNat) {k : Nat} (hk : k ≤ 8) :
    Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 8), k⟩ (stkR SP 32) := by
  intro x hx
  refine stkR_sub (a := 8) (b := 32) (sp := SP) (by omega_arith) hlo x ?_
  obtain e : State.addr (SP - BitVec.ofNat 32 8) = State.addr SP - BitVec.ofNat 64 8 := addr_sub' (by omega_arith)
  simp only [Region.Contains] at hx ⊢
  rw [e] at hx; omega_arith

/-- The callee's 16 bytes of stack, below its stack pointer `SP - k`. -/
theorem stk_callee {SP : BitVec 32} (hlo : 32 ≤ SP.toNat) {k : Nat} (hk : k ≤ 16) :
    Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 k) - 16, 16⟩ (stkR SP 32) :=
  stkR_inner (sp := SP) (a := 16) (k := k) (b := 32) (by omega_arith) hlo

/-! ## `init` -/

theorem keyBlock_nil (m : Mem) (p : Addr) : keyBlock 64 (bytesAt m p 0) = [] := rfl

/-- The regions `init` is given. -/
abbrev initRd (B : BitVec 32) : List Region := [⟨State.addr B, 0⟩]
abbrev initWr (B : BitVec 32) : List Region := [⟨State.addr B, 192⟩]

/-- `init`'s precondition, from the arguments in `r0`–`r3`. -/
theorem init_pre {B SP : BitVec 32} {s : State} (h : Ctx B SP s) {n : Nat} (hn : s.gpr .r1 = BitVec.ofNat 32 n)
    (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (h0 : s.gpr .r0 = B) (h2 : s.gpr .r2 = B) (h3 : s.gpr .r3 = 0) :
    (initArm b).pre (s.callEntry.withRegions (initRd B) (initWr B)) ∧
      Covers (initRd B ++ initWr B) (s.rd ++ s.wr) ∧ Covers (initWr B) s.wr := by
  refine ⟨?_, ?_, h.cov0 (by decide)⟩
  · simp only [initArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      Proof.Blake2.Arm.Stream.ce0, Proof.Blake2.Arm.Stream.ce1, Proof.Blake2.Arm.Stream.ce2,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), h0, hn, h2, h3, Proof.Blake2.bufOff, blockBytes]
    have hf := h.fits
    refine ⟨rfl, trivial, disjoint_nil _ _, by omega_arith, by simp; omega_arith, ?_, ?_, by simp⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; exact hn₁
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; exact hn₂
  · refine Covers.append_left (Covers.cons ?_ Covers.nil) ?_
    · intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', hc'⟩ := h.wr a k ⟨_, List.mem_singleton_self _, by
        simp only [Region.Contains] at hc ⊢; omega_arith⟩
      exact ⟨r', List.mem_append_right _ hr', hc'⟩
    · exact ((h.cov0 (n := 192) (by decide)).trans fun a k ⟨r', hr', hc'⟩ =>
        ⟨r', List.mem_append_right _ hr', hc'⟩)

theorem init_ok {B SP : BitVec 32} {s : State} (h : Ctx B SP s) {n : Nat} (hn : s.gpr .r1 = BitVec.ofNat 32 n)
    (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa init s fun t => Repr b (Spec.Blake2.init b n 0) t.mem (State.addr B) [] ∧
      (∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨State.addr B, 192⟩] s.mem t.mem := by
  unfold Impl.Argon2.Arm.HPrime.init
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_)
  obtain o₃ : ∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s.gpr r := fun r h0 h2 h3 => by
    rw [u₃.other _ h3, u₂.other _ h2, u₁.other _ h0]
  obtain r0 : s₃.gpr .r0 = B := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.r4]
  obtain r1 : s₃.gpr .r1 = BitVec.ofNat 32 n := by rw [o₃ _ (by decide) (by decide) (by decide), hn]
  obtain r2 : s₃.gpr .r2 = B := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.r4]
  have r3 : s₃.gpr .r3 = 0 := u₃.gpr
  obtain w₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  obtain c₃ : Ctx B SP s₃ := h.of_regs (o₃ _ (by decide) (by decide) (by decide)) sp₃ w₃
  obtain ⟨pre, cv, cw⟩ := init_pre c₃ r1 hn₁ hn₂ r0 r2 r3
  refine WP.call (k := initArm b) init_correct pre cv cw fun t hrd hwr hsp hf hcs _ hpost => ?_
  simp only [initArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    Proof.Blake2.Arm.Stream.ce0, Proof.Blake2.Arm.Stream.ce1, Proof.Blake2.Arm.Stream.ce2,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), r0, r1, r2, r3] at hpost
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega_arith)] at hpost
  refine ⟨by simpa [keyBlock_nil] using hpost, fun r hr hl => (hcs r hr hl).trans ?_, hrd.trans rd₃, hwr.trans w₃,
    hsp.trans sp₃, by rw [← m₃]; exact hf⟩
  have : r ≠ .r0 ∧ r ≠ .r2 ∧ r ≠ .r3 := by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact o₃ r this.1 this.2.1 this.2.2

/-! ## Streaming states in memory -/

/-- A streaming state is kept while only memory outside its 192 bytes changes. -/
theorem repr_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 192⟩ r) {h0 : HashValue 64} {d : List Byte}
    (h : Repr b h0 m p d) : Repr b h0 m' p d := by
  obtain hb : ∀ i < 192, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
    fun i hi => hf.bytes (R := ⟨p, 192⟩) hd (by simp) hi
  obtain ⟨h1, h2⟩ := h
  obtain hl := Proof.Blake2.bufLen_le (w := 64) (by decide) d.length
  obtain hs := Proof.Blake2.sub_bufLen (w := 64) d
  obtain hs' := Proof.Blake2.bufLen_le_self (w := 64) d.length
  refine ⟨?_, ?_⟩
  · rw [Proof.Blake2.stateAt_congr (fun i hi => hb i (by simp only [Proof.Blake2.bufOff] at hi; omega_arith))]
    exact h1
  · rw [← h2]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have hbb : blockBytes 64 = 128 := rfl
    rw [hbb] at hl hs hi
    exact hb _ (by omega_arith)

/-! ## `update` -/

/-- The registers `update`'s frame pushes: the data, its length, the callees'
scratch, and `lr` for alignment. -/
abbrev upd4 : List Reg := [.r9, .r10, .r12, .lr]

/-- The regions `update` is given. -/
abbrev updRd (D : BitVec 32) (L : Nat) (SP : BitVec 32) : List Region :=
  [⟨State.addr D, L⟩, ⟨State.addr (SP - BitVec.ofNat 32 16), 12⟩]
abbrev updWr (B : BitVec 32) : List Region := [⟨State.addr B, 192⟩, ⟨State.addr B + BitVec.ofNat 64 192, 576⟩]

/-- `update`'s precondition, after its frame's push. -/
theorem update_pre {B SP : BitVec 32} {s : State} (h : Ctx B SP s) {D : BitVec 32} {L : Nat}
    (hD : s.gpr .r9 = D) (hL : (s.gpr .r10).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨State.addr D, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨State.addr D, L⟩ ⟨State.addr B, 768⟩)
    (hDk : (stkR SP 32).Disjoint ⟨State.addr D, L⟩) (h0 : s.gpr .r0 = B) (h12 : s.gpr .r12 = B + 192) :
    (updateArm b).pre ((pushed upd4 s).callEntry.withRegions (updRd D L SP) (updWr B)) ∧
      Covers (updRd D L SP ++ updWr B) ((pushed upd4 s).rd ++ (pushed upd4 s).wr) ∧
      Covers (updWr B) (pushed upd4 s).wr := by
  have hlo := h.lo
  have hfit := h.fits
  obtain e192 : State.addr (B + 192) = State.addr B + BitVec.ofNat 64 192 := h.addr_add (by decide)
  obtain hn : 4 * upd4.length ≤ s.sp.toNat := by rw [h.sp]; simp only [List.length_cons, List.length_nil]; omega_arith
  obtain a0 : ∀ {rd wr}, stackArg ((pushed upd4 s).callEntry.withRegions rd wr) 0 = D := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [hD]
  obtain a1 : ∀ {rd wr}, (stackArg ((pushed upd4 s).callEntry.withRegions rd wr) 1).toNat = L := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [hL]
  obtain a2 : ∀ {rd wr}, stackArg ((pushed upd4 s).callEntry.withRegions rd wr) 2 = B + 192 := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [h12]
  obtain eA : ∀ {rd wr}, stackArgAddr ((pushed upd4 s).callEntry.withRegions rd wr) 0 =
      State.addr (SP - BitVec.ofNat 32 16) := by
    intro rd wr; rw [pushed_argAddr hn, h.sp, addr_sub' (by omega_arith)]; rfl
  obtain eSp : ∀ {rd wr}, ((pushed upd4 s).callEntry.withRegions rd wr).sp = SP - BitVec.ofNat 32 16 := by
    intro rd wr; simp [pushed_sp, h.sp]
  obtain stR : (stkR SP 32).Disjoint ⟨State.addr B, 192⟩ := h.stk0 (by decide)
  obtain scR : (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 192, 576⟩ := h.stk_sub (by decide)
  obtain argS : Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 16), 12⟩ (stkR SP 32) := stk_args hlo (by decide)
  obtain calS : Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 16) - 16, 16⟩ (stkR SP 32) :=
    stk_callee hlo (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [updateArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      Proof.Blake2.Arm.Stream.ce0, pushed_gpr, a0, a1, a2, eA, eSp, e192, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, Proof.Blake2.Arm.Stream.below, h0]
    refine ⟨trivial, trivial, Offset.base_disjoint _ (by decide) (by decide),
      hDs.sub_right (Region.sub_prefix (by decide)), hDs.sub_right (Offset.sub_base _ (by decide)),
      stR.sub_left argS, scR.sub_left argS, ?_, ?_, ?_, by omega_arith, hDfit, ?_, ?_, ?_⟩
    · exact stR.sub_left calS
    · exact hDk.sub_left calS
    · exact scR.sub_left calS
    · rw [show (B + 192).toNat = B.toNat + 192 by
        rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega_arith]; omega_arith
    · rw [sub_toNat' (by omega_arith)]; omega_arith
    · rw [sub_toNat' (by omega_arith)]; have := SP.isLt; omega_arith
  · rw [pushed_rd, pushed_wr]
    refine Covers.append_left (Covers.cons (covers_ins _ hDc) (Covers.cons ?_ Covers.nil))
      (covers_ins _ (Covers.right ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))))
    intro a k ⟨r, hr, hc'⟩
    simp only [List.mem_singleton] at hr; subst hr
    refine InRegions_append_cons.mpr (.inl ?_)
    simp only [List.length_cons, List.length_nil, h.sp, Region.Contains, Nat.zero_add, Nat.reduceAdd,
      Nat.reduceMul] at hc' ⊢
    rw [addr_sub' (by omega_arith)] at hc' ⊢; omega_arith
  · rw [pushed_wr]
    exact covers_cons _ ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))

/-- `update` hashes the `L` bytes at `D` (in `r9` and `r10`) into the state at
`B`, whose byte count is in `r3:r2`. -/
theorem update_ok {B SP : BitVec 32} {s : State} (h : Ctx B SP s) {D : BitVec 32} {L : Nat}
    (hD : s.gpr .r9 = D) (hL : (s.gpr .r10).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨State.addr D, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨State.addr D, L⟩ ⟨State.addr B, 768⟩)
    (hDk : (stkR SP 32).Disjoint ⟨State.addr D, L⟩)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (State.addr B) d)
    (hc : s.gpr .r3 ++ s.gpr .r2 = BitVec.ofNat 64 d.length) (hlen : d.length + L < 2 ^ 64) :
    WP isa update s fun t => Repr b h0 t.mem (State.addr B) (d ++ bytesAt s.mem (State.addr D) L) ∧
      (∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨State.addr B, 768⟩, stkR SP 32] s.mem t.mem := by
  unfold update
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_)
  have hlo := h.lo
  obtain o₂ : ∀ r, r ≠ .r0 → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r h0 h12 => by
    rw [u₂.other _ h12, u₁.other _ h0]
  obtain sp₂ : s₂.sp = SP := by rw [u₂.sp, u₁.sp, h.sp]
  obtain w₂ : s₂.wr = s.wr := u₂.wr.trans u₁.wr
  obtain r₂ : s₂.rd = s.rd := u₂.rd.trans u₁.rd
  obtain m₂ : s₂.mem = s.mem := u₂.mem.trans u₁.mem
  obtain c₂ : Ctx B SP s₂ := h.of_regs (o₂ _ (by decide) (by decide)) (u₂.sp.trans u₁.sp) w₂
  obtain hn : 4 * upd4.length ≤ s₂.sp.toNat := by rw [sp₂]; simp only [List.length_cons, List.length_nil]; omega_arith
  obtain ⟨pre, cv, cw⟩ := update_pre c₂ (by rw [o₂ _ (by decide) (by decide), hD])
    (by rw [o₂ _ (by decide) (by decide), hL]) hDfit (by rw [r₂, w₂]; exact hDc) hDs hDk
    (by rw [u₂.other _ (by decide), u₁.gpr, h.r4]) (by rw [u₂.gpr, u₁.other _ (by decide), h.r4])
  obtain stR : (stkR SP 32).Disjoint ⟨State.addr B, 192⟩ := h.stk0 (by decide)
  refine frameCall_ok (rs := upd4) (t := .r0) (by decide) (by decide) (by decide) (k := updateArm b)
    update_v.1 (K := 32) (by rw [update_stack]; decide) (by rw [sp₂]; exact hlo) pre cv cw
    fun t mL uL hfl af hpost => ?_
  obtain hfl' : Frame [stkR SP 32] t.mem mL := hfl.sub fun r hr =>
    ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr, sp₂]; exact stkR_sub (by decide) hlo⟩
  obtain hpush : Frame [stkR SP 32] s₂.mem (pushed upd4 s₂).mem :=
    (pushed_stk hn).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by rw [sp₂]; exact stkR_sub (by decide) hlo⟩
  obtain a0 : ∀ {rd wr}, stackArg ((pushed upd4 s₂).callEntry.withRegions rd wr) 0 = D := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [o₂ .r9 (by decide) (by decide), hD]
  obtain a1 : ∀ {rd wr}, (stackArg ((pushed upd4 s₂).callEntry.withRegions rd wr) 1).toNat = L := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [o₂ .r10 (by decide) (by decide), hL]
  simp only [updateArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    Proof.Blake2.Arm.Stream.ce0, pushed_gpr, u₂.other _ (by decide : Reg.r0 ≠ .r12), u₁.gpr, h.r4, a0, a1] at hpost
  obtain reprE : Repr b h0 (pushed upd4 s₂).mem (State.addr B) d :=
    repr_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact stR.symm) (m₂ ▸ repr)
  obtain countE : countArm ((pushed upd4 s₂).callEntry.withRegions (updRd D L SP) (updWr B)) =
      BitVec.ofNat 64 d.length := by
    simp only [countArm, State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce2,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), pushed_gpr,
      o₂ .r2 (by decide) (by decide), o₂ .r3 (by decide) (by decide)]
    exact hc
  obtain dataE : bytesAt (pushed upd4 s₂).mem (State.addr D) L = bytesAt s.mem (State.addr D) L := by
    rw [← m₂]
    exact Proof.Blake2.bytesAt_congr fun i hi =>
      hpush.bytes (R := ⟨State.addr D, L⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hDk.symm) (by simp; omega_arith) hi
  have := hpost h0 d reprE countE (by omega_arith)
  rw [dataE] at this
  refine ⟨repr_frame hfl' (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stR.symm) this,
    fun r hr hl => (af.cs r hr hl).trans ?_, af.rd.trans r₂, af.wr.trans w₂, af.sp.trans (by rw [sp₂, h.sp]), ?_⟩
  · have : r ≠ .r0 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact o₂ r this.1 this.2
  · rw [← m₂]
    refine af.frame.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [sp₂]; exact fun _ h => h⟩

/-! ## `finalize` -/

/-- The registers `finalize`'s frame pushes: the digest's address and the callees' scratch. -/
abbrev fin2 : List Reg := [.r1, .r12]

/-- The regions `finalize` is given. -/
abbrev finRd (SP : BitVec 32) : List Region := [⟨State.addr (SP - BitVec.ofNat 32 8), 8⟩]
abbrev finWr (B : BitVec 32) : List Region :=
  [⟨State.addr B, 192⟩, ⟨State.addr B + BitVec.ofNat 64 768, 64⟩, ⟨State.addr B + BitVec.ofNat 64 192, 576⟩]

/-- `finalize`'s precondition, after its frame's push. -/
theorem finalize_pre {B SP : BitVec 32} {s : State} (h : Ctx B SP s) (h0 : s.gpr .r0 = B)
    (h1 : s.gpr .r1 = B + 768) (h12 : s.gpr .r12 = B + 192) :
    (finalizeArm b).pre ((pushed fin2 s).callEntry.withRegions (finRd SP) (finWr B)) ∧
      Covers (finRd SP ++ finWr B) ((pushed fin2 s).rd ++ (pushed fin2 s).wr) ∧
      Covers (finWr B) (pushed fin2 s).wr := by
  have hlo := h.lo
  have hfit := h.fits
  obtain e192 : State.addr (B + 192) = State.addr B + BitVec.ofNat 64 192 := h.addr_add (by decide)
  obtain e768 : State.addr (B + 768) = State.addr B + BitVec.ofNat 64 768 := h.addr_add (by decide)
  obtain hn : 4 * fin2.length ≤ s.sp.toNat := by rw [h.sp]; simp only [List.length_cons, List.length_nil]; omega_arith
  obtain a0 : ∀ {rd wr}, stackArg ((pushed fin2 s).callEntry.withRegions rd wr) 0 = B + 768 := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [h1]
  obtain a1 : ∀ {rd wr}, stackArg ((pushed fin2 s).callEntry.withRegions rd wr) 1 = B + 192 := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [h12]
  obtain eA : ∀ {rd wr}, stackArgAddr ((pushed fin2 s).callEntry.withRegions rd wr) 0 =
      State.addr (SP - BitVec.ofNat 32 8) := by
    intro rd wr; rw [pushed_argAddr hn, h.sp, addr_sub' (by omega_arith)]; rfl
  obtain eSp : ∀ {rd wr}, ((pushed fin2 s).callEntry.withRegions rd wr).sp = SP - BitVec.ofNat 32 8 := by
    intro rd wr; simp [pushed_sp, h.sp]
  obtain stR : (stkR SP 32).Disjoint ⟨State.addr B, 192⟩ := h.stk0 (by decide)
  obtain scR : (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 192, 576⟩ := h.stk_sub (by decide)
  obtain dgR : (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 768, 64⟩ := h.stk_sub (by decide)
  obtain argS : Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 8), 8⟩ (stkR SP 32) := stk_args8 hlo (by decide)
  obtain calS : Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 8) - 16, 16⟩ (stkR SP 32) :=
    stk_callee hlo (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [finalizeArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      Proof.Blake2.Arm.Stream.ce0, pushed_gpr, a0, a1, eA, eSp, e192, e768, h0, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, Proof.Blake2.Arm.Stream.below]
    refine ⟨trivial, trivial, Offset.base_disjoint _ (by decide) (by decide),
      Offset.base_disjoint _ (by decide) (by decide), Offset.disjoint _ (by decide) (by decide) (by decide),
      stR.sub_left argS, dgR.sub_left argS, scR.sub_left argS, stR.sub_left calS, dgR.sub_left calS,
      scR.sub_left calS, by omega_arith, ?_, ?_, ?_, ?_⟩
    · rw [show (B + 768).toNat = B.toNat + 768 by
        rw [BitVec.toNat_add, show (768 : BitVec 32).toNat = 768 from rfl]; omega_arith]; omega_arith
    · rw [show (B + 192).toNat = B.toNat + 192 by
        rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega_arith]; omega_arith
    · rw [sub_toNat' (by omega_arith)]; omega_arith
    · rw [sub_toNat' (by omega_arith)]; have := SP.isLt; omega_arith
  · rw [pushed_rd, pushed_wr]
    refine Covers.append_left (Covers.cons ?_ Covers.nil)
      (covers_ins _ (Covers.right ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
        (h.cov (d := 192) (by decide))))))
    intro a k ⟨r, hr, hc'⟩
    simp only [List.mem_singleton] at hr; subst hr
    refine InRegions_append_cons.mpr (.inl ?_)
    simp only [List.length_cons, List.length_nil, h.sp, Region.Contains, Nat.zero_add, Nat.reduceAdd,
      Nat.reduceMul] at hc' ⊢
    rw [addr_sub' (by omega_arith)] at hc' ⊢; omega_arith
  · rw [pushed_wr]
    exact covers_cons _ ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
      (h.cov (d := 192) (by decide))))

/-- `finalize` writes the hash of the data in the state at `B`, whose byte
count is in `r3:r2`, to `scratch[768, 832)`. -/
theorem finalize_ok {B SP : BitVec 32} {s : State} (h : Ctx B SP s)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (State.addr B) d)
    (hc : s.gpr .r3 ++ s.gpr .r2 = BitVec.ofNat 64 d.length) (hlen : d.length < 2 ^ 64) :
    WP isa finalize s fun t => bytesAt t.mem (State.addr B + 768) 64 = finalHash b h0 d ∧
      (∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨State.addr B, 832⟩, stkR SP 32] s.mem t.mem := by
  unfold finalize
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_)
  have hlo := h.lo
  have hfit := h.fits
  obtain o₃ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h0 h1 h12 => by
    rw [u₃.other _ h12, u₂.other _ h1, u₁.other _ h0]
  obtain sp₃ : s₃.sp = SP := by rw [u₃.sp, u₂.sp, u₁.sp, h.sp]
  obtain w₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain r₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain e768 : State.addr (B + 768) = State.addr B + BitVec.ofNat 64 768 := h.addr_add (by decide)
  obtain hn : 4 * fin2.length ≤ s₃.sp.toNat := by rw [sp₃]; simp only [List.length_cons, List.length_nil]; omega_arith
  obtain r0₃ : s₃.gpr .r0 = B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.r4]
  obtain r1₃ : s₃.gpr .r1 = B + 768 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.r4]
  obtain r12₃ : s₃.gpr .r12 = B + 192 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r4]
  obtain c₃ : Ctx B SP s₃ := h.of_regs (o₃ _ (by decide) (by decide) (by decide)) (u₃.sp.trans (u₂.sp.trans u₁.sp)) w₃
  obtain ⟨pre, cv, cw⟩ := finalize_pre c₃ r0₃ r1₃ r12₃
  obtain stR : (stkR SP 32).Disjoint ⟨State.addr B, 192⟩ := h.stk0 (by decide)
  refine frameCall_ok (rs := fin2) (t := .r0) (by decide) (by decide) (by decide) (k := finalizeArm b)
    finalize_v.1 (K := 32) (by rw [finalize_stack]; decide) (by rw [sp₃]; exact hlo) pre cv cw
    fun t mL uL hfl af hpost => ?_
  obtain hfl' : Frame [stkR SP 32] t.mem mL := hfl.sub fun r hr =>
    ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr, sp₃]; exact stkR_sub (by decide) hlo⟩
  obtain hpush : Frame [stkR SP 32] s₃.mem (pushed fin2 s₃).mem :=
    (pushed_stk hn).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by rw [sp₃]; exact stkR_sub (by decide) hlo⟩
  obtain a0 : ∀ {rd wr}, stackArg ((pushed fin2 s₃).callEntry.withRegions rd wr) 0 = B + 768 := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [r1₃]
  simp only [finalizeArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    Proof.Blake2.Arm.Stream.ce0, pushed_gpr, r0₃, a0, e768, Proof.Blake2.bufOff] at hpost
  obtain reprE : Repr b h0 (pushed fin2 s₃).mem (State.addr B) d :=
    repr_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact stR.symm) (m₃ ▸ repr)
  obtain countE : countArm ((pushed fin2 s₃).callEntry.withRegions (finRd SP) (finWr B)) =
      BitVec.ofNat 64 d.length := by
    simp only [countArm, State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce2,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), pushed_gpr,
      o₃ .r2 (by decide) (by decide) (by decide), o₃ .r3 (by decide) (by decide) (by decide)]
    exact hc
  refine ⟨?_, fun r hr hl => (af.cs r hr hl).trans ?_,
    af.rd.trans r₃, af.wr.trans w₃, af.sp.trans (by rw [sp₃, h.sp]), ?_⟩
  · -- The digest is apart from the released frame.
    dsimp only
    rw [Proof.Blake2.bytesAt_congr fun i hi => hfl'.bytes (R := ⟨State.addr B + 768, 64⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.stk.sub_right (Offset.sub_base _ (by decide))).symm) (by show 64 ≤ 2 ^ 64; decide) hi]
    simpa using hpost h0 d reprE hlen countE
  · have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact o₃ r this.1 this.2.1 this.2.2
  · rw [← m₃]
    refine af.frame.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [sp₃]; exact fun _ h => h⟩

end VG.Proof.Argon2.Arm.HPrime

end

end

/-!
# Argon2 H′ on ARMv7: hashing in `scratch`

What the hash macros keep (`Keeps`: `r4`–`r8`, `r11`, the stack pointer, the
permissions, and the memory outside `scratch[0, 832)` and the 32 bytes below
the stack pointer), and the hash of a fixed `scratch` buffer
(`absorbFixed_ok`) and of the 64-byte digest (`next_ok`).
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (init update finalize absorbFixed next)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_reg op2_imm)

/-- The registers the hash macros keep, that callers keep their values in. -/
abbrev kept : List Reg := [.r4, .r5, .r6, .r7, .r8, .r11]

/-- The registers the macros write are not kept. -/
theorem kept_ne : ∀ q ∈ kept, q ≠ .r0 ∧ q ≠ .r1 ∧ q ≠ .r2 ∧ q ≠ .r3 ∧ q ≠ .r9 ∧ q ≠ .r10 ∧ q ≠ .r12 ∧
    q ≠ .lr := by decide

/-- What the hash macros keep. -/
structure Keeps (B SP : BitVec 32) (s t : State) : Prop where
  gpr : ∀ r ∈ kept, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨State.addr B, 832⟩, stkR SP 32] s.mem t.mem

theorem Keeps.trans {B SP : BitVec 32} {s t u : State} (h : Keeps B SP s t) (h' : Keeps B SP t u) :
    Keeps B SP s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.sp.trans h.sp, h'.rd.trans h.rd, h'.wr.trans h.wr,
    h.frame.trans h'.frame⟩

theorem Keeps.r4 {B SP : BitVec 32} {s t : State} (h : Keeps B SP s t) : t.gpr .r4 = s.gpr .r4 :=
  h.gpr _ (by decide)

theorem Keeps.ctx {B SP : BitVec 32} {s t : State} (h : Keeps B SP s t) (c : Ctx B SP s) : Ctx B SP t :=
  c.of_regs h.r4 h.sp h.wr

/-- Steps that keep memory, the permissions, the stack pointer and `kept`. -/
theorem Keeps.same {B SP : BitVec 32} {s t : State} (hg : ∀ r ∈ kept, t.gpr r = s.gpr r)
    (hs : t.sp = s.sp) (hm : t.mem = s.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : Keeps B SP s t :=
  ⟨hg, hs, hrd, hwr, hm ▸ Frame.refl _ _⟩

/-- Calls keep the callee-saved registers and write within the regions. -/
theorem Keeps.of_call {B SP : BitVec 32} {s t : State} (hr : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r)
    (hsp : t.sp = s.sp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [(⟨State.addr B, 832⟩ : Region), stkR SP 32], Region.Sub r r') :
    Keeps B SP s t :=
  ⟨fun r h => by
    have hk : r ∈ preserved ∧ r ≠ .lr := by
      simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hr r hk.1 hk.2,
    hsp, hrd, hwr, hf.sub hs⟩

/-- Bytes outside `scratch[0, 832)` and the stack are kept. -/
theorem Keeps.bytes {B SP : BitVec 32} {s t : State} (h : Keeps B SP s t) {R : Region}
    (hR : R.len ≤ 2 ^ 64) (h₁ : R.Disjoint ⟨State.addr B, 832⟩) (h₂ : R.Disjoint (stkR SP 32)) :
    bytesAt t.mem R.base R.len = bytesAt s.mem R.base R.len :=
  Proof.Blake2.bytesAt_congr fun i hi => h.frame.bytes (R := R) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂) hR hi

/-! ## Fixed buffers -/

/-- Absorb `size` bytes at `scratch + offset` into an empty state. -/
theorem absorbFixed_ok {B SP : BitVec 32} {s : State} (c : Ctx B SP s) {offset size : Nat}
    (heo : encodable (BitVec.ofNat 32 offset) = true) (hes : encodable (BitVec.ofNat 32 size) = true)
    (ho : B.toNat + offset + size ≤ 2 ^ 32) (hlo : 768 ≤ offset) (hs : size < 2 ^ 32) (hpos : 0 < size)
    (hcov : Covers [⟨State.addr B + BitVec.ofNat 64 offset, size⟩] s.wr)
    (hstk : (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 offset, size⟩) {h0 : HashValue 64}
    (repr : Repr b h0 s.mem (State.addr B) []) :
    WP isa (absorbFixed offset size) s fun t =>
      Repr b h0 t.mem (State.addr B) (bytesAt s.mem (State.addr B + BitVec.ofNat 64 offset) size) ∧
      Keeps B SP s t := by
  unfold absorbFixed
  have hfit := c.fits
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm heo) fun s₃ u₃ => wp_mov (op2_imm hes) fun s₄ u₄ => WP.block_nil ?_)
  have o : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have m : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c₄ : Ctx B SP s₄ := c.of_regs (o _ (by decide) (by decide) (by decide) (by decide))
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have eD : s₄.gpr .r9 = B + BitVec.ofNat 32 offset := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.r4]
  have eDw : State.addr (B + BitVec.ofNat 32 offset) = State.addr B + BitVec.ofNat 64 offset :=
    addr_add (by omega_using [ho, hpos])
  have dTo : (B + BitVec.ofNat 32 offset).toNat = B.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega_using [ho, hpos])]; omega_using [ho, hpos]
  have hL : (s₄.gpr .r10).toNat = size := by
    rw [u₄.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]
  have hDc : Covers [⟨State.addr (B + BitVec.ofNat 32 offset), size⟩] (s₄.rd ++ s₄.wr) := by
    rw [eDw, show s₄.wr = s.wr by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]]; exact Covers.right hcov
  have hDs : Region.Disjoint ⟨State.addr (B + BitVec.ofNat 32 offset), size⟩ ⟨State.addr B, 768⟩ := by
    rw [eDw]; exact Offset.disjoint_base _ hlo (by omega_using [ho])
  have hDk : (stkR SP 32).Disjoint ⟨State.addr (B + BitVec.ofNat 32 offset), size⟩ := by
    rw [eDw]; exact hstk
  have hcount : s₄.gpr .r3 ++ s₄.gpr .r2 = BitVec.ofNat 64 ([] : List Byte).length := by
    have e1 : s₄.gpr .r3 = 0 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    have e2 : s₄.gpr .r2 = 0 := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    rw [e1, e2]; rfl
  refine (update_ok c₄ eD hL (by rw [dTo]; omega_using [ho]) hDc hDs hDk (by rw [m]; exact repr) hcount
    (by simp only [List.length_nil]; omega_using [ho])).mono ?_
  rintro t ⟨r, cs, rd, wr, sp, f⟩
  refine ⟨by rw [m, eDw, List.nil_append] at r; exact r, ?_⟩
  refine (Keeps.same (B := B) (SP := SP) (fun q hq => o q (kept_ne q hq).2.2.1
      (kept_ne q hq).2.2.2.1 (kept_ne q hq).2.2.2.2.1 (kept_ne q hq).2.2.2.2.2.1) (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) m
      (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])).trans
    (Keeps.of_call cs sp rd wr f ?_)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

/-! ## The hash of the digest -/

theorem next_ok {B SP : BitVec 32} {s : State} (c : Ctx B SP s) {n : Nat}
    (hn : s.gpr .r1 = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa next s fun t =>
      bytesAt t.mem (State.addr B + 768) 64 =
        finalHash b (Spec.Blake2.init b n 0) (bytesAt s.mem (State.addr B + 768) 64) ∧
      Keeps B SP s t := by
  unfold next
  have hfit := c.fits
  refine WP.seq ((init_ok c hn hn₁ hn₂).mono fun s₁ ⟨r₁, cs₁, rd₁, wr₁, sp₁, f₁⟩ => ?_)
  have k₁ : Keeps B SP s s₁ := Keeps.of_call cs₁ sp₁ rd₁ wr₁ f₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  have dg : bytesAt s₁.mem (State.addr B + 768) 64 = bytesAt s.mem (State.addr B + 768) 64 := by
    refine Proof.Blake2.bytesAt_congr fun i hi => f₁.bytes (R := ⟨State.addr B + 768, 64⟩) ?_ (by simp) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by decide) (by decide)
  refine WP.seq ((absorbFixed_ok (k₁.ctx c) (offset := 768) (size := 64) (by decide) (by decide) (by omega_using [hfit])
    (by decide) (by decide) (by decide) ((k₁.ctx c).cov (by decide)) (c.stk_sub (by decide)) r₁).mono
    fun s₂ ⟨r₂, k₂⟩ => ?_)
  rw [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, dg] at r₂
  have c₂ := (k₁.trans k₂).ctx c
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
    WP.block_nil ?_)
  have c₄ : Ctx B SP s₄ := c₂.of_regs (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
    (by rw [u₄.sp, u₃.sp]) (by rw [u₄.wr, u₃.wr])
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  refine (finalize_ok c₄ (d := bytesAt s.mem (State.addr B + 768) 64) (by rw [m₄]; exact r₂)
    (by
      have len : (bytesAt s.mem (State.addr B + 768) 64).length = 64 := by simp [bytesAt]
      rw [u₄.gpr, u₄.other _ (by decide), u₃.gpr, len]; rfl) (by simp [bytesAt])).mono ?_
  rintro t ⟨d, cs, rd, wr, sp, f⟩
  refine ⟨d, (k₁.trans k₂).trans ?_⟩
  refine Keeps.of_call (fun q hq hl => (cs q hq hl).trans ?_) (sp.trans (by rw [u₄.sp, u₃.sp]))
    (rd.trans (by rw [u₄.rd, u₃.rd])) (wr.trans (by rw [u₄.wr, u₃.wr])) (m₄ ▸ f) ?_
  · have : q ≠ .r2 ∧ q ≠ .r3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other _ this.2, u₃.other _ this.1]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

end VG.Proof.Argon2.Arm.HPrime

end

end

/-! ### `Argon2.Arm.HPrime.Body`, which this module and modules that import it used -/

section

/-!
# Argon2 H′ on ARMv7: the state of the body

`Body s₀ s`: between H′'s setup and its restore, `r4` points to `scratch`,
`r5` and `r6` hold the input and its length, the stack pointer is as on entry,
memory has changed only in the output, `scratch` and the stack below the
stack pointer, and the caller's registers and the length prefix are kept in
`scratch`. `Out s₀ s xs`: the output so far, `xs`, its pointer (`r7`) and the
bytes left (`r8`). `copy_ok`: copying digest bytes to the output.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (copy copyLoop saved baseSlot pfxOff)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_sub wp_subs wp_ldrb wp_strb op2_reg op2_imm sub_ofNat
  ofNat_beq_zero eval_ne eval_eq)
open VG.WriteBytes

/-- Where the caller's registers are, `r4` first. -/
abbrev saveList : List (Reg × Nat) := (.r4, baseSlot) :: saved

theorem saveList_slots : Spill.Slots 840 876 saveList := by decide

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- The state of the body. -/
structure Body (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = scr s₀
  r5 : s.gpr .r5 = inp s₀
  r6 : s.gpr .r6 = s₀.gpr .r1
  sp : s.sp = sp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [outR s₀, scrR s₀, stk s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (P s₀) s₀.gpr saveList
  pfx : bytesAt s.mem (P s₀ + 832) 4 = Spec.Argon2.le32 (ol s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem Body.ctx {s : State} (h : Body s₀ s) : Ctx (scr s₀) (sp₀ s₀) s :=
  ⟨h.r4, h.sp, by have := hp.scr_fits; omega_arith, hp.sp_lo,
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp [h.wr, hp.wr], 0, by simp, by simp⟩),
    hp.stk_scr.sub_right (Region.sub_prefix (by decide))⟩

/-- A word of `scratch` from offset 832 on is kept by the hash macros. -/
theorem keeps_word {s t : State} (k : Keeps (scr s₀) (sp₀ s₀) s t) {d : Nat} (hd : 832 ≤ d)
    (hd' : d + 4 ≤ 16384) : t.mem.readW (P s₀ + BitVec.ofNat 64 d) 32 = s.mem.readW (P s₀ + BitVec.ofNat 64 d) 32 := by
  refine k.frame.readW (r := ⟨P s₀ + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ hd (by omega_arith)
  · exact (hp.stk_scr.sub_right (Offset.sub_base _ (show d + 4 ≤ 16384 from hd'))).symm

theorem Body.keeps {s t : State} (h : Body s₀ s) (k : Keeps (scr s₀) (sp₀ s₀) s t) : Body s₀ t := by
  refine ⟨(k.gpr _ (by decide)).trans h.r4, (k.gpr _ (by decide)).trans h.r5, (k.gpr _ (by decide)).trans h.r6,
    k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (k.frame.sub fun r hr => ?_), fun q hq => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stk s₀, by simp, fun _ h => h⟩
  · have hb := saveList_slots.bound hq
    rw [keeps_word hp k (by omega_arith) (by omega_arith)]; exact h.saved q hq
  · rw [← h.pfx]
    exact k.bytes (R := ⟨P s₀ + 832, 4⟩) (by simp) (Offset.disjoint_base _ (by decide) (by decide))
      (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))).symm

omit hp in
/-- A register write that keeps `r4`–`r6`. -/
theorem Body.upd {s t : State} (h : Body s₀ s) {d : Reg} {v : BitVec 32} (u : MdStream.Arm.Upd s t d v)
    (h4 : d ≠ .r4) (h5 : d ≠ .r5) (h6 : d ≠ .r6) : Body s₀ t :=
  ⟨by rw [u.other _ (Ne.symm h4), h.r4], by rw [u.other _ (Ne.symm h5), h.r5], by rw [u.other _ (Ne.symm h6), h.r6],
    by rw [u.sp, h.sp], by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.mem]; exact h.frame,
    by rw [u.mem]; exact h.saved, by rw [u.mem]; exact h.pfx⟩

end

/-! ## The output -/

/-- The output so far. -/
structure Out (s₀ s : State) (xs : List Byte) : Prop where
  ptr : s.gpr .r7 = op s₀ + BitVec.ofNat 32 xs.length
  left : s.gpr .r8 = BitVec.ofNat 32 (ol s₀ - xs.length)
  bytes : bytesAt s.mem (State.addr (op s₀)) xs.length = xs
  len : xs.length ≤ ol s₀

/-- The digest. -/
abbrev digest (s₀ s : State) : List Byte := bytesAt s.mem (P s₀ + 768) 64

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- The output is kept by the hash macros. -/
theorem Out.keeps {s t : State} {xs : List Byte} (h : Out s₀ s xs)
    (k : Keeps (scr s₀) (sp₀ s₀) s t) : Out s₀ t xs := by
  refine ⟨(k.gpr _ (by decide)).trans h.ptr, (k.gpr _ (by decide)).trans h.left, ?_, h.len⟩
  obtain kb := k.bytes (R := ⟨State.addr (op s₀), xs.length⟩)
    (by have := h.len; have := hp.out_fits; simp; omega_arith)
    ((hp.out_scr.sub_left (Region.sub_prefix h.len)).sub_right (Region.sub_prefix (by decide)))
    ((hp.stk_out.sub_right (Region.sub_prefix h.len)).symm)
  simp only at kb
  rw [kb]; exact h.bytes

/-! ## Copying digest bytes -/

/-- The copy loop's state after `j` of `n` bytes, from `s`: the bytes go from
the digest to `op + k`. -/
structure CopyI (s₀ s : State) (k n j : Nat) (t : State) : Prop where
  j_le : j ≤ n
  r9 : t.gpr .r9 = scr s₀ + 768 + BitVec.ofNat 32 j
  r7 : t.gpr .r7 = op s₀ + BitVec.ofNat 32 (k + j)
  r10 : t.gpr .r10 = BitVec.ofNat 32 (n - j)
  other : ∀ x, x ≠ .r12 → x ≠ .r9 → x ≠ .r7 → x ≠ .r10 → t.gpr x = s.gpr x
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = writeBytes s.mem (State.addr (op s₀) + BitVec.ofNat 64 k) ((digest s₀ s).take j)

omit hp in
theorem setWidth_byte (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  ext i hi; simp

theorem copyLoop_ok {s : State} (b : Body s₀ s) {k n : Nat} (hk : s.gpr .r7 = op s₀ + BitVec.ofNat 32 k)
    (h9 : s.gpr .r9 = scr s₀ + 768) (hn : s.gpr .r10 = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64)
    (hkn : k + n ≤ ol s₀) {Q : State → Prop} (hQ : ∀ t, CopyI s₀ s k n n t → Q t) :
    WP isa copyLoop s Q := by
  have hs := hp.scr_fits
  have ho := hp.out_fits
  obtain dgR : Region.Disjoint ⟨P s₀ + 768, 64⟩ ⟨State.addr (op s₀) + BitVec.ofNat 64 k, n⟩ :=
    ((hp.out_scr.sub_left (Offset.sub_base _ (d := k) (n := n) (k := ol s₀) (by omega_arith))).sub_right
      (Offset.sub_base (P s₀) (d := 768) (n := 64) (k := 16384) (by decide))).symm
  refine WP.loop (M := isa) (fun m (t : State) => ∃ j, m = n - j ∧ j < n ∧ CopyI s₀ s k n j t) ?_ n s
    ⟨0, by omega_arith, by omega_arith, ⟨by omega_arith, by simp [h9], by simp [hk], by rw [hn, Nat.sub_zero],
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩⟩
  rintro m t ⟨j, rfl, hj, h⟩
  obtain e768 : State.addr (scr s₀ + 768) = P s₀ + 768 := addr_add (k := 768) (by omega_arith)
  -- The byte read.
  obtain hin : InRegions (t.rd ++ t.wr) (P s₀ + 768 + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr, b.rd, b.wr, hp.wr]
    refine ⟨scrR s₀, by simp, ?_⟩
    rw [show P s₀ + 768 + BitVec.ofNat 64 j = P s₀ + BitVec.ofNat 64 (768 + j) from Offset.add_add _ 768 j]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  obtain hbyte : t.mem (P s₀ + 768 + BitVec.ofNat 64 j) = s.mem (P s₀ + 768 + BitVec.ofNat 64 j) := by
    rw [h.mem]
    obtain hl : ((digest s₀ s).take j).length ≤ n := by simp [digest, bytesAt]; omega_arith
    exact (writeBytes_frame (R := ⟨State.addr (op s₀) + BitVec.ofNat 64 k, n⟩) s.mem _ _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact hl)).bytes
      (R := ⟨P s₀ + 768, 64⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dgR)
      (by show (64 : Nat) ≤ 2 ^ 64; decide) (show j < 64 by omega_arith)
  -- The byte written.
  obtain hout : InRegions t.wr (State.addr (op s₀) + BitVec.ofNat 64 (k + j)) 1 := by
    rw [h.wr, b.wr, hp.wr]
    exact ⟨outR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine wp_ldrb (a := P s₀ + 768 + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r9, BitVec.add_zero, addr_add (by rw [BitVec.toNat_add]; simp; omega_arith), e768]) hin
    fun s₁ u₁ => ?_
  refine wp_strb (a := State.addr (op s₀) + BitVec.ofNat 64 (k + j)) (by decide)
    (by rw [u₁.other _ (by decide), h.r7, BitVec.add_zero, addr_add (by omega_arith)])
    (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun s₅ u₅ z₅ => WP.block_nil ?_
  obtain hr10 : s₅.gpr .r10 = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r10,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith), Nat.sub_sub]
  obtain hI : CopyI s₀ s k n (j + 1) s₅ := by
    refine ⟨by omega_arith, ?_, ?_, hr10, fun x h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r9,
        BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r7,
        BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [u₅.other x h4, u₄.other x h3, u₃.other x h2, g₂.gpr, u₁.other x h1, h.other x h1 h2 h3 h4]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · have hj' : j < (digest s₀ s).length := by simp [digest, bytesAt]; omega_arith
      obtain hl : (List.take j (digest s₀ s)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.gpr, hbyte, h.mem,
        List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega_arith), hl, setWidth_byte, Offset.add_add]
      congr 1
      simp [digest, bytesAt]
  obtain hz : isa.eval .ne s₅ = some (decide (n - (j + 1) ≠ 0)) := by
    show VG.Arm.eval .ne s₅ = _
    rw [eval_ne, z₅, ← u₅.gpr, hr10, ofNat_beq_zero (by omega_arith)]
    simp
  by_cases hjn : j + 1 = n
  · exact .inl ⟨by rw [hz]; simp; omega_arith, hQ _ (hjn ▸ hI)⟩
  · exact .inr ⟨by rw [hz]; simp; omega_arith, n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hI⟩

/-- Emit `n` digest bytes after the output `xs`. -/
theorem copyOut_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs) {n : Nat}
    (hn : s.gpr .r10 = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (hkn : xs.length + n ≤ ol s₀) :
    WP isa copy s fun t => Body s₀ t ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r11 = s.gpr .r11 ∧
      bytesAt t.mem (State.addr (op s₀)) (xs.length + n) = xs ++ (digest s₀ s).take n ∧
      t.gpr .r7 = op s₀ + BitVec.ofNat 32 (xs.length + n) ∧ digest s₀ t = digest s₀ s := by
  have hs := hp.scr_fits
  have ho := hp.out_fits
  unfold copy
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  obtain b₁ : Body s₀ s₁ := b.keeps hp (Keeps.same (fun r hr => u₁.other r (by
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.sp u₁.mem u₁.rd u₁.wr)
  refine copyLoop_ok hp b₁ (k := xs.length) (n := n) (by rw [u₁.other _ (by decide), h.ptr])
    (by rw [u₁.gpr, b.r4]) (by rw [u₁.other _ (by decide), hn]) hn₁ hn₂ hkn fun t ht => ?_
  obtain dgR : Region.Disjoint ⟨P s₀ + 768, 64⟩ ⟨State.addr (op s₀) + BitVec.ofNat 64 xs.length, n⟩ :=
    ((hp.out_scr.sub_left (Offset.sub_base _ (d := xs.length) (n := n) (k := ol s₀) (by omega_arith))).sub_right
      (Offset.sub_base (P s₀) (d := 768) (n := 64) (k := 16384) (by decide))).symm
  obtain lenL : ((digest s₀ s₁).take n).length = n := by simp [digest, bytesAt]; omega_arith
  obtain F : Frame [⟨State.addr (op s₀) + BitVec.ofNat 64 xs.length, n⟩] s₁.mem t.mem := by
    rw [ht.mem]; exact writeBytes_frame _ _ _ (by rw [lenL]; exact Region.contains_self _ _)
  obtain outSub : Region.Sub ⟨State.addr (op s₀) + BitVec.ofNat 64 xs.length, n⟩ (outR s₀) :=
    Offset.sub_base _ (by omega_arith)
  obtain d₁ : digest s₀ s₁ = digest s₀ s := by simp only [digest, u₁.mem]
  obtain dt : digest s₀ t = digest s₀ s₁ :=
    Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨P s₀ + 768, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dgR) (by simp) hi
  refine ⟨⟨by rw [ht.other _ (by decide) (by decide) (by decide) (by decide), b₁.r4],
      by rw [ht.other _ (by decide) (by decide) (by decide) (by decide), b₁.r5],
      by rw [ht.other _ (by decide) (by decide) (by decide) (by decide), b₁.r6],
      by rw [ht.sp, b₁.sp], by rw [ht.rd, b₁.rd], by rw [ht.wr, b₁.wr],
      b₁.frame.trans (F.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨outR s₀, by simp, outSub⟩),
      fun q hq => ?_, ?_⟩, ?_, ?_, ?_, ?_, dt.trans d₁⟩
  · have hb := saveList_slots.bound hq
    rw [F.readW (r := ⟨P s₀ + BitVec.ofNat 64 q.2, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.out_scr.sub_left outSub).sub_right (Offset.sub_base _ (by omega_arith))).symm) (by decide)]
    exact b₁.saved q hq
  · rw [← b₁.pfx]
    exact Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨P s₀ + 832, 4⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.out_scr.sub_left outSub).sub_right (Offset.sub_base _ (by decide))).symm) (by simp) hi
  · rw [ht.other _ (by decide) (by decide) (by decide) (by decide), u₁.other _ (by decide)]
  · rw [ht.other _ (by decide) (by decide) (by decide) (by decide), u₁.other _ (by decide)]
  · have old : bytesAt t.mem (State.addr (op s₀)) xs.length = bytesAt s₁.mem (State.addr (op s₀)) xs.length :=
      Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨State.addr (op s₀), xs.length⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (by have := h.len; simp; omega_arith) hi
    obtain new : bytesAt t.mem (State.addr (op s₀) + BitVec.ofNat 64 xs.length) n = (digest s₀ s₁).take n := by
      rw [ht.mem]
      have := bytesAt_writeBytes s₁.mem (State.addr (op s₀) + BitVec.ofNat 64 xs.length)
        ((digest s₀ s₁).take n) (by rw [lenL]; omega_arith)
      rwa [lenL] at this
    rw [Proof.Blake2.bytesAt_add, new, old, d₁, u₁.mem, h.bytes]
  · exact ht.r7

/-- Emit a 32-byte prefix of the digest. -/
theorem emit_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs)
    (hkn : xs.length + 32 ≤ ol s₀) :
    WP isa Impl.Argon2.Arm.HPrime.emitPrefix s fun t => Body s₀ t ∧ t.gpr .r11 = s.gpr .r11 ∧
      Out s₀ t (xs ++ (digest s₀ s).take 32) ∧ digest s₀ t = digest s₀ s := by
  unfold Impl.Argon2.Arm.HPrime.emitPrefix
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  obtain k₁ : Keeps (scr s₀) (sp₀ s₀) s s₁ := Keeps.same (fun r hr => u₁.other r (by
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.sp u₁.mem u₁.rd u₁.wr
  refine WP.seq ((copyOut_ok hp (b.keeps hp k₁) (h.keeps hp k₁) u₁.gpr (by decide) (by decide) hkn).mono
    fun s₂ ⟨b₂, l₂, e₂, by₂, p₂, d₂⟩ => ?_)
  refine wp_sub (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_
  obtain len' : (xs ++ (digest s₀ s).take 32).length = xs.length + 32 := by
    simp [digest, bytesAt]
  refine ⟨b₂.upd u₃ (by decide) (by decide) (by decide), by rw [u₃.other _ (by decide), e₂, u₁.other _ (by decide)],
    ⟨?_, ?_, ?_, by rw [len']; exact hkn⟩, by simp only [digest, u₃.mem]; exact d₂.trans (by simp only [digest, u₁.mem])⟩
  · rw [len', u₃.other _ (by decide), p₂]
  · rw [len', u₃.gpr, l₂, u₁.other _ (by decide), h.left]
    exact (sub_ofNat (a := ol s₀ - xs.length) (b := 32) (by omega_arith)).trans (by congr 1)
  · rw [len', u₃.mem, by₂, show digest s₀ s₁ = digest s₀ s by simp only [digest, u₁.mem]]

/-- Copy the bytes left. -/
theorem copyRemaining_ok {s : State} (b : Body s₀ s) {xs : List Byte} (h : Out s₀ s xs)
    (hn₁ : xs.length < ol s₀) (hn₂ : ol s₀ - xs.length ≤ 64) :
    WP isa Impl.Argon2.Arm.HPrime.copyRemaining s fun t => Body s₀ t ∧ t.gpr .r11 = s.gpr .r11 ∧
      bytesAt t.mem (State.addr (op s₀)) (ol s₀) = xs ++ (digest s₀ s).take (ol s₀ - xs.length) := by
  unfold Impl.Argon2.Arm.HPrime.copyRemaining
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ?_)
  obtain k₁ : Keeps (scr s₀) (sp₀ s₀) s s₁ := Keeps.same (fun r hr => u₁.other r (by
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.sp u₁.mem u₁.rd u₁.wr
  refine (copyOut_ok hp (b.keeps hp k₁) (h.keeps hp k₁) (n := ol s₀ - xs.length)
    (by rw [u₁.gpr, h.left]) (by omega_arith) hn₂ (by omega_arith)).mono
    fun t ⟨bt, _, et, byt, _, _⟩ => ⟨bt, by rw [et, u₁.other _ (by decide)], ?_⟩
  rw [show xs.length + (ol s₀ - xs.length) = ol s₀ by omega_arith] at byt
  rw [byt]; simp only [digest, u₁.mem]

end

end VG.Proof.Argon2.Arm.HPrime

end

end

/-! ### `Argon2.Arm.HPrime.First`, which only this module used -/

section

/-!
# Argon2 H′ on ARMv7: the first digest

`first_ok`: `first` leaves H(min(out_len, 64), LE32(out_len) ‖ input) at the
start of the digest, `scratch[768, 832)`. The input is read before anything
is written to the output, so the two may overlap.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (init update finalize absorbFixed chooseLength absorbInput finishInput first
  cmpLeft)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_add wp_sub wp_cmp op2_reg op2_imm op2_lsr eval_eq eval_ne
  ofNat_beq_zero)
open VG.Proof.Blake2.Arm.Stream (wp_adds wp_adc)

/-- `(x - 1) >> 6 = 0` exactly when `1 ≤ x ≤ 64`. -/
theorem le64_beq {x : Nat} (h₁ : 1 ≤ x) (h₂ : x < 2 ^ 32) :
    ((BitVec.ofNat 32 x - 1) >>> 6 - 0 == 0) = decide (x ≤ 64) := by
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.Arm.sub_ofNat h₁, show ∀ y : BitVec 32, y - 0 = y from fun y => BitVec.sub_zero y,
    MdStream.Arm.ofNat_shr (by omega_using [h₂]), ofNat_beq_zero (by omega_using [h₂])]
  by_cases h : x ≤ 64
  · simp only [h, decide_true, decide_eq_true_eq]; omega_using [h]
  · simp only [h, decide_false, decide_eq_false_iff_not]; omega_using [h]

/-- The comparisons with 64 of the bytes left (in `r8`). -/
theorem cmpLeft_ok {s : State} {x : Nat} (hx : s.gpr .r8 = BitVec.ofNat 32 x) (h₁ : 1 ≤ x) (h₂ : x < 2 ^ 32) :
    WP isa (.block cmpLeft) s fun t => isa.eval .eq t = some (decide (x ≤ 64)) ∧
      (∀ r, r ≠ .r0 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold cmpLeft
  refine wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · show VG.Arm.eval .eq s₃ = _
    rw [eval_eq, z₃, u₂.gpr, u₁.gpr, hx]
    exact congrArg some (le64_beq h₁ h₂)
  · rw [f₃.gpr, u₂.other _ hr, u₁.other _ hr]
  · rw [f₃.mem, u₂.mem, u₁.mem]
  · rw [f₃.rd, u₂.rd, u₁.rd]
  · rw [f₃.wr, u₂.wr, u₁.wr]
  · rw [f₃.sp, u₂.sp, u₁.sp]

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `r1 := min(out_len, 64)`. -/
theorem choose_ok {s : State} (_b : Body s₀ s) (o : Out s₀ s []) :
    WP isa chooseLength s fun t => t.gpr .r1 = BitVec.ofNat 32 (min (ol s₀) 64) ∧
      Keeps (scr s₀) (sp₀ s₀) s t := by
  have hol := (s₀.gpr .r3).isLt
  have hpos := hp.ol_pos
  have l₀ : s.gpr .r8 = BitVec.ofNat 32 (ol s₀) := by rw [o.left]; rfl
  unfold chooseLength
  refine WP.seq (wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ?_)
  have k₃ : Keeps (scr s₀) (sp₀ s₀) s s₃ := Keeps.same (fun r hr => by
      rw [f₃.gpr, u₂.other _ (kept_ne r hr).2.1, u₁.other _ (kept_ne r hr).2.1])
    (by rw [f₃.sp, u₂.sp, u₁.sp]) (by rw [f₃.mem, u₂.mem, u₁.mem]) (by rw [f₃.rd, u₂.rd, u₁.rd])
    (by rw [f₃.wr, u₂.wr, u₁.wr])
  have r8₃ : s₃.gpr .r8 = BitVec.ofNat 32 (ol s₀) := by rw [k₃.gpr _ (by decide), l₀]
  refine WP.ite (decide (ol s₀ ≤ 64)) (by
      show VG.Arm.eval .eq s₃ = _
      rw [eval_eq, z₃, u₂.gpr, u₁.gpr, l₀]; exact congrArg some (le64_beq hpos hol))
    (fun h => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ⟨?_, ?_⟩)
    (fun h => wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ⟨?_, ?_⟩)
  · have : ol s₀ ≤ 64 := by simpa using h
    rw [u₄.gpr, r8₃, Nat.min_eq_left this]
  · exact k₃.trans (Keeps.same (fun r hr => u₄.other r (kept_ne r hr).2.1) u₄.sp u₄.mem u₄.rd u₄.wr)
  · have : 64 ≤ ol s₀ := by simp at h; omega_using [h]
    rw [u₄.gpr, Nat.min_eq_right this]; rfl
  · exact k₃.trans (Keeps.same (fun r hr => u₄.other r (kept_ne r hr).2.1) u₄.sp u₄.mem u₄.rd u₄.wr)

end

/-! ## The steps of `first` -/

/-- The state before and between the steps of `first`: the body, no output
yet, and the input kept. -/
structure F0 (s₀ s : State) : Prop where
  body : Body s₀ s
  out : Out s₀ s []
  input : bytesAt s.mem (State.addr (inp s₀)) (inl s₀) = bytesAt s₀.mem (State.addr (inp s₀)) (inl s₀)

/-- The length of the first digest. -/
abbrev nF (s₀ : State) : Nat := min (ol s₀) 64

/-- The input, on entry. -/
abbrev inB (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (inp s₀)) (inl s₀)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem F0.keeps {s t : State} (h : F0 s₀ s) (k : Keeps (scr s₀) (sp₀ s₀) s t) : F0 s₀ t := by
  refine ⟨h.body.keeps hp k, h.out.keeps hp k, ?_⟩
  have hif := hp.in_fits
  have := k.bytes (R := inR s₀) (by simp; omega_using [hif])
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in.symm
  simp only at this
  rw [this, h.input]

theorem nF_pos : 1 ≤ nF s₀ := by have := hp.ol_pos; simp only [nF]; omega_using [this]

theorem first_choose {s : State} (h : F0 s₀ s) :
    WP isa chooseLength s fun t => F0 s₀ t ∧ t.gpr .r1 = BitVec.ofNat 32 (nF s₀) :=
  (choose_ok hp h.body h.out).mono fun _ ⟨e, k⟩ => ⟨h.keeps hp k, e⟩

theorem first_init {s : State} (h : F0 s₀ s ∧ s.gpr .r1 = BitVec.ofNat 32 (nF s₀)) :
    WP isa init s fun t => F0 s₀ t ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) [] := by
  have c := h.1.body.ctx hp
  refine (init_ok c h.2 (nF_pos hp) (Nat.min_le_right _ _)).mono fun t ⟨r, cs, rd, wr, sp, f⟩ => ⟨?_, r⟩
  refine h.1.keeps hp (Keeps.of_call cs sp rd wr f fun r hr => ?_)
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩

theorem pfx_cov {s : State} (b : Body s₀ s) : Covers [⟨P s₀ + BitVec.ofNat 64 832, 4⟩] s.wr := by
  rw [b.wr, hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, 832, rfl, by simp⟩

theorem first_fixed {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) []) :
    WP isa (absorbFixed 832 4) s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) (Spec.Argon2.le32 (ol s₀)) := by
  have hs := hp.scr_fits
  refine (absorbFixed_ok (h.1.body.ctx hp) (offset := 832) (size := 4) (by decide) (by decide) (by omega_using [hs])
    (by decide) (by decide) (by decide) (pfx_cov hp h.1.body) (hp.stk_scr.sub_right (Offset.sub_base _ (by decide)))
    h.2).mono fun t ⟨r, k⟩ => ⟨h.1.keeps hp k, ?_⟩
  rw [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, h.1.body.pfx] at r
  exact r

theorem first_input {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) (Spec.Argon2.le32 (ol s₀))) :
    WP isa absorbInput s fun t => F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (nF s₀) 0) t.mem (P s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  have hif := hp.in_fits
  have hil := (s₀.gpr .r1).isLt
  unfold absorbInput
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_)
  have o₄ : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have k₄ : Keeps (scr s₀) (sp₀ s₀) s s₄ := Keeps.same (fun r hr => o₄ r (kept_ne r hr).2.2.1
      (kept_ne r hr).2.2.2.1 (kept_ne r hr).2.2.2.2.1 (kept_ne r hr).2.2.2.2.2.1)
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have F₄ := h.1.keeps hp k₄
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have cnt₄ : s₄.gpr .r3 ++ s₄.gpr .r2 = BitVec.ofNat 64 (Spec.Argon2.le32 (ol s₀)).length := by
    rw [Proof.Argon2.le32_length, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl
  have r9 : s₄.gpr .r9 = inp s₀ := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.1.body.r5]
  have r10 : (s₄.gpr .r10).toNat = inl s₀ := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.1.body.r6]
  have hDc : Covers [⟨State.addr (inp s₀), inl s₀⟩] (s₄.rd ++ s₄.wr) := by
    rw [F₄.body.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨inR s₀, by simp, 0, by simp, by simp⟩
  refine (update_ok (F₄.body.ctx hp) (h0 := Spec.Blake2.init Spec.Blake2.b (nF s₀) 0) r9 r10 hif hDc
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in (by rw [m₄]; exact h.2) cnt₄
    (by rw [Proof.Argon2.le32_length]; omega_using [hif])).mono fun s₅ ⟨r₅, cs₅, rd₅, wr₅, sp₅, f₅⟩ => ?_
  rw [F₄.input] at r₅
  refine ⟨F₄.keeps hp (Keeps.of_call cs₅ sp₅ rd₅ wr₅ f₅ fun r hr => ?_), r₅⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

omit hp in
theorem count4 (x : Nat) (hx : x < 2 ^ 32) :
    ((0 : BitVec 32) + 0 + (if decide (2 ^ 32 ≤ (BitVec.ofNat 32 x).toNat + (4 : BitVec 32).toNat) = true
      then 1 else 0)) ++ (BitVec.ofNat 32 x + 4) = BitVec.ofNat 64 (x + 4) := by
  rw [Proof.Blake2.Arm.Stream.add64]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, Proof.Blake2.Arm.Stream.toNat_append32]
  simp [Nat.mod_eq_of_lt hx] <;> omega

theorem first_finish {s : State}
    (h : F0 s₀ s ∧ Repr b (Spec.Blake2.init b (nF s₀) 0) s.mem (P s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀)) :
    WP isa finishInput s fun t => F0 s₀ t ∧
      (digest s₀ t).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  have hif := hp.in_fits
  have hil := (s₀.gpr .r1).isLt
  unfold finishInput
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_adds (op2_imm (by decide)) fun s₂ u₂ c₂ =>
    wp_adc (op2_imm (by decide)) fun s₃ u₃ _ => WP.block_nil ?_)
  have o₃ : ∀ r, r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h2, u₂.other _ h1, u₁.other _ h2]
  have k₃ : Keeps (scr s₀) (sp₀ s₀) s s₃ := Keeps.same (fun r hr => o₃ r (kept_ne r hr).2.2.1
      (kept_ne r hr).2.2.2.1)
    (by rw [u₃.sp, u₂.sp, u₁.sp]) (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₃.wr, u₂.wr, u₁.wr])
  have F₃ := h.1.keeps hp k₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have r6 : s₁.gpr .r6 = BitVec.ofNat 32 (inl s₀) := by rw [u₁.other _ (by decide), h.1.body.r6]; simp
  have cnt : s₃.gpr .r3 ++ s₃.gpr .r2 = BitVec.ofNat 64 (Spec.Argon2.le32 (ol s₀) ++ inB s₀).length := by
    rw [u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide), u₁.gpr, c₂, r6, List.length_append,
      Proof.Argon2.le32_length]
    simp only [inB, bytesAt, List.length_map, List.length_range]
    rw [show 4 + inl s₀ = inl s₀ + 4 by omega_using []]
    exact count4 _ hil
  refine (finalize_ok (F₃.body.ctx hp) (by rw [m₃]; exact h.2) cnt
    (by simp only [List.length_append, Proof.Argon2.le32_length, inB, bytesAt, List.length_map,
      List.length_range]; omega_using [hif])).mono ?_
  rintro t ⟨d, cs, rd, wr, sp, f⟩
  refine ⟨F₃.keeps hp (Keeps.of_call cs sp rd wr f fun r hr => ?_), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · show (bytesAt t.mem (P s₀ + 768) 64).take _ = _
    rw [d, Proof.Argon2.H_stream]

/-- `first` hashes the length prefix and the input. -/
theorem first_ok {s : State} (h : F0 s₀ s) :
    WP isa first s fun t => F0 s₀ t ∧
      (digest s₀ t).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀) := by
  unfold first
  exact WP.seq ((first_choose hp h).mono fun _ h₁ => WP.seq ((first_init hp h₁).mono fun _ h₂ =>
    WP.seq ((first_fixed hp h₂).mono fun _ h₃ => WP.seq ((first_input hp h₃).mono fun _ h₄ =>
      first_finish hp h₄))))

end

end VG.Proof.Argon2.Arm.HPrime

end

end


/-!
# Argon2 H′ on ARMv7: the output from the first digest

`chain_ok`: after the first prefix V₁[0, 32) of a long output, each iteration
hashes the digest again and emits the prefix of the new one, while more than
64 bytes are left. `finish_ok`: `finishOutput` writes H′ to the output, from
the first digest: the digest itself for at most 64 bytes, and otherwise its
prefix, the chain and the last hash (`extend_ok`), of the 33 to 64 bytes left.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (next emitPrefix cmpLeft chain extendDigest finishOutput)
open VG.Proof.MdStream.Arm (Upd wp_mov op2_reg op2_imm)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem chainDigest_succ' (j : Nat) (v : List Byte) :
    chainDigest (j + 1) v = Spec.Argon2.H 64 (chainDigest j v) := by
  induction j generalizing v with
  | zero => rfl
  | succ j ih => exact ih (Spec.Argon2.H 64 v)

theorem chainPrefixes_succ' (j : Nat) (v : List Byte) :
    chainPrefixes (j + 1) v = chainPrefixes j v ++ (Spec.Argon2.H 64 (chainDigest j v)).take 32 := by
  induction j generalizing v with
  | zero => simp [chainPrefixes, chainDigest]
  | succ j ih =>
    rw [chainPrefixes, ih, chainPrefixes, chainDigest, List.append_assoc]

theorem finalHash_length (h0 : HashValue 64) (d : List Byte) : (finalHash b h0 d).length = 64 := by
  simp only [finalHash, Proof.Argon2.wordList_length, Vector.length_toList]

/-- The output after `j` iterations. -/
abbrev chainOut (V : List Byte) (j : Nat) : List Byte := V.take 32 ++ chainPrefixes j V

theorem chainOut_length {V : List Byte} (hV : V.length = 64) (j : Nat) :
    (chainOut V j).length = 32 + 32 * j := by
  simp only [chainOut, List.length_append, List.length_take, hV, Proof.Argon2.chainPrefixes_length]
  omega_arith

section
variable {s₀ : State} (hp : Pre s₀)
include hp

omit hp in
/-- `cmpLeft` on the output `xs`. -/
theorem cmp_ok {s : State} {xs : List Byte} (o : Out s₀ s xs) (hl : xs.length < ol s₀) :
    WP isa (.block cmpLeft) s fun t => isa.eval .eq t = some (decide (ol s₀ - xs.length ≤ 64)) ∧
      Keeps (scr s₀) (sp₀ s₀) s t ∧ t.mem = s.mem := by
  have hol := (s₀.gpr .r3).isLt
  refine (cmpLeft_ok o.left (by omega_arith) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hol)).mono
    fun t ⟨e, g, m, rd, wr, sp⟩ => ⟨e, Keeps.same (fun r hr => g r (kept_ne r hr).1) sp m rd wr, m⟩

/-- What the chain keeps between iterations. -/
structure ChainInv (s₀ : State) (e : BitVec 32) (V : List Byte) (j : Nat) (s : State) : Prop where
  body : Body s₀ s
  r11 : s.gpr .r11 = e
  out : Out s₀ s (chainOut V j)
  digest : digest s₀ s = chainDigest j V

/-- One iteration. -/
theorem iter_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : ChainInv s₀ e V j s) (hl : 32 + 32 * j + 32 ≤ ol s₀) (hl' : 32 + 32 * (j + 1) < ol s₀) :
    WP isa (.seq (.block [.mov .r1 (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft)))) s
      fun t => ChainInv s₀ e V (j + 1) t ∧
        isa.eval .eq t = some (decide (ol s₀ - (32 + 32 * (j + 1)) ≤ 64)) := by
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : Keeps (scr s₀) (sp₀ s₀) s s₁ := Keeps.same (fun r hr => u₁.other r (by
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.sp u₁.mem u₁.rd u₁.wr
  have b₁ := h.body.keeps hp k₁
  refine WP.seq ((next_ok (b₁.ctx hp) (n := 64) u₁.gpr (by decide) (by decide)).mono
    fun s₂ ⟨d₂, k₂⟩ => ?_)
  have K₂ := k₁.trans k₂
  have b₂ := h.body.keeps hp K₂
  have o₂ := h.out.keeps hp K₂
  have hlen := chainOut_length hV j
  refine WP.seq ((emit_ok hp b₂ o₂ (by rw [hlen]; exact hl)).mono fun s₃ ⟨b₃, e₃, o₃, d₃⟩ => ?_)
  have dg : digest s₀ s₂ = chainDigest (j + 1) V := by
    rw [chainDigest_succ', ← h.digest, Proof.Argon2.H_stream,
      List.take_of_length_le (by rw [finalHash_length])]
    rw [u₁.mem] at d₂
    exact d₂
  have xs₃ : chainOut V j ++ (digest s₀ s₂).take 32 = chainOut V (j + 1) := by
    rw [dg, chainDigest_succ', chainOut, chainOut, chainPrefixes_succ', List.append_assoc]
  rw [xs₃] at o₃
  refine (cmp_ok o₃ (by rw [chainOut_length hV]; exact hl')).mono fun t ⟨cf, k, m⟩ =>
    ⟨⟨b₃.keeps hp k, ?_, o₃.keeps hp k, ?_⟩, ?_⟩
  · rw [k.gpr _ (by decide), e₃, K₂.gpr _ (by decide), h.r11]
  · show bytesAt _ _ _ = _
    rw [m]
    exact d₃.trans dg
  · rw [cf, chainOut_length hV]

/-- The chain: iterations while more than 64 bytes are left. -/
theorem chain_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : ChainInv s₀ e V j s) (hl : 65 ≤ ol s₀ - (32 + 32 * j)) :
    WP isa chain s fun t => ∃ j', ChainInv s₀ e V j' t ∧ 33 ≤ ol s₀ - (32 + 32 * j') ∧
      ol s₀ - (32 + 32 * j') ≤ 64 ∧ 32 + 32 * j' ≤ ol s₀ := by
  unfold chain
  refine WP.loop (M := isa) (fun (m : Nat) (t : State) => ∃ j', m = ol s₀ - (32 + 32 * j') ∧
    ChainInv s₀ e V j' t ∧ 65 ≤ m) ?_ (ol s₀ - (32 + 32 * j)) s ⟨j, rfl, h, hl⟩
  rintro m t ⟨j', rfl, hi, hm⟩
  refine (iter_ok hp hV hi (by omega_arith) (by omega_arith)).mono fun u ⟨hu, cf⟩ => ?_
  have cf' : isa.eval .ne u = some (!decide (ol s₀ - (32 + 32 * (j' + 1)) ≤ 64)) := by
    have cf2 : VG.Arm.eval .eq u = _ := cf
    show VG.Arm.eval .ne u = _
    rw [MdStream.Arm.eval_eq, Option.some.injEq] at cf2
    rw [MdStream.Arm.eval_ne, cf2]
  by_cases hc : ol s₀ - (32 + 32 * (j' + 1)) ≤ 64
  · refine .inl ⟨by rw [cf']; simp [hc], j' + 1, hu, by omega_arith, by omega_arith, by omega_arith⟩
  · refine .inr ⟨by rw [cf']; simp [hc], _, by omega_arith, j' + 1, rfl, hu, by omega_arith⟩

/-- What the chain leaves: the output after `j` iterations and the last hash. -/
def Extended (s₀ : State) (e : BitVec 32) (V : List Byte) (t : State) : Prop :=
  ∃ j, Body s₀ t ∧ t.gpr .r11 = e ∧ Out s₀ t (chainOut V j) ∧
    (digest s₀ t).take (ol s₀ - (32 + 32 * j)) =
      Spec.Argon2.H (ol s₀ - (32 + 32 * j)) (chainDigest j V) ∧
    33 ≤ ol s₀ - (32 + 32 * j) ∧ ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀

theorem extend_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) (hol : 65 ≤ ol s₀) :
    WP isa extendDigest s (Extended s₀ (s.gpr .r11) (digest s₀ s)) := by
  have hV : (digest s₀ s).length = 64 := by simp [digest, bytesAt]
  unfold extendDigest
  refine WP.seq ((emit_ok hp b o (by simp only [List.length_nil]; omega_arith)).mono
    fun s₁ ⟨b₁, e₁, o₁, d₁⟩ => ?_)
  rw [List.nil_append, show (digest s₀ s).take 32 = chainOut (digest s₀ s) 0 by
    simp [chainOut, chainPrefixes]] at o₁
  have i₁ : ChainInv s₀ (s.gpr .r11) (digest s₀ s) 0 s₁ := ⟨b₁, e₁, o₁, d₁⟩
  refine WP.seq ((cmp_ok o₁ (by rw [chainOut_length hV]; omega_arith)).mono fun s₂ ⟨cf₂, k₂, m₂⟩ => ?_)
  rw [chainOut_length hV] at cf₂
  have i₂ : ChainInv s₀ (s.gpr .r11) (digest s₀ s) 0 s₂ :=
    ⟨b₁.keeps hp k₂, (k₂.gpr _ (by decide)).trans e₁, o₁.keeps hp k₂,
      by show bytesAt _ _ _ = _; rw [m₂]; exact d₁⟩
  have hIte : WP isa (.ite .eq (.block []) chain) s₂ fun t => ∃ j, ChainInv s₀ (s.gpr .r11) (digest s₀ s) j t ∧
      33 ≤ ol s₀ - (32 + 32 * j) ∧ ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀ := by
    refine WP.ite (decide (ol s₀ - (32 + 32 * 0) ≤ 64)) cf₂ (fun h => WP.block_nil ⟨0, i₂, ?_⟩)
      (fun h => (chain_ok hp hV i₂ ?_).mono fun t h => h)
    · simp only [decide_eq_true_eq] at h; omega_arith
    · simp only [decide_eq_false_iff_not] at h; omega_arith
  refine WP.seq (hIte.mono fun s₃ ⟨j, i₃, l₁, l₂, l₃⟩ => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_)
  have k₄ : Keeps (scr s₀) (sp₀ s₀) s₃ s₄ := Keeps.same (fun r hr => u₄.other r (by
    simp only [kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₄.sp u₄.mem u₄.rd u₄.wr
  have b₄ := i₃.body.keeps hp k₄
  have r1₄ : s₄.gpr .r1 = BitVec.ofNat 32 (ol s₀ - (32 + 32 * j)) := by
    rw [u₄.gpr, i₃.out.left, chainOut_length hV]
  refine (next_ok (b₄.ctx hp) r1₄ (by omega_arith) l₂).mono fun t ⟨d, k⟩ => ?_
  have K := k₄.trans k
  refine ⟨j, i₃.body.keeps hp K, by rw [K.gpr _ (by decide), i₃.r11], i₃.out.keeps hp K, ?_, l₁, l₂, l₃⟩
  rw [Proof.Argon2.H_stream, ← i₃.digest]
  rw [u₄.mem] at d
  exact congrArg (List.take _) d

/-- `finishOutput` writes H′ of the input `I` from its first digest. -/
theorem finish_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) {I : List Byte}
    (hd : (digest s₀ s).take (min (ol s₀) 64) =
      Spec.Argon2.H (min (ol s₀) 64) (Spec.Argon2.le32 (ol s₀) ++ I)) :
    WP isa finishOutput s fun t => Body s₀ t ∧ t.gpr .r11 = s.gpr .r11 ∧
      bytesAt t.mem (State.addr (op s₀)) (ol s₀) = Spec.Argon2.hPrime (ol s₀) I := by
  have hpos := hp.ol_pos
  have hV : (digest s₀ s).length = 64 := by simp [digest, bytesAt]
  unfold finishOutput
  refine WP.seq ((cmp_ok o (by simp only [List.length_nil]; omega_arith)).mono fun s₁ ⟨cf₁, k₁, m₁⟩ => ?_)
  simp only [List.length_nil, Nat.sub_zero] at cf₁
  have b₁ := b.keeps hp k₁
  have o₁ := o.keeps hp k₁
  have d₁ : digest s₀ s₁ = digest s₀ s := by show bytesAt _ _ _ = _; rw [m₁]
  have hIte : WP isa (.ite .eq (.block []) extendDigest) s₁ fun t => Body s₀ t ∧ t.gpr .r11 = s.gpr .r11 ∧
      ∃ xs, Out s₀ t xs ∧ xs.length < ol s₀ ∧ ol s₀ - xs.length ≤ 64 ∧
        xs ++ (digest s₀ t).take (ol s₀ - xs.length) = Spec.Argon2.hPrime (ol s₀) I := by
    refine WP.ite (decide (ol s₀ ≤ 64)) cf₁ (fun h => WP.block_nil ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      refine ⟨b₁, k₁.gpr _ (by decide), [], o₁, by simp only [List.length_nil]; omega_arith,
        by simp only [List.length_nil]; omega_arith, ?_⟩
      rw [Nat.min_eq_left (by omega_arith)] at hd
      rw [List.nil_append, List.length_nil, Nat.sub_zero, d₁, hd]
      simp only [Spec.Argon2.hPrime, eq_true (by omega_arith : ol s₀ ≤ 64), ite_true]
    · simp only [decide_eq_false_iff_not] at h
      refine (extend_ok hp b₁ o₁ (by omega_arith)).mono fun t ⟨j, bt, et, ot, dt, l₁, l₂, l₃⟩ =>
        ⟨bt, et.trans (k₁.gpr _ (by decide)), _, ot, ?_, ?_, ?_⟩
      · rw [chainOut_length (by rw [d₁]; exact hV)]; omega_arith
      · rw [chainOut_length (by rw [d₁]; exact hV)]; omega_arith
      · have V₁ : digest s₀ s₁ = Spec.Argon2.H 64 (Spec.Argon2.le32 (ol s₀) ++ I) := by
          rw [d₁, ← List.take_of_length_le (l := digest s₀ s) (i := 64) (by rw [hV]),
            ← Nat.min_eq_right (by omega_arith : 64 ≤ ol s₀), hd]
        rw [chainOut_length (by rw [d₁]; exact hV), dt, chainOut, ← Proof.Argon2.longHash_chain, V₁]
        have hr : (ol s₀ + 31) / 32 - 2 = j + 1 := by omega_arith
        simp only [Spec.Argon2.hPrime, eq_false (by omega_arith : ¬ ol s₀ ≤ 64), ite_false]
        rw [hr, show ol s₀ - 32 * (j + 1) = ol s₀ - (32 + 32 * j) by omega_arith]
  refine WP.seq (hIte.mono fun s₂ ⟨b₂, e₂, xs, o₂, l₁, l₂, h₂⟩ => ?_)
  refine (copyRemaining_ok hp b₂ o₂ l₁ l₂).mono fun t ⟨bt, et, ht⟩ => ⟨bt, et.trans e₂, ?_⟩
  rw [ht, h₂]

end

end VG.Proof.Argon2.Arm.HPrime
