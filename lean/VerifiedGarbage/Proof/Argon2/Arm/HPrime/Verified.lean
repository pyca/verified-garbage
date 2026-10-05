import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Argon2.Arm.Push
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Impl.Argon2.Arm.HPrime
import VerifiedGarbage.Proof.Blake2.Arm.Blake2b
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Argon2.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.HPrime.Contract`. -/
section

/-!
# Argon2 H′ on ARMv7: the contract of the proof

`hPrimeArm`: `vg_argon2_hprime(input = r0, input_len = r1, out = r2,
out_len = r3, scratch = [sp])` with its stack argument only read;
`Spec.Argon2.hPrimeContract`, which lets the code write it, is reached by
narrowing. H′ uses the 32 bytes of stack below the stack pointer: a call of
`vg_blake2b_update` pushes four words, and `update` itself uses 16 bytes.
-/

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
  post s s' := VG.Spec.Blake2.bytesAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
    Spec.Argon2.hPrime (s.gpr .r3).toNat (VG.Spec.Blake2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

section
variable (s₀ : VG.Arm.State)

abbrev inp : BitVec 32 := s₀.gpr .r0
abbrev inl : Nat := (s₀.gpr .r1).toNat
abbrev op : BitVec 32 := s₀.gpr .r2
abbrev ol : Nat := (s₀.gpr .r3).toNat
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev sp₀ : BitVec 32 := s₀.sp
/-- `scratch`, as an address. -/
abbrev P : Addr := State.addr (VG.Proof.Argon2.Arm.HPrime.scr s₀)
abbrev inR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.HPrime.inp s₀), VG.Proof.Argon2.Arm.HPrime.inl s₀⟩
abbrev outR : Region := ⟨State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀), VG.Proof.Argon2.Arm.HPrime.ol s₀⟩
abbrev scrR : Region := ⟨VG.Proof.Argon2.Arm.HPrime.P s₀, 16384⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
abbrev stk : Region := stkR (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) 32

end

structure Pre (s₀ : VG.Arm.State) : Prop where
  rd : s₀.rd = [VG.Proof.Argon2.Arm.HPrime.inR s₀, VG.Proof.Argon2.Arm.HPrime.argR s₀]
  wr : s₀.wr = [VG.Proof.Argon2.Arm.HPrime.outR s₀, VG.Proof.Argon2.Arm.HPrime.scrR s₀]
  in_scr : (VG.Proof.Argon2.Arm.HPrime.inR s₀).Disjoint (VG.Proof.Argon2.Arm.HPrime.scrR s₀)
  out_scr : (VG.Proof.Argon2.Arm.HPrime.outR s₀).Disjoint (VG.Proof.Argon2.Arm.HPrime.scrR s₀)
  arg_out : (VG.Proof.Argon2.Arm.HPrime.argR s₀).Disjoint (VG.Proof.Argon2.Arm.HPrime.outR s₀)
  arg_scr : (VG.Proof.Argon2.Arm.HPrime.argR s₀).Disjoint (VG.Proof.Argon2.Arm.HPrime.scrR s₀)
  stk_in : (VG.Proof.Argon2.Arm.HPrime.stk s₀).Disjoint (VG.Proof.Argon2.Arm.HPrime.inR s₀)
  stk_out : (VG.Proof.Argon2.Arm.HPrime.stk s₀).Disjoint (VG.Proof.Argon2.Arm.HPrime.outR s₀)
  stk_scr : (VG.Proof.Argon2.Arm.HPrime.stk s₀).Disjoint (VG.Proof.Argon2.Arm.HPrime.scrR s₀)
  in_fits : (VG.Proof.Argon2.Arm.HPrime.inp s₀).toNat + VG.Proof.Argon2.Arm.HPrime.inl s₀ ≤ 2 ^ 32
  out_fits : (VG.Proof.Argon2.Arm.HPrime.op s₀).toNat + VG.Proof.Argon2.Arm.HPrime.ol s₀ ≤ 2 ^ 32
  scr_fits : (VG.Proof.Argon2.Arm.HPrime.scr s₀).toNat + 16384 ≤ 2 ^ 32
  sp_lo : 32 ≤ (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀).toNat
  sp_hi : (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀).toNat + 4 ≤ 2 ^ 32
  ol_pos : 1 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀

theorem pre_of (s₀ : VG.Arm.State) (h : hPrimeArm.pre s₀) : VG.Proof.Argon2.Arm.HPrime.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- `[scratch + d]`, as the code addresses it. -/
theorem scr_addr {s₀ : VG.Arm.State} (hp : VG.Proof.Argon2.Arm.HPrime.Pre s₀) {d : Nat} (hd : d < 16384) :
    State.addr (VG.Proof.Argon2.Arm.HPrime.scr s₀ + BitVec.ofNat 32 d) = VG.Proof.Argon2.Arm.HPrime.P s₀ + BitVec.ofNat 64 d := VG.Arm.addr_add (by have := hp.scr_fits; omega)

end VG.Proof.Argon2.Arm.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.HPrime.Calls`. -/
section

/-!
# Argon2 H′ on ARMv7: the calls of the BLAKE2b functions

`init_ok`, `update_ok`, `finalize_ok`: H′'s macros (`Impl.Argon2.Arm.HPrime`)
call the ARMv7 BLAKE2b streaming functions with the state at `scratch` (in
`r4`, at `B`), their scratch at `scratch + 192`, and the stack below the
stack pointer (`SP`). Each is stated for any `B` and `SP`, so that the
derivation can use them too: they write only the state, their scratch, the
digest (`finalize`) and the 32 bytes below `SP`, and keep `r4`–`r11`.
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Arm.FrameStack
open VG.Impl.Argon2.Arm.HPrime (init update finalize initCode updateCode finalizeCode initName updateName
  finalizeName)
open VG.Proof.Blake2 (initArm updateArm finalizeArm countArm)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_reg op2_imm)

/-! ## The callees -/

theorem init_correct : ∀ s, (VG.Proof.Blake2.initArm b).pre s →
    ∃ t s', Exec isa initCode s t s' ∧ abiPreserved s s' ∧ (VG.Proof.Blake2.initArm b).post s s' :=
  (Proof.Blake2.Arm.Stream.init_verified Proof.Blake2.Arm.Stream.okB Proof.Blake2.Arm.Stream.init_check_b
    (Contract.Implies.refl Proof.Blake2.Arm.Stream.initB_implies.sat_left)).1

theorem init_ct : ConstantTime isa (VG.Proof.Blake2.initArm b).pre (VG.Proof.Blake2.initArm b).pub initCode :=
  (Proof.Blake2.Arm.Stream.init_verified Proof.Blake2.Arm.Stream.okB Proof.Blake2.Arm.Stream.init_check_b
    (Contract.Implies.refl Proof.Blake2.Arm.Stream.initB_implies.sat_left)).2.1

theorem update_v : Verified Arm.target updateCode (VG.Proof.Blake2.updateArm b) :=
  Proof.Blake2.Arm.Stream.update_verified Proof.Blake2.Arm.Stream.okB Proof.Blake2.ArmB.calleeB
    (Contract.Implies.refl Proof.Blake2.Arm.Stream.updateB_implies.sat_left)

theorem finalize_v : Verified Arm.target finalizeCode (VG.Proof.Blake2.finalizeArm b) :=
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

theorem Ctx.of_regs {B SP : BitVec 32} {s t : State} (h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) (hb : t.gpr .r4 = s.gpr .r4)
    (hs : t.sp = s.sp) (hw : t.wr = s.wr) : VG.Proof.Argon2.Arm.HPrime.Ctx B SP t :=
  ⟨hb.trans h.r4, hs.trans h.sp, h.fits, h.lo, hw ▸ h.wr, h.stk⟩

section
variable {B SP : BitVec 32} {s : State}

theorem Ctx.sub (_h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {d n : Nat} (hd : d + n ≤ 832) :
    Region.Sub ⟨State.addr B + BitVec.ofNat 64 d, n⟩ ⟨State.addr B, 832⟩ :=
  Offset.sub_base _ hd

theorem Ctx.cov (h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {d n : Nat} (hd : d + n ≤ 832) :
    Covers [⟨State.addr B + BitVec.ofNat 64 d, n⟩] s.wr :=
  (Covers.of_sub (rs' := [⟨State.addr B, 832⟩]) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, d, rfl, hd⟩).trans h.wr

theorem Ctx.cov0 (h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {n : Nat} (hn : n ≤ 832) : Covers [⟨State.addr B, n⟩] s.wr :=
  (Covers.of_sub (rs' := [⟨State.addr B, 832⟩]) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, 0, by simp, by simp; omega⟩).trans h.wr

theorem Ctx.stk_sub (h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {d n : Nat} (hd : d + n ≤ 832) :
    (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 d, n⟩ :=
  h.stk.sub_right (h.sub hd)

theorem Ctx.stk0 (h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {n : Nat} (hn : n ≤ 832) :
    (stkR SP 32).Disjoint ⟨State.addr B, n⟩ :=
  h.stk.sub_right (Region.sub_prefix hn)

theorem Ctx.addr_add (h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {d : Nat} (hd : d < 832) :
    State.addr (B + BitVec.ofNat 32 d) = State.addr B + BitVec.ofNat 64 d :=
  VG.Arm.addr_add (by have := h.fits; omega)

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
  have := stkR_inner (sp := SP) (a := 16) (k := 0) (b := 32) (by omega) hlo
  intro x hx
  refine stkR_sub (a := 16) (b := 32) (sp := SP) (by omega) hlo x ?_
  have e : State.addr (SP - BitVec.ofNat 32 16) = State.addr SP - BitVec.ofNat 64 16 := addr_sub' (by omega)
  simp only [Region.Contains] at hx ⊢
  rw [e] at hx; omega

theorem stk_args8 {SP : BitVec 32} (hlo : 32 ≤ SP.toNat) {k : Nat} (hk : k ≤ 8) :
    Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 8), k⟩ (stkR SP 32) := by
  intro x hx
  refine stkR_sub (a := 8) (b := 32) (sp := SP) (by omega) hlo x ?_
  have e : State.addr (SP - BitVec.ofNat 32 8) = State.addr SP - BitVec.ofNat 64 8 := addr_sub' (by omega)
  simp only [Region.Contains] at hx ⊢
  rw [e] at hx; omega

/-- The callee's 16 bytes of stack, below its stack pointer `SP - k`. -/
theorem stk_callee {SP : BitVec 32} (hlo : 32 ≤ SP.toNat) {k : Nat} (hk : k ≤ 16) :
    Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 k) - 16, 16⟩ (stkR SP 32) :=
  stkR_inner (sp := SP) (a := 16) (k := k) (b := 32) (by omega) hlo

/-! ## `init` -/

theorem keyBlock_nil (m : Mem) (p : Addr) : keyBlock 64 (bytesAt m p 0) = [] := rfl

/-- The regions `init` is given. -/
abbrev initRd (B : BitVec 32) : List Region := [⟨State.addr B, 0⟩]
abbrev initWr (B : BitVec 32) : List Region := [⟨State.addr B, 192⟩]

/-- `init`'s precondition, from the arguments in `r0`–`r3`. -/
theorem init_pre {B SP : BitVec 32} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {n : Nat} (hn : s.gpr .r1 = BitVec.ofNat 32 n)
    (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (h0 : s.gpr .r0 = B) (h2 : s.gpr .r2 = B) (h3 : s.gpr .r3 = 0) :
    (VG.Proof.Blake2.initArm b).pre (s.callEntry.withRegions (VG.Proof.Argon2.Arm.HPrime.initRd B) (VG.Proof.Argon2.Arm.HPrime.initWr B)) ∧
      Covers (VG.Proof.Argon2.Arm.HPrime.initRd B ++ VG.Proof.Argon2.Arm.HPrime.initWr B) (s.rd ++ s.wr) ∧ Covers (VG.Proof.Argon2.Arm.HPrime.initWr B) s.wr := by
  refine ⟨?_, ?_, h.cov0 (by decide)⟩
  · simp only [VG.Proof.Blake2.initArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      Proof.Blake2.Arm.Stream.ce0, Proof.Blake2.Arm.Stream.ce1, Proof.Blake2.Arm.Stream.ce2,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), h0, hn, h2, h3, Proof.Blake2.bufOff, blockBytes]
    have hf := h.fits
    refine ⟨rfl, trivial, VG.Proof.Argon2.Arm.HPrime.disjoint_nil _ _, by omega, by simp; omega, ?_, ?_, by simp⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn₁
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn₂
  · refine Covers.append_left (Covers.cons ?_ Covers.nil) ?_
    · intro a k ⟨r, hr, hc⟩
      simp only [List.mem_singleton] at hr; subst hr
      obtain ⟨r', hr', hc'⟩ := h.wr a k ⟨_, List.mem_singleton_self _, by
        simp only [Region.Contains] at hc ⊢; omega⟩
      exact ⟨r', List.mem_append_right _ hr', hc'⟩
    · exact ((h.cov0 (n := 192) (by decide)).trans fun a k ⟨r', hr', hc'⟩ =>
        ⟨r', List.mem_append_right _ hr', hc'⟩)

theorem init_ok {B SP : BitVec 32} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {n : Nat} (hn : s.gpr .r1 = BitVec.ofNat 32 n)
    (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa VG.Impl.Argon2.Arm.HPrime.init s fun t => Repr b (Spec.Blake2.init b n 0) t.mem (State.addr B) [] ∧
      (∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨State.addr B, 192⟩] s.mem t.mem := by
  unfold Impl.Argon2.Arm.HPrime.init
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_)
  have o₃ : ∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s.gpr r := fun r h0 h2 h3 => by
    rw [u₃.other _ h3, u₂.other _ h2, u₁.other _ h0]
  have r0 : s₃.gpr .r0 = B := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.r4]
  have r1 : s₃.gpr .r1 = BitVec.ofNat 32 n := by rw [o₃ _ (by decide) (by decide) (by decide), hn]
  have r2 : s₃.gpr .r2 = B := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.r4]
  have r3 : s₃.gpr .r3 = 0 := u₃.gpr
  have w₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have sp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  have c₃ : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s₃ := h.of_regs (o₃ _ (by decide) (by decide) (by decide)) sp₃ w₃
  obtain ⟨pre, cv, cw⟩ := VG.Proof.Argon2.Arm.HPrime.init_pre c₃ r1 hn₁ hn₂ r0 r2 r3
  refine WP.call (k := VG.Proof.Blake2.initArm b) VG.Proof.Argon2.Arm.HPrime.init_correct pre cv cw fun t hrd hwr hsp hf hcs _ hpost => ?_
  simp only [VG.Proof.Blake2.initArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    Proof.Blake2.Arm.Stream.ce0, Proof.Blake2.Arm.Stream.ce1, Proof.Blake2.Arm.Stream.ce2,
    State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), r0, r1, r2, r3] at hpost
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega)] at hpost
  refine ⟨by simpa [VG.Proof.Argon2.Arm.HPrime.keyBlock_nil] using hpost, fun r hr hl => (hcs r hr hl).trans ?_, hrd.trans rd₃, hwr.trans w₃,
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
  have hb : ∀ i < 192, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
    fun i hi => hf.bytes (R := ⟨p, 192⟩) hd (by simp) hi
  obtain ⟨h1, h2⟩ := h
  have hl := Proof.Blake2.bufLen_le (w := 64) (by decide) d.length
  have hs := Proof.Blake2.sub_bufLen (w := 64) d
  have hs' := Proof.Blake2.bufLen_le_self (w := 64) d.length
  refine ⟨?_, ?_⟩
  · rw [Proof.Blake2.stateAt_congr (fun i hi => hb i (by simp only [Proof.Blake2.bufOff] at hi; omega))]
    exact h1
  · rw [← h2]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have hbb : blockBytes 64 = 128 := rfl
    rw [hbb] at hl hs hi
    exact hb _ (by omega)

/-! ## `update` -/

/-- The registers `update`'s frame pushes: the data, its length, the callees'
scratch, and `lr` for alignment. -/
abbrev upd4 : List Reg := [.r9, .r10, .r12, .lr]

/-- The regions `update` is given. -/
abbrev updRd (D : BitVec 32) (L : Nat) (SP : BitVec 32) : List Region :=
  [⟨State.addr D, L⟩, ⟨State.addr (SP - BitVec.ofNat 32 16), 12⟩]
abbrev updWr (B : BitVec 32) : List Region := [⟨State.addr B, 192⟩, ⟨State.addr B + BitVec.ofNat 64 192, 576⟩]

/-- `update`'s precondition, after its frame's push. -/
theorem update_pre {B SP : BitVec 32} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {D : BitVec 32} {L : Nat}
    (hD : s.gpr .r9 = D) (hL : (s.gpr .r10).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨State.addr D, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨State.addr D, L⟩ ⟨State.addr B, 768⟩)
    (hDk : (stkR SP 32).Disjoint ⟨State.addr D, L⟩) (h0 : s.gpr .r0 = B) (h12 : s.gpr .r12 = B + 192) :
    (VG.Proof.Blake2.updateArm b).pre ((pushed VG.Proof.Argon2.Arm.HPrime.upd4 s).callEntry.withRegions (VG.Proof.Argon2.Arm.HPrime.updRd D L SP) (VG.Proof.Argon2.Arm.HPrime.updWr B)) ∧
      Covers (VG.Proof.Argon2.Arm.HPrime.updRd D L SP ++ VG.Proof.Argon2.Arm.HPrime.updWr B) ((pushed VG.Proof.Argon2.Arm.HPrime.upd4 s).rd ++ (pushed VG.Proof.Argon2.Arm.HPrime.upd4 s).wr) ∧
      Covers (VG.Proof.Argon2.Arm.HPrime.updWr B) (pushed VG.Proof.Argon2.Arm.HPrime.upd4 s).wr := by
  have hlo := h.lo
  have hfit := h.fits
  have e192 : State.addr (B + 192) = State.addr B + BitVec.ofNat 64 192 := h.addr_add (by decide)
  have hn : 4 * upd4.length ≤ s.sp.toNat := by rw [h.sp]; simp only [List.length_cons, List.length_nil]; omega
  have a0 : ∀ {rd wr}, stackArg ((pushed VG.Proof.Argon2.Arm.HPrime.upd4 s).callEntry.withRegions rd wr) 0 = D := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [hD]
  have a1 : ∀ {rd wr}, (stackArg ((pushed VG.Proof.Argon2.Arm.HPrime.upd4 s).callEntry.withRegions rd wr) 1).toNat = L := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [hL]
  have a2 : ∀ {rd wr}, stackArg ((pushed VG.Proof.Argon2.Arm.HPrime.upd4 s).callEntry.withRegions rd wr) 2 = B + 192 := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [h12]
  have eA : ∀ {rd wr}, stackArgAddr ((pushed VG.Proof.Argon2.Arm.HPrime.upd4 s).callEntry.withRegions rd wr) 0 =
      State.addr (SP - BitVec.ofNat 32 16) := by
    intro rd wr; rw [pushed_argAddr hn, h.sp, addr_sub' (by omega)]; rfl
  have eSp : ∀ {rd wr}, ((pushed VG.Proof.Argon2.Arm.HPrime.upd4 s).callEntry.withRegions rd wr).sp = SP - BitVec.ofNat 32 16 := by
    intro rd wr; simp [pushed_sp, h.sp]
  have stR : (stkR SP 32).Disjoint ⟨State.addr B, 192⟩ := h.stk0 (by decide)
  have scR : (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 192, 576⟩ := h.stk_sub (by decide)
  have argS : Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 16), 12⟩ (stkR SP 32) := VG.Proof.Argon2.Arm.HPrime.stk_args hlo (by decide)
  have calS : Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 16) - 16, 16⟩ (stkR SP 32) :=
    VG.Proof.Argon2.Arm.HPrime.stk_callee hlo (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [VG.Proof.Blake2.updateArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      Proof.Blake2.Arm.Stream.ce0, pushed_gpr, a0, a1, a2, eA, eSp, e192, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, Proof.Blake2.Arm.Stream.below, h0]
    refine ⟨trivial, trivial, Offset.base_disjoint _ (by decide) (by decide),
      hDs.sub_right (Region.sub_prefix (by decide)), hDs.sub_right (Offset.sub_base _ (by decide)),
      stR.sub_left argS, scR.sub_left argS, ?_, ?_, ?_, by omega, hDfit, ?_, ?_, ?_⟩
    · exact stR.sub_left calS
    · exact hDk.sub_left calS
    · exact scR.sub_left calS
    · rw [show (B + 192).toNat = B.toNat + 192 by
        rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega]; omega
    · rw [sub_toNat' (by omega)]; omega
    · rw [sub_toNat' (by omega)]; have := SP.isLt; omega
  · rw [pushed_rd, pushed_wr]
    refine Covers.append_left (Covers.cons (VG.Proof.Argon2.Arm.HPrime.covers_ins _ hDc) (Covers.cons ?_ Covers.nil))
      (VG.Proof.Argon2.Arm.HPrime.covers_ins _ (Covers.right ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))))
    intro a k ⟨r, hr, hc'⟩
    simp only [List.mem_singleton] at hr; subst hr
    refine InRegions_append_cons.mpr (.inl ?_)
    simp only [List.length_cons, List.length_nil, h.sp, Region.Contains, Nat.zero_add, Nat.reduceAdd,
      Nat.reduceMul] at hc' ⊢
    rw [addr_sub' (by omega)] at hc' ⊢; omega
  · rw [pushed_wr]
    exact VG.Proof.Argon2.Arm.HPrime.covers_cons _ ((h.cov0 (by decide)).pair (h.cov (d := 192) (by decide)))

/-- `update` hashes the `L` bytes at `D` (in `r9` and `r10`) into the state at
`B`, whose byte count is in `r3:r2`. -/
theorem update_ok {B SP : BitVec 32} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {D : BitVec 32} {L : Nat}
    (hD : s.gpr .r9 = D) (hL : (s.gpr .r10).toNat = L) (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDc : Covers [⟨State.addr D, L⟩] (s.rd ++ s.wr))
    (hDs : Region.Disjoint ⟨State.addr D, L⟩ ⟨State.addr B, 768⟩)
    (hDk : (stkR SP 32).Disjoint ⟨State.addr D, L⟩)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (State.addr B) d)
    (hc : s.gpr .r3 ++ s.gpr .r2 = BitVec.ofNat 64 d.length) (hlen : d.length + L < 2 ^ 64) :
    WP isa VG.Impl.Argon2.Arm.HPrime.update s fun t => Repr b h0 t.mem (State.addr B) (d ++ bytesAt s.mem (State.addr D) L) ∧
      (∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨State.addr B, 768⟩, stkR SP 32] s.mem t.mem := by
  unfold VG.Impl.Argon2.Arm.HPrime.update
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_)
  have hlo := h.lo
  have o₂ : ∀ r, r ≠ .r0 → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r h0 h12 => by
    rw [u₂.other _ h12, u₁.other _ h0]
  have sp₂ : s₂.sp = SP := by rw [u₂.sp, u₁.sp, h.sp]
  have w₂ : s₂.wr = s.wr := u₂.wr.trans u₁.wr
  have r₂ : s₂.rd = s.rd := u₂.rd.trans u₁.rd
  have m₂ : s₂.mem = s.mem := u₂.mem.trans u₁.mem
  have c₂ : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s₂ := h.of_regs (o₂ _ (by decide) (by decide)) (u₂.sp.trans u₁.sp) w₂
  have hn : 4 * upd4.length ≤ s₂.sp.toNat := by rw [sp₂]; simp only [List.length_cons, List.length_nil]; omega
  obtain ⟨pre, cv, cw⟩ := VG.Proof.Argon2.Arm.HPrime.update_pre c₂ (by rw [o₂ _ (by decide) (by decide), hD])
    (by rw [o₂ _ (by decide) (by decide), hL]) hDfit (by rw [r₂, w₂]; exact hDc) hDs hDk
    (by rw [u₂.other _ (by decide), u₁.gpr, h.r4]) (by rw [u₂.gpr, u₁.other _ (by decide), h.r4])
  have stR : (stkR SP 32).Disjoint ⟨State.addr B, 192⟩ := h.stk0 (by decide)
  refine frameCall_ok (rs := VG.Proof.Argon2.Arm.HPrime.upd4) (t := .r0) (by decide) (by decide) (by decide) (k := VG.Proof.Blake2.updateArm b)
    update_v.1 (K := 32) (by rw [VG.Proof.Argon2.Arm.HPrime.update_stack]; decide) (by rw [sp₂]; exact hlo) pre cv cw
    fun t af hpost => ?_
  have hpush : Frame [stkR SP 32] s₂.mem (pushed VG.Proof.Argon2.Arm.HPrime.upd4 s₂).mem :=
    (pushed_stk hn).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by rw [sp₂]; exact stkR_sub (by decide) hlo⟩
  have a0 : ∀ {rd wr}, stackArg ((pushed VG.Proof.Argon2.Arm.HPrime.upd4 s₂).callEntry.withRegions rd wr) 0 = D := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [o₂ .r9 (by decide) (by decide), hD]
  have a1 : ∀ {rd wr}, (stackArg ((pushed VG.Proof.Argon2.Arm.HPrime.upd4 s₂).callEntry.withRegions rd wr) 1).toNat = L := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [o₂ .r10 (by decide) (by decide), hL]
  simp only [VG.Proof.Blake2.updateArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    Proof.Blake2.Arm.Stream.ce0, pushed_gpr, u₂.other _ (by decide : Reg.r0 ≠ .r12), u₁.gpr, h.r4, a0, a1] at hpost
  have reprE : Repr b h0 (pushed VG.Proof.Argon2.Arm.HPrime.upd4 s₂).mem (State.addr B) d :=
    VG.Proof.Argon2.Arm.HPrime.repr_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact stR.symm) (m₂ ▸ repr)
  have countE : VG.Proof.Blake2.countArm ((pushed VG.Proof.Argon2.Arm.HPrime.upd4 s₂).callEntry.withRegions (VG.Proof.Argon2.Arm.HPrime.updRd D L SP) (VG.Proof.Argon2.Arm.HPrime.updWr B)) =
      BitVec.ofNat 64 d.length := by
    simp only [VG.Proof.Blake2.countArm, State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce2,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), pushed_gpr,
      o₂ .r2 (by decide) (by decide), o₂ .r3 (by decide) (by decide)]
    exact hc
  have dataE : bytesAt (pushed VG.Proof.Argon2.Arm.HPrime.upd4 s₂).mem (State.addr D) L = bytesAt s.mem (State.addr D) L := by
    rw [← m₂]
    exact Proof.Blake2.bytesAt_congr fun i hi =>
      hpush.bytes (R := ⟨State.addr D, L⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hDk.symm) (by simp; omega) hi
  have := hpost h0 d reprE countE (by omega)
  rw [dataE] at this
  refine ⟨by simpa [popped_mem] using this, fun r hr hl => (af.cs r hr hl).trans ?_,
    af.rd.trans r₂, af.wr.trans w₂, af.sp.trans (by rw [sp₂, h.sp]), ?_⟩
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
theorem finalize_pre {B SP : BitVec 32} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) (h0 : s.gpr .r0 = B)
    (h1 : s.gpr .r1 = B + 768) (h12 : s.gpr .r12 = B + 192) :
    (VG.Proof.Blake2.finalizeArm b).pre ((pushed VG.Proof.Argon2.Arm.HPrime.fin2 s).callEntry.withRegions (VG.Proof.Argon2.Arm.HPrime.finRd SP) (VG.Proof.Argon2.Arm.HPrime.finWr B)) ∧
      Covers (VG.Proof.Argon2.Arm.HPrime.finRd SP ++ VG.Proof.Argon2.Arm.HPrime.finWr B) ((pushed VG.Proof.Argon2.Arm.HPrime.fin2 s).rd ++ (pushed VG.Proof.Argon2.Arm.HPrime.fin2 s).wr) ∧
      Covers (VG.Proof.Argon2.Arm.HPrime.finWr B) (pushed VG.Proof.Argon2.Arm.HPrime.fin2 s).wr := by
  have hlo := h.lo
  have hfit := h.fits
  have e192 : State.addr (B + 192) = State.addr B + BitVec.ofNat 64 192 := h.addr_add (by decide)
  have e768 : State.addr (B + 768) = State.addr B + BitVec.ofNat 64 768 := h.addr_add (by decide)
  have hn : 4 * fin2.length ≤ s.sp.toNat := by rw [h.sp]; simp only [List.length_cons, List.length_nil]; omega
  have a0 : ∀ {rd wr}, stackArg ((pushed VG.Proof.Argon2.Arm.HPrime.fin2 s).callEntry.withRegions rd wr) 0 = B + 768 := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [h1]
  have a1 : ∀ {rd wr}, stackArg ((pushed VG.Proof.Argon2.Arm.HPrime.fin2 s).callEntry.withRegions rd wr) 1 = B + 192 := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [h12]
  have eA : ∀ {rd wr}, stackArgAddr ((pushed VG.Proof.Argon2.Arm.HPrime.fin2 s).callEntry.withRegions rd wr) 0 =
      State.addr (SP - BitVec.ofNat 32 8) := by
    intro rd wr; rw [pushed_argAddr hn, h.sp, addr_sub' (by omega)]; rfl
  have eSp : ∀ {rd wr}, ((pushed VG.Proof.Argon2.Arm.HPrime.fin2 s).callEntry.withRegions rd wr).sp = SP - BitVec.ofNat 32 8 := by
    intro rd wr; simp [pushed_sp, h.sp]
  have stR : (stkR SP 32).Disjoint ⟨State.addr B, 192⟩ := h.stk0 (by decide)
  have scR : (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 192, 576⟩ := h.stk_sub (by decide)
  have dgR : (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 768, 64⟩ := h.stk_sub (by decide)
  have argS : Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 8), 8⟩ (stkR SP 32) := VG.Proof.Argon2.Arm.HPrime.stk_args8 hlo (by decide)
  have calS : Region.Sub ⟨State.addr (SP - BitVec.ofNat 32 8) - 16, 16⟩ (stkR SP 32) :=
    VG.Proof.Argon2.Arm.HPrime.stk_callee hlo (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [VG.Proof.Blake2.finalizeArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      Proof.Blake2.Arm.Stream.ce0, pushed_gpr, a0, a1, eA, eSp, e192, e768, h0, Proof.Blake2.bufOff,
      blockBytes, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, Proof.Blake2.Arm.Stream.below]
    refine ⟨trivial, trivial, Offset.base_disjoint _ (by decide) (by decide),
      Offset.base_disjoint _ (by decide) (by decide), Offset.disjoint _ (by decide) (by decide) (by decide),
      stR.sub_left argS, dgR.sub_left argS, scR.sub_left argS, stR.sub_left calS, dgR.sub_left calS,
      scR.sub_left calS, by omega, ?_, ?_, ?_, ?_⟩
    · rw [show (B + 768).toNat = B.toNat + 768 by
        rw [BitVec.toNat_add, show (768 : BitVec 32).toNat = 768 from rfl]; omega]; omega
    · rw [show (B + 192).toNat = B.toNat + 192 by
        rw [BitVec.toNat_add, show (192 : BitVec 32).toNat = 192 from rfl]; omega]; omega
    · rw [sub_toNat' (by omega)]; omega
    · rw [sub_toNat' (by omega)]; have := SP.isLt; omega
  · rw [pushed_rd, pushed_wr]
    refine Covers.append_left (Covers.cons ?_ Covers.nil)
      (VG.Proof.Argon2.Arm.HPrime.covers_ins _ (Covers.right ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
        (h.cov (d := 192) (by decide))))))
    intro a k ⟨r, hr, hc'⟩
    simp only [List.mem_singleton] at hr; subst hr
    refine InRegions_append_cons.mpr (.inl ?_)
    simp only [List.length_cons, List.length_nil, h.sp, Region.Contains, Nat.zero_add, Nat.reduceAdd,
      Nat.reduceMul] at hc' ⊢
    rw [addr_sub' (by omega)] at hc' ⊢; omega
  · rw [pushed_wr]
    exact VG.Proof.Argon2.Arm.HPrime.covers_cons _ ((h.cov0 (by decide)).cons ((h.cov (d := 768) (by decide)).pair
      (h.cov (d := 192) (by decide))))

/-- `finalize` writes the hash of the data in the state at `B`, whose byte
count is in `r3:r2`, to `scratch[768, 832)`. -/
theorem finalize_ok {B SP : BitVec 32} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s)
    {h0 : HashValue 64} {d : List Byte} (repr : Repr b h0 s.mem (State.addr B) d)
    (hc : s.gpr .r3 ++ s.gpr .r2 = BitVec.ofNat 64 d.length) (hlen : d.length < 2 ^ 64) :
    WP isa VG.Impl.Argon2.Arm.HPrime.finalize s fun t => bytesAt t.mem (State.addr B + 768) 64 = finalHash b h0 d ∧
      (∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨State.addr B, 832⟩, stkR SP 32] s.mem t.mem := by
  unfold VG.Impl.Argon2.Arm.HPrime.finalize
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_)
  have hlo := h.lo
  have hfit := h.fits
  have o₃ : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h0 h1 h12 => by
    rw [u₃.other _ h12, u₂.other _ h1, u₁.other _ h0]
  have sp₃ : s₃.sp = SP := by rw [u₃.sp, u₂.sp, u₁.sp, h.sp]
  have w₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have r₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have e768 : State.addr (B + 768) = State.addr B + BitVec.ofNat 64 768 := h.addr_add (by decide)
  have hn : 4 * fin2.length ≤ s₃.sp.toNat := by rw [sp₃]; simp only [List.length_cons, List.length_nil]; omega
  have r0₃ : s₃.gpr .r0 = B := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.r4]
  have r1₃ : s₃.gpr .r1 = B + 768 := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.r4]
  have r12₃ : s₃.gpr .r12 = B + 192 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r4]
  have c₃ : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s₃ := h.of_regs (o₃ _ (by decide) (by decide) (by decide)) (u₃.sp.trans (u₂.sp.trans u₁.sp)) w₃
  obtain ⟨pre, cv, cw⟩ := VG.Proof.Argon2.Arm.HPrime.finalize_pre c₃ r0₃ r1₃ r12₃
  have stR : (stkR SP 32).Disjoint ⟨State.addr B, 192⟩ := h.stk0 (by decide)
  refine frameCall_ok (rs := VG.Proof.Argon2.Arm.HPrime.fin2) (t := .r0) (by decide) (by decide) (by decide) (k := VG.Proof.Blake2.finalizeArm b)
    finalize_v.1 (K := 32) (by rw [VG.Proof.Argon2.Arm.HPrime.finalize_stack]; decide) (by rw [sp₃]; exact hlo) pre cv cw
    fun t af hpost => ?_
  have hpush : Frame [stkR SP 32] s₃.mem (pushed VG.Proof.Argon2.Arm.HPrime.fin2 s₃).mem :=
    (pushed_stk hn).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by rw [sp₃]; exact stkR_sub (by decide) hlo⟩
  have a0 : ∀ {rd wr}, stackArg ((pushed VG.Proof.Argon2.Arm.HPrime.fin2 s₃).callEntry.withRegions rd wr) 0 = B + 768 := by
    intro rd wr; rw [pushed_arg hn (by decide)]; simp [r1₃]
  simp only [VG.Proof.Blake2.finalizeArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    Proof.Blake2.Arm.Stream.ce0, pushed_gpr, r0₃, a0, e768, Proof.Blake2.bufOff] at hpost
  have reprE : Repr b h0 (pushed VG.Proof.Argon2.Arm.HPrime.fin2 s₃).mem (State.addr B) d :=
    VG.Proof.Argon2.Arm.HPrime.repr_frame hpush (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact stR.symm) (m₃ ▸ repr)
  have countE : VG.Proof.Blake2.countArm ((pushed VG.Proof.Argon2.Arm.HPrime.fin2 s₃).callEntry.withRegions (VG.Proof.Argon2.Arm.HPrime.finRd SP) (VG.Proof.Argon2.Arm.HPrime.finWr B)) =
      BitVec.ofNat 64 d.length := by
    simp only [VG.Proof.Blake2.countArm, State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce2,
      State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), pushed_gpr,
      o₃ .r2 (by decide) (by decide) (by decide), o₃ .r3 (by decide) (by decide) (by decide)]
    exact hc
  refine ⟨by simpa [popped_mem] using hpost h0 d reprE hlen countE, fun r hr hl => (af.cs r hr hl).trans ?_,
    af.rd.trans r₃, af.wr.trans w₃, af.sp.trans (by rw [sp₃, h.sp]), ?_⟩
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

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.HPrime.Hash`. -/
section

/-!
# Argon2 H′ on ARMv7: hashing in `scratch`

What the hash macros keep (`Keeps`: `r4`–`r8`, `r11`, the stack pointer, the
permissions, and the memory outside `scratch[0, 832)` and the 32 bytes below
the stack pointer), and the hash of a fixed `scratch` buffer
(`absorbFixed_ok`) and of the 64-byte digest (`next_ok`).
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (init update finalize absorbFixed next)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_reg op2_imm)

/-- The registers the hash macros keep, that callers keep their values in. -/
abbrev kept : List Reg := [.r4, .r5, .r6, .r7, .r8, .r11]

/-- The registers the macros write are not kept. -/
theorem kept_ne : ∀ q ∈ VG.Proof.Argon2.Arm.HPrime.kept, q ≠ .r0 ∧ q ≠ .r1 ∧ q ≠ .r2 ∧ q ≠ .r3 ∧ q ≠ .r9 ∧ q ≠ .r10 ∧ q ≠ .r12 ∧
    q ≠ .lr := by decide

/-- What the hash macros keep. -/
structure Keeps (B SP : BitVec 32) (s t : State) : Prop where
  gpr : ∀ r ∈ VG.Proof.Argon2.Arm.HPrime.kept, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨State.addr B, 832⟩, stkR SP 32] s.mem t.mem

theorem Keeps.refl {B SP : BitVec 32} (s : State) : VG.Proof.Argon2.Arm.HPrime.Keeps B SP s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Keeps.trans {B SP : BitVec 32} {s t u : State} (h : VG.Proof.Argon2.Arm.HPrime.Keeps B SP s t) (h' : VG.Proof.Argon2.Arm.HPrime.Keeps B SP t u) :
    VG.Proof.Argon2.Arm.HPrime.Keeps B SP s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.sp.trans h.sp, h'.rd.trans h.rd, h'.wr.trans h.wr,
    h.frame.trans h'.frame⟩

theorem Keeps.r4 {B SP : BitVec 32} {s t : State} (h : VG.Proof.Argon2.Arm.HPrime.Keeps B SP s t) : t.gpr .r4 = s.gpr .r4 :=
  h.gpr _ (by decide)

theorem Keeps.ctx {B SP : BitVec 32} {s t : State} (h : VG.Proof.Argon2.Arm.HPrime.Keeps B SP s t) (c : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) : VG.Proof.Argon2.Arm.HPrime.Ctx B SP t :=
  c.of_regs h.r4 h.sp h.wr

/-- Steps that keep memory, the permissions, the stack pointer and `kept`. -/
theorem Keeps.same {B SP : BitVec 32} {s t : State} (hg : ∀ r ∈ VG.Proof.Argon2.Arm.HPrime.kept, t.gpr r = s.gpr r)
    (hs : t.sp = s.sp) (hm : t.mem = s.mem) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : VG.Proof.Argon2.Arm.HPrime.Keeps B SP s t :=
  ⟨hg, hs, hrd, hwr, hm ▸ Frame.refl _ _⟩

/-- Calls keep the callee-saved registers and write within the regions. -/
theorem Keeps.of_call {B SP : BitVec 32} {s t : State} (hr : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r)
    (hsp : t.sp = s.sp) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [(⟨State.addr B, 832⟩ : Region), stkR SP 32], Region.Sub r r') :
    VG.Proof.Argon2.Arm.HPrime.Keeps B SP s t :=
  ⟨fun r h => by
    have hk : r ∈ preserved ∧ r ≠ .lr := by
      simp only [VG.Proof.Argon2.Arm.HPrime.kept, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hr r hk.1 hk.2,
    hsp, hrd, hwr, hf.sub hs⟩

/-- Bytes outside `scratch[0, 832)` and the stack are kept. -/
theorem Keeps.bytes {B SP : BitVec 32} {s t : State} (h : VG.Proof.Argon2.Arm.HPrime.Keeps B SP s t) {R : Region}
    (hR : R.len ≤ 2 ^ 64) (h₁ : R.Disjoint ⟨State.addr B, 832⟩) (h₂ : R.Disjoint (stkR SP 32)) :
    bytesAt t.mem R.base R.len = bytesAt s.mem R.base R.len :=
  Proof.Blake2.bytesAt_congr fun i hi => h.frame.bytes (R := R) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂) hR hi

/-! ## Fixed buffers -/

/-- Absorb `size` bytes at `scratch + offset` into an empty state. -/
theorem absorbFixed_ok {B SP : BitVec 32} {s : State} (c : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {offset size : Nat}
    (heo : encodable (BitVec.ofNat 32 offset) = true) (hes : encodable (BitVec.ofNat 32 size) = true)
    (ho : B.toNat + offset + size ≤ 2 ^ 32) (hlo : 768 ≤ offset) (hs : size < 2 ^ 32) (hpos : 0 < size)
    (hcov : Covers [⟨State.addr B + BitVec.ofNat 64 offset, size⟩] s.wr)
    (hstk : (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 offset, size⟩) {h0 : HashValue 64}
    (repr : Repr b h0 s.mem (State.addr B) []) :
    WP isa (absorbFixed offset size) s fun t =>
      Repr b h0 t.mem (State.addr B) (bytesAt s.mem (State.addr B + BitVec.ofNat 64 offset) size) ∧
      VG.Proof.Argon2.Arm.HPrime.Keeps B SP s t := by
  unfold absorbFixed
  have hfit := c.fits
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm heo) fun s₃ u₃ => wp_mov (op2_imm hes) fun s₄ u₄ => WP.block_nil ?_)
  have o : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have m : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c₄ : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s₄ := c.of_regs (o _ (by decide) (by decide) (by decide) (by decide))
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have eD : s₄.gpr .r9 = B + BitVec.ofNat 32 offset := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.r4]
  have eDw : State.addr (B + BitVec.ofNat 32 offset) = State.addr B + BitVec.ofNat 64 offset :=
    VG.Arm.addr_add (by omega)
  have dTo : (B + BitVec.ofNat 32 offset).toNat = B.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega)]; omega
  have hL : (s₄.gpr .r10).toNat = size := by
    rw [u₄.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs]
  have hDc : Covers [⟨State.addr (B + BitVec.ofNat 32 offset), size⟩] (s₄.rd ++ s₄.wr) := by
    rw [eDw, show s₄.wr = s.wr by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]]; exact Covers.right hcov
  have hDs : Region.Disjoint ⟨State.addr (B + BitVec.ofNat 32 offset), size⟩ ⟨State.addr B, 768⟩ := by
    rw [eDw]; exact Offset.disjoint_base _ hlo (by omega)
  have hDk : (stkR SP 32).Disjoint ⟨State.addr (B + BitVec.ofNat 32 offset), size⟩ := by
    rw [eDw]; exact hstk
  have hcount : s₄.gpr .r3 ++ s₄.gpr .r2 = BitVec.ofNat 64 ([] : List Byte).length := by
    have e1 : s₄.gpr .r3 = 0 := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    have e2 : s₄.gpr .r2 = 0 := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    rw [e1, e2]; rfl
  refine (VG.Proof.Argon2.Arm.HPrime.update_ok c₄ eD hL (by rw [dTo]; omega) hDc hDs hDk (by rw [m]; exact repr) hcount
    (by simp only [List.length_nil]; omega)).mono ?_
  rintro t ⟨r, cs, rd, wr, sp, f⟩
  refine ⟨by rw [m, eDw, List.nil_append] at r; exact r, ?_⟩
  refine (Keeps.same (B := B) (SP := SP) (fun q hq => o q (VG.Proof.Argon2.Arm.HPrime.kept_ne q hq).2.2.1
      (VG.Proof.Argon2.Arm.HPrime.kept_ne q hq).2.2.2.1 (VG.Proof.Argon2.Arm.HPrime.kept_ne q hq).2.2.2.2.1 (VG.Proof.Argon2.Arm.HPrime.kept_ne q hq).2.2.2.2.2.1) (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) m
      (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])).trans
    (Keeps.of_call cs sp rd wr f ?_)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩

/-! ## The hash of the digest -/

theorem next_ok {B SP : BitVec 32} {s : State} (c : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {n : Nat}
    (hn : s.gpr .r1 = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    WP isa next s fun t =>
      bytesAt t.mem (State.addr B + 768) 64 =
        finalHash b (Spec.Blake2.init b n 0) (bytesAt s.mem (State.addr B + 768) 64) ∧
      VG.Proof.Argon2.Arm.HPrime.Keeps B SP s t := by
  unfold next
  have hfit := c.fits
  refine WP.seq ((VG.Proof.Argon2.Arm.HPrime.init_ok c hn hn₁ hn₂).mono fun s₁ ⟨r₁, cs₁, rd₁, wr₁, sp₁, f₁⟩ => ?_)
  have k₁ : VG.Proof.Argon2.Arm.HPrime.Keeps B SP s s₁ := Keeps.of_call cs₁ sp₁ rd₁ wr₁ f₁ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
  have dg : bytesAt s₁.mem (State.addr B + 768) 64 = bytesAt s.mem (State.addr B + 768) 64 := by
    refine Proof.Blake2.bytesAt_congr fun i hi => f₁.bytes (R := ⟨State.addr B + 768, 64⟩) ?_ (by simp) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by decide) (by decide)
  refine WP.seq ((VG.Proof.Argon2.Arm.HPrime.absorbFixed_ok (k₁.ctx c) (offset := 768) (size := 64) (by decide) (by decide) (by omega)
    (by decide) (by decide) (by decide) ((k₁.ctx c).cov (by decide)) (c.stk_sub (by decide)) r₁).mono
    fun s₂ ⟨r₂, k₂⟩ => ?_)
  rw [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, dg] at r₂
  have c₂ := (k₁.trans k₂).ctx c
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
    WP.block_nil ?_)
  have c₄ : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s₄ := c₂.of_regs (by rw [u₄.other _ (by decide), u₃.other _ (by decide)])
    (by rw [u₄.sp, u₃.sp]) (by rw [u₄.wr, u₃.wr])
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  refine (VG.Proof.Argon2.Arm.HPrime.finalize_ok c₄ (d := bytesAt s.mem (State.addr B + 768) 64) (by rw [m₄]; exact r₂)
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

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.HPrime.Body`. -/
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

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (copy copyLoop saved baseSlot pfxOff)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_add wp_sub wp_subs wp_ldrb wp_strb op2_reg op2_imm sub_ofNat
  ofNat_beq_zero eval_ne eval_eq)
open VG.WriteBytes

/-- Where the caller's registers are, `r4` first. -/
abbrev saveList : List (Reg × Nat) := (.r4, baseSlot) :: saved

theorem saveList_slots : Spill.Slots 840 876 VG.Proof.Argon2.Arm.HPrime.saveList := by decide

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesAt_take (m : Mem) (p : Addr) (n k : Nat) (hn : n ≤ k) :
    (bytesAt m p k).take n = bytesAt m p n := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]

/-- The state of the body. -/
structure Body (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = VG.Proof.Argon2.Arm.HPrime.scr s₀
  r5 : s.gpr .r5 = VG.Proof.Argon2.Arm.HPrime.inp s₀
  r6 : s.gpr .r6 = s₀.gpr .r1
  sp : s.sp = VG.Proof.Argon2.Arm.HPrime.sp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Argon2.Arm.HPrime.outR s₀, VG.Proof.Argon2.Arm.HPrime.scrR s₀, VG.Proof.Argon2.Arm.HPrime.stk s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (VG.Proof.Argon2.Arm.HPrime.P s₀) s₀.gpr VG.Proof.Argon2.Arm.HPrime.saveList
  pfx : bytesAt s.mem (VG.Proof.Argon2.Arm.HPrime.P s₀ + 832) 4 = Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.HPrime.Pre s₀)
include hp

theorem Body.ctx {s : State} (h : VG.Proof.Argon2.Arm.HPrime.Body s₀ s) : VG.Proof.Argon2.Arm.HPrime.Ctx (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s :=
  ⟨h.r4, h.sp, by have := hp.scr_fits; omega, hp.sp_lo,
    (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Argon2.Arm.HPrime.scrR s₀, by simp [h.wr, hp.wr], 0, by simp, by simp⟩),
    hp.stk_scr.sub_right (Region.sub_prefix (by decide))⟩

/-- A word of `scratch` from offset 832 on is kept by the hash macros. -/
theorem keeps_word {s t : State} (k : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s t) {d : Nat} (hd : 832 ≤ d)
    (hd' : d + 4 ≤ 16384) : t.mem.readW (VG.Proof.Argon2.Arm.HPrime.P s₀ + BitVec.ofNat 64 d) 32 = s.mem.readW (VG.Proof.Argon2.Arm.HPrime.P s₀ + BitVec.ofNat 64 d) 32 := by
  refine k.frame.readW (r := ⟨VG.Proof.Argon2.Arm.HPrime.P s₀ + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint_base _ hd (by omega)
  · exact (hp.stk_scr.sub_right (Offset.sub_base _ (show d + 4 ≤ 16384 from hd'))).symm

theorem Body.keeps {s t : State} (h : VG.Proof.Argon2.Arm.HPrime.Body s₀ s) (k : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s t) : VG.Proof.Argon2.Arm.HPrime.Body s₀ t := by
  refine ⟨(k.gpr _ (by decide)).trans h.r4, (k.gpr _ (by decide)).trans h.r5, (k.gpr _ (by decide)).trans h.r6,
    k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (k.frame.sub fun r hr => ?_), fun q hq => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Argon2.Arm.HPrime.scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.Argon2.Arm.HPrime.stk s₀, by simp, fun _ h => h⟩
  · have hb := saveList_slots.bound hq
    rw [VG.Proof.Argon2.Arm.HPrime.keeps_word hp k (by omega) (by omega)]; exact h.saved q hq
  · rw [← h.pfx]
    exact k.bytes (R := ⟨VG.Proof.Argon2.Arm.HPrime.P s₀ + 832, 4⟩) (by simp) (Offset.disjoint_base _ (by decide) (by decide))
      (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))).symm

omit hp in
/-- A register write that keeps `r4`–`r6`. -/
theorem Body.upd {s t : State} (h : VG.Proof.Argon2.Arm.HPrime.Body s₀ s) {d : Reg} {v : BitVec 32} (u : MdStream.Arm.Upd s t d v)
    (h4 : d ≠ .r4) (h5 : d ≠ .r5) (h6 : d ≠ .r6) : VG.Proof.Argon2.Arm.HPrime.Body s₀ t :=
  ⟨by rw [u.other _ (Ne.symm h4), h.r4], by rw [u.other _ (Ne.symm h5), h.r5], by rw [u.other _ (Ne.symm h6), h.r6],
    by rw [u.sp, h.sp], by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.mem]; exact h.frame,
    by rw [u.mem]; exact h.saved, by rw [u.mem]; exact h.pfx⟩

end

/-! ## The output -/

/-- The output so far. -/
structure Out (s₀ s : State) (xs : List Byte) : Prop where
  ptr : s.gpr .r7 = VG.Proof.Argon2.Arm.HPrime.op s₀ + BitVec.ofNat 32 xs.length
  left : s.gpr .r8 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.HPrime.ol s₀ - xs.length)
  bytes : bytesAt s.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀)) xs.length = xs
  len : xs.length ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀

/-- The digest. -/
abbrev digest (s₀ s : State) : List Byte := bytesAt s.mem (VG.Proof.Argon2.Arm.HPrime.P s₀ + 768) 64

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.HPrime.Pre s₀)
include hp

/-- The output is kept by the hash macros. -/
theorem Out.keeps {s t : State} {xs : List Byte} (h : VG.Proof.Argon2.Arm.HPrime.Out s₀ s xs)
    (k : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s t) : VG.Proof.Argon2.Arm.HPrime.Out s₀ t xs := by
  refine ⟨(k.gpr _ (by decide)).trans h.ptr, (k.gpr _ (by decide)).trans h.left, ?_, h.len⟩
  have kb := k.bytes (R := ⟨State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀), xs.length⟩)
    (by have := h.len; have := hp.out_fits; simp; omega)
    ((hp.out_scr.sub_left (Region.sub_prefix h.len)).sub_right (Region.sub_prefix (by decide)))
    ((hp.stk_out.sub_right (Region.sub_prefix h.len)).symm)
  simp only at kb
  rw [kb]; exact h.bytes

/-! ## Copying digest bytes -/

/-- The copy loop's state after `j` of `n` bytes, from `s`: the bytes go from
the digest to `op + k`. -/
structure CopyI (s₀ s : State) (k n j : Nat) (t : State) : Prop where
  j_le : j ≤ n
  r9 : t.gpr .r9 = VG.Proof.Argon2.Arm.HPrime.scr s₀ + 768 + BitVec.ofNat 32 j
  r7 : t.gpr .r7 = VG.Proof.Argon2.Arm.HPrime.op s₀ + BitVec.ofNat 32 (k + j)
  r10 : t.gpr .r10 = BitVec.ofNat 32 (n - j)
  other : ∀ x, x ≠ .r12 → x ≠ .r9 → x ≠ .r7 → x ≠ .r10 → t.gpr x = s.gpr x
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : t.mem = VG.WriteBytes.writeBytes s.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀) + BitVec.ofNat 64 k) ((VG.Proof.Argon2.Arm.HPrime.digest s₀ s).take j)

omit hp in
theorem setWidth_byte (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  ext i hi; simp

theorem copyLoop_ok {s : State} (b : VG.Proof.Argon2.Arm.HPrime.Body s₀ s) {k n : Nat} (hk : s.gpr .r7 = VG.Proof.Argon2.Arm.HPrime.op s₀ + BitVec.ofNat 32 k)
    (h9 : s.gpr .r9 = VG.Proof.Argon2.Arm.HPrime.scr s₀ + 768) (hn : s.gpr .r10 = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64)
    (hkn : k + n ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀) {Q : State → Prop} (hQ : ∀ t, VG.Proof.Argon2.Arm.HPrime.CopyI s₀ s k n n t → Q t) :
    WP isa copyLoop s Q := by
  have hs := hp.scr_fits
  have ho := hp.out_fits
  have dgR : Region.Disjoint ⟨VG.Proof.Argon2.Arm.HPrime.P s₀ + 768, 64⟩ ⟨State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀) + BitVec.ofNat 64 k, n⟩ :=
    ((hp.out_scr.sub_left (Offset.sub_base _ (d := k) (n := n) (k := VG.Proof.Argon2.Arm.HPrime.ol s₀) (by omega))).sub_right
      (Offset.sub_base (VG.Proof.Argon2.Arm.HPrime.P s₀) (d := 768) (n := 64) (k := 16384) (by decide))).symm
  refine WP.loop (M := isa) (fun m (t : State) => ∃ j, m = n - j ∧ j < n ∧ VG.Proof.Argon2.Arm.HPrime.CopyI s₀ s k n j t) ?_ n s
    ⟨0, by omega, by omega, ⟨by omega, by simp [h9], by simp [hk], by rw [hn, Nat.sub_zero],
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.take_zero, VG.WriteBytes.writeBytes_nil]⟩⟩
  rintro m t ⟨j, rfl, hj, h⟩
  have e768 : State.addr (VG.Proof.Argon2.Arm.HPrime.scr s₀ + 768) = VG.Proof.Argon2.Arm.HPrime.P s₀ + 768 := VG.Arm.addr_add (k := 768) (by omega)
  -- The byte read.
  have hin : InRegions (t.rd ++ t.wr) (VG.Proof.Argon2.Arm.HPrime.P s₀ + 768 + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr, b.rd, b.wr, hp.wr]
    refine ⟨VG.Proof.Argon2.Arm.HPrime.scrR s₀, by simp, ?_⟩
    rw [show VG.Proof.Argon2.Arm.HPrime.P s₀ + 768 + BitVec.ofNat 64 j = VG.Proof.Argon2.Arm.HPrime.P s₀ + BitVec.ofNat 64 (768 + j) from Offset.add_add _ 768 j]
    exact Offset.contains_base _ (by omega) (by omega)
  have hbyte : t.mem (VG.Proof.Argon2.Arm.HPrime.P s₀ + 768 + BitVec.ofNat 64 j) = s.mem (VG.Proof.Argon2.Arm.HPrime.P s₀ + 768 + BitVec.ofNat 64 j) := by
    rw [h.mem]
    have hl : ((VG.Proof.Argon2.Arm.HPrime.digest s₀ s).take j).length ≤ n := by simp [VG.Proof.Argon2.Arm.HPrime.digest, bytesAt]; omega
    exact (VG.WriteBytes.writeBytes_frame (R := ⟨State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀) + BitVec.ofNat 64 k, n⟩) s.mem _ _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact hl)).bytes
      (R := ⟨VG.Proof.Argon2.Arm.HPrime.P s₀ + 768, 64⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dgR)
      (by show (64 : Nat) ≤ 2 ^ 64; decide) (show j < 64 by omega)
  -- The byte written.
  have hout : InRegions t.wr (State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀) + BitVec.ofNat 64 (k + j)) 1 := by
    rw [h.wr, b.wr, hp.wr]
    exact ⟨VG.Proof.Argon2.Arm.HPrime.outR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_ldrb (a := VG.Proof.Argon2.Arm.HPrime.P s₀ + 768 + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r9, BitVec.add_zero, VG.Arm.addr_add (by rw [BitVec.toNat_add]; simp; omega), e768]) hin
    fun s₁ u₁ => ?_
  refine wp_strb (a := State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀) + BitVec.ofNat 64 (k + j)) (by decide)
    (by rw [u₁.other _ (by decide), h.r7, BitVec.add_zero, VG.Arm.addr_add (by omega)])
    (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_add (op2_imm (by decide)) fun s₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun s₅ u₅ z₅ => WP.block_nil ?_
  have hr10 : s₅.gpr .r10 = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r10,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  have hI : VG.Proof.Argon2.Arm.HPrime.CopyI s₀ s k n (j + 1) s₅ := by
    refine ⟨by omega, ?_, ?_, hr10, fun x h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r9,
        BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r7,
        BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [u₅.other x h4, u₄.other x h3, u₃.other x h2, g₂.gpr, u₁.other x h1, h.other x h1 h2 h3 h4]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · have hj' : j < (VG.Proof.Argon2.Arm.HPrime.digest s₀ s).length := by simp [VG.Proof.Argon2.Arm.HPrime.digest, bytesAt]; omega
      have hl : (List.take j (VG.Proof.Argon2.Arm.HPrime.digest s₀ s)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.gpr, hbyte, h.mem,
        List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, VG.Proof.Argon2.Arm.HPrime.setWidth_byte, Offset.add_add]
      congr 1
      simp [VG.Proof.Argon2.Arm.HPrime.digest, bytesAt]
  have hz : isa.eval .ne s₅ = some (decide (n - (j + 1) ≠ 0)) := by
    show VG.Arm.eval .ne s₅ = _
    rw [eval_ne, z₅, ← u₅.gpr, hr10, ofNat_beq_zero (by omega)]
    simp
  by_cases hjn : j + 1 = n
  · exact .inl ⟨by rw [hz]; simp; omega, hQ _ (hjn ▸ hI)⟩
  · exact .inr ⟨by rw [hz]; simp; omega, n - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

/-- Emit `n` digest bytes after the output `xs`. -/
theorem copyOut_ok {s : State} (b : VG.Proof.Argon2.Arm.HPrime.Body s₀ s) {xs : List Byte} (h : VG.Proof.Argon2.Arm.HPrime.Out s₀ s xs) {n : Nat}
    (hn : s.gpr .r10 = BitVec.ofNat 32 n) (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) (hkn : xs.length + n ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀) :
    WP isa copy s fun t => VG.Proof.Argon2.Arm.HPrime.Body s₀ t ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r11 = s.gpr .r11 ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀)) (xs.length + n) = xs ++ (VG.Proof.Argon2.Arm.HPrime.digest s₀ s).take n ∧
      t.gpr .r7 = VG.Proof.Argon2.Arm.HPrime.op s₀ + BitVec.ofNat 32 (xs.length + n) ∧ VG.Proof.Argon2.Arm.HPrime.digest s₀ t = VG.Proof.Argon2.Arm.HPrime.digest s₀ s := by
  have hs := hp.scr_fits
  have ho := hp.out_fits
  unfold copy
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have b₁ : VG.Proof.Argon2.Arm.HPrime.Body s₀ s₁ := b.keeps hp (Keeps.same (fun r hr => u₁.other r (by
    simp only [VG.Proof.Argon2.Arm.HPrime.kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.sp u₁.mem u₁.rd u₁.wr)
  refine VG.Proof.Argon2.Arm.HPrime.copyLoop_ok hp b₁ (k := xs.length) (n := n) (by rw [u₁.other _ (by decide), h.ptr])
    (by rw [u₁.gpr, b.r4]) (by rw [u₁.other _ (by decide), hn]) hn₁ hn₂ hkn fun t ht => ?_
  have dgR : Region.Disjoint ⟨VG.Proof.Argon2.Arm.HPrime.P s₀ + 768, 64⟩ ⟨State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀) + BitVec.ofNat 64 xs.length, n⟩ :=
    ((hp.out_scr.sub_left (Offset.sub_base _ (d := xs.length) (n := n) (k := VG.Proof.Argon2.Arm.HPrime.ol s₀) (by omega))).sub_right
      (Offset.sub_base (VG.Proof.Argon2.Arm.HPrime.P s₀) (d := 768) (n := 64) (k := 16384) (by decide))).symm
  have lenL : ((VG.Proof.Argon2.Arm.HPrime.digest s₀ s₁).take n).length = n := by simp [VG.Proof.Argon2.Arm.HPrime.digest, bytesAt]; omega
  have F : Frame [⟨State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀) + BitVec.ofNat 64 xs.length, n⟩] s₁.mem t.mem := by
    rw [ht.mem]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [lenL]; exact Region.contains_self _ _)
  have outSub : Region.Sub ⟨State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀) + BitVec.ofNat 64 xs.length, n⟩ (VG.Proof.Argon2.Arm.HPrime.outR s₀) :=
    Offset.sub_base _ (by omega)
  have d₁ : VG.Proof.Argon2.Arm.HPrime.digest s₀ s₁ = VG.Proof.Argon2.Arm.HPrime.digest s₀ s := by simp only [VG.Proof.Argon2.Arm.HPrime.digest, u₁.mem]
  have dt : VG.Proof.Argon2.Arm.HPrime.digest s₀ t = VG.Proof.Argon2.Arm.HPrime.digest s₀ s₁ :=
    Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨VG.Proof.Argon2.Arm.HPrime.P s₀ + 768, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dgR) (by simp) hi
  refine ⟨⟨by rw [ht.other _ (by decide) (by decide) (by decide) (by decide), b₁.r4],
      by rw [ht.other _ (by decide) (by decide) (by decide) (by decide), b₁.r5],
      by rw [ht.other _ (by decide) (by decide) (by decide) (by decide), b₁.r6],
      by rw [ht.sp, b₁.sp], by rw [ht.rd, b₁.rd], by rw [ht.wr, b₁.wr],
      b₁.frame.trans (F.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.Argon2.Arm.HPrime.outR s₀, by simp, outSub⟩),
      fun q hq => ?_, ?_⟩, ?_, ?_, ?_, ?_, dt.trans d₁⟩
  · have hb := saveList_slots.bound hq
    rw [F.readW (r := ⟨VG.Proof.Argon2.Arm.HPrime.P s₀ + BitVec.ofNat 64 q.2, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.out_scr.sub_left outSub).sub_right (Offset.sub_base _ (by omega))).symm) (by decide)]
    exact b₁.saved q hq
  · rw [← b₁.pfx]
    exact Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨VG.Proof.Argon2.Arm.HPrime.P s₀ + 832, 4⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.out_scr.sub_left outSub).sub_right (Offset.sub_base _ (by decide))).symm) (by simp) hi
  · rw [ht.other _ (by decide) (by decide) (by decide) (by decide), u₁.other _ (by decide)]
  · rw [ht.other _ (by decide) (by decide) (by decide) (by decide), u₁.other _ (by decide)]
  · have old : bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀)) xs.length = bytesAt s₁.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀)) xs.length :=
      Proof.Blake2.bytesAt_congr fun i hi => F.bytes (R := ⟨State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀), xs.length⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega)) (by have := h.len; simp; omega) hi
    have new : bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀) + BitVec.ofNat 64 xs.length) n = (VG.Proof.Argon2.Arm.HPrime.digest s₀ s₁).take n := by
      rw [ht.mem]
      have := VG.Proof.Argon2.Arm.HPrime.bytesAt_writeBytes s₁.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀) + BitVec.ofNat 64 xs.length)
        ((VG.Proof.Argon2.Arm.HPrime.digest s₀ s₁).take n) (by rw [lenL]; omega)
      rwa [lenL] at this
    rw [Proof.Blake2.bytesAt_add, new, old, d₁, u₁.mem, h.bytes]
  · exact ht.r7

/-- Emit a 32-byte prefix of the digest. -/
theorem emit_ok {s : State} (b : VG.Proof.Argon2.Arm.HPrime.Body s₀ s) {xs : List Byte} (h : VG.Proof.Argon2.Arm.HPrime.Out s₀ s xs)
    (hkn : xs.length + 32 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀) :
    WP isa Impl.Argon2.Arm.HPrime.emitPrefix s fun t => VG.Proof.Argon2.Arm.HPrime.Body s₀ t ∧ t.gpr .r11 = s.gpr .r11 ∧
      VG.Proof.Argon2.Arm.HPrime.Out s₀ t (xs ++ (VG.Proof.Argon2.Arm.HPrime.digest s₀ s).take 32) ∧ VG.Proof.Argon2.Arm.HPrime.digest s₀ t = VG.Proof.Argon2.Arm.HPrime.digest s₀ s := by
  unfold Impl.Argon2.Arm.HPrime.emitPrefix
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s s₁ := Keeps.same (fun r hr => u₁.other r (by
    simp only [VG.Proof.Argon2.Arm.HPrime.kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.sp u₁.mem u₁.rd u₁.wr
  refine WP.seq ((VG.Proof.Argon2.Arm.HPrime.copyOut_ok hp (b.keeps hp k₁) (h.keeps hp k₁) u₁.gpr (by decide) (by decide) hkn).mono
    fun s₂ ⟨b₂, l₂, e₂, by₂, p₂, d₂⟩ => ?_)
  refine wp_sub (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_
  have len' : (xs ++ (VG.Proof.Argon2.Arm.HPrime.digest s₀ s).take 32).length = xs.length + 32 := by
    simp [VG.Proof.Argon2.Arm.HPrime.digest, bytesAt]
  refine ⟨b₂.upd u₃ (by decide) (by decide) (by decide), by rw [u₃.other _ (by decide), e₂, u₁.other _ (by decide)],
    ⟨?_, ?_, ?_, by rw [len']; exact hkn⟩, by simp only [VG.Proof.Argon2.Arm.HPrime.digest, u₃.mem]; exact d₂.trans (by simp only [VG.Proof.Argon2.Arm.HPrime.digest, u₁.mem])⟩
  · rw [len', u₃.other _ (by decide), p₂]
  · rw [len', u₃.gpr, l₂, u₁.other _ (by decide), h.left]
    exact (sub_ofNat (a := VG.Proof.Argon2.Arm.HPrime.ol s₀ - xs.length) (b := 32) (by omega)).trans (by congr 1)
  · rw [len', u₃.mem, by₂, show VG.Proof.Argon2.Arm.HPrime.digest s₀ s₁ = VG.Proof.Argon2.Arm.HPrime.digest s₀ s by simp only [VG.Proof.Argon2.Arm.HPrime.digest, u₁.mem]]

/-- Copy the bytes left. -/
theorem copyRemaining_ok {s : State} (b : VG.Proof.Argon2.Arm.HPrime.Body s₀ s) {xs : List Byte} (h : VG.Proof.Argon2.Arm.HPrime.Out s₀ s xs)
    (hn₁ : xs.length < VG.Proof.Argon2.Arm.HPrime.ol s₀) (hn₂ : VG.Proof.Argon2.Arm.HPrime.ol s₀ - xs.length ≤ 64) :
    WP isa Impl.Argon2.Arm.HPrime.copyRemaining s fun t => VG.Proof.Argon2.Arm.HPrime.Body s₀ t ∧ t.gpr .r11 = s.gpr .r11 ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀)) (VG.Proof.Argon2.Arm.HPrime.ol s₀) = xs ++ (VG.Proof.Argon2.Arm.HPrime.digest s₀ s).take (VG.Proof.Argon2.Arm.HPrime.ol s₀ - xs.length) := by
  unfold Impl.Argon2.Arm.HPrime.copyRemaining
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s s₁ := Keeps.same (fun r hr => u₁.other r (by
    simp only [VG.Proof.Argon2.Arm.HPrime.kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.sp u₁.mem u₁.rd u₁.wr
  refine (VG.Proof.Argon2.Arm.HPrime.copyOut_ok hp (b.keeps hp k₁) (h.keeps hp k₁) (n := VG.Proof.Argon2.Arm.HPrime.ol s₀ - xs.length)
    (by rw [u₁.gpr, h.left]) (by omega) hn₂ (by omega)).mono
    fun t ⟨bt, _, et, byt, _, _⟩ => ⟨bt, by rw [et, u₁.other _ (by decide)], ?_⟩
  rw [show xs.length + (VG.Proof.Argon2.Arm.HPrime.ol s₀ - xs.length) = VG.Proof.Argon2.Arm.HPrime.ol s₀ by omega] at byt
  rw [byt]; simp only [VG.Proof.Argon2.Arm.HPrime.digest, u₁.mem]

end

end VG.Proof.Argon2.Arm.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.HPrime.CallsCT`. -/
section

/-!
# Argon2 H′ on ARMv7: the calls, in two runs

The macros calling the BLAKE2b functions leak the same trace in two runs that
pass them the same arguments (`init_rel`, `update_rel`, `finalize_rel`, and
`absorbFixed_rel` and `next_rel` built on them): the instructions before
each call are checked by the taint analysis, and the call (in the frame of
its stack arguments) is related by the callee's constant time
(`RelCT.call`, `frameCall_rel`), from the callee's precondition in both runs
(`init_pre`, `update_pre`, `finalize_pre`).
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Arm.FrameStack
open VG.Impl.Argon2.Arm.HPrime (init update finalize absorbFixed next)
open VG.Proof.Blake2 (initArm updateArm finalizeArm)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_reg op2_imm)

/-! ## Two runs -/

/-- Two runs, each described by `WP`, of code the taint analysis proves
constant time from the registers `rs` public. -/
theorem rel_regs {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun t₁ t₂ => G₁ t₁ ∧ G₂ t₂ :=
  rel_agree (Taint.ofRegs rs) (fun s₁ s₂ h₁ h₂ => Taint.agree_ofRegs (hag s₁ s₂ h₁ h₂)) hc hw₁ hw₂

/-- A relation proved from facts of the related states. -/
theorem RelCT.of_pre {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa P c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂

/-! ## `init` -/

/-- What `init` needs: the state's context, and the digest length in `r1`. -/
def InitIn (B SP : BitVec 32) (n : Nat) (s : State) : Prop :=
  VG.Proof.Argon2.Arm.HPrime.Ctx B SP s ∧ s.gpr .r1 = BitVec.ofNat 32 n

theorem init_blk {B SP : BitVec 32} {n : Nat} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.InitIn B SP n s) :
    WP isa (.block [.mov .r0 (.reg .r4), .mov .r2 (.reg .r4), .mov .r3 (.imm 0)]) s fun t =>
      VG.Proof.Argon2.Arm.HPrime.Ctx B SP t ∧ t.gpr .r1 = BitVec.ofNat 32 n ∧ t.gpr .r0 = B ∧ t.gpr .r2 = B ∧ t.gpr .r3 = 0 :=
  wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil
      ⟨h.1.of_regs (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₃.sp, u₂.sp, u₁.sp]) (by rw [u₃.wr, u₂.wr, u₁.wr]),
       by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.2],
       by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.1.r4],
       by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.1.r4], u₃.gpr⟩

theorem init_rel {B SP : BitVec 32} {n : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.HPrime.InitIn B SP n s₁ ∧ VG.Proof.Argon2.Arm.HPrime.InitIn B SP n s₂) VG.Impl.Argon2.Arm.HPrime.init fun _ _ => True := by
  unfold Impl.Argon2.Arm.HPrime.init
  refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [.r4, .r1] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.r4, h₂.1.r4]
      · rw [h₁.2, h₂.2]) ⟨_, by taint_decide⟩ (fun _ h => VG.Proof.Argon2.Arm.HPrime.init_blk h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.init_blk h)) ?_
  refine RelCT.call VG.Proof.Argon2.Arm.HPrime.init_correct VG.Proof.Argon2.Arm.HPrime.init_ct (VG.Proof.Argon2.Arm.HPrime.initRd B) (VG.Proof.Argon2.Arm.HPrime.initWr B)
    fun s₁ s₂ ⟨⟨c₁, e₁, a₁, x₁, y₁⟩, ⟨c₂, e₂, a₂, x₂, y₂⟩⟩ => ?_
  obtain ⟨p₁, v₁, w₁⟩ := VG.Proof.Argon2.Arm.HPrime.init_pre c₁ e₁ hn₁ hn₂ a₁ x₁ y₁
  obtain ⟨p₂, v₂, w₂⟩ := VG.Proof.Argon2.Arm.HPrime.init_pre c₂ e₂ hn₁ hn₂ a₂ x₂ y₂
  refine ⟨p₁, p₂, ?_, v₁, w₁, v₂, w₂⟩
  simp only [VG.Proof.Blake2.initArm, State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce0, Proof.Blake2.Arm.Stream.ce1,
    Proof.Blake2.Arm.Stream.ce2, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), a₁, a₂, e₁, e₂,
    x₁, x₂, y₁, y₂, and_self]

/-! ## `update` -/

/-- What `update` needs: the state's context, the data at `D`, of `L` bytes,
and the count in `r3:r2`. -/
def UpdateIn (B SP D : BitVec 32) (L : Nat) (lo hi : BitVec 32) (s : State) : Prop :=
  VG.Proof.Argon2.Arm.HPrime.Ctx B SP s ∧ s.gpr .r9 = D ∧ (s.gpr .r10).toNat = L ∧ s.gpr .r2 = lo ∧ s.gpr .r3 = hi ∧
    Covers [⟨State.addr D, L⟩] (s.rd ++ s.wr)

theorem update_blk {B SP D : BitVec 32} {L : Nat} {lo hi : BitVec 32} {s : State}
    (h : VG.Proof.Argon2.Arm.HPrime.UpdateIn B SP D L lo hi s) :
    WP isa (.block [.mov .r0 (.reg .r4), .dp .add .r12 .r4 (.imm 192)]) s fun t =>
      VG.Proof.Argon2.Arm.HPrime.UpdateIn B SP D L lo hi t ∧ t.gpr .r0 = B ∧ t.gpr .r12 = B + 192 := by
  obtain ⟨c, e1, e2, e3, e4, cv⟩ := h
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_
  have o : ∀ r, r ≠ .r0 → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r h0 h12 => by
    rw [u₂.other _ h12, u₁.other _ h0]
  refine ⟨⟨c.of_regs (o _ (by decide) (by decide)) (by rw [u₂.sp, u₁.sp]) (by rw [u₂.wr, u₁.wr]),
    by rw [o _ (by decide) (by decide), e1], by rw [o _ (by decide) (by decide), e2],
    by rw [o _ (by decide) (by decide), e3], by rw [o _ (by decide) (by decide), e4],
    by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact cv⟩, ?_, ?_⟩
  · rw [u₂.other _ (by decide), u₁.gpr, c.r4]
  · rw [u₂.gpr, u₁.other _ (by decide), c.r4]

theorem update_rel {B SP D : BitVec 32} {L : Nat} {lo hi : BitVec 32} (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDs : Region.Disjoint ⟨State.addr D, L⟩ ⟨State.addr B, 768⟩)
    (hDk : (stkR SP 32).Disjoint ⟨State.addr D, L⟩) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.HPrime.UpdateIn B SP D L lo hi s₁ ∧ VG.Proof.Argon2.Arm.HPrime.UpdateIn B SP D L lo hi s₂) VG.Impl.Argon2.Arm.HPrime.update
      fun _ _ => True := by
  unfold VG.Impl.Argon2.Arm.HPrime.update
  refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [.r4] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.r4, h₂.1.r4]) ⟨_, by taint_decide⟩ (fun _ h => VG.Proof.Argon2.Arm.HPrime.update_blk h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.update_blk h)) ?_
  refine frameCall_rel (rs := VG.Proof.Argon2.Arm.HPrime.upd4) (by decide) update_v.1 update_v.2.1 (VG.Proof.Argon2.Arm.HPrime.updRd D L SP) (VG.Proof.Argon2.Arm.HPrime.updWr B)
    fun s₁ s₂ ⟨⟨⟨c₁, d₁, l₁, x₁, y₁, v₁⟩, a₁, b₁⟩, ⟨⟨c₂, d₂, l₂, x₂, y₂, v₂⟩, a₂, b₂⟩⟩ => ?_
  obtain ⟨p₁, cv₁, cw₁⟩ := VG.Proof.Argon2.Arm.HPrime.update_pre c₁ d₁ l₁ hDfit v₁ hDs hDk a₁ b₁
  obtain ⟨p₂, cv₂, cw₂⟩ := VG.Proof.Argon2.Arm.HPrime.update_pre c₂ d₂ l₂ hDfit v₂ hDs hDk a₂ b₂
  have hlo := c₁.lo
  have hn₁ : 4 * upd4.length ≤ s₁.sp.toNat := by rw [c₁.sp]; simp only [List.length_cons, List.length_nil]; omega
  have hn₂ : 4 * upd4.length ≤ s₂.sp.toNat := by rw [c₂.sp]; simp only [List.length_cons, List.length_nil]; omega
  refine ⟨c₁.sp.trans c₂.sp.symm, p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, cv₁, cw₁, cv₂, cw₂⟩
  · simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, c₁.sp, c₂.sp]
  · simp only [State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce0, pushed_gpr, a₁, a₂]
  · simp only [State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce2, pushed_gpr, x₁, x₂]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), pushed_gpr,
      y₁, y₂]
  · exact pushed_arg_eq hn₁ hn₂ (i := 0) (by decide) (by show s₁.gpr .r9 = s₂.gpr .r9; rw [d₁, d₂])
  · exact pushed_arg_eq hn₁ hn₂ (i := 1) (by decide)
      (by show s₁.gpr .r10 = s₂.gpr .r10; exact BitVec.eq_of_toNat_eq (l₁.trans l₂.symm))
  · exact pushed_arg_eq hn₁ hn₂ (i := 2) (by decide) (by show s₁.gpr .r12 = s₂.gpr .r12; rw [b₁, b₂])

/-! ## `finalize` -/

/-- What `finalize` needs: the state's context and the count in `r3:r2`. -/
def FinalizeIn (B SP lo hi : BitVec 32) (s : State) : Prop :=
  VG.Proof.Argon2.Arm.HPrime.Ctx B SP s ∧ s.gpr .r2 = lo ∧ s.gpr .r3 = hi

theorem finalize_blk {B SP lo hi : BitVec 32} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.FinalizeIn B SP lo hi s) :
    WP isa (.block [.mov .r0 (.reg .r4), .dp .add .r1 .r4 (.imm 768), .dp .add .r12 .r4 (.imm 192)]) s
      fun t => VG.Proof.Argon2.Arm.HPrime.FinalizeIn B SP lo hi t ∧ t.gpr .r0 = B ∧ t.gpr .r1 = B + 768 ∧ t.gpr .r12 = B + 192 := by
  obtain ⟨c, e3, e4⟩ := h
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_
  have o : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h0 h1 h12 => by
    rw [u₃.other _ h12, u₂.other _ h1, u₁.other _ h0]
  refine ⟨⟨c.of_regs (o _ (by decide) (by decide) (by decide)) (by rw [u₃.sp, u₂.sp, u₁.sp])
    (by rw [u₃.wr, u₂.wr, u₁.wr]), by rw [o _ (by decide) (by decide) (by decide), e3],
    by rw [o _ (by decide) (by decide) (by decide), e4]⟩, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, c.r4]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), c.r4]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.r4]

theorem finalize_rel {B SP lo hi : BitVec 32} :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.HPrime.FinalizeIn B SP lo hi s₁ ∧ VG.Proof.Argon2.Arm.HPrime.FinalizeIn B SP lo hi s₂) VG.Impl.Argon2.Arm.HPrime.finalize
      fun _ _ => True := by
  unfold VG.Impl.Argon2.Arm.HPrime.finalize
  refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [.r4] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.r4, h₂.1.r4]) ⟨_, by taint_decide⟩ (fun _ h => VG.Proof.Argon2.Arm.HPrime.finalize_blk h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.finalize_blk h)) ?_
  refine frameCall_rel (rs := VG.Proof.Argon2.Arm.HPrime.fin2) (by decide) finalize_v.1 finalize_v.2.1 (VG.Proof.Argon2.Arm.HPrime.finRd SP) (VG.Proof.Argon2.Arm.HPrime.finWr B)
    fun s₁ s₂ ⟨⟨⟨c₁, x₁, y₁⟩, a₁, i₁, b₁⟩, ⟨⟨c₂, x₂, y₂⟩, a₂, i₂, b₂⟩⟩ => ?_
  obtain ⟨p₁, cv₁, cw₁⟩ := VG.Proof.Argon2.Arm.HPrime.finalize_pre c₁ a₁ i₁ b₁
  obtain ⟨p₂, cv₂, cw₂⟩ := VG.Proof.Argon2.Arm.HPrime.finalize_pre c₂ a₂ i₂ b₂
  have hlo := c₁.lo
  have hn₁ : 4 * fin2.length ≤ s₁.sp.toNat := by rw [c₁.sp]; simp only [List.length_cons, List.length_nil]; omega
  have hn₂ : 4 * fin2.length ≤ s₂.sp.toNat := by rw [c₂.sp]; simp only [List.length_cons, List.length_nil]; omega
  refine ⟨c₁.sp.trans c₂.sp.symm, p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, cv₁, cw₁, cv₂, cw₂⟩
  · simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, c₁.sp, c₂.sp]
  · simp only [State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce0, pushed_gpr, a₁, a₂]
  · simp only [State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce2, pushed_gpr, x₁, x₂]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), pushed_gpr,
      y₁, y₂]
  · exact pushed_arg_eq hn₁ hn₂ (i := 0) (by decide) (by show s₁.gpr .r1 = s₂.gpr .r1; rw [i₁, i₂])
  · exact pushed_arg_eq hn₁ hn₂ (i := 1) (by decide) (by show s₁.gpr .r12 = s₂.gpr .r12; rw [b₁, b₂])

/-! ## Hashing a fixed buffer, and the digest -/

/-- The instructions before `absorbFixed`'s call of `update`. -/
theorem absorbFixed_blk {B SP : BitVec 32} {s : State} (c : VG.Proof.Argon2.Arm.HPrime.Ctx B SP s) {offset size : Nat}
    (heo : encodable (BitVec.ofNat 32 offset) = true) (hes : encodable (BitVec.ofNat 32 size) = true)
    (ho : B.toNat + offset + size ≤ 2 ^ 32) (hs : 0 < size) (hlt : size < 2 ^ 32)
    (hcov : Covers [⟨State.addr B + BitVec.ofNat 64 offset, size⟩] s.wr) :
    WP isa (.block [.mov .r2 (.imm 0), .mov .r3 (.imm 0), .dp .add .r9 .r4 (.imm (BitVec.ofNat 32 offset)),
      .mov .r10 (.imm (BitVec.ofNat 32 size))]) s
      (VG.Proof.Argon2.Arm.HPrime.UpdateIn B SP (B + BitVec.ofNat 32 offset) size 0 0) := by
  have hfit := c.fits
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm heo) fun s₃ u₃ => wp_mov (op2_imm hes) fun s₄ u₄ => WP.block_nil ?_
  have o : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have w : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine ⟨c.of_regs (o _ (by decide) (by decide) (by decide) (by decide)) (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) w,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.r4]
  · rw [u₄.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [VG.Arm.addr_add (by omega), show s₄.rd ++ s₄.wr = s.rd ++ s.wr by
      rw [w, u₄.rd, u₃.rd, u₂.rd, u₁.rd]]
    exact Covers.right hcov

/-- What `absorbFixed` needs: the context, and the buffer writable. -/
def FixedIn (B SP : BitVec 32) (offset size : Nat) (s : State) : Prop :=
  VG.Proof.Argon2.Arm.HPrime.Ctx B SP s ∧ Covers [⟨State.addr B + BitVec.ofNat 64 offset, size⟩] s.wr

/-- The instructions before `absorbFixed`'s call, from `r4` public. -/
abbrev FixedCheck (offset size : Nat) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r4]) (.block [.mov .r2 (.imm 0), .mov .r3 (.imm 0),
      .dp .add .r9 .r4 (.imm (BitVec.ofNat 32 offset)), .mov .r10 (.imm (BitVec.ofNat 32 size))]) hc).isSome = true

theorem fixed_check_768 : VG.Proof.Argon2.Arm.HPrime.FixedCheck 768 64 := ⟨_, by taint_decide⟩
theorem fixed_check_832 : VG.Proof.Argon2.Arm.HPrime.FixedCheck 832 4 := ⟨_, by taint_decide⟩

theorem absorbFixed_rel {B SP : BitVec 32} {offset size : Nat}
    (heo : encodable (BitVec.ofNat 32 offset) = true) (hes : encodable (BitVec.ofNat 32 size) = true)
    (ho : B.toNat + offset + size ≤ 2 ^ 32) (hlo : 768 ≤ offset) (hs : 0 < size)
    (hstk : (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 offset, size⟩)
    (hc : VG.Proof.Argon2.Arm.HPrime.FixedCheck offset size) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.HPrime.FixedIn B SP offset size s₁ ∧ VG.Proof.Argon2.Arm.HPrime.FixedIn B SP offset size s₂)
      (absorbFixed offset size) fun _ _ => True := by
  have eD : State.addr (B + BitVec.ofNat 32 offset) = State.addr B + BitVec.ofNat 64 offset :=
    VG.Arm.addr_add (by omega)
  have dTo : (B + BitVec.ofNat 32 offset).toNat = B.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega)]; omega
  unfold absorbFixed
  refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [.r4] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.r4, h₂.1.r4]) hc
    (fun s ⟨c, h⟩ => VG.Proof.Argon2.Arm.HPrime.absorbFixed_blk c heo hes ho hs (by omega) h)
    (fun s ⟨c, h⟩ => VG.Proof.Argon2.Arm.HPrime.absorbFixed_blk c heo hes ho hs (by omega) h))
    (VG.Proof.Argon2.Arm.HPrime.update_rel (by rw [dTo]; omega) (by rw [eD]; exact Offset.disjoint_base _ hlo (by omega))
      (by rw [eD]; exact hstk))

/-- `next`, from the context and the digest length in `r1`. -/
theorem next_rel {B SP : BitVec 32} {n : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.Arm.HPrime.InitIn B SP n s₁ ∧ VG.Proof.Argon2.Arm.HPrime.InitIn B SP n s₂) next fun _ _ => True := by
  have st : ∀ s, VG.Proof.Argon2.Arm.HPrime.InitIn B SP n s → WP isa VG.Impl.Argon2.Arm.HPrime.init s fun t =>
      Repr b (Spec.Blake2.init b n 0) t.mem (State.addr B) [] ∧ VG.Proof.Argon2.Arm.HPrime.Ctx B SP t := fun s ⟨c, e⟩ =>
    (VG.Proof.Argon2.Arm.HPrime.init_ok c e hn₁ hn₂).mono fun t ⟨r, cs, _, wr, sp, _⟩ =>
      ⟨r, c.of_regs (cs _ (by decide) (by decide)) sp wr⟩
  have fx : ∀ s, Repr b (Spec.Blake2.init b n 0) s.mem (State.addr B) [] ∧ VG.Proof.Argon2.Arm.HPrime.Ctx B SP s →
      WP isa (absorbFixed 768 64) s fun t => VG.Proof.Argon2.Arm.HPrime.Ctx B SP t := fun s ⟨r, c⟩ =>
    (VG.Proof.Argon2.Arm.HPrime.absorbFixed_ok c (offset := 768) (size := 64) (by decide) (by decide) (by have := c.fits; omega)
      (by decide) (by decide) (by decide) (c.cov (by decide)) (c.stk_sub (by decide)) r).mono
      fun t ⟨_, k⟩ => k.ctx c
  have fin : ∀ s, VG.Proof.Argon2.Arm.HPrime.Ctx B SP s → WP isa (.block [.mov .r2 (.imm 64), .mov .r3 (.imm 0)]) s
      (VG.Proof.Argon2.Arm.HPrime.FinalizeIn B SP 64 0) := fun s c =>
    wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil
      ⟨c.of_regs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.sp, u₁.sp])
        (by rw [u₂.wr, u₁.wr]),
       by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr⟩
  unfold next
  refine RelCT.seq (rel_wp (VG.Proof.Argon2.Arm.HPrime.init_rel hn₁ hn₂) st st)
    (RelCT.seq (R := fun s₁ s₂ => VG.Proof.Argon2.Arm.HPrime.Ctx B SP s₁ ∧ VG.Proof.Argon2.Arm.HPrime.Ctx B SP s₂) ?_
      (RelCT.seq (R := fun s₁ s₂ => VG.Proof.Argon2.Arm.HPrime.FinalizeIn B SP 64 0 s₁ ∧ VG.Proof.Argon2.Arm.HPrime.FinalizeIn B SP 64 0 s₂) ?_ VG.Proof.Argon2.Arm.HPrime.finalize_rel))
  · refine rel_wp (RelCT.of_pre fun s₁ _ ⟨⟨_, c₁⟩, _⟩ =>
      (VG.Proof.Argon2.Arm.HPrime.absorbFixed_rel (B := B) (SP := SP) (offset := 768) (size := 64) (by decide) (by decide)
        (by have := c₁.fits; omega) (by decide) (by decide) (c₁.stk_sub (by decide)) VG.Proof.Argon2.Arm.HPrime.fixed_check_768).mono
      (fun s₁ s₂ ⟨⟨_, c₁⟩, ⟨_, c₂⟩⟩ => ⟨⟨c₁, c₁.cov (by decide)⟩, ⟨c₂, c₂.cov (by decide)⟩⟩)
      fun _ _ h => h) fx fx
  · exact VG.Proof.Argon2.Arm.HPrime.rel_regs [.r4] (fun s₁ s₂ c₁ c₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [c₁.r4, c₂.r4]) ⟨_, by taint_decide⟩ fin fin

end VG.Proof.Argon2.Arm.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.HPrime.First`. -/
section

/-!
# Argon2 H′ on ARMv7: the first digest

`first_ok`: `first` leaves H(min(out_len, 64), LE32(out_len) ‖ input) at the
start of the digest, `scratch[768, 832)`. The input is read before anything
is written to the output, so the two may overlap.
-/

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
    MdStream.Arm.ofNat_shr (by omega), ofNat_beq_zero (by omega)]
  by_cases h : x ≤ 64
  · simp only [h, decide_true, decide_eq_true_eq]; omega
  · simp only [h, decide_false, decide_eq_false_iff_not]; omega

/-- The comparisons with 64 of the bytes left (in `r8`). -/
theorem cmpLeft_ok {s : State} {x : Nat} (hx : s.gpr .r8 = BitVec.ofNat 32 x) (h₁ : 1 ≤ x) (h₂ : x < 2 ^ 32) :
    WP isa (.block cmpLeft) s fun t => isa.eval .eq t = some (decide (x ≤ 64)) ∧
      (∀ r, r ≠ .r0 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold cmpLeft
  refine wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · show VG.Arm.eval .eq s₃ = _
    rw [eval_eq, z₃, u₂.gpr, u₁.gpr, hx]
    exact congrArg some (VG.Proof.Argon2.Arm.HPrime.le64_beq h₁ h₂)
  · rw [f₃.gpr, u₂.other _ hr, u₁.other _ hr]
  · rw [f₃.mem, u₂.mem, u₁.mem]
  · rw [f₃.rd, u₂.rd, u₁.rd]
  · rw [f₃.wr, u₂.wr, u₁.wr]
  · rw [f₃.sp, u₂.sp, u₁.sp]

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.HPrime.Pre s₀)
include hp

/-- `r1 := min(out_len, 64)`. -/
theorem choose_ok {s : State} (_b : VG.Proof.Argon2.Arm.HPrime.Body s₀ s) (o : VG.Proof.Argon2.Arm.HPrime.Out s₀ s []) :
    WP isa chooseLength s fun t => t.gpr .r1 = BitVec.ofNat 32 (min (VG.Proof.Argon2.Arm.HPrime.ol s₀) 64) ∧
      VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s t := by
  have hol := (s₀.gpr .r3).isLt
  have hpos := hp.ol_pos
  have l₀ : s.gpr .r8 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.HPrime.ol s₀) := by rw [o.left]; rfl
  unfold chooseLength
  refine WP.seq (wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ?_)
  have k₃ : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s s₃ := Keeps.same (fun r hr => by
      rw [f₃.gpr, u₂.other _ (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.1, u₁.other _ (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.1])
    (by rw [f₃.sp, u₂.sp, u₁.sp]) (by rw [f₃.mem, u₂.mem, u₁.mem]) (by rw [f₃.rd, u₂.rd, u₁.rd])
    (by rw [f₃.wr, u₂.wr, u₁.wr])
  have r8₃ : s₃.gpr .r8 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.HPrime.ol s₀) := by rw [k₃.gpr _ (by decide), l₀]
  refine WP.ite (decide (VG.Proof.Argon2.Arm.HPrime.ol s₀ ≤ 64)) (by
      show VG.Arm.eval .eq s₃ = _
      rw [eval_eq, z₃, u₂.gpr, u₁.gpr, l₀]; exact congrArg some (VG.Proof.Argon2.Arm.HPrime.le64_beq hpos hol))
    (fun h => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ⟨?_, ?_⟩)
    (fun h => wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ⟨?_, ?_⟩)
  · have : VG.Proof.Argon2.Arm.HPrime.ol s₀ ≤ 64 := by simpa using h
    rw [u₄.gpr, r8₃, Nat.min_eq_left this]
  · exact k₃.trans (Keeps.same (fun r hr => u₄.other r (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.1) u₄.sp u₄.mem u₄.rd u₄.wr)
  · have : 64 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀ := by simp at h; omega
    rw [u₄.gpr, Nat.min_eq_right this]; rfl
  · exact k₃.trans (Keeps.same (fun r hr => u₄.other r (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.1) u₄.sp u₄.mem u₄.rd u₄.wr)

end

/-! ## The steps of `first` -/

/-- The state before and between the steps of `first`: the body, no output
yet, and the input kept. -/
structure F0 (s₀ s : State) : Prop where
  body : VG.Proof.Argon2.Arm.HPrime.Body s₀ s
  out : VG.Proof.Argon2.Arm.HPrime.Out s₀ s []
  input : bytesAt s.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.inp s₀)) (VG.Proof.Argon2.Arm.HPrime.inl s₀) = bytesAt s₀.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.inp s₀)) (VG.Proof.Argon2.Arm.HPrime.inl s₀)

/-- The length of the first digest. -/
abbrev nF (s₀ : State) : Nat := min (VG.Proof.Argon2.Arm.HPrime.ol s₀) 64

/-- The input, on entry. -/
abbrev inB (s₀ : State) : List Byte := bytesAt s₀.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.inp s₀)) (VG.Proof.Argon2.Arm.HPrime.inl s₀)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.HPrime.Pre s₀)
include hp

theorem F0.keeps {s t : State} (h : VG.Proof.Argon2.Arm.HPrime.F0 s₀ s) (k : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s t) : VG.Proof.Argon2.Arm.HPrime.F0 s₀ t := by
  refine ⟨h.body.keeps hp k, h.out.keeps hp k, ?_⟩
  have hif := hp.in_fits
  have := k.bytes (R := VG.Proof.Argon2.Arm.HPrime.inR s₀) (by simp; omega)
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in.symm
  simp only at this
  rw [this, h.input]

theorem nF_pos : 1 ≤ VG.Proof.Argon2.Arm.HPrime.nF s₀ := by have := hp.ol_pos; simp only [VG.Proof.Argon2.Arm.HPrime.nF]; omega

theorem first_choose {s : State} (h : VG.Proof.Argon2.Arm.HPrime.F0 s₀ s) :
    WP isa chooseLength s fun t => VG.Proof.Argon2.Arm.HPrime.F0 s₀ t ∧ t.gpr .r1 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.HPrime.nF s₀) :=
  (VG.Proof.Argon2.Arm.HPrime.choose_ok hp h.body h.out).mono fun _ ⟨e, k⟩ => ⟨h.keeps hp k, e⟩

theorem first_init {s : State} (h : VG.Proof.Argon2.Arm.HPrime.F0 s₀ s ∧ s.gpr .r1 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.HPrime.nF s₀)) :
    WP isa VG.Impl.Argon2.Arm.HPrime.init s fun t => VG.Proof.Argon2.Arm.HPrime.F0 s₀ t ∧ Repr b (Spec.Blake2.init b (VG.Proof.Argon2.Arm.HPrime.nF s₀) 0) t.mem (VG.Proof.Argon2.Arm.HPrime.P s₀) [] := by
  have c := h.1.body.ctx hp
  refine (VG.Proof.Argon2.Arm.HPrime.init_ok c h.2 (VG.Proof.Argon2.Arm.HPrime.nF_pos hp) (Nat.min_le_right _ _)).mono fun t ⟨r, cs, rd, wr, sp, f⟩ => ⟨?_, r⟩
  refine h.1.keeps hp (Keeps.of_call cs sp rd wr f fun r hr => ?_)
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩

theorem pfx_cov {s : State} (b : VG.Proof.Argon2.Arm.HPrime.Body s₀ s) : Covers [⟨VG.Proof.Argon2.Arm.HPrime.P s₀ + BitVec.ofNat 64 832, 4⟩] s.wr := by
  rw [b.wr, hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.Argon2.Arm.HPrime.scrR s₀, by simp, 832, rfl, by simp⟩

theorem first_fixed {s : State}
    (h : VG.Proof.Argon2.Arm.HPrime.F0 s₀ s ∧ Repr b (Spec.Blake2.init b (VG.Proof.Argon2.Arm.HPrime.nF s₀) 0) s.mem (VG.Proof.Argon2.Arm.HPrime.P s₀) []) :
    WP isa (absorbFixed 832 4) s fun t => VG.Proof.Argon2.Arm.HPrime.F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (VG.Proof.Argon2.Arm.HPrime.nF s₀) 0) t.mem (VG.Proof.Argon2.Arm.HPrime.P s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀)) := by
  have hs := hp.scr_fits
  refine (VG.Proof.Argon2.Arm.HPrime.absorbFixed_ok (h.1.body.ctx hp) (offset := 832) (size := 4) (by decide) (by decide) (by omega)
    (by decide) (by decide) (by decide) (VG.Proof.Argon2.Arm.HPrime.pfx_cov hp h.1.body) (hp.stk_scr.sub_right (Offset.sub_base _ (by decide)))
    h.2).mono fun t ⟨r, k⟩ => ⟨h.1.keeps hp k, ?_⟩
  rw [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, h.1.body.pfx] at r
  exact r

theorem first_input {s : State}
    (h : VG.Proof.Argon2.Arm.HPrime.F0 s₀ s ∧ Repr b (Spec.Blake2.init b (VG.Proof.Argon2.Arm.HPrime.nF s₀) 0) s.mem (VG.Proof.Argon2.Arm.HPrime.P s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀))) :
    WP isa absorbInput s fun t => VG.Proof.Argon2.Arm.HPrime.F0 s₀ t ∧
      Repr b (Spec.Blake2.init b (VG.Proof.Argon2.Arm.HPrime.nF s₀) 0) t.mem (VG.Proof.Argon2.Arm.HPrime.P s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀) ++ VG.Proof.Argon2.Arm.HPrime.inB s₀) := by
  have hif := hp.in_fits
  have hil := (s₀.gpr .r1).isLt
  unfold absorbInput
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_)
  have o₄ : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have k₄ : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s s₄ := Keeps.same (fun r hr => o₄ r (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.2.1
      (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.2.2.1 (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.2.2.2.1 (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.2.2.2.2.1)
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have F₄ := h.1.keeps hp k₄
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have cnt₄ : s₄.gpr .r3 ++ s₄.gpr .r2 = BitVec.ofNat 64 (Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀)).length := by
    rw [Proof.Argon2.le32_length, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl
  have r9 : s₄.gpr .r9 = VG.Proof.Argon2.Arm.HPrime.inp s₀ := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.1.body.r5]
  have r10 : (s₄.gpr .r10).toNat = VG.Proof.Argon2.Arm.HPrime.inl s₀ := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.1.body.r6]
  have hDc : Covers [⟨State.addr (VG.Proof.Argon2.Arm.HPrime.inp s₀), VG.Proof.Argon2.Arm.HPrime.inl s₀⟩] (s₄.rd ++ s₄.wr) := by
    rw [F₄.body.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Argon2.Arm.HPrime.inR s₀, by simp, 0, by simp, by simp⟩
  refine (VG.Proof.Argon2.Arm.HPrime.update_ok (F₄.body.ctx hp) (h0 := Spec.Blake2.init Spec.Blake2.b (VG.Proof.Argon2.Arm.HPrime.nF s₀) 0) r9 r10 hif hDc
    (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in (by rw [m₄]; exact h.2) cnt₄
    (by rw [Proof.Argon2.le32_length]; omega)).mono fun s₅ ⟨r₅, cs₅, rd₅, wr₅, sp₅, f₅⟩ => ?_
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
    (h : VG.Proof.Argon2.Arm.HPrime.F0 s₀ s ∧ Repr b (Spec.Blake2.init b (VG.Proof.Argon2.Arm.HPrime.nF s₀) 0) s.mem (VG.Proof.Argon2.Arm.HPrime.P s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀) ++ VG.Proof.Argon2.Arm.HPrime.inB s₀)) :
    WP isa finishInput s fun t => VG.Proof.Argon2.Arm.HPrime.F0 s₀ t ∧
      (VG.Proof.Argon2.Arm.HPrime.digest s₀ t).take (VG.Proof.Argon2.Arm.HPrime.nF s₀) = Spec.Argon2.H (VG.Proof.Argon2.Arm.HPrime.nF s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀) ++ VG.Proof.Argon2.Arm.HPrime.inB s₀) := by
  have hif := hp.in_fits
  have hil := (s₀.gpr .r1).isLt
  unfold finishInput
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_adds (op2_imm (by decide)) fun s₂ u₂ c₂ =>
    wp_adc (op2_imm (by decide)) fun s₃ u₃ _ => WP.block_nil ?_)
  have o₃ : ∀ r, r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h2, u₂.other _ h1, u₁.other _ h2]
  have k₃ : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s s₃ := Keeps.same (fun r hr => o₃ r (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.2.1
      (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.2.2.1)
    (by rw [u₃.sp, u₂.sp, u₁.sp]) (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₃.wr, u₂.wr, u₁.wr])
  have F₃ := h.1.keeps hp k₃
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have r6 : s₁.gpr .r6 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.HPrime.inl s₀) := by rw [u₁.other _ (by decide), h.1.body.r6]; simp
  have cnt : s₃.gpr .r3 ++ s₃.gpr .r2 = BitVec.ofNat 64 (Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀) ++ VG.Proof.Argon2.Arm.HPrime.inB s₀).length := by
    rw [u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide), u₁.gpr, c₂, r6, List.length_append,
      Proof.Argon2.le32_length]
    simp only [VG.Proof.Argon2.Arm.HPrime.inB, bytesAt, List.length_map, List.length_range]
    rw [show 4 + VG.Proof.Argon2.Arm.HPrime.inl s₀ = VG.Proof.Argon2.Arm.HPrime.inl s₀ + 4 by omega]
    exact VG.Proof.Argon2.Arm.HPrime.count4 _ hil
  refine (VG.Proof.Argon2.Arm.HPrime.finalize_ok (F₃.body.ctx hp) (by rw [m₃]; exact h.2) cnt
    (by simp only [List.length_append, Proof.Argon2.le32_length, VG.Proof.Argon2.Arm.HPrime.inB, bytesAt, List.length_map,
      List.length_range]; omega)).mono ?_
  rintro t ⟨d, cs, rd, wr, sp, f⟩
  refine ⟨F₃.keeps hp (Keeps.of_call cs sp rd wr f fun r hr => ?_), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · show (bytesAt t.mem (VG.Proof.Argon2.Arm.HPrime.P s₀ + 768) 64).take _ = _
    rw [d, Proof.Argon2.H_stream]

/-- `first` hashes the length prefix and the input. -/
theorem first_ok {s : State} (h : VG.Proof.Argon2.Arm.HPrime.F0 s₀ s) :
    WP isa first s fun t => VG.Proof.Argon2.Arm.HPrime.F0 s₀ t ∧
      (VG.Proof.Argon2.Arm.HPrime.digest s₀ t).take (VG.Proof.Argon2.Arm.HPrime.nF s₀) = Spec.Argon2.H (VG.Proof.Argon2.Arm.HPrime.nF s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀) ++ VG.Proof.Argon2.Arm.HPrime.inB s₀) := by
  unfold first
  exact WP.seq ((VG.Proof.Argon2.Arm.HPrime.first_choose hp h).mono fun _ h₁ => WP.seq ((VG.Proof.Argon2.Arm.HPrime.first_init hp h₁).mono fun _ h₂ =>
    WP.seq ((VG.Proof.Argon2.Arm.HPrime.first_fixed hp h₂).mono fun _ h₃ => WP.seq ((VG.Proof.Argon2.Arm.HPrime.first_input hp h₃).mono fun _ h₄ =>
      VG.Proof.Argon2.Arm.HPrime.first_finish hp h₄))))

end

end VG.Proof.Argon2.Arm.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.HPrime.Finish`. -/
section

/-!
# Argon2 H′ on ARMv7: the output from the first digest

`chain_ok`: after the first prefix V₁[0, 32) of a long output, each iteration
hashes the digest again and emits the prefix of the new one, while more than
64 bytes are left. `finish_ok`: `finishOutput` writes H′ to the output, from
the first digest: the digest itself for at most 64 bytes, and otherwise its
prefix, the chain and the last hash (`extend_ok`), of the 33 to 64 bytes left.
-/

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
    (VG.Proof.Argon2.Arm.HPrime.chainOut V j).length = 32 + 32 * j := by
  simp only [VG.Proof.Argon2.Arm.HPrime.chainOut, List.length_append, List.length_take, hV, Proof.Argon2.chainPrefixes_length]
  omega

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.HPrime.Pre s₀)
include hp

omit hp in
/-- `cmpLeft` on the output `xs`. -/
theorem cmp_ok {s : State} {xs : List Byte} (o : VG.Proof.Argon2.Arm.HPrime.Out s₀ s xs) (hl : xs.length < VG.Proof.Argon2.Arm.HPrime.ol s₀) :
    WP isa (.block cmpLeft) s fun t => isa.eval .eq t = some (decide (VG.Proof.Argon2.Arm.HPrime.ol s₀ - xs.length ≤ 64)) ∧
      VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s t ∧ t.mem = s.mem := by
  have hol := (s₀.gpr .r3).isLt
  refine (VG.Proof.Argon2.Arm.HPrime.cmpLeft_ok o.left (by omega) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hol)).mono
    fun t ⟨e, g, m, rd, wr, sp⟩ => ⟨e, Keeps.same (fun r hr => g r (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).1) sp m rd wr, m⟩

/-- What the chain keeps between iterations. -/
structure ChainInv (s₀ : State) (e : BitVec 32) (V : List Byte) (j : Nat) (s : State) : Prop where
  body : VG.Proof.Argon2.Arm.HPrime.Body s₀ s
  r11 : s.gpr .r11 = e
  out : VG.Proof.Argon2.Arm.HPrime.Out s₀ s (VG.Proof.Argon2.Arm.HPrime.chainOut V j)
  digest : VG.Proof.Argon2.Arm.HPrime.digest s₀ s = chainDigest j V

/-- One iteration. -/
theorem iter_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : VG.Proof.Argon2.Arm.HPrime.ChainInv s₀ e V j s) (hl : 32 + 32 * j + 32 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀) (hl' : 32 + 32 * (j + 1) < VG.Proof.Argon2.Arm.HPrime.ol s₀) :
    WP isa (.seq (.block [.mov .r1 (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft)))) s
      fun t => VG.Proof.Argon2.Arm.HPrime.ChainInv s₀ e V (j + 1) t ∧
        isa.eval .eq t = some (decide (VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * (j + 1)) ≤ 64)) := by
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil ?_)
  have k₁ : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s s₁ := Keeps.same (fun r hr => u₁.other r (by
    simp only [VG.Proof.Argon2.Arm.HPrime.kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₁.sp u₁.mem u₁.rd u₁.wr
  have b₁ := h.body.keeps hp k₁
  refine WP.seq ((VG.Proof.Argon2.Arm.HPrime.next_ok (b₁.ctx hp) (n := 64) u₁.gpr (by decide) (by decide)).mono
    fun s₂ ⟨d₂, k₂⟩ => ?_)
  have K₂ := k₁.trans k₂
  have b₂ := h.body.keeps hp K₂
  have o₂ := h.out.keeps hp K₂
  have hlen := VG.Proof.Argon2.Arm.HPrime.chainOut_length hV j
  refine WP.seq ((VG.Proof.Argon2.Arm.HPrime.emit_ok hp b₂ o₂ (by rw [hlen]; exact hl)).mono fun s₃ ⟨b₃, e₃, o₃, d₃⟩ => ?_)
  have dg : VG.Proof.Argon2.Arm.HPrime.digest s₀ s₂ = chainDigest (j + 1) V := by
    rw [VG.Proof.Argon2.Arm.HPrime.chainDigest_succ', ← h.digest, Proof.Argon2.H_stream,
      List.take_of_length_le (by rw [VG.Proof.Argon2.Arm.HPrime.finalHash_length])]
    rw [u₁.mem] at d₂
    exact d₂
  have xs₃ : VG.Proof.Argon2.Arm.HPrime.chainOut V j ++ (VG.Proof.Argon2.Arm.HPrime.digest s₀ s₂).take 32 = VG.Proof.Argon2.Arm.HPrime.chainOut V (j + 1) := by
    rw [dg, VG.Proof.Argon2.Arm.HPrime.chainDigest_succ', VG.Proof.Argon2.Arm.HPrime.chainOut, VG.Proof.Argon2.Arm.HPrime.chainOut, VG.Proof.Argon2.Arm.HPrime.chainPrefixes_succ', List.append_assoc]
  rw [xs₃] at o₃
  refine (VG.Proof.Argon2.Arm.HPrime.cmp_ok o₃ (by rw [VG.Proof.Argon2.Arm.HPrime.chainOut_length hV]; exact hl')).mono fun t ⟨cf, k, m⟩ =>
    ⟨⟨b₃.keeps hp k, ?_, o₃.keeps hp k, ?_⟩, ?_⟩
  · rw [k.gpr _ (by decide), e₃, K₂.gpr _ (by decide), h.r11]
  · show bytesAt _ _ _ = _
    rw [m]
    exact d₃.trans dg
  · rw [cf, VG.Proof.Argon2.Arm.HPrime.chainOut_length hV]

/-- The chain: iterations while more than 64 bytes are left. -/
theorem chain_ok {e : BitVec 32} {V : List Byte} (hV : V.length = 64) {j : Nat} {s : State}
    (h : VG.Proof.Argon2.Arm.HPrime.ChainInv s₀ e V j s) (hl : 65 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j)) :
    WP isa chain s fun t => ∃ j', VG.Proof.Argon2.Arm.HPrime.ChainInv s₀ e V j' t ∧ 33 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j') ∧
      VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j') ≤ 64 ∧ 32 + 32 * j' ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀ := by
  unfold chain
  refine WP.loop (M := isa) (fun (m : Nat) (t : State) => ∃ j', m = VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j') ∧
    VG.Proof.Argon2.Arm.HPrime.ChainInv s₀ e V j' t ∧ 65 ≤ m) ?_ (VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j)) s ⟨j, rfl, h, hl⟩
  rintro m t ⟨j', rfl, hi, hm⟩
  refine (VG.Proof.Argon2.Arm.HPrime.iter_ok hp hV hi (by omega) (by omega)).mono fun u ⟨hu, cf⟩ => ?_
  have cf' : isa.eval .ne u = some (!decide (VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * (j' + 1)) ≤ 64)) := by
    have cf2 : VG.Arm.eval .eq u = _ := cf
    show VG.Arm.eval .ne u = _
    rw [MdStream.Arm.eval_eq, Option.some.injEq] at cf2
    rw [MdStream.Arm.eval_ne, cf2]
  by_cases hc : VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * (j' + 1)) ≤ 64
  · refine .inl ⟨by rw [cf']; simp [hc], j' + 1, hu, by omega, by omega, by omega⟩
  · refine .inr ⟨by rw [cf']; simp [hc], _, by omega, j' + 1, rfl, hu, by omega⟩

/-- What the chain leaves: the output after `j` iterations and the last hash. -/
def Extended (s₀ : State) (e : BitVec 32) (V : List Byte) (t : State) : Prop :=
  ∃ j, VG.Proof.Argon2.Arm.HPrime.Body s₀ t ∧ t.gpr .r11 = e ∧ VG.Proof.Argon2.Arm.HPrime.Out s₀ t (VG.Proof.Argon2.Arm.HPrime.chainOut V j) ∧
    (VG.Proof.Argon2.Arm.HPrime.digest s₀ t).take (VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j)) =
      Spec.Argon2.H (VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j)) (chainDigest j V) ∧
    33 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j) ∧ VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀

theorem extend_ok {s : State} (b : VG.Proof.Argon2.Arm.HPrime.Body s₀ s) (o : VG.Proof.Argon2.Arm.HPrime.Out s₀ s []) (hol : 65 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀) :
    WP isa extendDigest s (VG.Proof.Argon2.Arm.HPrime.Extended s₀ (s.gpr .r11) (VG.Proof.Argon2.Arm.HPrime.digest s₀ s)) := by
  have hV : (VG.Proof.Argon2.Arm.HPrime.digest s₀ s).length = 64 := by simp [VG.Proof.Argon2.Arm.HPrime.digest, bytesAt]
  unfold extendDigest
  refine WP.seq ((VG.Proof.Argon2.Arm.HPrime.emit_ok hp b o (by simp only [List.length_nil]; omega)).mono
    fun s₁ ⟨b₁, e₁, o₁, d₁⟩ => ?_)
  rw [List.nil_append, show (VG.Proof.Argon2.Arm.HPrime.digest s₀ s).take 32 = VG.Proof.Argon2.Arm.HPrime.chainOut (VG.Proof.Argon2.Arm.HPrime.digest s₀ s) 0 by
    simp [VG.Proof.Argon2.Arm.HPrime.chainOut, chainPrefixes]] at o₁
  have i₁ : VG.Proof.Argon2.Arm.HPrime.ChainInv s₀ (s.gpr .r11) (VG.Proof.Argon2.Arm.HPrime.digest s₀ s) 0 s₁ := ⟨b₁, e₁, o₁, d₁⟩
  refine WP.seq ((VG.Proof.Argon2.Arm.HPrime.cmp_ok o₁ (by rw [VG.Proof.Argon2.Arm.HPrime.chainOut_length hV]; omega)).mono fun s₂ ⟨cf₂, k₂, m₂⟩ => ?_)
  rw [VG.Proof.Argon2.Arm.HPrime.chainOut_length hV] at cf₂
  have i₂ : VG.Proof.Argon2.Arm.HPrime.ChainInv s₀ (s.gpr .r11) (VG.Proof.Argon2.Arm.HPrime.digest s₀ s) 0 s₂ :=
    ⟨b₁.keeps hp k₂, (k₂.gpr _ (by decide)).trans e₁, o₁.keeps hp k₂,
      by show bytesAt _ _ _ = _; rw [m₂]; exact d₁⟩
  have hIte : WP isa (.ite .eq (.block []) chain) s₂ fun t => ∃ j, VG.Proof.Argon2.Arm.HPrime.ChainInv s₀ (s.gpr .r11) (VG.Proof.Argon2.Arm.HPrime.digest s₀ s) j t ∧
      33 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j) ∧ VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀ := by
    refine WP.ite (decide (VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * 0) ≤ 64)) cf₂ (fun h => WP.block_nil ⟨0, i₂, ?_⟩)
      (fun h => (VG.Proof.Argon2.Arm.HPrime.chain_ok hp hV i₂ ?_).mono fun t h => h)
    · simp only [decide_eq_true_eq] at h; omega
    · simp only [decide_eq_false_iff_not] at h; omega
  refine WP.seq (hIte.mono fun s₃ ⟨j, i₃, l₁, l₂, l₃⟩ => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_)
  have k₄ : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s₃ s₄ := Keeps.same (fun r hr => u₄.other r (by
    simp only [VG.Proof.Argon2.Arm.HPrime.kept, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) u₄.sp u₄.mem u₄.rd u₄.wr
  have b₄ := i₃.body.keeps hp k₄
  have r1₄ : s₄.gpr .r1 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j)) := by
    rw [u₄.gpr, i₃.out.left, VG.Proof.Argon2.Arm.HPrime.chainOut_length hV]
  refine (VG.Proof.Argon2.Arm.HPrime.next_ok (b₄.ctx hp) r1₄ (by omega) l₂).mono fun t ⟨d, k⟩ => ?_
  have K := k₄.trans k
  refine ⟨j, i₃.body.keeps hp K, by rw [K.gpr _ (by decide), i₃.r11], i₃.out.keeps hp K, ?_, l₁, l₂, l₃⟩
  rw [Proof.Argon2.H_stream, ← i₃.digest]
  rw [u₄.mem] at d
  exact congrArg (List.take _) d

/-- `finishOutput` writes H′ of the input `I` from its first digest. -/
theorem finish_ok {s : State} (b : VG.Proof.Argon2.Arm.HPrime.Body s₀ s) (o : VG.Proof.Argon2.Arm.HPrime.Out s₀ s []) {I : List Byte}
    (hd : (VG.Proof.Argon2.Arm.HPrime.digest s₀ s).take (min (VG.Proof.Argon2.Arm.HPrime.ol s₀) 64) =
      Spec.Argon2.H (min (VG.Proof.Argon2.Arm.HPrime.ol s₀) 64) (Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀) ++ I)) :
    WP isa finishOutput s fun t => VG.Proof.Argon2.Arm.HPrime.Body s₀ t ∧ t.gpr .r11 = s.gpr .r11 ∧
      bytesAt t.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.op s₀)) (VG.Proof.Argon2.Arm.HPrime.ol s₀) = Spec.Argon2.hPrime (VG.Proof.Argon2.Arm.HPrime.ol s₀) I := by
  have hpos := hp.ol_pos
  have hV : (VG.Proof.Argon2.Arm.HPrime.digest s₀ s).length = 64 := by simp [VG.Proof.Argon2.Arm.HPrime.digest, bytesAt]
  unfold finishOutput
  refine WP.seq ((VG.Proof.Argon2.Arm.HPrime.cmp_ok o (by simp only [List.length_nil]; omega)).mono fun s₁ ⟨cf₁, k₁, m₁⟩ => ?_)
  simp only [List.length_nil, Nat.sub_zero] at cf₁
  have b₁ := b.keeps hp k₁
  have o₁ := o.keeps hp k₁
  have d₁ : VG.Proof.Argon2.Arm.HPrime.digest s₀ s₁ = VG.Proof.Argon2.Arm.HPrime.digest s₀ s := by show bytesAt _ _ _ = _; rw [m₁]
  have hIte : WP isa (.ite .eq (.block []) extendDigest) s₁ fun t => VG.Proof.Argon2.Arm.HPrime.Body s₀ t ∧ t.gpr .r11 = s.gpr .r11 ∧
      ∃ xs, VG.Proof.Argon2.Arm.HPrime.Out s₀ t xs ∧ xs.length < VG.Proof.Argon2.Arm.HPrime.ol s₀ ∧ VG.Proof.Argon2.Arm.HPrime.ol s₀ - xs.length ≤ 64 ∧
        xs ++ (VG.Proof.Argon2.Arm.HPrime.digest s₀ t).take (VG.Proof.Argon2.Arm.HPrime.ol s₀ - xs.length) = Spec.Argon2.hPrime (VG.Proof.Argon2.Arm.HPrime.ol s₀) I := by
    refine WP.ite (decide (VG.Proof.Argon2.Arm.HPrime.ol s₀ ≤ 64)) cf₁ (fun h => WP.block_nil ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      refine ⟨b₁, k₁.gpr _ (by decide), [], o₁, by simp only [List.length_nil]; omega,
        by simp only [List.length_nil]; omega, ?_⟩
      rw [Nat.min_eq_left (by omega)] at hd
      rw [List.nil_append, List.length_nil, Nat.sub_zero, d₁, hd]
      simp only [Spec.Argon2.hPrime, eq_true (by omega : ol s₀ ≤ 64), ite_true]
    · simp only [decide_eq_false_iff_not] at h
      refine (VG.Proof.Argon2.Arm.HPrime.extend_ok hp b₁ o₁ (by omega)).mono fun t ⟨j, bt, et, ot, dt, l₁, l₂, l₃⟩ =>
        ⟨bt, et.trans (k₁.gpr _ (by decide)), _, ot, ?_, ?_, ?_⟩
      · rw [VG.Proof.Argon2.Arm.HPrime.chainOut_length (by rw [d₁]; exact hV)]; omega
      · rw [VG.Proof.Argon2.Arm.HPrime.chainOut_length (by rw [d₁]; exact hV)]; omega
      · have V₁ : VG.Proof.Argon2.Arm.HPrime.digest s₀ s₁ = Spec.Argon2.H 64 (Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀) ++ I) := by
          rw [d₁, ← List.take_of_length_le (l := VG.Proof.Argon2.Arm.HPrime.digest s₀ s) (i := 64) (by rw [hV]),
            ← Nat.min_eq_right (by omega : 64 ≤ ol s₀), hd]
        rw [VG.Proof.Argon2.Arm.HPrime.chainOut_length (by rw [d₁]; exact hV), dt, VG.Proof.Argon2.Arm.HPrime.chainOut, ← Proof.Argon2.longHash_chain, V₁]
        have hr : (VG.Proof.Argon2.Arm.HPrime.ol s₀ + 31) / 32 - 2 = j + 1 := by omega
        simp only [Spec.Argon2.hPrime, eq_false (by omega : ¬ ol s₀ ≤ 64), ite_false]
        rw [hr, show VG.Proof.Argon2.Arm.HPrime.ol s₀ - 32 * (j + 1) = VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j) by omega]
  refine WP.seq (hIte.mono fun s₂ ⟨b₂, e₂, xs, o₂, l₁, l₂, h₂⟩ => ?_)
  refine (VG.Proof.Argon2.Arm.HPrime.copyRemaining_ok hp b₂ o₂ l₁ l₂).mono fun t ⟨bt, et, ht⟩ => ⟨bt, et.trans e₂, ?_⟩
  rw [ht, h₂]

end

end VG.Proof.Argon2.Arm.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.HPrime.Correct`. -/
section

/-!
# Argon2 H′ on ARMv7: correctness

`setup_ok` saves the caller's registers in `scratch`, keeps the input, the
output pointer and the bytes left in registers and the length prefix in
`scratch`; `correct` composes it with `first_ok`, `finish_ok` and the
restore of the registers.
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (setup restore first finishOutput saved baseSlot pfxOff)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_str wp_ldrSp op2_reg)

section
variable {s₀ : State} (hp : VG.Proof.Argon2.Arm.HPrime.Pre s₀)
include hp

theorem arg_in : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 0)) 4 := by
  refine ⟨VG.Proof.Argon2.Arm.HPrime.argR s₀, by simp [hp.rd], ?_⟩
  simp [stackArgAddr, Region.Contains]

theorem scr_w {d : Nat} (hd : d + 4 ≤ 16384) : InRegions s₀.wr (VG.Proof.Argon2.Arm.HPrime.P s₀ + BitVec.ofNat 64 d) 4 :=
  ⟨VG.Proof.Argon2.Arm.HPrime.scrR s₀, by simp [hp.wr], Offset.contains_base _ hd (by omega)⟩

/-- The state after `setup`. -/
theorem setup_ok : WP isa (.block setup) s₀ fun t => VG.Proof.Argon2.Arm.HPrime.Body s₀ t ∧ VG.Proof.Argon2.Arm.HPrime.Out s₀ t [] ∧
    Frame [VG.Proof.Argon2.Arm.HPrime.scrR s₀] s₀.mem t.mem := by
  have hs := hp.scr_fits
  unfold setup
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (by decide) rfl (VG.Proof.Argon2.Arm.HPrime.arg_in hp) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .r12 = VG.Proof.Argon2.Arm.HPrime.scr s₀ := by rw [u₁.gpr]; rfl
  refine Spill.save_slots_ok (b := .r12) VG.Proof.Argon2.Arm.HPrime.saveList_slots (by rw [e₁]; omega)
    (fun d h₁ h₂ => by rw [e₁, u₁.wr]; exact VG.Proof.Argon2.Arm.HPrime.scr_w hp (by omega)) ?_
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  have r4₆ : s₆.gpr .r4 = VG.Proof.Argon2.Arm.HPrime.scr s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    exact e₁
  have w₆ : InRegions s₆.wr (State.addr (VG.Proof.Argon2.Arm.HPrime.scr s₀) + BitVec.ofNat 64 pfxOff) 4 := by
    rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    exact VG.Proof.Argon2.Arm.HPrime.scr_w hp (by decide)
  refine wp_str (by decide) (by rw [r4₆]; exact VG.Proof.Argon2.Arm.HPrime.scr_addr hp (by decide)) w₆ fun t u => WP.block_nil ?_
  -- Values.
  have g₆ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → s₆.gpr r = s₁.gpr r := fun r h4 h5 h6 h7 h8 => by
    rw [u₆.other _ h8, u₅.other _ h7, u₄.other _ h6, u₃.other _ h5, u₂.other _ h4]
  have m₆ : s₆.mem = Spill.saveMem s₁.mem (VG.Proof.Argon2.Arm.HPrime.P s₀) s₁.gpr VG.Proof.Argon2.Arm.HPrime.saveList := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, e₁]
  have gl : ∀ p ∈ VG.Proof.Argon2.Arm.HPrime.saveList, s₁.gpr p.1 = s₀.gpr p.1 := fun p hpm => u₁.other _ (by
    simp only [VG.Proof.Argon2.Arm.HPrime.saveList, saved, baseSlot, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hv : (s₆.gpr .r3) = s₀.gpr .r3 := by rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide),
    u₁.other _ (by decide)]
  have mt : t.mem = (Spill.saveMem s₀.mem (VG.Proof.Argon2.Arm.HPrime.P s₀) s₀.gpr VG.Proof.Argon2.Arm.HPrime.saveList).writeW (VG.Proof.Argon2.Arm.HPrime.P s₀ + BitVec.ofNat 64 pfxOff)
      (s₀.gpr .r3) := by
    rw [u.mem, m₆, hv, u₁.mem, Spill.saveMem_congr _ _ _ gl]
  have Ft : Frame [VG.Proof.Argon2.Arm.HPrime.scrR s₀] s₀.mem t.mem := by
    rw [mt]
    exact (Spill.saveMem_frame_of _ _ (List.mem_singleton_self (VG.Proof.Argon2.Arm.HPrime.scrR s₀)) _ _ fun p hpm => by
      have := saveList_slots.bound hpm
      exact Offset.contains_base _ (by omega) (by omega)).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by decide) (by decide))
  have gt : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → t.gpr r = s₀.gpr r :=
    fun r h4 h5 h6 h7 h8 h12 => by rw [u.gpr, g₆ r h4 h5 h6 h7 h8, u₁.other _ h12]
  refine ⟨⟨by rw [u.gpr, r4₆], ?_, ?_, ?_, ?_, ?_, Ft.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩,
      fun q hq => ?_, ?_⟩, ⟨?_, ?_, rfl, Nat.zero_le _⟩, Ft⟩
  · rw [u.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · have hb := saveList_slots.bound hq
    rw [mt, Mem.readW_writeW_sep (Offset.sep _ (by simp only [pfxOff]; omega) (by omega) (by decide)) (by decide)]
    exact Spill.saveMem_saved _ _ _ _ VG.Proof.Argon2.Arm.HPrime.saveList_slots q hq
  · rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (.inl rfl), mt,
      show VG.Proof.Argon2.Arm.HPrime.P s₀ + 832 = VG.Proof.Argon2.Arm.HPrime.P s₀ + BitVec.ofNat 64 pfxOff from rfl, Mem.readW_writeW_self32, Spec.Argon2.le32,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [u.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]; simp
  · rw [u.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]; simp [VG.Proof.Argon2.Arm.HPrime.ol]

theorem correct : WP isa Impl.Argon2.Arm.HPrime.code s₀ fun t =>
    (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ t.sp = s₀.sp ∧ hPrimeArm.post s₀ t := by
  have hif := hp.in_fits
  have hs := hp.scr_fits
  unfold Impl.Argon2.Arm.HPrime.code
  refine WP.seq ((VG.Proof.Argon2.Arm.HPrime.setup_ok hp).mono fun s₁ ⟨b₁, o₁, F₁⟩ => ?_)
  have hin : bytesAt s₁.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.inp s₀)) (VG.Proof.Argon2.Arm.HPrime.inl s₀) = bytesAt s₀.mem (State.addr (VG.Proof.Argon2.Arm.HPrime.inp s₀)) (VG.Proof.Argon2.Arm.HPrime.inl s₀) :=
    Proof.Blake2.bytesAt_congr fun i hi => F₁.bytes (R := VG.Proof.Argon2.Arm.HPrime.inR s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega) hi
  refine WP.seq ((VG.Proof.Argon2.Arm.HPrime.first_ok hp ⟨b₁, o₁, hin⟩).mono fun s₂ ⟨⟨b₂, o₂, _⟩, d₂⟩ => ?_)
  refine WP.seq ((VG.Proof.Argon2.Arm.HPrime.finish_ok hp b₂ o₂ d₂).mono fun s₃ ⟨b₃, _, h₃⟩ => ?_)
  unfold restore
  rw [← List.append_nil (List.map _ _)]
  have sv : Spill.Saved s₃.mem (State.addr (s₃.gpr .r4)) s₀.gpr (saved ++ [(.r4, baseSlot)]) := by
    rw [b₃.r4]
    intro p hpm
    exact b₃.saved p (by
      simp only [List.mem_append, List.mem_singleton] at hpm
      rcases hpm with hpm | rfl
      · exact List.mem_cons_of_mem _ hpm
      · exact List.mem_cons_self)
  refine Spill.restoreBase_slots_ok (lo := 840) (hi := 876) (by decide) (by decide) (g := s₀.gpr)
    (by rw [b₃.r4]; omega)
    (fun d h₁ h₂ => by rw [b₃.r4, b₃.rd, b₃.wr]; exact VG.Proof.Sha512.Arm.mem_rd (VG.Proof.Argon2.Arm.HPrime.scr_w hp (by omega))) sv
    fun t ht ho hm hrd hwr hsp => WP.block_nil ⟨fun r hr => ?_, hsp.trans b₃.sp, ?_⟩
  · exact Spill.restored_of ht (by decide) r hr
  · show bytesAt t.mem _ _ = _
    rw [hm]; exact h₃

end

end VG.Proof.Argon2.Arm.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.HPrime.OutputCT`. -/
section

/-!
# Argon2 H′ on ARMv7: the output, in two runs

Two runs of H′ with the same public data (`Same`: the stack pointer and the
arguments) write their output through the same addresses (`copy_rel`,
`emit_rel`, `copyRemaining_rel`, from states with the same number of output
bytes written), take the same branches (the output length decides them) and
the same number of chain iterations: `finishOutput_rel`.
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (copy copyLoop emitPrefix copyRemaining next cmpLeft chain extendDigest
  finishOutput)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_reg op2_imm)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

/-- The public data of two runs. -/
structure Same (s₀ s₀' : State) : Prop where
  sp : VG.Proof.Argon2.Arm.HPrime.sp₀ s₀' = VG.Proof.Argon2.Arm.HPrime.sp₀ s₀
  r0 : s₀'.gpr .r0 = s₀.gpr .r0
  r1 : s₀'.gpr .r1 = s₀.gpr .r1
  r2 : s₀'.gpr .r2 = s₀.gpr .r2
  r3 : s₀'.gpr .r3 = s₀.gpr .r3
  scr : VG.Proof.Argon2.Arm.HPrime.scr s₀' = VG.Proof.Argon2.Arm.HPrime.scr s₀

theorem Same.of_pub {s₀ s₀' : State} (h : hPrimeArm.pub s₀ s₀') : VG.Proof.Argon2.Arm.HPrime.Same s₀ s₀' :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm⟩

theorem Same.ol_eq {s₀ s₀' : State} (q : VG.Proof.Argon2.Arm.HPrime.Same s₀ s₀') : VG.Proof.Argon2.Arm.HPrime.ol s₀' = VG.Proof.Argon2.Arm.HPrime.ol s₀ := by
  show (s₀'.gpr .r3).toNat = (s₀.gpr .r3).toNat; rw [q.r3]

theorem Same.inl_eq {s₀ s₀' : State} (q : VG.Proof.Argon2.Arm.HPrime.Same s₀ s₀') : VG.Proof.Argon2.Arm.HPrime.inl s₀' = VG.Proof.Argon2.Arm.HPrime.inl s₀ := by
  show (s₀'.gpr .r1).toNat = (s₀.gpr .r1).toNat; rw [q.r1]

/-- A register write outside `kept` keeps what the hash macros keep. -/
theorem keeps_upd {B SP : BitVec 32} {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v)
    (hd : d ∉ VG.Proof.Argon2.Arm.HPrime.kept) : VG.Proof.Argon2.Arm.HPrime.Keeps B SP s t :=
  Keeps.same (fun r hr => u.other r fun h => hd (h ▸ hr)) u.sp u.mem u.rd u.wr

/-- Two runs agree on the registers the body keeps. -/
theorem agree_body {s₀ s₀' : State} (q : VG.Proof.Argon2.Arm.HPrime.Same s₀ s₀') {t₁ t₂ : State} (b₁ : VG.Proof.Argon2.Arm.HPrime.Body s₀ t₁)
    (b₂ : VG.Proof.Argon2.Arm.HPrime.Body s₀' t₂) : ∀ r ∈ [Reg.r4, .r5, .r6], t₁.gpr r = t₂.gpr r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [b₁.r4, b₂.r4, q.scr]
  · rw [b₁.r5, b₂.r5]; exact q.r0.symm
  · rw [b₁.r6, b₂.r6, q.r1]

/-- The code taint checks from nothing public, in two runs. -/
theorem rel_none {P : State → State → Prop} {c : Prog isa}
    (hc : ∃ hc, (VG.Taint.check taint (Taint.ofRegs []) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun _ h => nomatch h) hc

theorem rel_nil {P Q : State → State → Prop} (h : ∀ x y, P x y → Q x y) : RelCT isa P (.block []) Q :=
  ((VG.Proof.Argon2.Arm.HPrime.rel_none (P := P) ⟨_, by taint_decide⟩).wpDep (F := fun s t => t = s)
    fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, _, _, hp, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h _ _ hp

/-- `eval .ne`, from `eval .eq`. -/
theorem ne_of_eq {t : State} {p : Prop} [Decidable p] (h : isa.eval .eq t = some (decide p)) :
    isa.eval .ne t = some (!decide p) := by
  have h' : VG.Arm.eval .eq t = _ := h
  rw [MdStream.Arm.eval_eq, Option.some.injEq] at h'
  show VG.Arm.eval .ne t = _
  rw [MdStream.Arm.eval_ne, h']

/-! ## `copy` -/

/-- What `copy` needs: the body, `k` bytes of output written, and `n` to copy. -/
def CopyIn (s₀ : State) (k n : Nat) (s : State) : Prop :=
  VG.Proof.Argon2.Arm.HPrime.Body s₀ s ∧ s.gpr .r7 = VG.Proof.Argon2.Arm.HPrime.op s₀ + BitVec.ofNat 32 k ∧ s.gpr .r10 = BitVec.ofNat 32 n

/-- The registers of the copy loop. -/
def CopyRegs (s₀ : State) (k n : Nat) (t : State) : Prop :=
  t.gpr .r9 = VG.Proof.Argon2.Arm.HPrime.scr s₀ + 768 ∧ t.gpr .r7 = VG.Proof.Argon2.Arm.HPrime.op s₀ + BitVec.ofNat 32 k ∧ t.gpr .r10 = BitVec.ofNat 32 n

theorem copy_blk {s₀ : State} {k n : Nat} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.CopyIn s₀ k n s) :
    WP isa (.block [.dp .add .r9 .r4 (.imm 768)]) s (VG.Proof.Argon2.Arm.HPrime.CopyRegs s₀ k n) := by
  obtain ⟨b, hk, hn⟩ := h
  exact wp_add (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil
    ⟨by rw [u₁.gpr, b.r4], by rw [u₁.other _ (by decide), hk], by rw [u₁.other _ (by decide), hn]⟩

theorem copy_rel {s₀ s₀' : State} (q : VG.Proof.Argon2.Arm.HPrime.Same s₀ s₀') {k n : Nat} :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.Arm.HPrime.CopyIn s₀ k n t₁ ∧ VG.Proof.Argon2.Arm.HPrime.CopyIn s₀' k n t₂) copy fun _ _ => True := by
  unfold copy
  refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => VG.Proof.Argon2.Arm.HPrime.copy_blk h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.copy_blk h)) ?_
  exact RelCT.taint (A := taint) (Taint.ofRegs [.r9, .r7, .r10])
    (fun t₁ t₂ ⟨⟨a₁, b₁, c₁⟩, ⟨a₂, b₂, c₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂, q.scr]
      · rw [b₁, b₂]; exact congrArg (· + _) q.r2.symm
      · rw [c₁, c₂]) (by taint_decide)

/-- The body, with `L` output bytes written. -/
def OutAt (s₀ : State) (L : Nat) (s : State) : Prop :=
  VG.Proof.Argon2.Arm.HPrime.Body s₀ s ∧ ∃ xs, VG.Proof.Argon2.Arm.HPrime.Out s₀ s xs ∧ xs.length = L

theorem emit_blk {s₀ : State} {L : Nat} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L s) :
    WP isa (.block [.mov .r10 (.imm 32)]) s (VG.Proof.Argon2.Arm.HPrime.CopyIn s₀ L 32) := by
  obtain ⟨b, xs, o, hx⟩ := h
  exact wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil
    ⟨b.upd u₁ (by decide) (by decide) (by decide), by rw [u₁.other _ (by decide), o.ptr, hx], u₁.gpr⟩

theorem emit_rel {s₀ s₀' : State} (q : VG.Proof.Argon2.Arm.HPrime.Same s₀ s₀') {L : Nat} :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L t₁ ∧ VG.Proof.Argon2.Arm.HPrime.OutAt s₀' L t₂) emitPrefix fun _ _ => True := by
  unfold emitPrefix
  exact RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => VG.Proof.Argon2.Arm.HPrime.emit_blk h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.emit_blk h))
    (RelCT.seq (VG.Proof.Argon2.Arm.HPrime.copy_rel q) (VG.Proof.Argon2.Arm.HPrime.rel_none ⟨_, by taint_decide⟩))

theorem rem_blk {s₀ : State} {L : Nat} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L s) :
    WP isa (.block [.mov .r10 (.reg .r8)]) s (VG.Proof.Argon2.Arm.HPrime.CopyIn s₀ L (VG.Proof.Argon2.Arm.HPrime.ol s₀ - L)) := by
  obtain ⟨b, xs, o, hx⟩ := h
  exact wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil
    ⟨b.upd u₁ (by decide) (by decide) (by decide), by rw [u₁.other _ (by decide), o.ptr, hx],
      by rw [u₁.gpr, o.left, hx]⟩

theorem copyRemaining_rel {s₀ s₀' : State} (q : VG.Proof.Argon2.Arm.HPrime.Same s₀ s₀') {L : Nat} :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L t₁ ∧ VG.Proof.Argon2.Arm.HPrime.OutAt s₀' L t₂) copyRemaining fun _ _ => True := by
  unfold copyRemaining
  refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => VG.Proof.Argon2.Arm.HPrime.rem_blk h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.rem_blk h)) ?_
  rw [q.ol_eq]
  exact VG.Proof.Argon2.Arm.HPrime.copy_rel q

/-! ## The chain -/

/-- `ChainInv`, for some digest `V` and `r11`. -/
def ChainAt (s₀ : State) (j : Nat) (s : State) : Prop :=
  ∃ (V : List Byte) (e : BitVec 32), V.length = 64 ∧ VG.Proof.Argon2.Arm.HPrime.ChainInv s₀ e V j s

theorem ChainAt.outAt {s₀ : State} {j : Nat} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ j s) :
    VG.Proof.Argon2.Arm.HPrime.OutAt s₀ (32 + 32 * j) s :=
  let ⟨_, _, hV, i⟩ := h
  ⟨i.body, _, i.out, VG.Proof.Argon2.Arm.HPrime.chainOut_length hV j⟩

section
variable {s₀ s₀' : State} (hp : VG.Proof.Argon2.Arm.HPrime.Pre s₀) (hp' : VG.Proof.Argon2.Arm.HPrime.Pre s₀') (q : VG.Proof.Argon2.Arm.HPrime.Same s₀ s₀')

include hp in
theorem OutAt.keeps {L : Nat} {s t : State} (h : VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L s) (k : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s t) :
    VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L t :=
  let ⟨b, xs, o, hx⟩ := h
  ⟨b.keeps hp k, xs, o.keeps hp k, hx⟩

include hp in
theorem next_out_ok {n L : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) {s : State}
    (h : VG.Proof.Argon2.Arm.HPrime.InitIn (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) n s ∧ VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L s) : WP isa next s (VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L) := by
  obtain ⟨⟨c, e⟩, o⟩ := h
  exact (VG.Proof.Argon2.Arm.HPrime.next_ok c e hn₁ hn₂).mono fun t ⟨_, k⟩ => o.keeps hp k

include hp hp' q in
theorem next_out_rel {n L : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun t₁ t₂ => (VG.Proof.Argon2.Arm.HPrime.InitIn (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) n t₁ ∧ VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L t₁) ∧
      (VG.Proof.Argon2.Arm.HPrime.InitIn (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) n t₂ ∧ VG.Proof.Argon2.Arm.HPrime.OutAt s₀' L t₂)) next
      fun t₁ t₂ => VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L t₁ ∧ VG.Proof.Argon2.Arm.HPrime.OutAt s₀' L t₂ :=
  rel_wp ((VG.Proof.Argon2.Arm.HPrime.next_rel hn₁ hn₂).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    (fun _ h => VG.Proof.Argon2.Arm.HPrime.next_out_ok hp hn₁ hn₂ h)
    (fun _ h => VG.Proof.Argon2.Arm.HPrime.next_out_ok hp' hn₁ hn₂ ⟨by rw [q.scr, q.sp]; exact h.1, h.2⟩)

include hp in
/-- Setting `r1` keeps the body and the output. -/
theorem r1_blk {L n : Nat} (hn : encodable (BitVec.ofNat 32 n) = true) {s : State} (h : VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L s) :
    WP isa (.block [.mov .r1 (.imm (BitVec.ofNat 32 n))]) s fun t =>
      VG.Proof.Argon2.Arm.HPrime.InitIn (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) n t ∧ VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L t := by
  refine wp_mov (op2_imm hn) fun s₁ u₁ => WP.block_nil ?_
  have o₁ := h.keeps hp (VG.Proof.Argon2.Arm.HPrime.keeps_upd u₁ (by decide))
  exact ⟨⟨o₁.1.ctx hp, u₁.gpr⟩, o₁⟩

include hp hp' q in
/-- One iteration of the chain. -/
theorem body_rel {j : Nat} :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ j t₁ ∧ VG.Proof.Argon2.Arm.HPrime.ChainAt s₀' j t₂)
      (.seq (.block [.mov .r1 (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft))))
      fun _ _ => True := by
  refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => VG.Proof.Argon2.Arm.HPrime.r1_blk (n := 64) hp (by decide) h.outAt)
    (fun _ h => (VG.Proof.Argon2.Arm.HPrime.r1_blk (n := 64) hp' (by decide) h.outAt).mono fun _ h =>
      ⟨by rw [← q.scr, ← q.sp]; exact h.1, h.2⟩))
    (RelCT.seq (VG.Proof.Argon2.Arm.HPrime.next_out_rel hp hp' q (by decide) (by decide))
      (RelCT.seq (VG.Proof.Argon2.Arm.HPrime.emit_rel q) (VG.Proof.Argon2.Arm.HPrime.rel_none ⟨_, by taint_decide⟩)))

/-- What the chain leaves: `j` iterations, and 33 to 64 bytes left. -/
def ChainDone (s₀ s₀' : State) (t₁ t₂ : State) : Prop :=
  ∃ j, VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ j t₁ ∧ VG.Proof.Argon2.Arm.HPrime.ChainAt s₀' j t₂ ∧ 33 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j) ∧
    VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀

include hp hp' q in
theorem chain_rel :
    RelCT isa (fun t₁ t₂ => ∃ j, 65 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j) ∧ VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ j t₁ ∧ VG.Proof.Argon2.Arm.HPrime.ChainAt s₀' j t₂)
      chain (VG.Proof.Argon2.Arm.HPrime.ChainDone s₀ s₀') := by
  have ho := q.ol_eq
  refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, h65, h₁, h₂⟩ e₁ e₂ =>
    RelCT.loop (M := isa) (Q := VG.Proof.Argon2.Arm.HPrime.ChainDone s₀ s₀')
      (fun m t₁ t₂ => ∃ j, m = VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j) ∧ 65 ≤ m ∧ VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ j t₁ ∧ VG.Proof.Argon2.Arm.HPrime.ChainAt s₀' j t₂)
      (fun m => ?_) _ s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, rfl, h65, h₁, h₂⟩ e₁ e₂
  refine RelCT.of_pre fun _ _ ⟨j, hm, h65, _, _⟩ => ?_
  subst hm
  have it := (VG.Proof.Argon2.Arm.HPrime.body_rel hp hp' q (j := j)).wp
    (F₁ := fun (t : State) => VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ (j + 1) t ∧
      isa.eval .eq t = some (decide (VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * (j + 1)) ≤ 64)))
    (F₂ := fun (t : State) => VG.Proof.Argon2.Arm.HPrime.ChainAt s₀' (j + 1) t ∧
      isa.eval .eq t = some (decide (VG.Proof.Argon2.Arm.HPrime.ol s₀' - (32 + 32 * (j + 1)) ≤ 64)))
    fun t₁ t₂ ⟨⟨V, e, hV, i₁⟩, ⟨V', e', hV', i₂⟩⟩ =>
      ⟨(VG.Proof.Argon2.Arm.HPrime.iter_ok hp hV i₁ (by omega) (by omega)).mono fun _ h => ⟨⟨V, e, hV, h.1⟩, h.2⟩,
       (VG.Proof.Argon2.Arm.HPrime.iter_ok hp' hV' i₂ (by omega) (by omega)).mono fun _ h => ⟨⟨V', e', hV', h.1⟩, h.2⟩⟩
  refine it.mono (fun t₁ t₂ ⟨j', hj, _, a₁, a₂⟩ => ?_) fun t₁ t₂ ⟨_, ⟨c₁, f₁⟩, ⟨c₂, f₂⟩⟩ => ?_
  · have : j' = j := by omega
    subst this; exact ⟨a₁, a₂⟩
  · rw [ho] at f₂
    have n₁ := VG.Proof.Argon2.Arm.HPrime.ne_of_eq f₁
    have n₂ := VG.Proof.Argon2.Arm.HPrime.ne_of_eq f₂
    refine ⟨by rw [n₁, n₂], fun hf => ?_, fun ht => ?_⟩
    · rw [n₁] at hf
      have : VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * (j + 1)) ≤ 64 := by simpa using hf
      exact ⟨j + 1, c₁, c₂, by omega, by omega, by omega⟩
    · rw [n₁] at ht
      have : ¬ VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * (j + 1)) ≤ 64 := by simpa using ht
      exact ⟨_, by omega, j + 1, rfl, by omega, c₁, c₂⟩

/-! ## Extending the digest -/

/-- The state `finishOutput` starts from. -/
def ExtIn (s₀ s : State) : Prop := VG.Proof.Argon2.Arm.HPrime.Body s₀ s ∧ VG.Proof.Argon2.Arm.HPrime.Out s₀ s []

include hp in
theorem ext_emit {s : State} (h : VG.Proof.Argon2.Arm.HPrime.ExtIn s₀ s) (hol : 32 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀) :
    WP isa emitPrefix s (VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ 0) := by
  obtain ⟨b, o⟩ := h
  refine (VG.Proof.Argon2.Arm.HPrime.emit_ok hp b o (by simp only [List.length_nil]; omega)).mono fun t ⟨bt, et, ot, dt⟩ =>
    ⟨VG.Proof.Argon2.Arm.HPrime.digest s₀ s, s.gpr .r11, by simp [VG.Proof.Argon2.Arm.HPrime.digest, bytesAt], bt, et, ?_, dt⟩
  rw [List.nil_append] at ot
  simpa [VG.Proof.Argon2.Arm.HPrime.chainOut, chainPrefixes] using ot

include hp in
theorem ChainAt.keeps {j : Nat} {s t : State} (h : VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ j s)
    (k : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s t) (m : t.mem = s.mem) : VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ j t :=
  let ⟨V, e, hV, i⟩ := h
  ⟨V, e, hV, i.body.keeps hp k, (k.gpr _ (by decide)).trans i.r11, i.out.keeps hp k,
    by show bytesAt _ _ _ = _; rw [m]; exact i.digest⟩

include hp in
theorem chain_cmp {j : Nat} (hl : 32 + 32 * j < VG.Proof.Argon2.Arm.HPrime.ol s₀) {s : State} (h : VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ j s) :
    WP isa (.block cmpLeft) s fun t => VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ j t ∧
      isa.eval .eq t = some (decide (VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j) ≤ 64)) := by
  obtain ⟨V, e, hV, i⟩ := h
  refine (VG.Proof.Argon2.Arm.HPrime.cmp_ok i.out (by rw [VG.Proof.Argon2.Arm.HPrime.chainOut_length hV]; exact hl)).mono fun t ⟨cf, k, m⟩ =>
    ⟨ChainAt.keeps hp ⟨V, e, hV, i⟩ k m, ?_⟩
  rw [cf, VG.Proof.Argon2.Arm.HPrime.chainOut_length hV]

include hp in
theorem left_blk {j : Nat} {s : State} (h : VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ j s) :
    WP isa (.block [.mov .r1 (.reg .r8)]) s fun t =>
      VG.Proof.Argon2.Arm.HPrime.InitIn (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) (VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j)) t ∧ VG.Proof.Argon2.Arm.HPrime.OutAt s₀ (32 + 32 * j) t := by
  have o := h.outAt
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ?_
  have o₁ := o.keeps hp (VG.Proof.Argon2.Arm.HPrime.keeps_upd u₁ (by decide))
  obtain ⟨_, xs, ox, hx⟩ := o
  exact ⟨⟨o₁.1.ctx hp, by rw [u₁.gpr, ox.left, hx]⟩, o₁⟩

/-- `L` bytes written, and at most 64 left. -/
def Last (s₀ s₀' : State) (t₁ t₂ : State) : Prop :=
  ∃ L, VG.Proof.Argon2.Arm.HPrime.OutAt s₀ L t₁ ∧ VG.Proof.Argon2.Arm.HPrime.OutAt s₀' L t₂ ∧ L < VG.Proof.Argon2.Arm.HPrime.ol s₀ ∧ VG.Proof.Argon2.Arm.HPrime.ol s₀ - L ≤ 64

include hp hp' q in
theorem last_rel :
    RelCT isa (VG.Proof.Argon2.Arm.HPrime.ChainDone s₀ s₀') (.seq (.block [.mov .r1 (.reg .r8)]) next) (VG.Proof.Argon2.Arm.HPrime.Last s₀ s₀') := by
  have ho := q.ol_eq
  refine RelCT.of_pre fun _ _ ⟨j, _, _, l₁, l₂, l₃⟩ => ?_
  refine (RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [] (F₁ := VG.Proof.Argon2.Arm.HPrime.ChainAt s₀ j) (F₂ := VG.Proof.Argon2.Arm.HPrime.ChainAt s₀' j)
      (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
      (fun _ h => VG.Proof.Argon2.Arm.HPrime.left_blk hp h)
      (fun _ h => (VG.Proof.Argon2.Arm.HPrime.left_blk hp' h).mono fun _ h => ⟨by rw [← q.scr, ← q.sp, ← ho]; exact h.1, h.2⟩))
    (VG.Proof.Argon2.Arm.HPrime.next_out_rel hp hp' q (n := VG.Proof.Argon2.Arm.HPrime.ol s₀ - (32 + 32 * j)) (by omega) l₂)).mono ?_ ?_
  · intro t₁ t₂ ⟨j', c₁, c₂, m₁, m₂, m₃⟩
    have : j' = j := by omega
    subst this; exact ⟨c₁, c₂⟩
  · intro t₁ t₂ ⟨o₁, o₂⟩
    exact ⟨_, o₁, o₂, by omega, by omega⟩

include hp hp' q in
theorem extend_rel (hol : 65 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀) :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.Arm.HPrime.ExtIn s₀ t₁ ∧ VG.Proof.Argon2.Arm.HPrime.ExtIn s₀' t₂) extendDigest (VG.Proof.Argon2.Arm.HPrime.Last s₀ s₀') := by
  have ho := q.ol_eq
  have hol' : 65 ≤ VG.Proof.Argon2.Arm.HPrime.ol s₀' := by rw [ho]; exact hol
  unfold extendDigest
  refine RelCT.seq (rel_wp ((VG.Proof.Argon2.Arm.HPrime.emit_rel q (L := 0)).mono
      (fun _ _ ⟨⟨b₁, o₁⟩, ⟨b₂, o₂⟩⟩ => ⟨⟨b₁, [], o₁, rfl⟩, ⟨b₂, [], o₂, rfl⟩⟩) fun _ _ h => h)
      (fun _ h => VG.Proof.Argon2.Arm.HPrime.ext_emit hp h (by omega)) (fun _ h => VG.Proof.Argon2.Arm.HPrime.ext_emit hp' h (by omega))) ?_
  refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => VG.Proof.Argon2.Arm.HPrime.chain_cmp hp (by omega) h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.chain_cmp hp' (by omega) h)) ?_
  refine RelCT.seq (RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by rw [f₁, f₂, ho])
    (VG.Proof.Argon2.Arm.HPrime.rel_nil fun _ _ ⟨⟨⟨c₁, f₁⟩, ⟨c₂, _⟩⟩, ht⟩ => ⟨0, c₁, c₂, by
      rw [f₁] at ht; have := of_decide_eq_true (Option.some.inj ht); omega,
      by rw [f₁] at ht; have := of_decide_eq_true (Option.some.inj ht); omega, by omega⟩)
    ((VG.Proof.Argon2.Arm.HPrime.chain_rel hp hp' q).mono (fun _ _ ⟨⟨⟨c₁, f₁⟩, ⟨c₂, _⟩⟩, hf⟩ =>
      ⟨0, by rw [f₁] at hf; have := of_decide_eq_false (Option.some.inj hf); omega, c₁, c₂⟩)
      fun _ _ h => h))
    (VG.Proof.Argon2.Arm.HPrime.last_rel hp hp' q)

include hp in
theorem ext_cmp {s : State} (h : VG.Proof.Argon2.Arm.HPrime.ExtIn s₀ s) :
    WP isa (.block cmpLeft) s fun t => VG.Proof.Argon2.Arm.HPrime.ExtIn s₀ t ∧ isa.eval .eq t = some (decide (VG.Proof.Argon2.Arm.HPrime.ol s₀ ≤ 64)) := by
  obtain ⟨b, o⟩ := h
  refine (VG.Proof.Argon2.Arm.HPrime.cmp_ok o (by have := hp.ol_pos; simp only [List.length_nil]; omega)).mono
    fun t ⟨cf, k, _⟩ => ⟨⟨b.keeps hp k, o.keeps hp k⟩, ?_⟩
  rw [cf]; simp

include hp hp' q in
theorem finishOutput_rel :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.Arm.HPrime.ExtIn s₀ t₁ ∧ VG.Proof.Argon2.Arm.HPrime.ExtIn s₀' t₂) finishOutput fun _ _ => True := by
  have ho := q.ol_eq
  have hpos := hp.ol_pos
  unfold finishOutput
  refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => VG.Proof.Argon2.Arm.HPrime.ext_cmp hp h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.ext_cmp hp' h)) ?_
  refine RelCT.seq (R := VG.Proof.Argon2.Arm.HPrime.Last s₀ s₀') (RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by rw [f₁, f₂, ho])
    (VG.Proof.Argon2.Arm.HPrime.rel_nil fun _ _ ⟨⟨⟨⟨b₁, o₁⟩, f₁⟩, ⟨⟨b₂, o₂⟩, _⟩⟩, ht⟩ =>
      ⟨0, ⟨b₁, [], o₁, rfl⟩, ⟨b₂, [], o₂, rfl⟩, by omega,
        by rw [f₁] at ht; have := of_decide_eq_true (Option.some.inj ht); omega⟩)
    (RelCT.of_pre fun _ _ ⟨⟨⟨_, f₁⟩, _⟩, hf⟩ => (VG.Proof.Argon2.Arm.HPrime.extend_rel hp hp' q (by
        rw [f₁] at hf; have := of_decide_eq_false (Option.some.inj hf); omega)).mono
      (fun _ _ ⟨⟨⟨e₁, _⟩, ⟨e₂, _⟩⟩, _⟩ => ⟨e₁, e₂⟩) fun _ _ h => h)) ?_
  exact RelCT.mono (RelCT.exists_ fun L => (VG.Proof.Argon2.Arm.HPrime.copyRemaining_rel q (L := L)).mono
    (fun _ _ h => ⟨h.1, h.2.1⟩) fun _ _ h => h) (fun _ _ ⟨L, h⟩ => ⟨L, h⟩) fun _ _ h => h

end

end VG.Proof.Argon2.Arm.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.Arm.HPrime.Verified`. -/
section

/-!
# Argon2 H′ on ARMv7: verified

Constant time, by relating two runs with the same public data piece by piece
(`code_ct`): the setup is checked by the taint analysis from the stack
argument, `first` and `finishOutput` by their pieces; then `hPrime_verified`
against `hPrimeArm`, and `hPrimeShared_verified` against
`Spec.Argon2.hPrimeContract`.
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (setup restore first finishOutput chooseLength absorbInput finishInput
  absorbFixed)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_sub wp_cmp op2_reg op2_imm op2_lsr eval_eq)
open VG.Proof.Blake2.Arm.Stream (wp_adds wp_adc)

theorem Same.inp_eq {s₀ s₀' : State} (q : VG.Proof.Argon2.Arm.HPrime.Same s₀ s₀') : VG.Proof.Argon2.Arm.HPrime.inp s₀' = VG.Proof.Argon2.Arm.HPrime.inp s₀ := q.r0

/-! ## The setup -/

theorem agreeS {s₁ s₂ : State} (hp₁ : VG.Proof.Argon2.Arm.HPrime.Pre s₁) (hp₂ : VG.Proof.Argon2.Arm.HPrime.Pre s₂) (q : VG.Proof.Argon2.Arm.HPrime.Same s₁ s₂) :
    VG.Arm.Taint.Agree (argTaint [] 4) s₁ s₂ := by
  have e : ∀ s : State, (VG.Proof.Argon2.Arm.HPrime.argR s) = ⟨State.addr s.sp, 4⟩ := fun s => by simp [VG.Proof.Argon2.Arm.HPrime.argR, stackArgAddr]
  refine agree_argTaint (fun _ h => nomatch h) q.sp.symm ⟨hp₁.sp_hi, fun r hr => ?_⟩
    ⟨hp₂.sp_hi, fun r hr => ?_⟩ (argMem_of (j := 1) q.sp.symm (by have := hp₁.sp_hi; omega) fun i hi => ?_)
  · rw [← e]; rw [hp₁.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp₁.arg_out
    · exact hp₁.arg_scr
  · rw [← e]; rw [hp₂.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp₂.arg_out
    · exact hp₂.arg_scr
  · have : i = 0 := by omega
    subst this; exact q.scr.symm

theorem setup_F0 {s₀ : State} (hp : VG.Proof.Argon2.Arm.HPrime.Pre s₀) : WP isa (.block setup) s₀ (VG.Proof.Argon2.Arm.HPrime.F0 s₀) := by
  have hif := hp.in_fits
  refine (VG.Proof.Argon2.Arm.HPrime.setup_ok hp).mono fun t ⟨b, o, f⟩ => ⟨b, o, ?_⟩
  exact Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := VG.Proof.Argon2.Arm.HPrime.inR s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega) hi

theorem setup_rel {s₀ s₀' : State} (hp : VG.Proof.Argon2.Arm.HPrime.Pre s₀) (hp' : VG.Proof.Argon2.Arm.HPrime.Pre s₀') (q : VG.Proof.Argon2.Arm.HPrime.Same s₀ s₀') :
    RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') (.block setup) fun t₁ t₂ => VG.Proof.Argon2.Arm.HPrime.F0 s₀ t₁ ∧ VG.Proof.Argon2.Arm.HPrime.F0 s₀' t₂ :=
  ((RelCT.taint (A := taint) (argTaint [] 4) (fun _ _ ⟨e₁, e₂⟩ => by subst e₁ e₂; exact VG.Proof.Argon2.Arm.HPrime.agreeS hp hp' q)
    (by taint_decide)).wp fun _ _ ⟨e₁, e₂⟩ =>
      ⟨by subst e₁; exact VG.Proof.Argon2.Arm.HPrime.setup_F0 hp, by subst e₂; exact VG.Proof.Argon2.Arm.HPrime.setup_F0 hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## `first` -/

/-- The count `finishInput` passes to `finalize`, low and high words. -/
def cntLo (s₀ : State) : BitVec 32 := s₀.gpr .r1 + 4
def cntHi (s₀ : State) : BitVec 32 :=
  0 + 0 + (if decide (2 ^ 32 ≤ (s₀.gpr .r1).toNat + (4 : BitVec 32).toNat) then 1 else 0)

section
variable {s₀ s₀' : State} (hp : VG.Proof.Argon2.Arm.HPrime.Pre s₀) (hp' : VG.Proof.Argon2.Arm.HPrime.Pre s₀') (q : VG.Proof.Argon2.Arm.HPrime.Same s₀ s₀')

include hp in
theorem choose_blk {s : State} (h : VG.Proof.Argon2.Arm.HPrime.F0 s₀ s) :
    WP isa (.block [.dp .sub .r1 .r8 (.imm 1), .mov .r1 (.shifted .r1 .lsr 6), .cmp .r1 (.imm 0)]) s
      fun t => VG.Proof.Argon2.Arm.HPrime.F0 s₀ t ∧ isa.eval .eq t = some (decide (VG.Proof.Argon2.Arm.HPrime.ol s₀ ≤ 64)) := by
  have hol := (s₀.gpr .r3).isLt
  have hpos := hp.ol_pos
  have l₀ : s.gpr .r8 = BitVec.ofNat 32 (VG.Proof.Argon2.Arm.HPrime.ol s₀) := by rw [h.out.left]; rfl
  refine wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ⟨h.keeps hp ?_, ?_⟩
  · exact Keeps.same (fun r hr => by rw [f₃.gpr, u₂.other _ (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.1, u₁.other _ (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.1])
      (by rw [f₃.sp, u₂.sp, u₁.sp]) (by rw [f₃.mem, u₂.mem, u₁.mem]) (by rw [f₃.rd, u₂.rd, u₁.rd])
      (by rw [f₃.wr, u₂.wr, u₁.wr])
  · show VG.Arm.eval .eq s₃ = _
    rw [eval_eq, z₃, u₂.gpr, u₁.gpr, l₀]; exact congrArg some (VG.Proof.Argon2.Arm.HPrime.le64_beq hpos hol)

include hp hp' q in
theorem choose_rel :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.Arm.HPrime.F0 s₀ t₁ ∧ VG.Proof.Argon2.Arm.HPrime.F0 s₀' t₂) chooseLength fun _ _ => True := by
  unfold chooseLength
  refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => VG.Proof.Argon2.Arm.HPrime.choose_blk hp h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.choose_blk hp' h)) ?_
  exact RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by rw [f₁, f₂, q.ol_eq])
    (VG.Proof.Argon2.Arm.HPrime.rel_none ⟨_, by taint_decide⟩) (VG.Proof.Argon2.Arm.HPrime.rel_none ⟨_, by taint_decide⟩)

include hp in
theorem absorbInput_blk {s : State} (h : VG.Proof.Argon2.Arm.HPrime.F0 s₀ s) :
    WP isa (.block [.mov .r2 (.imm 4), .mov .r3 (.imm 0), .mov .r9 (.reg .r5), .mov .r10 (.reg .r6)]) s
      (VG.Proof.Argon2.Arm.HPrime.UpdateIn (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) (VG.Proof.Argon2.Arm.HPrime.inp s₀) (VG.Proof.Argon2.Arm.HPrime.inl s₀) 4 0) := by
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  have o₄ : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have k₄ : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s s₄ := Keeps.same (fun r hr => o₄ r (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.2.1
      (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.2.2.1 (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.2.2.2.1 (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.2.2.2.2.1)
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have F₄ := h.keeps hp k₄
  refine ⟨F₄.body.ctx hp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.body.r5]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.body.r6]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [F₄.body.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Argon2.Arm.HPrime.inR s₀, by simp, 0, by simp, by simp⟩

include hp in
theorem finishInput_blk {s : State} (h : VG.Proof.Argon2.Arm.HPrime.F0 s₀ s) :
    WP isa (.block [.mov .r3 (.imm 0), .adds .r2 .r6 (.imm 4), .adc .r3 .r3 (.imm 0)]) s
      (VG.Proof.Argon2.Arm.HPrime.FinalizeIn (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) (VG.Proof.Argon2.Arm.HPrime.cntLo s₀) (VG.Proof.Argon2.Arm.HPrime.cntHi s₀)) := by
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_adds (op2_imm (by decide)) fun s₂ u₂ c₂ =>
    wp_adc (op2_imm (by decide)) fun s₃ u₃ _ => WP.block_nil ?_
  have o₃ : ∀ r, r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h2, u₂.other _ h1, u₁.other _ h2]
  have k₃ : VG.Proof.Argon2.Arm.HPrime.Keeps (VG.Proof.Argon2.Arm.HPrime.scr s₀) (VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) s s₃ := Keeps.same (fun r hr => o₃ r (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.2.1
      (VG.Proof.Argon2.Arm.HPrime.kept_ne r hr).2.2.2.1)
    (by rw [u₃.sp, u₂.sp, u₁.sp]) (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₃.wr, u₂.wr, u₁.wr])
  have r6 : s₁.gpr .r6 = s₀.gpr .r1 := by rw [u₁.other _ (by decide), h.body.r6]
  refine ⟨(h.keeps hp k₃).body.ctx hp, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr, r6]; rfl
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, c₂, r6]; rfl

include q in
theorem cnt_eq : VG.Proof.Argon2.Arm.HPrime.cntLo s₀' = VG.Proof.Argon2.Arm.HPrime.cntLo s₀ ∧ VG.Proof.Argon2.Arm.HPrime.cntHi s₀' = VG.Proof.Argon2.Arm.HPrime.cntHi s₀ := by
  simp only [VG.Proof.Argon2.Arm.HPrime.cntLo, VG.Proof.Argon2.Arm.HPrime.cntHi, q.r1, and_self]

include hp hp' q in
theorem first_ct : RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.Arm.HPrime.F0 s₀ t₁ ∧ VG.Proof.Argon2.Arm.HPrime.F0 s₀' t₂) first fun _ _ => True := by
  have hs := hp.scr_fits
  have nE : VG.Proof.Argon2.Arm.HPrime.nF s₀' = VG.Proof.Argon2.Arm.HPrime.nF s₀ := by simp only [VG.Proof.Argon2.Arm.HPrime.nF, q.ol_eq]
  unfold first
  refine RelCT.seq (rel_wp (VG.Proof.Argon2.Arm.HPrime.choose_rel hp hp' q) (fun _ h => VG.Proof.Argon2.Arm.HPrime.first_choose hp h)
    (fun _ h => VG.Proof.Argon2.Arm.HPrime.first_choose hp' h)) ?_
  refine RelCT.seq (rel_wp ((VG.Proof.Argon2.Arm.HPrime.init_rel (B := VG.Proof.Argon2.Arm.HPrime.scr s₀) (SP := VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) (n := VG.Proof.Argon2.Arm.HPrime.nF s₀) (VG.Proof.Argon2.Arm.HPrime.nF_pos hp)
      (Nat.min_le_right _ _)).mono (fun _ _ ⟨⟨f₁, e₁⟩, ⟨f₂, e₂⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, e₁⟩, by
          have c := f₂.body.ctx hp'
          rw [q.scr, q.sp] at c
          exact ⟨c, by rw [e₂, nE]⟩⟩) fun _ _ h => h)
    (fun _ h => VG.Proof.Argon2.Arm.HPrime.first_init hp h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.first_init hp' h)) ?_
  refine RelCT.seq (rel_wp ((VG.Proof.Argon2.Arm.HPrime.absorbFixed_rel (B := VG.Proof.Argon2.Arm.HPrime.scr s₀) (SP := VG.Proof.Argon2.Arm.HPrime.sp₀ s₀) (offset := 832) (size := 4)
      (by decide) (by decide) (by omega) (by decide) (by decide)
      (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))) VG.Proof.Argon2.Arm.HPrime.fixed_check_832).mono
      (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, VG.Proof.Argon2.Arm.HPrime.pfx_cov hp f₁.body⟩, by
          have c := f₂.body.ctx hp'
          have v := VG.Proof.Argon2.Arm.HPrime.pfx_cov hp' f₂.body
          simp only [VG.Proof.Argon2.Arm.HPrime.P] at v
          rw [q.scr, q.sp] at c; rw [q.scr] at v
          exact ⟨c, v⟩⟩) fun _ _ h => h)
    (fun _ h => VG.Proof.Argon2.Arm.HPrime.first_fixed hp h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.first_fixed hp' h)) ?_
  refine RelCT.seq (rel_wp ?_ (fun _ h => VG.Proof.Argon2.Arm.HPrime.first_input hp h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.first_input hp' h)) ?_
  · unfold absorbInput
    refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
      (fun _ h => VG.Proof.Argon2.Arm.HPrime.absorbInput_blk hp h.1)
      (fun _ h => (VG.Proof.Argon2.Arm.HPrime.absorbInput_blk hp' h.1).mono fun _ h => by
        rw [q.scr, q.sp, q.inp_eq, q.inl_eq] at h; exact h)) ?_
    exact VG.Proof.Argon2.Arm.HPrime.update_rel hp.in_fits (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in
  · unfold finishInput
    refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
      (fun _ h => VG.Proof.Argon2.Arm.HPrime.finishInput_blk hp h.1)
      (fun _ h => (VG.Proof.Argon2.Arm.HPrime.finishInput_blk hp' h.1).mono fun _ h => by
        rw [q.scr, q.sp, (VG.Proof.Argon2.Arm.HPrime.cnt_eq q).1, (VG.Proof.Argon2.Arm.HPrime.cnt_eq q).2] at h; exact h)) ?_
    exact VG.Proof.Argon2.Arm.HPrime.finalize_rel

include hp hp' q in
theorem first_rel :
    RelCT isa (fun t₁ t₂ => VG.Proof.Argon2.Arm.HPrime.F0 s₀ t₁ ∧ VG.Proof.Argon2.Arm.HPrime.F0 s₀' t₂) first fun t₁ t₂ =>
      (VG.Proof.Argon2.Arm.HPrime.F0 s₀ t₁ ∧ (VG.Proof.Argon2.Arm.HPrime.digest s₀ t₁).take (VG.Proof.Argon2.Arm.HPrime.nF s₀) = Spec.Argon2.H (VG.Proof.Argon2.Arm.HPrime.nF s₀) (Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀) ++ VG.Proof.Argon2.Arm.HPrime.inB s₀)) ∧
      (VG.Proof.Argon2.Arm.HPrime.F0 s₀' t₂ ∧ (VG.Proof.Argon2.Arm.HPrime.digest s₀' t₂).take (VG.Proof.Argon2.Arm.HPrime.nF s₀') =
        Spec.Argon2.H (VG.Proof.Argon2.Arm.HPrime.nF s₀') (Spec.Argon2.le32 (VG.Proof.Argon2.Arm.HPrime.ol s₀') ++ VG.Proof.Argon2.Arm.HPrime.inB s₀')) :=
  rel_wp (VG.Proof.Argon2.Arm.HPrime.first_ct hp hp' q) (fun _ h => VG.Proof.Argon2.Arm.HPrime.first_ok hp h) (fun _ h => VG.Proof.Argon2.Arm.HPrime.first_ok hp' h)

end

/-! ## Constant time -/

theorem code_ct : ConstantTime isa hPrimeArm.pre hPrimeArm.pub Impl.Argon2.Arm.HPrime.code := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    fun s₀ s₀' t₁ t₂ r₁ r₂ ⟨h₀, h₀', hq⟩ e₁ e₂ => ?_
  have hp := VG.Proof.Argon2.Arm.HPrime.pre_of s₀ h₀
  have hp' := VG.Proof.Argon2.Arm.HPrime.pre_of s₀' h₀'
  have q := Same.of_pub hq
  suffices h : RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') Impl.Argon2.Arm.HPrime.code fun _ _ => True from
    h s₀ s₀' t₁ t₂ r₁ r₂ ⟨rfl, rfl⟩ e₁ e₂
  unfold Impl.Argon2.Arm.HPrime.code
  refine RelCT.seq (VG.Proof.Argon2.Arm.HPrime.setup_rel hp hp' q) (RelCT.seq (VG.Proof.Argon2.Arm.HPrime.first_rel hp hp' q)
    (RelCT.seq (R := fun t₁ t₂ => VG.Proof.Argon2.Arm.HPrime.Body s₀ t₁ ∧ VG.Proof.Argon2.Arm.HPrime.Body s₀' t₂) ?_ ?_))
  · exact rel_wp ((VG.Proof.Argon2.Arm.HPrime.finishOutput_rel hp hp' q).mono (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
      ⟨⟨f₁.body, f₁.out⟩, ⟨f₂.body, f₂.out⟩⟩) fun _ _ h => h)
      (fun _ ⟨f, d⟩ => (VG.Proof.Argon2.Arm.HPrime.finish_ok hp f.body f.out d).mono fun _ h => h.1)
      (fun _ ⟨f, d⟩ => (VG.Proof.Argon2.Arm.HPrime.finish_ok hp' f.body f.out d).mono fun _ h => h.1)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [.r4]) (fun _ _ ⟨b₁, b₂⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [b₁.r4, b₂.r4, q.scr]) (by taint_decide)

/-! ## A state satisfying the precondition -/

/-- `input` at `0x1000` (one byte), `out` at `0x2000` (one byte), `scratch`
at `0x10000`, its address the stack argument at `0x5000`. -/
def hSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | .r3 => 1 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5002 then 1 else 0
  rd := [⟨0x1000, 1⟩, ⟨0x5000, 4⟩]
  wr := [⟨0x2000, 1⟩, ⟨0x10000, 16384⟩]

theorem hSat_pre : hPrimeArm.pre VG.Proof.Argon2.Arm.HPrime.hSatState := by
  have e : stackArg VG.Proof.Argon2.Arm.HPrime.hSatState 0 = 0x10000 := by decide
  have e2 : stackArgAddr VG.Proof.Argon2.Arm.HPrime.hSatState 0 = 0x5000 := by decide
  simp only [VG.Proof.Argon2.Arm.HPrime.hPrimeArm, e, e2]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
    by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem hPrime_verified : Verified Arm.target Impl.Argon2.Arm.HPrime.code VG.Proof.Argon2.Arm.HPrime.hPrimeArm := by
  refine ⟨fun s hs => ?_, VG.Proof.Argon2.Arm.HPrime.code_ct, ⟨VG.Proof.Argon2.Arm.HPrime.hSatState, VG.Proof.Argon2.Arm.HPrime.hSat_pre⟩⟩
  obtain ⟨t, s', he, h₁, h₂, h₃⟩ := VG.Proof.Argon2.Arm.HPrime.correct (VG.Proof.Argon2.Arm.HPrime.pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩

theorem hPrime_implies : hPrimeArm.Implies (Spec.Argon2.hPrimeContract Arm.abi 32) := by
  sig_implies [Spec.Argon2.hPrimeContract, Spec.Argon2.hPrimeSig, VG.Proof.Argon2.Arm.HPrime.hPrimeArm, VG.Proof.Argon2.Arm.stkR,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [hSatState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Argon2.Arm.HPrime.hSatState

/-- The emitted function, against the shared contract. -/
theorem hPrimeShared_verified :
    Verified Arm.target Impl.Argon2.Arm.HPrime.code (Spec.Argon2.hPrimeContract Arm.abi 32) :=
  hPrime_verified.of_implies VG.Proof.Argon2.Arm.HPrime.hPrime_implies

end VG.Proof.Argon2.Arm.HPrime

end
