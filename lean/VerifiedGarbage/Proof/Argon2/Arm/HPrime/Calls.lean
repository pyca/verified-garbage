module

import VerifiedGarbage.Proof.Blake2.Arm.Blake2b
public import VerifiedGarbage.Impl.Argon2.Arm.HPrime
public import VerifiedGarbage.Proof.Blake2.Arm.Stream.Common
public import VerifiedGarbage.Proof.Argon2.Arm.Push
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Argon2.Contract

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
    fun t af hpost => ?_
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
    fun t af hpost => ?_
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
