module

public import VerifiedGarbage.Proof.Ffdh.X86.Entry
public import VerifiedGarbage.Proof.Ffdh.X86.ABI
public import VerifiedGarbage.Proof.Framework.X86.StackScratchConsts
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Shape
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Table
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Rsa.X86.StackTactic
meta import VerifiedGarbage.Proof.Rsa.X86.StackTactic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.X86.Checks
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGen
import VerifiedGarbage.Proof.Ffdh.X86.KeyScan
import VerifiedGarbage.Proof.Ffdh.X86.Ops
import VerifiedGarbage.Proof.Ffdh.ContextRows
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.Lead
import VerifiedGarbage.Proof.Ffdh.ScanAt
import VerifiedGarbage.Proof.Ffdh.VettedGroupFacts
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Prepare
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.State
public import VerifiedGarbage.Proof.Ffdh.X86.Dom
import VerifiedGarbage.Proof.Ffdh.X86.VettedValidation.Scan
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
public import VerifiedGarbage.Proof.Framework.X86.SymFrame
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Comb
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Digit
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
public import VerifiedGarbage.Proof.Ffdh.X86.KeyCut
import VerifiedGarbage.Proof.Bignum.X86.ArgumentFrame
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num

/-! # `vg_ffdh_generate_key_precompute` on i686 against its contract -/

@[expose] public section

/-!
# FFDH's key-generation context on i686: the precomputation's body

`body_ok`: the width (`recognize_ok`, the bound's scan and bit length,
`cap_ok`) and its metadata, then p's context, rows 0 and 1 (`p` and
`R² mod p`) and the table (`table_ok`); the context's words are
`generationValues` (`values_of`).
-/

/-!
# FFDH's key-generation context on i686: the width

The precomputation's front: the vetted groups' recognized width of the
domain (`recognize_ok`, `VettedValidation.scan` in a frame of its three
arguments), to the header word at 48.
-/

/-!
# FFDH's key-generation context on i686: the comb's table

The precomputation's table (`table_ok`): entry 0, Montgomery one, and entry
1, `g R mod p`; then for each tooth `d = 2^(k+1)` its entry, from the last
tooth's by `rows` squares, and the entries `d + j` for `0 < j < d`, entry
`j` times entry `d` (`FixedBaseComb.exponent_add_tooth`). Entry `e` is row
`2 + e` of the context, `g^(exponent e) R mod p`.
-/

/-!
# FFDH's key-generation context on i686: its rows

The precomputation writes the context: `storeRow_ok` copies a wide slot to
a row of it, `loadRow_ok` a row back to a slot, each by `selectLoop` with an
all-ones mask.
-/

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Ffdh.X86.Cached
open VG.Impl.Bignum.X86.PublicRt (argAt)

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The context writable, apart from the working space and the arguments. -/
structure CtxW (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  ws : Ws s (ctxAddr args) (ctxBytes len)
  apart : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ ⟨base, bytes⟩
  argsApart : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩ ⟨ctxAddr args, ctxBytes len⟩
  stk : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ (below (s.gpr .esp) 96)

theorem CtxW.keep {t : State} {rs : List Reg} (C : CtxW base bytes len args s) (K : Keeps rs s t)
    (sp : .esp ∉ rs := by decide) : CtxW base bytes len args t :=
  ⟨C.ws.of_keeps K, C.apart, by rw [K.1 _ sp]; exact C.argsApart, by rw [K.1 _ sp]; exact C.stk⟩

theorem CtxW.rd (C : CtxW base bytes len args s) : CtxRd base bytes len args s := by
  refine ⟨⟨?_, ?_⟩, C.apart⟩
  · rw [show off (ctxAddr args) 0 = ctxAddr args from BitVec.add_zero _]
    exact ⟨_, List.mem_append_right _ C.ws.wr, Region.contains_self _ _⟩
  · have := C.ws.nowrap; omega

/-- A slot's span, readable. -/
theorem slot_span (h : In Ex base bytes len args s) {a : Nat} (ha : a ≤ 27) :
    Span s base (lo len (.slot .wide a)) (4 * cwc len .wide) := by
  have bw := bc_eq_cwc len .wide
  have f := h.slot_fit .wide (j := a) ha
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have nw := h.scratch.nowrap
  refine ⟨?_, by omega⟩
  exact ⟨_, List.mem_append_right _ h.ws.wr, Offset.contains_base _ (by omega) (by omega)⟩

/-- An index into `eax`, by code that keeps the rest. -/
abbrev Idx (idx : List Instr) (s : State) (j : Nat) : Prop :=
  ∀ (is : List Instr) (Q : State → Prop), (∀ u, Keeps [.eax] s u → u.mem = s.mem →
    u.gpr .eax = BitVec.ofNat 32 j → WP isa (.block is) u Q) → WP isa (.block (idx ++ is)) s Q

theorem rowImm_idx (k : Nat) : Idx (rowImm k) s k := fun is Q k' => by
  simp only [rowImm, List.cons_append, List.nil_append]
  exact wp_movS rfl fun u U _ => k' u U.keeps U.mem U.gpr

/-- Row `j`'s bytes in the context. -/
theorem row_fit {j : Nat} (hj : j < 34) : 24 + bc len .wide * j + bc len .wide ≤ ctxBytes len := by
  have := Nat.mul_le_mul_left (bc len .wide) (show j + 1 ≤ 34 by omega)
  rw [Nat.mul_succ] at this
  simp only [ctxBytes]; omega

/-- Slot `a` to row `j` of the context. -/
theorem storeRow_ok (h : In Ex base bytes len args s) (C : CtxW base bytes len args s) {idx : List Instr} {j a : Nat}
    (hj : j < 34) (ha : a ≤ 27) (hidx : Idx idx s j) :
    WP isa (storeRow idx a) s fun u =>
      In Ex base bytes len args u ∧ Outside (ctxAddr args) (24 + bc len .wide * j) (bc len .wide) s.mem u.mem ∧
      val32 u.mem (ctxAddr args) (24 + bc len .wide * j) (cwc len .wide) = sv s.mem base len .wide a ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  have fa := h.slot_fit .wide (j := a) ha
  have bw := bc_eq_cwc len .wide
  have hb := bc_le h.upper' .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have rf := row_fit (len := len) hj
  unfold storeRow
  simp only [List.append_assoc]
  refine WP.seq (hidx _ _ fun s₀ K₀ m₀ e₀ => ?_)
  have h₀ := h.regs K₀ m₀
  refine rowAt_ok (r := .ebx) (j := j) h₀ (by omega) e₀ fun s₁ K₁ m₁ p₁ => ?_
  have h₁ := h₀.regs K₁ m₁
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun s₂ U₂ _ => ?_
  have h₂ := h₁.regs U₂.keeps U₂.mem
  refine ptrTo_ok (r := .ebp) (t := .edx) (x := .slot .wide a) (by decide) (by decide) h₂.edi h₂.width h.upper'
    (by omega) fun s₃ K₃ m₃ p₃ => ?_
  have h₃ := h₂.regs K₃ m₃
  refine cntTo_ok (n := one .wide) (r := .edi) h₃.width h.upper' (by decide) fun s₄ K₄ m₄ e₄ => WP.block_nil ?_
  have K₀₄ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s s₄ :=
    (((K₀.mono (by decide)).trans (K₁.mono (by decide))).trans (U₂.keeps.mono (by decide))).trans
      ((K₃.mono (by decide)).trans (K₄.mono (by decide)))
  have m₀₄ : s₄.mem = s.mem := by rw [m₄, m₃, U₂.mem, m₁, m₀]
  have ws₄ : Ws s₄ (ctxAddr args) (ctxBytes len) := C.ws.of_keeps K₀₄
  have ebx₄ : PtrAt s₄ (ctxAddr args) .ebx (24 + bc len .wide * j) := by
    rw [PtrAt, K₄.1 _ (by decide), K₃.1 _ (by decide), U₂.other _ (by decide)]; exact p₁
  have ebp₄ : PtrAt s₄ base .ebp (lo len (.slot .wide a)) := by rw [PtrAt, K₄.1 _ (by decide)]; exact p₃
  have edi₄ : (s₄.gpr .edi).toNat = 4 * cwc len .wide := by
    rw [e₄, cb1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact bw
  have ecx₄ : s₄.gpr .ecx = cmask true := by
    rw [K₄.1 _ (by decide), K₃.1 _ (by decide), U₂.gpr]; rfl
  have span : Span s₄ base (lo len (.slot .wide a)) (4 * cwc len .wide) := (slot_span h ha).of_keeps K₀₄
  have dis : Region.Disjoint ⟨off base (lo len (.slot .wide a)), 4 * cwc len .wide⟩
      ⟨off (ctxAddr args) (24 + bc len .wide * j), 4 * cwc len .wide⟩ :=
    (C.apart.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by rw [← bw]; exact rf))
  have g := bc_ge h.lower' .wide
  refine WP.seq (WP.mono (selectLoop_far_ok ws₄ true (by omega) span (by rw [← bw]; exact rf) dis ebp₄ ebx₄ edi₄ ecx₄)
    fun t ⟨O, V, _, _, Kt⟩ => ?_)
  have K₀t : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := K₀₄.trans (Kt.mono (by decide))
  have cw := C.ws.nowrap
  have Fr : Frame [⟨off (ctxAddr args) (24 + bc len .wide * j), 4 * cwc len .wide⟩] s.mem t.mem := by
    rw [← m₀₄]; exact Outside.frame_span O (by omega)
  have top := h.top
  have argR : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 76⟩
      ⟨off (ctxAddr args) (24 + bc len .wide * j), 4 * cwc len .wide⟩ :=
    C.argsApart.sub_right (Offset.sub_base _ (by omega))
  have A16 := (h.stack 16 (by decide)).frame K₀t (by decide) Fr (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    rw [show VG.Proof.Dsa.X86.stackAddress s 16 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * 16) from
      addr_eq (by omega_arith)]
    exact argR.sub_left (Offset.sub_base _ (by omega_arith)))
  refine wp_movS A16.readSrc fun u U _ => WP.block_nil ?_
  have ed : u.gpr .edi = s.gpr .edi := by rw [U.gpr]; exact h.edi_eq
  have Ku : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp])
      ((K₀t.trans (U.keeps.mono (by decide))).mono (by decide)) ed
  have Fu : Frame [⟨off (ctxAddr args) (24 + bc len .wide * j), 4 * cwc len .wide⟩] s.mem u.mem := by
    rw [U.mem]; exact Fr
  refine ⟨KeyCut.in_keepOut h Ku (by decide) (by decide) Fu argR, ?_, ?_, Ku⟩
  · rw [U.mem, ← m₀₄]; rw [← bw] at O; exact O
  · rw [U.mem, V, ← m₀₄]; rfl

/-- Row `j` of the context to slot `a`. -/
theorem loadRow_ok (h : In Ex base bytes len args s) (C : CtxRd base bytes len args s) {idx : List Instr} {j a : Nat}
    (hj : j < 34) (ha : a ≤ 27) (hidx : Idx idx s j) :
    WP isa (loadRow idx a) s fun u =>
      In Ex base bytes len args u ∧ Outside base (lo len (.slot .wide a)) (bc len .wide) s.mem u.mem ∧
      sv u.mem base len .wide a = val32 s.mem (ctxAddr args) (24 + bc len .wide * j) (cwc len .wide) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  have fa := h.slot_fit .wide (j := a) ha
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  have hb := bc_le h.upper' .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have rf := row_fit (len := len) hj
  unfold loadRow
  simp only [List.append_assoc]
  refine WP.seq (hidx _ _ fun s₀ K₀ m₀ e₀ => ?_)
  have h₀ := h.regs K₀ m₀
  refine rowAt_ok (r := .ebp) (j := j) h₀ (by omega) e₀ fun s₁ K₁ m₁ p₁ => ?_
  have h₁ := h₀.regs K₁ m₁
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun s₂ U₂ _ => ?_
  have h₂ := h₁.regs U₂.keeps U₂.mem
  refine ptrTo_ok (r := .ebx) (t := .edx) (x := .slot .wide a) (by decide) (by decide) h₂.edi h₂.width h.upper'
    (by omega) fun s₃ K₃ m₃ p₃ => ?_
  have h₃ := h₂.regs K₃ m₃
  refine cntTo_ok (n := one .wide) (r := .edi) h₃.width h.upper' (by decide) fun s₄ K₄ m₄ e₄ => WP.block_nil ?_
  have K₀₄ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s s₄ :=
    (((K₀.mono (by decide)).trans (K₁.mono (by decide))).trans (U₂.keeps.mono (by decide))).trans
      ((K₃.mono (by decide)).trans (K₄.mono (by decide)))
  have m₀₄ : s₄.mem = s.mem := by rw [m₄, m₃, U₂.mem, m₁, m₀]
  have ws₄ : Ws s₄ base bytes := h.ws.of_keeps K₀₄
  have ebp₄ : PtrAt s₄ (ctxAddr args) .ebp (24 + bc len .wide * j) := by
    rw [PtrAt, K₄.1 _ (by decide), K₃.1 _ (by decide), U₂.other _ (by decide)]; exact p₁
  have ebx₄ : PtrAt s₄ base .ebx (lo len (.slot .wide a)) := by rw [PtrAt, K₄.1 _ (by decide)]; exact p₃
  have edi₄ : (s₄.gpr .edi).toNat = 4 * cwc len .wide := by
    rw [e₄, cb1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact bw
  have ecx₄ : s₄.gpr .ecx = cmask true := by
    rw [K₄.1 _ (by decide), K₃.1 _ (by decide), U₂.gpr]; rfl
  have span : Span s₄ (ctxAddr args) (24 + bc len .wide * j) (4 * cwc len .wide) :=
    (C.keep K₀₄).row (by rw [← bw]; exact rf)
  have dis : Region.Disjoint ⟨off (ctxAddr args) (24 + bc len .wide * j), 4 * cwc len .wide⟩
      ⟨off base (lo len (.slot .wide a)), 4 * cwc len .wide⟩ :=
    (C.apart.sub_left (Offset.sub_base _ (by rw [← bw]; exact rf))).sub_right (Offset.sub_base _ (by omega))
  refine WP.seq (WP.mono (selectLoop_far_ok ws₄ true (by omega) span (by omega) dis ebp₄ ebx₄ edi₄ ecx₄)
    fun t ⟨O, V, _, _, Kt⟩ => ?_)
  have K₀t : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := K₀₄.trans (Kt.mono (by decide))
  have Oall : Outside base 0 bytes s.mem t.mem := by rw [← m₀₄]; exact O.mono (Nat.zero_le _) (by omega)
  refine wp_movS ((h.stack 16 (by decide)).keep K₀t (by decide) Oall).readSrc fun u U _ => WP.block_nil ?_
  have ed : u.gpr .edi = s.gpr .edi := by rw [U.gpr]; exact h.edi_eq
  have Ku : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp])
      ((K₀t.trans (U.keeps.mono (by decide))).mono (by decide)) ed
  refine ⟨h.keep Ku (by decide) (by decide) (by rw [U.mem]; exact Oall), ?_, ?_, Ku⟩
  · rw [U.mem, ← m₀₄, bw]; exact O
  · simp only [sv]
    rw [U.mem, V, m₀₄]; rfl

end

end VG.Proof.Ffdh.X86.Cached

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Precompute

/-- Row `r` of the context, as a number. -/
abbrev rowV (m : Mem) (args : Nat → BitVec 32) (len r : Nat) : Nat :=
  val32 m (ctxAddr args) (24 + bc len .wide * r) (cwc len .wide)

/-- Entry `e` of the table. -/
abbrev entV (len P G bits e : Nat) : Nat := enc len P G (Spec.Rsa.FixedBaseComb.exponent bits e)

/-- The context's words before the table: the header and rows 0 and 1. -/
abbrev preV (m : Mem) (args : Nat → BitVec 32) (len : Nat) : Nat :=
  val32 m (ctxAddr args) 0 (6 + 2 * cwc len .wide)

/-- The context's region. -/
abbrev ctxR (args : Nat → BitVec 32) (len : Nat) : Region := ⟨ctxAddr args, ctxBytes len⟩

/-- A state of the table, from `s₀`: its first `n` entries written. -/
structure TS (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (P G bits : Nat) (s₀ : State) (n : Nat) (u : State) : Prop where
  ctx : CtxOk Ex base bytes len args .wide P u
  cw : CtxW base bytes len args u
  le : n ≤ 32
  ents : ∀ e < n, rowV u.mem args len (2 + e) = entV len P G bits e
  rows : w32 u.mem base rowsOff = Spec.Rsa.FixedBaseComb.rows bits
  pre : preV u.mem args len = preV s₀.mem args len
  frame : Frame (ctxR args len :: frameR base (s₀.gpr .esp) (fR len)) s₀.mem u.mem
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ u

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32} {P G bits : Nat} {s₀ : State}

theorem TS.inp {n : Nat} {u : State} (S : TS Ex base bytes len args P G bits s₀ n u) :
    In Ex base bytes len args u := S.ctx.inp

theorem TS.esp {n : Nat} {u : State} (S : TS Ex base bytes len args P G bits s₀ n u) :
    u.gpr .esp = s₀.gpr .esp := S.keeps.1 _ (by decide)

/-- The context's words through writes of the working space and the stack. -/
theorem ctx_far {u : State} (C : CtxW base bytes len args u) {ws : List (Nat × Nat)} {m m' : Mem}
    (F : Frame (frameR base (u.gpr .esp) ws) m m') (hws : ∀ p ∈ ws, p.1 + p.2 ≤ bytes) {d N : Nat}
    (hd : d + 4 * N ≤ ctxBytes len) : val32 m' (ctxAddr args) d N = val32 m (ctxAddr args) d N :=
  ctx_val C.rd C.stk F hws hd

theorem row_fit' {r : Nat} (hr : r < 34) : 24 + bc len .wide * r + 4 * cwc len .wide ≤ ctxBytes len := by
  rw [← bc_eq_cwc]; exact row_fit hr

theorem pre_fit : 0 + 4 * (6 + 2 * cwc len .wide) ≤ ctxBytes len := by
  have bw := bc_eq_cwc len .wide
  simp only [ctxBytes]; omega

/-- A stage of the working space keeps the table. -/
theorem TS.step {n : Nat} {u t : State} (S : TS Ex base bytes len args P G bits s₀ n u)
    (St : Step Ex base bytes len args u t) (C : CtxOk Ex base bytes len args .wide P t)
    (hrows : w32 t.mem base rowsOff = w32 u.mem base rowsOff) : TS Ex base bytes len args P G bits s₀ n t := by
  have hf := fR_fit S.inp
  have hn := S.le
  refine ⟨C, S.cw.keep St.keeps, hn, fun e he => ?_, by rw [hrows]; exact S.rows, ?_, ?_, S.keeps.trans St.keeps⟩
  · rw [← S.ents e he]
    exact ctx_far S.cw St.frame hf (row_fit' (by omega))
  · rw [← S.pre]; exact ctx_far S.cw St.frame hf pre_fit
  · have F := St.frame
    rw [S.esp] at F
    exact S.frame.trans (F.mono fun r hr => List.mem_cons_of_mem _ hr)

/-- A product's writes are a context's operations'. -/
theorem mulR_stR {sp : BitVec 32} {m m' : Mem} {o : Nat} (ho : o ≤ 8)
    (F : Frame (frameR base sp (mulR len .wide o)) m m') : Frame (frameR base sp (stR len 0)) m m' := by
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e1 : lo len (.slot .wide 1) = numBase + st len .wide := by simp [lo]
  have eo : lo len (.slot .wide o) = numBase + o * st len .wide := rfl
  have := Nat.mul_le_mul_right (st len .wide) (show o + 1 ≤ 9 by omega)
  rw [Nat.succ_mul] at this
  refine frameR_widen F fun p hp => ⟨(numBase, 9 * st len .wide), by simp [stR], ?_⟩
  simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> dsimp only <;> omega

/-- A product into slot `o` keeps the table. -/
theorem TS.mul {n : Nat} {u : State} (S : TS Ex base bytes len args P G bits s₀ n u) {o a b : Nat}
    (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a) (ha : a ≤ 8) (hb3 : 3 ≤ b) (hb : b ≤ 8)
    (hB : sv u.mem base len .wide b < P) :
    WP isa (mul .wide o a b) u fun t => TS Ex base bytes len args P G bits s₀ n t ∧ sv t.mem base len .wide o < P ∧
      sv t.mem base len .wide o * 2 ^ (8 * bc len .wide) % P =
        sv u.mem base len .wide a * sv u.mem base len .wide b % P ∧
      (∀ j, 3 ≤ j → j ≤ 8 → j ≠ o → sv t.mem base len .wide j = sv u.mem base len .wide j) ∧
      (∀ d, d + 4 ≤ numBase → w32 t.mem base d = w32 u.mem base d) ∧
      (∀ j, 9 ≤ j → j ≤ 19 → sv t.mem base len .wide j = sv u.mem base len .wide j) := by
  have nb : numBase = 3336 := rfl
  refine WP.mono (cmul_ok S.ctx (o := o) (a := a) (b := b) ho3 ho ha3 ha hb3 hb hB) fun t ⟨C, K, F, L, V⟩ => ?_
  have St : Step Ex base bytes len args u t := Step.ops S.inp (mulR_stR ho F) K
  refine ⟨S.step St C (mul_w32 S.inp F S.inp.room ho (by simp only [rowsOff]; omega)), L, V,
    fun j hj3 hj hne => mulR_sv S.inp F S.inp.room ho3 ho hj3 hj hne,
    fun d hd => mul_w32 S.inp F S.inp.room ho hd, fun j hj9 hj => opsKeep_sv S.inp (mulR_stR ho F) S.inp.room hj9 hj⟩

/-- The workspace through a write of a row of the context. -/
theorem ws_far {u t : State} (C : CtxW base bytes len args u) (hb : bytes < 2 ^ 32) {r : Nat} (hr : r < 34)
    (O : Outside (ctxAddr args) (24 + bc len .wide * r) (bc len .wide) u.mem t.mem) {d N : Nat}
    (hd : d + 4 * N ≤ bytes) : val32 t.mem base d N = val32 u.mem base d N := by
  have rf := row_fit (len := len) hr
  have cw := C.ws.nowrap
  refine val32_far (Outside.frame_span O (by omega)) (fun x hx => ?_) (by omega)
  obtain rfl := List.mem_singleton.mp hx
  exact (C.apart.symm.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ rf)

/-- Slot `a`, entry `n`, to its row. -/
theorem TS.store {n : Nat} {u : State} (S : TS Ex base bytes len args P G bits s₀ n u) (hn : n < 32) {a : Nat}
    (ha : a ≤ 27) (hv : sv u.mem base len .wide a = entV len P G bits n) :
    WP isa (storeRow (rowImm (n + 2)) a) u fun t => TS Ex base bytes len args P G bits s₀ (n + 1) t ∧
      (∀ j, j ≤ 27 → sv t.mem base len .wide j = sv u.mem base len .wide j) ∧
      w32 t.mem base rowsOff = w32 u.mem base rowsOff := by
  have bl := S.inp.bytes_lt
  have nb : numBase = 3336 := rfl
  have bw := bc_eq_cwc len .wide
  have hn2 := S.le
  have nd := S.inp.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  refine WP.mono (storeRow_ok S.inp S.cw (j := n + 2) (by omega) ha (rowImm_idx _)) fun t ⟨I, O, V, K⟩ => ?_
  have W : ∀ {d N : Nat}, d + 4 * N ≤ bytes → val32 t.mem base d N = val32 u.mem base d N :=
    fun hd => ws_far S.cw bl (by omega) O hd
  have Wd : ∀ {d : Nat}, d + 4 ≤ bytes → w32 t.mem base d = w32 u.mem base d := fun {d} hd => by
    rw [← w32_val32_one, ← w32_val32_one]; exact W (by omega)
  have sl : ∀ j, j ≤ 27 → sv t.mem base len .wide j = sv u.mem base len .wide j := fun j hj => by
    have := S.inp.slot_fit .wide (j := j) hj
    have est : st len .wide = 2 * bc len .wide + 32 := rfl
    exact W (by omega)
  have Ct : CtxOk Ex base bytes len args .wide P t := by
    have c0 := S.ctx
    refine ⟨I, by rw [sl 0 (by decide)]; exact c0.mod, c0.gt, c0.odd, ?_⟩
    rw [Wd (by simp only [invOff]; omega)]; exact c0.inv
  have rf := row_fit (len := len) (j := n + 2) (by omega)
  have cw := S.cw.ws.nowrap
  have Fr : Frame [⟨off (ctxAddr args) (24 + bc len .wide * (n + 2)), bc len .wide⟩] u.mem t.mem :=
    Outside.frame_span O (by omega)
  refine ⟨⟨Ct, S.cw.keep K, by omega, fun e he => ?_, by rw [Wd (by simp only [rowsOff]; omega)]; exact S.rows,
    ?_, ?_, S.keeps.trans (K.mono (by decide))⟩, sl, Wd (by simp only [rowsOff]; omega)⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp he with he | rfl
    · rw [← S.ents e he]
      refine O.val32 (.inl ?_) (by have := row_fit' (len := len) (r := 2 + e) (by omega); omega)
      have := Nat.mul_le_mul_left (bc len .wide) (show 2 + e + 1 ≤ n + 2 by omega)
      rw [Nat.mul_succ] at this; omega
    · show val32 t.mem (ctxAddr args) (24 + bc len .wide * (2 + e)) (cwc len .wide) = _
      rw [show 2 + e = e + 2 by omega, V, hv]
  · rw [← S.pre]
    refine O.val32 (.inl ?_) (by have := pre_fit (len := len); omega)
    have := Nat.mul_le_mul_left (bc len .wide) (show 2 ≤ n + 2 by omega)
    omega
  · exact S.frame.trans (Fr.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨ctxR args len, List.mem_cons_self .., Offset.sub_base _ rf⟩)

/-- A write of slot `a` (3 to 27) keeps the table and the context. -/
theorem TS.slot {n : Nat} {u t : State} (S : TS Ex base bytes len args P G bits s₀ n u) {a : Nat} (ha3 : 3 ≤ a)
    (ha : a ≤ 27) (O : Outside base (lo len (.slot .wide a)) (bc len .wide) u.mem t.mem) {rs : List Reg}
    (K : Keeps rs u t) (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) :
    TS Ex base bytes len args P G bits s₀ n t := by
  have h := S.inp
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have fa := h.slot_fit .wide (j := a) ha
  have ea : lo len (.slot .wide a) = numBase + a * st len .wide := rfl
  have := Nat.mul_le_mul_right (st len .wide) ha3
  have di : .edi ∉ rs := fun hm => by have := hrs _ hm; simp at this
  have sp : .esp ∉ rs := fun hm => by have := hrs _ hm; simp at this
  have St : Step Ex base bytes len args u t := Step.slot h ha O K hrs
  refine S.step St (S.ctx.keepF2 K di sp (frameR_of_outside O (by omega) (List.mem_singleton_self _))
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; dsimp only; omega)
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact .inl (by dsimp only; omega)))
    (O.w32 (.inl (by simp only [rowsOff]; omega)) (by simp only [rowsOff]; omega))

/-- Row `2 + e`, entry `e`, to slot `a`. -/
theorem TS.load {n : Nat} {u : State} (S : TS Ex base bytes len args P G bits s₀ n u) {e a : Nat} (he : e < n)
    (ha3 : 3 ≤ a) (ha : a ≤ 27) :
    WP isa (loadRow (rowImm (e + 2)) a) u fun t => TS Ex base bytes len args P G bits s₀ n t ∧
      sv t.mem base len .wide a = entV len P G bits e ∧ Outside base (lo len (.slot .wide a)) (bc len .wide) u.mem t.mem := by
  have hn := S.le
  refine WP.mono (loadRow_ok S.inp S.cw.rd (j := e + 2) (by omega) ha (rowImm_idx _)) fun t ⟨_, O, V, K⟩ => ?_
  refine ⟨S.slot ha3 ha O K, ?_, O⟩
  rw [V, show e + 2 = 2 + e by omega]; exact S.ents e he

/-- Slot 10 copied to slot 5. -/
theorem TS.copy {n : Nat} {u : State} (S : TS Ex base bytes len args P G bits s₀ n u) :
    WP isa (copy (.slot .wide 10) (.slot .wide 5) (one .wide)) u fun t => TS Ex base bytes len args P G bits s₀ n t ∧
      sv t.mem base len .wide 5 = sv u.mem base len .wide 10 ∧
      ∀ j, j ≤ 19 → j ≠ 5 → sv t.mem base len .wide j = sv u.mem base len .wide j := by
  have h := S.inp
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e5 := lo_wide len 5
  have e10 := lo_wide len 10
  refine WP.mono (copy_ok h (x := .slot .wide 10) (d := .slot .wide 5) (one_ok .wide)
    (slot_fit1 h (by decide)) (slot_fit1 h (by decide)) (by rw [cb1]; exact .inl (by omega))) fun t ⟨O, V, K⟩ => ?_
  rw [cb1] at O
  rw [cw1] at V
  exact ⟨S.slot (by decide) (by decide) O K, V, fun j hj hne => slotKeep h hj (Ne.symm hne) O⟩

/-- A write of the row counter keeps the table. -/
theorem TS.iword {n : Nat} {u t : State} (S : TS Ex base bytes len args P G bits s₀ n u)
    (I : In Ex base bytes len args t) (O : Outside base iOff 4 u.mem t.mem) {rs : List Reg} (K : Keeps rs u t)
    (hrs : ∀ q ∈ rs, q ∈ [.eax, .ebx, .ecx, .edx, .ebp, .esi] := by decide) :
    TS Ex base bytes len args P G bits s₀ n t := by
  have h := S.inp
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have di : .edi ∉ rs := fun hm => by have := hrs _ hm; simp at this
  have sp : .esp ∉ rs := fun hm => by have := hrs _ hm; simp at this
  have St : Step Ex base bytes len args u t :=
    ⟨I, fR_of_outside h O (.inr ⟨by simp only [iOff]; omega, by simp only [iOff]; omega⟩), K.mono hrs⟩
  refine S.step St (S.ctx.keepF2 K di sp (frameR_of_outside O (by simp only [iOff]; omega) (List.mem_singleton_self _))
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; simp only [iOff]; omega)
    (by intro p hp; obtain rfl := List.mem_singleton.mp hp; exact .inr ⟨by simp only [iOff]; omega,
      by simp only [iOff]; omega⟩))
    (O.w32 (.inl (by simp only [rowsOff, iOff]; omega)) (by simp only [rowsOff]; omega))

/-- Slot 7 to the power `2^rows`, from `g^E R`: `g^(E 2^rows) R`. -/
theorem squares_ok {n : Nat} {u : State} (S : TS Ex base bytes len args P G bits s₀ n u) {E : Nat}
    (s7 : sv u.mem base len .wide 7 = enc len P G E) (hR : 0 < Spec.Rsa.FixedBaseComb.rows bits)
    (hR' : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639) :
    WP isa squares u fun t => TS Ex base bytes len args P G bits s₀ n t ∧
      sv t.mem base len .wide 7 = enc len P G (E * 2 ^ Spec.Rsa.FixedBaseComb.rows bits) := by
  have nb : numBase = 3336 := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e7 : lo len (.slot .wide 7) = numBase + 7 * st len .wide := rfl
  have P1 := S.ctx.gt
  have cp := S.ctx.coprime
  have bl := S.inp.bytes_lt
  have bw := bc_eq_cwc len .wide
  have f7 := S.inp.slot_fit .wide (j := 7) (by decide)
  unfold squares
  refine WP.seq (wp_movS (readW_ok S.inp (d := rowsOff) (by simp only [rowsOff]; omega) S.rows (by omega))
    fun s₁ U₁ _ => ?_)
  refine WP.mono (counter_store (S.inp.regs U₁.keeps U₁.mem) (d := iOff) (.inr rfl) .eax) fun s₂ ⟨I₂, O₂, W₂, K₂, _⟩ => ?_
  have S₁ := S.step (Step.regs S.inp U₁.mem U₁.keeps) (S.ctx.regs U₁.keeps U₁.mem) (by rw [U₁.mem])
  have S₂ := S₁.iword I₂ O₂ K₂
  have s7₂ : sv s₂.mem base len .wide 7 = enc len P G E := by
    simp only [sv]; rw [O₂.val32 (.inr (by simp only [iOff]; omega)) (by omega), U₁.mem]; exact s7
  have i₂ : w32 s₂.mem base iOff = Spec.Rsa.FixedBaseComb.rows bits := by
    rw [W₂, U₁.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (VG.Proof.Bignum.X86.PublicRt.countLoop hR (fun j t => TS Ex base bytes len args P G bits s₀ n t ∧
      sv t.mem base len .wide 7 = enc len P G (E * 2 ^ j) ∧ w32 t.mem base iOff = Spec.Rsa.FixedBaseComb.rows bits - j)
    (fun j t hj ⟨St, V, W⟩ => ?_) ⟨S₂, by rw [s7₂, Nat.pow_zero, Nat.mul_one], by rw [i₂, Nat.sub_zero]⟩)
    fun t ⟨St, V, _⟩ => ⟨St, V⟩
  refine WP.seq (WP.mono (St.mul (o := 7) (a := 7) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [V]; exact enc_lt (by omega))) fun t₁ ⟨S₁', L₁, V₁, _, H₁, _⟩ => ?_)
  have v₁ := VG.Proof.Rsa.FixedBaseComb.mont_square_encoded cp L₁ V V₁
  have w₁ : w32 t₁.mem base iOff = Spec.Rsa.FixedBaseComb.rows bits - j := by
    rw [H₁ iOff (by simp only [iOff]; omega), W]
  refine WP.mono (dec_ok S₁'.inp (i := Spec.Rsa.FixedBaseComb.rows bits - j) (by omega) (by omega) w₁)
    fun t₂ ⟨I, O, W₂, K, z⟩ => ⟨⟨S₁'.iword I O K, ?_, ?_⟩, ?_⟩
  · simp only [sv]; rw [O.val32 (.inr (by simp only [iOff]; omega)) (by omega)]
    show sv t₁.mem base len .wide 7 = _
    rw [v₁, show 2 * (E * 2 ^ j) = E * 2 ^ (j + 1) by rw [Nat.pow_succ]; ac_rfl]
  · rw [W₂]; omega
  · rw [z]; congr 1; exact decide_eq_decide.mpr (by omega)

/-- Entry `d + j`, entry `j` times entry `d` (in slot 7), for the tooth `d = 2^(k+1)`. -/
theorem product_ok {n : Nat} {u : State} (S : TS Ex base bytes len args P G bits s₀ n u) {k d j : Nat}
    (hk : k < 4) (hd : d = 2 ^ (k + 1)) (hj1 : 1 ≤ j) (hj : j < d) (hn : n = d + j)
    (s7 : sv u.mem base len .wide 7 = entV len P G bits d) :
    WP isa (product d j) u fun t => TS Ex base bytes len args P G bits s₀ (n + 1) t ∧
      sv t.mem base len .wide 7 = entV len P G bits d := by
  subst hn
  have P1 := S.ctx.gt
  have cp := S.ctx.coprime
  have p16 : 2 ^ (k + 1) ≤ 16 := (Nat.pow_le_pow_right (show 0 < 2 by decide) (show k + 1 ≤ 4 by omega) : 2 ^ (k + 1) ≤ 2 ^ 4)
  unfold product
  refine WP.seq (WP.mono (S.load (e := j) (a := 5) (by omega) (by decide) (by decide)) fun t₁ ⟨S₁, V₁, O₁⟩ => ?_)
  have s7₁ : sv t₁.mem base len .wide 7 = entV len P G bits d := by
    rw [slotKeep S.inp (a := 5) (b := 7) (by decide) (by decide) O₁]; exact s7
  refine WP.seq (WP.mono (S₁.mul (o := 8) (a := 5) (b := 7) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [s7₁]; exact enc_lt (by omega))) fun t₂ ⟨S₂, L₂, V₂, K₂, _, _⟩ => ?_)
  have v₂ := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded cp L₂ V₁ s7₁ V₂
  have ex : Spec.Rsa.FixedBaseComb.exponent bits j + Spec.Rsa.FixedBaseComb.exponent bits d =
      Spec.Rsa.FixedBaseComb.exponent bits (d + j) := by
    subst hd
    rw [VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits (k + 1) (by omega), Nat.add_comm (2 ^ (k + 1)) j,
      show j + 2 ^ (k + 1) = 2 ^ (k + 1) + j by omega,
      VG.Proof.Rsa.FixedBaseComb.exponent_add_tooth bits (k + 1) j (by omega) hj]
  rw [ex] at v₂
  have s7₂ : sv t₂.mem base len .wide 7 = entV len P G bits d := by
    rw [K₂ 7 (by decide) (by decide) (by decide)]; exact s7₁
  refine WP.mono (S₂.store (n := d + j) (by omega) (a := 8) (by decide) v₂) fun t ⟨St, Kt, _⟩ => ⟨St, ?_⟩
  rw [Kt 7 (by decide)]; exact s7₂

/-- The tooth `2^(k+1)`: its entry, from the last tooth's, and the entries it adds. -/
theorem column_ok {u : State} {k : Nat} (hk : k < 4) (S : TS Ex base bytes len args P G bits s₀ (2 ^ (k + 1)) u)
    (s7 : sv u.mem base len .wide 7 = entV len P G bits (2 ^ k)) (hR : 0 < Spec.Rsa.FixedBaseComb.rows bits)
    (hR' : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639) :
    WP isa (column k) u fun t => TS Ex base bytes len args P G bits s₀ (2 ^ (k + 2)) t ∧
      sv t.mem base len .wide 7 = entV len P G bits (2 ^ (k + 1)) := by
  have p16 : 2 ^ (k + 1) ≤ 16 := (Nat.pow_le_pow_right (show 0 < 2 by decide) (show k + 1 ≤ 4 by omega) : 2 ^ (k + 1) ≤ 2 ^ 4)
  have p1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have pk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have pk2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  unfold column
  refine WP.seq (WP.mono (squares_ok S s7 hR hR') fun t₁ ⟨S₁, V₁⟩ => ?_)
  have v₁ : sv t₁.mem base len .wide 7 = entV len P G bits (2 ^ (k + 1)) := by
    rw [V₁]
    show enc len P G _ = enc len P G (Spec.Rsa.FixedBaseComb.exponent bits (2 ^ (k + 1)))
    rw [VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits k (by omega),
      VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits (k + 1) (by omega), ← Nat.pow_add, Nat.succ_mul]
  refine WP.seq (WP.mono (S₁.store (n := 2 ^ (k + 1)) (by omega) (a := 7) (by decide) v₁) fun t₂ ⟨S₂, K₂, _⟩ => ?_)
  have v₂ : sv t₂.mem base len .wide 7 = entV len P G bits (2 ^ (k + 1)) := by rw [K₂ 7 (by decide)]; exact v₁
  refine WP.mono (wp_seqs_range (fun j => product (2 ^ (k + 1)) (j + 1)) (fun j t =>
      TS Ex base bytes len args P G bits s₀ (2 ^ (k + 1) + j + 1) t ∧
        sv t.mem base len .wide 7 = entV len P G bits (2 ^ (k + 1))) (2 ^ (k + 1) - 1)
    (fun j hj t ⟨St, Vt⟩ => WP.mono (product_ok St hk rfl (by omega) (by omega) (by omega) Vt)
      fun v hv => by rw [show 2 ^ (k + 1) + (j + 1) + 1 = 2 ^ (k + 1) + j + 1 + 1 by omega]; exact hv)
    ⟨S₂, v₂⟩) fun t ⟨St, Vt⟩ => ⟨?_, Vt⟩
  rw [show 2 ^ (k + 2) = 2 ^ (k + 1) + (2 ^ (k + 1) - 1) + 1 by omega]; exact St

/-- Entry 0, Montgomery one, and entry 1, `g R mod P`, from `R² mod P` in slot 4, one in slot 3 and
`G` in slot 10. -/
theorem initial_ok {u : State} (S : TS Ex base bytes len args P G bits s₀ 0 u)
    (h3 : sv u.mem base len .wide 3 = 1) (h4 : sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P)
    (h10 : sv u.mem base len .wide 10 = G) :
    WP isa (seqs initial) u fun t => TS Ex base bytes len args P G bits s₀ 2 t ∧
      sv t.mem base len .wide 7 = entV len P G bits (2 ^ 0) := by
  have P1 := S.ctx.gt
  have cp := S.ctx.coprime
  have RR : 2 ^ (16 * bc len .wide) = 2 ^ (8 * bc len .wide) * 2 ^ (8 * bc len .wide) := by
    rw [← Nat.pow_add]; congr 1; omega
  have e0 : Spec.Rsa.FixedBaseComb.exponent bits 0 = 0 := VG.Proof.Rsa.FixedBaseComb.exponent_zero bits
  have e1 : Spec.Rsa.FixedBaseComb.exponent bits 1 = 1 := by
    simpa using VG.Proof.Rsa.FixedBaseComb.exponent_tooth bits 0 (by decide)
  show WP isa (.seq (mul .wide 6 4 3) (.seq (storeRow (rowImm 2) 6) (.seq (copy (.slot .wide 10) (.slot .wide 5)
    (one .wide)) (.seq (mul .wide 7 5 4) (.seq (storeRow (rowImm 3) 7) (.block [])))))) u _
  refine WP.seq (WP.mono (S.mul (o := 6) (a := 4) (b := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [h3]; exact P1)) fun t₁ ⟨S₁, L₁, V₁, K₁, _, H₁⟩ => ?_)
  have v₁ : sv t₁.mem base len .wide 6 = entV len P G bits 0 := by
    have v := VG.Proof.Bignum.mont_cancel cp (o := sv t₁.mem base len .wide 6) (c := 2 ^ (8 * bc len .wide))
      (by rw [V₁, h4, h3, Nat.mul_one, Nat.mod_mod, RR])
    rw [Nat.mod_eq_of_lt L₁] at v
    show _ = enc len P G (Spec.Rsa.FixedBaseComb.exponent bits 0)
    rw [v, e0, enc, VG.Proof.Bignum.powMod_eq, Nat.pow_zero, Nat.mod_eq_of_lt P1, Nat.one_mul]
  refine WP.seq (WP.mono (S₁.store (n := 0) (by decide) (a := 6) (by decide) v₁) fun t₂ ⟨S₂, K₂, _⟩ => ?_)
  refine WP.seq (WP.mono S₂.copy fun t₃ ⟨S₃, V₃, K₃⟩ => ?_)
  have g₃ : sv t₃.mem base len .wide 5 = G := by
    rw [V₃, K₂ 10 (by decide), H₁ 10 (by decide) (by decide)]; exact h10
  have r₃ : sv t₃.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P := by
    rw [K₃ 4 (by decide) (by decide), K₂ 4 (by decide), K₁ 4 (by decide) (by decide) (by decide)]; exact h4
  refine WP.seq (WP.mono (S₃.mul (o := 7) (a := 5) (b := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [r₃]; exact Nat.mod_lt _ (by omega))) fun t₄ ⟨S₄, L₄, V₄, _, _, _⟩ => ?_)
  have v₄ : sv t₄.mem base len .wide 7 = entV len P G bits 1 := by
    have v := VG.Proof.Bignum.mont_cancel cp (o := sv t₄.mem base len .wide 7) (c := G * 2 ^ (8 * bc len .wide))
      (by rw [V₄, g₃, r₃, Nat.mul_mod_mod, RR, Nat.mul_assoc])
    rw [Nat.mod_eq_of_lt L₄] at v
    show _ = enc len P G (Spec.Rsa.FixedBaseComb.exponent bits 1)
    rw [v, e1, enc, VG.Proof.Bignum.powMod_eq, Nat.pow_one, Nat.mod_mul_mod]
  refine WP.seq (WP.mono (S₄.store (n := 1) (by decide) (a := 7) (by decide) v₄) fun t₅ ⟨S₅, K₅, _⟩ =>
    WP.block_nil ⟨S₅, ?_⟩)
  rw [K₅ 7 (by decide)]; exact v₄

/-- The table: its 32 entries in rows 2 to 33, from `R² mod P` in slot 4, one in slot 3 and `G` in slot 10. -/
theorem table_ok {u : State} (S : TS Ex base bytes len args P G bits s₀ 0 u)
    (h3 : sv u.mem base len .wide 3 = 1) (h4 : sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % P)
    (h10 : sv u.mem base len .wide 10 = G) (hR : 0 < Spec.Rsa.FixedBaseComb.rows bits)
    (hR' : Spec.Rsa.FixedBaseComb.rows bits ≤ 1639) :
    WP isa table u (TS Ex base bytes len args P G bits s₀ 32) := by
  unfold table
  refine WP.seq (WP.mono (initial_ok S h3 h4 h10) fun t ⟨St, Vt⟩ => ?_)
  refine WP.mono (wp_seqs_range column (fun k t => TS Ex base bytes len args P G bits s₀ (2 ^ (k + 1)) t ∧
      sv t.mem base len .wide 7 = entV len P G bits (2 ^ k)) 4
    (fun k hk t ⟨Sk, Vk⟩ => column_ok hk Sk Vk hR hR') ⟨St, Vt⟩) fun t ⟨St', _⟩ => St'

end

end VG.Proof.Ffdh.X86.Cached

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Precompute
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Impl.Ffdh.X86 (tbOff ldOff tOff)

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- A word of a frame of 16 bytes below `sp`, within the 96 bytes below it. -/
theorem alloc_contains {sp : BitVec 32} (low : 96 ≤ sp.toNat) {d : Nat} (hd : d + 4 ≤ 16) :
    (below sp 96).Contains ((sp - BitVec.ofNat 32 16 + BitVec.ofNat 32 d).setWidth 64) 4 := by
  have hE := sp.isLt
  simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

/-- The frame of 16 bytes below `sp`, within the 96 bytes below it. -/
theorem alloc_sub {sp : BitVec 32} (low : 96 ≤ sp.toNat) :
    Region.Sub ⟨(sp - BitVec.ofNat 32 16).setWidth 64, 16⟩ (below sp 96) := by
  have e16 : (sp - BitVec.ofNat 32 16).setWidth 64 = sp.setWidth 64 - BitVec.ofNat 64 16 :=
    VG.X86.Taint.sub_setWidth (by omega)
  have e96 : (sp - BitVec.ofNat 32 96).setWidth 64 = sp.setWidth 64 - BitVec.ofNat 64 96 :=
    VG.X86.Taint.sub_setWidth (by omega)
  simp only [below]
  rw [e16, e96]
  exact Offset.sub_below _ (by decide) (by decide)

/-- The four bytes below `sp`, within the 96 below it. -/
theorem below4_sub {sp : BitVec 32} (low : 96 ≤ sp.toNat) : Region.Sub (below sp 4) (below sp 96) := by
  have e4 : (sp - BitVec.ofNat 32 4).setWidth 64 = sp.setWidth 64 - BitVec.ofNat 64 4 :=
    VG.X86.Taint.sub_setWidth (by omega)
  have e96 : (sp - BitVec.ofNat 32 96).setWidth 64 = sp.setWidth 64 - BitVec.ofNat 64 96 :=
    VG.X86.Taint.sub_setWidth (by omega)
  simp only [below]
  rw [e4, e96]
  exact Offset.sub_below _ (by decide) (by decide)

/-- A synthetic argument, read in a frame of `4 k` bytes below the stack pointer of `s`. -/
theorem arg_in (h : In Ex base bytes len args s) {t : State} {i k : Nat} (hi : i < 18)
    (sp : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (4 * k)) (rd : t.rd = s.rd) (wr : ∀ r ∈ s.wr, r ∈ t.wr)
    (F : Frame [below (s.gpr .esp) 96] s.mem t.mem) :
    readSrc t (.mem (argAt k i)) = some (args i) := by
  have R := h.arg hi
  have top := h.top
  have hE := (s.gpr .esp).isLt
  have low := h.room.low
  have ea : t.ea (argAt k i) = s.ea (argAt 0 i) := by
    simp only [State.ea, argAt, at_, sp]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have eaS : s.ea (argAt 0 i) = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := by
    simp only [argAt, at_]
    rw [ea_mk, addr_eq (by omega_arith)]
    simp only [Nat.mul_zero, Nat.add_zero]
  change t.load32 (t.ea _) = _
  change s.load32 (s.ea _) = _ at R
  rw [ea]
  simp only [State.load32] at R ⊢
  split at R
  · rename_i hin
    have hin' : InRegions (t.rd ++ t.wr) (s.ea (argAt 0 i)) 4 := by
      obtain ⟨q, hq, hc⟩ := hin
      refine ⟨q, ?_, hc⟩
      rw [rd]
      rcases List.mem_append.mp hq with hq | hq
      · exact List.mem_append_left _ hq
      · exact List.mem_append_right _ (wr _ hq)
    simp only [hin', ↓reduceIte]
    rw [F.readW (r := ⟨s.ea (argAt 0 i), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [eaS]
      simp only [below]
      rw [VG.X86.Taint.sub_setWidth (by omega_arith)]
      exact Offset.disjoint_below _ (by omega_arith)) (by decide)]
    exact R
  · cases R

/-- Bytes of a frame of 16 bytes below `sp`. -/
theorem alloc_in {sp : BitVec 32} (low : 96 ≤ sp.toNat) {d n : Nat} (hd : d + n ≤ 16) :
    (⟨(sp - BitVec.ofNat 32 16).setWidth 64, 16⟩ : Region).Contains (addr (sp - BitVec.ofNat 32 16) d) n := by
  have hE := sp.isLt
  simp only [addr, Region.Contains, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

/-- Two words of a frame of 16 bytes. -/
theorem alloc_rw {m : Mem} {p : BitVec 32} {a b : Nat} {v : BitVec 32} (apart : b + 4 ≤ a ∨ a + 4 ≤ b)
    (fit : p.toNat + 16 ≤ 2 ^ 32) (ha : a + 4 ≤ 16) (hb : b + 4 ≤ 16) :
    (m.writeW (addr p a) v).readW (addr p b) 32 = m.readW (addr p b) 32 := by
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact Mem.readW_writeW_sep (Offset.sep _ apart (by omega) (by omega)) (by decide)

/-- Synthetic argument `i` to the word at `d` of a frame of 16 bytes below the stack pointer of `s`. -/
theorem pass_ok (h : In Ex base bytes len args s) {t : State} {i d : Nat} (hi : i < 18) (hd : d + 4 ≤ 16)
    (sp : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16) (rd : t.rd = s.rd)
    (wr : t.wr = ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ :: s.wr)
    (F : Frame [below (s.gpr .esp) 96] s.mem t.mem) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Keeps [.eax] t u → u.syms = t.syms →
      u.mem = t.mem.writeW (addr (s.gpr .esp - BitVec.ofNat 32 16) d) (args i) →
      Frame [below (s.gpr .esp) 96] s.mem u.mem → WP isa (.block is) u Q) :
    WP isa (.block (.mov .eax (.mem (argAt 4 i)) :: .store (at_ .esp d) .eax :: is)) t Q := by
  have low := h.room.low
  refine wp_movS (arg_in h hi (k := 4) sp rd (fun r hr => by rw [wr]; exact List.mem_cons_of_mem _ hr) F)
    fun u₁ U₁ _ => ?_
  have ea : u₁.ea (at_ .esp d) = addr (s.gpr .esp - BitVec.ofNat 32 16) d := by
    show addr (u₁.gpr .esp) d = _
    rw [U₁.other _ (by decide), sp]
  refine wp_storeS ea ⟨_, by rw [U₁.wr, wr]; exact List.mem_cons_self .., alloc_in low hd⟩ fun u₂ M₂ => k u₂ ?_ ?_ ?_ ?_
  · exact U₁.keeps.trans ((M₂.keeps []).mono (by decide))
  · rw [M₂.syms, U₁.syms]
  · rw [M₂.mem, U₁.mem, U₁.gpr]
  · rw [M₂.mem, U₁.mem]
    exact F.writeW (List.mem_singleton_self _) _ (by
      have := alloc_contains low hd
      simpa only [addr] using this)

/-- Writes of the 96 bytes below `sp`, within a stage's ranges. -/
theorem stk_frameR {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem} (F : Frame [below sp 96] m m') :
    Frame (frameR base sp ws) m m' :=
  F.mono fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self ..

/-- A header word stored. -/
theorem hdr_store (h : In Ex base bytes len args s) {d : Nat} (hd : d + 4 ≤ numBase) (r : Reg) :
    WP isa (.block [.store (sc d) r]) s fun u =>
      In Ex base bytes len args u ∧ Outside base d 4 s.mem u.mem ∧ w32 u.mem base d = (s.gpr r).toNat ∧
      Keeps [] s u ∧ u.syms = s.syms := by
  have bl := h.bytes_lt
  have nd := h.need
  have nb : numBase = 3336 := rfl
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  refine wp_storeS (h.scratch.ea (d := d) (by omega_arith)) (h.scratch.write (d := d) (n := 4) (by omega_arith))
    fun u M => WP.block_nil ?_
  have O : Outside base d 4 s.mem u.mem := by rw [M.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  refine ⟨h.keep (M.keeps []) (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega_arith)), O, ?_, M.keeps [],
    M.syms⟩
  rw [M.mem, w32_write_self]

/-- The vetted groups' table at `T`, from its bytes. -/
theorem tableAt_of {t : State} {T : BitVec 32} (read : InRegions (t.rd ++ t.wr) (byteAddr T) 17744)
    (bs : Spec.Rsa.bytesAt t.mem (byteAddr T) 17744 = VG.Impl.Ffdh.VettedGroups.tableBytes) :
    VettedValidation.TableAt (byteAddr T + BitVec.ofNat 64 0) VG.Impl.Ffdh.VettedGroups.groups t := by
  simp only [BitVec.add_zero]
  have e : (VG.Impl.Ffdh.VettedGroups.groups.flatMap VG.Impl.Ffdh.VettedGroups.Group.bytes).length = 17744 :=
    VG.Proof.Ffdh.VettedTableFacts.tableBytes_length
  refine VettedValidation.tableOfBytes _ _ t (by rw [e]; exact read) (by rw [e]; exact bs) (by rw [e]) ?_
  intro g hg
  simp only [VG.Impl.Ffdh.VettedGroups.groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A recognized width fits a word. -/
theorem recognize_lt (k : Nat) (dom : List Byte) :
    VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups k dom < 2 ^ 32 := by
  have aux : ∀ gs : List VG.Impl.Ffdh.VettedGroups.Group, (∀ g ∈ gs, g.bits < 2 ^ 32) →
      VG.Impl.Ffdh.VettedGroups.recognizeList gs k dom < 2 ^ 32 := by
    intro gs
    induction gs with
    | nil => intro _; simp only [VG.Impl.Ffdh.VettedGroups.recognizeList]; decide
    | cons g gs ih =>
      intro hb
      simp only [VG.Impl.Ffdh.VettedGroups.recognizeList]
      split
      · exact hb g List.mem_cons_self
      · exact ih fun g' hg' => hb g' (List.mem_cons_of_mem _ hg')
  refine aux _ fun g hg => ?_
  simp only [VG.Impl.Ffdh.VettedGroups.groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- After the table's address is saved in the header, from `s`. -/
structure RH (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (T : BitVec 32) (s v : State) : Prop where
  inp : In Ex base bytes len args v
  ebx : v.gpr .ebx = s.gpr .edi
  sp : v.gpr .esp = s.gpr .esp
  keeps : Keeps [.eax, .ebx, .ecx] s v
  frame : Frame (frameR base (s.gpr .esp) (fR len)) s.mem v.mem
  kept : Kept base len [] [tbOff, recOff] s.mem v.mem
  tw : v.mem.readW (off base 16) 32 = T
  syms : v.syms = s.syms

/-- What `ebx := edi`, the table's address and its store into the header leave. -/
theorem rh_of (h : In Ex base bytes len args s) {T : BitVec 32}
    (hT : s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym = T) {s₁ s₂ s₃ : State}
    (U₁ : Upd s s₁ .ebx (s.gpr .edi)) (R : SymAddrPost VG.Impl.Ffdh.X86.VettedValidation.tableSym s₁ s₂)
    (M₃ : Mupd s₂ s₃ (s₂.mem.writeW (off base 16) (s₂.gpr .eax))) : RH Ex base bytes len args T s s₃ := by
  have low := h.room.low
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have sp₂ : s₂.gpr .esp = s.gpr .esp := (R.gpr _ (by decide)).trans (U₁.other _ (by decide))
  have K₂ : Keeps [.eax, .ebx, .ecx] s s₂ := by
    refine ⟨fun r hr => ?_, R.rd.trans U₁.rd, R.wr.trans U₁.wr⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [R.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.2⟩),
      U₁.other _ hr.2.1]
  have ebx₂ : s₂.gpr .ebx = s.gpr .edi := (R.gpr _ (by decide)).trans U₁.gpr
  have eax₂ : s₂.gpr .eax = T := by rw [R.addr, U₁.syms, hT]
  have Fs₂ : Frame [below (s.gpr .esp) 96] s.mem s₂.mem := by
    have F := R.frame
    rw [U₁.mem, U₁.other _ (by decide)] at F
    exact F.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact ⟨_, List.mem_singleton_self _, below4_sub low⟩
  have F₂ : Frame (frameR base (s.gpr .esp) (fR len)) s.mem s₂.mem := stk_frameR Fs₂
  have O₃ : Outside base 16 4 s₂.mem s₃.mem := by rw [M₃.mem]; exact writeW32_outside _ _ _ (by omega)
  have K₃ : Keeps [.eax, .ebx, .ecx] s s₃ := K₂.trans ((M₃.keeps []).mono (by decide))
  have F₃ : Frame (frameR base (s.gpr .esp) (fR len)) s.mem s₃.mem :=
    F₂.trans (fR_of_outside h O₃ (.inl (by omega)))
  exact ⟨h.keepF K₃ (by decide) (by decide) F₃ (fR_fit h), by rw [M₃.gpr]; exact ebx₂,
    by rw [M₃.gpr, sp₂], K₃, F₃,
    ((kept_ops h (stk_frameR Fs₂) h.room).mono).trans (kept_word h (d := 16) (by omega) (by decide) O₃).mono,
    by rw [M₃.mem, Mem.readW_writeW_self32, eax₂], by rw [M₃.syms, R.syms, U₁.syms]⟩

/-- The table's address from `ebx := edi` and the symbol, to its header word: where it is written. -/
theorem saveTable_ok (h : In Ex base bytes len args s) {s₁ s₂ : State} (U₁ : Upd s s₁ .ebx (s.gpr .edi))
    (R : SymAddrPost VG.Impl.Ffdh.X86.VettedValidation.tableSym s₁ s₂) :
    WP isa (.block VG.Impl.Ffdh.X86.VettedValidation.saveTable) s₂ fun s₃ =>
      Mupd s₂ s₃ (s₂.mem.writeW (off base 16) (s₂.gpr .eax)) := by
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have ebx₂ : s₂.gpr .ebx = s.gpr .edi := (R.gpr _ (by decide)).trans U₁.gpr
  have ea₂ : s₂.ea ⟨.ebx, 16⟩ = off base 16 := by
    rw [ea_mk, ebx₂]; exact h.scratch.ea (d := 16) (by omega)
  have wr : s₂.wr = s.wr := R.wr.trans U₁.wr
  exact wp_storeS ea₂ (by rw [wr]; exact h.scratch.write (d := 16) (n := 4) (by omega)) fun s₃ M₃ =>
    WP.block_nil M₃

/-- `ebx := edi`, the table's address, saved in the header. -/
theorem recHead_ok (h : In Ex base bytes len args s) {T : BitVec 32}
    (hT : s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym = T) {X : Prog isa} {Q : State → Prop}
    (k : ∀ v, RH Ex base bytes len args T s v → WP isa X v Q) :
    WP isa (.seq (.block [.mov .ebx (.reg .edi)]) (.seq VG.Impl.Ffdh.X86.VettedValidation.tableAddress
      (.seq (.block VG.Impl.Ffdh.X86.VettedValidation.saveTable) X))) s Q := by
  have low := h.room.low
  refine WP.seq (wp_movS rfl fun s₁ U₁ _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (symFrame_ok _ s₁ (by rw [U₁.other _ (by decide)]; omega)) fun s₂ R => ?_)
  exact WP.seq (WP.mono (saveTable_ok h U₁ R) fun s₃ M₃ => k s₃ (rh_of h hT U₁ R M₃))

/-- The scan's arguments, in its frame: the scan's context. -/
theorem scanCtx_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96)) {T : BitVec 32}
    (tfit : T.toNat + 17744 ≤ 2 ^ 32) (tread : InRegions (s.rd ++ s.wr) (byteAddr T) 17744)
    (tbytes : Spec.Rsa.bytesAt s.mem (byteAddr T) 17744 = VG.Impl.Ffdh.VettedGroups.tableBytes)
    (tws : Region.Disjoint ⟨byteAddr T, 17744⟩ ⟨base, bytes⟩)
    (t40 : Region.Disjoint ⟨byteAddr T, 17744⟩ (below (s.gpr .esp) 96)) {v : State}
    (H : RH Ex base bytes len args T s v) :
    WP isa (.block scanArgs) (allocFrame 16 v) fun w =>
      VettedValidation.Context (args 16) (args 2) (s.gpr .esp - BitVec.ofNat 32 16) T len
        (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) dlen) w ∧
      VettedValidation.TableAt (byteAddr T + BitVec.ofNat 64 0) VG.Impl.Ffdh.VettedGroups.groups w ∧
      w.rd = v.rd ∧ w.wr = ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ :: v.wr ∧
      Frame [below (s.gpr .esp) 96] v.mem w.mem ∧ w.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 ∧
      w.gpr .ebx = args 16 := by
  have low := h.room.low
  have top := h.top
  have hE := (s.gpr .esp).isLt
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have nw := h.scratch.nowrap
  have dl := G.dl
  have lw := G.lower
  have up := G.upper
  have dfit := G.fit
  have h₃ := H.inp
  have sp₃ := H.sp
  have hlen : ∀ m : Mem, (Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen).length = dlen := fun m => by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have ea16 : addr (args 16) 16 = off base 16 := by rw [h.edi_eq]; exact h.scratch.ea (d := 16) (by omega)
  unfold scanArgs
  have aesp : (allocFrame 16 v).gpr .esp = v.gpr .esp - BitVec.ofNat 32 16 := allocFrame_esp _ _
  refine pass_ok h₃ (i := 2) (d := 4) (by decide) (by decide) aesp (allocFrame_rd _ _) (allocFrame_wr _ _)
    (by rw [allocFrame_mem]; exact Frame.refl _ _) fun u₁ K₁ Y₁ M₁ F₁ => ?_
  refine pass_ok h₃ (i := 12) (d := 8) (by decide) (by decide) (by rw [K₁.1 _ (by decide), aesp])
    (by rw [K₁.2.1, allocFrame_rd]) (by rw [K₁.2.2, allocFrame_wr]) F₁ fun u₂ K₂' Y₂ M₂ F₂' => ?_
  refine pass_ok h₃ (i := 1) (d := 12) (by decide) (by decide)
    (by rw [K₂'.1 _ (by decide), K₁.1 _ (by decide), aesp]) (by rw [K₂'.2.1, K₁.2.1, allocFrame_rd])
    (by rw [K₂'.2.2, K₁.2.2, allocFrame_wr]) F₂' fun w Kw Yw Mw Fw => WP.block_nil ?_
  rw [sp₃] at Fw Mw M₂ M₁
  have wbx : w.gpr .ebx = args 16 := by
    rw [Kw.1 _ (by decide), K₂'.1 _ (by decide), K₁.1 _ (by decide), allocFrame_gpr _ _ (by decide), H.ebx,
      h.edi_eq]
  have wrd' : w.rd = v.rd := by rw [Kw.2.1, K₂'.2.1, K₁.2.1, allocFrame_rd]
  have wwr' : w.wr = ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ :: v.wr := by
    rw [Kw.2.2, K₂'.2.2, K₁.2.2, allocFrame_wr, sp₃]
  have wesp' : w.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 := by
    rw [Kw.1 _ (by decide), K₂'.1 _ (by decide), K₁.1 _ (by decide), aesp, sp₃]
  have Fsw : Frame (frameR base (s.gpr .esp) (fR len)) s.mem w.mem := H.frame.trans (stk_frameR Fw)
  have dw : Spec.Rsa.bytesAt w.mem (byteAddr (args 2)) dlen = Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) dlen :=
    KeyScan.bytes_keep h G.apart (by omega) hb40 Fsw
  generalize hP : s.gpr .esp - BitVec.ofNat 32 16 = P at *
  have Pn : P.toNat = (s.gpr .esp).toNat - 16 := by rw [← hP]; exact VG.X86.sub_toNat (by omega)
  have wrd : w.rd = s.rd := by rw [wrd', H.keeps.2.1]
  have wwr : w.wr = ⟨P.setWidth 64, 16⟩ :: s.wr := by rw [wwr', H.keeps.2.2]
  have inw : ∀ {q : Addr} {n : Nat}, InRegions (s.rd ++ s.wr) q n → InRegions (w.rd ++ w.wr) q n := by
    intro q n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    rw [wrd, wwr]
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  refine ⟨?_, ?_, wrd', wwr', Fw, wesp', wbx⟩
  · have wmem : w.mem = ((v.mem.writeW (addr P 4) (args 2)).writeW (addr P 8) (args 12)).writeW (addr P 12)
        (args 1) := by
      rw [Mw, M₂, M₁, allocFrame_mem]
    have Pfit : P.toNat + 16 ≤ 2 ^ 32 := by omega
    have a0 : argAddr w 0 = addr P 4 := by show (w.gpr .esp + _).setWidth 64 = _; rw [wesp']; rfl
    have a1 : argAddr w 1 = addr P 8 := by show (w.gpr .esp + _).setWidth 64 = _; rw [wesp']; rfl
    have a2 : argAddr w 2 = addr P 12 := by show (w.gpr .esp + _).setWidth 64 = _; rw [wesp']; rfl
    refine ⟨wbx, wesp', ?_, ?_, ?_, ?_, ?_, ?_, inw ?_, ?_, ?_, tfit, ?_, ?_, lw, up⟩
    · show w.mem.readW (argAddr w 0) 32 = _
      rw [a0, wmem, alloc_rw (.inl (by decide)) Pfit (by decide) (by decide),
        alloc_rw (.inl (by decide)) Pfit (by decide) (by decide), Mem.readW_writeW_self32]
    · show w.mem.readW (argAddr w 1) 32 = _
      rw [a1, wmem, alloc_rw (.inl (by decide)) Pfit (by decide) (by decide), Mem.readW_writeW_self32, hlen, G.e12]
    · show w.mem.readW (argAddr w 2) 32 = _
      rw [a2, wmem, Mem.readW_writeW_self32, h.outLen]
    · rw [a0]
      exact ⟨_, List.mem_append_right _ (by rw [wwr]; exact List.mem_cons_self ..), alloc_in (sp := s.gpr .esp)
        low (d := 4) (n := 12) (by decide) |> fun c => by rw [hP] at c; exact c⟩
    · rw [ea16]
      exact ⟨_, List.mem_append_right _ (by rw [wwr]; exact List.mem_cons_of_mem _ h.ws.wr),
        Offset.contains_base _ (by omega) (by omega)⟩
    · rw [ea16, Fw.readW (r := ⟨off base 16, 4⟩) (Region.contains_self _ _) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact h.room.apart.symm.sub_left (Offset.sub_base _ (by omega))) (by decide)]
      exact H.tw
    · rw [hlen]; exact G.rd
    · rw [hlen, dw]
    · rw [hlen]; exact dfit
    · omega
    · rw [hlen]; exact dl
  · exact tableAt_of (t := w) (inw tread) (by rw [KeyScan.bytes_keep h tws (by decide) t40 Fsw]; exact tbytes)

/-- The scan, in a frame of its three arguments: `eax` the recognized width. -/
theorem recScan_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96)) {T : BitVec 32}
    (tfit : T.toNat + 17744 ≤ 2 ^ 32) (tread : InRegions (s.rd ++ s.wr) (byteAddr T) 17744)
    (tbytes : Spec.Rsa.bytesAt s.mem (byteAddr T) 17744 = VG.Impl.Ffdh.VettedGroups.tableBytes)
    (tws : Region.Disjoint ⟨byteAddr T, 17744⟩ ⟨base, bytes⟩)
    (t40 : Region.Disjoint ⟨byteAddr T, 17744⟩ (below (s.gpr .esp) 96)) {s₃ : State}
    (H : RH Ex base bytes len args T s s₃) :
    WP isa (.frame (.alloc 16) (.seq (.block scanArgs) (VG.Impl.Ffdh.X86.VettedValidation.scan
      VG.Impl.Ffdh.VettedGroups.groups 0)) (.free 16)) s₃ fun t => t.gpr .esp = s.gpr .esp ∧ t.rd = s₃.rd ∧
      t.wr = s₃.wr ∧ Frame [below (s.gpr .esp) 96] s₃.mem t.mem ∧
      t.gpr .eax = BitVec.ofNat 32 (VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups len
        (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) dlen)) ∧
      Keeps [.eax, .ecx, .edx, .esi, .edi, .ebp] s₃ t := by
  have low := h.room.low
  have sp₃ := H.sp
  have elen : (VG.Impl.Ffdh.VettedGroups.groups.flatMap VG.Impl.Ffdh.VettedGroups.Group.bytes).length = 17744 :=
    VG.Proof.Ffdh.VettedTableFacts.tableBytes_length
  have p16 : 16 ≤ (s₃.gpr .esp).toNat := by rw [sp₃]; omega
  refine WP.frameAlloc (by decide) (by decide) (by decide) p16 (NoSp.of_all (by rfl)) ?_
  refine WP.seq (WP.mono (scanCtx_ok h G hb40 tfit tread tbytes tws t40 H)
    fun w ⟨C, TA, wrd, wwr, Fw, wesp, wbx⟩ => ?_)
  refine WP.mono (VettedValidation.scan_ok _ 0 w C TA (by rw [elen])) fun t ⟨E, Mt, Kt⟩ => ?_
  have tesp : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 := (Kt.1 _ (by decide)).trans wesp
  have fesp : (freed 16 t).gpr .esp = s.gpr .esp := by rw [freed_esp, tesp]; exact BitVec.sub_add_cancel _ _
  refine ⟨fesp, by rw [freed_rd, Kt.2.1, wrd], by rw [freed_wr, Kt.2.2, wwr, List.tail_cons], ?_,
    by rw [freed_gpr _ _ (by decide), E], ?_⟩
  · rw [freed_mem, Mt]; exact Fw
  · refine ⟨fun r hr => ?_, by rw [freed_rd, Kt.2.1, wrd], by rw [freed_wr, Kt.2.2, wwr, List.tail_cons]⟩
    have e : r = .ebx ∨ r = .esp := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      cases r <;> simp_all
    rcases e with rfl | rfl
    · rw [freed_gpr _ _ (by decide), Kt.1 _ (by decide), wbx, H.ebx, h.edi_eq]
    · rw [fesp, sp₃]

/-- The vetted groups' recognized width of the domain, to the header word at 48. -/
theorem recognize_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96)) {T : BitVec 32}
    (hT : s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym = T) (tfit : T.toNat + 17744 ≤ 2 ^ 32)
    (tread : InRegions (s.rd ++ s.wr) (byteAddr T) 17744)
    (tbytes : Spec.Rsa.bytesAt s.mem (byteAddr T) 17744 = VG.Impl.Ffdh.VettedGroups.tableBytes)
    (tws : Region.Disjoint ⟨byteAddr T, 17744⟩ ⟨base, bytes⟩)
    (t40 : Region.Disjoint ⟨byteAddr T, 17744⟩ (below (s.gpr .esp) 96)) :
    WP isa recognize s fun u => Step Ex base bytes len args s u ∧ Kept base len [] [tbOff, recOff] s.mem u.mem ∧
      w32 u.mem base recOff = VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups len
        (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) dlen) := by
  have low := h.room.low
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have elen : (VG.Impl.Ffdh.VettedGroups.groups.flatMap VG.Impl.Ffdh.VettedGroups.Group.bytes).length = 17744 :=
    VG.Proof.Ffdh.VettedTableFacts.tableBytes_length
  unfold recognize
  refine recHead_ok h hT fun s₃ H => ?_
  have sp₃ := H.sp
  have K₃ := H.keeps
  have h₃ := H.inp
  have F₃ := H.frame
  have p16 : 16 ≤ (s₃.gpr .esp).toNat := by rw [sp₃]; omega
  refine WP.seq (WP.mono (recScan_ok h G hb40 tfit tread tbytes tws t40 H) fun s₄ H₄ => ?_)
  -- `edi` back, and the width to the header.
  obtain ⟨sp₄, rd₄, wr₄, Fr₄, ea₄, K₄⟩ := H₄
  refine wp_movS rfl fun s₅ U₅ _ => ?_
  have K₅ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₅ := by
    refine ⟨fun r hr => ?_, by rw [U₅.rd, rd₄, K₃.2.1], by rw [U₅.wr, wr₄, K₃.2.2]⟩
    have e : r = .edi ∨ r = .esp := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      cases r <;> simp_all
    rcases e with rfl | rfl
    · rw [U₅.gpr, K₄.1 _ (by decide)]; exact H.ebx
    · rw [U₅.other _ (by decide), sp₄]
  have Fs₅ : Frame [below (s.gpr .esp) 96] s₃.mem s₅.mem := by rw [U₅.mem]; exact Fr₄
  have F₅ : Frame (frameR base (s.gpr .esp) (fR len)) s.mem s₅.mem := F₃.trans (stk_frameR Fs₅)
  have h₅ : In Ex base bytes len args s₅ := h.keepF K₅ (by decide) (by decide) F₅ (fR_fit h)
  refine WP.mono (hdr_store h₅ (d := recOff) (by simp only [recOff]; omega) .eax) fun u ⟨I, O, W, K, _⟩ => ?_
  refine ⟨⟨I, F₅.trans (fR_of_outside h₅ O (.inr ⟨by simp only [recOff]; omega, by simp only [recOff]; omega⟩)),
    K₅.trans (K.mono (by decide))⟩, ?_, ?_⟩
  · exact (H.kept.trans (kept_ops h₃ (sp := s.gpr .esp) (stk_frameR Fs₅) h.room).mono).trans
      (kept_word h₅ (d := recOff) (by simp only [recOff]; omega) (by decide) O).mono
  · rw [W, U₅.other _ (by decide), ea₄, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (recognize_lt _ _)]

/-- The bit length of the bound's first nonzero byte, `n`, from its mask `2^n − 1`. -/
theorem maskBits_ok (h : In Ex base bytes len args s) {n : Nat} (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (ht : w32 s.mem base tOff = 2 ^ n - 1) :
    WP isa maskBits s fun u => u.gpr .eax = BitVec.ofNat 32 n ∧ u.mem = s.mem ∧ Keeps [.eax, .ecx] s u := by
  have nb : numBase = 3336 := rfl
  have p8 : 2 ^ n ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hn8
  have half : ∀ m < 9, 1 ≤ m → (2 ^ m - 1) / 2 = 2 ^ (m - 1) - 1 := by decide
  have zero : ∀ m < 9, (BitVec.ofNat 32 (2 ^ m - 1) == 0) = decide (m = 0) := by decide
  unfold maskBits
  refine WP.seq (wp_movS rfl fun s₁ U₁ _ => wp_movS (readW_ok (h.regs U₁.keeps U₁.mem) (d := tOff) (v := 2 ^ n - 1)
    (by decide) (by rw [U₁.mem]; exact ht) (by omega)) fun s₂ U₂ _ => WP.block_nil ?_)
  have K₂ : Keeps [.eax, .ecx] s s₂ := (U₁.keeps.mono (by decide)).widen U₂.keeps
  refine WP.mono (KeyScan.count_loop (n := n) (by omega)
    (fun j t => t.gpr .eax = BitVec.ofNat 32 j ∧ t.gpr .ecx = BitVec.ofNat 32 (2 ^ (n - j) - 1) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ecx] s t) (fun j hj t ⟨ea, ec, mt, Kt⟩ => ?_)
    ⟨by rw [U₂.other _ (by decide), U₁.gpr]; rfl, by rw [U₂.gpr, Nat.sub_zero], by rw [U₂.mem, U₁.mem], K₂⟩)
    fun t ⟨ea, _, mt, Kt⟩ => ⟨ea, mt, Kt⟩
  have pj : 2 ^ (n - j) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
  have sh : BitVec.ofNat 32 (2 ^ (n - j) - 1) >>> 1 = BitVec.ofNat 32 (2 ^ (n - (j + 1)) - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow, Nat.pow_one, half (n - j) (by omega) (by omega),
      show n - j - 1 = n - (j + 1) by omega]
    have : 2 ^ (n - (j + 1)) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.mod_eq_of_lt (by omega)]
  refine wp_addS rfl fun t₁ V₁ _ => wp_shr (by decide) fun t₂ V₂ _ => wp_testS rfl fun t₃ V₃ z₃ =>
    WP.block_nil ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [V₃.gpr, V₂.other _ (by decide), V₁.gpr, ea, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_add_ofNat]
  · rw [V₃.gpr, V₂.gpr, V₁.other _ (by decide), ec, sh]
  · rw [V₃.mem, V₂.mem, V₁.mem, mt]
  · exact Kt.trans (((V₁.keeps.mono (by decide)).widen V₂.keeps).trans ((V₃.keeps []).mono (by decide)))
  · rw [z₃, V₂.gpr, V₁.other _ (by decide), ec, sh, BitVec.and_self, zero _ (by omega)]
    congr 1
    exact decide_eq_decide.mpr (by omega)

/-- The bound's bit length, from its first nonzero byte's: `8 (len − 1 − ld)` more. -/
theorem boundBits_ok (h : In Ex base bytes len args s) (h3 : args 3 = BitVec.ofNat 32 len) {ld n : Nat}
    (hld : w32 s.mem base ldOff = ld) (hl : ld < len) (he : s.gpr .eax = BitVec.ofNat 32 n) :
    WP isa (.block boundBits) s fun u =>
      u.gpr .eax = BitVec.ofNat 32 (n + 8 * (len - 1 - ld)) ∧ u.mem = s.mem ∧ Keeps [.eax, .ecx] s u := by
  have nb : numBase = 3336 := rfl
  have up := h.upper
  unfold boundBits
  refine wp_movS (h.arg (i := 3) (by decide)) fun s₁ U₁ _ => wp_subS rfl fun s₂ U₂ _ => ?_
  have K₂ : Keeps [.ecx] s s₂ := U₁.keeps.trans U₂.keeps
  have m₂ : s₂.mem = s.mem := by rw [U₂.mem, U₁.mem]
  refine wp_subS (readW_ok (h.regs K₂ m₂) (d := ldOff) (v := ld) (by decide) (by rw [m₂]; exact hld)
    (by omega)) fun s₃ U₃ _ => wp_addS rfl fun s₄ U₄ _ => wp_addS rfl fun s₅ U₅ _ => wp_addS rfl fun s₆ U₆ _ =>
      wp_addS rfl fun s₇ U₇ _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have c₃ : s₃.gpr .ecx = BitVec.ofNat 32 (len - 1 - ld) := by
      rw [U₃.gpr, U₂.gpr, U₁.gpr, h3, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega), BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    rw [U₇.gpr, U₆.other _ (by decide), U₆.gpr, U₅.gpr, U₄.gpr, c₃, U₅.other _ (by decide), U₄.other _ (by decide),
      U₃.other _ (by decide), U₂.other _ (by decide), U₁.other _ (by decide), he]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, m₂]
  · exact (K₂.mono (by decide) : Keeps [.eax, .ecx] s s₂).trans (((((U₃.keeps.mono (by decide) :
      Keeps [.eax, .ecx] s₂ s₃).widen U₄.keeps).widen U₅.keeps).widen U₆.keeps).widen U₇.keeps)

/-- The width the code chooses: the recognized width `r` where it is not zero and below the bound's
bit length `b`. -/
def pick (r b : Nat) : Nat := if r = 0 then b else if r < b then r else b

/-- The recognized width, where it is not zero and below the bound's bit length. -/
theorem cap_ok (h : In Ex base bytes len args s) {r b : Nat} (hr : w32 s.mem base recOff = r) (hrl : r < 2 ^ 32)
    (he : s.gpr .eax = BitVec.ofNat 32 b) (hb : b < 2 ^ 32) :
    WP isa cap s fun u => u.gpr .eax = BitVec.ofNat 32 (pick r b) ∧ u.mem = s.mem ∧ Keeps [.eax, .edx] s u := by
  have nb : numBase = 3336 := rfl
  unfold cap
  refine WP.seq (wp_movS (readW_ok h (d := recOff) (by simp only [recOff]; omega) hr hrl) fun s₁ U₁ _ =>
    wp_testS rfl fun s₂ V₂ z₂ => WP.block_nil ?_)
  have ed₂ : s₂.gpr .edx = BitVec.ofNat 32 r := by rw [V₂.gpr, U₁.gpr]
  have ea₂ : s₂.gpr .eax = BitVec.ofNat 32 b := by rw [V₂.gpr, U₁.other _ (by decide), he]
  have K₂ : Keeps [.edx] s s₂ := U₁.keeps.trans ((V₂.keeps []).mono (by decide))
  have m₂ : s₂.mem = s.mem := by rw [V₂.mem, U₁.mem]
  have z : (BitVec.ofNat 32 r &&& BitVec.ofNat 32 r == 0) = decide (r = 0) := by
    rw [BitVec.and_self]
    by_cases e : r = 0
    · subst e; rfl
    · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro c
      have := congrArg BitVec.toNat c
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrl] at this
      exact e this
  refine WP.ite (decide (r = 0)) (by show s₂.zf = _; rw [z₂, U₁.gpr, z]) (fun hz => WP.block_nil ?_) (fun hz => ?_)
  · have e : r = 0 := of_decide_eq_true hz
    refine ⟨by rw [ea₂, pick, ite_eq_left e], m₂, K₂.mono (by decide)⟩
  · have e : r ≠ 0 := of_decide_eq_false hz
    refine WP.seq (wp_cmp fun s₃ V₃ c₃ _ => WP.block_nil ?_)
    rw [ed₂, ea₂, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrl, Nat.mod_eq_of_lt hb] at c₃
    refine WP.ite (decide (r < b)) c₃ (fun hc => wp_movS rfl fun s₄ U₄ _ => WP.block_nil ?_) (fun hc => WP.block_nil ?_)
    · refine ⟨by rw [U₄.gpr, V₃.gpr, ed₂, pick, ite_eq_right e, ite_eq_left (of_decide_eq_true hc)],
        by rw [U₄.mem, V₃.mem, m₂], (K₂.mono (by decide) : Keeps [.eax, .edx] s s₂).trans
          (((V₃.keeps []).mono (by decide) : Keeps [.eax, .edx] s₂ s₃).widen U₄.keeps)⟩
    · refine ⟨by rw [V₃.gpr, ea₂, pick, ite_eq_right e, ite_eq_right (of_decide_eq_false hc)], by rw [V₃.mem, m₂],
        K₂.trans ((V₃.keeps []).mono (by decide)) |>.mono (by decide)⟩

/-- A word of the context written through `ecx = ctx`. -/
theorem ctx_store (h : In Ex base bytes len args s) (C : CtxW base bytes len args s) (hc : s.gpr .ecx = args ctxArg)
    {d : Nat} (hd : d + 4 ≤ 24) (r : Reg) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, In Ex base bytes len args u → CtxW base bytes len args u →
      u.mem = s.mem.writeW (off (ctxAddr args) d) (s.gpr r) → u.gpr = s.gpr → Keeps [] s u →
      Frame [ctxR args len] s.mem u.mem → WP isa (.block is) u Q) :
    WP isa (.block (.store ⟨.ecx, d⟩ r :: is)) s Q := by
  have afit := C.rd.afit
  have nw := C.ws.nowrap
  have ad : s.ea ⟨.ecx, d⟩ = off (ctxAddr args) d := by
    rw [ea_mk, hc]; exact addr_eq (by simp only [ctxBytes] at afit; omega)
  have cin : (ctxR args len).Contains (off (ctxAddr args) d) 4 :=
    Offset.contains_base _ (by simp only [ctxBytes]; omega) (by omega)
  refine wp_storeS ad ⟨_, C.ws.wr, cin⟩ fun u M => ?_
  have F : Frame [ctxR args len] s.mem u.mem := by
    rw [M.mem]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ cin
  have K := M.keeps []
  exact k u (KeyCut.in_keepOut h K (by decide) (by decide) F C.argsApart) (C.keep K) M.mem M.gpr K F

/-- A header word written in CPS. -/
theorem hdr_storeK (h : In Ex base bytes len args s) {d : Nat} (hd : d + 4 ≤ numBase) (r : Reg) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u, In Ex base bytes len args u → u.mem = s.mem.writeW (off base d) (s.gpr r) → u.gpr = s.gpr →
      Keeps [] s u → Outside base d 4 s.mem u.mem → WP isa (.block is) u Q) :
    WP isa (.block (.store (sc d) r :: is)) s Q := by
  have bl := h.bytes_lt
  have nd := h.need
  have nb : numBase = 3336 := rfl
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  refine wp_storeS (h.scratch.ea (d := d) (by omega_arith)) (h.scratch.write (d := d) (n := 4) (by omega_arith))
    fun u M => ?_
  have O : Outside base d 4 s.mem u.mem := by rw [M.mem]; exact writeW32_outside _ _ _ (by omega_arith)
  exact k u (h.keep (M.keeps []) (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega_arith))) M.mem M.gpr
    (M.keeps []) O

/-- A word read through the write of another of the same base. -/
theorem w32_other {m : Mem} {P : Addr} {d e : Nat} {v : BitVec 32} (hde : d + 4 ≤ e ∨ e + 4 ≤ d)
    (hd : d + 4 ≤ 2 ^ 64) (he : e + 4 ≤ 2 ^ 64) : w32 (m.writeW (off P e) v) P d = w32 m P d :=
  congrArg BitVec.toNat (Mem.readW_writeW_sep (Offset.sep P hde hd he) (by decide))

/-- A word of a region read through a write of another, apart from it. -/
theorem w32_far {m : Mem} {P Q : Addr} {d e n k : Nat} {v : BitVec 32}
    (hR : Region.Disjoint ⟨P, n⟩ ⟨Q, k⟩) (hd : d + 4 ≤ n) (he : e + 4 ≤ k) (hn : n < 2 ^ 64) (hk : k < 2 ^ 64) :
    w32 (m.writeW (off Q e) v) P d = w32 m P d :=
  congrArg BitVec.toNat (Mem.readW_writeW_sep (hR.sep (Offset.contains_base _ hd (by omega))
    (Offset.contains_base _ he (by omega))) (by decide))

theorem w32_ofNat_self {m : Mem} {P : Addr} {d v : Nat} (hv : v < 2 ^ 32) :
    w32 (m.writeW (off P d) (BitVec.ofNat 32 v)) P d = v := by
  rw [w32_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

/-- The width `W` and its metadata: to the header, its width and rows, and to the context's first six
words, the width, its bytes and its rows, 64 bits each. -/
theorem metadata_ok (h : In Ex base bytes len args s) (C : CtxW base bytes len args s) {W : Nat}
    (he : s.gpr .eax = BitVec.ofNat 32 W) (hW : W ≤ 8192) :
    WP isa (.block metadata) s fun u => In Ex base bytes len args u ∧ CtxW base bytes len args u ∧
      Frame (ctxR args len :: frameR base (s.gpr .esp) (fR len)) s.mem u.mem ∧
      Keeps [.eax, .ecx, .edx] s u ∧ w32 u.mem base bitsOff = W ∧
      w32 u.mem base rowsOff = Spec.Rsa.FixedBaseComb.rows W ∧
      w32 u.mem (ctxAddr args) 0 = W ∧ w32 u.mem (ctxAddr args) 4 = 0 ∧
      w32 u.mem (ctxAddr args) 8 = (W + 7) / 8 ∧ w32 u.mem (ctxAddr args) 12 = 0 ∧
      w32 u.mem (ctxAddr args) 16 = Spec.Rsa.FixedBaseComb.rows W ∧ w32 u.mem (ctxAddr args) 20 = 0 := by
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have cb : 24 ≤ ctxBytes len := by simp only [ctxBytes]; omega
  have cl : ctxBytes len < 2 ^ 64 := by have := C.ws.nowrap; omega
  have ap := C.apart
  have bo : bitsOff = 52 := rfl
  have ro : rowsOff = 56 := rfl
  have rw' : Spec.Rsa.FixedBaseComb.rows W = (W + 4) * 52429 / 2 ^ 18 := by
    simp only [Spec.Rsa.FixedBaseComb.rows, Spec.Rsa.FixedBaseComb.teeth]; omega
  have rl : Spec.Rsa.FixedBaseComb.rows W < 2 ^ 32 := by rw [rw']; omega
  -- Through each kind of write.
  have cc : ∀ {m : Mem} {d e : Nat} {v : BitVec 32}, d + 4 ≤ 24 → e + 4 ≤ 24 → (d + 4 ≤ e ∨ e + 4 ≤ d) →
      w32 (m.writeW (off (ctxAddr args) e) v) (ctxAddr args) d = w32 m (ctxAddr args) d :=
    fun hd he hde => w32_other hde (by omega) (by omega)
  have cbw : ∀ {m : Mem} {d e : Nat} {v : BitVec 32}, d + 4 ≤ 24 → e + 4 ≤ bytes →
      w32 (m.writeW (off base e) v) (ctxAddr args) d = w32 m (ctxAddr args) d :=
    fun hd he => w32_far ap (by omega) he cl (by omega)
  have bcw : ∀ {m : Mem} {d e : Nat} {v : BitVec 32}, d + 4 ≤ bytes → e + 4 ≤ 24 →
      w32 (m.writeW (off (ctxAddr args) e) v) base d = w32 m base d :=
    fun hd he => w32_far ap.symm hd (by omega) (by omega) cl
  unfold metadata
  refine hdr_storeK h (d := bitsOff) (by omega) .eax fun s₁ h₁ M₁ G₁ K₁ O₁ => ?_
  have C₁ := C.keep K₁
  refine wp_movS (h₁.arg (i := ctxArg) (by decide)) fun s₂ U₂ _ => ?_
  have h₂ := h₁.regs U₂.keeps U₂.mem
  have C₂ := C₁.keep U₂.keeps
  refine ctx_store h₂ C₂ U₂.gpr (d := 0) (by decide) .eax fun s₃ h₃ C₃ M₃ G₃ K₃ F₃ => ?_
  refine wp_movS rfl fun s₄ U₄ _ => wp_addS rfl fun s₅ U₅ _ => wp_shr (by decide) fun s₆ U₆ _ => ?_
  have K₆ : Keeps [.edx] s₃ s₆ := ((U₄.keeps.widen U₅.keeps).widen U₆.keeps)
  have m₆ : s₆.mem = s₃.mem := by rw [U₆.mem, U₅.mem, U₄.mem]
  have h₆ := h₃.regs K₆ m₆
  have C₆ := C₃.keep K₆
  have ec₆ : s₆.gpr .ecx = args ctxArg := by
    rw [U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide), G₃, U₂.gpr]
  refine ctx_store h₆ C₆ ec₆ (d := 8) (by decide) .edx fun s₇ h₇ C₇ M₇ G₇ K₇ F₇ => ?_
  refine wp_addS rfl fun s₈ U₈ _ => wp_movS rfl fun s₉ U₉ _ => wp_mul fun s₁₀ U₁₀ => wp_shr (by decide) fun s₁₁ U₁₁ _ => ?_
  have K₁₁ : Keeps [.eax, .edx] s₇ s₁₁ := ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [U₁₁.other _ hr.1, U₁₀.other _ hr.1 hr.2, U₉.other _ hr.2, U₈.other _ hr.1],
    by rw [U₁₁.rd, U₁₀.rd, U₉.rd, U₈.rd], by rw [U₁₁.wr, U₁₀.wr, U₉.wr, U₈.wr]⟩
  have m₁₁ : s₁₁.mem = s₇.mem := by rw [U₁₁.mem, U₁₀.mem, U₉.mem, U₈.mem]
  have h₁₁ := h₇.regs K₁₁ m₁₁
  have C₁₁ := C₇.keep K₁₁
  have ea₁₁ : s₁₁.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows W) := by
    rw [U₁₁.gpr, U₁₀.eax, U₉.gpr, U₉.other _ (by decide), U₈.gpr, G₇, U₆.other _ (by decide), U₅.other _ (by decide),
      U₄.other _ (by decide), G₃, U₂.other _ (by decide), G₁, he]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.shiftRight_eq_div_pow]
    rw [rw']
    have : (52429 : BitVec 32).toNat = 52429 := rfl
    have h4 : (4 : BitVec 32).toNat = 4 := rfl
    rw [this, h4, Nat.mod_eq_of_lt (show W < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show W + 4 < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show (W + 4) * 52429 < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show (W + 4) * 52429 / 2 ^ 18 < 2 ^ 32 by omega)]
  refine hdr_storeK h₁₁ (d := rowsOff) (by omega) .eax fun s₁₂ h₁₂ M₁₂ G₁₂ K₁₂ O₁₂ => ?_
  have C₁₂ := C₁₁.keep K₁₂
  refine wp_movS (h₁₂.arg (i := ctxArg) (by decide)) fun s₁₃ U₁₃ _ => ?_
  have h₁₃ := h₁₂.regs U₁₃.keeps U₁₃.mem
  have C₁₃ := C₁₂.keep U₁₃.keeps
  refine ctx_store h₁₃ C₁₃ U₁₃.gpr (d := 16) (by decide) .eax fun s₁₄ h₁₄ C₁₄ M₁₄ G₁₄ K₁₄ F₁₄ => ?_
  refine wp_movS rfl fun s₁₅ U₁₅ _ => ?_
  have h₁₅ := h₁₄.regs U₁₅.keeps U₁₅.mem
  have C₁₅ := C₁₄.keep U₁₅.keeps
  have ec₁₅ : s₁₅.gpr .ecx = args ctxArg := by rw [U₁₅.other _ (by decide), G₁₄, U₁₃.gpr]
  refine ctx_store h₁₅ C₁₅ ec₁₅ (d := 4) (by decide) .eax fun s₁₆ h₁₆ C₁₆ M₁₆ G₁₆ K₁₆ F₁₆ => ?_
  refine ctx_store h₁₆ C₁₆ (by rw [G₁₆]; exact ec₁₅) (d := 12) (by decide) .eax fun s₁₇ h₁₇ C₁₇ M₁₇ G₁₇ K₁₇ F₁₇ => ?_
  refine ctx_store h₁₇ C₁₇ (by rw [G₁₇, G₁₆]; exact ec₁₅) (d := 20) (by decide) .eax
    fun u hu Cu Mu Gu Ku Fu => WP.block_nil ?_
  have v3 : s₂.gpr .eax = BitVec.ofNat 32 W := by rw [U₂.other _ (by decide), G₁, he]
  have v7 : s₆.gpr .edx = BitVec.ofNat 32 ((W + 7) / 8) := by
    rw [U₆.gpr, U₅.gpr, U₄.gpr, G₃, v3]
    apply BitVec.eq_of_toNat_eq
    have h7 : (7 : BitVec 32).toNat = 7 := rfl
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_add, Nat.shiftRight_eq_div_pow, h7]
    rw [Nat.mod_eq_of_lt (show W < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show W + 7 < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show (W + 7) / 2 ^ 3 < 2 ^ 32 by omega)]
  have v14 : s₁₃.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows W) := by
    rw [U₁₃.other _ (by decide), G₁₂, ea₁₁]
  have v16 : s₁₅.gpr .eax = 0 := U₁₅.gpr
  have v17 : s₁₆.gpr .eax = 0 := by rw [G₁₆, v16]
  have vu : s₁₇.gpr .eax = 0 := by rw [G₁₇, v17]
  have mu : u.mem = (((((((s.mem.writeW (off base bitsOff) (BitVec.ofNat 32 W)).writeW (off (ctxAddr args) 0)
      (BitVec.ofNat 32 W)).writeW (off (ctxAddr args) 8) (BitVec.ofNat 32 ((W + 7) / 8))).writeW (off base rowsOff)
      (BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows W))).writeW (off (ctxAddr args) 16)
      (BitVec.ofNat 32 (Spec.Rsa.FixedBaseComb.rows W))).writeW (off (ctxAddr args) 4) (0 : BitVec 32)).writeW
      (off (ctxAddr args) 12) (0 : BitVec 32)).writeW (off (ctxAddr args) 20) (0 : BitVec 32) := by
    rw [Mu, vu, M₁₇, v17, M₁₆, v16, U₁₅.mem, M₁₄, v14, U₁₃.mem, M₁₂, ea₁₁, m₁₁, M₇, v7, m₆, M₃, v3, U₂.mem, M₁, he]
  rw [U₂.mem] at F₃
  rw [m₆] at F₇
  rw [m₁₁] at O₁₂
  rw [U₁₃.mem] at F₁₄
  rw [U₁₅.mem] at F₁₆
  have up : ∀ {m m' : Mem}, Frame [ctxR args len] m m' →
      Frame (ctxR args len :: frameR base (s.gpr .esp) (fR len)) m m' :=
    fun F => F.mono fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self ..
  have upB : ∀ {m m' : Mem}, Frame (frameR base (s.gpr .esp) (fR len)) m m' →
      Frame (ctxR args len :: frameR base (s.gpr .esp) (fR len)) m m' :=
    fun F => F.mono fun r hr => List.mem_cons_of_mem _ hr
  have Fb₁ := upB (fR_of_outside h O₁ (.inr ⟨by omega, by omega⟩))
  have Fb₁₂ := upB (fR_of_outside h O₁₂ (.inr ⟨by omega, by omega⟩))
  refine ⟨hu, Cu, ((((((Fb₁.trans (up F₃)).trans (up F₇)).trans Fb₁₂).trans (up F₁₄)).trans (up F₁₆)).trans
      (up F₁₇)).trans (up Fu), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((((((((((K₁.mono (by decide) : Keeps [.eax, .ecx, .edx] s s₁).widen U₂.keeps).widen K₃).widen K₆).widen
      K₇).widen K₁₁).widen K₁₂).widen U₁₃.keeps).widen K₁₄).widen U₁₅.keeps).widen K₁₆).widen K₁₇).widen Ku)
  · rw [mu, bcw, bcw, bcw, bcw, w32_other, bcw, bcw, w32_ofNat_self] <;> omega
  · rw [mu, bcw, bcw, bcw, bcw, w32_ofNat_self] <;> omega
  · rw [mu, cc, cc, cc, cc, cbw, cc, w32_ofNat_self] <;> omega
  · rw [mu, cc, cc, w32_write_self] <;> first | rfl | omega
  · rw [mu, cc, cc, cc, cc, cbw, w32_ofNat_self] <;> omega
  · rw [mu, cc, w32_write_self] <;> first | rfl | omega
  · rw [mu, cc, cc, cc, w32_ofNat_self] <;> omega
  · rw [mu, w32_write_self]; rfl

end

end VG.Proof.Ffdh.X86.Cached

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Precompute
open VG.Impl.Ffdh.X86 (tbOff foundOff ldOff tOff)
open VG.Proof.Ffdh.KeyScalar (bnd)
open VG.Proof.Ffdh (lead)

/-! ## The width -/

/-- The bound's first significant byte is not zero. -/
theorem lead_ne {k : Nat} {dom : List Byte} (dv : Spec.Ffdh.domainValid k dom = true) (hk : 64 ≤ k)
    (size : dom.length = 2 * k ∨ dom.length = 3 * k) :
    (bnd k dom).getD (lead (bnd k dom)) 0 ≠ 0 := by
  have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length size
  have hne : bnd k dom ≠ [] := by intro he; rw [he] at hbl; simp at hbl; omega
  obtain ⟨hodd, h1p, -⟩ := VG.Proof.Bignum.valid_facts (VG.Proof.Ffdh.domainValid_mod dv) hk
  have hld := VG.Proof.Ffdh.lead_lt hne
  rw [hbl] at hld
  have hbits := VG.Proof.Ffdh.KeyScalar.bound_bits (k := k) (dom := dom) (by omega) size
    (fun _ => ⟨hodd, h1p⟩)
  have hbnd : 2 ≤ Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) := by
    have hv := (VG.Proof.Ffdh.domainValid_iff k dom).mp dv
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv.2.2 q hq).1.2.1; simp only [Option.getD_some]; omega
  rw [← List.getElem_eq_getD (h := VG.Proof.Ffdh.lead_lt hne) 0]
  intro hb0
  by_cases hlast : lead (bnd k dom) + 1 < (bnd k dom).length
  · exact VG.Proof.Ffdh.lead_nonzero hne hlast hb0
  · rw [hb0] at hbits
    have : Spec.RsaKeyGen.bitLength (0 : Byte).toNat = 0 := rfl
    rw [this] at hbits
    have hpos := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds
      (show Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≠ 0 by omega)).2
    rw [hbits] at hpos
    rw [hbl] at hlast
    have : k - lead (bnd k dom) - 1 = 0 := by omega
    rw [this] at hpos
    omega

/-- The width the code computes is `generationScalarBits`'s. -/
theorem width_spec {k : Nat} {dom : List Byte} (dv : Spec.Ffdh.domainValid k dom = true) (hk : 64 ≤ k)
    (size : dom.length = 2 * k ∨ dom.length = 3 * k) :
    pick (VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups k dom)
      (Spec.RsaKeyGen.bitLength ((bnd k dom).getD (lead (bnd k dom)) 0).toNat + 8 * (k - 1 - lead (bnd k dom))) =
      Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) := by
  have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length size
  have hne : bnd k dom ≠ [] := by intro he; rw [he] at hbl; simp at hbl; omega
  obtain ⟨hodd, h1p, hnorm⟩ := VG.Proof.Bignum.valid_facts (VG.Proof.Ffdh.domainValid_mod dv) hk
  have hbits := VG.Proof.Ffdh.KeyScalar.bound_bits (k := k) (dom := dom) (by omega) size
    (fun _ => ⟨hodd, h1p⟩)
  rw [List.getElem_eq_getD (h := VG.Proof.Ffdh.lead_lt hne) 0] at hbits
  have e : Spec.RsaKeyGen.bitLength ((bnd k dom).getD (lead (bnd k dom)) 0).toNat + 8 * (k - 1 - lead (bnd k dom)) =
      Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) := by
    rw [hbits]; omega
  rw [e, VG.Proof.Ffdh.VettedGroupFacts.recognize_spec (by omega) size hnorm]
  cases h : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom) with
  | none => simp only [Option.getD_none, pick, ite_true, Spec.Ffdh.generationScalarBits, h]
  | some bits =>
    have bf := VG.Proof.Ffdh.ContextRows.recognized_nonzero h
    simp only [Option.getD_some, pick, bf, ite_false, Spec.Ffdh.generationScalarBits, h, Nat.min_def]
    by_cases c : bits < Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))
    · rw [ite_eq_left c, ite_eq_left (Nat.le_of_lt c)]
    · rw [ite_eq_right c]
      by_cases c' : bits ≤ Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom))
      · rw [ite_eq_left c']; omega
      · rw [ite_eq_right c']

/-! ## The context's words -/

/-- A run of words from a longer one. -/
theorem val32_mid (m : Mem) (P : Addr) (d j k l : Nat) :
    val32 m P (d + 4 * j) k = val32 m P d (j + k + l) / 2 ^ (32 * j) % 2 ^ (32 * k) := by
  rw [val32_append m P d (j + k) l, val32_append m P d j k]
  have A := val32_lt m P d j
  have B := val32_lt m P (d + 4 * j) k
  rw [Nat.mul_add 32 j k, Nat.pow_add, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt A, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt B]

/-- The context's words from its 32-bit words: the width, its bytes and its rows, `p`, `R² mod p`
and the 32 entries. -/
theorem values_of {m : Mem} {args : Nat → BitVec 32} {len : Nat} {dom : List Byte}
    (bf : Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom) ≤ 8192)
    (h0 : w32 m (ctxAddr args) 0 = Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom))
    (h4 : w32 m (ctxAddr args) 4 = 0)
    (h8 : w32 m (ctxAddr args) 8 = (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom) + 7) / 8)
    (h12 : w32 m (ctxAddr args) 12 = 0)
    (h16 : w32 m (ctxAddr args) 16 =
      Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom)))
    (h20 : w32 m (ctxAddr args) 20 = 0)
    (r0 : rowV m args len 0 = (Spec.Ffdh.domainOf len dom).p)
    (r1 : rowV m args len 1 = 2 ^ (16 * bc len .wide) % (Spec.Ffdh.domainOf len dom).p)
    (re : ∀ e < 32, rowV m args len (2 + e) = entV len (Spec.Ffdh.domainOf len dom).p (Spec.Ffdh.domainOf len dom).g
      (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom)) e) :
    Spec.Rsa.wordsAt m (ctxAddr args) (3 + 34 * mw len) = generationValues len dom := by
  have hb : bc len .wide = 8 * mw len := rfl
  have hc : cwc len .wide = 2 * mw len := by simp only [cwc, hb]; omega
  have rw' : ∀ j, VG.Proof.Ffdh.ContextRows.row m (ctxAddr args) (mw len) j =
      Spec.Rsa.toWords (rowV m args len j) (mw len) := fun j => by
    rw [VG.Proof.Ffdh.ContextRows.row_self, rowV, hc, VG.Proof.Ffdh.ContextRows.val32_eq_wv, hb,
      show 8 * mw len * j = 8 * (mw len) * j from rfl]
  have wd : ∀ {d v : Nat}, v < 2 ^ 64 → w32 m (ctxAddr args) d + 2 ^ 32 * w32 m (ctxAddr args) (d + 4) = v →
      VG.Proof.Bignum.word m (ctxAddr args) d = BitVec.ofNat 64 v := fun {d v} hv e => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
    exact (word_eq_w32 m (ctxAddr args) d).trans e
  have rs := (VG.Proof.Rsa.FixedBaseComb.rows_small bf).1
  rw [VG.Proof.Ffdh.ContextRows.generationValues_parts]
  refine VG.Proof.Ffdh.ContextRows.ctx_words (wd (d := 0) (by omega) (by rw [h0, h4]; omega))
    (wd (d := 8) (by omega) (by rw [h8, h12]; omega)) (wd (d := 16) (by omega) (by rw [h16, h20]; omega)) ?_ ?_ fun e he => ?_
  · rw [rw', r0]
  · rw [rw', r1, show 16 * bc len .wide = 128 * mw len by rw [hb]; omega]
  · rw [rw', re e he, entV, enc, hb, show 8 * (8 * mw len) = 64 * mw len by omega]

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- Slot `a` to row `j` (0 or 1) of the context, which keeps the working space. -/
theorem storePre_ok {P : Nat} (Cx : CtxOk Ex base bytes len args .wide P s) (C : CtxW base bytes len args s)
    {j a : Nat} (hj : j < 2) (ha : a ≤ 27) :
    WP isa (storeRow (rowImm j) a) s fun t => CtxOk Ex base bytes len args .wide P t ∧ CtxW base bytes len args t ∧
      rowV t.mem args len j = sv s.mem base len .wide a ∧
      Outside (ctxAddr args) (24 + bc len .wide * j) (bc len .wide) s.mem t.mem ∧
      (∀ {d N : Nat}, d + 4 * N ≤ bytes → val32 t.mem base d N = val32 s.mem base d N) ∧
      Frame [ctxR args len] s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have h := Cx.inp
  have bl := h.bytes_lt
  have nb : numBase = 3336 := rfl
  have bw := bc_eq_cwc len .wide
  refine WP.mono (storeRow_ok h C (j := j) (by omega) ha (rowImm_idx _)) fun t ⟨I, O, V, K⟩ => ?_
  have W : ∀ {d N : Nat}, d + 4 * N ≤ bytes → val32 t.mem base d N = val32 s.mem base d N :=
    fun hd => ws_far C bl (by omega) O hd
  have Wd : ∀ {d : Nat}, d + 4 ≤ bytes → w32 t.mem base d = w32 s.mem base d := fun {d} hd => by
    rw [← w32_val32_one, ← w32_val32_one]; exact W (by omega)
  have Ct : CtxOk Ex base bytes len args .wide P t := by
    have f0 := h.slot_fit .wide (j := 0) (by decide)
    have est : st len .wide = 2 * bc len .wide + 32 := rfl
    refine ⟨I, ?_, Cx.gt, Cx.odd, ?_⟩
    · show val32 _ _ _ _ = _; rw [W (by omega)]; exact Cx.mod
    · rw [Wd (by have := h.need; simp only [invOff, CrtRt.need] at *; omega)]; exact Cx.inv
  have rf := row_fit (len := len) (j := j) (by omega)
  have cw := C.ws.nowrap
  refine ⟨Ct, C.keep K, V, O, W, ?_, K.mono (by decide)⟩
  exact (Outside.frame_span O (by omega)).sub fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨ctxR args len, List.mem_singleton_self _, Offset.sub_base _ rf⟩

/-- The domain's bytes through writes of the context, the working space and the stack. -/
theorem dom_keepC (h : In Ex base bytes len args s) {dlen : Nat} {rd wr : List Region}
    (G : DomGeo args base bytes len dlen rd wr) {sp : BitVec 32}
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96))
    (domC : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (ctxR args len)) {m m' : Mem}
    (F : Frame (ctxR args len :: frameR base sp (fR len)) m m') :
    Spec.Rsa.bytesAt m' (byteAddr (args 2)) dlen = Spec.Rsa.bytesAt m (byteAddr (args 2)) dlen := by
  have := G.fit
  refine frame_bytes F (fun r hr => ?_) (by omega)
  rcases List.mem_cons.mp hr with rfl | hr
  · exact domC
  · exact dom_frame h G hb40 r hr

/-- A component of the domain through writes of the context, the working space and the stack. -/
theorem comp_keepC (h : In Ex base bytes len args s) {dlen : Nat} {rd wr : List Region}
    (G : DomGeo args base bytes len dlen rd wr) {sp : BitVec 32}
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below sp 96))
    (domC : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (ctxR args len)) {m m' : Mem}
    (F : Frame (ctxR args len :: frameR base sp (fR len)) m m') {k : Nat} (hk : k * len + len ≤ dlen) :
    comp m' args len k = comp m args len k := by
  have := G.fit
  unfold comp
  refine congrArg _ (frame_bytes F (fun r hr => ?_) (by omega))
  rcases List.mem_cons.mp hr with rfl | hr
  · exact domC.sub_left (Offset.sub_base _ hk)
  · exact (dom_frame h G hb40 r hr).sub_left (Offset.sub_base _ hk)

/-- A word of the context's header through the table. -/
theorem pre_word {m m' : Mem} (hp : preV m' args len = preV m args len) {i : Nat} (hi : i < 6) :
    w32 m' (ctxAddr args) (4 * i) = w32 m (ctxAddr args) (4 * i) := by
  have e : ∀ m : Mem, w32 m (ctxAddr args) (4 * i) = preV m args len / 2 ^ (32 * i) % 2 ^ (32 * 1) := fun m => by
    rw [← w32_val32_one, show 4 * i = 0 + 4 * i by omega, val32_mid m _ 0 i 1 (5 - i + 2 * cwc len .wide),
      show i + 1 + (5 - i + 2 * cwc len .wide) = 6 + 2 * cwc len .wide by omega]
  rw [e, e, hp]

/-- Row 0 or 1 of the context through the table. -/
theorem pre_row {m m' : Mem} (hp : preV m' args len = preV m args len) {j : Nat} (hj : j < 2) :
    rowV m' args len j = rowV m args len j := by
  have bw := bc_eq_cwc len .wide
  have e : ∀ m : Mem, rowV m args len j =
      preV m args len / 2 ^ (32 * (6 + cwc len .wide * j)) % 2 ^ (32 * cwc len .wide) := fun m => by
    rw [rowV, show 24 + bc len .wide * j = 0 + 4 * (6 + cwc len .wide * j) by rw [bw, Nat.mul_assoc]; omega,
      val32_mid m _ 0 (6 + cwc len .wide * j) (cwc len .wide) (cwc len .wide - cwc len .wide * j),
      show 6 + cwc len .wide * j + cwc len .wide + (cwc len .wide - cwc len .wide * j) = 6 + 2 * cwc len .wide by
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> omega]
  rw [e, e, hp]

/-- The precomputation's body: the context of the domain, and 1. -/
theorem pcBody_ok (h : In Ex base bytes len args s) {dlen : Nat} (G : DomGeo args base bytes len dlen s.rd s.wr)
    (hb40 : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (below (s.gpr .esp) 96))
    (domC : Region.Disjoint ⟨byteAddr (args 2), dlen⟩ (ctxR args len)) (C : CtxW base bytes len args s)
    {T : BitVec 32} (hT : s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym = T) (tfit : T.toNat + 17744 ≤ 2 ^ 32)
    (tread : InRegions (s.rd ++ s.wr) (byteAddr T) 17744)
    (tbytes : Spec.Rsa.bytesAt s.mem (byteAddr T) 17744 = VG.Impl.Ffdh.VettedGroups.tableBytes)
    (tws : Region.Disjoint ⟨byteAddr T, 17744⟩ ⟨base, bytes⟩)
    (t40 : Region.Disjoint ⟨byteAddr T, 17744⟩ (below (s.gpr .esp) 96))
    (dv : Spec.Ffdh.domainValid len (KeyGen.domOf s.mem args dlen) = true) :
    WP isa Precompute.body s fun t => t.gpr .eax = 1 ∧
      Frame (ctxR args len :: frameR base (s.gpr .esp) (fR len)) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧
      Spec.Rsa.wordsAt t.mem (ctxAddr args) (3 + 34 * mw len) = generationValues len (KeyGen.domOf s.mem args dlen) := by
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  have nd := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have dl := G.dl
  have lw := G.lower
  have up := G.upper
  have dfit := G.fit
  have h2 : 2 * len ≤ dlen := by omega
  generalize hD : KeyGen.domOf s.mem args dlen = dom at dv
  have size : dom.length = 2 * len ∨ dom.length = 3 * len := by
    rw [← hD, VG.Proof.Bignum.bytesAt_length]; exact dl
  obtain ⟨hodd, h1p, -⟩ := VG.Proof.Bignum.valid_facts (VG.Proof.Ffdh.domainValid_mod dv) lw
  have bf := VG.Proof.Ffdh.ContextRows.genBits_facts dv
  have hp : comp s.mem args len 0 = (Spec.Ffdh.domainOf len dom).p := by rw [comp_p s.mem args h2, ← hD]
  have hg : comp s.mem args len 1 = (Spec.Ffdh.domainOf len dom).g := by rw [comp_g s.mem args h2, ← hD]
  have up' : ∀ {m m' : Mem}, Frame [ctxR args len] m m' →
      Frame (ctxR args len :: frameR base (s.gpr .esp) (fR len)) m m' :=
    fun F => F.mono fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self ..
  have upB : ∀ {m m' : Mem}, Frame (frameR base (s.gpr .esp) (fR len)) m m' →
      Frame (ctxR args len :: frameR base (s.gpr .esp) (fR len)) m m' :=
    fun F => F.mono fun r hr => List.mem_cons_of_mem _ hr
  unfold Precompute.body
  -- The recognized width.
  refine WP.seq (WP.mono (recognize_ok h G hb40 hT tfit tread tbytes tws t40) fun u₁ ⟨S₁, k₁, r₁⟩ => ?_)
  rw [show Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) dlen = dom from hD] at r₁
  have sp₁ := S₁.esp
  -- The bound's first significant byte and its mask.
  have G₁ := G.keep ⟨rfl, rfl⟩ S₁.keeps
  refine WP.seq (WP.mono (KeyScan.scan_ok S₁.inp G.e3 (KeyGen.bound_geo G₁ (by rw [sp₁]; exact hb40)))
    fun u₂ Sc => ?_)
  have bs : Spec.Rsa.bytesAt u₁.mem (byteAddr (KeyScan.boundAt args)) len = bnd len dom := by
    rw [KeyGen.bound_bytes G, dom_keep h G hb40 S₁.frame]; exact congrArg _ hD
  rw [bs] at Sc
  have hbl := VG.Proof.Ffdh.KeyScalar.bnd_length size
  have hne : bnd len dom ≠ [] := by intro he; rw [he] at hbl; simp at hbl; omega
  have hld : lead (bnd len dom) < len := by have := VG.Proof.Ffdh.lead_lt hne; rwa [hbl] at this
  generalize hb : (bnd len dom).getD (lead (bnd len dom)) 0 = b at Sc
  have b0 : b ≠ 0 := hb ▸ lead_ne dv lw size
  have bt : b.toNat ≠ 0 := fun e => b0 (BitVec.eq_of_toNat_eq e)
  have hn := VG.Proof.Ffdh.KeyScalar.bitLength_bounds bt
  have hn1 : 1 ≤ Spec.RsaKeyGen.bitLength b.toNat := by
    simp only [Spec.RsaKeyGen.bitLength, bt, ↓reduceIte]; omega
  have hn8 : Spec.RsaKeyGen.bitLength b.toNat ≤ 8 := by
    have := b.isLt
    by_contra hc
    have : 2 ^ 8 ≤ 2 ^ (Spec.RsaKeyGen.bitLength b.toNat - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have S₁₂ := S₁.trans Sc.step
  -- Its bit length.
  refine WP.seq (WP.mono (maskBits_ok Sc.step.inp (n := Spec.RsaKeyGen.bitLength b.toNat) hn1 hn8
    (by rw [Sc.t, hb, VG.Proof.Ffdh.KeyScalar.smearN_eq _ b.isLt])) fun u₃ ⟨e₃, m₃, K₃⟩ => ?_)
  have h₃ := Sc.step.inp.regs K₃ m₃
  refine WP.seq (WP.mono (boundBits_ok h₃ G.e3 (ld := lead (bnd len dom)) (by rw [m₃]; exact Sc.ld) hld e₃)
    fun u₄ ⟨e₄, m₄, K₄⟩ => ?_)
  have h₄ := h₃.regs K₄ m₄
  -- The width.
  have rec₄ : w32 u₄.mem base recOff =
      VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups len dom := by
    rw [m₄, m₃, Sc.kept.word_eq (by simp only [recOff, numBase]; decide)]; exact r₁
  refine WP.seq (WP.mono (cap_ok h₄ rec₄ (recognize_lt _ _) e₄ (by omega)) fun u₅ ⟨e₅, m₅, K₅⟩ => ?_)
  have h₅ := h₄.regs K₅ m₅
  rw [show Spec.RsaKeyGen.bitLength b.toNat + 8 * (len - 1 - lead (bnd len dom)) =
      Spec.RsaKeyGen.bitLength ((bnd len dom).getD (lead (bnd len dom)) 0).toNat + 8 * (len - 1 - lead (bnd len dom))
      by rw [hb], width_spec dv lw size] at e₅
  generalize hW : Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf len dom) = W at e₅ bf
  have bW : W ≤ 8192 := by omega
  -- The metadata.
  have K₁₅ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₅ :=
    S₁₂.keeps.trans ((K₃.mono (by decide)).trans ((K₄.mono (by decide)).trans (K₅.mono (by decide))))
  have m₂₅ : u₅.mem = u₂.mem := by rw [m₅, m₄, m₃]
  have sp₅ : u₅.gpr .esp = s.gpr .esp := K₁₅.1 _ (by decide)
  refine WP.seq (WP.mono (metadata_ok h₅ (C.keep K₁₅) e₅ bW)
    fun u₆ ⟨h₆, C₆, F₆, K₆, _, wr₆, c0, c4, c8, c12, c16, c20⟩ => ?_)
  rw [sp₅, m₂₅] at F₆
  have FA₆ : Frame (ctxR args len :: frameR base (s.gpr .esp) (fR len)) s.mem u₆.mem := (upB S₁₂.frame).trans F₆
  have K₁₆ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s u₆ := K₁₅.trans (K₆.mono (by decide))
  have sp₆ : u₆.gpr .esp = s.gpr .esp := K₁₆.1 _ (by decide)
  have G₆ := G.keep ⟨rfl, rfl⟩ K₁₆
  -- p, one and `p − 1`.
  refine WP.seq (WP.mono (pSetup_ok h₆ G.e3 (by omega)
    (by have := VG.CallLay.inRegions_sub G₆.rd (off := 0) (l := len) (by omega) (by omega)
        rwa [BitVec.add_zero] at this)
    (G.apart.sub_left (Region.sub_prefix (by omega)))) fun u₇ ⟨h₇, F₇, k₇, v9, _, _, K₇⟩ => ?_)
  rw [CheckDomain.argNum_comp, comp_keepC h G hb40 domC FA₆ (by omega), hp] at v9
  rw [sp₆] at F₇
  have FA₇ := FA₆.trans (upB F₇)
  have K₁₇ := K₁₆.trans K₇
  -- g.
  refine WP.seq (WP.mono (loadComp_ok h₇ (G.keep ⟨rfl, rfl⟩ K₁₇) (k := 1) (j := 10) (by decide) (by omega)
    (by decide)) fun u₈ ⟨v10, O₈, K₈⟩ => ?_)
  rw [comp_keepC h G hb40 domC FA₇ (by omega), hg] at v10
  have S₈ : Step Ex base bytes len args u₇ u₈ := Step.slot h₇ (by decide) O₈ K₈
  have k₈ := kept_slot h₇ (a := 10) O₈
  have sp₇ : u₇.gpr .esp = s.gpr .esp := K₁₇.1 _ (by decide)
  have F₈ := S₈.frame
  rw [sp₇] at F₈
  have FA₈ := FA₇.trans (upB F₈)
  have K₁₈ := K₁₇.trans S₈.keeps
  -- p's context.
  have v9₈ : sv u₈.mem base len .wide 9 = (Spec.Ffdh.domainOf len dom).p := by rw [k₈.slot_eq]; exact v9
  refine WP.seq (WP.mono (ctxP_ok S₈.inp (P := (Spec.Ffdh.domainOf len dom).p) (by rw [v9₈]; exact safeM_of h1p hodd))
    fun u₉ ⟨Cx₉, s3, s4, F₉, k₉, K₉⟩ => ?_)
  have sp₈ : u₈.gpr .esp = s.gpr .esp := K₁₈.1 _ (by decide)
  rw [sp₈] at F₉
  have FA₉ := FA₈.trans (upB (fR_widen F₉ (stR_inF S₈.inp)))
  have K₁₉ := K₁₈.trans K₉
  -- Rows 0 and 1: p and `R² mod p`.
  refine WP.seq (WP.mono (storePre_ok Cx₉ (C.keep K₁₉) (j := 0) (a := 9) (by decide) (by decide))
    fun u₁₀ ⟨Cx₁₀, C₁₀, rv₁₀, O₁₀, W₁₀, F₁₀, K₁₀⟩ => ?_)
  refine WP.seq (WP.mono (storePre_ok Cx₁₀ C₁₀ (j := 1) (a := 4) (by decide) (by decide))
    fun u₁₁ ⟨Cx₁₁, C₁₁, rv₁₁, O₁₁, W₁₁, F₁₁, K₁₁⟩ => ?_)
  have FA₁₁ := (FA₉.trans (up' F₁₀)).trans (up' F₁₁)
  have K₁₁' := (K₁₉.trans K₁₀).trans K₁₁
  have sw : ∀ {j : Nat}, j ≤ 27 → sv u₁₁.mem base len .wide j = sv u₉.mem base len .wide j := fun {j} hj => by
    have := Cx₉.inp.slot_fit .wide (j := j) hj
    have est : st len .wide = 2 * bc len .wide + 32 := rfl
    have bw := bc_eq_cwc len .wide
    show val32 _ _ _ _ = val32 _ _ _ _
    rw [W₁₁ (by omega), W₁₀ (by omega)]
  have rows₁₁ : w32 u₁₁.mem base rowsOff = Spec.Rsa.FixedBaseComb.rows W := by
    rw [← w32_val32_one, W₁₁ (by simp only [rowsOff]; omega), W₁₀ (by simp only [rowsOff]; omega), w32_val32_one,
      k₉.word_eq (by simp only [rowsOff, numBase]; decide), k₈.word_eq (by simp only [rowsOff, numBase]; decide),
      k₇.word_eq (by simp only [rowsOff, numBase]; decide)]
    exact wr₆
  -- The table.
  have S₀ : TS Ex base bytes len args (Spec.Ffdh.domainOf len dom).p (Spec.Ffdh.domainOf len dom).g W u₁₁ 0 u₁₁ :=
    ⟨Cx₁₁, C₁₁, by omega, fun e he => absurd he (Nat.not_lt_zero _), rows₁₁, rfl, Frame.refl _ _, Keeps.refl _ _⟩
  have rs := VG.Proof.Rsa.FixedBaseComb.rows_small bW
  refine WP.seq (WP.mono (table_ok S₀ (by rw [sw (by decide)]; exact s3) (by rw [sw (by decide)]; exact s4)
    (by rw [sw (by decide), k₉.slot_eq]; exact v10) (VG.Proof.Rsa.FixedBaseComb.rows_pos (by omega)) rs.1)
    fun u₁₂ S₁₂' => WP.mono ret_ok fun t ⟨et, mt, Kt⟩ => ?_)
  have sp₁₁ : u₁₁.gpr .esp = s.gpr .esp := K₁₁'.1 _ (by decide)
  have F₁₂ := S₁₂'.frame
  rw [sp₁₁] at F₁₂
  refine ⟨by rw [et]; rfl, by rw [mt]; exact FA₁₁.trans F₁₂, K₁₁'.trans (S₁₂'.keeps.trans (Kt.mono (by decide))), ?_⟩
  -- The context's words.
  have bw := bc_eq_cwc len .wide
  have bg := bc_ge lw .wide
  have cbn : ctxBytes len = 24 + bc len .wide * 34 := rfl
  have cw := C.ws.nowrap
  have F69 : Frame (frameR base (s.gpr .esp) (fR len)) u₆.mem u₉.mem :=
    (F₇.trans F₈).trans (fR_widen F₉ (stR_inF S₈.inp))
  have hdr : ∀ i, i < 6 → w32 t.mem (ctxAddr args) (4 * i) = w32 u₆.mem (ctxAddr args) (4 * i) := fun i hi => by
    rw [mt, pre_word S₁₂'.pre hi, O₁₁.w32 (.inl (by omega)) (by omega), O₁₀.w32 (.inl (by omega)) (by omega),
      ← w32_val32_one, ← w32_val32_one, ctx_far C F69 (fR_fit h) (by omega)]
  have r0 : rowV t.mem args len 0 = (Spec.Ffdh.domainOf len dom).p := by
    rw [mt, pre_row S₁₂'.pre (by decide)]
    show val32 _ _ _ _ = _
    rw [O₁₁.val32 (.inl (by omega)) (by omega)]
    rw [show val32 u₁₀.mem (ctxAddr args) (24 + bc len .wide * 0) (cwc len .wide) = rowV u₁₀.mem args len 0 from rfl,
      rv₁₀, k₉.slot_eq]
    exact v9₈
  have r1 : rowV t.mem args len 1 = 2 ^ (16 * bc len .wide) % (Spec.Ffdh.domainOf len dom).p := by
    rw [mt, pre_row S₁₂'.pre (by decide), rv₁₁]
    have := Cx₉.inp.slot_fit .wide (j := 4) (by decide)
    have est : st len .wide = 2 * bc len .wide + 32 := rfl
    show val32 _ _ _ _ = _
    rw [W₁₀ (by omega)]
    exact s4
  have e0 := hdr 0 (by decide)
  have e1 := hdr 1 (by decide)
  have e2 := hdr 2 (by decide)
  have e3 := hdr 3 (by decide)
  have e4 := hdr 4 (by decide)
  have e5 := hdr 5 (by decide)
  rw [c0] at e0
  rw [c4] at e1
  rw [c8] at e2
  rw [c12] at e3
  rw [c16] at e4
  rw [c20] at e5
  subst hW
  refine values_of bW e0 e1 e2 e3 e4 e5 r0 r1 fun e he => ?_
  rw [mt]; exact S₁₂'.ents e he

end

end VG.Proof.Ffdh.X86.Cached

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.CrtRt (In mw)
open VG.Proof.Ffdh.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Ffdh.X86 (argsFrame)
open VG.Impl.Ffdh.X86.Cached

/-- The tables the precomputation reads. -/
abbrev pcConsts : List (String × List (BitVec 64)) := VG.Impl.Ffdh.X86.VettedValidation.tableConsts

/-- The precomputation's contract. -/
abbrev pcContract : Contract isa := Spec.Ffdh.generationPrecomputeContract (abi.withConsts pcConsts) stack

/-- What the contract gives `vg_ffdh_generate_key_precompute(ctx, ctx_len, domain, domain_len, p_len, scratch,
scratch_len)`, but the tables. -/
structure PreABI (s : State) : Prop where
  stackLow : stack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 4 + 28 ≤ 2 ^ 32
  rdIn : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region) ∈ s.rd
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat * 8⟩, ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩,
    ⟨argAddr s 0, 28⟩]
  ctxDom : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  ctxScratch : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint
    ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩
  ctxArgs : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  domScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩
  domArgs : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  scratchArgs : (⟨argumentPointer s 5, (arg s 6).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  retCtx : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩
  retDom : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩
  retArgs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  belowCtx : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩
  belowDom : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint
    ⟨argumentPointer s 5, (arg s 6).toNat * 8⟩
  belowArgs : (⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ : Region).Disjoint ⟨argAddr s 0, 28⟩
  ctxBound : (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32
  domBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  scratchBound : (arg s 5).toNat + (arg s 6).toNat * 8 ≤ 2 ^ 32
  pLen : Spec.Ffdh.pLenValid (arg s 4).toNat
  dLen : Spec.Ffdh.domainLenValid (arg s 4).toNat (arg s 3).toNat
  ctxLen : (arg s 1).toNat = Spec.Ffdh.generationPrecomputedWords (arg s 4).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 4).toNat ≤ (arg s 6).toNat
  valid : Spec.Ffdh.domainValid (arg s 4).toNat (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat) = true

theorem preABI_plain {s : State} (h : (Spec.Ffdh.generationPrecomputeContract abi stack).pre s) : PreABI s := by
  sig_pre [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi,
    argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  have hrd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩] := by assumption
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (with_reducible assumption)
    | (rw [hrd]; exact List.mem_cons_self ..)

theorem preABI_of {s : State} (h : pcContract.pre s) : PreABI s ∧ ConstsOk pcConsts stack s := by
  obtain ⟨hp, hc⟩ := pre_consts.mp h
  have A := preABI_plain hp
  exact ⟨⟨A.stackLow, A.stackBound, stripConsts_rd_mem A.rdIn, A.wr, A.ctxDom, A.ctxScratch, A.ctxArgs,
    A.domScratch, A.domArgs, A.scratchArgs, A.retCtx, A.retDom, A.retScratch, A.retArgs, A.belowCtx, A.belowDom,
    A.belowScratch, A.belowArgs, A.ctxBound, A.domBound, A.scratchBound, A.pLen, A.dLen, A.ctxLen,
    A.scratchLength, A.valid⟩, hc⟩

abbrev pArgs : Impl.Ffdh.X86.Args := Impl.Ffdh.X86.Cached.Precompute.args

theorem wrapABI' {s : State} (A : PreABI s) : WrapABI pArgs 7 s where
  below := ⟨(fun _ h => by cases h), by decide, by decide, by decide, (fun _ h => by cases h),
    (fun _ h => by cases h), by decide, (fun _ h => by cases h; decide)⟩
  stackLow := A.stackLow
  stackBound := by have := A.stackBound; omega
  argsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  wsIn := by rw [A.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  scratchArgs := A.scratchArgs
  retScratch := A.retScratch
  belowScratch := A.belowScratch
  scratchBound := A.scratchBound
  lower := A.pLen.1
  upper := A.pLen.2
  scratchLength := A.scratchLength

theorem pcFrameBody_all :
    (Code.seq (.block (Impl.Ffdh.X86.fill pArgs)) Impl.Ffdh.X86.Cached.Precompute.body :
      Prog isa).allInstrs VG.Proof.Mont.X86.StaticSquare.noSp = true := by
  rsa_stack_shape

/-- The bytes of the domain at entry. -/
abbrev pcDom (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat

/-- What the body may read: the domain and the table; and write: the context. -/
abbrev PRd (s : State) : List Region → List Region → Prop :=
  fun rd wr => InRegions (rd ++ wr) (argumentPointer s 2) (arg s 3).toNat ∧
    (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region) ∈ wr ∧
    InRegions (rd ++ wr) (symAddr s VG.Impl.Ffdh.X86.VettedValidation.tableSym) 17744

theorem pcWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = 3 + 34 * ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords]
  omega

/-- The context's bytes. -/
theorem pcCtxBytes {s : State} (A : PreABI s) : (arg s 1).toNat * 8 = ctxBytes (pLenOf pArgs s) := by
  have := A.ctxLen
  rw [pcWords_eq] at this
  simp only [ctxBytes, CrtRt.bc, mw, Spec.Rsa.modulusWords]
  show _ = 24 + 8 * (((arg s 4).toNat + 7) / 8) * 34
  omega

/-- The table, and the 96 bytes below the frame and the frame, within the stack below the caller's. -/
theorem pc_subs {s : State} (A : PreABI s) {sp : BitVec 32} (espf : sp = s.gpr .esp - BitVec.ofNat 32 argsFrame) :
    Region.Sub (below sp 96) ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ ∧
      Region.Sub ⟨sp.setWidth 64, 76⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
  have fb : argsFrame = 76 := rfl
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by omega)
  have espN : sp.toNat = (s.gpr .esp).toNat - 76 := by rw [espf]; exact VG.X86.sub_toNat (by omega)
  refine ⟨?_, ?_⟩
  · simp only [below]
    rw [VG.X86.Taint.sub_setWidth (by rw [espN]; omega), espf,
      show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA,
      ← VG.Offset.sub_add_eq, show BitVec.ofNat 64 argsFrame + 96#64 = BitVec.ofNat 64 172 from rfl]
    exact Region.sub_prefix (by decide)
  · rw [espf, show (s.gpr .esp - BitVec.ofNat 32 argsFrame).setWidth 64 = frameAt s from rfl, FA]
    exact Offset.sub_below _ (by decide) (by decide)

/-- A table's region, apart from what the code writes. -/
theorem single_apart {name : String} {words : List (BitVec 64)} {s : State} {st : Nat}
    (h : ConstsOk [(name, words)] st s) :
    (symAddr s name).toNat + 8 * words.length ≤ 2 ^ 32 ∧
      (∀ r ∈ s.wr, Region.Disjoint ⟨symAddr s name, 8 * words.length⟩ r) ∧
      ∀ r ∈ abi.reserved st s, Region.Disjoint ⟨symAddr s name, 8 * words.length⟩ r :=
  h.2.2.1 ⟨symAddr s name, 8 * words.length⟩ List.mem_cons_self

/-- The tables' region, apart from what the code writes. -/
theorem table_apart {s : State} (hc : ConstsOk pcConsts stack s) :
    (symAddr s VG.Impl.Ffdh.X86.VettedValidation.tableSym).toNat + 17744 ≤ 2 ^ 32 ∧
      (∀ r ∈ s.wr, Region.Disjoint ⟨symAddr s VG.Impl.Ffdh.X86.VettedValidation.tableSym, 17744⟩ r) ∧
      Region.Disjoint ⟨symAddr s VG.Impl.Ffdh.X86.VettedValidation.tableSym, 17744⟩
        ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
  have T := single_apart (name := VG.Impl.Ffdh.X86.VettedValidation.tableSym)
    (words := VG.Impl.Ffdh.VettedGroups.tableWords) hc
  rw [VG.Proof.Ffdh.VettedTableFacts.tableWords_length] at T
  exact ⟨T.1, T.2.1, T.2.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

/-- What the body needs, from the frame's state. -/
theorem pc_frame_facts {s : State} (A : PreABI s) (hc : ConstsOk pcConsts stack s) (f : State)
    (I : In (PRd s) (wsBase pArgs s) (wsSize pArgs s) (pLenOf pArgs s) (synth pArgs (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase pArgs s, wsSize pArgs s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem) :
    DomGeo (synth pArgs (arg s)) (wsBase pArgs s) (wsSize pArgs s) (pLenOf pArgs s) (arg s 3).toNat f.rd f.wr ∧
      Region.Disjoint ⟨byteAddr (synth pArgs (arg s) 2), (arg s 3).toNat⟩ (below (f.gpr .esp) 96) ∧
      Region.Disjoint ⟨byteAddr (synth pArgs (arg s) 2), (arg s 3).toNat⟩
        (ctxR (synth pArgs (arg s)) (pLenOf pArgs s)) ∧
      CtxW (wsBase pArgs s) (wsSize pArgs s) (pLenOf pArgs s) (synth pArgs (arg s)) f ∧
      (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym).toNat + 17744 ≤ 2 ^ 32 ∧
      Spec.Rsa.bytesAt f.mem (byteAddr (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym)) 17744 = VG.Impl.Ffdh.VettedGroups.tableBytes ∧
      Region.Disjoint ⟨byteAddr (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym), 17744⟩ ⟨wsBase pArgs s, wsSize pArgs s⟩ ∧
      Region.Disjoint ⟨byteAddr (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym), 17744⟩ (below (f.gpr .esp) 96) ∧
      KeyGen.domOf f.mem (synth pArgs (arg s)) (arg s 3).toNat = pcDom s := by
  obtain ⟨sub96, subF⟩ := pc_subs A espf
  obtain ⟨tfit, twr, t172⟩ := table_apart hc
  have hE := (s.gpr .esp).isLt
  have low := A.stackLow
  have st' : stack = 172 := rfl
  have FA : frameAt s = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 argsFrame :=
    VG.X86.Taint.sub_setWidth (by simp only [argsFrame]; omega)
  have frameSub : Region.Sub ⟨frameAt s, argsFrame⟩ ⟨(s.gpr .esp).setWidth 64 - 172#64, 172⟩ := by
    rw [FA]; exact Offset.sub_below _ (by decide) (by decide)
  have ofn : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have cb := pcCtxBytes A
  have G : DomGeo (synth pArgs (arg s)) (wsBase pArgs s) (wsSize pArgs s) (pLenOf pArgs s) (arg s 3).toNat
      f.rd f.wr :=
    ⟨(ofn _).symm, (ofn _).symm, (ofn _).symm, rfl, rfl, (ofn _).symm, A.dLen, A.domBound, I.extra.1, A.domScratch,
      A.pLen.1, A.pLen.2⟩
  have hb40 : Region.Disjoint ⟨byteAddr (synth pArgs (arg s) 2), (arg s 3).toNat⟩ (below (f.gpr .esp) 96) :=
    (A.belowDom.sub_left sub96).symm
  have ctxE : ctxR (synth pArgs (arg s)) (pLenOf pArgs s) = ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ := by
    rw [cb]; rfl
  have domC : Region.Disjoint ⟨byteAddr (synth pArgs (arg s) 2), (arg s 3).toNat⟩
      (ctxR (synth pArgs (arg s)) (pLenOf pArgs s)) := by rw [ctxE]; exact A.ctxDom.symm
  have C : CtxW (wsBase pArgs s) (wsSize pArgs s) (pLenOf pArgs s) (synth pArgs (arg s)) f := by
    have cfit : (argumentPointer s 0).toNat = (arg s 0).toNat := by
      simp only [argumentPointer, BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega)
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · show ctxR _ _ ∈ _; rw [ctxE]; exact I.extra.2.1
    · show (argumentPointer s 0).toNat + _ ≤ _; rw [← cb, cfit]; exact A.ctxBound
    · show Region.Disjoint (ctxR _ _) _; rw [ctxE]; exact A.ctxScratch
    · show Region.Disjoint _ (ctxR _ _); rw [ctxE]; exact (A.belowCtx.sub_left subF)
    · show Region.Disjoint (ctxR _ _) _; rw [ctxE]; exact (A.belowCtx.sub_left sub96).symm
  have tws : Region.Disjoint ⟨byteAddr (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym), 17744⟩
      ⟨wsBase pArgs s, wsSize pArgs s⟩ := twr _ (by rw [A.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have tbytes : Spec.Rsa.bytesAt f.mem (byteAddr (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym)) 17744 =
      VG.Impl.Ffdh.VettedGroups.tableBytes := by
    rw [frame_bytes Ft (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact tws
      · exact t172.sub_right frameSub) (by decide)]
    have := VettedValidation.consts_bytes hc
    rwa [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length] at this
  have tfit' : (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym).toNat + 17744 ≤ 2 ^ 32 := by
    have e : (symAddr s VG.Impl.Ffdh.X86.VettedValidation.tableSym).toNat =
        (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym).toNat := by
      simp only [symAddr, BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := (s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym).isLt; omega)
    rw [e] at tfit; exact tfit
  have dd : KeyGen.domOf f.mem (synth pArgs (arg s)) (arg s 3).toNat = pcDom s := by
    show Spec.Rsa.bytesAt f.mem (argumentPointer s 2) _ = _
    exact frame_bytes Ft (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.domScratch
      · exact (A.belowDom.sub_left frameSub).symm) (by have := A.domBound; omega)
  exact ⟨G, hb40, domC, C, tfit', tbytes, tws, t172.sub_right sub96, dd⟩

/-- The body, from the frame's state. -/
theorem pc_frame_ok {s : State} (A : PreABI s) (hc : ConstsOk pcConsts stack s) (f : State)
    (I : In (PRd s) (wsBase pArgs s) (wsSize pArgs s) (pLenOf pArgs s) (synth pArgs (arg s)) f)
    (espf : f.gpr .esp = s.gpr .esp - BitVec.ofNat 32 argsFrame)
    (Ft : Frame [⟨wsBase pArgs s, wsSize pArgs s⟩, ⟨frameAt s, argsFrame⟩] s.mem f.mem) (hsy : f.syms = s.syms) :
    WP isa Impl.Ffdh.X86.Cached.Precompute.body f fun t =>
      (t.gpr .eax = 1 ∧ Spec.Rsa.wordsAt t.mem (argumentPointer s 0) (arg s 1).toNat =
        generationValues (pLenOf pArgs s) (pcDom s)) ∧
      Frame ([ctxR (synth pArgs (arg s)) (pLenOf pArgs s)] ++
        CrtRt.frameR (wsBase pArgs s) (f.gpr .esp) (fR (pLenOf pArgs s))) f.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] f t := by
  obtain ⟨G, hb40, domC, C, tfit', tbytes, tws, t40, dd⟩ := pc_frame_facts A hc f I espf Ft
  have dv : Spec.Ffdh.domainValid (pLenOf pArgs s) (KeyGen.domOf f.mem (synth pArgs (arg s)) (arg s 3).toNat) := by
    rw [dd]; exact A.valid
  refine WP.mono (pcBody_ok I G hb40 domC C (T := s.syms VG.Impl.Ffdh.X86.VettedValidation.tableSym)
    (by rw [hsy]) tfit' I.extra.2.2 tbytes tws t40 dv) fun t ⟨E, F, K, W⟩ =>
      ⟨⟨E, ?_⟩, by rw [List.singleton_append]; exact F, K⟩
  rw [dd] at W
  rw [A.ctxLen, pcWords_eq]
  exact W

theorem pc_operation_ok {s : State} (A : PreABI s) (hc : ConstsOk pcConsts stack s) :
    WP isa Impl.Ffdh.X86.Cached.Precompute.code s fun u =>
      (u.gpr .eax = 1 ∧ Spec.Rsa.wordsAt u.mem (argumentPointer s 0) (arg s 1).toNat =
        generationValues (pLenOf pArgs s) (pcDom s)) ∧ abiPreserved s u := by
  have tr := VettedValidation.consts_read hc
  rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length] at tr
  have hx : PRd s s.rd (⟨frameAt s, argsFrame⟩ :: s.wr) := by
    refine ⟨⟨_, List.mem_append_left _ A.rdIn, Region.contains_self _ _⟩, ?_, ?_⟩
    · rw [A.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
    · obtain ⟨r, hr, hcn⟩ := tr
      refine ⟨r, ?_, hcn⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have cb := pcCtxBytes A
  have ctxE : ctxR (synth pArgs (arg s)) (pLenOf pArgs s) = ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ := by
    rw [cb]; rfl
  exact wrap_syms_ok (wrapABI' A) (NoSp.of_all pcFrameBody_all) hx (Out := [ctxR (synth pArgs (arg s)) (pLenOf pArgs s)])
    (fun r hr => by obtain rfl := List.mem_singleton.mp hr; rw [ctxE]; exact A.retCtx)
    (fun r hr => by obtain rfl := List.mem_singleton.mp hr; rw [ctxE]; exact A.ctxScratch.symm)
    (P := fun m e => e = 1 ∧ Spec.Rsa.wordsAt m (argumentPointer s 0) (arg s 1).toNat =
      generationValues (pLenOf pArgs s) (pcDom s))
    fun f I espf Ft hsy => pc_frame_ok A hc f I espf Ft hsy

theorem pc_correct (s : State) (h : pcContract.pre s) :
    ∃ trace t, Exec isa Impl.Ffdh.X86.Cached.Precompute.code s trace t ∧ abiPreserved s t ∧
      pcContract.post s t := by
  obtain ⟨A, hc⟩ := preABI_of h
  obtain ⟨trace, t, E, ⟨e1, W⟩, P⟩ := pc_operation_ok A hc
  refine ⟨trace, t, E, P, ?_⟩
  change (Spec.Ffdh.generationPrecomputeContract abi stack).post s t
  sig_post [Spec.Ffdh.generationPrecomputeContract, Spec.Ffdh.generationPrecomputeSig, abi,
    argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right, e1]
  refine ⟨rfl, ?_⟩
  have dl : (arg s 3).toNat = 2 * (arg s 4).toNat ∨ (arg s 3).toNat = 3 * (arg s 4).toNat := A.dLen
  have dlen : (arg s 4).toNat ≤ (pcDom s).length := by rw [VG.Proof.Bignum.bytesAt_length]; omega
  rw [VG.Proof.Ffdh.generationPrecompute_eq dlen (VG.Proof.Ffdh.domainValid_mod A.valid)]
  exact congrArg some W.symm

end VG.Proof.Ffdh.X86.Cached
