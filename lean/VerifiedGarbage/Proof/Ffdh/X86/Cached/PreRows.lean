module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Select
public import VerifiedGarbage.Proof.Ffdh.X86.KeyCut
import VerifiedGarbage.Proof.Bignum.X86.ArgumentFrame
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# FFDH's key-generation context on i686: its rows

The precomputation writes the context: `storeRow_ok` copies a wide slot to
a row of it, `loadRow_ok` a row back to a slot, each by `selectLoop` with an
all-ones mask.
-/

@[expose] public section

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

theorem CtxW.keep {t : State} {rs : List Reg} (C : CtxW base bytes len args s) (K : Keeps rs s t)
    (sp : .esp ∉ rs := by decide) : CtxW base bytes len args t :=
  ⟨C.ws.of_keeps K, C.apart, by rw [K.1 _ sp]; exact C.argsApart⟩

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
