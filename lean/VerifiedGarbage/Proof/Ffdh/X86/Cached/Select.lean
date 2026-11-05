module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Digit
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Rows
import VerifiedGarbage.Proof.Mont.X86.WindowSelect
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Num
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# FFDH key generation from the context on i686: the digit's entry

`select_ok`: slot 7 the context's entry of the digit in the window word, by
scanning all 32 entries under an equality mask, each copied by
`selectLoop_far_ok`; the context's rows, at `ctx + 24 + B j` (`rowAt_ok`),
are read only.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cached

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Impl.Ffdh.X86.Cached VG.Impl.Ffdh.X86.Cached.Generate
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- A number apart from the bytes that changed keeps its value. -/
theorem val32_far {rs : List Region} {m m' : Mem} (F : Frame rs m m') {P : Addr} {d N : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨off P d, 4 * N⟩ r) (hn : 4 * N < 2 ^ 64) :
    val32 m' P d N = val32 m P d N := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
  exact congrArg BitVec.toNat (F.read (Region.contains_self _ _) hd hn)

section
variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The context's address. -/
abbrev ctxAddr (args : Nat → BitVec 32) : Addr := byteAddr (args ctxArg)

/-- The context's bytes: three words, then 34 rows of `B` bytes. -/
abbrev ctxBytes (len : Nat) : Nat := 24 + bc len .wide * 34

/-- `r :=` the address of row `j` of the context, `ctx + 24 + B j`. -/
theorem rowAt_ok {is : List Instr} {Q : State → Prop} (h : In Ex base bytes len args s) {r : Reg} {j : Nat}
    (hj : j ≤ 34) (heax : s.gpr .eax = BitVec.ofNat 32 j)
    (k : ∀ u, Keeps [.eax, .edx, r] s u → u.mem = s.mem →
      PtrAt u (ctxAddr args) r (24 + bc len .wide * j) → WP isa (.block is) u Q) :
    WP isa (.block (rowAt r ++ is)) s Q := by
  have hb := bc_le h.upper' .wide
  unfold rowAt
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine widthC_ok h.width h.upper' fun s₁ K₁ m₁ e₁ => wp_mul fun s₂ U₂ => ?_
  have h₁ := h.regs K₁ m₁
  have h₂ := h₁.regs ⟨fun q hq => U₂.other q (by simp at hq; exact hq.1) (by simp at hq; exact hq.2), U₂.rd,
    U₂.wr⟩ U₂.mem (rs := [.eax, .edx])
  refine wp_addS (h₂.arg (i := ctxArg) (by decide)) fun s₃ U₃ _ => wp_addS rfl fun s₄ U₄ _ =>
    wp_mov fun u U => ?_
  refine k u ?_ (by rw [U.mem, U₄.mem, U₃.mem, U₂.mem, m₁]) ?_
  · refine ⟨fun q hq => ?_, by rw [U.rd, U₄.rd, U₃.rd, U₂.rd, K₁.2.1], by rw [U.wr, U₄.wr, U₃.wr, U₂.wr, K₁.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [U.other q hq.2.2, U₄.other q hq.1, U₃.other q hq.1, U₂.other q hq.1 hq.2.1, K₁.1 q (by simpa using hq.2.1)]
  · have ea : (s₁.gpr .eax).toNat = j := by
      rw [K₁.1 _ (by decide), heax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [PtrAt, U.gpr, U₄.gpr, U₃.gpr, U₂.eax, e₁, ea, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, ctxAddr, byteAddr, BitVec.toNat_setWidth]
    have a32 := (args ctxArg).isLt
    rw [Nat.mod_eq_of_lt (a := (args ctxArg).toNat) (by omega)]
    rw [Nat.mod_eq_of_lt (a := j * bc len .wide) (by
      have := Nat.mul_le_mul_right (bc len .wide) hj; omega)]
    rw [show BitVec.toNat (24 : BitVec 32) = 24 from rfl, Nat.mul_comm j]
    omega


/-- The context readable, apart from the working space. -/
structure CtxRd (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s : State) : Prop where
  span : Span s (ctxAddr args) 0 (ctxBytes len)
  apart : Region.Disjoint ⟨ctxAddr args, ctxBytes len⟩ ⟨base, bytes⟩

theorem CtxRd.keep {t : State} {rs : List Reg} (C : CtxRd base bytes len args s) (K : Keeps rs s t) :
    CtxRd base bytes len args t := ⟨C.span.of_keeps K, C.apart⟩

/-- The context's 32-bit address does not wrap. -/
theorem CtxRd.afit (C : CtxRd base bytes len args s) : (args ctxArg).toNat + ctxBytes len ≤ 2 ^ 32 := by
  have fit := C.span.fit
  have hv : (byteAddr (args ctxArg)).toNat = (args ctxArg).toNat := by
    simp only [byteAddr, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (args ctxArg).isLt; omega)
  simp only [ctxAddr] at fit
  omega

/-- A span of the context, within it. -/
theorem CtxRd.row (C : CtxRd base bytes len args s) {d n : Nat} (hd : d + n ≤ ctxBytes len) :
    Span s (ctxAddr args) d n := C.span.sub (Nat.zero_le _) (by omega)

/-- Entry `e` (at `ebp`) into slot 7 if it is the window word's; `ebp` past it. -/
theorem combSelectStep_ok (h : In Ex base bytes len args s) (C : CtxRd base bytes len args s) {e D : Nat} (he : e < 32)
    (hw : w32 s.mem base winOff = D) (hD : D < 32)
    (hebp : PtrAt s (ctxAddr args) .ebp (24 + bc len .wide * (2 + e))) :
    WP isa (selectStep e) s fun u =>
      In Ex base bytes len args u ∧ Outside base (lo len (.slot .wide 7)) (bc len .wide) s.mem u.mem ∧
      PtrAt u (ctxAddr args) .ebp (24 + bc len .wide * (2 + (e + 1))) ∧
      sv u.mem base len .wide 7 = (if D = e then val32 s.mem (ctxAddr args) (24 + bc len .wide * (2 + e))
        (cwc len .wide) else sv s.mem base len .wide 7) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  have f7 := h.slot_fit .wide (j := 7) (by decide)
  have bw := bc_eq_cwc len .wide
  have g := bc_ge h.lower' .wide
  have hb := bc_le h.upper' .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e7 : lo len (.slot .wide 7) = numBase + 7 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  have ce : 2 + e ≤ 33 := by omega
  have row := Nat.mul_le_mul_left (bc len .wide) (show 2 + e + 1 ≤ 34 by omega)
  rw [Nat.mul_add, Nat.mul_one] at row
  unfold Generate.selectStep
  simp only [List.append_assoc]
  refine WP.seq (WP.block_append (WP.mono (VG.Proof.Mont.X86.Dynamic.windowMask_ok h.scratch (j := e)
    (by omega) (by rw [← wo, hw]; exact hD) he) fun s₁ ⟨m₁, c₁, K₁⟩ => ?_))
  have h₁ := h.regs K₁ m₁
  refine ptrTo_ok (r := .ebx) (t := .edx) (x := .slot .wide 7) (by decide) (by decide) h₁.edi h₁.width h.upper'
    (by omega) fun s₂ K₂ m₂ p₂ => ?_
  have h₂ := h₁.regs K₂ m₂
  refine cntTo_ok (n := one .wide) (r := .edi) h₂.width h.upper' (by decide) fun s₃ K₃ m₃ e₃ => WP.block_nil ?_
  have K₁₃ : Keeps [.eax, .ebx, .ecx, .edx, .edi] s s₃ :=
    ((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))
  have m₁₃ : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  have ws₃ : Ws s₃ base bytes := h.ws.of_keeps K₁₃
  have ebp₃ : PtrAt s₃ (ctxAddr args) .ebp (24 + bc len .wide * (2 + e)) := by
    rw [PtrAt, K₁₃.1 _ (by decide)]; exact hebp
  have ebx₃ : PtrAt s₃ base .ebx (lo len (.slot .wide 7)) := by rw [PtrAt, K₃.1 _ (by decide)]; exact p₂
  have edi₃ : (s₃.gpr .edi).toNat = 4 * cwc len .wide := by
    rw [e₃, cb1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact bw
  have ecx₃ : s₃.gpr .ecx = cmask (decide (D = e)) := by
    rw [K₃.1 _ (by decide), K₂.1 _ (by decide), c₁, show w32 s.mem base 4 = D from hw]
    simp only [cmask, decide_eq_true_eq]
  have span : Span s₃ (ctxAddr args) (24 + bc len .wide * (2 + e)) (4 * cwc len .wide) :=
    (C.keep K₁₃).row (by simp only [ctxBytes]; omega)
  have dis : Region.Disjoint ⟨off (ctxAddr args) (24 + bc len .wide * (2 + e)), 4 * cwc len .wide⟩
      ⟨off base (lo len (.slot .wide 7)), 4 * cwc len .wide⟩ :=
    (C.apart.sub_left (Offset.sub_base _ (by simp only [ctxBytes]; omega))).sub_right
      (Offset.sub_base _ (by omega))
  refine WP.seq (WP.mono (selectLoop_far_ok ws₃ (decide (D = e)) (by omega) span (by omega) dis ebp₃ ebx₃ edi₃ ecx₃)
    fun t ⟨O, V, _, pe, Kt⟩ => ?_)
  have K₀ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s t := (K₁₃.mono (by decide)).trans (Kt.mono (by decide))
  have Oall : Outside base 0 bytes s.mem t.mem := by rw [← m₁₃]; exact O.mono (Nat.zero_le _) (by omega)
  refine wp_movS ((h.stack 16 (by decide)).keep K₀ (by decide) Oall).readSrc fun u U _ => WP.block_nil ?_
  have ed : u.gpr .edi = s.gpr .edi := by rw [U.gpr]; exact h.edi_eq
  have Ku : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp])
      ((K₀.trans (U.keeps.mono (by decide))).mono (by decide)) ed
  have Ou : Outside base (lo len (.slot .wide 7)) (bc len .wide) s.mem u.mem := by
    rw [U.mem, ← m₁₃, bw]; exact O
  refine ⟨h.keep Ku (by decide) (by decide) (by rw [U.mem]; exact Oall), Ou, ?_, ?_, Ku⟩
  · rw [PtrAt, U.other _ (by decide), pe, ← bw, show 2 + (e + 1) = (2 + e) + 1 by omega, Nat.mul_succ]
    congr 1; omega
  · simp only [sv]
    rw [U.mem, V, m₁₃]
    by_cases d : D = e <;> simp [d]

/-- Slot 7 the context's entry of the digit in the window word (below 32), by scanning all 32 entries. -/
theorem select_ok (h : In Ex base bytes len args s) (C : CtxRd base bytes len args s) {D : Nat}
    (hw : w32 s.mem base winOff = D) (hD : D < 32) :
    WP isa Generate.select s fun u =>
      In Ex base bytes len args u ∧ Outside base (lo len (.slot .wide 7)) (bc len .wide) s.mem u.mem ∧
      sv u.mem base len .wide 7 = val32 s.mem (ctxAddr args) (24 + bc len .wide * (2 + D)) (cwc len .wide) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have bl := h.bytes_lt
  have nw := h.scratch.nowrap
  have f7 := h.slot_fit .wide (j := 7) (by decide)
  have bw := bc_eq_cwc len .wide
  have hb := bc_le h.upper' .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e7 : lo len (.slot .wide 7) = numBase + 7 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have wo : winOff = 4 := rfl
  unfold Generate.select
  refine WP.seq (WP.mono (zero_ok h (x := .slot .wide 7) (one_ok .wide) (by rw [cb1]; omega))
    fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
  rw [cb1] at O₁
  rw [cw1] at V₁
  have h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega))
  refine WP.seq (wp_movS rfl fun s₂ U₂ _ => rowAt_ok (r := .ebp) (j := 2) (h₁.regs U₂.keeps U₂.mem) (by decide)
    U₂.gpr fun s₃ K₃ m₃ p₃ => WP.block_nil ?_)
  have K₁₃ : Keeps [.eax, .ecx, .edx, .ebp] s s₃ :=
    (K₁.trans (U₂.keeps.mono (by decide))).trans (K₃.mono (by decide))
  have m₁₃ : s₃.mem = s₁.mem := by rw [m₃, U₂.mem]
  have h₃ := h₁.regs ((U₂.keeps.mono (by decide)).trans (K₃.mono (by decide)) : Keeps [.eax, .edx, .ebp] s₁ s₃)
    m₁₃
  have C₀ : CtxRd base bytes len args s₃ := C.keep K₁₃
  -- The context did not change: only slot 7 did.
  have far : ∀ {m m' : Mem}, Outside base (lo len (.slot .wide 7)) (bc len .wide) m m' → ∀ j < 32,
      val32 m' (ctxAddr args) (24 + bc len .wide * (2 + j)) (cwc len .wide) =
        val32 m (ctxAddr args) (24 + bc len .wide * (2 + j)) (cwc len .wide) := fun {m m'} O j hj => by
    have row := Nat.mul_le_mul_left (bc len .wide) (show 2 + j + 1 ≤ 34 by omega)
    rw [Nat.mul_add, Nat.mul_one] at row
    refine val32_far (Outside.frame_span O (by omega)) (fun r hr => ?_) (by omega)
    obtain rfl := List.mem_singleton.mp hr
    exact (C.apart.sub_left (Offset.sub_base _ (by simp only [ctxBytes]; omega))).sub_right
      (Offset.sub_base _ (by omega))
  refine WP.mono (wp_seqs_range Generate.selectStep (fun e u => In Ex base bytes len args u ∧
      Outside base (lo len (.slot .wide 7)) (bc len .wide) s.mem u.mem ∧
      PtrAt u (ctxAddr args) .ebp (24 + bc len .wide * (2 + e)) ∧
      sv u.mem base len .wide 7 = (if D < e then val32 s.mem (ctxAddr args) (24 + bc len .wide * (2 + D))
        (cwc len .wide) else 0) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u) 32 (fun e he u ⟨Iu, Ou, pu, Vu, Ku⟩ => ?_)
    ⟨h₃, by rw [m₁₃]; exact O₁, p₃, by simp only [sv]; rw [m₁₃, V₁]; simp, K₁₃.mono (by decide)⟩)
    fun u ⟨Iu, Ou, _, Vu, Ku⟩ => ⟨Iu, Ou, by rw [Vu]; simp [hD], Ku⟩
  have wu : w32 u.mem base winOff = D := by rw [Ou.w32 (by omega) (by omega)]; exact hw
  refine WP.mono (combSelectStep_ok Iu (C.keep Ku) he wu hD pu) fun v ⟨Iv, Ov, pv, Vv, Kv⟩ =>
    ⟨Iv, Ou.trans Ov, pv, ?_, Ku.trans Kv⟩
  rw [Vv, Vu, far Ou e he]
  by_cases d : D = e
  · subst d; simp
  · by_cases l : D < e
    · simp [d, l, show D < e + 1 by omega]
    · simp [d, l, show ¬ D < e + 1 by omega]

end

end VG.Proof.Ffdh.X86.Cached
