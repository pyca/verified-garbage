module

public import VerifiedGarbage.Proof.Ffdh.X86.Cached.PreRows
public import VerifiedGarbage.Proof.Ffdh.X86.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Frame
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.MulOk
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Ffdh.X86.Ops
import VerifiedGarbage.Proof.Ffdh.X86.Cached.Digit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# FFDH's key-generation context on i686: the comb's table

The precomputation's table (`table_ok`): entry 0, Montgomery one, and entry
1, `g R mod p`; then for each tooth `d = 2^(k+1)` its entry, from the last
tooth's by `rows` squares, and the entries `d + j` for `0 < j < d`, entry
`j` times entry `d` (`FixedBaseComb.exponent_add_tooth`). Entry `e` is row
`2 + e` of the context, `g^(exponent e) R mod p`.
-/

@[expose] public section

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
