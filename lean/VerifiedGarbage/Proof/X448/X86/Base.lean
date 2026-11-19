module

public import VerifiedGarbage.Proof.X448.X86.Verified
public import VerifiedGarbage.Impl.X448.X86.Base
public import VerifiedGarbage.Proof.Ed448.CombRef
public import VerifiedGarbage.Proof.X448.X86.BaseLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ed448.X86.BaseCT
public import VerifiedGarbage.Proof.Ed448.X86.BaseMain
public import VerifiedGarbage.Proof.Ed448.X86.ScalarIO
public import VerifiedGarbage.Proof.X448.X86.Runs
import VerifiedGarbage.Proof.X448.X86.Main
import VerifiedGarbage.Proof.X448.X86.FinalSwap
import VerifiedGarbage.Proof.X448.X86.Output
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Inv
import VerifiedGarbage.Proof.X448.X86.Bits
import VerifiedGarbage.Proof.X448.X86.ByteMem
import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.X448.X86.Instr
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.X448.X86.Verified
meta import VerifiedGarbage.Impl.X448.X86.Base
meta import VerifiedGarbage.Proof.Ed448.CombRef
meta import VerifiedGarbage.Proof.X448.X86.BaseLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ed448.X86.BaseCT
meta import VerifiedGarbage.Proof.Ed448.X86.BaseMain
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarIO
meta import VerifiedGarbage.Proof.X448.X86.Runs
meta import VerifiedGarbage.Proof.X448.X86.Main
meta import VerifiedGarbage.Proof.X448.X86.FinalSwap
meta import VerifiedGarbage.Proof.X448.X86.Output
meta import VerifiedGarbage.Proof.X448.X86.Freeze
meta import VerifiedGarbage.Proof.X448.X86.Restore
meta import VerifiedGarbage.Proof.X448.X86.Inv
meta import VerifiedGarbage.Proof.X448.X86.Bits
meta import VerifiedGarbage.Proof.X448.X86.ByteMem
meta import VerifiedGarbage.Proof.X448.X86.Iter
meta import VerifiedGarbage.Proof.X448.X86.Counters
meta import VerifiedGarbage.Proof.X448.X86.Instr
meta import VerifiedGarbage.Proof.X448.Bytes
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# X448 of the base point on x86 (32-bit): `Verified`

`vg_x448_base` is Ed448's base-point multiplication on this target, the
four-column comb (`Proof/Ed448/X86/BaseMain.lean`'s `combLoop_ok`), on the
bits of the decoded scalar (X448's `bitsData_ok`, and `zeroTop_ok` for the
eight bits above them), then `Y² / X²` of the comb's point by the ladder's
inversion and output (`invert_ok`, `finishX_ok`): `x448Base_main`, and
`x448Base_ok` given that this is X448 of the base point
(`Proof.Ed448.BaseCombUOk`, proven with the group law in
`Proof/Ed448/CombFacts.lean`, which only the registration file imports).

Constant time is run by run, as Ed448's base-point multiplication's
(`Proof/Ed448/X86/BaseCT.lean`, whose `combLoopG_tr` relates the comb's rows):
the entry by the taint analysis from the arguments (`τb`), the field
operations by the field functions' constant time, and the last block by the
taint analysis from what each run's correctness says of its own state.
-/

@[expose] public section

namespace VG.Proof.X448

open VG VG.X86 in
/-- `vg_x448_base(out, scalar, scratch)`, whose arguments are on the stack
(cdecl), with the 20 bytes of stack below its return address that its calls
of the field functions use. -/
def x448BaseX86 : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 56⟩
    let scalar : Region := ⟨(arg s 1).setWidth 64, 56⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - 20#64, 20⟩
    s.rd = [scalar, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 56 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 56 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ stk.Disjoint out ∧
      stk.Disjoint scratch
  post s s' := Spec.X448.bytesAt s'.mem ((arg s 0).setWidth 64) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem ((arg s 1).setWidth 64) 56) Spec.X448.basePoint
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2

end VG.Proof.X448

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.Ed448 (BaseCombUOk comb pt)
open VG.Proof.Ed448.X86 (Args CombInv combLoop_ok initSlots_ok initSlots_E initSlots_bounded initE
  stkR_below BitsG combLoopG_tr far_out Input)

/-! ## The precondition -/

/-- `vg_x448_base`'s precondition, by name. -/
structure BPre (s : State) : Prop where
  rd : s.rd = [scalarR s, ⟨argAddr s 0, 12⟩]
  wr : s.wr = [outR s, scR (arg s 2)]
  out_sc : (outR s).Disjoint (scR (arg s 2))
  scalar_sc : (scalarR s).Disjoint (scR (arg s 2))
  args_out : (⟨argAddr s 0, 12⟩ : Region).Disjoint (outR s)
  args_sc : (⟨argAddr s 0, 12⟩ : Region).Disjoint (scR (arg s 2))
  ret_out : (retR s).Disjoint (outR s)
  ret_sc : (retR s).Disjoint (scR (arg s 2))
  out_fit : (arg s 0).toNat + 56 ≤ 2 ^ 32
  scalar_fit : (arg s 1).toNat + 56 ≤ 2 ^ 32
  sc_fit : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  sp_room : 20 ≤ (s.gpr .esp).toNat
  stk_out : (stkR s).Disjoint (outR s)
  stk_sc : (stkR s).Disjoint (scR (arg s 2))

theorem BPre.of {s : State} (h : Proof.X448.x448BaseX86.pre s) : BPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem BPre.stk_args {s : State} (h : BPre s) : (stkR s).Disjoint ⟨argAddr s 0, 12⟩ := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> simp only [argAddr] <;> bv_omega

theorem BPre.stk_ret {s : State} (h : BPre s) : (stkR s).Disjoint (retR s) := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> bv_omega

theorem BPre.args {s : State} (h : BPre s) : Args s 3 2 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega_using [this], by decide, by rw [h.wr]; simp, h.sc_fit,
    h.args_sc, h.ret_sc⟩

/-- The arguments lie apart from what the code writes. -/
theorem BPre.args_wr {s : State} (h : BPre s) :
    ∀ r ∈ s.wr ++ [below (s.gpr .esp) 20], (⟨argAddr s 0, 4 * 3⟩ : Region).Disjoint r := by
  rw [h.wr, ← stkR_below h.sp_room]
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact h.args_out
  · exact h.args_sc
  · exact h.stk_args.symm

section
variable (σ : State)
/-- The working space and the scalar, from the entry state `σ`. -/
abbrev bsX : Addr := (arg σ 2).setWidth 64
abbrev kX : Nat := Spec.X448.decodeScalar448 (Spec.X448.bytesAt σ.mem ((arg σ 1).setWidth 64) 56)
end

theorem pow256_le {a n t : Nat} (ha : a ≤ n) (ht : 8 * n ≤ t) : 256 ^ a ≤ 2 ^ t := by
  refine Nat.le_trans (Nat.pow_le_pow_right (by decide) ha) ?_
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  exact Nat.pow_le_pow_right (by decide) ht

/-- The decoded scalar's bits from 448 up are zero. -/
theorem decodeScalar448_top (kb : List Byte) {t : Nat} (ht : 448 ≤ t) :
    (Spec.X448.decodeScalar448 kb >>> t) &&& 1 = 0 := by
  have hlt : Spec.X448.decodeScalar448 kb < 2 ^ t := by
    rw [Spec.X448.decodeScalar448, VG.Proof.X448.decodeLittleEndian_eq]
    exact Nat.lt_of_lt_of_le (VG.Proof.X25519.leNum_lt _) (pow256_le (List.length_take_le _ _) ht)
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]
  rfl

/-! ## The entry -/

/-- The bytes of bits 448–455 at `BITS` are zero. -/
theorem zeroTop_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block zeroTop) s fun t =>
      (∀ j < 8, t.mem (off base (BITS + 448 + j)) = 0) ∧ Outside base (BITS + 448) 8 s.mem t.mem ∧
        Keeps [.edx] s t := by
  have hB : BITS = 3072 := rfl
  unfold zeroTop
  refine wp_mov rfl fun u hu => ?_
  obtain ku : Keeps [.edx] s u := hu.rest (by decide)
  obtain hsu := hs.of_keeps ku (by decide)
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (BITS + 448 + j)) = 0) ∧ Outside base (BITS + 448) 8 u.mem t.mem ∧ Keeps [] u t
  obtain step : ∀ n t, n < 8 → inv n t →
      WP isa (.block [.store8 (sc (BITS + 448 + n)) .dl]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (storeByte_ok (hsu.of_keeps tk (by decide)) (d := BITS + 448 + n) (by omega_using [hB, hn]))
      fun v ⟨vm, vk⟩ => ⟨fun j hj => ?_, tm.trans ?_, tk.trans vk⟩
    · rw [vm, writeW8_apply]
      obtain eq : off base (BITS + 448 + j) = off base (BITS + 448 + n) ↔ j = n := by
        rw [off_eq_iff base (by omega_using [hB, hj, hn]) (by omega_using [hB, hn])]
        omega_using []
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), tk.1 _ (by decide), hu.gpr]; rfl
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega_using [hj, he])
    · intro x hx
      rw [vm]
      exact writeW8_outside _ _ _ (by omega_using [hB, hn]) (by omega_using [hn, hx])
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) u
    ⟨fun _ hj => absurd hj (Nat.not_lt_zero _), Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ =>
    ⟨tf, by rw [← hu.mem]; exact tm, ku.trans (tk.mono (by simp))⟩

/-- After the entry, from the entry state `σ`. -/
structure XMid (σ s : State) : Prop where
  pre : BPre σ
  fe : FE bsX σ s
  rd : s.rd = σ.rd
  saved : Saved (bsX σ) σ.gpr s.mem
  bits : BitsG bsX kX σ s
  start : ∀ s', s'.gpr .esi = BitVec.ofNat 32 114 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
    s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → CombInv (bsX σ) (kX σ) s s' 114

theorem entryB_stage {s₀ : State} (h : BPre s₀) : WP isa baseEntry s₀ (XMid s₀) := by
  have hA := h.args
  have hB : BITS = 3072 := rfl
  obtain hin : Input s₀ (bsX s₀) (arg s₀ 1) 56 :=
    Input.of_region h.scalar_fit (by rw [h.rd]; simp) h.scalar_sc
  unfold baseEntry
  refine WP.seq (WP.mono (Proof.Ed448.X86.save_ok hA) fun s₁ ⟨hs₁, sv₁, o₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (initSlots_ok hs₁) fun s₂ ⟨l₂, o₂, k₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.seq (WP.mono (zeroTop_ok hs₂) fun s₃ ⟨z₃, o₃, k₃⟩ => ?_)
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  obtain k03 : Keeps [.eax, .ebx, .ebp, .edi, .edx] s₀ s₃ :=
    (k₁.mono (by decide)).trans ((k₂.mono (by decide)).trans (k₃.mono (by decide)))
  obtain o03 : Outside (bsX s₀) 0 8192 s₀.mem s₃.mem :=
    (o₁.mono (by omega_using []) (by omega_using [])).trans ((o₂.mono (by omega_using []) (by omega_using [])).trans
      (o₃.mono (by omega_using []) (by omega_using [hB])))
  unfold bits
  refine WP.seq (hA.load (i := 1) (k03.1 _ (by decide)) k03.2.1 k03.2.2 o03 (by decide)
    fun s₄ u₄ => WP.block_nil ?_)
  obtain hs₄ := hs₃.of_upd u₄ (by decide)
  refine WP.mono (bitsData_ok (k := (arg s₀ 1).setWidth 64) hs₄ (by rw [u₄.gpr]) (by rw [u₄.gpr]; exact hin.fit)
    (by rw [u₄.rd, u₄.wr, k03.2.1, k03.2.2]; exact hin.read) hin.far) fun s₅ ⟨k₅, o₅, bits₅⟩ => ?_
  rw [u₄.mem, bytesAt_outside o03 hin.far] at bits₅
  obtain hs₅ := hs₄.of_keeps k₅ (by decide)
  obtain bits : BitsG bsX kX s₀ s₅ := fun t ht => by
    rcases Nat.lt_or_ge t 448 with h448 | h448
    · exact bits₅ t h448
    · rw [o₅ _ (Or.inr (by rw [ofs_off' _ (by omega_using [hB, ht])]; omega_using [h448])), u₄.mem,
        decodeScalar448_top _ h448, show BITS + t = BITS + 448 + (t - 448) by omega_using [h448]]
      exact z₃ (t - 448) (by omega_using [ht, h448])
  obtain slotOut : ∀ i : Index, ∀ j < 28,
      limbs s₅.mem (bsX s₀) (slot i.val) j = limbs s₂.mem (bsX s₀) (slot i.val) j := fun i j hj => by
    have hi := i.isLt
    rw [o₅.limbs (d := slot i.val) (Or.inl (by simp only [slot]; omega_using [hB, hi]))
        (by simp only [slot]; omega_using [hi]) hj, u₄.mem,
      o₃.limbs (d := slot i.val) (Or.inl (by simp only [slot]; omega_using [hB, hi]))
        (by simp only [slot]; omega_using [hi]) hj]
  obtain e₅ : ∀ i : Index, E s₅.mem (bsX s₀) i = Proof.X448.toFe (Impl.Ed448.X86.initVal i.val) := fun i => by
    rw [← initSlots_E l₂ i]
    exact congrArg Proof.X448.toFe (valN_congr (slotOut i))
  obtain b₅ : BoundedEnv s₅.mem (bsX s₀) := fun i j hj => by
    rw [slotOut i j hj]; exact initSlots_bounded l₂ i j hj
  obtain ⟨er, eq, ed⟩ := initE _ e₅
  obtain k05 : Keeps [.eax, .ebx, .ebp, .edi, .edx, .esi, .ecx] s₀ s₅ :=
    (k03.mono (by decide)).trans ((u₄.rest (by decide)).trans (k₅.mono (by decide)))
  obtain sp₅ : s₅.gpr .esp = s₀.gpr .esp := k05.1 _ (by decide)
  obtain hc₅ : CallCtx s₅ (bsX s₀) := ⟨by rw [sp₅]; exact h.sp_room, by
    simp only [callStk, sp₅]; rw [← stkR_below h.sp_room]; exact h.stk_sc.symm⟩
  obtain o35 : Outside (bsX s₀) 0 8192 s₃.mem s₅.mem := by
    rw [← u₄.mem]; exact o₅.mono (by omega_using []) (by omega_using [hB])
  obtain ws : (⟨bsX s₀, 8192⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) 20] := by
    rw [h.wr]; simp
  refine ⟨h, ⟨⟨hs₅, hc₅, b₅⟩, sp₅, k05.2.2, (Outside.frame (o03.trans o35)).mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ws⟩, k05.2.1,
    (((sv₁.outside o₂ (by decide)).outside o₃ (by decide)).outside (u₄.mem ▸ o₅) (by decide)), bits,
    fun s' h1 h2 h3 h4 h5 => ?_⟩
  have k' : Keeps (.esi :: workRegs) s₅ s' :=
    ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
  exact ⟨hs₅.of_keeps k' (by decide), hc₅.keep (h2 _ (by decide)), h3 ▸ b₅, k', h1,
    h3 ▸ WsOut2.refl _ _ _ _ _ _, by rw [h3, er]; rfl, by rw [h3]; exact congrArg Spec.Ed448.Point.Z eq,
    by rw [h3]; exact ed⟩

/-! ## The comb, the squares and the inversion -/

/-- After the comb, which started in `s₄`. -/
def XL (σ s : State) : Prop := ∃ s₄, XMid σ s₄ ∧ CombInv (bsX σ) (kX σ) s₄ s 0 ∧ FE bsX σ s

theorem loopB_stage {σ s : State} (h : XMid σ s) : WP isa Impl.Ed448.X86.combLoop s (XL σ) :=
  WP.mono (h.fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (Q := fun t => CombInv (bsX σ) (kX σ) s t 0) (WP.mono (combLoop_ok h.bits h.start) fun t ht =>
      ⟨⟨ht.scr, ht.ctx, ht.bounded⟩, ht.regs.1 _ (by decide), ht.regs.2.2, ht⟩))
    fun t ⟨fe, ht⟩ => ⟨s, h, ht, fe⟩

/-- `X²` and `Y²`. -/
def uFields : List FieldOp := [.mul 2 0 0, .mul 1 1 1]

theorem uFields_impl : uOps = uFields.map FieldOp.impl := by decide +kernel

/-- Before the last block: the field arithmetic's invariant, the saved registers, and the
quotient's factors in slots 1 and 21. -/
structure XI (σ s : State) : Prop where
  pre : BPre σ
  fe : FE bsX σ s
  rd : s.rd = σ.rd
  saved : Saved (bsX σ) σ.gpr s.mem
  val : E s.mem (bsX σ) 1 * E s.mem (bsX σ) 21 =
    (comb (kX σ) 114).Y * (comb (kX σ) 114).Y *
      Proof.X448.invert ((comb (kX σ) 114).X * (comb (kX σ) 114).X)

/-- After the squares. -/
structure XU (σ s : State) : Prop where
  pre : BPre σ
  fe : FE bsX σ s
  rd : s.rd = σ.rd
  saved : Saved (bsX σ) σ.gpr s.mem
  x : E s.mem (bsX σ) 2 = (comb (kX σ) 114).X * (comb (kX σ) 114).X
  y : E s.mem (bsX σ) 1 = (comb (kX σ) 114).Y * (comb (kX σ) 114).Y

theorem squaresB_stage {σ s : State} (h : XL σ s) :
    WP isa (ops (uFields.map FieldOp.impl)) s (XU σ) := by
  obtain ⟨s₄, m, L, fe⟩ := h
  refine WP.mono (ops_FE fe uFields) fun t ⟨fe', k, e⟩ => ?_
  obtain hX : E s.mem (bsX σ) 0 = (comb (kX σ) 114).X := congrArg Spec.Ed448.Point.X L.r
  obtain hY : E s.mem (bsX σ) 1 = (comb (kX σ) 114).Y := congrArg Spec.Ed448.Point.Y L.r
  exact ⟨m.pre, fe', k.regs.2.1.trans (L.regs.2.1.trans m.rd),
    (m.saved.wsout2 L.mem (by decide) (by decide)).wsout2 k.mem (by decide) (by decide),
    by rw [e, ← hX]; rfl, by rw [e, ← hY]; rfl⟩

theorem invertB_stage {σ s : State} (h : XU σ s) : WP isa Impl.X448.X86.invert s (XI σ) := by
  have fe := h.fe
  refine WP.mono (fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (Q := fun t => IKeep (bsX σ) s t ∧ E t.mem (bsX σ) = invEnv (E s.mem (bsX σ)))
    (WP.mono (invert_ok fe.fin.scr fe.fin.ctx fe.fin.bounded) fun t ⟨k, b, e⟩ =>
      ⟨⟨k.scr fe.fin.scr, k.ctx fe.fin.ctx, b⟩, k.regs.1 _ (by decide), k.regs.2.2, k, e⟩))
    fun t ⟨fe', k, e⟩ => ?_
  exact ⟨h.pre, fe', k.regs.2.1.trans h.rd, h.saved.wsout2 k.mem (by decide) (by decide),
    by rw [e, invEnv_x2, invEnv_eval, h.x, h.y]⟩

/-! ## The output -/

/-- X448's `finish`, for a function of `n` arguments whose first is the output's address. -/
theorem finishX_ok {s₀ s : State} {n sc : Nat} (hA : Args s₀ n sc) (h0 : 0 < n)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {base : Addr} (hm : Frame (s₀.wr ++ [below (s₀.gpr .esp) 20]) s₀.mem s.mem)
    (hawr : ∀ r ∈ s₀.wr ++ [below (s₀.gpr .esp) 20], (⟨argAddr s₀ 0, 4 * n⟩ : Region).Disjoint r)
    (hs : Scr s base) (hc : CallCtx s base) (hb : BoundedEnv s.mem base)
    (hout : outR s₀ ∈ s₀.wr) (hofit : (arg s₀ 0).toNat + 56 ≤ 2 ^ 32)
    (hd : (outR s₀).Disjoint ⟨base, 8192⟩)
    {g : Reg → BitVec 32} (sv : Saved base g s.mem) :
    WP isa finish s fun t =>
      Spec.X448.bytesAt t.mem ((arg s₀ 0).setWidth 64) 56 =
        Spec.X448.encodeUCoordinate (E s.mem base 1 * E s.mem base 21) ∧
      (∀ p ∈ savedSlots, t.gpr p.1 = g p.1) ∧ t.gpr .esp = s.gpr .esp ∧
      Frame (s₀.wr ++ [below (s₀.gpr .esp) 20]) s.mem t.mem := by
  obtain hfar : ∀ j < 8192, 56 ≤ ofs ((arg s₀ 0).setWidth 64) (off base j) := fun j hj => far_out hd hj
  obtain hw56 : ∀ j < 56, InRegions s₀.wr (off ((arg s₀ 0).setWidth 64) j) 1 := fun j hj =>
    ⟨_, hout, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  obtain ws : (⟨base, 8192⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) 20] :=
    List.mem_append_left _ (hwr ▸ hs.wr)
  obtain ws1 : ∀ {m m' : Mem}, Outside base 0 8192 m m' → Frame (s₀.wr ++ [below (s₀.gpr .esp) 20]) m m' :=
    fun h => (Outside.frame h).mono fun r hr => by rw [List.mem_singleton.mp hr]; exact ws
  unfold finish
  refine WP.seq (WP.mono (mulCall_ok hs hc (o := X2) (a := X2) (b := T7) (by decide) (by decide)
    (by decide) (hb 1) (hb 21)) fun u ⟨uk, ub, uv⟩ => ?_)
  have us := hs.of_keeps uk.keeps (by decide)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok us ub) fun v ⟨vb, vv, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  obtain stk : callStk s = below (s₀.gpr .esp) 20 := by simp only [callStk, hsp]
  obtain frames : Frame (s₀.wr ++ [below (s₀.gpr .esp) 20]) s.mem v.mem := by
    refine (uk.ext.mono fun r hr => ?_).trans (ws1 (vm.whole (by decide)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ws
    · rw [stk]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have ksv := uk.keeps.then vk
  have hvsp : v.gpr .esp = s₀.gpr .esp := (ksv.1 _ (by decide)).trans hsp
  refine hA.loadF hvsp (ksv.2.1.trans hr) (ksv.2.2.trans hwr) (hm.trans frames) hawr h0 fun v' hv => ?_
  have vs' := vs.of_upd hv (by decide)
  change WP isa (.block ((List.range 28).flatMap packLimb ++ restore)) v' _
  rw [WP.block_append_iff]
  refine WP.mono (output_ok vs' (hv.mem ▸ vb) (by rw [hv.gpr])
    (by rw [hv.gpr]; exact hofit)
    (by intro j hj; rw [hv.wr, ksv.2.2, hwr]; exact hw56 j hj) hfar) fun w ⟨wv, wm, wk⟩ => ?_
  have ws' := vs'.of_keeps wk (by decide)
  have svv := (sv.wsfield uk.mem (by decide)).field vm (by decide)
  have svw : Saved base g w.mem := svv.of_readW fun p hp => by
    have := savedSlots_bound p hp
    rw [← hv.mem]; exact output_word wm (by decide) (by omega_using [this]) hfar
  refine WP.mono (restore_ok ws' svw) fun t ⟨tr, tm, tk⟩ => ⟨?_, tr, ?_, ?_⟩
  · rw [tm, wv, hv.mem, vv, encodeUCoordinate_eq]
    refine congrArg (VG.Proof.X25519.leBytes 56) ?_
    exact congrArg Fin.val uv
  · rw [tk.1 _ (by decide), wk.1 _ (by decide), hv.other _ (by decide), ksv.1 _ (by decide)]
  · rw [tm]
    rw [hv.mem] at wm
    exact frames.trans ((Outside.frame wm).mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_append_left _ hout)

theorem finishB_stage {σ s : State} (h : XI σ s) :
    WP isa finish s fun t => abiPreserved σ t ∧
      Spec.X448.bytesAt t.mem ((arg σ 0).setWidth 64) 56 = Spec.X448.encodeUCoordinate
        ((comb (kX σ) 114).Y * (comb (kX σ) 114).Y *
          Proof.X448.invert ((comb (kX σ) 114).X * (comb (kX σ) 114).X)) := by
  have hp := h.pre
  have fe := h.fe
  refine WP.mono (finishX_ok hp.args (by decide) fe.sp h.rd fe.wr fe.frame hp.args_wr fe.fin.scr fe.fin.ctx
    fe.fin.bounded (by rw [hp.wr]; simp) hp.out_fit hp.out_sc h.saved) fun t ⟨bt, rt, spt, ft⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, by rw [bt, h.val]⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rt (.ebx, 0) (by decide)
    · exact rt (.esi, 4) (by decide)
    · exact rt (.edi, 8) (by decide)
    · exact rt (.ebp, 12) (by decide)
    · rw [spt, fe.sp]
  · have ret : (retR σ).Contains ((σ.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((σ.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
          (by decide)
    refine (fe.frame.trans ft).readW ret ?_ (by decide)
    rw [hp.wr, ← stkR_below hp.sp_room]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.ret_out
    · exact hp.ret_sc
    · exact hp.stk_ret.symm

/-! ## The whole function -/

theorem x448Base_main {s₀ : State} (h : BPre s₀) :
    WP isa x448Base s₀ fun t => abiPreserved s₀ t ∧
      Spec.X448.bytesAt t.mem ((arg s₀ 0).setWidth 64) 56 = Spec.X448.encodeUCoordinate
        ((comb (kX s₀) 114).Y * (comb (kX s₀) 114).Y *
          Proof.X448.invert ((comb (kX s₀) 114).X * (comb (kX s₀) 114).X)) := by
  unfold x448Base
  rw [uFields_impl]
  exact WP.seq (WP.mono (entryB_stage h) fun _ m => WP.seq (WP.mono (loopB_stage m) fun _ l =>
    WP.seq (WP.mono (squaresB_stage l) fun _ u => WP.seq (WP.mono (invertB_stage u) fun _ i => finishB_stage i))))

theorem x448Base_ok (hu : BaseCombUOk) (s : State) (hs : Proof.X448.x448BaseX86.pre s) :
    ∃ t s', Exec isa Impl.X448.X86.x448Base s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448BaseX86.post s s' := by
  obtain ⟨tr, t, he, h1, h2⟩ := x448Base_main (BPre.of hs)
  refine ⟨tr, t, he, h1, ?_⟩
  change Spec.X448.bytesAt t.mem _ 56 = _
  rw [h2, (hu _).2]

/-! ## Constant time -/

/-- Two entry states the constant-time statement relates. -/
def XP₀ (σ₁ σ₂ : State) : Prop :=
  Proof.X448.x448BaseX86.pre σ₁ ∧ Proof.X448.x448BaseX86.pre σ₂ ∧ Proof.X448.x448BaseX86.pub σ₁ σ₂

theorem XP₀.hp {σ₁ σ₂ : State} (h : XP₀ σ₁ σ₂) : bsX σ₁ = bsX σ₂ ∧ σ₁.gpr .esp = σ₂.gpr .esp :=
  ⟨by simp only [bsX, h.2.2.2.2.2], h.2.2.1⟩

/-- The taint analysis starts with the stack arguments public, and the words holding `out` and
`scratch` known to be the base addresses of the writable regions. -/
def τb : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [56, 8192], argLen := 16, argBases := [(4, 0), (12, 1)] }

theorem wfb {s : State} (hp : BPre s) : VG.X86.Taint.Wf τb s := by
  have hsc := hp.sc_fit; have ho := hp.out_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τb], by simpa [hp.wr] using hp.out_sc, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hsc, ho]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [hs]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [τb, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agreeb {s₁ s₂ : State} (h₁ : Proof.X448.x448BaseX86.pre s₁) (h₂ : Proof.X448.x448BaseX86.pre s₂)
    (hpub : Proof.X448.x448BaseX86.pub s₁ s₂) : VG.X86.Taint.Agree τb s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2⟩ := hpub
  have hp₁ := BPre.of h₁; have hp₂ := BPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wfb hp₁, wfb hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τb, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [outR, a0, a2]
  · simp only [τb] at hk
    rw [show VG.X86.Taint.depth τb.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.sp_fit h4 hk, VG.X86.Taint.argByte_eq hp₂.sp_fit h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 := by omega_using [hk]
    rcases this with h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2

theorem entryB_rel : RelCT isa (Runs XP₀ fun σ s => s = σ ∧ BPre σ) baseEntry (Runs XP₀ XMid) := by
  refine Runs.step (RelCT.taint (A := taint) τb ?_ (by taint_decide))
    fun σ s ⟨e, h⟩ => by subst e; exact entryB_stage h
  rintro s₁ s₂ ⟨σ₁, σ₂, hP, ⟨rfl, -⟩, ⟨rfl, -⟩⟩
  exact agreeb hP.1 hP.2.1 hP.2.2

theorem loopB_rel : RelCT isa (Runs XP₀ XMid) Impl.Ed448.X86.combLoop (Runs XP₀ XL) :=
  Runs.step ((combLoopG_tr (bs := bsX) (k := kX) fun _ _ h => h.hp).mono
      (fun _ _ ⟨σ₁, σ₂, hP, m₁, m₂⟩ => ⟨σ₁, σ₂, hP, ⟨m₁.fe, m₁.bits⟩, ⟨m₂.fe, m₂.bits⟩⟩) fun _ _ h => h)
    fun _ _ m => loopB_stage m

theorem squaresB_rel : RelCT isa (Runs XP₀ XL) (ops (uFields.map FieldOp.impl)) (Runs XP₀ XU) :=
  Runs.step (ops_tr (fun _ _ h => h.hp) (fun _ _ ⟨_, _, _, fe⟩ => fe.fs) uFields) fun _ _ h => squaresB_stage h

theorem invertB_rel : RelCT isa (Runs XP₀ XU) Impl.X448.X86.invert (Runs XP₀ XI) :=
  Runs.step (rf_tr (fun _ _ h => h.hp) (fun _ _ h => h.fe.fs) invert_rel) fun _ _ h => invertB_stage h

theorem finishB_tr : RelCT isa (Runs XP₀ XI) finish fun _ _ => True := by
  unfold finish
  refine RelCT.seq (Runs.step (G := FE bsX)
    (rf_tr (fun _ _ h => h.hp) (fun _ _ h => h.fe.fs) finishMul_rel) ?_) ?_
  · intro σ s h
    have fe := h.fe
    exact WP.mono (fe.wp (op_nosp (.mul 1 1 21)) (op_stack (.mul 1 1 21)) (Q := fun _ => True)
      (WP.mono (mulE fe.fin.scr fe.fin.ctx fe.fin.bounded 1 1 21) fun t ⟨k, b, _⟩ =>
        ⟨⟨k.scr fe.fin.scr, k.ctx fe.fin.ctx, b⟩, k.regs.1 _ (by decide), k.regs.2.2, trivial⟩))
      fun t ⟨fe', _⟩ => fe'
  · refine RelCT.taint (A := taint) (τa 16) ?_ (by taint_decide)
    rintro s₁ s₂ ⟨σ₁, σ₂, hP, f₁, f₂⟩
    have p₁ := BPre.of hP.1
    have p₂ := BPre.of hP.2.1
    have a := agreeb hP.1 hP.2.1 hP.2.2
    have wr : ∀ {σ : State}, BPre σ → ∀ r ∈ σ.wr, Region.Disjoint ⟨(σ.gpr .esp).setWidth 64, 16⟩ r := by
      intro σ p r hr
      have := p.sp_fit
      rw [p.wr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [this]) p.ret_out p.args_out
      · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [this]) p.ret_sc p.args_sc
    exact f₁.agreeA f₂ hP.hp.1 hP.hp.2 p₁.sp_fit p₂.sp_fit (wr p₁) (wr p₂) p₁.args_wr p₂.args_wr
      fun k h4 hk => by
        have := a.argMem k h4 hk
        simpa only [τb, VG.X86.Taint.depth, Nat.zero_add] using this

theorem x448Base_ct : ConstantTime isa Proof.X448.x448BaseX86.pre Proof.X448.x448BaseX86.pub
    Impl.X448.X86.x448Base := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    ((?_ : RelCT isa (Runs XP₀ fun σ s => s = σ ∧ BPre σ) x448Base fun _ _ => True).mono
      (fun s₁ s₂ h => ⟨s₁, s₂, h, ⟨rfl, BPre.of h.1⟩, ⟨rfl, BPre.of h.2.1⟩⟩) fun _ _ h => h)
  unfold x448Base
  rw [uFields_impl]
  exact entryB_rel.seq (loopB_rel.seq (squaresB_rel.seq (invertB_rel.seq finishB_tr)))

/-! ## `Verified` -/

/-- Memory holding the arguments `0x1000, 0x2000, 0x4000` at `0x8004`. -/
def satBaseMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x40 else 0

/-- A state satisfying the precondition. -/
def satBaseState : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satBaseMem
  rd := [⟨0x2000, 56⟩, ⟨0x8004, 12⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448Base_verified (hu : BaseCombUOk) :
    Verified X86.target Impl.X448.X86.x448Base (Spec.X448.x448BaseContract X86.abi 20) :=
  Verified.of_correct (x448Base_ok hu) x448Base_ct (by
    have a0 : arg satBaseState 0 = 0x1000 := by decide
    have a1 : arg satBaseState 1 = 0x2000 := by decide
    have a2 : arg satBaseState 2 = 0x4000 := by decide
    have e : argAddr satBaseState 0 = 0x8004 := by decide
    have esp : satBaseState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, Proof.X448.x448BaseX86, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, e, esp] using Proof.X448.X86.satBaseState)

end VG.Proof.X448.X86
