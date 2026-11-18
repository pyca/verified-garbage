module

import VerifiedGarbage.Proof.MillerRabin.Arm.Mont
import VerifiedGarbage.Proof.MillerRabin.Arm.Ops
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Base
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.WideMul
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
public import VerifiedGarbage.Proof.MillerRabin.Word32 -- shake: keep: re-export the shared arithmetic under the existing ARM names.
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.MillerRabin.Arm.Base
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.MillerRabin.Arm.ArithmeticCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2
public import VerifiedGarbage.Impl.MillerRabin.Arm.Round
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.MillerRabin.Arm.Round
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MillerRabin.Arm.Taint`, which only this module used -/

section

/-! # The Miller–Rabin round on ARMv7: the pieces the taint analysis checks

Each piece between the loads from the stack and the Montgomery products
computes its addresses and loop counts from `r0` (`ws`, for the context) or
from `r7`–`r9` (the key view's registers), which two runs agree on by
correctness; the load of a word of the exponent also from the count of
windows left in `r1`, which is public too.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm

/-- The key view's registers. -/
abbrev kRegs : List Reg := [.r7, .r8, .r9]

/-- A piece the taint analysis checks with `r7`–`r9` public. -/
abbrev Cert (c : Prog isa) : Prop := ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs kRegs) c hc).isSome = true

theorem ctx_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0]) (.block ctx) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cT0_taint : Cert (seqs (copyClr aT0 9)) := ⟨_, by taint_decide⟩
theorem cM1_taint : Cert (seqs (copyClr aM1 10)) := ⟨_, by taint_decide⟩
theorem clrX_taint : Cert (.block (Impl.Rsa.Arm.Recover.clrTop aX)) := ⟨_, by taint_decide⟩
theorem clrY_taint : Cert (.block (Impl.Rsa.Arm.Recover.clrTop aY)) := ⟨_, by taint_decide⟩
theorem cT1_taint : Cert (copy (aT0 + 1) aX) := ⟨_, by taint_decide⟩
theorem cYX_taint : Cert (copy aY aX) := ⟨_, by taint_decide⟩
theorem cY0_taint : Cert (copy aY aT0) := ⟨_, by taint_decide⟩

theorem tabCnt_taint : Cert (.block tabCnt) := ⟨_, by taint_decide⟩
theorem tabCopyLoad_taint : Cert (.block [.ldr .lr .r8 sK]) := ⟨_, by taint_decide⟩
theorem tabCopyStore_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.lr,.r7,.r8,.r9])
      tabCopyStore hc).isSome = true := ⟨_, by taint_decide⟩
theorem cnt_taint : Cert (.block cntNext) := ⟨_, by taint_decide⟩

theorem winCnt_taint : Cert (.block winCnt) := ⟨_, by taint_decide⟩
theorem sqFour_taint : Cert (.block sqFour) := ⟨_, by taint_decide⟩
theorem eq1_taint : Cert (eqS sE1 aY aT0 aX) := ⟨_, by taint_decide⟩
theorem eq2_taint : Cert (eqS sE2 aY aM1 aX) := ⟨_, by taint_decide⟩
theorem sqFlag_taint : Cert (.block sqFlag) := ⟨_, by taint_decide⟩
theorem scan_taint : Cert scan := ⟨_, by taint_decide⟩
theorem winEnd_taint : Cert (.block winEnd) := ⟨_, by taint_decide⟩
theorem wordK_taint : Cert (.block wordK) := ⟨_, by taint_decide⟩

/-- The load of the word of the exponent, with the count in `r1` public too. -/
theorem wordLd_taint :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r1, .r7, .r8, .r9]) (.block wordLd) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem wordEnd_taint : Cert (.block wordEnd) := ⟨_, by taint_decide⟩
theorem lowBits_taint : Cert (.block lowBits) := ⟨_, by taint_decide⟩
theorem ret_taint : Cert (.block [.ldr .r0 .r8 sF]) := ⟨_, by taint_decide⟩

end VG.Proof.MillerRabin.Arm

end

end

/-! ### `MillerRabin.Arm.Words`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.Arm.Pieces2`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.Arm.Pieces`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.Arm.Math`, which only this module used -/

section

/-! # The ARMv7 round uses the shared native-word Miller–Rabin arithmetic -/

@[expose] public section
namespace VG.Proof.MillerRabin.Arm

export VG.Proof.MillerRabin.Word32 (
  rinv mm R_rinv mm_eq mm_val mm_lt
  tp tp_val tp_lt msq msqs mwin
  mrun msq_rel msqs4_rel mwin_rel mrun_rel mrA_le
  final_eq shl_shr28 shl4_succ32 digit_word mask_lt mask_eq
  mask_zero flag_bits foldR foldR_eq
)

end VG.Proof.MillerRabin.Arm

end

end


/-! # The Miller–Rabin round on ARMv7: its steps as pieces

`St P E A L V LS`: a stage (`KS`) with the key view's registers (`Ws`), the
values `A σ` and `V σ` given by the state `σ` the body starts from. Each step
of the round as a piece (`VP`): correct from any such stage, and leaking the
same in two runs at it.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- A stage with the key view's registers. -/
abbrev St (P : MP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (V : State → Nat → Nat)
    (LS : List Nat) (σ s : State) : Prop :=
  E σ ∧ KS P σ (A σ) L (V σ) LS s ∧ Ws s P.B P.Z P.W nArr

/-- A piece the taint analysis checks with the key view's registers public. -/
theorem VP.kv {P : MP} {F G : State → State → Prop} {c : Prog isa} (cert : Cert c)
    (hws : ∀ σ s, F σ s → Ws s P.B P.Z P.W nArr) (wp : ∀ σ s, F σ s → WP isa c s (G σ)) : VP F c G :=
  VP.taint _ cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
    have w₁ := hws _ _ h₁; have w₂ := hws _ _ h₂
    simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · rw [w₁.r7, w₂.r7]
    · rw [w₁.r8, w₂.r8]
    · rw [w₁.r9, w₂.r9]) wp

section
variable {P : MP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

theorem St.mono {A' : State → Nat → Nat} {L' : List Nat} {V' : State → Nat → Nat} {LS' : List Nat} {σ s : State}
    (h : St P E A L V LS σ s) (hl : ∀ j ∈ L', j ∈ L ∧ A σ j = A' σ j) (hls : ∀ d ∈ LS', d ∈ LS ∧ V σ d = V' σ d) :
    St P E A' L' V' LS' σ s :=
  ⟨h.1, h.2.1.mono hl hls, h.2.2⟩

/-- `copy o a` and `clrTop o` of an array the round does not write. -/
theorem St.pcopyClr {o a : Nat} (cert : Cert (seqs (copyClr o a))) (ho : o ∈ wJs) (ha : a < nArr) (haw : a ∉ wJs)
    (hoa : o ≠ a) :
    VP (St P E A L V LS) (seqs (copyClr o a)) (St P E (fun σ => upd (A σ) o (numAt σ.mem (State.addr P.ws) P.w a)) (o :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hw⟩ =>
    WP.mono (h.copyClr_ok hw ho ha hoa) fun _ ⟨ht, hwt⟩ => ⟨e, by rwa [h.numAt_input ha haw] at ht, hwt⟩

theorem St.pcopy {o a : Nat} (cert : Cert (copy o a)) (ho : o ∈ wJs) (ha : a ∈ L) (hoa : o ≠ a) :
    VP (St P E A L V LS) (copy o a) (St P E (fun σ => upd (A σ) o (A σ a)) (o :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hw⟩ =>
    WP.mono (h.copy_ok hw ho (h.live_lt a ha) hoa) fun _ ⟨ht, hwt, _⟩ => ⟨e, by rwa [h.arrs a ha] at ht, hwt⟩

theorem St.peqS {d a b t : Nat} (cert : Cert (eqS d a b t)) (ha : a ∈ L) (hb : b ∈ L) (hd : d ∈ wDs)
    (htw : t ∈ wJs) (hT : t ∉ L) (hls : sT ∉ LS) (hdT : d ≠ sT) :
    VP (St P E A L V LS) (eqS d a b t)
      (St P E A L (fun σ => upd (V σ) d (if A σ a = A σ b then 1 else 0)) (d :: LS)) :=
  VP.kv cert (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hw⟩ =>
    WP.mono (h.eqS_ok hw ha hb hd htw hT hls hdT) fun _ ⟨ht, hwt, _⟩ => ⟨e, ht, hwt⟩

/-! ## Montgomery products -/

/-- The stage after the product: `[aY]`'s number of the working space. -/
structure AfterM (P : MP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (V : State → Nat → Nat)
    (LS : List Nat) (T : State → Nat) (σ s : State) : Prop where
  e : E σ
  ks : KS P σ (A σ) L (V σ) LS s
  ptr : s.gpr .r0 = P.ws
  val : numAt s.mem (State.addr P.ws) P.w aY = T σ

/-- `mulY b`: `[aY] := mm c w [aY] [b]`. -/
theorem St.pmulY {b : Nat} (hb : b = aY ∨ b = aX) (hYl : aY ∉ L) (h2 : 2 ∉ L) (h3 : 3 ∉ L) (hbL : b ∈ aY :: L)
    (hYv : ∀ σ, E σ → A σ aY < cOf P σ.mem) (hbv : ∀ σ, E σ → A σ b < cOf P σ.mem) (fios : Bool := false) :
    VP (St P E A (aY :: L) V LS) (seqs (mulY (fios := fios) b))
      (St P E (fun σ => upd (A σ) aY (mm (cOf P σ.mem) P.w (A σ aY) (A σ b))) (aY :: L) V LS) := by
  have opd : Operand aY ∧ Operand b := by
    refine ⟨by simp [Operand, aY, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp], ?_⟩
    rcases hb with rfl | rfl <;> simp [Operand, aY, aX, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  simp only [mulY, seqs]
  let G1 := fun σ s => St P E A (aY :: L) V LS σ s ∧ s.gpr .r0 = P.ws
  let G2 := AfterM P E A L V LS (fun σ => mm (cOf P σ.mem) P.w (A σ aY) (A σ b))
  let G3 := fun σ s => G2 σ s ∧ Ws s P.B P.Z P.W nArr
  refine VP.seq (G := G1) ?_ (VP.seq (G := G2) ?_ (VP.block_append (G := G3) ?_ ?_))
  -- Frame word 0 into `r0`.
  · show VP _ (.block ([(Reg.r0, 0)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
    · have pre := h.pre
      have spr : State.addr (s.sp + BitVec.ofNat 32 0) = State.addr P.sp := by rw [h.sp, pre.sp, BitVec.add_zero]
      refine wp_loadStack (by decide) spr ⟨P.rF, List.mem_append_right _ (by rw [h.wr, pre.wr]; simp), by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩ fun s1 u1 => WP.block_nil ?_
      refine ⟨⟨e, h.of_rest (u1.rest (ws := [.r0]) (by simp)) u1.mem,
        hw.of_upd u1 (by decide) (by decide) (by decide)⟩, ?_⟩
      rw [u1.gpr]; have := h.frameWord (o := 0) (by decide); simp only [off, BitVec.add_zero] at this
      rw [this, pre.saved]
  -- The product.
  · have rdy : ∀ σ s, G1 σ s → ArithmeticReady P.ws P.len P.w s ∧
        numAt s.mem (State.addr P.ws) P.w b < numAt s.mem (State.addr P.ws) P.w 0 := fun σ s ⟨⟨e, h, _⟩, r0⟩ => by
      have pre := h.pre
      have cR := pre.c_lt
      have hb' := h.arrs b hbL
      refine ⟨h.ready r0, ?_⟩
      rw [pre.numAt_eq (by rw [hb']; have := hbv σ e; omega_arith), hb',
        show numAt s.mem (State.addr P.ws) P.w 0 = cOf P s.mem from rfl, h.c_eq]
      exact hbv σ e
    refine VP.of_ct (fun σ₁ σ₂ => ?_) fun σ s hs => ?_
    · intro s₁ s₂ t₁ t₂ u₁ u₂ hp e₁ e₂
      have len := hp.1.1.2.1.pre.len
      have ct := Arithmetic.product_ct fios (base := P.ws) (len := P.len) (w := P.w) opd.1 opd.1 opd.2
        (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith)
      exact ct s₁ s₂ t₁ t₂ u₁ u₂ ⟨rdy _ _ hp.1, rdy _ _ hp.2, by
        rw [hp.1.1.2.1.sp, hp.1.1.2.1.pre.sp, hp.2.1.2.1.sp, hp.2.1.2.1.pre.sp]⟩ e₁ e₂
    · obtain ⟨ar, lt⟩ := rdy σ s hs
      obtain ⟨⟨e, h, _⟩, r0⟩ := hs
      have pre := h.pre
      have cR := pre.c_lt
      have hY := h.arrs aY (by simp)
      have hB := h.arrs b hbL
      have eY : numAt s.mem (State.addr P.ws) P.w aY = A σ aY := by
        rw [pre.numAt_eq (by rw [hY]; have := hYv σ e; omega_arith), hY]
      have eB : numAt s.mem (State.addr P.ws) P.w b = A σ b := by
        rw [pre.numAt_eq (by rw [hB]; have := hbv σ e; omega_arith), hB]
      have c0 : numAt s.mem (State.addr P.ws) P.w 0 = cOf P σ.mem := h.c_eq
      refine WP.mono (Arithmetic.product_ok fios s ar opd.1 opd.1 opd.2 (by decide) lt)
        fun t ⟨ar', _, lt', v, keeps, frame, rest⟩ => ?_
      have k := keep_of_mont pre keeps frame
      have hL : KS P σ (A σ) L (V σ) LS s := h.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩)
      refine ⟨e, hL.core k (by decide) (by simp) rest.sp rest.rd rest.wr (hL.arrs_keep k ?_ (by simp))
        (hL.sl_keep k (by simp) (by simp)) hL.live_lt hL.ls_ok, ?_, ?_⟩
      · intro j hj hj'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
        rcases hj' with rfl | rfl | rfl
        · exact h2 hj
        · exact h3 hj
        · exact hYl hj
      · exact ar'.ptr
      · rw [c0] at lt' v
        rw [eY, eB] at v
        exact mm_eq pre.codd lt' v
  -- The context.
  · refine VP.taint [.r0] ctx_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s h => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ptr, h₂.ptr]
    · rw [← List.append_nil ctx]
      exact h.ks.ctx_ok h.ptr fun t ht hwt r m => WP.block_nil
        ⟨⟨h.e, ht, by rw [r.gpr _ (by decide), h.ptr], by rw [m]; exact h.val⟩, hwt⟩
  -- The top words cleared.
  · refine VP.kv clrY_taint (fun _ _ h => h.2) fun σ s ⟨h, hw⟩ => ?_
    have pre := h.ks.pre
    rw [← List.append_nil (Impl.Rsa.Arm.Recover.clrTop aY)]
    refine h.ks.clrTop_ok hw (by decide) fun t ht hwt _ => WP.block_nil ⟨h.e, ?_, hwt⟩
    rw [← pre.numAt_val32, h.val] at ht
    refine ht.mono (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
    · exact hj
    · rcases List.mem_cons.mp hj with rfl | hj'
      · simp only [upd_self]
      · have : j ≠ aY := fun e => hYl (e ▸ hj')
        simp only [upd_ne _ _ this]


/-- `sqY`: `[aY] := mm c w [aY] [aY]`, by the dedicated square. -/
theorem St.psqY (hYl : aY ∉ L) (h2 : 2 ∉ L) (h3 : 3 ∉ L) (hYv : ∀ σ, E σ → A σ aY < cOf P σ.mem) (fios : Bool := false) :
    VP (St P E A (aY :: L) V LS) (seqs (sqY (fios := fios)))
      (St P E (fun σ => upd (A σ) aY (mm (cOf P σ.mem) P.w (A σ aY) (A σ aY))) (aY :: L) V LS) := by
  have opd : Operand aY := by simp [Operand, aY, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have hbL : aY ∈ aY :: L := List.mem_cons_self
  have hbv := hYv
  simp only [sqY, seqs]
  let G1 := fun σ s => St P E A (aY :: L) V LS σ s ∧ s.gpr .r0 = P.ws
  let G2 := AfterM P E A L V LS (fun σ => mm (cOf P σ.mem) P.w (A σ aY) (A σ aY))
  let G3 := fun σ s => G2 σ s ∧ Ws s P.B P.Z P.W nArr
  refine VP.seq (G := G1) ?_ (VP.seq (G := G2) ?_ (VP.block_append (G := G3) ?_ ?_))
  -- Frame word 0 into `r0`.
  · show VP _ (.block ([(Reg.r0, 0)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨e, h, hw⟩ => ?_
    · rw [h₁.2.1.sp, h₁.2.1.pre.sp, h₂.2.1.sp, h₂.2.1.pre.sp]
    · have pre := h.pre
      have spr : State.addr (s.sp + BitVec.ofNat 32 0) = State.addr P.sp := by rw [h.sp, pre.sp, BitVec.add_zero]
      refine wp_loadStack (by decide) spr ⟨P.rF, List.mem_append_right _ (by rw [h.wr, pre.wr]; simp), by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩ fun s1 u1 => WP.block_nil ?_
      refine ⟨⟨e, h.of_rest (u1.rest (ws := [.r0]) (by simp)) u1.mem,
        hw.of_upd u1 (by decide) (by decide) (by decide)⟩, ?_⟩
      rw [u1.gpr]; have := h.frameWord (o := 0) (by decide); simp only [off, BitVec.add_zero] at this
      rw [this, pre.saved]
  -- The product.
  · have rdy : ∀ σ s, G1 σ s → ArithmeticReady P.ws P.len P.w s ∧
        numAt s.mem (State.addr P.ws) P.w aY < numAt s.mem (State.addr P.ws) P.w 0 := fun σ s ⟨⟨e, h, _⟩, r0⟩ => by
      have pre := h.pre
      have cR := pre.c_lt
      have hb' := h.arrs aY hbL
      refine ⟨h.ready r0, ?_⟩
      rw [pre.numAt_eq (by rw [hb']; have := hbv σ e; omega_arith), hb',
        show numAt s.mem (State.addr P.ws) P.w 0 = cOf P s.mem from rfl, h.c_eq]
      exact hbv σ e
    refine VP.of_ct (fun σ₁ σ₂ => ?_) fun σ s hs => ?_
    · intro s₁ s₂ t₁ t₂ u₁ u₂ hp e₁ e₂
      have len := hp.1.1.2.1.pre.len
      have ct := Arithmetic.square_ct fios (base := P.ws) (len := P.len) (w := P.w) opd opd
        (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith)
      exact ct s₁ s₂ t₁ t₂ u₁ u₂ ⟨rdy _ _ hp.1, rdy _ _ hp.2, by
        rw [hp.1.1.2.1.sp, hp.1.1.2.1.pre.sp, hp.2.1.2.1.sp, hp.2.1.2.1.pre.sp]⟩ e₁ e₂
    · obtain ⟨ar, lt⟩ := rdy σ s hs
      obtain ⟨⟨e, h, _⟩, r0⟩ := hs
      have pre := h.pre
      have cR := pre.c_lt
      have hY := h.arrs aY (by simp)
      have hB := h.arrs aY hbL
      have eY : numAt s.mem (State.addr P.ws) P.w aY = A σ aY := by
        rw [pre.numAt_eq (by rw [hY]; have := hYv σ e; omega_arith), hY]
      have eB : numAt s.mem (State.addr P.ws) P.w aY = A σ aY := by
        rw [pre.numAt_eq (by rw [hB]; have := hbv σ e; omega_arith), hB]
      have c0 : numAt s.mem (State.addr P.ws) P.w 0 = cOf P σ.mem := h.c_eq
      refine WP.mono (Arithmetic.square_ok fios s ar opd opd (by decide) lt)
        fun t ⟨ar', _, lt', v, keeps, frame, rest⟩ => ?_
      have k := keep_of_mont pre keeps frame
      have hL : KS P σ (A σ) L (V σ) LS s := h.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩)
      refine ⟨e, hL.core k (by decide) (by simp) rest.sp rest.rd rest.wr (hL.arrs_keep k ?_ (by simp))
        (hL.sl_keep k (by simp) (by simp)) hL.live_lt hL.ls_ok, ?_, ?_⟩
      · intro j hj hj'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
        rcases hj' with rfl | rfl | rfl
        · exact h2 hj
        · exact h3 hj
        · exact hYl hj
      · exact ar'.ptr
      · rw [c0] at lt' v
        rw [eY] at v
        exact mm_eq pre.codd lt' v
  -- The context.
  · refine VP.taint [.r0] ctx_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s h => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ptr, h₂.ptr]
    · rw [← List.append_nil ctx]
      exact h.ks.ctx_ok h.ptr fun t ht hwt r m => WP.block_nil
        ⟨⟨h.e, ht, by rw [r.gpr _ (by decide), h.ptr], by rw [m]; exact h.val⟩, hwt⟩
  -- The top words cleared.
  · refine VP.kv clrY_taint (fun _ _ h => h.2) fun σ s ⟨h, hw⟩ => ?_
    have pre := h.ks.pre
    rw [← List.append_nil (Impl.Rsa.Arm.Recover.clrTop aY)]
    refine h.ks.clrTop_ok hw (by decide) fun t ht hwt _ => WP.block_nil ⟨h.e, ?_, hwt⟩
    rw [← pre.numAt_val32, h.val] at ht
    refine ht.mono (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
    · exact hj
    · rcases List.mem_cons.mp hj with rfl | hj'
      · simp only [upd_self]
      · have : j ≠ aY := fun e => hYl (e ▸ hj')
        simp only [upd_ne _ _ this]

end

end VG.Proof.MillerRabin.Arm

end

end

/-! # The Miller–Rabin round on ARMv7: the blocks on the header words as pieces

The counts (`St.ptabCnt`, `St.pcnt`, `St.pwinCnt`, `St.psqFour`), a
squaring's flag (`St.psqFlag`) and a window's end (`St.pwinEnd`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

theorem ofNat_toNat32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.ofNat 32 v).toNat = v := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_shr32 {v : Nat} (h : v < 2 ^ 32) (n : Nat) : BitVec.ofNat 32 v >>> n = BitVec.ofNat 32 (v / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, ofNat_toNat32 h, Nat.shiftRight_eq_div_pow,
    ofNat_toNat32 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

/-- The flag of a squaring on bits. -/
theorem sqflag_bits (f e m : Bool) :
    (BitVec.ofNat 32 f.toNat ||| (BitVec.ofNat 32 e.toNat &&& BitVec.ofNat 32 m.toNat)).toNat = (f || (m && e)).toNat := by
  cases f <;> cases e <;> cases m <;> decide

section
variable {P : MP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- `str t, [r8, #d]`, keeping the flags. -/
theorem KS.strz {σ s : State} {A : Nat → Nat} {V : Nat → Nat} {d : Nat} (h : KS P σ A L V LS s)
    (hw : Ws s P.B P.Z P.W nArr) (hd : d ∈ wDs) {r : Reg} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A L (upd V d (s.gpr r).toNat) (d :: LS) t → Ws t P.B P.Z P.W nArr → t.z = s.z →
      t.gpr = s.gpr → WP isa (.block rest) t Q) :
    WP isa (.block (.str r .r8 d :: rest)) s Q := by
  obtain hd' := wDs_hdr d hd
  have hz := hw.hdr_le
  refine wp_str_z (by simp only [hdr] at hd'; omega_arith) (slot_addr hw (by omega_arith)) (hw.write (by omega_arith)) fun t m z => ?_
  obtain kt : Keep P.B P.W [] [d] s.mem t.mem := by
    rw [m.mem]; exact keep_write _ _ (by simp) (by simp only [hdr] at hd'; omega_arith)
  exact k t (h.slot1 kt hd m.sp m.rd m.wr (by rw [m.mem, slot_write_self])) (hw.of_mupd m) z m.gpr

/-- The count of the table's entries. -/
theorem St.ptabCnt :
    VP (St P E A L V LS) (.block tabCnt) (St P E A L (fun σ => upd (V σ) sK 14) (sK :: LS)) := by
  refine VP.kv tabCnt_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  obtain h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  obtain hw1 := hw.of_upd u1 (by decide) (by decide) (by decide)
  refine h1.str hw1 (d := sK) (by decide) (r := .r1) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
  rw [u1.gpr] at ht; exact ht

/-- The count decremented. -/
theorem St.pcnt {n : Nat} (hk : sK ∈ LS) (vk : ∀ σ, E σ → V σ sK = n + 1) (hn : n + 1 < 2 ^ 32) :
    VP (St P E A L V LS) (.block cntNext)
      (fun σ s => St P E A L (fun σ => upd (V σ) sK n) (sK :: LS) σ s ∧ s.z = decide (n = 0)) := by
  refine VP.kv cnt_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  simp only [cntNext]
  refine h.ldr hw hk (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  rw [vk σ e] at u1
  refine wp_subs (op2_imm (by decide)) fun s2 u2 z2 => ?_
  obtain h2 := h1.of_rest (u2.rest (ws := [.r1]) (by simp)) u2.mem
  obtain hw2 := hw1.of_upd u2 (by decide) (by decide) (by decide)
  obtain e2 : s2.gpr .r1 = BitVec.ofNat 32 n := by
    rw [u2.gpr, u1.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), Nat.add_sub_cancel]
  refine KS.strz h2 hw2 (d := sK) (by decide) (r := .r1) fun t ht hwt zt _ => WP.block_nil ⟨⟨e, ?_, hwt⟩, ?_⟩
  · rwa [e2, ofNat_toNat32 (by omega_arith)] at ht
  · rw [zt, z2, show s1.gpr .r1 - 1 = s2.gpr .r1 from u2.gpr.symm, e2, ofNat_beq_zero (by omega_arith)]

/-- The flag 0 and the count of windows `16 w`. -/
theorem St.pwinCnt :
    VP (St P E A L V LS) (.block winCnt)
      (St P E A L (fun σ => upd (upd (V σ) sF 0) sK (16 * P.w)) (sK :: sF :: LS)) := by
  refine VP.kv winCnt_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  have w128 := h.pre.w128
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  obtain h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  obtain hw1 := hw.of_upd u1 (by decide) (by decide) (by decide)
  refine h1.str hw1 (d := sF) (by decide) (r := .r1) fun s2 h2 hw2 m2 => ?_
  rw [u1.gpr] at h2
  refine wp_mov (op2_lsl (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  obtain r34 : Rest [.r1] s2 s4 := (u3.rest (by simp)).trans (u4.rest (by simp))
  obtain h4 := h2.of_rest r34 (u4.mem.trans u3.mem)
  obtain hw4 := hw2.rest r34
  refine h4.str hw4 (d := sK) (by decide) (r := .r1) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
  obtain e4 : (s4.gpr .r1).toNat = 16 * P.w := by
    rw [u4.gpr, dpVal, u3.gpr, m2.gpr, u1.other _ (by decide), hw.r9,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl]
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      simp only [MP.W]; omega_arith), BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [MP.W]; omega_arith
  rw [e4, show (0 : BitVec 32).toNat = 0 from rfl] at ht
  exact ht

/-- Four squarings' count and threshold. -/
theorem St.psqFour :
    VP (St P E A L V LS) (.block sqFour)
      (St P E A L (fun σ => upd (upd (V σ) sR 0) sQ 4) (sQ :: sR :: LS)) := by
  refine VP.kv sqFour_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  obtain h1 := h.of_rest (u1.rest (ws := [.r1]) (by simp)) u1.mem
  obtain hw1 := hw.of_upd u1 (by decide) (by decide) (by decide)
  refine h1.str hw1 (d := sR) (by decide) (r := .r1) fun s2 h2 hw2 m2 => ?_
  rw [u1.gpr] at h2
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  obtain h3 := h2.of_rest (u3.rest (ws := [.r1]) (by simp)) u3.mem
  obtain hw3 := hw2.of_upd u3 (by decide) (by decide) (by decide)
  refine h3.str hw3 (d := sQ) (by decide) (r := .r1) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
  rw [u3.gpr] at ht; exact ht

/-- A squaring's flag: or'ed with `e₂` if the threshold is below the count
`k + 1`; the count decremented. -/
theorem St.psqFlag {k : Nat} {r : State → Nat} {fb eb : State → Bool} (hq : sQ ∈ LS) (hr : sR ∈ LS)
    (he : sE2 ∈ LS) (hf : sF ∈ LS) (vq : ∀ σ, E σ → V σ sQ = k + 1) (vr : ∀ σ, E σ → V σ sR = r σ)
    (rl : ∀ σ, E σ → r σ < 2 ^ 31) (hk : k + 1 < 2 ^ 31)
    (ve : ∀ σ, E σ → V σ sE2 = (eb σ).toNat) (vf : ∀ σ, E σ → V σ sF = (fb σ).toNat) :
    VP (St P E A L V LS) (.block sqFlag)
      (fun σ s => St P E A L (fun σ => upd (upd (V σ) sF (fb σ || (decide (r σ < k + 1) && eb σ)).toNat) sQ k)
        (sQ :: sF :: LS) σ s ∧ s.z = decide (k = 0)) := by
  refine VP.kv sqFlag_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  simp only [sqFlag]
  refine h.ldr hw hq (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  refine h1.ldr hw1 hr (r := .r2) (by decide) fun s2 h2 hw2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  obtain r34 : Rest [.r2] s2 s4 := (u3.rest (by simp)).trans (u4.rest (by simp))
  obtain h4 := h2.of_rest r34 (u4.mem.trans u3.mem)
  obtain hw4 := hw2.rest r34
  refine h4.ldr hw4 he (r := .r3) (by decide) fun s5 h5 hw5 u5 => ?_
  refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
  obtain h6 := h5.of_rest (u6.rest (ws := [.r3]) (by simp)) u6.mem
  obtain hw6 := hw5.of_upd u6 (by decide) (by decide) (by decide)
  refine h6.ldr hw6 hf (r := .r4) (by decide) fun s7 h7 hw7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun s8 u8 => ?_
  obtain h8 := h7.of_rest (u8.rest (ws := [.r4]) (by simp)) u8.mem
  obtain hw8 := hw7.of_upd u8 (by decide) (by decide) (by decide)
  obtain g1 : s8.gpr .r1 = BitVec.ofNat 32 (k + 1) := by
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide),
      u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr, vq σ e]
  obtain a1 : s2.gpr .r1 = BitVec.ofNat 32 (k + 1) := by rw [u2.other _ (by decide), u1.gpr, vq σ e]
  obtain a2 : s2.gpr .r2 = BitVec.ofNat 32 (r σ) := by rw [u2.gpr, vr σ e]
  obtain g4 : s4.gpr .r2 = BitVec.ofNat 32 (decide (r σ < k + 1)).toNat := by
    rw [u4.gpr, u3.gpr, dpVal, a1, a2]
    apply BitVec.eq_of_toNat_eq
    rw [mask_lt (rl σ e) hk, ofNat_toNat32 (by cases decide (r σ < k + 1) <;> decide)]
  obtain g8 : (s8.gpr .r4).toNat = (fb σ || (decide (r σ < k + 1) && eb σ)).toNat := by
    rw [u8.gpr, dpVal, u7.gpr, vf σ e, u7.other _ (by decide), u6.gpr, dpVal, u5.gpr, ve σ e,
      u5.other _ (by decide), g4]
    exact sqflag_bits _ _ _
  refine h8.str hw8 (d := sF) (by decide) (r := .r4) fun s9 h9 hw9 m9 => ?_
  rw [g8] at h9
  refine wp_subs (op2_imm (by decide)) fun s10 u10 z10 => ?_
  obtain h10 := h9.of_rest (u10.rest (ws := [.r1]) (by simp)) u10.mem
  obtain hw10 := hw9.of_upd u10 (by decide) (by decide) (by decide)
  obtain e10 : s10.gpr .r1 = BitVec.ofNat 32 k := by
    rw [u10.gpr, m9.gpr, g1, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), Nat.add_sub_cancel]
  refine KS.strz h10 hw10 (d := sQ) (by decide) (r := .r1) fun t ht hwt zt _ => WP.block_nil ⟨⟨e, ?_, hwt⟩, ?_⟩
  · rwa [e10, ofNat_toNat32 (by omega_arith)] at ht
  · rw [zt, z10, m9.gpr, g1, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), Nat.add_sub_cancel, ofNat_beq_zero (by omega_arith)]

/-- The digit at the top of the word `v`. -/
abbrev digitOf (v : Nat) : Nat := v / 2 ^ 28

/-- A window's end: the flag `y = 1 ∨ y = −1` if the digit is not 0, the
word shifted, the count of windows decremented, Z at the word's end. -/
theorem St.pwinEnd {K : Nat} {v : State → Nat} {e1 e2 fb : State → Bool} (hv : sV ∈ LS) (h1 : sE1 ∈ LS)
    (h2 : sE2 ∈ LS) (hf : sF ∈ LS) (hk : sK ∈ LS) (vv : ∀ σ, E σ → V σ sV = v σ) (vl : ∀ σ, E σ → v σ < 2 ^ 32)
    (v1 : ∀ σ, E σ → V σ sE1 = (e1 σ).toNat) (v2 : ∀ σ, E σ → V σ sE2 = (e2 σ).toNat)
    (vf : ∀ σ, E σ → V σ sF = (fb σ).toNat) (vk : ∀ σ, E σ → V σ sK = K + 1) (hK : K + 1 < 2 ^ 32) :
    VP (St P E A L V LS) (.block winEnd)
      (fun σ s => St P E A L (fun σ => upd (upd (upd (V σ) sF
          (if digitOf (v σ) = 0 then fb σ else (e1 σ || e2 σ)).toNat) sV (BitVec.ofNat 32 (v σ) <<< 4).toNat) sK K)
        (sK :: sV :: sF :: LS) σ s ∧ s.z = decide (K % 8 = 0)) := by
  refine VP.kv winEnd_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  obtain dl : digitOf (v σ) < 16 := by have := vl σ e; simp only [digitOf]; omega_arith
  simp only [winEnd]
  refine h.ldr hw hv (r := .r1) (by decide) fun s1 h1' hw1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  obtain r5 : Rest [.r2, .r3] s1 s5 :=
    (u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp))))
  obtain h5 := h1'.of_rest r5 (u5.mem.trans (u4.mem.trans (u3.mem.trans u2.mem)))
  obtain hw5 := hw1.rest r5
  refine h5.ldr hw5 h1 (r := .r4) (by decide) fun s6 h6 hw6 u6 => ?_
  refine h6.ldr hw6 h2 (r := .r5) (by decide) fun s7 h7 hw7 u7 => ?_
  refine wp_dp (op2_reg _ _) fun s8 u8 => ?_
  refine wp_dp (op2_reg _ _) fun s9 u9 => ?_
  obtain r9 : Rest [.r4] s7 s9 := (u8.rest (by simp)).trans (u9.rest (by simp))
  obtain h9 := h7.of_rest r9 (u9.mem.trans u8.mem)
  obtain hw9 := hw7.rest r9
  refine h9.ldr hw9 hf (r := .r5) (by decide) fun s10 h10 hw10 u10 => ?_
  refine wp_dp (op2_reg _ _) fun s11 u11 => ?_
  refine wp_dp (op2_reg _ _) fun s12 u12 => ?_
  obtain r12 : Rest [.r4, .r5] s10 s12 := (u11.rest (by simp)).trans (u12.rest (by simp))
  obtain h12 := h10.of_rest r12 (u12.mem.trans u11.mem)
  obtain hw12 := hw10.rest r12
  -- The values.
  obtain gz : s4.gpr .r2 = BitVec.ofNat 32 (decide (digitOf (v σ) = 0)).toNat := by
    rw [u4.gpr, u3.gpr, dpVal, u2.gpr, u1.gpr, vv σ e, ofNat_shr32 (vl σ e)]
    apply BitVec.eq_of_toNat_eq
    rw [mask_zero _ dl, ofNat_toNat32 (by cases decide (digitOf (v σ) = 0) <;> decide)]
  obtain x5 : s5.gpr .r3 = BitVec.ofNat 32 (decide (digitOf (v σ) = 0)).toNat ^^^ 1 := by
    rw [u5.gpr, dpVal, gz]
  obtain x7r3 : s7.gpr .r3 = s5.gpr .r3 := by rw [u7.other _ (by decide), u6.other _ (by decide)]
  obtain x7r4 : s7.gpr .r4 = BitVec.ofNat 32 (e1 σ).toNat := by rw [u7.other _ (by decide), u6.gpr, v1 σ e]
  obtain x7r5 : s7.gpr .r5 = BitVec.ofNat 32 (e2 σ).toNat := by rw [u7.gpr, v2 σ e]
  obtain x9 : s9.gpr .r4 = (BitVec.ofNat 32 (e1 σ).toNat ||| BitVec.ofNat 32 (e2 σ).toNat) &&&
      (BitVec.ofNat 32 (decide (digitOf (v σ) = 0)).toNat ^^^ 1) := by
    rw [u9.gpr, dpVal, u8.gpr, dpVal, x7r4, x7r5, u8.other _ (by decide), x7r3, x5]
  obtain x10r2 : s10.gpr .r2 = s4.gpr .r2 := by
    rw [u10.other _ (by decide), r9.gpr _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide)]
  obtain x11 : s11.gpr .r5 = BitVec.ofNat 32 (fb σ).toNat &&& BitVec.ofNat 32 (decide (digitOf (v σ) = 0)).toNat := by
    rw [u11.gpr, dpVal, u10.gpr, vf σ e, x10r2, gz]
  obtain gF : (s12.gpr .r4).toNat = (if digitOf (v σ) = 0 then fb σ else (e1 σ || e2 σ)).toNat := by
    rw [u12.gpr, dpVal, x11, u11.other _ (by decide), u10.other _ (by decide), x9]
    have := flag_bits (decide (digitOf (v σ) = 0)) (e1 σ) (e2 σ) (fb σ)
    simp only [decide_eq_true_eq] at this
    exact this
  refine h12.str hw12 (d := sF) (by decide) (r := .r4) fun s13 h13 hw13 m13 => ?_
  rw [gF] at h13
  refine wp_mov (op2_lsl (by decide)) fun s14 u14 => ?_
  obtain h14 := h13.of_rest (u14.rest (ws := [.r1]) (by simp)) u14.mem
  obtain hw14 := hw13.of_upd u14 (by decide) (by decide) (by decide)
  obtain g14 : s14.gpr .r1 = BitVec.ofNat 32 (v σ) <<< 4 := by
    rw [u14.gpr, m13.gpr, u12.other _ (by decide), u11.other _ (by decide), u10.other _ (by decide),
      u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      r5.gpr _ (by decide), u1.gpr, vv σ e]
  refine h14.str hw14 (d := sV) (by decide) (r := .r1) fun s15 h15 hw15 m15 => ?_
  rw [g14] at h15
  refine h15.ldr hw15 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk)) (r := .r1) (by decide)
    fun s16 h16 hw16 u16 => ?_
  obtain k16 : upd (upd (V σ) sF (if digitOf (v σ) = 0 then fb σ else (e1 σ || e2 σ)).toNat)
      sV (BitVec.ofNat 32 (v σ) <<< 4).toNat sK = K + 1 := by
    simp only [upd, show sK ≠ sV by decide, show sK ≠ sF by decide, ↓reduceIte]; exact vk σ e
  rw [k16] at u16
  refine wp_dp (op2_imm (by decide)) fun s17 u17 => ?_
  obtain h17 := h16.of_rest (u17.rest (ws := [.r1]) (by simp)) u17.mem
  obtain hw17 := hw16.of_upd u17 (by decide) (by decide) (by decide)
  obtain e17 : s17.gpr .r1 = BitVec.ofNat 32 K := by
    rw [u17.gpr, dpVal, u16.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), Nat.add_sub_cancel]
  refine h17.str hw17 (d := sK) (by decide) (r := .r1) fun s18 h18 hw18 m18 => ?_
  rw [e17, ofNat_toNat32 (by omega_arith)] at h18
  refine wp_dp (op2_imm (by decide)) fun s19 u19 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t u20 z20 => WP.block_nil ⟨⟨e, ?_, ?_⟩, ?_⟩
  · exact h18.of_rest ((u19.rest (ws := [.r1]) (by simp)).trans (u20.rest _)) (u20.mem.trans u19.mem)
  · exact (hw18.of_upd u19 (by decide) (by decide) (by decide)).rest (u20.rest [])
  · rw [z20, u19.gpr, dpVal, m18.gpr, e17]
    have : BitVec.ofNat 32 K &&& 7 = BitVec.ofNat 32 (K % 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, ofNat_toNat32 (by omega_arith), show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, ofNat_toNat32 (by omega_arith)]
    rw [this, show BitVec.ofNat 32 (K % 8) - 0 = BitVec.ofNat 32 (K % 8) from BitVec.sub_zero _,
      ofNat_beq_zero (by omega_arith)]

end

end VG.Proof.MillerRabin.Arm

end

end

/-! # The Miller–Rabin round on ARMv7: the words of the exponent

`ew P σ i`: the 32-bit word `i` of the exponent's array, which the round
does not write: below `2 w`, the words of `E` (`In.ew_val`); words `2 w`
and `2 w + 1`, the halves of `2^(t mod 64)` (`In.ew_low`). The load of the
word of the windows left (`St.pwordLd`), the count read (`St.pwordK`) and
tested (`St.pwordEnd`), and the threshold `4 − σ` of the last squarings
(`St.plowBits`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- Word `i` of the exponent's array, in `σ`. -/
abbrev ew (P : MP) (σ : State) (i : Nat) : Nat := w32 σ.mem (State.addr P.B) (arr P.W aE + 4 * i)

/-- `t`, the exponent of 2 in `c − 1`. -/
abbrev tOf (P : MP) (σ : State) : Nat := (Spec.Rsa.splitTwos (cOf P σ.mem - 1)).1

/-- The exponent. -/
abbrev eOf (P : MP) (σ : State) : Nat := Proof.MillerRabin.Round.exponent (cOf P σ.mem)

/-- Word `i` of a number of `k` words. -/
theorem val32_word' (m : Mem) (base : Addr) {d k i : Nat} (hi : i < k) :
    w32 m base (d + 4 * i) = val32 m base d k / 2 ^ (32 * i) % 2 ^ 32 := by
  obtain ⟨r, rfl⟩ : ∃ r, k = i + (r + 1) := ⟨k - i - 1, by omega_arith⟩
  rw [val32_append m base d i (r + 1)]
  simp only [val32]
  obtain lo := val32_lt m base d i
  obtain hw : w32 m base (d + 4 * i) < 2 ^ 32 := (m.readW _ 32).isLt
  obtain hp : 0 < 2 ^ (32 * i) := Nat.two_pow_pos _
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt lo, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hw]

theorem bv_add_sub (x y z : BitVec 32) : x + y - z = x + (y - z) := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

section
variable {P : MP} {σ : State}

theorem In.ew_val (h : In P σ) {i : Nat} (hi : i < 2 * P.w) :
    ew P σ i = eOf P σ / 2 ^ (32 * i) % 2 ^ 32 := by
  rw [ew, val32_word' _ _ hi, ← h.numAt_val32, h.exp]

theorem In.ew_low (h : In P σ) :
    ew P σ (2 * P.w) = 2 ^ (tOf P σ % 64) % 2 ^ 32 ∧ ew P σ (2 * P.w + 1) = 2 ^ (tOf P σ % 64) / 2 ^ 32 := by
  obtain e := congrArg BitVec.toNat h.low
  obtain k64 : tOf P σ % 64 < 64 := Nat.mod_lt _ (by decide)
  rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) k64)] at e
  obtain ew2 := word_eq_w32 σ.mem (State.addr P.ws) (arrAt P.w aE + 8 * P.w)
  simp only [VG.Proof.Mont.word, off] at ew2
  rw [e] at ew2
  obtain a1 : w32 σ.mem (State.addr P.ws) (arrAt P.w aE + 8 * P.w) = ew P σ (2 * P.w) := by
    simp only [ew, w32]; rw [h.off_eq, ← h.arr_eq aE, show kOff + arr P.W aE + 8 * P.w = kOff + (arr P.W aE + 4 * (2 * P.w)) by omega_arith]
  obtain a2 : w32 σ.mem (State.addr P.ws) (arrAt P.w aE + 8 * P.w + 4) = ew P σ (2 * P.w + 1) := by
    simp only [ew, w32]; rw [h.off_eq, ← h.arr_eq aE,
      show kOff + arr P.W aE + 8 * P.w + 4 = kOff + (arr P.W aE + 4 * (2 * P.w + 1)) by omega_arith]
  rw [a1, a2] at ew2
  obtain lt : ew P σ (2 * P.w) < 2 ^ 32 := (σ.mem.readW _ 32).isLt
  omega_arith

end

section
variable {P : MP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- The count of windows into `r1`. -/
theorem St.pwordK {K : Nat} (hk : sK ∈ LS) (vk : ∀ σ, E σ → V σ sK = K) :
    VP (St P E A L V LS) (.block wordK) (fun σ s => St P E A L V LS σ s ∧ s.gpr .r1 = BitVec.ofNat 32 K) := by
  refine VP.kv wordK_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  refine h.ldr hw hk (r := .r1) (by decide) fun t ht hwt u => WP.block_nil ⟨⟨e, ht, hwt⟩, ?_⟩
  rw [u.gpr, vk σ e]

/-- Word `m − 1` of the exponent into `sV`, for `r1 = 8 m`. -/
theorem St.pwordLd {m : Nat} (hE : ∀ σ, E σ → In P σ) (hm : 1 ≤ m) (hm2 : m ≤ 2 * P.w) :
    VP (fun σ s => St P E A L V LS σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (8 * m)) (.block wordLd)
      (St P E A L (fun σ => upd (V σ) sV (ew P σ (m - 1))) (sV :: LS)) := by
  refine VP.taint [.r1, .r7, .r8, .r9] wordLd_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, h, hw⟩, r1⟩ => ?_
  · have w₁ := h₁.1.2.2; have w₂ := h₂.1.2.2
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · rw [h₁.2, h₂.2]
    · rw [w₁.r7, w₂.r7]
    · rw [w₁.r8, w₂.r8]
    · rw [w₁.r9, w₂.r9]
  obtain pre := hE σ e
  have w128 := pre.w128
  simp only [wordLd]
  refine ptr_ok hw (r := .r0) (by decide) (j := aE) (by decide) fun s1 p1 rr1 m1 hw1 => ?_
  obtain q1 : s1.gpr .r1 = BitVec.ofNat 32 (8 * m) := by rw [rr1.gpr _ (by decide), r1]
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s4 u4 => ?_
  obtain q3 : s3.gpr .r1 = BitVec.ofNat 32 (m - 1) := by
    rw [u3.gpr, dpVal, u2.gpr, q1, ofNat_shr32 (by omega_arith), show 8 * m / 2 ^ 3 = m by omega_arith,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
  obtain fitE := hw.arr_fit (j := aE) (by decide)
  have nw := hw.nowrap
  have hS : S P.W = 4 * (P.W + 2) := rfl
  have hW : P.W = 2 * P.w + 2 := rfl
  obtain sh : BitVec.ofNat 32 (m - 1) <<< 2 = BitVec.ofNat 32 (4 * (m - 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ofNat_toNat32 (by omega_arith), ofNat_toNat32 (by omega_arith)]
    omega_arith
  obtain q4 : s4.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W aE + 4 * (m - 1)) := by
    rw [u4.gpr, dpVal, u3.other _ (by decide), u2.other _ (by decide), p1, q3, sh, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  obtain hw4 : Ws s4 P.B P.Z P.W nArr :=
    ((hw1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)).of_upd u4
      (by decide) (by decide) (by decide)
  obtain ea : State.addr (s4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr P.B) (arr P.W aE + 4 * (m - 1)) := by
    rw [q4, Offset.add_add, Nat.add_zero]
    exact hw.addr (by omega_arith)
  refine wp_ldr (by decide) ea (hw4.read (by omega_arith)) fun s5 u5 => ?_
  obtain r5 : Rest [.r0, .r1, .r2] s s5 := (rr1.mono (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))))
  obtain m5 : s5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, m1]
  obtain h5 := h.of_rest r5 m5
  obtain hw5 := hw4.of_upd u5 (by decide) (by decide) (by decide)
  refine h5.str hw5 (d := sV) (by decide) (r := .r2) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
  obtain v : (s5.gpr .r2).toNat = ew P σ (m - 1) := by
    rw [u5.gpr, u4.mem, u3.mem, u2.mem, m1]
    show w32 s.mem (State.addr P.B) (arr P.W aE + 4 * (m - 1)) = _
    exact h.keep.word (by omega_arith) (fun k hk e' => by subst e'; revert hk; decide)
      (fun d hd => wDs_hdr d hd) (h.fit (by decide))
  rwa [v] at ht

/-- Z when no window is left. -/
theorem St.pwordEnd {K : Nat} (hk : sK ∈ LS) (vk : ∀ σ, E σ → V σ sK = K) (hK : K < 2 ^ 32) :
    VP (St P E A L V LS) (.block wordEnd) (fun σ s => St P E A L V LS σ s ∧ s.z = decide (K = 0)) := by
  refine VP.kv wordEnd_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  simp only [wordEnd]
  refine h.ldr hw hk (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  refine wp_cmp (op2_imm (by decide)) fun t u2 z2 => WP.block_nil ⟨⟨e, h1.of_rest (u2.rest []) u2.mem,
    hw1.rest (u2.rest [])⟩, ?_⟩
  rw [z2, u1.gpr, vk σ e, show BitVec.ofNat 32 K - 0 = BitVec.ofNat 32 K from BitVec.sub_zero _,
    ofNat_beq_zero hK]

/-- The threshold `4 − σ` of the last squarings, and their count 3. -/
theorem St.plowBits (hE : ∀ σ, E σ → In P σ) :
    VP (St P E A L V LS) (.block lowBits)
      (St P E A L (fun σ => upd (upd (V σ) sR
        (foldR (BitVec.ofNat 32 (ew P σ (2 * P.w))) (BitVec.ofNat 32 (ew P σ (2 * P.w + 1)))).toNat) sQ 3)
        (sQ :: sR :: LS)) := by
  refine VP.kv lowBits_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  obtain pre := hE σ e
  have w128 := pre.w128
  have w4 := pre.w4
  simp only [lowBits]
  refine ptr_ok hw (r := .r0) (by decide) (j := aE) (by decide) fun s1 p1 rr1 m1 hw1 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  obtain fitE := hw.arr_fit (j := aE) (by decide)
  have nw := hw.nowrap
  have hS : S P.W = 4 * (P.W + 2) := rfl
  have hW : P.W = 2 * P.w + 2 := rfl
  obtain sh : BitVec.ofNat 32 P.W <<< 2 = BitVec.ofNat 32 (4 * P.W) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ofNat_toNat32 (by omega_arith), ofNat_toNat32 (by omega_arith)]
    omega_arith
  obtain q3 : s3.gpr .r0 = P.B + BitVec.ofNat 32 (arr P.W aE + 4 * (2 * P.w)) := by
    rw [u3.gpr, dpVal, u2.gpr, dpVal, p1, show s1.gpr .r9 = BitVec.ofNat 32 P.W by rw [rr1.gpr _ (by decide), hw.r9],
      sh, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat, bv_add_sub, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith),
      show arr P.W aE + 4 * P.W - 8 = arr P.W aE + 4 * (2 * P.w) by omega_arith]
  obtain hw3 : Ws s3 P.B P.Z P.W nArr :=
    (hw1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide) (by decide) (by decide)
  obtain rd : ∀ i, i ≤ 1 → InRegions (s3.rd ++ s3.wr) (off (State.addr P.B) (arr P.W aE + 4 * (2 * P.w + i))) 4 :=
    fun i hi => hw3.read (by omega_arith)
  obtain a0 : State.addr (s3.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr P.B) (arr P.W aE + 4 * (2 * P.w + 0)) := by
    rw [q3, Offset.add_add, Nat.add_zero, Nat.add_zero]
    exact hw.addr (by omega_arith)
  refine wp_ldr (by decide) a0 (rd 0 (by decide)) fun s4 u4 => ?_
  obtain a1 : State.addr (s4.gpr .r0 + BitVec.ofNat 32 4) = off (State.addr P.B) (arr P.W aE + 4 * (2 * P.w + 1)) := by
    rw [u4.other _ (by decide), q3, Offset.add_add,
      show arr P.W aE + 4 * (2 * P.w) + 4 = arr P.W aE + 4 * (2 * P.w + 1) by omega_arith]
    exact hw.addr (by omega_arith)
  refine wp_ldr (by decide) a1 (by rw [u4.rd, u4.wr]; exact rd 1 (by decide)) fun s5 u5 => ?_
  obtain mem : ∀ i, i ≤ 1 → (s3.mem.readW (off (State.addr P.B) (arr P.W aE + 4 * (2 * P.w + i))) 32) =
      BitVec.ofNat 32 (ew P σ (2 * P.w + i)) := fun i hi => by
    rw [u3.mem, u2.mem, m1]
    apply BitVec.eq_of_toNat_eq
    rw [ofNat_toNat32 (σ.mem.readW _ 32).isLt]
    exact h.keep.word (by omega_arith) (fun k hk e' => by subst e'; revert hk; decide)
      (fun d hd => wDs_hdr d hd) (h.fit (by decide))
  obtain g4 : s4.gpr .r1 = BitVec.ofNat 32 (ew P σ (2 * P.w)) := by rw [u4.gpr]; exact mem 0 (by decide)
  obtain g5 : s5.gpr .r2 = BitVec.ofNat 32 (ew P σ (2 * P.w + 1)) := by
    rw [u5.gpr, u4.mem]; exact mem 1 (by decide)
  generalize hlo : BitVec.ofNat 32 (ew P σ (2 * P.w)) = lo at g4
  generalize hhi : BitVec.ofNat 32 (ew P σ (2 * P.w + 1)) = hi at g5
  refine wp_dp (op2_reg _ _) fun s6 u6 => ?_
  refine wp_dp (op2_lsr (by decide)) fun s7 u7 => ?_
  refine wp_dp (op2_lsr (by decide)) fun s8 u8 => ?_
  refine wp_dp (op2_lsr (by decide)) fun s9 u9 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s10 u10 => ?_
  refine wp_dp (op2_imm (by decide)) fun s11 u11 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s12 u12 => ?_
  refine wp_dp (op2_imm (by decide)) fun s13 u13 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s14 u14 => ?_
  refine wp_dp (op2_imm (by decide)) fun s15 u15 => ?_
  refine wp_dp (op2_reg _ _) fun s16 u16 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s17 u17 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s18 u18 => ?_
  obtain y5 : s5.gpr .r1 = lo := by rw [u5.other _ (by decide), g4]
  obtain x6 : s6.gpr .r1 = lo ||| hi := by rw [u6.gpr, dpVal, y5, g5]
  obtain x11 : s11.gpr .r2 = s9.gpr .r1 >>> 1 &&& 1 := by rw [u11.gpr, dpVal, u10.gpr]
  obtain x13 : s13.gpr .r3 = s9.gpr .r1 >>> 2 &&& 1 := by
    rw [u13.gpr, dpVal, u12.gpr, u11.other _ (by decide), u10.other _ (by decide)]
  obtain x15 : s15.gpr .r4 = s9.gpr .r1 >>> 3 &&& 1 := by
    rw [u15.gpr, dpVal, u14.gpr, u13.other _ (by decide), u12.other _ (by decide), u11.other _ (by decide),
      u10.other _ (by decide)]
  obtain x15b : s15.gpr .r2 = s11.gpr .r2 := by
    rw [u15.other _ (by decide), u14.other _ (by decide), u13.other _ (by decide), u12.other _ (by decide)]
  obtain x15c : s15.gpr .r3 = s13.gpr .r3 := by rw [u15.other _ (by decide), u14.other _ (by decide)]
  obtain x16 : s16.gpr .r4 = s15.gpr .r4 + s15.gpr .r2 := by rw [u16.gpr, dpVal]
  obtain x17 : s17.gpr .r4 = s16.gpr .r4 + s16.gpr .r2 <<< 1 := by rw [u17.gpr, dpVal]
  obtain x18' : s18.gpr .r4 = s17.gpr .r4 + s17.gpr .r3 <<< 1 := by rw [u18.gpr, dpVal]
  obtain x16b : s16.gpr .r2 = s15.gpr .r2 := u16.other _ (by decide)
  obtain x17c : s17.gpr .r3 = s15.gpr .r3 := by rw [u17.other _ (by decide), u16.other _ (by decide)]
  obtain x9 : s9.gpr .r1 = (fun x3 : BitVec 32 => x3 ||| x3 >>> 4) ((fun x2 : BitVec 32 => x2 ||| x2 >>> 8)
      ((fun x1 : BitVec 32 => x1 ||| x1 >>> 16) (lo ||| hi))) := by
    rw [u9.gpr, dpVal, u8.gpr, dpVal, u7.gpr, dpVal, x6]
  obtain x18 : s18.gpr .r4 = foldR lo hi := by
    rw [x18', x17, x16, x17c, x16b, x15, x15b, x15c, x11, x13, x9]
    rfl
  obtain r18 : Rest [.r0, .r1, .r2, .r3, .r4] s s18 := (rr1.mono (by simp)).trans ((u2.rest (by simp)).trans
    ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans
    ((u7.rest (by simp)).trans ((u8.rest (by simp)).trans ((u9.rest (by simp)).trans ((u10.rest (by simp)).trans
    ((u11.rest (by simp)).trans ((u12.rest (by simp)).trans ((u13.rest (by simp)).trans ((u14.rest (by simp)).trans
    ((u15.rest (by simp)).trans ((u16.rest (by simp)).trans ((u17.rest (by simp)).trans (u18.rest (by simp))))))))))))))))))
  obtain m18 : s18.mem = s.mem := by
    rw [u18.mem, u17.mem, u16.mem, u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem,
      u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, m1]
  obtain h18 := h.of_rest r18 m18
  obtain hw18 := hw.rest r18
  refine h18.str hw18 (d := sR) (by decide) (r := .r4) fun s19 h19 hw19 _ => ?_
  rw [x18] at h19
  refine wp_mov (op2_imm (by decide)) fun s20 u20 => ?_
  obtain h20 := h19.of_rest (u20.rest (ws := [.r1]) (by simp)) u20.mem
  obtain hw20 := hw19.of_upd u20 (by decide) (by decide) (by decide)
  refine h20.str hw20 (d := sQ) (by decide) (r := .r1) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
  rw [u20.gpr] at ht
  subst hlo hhi
  exact ht

end

end VG.Proof.MillerRabin.Arm

end

end

/-! ### `MillerRabin.Arm.Win`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.Arm.Tab`, which only this module used -/

section

/-! ### `MillerRabin.Arm.Sq`, which only this module used -/

section

/-! # The Miller–Rabin round on ARMv7: a run of squarings

`SqS … q0 r st0 k`: a run of `q0` squarings from `st0` (`y` in `aY`, the
flag in `sF`), with the threshold `r` in `sR`, `k` of them left (in `sQ`):
`y` and the flag are `msqs … (q0 − k)` (`Proof/MillerRabin/Arm/Math.lean`).
One squaring goes from `k + 1` left to `k` (`sq_step`), and the loop from
`q0` to none (`sq_loop`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The witness, Montgomery one and minus one, from `σ`. -/
abbrev xOf (P : MP) (σ : State) : Nat := numAt σ.mem (State.addr P.ws) P.w 5
abbrev oOf (P : MP) (σ : State) : Nat := numAt σ.mem (State.addr P.ws) P.w 9
abbrev mOf (P : MP) (σ : State) : Nat := numAt σ.mem (State.addr P.ws) P.w 10

/-- A piece whose precondition is never met. -/
theorem VP.of_false {F G : State → State → Prop} {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  ⟨fun σ s hs => absurd hs (h σ s), fun _ _ _ _ _ _ ⟨σ, _, h₁, _⟩ => absurd h₁ (h σ _)⟩

/-- A piece under a fact its stage implies. -/
theorem VP.of_imp {F G : State → State → Prop} {c : Prog isa} {p : Prop} (hp : ∀ σ s, F σ s → p)
    (h : p → VP F c G) : VP F c G :=
  ⟨fun σ s hs => (h (hp σ s hs)).wp σ s hs, fun s₁ s₂ t₁ t₂ s₁' s₂' hs e₁ e₂ =>
    match hs with
    | ⟨σ₁, σ₂, h₁, h₂⟩ => (h (hp _ _ h₁)).ct s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, h₁, h₂⟩ e₁ e₂⟩

/-- `y` and the flag after `n` squarings of the run. -/
abbrev sqst (P : MP) (q0 : Nat) (r : State → Nat) (st0 : State → Nat × Bool) (σ : State) (n : Nat) : Nat × Bool :=
  msqs (cOf P σ.mem) P.w (mOf P σ) (r σ) q0 (st0 σ) n

/-- The run's stage with `k` squarings left. -/
def SqS (P : MP) (E : State → Prop) (A : State → Nat → Nat) (L : List Nat) (V : State → Nat → Nat)
    (LS : List Nat) (q0 : Nat) (r : State → Nat) (st0 : State → Nat × Bool) (k : Nat) (σ s : State) : Prop :=
  k ≤ q0 ∧ St P E (fun σ => upd (A σ) aY (sqst P q0 r st0 σ (q0 - k)).1) (aY :: L)
    (fun σ => upd (upd (V σ) sF (sqst P q0 r st0 σ (q0 - k)).2.toNat) sQ k) LS σ s

section
variable {P : MP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat} {q0 : Nat} {r : State → Nat} {st0 : State → Nat × Bool}

theorem sqst_lt (hE : ∀ σ, E σ → In P σ) (h0 : ∀ σ, E σ → (st0 σ).1 < cOf P σ.mem) :
    ∀ σ, E σ → ∀ n, (sqst P q0 r st0 σ n).1 < cOf P σ.mem := by
  intro σ e n
  have := (hE σ e).c3
  cases n with
  | zero => exact h0 σ e
  | succ n => exact mm_lt (by omega_using [this])

/-- One squaring. -/
theorem sq_step (hE : ∀ σ, E σ → In P σ) (hYL : aY ∉ L) (hM : aM1 ∈ L) (hX : aX ∉ L) (h2 : 2 ∉ L) (h3 : 3 ∉ L)
    (hF : sF ∈ LS) (hQ : sQ ∈ LS) (hR : sR ∈ LS) (hE2 : sE2 ∉ LS) (hT : sT ∉ LS)
    (vM : ∀ σ, E σ → A σ aM1 = mOf P σ) (vR : ∀ σ, E σ → V σ sR = r σ) (rl : ∀ σ, E σ → r σ < 2 ^ 31)
    (hq0 : q0 < 2 ^ 31) (h0 : ∀ σ, E σ → (st0 σ).1 < cOf P σ.mem) (k : Nat) (fios : Bool := false) :
    VP (SqS P E A L V LS q0 r st0 (k + 1)) (sqStep (fios := fios)) fun σ s =>
      isa.eval .ne s = some (decide (0 < k)) ∧ (k = 0 → SqS P E A L V LS q0 r st0 0 σ s) ∧
        (0 < k → SqS P E A L V LS q0 r st0 k σ s) := by
  by_cases hk : k + 1 ≤ q0
  swap
  · exact VP.of_false fun σ s h => hk h.1
  obtain lt := sqst_lt (q0 := q0) (r := r) hE h0
  let A1 := fun σ => upd (A σ) aY (sqst P q0 r st0 σ (q0 - (k + 1))).1
  let V1 := fun σ => upd (upd (V σ) sF (sqst P q0 r st0 σ (q0 - (k + 1))).2.toNat) sQ (k + 1)
  let A2 := fun σ => upd (A1 σ) aY (mm (cOf P σ.mem) P.w (A1 σ aY) (A1 σ aY))
  let V3 := fun σ => upd (V1 σ) sE2 (if A2 σ aY = A2 σ aM1 then 1 else 0)
  obtain a1Y : ∀ σ, A1 σ aY = (sqst P q0 r st0 σ (q0 - (k + 1))).1 := fun σ => upd_self _ _ _
  obtain a2Y : ∀ σ, A2 σ aY = (sqst P q0 r st0 σ (q0 - k)).1 := fun σ => by
    show mm _ _ (A1 σ aY) (A1 σ aY) = _
    rw [a1Y, show q0 - k = q0 - (k + 1) + 1 by omega_using [hk]]
    rfl
  obtain a2M : ∀ σ, E σ → A2 σ aM1 = mOf P σ := fun σ e => by
    show upd (upd (A σ) aY _) aY _ aM1 = _
    rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), vM σ e]
  refine VP.mono (F := St P E A1 (aY :: L) V1 LS) ?_ (fun σ s h => h.2) (fun _ _ h => h)
  simp only [sqStep, seqs]
  refine VP.seq (G := St P E A2 (aY :: L) V1 LS) ?_
    (VP.seq (G := St P E A2 (aY :: L) V3 (sE2 :: LS)) ?_ ?_)
  -- `y²`.
  · exact St.psqY (fios := fios) hYL h2 h3 (fun σ e => by rw [a1Y]; exact lt σ e _)
  -- `y = −1`.
  · exact St.peqS eq2_taint List.mem_cons_self (List.mem_cons_of_mem _ hM) (by decide) (by decide)
      (fun h => (List.mem_cons.mp h).elim (fun e => absurd e (by decide)) hX) hT (by decide)
  -- The flag and the count.
  · have vQ : ∀ σ, E σ → V3 σ sQ = k + 1 := fun σ _ => by
      show upd (upd (upd (V σ) sF _) sQ (k + 1)) sE2 _ sQ = _
      rw [upd_ne _ _ (by decide), upd_self]
    obtain vR3 : ∀ σ, E σ → V3 σ sR = r σ := fun σ e => by
      show upd (upd (upd (V σ) sF _) sQ (k + 1)) sE2 _ sR = _
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), vR σ e]
    obtain vE : ∀ σ, E σ → V3 σ sE2 =
        (decide (mm (cOf P σ.mem) P.w (sqst P q0 r st0 σ (q0 - (k + 1))).1
          (sqst P q0 r st0 σ (q0 - (k + 1))).1 = mOf P σ)).toNat := fun σ e => by
      show upd (V1 σ) sE2 (if A2 σ aY = A2 σ aM1 then 1 else 0) sE2 = _
      rw [upd_self, a2M σ e]
      show (if mm _ _ (A1 σ aY) (A1 σ aY) = _ then 1 else 0) = _
      rw [a1Y]
      split <;> simp_all
    obtain vF : ∀ σ, E σ → V3 σ sF = (sqst P q0 r st0 σ (q0 - (k + 1))).2.toNat := fun σ _ => by
      show upd (upd (upd (V σ) sF _) sQ (k + 1)) sE2 _ sF = _
      rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]
    refine (St.psqFlag (k := k) (List.mem_cons_of_mem _ hQ) (List.mem_cons_of_mem _ hR) List.mem_cons_self
      (List.mem_cons_of_mem _ hF) vQ vR3 rl (by omega_using [hq0, hk]) vE vF).mono (fun _ _ h => h) fun σ s ⟨h, z⟩ => ?_
    obtain stage : SqS P E A L V LS q0 r st0 k σ s := by
      refine ⟨by omega_using [hk], h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨?_, ?_⟩)⟩
      · rcases List.mem_cons.mp hi with rfl | hi'
        · rw [a2Y]; exact (upd_self _ _ _).symm
        · have : i ≠ aY := fun x => hYL (x ▸ hi')
          show upd (upd (A σ) aY _) aY _ i = upd (A σ) aY _ i
          rw [upd_ne _ _ this, upd_ne _ _ this, upd_ne _ _ this]
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))
      · have e : sqst P q0 r st0 σ (q0 - k) = msq (cOf P σ.mem) P.w (mOf P σ) (decide (r σ < k + 1))
            (sqst P q0 r st0 σ (q0 - (k + 1))) := by
          rw [show q0 - k = q0 - (k + 1) + 1 by omega_using [hk]]
          show msq _ _ _ (decide (r σ < q0 - (q0 - (k + 1)))) _ = _
          rw [show q0 - (q0 - (k + 1)) = k + 1 by omega_using [hk]]
        by_cases dQ : d = sQ
        · subst dQ; simp only [upd_self]
        · by_cases dF : d = sF
          · subst dF
            simp only [upd_ne _ _ dQ, upd_self, e, msq]
          · have dE : d ≠ sE2 := fun x => hE2 (x ▸ hd)
            simp only [V3, V1, upd_ne _ _ dQ, upd_ne _ _ dF, upd_ne _ _ dE]
    refine ⟨?_, fun h0 => h0 ▸ stage, fun _ => stage⟩
    show some (!s.z) = _
    rw [z]
    by_cases h0 : k = 0 <;> simp [h0] <;> omega_using [h0]

/-- The run. -/
theorem sq_loop (hE : ∀ σ, E σ → In P σ) (hYL : aY ∉ L) (hM : aM1 ∈ L) (hX : aX ∉ L) (h2 : 2 ∉ L) (h3 : 3 ∉ L)
    (hF : sF ∈ LS) (hQ : sQ ∈ LS) (hR : sR ∈ LS) (hE2 : sE2 ∉ LS) (hT : sT ∉ LS)
    (vM : ∀ σ, E σ → A σ aM1 = mOf P σ) (vR : ∀ σ, E σ → V σ sR = r σ) (rl : ∀ σ, E σ → r σ < 2 ^ 31)
    (hq0 : q0 < 2 ^ 31) (h0 : ∀ σ, E σ → (st0 σ).1 < cOf P σ.mem) (n : Nat) (fios : Bool := false) :
    VP (SqS P E A L V LS q0 r st0 (n + 1)) (sqLoop (fios := fios)) (SqS P E A L V LS q0 r st0 0) :=
  VP.loop (fun k => sq_step (fios := fios) hE hYL hM hX h2 h3 hF hQ hR hE2 hT vM vR rl hq0 h0 k) n

end

end VG.Proof.MillerRabin.Arm

end

end

/-! ### `MillerRabin.Arm.Scan`, which only this module used -/

section

/-! # The Miller–Rabin round on ARMv7: the scan and the table's shift

The scan (`St.pscan`): `T_d` into array 5 for the digit `d` at the top of
`sV`, through the masks of all 16 entries, the selection so far alternating
between arrays 8 and 5 (`hold`): before entry `j`, it is `T_d` if `d < j`,
else `T_0` (`selv`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The selection before entry `j`, for the digit `d`. -/
def selv (A : Nat → Nat) (d j : Nat) : Nat := if d < j then A (aT0 + d) else A aT0

theorem hold_mem (j : Nat) : hold j ∈ wJs := by unfold hold; split <;> decide
theorem hold_ne (j : Nat) : hold j ≠ hold (j + 1) := by unfold hold; split <;> split <;> first | decide | omega
theorem hold_two (j : Nat) : hold (j + 2) = hold j := by unfold hold; congr 1; simp only [Nat.add_mod_right]
theorem hold_lt (j : Nat) : hold j < aT0 := by unfold hold; split <;> decide
section
variable {P : MP} {σ s : State} {A : Nat → Nat} {L : List Nat} {V : Nat → Nat} {LS : List Nat}

/-- `maskJ j`: the mask of the digit at the top of `sV` being `j` into `sE1`. -/
theorem KS.mask_ok {j : Nat} (hj : j < 16) (h : KS P σ A L V LS s) (hw : Ws s P.B P.Z P.W nArr) (hv : sV ∈ LS)
    (vl : V sV < 2 ^ 32) :
    WP isa (.block (maskJ j)) s fun t =>
      KS P σ A L (upd V sE1 (decide (digitOf (V sV) = j)).toNat) (sE1 :: LS) t ∧ Ws t P.B P.Z P.W nArr := by
  simp only [maskJ]
  refine h.ldr hw hv (r := .r1) (by decide) fun s1 h1 hw1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  refine wp_dp (op2_imm (encodable_lt (by omega_using [hj]))) fun s3 u3 => ?_
  refine wp_dp (op2_imm (by decide)) fun s4 u4 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  obtain r5 : Rest [.r1] s1 s5 :=
    (u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp))))
  obtain h5 := h1.of_rest r5 (u5.mem.trans (u4.mem.trans (u3.mem.trans u2.mem)))
  obtain hw5 := hw1.rest r5
  refine h5.str hw5 (d := sE1) (by decide) (r := .r1) fun t ht hwt _ => WP.block_nil ⟨?_, hwt⟩
  obtain dl : digitOf (V sV) < 16 := by simp only [digitOf]; omega_using [vl]
  obtain g : (s5.gpr .r1).toNat = (decide (digitOf (V sV) = j)).toNat := by
    rw [u5.gpr, u4.gpr, dpVal, u3.gpr, dpVal, u2.gpr, u1.gpr, ofNat_shr32 vl]
    exact mask_eq _ dl _ hj
  rwa [g] at ht

/-- The entries `j, …, 15` of the scan, from the selection before entry `j`. -/
theorem scanFrom_ok {d : Nat} (hd : d < 16) (hT : ∀ k < 16, aT0 + k ∈ L) (hX : aX ∉ L) (hM : aM1 ∉ L)
    (hv : sV ∈ LS) (hE1 : sE1 ∉ LS) (dv : digitOf (V sV) = d) (vl : V sV < 2 ^ 32) :
    ∀ n j, j + n = 16 → 1 ≤ j → ∀ s, KS P σ (upd A (hold (j + 1)) (selv A d j)) (hold (j + 1) :: L) V LS s →
      Ws s P.B P.Z P.W nArr →
      WP isa (scanFrom j n) s fun t => KS P σ (upd A aX (A (aT0 + d))) (aX :: L) V LS t ∧ Ws t P.B P.Z P.W nArr
  | 0, j, hjn, _, s, h, hw => by
    have : j = 16 := by omega_using [hjn]
    subst this
    refine WP.block_nil ⟨?_, hw⟩
    obtain e : selv A d 16 = A (aT0 + d) := by simp only [selv, hd, ↓reduceIte]
    rw [e] at h
    exact h
  | n + 1, j, hjn, hj1, s, h, hw => by
    obtain hold_L : ∀ i, hold i ∉ L := fun i => by unfold hold; split; exacts [hX, hM]
    rw [scanFrom, WP.seq_iff]
    refine WP.mono (h.mask_ok (j := j) (by omega_using [hjn]) hw hv vl) fun s1 ⟨h1, hw1⟩ => ?_
    rw [WP.seq_iff]
    obtain hb : aT0 + j ∈ hold (j + 1) :: L := List.mem_cons_of_mem _ (hT j (by omega_using [hjn]))
    obtain ne1 : hold j ≠ aT0 + j := fun e => by have := hold_lt j; omega_using [e, this]
    refine WP.mono (h1.sel_ok hw1 (hold_mem j) List.mem_cons_self hb (hold_ne j) ne1 List.mem_cons_self
      (by rw [upd_self]; cases decide (digitOf (V sV) = j) <;> decide)) fun s2 ⟨h2, hw2, _⟩ => ?_
    refine scanFrom_ok hd hT hX hM hv hE1 dv vl n (j + 1) (by omega_using [hjn]) (by omega_using []) s2 ?_ hw2
    rw [hold_two]
    refine h2.mono (fun i hi => ⟨?_, ?_⟩) (fun e he => ⟨List.mem_cons_of_mem _ he, ?_⟩)
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi)
    · rcases List.mem_cons.mp hi with rfl | hi
      · have ne2 : aT0 + j ≠ hold (j + 1) := fun e => by have := hold_lt (j + 1); omega_using [e, this]
        simp only [upd_self]
        rw [upd_ne _ _ ne2, dv]
        unfold selv
        by_cases hdj : d = j
        · simp only [hdj, decide_true, Bool.toNat_true, Nat.one_ne_zero, ↓reduceIte, Nat.lt_succ_self]
        · simp only [hdj, decide_false, Bool.toNat_false, ↓reduceIte, show (d < j + 1) ↔ (d < j) by omega_using [hdj]]
      · have n1 : i ≠ hold j := fun e => hold_L j (e ▸ hi)
        obtain n2 : i ≠ hold (j + 1) := fun e => hold_L (j + 1) (e ▸ hi)
        rw [upd_ne _ _ n1, upd_ne _ _ n2, upd_ne _ _ n1]
    · have : e ≠ sE1 := fun x => hE1 (x ▸ he)
      rw [upd_ne _ _ this]

end

section
variable {P : MP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- The scan: `[aX] := T_d` for the digit `d` at the top of `sV`. -/
theorem St.pscan (hT : ∀ k < 16, aT0 + k ∈ L) (hX : aX ∉ L) (hM : aM1 ∉ L) (hv : sV ∈ LS) (hE1 : sE1 ∉ LS)
    (vl : ∀ σ, E σ → V σ sV < 2 ^ 32) :
    VP (St P E A L V LS) scan
      (St P E (fun σ => upd (A σ) aX (A σ (aT0 + digitOf (V σ sV)))) (aX :: L) V LS) := by
  refine VP.kv scan_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  obtain dl : digitOf (V σ sV) < 16 := by have := vl σ e; simp only [digitOf]; omega_using [this]
  rw [scan, WP.seq_iff]
  obtain t0 : aT0 ∈ L := hT 0 (by decide)
  refine WP.mono (h.copy_ok hw (by decide) (h.live_lt _ t0) (by decide)) fun s1 ⟨h1, hw1, _⟩ => ?_
  refine WP.mono (scanFrom_ok (A := A σ) dl hT hX hM hv hE1 rfl (vl σ e) 15 1 rfl (Nat.le_refl _) s1 ?_ hw1)
    fun t ⟨ht, hwt⟩ => ⟨e, ht, hwt⟩
  rw [h.arrs aT0 t0] at h1
  obtain e1 : selv (A σ) (digitOf (V σ sV)) 1 = A σ aT0 := by
    unfold selv; split
    · rw [show digitOf (V σ sV) = 0 by omega_arith]; rfl
    · rfl
  rw [show hold (1 + 1) = aM1 from rfl, e1]
  exact h1

end

end VG.Proof.MillerRabin.Arm

end

end


/-! # The Miller–Rabin round on ARMv7: the table

`tv P σ k` is power `k` in Montgomery form. After `i` steps, entries
0 through `i + 1` are complete, and each remaining entry retains its input
value. Each product is copied once to its final public slot.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- The table's entry `k`. -/
abbrev tv (P : MP) (σ : State) (k : Nat) : Nat := tp (cOf P σ.mem) P.w (xOf P σ) (oOf P σ) k

/-- Entry `k` of the table after `i` iterations. -/
def tabEnt (P : MP) (σ : State) (i k : Nat) : Nat :=
  if k = 0 then oOf P σ else if k = 1 then xOf P σ else
    if k ≤ i + 1 then tv P σ k else num σ.mem P.B P.W (aT0 + k)

/-- The arrays after `i` iterations. -/
def AT (P : MP) (i : Nat) (σ : State) (j : Nat) : Nat :=
  if j = aY then tv P σ (i + 1) else if j = aX then xOf P σ else tabEnt P σ i (j - aT0)

/-- `y`, `x` and the table. -/
abbrev LT : List Nat := [aY, aX, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

/-- The table's loop with `k` iterations left. -/
def TS (P : MP) (k : Nat) (σ s : State) : Prop :=
  k ≤ 14 ∧ St P (In P) (AT P (14 - k)) LT (fun _ => upd (fun _ => 0) sK k) [sK] σ s

theorem tv_lt {P : MP} {σ : State} (h : In P σ) (k : Nat) : tv P σ k < cOf P σ.mem := by
  have := h.c3
  exact tp_lt (by omega_using [this]) h.x5 (by show numAt σ.mem (State.addr P.ws) P.w 9 < _; rw [h.one]; exact Nat.mod_lt _ (by omega_using [this])) k

/-- A product and one final-slot copy advance the completed prefix. -/
theorem AT_step {P : MP} {σ : State} {i : Nat} (hi : i < 14) :
    ∀ j ∈ LT,
      upd (upd (AT P i σ) aY
        (mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX)))
        (aT0 + i + 2) (tv P σ (i + 2)) j = AT P (i + 1) σ j := by
  have ey : mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX) = tv P σ (i + 2) := rfl
  rw [ey]
  have e0 : aT0 = 11 := rfl
  have eY : aY = 6 := rfl
  have eX : aX = 5 := rfl
  intro j hj
  obtain hj' : j = aY ∨ j = aX ∨ (aT0 ≤ j ∧ j < aT0 + 16) := by
    simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hj
    omega_using [e0, hj]
  rcases hj' with rfl | rfl | hj
  · simp (disch := omega) only [upd, AT, ↓ite_eq_left, ↓ite_eq_right]
  · simp (disch := omega) only [upd, AT, ↓ite_eq_left, ↓ite_eq_right]
  · have hY : j ≠ aY := by omega_using [e0, eY, hj]
    obtain hX : j ≠ aX := by omega_using [e0, eX, hj]
    by_cases he : j = aT0 + i + 2
    · subst j
      obtain hsub : aT0 + i + 2 - aT0 = i + 2 := by omega_using []
      simp (disch := omega) only [upd, AT, tabEnt, hsub, ↓ite_eq_left, ↓ite_eq_right]
    · have hidx : j - aT0 ≠ i + 2 := by omega_using [he]
      obtain hbound : (j - aT0 ≤ i + 1) = (j - aT0 ≤ (i + 1) + 1) := by apply propext; omega_using [he]
      simp only [upd, he, hY, hX, AT, tabEnt, ↓reduceIte, hbound]


/-- The count addresses one final slot, then the existing copy loop preserves the stage. -/
private theorem tab_copy_store {P : MP} {σ s : State} {A : Nat → Nat} {L : List Nat}
    {V : Nat → Nat} {LS : List Nat} (h : KS P σ A L V LS s) (hw : Ws s P.B P.Z P.W nArr)
    (ha : aY ∈ L) (i : Nat) (hi : i<14) (count : s.gpr .lr=BitVec.ofNat 32 (14-i)) :
    WP isa tabCopyStore s fun t =>
      KS P σ (upd A (aT0+i+2) (num s.mem P.B P.W aY)) ((aT0+i+2)::L) V LS t ∧
      Ws t P.B P.Z P.W nArr := by
  rw [tabCopyStore,WP.seq_iff]
  simp only [tabCopyArgs,List.append_assoc,List.cons_append,List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  let s4 := s2.setReg .r0 (s2.gpr .r0*s2.gpr .r7+s2.gpr .r8)
  obtain u4 : Upd s2 s4 .r0 (s2.gpr .r0*s2.gpr .r7+s2.gpr .r8) := Upd.setReg _ _ _
  refine VG.Proof.X25519.Arm.WP.cons rfl ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  obtain index : s2.gpr .r0=BitVec.ofNat 32 (aT0+i+2) := by
    rw [u2.gpr,dpVal,u1.gpr,u1.other .lr (by decide),count]
    change BitVec.ofNat 32 27-BitVec.ofNat 32 (14-i)=_
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_using []) (by omega_using [])]
    congr 1
    simp only [aT0]
    omega_using [hi]
  obtain r5 : Rest [.r0] s s5 := (u1.rest (by simp)).trans ((u2.rest (by simp)).trans
    ((u4.rest (by simp)).trans (u5.rest (by simp))))
  obtain mem5 : s5.mem=s.mem := by rw [u5.mem,u4.mem,u2.mem,u1.mem]
  obtain hw5 : Ws s5 P.B P.Z P.W nArr := hw.rest r5 (by decide) (by decide) (by decide)
  obtain p0 : s5.gpr .r0=P.B+BitVec.ofNat 32 (arr P.W (aT0+i+2)) := by
    rw [u5.gpr,dpVal,u4.gpr,index,
      u2.other .r8 (by decide),u1.other .r8 (by decide),
      u2.other .r7 (by decide),u1.other .r7 (by decide),hw.r7,hw.r8]
    exact ptr_val _ _ _
  refine ptr_ok hw5 (r := .r10) (by decide) (j := aY) (by decide) fun s6 p10 r6 mem6 hw6 => ?_
  refine ptr_ok hw6 (r := .r12) (by decide) (j := aY) (by decide) fun s7 p12 r7 mem7 hw7 => ?_
  refine wp_mov (op2_reg _ _) fun s8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u9 => WP.block_nil ?_
  obtain hu : Ws u P.B P.Z P.W nArr := (hw7.of_upd u8 (by decide) (by decide) (by decide)).of_upd u9 (by decide) (by decide) (by decide)
  obtain mu : u.mem=s.mem := by rw [u9.mem,u8.mem,mem7,mem6,mem5]
  obtain restU : Rest opRegs s u := (r5.mono (by simp)).trans ((r6.mono (by simp)).trans
    ((r7.mono (by simp)).trans ((u8.rest (by simp)).trans (u9.rest (by simp)))))
  obtain ho : aT0+i+2<nArr := by simp only [aT0,nArr]; omega_using [hi]
  obtain ha' := h.live_lt _ ha
  obtain hoa : aT0+i+2≠aY := by simp only [aT0,aY]; omega_using []
  refine WP.mono (copyWords_ok u (hu.subCtx ho ha' ha' hoa hoa) hw.wpos
    (by rw [u9.other _ (by decide),u8.other _ (by decide),r7.gpr .r0 (by decide),r6.gpr .r0 (by decide),p0])
    (by rw [u9.other _ (by decide),u8.other _ (by decide),r7.gpr .r10 (by decide),p10])
    (by rw [u9.other _ (by decide),u8.other _ (by decide),p12])
    (by rw [u9.other _ (by decide),u8.gpr,hw7.r9])) ?_
  intro t inv
  have value := inv.value
  rw [mu] at value
  obtain keep : Keep P.B P.W [aT0+i+2] [] s.mem t.mem := Keep.of_arr (d := 0)
    (by simpa only [Nat.add_zero,mu] using inv.outside) (by simp only [S]; omega_using []) (by simp)
  obtain numeq : num t.mem P.B P.W (aT0+i+2)=num s.mem P.B P.W aY := by
    change val32 _ _ _ _=_
    rw [value]
    split <;> rfl
  obtain rest := restU.trans (inv.rest.mono (by simp))
  exact ⟨h.write1 keep (by simp [wJs,aT0]; omega_using [hi]) (by simp) rest.sp rest.rd rest.wr numeq (by simp),hu.rest inv.rest⟩

private theorem St.ptabCopy {P : MP} {E : State → Prop} {A : State → Nat → Nat}
    {L : List Nat} {V : State → Nat → Nat} {LS : List Nat} (i : Nat) (hi : i<14)
    (ha : aY ∈ L) (hk : sK ∈ LS) (vk : ∀ σ, E σ → V σ sK=14-i) :
    VP (St P E A L V LS) tabCopy
      (St P E (fun σ => upd (A σ) (aT0+i+2) (A σ aY)) ((aT0+i+2)::L) V LS) := by
  rw [tabCopy]
  refine VP.seq (G := fun σ s => St P E A L V LS σ s ∧ s.gpr .lr=BitVec.ofNat 32 (14-i)) ?_ ?_
  · refine VP.kv tabCopyLoad_taint (fun _ _ h => h.2.2) fun σ s ⟨e,h,hw⟩ => ?_
    refine h.ldr hw hk (r := .lr) (by decide) fun t ht hwt u => WP.block_nil ⟨⟨e,ht,hwt⟩,?_⟩
    rw [u.gpr,vk σ e]
  · refine VP.taint [.lr,.r7,.r8,.r9] tabCopyStore_taint ?_ ?_
    · intro σ₁ σ₂ s₁ s₂ h₁ h₂ r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl
      · rw [h₁.2,h₂.2]
      · rw [h₁.1.2.2.r7,h₂.1.2.2.r7]
      · rw [h₁.1.2.2.r8,h₂.1.2.2.r8]
      · rw [h₁.1.2.2.r9,h₂.1.2.2.r9]
    · intro σ s ⟨⟨e,h,hw⟩,count⟩
      exact WP.mono (tab_copy_store h hw ha i hi count)
        fun t ⟨ht,hwt⟩ => ⟨e,by rwa [h.arrs aY ha] at ht,hwt⟩

/-- One fixed, public entry index. -/
theorem tab_step {P : MP} (i : Nat) (hi : i < 14) (fios : Bool := false) :
    VP (TS P (14 - i)) (tabStep (fios := fios)) (fun σ s => TS P (13-i) σ s ∧ s.z=decide (13-i=0)) := by
  let V := fun (_ : State) => upd (fun _ => 0) sK (14 - i)
  refine VP.mono (F := St P (In P) (AT P i) LT V [sK]) ?_
    (fun σ s h => by simpa only [TS, Nat.sub_sub_self (by omega_using [hi] : i ≤ 14)] using h.2)
    (fun _ _ h => h)
  simp only [tabStep, seqs]
  refine VP.seq (St.pmulY (fios := fios) (P := P) (A := AT P i) (L := LT.tail) (.inr rfl)
    (by decide) (by decide) (by decide) (by decide) (fun σ e => tv_lt e _) (fun σ e => e.x5)) ?_
  refine VP.seq (St.ptabCopy i hi (by simp) (by simp) (fun _ _ => rfl)) ?_
  refine (St.pcnt (n := 13 - i) (by simp) (fun σ _ => by simp [V, upd]; omega_using [hi]) (by omega_using [])).mono
    (fun _ _ h => h) fun σ s ⟨h, z⟩ => ?_
  refine ⟨⟨by omega_using [], h.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩)
    (fun d hd => ⟨by simp only [List.mem_singleton] at hd; simp [hd], by
      simp only [List.mem_singleton] at hd; subst d; simp only [upd_self]⟩)⟩,z⟩
  change upd (upd (AT P i σ) aY _) (aT0 + i + 2) _ j = _
  rw [show (upd (AT P i σ) aY
      (mm (cOf P σ.mem) P.w (AT P i σ aY) (AT P i σ aX))) aY = tv P σ (i + 2) from rfl]
  rw [AT_step hi j hj]
  congr 1
  omega_using [hi]

/-- The compact loop advances the completed prefix. -/
theorem tab_loop {P : MP} (fios : Bool := false) :
    VP (TS P 14) (tabBuild (fios := fios)) (TS P 0) := by
  refine VP.loop (fun n => ?_) 13
  by_cases hn : n+1 ≤ 14
  · have hi : 14-(n+1)<14 := by omega_using []
    obtain eq1 : 14-(14-(n+1))=n+1 := by omega_using [hn]
    obtain eq2 : 13-(14-(n+1))=n := by omega_using [hn]
    refine (tab_step (P := P) (14-(n+1)) hi (fios := fios)).mono ?_ ?_
    · intro σ s h
      simpa only [eq1] using h
    · intro σ s h
      obtain ts : TS P n σ s := by simpa only [eq2] using h.1
      refine ⟨?_,fun h0 => h0 ▸ ts,fun _ => ts⟩
      show some (!s.z) = _
      rw [h.2,eq2]
      by_cases h0 : n=0 <;> simp [h0] <;> omega_using [h0]
  · exact VP.of_false fun _ _ h => hn h.1

end VG.Proof.MillerRabin.Arm

end

end


/-! # The Miller–Rabin round on ARMv7: the windows

`wst P σ j`: `y` and the flag after `j` of the `16 w` windows (`mrun`).
`WI P m r`: in the word `m − 1` of `E` (`m` words left), `r` of its windows
left, the word shifted past the others (`svOf`); `WO P m`: `m` words left.
A window goes from `WI P m (n + 1)` to `WI P m n`, or `WO P (m − 1)` at the
word's end (`win_step`); a word from `WO P (n + 1)` to `WO P n` (`word_step`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)

/-- `y` and the flag after `j` windows. -/
abbrev wst (P : MP) (σ : State) (j : Nat) : Nat × Bool :=
  mrun (cOf P σ.mem) P.w (mOf P σ) (tv P σ) (eOf P σ) (16 * P.w) j

/-- The arrays during the windows. -/
def AW (P : MP) (j : Nat) (σ : State) (i : Nat) : Nat :=
  if i = aY then (wst P σ j).1 else if i = aM1 then mOf P σ else tv P σ (i - aT0)

/-- `y`, `−1` and the table. -/
abbrev LW : List Nat := [aY, aM1, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

/-- The word `m − 1` of `E` shifted for `r` windows left. -/
abbrev svOf (P : MP) (σ : State) (m r : Nat) : Nat := (BitVec.ofNat 32 (ew P σ (m - 1)) <<< (4 * (8 - r))).toNat

/-- In the word `m − 1`, `r` of its windows left. -/
def WI (P : MP) (m r : Nat) (σ s : State) : Prop :=
  1 ≤ m ∧ m ≤ 2 * P.w ∧ r ≤ 8 ∧ St P (In P) (AW P (16 * P.w - (8 * (m - 1) + r))) LW
    (fun σ => upd (upd (upd (fun _ => 0) sF (wst P σ (16 * P.w - (8 * (m - 1) + r))).2.toNat) sK
      (8 * (m - 1) + r)) sV (svOf P σ m r)) [sV, sK, sF] σ s

/-- `m` words left. -/
def WO (P : MP) (m : Nat) (σ s : State) : Prop :=
  m ≤ 2 * P.w ∧ St P (In P) (AW P (16 * P.w - 8 * m)) LW
    (fun σ => upd (upd (fun _ => 0) sF (wst P σ (16 * P.w - 8 * m)).2.toNat) sK (8 * m)) [sK, sF] σ s

section
variable {P : MP} {σ : State}

theorem wst_lt (h : In P σ) (j : Nat) : (wst P σ j).1 < cOf P σ.mem := by
  have := h.c3
  cases j with
  | zero => exact tv_lt h 0
  | succ j => exact mm_lt (by omega_arith)

/-- The digit at the top of the shifted word is the window's. -/
theorem digit_sv (h : In P σ) {m r : Nat} (hm1 : 1 ≤ m) (hm : m ≤ 2 * P.w) (hr1 : 1 ≤ r) (hr : r ≤ 8) :
    digitOf (svOf P σ m r) = eOf P σ / 16 ^ (16 * P.w - 1 - (16 * P.w - (8 * (m - 1) + r))) % 16 := by
  obtain lt : ew P σ (m - 1) < 2 ^ 32 := (σ.mem.readW _ 32).isLt
  obtain e := shl_shr28 (BitVec.ofNat 32 (ew P σ (m - 1))) (t := 8 - r) (by omega_arith)
  rw [ofNat_toNat32 lt] at e
  obtain e2 : (BitVec.ofNat 32 (ew P σ (m - 1)) <<< (4 * (8 - r)) >>> 28).toNat = digitOf (svOf P σ m r) := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [← e2, e, h.ew_val (by omega_arith), show 28 - 4 * (8 - r) = 4 * (r - 1) by omega_arith, digit_word _ _ _ (by omega_arith),
    show 16 * P.w - 1 - (16 * P.w - (8 * (m - 1) + r)) = 8 * (m - 1) + (r - 1) by omega_arith]

theorem svOf_next {m n : Nat} (hn : n < 8) :
    (BitVec.ofNat 32 (svOf P σ m (n + 1)) <<< 4).toNat = svOf P σ m n := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, shl4_succ32, show 8 - (n + 1) + 1 = 8 - n by omega_arith]

theorem svOf_lt (m r : Nat) : svOf P σ m r < 2 ^ 32 := BitVec.isLt _

theorem svOf_eight (m : Nat) : svOf P σ m 8 = ew P σ (m - 1) := by
  rw [svOf, show 4 * (8 - 8) = 0 from rfl, BitVec.shiftLeft_zero, ofNat_toNat32 (σ.mem.readW _ 32).isLt]

end


/-! ## A window's stages, `n + 1` windows left in the word `m − 1` -/

section
variable (P : MP) (m n : Nat)

/-- The windows done. -/
abbrev jw : Nat := 16 * P.w - (8 * (m - 1) + (n + 1))

/-- The header words at the window's start. -/
def V0w (σ : State) : Nat → Nat :=
  upd (upd (upd (fun _ => 0) sF (wst P σ (jw P m n)).2.toNat) sK (8 * (m - 1) + (n + 1))) sV (svOf P σ m (n + 1))

/-- After the four squarings. -/
abbrev st4 (σ : State) : Nat × Bool := sqst P 4 (fun _ => 0) (fun σ => wst P σ (jw P m n)) σ 4
def A2w (σ : State) : Nat → Nat := upd (AW P (jw P m n) σ) aY (st4 P m n σ).1
def V2w (σ : State) : Nat → Nat := upd (upd (upd (V0w P m n σ) sR 0) sF (st4 P m n σ).2.toNat) sQ 0

/-- The digit, and after the scan, `−1` and the product. -/
abbrev dgw (σ : State) : Nat := digitOf (svOf P σ m (n + 1))
def A3w (σ : State) : Nat → Nat := upd (A2w P m n σ) aX (tv P σ (dgw P m n σ))
def A4w (σ : State) : Nat → Nat := upd (A3w P m n σ) aM1 (mOf P σ)
abbrev Y5w (σ : State) : Nat := mm (cOf P σ.mem) P.w (st4 P m n σ).1 (tv P σ (dgw P m n σ))
def A5w (σ : State) : Nat → Nat := upd (A4w P m n σ) aY (Y5w P m n σ)

/-- After the comparisons. -/
def V7w (σ : State) : Nat → Nat :=
  upd (upd (V2w P m n σ) sE1 (decide (Y5w P m n σ = tv P σ 0)).toNat) sE2 (decide (Y5w P m n σ = mOf P σ)).toNat

end

/-- The table's entries. -/
abbrev Lt : List Nat := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
abbrev LS4 : List Nat := [sQ, sR, sV, sK, sF]

theorem ite_toNat (p : Prop) [Decidable p] : (if p then 1 else 0) = (decide p).toNat := by
  by_cases h : p <;> simp [h]

theorem Lt_ne : ∀ i ∈ Lt, i ≠ aY ∧ i ≠ aX ∧ i ≠ aM1 := by decide

theorem AW_tab {P : MP} {j : Nat} {σ : State} {i : Nat} (hi : i ∈ Lt) : AW P j σ i = tv P σ (i - aT0) := by
  obtain ⟨h1, -, h3⟩ := Lt_ne i hi
  unfold AW; rw [ite_eq_right h1, ite_eq_right h3]

section
variable {P : MP} {m n : Nat} {σ : State}

theorem A5w_Y : A5w P m n σ aY = Y5w P m n σ := upd_self _ _ _
theorem A5w_M : A5w P m n σ aM1 = mOf P σ := by
  unfold A5w A4w; rw [upd_ne _ _ (by decide), upd_self]
theorem A5w_tab {i : Nat} (hi : i ∈ Lt) : A5w P m n σ i = tv P σ (i - aT0) := by
  obtain ⟨h1, h2, h3⟩ := Lt_ne i hi
  unfold A5w A4w A3w A2w; rw [upd_ne _ _ h1, upd_ne _ _ h3, upd_ne _ _ h2, upd_ne _ _ h1, AW_tab hi]
theorem A4w_Y : A4w P m n σ aY = (st4 P m n σ).1 := by
  unfold A4w A3w A2w; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]
theorem A4w_X : A4w P m n σ aX = tv P σ (dgw P m n σ) := by
  unfold A4w A3w; rw [upd_ne _ _ (by decide), upd_self]
theorem dgw_lt : dgw P m n σ < 16 := by
  have := svOf_lt (P := P) (σ := σ) m (n + 1); unfold dgw digitOf; omega_arith

theorem V2w_sV : V2w P m n σ sV = svOf P σ m (n + 1) := by
  unfold V2w V0w; simp only [upd, show sV ≠ sQ by decide, show sV ≠ sF by decide, show sV ≠ sR by decide, ↓reduceIte]
theorem V7w_sV : V7w P m n σ sV = svOf P σ m (n + 1) := by
  unfold V7w; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), V2w_sV]
theorem V7w_sE1 : V7w P m n σ sE1 = (decide (Y5w P m n σ = tv P σ 0)).toNat := by
  unfold V7w; rw [upd_ne _ _ (by decide), upd_self]
theorem V7w_sE2 : V7w P m n σ sE2 = (decide (Y5w P m n σ = mOf P σ)).toNat := by
  unfold V7w; rw [upd_self]
theorem V7w_sF : V7w P m n σ sF = (st4 P m n σ).2.toNat := by
  unfold V7w V2w; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_ne _ _ (by decide), upd_self]
theorem V7w_sK : V7w P m n σ sK = 8 * (m - 1) + (n + 1) := by
  unfold V7w V2w V0w
  simp only [upd, show sK ≠ sE2 by decide, show sK ≠ sE1 by decide, show sK ≠ sQ by decide, show sK ≠ sF by decide,
    show sK ≠ sR by decide, show sK ≠ sV by decide, ↓reduceIte]

/-- The window's result. -/
theorem wst_next (h : In P σ) (hm1 : 1 ≤ m) (hm : m ≤ 2 * P.w) (hn : n + 1 ≤ 8) :
    wst P σ (jw P m n + 1) = (Y5w P m n σ, if dgw P m n σ = 0 then (st4 P m n σ).2 else
      (decide (Y5w P m n σ = tv P σ 0) || decide (Y5w P m n σ = mOf P σ))) := by
  obtain hd := digit_sv h hm1 hm (by omega_arith) hn
  show mwin _ _ _ _ (eOf P σ / 16 ^ (16 * P.w - 1 - jw P m n) % 16) (wst P σ (jw P m n)) = _
  rw [← hd]
  rfl

end

/-- One window. -/
theorem win_step {P : MP} {m : Nat} (n : Nat) (fios : Bool := false) :
    VP (WI P m (n + 1)) (win (fios := fios)) fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → WO P (m - 1) σ s) ∧ (0 < n → WI P m n σ s) := by
  by_cases hc : 1 ≤ m ∧ m ≤ 2 * P.w ∧ n + 1 ≤ 8
  swap
  · exact VP.of_false fun σ s h => hc ⟨h.1, h.2.1, h.2.2.1⟩
  obtain ⟨hm1, hm, hn⟩ := hc
  refine VP.of_imp (p := P.w ≤ 128) (fun σ s h => (h.2.2.2.1 : In P σ).w128) fun w128 => ?_
  refine VP.mono (F := St P (In P) (AW P (jw P m n)) LW (V0w P m n) [sV, sK, sF]) ?_ (fun σ s h => h.2.2.2)
    (fun _ _ h => h)
  simp only [win, seqs]
  -- The count and threshold of the squarings.
  refine VP.seq (G := SqS P (In P) (AW P (jw P m n)) LW.tail (fun σ => upd (V0w P m n σ) sR 0) LS4 4 (fun _ => 0)
    (fun σ => wst P σ (jw P m n)) 4) ?_ ?_
  · refine St.psqFour.mono (fun _ _ h => h) fun σ s h => ⟨Nat.le_refl _, h.mono (fun i hi => ⟨hi, ?_⟩)
      (fun d hd => ⟨hd, ?_⟩)⟩
    · rcases List.mem_cons.mp hi with rfl | hi
      · show AW P (jw P m n) σ aY = upd (AW P (jw P m n) σ) aY (wst P σ (jw P m n)).1 aY
        rw [upd_self]; rfl
      · exact (upd_ne _ _ ((by decide : ∀ i ∈ LW.tail, i ≠ aY) i hi)).symm
    · simp only [LS4, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> rfl
  -- The squarings.
  refine VP.seq (G := St P (In P) (A2w P m n) (aY :: LW.tail) (V2w P m n) LS4)
    ((sq_loop (fios := fios) (fun σ e => e) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (fun σ _ => rfl) (fun σ _ => upd_self _ _ _)
      (fun _ _ => by decide) (by decide) (fun σ e => wst_lt e _) 3).mono (fun _ _ h => h)
      (fun σ s h => h.2)) ?_
  -- The scan.
  refine VP.seq (G := St P (In P) (A3w P m n) (aX :: aY :: Lt) (V2w P m n) LS4) ?_ ?_
  · refine VP.mono (F := St P (In P) (A2w P m n) (aY :: Lt) (V2w P m n) LS4) ?_ (fun σ s h => ?_)
      (fun _ _ h => h)
    · refine (St.pscan (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun σ _ => by rw [V2w_sV]; exact svOf_lt m (n + 1))).mono (fun _ _ h => h) fun σ s h => ?_
      refine h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
      rw [V2w_sV]
      show upd _ aX (A2w P m n σ (aT0 + dgw P m n σ)) i = upd _ aX (tv P σ (dgw P m n σ)) i
      have dl : dgw P m n σ < 16 := dgw_lt
      congr 1
      unfold A2w
      rw [upd_ne _ _ (by simp only [aT0, aY]; omega_arith), AW_tab (i := aT0 + dgw P m n σ) (by
        have : ∀ k < 16, aT0 + k ∈ Lt := by decide
        exact this _ dl), Nat.add_sub_cancel_left]
    · exact h.mono (fun i hi => ⟨(by decide : ∀ i ∈ aY :: Lt, i ∈ aY :: LW.tail) i hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩)
  -- `−1`.
  refine VP.seq (G := St P (In P) (A4w P m n) (aM1 :: aX :: aY :: Lt) (V2w P m n) LS4)
    (St.pcopyClr cM1_taint (by decide) (by decide) (by decide) (by decide)) ?_
  -- `y T_d`.
  refine VP.seq (G := St P (In P) (A5w P m n) (aY :: aM1 :: aX :: Lt) (V2w P m n) LS4) ?_ ?_
  · refine VP.mono (F := St P (In P) (A4w P m n) (aY :: aM1 :: aX :: Lt) (V2w P m n) LS4) ?_ (fun σ s h => ?_)
      (fun _ _ h => h)
    · refine (St.pmulY (fios := fios) (.inr rfl) (by decide) (by decide) (by decide) (by decide)
        (fun σ e => by rw [A4w_Y]; exact sqst_lt (q0 := 4) (fun σ e => e) (fun σ e => wst_lt e _) σ e 4)
        (fun σ e => by rw [A4w_X]; exact tv_lt e _)).mono (fun _ _ h => h) fun σ s h => ?_
      refine h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨hd, rfl⟩)
      rw [A4w_Y, A4w_X]; rfl
    · exact h.mono (fun i hi => ⟨(by decide : ∀ i ∈ aY :: aM1 :: aX :: Lt, i ∈ aM1 :: aX :: aY :: Lt) i hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩)
  -- The comparisons.
  refine VP.seq (G := St P (In P) (A5w P m n) (aY :: aM1 :: Lt)
    (fun σ => upd (V2w P m n σ) sE1 (decide (Y5w P m n σ = tv P σ 0)).toNat) (sE1 :: LS4)) ?_ ?_
  · refine VP.mono (F := St P (In P) (A5w P m n) (aY :: aM1 :: Lt) (V2w P m n) LS4) ?_ (fun σ s h => ?_)
      (fun _ _ h => h)
    · refine (St.peqS eq1_taint (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨hd, ?_⟩)
      rw [A5w_Y, A5w_tab (i := aT0) (by decide), ite_toNat, Nat.sub_self]
    · exact h.mono (fun i hi => ⟨(by decide : ∀ i ∈ aY :: aM1 :: Lt, i ∈ aY :: aM1 :: aX :: Lt) i hi, rfl⟩)
        (fun d hd => ⟨hd, rfl⟩)
  refine VP.seq (G := St P (In P) (A5w P m n) (aY :: aM1 :: Lt) (V7w P m n) (sE2 :: sE1 :: LS4))
    ((St.peqS eq2_taint (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).mono (fun _ _ h => h) fun σ s h => h.mono (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨hd, ?_⟩)) ?_
  · rw [A5w_Y, A5w_M, ite_toNat]; rfl
  -- The flag, the word and the count.
  refine (St.pwinEnd (K := 8 * (m - 1) + n) (v := fun σ => svOf P σ m (n + 1))
    (e1 := fun σ => decide (Y5w P m n σ = tv P σ 0)) (e2 := fun σ => decide (Y5w P m n σ = mOf P σ))
    (fb := fun σ => (st4 P m n σ).2) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun σ _ => V7w_sV) (fun σ _ => svOf_lt m (n + 1)) (fun σ _ => V7w_sE1) (fun σ _ => V7w_sE2)
    (fun σ _ => V7w_sF) (fun σ _ => V7w_sK) (by omega_arith)).mono (fun _ _ h => h) fun σ s ⟨h, z⟩ => ?_
  have pre : In P σ := h.1
  obtain wn := wst_next pre hm1 hm hn
  obtain j1 : jw P m n + 1 = 16 * P.w - (8 * (m - 1) + n) := by have := pre.w4; simp only [jw]; omega_arith
  rw [j1] at wn
  obtain hA : ∀ i ∈ LW, A5w P m n σ i = AW P (16 * P.w - (8 * (m - 1) + n)) σ i := fun i hi => by
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [A5w_Y]; unfold AW; rw [ite_eq_left rfl, wn]
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [A5w_M]; unfold AW; rw [ite_eq_right (by decide), ite_eq_left rfl]
    · rw [A5w_tab hi, AW_tab hi]
  obtain hF : (if digitOf (svOf P σ m (n + 1)) = 0 then (st4 P m n σ).2 else
      (decide (Y5w P m n σ = tv P σ 0) || decide (Y5w P m n σ = mOf P σ))).toNat =
      (wst P σ (16 * P.w - (8 * (m - 1) + n))).2.toNat := by rw [wn]
  obtain hL : ∀ i ∈ LW, i ∈ aY :: aM1 :: Lt := by decide
  obtain stI : 0 < n → WI P m n σ s := fun hn0 => by
    refine ⟨hm1, hm, by omega_arith, h.mono (fun i hi => ⟨hL i hi, hA i hi⟩) (fun d hd => ⟨?_, ?_⟩)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · simp only [upd, show sV ≠ sK by decide, ↓reduceIte]; exact svOf_next (by omega_arith)
      · rw [upd_self, upd_ne _ _ (by decide : sK ≠ sV), upd_self]
      · simp only [upd, show sF ≠ sK by decide, show sF ≠ sV by decide, ↓reduceIte]; exact hF
  obtain stO : n = 0 → WO P (m - 1) σ s := fun hn0 => by
    subst hn0
    refine ⟨by omega_arith, h.mono (fun i hi => ⟨hL i hi, ?_⟩) (fun d hd => ⟨?_, ?_⟩)⟩
    · rw [hA i hi, show 16 * P.w - (8 * (m - 1) + 0) = 16 * P.w - 8 * (m - 1) by omega_arith]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · simp only [upd_self, Nat.add_zero]
      · simp only [upd, show sF ≠ sK by decide, show sF ≠ sV by decide, ↓reduceIte]
        rw [hF, show 16 * P.w - (8 * (m - 1) + 0) = 16 * P.w - 8 * (m - 1) by omega_arith]
  refine ⟨?_, stO, stI⟩
  show some (!s.z) = _
  rw [z]
  by_cases h0 : n = 0
  · subst h0; simp
  · have : (8 * (m - 1) + n) % 8 = n := by omega_arith
    rw [this]; simp [h0]; omega_arith

end VG.Proof.MillerRabin.Arm

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

/-- A word's windows. -/
theorem word_step {P : MP} (n : Nat) (fios : Bool := false) :
    VP (WO P (n + 1)) (word (fios := fios)) fun σ s =>
      isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → WO P 0 σ s) ∧ (0 < n → WO P n σ s) := by
  by_cases hc : n + 1 ≤ 2 * P.w
  swap
  · exact VP.of_false fun σ s h => hc h.1
  refine VP.of_imp (p := P.w ≤ 128) (fun σ s h => (h.2.1 : In P σ).w128) fun w128 => ?_
  refine VP.mono (F := St P (In P) (AW P (16 * P.w - 8 * (n + 1))) LW
    (fun σ => upd (upd (fun _ => 0) sF (wst P σ (16 * P.w - 8 * (n + 1))).2.toNat) sK (8 * (n + 1))) [sK, sF]) ?_
    (fun σ s h => h.2) (fun _ _ h => h)
  simp only [Impl.MillerRabin.Arm.word, seqs]
  refine VP.seq (St.pwordK (K := 8 * (n + 1)) (by decide) (fun σ _ => by
    rw [upd_self])) (VP.seq (St.pwordLd (m := n + 1) (fun σ e => e) (by omega_arith) hc) ?_)
  refine VP.seq ((VP.loop (I := fun k => WI P (n + 1) k) (fun k => win_step (fios := fios) k) 7).mono (fun σ s h => ?_)
    (fun _ _ h => h)) ?_
  · refine ⟨by omega_arith, hc, by decide, ?_⟩
    refine h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨?_, ?_⟩)
    · rw [show 16 * P.w - (8 * (n + 1 - 1) + 8) = 16 * P.w - 8 * (n + 1) by omega_arith]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl
      · rw [upd_self, upd_self, svOf_eight, Nat.add_sub_cancel]
      · rw [upd_ne _ _ (by decide), upd_self, upd_ne _ _ (by decide), upd_self]; omega_arith
      · simp only [upd, show sF ≠ sV by decide, show sF ≠ sK by decide, ↓reduceIte]
        rw [show 16 * P.w - (8 * (n + 1 - 1) + (7 + 1)) = 16 * P.w - 8 * (n + 1) by omega_arith]
  · refine VP.mono (F := St P (In P) (AW P (16 * P.w - 8 * n)) LW
      (fun σ => upd (upd (fun _ => 0) sF (wst P σ (16 * P.w - 8 * n)).2.toNat) sK (8 * n)) [sK, sF]) ?_
      (fun σ s h => by rw [Nat.add_sub_cancel] at h; exact h.2) (fun _ _ h => h)
    refine (St.pwordEnd (K := 8 * n) (by decide) (fun σ _ => upd_self _ _ _) (by omega_arith)).mono (fun _ _ h => h)
      fun σ s ⟨h, z⟩ => ⟨?_, fun h0 => ⟨by omega_arith, h0 ▸ h⟩, fun _ => ⟨by omega_arith, h⟩⟩
    show some (!s.z) = _
    rw [z]
    by_cases h0 : n = 0 <;> simp [h0, Nat.pos_iff_ne_zero, Nat.mul_eq_zero]

/-- The words. -/
theorem words_loop {P : MP} (fios : Bool := false) : VP (WO P (2 * P.w)) (.loop (word (fios := fios)) .ne) (WO P 0) := by
  refine VP.of_imp (p := 1 ≤ P.w) (fun σ s h => by have := (h.2.1 : In P σ).w4; omega_arith) fun w1 => ?_
  have := VP.loop (I := fun k => WO P k) (fun k => word_step (fios := fios) k) (2 * P.w - 1)
  rwa [show 2 * P.w - 1 + 1 = 2 * P.w by omega_arith] at this

end VG.Proof.MillerRabin.Arm

end

end

/-! # The Miller–Rabin round on ARMv7: the body

From the state `σ` after the push (`In P σ`, `ws` in `r0`): the table's
first entries (`tabInit_vp`), its loop, the windows' start (`winInit_vp`),
the words, the last three squarings with the threshold `4 − σ`, and the
flag into `r0` (`body_vp`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Arm
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.MillerRabin.Arm VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.RsaKeyGen (sigOf sigOf_pos)

/-- The body's start. -/
def Start (P : MP) (σ s : State) : Prop := s = σ ∧ In P σ ∧ σ.gpr .r0 = P.ws

/-- The threshold of the last squarings: `4 − σ`. -/
abbrev rEnd (P : MP) (σ : State) : Nat := 4 - sigOf (tOf P σ % 64)

/-- The flag after the last squarings. -/
abbrev fl (P : MP) (σ : State) : Bool := (sqst P 3 (rEnd P) (fun σ => wst P σ (16 * P.w)) σ 3).2

/-- The body's end: the flag in `r0`. -/
def Done (P : MP) (σ s : State) : Prop :=
  (∃ A L V LS, KS P σ A L V LS s) ∧ s.gpr .r0 = BitVec.ofNat 32 (fl P σ).toNat

/-- The arrays the table's loop starts from: `x` and the original arrays it shifts. -/
abbrev L0 : List Nat := [aX, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

section
variable {P : MP}

/-- `x`'s top words cleared. -/
theorem St.pclrX {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
    {LS : List Nat} (hx : aX ∈ L) (hv : ∀ σ, E σ → A σ aX = num σ.mem P.B P.W aX) :
    VP (St P E A L V LS) (.block (Impl.Rsa.Arm.Recover.clrTop aX))
      (St P E (fun σ => upd (A σ) aX (xOf P σ)) (aX :: L) V LS) := by
  refine VP.kv clrX_taint (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ => ?_
  rw [← List.append_nil (Impl.Rsa.Arm.Recover.clrTop aX)]
  refine h.clrTop_ok hw (by decide) fun t ht hwt _ => WP.block_nil ⟨e, ?_, hwt⟩
  have pre := h.pre
  have a1 := (h.arrs aX hx).trans (hv σ e)
  have e1 : val32 s.mem (State.addr P.B) (arr P.W aX) (2 * P.w) = xOf P σ :=
    calc val32 s.mem (State.addr P.B) (arr P.W aX) (2 * P.w)
        = num s.mem P.B P.W aX % 2 ^ (32 * (2 * P.w)) := val32_low _ _ _ _ 2
      _ = num σ.mem P.B P.W aX % 2 ^ (32 * (2 * P.w)) := by rw [a1]
      _ = val32 σ.mem (State.addr P.B) (arr P.W aX) (2 * P.w) := (val32_low _ _ _ _ 2).symm
      _ = xOf P σ := (pre.numAt_val32 σ.mem aX).symm
  rwa [e1] at ht

theorem tabInit_vp : VP (Start P) (seqs tabInit) (TS P 14) := by
  simp only [tabInit, seqs]
  let A0 := fun σ : State => fun j => num σ.mem P.B P.W j
  refine VP.seq (G := St P (In P) A0 L0 (fun _ _ => 0) []) ?_ ?_
  · refine VP.taint [.r0] ctx_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨hs, pre, r0⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      rw [h₁.1, h₂.1, h₁.2.2, h₂.2.2]
    · rw [hs, ← List.append_nil ctx]
      have k0 : KS P σ (A0 σ) L0 (fun _ => 0) [] σ :=
        ⟨pre, rfl, rfl, rfl, Keep.refl _ _ _ _ _, fun j _ => rfl, fun _ h => absurd h List.not_mem_nil,
          by decide, fun _ h => absurd h List.not_mem_nil⟩
      exact k0.ctx_ok r0 fun t ht hwt _ _ => WP.block_nil ⟨pre, ht, hwt⟩
  refine VP.seq (St.pcopyClr cT0_taint (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq (St.pclrX (by decide) fun σ _ => rfl) ?_
  refine VP.seq (St.pcopy cT1_taint (by decide) (by decide) (by decide)) ?_
  refine VP.seq (St.pcopy cYX_taint (by decide) (by decide) (by decide)) ?_
  refine St.ptabCnt.mono (fun _ _ h => h) fun σ s h => ⟨by decide, h.mono (fun i hi => ⟨?_, ?_⟩)
    (fun d hd => ⟨by simp only [List.mem_singleton] at hd; simp [hd], by
      simp only [List.mem_singleton] at hd; subst hd; rfl⟩)⟩
  · exact (by decide : ∀ i ∈ LT, i ∈ aY :: (aT0 + 1) :: aX :: aT0 :: L0) i hi
  · simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> rfl

theorem tab_final {σ : State} : ∀ i ∈ LT, i ≠ aY → i ≠ aX → AT P 14 σ i = tv P σ (i - aT0) := by
  intro i hi h1 h2
  simp only [LT, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · exact absurd rfl h1
  · exact absurd rfl h2
  all_goals rfl

theorem winInit_vp : VP (TS P 0) (seqs winInit) (WO P (2 * P.w)) := by
  simp only [winInit, seqs]
  refine VP.mono (F := St P (In P) (AT P 14) LT (fun _ => upd (fun _ => 0) sK 0) [sK]) ?_ (fun σ s h => h.2)
    (fun _ _ h => h)
  refine VP.seq (St.pcopyClr cM1_taint (by decide) (by decide) (by decide) (by decide)) ?_
  refine VP.seq (St.pcopy cY0_taint (by decide) (by decide) (by decide)) ?_
  refine St.pwinCnt.mono (fun _ _ h => h) fun σ s h => ⟨Nat.le_refl _, h.mono (fun i hi => ⟨?_, ?_⟩)
    (fun d hd => ⟨?_, ?_⟩)⟩
  · exact (by decide : ∀ i ∈ LW, i ∈ aY :: aM1 :: LT) i hi
  · rw [show 16 * P.w - 8 * (2 * P.w) = 0 by omega_using []]
    rcases List.mem_cons.mp hi with rfl | hi
    · rfl
    rcases List.mem_cons.mp hi with rfl | hi
    · rfl
    · obtain ⟨h1, h2, h3⟩ := Lt_ne i hi
      rw [upd_ne _ _ h1, upd_ne _ _ h3, tab_final i ((by decide : ∀ i ∈ Lt, i ∈ LT) i hi) h1 h2, AW_tab hi]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢; rcases hd with rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · rw [upd_self, upd_self]; omega_using []
    · rw [upd_ne _ _ (by decide), upd_self, upd_ne _ _ (by decide), upd_self,
        show 16 * P.w - 8 * (2 * P.w) = 0 by omega_using []]
      rfl

/-- The threshold from the word `2^(t mod 64)`. -/
theorem rEnd_eq {σ : State} (pre : In P σ) :
    (foldR (BitVec.ofNat 32 (ew P σ (2 * P.w))) (BitVec.ofNat 32 (ew P σ (2 * P.w + 1)))).toNat = rEnd P σ := by
  obtain ⟨e1, e2⟩ := pre.ew_low
  rw [e1, e2, foldR_eq _ (Nat.mod_lt _ (by decide)), ofNat_toNat32 (by omega_using [])]

theorem body_vp (fios : Bool := false) : VP (Start P) (body (fios := fios)) (Done P) := by
  simp only [body, seqs]
  refine VP.seq tabInit_vp (VP.seq (tab_loop (fios := fios)) (VP.seq winInit_vp (VP.seq (words_loop (fios := fios)) ?_)))
  refine VP.mono (F := St P (In P) (AW P (16 * P.w)) LW
    (fun σ => upd (upd (fun _ => 0) sF (wst P σ (16 * P.w)).2.toNat) sK 0) [sK, sF]) ?_ (fun σ s h => h.2)
    (fun _ _ h => h)
  let V' := fun σ => upd (upd (upd (fun _ => 0) sF (wst P σ (16 * P.w)).2.toNat) sK 0) sR (rEnd P σ)
  refine VP.seq (G := SqS P (In P) (AW P (16 * P.w)) LW.tail V' [sQ, sR, sK, sF] 3 (rEnd P)
    (fun σ => wst P σ (16 * P.w)) 3) ?_ ?_
  · refine (St.plowBits (fun σ e => e)).mono (fun _ _ h => h) fun σ s h => ⟨by decide,
      h.mono (fun i hi => ⟨hi, ?_⟩) (fun d hd => ⟨hd, ?_⟩)⟩
    · rcases List.mem_cons.mp hi with rfl | hi
      · rw [upd_self]; unfold AW; rw [ite_eq_left rfl]; rfl
      · exact (upd_ne _ _ ((by decide : ∀ i ∈ LW.tail, i ≠ aY) i hi)).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl
      · simp only [upd_self]
      · simp only [V', upd, show sR ≠ sQ by decide, show sR ≠ sF by decide, ↓reduceIte]
        exact rEnd_eq h.1
      · simp only [V', upd, show sK ≠ sQ by decide, show sK ≠ sF by decide, show sK ≠ sR by decide, ↓reduceIte]
      · simp only [V', upd, show sF ≠ sQ by decide, show sF ≠ sR by decide, ↓reduceIte]; rfl
  refine VP.seq (sq_loop (fios := fios) (fun σ e => e) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (fun σ _ => rfl) (fun σ _ => upd_self _ _ _)
    (fun σ _ => by show 4 - sigOf (tOf P σ % 64) < 2 ^ 31; omega_using []) (by decide) (fun σ e => wst_lt e _) 2) ?_
  refine VP.kv ret_taint (fun _ _ h => h.2.2.2) fun σ s ⟨_, e, h, hw⟩ => ?_
  refine h.ldr hw (d := sF) (by decide) (r := .r0) (by decide) fun t ht _ u => WP.block_nil ⟨⟨_, _, _, _, ht⟩, ?_⟩
  rw [u.gpr]
  simp only [upd, show sF ≠ sQ by decide, ↓reduceIte]

end

end VG.Proof.MillerRabin.Arm
