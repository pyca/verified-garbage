module

import VerifiedGarbage.Proof.MillerRabin.Arm.Ops
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Base
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.MillerRabin.Arm.Mont
public import VerifiedGarbage.Proof.MillerRabin.Arm.Taint
public import VerifiedGarbage.Proof.MillerRabin.Word32 -- shake: keep: re-export the shared arithmetic under the existing ARM names.
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.MillerRabin.Arm.Base
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.MillerRabin.Arm.ArithmeticCT
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Rsa.Arm.CvLoad
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont2

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
