module

import VerifiedGarbage.Proof.MillerRabin.Arm.Mont
public import VerifiedGarbage.Proof.MillerRabin.Arm.Taint
public import VerifiedGarbage.Proof.MillerRabin.Arm.Math
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.MillerRabin.Arm.Base
import VerifiedGarbage.Proof.Bignum.Arm.MontOpCT
import VerifiedGarbage.Proof.MillerRabin.Arm.ArithmeticCT
import VerifiedGarbage.Proof.MillerRabin.Arm.Ops
import VerifiedGarbage.Proof.MillerRabin.Arm.Arithmetic
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Rsa.Arm.KeyDiv
import VerifiedGarbage.Proof.Rsa.Arm.RvKS
import VerifiedGarbage.Proof.Rsa.Arm.RvMont2

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

/-- `copy o a` and `clrTop o` of an array whose words the stage knows from `σ`. -/
theorem St.pcopyClrL {o a : Nat} (cert : Cert (seqs (copyClr o a))) (ho : o ∈ wJs) (ha : a ∈ L) (hoa : o ≠ a)
    (hv : ∀ σ, E σ → A σ a = num σ.mem P.B P.W a) :
    VP (St P E A L V LS) (seqs (copyClr o a)) (St P E (fun σ => upd (A σ) o (numAt σ.mem (State.addr P.ws) P.w a))
      (o :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ s ⟨e, h, hw⟩ =>
    WP.mono (h.copyClr_ok hw ho (h.live_lt a ha) hoa) fun _ ⟨ht, hwt⟩ => ⟨e, by
      have pre := h.pre
      have e1 : numAt s.mem (State.addr P.ws) P.w a = numAt σ.mem (State.addr P.ws) P.w a := by
        rw [pre.numAt_val32, pre.numAt_val32, val32_low _ _ _ (2 * P.w) 2, val32_low σ.mem _ _ (2 * P.w) 2]
        have := (h.arrs a ha).trans (hv σ e)
        simp only [num, MP.W] at this
        rw [this]
      rwa [e1] at ht, hwt⟩

theorem St.pcopy {o a : Nat} (cert : Cert (copy o a)) (ho : o ∈ wJs) (ha : a ∈ L) (hoa : o ≠ a) :
    VP (St P E A L V LS) (copy o a) (St P E (fun σ => upd (A σ) o (A σ a)) (o :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun _ _ ⟨e, h, hw⟩ =>
    WP.mono (h.copy_ok hw ho (h.live_lt a ha) hoa) fun _ ⟨ht, hwt, _⟩ => ⟨e, by rwa [h.arrs a ha] at ht, hwt⟩

theorem St.psel {o a b sl : Nat} (cert : Cert (sel o a b sl)) (ho : o ∈ wJs) (ha : a ∈ L) (hb : b ∈ L)
    (hoa : o ≠ a) (hob : o ≠ b) (hsl : sl ∈ LS) (bit : ∀ σ, E σ → V σ sl ≤ 1) :
    VP (St P E A L V LS) (sel o a b sl)
      (St P E (fun σ => upd (A σ) o (if V σ sl = 0 then A σ a else A σ b)) (o :: L) V LS) :=
  VP.kv cert (fun _ _ h => h.2.2) fun σ _ ⟨e, h, hw⟩ =>
    WP.mono (h.sel_ok hw ho ha hb hoa hob hsl (bit σ e)) fun _ ⟨ht, hwt, _⟩ => ⟨e, ht, hwt⟩

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
