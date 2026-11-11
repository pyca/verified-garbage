module

-- separate module: its proofs (about 2 s, a step of the loop) are not checked again when `Window` changes

public import VerifiedGarbage.Proof.P256.X86_64.Ifma.Pass
public import VerifiedGarbage.Proof.Weierstrass.Joint
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInvariant
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepFields
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
public import VerifiedGarbage.Proof.Weierstrass.WinLay
public import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigit
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Weierstrass.TCombWords

/-!
# P-256 on x86-64 with AVX512_IFMA: the loop over the digits

What the accumulator is after each digit, as field elements (`accDbl`,
`accStep`), and that it stands for the sum so far or has `z` zero (`AccPt`).
-/

@[expose] public section

namespace VG.Proof.P256.X86_64.Ifma

open VG VG.X86_64 VG.Impl.P256.X86_64.Ifma
open Spec.Weierstrass VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

/-- The accumulator after a doubling. -/
def accDbl : Option (Fin pN × Fin pN × Fin pN) → Option (Fin pN × Fin pN × Fin pN)
  | none => none
  | some a => some (fX3 a.1 a.2.1 a.2.2, fU a.1 a.2.1 a.2.2, fZ3 a.2.1 a.2.2)

/-- The accumulator stands for `A`, or its `z` is zero; if it is not set, `A` is `O`. -/
def AccPt (acc : Option (Fin pN × Fin pN × Fin pN)) (A : Point Cv) : Prop :=
  match acc with
  | none => A = .infinity
  | some a => Pinv a.1 a.2.1 a.2.2 A

theorem accPt_dbl (hC : Law Cv) (ha : AM3 Cv) {acc : Option (Fin pN × Fin pN × Fin pN)} {A : Point Cv}
    (hA : onCurve Cv A = true) (h : AccPt acc A) : AccPt (accDbl acc) (Spec.Weierstrass.add A A) := by
  cases acc with
  | none =>
    have : A = .infinity := h
    subst this
    rfl
  | some a => exact pinv_dbl hC ha hA h

/-- The entry of the triple `(X, Y, Z)` of `B`, or of its negative, added to the accumulator or taken as it. -/
theorem accPt_step (hC : Law Cv) (ha : AM3 Cv) {acc : Option (Fin pN × Fin pN × Fin pN)} {A B : Point Cv}
    {X Y Z : Fe Cv} (neg : Bool) (hA : onCurve Cv A = true) (hB : onCurve Cv B = true) (h : AccPt acc A)
    (hJ : InvJ Cv X Y Z B) :
    AccPt (some (accStep X Y Z neg acc)) (Spec.Weierstrass.add A (if neg then negPt B else B)) := by
  cases acc with
  | none =>
    have : A = .infinity := h
    subst this
    obtain ⟨hi, hy⟩ := entQ_inv hC hJ neg 0 0 0
    exact pinv_set hC neg hi hy
  | some a =>
    obtain ⟨hi, hy⟩ := entQ_inv hC hJ neg a.1 a.2.1 a.2.2
    exact pinv_add hC ha hA hB h hi hy (entQ_zz X Y Z neg _ _ _) (entQ_zzz X Y Z neg _ _ _)

/-! ### The joint multiplication's invariant is kept by the vectors' code -/

/-- `JointStable.keep`, for memory kept but in ranges `W`. -/
theorem jointStable_unch {c : Joint.Cfg} {C : Curve} {base : Addr} {Q : Point C} {u v : Nat} {s t : State}
    {W : List (Nat × Nat)} (h : JointStable c C base Q u v s) (hu : Unch base W s.mem t.mem)
    (hb : ∀ r ∈ jointStableRanges c, r.1 + r.2 ≤ 2 ^ 64)
    (hsep : ∀ r ∈ jointStableRanges c, ∀ w ∈ W, r.1 + r.2 ≤ w.1 ∨ w.1 + w.2 ≤ r.1) :
    JointStable c C base Q u v t := by
  have hrange (x : Nat) (hx : x ∈ jointStableFields c) : (x, 8 * c.K.M.n) ∈ jointStableRanges c :=
    List.mem_append_left _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
  have hf (x : Nat) (hx : x ∈ jointStableFields c) : tmv C c.K.M.n base t x = tmv C c.K.M.n base s x := by
    unfold tmv
    rw [hu.wordsVal (hsep _ (hrange x hx)) (hb _ (hrange x hx))]
  have hbits (d l : Nat) (ho : (d, l) ∈ jointStableRanges c) (j : Nat) (hj : j < l) :
      t.mem (off base (d + j)) = s.mem (off base (d + j)) := by
    apply hu.byte
    · intro w hw
      have := hsep _ ho w hw
      dsimp only at this ⊢; omega
    · have := hb _ ho; dsimp only at this; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf c.K.zero (by simp [jointStableFields, winRo]), h.zero]
  · intro a ha hb
    rw [hf _ (jointStable_table c ha (by omega) (by simp [jacCoords])),
      hf _ (jointStable_table c ha (by omega) (by simp [jacCoords])),
      hf _ (jointStable_table c ha (by omega) (by simp [jacCoords]))]
    exact h.table a ha hb
  · intro j hj
    rw [hbits c.K.bits _ (by simp [jointStableRanges]) j hj]
    exact h.peer j hj
  · intro j hj
    rw [hbits c.gBits _ (by simp [jointStableRanges]) j hj]
    exact h.generator j hj
  · intro i hi
    rw [hf _ (jointStable_cache2 c hi), hf _ (jointStable_table c (a := i + 1) (by omega) (by omega) (by simp [jacCoords]))]
    exact h.cache2 i hi
  · intro i hi
    rw [hf _ (jointStable_cache3 c hi), hf _ (jointStable_cache2 c hi),
      hf _ (jointStable_table c (a := i + 1) (by omega) (by omega) (by simp [jacCoords]))]
    exact h.cache3 i hi

/-- What the loop in vectors writes of the working space: the vectors' slots, MXCSR saved, and the
blocks' constants. -/
def vW : List (Nat × Nat) := [(4512, 896), (5472, 8), (6016, 1760)]

/-- Where the vectors' slots are among what the joint multiplication keeps in the working space. -/
structure VLay (c : Joint.Cfg) (size : Nat) : Prop where
  big : 5408 ≤ size
  mx : 5480 ≤ size
  pool : 7776 ≤ size
  live : ∀ x ∈ jointLive c, ∀ w ∈ vW, x + 8 * c.K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x
  liveB : ∀ x ∈ jointLive c, x + 8 * c.K.M.n ≤ size
  mo : ∀ w ∈ vW, c.K.M.mo + 8 * c.K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ c.K.M.mo
  stable : ∀ r ∈ jointStableRanges c, ∀ w ∈ vW, r.1 + r.2 ≤ w.1 ∨ w.1 + w.2 ≤ r.1
  stableB : ∀ r ∈ jointStableRanges c, r.1 + r.2 ≤ size
  n : c.K.M.n = 4
  tbl : c.K.tbl + 768 ≤ 4512
  cache : c.cache + 512 ≤ 4512
  rxy : c.K.R.x ≠ c.K.R.y
  rxz : c.K.R.x ≠ c.K.R.z
  ryz : c.K.R.y ≠ c.K.R.z

/-- What the loop keeps: the registers but its own, and memory but the vectors' slots. -/
structure VKeep (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .rbx] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : Unch (s.gpr .rdi) [(cfg.sbase, par.win - cfg.sbase)] s.mem t.mem

theorem VKeep.refl (s : State) : VKeep s s := ⟨fun _ _ => rfl, rfl, rfl, Unch.refl _ _ _⟩

theorem VKeep.trans {s t u : State} (h₁ : VKeep s t) (h₂ : VKeep t u) : VKeep s u := by
  refine ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, ?_⟩
  have := h₂.mem
  rw [h₁.gpr .rdi (by decide)] at this
  exact (h₁.mem.trans this).mono (by decide)

theorem VKeep.of_lkeep {s t : State} (h : LKeep s t) : VKeep s t :=
  ⟨fun r hr => h.gpr r fun h' => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
    rcases h' with h' | h' | h' | h' | h' | h' | h' <;> simp [h']), h.rd, h.wr, h.mem⟩

theorem VKeep.of_skeep {rs : List Reg} {s t : State} (h : SKeep rs s t)
    (hr : (rs.all fun r => [Reg.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .rbx].contains r) = true := by decide) :
    VKeep s t :=
  ⟨fun r h' => h.gpr r fun hin => h' (List.contains_iff_mem.mp (List.all_eq_true.mp hr r hin)), h.rd, h.wr,
    by rw [h.mem]; exact Unch.refl _ _ _⟩

/-- The joint multiplication's invariant is kept by writes to the vectors' part of the working space. -/
theorem jointCore_unch {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v : Nat} {G Q A : Point C}
    {row : JointGeneratorRow c.K.M.n C G (jointGTop c)} {s t : State} (hV : VLay c size)
    (h : JointCore c C base size Q u v (JointGenerator c C base T size row) A s)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hu : Unch base vW s.mem t.mem)
    (hs : t.syms = s.syms) : JointCore c C base size Q u v (JointGenerator c C base T size row) A t := by
  have hnw := h.field.scr.nowrap
  have st : Scr t base size := ⟨hdi.trans h.field.scr.rdi, hwr ▸ h.field.scr.wr, hnw⟩
  have hi : Inv c.K.M base size C.p (· ∈ jointSlots c) (jointLive c) (tmv C c.K.M.n base s) t :=
    Inv.of_unch h.field st hu hV.liveB hV.live hV.mo
  refine ⟨hi.to_tmv, jointStable_unch h.stable hu (fun r hr => by have := hV.stableB r hr; omega) hV.stable, ?_,
    hi.point_tmv (jointLive_R c) h.point⟩
  intro a ha hb ho
  refine (h.external a ha hb ho).keep_of_mem hs hrd hwr fun z hz => ?_
  exact hu z fun w hw => by
    have := hV.pool
    simp only [vW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> dsimp only <;> omega

/-- The joint multiplication's invariant is kept by the loop's code. -/
theorem jointCore_vkeep {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v : Nat} {G Q A : Point C}
    {row : JointGeneratorRow c.K.M.n C G (jointGTop c)} {s t : State} (hV : VLay c size)
    (h : JointCore c C base size Q u v (JointGenerator c C base T size row) A s) (k : VKeep s t)
    (hs : t.syms = s.syms) : JointCore c C base size Q u v (JointGenerator c C base T size row) A t := by
  refine jointCore_unch hV h (k.gpr .rdi (by decide)) k.rd k.wr ?_ hs
  have := k.mem
  rw [h.field.scr.rdi] at this
  exact this.mono (by decide)

theorem jointCore_lkeep {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v : Nat} {G Q A : Point C}
    {row : JointGeneratorRow c.K.M.n C G (jointGTop c)} {s t : State} (hV : VLay c size)
    (h : JointCore c C base size Q u v (JointGenerator c C base T size row) A s) (k : LKeep s t)
    (hs : t.syms = s.syms) : JointCore c C base size Q u v (JointGenerator c C base T size row) A t :=
  jointCore_vkeep hV h (.of_lkeep k) hs

/-! ### A digit of `Q`'s scalar -/

/-- The accumulator after digit `j` of `Q`'s scalar `v`: with the digit's multiple of `Q`, from the table. -/
def qNext (c : Joint.Cfg) (E : Nat → Fe Cv) (v j : Nat) (acc : Option (Fin pN × Fin pN × Fin pN)) :
    Option (Fin pN × Fin pN × Fin pN) :=
  if FastNaf.byte 5 v j = 0 then acc
  else some (accStep (E (c.K.tblPt ((FastNaf.magnitude 5 v j - 1) / 2 + 1)).x)
    (E (c.K.tblPt ((FastNaf.magnitude 5 v j - 1) / 2 + 1)).y)
    (E (c.K.tblPt ((FastNaf.magnitude 5 v j - 1) / 2 + 1)).z) (FastNaf.negative 5 v j) acc)

theorem accSt_skeep {rs : List Reg} {s t : State} (k : SKeep rs s t) (h11 : Reg.r11 ∉ rs)
    {acc : Option (Fin pN × Fin pN × Fin pN)} (h : AccSt s acc) : AccSt t acc := by
  cases acc with
  | none => exact (k.gpr .r11 h11).trans h
  | some a => exact ⟨(k.gpr .r11 h11).trans h.1, h.2.congr k.v⟩

theorem qNeg (b : BitVec 8) : (!decide (b.toNat < 128)) = decide (128 ≤ b.toNat) := by
  by_cases h : b.toNat < 128
  · simp only [h, decide_true, Bool.not_true]
    exact (decide_eq_false (by omega)).symm
  · simp only [h, decide_false, Bool.not_false]
    exact (decide_eq_true (by omega)).symm

/-- A digit of `Q`'s scalar: its multiple of `Q` added to the accumulator, if it is not zero. -/
theorem qPass_ok {c : Joint.Cfg} {base T : Addr} {size u v j : Nat} {G Q A : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {s : State} (hV : VLay c size)
    (h : JointCore c Cv base size Q u v (JointGenerator c Cv base T size row) A s)
    (hc : Ctx par s) (hB : EnvOK s stB) (hj : j < 257) (hb : s.gpr .rbx = BitVec.ofNat 64 j)
    {acc : Option (Fin pN × Fin pN × Fin pN)} (hacc : AccSt s acc) :
    WP isa (qPass c) s fun t =>
      JointCore c Cv base size Q u v (JointGenerator c Cv base T size row) A t ∧ Ctx par t ∧ EnvOK t stB ∧
        AccSt t (qNext c (tmv Cv c.K.M.n base s) v j acc) ∧ LKeep s t := by
  have hn := hV.n
  have hbytes : c.K.bits + j < size := by
    have := hV.stableB (c.K.bits, 64 * c.K.M.n + 1) (by simp [jointStableRanges])
    rw [hn] at this
    dsimp only at this
    omega
  rw [qPass, qBody]
  apply WP.seq
  have hr := WP.mono (nafRead_ok h.field.scr hbytes hb (h.stable.peer j (by rw [hn]; omega)))
    fun t (x : t.gpr .r8 = (FastNaf.byte 5 v j).setWidth 64 ∧ t.zf = some (decide (FastNaf.byte 5 v j = 0)) ∧
      VG.Proof.X25519.X86_64.Keeps [.r8] s t) =>
      (⟨⟨x.1, x.2.1⟩, x.2.2⟩ : (t.gpr .r8 = (FastNaf.byte 5 v j).setWidth 64 ∧
        t.zf = some (decide (FastNaf.byte 5 v j = 0))) ∧ VG.Proof.X25519.X86_64.Keeps [.r8] s t)
  refine WP.mono_syms (WP.skeep rfl hr) fun a ⟨⟨a8, az⟩, ka⟩ sa => ?_
  have la : LKeep s a := LKeep.of_skeep ka
  have ca := jointCore_lkeep hV h la sa
  have hca : Ctx par a := ctx_skeep hc ka (by decide) (by decide) (fun r d hr' hd => by
    rw [List.mem_singleton] at hr'; subst hr'
    rw [lim_other (by decide) (by decide) (by decide)] at hd; omega)
  have hBa : EnvOK a stB := envOK_skeep ka (by decide) hB
  have hacca : AccSt a acc := accSt_skeep ka (by decide) hacc
  refine WP.ite (decide (FastNaf.byte 5 v j = 0)) az (fun hz => ?_) (fun hnz => ?_)
  · have hz' : FastNaf.byte 5 v j = 0 := of_decide_eq_true hz
    refine WP.block_nil ⟨ca, hca, hBa, ?_, la⟩
    simp only [qNext, hz', ↓reduceIte]
    exact hacca
  · have hnz' : ¬FastNaf.byte 5 v j = 0 := of_decide_eq_false hnz
    have hmag : FastNaf.magnitude 5 v j ≠ 0 := fun he => hnz' ((FastNaf.byte_zero_iff 5 v j).mpr he)
    have hl := FastNaf.magnitude_le (Or.inl rfl) v j
    have ho := (FastNaf.magnitude_odd_or_zero 5 v j).resolve_left hmag
    have em : qMag (FastNaf.byte 5 v j) = FastNaf.magnitude 5 v j := FastNaf.byte_magnitude 5 v j
    have hi : (FastNaf.magnitude 5 v j - 1) / 2 < 8 := by omega
    have tv (x : Nat) : tmv Cv c.K.M.n base a x = tmv Cv c.K.M.n base s x := by
      unfold tmv; rw [ka.mem]
    have tw (x d : Nat) (hx : x = d) :
        toM pN (2 ^ 256) (wordsVal a.mem base d 4) = tmv Cv c.K.M.n base s x := by
      subst hx; unfold tmv; rw [ka.mem, hn]; rfl
    have c2 := ca.stable.cache2 _ hi
    have c3 := ca.stable.cache3 _ hi
    rw [tv, tv] at c2
    rw [tv, tv, tv] at c3
    rw [c2] at c3
    refine WP.mono_syms (qDigit_ok hn ca.field.scr hca hBa a8 (by rw [em]; omega) (by rw [em]; exact hl)
      (by rw [em]; exact ho) hV.tbl hV.cache hV.big
      (tw (c.K.tblPt ((FastNaf.magnitude 5 v j - 1) / 2 + 1)).x _ (by rw [tblPt_x, hn, em] <;> omega))
      (tw (c.K.tblPt ((FastNaf.magnitude 5 v j - 1) / 2 + 1)).y _ (by rw [tblPt_y, hn, em] <;> omega))
      (tw (c.K.tblPt ((FastNaf.magnitude 5 v j - 1) / 2 + 1)).z _ (by rw [tblPt_z, hn, em] <;> omega))
      ((tw (c.cache + 16 * c.K.M.n * ((FastNaf.magnitude 5 v j - 1) / 2)) _ (by rw [hn, em] <;> omega)).trans c2)
      ((tw (c.cache + 16 * c.K.M.n * ((FastNaf.magnitude 5 v j - 1) / 2) + 8 * c.K.M.n) _
        (by rw [hn, em] <;> omega)).trans c3) hacca) fun t ⟨hct, hBt, hat, kt⟩ st => ?_
    refine ⟨jointCore_lkeep hV ca kt st, hct, hBt, ?_, la.trans kt⟩
    simp only [qNext, hnz', ↓reduceIte]
    rw [qNeg, FastNaf.byte_negative 5 v j] at hat
    exact hat

/-! ### A digit of the generator's scalar -/

/-- The generator's table at `T`: readable, and outside the working space. -/
def GTab (base T : Addr) (size : Nat) (s : State) : Prop :=
  InRegions (s.rd ++ s.wr) T 16320 ∧ ∀ d, d < 16320 → size ≤ ofs base (T + BitVec.ofNat 64 d)

theorem GTab.lkeep {base T : Addr} {size : Nat} {s t : State} (h : GTab base T size s) (k : LKeep s t) :
    GTab base T size t := ⟨by rw [k.rd, k.wr]; exact h.1, h.2⟩

theorem GTab.vkeep {base T : Addr} {size : Nat} {s t : State} (h : GTab base T size s) (k : VKeep s t) :
    GTab base T size t := ⟨by rw [k.rd, k.wr]; exact h.1, h.2⟩

/-- The accumulator after digit `j` of the generator's scalar `u`: with the digit's multiple of the generator,
from the rows of the table. -/
def gNext (c : Joint.Cfg) {G : Point Cv} (row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)) (u j : Nat)
    (acc : Option (Fin pN × Fin pN × Fin pN)) : Option (Fin pN × Fin pN × Fin pN) :=
  if FastNaf.magnitude 9 u j = 0 then acc
  else some (accStep (toM Cv.p (2 ^ (64 * c.K.M.n)) (row.x (FastNaf.magnitude 9 u j)))
    (toM Cv.p (2 ^ (64 * c.K.M.n)) (row.y (FastNaf.magnitude 9 u j))) 1 (FastNaf.negative 9 u j) acc)

theorem gNeg (w : BitVec 16) : (!decide (w.toNat < 256)) = decide (256 ≤ w.toNat) := by
  by_cases h : w.toNat < 256
  · simp only [h, decide_true, Bool.not_true]
    exact (decide_eq_false (by omega)).symm
  · simp only [h, decide_false, Bool.not_false]
    exact (decide_eq_true (by omega)).symm

/-- A digit of the generator's scalar: its multiple of the generator added to the accumulator, if it is not zero. -/
theorem gPass_ok {c : Joint.Cfg} {base T : Addr} {size u v j : Nat} {G Q A : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {s : State} (hV : VLay c size) (hL : JointLayout c size)
    (h9 : c.gw = 9) (h : JointCore c Cv base size Q u v (JointGenerator c Cv base T size row) A s)
    (hG : GTab base T size s) (hc : Ctx par s) (hB : EnvOK s stB) (hj : j < 257)
    (hb : s.gpr .rbx = BitVec.ofNat 64 j) {acc : Option (Fin pN × Fin pN × Fin pN)} (hacc : AccSt s acc) :
    WP isa (gPass c) s fun t =>
      JointCore c Cv base size Q u v (JointGenerator c Cv base T size row) A t ∧ Ctx par t ∧ EnvOK t stB ∧
        AccSt t (gNext c row u j acc) ∧ LKeep s t := by
  have hn := hV.n
  have hdi := h.field.scr.rdi
  have hnw := h.field.scr.nowrap
  have hlo : par.lo = 4512 := rfl
  have hwin : par.win = 5408 := rfl
  have hbig := hV.big
  rw [gPass, gBody]
  apply WP.seq
  have hr := WP.mono (jointFixedRead_ok hL h (by rw [hn]; omega) hb)
    fun t (x : t.gpr .r8 = jointGCell c u j ∧ t.zf = some (decide (FastNaf.magnitude c.gw u j = 0)) ∧
      VG.Proof.X25519.X86_64.Keeps [.r8] s t) =>
      (⟨⟨x.1, x.2.1⟩, x.2.2⟩ : (t.gpr .r8 = jointGCell c u j ∧
        t.zf = some (decide (FastNaf.magnitude c.gw u j = 0))) ∧ VG.Proof.X25519.X86_64.Keeps [.r8] s t)
  refine WP.mono_syms (WP.skeep (by rw [Joint.fixedRead, ite_eq_left h9]; rfl) hr) fun a ⟨⟨a8, az⟩, ka⟩ sa => ?_
  rw [h9] at az
  have a8' : a.gpr .r8 = (FastNaf.word u j).setWidth 64 := by rw [a8, jointGCell, ite_eq_left h9]
  have la : LKeep s a := LKeep.of_skeep ka
  have ca := jointCore_lkeep hV h la sa
  have hca : Ctx par a := ctx_skeep hc ka (by decide) (by decide) (fun r d hr' hd => by
    rw [List.mem_singleton] at hr'; subst hr'
    rw [lim_other (by decide) (by decide) (by decide)] at hd; omega)
  have hBa : EnvOK a stB := envOK_skeep ka (by decide) hB
  have hacca : AccSt a acc := accSt_skeep ka (by decide) hacc
  refine WP.ite (decide (FastNaf.magnitude 9 u j = 0)) az (fun hz => ?_) (fun hnz => ?_)
  · have hz' : FastNaf.magnitude 9 u j = 0 := of_decide_eq_true hz
    refine WP.block_nil ⟨ca, hca, hBa, ?_, la⟩
    simp only [gNext, hz', ↓reduceIte]
    exact hacca
  · have hnz' : ¬FastNaf.magnitude 9 u j = 0 := of_decide_eq_false hnz
    have e9 : FastNaf.magnitude 9 u j = FastNaf9.magnitude u j := by
      simp only [FastNaf.magnitude, FastNaf.ne_9_7, ↓reduceIte]
    have en : FastNaf.negative 9 u j = FastNaf9.negative u j := by
      simp only [FastNaf.negative, FastNaf.ne_9_7, ↓reduceIte]
    have em : gMag (FastNaf.word u j) = FastNaf.magnitude 9 u j := by
      rw [e9]; exact FastNaf9.word_magnitude u j
    have hl : FastNaf.magnitude 9 u j ≤ 255 := by rw [e9]; exact FastNaf9.magnitude_le u j
    have ho : FastNaf.magnitude 9 u j % 2 = 1 := by
      rw [e9] at hnz' ⊢; exact (FastNaf9.magnitude_odd_or_zero u j).resolve_left hnz'
    have hrow := ca.external (FastNaf.magnitude 9 u j) (by omega) (by rw [jointGTop, ite_eq_left h9]; exact hl) ho
    have hGa := hG.lkeep la
    have eo : 16 * c.K.M.n * (FastNaf.magnitude 9 u j - 1) = 64 * (FastNaf.magnitude 9 u j - 1) := by rw [hn]
    have key : ∀ (n : Nat) (_ : n = 4) (P : Addr) (d d' w : Nat), d = d' → wordsVal a.mem P d n = w →
        toM pN (2 ^ 256) (wordsVal a.mem P d' 4) = toM Cv.p (2 ^ (64 * n)) w := by
      intro n hn' P d d' w hd hw
      subst hn' hd hw
      rfl
    have xv := hrow.xval
    have yv := hrow.yval
    rw [eo] at xv yv
    refine WP.mono_syms (gDigit_ok hn hca hBa a8' hrow.symbol (by rw [em]; omega) (fun d hd => ?_)
      (x := toM Cv.p (2 ^ (64 * c.K.M.n)) (row.x (FastNaf.magnitude 9 u j)))
      (y := toM Cv.p (2 ^ (64 * c.K.M.n)) (row.y (FastNaf.magnitude 9 u j)))
      (by rw [em]; exact key _ hn _ _ _ _ rfl xv) (by rw [em]; exact key _ hn _ _ _ _ (by rw [hn]) yv) hacca)
      fun t ⟨hct, hBt, hat, kt⟩ st => ?_
    · rw [em]
      obtain ⟨r, hr, hreg⟩ := hGa.1
      simp only [off, Offset.add_add]
      refine ⟨⟨r, hr, Region.contains_off hreg (by omega)⟩, fun x hx hy => ?_⟩
      have ho := hGa.2 (64 * (FastNaf.magnitude 9 u j - 1) + d + (x - (T + BitVec.ofNat 64
        (64 * (FastNaf.magnitude 9 u j - 1) + d))).toNat) (by omega)
      rw [← Offset.add_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel] at ho
      rw [ka.gpr .rdi (by decide), hdi] at hy
      simp only [Offset.sub_add_eq, Offset.toNat_sub_ofNat] at hy
      have := (x - base).isLt
      simp only [ofs] at ho
      omega
    refine ⟨jointCore_lkeep hV ca kt st, hct, hBt, ?_, la.trans kt⟩
    simp only [gNext, hnz', ↓reduceIte]
    rw [gNeg, show FastNaf.word u j = FastNaf9.word u j from rfl, FastNaf9.word_negative u j, ← en] at hat
    exact hat


/-! ### A digit of each scalar -/

theorem point_zero {P : Point Cv} {w k j : Nat} (h : FastNaf.magnitude w k j = 0) :
    FastNaf.point Cv P w k j = .infinity := by
  have h0 : Spec.Weierstrass.mul 0 P = .infinity := by rw [Spec.Weierstrass.mul]; rfl
  rw [FastNaf.point, h, h0]
  split <;> rfl

/-- The table of the odd multiples of `Q`, as the field elements `E` of its slots. -/
def QTab (c : Joint.Cfg) (E : Nat → Fe Cv) (Q : Point Cv) : Prop :=
  ∀ a, 1 ≤ a → a ≤ 8 → InvJ Cv (E (c.K.tblPt a).x) (E (c.K.tblPt a).y) (E (c.K.tblPt a).z)
    (Spec.Weierstrass.mul (2 * a - 1) Q)

theorem accPt_qNext (hC : Law Cv) (ha : AM3 Cv) {c : Joint.Cfg} {E : Nat → Fe Cv} {v : Nat} {Q A : Point Cv}
    (hT : QTab c E Q) (hQ : onCurve Cv Q = true) (hA : onCurve Cv A = true)
    {acc : Option (Fin pN × Fin pN × Fin pN)} (hacc : AccPt acc A) (j : Nat) :
    AccPt (qNext c E v j acc) (Spec.Weierstrass.add A (FastNaf.point Cv Q 5 v j)) := by
  unfold qNext
  split
  · rename_i hz
    rw [point_zero ((FastNaf.byte_zero_iff 5 v j).mp hz), add_infinity]
    exact hacc
  · rename_i hz
    have hmag : FastNaf.magnitude 5 v j ≠ 0 := fun he => hz ((FastNaf.byte_zero_iff 5 v j).mpr he)
    have hl := FastNaf.magnitude_le (Or.inl rfl) v j
    have ho := (FastNaf.magnitude_odd_or_zero 5 v j).resolve_left hmag
    have ht := hT ((FastNaf.magnitude 5 v j - 1) / 2 + 1) (by omega) (by omega)
    rw [show 2 * ((FastNaf.magnitude 5 v j - 1) / 2 + 1) - 1 = FastNaf.magnitude 5 v j by omega] at ht
    exact accPt_step hC ha (FastNaf.negative 5 v j) hA (hC.onCurve_mul hQ _) hacc ht

theorem accPt_gNext (hC : Law Cv) (ha : AM3 Cv) {c : Joint.Cfg} {G A : Point Cv}
    (row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)) (h9 : c.gw = 9) (hG : onCurve Cv G = true)
    (hA : onCurve Cv A = true) {acc : Option (Fin pN × Fin pN × Fin pN)} (hacc : AccPt acc A) (u j : Nat) :
    AccPt (gNext c row u j acc) (Spec.Weierstrass.add A (FastNaf.point Cv G 9 u j)) := by
  unfold gNext
  split
  · rename_i hz
    rw [point_zero hz, add_infinity]
    exact hacc
  · rename_i hz
    have e9 : FastNaf.magnitude 9 u j = FastNaf9.magnitude u j := by
      simp only [FastNaf.magnitude, FastNaf.ne_9_7, ↓reduceIte]
    have hl : FastNaf.magnitude 9 u j ≤ 255 := by rw [e9]; exact FastNaf9.magnitude_le u j
    have ho : FastNaf.magnitude 9 u j % 2 = 1 := by
      rw [e9] at hz ⊢; exact (FastNaf9.magnitude_odd_or_zero u j).resolve_left hz
    have hp := row.point (FastNaf.magnitude 9 u j) (by omega) (by rw [jointGTop, ite_eq_left h9]; exact hl) ho
    exact accPt_step hC ha (FastNaf.negative 9 u j) hA (hC.onCurve_mul hG _) hacc hp

/-- The accumulator after digit `j` of both scalars. -/
def stepAcc (c : Joint.Cfg) {G : Point Cv} (row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)) (E : Nat → Fe Cv)
    (u v j : Nat) (acc : Option (Fin pN × Fin pN × Fin pN)) : Option (Fin pN × Fin pN × Fin pN) :=
  gNext c row u j (qNext c E v j (accDbl acc))

/-- The accumulator after the `k` digits from the top of both scalars. -/
def accN (c : Joint.Cfg) {G : Point Cv} (row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)) (E : Nat → Fe Cv)
    (u v : Nat) : Nat → Option (Fin pN × Fin pN × Fin pN)
  | 0 => none
  | k + 1 => stepAcc c row E u v (256 - k) (accN c row E u v k)

/-- The accumulator stands for the sum of the digits so far, or its `z` is zero. -/
theorem accN_pt (hC : Law Cv) (ha : AM3 Cv) {c : Joint.Cfg} {G Q : Point Cv}
    (row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)) {E : Nat → Fe Cv} {u v : Nat} (h9 : c.gw = 9)
    (hT : QTab c E Q) (hG : onCurve Cv G = true) (hQ : onCurve Cv Q = true) (hu : u < 2 ^ 256) (hv : v < 2 ^ 256) :
    ∀ k, k ≤ 257 → AccPt (accN c row E u v k) (jointPoint G Q u v (257 - k) 9)
  | 0, _ => jointPoint_top G Q hu hv 9
  | k + 1, hk => by
    have ih := accN_pt hC ha row h9 hT hG hQ hu hv k (by omega)
    have hA := jointPoint_curve hC hG hQ u v (257 - k) 9
    have e : 257 - k = 256 - k + 1 := by omega
    rw [e] at ih hA
    have h1 := accPt_qNext hC ha (v := v) hT hQ (hC.onCurve_add hA hA) (accPt_dbl hC ha hA ih) (256 - k)
    have h2 := accPt_gNext hC ha row h9 hG
      (hC.onCurve_add (hC.onCurve_add hA hA) (FastNaf.onCurve_point hC hQ 5 v (256 - k))) h1 u (256 - k)
    rw [jointPoint_step hC hG hQ u v (256 - k) 9] at h2
    rw [show 257 - (k + 1) = 256 - k by omega]
    exact h2

/-- The slots of the table of `Q`'s odd multiples are among those the invariant has the values of. -/
theorem qNext_congr {c : Joint.Cfg} {E E' : Nat → Fe Cv} (h : ∀ x ∈ jointLive c, E x = E' x) (v j : Nat)
    (acc : Option (Fin pN × Fin pN × Fin pN)) : qNext c E v j acc = qNext c E' v j acc := by
  unfold qNext
  split
  · rfl
  · rename_i hz
    have hmag : FastNaf.magnitude 5 v j ≠ 0 := fun he => hz ((FastNaf.byte_zero_iff 5 v j).mpr he)
    have hl := FastNaf.magnitude_le (Or.inl rfl) v j
    have hm (x : Nat) (hx : x ∈ jacCoords (c.K.tblPt ((FastNaf.magnitude 5 v j - 1) / 2 + 1))) :
        x ∈ jointLive c := jointStable_live c x (jointStable_table c (by omega) (by omega) hx)
    rw [h _ (hm _ (by simp [jacCoords])), h _ (hm _ (by simp [jacCoords])), h _ (hm _ (by simp [jacCoords]))]

/-- The loop's invariant before digit `j - 1`: the joint multiplication's, with `R` still `O` and the
field elements `E` in its slots; the accumulator `acc` in the vectors. -/
structure VInv (c : Joint.Cfg) (base T K : Addr) (size u v : Nat) {G : Point Cv} (Q : Point Cv)
    (row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)) (E : Nat → Fe Cv) (j : Nat)
    (acc : Option (Fin pN × Fin pN × Fin pN)) (t : State) : Prop where
  core : JointCore c Cv base size Q u v (JointGenerator c Cv base T size row) .infinity t
  live : ∀ x ∈ jointLive c, tmv Cv c.K.M.n base t x = E x
  gtab : GTab base T size t
  ctx : Ctx par t
  env : EnvOK t stB
  acc : AccSt t acc
  rbx : t.gpr .rbx = BitVec.ofNat 64 j
  k : t.gpr .r10 = K

/-- The field elements of the joint multiplication's slots are kept by the loop's code. -/
theorem live_vkeep {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v : Nat} {G Q A : Point C}
    {row : JointGeneratorRow c.K.M.n C G (jointGTop c)} {s t : State} (hV : VLay c size)
    (h : JointCore c C base size Q u v (JointGenerator c C base T size row) A s) (k : VKeep s t) :
    ∀ x ∈ jointLive c, tmv C c.K.M.n base t x = tmv C c.K.M.n base s x := by
  have hnw := h.field.scr.nowrap
  have hu : Unch base vW s.mem t.mem := by
    have := k.mem
    rw [h.field.scr.rdi] at this
    exact this.mono (by decide)
  have st : Scr t base size := ⟨(k.gpr .rdi (by decide)).trans h.field.scr.rdi, k.wr ▸ h.field.scr.wr, hnw⟩
  exact (Inv.of_unch h.field st hu hV.liveB hV.live hV.mo).val

/-- The invariant after code that keeps what the loop keeps. -/
theorem VInv.vkeep {c : Joint.Cfg} {base T K : Addr} {size u v j j' : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}
    {acc acc' : Option (Fin pN × Fin pN × Fin pN)} {s t : State} (hV : VLay c size)
    (h : VInv c base T K size u v Q row E j acc s) (k : VKeep s t) (hs : t.syms = s.syms) (hc : Ctx par t)
    (hB : EnvOK t stB) (ha : AccSt t acc') (hb : t.gpr .rbx = BitVec.ofNat 64 j')
    (h10 : t.gpr .r10 = s.gpr .r10) : VInv c base T K size u v Q row E j' acc' t :=
  ⟨jointCore_vkeep hV h.core k hs, fun x hx => (live_vkeep hV h.core k x hx).trans (h.live x hx),
    h.gtab.vkeep k, hc, hB, ha, hb, h10.trans h.k⟩

/-- The invariant after scalar code that keeps the registers the blocks read through. -/
theorem VInv.skeep {c : Joint.Cfg} {base T K : Addr} {size u v j : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}
    {acc : Option (Fin pN × Fin pN × Fin pN)} {s t : State} (hV : VLay c size)
    (h : VInv c base T K size u v Q row E j acc s) {rs : List Reg} (k : SKeep rs s t) (hs : t.syms = s.syms)
    (hr : (rs.all fun r => [Reg.rax, .rbp, .r8].contains r) = true := by decide) :
    VInv c base T K size u v Q row E j acc t := by
  have hin : ∀ r ∈ rs, r ∈ [Reg.rax, .rbp, .r8] := fun r hr' =>
    List.contains_iff_mem.mp (List.all_eq_true.mp hr r hr')
  have hno : ∀ r, r ∉ [Reg.rax, .rbp, .r8] → r ∉ rs := fun r h' h'' => h' (hin r h'')
  have k' := k.mono hin
  refine h.vkeep hV (.of_skeep k') hs (ctx_skeep h.ctx k (hno _ (by decide)) (hno _ (by decide))
    (fun r d hr' hd => ?_)) (envOK_skeep k (hno _ (by decide)) h.env) (accSt_skeep k (hno _ (by decide)) h.acc)
    ((k.gpr .rbx (hno _ (by decide))).trans h.rbx) (k.gpr .r10 (hno _ (by decide)))
  have hm := hin r hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rw [lim_other (by rcases hm with h | h | h <;> simp [h]) (by rcases hm with h | h | h <;> simp [h])
    (by rcases hm with h | h | h <;> simp [h])] at hd
  omega

/-- The counter, and the accumulator doubled if it is set. -/
theorem vhead_ok {c : Joint.Cfg} {base T K : Addr} {size u v j : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}
    {acc : Option (Fin pN × Fin pN × Fin pN)} {s : State} (hV : VLay c size) (hj : j < 257)
    (h : VInv c base T K size u v Q row E (j + 1) acc s) :
    WP isa (.seq (.block [.alu .sub .rbx (.imm 1), .alu .test .r11 (.reg .r11)])
      (.ite .e (.block []) (.block dblPieces.flatten))) s fun t =>
      VInv c base T K size u v Q row E j (accDbl acc) t ∧ VKeep s t := by
  apply WP.seq
  show WP isa (.block ([.alu .sub .rbx (.imm 1)] ++ [.alu .test .r11 (.reg .r11)])) s _
  rw [WP.block_append_iff]
  refine WP.mono_syms (WP.skeep rfl (decRbx_ok s (by omega) (by omega) h.rbx)) fun a ⟨ab, ka⟩ sa => ?_
  rw [Nat.add_sub_cancel] at ab
  have va : VKeep s a := .of_skeep ka
  have ia : VInv c base T K size u v Q row E j acc a := h.vkeep hV va sa
    (ctx_skeep h.ctx ka (by decide) (by decide) (fun r d hr' hd => by
      rw [List.mem_singleton] at hr'; subst hr'
      rw [lim_other (by decide) (by decide) (by decide)] at hd; omega))
    (envOK_skeep ka (by decide) h.env) (accSt_skeep ka (by decide) h.acc) ab (ka.gpr .r10 (by decide))
  refine WP.mono_syms (WP.skeep rfl (test_ok a .r11)) fun b ⟨bz, kb⟩ sb => ?_
  have vb : VKeep a b := .of_skeep kb
  have ib : VInv c base T K size u v Q row E j acc b := ia.skeep hV kb sb
  cases acc with
  | none =>
    have h0 : a.gpr .r11 = 0 := ia.acc
    exact WP.ite true (by show b.zf = _; rw [bz, h0]; rfl)
      (fun _ => WP.block_nil ⟨ib, va.trans vb⟩) (fun h => nomatch h)
  | some x =>
    refine WP.ite false (by show b.zf = _; rw [bz, ia.acc.1]; rfl) (fun h => nomatch h) (fun _ => ?_)
    refine WP.mono_syms (dbl_ok ib.ctx ib.env ib.acc.2) fun d ⟨hcd, kd, hBd, had⟩ sd => ?_
    have vd : VKeep b d := .of_lkeep (.of_kept kd)
    exact ⟨ib.vkeep hV vd sd hcd hBd ⟨by rw [kd.gpr]; exact ib.acc.1, had⟩ (by rw [kd.gpr]; exact ib.rbx)
      (by rw [kd.gpr]), (va.trans vb).trans vd⟩

/-- A digit of `Q`'s scalar, read. -/
theorem vqRead_ok {c : Joint.Cfg} {base T K : Addr} {size u v j : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}
    {acc : Option (Fin pN × Fin pN × Fin pN)} {s : State} (hV : VLay c size) (hj : j < 257)
    (h : VInv c base T K size u v Q row E j acc s) :
    WP isa (.block (Naf.digitRead c.K)) s fun t =>
      VInv c base T K size u v Q row E j acc t ∧ t.gpr .r8 = (FastNaf.byte 5 v j).setWidth 64 ∧
        t.zf = some (decide (FastNaf.byte 5 v j = 0)) := by
  have hn := hV.n
  have hbytes : c.K.bits + j < size := by
    have := hV.stableB (c.K.bits, 64 * c.K.M.n + 1) (by simp [jointStableRanges])
    rw [hn] at this
    dsimp only at this
    omega
  have hr := WP.mono (nafRead_ok h.core.field.scr hbytes h.rbx (h.core.stable.peer j (by rw [hn]; omega)))
    fun t (x : t.gpr .r8 = (FastNaf.byte 5 v j).setWidth 64 ∧ t.zf = some (decide (FastNaf.byte 5 v j = 0)) ∧
      VG.Proof.X25519.X86_64.Keeps [.r8] s t) =>
      (⟨⟨x.1, x.2.1⟩, x.2.2⟩ : (t.gpr .r8 = (FastNaf.byte 5 v j).setWidth 64 ∧
        t.zf = some (decide (FastNaf.byte 5 v j = 0))) ∧ VG.Proof.X25519.X86_64.Keeps [.r8] s t)
  exact WP.mono_syms (WP.skeep rfl hr) fun a ⟨⟨a8, az⟩, ka⟩ sa => ⟨h.skeep hV ka sa, a8, az⟩

/-- A digit of `Q`'s scalar. -/
theorem vq_ok {c : Joint.Cfg} {base T K : Addr} {size u v j : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}
    {acc : Option (Fin pN × Fin pN × Fin pN)} {s : State} (hV : VLay c size) (hj : j < 257)
    (h : VInv c base T K size u v Q row E j acc s) :
    WP isa (qPass c) s fun t => VInv c base T K size u v Q row E j (qNext c E v j acc) t ∧ VKeep s t := by
  refine WP.mono_syms (qPass_ok hV h.core h.ctx h.env hj h.rbx h.acc) fun t ⟨_, hct, hBt, hat, kt⟩ st => ?_
  rw [qNext_congr h.live] at hat
  exact ⟨h.vkeep hV (.of_lkeep kt) st hct hBt hat ((kt.gpr .rbx (by decide)).trans h.rbx) (kt.gpr .r10 (by decide)),
    .of_lkeep kt⟩

/-- A digit of the generator's scalar, read. -/
theorem vgRead_ok {c : Joint.Cfg} {base T K : Addr} {size u v j : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}
    {acc : Option (Fin pN × Fin pN × Fin pN)} {s : State} (hV : VLay c size) (hL : JointLayout c size)
    (h9 : c.gw = 9) (hj : j < 257) (h : VInv c base T K size u v Q row E j acc s) :
    WP isa (.block (Joint.fixedRead c)) s fun t =>
      VInv c base T K size u v Q row E j acc t ∧ t.gpr .r8 = (FastNaf.word u j).setWidth 64 ∧
        t.zf = some (decide (FastNaf.magnitude 9 u j = 0)) := by
  have hn := hV.n
  have hr := WP.mono (jointFixedRead_ok hL h.core (by rw [hn]; omega) h.rbx)
    fun t (x : t.gpr .r8 = jointGCell c u j ∧ t.zf = some (decide (FastNaf.magnitude c.gw u j = 0)) ∧
      VG.Proof.X25519.X86_64.Keeps [.r8] s t) =>
      (⟨⟨x.1, x.2.1⟩, x.2.2⟩ : (t.gpr .r8 = jointGCell c u j ∧
        t.zf = some (decide (FastNaf.magnitude c.gw u j = 0))) ∧ VG.Proof.X25519.X86_64.Keeps [.r8] s t)
  refine WP.mono_syms (WP.skeep (by rw [Joint.fixedRead, ite_eq_left h9]; rfl) hr) fun a ⟨⟨a8, az⟩, ka⟩ sa => ?_
  rw [h9] at az
  exact ⟨h.skeep hV ka sa, by rw [a8, jointGCell, ite_eq_left h9], az⟩

/-- A digit of the generator's scalar. -/
theorem vg_ok {c : Joint.Cfg} {base T K : Addr} {size u v j : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}
    {acc : Option (Fin pN × Fin pN × Fin pN)} {s : State} (hV : VLay c size) (hL : JointLayout c size)
    (h9 : c.gw = 9) (hj : j < 257) (h : VInv c base T K size u v Q row E j acc s) :
    WP isa (gPass c) s fun t => VInv c base T K size u v Q row E j (gNext c row u j acc) t ∧ VKeep s t := by
  refine WP.mono_syms (gPass_ok hV hL h9 h.core h.gtab h.ctx h.env hj h.rbx h.acc)
    fun t ⟨_, hct, hBt, hat, kt⟩ st => ?_
  exact ⟨h.vkeep hV (.of_lkeep kt) st hct hBt hat ((kt.gpr .rbx (by decide)).trans h.rbx) (kt.gpr .r10 (by decide)),
    .of_lkeep kt⟩

/-- The loop's condition. -/
theorem vtail_ok {c : Joint.Cfg} {base T K : Addr} {size u v j : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}
    {acc : Option (Fin pN × Fin pN × Fin pN)} {s : State} (hV : VLay c size) (hj : j < 257)
    (h : VInv c base T K size u v Q row E j acc s) :
    WP isa (.block [.alu .test .rbx (.reg .rbx)]) s fun t =>
      (VInv c base T K size u v Q row E j acc t ∧ t.zf = some (decide (j = 0))) ∧ VKeep s t :=
  WP.mono_syms (WP.skeep rfl (testRbx_ok s (by omega) h.rbx)) fun _ ⟨tz, kt⟩ st =>
    ⟨⟨h.skeep hV kt st, tz⟩, .of_skeep kt⟩

/-- A digit of each scalar. -/
theorem vstep_ok {c : Joint.Cfg} {base T K : Addr} {size u v j : Nat} {G Q : Point Cv}
    {row : JointGeneratorRow c.K.M.n Cv G (jointGTop c)} {E : Nat → Fe Cv}
    {acc : Option (Fin pN × Fin pN × Fin pN)} {s : State} (hV : VLay c size) (hL : JointLayout c size)
    (h9 : c.gw = 9) (hj : j < 257) (h : VInv c base T K size u v Q row E (j + 1) acc s) :
    WP isa (vstep c) s fun t =>
      (VInv c base T K size u v Q row E j (stepAcc c row E u v j acc) t ∧ t.zf = some (decide (j = 0))) ∧
        VKeep s t := by
  rw [vstep]
  apply WP.assoc
  apply WP.seq
  refine WP.mono (vhead_ok hV hj h) fun a ⟨ia, ka⟩ => ?_
  apply WP.seq
  refine WP.mono (vq_ok hV hj ia) fun b ⟨ib, kb⟩ => ?_
  apply WP.seq
  refine WP.mono (vg_ok hV hL h9 hj ib) fun d ⟨id, kd⟩ => ?_
  exact WP.mono (vtail_ok hV hj id) fun t ⟨it, kt⟩ => ⟨it, ((ka.trans kb).trans kd).trans kt⟩

end VG.Proof.P256.X86_64.Ifma
