module

import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlKem.X86.SampleSetup
public import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.MlKem.X86.SampleSetup
meta import VerifiedGarbage.Proof.MlKem.KPke

/-! ### `MlKem.X86.SampleLoop`, which only this module used -/

section

/-! ### `MlKem.X86.SampleCalls`, which only this module used -/

section

/-!
# ML-KEM on x86 (32-bit): the Keccak calls of `vg_mlkem_sample_ntt`

From the all-zero state (`Z`), absorbing the seed (`absorb_call`), padding for
SHAKE128 (`pad_call`) and squeezing 840 bytes into `scratch` (`squeeze_call`)
leaves the first 840 bytes of the XOF output of the seed there (`Out`). Each
call's arguments are set by a block (`absArgs_piece`, `padArgs_piece`,
`sqArgs_piece`) from `esi = scratch` and the seed pointer on the stack.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Proof.Sha3.X86 (reg32)
open VG.Spec.Sha3 (bytesAt stateAt Repr squeezeFrom shakeSuffix)

/-! ## Absorbing the seed -/

theorem absArgs_piece : Piece Pre Pub Z (fun s₀ s => Z s₀ s ∧ AbsArgs s (SS s₀) (dP s₀) (WW s₀) 168 0 34)
    (.block smpAbsorbArgs) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have a₀ := h.argEa (i := 0)
    have i₀ := h.argIn hp (i := 0) (by omega_using [])
    have v₀ := h.argw hp (i := 0) (by omega_using [])
    simp only [Nat.mul_zero, Nat.add_zero] at a₀
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, smpAbsorbArgs, smpSt, smpWk, at_, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.ea, State.load32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a₀, i₀, v₀, Option.some.injEq, exists_eq_left']
    exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, by simp [h.esi]⟩, h.st⟩,
      ⟨by simp [h.esi], rfl, rfl, rfl, rfl, by simp [h.esi]⟩⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.E1]

/-- `Ctx`, with the seed absorbed. -/
structure A1 (s₀ s : State) : Prop extends Ctx s₀ s where
  st : Repr s.mem ((SS s₀).setWidth 64) 168 (Bs s₀)

theorem absorb_call : Piece Pre Pub (fun s₀ s => Z s₀ s ∧ AbsArgs s (SS s₀) (dP s₀) (WW s₀) 168 0 34) A1
    (callWith rs6 "vg_keccak_absorb_scratch" Impl.Sha3.X86.Stream.absorb) := by
  refine absorb_piece E1 SS dP WW 168 0 34 rate168 (by decide) (by decide) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, by rw [SS, SS, hq.2.2.2.2], hq.2.2.1, by rw [WW, WW, hq.2.2.2.2]⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr post => ?_)
  · have hk := hp.kbufs
    have hs := hp.s_fit
    refine ⟨h.esp, ha, hk, hp.d_fit, ?_, ?_, (hp.stk_d.sub_left hp.c_sub), ?_, hp.within_s h.wr (by omega_using []) (by omega_using []),
      hp.within_s h.wr (by omega_using []) (by omega_using [])⟩
    · rw [hp.reg_s (by omega_using [])]; exact hp.d_s.sub_right (hp.sub_s (by omega_using []))
    · rw [hp.reg_s (by omega_using [])]; exact hp.d_s.sub_right (hp.sub_s (by omega_using []))
    · refine ⟨dR s₀, ?_, 0, (BitVec.add_zero _).symm, Nat.le_refl _⟩
      rw [h.rd, h.wr, pushed_rd, hp.rd]; simp
  · refine ⟨h.toCtx.call e₁ e₂ e₃ fr (calls_sub3 hp), ?_⟩
    have := post [] (repr_nil h.st) (by simp)
    rwa [List.nil_append, h.seed hp] at this

/-! ## Padding -/

theorem padArgs_piece : Piece Pre Pub A1 (fun s₀ s => A1 s₀ s ∧ PadArgs s (SS s₀) (WW s₀) 168 34 0x1f)
    (.block smpPadArgs) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, smpPadArgs, smpSt, smpWk, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, by simp [h.esi]⟩, h.st⟩,
    ⟨by simp [h.esi], rfl, rfl, rfl, by simp [h.esi]⟩⟩

/-- `Ctx`, with the seed absorbed and padded for SHAKE128. -/
structure A2 (s₀ s : State) : Prop extends Ctx s₀ s where
  st : stateAt s.mem ((SS s₀).setWidth 64) = padded 168 shakeSuffix (Bs s₀)

theorem pad_call : Piece Pre Pub (fun s₀ s => A1 s₀ s ∧ PadArgs s (SS s₀) (WW s₀) 168 34 0x1f) A2
    (callWith rs5 "vg_keccak_pad_scratch" Impl.Sha3.X86.Stream.pad) := by
  refine pad_piece E1 SS WW 168 34 0x1f rate168 (by decide) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, by rw [SS, SS, hq.2.2.2.2], by rw [WW, WW, hq.2.2.2.2]⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr post => ?_)
  · exact ⟨h.esp, ha, hp.kbufs, hp.within_s h.wr (by omega_using []) (by omega_using []), hp.within_s h.wr (by omega_using []) (by omega_using [])⟩
  · refine ⟨h.toCtx.call e₁ e₂ e₃ fr (calls_sub3 hp), ?_⟩
    have := post (Bs s₀) h.st (by rw [bytesAt_length])
    rwa [show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32] at this

/-! ## Squeezing -/

theorem sqArgs_piece : Piece Pre Pub A2 (fun s₀ s => A2 s₀ s ∧ AbsArgs s (SS s₀) (sP s₀) (WW s₀) 168 0 840)
    (.block smpSqueezeArgs) := by
  refine Piece.taint [] (fun s₀ s hp h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, smpSqueezeArgs, smpSt, smpWk, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, by simp [h.esi]⟩, h.st⟩,
    ⟨by simp [h.esi], rfl, rfl, by simp [h.esi], rfl, by simp [h.esi]⟩⟩

/-- `Ctx`, with the first 840 bytes of the XOF output of the seed at `scratch`. -/
structure Out (s₀ s : State) : Prop extends Ctx s₀ s where
  out : ∀ p < 840, s.mem (sA s₀ + BitVec.ofNat 64 p) = xofByte (Bs s₀) p

theorem squeeze_call : Piece Pre Pub (fun s₀ s => A2 s₀ s ∧ AbsArgs s (SS s₀) (sP s₀) (WW s₀) 168 0 840) Out
    (callWith rs6 "vg_keccak_squeeze_scratch" Impl.Sha3.X86.Stream.squeeze) := by
  refine squeeze_piece E1 SS sP WW 168 0 840 rate168 (by decide) (by decide) (fun s₀ s hp ⟨h, ha⟩ => ?_)
    (fun s₀ s₀' _ _ hq => ⟨hq.E1, by rw [SS, SS, hq.2.2.2.2], hq.2.2.2.2, by rw [WW, WW, hq.2.2.2.2]⟩)
    (fun s₀ s s' hp ⟨h, _⟩ e₁ e₂ e₃ fr r₁ _ => ?_)
  · have hs := hp.s_fit
    refine ⟨h.esp, ha, hp.kbufs, by omega_using [hs], ?_, ?_, ?_, hp.within_s h.wr (by omega_using []) (by omega_using []),
      hp.within_s0 h.wr (by omega_using []), hp.within_s h.wr (by omega_using []) (by omega_using [])⟩
    · rw [hp.reg_s (by omega_using []), Pre.reg_s0]
      exact disj_at (len := 2048) (by omega_using []) (by omega_using []) hs (by omega_using [])
    · rw [hp.reg_s (by omega_using []), Pre.reg_s0]
      exact disj_at (len := 2048) (by omega_using []) (by omega_using []) hs (by omega_using [])
    · rw [Pre.reg_s0]
      exact (hp.stk_s.sub_left hp.c_sub).sub_right (hp.sub_s (by omega_using []))
  · refine ⟨h.toCtx.call e₁ e₂ e₃ fr (calls_sub hp), fun p hp' => ?_⟩
    rw [h.st] at r₁
    have e := bytesAt_getD s'.mem (sA s₀) (len := 840) hp'
    rw [r₁, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [VG.Proof.Sha3.length_squeezeFrom (by decide) (by decide)]; exact hp'),
      Option.getD_some, xof_squeezeFrom_getElem _ hp', Nat.zero_add] at e
    exact e.symm

end VG.Proof.MlKem.X86.Sample

end

end

/-!
# ML-KEM on x86 (32-bit): the loop of `vg_mlkem_sample_ntt`

After `t` iterations of the loop on the XOF output at `scratch`, the
coefficients accepted, `LA B t = sampleAfter [] (xofByte B) t`
(`Proof/MlKem/KPke.lean`), are at `a`, `edi` points after them and `ecx`
counts them (`Loop`). An iteration computes the candidates `d₁` in `eax` and
`d₂` in `ebx` (`chunk_ok`), and, while there are fewer than 256 coefficients,
accepts each that is less than `q` (`accept_piece`); its branches depend on
the XOF output, which is a function of the seed, and so agree in two runs from
the same seed.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

/-- The first candidate of chunk `t`. -/
abbrev d₁ (B : List Byte) (t : Nat) : Nat :=
  (xofByte B (3 * t)).toNat + 256 * ((xofByte B (3 * t + 1)).toNat % 16)

/-- The second candidate of chunk `t`. -/
abbrev d₂ (B : List Byte) (t : Nat) : Nat :=
  (xofByte B (3 * t + 1)).toNat / 16 + 16 * (xofByte B (3 * t + 2)).toNat

/-- The coefficients accepted after `t` iterations. -/
abbrev LA (B : List Byte) (t : Nat) : List Zq := sampleAfter [] (xofByte B) t

/-- `L`, with `v` accepted if it is less than `q`. -/
def acc (L : List Zq) (v : Nat) : List Zq := if v < q then L ++ [ofNat v] else L

/-- Coefficient `i` of `L`, as stored. -/
def cv (L : List Zq) (i : Nat) : BitVec 32 := BitVec.ofNat 32 (L.getD i 0).val

theorem d₁_lt (B : List Byte) (t : Nat) : d₁ B t < 2 ^ 12 := by
  have := (xofByte B (3 * t)).isLt
  have := Nat.mod_lt (xofByte B (3 * t + 1)).toNat (show 16 > 0 by decide)
  simp only [d₁]; omega_arith

theorem d₂_lt (B : List Byte) (t : Nat) : d₂ B t < 2 ^ 12 := by
  have := (xofByte B (3 * t + 1)).isLt
  have := (xofByte B (3 * t + 2)).isLt
  simp only [d₂]; omega_arith

theorem LA_else {B : List Byte} {t : Nat} (h : ¬ (LA B t).length < 256) : LA B t = LA B (t + 1) := by
  have := sampleAfter_length_le (a := []) (Nat.zero_le _) (xofByte B) t
  simp only [LA] at h ⊢
  rw [sampleAfter_succ, sampleStepCap_full (by rw [n_eq] at this ⊢; omega_arith)]

theorem step_eq (L : List Zq) (c₀ c₁ c₂ : Byte) :
    sampleStep L c₀ c₁ c₂ = (let L₁ := acc L (c₀.toNat + 256 * (c₁.toNat % 16))
      if L₁.length < 256 then acc L₁ (c₁.toNat / 16 + 16 * c₂.toNat) else L₁) := by
  unfold sampleStep acc
  generalize c₀.toNat + 256 * (c₁.toNat % 16) = x
  generalize c₁.toNat / 16 + 16 * c₂.toNat = y
  by_cases hx : x < q <;> by_cases hy : y < q <;> simp [hx, hy, n_eq]

theorem LA_step {B : List Byte} {t : Nat} (h : (LA B t).length < 256) :
    LA B (t + 1) = (if (acc (LA B t) (d₁ B t)).length < 256 then acc (acc (LA B t) (d₁ B t)) (d₂ B t)
      else acc (LA B t) (d₁ B t)) := by
  rw [LA, sampleAfter_succ, sampleStepCap, ite_eq_right (by rw [n_eq]; exact Nat.ne_of_lt h), step_eq]

theorem LA_then {B : List Byte} {t : Nat} (h : (LA B t).length < 256)
    (h₂ : (acc (LA B t) (d₁ B t)).length < 256) : acc (acc (LA B t) (d₁ B t)) (d₂ B t) = LA B (t + 1) := by
  rw [LA_step h, ite_eq_left h₂]

theorem LA_then' {B : List Byte} {t : Nat} (h : (LA B t).length < 256)
    (h₂ : ¬ (acc (LA B t) (d₁ B t)).length < 256) : acc (LA B t) (d₁ B t) = LA B (t + 1) := by
  rw [LA_step h, ite_eq_right h₂]

/-! ## The state of the loop -/

/-- After `t` iterations, with the coefficients `L` accepted. -/
structure Loop (s₀ : State) (t : Nat) (L : List Zq) (s : State) : Prop extends Base s₀ s where
  out : ∀ p < 840, s.mem (sA s₀ + BitVec.ofNat 64 p) = xofByte (Bs s₀) p
  esi : s.gpr .esi = sP s₀ + BitVec.ofNat 32 (3 * t)
  ebp : s.gpr .ebp = BitVec.ofNat 32 (280 - t)
  len : L.length ≤ 256
  edi : s.gpr .edi = aP s₀ + BitVec.ofNat 32 (4 * L.length)
  ecx : s.gpr .ecx = BitVec.ofNat 32 L.length
  coef : ∀ i < L.length, coeffAt s.mem (aA s₀) i = cv L i

/-- Within iteration `t`, with the second candidate in `ebx`. -/
structure Mid (s₀ : State) (t : Nat) (L : List Zq) (s : State) : Prop extends Loop s₀ t L s where
  ebx : s.gpr .ebx = BitVec.ofNat 32 (d₂ (Bs s₀) t)

theorem Mid.flags {s₀ s s' : State} {t : Nat} {L : List Zq} (h : Mid s₀ t L s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : Mid s₀ t L s' :=
  ⟨⟨⟨by rw [hg, h.esp], by rw [hr, h.rd], by rw [hw, h.wr], by rw [hm]; exact h.frame⟩,
    by rw [hm]; exact h.out, by rw [hg, h.esi], by rw [hg, h.ebp], h.len, by rw [hg, h.edi], by rw [hg, h.ecx],
    by rw [hm]; exact h.coef⟩, by rw [hg, h.ebx]⟩

theorem linit_piece : Piece Pre Pub Out (fun s₀ s => Loop s₀ 0 (LA (Bs s₀) 0) s) (.block smpLoopInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_)
    (by taint_decide)
  · have a₁ := h.argEa (i := 1)
    have i₁ := h.argIn hp (i := 1) (by omega_arith)
    have v₁ := h.argw hp (i := 1) (by omega_arith)
    simp only [Nat.mul_one, Nat.reduceAdd] at a₁
    apply WP.of_runBlock
    simp only [↓reduceIte, smpLoopInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₁, i₁, v₁, 
      Option.some.injEq, exists_eq_left']
    exact ⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], rfl, by simp [sampleAfter_zero],
      by simp [sampleAfter_zero], by simp [sampleAfter_zero], fun i hi => by simp [sampleAfter_zero] at hi⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [h.esp, h'.esp, hq.E1]

/-! ## The candidates -/

theorem chunk_ok {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < 280) {s : State}
    (h : Loop s₀ t (LA (Bs s₀) t) s) :
    WP isa (.block smpChunk) s fun s' => Mid s₀ t (LA (Bs s₀) t) s' ∧
      s'.gpr .eax = BitVec.ofNat 32 (d₁ (Bs s₀) t) ∧
      eval .b s' = some (decide ((LA (Bs s₀) t).length < 256)) := by
  have hs := hp.s_fit
  have eb : ∀ o < 3, (sP s₀ + BitVec.ofNat 32 (3 * t) + BitVec.ofNat 32 o).setWidth 64 =
      sA s₀ + BitVec.ofNat 64 (3 * t + o) := fun o ho => ea_add (by omega_arith)
  have e0 := eb 0 (by omega_arith)
  have e1 := eb 1 (by omega_arith)
  have e2 := eb 2 (by omega_arith)
  have inS : ∀ o < 3, InRegions (s.rd ++ s.wr) (sA s₀ + BitVec.ofNat 64 (3 * t + o)) 1 := fun o ho =>
    ⟨sR s₀, List.mem_append_right _ (by rw [h.wr, P0_wr, hp.wr]; simp), contains_at (by omega_arith) hs⟩
  have i0 := inS 0 (by omega_arith)
  have i1 := inS 1 (by omega_arith)
  have i2 := inS 2 (by omega_arith)
  have v0 := h.out (3 * t + 0) (by omega_arith)
  have v1 := h.out (3 * t + 1) (by omega_arith)
  have v2 := h.out (3 * t + 2) (by omega_arith)
  simp only [Nat.add_zero] at e0 i0 v0
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow, and_self, smpChunk, at_, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, readSrc, State.ea, State.load8, State.setReg, arithFlags, State.setFlags,
    Option.map_some, Option.bind_some, h.esi, e0, e1, e2, i0, i1, i2, v0, v1, v2, 
    Option.some.injEq, exists_eq_left']
  have x0 : (BitVec.setWidth 32 (xofByte (Bs s₀) (3 * t)) +
      (BitVec.setWidth 32 (xofByte (Bs s₀) (3 * t + 1)) &&& 15).rotateRight 24).toNat = d₁ (Bs s₀) t := by
    have l0 := (xofByte (Bs s₀) (3 * t)).isLt
    have l1 := (xofByte (Bs s₀) (3 * t + 1)).isLt
    have hm : (BitVec.setWidth 32 (xofByte (Bs s₀) (3 * t + 1)) &&& 15).toNat =
        (xofByte (Bs s₀) (3 * t + 1)).toNat % 16 := by
      rw [show (15 : BitVec 32) = BitVec.ofNat 32 (2 ^ 4 - 1) from rfl, toNat_and_mask _ _ (by decide),
        toNat_byte32]
    rw [BitVec.toNat_add, rotr_small _ (by decide) (by decide) (by rw [hm]; omega_arith), hm, toNat_byte32,
      Nat.mod_eq_of_lt (by omega_arith), d₁]
    omega_arith
  have x1 : (BitVec.setWidth 32 (xofByte (Bs s₀) (3 * t + 1)) >>> 4 +
      (BitVec.setWidth 32 (xofByte (Bs s₀) (3 * t + 2))).rotateRight 28).toNat = d₂ (Bs s₀) t := by
    have l1 := (xofByte (Bs s₀) (3 * t + 1)).isLt
    have l2 := (xofByte (Bs s₀) (3 * t + 2)).isLt
    rw [BitVec.toNat_add, rotr_small _ (by decide) (by decide) (by rw [toNat_byte32]; omega_arith), toNat_shr,
      toNat_byte32, toNat_byte32, Nat.mod_eq_of_lt (by omega_arith), d₂]
    omega_arith
  have hl := h.len
  refine ⟨⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, by simp [h.esi], by simp [h.ebp], h.len,
    by simp [h.edi], by simp [h.ecx], h.coef⟩, ?_⟩, ?_, ?_⟩
  · exact eq_ofNat_of_toNat x1
  · exact eq_ofNat_of_toNat x0
  · simp only [eval, h.ecx, toNat_ofNat32 (show (LA (Bs s₀) t).length < 2 ^ 32 by omega_arith)]
    rfl

theorem chunk_piece (t : Nat) (ht : t < 280) :
    Piece Pre Pub (fun s₀ s => Loop s₀ t (LA (Bs s₀) t) s) (fun s₀ s => Mid s₀ t (LA (Bs s₀) t) s ∧
      s.gpr .eax = BitVec.ofNat 32 (d₁ (Bs s₀) t) ∧
      eval .b s = some (decide ((LA (Bs s₀) t).length < 256))) (.block smpChunk) :=
  Piece.taint [.esi] (fun s₀ s hp h => chunk_ok hp ht h)
    (fun s₀ s₀' s s' _ _ hq h h' r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esi, h'.esi, hq.2.2.2.2]) (by taint_decide)

/-! ## Accepting a candidate -/

theorem cv_append (L : List Zq) (x : Zq) {i : Nat} (hi : i < L.length) : cv (L ++ [x]) i = cv L i := by
  simp only [cv, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem cv_last (L : List Zq) {v : Nat} (hv : v < q) : cv (L ++ [ofNat v]) L.length = BitVec.ofNat 32 v := by
  simp only [cv, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some, val_ofNat, Nat.mod_eq_of_lt hv]

theorem store_ok {s₀ : State} (hp : Pre s₀) {t : Nat} {L : List Zq} {r : Reg} {v : Nat} (hv : v < q)
    (hl : L.length < 256) {s : State} (h : Mid s₀ t L s) (hrv : s.gpr r = BitVec.ofNat 32 v) :
    WP isa (.block [.store (at_ .edi 0) r, .alu .add .edi (.imm 4), .alu .add .ecx (.imm 1)]) s
      fun s' => Mid s₀ t (L ++ [ofNat v]) s' := by
  have ha := hp.a_fit
  have hn : L.length < n := by rw [n_eq]; exact hl
  have ea : (aP s₀ + BitVec.ofNat 32 (4 * L.length) + BitVec.ofNat 32 0).setWidth 64 =
      coeffAddr (aA s₀) L.length := by
    rw [ea_add (by omega_arith)]; rfl
  have hin : InRegions s.wr (coeffAddr (aA s₀) L.length) 4 :=
    ⟨polyRegion (aA s₀), by rw [h.wr, P0_wr, hp.wr]; simp, coeff_contains _ hn⟩
  have fa : Frame [polyRegion (aA s₀)] s.mem (s.mem.writeW (coeffAddr (aA s₀) L.length) (BitVec.ofNat 32 v)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hn)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.ea, State.store32, State.setReg, arithFlags, State.setFlags, Option.bind_some, h.edi, ea, hin,
    hrv, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame.writeW (r := polyRegion (aA s₀)) (by simp) _
    (coeff_contains _ hn)⟩, fun p hp' => ?_, by simp [h.esi], by simp [h.ebp],
    (by simp only [List.length_append, List.length_singleton]; omega_arith), ?_, ?_, fun i hi => ?_⟩, by simp [h.ebx]⟩
  · exact (fa.bytes (R := ⟨sA s₀, 840⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.a_s.symm.sub_left (Region.sub_prefix (by decide))) (show 840 ≤ 2 ^ 64 by decide) hp').trans (h.out p hp')
  · simp only [ite_true, List.length_append, List.length_singleton]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ecx, List.length_append, List.length_singleton]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ofNat_add_ofNat]
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases e : i < L.length
    · rw [coeffAt_writeW_ne _ _ (by rw [n_eq]; omega_arith) hn (by omega_arith), cv_append _ _ e]; exact h.coef i e
    · rw [show i = L.length by omega_arith, coeffAt_writeW_self, cv_last _ hv]

/-- Accepting the candidate `v` in `r`: the coefficients `L` become `L' = acc L v`. -/
theorem accept_piece (t : Nat) (r : Reg) {A : State → State → Prop} (X : State → Prop)
    (L L' : List Byte → List Zq) (v : List Byte → Nat)
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → Mid s₀ t (L (Bs s₀)) s ∧ s.gpr r = BitVec.ofNat 32 (v (Bs s₀)) ∧
      v (Bs s₀) < 2 ^ 12 ∧ (L (Bs s₀)).length < 256 ∧ acc (L (Bs s₀)) (v (Bs s₀)) = L' (Bs s₀) ∧ X s₀)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr []) (.block [.alu .cmp r (.imm Q)]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr [.edi])
      (.block [.store (at_ .edi 0) r, .alu .add .edi (.imm 4), .alu .add .ecx (.imm 1)]) h₂).isSome = true) :
    Piece Pre Pub A (fun s₀ s => Mid s₀ t (L' (Bs s₀)) s ∧ X s₀) (smpAccept r) := by
  refine Piece.seq (B := fun s₀ s => Mid s₀ t (L (Bs s₀)) s ∧ s.gpr r = BitVec.ofNat 32 (v (Bs s₀)) ∧
      (L (Bs s₀)).length < 256 ∧ acc (L (Bs s₀)) (v (Bs s₀)) = L' (Bs s₀) ∧ X s₀ ∧
      eval .b s = some (decide (v (Bs s₀) < q))) ?_
    (Piece.ite (fun s₀ => decide (v (Bs s₀) < q)) (fun _ _ _ h => h.2.2.2.2.2)
      (fun s₀ s₀' _ _ hq => by rw [hq.2.1]) ?_ ?_)
  · refine Piece.taint [] (fun s₀ s hp ha => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) t₁
    obtain ⟨h, hv, hv', hl, he, hx⟩ := hA s₀ s hp ha
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨h.flags rfl rfl rfl rfl, hv, hl, he, hx, ?_⟩
    simp only [eval, hv, toNat_ofNat32 (show v (Bs s₀) < 2 ^ 32 by omega_arith)]
    rfl
  · refine Piece.taint [.edi] (fun s₀ s hp ⟨⟨h, hv, hl, he, hx, _⟩, hb⟩ => ?_)
      (fun s₀ s₀' s s' _ _ hq ⟨⟨h, _⟩, _⟩ ⟨⟨h', _⟩, _⟩ r hr => ?_) t₂
    · have hq : v (Bs s₀) < q := of_decide_eq_true hb
      rw [acc, ite_eq_left hq] at he
      exact (store_ok hp hq hl h hv).mono fun s' h' => ⟨he ▸ h', hx⟩
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.edi, h'.edi, hq.2.2.2.1, hq.2.1]
  · refine Piece.taint [] (fun s₀ s hp ⟨⟨h, _, _, he, hx, _⟩, hb⟩ => ?_)
      (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)
    have hq : ¬ v (Bs s₀) < q := of_decide_eq_false hb
    rw [acc, ite_eq_right hq] at he
    exact WP.block_nil_iff.mpr ⟨he ▸ h, hx⟩

theorem cmp_piece (t : Nat) (X : State → Prop) (L : List Byte → List Zq) :
    Piece Pre Pub (fun s₀ s => Mid s₀ t (L (Bs s₀)) s ∧ X s₀)
      (fun s₀ s => (Mid s₀ t (L (Bs s₀)) s ∧ X s₀) ∧ eval .b s = some (decide ((L (Bs s₀)).length < 256)))
      (.block [.alu .cmp .ecx (.imm 256)]) := by
  refine Piece.taint [] (fun s₀ s hp ⟨h, hx⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hl := h.len
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨h.flags rfl rfl rfl rfl, hx⟩, ?_⟩
  simp only [eval, h.ecx, toNat_ofNat32 (show (L (Bs s₀)).length < 2 ^ 32 by omega_arith)]
  rfl

theorem end_ok {s₀ : State} {t : Nat} (ht : t < 280) {L : List Zq} {s : State} (h : Mid s₀ t L s) :
    WP isa (.block [.alu .add .esi (.imm 3), .alu .sub .ebp (.imm 1)]) s
      fun s' => Loop s₀ (t + 1) L s' ∧ eval .ne s' = some (decide (t + 1 < 280)) := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨by simp [h.esp], h.rd, h.wr, h.frame⟩, h.out, ?_, ?_, h.len, by simp [h.edi], by simp [h.ecx],
    h.coef⟩, ?_⟩
  · simp only [ite_true, h.esi]
    rw [show (3 : BitVec 32) = BitVec.ofNat 32 3 from rfl, add_ofNat_add]; congr 2
  · simp only [ite_true, h.ebp]
    exact cnt_next ht
  · simp only [eval, h.ebp]
    exact cnt_ne ht (by omega_arith)

theorem nil_piece {A B : State → State → Prop} (h : ∀ s₀ s, Pre s₀ → A s₀ s → B s₀ s) :
    Piece Pre Pub A B (.block []) :=
  Piece.taint [] (fun s₀ s hp ha => WP.block_nil_iff.mpr (h s₀ s hp ha))
    (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp)) (by taint_decide)

/-! ## An iteration, and the loop -/

theorem body_piece (t : Nat) (ht : t < 280) :
    Piece Pre Pub (fun s₀ s => Loop s₀ t (LA (Bs s₀) t) s)
      (fun s₀ s => Loop s₀ (t + 1) (LA (Bs s₀) (t + 1)) s ∧ eval .ne s = some (decide (t + 1 < 280)))
      smpBody := by
  refine Piece.seq (chunk_piece t ht) (Piece.seq (B := fun s₀ s => Mid s₀ t (LA (Bs s₀) (t + 1)) s) ?_
    (Piece.taint [] (fun s₀ s _ h => end_ok ht h) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
      (by taint_decide)))
  refine Piece.ite (fun s₀ => decide ((LA (Bs s₀) t).length < 256)) (fun _ _ _ h => h.2.2)
    (fun s₀ s₀' _ _ hq => by rw [hq.2.1]) ?_ ?_
  · refine Piece.seq (accept_piece t .eax (fun s₀ => (LA (Bs s₀) t).length < 256) (fun B => LA B t)
      (fun B => acc (LA B t) (d₁ B t)) (fun B => d₁ B t)
      (fun s₀ s _ ⟨⟨h, he, _⟩, hb⟩ => ⟨h, he, d₁_lt _ _, of_decide_eq_true hb, rfl, of_decide_eq_true hb⟩)
      (by taint_decide) (by taint_decide)) ?_
    refine Piece.seq (cmp_piece t _ (fun B => acc (LA B t) (d₁ B t))) ?_
    refine Piece.ite (fun s₀ => decide ((acc (LA (Bs s₀) t) (d₁ (Bs s₀) t)).length < 256)) (fun _ _ _ h => h.2)
      (fun s₀ s₀' _ _ hq => by rw [hq.2.1]) ?_ ?_
    · exact (accept_piece t .ebx (fun _ => True) (fun B => acc (LA B t) (d₁ B t)) (fun B => LA B (t + 1))
        (fun B => d₂ B t) (fun s₀ s _ ⟨⟨⟨h, hx⟩, _⟩, hb⟩ =>
          ⟨h, h.ebx, d₂_lt _ _, of_decide_eq_true hb, LA_then hx (of_decide_eq_true hb), trivial⟩)
        (by taint_decide) (by taint_decide)).mono (fun _ _ _ h => h) fun _ _ _ h => h.1
    · exact nil_piece fun s₀ s _ ⟨⟨⟨h, hx⟩, _⟩, hb⟩ => LA_then' hx (of_decide_eq_false hb) ▸ h
  · exact nil_piece fun s₀ s _ ⟨⟨h, _⟩, hb⟩ => LA_else (of_decide_eq_false hb) ▸ h

theorem loop_piece : Piece Pre Pub (fun s₀ s => Loop s₀ 0 (LA (Bs s₀) 0) s)
    (fun s₀ s => Loop s₀ 280 (LA (Bs s₀) 280) s) (.loop smpBody .ne) :=
  Piece.loop (fun t s₀ s => Loop s₀ t (LA (Bs s₀) t) s) (by decide) fun t ht => body_piece t ht

/-- The end: 1 in `eax` if there are 256 coefficients, 0 if fewer. -/
structure Fin (s₀ s : State) : Prop extends Loop s₀ 280 (LA (Bs s₀) 280) s where
  eax : s.gpr .eax = BitVec.ofNat 32 ((LA (Bs s₀) 280).length / 256)

theorem fin_piece : Piece Pre Pub (fun s₀ s => Loop s₀ 280 (LA (Bs s₀) 280) s) Fin (.block smpEnd) := by
  refine Piece.taint [] (fun s₀ s _ h => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  have hl := h.len
  refine wp_movr (wp_shr (by decide) (by decide) fun s' o e => WP.block_nil_iff.mpr ?_)
  have g : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r := fun r hr => by
    rw [o.gpr r (by simp [hr])]; simp [State.setReg, hr]
  refine ⟨⟨⟨by rw [g _ (by decide), h.esp], by rw [o.rd]; exact h.rd, by rw [o.wr]; exact h.wr, by rw [o.mem]; exact h.frame⟩,
    by rw [o.mem]; exact h.out, by rw [g _ (by decide), h.esi], by rw [g _ (by decide), h.ebp], h.len,
    by rw [g _ (by decide), h.edi], by rw [g _ (by decide), h.ecx], by rw [o.mem]; exact h.coef⟩, ?_⟩
  rw [e]
  simp only [State.setReg, ite_true, h.ecx]
  exact eq_ofNat_of_toNat (by rw [toNat_shr, toNat_ofNat32 (show (LA (Bs s₀) 280).length < 2 ^ 32 by omega_arith)])

end VG.Proof.MlKem.X86.Sample

end

end

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_sample_ntt`

The body is the SHAKE128 output of the seed at `scratch` (`SampleSetup.lean`,
`SampleCalls.lean`), then the 280 iterations of the loop (`SampleLoop.lean`),
which leave `sampleAfter [] (xofByte B) 280` at `a` and return whether it has
256 coefficients; `sampleNTT_of_full`, `sampleNTT_none` and `outcome_of_min`
(`Proof/MlKem/KPke.lean`) give the contract. Two runs with the same pointers
and seed leak the same (`Pub`): the contract lets the function leak the seed.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86.Sample

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem main_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) Fin
    (.seq (.block [.mov .esi (.mem (at_ .esp 28))]) <|
      .seq (zeroSt smpSt) <|
      .seq (.block smpAbsorbArgs) <|
      .seq (callWith [.edi, .ebp, .ebx, .edx, .ecx, .eax] "vg_keccak_absorb_scratch" Impl.Sha3.X86.Stream.absorb) <|
      .seq (.block smpPadArgs) <|
      .seq (callWith [.edi, .ebx, .edx, .ecx, .eax] "vg_keccak_pad_scratch" Impl.Sha3.X86.Stream.pad) <|
      .seq (.block smpSqueezeArgs) <|
      .seq (callWith [.edi, .ebp, .ebx, .edx, .ecx, .eax] "vg_keccak_squeeze_scratch" Impl.Sha3.X86.Stream.squeeze) <|
      .seq (.block smpLoopInit) <|
      .seq (.loop smpBody .ne) (.block smpEnd)) :=
  Piece.seq ld_piece <| Piece.seq zero_piece <| Piece.seq absArgs_piece <| Piece.seq absorb_call <|
    Piece.seq padArgs_piece <| Piece.seq pad_call <| Piece.seq sqArgs_piece <| Piece.seq squeeze_call <|
    Piece.seq linit_piece <| Piece.seq loop_piece fin_piece

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlKem.X86.sampleNTT :=
  Piece.leaf W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨by have := hp.sp; omega_using [this], by have := hp.sp'; omega_using [this]⟩)
    (fun _ hp => hp.hW) (fun _ _ _ _ hq => hq.1)
    (main_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- The coefficients at `a`, when there are 256. -/
theorem poly_eq {s₀ s : State} (h : Loop s₀ 280 (LA (Bs s₀) 280) s) (hl : (LA (Bs s₀) 280).length = 256) :
    Reduced s.mem (aA s₀) ∧ polyAt s.mem (aA s₀) = toPoly (LA (Bs s₀) 280) := by
  have hc : ∀ i < n, coeffAt s.mem (aA s₀) i = cv (LA (Bs s₀) 280) i := fun i hi =>
    h.coef i (by rw [hl]; rw [n_eq] at hi; exact hi)
  have hv : ∀ i < n, (coeffAt s.mem (aA s₀) i).toNat = ((LA (Bs s₀) 280).getD i 0).val := fun i hi => by
    rw [hc i hi, cv, toNat_ofNat32 (by have := ((LA (Bs s₀) 280).getD i 0).isLt; have := q_eq; omega)]
  refine ⟨fun i hi => by rw [hv i hi]; exact ((LA (Bs s₀) 280).getD i 0).isLt, ?_⟩
  apply Vector.ext
  intro i hi
  simp only [polyAt, toPoly, Vector.getElem_ofFn]
  rw [hv i hi, ofNat_val]

/-- Memory with the arguments `0`, `0x100` and `0x1000` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 1 else if a = 0x500d then 0x10 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.sampleNTT (sampleNTTContract X86.abi 56) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of h) fun s s' _ _ h => ?_).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · sig_pub [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := h
    exact ⟨e₁, map_toNat_inj e₂, e₃, e₄, e₅⟩
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    obtain kA := leaf_keep hm ((Pre.of h₀).hW _ List.mem_cons_self).1 (by show 1024 ≤ 2 ^ 64; decide)
    rw [setWidth_append32, hax, hfin.eax, polyAt_congr kA]
    have hl := hfin.len
    by_cases e : (LA (Bs s₀) 280).length = 256
    · obtain ⟨hr, hp⟩ := poly_eq hfin.toLoop e
      rw [e]
      refine ⟨fun _ => reduced_congr kA hr, outcome_of_min (.inl ⟨rfl, ?_⟩)⟩
      rw [hp]
      exact sampleNTT_of_full (Nat.le_refl _) (by rw [n_eq]; exact e)
    · rw [Nat.div_eq_of_lt (by omega_using [hl, e])]
      refine ⟨fun h => absurd (congrArg BitVec.toNat h) (by show ¬ (0 = 1); decide), outcome_of_min (.inr ⟨rfl, ?_⟩)⟩
      exact sampleNTT_none (by rw [n_eq]; exact e)
  · let st := satState satMem [⟨0, 34⟩] [⟨0x100, 1024⟩, ⟨0x1000, 2048⟩, ⟨0x5004, 12⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [sampleNTTContract, sampleNTTSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlKem.X86.Sample
