module

import VerifiedGarbage.Proof.Dsa.X86.Generation.PPart
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
import VerifiedGarbage.Proof.Bignum.X86.LoadBE
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.OutsFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Rsa.X86.DivContext
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Dsa.X86.Generation.Base
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words

/-! # The generator's candidate `h` and its range check (A.2.1 steps 1–3) -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)
open VG.Impl.Mont.X86.Dynamic (chainW selectsW)

/-- `h` number `j`: its `pLen` bytes of the tape. -/
def hChunk (E : Env) (j : Nat) : List Byte := (E.hT.drop (j * E.pLen)).take E.pLen

theorem cmask_zf (c : Bool) : (cmask c - 0 == 0) = !c := by cases c <;> decide

theorem cmask_and (a b : Bool) : (cmask a &&& cmask b) = cmask (a && b) := by cases a <;> cases b <;> decide

/-- A borrow out of `a − b` is `a < b`. -/
theorem borrow_lt {o a b K : Nat} {c : Bool} (h : o + b = a + K * c.toNat) (ho : o < K) :
    c = decide (a < b) := by
  cases c <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h
  · exact (decide_eq_false (by omega)).symm
  · exact (decide_eq_true (by omega)).symm

/-- A change of memory that a helper call makes within ranges of `scratch`
and the call's stack. -/
theorem Env.Chg.of_stackOuts {E : Env} (v : E.Valid) {rs : List (Nat × Nat)} {m m' : Mem}
    (O : VG.Proof.Dsa.X86.StackOuts E.base E.sp rs m m') (fit : ∀ r ∈ rs, r.1 + r.2 ≤ E.size) :
    E.Chg rs m m' := by
  have nw := v.scratchFit
  intro x hx
  refine O x (fun r hr => ?_) (.inr fun hc => ?_)
  · have H := hx ⟨off E.base r.1, r.2⟩ (List.mem_append_left _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
    have I := Offset.lt_iff x E.base (show r.1 + r.2 ≤ 2 ^ 64 by have := fit r hr; omega)
    change ¬ ((x - off E.base r.1).toNat + 1 ≤ r.2) at H
    change (x - off E.base r.1).toNat < r.2 ↔ r.1 ≤ ofs E.base x ∧ ofs E.base x < r.1 + r.2 at I
    omega
  · exact hx E.stackRegion (List.mem_append_right _ (List.mem_singleton_self _))
      (below_sub (by decide : 108 ≤ 200) v.low x (show (below E.sp 108).Contains x 1 from hc))

/-- The range check's ranges: the temporary, `h` and the word of the first
borrow. -/
def rRanges : List (Nat × Nat) := [(aTmp, 400), (aH, 400), (fLo, 4)]

/-- After the range check of `h`: `h` in its array and ZF clear exactly when
`1 < h < p − 1`. -/
structure RangePost (E : Env) (g : Geo) (j p : Nat) (s t : State) : Prop where
  base : Base E t
  h : val32 t.mem E.base aH g.n32 = Spec.Dsa.decodeBE (hChunk E j)
  zf : isa.eval .e t = some (!decide (1 < Spec.Dsa.decodeBE (hChunk E j) ∧
    Spec.Dsa.decodeBE (hChunk E j) < p - 1))
  chg : E.Chg rRanges s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem rRanges_apart {E : Env} (v : E.Valid) : E.Apart rRanges := by
  have sz := v.size_ge
  intro o ho
  simp only [rRanges, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> simp only [aTmp, aH, arr, fLo, fOut, fWitLen, hdr] <;> omega

/-- The `pLen` bytes of `h` number `j` at its address in the tape. -/
theorem h_bytes {E : Env} {s : State} (B : Base E s) {j : Nat} (hj : (j + 1) * E.pLen ≤ E.hsLen) :
    Spec.Rsa.bytesAt s.mem (E.hs + BitVec.ofNat 64 (j * E.pLen)) E.pLen = hChunk E j := by
  rw [Nat.succ_mul] at hj
  simp only [hChunk, ← B.hs, Spec.Rsa.bytesAt]
  apply List.ext_getElem (by simp; omega)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
  rw [VG.Offset.add_add]

/-- `h` number `j` is loaded, and compared with 1 and `p − 1`. -/
theorem gRange_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) {s : State} (B : Base E s)
    {j p : Nat} (hj : (j + 1) * E.pLen ≤ E.hsLen)
    (hH : s.mem.readW (off E.base fH) 32 = (E.hs + BitVec.ofNat 64 (j * E.pLen)).setWidth 32)
    (hone : val32 s.mem E.base aOne g.n32 = 1) (hpm1 : val32 s.mem E.base aPm1 g.n32 = p - 1)
    {P : Prog isa} {Q : State → Prop} (k : ∀ t, RangePost E g j p s t → WP isa P t Q) :
    WP isa (.seq (.block [.mov .esi (.mem (sc fH)), .mov .ecx (.imm (BitVec.ofNat 32 g.pLen))])
      (.seq (VG.Impl.Bignum.X86.loadBE g.n64 aH) (.seq (chainW .sbb g.n32 aTmp aOne aH)
      (.seq (.block [.store (sc fLo) .ecx]) (.seq (chainW .sbb g.n32 aTmp aH aPm1)
      (.seq (.block [.alu .and .ecx (.mem (sc fLo)), .alu .cmp .ecx (.imm 0)]) P)))))) s Q := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have hf := v.hsFit
  have hl := v.ptrs.2.2.1
  have n64 : g.n64 = g.pLen / 8 := rfl
  have n32 : g.n32 = g.pLen / 4 := rfl
  have h2 : 2 * g.n64 = g.n32 := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, n32, h]
  have h8 : 8 * g.n64 = g.pLen := by
    rcases G.lengths with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> simp only [n64, h]
  have jq : j * E.pLen + E.pLen ≤ E.hsLen := by rw [Nat.succ_mul] at hj; omega_arith
  have hW : ((E.hs + BitVec.ofNat 64 (j * E.pLen)).setWidth 32).setWidth 64 = E.hs + BitVec.ofNat 64 (j * E.pLen) := by
    apply BitVec.eq_of_toNat_eq
    have e : (E.hs + BitVec.ofNat 64 (j * E.pLen)).toNat = E.hs.toNat + j * E.pLen := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j * E.pLen) (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]
    simp only [BitVec.toNat_setWidth, e]
    rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  have hN : ((E.hs + BitVec.ofNat 64 (j * E.pLen)).setWidth 32).toNat = E.hs.toNat + j * E.pLen := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j * E.pLen) (by omega_arith),
      Nat.mod_eq_of_lt (a := E.hs.toNat + j * E.pLen) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  -- `h`.
  refine WP.seq (ld_ok B.scr (d := fH) (by simp only [fH, hdr]; omega_arith) fun s₁ u₁ => wp_movi fun s₂ u₂ =>
    WP.block_nil ?_)
  have hs₂ : Scr s₂ E.base E.size := Scr.of_eq B.scr (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.wr, u₁.wr])
  have esi₂ : s₂.gpr .esi = (E.hs + BitVec.ofNat 64 (j * E.pLen)).setWidth 32 := by
    rw [u₂.other _ (by decide), u₁.gpr, hH]
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have K₂ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s s₂ :=
    ⟨fun r hr => by rw [u₂.other r (fun e => hr (e ▸ by simp)), u₁.other r (fun e => hr (e ▸ by simp))],
      by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  have sub : Region.Sub ⟨E.hs + BitVec.ofNat 64 (j * E.pLen), E.pLen⟩ E.hsRegion :=
    Offset.sub_base _ (show j * E.pLen + E.pLen ≤ E.hsLen by omega_arith)
  refine WP.seq (VG.X86.WP.mono_syms (VG.Proof.Bignum.X86.loadBE_ok hs₂ (n := g.n64) (out := aH) (len := g.pLen)
    (by omega_arith) (by simp only [aH, arr]; omega_arith) (by omega_arith) (by omega_arith) (by rw [esi₂, hN]; omega_arith) u₂.gpr
    (by rw [esi₂, VG.Proof.Bignum.X86.byteAddr, hW, u₂.rd, u₂.wr, u₁.rd, u₁.wr, ← hp]
        exact ⟨_, List.mem_append_left _ B.tapes.2.1, Offset.contains_base _ jq (by omega_arith)⟩)
    (by rw [esi₂, VG.Proof.Bignum.X86.byteAddr, hW, ← hp]
        exact ((v.tapesFar _ (by simp)).1.sub_left sub).sub_right (Offset.sub_base _ (by simp only [aH, arr]; omega_arith))))
    fun t₃ ⟨V₃, O₃, K₃⟩ sy₃ => ?_)
  rw [esi₂, VG.Proof.Bignum.X86.byteAddr, hW, m₂, ← hp, h_bytes B hj, wordsVal_eq_val32, h2,
    ← VG.Proof.Dsa.decodeBE_os2ip] at V₃
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  have one₃ : val32 t₃.mem E.base aOne g.n32 = 1 := by
    rw [O₃.val32 (by simp only [aH, aOne, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith), m₂, hone]
  have pm₃ : val32 t₃.mem E.base aPm1 g.n32 = p - 1 := by
    rw [O₃.val32 (by simp only [aH, aPm1, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), m₂, hpm1]
  -- `1 < h`.
  refine WP.seq (VG.X86.WP.mono_syms (chainSubW_ok hs₃ (k := g.n32) (o := aTmp) (a := aOne) (b := aH) (by omega_arith)
    (by simp only [aTmp, arr]; omega_arith) (by simp only [aOne, arr]; omega_arith) (by simp only [aH, arr]; omega_arith)
    (by simp only [aTmp, aOne, arr]; omega_arith) (by simp only [aTmp, aH, arr]; omega_arith)) fun t₄ ⟨O₄, ⟨c₄, e₄, E₄⟩, K₄⟩ sy₄ =>
    ?_)
  rw [one₃, V₃] at E₄
  have c₄v := borrow_lt E₄ (val32_lt _ _ _ _)
  have hs₄ := hs₃.of_keeps K₄ (by decide)
  refine WP.seq (st_ok hs₄ (d := fLo) (by simp only [fLo, hdr]; omega_arith) fun t₅ M₅ => WP.block_nil ?_)
  have hs₅ : Scr t₅ E.base E.size := Scr.of_eq hs₄ (by rw [M₅.gpr]) (by rw [M₅.gpr]) M₅.wr
  have O₅ : Outside E.base fLo 4 t₄.mem t₅.mem := by
    rw [M₅.mem]; exact writeW32_outside _ _ _ (by simp only [fLo, hdr]; omega_arith)
  have h₅ : val32 t₅.mem E.base aH g.n32 = Spec.Dsa.decodeBE (hChunk E j) := by
    rw [O₅.val32 (by simp only [aH, fLo, arr, hdr]; omega_arith) (by simp only [aH, arr]; omega_arith),
      O₄.val32 (by simp only [aH, aTmp, arr]; omega_arith) (by simp only [aH, arr]; omega_arith), V₃]
  have pm₅ : val32 t₅.mem E.base aPm1 g.n32 = p - 1 := by
    rw [O₅.val32 (by simp only [aPm1, fLo, arr, hdr]; omega_arith) (by simp only [aPm1, arr]; omega_arith),
      O₄.val32 (by simp only [aPm1, aTmp, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith), pm₃]
  -- `h < p − 1`.
  refine WP.seq (VG.X86.WP.mono_syms (chainSubW_ok hs₅ (k := g.n32) (o := aTmp) (a := aH) (b := aPm1) (by omega_arith)
    (by simp only [aTmp, arr]; omega_arith) (by simp only [aH, arr]; omega_arith) (by simp only [aPm1, arr]; omega_arith)
    (by simp only [aTmp, aH, arr]; omega_arith) (by simp only [aTmp, aPm1, arr]; omega_arith)) fun t₆ ⟨O₆, ⟨c₆, e₆, E₆⟩, K₆⟩ sy₆ =>
    ?_)
  rw [h₅, pm₅] at E₆
  have c₆v := borrow_lt E₆ (val32_lt _ _ _ _)
  have hs₆ := hs₅.of_keeps K₆ (by decide)
  have lo₆ : t₆.mem.readW (off E.base fLo) 32 = cmask c₄ := by
    apply BitVec.eq_of_toNat_eq
    rw [show (t₆.mem.readW (off E.base fLo) 32).toNat = w32 t₆.mem E.base fLo from rfl,
      O₆.w32 (by simp only [aTmp, fLo, arr, hdr]; omega_arith) (by simp only [fLo, hdr]; omega_arith), M₅.mem,
      w32_write_self, e₄]
  refine WP.seq (andm_ok hs₆ (r := .ecx) (d := fLo) (by simp only [fLo, hdr]; omega_arith) fun t₇ u₇ =>
    wp_cmpi fun t₈ f₈ _ z₈ => WP.block_nil (k t₈ ?_))
  have h₆ : val32 t₆.mem E.base aH g.n32 = Spec.Dsa.decodeBE (hChunk E j) := by
    rw [O₆.val32 (by simp only [aH, aTmp, arr]; omega_arith) (by simp only [aH, arr]; omega_arith), h₅]
  have m₈ : t₈.mem = t₆.mem := by rw [f₈.mem, u₇.mem]
  have Ksum : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t₈ :=
    K₂.trans (K₃.trans ((K₄.mono (by decide)).trans ((show Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t₄ t₅ from
      ⟨fun r _ => by rw [M₅.gpr], M₅.rd, M₅.wr⟩).trans
      ((K₆.mono (by decide)).trans ⟨fun r hr => by rw [f₈.gpr, u₇.other r (fun e => hr (e ▸ by simp))],
        by rw [f₈.rd, u₇.rd], by rw [f₈.wr, u₇.wr]⟩))))
  have Ar := rRanges_apart v
  have inR : ∀ {o n d len : Nat}, (o, n) ∈ rRanges → o ≤ d → d + len ≤ o + n →
      ∃ r' ∈ (rRanges.map fun o => (⟨off E.base o.1, o.2⟩ : Region)) ++ [E.stackRegion],
        Region.Sub ⟨off E.base d, len⟩ r' := fun ho h₁ h₂ => Env.in_range ho h₁ h₂
  have ofOut : ∀ {m m' : Mem} {o n o' n' : Nat}, Outside E.base o n m m' → (o', n') ∈ rRanges → o' ≤ o →
      o + n ≤ o' + n' → E.Chg rRanges m m' := by
    intro m m' o n o' n' O ho h₁ h₂
    have fit := (Ar _ ho).1
    refine Env.Chg.of_frame (VG.Proof.Bignum.outs_frame (Outs.of_outside O (List.mem_singleton_self _)) ?_) ?_
    · intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      show o + n ≤ 2 ^ 64
      omega_arith
    · intro r hr
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr; subst hr
      exact inR ho h₁ h₂
  have C₃ : E.Chg rRanges s.mem t₃.mem := by
    rw [← m₂]; exact ofOut O₃ (o' := aH) (n' := 400) (by simp [rRanges]) (Nat.le_refl _)
      (by simp only [aH, arr]; omega_arith)
  have C₄ := ofOut O₄ (o' := aTmp) (n' := 400) (by simp [rRanges]) (Nat.le_refl _) (by simp only [aTmp, arr]; omega_arith)
  have C₅ := ofOut O₅ (o' := fLo) (n' := 4) (by simp [rRanges]) (Nat.le_refl _) (Nat.le_refl _)
  have C₆ := ofOut O₆ (o' := aTmp) (n' := 400) (by simp [rRanges]) (Nat.le_refl _) (by simp only [aTmp, arr]; omega_arith)
  have C : E.Chg rRanges s.mem t₈.mem := by
    rw [m₈]; exact C₃.trans (C₄.trans (C₅.trans C₆))
  have sy₈ : t₈.syms = s.syms := by
    rw [f₈.syms, u₇.syms, sy₆, M₅.syms, sy₄, sy₃, u₂.syms, u₁.syms]
  refine ⟨B.keep v C Ar (Ksum.1 _ (by decide)) (Ksum.1 _ (by decide)) Ksum.2.1 Ksum.2.2 sy₈, by rw [m₈]; exact h₆,
    ?_, C, Ksum.2.1, Ksum.2.2, sy₈⟩
  show t₈.zf = _
  rw [z₈, u₇.gpr, e₆, lo₆, cmask_and, cmask_zf, c₆v, c₄v, Bool.and_comm, ← Bool.decide_and]

end VG.Proof.Dsa.X86.Generation
