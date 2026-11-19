module

public import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttSetup
import VerifiedGarbage.Proof.MlKem.X86.Red
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttSetup
meta import VerifiedGarbage.Proof.MlKem.X86.Red
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Mul
meta import VerifiedGarbage.Impl.MlDsa.X86.Arith.Mul
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic
public import VerifiedGarbage.Proof.MlKem.X86.Common
public import VerifiedGarbage.Proof.MlKem.X86.Leaf
meta import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.MlKem.X86.Leaf

/-! ### `MlDsa.X86.Arith.Ntt`, which the modules that import this one used -/

section

/-! ### `MlDsa.X86.Arith.Mul`, which the modules that import this one used -/

section

/-! ### `MlDsa.X86.Arith.AddSub`, which only this module used -/

section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_add` and `vg_mldsa_sub`

Both are `Impl.MlKem.X86.mapLoop` around an arithmetic step; the loop is
proven once for any step that computes a function `F` of the two coefficients
(`OpSpec`), as for ML-KEM on x86.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_ leaf mapLoop mapBody mapInit)
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa VG.Proof.MlDsa
open VG.Proof.MlKem.X86 (Only wp_cons wp_movm toNat_ofNat32 eq_ofNat_of_toNat E0 P0 P0_esp P0_wr frameR
  retR LeafPost LeafEnd Piece ea_add ptr_next cnt_next cnt_ne)

/-- `op` computes `F a b` in `eax` from `eax = a` and `[edi] = b`, changing
only `eax`, `edx` and the flags. -/
def OpSpec (op : List Instr) (F : Nat → Nat → Nat) : Prop :=
  ∀ (is : List Instr) (s : State) (Q : State → Prop) (a b : Nat), a < q → b < q →
    (s.gpr .eax).toNat = a → InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 4 →
    (s.mem.readW (s.ea (at_ .edi 0)) 32).toNat = b →
    (∀ s', Only [.eax, .edx] s s' → (s'.gpr .eax).toNat = F a b → WP isa (.block is) s' Q) →
    WP isa (.block (op ++ is)) s Q

theorem addOp_spec : OpSpec addOp fun a b => (a + b) % q := by
  intro is s P a b ha hb h₁ hin h₂ k
  have hin' : InRegions (s.rd ++ s.wr) ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 4 := hin
  have h₂' : (s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32).toNat = b := h₂
  rw [addOp, List.cons_append]
  refine wp_cons (s' := (arithFlags s (s.gpr .eax + s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32)
    (2 ^ 32 ≤ (s.gpr .eax).toNat + (s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32).toNat)
    (addOverflow (s.gpr .eax) (s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32)
      (s.gpr .eax + s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32))).setReg .eax
    (s.gpr .eax + s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32))
    (by simp only [exec, execAlu, readSrc, State.ea, at_, State.load32, hin', ite_true, Option.bind_some]) ?_
  have e : (s.gpr .eax + s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32).toNat = a + b := by
    rw [BitVec.toNat_add, h₁, h₂', Nat.mod_eq_of_lt (by rw [q_eq] at ha hb; omega_using [ha, hb])]
  refine csubQ_spec (by decide) is _ P (by simp only [State.setReg, ite_true]; rw [e]; omega_using [ha, hb])
    fun s' o v => k s' ⟨fun r hr => ?_, o.mem, o.rd, o.wr⟩ ?_
  · rw [o.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [State.setReg, arithFlags, State.setFlags, hr.1]
  · rw [v]; simp only [State.setReg, ite_true]; rw [e]

theorem subOp_spec : OpSpec subOp fun a b => (a + q - b) % q := by
  intro is s P a b ha hb h₁ hin h₂ k
  have hin' : InRegions (s.rd ++ s.wr) ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 4 := hin
  have h₂' : (s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32).toNat = b := h₂
  rw [subOp, List.cons_append, List.cons_append]
  let B := s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32
  try rewrite [show s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32 = B from rfl] at *
  have hB : B = s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32 := rfl
  let A := s.gpr .eax + qImm
  try rewrite [show s.gpr .eax + qImm = A from rfl] at *
  have hA : A = s.gpr .eax + qImm := rfl
  refine wp_cons (s' := (arithFlags s A (2 ^ 32 ≤ (s.gpr .eax).toNat + qImm.toNat)
    (addOverflow (s.gpr .eax) qImm A)).setReg .eax A)
    (by simp only [exec, execAlu, readSrc, Option.bind_some]; rfl) ?_
  refine wp_cons (s' := (arithFlags ((arithFlags s A (2 ^ 32 ≤ (s.gpr .eax).toNat + qImm.toNat)
    (addOverflow (s.gpr .eax) qImm A)).setReg .eax A) (A - B) (A.toNat < B.toNat) (subOverflow A B (A - B))).setReg
    .eax (A - B))
    (by simp only [exec, execAlu, readSrc, State.ea, at_, State.load32, State.setReg, arithFlags, State.setFlags,
      hin', ite_true, ite_false, Option.bind_some, reduceCtorEq]; rfl) ?_
  have hA' : A.toNat = a + q := by
    rw [hA, BitVec.toNat_add, h₁, qImm_toNat, Nat.mod_eq_of_lt (by rw [q_eq] at ha ⊢; omega_using [ha])]
  have e : (A - B).toNat = a + q - b := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hA', h₂']; omega_using [hb]), hA', h₂']
  refine csubQ_spec (by decide) is _ P (by simp only [State.setReg, ite_true]; rw [e]; omega_using [ha])
    fun s' o v => k s' ⟨fun r hr => ?_, o.mem, o.rd, o.wr⟩ ?_
  · rw [o.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [State.setReg, arithFlags, State.setFlags, hr.1]
  · rw [v]; simp only [State.setReg, ite_true]; rw [e]

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev fP : BitVec 32 := arg s₀ 0
abbrev gP : BitVec 32 := arg s₀ 1
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev gA : Addr := (gP s₀).setWidth 64
abbrev aR2 : Region := ⟨argAddr s₀ 0, 8⟩
/-- The stack below the return address, as the contract states it. -/
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
end

structure AccPre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (gA s₀)]
  wr : s₀.wr = [polyRegion (fA s₀), aR2 s₀]
  f_g : (polyRegion (fA s₀)).Disjoint (polyRegion (gA s₀))
  f_a : (polyRegion (fA s₀)).Disjoint (aR2 s₀)
  g_a : (polyRegion (gA s₀)).Disjoint (aR2 s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_g : (retR s₀).Disjoint (polyRegion (gA s₀))
  ret_a : (retR s₀).Disjoint (aR2 s₀)
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_g : (stkR s₀).Disjoint (polyRegion (gA s₀))
  stk_a : (stkR s₀).Disjoint (aR2 s₀)
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32
  g_fit : (gP s₀).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (fA s₀)
  g_red : Reduced s₀.mem (gA s₀)

theorem AccPre.of_add {s₀ : State} (h : (addContract X86.abi 16).pre s₀) : AccPre s₀ := by
  sig_pre [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem AccPre.of_sub {s₀ : State} (h : (subContract X86.abi 16).pre s₀) : AccPre s₀ := by
  sig_pre [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-! ## The loop -/

/-- The new value of coefficient `i`. -/
def newC (F : Nat → Nat → Nat) (s₀ : State) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (F (coeffAt s₀.mem (fA s₀) i).toNat (coeffAt s₀.mem (gA s₀) i).toNat)

/-- After `k` coefficients. -/
structure MapInv (F : Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = fP s₀ + BitVec.ofNat 32 (4 * k)
  edi : s.gpr .edi = gP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  frame : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem
  f : ∀ i < 256, coeffAt s.mem (fA s₀) i = if i < k then newC F s₀ i else coeffAt s₀.mem (fA s₀) i

namespace AccPre
variable {s₀ : State} (hp : AccPre s₀)
include hp

theorem in_f {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions s.wr (coeffAddr (fA s₀) k) 4 := by
  rw [hw, P0_wr, hp.wr]
  exact ⟨polyRegion (fA s₀), by simp, coeff_contains _ hk⟩

theorem in_f' {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (fA s₀) k) 4 :=
  let ⟨r, h, c⟩ := hp.in_f hw hk; ⟨r, List.mem_append_right _ h, c⟩

theorem in_g {s : State} (hr : s.rd = (P0 s₀).rd) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (gA s₀) k) 4 := by
  rw [hr, pushed_rd, hp.rd]
  exact ⟨polyRegion (gA s₀), by simp, coeff_contains _ hk⟩

/-- `g` is never written. -/
theorem g_keep {s : State} (hf : Frame [polyRegion (fA s₀)] (P0 s₀).mem s.mem) {i : Nat} (hi : i < 256) :
    coeffAt s.mem (gA s₀) i = coeffAt s₀.mem (gA s₀) i := by
  have f₁ := P0_mem hp.sp
  rw [coeffAt_congr (m := s₀.mem) (m' := s.mem) (fun j hj => ?_) hi]
  rw [hf.bytes (R := polyRegion (gA s₀)) (by simpa using hp.f_g.symm) (polyLen _) hj,
    f₁.bytes (R := polyRegion (gA s₀)) (by simpa [← stk_eq hp.sp] using hp.stk_g.symm) (polyLen _) hj]

theorem f_P0 {i : Nat} (hi : i < 256) : coeffAt (P0 s₀).mem (fA s₀) i = coeffAt s₀.mem (fA s₀) i :=
  coeffAt_congr (fun j hj => (P0_mem hp.sp).bytes (R := polyRegion (fA s₀))
    (by simpa [← stk_eq hp.sp] using hp.stk_f.symm) (polyLen _) hj) hi

theorem ea_f (k : Nat) (hk : k < 256) :
    (fP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (fA s₀) k := by
  rw [ea_add (by have := hp.f_fit; omega_using [hk, this]), Nat.add_zero]

theorem ea_g (k : Nat) (hk : k < 256) :
    (gP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (gA s₀) k := by
  rw [ea_add (by have := hp.g_fit; omega_using [hk, this]), Nat.add_zero]

end AccPre

theorem map_step {op : List Instr} {F : Nat → Nat → Nat} (hop : OpSpec op F) {s₀ : State} (hp : AccPre s₀)
    {k : Nat} (hk : k < 256) {s : State} (h : MapInv F s₀ k s) :
    WP isa (.block (mapBody op)) s fun s' =>
      MapInv F s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < n := hk
  have ef : s.ea (at_ .esi 0) = coeffAddr (fA s₀) k := by
    rw [State.ea, at_, h.esi]; exact hp.ea_f k hk
  refine wp_movm (by rw [ef]; exact hp.in_f' h.wr hk) ?_
  let s₁ := s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)
  try rewrite [show s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32) = s₁ from rfl] at *
  have hs₁ : s₁ = s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32) := rfl
  have ha : (coeffAt s₀.mem (fA s₀) k).toNat < q := hp.f_red k hk'
  have hb : (coeffAt s₀.mem (gA s₀) k).toNat < q := hp.g_red k hk'
  have eg : s₁.ea (at_ .edi 0) = coeffAddr (gA s₀) k := by
    simp only [hs₁, State.ea, at_, State.setReg, show Reg.edi ≠ Reg.eax by decide, ite_false, h.edi]
    exact hp.ea_g k hk
  refine hop _ s₁ _ _ _ ha hb ?_ ?_ ?_ fun s₂ o₂ v₂ => ?_
  · simp only [hs₁, State.setReg, ite_true]
    rw [ef, ← coeffAt_eq, h.f k hk, ite_eq_right (Nat.lt_irrefl k)]
  · rw [eg]; exact hp.in_g h.rd hk
  · rw [eg, show s₁.mem = s.mem from rfl, ← coeffAt_eq, hp.g_keep h.frame hk]
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [o₂.gpr r (by simp [h₁, h₂])]; simp [hs₁, State.setReg, h₁]
  have m₂ : s₂.mem = s.mem := o₂.mem
  have r₂ : s₂.rd = (P0 s₀).rd := o₂.rd.trans h.rd
  have w₂ : s₂.wr = (P0 s₀).wr := o₂.wr.trans h.wr
  have esi₂ : s₂.gpr .esi = fP s₀ + BitVec.ofNat 32 (4 * k) := by rw [g₂ _ (by decide) (by decide), h.esi]
  have edi₂ : s₂.gpr .edi = gP s₀ + BitVec.ofNat 32 (4 * k) := by rw [g₂ _ (by decide) (by decide), h.edi]
  have ecx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (256 - k) := by rw [g₂ _ (by decide) (by decide), h.ecx]
  have out : InRegions s₂.wr (coeffAddr (fA s₀) k) 4 := hp.in_f w₂ hk
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store32, State.setReg, arithFlags, State.setFlags, esi₂,
    hp.ea_f k hk, out, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hv : s₂.gpr .eax = newC F s₀ k := eq_ofNat_of_toNat v₂
  refine ⟨⟨by simp [g₂, h.esp], r₂, w₂, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · simp only [ite_true, ite_false, show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide]
    exact ptr_next _ _ 4
  · simp only [ite_true, ite_false, show Reg.edi ≠ Reg.ecx by decide, edi₂]
    exact ptr_next _ _ 4
  · simp only [ite_true, ecx₂]
    exact cnt_next hk
  · rw [m₂]; exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk')
  · dsimp only
    rw [coeffAt_writeW _ _ (show i < n from hi) hk', m₂, hv, h.f i hi]
    by_cases e : k = i
    · subst e; simp
    · rw [ite_eq_right e]
      by_cases hik : i < k
      · rw [ite_eq_left hik, ite_eq_left (by omega_using [hik])]
      · rw [ite_eq_right hik, ite_eq_right (by omega_using [e, hik])]
  · simp only [eval, ecx₂]
    exact cnt_ne hk (by decide)

/-! ## The function -/

/-- The public data: the stack pointer and the pointers. -/
def AccPub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

/-- The arguments, which the push leaves in place. -/
theorem AccPre.arg_P0 {s₀ : State} (hp : AccPre s₀) {i : Nat} (hi : i < 2) :
    ((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      InRegions ((P0 s₀).rd ++ (P0 s₀).wr) (argAddr s₀ i) 4 ∧
      (P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hc : (aR2 s₀).Contains (argAddr s₀ i) 4 := by
    have := hp.sp'
    simp only [argAddr, Region.Contains, E0] at this ⊢
    bv_omega
  refine ⟨?_, ⟨aR2 s₀, by simp [hp.wr], hc⟩, ?_⟩
  · rw [P0_esp]; simp only [argAddr, E0]; congr 1; bv_omega
  · exact (P0_mem hp.sp).readW hc (by simpa [← stk_eq hp.sp] using hp.stk_a.symm) (by decide)

theorem init_piece (F : Nat → Nat → Nat) :
    Piece AccPre AccPub (fun s₀ s => s = P0 s₀) (MapInv F · 0) (.block mapInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by native_taint_decide)
  · subst e
    obtain ⟨a₀, i₀, v₀⟩ := hp.arg_P0 (i := 0) (by omega_using [])
    obtain ⟨a₁, i₁, v₁⟩ := hp.arg_P0 (i := 1) (by omega_using [])
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at a₀ a₁
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, mapInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, a₁, i₀, i₁, v₀, v₁,
      Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, by simp, by simp, by simp, Frame.refl _ _, fun i hi => ?_⟩
    simp only [Nat.not_lt_zero, ite_false]
    exact hp.f_P0 hi
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

theorem loop_piece {op : List Instr} {F : Nat → Nat → Nat} (hop : OpSpec op F)
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (mapBody op)) hc).isSome = true) :
    Piece AccPre AccPub (MapInv F · 0) (MapInv F · 256) (.loop (.block (mapBody op)) .ne) :=
  Piece.loop (fun k s₀ s => MapInv F s₀ k s) (by decide) fun k hk =>
    Piece.taint [.esp, .esi, .edi, .ecx] (fun _ _ hp h => map_step hop hp hk h)
      (fun s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, fP, fP, hq.2.1]
        · rw [h.edi, h'.edi, gP, gP, hq.2.2]
        · rw [h.ecx, h'.ecx]) ht

theorem map_piece {op : List Instr} {F : Nat → Nat → Nat} (hop : OpSpec op F)
    (hsp : NoSp (mapLoop op)) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (mapBody op)) hc).isSome = true) :
    Piece AccPre AccPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (MapInv F s₀ 256) s₀ s')
      (leaf (mapLoop op)) :=
  Piece.leaf (fun s₀ => [polyRegion (fA s₀)]) hsp (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega_using [this]⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← stk_eq hp.sp]; exact hp.stk_f, hp.ret_f⟩)
    (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (init_piece F) (loop_piece hop ht)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- The polynomial the loop leaves. -/
theorem map_post {F : Nat → Nat → Nat} {G : Zq → Zq → Zq} (hG : ∀ x y : Zq, (G x y).val = F x.val y.val)
    {s₀ s : State} (hp : AccPre s₀) (h : MapInv F s₀ 256 s) :
    PolyIs s.mem (fA s₀) (Vector.zipWith G (polyAt s₀.mem (fA s₀)) (polyAt s₀.mem (gA s₀))) := by
  refine polyIs_of_toNat fun i hi => ?_
  have hlt := val_lt (G (polyAt s₀.mem (fA s₀))[i]! (polyAt s₀.mem (gA s₀))[i]!)
  rw [hG, polyAt_val hp.f_red hi, polyAt_val hp.g_red hi] at hlt
  rw [h.f i hi, ite_eq_left hi, getElem!_eq _ hi, Vector.getElem_zipWith, ← getElem!_eq _ hi,
    ← getElem!_eq _ hi, hG, polyAt_val hp.f_red hi, polyAt_val hp.g_red hi, newC, toNat_ofNat32 (by omega_using [hlt])]

/-- Memory whose argument words (at `0x5004`) hold `0` and `0x400`. -/
def accSatMem : Mem := fun a => if a = 0x5009 then 4 else 0

/-- A state satisfying the precondition: `f` at `0`, `g` at `0x400`. -/
def accSat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := accSatMem
  rd := [⟨0x400, 1024⟩]
  wr := [⟨0, 1024⟩, ⟨0x5004, 8⟩]

theorem accSat_red (p : Nat) (hp : p + 1024 ≤ 0x5000) : Reduced accSatMem (BitVec.ofNat 64 p) :=
  reduced_below (fun a ha => by
    simp only [accSatMem]
    rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha])]) p hp

theorem add_verified : Verified X86.target add (addContract X86.abi 16) := by
  refine Piece.verified (((map_piece addOp_spec (NoSp.of_all (by decide +kernel)) (by native_taint_decide)).pre_mono
    (fun _ h => AccPre.of_add h) fun s s' _ _ h => by
      sig_pub [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    refine Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; have hp := AccPre.of_add h₀; rw [← stk_eq hp.sp]; exact hp.stk_f.symm) ?_
    exact map_post (G := (· + ·)) (fun x y => val_add' x y) (AccPre.of_add h₀) hinv
  · refine ⟨accSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg accSat 0) = BitVec.ofNat 64 0 by decide]
           exact accSat_red 0 (by decide))
        | (rw [show BitVec.setWidth 64 (arg accSat 1) = BitVec.ofNat 64 0x400 by decide]
           exact accSat_red 0x400 (by decide))
        | decide +kernel

theorem sub_verified : Verified X86.target sub (subContract X86.abi 16) := by
  refine Piece.verified (((map_piece subOp_spec (NoSp.of_all (by decide +kernel)) (by native_taint_decide)).pre_mono
    (fun _ h => AccPre.of_sub h) fun s s' _ _ h => by
      sig_pub [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    refine Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; have hp := AccPre.of_sub h₀; rw [← stk_eq hp.sp]; exact hp.stk_f.symm) ?_
    exact map_post (G := (· - ·)) sub_val (AccPre.of_sub h₀) hinv
  · refine ⟨accSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg accSat 0) = BitVec.ofNat 64 0 by decide]
           exact accSat_red 0 (by decide))
        | (rw [show BitVec.setWidth 64 (arg accSat 1) = BitVec.ofNat 64 0x400 by decide]
           exact accSat_red 0x400 (by decide))
        | decide +kernel

end VG.Proof.MlDsa.X86.Arith

end

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

`mulHead` leaves `f[i] · g[i] mod q` in `ebx` (`head_spec`): two Montgomery
reductions, the second of the first times `2⁶⁴ mod q` (`mont_mont_R2`). The
loop over the coefficients is proven once for both functions (`MulInv`,
`step`), with the value `V a b c` of coefficient `i` from those of `f`, `g`
and `h`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_ leaf)
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa VG.Proof.MlDsa
open VG.Proof.MlKem.X86 (Only wp_cons wp_movm wp_movr wp_mul toNat_ofNat32 eq_ofNat_of_toNat E0 P0 P0_esp
  P0_wr frameR retR LeafPost LeafEnd Piece ea_add ptr_next cnt_next cnt_ne execMul_other satState)

theorem mulHead_eq (is : List Instr) : mulHead ++ is =
    .mov .eax (.mem (at_ .esi 0)) :: .mov .edx (.mem (at_ .edi 0)) :: .mul .edx :: (mredRaw .ebx ++
      (.mov .eax (.reg .ebx) :: .mov .edx (.imm r2Imm) :: .mul .edx :: (mred .ebx ++ is))) := by
  simp only [mulHead, List.cons_append, List.nil_append, List.append_assoc]

theorem r2Imm_toNat : r2Imm.toNat = 2 ^ 64 % q := rfl

/-- `mulHead` leaves `a · b mod q` in `ebx` from `[esi] = a` and `[edi] = b`,
changing only `eax`, `edx`, `ebx` and the flags. -/
theorem head_spec (is : List Instr) (s : State) (P : State → Prop) {a b : Nat} (ha : a < q) (hb : b < q)
    (hia : InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 4) (hva : (s.mem.readW (s.ea (at_ .esi 0)) 32).toNat = a)
    (hib : InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 4) (hvb : (s.mem.readW (s.ea (at_ .edi 0)) 32).toNat = b)
    (k : ∀ s', Only [.eax, .edx, .ebx] s s' → (s'.gpr .ebx).toNat = a * b % q → WP isa (.block is) s' P) :
    WP isa (.block (mulHead ++ is)) s P := by
  rw [mulHead_eq]
  refine wp_movm hia (wp_movm ?_ (wp_mul ?_))
  · simpa only [State.ea, at_, State.setReg, show Reg.edi ≠ Reg.eax by decide, ite_false] using hib
  let s₁ := (s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)).setReg .edx
    ((s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)).mem.readW
      ((s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)).ea (at_ .edi 0)) 32)
  try rewrite [show (s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)).setReg .edx
    ((s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)).mem.readW
      ((s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)).ea (at_ .edi 0)) 32) = s₁ from rfl] at *
  have hs₁ : s₁ = (s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)).setReg .edx
    ((s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)).mem.readW
      ((s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32)).ea (at_ .edi 0)) 32) := rfl
  have e₁ : ((execMul .edx s₁).gpr .edx).toNat * 2 ^ 32 + ((execMul .edx s₁).gpr .eax).toNat = a * b := by
    rw [execMul_pair]
    simp only [hs₁, State.setReg, ite_true, ite_false, show Reg.eax ≠ Reg.edx by decide, State.ea, at_,
      show Reg.edi ≠ Reg.eax by decide]
    simp only [State.ea, at_] at hva hvb
    rw [hva, hvb]
  have hab : a * b < q * 2 ^ 32 := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt ha hb) (by decide)
  refine mredRaw_spec (by decide) (by decide) _ _ P e₁ hab fun s₂ o₂ v₂ => ?_
  refine wp_movr (wp_movi (wp_mul ?_))
  have ht := mont_lt hab
  have e₂ : ((execMul .edx ((s₂.setReg .eax (s₂.gpr .ebx)).setReg .edx r2Imm)).gpr .edx).toNat * 2 ^ 32 +
      ((execMul .edx ((s₂.setReg .eax (s₂.gpr .ebx)).setReg .edx r2Imm)).gpr .eax).toNat =
      mont (a * b) * (2 ^ 64 % q) := by
    rw [execMul_pair]
    simp only [State.setReg, ite_true, ite_false, show Reg.eax ≠ Reg.edx by decide]
    rw [v₂, r2Imm_toNat]
  have hlt : mont (a * b) * (2 ^ 64 % q) < q * 2 ^ 32 := by
    have : 2 ^ 64 % q < q := Nat.mod_lt _ (by decide)
    have := Nat.mul_lt_mul_of_lt_of_lt ht this
    rw [q_eq] at this ⊢; omega_using [v₂]
  refine mred_spec (by decide) (by decide) _ _ P e₂ hlt fun s₃ o₃ v₃ => k s₃ ⟨fun r hr => ?_, ?_, ?_, ?_⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [o₃.gpr r (by simp [hr.1, hr.2.1, hr.2.2]), execMul_other _ _ hr.1 hr.2.1]
    simp only [State.setReg, hr.1, hr.2.1, ite_false]
    rw [o₂.gpr r (by simp [hr.1, hr.2.1, hr.2.2]), execMul_other _ _ hr.1 hr.2.1]
    simp [hs₁, State.setReg, hr.1, hr.2.1]
  · rw [o₃.mem]; simp only [execMul, State.setReg, State.setFlags]; rw [o₂.mem]; rfl
  · rw [o₃.rd]; simp only [execMul, State.setReg, State.setFlags]; rw [o₂.rd]; rfl
  · rw [o₃.wr]; simp only [execMul, State.setReg, State.setFlags]; rw [o₂.wr]; rfl
  · rw [v₃, mont_mont_R2]

/-! ## The bodies -/

/-- The arithmetic of the body of `multiplyNTT` (`acc = false`) or
`multiplyAddNTT` (`true`): `ebx ← V a b c` from `[esi] = a`, `[edi] = b` and
`[ebp] = c` (reduced if `acc`), changing only `eax`, `edx`, `ebx` and the
flags. -/
def CoreSpec (core : List Instr) (acc : Bool) (V : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (is : List Instr) (s : State) (P : State → Prop) (a b c : Nat), a < q → b < q → (acc = true → c < q) →
    InRegions (s.rd ++ s.wr) (s.ea (at_ .esi 0)) 4 → (s.mem.readW (s.ea (at_ .esi 0)) 32).toNat = a →
    InRegions (s.rd ++ s.wr) (s.ea (at_ .edi 0)) 4 → (s.mem.readW (s.ea (at_ .edi 0)) 32).toNat = b →
    InRegions (s.rd ++ s.wr) (s.ea (at_ .ebp 0)) 4 → (s.mem.readW (s.ea (at_ .ebp 0)) 32).toNat = c →
    (∀ s', Only [.eax, .edx, .ebx] s s' → (s'.gpr .ebx).toNat = V a b c → WP isa (.block is) s' P) →
    WP isa (.block (core ++ is)) s P

/-- The value of `multiplyNTT`. -/
def mulV (a b _c : Nat) : Nat := a * b % q

/-- The value of `multiplyAddNTT`. -/
def mulAddV (a b c : Nat) : Nat := (a * b % q + c) % q

theorem mul_core : CoreSpec mulHead false mulV :=
  fun is s P _ _ _ ha hb _ hia hva hib hvb _ _ k => head_spec is s P ha hb hia hva hib hvb k

/-- `mulHead`, then `h[i]` added. -/
def mulAddCore : List Instr := mulHead ++ .alu .add .ebx (.mem (at_ .ebp 0)) :: csubQ .ebx .edx

theorem mulAdd_core : CoreSpec mulAddCore true mulAddV := by
  intro is s P a b c ha hb hc hia hva hib hvb hic hvc k
  rw [mulAddCore, List.append_assoc]
  refine head_spec _ s P ha hb hia hva hib hvb fun s₁ o₁ v₁ => ?_
  have hc' := hc rfl
  have hic' : InRegions (s₁.rd ++ s₁.wr) ((s₁.gpr .ebp + BitVec.ofNat 32 0).setWidth 64) 4 := by
    rw [o₁.rd, o₁.wr, o₁.gpr .ebp (by decide)]; exact hic
  have hvc' : (s₁.mem.readW ((s₁.gpr .ebp + BitVec.ofNat 32 0).setWidth 64) 32).toNat = c := by
    rw [o₁.mem, o₁.gpr .ebp (by decide)]; exact hvc
  let C := s₁.mem.readW ((s₁.gpr .ebp + BitVec.ofNat 32 0).setWidth 64) 32
  try rewrite [show s₁.mem.readW ((s₁.gpr .ebp + BitVec.ofNat 32 0).setWidth 64) 32 = C from rfl] at *
  have hC : C = s₁.mem.readW ((s₁.gpr .ebp + BitVec.ofNat 32 0).setWidth 64) 32 := rfl
  rw [List.cons_append]
  refine wp_cons (s' := (arithFlags s₁ (s₁.gpr .ebx + C) (2 ^ 32 ≤ (s₁.gpr .ebx).toNat + C.toNat)
    (addOverflow (s₁.gpr .ebx) C (s₁.gpr .ebx + C))).setReg .ebx (s₁.gpr .ebx + C))
    (by simp only [exec, execAlu, readSrc, State.ea, at_, State.load32, hic', ite_true, Option.bind_some]; rfl) ?_
  have hlt := Nat.mod_lt (a * b) (show q > 0 by decide)
  have e : (s₁.gpr .ebx + C).toNat = a * b % q + c := by
    rw [BitVec.toNat_add, v₁, hvc', Nat.mod_eq_of_lt (by rw [q_eq] at hlt hc' ⊢; omega_using [hc'])]
  refine csubQ_spec (by decide) is _ P (by simp only [State.setReg, ite_true]; rw [e]; rw [q_eq] at hlt hc' ⊢; omega_using [hc'])
    fun s' o v => k s' ((o₁.trans (show Only [.ebx, .edx] s₁ s' from ⟨fun r hr => ?_, o.mem, o.rd, o.wr⟩)).mono
      fun r hr => ?_) ?_
  · rw [o.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [State.setReg, arithFlags, State.setFlags, hr.1]
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (e | e | e) | (e | e) <;> simp [e]
  · rw [v]; simp only [State.setReg, ite_true]; rw [e]; rfl

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev hP : BitVec 32 := arg s₀ 0
abbrev fP' : BitVec 32 := arg s₀ 1
abbrev gP' : BitVec 32 := arg s₀ 2
abbrev hA : Addr := (hP s₀).setWidth 64
abbrev fA' : Addr := (fP' s₀).setWidth 64
abbrev gA' : Addr := (gP' s₀).setWidth 64
abbrev aR3 : Region := ⟨argAddr s₀ 0, 12⟩
end

/-- The precondition of both functions: `h` is reduced if `acc`. -/
structure MulPre (acc : Bool) (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 12 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (fA' s₀), polyRegion (gA' s₀)]
  wr : s₀.wr = [polyRegion (hA s₀), aR3 s₀]
  h_f : (polyRegion (hA s₀)).Disjoint (polyRegion (fA' s₀))
  h_g : (polyRegion (hA s₀)).Disjoint (polyRegion (gA' s₀))
  h_a : (polyRegion (hA s₀)).Disjoint (aR3 s₀)
  f_a : (polyRegion (fA' s₀)).Disjoint (aR3 s₀)
  g_a : (polyRegion (gA' s₀)).Disjoint (aR3 s₀)
  ret_h : (retR s₀).Disjoint (polyRegion (hA s₀))
  ret_f : (retR s₀).Disjoint (polyRegion (fA' s₀))
  ret_g : (retR s₀).Disjoint (polyRegion (gA' s₀))
  ret_a : (retR s₀).Disjoint (aR3 s₀)
  stk_h : (stkR s₀).Disjoint (polyRegion (hA s₀))
  stk_f : (stkR s₀).Disjoint (polyRegion (fA' s₀))
  stk_g : (stkR s₀).Disjoint (polyRegion (gA' s₀))
  stk_a : (stkR s₀).Disjoint (aR3 s₀)
  h_fit : (hP s₀).toNat + 1024 ≤ 2 ^ 32
  f_fit : (fP' s₀).toNat + 1024 ≤ 2 ^ 32
  g_fit : (gP' s₀).toNat + 1024 ≤ 2 ^ 32
  h_red : acc = true → Reduced s₀.mem (hA s₀)
  f_red : Reduced s₀.mem (fA' s₀)
  g_red : Reduced s₀.mem (gA' s₀)

theorem MulPre.of_mul {s₀ : State} (h : (mulContract X86.abi 16).pre s₀) : MulPre false s₀ := by
  sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    fun e => absurd e (by decide), h21, h22⟩

theorem MulPre.of_mulAdd {s₀ : State} (h : (mulAddContract X86.abi 16).pre s₀) : MulPre true s₀ := by
  sig_pre [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    fun _ => h21, h22, h23⟩

/-! ## The loop -/

/-- The new value of coefficient `i`. -/
def newM (V : Nat → Nat → Nat → Nat) (s₀ : State) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (V (coeffAt s₀.mem (fA' s₀) i).toNat (coeffAt s₀.mem (gA' s₀) i).toNat
    (coeffAt s₀.mem (hA s₀) i).toNat)

/-- After `k` coefficients. -/
structure MulInv (V : Nat → Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  ebp : s.gpr .ebp = hP s₀ + BitVec.ofNat 32 (4 * k)
  esi : s.gpr .esi = fP' s₀ + BitVec.ofNat 32 (4 * k)
  edi : s.gpr .edi = gP' s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  frame : Frame [polyRegion (hA s₀)] (P0 s₀).mem s.mem
  h : ∀ i < 256, coeffAt s.mem (hA s₀) i = if i < k then newM V s₀ i else coeffAt s₀.mem (hA s₀) i

namespace MulPre
variable {acc : Bool} {s₀ : State} (hp : MulPre acc s₀)
include hp

theorem in_h {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions s.wr (coeffAddr (hA s₀) k) 4 := by
  rw [hw, P0_wr, hp.wr]
  exact ⟨polyRegion (hA s₀), by simp, coeff_contains _ hk⟩

theorem in_h' {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (hA s₀) k) 4 :=
  let ⟨r, h, c⟩ := hp.in_h hw hk; ⟨r, List.mem_append_right _ h, c⟩

theorem in_f {s : State} (hr : s.rd = (P0 s₀).rd) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (fA' s₀) k) 4 := by
  rw [hr, pushed_rd, hp.rd]
  exact ⟨polyRegion (fA' s₀), by simp, coeff_contains _ hk⟩

theorem in_g {s : State} (hr : s.rd = (P0 s₀).rd) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (gA' s₀) k) 4 := by
  rw [hr, pushed_rd, hp.rd]
  exact ⟨polyRegion (gA' s₀), by simp, coeff_contains _ hk⟩

/-- `f` and `g` are never written. -/
theorem f_keep {s : State} (hf : Frame [polyRegion (hA s₀)] (P0 s₀).mem s.mem) {i : Nat} (hi : i < 256) :
    coeffAt s.mem (fA' s₀) i = coeffAt s₀.mem (fA' s₀) i := by
  rw [coeffAt_congr (m := s₀.mem) (m' := s.mem) (fun j hj => ?_) hi]
  rw [hf.bytes (R := polyRegion (fA' s₀)) (by simpa using hp.h_f.symm) (polyLen _) hj,
    (P0_mem hp.sp).bytes (R := polyRegion (fA' s₀)) (by simpa [← stk_eq hp.sp] using hp.stk_f.symm)
      (polyLen _) hj]

theorem g_keep {s : State} (hf : Frame [polyRegion (hA s₀)] (P0 s₀).mem s.mem) {i : Nat} (hi : i < 256) :
    coeffAt s.mem (gA' s₀) i = coeffAt s₀.mem (gA' s₀) i := by
  rw [coeffAt_congr (m := s₀.mem) (m' := s.mem) (fun j hj => ?_) hi]
  rw [hf.bytes (R := polyRegion (gA' s₀)) (by simpa using hp.h_g.symm) (polyLen _) hj,
    (P0_mem hp.sp).bytes (R := polyRegion (gA' s₀)) (by simpa [← stk_eq hp.sp] using hp.stk_g.symm)
      (polyLen _) hj]

theorem h_P0 {i : Nat} (hi : i < 256) : coeffAt (P0 s₀).mem (hA s₀) i = coeffAt s₀.mem (hA s₀) i :=
  coeffAt_congr (fun j hj => (P0_mem hp.sp).bytes (R := polyRegion (hA s₀))
    (by simpa [← stk_eq hp.sp] using hp.stk_h.symm) (polyLen _) hj) hi

end MulPre

theorem mul_step {core : List Instr} {acc : Bool} {V : Nat → Nat → Nat → Nat} (hc : CoreSpec core acc V)
    {s₀ : State} (hp : MulPre acc s₀) {k : Nat} (hk : k < 256) {s : State} (h : MulInv V s₀ k s) :
    WP isa (.block (core ++ mulTail)) s fun s' =>
      MulInv V s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < n := hk
  have eh : s.ea (at_ .ebp 0) = coeffAddr (hA s₀) k := by
    rw [State.ea, at_, h.ebp]; exact ea_ptr hp.h_fit hk
  have ef : s.ea (at_ .esi 0) = coeffAddr (fA' s₀) k := by
    rw [State.ea, at_, h.esi]; exact ea_ptr hp.f_fit hk
  have eg : s.ea (at_ .edi 0) = coeffAddr (gA' s₀) k := by
    rw [State.ea, at_, h.edi]; exact ea_ptr hp.g_fit hk
  refine hc _ s _ _ _ _ (hp.f_red k hk') (hp.g_red k hk') (fun e => (hp.h_red e) k hk')
    (by rw [ef]; exact hp.in_f h.rd hk) (by rw [ef, ← coeffAt_eq, hp.f_keep h.frame hk])
    (by rw [eg]; exact hp.in_g h.rd hk) (by rw [eg, ← coeffAt_eq, hp.g_keep h.frame hk])
    (by rw [eh]; exact hp.in_h' h.wr hk) (by rw [eh, ← coeffAt_eq, h.h k hk, ite_eq_right (Nat.lt_irrefl k)])
    fun s₂ o₂ v₂ => ?_
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [o₂.gpr r (by simp [h₁, h₂, h₃])]
  have m₂ : s₂.mem = s.mem := o₂.mem
  have r₂ : s₂.rd = (P0 s₀).rd := o₂.rd.trans h.rd
  have w₂ : s₂.wr = (P0 s₀).wr := o₂.wr.trans h.wr
  have ebp₂ : s₂.gpr .ebp = hP s₀ + BitVec.ofNat 32 (4 * k) := by
    rw [g₂ _ (by decide) (by decide) (by decide), h.ebp]
  have esi₂ : s₂.gpr .esi = fP' s₀ + BitVec.ofNat 32 (4 * k) := by
    rw [g₂ _ (by decide) (by decide) (by decide), h.esi]
  have edi₂ : s₂.gpr .edi = gP' s₀ + BitVec.ofNat 32 (4 * k) := by
    rw [g₂ _ (by decide) (by decide) (by decide), h.edi]
  have ecx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (256 - k) := by
    rw [g₂ _ (by decide) (by decide) (by decide), h.ecx]
  have out : InRegions s₂.wr (coeffAddr (hA s₀) k) 4 := hp.in_h w₂ hk
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, mulTail, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store32, State.setReg, arithFlags, State.setFlags, ebp₂,
    ea_ptr hp.h_fit hk, out, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hv : s₂.gpr .ebx = newM V s₀ k := eq_ofNat_of_toNat v₂
  refine ⟨⟨by simp [g₂, h.esp], r₂, w₂, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · simp only [ite_true, ite_false, show Reg.ebp ≠ Reg.ecx by decide]
    exact ptr_next _ _ 4
  · simp only [ite_true, ite_false, show Reg.esi ≠ Reg.ecx by decide, show Reg.esi ≠ Reg.edi by decide,
      show Reg.esi ≠ Reg.ebp by decide, esi₂]
    exact ptr_next _ _ 4
  · simp only [ite_true, ite_false, show Reg.edi ≠ Reg.ecx by decide, show Reg.edi ≠ Reg.ebp by decide, edi₂]
    exact ptr_next _ _ 4
  · simp only [ite_true, ecx₂]
    exact cnt_next hk
  · rw [m₂]; exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk')
  · dsimp only
    rw [coeffAt_writeW _ _ (show i < n from hi) hk', m₂, hv, h.h i hi]
    by_cases e : k = i
    · subst e; simp
    · rw [ite_eq_right e]
      by_cases hik : i < k
      · rw [ite_eq_left hik, ite_eq_left (by omega_using [hik])]
      · rw [ite_eq_right hik, ite_eq_right (by omega_using [e, hik])]
  · simp only [eval, ecx₂]
    exact cnt_ne hk (by decide)

/-! ## The functions -/

/-- The public data: the stack pointer and the pointers. -/
def MulPub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2

/-- The arguments, which the push leaves in place. -/
theorem MulPre.arg_P0 {acc : Bool} {s₀ : State} (hp : MulPre acc s₀) {i : Nat} (hi : i < 3) :
    ((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      InRegions ((P0 s₀).rd ++ (P0 s₀).wr) (argAddr s₀ i) 4 ∧
      (P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hc : (aR3 s₀).Contains (argAddr s₀ i) 4 := by
    have := hp.sp'
    simp only [argAddr, Region.Contains, E0] at this ⊢
    bv_omega
  refine ⟨?_, ⟨aR3 s₀, by simp [hp.wr], hc⟩, ?_⟩
  · rw [P0_esp]; simp only [argAddr, E0]; congr 1; bv_omega
  · exact (P0_mem hp.sp).readW hc (by simpa [← stk_eq hp.sp] using hp.stk_a.symm) (by decide)

theorem mulInit_piece (acc : Bool) (V : Nat → Nat → Nat → Nat) :
    Piece (MulPre acc) MulPub (fun s₀ s => s = P0 s₀) (MulInv V · 0) (.block mulInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by native_taint_decide)
  · subst e
    obtain ⟨a₀, i₀, v₀⟩ := hp.arg_P0 (i := 0) (by omega_using [])
    obtain ⟨a₁, i₁, v₁⟩ := hp.arg_P0 (i := 1) (by omega_using [])
    obtain ⟨a₂, i₂, v₂⟩ := hp.arg_P0 (i := 2) (by omega_using [])
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at a₀ a₁ a₂
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, mulInit, at_, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, State.ea, State.load32, State.setReg, Option.map_some, a₀, a₁, a₂, i₀, i₁, i₂, v₀, v₁,
      v₂, Option.some.injEq, exists_eq_left']
    refine ⟨by simp, rfl, rfl, by simp, by simp, by simp, by simp, Frame.refl _ _, fun i hi => ?_⟩
    simp only [Nat.not_lt_zero, ite_false]
    exact hp.h_P0 hi
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', P0_esp, P0_esp, hq.1]

theorem mul_piece {core : List Instr} {acc : Bool} {V : Nat → Nat → Nat → Nat} (hc : CoreSpec core acc V)
    (hsp : NoSp (.seq (.block mulInit) (.loop (.block (core ++ mulTail)) .ne))) {hh : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .ebp, .esi, .edi, .ecx]) (.block (core ++ mulTail)) hh).isSome = true) :
    Piece (MulPre acc) MulPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (MulInv V s₀ 256) s₀ s')
      (leaf (.seq (.block mulInit) (.loop (.block (core ++ mulTail)) .ne))) :=
  Piece.leaf (fun s₀ => [polyRegion (hA s₀)]) hsp (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega_using [this]⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← stk_eq hp.sp]; exact hp.stk_h, hp.ret_h⟩)
    (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (mulInit_piece acc V) (Piece.loop (fun k s₀ s => MulInv V s₀ k s) (by decide) fun k hk =>
      Piece.taint [.esp, .ebp, .esi, .edi, .ecx] (fun _ _ hp h => mul_step hc hp hk h)
        (fun s₀ s₀' s s' _ _ hq h h' r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl
          · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
          · rw [h.ebp, h'.ebp, hP, hP, hq.2.1]
          · rw [h.esi, h'.esi, fP', fP', hq.2.2.1]
          · rw [h.edi, h'.edi, gP', gP', hq.2.2.2]
          · rw [h.ecx, h'.ecx]) ht)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- Memory with the arguments `0`, `0x400` and `0x800` at `0x5004`. -/
def mulSatMem : Mem := fun a => if a = 0x5009 then 4 else if a = 0x500d then 8 else 0

theorem mulSat_zero (a : Addr) (ha : a.toNat < 0x5000) : mulSatMem a = 0 := by
  simp only [mulSatMem]
  rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha]),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha])]

theorem mul_verified : Verified X86.target mul (mulContract X86.abi 16) := by
  refine Piece.verified (((mul_piece mul_core (NoSp.of_all (by decide +kernel)) (by native_taint_decide)).pre_mono
    (fun _ h => MulPre.of_mul h) fun s s' _ _ h => by
      sig_pub [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have hp := MulPre.of_mul h₀
    refine Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; rw [← stk_eq hp.sp]; exact hp.stk_h.symm) ?_
    refine polyIs_of_toNat fun i hi => ?_
    rw [hinv.h i hi, ite_eq_left hi, mul_get _ _ hi, val_mul, polyAt_val hp.f_red hi, polyAt_val hp.g_red hi,
      newM, mulV, toNat_ofNat32 (mod_q_lt32 _)]
  · let st := satState mulSatMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 12⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 0x400 := by decide
    have a2 : arg st 2 = 0x800 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, reduced_below (mulSat_zero) 0x400 (by decide),
      reduced_below mulSat_zero 0x800 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

theorem mulAdd_verified : Verified X86.target mulAdd (mulAddContract X86.abi 16) := by
  refine Piece.verified ((((mul_piece mulAdd_core (NoSp.of_all (by decide +kernel)) (by native_taint_decide)).pre_mono
    (fun _ h => MulPre.of_mulAdd h) fun s s' _ _ h => by
      sig_pub [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h)).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have hp := MulPre.of_mulAdd h₀
    refine Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; rw [← stk_eq hp.sp]; exact hp.stk_h.symm) ?_
    have hr := hp.h_red rfl
    refine polyIs_of_toNat fun i hi => ?_
    rw [hinv.h i hi, ite_eq_left hi, add_get _ _ hi, val_add', mul_get _ _ hi, val_mul, polyAt_val hp.f_red hi,
      polyAt_val hp.g_red hi, polyAt_val hr hi, newM, mulAddV, Nat.add_comm (_ % q),
      toNat_ofNat32 (mod_q_lt32 _)]
  · let st := satState mulSatMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 12⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 0x400 := by decide
    have a2 : arg st 2 = 0x800 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, reduced_below mulSat_zero 0 (by decide),
      reduced_below mulSat_zero 0x400 (by decide), reduced_below mulSat_zero 0x800 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlDsa.X86.Arith

end

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_ntt`

The eight layers of Algorithm 41 (`ntt_eq_layers`), each a `layer_piece`
(`NttLoop.lean`) of the butterfly `bflyBody` (`bfly_spec`), with the zetas
from `zetas 1` up.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Arith.NttFwd

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_ ldScratch layerCode layers blockInit blockEnd zUp)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86.Arith
open VG.Proof.MlDsa.X86.Arith.NttLoop
open VG.Spec.MlDsa (q n Poly Zq zetas)
open VG.Proof.MlDsa (PolyIs Reduced coeffAt polyAt nttContract inPlaceContract inPlaceSig)
open VG.Proof.MlKem.X86 (E0 P0 frameR retR Piece LeafPost satState)

/-- The butterfly of Algorithm 41. -/
def bf : Bfly := ⟨bflyBody, bfly, bfly_spec⟩

/-- The table entry of block `c` of the layer with `len`. -/
def kf (len c : Nat) : Nat := 128 / len + c

theorem tab : TabOK montZetaTable zetas := fun _ hk => montZeta_eq hk

theorem lay (len B : Nat) (hB : len * B = 128) (hBp : 0 < B) (hk : 128 / len + B ≤ 256) (P : State → Poly)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp 20))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr []) (.block (blockInit len)) h₂).isSome = true)
    {h₃ : Taint.Hint VG.X86.Taint.T}
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block bflyBody) h₃).isSome = true)
    {h₄ : Taint.Hint VG.X86.Taint.T}
    (t₄ : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd zUp)) h₄).isSome = true) :
    Piece Pre Pub (fun s₀ s => LB s₀ montZetaTable (P s₀) (kf len 0) s)
      (fun s₀ s => LB s₀ montZetaTable (layerN bfly (P s₀) len (zf zetas kf len) B) (kf len B) s)
      (layerCode bflyBody zUp len) :=
  layer_piece bf montZetaTable zetas kf P tab true len B hB hBp (fun c _ => by simp [kf]; omega_using [])
    (fun c hc => by simp only [kf]; omega_using [hk, hc]) (fun h => absurd h (by decide)) t₁ t₂ t₃ t₄

/-- The input polynomial. -/
abbrev F (s₀ : State) : Poly := polyAt s₀.mem (fA s₀)

example : True := by
  have := lay 128 1 (by decide) (by decide) (by decide) F (by native_taint_decide) (by native_taint_decide)
    (by native_taint_decide) (by native_taint_decide)
  trivial

theorem fold_eq (f : Poly) : nttLens.foldl nttLayer f =
    nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (nttLayer f 128) 64) 32) 16) 8) 4) 2) 1 := by
  simp only [nttLens, List.foldl_cons, List.foldl_nil]

theorem layers_piece : Piece Pre Pub (fun s₀ s => LB s₀ montZetaTable (F s₀) 1 s)
    (fun s₀ s => LB s₀ montZetaTable (nttLens.foldl nttLayer (F s₀)) 256 s)
    (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2, 1]) := by
  refine Piece.seq (lay 128 1 (by decide) (by decide) (by decide) F (by native_taint_decide) (by native_taint_decide)
    (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 64 2 (by decide) (by decide) (by decide) (fun s₀ => nttLayer (F s₀) 128)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 32 4 (by decide) (by decide) (by decide)
    (fun s₀ => nttLayer (nttLayer (F s₀) 128) 64)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 16 8 (by decide) (by decide) (by decide)
    (fun s₀ => nttLayer (nttLayer (nttLayer (F s₀) 128) 64) 32)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 8 16 (by decide) (by decide) (by decide)
    (fun s₀ => nttLayer (nttLayer (nttLayer (nttLayer (F s₀) 128) 64) 32) 16)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 4 32 (by decide) (by decide) (by decide)
    (fun s₀ => nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (F s₀) 128) 64) 32) 16) 8)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 2 64 (by decide) (by decide) (by decide)
    (fun s₀ => nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (F s₀) 128) 64) 32) 16) 8) 4)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 1 128 (by decide) (by decide) (by decide)
    (fun s₀ => nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (nttLayer (F s₀) 128) 64) 32) 16)
      8) 4) 2)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  exact nil_piece.mono (fun _ _ _ h => h) fun s₀ _ _ h => by rw [fold_eq]; exact h

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀)
    (fun s₀ s => LB s₀ montZetaTable (nttLens.foldl nttLayer (F s₀)) 256 s)
    (.seq (.block ldScratch) (.seq (.block (nttSetup montZetaTable 1))
      (layers (layerCode bflyBody zUp) [128, 64, 32, 16, 8, 4, 2, 1]))) :=
  Piece.seq ld_piece (Piece.seq (setup_piece montZetaTable 1 (by native_taint_decide)) layers_piece)

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀)
    (fun s₀ s' => LeafPost (fun s => LB s₀ montZetaTable (nttLens.foldl nttLayer (F s₀)) 256 s) s₀ s')
    Impl.MlDsa.X86.Arith.ntt :=
  Piece.leaf W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega_using [this]⟩)
    (fun _ hp => hW hp) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.mem.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem verified : Verified X86.target Impl.MlDsa.X86.Arith.ntt (nttContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of (t := VG.Spec.MlDsa.ntt) h rfl) fun s s' _ _ h => by
      sig_pub [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [ntt_eq_layers]
    exact Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; exact (hW (Pre.of (t := VG.Spec.MlDsa.ntt) h₀ rfl) _ List.mem_cons_self).1.symm)
      hinv.mem.poly
  · let st := satState satMem [] [⟨0, 1024⟩, ⟨0x400, 1024⟩, ⟨0x5004, 8⟩]
    refine ⟨st, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [nttContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg st 0) = BitVec.ofNat 64 0 by decide]
           refine reduced_below (fun a ha => ?_) 0 (by decide)
           simp only [satMem]
           rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha])])
        | decide +kernel

end VG.Proof.MlDsa.X86.Arith.NttFwd

end

end

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_inv_ntt`

The eight layers of Algorithm 42 (`nttInv_eq_layers`), each a `layer_piece`
(`NttLoop.lean`) of the butterfly `ibflyBody` (`ibfly_spec`), with the negated
zetas from `zetas 255` down, then every coefficient times `8347681 = 256⁻¹ mod
q` (`scale_step`), by a Montgomery reduction of its product with `8347681` in
Montgomery form.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Arith.NttInvP

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_ ldScratch layerCode layers blockInit blockEnd zDown)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86.Arith
open VG.Proof.MlDsa.X86.Arith.NttLoop
open VG.Spec.MlDsa (q n Poly Zq zetas)
open VG.Proof.MlDsa (PolyIs Reduced coeffAt polyAt nttInvContract inPlaceContract inPlaceSig)
open VG.Proof.MlKem.X86 (Only E0 P0 P0_argAddr frameR retR Piece LeafPost satState wp_movm wp_mul ea_add
  ptr_next cnt_next cnt_ne toNat_ofNat32 eq_ofNat_of_toNat execMul_other)

/-- The butterfly of Algorithm 42. -/
def bf : Bfly := ⟨ibflyBody, bflyInv, ibfly_spec⟩

/-- The table entry of block `c` of the layer with `len`. -/
def kf (len c : Nat) : Nat := 256 / len - 1 - c

/-- The zetas of Algorithm 42, negated. -/
def zv (k : Nat) : Zq := -zetas k

theorem tab : TabOK montNegZetaTable zv := fun _ hk => montNegZeta_eq hk

theorem lay (len B : Nat) (hB : len * B = 128) (hBp : 0 < B) (hk : B + 1 ≤ 256 / len) (hk' : 256 / len ≤ 256)
    (P : State → Poly)
    {h₁ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (at_ .esp 20))]) h₁).isSome = true)
    {h₂ : Taint.Hint VG.X86.Taint.T}
    (t₂ : (VG.X86.taint.check (τr []) (.block (blockInit len)) h₂).isSome = true)
    {h₃ : Taint.Hint VG.X86.Taint.T}
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ebp, .ecx]) (.block ibflyBody) h₃).isSome = true)
    {h₄ : Taint.Hint VG.X86.Taint.T}
    (t₄ : (VG.X86.taint.check (τr [.esp]) (.block (blockEnd zDown)) h₄).isSome = true) :
    Piece Pre Pub (fun s₀ s => LB s₀ montNegZetaTable (P s₀) (kf len 0) s)
      (fun s₀ s => LB s₀ montNegZetaTable (layerN bflyInv (P s₀) len (zf zv kf len) B) (kf len B) s)
      (layerCode ibflyBody zDown len) :=
  layer_piece bf montNegZetaTable zv kf P tab false len B hB hBp (fun c _ => by simp only [kf]; simp; omega_arith)
    (fun c hc => by simp only [kf]; omega_arith) (fun _ c hc => by simp only [kf]; omega_arith) t₁ t₂ t₃ t₄

/-- The input polynomial. -/
abbrev F (s₀ : State) : Poly := polyAt s₀.mem (fA s₀)

theorem fold_eq (f : Poly) : nttInvLens.foldl nttInvLayer f =
    nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer f 1)
      2) 4) 8) 16) 32) 64) 128 := by
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil]

theorem layers_piece : Piece Pre Pub (fun s₀ s => LB s₀ montNegZetaTable (F s₀) 255 s)
    (fun s₀ s => LB s₀ montNegZetaTable (nttInvLens.foldl nttInvLayer (F s₀)) 0 s)
    (layers (layerCode ibflyBody zDown) [1, 2, 4, 8, 16, 32, 64, 128]) := by
  refine Piece.seq (lay 1 128 (by decide) (by decide) (by decide) (by decide) F (by native_taint_decide)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 2 64 (by decide) (by decide) (by decide) (by decide) (fun s₀ => nttInvLayer (F s₀) 1)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 4 32 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => nttInvLayer (nttInvLayer (F s₀) 1) 2)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 8 16 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => nttInvLayer (nttInvLayer (nttInvLayer (F s₀) 1) 2) 4)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 16 8 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (F s₀) 1) 2) 4) 8)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 32 4 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (F s₀) 1) 2) 4) 8) 16)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 64 2 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (F s₀) 1) 2) 4) 8)
      16) 32)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  refine Piece.seq (lay 128 1 (by decide) (by decide) (by decide) (by decide)
    (fun s₀ => nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (F s₀) 1)
      2) 4) 8) 16) 32) 64)
    (by native_taint_decide) (by native_taint_decide) (by native_taint_decide) (by native_taint_decide)) ?_
  exact nil_piece.mono (fun _ _ _ h => h) fun s₀ _ _ h => by rw [fold_eq]; exact h

/-! ## The scaling by `256⁻¹` -/

/-- The polynomial after the layers. -/
abbrev G (s₀ : State) : Poly := nttInvLens.foldl nttInvLayer (F s₀)

/-- `8347681`, the scaling factor, in `ℤ_q`. -/
abbrev c256 : Zq := 8347681

/-- After `k` coefficients are scaled. -/
structure SI (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = fP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  frame : Frame [polyRegion (fA s₀), polyRegion (sA s₀), aR s₀] (P0 s₀).mem s.mem
  f : ∀ i < 256, (coeffAt s.mem (fA s₀) i).toNat = if i < k then ((G s₀)[i]! * c256).val else ((G s₀)[i]!).val

theorem scaleImm_toNat : scaleImm.toNat = (8347681 : Nat) * 2 ^ 32 % q := rfl

theorem scaleBody_eq : scaleBody =
    .mov .eax (.mem (at_ .esi 0)) :: .mov .edx (.imm scaleImm) :: .mul .edx :: (mred .ebx ++
      ([.store (at_ .esi 0) .ebx, .alu .add .esi (.imm 4), .alu .sub .ecx (.imm 1)] : List Instr)) := by
  simp only [scaleBody, List.cons_append, List.nil_append]

theorem scale_step {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 256) {s : State} (h : SI s₀ k s) :
    WP isa (.block scaleBody) s fun s' => SI s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < n := hk
  have ef : s.ea (at_ .esi 0) = coeffAddr (fA s₀) k := by
    rw [State.ea, at_, h.esi]; exact ea_ptr hp.f_fit hk
  have ha := h.f k hk
  rw [ite_eq_right (Nat.lt_irrefl k)] at ha
  have la := val_lt (G s₀)[k]!
  rw [scaleBody_eq]
  refine wp_movm (by rw [ef]; exact inRd (hp.in_f h.wr hk)) (wp_movi (wp_mul ?_))
  have hx : (8347681 * 2 ^ 32 % q) < q := Nat.mod_lt _ (by decide)
  have hlt : ((G s₀)[k]!).val * (8347681 * 2 ^ 32 % q) < q * 2 ^ 32 := by
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt la hx) (by decide)
  refine mred_spec (r := .ebx) (by decide) (by decide) _ _ _ (x := ((G s₀)[k]!).val * (8347681 * 2 ^ 32 % q))
    ?_ hlt fun s₂ o₂ v₂ => ?_
  · rw [execMul_pair]
    simp only [State.setReg, ite_true, ite_false, reduceCtorEq]
    rw [ef, ← coeffAt_eq, ha, scaleImm_toNat]
  have g₂ : ∀ r, r ≠ .eax → r ≠ .edx → r ≠ .ebx → s₂.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [o₂.gpr r (by simp [h1, h2, h3]), execMul_other _ _ h1 h2]
    simp only [State.setReg, h1, h2, ite_false]
  have esi₂ := g₂ .esi (by decide) (by decide) (by decide)
  have ecx₂ := g₂ .ecx (by decide) (by decide) (by decide)
  have m₂ : s₂.mem = s.mem := by rw [o₂.mem]; rfl
  have rd₂ : s₂.rd = (P0 s₀).rd := by rw [o₂.rd]; exact h.rd
  have wr₂ : s₂.wr = (P0 s₀).wr := by rw [o₂.wr]; exact h.wr
  have hv : (s₂.gpr .ebx).toNat = ((G s₀)[k]! * c256).val := by
    rw [v₂, mont_mulR, val_mul]; rfl
  have out : InRegions s₂.wr (coeffAddr (fA s₀) k) 4 := hp.in_f wr₂ hk
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store32, State.setReg, arithFlags, State.setFlags, esi₂, h.esi,
    ea_ptr hp.f_fit hk, out, 
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by simp [g₂, h.esp], rd₂, wr₂, ?_, ?_, ?_, fun i hi => ?_⟩, ?_⟩
  · simp only [ite_true, ite_false, show Reg.esi ≠ Reg.ecx by decide]
    exact ptr_next _ _ 4
  · simp only [ite_true, ecx₂, h.ecx]
    exact cnt_next hk
  · rw [m₂]; exact h.frame.writeW (by simp) _ (coeff_contains _ hk')
  · dsimp only
    rw [coeffAt_writeW _ _ (show i < n from hi) hk', m₂]
    by_cases e : k = i
    · subst e; rw [ite_eq_left rfl, ite_eq_left (by omega_arith), hv]
    · rw [ite_eq_right e, h.f i hi]
      by_cases hik : i < k
      · rw [ite_eq_left hik, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right hik, ite_eq_right (by omega_arith)]
  · simp only [eval, ecx₂, h.ecx]
    exact cnt_ne hk (by decide)

theorem scale_piece : Piece Pre Pub (fun s₀ s => LB s₀ montNegZetaTable (G s₀) 0 s) (SI · 256)
    (.seq (.block [.mov .esi (.mem (at_ .esp 20))]) (.seq (.block [.mov .ecx (.imm 256)])
      (.loop (.block scaleBody) .ne))) := by
  refine Piece.seq (B := fun s₀ s => LB s₀ montNegZetaTable (G s₀) 0 s ∧ s.gpr .esi = fP s₀) ?_ ?_
  · refine Piece.taint [.esp] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) (by native_taint_decide)
    · have hsl : (s.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 0 := by
        rw [h.esp]; exact P0_argAddr s₀ 0
      have ins : InRegions (s.rd ++ s.wr) (argAddr s₀ 0) 4 := hp.in_a h.wr (by decide)
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some, State.setReg,
        State.ea, at_, State.load32, hsl, ins, h.mem.arg0, ite_true, Option.some.injEq, exists_eq_left']
      exact ⟨⟨by simp [h.esp], h.rd, h.wr, by simp [h.ebp], h.mem⟩, by simp⟩
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esp, h'.esp, pub_esp hq]
  refine Piece.seq (B := (SI · 0)) ?_ ?_
  · refine Piece.taint [.esp] (fun s₀ s hp ⟨h, hsi⟩ => ?_) (fun s₀ s₀' s s' _ _ hq ⟨h, _⟩ ⟨h', _⟩ r hr => ?_)
      (by native_taint_decide)
    · apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
        Option.some.injEq, exists_eq_left']
      refine ⟨by simp [State.setReg, h.esp], h.rd, h.wr, by simp [State.setReg, hsi], by simp [State.setReg],
        h.mem.frame, fun i hi => ?_⟩
      rw [ite_eq_right (Nat.not_lt_zero i), show (s.setReg .ecx 256).mem = s.mem from rfl, polyIs_toNat h.mem.poly hi]
    · simp only [List.mem_singleton] at hr
      subst hr
      rw [h.esp, h'.esp, pub_esp hq]
  · exact Piece.countLoop (by decide) (fun k s₀ s => SI s₀ k s) [.esp, .esi, .ecx] (fun k hk s₀ s hp h => scale_step hp hk h)
      (fun k _ s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.esp, h'.esp, pub_esp hq]
        · rw [h.esi, h'.esi, fP, fP, hq.2.1]
        · rw [h.ecx, h'.ecx]) (by native_taint_decide)

theorem body_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) (SI · 256)
    (.seq (.block ldScratch) (.seq (.block (nttSetup montNegZetaTable 255))
      (.seq (layers (layerCode ibflyBody zDown) [1, 2, 4, 8, 16, 32, 64, 128])
        (.seq (.block [.mov .esi (.mem (at_ .esp 20))])
          (.seq (.block [.mov .ecx (.imm 256)]) (.loop (.block scaleBody) .ne)))))) :=
  Piece.seq ld_piece (Piece.seq (setup_piece montNegZetaTable 255 (by native_taint_decide))
    (Piece.seq layers_piece scale_piece))

theorem piece : Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (SI s₀ 256) s₀ s')
    Impl.MlDsa.X86.Arith.nttInv :=
  Piece.leaf W (NoSp.of_all (by decide +kernel)) (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega_arith⟩)
    (fun _ hp => hW hp) (fun _ _ _ _ hq => hq.1)
    (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

theorem verified : Verified X86.target Impl.MlDsa.X86.Arith.nttInv (nttInvContract X86.abi 16) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => Pre.of (t := VG.Spec.MlDsa.nttInv) h rfl) fun s s' _ _ h => by
      sig_pub [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    refine Proof.MlDsa.Arith.polyIs_frame hm
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact (hW (Pre.of (t := VG.Spec.MlDsa.nttInv) h₀ rfl) _ List.mem_cons_self).1.symm) ?_
    rw [nttInv_eq_layers]
    refine polyIs_of_toNat fun i hi => ?_
    rw [hinv.f i hi, ite_eq_left hi, map_mul_get _ _ hi]
  · let st := satState satMem [] [⟨0, 1024⟩, ⟨0x400, 1024⟩, ⟨0x5004, 8⟩]
    refine ⟨st, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [nttInvContract, inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg st 0) = BitVec.ofNat 64 0 by decide]
           refine reduced_below (fun a ha => ?_) 0 (by decide)
           simp only [satMem]
           rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_arith)])
        | decide +kernel

end VG.Proof.MlDsa.X86.Arith.NttInvP
