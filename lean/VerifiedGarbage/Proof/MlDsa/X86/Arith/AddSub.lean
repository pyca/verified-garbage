import VerifiedGarbage.Proof.MlKem.X86.Mul
import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Arith.Basic`. -/
section

/-!
# ML-DSA on x86 (32-bit): the reductions modulo `q`

What the pieces of code of `Impl/MlDsa/X86/Arith/Basic.lean` compute: `csubQ`
reduces a value less than `2q` (`csubQ_eq`), and `mredRaw` and `mred` leave
the Montgomery reduction `mont x` (`Proof/MlDsa/Arith/Mont.lean`) of the
product `x` in `edx:eax` (`mredRaw_spec`, `mred_spec`).
-/

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q)
open VG.Proof.MlKem.X86 (Only wp_cons toNat_ofNat32 eq_ofNat_of_toNat E0 P0 frameR retR saveRegs_len
  execMul_eax execMul_other ea_add)

theorem qImm_toNat : qImm.toNat = q := rfl

theorem sub_val (x y : Spec.MlDsa.Zq) : (x - y).val = (x.val + q - y.val) % q := by
  rw [val_sub', show x.val + (q - y.val) = x.val + q - y.val by have := y.isLt; omega]

theorem mod_q_lt32 (x : Nat) : x % q < 2 ^ 32 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)

/-- `csubQ` as the code computes it, as a word. -/
theorem csubQ_eq (x d : BitVec 32) (hx : x.toNat < 2 * q) :
    x - qImm + ((d - d - (BitVec.ofBool (decide (x.toNat < qImm.toNat))).setWidth 32) &&& qImm) =
      BitVec.ofNat 32 (x.toNat % q) := by
  rw [VG.Proof.MlDsa.X86.Arith.qImm_toNat]
  apply BitVec.eq_of_toNat_eq
  rw [q_eq] at hx ⊢
  by_cases h : x.toNat < 8380417
  · rw [decide_eq_true h]
    have e : (d - d - (BitVec.ofBool true).setWidth 32) &&& qImm = qImm := by
      rw [BitVec.sub_self]; decide
    rw [e, BitVec.sub_add_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]
  · rw [decide_eq_false h]
    have e : (d - d - (BitVec.ofBool false).setWidth 32) &&& qImm = 0 := by
      rw [BitVec.sub_self]; decide
    rw [e, show x - qImm + 0 = x - qImm from BitVec.add_zero _, BitVec.toNat_sub, VG.Proof.MlDsa.X86.Arith.qImm_toNat, q_eq,
      BitVec.toNat_ofNat]
    omega

/-- The value `mredRaw` leaves, from the halves `hi` and `lo` of `x`. -/
theorem mredRaw_val (hi lo : BitVec 32) (hx : hi.toNat * 2 ^ 32 + lo.toNat < q * 2 ^ 32) :
    (hi + BitVec.ofNat 32 ((BitVec.ofNat 32 (lo.toNat * qInvImm.toNat)).toNat * qImm.toNat / 2 ^ 32) +
      BitVec.setWidth 32 (BitVec.ofBool (decide (2 ^ 32 ≤
        (BitVec.ofNat 32 ((BitVec.ofNat 32 (lo.toNat * qInvImm.toNat)).toNat * qImm.toNat)).toNat +
          BitVec.toNat (4294967295 : BitVec 32))))).toNat = mont (hi.toNat * 2 ^ 32 + lo.toNat) := by
  have hl := lo.isLt
  have hm : (BitVec.ofNat 32 (lo.toNat * qInvImm.toNat)).toNat = montM (hi.toNat * 2 ^ 32 + lo.toNat) := by
    rw [BitVec.toNat_ofNat, montM, Nat.mul_add_mod_of_lt hl]; rfl
  rw [hm, VG.Proof.MlDsa.X86.Arith.qImm_toNat, BitVec.toNat_ofNat, show BitVec.toNat (4294967295 : BitVec 32) = 4294967295 from rfl]
  have hlt := mont_lt hx
  rw [mont_halves] at hlt ⊢
  have e1 : (hi.toNat * 2 ^ 32 + lo.toNat) / 2 ^ 32 = hi.toNat := by omega
  rw [e1] at hlt ⊢
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  have hP := Nat.mod_lt (montM (hi.toNat * 2 ^ 32 + lo.toNat) * q) (show 0 < 2 ^ 32 by decide)
  obtain ⟨P, hPd⟩ : ∃ P, montM (hi.toNat * 2 ^ 32 + lo.toNat) * q = P := ⟨_, rfl⟩
  rw [hPd] at hlt hP ⊢
  rw [q_eq] at hlt
  have hh := hi.isLt
  by_cases hc : 1 ≤ P % 2 ^ 32
  · rw [decide_eq_true (by omega), ite_eq_left_of_eq_true _ _ (eq_true hc)] at *
    simp only [Bool.toNat_true] at *
    omega
  · rw [decide_eq_false (by omega), ite_eq_right_of_eq_false _ _ (eq_false hc)] at *
    simp only [Bool.toNat_false] at *
    omega

/-- `mredRaw r` leaves `mont x` in `r` from `x` in `edx:eax`, changing only
`eax`, `edx`, `r` and the flags. -/
theorem mredRaw_spec {r : Reg} (h1 : r ≠ .eax) (h2 : r ≠ .edx) (is : List Instr) (s : State)
    (P : State → Prop) {x : Nat} (hx : (s.gpr .edx).toNat * 2 ^ 32 + (s.gpr .eax).toNat = x)
    (hlt : x < q * 2 ^ 32)
    (k : ∀ s', Only [.eax, .edx, r] s s' → (s'.gpr r).toNat = mont x → WP isa (.block is) s' P) :
    WP isa (.block (mredRaw r ++ is)) s P := by
  have h2' : Reg.edx ≠ r := fun e => h2 e.symm
  have h1' : Reg.eax ≠ r := fun e => h1 e.symm
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, mredRaw, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, execMul, readSrc, State.setReg, arithFlags, State.setFlags,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', h1, h2,
    h1']
  refine k _ ⟨fun q hq => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp [hq.1, hq.2.1, hq.2.2]
  · simp only [ite_true]
    rw [← hx] at hlt ⊢
    exact VG.Proof.MlDsa.X86.Arith.mredRaw_val _ _ hlt

/-- `csubQ r t` reduces `r < 2q`, changing only `r`, `t` and the flags. -/
theorem csubQ_spec {r t : Reg} (h : r ≠ t) (is : List Instr) (s : State) (P : State → Prop)
    (hr : (s.gpr r).toNat < 2 * q)
    (k : ∀ s', Only [r, t] s s' → (s'.gpr r).toNat = (s.gpr r).toNat % q → WP isa (.block is) s' P) :
    WP isa (.block (csubQ r t ++ is)) s P := by
  have h' : t ≠ r := fun e => h e.symm
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reducePow, csubQ, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.setReg, arithFlags, State.setFlags, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left', h, h']
  refine k _ ⟨fun x hx => ?_, rfl, rfl, rfl⟩ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hx.1, hx.2]
  · simp only [ite_true]
    have := Nat.mod_lt (s.gpr r).toNat (show q > 0 by decide)
    rw [q_eq] at this
    rw [VG.Proof.MlDsa.X86.Arith.csubQ_eq _ _ hr, toNat_ofNat32 (by rw [q_eq]; omega)]

/-- `mred r` leaves `mont x mod q` in `r` from `x` in `edx:eax`, changing
only `eax`, `edx`, `r` and the flags. -/
theorem mred_spec {r : Reg} (h1 : r ≠ .eax) (h2 : r ≠ .edx) (is : List Instr) (s : State)
    (P : State → Prop) {x : Nat} (hx : (s.gpr .edx).toNat * 2 ^ 32 + (s.gpr .eax).toNat = x)
    (hlt : x < q * 2 ^ 32)
    (k : ∀ s', Only [.eax, .edx, r] s s' → (s'.gpr r).toNat = mont x % q → WP isa (.block is) s' P) :
    WP isa (.block (mred r ++ is)) s P := by
  rw [mred, List.append_assoc]
  refine VG.Proof.MlDsa.X86.Arith.mredRaw_spec h1 h2 _ s P hx hlt fun s₁ o₁ v₁ => ?_
  refine VG.Proof.MlDsa.X86.Arith.csubQ_spec h2 _ s₁ P (by rw [v₁]; exact mont_lt hlt) fun s₂ o₂ v₂ => ?_
  refine k s₂ ((o₁.trans o₂).mono fun y hy => ?_) (by rw [v₂, v₁])
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
  rcases hy with (e | e | e) | (e | e) <;> simp [e]

/-! ## Products -/

theorem execMul_edx (r : Reg) (s : State) :
    (execMul r s).gpr .edx = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat / 2 ^ 32) := by
  simp [execMul, State.setReg, State.setFlags]

/-- `mul r` leaves the product in `edx:eax`. -/
theorem execMul_pair (r : Reg) (s : State) :
    ((execMul r s).gpr .edx).toNat * 2 ^ 32 + ((execMul r s).gpr .eax).toNat =
      (s.gpr .eax).toNat * (s.gpr r).toNat := by
  rw [VG.Proof.MlDsa.X86.Arith.execMul_edx, execMul_eax, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := Nat.mul_lt_mul_of_lt_of_lt (s.gpr .eax).isLt (s.gpr r).isLt
  generalize (s.gpr .eax).toNat * (s.gpr r).toNat = p at this ⊢
  omega

/-- `mov d, imm` -/
theorem wp_movi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : WP isa (.block is) (s.setReg d v) Q) : WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  wp_cons (by simp only [exec, readSrc, Option.map_some]) k

/-! ## Memory -/

theorem polyLen (p : Addr) : (polyRegion p).len ≤ 2 ^ 64 := by show 1024 ≤ 2 ^ 64; decide

/-- The stack below the return address, as the contracts state it, is the leaf's frame. -/
theorem stk_eq {s₀ : State} (h : 16 ≤ (E0 s₀).toNat) :
    (⟨(E0 s₀).setWidth 64 - 16#64, 16⟩ : Region) = frameR s₀ := by
  simp only [frameR, below]; rw [Taint.sub_setWidth h]

/-- The push changes nothing of a region apart from the frame. -/
theorem P0_mem {s₀ : State} (h : 16 ≤ (E0 s₀).toNat) : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := Impl.MlKem.X86.saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact h)
  rw [saveRegs_len] at hf
  exact hf

/-- Coefficient `k` at the pointer `x + 4k`. -/
theorem ea_ptr {x : BitVec 32} (hx : x.toNat + 1024 ≤ 2 ^ 32) {k : Nat} (hk : k < 256) :
    (x + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (x.setWidth 64) k := by
  rw [ea_add (by omega), Nat.add_zero]

/-- All-zero memory holds a reduced polynomial. -/
theorem reduced_of_zero {m : Mem} {p : Addr} (h : ∀ k < 1024, m (p + BitVec.ofNat 64 k) = 0) :
    Spec.MlDsa.Reduced m p := fun i hi => by
  rw [coeffAt_congr (m' := m) (m := fun _ => 0) (fun k hk => h k hk) hi]
  simp [Spec.MlDsa.coeffAt, Mem.readW, Mem.read]

/-- Memory that is zero below `0x5000` holds reduced polynomials there. -/
theorem reduced_below {m : Mem} (hm : ∀ a : Addr, a.toNat < 0x5000 → m a = 0) (p : Nat)
    (hp : p + 1024 ≤ 0x5000) : Spec.MlDsa.Reduced m (BitVec.ofNat 64 p) :=
  VG.Proof.MlDsa.X86.Arith.reduced_of_zero fun k hk => hm _ (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega)

end VG.Proof.MlDsa.X86.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86.Arith.AddSub`. -/
section

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_add` and `vg_mldsa_sub`

Both are `Impl.MlKem.X86.mapLoop` around an arithmetic step; the loop is
proven once for any step that computes a function `F` of the two coefficients
(`OpSpec`), as for ML-KEM on x86.
-/

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_ leaf mapLoop mapBody mapInit)
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa
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

theorem addOp_spec : VG.Proof.MlDsa.X86.Arith.OpSpec addOp fun a b => (a + b) % q := by
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
    rw [BitVec.toNat_add, h₁, h₂', Nat.mod_eq_of_lt (by rw [q_eq] at ha hb; omega)]
  refine VG.Proof.MlDsa.X86.Arith.csubQ_spec (by decide) is _ P (by simp only [State.setReg, ite_true]; rw [e]; omega)
    fun s' o v => k s' ⟨fun r hr => ?_, o.mem, o.rd, o.wr⟩ ?_
  · rw [o.gpr r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [State.setReg, arithFlags, State.setFlags, hr.1]
  · rw [v]; simp only [State.setReg, ite_true]; rw [e]

theorem subOp_spec : VG.Proof.MlDsa.X86.Arith.OpSpec subOp fun a b => (a + q - b) % q := by
  intro is s P a b ha hb h₁ hin h₂ k
  have hin' : InRegions (s.rd ++ s.wr) ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 4 := hin
  have h₂' : (s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32).toNat = b := h₂
  rw [subOp, List.cons_append, List.cons_append]
  set B := s.mem.readW ((s.gpr .edi + BitVec.ofNat 32 0).setWidth 64) 32 with hB
  set A := s.gpr .eax + qImm with hA
  refine wp_cons (s' := (arithFlags s A (2 ^ 32 ≤ (s.gpr .eax).toNat + qImm.toNat)
    (addOverflow (s.gpr .eax) qImm A)).setReg .eax A)
    (by simp only [exec, execAlu, readSrc, Option.bind_some]; rfl) ?_
  refine wp_cons (s' := (arithFlags ((arithFlags s A (2 ^ 32 ≤ (s.gpr .eax).toNat + qImm.toNat)
    (addOverflow (s.gpr .eax) qImm A)).setReg .eax A) (A - B) (A.toNat < B.toNat) (subOverflow A B (A - B))).setReg
    .eax (A - B))
    (by simp only [exec, execAlu, readSrc, State.ea, at_, State.load32, State.setReg, arithFlags, State.setFlags,
      hin', ite_true, ite_false, Option.bind_some, reduceCtorEq]; rfl) ?_
  have hA' : A.toNat = a + q := by
    rw [hA, BitVec.toNat_add, h₁, VG.Proof.MlDsa.X86.Arith.qImm_toNat, Nat.mod_eq_of_lt (by rw [q_eq] at ha ⊢; omega)]
  have e : (A - B).toNat = a + q - b := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hA', h₂']; omega), hA', h₂']
  refine VG.Proof.MlDsa.X86.Arith.csubQ_spec (by decide) is _ P (by simp only [State.setReg, ite_true]; rw [e]; omega)
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
abbrev fA : Addr := (VG.Proof.MlDsa.X86.Arith.fP s₀).setWidth 64
abbrev gA : Addr := (VG.Proof.MlDsa.X86.Arith.gP s₀).setWidth 64
abbrev aR2 : Region := ⟨argAddr s₀ 0, 8⟩
/-- The stack below the return address, as the contract states it. -/
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
end

structure AccPre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (VG.Proof.MlDsa.X86.Arith.gA s₀)]
  wr : s₀.wr = [polyRegion (VG.Proof.MlDsa.X86.Arith.fA s₀), VG.Proof.MlDsa.X86.Arith.aR2 s₀]
  f_g : (polyRegion (VG.Proof.MlDsa.X86.Arith.fA s₀)).Disjoint (polyRegion (VG.Proof.MlDsa.X86.Arith.gA s₀))
  f_a : (polyRegion (VG.Proof.MlDsa.X86.Arith.fA s₀)).Disjoint (VG.Proof.MlDsa.X86.Arith.aR2 s₀)
  g_a : (polyRegion (VG.Proof.MlDsa.X86.Arith.gA s₀)).Disjoint (VG.Proof.MlDsa.X86.Arith.aR2 s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (VG.Proof.MlDsa.X86.Arith.fA s₀))
  ret_g : (retR s₀).Disjoint (polyRegion (VG.Proof.MlDsa.X86.Arith.gA s₀))
  ret_a : (retR s₀).Disjoint (VG.Proof.MlDsa.X86.Arith.aR2 s₀)
  stk_f : (VG.Proof.MlDsa.X86.Arith.stkR s₀).Disjoint (polyRegion (VG.Proof.MlDsa.X86.Arith.fA s₀))
  stk_g : (VG.Proof.MlDsa.X86.Arith.stkR s₀).Disjoint (polyRegion (VG.Proof.MlDsa.X86.Arith.gA s₀))
  stk_a : (VG.Proof.MlDsa.X86.Arith.stkR s₀).Disjoint (VG.Proof.MlDsa.X86.Arith.aR2 s₀)
  f_fit : (VG.Proof.MlDsa.X86.Arith.fP s₀).toNat + 1024 ≤ 2 ^ 32
  g_fit : (VG.Proof.MlDsa.X86.Arith.gP s₀).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (VG.Proof.MlDsa.X86.Arith.fA s₀)
  g_red : Reduced s₀.mem (VG.Proof.MlDsa.X86.Arith.gA s₀)

theorem AccPre.of_add {s₀ : State} (h : (addContract X86.abi 16).pre s₀) : VG.Proof.MlDsa.X86.Arith.AccPre s₀ := by
  sig_pre [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem AccPre.of_sub {s₀ : State} (h : (subContract X86.abi 16).pre s₀) : VG.Proof.MlDsa.X86.Arith.AccPre s₀ := by
  sig_pre [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

/-! ## The loop -/

/-- The new value of coefficient `i`. -/
def newC (F : Nat → Nat → Nat) (s₀ : State) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (F (coeffAt s₀.mem (VG.Proof.MlDsa.X86.Arith.fA s₀) i).toNat (coeffAt s₀.mem (VG.Proof.MlDsa.X86.Arith.gA s₀) i).toNat)

/-- After `k` coefficients. -/
structure MapInv (F : Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  esi : s.gpr .esi = VG.Proof.MlDsa.X86.Arith.fP s₀ + BitVec.ofNat 32 (4 * k)
  edi : s.gpr .edi = VG.Proof.MlDsa.X86.Arith.gP s₀ + BitVec.ofNat 32 (4 * k)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (256 - k)
  frame : Frame [polyRegion (VG.Proof.MlDsa.X86.Arith.fA s₀)] (P0 s₀).mem s.mem
  f : ∀ i < 256, coeffAt s.mem (VG.Proof.MlDsa.X86.Arith.fA s₀) i = if i < k then VG.Proof.MlDsa.X86.Arith.newC F s₀ i else coeffAt s₀.mem (VG.Proof.MlDsa.X86.Arith.fA s₀) i

namespace AccPre
variable {s₀ : State} (hp : VG.Proof.MlDsa.X86.Arith.AccPre s₀)
include hp

theorem in_f {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions s.wr (coeffAddr (VG.Proof.MlDsa.X86.Arith.fA s₀) k) 4 := by
  rw [hw, P0_wr, hp.wr]
  exact ⟨polyRegion (VG.Proof.MlDsa.X86.Arith.fA s₀), by simp, coeff_contains _ hk⟩

theorem in_f' {s : State} (hw : s.wr = (P0 s₀).wr) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (VG.Proof.MlDsa.X86.Arith.fA s₀) k) 4 :=
  let ⟨r, h, c⟩ := hp.in_f hw hk; ⟨r, List.mem_append_right _ h, c⟩

theorem in_g {s : State} (hr : s.rd = (P0 s₀).rd) {k : Nat} (hk : k < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (VG.Proof.MlDsa.X86.Arith.gA s₀) k) 4 := by
  rw [hr, pushed_rd, hp.rd]
  exact ⟨polyRegion (VG.Proof.MlDsa.X86.Arith.gA s₀), by simp, coeff_contains _ hk⟩

/-- `g` is never written. -/
theorem g_keep {s : State} (hf : Frame [polyRegion (VG.Proof.MlDsa.X86.Arith.fA s₀)] (P0 s₀).mem s.mem) {i : Nat} (hi : i < 256) :
    coeffAt s.mem (VG.Proof.MlDsa.X86.Arith.gA s₀) i = coeffAt s₀.mem (VG.Proof.MlDsa.X86.Arith.gA s₀) i := by
  have f₁ := VG.Proof.MlDsa.X86.Arith.P0_mem hp.sp
  rw [coeffAt_congr (m := s₀.mem) (m' := s.mem) (fun j hj => ?_) hi]
  rw [hf.bytes (R := polyRegion (VG.Proof.MlDsa.X86.Arith.gA s₀)) (by simpa using hp.f_g.symm) (VG.Proof.MlDsa.X86.Arith.polyLen _) hj,
    f₁.bytes (R := polyRegion (VG.Proof.MlDsa.X86.Arith.gA s₀)) (by simpa [← VG.Proof.MlDsa.X86.Arith.stk_eq hp.sp] using hp.stk_g.symm) (VG.Proof.MlDsa.X86.Arith.polyLen _) hj]

theorem f_P0 {i : Nat} (hi : i < 256) : coeffAt (P0 s₀).mem (VG.Proof.MlDsa.X86.Arith.fA s₀) i = coeffAt s₀.mem (VG.Proof.MlDsa.X86.Arith.fA s₀) i :=
  coeffAt_congr (fun j hj => (VG.Proof.MlDsa.X86.Arith.P0_mem hp.sp).bytes (R := polyRegion (VG.Proof.MlDsa.X86.Arith.fA s₀))
    (by simpa [← VG.Proof.MlDsa.X86.Arith.stk_eq hp.sp] using hp.stk_f.symm) (VG.Proof.MlDsa.X86.Arith.polyLen _) hj) hi

theorem ea_f (k : Nat) (hk : k < 256) :
    (VG.Proof.MlDsa.X86.Arith.fP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (VG.Proof.MlDsa.X86.Arith.fA s₀) k := by
  rw [ea_add (by have := hp.f_fit; omega), Nat.add_zero]

theorem ea_g (k : Nat) (hk : k < 256) :
    (VG.Proof.MlDsa.X86.Arith.gP s₀ + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (VG.Proof.MlDsa.X86.Arith.gA s₀) k := by
  rw [ea_add (by have := hp.g_fit; omega), Nat.add_zero]

end AccPre

theorem map_step {op : List Instr} {F : Nat → Nat → Nat} (hop : VG.Proof.MlDsa.X86.Arith.OpSpec op F) {s₀ : State} (hp : VG.Proof.MlDsa.X86.Arith.AccPre s₀)
    {k : Nat} (hk : k < 256) {s : State} (h : VG.Proof.MlDsa.X86.Arith.MapInv F s₀ k s) :
    WP isa (.block (mapBody op)) s fun s' =>
      VG.Proof.MlDsa.X86.Arith.MapInv F s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 256)) := by
  have hk' : k < n := hk
  have ef : s.ea (at_ .esi 0) = coeffAddr (VG.Proof.MlDsa.X86.Arith.fA s₀) k := by
    rw [State.ea, at_, h.esi]; exact hp.ea_f k hk
  refine wp_movm (by rw [ef]; exact hp.in_f' h.wr hk) ?_
  set s₁ := s.setReg .eax (s.mem.readW (s.ea (at_ .esi 0)) 32) with hs₁
  have ha : (coeffAt s₀.mem (VG.Proof.MlDsa.X86.Arith.fA s₀) k).toNat < q := hp.f_red k hk'
  have hb : (coeffAt s₀.mem (VG.Proof.MlDsa.X86.Arith.gA s₀) k).toNat < q := hp.g_red k hk'
  have eg : s₁.ea (at_ .edi 0) = coeffAddr (VG.Proof.MlDsa.X86.Arith.gA s₀) k := by
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
  have esi₂ : s₂.gpr .esi = VG.Proof.MlDsa.X86.Arith.fP s₀ + BitVec.ofNat 32 (4 * k) := by rw [g₂ _ (by decide) (by decide), h.esi]
  have edi₂ : s₂.gpr .edi = VG.Proof.MlDsa.X86.Arith.gP s₀ + BitVec.ofNat 32 (4 * k) := by rw [g₂ _ (by decide) (by decide), h.edi]
  have ecx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (256 - k) := by rw [g₂ _ (by decide) (by decide), h.ecx]
  have out : InRegions s₂.wr (coeffAddr (VG.Proof.MlDsa.X86.Arith.fA s₀) k) 4 := hp.in_f w₂ hk
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store32, State.setReg, arithFlags, State.setFlags, esi₂,
    hp.ea_f k hk, out, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hv : s₂.gpr .eax = VG.Proof.MlDsa.X86.Arith.newC F s₀ k := eq_ofNat_of_toNat v₂
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
      · rw [ite_eq_left hik, ite_eq_left (by omega)]
      · rw [ite_eq_right hik, ite_eq_right (by omega)]
  · simp only [eval, ecx₂]
    exact cnt_ne hk (by decide)

/-! ## The function -/

/-- The public data: the stack pointer and the pointers. -/
def AccPub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

/-- The arguments, which the push leaves in place. -/
theorem AccPre.arg_P0 {s₀ : State} (hp : VG.Proof.MlDsa.X86.Arith.AccPre s₀) {i : Nat} (hi : i < 2) :
    ((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      InRegions ((P0 s₀).rd ++ (P0 s₀).wr) (argAddr s₀ i) 4 ∧
      (P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hc : (VG.Proof.MlDsa.X86.Arith.aR2 s₀).Contains (argAddr s₀ i) 4 := by
    have := hp.sp'
    simp only [argAddr, Region.Contains, E0] at this ⊢
    bv_omega
  refine ⟨?_, ⟨VG.Proof.MlDsa.X86.Arith.aR2 s₀, by simp [hp.wr], hc⟩, ?_⟩
  · rw [P0_esp]; simp only [argAddr, E0]; congr 1; bv_omega
  · exact (VG.Proof.MlDsa.X86.Arith.P0_mem hp.sp).readW hc (by simpa [← VG.Proof.MlDsa.X86.Arith.stk_eq hp.sp] using hp.stk_a.symm) (by decide)

theorem init_piece (F : Nat → Nat → Nat) :
    Piece VG.Proof.MlDsa.X86.Arith.AccPre VG.Proof.MlDsa.X86.Arith.AccPub (fun s₀ s => s = P0 s₀) (VG.Proof.MlDsa.X86.Arith.MapInv F · 0) (.block mapInit) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    obtain ⟨a₀, i₀, v₀⟩ := hp.arg_P0 (i := 0) (by omega)
    obtain ⟨a₁, i₁, v₁⟩ := hp.arg_P0 (i := 1) (by omega)
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

theorem loop_piece {op : List Instr} {F : Nat → Nat → Nat} (hop : VG.Proof.MlDsa.X86.Arith.OpSpec op F)
    {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (mapBody op)) hc).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Arith.AccPre VG.Proof.MlDsa.X86.Arith.AccPub (VG.Proof.MlDsa.X86.Arith.MapInv F · 0) (VG.Proof.MlDsa.X86.Arith.MapInv F · 256) (.loop (.block (mapBody op)) .ne) :=
  Piece.loop (fun k s₀ s => VG.Proof.MlDsa.X86.Arith.MapInv F s₀ k s) (by decide) fun k hk =>
    Piece.taint [.esp, .esi, .edi, .ecx] (fun _ _ hp h => VG.Proof.MlDsa.X86.Arith.map_step hop hp hk h)
      (fun s₀ s₀' s s' _ _ hq h h' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.esp, h'.esp, P0_esp, P0_esp, hq.1]
        · rw [h.esi, h'.esi, VG.Proof.MlDsa.X86.Arith.fP, VG.Proof.MlDsa.X86.Arith.fP, hq.2.1]
        · rw [h.edi, h'.edi, VG.Proof.MlDsa.X86.Arith.gP, VG.Proof.MlDsa.X86.Arith.gP, hq.2.2]
        · rw [h.ecx, h'.ecx]) ht

theorem map_piece {op : List Instr} {F : Nat → Nat → Nat} (hop : VG.Proof.MlDsa.X86.Arith.OpSpec op F)
    (hsp : NoSp (mapLoop op)) {hc : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .esi, .edi, .ecx]) (.block (mapBody op)) hc).isSome = true) :
    Piece VG.Proof.MlDsa.X86.Arith.AccPre VG.Proof.MlDsa.X86.Arith.AccPub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlDsa.X86.Arith.MapInv F s₀ 256) s₀ s')
      (leaf (mapLoop op)) :=
  Piece.leaf (fun s₀ => [polyRegion (VG.Proof.MlDsa.X86.Arith.fA s₀)]) hsp (fun _ hp => ⟨hp.sp, by have := hp.sp'; omega⟩)
    (fun _ hp r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨by rw [← VG.Proof.MlDsa.X86.Arith.stk_eq hp.sp]; exact hp.stk_f, hp.ret_f⟩)
    (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (VG.Proof.MlDsa.X86.Arith.init_piece F) (VG.Proof.MlDsa.X86.Arith.loop_piece hop ht)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr⟩, h⟩)

/-- The polynomial the loop leaves. -/
theorem map_post {F : Nat → Nat → Nat} {G : Zq → Zq → Zq} (hG : ∀ x y : Zq, (G x y).val = F x.val y.val)
    {s₀ s : State} (hp : VG.Proof.MlDsa.X86.Arith.AccPre s₀) (h : VG.Proof.MlDsa.X86.Arith.MapInv F s₀ 256 s) :
    PolyIs s.mem (VG.Proof.MlDsa.X86.Arith.fA s₀) (Vector.zipWith G (polyAt s₀.mem (VG.Proof.MlDsa.X86.Arith.fA s₀)) (polyAt s₀.mem (VG.Proof.MlDsa.X86.Arith.gA s₀))) := by
  refine polyIs_of_toNat fun i hi => ?_
  have hlt := val_lt (G (polyAt s₀.mem (VG.Proof.MlDsa.X86.Arith.fA s₀))[i]! (polyAt s₀.mem (VG.Proof.MlDsa.X86.Arith.gA s₀))[i]!)
  rw [hG, polyAt_val hp.f_red hi, polyAt_val hp.g_red hi] at hlt
  rw [h.f i hi, ite_eq_left hi, getElem!_eq _ hi, Vector.getElem_zipWith, ← getElem!_eq _ hi,
    ← getElem!_eq _ hi, hG, polyAt_val hp.f_red hi, polyAt_val hp.g_red hi, VG.Proof.MlDsa.X86.Arith.newC, toNat_ofNat32 (by omega)]

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
  mem := VG.Proof.MlDsa.X86.Arith.accSatMem
  rd := [⟨0x400, 1024⟩]
  wr := [⟨0, 1024⟩, ⟨0x5004, 8⟩]

theorem accSat_red (p : Nat) (hp : p + 1024 ≤ 0x5000) : Reduced VG.Proof.MlDsa.X86.Arith.accSatMem (BitVec.ofNat 64 p) :=
  VG.Proof.MlDsa.X86.Arith.reduced_below (fun a ha => by
    simp only [VG.Proof.MlDsa.X86.Arith.accSatMem]
    rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega)]) p hp

theorem add_verified : Verified X86.target add (addContract X86.abi 16) := by
  refine Piece.verified (((VG.Proof.MlDsa.X86.Arith.map_piece VG.Proof.MlDsa.X86.Arith.addOp_spec (NoSp.of_all (by decide +kernel)) (by taint_decide)).pre_mono
    (fun _ h => AccPre.of_add h) fun s s' _ _ h => by
      sig_pub [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact VG.Proof.MlDsa.X86.Arith.map_post (G := (· + ·)) (fun x y => val_add' x y) (AccPre.of_add h₀) hinv
  · refine ⟨VG.Proof.MlDsa.X86.Arith.accSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [addContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg VG.Proof.MlDsa.X86.Arith.accSat 0) = BitVec.ofNat 64 0 by decide]
           exact VG.Proof.MlDsa.X86.Arith.accSat_red 0 (by decide))
        | (rw [show BitVec.setWidth 64 (arg VG.Proof.MlDsa.X86.Arith.accSat 1) = BitVec.ofNat 64 0x400 by decide]
           exact VG.Proof.MlDsa.X86.Arith.accSat_red 0x400 (by decide))
        | decide +kernel

theorem sub_verified : Verified X86.target sub (subContract X86.abi 16) := by
  refine Piece.verified (((VG.Proof.MlDsa.X86.Arith.map_piece VG.Proof.MlDsa.X86.Arith.subOp_spec (NoSp.of_all (by decide +kernel)) (by taint_decide)).pre_mono
    (fun _ h => AccPre.of_sub h) fun s s' _ _ h => by
      sig_pub [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm, -⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [hm]
    exact VG.Proof.MlDsa.X86.Arith.map_post (G := (· - ·)) VG.Proof.MlDsa.X86.Arith.sub_val (AccPre.of_sub h₀) hinv
  · refine ⟨VG.Proof.MlDsa.X86.Arith.accSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [subContract, accSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      sig_and_intros
      all_goals first
        | trivial
        | (rw [show BitVec.setWidth 64 (arg VG.Proof.MlDsa.X86.Arith.accSat 0) = BitVec.ofNat 64 0 by decide]
           exact VG.Proof.MlDsa.X86.Arith.accSat_red 0 (by decide))
        | (rw [show BitVec.setWidth 64 (arg VG.Proof.MlDsa.X86.Arith.accSat 1) = BitVec.ofNat 64 0x400 by decide]
           exact VG.Proof.MlDsa.X86.Arith.accSat_red 0x400 (by decide))
        | decide +kernel

end VG.Proof.MlDsa.X86.Arith

end
