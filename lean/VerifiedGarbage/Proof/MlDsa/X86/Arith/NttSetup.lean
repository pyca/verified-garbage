module

import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Ntt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlKem.X86.Red
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.MlKem.X86.Leaf
meta import VerifiedGarbage.Proof.MlDsa.Arith.Ntt
meta import VerifiedGarbage.Impl.MlDsa.X86.Arith.Ntt
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlKem.X86.Red
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.MlKem.X86.Leaf
public import VerifiedGarbage.Proof.MlKem.X86.Common
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.Reduce
meta import VerifiedGarbage.Proof.MlKem.X86.Common
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Reduce
public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.Arith.Mont
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Impl.MlDsa.X86.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mont

/-! ### `MlDsa.X86.Arith.Basic`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86 (32-bit): the reductions modulo `q`

What the pieces of code of `Impl/MlDsa/X86/Arith/Basic.lean` compute: `csubQ`
reduces a value less than `2q` (`csubQ_eq`), and `mredRaw` and `mred` leave
the Montgomery reduction `mont x` (`Proof/MlDsa/Arith/Mont.lean`) of the
product `x` in `edx:eax` (`mredRaw_spec`, `mred_spec`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q)
open VG.Proof.MlKem.X86 (Only wp_cons toNat_ofNat32 eq_ofNat_of_toNat E0 P0 frameR retR saveRegs_len
  execMul_eax execMul_other ea_add)

theorem qImm_toNat : qImm.toNat = q := rfl

theorem sub_val (x y : Spec.MlDsa.Zq) : (x - y).val = (x.val + q - y.val) % q := by
  rw [val_sub', show x.val + (q - y.val) = x.val + q - y.val by have := y.isLt; omega_using []]

theorem mod_q_lt32 (x : Nat) : x % q < 2 ^ 32 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)

/-- `csubQ` as the code computes it, as a word. -/
theorem csubQ_eq (x d : BitVec 32) (hx : x.toNat < 2 * q) :
    x - qImm + ((d - d - (BitVec.ofBool (decide (x.toNat < qImm.toNat))).setWidth 32) &&& qImm) =
      BitVec.ofNat 32 (x.toNat % q) := by
  rw [qImm_toNat]
  apply BitVec.eq_of_toNat_eq
  rw [q_eq] at hx ⊢
  by_cases h : x.toNat < 8380417
  · rw [decide_eq_true h]
    have e : (d - d - (BitVec.ofBool true).setWidth 32) &&& qImm = qImm := by
      rw [BitVec.sub_self]; decide
    rw [e, BitVec.sub_add_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_using [])]
  · rw [decide_eq_false h]
    have e : (d - d - (BitVec.ofBool false).setWidth 32) &&& qImm = 0 := by
      rw [BitVec.sub_self]; decide
    rw [e, show x - qImm + 0 = x - qImm from BitVec.add_zero _, BitVec.toNat_sub, qImm_toNat, q_eq,
      BitVec.toNat_ofNat]
    omega_using [hx, h]

/-- The value `mredRaw` leaves, from the halves `hi` and `lo` of `x`. -/
theorem mredRaw_val (hi lo : BitVec 32) (hx : hi.toNat * 2 ^ 32 + lo.toNat < q * 2 ^ 32) :
    (hi + BitVec.ofNat 32 ((BitVec.ofNat 32 (lo.toNat * qInvImm.toNat)).toNat * qImm.toNat / 2 ^ 32) +
      BitVec.setWidth 32 (BitVec.ofBool (decide (2 ^ 32 ≤
        (BitVec.ofNat 32 ((BitVec.ofNat 32 (lo.toNat * qInvImm.toNat)).toNat * qImm.toNat)).toNat +
          BitVec.toNat (4294967295 : BitVec 32))))).toNat = mont (hi.toNat * 2 ^ 32 + lo.toNat) := by
  have hl := lo.isLt
  have hm : (BitVec.ofNat 32 (lo.toNat * qInvImm.toNat)).toNat = montM (hi.toNat * 2 ^ 32 + lo.toNat) := by
    rw [BitVec.toNat_ofNat, montM, Nat.mul_add_mod_of_lt hl]; rfl
  rw [hm, qImm_toNat, BitVec.toNat_ofNat, show BitVec.toNat (4294967295 : BitVec 32) = 4294967295 from rfl]
  have hlt := mont_lt hx
  rw [mont_halves] at hlt ⊢
  have e1 : (hi.toNat * 2 ^ 32 + lo.toNat) / 2 ^ 32 = hi.toNat := by omega_using []
  rw [e1] at hlt ⊢
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofBool]
  have hP := Nat.mod_lt (montM (hi.toNat * 2 ^ 32 + lo.toNat) * q) (show 0 < 2 ^ 32 by decide)
  obtain ⟨P, hPd⟩ : ∃ P, montM (hi.toNat * 2 ^ 32 + lo.toNat) * q = P := ⟨_, rfl⟩
  rw [hPd] at hlt hP ⊢
  rw [q_eq] at hlt
  have hh := hi.isLt
  by_cases hc : 1 ≤ P % 2 ^ 32
  · rw [decide_eq_true (by omega_using [hc]), ite_eq_left_of_eq_true _ _ (eq_true hc)] at *
    simp only [Bool.toNat_true] at *
    omega_using [hlt]
  · rw [decide_eq_false (by omega_using [hc]), ite_eq_right_of_eq_false _ _ (eq_false hc)] at *
    simp only [Bool.toNat_false] at *
    omega_using [hlt]

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
    exact mredRaw_val _ _ hlt

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
    rw [csubQ_eq _ _ hr, toNat_ofNat32 (by rw [q_eq]; omega_using [])]

/-- `mred r` leaves `mont x mod q` in `r` from `x` in `edx:eax`, changing
only `eax`, `edx`, `r` and the flags. -/
theorem mred_spec {r : Reg} (h1 : r ≠ .eax) (h2 : r ≠ .edx) (is : List Instr) (s : State)
    (P : State → Prop) {x : Nat} (hx : (s.gpr .edx).toNat * 2 ^ 32 + (s.gpr .eax).toNat = x)
    (hlt : x < q * 2 ^ 32)
    (k : ∀ s', Only [.eax, .edx, r] s s' → (s'.gpr r).toNat = mont x % q → WP isa (.block is) s' P) :
    WP isa (.block (mred r ++ is)) s P := by
  rw [mred, List.append_assoc]
  refine mredRaw_spec h1 h2 _ s P hx hlt fun s₁ o₁ v₁ => ?_
  refine csubQ_spec h2 _ s₁ P (by rw [v₁]; exact mont_lt hlt) fun s₂ o₂ v₂ => ?_
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
  rw [execMul_edx, execMul_eax, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have := Nat.mul_lt_mul_of_lt_of_lt (s.gpr .eax).isLt (s.gpr r).isLt
  generalize (s.gpr .eax).toNat * (s.gpr r).toNat = p at this ⊢
  omega_using [this]

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
  rw [ea_add (by omega_using [hx, hk]), Nat.add_zero]

/-- All-zero memory holds a reduced polynomial. -/
theorem reduced_of_zero {m : Mem} {p : Addr} (h : ∀ k < 1024, m (p + BitVec.ofNat 64 k) = 0) :
    Proof.MlDsa.Reduced m p := fun i hi => by
  rw [coeffAt_congr (m' := m) (m := fun _ => 0) (fun k hk => h k hk) hi]
  simp [Proof.MlDsa.coeffAt, Mem.readW, Mem.read]

/-- Memory that is zero below `0x5000` holds reduced polynomials there. -/
theorem reduced_below {m : Mem} (hm : ∀ a : Addr, a.toNat < 0x5000 → m a = 0) (p : Nat)
    (hp : p + 1024 ≤ 0x5000) : Proof.MlDsa.Reduced m (BitVec.ofNat 64 p) :=
  reduced_of_zero fun k hk => hm _ (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [hp, hk])

end VG.Proof.MlDsa.X86.Arith

end

end

/-! ### `MlDsa.X86.Arith.Table`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86 (32-bit): writing a table of constants

`table t` stores the 256 entries of `t` as words at `[eax]`, through `edx`
(`table_spec`), one entry at a time (`tableN`), so that each step is a short
symbolic execution. The table is read like a polynomial (`coeffAt`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_)
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (q n)
open VG.Proof.MlDsa (coeffAt)
open VG.Proof.MlKem.X86 (wp_cons wp_store)

/-- `s'` is `s` but for the registers `ds`, the flags and memory. -/
structure Regs (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : s'.xmm = s.xmm
  mcdt : s'.mcdt = s.mcdt

/-- Entry `k` of the table. -/
def entry (T : List Nat) (k : Nat) : List Instr :=
  [.mov .edx (.imm (BitVec.ofNat 32 (T.getD k 0))), .store (at_ .eax (4 * k)) .edx]

/-- The first `n` entries. -/
def tableN (T : List Nat) (n : Nat) : List Instr := (List.range n).flatMap (entry T)

theorem table_eq (T : List Nat) : table T = tableN T 256 := rfl

theorem tableN_succ (t : List Nat) (n : Nat) : tableN t (n + 1) = tableN t n ++ entry t n := by
  simp only [tableN, List.range_succ, List.flatMap_append, List.flatMap_singleton]

/-- The first `n` entries of `t` at `p`, from `eax` at `p`: only `edx`, the
flags and the words at `p` change. -/
theorem tableN_spec (t : List Nat) {p : Addr} :
    ∀ (n : Nat) (is : List Instr) (s : State) (P : State → Prop), n ≤ 256 →
      (∀ k < 256, s.ea (at_ .eax (4 * k)) = coeffAddr p k) → (∀ k < 256, InRegions s.wr (coeffAddr p k) 4) →
      (∀ s', Regs [.edx] s s' → Frame [polyRegion p] s.mem s'.mem →
        (∀ k < n, coeffAt s'.mem p k = BitVec.ofNat 32 (t.getD k 0)) → WP isa (.block is) s' P) →
      WP isa (.block (tableN t n ++ is)) s P
  | 0, is, s, P, _, _, _, k => k s ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩ (Frame.refl _ _) (fun _ h => absurd h (by omega_using []))
  | n + 1, is, s, P, hn, hea, hin, k => by
    rw [tableN_succ, List.append_assoc]
    refine tableN_spec t n _ s P (by omega_using [hn]) hea hin fun s₁ o₁ f₁ c₁ => ?_
    have ea₁ : s₁.ea (at_ .eax (4 * n)) = coeffAddr p n := by
      rw [← hea n (by omega_using [hn])]; simp only [State.ea, at_, o₁.gpr .eax (by decide)]
    have hn' : n < Spec.MlDsa.n := by rw [n_eq]; omega_using [hn]
    refine wp_cons (s' := s₁.setReg .edx (BitVec.ofNat 32 (t.getD n 0)))
      (by simp only [reduceExec, readSrc, Option.map_some]) ?_
    have hin' : InRegions (s₁.setReg .edx (BitVec.ofNat 32 (t.getD n 0))).wr
        ((s₁.setReg .edx (BitVec.ofNat 32 (t.getD n 0))).ea (at_ .eax (4 * n))) 4 := by
      simp only [State.ea, at_, State.setReg, show Reg.eax ≠ Reg.edx by decide, ite_false]
      rw [show (s₁.gpr .eax + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁, o₁.wr]
      exact hin n (by omega_using [hn])
    refine wp_store hin' ?_
    refine k _ ⟨fun r hr => ?_, o₁.rd, o₁.wr, o₁.xmm, o₁.mcdt⟩ ?_ ?_
    · simp only [List.mem_singleton] at hr
      show (s₁.setReg .edx _).gpr r = s.gpr r
      simp only [State.setReg, hr, ite_false]
      exact o₁.gpr r (by simp [hr])
    · simp only [State.ea, at_, State.setReg, show Reg.eax ≠ Reg.edx by decide, ite_false]
      rw [show (s₁.gpr .eax + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁]
      exact f₁.writeW (List.mem_singleton_self _) _ (coeff_contains _ hn')
    · intro j hj
      simp only [State.ea, at_, State.setReg, show Reg.eax ≠ Reg.edx by decide, ite_false, ite_true]
      rw [show (s₁.gpr .eax + BitVec.ofNat 32 (4 * n)).setWidth 64 = coeffAddr p n from ea₁,
        coeffAt_writeW _ _ (show j < Spec.MlDsa.n by rw [n_eq]; omega_using [hn, hj]) hn']
      by_cases e : n = j
      · rw [ite_eq_left e, e]
      · rw [ite_eq_right e]; exact c₁ j (by omega_using [hj, e])

theorem table_spec (t : List Nat) {p : Addr} (is : List Instr) (s : State) (P : State → Prop)
    (hea : ∀ k < 256, s.ea (at_ .eax (4 * k)) = coeffAddr p k)
    (hin : ∀ k < 256, InRegions s.wr (coeffAddr p k) 4)
    (k : ∀ s', Regs [.edx] s s' → Frame [polyRegion p] s.mem s'.mem →
      (∀ k < 256, coeffAt s'.mem p k = BitVec.ofNat 32 (t.getD k 0)) → WP isa (.block is) s' P) :
    WP isa (.block (table t ++ is)) s P := by
  rw [table_eq]
  exact tableN_spec t 256 is s P (Nat.le_refl _) hea hin k

theorem getD_map_range {f : Nat → Nat} {n k : Nat} (hk : k < n) : ((List.range n).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]

theorem montZeta_eq {k : Nat} (hk : k < 256) :
    montZetaTable.getD k 0 = (Spec.MlDsa.zetas k).val * 2 ^ 32 % q := by
  rw [← zetaNat_eq, (by decide +kernel :
    montZetaTable = (List.range 256).map fun k => zetaNat k * 2 ^ 32 % 8380417), getD_map_range hk]

theorem montNegZeta_eq {k : Nat} (hk : k < 256) :
    montNegZetaTable.getD k 0 = (-Spec.MlDsa.zetas k).val * 2 ^ 32 % q := by
  rw [← negZetaNat_eq, (by decide +kernel :
    montNegZetaTable = (List.range 256).map fun k => negZetaNat k * 2 ^ 32 % 8380417), getD_map_range hk]

end VG.Proof.MlDsa.X86.Arith

end

end

/-!
# ML-DSA on x86 (32-bit): the entry state of `vg_mldsa_ntt` and `vg_mldsa_inv_ntt`

`Pre s₀` is what the contract of `vg_mldsa_ntt(f, scratch)` and
`vg_mldsa_inv_ntt(f, scratch)` gives of their entry state `s₀` (`Pre.of`),
and `Pub` their public data: the stack pointer and the two pointers. A
table `T` holds the zetas `zv k` in Montgomery form (`TabOK`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Arith

theorem inRd {s : VG.X86.State} {a : Addr} (h : InRegions s.wr a 4) : InRegions (s.rd ++ s.wr) a 4 :=
  let ⟨r, hr, c⟩ := h; ⟨r, List.mem_append_right _ hr, c⟩

end VG.Proof.MlDsa.X86.Arith

namespace VG.Proof.MlDsa.X86.Arith.NttLoop

open VG VG.X86
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86.Arith
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (Reduced inPlaceContract inPlaceSig)
open VG.Proof.MlKem.X86 (E0 retR sub_beq_zero toNat_ofNat32)

section
variable (s₀ : State)
abbrev fP : BitVec 32 := arg s₀ 0
abbrev sP : BitVec 32 := arg s₀ 1
abbrev fA : Addr := (fP s₀).setWidth 64
abbrev sA : Addr := (sP s₀).setWidth 64
abbrev aR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev stkR : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩
end

structure Pre (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 8 ≤ 2 ^ 32
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (fA s₀), polyRegion (sA s₀), aR s₀]
  f_s : (polyRegion (fA s₀)).Disjoint (polyRegion (sA s₀))
  f_a : (polyRegion (fA s₀)).Disjoint (aR s₀)
  s_a : (polyRegion (sA s₀)).Disjoint (aR s₀)
  ret_f : (retR s₀).Disjoint (polyRegion (fA s₀))
  ret_s : (retR s₀).Disjoint (polyRegion (sA s₀))
  ret_a : (retR s₀).Disjoint (aR s₀)
  stk_f : (stkR s₀).Disjoint (polyRegion (fA s₀))
  stk_s : (stkR s₀).Disjoint (polyRegion (sA s₀))
  stk_a : (stkR s₀).Disjoint (aR s₀)
  f_fit : (fP s₀).toNat + 1024 ≤ 2 ^ 32
  s_fit : (sP s₀).toNat + 1024 ≤ 2 ^ 32
  f_red : Reduced s₀.mem (fA s₀)

def Pub (s₀ s₀' : State) : Prop := E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1

theorem Pre.arg_in {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 2) : (aR s₀).Contains (argAddr s₀ i) 4 := by
  have := hp.sp'
  simp only [argAddr, Region.Contains, E0] at this ⊢
  bv_omega

/-- The table `T` holds the zetas `zv k` in Montgomery form. -/
def TabOK (T : List Nat) (zv : Nat → Zq) : Prop := ∀ k < 256, T.getD k 0 = (zv k).val * 2 ^ 32 % q

/-- The pointer compared with the end of `f`. -/
theorem end_cmp (x : BitVec 32) {X : Nat} (hX : X ≤ 1024) :
    (x + BitVec.ofNat 32 X - (x + 1024) == 0) = decide (X = 1024) := by
  rw [sub_beq_zero, BitVec.toNat_add, BitVec.toNat_add, toNat_ofNat32 (by omega_arith),
    show (1024 : BitVec 32).toNat = 1024 from rfl]
  simp only [Nat.reducePow]
  exact decide_eq_decide.mpr (by constructor <;> intro h <;> omega_arith)

theorem Pre.of {s₀ : State} {stk : Nat} {t : Poly → Poly}
    (h : (inPlaceContract X86.abi t stk).pre s₀) (hs : stk = 16) : Pre s₀ := by
  subst hs
  sig_pre [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem arg01_sep {s₀ : State} (hp : Pre s₀) : Mem.Sep (argAddr s₀ 0) 4 (argAddr s₀ 1) 4 := by
  have := hp.sp'
  intro x h₁ h₂
  simp only [argAddr, E0] at this h₁ h₂
  bv_omega

/-- Memory with the arguments `0` and `0x400` at `0x5004`. -/
def satMem : Mem := fun a => if a = 0x5009 then 4 else 0

end VG.Proof.MlDsa.X86.Arith.NttLoop

end
