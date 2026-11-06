module
-- separate module: the P-521 fast window's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521F.Fns
public import VerifiedGarbage.Proof.Weierstrass.X86_64.P521F.Cms
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
public import VerifiedGarbage.Impl.Weierstrass.X86_64.P521Win
public import VerifiedGarbage.Proof.Weierstrass.X86_64.DoubleCms
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-521 on x86-64: the fast steps

Each step of the doubling and of the mixed addition (`stepProg`): a product
by a call (`pmul_ok`), a sum or difference (`sAdd_ok`, `sSub_ok`), or
`C a - D b` (`cmsF_ok`), keeping the registers but `fclob`, the regions and
the memory but its output and the functions' temporary area (`OpKeepF`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.P521F

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.P521F
open VG.Impl.Weierstrass.X86_64.Mont (fnTmp)
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Impl.Weierstrass VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

variable {Z : Nat}

/-- The registers the steps may change. -/
abbrev fclob : List Reg := .rsi :: lclob

/-- What a step writing `[o]` keeps. -/
structure OpKeepF (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ fclob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : ∀ x, (ofs base x < o ∨ o + 72 ≤ ofs base x) → (ofs base x < fnTmp ∨ fnTmp + 72 ≤ ofs base x) →
    s'.mem x = s.mem x

theorem OpKeepF.scr {base : Addr} {o : Nat} {s s' : State} (h : OpKeepF base o s s') (hs : Scr s base Z) :
    Scr s' base Z := ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem se32 {a : Nat} (ha : a < 2 ^ 31) : (BitVec.ofNat 32 a).signExtend 64 = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.signExtend_eq_setWidth_of_msb_false (by rw [BitVec.msb_eq_decide]; simp; omega)]
  simp [BitVec.toNat_setWidth]; omega

theorem sw32 {a : Nat} (ha : a < 2 ^ 32) : (BitVec.ofNat 32 a).setWidth 64 = BitVec.ofNat 64 a := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]; omega

/-- The arguments: `rbx = ws + a`, `rcx = ws + b`, `rsi = o`. -/
theorem args_ok {s : State} {base : Addr} (hs : Scr s base Z) {o a b : Nat} (ho : o < 2 ^ 31) (ha : a < 2 ^ 31)
    (hb : b < 2 ^ 31) :
    WP isa (.block (args o a b)) s fun s' =>
      s'.gpr .rbx = off base a ∧ s'.gpr .rcx = off base b ∧ s'.gpr .rsi = BitVec.ofNat 64 o ∧
      Keeps [.rbx, .rcx, .rsi] s s' := by
  apply WP.of_runBlock
  simp only [args, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, Option.bind_some,
    Option.map_some, State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, reduceCtorEq,
    ite_true, ite_false, RegUpd.gpr_arithFlags, hs.rdi]
  refine ⟨by rw [se32 ha], by rw [se32 hb], sw32 (by omega), fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2]

/-- `FnPost` as what a step keeps, after `args`. -/
theorem fnPost_keep {m : Nat} {weak : Bool} {base : Addr} {o P : Nat} {s s₁ s' : State}
    (k₁ : Keeps [.rbx, .rcx, .rsi] s s₁) (h : FnPost m weak base o P s₁ s') : OpKeepF base o s s' :=
  ⟨fun r hr => by
    have h1 : r ∉ lclob := fun h' => hr (List.mem_cons_of_mem _ h')
    have h2 : r ∉ [Reg.rbx, .rcx, .rsi] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨fun e => h1 (e ▸ by decide), fun e => h1 (e ▸ by decide), fun e => hr (e ▸ by decide)⟩
    rw [h.2.2.1.gpr r h1, k₁.1 r h2],
   by rw [h.2.2.1.rd, k₁.2.2.1], by rw [h.2.2.1.wr, k₁.2.2.2],
   fun x hx ht => by rw [h.2.2.2 x hx (by simp only [fnTmp] at ht ⊢; omega), k₁.2.1]⟩

/-- A product by a call: `[o] = [a] [b] 2⁻⁵⁷⁶ mod p`, below `p` (or `2p` if `weak`). -/
theorem pmul_ok (hZ : 4096 ≤ Z) {s : State} {base : Addr} (hs : Scr s base Z) {weak : Bool} {o a b m : Nat}
    (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (ho : o + 72 ≤ 3520) (ha : a + 72 ≤ 3520) (hb : b + 72 ≤ 3520)
    (hA : wordsVal s.mem base a 9 < m) (hB : wordsVal s.mem base b 9 < m) :
    WP isa (pmul weak o a b).inline s fun s' => OpKeepF base o s s' ∧
      wordsVal s'.mem base o 9 < (if weak then 2 * m else m) ∧
      wordsVal s'.mem base o 9 * (2 ^ 64) ^ 9 % m = wordsVal s.mem base a 9 * wordsVal s.mem base b 9 % m := by
  simp only [pmul, Code.inline]
  refine WP.seq (WP.mono (args_ok hs (o := o) (a := a) (b := b) (by omega) (by omega) (by omega))
    fun s₁ ⟨hbx, hcx, hsi, k₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [← hm₁] at hA hB
  split
  · rename_i hab
    subst hab
    refine WP.mono (sqrFn_ok hZ hs₁ hbx hsi ha ho hm hA) fun s' h => ⟨fnPost_keep k₁ h, ?_, ?_⟩
    · have h1 := h.1
      simp only [Bool.false_eq_true, ite_false] at h1
      split <;> omega
    · rw [h.2.1, hm₁]
  · split
    · refine WP.mono (mulFnW_ok hZ hs₁ hbx hcx hsi ha hb ho hm hA hB) fun s' h =>
        ⟨fnPost_keep k₁ h, ?_, ?_⟩
      · have h1 := h.1; simp only [ite_true] at h1; exact h1
      · rw [h.2.1, hm₁]
    · refine WP.mono (mulFn_ok hZ hs₁ hbx hcx hsi ha hb ho hm hA hB) fun s' h => ⟨fnPost_keep k₁ h, ?_, ?_⟩
      · have h1 := h.1; simp only [Bool.false_eq_true, ite_false] at h1; exact h1
      · rw [h.2.1, hm₁]

/-! ## The invariant, with weak slots -/

theorem opKeepF_wordsVal {base : Addr} {o : Nat} {s s' : State}
    (h : OpKeepF base o s s') : ∀ {k y : Nat}, (y + 8 * k ≤ o ∨ o + 72 ≤ y) →
      (y + 8 * k ≤ fnTmp ∨ fnTmp + 72 ≤ y) → y + 8 * k ≤ 2 ^ 64 →
      wordsVal s'.mem base y k = wordsVal s.mem base y k
  | 0, _, _, _, _ => rfl
  | k + 1, y, ho, ht, hy => by
    simp only [wordsVal]
    have hw : word s'.mem base y = word s.mem base y :=
      Mem.readW_congr fun i hi => h.mem _ (by rw [ofs_off base (by omega_arith)]; omega_arith)
        (by rw [ofs_off base (by omega_arith)]; omega_arith)
    rw [opKeepF_wordsVal h (k := k) (y := y + 8) (by omega_arith) (by omega_arith) (by omega_arith), hw]

/-- `Inv` for the slots `V`, and the slots `W` below `2m`. -/
structure InvW (M : Mod) (base : Addr) (size m : Nat) [NeZero m] (Sl : Nat → Prop) (V W : List Nat)
    (E : Nat → Fin m) (s : State) : Prop where
  inv : Inv M base size m Sl V E s
  sl : ∀ x ∈ W, Sl x
  lt : ∀ x ∈ W, wordsVal s.mem base x M.n < 2 * m
  val : ∀ x ∈ W, toM m (2 ^ (64 * M.n)) (wordsVal s.mem base x M.n) = E x

/-- The slots but `o`'s keep their values through a step writing `o`. -/
theorem keepF_slot {M : Mod} {size : Nat} {Sl : Nat → Prop} (hL : Lay M size Sl) (hn : M.n = 9)
    (ht : M.tmp = fnTmp) {base : Addr} {o : Nat} {s s' : State} (hs : Scr s base size) (hk : OpKeepF base o s s')
    (ho : Sl o) {x : Nat} (hx : Sl x) (hxo : x ≠ o) : wordsVal s'.mem base x M.n = wordsVal s.mem base x M.n := by
  have hn' := hs.nowrap
  have := hL.apart x o hx ho hxo
  have := hL.tmp x hx
  have := hL.le x hx
  rw [hn, ht] at *
  exact opKeepF_wordsVal hk (by omega) (by omega) (by omega)

/-- `ModOkW` through a step writing a slot. -/
theorem keepF_mod {M : Mod} {size m : Nat} {Sl : Nat → Prop} (hL : Lay M size Sl) (hn : M.n = 9)
    (ht : M.tmp = fnTmp) {base : Addr} {o : Nat} {s s' : State} (hs : Scr s base size) (hk : OpKeepF base o s s')
    (ho : Sl o) (hM : ModOkW M size m s.mem base) : ModOkW M size m s'.mem base := by
  have hn' := hs.nowrap
  have hmo := hL.mo o ho
  have h1 := hM.mo
  have h2 := hM.sep
  have hv := hM.val
  refine ⟨hM.n0, hM.mo, hM.tmp, hM.sep, ?_, hM.inv, hM.red⟩
  rw [hn] at hmo h1 h2 hv ⊢
  rw [ht] at h2
  rw [opKeepF_wordsVal hk (by omega) (by omega) (by omega)]
  exact hv

/-- A step writing `o`, below `m`. -/
theorem InvW.update {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hn : M.n = 9) (ht : M.tmp = fnTmp) {V W : List Nat} {E : Nat → Fin m} {s s' : State}
    (hI : InvW M base size m Sl V W E s) {o : Nat} (ho : Sl o) (hk : OpKeepF base o s s')
    (hr : wordsVal s'.mem base o M.n < m) {v : Fin m}
    (hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = v) :
    InvW M base size m Sl (o :: V) (W.filter (· ≠ o)) (Function.update E o v) s' := by
  have hs := hI.inv.scr
  have heq := fun x hx hxo => keepF_slot hL hn ht hs hk ho (x := x) hx hxo
  refine ⟨⟨hk.scr hs, keepF_mod hL hn ht hs hk ho hI.inv.mod, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ho
    · exact hI.inv.sl x hx
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; exact hr
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x (hI.inv.sl x hx') hxo]; exact hI.inv.lt x hx'
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; rw [Function.update_self]; exact hv
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x (hI.inv.sl x hx') hxo, Function.update_of_ne hxo]
      exact hI.inv.val x hx'
  · intro x hx; exact hI.sl x ((List.mem_filter.mp hx).1)
  · intro x hx
    have hxo : x ≠ o := by simpa using (List.mem_filter.mp hx).2
    have hx' := (List.mem_filter.mp hx).1
    rw [heq x (hI.sl x hx') hxo]; exact hI.lt x hx'
  · intro x hx
    have hxo : x ≠ o := by simpa using (List.mem_filter.mp hx).2
    have hx' := (List.mem_filter.mp hx).1
    rw [heq x (hI.sl x hx') hxo, Function.update_of_ne hxo]; exact hI.val x hx'

/-- A step writing `o`, below `2m`. -/
theorem InvW.updateW {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hn : M.n = 9) (ht : M.tmp = fnTmp) {V W : List Nat} {E : Nat → Fin m} {s s' : State}
    (hI : InvW M base size m Sl V W E s) {o : Nat} (ho : Sl o) (hk : OpKeepF base o s s')
    (hr : wordsVal s'.mem base o M.n < 2 * m) {v : Fin m}
    (hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = v) :
    InvW M base size m Sl (V.filter (· ≠ o)) (o :: W) (Function.update E o v) s' := by
  have hs := hI.inv.scr
  have heq := fun x hx hxo => keepF_slot hL hn ht hs hk ho (x := x) hx hxo
  refine ⟨⟨hk.scr hs, keepF_mod hL hn ht hs hk ho hI.inv.mod, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx; exact hI.inv.sl x ((List.mem_filter.mp hx).1)
  · intro x hx
    have hxo : x ≠ o := by simpa using (List.mem_filter.mp hx).2
    have hx' := (List.mem_filter.mp hx).1
    rw [heq x (hI.inv.sl x hx') hxo]; exact hI.inv.lt x hx'
  · intro x hx
    have hxo : x ≠ o := by simpa using (List.mem_filter.mp hx).2
    have hx' := (List.mem_filter.mp hx).1
    rw [heq x (hI.inv.sl x hx') hxo, Function.update_of_ne hxo]; exact hI.inv.val x hx'
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ho
    · exact hI.sl x hx
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; exact hr
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x (hI.sl x hx') hxo]; exact hI.lt x hx'
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; rw [Function.update_self]; exact hv
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x (hI.sl x hx') hxo, Function.update_of_ne hxo]
      exact hI.val x hx'

/-! ## The steps -/

theorem keepF_of {rs : List Reg} {base : Addr} {o : Nat} {s s' : State} (k : KeepRegs rs s s')
    (hrs : ∀ r ∈ rs, r ∈ fclob) (O : Outside base o 72 s.mem s'.mem) : OpKeepF base o s s' :=
  ⟨fun r hr => k.gpr r fun h => hr (hrs r h), k.rd, k.wr, fun x hx _ => O x hx⟩

section
variable {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}

/-- The facts every step needs. -/
structure StepCtx (M : Mod) (size m : Nat) [NeZero m] (Sl : Nat → Prop) : Prop where
  lay : Lay M size Sl
  n9 : M.n = 9
  tmp : M.tmp = fnTmp
  pm : m + 1 = 512 * (2 ^ 64) ^ 8
  unit : UnitMod m (2 ^ (64 * M.n))
  z : 4096 ≤ size

/-- `[o] = [a] [b] R⁻¹` by a call, `o` weak if `w`. -/
theorem mulStep_ok (H : StepCtx M size m Sl) {V W : List Nat} {E : Nat → Fin m} {s : State}
    (hI : InvW M base size m Sl V W E s) {w : Bool} {o a b : Nat} (hS : Sl o)
    (hlo : o + 72 ≤ 3520) (hla : a + 72 ≤ 3520) (hlb : b + 72 ≤ 3520) (ha : a ∈ V) (hb : b ∈ V) :
    WP isa (pmul w o a b).inline s fun s' => OpKeepF base o s s' ∧
      (if w then InvW M base size m Sl (V.filter (· ≠ o)) (o :: W) (Function.update E o (E a * E b)) s'
       else InvW M base size m Sl (o :: V) (W.filter (· ≠ o)) (Function.update E o (E a * E b)) s') := by
  have hA := hI.inv.lt a ha
  have hB := hI.inv.lt b hb
  rw [H.n9] at hA hB
  refine WP.mono (pmul_ok (H.z) hI.inv.scr (weak := w) H.pm hlo hla hlb hA hB) fun s' ⟨hk, hlt, heq⟩ => ⟨hk, ?_⟩
  have h' : wordsVal s'.mem base o 9 * 2 ^ (64 * 9) % m =
      wordsVal s.mem base a 9 * wordsVal s.mem base b 9 % m := by rw [p9]; exact heq
  have hu := H.unit
  rw [H.n9] at hu
  have hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = E a * E b := by
    rw [← hI.inv.val a ha, ← hI.inv.val b hb, H.n9]
    exact toM_mul hu h'
  cases w
  · exact hI.update H.lay H.n9 H.tmp hS hk (by rw [H.n9]; simpa using hlt) hv
  · exact hI.updateW H.lay H.n9 H.tmp hS hk (by rw [H.n9]; simpa using hlt) hv

/-- `[o] = [a] + [b]`. -/
theorem addStep_ok (H : StepCtx M size m Sl) {V W : List Nat} {E : Nat → Fin m} {s : State}
    (hI : InvW M base size m Sl V W E s) {o a b : Nat} (hS : Sl o)
    (hlo : o + 72 ≤ 3520) (hla : a + 72 ≤ 3520) (hlb : b + 72 ≤ 3520) (ha : a ∈ V) (hb : b ∈ V) :
    WP isa (.block (sAdd o a b)) s fun s' => OpKeepF base o s s' ∧
      InvW M base size m Sl (o :: V) (W.filter (· ≠ o)) (Function.update E o (E a + E b)) s' := by
  have hA := hI.inv.lt a ha
  have hB := hI.inv.lt b hb
  rw [H.n9] at hA hB
  refine WP.mono (sAdd_ok H.z hI.inv.scr (o := o) (by omega) (by omega) (by omega) H.pm (by omega))
    fun s' ⟨heq, hk, O⟩ => ?_
  have hk' := keepF_of hk (by decide) O
  refine ⟨hk', hI.update H.lay H.n9 H.tmp hS hk' (by rw [H.n9, heq]; exact Nat.mod_lt _ (by omega)) ?_⟩
  rw [H.n9, heq, toM_add, ← hI.inv.val a ha, ← hI.inv.val b hb, H.n9]

/-- `[o] = [a] - [b]`. -/
theorem subStep_ok (H : StepCtx M size m Sl) {V W : List Nat} {E : Nat → Fin m} {s : State}
    (hI : InvW M base size m Sl V W E s) {o a b : Nat} (hS : Sl o)
    (hlo : o + 72 ≤ 3520) (hla : a + 72 ≤ 3520) (hlb : b + 72 ≤ 3520) (ha : a ∈ V) (hb : b ∈ V) :
    WP isa (.block (sSub o a b)) s fun s' => OpKeepF base o s s' ∧
      InvW M base size m Sl (o :: V) (W.filter (· ≠ o)) (Function.update E o (E a - E b)) s' := by
  have hA := hI.inv.lt a ha
  have hB := hI.inv.lt b hb
  rw [H.n9] at hA hB
  refine WP.mono (sSub_ok H.z hI.inv.scr (o := o) (by omega) (by omega) (by omega) H.pm hA hB)
    fun s' ⟨heq, hk, O⟩ => ?_
  have hk' := keepF_of hk (by decide) O
  refine ⟨hk', hI.update H.lay H.n9 H.tmp hS hk' (by rw [H.n9, heq]; exact Nat.mod_lt _ (by omega)) ?_⟩
  rw [H.n9, heq, show wordsVal s.mem base a 9 + (m - wordsVal s.mem base b 9) =
    wordsVal s.mem base a 9 + m - wordsVal s.mem base b 9 by omega, toM_sub (by omega),
    ← hI.inv.val a ha, ← hI.inv.val b hb, H.n9]

/-- `[o] = C [a] - D [b]`, `[a]` below `2m`. -/
theorem cmsStep_ok (H : StepCtx M size m Sl) {V W : List Nat} {E : Nat → Fin m} {s : State}
    (hI : InvW M base size m Sl V W E s) {o C a D b : Nat} (hS : Sl o)
    (hCD : (C = 4 ∧ D = 1) ∨ (C = 12 ∧ D = 9) ∨ (C = 3 ∧ D = 8))
    (hlo : o + 72 ≤ 3520) (hla : a + 72 ≤ 3520) (hlb : b + 72 ≤ 3520) (ha : a ∈ V ∨ a ∈ W) (hb : b ∈ V) :
    WP isa (.block (cmsF o C a D b)) s fun s' => OpKeepF base o s s' ∧
      InvW M base size m Sl (o :: V) (W.filter (· ≠ o))
        (Function.update E o (smulN C (E a) - smulN D (E b))) s' := by
  have hA : wordsVal s.mem base a M.n < 2 * m := by
    rcases ha with ha | ha
    · have := hI.inv.lt a ha; omega
    · exact hI.lt a ha
  have hva : toM m (2 ^ (64 * M.n)) (wordsVal s.mem base a M.n) = E a := by
    rcases ha with ha | ha
    · exact hI.inv.val a ha
    · exact hI.val a ha
  have hB := hI.inv.lt b hb
  rw [H.n9] at hA hB hva
  refine WP.mono (cmsF_ok H.z hI.inv.scr (o := o) (by omega) (by omega) (by omega) H.pm hCD hA hB)
    fun s' ⟨heq, hk, O⟩ => ?_
  have hk' := keepF_of hk (by decide) O
  refine ⟨hk', hI.update H.lay H.n9 H.tmp hS hk' (by rw [H.n9, heq]; exact Nat.mod_lt _ (by omega)) ?_⟩
  rw [H.n9, heq, toM_cms _ _ _ _ _ (Nat.le_of_lt hB), hva, ← hI.inv.val b hb, H.n9]

end

/-! ## Chaining steps -/

theorem InvW.sub {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {V W V' W' : List Nat}
    {E : Nat → Fin m} {s : State} (h : InvW M base size m Sl V W E s) (hV : ∀ x ∈ V', x ∈ V)
    (hW : ∀ x ∈ W', x ∈ W) : InvW M base size m Sl V' W' E s :=
  ⟨h.inv.sub hV, fun x hx => h.sl x (hW x hx), fun x hx => h.lt x (hW x hx), fun x hx => h.val x (hW x hx)⟩

/-- What steps writing the slots `Ws` keep. -/
structure KeepW (base : Addr) (Ws : List Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ fclob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : ∀ x, (∀ w ∈ Ws, ofs base x < w ∨ w + 72 ≤ ofs base x) →
    (ofs base x < fnTmp ∨ fnTmp + 72 ≤ ofs base x) → s'.mem x = s.mem x

theorem KeepW.refl (base : Addr) (Ws : List Nat) (s : State) : KeepW base Ws s s :=
  ⟨fun _ _ => rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem KeepW.cons {base : Addr} {Ws : List Nat} {o : Nat} {s₁ s₂ s₃ : State} (ho : o ∈ Ws)
    (h₁ : OpKeepF base o s₁ s₂) (h₂ : KeepW base Ws s₂ s₃) : KeepW base Ws s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    fun x hx ht => (h₂.mem x hx ht).trans (h₁.mem x (hx o ho) ht)⟩

/-- A step, then the rest. -/
theorem stepThen {c₁ c₂ : Prog isa} {base : Addr} {Ws : List Nat} {o : Nat} {s : State}
    {P Q : State → Prop} (ho : o ∈ Ws) (h₁ : WP isa c₁ s fun s₁ => OpKeepF base o s s₁ ∧ P s₁)
    (h₂ : ∀ s₁, P s₁ → WP isa c₂ s₁ fun s₂ => KeepW base Ws s₁ s₂ ∧ Q s₂) :
    WP isa (.seq c₁ c₂) s fun s₂ => KeepW base Ws s s₂ ∧ Q s₂ :=
  WP.seq (WP.mono h₁ fun s₁ ⟨k₁, p₁⟩ => WP.mono (h₂ s₁ p₁) fun _ ⟨k₂, q₂⟩ => ⟨KeepW.cons ho k₁ k₂, q₂⟩)

/-- The last step. -/
theorem stepLast' {c : Prog isa} {base : Addr} {Ws : List Nat} {o : Nat} {s : State} {Q : State → Prop}
    (ho : o ∈ Ws) (h : WP isa c s fun s₁ => OpKeepF base o s s₁ ∧ Q s₁) :
    WP isa c s fun s₁ => KeepW base Ws s s₁ ∧ Q s₁ :=
  WP.mono h fun _ ⟨k, q⟩ => ⟨KeepW.cons ho k (KeepW.refl _ _ _), q⟩

section
variable {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}

/-- `mulStep_ok` for a product into a slot below `m`. -/
theorem mulStepS_ok (H : StepCtx M size m Sl) {V W : List Nat} {E : Nat → Fin m} {s : State}
    (hI : InvW M base size m Sl V W E s) {w : Bool} (hw : w = false) {o a b : Nat} (hS : Sl o)
    (hlo : o + 72 ≤ 3520) (hla : a + 72 ≤ 3520) (hlb : b + 72 ≤ 3520) (ha : a ∈ V) (hb : b ∈ V) :
    WP isa (pmul w o a b).inline s fun s' => OpKeepF base o s s' ∧
      InvW M base size m Sl (o :: V) (W.filter (· ≠ o)) (Function.update E o (E a * E b)) s' := by
  subst hw; exact mulStep_ok H hI hS hlo hla hlb ha hb

/-- `mulStep_ok` for a product into a weak slot. -/
theorem mulStepW_ok (H : StepCtx M size m Sl) {V W : List Nat} {E : Nat → Fin m} {s : State}
    (hI : InvW M base size m Sl V W E s) {w : Bool} (hw : w = true) {o a b : Nat} (hS : Sl o)
    (hlo : o + 72 ≤ 3520) (hla : a + 72 ≤ 3520) (hlb : b + 72 ≤ 3520) (ha : a ∈ V) (hb : b ∈ V) :
    WP isa (pmul w o a b).inline s fun s' => OpKeepF base o s s' ∧
      InvW M base size m Sl (V.filter (· ≠ o)) (o :: W) (Function.update E o (E a * E b)) s' := by
  subst hw; exact mulStep_ok H hI hS hlo hla hlb ha hb

end

theorem weakOp_false {S : RcbSlots} {o a : Nat} (h1 : o ≠ S.t5) (h2 : o ≠ S.t4) : weakOp S o a = false := by
  simp only [weakOp, Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff]
  exact ⟨h1, Or.inl h2⟩

theorem weakOp_false' {S : RcbSlots} {o a : Nat} (h1 : o ≠ S.t5) (h2 : a ≠ S.t3) : weakOp S o a = false := by
  simp only [weakOp, Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff]
  exact ⟨h1, Or.inr h2⟩

theorem mem_filter_ne {q o : Nat} {W : List Nat} (h : q ∈ W) (hne : q ≠ o) : q ∈ W.filter (· ≠ o) :=
  List.mem_filter.mpr ⟨h, by simpa using hne⟩

/-- Membership in a literal list (or one appended to others). -/
macro "mem_tac" : tactic => `(tactic| simp only [List.mem_cons, List.mem_append, true_or, or_true])

theorem KeepW.trans {base : Addr} {Ws : List Nat} {s₁ s₂ s₃ : State} (h₁ : KeepW base Ws s₁ s₂)
    (h₂ : KeepW base Ws s₂ s₃) : KeepW base Ws s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    fun x hx ht => (h₂.mem x hx ht).trans (h₁.mem x hx ht)⟩

/-- `progs` of `a ++ b`, both nonempty: `a`, then `b`. -/
theorem progs_append_inline : ∀ (a b : List (Prog isa)), a ≠ [] → b ≠ [] → ∀ {s : State} {Q : State → Prop},
    WP isa (VG.Impl.Weierstrass.X86_64.progs a).inline s (fun t => WP isa (VG.Impl.Weierstrass.X86_64.progs b).inline t Q) →
      WP isa (VG.Impl.Weierstrass.X86_64.progs (a ++ b)).inline s Q
  | [], _, ha, _, _, _, _ => absurd rfl ha
  | [x], b :: bs, _, _, _, _, h => WP.seq h
  | x :: y :: a, b, _, hb, _, _, h => by
    show WP isa (.seq x.inline (VG.Impl.Weierstrass.X86_64.progs (y :: a ++ b)).inline) _ _
    exact WP.seq (WP.mono (WP.seq_iff.mp h) fun _ h' => progs_append_inline (y :: a) b (by simp) hb h')
  | [_], [], _, hb, _, _, _ => absurd rfl hb

end VG.Proof.Weierstrass.X86_64.P521F
