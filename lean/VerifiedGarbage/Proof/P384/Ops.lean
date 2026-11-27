module

public import VerifiedGarbage.Impl.P384.Ops
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
import VerifiedGarbage.Proof.Mont.AArch64.P384Field.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Field.Reduce
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks

/-!
# P-384's field operations inline on AArch64

`mul_ok` and `sqr_ok`: `Ops.mul` and `Ops.sqr` (`Impl/P384/Ops.lean`) compute
Montgomery's product and square modulo `p`. `fop_ok`: an operation writes its
slot and keeps the others; `fprog_ok`: so does a straight line of them. They
change five callee-saved registers besides those of the other moduli's
operations (`clobX`).
-/

@[expose] public section

-- Powers of two up to `2^768` are evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.P384.Ops

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.Mont.AArch64
open VG.Impl.P384.Ops (M)
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

theorem M_n : M.n = 6 := rfl

/-- The registers the operations change. -/
def clobX : List Reg := clob 6 ++ [.x21, .x22, .x23, .x24, .x25]

theorem clob_clobX : ∀ r ∈ clob 6, r ∈ clobX := fun _ h => List.mem_append_left _ h

theorem x0_not_clobX : Reg.x0 ∉ clobX := by decide

/-- What an operation writing `o` keeps. -/
structure OpKeepX (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clobX → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : ∀ x, (ofs base x < o ∨ o + 8 * M.n ≤ ofs base x) →
    (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s'.mem x = s.mem x

theorem OpKeep.toX {base : Addr} {o : Nat} {s s' : State} (h : OpKeep M base o s s') : OpKeepX base o s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (clob_clobX r h'), h.rd, h.wr, h.sp, h.mem⟩

theorem opKeepX_wordsVal {base : Addr} {o : Nat} {s s' : State} (h : OpKeepX base o s s') :
    ∀ {k y : Nat}, (y + 8 * k ≤ o ∨ o + 8 * M.n ≤ y) → (y + 8 * k ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ y) →
      y + 8 * k ≤ 2 ^ 64 → wordsVal s'.mem base y k = wordsVal s.mem base y k
  | 0, _, _, _, _ => rfl
  | k + 1, y, ho, ht, hy => by
    have hw : word s'.mem base y = word s.mem base y :=
      Mem.readW_congr fun i hi => h.mem _ (by rw [ofs_off base (by omega_arith)]; omega_arith)
        (by rw [ofs_off base (by omega_arith)]; omega_arith)
    simp only [wordsVal]
    rw [opKeepX_wordsVal h (k := k) (y := y + 8) (by omega_arith) (by omega_arith) (by omega_arith), hw]

/-- An operation writing `o`, which then holds `v`, keeps the invariant. -/
theorem Inv.updateX {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    {V : List Nat} {E : Nat → Fin m} {s s' : State} (hI : Inv M base size m Sl V E s) {o : Nat}
    (ho : Sl o) (hk : OpKeepX base o s s') (hr : wordsVal s'.mem base o M.n < m) {v : Fin m}
    (hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = v) :
    Inv M base size m Sl (o :: V) (Fun.update E o v) s' := by
  have hn := hI.scr.nowrap
  have hmo := hL.mo o ho
  have hM := hI.mod
  have hmo' := hM.mo
  have hsep := hM.sep
  have heq : ∀ x ∈ V, x ≠ o → wordsVal s'.mem base x M.n = wordsVal s.mem base x M.n := fun x hx hxo => by
    have h1 := hL.apart x o (hI.sl x hx) ho hxo
    have h2 := hL.tmp x (hI.sl x hx)
    have h3 := hL.le x (hI.sl x hx)
    exact opKeepX_wordsVal hk h1 h2 (by omega_using [h3, hn])
  refine ⟨⟨(hk.gpr _ x0_not_clobX).trans hI.scr.x0, hk.wr ▸ hI.scr.wr, hn, hI.scr.enc⟩,
    ⟨hM.n0, hM.n10, hM.mo, hM.tmp, hM.sep, ?_, hM.inv, hM.red, hM.call⟩, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · rw [opKeepX_wordsVal hk hmo.symm hsep (by omega_using [hmo', hn])]
    exact hM.val
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact ho
    · exact hI.sl x hx
  · by_cases hxo : x = o
    · exact hxo ▸ hr
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x hx' hxo]; exact hI.lt x hx'
  · by_cases hxo : x = o
    · rw [hxo, Fun.update_self]; exact hv
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x hx' hxo, Fun.update_of_ne hxo]; exact hI.val x hx'

/-- What a program writing the slots `W` keeps. -/
structure ProgKeepX (base : Addr) (W : List Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clobX → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : ∀ x, (∀ w ∈ W, ofs base x < w ∨ w + 8 * M.n ≤ ofs base x) →
    (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s'.mem x = s.mem x

theorem ProgKeepX.refl (base : Addr) (W : List Nat) (s : State) : ProgKeepX base W s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem ProgKeepX.mono {base : Addr} {W W' : List Nat} {s s' : State} (h : ProgKeepX base W s s')
    (hW : ∀ w ∈ W, w ∈ W') : ProgKeepX base W' s s' :=
  ⟨h.gpr, h.rd, h.wr, h.sp, fun x hx ht => h.mem x (fun w hw => hx w (hW w hw)) ht⟩

theorem ProgKeepX.unch {base : Addr} {W : List Nat} {s s' : State} (h : ProgKeepX base W s s') :
    Unch base (W.map (·, 8 * M.n) ++ [(M.tmp, 8 * M.n)]) s.mem s'.mem :=
  fun x hx => h.mem x (fun _ hw => hx _ (List.mem_append_left _ (List.mem_map_of_mem hw)))
    (hx _ (List.mem_append_right _ (List.mem_singleton_self _)))

theorem OpKeepX.prog {base : Addr} {o : Nat} {s s' : State} (h : OpKeepX base o s s') :
    ProgKeepX base [o] s s' :=
  ⟨h.gpr, h.rd, h.wr, h.sp, fun x hx ht => h.mem x (hx o (List.mem_singleton_self _)) ht⟩

theorem ProgKeepX.trans {base : Addr} {W W' : List Nat} {s t u : State} (h : ProgKeepX base W s t)
    (h' : ProgKeepX base W' t u) : ProgKeepX base (W ++ W') s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp,
    fun x hx ht => (h'.mem x (fun w hw => hx w (List.mem_append_right _ hw)) ht).trans
      (h.mem x (fun w hw => hx w (List.mem_append_left _ hw)) ht)⟩

/-- The end of a product or a square: the reduction of `T`, and the store. -/
theorem finish_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hM : ModOkA M size p384 s.mem base) (hA : ModA M) {o : Nat} (ho : o + 48 ≤ size) (ho8 : o % 8 = 0)
    (hz : s.gpr .x7 = 0) (hT : regsVal s (P384Field.tl ++ P384Field.th) < 2 ^ 384 * p384) :
    WP isa (.block (Impl.P384.Ops.finish o)) s fun t => OpKeepX base o s t ∧
      wordsVal t.mem base o 6 < p384 ∧
      wordsVal t.mem base o 6 * 2 ^ (64 * 6) % p384 = regsVal s (P384Field.tl ++ P384Field.th) % p384 := by
  have hp : P384Field.p = p384 := by decide
  simp only [Impl.P384.Ops.finish, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (P384Field.reduce_ok hz (hp ▸ hT)) fun s₁ ⟨⟨V, hV, hlt, hmod⟩, k₁⟩ => ?_
  rw [hp] at hlt hmod
  have z₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (by decide), hz]
  rw [WP.block_append_iff]
  refine WP.mono (csubR_ok (hs.of_keeps k₁ (by decide)) (M := M) (m := p384) (ts := P384Field.rs) (top := .x13) rfl (by decide)
    (by decide) (by unfold Fresh; decide) hM.mo hA.mo z₁ (by rw [k₁.mem]; exact hM.val)
    (Nat.lt_of_le_of_lt (Nat.le_of_eq hV) hlt)) fun s₂ ⟨e₂, k₂⟩ => ?_
  have e₂' : regsVal s₂ P384Field.rs = V % p384 := e₂.trans (congrArg (· % p384) hV)
  refine WP.mono (stores_ok P384Field.rs ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)) (by simpa using ho) ho8
    (by decide)) fun t ⟨e₃, k₃, O₃⟩ => ?_
  have e₃' : wordsVal t.mem base o 6 = V % p384 := e₃.trans e₂'
  refine ⟨⟨fun r hr => ?_, by rw [k₃.rd, k₂.rd, k₁.rd], by rw [k₃.wr, k₂.wr, k₁.wr], by rw [k₃.sp, k₂.sp, k₁.sp],
    fun x hx _ => ?_⟩, ?_, ?_⟩
  · have sub₁ : ∀ q ∈ P384Field.redW, q ∈ clobX := by decide
    have sub₂ : ∀ q ∈ Reg.x2 :: .x17 :: P384Field.rs ++ dRegs M.n, q ∈ clobX := by decide
    rw [k₃.gpr r (by simp), k₂.gpr r fun h => hr (sub₂ r h), k₁.gpr r fun h => hr (sub₁ r h)]
  · rw [O₃ x hx, k₂.mem, k₁.mem]
  · rw [e₃']; exact Nat.mod_lt _ (by decide)
  · rw [e₃', Nat.mod_mul_mod, hmod]

theorem zero7_ok (s : State) : WP isa (.block [zero7]) s fun t => t.gpr .x7 = 0 ∧ Keeps [.x7] s t :=
  WP.mono (movz0_ok s .x7) fun _ ⟨e, k⟩ => ⟨e, k⟩

/-- What a product or a square keeps, from what its end does. -/
theorem OpKeepX.of_keeps {base : Addr} {o : Nat} {W : List Reg} {s t u : State} (k : Keeps W s t)
    (hW : ∀ r ∈ W, r ∈ clobX) (h : OpKeepX base o t u) : OpKeepX base o s u :=
  ⟨fun r hr => (h.gpr r hr).trans (k.gpr r fun h' => hr (hW r h')), h.rd.trans k.rd, h.wr.trans k.wr,
    h.sp.trans k.sp, fun x hx ht => by rw [h.mem x hx ht, k.mem]⟩

/-- `[o] = [a] [b] R⁻¹ mod p`. -/
theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hM : ModOkA M size p384 s.mem base) (hA : ModA M) {o a b : Nat} (ho : o + 48 ≤ size) (ha : a + 48 ≤ size)
    (hb : b + 48 ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (hB : wordsVal s.mem base b 6 < p384) :
    WP isa (.block (Impl.P384.Ops.mul o a b)) s fun t => OpKeepX base o s t ∧
      wordsVal t.mem base o 6 < p384 ∧
      wordsVal t.mem base o 6 * 2 ^ (64 * 6) % p384 = wordsVal s.mem base a 6 * wordsVal s.mem base b 6 % p384 := by
  rw [Impl.P384.Ops.mul, List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (P384Field.prod_ok hs₁.ptr hs₁.ptr ha hb ha8 hb8 (by decide) (by decide) z₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [k₁.mem] at e₂
  have k : Keeps (.x7 :: P384Field.prodW) s s₂ := (k₁.mono (by simp)).trans (k₂.mono (by simp +contextual))
  refine WP.mono (finish_ok (hs.of_keeps k (by decide)) (by rw [k.mem]; exact hM) hA ho ho8
    (by rw [k₂.gpr _ (by decide), z₁]) (by rw [e₂]; exact Nat.mul_lt_mul'' (wordsVal_lt ..) hB))
    fun t ⟨h, lt, md⟩ => ⟨OpKeepX.of_keeps k (by decide) h, lt, by rw [md, e₂]⟩

/-- `[o] = [a]² R⁻¹ mod p`. -/
theorem sqr_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hM : ModOkA M size p384 s.mem base) (hMA : ModA M) {o a : Nat} (ho : o + 48 ≤ size) (ha : a + 48 ≤ size)
    (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hA : wordsVal s.mem base a 6 < p384) :
    WP isa (.block (Impl.P384.Ops.sqr o a)) s fun t => OpKeepX base o s t ∧
      wordsVal t.mem base o 6 < p384 ∧
      wordsVal t.mem base o 6 * 2 ^ (64 * 6) % p384 = wordsVal s.mem base a 6 * wordsVal s.mem base a 6 % p384 := by
  rw [Impl.P384.Ops.sqr, List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (P384Field.sqr_ok hs₁.ptr ha ha8 (by decide) z₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [k₁.mem] at e₂
  have k : Keeps (.x7 :: P384Field.prodW) s s₂ := (k₁.mono (by simp)).trans (k₂.mono (by simp +contextual))
  refine WP.mono (finish_ok (hs.of_keeps k (by decide)) (by rw [k.mem]; exact hM) hMA ho ho8
    (by rw [k₂.gpr _ (by decide), z₁]) (by rw [e₂]; exact Nat.mul_lt_mul'' (wordsVal_lt ..) hA))
    fun t ⟨h, lt, md⟩ => ⟨OpKeepX.of_keeps k (by decide) h, lt, by rw [md, e₂]⟩

/-- A field operation keeps the invariant, its slot holding its result. -/
theorem fop_ok {size m : Nat} [NeZero m] (hmp : m = p384) {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {base : Addr} {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (.block (Impl.P384.Ops.op op)) s fun s' =>
      OpKeepX base op.out s s' ∧ Inv M base size m Sl (op.out :: V) (op.run E) s' := by
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hS hR
    have h : WP isa (.block (Impl.P384.Ops.op (.mul o a b))) s fun t => OpKeepX base o s t ∧
        wordsVal t.mem base o 6 < p384 ∧
        wordsVal t.mem base o 6 * 2 ^ (64 * 6) % p384 = wordsVal s.mem base a 6 * wordsVal s.mem base b 6 % p384 := by
      have hlt : wordsVal s.mem base b 6 < p384 := hmp ▸ hI.lt b hR.2
      simp only [Impl.P384.Ops.op]
      split
      · rename_i e
        obtain rfl : a = b := by simpa using e
        exact sqr_ok hI.scr (hmp ▸ hI.mod) hAl.mod (hL.le o hS.1) (hL.le a hS.2.1) (hAl.sl o hS.1) (hAl.sl a hS.2.1) hlt
      · exact mul_ok hI.scr (hmp ▸ hI.mod) hAl.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2) (hAl.sl o hS.1)
          (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) hlt
    refine WP.mono h fun t ⟨k, lt, e⟩ => ⟨k, Inv.updateX hL hI hS.1 k (hmp ▸ lt) ?_⟩
    exact (toM_mul hm (hmp ▸ e)).trans (congr (congrArg HMul.hMul (hI.val a hR.1)) (hI.val b hR.2))
  | add o a b =>
    exact WP.mono (VG.Proof.Weierstrass.AArch64.fop_ok hL hAl hm hI hS hR) fun t ⟨k, I⟩ => ⟨OpKeep.toX k, I⟩
  | sub o a b =>
    exact WP.mono (VG.Proof.Weierstrass.AArch64.fop_ok hL hAl hm hI hS hR) fun t ⟨k, I⟩ => ⟨OpKeep.toX k, I⟩

/-- A straight line of field operations. -/
theorem fprog_ok {size m : Nat} [NeZero m] (hmp : m = p384) {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {base : Addr} :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) → readsOk ops V = true →
      WP isa (.block (ops.flatMap Impl.P384.Ops.op)) s fun s' => ProgKeepX base (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨ProgKeepX.refl _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fop_ok hmp hL hAl hm hI (hS op (List.mem_cons_self ..)) hR.1) fun s₁ ⟨k₁, I₁⟩ => ?_
    exact WP.mono (fprog_ok hmp hL hAl hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨(OpKeepX.prog k₁).trans k₂, I₂⟩

end VG.Proof.P384.Ops
