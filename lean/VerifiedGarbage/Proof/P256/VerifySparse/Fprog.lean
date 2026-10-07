import VerifiedGarbage.Proof.P256.VerifySparse.Code
import VerifiedGarbage.Proof.P256.VerifySparse.Sub
import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog

namespace VG.Proof.P256.VerifySparse
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Weierstrass VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

/-- The sparse compiler retains the canonical Montgomery multiplication contract. -/
theorem mulOp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} (hME : M=Impl.P256.VerifySparse.M) {m : Nat} (hp : m=p)
    (hM : ModOkA M size m s.mem base) (hA : ModA M) {o a b : Nat} (ho : o+8*M.n≤size)
    (ha : a+8*M.n≤size) (hb : b+8*M.n≤size) (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (hB : wordsVal s.mem base b M.n<m) :
    WP isa (.block (Impl.P256.VerifySparse.op (.mul o a b))) s fun t =>
      OpKeep M base o s t ∧ wordsVal t.mem base o M.n<m ∧
      wordsVal t.mem base o M.n*2^(64*M.n)%m =
        wordsVal s.mem base a M.n*wordsVal s.mem base b M.n%m := by
  subst m
  have hn : M.n=4 := hME ▸ rfl
  by_cases hab : a=b
  · subst b
    rw [op_square]
    refine WP.mono (square_ok hs hME hn hM hA (by simpa only [hn] using ho)
      (by simpa only [hn] using ha) ho8 ha8 (by simpa only [hn] using hB))
      fun t ⟨hk,hlt,he⟩ => ?_
    exact ⟨hk.toOpKeep hn,by simpa only [hn] using hlt,by simpa only [hn] using he⟩
  · rw [op_mul o a b hab]
    rw [←hME]
    exact mul_ok hs hME hM.toW hM.n10 hA ho ha hb ho8 ha8 hb8 hB

/-- The sparse compiler retains canonical addition and the ordinary memory frame. -/
theorem addOp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} (hME : M=Impl.P256.VerifySparse.M) {m : Nat} (hp : m=p)
    (hM : ModOkA M size m s.mem base) (hA : ModA M) {o a b : Nat} (ho : o+8*M.n≤size)
    (ha : a+8*M.n≤size) (hb : b+8*M.n≤size) (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (hAB : wordsVal s.mem base a M.n+wordsVal s.mem base b M.n<2*m) :
    WP isa (.block (Impl.P256.VerifySparse.op (.add o a b))) s fun t =>
      OpKeep M base o s t ∧ wordsVal t.mem base o M.n=
        (wordsVal s.mem base a M.n+wordsVal s.mem base b M.n)%m := by
  subst m
  rw [op_add,←hME]
  exact add_ok hs hME hM.toW hM.n10 hA ho ha hb ho8 ha8 hb8 hAB

/-- The sparse compiler retains canonical subtraction and the ordinary memory frame. -/
theorem subOp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : Mod} (hME : M=Impl.P256.VerifySparse.M) {m : Nat} (hp : m=p)
    {o a b : Nat} (ho : o+8*M.n≤size) (ha : a+8*M.n≤size) (hb : b+8*M.n≤size)
    (ho8 : o%8=0) (ha8 : a%8=0) (hb8 : b%8=0)
    (hA : wordsVal s.mem base a M.n<m) (hB : wordsVal s.mem base b M.n<m) :
    WP isa (.block (Impl.P256.VerifySparse.op (.sub o a b))) s fun t =>
      OpKeep M base o s t ∧ wordsVal t.mem base o M.n=
        (wordsVal s.mem base a M.n+m-wordsVal s.mem base b M.n)%m := by
  subst M m
  exact sub_ok hs ho ha hb ho8 ha8 hb8 hA hB

theorem fop_ok {M : Mod} (hME : M=Impl.P256.VerifySparse.M) {base : Addr} {size m : Nat} [NeZero m] (hp : m=p) {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (.block (Impl.P256.VerifySparse.op op)) s fun s' =>
      OpKeep M base op.out s s' ∧ Inv M base size m Sl (op.out :: V) (op.run E) s' := by
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (mulOp_ok hI.scr hME hp hI.mod hAl.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) (hI.lt b hR.2)) fun s' ⟨hk, hlt, heq⟩ => ⟨hk, hI.update hL hS.1 hk hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (addOp_ok hI.scr hME hp hI.mod hAl.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) (by omega)) fun s' ⟨hk, heq⟩ => ⟨hk, hI.update hL hS.1 hk ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega)
    · rw [heq, toM_add, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (subOp_ok hI.scr hME hp (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hAl.sl o hS.1) (hAl.sl a hS.2.1) (hAl.sl b hS.2.2) hA hB)
      fun s' ⟨hk, heq⟩ => ⟨hk, hI.update hL hS.1 hk ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega)
    · rw [heq, toM_sub (by omega), hI.val a hR.1, hI.val b hR.2]

/-- A field program. -/
theorem fprog_ok {M : Mod} (hME : M=Impl.P256.VerifySparse.M) {base : Addr} {size m : Nat} [NeZero m] (hp : m=p) {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hAl : Aligned M Sl) (hm : UnitMod m (2 ^ (64 * M.n))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (.block (ops.flatMap Impl.P256.VerifySparse.op)) s fun s' => ProgKeep M base (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (fop_ok hME hp hL hAl hm hI (hS op (List.mem_cons_self ..)) hR.1) fun s₁ ⟨k₁, I₁⟩ => ?_
    refine WP.mono (fprog_ok hME hp hL hAl hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨⟨fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.rd.trans k₁.rd,
        k₂.wr.trans k₁.wr, k₂.sp.trans k₁.sp, fun x hx ht => ?_⟩, I₂⟩
    rw [List.map_cons] at hx
    rw [k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht,
      k₁.mem x (hx _ (List.mem_cons_self ..)) ht]


end VG.Proof.P256.VerifySparse
