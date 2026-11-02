module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.JacMadd
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Impl.X86_64Scal
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Field programs with code between their operations, on x86-64

`fprogBI M ops side i` runs the block `side (i + k)` after operation `k` of
`ops`. The operations, of scalar code (`scalCode`), leave the vector
registers alone, and keep nothing in registers from one to the next; code
`side` that keeps the memory, the regions and the registers but `clob`
(`SideKeep`), and so the operations' invariant (`Inv.of_side`), may run
between them, the field program computing what `fprogB` does
(`fprogBI_ok`), and the mixed Jacobian addition what `maddJ_ok` says
(`maddJI_ok`), while what the side code computes (`SI`), which the
operations leave as it is (`hstab`), follows it.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass

/-- Scalar code is scalar inlined. -/
theorem scalCode_inline : ∀ {c : Prog isa}, scalCode c = true → scalCode c.inline = true
  | .block _, h => h
  | .seq a b, h => by
    simp only [scalCode, Bool.and_eq_true] at h
    simp only [Code.inline, scalCode, scalCode_inline h.1, scalCode_inline h.2, Bool.and_self]
  | .ite _ a b, h => by
    simp only [scalCode, Bool.and_eq_true] at h
    simp only [Code.inline, scalCode, scalCode_inline h.1, scalCode_inline h.2, Bool.and_self]
  | .loop b _, h => by
    simp only [scalCode] at h
    simp only [Code.inline, scalCode, scalCode_inline h]
  | .call _ b, h => by
    simp only [scalCode] at h
    exact h
  | .frame .., h => by simp only [scalCode, Bool.false_eq_true] at h
  | .icall .., h => by simp only [scalCode, Bool.false_eq_true] at h

/-- What code run between the operations keeps: the registers but `clob`, the
memory and the regions. -/
structure SideKeep (M : Mod) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob M.n → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Inv.of_side {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {V : List Nat}
    {E : Nat → Fin m} {s s' : State} (hI : Inv M base size m Sl V E s) (h : SideKeep M s s') :
    Inv M base size m Sl V E s' :=
  ⟨⟨by rw [h.gpr _ (rdi_not_clob _)]; exact hI.scr.rdi, by rw [h.wr]; exact hI.scr.wr, hI.scr.nowrap⟩,
    by rw [h.mem]; exact hI.mod, hI.sl, fun x hx => by rw [h.mem]; exact hI.lt x hx,
    fun x hx => by rw [h.mem]; exact hI.val x hx⟩

theorem ProgKeep.of_side {M : Mod} {base : Addr} (W : List Nat) {s s' : State} (h : SideKeep M s s') :
    ProgKeep M base W s s' :=
  ⟨h.gpr, h.rd, h.wr, fun x _ _ => by rw [h.mem]⟩

theorem ProgKeep.append {M : Mod} {base : Addr} {W W' : List Nat} {s₁ s₂ s₃ : State}
    (h₁ : ProgKeep M base W s₁ s₂) (h₂ : ProgKeep M base W' s₂ s₃) : ProgKeep M base (W ++ W') s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    fun x hx ht => by
      rw [h₂.mem x (fun w hw => hx w (List.mem_append_right _ hw)) ht,
        h₁.mem x (fun w hw => hx w (List.mem_append_left _ hw)) ht]⟩

/-- `fprogB_ok` with the block `side (i + k)` after operation `k`: the field
program computes what it does, and the side code `SI` from `SI i` to
`SI (i + ops.length)`. -/
theorem fprogBI_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {side : Nat → List Instr} {SI : Nat → State → Prop} {N : Nat}
    (hside : ∀ i t, i < N → SI i t → WP isa (.block (side i)) t fun t' => SI (i + 1) t' ∧ SideKeep M t t')
    (hstab : ∀ i o t t', Sl o → SI i t → OpKeep M base o t t' → t'.xmm = t.xmm → t'.ymmHi = t.ymmHi →
      t'.syms = t.syms → SI i t') :
    ∀ (ops : List FOp) (i : Nat) {V : List Nat} {E : Nat → Fin m} {s : State},
      i + ops.length ≤ N → (∀ op ∈ ops, scalCode (opProg M op) = true) →
      Inv M base size m Sl V E s → SI i s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (fprogBI M ops side i).inline s fun s' => ProgKeep M base (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s' ∧ SI (i + ops.length) s'
  | [], i, _, _, s, _, _, hI, hS, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI, hS⟩
  | op :: ops, i, V, E, s, hN, hsc, hI, hS, hSl, hR => by
    rw [readsOk, Bool.and_eq_true, List.all_eq_true] at hR
    simp only [decide_eq_true_eq] at hR
    show WP isa (Code.seq (opProg M op).inline (Code.seq (.block (side i)) (fprogBI M ops side (i + 1)).inline)) s _
    refine WP.seq (WP.mono_syms (WP.vecKeep (scalCode_inline (hsc op (List.mem_cons_self ..)))
      (opProg_ok hL hm hI (hSl op (List.mem_cons_self ..)) hR.1)) fun s₁ ⟨⟨k₁, I₁⟩, x₁, y₁⟩ sy₁ => ?_)
    have hS₁ := hstab i op.out s s₁ (hSl op (List.mem_cons_self ..) op.out (List.mem_cons_self ..)) hS k₁ x₁ y₁
      sy₁
    refine WP.seq (WP.mono (hside i s₁ (by rw [List.length_cons] at hN; omega) hS₁) fun s₂ ⟨hS₂, k₂⟩ => ?_)
    refine WP.mono (fprogBI_ok hL hm hside hstab ops (i + 1) (by rw [List.length_cons] at hN; omega)
      (fun op' h => hsc op' (List.mem_cons_of_mem _ h))
      (I₁.of_side k₂) hS₂ (fun op' h => hSl op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₃ ⟨k₃, I₃, hS₃⟩ => ⟨?_, I₃, by rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]; exact hS₃⟩
    have k₁' : ProgKeep M base [op.out] s s₁ :=
      ⟨k₁.gpr, k₁.rd, k₁.wr, fun x hx ht => k₁.mem x (hx _ (List.mem_cons_self ..)) ht⟩
    have h := (k₁'.append (ProgKeep.of_side [] k₂)).append k₃
    exact ⟨h.gpr, h.rd, h.wr, fun x hx ht => h.mem x (fun w hw => hx w (by
      simp only [List.map_cons, List.mem_cons, List.append_nil, List.cons_append, List.nil_append] at hw ⊢
      exact hw)) ht⟩

/-- `maddJ_ok`, with the block `side (i + k)` after operation `k`. -/
theorem maddJI_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {side : Nat → List Instr}
    {SI : Nat → State → Prop} {N : Nat}
    (hside : ∀ i t, i < N → SI i t → WP isa (.block (side i)) t fun t' => SI (i + 1) t' ∧ SideKeep M t t')
    (hstab : ∀ i o t t', Sl o → SI i t → OpKeep M base o t t' → t'.xmm = t.xmm → t'.ymmHi = t.ymmHi →
      t'.syms = t.syms → SI i t')
    (hsc : ∀ op ∈ maddJ S p q o, scalCode (opProg M op) = true) {i : Nat} (hiN : i + (maddJ S p q o).length ≤ N)
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V)
    (hS : SI i s) :
    WP isa (fprogBI M (maddJ S p q o) side i).inline s fun s' => ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (maddJ S p q o) E) s' ∧
      (runOps (maddJ S p q o) E o.x, runOps (maddJ S p q o) E o.y, runOps (maddJ S p q o) E o.z) =
        maddJF (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) ∧
      SI (i + (maddJ S p q o).length) s' := by
  rw [maddJ_eq] at hsc hiN ⊢
  have hN := maddJN_ok
  have hR : readsOk (ofN maddJN S p q o) V = true := readsOk_mono (ofN_readsOk hN S p q o) hV
  refine WP.mono (fprogBI_ok hL hm hside hstab _ i hiN hsc hI hS (fun op hop x hx => hSl x (ofN_slots op hop x hx)) hR)
    fun s' ⟨hk, hI', hS'⟩ => ⟨hk.mono fun w hw => ?_, hI'.sub fun x hx => ?_, ?_, hS'⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out hN op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem hN hx)
    · exact Or.inl hx
  · exact (congrArg₂ Prod.mk (ofN_run hN hA E 6) (congrArg₂ Prod.mk (ofN_run hN hA E 7) (ofN_run hN hA E 8))).trans
      (maddJN_run _)

end VG.Proof.Weierstrass.X86_64
