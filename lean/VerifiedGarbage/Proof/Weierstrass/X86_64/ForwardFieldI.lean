module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardFieldI
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogI
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Forward
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardStores
import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# Field programs with code between their operations, forwarded on x86-64

`ForwardField.programBI M ops side` computes what `programB` does
(`programBI_ok`), with code `side` between its operations that keeps every
register but `rdx`, the memory and the regions (`SideKeepF`): the cache of
the registers an operation stored passes over it, as none of them is `rdx`
(`outputRegs_ne_rdx`). As for `fprogBI_ok`, the operations, of scalar code,
leave the vector registers alone, and so what the side code computes (`SI`),
which they keep (`hstab`), follows it.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.ForwardField
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64
open VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass.X86_64.ForwardField
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64

/-- What code run between the forwarded operations keeps: every register but
`rdx`, the memory and the regions. -/
structure SideKeepF (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .rdx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem SideKeepF.side {M : Mod} {s s' : State} (h : SideKeepF s s') : SideKeep M s s' :=
  ⟨fun r hr => h.gpr r fun e => hr (e ▸ by simp [clob]), h.mem, h.rd, h.wr⟩

theorem outputRegs_ne_rdx {M : Mod} (hn : M.n = 4) (op : FOp) : ∀ r ∈ outputRegs M op, r ≠ .rdx := by
  cases op with
  | mul o a b =>
    simp only [outputRegs]
    split
    · decide
    · rw [hn]; decide
  | add o a b => simp only [outputRegs]; decide
  | sub o a b => simp only [outputRegs]; decide

theorem ofStores_ne {rs : List Reg} (h : ∀ r ∈ rs, r ≠ .rdx) :
    ∀ o, ∀ c ∈ Forward.ofStores rs o, c.2 ≠ .rdx := by
  induction rs with
  | nil => intro o c hc; cases hc
  | cons r rs ih =>
    intro o c hc
    simp only [Forward.ofStores, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact h r (List.mem_cons_self ..)
    · exact ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) _ c hc

/-- A cache without `rdx` survives code that keeps all else. -/
theorem valid_side {cs : Forward.Cache} (hcs : ∀ c ∈ cs, c.2 ≠ .rdx) {s s' : State}
    (hc : Forward.Valid cs s) (h : SideKeepF s s') : Forward.Valid cs s' := by
  intro c hmem
  have e := hc c hmem
  simp only [State.load64] at e ⊢
  rw [h.mem, h.rd, h.wr, h.gpr _ (by decide), h.gpr _ (hcs c hmem)]
  exact e

/-- `step_ok`, with what an operation of scalar code keeps of the vector
registers and the symbols. -/
theorem stepV_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hn : M.n = 4) (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n)))
    {V : List Nat} {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s)
    {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x) (hR : ∀ x ∈ op.ins, x ∈ V)
    (hsc : (code M op).all scalarI = true) {cs : Forward.Cache} (hc : Forward.Valid cs s) :
    WP isa (.block (Forward.block cs (code M op))) s fun t =>
      ((OpKeep M base op.out s t ∧ Inv M base size m Sl (op.out :: V) (op.run E) t) ∧
        t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.syms = s.syms) ∧
      Forward.Valid (outputCache M op) t := by
  apply Forward.block_wp hc
  obtain ⟨is, he⟩ := code_stores hn op
  have h := WP.mono_syms (WP.vecKeep (c := .block (code M op)) hsc (code_ok hL hm hI hS hR))
    fun t ⟨q, x, y⟩ sy => (⟨q, x, y, sy⟩ : (OpKeep M base op.out s t ∧
      Inv M base size m Sl (op.out :: V) (op.run E) t) ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.syms = s.syms)
  rw [he] at h ⊢
  apply Forward.block_stores_valid h (fun _ ht => ht.1.2.scr)
  · rw [outputRegs_length hn]
    have hle := hL.le op.out (hS _ (List.mem_cons_self ..))
    simpa only [hn] using hle
  · exact outputRegs_nodup hn op

section
variable {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
  {side : Nat → List Instr} {SI : Nat → State → Prop} {N : Nat}

theorem keep_cons {op : FOp} {ops : List FOp} {s s₁ s₂ s₃ : State} (k₁ : OpKeep M base op.out s s₁)
    (k₂ : SideKeep M s₁ s₂) (k₃ : ProgKeep M base (ops.map FOp.out) s₂ s₃) :
    ProgKeep M base ((op :: ops).map FOp.out) s s₃ := by
  have k₁' : ProgKeep M base [op.out] s s₁ :=
    ⟨k₁.gpr, k₁.rd, k₁.wr, fun x hx ht => k₁.mem x (hx _ (List.mem_cons_self ..)) ht⟩
  have h := (k₁'.append (ProgKeep.of_side [] k₂)).append k₃
  exact ⟨h.gpr, h.rd, h.wr, fun x hx ht => h.mem x (fun w hw => hx w (by
    simp only [List.map_cons, List.mem_cons, List.append_nil, List.cons_append, List.nil_append] at hw ⊢
    exact hw)) ht⟩

/-- The forwarded program with side code. -/
theorem codesI_ok (hn : M.n = 4) (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n)))
    (hside : ∀ i t, i < N → SI i t → WP isa (.block (side i)) t fun t' => SI (i + 1) t' ∧ SideKeepF t t')
    {W : List Nat} (hstab : ∀ i o t t', o ∈ W → SI i t → OpKeep M base o t t' → t'.xmm = t.xmm →
      t'.ymmHi = t.ymmHi → t'.syms = t.syms → SI i t') :
    ∀ (ops : List FOp) (i : Nat) {V : List Nat} {E : Nat → Fin m} {s : State} {cs : Forward.Cache},
      i + ops.length ≤ N → (∀ op ∈ ops, op.out ∈ W) → (∀ op ∈ ops, (code M op).all scalarI = true) →
      Inv M base size m Sl V E s → SI i s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true → Forward.Valid cs s →
      WP isa (.block (codesI M side cs ops i).flatten) s fun s' => ProgKeep M base (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s' ∧ SI (i + ops.length) s'
  | [], i, _, _, s, _, _, _, _, hI, hS, _, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI, hS⟩
  | op :: ops, i, V, E, s, cs, hN, hW, hsc, hI, hS, hSl, hR, hc => by
    rw [readsOk, Bool.and_eq_true, List.all_eq_true] at hR
    simp only [decide_eq_true_eq] at hR
    simp only [codesI, List.flatten_cons]
    apply WP.block_append
    refine WP.mono (stepV_ok hn hL hm hI (hSl op (List.mem_cons_self ..)) hR.1 (hsc op (List.mem_cons_self ..)) hc)
      fun s₁ ⟨⟨⟨k₁, I₁⟩, x₁, y₁, sy₁⟩, c₁⟩ => ?_
    have hS₁ := hstab i op.out s s₁ (hW op (List.mem_cons_self ..)) hS k₁ x₁ y₁ sy₁
    apply WP.block_append
    refine WP.mono (hside i s₁ (by rw [List.length_cons] at hN; omega) hS₁) fun s₂ ⟨hS₂, k₂⟩ => ?_
    have c₂ := valid_side (ofStores_ne (outputRegs_ne_rdx hn op) op.out) c₁ k₂
    refine WP.mono (codesI_ok hn hL hm hside hstab ops (i + 1) (by rw [List.length_cons] at hN; omega)
      (fun op' h => hW op' (List.mem_cons_of_mem _ h)) (fun op' h => hsc op' (List.mem_cons_of_mem _ h))
      (I₁.of_side k₂.side) hS₂ (fun op' h => hSl op' (List.mem_cons_of_mem _ h)) hR.2 c₂)
      fun s₃ ⟨k₃, I₃, hS₃⟩ =>
        ⟨keep_cons k₁ k₂.side k₃, I₃, by rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]; exact hS₃⟩

/-- The plain program with side code. -/
theorem plainI_ok (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n)))
    (hside : ∀ i t, i < N → SI i t → WP isa (.block (side i)) t fun t' => SI (i + 1) t' ∧ SideKeepF t t')
    {W : List Nat} (hstab : ∀ i o t t', o ∈ W → SI i t → OpKeep M base o t t' → t'.xmm = t.xmm →
      t'.ymmHi = t.ymmHi → t'.syms = t.syms → SI i t') :
    ∀ (ops : List FOp) (i : Nat) {V : List Nat} {E : Nat → Fin m} {s : State},
      i + ops.length ≤ N → (∀ op ∈ ops, op.out ∈ W) →
      (∀ op ∈ ops, scalCode ((opCall? M op).getD (.block (code M op))) = true) →
      Inv M base size m Sl V E s → SI i s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (plainI M ops side i).inline s fun s' => ProgKeep M base (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s' ∧ SI (i + ops.length) s'
  | [], i, _, _, s, _, _, _, hI, hS, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI, hS⟩
  | op :: ops, i, V, E, s, hN, hW, hsc, hI, hS, hSl, hR => by
    rw [readsOk, Bool.and_eq_true, List.all_eq_true] at hR
    simp only [decide_eq_true_eq] at hR
    show WP isa (Code.seq ((opCall? M op).getD (.block (code M op))).inline
      (Code.seq (.block (side i)) (plainI M ops side (i + 1)).inline)) s _
    refine WP.seq (WP.mono_syms (WP.vecKeep (scalCode_inline (hsc op (List.mem_cons_self ..)))
      (plainOp_ok hL hm hI (hSl op (List.mem_cons_self ..)) hR.1)) fun s₁ ⟨⟨k₁, I₁⟩, x₁, y₁⟩ sy₁ => ?_)
    have hS₁ := hstab i op.out s s₁ (hW op (List.mem_cons_self ..)) hS k₁ x₁ y₁
      sy₁
    refine WP.seq (WP.mono (hside i s₁ (by rw [List.length_cons] at hN; omega) hS₁) fun s₂ ⟨hS₂, k₂⟩ => ?_)
    refine WP.mono (plainI_ok hL hm hside hstab ops (i + 1) (by rw [List.length_cons] at hN; omega)
      (fun op' h => hW op' (List.mem_cons_of_mem _ h)) (fun op' h => hsc op' (List.mem_cons_of_mem _ h))
      (I₁.of_side k₂.side) hS₂ (fun op' h => hSl op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₃ ⟨k₃, I₃, hS₃⟩ =>
        ⟨keep_cons k₁ k₂.side k₃, I₃, by rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]; exact hS₃⟩

/-- `programB_ok` with the block `side k` after operation `k`: the field
program computes what it does, and the side code `SI` from `SI 0` to
`SI ops.length`, for operations of scalar code. -/
theorem programBI_ok (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n)))
    (hside : ∀ i t, i < N → SI i t → WP isa (.block (side i)) t fun t' => SI (i + 1) t' ∧ SideKeepF t t')
    {W : List Nat} (hstab : ∀ i o t t', o ∈ W → SI i t → OpKeep M base o t t' → t'.xmm = t.xmm →
      t'.ymmHi = t.ymmHi → t'.syms = t.syms → SI i t')
    (ops : List FOp) (hW : ∀ op ∈ ops, op.out ∈ W) (hN : ops.length ≤ N)
    (hsc : ∀ op ∈ ops, (code M op).all scalarI = true ∧
      scalCode ((opCall? M op).getD (.block (code M op))) = true)
    {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hS : SI 0 s) (hSl : ∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : readsOk ops V = true) :
    WP isa (programBI M ops side).inline s fun s' =>
      ProgKeep M base (ops.map FOp.out) s s' ∧
      Inv M base size m Sl (validAfter ops V) (runOps ops E) s' ∧ SI ops.length s' := by
  rw [programBI]
  split
  · rename_i h
    rw [Code.inline_of_noCalls (blocks_noCalls _)]
    apply (blocks_wp _).mpr
    refine WP.mono (codesI_ok h.2 hL hm hside hstab ops 0 (by omega) hW (fun op hop => (hsc op hop).1) hI hS hSl hR
      (fun _ h => by cases h)) fun t ⟨k, I, S⟩ => ⟨k, I, by rw [Nat.zero_add] at S; exact S⟩
  · refine WP.mono (plainI_ok hL hm hside hstab ops 0 (by omega) hW (fun op hop => (hsc op hop).2) hI hS hSl hR)
      fun t ⟨k, I, S⟩ => ⟨k, I, by rw [Nat.zero_add] at S; exact S⟩

end

end VG.Proof.Weierstrass.X86_64.ForwardField
