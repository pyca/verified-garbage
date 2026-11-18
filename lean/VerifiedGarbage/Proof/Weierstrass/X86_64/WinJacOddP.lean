module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddWin
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOddP
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJP
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.JacAdd
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelect
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Impl.Weierstrass.X86_64.ForwardFieldI
public import VerifiedGarbage.Proof.Weierstrass.X86_64.FprogI
public import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardStores
import VerifiedGarbage.Proof.Weierstrass.X86_64.ForwardField
import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-! ### `Weierstrass.X86_64.WinJacOddPSel`, which only this module used -/

section

/-! ### `Weierstrass.X86_64.ForwardFieldI`, which only this module used -/

section

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
    refine WP.mono (hside i s₁ (by rw [List.length_cons] at hN; omega_using [hN]) hS₁) fun s₂ ⟨hS₂, k₂⟩ => ?_
    have c₂ := valid_side (ofStores_ne (outputRegs_ne_rdx hn op) op.out) c₁ k₂
    refine WP.mono (codesI_ok hn hL hm hside hstab ops (i + 1) (by rw [List.length_cons] at hN; omega_using [hN])
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
    refine WP.seq (WP.mono (hside i s₁ (by rw [List.length_cons] at hN; omega_using [hN]) hS₁) fun s₂ ⟨hS₂, k₂⟩ => ?_)
    refine WP.mono (plainI_ok hL hm hside hstab ops (i + 1) (by rw [List.length_cons] at hN; omega_using [hN])
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
    refine WP.mono (codesI_ok h.2 hL hm hside hstab ops 0 (by omega_using [hN]) hW (fun op hop => (hsc op hop).1) hI hS hSl hR
      (fun _ h => by cases h)) fun t ⟨k, I, S⟩ => ⟨k, I, by rw [Nat.zero_add] at S; exact S⟩
  · refine WP.mono (plainI_ok hL hm hside hstab ops 0 (by omega_using [hN]) hW (fun op hop => (hsc op hop).2) hI hS hSl hR)
      fun t ⟨k, I, S⟩ => ⟨k, I, by rw [Nat.zero_add] at S; exact S⟩

end

end VG.Proof.Weierstrass.X86_64.ForwardField

end

end

/-! ### `Weierstrass.X86_64.SelectX`, which only this module used -/

section

/-!
# The selection with SSE2 and a counter on x86-64

`selEntryX` (`Impl/Weierstrass/X86_64/WinJacOddP.lean`) is `selEntryAt` with
the mask of entry `m` from `pcmpeqd` of the broadcasts of `m` (a counter in
`xmm11`, incremented by `paddd`) and of the magnitude `a` (in `xmm13`), as
`selEntryY` takes it with AVX2, rather than from `r8`: after entry `m` the
accumulators hold their pieces of entry `a` if `1 ≤ a ≤ m`, else zero
(`accVal`, `selEntriesFromX_ok`), and no general-purpose register but `rdx`
is read or written.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass

theorem selAcc_neX : ∀ c < 10, selAcc c ≠ .xmm11 ∧ selAcc c ≠ .xmm12 ∧ selAcc c ≠ .xmm13 ∧
    selAcc c ≠ .xmm14 ∧ selAcc c ≠ .xmm15 := by decide

/-- `pshufd` by `0` of `movq`'s result: doubleword `0` in every one. -/
theorem shuf0_movq {a : Nat} (ha : a < 2 ^ 32) :
    shufDwords ((0 : BitVec 64) ++ BitVec.ofNat 64 a) 0 = bcast32 (BitVec.ofNat 32 a) := by
  have e : ∀ i, ((0 : BitVec 8).extractLsb' i 2).toNat = 0 := fun i => by
    simp
  simp only [shufDwords, e, dword_movq ha]

/-- `r = a` broadcast to every doubleword of `d`. -/
theorem bcastX_ok (s : State) (d : XReg) (r : Reg) {a : Nat} (ha : a < 2 ^ 32)
    (hr : s.gpr r = BitVec.ofNat 64 a) :
    WP isa (.block [.xop (.movq d r), .xop (.pshufd d d 0)]) s fun t =>
      t.xmm d = bcast32 (BitVec.ofNat 32 a) ∧ XKeep [] (· = d) s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, RegUpd.xmm_setXmm_self, hr,
    shuf0_movq ha, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl, fun x hx => by
    rw [RegUpd.xmm_setXmm_of_ne _ _ hx, RegUpd.xmm_setXmm_of_ne _ _ hx]⟩

/-- The magnitude `r8 = a` broadcast to `xmm13`, and one to `xmm12` and the
counter `xmm11`, through `rcx`. -/
theorem selSetX_ok (s : State) {a : Nat} (ha : a < 2 ^ 31) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block [.xop (.movq .xmm13 .r8), .xop (.pshufd .xmm13 .xmm13 0), .mov32 .rcx (.imm 1),
      .xop (.movq .xmm12 .rcx), .xop (.pshufd .xmm12 .xmm12 0), .xop (.bin .movdqa .xmm11 .xmm12)]) s fun t =>
      t.xmm .xmm13 = bcast32 (BitVec.ofNat 32 a) ∧ t.xmm .xmm12 = bcast32 (BitVec.ofNat 32 1) ∧
      t.xmm .xmm11 = bcast32 (BitVec.ofNat 32 1) ∧
      XKeep [.rcx] (fun r => r = .xmm11 ∨ r = .xmm12 ∨ r = .xmm13) s t := by
  rw [show ([.xop (.movq .xmm13 .r8), .xop (.pshufd .xmm13 .xmm13 0), .mov32 .rcx (.imm 1),
      .xop (.movq .xmm12 .rcx), .xop (.pshufd .xmm12 .xmm12 0), .xop (.bin .movdqa .xmm11 .xmm12)] : List Instr) =
    [.xop (.movq .xmm13 .r8), .xop (.pshufd .xmm13 .xmm13 0)] ++ ([.mov32 .rcx (.imm 1)] ++
      ([.xop (.movq .xmm12 .rcx), .xop (.pshufd .xmm12 .xmm12 0)] ++
        [.xop (.bin .movdqa .xmm11 .xmm12)])) from rfl, WP.block_append_iff]
  refine WP.mono (bcastX_ok s .xmm13 .r8 (by omega_using [ha]) h8) fun s₁ ⟨b₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rcx (.imm 1)]) s₁ (fun s₂ =>
      s₂.gpr .rcx = BitVec.ofNat 64 1 ∧ XKeep [.rcx] (fun _ => False) s₁ s₂) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      Option.some.injEq, exists_eq_left', State.setReg32, RegUpd.gpr_setReg, ite_true]
    refine ⟨by decide, fun r hr => ?_, rfl, rfl, rfl, fun _ _ => rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₂ ⟨c₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (bcastX_ok s₂ .xmm12 .rcx (by decide) c₂) fun s₃ ⟨b₃, k₃⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, XBinOp.eval, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, fun x hx => ?_⟩⟩
  · rw [RegUpd.xmm_setXmm_of_ne _ _ (by decide), k₃.xmm _ (by decide), k₂.xmm _ id, b₁]
  · rw [RegUpd.xmm_setXmm_of_ne _ _ (by decide), b₃]
  · rw [RegUpd.xmm_setXmm_self, b₃]
  · rw [RegUpd.gpr_setXmm, k₃.gpr r List.not_mem_nil, k₂.gpr r hr, k₁.gpr r List.not_mem_nil]
  · rw [RegUpd.mem_setXmm, k₃.mem, k₂.mem, k₁.mem]
  · show s₃.rd = s.rd; rw [k₃.rd, k₂.rd, k₁.rd]
  · show s₃.wr = s.wr; rw [k₃.wr, k₂.wr, k₁.wr]
  · simp only [not_or] at hx
    rw [RegUpd.xmm_setXmm_of_ne _ _ hx.1, k₃.xmm _ hx.2.1, k₂.xmm _ id, k₁.xmm _ hx.2.2]

/-- The mask of `a = m` in `xmm15`, from the counter `xmm11 = m` and the
broadcast magnitude `xmm13 = a`, and the counter incremented by `xmm12 = 1`. -/
theorem selMaskX_ok (s : State) {a m : Nat} (ha : a < 2 ^ 31) (hm : m < 2 ^ 31)
    (h13 : s.xmm .xmm13 = bcast32 (BitVec.ofNat 32 a)) (h12 : s.xmm .xmm12 = bcast32 (BitVec.ofNat 32 1))
    (h11 : s.xmm .xmm11 = bcast32 (BitVec.ofNat 32 m)) :
    WP isa (.block [.xop (.bin .movdqa .xmm15 .xmm11), .xop (.bin .pcmpeqd .xmm15 .xmm13),
        .xop (.bin .paddd .xmm11 .xmm12)]) s fun t =>
      t.xmm .xmm15 = bmask128 (decide (a = m)) ∧ t.xmm .xmm11 = bcast32 (BitVec.ofNat 32 (m + 1)) ∧
      XKeep [] (fun r => r = .xmm11 ∨ r = .xmm15) s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr => ?_⟩⟩
  · rw [RegUpd.xmm_setXmm_of_ne _ _ (by decide), RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_self,
      RegUpd.xmm_setXmm_of_ne _ _ (by decide), h13, XBinOp.eval, h11, pcmpeqd_bcast,
      ofNat32_eq (show a < 2 ^ 32 by omega_using [ha]) (show m < 2 ^ 32 by omega_using [hm])]
  · simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm11 = .xmm15 by decide),
      RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm12 = .xmm15 by decide), h11, h12, paddd_bcast,
      ← BitVec.ofNat_add]
  · simp only [not_or] at hr
    rw [RegUpd.xmm_setXmm_of_ne _ _ hr.1, RegUpd.xmm_setXmm_of_ne _ _ hr.2, RegUpd.xmm_setXmm_of_ne _ _ hr.2]

/-- The accumulators after entries `1 … m`, 16 bytes at a time: accumulator
`c` is piece `c` (`accVal`). -/
def AccX (t : State) (mem : Mem) (X : Addr) (st a m np : Nat) : Prop :=
  ∀ c < np, t.xmm (selAcc c) = accVal mem X st (16 * ·) a m c

/-- Entry `m` of the table at `rdx = X` kept in the accumulators under the
mask of `a = m`, and the counter incremented. -/
theorem selEntryX_ok {st np : Nat} {s : State} {X : Addr} {a m : Nat} (hn : np ≤ 10)
    (hm1 : 1 ≤ m) (hm : m < 2 ^ 31) (ha : a < 2 ^ 31) (hx : s.gpr .rdx = X)
    (h13 : s.xmm .xmm13 = bcast32 (BitVec.ofNat 32 a)) (h12 : s.xmm .xmm12 = bcast32 (BitVec.ofNat 32 1))
    (h11 : s.xmm .xmm11 = bcast32 (BitVec.ofNat 32 m))
    (hr : ∀ c < np, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (st * (m - 1) + 16 * c)) 16)
    (hacc : AccX s s.mem X st a (m - 1) np) :
    WP isa (.block (selEntryX st np m)) s fun t =>
      AccX t s.mem X st a m np ∧ t.xmm .xmm11 = bcast32 (BitVec.ofNat 32 (m + 1)) ∧
      XKeep [] (fun r => (∃ c < np, r = selAcc c) ∨ r = .xmm11 ∨ r = .xmm14 ∨ r = .xmm15) s t := by
  rw [selEntryX, WP.block_append_iff]
  refine WP.mono (selMaskX_ok s ha hm h13 h12 h11) fun s₁ ⟨x₁, c₁, k₁⟩ => ?_
  refine WP.mono (selSteps_ok (X := X) (po := (16 * ·)) (by omega_using [hn]) np (Nat.le_refl _) s₁
    (by rw [k₁.gpr _ List.not_mem_nil, hx]) (by rw [k₁.rd, k₁.wr]; exact hr)) fun t ⟨a₂, k₂⟩ =>
    ⟨fun c hc => ?_, ?_, ?_⟩
  · obtain ⟨n11, -, -, -, n15⟩ := selAcc_neX c (by omega_using [hn, hc])
    rw [a₂ c (by omega_using [hn, hc]), ite_eq_left_of_eq_true _ _ (eq_true hc), x₁, k₁.mem,
      k₁.xmm _ (by rintro (h | h); exacts [n11 h, n15 h]), hacc c hc]
    exact accVal_step _ _ _ (16 * ·) _ _ _ hm1
  · rw [k₂.xmm _ (by
      rintro (⟨c, hc, h⟩ | h)
      · exact (selAcc_neX c (by omega_using [hn, hc])).1 h.symm
      · exact absurd h (by decide)), c₁]
  · exact (k₁.mono (fun _ h => h) fun r h => by
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))).trans (k₂.mono (fun _ h => h) fun r h => by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h)))

/-- Entries `lo + 1 … lo + h` of the table at `rdx = X` kept in the
accumulators (holding entries `1 … lo`) under the masks of `a`, the counter
from `lo + 1`. -/
theorem selEntriesFromX_ok {st np : Nat} {X : Addr} {a lo : Nat} (hn : np ≤ 10) (ha : a < 2 ^ 31) :
    ∀ h, lo + h < 2 ^ 31 → ∀ (s : State), s.gpr .rdx = X →
    s.xmm .xmm13 = bcast32 (BitVec.ofNat 32 a) → s.xmm .xmm12 = bcast32 (BitVec.ofNat 32 1) →
    s.xmm .xmm11 = bcast32 (BitVec.ofNat 32 (lo + 1)) →
    (∀ e < h, ∀ c < np, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (st * (lo + e) + 16 * c)) 16) →
    AccX s s.mem X st a lo np →
    WP isa (.block ((List.range h).flatMap fun e => selEntryX st np (lo + e + 1))) s fun t =>
      AccX t s.mem X st a (lo + h) np ∧ t.xmm .xmm11 = bcast32 (BitVec.ofNat 32 (lo + h + 1)) ∧
      XKeep [] (fun r => (∃ c < np, r = selAcc c) ∨ r = .xmm11 ∨ r = .xmm14 ∨ r = .xmm15) s t
  | 0, _, s, _, _, _, h11, _, h0 => WP.block_nil ⟨h0, h11, XKeep.refl _ _ _⟩
  | h + 1, hh, s, hx, h13, h12, h11, hr, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (selEntriesFromX_ok hn ha h (by omega_using [hh]) s hx h13 h12 h11 (fun e he => hr e (by omega_using [he])) h0)
      fun s₁ ⟨a₁, c₁, k₁⟩ => ?_
    have n13 : ¬ ((∃ c < np, XReg.xmm13 = selAcc c) ∨ XReg.xmm13 = .xmm11 ∨ XReg.xmm13 = .xmm14 ∨
        XReg.xmm13 = .xmm15) := by
      rintro (⟨c, hc, h⟩ | h | h | h)
      · exact (selAcc_neX c (by omega_using [hn, hc])).2.2.1 h.symm
      all_goals exact absurd h (by decide)
    have n12 : ¬ ((∃ c < np, XReg.xmm12 = selAcc c) ∨ XReg.xmm12 = .xmm11 ∨ XReg.xmm12 = .xmm14 ∨
        XReg.xmm12 = .xmm15) := by
      rintro (⟨c, hc, h⟩ | h | h | h)
      · exact (selAcc_neX c (by omega_using [hn, hc])).2.1 h.symm
      all_goals exact absurd h (by decide)
    refine WP.mono (selEntryX_ok (X := X) (m := lo + h + 1) hn (by omega_using []) hh ha
      (by rw [k₁.gpr _ List.not_mem_nil, hx]) (by rw [k₁.xmm _ n13, h13])
      (by rw [k₁.xmm _ n12, h12]) c₁
      (fun c hc => by rw [k₁.rd, k₁.wr, Nat.add_sub_cancel]; exact hr h (by omega_using []) c hc)
      (fun c hc => by rw [a₁ c hc, k₁.mem, Nat.add_sub_cancel])) fun t ⟨a₂, c₂, k₂⟩ =>
      ⟨fun c hc => by rw [a₂ c hc, k₁.mem, ← Nat.add_assoc], by
        rw [show lo + (h + 1) + 1 = lo + h + 1 + 1 by omega_using []]; exact c₂, k₁.trans k₂⟩

end VG.Proof.Weierstrass.X86_64

end

end

/-!
# The odd window method on x86-64: the selection woven into the addition

What the selection of digit `j - 1`'s entry keeps between the addition's
field operations (`SelP`): the broadcasts of its magnitude `a` and of one,
the counter and the accumulators after entries `1 … e` (`SelS`: 32 bytes at
a time with AVX2, `AccY`, else 16, `AccX`), of the table at `rdi + tbl` as
in the memory `mem` it started from, whose bytes the state still holds. The
field operations keep it (`SelP.stab`), writing neither the vector registers
nor the table; each part of the selection advances it (`selChunkO_ok`),
writing no register but `rdx` (`SideKeepF`); `selSetP_ok` starts it and
`storeP_ok` stores the accumulators to `T`, which then holds entry `a`
(`jselOut`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

variable {K : JacWinCfg} {size : Nat}

/-- The table's address. -/
abbrev tblX (K : JacWinCfg) (base : Addr) : Addr := base + BitVec.ofNat 64 K.tbl

/-- The selection's registers after entries `1 … e` for the magnitude `a`,
the table as in `mem`. -/
def SelS (K : JacWinCfg) (base : Addr) (mem : Mem) (a e : Nat) (t : State) : Prop :=
  if K.avx2 then
    (∀ l < 2, t.lane .xmm13 l = bcast32 (BitVec.ofNat 32 a)) ∧
    (∀ l < 2, t.lane .xmm12 l = bcast32 (BitVec.ofNat 32 1)) ∧
    (∀ l < 2, t.lane .xmm14 l = bcast32 (BitVec.ofNat 32 (e + 1))) ∧
    AccY t mem (tblX K base) K.st a e K.np32 (qY K.np16)
  else
    t.xmm .xmm13 = bcast32 (BitVec.ofNat 32 a) ∧ t.xmm .xmm12 = bcast32 (BitVec.ofNat 32 1) ∧
    t.xmm .xmm11 = bcast32 (BitVec.ofNat 32 (e + 1)) ∧ AccX t mem (tblX K base) K.st a e K.np16

/-- The selection between the addition's operations: `SelS`, the table's
bytes as in `mem`, in the regions, and `rdi` the working space. -/
structure SelP (K : JacWinCfg) (base : Addr) (mem : Mem) (a e : Nat) (t : State) : Prop where
  ha : a ≤ 16
  sel : SelS K base mem a e t
  tblm : ∀ b < 16 * K.st, t.mem (tblX K base + BitVec.ofNat 64 b) = mem (tblX K base + BitVec.ofNat 64 b)
  reg : InRegions (t.rd ++ t.wr) (tblX K base) (16 * K.st)
  rdi : t.gpr .rdi = base

theorem SelS.of_vec {base : Addr} {mem : Mem} {a e : Nat} {t t' : State} (h : SelS K base mem a e t)
    (hx : t'.xmm = t.xmm) (hy : t'.ymmHi = t.ymmHi) : SelS K base mem a e t' := by
  unfold SelS at h ⊢
  have hl := lane_congr hx hy
  split
  · next hv =>
    rw [ite_eq_left_of_eq_true _ _ (eq_true hv)] at h
    exact ⟨fun l hl' => by rw [hl]; exact h.1 l hl', fun l hl' => by rw [hl]; exact h.2.1 l hl',
      fun l hl' => by rw [hl]; exact h.2.2.1 l hl', fun c hc l hl' => by rw [hl]; exact h.2.2.2 c hc l hl'⟩
  · next hv =>
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)] at h
    exact ⟨by rw [hx]; exact h.1, by rw [hx]; exact h.2.1, by rw [hx]; exact h.2.2.1,
      fun c hc => by rw [hx]; exact h.2.2.2 c hc⟩

/-- The table's entries: `16 st = 80 (8 n)` bytes. -/
theorem st16 (K : JacWinCfg) : 16 * K.st = 80 * (8 * K.M.n) := by
  unfold JacWinCfg.st; omega_arith

/-- A range apart from the table's 80 slots is apart from each of its bytes. -/
theorem tbl_byte_apart (hL : JacWinLay K size) {w : Nat × Nat}
    (hw : ∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) {b : Nat} (hb : b < 16 * K.st) :
    K.tbl + b + 1 ≤ w.1 ∨ w.1 + w.2 ≤ K.tbl + b := by
  have h0 := hL.n0
  rw [st16] at hb
  have hi : b / (8 * K.M.n) < 80 := (Nat.div_lt_iff_lt_mul (by omega_arith)).mpr (by rw [Nat.mul_comm]; omega_arith)
  have h1 := Nat.div_mul_le_self b (8 * K.M.n)
  have h2 := Nat.lt_div_mul_add (a := b) (show 0 < 8 * K.M.n by omega_arith)
  have := hw _ hi
  unfold jg at this
  rw [Nat.mul_comm (8 * K.M.n)] at this
  generalize b / (8 * K.M.n) * (8 * K.M.n) = q at h1 h2 this
  omega_arith

/-- Byte `b` of the table: `off base (tbl + b)`. -/
theorem tblX_off (K : JacWinCfg) (base : Addr) (b : Nat) :
    tblX K base + BitVec.ofNat 64 b = off base (K.tbl + b) := Offset.add_add base _ _

/-- The table's bytes survive a write that misses its slots. -/
theorem tblm_unch (hL : JacWinLay K size) {base : Addr} {W : List (Nat × Nat)} {m m' : Mem}
    (hU : Unch base W m m') (hn : base.toNat + size ≤ 2 ^ 64)
    (hW : ∀ w ∈ W, ∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) :
    ∀ b < 16 * K.st, m' (tblX K base + BitVec.ofNat 64 b) = m (tblX K base + BitVec.ofNat 64 b) := by
  intro b hb
  have hg := hL.grid_le
  have := st16 K
  rw [tblX_off]
  exact hU.byte (fun w hw => tbl_byte_apart hL (hW w hw) hb) (by omega_arith)

/-- A slot but the grid's, and the temporary area, miss the table's slots. -/
theorem other_tbl_apart (hL : JacWinLay K size) {o : Nat} (ho : o ∈ jwOther K) :
    ∀ w ∈ [(o, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], ∀ i < 80, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i := by
  intro w hw i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact (hL.jg_apart (List.mem_append_right _ ho) (i := i) (by omega_arith)).symm
  · exact hL.lay.tmp _ (jg_mem (by omega_arith))

/-- A field operation writing a slot but the grid's keeps the selection
(`programBI_ok`'s `hstab`). -/
theorem SelP.stab (hL : JacWinLay K size) {base : Addr} {mem : Mem} {a e o : Nat} (ho : o ∈ jwOther K)
    (hn : base.toNat + size ≤ 2 ^ 64) {t t' : State} (h : SelP K base mem a e t)
    (hk : OpKeep K.M base o t t') (hx : t'.xmm = t.xmm) (hy : t'.ymmHi = t.ymmHi) :
    SelP K base mem a e t' :=
  ⟨h.ha, h.sel.of_vec hx hy, fun b hb => by
    rw [tblm_unch hL hk.unch hn (other_tbl_apart hL ho) b hb]; exact h.tblm b hb,
    by rw [hk.rd, hk.wr]; exact h.reg, by rw [hk.gpr _ (rdi_not_clob _)]; exact h.rdi⟩

/-- `rdx = rdi + tbl`. -/
theorem tblRdx_ok (hL : JacWinLay K size) (s : State) {base : Addr} (hd : s.gpr .rdi = base) :
    WP isa (.block [.mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl))]) s fun t =>
      t.gpr .rdx = tblX K base ∧ Keeps [.rdx] s t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  have ht := hL.tbl31
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.map_some, imm32_sext ht, hd, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- An entry's pieces: ten for four words. -/
theorem np_four (hL : JacWinLay K size) (hn4 : K.M.n = 4) :
    K.np16 = 10 ∧ K.np32 = 5 ∧ K.st = 16 * K.np16 := by
  obtain ⟨-, hst, -⟩ := np16_eq hL
  unfold JacWinCfg.np32 JacWinCfg.np16 at *
  rw [hn4] at *
  exact ⟨rfl, rfl, hst⟩

theorem AccX.congr {t : State} {m m' : Mem} {X : Addr} {n H a e : Nat} (ha : a ≤ H)
    (h : ∀ b < 16 * n * H, m (X + BitVec.ofNat 64 b) = m' (X + BitVec.ofNat 64 b))
    (hA : AccX t m X (16 * n) a e n) : AccX t m' X (16 * n) a e n :=
  fun c hc => by rw [hA c hc]; exact accVal_congr ha hc h

theorem chunkO_le (K : JacWinCfg) {i : Nat} (hi : i < K.nAddO) :
    K.chunkO i ≤ K.chunkO (i + 1) ∧ K.chunkO (i + 1) ≤ 16 := by
  unfold JacWinCfg.chunkO
  exact ⟨Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega_arith)),
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm K.nAddO]; exact Nat.mul_le_mul_left _ (by omega_arith))⟩

/-- A part of the selection (`programBI_ok`'s `hside`): entries `chunkO i + 1`
to `chunkO (i + 1)`. -/
theorem selChunkO_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) {base : Addr} {mem : Mem} {a : Nat} (i : Nat)
    (hi : i < K.nAddO) {t : State} (h : SelP K base mem a (K.chunkO i) t) :
    WP isa (.block (K.selChunkO i)) t fun t' => SelP K base mem a (K.chunkO (i + 1)) t' ∧
      ForwardField.SideKeepF t t' := by
  obtain ⟨hlo, hhi⟩ := chunkO_le K hi
  obtain ⟨h10, h5, hst⟩ := np_four hL hn4
  unfold JacWinCfg.selChunkO
  split
  · next he => exact WP.block_nil ⟨by rw [he]; exact h, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  rw [WP.block_append_iff]
  refine WP.mono (tblRdx_ok hL t h.rdi) fun t₁ ⟨x₁, k₁, xx₁, xy₁⟩ => ?_
  have hm₁ : t₁.mem = t.mem := k₁.2.1
  have hT : ∀ b < 16 * K.np16 * 16, mem (tblX K base + BitVec.ofNat 64 b) =
      t₁.mem (tblX K base + BitVec.ofNat 64 b) := fun b hb => by
    rw [hm₁]; exact (h.tblm b (by rw [hst]; omega_arith)).symm
  have hT' : ∀ b < 16 * K.np16 * 16, t₁.mem (tblX K base + BitVec.ofNat 64 b) =
      mem (tblX K base + BitVec.ofNat 64 b) := fun b hb => (hT b hb).symm
  have hreg : InRegions (t₁.rd ++ t₁.wr) (tblX K base) (16 * K.st) := by
    rw [k₁.2.2.1, k₁.2.2.2]; exact h.reg
  have hS₁ := h.sel.of_vec xx₁ xy₁
  have hdi : t₁.gpr .rdi = base := by rw [k₁.1 _ (by decide)]; exact h.rdi
  have side : ∀ {t' : State}, t'.mem = t₁.mem → t'.rd = t₁.rd → t'.wr = t₁.wr →
      (∀ r, r ≠ .rdx → t'.gpr r = t₁.gpr r) → ForwardField.SideKeepF t t' := fun hm hr hw hg =>
    ⟨fun r hr' => by rw [hg r hr', k₁.1 r (by simpa using hr')], by rw [hm, hm₁], by rw [hr, k₁.2.2.1],
      by rw [hw, k₁.2.2.2]⟩
  have hlo' : K.chunkO i + (K.chunkO (i + 1) - K.chunkO i) = K.chunkO (i + 1) := by omega_arith
  unfold SelS at hS₁
  unfold JacWinCfg.selEntryP
  cases hv : K.avx2
  · -- SSE2
    rw [hv, ite_eq_right_of_eq_false _ _ (by simp)] at hS₁
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨b13, b12, b11, acc⟩ := hS₁
    refine WP.mono (selEntriesFromX_ok (X := tblX K base) (st := K.st) (np := K.np16) (lo := K.chunkO i)
      (by omega_arith) (by have := h.ha; omega_arith) (K.chunkO (i + 1) - K.chunkO i) (by omega_arith) t₁ x₁ b13 b12 b11
      (fun e he c hc => by
        refine VG.CallLay.inRegions_sub hreg ?_ (by omega_arith)
        have := Nat.mul_le_mul_left K.st (show K.chunkO i + e + 1 ≤ 16 by omega_arith)
        rw [Nat.mul_succ] at this
        omega_arith)
      (by rw [hst] at acc ⊢; exact AccX.congr (H := 16) h.ha hT acc)) fun t' ⟨a', c', k'⟩ => ?_
    have hm' : t'.mem = t₁.mem := k'.mem
    have n13 : ¬ ((∃ c < K.np16, XReg.xmm13 = selAcc c) ∨ XReg.xmm13 = .xmm11 ∨ XReg.xmm13 = .xmm14 ∨
        XReg.xmm13 = .xmm15) := by
      rintro (⟨c, hc, h'⟩ | h' | h' | h')
      · exact (selAcc_neX c (by omega_arith)).2.2.1 h'.symm
      all_goals exact absurd h' (by decide)
    have n12 : ¬ ((∃ c < K.np16, XReg.xmm12 = selAcc c) ∨ XReg.xmm12 = .xmm11 ∨ XReg.xmm12 = .xmm14 ∨
        XReg.xmm12 = .xmm15) := by
      rintro (⟨c, hc, h'⟩ | h' | h' | h')
      · exact (selAcc_neX c (by omega_arith)).2.1 h'.symm
      all_goals exact absurd h' (by decide)
    refine ⟨⟨h.ha, ?_, fun b hb => by rw [hm', hm₁]; exact h.tblm b hb,
      by rw [k'.rd, k'.wr]; exact hreg, by rw [k'.gpr _ List.not_mem_nil]; exact hdi⟩,
      side hm' k'.rd k'.wr fun r _ => k'.gpr r List.not_mem_nil⟩
    unfold SelS
    rw [hv, ite_eq_right_of_eq_false _ _ (by simp)]
    refine ⟨by rw [k'.xmm _ n13]; exact b13, by rw [k'.xmm _ n12]; exact b12, by rw [← hlo']; exact c', ?_⟩
    rw [hlo', hm₁] at a'
    rw [hst] at a' ⊢
    exact AccX.congr (H := 16) h.ha (fun b hb => (h.tblm b (by rw [hst]; omega_arith))) a'
  · -- AVX2
    rw [hv, ite_eq_left_of_eq_true _ _ (by simp)] at hS₁
    simp only [↓reduceIte]
    obtain ⟨b13, b12, b14, acc⟩ := hS₁
    have hq : ∀ c, qY K.np16 c + 2 ≤ K.np16 := fun c => qY_le c (by omega_arith)
    have hnp : K.np32 = (K.np16 + 1) / 2 := rfl
    refine WP.mono (selEntriesFromY_ok (X := tblX K base) (st := K.st) (np := K.np32) (q := qY K.np16)
      (lo := K.chunkO i) (by omega_arith) (by have := h.ha; omega_arith) (K.chunkO (i + 1) - K.chunkO i) (by omega_arith) t₁ x₁
      b13 b12 b14
      (fun e he c hc => by
        refine VG.CallLay.inRegions_sub hreg ?_ (by omega_arith)
        have := Nat.mul_le_mul_left K.st (show K.chunkO i + e + 1 ≤ 16 by omega_arith)
        rw [Nat.mul_succ] at this
        have := hq c
        omega_arith)
      (by rw [hst, hnp] at acc ⊢; exact AccY.congr (H := 16) h.ha (by omega_arith) hT acc)) fun t' ⟨a', c', k'⟩ => ?_
    have hm' : t'.mem = t₁.mem := k'.mem
    have n13 : ¬ ((∃ c < K.np32, XReg.xmm13 = selAcc c) ∨ XReg.xmm13 = .xmm11 ∨ XReg.xmm13 = .xmm14 ∨
        XReg.xmm13 = .xmm15) := by
      rintro (⟨c, hc, h'⟩ | h' | h' | h')
      · exact (selAcc_neY c (by omega_arith)).2.2.1 h'.symm
      all_goals exact absurd h' (by decide)
    have n12 : ¬ ((∃ c < K.np32, XReg.xmm12 = selAcc c) ∨ XReg.xmm12 = .xmm11 ∨ XReg.xmm12 = .xmm14 ∨
        XReg.xmm12 = .xmm15) := by
      rintro (⟨c, hc, h'⟩ | h' | h' | h')
      · exact (selAcc_neY c (by omega_arith)).2.1 h'.symm
      all_goals exact absurd h' (by decide)
    refine ⟨⟨h.ha, ?_, fun b hb => by rw [hm', hm₁]; exact h.tblm b hb,
      by rw [k'.rd, k'.wr]; exact hreg, by rw [k'.gpr _ List.not_mem_nil]; exact hdi⟩,
      side hm' k'.rd k'.wr fun r _ => k'.gpr r List.not_mem_nil⟩
    unfold SelS
    rw [hv, ite_eq_left_of_eq_true _ _ (by simp)]
    refine ⟨fun l hl => by rw [k'.lane _ n13 l]; exact b13 l hl, fun l hl => by rw [k'.lane _ n12 l]; exact b12 l hl,
      by rw [← hlo']; exact c', ?_⟩
    rw [hlo', hm₁] at a'
    rw [hst, hnp] at a' ⊢
    exact AccY.congr (H := 16) h.ha (by omega_arith) (fun b hb => (h.tblm b (by rw [hst]; omega_arith))) a'

/-- The selection set up for the magnitude `r8 = a ≤ 16`, through `rcx`: no
entry kept yet, of any table. -/
theorem selSetP_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) (s : State) {base : Addr} (mem : Mem) {a : Nat}
    (ha : a ≤ 16) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block K.selSetP) s fun t => SelS K base mem a 0 t ∧ Keeps [.rcx] s t := by
  obtain ⟨h10, h5, -⟩ := np_four hL hn4
  unfold JacWinCfg.selSetP SelS
  cases hv : K.avx2
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (selSetX_ok s (by omega_arith) h8) fun s₁ ⟨b13, b12, b11, k₁⟩ => ?_
    refine WP.mono (clearAcc_ok K.np16 (by omega_arith) s₁) fun t ⟨z, k⟩ => ?_
    have nacc : ∀ r, r = XReg.xmm11 ∨ r = .xmm12 ∨ r = .xmm13 → ¬ ∃ c < K.np16, r = selAcc c := by
      rintro r hr ⟨c, hc, rfl⟩
      obtain ⟨n11, n12, n13, -, -⟩ := selAcc_neX c (by omega_arith)
      rcases hr with h' | h' | h' <;> contradiction
    refine ⟨⟨by rw [k.xmm _ (nacc _ (by simp))]; exact b13, by rw [k.xmm _ (nacc _ (by simp))]; exact b12,
      by rw [k.xmm _ (nacc _ (by simp))]; exact b11, fun c hc => by
        rw [z c hc, accVal, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]⟩,
      fun r hr => by rw [k.gpr r List.not_mem_nil, k₁.gpr r hr], by rw [k.mem, k₁.mem],
      by rw [k.rd, k₁.rd], by rw [k.wr, k₁.wr]⟩
  · simp only [↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (selSetY_ok s (by omega_arith) h8) fun s₁ ⟨b13, b12, b14, k₁⟩ => ?_
    refine WP.mono (clearAccY_ok K.np32 (by omega_arith) s₁) fun t ⟨z, k⟩ => ?_
    have nacc : ∀ r, r = XReg.xmm12 ∨ r = .xmm13 ∨ r = .xmm14 → ¬ ∃ c < K.np32, r = selAcc c := by
      rintro r hr ⟨c, hc, rfl⟩
      obtain ⟨-, n12, n13, n14, -⟩ := selAcc_neY c (by omega_arith)
      rcases hr with h' | h' | h' <;> contradiction
    refine ⟨⟨fun l hl => by rw [k.lane _ (nacc _ (by simp)) l]; exact b13 l hl,
      fun l hl => by rw [k.lane _ (nacc _ (by simp)) l]; exact b12 l hl,
      fun l hl => by rw [k.lane _ (nacc _ (by simp)) l]; exact b14 l hl, fun c hc l hl => by
        rw [z c hc l hl, accVal, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]⟩,
      fun r hr => by rw [k.gpr r List.not_mem_nil, k₁.gpr r hr], by rw [k.mem, k₁.mem],
      by rw [k.rd, k₁.rd], by rw [k.wr, k₁.wr]⟩

/-- The accumulators after the sixteen entries stored to `T`. -/
theorem storeP_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) {base : Addr} {mem : Mem} {a : Nat} {t : State}
    (hs : Scr t base size) (h : SelS K base mem a 16 t) :
    WP isa (.block K.storeP) t fun t' =>
      (∀ c < K.np16, t'.mem.readW (off base (K.T + 16 * c)) 128 = accVal mem (tblX K base) K.st (16 * ·) a 16 c) ∧
      Outside base K.T (16 * K.np16) t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain ⟨h10, h5, hst⟩ := np_four hL hn4
  have hT : K.T + 16 * K.np16 ≤ size := by
    have := hL.grid_le; rw [hL.T80]; unfold jg; rw [h10, hn4] at *; omega_arith
  unfold JacWinCfg.storeP
  unfold SelS at h
  cases hv : K.avx2
  · rw [hv, ite_eq_right_of_eq_false _ _ (by simp)] at h
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.mono (storeAcc_ok K.np16 t hs hT) fun t' ⟨a', O', g', r', w', _⟩ =>
      ⟨fun c hc => by rw [a' c hc]; exact h.2.2.2 c hc, O', g', r', w'⟩
  · rw [hv, ite_eq_left_of_eq_true _ _ (by simp)] at h
    simp only [↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (storeAccY_ok (o := K.T) (n := K.np16) (q := qY K.np16)
      (V := accVal mem (tblX K base) K.st (16 * ·) a 16) hT K.np32 t hs (fun c _ => qY_le c (by omega_arith))
      (fun c hc l hl => h.2.2.2 c hc l hl)) fun t₁ ⟨a₁, O₁, g₁, r₁, w₁, _⟩ => ?_
    refine WP.mono (vzeroupper_ok t₁) fun t' ⟨m', g', r', w'⟩ =>
      ⟨fun j hj => ?_, by rw [m']; exact O₁, by rw [g', g₁], by rw [r', r₁], by rw [w', w₁]⟩
    obtain ⟨c, hc, l, hl, e⟩ := qY_cover (n := K.np16) (by omega_arith) hj
    have := a₁ c (by unfold JacWinCfg.np32; exact hc) l hl
    rw [e] at this
    rw [m']
    exact this

/-- `T`'s five coordinates after `storeP_ok`: entry `a`'s, as in `mem`. -/
theorem jselOut (hL : JacWinLay K size) (hn4 : K.M.n = 4) {base : Addr} {mem mem' : Mem} {a : Nat}
    (ha : 1 ≤ a ∧ a ≤ 16)
    (h : ∀ c < K.np16, mem'.readW (off base (K.T + 16 * c)) 128 = accVal mem (tblX K base) K.st (16 * ·) a 16 c) :
    ∀ c < 5, wordsVal mem' base (jg K (80 + c)) K.M.n = wordsVal mem base (jg K (5 * (a - 1) + c)) K.M.n := by
  obtain ⟨h10, -, hst⟩ := np_four hL hn4
  intro c hc
  rw [hst] at h
  have hw := accVal_word (mem := mem) (mem' := mem') (base := base) (n := K.np16) (o := K.T) h
  have hX : ∀ d, word mem (tblX K base) d = word mem base (K.tbl + d) := fun d => by
    rw [Mont.word, Mont.word, off, off, Offset.add_add]
  have h2n : 2 * K.np16 = 5 * K.M.n := by rw [h10, hn4]
  have hcn := Nat.mul_le_mul_left K.M.n (show c + 1 ≤ 5 by omega_arith)
  rw [Nat.mul_succ] at hcn
  have eT : ∀ i, jg K (80 + c) + 8 * i = K.T + 8 * (K.M.n * c + i) := fun i => by
    rw [hL.T80]; unfold jg; rw [Nat.mul_add, Nat.mul_add, Nat.mul_assoc 8 K.M.n c]; omega_arith
  refine wordsVal_congr₂ _ _ _ fun i hi => ?_
  have e := hw (K.M.n * c + i) (by omega_arith)
  rw [ite_eq_left_of_eq_true _ _ (eq_true ha), hX] at e
  rw [eT, e, ← hst]
  congr 1; unfold jg JacWinCfg.st
  rw [show 40 * K.M.n * (a - 1) = 8 * K.M.n * (5 * (a - 1)) by
    rw [Nat.mul_assoc, Nat.mul_assoc, show 40 = 8 * 5 from rfl, Nat.mul_assoc, Nat.mul_left_comm 5],
    Nat.mul_add (8 * K.M.n), Nat.mul_assoc 8 K.M.n c]
  omega_arith

end VG.Proof.Weierstrass.X86_64

end

end

/-!
# Odd 5-bit windows on x86-64, each selection woven into the addition before it

`JacWinCfg.windowOP K dbl` (`Impl/Weierstrass/X86_64/WinJacOddP.lean`)
computes what `windowO` does (`winJacOP_ok`, as `winJacO_ok`): its loop keeps
digit `j - 1`'s entry in `T` at `rbx = j` (`JInvOP`). An iteration
(`jstepOP_ok`) doubles `R` five times, which writes neither `T` nor the
table; sets up digit `j - 2`'s selection (`selSetP_ok`); adds `T` to `R`
while it selects (`caddOI_ok`, with `SelP` as the side code's state, which
the addition's operations keep, writing only other slots); and stores and
negates the entry (`storeP_ok`, `jselOut`, `jnegO_ok`). Digit `J - 2`'s
entry is selected before the loop (`jfirstOP_ok`), and digit `0`'s addition
selects none (`jlastO_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The woven loop's invariant at `rbx = j`: `JInvO`, and digit `j - 1`'s
point with its powers in `T`. -/
structure JInvOP (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k : Nat) (j : Nat) (s : State) : Prop where
  inv : JInvO K C base size P s₀ k j s
  ent : JPt C K.M.n base s (TS K) (OddWin.oddPt C P K.J k (j - 1))

/-- `T` survives writes to the other slots and the temporary area. -/
theorem JPt.othW (hL : JacWinLay K size) {base : Addr} {s t : State} {Q : Point C}
    (h : JPt C K.M.n base s (TS K) Q) (hU : Unch base (jwOthW K) s.mem t.mem) (hn : base.toNat + size ≤ 2 ^ 64) :
    JPt C K.M.n base t (TS K) Q :=
  h.congr fun c hc => hU.wordsVal (fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      exact (hL.jg_apart (List.mem_append_right _ ho) (i := 80 + c) (by omega_arith)).symm
    · rw [List.mem_singleton.mp hw]; exact hL.lay.tmp _ (jg_mem (by omega_arith)))
    (by show jg K (80 + c) + 8 * K.M.n ≤ 2 ^ 64; have := hL.le (jg_mem (K := K) (i := 80 + c) (by omega_arith)); omega_arith)

/-- What the addition writes are other slots. -/
theorem addOpsO_out (K : JacWinCfg) : ∀ op ∈ K.addOpsO, op.out ∈ rcbW K.S K.R := by
  intro op hop
  rw [JacWinCfg.addOpsO, CachedJac.ip_eq] at hop
  obtain ⟨op', hop', rfl⟩ := List.mem_map.mp hop
  rw [FOp.out_rename]
  exact CachedJac.ipσ_out _ _ _ _ _ (CachedJac.ipN_out op' hop')

theorem rcbW_other (K : JacWinCfg) : ∀ x ∈ rcbW K.S K.R, x ∈ jwOther K := by
  intro x hx
  simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jw_mem

/-- `caddO_ok` with the side code `side i` after operation `i` (`programBI`). -/
theorem caddOI_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {base : Addr}
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p (· ∈ jwSlots K) V E s)
    (hV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n], x ∈ V)
    (h2 : E K.z2 = E K.E.z * E K.E.z) (h3 : E (K.z2 + 8 * K.M.n) = E K.z2 * E K.E.z)
    {side : Nat → List Instr} {SI : Nat → State → Prop}
    (hside : ∀ i t, i < K.addOpsO.length → SI i t →
      WP isa (.block (side i)) t fun t' => SI (i + 1) t' ∧ ForwardField.SideKeepF t t')
    (hstab : ∀ i o t t', o ∈ rcbW K.S K.R → SI i t → OpKeep K.M base o t t' → t'.xmm = t.xmm →
      t'.ymmHi = t.ymmHi → t'.syms = t.syms → SI i t')
    (hsc : ∀ op ∈ K.addOpsO, (ForwardField.code K.M op).all scalarI = true ∧
      scalCode ((opCall? K.M op).getD (.block (ForwardField.code K.M op))) = true)
    (hS : SI 0 s) :
    WP isa (ForwardField.programBI K.M K.addOpsO side).inline s fun t =>
      ProgKeep K.M base (rcbW K.S K.R) s t ∧ (∃ E' : Nat → Fe C,
        Inv K.M base size C.p (· ∈ jwSlots K) ([K.R.x, K.R.y, K.R.z] ++ V) E' t ∧
        (E' K.R.x, E' K.R.y, E' K.R.z) =
          jacAddF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y) (E K.E.z)) ∧
      SI K.addOpsO.length t := by
  have hA := hL.ipApart
  obtain hSl : ∀ x ∈ CachedJac.ipW K.S K.R ++ CachedJac.ipR K.M.n K.S K.E K.z2, x ∈ jwSlots K := by
    intro x hx
    simp only [CachedJac.ipW, CachedJac.ipR, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rw [hL.Tz3, hL.Tx, hL.Ty, hL.Tz, hL.Tz2] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first
      | exact jg_mem (by decide) | jw_mem
  obtain hr : readsOk K.addOpsO V = true := by
    rw [JacWinCfg.addOpsO, CachedJac.ip_eq]
    refine readsOk_mono (readsOk_rename (CachedJac.ipσ K.M.n K.S K.R K.E K.z2)
      (show readsOk (CachedJac.headIPN ++ CachedJac.tailIPN) [6, 7, 8, 11, 12, 13, 14, 15] = true by decide))
      fun x hx => hV x ?_
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h <;> rw [h] <;>
      simp [CachedJac.ipσ, CachedJac.ipW, CachedJac.ipR]
  obtain hs : ∀ op ∈ K.addOpsO, ∀ x ∈ op.out :: op.ins, x ∈ jwSlots K := by
    rw [JacWinCfg.addOpsO, CachedJac.ip_eq]
    intro op hop x hx
    obtain ⟨op', _, rfl⟩ := List.mem_map.mp hop
    refine hSl x ?_
    cases op' <;> simp only [FOp.rename, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil,
      or_false] at hx <;> rcases hx with rfl | rfl | rfl <;> exact CachedJac.ipσ_mem ..
  refine WP.mono (ForwardField.programBI_ok hL.lay hp hside hstab _ (addOpsO_out K) (Nat.le_refl _) hsc hI hS hs hr)
    fun t ⟨kt, it, st⟩ => ⟨kt.mono ?_, ⟨_, it.sub fun x hx => ?_, CachedJac.ip_run hA E h2 h3⟩, st⟩
  · intro x hx
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
    exact addOpsO_out K op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · right
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [JacWinCfg.addOpsO, jacTail, FOp.out]
    · exact Or.inl hx

/-- `R = R + T` from `u` to `t` (`caddO_ok`'s or `caddOI_ok`'s facts), `R` a
triple of `[32 S_{i+1}]P`'s stand-in `Q` and `T` of digit `i`'s point: `R` a
triple of `[S_i]P`'s, and nothing written but other slots. -/
theorem addO_post (hL : JacWinLay K size) (hC : Law C) (hM3 : AM3 C) (hO : PrimeOrder C) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33)
    (hnb : 128 ≤ C.n) {base : Addr} {s₀ u t : State} {k i : Nat} (hi : i + 1 < K.J)
    {Q : Point C} (hQ : onCurve C Q = true)
    (hQe : k % 2 = 1 ∧ k < C.n → Q = mul (32 * OddWin.oS K.J k (i + 1)) P)
    (F : JFrame K C base size s₀ u) (hT : JTblOkO K C base P 16 u)
    (hRep : InvJ C (tmv C K.M.n base u K.R.x) (tmv C K.M.n base u K.R.y) (tmv C K.M.n base u K.R.z) Q)
    (hE : JPt C K.M.n base u (TS K) (OddWin.oddPt C P K.J k i))
    (k₅ : ProgKeep K.M base (rcbW K.S K.R) u t) {V : List Nat} {E₅ : Nat → Fe C}
    (I₅ : Inv K.M base size C.p (· ∈ jwSlots K) ([K.R.x, K.R.y, K.R.z] ++ V) E₅ t)
    (v₅ : (E₅ K.R.x, E₅ K.R.y, E₅ K.R.z) = jacAddF (tmv C K.M.n base u K.R.x) (tmv C K.M.n base u K.R.y)
      (tmv C K.M.n base u K.R.z) (tmv C K.M.n base u K.E.x) (tmv C K.M.n base u K.E.y) (tmv C K.M.n base u K.E.z)) :
    (∃ Q' : Point C, onCurve C Q' = true ∧ (k % 2 = 1 ∧ k < C.n → Q' = mul (OddWin.oS K.J k i) P) ∧
      RStO K C base size P s₀ Q' t) ∧ Unch base (jwOthW K) u.mem t.mem := by
  have hn := F.scr.nowrap
  obtain ⟨tx, ty, tz, -, -⟩ := hL.TS_eq
  obtain U₅' : Unch base (jwOthW K) u.mem t.mem := (ProgKeep.unch k₅).mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (rcbW_other K x hx))
    · exact List.mem_append_right _ hw
  obtain U₅ : Unch base (jwLoopW K) u.mem t.mem := U₅'.mono (jwOthW_loopW K)
  obtain F₅ := F.next hL (k₅.scr F.scr) k₅.regs U₅ (jwLoopW_sub K)
  obtain Rv : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base t x = E₅ x ∧
      wordsVal t.mem base x K.M.n < C.p := fun x hx => by
    obtain hm : x ∈ [K.R.x, K.R.y, K.R.z] ++ V := List.mem_append_left _ hx
    exact ⟨I₅.val x hm, I₅.lt x hm⟩
  obtain ⟨Q', hQ', hQe', hR⟩ := jstepO_pt hC hM3 hO hP hP0 hn2 hn64 hnb (k := k) (i := i) (J := K.J) hi hQ hQe hRep
    (Z2 := tmv C K.M.n base u K.E.z) (X2 := tmv C K.M.n base u K.E.x) (Y2 := tmv C K.M.n base u K.E.y)
    (by have J := hE.jac; rw [tx, ty, tz] at J; exact J) (by have J := hE.z; rw [tz] at J; exact J)
  obtain vx := congrArg Prod.fst v₅
  obtain vy := congrArg (fun p => p.2.1) v₅
  obtain vz := congrArg (fun p => p.2.2) v₅
  dsimp only at vx vy vz
  refine ⟨⟨Q', hQ', hQe', F₅, hT.loopW hL U₅ hn (by decide), fun x hx => (Rv x hx).2, ?_⟩, U₅'⟩
  rw [(Rv _ (by simp)).1, (Rv _ (by simp)).1, (Rv _ (by simp)).1, vx, vy, vz]
  exact hR

theorem chunkO_zero (K : JacWinCfg) : K.chunkO 0 = 0 := by
  rw [JacWinCfg.chunkO, Nat.mul_zero, Nat.zero_div]

theorem chunkO_last (K : JacWinCfg) (h : 0 < K.nAddO) : K.chunkO K.nAddO = 16 := by
  rw [JacWinCfg.chunkO, Nat.mul_div_cancel _ h]

/-- `ZF` for `m = 1`, with `rbx = m`. -/
theorem cmpRbx1_ok (s : State) {m : Nat} (hm : m < 2 ^ 63) (hb : s.gpr .rbx = BitVec.ofNat 64 m) :
    WP isa (.block [.alu .cmp .rbx (.imm 1)]) s fun t => t.zf = some (decide (m = 1)) ∧ Keeps [] s t := by
  obtain e : (BitVec.ofNat 64 m - BitVec.signExtend 64 (1 : BitVec 32) == 0) = decide (m = 1) := by
    obtain hse : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide
    rw [hse]
    by_cases h : m = 1
    · subst h; decide
    · rw [decide_eq_false h, beq_eq_false_iff_ne]
      intro e
      exact h (by bv_omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', hb, RegUpd.zf_arithFlags, e]
  refine ⟨trivial, fun r _ => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_arithFlags]

/-- Before digit `rbx = j`'s addition: digit `j - 1`'s entry `a` set up for
its selection, from `s`'s table. -/
theorem prepO_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixedO K C base s₀ P k) {s : State} {j : Nat} (hj1 : 1 ≤ j) (hjJ : j < K.J)
    (hf : JFrame K C base size s₀ s) (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block K.prepO) s fun t =>
      SelP K base s.mem (magO (Window5.nib (OddWin.oq K.J k) (j - 1))) 0 t ∧ Keeps [.rax, .rcx, .rdx, .r8] s t := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hJ := hL.J
  have hbl := hL.bits
  obtain hbits := hf.bitsO hL hF
  rw [JacWinCfg.prepO, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (decRbx_ok s hj1 (by omega_arith) hb) fun s₁ ⟨b₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (digitO_ok K hs₁ (k := OddWin.oq K.J k) (j := j - 1) (N := 5 * K.J) (by omega_arith) (by omega_arith) b₁
    (fun t ht => by rw [k₁.2.1]; exact hbits t ht)) fun s₂ ⟨_, r₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (incRbxJ_ok s₂ (j := j - 1) (by rw [k₂.1 _ (by decide), b₁])) fun s₃ ⟨b₃, k₃, _, _⟩ => ?_
  obtain ha := magO_pos (Window5.nib_lt (OddWin.oq K.J k) (j - 1))
  refine WP.mono (selSetP_ok hL hn4 s₃ (base := base) s.mem ha.2 (by rw [k₃.1 _ (by decide), r₂]))
    fun t ⟨S, k₄⟩ => ⟨⟨ha.2, S, ?_, ?_, ?_⟩, ?_⟩
  · intro b _; rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  · have hg := hL.grid_le
    have := st16 K
    rw [k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
    exact ⟨_, List.mem_append_right _ hs.wr, hs.contains (d := K.tbl) (by omega_arith) (by omega_arith)⟩
  · rw [k₄.1 _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide), k₁.1 _ (by decide)]; exact hs.rdi
  · refine ⟨fun r hr => ?_, by rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1], by rw [k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1],
      by rw [k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₄.1 r (by simp [hr.2.1])]
    by_cases hrb : r = .rbx
    · subst hrb; rw [b₃, hb, show j - 1 + 1 = j by omega_arith]
    · rw [k₃.1 r (by simp [hrb]), k₂.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]), k₁.1 r (by simp [hrb])]

theorem nAddO_pos (K : JacWinCfg) : 0 < K.nAddO := by
  rw [JacWinCfg.nAddO, JacWinCfg.addOpsO, CachedJac.ip_eq, List.length_map]; decide

/-- `R`'s state survives writes that miss `R` and keep the frame. -/
theorem RStO.unchW (hL : JacWinLay K size) {base : Addr} {P Q : Point C} {s₀ s t : State}
    (h : RStO K C base size P s₀ Q s) (F : JFrame K C base size s₀ t) {W : List (Nat × Nat)}
    (hU : Unch base W s.mem t.mem) (hW : ∀ w ∈ W, w ∈ jwLoopW K)
    (hR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ w ∈ W, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x) :
    RStO K C base size P s₀ Q t := by
  have hn := h.fr.scr.nowrap
  obtain e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal t.mem base x K.M.n = wordsVal s.mem base x K.M.n :=
    fun x hx => hU.wordsVal (hR x hx) (by
      obtain hxo : x ∈ jwOther K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
      have := hL.le (other_mem hxo); omega_arith)
  obtain tv : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base t x = tmv C K.M.n base s x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [e x hx]
  refine ⟨F, h.tbl.loopW hL (hU.mono hW) hn (by decide), fun x hx => by rw [e x hx]; exact h.lt x hx, ?_⟩
  rw [tv _ (by simp), tv _ (by simp), tv _ (by simp)]; exact h.rep

/-- `R`'s slots miss `T`'s. -/
theorem R_T_apart (hL : JacWinLay K size) :
    ∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ w ∈ (List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)),
      x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro x hx w hw
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
  obtain hxo : x ∈ jwOther K := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
  exact hL.jg_apart (List.mem_append_right _ hxo) (by have := List.mem_range.mp hc; omega_arith)

/-- `R`'s slots miss what the negation writes. -/
theorem R_neg_apart (hL : JacWinLay K size) :
    ∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ w ∈ [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (jg K 81, 8 * K.M.n)],
      x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro x hx w hw
  obtain hxo : x ∈ jwOther K := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> jw_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hL.ap_oth (i := 0) (j := 6) (by decide) (by decide) (by decide)
    · exact hL.ap_oth (i := 1) (j := 6) (by decide) (by decide) (by decide)
    · exact hL.ap_oth (i := 2) (j := 6) (by decide) (by decide) (by decide)
  · exact hL.lay.tmp x (other_mem hxo)
  · exact hL.jg_apart (List.mem_append_right _ hxo) (by decide)

theorem neg_loopW (K : JacWinCfg) :
    ∀ w ∈ [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (jg K 81, 8 * K.M.n)], w ∈ jwLoopW K := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact other_loopW (by jw_mem)
  · exact tmp_loopW
  · exact T_loopW K (show 1 < 5 by decide)

/-- An iteration, `2 ≤ j < J`: `R = 32 R + [d_{j-1}]P`, with digit `j - 2`'s
entry selected meanwhile into `T`. -/
theorem jstepOP_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33)
    (hnb : 128 ≤ C.n) {base : Addr} {s₀ : State} {k : Nat} (hF : JacWinFixedO K C base s₀ P k)
    (hsc : ∀ op ∈ K.addOpsO, (ForwardField.code K.M op).all scalarI = true ∧
      scalCode ((opCall? K.M op).getD (.block (ForwardField.code K.M op))) = true)
    {j : Nat} (hj2 : 2 ≤ j) (hjJ : j < K.J) {s : State} (hI : JInvOP K C base size P s₀ k j s) :
    WP isa (K.stepOP dbl).inline s fun s' => JInvOP K C base size P s₀ k (j - 1) s' ∧
      s'.zf = some (decide (j - 1 = 1)) := by
  obtain ⟨⟨⟨Q, hQ, hQe, R₀⟩, hb⟩, T₀⟩ := hI
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  obtain ⟨h10, h5, hst⟩ := np_four hL hn4
  rw [JacWinCfg.stepOP]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s (by omega_arith) (by omega_arith) hb) fun s₁ ⟨b₁, k₁⟩ => ?_)
  obtain R₁ := R₀.rbxKeeps hL k₁
  obtain T₁ : JPt C K.M.n base s₁ (TS K) (OddWin.oddPt C P K.J k (j - 1)) := T₀.congr fun c _ => by rw [k₁.2.1]
  rw [← mul_one_pt Q] at R₁
  refine WP.seq (WP.mono (dblsO_ok hL hC hD hQ (j := j - 1) (by omega_arith) b₁ R₁) fun s₂ ⟨R₂, b₂, U₂⟩ => ?_)
  obtain T₂ := T₁.othW hL U₂ hn
  -- Digit `j - 2`'s selection set up.
  refine WP.seq (WP.mono (prepO_ok hL hn4 hF (j := j - 1) (by omega_arith) (by omega_arith) R₂.fr b₂) fun s₃ ⟨S₃, k₃⟩ => ?_)
  obtain ha16 := magO_pos (Window5.nib_lt (OddWin.oq K.J k) (j - 1 - 1))
  generalize ha : magO (Window5.nib (OddWin.oq K.J k) (j - 1 - 1)) = a at S₃ ha16
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  obtain hs₃ := R₂.fr.scr.of_keeps k₃ (by decide)
  obtain F₃ := R₂.fr.next hL hs₃ ((Keeps.regs k₃).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₃]; exact Unch.refl _ _ _) (by simp)
  obtain tv₃ : ∀ x, tmv C K.M.n base s₃ x = tmv C K.M.n base s₂ x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [m₃]
  obtain T₃ : JPt C K.M.n base s₃ (TS K) (OddWin.oddPt C P K.J k (j - 1)) := T₂.congr fun c _ => by rw [m₃]
  obtain hT₃ : JTblOkO K C base P 16 s₃ := fun m h1 hm => (R₂.tbl m h1 hm).congr fun c _ => by rw [m₃]
  -- `R = R + T`, the selection woven in.
  obtain V₃ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n],
      x ∈ jwSlots K ∧ wordsVal s₃.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by jw_mem, by rw [m₃]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [m₃]; exact R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, by rw [m₃]; exact R₂.lt _ (by simp)⟩
    · exact ⟨mx, by rw [← tx]; exact T₃.lt 0 (by decide)⟩
    · exact ⟨my, by rw [← ty]; exact T₃.lt 1 (by decide)⟩
    · exact ⟨mz, by rw [← tz]; exact T₃.lt 2 (by decide)⟩
    · exact ⟨m2, by rw [← t2]; exact T₃.lt 3 (by decide)⟩
    · exact ⟨m3, by rw [← t3]; exact T₃.lt 4 (by decide)⟩
  obtain I₃ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] (tmv C K.M.n base s₃) s₃ :=
    ⟨hs₃, F₃.mod, fun x hx => (V₃ x hx).1, fun x hx => (V₃ x hx).2, fun _ _ => rfl⟩
  obtain h2 := T₃.z2; have h3 := T₃.z3
  rw [t2, tz] at h2; rw [t3, t2, tz] at h3
  obtain hS₀ : SelP K base s₂.mem a (K.chunkO 0) s₃ := by rw [chunkO_zero]; exact S₃
  refine WP.seq (WP.mono (caddOI_ok hL hp I₃ (fun x hx => hx) h2 h3
    (SI := fun i t => SelP K base s₂.mem a (K.chunkO i) t)
    (fun i t hi h => selChunkO_ok hL hn4 i hi h)
    (fun i o t t' ho h hk hx hy _ => SelP.stab hL (rcbW_other K o ho) hn h hk hx hy) hsc hS₀)
    fun s₅ ⟨k₅, ⟨E₅, I₅, v₅⟩, S₅⟩ => ?_)
  obtain ⟨⟨Q', hQ', hQe', R₅⟩, U₅⟩ := addO_post hL hC hM3 hO hP hP0 hn2 hn64 hnb (k := k) (i := j - 1) (by omega_arith)
    (hC.onCurve_mul hQ 32) (fun hk => by rw [hQe hk, Window5.mul_mul hC hP, show j - 1 + 1 = j by omega_arith]) F₃ hT₃
    (by rw [tv₃, tv₃, tv₃]; exact R₂.rep) T₃ k₅ I₅ v₅
  have hs₅ := R₅.fr.scr
  obtain hb₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₅.gpr _ (rbx_not_clob _), k₃.1 _ (by decide), b₂]
  obtain S₅' : SelS K base s₂.mem a 16 s₅ := by
    have := S₅.sel; rw [show K.addOpsO.length = K.nAddO from rfl, chunkO_last K (nAddO_pos K)] at this; exact this
  -- The entry stored to `T`.
  rw [JacWinCfg.finO, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeP_ok hL hn4 hs₅ S₅') fun s₆ ⟨a₆, O₆, g₆, r₆, w₆⟩ => ?_
  obtain e₆ := jselOut hL hn4 (mem := s₂.mem) (mem' := s₆.mem) ⟨ha16.1, ha16.2⟩ a₆
  obtain T₆ : JPt C K.M.n base s₆ (TS K) (mul (2 * a - 1) P) := (R₂.tbl a ha16.1 ha16.2).congr fun c hc => e₆ c hc
  obtain hs₆ : Scr s₆ base size := ⟨by rw [g₆]; exact hs₅.rdi, by rw [w₆]; exact hs₅.wr, hs₅.nowrap⟩
  obtain O₆' : Outside base (jg K 80) (40 * K.M.n) s₅.mem s₆.mem := by
    rw [← hL.T80, show 40 * K.M.n = 16 * K.np16 by rw [h10, hn4]]; exact O₆
  obtain U₆ := outside_grid5 (b := 80) O₆'
  obtain hU₆W : ∀ w ∈ (List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)), w ∈ jwLoopW K := by
    intro w hw; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  obtain F₆ := R₅.fr.next hL hs₆ ⟨fun r _ => by rw [g₆], r₆, w₆⟩ U₆ (fun w hw => jwLoopW_sub K w (hU₆W w hw))
  obtain R₆ := R₅.unchW hL F₆ U₆ hU₆W (R_T_apart hL)
  -- Its `Y` negated.
  rw [WP.block_append_iff]
  refine WP.mono (decRbx_ok s₆ (j := j - 1) (by omega_arith) (by omega_arith) (by rw [g₆, hb₅])) fun s₇ ⟨b₇, k₇⟩ => ?_
  obtain hs₇ := hs₆.of_keeps k₇ (by decide)
  have m₇ : s₇.mem = s₆.mem := k₇.2.1
  obtain F₇ := F₆.next hL hs₇ ((Keeps.regs k₇).mono (sub_powClob (by decide))) (W := [])
    (by rw [m₇]; exact Unch.refl _ _ _) (by simp)
  obtain R₇ := (R₆.rbxKeeps hL k₇)
  obtain T₇ : JPt C K.M.n base s₇ (TS K) (mul (2 * magO (Window5.nib (OddWin.oq K.J k) (j - 1 - 1)) - 1) P) := by
    rw [ha]; exact T₆.congr fun c _ => by rw [m₇]
  rw [WP.block_append_iff]
  refine WP.mono (jnegO_ok hL hF (j := j - 1 - 1) (by omega_arith) F₇ b₇ T₇) fun s₈ ⟨F₈, U₈, kk₈, P₈⟩ => ?_
  obtain R₈ := R₇.unchW hL F₈ U₈ (neg_loopW K) (R_neg_apart hL)
  obtain b₈ : s₈.gpr .rbx = BitVec.ofNat 64 (j - 1 - 1) := by rw [kk₈.gpr _ (rbx_not_clob _), b₇]
  rw [show ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 1)] : List Instr) =
    [.alu .add .rbx (.imm 1)] ++ [.alu .cmp .rbx (.imm 1)] from rfl, WP.block_append_iff]
  refine WP.mono (incRbxJ_ok s₈ b₈) fun s₉ ⟨b₉, k₉, _, _⟩ => ?_
  refine WP.mono (cmpRbx1_ok s₉ (m := j - 1) (by omega_arith) (by rw [b₉, show j - 1 - 1 + 1 = j - 1 by omega_arith]))
    fun s₁₀ ⟨z₁₀, k₁₀⟩ => ?_
  obtain R₁₀ := (R₈.rbxKeeps hL k₉).rbxKeeps hL (k₁₀.mono (by simp))
  refine ⟨⟨⟨⟨Q', hQ', hQe', R₁₀⟩, by rw [k₁₀.1 _ (by simp), b₉, show j - 1 - 1 + 1 = j - 1 by omega_arith]⟩, ?_⟩, z₁₀⟩
  exact P₈.congr fun c _ => by rw [k₁₀.2.1, k₉.2.1]

/-- `R`'s slots miss what the entry writes. -/
theorem R_ent_apart (hL : JacWinLay K size) :
    ∀ x ∈ [K.R.x, K.R.y, K.R.z], ∀ w ∈ (List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
      [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro x hx w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact R_T_apart hL x hx w hw
  · exact R_neg_apart hL x hx w (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h))

/-- `rbx = J - 1`, `R = P`, and digit `J - 2`'s entry in `T`. -/
theorem jfirstOP_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} (hP : onCurve C P = true)
    {s₀ s : State} {k : Nat} (hF : JacWinFixedO K C base s₀ P k) (hJ2 : 2 ≤ K.J)
    (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) (hf : JFrame K C base size s₀ s) (hT : JTblOkO K C base P 16 s) :
    WP isa (.block K.firstOP) s fun t => JInvOP K C base size P s₀ k (K.J - 1) t := by
  have hn := hf.scr.nowrap
  have hJ := hL.J
  rw [show K.firstOP = K.firstO ++ ([.alu .sub .rbx (.imm 1)] ++ ((K.digitO ++ K.select) ++
      (K.tc.negY ++ [.alu .add .rbx (.imm 1)]))) by simp only [JacWinCfg.firstOP, List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (jfirstO_ok hL hP hF (by omega_arith) hkJ hf hT) fun s₁ I₁ => ?_
  obtain ⟨⟨Q, hQ, hQe, R₁⟩, b₁⟩ := I₁
  rw [WP.block_append_iff]
  refine WP.mono (decRbx_ok s₁ (j := K.J - 1) (by omega_arith) (by omega_arith) b₁) fun s₂ ⟨b₂, k₂⟩ => ?_
  obtain R₂ := R₁.rbxKeeps hL k₂
  rw [WP.block_append_iff]
  refine WP.mono (jentryO_ok hL hF (j := K.J - 1 - 1) (by omega_arith) R₂.fr R₂.tbl b₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono h₃ fun s₄ E₄ => ?_
  obtain R₄ := R₂.unchW hL E₄.fr E₄.unch (jent_loopW K) (R_ent_apart hL)
  refine WP.mono (incRbxJ_ok s₄ (j := K.J - 1 - 1) (by rw [E₄.keep.gpr _ (rbx_not_clob _), b₂]))
    fun t ⟨b₅, k₅, _, _⟩ => ⟨⟨⟨Q, hQ, hQe, R₄.rbxKeeps hL k₅⟩, by rw [b₅, show K.J - 1 - 1 + 1 = K.J - 1 by omega_arith]⟩,
      E₄.ent.congr fun c _ => by rw [k₅.2.1]⟩

/-- The last iteration, `rbx = 1`: `R = 32 R + [d_0]P`. -/
theorem jlastO_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl) {P : Point C}
    (hP : onCurve C P = true) (hP0 : P ≠ .infinity) (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33)
    (hnb : 128 ≤ C.n) {base : Addr} {s₀ : State} {k : Nat} {s : State}
    (hI : JInvOP K C base size P s₀ k 1 s) :
    WP isa (K.lastO dbl).inline s fun s' => JInvO K C base size P s₀ k 0 s' := by
  obtain ⟨⟨⟨Q, hQ, hQe, R₀⟩, hb⟩, T₀⟩ := hI
  have hn := R₀.fr.scr.nowrap
  have hJ := hL.J
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  rw [JacWinCfg.lastO]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s (j := 1) (by omega_arith) (by omega_arith) hb) fun s₁ ⟨b₁, k₁⟩ => ?_)
  obtain R₁ := R₀.rbxKeeps hL k₁
  obtain T₁ : JPt C K.M.n base s₁ (TS K) (OddWin.oddPt C P K.J k (1 - 1)) := T₀.congr fun c _ => by rw [k₁.2.1]
  rw [← mul_one_pt Q] at R₁
  refine WP.seq (WP.mono (dblsO_ok hL hC hD hQ (j := 1 - 1) (by omega_arith) b₁ R₁) fun s₂ ⟨R₂, b₂, U₂⟩ => ?_)
  obtain T₂ := T₁.othW hL U₂ hn
  obtain V₂ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2, K.z2 + 8 * K.M.n],
      x ∈ jwSlots K ∧ wordsVal s₂.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by jw_mem, R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, R₂.lt _ (by simp)⟩
    · exact ⟨by jw_mem, R₂.lt _ (by simp)⟩
    · exact ⟨mx, by rw [← tx]; exact T₂.lt 0 (by decide)⟩
    · exact ⟨my, by rw [← ty]; exact T₂.lt 1 (by decide)⟩
    · exact ⟨mz, by rw [← tz]; exact T₂.lt 2 (by decide)⟩
    · exact ⟨m2, by rw [← t2]; exact T₂.lt 3 (by decide)⟩
    · exact ⟨m3, by rw [← t3]; exact T₂.lt 4 (by decide)⟩
  obtain I₂ : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.z2,
      K.z2 + 8 * K.M.n] (tmv C K.M.n base s₂) s₂ :=
    ⟨R₂.fr.scr, R₂.fr.mod, fun x hx => (V₂ x hx).1, fun x hx => (V₂ x hx).2, fun _ _ => rfl⟩
  obtain h2 := T₂.z2; have h3 := T₂.z3
  rw [t2, tz] at h2; rw [t3, t2, tz] at h3
  refine WP.mono (caddO_ok hL hp I₂ (fun x hx => hx) h2 h3) fun s₅ ⟨k₅, E₅, I₅, v₅⟩ => ?_
  obtain ⟨⟨Q', hQ', hQe', R₅⟩, -⟩ := addO_post hL hC hM3 hO hP hP0 hn2 hn64 hnb (k := k) (i := 0) (by omega_arith)
    (hC.onCurve_mul hQ 32) (fun hk => by rw [hQe hk, Window5.mul_mul hC hP]) R₂.fr R₂.tbl R₂.rep T₂ k₅ I₅ v₅
  exact ⟨⟨Q', hQ', hQe', R₅⟩, by rw [k₅.gpr _ (rbx_not_clob _), b₂]⟩

/-- `winJacO_ok` for `windowOP`, the selections woven into the additions:
`[k]P` into `R`, in projective coordinates, if `k` is odd and below `n`. -/
theorem winJacOP_ok (hL : JacWinLay K size) (hn4 : K.M.n = 4) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33) (hnb : 128 ≤ C.n) (hJ3 : 3 ≤ K.J)
    (hsc : ∀ op ∈ K.addOpsO, (ForwardField.code K.M op).all scalarI = true ∧
      scalCode ((opCall? K.M op).getD (.block (ForwardField.code K.M op))) = true)
    {P : Point C} (hP : onCurve C P = true)
    {k : Nat} (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base) (hF : JacWinFixedO K C base s P k) :
    WP isa (K.windowOP dbl).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k % 2 = 1 ∧ k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  obtain hP0 := hF.ne_infinity hC
  rw [JacWinCfg.windowOP]
  simp only [Code.inline]
  refine WP.seq (WP.mono (jbuildO_ok hL hp hC hM3 hO hP hP0 (by omega_arith) hs hM hF.toJacWinPt)
    fun s₁ ⟨F₁, T₁⟩ => ?_)
  refine WP.seq (WP.mono (jfirstOP_ok hL hP hF (by omega_arith) hkJ F₁ T₁) fun s₂ I₂ => ?_)
  refine WP.seq (WP.mono (countLoop_ok (Q := fun t => JInvOP K C base size P s k 1 t)
    (Inv := fun i t => JInvOP K C base size P s k (i + 1) t) (n := K.J - 2)
    (fun i t h1 h2 hi => (jstepOP_ok hL hn4 hp hC hM3 hO hD hP hP0 hn2 hn64 hnb hF hsc (j := i + 1) (by omega_arith)
      (by omega_arith) hi).mono fun t' ⟨I', z'⟩ => ⟨by rw [show i - 1 + 1 = i + 1 - 1 by omega_arith]; exact I', by
        rw [z']; congr 1; exact decide_eq_decide.mpr (by omega_arith)⟩)
    (fun _ h => h) (by omega_arith) (by rw [show K.J - 2 + 1 = K.J - 1 by omega_arith]; exact I₂)) fun s₃ I₃ => ?_)
  refine WP.seq (WP.mono (jlastO_ok hL hp hC hM3 hO hD hP hP0 hn2 hn64 hnb I₃) fun s₄ I₄ => ?_)
  exact jfinO_ok hL hp hC hpn hone_lt hone hF I₄

/-- `windowOW`, woven or not: `winJacO_ok`'s postcondition. -/
theorem winJacOW_ok (hL : JacWinLay K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C)
    (hM3 : AM3 C) (hO : PrimeOrder C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p) (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1)
    (hn2 : C.n % 2 = 1) (hn64 : C.n % 64 < 33) (hnb : 128 ≤ C.n) {P : Point C} (hP : onCurve C P = true)
    {k : Nat} (hkJ : k ≤ 2 * 32 ^ (K.J - 1)) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base) (hF : JacWinFixedO K C base s P k) :
    WP isa (K.windowOW dbl).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (jwW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      (k % 2 = 1 ∧ k < C.n → Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y)
        (tmv C K.M.n base s' K.R.z) (mul k P)) := by
  unfold JacWinCfg.windowOW
  split
  · next hw =>
    simp only [JacWinCfg.weaveOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hw
    obtain ⟨⟨hn4, hJ3⟩, hsc⟩ := hw
    exact winJacOP_ok hL hn4 hp hC hM3 hO hD hpn hone_lt hone hn2 hn64 hnb hJ3
      (fun op hop => ⟨List.all_eq_true.mpr (hsc op hop).1, (hsc op hop).2⟩) hP hkJ hs hM hF
  · exact winJacO_ok hL hp hC hM3 hO hD hpn hone_lt hone hn2 hn64 hnb hP hkJ hs hM hF

end VG.Proof.Weierstrass.X86_64
