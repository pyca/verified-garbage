module

public import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaint
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueKeep
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The residue analysis is sound (x86-64)

`rtaint`, the analysis of `ResidueTaint.lean` as a `VG.Taint`: each transfer
function is sound (`step_sound`, `call_sound`, `ret_sound`, `push_sound`,
`pop_sound`, and the order and joins). `Taint.check_sound` then gives, for
two runs of code from states the starting taint describes, states that the
final taint describes: equal outside the writable regions but within the
window's bytes that `sec` lists.
-/

@[expose] public section

namespace VG.X86_64.RTaint

open VG.X86_64 VG.X86_64.Taint
open VG.X86_64.Residue (Pres Pres.none' Pres.some' Pres.map' Pres.bind')

/-! ## What instructions change -/

macro "uk_leaf" : tactic => `(tactic| first
  | exact Pres.none'
  | (apply Pres.some'; rfl)
  | (apply Pres.map'; intro _; rfl)
  | (apply Pres.map'; intro _; split <;> rfl))

syntax "uk_go" : tactic
macro_rules
  | `(tactic| uk_go) => `(tactic| first
    | uk_leaf
    | (apply Pres.bind'; intro _; uk_go)
    | (split <;> uk_go))

theorem exec_unknowns_pres (i : Instr) (s : State) :
    Pres (fun x => x.unknowns = s.unknowns) (exec i s) := by
  cases i
  case vop op => simp only [reduceExec]; rw [Taint.VOp.exec_eq]; exact Pres.some' rfl
  case zop op => simp only [reduceExec]; rw [Taint.ZOp.exec_eq]; exact Pres.some' rfl
  case xop op => simp only [reduceExec]; rw [Taint.XOp.exec_eq]; exact Pres.some' rfl
  case eop op => simp only [reduceExec]; rw [Taint.EOp.exec_eq]; exact Pres.some' rfl
  case vmovdquLoad len _ _ | vmovdquStore len _ _ | vbinLoad _ len _ _ _ =>
    cases len <;> simp only [reduceExec, State.store128, State.store256] <;> uk_go
  case evLoad d _ | evMadd52Load _ d _ _ =>
    simp only [reduceExec]; apply Pres.map'; intro _; rw [Taint.setVy_eq]
  all_goals simp only [reduceExec, execAlu, execAluW, execAlu32, execShift32, execShift, execRorx32,
      execRorx, execShld, execBtr, execMulx, execAdcx, execAdox, execCmov, State.store64,
      State.store32, State.store8, State.store16, State.store128, State.store256, State.store512,
      State.storeMasked512, State.storeMasked512B]
  all_goals uk_go

theorem exec_unknowns {i : Instr} {s s' : State} (h : exec i s = some s') : s'.unknowns = s.unknowns :=
  exec_unknowns_pres i s s' h

theorem exec_frame {i : Instr} {s s' : State} (h : exec i s = some s') :
    s'.wr = s.wr ∧ Frame s.wr s.mem s'.mem := by
  have e : execBlock isa [i] s = some (s', (addrs i s).map Leak.addr) := by
    simp only [execBlock, isa, h, Option.map_some, List.append_nil]
  obtain ⟨-, hw, hf⟩ := execBlock_regions e
  exact ⟨hw, hf⟩



theorem exec_mem_pres (i : Instr) (s : State) (h : writesMem i = false) :
    Pres (fun x => x.mem = s.mem) (exec i s) := by
  cases i <;> simp only [writesMem, storeW, Option.isSome_some, Option.isSome_none, Bool.true_or,
    Bool.false_or, reduceCtorEq] at h
  case vop op => simp only [reduceExec]; rw [Taint.VOp.exec_eq]; exact Pres.some' rfl
  case zop op => simp only [reduceExec]; rw [Taint.ZOp.exec_eq]; exact Pres.some' rfl
  case xop op => simp only [reduceExec]; rw [Taint.XOp.exec_eq]; exact Pres.some' rfl
  case eop op => simp only [reduceExec]; rw [Taint.EOp.exec_eq]; exact Pres.some' rfl
  case vmovdquLoad len _ _ | vbinLoad _ len _ _ _ => cases len <;> simp only [reduceExec] <;> uk_go
  case vmovdquStore len _ _ => cases len <;> simp at h
  case evLoad d _ | evMadd52Load _ d _ _ =>
    simp only [reduceExec]; apply Pres.map'; intro _; rw [Taint.setVy_eq]
  all_goals simp only [reduceExec, execAlu, execAluW, execAlu32, execShift32, execShift, execRorx32,
      execRorx, execShld, execBtr, execMulx, execAdcx, execAdox, execCmov]
  all_goals uk_go

theorem exec_mem {i : Instr} {s s' : State} (h : writesMem i = false) (e : exec i s = some s') :
    s'.mem = s.mem :=
  exec_mem_pres i s h s' e

theorem writeW_out {m : Mem} {a y : Addr} {w : Nat} {v : BitVec w} (h : ¬ (y - a).toNat < w / 8) :
    m.writeW a v y = m y :=
  Mem.write_apply h

/-- A store changes memory only within the `w` bytes at its address. -/
theorem exec_store {i : Instr} {m : MemOp} {w : Nat} (hi : storeW i = some (m, w)) {s s' : State}
    (e : exec i s = some s') : ∀ y, ¬ (y - s.ea m).toNat < w → s'.mem y = s.mem y := by
  intro y hy
  cases i <;> simp only [storeW, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hi
  all_goals first
    | (obtain ⟨rfl, rfl⟩ := hi
       simp only [reduceExec, State.store64, State.store32, State.store8, State.store16, State.store128,
         State.store256, State.store512] at e
       split at e <;> [skip; cases e]
       cases e
       exact writeW_out (by omega))
    | skip
  case vmovdquStore len _ _ =>
    cases len <;> simp only [Option.some.injEq, Prod.mk.injEq] at hi <;> obtain ⟨rfl, rfl⟩ := hi <;>
      simp only [reduceExec, State.store128, State.store256] at e <;> split at e <;> cases e <;>
      exact writeW_out (by omega)

/-- A byte at offset `k` of region `j` is not among the `n` bytes at offset `d`
of region `i`, if they are other regions or other offsets. -/
theorem byte_not_in {τ : Taint.T} {s : State} (hw : Wf τ s) {i d n j k : Nat} (hn : 0 < n)
    (hd : d + n ≤ τ.lens.getD i 0) (hk : k < τ.lens.getD j 0) (hsep : j ≠ i ∨ k < d ∨ d + n ≤ k) :
    ¬ (byteAddr s j k - byteAddr s i d).toNat < n := by
  intro hlt
  have hne := lens_ne (n := d + n) (by omega) hd
  obtain ⟨-, hdisj, hbound⟩ := hw.1 hne
  obtain ⟨hi, hri⟩ := region_mem hw hne (i := i) (by omega)
  obtain ⟨hj, hrj⟩ := region_mem hw hne (i := j) (by omega)
  have hli := region_len hw hne i
  have hlj := region_len hw hne j
  have hbi : (region s i).len ≤ 2 ^ 64 := by rw [hri]; exact hbound _ (List.getElem_mem _)
  have hbj : (region s j).len ≤ 2 ^ 64 := by rw [hrj]; exact hbound _ (List.getElem_mem _)
  by_cases hji : j = i
  · -- The same region, at other offsets.
    subst hji
    have hsep := hsep.resolve_left (· rfl)
    have h : byteAddr s j k - byteAddr s j d = BitVec.ofNat 64 k - BitVec.ofNat 64 d :=
      Offset.add_sub_add_left _ _ _
    exact Offset.not_lt_sub_ofNat hsep (by omega) hn (by omega) (h ▸ hlt)
  · -- Another region: the regions are disjoint.
    have hA : (region s i).Contains (byteAddr s i d) n := by
      simp only [Region.Contains, byteAddr]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hX : (region s j).Contains (byteAddr s j k) 1 := by
      simp only [Region.Contains, byteAddr]
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hXi := hA.byte hlt
    rw [List.pairwise_iff_getElem] at hdisj
    rcases Nat.lt_or_gt_of_ne hji with h | h
    · exact hdisj j i hj hi h _ (hrj ▸ hX) (hri ▸ hXi)
    · exact hdisj i j hi hj h _ (hri ▸ hXi) (hrj ▸ hX)


/-! ## Stores within a known range of a region -/

theorem idxSlots_ok {t : Taint.T} (hok : SlotsOk t) (ri lo hi : Nat) (p : Bool) :
    SlotsOk (idxStore t ri lo hi p) := by
  intro sl hsl
  simp only [idxStore] at hsl
  split at hsl
  · exact hok sl hsl
  · exact hok sl (List.mem_filter.mp hsl).1

/-- A store of `n` bytes at offset `d` of region `ri`, within `[lo, hi)`, of
the same value in both runs if `p`. -/
theorem Agree.storeAt {t : Taint.T} {s₁ s₂ : State} (ha : Taint.Agree t s₁ s₂) {ri lo hi d n : Nat}
    (hn : 0 < n) (hlo : lo ≤ d) (hhi : d + n ≤ hi) (hfit : hi ≤ t.lens.getD ri 0)
    {V₁ V₂ : BitVec (8 * n)} {p : Bool} (hv : p = true → V₁ = V₂) :
    Taint.Agree (idxStore t ri lo hi p)
      { s₁ with mem := s₁.mem.write (byteAddr s₁ ri d) n V₁ }
      { s₂ with mem := s₂.mem.write (byteAddr s₂ ri d) n V₂ } where
  rf := ha.rf
  wr := ha.wr
  wf₁ := ha.wf₁
  wf₂ := ha.wf₂
  ok := idxSlots_ok ha.ok ri lo hi p
  lo := ha.lo
  xr := ha.xr
  slots := by
    intro sl hsl k hk₁ hk₂
    simp only [byteAddr_withMem]
    have hne : t.lens ≠ [] := lens_ne (i := ri) (n := d + n) (by omega) (Nat.le_trans hhi hfit)
    have hA : byteAddr s₁ ri d = byteAddr s₂ ri d := by simp only [byteAddr, region, ha.wr hne]
    simp only [idxStore] at hsl
    split at hsl
    · rename_i hp
      rw [hA, hv hp, ha.byteAddr_eq hsl hk₂]
      exact write_same _ (ha.byteAddr_eq hsl hk₂ ▸ ha.slots sl hsl k hk₁ hk₂)
    · rw [List.mem_filter] at hsl
      obtain ⟨h, hsep⟩ := hsl
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hsep
      have hsep : sl.1 ≠ ri ∨ k < d ∨ d + n ≤ k := by
        rcases hsep with (h' | h') | h'
        · exact .inl h'
        · exact .inr (.inr (by omega))
        · exact .inr (.inl (by omega))
      have hk : sl.2.1 + sl.2.2 ≤ t.lens.getD sl.1 0 := ha.ok sl h
      have hd' : d + n ≤ t.lens.getD ri 0 := Nat.le_trans hhi hfit
      have hk' : k < t.lens.getD sl.1 0 := Nat.lt_of_lt_of_le hk₂ hk
      rw [write_other ha.wf₁ hn hd' hk' hsep, write_other ha.wf₂ hn hd' hk' hsep]
      exact ha.slots sl h k hk₁ hk₂

/-! ## The stores `special` handles -/

theorem exec_store_eq {m : MemOp} {r : Reg} {s s' : State} (h : exec (.store m r) s = some s') :
    s' = { s with mem := s.mem.write (s.ea m) 8 ((s.gpr r).setWidth 64) } := by
  simp only [reduceExec, State.store64] at h; split at h <;> cases h; rfl

theorem exec_store8_eq {m : MemOp} {r : Reg} {s s' : State} (h : exec (.store8 m r) s = some s') :
    s' = { s with mem := s.mem.write (s.ea m) 1 (((s.gpr r).setWidth 8).setWidth 8) } := by
  simp only [reduceExec, State.store8] at h; split at h <;> cases h; rfl

theorem exec_movdquStore_eq {m : MemOp} {x : XReg} {s s' : State} (h : exec (.movdquStore m x) s = some s') :
    s' = { s with mem := s.mem.write (s.ea m) 16 ((s.xmm x).setWidth 128) } := by
  simp only [reduceExec, State.store128] at h; split at h <;> cases h; rfl

theorem ubOf_some {l : List (Reg × Nat)} {r : Reg} {n : Nat} (h : ubOf l r = some n) : (r, n) ∈ l := by
  simp only [ubOf, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have := List.find?_some hp
  simp only [beq_iff_eq] at this
  rw [← this]; exact List.mem_of_find?_eq_some hp

theorem find_base {l : List (Reg × Nat × Nat)} {b : Reg} {q : Reg × Nat × Nat}
    (h : l.find? (·.1 == b) = some q) : q ∈ l ∧ q.1 = b := by
  have := List.find?_some h
  simp only [beq_iff_eq] at this
  exact ⟨List.mem_of_find?_eq_some h, this⟩

/-- Where a store `idxRange` bounds writes: at offset `lo` plus the index of region `ri`. -/
theorem idxRange_ea {τ : FT} {s : State} (hw : Wf τ.t s) (o : One τ s) {m : MemOp} {w ri lo hi : Nat}
    (h : idxRange τ m w = some (ri, lo, hi)) :
    ∃ x, m.index = some x ∧ s.ea m = byteAddr s ri (lo + (s.gpr x).toNat) ∧
      lo + (s.gpr x).toNat + w ≤ hi ∧ hi ≤ τ.t.lens.getD ri 0 := by
  unfold idxRange at h
  split at h <;> [rename_i x hx; cases h]
  split at h <;> [rename_i b ri' k B hb hB; cases h]
  split at h <;> [rename_i hc; cases h]
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨hbm, hbe⟩ := find_base hb
  simp only at hbe
  subst hbe
  have hxB := o.ub _ (ubOf_some hB)
  obtain ⟨hs, hd, hfit⟩ := hc
  refine ⟨x, hx, ?_, by simp only at hxB; omega, by omega⟩
  have hbase := hw.2 _ hbm
  simp only [State.ea, hx, hs, hbase, byteAddr]
  rw [show m.disp = ((m.disp.toNat : Nat) : Int) from (Int.toNat_of_nonneg hd).symm, BitVec.ofInt_natCast]
  rw [show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, BitVec.ofNat_add, BitVec.ofNat_add,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  ac_rfl

theorem memPub_idx {t : Taint.T} {m : MemOp} {x : Reg} (h : memPub t m = true) (hx : m.index = some x) :
    pub t x = true := by
  simp only [memPub, hx, Bool.and_eq_true] at h; exact h.2

/-- An indexed store whose range `idxRange` bounds. -/
theorem idx_sound {τ : FT} {s₁ s₂ : State} (ha : Taint.Agree τ.t s₁ s₂) (o₁ : One τ s₁) (o₂ : One τ s₂)
    {m : MemOp} {w ri lo hi : Nat} (hr : idxRange τ m w = some (ri, lo, hi)) (hm : memPub τ.t m = true)
    (hw : 0 < w) {V₁ V₂ : BitVec (8 * w)} {p : Bool} (hv : p = true → V₁ = V₂) :
    Taint.Agree (idxStore τ.t ri lo hi p)
      { s₁ with mem := s₁.mem.write (s₁.ea m) w V₁ } { s₂ with mem := s₂.mem.write (s₂.ea m) w V₂ } := by
  obtain ⟨x, hx, ea₁, hle, hfit⟩ := idxRange_ea ha.wf₁ o₁ hr
  obtain ⟨x', hx', ea₂, -, -⟩ := idxRange_ea ha.wf₂ o₂ hr
  rw [hx] at hx'; cases hx'
  have hxe : s₁.gpr x = s₂.gpr x := ha.reg (memPub_idx hm hx)
  rw [ea₁, ea₂, ← hxe]
  exact Agree.storeAt ha hw (Nat.le_add_right _ _) hle hfit hv

theorem special_sound {τ : FT} {i : Instr} {t' : Taint.T} {s₁ s₂ s₁' s₂' : State}
    (ha : Taint.Agree τ.t s₁ s₂) (o₁ : One τ s₁) (o₂ : One τ s₂) (h : special τ i = some t')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Taint.Agree t' s₁' s₂' := by
  cases i
  case store m r =>
    rw [exec_store_eq e₁, exec_store_eq e₂]
    cases hx : m.index with
    | none => simp only [special, hx] at h; cases h
    | some x =>
      simp only [special, hx, storeW, storePub] at h
      cases hr : idxRange τ m 8 with
      | none => simp only [hr] at h; cases h
      | some q =>
        obtain ⟨ri, lo, hi⟩ := q
        simp only [hr] at h
        split at h <;> [rename_i hm; cases h]
        cases h
        exact ⟨by simp only [addrs, ha.ea hm], idx_sound ha o₁ o₂ hr hm (by decide) fun hp => by rw [ha.reg hp]⟩
  case store8 m r =>
    rw [exec_store8_eq e₁, exec_store8_eq e₂]
    cases hx : m.index with
    | none => simp only [special, hx] at h; cases h
    | some x =>
      simp only [special, hx, storeW, storePub] at h
      cases hr : idxRange τ m 1 with
      | none => simp only [hr] at h; cases h
      | some q =>
        obtain ⟨ri, lo, hi⟩ := q
        simp only [hr] at h
        split at h <;> [rename_i hm; cases h]
        cases h
        exact ⟨by simp only [addrs, ha.ea hm], idx_sound ha o₁ o₂ hr hm (by decide) fun hp => by rw [ha.reg hp]⟩
  case movdquStore m x =>
    rw [exec_movdquStore_eq e₁, exec_movdquStore_eq e₂]
    cases hx : m.index with
    | none =>
      simp only [special, hx] at h
      split at h <;> [rename_i hxp; cases h]
      simp only [storeStep] at h
      split at h <;> [rename_i hm; cases h]
      cases h
      exact ⟨by simp only [addrs, ha.ea hm], ha.store hm (by decide) fun _ => by rw [ha.xr x hxp]⟩
    | some y =>
      simp only [special, hx, storeW, storePub] at h
      cases hr : idxRange τ m 16 with
      | none => simp only [hr] at h; cases h
      | some q =>
        obtain ⟨ri, lo, hi⟩ := q
        simp only [hr] at h
        split at h <;> [rename_i hm; cases h]
        cases h
        exact ⟨by simp only [addrs, ha.ea hm], idx_sound ha o₁ o₂ hr hm (by decide) fun hp => by rw [ha.xr x hp]⟩
  all_goals simp only [special, reduceCtorEq] at h

/-! ## Zeroing idioms and pointers reloaded from slots -/

theorem _root_.VG.X86_64.Taint.Agree.addReg {t : Taint.T} {s₁ s₂ : State} (ha : Taint.Agree t s₁ s₂) {d : Reg}
    (h : s₁.gpr d = s₂.gpr d) : Taint.Agree { t with regs := t.regs.insert d } s₁ s₂ :=
  ⟨⟨fun r hr => by
      rcases RegSet.mem_insert.mp hr with rfl | hr
      · exact h
      · exact ha.rf.1 r hr, ha.rf.2⟩, ha.wr, ha.wf₁, ha.wf₂, ha.ok, ha.slots, ha.lo, ha.xr⟩

theorem _root_.VG.X86_64.Taint.Agree.addXreg {t : Taint.T} {s₁ s₂ : State} (ha : Taint.Agree t s₁ s₂) {x : XReg}
    (h : s₁.xmm x = s₂.xmm x) : Taint.Agree { t with xregs := t.xregs.insert x } s₁ s₂ :=
  ⟨ha.rf, ha.wr, ha.wf₁, ha.wf₂, ha.ok, ha.slots, ha.lo, fun r hr => by
      rcases RegSet.mem_insert.mp hr with rfl | hr
      · exact h
      · exact ha.xr r hr⟩

theorem _root_.VG.X86_64.Taint.Agree.addBase {t : Taint.T} {s₁ s₂ : State} (ha : Taint.Agree t s₁ s₂) {p : Reg × Nat × Nat}
    (h₁ : s₁.gpr p.1 = (region s₁ p.2.1).base + BitVec.ofNat 64 p.2.2)
    (h₂ : s₂.gpr p.1 = (region s₂ p.2.1).base + BitVec.ofNat 64 p.2.2) :
    Taint.Agree { t with bases := p :: t.bases } s₁ s₂ :=
  ⟨ha.rf, ha.wr,
    ⟨ha.wf₁.1, fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h₁
      · exact ha.wf₁.2 q hq⟩,
    ⟨ha.wf₂.1, fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact h₂
      · exact ha.wf₂.2 q hq⟩, ha.ok, ha.slots, ha.lo, ha.xr⟩

theorem exec_xor_self {d : Reg} {s s' : State} (h : exec (.alu .xor d (.reg d)) s = some s') :
    s'.gpr d = 0 := by
  simp only [reduceExec, execAlu, readSrc, Option.bind_some, Option.some.injEq] at h
  subst h
  simp only [State.setReg, ↓reduceIte, BitVec.xor_self]; rfl

theorem exec_xor32_self {d : Reg} {s s' : State} (h : exec (.alu32 .xor d (.reg d)) s = some s') :
    s'.gpr d = 0 := by
  simp only [reduceExec, execAlu32, readSrc32, Option.bind_some, Option.some.injEq] at h
  subst h
  simp only [State.setReg32, State.setReg, ↓reduceIte, BitVec.xor_self, BitVec.setWidth_zero]; rfl

theorem exec_pxor_self {x : XReg} {s s' : State} (h : exec (.xop (.bin .pxor x x)) s = some s') :
    s'.xmm x = 0 := by
  simp only [reduceExec, Option.some.injEq] at h
  subst h
  simp only [XOp.exec, State.setXmm, ↓reduceIte, XBinOp.eval, BitVec.xor_self]; rfl

theorem exec_mov_mem {d : Reg} {m : MemOp} {s s' : State} (h : exec (.mov d (.mem m)) s = some s') :
    s'.gpr d = s.mem.readW (s.ea m) 64 ∧ s'.wr = s.wr := by
  simp only [reduceExec, readSrc, State.load64, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  split at hv <;> cases hv
  simp only [State.setReg, ↓reduceIte, and_self]

theorem find_mb {l : List (Nat × Nat × Nat × Nat)} {ri o : Nat} {q : Nat × Nat × Nat × Nat}
    (h : l.find? (fun e => e.1 == ri && e.2.1 == o) = some q) : q ∈ l ∧ q.1 = ri ∧ q.2.1 = o := by
  have := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨List.mem_of_find?_eq_some h, this⟩

/-- The pointer a load from a slot of `mb` reads. -/
theorem mb_load {τ : FT} {s s' : State} (hw : Wf τ.t s) (o : One τ s) {d : Reg} {m : MemOp}
    {ri off : Nat} {q : Nat × Nat × Nat × Nat} (hm : addrOf τ.t m = some (ri, off))
    (hf : τ.mb.find? (fun e => e.1 == ri && e.2.1 == off) = some q)
    (e : exec (.mov d (.mem m)) s = some s') :
    s'.gpr d = (region s' q.2.2.1).base + BitVec.ofNat 64 q.2.2.2 := by
  obtain ⟨hg, hwr⟩ := exec_mov_mem e
  obtain ⟨hq, h1, h2⟩ := find_mb hf
  have := o.mb _ hq
  rw [h1, h2] at this
  rw [hg, ea_of_addrOf hw hm, this]
  simp only [region, hwr]

theorem post_sound {τ : FT} {i : Instr} {t' : Taint.T} {s₁ s₂ s₁' s₂' : State}
    (hw₁ : Wf τ.t s₁) (hw₂ : Wf τ.t s₂) (o₁ : One τ s₁) (o₂ : One τ s₂)
    (ha : Taint.Agree t' s₁' s₂') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    Taint.Agree (post τ i t') s₁' s₂' := by
  unfold post
  split
  · rename_i d d'
    split
    · rename_i hd
      simp only [beq_iff_eq] at hd; subst hd
      exact ha.addReg (by rw [exec_xor_self e₁, exec_xor_self e₂])
    · exact ha
  · rename_i d d'
    split
    · rename_i hd
      simp only [beq_iff_eq] at hd; subst hd
      exact ha.addReg (by rw [exec_xor32_self e₁, exec_xor32_self e₂])
    · exact ha
  · rename_i x x'
    split
    · rename_i hx
      simp only [beq_iff_eq] at hx; subst hx
      exact ha.addXreg (by rw [exec_pxor_self e₁, exec_pxor_self e₂])
    · exact ha
  · rename_i d m
    split
    · rename_i ri off hm
      split
      · rename_i q hf
        exact ha.addBase (mb_load hw₁ o₁ hm hf e₁) (mb_load hw₂ o₂ hm hf e₂)
      · exact ha
    · exact ha
  · exact ha

theorem baseStep_sound {τ : FT} {i : Instr} {t' : Taint.T} {s₁ s₂ s₁' s₂' : State}
    (ha : Taint.Agree τ.t s₁ s₂) (o₁ : One τ s₁) (o₂ : One τ s₂) (h : baseStep τ i = some t')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Taint.Agree t' s₁' s₂' := by
  unfold baseStep at h
  split at h
  · rename_i t'' hs
    cases h
    exact special_sound ha o₁ o₂ hs e₁ e₂
  · obtain ⟨t'', ht, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨had, hb⟩ := X86_64.taint.step_sound ha ht e₁ e₂
    exact ⟨had, post_sound ha.wf₁ ha.wf₂ o₁ o₂ hb e₁ e₂⟩

/-! ## Bounds, flags and pointers in slots -/

theorem toNat_signExtend_of_msb {v : BitVec 32} (h : v.msb = false) : (v.signExtend 64).toNat = v.toNat := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false h, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le v.isLt (by decide))]

theorem ubNew_sound {τ : FT} {i : Instr} {p : Reg × Nat} {s s' : State} (o : One τ s)
    (h : ubNew τ i = some p) (e : exec i s = some s') : (s'.gpr p.1).toNat ≤ p.2 := by
  unfold ubNew at h
  split at h
  · rename_i d v
    split at h <;> [cases h; skip]
    rename_i hm
    cases h
    simp only [reduceExec, readSrc, Option.map_some, Option.some.injEq] at e
    subst e
    simp only [State.setReg, ↓reduceIte, toNat_signExtend_of_msb (Bool.of_not_eq_true hm), Nat.le_refl]
  · rename_i d v
    cases h
    simp only [reduceExec, readSrc32, Option.map_some, Option.some.injEq] at e
    subst e
    simp only [State.setReg32, State.setReg, ↓reduceIte, BitVec.toNat_setWidth]
    exact Nat.le_of_eq (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le v.isLt (by decide)))
  · rename_i d v
    split at h <;> [cases h; skip]
    rename_i hm
    cases h
    simp only [reduceExec, execAlu, readSrc, Option.bind_some, Option.some.injEq] at e
    subst e
    simp only [State.setReg, ↓reduceIte, BitVec.toNat_and]
    exact Nat.le_trans Nat.and_le_right (Nat.le_of_eq (toNat_signExtend_of_msb (Bool.of_not_eq_true hm)))
  · rename_i d v
    cases h
    simp only [reduceExec, execAlu32, readSrc32, Option.bind_some, Option.some.injEq] at e
    subst e
    simp only [State.setReg32, State.setReg, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_and]
    exact Nat.le_trans (Nat.mod_le _ _) Nat.and_le_right
  · rename_i d x
    split at h <;> [skip; cases h]
    rename_i hf
    simp only [beq_iff_eq] at hf
    obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.mp h
    have hd := o.ub _ (ubOf_some hB)
    have hcf := o.fl _ _ hf
    obtain ⟨v, c, hv, hc, rfl⟩ := execCmov_some (by simpa only [reduceExec] using e)
    simp only [readSrc, Option.some.injEq] at hv
    subst hv
    simp only [eval, hcf, Option.some.injEq] at hc
    subst hc
    simp only at hd ⊢
    rw [cmov_gpr]
    simp only [↓reduceIte]
    split
    · rename_i hlt; simp only [decide_eq_true_eq] at hlt; omega
    · exact hd
  · cases h

theorem ub_step {τ : FT} {i : Instr} {s s' : State} (o : One τ s) (e : exec i s = some s') :
    ∀ p ∈ (ubNew τ i).toList ++ ubKill τ.ub i, (s'.gpr p.1).toNat ≤ p.2 := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact ubNew_sound o (Option.mem_toList.mp hp) e
  · simp only [ubKill, List.mem_filter, Bool.not_eq_true'] at hp
    rw [exec_gpr hp.2 e]
    exact o.ub p hp.1

theorem fl_step {i : Instr} {s s' : State} (e : exec i s = some s') :
    ∀ a b, (match i with
      | .alu .cmp a (.reg b) => some (a, b)
      | _ => none) = some (a, b) → s'.cf = some (decide ((s'.gpr a).toNat < (s'.gpr b).toNat)) := by
  intro a b h
  split at h
  · rename_i a' b'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [reduceExec, execAlu, readSrc, Option.bind_some, Option.some.injEq] at e
    subst e
    simp only [arithFlags, State.setFlags]
    rfl
  · cases h

theorem storeW_pos {i : Instr} {m : MemOp} {w : Nat} (h : storeW i = some (m, w)) : 0 < w := by
  cases i <;> simp only [storeW, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
  all_goals first | (obtain ⟨-, rfl⟩ := h; decide) | skip
  rename_i len _ _
  cases len <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨-, rfl⟩ := h <;> decide

/-- Where a store `storeRange` bounds writes. -/
theorem storeRange_ea {τ : FT} {s : State} (hw : Wf τ.t s) (o : One τ s) {m : MemOp} {w ri lo hi : Nat}
    (h : storeRange τ m w = some (ri, lo, hi)) :
    ∃ d, s.ea m = byteAddr s ri d ∧ lo ≤ d ∧ d + w ≤ hi ∧ hi ≤ τ.t.lens.getD ri 0 := by
  unfold storeRange at h
  split at h
  · rename_i ri' d hm
    split at h <;> [rename_i hfit; cases h]
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨d, ea_of_addrOf hw hm, Nat.le_refl _, Nat.le_refl _, hfit⟩
  · obtain ⟨x, -, hea, hle, hfit⟩ := idxRange_ea hw o h
    exact ⟨lo + (s.gpr x).toNat, hea, Nat.le_add_right _ _, hle, hfit⟩

theorem mem_mbKill {mb : List (Nat × Nat × Nat × Nat)} {ri lo hi : Nat} {e : Nat × Nat × Nat × Nat}
    (h : e ∈ mbKill mb ri lo hi) : e ∈ mb ∧ (e.1 ≠ ri ∨ e.2.1 + 8 ≤ lo ∨ hi ≤ e.2.1) := by
  simp only [mbKill, List.mem_filter, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  exact ⟨h.1, by rcases h.2 with (h | h) | h <;> [exact .inl h; exact .inr (.inl h); exact .inr (.inr h)]⟩

theorem mbAfter_fit {τ : FT} {i : Instr} (hf : ∀ e ∈ τ.mb, e.2.1 + 8 ≤ τ.t.lens.getD e.1 0) :
    ∀ e ∈ mbAfter τ i, e.2.1 + 8 ≤ τ.t.lens.getD e.1 0 := by
  intro e he
  unfold mbAfter at he
  split at he
  · rename_i m w hsw
    split at he
    · rename_i ri lo hi hr
      have hk : ∀ e ∈ mbKill τ.mb ri lo hi, e.2.1 + 8 ≤ τ.t.lens.getD e.1 0 :=
        fun e he => hf e (mem_mbKill he).1
      split at he
      · rename_i m' r
        split at he
        · rename_i _ pj pk _ ri' d' hb hm
          rcases List.mem_cons.mp he with rfl | he
          · simp only [storeW, Option.some.injEq, Prod.mk.injEq] at hsw
            obtain ⟨rfl, rfl⟩ := hsw
            simp only [storeRange, hm] at hr
            split at hr <;> [rename_i hfit; cases hr]
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            exact hfit
          · exact hk e he
        · exact hk e he
      · exact hk e he
    · cases he
  · split at he
    · cases he
    · exact hf e he

/-- The 8 bytes of a slot of `mb` are outside what a store bounded by
`[lo, hi)` of region `ri` writes. -/
theorem mb_keep {τ : FT} {i : Instr} {m : MemOp} {w ri lo hi : Nat} {s s' : State}
    (hw : Wf τ.t s) (o : One τ s) (hsw : storeW i = some (m, w)) (hr : storeRange τ m w = some (ri, lo, hi))
    (e : exec i s = some s') {q : Nat × Nat × Nat × Nat} (hq : q.2.1 + 8 ≤ τ.t.lens.getD q.1 0)
    (hsep : q.1 ≠ ri ∨ q.2.1 + 8 ≤ lo ∨ hi ≤ q.2.1) :
    s'.mem.readW (byteAddr s q.1 q.2.1) 64 = s.mem.readW (byteAddr s q.1 q.2.1) 64 := by
  obtain ⟨d, hea, hlo, hhi, hfit⟩ := storeRange_ea hw o hr
  have hw0 := storeW_pos hsw
  apply Mem.readW_congr
  intro k hk
  simp only [Nat.reduceDiv] at hk
  rw [byteAddr_add]
  apply exec_store hsw e
  rw [hea]
  exact byte_not_in hw hw0 (by omega) (by omega) (by omega)

theorem mb_step {τ : FT} {i : Instr} {s s' : State} (hw : Wf τ.t s) (o : One τ s)
    (hf : ∀ e ∈ τ.mb, e.2.1 + 8 ≤ τ.t.lens.getD e.1 0) (e : exec i s = some s') :
    ∀ q ∈ mbAfter τ i, s'.mem.readW (byteAddr s' q.1 q.2.1) 64 =
      (region s' q.2.2.1).base + BitVec.ofNat 64 q.2.2.2 := by
  have hwr := (exec_frame e).1
  have hba : ∀ j k, byteAddr s' j k = byteAddr s j k := fun j k => by simp only [byteAddr, region, hwr]
  have hrg : ∀ j, region s' j = region s j := fun j => by simp only [region, hwr]
  intro q hq
  rw [hba, hrg]
  unfold mbAfter at hq
  split at hq
  · rename_i m w hsw
    split at hq
    · rename_i ri lo hi hr
      have hk : ∀ q ∈ mbKill τ.mb ri lo hi, s'.mem.readW (byteAddr s q.1 q.2.1) 64 =
          (region s q.2.2.1).base + BitVec.ofNat 64 q.2.2.2 := fun q hq => by
        obtain ⟨hq, hsep⟩ := mem_mbKill hq
        rw [mb_keep hw o hsw hr e (hf q hq) hsep]
        exact o.mb q hq
      split at hq
      · rename_i m' r
        split at hq
        · rename_i _ _ b pj pk d' hb hm
          rcases List.mem_cons.mp hq with rfl | hq
          · simp only [storeW, Option.some.injEq, Prod.mk.injEq] at hsw
            obtain ⟨rfl, rfl⟩ := hsw
            simp only [storeRange, hm] at hr
            split at hr <;> [skip; cases hr]
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            obtain ⟨hbm, hbe⟩ := find_base hb
            simp only at hbe
            subst hbe
            rw [exec_store_eq e]
            simp only
            rw [← ea_of_addrOf hw hm]
            rw [BitVec.setWidth_eq]
            exact (Mem.readW_writeW_self64 s.mem _ (s.gpr b)).trans (hw.2 _ hbm)
          · exact hk q hq
        · exact hk q hq
      · exact hk q hq
    · cases hq
  · split at hq
    · cases hq
    · rename_i hwm
      rw [exec_mem (Bool.of_not_eq_true hwm) e]
      exact o.mb q hq

/-! ## Soundness: instructions -/

theorem step_sound {τ τ' : FT} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  unfold step at hs
  split at hs <;> [rename_i hok; cases hs]
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨hok, hsp⟩ := hok
  split at hs <;> [rename_i t' ht; cases hs]
  split at hs <;> [rename_i hl; cases hs]
  cases hs
  have hl : t'.lens = τ.t.lens := by simpa using hl
  have inv := ha hok
  obtain ⟨had, hb⟩ := baseStep_sound inv.base inv.one₁ inv.one₂ ht e₁ e₂
  have r₁ := exec_rsp hsp e₁
  have r₂ := exec_rsp hsp e₂
  obtain ⟨w₁, f₁⟩ := exec_frame e₁
  obtain ⟨w₂, f₂⟩ := exec_frame e₂
  have hfit := mbAfter_fit (i := i) inv.mbFit
  refine ⟨had, fun _ => ⟨hb, by rw [r₁, r₂, inv.rsp], by rw [exec_unknowns e₁, exec_unknowns e₂, inv.unk],
    by rw [w₁, w₂, inv.wr], fun h => by rw [w₁]; exact inv.lens (hl ▸ h), by rw [w₁]; exact inv.nfr,
    by rw [r₁]; exact inv.room, by rw [r₁]; exact inv.top, ?_, ?_, inv.rasIn, inv.rasSorted, ?_, ?_,
    fun e he => by rw [hl]; exact hfit e he,
    ⟨ub_step inv.one₁ e₁, fl_step e₁, mb_step inv.base.wf₁ inv.one₁ inv.mbFit e₁⟩,
    ⟨ub_step inv.one₂ e₂, fl_step e₂, mb_step inv.base.wf₂ inv.one₂ inv.mbFit e₂⟩⟩⟩
  · intro i hi; simp only [region, w₁, r₁]; exact inv.frames i hi
  · intro i h₁ h₂; simp only [region, w₁, wb, r₁]; rw [w₁] at h₂; exact inv.others i h₁ h₂
  · intro j hj i hi; simp only [region, raSlot, wa, wb, w₁, r₁]; exact inv.rasFr j hj i hi
  · intro j hj hn hw
    have d := inv.dead j hj hn
    simp only [wa, wb] at hw d ⊢
    rw [w₁, r₁] at hw
    rw [r₁, r₂, f₁ _ hw, f₂ _ (by rw [← inv.wr, ← inv.rsp]; exact hw)]
    exact d hw

/-! ## Soundness: branches, joins and order -/

theorem cond_sound {τ : FT} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (h : (τ.ok && τ.t.flags) = true) : eval c s₁ = eval c s₂ := by
  simp only [Bool.and_eq_true] at h
  exact Taint.cond_sound (ha h.1).base h.2

/-- `RInv τ` gives `RInv σ` for a `σ` of the same frames that knows less. -/
theorem RInv.weaken {τ σ : FT} {s₁ s₂ : State} (inv : RInv τ s₁ s₂) (hn : σ.nfr = τ.nfr)
    (hd : σ.depth = τ.depth) (hr : σ.room = τ.room) (hra : σ.ras = τ.ras)
    (hb : Taint.Agree σ.t s₁ s₂) (hl : σ.t.lens = τ.t.lens)
    (hsec : ∀ j, ¬ InSec σ.sec j → ¬ InSec τ.sec j)
    (hub : ∀ p ∈ σ.ub, ∃ n, (p.1, n) ∈ τ.ub ∧ n ≤ p.2) (hfl : σ.fl = none ∨ σ.fl = τ.fl)
    (hmb : ∀ e ∈ σ.mb, e ∈ τ.mb) : RInv σ s₁ s₂ := by
  have e : ∀ s, wa s σ = wa s τ := fun s => by funext j; simp only [wa, wb, hr]
  have e' : ∀ s, raSlot s σ = raSlot s τ := fun s => by funext j; simp only [raSlot, e]
  have one : ∀ {s}, One τ s → One σ s := fun o =>
    ⟨fun p hp => by
      obtain ⟨n, hn, hle⟩ := hub p hp
      exact Nat.le_trans (o.ub (p.1, n) hn) hle,
     fun a b h => by
      rcases hfl with h' | h'
      · rw [h'] at h; cases h
      · exact o.fl a b (h' ▸ h),
     fun e he => o.mb e (hmb e he)⟩
  refine ⟨hb, inv.rsp, inv.unk, inv.wr, fun x => inv.lens (hl ▸ x), hn ▸ inv.nfr, hr ▸ inv.room,
    hd ▸ inv.top, ?_, ?_, ?_, hra ▸ inv.rasSorted, ?_, ?_, ?_, one inv.one₁, one inv.one₂⟩
  · rw [hn, hd]; exact inv.frames
  · intro i h₁ h₂; simp only [wb, hr, hd]; exact inv.others i (hn ▸ h₁) h₂
  · rw [hra, hr, hd]; exact inv.rasIn
  · rw [e', hra, hn]; exact inv.rasFr
  · intro j hj hnot hw
    rw [e] at hw ⊢; rw [e]
    exact inv.dead j (hr ▸ hd ▸ hj) (hsec j hnot) hw
  · intro e he; rw [hl]; exact inv.mbFit e (hmb e he)

theorem inSec_append_left {l₁ l₂ : List (Nat × Nat)} {j : Nat} (h : ¬ InSec (l₁ ++ l₂) j) : ¬ InSec l₁ j :=
  fun ⟨p, hp, h'⟩ => h ⟨p, List.mem_append_left _ hp, h'⟩

theorem inSec_append_right {l₁ l₂ : List (Nat × Nat)} {j : Nat} (h : ¬ InSec (l₁ ++ l₂) j) : ¬ InSec l₂ j :=
  fun ⟨p, hp, h'⟩ => h ⟨p, List.mem_append_right _ hp, h'⟩

theorem mem_ubMeet {l₁ l₂ : List (Reg × Nat)} {p : Reg × Nat}
    (h : p ∈ l₁.filterMap fun p => (ubOf l₂ p.1).map fun n => (p.1, max p.2 n)) :
    (∃ n, (p.1, n) ∈ l₁ ∧ n ≤ p.2) ∧ (∃ n, (p.1, n) ∈ l₂ ∧ n ≤ p.2) := by
  obtain ⟨q, hq, h⟩ := List.mem_filterMap.mp h
  obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨⟨q.2, hq, Nat.le_max_left _ _⟩, ⟨n, ubOf_some hn, Nat.le_max_right _ _⟩⟩

theorem meet_left {τ₁ τ₂ : FT} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ := by
  unfold meet
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, -⟩, hl⟩ := hc
    intro _
    refine (h h1).weaken rfl rfl rfl rfl (Taint.meet_left (h h1).base) (by simp [Taint.meet, hl])
      (fun j hn => inSec_append_left hn) (fun p hp => (mem_ubMeet hp).1) ?_
      (fun e he => (List.mem_filter.mp he).1)
    simp only
    split <;> [exact .inr rfl; exact .inl rfl]
  · exact fun h => absurd h (by decide)

theorem meet_right {τ₁ τ₂ : FT} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ := by
  unfold meet
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨-, h2⟩, hn⟩, hd⟩, hr⟩, hra⟩, hl⟩ := hc
    intro _
    refine (h h2).weaken hn hd hr hra (Taint.meet_right (h h2).base) (by simp [Taint.meet, hl])
      (fun j hn => inSec_append_right hn) (fun p hp => (mem_ubMeet hp).2) ?_
      (fun e he => by simpa using (List.mem_filter.mp he).2)
    simp only
    split
    · rename_i hf; simp only [beq_iff_eq] at hf; exact .inr hf
    · exact .inl rfl
  · exact fun h => absurd h (by decide)

theorem le_sound {τ σ : FT} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) : Agree τ s₁ s₂ := by
  intro hτ
  simp only [le, hτ, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.contains_iff_mem] at hle
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, hn⟩, hd⟩, hr⟩, hra⟩, hb⟩, hsec⟩, hub⟩, hfl⟩, hmb⟩ := hle
  have inv := h hs
  have hbase := Taint.le_sound (Taint.leK_eq ▸ hb) inv.base
  have hl : τ.t.lens = σ.t.lens := by
    have hb' := hb
    rw [Taint.leK_eq] at hb'; simp only [Taint.le, Bool.and_eq_true, beq_iff_eq] at hb'; exact hb'.1.1.1.1.2
  refine inv.weaken hn hd hr hra hbase hl (fun j hnot ⟨p, hp, h'⟩ => hnot ⟨p, hsec p hp, h'⟩) ?_ ?_ hmb
  · intro p hp
    have h := hub p hp
    cases hn : ubOf σ.ub p.1 with
    | none => rw [hn] at h; cases h
    | some n => rw [hn] at h; exact ⟨n, ubOf_some hn, by simpa using h⟩
  · rcases Bool.or_eq_true_iff.mp hfl with h | h
    · exact .inl (Option.isNone_iff_eq_none.mp h)
    · exact .inr (by simpa using h)

/-! ## The window -/

theorem addr_add_sub (p : Addr) (n r : Nat) : p + BitVec.ofNat 64 n - BitVec.ofNat 64 (r + n) = p - BitVec.ofNat 64 r := by
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 r), BitVec.sub_eq_add_neg, BitVec.neg_add,
    BitVec.sub_eq_add_neg, ← BitVec.add_assoc, BitVec.add_assoc p, BitVec.add_right_neg, BitVec.add_zero,
    BitVec.add_neg_eq_sub]

theorem addr_sub_sub (p : Addr) {n r : Nat} (h : n ≤ r) :
    p - BitVec.ofNat 64 n - BitVec.ofNat 64 (r - n) = p - BitVec.ofNat 64 r := by
  rw [Offset.sub_ofNat_eq p h, BitVec.add_sub_cancel]

theorem toNat_sub_ofNat (x : Addr) {n : Nat} (h : n ≤ x.toNat) : (x - BitVec.ofNat 64 n).toNat = x.toNat - n := by
  have := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega),
    show 2 ^ 64 - n + x.toNat = x.toNat - n + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem toNat_add_ofNat (x : Addr) {n : Nat} (h : x.toNat + n < 2 ^ 64) : (x + BitVec.ofNat 64 n).toNat = x.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

theorem wa_eq {s₁ s₂ : State} {τ : FT} (h : s₁.gpr .rsp = s₂.gpr .rsp) (j : Nat) : wa s₁ τ j = wa s₂ τ j := by
  simp only [wa, wb, h]

/-- An address within `n` bytes below the stack pointer is a window index below `room`. -/
theorem below_wa {τ : FT} {s : State} {n : Nat} (hn : n ≤ τ.room) (y : Addr) :
    y = wa s τ (τ.room - n + (y - (s.gpr .rsp - BitVec.ofNat 64 n)).toNat) := by
  simp only [wa, wb]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← Offset.sub_ofNat_eq _ hn, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.add_comm, BitVec.sub_add_cancel]

theorem wa_shift {s s' : State} {τ τ' : FT}
    (h : s'.gpr .rsp - BitVec.ofNat 64 τ'.room = s.gpr .rsp - BitVec.ofNat 64 τ.room) : wa s' τ' = wa s τ := by
  funext j; simp only [wa, wb, h]

theorem region_getElem {s : State} {i : Nat} (hi : i < s.wr.length) : region s i = s.wr[i] := by
  simp only [region, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem contains_self (a : Addr) {n : Nat} (h : 0 < n) : (⟨a, n⟩ : Region).Contains a 1 := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- The bytes of the window below the stack pointer are in no writable region. -/
theorem below_free {τ : FT} {s₁ s₂ : State} (inv : RInv τ s₁ s₂) {j : Nat} (hj : j < τ.room) :
    ∀ r ∈ s₁.wr, ¬ r.Contains (wa s₁ τ j) 1 := by
  intro r hr hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  have hroom := inv.room
  have htop := inv.top
  rw [← region_getElem hi] at hc
  by_cases hfr : i < τ.nfr
  · have h1 := inv.frames i hfr _ hc
    have hw : wa s₁ τ j = s₁.gpr .rsp - BitVec.ofNat 64 (τ.room - j) := by
      simp only [wa, wb]
      rw [Offset.sub_ofNat_eq _ (Nat.sub_le τ.room j), Nat.sub_sub_self (Nat.le_of_lt hj)]
    have hd := Offset.base_disjoint_below (s₁.gpr .rsp) (n := τ.room - j) (k := τ.depth) (by omega)
    exact hd _ h1 (by rw [hw]; exact contains_self _ (by omega))
  · have hd := inv.others i (by omega) hi
    exact hd _ hc (Offset.contains_base _ (by omega) (by omega))

theorem below_free' {τ : FT} {s₁ s₂ : State} (inv : RInv τ s₁ s₂) {n : Nat} (hn : n ≤ τ.room) :
    ∀ y, (y - (s₁.gpr .rsp - BitVec.ofNat 64 n)).toNat < n → ∀ r ∈ s₁.wr, ¬ r.Contains y 1 := by
  intro y hy
  rw [below_wa hn y]
  exact below_free inv (by omega)

/-- A byte of a region the base analysis knows is in the region. -/
theorem byte_in {t : Taint.T} {s : State} (hw : Wf t s) {i k : Nat} (hk : k < t.lens.getD i 0) :
    region s i ∈ s.wr ∧ (region s i).Contains (byteAddr s i k) 1 := by
  have hne := lens_ne (n := k + 1) (by omega) hk
  obtain ⟨hi, hri⟩ := region_mem hw hne (i := i) (by omega)
  have hli := region_len hw hne i
  have hb : (region s i).len ≤ 2 ^ 64 := by rw [hri]; exact (hw.1 hne).2.2 _ (List.getElem_mem _)
  refine ⟨hri ▸ List.getElem_mem _, ?_⟩
  simp only [Region.Contains, byteAddr]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The pointers of `mb` are kept by a change of memory outside the writable regions. -/
theorem mb_out {τ : FT} {s s' : State} (hw : Wf τ.t s) (o : One τ s)
    (hfit : ∀ e ∈ τ.mb, e.2.1 + 8 ≤ τ.t.lens.getD e.1 0) (hwr : s'.wr = s.wr)
    (hm : ∀ y, (∃ r ∈ s.wr, r.Contains y 1) → s'.mem y = s.mem y) :
    ∀ e ∈ τ.mb, s'.mem.readW (byteAddr s' e.1 e.2.1) 64 = (region s' e.2.2.1).base + BitVec.ofNat 64 e.2.2.2 := by
  intro e he
  have hba : byteAddr s' e.1 e.2.1 = byteAddr s e.1 e.2.1 := by simp only [byteAddr, region, hwr]
  have hrg : region s' e.2.2.1 = region s e.2.2.1 := by simp only [region, hwr]
  rw [hba, hrg, ← o.mb e he]
  apply Mem.readW_congr
  intro k hk
  simp only [Nat.reduceDiv] at hk
  rw [byteAddr_add]
  have := hfit e he
  obtain ⟨h1, h2⟩ := byte_in hw (i := e.1) (k := e.2.1 + k) (by omega)
  exact hm _ ⟨_, h1, h2⟩

/-- The base analysis's agreement after a call or a return: the stack pointer
moves the same way in both runs, and memory changes only to equal values. -/
theorem agree_killSp {t : Taint.T} {s₁ s₂ s₁' s₂' : State} (ha : Taint.Agree t s₁ s₂)
    (hsp : s₁'.gpr .rsp = s₂'.gpr .rsp)
    (hg₁ : ∀ r, r ≠ .rsp → s₁'.gpr r = s₁.gpr r) (hg₂ : ∀ r, r ≠ .rsp → s₂'.gpr r = s₂.gpr r)
    (hf₁ : s₁'.cf = s₁.cf ∧ s₁'.zf = s₁.zf ∧ s₁'.sf = s₁.sf ∧ s₁'.of = s₁.of)
    (hf₂ : s₂'.cf = s₂.cf ∧ s₂'.zf = s₂.zf ∧ s₂'.sf = s₂.sf ∧ s₂'.of = s₂.of)
    (hx₁ : s₁'.xmm = s₁.xmm) (hx₂ : s₂'.xmm = s₂.xmm) (hw₁ : s₁'.wr = s₁.wr) (hw₂ : s₂'.wr = s₂.wr)
    (hm : ∀ a, (s₁'.mem a = s₁.mem a ∧ s₂'.mem a = s₂.mem a) ∨ s₁'.mem a = s₂'.mem a) :
    Taint.Agree (killSp t) s₁' s₂' where
  rf := ⟨fun r hr => by
      by_cases h : r = .rsp
      · subst h; exact hsp
      · rw [hg₁ r h, hg₂ r h]; exact ha.rf.1 r hr,
    fun hf => by
      obtain ⟨a, b, c, d⟩ := ha.rf.2 hf
      rw [hf₁.1, hf₂.1, hf₁.2.1, hf₂.2.1, hf₁.2.2.1, hf₂.2.2.1, hf₁.2.2.2, hf₂.2.2.2]
      exact ⟨a, b, c, d⟩⟩
  wr h := by rw [hw₁, hw₂]; exact ha.wr h
  wf₁ := ⟨fun h => by rw [hw₁]; exact ha.wf₁.1 h, kill_bases ha.wf₁ hw₁ hg₁⟩
  wf₂ := ⟨fun h => by rw [hw₂]; exact ha.wf₂.1 h, kill_bases ha.wf₂ hw₂ hg₂⟩
  ok := ha.ok
  slots sl h k h₁ h₂ := by
    have hb : ∀ s s' : State, s'.wr = s.wr → byteAddr s' sl.1 k = byteAddr s sl.1 k := fun s s' h => by
      simp only [byteAddr, region, h]
    rw [hb _ _ hw₁, hb _ _ hw₂, ← ha.byteAddr_eq h h₂]
    rcases hm (byteAddr s₁ sl.1 k) with ⟨e₁, e₂⟩ | e
    · have := ha.slots sl h k h₁ h₂
      rw [← ha.byteAddr_eq h h₂] at this
      rw [e₁, e₂]; exact this
    · exact e
  lo := noLo
  xr r h := by rw [hx₁, hx₂]; exact ha.xr r h

/-- `[p, p + d)` without its first `b` bytes. -/
theorem sub_shrink {r : Region} {p : Addr} {d b : Nat} (hs : Region.Sub r ⟨p, d⟩)
    (hd : Region.Disjoint r ⟨p, b⟩) (hb : b ≤ d) (hd64 : d < 2 ^ 64) :
    Region.Sub r ⟨p + BitVec.ofNat 64 b, d - b⟩ := by
  intro a ha
  have h1 := hs a ha
  have h2 := hd a ha
  simp only [Region.Contains] at h1 h2 ⊢
  rw [Offset.toNat_sub_add _ _ (by omega), show 2 ^ 64 - b + (a - p).toNat = (a - p).toNat - b + 2 ^ 64 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  omega

theorem sub_down (p : Addr) (n d : Nat) : Region.Sub ⟨p, d⟩ ⟨p - BitVec.ofNat 64 n, d + n⟩ := by
  have := Offset.sub_base (p - BitVec.ofNat 64 n) (d := n) (n := d) (k := d + n) (by omega)
  rwa [BitVec.sub_add_cancel] at this

theorem Region.sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

/-! ## Soundness: calls and returns -/

/-- What a call does to the state, field by field. -/
structure CallFx (s s' : State) : Prop where
  sp : s'.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 8
  gpr : ∀ r, r ≠ .rsp → s'.gpr r = s.gpr r
  flags : s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.sf = s.sf ∧ s'.of = s.of
  xmm : s'.xmm = s.xmm
  wr : s'.wr = s.wr
  unk : s'.unknowns = fun n => s.unknowns (n + 1)
  mem : s'.mem = s.mem.writeW (s.gpr .rsp - BitVec.ofNat 64 8) (s.unknowns 0)

theorem callFx {s s' : State} (h : isa.call s = some s') : CallFx s s' := by
  simp only [isa, call, Option.some.injEq] at h
  subst h
  exact ⟨by simp only [State.setReg, ↓reduceIte]; rfl, fun _ h => setReg_ne h, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

theorem call_sound {τ τ' : FT} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂) (hs : callF τ = some τ')
    (e₁ : isa.call s₁ = some s₁') (e₂ : isa.call s₂ = some s₂') :
    isa.callAddrs s₁ = isa.callAddrs s₂ ∧ Agree τ' s₁' s₂' := by
  unfold callF at hs
  split at hs <;> [rename_i hc; cases hs]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hok, h8⟩ := hc
  cases hs
  have inv := ha hok
  have c₁ := callFx e₁
  have c₂ := callFx e₂
  refine ⟨by simp only [inv.rsp], fun _ => ?_⟩
  have hroom := inv.room
  have htop := inv.top
  -- What the call writes: the 8 bytes below the stack pointer, the same in both runs.
  have hout₁ : ∀ y, ¬ (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 8 → s₁'.mem y = s₁.mem y := by
    intro y hy; rw [c₁.mem]; exact writeW_out (by simpa using hy)
  have hout₂ : ∀ y, ¬ (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 8 → s₂'.mem y = s₂.mem y := by
    intro y hy; rw [c₂.mem, ← inv.rsp]; exact writeW_out (by simpa using hy)
  have hin : ∀ y, (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 8 → s₁'.mem y = s₂'.mem y := by
    intro y hy
    have hy' : (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 64 / 8 := hy
    rw [c₁.mem, c₂.mem]
    simp only [Mem.writeW, Mem.write, ← inv.rsp, ← inv.unk, hy', ↓reduceIte]
  have hm : ∀ y, (s₁'.mem y = s₁.mem y ∧ s₂'.mem y = s₂.mem y) ∨ s₁'.mem y = s₂'.mem y := by
    intro y
    by_cases hy : (y - (s₁.gpr .rsp - BitVec.ofNat 64 8)).toNat < 8
    · exact .inr (hin y hy)
    · exact .inl ⟨hout₁ y hy, hout₂ y hy⟩
  have hfree₁ := below_free' inv (n := 8) (by omega)
  have hsh₁ : s₁'.gpr .rsp - BitVec.ofNat 64 (τ.room - 8) = s₁.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [c₁.sp]; exact addr_sub_sub _ h8
  have hsh₂ : s₂'.gpr .rsp - BitVec.ofNat 64 (τ.room - 8) = s₂.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [c₂.sp]; exact addr_sub_sub _ h8
  have hr8 : (s₁.gpr .rsp - BitVec.ofNat 64 8).toNat = (s₁.gpr .rsp).toNat - 8 := toNat_sub_ofNat _ (by omega)
  have hwa8 : wa s₁ τ (τ.room - 8) = s₁.gpr .rsp - BitVec.ofNat 64 8 := by
    simp only [wa, wb]; rw [← Offset.sub_ofNat_eq _ h8]
  have hrg : ∀ i, region s₁' i = region s₁ i := fun i => by simp only [region, c₁.wr]
  refine ⟨agree_killSp inv.base (by rw [c₁.sp, c₂.sp, inv.rsp]) c₁.gpr c₂.gpr c₁.flags c₂.flags c₁.xmm c₂.xmm
      c₁.wr c₂.wr hm,
    by rw [c₁.sp, c₂.sp, inv.rsp], by rw [c₁.unk, c₂.unk, inv.unk], by rw [c₁.wr, c₂.wr, inv.wr],
    fun h => by rw [c₁.wr]; exact inv.lens h, by rw [c₁.wr]; exact inv.nfr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, inv.mbFit, ?_, ?_⟩
  · dsimp only; rw [c₁.sp]; omega
  · dsimp only; rw [c₁.sp]; omega
  · intro i hi
    dsimp only
    rw [hrg, c₁.sp]
    exact Region.sub_trans (inv.frames i hi) (sub_down _ 8 τ.depth)
  · intro i h₁ h₂
    rw [c₁.wr] at h₂
    have := inv.others i h₁ h₂
    simp only [wb] at this ⊢
    rw [hrg, hsh₁, show τ.room - 8 + (τ.depth + 8) = τ.room + τ.depth by omega]
    exact this
  · intro j hj
    dsimp only at hj ⊢
    rcases List.mem_cons.mp hj with rfl | hj
    · omega
    · have := inv.rasIn j hj; omega
  · dsimp only
    exact List.pairwise_cons.mpr ⟨fun j hj => by have := inv.rasIn j hj; omega, inv.rasSorted⟩
  · intro j hj i hi
    simp only [raSlot]
    rw [wa_shift hsh₁, hrg]
    dsimp only at hj
    rcases List.mem_cons.mp hj with rfl | hj
    · rw [hwa8]
      exact Region.Disjoint.sub_left (Offset.base_disjoint_below (s₁.gpr .rsp) (n := 8) (k := τ.depth) (by omega))
        (inv.frames i hi)
    · exact inv.rasFr j hj i hi
  · intro j hj hn hw
    rw [c₁.wr] at hw
    dsimp only at hj
    simp only [wa, wb] at hw ⊢
    rw [hsh₁] at hw
    rw [hsh₁, hsh₂, ← inv.rsp]
    show s₁'.mem (wa s₁ τ j) = s₂'.mem (wa s₁ τ j)
    rcases hm (wa s₁ τ j) with ⟨h₁, h₂⟩ | h
    · rw [h₁, h₂]
      have := inv.dead j (by omega) hn hw
      rwa [← wa_eq inv.rsp] at this
    · exact h
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [c₁.gpr _ hp.2]; exact inv.one₁.ub p hp.1
    · exact mb_out (τ := τ) inv.base.wf₁ inv.one₁ inv.mbFit c₁.wr
        (fun y ⟨r, hr, hc⟩ => hout₁ y (fun hy => hfree₁ y hy r hr hc))
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [c₂.gpr _ hp.2]; exact inv.one₂.ub p hp.1
    · exact mb_out (τ := τ) inv.base.wf₂ inv.one₂ inv.mbFit c₂.wr
        (fun y ⟨r, hr, hc⟩ => hout₂ y (fun hy => hfree₁ y hy r (inv.wr ▸ hr) hc))

theorem retFx {a b c : State} (h : isa.ret a b = some c) :
    c.gpr .rsp = b.gpr .rsp + BitVec.ofNat 64 8 ∧ (∀ r, r ≠ .rsp → c.gpr r = b.gpr r) ∧
    (c.cf = b.cf ∧ c.zf = b.zf ∧ c.sf = b.sf ∧ c.of = b.of) ∧ c.xmm = b.xmm ∧ c.wr = b.wr ∧
    c.unknowns = b.unknowns ∧ c.mem = b.mem := by
  simp only [isa, ret] at h
  split at h <;> [skip; cases h]
  cases h
  exact ⟨by simp only [State.setReg, ↓reduceIte]; rfl, fun _ h => setReg_ne h, ⟨rfl, rfl, rfl, rfl⟩,
    rfl, rfl, rfl, rfl⟩

theorem ret_sound {τ τ' : FT} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂) (hs : retF τ = some τ')
    (e₁ : isa.ret a₁ b₁ = some c₁) (e₂ : isa.ret a₂ b₂ = some c₂) :
    isa.retAddrs b₁ = isa.retAddrs b₂ ∧ Agree τ' c₁ c₂ := by
  unfold retF at hs
  split at hs <;> [rename_i hc; cases hs]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨hok, hhd⟩, h8⟩ := hc
  cases hs
  have inv := ha hok
  obtain ⟨sp₁, g₁, f₁, x₁, w₁, u₁, m₁⟩ := retFx e₁
  obtain ⟨sp₂, g₂, f₂, x₂, w₂, u₂, m₂⟩ := retFx e₂
  refine ⟨by simp only [inv.rsp], fun _ => ?_⟩
  have hroom := inv.room
  have htop := inv.top
  obtain ⟨tl, hras⟩ : ∃ tl, τ.ras = τ.room :: tl := by
    cases h : τ.ras with
    | nil => rw [h] at hhd; cases hhd
    | cons x tl => rw [h] at hhd; cases hhd; exact ⟨tl, rfl⟩
  have hsorted := inv.rasSorted
  rw [hras] at hsorted
  have hsh₁ : c₁.gpr .rsp - BitVec.ofNat 64 (τ.room + 8) = b₁.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [sp₁]; exact addr_add_sub _ _ _
  have hsh₂ : c₂.gpr .rsp - BitVec.ofNat 64 (τ.room + 8) = b₂.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [sp₂]; exact addr_add_sub _ _ _
  have hr8 : (b₁.gpr .rsp + BitVec.ofNat 64 8).toNat = (b₁.gpr .rsp).toNat + 8 := toNat_add_ofNat _ (by omega)
  have hwaR : wa b₁ τ τ.room = b₁.gpr .rsp := by simp only [wa, wb, BitVec.sub_add_cancel]
  have hrg : ∀ i, region c₁ i = region b₁ i := fun i => by simp only [region, w₁]
  refine ⟨agree_killSp inv.base (by rw [sp₁, sp₂, inv.rsp]) g₁ g₂ f₁ f₂ x₁ x₂ w₁ w₂
      (fun y => .inl ⟨by rw [m₁], by rw [m₂]⟩),
    by rw [sp₁, sp₂, inv.rsp], by rw [u₁, u₂, inv.unk], by rw [w₁, w₂, inv.wr],
    fun h => by rw [w₁]; exact inv.lens h, by rw [w₁]; exact inv.nfr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, inv.mbFit, ?_, ?_⟩
  · dsimp only; rw [sp₁]; omega
  · dsimp only; rw [sp₁]; omega
  · intro i hi
    dsimp only
    rw [hrg, sp₁]
    have hd := inv.rasFr τ.room (by rw [hras]; exact List.mem_cons_self) i hi
    simp only [raSlot, hwaR] at hd
    exact sub_shrink (inv.frames i hi) hd h8 (by omega)
  · intro i h₁ h₂
    rw [w₁] at h₂
    have := inv.others i h₁ h₂
    simp only [wb] at this ⊢
    rw [hrg, hsh₁, show τ.room + 8 + (τ.depth - 8) = τ.room + τ.depth by omega]
    exact this
  · intro j hj
    dsimp only at hj ⊢
    rw [hras] at hj
    have h1 := (List.pairwise_cons.mp hsorted).1 j hj
    have h2 := inv.rasIn j (by rw [hras]; exact List.mem_cons_of_mem _ hj)
    omega
  · dsimp only
    rw [hras]
    exact (List.pairwise_cons.mp hsorted).2
  · intro j hj i hi
    dsimp only at hj
    rw [hras] at hj
    simp only [raSlot, wa, wb]
    rw [hsh₁, hrg]
    exact inv.rasFr j (by rw [hras]; exact List.mem_cons_of_mem _ hj) i hi
  · intro j hj hn hw
    rw [w₁] at hw
    dsimp only at hj
    simp only [wa, wb] at hw ⊢
    rw [hsh₁] at hw
    rw [hsh₁, hsh₂, m₁, m₂]
    exact inv.dead j (by omega) hn hw
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [g₁ _ hp.2]; exact inv.one₁.ub p hp.1
    · exact mb_out (τ := τ) inv.base.wf₁ inv.one₁ inv.mbFit w₁ (fun y _ => by rw [m₁])
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [g₂ _ hp.2]; exact inv.one₂.ub p hp.1
    · exact mb_out (τ := τ) inv.base.wf₂ inv.one₂ inv.mbFit w₂ (fun y _ => by rw [m₂])

/-! ## Soundness: frames -/

theorem split16_mem : ∀ {f x n : Nat} {q : Nat × Nat}, q ∈ split16 f x n → x ≤ q.1 ∧ q.1 + q.2 ≤ x + n ∧ 0 < q.2
  | 0, _, _, _, h => by simp [split16] at h
  | _ + 1, _, 0, _, h => by simp [split16] at h
  | f + 1, x, n + 1, q, h => by
    simp only [split16] at h
    split at h
    · simp only [List.mem_singleton] at h; subst h; simp only; omega
    · rcases List.mem_cons.mp h with rfl | h
      · simp only; omega
      · have := split16_mem h; omega

/-- The slots of a new frame are bytes of the frame outside `sec`. -/
theorem newSlots_mem {sec : List (Nat × Nat)} {a b : Nat} {sl : Nat × Nat × Nat} (h : sl ∈ newSlots sec a b) :
    sl.1 = 0 ∧ sl.2.1 + sl.2.2 ≤ b ∧ ∀ k, sl.2.1 ≤ k → k < sl.2.1 + sl.2.2 → ¬ InSec sec (a + k) := by
  simp only [newSlots, List.mem_map, List.mem_flatMap] at h
  obtain ⟨q, ⟨p, hp, hq⟩, rfl⟩ := h
  obtain ⟨h1, h2, h3⟩ := split16_mem hq
  have hin : ∀ j, q.1 ≤ j → j < q.1 + q.2 → (a ≤ j ∧ j < a + b) ∧ ¬ InSec sec j := by
    intro j hj₁ hj₂
    have := (mem_gaps (j := j) sec [(a, b)]).mp ⟨p, hp, by omega, by omega⟩
    obtain ⟨⟨p', hp', h'⟩, hn⟩ := this
    simp only [List.mem_singleton] at hp'; subst hp'
    exact ⟨h', hn⟩
  have hq1 := (hin q.1 (Nat.le_refl _) (by omega)).1
  have hq2 := (hin (q.1 + q.2 - 1) (by omega) (by omega)).1
  refine ⟨rfl, by simp only; omega, fun k hk₁ hk₂ => ?_⟩
  simp only at hk₁ hk₂
  exact (hin (a + k) (by omega) (by omega)).2

/-- What the allocation of a frame of `b` bytes does to the state. -/
structure AllocFx (b : Nat) (s s' : State) : Prop where
  sp : s'.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 b
  gpr : ∀ r, r ≠ .rsp → s'.gpr r = s.gpr r
  flags : s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.sf = s.sf ∧ s'.of = s.of
  xmm : s'.xmm = s.xmm
  wr : s'.wr = ⟨s.gpr .rsp - BitVec.ofNat 64 b, b⟩ :: s.wr
  unk : s'.unknowns = s.unknowns
  mem : s'.mem = s.mem
  lt : b < 4096

theorem allocFx {b : Nat} {s s' : State} (h : isa.push (.alloc b) s = some s') : AllocFx b s s' := by
  simp only [isa, push] at h
  split at h <;> [rename_i hc; cases h]
  cases h
  exact ⟨by simp only [State.setReg, ↓reduceIte], fun _ h => setReg_ne h, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
    rfl, hc.2.1⟩

theorem region_cons_zero {s : State} {r : Region} {l : List Region} (h : s.wr = r :: l) : region s 0 = r := by
  simp only [region, h, List.getD_cons_zero]

theorem region_cons_succ {s : State} {r : Region} {l : List Region} (h : s.wr = r :: l) (i : Nat) :
    region s (i + 1) = l.getD i ⟨0, 0⟩ := by
  simp only [region, h, List.getD_cons_succ]

/-- The wellformedness facts of the writable regions, whether or not the
base analysis knows any. -/
theorem wr_facts {τ : FT} {s₁ s₂ : State} (inv : RInv τ s₁ s₂) :
    List.Forall₂ (fun r l => l ≤ r.len) s₁.wr τ.t.lens ∧ s₁.wr.Pairwise Region.Disjoint ∧
      ∀ r ∈ s₁.wr, r.len ≤ 2 ^ 64 := by
  by_cases h : τ.t.lens = []
  · rw [inv.lens h, h]; exact ⟨.nil, .nil, fun _ h => by cases h⟩
  · exact inv.base.wf₁.1 h

theorem push_sound {τ τ' : FT} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : pushF τ i = some τ') (e₁ : isa.push i s₁ = some s₁') (e₂ : isa.push i s₂ = some s₂') :
    isa.addrs i s₁ = isa.addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i <;> simp only [pushF, reduceCtorEq] at hs
  rename_i b
  split at hs <;> [rename_i hc; cases hs]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hok, hb0⟩, hb4⟩, hb8⟩, hbr⟩ := hc
  cases hs
  have inv := ha hok
  have c₁ := allocFx e₁
  have c₂ := allocFx e₂
  refine ⟨rfl, fun _ => ?_⟩
  have hroom := inv.room
  have htop := inv.top
  have hsh₁ : s₁'.gpr .rsp - BitVec.ofNat 64 (τ.room - b) = s₁.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [c₁.sp]; exact addr_sub_sub _ hbr
  have hsh₂ : s₂'.gpr .rsp - BitVec.ofNat 64 (τ.room - b) = s₂.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [c₂.sp]; exact addr_sub_sub _ hbr
  have hrb : (s₁.gpr .rsp - BitVec.ofNat 64 b).toNat = (s₁.gpr .rsp).toNat - b := toNat_sub_ofNat _ (by omega)
  have hwab : ∀ k, wa s₁ τ (τ.room - b + k) = s₁.gpr .rsp - BitVec.ofNat 64 b + BitVec.ofNat 64 k := fun k => by
    simp only [wa, wb]
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, ← Offset.sub_ofNat_eq _ hbr]
  have hr0 : region s₁' 0 = ⟨s₁.gpr .rsp - BitVec.ofNat 64 b, b⟩ := region_cons_zero c₁.wr
  have hrs : ∀ i, region s₁' (i + 1) = region s₁ i := fun i => region_cons_succ c₁.wr i
  have hrs₂ : ∀ i, region s₂' (i + 1) = region s₂ i := fun i => region_cons_succ c₂.wr i
  have hba : ∀ i k, byteAddr s₁' (i + 1) k = byteAddr s₁ i k := fun i k => by simp only [byteAddr, hrs]
  have hba₂ : ∀ i k, byteAddr s₂' (i + 1) k = byteAddr s₂ i k := fun i k => by simp only [byteAddr, hrs₂]
  have hfree := below_free' inv (n := b) hbr
  obtain ⟨hF, hP, hB⟩ := wr_facts inv
  -- The new frame is disjoint from every writable region.
  have hdis : ∀ r ∈ s₁.wr, Region.Disjoint ⟨s₁.gpr .rsp - BitVec.ofNat 64 b, b⟩ r := by
    intro r hr a ha hc
    exact hfree a (by simp only [Region.Contains] at ha; omega) r hr hc
  have hwr₂ : s₂'.wr = s₁'.wr := by rw [c₁.wr, c₂.wr, inv.rsp, inv.wr]
  have hbase : Taint.Agree (shiftIn τ.t b (newSlots τ.sec (τ.room - b) b)) s₁' s₂' := by
    have wf : ∀ {s s' : State}, AllocFx b s s' → s.gpr .rsp = s₁.gpr .rsp → s.wr = s₁.wr → Wf τ.t s →
        Wf (shiftIn τ.t b (newSlots τ.sec (τ.room - b) b)) s' := by
      intro s s' c hsp hwr hw
      refine ⟨fun _ => ?_, fun p hp => ?_⟩
      · rw [c.wr, hsp, hwr]
        exact ⟨.cons (Nat.le_refl _) hF, List.pairwise_cons.mpr ⟨hdis, hP⟩, fun r hr => by
          rcases List.mem_cons.mp hr with rfl | hr
          · simp only; omega
          · exact hB r hr⟩
      · simp only [shiftIn, List.mem_cons, List.mem_map] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩
        · simp only [region_cons_zero c.wr, c.sp, BitVec.add_zero]
        · simp only [kill, List.mem_filter, bne_iff_ne, ne_eq] at hq
          simp only [region_cons_succ c.wr, c.gpr _ hq.2, hw.2 q hq.1]
          rfl
    refine ⟨⟨fun r hr => ?_, fun hf => ?_⟩, fun _ => hwr₂.symm, wf c₁ rfl rfl inv.base.wf₁,
      wf c₂ inv.rsp.symm inv.wr.symm inv.base.wf₂, ?_, ?_, noLo, fun r hr => by
        rw [c₁.xmm, c₂.xmm]; exact inv.base.xr r hr⟩
    · by_cases h : r = .rsp
      · subst h; rw [c₁.sp, c₂.sp, inv.rsp]
      · rw [c₁.gpr r h, c₂.gpr r h]; exact inv.base.rf.1 r hr
    · obtain ⟨a, b', c, d⟩ := inv.base.rf.2 hf
      rw [c₁.flags.1, c₂.flags.1, c₁.flags.2.1, c₂.flags.2.1, c₁.flags.2.2.1, c₂.flags.2.2.1,
        c₁.flags.2.2.2, c₂.flags.2.2.2]
      exact ⟨a, b', c, d⟩
    · intro sl hsl
      simp only [shiftIn, List.mem_append, List.mem_map] at hsl
      rcases hsl with hsl | ⟨q, hq, rfl⟩
      · obtain ⟨h0, hle, -⟩ := newSlots_mem hsl
        simp only [h0]; exact hle
      · exact inv.base.ok q hq
    · intro sl hsl k hk₁ hk₂
      simp only [shiftIn, List.mem_append, List.mem_map] at hsl
      rcases hsl with hsl | ⟨q, hq, rfl⟩
      · obtain ⟨h0, hle, hn⟩ := newSlots_mem hsl
        rw [h0]
        have hb₁ : byteAddr s₁' 0 k = wa s₁ τ (τ.room - b + k) := by
          rw [hwab]; simp only [byteAddr, hr0]
        have hb₂ : byteAddr s₂' 0 k = wa s₂ τ (τ.room - b + k) := by
          rw [← wa_eq inv.rsp, ← hb₁]; simp only [byteAddr, region, hwr₂]
        rw [hb₁, hb₂, c₁.mem, c₂.mem]
        exact inv.dead _ (by omega) (hn k hk₁ hk₂) (below_free inv (by omega))
      · simp only at hk₁ hk₂ ⊢
        rw [hba, hba₂, c₁.mem, c₂.mem]
        exact inv.base.slots q hq k hk₁ hk₂
  refine ⟨hbase, by rw [c₁.sp, c₂.sp, inv.rsp], by rw [c₁.unk, c₂.unk, inv.unk], hwr₂.symm,
    fun h => by simp [shiftIn] at h, by rw [c₁.wr]; simp only [List.length_cons]; have := inv.nfr; omega,
    ?_, ?_, ?_, ?_, ?_, inv.rasSorted, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only; rw [c₁.sp]; omega
  · dsimp only; rw [c₁.sp]; omega
  · intro i hi
    dsimp only at hi ⊢
    rw [c₁.sp]
    cases i with
    | zero => rw [hr0]; exact Region.sub_prefix (by omega)
    | succ i => rw [hrs]; exact Region.sub_trans (inv.frames i (by omega)) (sub_down _ b τ.depth)
  · intro i h₁ h₂
    dsimp only at h₁
    rw [c₁.wr, List.length_cons] at h₂
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have := inv.others i (by omega) (by omega)
    simp only [wb] at this ⊢
    rw [hrs, hsh₁, show τ.room - b + (τ.depth + b) = τ.room + τ.depth by omega]
    exact this
  · intro j hj
    dsimp only at hj ⊢
    have := inv.rasIn j hj; omega
  · intro j hj i hi
    dsimp only at hj hi
    simp only [raSlot, wa, wb]
    rw [hsh₁]
    cases i with
    | zero =>
      rw [hr0]
      have hj' := inv.rasIn j hj
      rw [Offset.sub_ofNat_eq _ hbr]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    | succ i => rw [hrs]; exact inv.rasFr j hj i (by omega)
  · intro j hj hn hw
    dsimp only at hj hn
    simp only [wa, wb] at hw ⊢
    rw [hsh₁] at hw
    rw [hsh₁, hsh₂, c₁.mem, c₂.mem]
    exact inv.dead j (by omega) hn (fun r hr => hw r (by rw [c₁.wr]; exact List.mem_cons_of_mem _ hr))
  · intro e he
    simp only [List.mem_map] at he
    obtain ⟨e, he, rfl⟩ := he
    simp only [shiftIn, List.getD_cons_succ]
    exact inv.mbFit e he
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), fun e he => ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [c₁.gpr _ hp.2]; exact inv.one₁.ub p hp.1
    · simp only [List.mem_map] at he
      obtain ⟨e, he, rfl⟩ := he
      simp only [hba, hrs, c₁.mem]
      exact inv.one₁.mb e he
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), fun e he => ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [c₂.gpr _ hp.2]; exact inv.one₂.ub p hp.1
    · simp only [List.mem_map] at he
      obtain ⟨e, he, rfl⟩ := he
      simp only [hba₂, hrs₂, c₂.mem]
      exact inv.one₂.mb e he

/-- What the free of a frame of `b` bytes does to the state. -/
structure FreeFx (b : Nat) (s s' : State) : Prop where
  head : s.wr = ⟨s.gpr .rsp, b⟩ :: s'.wr
  sp : s'.gpr .rsp = s.gpr .rsp + BitVec.ofNat 64 b
  gpr : ∀ r, r ≠ .rsp → s'.gpr r = s.gpr r
  flags : s'.cf = s.cf ∧ s'.zf = s.zf ∧ s'.sf = s.sf ∧ s'.of = s.of
  xmm : s'.xmm = s.xmm
  unk : s'.unknowns = s.unknowns
  mem : s'.mem = s.mem

theorem freeFx {b : Nat} {a s s' : State} (h : isa.pop (.free b) a s = some s') : FreeFx b s s' := by
  simp only [isa, pop] at h
  split at h <;> [rename_i hc; cases h]
  cases h
  obtain ⟨-, -, -, hsp, hwr, hhd⟩ := hc
  refine ⟨?_, by simp only [State.setReg, ↓reduceIte], fun _ h => setReg_ne h, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
  rw [hwr]
  cases hw : a.wr with
  | nil => rw [hw] at hhd; cases hhd
  | cons r l => rw [hw] at hhd; cases hhd; rw [hsp]; rfl

theorem region_tail {s s' : State} {r : Region} (h : s.wr = r :: s'.wr) (i : Nat) :
    region s' i = region s (i + 1) := by
  simp only [region, h, List.getD_cons_succ]

theorem pop_sound {τ τ' : FT} {j : Instr} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : popF τ j = some τ') (e₁ : isa.pop j a₁ b₁ = some c₁) (e₂ : isa.pop j a₂ b₂ = some c₂) :
    isa.addrs j b₁ = isa.addrs j b₂ ∧ Agree τ' c₁ c₂ := by
  cases j <;> simp only [popF, reduceCtorEq] at hs
  rename_i b
  split at hs <;> [rename_i hc; cases hs]
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨hok, hn1⟩, hhd⟩, hbd⟩, hras⟩ := hc
  cases hs
  have inv := ha hok
  have c₁' := freeFx e₁
  have c₂' := freeFx e₂
  refine ⟨rfl, fun _ => ?_⟩
  have hroom := inv.room
  have htop := inv.top
  have hne : τ.t.lens ≠ [] := by intro h; rw [h] at hhd; cases hhd
  obtain ⟨hF, hP, hB⟩ := inv.base.wf₁.1 hne
  obtain ⟨lt, hlt⟩ : ∃ lt, τ.t.lens = b :: lt := by
    cases h : τ.t.lens with
    | nil => exact absurd h hne
    | cons x lt => rw [h] at hhd; cases hhd; exact ⟨lt, rfl⟩
  have hw1 := c₁'.head
  have hsh₁ : c₁.gpr .rsp - BitVec.ofNat 64 (τ.room + b) = b₁.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [c₁'.sp]; exact addr_add_sub _ _ _
  have hsh₂ : c₂.gpr .rsp - BitVec.ofNat 64 (τ.room + b) = b₂.gpr .rsp - BitVec.ofNat 64 τ.room := by
    rw [c₂'.sp]; exact addr_add_sub _ _ _
  have hwr₂ : c₂.wr = c₁.wr := by
    have h := c₂'.head
    rw [← inv.wr, hw1, ← inv.rsp] at h
    exact (List.cons.inj h).2.symm
  have hrb : (b₁.gpr .rsp + BitVec.ofNat 64 b).toNat = (b₁.gpr .rsp).toNat + b := toNat_add_ofNat _ (by omega)
  have hrt : ∀ i, region c₁ i = region b₁ (i + 1) := region_tail hw1
  have hrt₂ : ∀ i, region c₂ i = region b₂ (i + 1) := region_tail c₂'.head
  have hba : ∀ i k, byteAddr c₁ i k = byteAddr b₁ (i + 1) k := fun i k => by simp only [byteAddr, hrt]
  have hba₂ : ∀ i k, byteAddr c₂ i k = byteAddr b₂ (i + 1) k := fun i k => by simp only [byteAddr, hrt₂]
  have hr0 : region b₁ 0 = ⟨b₁.gpr .rsp, b⟩ := region_cons_zero hw1
  have hlen : b₁.wr.length = c₁.wr.length + 1 := by rw [hw1, List.length_cons]
  -- The regions after the frame are disjoint from it.
  have hdis : ∀ i, Region.Disjoint (region b₁ (i + 1)) ⟨b₁.gpr .rsp, b⟩ := by
    intro i
    rw [hw1] at hP
    by_cases hi : i < c₁.wr.length
    · rw [region_cons_succ hw1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact Region.Disjoint.symm ((List.pairwise_cons.mp hP).1 _ (List.getElem_mem _))
    · intro x hx
      rw [region_cons_succ hw1, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
        Option.getD_none] at hx
      simp only [Region.Contains] at hx; omega
  have hbase : Taint.Agree (shiftOut τ.t) c₁ c₂ := by
    have wf : ∀ {s s' : State}, FreeFx b s s' → Wf τ.t s → Wf (shiftOut τ.t) s' := by
      intro s s' c hw
      refine ⟨fun _ => ?_, fun p hp => ?_⟩
      · obtain ⟨hF, hP, hB⟩ := hw.1 hne
        rw [c.head, hlt] at hF
        rw [c.head] at hP hB
        simp only [shiftOut, hlt, List.tail_cons]
        exact ⟨(List.forall₂_cons.mp hF).2, (List.pairwise_cons.mp hP).2,
          fun r hr => hB r (List.mem_cons_of_mem _ hr)⟩
      · simp only [shiftOut, List.mem_filterMap, kill, List.mem_filter, bne_iff_ne, ne_eq] at hp
        obtain ⟨q, ⟨hq, hqr⟩, hq'⟩ := hp
        split at hq' <;> [cases hq'; rename_i hq0]
        cases hq'
        simp only
        rw [c.gpr _ hqr, hw.2 q hq, region_tail c.head, Nat.sub_add_cancel (by omega)]
    refine ⟨⟨fun r hr => ?_, fun hf => ?_⟩, fun _ => hwr₂.symm, wf c₁' inv.base.wf₁, wf c₂' inv.base.wf₂,
      ?_, ?_, noLo, fun r hr => by rw [c₁'.xmm, c₂'.xmm]; exact inv.base.xr r hr⟩
    · by_cases h : r = .rsp
      · subst h; rw [c₁'.sp, c₂'.sp, inv.rsp]
      · rw [c₁'.gpr r h, c₂'.gpr r h]; exact inv.base.rf.1 r hr
    · obtain ⟨a, b', c, d⟩ := inv.base.rf.2 hf
      rw [c₁'.flags.1, c₂'.flags.1, c₁'.flags.2.1, c₂'.flags.2.1, c₁'.flags.2.2.1, c₂'.flags.2.2.1,
        c₁'.flags.2.2.2, c₂'.flags.2.2.2]
      exact ⟨a, b', c, d⟩
    · intro sl hsl
      simp only [shiftOut, List.mem_filterMap] at hsl
      obtain ⟨q, hq, hq'⟩ := hsl
      split at hq' <;> [cases hq'; rename_i hq0]
      cases hq'
      have := inv.base.ok q hq
      simp only [shiftOut, hlt, List.tail_cons]
      rw [hlt] at this
      obtain ⟨k, hk⟩ : ∃ k, q.1 = k + 1 := ⟨q.1 - 1, by omega⟩
      rw [hk, List.getD_cons_succ] at this
      simp only [hk, Nat.add_sub_cancel]
      exact this
    · intro sl hsl k hk₁ hk₂
      simp only [shiftOut, List.mem_filterMap] at hsl
      obtain ⟨q, hq, hq'⟩ := hsl
      split at hq' <;> [cases hq'; rename_i hq0]
      cases hq'
      simp only at hk₁ hk₂ ⊢
      rw [hba, hba₂, c₁'.mem, c₂'.mem, Nat.sub_add_cancel (by omega)]
      exact inv.base.slots q hq k hk₁ hk₂
  refine ⟨hbase, by rw [c₁'.sp, c₂'.sp, inv.rsp], by rw [c₁'.unk, c₂'.unk, inv.unk], hwr₂.symm,
    ?_, by dsimp only; have := inv.nfr; omega, ?_, ?_, ?_, ?_, ?_, inv.rasSorted, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hF' := hF
    rw [hw1, hlt] at hF'
    have := forall₂_length (List.forall₂_cons.mp hF').2
    simp only [shiftOut, hlt, List.tail_cons] at h
    rw [h, List.length_nil] at this
    exact List.eq_nil_of_length_eq_zero this
  · dsimp only; rw [c₁'.sp]; omega
  · dsimp only; rw [c₁'.sp]; omega
  · intro i hi
    dsimp only at hi ⊢
    rw [hrt, c₁'.sp]
    exact sub_shrink (inv.frames (i + 1) (by omega)) (hdis i) hbd (by omega)
  · intro i h₁ h₂
    dsimp only at h₁
    have := inv.others (i + 1) (by omega) (by omega)
    simp only [wb] at this ⊢
    rw [hrt, hsh₁, show τ.room + b + (τ.depth - b) = τ.room + τ.depth by omega]
    exact this
  · intro j hj
    dsimp only at hj ⊢
    have := inv.rasIn j hj
    have := hras j hj
    omega
  · intro j hj i hi
    dsimp only at hj hi
    simp only [raSlot, wa, wb]
    rw [hsh₁, hrt]
    exact inv.rasFr j hj (i + 1) (by omega)
  · intro j hj hn hw
    dsimp only at hj hn
    simp only [wa, wb] at hw ⊢
    rw [hsh₁] at hw
    rw [hsh₁, hsh₂, c₁'.mem, c₂'.mem]
    show b₁.mem (wa b₁ τ j) = b₂.mem (wa b₂ τ j)
    change ∀ r ∈ c₁.wr, ¬ r.Contains (wa b₁ τ j) 1 at hw
    by_cases hin : (⟨b₁.gpr .rsp, b⟩ : Region).Contains (wa b₁ τ j) 1
    · -- A byte of the frame freed: public unless `sec` now lists it.
      have hrw : b₁.gpr .rsp = wb b₁ τ + BitVec.ofNat 64 τ.room := by simp only [wb, BitVec.sub_add_cancel]
      have hj' : τ.room ≤ j ∧ j < τ.room + b := by
        simp only [Region.Contains, hrw] at hin
        have h := (Offset.lt_iff (wa b₁ τ j) (wb b₁ τ) (d := τ.room) (n := b) (by omega)).mp (by omega)
        simp only [wa, Mem.sub_ofNat_toNat _ (show j < 2 ^ 64 by omega)] at h
        exact h
      have hfs : InSec (frameSlots τ.t τ.room) j := Classical.byContradiction fun hns => hn (by
        obtain ⟨p, hp, h⟩ := (mem_gaps (j := j) (frameSlots τ.t τ.room) [(τ.room, b)]).mpr
          ⟨⟨(τ.room, b), List.mem_singleton_self _, hj'⟩, hns⟩
        exact ⟨p, List.mem_append_right _ hp, h⟩)
      obtain ⟨p, hp, hp1, hp2⟩ := hfs
      simp only [frameSlots, List.mem_filterMap] at hp
      obtain ⟨sl, hsl, hsl'⟩ := hp
      split at hsl' <;> [rename_i h0; cases hsl']
      cases hsl'
      simp only at hp1 hp2
      have hag := inv.base.slots sl hsl (j - τ.room) (by omega) (by omega)
      have e₁ : byteAddr b₁ sl.1 (j - τ.room) = wa b₁ τ j := by
        rw [h0, byteAddr, hr0]
        dsimp only
        rw [hrw, wa, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hj'.1]
      have e₂ : byteAddr b₂ sl.1 (j - τ.room) = wa b₂ τ j := by
        rw [← inv.base.byteAddr_eq hsl (by omega), e₁, wa_eq inv.rsp]
      rw [← e₁, ← e₂]
      exact hag
    · have hw' : ∀ r ∈ b₁.wr, ¬ r.Contains (wa b₁ τ j) 1 := by
        rw [hw1]
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hin
        · exact hw r hr
      exact inv.dead j (by omega) (inSec_append_left hn) hw'
  · intro e he
    simp only [List.mem_filterMap] at he
    obtain ⟨q, hq, hq'⟩ := he
    split at hq' <;> [cases hq'; rename_i hq0]
    cases hq'
    have := inv.mbFit q hq
    simp only [shiftOut, hlt, List.tail_cons]
    rw [hlt] at this
    obtain ⟨k, hk⟩ : ∃ k, q.1 = k + 1 := ⟨q.1 - 1, by omega⟩
    rw [hk, List.getD_cons_succ] at this
    simp only [hk, Nat.add_sub_cancel]
    exact this
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), fun e he => ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [c₁'.gpr _ hp.2]; exact inv.one₁.ub p hp.1
    · simp only [List.mem_filterMap] at he
      obtain ⟨q, hq, hq'⟩ := he
      split at hq' <;> [cases hq'; rename_i hq0]
      cases hq'
      simp only
      rw [hba, hrt, c₁'.mem, Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
      exact inv.one₁.mb q hq
  · refine ⟨fun p hp => ?_, fun _ _ h => (by cases h), fun e he => ?_⟩
    · simp only [List.mem_filter, bne_iff_ne, ne_eq] at hp
      rw [c₂'.gpr _ hp.2]; exact inv.one₂.ub p hp.1
    · simp only [List.mem_filterMap] at he
      obtain ⟨q, hq, hq'⟩ := he
      split at hq' <;> [cases hq'; rename_i hq0]
      cases hq'
      simp only
      rw [hba₂, hrt₂, c₂'.mem, Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
      exact inv.one₂.mb q hq

/-! ## The analysis -/

/-- The residue analysis, as a `VG.Taint`. -/
def rtaint : VG.Taint isa where
  T := FT
  Agree := Agree
  step := step
  step_sound := step_sound
  condPub τ _ := τ.ok && τ.t.flags
  cond_sound := cond_sound
  meet := meet
  meet_left := meet_left
  meet_right := meet_right
  le := le
  le_sound := le_sound
  call := callF
  call_sound := call_sound
  ret := retF
  ret_sound := ret_sound
  push := pushF
  push_sound := push_sound
  pop := popF
  pop_sound := pop_sound

end VG.X86_64.RTaint
