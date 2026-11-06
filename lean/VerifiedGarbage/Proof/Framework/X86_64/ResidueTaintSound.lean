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

end VG.X86_64.RTaint
