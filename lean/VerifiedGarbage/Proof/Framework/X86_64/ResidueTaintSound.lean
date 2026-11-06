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

end VG.X86_64.RTaint
