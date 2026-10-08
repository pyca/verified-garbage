import VerifiedGarbage.Proof.AesCbc.AArch64.Call

/-!
# AES-CBC on AArch64: the code between the calls

The straight-line pieces of `whole`, `encBody` and `decBody`, run once each:
saving and restoring the registers, the arguments of a call, `xorInto` (the
block at `x22` XORed with the chaining value), `copy` (a block copied, as two
words) and `advance`, with their memories as explicit writes (`savedMem`,
`xorMem`, `copyMem`). `crun` runs a block symbolically.
-/

namespace VG.Proof.AesCbc.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCbc.AArch64
open VG.Spec.Aes (bytesAt)

theorem write8 (m : Mem) (a : Addr) (v : BitVec (8 * 8)) : m.write a 8 v = m.writeW a v := by
  simp [Mem.writeW]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp [Mem.readW]

/-- Runs a block of the instructions the AES-CBC code uses. -/
macro "crun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.AArch64.addr,
    State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
    sp_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq, and_self,
    mov, List.cons_append, List.nil_append, reduceCtorEq, ↓reduceIte, Nat.reduceLT,
    Nat.reduceLeDiff, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod,
    and_true, true_and, write8, read8, BitVec.add_zero, $ts,*]) <;> try rfl)

/-! ## Saving and restoring the registers -/

/-- The memory after saving the registers. -/
def savedMem (s : State) : Mem :=
  saved.foldl (fun m (r, d) => m.writeW (s.gpr .x5 + BitVec.ofNat 64 d) (s.gpr r)) s.mem

theorem prologue_ok (s : State)
    (hw : ∀ d, 2064 ≤ d → d + 8 ≤ 2120 → InRegions s.wr (s.gpr .x5 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (save ++ setup) s = some s' ∧
      s'.gpr .x19 = s.gpr .x0 ∧ s'.gpr .x20 = s.gpr .x1 ∧ s'.gpr .x21 = s.gpr .x2 ∧
      s'.gpr .x22 = s.gpr .x3 ∧ s'.gpr .x23 = s.gpr .x4 ∧ s'.gpr .x24 = s.gpr .x5 ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = savedMem s ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, save, setup,
      saved, mov, List.map, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, addr, State.store, Size.bytes, Size.bits, State.read, gpr_write, Option.bind_some,
      hw 2064 (by decide) (by decide), hw 2072 (by decide) (by decide), hw 2080 (by decide) (by decide),
      hw 2088 (by decide) (by decide), hw 2096 (by decide) (by decide), hw 2104 (by decide) (by decide),
      hw 2112 (by decide) (by decide)]
    rfl, ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_, rfl, ?_, rfl, rfl⟩
  · simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆]
  · simp only [mem_write, savedMem, saved, List.foldl, Mem.writeW, BitVec.setWidth_eq]

theorem slot_contains (b : Addr) {d : Nat} (h₁ : 2064 ≤ d) (h₂ : d + 8 ≤ 2120) :
    (⟨b + BitVec.ofNat 64 2064, 56⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [show b + BitVec.ofNat 64 d = (b + BitVec.ofNat 64 2064) + BitVec.ofNat 64 (d - 2064) from
    (Offset.add_add_eq b (by omega)).symm]
  exact Offset.contains_base _ (by omega) (by omega)

/-- Saving the registers changes only their slots. -/
theorem savedMem_frame (s : State) : Frame [⟨s.gpr .x5 + BitVec.ofNat 64 2064, 56⟩] s.mem (savedMem s) := by
  simp only [savedMem, saved, List.foldl]
  exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (slot_contains _ (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (slot_contains _ (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (slot_contains _ (by decide) (by decide)))

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

/-- Each slot holds the register saved there. -/
theorem savedMem_slot (s : State) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (savedMem s).readW (s.gpr .x5 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  simp only [savedMem, saved, List.foldl]
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  repeat (first
    | rw [Mem.readW_writeW_self64]
    | rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)])

theorem restore_ok (s : State) {B : Addr} (hb : s.gpr .x24 = B)
    (hr : ∀ d, 2064 ≤ d → d + 8 ≤ 2120 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa restore s = some s' ∧
      (∀ r d, (r, d) ∈ saved → s'.gpr r = s.mem.readW (B + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x30 → r ≠ .x24 →
        s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, restore, saved,
      List.map, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, hb,
      hr 2064 (by decide) (by decide), hr 2072 (by decide) (by decide), hr 2080 (by decide) (by decide),
      hr 2088 (by decide) (by decide), hr 2096 (by decide) (by decide), hr 2104 (by decide) (by decide),
      hr 2112 (by decide) (by decide)]
    rfl, ?_⟩
  refine ⟨fun r d h => ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ => ?_, rfl, rfl⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [gpr_write, Mem.readW]
  · simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆, h₇]

/-! ## The pieces of a block -/

theorem callArgs_ok (s : State) :
    ∃ s', runBlock isa callArgs s = some s' ∧
      s'.gpr .x0 = s.gpr .x19 ∧ s'.gpr .x1 = s.gpr .x20 ∧ s'.gpr .x2 = s.gpr .x22 ∧
      s'.gpr .x3 = 1 ∧ s'.gpr .x4 = s.gpr .x24 ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [callArgs], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], ?_, by simp [gpr_write],
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-- The block at `x22` XORed with the chaining value at `x21`. -/
theorem xorInto_ok (s : State) {P Q : Addr} (hp : s.gpr .x22 = P) (hq : s.gpr .x21 = Q)
    (rp : InRegions (s.rd ++ s.wr) P 8) (rp8 : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 8) 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa xorInto s = some s' ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = xorMem s.mem P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [xorInto, hp, hq, rp, rp8, rq, rq8, wp, wp8], ?_⟩
  refine ⟨fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], rfl, ?_, rfl, rfl⟩
  simp only [xorMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq]

/-- The block at `src + e` copied to `dst + d`, given as `P` and `Q`. -/
theorem copy_ok (s : State) {dst src : Reg} {d e : Nat} {P Q : Addr}
    (hp : s.gpr dst + BitVec.ofNat 64 d = P) (hp8 : s.gpr dst + BitVec.ofNat 64 (d + 8) = P + BitVec.ofNat 64 8)
    (hq : s.gpr src + BitVec.ofNat 64 e = Q) (hq8 : s.gpr src + BitVec.ofNat 64 (e + 8) = Q + BitVec.ofNat 64 8)
    (rq : InRegions (s.rd ++ s.wr) Q 8) (rq8 : InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 8) 8)
    (wp : InRegions s.wr P 8) (wp8 : InRegions s.wr (P + BitVec.ofNat 64 8) 8)
    (hsrc : src ≠ .x9) (hdst : dst ≠ .x9)
    (hd : d % 8 = 0 ∧ d < 32768) (hd8 : (d + 8) % 8 = 0 ∧ d + 8 < 32768)
    (he : e % 8 = 0 ∧ e < 32768) (he8 : (e + 8) % 8 = 0 ∧ e + 8 < 32768) :
    ∃ s', runBlock isa (copy dst d src e) s = some s' ∧
      (∀ r, r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = copyMem s.mem P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [copy, hsrc, hdst, hd, hd8, he, he8, hp, hp8, hq, hq8, rq, rq8, wp, wp8], ?_⟩
  refine ⟨fun r h₁ => by simp [gpr_write, h₁], rfl, ?_, rfl, rfl⟩
  simp only [copyMem, Mem.writeW, Mem.readW, BitVec.setWidth_eq]

theorem advance_ok (s : State) :
    ∃ s', runBlock isa advance s = some s' ∧
      s'.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 16 ∧ s'.gpr .x23 = s.gpr .x23 - 1 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [advance, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_write, State.read]
  · simp [gpr_write, State.read]
  · simp [gpr_write, h₁, h₂]

end VG.Proof.AesCbc.AArch64
