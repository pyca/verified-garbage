module

public import VerifiedGarbage.Impl.AesCbc.AArch64
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.AesCbc.Mem
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Impl.Aes.AArch64.Blocks
public import VerifiedGarbage.Proof.Aes.AArch64.Encrypt
public import VerifiedGarbage.Proof.Aes.InvSboxSpec
public import VerifiedGarbage.Proof.Aes.InvBitsliced
public import VerifiedGarbage.Impl.Aes.AArch64.Callee
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `AesCbc.AArch64.Call`, which this module and modules that import it used -/

section

/-!
# AES-CBC on AArch64: the contracts, and a call of a block function

The artifacts' contracts are the shared ones of `Spec/Cbc/Contract.lean`,
which imply these (`Verified.lean`): `cbcAArch64 enc`, for encryption
(`enc = true`) and decryption, `modeAArch64` for CBC (`cbcMode`). A call
(`bl`) stores nothing in memory, so no stack is used.

`blk_call`: a call of any implementation of `vg_aes_encrypt_blocks` or
`vg_aes_decrypt_blocks` (`f` being `Spec.Aes.cipher` or
`Spec.Aes.invCipher`) on one block `D` in place, with working space `S`,
from its contract (with `WP.call`): `D` then holds `f` of it, and only `D`
and `S` change in memory. `blk_rel`: such calls, with the same arguments in
both runs, are constant time.
-/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cbc_encrypt` (`enc`) or `vg_aes_cbc_decrypt`
`(schedule = x0, rounds = x1, iv = x2, data = x3, n = x4, scratch = x5)`. -/
def modeAArch64 (M : Mode) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let iv : Region := ⟨s.gpr .x2, 16⟩
    let data : Region := ⟨s.gpr .x3, 16 * (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 2176⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧
      iv.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .x2).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    let w := bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1))
    let iv := bytesAt s.mem (s.gpr .x2) 16
    let xs := Spec.Cbc.blocksAt s.mem (s.gpr .x3) (s.gpr .x4).toNat
    Spec.Cbc.blocksAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat = M.out (s.gpr .x1).toNat w iv xs ∧
      bytesAt s'.mem (s.gpr .x2) 16 = M.chain (s.gpr .x1).toNat w iv xs
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

/-- `vg_aes_cbc_encrypt` (`enc`) or `vg_aes_cbc_decrypt`. -/
abbrev cbcAArch64 (enc : Bool) : Contract isa := modeAArch64 (cbcMode enc)

/-! ## A call of a block function -/

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 64 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hR])

theorem one_toNat : (1 : BitVec 64).toNat = 1 := rfl

theorem callEntry_x0 (s : State) : s.callEntry.gpr .x0 = s.gpr .x0 := s.callEntry_gpr (by decide)
theorem callEntry_x1 (s : State) : s.callEntry.gpr .x1 = s.gpr .x1 := s.callEntry_gpr (by decide)
theorem callEntry_x2 (s : State) : s.callEntry.gpr .x2 = s.gpr .x2 := s.callEntry_gpr (by decide)
theorem callEntry_x3 (s : State) : s.callEntry.gpr .x3 = s.gpr .x3 := s.callEntry_gpr (by decide)
theorem callEntry_x4 (s : State) : s.callEntry.gpr .x4 = s.gpr .x4 := s.callEntry_gpr (by decide)

/-- What a call of a block function on one block needs. -/
structure CallPre (s : State) (W D S : Addr) (R : Nat) : Prop where
  x0 : s.gpr .x0 = W
  x1 : s.gpr .x1 = BitVec.ofNat 64 R
  x2 : s.gpr .x2 = D
  x3 : s.gpr .x3 = 1
  x4 : s.gpr .x4 = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  wd : (⟨W, 240⟩ : Region).Disjoint ⟨D, 16⟩
  ws : (⟨W, 240⟩ : Region).Disjoint ⟨S, 2048⟩
  ds : (⟨D, 16⟩ : Region).Disjoint ⟨S, 2048⟩
  wrap : D.toNat + 16 ≤ 2 ^ 64
  reads : Covers ([⟨W, 240⟩] ++ [⟨D, 16⟩, ⟨S, 2048⟩]) (s.rd ++ s.wr)
  writes : Covers [⟨D, 16⟩, ⟨S, 2048⟩] s.wr

/-- What a call of a block function on one block leaves. -/
structure CallPost (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (W D S : Addr)
    (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  frame : Frame [⟨D, 16⟩, ⟨S, 2048⟩] s.mem s'.mem
  out : bytesAt s'.mem D 16 = (f R (bytesAt s.mem W (16 * (R + 1))) (Spec.Aes.stateAt s.mem D)).toList

/-- The block function's precondition, on entry to a call with the regions it is given. -/
theorem CallPre.blk_pre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s : State} {W D S : Addr}
    {R : Nat} (h : CallPre s W D S R) :
    (Proof.Aes.blocksAArch64 f).pre (s.callEntry.withRegions [⟨W, 240⟩] [⟨D, 16⟩, ⟨S, 2048⟩]) := by
  have hR := toNat_rounds h.rounds
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h.x0, h.x1, h.x2, h.x3, h.x4, hR, one_toNat, Nat.mul_one]
  exact ⟨trivial, trivial, h.wd, h.ws, h.ds, h.wrap, h.rounds⟩

theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true)
    {s : State} {W D S : Addr} {R : Nat} (h : CallPre s W D S R) :
    WP isa (.call b.name b.code) s (CallPost f s W D S R) := by
  have hR := toNat_rounds h.rounds
  refine WP.call (k := Proof.Aes.blocksAArch64 f) ok (rd := [⟨W, 240⟩])
    (wr := [⟨D, 16⟩, ⟨S, 2048⟩]) h.blk_pre h.reads h.writes ?_ nf
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, h.x0, h.x1, h.x2, h.x3, hR, one_toNat] at hpost
  rw [bytesAt_of_statesAt hpost]

/-- Calls of a block function on one block, with the same arguments in both
runs, are constant time. -/
theorem blk_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    {W D S : Addr} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → CallPre s₁ W D S R ∧ CallPre s₂ W D S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call b.name b.code) fun _ _ => True := by
  refine RelCT.call ok ct [⟨W, 240⟩] [⟨D, 16⟩, ⟨S, 2048⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.blk_pre, h₂.blk_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.blocksAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4,
    h₁.x0, h₁.x1, h₁.x2, h₁.x3, h₁.x4, h₂.x0, h₂.x1, h₂.x2, h₂.x3, h₂.x4, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesCbc.AArch64

end

end

/-!
# AES-CBC on AArch64: the code between the calls

The straight-line pieces of `whole`, `encBody` and `decBody`, run once each:
saving and restoring the registers, the arguments of a call, `xorInto` (the
block at `x22` XORed with the chaining value), `copy` (a block copied, as two
words) and `advance`, with their memories as explicit writes (`savedMem`,
`xorMem`, `copyMem`). `crun` runs a block symbolically.
-/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCbc.AArch64
open VG.Spec.Aes (bytesAt)

theorem write8 (m : Mem) (a : Addr) (v : BitVec (8 * 8)) : m.write a 8 v = m.writeW a v := by
  simp [Mem.writeW]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp [Mem.readW]

/-- Runs a block of the instructions the AES-CBC code uses. -/
macro "crun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| plain_simp_names (
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
    (Offset.add_add_eq b (by omega_using [h₁])).symm]
  exact Offset.contains_base _ (by omega_using [h₂]) (by omega_using [h₂])

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
