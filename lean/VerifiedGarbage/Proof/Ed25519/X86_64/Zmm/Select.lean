module

public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombSelect
public import VerifiedGarbage.Impl.Ed25519.X86_64.CombZmm
import VerifiedGarbage.Proof.Framework.X86_64.ZVecKeep
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.X86_64Scal
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Sym
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.TCB.X86_64.Avx512

/-! ### `Ed25519.X86_64.Zmm.Keep`, which this module and modules that import it used -/

section

/-!
# The `zmm` comb: what the vector instructions keep

Untrusted: everything here is checked by Lean. `rfl` proofs of `t.mem = s.mem`,
for a state `t` built by vector instructions from `s` (often a local
definition), make the unifier compare the states field by field before it
reduces the projection, for seconds; `zkeep` rewrites with the frame lemmas
instead.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64

theorem zop_exec_syms (o : ZOp) (s : State) : (o.exec s).syms = s.syms := by
  cases o <;> rfl

theorem setV_syms (s : State) (len : VLen) (r : XReg) (lo hi : BitVec 128) :
    (s.setV len r lo hi).syms = s.syms := by
  cases s; rfl

theorem setZ_syms (s : State) (r : XReg) (a b c d : BitVec 128) : (s.setZ r a b c d).syms = s.syms := by
  cases s; rfl

theorem setMem_syms (s : State) (m : Mem) : (s.setMem m).syms = s.syms := by
  cases s; rfl

theorem vop_exec_syms (o : VOp) (s : State) : (o.exec s).syms = s.syms := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl

/-- Closes `t.f = s.f` for `f` the memory, the regions, the registers or the statics, `t` built
from `s` by vector instructions (unfolding local definitions). -/
tactic_template "zkeep" : tactic => `(tactic| simp (config := { zetaDelta := true }) only [ZOp.exec_mem, ZOp.exec_rd,
                   ZOp.exec_wr, ZOp.exec_gpr, zop_exec_syms, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, VOp.exec_gpr, vop_exec_syms,
                   State.setV_mem, State.setV_rd, State.setV_wr, State.setV_gpr, setV_syms, State.setZ_mem, State.setZ_rd,
                   State.setZ_wr, State.setZ_gpr, setZ_syms, State.setMem_rd, State.setMem_wr, State.setMem_gpr, setMem_syms])

end VG.Proof.Ed25519.X86_64.Zmm

end

end

/-! ### `Ed25519.X86_64.Zmm.Half`, which this module and modules that import it used -/

section

/-!
# The `zmm` comb: each half of the `zmm` code is the `ymm` code

`tzs t is` runs the `ymm` block `is` on both 256-bit halves of the `zmm`
registers at once (`Impl/Ed25519/X86_64/CombZmm.lean`). Half `h` of a state
`z` is the state `half b h z` whose `ymm` registers are the halves `h` of
`z`'s `zmm` registers, and whose memory, in the window `[1024, 1792)` of the
scratch at `b`, is the half `h` of each 64-byte row at `zrow` (`hmem`).

`Rel b h J z y` says that `y` is half `h` of `z` but for the registers in
`J` (those a blend's free register has clobbered and the block has not
written since) and the rows of the `zmm` code (which `y` does not see).
`sim_wp`: if the `ymm` block, run from states related to the halves, ends
in `Q h`, the `zmm` block ends in a state whose halves are related to states
satisfying `Q h`. The check `junk` (by `decide`) says the block reads no
register of `J`, and what `J` is after it.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64.Zmm
open VG.Impl.X25519.X86_64 (sc)
open VG.Impl.X25519.X86_64.Ifma (y lanes)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi xi_inj)
open VG.Proof.X25519.X86_64.Ifma (rdiOff rdiOff_ok vm vm_vop)

/-! ## Halves -/

/-- The byte of half `h` of the `zmm` rows for offset `o` of the window. -/
def zoff (h o : Nat) : Nat := ZB + 64 * ((o - 1024) / 32) + 32 * h + (o - 1024) % 32

/-- Whether offset `o` is in the window `[1024, 1792)`. -/
def InWin (o : Nat) : Prop := 1024 ≤ o ∧ o < 1792

instance (o : Nat) : Decidable (InWin o) := by unfold InWin; infer_instance

/-- Whether offset `o` is in the rows of the window, `[ZB, ZMASK)`. -/
def InZ (o : Nat) : Prop := ZB ≤ o ∧ o < ZMASK

instance (o : Nat) : Decidable (InZ o) := by unfold InZ; infer_instance

/-- The memory half `h` sees: the window from the `zmm` rows. -/
def hmem (b : Addr) (h : Nat) (m : Mem) : Mem := fun a =>
  if InWin (a - b).toNat then m (b + BitVec.ofNat 64 (zoff h (a - b).toNat)) else m a

/-- Half `h` of a state. -/
def half (b : Addr) (h : Nat) (z : State) : State :=
  { z with
    xmm := fun r => z.zlane r (2 * h)
    ymmHi := fun r => z.zlane r (2 * h + 1)
    mem := hmem b h z.mem }

/-- `y` is half `h` of `z` but for the registers of `J` and the rows of the window. -/
structure Rel (b : Addr) (h : Nat) (J : List Nat) (z y : State) : Prop where
  xmm : ∀ r, xi r ∉ J → y.xmm r = z.zlane r (2 * h)
  hi : ∀ r, xi r ∉ J → y.ymmHi r = z.zlane r (2 * h + 1)
  gpr : y.gpr = z.gpr
  rd : y.rd = z.rd
  wr : y.wr = z.wr
  mem : ∀ a, ¬ InZ (a - b).toNat → y.mem a = hmem b h z.mem a

theorem Rel.half (b : Addr) (h : Nat) (J : List Nat) (z : State) : Rel b h J z (half b h z) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem Rel.lane {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y) {r : XReg}
    (hj : xi r ∉ J) {k : Nat} (hk : k < 2) : y.lane r k = z.zlane r (2 * h + k) := by
  rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
  · exact hr.xmm r hj
  · exact hr.hi r hj

/-- The dword masks of a `vpblendd` selector's four bits. -/
def maskLane (n : BitVec 4) : BitVec 128 :=
  let f (k : Nat) : BitVec 32 := if n.getLsbD k then BitVec.allOnes 32 else 0
  ofDwords (f 0) (f 1) (f 2) (f 3)

/-- The `zmm` code's working space: the scratch at `b` (in `rdi`), with the masks of the
blends' selectors at `maskRow`. -/
structure ZOK (b : Addr) (z : State) : Prop where
  rdi : z.gpr .rdi = b
  wr : (⟨b, 8192⟩ : Region) ∈ z.wr
  nowrap : b.toNat + 8192 ≤ 2 ^ 64
  masks : ∀ sel ∈ blendSels, ∀ i < 4,
    (z.mem.readW (b + BitVec.ofNat 64 (maskRow sel)) 512).extractLsb' (128 * i) 128 =
      maskLane (sel.extractLsb' (4 * (i % 2)) 4)

/-! ## Lanes -/

theorem ternlog_AC (n : BitVec 4) (a c : BitVec 128) :
    ternlog (maskLane n) a c 0xAC = blendDwords a c n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨q, s, rfl, hq, hs⟩ : ∃ q s, i = 32 * q + s ∧ q < 4 ∧ s < 32 :=
    ⟨i / 32, i % 32, by omega_arith, by omega_arith, by omega_arith⟩
  simp only [ternlog, List.range, List.range.loop, List.foldl, BitVec.reduceGetLsb, Bool.false_eq_true,
    ↓reduceIte]
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
    decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
    BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, Bool.false_or]
  simp only [maskLane, blendDwords, getLsbD_ofDwords_block _ _ _ _ hq hs]
  rcases (by omega_arith : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
    simp only [↓reduceIte, Nat.reduceEqDiff] <;>
    cases n.getLsbD _ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, getLsbD_dword, decide_eq_true hs, Bool.true_and,
      BitVec.getLsbD_allOnes, Nat.mul_zero, Nat.zero_add] <;>
    cases a.getLsbD _ <;> cases c.getLsbD _ <;> simp

theorem zlane_vpternlogd (d a c : XReg) (n : BitVec 8) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vpternlogd d a c n).exec s).zlane r i =
      if r = d then ternlog (s.zlane d i) (s.zlane a i) (s.zlane c i) n else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi,
    pick4_lanes (fun i => ternlog (s.zlane d i) (s.zlane a i) (s.zlane c i) n) hi]

theorem zlane_vpmadd52 (hb : Bool) (d a c : XReg) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vpmadd52 hb d a c).exec s).zlane r i =
      if r = d then madd52 hb (s.zlane d i) (s.zlane a i) (s.zlane c i) else s.zlane r i := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi,
    pick4_lanes (fun i => madd52 hb (s.zlane d i) (s.zlane a i) (s.zlane c i)) hi]

theorem zlane_vpermq (d a : XReg) (o : BitVec 8) (s : State) (r : XReg) {h k : Nat} (hh : h < 2)
    (hk : k < 2) :
    ((ZOp.vpermq d a o).exec s).zlane r (2 * h + k) =
      if r = d then (permQwords (s.zlane a (2 * h + 1) ++ s.zlane a (2 * h)) o).extractLsb' (128 * k) 128
      else s.zlane r (2 * h + k) := by
  simp only [ZOp.exec]
  rw [State.zlane_setZ _ _ _ _ _ _ _ (by omega_arith)]
  split
  · rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl <;> rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl <;> rfl
  · rfl

theorem zlane_load (d : XReg) (v : BitVec 512) (s : State) (r : XReg) {i : Nat} (hi : i < 4) :
    (s.setZ d (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
      (v.extractLsb' 384 128)).zlane r i = if r = d then v.extractLsb' (128 * i) 128 else s.zlane r i := by
  rw [State.zlane_setZ _ _ _ _ _ _ _ hi, pick4_lanes (fun i => v.extractLsb' (128 * i) 128) hi]

/-- Half `h` of a `zmm` register. -/
theorem zmm_half (s : State) (r : XReg) {h : Nat} (hh : h < 2) :
    (s.zmm r).extractLsb' (256 * h) 256 = s.zlane r (2 * h + 1) ++ s.zlane r (2 * h) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.zmm, State.ymm, State.zlane, State.lane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    decide_eq_true hj, Bool.true_and]
  rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl
  · simp only [Nat.mul_zero, Nat.zero_add, show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide,
      show (1 : Nat) ≠ 0 by decide, ite_true, ite_false]
    rw [ite_eq_left hj]
  · simp only [show ¬ 256 * 1 + j < 256 by omega_arith, ite_false, show ¬ (2 * 1 + 1 : Nat) < 2 by decide,
      show ¬ (2 * 1 : Nat) < 2 by decide, BitVec.getLsbD_extractLsb', show 256 * 1 + j - 256 = j by omega_arith]
    by_cases h : j < 128
    · rw [ite_eq_left h, show 2 * 1 - 2 = 0 by rfl, Nat.mul_zero, Nat.zero_add, decide_eq_true h, Bool.true_and]
    · rw [ite_eq_right h, show 2 * 1 + 1 - 2 = 1 by rfl, Nat.mul_one, decide_eq_true (show j - 128 < 128 by omega_arith),
        Bool.true_and, show 128 + (j - 128) = j by omega_arith]

/-- `(x - (b + c)).toNat`, from `(x - b).toNat`. -/
theorem sub_off (x b : Addr) (c : Nat) :
    (x - (b + BitVec.ofNat 64 c)).toNat = (2 ^ 64 - c % 2 ^ 64 + (x - b).toNat) % 2 ^ 64 := by
  rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat]

theorem off_ofNat (b : Addr) {x : Nat} (hx : x < 2 ^ 64) : (b + BitVec.ofNat 64 x - b).toNat = x :=
  Mem.sub_ofNat_toNat b hx

/-! ## The check: which registers a block leaves junk -/

/-- The `VBinOp`s `toZ` translates. -/
def zbinOk : VBinOp → Bool
  | .vpaddq | .vpsubq | .vpand | .vpor | .vpxor | .vpunpcklqdq | .vpunpckhqdq => true
  | _ => false

theorem zbin_sse {op : VBinOp} (h : zbinOk op = true) : (zbin op).sse = op.sse := by
  cases op <;> first | rfl | (simp [zbinOk] at h)

/-- A row of the window: `[rdi + o]`, `o` 32-byte aligned in `[1024, 1792)`. -/
def rowOk (m : MemOp) : Bool :=
  match rdiOff m with
  | some o => decide (1024 ≤ o ∧ o + 32 ≤ 1792 ∧ (o - 1024) % 32 = 0)
  | none => false

/-- `J` once `d` is written. -/
def jw (J : List Nat) (d : XReg) : List Nat := J.filter (· ≠ xi d)

/-- Whether `r` is not junk. -/
def free (J : List Nat) (r : XReg) : Bool := !(J.contains (xi r))

theorem free_iff {J : List Nat} {r : XReg} : free J r = true ↔ xi r ∉ J := by
  simp [free]

theorem not_mem_jw {J : List Nat} {d r : XReg} (h : xi r ∉ jw J d) (hd : r ≠ d) : xi r ∉ J := by
  intro hm; exact h (List.mem_filter.2 ⟨hm, by simpa [xi_inj] using hd⟩)

/-- The junk after one instruction, if it reads none. -/
def jstep (t : Nat) (J : List Nat) : Instr → Option (List Nat)
  | .vop (.vbin op .l256 d a c) => if zbinOk op && free J a && free J c then some (jw J d) else none
  | .vop (.vshift .psllq .l256 d a _) => if free J a then some (jw J d) else none
  | .vop (.vshift .psrlq .l256 d a _) => if free J a then some (jw J d) else none
  | .vop (.vpermq d a _) => if free J a then some (jw J d) else none
  | .vop (.vpmadd52luq .l256 d a c) =>
    if free J d && free J a && free J c then some (jw J d) else none
  | .vop (.vpmadd52huq .l256 d a c) =>
    if free J d && free J a && free J c then some (jw J d) else none
  | .vop (.vmovdqa .l256 d a) => if free J a then some (jw J d) else none
  | .vop (.vpblendd .l256 d a c sel) =>
    if free J a && free J c && decide (t < 16) && xi a != t && xi c != t && blendSels.contains sel then
      some (if xi d = t then jw J d else t :: jw J d) else none
  | .vop (.vperm2i128 d a c sel) =>
    if (sel == 0x20 || sel == 0x31) && free J a && free J c then some (jw J d) else none
  | .vmovdquLoad .l256 d m => if rowOk m then some (jw J d) else none
  | .vmovdquStore .l256 m r => if rowOk m && free J r then some J else none
  | _ => none

/-- The junk after a block, if it reads none. -/
def junk (t : Nat) : List Nat → List Instr → Option (List Nat)
  | J, [] => some J
  | J, i :: is => (jstep t J i).bind fun J' => junk t J' is

/-! ## One instruction -/

/-- What the `zmm` code keeps: all but the vector registers, and the memory but the rows of the
window. -/
structure ZKeep (b : Addr) (z z' : State) : Prop where
  vm : vm z z' = z'
  mem : ∀ a, ¬ InZ (a - b).toNat → z'.mem a = z.mem a

theorem vm_trans {a b c : State} (h₁ : vm a b = b) (h₂ : vm b c = c) : vm a c = c := by
  rw [← h₂, ← h₁]; rfl

theorem vm_gpr' {s s' : State} (h : vm s s' = s') : s'.gpr = s.gpr := by rw [← h]; rfl
theorem vm_rd' {s s' : State} (h : vm s s' = s') : s'.rd = s.rd := by rw [← h]; rfl
theorem vm_wr' {s s' : State} (h : vm s s' = s') : s'.wr = s.wr := by rw [← h]; rfl

theorem ZKeep.refl (b : Addr) (z : State) : ZKeep b z z := ⟨by cases z; rfl, fun _ _ => rfl⟩

theorem ZKeep.trans {b : Addr} {z₁ z₂ z₃ : State} (h₁ : ZKeep b z₁ z₂) (h₂ : ZKeep b z₂ z₃) :
    ZKeep b z₁ z₃ :=
  ⟨vm_trans h₁.vm h₂.vm, fun a ha => (h₂.mem a ha).trans (h₁.mem a ha)⟩

theorem ZOK.of_keep {b : Addr} {z z' : State} (hz : ZOK b z) (hk : ZKeep b z z') : ZOK b z' where
  rdi := by rw [vm_gpr' hk.vm]; exact hz.rdi
  wr := by rw [vm_wr' hk.vm]; exact hz.wr
  nowrap := hz.nowrap
  masks sel hs i hi := by
    rw [← hz.masks sel hs i hi]
    refine congrArg (fun (v : BitVec 512) => v.extractLsb' (128 * i) 128) ?_
    refine Mem.readW_congr fun j hj => hk.mem _ ?_
    have hm : ∀ sel ∈ blendSels, ZMASK ≤ maskRow sel ∧ maskRow sel + 64 ≤ 6016 := by decide +kernel
    have := hm sel hs
    rw [Offset.add_ofNat_add_ofNat, off_ofNat _ (by omega_arith)]
    simp only [InZ]; omega_arith

theorem ea_sc' {z : State} {b : Addr} (h : z.gpr .rdi = b) (d : Nat) : z.ea (sc d) = b + BitVec.ofNat 64 d := by
  simp only [State.ea, sc, VG.Impl.X25519.X86_64.at_, BitVec.ofInt_natCast, h]

theorem runBlock_one {i : Instr} {z z' : State} (h : exec i z = some z') : runBlock isa [i] z = some z' := by
  rw [runBlock_cons, h, runStep_some, runBlock_nil]

theorem runBlock_two {i j : Instr} {z z₁ z₂ : State} (h₁ : exec i z = some z₁) (h₂ : exec j z₁ = some z₂) :
    runBlock isa [i, j] z = some z₂ := by
  rw [runBlock_cons, h₁, runStep_some, runBlock_one h₂]

theorem runBlock_three {i j k : Instr} {z z₁ z₂ z₃ : State} (h₁ : exec i z = some z₁)
    (h₂ : exec j z₁ = some z₂) (h₃ : exec k z₂ = some z₃) : runBlock isa [i, j, k] z = some z₃ := by
  rw [runBlock_cons, h₁, runStep_some, runBlock_two h₂ h₃]

theorem zop_keep (b : Addr) (o : ZOp) (z : State) : ZKeep b z (o.exec z) :=
  ⟨by cases o <;> rfl, fun _ _ => by rw [ZOp.exec_mem]⟩

/-- A `ymm` result `lo, hi` to `d`, and the same to half `h` of `zmm d`: the halves stay related,
but for the registers of `J'`. -/
theorem rel_write {b : Addr} {h : Nat} {J J' : List Nat} {z y z' : State} (hr : Rel b h J z y)
    (hk : ZKeep b z z') (hm : z'.mem = z.mem) {d : XReg} {lo hi : BitVec 128}
    (hJ : ∀ r, xi r ∉ J' → r ≠ d → xi r ∉ J)
    (hl : ∀ r, r ≠ d → xi r ∉ J' → ∀ k < 2, z'.zlane r (2 * h + k) = z.zlane r (2 * h + k))
    (h0 : z'.zlane d (2 * h) = lo) (h1 : z'.zlane d (2 * h + 1) = hi) :
    Rel b h J' z' (y.setV .l256 d lo hi) where
  xmm r hj := by
    simp only [State.setV]
    split
    next e => rw [e]; exact h0.symm
    next hrd =>
      have e := hl r hrd hj 0 (by decide)
      rw [Nat.add_zero] at e
      rw [hr.xmm r (hJ r hj hrd), e]
  hi r hj := by
    simp only [State.setV]
    split
    next e => rw [e]; exact h1.symm
    next hrd => rw [hr.hi r (hJ r hj hrd), hl r hrd hj 1 (by decide)]
  gpr := by rw [vm_gpr' hk.vm]; exact hr.gpr
  rd := by rw [vm_rd' hk.vm]; exact hr.rd
  wr := by rw [vm_wr' hk.vm]; exact hr.wr
  mem a ha := by rw [hm]; exact hr.mem a ha

theorem jw_J {J : List Nat} {d : XReg} : ∀ r, xi r ∉ jw J d → r ≠ d → xi r ∉ J :=
  fun _ h hd => not_mem_jw h hd

/-- A lane-wise `zmm` operation and its `ymm` one. -/
theorem sim_lanewise {b : Addr} {J : List Nat} {d : XReg} {z : State} {o : ZOp} {v : VOp}
    {F : (XReg → Nat → BitVec 128) → Nat → BitVec 128}
    (hz : ∀ r i, i < 4 → (o.exec z).zlane r i = if r = d then F z.zlane i else z.zlane r i)
    (hv : ∀ y : State, v.exec y = y.setV .l256 d (F (fun r k => y.lane r k) 0) (F (fun r k => y.lane r k) 1))
    (hF : ∀ h < 2, ∀ y, Rel b h J z y → ∀ k < 2, F (fun r k => y.lane r k) k = F z.zlane (2 * h + k)) :
    ∀ h < 2, ∀ y y', Rel b h J z y → exec (.vop v) y = some y' → Rel b h (jw J d) (o.exec z) y' := by
  intro h hh y y' hr e
  simp only [exec, Option.some.injEq] at e
  subst e
  rw [hv]
  refine rel_write hr (zop_keep b o z) (ZOp.exec_mem o z) jw_J (fun r hrd _ k hk => ?_)
    ?_ ?_
  · rw [hz r _ (by omega_arith), ite_eq_right hrd]
  · have e := hF h hh y hr 0 (by decide)
    rw [Nat.add_zero] at e
    rw [hz d _ (by omega_arith), ite_eq_left rfl, e]
  · rw [hz d _ (by omega_arith), ite_eq_left rfl, hF h hh y hr 1 (by decide)]

/-! ## Rows of the window -/

/-- A row of the window, at its offset. -/
def RowAt (o : Nat) : Prop := 1024 ≤ o ∧ o + 32 ≤ 1792 ∧ (o - 1024) % 32 = 0

instance (o : Nat) : Decidable (RowAt o) := by unfold RowAt; infer_instance

theorem rowOk_iff {m : MemOp} (h : rowOk m = true) : ∃ o, rdiOff m = some o ∧ RowAt o := by
  unfold rowOk at h
  split at h
  · rename_i o ho; exact ⟨o, ho, of_decide_eq_true h⟩
  · cases h

theorem zmem_ea {m : MemOp} {o : Nat} (h : rdiOff m = some o) (ho : 1024 ≤ o) (s : State) :
    s.ea (zmem m) = s.gpr .rdi + BitVec.ofNat 64 (zrow o) := by
  unfold rdiOff at h
  split at h
  · rename_i hb
    split at h
    · rename_i n hn
      cases h
      have e : ((ZB : Int) + 2 * (Int.ofNat o - 1024)) = ((zrow o : Nat) : Int) := by
        unfold zrow; rw [Int.ofNat_eq_natCast]; omega_arith
      simp only [State.ea, zmem, hb.1, hb.2, hn, e, BitVec.ofInt_natCast]
    · cases h
  · cases h

/-- The bytes of a row as half `h` sees them. -/
theorem win_byte {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y) {o : Nat}
    (ho : RowAt o) {j : Nat} (hj : j < 32) :
    y.mem (b + BitVec.ofNat 64 (o + j)) = z.mem (b + BitVec.ofNat 64 (zrow o + 32 * h + j)) := by
  obtain ⟨h1, h2, h3⟩ := ho
  rw [hr.mem _ (by rw [off_ofNat _ (by omega_arith)]; unfold InZ ZB; omega_arith), hmem,
    off_ofNat _ (by omega_arith), ite_eq_left (by simp only [InWin]; omega_arith)]
  refine congrArg z.mem (congrArg (b + ·) (congrArg (BitVec.ofNat 64) ?_))
  unfold zoff zrow
  omega_arith

theorem read_congr2 {m m' : Mem} {a a' : Addr} {n : Nat}
    (h : ∀ i < n, m (a + BitVec.ofNat 64 i) = m' (a' + BitVec.ofNat 64 i)) :
    m.read a n = m'.read a' n := by
  induction n generalizing a a' with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega_arith)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih fun i hi => ?_]
    have := h (i + 1) (by omega_arith)
    rwa [Offset.add_ofNat_succ, Offset.add_ofNat_succ] at this

theorem readW_congr2 {m m' : Mem} {a a' : Addr} {w : Nat}
    (h : ∀ i < w / 8, m (a + BitVec.ofNat 64 i) = m' (a' + BitVec.ofNat 64 i)) :
    m.readW a w = m'.readW a' w := by
  simp only [Mem.readW, read_congr2 h]

/-- A load of a row, as half `h` sees it. -/
theorem win_read {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y) (hh : h < 2)
    {o : Nat} (ho : RowAt o) {k : Nat} (hk : k < 2) :
    (z.mem.readW (b + BitVec.ofNat 64 (zrow o)) 512).extractLsb' (128 * (2 * h + k)) 128 =
      (y.mem.readW (b + BitVec.ofNat 64 o) 256).extractLsb' (128 * k) 128 := by
  have e₁ := readW_extract z.mem (b + BitVec.ofNat 64 (zrow o)) (w := 512) (k := 16 * (2 * h + k))
    (n := 16) (by omega_arith)
  have e₂ := readW_extract y.mem (b + BitVec.ofNat 64 o) (w := 256) (k := 16 * k) (n := 16) (by omega_arith)
  rw [show 8 * (16 * (2 * h + k)) = 128 * (2 * h + k) by omega_arith] at e₁
  rw [show 8 * (16 * k) = 128 * k by omega_arith] at e₂
  rw [e₁, e₂]
  refine (readW_congr2 fun j hj => ?_).symm
  simp only [Offset.add_ofNat_add_ofNat]
  rw [Nat.add_assoc, win_byte hr ho (j := 16 * k + j) (by omega_arith)]
  refine congrArg z.mem (congrArg (b + ·) (congrArg (BitVec.ofNat 64) ?_))
  omega_arith

/-- Byte `j` of half `h` of a `zmm` register. -/
theorem zmm_byte (s : State) (r : XReg) {h j : Nat} (hh : h < 2) (hj : j < 32) :
    (s.zmm r).extractLsb' (8 * (32 * h + j)) 8 =
      (s.zlane r (2 * h + 1) ++ s.zlane r (2 * h)).extractLsb' (8 * j) 8 := by
  rw [← zmm_half s r hh]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    decide_eq_true (show 8 * j + i < 256 by omega_arith)]
  congr 1; omega_arith

/-- The bytes of a written row, as half `h` sees them. -/
theorem win_write {b : Addr} {h : Nat} {J : List Nat} {z y : State} (hr : Rel b h J z y) (hh : h < 2)
    {o : Nat} (ho : RowAt o) {r : XReg} (hf : xi r ∉ J) (a : Addr)
    (ha : ¬ InZ (a - b).toNat) :
    (y.mem.writeW (b + BitVec.ofNat 64 o) (y.ymm r)) a =
      hmem b h (z.mem.writeW (b + BitVec.ofNat 64 (zrow o)) (z.zmm r)) a := by
  obtain ⟨h1, h2, h3⟩ := ho
  have hx := (a - b).isLt
  simp only [Mem.writeW, Mem.write, hmem]
  rw [sub_off]
  generalize hxd : (a - b).toNat = x at *
  by_cases hin : o ≤ x ∧ x < o + 32
  · have hz : zrow o ≤ zoff h x ∧ zoff h x < zrow o + 64 := by
      unfold zoff zrow; omega_arith
    rw [ite_eq_left (by omega_arith), ite_eq_left (by simp only [InWin]; omega_arith), Offset.add_sub_add_left,
      Offset.ofNat_sub_ofNat hz.1, BitVec.toNat_ofNat, ite_eq_left (by omega_arith)]
    have e : (2 ^ 64 - o % 2 ^ 64 + x) % 2 ^ 64 = x - o := by omega_arith
    have e' : (zoff h x - zrow o) % 2 ^ 64 = 32 * h + (x - o) := by
      unfold zoff zrow; omega_arith
    rw [e, e']
    simp only [BitVec.setWidth_eq]
    rw [zmm_byte z r hh (by omega_arith), State.ymm, ← hr.hi r hf, ← hr.xmm r hf]
  · rw [ite_eq_right (by omega_arith), hr.mem a (hxd ▸ ha), hmem, hxd]
    split
    · rename_i hw
      rw [Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        ite_eq_right]
      simp only [InWin] at hw
      unfold zoff zrow
      omega_arith
    · simp only [InZ] at ha
      rw [sub_off, ite_eq_right (by unfold zrow at *; unfold ZB ZMASK at *; omega_arith)]

/-! ## Each instruction -/

theorem zrow_in {o : Nat} (ho : RowAt o) : ZB ≤ zrow o ∧ zrow o + 64 ≤ ZMASK := by
  obtain ⟨h1, h2, h3⟩ := ho; unfold zrow ZB ZMASK; omega_arith

theorem scratch_in {b : Addr} {z : State} (hz : ZOK b z) {d : Nat} (hd : d + 64 ≤ 8192) :
    InRegions z.wr (b + BitVec.ofNat 64 d) 64 :=
  ⟨_, hz.wr, Offset.contains_base b hd (by omega_arith)⟩

theorem setZ_keep (b : Addr) (z : State) (d : XReg) (l0 l1 l2 l3 : BitVec 128) :
    ZKeep b z (z.setZ d l0 l1 l2 l3) := ⟨rfl, fun _ _ => rfl⟩

/-- A load of a row. -/
theorem sim_load {b : Addr} {t : Nat} {J : List Nat} {d : XReg} {m : MemOp} (hm : rowOk m = true)
    {z : State} (hz : ZOK b z) :
    ∃ z', runBlock isa (toZ t (.vmovdquLoad .l256 d m)) z = some z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∀ y y', Rel b h J z y → exec (.vmovdquLoad .l256 d m) y = some y' →
        Rel b h (jw J d) z' y' := by
  obtain ⟨o, ho, hr⟩ := rowOk_iff hm
  have ea : z.ea (zmem m) = b + BitVec.ofNat 64 (zrow o) := by rw [zmem_ea ho hr.1, hz.rdi]
  have hin : InRegions (z.rd ++ z.wr) (b + BitVec.ofNat 64 (zrow o)) 64 := by
    obtain ⟨r, hr', hc⟩ := scratch_in hz (d := zrow o) (by have := zrow_in hr; unfold ZMASK at this; omega_arith)
    exact ⟨r, List.mem_append_right _ hr', hc⟩
  let w := z.mem.readW (b + BitVec.ofNat 64 (zrow o)) 512
  refine ⟨z.setZ d (w.extractLsb' 0 128) (w.extractLsb' 128 128) (w.extractLsb' 256 128)
    (w.extractLsb' 384 128), runBlock_one ?_, setZ_keep b z d _ _ _ _, ?_⟩
  · simp only [exec, ea, State.load512, hin, ite_true, Option.map_some]; rfl
  intro h hh y y' hy e
  have eay : y.ea m = b + BitVec.ofNat 64 o := by rw [rdiOff_ok ho, hy.gpr, hz.rdi]
  simp only [exec, eay, State.load256] at e
  split at e
  case isFalse => cases e
  simp only [Option.map_some, Option.some.injEq] at e
  subst e
  have r0 := win_read hy hh hr (k := 0) (by decide)
  have r1 := win_read hy hh hr (k := 1) (by decide)
  rw [Nat.add_zero, Nat.mul_zero] at r0
  rw [Nat.mul_one] at r1
  refine rel_write hy (setZ_keep b z d _ _ _ _) rfl jw_J (fun r hrd _ k hk => ?_) ?_ ?_
  · rw [zlane_load _ _ _ _ (by omega_arith), ite_eq_right hrd]
  · rw [zlane_load _ _ _ _ (by omega_arith), ite_eq_left rfl]; exact r0
  · rw [zlane_load _ _ _ _ (by omega_arith), ite_eq_left rfl]; exact r1

/-- A store of a row. -/
theorem sim_store {b : Addr} {t : Nat} {J : List Nat} {r : XReg} {m : MemOp} (hm : rowOk m = true)
    (hf : xi r ∉ J) {z : State} (hz : ZOK b z) :
    ∃ z', runBlock isa (toZ t (.vmovdquStore .l256 m r)) z = some z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∀ y y', Rel b h J z y → exec (.vmovdquStore .l256 m r) y = some y' → Rel b h J z' y' := by
  obtain ⟨o, ho, hr⟩ := rowOk_iff hm
  have ea : z.ea (zmem m) = b + BitVec.ofNat 64 (zrow o) := by rw [zmem_ea ho hr.1, hz.rdi]
  have zi := zrow_in hr
  have hin : InRegions z.wr (b + BitVec.ofNat 64 (zrow o)) 64 :=
    scratch_in hz (d := zrow o) (by unfold ZMASK at zi; omega_arith)
  refine ⟨z.setMem (z.mem.writeW (b + BitVec.ofNat 64 (zrow o)) (z.zmm r)), runBlock_one ?_, ⟨rfl, ?_⟩, ?_⟩
  · simp only [exec, ea, State.store512_eq, hin, ite_true]
  · intro a ha
    simp only [State.setMem, Mem.writeW, Mem.write]
    rw [sub_off, ite_eq_right]
    have := (a - b).isLt
    unfold InZ at ha
    unfold ZB ZMASK at ha zi
    omega_arith
  intro h hh y y' hy e
  have eay : y.ea m = b + BitVec.ofNat 64 o := by rw [rdiOff_ok ho, hy.gpr, hz.rdi]
  simp only [exec, eay, State.store256] at e
  split at e
  case isFalse => cases e
  simp only [Option.some.injEq] at e
  subst e
  exact ⟨fun r' hr' => by rw [hy.xmm r' hr']; rfl, fun r' hr' => by rw [hy.hi r' hr']; rfl, hy.gpr, hy.rd,
    hy.wr, fun a ha => win_write hy hh hr hf a ha⟩

theorem xi_y {t : Nat} (ht : t < 16) : xi (y t) = t := by
  have e : ∀ t < 16, xi (y t) = t := by decide
  exact e t ht

/-- A blend, through the free register `y t`. -/
theorem sim_blend {b : Addr} {t : Nat} {J : List Nat} {d a c : XReg} {sel : BitVec 8} (ht : t < 16)
    (ha : xi a ≠ t) (hc : xi c ≠ t) (hfa : xi a ∉ J) (hfc : xi c ∉ J) (hs : sel ∈ blendSels)
    {z : State} (hz : ZOK b z) :
    ∃ z', runBlock isa (toZ t (.vop (.vpblendd .l256 d a c sel))) z = some z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∀ y' y'', Rel b h J z y' → exec (.vop (.vpblendd .l256 d a c sel)) y' = some y'' →
        Rel b h (if xi d = t then jw J d else t :: jw J d) z' y'' := by
  have hT := xi_y ht
  have hm : ∀ sel ∈ blendSels, maskRow sel + 64 ≤ 8192 := by decide +kernel
  have hin : InRegions (z.rd ++ z.wr) (b + BitVec.ofNat 64 (maskRow sel)) 64 := by
    obtain ⟨r, hr', hc'⟩ := scratch_in hz (hm sel hs)
    exact ⟨r, List.mem_append_right _ hr', hc'⟩
  have haT : a ≠ y t := fun e => ha (by rw [e, hT])
  have hcT : c ≠ y t := fun e => hc (by rw [e, hT])
  let w := z.mem.readW (b + BitVec.ofNat 64 (maskRow sel)) 512
  let z₁ := z.setZ (y t) (w.extractLsb' 0 128) (w.extractLsb' 128 128) (w.extractLsb' 256 128)
    (w.extractLsb' 384 128)
  let z₂ := (ZOp.vpternlogd (y t) a c 0xAC).exec z₁
  let z₃ := (ZOp.vmovdqa64 d (y t)).exec z₂
  have L : ∀ r i, i < 4 → z₃.zlane r i =
      if r = d ∨ r = y t then blendDwords (z.zlane a i) (z.zlane c i) (sel.extractLsb' (4 * (i % 2)) 4)
      else z.zlane r i := by
    intro r i hi
    simp only [z₃, z₂, z₁, zlane_vmovdqa64 _ _ _ _ hi, zlane_vpternlogd _ _ _ _ _ _ hi, zlane_load _ _ _ _ hi,
      ite_true, haT, hcT, ite_false]
    rw [hz.masks sel hs i hi, ternlog_AC]
    by_cases h1 : r = d <;> by_cases h2 : r = y t <;> simp [h1, h2]
  refine ⟨z₃, runBlock_three ?_ rfl rfl,
    (setZ_keep b z _ _ _ _ _).trans ((zop_keep b _ _).trans (zop_keep b _ _)), ?_⟩
  · simp only [exec, ea_sc' hz.rdi, State.load512, hin, ite_true, Option.map_some]; rfl
  intro h hh y' y'' hy e
  simp only [exec, Option.some.injEq] at e
  subst e
  refine rel_write hy ((setZ_keep b z _ _ _ _ _).trans ((zop_keep b _ _).trans (zop_keep b _ _))) rfl
    (fun r hr hrd => ?_) (fun r hrd hr k hk => ?_) ?_ ?_
  · by_cases hd : xi d = t
    · rw [ite_eq_left hd] at hr; exact jw_J r hr hrd
    · rw [ite_eq_right hd] at hr; exact jw_J r (fun h' => hr (List.mem_cons_of_mem _ h')) hrd
  · have hrT : r ≠ y t := by
      intro e
      by_cases hd : xi d = t
      · exact hrd (xi_inj.1 (by rw [e, hT, hd]))
      · rw [ite_eq_right hd, e, hT] at hr; exact hr (List.mem_cons_self ..)
    rw [L r _ (by omega_arith), ite_eq_right (fun h' => h'.elim hrd hrT)]
  · rw [L d _ (by omega_arith), ite_eq_left (Or.inl rfl), hy.lane hfa (k := 0) (by decide),
      hy.lane hfc (k := 0) (by decide), Nat.add_zero]
    simp only [Nat.mul_mod_right, Nat.mul_zero]
  · rw [L d _ (by omega_arith), ite_eq_left (Or.inl rfl), hy.lane hfa (k := 1) (by decide),
      hy.lane hfc (k := 1) (by decide)]
    simp only [show (2 * h + 1) % 2 = 1 by omega_arith, Nat.mul_one]

theorem perm2Lanes_congr {a a' c c' : Nat → BitVec 128} (ha : ∀ k < 2, a k = a' k) (hc : ∀ k < 2, c k = c' k)
    (sel : BitVec 8) (j : Nat) : perm2Lanes a c sel j = perm2Lanes a' c' sel j := by
  simp only [perm2Lanes]
  rw [ha _ (Nat.mod_lt _ (by decide)), hc _ (Nat.mod_lt _ (by decide))]

/-- `vperm2i128` with `0x20` or `0x31`, as two `vshufi32x4`. -/
theorem sim_perm2 {b : Addr} {t : Nat} {J : List Nat} {d a c : XReg} {sel : BitVec 8}
    (hsel : sel = 0x20 ∨ sel = 0x31) (hfa : xi a ∉ J) (hfc : xi c ∉ J) (z : State) :
    ∃ z', runBlock isa (toZ t (.vop (.vperm2i128 d a c sel))) z = some z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∀ y' y'', Rel b h J z y' → exec (.vop (.vperm2i128 d a c sel)) y' = some y'' →
        Rel b h (jw J d) z' y'' := by
  have key : ∀ h < 2, ∀ k < 2, ((ZOp.vshufi32x4 d d d 0xD8).exec ((ZOp.vshufi32x4 d a c
      (if sel = 0x31 then 0xDD else 0x88)).exec z)).zlane d (2 * h + k) =
      perm2Lanes (fun k => z.zlane a (2 * h + k)) (fun k => z.zlane c (2 * h + k)) sel k := by
    intro h hh k hk
    rcases hsel with rfl | rfl <;> rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl <;>
      rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl <;>
      simp [zlane_vshufi32x4, shuf4Lanes, perm2Lanes]
  refine ⟨_, runBlock_two rfl rfl, (zop_keep b _ _).trans (zop_keep b _ _), ?_⟩
  intro h hh y' y'' hy e
  simp only [exec, Option.some.injEq] at e
  subst e
  have pc : ∀ k, perm2Lanes (y'.lane a) (y'.lane c) sel k =
      perm2Lanes (fun k => z.zlane a (2 * h + k)) (fun k => z.zlane c (2 * h + k)) sel k :=
    perm2Lanes_congr (fun k hk => hy.lane hfa hk) (fun k hk => hy.lane hfc hk) sel
  refine rel_write hy ((zop_keep b _ _).trans (zop_keep b _ _)) rfl jw_J (fun r hrd _ k hk => ?_) ?_ ?_
  · simp only [zlane_vshufi32x4 _ _ _ _ _ _ (show 2 * h + k < 4 by omega_arith), hrd, ite_false]
  · rw [← Nat.add_zero (2 * h), key h hh 0 (by decide), pc]
  · rw [key h hh 1 (by decide), pc]

/-- One instruction of a translated block. -/
theorem sim1 {b : Addr} {t : Nat} {J J' : List Nat} {i : Instr} (hj : jstep t J i = some J') {z : State}
    (hz : ZOK b z) :
    ∃ z', runBlock isa (toZ t i) z = some z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∀ y y', Rel b h J z y → exec i y = some y' → Rel b h J' z' y' := by
  unfold jstep at hj
  split at hj
  next op d a c =>
    split at hj
    case isFalse => cases hj
    next hc =>
    cases hj
    simp only [Bool.and_eq_true, free_iff] at hc
    obtain ⟨⟨hop, ha⟩, hc⟩ := hc
    exact ⟨_, runBlock_one rfl, zop_keep b _ z, sim_lanewise (F := fun L i => op.sse.eval (L a i) (L c i))
      (fun r i hi => by rw [zlane_zbin _ _ _ _ _ _ hi, zbin_sse hop]) (fun _ => rfl)
      (fun h hh y hr k hk => by simp only; rw [hr.lane ha hk, hr.lane hc hk])⟩
  next d a n =>
    split at hj
    case isFalse => cases hj
    next ha =>
    cases hj
    rw [free_iff] at ha
    exact ⟨_, runBlock_one rfl, zop_keep b _ z, sim_lanewise (F := fun L i => XShiftOp.psllq.eval (L a i) n)
      (fun r i hi => by rw [zlane_vshift _ _ _ _ _ _ hi]; rfl) (fun _ => rfl)
      (fun h hh y hr k hk => by simp only; rw [hr.lane ha hk])⟩
  next d a n =>
    split at hj
    case isFalse => cases hj
    next ha =>
    cases hj
    rw [free_iff] at ha
    exact ⟨_, runBlock_one rfl, zop_keep b _ z, sim_lanewise (F := fun L i => XShiftOp.psrlq.eval (L a i) n)
      (fun r i hi => by rw [zlane_vshift _ _ _ _ _ _ hi]; rfl) (fun _ => rfl)
      (fun h hh y hr k hk => by simp only; rw [hr.lane ha hk])⟩
  next d a o =>
    split at hj
    case isFalse => cases hj
    next ha =>
    cases hj
    rw [free_iff] at ha
    refine ⟨_, runBlock_one rfl, zop_keep b _ z, sim_lanewise
      (F := fun L i => (permQwords (L a (2 * (i / 2) + 1) ++ L a (2 * (i / 2))) o).extractLsb' (128 * (i % 2)) 128)
      (fun r i hi => ?_) (fun _ => rfl) (fun h hh y hr k hk => ?_)⟩
    · have e := zlane_vpermq d a o z r (h := i / 2) (k := i % 2) (by omega_arith) (by omega_arith)
      rw [show 2 * (i / 2) + i % 2 = i by omega_arith] at e
      exact e
    · simp only [show k / 2 = 0 by omega_arith, show (2 * h + k) / 2 = h by omega_arith, show (2 * h + k) % 2 = k by omega_arith,
        show k % 2 = k by omega_arith, Nat.mul_zero, Nat.zero_add]
      rw [hr.lane ha (k := 1) (by decide), show y.lane a 0 = z.zlane a (2 * h) from hr.xmm a ha]
  next d a c =>
    split at hj
    case isFalse => cases hj
    next hc =>
    cases hj
    simp only [Bool.and_eq_true, free_iff] at hc
    obtain ⟨⟨hd, ha⟩, hc⟩ := hc
    exact ⟨_, runBlock_one rfl, zop_keep b _ z,
      sim_lanewise (F := fun L i => madd52 false (L d i) (L a i) (L c i))
      (fun r i hi => by rw [zlane_vpmadd52 _ _ _ _ _ _ hi]) (fun _ => rfl)
      (fun h hh y hr k hk => by simp only; rw [hr.lane hd hk, hr.lane ha hk, hr.lane hc hk])⟩
  next d a c =>
    split at hj
    case isFalse => cases hj
    next hc =>
    cases hj
    simp only [Bool.and_eq_true, free_iff] at hc
    obtain ⟨⟨hd, ha⟩, hc⟩ := hc
    exact ⟨_, runBlock_one rfl, zop_keep b _ z,
      sim_lanewise (F := fun L i => madd52 true (L d i) (L a i) (L c i))
      (fun r i hi => by rw [zlane_vpmadd52 _ _ _ _ _ _ hi]) (fun _ => rfl)
      (fun h hh y hr k hk => by simp only; rw [hr.lane hd hk, hr.lane ha hk, hr.lane hc hk])⟩
  next d a =>
    split at hj
    case isFalse => cases hj
    next ha =>
    cases hj
    rw [free_iff] at ha
    exact ⟨_, runBlock_one rfl, zop_keep b _ z, sim_lanewise (F := fun L i => L a i)
      (fun r i hi => by rw [zlane_vmovdqa64 _ _ _ _ hi]) (fun _ => rfl)
      (fun h hh y hr k hk => by simp only; rw [hr.lane ha hk])⟩
  next d a c sel =>
    split at hj
    case isFalse => cases hj
    next hc =>
    cases hj
    simp only [Bool.and_eq_true, free_iff, decide_eq_true_eq, bne_iff_ne, ne_eq, List.contains_iff_mem]
      at hc
    obtain ⟨⟨⟨⟨⟨ha, hc'⟩, ht⟩, hat⟩, hct⟩, hs⟩ := hc
    exact sim_blend ht hat hct ha hc' hs hz
  next d a c sel =>
    split at hj
    case isFalse => cases hj
    next hc =>
    cases hj
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, free_iff] at hc
    obtain ⟨⟨hs, ha⟩, hc⟩ := hc
    exact sim_perm2 hs ha hc z
  next d m =>
    split at hj
    case isFalse => cases hj
    next hm =>
    cases hj
    exact sim_load hm hz
  next m r =>
    split at hj
    case isFalse => cases hj
    next hm =>
    cases hj
    simp only [Bool.and_eq_true, free_iff] at hm
    exact sim_store hm.1 hm.2 hz
  · cases hj

/-! ## Blocks -/

/-- A translated block: if the `ymm` block, from states related to the halves, ends in `Q h`,
the `zmm` block ends in a state whose halves are related to states satisfying `Q h`. -/
theorem sim_run {b : Addr} {t : Nat} : ∀ (is : List Instr) {J J' : List Nat}, junk t J is = some J' →
    ∀ {z : State}, ZOK b z → ∀ {Q : Nat → State → Prop},
      (∀ h < 2, ∃ y, Rel b h J z y ∧ WP isa (.block is) y (Q h)) →
      WP isa (.block (tzs t is)) z fun z' => ZOK b z' ∧ ZKeep b z z' ∧
        ∀ h < 2, ∃ y, Rel b h J' z' y ∧ Q h y
  | [], J, J', hj, z, hz, Q, hy => by
    simp only [junk, Option.some.injEq] at hj
    subst hj
    exact WP.block_nil ⟨hz, ZKeep.refl b z, fun h hh => by
      obtain ⟨y, hr, hw⟩ := hy h hh
      exact ⟨y, hr, WP.block_nil_iff.1 hw⟩⟩
  | i :: is, J, J', hj, z, hz, Q, hy => by
    simp only [junk, Option.bind_eq_some_iff] at hj
    obtain ⟨J₁, hj₁, hj₂⟩ := hj
    obtain ⟨z₁, hz₁, hk₁, hr₁⟩ := sim1 hj₁ hz
    rw [tzs, List.flatMap_cons, WP.block_append_iff]
    refine WP.of_runBlock ⟨z₁, hz₁, ?_⟩
    refine WP.mono (sim_run is hj₂ (hz.of_keep hk₁) fun h hh => ?_) fun z' ⟨o, k, r⟩ => ⟨o, hk₁.trans k, r⟩
    obtain ⟨y, hr, hw⟩ := hy h hh
    obtain ⟨y₁, e, hw₁⟩ := WP.block_cons_iff.1 hw
    exact ⟨y₁, hr₁ h hh y y₁ hr e, hw₁⟩

/-- `sim_run` from the halves themselves. -/
theorem sim_wp {b : Addr} {t : Nat} {is : List Instr} {J' : List Nat} (hj : junk t [] is = some J')
    {z : State} (hz : ZOK b z) {Q : Nat → State → Prop} (hy : ∀ h < 2, WP isa (.block is) (half b h z) (Q h)) :
    WP isa (.block (tzs t is)) z fun z' => ZOK b z' ∧ ZKeep b z z' ∧
      ∀ h < 2, ∃ y, Rel b h J' z' y ∧ Q h y :=
  sim_run is hj hz fun h hh => ⟨_, Rel.half b h [] z, hy h hh⟩

end VG.Proof.Ed25519.X86_64.Zmm

end

end

/-!
# The `zmm` comb: the selection

`zselect` keeps each 32-byte piece of each entry of a table, loaded once into
both halves of `zmm10`, under the mask of each half's magnitude (`r8` for half
0, `r10` for half 1) in `zmm11–zmm13`, as `vselect` does in one half: half `h`
then holds the words of the entry for its magnitude, or zero (`accQ`), with
the identity's `1`s or'd in for a zero magnitude, and `zmm14` holds the row
`ZK2`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Zmm

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Zmm VG.Proof.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (sc)
open VG.Impl.X25519.X86_64.Ifma (y v zero)
open VG.Proof.Ed25519.X86_64.Ifma (accQ accQ_step)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw qword_and qword_or qword_app0 qword_app1 qword256_eq)

/-- Quadword `k` (of four) of half `h` of `zmm r`. -/
def zq (s : State) (r : XReg) (h k : Nat) : BitVec 64 := qword (s.zlane r (2 * h + k / 2)) (k % 2)

/-- What a block keeps of the rest of the state: the general-purpose registers but `rs`, the
memory, the regions and the statics, and the vector registers but those of `xs`. -/
structure ZVKeep (rs : List Reg) (xs : XReg → Prop) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  zl : ∀ r, ¬ xs r → ∀ i < 4, t.zlane r i = s.zlane r i
  syms : t.syms = s.syms

theorem ZVKeep.refl (rs : List Reg) (xs : XReg → Prop) (s : State) : ZVKeep rs xs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl, rfl⟩

theorem ZVKeep.trans {rs : List Reg} {xs : XReg → Prop} {s₁ s₂ s₃ : State} (h₁ : ZVKeep rs xs s₁ s₂)
    (h₂ : ZVKeep rs xs s₂ s₃) : ZVKeep rs xs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, fun r hr i hi => (h₂.zl r hr i hi).trans (h₁.zl r hr i hi), h₂.syms.trans h₁.syms⟩

theorem ZVKeep.mono {rs rs' : List Reg} {xs xs' : XReg → Prop} {s t : State} (h : ZVKeep rs xs s t)
    (hr : ∀ r ∈ rs, r ∈ rs') (hx : ∀ r, xs r → xs' r) : ZVKeep rs' xs' s t :=
  ⟨fun r h' => h.gpr r fun h'' => h' (hr r h''), h.mem, h.rd, h.wr,
    fun r h' => h.zl r fun h'' => h' (hx r h''), h.syms⟩

theorem zlane_of {s t : State} (hx : t.xmm = s.xmm) (hy : t.ymmHi = s.ymmHi) (hz : t.zmmHi = s.zmmHi)
    (r : XReg) (i : Nat) : t.zlane r i = s.zlane r i := by
  simp only [State.zlane, State.lane, hx, hy, hz]

theorem zlane_setV256 (s : State) (d r : XReg) (lo hi : BitVec 128) {i : Nat} (hi4 : i < 4) :
    (s.setV .l256 d lo hi).zlane r i = if r = d then (if i = 0 then lo else if i = 1 then hi else 0)
      else s.zlane r i := by
  simp only [State.zlane, State.lane, State.setV]
  by_cases h : r = d
  · subst h
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> simp
  · simp [h]

/-! ## The masks -/

/-- `rcx` all ones if `r10 = a` is `v`, else zero. -/
theorem eqMaskB_ok (s : State) {v a : Nat} (hv : v < 2 ^ 31) (ha : a < 2 ^ 31)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 a) :
    WP isa (.block (eqMaskB v)) s fun t => t.gpr .rcx = cmask (decide (a = v)) ∧
      Proof.X25519.X86_64.Keeps [.rcx] s t ∧ t.syms = s.syms := by
  erun [eqMaskB, imm32_ofNat hv, h10]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩
  · have h1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := by decide
    obtain hx : decide ((BitVec.ofNat 64 v ^^^ BitVec.ofNat 64 a).toNat < 1) = decide (a = v) := by
      refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
      · have e0 : BitVec.ofNat 64 v ^^^ BitVec.ofNat 64 a = 0 :=
          BitVec.eq_of_toNat_eq ((Nat.lt_one_iff.mp h).trans rfl)
        obtain e := BitVec.xor_eq_zero_iff.mp e0
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        omega_arith
      · subst h; rw [BitVec.xor_self, BitVec.toNat_zero]; decide
    rw [BitVec.sub_self, h1, hx]
    cases decide (a = v) <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- A scalar block's facts, with the vector registers kept. -/
theorem zscal {c : Prog isa} (hc : scalCode c = true) {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ ∀ r i, t.zlane r i = s.zlane r i :=
  WP.mono (WP.zvecKeep hc h) fun _ ⟨q, x, y, z⟩ => ⟨q, zlane_of x y z⟩

/-- `vmovq` and `vpbroadcastq`: a general-purpose register in every quadword of `zmm d`. -/
theorem zlane_dup (s : State) (d : XReg) (g : Reg) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vpbroadcastq d d).exec ((VOp.vmovq d g).exec s)).zlane r i =
      if r = d then s.gpr g ++ s.gpr g else s.zlane r i := by
  rw [zlane_vpbroadcastq _ _ _ _ hi]
  split
  · subst_vars; simp only [VOp.exec, State.setV, ite_true, qword_app0]
  · simp only [VOp.exec, State.zlane_setV128 _ _ _ _ _ hi]; rw [ite_eq_right (by assumption)]

/-- `zlo d a b`: the low halves of `zmm a` and `zmm b`. -/
theorem zlane_zlo (s : State) (d a b : Nat) (r : XReg) {i : Nat} (hi : i < 4) :
    ((ZOp.vshufi32x4 (y d) (y a) (y b) 0x44).exec s).zlane r i =
      if r = y d then (if i < 2 then s.zlane (y a) i else s.zlane (y b) (i - 2)) else s.zlane r i := by
  rw [zlane_vshufi32x4 _ _ _ _ _ _ hi]
  split
  · rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rfl

theorem combEqMask_scal (m : Nat) : scalCode (.block (combEqMask m)) = true := rfl
theorem eqMaskB_scal (m : Nat) : scalCode (.block (eqMaskB m)) = true := rfl

/-- Both masks: `zmm15` all ones in half 0 if `r8 = a` is `m`, and in half 1 if `r10 = b` is. -/
theorem zmasks_ok (s : State) {a b m : Nat} (hm : m < 2 ^ 31) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (h10 : s.gpr .r10 = BitVec.ofNat 64 b) :
    WP isa (.block (combEqMask m ++ ([.vop (.vmovq (y 15) .rcx), .zop (.vpbroadcastq (y 15) (y 15))] : List Instr) ++
      eqMaskB m ++ ([.vop (.vmovq (y 14) .rcx), .zop (.vpbroadcastq (y 14) (y 14)), zlo 15 15 14] : List Instr))) s
      fun t => (∀ i < 4, t.zlane (xr 15) i = (cmask (decide ((if i < 2 then a else b) = m)) ++
          cmask (decide ((if i < 2 then a else b) = m)))) ∧
        ZVKeep [.rcx] (fun r => r = xr 14 ∨ r = xr 15) s t := by
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zscal (combEqMask_scal m) (combEqMask_ok s hm ha h8)) fun s₁ ⟨⟨c₁, k₁, _, y₁⟩, z₁⟩ => ?_
  let s₂ := (ZOp.vpbroadcastq (y 15) (y 15)).exec ((VOp.vmovq (y 15) .rcx).exec s₁)
  refine WP.of_runBlock ⟨s₂, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  obtain l₂ : ∀ r, ∀ i < 4, s₂.zlane r i = if r = y 15 then cmask (decide (a = m)) ++ cmask (decide (a = m))
      else s₁.zlane r i := fun r i hi => by rw [zlane_dup _ _ _ _ hi, c₁]
  refine WP.mono (zscal (eqMaskB_scal m) (eqMaskB_ok s₂ hm hb (by
    show s₁.gpr .r10 = _; rw [k₁.1 _ (by decide), h10]))) fun s₃ ⟨⟨c₃, k₃, y₃⟩, z₃⟩ => ?_
  let s₄ := (ZOp.vshufi32x4 (y 15) (y 15) (y 14) 0x44).exec
    ((ZOp.vpbroadcastq (y 14) (y 14)).exec ((VOp.vmovq (y 14) .rcx).exec s₃))
  refine WP.of_runBlock ⟨s₄, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, zlo]; rfl, ?_⟩
  obtain l₄ : ∀ r, ∀ i < 4, s₄.zlane r i = if r = y 15 then
      (if i < 2 then cmask (decide (a = m)) ++ cmask (decide (a = m))
        else cmask (decide (b = m)) ++ cmask (decide (b = m)))
      else if r = y 14 then cmask (decide (b = m)) ++ cmask (decide (b = m)) else s₁.zlane r i := by
    intro r i hi
    simp only [s₄, zlane_zlo _ _ _ _ _ hi, zlane_dup _ _ _ _ hi, zlane_dup _ _ _ _ (show i - 2 < 4 by omega_arith),
      z₃, l₂ _ _ hi, c₃]
    obtain n1514 : y 15 ≠ y 14 := by decide
    by_cases h15 : r = y 15
    · subst h15; simp only [n1514, ite_true, ite_false]
    · by_cases h14 : r = y 14
      · subst h14; simp only [n1514, n1514.symm, ite_true, ite_false]
      · simp only [h15, h14, n1514, ite_true, ite_false]
  refine ⟨fun i hi => ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr i hi => ?_, ?_⟩⟩
  · rw [show xr 15 = y 15 from rfl, l₄ _ _ hi, ite_eq_left rfl]
    split <;> rfl
  · rw [show s₄.gpr = s₃.gpr by zkeep, k₃.1 r hr, show s₂.gpr = s₁.gpr by zkeep]; exact k₁.1 r hr
  · rw [show s₄.mem = s₃.mem by zkeep, k₃.2.1, show s₂.mem = s₁.mem by zkeep]; exact k₁.2.1
  · rw [show s₄.rd = s₃.rd by zkeep, k₃.2.2.1, show s₂.rd = s₁.rd by zkeep]; exact k₁.2.2.1
  · rw [show s₄.wr = s₃.wr by zkeep, k₃.2.2.2, show s₂.wr = s₁.wr by zkeep]; exact k₁.2.2.2
  · simp only [not_or, show xr 14 = y 14 from rfl, show xr 15 = y 15 from rfl] at hr
    rw [l₄ _ _ hi, ite_eq_right hr.2, ite_eq_right hr.1, z₁]
  · rw [show s₄.syms = s₃.syms by zkeep, y₃, show s₂.syms = s₁.syms by zkeep]; exact y₁

/-! ## The pieces -/

theorem qword_load (m : Mem) (a : Addr) {k : Nat} (hk : k < 4) :
    qword ((m.readW a 256).extractLsb' (128 * (k / 2)) 128) (k % 2) = m.readW (a + BitVec.ofNat 64 (8 * k)) 64 := by
  rw [← qword256_eq, qword256, show 64 * k = 8 * (8 * k) by omega_arith]
  exact readW_extract _ _ (k := 8 * k) (n := 8) (by omega_arith)

/-- Piece `c` of the 32 bytes at `rdx + d`, in both halves, kept under the masks `zmm15` in
`zmm (11 + c)`. -/
theorem zselLoad_ok (s : State) {X : Addr} (hx : s.gpr .rdx = X) {d c : Nat} (hc : c < 3)
    (hr : InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 d) 32) :
    WP isa (.block [.vmovdquLoad .l256 (y 10) (combTblAt d), zlo 10 10 10,
        .zop (.zbin .vpandq (y 10) (y 10) (y 15)), .zop (.zbin .vporq (y (11 + c)) (y (11 + c)) (y 10))]) s
      fun t => (∀ h < 2, ∀ k < 4, zq t (xr (11 + c)) h k = zq s (xr (11 + c)) h k |||
          (s.mem.readW (X + BitVec.ofNat 64 d + BitVec.ofNat 64 (8 * k)) 64 &&& zq s (xr 15) h k)) ∧
        ZVKeep [] (fun r => r = xr 10 ∨ r = xr (11 + c)) s t := by
  let w := s.mem.readW (X + BitVec.ofNat 64 d) 256
  let s₁ := s.setV .l256 (y 10) (w.extractLsb' 0 128) (w.extractLsb' 128 128)
  let s₂ := (ZOp.vshufi32x4 (y 10) (y 10) (y 10) 0x44).exec s₁
  let s₃ := (ZOp.zbin .vpandq (y 10) (y 10) (y 15)).exec s₂
  let s₄ := (ZOp.zbin .vporq (y (11 + c)) (y (11 + c)) (y 10)).exec s₃
  obtain h1015 : y 10 ≠ y 15 := by decide
  obtain hc10 : y (11 + c) ≠ y 10 := by rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide
  obtain hc15 : y (11 + c) ≠ y 15 := by rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide
  obtain l₃ : ∀ i < 4, s₃.zlane (y 10) i = w.extractLsb' (128 * (i % 2)) 128 &&& s.zlane (y 15) i := by
    intro i hi
    simp only [s₃, s₂, s₁, zlane_zbin _ _ _ _ _ _ hi, ite_true, zlane_zlo _ _ _ _ _ hi,
      zlane_setV256 _ _ _ _ _ hi, zlane_setV256 _ _ _ _ _ (show i - 2 < 4 by omega_arith), ite_eq_right h1015.symm,
      ZBinOp.sse, XBinOp.eval]
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl
  obtain l₄ : ∀ r, ∀ i < 4, s₄.zlane r i = if r = y (11 + c) then
      s.zlane (y (11 + c)) i ||| (w.extractLsb' (128 * (i % 2)) 128 &&& s.zlane (y 15) i)
      else if r = y 10 then w.extractLsb' (128 * (i % 2)) 128 &&& s.zlane (y 15) i else s.zlane r i := by
    intro r i hi
    simp only [s₄, zlane_zbin _ _ _ _ _ _ hi]
    split
    · next e =>
      subst e
      rw [l₃ i hi]
      simp only [s₃, s₂, s₁, zlane_zbin _ _ _ _ _ _ hi, zlane_zlo _ _ _ _ _ hi, zlane_setV256 _ _ _ _ _ hi,
        hc10, ite_false, ZBinOp.sse, XBinOp.eval]
    · next e =>
      by_cases e' : r = y 10
      · subst e'; rw [l₃ i hi, ite_eq_left rfl]
      · simp only [s₃, s₂, s₁, zlane_zbin _ _ _ _ _ _ hi, zlane_zlo _ _ _ _ _ hi, zlane_setV256 _ _ _ _ _ hi,
          e', ite_false]
  obtain hea : s.ea (combTblAt d) = X + BitVec.ofNat 64 d := by rw [ea_combTblAt, hx]
  refine WP.of_runBlock ⟨s₄, ?_, fun h hh k hk => ?_, ⟨fun _ _ => by zkeep, by zkeep, by zkeep, by zkeep,
    fun r hr i hi => ?_, by zkeep⟩⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hea, State.load256, hr, ite_true,
      Option.map_some, zlo]
    rfl
  · simp only [zq]
    rw [show xr (11 + c) = y (11 + c) by rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> rfl,
      l₄ _ _ (by omega_arith), ite_eq_left rfl, qword_or, qword_and, show (2 * h + k / 2) % 2 = k / 2 by omega_arith,
      qword_load _ _ hk]
    rfl
  · simp only [not_or, show xr 10 = y 10 from rfl] at hr
    rw [l₄ _ _ hi, ite_eq_right (by
        rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> exact hr.2),
      ite_eq_right hr.1]

/-- The magnitude of half `h`. -/
abbrev hmag (a b h : Nat) : Nat := if h = 0 then a else b

/-- The pieces `c < n` of entry `m` of the table at `rdx = X` kept under the masks `zmm15`. -/
theorem zselLoads_ok {m : Nat} {X : Addr} : ∀ n ≤ 3, ∀ (s : State), s.gpr .rdx = X →
    (∀ c < 3, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 32 * c)) 32) →
    WP isa (.block ((List.range n).flatMap fun c =>
        [.vmovdquLoad .l256 (y 10) (combTblAt (combEntryBytes * (m - 1) + 32 * c)), zlo 10 10 10,
          .zop (.zbin .vpandq (y 10) (y 10) (y 15)), .zop (.zbin .vporq (y (11 + c)) (y (11 + c)) (y 10))])) s
      fun t => (∀ h < 2, ∀ c < 3, ∀ k < 4, zq t (xr (11 + c)) h k = if c < n then zq s (xr (11 + c)) h k |||
          (s.mem.readW (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 32 * c) + BitVec.ofNat 64 (8 * k)) 64 &&&
            zq s (xr 15) h k)
        else zq s (xr (11 + c)) h k) ∧
      ZVKeep [] (fun r => r = xr 10 ∨ ∃ c < 3, r = xr (11 + c)) s t
  | 0, _, s, _, _ => WP.block_nil ⟨fun h _ c _ k _ => by simp, ZVKeep.refl _ _ _⟩
  | n + 1, hn, s, hx, hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (zselLoads_ok n (by omega_arith) s hx hr) fun s₁ ⟨a₁, k₁⟩ => ?_
    obtain h15 : ∀ h < 2, ∀ k < 4, zq s₁ (xr 15) h k = zq s (xr 15) h k := fun h hh k hk => by
      simp only [zq]
      rw [k₁.zl _ (by
        rintro (h | ⟨c, hc, h⟩)
        · exact absurd h (by decide)
        · rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> exact absurd h (by decide)) _
        (by omega_arith)]
    refine WP.mono (zselLoad_ok s₁ ((k₁.gpr _ List.not_mem_nil).trans hx) (c := n) (by omega_arith)
      (by rw [k₁.rd, k₁.wr]; exact hr n (by omega_arith))) fun t ⟨a₂, k₂⟩ => ⟨fun h hh c hc k hk => ?_, ?_⟩
    · by_cases hcn : c = n
      · subst hcn
        rw [a₂ h hh k hk, a₁ h hh c hc k hk, h15 h hh k hk, k₁.mem]
        simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self]
      · have hz : ∀ i < 4, t.zlane (xr (11 + c)) i = s₁.zlane (xr (11 + c)) i := k₂.zl _ (by
          rintro (h | h)
          · rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> exact absurd h (by decide)
          · exact hcn (by
              rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
              rcases (by omega_arith : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;>
              first | rfl | exact absurd h (by decide)))
        rw [show zq t (xr (11 + c)) h k = zq s₁ (xr (11 + c)) h k by simp only [zq]; rw [hz _ (by omega_arith)],
          a₁ h hh c hc k hk]
        by_cases hlt : c < n
        · simp only [hlt, show c < n + 1 by omega_arith, ↓reduceIte]
        · simp only [hlt, show ¬ c < n + 1 by omega_arith, ↓reduceIte]
    · exact k₁.trans (k₂.mono (fun _ h => h) fun r h => by
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨n, by omega_arith, h⟩)

/-- The registers the selection writes. -/
abbrev zselRegs (r : XReg) : Prop := r = xr 10 ∨ (∃ c < 3, r = xr (11 + c)) ∨ r = xr 14 ∨ r = xr 15

/-- Entry `m` of the table at `rdx = X` kept in the accumulators of each half under the mask of
its magnitude, `r8 = a` or `r10 = b`. -/
theorem zselEntry_ok {s : State} {X : Addr} {a b m : Nat} (hm1 : 1 ≤ m) (hm : m < 2 ^ 31)
    (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (h8 : s.gpr .r8 = BitVec.ofNat 64 a)
    (h10 : s.gpr .r10 = BitVec.ofNat 64 b) (hx : s.gpr .rdx = X)
    (hr : ∀ c < 3, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 32 * c)) 32)
    (hacc : ∀ h < 2, ∀ c < 3, ∀ k < 4, zq s (xr (11 + c)) h k = accQ s.mem X (hmag a b h) (m - 1) c k) :
    WP isa (.block (zselEntry m)) s fun t =>
      (∀ h < 2, ∀ c < 3, ∀ k < 4, zq t (xr (11 + c)) h k = accQ s.mem X (hmag a b h) m c k) ∧
      ZVKeep [.rcx] zselRegs s t := by
  rw [zselEntry, WP.block_append_iff]
  refine WP.mono (zmasks_ok s hm ha hb h8 h10) fun s₁ ⟨x₁, k₁⟩ => ?_
  refine WP.mono (zselLoads_ok (X := X) 3 (Nat.le_refl _) s₁ (by rw [k₁.gpr _ (by decide), hx]) (by
      rw [k₁.rd, k₁.wr]; exact hr)) fun t ⟨a₃, k₃⟩ => ⟨fun h hh c hc k hk => ?_, ?_⟩
  · have hne : ∀ i < 4, s₁.zlane (xr (11 + c)) i = s.zlane (xr (11 + c)) i := k₁.zl _ (by
      rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide)
    obtain hm15 : zq s₁ (xr 15) h k = cmask (decide (hmag a b h = m)) := by
      simp only [zq]
      rw [x₁ _ (by omega_arith)]
      rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl <;>
        rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> simp [hmag]
    rw [a₃ h hh c hc k hk, ite_eq_left_of_eq_true _ _ (eq_true hc), hm15, k₁.mem,
      show zq s₁ (xr (11 + c)) h k = zq s (xr (11 + c)) h k by simp only [zq]; rw [hne _ (by omega_arith)],
      hacc h hh c hc k hk]
    exact accQ_step _ _ _ _ _ _ hm1
  · refine k₁.mono (fun _ h => h) (fun r h => ?_) |>.trans (k₃.mono (fun _ h => by simp at h) fun r h => ?_)
    · rcases h with h | h <;> simp [zselRegs, h]
    · rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

/-- The entries `1 … n` of the table at `rdx = X` kept in the cleared accumulators under the
masks of the halves' magnitudes. -/
theorem zselEntries_ok {X : Addr} {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ∀ n, n < 2 ^ 31 → ∀ (s : State), s.gpr .r8 = BitVec.ofNat 64 a → s.gpr .r10 = BitVec.ofNat 64 b →
    s.gpr .rdx = X →
    (∀ e < n, ∀ c < 3, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * e + 32 * c)) 32) →
    (∀ h < 2, ∀ c < 3, ∀ k < 4, zq s (xr (11 + c)) h k = 0) →
    WP isa (.block ((List.range n).flatMap fun m => zselEntry (m + 1))) s fun t =>
      (∀ h < 2, ∀ c < 3, ∀ k < 4, zq t (xr (11 + c)) h k = accQ s.mem X (hmag a b h) n c k) ∧
      ZVKeep [.rcx] zselRegs s t
  | 0, _, s, _, _, _, _, h0 => WP.block_nil ⟨fun h hh c hc k hk => by
      rw [h0 h hh c hc k hk, accQ, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))], ZVKeep.refl _ _ _⟩
  | n + 1, hn, s, h8, h10, hx, hr, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (zselEntries_ok ha hb n (by omega_arith) s h8 h10 hx (fun e he => hr e (by omega_arith)) h0)
      fun s₁ ⟨a₁, k₁⟩ => ?_
    refine WP.mono (zselEntry_ok (X := X) (m := n + 1) (by omega_arith) hn ha hb
      (by rw [k₁.gpr _ (by decide), h8]) (by rw [k₁.gpr _ (by decide), h10]) (by rw [k₁.gpr _ (by decide), hx])
      (fun c hc => by rw [k₁.rd, k₁.wr, Nat.add_sub_cancel]; exact hr n (by omega_arith) c hc)
      (fun h hh c hc k hk => by rw [a₁ h hh c hc k hk, k₁.mem, Nat.add_sub_cancel])) fun t ⟨a₂, k₂⟩ =>
      ⟨fun h hh c hc k hk => by rw [a₂ h hh c hc k hk, k₁.mem], k₁.trans k₂⟩

/-- `zmm11–zmm13` cleared. -/
theorem zselClear_ok (s : State) :
    WP isa (.block [zero 11, zero 12, zero 13]) s fun t =>
      (∀ h < 2, ∀ c < 3, ∀ k < 4, zq t (xr (11 + c)) h k = 0) ∧ ZVKeep [] zselRegs s t := by
  apply WP.of_runBlock
  simp only [zero, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun h hh c hc k hk => ?_, ⟨fun _ _ => by zkeep, by zkeep, by zkeep, by zkeep, fun r hr i hi => ?_,
    by zkeep⟩⟩
  · simp only [zq]
    rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;>
      simp only [VOp.exec, zlane_setV256 _ _ _ _ _ (show 2 * h + k / 2 < 4 by omega_arith), y, xr, Nat.reduceAdd,
        reduceCtorEq, ↓reduceIte, VBinOp.sse, XBinOp.eval, BitVec.xor_self] <;>
      split <;> (try split) <;> exact Ifma.qword_zero _
  · simp only [zselRegs, not_or, not_exists, not_and] at hr
    obtain h1 := hr.2.1 0 (by decide); have h2 := hr.2.1 1 (by decide); have h3 := hr.2.1 2 (by decide)
    simp only [Nat.reduceAdd] at h1 h2 h3
    simp only [VOp.exec, zlane_setV256 _ _ _ _ _ hi, show y 11 = xr 11 from rfl, show y 12 = xr 12 from rfl,
      show y 13 = xr 13 from rfl, h1, h2, h3, ite_false]

/-- `rax = 1` if `g = a` is zero, else `0`. -/
theorem isZero_ok (s : State) (g : Reg) {a : Nat} (ha : a < 2 ^ 64) (hg : s.gpr g = BitVec.ofNat 64 a) :
    WP isa (.block (isZero g)) s fun t => t.gpr .rax = (if a = 0 then 1 else 0) ∧
      Proof.X25519.X86_64.Keeps [.rax] s t ∧ t.syms = s.syms := by
  obtain hM : (BitVec.ofNat 64 a - BitVec.ofNat 64 a - BitVec.setWidth 64 (BitVec.ofBool
      (decide ((BitVec.ofNat 64 a).toNat < (BitVec.signExtend 64 (1 : BitVec 32)).toNat)))) &&&
      BitVec.signExtend 64 (1 : BitVec 32) = if a = 0 then 1 else 0 := by
    by_cases h : a = 0
    · subst h; decide
    · have h1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := by decide
      rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, decide_eq_false (by omega_arith),
        ite_eq_right_iff.mpr (fun h2 => absurd h2 h)]
      simp
  erun [isZero, hg, hM]
  refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem isZero_scal (g : Reg) : scalCode (.block (isZero g)) = true := rfl

/-- The word of entry `m` of table `j` the selection leaves in row `c`, word `k`: the identity's
`[1, 1, 0]` for a zero magnitude. -/
def selWord (j m c k : Nat) : BitVec 64 :=
  if 1 ≤ m then feWord (combField j m c) k else if c < 2 ∧ k = 0 then 1 else 0

theorem selWord_or (j m c k : Nat) (hm : m ≤ 16) :
    (if 1 ≤ m ∧ m ≤ 16 then feWord (combField j m c) k else 0) |||
      (if c < 2 ∧ k = 0 then (if m = 0 then 1 else 0) else 0) = selWord j m c k := by
  unfold selWord
  by_cases h : 1 ≤ m
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h, hm⟩), ite_eq_left_of_eq_true _ _ (eq_true h)]
    split <;> simp [show m ≠ 0 by omega_arith]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false h)]
    split <;> simp [show m = 0 by omega_arith]

theorem qword_zero' (i : Nat) : qword (0#128) i = 0 := Ifma.qword_zero i

theorem qword_load512 (m : Mem) (a : Addr) {i q : Nat} (hi : i < 4) (hq : q < 2) :
    qword ((m.readW a 512).extractLsb' (128 * i) 128) q = m.readW (a + BitVec.ofNat 64 (16 * i + 8 * q)) 64 := by
  obtain e := readW_extract m a (w := 512) (k := 16 * i + 8 * q) (n := 8) (by omega_arith)
  rw [← e]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 64 * q + j < 128 by omega_arith)]
  congr 1; omega_arith

theorem zselect_split : zselect = combSelSetup ++ ([zero 11, zero 12, zero 13] : List Instr) ++
    (List.range 16).flatMap (fun m => zselEntry (m + 1)) ++ isZero .r8 ++
    ([.vop (.vmovq (y 10) .rax)] : List Instr) ++ isZero .r10 ++
    ([.vop (.vmovq (y 9) .rax), zlo 10 10 9, .zop (.zbin .vporq (y 11) (y 11) (y 10)),
      .zop (.zbin .vporq (y 12) (y 12) (y 10)), .vmovdqu32Load (y 14) (sc ZK2)] : List Instr) := by
  simp only [zselect, List.append_assoc, List.cons_append, List.nil_append]

theorem zlane_vmovq (s : State) (d : XReg) (g : Reg) (r : XReg) {i : Nat} (hi : i < 4) :
    ((VOp.vmovq d g).exec s).zlane r i = if r = d then (if i = 0 then (0 : BitVec 64) ++ s.gpr g else 0)
      else s.zlane r i := by
  simp only [VOp.exec, State.zlane_setV128 _ _ _ _ _ hi]

/-- The selection: in half `h`, the words of entry `m_h` (`r8` for half 0, `r10` for half 1) of
table `j`, or the identity's, in `zmm11–zmm13` (`selWord`), and the row `ZK2` in `zmm14`. -/
theorem zselect_ok {s : State} {base T : Addr} (hs : Scratch s base) (ht : CombTbl s T) {j a b : Nat}
    (hj : j < 26) (ha : a ≤ 16) (hb : b ≤ 16) (hd : s.gpr .rdx = BitVec.ofNat 64 j)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (h10 : s.gpr .r10 = BitVec.ofNat 64 b) :
    WP isa (.block zselect) s fun t =>
      (∀ h < 2, ∀ c < 3, ∀ k < 4, zq t (xr (11 + c)) h k = selWord j (hmag a b h) c k) ∧
      (∀ h < 2, ∀ k < 4, zq t (xr 14) h k = s.mem.readW (base + BitVec.ofNat 64 (ZK2 + 32 * h + 8 * k)) 64) ∧
      ZVKeep [.rax, .rcx, .rdx] (fun r => zselRegs r ∨ r = xr 9) s t := by
  rw [zselect_split, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (zscal rfl (combSelSetup_ok s hd ht.sym)) fun s₁ ⟨⟨x₁, k₁, _, y₁⟩, z₁⟩ => ?_
  refine WP.mono (zselClear_ok s₁) fun s₂ ⟨a₂, k₂⟩ => ?_
  obtain hr : ∀ e < 16, ∀ c < 3, InRegions (s₂.rd ++ s₂.wr)
      (T + BitVec.ofNat 64 (j * combTblBytes) + BitVec.ofNat 64 (combEntryBytes * e + 32 * c)) 32 := by
    intro e he c hc
    rw [k₂.rd, k₂.wr, k₁.2.2.1, k₁.2.2.2, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    refine VG.CallLay.inRegions_sub ht.rd ?_ (by decide)
    simp only [combTblBytes, combEntryBytes, combWordCount]; omega_arith
  refine WP.mono (zselEntries_ok (X := T + BitVec.ofNat 64 (j * combTblBytes)) (a := a) (b := b) (by omega_arith)
    (by omega_arith) 16 (by decide) s₂
    (by rw [k₂.gpr _ List.not_mem_nil, k₁.1 _ (by decide), h8])
    (by rw [k₂.gpr _ List.not_mem_nil, k₁.1 _ (by decide), h10])
    (by rw [k₂.gpr _ List.not_mem_nil, x₁]) hr a₂) fun s₃ ⟨a₃, k₃⟩ => ?_
  obtain g₃ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [k₃.gpr r (by simpa using h2), k₂.gpr r List.not_mem_nil, k₁.1 r (by simp [h1, h2, h3])]
  refine WP.mono (zscal (isZero_scal .r8) (isZero_ok s₃ .r8 (a := a) (by omega_arith)
    (by rw [g₃ _ (by decide) (by decide) (by decide), h8]))) fun s₄ ⟨⟨r₄, k₄, y₄⟩, z₄⟩ => ?_
  let s₅ := (VOp.vmovq (y 10) .rax).exec s₄
  refine WP.of_runBlock ⟨s₅, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_⟩
  refine WP.mono (zscal (isZero_scal .r10) (isZero_ok s₅ .r10 (a := b) (by omega_arith)
    (by show s₄.gpr .r10 = _; rw [k₄.1 _ (by decide), g₃ _ (by decide) (by decide) (by decide), h10])))
    fun s₆ ⟨⟨r₆, k₆, y₆⟩, z₆⟩ => ?_
  obtain hz2 : InRegions (s₆.rd ++ s₆.wr) (base + BitVec.ofNat 64 ZK2) 64 := by
    rw [k₆.2.2.1, k₆.2.2.2]
    show InRegions (s₄.rd ++ s₄.wr) _ 64
    rw [k₄.2.2.1, k₄.2.2.2, k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.2.2.1, k₁.2.2.2]
    exact ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base base (by unfold ZK2; omega_arith) (by unfold ZK2; omega_arith)⟩
  obtain hrdi : s₆.gpr .rdi = base := by
    rw [k₆.1 _ (by decide)]; show s₄.gpr .rdi = _; rw [k₄.1 _ (by decide), g₃ _ (by decide) (by decide) (by decide),
      hs.rdi]
  obtain m₆ : s₆.mem = s.mem := by
    rw [k₆.2.1]; show s₄.mem = _; rw [k₄.2.1, k₃.mem, k₂.mem, k₁.2.1]
  let w := s₆.mem.readW (base + BitVec.ofNat 64 ZK2) 512
  let u₁ := (VOp.vmovq (y 9) .rax).exec s₆
  let u₂ := (ZOp.vshufi32x4 (y 10) (y 10) (y 9) 0x44).exec u₁
  let u₃ := (ZOp.zbin .vporq (y 11) (y 11) (y 10)).exec u₂
  let u₄ := (ZOp.zbin .vporq (y 12) (y 12) (y 10)).exec u₃
  let u₅ := u₄.setZ (y 14) (w.extractLsb' 0 128) (w.extractLsb' 128 128) (w.extractLsb' 256 128)
    (w.extractLsb' 384 128)
  obtain e5 : exec (.vmovdqu32Load (y 14) (sc ZK2)) u₄ = some u₅ := by
    obtain hea : u₄.ea (sc ZK2) = base + BitVec.ofNat 64 ZK2 := by
      simp only [u₄, ZOp.exec_ea, u₃, u₂, u₁, VOp.exec_ea]
      exact ea_sc' hrdi ZK2
    obtain hin : InRegions (u₄.rd ++ u₄.wr) (base + BitVec.ofNat 64 ZK2) 64 := by
      simp only [u₄, ZOp.exec_rd, ZOp.exec_wr, u₃, u₂, u₁, VOp.exec_rd, VOp.exec_wr]
      exact hz2
    simp (config := { zetaDelta := true }) only [exec, hea, State.load512, hin, ite_true, Option.map_some,
      ZOp.exec_mem, VOp.exec_mem]
  refine WP.of_runBlock ⟨u₅, ?_, ?_⟩
  · rw [runBlock_cons, show exec _ s₆ = some u₁ from rfl, runStep_some, runBlock_cons,
      show exec (zlo 10 10 9) u₁ = some u₂ from rfl, runStep_some, runBlock_cons, show exec _ u₂ = some u₃ from rfl,
      runStep_some, runBlock_cons, show exec _ u₃ = some u₄ from rfl, runStep_some, runBlock_cons, e5, runStep_some,
      runBlock_nil]
  obtain l₂ : ∀ i < 4, u₂.zlane (y 10) i = if i % 2 = 0 then
      (0 : BitVec 64) ++ (if hmag a b (i / 2) = 0 then (1 : BitVec 64) else 0) else 0 := by
    intro i hi
    have r6 : s₆.gpr .rax = if b = 0 then 1 else 0 := r₆
    have r4 : s₄.gpr .rax = if a = 0 then 1 else 0 := r₄
    simp only [u₂, zlane_zlo _ _ _ _ _ hi, ite_true, u₁, zlane_vmovq _ _ _ _ (show i - 2 < 4 by omega_arith),
      zlane_vmovq _ _ _ _ hi, show y 10 ≠ y 9 by decide, ite_false, z₆, s₅, r6, r4]
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> simp [hmag]
  obtain l₃ : ∀ r, r ≠ y 9 → r ≠ y 10 → ∀ i < 4, u₂.zlane r i = s₃.zlane r i := fun r h9 h10 i hi => by
    simp only [u₂, zlane_zlo _ _ _ _ _ hi, h10, ite_false, u₁, zlane_vmovq _ _ _ _ hi, h9, z₆, s₅]
    exact z₄ r i
  obtain hacc : ∀ h < 2, ∀ c < 3, ∀ k < 4, zq s₃ (xr (11 + c)) h k =
      if 1 ≤ hmag a b h ∧ hmag a b h ≤ 16 then feWord (combField j (hmag a b h) c) k else 0 := by
    intro h hh c hc k hk
    rw [a₃ h hh c hc k hk, accQ, k₂.mem, k₁.2.1]
    obtain hm : hmag a b h ≤ 16 := by simp only [hmag]; split <;> omega_arith
    by_cases h1 : 1 ≤ hmag a b h
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, hm⟩), ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, hm⟩)]
      obtain hw := combTbl_word ht hj h1 hm (i := 4 * c + k) (by omega_arith)
      rw [Proof.X25519.X86_64.word, Proof.X25519.X86_64.off] at hw
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        show combEntryBytes * (hmag a b h - 1) + 32 * c + 8 * k =
          combEntryBytes * (hmag a b h - 1) + 8 * (4 * c + k) by omega_arith,
        hw, entryWords_getD _ c k hc hk, combField, combCached_succ j _ h1]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
  obtain h3 : ∀ c < 3, ∀ i < 4, s₃.zlane (y (11 + c)) i = s₃.zlane (xr (11 + c)) i := fun c hc i _ => by
    rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> rfl
  refine ⟨fun h hh c hc k hk => ?_, fun h hh k hk => ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, fun r hr i hi => ?_, ?_⟩⟩
  · have hmh : hmag a b h ≤ 16 := by simp only [hmag]; split <;> omega_arith
    rw [← selWord_or _ _ _ _ hmh, ← hacc h hh c hc k hk]
    obtain hi : 2 * h + k / 2 < 4 := by omega_arith
    obtain L1 : ∀ i < 4, u₅.zlane (y 11) i = s₃.zlane (y 11) i ||| u₂.zlane (y 10) i := fun i hi => by
      simp only [u₅, zlane_load _ _ _ _ hi, show y 11 ≠ y 14 by decide, ite_false, u₄, zlane_zbin _ _ _ _ _ _ hi,
        show y 11 ≠ y 12 by decide, u₃, ite_true, ZBinOp.sse, XBinOp.eval, l₃ (y 11) (by decide) (by decide) _ hi]
    obtain L2 : ∀ i < 4, u₅.zlane (y 12) i = s₃.zlane (y 12) i ||| u₂.zlane (y 10) i := fun i hi => by
      simp only [u₅, zlane_load _ _ _ _ hi, show y 12 ≠ y 14 by decide, ite_false, u₄, zlane_zbin _ _ _ _ _ _ hi,
        ite_true, u₃, show y 10 ≠ y 11 by decide, show y 12 ≠ y 11 by decide, ZBinOp.sse, XBinOp.eval,
        l₃ (y 12) (by decide) (by decide) _ hi]
    obtain L3 : ∀ i < 4, u₅.zlane (y 13) i = s₃.zlane (y 13) i := fun i hi => by
      simp only [u₅, zlane_load _ _ _ _ hi, show y 13 ≠ y 14 by decide, ite_false, u₄, zlane_zbin _ _ _ _ _ _ hi,
        show y 13 ≠ y 12 by decide, u₃, show y 13 ≠ y 11 by decide, l₃ (y 13) (by decide) (by decide) _ hi]
    rw [show xr (11 + c) = y (11 + c) by rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> rfl]
    simp only [zq]
    rcases (by omega_arith : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
    · rw [L1 _ hi, qword_or, l₂ _ hi]
      rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl <;>
        rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
        simp [hmag, qword_zero']
    · rw [L2 _ hi, qword_or, l₂ _ hi]
      rcases (by omega_arith : h = 0 ∨ h = 1) with rfl | rfl <;>
        rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;>
        simp [hmag, qword_zero']
    · rw [L3 _ hi]; simp
  · simp only [zq, u₅, show xr 14 = y 14 from rfl, zlane_load _ _ _ _ (show 2 * h + k / 2 < 4 by omega_arith),
      ite_true, w]
    rw [qword_load512 _ _ (by omega_arith) (Nat.mod_lt _ (by decide)), show s₆.mem = s.mem from m₆,
      Offset.add_ofNat_add_ofNat]
    congr 3; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [u₅, State.setZ_gpr, u₄, ZOp.exec_gpr, u₃, u₂, u₁, VOp.exec_gpr]
    rw [k₆.1 r (by simp [hr.1])]
    show s₄.gpr r = s.gpr r
    rw [k₄.1 r (by simp [hr.1]), g₃ r hr.1 hr.2.1 hr.2.2]
  · simp only [u₅, State.setZ_mem, u₄, ZOp.exec_mem, u₃, u₂, u₁, VOp.exec_mem]
    exact m₆
  · simp only [u₅, State.setZ_rd, u₄, ZOp.exec_rd, u₃, u₂, u₁, VOp.exec_rd]
    rw [k₆.2.2.1]; show s₄.rd = _; rw [k₄.2.2.1, k₃.rd, k₂.rd, k₁.2.2.1]
  · simp only [u₅, State.setZ_wr, u₄, ZOp.exec_wr, u₃, u₂, u₁, VOp.exec_wr]
    rw [k₆.2.2.2]; show s₄.wr = _; rw [k₄.2.2.2, k₃.wr, k₂.wr, k₁.2.2.2]
  · simp only [zselRegs, not_or, not_exists, not_and] at hr
    have n9 : r ≠ y 9 := hr.2
    have n10 : r ≠ y 10 := hr.1.1
    obtain n11 : r ≠ y 11 := hr.1.2.1 0 (by decide)
    obtain n12 : r ≠ y 12 := hr.1.2.1 1 (by decide)
    have n14 : r ≠ y 14 := hr.1.2.2.1
    simp only [u₅, zlane_load _ _ _ _ hi, n14, ite_false, u₄, zlane_zbin _ _ _ _ _ _ hi, n12, u₃, n11,
      l₃ r n9 n10 _ hi]
    rw [k₃.zl r (by simp only [zselRegs, not_or, not_exists, not_and]; exact hr.1) i hi,
      k₂.zl r (by simp only [zselRegs, not_or, not_exists, not_and]; exact hr.1) i hi, z₁]
  · dsimp only [u₅, State.setZ, u₄, u₃, u₂, ZOp.exec, u₁, VOp.exec, State.setV]
    rw [y₆]; show s₄.syms = _; rw [y₄, k₃.syms, k₂.syms, y₁]

end VG.Proof.Ed25519.X86_64.Zmm
