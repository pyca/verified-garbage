module

public import VerifiedGarbage.Proof.Framework.PlainSimp
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
public import VerifiedGarbage.Impl.RsaPss.Arm
public import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Lay
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `RsaPss.Arm.Base`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS on ARMv7: where everything is, for the pieces both functions share

`Geo L scr`: the layout `L` (`Proof/RsaPkcs1Sig/Arm/Lay.lean`) has our
frame, and our part of `scratch` (`oRsa` bytes at `scr`) lies in one of its
writable buffers. `Ctx L scr σ s`: a state of the body with `scr` in its
slot `sS`. Every piece of code both functions share is proven from such a
state, keeping any fact about memory that its writes do not reach.

`VP.blk`: a block of arithmetic, comparisons, `movw` and loads and stores
relative to `sp` (`r12 = sp`) is constant time when the stack pointer is the
same, whatever the registers hold.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)

/-- Byte `o` of our part of `scratch`. -/
abbrev sa (scr : BitVec 32) (o : Nat) : Addr := State.addr scr + BitVec.ofNat 64 o

/-- Bytes `o … o + n - 1` of our part of `scratch`. -/
abbrev sR (scr : BitVec 32) (o n : Nat) : Region := ⟨sa scr o, n⟩

/-- A slot of the frame. -/
abbrev slotR (L : Lay) (d : Nat) : Region := ⟨L.fr d, 4⟩

/-- The layout has our frame, and our part of `scratch` lies in one of its
writable buffers. -/
structure Geo (L : Lay) (scr : BitVec 32) : Prop where
  F : L.F = frameBytes
  fit : scr.toNat + oRsa < 2 ^ 32
  sub : ∃ k, oRsa ≤ k ∧ (⟨State.addr scr, k⟩ : Region) ∈ L.rw
  ok : ∃ σ, L.Ok σ
  C16 : 16 ≤ L.C

/-- A state of the body, with `scr` in its slot. -/
structure Ctx (L : Lay) (scr : BitVec 32) (σ s : State) : Prop where
  st : L.St σ s
  slotS : s.mem.readW (L.fr sS) 32 = scr

section
variable {L : Lay} {scr : BitVec 32}

namespace Geo
variable (hg : Geo L scr)
include hg

theorem addr {o : Nat} (h : o < oRsa) : State.addr (scr + BitVec.ofNat 32 o) = sa scr o :=
  addr_add (by have := hg.fit; unfold oRsa at *; omega_using [h, this])

/-- A range of our part of `scratch` within a writable buffer. -/
theorem inR {o n : Nat} (h : o + n ≤ oRsa) : ∃ R ∈ L.rw, Region.Sub (sR scr o n) R := by
  obtain ⟨k, hk, hR⟩ := hg.sub
  exact ⟨_, hR, Offset.sub_base _ (by omega_using [h, hk])⟩

theorem inW {o n : Nat} (h : o + n ≤ oRsa) : ∃ R ∈ L.W, Region.Sub (sR scr o n) R := by
  obtain ⟨R, hR, hs⟩ := hg.inR h
  exact ⟨R, by simp [Lay.W, hR], hs⟩

/-- Our part of `scratch` misses our stack. -/
theorem stk {σ : State} (ok : L.Ok σ) {o n : Nat} (h : o + n ≤ oRsa) : (sR scr o n).Disjoint L.STK := by
  obtain ⟨R, hR, hs⟩ := hg.inR h
  exact ((ok.stk R (List.mem_append_right _ hR)).sub_right hs).symm

theorem slot {σ : State} (ok : L.Ok σ) {o n d k : Nat} (h : o + n ≤ oRsa) (hd : d + k ≤ L.F + 56) :
    Region.Disjoint ⟨L.fr d, k⟩ (sR scr o n) :=
  ((hg.stk ok h).sub_right (Lay.sub_stk hd)).symm

theorem low {σ : State} (ok : L.Ok σ) {o n : Nat} (h : o + n ≤ oRsa) : (sR scr o n).Disjoint L.LOW :=
  (hg.stk ok h).sub_right Lay.low_stk

/-- And the buffers only read. -/
theorem ro {σ : State} (ok : L.Ok σ) {o n : Nat} (h : o + n ≤ oRsa) {R : Region} (hR : R ∈ L.ro) :
    (sR scr o n).Disjoint R := by
  obtain ⟨W, hW, hs⟩ := hg.inR h
  exact (ok.wro W hW R (List.mem_append_left _ hR)).sub_left hs

theorem wr {σ s : State} (hs : L.St σ s) {o n : Nat} (h : o + n ≤ oRsa) : InRegions s.wr (sa scr o) n := by
  obtain ⟨k, hk, hR⟩ := hg.sub
  exact ⟨_, by rw [hs.wr, hs.ok.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hR), Offset.contains_base _ (by omega_using [h, hk]) (by unfold oRsa at h; omega_using [h])⟩

theorem rd {σ s : State} (hs : L.St σ s) {o n : Nat} (h : o + n ≤ oRsa) :
    InRegions (s.rd ++ s.wr) (sa scr o) n :=
  let ⟨r, hr, hc⟩ := hg.wr hs h
  ⟨r, List.mem_append_right _ hr, hc⟩

omit hg in
/-- Two ranges of our part of `scratch`. -/
theorem sep {o n e k : Nat} (h : o + n ≤ e ∨ e + k ≤ o) (ho : o + n ≤ oRsa) (he : e + k ≤ oRsa) :
    (sR scr o n).Disjoint (sR scr e k) :=
  Offset.disjoint _ h (by unfold oRsa at ho; omega_using [ho]) (by unfold oRsa at he; omega_using [he])

end Geo

/-! ## Keeping `Ctx` -/

namespace Ctx

theorem regs {σ s t : State} (h : Ctx L scr σ s) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp)
    (m : t.mem = s.mem) : Ctx L scr σ t :=
  ⟨h.st.regs rd wr sp m, by rw [m]; exact h.slotS⟩

/-- Memory changed within regions of what the body may write, apart from
the slot `sS`. -/
theorem write {σ s t : State} (h : Ctx L scr σ s) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ R ∈ L.W, Region.Sub r R) (hd : ∀ r ∈ rs, (slotR L sS).Disjoint r)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp) : Ctx L scr σ t :=
  ⟨h.st.write hf hs rd wr sp, by
    rw [hf.readW (r := slotR L sS) (Region.contains_self _ _) hd (by decide)]; exact h.slotS⟩

theorem setReg_iff {σ s : State} {r : Reg} {v : BitVec 32} : Ctx L scr σ (s.setReg r v) ↔ Ctx L scr σ s :=
  ⟨fun h => h.regs rfl rfl rfl rfl, fun h => h.regs rfl rfl rfl rfl⟩

/-- A slot's address, for the symbolic execution of a block. -/
theorem aFr {σ s : State} (hg : Geo L scr) (h : Ctx L scr σ s) :
    ∀ d, d + 4 ≤ frameBytes → State.addr (L.B + BitVec.ofNat 32 d) = L.fr d :=
  fun d hd => h.st.ok.addrB (by rw [hg.F]; omega_using [hd])

theorem rFr {σ s : State} (hg : Geo L scr) (h : Ctx L scr σ s) :
    ∀ d, d + 4 ≤ frameBytes → InRegions (s.rd ++ s.wr) (L.fr d) 4 :=
  fun d hd => h.st.inFrR (by rw [hg.F]; exact hd)

theorem wFr {σ s : State} (hg : Geo L scr) (h : Ctx L scr σ s) :
    ∀ d, d + 4 ≤ frameBytes → InRegions s.wr (L.fr d) 4 :=
  fun d hd => h.st.inFr (by rw [hg.F]; exact hd)

end Ctx

end

/-- A piece from no state. -/
theorem VP.empty {F G : State → State → Prop} {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c G :=
  ⟨fun σ s hs => (h σ s hs).elim, fun _ _ _ _ _ _ ⟨σ, _, hs, _⟩ => (h σ _ hs).elim⟩

/-! ## Blocks that address only the stack -/

/-- An instruction whose addresses depend only on `sp` and on `r12` (which
blocks set to `sp`). -/
def stkInstr : Instr → Bool
  | .str _ n _ => decide (n = .r12)
  | .ldr _ n _ => decide (n = .r12)
  | .ldrSp _ _ | .dp _ _ _ _ | .mov _ _ | .addSp _ _ | .movw _ _ | .movt _ _ | .cmp _ _ | .subs _ _ _
  | .adds _ _ _ => true
  | _ => false

theorem stkInstr_leak {i : Instr} (hi : stkInstr i = true) {s t : State}
    (h : VG.Proof.Rsa.Arm.StackBaseEq s t) : addrs i s = addrs i t := by
  cases i <;> simp_all [stkInstr, addrs, VG.Proof.Rsa.Arm.StackBaseEq]

/-- `stkInstr` and no write of `r12`, for every instruction of a block, by
evaluation (the immediates may be parameters). -/
theorem blkOk {code : List Instr}
    (h : code.all (fun i => stkInstr i && !(clobbers i .r12)) = true) :
    ∀ i ∈ code, stkInstr i = true ∧ clobbers i .r12 = false := by
  intro i hi
  have := List.all_eq_true.mp h i hi
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this

/-- A block of such instructions after `r12 := sp`, never writing `r12`, is
constant time when the stack pointer is the same. -/
theorem VP.blk {F G : State → State → Prop} {code : List Instr}
    (ok : ∀ i ∈ code, stkInstr i = true ∧ clobbers i .r12 = false)
    (sp : ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → s₁.sp = s₂.sp)
    (wp : ∀ σ s, F σ s → WP isa (.block (.addSp .r12 0 :: code)) s (G σ)) :
    VP F (.block (.addSp .r12 0 :: code)) G :=
  VP.of_ct (fun _ _ => (VG.Proof.Rsa.Arm.setupBlock_ct code (fun i hi => (ok i hi).2)
    (fun i hi _ _ h => stkInstr_leak (ok i hi).1 h)).mono
    (fun _ _ h => sp _ _ _ _ h.1 h.2) fun _ _ _ => trivial) wp

end VG.Proof.RsaPss.Arm

end

end

/-!
# RSASSA-PSS on ARMv7: running a block symbolically

Rewrite rules for `exec` of each instruction the blocks use, stated so that
`simp` steps through a block (`WP.of_runBlock`, then `runBlock_cons`,
`runStep_some` and `runBlock_nil`), discharging the permissions of loads and
stores from facts about the state the block starts in (the permissions and
the stack pointer of every later state are its own, by `RegUpd`), and
reading registers through the writes with `RegUpd.gpr_setReg`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm

/-- `s` with memory `m`. -/
def setMem (s : State) (m : Mem) : State := { s with mem := m }

@[simp] theorem setMem_gpr (s : State) (m : Mem) : (setMem s m).gpr = s.gpr := rfl
@[simp] theorem setMem_sp (s : State) (m : Mem) : (setMem s m).sp = s.sp := rfl
@[simp] theorem setMem_rd (s : State) (m : Mem) : (setMem s m).rd = s.rd := rfl
@[simp] theorem setMem_wr (s : State) (m : Mem) : (setMem s m).wr = s.wr := rfl
@[simp] theorem setMem_mem (s : State) (m : Mem) : (setMem s m).mem = m := rfl
@[simp] theorem setMem_z (s : State) (m : Mem) : (setMem s m).z = s.z := rfl

theorem subFlags_gpr (s : State) (x y : BitVec 32) : (subFlags s x y).gpr = s.gpr := rfl
theorem subFlags_mem (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl
theorem subFlags_rd (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl
theorem subFlags_wr (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
theorem subFlags_sp (s : State) (x y : BitVec 32) : (subFlags s x y).sp = s.sp := rfl
theorem subFlags_z (s : State) (x y : BitVec 32) : (subFlags s x y).z = (x - y == 0) := rfl

theorem setWidth_zero16 : (0#16).setWidth 32 = (0 : BitVec 32) := rfl

theorem movw_val {v : Nat} (h : v < 2 ^ 16) : (BitVec.ofNat 16 v).setWidth 32 = BitVec.ofNat 32 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using [h]

end VG.Proof.RsaPss.Arm

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.RsaPss.Arm

/-! The slots' offsets are immediates. -/

theorem sS_lt : sS < 4096 := by decide
theorem sLo_lt : sLo < 4096 := by decide
theorem sC_lt : sC < 4096 := by decide
theorem sDb_lt : sDb < 4096 := by decide
theorem sL_lt : sL < 4096 := by decide
theorem sNb_lt : sNb < 4096 := by decide
theorem sBi_lt : sBi < 4096 := by decide
theorem sCtr_lt : sCtr < 4096 := by decide
theorem sDone_lt : sDone < 4096 := by decide
theorem sAcc_lt : sAcc < 4096 := by decide
theorem sPos_lt : sPos < 4096 := by decide
theorem sA_lt : sA < 4096 := by decide
theorem sD_lt : sD < 4096 := by decide
theorem sPc_lt : sPc < 4096 := by decide
theorem sAny_lt : sAny < 4096 := by decide

theorem store32_eq (s : State) (a : Addr) (x : BitVec 32) :
    s.store32 a x = if InRegions s.wr a 4 then some (setMem s (s.mem.writeW a x)) else none := rfl
theorem store8_eq (s : State) (a : Addr) (x : BitVec 8) :
    s.store8 a x = if InRegions s.wr a 1 then some (setMem s (s.mem.writeW a x)) else none := rfl
theorem c_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).c = decide (y.toNat ≤ x.toNat) := rfl

/-- Runs a block symbolically: `WP.of_runBlock`, then each instruction's
semantics, reading registers through the writes (`RegUpd`) and keeping
memory and flag updates folded (`setMem`, `subFlags`), with `facts` (the
permissions of the accesses, the values of shift amounts and immediates the
code takes as parameters). -/
syntax "prun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| prun) => `(tactic| prun [])
  | `(tactic| prun [$ls,*]) => `(tactic| plain_simp_names (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (disch := decide) only [runBlock_cons, runStep_some, runBlock_nil, exec,
        VG.Proof.RsaPkcs1Sig.Arm.encodable_of_lt, Op2.eval, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg,
        z_setReg, c_setReg, subFlags_gpr, subFlags_mem, subFlags_rd, subFlags_wr, subFlags_sp, subFlags_z,
        c_subFlags, State.load32, store32_eq, State.load8, store8_eq, setMem_gpr, setMem_sp, setMem_rd,
        setMem_wr, setMem_mem, setMem_z, ite_true, ite_false, ↓reduceIte, reduceCtorEq, Nat.reduceLT,
        Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, Option.map_some, Option.some.injEq, exists_eq_left',
        List.cons_append, List.nil_append, and_true, true_and, BitVec.add_zero, sS_lt, sLo_lt, sC_lt, sDb_lt, sL_lt,
        sNb_lt, setWidth_zero16, sBi_lt, sCtr_lt, sDone_lt, sAcc_lt, sPos_lt, sA_lt, sD_lt, sPc_lt, sAny_lt, $ls,*]))

end VG.Proof.RsaPss.Arm

