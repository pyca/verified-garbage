module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FastTable
public import VerifiedGarbage.Proof.MlKem.Kpke16Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Spec.MlKem
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunF
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.ModelI
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.Mem16
import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.FastInv
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunFI
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.ModelFI
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sym
public import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitFI
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.RunW
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.LitF

/-! ### `MlKem.AArch64.NttR.AbiF`, which only this module used -/

section

/-!
# ML-KEM on AArch64: `vg_mlkem16_ntt` keeps what the ABI preserves

`fwdFast` keeps the low halves of `v8`–`v15` in `x7`–`x14` (`save`), which
the transform (`core`) does not write, and puts them back at the end
(`restore`); it writes none of `x19`–`x28` and `x30`, and leaves `sp` alone.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Impl.MlKem.AArch64.Ntt16.Fast

/-- `x7 + k` kept in lane 0 of `v8 + k`. -/
def lanesF : List (Reg × VReg × Nat) :=
  [(.x7, .v8, 0), (.x8, .v9, 0), (.x9, .v10, 0), (.x10, .v11, 0),
   (.x11, .v12, 0), (.x12, .v13, 0), (.x13, .v14, 0), (.x14, .v15, 0)]

theorem save_eq : save = umovOf lanesF ++ ([.adrSym .x1 name, .addImm .x .x2 .x1 160] : List Instr) := rfl

theorem restore_eq : restore = insOf lanesF := rfl

theorem save_ok (s : State) :
    WP isa (.block save) s fun t => ∀ k ∈ lanesF, t.gpr k.1 = laneOf s k.2.1 k.2.2 := by
  rw [save_eq]
  refine WP.block_append (WP.mono (umovOf_ok lanesF s (by decide) (by decide)) fun t ⟨_, _, _, _, ht, _⟩ => ?_)
  refine WP.block_cons_iff.mpr ⟨_, exec_adrSym, WP.block_cons_iff.mpr ⟨_, exec_addImm_x (imm := 160) (by decide), WP.block_nil ?_⟩⟩
  intro k hk
  have h1 : k.1 ≠ .x1 := by revert k; decide
  have h2 : k.1 ≠ .x2 := by revert k; decide
  rw [RegUpd.gpr_write_of_ne (s := _) _ _ h2, RegUpd.gpr_write_of_ne (s := _) _ _ h1]
  exact ht k hk

/-- No instruction of `core` writes `x7`–`x14`. -/
theorem core_keeps : core.allInstrs (fun i => lanesF.all fun k => !clobbers i k.1) = true := by
  decide +kernel

/-- No instruction of `fwdFast` writes `x19`–`x28` or `x30`. -/
theorem fwdFast_keeps : fwdFast.allInstrs (fun i => preserved.all fun r => !clobbers i r) = true := by
  lit_decide

theorem fwdFast_abi {s s' : State} {t : List Leak} (he : Exec isa fwdFast s t s') : abiPreserved s s' := by
  refine ⟨fun r hr => Exec.gpr (fun i hi => ?_) he, Exec.sp he, fun r hr => ?_⟩
  · have := List.all_eq_true.mp ((Code.allInstrs_eq _ fwdFast) ▸ fwdFast_keeps) i hi
    simpa using List.all_eq_true.mp this r hr
  · cases he with
    | seq h1 h23 =>
    cases h23 with
    | seq h2 h3 =>
    obtain ⟨_, t1, e1, hs⟩ := save_ok s
    have hk : ∀ k ∈ lanesF, ∀ i ∈ instrs core, clobbers i k.1 = false := fun k hk i hi => by
      have := List.all_eq_true.mp ((Code.allInstrs_eq _ core) ▸ core_keeps) i hi
      simpa using List.all_eq_true.mp this k hk
    rw [restore_eq] at h3
    obtain ⟨_, t3, e3, -, -, -, -, -, h3l, -⟩ := insOf_ok lanesF _ (by decide) (by decide)
    rw [← (Exec.det h3 e3).2] at h3l
    rw [← (Exec.det h1 e1).2] at hs
    have hl : ∀ k ∈ lanesF, laneOf s' k.2.1 k.2.2 = laneOf s k.2.1 k.2.2 := fun k hkm => by
      rw [h3l k hkm, Exec.gpr (hk k hkm) h2, hs k hkm]
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hl (.x7, .v8, 0) (by decide) | exact hl (.x8, .v9, 0) (by decide)
      | exact hl (.x9, .v10, 0) (by decide) | exact hl (.x10, .v11, 0) (by decide)
      | exact hl (.x11, .v12, 0) (by decide) | exact hl (.x12, .v13, 0) (by decide)
      | exact hl (.x13, .v14, 0) (by decide) | exact hl (.x14, .v15, 0) (by decide)

end VG.Proof.MlKem.AArch64.NttR

end

end

/-! ### `MlKem.AArch64.NttR.FwdW`, which only this module used -/

section

/-! ### `MlKem.AArch64.NttR.Ctx`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.NttR.Step`, which this module and modules that import it used -/

section

/-!
# ML-KEM on AArch64: the NTT halfword by halfword, the machine agrees with the code

The machine's state holds of the code's (`Rel`): each halfword of a vector
register or of a chunk of a region is the value of its term, unless the term
is not followed, and each general register the machine follows holds its
number, or a pointer into a region (`GHd`). The regions are readable,
writable if the machine writes them, and apart (`Ctx`). Each instruction the
machine follows keeps this (`step_ok`), and so do its runs of blocks,
sequences and loops (`runP_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64

/-! ## The machine's accessors -/

/-- The register of an index: `vi` has it for a left inverse, so the 32 cases of one register show
that `vi` is injective, not the 1024 of two. -/
private def viInv : Nat → VReg
  | 0 => .v0 | 1 => .v1 | 2 => .v2 | 3 => .v3 | 4 => .v4 | 5 => .v5 | 6 => .v6 | 7 => .v7 | 8 => .v8
  | 9 => .v9 | 10 => .v10 | 11 => .v11 | 12 => .v12 | 13 => .v13 | 14 => .v14 | 15 => .v15 | 16 => .v16
  | 17 => .v17 | 18 => .v18 | 19 => .v19 | 20 => .v20 | 21 => .v21 | 22 => .v22 | 23 => .v23 | 24 => .v24
  | 25 => .v25 | 26 => .v26 | 27 => .v27 | 28 => .v28 | 29 => .v29 | 30 => .v30
  | _ => .v31

private theorem viInv_vi (r : VReg) : viInv (vi r) = r := by cases r <;> rfl

theorem vi_inj {r r' : VReg} : vi r = vi r' ↔ r = r' :=
  ⟨fun h => (viInv_vi r).symm.trans ((congrArg viInv h).trans (viInv_vi r')), fun h => congrArg vi h⟩

/-- The register of an index, for `gi`. -/
private def giInv : Nat → Reg
  | 0 => .x0 | 1 => .x1 | 2 => .x2 | 3 => .x3 | 4 => .x4 | 5 => .x5 | 6 => .x6 | 7 => .x7 | 8 => .x8
  | 9 => .x9 | 10 => .x10 | 11 => .x11 | 12 => .x12 | 13 => .x13 | 14 => .x14 | 15 => .x15 | 16 => .x16
  | 17 => .x17 | 19 => .x19 | 20 => .x20 | 21 => .x21 | 22 => .x22 | 23 => .x23 | 24 => .x24 | 25 => .x25
  | 26 => .x26 | 27 => .x27 | 28 => .x28
  | _ => .x30

private theorem giInv_gi (r : Reg) : giInv (gi r) = r := by cases r <;> rfl

theorem gi_inj {r r' : Reg} : gi r = gi r' ↔ r = r' :=
  ⟨fun h => (giInv_gi r).symm.trans ((congrArg giInv h).trans (giInv_gi r')), fun h => congrArg gi h⟩

theorem vreg_setV (σ : St) (d r : VReg) {y : Nat} (hy : y < 2 ^ yw) :
    (σ.setV d y).vreg r = if r = d then y else σ.vreg r := by
  unfold St.vreg St.setV
  rw [slot_upd yw σ.v (vi d) y hy (vi r)]
  by_cases h : r = d
  · rw [ite_eq_left (vi_inj.2 h), ite_eq_left h]
  · rw [ite_eq_right (fun e => h (vi_inj.1 e)), ite_eq_right h]

theorem greg_setV (σ : St) (d : VReg) (y : Nat) : (σ.setV d y).greg = σ.greg := rfl
theorem chunk_setV (σ : St) (d : VReg) (y : Nat) : (σ.setV d y).chunk = σ.chunk := rfl

theorem gcode_lt (g : G) : g.code < 2 ^ gw := by
  cases g with
  | junk => decide
  | num n =>
    have := Nat.mod_lt n (show 0 < 2 ^ 64 by decide)
    show 1 + 2 * (n % 2 ^ 64) < 2 ^ gw
    rw [show 2 ^ gw = 2 ^ 64 * 2 ^ 16 from rfl]
    omega_using []
  | ptr k o =>
    have := Nat.mod_lt o (show 0 < 2 ^ 32 by decide)
    have := Nat.mod_lt k (show 0 < 16 by decide)
    show 2 + 2 * (k % 16 + 16 * (o % 2 ^ 32)) < 2 ^ gw
    rw [show 2 ^ gw = 2 ^ 32 * 2 ^ 48 from rfl]
    omega_using []

theorem greg_setG (σ : St) (d r : Reg) (g : G) :
    (σ.setG d g).greg r = if r = d then G.ofCode g.code else σ.greg r := by
  unfold St.greg St.setG
  rw [slot_upd _ _ _ _ (gcode_lt g)]
  by_cases h : r = d
  · rw [ite_eq_left (gi_inj.2 h), ite_eq_left h]
  · rw [ite_eq_right (fun e => h (gi_inj.1 e)), ite_eq_right h]

theorem vreg_setG (σ : St) (d : Reg) (g : G) : (σ.setG d g).vreg = σ.vreg := rfl
theorem chunk_setG (σ : St) (d : Reg) (g : G) : (σ.setG d g).chunk = σ.chunk := rfl

theorem chunk_setChunk (σ : St) (k j : Nat) {y : Nat} (hy : y < 2 ^ yw) (k' j' : Nat) :
    (σ.setChunk k j y).chunk k' j' = if k' = k ∧ j' = j ∧ k < σ.mem.length then y else σ.chunk k' j' := by
  unfold St.chunk St.setChunk
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases hk : k = k'
  · subst hk
    by_cases hl : k < σ.mem.length
    · rw [ite_eq_left rfl, ite_eq_left hl, List.getElem?_eq_getElem hl, Option.getD_some, Option.getD_some,
        slot_upd yw σ.mem[k] j y hy j', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
      by_cases hj : j' = j
      · simp [hj, hl]
      · simp [hj]
    · rw [ite_eq_left rfl, ite_eq_right hl]
      simp [hl, List.getD_eq_getElem?_getD]
  · rw [ite_eq_right hk]
    simp [Ne.symm hk]

theorem vreg_setChunk (σ : St) (k j : Nat) (y : Nat) : (σ.setChunk k j y).vreg = σ.vreg := rfl
theorem greg_setChunk (σ : St) (k j : Nat) (y : Nat) : (σ.setChunk k j y).greg = σ.greg := rfl

theorem vreg_lt (σ : St) (r : VReg) : @LT.lt Nat instLTNat (σ.vreg r) (2 ^ yw) := by
  unfold St.vreg; exact slot_bound yw σ.v (vi r)
theorem chunk_lt (σ : St) (k j : Nat) : @LT.lt Nat instLTNat (σ.chunk k j) (2 ^ yw) := by
  unfold St.chunk; exact slot_bound yw (σ.mem.getD k 0) j

/-! ## Lanes -/

open VG.Proof.MlKem.AArch64.Ntt16 (vhalf_ofVHalves vhalf_map2 getLsbD_vhalf vhalf_perm_h8 vhalf_perm_s4
  vhalf_trn_d2 eval_mulH)

theorem vhalf_zero' (e : Nat) : vhalf 0 e = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [getLsbD_vhalf _ _ hi]

theorem vhalf_and' (a b : BitVec 128) {e : Nat} : vhalf (a &&& b) e = vhalf a e &&& vhalf b e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [getLsbD_vhalf _ _ hi, BitVec.getLsbD_and]

theorem vhalf_setLane' (x : BitVec 128) {k e : Nat} (hk : k < 8) (he : e < 8) (h : BitVec 16) :
    vhalf (setLane x 16 k h) e = if e = k then h else vhalf x e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_vhalf _ _ hi]
  simp only [setLane, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    show 16 * e + i < 128 by omega_using [he, hi], decide_true, Bool.true_and]
  by_cases h' : e = k
  · subst h'
    simp [hi, show ¬ 16 * e + i < 16 * e by omega_using [], show 16 * e + i - 16 * e = i by omega_using [],
      show i < 128 by omega_using [hi]]
  · rw [ite_eq_right h', getLsbD_vhalf _ _ hi]
    rcases (by omega_using [h'] : e < k ∨ k < e) with c | c
    · simp [show 16 * e + i < 16 * k by omega_using [hi, c]]
    · have : h.getLsbD (16 * e + i - 16 * k) = false := BitVec.getLsbD_of_ge _ _ (by omega_using [c])
      simp [show ¬ 16 * e + i < 16 * k by omega_using [c], show ¬ 16 * e + i - 16 * k < 16 by omega_using [c], this]

/-- The halfword `e` of a permutation the machine follows. -/
theorem vhalf_perm (op : VPermOp) (a : VArr) (x y : BitVec 128) {e : Nat} (he : e < 8) {b : Bool} {i : Nat}
    (h : permSrc op a e = some (b, i)) : vhalf (op.eval a x y) e = vhalf (if b then y else x) i := by
  cases a with
  | d2 =>
    cases op <;> simp [permSrc] at h
    · rw [(vhalf_trn_d2 x y he).1]; split at h <;> simp_all <;> intro <;> omega
    · rw [(vhalf_trn_d2 x y he).2]; split at h <;> simp_all <;> intro <;> omega
  | s4 =>
    rw [vhalf_perm_s4 _ _ _ he]
    cases op <;> simp only [permSrc] at h <;> (try split at h) <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp_all <;>
      first | (intro; omega) | (split <;> split <;> first | rfl | omega)
  | b16 => cases op <;> simp [permSrc] at h
  | h8 =>
    rw [vhalf_perm_h8 _ _ _ he]
    cases op <;> simp only [permSrc] at h <;> (try split at h) <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp_all <;>
      first | (intro; omega) | (split <;> split <;> first | rfl | omega)

theorem permSrc_lt {op : VPermOp} {a : VArr} {e : Nat} {b : Bool} {i : Nat} (h : permSrc op a e = some (b, i))
    (he : e < 8) : i < 8 := by
  cases a <;> cases op <;> simp only [permSrc, reduceCtorEq] at h <;> (try split at h) <;>
    simp only [Option.some.injEq, Prod.mk.injEq] at h <;> omega

/-! ## Registers and regions -/

section
variable (rs : List Rg) (s₀ : State)

/-- Where a region starts. -/
def baseOf : Base → Addr
  | .reg r => s₀.gpr r
  | .sym n => s₀.syms n

/-- The address of region `k`. -/
def rbase (k : Nat) : Addr := baseOf s₀ (rs.getD k default).base + BitVec.ofNat 64 (rs.getD k default).off

/-- The address of chunk `j` of region `k`. -/
def caddr (k j : Nat) : Addr := rbase rs s₀ k + BitVec.ofNat 64 (16 * j)

/-- The number of chunks of region `k`. -/
def chunks (k : Nat) : Nat := (rs.getD k default).chunks

/-- A general register holds what the machine says. -/
def GHd : G → BitVec 64 → Prop
  | .junk, _ => True
  | .num n, v => n < 2 ^ 64 ∧ v = BitVec.ofNat 64 n
  | .ptr k o, v => k < rs.length ∧ k < 16 ∧ o < 2 ^ 32 ∧ v = rbase rs s₀ k + BitVec.ofNat 64 o

/-- The regions are few and small, readable, writable where the machine
writes them, and apart. -/
structure Ctx : Prop where
  len : rs.length ≤ 16
  small : ∀ k < rs.length, (rs.getD k default).off + 16 * chunks rs k < 2 ^ 32
  rd : ∀ k < rs.length, ∀ j < chunks rs k, InRegions (s₀.rd ++ s₀.wr) (caddr rs s₀ k j) 16
  wr : ∀ k < rs.length, (rs.getD k default).wr = true → ∀ j < chunks rs k, InRegions s₀.wr (caddr rs s₀ k j) 16
  sep : ∀ k j k' j', k < rs.length → j < chunks rs k → k' < rs.length → j' < chunks rs k' →
    ¬ (k = k' ∧ j = j') → Mem.Sep (caddr rs s₀ k j) 16 (caddr rs s₀ k' j') 16

/-- The machine's state `σ` holds of `s`, from `s₀`. -/
structure Rel (L : Nat → Nat → BitVec 16) (O : Nat → BitVec 16) (σ : St) (s : State) : Prop where
  v : ∀ r, ∀ e < 8, Hd L O ((σ.vreg r).get e) (vhalf (s.v r) e)
  g : ∀ r, GHd rs s₀ (σ.greg r) (s.gpr r)
  mem : ∀ k < rs.length, ∀ j < chunks rs k, ∀ e < 8,
    Hd L O ((σ.chunk k j).get e) (vhalf (s.mem.read (caddr rs s₀ k j) 16) e)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  syms : s.syms = s₀.syms

end

theorem GHd.code {rs : List Rg} {s₀ : State} {g : G} {v : BitVec 64} (h : GHd rs s₀ g v) :
    GHd rs s₀ (G.ofCode g.code) v := by
  cases g with
  | junk => trivial
  | num n =>
    obtain ⟨hn, rfl⟩ := h
    have e : G.ofCode (G.num n).code = .num n := by
      simp only [G.code, G.ofCode, Nat.mod_eq_of_lt hn]
      rw [ite_eq_right (by omega_using []), ite_eq_left (by omega_using [])]
      congr 1; omega_using []
    rw [e]; exact ⟨hn, rfl⟩
  | ptr k o =>
    obtain ⟨hk, hk16, ho, rfl⟩ := h
    have e : G.ofCode (G.ptr k o).code = .ptr k o := by
      simp only [G.code, G.ofCode, Nat.mod_eq_of_lt hk16, Nat.mod_eq_of_lt ho]
      rw [ite_eq_right (by omega_using []), ite_eq_right (by omega_using [])]
      congr 1 <;> omega_using [hk16]
    rw [e]; exact ⟨hk, hk16, ho, rfl⟩

/-- What `locate` finds. -/
theorem locate_some {rs : List Rg} {b : Base} {a k o : Nat} (h : locate rs b a = some (k, o)) :
    k < rs.length ∧ (rs.getD k default).base = b ∧ (rs.getD k default).off + o = a ∧
      o < 16 * (rs.getD k default).chunks := by
  unfold locate at h
  cases hf : rs.findIdx? (fun r => r.base == b && r.off ≤ a && a < r.off + 16 * r.chunks) with
  | none => rw [hf] at h; cases h
  | some k' =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hk, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
    exact ⟨hk, hp.1.1, by omega, by omega⟩

end VG.Proof.MlKem.AArch64.NttR

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64
open VG.Proof.MlKem.AArch64.Ntt16 (vhalf_ofVHalves vhalf_map2 eval_mulH)

section
variable {rs : List Rg} {s₀ : State} {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16}

theorem ofNat_mod16 (v : Nat) : BitVec.ofNat 16 (v % 65536) = BitVec.ofNat 16 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega_using []

theorem Hd.cT (v : Nat) : Hd L O (cT v) (BitVec.ofNat 16 v) := by
  refine (Hd.mk (by decide)).2 ?_
  rw [eval_mk]
  exact (ofNat_mod16 v).symm

theorem cT_lt (v : Nat) : @LT.lt Nat instLTNat (cT v) (2 ^ tw) := mk_lt_tw ..

theorem setWidth16 (v : Nat) : (BitVec.ofNat 64 v).setWidth 16 = BitVec.ofNat 16 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

theorem Hd.ofFn {f : Nat → T} {g : Nat → BitVec 16} (hlt : ∀ e < 8, @LT.lt Nat instLTNat (f e) (2 ^ tw))
    (h : ∀ e < 8, Hd L O (f e) (g e)) : ∀ e < 8, Hd L O ((Y.ofFn f).get e) (g e) := by
  intro e he
  rw [get_ofFn _ he, Nat.mod_eq_of_lt (hlt e he)]
  exact h e he

theorem get_lt (y : Y) (e : Nat) : @LT.lt Nat instLTNat (y.get e) (2 ^ tw) := slot_bound tw y e

theorem Rel.setV {σ : St} {s : State} (h : Rel rs s₀ L O σ s) {d : VReg} {y : Nat} {x : BitVec 128}
    (hy : y < 2 ^ yw) (hx : ∀ e < 8, Hd L O (Y.get y e) (vhalf x e)) :
    Rel rs s₀ L O (σ.setV d y) (s.setV d x) := by
  refine ⟨fun r e he => ?_, fun r => ?_, fun k hk j hj e he => ?_, h.rd, h.wr, h.sp, h.syms⟩
  · rw [vreg_setV _ _ _ hy]
    by_cases hr : r = d
    · subst hr; rw [ite_eq_left rfl]; simp only [State.setV, ite_true]; exact hx e he
    · rw [ite_eq_right hr]; simp only [State.setV, hr, ite_false]; exact h.v r e he
  · rw [greg_setV]; exact h.g r
  · rw [chunk_setV]; exact h.mem k hk j hj e he

theorem Y.get_dup (a : T) {e : Nat} (he : e < 8) : (Y.dup a).get e = a % 2 ^ tw := get_ofFn _ he

theorem eval_dupE' {s : State} {d n : VReg} {k : Nat} (hk : k < 8) :
    VOp.eval s (.dupE .h8 d n k) = some (d, ofVHalves fun _ => vhalf (s.v n) k) := by
  simp only [VOp.eval, VArr.esize, show k < 128 / 16 from hk, ite_true, VArr.map2]
  rfl

theorem exec_vop {s : State} {o : VOp} {d : VReg} {x : BitVec 128} (h : o.eval s = some (d, x)) :
    exec (.vop o) s = some (s.setV d x) := by
  simp only [exec, h, Option.map_some]

/-- The lanes of `ofVHalves f`, from those of terms. -/
theorem Hd.ofVHalves {y : Nat} {f : Nat → BitVec 16} (h : ∀ e < 8, Hd L O (Y.get y e) (f e)) :
    ∀ e < 8, Hd L O (Y.get y e) (vhalf (ofVHalves f) e) := fun e he => by
  rw [vhalf_ofVHalves _ he]; exact h e he

theorem eval_mulHE {s : State} {op : VMulHOp} {d n m : VReg} {i : Nat} (hi : i < 8) (hm : m.index < 16)
    (h : ∀ e < 8, (op.lane (vhalf (s.v d) e) (vhalf (s.v n) e) (vhalf (s.v m) i)).isSome) :
    VOp.eval s (.mulHE op d n m i) =
      some (d, ofVHalves fun e => (op.lane (vhalf (s.v d) e) (vhalf (s.v n) e) (vhalf (s.v m) i)).getD 0) := by
  simp only [VOp.eval]
  rw [ite_eq_left ⟨hi, hm, by
    rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
    simp only [List.all_cons, List.all_nil, h 0 (by decide), h 1 (by decide), h 2 (by decide),
      h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide),
      Bool.and_self]⟩]

theorem vop_ok {R : Rules} (hM : Model L O R) {σ σ' : St} {s : State} (h : Rel rs s₀ L O σ s) {o : VOp}
    (hs : σ.vop R o = some σ') : ∃ s', exec (.vop o) s = some s' ∧ Rel rs s₀ L O σ' s' := by
  cases o with
  | movi0 d =>
    simp only [St.vop, Option.some.injEq] at hs; subst hs
    refine ⟨_, exec_vop rfl, h.setV (ofFn_lt _) fun e he => ?_⟩
    rw [Y.get_dup _ he, Nat.mod_eq_of_lt (cT_lt 0), vhalf_zero']
    exact Hd.cT 0
  | mov d n =>
    simp only [St.vop, Option.some.injEq] at hs; subst hs
    exact ⟨_, exec_vop rfl, h.setV (slot_bound _ _ _) (h.v n)⟩
  | dup a d n =>
    cases a <;> simp only [St.vop, reduceCtorEq] at hs
    split at hs
    · rename_i v hv
      simp only [Option.some.injEq] at hs; subst hs
      have hg := h.g n; rw [hv] at hg; obtain ⟨-, hg⟩ := hg
      refine ⟨_, exec_vop rfl, h.setV (ofFn_lt _) (Hd.ofVHalves fun e he => ?_)⟩
      rw [Y.get_dup _ he, Nat.mod_eq_of_lt (cT_lt _), hg, setWidth16, ← ofNat_mod16 v]
      exact Hd.cT _
    · cases hs
  | ins a d i n =>
    cases a <;> simp only [St.vop, reduceCtorEq] at hs
    case d2 =>
      split at hs
      · rename_i hi
        simp only [Option.some.injEq] at hs; subst hs
        refine ⟨_, exec_vop (x := setLane (s.v d) 64 i (s.gpr n)) (by simp only [VOp.eval, hi, ite_true]),
          h.setV (Nat.two_pow_pos _) fun e _ => ?_⟩
        rw [show Y.get 0 e = junkT by show slot tw 0 e = 0; rw [slot_zero]]
        exact Hd.junk _
      · cases hs
    split at hs
    · rename_i v hv
      split at hs
      · rename_i hi
        simp only [Option.some.injEq] at hs; subst hs
        have hg := h.g n; rw [hv] at hg; obtain ⟨-, hg⟩ := hg
        have hy : @LT.lt Nat instLTNat (upd tw (σ.vreg d) i (cT (v % 65536))) (2 ^ yw) := by
          have := vreg_lt σ d
          rw [show yw = tw * 8 from rfl] at this ⊢
          exact upd_lt this (cT_lt _) hi
        refine ⟨_, exec_vop (x := setLane (s.v d) 16 i ((s.gpr n).setWidth 16))
          (by simp only [VOp.eval, hi, ite_true]), h.setV hy fun e he => ?_⟩
        rw [vhalf_setLane' _ hi he]
        unfold Y.get
        rw [slot_upd tw _ _ _ (cT_lt _)]
        by_cases hei : e = i
        · rw [ite_eq_left hei, ite_eq_left hei, hg, setWidth16, ← ofNat_mod16 v]; exact Hd.cT _
        · rw [ite_eq_right hei, ite_eq_right hei]; exact h.v d e he
      · cases hs
    · cases hs
  | dupE a d n i =>
    cases a <;> simp only [St.vop, reduceCtorEq] at hs
    split at hs
    · rename_i hi
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨_, exec_vop (eval_dupE' hi), h.setV (ofFn_lt _) (Hd.ofVHalves fun e he => ?_)⟩
      rw [Y.get_dup _ he, Nat.mod_eq_of_lt (get_lt _ _)]
      exact h.v n i hi
    · cases hs
  | mulH op d n m =>
    cases op <;> simp only [St.vop, reduceCtorEq] at hs
    · -- mul
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨_, exec_vop (eval_mulH fun _ _ => rfl), h.setV (ofFn_lt _)
        (Hd.ofVHalves (Hd.ofFn (fun e _ => mulT_lt _ _) fun e he => ?_))⟩
      exact mulT_ok (h.v n e he) (h.v m e he)
    · -- mls
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨_, exec_vop (eval_mulH fun _ _ => rfl), h.setV (ofFn_lt _)
        (Hd.ofVHalves (Hd.ofFn (fun e _ => subT_lt _ _ _) fun e he => ?_))⟩
      exact subT_ok hM (h.v d e he) (mulT_ok (h.v n e he) (h.v m e he))
    · -- sqrdmulh
      split at hs
      · rename_i hq
        simp only [Option.some.injEq] at hs; subst hs
        have hok : ∀ e < 8, qdOk ((σ.vreg m).get e) = true := fun e he =>
          List.all_eq_true.1 hq e (List.mem_range.2 he)
        refine ⟨_, exec_vop (eval_mulH fun e he => qdOk_some (h.v m e he) (hok e he) _), h.setV (ofFn_lt _)
          (Hd.ofVHalves (Hd.ofFn (fun e _ => qdT_lt _ _) fun e he => ?_))⟩
        exact qdT_ok (h.v n e he) (h.v m e he)
      · cases hs
  | mulHE op d n m i =>
    cases op <;> simp only [St.vop, reduceCtorEq] at hs
    · -- mul
      split at hs
      · rename_i hc
        simp only [Option.some.injEq] at hs; subst hs
        refine ⟨_, exec_vop (eval_mulHE hc.1 hc.2 fun _ _ => rfl), h.setV (ofFn_lt _)
          (Hd.ofVHalves (Hd.ofFn (fun e _ => mulT_lt _ _) fun e he => ?_))⟩
        exact mulT_ok (h.v n e he) (h.v m i hc.1)
      · cases hs
    · -- mls
      split at hs
      · rename_i hc
        simp only [Option.some.injEq] at hs; subst hs
        refine ⟨_, exec_vop (eval_mulHE hc.1 hc.2 fun _ _ => rfl), h.setV (ofFn_lt _)
          (Hd.ofVHalves (Hd.ofFn (fun e _ => subT_lt _ _ _) fun e he => ?_))⟩
        exact subT_ok hM (h.v d e he) (mulT_ok (h.v n e he) (h.v m i hc.1))
      · cases hs
    · -- sqrdmulh
      split at hs
      · rename_i hc
        simp only [Option.some.injEq] at hs; subst hs
        refine ⟨_, exec_vop (eval_mulHE hc.1 hc.2.1 fun e he => qdOk_some (h.v m i hc.1) hc.2.2 _),
          h.setV (ofFn_lt _) (Hd.ofVHalves (Hd.ofFn (fun e _ => qdT_lt _ _) fun e he => ?_))⟩
        exact qdT_ok (h.v n e he) (h.v m i hc.1)
      · cases hs
  | add a d n m =>
    cases a <;> simp only [St.vop, reduceCtorEq] at hs
    simp only [Option.some.injEq] at hs; subst hs
    refine ⟨_, exec_vop rfl, h.setV (ofFn_lt _) fun e he => ?_⟩
    rw [vhalf_map2 _ _ _ he]
    exact Hd.ofFn (fun e _ => addT_lt _ _ _) (fun e he => addT_ok hM (h.v n e he) (h.v m e he)) e he
  | sub a d n m =>
    cases a <;> simp only [St.vop, reduceCtorEq] at hs
    simp only [Option.some.injEq] at hs; subst hs
    refine ⟨_, exec_vop rfl, h.setV (ofFn_lt _) fun e he => ?_⟩
    rw [vhalf_map2 _ _ _ he]
    exact Hd.ofFn (fun e _ => subT_lt _ _ _) (fun e he => subT_ok hM (h.v n e he) (h.v m e he)) e he
  | shift op a d n sh =>
    cases op <;> cases a <;> simp only [St.vop, reduceCtorEq] at hs
    split at hs
    · rename_i h15
      subst h15
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨_, exec_vop (by simp only [VOp.eval]; rfl), h.setV (ofFn_lt _) fun e he => ?_⟩
      rw [vhalf_map2 _ _ _ he]
      exact Hd.ofFn (fun e _ => sraT_lt _) (fun e he => sraT_ok (h.v n e he)) e he
    · cases hs
  | logic op d n m =>
    cases op <;> simp only [St.vop, reduceCtorEq] at hs
    simp only [Option.some.injEq] at hs; subst hs
    refine ⟨_, exec_vop rfl, h.setV (ofFn_lt _) fun e he => ?_⟩
    rw [vhalf_and']
    exact Hd.ofFn (g := fun e => vhalf (s.v n) e &&& vhalf (s.v m) e) (fun e _ => andT_lt _ _) (fun e he => andT_ok (h.v n e he) (h.v m e he)) e he
  | perm op a d n m =>
    simp only [St.vop] at hs
    split at hs
    · rename_i hp
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨_, exec_vop rfl, h.setV (ofFn_lt _) (Hd.ofFn (fun e _ => ?_) fun e he => ?_)⟩
      · split
        · exact get_lt _ _
        · exact junk_lt
      · obtain ⟨⟨b, i⟩, hsrc⟩ := Option.isSome_iff_exists.1 (List.all_eq_true.1 hp e (List.mem_range.2 he))
        rw [hsrc, vhalf_perm op a _ _ he hsrc]
        have hi : i < 8 := permSrc_lt hsrc he
        cases b
        · exact h.v n i hi
        · exact h.v m i hi
    · cases hs
  | _ => simp [St.vop, reduceCtorEq] at hs

/-! ## General registers and memory -/

theorem read_write16' (m : Mem) (a : Addr) (x : BitVec 128) : (m.write a 16 x).read a 16 = x := by
  refine Mem.read_eq_of_bytes fun i hi => ?_
  simp only [Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega_using [hi]), hi, ite_true]

theorem Rel.setG {σ : St} {s : State} (h : Rel rs s₀ L O σ s) {d : Reg} {g : G} {v : BitVec 64}
    (hg : GHd rs s₀ g v) : Rel rs s₀ L O (σ.setG d g) (s.write .x d v) := by
  refine ⟨fun r e he => ?_, fun r => ?_, fun k hk j hj e he => ?_, h.rd, h.wr, h.sp, h.syms⟩
  · rw [vreg_setG]; exact h.v r e he
  · rw [greg_setG]
    simp only [State.write]
    by_cases hr : r = d
    · rw [ite_eq_left hr, ite_eq_left hr, BitVec.setWidth_eq]; exact hg.code
    · rw [ite_eq_right hr, ite_eq_right hr]; exact h.g r
  · rw [chunk_setG]; exact h.mem k hk j hj e he

theorem rbase_norm {rs : List Rg} {s₀ : State} (hc : Ctx rs s₀) {k o : Nat} (hk : k < rs.length) (ho : o < 2 ^ 32)
    : GHd rs s₀ (norm rs k o) (rbase rs s₀ k + BitVec.ofNat 64 o) := by
  unfold norm
  split
  · rename_i k' o' hl
    obtain ⟨hk', hb, ho', hlt⟩ := locate_some hl
    have hs := hc.small k' hk'
    unfold chunks at hs
    refine ⟨hk', by have := hc.len; omega_using [hk', this], by omega_using [hlt, hs], ?_⟩
    unfold rbase
    rw [hb, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add, ho']
  · exact ⟨hk, by have := hc.len; omega_using [hk, this], ho, rfl⟩

theorem GHd.addG {rs : List Rg} {s₀ : State} (hc : Ctx rs s₀) {g : G} {v : BitVec 64} (h : GHd rs s₀ g v)
    (imm : Nat) : GHd rs s₀ (addG rs g imm) (v + BitVec.ofNat 64 imm) := by
  cases g with
  | junk => trivial
  | num n =>
    obtain ⟨-, rfl⟩ := h
    refine ⟨Nat.mod_lt _ (by decide), ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using []
  | ptr k o =>
    obtain ⟨hk, -, -, rfl⟩ := h
    simp only [NttR.addG]
    split
    · rename_i ho
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact rbase_norm hc hk ho
    · trivial

theorem GHd.subG {rs : List Rg} {s₀ : State} (hc : Ctx rs s₀) {g : G} {v : BitVec 64} (h : GHd rs s₀ g v)
    {imm : Nat} (himm : imm < 4096) : GHd rs s₀ (subG rs g imm) (v - BitVec.ofNat 64 imm) := by
  cases g with
  | junk => trivial
  | num n =>
    obtain ⟨hn, rfl⟩ := h
    refine ⟨Nat.mod_lt _ (by decide), ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [himm]
  | ptr k o =>
    obtain ⟨hk, -, ho, rfl⟩ := h
    simp only [NttR.subG]
    split
    · rename_i hle
      have e : BitVec.ofNat 64 o = BitVec.ofNat 64 (o - imm) + BitVec.ofNat 64 imm := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hle]
      rw [e, ← BitVec.add_assoc, BitVec.add_sub_cancel]
      exact rbase_norm hc hk (by omega_using [ho])
    · trivial

/-- An access the machine finds. -/
theorem chunkAt_some {rs : List Rg} {s₀ : State} {g : G} {v : BitVec 64} (h : GHd rs s₀ g v) {off k j : Nat}
    (hk : chunkAt rs g off = some (k, j)) :
    k < rs.length ∧ j < chunks rs k ∧ v + BitVec.ofNat 64 off = caddr rs s₀ k j := by
  cases g with
  | junk => cases hk
  | num n => cases hk
  | ptr k₀ o =>
    obtain ⟨hk₀, -, -, rfl⟩ := h
    simp only [chunkAt] at hk
    cases hl : locate rs (rs.getD k₀ default).base ((rs.getD k₀ default).off + o + off) with
    | none => rw [hl] at hk; cases hk
    | some p =>
      obtain ⟨k', o'⟩ := p
      rw [hl] at hk
      by_cases h16 : o' % 16 = 0
      · simp only [h16, ite_true, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        obtain ⟨hk', hb, ho', hlt⟩ := locate_some hl
        refine ⟨hk', ?_, ?_⟩
        · unfold chunks; omega_using [hlt]
        · unfold caddr rbase
          rw [hb, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
            ← BitVec.ofNat_add, show 16 * (o' / 16) = o' by omega_using [h16], ho', Nat.add_assoc]
      · simp [h16] at hk

theorem chunk_none {σ : St} {k j : Nat} (hk : ¬ k < σ.mem.length) (e : Nat) : (σ.chunk k j).get e = 0 := by
  unfold St.chunk Y.get
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hk), Option.getD_none]
  simp only [slot, ndiv, nmod, Nat.zero_div, Nat.zero_mod]


theorem exec_ldrq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp [exec, addr, State.load, hr, ho.1, show off < 4096 * 16 by omega_using [ho]]

theorem exec_strq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (hr : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp [exec, addr, State.store, hr, ho.1, show off < 4096 * 16 by omega_using [ho]]

theorem movz_val (imm : BitVec 16) {hw : Nat} (hw4 : hw < 4) :
    imm.setWidth 64 <<< (16 * hw) = BitVec.ofNat 64 (imm.toNat * 2 ^ (16 * hw)) ∧
      imm.toNat * 2 ^ (16 * hw) < 2 ^ 64 := by
  have hi := imm.isLt
  have hp : imm.toNat * 2 ^ (16 * hw) < 2 ^ 64 := by
    calc imm.toNat * 2 ^ (16 * hw) < 2 ^ 16 * 2 ^ (16 * hw) := Nat.mul_lt_mul_of_pos_right hi (Nat.two_pow_pos _)
      _ = 2 ^ (16 + 16 * hw) := (Nat.pow_add ..).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega_using [hw4])
  refine ⟨?_, hp⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show imm.toNat < 2 ^ 64 by omega_using [])]

theorem step_ok {R : Rules} (hM : Model L O R) (hc : Ctx rs s₀) {σ σ' : St} {s : State}
    (h : Rel rs s₀ L O σ s) {i : Instr} (hs : σ.step R rs i = some σ') :
    ∃ s', exec i s = some s' ∧ Rel rs s₀ L O σ' s' := by
  cases i
  case vop o => exact vop_ok hM h hs
  case addImm sz d n imm =>
    cases sz <;> simp only [St.step, reduceCtorEq] at hs
    split at hs
    · rename_i himm
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨_, by simp only [exec, himm, ite_true, State.read, BitVec.setWidth_eq], h.setG (h.g n |>.addG hc imm)⟩
    · cases hs
  case subImm sz d n imm =>
    cases sz <;> simp only [St.step, reduceCtorEq] at hs
    split at hs
    · rename_i himm
      simp only [Option.some.injEq] at hs; subst hs
      refine ⟨_, by simp only [exec, himm, ite_true, State.read, BitVec.setWidth_eq], h.setG (h.g n |>.subG hc himm)⟩
    · cases hs
  case movz sz d imm hw =>
    cases sz <;> simp only [St.step, reduceCtorEq] at hs
    split at hs
    · rename_i hw4
      simp only [Option.some.injEq] at hs; subst hs
      obtain ⟨e, hp⟩ := movz_val imm hw4
      refine ⟨_, by simp only [exec, show 16 * hw < Size.bits .x by simp [Size.bits]; omega_using [hw4], ite_true],
        h.setG (g := .num _) ⟨hp, e⟩⟩
    · cases hs
  case umov sz d n i =>
    cases sz <;> simp only [St.step, reduceCtorEq] at hs
    split at hs
    · rename_i hi
      simp only [Option.some.injEq] at hs; subst hs
      exact ⟨_, by simp only [exec, Size.bits, show i * 64 < 128 by omega_using [hi], ite_true]; rfl, h.setG (g := .junk) trivial⟩
    · cases hs
  case adrSym d name =>
    simp only [St.step, Option.some.injEq] at hs; subst hs
    refine ⟨_, rfl, h.setG ?_⟩
    unfold symRegion
    split
    · rename_i k hk
      obtain ⟨hk, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hk
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      refine ⟨hk, by have := hc.len; omega_using [hk, this], by decide, ?_⟩
      unfold rbase baseOf
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hp.1, hp.2,
        BitVec.add_zero, h.syms]
    · trivial
  case ldrq t n off =>
    simp only [St.step] at hs
    split at hs
    · rename_i ho
      cases hk : chunkAt rs (σ.greg n) off with
      | none => rw [hk] at hs; cases hs
      | some p =>
        obtain ⟨k, j⟩ := p
        rw [hk] at hs
        simp only [Option.map_some, Option.some.injEq] at hs; subst hs
        obtain ⟨hk', hj, ha⟩ := chunkAt_some (h.g n) hk
        have hr := hc.rd k hk' j hj
        rw [← ha, ← h.rd, ← h.wr] at hr
        refine ⟨_, exec_ldrq ho hr, h.setV (chunk_lt _ _ _) fun e he => ?_⟩
        rw [ha]
        exact h.mem k hk' j hj e he
    · cases hs
  case strq t n off =>
    simp only [St.step] at hs
    split at hs
    · rename_i ho
      cases hk : chunkAt rs (σ.greg n) off with
      | none => rw [hk] at hs; cases hs
      | some p =>
        obtain ⟨k, j⟩ := p
        rw [hk] at hs
        simp only [Option.bind_some] at hs
        split at hs
        · rename_i hw
          simp only [Option.some.injEq] at hs; subst hs
          obtain ⟨hk', hj, ha⟩ := chunkAt_some (h.g n) hk
          have hr := hc.wr k hk' hw j hj
          rw [← ha, ← h.wr] at hr
          refine ⟨_, exec_strq ho hr, fun r e he => ?_, fun r => ?_, fun k' hk'' j' hj' e he => ?_,
            h.rd, h.wr, h.sp, h.syms⟩
          · rw [vreg_setChunk]; exact h.v r e he
          · rw [greg_setChunk]; exact h.g r
          · rw [chunk_setChunk _ _ _ (vreg_lt _ _), ha]
            split
            · rename_i hkj
              obtain ⟨rfl, rfl, -⟩ := hkj
              rw [read_write16']
              exact h.v t e he
            · by_cases hkj : k' = k ∧ j' = j
              · obtain ⟨rfl, rfl⟩ := hkj
                rw [chunk_none (by omega_arith)]
                exact Hd.junk _
              · rw [Mem.read_write_sep (hc.sep k' j' k j hk'' hj' hk' hj hkj) (by decide)]
                exact h.mem k' hk'' j' hj' e he
        · cases hs
    · cases hs
  all_goals simp only [St.step, reduceCtorEq] at hs

/-! ## Runs -/

theorem run_ok {R : Rules} (hM : Model L O R) (hc : Ctx rs s₀) :
    ∀ (is : List Instr) {σ σ' : St} {s : State}, Rel rs s₀ L O σ s → σ.run R rs is = some σ' →
      WP isa (.block is) s (Rel rs s₀ L O σ')
  | [], σ, σ', s, h, hs => by
    simp only [St.run, Option.some.injEq] at hs; subst hs; exact WP.block_nil h
  | i :: is, σ, σ', s, h, hs => by
    simp only [St.run] at hs
    cases h₁ : σ.step R rs i with
    | none => rw [h₁] at hs; cases hs
    | some σ₁ =>
      rw [h₁, Option.bind_some] at hs
      obtain ⟨s₁, e₁, r₁⟩ := step_ok hM hc h h₁
      exact WP.block_cons_iff.mpr ⟨s₁, e₁, run_ok hM hc is r₁ hs⟩

theorem loop_ok {body : Prog isa} {f : St → Option St} {r : Reg}
    (hf : ∀ {σ σ' : St} {s : State}, Rel rs s₀ L O σ s → f σ = some σ' → WP isa body s (Rel rs s₀ L O σ'))
    (fuel : Nat) {σ σ' : St} {s : State} (h : Rel rs s₀ L O σ s) (hs : loopRun f r fuel σ = some σ') :
    WP isa (.loop body (.nonzero .x r)) s (Rel rs s₀ L O σ') := by
  refine WP.loop (M := isa) (fun n s => ∃ σ, Rel rs s₀ L O σ s ∧ loopRun f r n σ = some σ')
    (fun n s hi => ?_) fuel s ⟨σ, h, hs⟩
  obtain ⟨σ, h, hs⟩ := hi
  cases n with
  | zero => simp [loopRun] at hs
  | succ n =>
    simp only [loopRun] at hs
    cases h₁ : f σ with
    | none => rw [h₁] at hs; cases hs
    | some σ₁ =>
      rw [h₁, Option.bind_some] at hs
      refine WP.mono (hf h h₁) fun s₁ r₁ => ?_
      have hg := r₁.g r
      cases hgr : σ₁.greg r with
      | junk => rw [hgr] at hs; cases hs
      | ptr k o => rw [hgr] at hs; cases hs
      | num k =>
        rw [hgr] at hs hg
        obtain ⟨hlt, hv⟩ := hg
        cases k with
        | zero =>
          simp only [Option.some.injEq] at hs; subst hs
          refine .inl ⟨?_, r₁⟩
          simp only [eval, State.read, BitVec.setWidth_eq, hv]
          rfl
        | succ k =>
          refine .inr ⟨?_, n, Nat.lt_succ_self n, σ₁, r₁, hs⟩
          simp only [eval, State.read, BitVec.setWidth_eq, hv]
          congr 1
          simp only [bne_iff_ne, ne_eq]
          intro e
          have := congrArg BitVec.toNat e
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
          cases this

theorem runP_ok {R : Rules} (hM : Model L O R) (hc : Ctx rs s₀) (fuel : Nat) :
    ∀ (c : Prog isa) {σ σ' : St} {s : State}, Rel rs s₀ L O σ s → σ.runP R rs fuel c = some σ' →
      WP isa c s (Rel rs s₀ L O σ')
  | .block is, _, _, _, h, hs => run_ok hM hc is h hs
  | .seq a b, σ, σ', s, h, hs => by
    simp only [St.runP] at hs
    cases h₁ : σ.runP R rs fuel a with
    | none => rw [h₁] at hs; cases hs
    | some σ₁ =>
      rw [h₁, Option.bind_some] at hs
      exact WP.seq (WP.mono (runP_ok hM hc fuel a h h₁) fun s₁ r₁ => runP_ok hM hc fuel b r₁ hs)
  | .loop b c, σ, σ', s, h, hs => by
    cases c with
    | nonzero sz r =>
      cases sz with
      | x =>
        simp only [St.runP] at hs
        exact loop_ok (fun h h' => runP_ok hM hc fuel b h h') fuel h hs
      | w => simp [St.runP] at hs
    | _ => simp [St.runP] at hs
  | .ite .., _, _, _, _, hs => by simp [St.runP] at hs
  | .call .., _, _, _, _, hs => by simp [St.runP] at hs
  | .frame .., _, _, _, _, hs => by simp [St.runP] at hs
  | .icall .., _, _, _, _, hs => by simp [St.runP] at hs

end

end VG.Proof.MlKem.AArch64.NttR

end

end

/-!
# ML-KEM on AArch64: the NTT halfword by halfword, the regions

The regions of the machine are apart, readable and writable (`Ctx`) when
each lies within a region of the caller's (`P k`), these are apart, and the
code may read them (and write those it writes) (`Ctx.of`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64

/-- A 16-byte chunk of a range a region contains. -/
theorem contains_chunk {P : Region} {b : Addr} {c j : Nat} (h : P.Contains b (16 * c)) (hj : j < c)
    (hc : 16 * c < 2 ^ 64) :
    P.Contains (b + BitVec.ofNat 64 (16 * j)) 16 := by
  unfold Region.Contains at *
  have hl : P.len < 2 ^ 64 ∨ 2 ^ 64 ≤ P.len := Nat.lt_or_ge _ _
  have hb := (b - P.base).isLt
  rw [show b + BitVec.ofNat 64 (16 * j) - P.base = (b - P.base) + BitVec.ofNat 64 (16 * j) by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 _),
      ← BitVec.add_assoc], BitVec.toNat_add, BitVec.toNat_ofNat]
  have : 16 * j < 2 ^ 64 := by omega_using [hj, hc]
  rw [Nat.mod_eq_of_lt this]
  have : (b - P.base).toNat + 16 * j < 2 ^ 64 ∨ 2 ^ 64 ≤ (b - P.base).toNat + 16 * j := Nat.lt_or_ge _ _
  rcases this with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]; omega_using [h, hj]
  · omega_using [h, hj]

theorem Ctx.of {rs : List Rg} {s₀ : State} (P : Nat → Region) (hlen : rs.length ≤ 16)
    (hsmall : ∀ k < rs.length, (rs.getD k default).off + 16 * chunks rs k < 2 ^ 32)
    (hcont : ∀ k < rs.length, (P k).Contains (rbase rs s₀ k) (16 * chunks rs k))
    (hrd : ∀ k < rs.length, ∀ a, (P k).Contains a 16 → InRegions (s₀.rd ++ s₀.wr) a 16)
    (hwr : ∀ k < rs.length, (rs.getD k default).wr = true → ∀ a, (P k).Contains a 16 → InRegions s₀.wr a 16)
    (hdisj : ∀ k k', k < rs.length → k' < rs.length → k ≠ k' → (P k).Disjoint (P k')) : Ctx rs s₀ := by
  have hc : ∀ k < rs.length, 16 * chunks rs k < 2 ^ 64 := fun k hk => by have := hsmall k hk; omega_using [this]
  refine ⟨hlen, hsmall, fun k hk j hj => hrd k hk _ (contains_chunk (hcont k hk) hj (hc k hk)),
    fun k hk hw j hj => hwr k hk hw _ (contains_chunk (hcont k hk) hj (hc k hk)),
    fun k j k' j' hk hj hk' hj' hne => ?_⟩
  by_cases hkk : k = k'
  · subst hkk
    have hj' : j ≠ j' := fun e => hne ⟨rfl, e⟩
    have hs := hsmall k hk
    unfold caddr
    exact Offset.sep _ (by omega_using [hne]) (by omega_using [hj, hs]) (by omega_arith)
  · exact (hdisj k k' hk hk' hkk).sep (contains_chunk (hcont k hk) hj (hc k hk))
      (contains_chunk (hcont k' hk') hj' (hc k' hk'))

end VG.Proof.MlKem.AArch64.NttR

end

end

/-!
# ML-KEM on AArch64: the 16-bit NTTs of a polynomial stored with 16 bits, their inputs

The coefficients of the polynomial at `x0` (`Wi`), and those of a reduced
polynomial represent themselves (`lrep_red`), for the runs of
`vg_mlkem16_ntt` and `vg_mlkem16_inv_ntt` (`FwdF`, `InvFI`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Ntt16 (hw4 vhalf_table LRep)

/-- The input's coefficients. -/
def Wi (s₀ : State) (p : Nat) : BitVec 16 := coeffAtW 16 s₀.mem (s₀.gpr .x0) p

/-- The coefficients of a reduced polynomial represent themselves. -/
theorem lrep_red {m : Mem} {p : Addr} (h : ReducedW 16 m p) {i : Nat} (hi : i < 256) :
    LRep (coeffAtW 16 m p i) (polyAtW 16 m p)[i]! 3329 := by
  have hv := polyIsW16_toNat (⟨h, rfl⟩ : PolyIsW 16 m p (polyAtW 16 m p)) hi
  have hl : (coeffAtW 16 m p i).toNat < 3329 := h i hi
  have hz : ((polyAtW 16 m p)[i]!).val < 3329 := ((polyAtW 16 m p)[i]!).isLt
  rw [LRep, BitVec.toInt_eq_toNat_of_lt (by omega_using [hl]), hv]
  exact ⟨by omega_using [], by omega_using [hz], by simp⟩

end VG.Proof.MlKem.AArch64.NttR

end

end

/-! ### `MlKem.AArch64.NttR.FwdF`, which only this module used -/

section

/-!
# ML-KEM on AArch64: `vg_mlkem16_ntt` (mlkem-native's schedule), by the machine

`Impl.MlKem.AArch64.Ntt16.Fast.fwdFast` transforms the polynomial at `x0`
(`fwdF_run`): the machine's state at the start (`initF`) holds of the
caller's (`initF_rel`), in regions that are apart (`ctxF`), and its run
(`checkF_ok`) leaves the reduced coefficients of `NTT` in the polynomial.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16.Fast
open VG.Proof.MlKem.AArch64.Ntt16 (hw4 vhalf_table)

/-- What `fwdFast` needs of the state it starts from: the polynomial at `x0`,
writable and reduced, and the table, readable and apart from it. -/
structure InF (s : State) : Prop where
  wr : (⟨s.gpr .x0, 512⟩ : Region) ∈ s.wr
  red : ReducedW 16 s.mem (s.gpr .x0)
  table : ∀ j < 116, s.mem.readW (s.syms name + BitVec.ofNat 64 (8 * j)) 64 = hw4 tab j
  readable : Covers [⟨s.syms name, 928⟩] (s.rd ++ s.wr)
  apart : Region.Disjoint ⟨s.gpr .x0, 512⟩ ⟨s.syms name, 928⟩

/-- The regions of `rsF`. -/
def regF (s₀ : State) : List Region := [⟨s₀.gpr .x0, 512⟩, ⟨s₀.syms name, 928⟩]

theorem ctxF {s₀ : State} (hi : InF s₀) : Ctx rsF s₀ := by
  have h2 : rsF.length = 2 := rfl
  have cases2 : ∀ k < rsF.length, k = 0 ∨ k = 1 := fun k hk => by rw [h2] at hk; omega_using [hk]
  refine Ctx.of (fun k => (regF s₀).getD k ⟨0, 0⟩) (by decide) (fun k hk => ?_) (fun k hk => ?_)
    (fun k hk a ha => ?_) (fun k hk hw a ha => ?_) (fun k k' hk hk' hne => ?_)
  · rcases cases2 k hk with rfl | rfl <;> decide
  · rcases cases2 k hk with rfl | rfl <;> exact contains_off (by decide) (by decide)
  · rcases cases2 k hk with rfl | rfl
    · exact in_rd_wr (in_regions hi.wr ha)
    · exact hi.readable _ _ (in_regions (List.mem_singleton_self _) ha)
  · rcases cases2 k hk with rfl | rfl
    · exact in_regions hi.wr ha
    · exact absurd hw (by decide)
  · rcases cases2 k hk with rfl | rfl <;> rcases cases2 k' hk' with rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | exact hi.apart | exact hi.apart.symm

theorem initF_rel {s₀ : State} (hi : InF s₀) : Rel rsF s₀ (Lf (Wi s₀)) (Of (Wi s₀)) initF s₀ := by
  refine ⟨fun r e he => ?_, fun r => ?_, fun k hk j hj e he => ?_, rfl, rfl, rfl, rfl⟩
  · have : (initF.vreg r).get e = junkT := by
      show slot tw (slot yw 0 (vi r)) e = 0
      rw [slot_zero, slot_zero]
    rw [this]; exact Hd.junk _
  · unfold initF
    rw [greg_setG]
    by_cases h0 : r = .x0
    · subst h0
      rw [ite_eq_left rfl]
      exact GHd.code (rs := rsF) ⟨by decide, by decide, by decide, by
        show s₀.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 0
        rw [ptr_zero, ptr_zero]⟩
    · rw [ite_eq_right h0]
      show GHd rsF s₀ (G.ofCode (slot gw 0 (gi r))) _
      rw [slot_zero]
      trivial
  · have h2 : rsF.length = 2 := rfl
    rcases (by omega_using [hk, h2] : k = 0 ∨ k = 1) with rfl | rfl
    · have hj' : j < 32 := hj
      rw [initF_f j hj' e he]
      refine (Hd.mk (by decide)).2 ?_
      rw [eval_mk, Nat.zero_mod, Nat.mod_eq_of_lt (show 8 * j + e < 512 by omega_using [he, hj'])]
      apply BitVec.eq_of_toNat_eq
      show (vhalf (s₀.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * j)) 16) e).toNat = _
      rw [ptr_zero, show 16 * j = 2 * (8 * j) by omega_using [], vhalf_read_coeff _ _ _ he]
      rfl
    · have hj' : j < 58 := hj
      have ea : caddr rsF s₀ 1 j = s₀.syms name + BitVec.ofNat 64 (0 + 16 * j) := by
        show s₀.syms name + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * j) = _
        rw [ptr_zero, Nat.zero_add]
      have hv := vhalf_table (m := s₀.mem) (p := s₀.syms name) (off := 0) (N := 116)
        (H := tab) (fun j hj => by rw [Nat.zero_add]; exact hi.table j hj) (i := j) (by omega_using [hj']) he
      rw [initF_t hj' he, ea, hv]
      exact Hd.cT _

theorem fwdF_run (s₀ : State) (hi : InF s₀) :
    WP isa fwdFast s₀ fun s' =>
      s'.sp = s₀.sp ∧ PolyIsW 16 s'.mem (s₀.gpr .x0) (ntt (polyAtW 16 s₀.mem (s₀.gpr .x0))) := by
  have hc := checkF_ok
  generalize hx : initF.runP fwdRules rsF 16 fwdFast = x at hc
  cases x with
  | none => cases hc
  | some σ =>
    have hout : ∀ j < 32, ∀ e < 8, (σ.chunk 0 j).get e = outT (8 * j + e) := by
      simpa only [Option.elim, outW, List.all_eq_true, List.mem_range, Nat.beq_eq] using hc
    refine WP.mono (runP_ok (model (Wi s₀)) (ctxF hi) 16 _ (initF_rel hi) hx) fun s' h' => ⟨h'.sp, ?_⟩
    refine polyIsW_of_toNat fun i hi' => ?_
    have hi256 : i < 256 := hi'
    have hm := h'.mem 0 (by decide) (i / 8) (by show i / 8 < 32; omega_using [hi256]) (i % 8) (Nat.mod_lt _ (by decide))
    rw [hout _ (by omega_using [hi256]) _ (Nat.mod_lt _ (by decide)), show 8 * (i / 8) + i % 8 = i by omega_using []] at hm
    have hv := (Hd.mk (by decide)).1 hm
    rw [eval_mk, Nat.mod_eq_of_lt (show i < 512 by omega_using [hi256])] at hv
    have hr := vhalf_read_coeff s'.mem (s₀.gpr .x0) (8 * (i / 8)) (Nat.mod_lt i (show 0 < 8 by decide))
    rw [show 8 * (i / 8) + i % 8 = i by omega_using [], show 2 * (8 * (i / 8)) = 16 * (i / 8) by omega_using []] at hr
    rw [← hr]
    change (vhalf (s'.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * (i / 8))) 16)
      (i % 8)) = _ at hv
    rw [ptr_zero] at hv
    rw [hv]
    exact Of_ntt (Wi s₀) _ (fun p hp => lrep_red hi.red hp) hi256

end VG.Proof.MlKem.AArch64.NttR

end

end

/-! ### `MlKem.AArch64.NttR.InvFI`, which only this module used -/

section

/-!
# ML-KEM on AArch64: `vg_mlkem16_inv_ntt` (mlkem-native's schedule), by the machine

`Impl.MlKem.AArch64.Ntt16.FastInv.invFast` transforms the polynomial at `x0`
(`invFI_run`): the machine's state at the start (`initFI`) holds of the
caller's (`initFI_rel`), in regions that are apart (`ctxFII`), and its run
(`checkFI_ok`) leaves the reduced coefficients of `NTT⁻¹` in the polynomial.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16.FastInv
open VG.Proof.MlKem.AArch64.Ntt16 (hw4 vhalf_table)

/-- What `invFast` needs of the state it starts from: the polynomial at `x0`,
writable and reduced, and the table, readable and apart from it. -/
structure InFI (s : State) : Prop where
  wr : (⟨s.gpr .x0, 512⟩ : Region) ∈ s.wr
  red : ReducedW 16 s.mem (s.gpr .x0)
  table : ∀ j < 116, s.mem.readW (s.syms name + BitVec.ofNat 64 (8 * j)) 64 = hw4 tab j
  readable : Covers [⟨s.syms name, 928⟩] (s.rd ++ s.wr)
  apart : Region.Disjoint ⟨s.gpr .x0, 512⟩ ⟨s.syms name, 928⟩

/-- The regions of `rsFI`. -/
def regFI (s₀ : State) : List Region := [⟨s₀.gpr .x0, 512⟩, ⟨s₀.syms name, 928⟩]

theorem ctxFI {s₀ : State} (hi : InFI s₀) : Ctx rsFI s₀ := by
  have h2 : rsFI.length = 2 := rfl
  have cases2 : ∀ k < rsFI.length, k = 0 ∨ k = 1 := fun k hk => by rw [h2] at hk; omega_using [hk]
  refine Ctx.of (fun k => (regFI s₀).getD k ⟨0, 0⟩) (by decide) (fun k hk => ?_) (fun k hk => ?_)
    (fun k hk a ha => ?_) (fun k hk hw a ha => ?_) (fun k k' hk hk' hne => ?_)
  · rcases cases2 k hk with rfl | rfl <;> decide
  · rcases cases2 k hk with rfl | rfl <;> exact contains_off (by decide) (by decide)
  · rcases cases2 k hk with rfl | rfl
    · exact in_rd_wr (in_regions hi.wr ha)
    · exact hi.readable _ _ (in_regions (List.mem_singleton_self _) ha)
  · rcases cases2 k hk with rfl | rfl
    · exact in_regions hi.wr ha
    · exact absurd hw (by decide)
  · rcases cases2 k hk with rfl | rfl <;> rcases cases2 k' hk' with rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | exact hi.apart | exact hi.apart.symm

theorem initFI_rel {s₀ : State} (hi : InFI s₀) : Rel rsFI s₀ (Lfi (Wi s₀)) (Ofi (Wi s₀)) initFI s₀ := by
  refine ⟨fun r e he => ?_, fun r => ?_, fun k hk j hj e he => ?_, rfl, rfl, rfl, rfl⟩
  · have : (initFI.vreg r).get e = junkT := by
      show slot tw (slot yw 0 (vi r)) e = 0
      rw [slot_zero, slot_zero]
    rw [this]; exact Hd.junk _
  · unfold initFI
    rw [greg_setG]
    by_cases h0 : r = .x0
    · subst h0
      rw [ite_eq_left rfl]
      exact GHd.code (rs := rsFI) ⟨by decide, by decide, by decide, by
        show s₀.gpr .x0 = s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 0
        rw [ptr_zero, ptr_zero]⟩
    · rw [ite_eq_right h0]
      show GHd rsFI s₀ (G.ofCode (slot gw 0 (gi r))) _
      rw [slot_zero]
      trivial
  · have h2 : rsFI.length = 2 := rfl
    rcases (by omega_using [hk, h2] : k = 0 ∨ k = 1) with rfl | rfl
    · have hj' : j < 32 := hj
      rw [initFI_f j hj' e he]
      refine (Hd.mk (by decide)).2 ?_
      rw [eval_mk, Nat.zero_mod, Nat.mod_eq_of_lt (show 8 * j + e < 512 by omega_using [he, hj'])]
      apply BitVec.eq_of_toNat_eq
      show (vhalf (s₀.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * j)) 16) e).toNat = _
      rw [ptr_zero, show 16 * j = 2 * (8 * j) by omega_using [], vhalf_read_coeff _ _ _ he]
      rfl
    · have hj' : j < 58 := hj
      have ea : caddr rsFI s₀ 1 j = s₀.syms name + BitVec.ofNat 64 (0 + 16 * j) := by
        show s₀.syms name + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * j) = _
        rw [ptr_zero, Nat.zero_add]
      have hv := vhalf_table (m := s₀.mem) (p := s₀.syms name) (off := 0) (N := 116)
        (H := tab) (fun j hj => by rw [Nat.zero_add]; exact hi.table j hj) (i := j) (by omega_using [hj']) he
      rw [initFI_t hj' he, ea, hv]
      exact Hd.cT _

theorem invFI_run (s₀ : State) (hi : InFI s₀) :
    WP isa invFast s₀ fun s' =>
      s'.sp = s₀.sp ∧ PolyIsW 16 s'.mem (s₀.gpr .x0) (nttInv (polyAtW 16 s₀.mem (s₀.gpr .x0))) := by
  have hc := checkFI_ok
  generalize hx : initFI.runP fastInvRules rsFI 16 invFast = x at hc
  cases x with
  | none => cases hc
  | some σ =>
    have hout : ∀ j < 32, ∀ e < 8, (σ.chunk 0 j).get e = outT (8 * j + e) := by
      simpa only [Option.elim, outW, List.all_eq_true, List.mem_range, Nat.beq_eq] using hc
    refine WP.mono (runP_ok (modelFI (Wi s₀)) (ctxFI hi) 16 _ (initFI_rel hi) hx) fun s' h' => ⟨h'.sp, ?_⟩
    refine polyIsW_of_toNat fun i hi' => ?_
    have hi256 : i < 256 := hi'
    have hm := h'.mem 0 (by decide) (i / 8) (by show i / 8 < 32; omega_using [hi256]) (i % 8) (Nat.mod_lt _ (by decide))
    rw [hout _ (by omega_using [hi256]) _ (Nat.mod_lt _ (by decide)), show 8 * (i / 8) + i % 8 = i by omega_using []] at hm
    have hv := (Hd.mk (by decide)).1 hm
    rw [eval_mk, Nat.mod_eq_of_lt (show i < 512 by omega_using [hi256])] at hv
    have hr := vhalf_read_coeff s'.mem (s₀.gpr .x0) (8 * (i / 8)) (Nat.mod_lt i (show 0 < 8 by decide))
    rw [show 8 * (i / 8) + i % 8 = i by omega_using [], show 2 * (8 * (i / 8)) = 16 * (i / 8) by omega_using []] at hr
    rw [← hr]
    change (vhalf (s'.mem.read (s₀.gpr .x0 + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * (i / 8))) 16)
      (i % 8)) = _ at hv
    rw [ptr_zero] at hv
    rw [hv]
    exact Ofi_nttInv (Wi s₀) _ (fun p hp => lrep_red hi.red hp) hi256

end VG.Proof.MlKem.AArch64.NttR

end

end

/-! ### `MlKem.AArch64.NttR.AbiFI`, which only this module used -/

section

/-!
# ML-KEM on AArch64: `vg_mlkem16_inv_ntt` keeps what the ABI preserves

`invFast` keeps the low halves of `v8`–`v15` in `x7`–`x14` (`save`), which
the transform (`core`) does not write, and puts them back at the end
(`Fast.restore`); it writes none of `x19`–`x28` and `x30`, and leaves `sp` alone.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Impl.MlKem.AArch64.Ntt16.FastInv

theorem saveI_eq : save = umovOf lanesF ++ ([.adrSym .x1 name, .addImm .x .x2 .x1 160] : List Instr) := rfl

theorem saveI_ok (s : State) :
    WP isa (.block save) s fun t => ∀ k ∈ lanesF, t.gpr k.1 = laneOf s k.2.1 k.2.2 := by
  rw [saveI_eq]
  refine WP.block_append (WP.mono (umovOf_ok lanesF s (by decide) (by decide)) fun t ⟨_, _, _, _, ht, _⟩ => ?_)
  refine WP.block_cons_iff.mpr ⟨_, exec_adrSym, WP.block_cons_iff.mpr ⟨_, exec_addImm_x (imm := 160) (by decide), WP.block_nil ?_⟩⟩
  intro k hk
  have h1 : k.1 ≠ .x1 := by revert k; decide
  have h2 : k.1 ≠ .x2 := by revert k; decide
  rw [RegUpd.gpr_write_of_ne (s := _) _ _ h2, RegUpd.gpr_write_of_ne (s := _) _ _ h1]
  exact ht k hk

/-- No instruction of `core` writes `x7`–`x14`. -/
theorem coreI_keeps : core.allInstrs (fun i => lanesF.all fun k => !clobbers i k.1) = true := by
  decide +kernel

/-- No instruction of `invFast` writes `x19`–`x28` or `x30`. -/
theorem invFast_keeps : invFast.allInstrs (fun i => preserved.all fun r => !clobbers i r) = true := by
  lit_decide

theorem invFast_abi {s s' : State} {t : List Leak} (he : Exec isa invFast s t s') : abiPreserved s s' := by
  refine ⟨fun r hr => Exec.gpr (fun i hi => ?_) he, Exec.sp he, fun r hr => ?_⟩
  · have := List.all_eq_true.mp ((Code.allInstrs_eq _ invFast) ▸ invFast_keeps) i hi
    simpa using List.all_eq_true.mp this r hr
  · cases he with
    | seq h1 h23 =>
    cases h23 with
    | seq h2 h3 =>
    obtain ⟨_, t1, e1, hs⟩ := saveI_ok s
    have hk : ∀ k ∈ lanesF, ∀ i ∈ instrs core, clobbers i k.1 = false := fun k hk i hi => by
      have := List.all_eq_true.mp ((Code.allInstrs_eq _ core) ▸ coreI_keeps) i hi
      simpa using List.all_eq_true.mp this k hk
    rw [restore_eq] at h3
    obtain ⟨_, t3, e3, -, -, -, -, -, h3l, -⟩ := insOf_ok lanesF _ (by decide) (by decide)
    rw [← (Exec.det h3 e3).2] at h3l
    rw [← (Exec.det h1 e1).2] at hs
    have hl : ∀ k ∈ lanesF, laneOf s' k.2.1 k.2.2 = laneOf s k.2.1 k.2.2 := fun k hkm => by
      rw [h3l k hkm, Exec.gpr (hk k hkm) h2, hs k hkm]
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hl (.x7, .v8, 0) (by decide) | exact hl (.x8, .v9, 0) (by decide)
      | exact hl (.x9, .v10, 0) (by decide) | exact hl (.x10, .v11, 0) (by decide)
      | exact hl (.x11, .v12, 0) (by decide) | exact hl (.x12, .v13, 0) (by decide)
      | exact hl (.x13, .v14, 0) (by decide) | exact hl (.x14, .v15, 0) (by decide)

end VG.Proof.MlKem.AArch64.NttR

end

end

/-!
# ML-KEM on AArch64: the 16-bit NTT and its inverse of polynomials stored with 16 bits, at offsets

`vg_mlkem16_ntt` and `vg_mlkem16_inv_ntt` called on the polynomial at an offset of `x28`
(`nttAtWithW_ok`, `nttInvAtWithW_ok`). The polynomial and the working space are 512 bytes
each.
-/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/NttR/CallF.lean`, which only this module imported.
section

/-!
# ML-KEM on AArch64: calling `vg_mlkem16_ntt`

`fwdFast` as a callee: correct under its own contract (`fastC`), and its
call on the polynomial at `f` (`ntt16_call`), with the table as `FastReady`
says.
-/

section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16.Fast (fwdFast name)

/-- `fwdFast`'s contract as the code sees it. -/
def fastC : Contract isa where
  pre s := InF s
  post s t := PolyIsW 16 t.mem (s.gpr .x0) (ntt (polyAtW 16 s.mem (s.gpr .x0)))
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.syms name = t.syms name

theorem fastC_correct (s : State) (h : fastC.pre s) :
    ∃ tr t, Exec isa fwdFast s tr t ∧ abiPreserved s t ∧ fastC.post s t := by
  obtain ⟨tr, t, he, -, hp⟩ := fwdF_run s h
  exact ⟨tr, t, he, fwdFast_abi he, hp⟩

/-- `vg_mlkem16_ntt(f, _)`: `NTT` of the polynomial with 16-bit coefficients at `f`. -/
theorem ntt16_call {s : State} {f : Addr} (h0 : s.gpr .x0 = f) (hr : ReducedW 16 s.mem f)
    (hw : Covers [⟨f, 512⟩] s.wr) {w : Addr} (ht : FastReady s f w) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 512⟩] s s' → PolyIsW 16 s'.mem f (ntt (polyAtW 16 s.mem f)) → Q s') :
    WP isa (.call "vg_mlkem16_ntt" fwdFast) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  refine WP.callV (k := fastC) fastC_correct (rd := [fastRegion s]) (wr := [⟨f, 512⟩]) ?_
    (ht.readable.append_left hw.right) hw ?_
  · have hsy : (s.callEntry.withRegions [fastRegion s] [⟨f, 512⟩]).syms = s.syms := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_wr, State.withRegions_gpr, c0]; exact List.mem_singleton_self _
    · simpa only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr, c0] using hr
    · simpa only [State.withRegions_mem, State.callEntry_mem, hsy] using ht.table
    · simp only [State.withRegions_rd, State.withRegions_wr, hsy]
      exact Covers.of_mem (fun r h => List.mem_append_left _ h)
    · simpa only [State.withRegions_gpr, hsy, c0] using ht.output.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024))
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [fastC, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

end VG.Proof.MlKem.AArch64.NttR
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/NttR/CallFI.lean`, which only this module imported.
section

/-!
# ML-KEM on AArch64: calling `vg_mlkem16_inv_ntt`

`invFast` as a callee: correct under its own contract (`fastInvC`), and its
call on the polynomial at `f` (`nttInv16_call`), with the table as
`FastInvReady` says.
-/

section

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16.FastInv (invFast name)

/-- `invFast`'s contract as the code sees it. -/
def fastInvC : Contract isa where
  pre s := InFI s
  post s t := PolyIsW 16 t.mem (s.gpr .x0) (nttInv (polyAtW 16 s.mem (s.gpr .x0)))
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧ s.syms name = t.syms name

theorem fastInvC_correct (s : State) (h : fastInvC.pre s) :
    ∃ tr t, Exec isa invFast s tr t ∧ abiPreserved s t ∧ fastInvC.post s t := by
  obtain ⟨tr, t, he, -, hp⟩ := invFI_run s h
  exact ⟨tr, t, he, invFast_abi he, hp⟩

/-- `vg_mlkem16_inv_ntt(f, _)`: `NTT⁻¹` of the polynomial with 16-bit coefficients at `f`. -/
theorem nttInv16_call {s : State} {f : Addr} (h0 : s.gpr .x0 = f) (hr : ReducedW 16 s.mem f)
    (hw : Covers [⟨f, 512⟩] s.wr) {w : Addr} (ht : FastInvReady s f w) {Q : State → Prop}
    (hQ : ∀ s', Kept [⟨f, 512⟩] s s' → PolyIsW 16 s'.mem f (nttInv (polyAtW 16 s.mem f)) → Q s') :
    WP isa (.call "vg_mlkem16_inv_ntt" invFast) s Q := by
  have c0 : s.callEntry.gpr .x0 = f := (entry s).trans h0
  refine WP.callV (k := fastInvC) fastInvC_correct (rd := [fastInvRegion s]) (wr := [⟨f, 512⟩]) ?_
    (ht.readable.append_left hw.right) hw ?_
  · have hsy : (s.callEntry.withRegions [fastInvRegion s] [⟨f, 512⟩]).syms = s.syms := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.withRegions_wr, State.withRegions_gpr, c0]; exact List.mem_singleton_self _
    · simpa only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr, c0] using hr
    · simpa only [State.withRegions_mem, State.callEntry_mem, hsy] using ht.table
    · simp only [State.withRegions_rd, State.withRegions_wr, hsy]
      exact Covers.of_mem (fun r h => List.mem_append_left _ h)
    · simpa only [State.withRegions_gpr, hsy, c0] using ht.output.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024))
  · intro s' hrd hwr hsp hf hcs _ hvec hpost
    simp only [fastInvC, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c0] at hpost
    exact hQ s' ⟨hcs, hsp, hrd, hwr, hf, hvec⟩ hpost

end VG.Proof.MlKem.AArch64.NttR
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.W
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Ntt16
open VG.Impl.MlKem.AArch64.Ntt16

theorem nttAtWithW_ok {s : State} {off ns : Nat} {f w : Addr} {F : Poly}
    (hoff : off<65536) (hns : ns<65536)
    (hf : s.gpr .x28+BitVec.ofNat 64 off=f) (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
    (_hd : (Region.mk f 512).Disjoint ⟨w,512⟩) (hp : PolyIsW 16 s.mem f F)
    (hc : Covers [⟨f,512⟩,⟨w,512⟩] s.wr) (ht : NttR.FastReady s f w) :
    WP isa (Impl.MlKem.AArch64.Ntt16.Readonly.nttAtWithW off ns) s fun t=>
      Kept [⟨f,512⟩,⟨w,512⟩] s t ∧ PolyIsW 16 t.mem f (ntt F) := by
  have prep : WP isa (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 off ++ Impl.MlKem.AArch64.ptrTo .x1 .x28 ns)) s
      fun z=>Only [.x0,.x1] s z ∧ z.gpr .x0=f ∧ z.gpr .x1=w := by
    refine wp_ptrTo (by decide) hoff fun a ha ea=>wp_ptrTo' (by decide) hns fun z hz ez=>?_
    exact ⟨(ha.trans hz).mono (by simp),by rw [hz.get .x0 (by decide),ea]; exact hf,
      by rw [ez,ha.get .x28 (by decide)]; exact hw⟩
  refine WP.seq (WP.mono_syms prep fun z ⟨oz,z0,_⟩ zs=>?_)
  have table : NttR.FastReady z f w :=
    ⟨by simpa only [zs,oz.mem] using ht.table,
      by simpa only [NttR.sRegion,zs,oz.rd,oz.wr] using ht.readable,
      by simpa only [NttR.sRegion,zs] using ht.output,by simpa only [NttR.sRegion,zs] using ht.scratch⟩
  exact NttR.ntt16_call z0 (by rw [oz.mem]; exact hp.1) (by rw [oz.wr]; exact Covers.head hc) table
    fun t kt pt=>⟨(Kept.of_keep oz.keep oz.mem (by decide)).trans
      (kt.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self),
      by simpa only [oz.mem,hp.2] using pt⟩

theorem nttInvAtWithW_ok {s : State} {off ns : Nat} {f w : Addr} {F : Poly}
    (hoff : off<65536) (hns : ns<65536)
    (hf : s.gpr .x28+BitVec.ofNat 64 off=f) (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
    (_hd : (Region.mk f 512).Disjoint ⟨w,512⟩) (hp : PolyIsW 16 s.mem f F)
    (hc : Covers [⟨f,512⟩,⟨w,512⟩] s.wr) (ht : NttR.FastInvReady s f w) :
    WP isa (Impl.MlKem.AArch64.Ntt16.Readonly.nttInvAtWithW off ns) s fun t=>
      Kept [⟨f,512⟩,⟨w,512⟩] s t ∧ PolyIsW 16 t.mem f (nttInv F) := by
  have prep : WP isa (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 off ++ Impl.MlKem.AArch64.ptrTo .x1 .x28 ns)) s
      fun z=>Only [.x0,.x1] s z ∧ z.gpr .x0=f ∧ z.gpr .x1=w := by
    refine wp_ptrTo (by decide) hoff fun a ha ea=>wp_ptrTo' (by decide) hns fun z hz ez=>?_
    exact ⟨(ha.trans hz).mono (by simp),by rw [hz.get .x0 (by decide),ea]; exact hf,
      by rw [ez,ha.get .x28 (by decide)]; exact hw⟩
  refine WP.seq (WP.mono_syms prep fun z ⟨oz,z0,_⟩ zs=>?_)
  have table : NttR.FastInvReady z f w :=
    ⟨by simpa only [zs,oz.mem] using ht.table,
      by simpa only [NttR.sRegion,zs,oz.rd,oz.wr] using ht.readable,
      by simpa only [NttR.sRegion,zs] using ht.output,by simpa only [NttR.sRegion,zs] using ht.scratch⟩
  exact NttR.nttInv16_call z0 (by rw [oz.mem]; exact hp.1) (by rw [oz.wr]; exact Covers.head hc) table
    fun t kt pt=>⟨(Kept.of_keep oz.keep oz.mem (by decide)).trans
      (kt.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self),
      by simpa only [oz.mem,hp.2] using pt⟩

end VG.Proof.MlKem.AArch64.Ntt16.W
