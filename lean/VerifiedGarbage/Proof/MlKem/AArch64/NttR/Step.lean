module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Target

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

theorem vi_inj {r r' : VReg} : vi r = vi r' ↔ r = r' := by
  cases r <;> cases r' <;> decide

theorem gi_inj {r r' : Reg} : gi r = gi r' ↔ r = r' := by
  cases r <;> cases r' <;> decide

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
    omega
  | ptr k o =>
    have := Nat.mod_lt o (show 0 < 2 ^ 32 by decide)
    have := Nat.mod_lt k (show 0 < 16 by decide)
    show 2 + 2 * (k % 16 + 16 * (o % 2 ^ 32)) < 2 ^ gw
    rw [show 2 ^ gw = 2 ^ 32 * 2 ^ 48 from rfl]
    omega

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
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      congr 1; omega
    rw [e]; exact ⟨hn, rfl⟩
  | ptr k o =>
    obtain ⟨hk, hk16, ho, rfl⟩ := h
    have e : G.ofCode (G.ptr k o).code = .ptr k o := by
      simp only [G.code, G.ofCode, Nat.mod_eq_of_lt hk16, Nat.mod_eq_of_lt ho]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      congr 1 <;> omega
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
