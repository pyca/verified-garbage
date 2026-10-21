module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec

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
    show 16 * e + i < 128 by omega, decide_true, Bool.true_and]
  by_cases h' : e = k
  · subst h'
    simp [hi, show ¬ 16 * e + i < 16 * e by omega, show 16 * e + i - 16 * e = i by omega,
      show i < 128 by omega]
  · rw [ite_eq_right h', getLsbD_vhalf _ _ hi]
    rcases (by omega : e < k ∨ k < e) with c | c
    · simp [show 16 * e + i < 16 * k by omega]
    · have : h.getLsbD (16 * e + i - 16 * k) = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp [show ¬ 16 * e + i < 16 * k by omega, show ¬ 16 * e + i - 16 * k < 16 by omega, this]

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

namespace VG.Proof.MlKem.AArch64.NttR

open VG VG.AArch64
open VG.Proof.MlKem.AArch64.Ntt16 (vhalf_ofVHalves vhalf_map2 eval_mulH)

section
variable {rs : List Rg} {s₀ : State} {L : Nat → Nat → BitVec 16} {O : Nat → BitVec 16}

theorem ofNat_mod16 (v : Nat) : BitVec.ofNat 16 (v % 65536) = BitVec.ofNat 16 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

theorem Hd.cT (v : Nat) : Hd L O (cT v) (BitVec.ofNat 16 v) := by
  refine (Hd.mk (by decide)).2 ?_
  rw [eval_mk]
  exact (ofNat_mod16 v).symm

theorem cT_lt (v : Nat) : @LT.lt Nat instLTNat (cT v) (2 ^ tw) := mk_lt_tw ..

theorem setWidth16 (v : Nat) : (BitVec.ofNat 64 v).setWidth 16 = BitVec.ofNat 16 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

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

theorem vop_ok {R : Rules} (hM : Model L O R) {σ σ' : St} {s : State} (h : Rel rs s₀ L O σ s) {o : VOp}
    (hs : σ.vop R o = some σ') : ∃ s', exec (.vop o) s = some s' ∧ Rel rs s₀ L O σ' s' := by
  cases o with
  | movi0 d =>
    simp only [St.vop, Option.some.injEq] at hs; subst hs
    refine ⟨_, exec_vop rfl, h.setV (ofFn_lt _) fun e he => ?_⟩
    rw [Y.get_dup _ he, Nat.mod_eq_of_lt (cT_lt 0), vhalf_zero']
    exact Hd.cT 0
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

end

end VG.Proof.MlKem.AArch64.NttR
