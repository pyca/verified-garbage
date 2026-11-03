module

public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.Sound
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block

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
  simp only [Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega), hi, ite_true]

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
    refine ⟨hk', by have := hc.len; omega, by omega, ?_⟩
    unfold rbase
    rw [hb, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add, ho']
  · exact ⟨hk, by have := hc.len; omega, ho, rfl⟩

theorem GHd.addG {rs : List Rg} {s₀ : State} (hc : Ctx rs s₀) {g : G} {v : BitVec 64} (h : GHd rs s₀ g v)
    (imm : Nat) : GHd rs s₀ (addG rs g imm) (v + BitVec.ofNat 64 imm) := by
  cases g with
  | junk => trivial
  | num n =>
    obtain ⟨-, rfl⟩ := h
    refine ⟨Nat.mod_lt _ (by decide), ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
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
    omega
  | ptr k o =>
    obtain ⟨hk, -, ho, rfl⟩ := h
    simp only [NttR.subG]
    split
    · rename_i hle
      have e : BitVec.ofNat 64 o = BitVec.ofNat 64 (o - imm) + BitVec.ofNat 64 imm := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hle]
      rw [e, ← BitVec.add_assoc, BitVec.add_sub_cancel]
      exact rbase_norm hc hk (by omega)
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
        · unfold chunks; omega
        · unfold caddr rbase
          rw [hb, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
            ← BitVec.ofNat_add, show 16 * (o' / 16) = o' by omega, ho', Nat.add_assoc]
      · simp [h16] at hk

theorem chunk_none {σ : St} {k j : Nat} (hk : ¬ k < σ.mem.length) (e : Nat) : (σ.chunk k j).get e = 0 := by
  unfold St.chunk Y.get
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hk), Option.getD_none]
  simp only [slot, ndiv, nmod, Nat.zero_div, Nat.zero_mod]


theorem exec_ldrq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp [exec, addr, State.load, hr, ho.1, show off < 4096 * 16 by omega]

theorem exec_strq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (hr : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp [exec, addr, State.store, hr, ho.1, show off < 4096 * 16 by omega]

theorem movz_val (imm : BitVec 16) {hw : Nat} (hw4 : hw < 4) :
    imm.setWidth 64 <<< (16 * hw) = BitVec.ofNat 64 (imm.toNat * 2 ^ (16 * hw)) ∧
      imm.toNat * 2 ^ (16 * hw) < 2 ^ 64 := by
  have hi := imm.isLt
  have hp : imm.toNat * 2 ^ (16 * hw) < 2 ^ 64 := by
    calc imm.toNat * 2 ^ (16 * hw) < 2 ^ 16 * 2 ^ (16 * hw) := Nat.mul_lt_mul_of_pos_right hi (Nat.two_pow_pos _)
      _ = 2 ^ (16 + 16 * hw) := (Nat.pow_add ..).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨?_, hp⟩
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show imm.toNat < 2 ^ 64 by omega)]

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
      refine ⟨_, by simp only [exec, show 16 * hw < Size.bits .x by simp [Size.bits]; omega, ite_true],
        h.setG (g := .num _) ⟨hp, e⟩⟩
    · cases hs
  case umov sz d n i =>
    cases sz <;> simp only [St.step, reduceCtorEq] at hs
    split at hs
    · rename_i hi
      simp only [Option.some.injEq] at hs; subst hs
      exact ⟨_, by simp only [exec, Size.bits, show i * 64 < 128 by omega, ite_true]; rfl, h.setG (g := .junk) trivial⟩
    · cases hs
  case adrSym d name =>
    simp only [St.step, Option.some.injEq] at hs; subst hs
    refine ⟨_, rfl, h.setG ?_⟩
    unfold symRegion
    split
    · rename_i k hk
      obtain ⟨hk, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hk
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      refine ⟨hk, by have := hc.len; omega, by decide, ?_⟩
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
                rw [chunk_none (by omega)]
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
