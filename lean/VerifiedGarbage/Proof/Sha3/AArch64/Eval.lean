module

public import VerifiedGarbage.Proof.Sha3.Forms
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Framework.AArch64.Straight
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.StraightV
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Keccak-f[1600] on AArch64: running a round's code over forms

`evalV` runs a block of bitwise vector instructions, and `evalS` one of
general instructions (with lanes spilled to vector registers or to the
stack), over the forms of `Forms.lean`: what the block computes from the
input lanes, in every register. `runV` and `runS` say that the machine runs
the block and that its registers hold those forms of the lanes they held.
-/

-- separate module: how any round's code runs over forms, apart from the rounds' own

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Eval

open VG VG.AArch64 VG.Proof.Sha3.Forms

/-- The forms known, by index. -/
abbrev File := List (Option Form)

theorem getD_set (e : File) (i j : Nat) (x : Option Form) :
    (e.set i x).getD j none = if i = j ∧ i < e.length then x else e.getD j none := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases hl : i < e.length
    · simp [hl]
    · simp [hl]
  · simp [h]

theorem getD_none {e : File} {i : Nat} (h : e.length ≤ i) : e.getD i none = none := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-! ## Vector code -/

def vget (e : File) (r : VReg) : Option Form := e.getD r.ctorIdx none
def vset (e : File) (r : VReg) (f : Form) : File := e.set r.ctorIdx (some f)

/-- The instruction's effect on the forms in the vector registers. -/
def stepV (e : File) : Instr → Option File
  | .vop (.logic .eor d n m) =>
    match vget e n, vget e m with
    | some a, some b => some (vset e d (a.xor b))
    | _, _ => none
  | .vop (.logic .bic d n m) =>
    match vget e n, vget e m with
    | some a, some b => (a.bic b).map (vset e d)
    | _, _ => none
  | .vop (.eor3 d n m a) =>
    match vget e n, vget e m, vget e a with
    | some x, some y, some z => some (vset e d ((x.xor y).xor z))
    | _, _, _ => none
  | .vop (.bcax d n m a) =>
    match vget e n, vget e m, vget e a with
    | some x, some y, some z => (y.bic z).map fun t => vset e d (x.xor t)
    | _, _, _ => none
  | .vop (.rax1 d n m) =>
    match vget e n, vget e m with
    | some a, some b => some (vset e d (a.xor (b.rot 1)))
    | _, _ => none
  | .vop (.xar d n m imm) =>
    if imm < 64 then
      match vget e n, vget e m with
      | some a, some b => some (vset e d ((a.xor b).rot ((64 - imm) % 64)))
      | _, _ => none
    else none
  | _ => none

def evalV : List Instr → File → Option File
  | [], e => some e
  | i :: is, e => match stepV e i with | some e' => evalV is e' | none => none

/-- Doubleword `q` of every vector register holds its form of the lanes `env q`. -/
def RelV (env : Nat → Nat → BitVec 64) (e : File) (s : State) : Prop :=
  ∀ r f, vget e r = some f → ∀ q < 2, Is (env q) f (vdword (s.v r) q)

/-- Only vector registers differ. -/
def OnlyV (s s' : State) : Prop := ∃ v, s' = { s with v := v }

theorem OnlyV.refl (s : State) : OnlyV s s := ⟨s.v, rfl⟩
theorem OnlyV.trans {s t u : State} : OnlyV s t → OnlyV t u → OnlyV s u := by
  rintro ⟨v, rfl⟩ ⟨w, rfl⟩; exact ⟨w, rfl⟩
theorem OnlyV.setV (s : State) (d : VReg) (x : BitVec 128) : OnlyV s (s.setV d x) := ⟨_, rfl⟩

theorem RelV.set {env : Nat → Nat → BitVec 64} {e : File} {s : State} (h : RelV env e s) {d : VReg} {f : Form}
    {x : BitVec 128} (hx : ∀ q < 2, Is (env q) f (vdword x q)) : RelV env (vset e d f) (s.setV d x) := by
  intro r g hg q hq
  simp only [vget, vset, getD_set] at hg
  rw [RegUpd.v_setV]
  split at hg
  · rename_i hd
    have : r = d := by
      have := hd.1
      rw [← VReg.ofNat_ctorIdx r, ← VReg.ofNat_ctorIdx d, this]
    subst this
    cases hg
    rw [ite_eq_left rfl]; exact hx q hq
  · rename_i hd
    by_cases hr : r = d
    · subst hr
      simp only [true_and, Nat.not_lt] at hd
      rw [getD_none hd] at hg; cases hg
    · rw [ite_eq_right hr]; exact h r g hg q hq

private theorem vop_ok {op : VOp} {s : State} {d : VReg} {x : BitVec 128} (h : op.eval s = some (d, x)) :
    exec (.vop op) s = some (s.setV d x) := by
  simp only [exec, h, Option.map_some]

theorem stepV_ok {env : Nat → Nat → BitVec 64} {e e' : File} {s : State} (hr : RelV env e s) {i : Instr}
    (h : stepV e i = some e') : ∃ s', exec i s = some s' ∧ RelV env e' s' ∧ OnlyV s s' := by
  unfold stepV at h
  split at h
  · split at h
    · rename_i d n m _ _ a b ha hb
      cases h
      exact ⟨_, vop_ok rfl, hr.set fun q hq => by
        rw [StraightV.vdword_xor]; exact (hr _ _ ha q hq).xor (hr _ _ hb q hq), .setV ..⟩
    · cases h
  · split at h
    · rename_i d n m _ _ a b ha hb
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨_, vop_ok rfl, hr.set fun q hq => by
        rw [StraightV.vdword_and, StraightV.vdword_not _ hq]
        exact (hr _ _ ha q hq).bic (hr _ _ hb q hq) ht, .setV ..⟩
    · cases h
  · split at h
    · rename_i d n m a _ _ _ x y z hx hy hz
      cases h
      exact ⟨_, vop_ok rfl, hr.set fun q hq => by
        rw [StraightV.vdword_xor, StraightV.vdword_xor]
        exact ((hr _ _ hx q hq).xor (hr _ _ hy q hq)).xor (hr _ _ hz q hq), .setV ..⟩
    · cases h
  · split at h
    · rename_i d n m a _ _ _ x y z hx hy hz
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨_, vop_ok rfl, hr.set fun q hq => by
        rw [StraightV.vdword_xor, StraightV.vdword_and, StraightV.vdword_not _ hq]
        exact (hr _ _ hx q hq).xor ((hr _ _ hy q hq).bic (hr _ _ hz q hq) ht), .setV ..⟩
    · cases h
  · split at h
    · rename_i d n m _ _ a b ha hb
      cases h
      exact ⟨_, vop_ok rfl, hr.set fun q hq => by
        rw [StraightV.vdword_map2 _ _ _ hq]
        exact (hr _ _ ha q hq).xor ((hr _ _ hb q hq).rot (by decide)), .setV ..⟩
    · cases h
  · split at h
    · rename_i d n m imm himm
      split at h
      · rename_i a b ha hb
        cases h
        exact ⟨_, vop_ok (by simp only [VOp.eval, himm, ite_true]; rfl), hr.set fun q hq => by
          rw [StraightV.vdword_map2 _ _ _ hq]
          exact ((hr _ _ ha q hq).xor (hr _ _ hb q hq)).ror himm, .setV ..⟩
      · cases h
    · cases h
  · cases h

theorem runV {env : Nat → Nat → BitVec 64} : ∀ (is : List Instr) {e e' : File} {s : State}, RelV env e s →
    evalV is e = some e' → ∃ s', runBlock isa is s = some s' ∧ RelV env e' s' ∧ OnlyV s s'
  | [], e, e', s, hr, h => by cases h; exact ⟨s, runBlock_nil, hr, .refl s⟩
  | i :: is, e, e', s, hr, h => by
    simp only [evalV] at h
    split at h
    · rename_i e₁ h₁
      obtain ⟨s₁, x₁, r₁, o₁⟩ := stepV_ok hr h₁
      obtain ⟨s', x', r', o'⟩ := runV is r₁ h
      exact ⟨s', by rw [runBlock_cons, x₁, runStep_some]; exact x', r', o₁.trans o'⟩
    · cases h

/-! ## General code -/

/-- Where lanes are spilled: the `n` doublewords from `[b, #(8 lo)]`. -/
structure Mode where
  b : Reg
  lo : Nat
  n : Nat

/-- The forms in the general registers and the slots. -/
structure Env where
  g : File
  sl : File

def gget (e : Env) (r : Reg) : Option Form := e.g.getD r.ctorIdx none
def gset (e : Env) (r : Reg) (f : Form) : Env := { e with g := e.g.set r.ctorIdx (some f) }
def sset (e : Env) (k : Nat) (f : Form) : Env := { e with sl := e.sl.set k (some f) }

/-- The instruction's effect on the forms in the general registers and the slots. -/
def stepS (m : Mode) (w : Nat) (e : Env) : Instr → Option Env
  | .logic .eor .x d n a =>
    if w.testBit d.ctorIdx then
      match gget e n, gget e a with
      | some x, some y => some (gset e d (x.xor y))
      | _, _ => none
    else none
  | .logicRor .eor .x d n a k =>
    if w.testBit d.ctorIdx ∧ k < 64 then
      match gget e n, gget e a with
      | some x, some y => some (gset e d (x.xor (y.rot ((64 - k) % 64))))
      | _, _ => none
    else none
  | .bicRor .x d n a k =>
    if w.testBit d.ctorIdx ∧ k < 64 then
      match gget e n, gget e a with
      | some x, some y => (x.bic (y.rot ((64 - k) % 64))).map (gset e d)
      | _, _ => none
    else none
  | .ror .x d n k =>
    if w.testBit d.ctorIdx ∧ k < 64 then
      match gget e n with
      | some x => some (gset e d (x.rot ((64 - k) % 64)))
      | none => none
    else none
  | .str .x r b off =>
    if b = m.b ∧ off % 8 = 0 ∧ m.lo ≤ off / 8 ∧ off / 8 < m.lo + m.n then
      match gget e r with | some x => some (sset e (off / 8 - m.lo) x) | none => none
    else none
  | .ldr .x r b off =>
    if w.testBit r.ctorIdx ∧ b = m.b ∧ off % 8 = 0 ∧ m.lo ≤ off / 8 ∧ off / 8 < m.lo + m.n then
      match e.sl.getD (off / 8 - m.lo) none with | some x => some (gset e r x) | none => none
    else none
  | _ => none

def evalS (m : Mode) (w : Nat) : List Instr → Env → Option Env
  | [], e => some e
  | i :: is, e => match stepS m w e i with | some e' => evalS m w is e' | none => none

/-- The base of the slots. -/
def slotBase (m : Mode) (s : State) : Addr := s.gpr m.b + BitVec.ofNat 64 (8 * m.lo)

/-- What slot `k` holds. -/
def slotVal (m : Mode) (s : State) (k : Nat) : BitVec 64 := s.mem.readW (Straight.wordAddr (slotBase m s) k) 64

/-- The slots are the code's. -/
def ModeOk (m : Mode) (s : State) : Prop :=
  m.lo + m.n ≤ 1024 ∧ ∀ k < m.n, InRegions s.wr (Straight.wordAddr (slotBase m s) k) 8

structure RelS (env : Nat → BitVec 64) (m : Mode) (e : Env) (s : State) : Prop where
  reg : ∀ r f, gget e r = some f → Is env f (s.gpr r)
  slot : ∀ k f, k < m.n → e.sl.getD k none = some f → Is env f (slotVal m s k)

/-- The memory the spills write. -/
def slotR (m : Mode) (s : State) : Region := ⟨slotBase m s, 8 * m.n⟩

/-- What a block of general code, writing the registers `w`, keeps. -/
structure KeepS (m : Mode) (w : Nat) (s s' : State) : Prop where
  gpr : ∀ r, w.testBit r.ctorIdx = false → s'.gpr r = s.gpr r
  v : s'.v = s.v
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  syms : s'.syms = s.syms
  frame : Frame [slotR m s] s.mem s'.mem

theorem KeepS.refl (m : Mode) (w : Nat) (s : State) : KeepS m w s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem slotBase_congr {m : Mode} {s s' : State} (h : s'.gpr m.b = s.gpr m.b) : slotBase m s' = slotBase m s := by
  simp only [slotBase, h]

theorem KeepS.trans {m : Mode} {w : Nat} (hb : w.testBit m.b.ctorIdx = false) {s t u : State} (h : KeepS m w s t)
    (g : KeepS m w t u) : KeepS m w s u where
  gpr r hr := (g.gpr r hr).trans (h.gpr r hr)
  v := g.v.trans h.v
  rd := g.rd.trans h.rd
  wr := g.wr.trans h.wr
  sp := g.sp.trans h.sp
  syms := g.syms.trans h.syms
  frame := by
    have := g.frame
    simp only [slotR, slotBase_congr (h.gpr _ hb)] at this
    exact h.frame.trans this

theorem ModeOk.congr {m : Mode} {s s' : State} (h : ModeOk m s) (hb : s'.gpr m.b = s.gpr m.b) (hwr : s'.wr = s.wr) :
    ModeOk m s' := by
  refine ⟨h.1, fun k hk => ?_⟩
  have := h.2 k hk
  rw [slotBase_congr hb, hwr]
  exact this

theorem regIdx_inj {a b : Reg} (h : a.ctorIdx = b.ctorIdx) : a = b := by
  rw [← Reg.ofNat_ctorIdx a, ← Reg.ofNat_ctorIdx b, h]

/-- Writing a general register. -/
private theorem put {env : Nat → BitVec 64} {m : Mode} {w : Nat} {e : Env} {s : State} (hr : RelS env m e s)
    (hb : w.testBit m.b.ctorIdx = false) {d : Reg} {f : Form} {x : BitVec 64} (hd : w.testBit d.ctorIdx = true)
    (hx : Is env f x) : RelS env m (gset e d f) (s.write .x d x) ∧ KeepS m w s (s.write .x d x) := by
  have hne : ∀ r, w.testBit r.ctorIdx = false → (s.write .x d x).gpr r = s.gpr r := fun r hr => by
    rw [RegUpd.gpr_write, ite_eq_right]
    rintro rfl; rw [hd] at hr; cases hr
  refine ⟨⟨fun r g hg => ?_, fun k g hk hg => ?_⟩, ⟨hne, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩⟩
  · simp only [gget, gset, getD_set] at hg
    rw [RegUpd.gpr_write]
    split at hg
    · rename_i h
      obtain rfl := regIdx_inj h.1
      cases hg
      simp only [ite_true, BitVec.setWidth_eq]; exact hx
    · rename_i h
      by_cases hrd : r = d
      · subst hrd
        simp only [true_and, Nat.not_lt] at h
        rw [getD_none h] at hg; cases hg
      · rw [ite_eq_right hrd]; exact hr.reg r g hg
  · rw [slotVal, slotBase_congr (hne _ hb), RegUpd.mem_write]; exact hr.slot k g hk hg

theorem str_ok {env : Nat → BitVec 64} {m : Mode} {w : Nat} {e e' : Env} {s : State}
    (hr : RelS env m e s) (hm : ModeOk m s) {r b : Reg} {off : Nat}
    (h : stepS m w e (.str .x r b off) = some e') :
    ∃ s', exec (.str .x r b off) s = some s' ∧ RelS env m e' s' ∧ KeepS m w s s' := by
  simp only [stepS] at h
  split at h
  · rename_i ho
    split at h
    · rename_i x hx
      cases h
      obtain ⟨rfl, o1, o2, o3⟩ := ho
      obtain ⟨hlo, hin⟩ := hm
      obtain ⟨b, lo, n⟩ := m
      simp only at o2 o3 hlo
      have ha : s.gpr b + BitVec.ofNat 64 off = Straight.wordAddr (slotBase ⟨b, lo, n⟩ s) (off / 8 - lo) := by
        simp only [Straight.wordAddr, slotBase, BitVec.add_assoc]
        rw [BitVec.ofNat_add_ofNat]; congr 2; omega
      have hi := hin (off / 8 - lo) (by simp only; omega)
      have hsep : ∀ j < n, j ≠ off / 8 - lo → Mem.Sep (Straight.wordAddr (slotBase ⟨b, lo, n⟩ s) j) (64 / 8)
          (Straight.wordAddr (slotBase ⟨b, lo, n⟩ s) (off / 8 - lo)) (64 / 8) := fun j hj hjk =>
        Straight.slot_sep _ (by omega) (by omega) hjk
      have hfr : Frame [slotR ⟨b, lo, n⟩ s] s.mem
          (s.mem.writeW (Straight.wordAddr (slotBase ⟨b, lo, n⟩ s) (off / 8 - lo)) (s.gpr r)) :=
        (Frame.refl [slotR ⟨b, lo, n⟩ s] s.mem).writeW (List.mem_singleton_self _) (s.gpr r)
          (Straight.slot_contains (slotBase ⟨b, lo, n⟩ s) (n := n) (k := off / 8 - lo) (by omega) (by omega))
      refine ⟨{ s with mem := s.mem.writeW (Straight.wordAddr (slotBase ⟨b, lo, n⟩ s) (off / 8 - lo)) (s.gpr r) }, ?_,
        ⟨hr.reg, fun k g hk hg => ?_⟩, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, hfr⟩⟩
      · have := exec_str_x (s := s) (t := r) (n := b) (off := off) ⟨o1, by omega⟩ (by rw [ha]; exact hi)
        rw [this, ha]
      · simp only [sset, getD_set] at hg
        simp only [slotVal, slotBase]
        split at hg
        · rename_i hk'
          cases hg
          rw [← hk'.1]
          rw [Mem.readW_writeW_self64 s.mem (Straight.wordAddr (s.gpr b + BitVec.ofNat 64 (8 * lo)) (off / 8 - lo)) (s.gpr r)]
          exact hr.reg _ _ hx
        · rename_i hk'
          by_cases hkk : k = off / 8 - lo
          · subst hkk
            simp only [true_and, Nat.not_lt] at hk'
            rw [getD_none hk'] at hg; cases hg
          · have hs := hr.slot k g hk hg
            have e := Mem.readW_writeW_sep (m := s.mem) (v := s.gpr r) (hsep k hk hkk) (by decide)
            simp only [slotVal, slotBase] at hs e
            rw [e]; exact hs
    · cases h
  · cases h

theorem ldr_ok {env : Nat → BitVec 64} {m : Mode} {w : Nat} {e e' : Env} {s : State}
    (hr : RelS env m e s) (hm : ModeOk m s) (hb : w.testBit m.b.ctorIdx = false) {r b : Reg} {off : Nat}
    (h : stepS m w e (.ldr .x r b off) = some e') :
    ∃ s', exec (.ldr .x r b off) s = some s' ∧ RelS env m e' s' ∧ KeepS m w s s' := by
  simp only [stepS] at h
  split at h
  · rename_i ho
    split at h
    · rename_i x hx
      cases h
      obtain ⟨hd, rfl, o1, o2, o3⟩ := ho
      obtain ⟨hlo, hin⟩ := hm
      have ha : s.gpr m.b + BitVec.ofNat 64 off = Straight.wordAddr (slotBase m s) (off / 8 - m.lo) := by
        simp only [Straight.wordAddr, slotBase, BitVec.add_assoc]
        rw [BitVec.ofNat_add_ofNat]; congr 2; omega
      have hi : InRegions (s.rd ++ s.wr) (Straight.wordAddr (slotBase m s) (off / 8 - m.lo)) 8 := by
        obtain ⟨R, hR, hc⟩ := hin (off / 8 - m.lo) (by omega)
        exact ⟨R, List.mem_append_right _ hR, hc⟩
      obtain ⟨p, q⟩ := put hr hb hd (hr.slot _ _ (by omega) hx)
      refine ⟨_, ?_, p, q⟩
      have := exec_ldr_x (s := s) (t := r) (n := m.b) (off := off) ⟨o1, by omega⟩ (by rw [ha]; exact hi)
      rw [this, ha]; rfl
    · cases h
  · cases h

theorem stepS_ok {env : Nat → BitVec 64} {m : Mode} {w : Nat} {e e' : Env} {s : State} (hr : RelS env m e s)
    (hm : ModeOk m s) (hb : w.testBit m.b.ctorIdx = false) {i : Instr} (h : stepS m w e i = some e') :
    ∃ s', exec i s = some s' ∧ RelS env m e' s' ∧ KeepS m w s s' := by
  unfold stepS at h
  split at h
  · split at h
    · rename_i d n a hd
      split at h
      · rename_i x y hx hy
        cases h
        obtain ⟨p, q⟩ := put hr hb hd ((hr.reg _ _ hx).xor (hr.reg _ _ hy))
        exact ⟨_, by simp only [exec_logic, State.read, BitVec.setWidth_eq], p, q⟩
      · cases h
    · cases h
  · split at h
    · rename_i d n a k hd
      split at h
      · rename_i x y hx hy
        cases h
        obtain ⟨p, q⟩ := put hr hb hd.1 ((hr.reg _ _ hx).xor ((hr.reg _ _ hy).ror hd.2))
        refine ⟨_, ?_, p, q⟩
        simp only [exec, Size.bits, hd.2, ite_true, State.read, BitVec.setWidth_eq]
      · cases h
    · cases h
  · split at h
    · rename_i d n a k hd
      split at h
      · rename_i x y hx hy
        obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨p, q⟩ := put hr hb hd.1 ((hr.reg _ _ hx).bic ((hr.reg _ _ hy).ror hd.2) ht)
        refine ⟨_, ?_, p, q⟩
        simp only [exec, Size.bits, hd.2, ite_true, State.read, BitVec.setWidth_eq]
      · cases h
    · cases h
  · split at h
    · rename_i d n k hd
      split at h
      · rename_i x hx
        cases h
        obtain ⟨p, q⟩ := put hr hb hd.1 ((hr.reg _ _ hx).ror hd.2)
        refine ⟨_, ?_, p, q⟩
        simp only [exec, Size.bits, hd.2, ite_true, State.read, BitVec.setWidth_eq]
      · cases h
    · cases h
  · exact str_ok hr hm h
  · exact ldr_ok hr hm hb h
  · cases h

theorem runS {env : Nat → BitVec 64} {m : Mode} {w : Nat} (hb : w.testBit m.b.ctorIdx = false) : ∀ (is : List Instr) {e e' : Env} {s : State},
    RelS env m e s → ModeOk m s → evalS m w is e = some e' →
    ∃ s', runBlock isa is s = some s' ∧ RelS env m e' s' ∧ KeepS m w s s'
  | [], e, e', s, hr, _, h => by cases h; exact ⟨s, runBlock_nil, hr, .refl ..⟩
  | i :: is, e, e', s, hr, hm, h => by
    simp only [evalS] at h
    split at h
    · rename_i e₁ h₁
      obtain ⟨s₁, x₁, r₁, k₁⟩ := stepS_ok hr hm hb h₁
      obtain ⟨s', x', r', k'⟩ := runS hb is r₁ (hm.congr (k₁.gpr _ hb) k₁.wr) h
      exact ⟨s', by rw [runBlock_cons, x₁, runStep_some]; exact x', r', k₁.trans hb k'⟩
    · cases h

end VG.Proof.Sha3.AArch64.Eval
