import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Impl.Rc4.AArch64
import VerifiedGarbage.Proof.Rc4.Update
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc4.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Vec`. -/
section

/-!
# Byte lanes of the RC4 code's vectors

The RC4 code's vectors are byte tables (the permutation, sixteen bytes per
register) and bytes broadcast to every lane (`bc`). These are the byte-lane
facts about the AdvSIMD instructions it uses.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64

/-- `b` in every byte. -/
def bc (b : BitVec 8) : BitVec 128 := ofVBytes fun _ => b

theorem vbyte_ext {x y : BitVec 128} (h : ∀ e < 16, vbyte x e = vbyte y e) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := congrArg (fun z => z.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [vbyte, BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true,
    Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

theorem vbyte_bc (b : BitVec 8) {e : Nat} (he : e < 16) : vbyte (VG.Proof.Rc4.AArch64.bc b) e = b :=
  vbyte_ofVBytes _ he

theorem vbyte_xor (x y : BitVec 128) (e : Nat) : vbyte (x ^^^ y) e = vbyte x e ^^^ vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem vbyte_or (x y : BitVec 128) (e : Nat) : vbyte (x ||| y) e = vbyte x e ||| vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem vbyte_and (x y : BitVec 128) (e : Nat) : vbyte (x &&& y) e = vbyte x e &&& vbyte y e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [vbyte, hi]

theorem vbyte_not (x : BitVec 128) {e : Nat} (he : e < 16) : vbyte (~~~x) e = ~~~vbyte x e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
    show 8 * e + i < 128 by omega]

theorem bc_xor (a b : BitVec 8) : VG.Proof.Rc4.AArch64.bc a ^^^ VG.Proof.Rc4.AArch64.bc b = VG.Proof.Rc4.AArch64.bc (a ^^^ b) :=
  VG.Proof.Rc4.AArch64.vbyte_ext fun e he => by rw [VG.Proof.Rc4.AArch64.vbyte_xor, VG.Proof.Rc4.AArch64.vbyte_bc _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he]

theorem bc_or (a b : BitVec 8) : VG.Proof.Rc4.AArch64.bc a ||| bc b = VG.Proof.Rc4.AArch64.bc (a ||| b) :=
  VG.Proof.Rc4.AArch64.vbyte_ext fun e he => by rw [VG.Proof.Rc4.AArch64.vbyte_or, VG.Proof.Rc4.AArch64.vbyte_bc _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he]

theorem vbyte_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat}
    (he : e < 16) : vbyte (VArr.b16.map2 f x y) e = f 8 (vbyte x e) (vbyte y e) := by
  simp only [VArr.map2]
  exact vbyte_ofVBytes _ he

theorem add_bc (a b : BitVec 8) : VArr.b16.map2 (fun _ x y => x + y) (VG.Proof.Rc4.AArch64.bc a) (VG.Proof.Rc4.AArch64.bc b) = VG.Proof.Rc4.AArch64.bc (a + b) :=
  VG.Proof.Rc4.AArch64.vbyte_ext fun e he => by rw [VG.Proof.Rc4.AArch64.vbyte_map2 _ _ _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he]

theorem sub_bc (a b : BitVec 8) : VArr.b16.map2 (fun _ x y => x - y) (VG.Proof.Rc4.AArch64.bc a) (VG.Proof.Rc4.AArch64.bc b) = VG.Proof.Rc4.AArch64.bc (a - b) :=
  VG.Proof.Rc4.AArch64.vbyte_ext fun e he => by rw [VG.Proof.Rc4.AArch64.vbyte_map2 _ _ _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he]

/-- CMEQ's mask, byte by byte. -/
theorem vbyte_cmeq (x y : BitVec 128) {e : Nat} (he : e < 16) :
    vbyte (VArr.b16.map2 (fun w a b => if a = b then BitVec.allOnes w else 0) x y) e =
      if vbyte x e = vbyte y e then BitVec.allOnes 8 else 0 :=
  VG.Proof.Rc4.AArch64.vbyte_map2 _ _ _ he

/-- BIT, byte by byte, for a mask of all-zero and all-one bytes. -/
theorem vbyte_bit (d n m : BitVec 128) {e : Nat} (c : Prop) [Decidable c]
    (hm : vbyte m e = if c then BitVec.allOnes 8 else 0) :
    vbyte (VSelOp.bit.eval d n m) e = if c then vbyte n e else vbyte d e := by
  by_cases hc : c
  · simp only [hc, ite_true] at hm ⊢
    simp only [VSelOp.eval, VG.Proof.Rc4.AArch64.vbyte_xor, VG.Proof.Rc4.AArch64.vbyte_and, hm, BitVec.and_allOnes, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]
  · simp only [hc, ite_false] at hm ⊢
    simp [VSelOp.eval, VG.Proof.Rc4.AArch64.vbyte_xor, VG.Proof.Rc4.AArch64.vbyte_and, hm]

/-- A byte replaced. -/
theorem vbyte_setLane (x : BitVec 128) (v : BitVec 8) {i e : Nat} (hi : i < 16) (he : e < 16) :
    vbyte (setLane x 8 i v) e = if e = i then v else vbyte x e := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp only [setLane, vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    hk, decide_true, Bool.true_and, show 8 * e + k < 128 by omega]
  by_cases h : e = i
  · subst h
    simp [show ¬ 8 * e + k < 8 * e by omega, show 8 * e + k - 8 * e = k by omega, hk,
      show k < 128 by omega]
  · simp only [h, ite_false]
    rcases (by omega : e < i ∨ i < e) with h' | h'
    · simp [show 8 * e + k < 8 * i by omega]
      intro; omega
    · simp [show ¬ 8 * e + k < 8 * i by omega, show ¬ 8 * e + k - 8 * i < 8 by omega,
        BitVec.getLsbD_of_ge v (8 * e + k - 8 * i) (by omega), hk]

theorem ite_iff {α : Type} {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) (a b : α) :
    (if p then a else b) = if q then a else b := by
  by_cases hp : p
  · simp [hp, h.mp hp]
  · have hq : ¬ q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

theorem extract_byte (x : BitVec 128) (j : Nat) : x.extractLsb' (8 * j) 8 = vbyte x j := rfl

open RegUpd in
syntax "rrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rrun) => `(tactic| rrun [])
  | `(tactic| rrun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil,
        exec, State.read, addr, State.load, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
        RegUpd.wr_write, RegUpd.v_write, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV,
        RegUpd.wr_setV, RegUpd.v_setV,
        VOp.eval, Size.bits, BitVec.setWidth_eq, BitVec.shiftLeft_zero,
        BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.zero_width_append,
        BitVec.cast_eq, Option.bind_some, Option.map_some, Option.some.injEq,
        exists_eq_left', ite_true, ite_false, reduceCtorEq,
        Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, true_and, and_true, $ls,*]))

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Regs`. -/
section

/-!
# The table registers

Byte `k` of the table registers (`tbyte`) is lane `k % 16` of
`v(16 + k / 16)`. A four-register `tbl`/`tbx` from `v16`, `v20`, `v24` or
`v28` reads the bytes of one quarter of it.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64

/-- Byte `k` of the table registers. -/
def tbyte (v : VReg → BitVec 128) (k : Nat) : BitVec 8 := vbyte (v (treg (k / 16))) (k % 16)

theorem treg_quarter : ∀ q < 4, ∀ k < 4,
    Nat.repeat VReg.succ k ([VReg.v16, .v20, .v24, .v28].getD q .v16) = treg (4 * q + k) := by
  decide

theorem treg_inj : ∀ a < 16, ∀ b < 16, treg a = treg b → a = b := by decide

theorem treg_ne : ∀ a < 16, treg a ≠ .v0 ∧ treg a ≠ .v1 ∧ treg a ≠ .v2 ∧ treg a ≠ .v3 ∧
    treg a ≠ .v4 ∧ treg a ≠ .v5 ∧ treg a ≠ .v6 ∧ treg a ≠ .v7 ∧ treg a ≠ .v8 ∧ treg a ≠ .v9 ∧
    treg a ≠ .v10 ∧ treg a ≠ .v11 ∧ treg a ≠ .v12 ∧ treg a ≠ .v13 ∧ treg a ≠ .v14 := by decide

/-- A register outside the table. -/
def NotTable (r : VReg) : Prop := ∀ a < 16, treg a ≠ r

instance (r : VReg) : Decidable (VG.Proof.Rc4.AArch64.NotTable r) := inferInstanceAs (Decidable (∀ a < 16, treg a ≠ r))

theorem treg_of_ge {n : Nat} (h : 16 ≤ n) : treg n = .v16 := by
  simp only [treg, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simp; omega)]; rfl

theorem NotTable.ne {r : VReg} (h : VG.Proof.Rc4.AArch64.NotTable r) (n : Nat) : treg n ≠ r := by
  by_cases hn : n < 16
  · exact h n hn
  · rw [VG.Proof.Rc4.AArch64.treg_of_ge (by omega)]; exact h 0 (by decide)

theorem tbyte_congr {v w : VReg → BitVec 128} (h : ∀ a < 16, v (treg a) = w (treg a)) {k : Nat}
    (hk : k < 256) : VG.Proof.Rc4.AArch64.tbyte v k = VG.Proof.Rc4.AArch64.tbyte w k := by
  simp only [VG.Proof.Rc4.AArch64.tbyte, h _ (by omega : k / 16 < 16)]

/-- The table byte that a quarter's `tbl` reads, for an index in the quarter. -/
theorem tableByte_quarter (v : VReg → BitVec 128) {q : Nat} (hq : q < 4) {idx : Nat} (hi : idx < 64) :
    tableByte v ([VReg.v16, .v20, .v24, .v28].getD q .v16) idx = VG.Proof.Rc4.AArch64.tbyte v (64 * q + idx) := by
  simp only [tableByte, VG.Proof.Rc4.AArch64.tbyte, VG.Proof.Rc4.AArch64.treg_quarter q hq _ (by omega : idx / 16 < 4)]
  rw [show (64 * q + idx) / 16 = 4 * q + idx / 16 by omega, show (64 * q + idx) % 16 = idx % 16 by omega]

/-- The quarter of each byte, and its index there. -/
theorem xor_quarter : ∀ x < 256, ∀ q < 4,
    (x ^^^ 64 * q < 64 ↔ x / 64 = q) ∧ (x / 64 = q → x ^^^ 64 * q = x - 64 * q) := by
  decide +kernel

/-! ## The constants -/

/-- The lane numbers of quarter `q`: `16 q`, …, `16 q + 15`. -/
def laneNums (q : Nat) : BitVec 128 := ofVBytes fun e => BitVec.ofNat 8 (16 * q + e)

structure Consts (s : State) : Prop where
  lns : ∀ q < 4, s.v (VG.Impl.Rc4.AArch64.lanes q) = VG.Proof.Rc4.AArch64.laneNums q
  c64 : s.v c64 = VG.Proof.Rc4.AArch64.bc 64
  c128 : s.v c128 = VG.Proof.Rc4.AArch64.bc 128

theorem Consts.congr {s s' : State} (h : VG.Proof.Rc4.AArch64.Consts s)
    (hv : ∀ r, r = .v8 ∨ r = .v9 ∨ r = .v10 ∨ r = .v11 ∨ r = .v12 ∨ r = .v13 → s'.v r = s.v r) :
    VG.Proof.Rc4.AArch64.Consts s' where
  lns q hq := by
    have : VG.Impl.Rc4.AArch64.lanes q = .v8 ∨ VG.Impl.Rc4.AArch64.lanes q = .v9 ∨
        VG.Impl.Rc4.AArch64.lanes q = .v10 ∨ VG.Impl.Rc4.AArch64.lanes q = .v11 := by
      revert q; decide
    rw [hv _ (by rcases this with h | h | h | h <;> simp [h])]; exact h.lns q hq
  c64 := by rw [hv _ (by simp [VG.Impl.Rc4.AArch64.c64])]; exact h.c64
  c128 := by rw [hv _ (by simp [VG.Impl.Rc4.AArch64.c128])]; exact h.c128

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Lookup`. -/
section

/-!
# A table lookup

`lookup_run`: from the index `X` broadcast in `x`, and `X ^ 64`, `X ^ 128`,
`X ^ 192` in `a`, `b`, `c` (`quarters_run` computes them), the lookup
leaves `S[X]` (`tbyte`) broadcast in `d`, through the temporary `t`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

theorem exec_vop' (s : State) (op : VOp) :
    exec (.vop op) s = (op.eval s).map fun (d, x) => s.setV d x := rfl

/-- The registers but `d` keep their values, and nothing else changes. -/
def Only (ds : List VReg) (s s' : State) : Prop :=
  s' = { s with v := s'.v } ∧ ∀ r, r ∉ ds → s'.v r = s.v r

theorem Only.refl (ds : List VReg) (s : State) : VG.Proof.Rc4.AArch64.Only ds s s := ⟨rfl, fun _ _ => rfl⟩

theorem Only.trans {ds : List VReg} {a b c : State} (h₁ : VG.Proof.Rc4.AArch64.Only ds a b) (h₂ : VG.Proof.Rc4.AArch64.Only ds b c) :
    VG.Proof.Rc4.AArch64.Only ds a c := by
  refine ⟨?_, fun r hr => (h₂.2 r hr).trans (h₁.2 r hr)⟩
  rw [h₂.1, h₁.1]

theorem Only.mono {ds ds' : List VReg} {a b : State} (h : VG.Proof.Rc4.AArch64.Only ds a b) (hs : ∀ r ∈ ds, r ∈ ds') :
    VG.Proof.Rc4.AArch64.Only ds' a b := ⟨h.1, fun r hr => h.2 r fun h' => hr (hs r h')⟩

theorem Only.setV (s : State) {d : VReg} {ds : List VReg} (hd : d ∈ ds) (x : BitVec 128) :
    VG.Proof.Rc4.AArch64.Only ds s (s.setV d x) := by
  refine ⟨rfl, fun r hr => ?_⟩
  have : r ≠ d := fun e => hr (e ▸ hd)
  exact v_setV_of_ne _ _ this

theorem Only.gpr {ds : List VReg} {s s' : State} (h : VG.Proof.Rc4.AArch64.Only ds s s') : s'.gpr = s.gpr := by
  rw [h.1]
theorem Only.mem {ds : List VReg} {s s' : State} (h : VG.Proof.Rc4.AArch64.Only ds s s') : s'.mem = s.mem := by
  rw [h.1]
theorem Only.rd {ds : List VReg} {s s' : State} (h : VG.Proof.Rc4.AArch64.Only ds s s') : s'.rd = s.rd := by
  rw [h.1]
theorem Only.wr {ds : List VReg} {s s' : State} (h : VG.Proof.Rc4.AArch64.Only ds s s') : s'.wr = s.wr := by
  rw [h.1]
theorem Only.sp {ds : List VReg} {s s' : State} (h : VG.Proof.Rc4.AArch64.Only ds s s') : s'.sp = s.sp := by
  rw [h.1]

theorem runBlock_cat (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem runBlock_cat_some {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [VG.Proof.Rc4.AArch64.runBlock_cat, h₁, Option.bind_some, h₂]

/-! ## The quarters -/

theorem xor64_128 (X : BitVec 8) : X ^^^ 64 ^^^ 128 = X ^^^ 192 := by
  rw [BitVec.xor_assoc]; rfl

theorem quarters_run {s : State} (hk : VG.Proof.Rc4.AArch64.Consts s) {x a b c : VReg} (X : BitVec 8)
    (hx : s.v x = VG.Proof.Rc4.AArch64.bc X) (hax : a ≠ x) (hba : b ≠ a) (hca : c ≠ a) (hbc : b ≠ c)
    (ha128 : a ≠ c128) (hb128 : b ≠ c128) :
    ∃ s', runBlock isa (quarters x a b c) s = some s' ∧ s'.v a = VG.Proof.Rc4.AArch64.bc (X ^^^ 64) ∧
      s'.v b = VG.Proof.Rc4.AArch64.bc (X ^^^ 128) ∧ s'.v c = VG.Proof.Rc4.AArch64.bc (X ^^^ 192) ∧ VG.Proof.Rc4.AArch64.Only [a, b, c] s s' := by
  let s₁ := s.setV a (s.v x ^^^ s.v c64)
  let s₂ := s₁.setV b (s₁.v x ^^^ s₁.v c128)
  let s₃ := s₂.setV c (s₂.v a ^^^ s₂.v c128)
  have ha₁ : s₁.v a = VG.Proof.Rc4.AArch64.bc (X ^^^ 64) := by
    simp only [s₁, v_setV_self, hx, hk.c64, VG.Proof.Rc4.AArch64.bc_xor]
  have ha₂ : s₂.v a = VG.Proof.Rc4.AArch64.bc (X ^^^ 64) := by simp only [s₂, v_setV_of_ne _ _ (Ne.symm hba), ha₁]
  have hb₂ : s₂.v b = VG.Proof.Rc4.AArch64.bc (X ^^^ 128) := by
    simp only [s₂, v_setV_self, s₁, v_setV_of_ne _ _ hax.symm, v_setV_of_ne _ _ ha128.symm, hx,
      hk.c128, VG.Proof.Rc4.AArch64.bc_xor]
  have c128₂ : s₂.v c128 = VG.Proof.Rc4.AArch64.bc 128 := by
    simp only [s₂, s₁, v_setV_of_ne _ _ hb128.symm, v_setV_of_ne _ _ ha128.symm, hk.c128]
  refine ⟨s₃, ?_, ?_, ?_, ?_, ?_⟩
  · have e₁ : exec (eorV a x c64) s = some s₁ := rfl
    have e₂ : exec (eorV b x c128) s₁ = some s₂ := rfl
    have e₃ : exec (eorV c a c128) s₂ = some s₃ := rfl
    rw [quarters, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some,
      runBlock_cons, e₃, runStep_some, runBlock_nil]
  · by_cases h : a = c
    · exact absurd h hca.symm
    · simp only [s₃, v_setV_of_ne _ _ h, ha₂]
  · simp only [s₃, v_setV_of_ne _ _ hbc]
    exact hb₂
  · simp only [s₃, v_setV_self, ha₂, c128₂, VG.Proof.Rc4.AArch64.bc_xor, VG.Proof.Rc4.AArch64.xor64_128]
  · exact (((Only.setV s (by simp) _).trans (Only.setV _ (by simp) _)).trans (Only.setV _ (by simp) _))

/-! ## The lookup -/

/-- What a `tbl` (or `tbx`, keeping `prev`) of quarter `q`, at index `idx`,
leaves in a byte. -/
def qbyte (T : Nat → BitVec 8) (q idx : Nat) (ext : Bool) (prev : BitVec 8) : BitVec 8 :=
  if idx < 64 then T (64 * q + idx) else if ext then prev else 0

theorem vbyte_tblN (s : State) (ext : Bool) {q : Nat} (hq : q < 4) (d m : VReg) {e : Nat}
    (he : e < 16) :
    vbyte (ofVBytes fun i => if (vbyte (s.v m) i).toNat < 16 * 4 then
        tableByte s.v ([VReg.v16, .v20, .v24, .v28].getD q .v16) (vbyte (s.v m) i).toNat
      else if ext then vbyte (s.v d) i else 0) e =
      VG.Proof.Rc4.AArch64.qbyte (VG.Proof.Rc4.AArch64.tbyte s.v) q (vbyte (s.v m) e).toNat ext (vbyte (s.v d) e) := by
  rw [vbyte_ofVBytes _ he, VG.Proof.Rc4.AArch64.qbyte]
  split
  · rename_i h; rw [VG.Proof.Rc4.AArch64.tableByte_quarter _ hq h]
  · rfl

theorem toNat_xor_byte (X : BitVec 8) (k : Nat) (hk : k < 256) :
    (X ^^^ BitVec.ofNat 8 k).toNat = X.toNat ^^^ k := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

theorem or_zero8 (y : BitVec 8) : y ||| 0 = y := by simp
theorem zero_or8 (y : BitVec 8) : 0 ||| y = y := by simp

/-- The four quarters' bytes, combined, are the byte at the index. -/
theorem quarters_byte (T : Nat → BitVec 8) (X : BitVec 8) (p p' : BitVec 8) :
    VG.Proof.Rc4.AArch64.qbyte T 1 (X.toNat ^^^ 64) true (VG.Proof.Rc4.AArch64.qbyte T 0 X.toNat false p) |||
      VG.Proof.Rc4.AArch64.qbyte T 3 (X.toNat ^^^ 192) true (VG.Proof.Rc4.AArch64.qbyte T 2 (X.toNat ^^^ 128) false p') = T X.toNat := by
  have hX := X.isLt
  have q := VG.Proof.Rc4.AArch64.xor_quarter X.toNat hX
  obtain ⟨h1, e1⟩ := q 1 (by decide)
  obtain ⟨h2, e2⟩ := q 2 (by decide)
  obtain ⟨h3, e3⟩ := q 3 (by decide)
  simp only [Nat.mul_one, show 64 * 2 = 128 by rfl, show 64 * 3 = 192 by rfl] at h1 h2 h3 e1 e2 e3
  simp only [VG.Proof.Rc4.AArch64.qbyte]
  have n1 : X.toNat / 64 ≠ 1 → ¬ (X.toNat ^^^ 64 < 64) := fun h h' => h (h1.mp h')
  have n2 : X.toNat / 64 ≠ 2 → ¬ (X.toNat ^^^ 128 < 64) := fun h h' => h (h2.mp h')
  have n3 : X.toNat / 64 ≠ 3 → ¬ (X.toNat ^^^ 192 < 64) := fun h h' => h (h3.mp h')
  rcases (by omega : X.toNat / 64 = 0 ∨ X.toNat / 64 = 1 ∨ X.toNat / 64 = 2 ∨ X.toNat / 64 = 3)
    with h | h | h | h
  · simp only [show X.toNat < 64 by omega, n1 (by omega), n2 (by omega), n3 (by omega), ite_true,
      ite_false, Bool.false_eq_true, Nat.mul_zero, Nat.zero_add, VG.Proof.Rc4.AArch64.or_zero8]
  · simp only [show ¬ X.toNat < 64 by omega, h1.mpr h, n2 (by omega), n3 (by omega), ite_true,
      ite_false, Bool.false_eq_true]
    rw [e1 h, VG.Proof.Rc4.AArch64.or_zero8]
    exact congrArg T (by omega)
  · simp only [show ¬ X.toNat < 64 by omega, n1 (by omega), h2.mpr h, n3 (by omega), ite_true,
      ite_false, Bool.false_eq_true]
    rw [e2 h, VG.Proof.Rc4.AArch64.zero_or8]
    exact congrArg T (by omega)
  · simp only [show ¬ X.toNat < 64 by omega, n1 (by omega), n2 (by omega), h3.mpr h, ite_true,
      ite_false, Bool.false_eq_true]
    rw [e3 h, VG.Proof.Rc4.AArch64.zero_or8]
    exact congrArg T (by omega)

theorem xor_toNat (X : BitVec 8) (k : BitVec 8) : (X ^^^ k).toNat = X.toNat ^^^ k.toNat :=
  BitVec.toNat_xor _ _

theorem lookup_run {s : State} {d t x a b c : VReg} (X : BitVec 8)
    (hx : s.v x = VG.Proof.Rc4.AArch64.bc X) (ha : s.v a = VG.Proof.Rc4.AArch64.bc (X ^^^ 64)) (hb : s.v b = VG.Proof.Rc4.AArch64.bc (X ^^^ 128))
    (hc : s.v c = VG.Proof.Rc4.AArch64.bc (X ^^^ 192))
    (hd : VG.Proof.Rc4.AArch64.NotTable d) (ht : VG.Proof.Rc4.AArch64.NotTable t) (hdt : d ≠ t) (hda : d ≠ a) (hdb : d ≠ b)
    (hdc : d ≠ c) (htc : t ≠ c) :
    ∃ s', runBlock isa (lookup d t x a b c) s = some s' ∧ s'.v d = VG.Proof.Rc4.AArch64.bc (VG.Proof.Rc4.AArch64.tbyte s.v X.toNat) ∧
      VG.Proof.Rc4.AArch64.Only [d, t] s s' := by
  let T := VG.Proof.Rc4.AArch64.tbyte s.v
  let f (q : Nat) (m : VReg) (ext : Bool) (st : State) (dd : VReg) : BitVec 128 :=
    ofVBytes fun i => if (vbyte (st.v m) i).toNat < 16 * 4 then
      tableByte st.v ([VReg.v16, .v20, .v24, .v28].getD q .v16) (vbyte (st.v m) i).toNat
    else if ext then vbyte (st.v dd) i else 0
  let s₁ := s.setV d (f 0 x false s d)
  let s₂ := s₁.setV d (f 1 a true s₁ d)
  let s₃ := s₂.setV t (f 2 b false s₂ t)
  let s₄ := s₃.setV t (f 3 c true s₃ t)
  let s₅ := s₄.setV d (s₄.v d ||| s₄.v t)
  have o₁ : VG.Proof.Rc4.AArch64.Only [d, t] s s₁ := Only.setV _ (by simp) _
  have o₂ : VG.Proof.Rc4.AArch64.Only [d, t] s s₂ := o₁.trans (Only.setV _ (by simp) _)
  have o₃ : VG.Proof.Rc4.AArch64.Only [d, t] s s₃ := o₂.trans (Only.setV _ (by simp) _)
  have o₄ : VG.Proof.Rc4.AArch64.Only [d, t] s s₄ := o₃.trans (Only.setV _ (by simp) _)
  have o₅ : VG.Proof.Rc4.AArch64.Only [d, t] s s₅ := o₄.trans (Only.setV _ (by simp) _)
  have tab : ∀ st, VG.Proof.Rc4.AArch64.Only [d, t] s st → VG.Proof.Rc4.AArch64.tbyte st.v = T := by
    intro st h; funext k; simp only [VG.Proof.Rc4.AArch64.tbyte, T]
    rw [h.2 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hd.ne _, ht.ne _⟩)]
  have a₁ : s₁.v a = VG.Proof.Rc4.AArch64.bc (X ^^^ 64) := by rw [v_setV_of_ne _ _ (Ne.symm hda), ha]
  have b₂ : s₂.v b = VG.Proof.Rc4.AArch64.bc (X ^^^ 128) := by
    rw [v_setV_of_ne _ _ (Ne.symm hdb), v_setV_of_ne _ _ (Ne.symm hdb), hb]
  have c₃ : s₃.v c = VG.Proof.Rc4.AArch64.bc (X ^^^ 192) := by
    rw [v_setV_of_ne _ _ (Ne.symm htc), v_setV_of_ne _ _ (Ne.symm hdc), v_setV_of_ne _ _ (Ne.symm hdc), hc]
  have d₄ : s₄.v d = s₂.v d := by
    rw [v_setV_of_ne _ _ hdt, v_setV_of_ne _ _ hdt]
  have hf : ∀ q m ext st dd e, q < 4 → e < 16 →
      vbyte (f q m ext st dd) e = VG.Proof.Rc4.AArch64.qbyte (VG.Proof.Rc4.AArch64.tbyte st.v) q (vbyte (st.v m) e).toNat ext (vbyte (st.v dd) e) :=
    fun q m ext st dd e hq he => VG.Proof.Rc4.AArch64.vbyte_tblN st ext hq dd m he
  have y₁ : ∀ e < 16, vbyte (s₁.v d) e = VG.Proof.Rc4.AArch64.qbyte T 0 X.toNat false (vbyte (s.v d) e) := by
    intro e he
    rw [show s₁.v d = f 0 x false s d from v_setV_self _ _ _, hf _ _ _ _ _ _ (by decide) he, hx,
      VG.Proof.Rc4.AArch64.vbyte_bc _ he]
  have y₂ : ∀ e < 16, vbyte (s₂.v d) e =
      VG.Proof.Rc4.AArch64.qbyte T 1 (X.toNat ^^^ 64) true (vbyte (s₁.v d) e) := by
    intro e he
    rw [show s₂.v d = f 1 a true s₁ d from v_setV_self _ _ _, hf _ _ _ _ _ _ (by decide) he, a₁,
      VG.Proof.Rc4.AArch64.vbyte_bc _ he, VG.Proof.Rc4.AArch64.xor_toNat, tab s₁ o₁]
    rfl
  have y₃ : ∀ e < 16, vbyte (s₃.v t) e =
      VG.Proof.Rc4.AArch64.qbyte T 2 (X.toNat ^^^ 128) false (vbyte (s₂.v t) e) := by
    intro e he
    rw [show s₃.v t = f 2 b false s₂ t from v_setV_self _ _ _, hf _ _ _ _ _ _ (by decide) he, b₂,
      VG.Proof.Rc4.AArch64.vbyte_bc _ he, VG.Proof.Rc4.AArch64.xor_toNat, tab s₂ o₂]
    rfl
  have y₄ : ∀ e < 16, vbyte (s₄.v t) e =
      VG.Proof.Rc4.AArch64.qbyte T 3 (X.toNat ^^^ 192) true (vbyte (s₃.v t) e) := by
    intro e he
    rw [show s₄.v t = f 3 c true s₃ t from v_setV_self _ _ _, hf _ _ _ _ _ _ (by decide) he, c₃,
      VG.Proof.Rc4.AArch64.vbyte_bc _ he, VG.Proof.Rc4.AArch64.xor_toNat, tab s₃ o₃]
    rfl
  refine ⟨s₅, ?_, ?_, o₅⟩
  · have e₁ : exec (.vop (.tblN false 4 d .v16 x)) s = some s₁ := rfl
    have e₂ : exec (.vop (.tblN true 4 d .v20 a)) s₁ = some s₂ := rfl
    have e₃ : exec (.vop (.tblN false 4 t .v24 b)) s₂ = some s₃ := rfl
    have e₄ : exec (.vop (.tblN true 4 t .v28 c)) s₃ = some s₄ := rfl
    have e₅ : exec (.vop (.logic .orr d d t)) s₄ = some s₅ := rfl
    rw [lookup, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  · apply VG.Proof.Rc4.AArch64.vbyte_ext; intro e he
    simp only [s₅, v_setV_self, VG.Proof.Rc4.AArch64.vbyte_or, d₄, y₂ e he, y₁ e he, y₄ e he, y₃ e he, VG.Proof.Rc4.AArch64.vbyte_bc _ he]
    exact VG.Proof.Rc4.AArch64.quarters_byte T X _ _

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.WriteJ`. -/
section

/-!
# A write at a secret index

`writeJ_run`: with the index `J` (and `J ^ 64`, `J ^ 128`, `J ^ 192`)
broadcast in `v0`–`v3` and the value `V` broadcast in `v4`, the sixteen
`cmeq`/`bit` pairs replace byte `J` of the table registers by `V`, and leave
the others.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

/-- The index's four quarters, broadcast in `v0`–`v3`. -/
def Quarters (s : State) (J : BitVec 8) : Prop :=
  ∀ q < 4, s.v (dq q) = VG.Proof.Rc4.AArch64.bc (J ^^^ BitVec.ofNat 8 (64 * q))

theorem xor_low : ∀ a < 64, ∀ q < 4, a ^^^ 64 * q = 64 * q + a := by decide +kernel

/-- Lane `e` of quarter `r % 4`'s lane numbers equals `J ^ 64 (r / 4)` just
when `16 r + e` is `J`. -/
theorem lane_eq (J : BitVec 8) {r e : Nat} (hr : r < 16) (he : e < 16) :
    BitVec.ofNat 8 (16 * (r % 4) + e) = J ^^^ BitVec.ofNat 8 (64 * (r / 4)) ↔ 16 * r + e = J.toNat := by
  have hJ := J.isLt
  have hq : (BitVec.ofNat 8 (64 * (r / 4))).toNat = 64 * (r / 4) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ha : (BitVec.ofNat 8 (16 * (r % 4) + e)).toNat = 16 * (r % 4) + e := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have low := VG.Proof.Rc4.AArch64.xor_low (16 * (r % 4) + e) (by omega) (r / 4) (by omega)
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [ha, BitVec.toNat_xor, hq] at h'
    have : J.toNat = (16 * (r % 4) + e) ^^^ 64 * (r / 4) := by
      rw [h', Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [low] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [ha, BitVec.toNat_xor, hq, ← h, show 16 * r + e = 64 * (r / 4) + (16 * (r % 4) + e) by omega,
      ← low, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

def writeN (n : Nat) : List Instr :=
  (List.range n).flatMap fun k =>
    [.vop (.cmeq .b16 .v7 (lanes (k % 4)) (dq (k / 4))), .vop (.bsel .bit (treg k) si .v7)]

theorem writeN_succ (n : Nat) : VG.Proof.Rc4.AArch64.writeN (n + 1) = VG.Proof.Rc4.AArch64.writeN n ++
    ([.vop (.cmeq .b16 .v7 (lanes (n % 4)) (dq (n / 4))), .vop (.bsel .bit (treg n) si .v7)] :
      List Instr) := by
  simp only [VG.Proof.Rc4.AArch64.writeN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- The registers the write changes. -/
def writeRegs : List VReg :=
  [.v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31]

theorem treg_mem : ∀ r < 16, treg r ∈ VG.Proof.Rc4.AArch64.writeRegs := by decide

theorem notTable_v7 : VG.Proof.Rc4.AArch64.NotTable .v7 := by decide

theorem lanes_notW : ∀ q < 4, lanes q ∉ VG.Proof.Rc4.AArch64.writeRegs := by decide
theorem dq_notW : ∀ q < 4, dq q ∉ VG.Proof.Rc4.AArch64.writeRegs := by decide

theorem writeN_run {s : State} (hk : VG.Proof.Rc4.AArch64.Consts s) {J V : BitVec 8} (hq : VG.Proof.Rc4.AArch64.Quarters s J)
    (hv : s.v si = VG.Proof.Rc4.AArch64.bc V) {n : Nat} (hn : n ≤ 16) :
    ∃ s', runBlock isa (VG.Proof.Rc4.AArch64.writeN n) s = some s' ∧
      (∀ k < 256, VG.Proof.Rc4.AArch64.tbyte s'.v k = if k / 16 < n ∧ k = J.toNat then V else VG.Proof.Rc4.AArch64.tbyte s.v k) ∧
      VG.Proof.Rc4.AArch64.Only VG.Proof.Rc4.AArch64.writeRegs s s' := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun k _ => by simp, Only.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, t₁, o₁⟩ := ih (by omega)
    have notW : ∀ r, r ∉ VG.Proof.Rc4.AArch64.writeRegs → s₁.v r = s.v r := o₁.2
    let m := VArr.b16.map2 (fun w a b => if a = b then BitVec.allOnes w else 0)
      (s₁.v (lanes (n % 4))) (s₁.v (dq (n / 4)))
    let s₂ := s₁.setV .v7 m
    let s₃ := s₂.setV (treg n) (VSelOp.bit.eval (s₂.v (treg n)) (s₂.v si) (s₂.v .v7))
    have e₂ : exec (.vop (.cmeq .b16 .v7 (lanes (n % 4)) (dq (n / 4)))) s₁ = some s₂ := rfl
    have e₃ : exec (.vop (.bsel .bit (treg n) si .v7)) s₂ = some s₃ := rfl
    have l₁ : s₁.v (lanes (n % 4)) = VG.Proof.Rc4.AArch64.laneNums (n % 4) := by
      rw [notW _ (VG.Proof.Rc4.AArch64.lanes_notW _ (by omega))]; exact hk.lns _ (by omega)
    have d₁ : s₁.v (dq (n / 4)) = VG.Proof.Rc4.AArch64.bc (J ^^^ BitVec.ofNat 8 (64 * (n / 4))) := by
      rw [notW _ (VG.Proof.Rc4.AArch64.dq_notW _ (by omega))]
      exact hq _ (by omega)
    have v₂ : s₂.v si = VG.Proof.Rc4.AArch64.bc V := by
      rw [v_setV_of_ne _ _ (by decide), notW _ (by decide)]; exact hv
    have m_byte : ∀ e < 16, vbyte (s₂.v .v7) e =
        if 16 * n + e = J.toNat then BitVec.allOnes 8 else 0 := by
      intro e he
      rw [v_setV_self, VG.Proof.Rc4.AArch64.vbyte_cmeq _ _ he, l₁, d₁, VG.Proof.Rc4.AArch64.laneNums, vbyte_ofVBytes _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he]
      simp only [VG.Proof.Rc4.AArch64.lane_eq J (by omega : n < 16) he]
    refine ⟨s₃, by rw [VG.Proof.Rc4.AArch64.writeN_succ]; exact VG.Proof.Rc4.AArch64.runBlock_cat_some run₁ (by
      rw [runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil]), ?_, ?_⟩
    · intro k hk
      by_cases hkn : k / 16 = n
      · have b₃ : VG.Proof.Rc4.AArch64.tbyte s₃.v k = vbyte (VSelOp.bit.eval (s₂.v (treg n)) (s₂.v si) (s₂.v .v7)) (k % 16) := by
          simp only [VG.Proof.Rc4.AArch64.tbyte, hkn, s₃, v_setV_self]
        rw [b₃, VG.Proof.Rc4.AArch64.vbyte_bit _ _ _ (16 * n + k % 16 = J.toNat) (m_byte _ (by omega)), v₂,
          VG.Proof.Rc4.AArch64.vbyte_bc _ (by omega)]
        have old : vbyte (s₂.v (treg n)) (k % 16) = VG.Proof.Rc4.AArch64.tbyte s.v k := by
          rw [v_setV_of_ne _ _ (notTable_v7.ne n)]
          have := t₁ k hk
          simp only [show ¬ k / 16 < n by omega, false_and, ite_false] at this
          rw [← this]; simp only [VG.Proof.Rc4.AArch64.tbyte, hkn]
        rw [old]
        exact VG.Proof.Rc4.AArch64.ite_iff ⟨fun h => ⟨by omega, by omega⟩, fun h => by omega⟩ _ _
      · have ne : treg (k / 16) ≠ treg n := fun h => hkn (VG.Proof.Rc4.AArch64.treg_inj _ (by omega) _ (by omega) h)
        have keep : s₃.v (treg (k / 16)) = s₁.v (treg (k / 16)) := by
          rw [v_setV_of_ne _ _ ne, v_setV_of_ne _ _ (notTable_v7.ne _)]
        have : VG.Proof.Rc4.AArch64.tbyte s₃.v k = VG.Proof.Rc4.AArch64.tbyte s₁.v k := by simp only [VG.Proof.Rc4.AArch64.tbyte, keep]
        rw [this, t₁ k hk]
        have e : (k / 16 < n + 1) ↔ (k / 16 < n) := by omega
        simp only [e]
    · exact (o₁.trans (Only.setV _ (by decide) _)).trans (Only.setV _ (VG.Proof.Rc4.AArch64.treg_mem n (by omega)) _)

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Step`. -/
section

/-!
# One swap

`swapStep_run`: with the table `R` in the table registers (indexed from the
base), `j` (from the base) broadcast in `v0` and `S[i] = R l` broadcast in
`v4`, the swap step adds `R l` to `j`, swaps `R l` and `R j`, leaves the
next `S[i]` (the new `R (l + 1)`) in `v4` and, in the PRGA, the output index
`R l + R j - B` in `v6`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

theorem dupE_bc (s : State) (n : VReg) (i : Nat) :
    VArr.b16.map2 (fun w _ _ => (s.v n).extractLsb' (w * i) w) 0 0 = VG.Proof.Rc4.AArch64.bc (vbyte (s.v n) i) :=
  VG.Proof.Rc4.AArch64.vbyte_ext fun e he => by
    rw [VG.Proof.Rc4.AArch64.vbyte_map2 _ _ _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he]
    rfl

/-- What follows the write at `j`: the output index, in the PRGA, the next
`S[i]`, and the write at `i`. -/
def stepTail (prga : Bool) (l : Nat) : List Instr :=
  (if prga then [.vop (.add .b16 .v6 si .v5), .vop (.add .b16 .v6 .v6 negBase)] else []) ++
  [.vop (.dupE .b16 si (treg ((l + 1) / 16)) ((l + 1) % 16)), .vop (.insE .b16 (treg 0) l .v5 0)]

theorem swapStep_eq (prga : Bool) (l : Nat) :
    swapStep prga l = ([.vop (.add .b16 (dq 0) (dq 0) si)] : List Instr) ++
      (quarters (dq 0) (dq 1) (dq 2) (dq 3) ++ (lookup .v5 .v6 (dq 0) (dq 1) (dq 2) (dq 3) ++
        (VG.Proof.Rc4.AArch64.writeN 16 ++ VG.Proof.Rc4.AArch64.stepTail prga l))) := by
  simp only [swapStep, VG.Proof.Rc4.AArch64.stepTail, writeJ, VG.Proof.Rc4.AArch64.writeN, List.append_assoc]

/-- The registers a swap step changes. -/
def stepRegs : List VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7,
   .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31]

/-- The table after the swap of positions `l` and `J`. -/
def swapR (R : Nat → BitVec 8) (l J : Nat) (k : Nat) : BitVec 8 :=
  if k = l then R J else if k = J then R l else R k

theorem consts_of_only {s s' : State} (hk : VG.Proof.Rc4.AArch64.Consts s) (h : VG.Proof.Rc4.AArch64.Only VG.Proof.Rc4.AArch64.stepRegs s s') : VG.Proof.Rc4.AArch64.Consts s' :=
  hk.congr fun r hr => h.2 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem swapStep_run (prga : Bool) {l : Nat} (hl : l < 16) {s : State} (hk : VG.Proof.Rc4.AArch64.Consts s)
    {Jr NB : BitVec 8} (hj : s.v (dq 0) = VG.Proof.Rc4.AArch64.bc Jr) (hi : s.v si = VG.Proof.Rc4.AArch64.bc (VG.Proof.Rc4.AArch64.tbyte s.v l))
    (hn : prga = true → s.v negBase = VG.Proof.Rc4.AArch64.bc NB) :
    ∃ s', runBlock isa (swapStep prga l) s = some s' ∧
      (∀ k < 256, VG.Proof.Rc4.AArch64.tbyte s'.v k =
        VG.Proof.Rc4.AArch64.swapR (VG.Proof.Rc4.AArch64.tbyte s.v) l (Jr + VG.Proof.Rc4.AArch64.tbyte s.v l).toNat k) ∧
      s'.v (dq 0) = VG.Proof.Rc4.AArch64.bc (Jr + VG.Proof.Rc4.AArch64.tbyte s.v l) ∧
      s'.v si = VG.Proof.Rc4.AArch64.bc (VG.Proof.Rc4.AArch64.swapR (VG.Proof.Rc4.AArch64.tbyte s.v) l (Jr + VG.Proof.Rc4.AArch64.tbyte s.v l).toNat (l + 1)) ∧
      (prga = true → s'.v .v6 = VG.Proof.Rc4.AArch64.bc (VG.Proof.Rc4.AArch64.tbyte s.v l + VG.Proof.Rc4.AArch64.tbyte s.v (Jr + VG.Proof.Rc4.AArch64.tbyte s.v l).toNat + NB)) ∧
      VG.Proof.Rc4.AArch64.Only VG.Proof.Rc4.AArch64.stepRegs s s' := by
  let R := VG.Proof.Rc4.AArch64.tbyte s.v
  let J := Jr + R l
  -- j += S[i]
  let s₁ := s.setV (dq 0) (VArr.b16.map2 (fun _ x y => x + y) (s.v (dq 0)) (s.v si))
  have e₁ : exec (.vop (.add .b16 (dq 0) (dq 0) si)) s = some s₁ := rfl
  have o₁ : VG.Proof.Rc4.AArch64.Only VG.Proof.Rc4.AArch64.stepRegs s s₁ := Only.setV _ (by decide) _
  have j₁ : s₁.v (dq 0) = VG.Proof.Rc4.AArch64.bc J := by rw [v_setV_self, hj, hi, VG.Proof.Rc4.AArch64.add_bc]
  have k₁ : VG.Proof.Rc4.AArch64.Consts s₁ := VG.Proof.Rc4.AArch64.consts_of_only hk o₁
  have t₁ : VG.Proof.Rc4.AArch64.tbyte s₁.v = R := by
    funext k; simp only [VG.Proof.Rc4.AArch64.tbyte, R]; rw [v_setV_of_ne _ _ ((show VG.Proof.Rc4.AArch64.NotTable (dq 0) by decide).ne _)]
  -- the quarters
  obtain ⟨s₂, run₂, a₂, b₂, c₂, o₂⟩ := VG.Proof.Rc4.AArch64.quarters_run (x := dq 0) (a := dq 1) (b := dq 2) (c := dq 3) k₁ J j₁ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have o₂' : VG.Proof.Rc4.AArch64.Only VG.Proof.Rc4.AArch64.stepRegs s s₂ := o₁.trans (o₂.mono (by decide))
  have j₂ : s₂.v (dq 0) = VG.Proof.Rc4.AArch64.bc J := by rw [o₂.2 _ (by decide), j₁]
  have t₂ : VG.Proof.Rc4.AArch64.tbyte s₂.v = R := by
    rw [← t₁]; funext k; simp only [VG.Proof.Rc4.AArch64.tbyte]
    rw [o₂.2 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(show VG.Proof.Rc4.AArch64.NotTable (dq 1) by decide).ne _, (show VG.Proof.Rc4.AArch64.NotTable (dq 2) by decide).ne _,
        (show VG.Proof.Rc4.AArch64.NotTable (dq 3) by decide).ne _⟩)]
  -- S[j]
  obtain ⟨s₃, run₃, v₃, o₃⟩ := VG.Proof.Rc4.AArch64.lookup_run (d := .v5) (t := .v6) (x := dq 0) (a := dq 1) (b := dq 2) (c := dq 3) J j₂ a₂ b₂ c₂ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have o₃' : VG.Proof.Rc4.AArch64.Only VG.Proof.Rc4.AArch64.stepRegs s s₃ := o₂'.trans (o₃.mono (by decide))
  have t₃ : VG.Proof.Rc4.AArch64.tbyte s₃.v = R := by
    rw [← t₂]; funext k; simp only [VG.Proof.Rc4.AArch64.tbyte]
    rw [o₃.2 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(show VG.Proof.Rc4.AArch64.NotTable .v5 by decide).ne _, (show VG.Proof.Rc4.AArch64.NotTable .v6 by decide).ne _⟩)]
  have v₃' : s₃.v .v5 = VG.Proof.Rc4.AArch64.bc (R J.toNat) := by rw [v₃, t₂]
  -- S[j] := S[i]
  have q₃ : VG.Proof.Rc4.AArch64.Quarters s₃ J := by
    intro q hq
    rw [o₃.2 _ (by revert q; decide)]
    rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
    · rw [j₂, show J ^^^ BitVec.ofNat 8 (64 * 0) = J from BitVec.xor_zero]
    · exact a₂
    · exact b₂
    · exact c₂
  have i₃ : s₃.v si = VG.Proof.Rc4.AArch64.bc (R l) := by
    rw [o₃.2 _ (by decide), o₂.2 _ (by decide), v_setV_of_ne _ _ (by decide), hi]
  obtain ⟨s₄, run₄, t₄, o₄⟩ := VG.Proof.Rc4.AArch64.writeN_run (VG.Proof.Rc4.AArch64.consts_of_only hk o₃') q₃ i₃ (Nat.le_refl 16)
  have o₄' : VG.Proof.Rc4.AArch64.Only VG.Proof.Rc4.AArch64.stepRegs s s₄ := o₃'.trans (o₄.mono (by decide))
  have tb₄ : ∀ k < 256, VG.Proof.Rc4.AArch64.tbyte s₄.v k = if k = J.toNat then R l else R k := by
    intro k hk
    rw [t₄ k hk, t₃]
    exact VG.Proof.Rc4.AArch64.ite_iff ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩ _ _
  have five₄ : s₄.v .v5 = VG.Proof.Rc4.AArch64.bc (R J.toNat) := by rw [o₄.2 _ (by decide), v₃']
  have i₄ : s₄.v si = VG.Proof.Rc4.AArch64.bc (R l) := by rw [o₄.2 _ (by decide), i₃]
  have j₄ : s₄.v (dq 0) = VG.Proof.Rc4.AArch64.bc J := by rw [o₄.2 _ (by decide), o₃.2 _ (by decide), j₂]
  have n₄ : prga = true → s₄.v negBase = VG.Proof.Rc4.AArch64.bc NB := fun h => by
    rw [o₄'.2 _ (by decide)]; exact hn h
  -- the output index
  obtain ⟨s₆, run₆, six₆, o₆⟩ : ∃ s₆, runBlock isa
      ((if prga then [.vop (.add .b16 .v6 si .v5), .vop (.add .b16 .v6 .v6 negBase)] else []) :
        List Instr) s₄ = some s₆ ∧
      (prga = true → s₆.v .v6 = VG.Proof.Rc4.AArch64.bc (R l + R J.toNat + NB)) ∧ VG.Proof.Rc4.AArch64.Only [.v6] s₄ s₆ := by
    cases prga
    · exact ⟨s₄, by simp only [Bool.false_eq_true, ite_false]; exact runBlock_nil,
        fun h => absurd h (by decide), Only.refl _ _⟩
    · let a := s₄.setV .v6 (VArr.b16.map2 (fun _ x y => x + y) (s₄.v si) (s₄.v .v5))
      let b := a.setV .v6 (VArr.b16.map2 (fun _ x y => x + y) (a.v .v6) (a.v negBase))
      refine ⟨b, ?_, fun _ => ?_, (Only.setV _ (by simp) _).trans (Only.setV _ (by simp) _)⟩
      · have ea : exec (.vop (.add .b16 .v6 si .v5)) s₄ = some a := rfl
        have eb : exec (.vop (.add .b16 .v6 .v6 negBase)) a = some b := rfl
        simp only [ite_true]
        rw [runBlock_cons, ea, runStep_some, runBlock_cons, eb, runStep_some, runBlock_nil]
      · simp only [b, v_setV_self, a, v_setV_of_ne _ _ (show negBase ≠ .v6 by decide), i₄, five₄,
          n₄ rfl, VG.Proof.Rc4.AArch64.add_bc]
  have t₆ : VG.Proof.Rc4.AArch64.tbyte s₆.v = VG.Proof.Rc4.AArch64.tbyte s₄.v := by
    funext k; simp only [VG.Proof.Rc4.AArch64.tbyte]; rw [o₆.2 _ (by simp [(show VG.Proof.Rc4.AArch64.NotTable .v6 by decide).ne _])]
  have five₆ : s₆.v .v5 = VG.Proof.Rc4.AArch64.bc (R J.toNat) := by rw [o₆.2 _ (by decide), five₄]
  have j₆ : s₆.v (dq 0) = VG.Proof.Rc4.AArch64.bc J := by rw [o₆.2 _ (by decide), j₄]
  -- the next S[i]
  let s₇ := s₆.setV si (VArr.b16.map2 (fun w _ _ => (s₆.v (treg ((l + 1) / 16))).extractLsb'
    (w * ((l + 1) % 16)) w) 0 0)
  have e₇ : exec (.vop (.dupE .b16 si (treg ((l + 1) / 16)) ((l + 1) % 16))) s₆ = some s₇ := by
    rw [VG.Proof.Rc4.AArch64.exec_vop']
    simp only [VOp.eval, VArr.esize, show (l + 1) % 16 < 128 / 8 by omega, ite_true]
    rfl
  have i₇ : s₇.v si = VG.Proof.Rc4.AArch64.bc (VG.Proof.Rc4.AArch64.tbyte s₄.v (l + 1)) := by
    rw [v_setV_self, VG.Proof.Rc4.AArch64.dupE_bc, ← t₆]; rfl
  -- S[i] := S[j]
  let s₈ := s₇.setV (treg 0) (setLane (s₇.v (treg 0)) 8 l ((s₇.v .v5).extractLsb' (8 * 0) 8))
  have e₈ : exec (.vop (.insE .b16 (treg 0) l .v5 0)) s₇ = some s₈ := by
    rw [VG.Proof.Rc4.AArch64.exec_vop']
    simp only [VOp.eval, VArr.esize, show l < 128 / 8 by omega, show 0 < 128 / 8 by omega,
      and_self, ite_true]
    rfl
  have five₇ : s₇.v .v5 = VG.Proof.Rc4.AArch64.bc (R J.toNat) := by rw [v_setV_of_ne _ _ (by decide), five₆]
  have t₇ : VG.Proof.Rc4.AArch64.tbyte s₇.v = VG.Proof.Rc4.AArch64.tbyte s₄.v := by
    rw [← t₆]; funext k; simp only [VG.Proof.Rc4.AArch64.tbyte]
    rw [v_setV_of_ne _ _ ((show VG.Proof.Rc4.AArch64.NotTable si by decide).ne _)]
  have tb₈ : ∀ k < 256, VG.Proof.Rc4.AArch64.tbyte s₈.v k = VG.Proof.Rc4.AArch64.swapR R l J.toNat k := by
    intro k hk
    by_cases h0 : k / 16 = 0
    · have : VG.Proof.Rc4.AArch64.tbyte s₈.v k = vbyte (setLane (s₇.v (treg 0)) 8 l ((s₇.v .v5).extractLsb' (8 * 0) 8))
          (k % 16) := by simp only [VG.Proof.Rc4.AArch64.tbyte, h0, s₈, v_setV_self]
      rw [this, VG.Proof.Rc4.AArch64.vbyte_setLane _ _ hl (by omega), VG.Proof.Rc4.AArch64.extract_byte, five₇, VG.Proof.Rc4.AArch64.vbyte_bc _ (by decide)]
      have old : vbyte (s₇.v (treg 0)) (k % 16) = VG.Proof.Rc4.AArch64.tbyte s₄.v k := by
        rw [← t₇]; simp only [VG.Proof.Rc4.AArch64.tbyte, h0]
      rw [old, tb₄ k hk, VG.Proof.Rc4.AArch64.swapR]
      exact VG.Proof.Rc4.AArch64.ite_iff ⟨fun h => by omega, fun h => by omega⟩ _ _
    · have : VG.Proof.Rc4.AArch64.tbyte s₈.v k = VG.Proof.Rc4.AArch64.tbyte s₇.v k := by
        simp only [VG.Proof.Rc4.AArch64.tbyte, s₈]
        rw [v_setV_of_ne _ _ (fun h => h0 (VG.Proof.Rc4.AArch64.treg_inj _ (by omega) _ (by decide) h))]
      rw [this, t₇, tb₄ k hk, VG.Proof.Rc4.AArch64.swapR, ite_eq_right (show ¬ k = l by omega)]
  refine ⟨s₈, ?_, tb₈, ?_, ?_, ?_, ?_⟩
  · rw [VG.Proof.Rc4.AArch64.swapStep_eq, List.singleton_append, runBlock_cons, e₁, runStep_some]
    refine VG.Proof.Rc4.AArch64.runBlock_cat_some run₂ (VG.Proof.Rc4.AArch64.runBlock_cat_some run₃ (VG.Proof.Rc4.AArch64.runBlock_cat_some run₄
      (VG.Proof.Rc4.AArch64.runBlock_cat_some run₆ ?_)))
    rw [runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  · rw [v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide), j₆]
  · rw [v_setV_of_ne _ _ (by decide), i₇, tb₄ _ (by omega), VG.Proof.Rc4.AArch64.swapR,
      ite_eq_right (show ¬ (l + 1 = l) by omega)]
  · intro hp
    rw [v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide), six₆ hp]
  · exact ((o₄'.trans (o₆.mono (by decide))).trans (Only.setV _ (by decide) _)).trans
      (Only.setV _ (by decide) _)

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Output`. -/
section

/-!
# A keystream byte

`output_ok`: with the output index `X` (from the base) broadcast in `v6`,
the keystream byte `S[X]` is looked up and XORed into the data byte at `x1`;
`x1` and `x2` advance.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

theorem low_byte (K : BitVec 8) : ((VG.Proof.Rc4.AArch64.bc K).extractLsb' 0 32).setWidth 8 = K := by
  have h := VG.Proof.Rc4.AArch64.vbyte_bc K (e := 0) (by decide)
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (·.getLsbD i) h
  simp only [vbyte, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.mul_zero,
    Nat.zero_add] at this
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show i < 32 by omega, Nat.zero_add]
  exact this

theorem xor_low_byte (a : BitVec 8) (w : BitVec 32) :
    ((a.setWidth 32 ^^^ w).setWidth 8) = a ^^^ w.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show i < 32 by omega]

/-- The scalar part: the byte's XOR, and the pointer and count. -/
theorem outScalar_ok {s : State} {K : BitVec 8} (h7 : s.v .v7 = VG.Proof.Rc4.AArch64.bc K)
    (hd : InRegions s.wr (s.gpr .x1) 1) :
    WP isa (.block [.umov .w .x6 .v7 0, .ldrb .x7 .x1 0, .logic .eor .w .x7 .x7 .x6, .strb .x7 .x1 0,
        .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1]) s fun t =>
      t.mem = s.mem.write (s.gpr .x1) 1 (s.mem (s.gpr .x1) ^^^ K) ∧
      t.gpr .x1 = s.gpr .x1 + 1 ∧ t.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .x1) 1 := by
    obtain ⟨region, hregion, hc⟩ := hd
    exact ⟨region, List.mem_append_right _ hregion, hc⟩
  have hc8 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x :=
    (BitVec.setWidth_setWidth_of_le x (by decide)).trans (BitVec.setWidth_eq x)
  have read1 (m : Mem) (p : Addr) : m.read p 1 = m p := by
    change (0#0 ++ m p : BitVec 8) = m p
    exact BitVec.zero_width_append _ _
  rrun [State.store, hd, hr, read1, hc8, h7, VG.Proof.Rc4.AArch64.xor_low_byte, VG.Proof.Rc4.AArch64.low_byte]
  refine ⟨fun r h1 h2 h6 h7 => by simp [h1, h2, h6, h7], ?_⟩
  simp [State.write]

/-- The registers the output changes. -/
def outRegs : List VReg := [.v1, .v2, .v3, .v7]

theorem output_ok {s : State} (hk : VG.Proof.Rc4.AArch64.Consts s) {X : BitVec 8} (hx : s.v .v6 = VG.Proof.Rc4.AArch64.bc X)
    (hd : InRegions s.wr (s.gpr .x1) 1) :
    WP isa (.block output) s fun t =>
      t.mem = s.mem.write (s.gpr .x1) 1 (s.mem (s.gpr .x1) ^^^ VG.Proof.Rc4.AArch64.tbyte s.v X.toNat) ∧
      t.gpr .x1 = s.gpr .x1 + 1 ∧ t.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      (∀ r, r ∉ VG.Proof.Rc4.AArch64.outRegs → t.v r = s.v r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain ⟨s₁, run₁, a₁, b₁, c₁, o₁⟩ := VG.Proof.Rc4.AArch64.quarters_run (x := .v6) (a := .v1) (b := .v2) (c := .v3) hk X hx
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have x₁ : s₁.v .v6 = VG.Proof.Rc4.AArch64.bc X := by rw [o₁.2 _ (by decide), hx]
  obtain ⟨s₂, run₂, v₂, o₂⟩ := VG.Proof.Rc4.AArch64.lookup_run (d := .v7) (t := .v1) (x := .v6) (a := .v1) (b := .v2)
    (c := .v3) X x₁ a₁ b₁ c₁ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  have t₁ : VG.Proof.Rc4.AArch64.tbyte s₁.v = VG.Proof.Rc4.AArch64.tbyte s.v := by
    funext k; simp only [VG.Proof.Rc4.AArch64.tbyte]
    rw [o₁.2 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(show VG.Proof.Rc4.AArch64.NotTable .v1 by decide).ne _, (show VG.Proof.Rc4.AArch64.NotTable .v2 by decide).ne _,
        (show VG.Proof.Rc4.AArch64.NotTable .v3 by decide).ne _⟩)]
  rw [t₁] at v₂
  have o : VG.Proof.Rc4.AArch64.Only VG.Proof.Rc4.AArch64.outRegs s s₂ := (o₁.mono (by decide)).trans (o₂.mono (by decide))
  rw [output, WP.block_append_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  have hd₂ : InRegions s₂.wr (s₂.gpr .x1) 1 := by rw [o.wr, o.gpr]; exact hd
  refine WP.mono (VG.Proof.Rc4.AArch64.outScalar_ok v₂ hd₂) fun t ⟨m, x1, x2, g, v, rd, wr, sp⟩ => ?_
  refine ⟨by rw [m, o.mem, o.gpr], by rw [x1, o.gpr], by rw [x2, o.gpr],
    fun r a b c d => by rw [g r a b c d, o.gpr], fun r hr => by rw [v, o.2 r hr],
    by rw [rd, o.rd], by rw [wr, o.wr], by rw [sp, o.sp]⟩

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Prga`. -/
section

/-!
# The table registers as an RC4 context

The table registers hold the table `T` from the base `B` (`TableIn`): byte
`k` is `T[B + k]`. With `j - B` broadcast in `v0` and `-B` in `v14`
(`PrgaRegs`), one byte of the stream (`byte_ok`: a swap step and the
output) does what RC4's `step` does.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- `B` as a byte. -/
abbrev bB (B : Nat) : BitVec 8 := BitVec.ofNat 8 B

/-- The table registers hold `T` from the base `B`. -/
def TableIn (s : State) (B : Nat) (T : Table) : Prop :=
  ∀ k < 256, VG.Proof.Rc4.AArch64.tbyte s.v k = T.getD (BitVec.ofNat 8 (B + k)).toNat 0

theorem ofNat_add_eq_iff {B k m : Nat} (hk : k < 256) (hm : m < 256) :
    BitVec.ofNat 8 (B + k) = BitVec.ofNat 8 (B + m) ↔ k = m := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  · intro h; rw [h]

theorem ofNat_add_eq_j {B k : Nat} (hk : k < 256) (j : BitVec 8) :
    BitVec.ofNat 8 (B + k) = j ↔ k = (j - VG.Proof.Rc4.AArch64.bB B).toNat := by
  have hj := j.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega

/-- The swap of positions `l` and `J` of the registers' table is RC4's swap
of `B + l` and `j`. -/
theorem swapR_eq (T : Table) {B l : Nat} (hl : l < 256) {R : Nat → BitVec 8}
    (hR : ∀ k < 256, R k = T.getD (BitVec.ofNat 8 (B + k)).toNat 0) (j : BitVec 8) {k : Nat}
    (hk : k < 256) :
    VG.Proof.Rc4.AArch64.swapR R l (j - VG.Proof.Rc4.AArch64.bB B).toNat k = (swap T (BitVec.ofNat 8 (B + l)) j).getD (BitVec.ofNat 8 (B + k)).toNat 0 := by
  have hJ := (j - VG.Proof.Rc4.AArch64.bB B).isLt
  have hJj : BitVec.ofNat 8 (B + (j - VG.Proof.Rc4.AArch64.bB B).toNat) = j := (VG.Proof.Rc4.AArch64.ofNat_add_eq_j hJ j).mpr rfl
  rw [swap_get]
  simp only [VG.Proof.Rc4.AArch64.swapR, VG.Proof.Rc4.AArch64.ofNat_add_eq_j hk j, VG.Proof.Rc4.AArch64.ofNat_add_eq_iff hk hl]
  by_cases h1 : k = l
  · subst h1
    by_cases h2 : k = (j - VG.Proof.Rc4.AArch64.bB B).toNat
    · simp only [ite_true, h2, hR _ hJ]
    · simp only [ite_true, h2, ite_false, hR _ hJ, hJj]
  · by_cases h2 : k = (j - VG.Proof.Rc4.AArch64.bB B).toNat
    · have h1' : ¬ (j - VG.Proof.Rc4.AArch64.bB B).toNat = l := fun h => h1 (h2.trans h)
      simp only [h2, h1', ite_true, ite_false, hR _ hl]
    · simp only [h1, h2, ite_false, hR _ hk]

/-- The PRGA's registers hold the context `c` from the base `B`: its table,
`j - B`, and `-B`. -/
structure PrgaRegs (s : State) (B : Nat) (c : Context) : Prop where
  table : VG.Proof.Rc4.AArch64.TableIn s B c.table
  j : s.v (dq 0) = VG.Proof.Rc4.AArch64.bc (c.j - VG.Proof.Rc4.AArch64.bB B)
  nb : s.v negBase = VG.Proof.Rc4.AArch64.bc (0 - VG.Proof.Rc4.AArch64.bB B)
  consts : VG.Proof.Rc4.AArch64.Consts s

theorem byte_add_sub (cj a B : BitVec 8) : cj - B + a = cj + a - B := by bv_omega

theorem idx_out (a b : BitVec 8) (B : Nat) :
    BitVec.ofNat 8 (B + (a + b + (0 - VG.Proof.Rc4.AArch64.bB B)).toNat) = a + b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub,
    show (0 : BitVec 8).toNat = 0 from rfl]
  have := a.isLt; have := b.isLt
  omega

/-- One byte of the stream, at lane `l` of the group whose base is `B`. -/
theorem byte_ok {l : Nat} (hl : l < 16) {B : Nat} {c : Context} {s : State} (h : VG.Proof.Rc4.AArch64.PrgaRegs s B c)
    (hi : c.i + 1 = BitVec.ofNat 8 (B + l)) (hsi : s.v si = VG.Proof.Rc4.AArch64.bc (VG.Proof.Rc4.AArch64.tbyte s.v l))
    (hd : InRegions s.wr (s.gpr .x1) 1) :
    WP isa (.block (swapStep true l ++ output)) s fun t =>
      VG.Proof.Rc4.AArch64.PrgaRegs t B (VG.Spec.Rc4.step c).1 ∧ t.v si = VG.Proof.Rc4.AArch64.bc (VG.Proof.Rc4.AArch64.tbyte t.v (l + 1)) ∧
      t.mem = s.mem.write (s.gpr .x1) 1 (s.mem (s.gpr .x1) ^^^ (VG.Spec.Rc4.step c).2) ∧
      t.gpr .x1 = s.gpr .x1 + 1 ∧ t.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      (∀ r, r ∉ VG.Proof.Rc4.AArch64.stepRegs → t.v r = s.v r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let T := c.table
  let i := c.i + 1
  let a := T.getD i.toNat 0
  let j := c.j + a
  let b := T.getD j.toNat 0
  have hR : ∀ k < 256, VG.Proof.Rc4.AArch64.tbyte s.v k = T.getD (BitVec.ofNat 8 (B + k)).toNat 0 := h.table
  have ha : VG.Proof.Rc4.AArch64.tbyte s.v l = a := by rw [hR l (by omega)]; simp only [a, i, hi]
  have hJ : c.j - VG.Proof.Rc4.AArch64.bB B + VG.Proof.Rc4.AArch64.tbyte s.v l = j - VG.Proof.Rc4.AArch64.bB B := by rw [ha, VG.Proof.Rc4.AArch64.byte_add_sub]
  obtain ⟨s₁, run₁, t₁, j₁, i₁, o6₁, o₁⟩ := VG.Proof.Rc4.AArch64.swapStep_run true hl h.consts h.j hsi fun _ => h.nb
  rw [hJ] at t₁ j₁ i₁ o6₁
  have tab₁ : ∀ k < 256, VG.Proof.Rc4.AArch64.tbyte s₁.v k = (swap T i j).getD (BitVec.ofNat 8 (B + k)).toNat 0 := by
    intro k hk; rw [t₁ k hk, VG.Proof.Rc4.AArch64.swapR_eq T (by omega) hR j hk, ← hi]
  have hb : VG.Proof.Rc4.AArch64.tbyte s.v (j - VG.Proof.Rc4.AArch64.bB B).toNat = b := by
    rw [hR _ (j - VG.Proof.Rc4.AArch64.bB B).isLt, (VG.Proof.Rc4.AArch64.ofNat_add_eq_j (j - VG.Proof.Rc4.AArch64.bB B).isLt j).mpr rfl]
  have six₁ : s₁.v .v6 = VG.Proof.Rc4.AArch64.bc (a + b + (0 - VG.Proof.Rc4.AArch64.bB B)) := by rw [o6₁ rfl, ha, hb]
  have k₁ : VG.Proof.Rc4.AArch64.Consts s₁ := VG.Proof.Rc4.AArch64.consts_of_only h.consts o₁
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have hd₁ : InRegions s₁.wr (s₁.gpr .x1) 1 := by rw [o₁.wr, o₁.gpr]; exact hd
  refine WP.mono (VG.Proof.Rc4.AArch64.output_ok k₁ six₁ hd₁) fun t ⟨m, x1, x2, g, v, rd, wr, sp⟩ => ?_
  have tt : VG.Proof.Rc4.AArch64.tbyte t.v = VG.Proof.Rc4.AArch64.tbyte s₁.v := by
    funext k; simp only [VG.Proof.Rc4.AArch64.tbyte]; rw [v _ (by
      simp only [VG.Proof.Rc4.AArch64.outRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(show VG.Proof.Rc4.AArch64.NotTable .v1 by decide).ne _, (show VG.Proof.Rc4.AArch64.NotTable .v2 by decide).ne _,
        (show VG.Proof.Rc4.AArch64.NotTable .v3 by decide).ne _, (show VG.Proof.Rc4.AArch64.NotTable .v7 by decide).ne _⟩)]
  have step_c : VG.Spec.Rc4.step c = ({ table := swap T i j, i, j }, (swap T i j).getD (a + b).toNat 0) :=
    step_eq c
  rw [step_c]
  refine ⟨⟨fun k hk => by rw [tt, tab₁ k hk], by rw [v _ (by decide), j₁],
      by rw [v _ (by decide), o₁.2 _ (by decide), h.nb], k₁.congr fun r hr => v r (by
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)⟩,
    by rw [v _ (by decide), i₁, tt, t₁ _ (by omega)], ?_, by rw [x1, o₁.gpr], by rw [x2, o₁.gpr],
    fun r a b c d => by rw [g r a b c d, o₁.gpr], fun r hr => ?_, by rw [rd, o₁.rd],
    by rw [wr, o₁.wr], by rw [sp, o₁.sp]⟩
  · rw [m, o₁.mem, o₁.gpr, tab₁ _ (by exact (a + b + (0 - VG.Proof.Rc4.AArch64.bB B)).isLt), VG.Proof.Rc4.AArch64.idx_out]
  · have hr' : r ∉ VG.Proof.Rc4.AArch64.outRegs := fun h' => hr (by
      simp only [VG.Proof.Rc4.AArch64.outRegs, List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl <;> decide)
    rw [v r hr', o₁.2 r hr]

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Rotate`. -/
section

/-!
# The rotation after a group

`rotate_ok`: the table registers move down by one (byte `k` becomes the old
byte `k + 16`, around the table), `j` and `-B` move back by 16, and the base
in `x8` advances by 16.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

def movs (n : Nat) : List Instr := (List.range n).map fun r => .vop (.mov (treg r) (treg (r + 1)))

theorem movs_succ (n : Nat) :
    VG.Proof.Rc4.AArch64.movs (n + 1) = VG.Proof.Rc4.AArch64.movs n ++ ([.vop (.mov (treg n) (treg (n + 1)))] : List Instr) := by
  simp only [VG.Proof.Rc4.AArch64.movs, List.range_succ, List.map_append, List.map_cons, List.map_nil]

theorem movs_run (s : State) {n : Nat} (hn : n ≤ 15) :
    ∃ t, runBlock isa (VG.Proof.Rc4.AArch64.movs n) s = some t ∧ (∀ r < 16, t.v (treg r) =
      if r < n then s.v (treg (r + 1)) else s.v (treg r)) ∧ VG.Proof.Rc4.AArch64.Only (treg 0 :: (List.range 15).map treg) s t := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun r _ => by simp, Only.refl _ _⟩
  | succ n ih =>
    obtain ⟨t, run, v, o⟩ := ih (by omega)
    let t' := t.setV (treg n) (t.v (treg (n + 1)))
    refine ⟨t', ?_, fun r hr => ?_, o.trans (Only.setV _ (by
      simp only [List.mem_cons, List.mem_map, List.mem_range]
      exact .inr ⟨n, by omega, rfl⟩) _)⟩
    · rw [VG.Proof.Rc4.AArch64.movs_succ]
      exact VG.Proof.Rc4.AArch64.runBlock_cat_some run (by rw [runBlock_cons]; exact rfl)
    · by_cases h : r = n
      · subst h
        simp only [t', v_setV_self, v (r + 1) (by omega), show ¬ r + 1 < r by omega, ite_false,
          show r < r + 1 by omega, ite_true]
      · rw [v_setV_of_ne _ _ (fun e => h (VG.Proof.Rc4.AArch64.treg_inj _ hr _ (by omega) e)), v r hr]
        exact VG.Proof.Rc4.AArch64.ite_iff ⟨fun h' => by omega, fun h' => by omega⟩ _ _

theorem lanes_diff : VArr.b16.map2 (fun _ x y => x - y) (VG.Proof.Rc4.AArch64.laneNums 1) (VG.Proof.Rc4.AArch64.laneNums 0) = VG.Proof.Rc4.AArch64.bc 16 :=
  VG.Proof.Rc4.AArch64.vbyte_ext fun e he => by
    rw [VG.Proof.Rc4.AArch64.vbyte_map2 _ _ _ he, VG.Proof.Rc4.AArch64.laneNums, VG.Proof.Rc4.AArch64.laneNums, vbyte_ofVBytes _ he, vbyte_ofVBytes _ he,
      VG.Proof.Rc4.AArch64.vbyte_bc _ he]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (16 : BitVec 8).toNat = 16 from rfl]
    omega

theorem rotate_eq (prga : Bool) : rotate prga =
    ([.vop (.sub .b16 .v7 (lanes 1) (lanes 0)), .vop (.sub .b16 (dq 0) (dq 0) .v7)] : List Instr) ++
      ((if prga then [.vop (.sub .b16 negBase negBase .v7)] else []) ++
        (([.vop (.mov .v7 (treg 0))] : List Instr) ++ (VG.Proof.Rc4.AArch64.movs 15 ++
          ([.vop (.mov (treg 15) .v7), .addImm .x .x8 .x8 16] : List Instr)))) := by
  simp only [rotate, VG.Proof.Rc4.AArch64.movs, List.append_assoc]

/-- The vector registers a rotation changes. -/
def rotRegs : List VReg := .v7 :: dq 0 :: negBase :: (List.range 16).map treg

theorem rotate_ok (prga : Bool) {s : State} (hk : VG.Proof.Rc4.AArch64.Consts s) {J NB : BitVec 8}
    (hj : s.v (dq 0) = VG.Proof.Rc4.AArch64.bc J) (hn : prga = true → s.v negBase = VG.Proof.Rc4.AArch64.bc NB) :
    WP isa (.block (rotate prga)) s fun t =>
      (∀ k < 256, VG.Proof.Rc4.AArch64.tbyte t.v k = VG.Proof.Rc4.AArch64.tbyte s.v ((k + 16) % 256)) ∧ t.v (dq 0) = VG.Proof.Rc4.AArch64.bc (J - 16) ∧
      t.v negBase = (if prga then VG.Proof.Rc4.AArch64.bc (NB - 16) else s.v negBase) ∧
      t.gpr .x8 = s.gpr .x8 + 16 ∧ (∀ r, r ≠ .x8 → t.gpr r = s.gpr r) ∧
      (∀ r, r ∉ VG.Proof.Rc4.AArch64.rotRegs → t.v r = s.v r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let s₁ := s.setV .v7 (VArr.b16.map2 (fun _ x y => x - y) (s.v (lanes 1)) (s.v (lanes 0)))
  have v₁ : s₁.v .v7 = VG.Proof.Rc4.AArch64.bc 16 := by
    rw [v_setV_self, hk.lns 1 (by decide), hk.lns 0 (by decide), VG.Proof.Rc4.AArch64.lanes_diff]
  let s₂ := s₁.setV (dq 0) (VArr.b16.map2 (fun _ x y => x - y) (s₁.v (dq 0)) (s₁.v .v7))
  have j₂ : s₂.v (dq 0) = VG.Proof.Rc4.AArch64.bc (J - 16) := by
    rw [v_setV_self, v₁, v_setV_of_ne _ _ (by decide), hj, VG.Proof.Rc4.AArch64.sub_bc]
  obtain ⟨s₃, run₃, n₃, o₃⟩ : ∃ s₃, runBlock isa
      ((if prga then [.vop (.sub .b16 negBase negBase .v7)] else []) : List Instr) s₂ = some s₃ ∧
      s₃.v negBase = (if prga then VG.Proof.Rc4.AArch64.bc (NB - 16) else s.v negBase) ∧ VG.Proof.Rc4.AArch64.Only [negBase] s₂ s₃ := by
    cases prga
    · refine ⟨s₂, by simp only [Bool.false_eq_true, ite_false]; exact runBlock_nil, ?_, Only.refl _ _⟩
      simp only [Bool.false_eq_true, ite_false]
      rw [v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide)]
    · refine ⟨s₂.setV negBase (VArr.b16.map2 (fun _ x y => x - y) (s₂.v negBase) (s₂.v .v7)),
        by simp only [ite_true]; rw [runBlock_cons]; rfl, ?_, Only.setV _ (by simp) _⟩
      simp only [ite_true]
      rw [v_setV_self, v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide), hn rfl,
        v_setV_of_ne _ _ (by decide), v₁, VG.Proof.Rc4.AArch64.sub_bc]
  let s₄ := s₃.setV .v7 (s₃.v (treg 0))
  obtain ⟨s₅, run₅, v₅, o₅⟩ := VG.Proof.Rc4.AArch64.movs_run s₄ (n := 15) (Nat.le_refl _)
  let s₆ := s₅.setV (treg 15) (s₅.v .v7)
  let s₇ := s₆.write .x .x8 (s₆.read .x .x8 + BitVec.ofNat _ 16)
  have run : runBlock isa (rotate prga) s = some s₇ := by
    rw [VG.Proof.Rc4.AArch64.rotate_eq]
    refine VG.Proof.Rc4.AArch64.runBlock_cat_some (s₁ := s₂) (by
      rw [runBlock_cons, show exec (.vop (.sub .b16 .v7 (lanes 1) (lanes 0))) s = some s₁ from rfl,
        runStep_some, runBlock_cons, show exec (.vop (.sub .b16 (dq 0) (dq 0) .v7)) s₁ = some s₂ from rfl,
        runStep_some, runBlock_nil]) ?_
    refine VG.Proof.Rc4.AArch64.runBlock_cat_some run₃ ?_
    rw [List.singleton_append, runBlock_cons, show exec (.vop (.mov .v7 (treg 0))) s₃ = some s₄ from rfl,
      runStep_some]
    refine VG.Proof.Rc4.AArch64.runBlock_cat_some run₅ ?_
    rw [runBlock_cons, show exec (.vop (.mov (treg 15) .v7)) s₅ = some s₆ from rfl, runStep_some,
      runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil]
  refine WP.of_runBlock ⟨s₇, run, ?_⟩
  have v₇ : s₇.v = s₆.v := rfl
  have movsRegs : ∀ r, r ∉ (treg 0 :: (List.range 15).map treg) → r ∉ (List.range 16).map treg →
      True := fun _ _ _ => trivial
  -- what the moves leave alone
  have keep₅ : ∀ r, VG.Proof.Rc4.AArch64.NotTable r → s₅.v r = s₄.v r := fun r hr => o₅.2 r (by
    simp only [List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists, not_and]
    exact ⟨fun h => hr.ne 0 h.symm, fun a _ h => hr.ne a h⟩)
  have keep₂ : ∀ r, VG.Proof.Rc4.AArch64.NotTable r → r ≠ .v7 → r ≠ dq 0 → r ≠ negBase → s₃.v r = s.v r := by
    intro r _ h7 hd hn
    rw [o₃.2 r (by simp [hn]), v_setV_of_ne _ _ hd, v_setV_of_ne _ _ h7]
  have tab₃ : ∀ a < 16, s₃.v (treg a) = s.v (treg a) := by
    intro a ha
    rw [o₃.2 _ (by simp; exact fun h => absurd h (by revert a; decide)),
      v_setV_of_ne _ _ (by revert a; decide), v_setV_of_ne _ _ (by revert a; decide)]
  have g₆ : s₆.gpr = s.gpr := by
    show s₅.gpr = s.gpr; rw [o₅.gpr]; show s₃.gpr = s.gpr; rw [o₃.gpr]; rfl
  have m₇ : s₇.mem = s.mem := by
    show s₅.mem = s.mem; rw [o₅.mem]; show s₃.mem = s.mem; rw [o₃.mem]; rfl
  have rd₇ : s₇.rd = s.rd := by
    show s₅.rd = s.rd; rw [o₅.rd]; show s₃.rd = s.rd; rw [o₃.rd]; rfl
  have wr₇ : s₇.wr = s.wr := by
    show s₅.wr = s.wr; rw [o₅.wr]; show s₃.wr = s.wr; rw [o₃.wr]; rfl
  have sp₇ : s₇.sp = s.sp := by
    show s₅.sp = s.sp; rw [o₅.sp]; show s₃.sp = s.sp; rw [o₃.sp]; rfl
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_, m₇, rd₇, wr₇, sp₇⟩
  · simp only [VG.Proof.Rc4.AArch64.tbyte, v₇]
    by_cases h15 : k / 16 = 15
    · rw [h15, show s₆.v (treg 15) = s₅.v .v7 from v_setV_self _ _ _,
        keep₅ _ (by decide), v_setV_self, tab₃ 0 (by decide),
        show (k + 16) % 256 / 16 = 0 by omega, show (k + 16) % 256 % 16 = k % 16 by omega]
    · rw [v_setV_of_ne _ _ (fun e => h15 (VG.Proof.Rc4.AArch64.treg_inj _ (by omega) _ (by decide) e)),
        v₅ _ (by omega), ite_eq_left (show k / 16 < 15 by omega),
        v_setV_of_ne _ _ ((show VG.Proof.Rc4.AArch64.NotTable .v7 by decide).ne _), tab₃ _ (by omega),
        show (k + 16) % 256 / 16 = k / 16 + 1 by omega, show (k + 16) % 256 % 16 = k % 16 by omega]
  · rw [v₇, v_setV_of_ne _ _ ((show VG.Proof.Rc4.AArch64.NotTable (dq 0) by decide).ne _ |>.symm),
      keep₅ _ (by decide), v_setV_of_ne _ _ (by decide), o₃.2 _ (by decide), j₂]
  · rw [v₇, v_setV_of_ne _ _ ((show VG.Proof.Rc4.AArch64.NotTable negBase by decide).ne _ |>.symm),
      keep₅ _ (by decide), v_setV_of_ne _ _ (by decide), n₃]
  · simp only [s₇, State.write, State.read, BitVec.setWidth_eq, ite_true]
    rw [g₆]; rfl
  · simp only [s₇, State.write, BitVec.setWidth_eq, hr, ite_false]
    rw [g₆]
  · simp only [VG.Proof.Rc4.AArch64.rotRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists,
      not_and] at hr
    obtain ⟨h7, hd, hn, ht⟩ := hr
    rw [v₇, v_setV_of_ne _ _ (fun e => ht 15 (by decide) e.symm), keep₅ r (fun a ha e => ht a (by omega) e),
      v_setV_of_ne _ _ h7, o₃.2 r (by simp [hn]), v_setV_of_ne _ _ hd, v_setV_of_ne _ _ h7]

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Lanes`. -/
section

/-!
# A group of sixteen bytes

In a group whose base is `B`, lane `n` is skipped while `x5` counts lanes to
skip (the first group starts at lane `sk = (i + 1) mod 16`), does nothing
once the data has ended, and otherwise produces the next byte of the stream
(`lane_ok`). `p` bytes of the `N` at `D` are done after lane `n`:
`p = min N (p₀ + (n - sk))` (`LaneInv`).
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- The stream's fixed parameters: the context it starts from, the data and
its original bytes, and the state the loop starts in. -/
structure Glob where
  c₀ : Context
  D : Addr
  N : Nat
  M₀ : Mem
  s₀ : State

/-- `p` bytes of the data done. -/
structure DataAt (g : VG.Proof.Rc4.AArch64.Glob) (p : Nat) (s : State) : Prop where
  le : p ≤ g.N
  x1 : s.gpr .x1 = g.D + BitVec.ofNat 64 p
  x2 : s.gpr .x2 = BitVec.ofNat 64 (g.N - p)
  bytes : ∀ k < g.N, s.mem (g.D + BitVec.ofNat 64 k) =
    if k < p then g.M₀ (g.D + BitVec.ofNat 64 k) ^^^ ks g.c₀ k else g.M₀ (g.D + BitVec.ofNat 64 k)
  frame : Frame [⟨g.D, g.N⟩] g.M₀ s.mem

/-- What the loop keeps: the registers it does not use, the regions and the
stack pointer. -/
structure Kept (g : VG.Proof.Rc4.AArch64.Glob) (s : State) : Prop where
  gpr : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s.gpr r = g.s₀.gpr r
  rd : s.rd = g.s₀.rd
  wr : s.wr = g.s₀.wr
  sp : s.sp = g.s₀.sp

/-- The bytes done after lane `n` of the group with base `B` that starts
after `p₀` bytes, skipping its first `sk` lanes. -/
def doneAt (g : VG.Proof.Rc4.AArch64.Glob) (p₀ sk n : Nat) : Nat := min g.N (p₀ + (n - sk))

structure LaneInv (g : VG.Proof.Rc4.AArch64.Glob) (B p₀ sk n : Nat) (s : State) : Prop where
  prga : VG.Proof.Rc4.AArch64.PrgaRegs s B (stepN g.c₀ (VG.Proof.Rc4.AArch64.doneAt g p₀ sk n))
  data : VG.Proof.Rc4.AArch64.DataAt g (VG.Proof.Rc4.AArch64.doneAt g p₀ sk n) s
  x5 : s.gpr .x5 = BitVec.ofNat 64 (sk - n)
  x8 : s.gpr .x8 = BitVec.ofNat 64 B
  next : VG.Proof.Rc4.AArch64.doneAt g p₀ sk n < g.N →
    (stepN g.c₀ (VG.Proof.Rc4.AArch64.doneAt g p₀ sk n)).i + 1 = BitVec.ofNat 8 (B + max n sk) ∧
      s.v si = VG.Proof.Rc4.AArch64.bc (VG.Proof.Rc4.AArch64.tbyte s.v (max n sk))
  kept : VG.Proof.Rc4.AArch64.Kept g s
  vkept : ∀ r, r ∉ VG.Proof.Rc4.AArch64.stepRegs → r ≠ negBase → s.v r = g.s₀.v r

theorem eval_nonzero' (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.nonzero .x r) s = some (m != 0) := by
  show some (s.read .x r != 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · have hne : BitVec.ofNat 64 m ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] at this; simp at this; omega
    change (BitVec.ofNat 64 m != (0 : BitVec 64)) = (m != 0)
    simp only [bne, beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h0]

theorem eval_zero' (s : State) (r : Reg) {m : Nat} (h : s.gpr r = BitVec.ofNat 64 m)
    (hm : m < 2 ^ 64) : isa.eval (.zero .x r) s = some (m == 0) := by
  show some (s.read .x r == 0) = _
  simp only [State.read, BitVec.setWidth_eq, h]
  congr 1
  by_cases h0 : m = 0
  · subst h0; rfl
  · have hne : BitVec.ofNat 64 m ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm] at this; simp at this; omega
    change (BitVec.ofNat 64 m == (0 : BitVec 64)) = (m == 0)
    simp only [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr h0]

theorem write_byte_apply (m : Mem) (p x : Addr) (v : BitVec 8) :
    m.write p 1 v x = if x = p then v else m x := VG.Proof.Rc4.write_byte m p x v

/-- The data region is writable, and fits in the address space. -/
structure DataOk (g : VG.Proof.Rc4.AArch64.Glob) : Prop where
  wr : (⟨g.D, g.N⟩ : Region) ∈ g.s₀.wr
  fit : g.N < 2 ^ 64

theorem DataOk.byte {g : VG.Proof.Rc4.AArch64.Glob} (h : VG.Proof.Rc4.AArch64.DataOk g) {s : State} (hk : VG.Proof.Rc4.AArch64.Kept g s) {p : Nat} (hp : p < g.N) :
    InRegions s.wr (g.D + BitVec.ofNat 64 p) 1 :=
  ⟨_, hk.wr ▸ h.wr, Offset.contains_base _ (by omega) (by have := h.fit; omega)⟩

theorem lane_ok (g : VG.Proof.Rc4.AArch64.Glob) (hg : VG.Proof.Rc4.AArch64.DataOk g) {B p₀ sk n : Nat} (hsk : sk ≤ 15) (hn : n < 16) {s : State}
    (h : VG.Proof.Rc4.AArch64.LaneInv g B p₀ sk n s) : WP isa (lane n) s (VG.Proof.Rc4.AArch64.LaneInv g B p₀ sk (n + 1)) := by
  have hfit := hg.fit
  unfold lane
  apply WP.ite _ (VG.Proof.Rc4.AArch64.eval_nonzero' s .x5 h.x5 (by omega))
  · intro hz
    have hlt : n < sk := by simp at hz; omega
    let t := s.write .x .x5 (s.read .x .x5 - BitVec.ofNat _ 1)
    refine WP.of_runBlock ⟨t, by rw [runBlock_cons, exec_subImm_x (by decide), runStep_some,
      runBlock_nil], ?_⟩
    have hd : VG.Proof.Rc4.AArch64.doneAt g p₀ sk (n + 1) = VG.Proof.Rc4.AArch64.doneAt g p₀ sk n := by simp only [VG.Proof.Rc4.AArch64.doneAt]; omega
    have hm : max (n + 1) sk = max n sk := by omega
    have g5 : ∀ r, r ≠ .x5 → t.gpr r = s.gpr r := fun r hr => by simp [t, State.write, hr]
    have x5 : t.gpr .x5 = BitVec.ofNat 64 (sk - (n + 1)) := by
      simp only [t, State.write, State.read, BitVec.setWidth_eq, ite_true, h.x5]
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
      congr 1
    exact {
      prga := by
        rw [hd]
        exact ⟨h.prga.table, h.prga.j, h.prga.nb,
          ⟨h.prga.consts.lns, h.prga.consts.c64, h.prga.consts.c128⟩⟩
      data := by
        rw [hd]
        exact ⟨h.data.le, by rw [g5 _ (by decide), h.data.x1], by rw [g5 _ (by decide), h.data.x2],
          h.data.bytes, h.data.frame⟩
      x5 := x5
      x8 := by rw [g5 _ (by decide), h.x8]
      next := by rw [hd, hm]; exact h.next
      kept := ⟨fun r a b c d e f => by rw [g5 r c, h.kept.gpr r a b c d e f], h.kept.rd, h.kept.wr,
        h.kept.sp⟩
      vkept := h.vkept }
  · intro hnz
    have hge : sk ≤ n := by simp at hnz; omega
    let p := VG.Proof.Rc4.AArch64.doneAt g p₀ sk n
    have hp := h.data.le
    apply WP.ite _ (VG.Proof.Rc4.AArch64.eval_zero' s .x2 h.data.x2 (by omega))
    · intro hz
      have hpN : p = g.N := by simp at hz; omega
      apply WP.block_nil
      have hd : VG.Proof.Rc4.AArch64.doneAt g p₀ sk (n + 1) = p := by simp only [VG.Proof.Rc4.AArch64.doneAt, p] at hpN ⊢; omega
      exact {
        prga := by rw [hd]; exact h.prga
        data := by rw [hd]; exact h.data
        x5 := by rw [h.x5]; congr 1; omega
        x8 := h.x8
        next := fun hlt => absurd hlt (by omega)
        kept := h.kept
        vkept := h.vkept }
    · intro hnz2
      have hpN : p < g.N := by simp at hnz2; omega
      obtain ⟨hi, hsi⟩ := h.next hpN
      rw [show max n sk = n by omega] at hi hsi
      have hd : InRegions s.wr (s.gpr .x1) 1 := by rw [h.data.x1]; exact hg.byte h.kept hpN
      refine WP.mono (VG.Proof.Rc4.AArch64.byte_ok hn h.prga hi hsi hd) fun t ⟨pr, tsi, m, x1, x2, gg, vv, rd, wr, sp⟩ => ?_
      have hd1 : VG.Proof.Rc4.AArch64.doneAt g p₀ sk (n + 1) = p + 1 := by simp only [VG.Proof.Rc4.AArch64.doneAt, p] at hpN ⊢; omega
      have bytes : ∀ k < g.N, t.mem (g.D + BitVec.ofNat 64 k) =
          if k < p + 1 then g.M₀ (g.D + BitVec.ofNat 64 k) ^^^ ks g.c₀ k
          else g.M₀ (g.D + BitVec.ofNat 64 k) := by
        intro k hk
        rw [m, h.data.x1, VG.Proof.Rc4.AArch64.write_byte_apply]
        have hne : (g.D + BitVec.ofNat 64 k = g.D + BitVec.ofNat 64 p) ↔ k = p := by
          constructor
          · intro e; have := congrArg (fun x => (x - g.D).toNat) e
            simp only [Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at this
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact this
          · intro e; rw [e]
        by_cases hkp : k = p
        · subst hkp
          rw [ite_eq_left rfl, h.data.bytes _ hk, ite_eq_right (by omega), ite_eq_left (by omega)]
          rfl
        · rw [ite_eq_right (fun e => hkp (hne.mp e)), h.data.bytes k hk]
          exact VG.Proof.Rc4.AArch64.ite_iff ⟨fun h' => by omega, fun h' => by omega⟩ _ _
      have nexti : (stepN g.c₀ (p + 1)).i + 1 = BitVec.ofNat 8 (B + max (n + 1) sk) := by
        rw [show stepN g.c₀ (p + 1) = (VG.Spec.Rc4.step (stepN g.c₀ p)).1 from rfl, show max (n + 1) sk = n + 1 by omega]
        simp only [VG.Spec.Rc4.step]
        rw [hi]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 8).toNat = 1 from rfl]
        omega
      exact {
        prga := by rw [hd1]; exact pr
        data := by
          rw [hd1]
          refine ⟨by omega, ?_, ?_, bytes, ?_⟩
          · rw [x1, h.data.x1, BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
              BitVec.ofNat_add_ofNat]
          · rw [x2, h.data.x2, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
              BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
            congr 1
          · rw [m, h.data.x1]
            exact h.data.frame.write List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
        x5 := by
          rw [gg _ (by decide) (by decide) (by decide) (by decide), h.x5]; congr 1; omega
        x8 := by rw [gg _ (by decide) (by decide) (by decide) (by decide), h.x8]
        next := by
          rw [hd1]
          exact fun _ => ⟨nexti, by rw [tsi, show max (n + 1) sk = n + 1 by omega]⟩
        kept := ⟨fun r a b c d e f => by rw [gg r a b d e, h.kept.gpr r a b c d e f],
          rd.trans h.kept.rd, wr.trans h.kept.wr, sp.trans h.kept.sp⟩
        vkept := fun r hr hn => by rw [vv r hr, h.vkept r hr hn] }

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Group`. -/
section

/-!
# The groups

`group_ok`: sixteen lanes and the rotation take a group with base `B` that
starts after `p` bytes to the next group, with base `B + 16`, after
`min N (p + 16 - sk)` bytes and no lanes to skip. `loop_ok`: the groups run
until the data has ended.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem lanesFrom_ok (g : VG.Proof.Rc4.AArch64.Glob) (hg : VG.Proof.Rc4.AArch64.DataOk g) {B p sk : Nat} (hsk : sk ≤ 15) {n : Nat} (hn : n ≤ 16)
    {s : State} (h : VG.Proof.Rc4.AArch64.LaneInv g B p sk 0 s) : WP isa (lanesFrom n) s (VG.Proof.Rc4.AArch64.LaneInv g B p sk n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    exact WP.seq (WP.mono (ih (by omega)) fun t ht => VG.Proof.Rc4.AArch64.lane_ok g hg hsk (by omega) ht)

theorem ofNat_wrap (B k : Nat) : BitVec.ofNat 8 (B + (k + 16) % 256) = BitVec.ofNat 8 (B + 16 + k) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem byte_shift (x : BitVec 8) (B : Nat) : x - VG.Proof.Rc4.AArch64.bB B - 16 = x - VG.Proof.Rc4.AArch64.bB (B + 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (16 : BitVec 8).toNat = 16 from rfl]
  omega

theorem treg_step : ∀ a < 16, treg a ∈ VG.Proof.Rc4.AArch64.stepRegs := by decide

theorem group_ok (g : VG.Proof.Rc4.AArch64.Glob) (hg : VG.Proof.Rc4.AArch64.DataOk g) {B p sk : Nat} (hsk : sk ≤ 15) {s : State}
    (h : VG.Proof.Rc4.AArch64.LaneInv g B p sk 0 s) :
    WP isa group s (VG.Proof.Rc4.AArch64.LaneInv g (B + 16) (VG.Proof.Rc4.AArch64.doneAt g p sk 16) 0 0) := by
  apply WP.seq (WP.mono (VG.Proof.Rc4.AArch64.lanesFrom_ok g hg hsk (Nat.le_refl 16) h) fun s₁ h₁ => ?_)
  refine WP.mono (VG.Proof.Rc4.AArch64.rotate_ok true h₁.prga.consts h₁.prga.j fun _ => h₁.prga.nb) fun t ⟨tab, j, nb, x8, gg, vv, m, rd, wr, sp⟩ => ?_
  have hd0 : VG.Proof.Rc4.AArch64.doneAt g (VG.Proof.Rc4.AArch64.doneAt g p sk 16) 0 0 = VG.Proof.Rc4.AArch64.doneAt g p sk 16 := by
    have := h₁.data.le; simp only [VG.Proof.Rc4.AArch64.doneAt] at this ⊢; omega
  let q := VG.Proof.Rc4.AArch64.doneAt g p sk 16
  have notRot : ∀ r, r ∉ VG.Proof.Rc4.AArch64.rotRegs → r ∉ VG.Proof.Rc4.AArch64.stepRegs ∨ r = negBase → True := fun _ _ _ => trivial
  exact {
    prga := by
      rw [hd0]
      refine ⟨fun k hk => ?_, ?_, ?_, ?_⟩
      · rw [tab k hk, h₁.prga.table _ (by omega), VG.Proof.Rc4.AArch64.ofNat_wrap]
      · rw [j, VG.Proof.Rc4.AArch64.byte_shift]
      · simp only [ite_true] at nb; rw [nb, VG.Proof.Rc4.AArch64.byte_shift]
      · exact h₁.prga.consts.congr fun r hr => vv r (by
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    data := by
      rw [hd0]
      exact ⟨h₁.data.le, by rw [gg _ (by decide), h₁.data.x1], by rw [gg _ (by decide), h₁.data.x2],
        fun k hk => by rw [m]; exact h₁.data.bytes k hk, by rw [m]; exact h₁.data.frame⟩
    x5 := by rw [gg _ (by decide), h₁.x5]; congr 1; omega
    x8 := by
      rw [x8, h₁.x8, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
    next := by
      rw [hd0]
      intro hlt
      obtain ⟨hi, hsi⟩ := h₁.next hlt
      rw [show max 16 sk = 16 by omega] at hi hsi
      refine ⟨by rw [hi]; simp, ?_⟩
      rw [vv _ (by decide), hsi, show max 0 0 = 0 from rfl, tab 0 (by decide)]
    kept := ⟨fun r a b c d e f => by rw [gg r f, h₁.kept.gpr r a b c d e f], rd.trans h₁.kept.rd,
      wr.trans h₁.kept.wr, sp.trans h₁.kept.sp⟩
    vkept := fun r hr hn => by
      rw [vv r (by
        simp only [VG.Proof.Rc4.AArch64.rotRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists, not_and]
        refine ⟨fun e => hr (by rw [e]; decide), fun e => hr (by rw [e]; decide), hn,
          fun a ha e => hr (e ▸ VG.Proof.Rc4.AArch64.treg_step a ha)⟩), h₁.vkept r hr hn] }

/-- A group about to start, `m` bytes before the end. -/
def LoopInv (g : VG.Proof.Rc4.AArch64.Glob) (m : Nat) (s : State) : Prop :=
  ∃ B p sk, B % 16 = 0 ∧ m = g.N - p ∧ p < g.N ∧ sk ≤ 15 ∧ VG.Proof.Rc4.AArch64.LaneInv g B p sk 0 s

/-- The data has ended. -/
def LoopDone (g : VG.Proof.Rc4.AArch64.Glob) (s : State) : Prop := ∃ B sk, B % 16 = 0 ∧ VG.Proof.Rc4.AArch64.LaneInv g B g.N sk 0 s

theorem loop_ok (g : VG.Proof.Rc4.AArch64.Glob) (hg : VG.Proof.Rc4.AArch64.DataOk g) (m : Nat) {s : State} (h : VG.Proof.Rc4.AArch64.LoopInv g m s) :
    WP isa (.loop group (.nonzero .x .x2)) s (VG.Proof.Rc4.AArch64.LoopDone g) := by
  refine WP.loop (M := isa) (VG.Proof.Rc4.AArch64.LoopInv g) ?_ m s h
  intro m s ⟨B, p, sk, hB, hm, hp, hsk, h⟩
  refine WP.mono (VG.Proof.Rc4.AArch64.group_ok g hg hsk h) fun t ht => ?_
  have hfit := hg.fit
  let q := VG.Proof.Rc4.AArch64.doneAt g p sk 16
  have hd0 : VG.Proof.Rc4.AArch64.doneAt g q 0 0 = q := by
    have := ht.data.le; simp only [VG.Proof.Rc4.AArch64.doneAt, q] at this ⊢; omega
  have hq : q ≤ g.N := by have := ht.data.le; rw [hd0] at this; exact this
  have x2 : t.gpr .x2 = BitVec.ofNat 64 (g.N - q) := by rw [ht.data.x2, hd0]
  have flag := VG.Proof.Rc4.AArch64.eval_nonzero' t .x2 x2 (by omega)
  by_cases hend : q = g.N
  · left
    exact ⟨by rw [flag]; simp [hend], B + 16, 0, by omega, hend ▸ ht⟩
  · right
    exact ⟨by rw [flag]; simp; omega, g.N - q, by simp only [VG.Proof.Rc4.AArch64.doneAt, q] at hend ⊢; omega,
      B + 16, q, 0, by omega, rfl, by omega, by decide, ht⟩

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Rows`. -/
section

/-!
# The table in memory, rotated

`loadTable_ok` loads row `(B + 16 r) mod 256` of the table at `x0` into
table register `r`, for a base `B` (in `x8`) that is a multiple of 16, so
that the registers hold the table from `B` (`TableIn`); `storeTable_ok`
stores the registers back the same way.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem and255 (x : BitVec 64) : x &&& 255#64 = BitVec.ofNat 64 (x.toNat % 256) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (255#64).toNat = 2 ^ 8 - 1 := rfl
  rw [BitVec.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- The row address of table register `r`, for the base `B`. -/
def rowOff (B r : Nat) : Nat := (B + 16 * r) % 256

theorem hand (B r : Nat) : (BitVec.ofNat 64 B + BitVec.ofNat 64 (16 * r)) &&& 255#64 =
    BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.rowOff B r) := by
  rw [VG.Proof.Rc4.AArch64.and255, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, VG.Proof.Rc4.AArch64.rowOff]
  congr 1; omega

theorem rowOff_le {B : Nat} (r : Nat) (hB : B % 16 = 0) : VG.Proof.Rc4.AArch64.rowOff B r + 16 ≤ 256 := by
  simp only [VG.Proof.Rc4.AArch64.rowOff]; omega

theorem rowLoad_ok {s : State} {B r : Nat} (hr : r < 16) (hB : B % 16 = 0)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 B) (h9 : s.gpr .x9 = 255#64)
    (hp : InRegions (s.rd ++ s.wr) (s.gpr .x0) 256) :
    WP isa (.block (rowAddr r ++ ([.ldrq (treg r) .x7 0] : List Instr))) s fun t =>
      t.v (treg r) = s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.rowOff B r)) 16 ∧
      (∀ v, v ≠ treg r → t.v v = s.v v) ∧ (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hrow := region_offset _ _ _ (VG.Proof.Rc4.AArch64.rowOff B r) 16 (by simp only [VG.Proof.Rc4.AArch64.rowOff]; omega)
    (VG.Proof.Rc4.AArch64.rowOff_le r hB) hp
  unfold rowAddr
  have himm : 16 * r < 4096 := by omega
  rrun [List.cons_append, List.nil_append, himm, h8, h9, VG.Proof.Rc4.AArch64.hand, hrow]
  exact ⟨fun v hv => by simp [hv], fun g h6 h7 => by simp [h6, h7], rfl⟩

def loadN (n : Nat) : List Instr := (List.range n).flatMap fun r => rowAddr r ++ [.ldrq (treg r) .x7 0]

theorem loadN_succ (n : Nat) :
    VG.Proof.Rc4.AArch64.loadN (n + 1) = VG.Proof.Rc4.AArch64.loadN n ++ (rowAddr n ++ ([.ldrq (treg n) .x7 0] : List Instr)) := by
  simp only [VG.Proof.Rc4.AArch64.loadN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem loadN_ok {s : State} {B : Nat} (hB : B % 16 = 0) (h8 : s.gpr .x8 = BitVec.ofNat 64 B)
    (h9 : s.gpr .x9 = 255#64) (hp : InRegions (s.rd ++ s.wr) (s.gpr .x0) 256) {n : Nat} (hn : n ≤ 16) :
    WP isa (.block (VG.Proof.Rc4.AArch64.loadN n)) s fun t =>
      (∀ r < n, t.v (treg r) = s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.rowOff B r)) 16) ∧
      (∀ v, (∀ r < 16, v ≠ treg r) → t.v v = s.v v) ∧ (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨fun r h => absurd h (by omega), fun _ _ => rfl, fun _ _ _ => rfl,
      rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [VG.Proof.Rc4.AArch64.loadN_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨rows, vk, gk, m, rd, wr, sp⟩ => ?_
    have t8 : t.gpr .x8 = BitVec.ofNat 64 B := by rw [gk _ (by decide) (by decide), h8]
    have t9 : t.gpr .x9 = 255#64 := by rw [gk _ (by decide) (by decide), h9]
    have t0 : t.gpr .x0 = s.gpr .x0 := gk _ (by decide) (by decide)
    have tp : InRegions (t.rd ++ t.wr) (t.gpr .x0) 256 := by rw [rd, wr, t0]; exact hp
    refine WP.mono (VG.Proof.Rc4.AArch64.rowLoad_ok (s := t) (B := B) (r := n) (by omega) hB t8 t9 tp)
      fun u ⟨row, uv, ug, um, urd, uwr, usp⟩ => ?_
    refine ⟨fun r hr => ?_, fun v hv => by rw [uv v (hv n (by omega)), vk v hv],
      fun g a b => by rw [ug g a b, gk g a b], by rw [um, m], by rw [urd, rd], by rw [uwr, wr],
      by rw [usp, sp]⟩
    by_cases hrn : r = n
    · subst hrn; rw [row, m, t0]
    · rw [uv _ (fun e => hrn (VG.Proof.Rc4.AArch64.treg_inj _ (by omega) _ (by omega) e)), rows r (by omega)]

theorem loadTable_eq : loadTable = VG.Proof.Rc4.AArch64.loadN 16 := rfl

/-- Byte `e` of a 16-byte load. -/
theorem vbyte_read (m : Mem) (a : Addr) {e : Nat} (he : e < 16) :
    vbyte (m.read a 16) e = m (a + BitVec.ofNat 64 e) := Mem.extractLsb'_read m a he

theorem rows_table {s : State} {m : Mem} {p : Addr} {B : Nat} (hB : B % 16 = 0)
    (h : ∀ r < 16, s.v (treg r) = m.read (p + BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.rowOff B r)) 16) :
    VG.Proof.Rc4.AArch64.TableIn s B (contextAt m p).table := by
  intro k hk
  have hidx : VG.Proof.Rc4.AArch64.rowOff B (k / 16) + k % 16 = (BitVec.ofNat 8 (B + k)).toNat := by
    simp only [VG.Proof.Rc4.AArch64.rowOff, BitVec.toNat_ofNat]; omega
  rw [table_get, VG.Proof.Rc4.AArch64.tbyte, h _ (by omega), VG.Proof.Rc4.AArch64.vbyte_read _ _ (by omega), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, hidx]

/-! ## Storing the table -/

theorem rowStore_ok {s : State} {B r : Nat} (hr : r < 16) (hB : B % 16 = 0)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 B) (h9 : s.gpr .x9 = 255#64)
    (hp : InRegions s.wr (s.gpr .x0) 256) :
    WP isa (.block (rowAddr r ++ ([.strq (treg r) .x7 0] : List Instr))) s fun t =>
      t.mem = s.mem.write (s.gpr .x0 + BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.rowOff B r)) 16 (s.v (treg r)) ∧
      t.v = s.v ∧ (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hrow := region_offset _ _ _ (VG.Proof.Rc4.AArch64.rowOff B r) 16 (by simp only [VG.Proof.Rc4.AArch64.rowOff]; omega)
    (VG.Proof.Rc4.AArch64.rowOff_le r hB) hp
  have himm : 16 * r < 4096 := by omega
  unfold rowAddr
  rrun [List.cons_append, List.nil_append, himm, h8, h9, VG.Proof.Rc4.AArch64.hand, hrow, State.store]
  exact ⟨fun g h6 h7 => by simp [h6, h7], rfl⟩

def storeN (n : Nat) : List Instr := (List.range n).flatMap fun r => rowAddr r ++ [.strq (treg r) .x7 0]

theorem storeN_succ (n : Nat) :
    VG.Proof.Rc4.AArch64.storeN (n + 1) = VG.Proof.Rc4.AArch64.storeN n ++ (rowAddr n ++ ([.strq (treg n) .x7 0] : List Instr)) := by
  simp only [VG.Proof.Rc4.AArch64.storeN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem storeTable_eq : storeTable = VG.Proof.Rc4.AArch64.storeN 16 := rfl

/-- Rows `r` and `n` of the table do not overlap. -/
theorem row_apart {p : Addr} {B r n e : Nat} (hB : B % 16 = 0) (hr : r < 16) (hn : n < 16)
    (hrn : r ≠ n) (he : e < 16) :
    ¬ (p + BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.rowOff B r + e) - (p + BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.rowOff B n))).toNat < 16 := by
  rw [Offset.add_sub_add_left, Offset.toNat_sub_ofNat, BitVec.toNat_ofNat]
  simp only [VG.Proof.Rc4.AArch64.rowOff]
  omega

theorem storeN_ok {s : State} {B : Nat} (hB : B % 16 = 0) (h8 : s.gpr .x8 = BitVec.ofNat 64 B)
    (h9 : s.gpr .x9 = 255#64) (hp : InRegions s.wr (s.gpr .x0) 256) {n : Nat} (hn : n ≤ 16) :
    WP isa (.block (VG.Proof.Rc4.AArch64.storeN n)) s fun t =>
      (∀ r < n, ∀ e < 16, t.mem (s.gpr .x0 + BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.rowOff B r + e)) =
        vbyte (s.v (treg r)) e) ∧
      (∀ y, (∀ r < n, ¬ (y - (s.gpr .x0 + BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.rowOff B r))).toNat < 16) →
        t.mem y = s.mem y) ∧
      t.v = s.v ∧ (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact WP.block_nil ⟨fun r h => absurd h (by omega), fun _ _ => rfl, rfl,
      fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    rw [VG.Proof.Rc4.AArch64.storeN_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨rows, fr, tv, gk, rd, wr, sp⟩ => ?_
    have t8 : t.gpr .x8 = BitVec.ofNat 64 B := by rw [gk _ (by decide) (by decide), h8]
    have t9 : t.gpr .x9 = 255#64 := by rw [gk _ (by decide) (by decide), h9]
    have t0 : t.gpr .x0 = s.gpr .x0 := gk _ (by decide) (by decide)
    have tp : InRegions t.wr (t.gpr .x0) 256 := by rw [wr, t0]; exact hp
    refine WP.mono (VG.Proof.Rc4.AArch64.rowStore_ok (s := t) (B := B) (r := n) (by omega) hB t8 t9 tp)
      fun u ⟨um, uv, ug, urd, uwr, usp⟩ => ?_
    refine ⟨fun r hr e he => ?_, fun y hy => ?_, by rw [uv, tv], fun g a b => by rw [ug g a b, gk g a b],
      by rw [urd, rd], by rw [uwr, wr], by rw [usp, sp]⟩
    · rw [um, t0, Mem.write]
      by_cases hrn : r = n
      · subst hrn
        have d : (s.gpr .x0 + BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.rowOff B r + e) -
            (s.gpr .x0 + BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.rowOff B r))).toNat = e := by
          rw [Offset.add_sub_add_left, Offset.toNat_sub_ofNat]
          simp only [VG.Proof.Rc4.AArch64.rowOff, BitVec.toNat_ofNat]
          omega
        rw [d, ite_eq_left he, tv]
        rfl
      · rw [ite_eq_right (VG.Proof.Rc4.AArch64.row_apart hB (by omega) (by omega) hrn he), rows r (by omega) e he]
    · rw [um, t0, Mem.write, ite_eq_right (hy n (by omega)), fr y fun r hr => hy r (by omega)]

/-- The rows stored are the table from `B`. -/
theorem stored_table {s : State} {m : Mem} {p : Addr} {B : Nat} (hB : B % 16 = 0) {T : Table}
    (hT : VG.Proof.Rc4.AArch64.TableIn s B T)
    (h : ∀ r < 16, ∀ e < 16, m (p + BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.rowOff B r + e)) = vbyte (s.v (treg r)) e) :
    (contextAt m p).table = T := by
  apply Vector.ext
  intro k hk
  have hx := (BitVec.ofNat 8 k).isLt
  let r := (k + 256 - B % 256) % 256 / 16
  have hr : r < 16 := by omega
  have hrow : VG.Proof.Rc4.AArch64.rowOff B r + k % 16 = k := by simp only [VG.Proof.Rc4.AArch64.rowOff, r]; omega
  have e1 : (contextAt m p).table[k] = m (p + BitVec.ofNat 64 k) := by
    simp only [contextAt, Vector.getElem_ofFn]
  have e2 : m (p + BitVec.ofNat 64 k) = vbyte (s.v (treg r)) (k % 16) := by
    rw [← h r hr _ (by omega), hrow]
  rw [e1, e2]
  have := hT (16 * r + k % 16) (by omega)
  simp only [VG.Proof.Rc4.AArch64.tbyte, show (16 * r + k % 16) / 16 = r by omega, show (16 * r + k % 16) % 16 = k % 16 by omega] at this
  have hk' : (BitVec.ofNat 8 (B + (16 * r + k % 16))).toNat = k := by
    simp only [BitVec.toNat_ofNat, r]; omega
  rw [this, hk']
  simp [Vector.getD, Array.getD, hk]

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Consts`. -/
section

/-!
# The constants

`constants_ok`: the lane numbers 0–63 in `v8`–`v11`, and 64 and 128 in
every byte of `v12` and `v13`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

theorem lanes0 (v : BitVec 128) :
    setLane (setLane v 64 0 0x0706050403020100#64) 64 1 0x0f0e0d0c0b0a0908#64 = VG.Proof.Rc4.AArch64.laneNums 0 := by
  rw [setLane_two]
  decide

theorem lanes_next (q : Nat) :
    VArr.b16.map2 (fun _ x y => x + y) (VG.Proof.Rc4.AArch64.laneNums q) (VG.Proof.Rc4.AArch64.bc 16) = VG.Proof.Rc4.AArch64.laneNums (q + 1) :=
  VG.Proof.Rc4.AArch64.vbyte_ext fun e he => by
    rw [VG.Proof.Rc4.AArch64.vbyte_map2 _ _ _ he, VG.Proof.Rc4.AArch64.laneNums, VG.Proof.Rc4.AArch64.laneNums, vbyte_ofVBytes _ he, vbyte_ofVBytes _ he,
      VG.Proof.Rc4.AArch64.vbyte_bc _ he]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (16 : BitVec 8).toNat = 16 from rfl]
    omega

theorem dup_b16 (s : State) (r : Reg) (b : Nat) (h : s.gpr r = BitVec.ofNat 64 b) :
    (ofVBytes fun _ => (s.gpr r).setWidth 8) = VG.Proof.Rc4.AArch64.bc (BitVec.ofNat 8 b) := by
  rw [h]; congr; funext _
  apply BitVec.eq_of_toNat_eq; simp

theorem bc_lit (b : BitVec 8) : (ofVBytes fun _ => b) = VG.Proof.Rc4.AArch64.bc b := rfl

theorem const64_ok (s : State) (r : Reg) (v : BitVec 64) :
    WP isa (.block (const64 r v)) s fun t =>
      t.gpr r = v ∧ (∀ g, g ≠ r → t.gpr g = s.gpr g) ∧ t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr ∧ t.sp = s.sp := by
  refine WP.of_runBlock ⟨_, rfl, ?_, fun g hg => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
    exact movz_movk64' v
  · simp [State.write, hg]

theorem constants_ok (s : State) :
    WP isa (.block constants) s fun t =>
      VG.Proof.Rc4.AArch64.Consts t ∧ (∀ v, v ≠ .v7 → v ≠ .v8 → v ≠ .v9 → v ≠ .v10 → v ≠ .v11 → v ≠ .v12 → v ≠ .v13 →
        t.v v = s.v v) ∧ (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold constants
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.AArch64.const64_ok s .x6 _) fun a ⟨a6, ag, av, am, ard, awr, asp⟩ => ?_
  refine WP.mono (VG.Proof.Rc4.AArch64.const64_ok a .x7 _) fun b ⟨b7, bg, bv, bm, brd, bwr, bsp⟩ => ?_
  have b6 : b.gpr .x6 = 0x0706050403020100#64 := by rw [bg _ (by decide), a6]; rfl
  have b7' : b.gpr .x7 = 0x0f0e0d0c0b0a0908#64 := by rw [b7]; rfl
  have l0 : lanes 0 = .v8 := rfl
  have l1 : lanes 1 = .v9 := rfl
  have l2 : lanes 2 = .v10 := rfl
  have l3 : lanes 3 = .v11 := rfl
  have k64 : c64 = .v12 := rfl
  have k128 : c128 = .v13 := rfl
  rrun [l0, l1, l2, l3, k64, k128, b6, b7', VG.Proof.Rc4.AArch64.bc_lit]
  have L0 := VG.Proof.Rc4.AArch64.lanes0 (b.v .v8)
  have L1 : VArr.b16.map2 (fun _ x y => x + y) (VG.Proof.Rc4.AArch64.laneNums 0) (VG.Proof.Rc4.AArch64.bc 16#8) = VG.Proof.Rc4.AArch64.laneNums 1 := VG.Proof.Rc4.AArch64.lanes_next 0
  have L2 : VArr.b16.map2 (fun _ x y => x + y) (VG.Proof.Rc4.AArch64.laneNums 1) (VG.Proof.Rc4.AArch64.bc 16#8) = VG.Proof.Rc4.AArch64.laneNums 2 := VG.Proof.Rc4.AArch64.lanes_next 1
  have L3 : VArr.b16.map2 (fun _ x y => x + y) (VG.Proof.Rc4.AArch64.laneNums 2) (VG.Proof.Rc4.AArch64.bc 16#8) = VG.Proof.Rc4.AArch64.laneNums 3 := VG.Proof.Rc4.AArch64.lanes_next 2
  refine ⟨⟨fun q hq => ?_, ?_, ?_⟩, fun v h7 h8 h9 h10 h11 h12 h13 => ?_, fun g h6 h7 => ?_,
    ?_, ?_, ?_, ?_⟩
  · rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
      simp [State.setV, State.write, l0, l1, l2, l3, L0, L1, L2, L3]
  · simp [State.setV, State.write, k64]
  · simp [State.setV, State.write, k128]
  · simp [h7, h8, h9, h10, h11, h12, h13, bv, av]
  · simp [h6, h7, bg, ag]
  · simp [bm, am]
  · simp [brd, ard]
  · simp [bwr, awr]
  · simp [State.setV, State.write, bsp, asp]

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.ApplySetup`. -/
section

/-!
# The PRGA's setup

`applySetup_ok`: the setup saves the callee-saved vector registers it uses
in general-purpose registers, reads `i` and `j`, and computes the first
group's base `B = (i + 1) mod 256` rounded down to 16 and the lanes to skip
`sk = (i + 1) mod 16`; loads the table from `B`; and leaves the constants,
`j - B`, `-B` and `S[i + 1]` broadcast: the first group's `LaneInv`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- The first group, from `i`. -/
def i1 (i : BitVec 8) : Nat := (i.toNat + 1) % 256
def sk0 (i : BitVec 8) : Nat := VG.Proof.Rc4.AArch64.i1 i % 16
def base0 (i : BitVec 8) : Nat := VG.Proof.Rc4.AArch64.i1 i - VG.Proof.Rc4.AArch64.sk0 i

theorem incr_byte (I : BitVec 8) :
    (I.setWidth 64 + 1#64) &&& BitVec.setWidth 64 255#16 = BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.i1 I) := by
  rw [show BitVec.setWidth 64 255#16 = 255#64 from rfl, VG.Proof.Rc4.AArch64.and255]
  congr 1
  simp only [VG.Proof.Rc4.AArch64.i1, BitVec.toNat_add, BitVec.toNat_setWidth, show (1#64).toNat = 1 from rfl]
  have := I.isLt
  omega

theorem low4 (n : Nat) (hn : n < 256) :
    BitVec.ofNat 64 n &&& BitVec.setWidth 64 15#16 = BitVec.ofNat 64 (n % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.setWidth 64 15#16).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem read_byte' (m : Mem) (p : Addr) : m.read p 1 = m p := by
  change (0#0 ++ m p : BitVec 8) = m p
  exact BitVec.zero_width_append _ _

/-- The general-purpose registers the setup writes. -/
def setupRegs : List Reg :=
  [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The save and the scalar part of the setup. -/
theorem setupA_ok {s : State} (hp : InRegions (s.rd ++ s.wr) (s.gpr .x0) 258) :
    WP isa (.block (save true ++ ([.ldrb .x12 .x0 256, .ldrb .x13 .x0 257, .movz .x .x9 255 0,
      .add .x .x4 .x12 .x2, .addImm .x .x6 .x12 1, .logic .and .x .x6 .x6 .x9, .movz .x .x7 15 0,
      .logic .and .x .x5 .x6 .x7, .sub .x .x8 .x6 .x5] : List Instr))) s fun t =>
      let c := contextAt s.mem (s.gpr .x0)
      t.gpr .x13 = c.j.setWidth 64 ∧ t.gpr .x9 = 255#64 ∧
      t.gpr .x4 = c.i.setWidth 64 + s.gpr .x2 ∧
      t.gpr .x5 = BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.sk0 c.i) ∧ t.gpr .x8 = BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.base0 c.i) ∧
      t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ p ∈ saved true, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ g, g ∉ VG.Proof.Rc4.AArch64.setupRegs → t.gpr g = s.gpr g) := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  have hc (x : BitVec 8) : (x.setWidth 32).setWidth 64 = x.setWidth 64 :=
    BitVec.setWidth_setWidth (by decide)
  unfold save saved
  have hi1 : VG.Proof.Rc4.AArch64.i1 (s.mem (s.gpr .x0 + 256#64)) < 256 := by simp only [VG.Proof.Rc4.AArch64.i1]; omega
  rrun [List.cons_append, List.nil_append, List.map_cons, List.map_nil, h256, h257, VG.Proof.Rc4.AArch64.read_byte', hc,
    VG.Proof.Rc4.AArch64.incr_byte, VG.Proof.Rc4.AArch64.low4 _ hi1]
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]; rfl
  · simp [State.write]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [negBase]
  · intro g hg
    simp only [VG.Proof.Rc4.AArch64.setupRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hg
    obtain ⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hg
    simp [h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]

theorem low_sub (j : BitVec 8) (B : Nat) :
    (j.setWidth 64 - BitVec.ofNat 64 B).setWidth 8 = j - VG.Proof.Rc4.AArch64.bB B := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := j.isLt
  omega

theorem low_neg (B : Nat) : (255#64 - BitVec.ofNat 64 B + 1#64).setWidth 8 = 0 - VG.Proof.Rc4.AArch64.bB B := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
    show (255#64).toNat = 255 from rfl, show (1#64).toNat = 1 from rfl,
    show (0 : BitVec 8).toNat = 0 from rfl]
  omega

theorem low_nat (n : Nat) : (BitVec.ofNat 64 n).setWidth 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem tbl_bc (x : BitVec 128) {k : Nat} (hk : k < 16) :
    (ofVBytes fun i => if (vbyte (VG.Proof.Rc4.AArch64.bc (BitVec.ofNat 8 k)) i).toNat < 16 then
      vbyte x (vbyte (VG.Proof.Rc4.AArch64.bc (BitVec.ofNat 8 k)) i).toNat else 0#8) = VG.Proof.Rc4.AArch64.bc (vbyte x k) :=
  VG.Proof.Rc4.AArch64.vbyte_ext fun e he => by
    rw [vbyte_ofVBytes _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he, VG.Proof.Rc4.AArch64.vbyte_bc _ he, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), ite_eq_left hk]

theorem setupD_ok {s : State} {j : BitVec 8} {B sk : Nat} (hsk : sk < 16)
    (h13 : s.gpr .x13 = j.setWidth 64) (h8 : s.gpr .x8 = BitVec.ofNat 64 B)
    (h9 : s.gpr .x9 = 255#64) (h5 : s.gpr .x5 = BitVec.ofNat 64 sk) :
    WP isa (.block [.sub .x .x6 .x13 .x8, .vop (.dup .b16 (dq 0) .x6), .sub .x .x6 .x9 .x8,
      .addImm .x .x6 .x6 1, .vop (.dup .b16 negBase .x6), .vop (.dup .b16 .v7 .x5),
      .vop (.tbl si (treg 0) .v7)]) s fun t =>
      t.v (dq 0) = VG.Proof.Rc4.AArch64.bc (j - VG.Proof.Rc4.AArch64.bB B) ∧ t.v negBase = VG.Proof.Rc4.AArch64.bc (0 - VG.Proof.Rc4.AArch64.bB B) ∧
      t.v si = VG.Proof.Rc4.AArch64.bc (vbyte (s.v (treg 0)) sk) ∧
      (∀ v, v ≠ dq 0 → v ≠ negBase → v ≠ .v7 → v ≠ si → t.v v = s.v v) ∧
      (∀ g, g ≠ .x6 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have d0 : dq 0 = .v0 := rfl
  have nb : negBase = .v14 := rfl
  have t0 : treg 0 = .v16 := rfl
  have s4 : si = .v4 := rfl
  rrun [d0, nb, t0, s4, h13, h8, h9, h5, VG.Proof.Rc4.AArch64.bc_lit, VG.Proof.Rc4.AArch64.low_sub, VG.Proof.Rc4.AArch64.low_neg, VG.Proof.Rc4.AArch64.low_nat, VG.Proof.Rc4.AArch64.tbl_bc _ hsk]
  refine ⟨fun v a b c d => ?_, fun g hg => ?_, ?_⟩
  · simp [a, b, c, d]
  · simp [hg]
  · simp [State.setV, State.write]

theorem i1_eq (i : BitVec 8) : BitVec.ofNat 8 (VG.Proof.Rc4.AArch64.base0 i + VG.Proof.Rc4.AArch64.sk0 i) = i + 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [VG.Proof.Rc4.AArch64.base0, VG.Proof.Rc4.AArch64.sk0, VG.Proof.Rc4.AArch64.i1, BitVec.toNat_ofNat, BitVec.toNat_add, show (1 : BitVec 8).toNat = 1 from rfl]
  omega

theorem base0_mod (i : BitVec 8) : VG.Proof.Rc4.AArch64.base0 i % 16 = 0 := by simp only [VG.Proof.Rc4.AArch64.base0, VG.Proof.Rc4.AArch64.sk0]; omega

theorem sk0_lt (i : BitVec 8) : VG.Proof.Rc4.AArch64.sk0 i < 16 := by simp only [VG.Proof.Rc4.AArch64.sk0]; omega

/-- The loop's globals for the call from `s`, entering the loop in `t`. -/
def glob (s t : State) : VG.Proof.Rc4.AArch64.Glob :=
  ⟨contextAt s.mem (s.gpr .x0), s.gpr .x1, (s.gpr .x2).toNat, s.mem, t⟩

theorem saved_ne : ∀ p ∈ saved true, p.2 ≠ .x6 ∧ p.2 ≠ .x7 := by decide

theorem applySetup_ok {s : State} (hp : InRegions s.wr (s.gpr .x0) 258) :
    WP isa (.block (applyLoad ++ applySetup)) s fun t =>
      let c := contextAt s.mem (s.gpr .x0)
      VG.Proof.Rc4.AArch64.LaneInv (VG.Proof.Rc4.AArch64.glob s t) (VG.Proof.Rc4.AArch64.base0 c.i) 0 (VG.Proof.Rc4.AArch64.sk0 c.i) 0 t ∧
      t.gpr .x4 = c.i.setWidth 64 + s.gpr .x2 ∧ t.gpr .x9 = 255#64 ∧
      (∀ p ∈ saved true, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ g, g ∉ VG.Proof.Rc4.AArch64.setupRegs → t.gpr g = s.gpr g) ∧ t.v .v15 = s.v .v15 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hpr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 258 :=
    let ⟨r, h1, h2⟩ := hp; ⟨r, List.mem_append_right _ h1, h2⟩
  have h256 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 256 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      region_offset _ _ _ 0 256 (by decide) (by decide) hpr
  unfold applyLoad applySetup
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.AArch64.setupA_ok hpr) fun a ⟨a13, a9, a4, a5, a8, av, am, ard, awr, asp, asv, ag⟩ => ?_
  rw [List.append_assoc, WP.block_append_iff, VG.Proof.Rc4.AArch64.loadTable_eq]
  have hpa : InRegions (a.rd ++ a.wr) (a.gpr .x0) 256 := by
    rw [ard, awr, ag .x0 (by decide)]; exact h256
  refine WP.mono (VG.Proof.Rc4.AArch64.loadN_ok (VG.Proof.Rc4.AArch64.base0_mod _) a8 a9 hpa (Nat.le_refl 16))
    fun b ⟨brow, bv, bg, bm, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.AArch64.constants_ok b) fun e ⟨ec, ev, eg, em, erd, ewr, esp⟩ => ?_
  have e13 : e.gpr .x13 = (contextAt s.mem (s.gpr .x0)).j.setWidth 64 := by
    rw [eg _ (by decide) (by decide), bg _ (by decide) (by decide), a13]
  have e8 : e.gpr .x8 = BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.base0 (contextAt s.mem (s.gpr .x0)).i) := by
    rw [eg _ (by decide) (by decide), bg _ (by decide) (by decide), a8]
  have e9 : e.gpr .x9 = 255#64 := by
    rw [eg _ (by decide) (by decide), bg _ (by decide) (by decide), a9]
  have e5 : e.gpr .x5 = BitVec.ofNat 64 (VG.Proof.Rc4.AArch64.sk0 (contextAt s.mem (s.gpr .x0)).i) := by
    rw [eg _ (by decide) (by decide), bg _ (by decide) (by decide), a5]
  refine WP.mono (VG.Proof.Rc4.AArch64.setupD_ok (VG.Proof.Rc4.AArch64.sk0_lt _) e13 e8 e9 e5)
    fun t ⟨tj, tnb, tsi, tv, tg, tm, trd, twr, tsp⟩ => ?_
  have gk : ∀ g, g ∉ VG.Proof.Rc4.AArch64.setupRegs → t.gpr g = s.gpr g := fun g hg => by
    have h6 : g ≠ .x6 := fun h => hg (h ▸ by decide)
    have h7 : g ≠ .x7 := fun h => hg (h ▸ by decide)
    rw [tg g h6, eg g h6 h7, bg g h6 h7, ag g hg]
  have hsk := VG.Proof.Rc4.AArch64.sk0_lt (contextAt s.mem (s.gpr .x0)).i
  have hd : VG.Proof.Rc4.AArch64.doneAt (VG.Proof.Rc4.AArch64.glob s t) 0 (VG.Proof.Rc4.AArch64.sk0 (contextAt s.mem (s.gpr .x0)).i) 0 = 0 := by
    simp only [VG.Proof.Rc4.AArch64.doneAt]; omega
  refine ⟨LaneInv.mk ?_ ?_ ?_ ?_ ?_ ⟨fun _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩ fun _ _ _ => rfl, ?_, ?_,
    fun p hp => ?_, gk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd]
    refine ⟨VG.Proof.Rc4.AArch64.rows_table (m := s.mem) (p := s.gpr .x0) (VG.Proof.Rc4.AArch64.base0_mod _) fun r hr => ?_, tj, tnb,
      ec.congr fun r hr => tv r ?_ ?_ ?_ ?_⟩
    · have ht := VG.Proof.Rc4.AArch64.treg_ne r hr
      rw [tv _ ht.1 (by revert r; decide) (by revert r; decide) (by revert r; decide),
        ev _ (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide) (by revert r; decide) (by revert r; decide),
        brow r hr, am, ag .x0 (by decide)]
    all_goals rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hd]
    refine ⟨Nat.zero_le _, ?_, ?_, fun k _ => ?_, ?_⟩
    · rw [gk .x1 (by decide)]; simp [VG.Proof.Rc4.AArch64.glob]
    · rw [gk .x2 (by decide)]; simp [VG.Proof.Rc4.AArch64.glob]
    · simp only [Nat.not_lt_zero, ite_false, VG.Proof.Rc4.AArch64.glob]; rw [tm, em, bm, am]
    · rw [tm, em, bm, am]; exact Frame.refl _ _
  · rw [tg _ (by decide), eg _ (by decide) (by decide), bg _ (by decide) (by decide), a5,
      Nat.sub_zero]
  · rw [tg _ (by decide), e8]
  · intro _
    refine ⟨?_, ?_⟩
    · rw [hd, Nat.zero_max]; exact (VG.Proof.Rc4.AArch64.i1_eq _).symm
    · rw [Nat.zero_max, tsi, VG.Proof.Rc4.AArch64.tbyte, Nat.div_eq_of_lt hsk,
        Nat.mod_eq_of_lt hsk, tv (treg 0) (by decide) (by decide) (by decide) (by decide)]
  · rw [tg _ (by decide), eg _ (by decide) (by decide), bg _ (by decide) (by decide), a4]
  · rw [tg _ (by decide), e9]
  · obtain ⟨h6, h7⟩ := VG.Proof.Rc4.AArch64.saved_ne p hp
    rw [tg _ h6, eg _ h6 h7, bg _ h6 h7, asv p hp]
  · rw [tv _ (by decide) (by decide) (by decide) (by decide),
      ev _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      bv _ (by decide), av]
  · rw [tm, em, bm, am]
  · rw [trd, erd, brd, ard]
  · rw [twr, ewr, bwr, awr]
  · rw [tsp, esp, bsp, asp]

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.ApplyFinish`. -/
section

/-!
# The PRGA's finish

`finish_ok`: the table is stored back from its registers at base `B`, then
`i` and `j = (j - B) + B`, and the callee-saved vector registers are
restored.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem far_row {y p : Addr} {o : Nat} (ho : o + 16 ≤ 256) (h : ¬ (y - p).toNat < 258) :
    ¬ (y - (p + BitVec.ofNat 64 o)).toNat < 16 := by
  rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
  have := (y - p).isLt
  rw [show 2 ^ 64 - o + (y - p).toNat = ((y - p).toNat - o) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem j_byte (K : BitVec 8) (B : Nat) :
    (((VG.Proof.Rc4.AArch64.bc K).extractLsb' 0 32).setWidth 64 + BitVec.ofNat 64 B).setWidth 8 = K + VG.Proof.Rc4.AArch64.bB B := by
  have hl := congrArg BitVec.toNat (VG.Proof.Rc4.AArch64.low_byte K)
  have hx := ((VG.Proof.Rc4.AArch64.bc K).extractLsb' 0 32).isLt
  simp only [BitVec.toNat_setWidth] at hl
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem low_setLane (v : BitVec 128) (a : BitVec 64) : (setLane v 64 0 a).extractLsb' 0 64 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [setLane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  simp (disch := omega) [hi, decide_eq_true]

theorem i_byte (x : BitVec 64) : (x.setWidth 32).setWidth 8 = x.setWidth 8 :=
  BitVec.setWidth_setWidth (by decide)

/-- `i` and `j = (j - B) + B`. -/
theorem indices_ok {a : State} {B : Nat} {J : BitVec 8} (h8 : a.gpr .x8 = BitVec.ofNat 64 B)
    (hp : InRegions a.wr (a.gpr .x0) 258) (hj : a.v (dq 0) = VG.Proof.Rc4.AArch64.bc (J - VG.Proof.Rc4.AArch64.bB B)) :
    WP isa (.block [.strb .x4 .x0 256, .umov .w .x6 (dq 0) 0, .add .x .x6 .x6 .x8,
      .strb .x6 .x0 257]) a fun b =>
      b.mem = (a.mem.write (a.gpr .x0 + 256#64) 1 ((a.gpr .x4).setWidth 8)).write
        (a.gpr .x0 + 257#64) 1 J ∧
      b.v = a.v ∧ (∀ g, g ≠ .x6 → b.gpr g = a.gpr g) ∧ b.rd = a.rd ∧ b.wr = a.wr ∧ b.sp = a.sp := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [State.store, h256, h257, hj, h8, VG.Proof.Rc4.AArch64.i_byte, VG.Proof.Rc4.AArch64.j_byte, BitVec.sub_add_cancel]
  refine ⟨fun g hg => ?_, ?_⟩
  · simp [hg]
  · simp [State.write]

theorem restore_ok (prga : Bool) (s : State) :
    WP isa (.block (restore prga)) s fun t =>
      (∀ p ∈ saved prga, (t.v p.1).extractLsb' 0 64 = s.gpr p.2) ∧
      (∀ v, (∀ p ∈ saved prga, p.1 ≠ v) → t.v v = s.v v) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  cases prga <;>
  · unfold restore saved
    rrun [List.cons_append, List.nil_append, List.map_cons, List.map_nil]
    refine ⟨fun p hp => ?_, fun v hv => ?_, by simp [State.setV]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [negBase, VG.Proof.Rc4.AArch64.low_setLane]
    · simp only [List.forall_mem_cons] at hv
      try simp only [negBase] at hv ⊢
      simp only [show ∀ a : VReg, (v = a) = (a = v) from fun a => propext eq_comm]
      simp [hv]

theorem finish_ok {u : State} {B : Nat} {T : Table} {I J : BitVec 8} (hB : B % 16 = 0)
    (h8 : u.gpr .x8 = BitVec.ofNat 64 B) (h9 : u.gpr .x9 = 255#64)
    (hp : InRegions u.wr (u.gpr .x0) 258) (hT : VG.Proof.Rc4.AArch64.TableIn u B T)
    (hj : u.v (dq 0) = VG.Proof.Rc4.AArch64.bc (J - VG.Proof.Rc4.AArch64.bB B)) (h4 : (u.gpr .x4).setWidth 8 = I) :
    WP isa (.block applyFinish) u fun t =>
      contextAt t.mem (u.gpr .x0) = ⟨T, I, J⟩ ∧
      (∀ y, ¬ (y - u.gpr .x0).toNat < 258 → t.mem y = u.mem y) ∧
      (∀ p ∈ saved true, (t.v p.1).extractLsb' 0 64 = u.gpr p.2) ∧ t.v .v15 = u.v .v15 ∧
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp := by
  have h256w : InRegions u.wr (u.gpr .x0) 256 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      region_offset _ _ _ 0 256 (by decide) (by decide) hp
  unfold applyFinish
  rw [List.append_assoc, WP.block_append_iff, VG.Proof.Rc4.AArch64.storeTable_eq]
  refine WP.mono (VG.Proof.Rc4.AArch64.storeN_ok hB h8 h9 h256w (Nat.le_refl 16))
    fun a ⟨arow, aout, av, ag, ard, awr, asp⟩ => ?_
  have a0 : a.gpr .x0 = u.gpr .x0 := ag _ (by decide) (by decide)
  have a4 : a.gpr .x4 = u.gpr .x4 := ag _ (by decide) (by decide)
  have a8 : a.gpr .x8 = u.gpr .x8 := ag _ (by decide) (by decide)
  rw [WP.block_append_iff]
  have hpa : InRegions a.wr (a.gpr .x0) 258 := by rw [awr, a0]; exact hp
  refine WP.mono (VG.Proof.Rc4.AArch64.indices_ok (J := J) (a8.trans h8) hpa (by rw [av]; exact hj))
    fun b ⟨bm, bv, bg, brd, bwr, bsp⟩ => ?_
  refine WP.mono (VG.Proof.Rc4.AArch64.restore_ok true b) fun t ⟨tsv, tv, _, tm, trd, twr, tsp⟩ => ?_
  refine ⟨?_, fun y hy => ?_, fun p hp => ?_, ?_, ?_, ?_, ?_⟩
  · rw [tm, bm, a0, a4, h4, context_finish, VG.Proof.Rc4.AArch64.stored_table hB hT arow]
  · have hne (d : Nat) (hd : d < 258) : y ≠ u.gpr .x0 + BitVec.ofNat 64 d := fun e => by
      rw [e, Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at hy; omega
    rw [tm, bm, a0, write_byte, ite_eq_right (hne 257 (by decide)), write_byte,
      ite_eq_right (hne 256 (by decide))]
    exact aout y fun r _ => VG.Proof.Rc4.AArch64.far_row (VG.Proof.Rc4.AArch64.rowOff_le r hB) hy
  · obtain ⟨h6, h7⟩ := VG.Proof.Rc4.AArch64.saved_ne p hp
    rw [tsv p hp, bg _ h6, ag _ h6 h7]
  · rw [tv _ (by decide), bv, av]
  · rw [trd, brd, ard]
  · rw [twr, bwr, awr]
  · rw [tsp, bsp, asp]

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Apply`. -/
section

/-!
# The PRGA

`apply_ok`: `vg_rc4_apply` XORs the next `len` keystream bytes into the
data and leaves the context `len` steps on, preserving the low halves of
`v8`–`v15`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem stepN_i (c : Context) (n : Nat) : (stepN c n).i = c.i + BitVec.ofNat 8 n := by
  induction n with
  | zero => exact (BitVec.add_zero _).symm
  | succ n ih =>
    show (stepN c n).i + 1 = _
    rw [ih, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 8).toNat = 1 from rfl]
    omega

theorem final_i (i : BitVec 8) (x : BitVec 64) :
    (i.setWidth 64 + x).setWidth 8 = i + BitVec.ofNat 8 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := i.isLt
  omega

theorem saved_kept : ∀ p ∈ saved true, p.2 ≠ .x1 ∧ p.2 ≠ .x2 ∧ p.2 ≠ .x5 ∧ p.2 ≠ .x6 ∧
    p.2 ≠ .x7 ∧ p.2 ≠ .x8 := by decide

theorem saved_v : ∀ r ∈ VG.AArch64.preservedV, r = .v15 ∨ ∃ p ∈ saved true, p.1 = r := by decide

theorem apply_ok (s : State)
    (hp : InRegions s.wr (s.gpr .x0) 258)
    (hd : (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region) ∈ s.wr)
    (hs : Mem.Sep (s.gpr .x0) 258 (s.gpr .x1) (s.gpr .x2).toNat) :
    WP isa VG.Impl.Rc4.AArch64.apply s fun t =>
      let result := update (contextAt s.mem (s.gpr .x0)) (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
      (contextAt t.mem (s.gpr .x0) = result.1 ∧
        bytesAt t.mem (s.gpr .x1) (s.gpr .x2).toNat = result.2) ∧
      ∀ r ∈ VG.AArch64.preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  unfold VG.Impl.Rc4.AArch64.apply applyRest
  have hN := (s.gpr .x2).isLt
  have x2 : s.gpr .x2 = BitVec.ofNat 64 (s.gpr .x2).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  apply WP.ite _ (VG.Proof.Rc4.AArch64.eval_zero' s .x2 x2 hN)
  · intro hz
    have h0 : (s.gpr .x2).toNat = 0 := by simpa using hz
    refine WP.block_nil ⟨?_, fun _ _ => rfl⟩
    rw [h0]
    exact ⟨rfl, rfl⟩
  intro hnz
  have hpos : 0 < (s.gpr .x2).toNat := by simp at hnz; omega
  refine WP.seq (WP.mono (WP.block_append_iff.mp (VG.Proof.Rc4.AArch64.applySetup_ok hp)) fun _ h => WP.seq (WP.mono h
    fun t ⟨hl, t4, t9, tsv, tg, t15, tm, trd, twr, tsp⟩ => ?_))
  let g := VG.Proof.Rc4.AArch64.glob s t
  have hg : VG.Proof.Rc4.AArch64.DataOk g := ⟨by show _ ∈ t.wr; rw [twr]; exact hd, hN⟩
  refine WP.seq (WP.mono (VG.Proof.Rc4.AArch64.loop_ok g hg _ ⟨_, 0, _, VG.Proof.Rc4.AArch64.base0_mod _, rfl, hpos,
    by have := VG.Proof.Rc4.AArch64.sk0_lt (contextAt s.mem (s.gpr .x0)).i; omega, hl⟩) fun u ⟨B, sk, hB, hu⟩ => ?_)
  have hdN : VG.Proof.Rc4.AArch64.doneAt g g.N sk 0 = g.N := by simp only [VG.Proof.Rc4.AArch64.doneAt]; omega
  have hpr := hu.prga
  have hdat := hu.data
  rw [hdN] at hpr hdat
  have u0 : u.gpr .x0 = s.gpr .x0 := by
    rw [hu.kept.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact tg _ (by decide)
  have hpu : InRegions u.wr (u.gpr .x0) 258 := by rw [hu.kept.wr, u0]; show InRegions t.wr _ _; rw [twr]; exact hp
  have u9 : u.gpr .x9 = 255#64 := by
    rw [hu.kept.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact t9
  have u4 : (u.gpr .x4).setWidth 8 = (stepN g.c₀ g.N).i := by
    rw [hu.kept.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    show (t.gpr .x4).setWidth 8 = _
    rw [t4, VG.Proof.Rc4.AArch64.final_i, VG.Proof.Rc4.AArch64.stepN_i]; rfl
  refine WP.mono (VG.Proof.Rc4.AArch64.finish_ok hB hu.x8 u9 hpu hpr.table hpr.j u4)
    fun w ⟨wc, wm, wsv, w15, _, _, _⟩ => ?_
  refine ⟨⟨?_, ?_⟩, fun r hr => ?_⟩
  · have wc' : contextAt w.mem (s.gpr .x0) = ⟨(stepN g.c₀ g.N).table, (stepN g.c₀ g.N).i,
        (stepN g.c₀ g.N).j⟩ := by rw [← u0]; exact wc
    rw [wc', update_fst, bytes_length]; rfl
  · refine update_bytes _ _ _ _ _ fun k hk => ?_
    have hsep : ¬ (s.gpr .x1 + BitVec.ofNat 64 k - u.gpr .x0).toNat < 258 := fun h => by
      rw [u0] at h
      refine hs _ h ?_
      rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact hk
    have hb : u.mem (g.D + BitVec.ofNat 64 k) = g.M₀ (g.D + BitVec.ofNat 64 k) ^^^ ks g.c₀ k :=
      (hdat.bytes k hk).trans (ite_eq_left hk)
    rw [wm _ hsep]; exact hb
  · rcases VG.Proof.Rc4.AArch64.saved_v r hr with rfl | ⟨p, hp, rfl⟩
    · rw [w15, hu.vkept _ (by decide) (by decide)]; exact congrArg _ t15
    · obtain ⟨a1, a2, a5, a6, a7, a8⟩ := VG.Proof.Rc4.AArch64.saved_kept p hp
      rw [wsv p hp, hu.kept.gpr _ a1 a2 a5 a6 a7 a8]
      exact tsv p hp

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Lit`. -/
section

/-! Literal code keeps the unrolled groups cheap for kernel-evaluated audits. -/
namespace VG.Impl.Rc4.AArch64
materialize_code applyRest
materialize_code apply
materialize_code VG.Impl.Rc4.AArch64.init
end VG.Impl.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.ApplyCT`. -/
section

/-!
# The PRGA's constant time

Only the pointers, the length and `i` reach the trace: `applyLoad` computes
from `i` the final `i`, the lanes to skip and the base `B`, which agree in
two runs that agree on `i`, and the rest is checked by taint from those.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4

structure EntryAgree (a b : State) : Prop where
  sp : a.sp = b.sp
  p : a.gpr .x0 = b.gpr .x0
  data : a.gpr .x1 = b.gpr .x1
  len : a.gpr .x2 = b.gpr .x2
  i : (contextAt a.mem (a.gpr .x0)).i = (contextAt b.mem (b.gpr .x0)).i

def ReadValid (s : State) : Prop := InRegions (s.rd ++ s.wr) (s.gpr .x0) 258

/-- The registers the rest of the PRGA needs public. -/
def restPublic : List Reg := [.x0, .x1, .x2, .x4, .x5, .x8, .x9]

theorem applyLoad_ct : RelCT isa (fun a b => VG.Proof.Rc4.AArch64.ReadValid a ∧ VG.Proof.Rc4.AArch64.ReadValid b ∧ VG.Proof.Rc4.AArch64.EntryAgree a b)
    (.block applyLoad) (VG.AArch64.Taint.Agree (Taint.ofRegs VG.Proof.Rc4.AArch64.restPublic)) := by
  intro a b tr tr' a' b' ⟨hpa, hpb, hab⟩ ea eb
  have hct : ConstantTime isa (fun _ => True)
      (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0])) (.block applyLoad) := by
    exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
      (fun _ _ _ _ h => h) (by taint_decide)
  have hagree : VG.AArch64.Taint.Agree (Taint.ofRegs [.x0]) a b := by
    refine ⟨hab.sp, fun r hr => ?_⟩
    have he : r = .x0 := by simpa only [VG.AArch64.Taint.mem_ofRegs, List.mem_singleton] using hr
    subst r
    exact hab.p
  have htrace := hct a b tr tr' a' b' trivial trivial hagree ea eb
  obtain ⟨_, u, eu, hau⟩ := VG.Proof.Rc4.AArch64.setupA_ok hpa
  obtain ⟨_, rfl⟩ := Exec.det eu ea
  obtain ⟨_, v, ev, hbv⟩ := VG.Proof.Rc4.AArch64.setupA_ok hpb
  obtain ⟨_, rfl⟩ := Exec.det ev eb
  obtain ⟨_, a9, a4, a5, a8, -, -, -, -, -, -, ag⟩ := hau
  obtain ⟨_, b9, b4, b5, b8, -, -, -, -, -, -, bg⟩ := hbv
  refine ⟨htrace, (Exec.sp ea).trans (hab.sp.trans (Exec.sp eb).symm), fun r hr => ?_⟩
  simp only [VG.Proof.Rc4.AArch64.restPublic, VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ag _ (by decide), bg _ (by decide), hab.p]
  · rw [ag _ (by decide), bg _ (by decide), hab.data]
  · rw [ag _ (by decide), bg _ (by decide), hab.len]
  · rw [a4, b4, hab.i, hab.len]
  · rw [a5, b5, hab.i]
  · rw [a8, b8, hab.i]
  · rw [a9, b9]

theorem apply_ct : ConstantTime isa VG.Proof.Rc4.AArch64.ReadValid VG.Proof.Rc4.AArch64.EntryAgree VG.Impl.Rc4.AArch64.apply := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold VG.Impl.Rc4.AArch64.apply
  refine RelCT.ite ?_ ?_ ?_
  · intro a b ⟨_, _, hab⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hab.len]
  · refine RelCT.taint (A := taint) (Taint.ofRegs []) ?_ (by taint_decide)
    intro a b ⟨⟨_, _, hab⟩, _⟩
    exact ⟨hab.sp, fun r hr => by simp only [VG.AArch64.Taint.mem_ofRegs, List.not_mem_nil] at hr⟩
  · refine RelCT.seq (RelCT.mono VG.Proof.Rc4.AArch64.applyLoad_ct (fun _ _ h => h.1) (fun _ _ h => h)) ?_
    exact RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.Rc4.AArch64.restPublic) (fun _ _ h => h) (by taint_decide)

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.KsaStep`. -/
section

/-!
# The key schedule's lanes

`keyByte_ok`: the next key byte is added to `j`, and the key pointer `x7`
and the bytes left before the key repeats, `x5`, advance (wrapping).
`ksaSwap_ok`: then the swap step is the specification's scheduling round.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem mod_succ_wrap {n L : Nat} (h : n % L + 1 = L) : (n + 1) % L = 0 := by
  have := Nat.div_add_mod n L
  rw [show n + 1 = L * (n / L + 1) by rw [Nat.mul_add]; omega]
  exact Nat.mul_mod_right _ _

theorem mod_succ_lt {n L : Nat} (h : n % L + 1 < L) : (n + 1) % L = n % L + 1 := by
  have := Nat.div_add_mod n L
  rw [show n + 1 = (n % L + 1) + L * (n / L) by omega, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt h]

theorem low8 (x : BitVec 8) : ((x.setWidth 32).setWidth 64).setWidth 8 = x := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; omega

theorem keyLoad_ok {s : State} {K : Addr} {L n : Nat} {J : BitVec 8} (hL : 0 < L) (hL' : L < 2 ^ 64)
    (h7 : s.gpr .x7 = K + BitVec.ofNat 64 (n % L)) (h5 : s.gpr .x5 = BitVec.ofNat 64 (L - n % L))
    (hkey : InRegions (s.rd ++ s.wr) K L) (hj : s.v (dq 0) = VG.Proof.Rc4.AArch64.bc J) :
    WP isa (.block [.ldrb .x6 .x7 0, .vop (.dup .b16 .v6 .x6), .vop (.add .b16 (dq 0) (dq 0) .v6),
      .addImm .x .x7 .x7 1, .subImm .x .x5 .x5 1]) s fun t =>
      t.v (dq 0) = VG.Proof.Rc4.AArch64.bc (J + s.mem (K + BitVec.ofNat 64 (n % L))) ∧
      t.gpr .x7 = K + BitVec.ofNat 64 (n % L) + 1 ∧ t.gpr .x5 = BitVec.ofNat 64 (L - n % L - 1) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ dq 0 → v ≠ .v6 → t.v v = s.v v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hm : n % L < L := Nat.mod_lt _ hL
  have hb := region_offset _ _ _ (n % L) 1 (by omega) (by omega) hkey
  have hj' : s.v .v0 = VG.Proof.Rc4.AArch64.bc J := hj
  have h1 : BitVec.ofNat 64 (L - n % L) - 1#64 = BitVec.ofNat 64 (L - n % L - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)
  have d0 : dq 0 = .v0 := rfl
  rrun [d0, hb, VG.Proof.Rc4.AArch64.read_byte', hj', h7, h5, VG.Proof.Rc4.AArch64.low8, VG.Proof.Rc4.AArch64.bc_lit, VG.Proof.Rc4.AArch64.add_bc, h1]
  refine ⟨fun r a b c => ?_, fun v a b => ?_, ?_⟩
  · simp [a, b, c]
  · simp [a, b]
  · simp [State.write, State.setV]

theorem keyByte_ok {s : State} {K : Addr} {L n : Nat} {J : BitVec 8} (hL : 0 < L) (hL' : L < 2 ^ 64)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 L)
    (h7 : s.gpr .x7 = K + BitVec.ofNat 64 (n % L)) (h5 : s.gpr .x5 = BitVec.ofNat 64 (L - n % L))
    (hkey : InRegions (s.rd ++ s.wr) K L) (hj : s.v (dq 0) = VG.Proof.Rc4.AArch64.bc J) :
    WP isa keyByte s fun t =>
      t.v (dq 0) = VG.Proof.Rc4.AArch64.bc (J + s.mem (K + BitVec.ofNat 64 (n % L))) ∧
      t.gpr .x7 = K + BitVec.ofNat 64 ((n + 1) % L) ∧
      t.gpr .x5 = BitVec.ofNat 64 (L - (n + 1) % L) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      (∀ v, v ≠ dq 0 → v ≠ .v6 → t.v v = s.v v) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hm : n % L < L := Nat.mod_lt _ hL
  unfold keyByte
  refine WP.seq (WP.mono (VG.Proof.Rc4.AArch64.keyLoad_ok hL hL' h7 h5 hkey hj)
    fun a ⟨aj, a7, a5, ag, av, am, ard, awr, asp⟩ => ?_)
  apply WP.ite _ (VG.Proof.Rc4.AArch64.eval_zero' a .x5 a5 (by omega))
  · intro hz
    have hw : n % L + 1 = L := by simp at hz; omega
    have a0 : a.gpr .x0 = K := by rw [ag _ (by decide) (by decide) (by decide), h0]
    have a1 : a.gpr .x1 = BitVec.ofNat 64 L := by rw [ag _ (by decide) (by decide) (by decide), h1]
    rrun [a0, a1]
    refine ⟨aj, ?_, ?_, fun r r5 r6 r7 => ?_, av, am, ard, awr, ?_⟩
    · rw [VG.Proof.Rc4.AArch64.mod_succ_wrap hw]; simp
    · rw [VG.Proof.Rc4.AArch64.mod_succ_wrap hw, Nat.sub_zero]
    · simp only [r5, r7, ite_false]; exact ag r r5 r6 r7
    · simp only [State.write]; exact asp
  · intro hnz
    have hlt : n % L + 1 < L := by simp at hnz; omega
    refine WP.block_nil ⟨aj, ?_, ?_, ag, av, am, ard, awr, asp⟩
    · rw [a7, VG.Proof.Rc4.AArch64.mod_succ_lt hlt, Offset.add_ofNat_add_one]
    · rw [a5, VG.Proof.Rc4.AArch64.mod_succ_lt hlt, Nat.sub_add_eq]

theorem byte_rearr (a b c d : BitVec 8) : a + b - d + c = a + c + b - d := by bv_omega

/-- A scheduling round at lane `l` of the group whose base is `B`, once the
key byte is in `j`. -/
theorem ksaSwap_ok {l B n : Nat} (hl : l < 16) (hn : n = B + l) (hn' : n < 256) {key : List Byte}
    {s : State} (hk : VG.Proof.Rc4.AArch64.Consts s) (ht : VG.Proof.Rc4.AArch64.TableIn s B (schedulePrefix key n).1)
    (hj : s.v (dq 0) = VG.Proof.Rc4.AArch64.bc ((schedulePrefix key n).2 + key.getD (n % key.length) 0 - VG.Proof.Rc4.AArch64.bB B))
    (hsi : s.v si = VG.Proof.Rc4.AArch64.bc (VG.Proof.Rc4.AArch64.tbyte s.v l)) :
    ∃ s', runBlock isa (swapStep false l) s = some s' ∧
      VG.Proof.Rc4.AArch64.TableIn s' B (schedulePrefix key (n + 1)).1 ∧
      s'.v (dq 0) = VG.Proof.Rc4.AArch64.bc ((schedulePrefix key (n + 1)).2 - VG.Proof.Rc4.AArch64.bB B) ∧
      s'.v si = VG.Proof.Rc4.AArch64.bc (VG.Proof.Rc4.AArch64.tbyte s'.v (l + 1)) ∧ VG.Proof.Rc4.AArch64.Only VG.Proof.Rc4.AArch64.stepRegs s s' := by
  have hS := schedule_succ key n
  simp only [scheduleRound] at hS
  generalize schedulePrefix key n = st at ht hj hS
  obtain ⟨s₁, run₁, t₁, j₁, i₁, -, o₁⟩ :=
    VG.Proof.Rc4.AArch64.swapStep_run false hl hk hj hsi (NB := 0) fun h => absurd h (by decide)
  have hR : ∀ k < 256, VG.Proof.Rc4.AArch64.tbyte s.v k = st.1.getD (BitVec.ofNat 8 (B + k)).toNat 0 := ht
  have ha : VG.Proof.Rc4.AArch64.tbyte s.v l = st.1.getD n 0 := by
    rw [hR l (by omega), ← hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn']
  have hJ : st.2 + key.getD (n % key.length) 0 - VG.Proof.Rc4.AArch64.bB B + VG.Proof.Rc4.AArch64.tbyte s.v l =
      st.2 + st.1.getD n 0 + key.getD (n % key.length) 0 - VG.Proof.Rc4.AArch64.bB B := by rw [ha, VG.Proof.Rc4.AArch64.byte_rearr]
  rw [hJ] at t₁ j₁ i₁
  refine ⟨s₁, run₁, fun k hk => ?_, by rw [j₁, hS], ?_, o₁⟩
  · rw [hS, t₁ k hk, VG.Proof.Rc4.AArch64.swapR_eq st.1 (by omega) hR _ hk, hn]
  · rw [i₁, t₁ _ (by omega)]

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.KsaGroup`. -/
section

/-!
# The key schedule's groups

`ksaLane_ok`: a lane of the key schedule is a scheduling round;
`ksaGroup_ok`: sixteen lanes and the rotation take the group with base `B`
to the next, with base `B + 16`; `ksaLoop_ok`: sixteen groups take the
identity table to the key schedule, its registers back where they started.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- The key schedule's globals: the key at `K` of `L` bytes in the memory
`M`, and the state `s₀` that the setup leaves. -/
structure KGlob where
  K : Addr
  L : Nat
  M : Mem
  s₀ : State

def KGlob.key (g : VG.Proof.Rc4.AArch64.KGlob) : List Byte := bytesAt g.M g.K g.L

structure KGlob.Ok (g : VG.Proof.Rc4.AArch64.KGlob) : Prop where
  pos : 0 < g.L
  le : g.L ≤ 256
  x0 : g.s₀.gpr .x0 = g.K
  x1 : g.s₀.gpr .x1 = BitVec.ofNat 64 g.L
  key : InRegions (g.s₀.rd ++ g.s₀.wr) g.K g.L

/-- Lane `l` of the group whose base is `B`: `B + l` rounds done. -/
structure KsaInv (g : VG.Proof.Rc4.AArch64.KGlob) (B l : Nat) (s : State) : Prop where
  consts : VG.Proof.Rc4.AArch64.Consts s
  table : VG.Proof.Rc4.AArch64.TableIn s B (schedulePrefix g.key (B + l)).1
  j : s.v (dq 0) = VG.Proof.Rc4.AArch64.bc ((schedulePrefix g.key (B + l)).2 - VG.Proof.Rc4.AArch64.bB B)
  si : s.v si = VG.Proof.Rc4.AArch64.bc (VG.Proof.Rc4.AArch64.tbyte s.v l)
  x7 : s.gpr .x7 = g.K + BitVec.ofNat 64 ((B + l) % g.L)
  x5 : s.gpr .x5 = BitVec.ofNat 64 (g.L - (B + l) % g.L)
  x8 : s.gpr .x8 = BitVec.ofNat 64 B
  x4 : s.gpr .x4 = BitVec.ofNat 64 (16 - B / 16)
  gpr : ∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s.gpr r = g.s₀.gpr r
  vkept : ∀ r, r ∉ VG.Proof.Rc4.AArch64.stepRegs → s.v r = g.s₀.v r
  mem : s.mem = g.M
  rd : s.rd = g.s₀.rd
  wr : s.wr = g.s₀.wr
  sp : s.sp = g.s₀.sp

theorem sub_add_comm8 (x y z : BitVec 8) : x - y + z = x + z - y := by bv_omega

theorem ksaLane_ok {g : VG.Proof.Rc4.AArch64.KGlob} (hg : g.Ok) {B l : Nat} (hl : l < 16) (hB : B + l < 256) {s : State}
    (h : VG.Proof.Rc4.AArch64.KsaInv g B l s) :
    WP isa (.seq keyByte (.block (swapStep false l))) s (VG.Proof.Rc4.AArch64.KsaInv g B (l + 1)) := by
  have h0 : s.gpr .x0 = g.K := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), hg.x0]
  have h1 : s.gpr .x1 = BitVec.ofNat 64 g.L := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), hg.x1]
  have hkey : InRegions (s.rd ++ s.wr) g.K g.L := by rw [h.rd, h.wr]; exact hg.key
  refine WP.seq (WP.mono (VG.Proof.Rc4.AArch64.keyByte_ok hg.pos (by have := hg.le; omega) h0 h1 h.x7 h.x5 hkey h.j)
    fun a ⟨aj, a7, a5, ag, av, am, ard, awr, asp⟩ => ?_)
  have hkb : s.mem (g.K + BitVec.ofNat 64 ((B + l) % g.L)) =
      g.key.getD ((B + l) % g.key.length) 0 := by
    rw [KGlob.key, bytes_length, bytes_get _ _ _ _ (Nat.mod_lt _ hg.pos), h.mem]
  have aj' : a.v (dq 0) = VG.Proof.Rc4.AArch64.bc ((schedulePrefix g.key (B + l)).2 +
      g.key.getD ((B + l) % g.key.length) 0 - VG.Proof.Rc4.AArch64.bB B) := by rw [aj, hkb, VG.Proof.Rc4.AArch64.sub_add_comm8]
  have ka : VG.Proof.Rc4.AArch64.Consts a := h.consts.congr fun r hr => av r
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have tba : ∀ k < 256, VG.Proof.Rc4.AArch64.tbyte a.v k = VG.Proof.Rc4.AArch64.tbyte s.v k := fun k hk =>
    VG.Proof.Rc4.AArch64.tbyte_congr (fun q hq => av _ ((show VG.Proof.Rc4.AArch64.NotTable (dq 0) by decide) q hq)
      ((show VG.Proof.Rc4.AArch64.NotTable .v6 by decide) q hq)) hk
  have ta : VG.Proof.Rc4.AArch64.TableIn a B (schedulePrefix g.key (B + l)).1 := fun k hk => by
    rw [tba k hk]; exact h.table k hk
  have sia : a.v si = VG.Proof.Rc4.AArch64.bc (VG.Proof.Rc4.AArch64.tbyte a.v l) := by
    rw [av _ (by decide) (by decide), h.si, tba l (by omega)]
  obtain ⟨t, run, tt, tj, tsi, to⟩ := VG.Proof.Rc4.AArch64.ksaSwap_ok hl rfl hB ka ta aj' sia
  refine WP.of_runBlock ⟨t, run, ?_⟩
  have tg := to.gpr
  exact {
    consts := VG.Proof.Rc4.AArch64.consts_of_only ka to
    table := tt
    j := tj
    si := tsi
    x7 := by rw [tg, a7]; rfl
    x5 := by rw [tg, a5]; rfl
    x8 := by rw [tg, ag _ (by decide) (by decide) (by decide)]; exact h.x8
    x4 := by rw [tg, ag _ (by decide) (by decide) (by decide)]; exact h.x4
    gpr := fun r r4 r5 r6 r7 r8 => by rw [tg, ag r r5 r6 r7]; exact h.gpr r r4 r5 r6 r7 r8
    vkept := fun r hr => by
      rw [to.2 r hr, av r (fun e => hr (e ▸ by decide)) (fun e => hr (e ▸ by decide))]
      exact h.vkept r hr
    mem := by rw [to.mem, am]; exact h.mem
    rd := by rw [to.rd, ard]; exact h.rd
    wr := by rw [to.wr, awr]; exact h.wr
    sp := by rw [to.sp, asp]; exact h.sp }

theorem ksaLanes_ok {g : VG.Proof.Rc4.AArch64.KGlob} (hg : g.Ok) {B : Nat} (hB : B + 16 ≤ 256) {n : Nat} (hn : n ≤ 16)
    {s : State} (h : VG.Proof.Rc4.AArch64.KsaInv g B 0 s) : WP isa (scheduleLanes n) s (VG.Proof.Rc4.AArch64.KsaInv g B n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    exact WP.seq (WP.mono (ih (by omega)) fun t ht => VG.Proof.Rc4.AArch64.ksaLane_ok hg (by omega) (by omega) ht)

theorem subX4_ok (s : State) :
    WP isa (.block [.subImm .x .x4 .x4 1]) s fun t =>
      t.gpr .x4 = s.gpr .x4 - 1 ∧ (∀ r, r ≠ .x4 → t.gpr r = s.gpr r) ∧ t.v = s.v ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rrun
  refine ⟨fun r hr => by simp [hr], by simp [State.write]⟩

theorem ksaGroup_ok {g : VG.Proof.Rc4.AArch64.KGlob} (hg : g.Ok) {B : Nat} (hB16 : B % 16 = 0) (hB : B < 256) {s : State}
    (h : VG.Proof.Rc4.AArch64.KsaInv g B 0 s) : WP isa scheduleGroup s (VG.Proof.Rc4.AArch64.KsaInv g (B + 16) 0) := by
  apply WP.seq (WP.mono (VG.Proof.Rc4.AArch64.ksaLanes_ok hg (by omega) (Nat.le_refl 16) h) fun s₁ h₁ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.AArch64.rotate_ok false h₁.consts h₁.j (NB := 0) fun e => absurd e (by decide))
    fun t ⟨tab, j, nb, x8, gg, vv, m, rd, wr, sp⟩ => ?_
  refine WP.mono (VG.Proof.Rc4.AArch64.subX4_ok t) fun u ⟨u4, ug, uv, um, urd, uwr, usp⟩ => ?_
  have tbu : VG.Proof.Rc4.AArch64.tbyte u.v = VG.Proof.Rc4.AArch64.tbyte t.v := by rw [uv]
  exact {
    consts := h₁.consts.congr fun r hr => by
      rw [uv]; exact vv r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    table := fun k hk => by
      rw [tbu, tab k hk, h₁.table _ (by omega), VG.Proof.Rc4.AArch64.ofNat_wrap]
    j := by rw [uv, j, VG.Proof.Rc4.AArch64.byte_shift]
    si := by
      rw [uv, vv _ (by decide), h₁.si, tab 0 (by decide)]
    x7 := by
      rw [ug _ (by decide), gg _ (by decide), h₁.x7, show B + 16 + 0 = B + 16 from rfl]
    x5 := by rw [ug _ (by decide), gg _ (by decide), h₁.x5]
    x8 := by
      rw [ug _ (by decide), x8, h₁.x8, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
        BitVec.ofNat_add_ofNat]
    x4 := by
      rw [u4, gg _ (by decide), h₁.x4, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
      congr 1; omega
    gpr := fun r r4 r5 r6 r7 r8 => by rw [ug r r4, gg r r8]; exact h₁.gpr r r4 r5 r6 r7 r8
    vkept := fun r hr => by
      rw [uv]
      by_cases hn : r = negBase
      · subst hn; simp only [Bool.false_eq_true, ite_false] at nb; rw [nb]; exact h₁.vkept _ hr
      · rw [vv r (by
          simp only [VG.Proof.Rc4.AArch64.rotRegs, List.mem_cons, List.mem_map, List.mem_range, not_or, not_exists,
            not_and]
          exact ⟨fun e => hr (by rw [e]; decide), fun e => hr (by rw [e]; decide), hn,
            fun a ha e => hr (e ▸ VG.Proof.Rc4.AArch64.treg_step a ha)⟩)]
        exact h₁.vkept r hr
    mem := by rw [um, m]; exact h₁.mem
    rd := by rw [urd, rd]; exact h₁.rd
    wr := by rw [uwr, wr]; exact h₁.wr
    sp := by rw [usp, sp]; exact h₁.sp }

/-- A group about to start, `m` groups before the end. -/
def KLoopInv (g : VG.Proof.Rc4.AArch64.KGlob) (m : Nat) (s : State) : Prop :=
  ∃ B, m = 16 - B / 16 ∧ B % 16 = 0 ∧ B < 256 ∧ VG.Proof.Rc4.AArch64.KsaInv g B 0 s

theorem ksaLoop_ok {g : VG.Proof.Rc4.AArch64.KGlob} (hg : g.Ok) (m : Nat) {s : State} (h : VG.Proof.Rc4.AArch64.KLoopInv g m s) :
    WP isa (.loop scheduleGroup (.nonzero .x .x4)) s (VG.Proof.Rc4.AArch64.KsaInv g 256 0) := by
  refine WP.loop (M := isa) (VG.Proof.Rc4.AArch64.KLoopInv g) ?_ m s h
  intro m s ⟨B, hm, hB16, hB, h⟩
  refine WP.mono (VG.Proof.Rc4.AArch64.ksaGroup_ok hg hB16 hB h) fun t ht => ?_
  have flag := VG.Proof.Rc4.AArch64.eval_nonzero' t .x4 ht.x4 (by omega)
  by_cases hend : B + 16 = 256
  · left
    exact ⟨by rw [flag]; simp [hend], hend ▸ ht⟩
  · right
    exact ⟨by rw [flag]; simp; omega, 16 - (B + 16) / 16, by omega, B + 16, rfl, by omega,
      by omega, ht⟩

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.KsaSetup`. -/
section

/-!
# The key schedule's setup

`ksaSetup_ok`: the setup saves the callee-saved vector registers it uses,
leaves the constants, the identity table in `v16`–`v31` (lane numbers, and
their XORs with 64, 128 and 192), `j = 0`, `S[0] = 0`, the key pointer and
length, sixteen groups to go and the base `0`: the first group's `KsaInv`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem ident_xor : ∀ q < 4, VG.Proof.Rc4.AArch64.laneNums q ^^^ VG.Proof.Rc4.AArch64.bc 64#8 = VG.Proof.Rc4.AArch64.laneNums (q + 4) ∧
    VG.Proof.Rc4.AArch64.laneNums q ^^^ VG.Proof.Rc4.AArch64.bc 128#8 = VG.Proof.Rc4.AArch64.laneNums (q + 8) ∧ VG.Proof.Rc4.AArch64.laneNums (q + 4) ^^^ VG.Proof.Rc4.AArch64.bc 128#8 = VG.Proof.Rc4.AArch64.laneNums (q + 12) := by
  decide +kernel

/-- The identity table's code, written out. -/
def identCode : List Instr :=
  [.vop (.mov .v16 .v8), .vop (.mov .v17 .v9), .vop (.mov .v18 .v10), .vop (.mov .v19 .v11),
   eorV .v20 .v8 .v12, eorV .v21 .v9 .v12, eorV .v22 .v10 .v12, eorV .v23 .v11 .v12,
   eorV .v24 .v8 .v13, eorV .v25 .v9 .v13, eorV .v26 .v10 .v13, eorV .v27 .v11 .v13,
   eorV .v28 .v20 .v13, eorV .v29 .v21 .v13, eorV .v30 .v22 .v13, eorV .v31 .v23 .v13]

theorem identCode_eq :
    (List.range 4).map (fun r => .vop (.mov (treg r) (lanes r))) ++
    (List.range 4).map (fun r => eorV (treg (4 + r)) (lanes r) c64) ++
    (List.range 4).map (fun r => eorV (treg (8 + r)) (lanes r) c128) ++
    (List.range 4).map (fun r => eorV (treg (12 + r)) (treg (4 + r)) c128) = VG.Proof.Rc4.AArch64.identCode := by
  decide

theorem ident_ok {s : State} (hk : VG.Proof.Rc4.AArch64.Consts s) :
    WP isa (.block VG.Proof.Rc4.AArch64.identCode) s fun t =>
      (∀ q < 16, t.v (treg q) = VG.Proof.Rc4.AArch64.laneNums q) ∧ (∀ v, VG.Proof.Rc4.AArch64.NotTable v → t.v v = s.v v) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have l0 : s.v .v8 = VG.Proof.Rc4.AArch64.laneNums 0 := hk.lns 0 (by decide)
  have l1 : s.v .v9 = VG.Proof.Rc4.AArch64.laneNums 1 := hk.lns 1 (by decide)
  have l2 : s.v .v10 = VG.Proof.Rc4.AArch64.laneNums 2 := hk.lns 2 (by decide)
  have l3 : s.v .v11 = VG.Proof.Rc4.AArch64.laneNums 3 := hk.lns 3 (by decide)
  have k64 : s.v .v12 = VG.Proof.Rc4.AArch64.bc 64 := hk.c64
  have k128 : s.v .v13 = VG.Proof.Rc4.AArch64.bc 128 := hk.c128
  have x0 := VG.Proof.Rc4.AArch64.ident_xor 0 (by decide)
  have x1 := VG.Proof.Rc4.AArch64.ident_xor 1 (by decide)
  have x2 := VG.Proof.Rc4.AArch64.ident_xor 2 (by decide)
  have x3 := VG.Proof.Rc4.AArch64.ident_xor 3 (by decide)
  simp only [Nat.reduceAdd] at x0 x1 x2 x3
  unfold VG.Proof.Rc4.AArch64.identCode eorV
  rrun [l0, l1, l2, l3, k64, k128, x0.1, x0.2.1, x0.2.2, x1.1, x1.2.1, x1.2.2, x2.1, x2.2.1,
    x2.2.2, x3.1, x3.2.1, x3.2.2]
  refine ⟨fun q hq => ?_, fun v hv => ?_, ?_⟩
  · rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨
      q = 9 ∨ q = 10 ∨ q = 11 ∨ q = 12 ∨ q = 13 ∨ q = 14 ∨ q = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [treg]
  · have ne (a : Nat) (ha : a < 16) : v ≠ treg a := (hv a ha).symm
    have n0 : v ≠ .v16 := ne 0 (by decide)
    have n1 : v ≠ .v17 := ne 1 (by decide)
    have n2 : v ≠ .v18 := ne 2 (by decide)
    have n3 : v ≠ .v19 := ne 3 (by decide)
    have n4 : v ≠ .v20 := ne 4 (by decide)
    have n5 : v ≠ .v21 := ne 5 (by decide)
    have n6 : v ≠ .v22 := ne 6 (by decide)
    have n7 : v ≠ .v23 := ne 7 (by decide)
    have n8 : v ≠ .v24 := ne 8 (by decide)
    have n9 : v ≠ .v25 := ne 9 (by decide)
    have n10 : v ≠ .v26 := ne 10 (by decide)
    have n11 : v ≠ .v27 := ne 11 (by decide)
    have n12 : v ≠ .v28 := ne 12 (by decide)
    have n13 : v ≠ .v29 := ne 13 (by decide)
    have n14 : v ≠ .v30 := ne 14 (by decide)
    have n15 : v ≠ .v31 := ne 15 (by decide)
    simp [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15]
  · simp [State.setV]

theorem saveK_ok (s : State) :
    WP isa (.block (save false)) s fun t =>
      (∀ p ∈ saved false, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ g, g ≠ .x10 → g ≠ .x11 → g ≠ .x14 → g ≠ .x15 → g ≠ .x16 → g ≠ .x17 → t.gpr g = s.gpr g) ∧
      t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold save saved
  rrun [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.append_nil]
  refine ⟨fun p hp => ?_, fun g a b c d e f => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp [a, b, c, d, e, f]
  · simp [State.write]

/-- The registers the key schedule's setup writes. -/
def ksaRegs : List Reg := [.x4, .x5, .x6, .x7, .x8, .x10, .x11, .x14, .x15, .x16, .x17]

/-- The key schedule's globals for the call from `s`, entering the loop in `t`. -/
def kglob (s t : State) : VG.Proof.Rc4.AArch64.KGlob := ⟨s.gpr .x0, (s.gpr .x1).toNat, s.mem, t⟩

theorem ident_get {k : Nat} (hk : k < 256) :
    (Vector.ofFn fun i : Fin 256 => BitVec.ofNat 8 i.val).getD (BitVec.ofNat 8 (0 + k)).toNat 0 =
      BitVec.ofNat 8 k := by
  rw [Nat.zero_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  simp [Vector.getD, hk]
  apply BitVec.eq_of_toNat_eq
  show k = k % 2 ^ 8
  omega

theorem scheduleSetup_eq : scheduleSetup = save false ++ (constants ++ (VG.Proof.Rc4.AArch64.identCode ++
    ([.vop (.movi0 (dq 0)), .vop (.movi0 si), .addImm .x .x7 .x0 0, .addImm .x .x5 .x1 0,
      .movz .x .x4 16 0, .movz .x .x8 0 0] : List Instr))) := by
  rw [← VG.Proof.Rc4.AArch64.identCode_eq]; simp only [scheduleSetup, List.append_assoc]

theorem tailK_ok (c : State) :
    WP isa (.block ([.vop (.movi0 (dq 0)), .vop (.movi0 si), .addImm .x .x7 .x0 0,
      .addImm .x .x5 .x1 0, .movz .x .x4 16 0, .movz .x .x8 0 0] : List Instr)) c fun t =>
      t.v (dq 0) = 0 ∧ t.v si = 0 ∧ (∀ v, v ≠ .v0 → v ≠ .v4 → t.v v = c.v v) ∧
      t.gpr .x7 = c.gpr .x0 ∧ t.gpr .x5 = c.gpr .x1 ∧ t.gpr .x4 = 16#64 ∧ t.gpr .x8 = 0#64 ∧
      (∀ r, r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x8 → t.gpr r = c.gpr r) ∧
      t.mem = c.mem ∧ t.rd = c.rd ∧ t.wr = c.wr ∧ t.sp = c.sp := by
  have d0 : dq 0 = .v0 := rfl
  have s4 : si = .v4 := rfl
  rrun [d0, s4]
  refine ⟨fun v a b => by simp [a, b], fun r a b c d => by simp [a, b, c, d], ?_⟩
  simp [State.write, State.setV]

theorem ksaSetup_ok {s : State} (hL : 0 < (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat) :
    WP isa (.block scheduleSetup) s fun t =>
      (VG.Proof.Rc4.AArch64.kglob s t).Ok ∧ VG.Proof.Rc4.AArch64.KsaInv (VG.Proof.Rc4.AArch64.kglob s t) 0 0 t ∧
      (∀ p ∈ saved false, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ r, r ∉ VG.Proof.Rc4.AArch64.ksaRegs → t.gpr r = s.gpr r) ∧ t.v .v14 = s.v .v14 ∧ t.v .v15 = s.v .v15 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  rw [VG.Proof.Rc4.AArch64.scheduleSetup_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.AArch64.saveK_ok s) fun a ⟨asv, ag, av, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.AArch64.constants_ok a) fun b ⟨bc', bv, bg, bm, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.AArch64.ident_ok bc') fun c ⟨ct, cv, cg, cm, crd, cwr, csp⟩ => ?_
  refine WP.mono (VG.Proof.Rc4.AArch64.tailK_ok c) fun t ⟨tj, tsi, tv, t7, t5, t4, t8, tg, tm, trd, twr, tsp⟩ => ?_
  have hL1 := hL.1
  have gk : ∀ r, r ∉ VG.Proof.Rc4.AArch64.ksaRegs → t.gpr r = s.gpr r := fun r hr => by
    have n : ∀ g ∈ VG.Proof.Rc4.AArch64.ksaRegs, r ≠ g := fun g hg e => hr (e ▸ hg)
    rw [tg r (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide)), cg,
      bg r (n _ (by decide)) (n _ (by decide)),
      ag r (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide)) (n _ (by decide))
        (n _ (by decide))]
  have t0 : t.gpr .x0 = s.gpr .x0 := gk _ (by decide)
  have t1 : t.gpr .x1 = s.gpr .x1 := gk _ (by decide)
  have tvt : ∀ q < 16, t.v (treg q) = VG.Proof.Rc4.AArch64.laneNums q := fun q hq => by
    rw [tv _ ((show VG.Proof.Rc4.AArch64.NotTable .v0 by decide) q hq) ((show VG.Proof.Rc4.AArch64.NotTable .v4 by decide) q hq), ct q hq]
  have tcon : VG.Proof.Rc4.AArch64.Consts t := bc'.congr fun r hr => by
    rw [tv r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      cv r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  have tb : ∀ k < 256, VG.Proof.Rc4.AArch64.tbyte t.v k = BitVec.ofNat 8 k := fun k hk => by
    rw [VG.Proof.Rc4.AArch64.tbyte, tvt _ (by omega), VG.Proof.Rc4.AArch64.laneNums, vbyte_ofVBytes _ (by omega)]
    congr 1; omega
  have keep : ∀ v, v ≠ .v0 → v ≠ .v4 → VG.Proof.Rc4.AArch64.NotTable v → v ≠ .v7 → v ≠ .v8 → v ≠ .v9 → v ≠ .v10 →
      v ≠ .v11 → v ≠ .v12 → v ≠ .v13 → t.v v = s.v v := fun v h0 h4 ht h7 h8 h9 h10 h11 h12 h13 => by
    rw [tv v h0 h4, cv v ht, bv v h7 h8 h9 h10 h11 h12 h13, av]
  have hok : (VG.Proof.Rc4.AArch64.kglob s t).Ok := by
    refine ⟨hL.1, hL.2, t0, ?_, ?_⟩
    · show t.gpr .x1 = _
      rw [t1]; simp [VG.Proof.Rc4.AArch64.kglob]
    · show InRegions (t.rd ++ t.wr) _ _
      rw [trd, twr, crd, cwr, brd, bwr, ard, awr]; exact hk
  refine ⟨hok, ?_, fun p hp => ?_, gk, keep _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), by rw [tm, cm, bm, am], by rw [trd, crd, brd, ard],
    by rw [twr, cwr, bwr, awr], by rw [tsp, csp, bsp, asp]⟩
  · exact {
      consts := tcon
      table := fun k hk => by rw [tb k hk]; exact (VG.Proof.Rc4.AArch64.ident_get hk).symm
      j := by rw [tj, Nat.add_zero, schedule_zero]; decide
      si := by rw [tsi, tb 0 (by decide)]; rfl
      x7 := by rw [t7, cg, bg _ (by decide) (by decide), ag _ (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]; simp [VG.Proof.Rc4.AArch64.kglob]
      x5 := by
        rw [t5, cg, bg _ (by decide) (by decide), ag _ (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)]
        simp [VG.Proof.Rc4.AArch64.kglob]
      x8 := by rw [t8]
      x4 := by rw [t4]
      gpr := fun _ _ _ _ _ _ => rfl
      vkept := fun _ _ => rfl
      mem := by rw [tm, cm, bm, am]; rfl
      rd := rfl
      wr := rfl
      sp := rfl }
  · have ⟨h6, h7⟩ : p.2 ≠ .x6 ∧ p.2 ≠ .x7 := by revert p; decide
    have ⟨h4, h5, h8⟩ : p.2 ≠ .x4 ∧ p.2 ≠ .x5 ∧ p.2 ≠ .x8 := by revert p; decide
    rw [tg _ h4 h5 h7 h8, cg, bg _ h6 h7, asv p hp]

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Init`. -/
section

/-!
# The key schedule

`init_ok`: `vg_rc4_init` checks the key length, and for a valid one leaves
the key schedule with both indices zero at `ctx`, preserving the low halves
of `v8`–`v15`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem ctxRegs_ok (a : State) :
    WP isa (.block [.addImm .x .x0 .x2 0, .movz .x .x9 255 0]) a fun b =>
      b.gpr .x0 = a.gpr .x2 ∧ b.gpr .x9 = 255#64 ∧ (∀ r, r ≠ .x0 → r ≠ .x9 → b.gpr r = a.gpr r) ∧
      b.v = a.v ∧ b.mem = a.mem ∧ b.rd = a.rd ∧ b.wr = a.wr ∧ b.sp = a.sp := by
  rrun
  refine ⟨fun r h0 h9 => by simp [h0, h9], ?_⟩
  simp [State.write]

theorem zeros_ok {b : State} (hp : InRegions b.wr (b.gpr .x0) 258) :
    WP isa (.block [.movz .w .x6 0 0, .strb .x6 .x0 256, .strb .x6 .x0 257, .movz .w .x0 0 0]) b
      fun c => c.mem = (b.mem.write (b.gpr .x0 + 256#64) 1 0).write (b.gpr .x0 + 257#64) 1 0 ∧
        c.gpr .x0 = 0#64 ∧ (∀ r, r ≠ .x0 → r ≠ .x6 → c.gpr r = b.gpr r) ∧ c.v = b.v ∧
        c.rd = b.rd ∧ c.wr = b.wr ∧ c.sp = b.sp := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  have hz : BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 0#16))) =
    0#8 := by decide
  rrun [State.store, h256, h257]
  refine ⟨by rw [hz], fun r a b => by simp [a, b], by simp [State.write]⟩

theorem ksaFinish_ok {g : VG.Proof.Rc4.AArch64.KGlob} {u : State} (h : VG.Proof.Rc4.AArch64.KsaInv g 256 0 u)
    (hp : InRegions u.wr (u.gpr .x2) 258) :
    WP isa (.block scheduleFinish) u fun t =>
      t.gpr .x0 = 0#64 ∧
      contextAt t.mem (u.gpr .x2) = { table := (schedulePrefix g.key 256).1, i := 0, j := 0 } ∧
      (∀ p ∈ saved false, (t.v p.1).extractLsb' 0 64 = u.gpr p.2) ∧
      (∀ v, (∀ p ∈ saved false, p.1 ≠ v) → t.v v = u.v v) ∧
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp := by
  unfold scheduleFinish
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc4.AArch64.ctxRegs_ok u) fun a ⟨a0, a9, ag, av, am, ard, awr, asp⟩ => ?_
  rw [WP.block_append_iff, VG.Proof.Rc4.AArch64.storeTable_eq]
  have a8 : a.gpr .x8 = BitVec.ofNat 64 256 := by rw [ag _ (by decide) (by decide)]; exact h.x8
  have hpa : InRegions a.wr (a.gpr .x0) 258 := by rw [awr, a0]; exact hp
  have hpa' : InRegions a.wr (a.gpr .x0) 256 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      region_offset _ _ _ 0 256 (by decide) (by decide) hpa
  refine WP.mono (VG.Proof.Rc4.AArch64.storeN_ok (by decide) a8 a9 hpa' (Nat.le_refl 16))
    fun b ⟨brow, _, bv, bg, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  have b0 : b.gpr .x0 = a.gpr .x0 := bg _ (by decide) (by decide)
  refine WP.mono (VG.Proof.Rc4.AArch64.zeros_ok (by rw [bwr, b0]; exact hpa)) fun c ⟨cm, c0, cg, cv, crd, cwr, csp⟩ => ?_
  refine WP.mono (VG.Proof.Rc4.AArch64.restore_ok false c) fun t ⟨tsv, tv, tg, tm, trd, twr, tsp⟩ => ?_
  have hT : VG.Proof.Rc4.AArch64.TableIn a 256 (schedulePrefix g.key 256).1 := fun k hk => by
    rw [show VG.Proof.Rc4.AArch64.tbyte a.v = VG.Proof.Rc4.AArch64.tbyte u.v by rw [av]]; exact h.table k hk
  refine ⟨?_, ?_, fun p hp => ?_, fun v hv => ?_, ?_, ?_, ?_⟩
  · rw [tg, c0]
  · rw [tm, cm, b0, a0, context_finish, ← a0, VG.Proof.Rc4.AArch64.stored_table (by decide) hT brow]
  · have ⟨n0, n6, n7, n9⟩ : p.2 ≠ .x0 ∧ p.2 ≠ .x6 ∧ p.2 ≠ .x7 ∧ p.2 ≠ .x9 := by revert p; decide
    rw [tsv p hp, cg _ n0 n6, bg _ n6 n7, ag _ n0 n9]
  · rw [tv v hv, cv, bv, av]
  · rw [trd, crd, brd, ard]
  · rw [twr, cwr, bwr, awr]
  · rw [tsp, csp, bsp, asp]

theorem savedK_v : ∀ r ∈ VG.AArch64.preservedV, r = .v14 ∨ r = .v15 ∨ ∃ p ∈ saved false, p.1 = r := by decide

theorem savedK_kept : ∀ p ∈ saved false, p.2 ≠ .x4 ∧ p.2 ≠ .x5 ∧ p.2 ≠ .x6 ∧ p.2 ≠ .x7 ∧
    p.2 ≠ .x8 := by decide

theorem initValid_ok (s : State) (hL : 0 < (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256)
    (hp : InRegions s.wr (s.gpr .x2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat) :
    WP isa initValid s fun t => t.gpr .x0 = 0#64 ∧
      contextAt t.mem (s.gpr .x2) =
        { table := keySchedule (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat), i := 0, j := 0 } ∧
      ∀ r ∈ VG.AArch64.preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  unfold initValid
  refine WP.seq (WP.mono (VG.Proof.Rc4.AArch64.ksaSetup_ok hL hk)
    fun t ⟨hok, hi, tsv, tg, t14, t15, _, _, twr, _⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Rc4.AArch64.ksaLoop_ok hok 16 ⟨0, rfl, rfl, by decide, hi⟩) fun u hu => ?_)
  have u2 : u.gpr .x2 = s.gpr .x2 := by
    rw [hu.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact tg _ (by decide)
  have hpu : InRegions u.wr (u.gpr .x2) 258 := by
    rw [hu.wr, u2]; show InRegions t.wr _ _; rw [twr]; exact hp
  refine WP.mono (VG.Proof.Rc4.AArch64.ksaFinish_ok hu hpu) fun w ⟨w0, wc, wsv, wv, _, _, _⟩ => ?_
  refine ⟨w0, ?_, fun r hr => ?_⟩
  · rw [← u2, wc, keySchedule_eq]; rfl
  · have hn : ∀ p ∈ saved false, p.1 ≠ .v14 ∧ p.1 ≠ .v15 := by decide
    rcases VG.Proof.Rc4.AArch64.savedK_v r hr with rfl | rfl | ⟨p, hp, rfl⟩
    · rw [wv _ fun p hp => (hn p hp).1, hu.vkept _ (by decide)]; exact congrArg _ t14
    · rw [wv _ fun p hp => (hn p hp).2, hu.vkept _ (by decide)]; exact congrArg _ t15
    · obtain ⟨a4, a5, a6, a7, a8⟩ := VG.Proof.Rc4.AArch64.savedK_kept p hp
      rw [wsv p hp, hu.gpr _ a4 a5 a6 a7 a8]
      exact tsv p hp

theorem valid_length (len : BitVec 64) :
    (len - 1#64) >>> 8 = 0#64 ↔ 1 ≤ len.toNat ∧ len.toNat ≤ 256 := by bv_omega

/-- The full checked initializer, including both key-length boundaries. -/
theorem init_ok (s : State)
    (hp : InRegions s.wr (s.gpr .x2) 258)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x0) (s.gpr .x1).toNat) :
    WP isa VG.Impl.Rc4.AArch64.init s fun t =>
      (match VG.Spec.Rc4.init (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) with
      | .ok ctx => t.gpr .x0 = 0#64 ∧ contextAt t.mem (s.gpr .x2) = ctx
      | .error .invalidKeyLength => t.gpr .x0 = 1#64) ∧
      ∀ r ∈ VG.AArch64.preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  have hcheck : WP isa (.block [.subImm .x .x4 .x1 1, .lsr .x .x4 .x4 8]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.v = s.v ∧
      t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x2 ∧
      t.gpr .x4 = (s.gpr .x1 - 1#64) >>> 8 := by rrun
  unfold VG.Impl.Rc4.AArch64.init
  refine WP.seq (WP.mono hcheck fun t ht => ?_)
  obtain ⟨htm, htr, htw, htv, ht0, ht1, ht2, ht4⟩ := ht
  let good := 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256
  have hcond : isa.eval (.nonzero .x .x4) t = some (decide (¬ good)) := by
    simp only [eval, State.read, BitVec.setWidth_eq, ht4, BitVec.ofNat_eq_ofNat, bne]
    apply congrArg some
    by_cases hg : good
    · have hz := (VG.Proof.Rc4.AArch64.valid_length (s.gpr .x1)).mpr hg
      rw [hz, beq_self_eq_true]
      simp only [hg, not_true_eq_false, decide_false, Bool.not_true]
    · have hn : (s.gpr .x1 - 1#64) >>> 8 ≠ 0#64 := fun hz => hg ((VG.Proof.Rc4.AArch64.valid_length _).mp hz)
      rw [beq_eq_false_iff_ne.mpr hn]
      simp only [hg, not_false_eq_true, decide_true, Bool.not_false]
  refine WP.ite (decide (¬ good)) hcond (fun hn => ?_) (fun hy => ?_)
  · have hn' : ¬ good := of_decide_eq_true hn
    change ¬ (1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256) at hn'
    simp only [VG.Spec.Rc4.init, bytes_length, hn', ite_false]
    rrun
    exact fun r _ => by rw [htv]
  · have hg : good := by
      have hnn := of_decide_eq_false hy
      exact Classical.not_not.mp hnn
    change 1 ≤ (s.gpr .x1).toNat ∧ (s.gpr .x1).toNat ≤ 256 at hg
    simp only [VG.Spec.Rc4.init, bytes_length, hg, and_self, ite_true]
    have hpt : InRegions t.wr (t.gpr .x2) 258 := by rw [htw, ht2]; exact hp
    have hkt : InRegions (t.rd ++ t.wr) (t.gpr .x0) (t.gpr .x1).toNat := by
      rw [htr, htw, ht0, ht1]; exact hk
    have hlt : 0 < (t.gpr .x1).toNat ∧ (t.gpr .x1).toNat ≤ 256 := by rw [ht1]; omega
    refine WP.mono (VG.Proof.Rc4.AArch64.initValid_ok t hlt hpt hkt) fun u ⟨u0, uc, uv⟩ => ?_
    refine ⟨⟨u0, ?_⟩, fun r hr => by rw [uv r hr, htv]⟩
    rw [← ht2, uc, htm, ht0, ht1]

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.Taint`. -/
section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64

/-- Key scheduling has no secret-dependent control flow or memory address:
the key bytes, `j` and the table indices stay in vector registers. -/
theorem init_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2])) VG.Impl.Rc4.AArch64.init := by
  exact VG.Taint.constantTime (A := VG.AArch64.taint) (Taint.ofRegs [.x0, .x1, .x2])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Rc4.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc4.AArch64.VerifiedApply`. -/
section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4

def applySat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 1 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 258⟩, ⟨0x2000, 1⟩]

theorem apply_verified : Verified AArch64.target VG.Impl.Rc4.AArch64.apply
    (Spec.Rc4.applyContract AArch64.abi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    sig_pre [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost,
      Spec.Rc4.applyLeak, AArch64.abi, AArch64.argRegs] at hs
    obtain ⟨_, hwr, hsep, _⟩ := hs
    have hp : InRegions s.wr (s.gpr .x0) 258 := by
      refine ⟨⟨s.gpr .x0, 258⟩, ?_, ?_⟩
      · rw [hwr]; exact List.mem_cons_self
      · simp only [Region.Contains, BitVec.sub_self]; decide
    have hd : (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region) ∈ s.wr := by
      rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
    have hsep' : Mem.Sep (s.gpr .x0) 258 (s.gpr .x1) (s.gpr .x2).toNat :=
      hsep.sep (by simp [Region.Contains]) (by simp [Region.Contains])
    obtain ⟨tr, t, he, hpost, hregs⟩ := WP.gprs (rs := preserved) (VG.Proof.Rc4.AArch64.apply_ok s hp hd hsep')
      (by lit_decide) (by rfl)
    refine ⟨tr, t, he, ⟨hregs, Exec.sp he, hpost.2⟩, ?_⟩
    sig_post [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost,
      Spec.Rc4.applyLeak, AArch64.abi, AArch64.argRegs]
    exact hpost.1
  · intro s₁ s₂ tr₁ tr₂ t₁ t₂ hpre₁ hpre₂ hpub he₁ he₂
    sig_pre [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost,
      Spec.Rc4.applyLeak, AArch64.abi, AArch64.argRegs] at hpre₁ hpre₂
    sig_pub [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost,
      Spec.Rc4.applyLeak, AArch64.abi, AArch64.argRegs] at hpub
    obtain ⟨hsp, hleak, h0, h1, h2⟩ := hpub
    have hp₁ : VG.Proof.Rc4.AArch64.ReadValid s₁ := by
      refine ⟨⟨s₁.gpr .x0, 258⟩, List.mem_append_right _ ?_, ?_⟩
      · rw [hpre₁.2.1]; exact List.mem_cons_self
      · simp only [Region.Contains, BitVec.sub_self]; decide
    have hp₂ : VG.Proof.Rc4.AArch64.ReadValid s₂ := by
      refine ⟨⟨s₂.gpr .x0, 258⟩, List.mem_append_right _ ?_, ?_⟩
      · rw [hpre₂.2.1]; exact List.mem_cons_self
      · simp only [Region.Contains, BitVec.sub_self]; decide
    have hi : (contextAt s₁.mem (s₁.gpr .x0)).i = (contextAt s₂.mem (s₂.gpr .x0)).i :=
      BitVec.eq_of_toNat_eq (List.cons.inj hleak).1
    exact VG.Proof.Rc4.AArch64.apply_ct s₁ s₂ tr₁ tr₂ t₁ t₂ hp₁ hp₂ ⟨hsp, h0, h1, h2, hi⟩ he₁ he₂
  · sig_implies_sat [Spec.Rc4.applyContract, Spec.Rc4.applySig, Spec.Rc4.applyPost,
      Spec.Rc4.applyLeak, AArch64.abi, AArch64.argRegs]
      [applySat] using VG.Proof.Rc4.AArch64.applySat

end VG.Proof.Rc4.AArch64

end
