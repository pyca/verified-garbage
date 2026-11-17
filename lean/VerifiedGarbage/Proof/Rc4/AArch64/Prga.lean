module

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Spec.Rc4
import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Impl.Rc4.AArch64

/-! ### `Rc4.AArch64.Lookup`, which this module and modules that import it used -/

section

/-! ### `Rc4.AArch64.Regs`, which this module and modules that import it used -/

section

/-!
# The table registers

Byte `k` of the table registers (`tbyte`) is lane `k % 16` of
`v(16 + k / 16)`. A four-register `tbl`/`tbx` from `v16`, `v20`, `v24` or
`v28` reads the bytes of one quarter of it.
-/

@[expose] public section

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

-- Given directly: `inferInstanceAs` searches for it for seconds.
instance (r : VReg) : Decidable (NotTable r) := Nat.decidableBallLT 16 fun a _ => treg a ≠ r

theorem treg_of_ge {n : Nat} (h : 16 ≤ n) : treg n = .v16 := by
  simp only [treg, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by simp; omega_using [h])]; rfl

theorem NotTable.ne {r : VReg} (h : NotTable r) (n : Nat) : treg n ≠ r := by
  by_cases hn : n < 16
  · exact h n hn
  · rw [treg_of_ge (by omega_using [hn])]; exact h 0 (by decide)

theorem tbyte_congr {v w : VReg → BitVec 128} (h : ∀ a < 16, v (treg a) = w (treg a)) {k : Nat}
    (hk : k < 256) : tbyte v k = tbyte w k := by
  simp only [tbyte, h _ (by omega_using [hk] : k / 16 < 16)]

/-- The table byte that a quarter's `tbl` reads, for an index in the quarter. -/
theorem tableByte_quarter (v : VReg → BitVec 128) {q : Nat} (hq : q < 4) {idx : Nat} (hi : idx < 64) :
    tableByte v ([VReg.v16, .v20, .v24, .v28].getD q .v16) idx = tbyte v (64 * q + idx) := by
  simp only [tableByte, tbyte, treg_quarter q hq _ (by omega_using [hi] : idx / 16 < 4)]
  rw [show (64 * q + idx) / 16 = 4 * q + idx / 16 by omega_using [], show (64 * q + idx) % 16 = idx % 16 by omega_using []]

/-- The quarter of each byte, and its index there. -/
theorem xor_quarter : ∀ x < 256, ∀ q < 4,
    (x ^^^ 64 * q < 64 ↔ x / 64 = q) ∧ (x / 64 = q → x ^^^ 64 * q = x - 64 * q) := by
  decide +kernel

/-! ## The constants -/

/-- The lane numbers of quarter `q`: `16 q`, …, `16 q + 15`. -/
def laneNums (q : Nat) : BitVec 128 := ofVBytes fun e => BitVec.ofNat 8 (16 * q + e)

structure Consts (s : State) : Prop where
  lns : ∀ q < 4, s.v (VG.Impl.Rc4.AArch64.lanes q) = laneNums q
  c64 : s.v c64 = bc 64
  c128 : s.v c128 = bc 128

theorem Consts.congr {s s' : State} (h : Consts s)
    (hv : ∀ r, r = .v8 ∨ r = .v9 ∨ r = .v10 ∨ r = .v11 ∨ r = .v12 ∨ r = .v13 → s'.v r = s.v r) :
    Consts s' where
  lns q hq := by
    have : VG.Impl.Rc4.AArch64.lanes q = .v8 ∨ VG.Impl.Rc4.AArch64.lanes q = .v9 ∨
        VG.Impl.Rc4.AArch64.lanes q = .v10 ∨ VG.Impl.Rc4.AArch64.lanes q = .v11 := by
      revert q; decide
    rw [hv _ (by rcases this with h | h | h | h <;> simp [h])]; exact h.lns q hq
  c64 := by rw [hv _ (by simp [VG.Impl.Rc4.AArch64.c64])]; exact h.c64
  c128 := by rw [hv _ (by simp [VG.Impl.Rc4.AArch64.c128])]; exact h.c128

end VG.Proof.Rc4.AArch64

end

end

/-!
# A table lookup

`lookup_run`: from the index `X` broadcast in `x`, and `X ^ 64`, `X ^ 128`,
`X ^ 192` in `a`, `b`, `c` (`quarters_run` computes them), the lookup
leaves `S[X]` (`tbyte`) broadcast in `d`, through the temporary `t`.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

theorem exec_vop' (s : State) (op : VOp) :
    exec (.vop op) s = (op.eval s).map fun (d, x) => s.setV d x := rfl

/-- The registers but `d` keep their values, and nothing else changes. -/
def Only (ds : List VReg) (s s' : State) : Prop :=
  s' = { s with v := s'.v } ∧ ∀ r, r ∉ ds → s'.v r = s.v r

theorem Only.refl (ds : List VReg) (s : State) : Only ds s s := ⟨rfl, fun _ _ => rfl⟩

theorem Only.trans {ds : List VReg} {a b c : State} (h₁ : Only ds a b) (h₂ : Only ds b c) :
    Only ds a c := by
  refine ⟨?_, fun r hr => (h₂.2 r hr).trans (h₁.2 r hr)⟩
  rw [h₂.1, h₁.1]

theorem Only.mono {ds ds' : List VReg} {a b : State} (h : Only ds a b) (hs : ∀ r ∈ ds, r ∈ ds') :
    Only ds' a b := ⟨h.1, fun r hr => h.2 r fun h' => hr (hs r h')⟩

theorem Only.setV (s : State) {d : VReg} {ds : List VReg} (hd : d ∈ ds) (x : BitVec 128) :
    Only ds s (s.setV d x) := by
  refine ⟨rfl, fun r hr => ?_⟩
  have : r ≠ d := fun e => hr (e ▸ hd)
  exact v_setV_of_ne _ _ this

theorem Only.gpr {ds : List VReg} {s s' : State} (h : Only ds s s') : s'.gpr = s.gpr := by
  rw [h.1]
theorem Only.mem {ds : List VReg} {s s' : State} (h : Only ds s s') : s'.mem = s.mem := by
  rw [h.1]
theorem Only.rd {ds : List VReg} {s s' : State} (h : Only ds s s') : s'.rd = s.rd := by
  rw [h.1]
theorem Only.wr {ds : List VReg} {s s' : State} (h : Only ds s s') : s'.wr = s.wr := by
  rw [h.1]
theorem Only.sp {ds : List VReg} {s s' : State} (h : Only ds s s') : s'.sp = s.sp := by
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
  rw [runBlock_cat, h₁, Option.bind_some, h₂]

/-! ## The quarters -/

theorem xor64_128 (X : BitVec 8) : X ^^^ 64 ^^^ 128 = X ^^^ 192 := by
  rw [BitVec.xor_assoc]; rfl

theorem quarters_run {s : State} (hk : Consts s) {x a b c : VReg} (X : BitVec 8)
    (hx : s.v x = bc X) (hax : a ≠ x) (hba : b ≠ a) (hca : c ≠ a) (hbc : b ≠ c)
    (ha128 : a ≠ c128) (hb128 : b ≠ c128) :
    ∃ s', runBlock isa (quarters x a b c) s = some s' ∧ s'.v a = bc (X ^^^ 64) ∧
      s'.v b = bc (X ^^^ 128) ∧ s'.v c = bc (X ^^^ 192) ∧ Only [a, b, c] s s' := by
  let s₁ := s.setV a (s.v x ^^^ s.v c64)
  let s₂ := s₁.setV b (s₁.v x ^^^ s₁.v c128)
  let s₃ := s₂.setV c (s₂.v a ^^^ s₂.v c128)
  have ha₁ : s₁.v a = bc (X ^^^ 64) := by
    simp only [s₁, v_setV_self, hx, hk.c64, bc_xor]
  have ha₂ : s₂.v a = bc (X ^^^ 64) := by simp only [s₂, v_setV_of_ne _ _ (Ne.symm hba), ha₁]
  have hb₂ : s₂.v b = bc (X ^^^ 128) := by
    simp only [s₂, v_setV_self, s₁, v_setV_of_ne _ _ hax.symm, v_setV_of_ne _ _ ha128.symm, hx,
      hk.c128, bc_xor]
  have c128₂ : s₂.v c128 = bc 128 := by
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
  · simp only [s₃, v_setV_self, ha₂, c128₂, bc_xor, xor64_128]
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
      qbyte (tbyte s.v) q (vbyte (s.v m) e).toNat ext (vbyte (s.v d) e) := by
  rw [vbyte_ofVBytes _ he, qbyte]
  split
  · rename_i h; rw [tableByte_quarter _ hq h]
  · rfl

theorem or_zero8 (y : BitVec 8) : y ||| 0 = y := by simp
theorem zero_or8 (y : BitVec 8) : 0 ||| y = y := by simp

/-- The four quarters' bytes, combined, are the byte at the index. -/
theorem quarters_byte (T : Nat → BitVec 8) (X : BitVec 8) (p p' : BitVec 8) :
    qbyte T 1 (X.toNat ^^^ 64) true (qbyte T 0 X.toNat false p) |||
      qbyte T 3 (X.toNat ^^^ 192) true (qbyte T 2 (X.toNat ^^^ 128) false p') = T X.toNat := by
  have hX := X.isLt
  have q := xor_quarter X.toNat hX
  obtain ⟨h1, e1⟩ := q 1 (by decide)
  obtain ⟨h2, e2⟩ := q 2 (by decide)
  obtain ⟨h3, e3⟩ := q 3 (by decide)
  simp only [Nat.mul_one, show 64 * 2 = 128 by rfl, show 64 * 3 = 192 by rfl] at h1 h2 h3 e1 e2 e3
  simp only [qbyte]
  have n1 : X.toNat / 64 ≠ 1 → ¬ (X.toNat ^^^ 64 < 64) := fun h h' => h (h1.mp h')
  have n2 : X.toNat / 64 ≠ 2 → ¬ (X.toNat ^^^ 128 < 64) := fun h h' => h (h2.mp h')
  have n3 : X.toNat / 64 ≠ 3 → ¬ (X.toNat ^^^ 192 < 64) := fun h h' => h (h3.mp h')
  rcases (by omega_using [] : X.toNat / 64 = 0 ∨ X.toNat / 64 = 1 ∨ X.toNat / 64 = 2 ∨ X.toNat / 64 = 3)
    with h | h | h | h
  · simp only [show X.toNat < 64 by omega_using [h], n1 (by omega_using [h]), n2 (by omega_using [h]), n3 (by omega_using [h]), ite_true,
      ite_false, Bool.false_eq_true, Nat.mul_zero, Nat.zero_add, or_zero8]
  · simp only [show ¬ X.toNat < 64 by omega_using [h], h1.mpr h, n2 (by omega_using [h]), n3 (by omega_using [h]), ite_true,
      ite_false, Bool.false_eq_true]
    rw [e1 h, or_zero8]
    exact congrArg T (by omega_using [h])
  · simp only [show ¬ X.toNat < 64 by omega_using [h], n1 (by omega_using [h]), h2.mpr h, n3 (by omega_using [h]), ite_true,
      ite_false, Bool.false_eq_true]
    rw [e2 h, zero_or8]
    exact congrArg T (by omega_using [h])
  · simp only [show ¬ X.toNat < 64 by omega_using [h], n1 (by omega_using [h]), n2 (by omega_using [h]), h3.mpr h, ite_true,
      ite_false, Bool.false_eq_true]
    rw [e3 h, zero_or8]
    exact congrArg T (by omega_using [h])

theorem xor_toNat (X : BitVec 8) (k : BitVec 8) : (X ^^^ k).toNat = X.toNat ^^^ k.toNat :=
  BitVec.toNat_xor _ _

theorem lookup_run {s : State} {d t x a b c : VReg} (X : BitVec 8)
    (hx : s.v x = bc X) (ha : s.v a = bc (X ^^^ 64)) (hb : s.v b = bc (X ^^^ 128))
    (hc : s.v c = bc (X ^^^ 192))
    (hd : NotTable d) (ht : NotTable t) (hdt : d ≠ t) (hda : d ≠ a) (hdb : d ≠ b)
    (hdc : d ≠ c) (htc : t ≠ c) :
    ∃ s', runBlock isa (lookup d t x a b c) s = some s' ∧ s'.v d = bc (tbyte s.v X.toNat) ∧
      Only [d, t] s s' := by
  let T := tbyte s.v
  let f (q : Nat) (m : VReg) (ext : Bool) (st : State) (dd : VReg) : BitVec 128 :=
    ofVBytes fun i => if (vbyte (st.v m) i).toNat < 16 * 4 then
      tableByte st.v ([VReg.v16, .v20, .v24, .v28].getD q .v16) (vbyte (st.v m) i).toNat
    else if ext then vbyte (st.v dd) i else 0
  let s₁ := s.setV d (f 0 x false s d)
  let s₂ := s₁.setV d (f 1 a true s₁ d)
  let s₃ := s₂.setV t (f 2 b false s₂ t)
  let s₄ := s₃.setV t (f 3 c true s₃ t)
  let s₅ := s₄.setV d (s₄.v d ||| s₄.v t)
  have o₁ : Only [d, t] s s₁ := Only.setV _ (by simp) _
  have o₂ : Only [d, t] s s₂ := o₁.trans (Only.setV _ (by simp) _)
  have o₃ : Only [d, t] s s₃ := o₂.trans (Only.setV _ (by simp) _)
  have o₄ : Only [d, t] s s₄ := o₃.trans (Only.setV _ (by simp) _)
  have o₅ : Only [d, t] s s₅ := o₄.trans (Only.setV _ (by simp) _)
  have tab : ∀ st, Only [d, t] s st → tbyte st.v = T := by
    intro st h; funext k; simp only [tbyte, T]
    rw [h.2 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hd.ne _, ht.ne _⟩)]
  have a₁ : s₁.v a = bc (X ^^^ 64) := by rw [v_setV_of_ne _ _ (Ne.symm hda), ha]
  have b₂ : s₂.v b = bc (X ^^^ 128) := by
    rw [v_setV_of_ne _ _ (Ne.symm hdb), v_setV_of_ne _ _ (Ne.symm hdb), hb]
  have c₃ : s₃.v c = bc (X ^^^ 192) := by
    rw [v_setV_of_ne _ _ (Ne.symm htc), v_setV_of_ne _ _ (Ne.symm hdc), v_setV_of_ne _ _ (Ne.symm hdc), hc]
  have d₄ : s₄.v d = s₂.v d := by
    rw [v_setV_of_ne _ _ hdt, v_setV_of_ne _ _ hdt]
  have hf : ∀ q m ext st dd e, q < 4 → e < 16 →
      vbyte (f q m ext st dd) e = qbyte (tbyte st.v) q (vbyte (st.v m) e).toNat ext (vbyte (st.v dd) e) :=
    fun q m ext st dd e hq he => vbyte_tblN st ext hq dd m he
  have y₁ : ∀ e < 16, vbyte (s₁.v d) e = qbyte T 0 X.toNat false (vbyte (s.v d) e) := by
    intro e he
    rw [show s₁.v d = f 0 x false s d from v_setV_self _ _ _, hf _ _ _ _ _ _ (by decide) he, hx,
      vbyte_bc _ he]
  have y₂ : ∀ e < 16, vbyte (s₂.v d) e =
      qbyte T 1 (X.toNat ^^^ 64) true (vbyte (s₁.v d) e) := by
    intro e he
    rw [show s₂.v d = f 1 a true s₁ d from v_setV_self _ _ _, hf _ _ _ _ _ _ (by decide) he, a₁,
      vbyte_bc _ he, xor_toNat, tab s₁ o₁]
    rfl
  have y₃ : ∀ e < 16, vbyte (s₃.v t) e =
      qbyte T 2 (X.toNat ^^^ 128) false (vbyte (s₂.v t) e) := by
    intro e he
    rw [show s₃.v t = f 2 b false s₂ t from v_setV_self _ _ _, hf _ _ _ _ _ _ (by decide) he, b₂,
      vbyte_bc _ he, xor_toNat, tab s₂ o₂]
    rfl
  have y₄ : ∀ e < 16, vbyte (s₄.v t) e =
      qbyte T 3 (X.toNat ^^^ 192) true (vbyte (s₃.v t) e) := by
    intro e he
    rw [show s₄.v t = f 3 c true s₃ t from v_setV_self _ _ _, hf _ _ _ _ _ _ (by decide) he, c₃,
      vbyte_bc _ he, xor_toNat, tab s₃ o₃]
    rfl
  refine ⟨s₅, ?_, ?_, o₅⟩
  · have e₁ : exec (.vop (.tblN false 4 d .v16 x)) s = some s₁ := rfl
    have e₂ : exec (.vop (.tblN true 4 d .v20 a)) s₁ = some s₂ := rfl
    have e₃ : exec (.vop (.tblN false 4 t .v24 b)) s₂ = some s₃ := rfl
    have e₄ : exec (.vop (.tblN true 4 t .v28 c)) s₃ = some s₄ := rfl
    have e₅ : exec (.vop (.logic .orr d d t)) s₄ = some s₅ := rfl
    rw [lookup, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  · apply vbyte_ext; intro e he
    simp only [s₅, v_setV_self, vbyte_or, d₄, y₂ e he, y₁ e he, y₄ e he, y₃ e he, vbyte_bc _ he]
    exact quarters_byte T X _ _

end VG.Proof.Rc4.AArch64

end

end

/-! ### `Rc4.AArch64.Output`, which only this module used -/

section

/-!
# A keystream byte

`output_ok`: with the output index `X` (from the base) broadcast in `v6`,
the keystream byte `S[X]` is looked up and XORed into the data byte at `x1`;
`x1` and `x2` advance.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

theorem low_byte (K : BitVec 8) : ((bc K).extractLsb' 0 32).setWidth 8 = K := by
  obtain h := vbyte_bc K (e := 0) (by decide)
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (·.getLsbD i) h
  simp only [vbyte, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Nat.mul_zero,
    Nat.zero_add] at this
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show i < 32 by omega_using [hi], Nat.zero_add]
  exact this

theorem xor_low_byte (a : BitVec 8) (w : BitVec 32) :
    ((a.setWidth 32 ^^^ w).setWidth 8) = a ^^^ w.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi, show i < 32 by omega_using [hi]]

/-- The scalar part: the byte's XOR, and the pointer and count. -/
theorem outScalar_ok {s : State} {K : BitVec 8} (h7 : s.v .v7 = bc K)
    (hd : InRegions s.wr (s.gpr .x1) 1) :
    WP isa (.block [.umov .w .x6 .v7 0, .ldrb .x7 .x1 0, .logic .eor .w .x7 .x7 .x6, .strb .x7 .x1 0,
        .addImm .x .x1 .x1 1, .subImm .x .x2 .x2 1]) s fun t =>
      t.mem = s.mem.write (s.gpr .x1) 1 (s.mem (s.gpr .x1) ^^^ K) ∧
      t.gpr .x1 = s.gpr .x1 + 1 ∧ t.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      t.v = s.v ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain hr : InRegions (s.rd ++ s.wr) (s.gpr .x1) 1 := by
    obtain ⟨region, hregion, hc⟩ := hd
    exact ⟨region, List.mem_append_right _ hregion, hc⟩
  have hc8 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x :=
    (BitVec.setWidth_setWidth_of_le x (by decide)).trans (BitVec.setWidth_eq x)
  have read1 (m : Mem) (p : Addr) : m.read p 1 = m p := by
    change (0#0 ++ m p : BitVec 8) = m p
    exact BitVec.zero_width_append _ _
  rrun [State.store, hd, hr, read1, hc8, h7, xor_low_byte, low_byte]
  refine ⟨fun r h1 h2 h6 h7 => by simp [h1, h2, h6, h7], ?_⟩
  simp [State.write]

/-- The registers the output changes. -/
def outRegs : List VReg := [.v1, .v2, .v3, .v7]

theorem output_ok {s : State} (hk : Consts s) {X : BitVec 8} (hx : s.v .v6 = bc X)
    (hd : InRegions s.wr (s.gpr .x1) 1) :
    WP isa (.block output) s fun t =>
      t.mem = s.mem.write (s.gpr .x1) 1 (s.mem (s.gpr .x1) ^^^ tbyte s.v X.toNat) ∧
      t.gpr .x1 = s.gpr .x1 + 1 ∧ t.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      (∀ r, r ∉ outRegs → t.v r = s.v r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  obtain ⟨s₁, run₁, a₁, b₁, c₁, o₁⟩ := quarters_run (x := .v6) (a := .v1) (b := .v2) (c := .v3) hk X hx
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain x₁ : s₁.v .v6 = bc X := by rw [o₁.2 _ (by decide), hx]
  obtain ⟨s₂, run₂, v₂, o₂⟩ := lookup_run (d := .v7) (t := .v1) (x := .v6) (a := .v1) (b := .v2)
    (c := .v3) X x₁ a₁ b₁ c₁ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  obtain t₁ : tbyte s₁.v = tbyte s.v := by
    funext k; simp only [tbyte]
    rw [o₁.2 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(show NotTable .v1 by decide).ne _, (show NotTable .v2 by decide).ne _,
        (show NotTable .v3 by decide).ne _⟩)]
  rw [t₁] at v₂
  obtain o : Only outRegs s s₂ := (o₁.mono (by decide)).trans (o₂.mono (by decide))
  rw [output, WP.block_append_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩
  obtain hd₂ : InRegions s₂.wr (s₂.gpr .x1) 1 := by rw [o.wr, o.gpr]; exact hd
  refine WP.mono (outScalar_ok v₂ hd₂) fun t ⟨m, x1, x2, g, v, rd, wr, sp⟩ => ?_
  refine ⟨by rw [m, o.mem, o.gpr], by rw [x1, o.gpr], by rw [x2, o.gpr],
    fun r a b c d => by rw [g r a b c d, o.gpr], fun r hr => by rw [v, o.2 r hr],
    by rw [rd, o.rd], by rw [wr, o.wr], by rw [sp, o.sp]⟩

end VG.Proof.Rc4.AArch64

end

end

/-! ### `Rc4.AArch64.Step`, which only this module used -/

section

/-! ### `Rc4.AArch64.WriteJ`, which only this module used -/

section

/-!
# A write at a secret index

`writeJ_run`: with the index `J` (and `J ^ 64`, `J ^ 128`, `J ^ 192`)
broadcast in `v0`–`v3` and the value `V` broadcast in `v4`, the sixteen
`cmeq`/`bit` pairs replace byte `J` of the table registers by `V`, and leave
the others.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

/-- The index's four quarters, broadcast in `v0`–`v3`. -/
def Quarters (s : State) (J : BitVec 8) : Prop :=
  ∀ q < 4, s.v (dq q) = bc (J ^^^ BitVec.ofNat 8 (64 * q))

theorem xor_low : ∀ a < 64, ∀ q < 4, a ^^^ 64 * q = 64 * q + a := by decide +kernel

/-- Lane `e` of quarter `r % 4`'s lane numbers equals `J ^ 64 (r / 4)` just
when `16 r + e` is `J`. -/
theorem lane_eq (J : BitVec 8) {r e : Nat} (hr : r < 16) (he : e < 16) :
    BitVec.ofNat 8 (16 * (r % 4) + e) = J ^^^ BitVec.ofNat 8 (64 * (r / 4)) ↔ 16 * r + e = J.toNat := by
  have hJ := J.isLt
  obtain hq : (BitVec.ofNat 8 (64 * (r / 4))).toNat = 64 * (r / 4) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hr])]
  obtain ha : (BitVec.ofNat 8 (16 * (r % 4) + e)).toNat = 16 * (r % 4) + e := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [he])]
  obtain low := xor_low (16 * (r % 4) + e) (by omega_using [he]) (r / 4) (by omega_using [hr])
  constructor
  · intro h
    obtain h' := congrArg BitVec.toNat h
    rw [ha, BitVec.toNat_xor, hq] at h'
    have : J.toNat = (16 * (r % 4) + e) ^^^ 64 * (r / 4) := by
      rw [h', Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [low] at this
    omega_using [this]
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [ha, BitVec.toNat_xor, hq, ← h, show 16 * r + e = 64 * (r / 4) + (16 * (r % 4) + e) by omega_using [],
      ← low, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

def writeN (n : Nat) : List Instr :=
  (List.range n).flatMap fun k =>
    [.vop (.cmeq .b16 .v7 (lanes (k % 4)) (dq (k / 4))), .vop (.bsel .bit (treg k) si .v7)]

theorem writeN_succ (n : Nat) : writeN (n + 1) = writeN n ++
    ([.vop (.cmeq .b16 .v7 (lanes (n % 4)) (dq (n / 4))), .vop (.bsel .bit (treg n) si .v7)] :
      List Instr) := by
  simp only [writeN, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- The registers the write changes. -/
def writeRegs : List VReg :=
  [.v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31]

theorem treg_mem : ∀ r < 16, treg r ∈ writeRegs := by decide

theorem notTable_v7 : NotTable .v7 := by decide

theorem lanes_notW : ∀ q < 4, lanes q ∉ writeRegs := by decide
theorem dq_notW : ∀ q < 4, dq q ∉ writeRegs := by decide

theorem writeN_run {s : State} (hk : Consts s) {J V : BitVec 8} (hq : Quarters s J)
    (hv : s.v si = bc V) {n : Nat} (hn : n ≤ 16) :
    ∃ s', runBlock isa (writeN n) s = some s' ∧
      (∀ k < 256, tbyte s'.v k = if k / 16 < n ∧ k = J.toNat then V else tbyte s.v k) ∧
      Only writeRegs s s' := by
  induction n with
  | zero => exact ⟨s, runBlock_nil, fun k _ => by simp, Only.refl _ _⟩
  | succ n ih =>
    obtain ⟨s₁, run₁, t₁, o₁⟩ := ih (by omega_using [hn])
    have notW : ∀ r, r ∉ writeRegs → s₁.v r = s.v r := o₁.2
    let m := VArr.b16.map2 (fun w a b => if a = b then BitVec.allOnes w else 0)
      (s₁.v (lanes (n % 4))) (s₁.v (dq (n / 4)))
    let s₂ := s₁.setV .v7 m
    let s₃ := s₂.setV (treg n) (VSelOp.bit.eval (s₂.v (treg n)) (s₂.v si) (s₂.v .v7))
    have e₂ : exec (.vop (.cmeq .b16 .v7 (lanes (n % 4)) (dq (n / 4)))) s₁ = some s₂ := rfl
    have e₃ : exec (.vop (.bsel .bit (treg n) si .v7)) s₂ = some s₃ := rfl
    obtain l₁ : s₁.v (lanes (n % 4)) = laneNums (n % 4) := by
      rw [notW _ (lanes_notW _ (by omega_using []))]; exact hk.lns _ (by omega_using [])
    obtain d₁ : s₁.v (dq (n / 4)) = bc (J ^^^ BitVec.ofNat 8 (64 * (n / 4))) := by
      rw [notW _ (dq_notW _ (by omega_using [hn]))]
      exact hq _ (by omega_using [hn])
    obtain v₂ : s₂.v si = bc V := by
      rw [v_setV_of_ne _ _ (by decide), notW _ (by decide)]; exact hv
    obtain m_byte : ∀ e < 16, vbyte (s₂.v .v7) e =
        if 16 * n + e = J.toNat then BitVec.allOnes 8 else 0 := by
      intro e he
      rw [v_setV_self, vbyte_cmeq _ _ he, l₁, d₁, laneNums, vbyte_ofVBytes _ he, vbyte_bc _ he]
      simp only [lane_eq J (by omega_using [hn] : n < 16) he]
    refine ⟨s₃, by rw [writeN_succ]; exact runBlock_cat_some run₁ (by
      rw [runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil]), ?_, ?_⟩
    · intro k hk
      by_cases hkn : k / 16 = n
      · have b₃ : tbyte s₃.v k = vbyte (VSelOp.bit.eval (s₂.v (treg n)) (s₂.v si) (s₂.v .v7)) (k % 16) := by
          simp only [tbyte, hkn, s₃, v_setV_self]
        rw [b₃, vbyte_bit _ _ _ (16 * n + k % 16 = J.toNat) (m_byte _ (by omega_using [])), v₂,
          vbyte_bc _ (by omega_using [])]
        obtain old : vbyte (s₂.v (treg n)) (k % 16) = tbyte s.v k := by
          rw [v_setV_of_ne _ _ (notTable_v7.ne n)]
          have := t₁ k hk
          simp only [show ¬ k / 16 < n by omega_using [hkn], false_and, ite_false] at this
          rw [← this]; simp only [tbyte, hkn]
        rw [old]
        exact ite_iff ⟨fun h => ⟨by omega_using [hkn], by omega_using [hkn, h]⟩, fun h => by omega_using [hkn, h]⟩ _ _
      · have ne : treg (k / 16) ≠ treg n := fun h => hkn (treg_inj _ (by omega_using [hk]) _ (by omega_using [hn]) h)
        obtain keep : s₃.v (treg (k / 16)) = s₁.v (treg (k / 16)) := by
          rw [v_setV_of_ne _ _ ne, v_setV_of_ne _ _ (notTable_v7.ne _)]
        have : tbyte s₃.v k = tbyte s₁.v k := by simp only [tbyte, keep]
        rw [this, t₁ k hk]
        obtain e : (k / 16 < n + 1) ↔ (k / 16 < n) := by omega_using [hkn]
        simp only [e]
    · exact (o₁.trans (Only.setV _ (by decide) _)).trans (Only.setV _ (treg_mem n (by omega_using [hn])) _)

end VG.Proof.Rc4.AArch64

end

end


/-!
# One swap

`swapStep_run`: with the table `R` in the table registers (indexed from the
base), `j` (from the base) broadcast in `v0` and `S[i] = R l` broadcast in
`v4`, the swap step adds `R l` to `j`, swaps `R l` and `R j`, leaves the
next `S[i]` (the new `R (l + 1)`) in `v4` and, in the PRGA, the output index
`R l + R j - B` in `v6`.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64

theorem dupE_bc (s : State) (n : VReg) (i : Nat) :
    VArr.b16.map2 (fun w _ _ => (s.v n).extractLsb' (w * i) w) 0 0 = bc (vbyte (s.v n) i) :=
  vbyte_ext fun e he => by
    rw [vbyte_map2 _ _ _ he, vbyte_bc _ he]
    rfl

/-- What follows the write at `j`: the output index, in the PRGA, the next
`S[i]`, and the write at `i`. -/
def stepTail (prga : Bool) (l : Nat) : List Instr :=
  (if prga then [.vop (.add .b16 .v6 si .v5), .vop (.add .b16 .v6 .v6 negBase)] else []) ++
  [.vop (.dupE .b16 si (treg ((l + 1) / 16)) ((l + 1) % 16)), .vop (.insE .b16 (treg 0) l .v5 0)]

theorem swapStep_eq (prga : Bool) (l : Nat) :
    swapStep prga l = ([.vop (.add .b16 (dq 0) (dq 0) si)] : List Instr) ++
      (quarters (dq 0) (dq 1) (dq 2) (dq 3) ++ (lookup .v5 .v6 (dq 0) (dq 1) (dq 2) (dq 3) ++
        (writeN 16 ++ stepTail prga l))) := by
  simp only [swapStep, stepTail, writeJ, writeN, List.append_assoc]

/-- The registers a swap step changes. -/
def stepRegs : List VReg :=
  [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7,
   .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25, .v26, .v27, .v28, .v29, .v30, .v31]

/-- The table after the swap of positions `l` and `J`. -/
def swapR (R : Nat → BitVec 8) (l J : Nat) (k : Nat) : BitVec 8 :=
  if k = l then R J else if k = J then R l else R k

theorem consts_of_only {s s' : State} (hk : Consts s) (h : Only stepRegs s s') : Consts s' :=
  hk.congr fun r hr => h.2 r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

theorem swapStep_run (prga : Bool) {l : Nat} (hl : l < 16) {s : State} (hk : Consts s)
    {Jr NB : BitVec 8} (hj : s.v (dq 0) = bc Jr) (hi : s.v si = bc (tbyte s.v l))
    (hn : prga = true → s.v negBase = bc NB) :
    ∃ s', runBlock isa (swapStep prga l) s = some s' ∧
      (∀ k < 256, tbyte s'.v k =
        swapR (tbyte s.v) l (Jr + tbyte s.v l).toNat k) ∧
      s'.v (dq 0) = bc (Jr + tbyte s.v l) ∧
      s'.v si = bc (swapR (tbyte s.v) l (Jr + tbyte s.v l).toNat (l + 1)) ∧
      (prga = true → s'.v .v6 = bc (tbyte s.v l + tbyte s.v (Jr + tbyte s.v l).toNat + NB)) ∧
      Only stepRegs s s' := by
  let R := tbyte s.v
  let J := Jr + R l
  -- j += S[i]
  let s₁ := s.setV (dq 0) (VArr.b16.map2 (fun _ x y => x + y) (s.v (dq 0)) (s.v si))
  have e₁ : exec (.vop (.add .b16 (dq 0) (dq 0) si)) s = some s₁ := rfl
  obtain o₁ : Only stepRegs s s₁ := Only.setV _ (by decide) _
  obtain j₁ : s₁.v (dq 0) = bc J := by rw [v_setV_self, hj, hi, add_bc]
  obtain k₁ : Consts s₁ := consts_of_only hk o₁
  obtain t₁ : tbyte s₁.v = R := by
    funext k; simp only [tbyte, R]; rw [v_setV_of_ne _ _ ((show NotTable (dq 0) by decide).ne _)]
  -- the quarters
  obtain ⟨s₂, run₂, a₂, b₂, c₂, o₂⟩ := quarters_run (x := dq 0) (a := dq 1) (b := dq 2) (c := dq 3) k₁ J j₁ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  obtain o₂' : Only stepRegs s s₂ := o₁.trans (o₂.mono (by decide))
  obtain j₂ : s₂.v (dq 0) = bc J := by rw [o₂.2 _ (by decide), j₁]
  obtain t₂ : tbyte s₂.v = R := by
    rw [← t₁]; funext k; simp only [tbyte]
    rw [o₂.2 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(show NotTable (dq 1) by decide).ne _, (show NotTable (dq 2) by decide).ne _,
        (show NotTable (dq 3) by decide).ne _⟩)]
  -- S[j]
  obtain ⟨s₃, run₃, v₃, o₃⟩ := lookup_run (d := .v5) (t := .v6) (x := dq 0) (a := dq 1) (b := dq 2) (c := dq 3) J j₂ a₂ b₂ c₂ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain o₃' : Only stepRegs s s₃ := o₂'.trans (o₃.mono (by decide))
  obtain t₃ : tbyte s₃.v = R := by
    rw [← t₂]; funext k; simp only [tbyte]
    rw [o₃.2 _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(show NotTable .v5 by decide).ne _, (show NotTable .v6 by decide).ne _⟩)]
  obtain v₃' : s₃.v .v5 = bc (R J.toNat) := by rw [v₃, t₂]
  -- S[j] := S[i]
  obtain q₃ : Quarters s₃ J := by
    intro q hq
    rw [o₃.2 _ (by revert q; decide)]
    rcases (by omega_arith : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl
    · rw [j₂, show J ^^^ BitVec.ofNat 8 (64 * 0) = J from BitVec.xor_zero]
    · exact a₂
    · exact b₂
    · exact c₂
  obtain i₃ : s₃.v si = bc (R l) := by
    rw [o₃.2 _ (by decide), o₂.2 _ (by decide), v_setV_of_ne _ _ (by decide), hi]
  obtain ⟨s₄, run₄, t₄, o₄⟩ := writeN_run (consts_of_only hk o₃') q₃ i₃ (Nat.le_refl 16)
  obtain o₄' : Only stepRegs s s₄ := o₃'.trans (o₄.mono (by decide))
  obtain tb₄ : ∀ k < 256, tbyte s₄.v k = if k = J.toNat then R l else R k := by
    intro k hk
    rw [t₄ k hk, t₃]
    exact ite_iff ⟨fun h => h.2, fun h => ⟨by omega_arith, h⟩⟩ _ _
  obtain five₄ : s₄.v .v5 = bc (R J.toNat) := by rw [o₄.2 _ (by decide), v₃']
  obtain i₄ : s₄.v si = bc (R l) := by rw [o₄.2 _ (by decide), i₃]
  obtain j₄ : s₄.v (dq 0) = bc J := by rw [o₄.2 _ (by decide), o₃.2 _ (by decide), j₂]
  obtain n₄ : prga = true → s₄.v negBase = bc NB := fun h => by
    rw [o₄'.2 _ (by decide)]; exact hn h
  -- the output index
  obtain ⟨s₆, run₆, six₆, o₆⟩ : ∃ s₆, runBlock isa
      ((if prga then [.vop (.add .b16 .v6 si .v5), .vop (.add .b16 .v6 .v6 negBase)] else []) :
        List Instr) s₄ = some s₆ ∧
      (prga = true → s₆.v .v6 = bc (R l + R J.toNat + NB)) ∧ Only [.v6] s₄ s₆ := by
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
          n₄ rfl, add_bc]
  obtain t₆ : tbyte s₆.v = tbyte s₄.v := by
    funext k; simp only [tbyte]; rw [o₆.2 _ (by simp [(show NotTable .v6 by decide).ne _])]
  obtain five₆ : s₆.v .v5 = bc (R J.toNat) := by rw [o₆.2 _ (by decide), five₄]
  obtain j₆ : s₆.v (dq 0) = bc J := by rw [o₆.2 _ (by decide), j₄]
  -- the next S[i]
  let s₇ := s₆.setV si (VArr.b16.map2 (fun w _ _ => (s₆.v (treg ((l + 1) / 16))).extractLsb'
    (w * ((l + 1) % 16)) w) 0 0)
  obtain e₇ : exec (.vop (.dupE .b16 si (treg ((l + 1) / 16)) ((l + 1) % 16))) s₆ = some s₇ := by
    rw [exec_vop']
    simp only [reduceVOpEval, VArr.esize, show (l + 1) % 16 < 128 / 8 by omega_arith, ite_true]
    rfl
  obtain i₇ : s₇.v si = bc (tbyte s₄.v (l + 1)) := by
    rw [v_setV_self, dupE_bc, ← t₆]; rfl
  -- S[i] := S[j]
  let s₈ := s₇.setV (treg 0) (setLane (s₇.v (treg 0)) 8 l ((s₇.v .v5).extractLsb' (8 * 0) 8))
  obtain e₈ : exec (.vop (.insE .b16 (treg 0) l .v5 0)) s₇ = some s₈ := by
    rw [exec_vop']
    simp only [reduceVOpEval, VArr.esize, show l < 128 / 8 by omega_arith, show 0 < 128 / 8 by omega_arith,
      and_self, ite_true]
    rfl
  obtain five₇ : s₇.v .v5 = bc (R J.toNat) := by rw [v_setV_of_ne _ _ (by decide), five₆]
  obtain t₇ : tbyte s₇.v = tbyte s₄.v := by
    rw [← t₆]; funext k; simp only [tbyte]
    rw [v_setV_of_ne _ _ ((show NotTable si by decide).ne _)]
  obtain tb₈ : ∀ k < 256, tbyte s₈.v k = swapR R l J.toNat k := by
    intro k hk
    by_cases h0 : k / 16 = 0
    · have : tbyte s₈.v k = vbyte (setLane (s₇.v (treg 0)) 8 l ((s₇.v .v5).extractLsb' (8 * 0) 8))
          (k % 16) := by simp only [tbyte, h0, s₈, v_setV_self]
      rw [this, vbyte_setLane _ _ hl (by omega_arith), extract_byte, five₇, vbyte_bc _ (by decide)]
      obtain old : vbyte (s₇.v (treg 0)) (k % 16) = tbyte s₄.v k := by
        rw [← t₇]; simp only [tbyte, h0]
      rw [old, tb₄ k hk, swapR]
      exact ite_iff ⟨fun h => by omega_arith, fun h => by omega_arith⟩ _ _
    · have : tbyte s₈.v k = tbyte s₇.v k := by
        simp only [tbyte, s₈]
        rw [v_setV_of_ne _ _ (fun h => h0 (treg_inj _ (by omega_arith) _ (by decide) h))]
      rw [this, t₇, tb₄ k hk, swapR, ite_eq_right (show ¬ k = l by omega_arith)]
  refine ⟨s₈, ?_, tb₈, ?_, ?_, ?_, ?_⟩
  · rw [swapStep_eq, List.singleton_append, runBlock_cons, e₁, runStep_some]
    refine runBlock_cat_some run₂ (runBlock_cat_some run₃ (runBlock_cat_some run₄
      (runBlock_cat_some run₆ ?_)))
    rw [runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  · rw [v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide), j₆]
  · rw [v_setV_of_ne _ _ (by decide), i₇, tb₄ _ (by omega_arith), swapR,
      ite_eq_right (show ¬ (l + 1 = l) by omega_arith)]
  · intro hp
    rw [v_setV_of_ne _ _ (by decide), v_setV_of_ne _ _ (by decide), six₆ hp]
  · exact ((o₄'.trans (o₆.mono (by decide))).trans (Only.setV _ (by decide) _)).trans
      (Only.setV _ (by decide) _)

end VG.Proof.Rc4.AArch64

end

end


/-!
# The table registers as an RC4 context

The table registers hold the table `T` from the base `B` (`TableIn`): byte
`k` is `T[B + k]`. With `j - B` broadcast in `v0` and `-B` in `v14`
(`PrgaRegs`), one byte of the stream (`byte_ok`: a swap step and the
output) does what RC4's `step` does.
-/

@[expose] public section

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- `B` as a byte. -/
abbrev bB (B : Nat) : BitVec 8 := BitVec.ofNat 8 B

/-- The table registers hold `T` from the base `B`. -/
def TableIn (s : State) (B : Nat) (T : Table) : Prop :=
  ∀ k < 256, tbyte s.v k = T.getD (BitVec.ofNat 8 (B + k)).toNat 0

theorem ofNat_add_eq_iff {B k m : Nat} (hk : k < 256) (hm : m < 256) :
    BitVec.ofNat 8 (B + k) = BitVec.ofNat 8 (B + m) ↔ k = m := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega_using [hk, hm, this]
  · intro h; rw [h]

theorem ofNat_add_eq_j {B k : Nat} (hk : k < 256) (j : BitVec 8) :
    BitVec.ofNat 8 (B + k) = j ↔ k = (j - bB B).toNat := by
  have hj := j.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    omega_using [hk, this]
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega_using [h]

/-- The swap of positions `l` and `J` of the registers' table is RC4's swap
of `B + l` and `j`. -/
theorem swapR_eq (T : Table) {B l : Nat} (hl : l < 256) {R : Nat → BitVec 8}
    (hR : ∀ k < 256, R k = T.getD (BitVec.ofNat 8 (B + k)).toNat 0) (j : BitVec 8) {k : Nat}
    (hk : k < 256) :
    swapR R l (j - bB B).toNat k = (swap T (BitVec.ofNat 8 (B + l)) j).getD (BitVec.ofNat 8 (B + k)).toNat 0 := by
  obtain hJ := (j - bB B).isLt
  obtain hJj : BitVec.ofNat 8 (B + (j - bB B).toNat) = j := (ofNat_add_eq_j hJ j).mpr rfl
  rw [swap_get]
  simp only [swapR, ofNat_add_eq_j hk j, ofNat_add_eq_iff hk hl]
  by_cases h1 : k = l
  · subst h1
    by_cases h2 : k = (j - bB B).toNat
    · simp only [ite_true, h2, hR _ hJ]
    · simp only [ite_true, h2, ite_false, hR _ hJ, hJj]
  · by_cases h2 : k = (j - bB B).toNat
    · have h1' : ¬ (j - bB B).toNat = l := fun h => h1 (h2.trans h)
      simp only [h2, h1', ite_true, ite_false, hR _ hl]
    · simp only [h1, h2, ite_false, hR _ hk]

/-- The PRGA's registers hold the context `c` from the base `B`: its table,
`j - B`, and `-B`. -/
structure PrgaRegs (s : State) (B : Nat) (c : Context) : Prop where
  table : TableIn s B c.table
  j : s.v (dq 0) = bc (c.j - bB B)
  nb : s.v negBase = bc (0 - bB B)
  consts : Consts s

theorem byte_add_sub (cj a B : BitVec 8) : cj - B + a = cj + a - B := by bv_omega

theorem idx_out (a b : BitVec 8) (B : Nat) :
    BitVec.ofNat 8 (B + (a + b + (0 - bB B)).toNat) = a + b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_sub,
    show (0 : BitVec 8).toNat = 0 from rfl]
  have := a.isLt; have := b.isLt
  omega_using []

/-- One byte of the stream, at lane `l` of the group whose base is `B`. -/
theorem byte_ok {l : Nat} (hl : l < 16) {B : Nat} {c : Context} {s : State} (h : PrgaRegs s B c)
    (hi : c.i + 1 = BitVec.ofNat 8 (B + l)) (hsi : s.v si = bc (tbyte s.v l))
    (hd : InRegions s.wr (s.gpr .x1) 1) :
    WP isa (.block (swapStep true l ++ output)) s fun t =>
      PrgaRegs t B (step c).1 ∧ t.v si = bc (tbyte t.v (l + 1)) ∧
      t.mem = s.mem.write (s.gpr .x1) 1 (s.mem (s.gpr .x1) ^^^ (step c).2) ∧
      t.gpr .x1 = s.gpr .x1 + 1 ∧ t.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x6 → r ≠ .x7 → t.gpr r = s.gpr r) ∧
      (∀ r, r ∉ stepRegs → t.v r = s.v r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  let T := c.table
  let i := c.i + 1
  let a := T.getD i.toNat 0
  let j := c.j + a
  let b := T.getD j.toNat 0
  have hR : ∀ k < 256, tbyte s.v k = T.getD (BitVec.ofNat 8 (B + k)).toNat 0 := h.table
  obtain ha : tbyte s.v l = a := by rw [hR l (by omega_using [hl])]; simp only [a, i, hi]
  obtain hJ : c.j - bB B + tbyte s.v l = j - bB B := by rw [ha, byte_add_sub]
  obtain ⟨s₁, run₁, t₁, j₁, i₁, o6₁, o₁⟩ := swapStep_run true hl h.consts h.j hsi fun _ => h.nb
  rw [hJ] at t₁ j₁ i₁ o6₁
  obtain tab₁ : ∀ k < 256, tbyte s₁.v k = (swap T i j).getD (BitVec.ofNat 8 (B + k)).toNat 0 := by
    intro k hk; rw [t₁ k hk, swapR_eq T (by omega_using [hl]) hR j hk, ← hi]
  obtain hb : tbyte s.v (j - bB B).toNat = b := by
    rw [hR _ (j - bB B).isLt, (ofNat_add_eq_j (j - bB B).isLt j).mpr rfl]
  obtain six₁ : s₁.v .v6 = bc (a + b + (0 - bB B)) := by rw [o6₁ rfl, ha, hb]
  obtain k₁ : Consts s₁ := consts_of_only h.consts o₁
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain hd₁ : InRegions s₁.wr (s₁.gpr .x1) 1 := by rw [o₁.wr, o₁.gpr]; exact hd
  refine WP.mono (output_ok k₁ six₁ hd₁) fun t ⟨m, x1, x2, g, v, rd, wr, sp⟩ => ?_
  obtain tt : tbyte t.v = tbyte s₁.v := by
    funext k; simp only [tbyte]; rw [v _ (by
      simp only [outRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(show NotTable .v1 by decide).ne _, (show NotTable .v2 by decide).ne _,
        (show NotTable .v3 by decide).ne _, (show NotTable .v7 by decide).ne _⟩)]
  obtain step_c : step c = ({ table := swap T i j, i, j }, (swap T i j).getD (a + b).toNat 0) :=
    step_eq c
  rw [step_c]
  refine ⟨⟨fun k hk => by rw [tt, tab₁ k hk], by rw [v _ (by decide), j₁],
      by rw [v _ (by decide), o₁.2 _ (by decide), h.nb], k₁.congr fun r hr => v r (by
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)⟩,
    by rw [v _ (by decide), i₁, tt, t₁ _ (by omega_using [hl])], ?_, by rw [x1, o₁.gpr], by rw [x2, o₁.gpr],
    fun r a b c d => by rw [g r a b c d, o₁.gpr], fun r hr => ?_, by rw [rd, o₁.rd],
    by rw [wr, o₁.wr], by rw [sp, o₁.sp]⟩
  · rw [m, o₁.mem, o₁.gpr, tab₁ _ (by exact (a + b + (0 - bB B)).isLt), idx_out]
  · have hr' : r ∉ outRegs := fun h' => hr (by
      simp only [outRegs, List.mem_cons, List.not_mem_nil, or_false] at h'
      rcases h' with rfl | rfl | rfl | rfl <;> decide)
    rw [v r hr', o₁.2 r hr]

end VG.Proof.Rc4.AArch64
