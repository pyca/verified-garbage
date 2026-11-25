module

public import VerifiedGarbage.Impl.Aes.AArch64.Neon.Blocks
public import VerifiedGarbage.Proof.Aes.Sbox0
public import VerifiedGarbage.Proof.Framework.AArch64.StraightQ
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The layers of AES bitsliced in AdvSIMD registers, on AArch64

`NRel Q S`: the slices `Q` hold the eight states `S`, bit `j` of byte `n` of
state `k` at bit `8 n + k` of slice `j`. The transposes are evaluated byte
by byte (`ByteEval`), the S-boxes on truth tables (`StraightV`), and the
permutations and MixColumns on whole vectors of atoms (`StraightQ`). Each
layer's theorem says what it does to `NRel`, or to the blocks, and that it
changes only vector registers, `x6` and the first slot of the scratch
buffer (`Keeps`).
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64.Neon

open VG VG.AArch64 VG.Bitslice VG.Impl.Aes.AArch64.Neon VG.Proof.Aes
open VG.AArch64.StraightV (vAddr exec_vop_some addr_slot read16_readW)

/-! ## Byte by byte -/

namespace ByteEval

/-- The abstract value of a vector register, the same for each of its
bytes, and the byte at the bottom of `x6`. -/
structure Env (α : Type) where
  reg : VReg → Option α
  x6 : Option (BitVec 8) := none

variable {α : Type}

def Env.setReg (e : Env α) (d : VReg) (v : α) : Env α :=
  { e with reg := fun r => if r = d then some v else e.reg r }

section
variable (D : Dom α 8)

/-- `a ∧ m`, for a constant `m`. -/
def andC (m : BitVec 8) (a : α) : Option α := (D.const m).bind (D.and a)

/-- `a <<< n`. -/
def shl (n : Nat) (a : α) : Option α := (andC D (BitVec.allOnes 8 >>> n) a).bind (D.ror (8 - n))

/-- `a`, but `n` where `m` is 1. -/
def ins (a n m : α) : Option α :=
  (D.xor a n).bind fun t => (D.and t m).bind fun t => D.xor a t

def step (e : Env α) : Instr → Option (Env α)
  | .vop (.mov d n) => (e.reg n).map (e.setReg d)
  | .vop (.shift .ushr .b16 d n sh) =>
    if 1 ≤ sh ∧ sh ≤ 7 then (e.reg n).bind fun a => (D.shr sh a).map (e.setReg d) else none
  | .vop (.shift .shl .b16 d n sh) =>
    if 1 ≤ sh ∧ sh ≤ 7 then (e.reg n).bind fun a => (shl D sh a).map (e.setReg d) else none
  | .vop (.shift .sli .b16 d n sh) =>
    if 1 ≤ sh ∧ sh ≤ 7 then
      match e.reg d, e.reg n with
      | some a, some b => (andC D (~~~(BitVec.allOnes 8 <<< sh)) a).bind fun a =>
          (shl D sh b).bind fun b => (D.xor a b).map (e.setReg d)
      | _, _ => none
    else none
  | .vop (.shift .sri .b16 d n sh) =>
    if 1 ≤ sh ∧ sh ≤ 7 then
      match e.reg d, e.reg n with
      | some a, some b => (andC D (~~~(BitVec.allOnes 8 >>> sh)) a).bind fun a =>
          (D.shr sh b).bind fun b => (D.xor a b).map (e.setReg d)
      | _, _ => none
    else none
  | .vop (.bsel .bit d n m) =>
    match e.reg d, e.reg n, e.reg m with
    | some a, some b, some c => (ins D a b c).map (e.setReg d)
    | _, _, _ => none
  | .vop (.bsel .bif d n m) =>
    match e.reg d, e.reg n, e.reg m with
    | some a, some b, some c =>
      ((D.const (BitVec.allOnes 8)).bind (D.xor c)).bind fun c => (ins D a b c).map (e.setReg d)
    | _, _, _ => none
  | .movz .w d imm hw =>
    if d = .x6 ∧ hw = 0 then some { e with x6 := some (imm.setWidth 8) } else none
  | .vop (.dup .b16 d n) =>
    if n = .x6 then e.x6.bind fun v => (D.const v).map (e.setReg d) else none
  | _ => none

def eval : List Instr → Env α → Option (Env α)
  | [], e => some e
  | i :: is, e => (step D e i).bind (eval is)

def check (is : List Instr) (e : Env α) (post : Env α → Bool) : Bool :=
  match eval D is e with
  | some e' => post e'
  | none => false

theorem of_check {is : List Instr} {e : Env α} {post : Env α → Bool}
    (h : check D is e post = true) : ∃ e', eval D is e = some e' ∧ post e' = true := by
  unfold check at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · cases h

end

/-! ### Bytes -/

theorem vbyte_and (x y : BitVec 128) (e : Nat) : vbyte (x &&& y) e = vbyte x e &&& vbyte y e :=
  StraightQ.vbyte_and x y e

theorem vbyte_not (x : BitVec 128) {e : Nat} (he : e < 16) : vbyte (~~~x) e = ~~~vbyte x e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
    show 8 * e + i < 128 by omega_using [he, hi]]

theorem shl_eq (x : BitVec 8) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 7) :
    (x &&& BitVec.allOnes 8 >>> n).rotateRight (8 - n) = x <<< n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_rotateRight_of_lt (by omega_using [h1])]
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes]
  by_cases h : i < 8 - (8 - n)
  · simp only [h, ite_true]
    simp [show i < n by omega_using [h], hi]
    omega_using []
  · simp only [h, ite_false]
    simp only [show ¬ i < n by omega_using [h2, h], decide_true, hi, Bool.true_and,
      show i - (8 - (8 - n)) = i - n by omega_using [h2]]
    simp [show n + (i - n) < 8 by omega_using [h2, hi]]

theorem sli_eq (a b : BitVec 8) (n : Nat) :
    (a &&& ~~~(BitVec.allOnes 8 <<< n)) ^^^ (b <<< n) = (a &&& ~~~(BitVec.allOnes 8 <<< n)) ||| (b <<< n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
  by_cases h : i < n
  · simp [h]
  · simp [h, show i - n < 8 by omega_using [hi]]

theorem sri_eq (a b : BitVec 8) (n : Nat) :
    (a &&& ~~~(BitVec.allOnes 8 >>> n)) ^^^ (b >>> n) = (a &&& ~~~(BitVec.allOnes 8 >>> n)) ||| (b >>> n) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
  by_cases h : n + i < 8
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge b (n + i) (by omega_using [h])]

/-! ### The run -/

structure Rel (R : Nat → α → BitVec 8 → Prop) (e : Env α) (s : State) : Prop where
  reg : ∀ r a, e.reg r = some a → ∀ i < 16, R i a (vbyte (s.v r) i)
  x6 : ∀ v, e.x6 = some v → (s.gpr .x6).setWidth 8 = v

structure Post (R : Nat → α → BitVec 8 → Prop) (e' : Env α) (s s' : State) (writes : VReg → Prop) :
    Prop where
  rel : Rel R e' s'
  other : ∀ r, ¬ writes r → s'.v r = s.v r
  gpr : ∀ r, r ≠ .x6 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

variable {D : Dom α 8} {R : Nat → α → BitVec 8 → Prop}

theorem post_setV {e : Env α} {s : State} (hrel : Rel R e s) {d : VReg} {a : α} {v : BitVec 128}
    (hv : ∀ i < 16, R i a (vbyte v i)) : Post R (e.setReg d a) s (s.setV d v) (· = d) where
  rel := {
    reg := fun r b h i hi => by
      simp only [Env.setReg] at h
      simp only [State.setV]
      split at h
      · rename_i hr; cases h; simp only [hr, ite_true]; exact hv i hi
      · rename_i hr; simp only [hr, ite_false]; exact hrel.reg r b h i hi
    x6 := fun w h => hrel.x6 w h }
  other r hr := by simp [State.setV, hr]
  gpr _ _ := rfl
  mem := rfl
  rd := rfl
  wr := rfl
  sp := rfl

/-- A vector instruction, as `step` evaluates it. -/
theorem vop_ok {e : Env α} {s : State} (hrel : Rel R e s) {op : VOp} {d : VReg} {a : α}
    {v : BitVec 128} (hop : op.eval s = some (d, v)) (hd : op.dst = d)
    (hv : ∀ i < 16, R i a (vbyte v i)) :
    ∃ s', exec (.vop op) s = some s' ∧
      Post R (e.setReg d a) s s' (fun r => vdstOf (.vop op) = some r) := by
  refine ⟨_, exec_vop_some hop, ?_⟩
  have := post_setV (d := d) hrel hv
  exact { this with other := fun r hr => this.other r fun hw => hr (by simp [vdstOf, hd, hw]) }

theorem andC_sound (hD : ∀ i < 16, D.Sound (R i)) {m : BitVec 8} {a c : α} {x : BitVec 8} {i : Nat}
    (hi : i < 16) (ha : R i a x) (h : andC D m a = some c) : R i c (x &&& m) := by
  simp only [andC, Option.bind_eq_some_iff] at h
  obtain ⟨k, hk, h⟩ := h
  exact (hD i hi).and ha ((hD i hi).const hk) h

theorem shl_sound (hD : ∀ i < 16, D.Sound (R i)) {n : Nat} {a c : α} {x : BitVec 8} {i : Nat}
    (h1 : 1 ≤ n) (h2 : n ≤ 7) (hi : i < 16) (ha : R i a x) (h : shl D n a = some c) :
    R i c (x <<< n) := by
  simp only [shl, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, h⟩ := h
  rw [← shl_eq x h1 h2]
  exact (hD i hi).ror (andC_sound hD hi ha ht) h

theorem ins_sound (hD : ∀ i < 16, D.Sound (R i)) {a n m c : α} {x y z : BitVec 8} {i : Nat}
    (hi : i < 16) (ha : R i a x) (hn : R i n y) (hm : R i m z) (h : ins D a n m = some c) :
    R i c (x ^^^ ((x ^^^ y) &&& z)) := by
  simp only [ins, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, u, hu, h⟩ := h
  exact (hD i hi).xor ha ((hD i hi).and ((hD i hi).xor ha hn ht) hm hu) h

theorem step_ok (hD : ∀ i < 16, D.Sound (R i)) {e e' : Env α} {s : State} (hrel : Rel R e s)
    {i : Instr} (h : step D e i = some e') :
    ∃ s', exec i s = some s' ∧ Post R e' s s' (fun r => vdstOf i = some r) := by
  cases i with
  | vop op =>
    cases op with
    | mov d n =>
      simp only [step] at h
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      exact vop_ok hrel rfl rfl (hrel.reg n a ha)
    | dup a d n =>
      cases a <;> simp only [step] at h <;> try cases h
      split at h
      · rename_i hn
        subst hn
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨v, hv, h⟩ := h
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        refine vop_ok (v := Tbl.bc ((s.gpr .x6).setWidth 8)) hrel rfl rfl fun i hi => ?_
        rw [Tbl.vbyte_bc _ hi]
        have := (hD i hi).const hc
        rw [← hrel.x6 v hv] at this
        exact this
      · cases h
    | shift op a d n sh =>
      cases a <;> cases op <;> simp only [step] at h <;> try cases h
      all_goals (split at h <;> try cases h)
      · rename_i hsh
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨a, ha, h⟩ := h
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        refine vop_ok hrel (show (VOp.shift .shl .b16 d n sh).eval s = some (d, VArr.b16.map2
            (fun w x y => VShiftOp.eval .shl sh w x y) (s.v d) (s.v n)) from
          ite_eq_left (by
            simp only [VShiftOp.ok, decide_eq_true_eq, show VArr.b16.esize = 8 from rfl]
            omega_using [hsh])) rfl fun i hi => ?_
        rw [VArr.map2, vbyte_ofVBytes _ hi]
        exact shl_sound hD hsh.1 hsh.2 hi (hrel.reg n a ha i hi) hc
      · rename_i hsh
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨a, ha, h⟩ := h
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        refine vop_ok hrel (show (VOp.shift .ushr .b16 d n sh).eval s = some (d, VArr.b16.map2
            (fun w x y => VShiftOp.eval .ushr sh w x y) (s.v d) (s.v n)) from
          ite_eq_left (by
            simp only [VShiftOp.ok, decide_eq_true_eq, Bool.and_eq_true, show VArr.b16.esize = 8 from rfl]
            omega_using [hsh])) rfl fun i hi => ?_
        rw [VArr.map2, vbyte_ofVBytes _ hi]
        exact (hD i hi).shr (hrel.reg n a ha i hi) hc
      · rename_i hsh
        split at h
        · rename_i a b ha hb
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨t, ht, u, hu, h⟩ := h
          obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
          refine vop_ok hrel (show (VOp.shift .sri .b16 d n sh).eval s = some (d, VArr.b16.map2
            (fun w x y => VShiftOp.eval .sri sh w x y) (s.v d) (s.v n)) from
          ite_eq_left (by
            simp only [VShiftOp.ok, decide_eq_true_eq, Bool.and_eq_true, show VArr.b16.esize = 8 from rfl]
            omega_using [hsh])) rfl fun i hi => ?_
          rw [VArr.map2, vbyte_ofVBytes _ hi]
          simp only [VShiftOp.eval]
          rw [← sri_eq]
          exact (hD i hi).xor (andC_sound hD hi (hrel.reg d a ha i hi) ht)
            ((hD i hi).shr (hrel.reg n b hb i hi) hu) hc
        · cases h
      · rename_i hsh
        split at h
        · rename_i a b ha hb
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨t, ht, u, hu, h⟩ := h
          obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
          refine vop_ok hrel (show (VOp.shift .sli .b16 d n sh).eval s = some (d, VArr.b16.map2
            (fun w x y => VShiftOp.eval .sli sh w x y) (s.v d) (s.v n)) from
          ite_eq_left (by
            simp only [VShiftOp.ok, decide_eq_true_eq, show VArr.b16.esize = 8 from rfl]
            omega_using [hsh])) rfl fun i hi => ?_
          rw [VArr.map2, vbyte_ofVBytes _ hi]
          simp only [VShiftOp.eval]
          rw [← sli_eq]
          exact (hD i hi).xor (andC_sound hD hi (hrel.reg d a ha i hi) ht)
            (shl_sound hD hsh.1 hsh.2 hi (hrel.reg n b hb i hi) hu) hc
        · cases h
    | bsel op d n m =>
      cases op <;> simp only [step] at h <;> try cases h
      · split at h
        · rename_i a b c ha hb hc
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
          refine vop_ok hrel rfl rfl fun i hi => ?_
          simp only [VSelOp.eval, StraightQ.vbyte_xor, vbyte_and]
          exact ins_sound hD hi (hrel.reg d a ha i hi) (hrel.reg n b hb i hi) (hrel.reg m c hc i hi) ht
        · cases h
      · split at h
        · rename_i a b c ha hb hc
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨u, ⟨k, hk, hu⟩, h⟩ := h
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
          refine vop_ok hrel rfl rfl fun i hi => ?_
          simp only [VSelOp.eval, StraightQ.vbyte_xor, vbyte_and, vbyte_not _ hi]
          rw [← BitVec.xor_allOnes]
          exact ins_sound hD hi (hrel.reg d a ha i hi) (hrel.reg n b hb i hi)
            ((hD i hi).xor (hrel.reg m c hc i hi) ((hD i hi).const hk) hu) ht
        · cases h
    | _ => simp [step] at h
  | movz sz d imm hw =>
    cases sz <;> simp only [step] at h <;> try cases h
    split at h
    · rename_i hd
      obtain ⟨rfl, rfl⟩ := hd
      cases h
      refine ⟨_, exec_movz_w, ⟨fun r a h i hi => hrel.reg r a h i hi, fun v hv => ?_⟩, fun _ _ => rfl,
        fun r hr => by simp [State.write, hr], rfl, rfl, rfl, rfl⟩
      simp only [Option.some.injEq] at hv
      subst hv
      simp only [State.write, ite_true, Size.bits]
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp only [BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
        show j < 64 by omega_using [hj], show j < 32 by omega_using [hj]]
    · cases h
  | _ => simp [step] at h

theorem run (hD : ∀ i < 16, D.Sound (R i)) {is : List Instr} {e e' : Env α} {s : State}
    (hrel : Rel R e s) (h : eval D is e = some e') :
    ∃ s', runBlock isa is s = some s' ∧
      Post R e' s s' (fun r => (is.all fun i => vdstOf i != some r) = false) := by
  induction is generalizing e s with
  | nil =>
    cases h
    exact ⟨s, runBlock_nil, hrel, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons i is ih =>
    simp only [eval, Option.bind_eq_some_iff] at h
    obtain ⟨e₁, h₁, h₂⟩ := h
    obtain ⟨s₁, hs₁, p₁⟩ := step_ok hD hrel h₁
    obtain ⟨s', hs', p⟩ := ih p₁.rel h₂
    refine ⟨s', by rw [runBlock_cons, hs₁, runStep_some]; exact hs', p.rel, fun r hr => ?_,
      fun r hr => (p.gpr r hr).trans (p₁.gpr r hr), p.mem.trans p₁.mem, p.rd.trans p₁.rd,
      p.wr.trans p₁.wr, p.sp.trans p₁.sp⟩
    simp only [List.all_cons, Bool.and_eq_false_iff, bne_eq_false_iff_eq, not_or] at hr
    exact (p.other r hr.2).trans (p₁.other r hr.1)

end ByteEval

/-! ## What a layer keeps -/

/-- The scratch buffer, of 2048 bytes or more, is writable. -/
def ScrIn (b : Addr) (wr : List Region) : Prop :=
  ∃ L, 2048 ≤ L ∧ L < 2 ^ 64 ∧ (⟨b, L⟩ : Region) ∈ wr

theorem ScrIn.of_mem {b : Addr} {wr : List Region} (h : (⟨b, 2048⟩ : Region) ∈ wr) : ScrIn b wr :=
  ⟨2048, by decide, by decide, h⟩

structure Keeps (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x6 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [⟨s.gpr sb, 16⟩] s.mem s'.mem

theorem Keeps.trans {s₁ s₂ s₃ : State} (h : Keeps s₁ s₂) (h' : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.rd.trans h.rd, h'.wr.trans h.wr,
    h'.sp.trans h.sp, h.frame.trans (by rw [← h.gpr sb (by decide)]; exact h'.frame)⟩

/-- A block that changes only vector registers. -/
theorem Keeps.of_v {s s' : State} (h : s' = { s with v := s'.v }) : Keeps s s' := by
  rw [h]; exact ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

/-! ## Blocks and slices -/

/-- The words `Q` hold the states `S`, a block each. -/
def InRel (Q : Nat → BitVec 128) (S : Nat → Spec.Aes.State) : Prop :=
  ∀ b < 8, ∀ i < 16, ∀ j < 8, (Q b).getLsbD (8 * i + j) = ((S b).getD i 0).getLsbD j

/-- The slices `Q` hold the states `S`. -/
def NRel (Q : Nat → BitVec 128) (S : Nat → Spec.Aes.State) : Prop :=
  ∀ j < 8, ∀ n < 16, ∀ k < 8, (Q j).getLsbD (8 * n + k) = ((S k).getD n 0).getLsbD j

theorem NRel.congrW {Q Q' : Nat → BitVec 128} {S : Nat → Spec.Aes.State} (h : NRel Q S)
    (hQ : ∀ j < 8, Q j = Q' j) : NRel Q' S :=
  fun j hj n hn k hk => by rw [← hQ j hj]; exact h j hj n hn k hk

theorem NRel.congr {Q : Nat → BitVec 128} {S S' : Nat → Spec.Aes.State} (h : NRel Q S)
    (hS : ∀ k < 8, S k = S' k) : NRel Q S' :=
  fun j hj n hn k hk => by rw [← hS k hk]; exact h j hj n hn k hk

theorem NRel.byte {Q : Nat → BitVec 128} {S : Nat → Spec.Aes.State} (h : NRel Q S) {n k : Nat}
    (hn : n < 16) (hk : k < 8) : bsByte Q (8 * n + k) = (S k).getD n 0 :=
  byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, h j hj n hn k hk]

/-! ## The transposes -/

def orthoEnv (P : Nat → VReg) : ByteEval.Env (Nat × Nat) :=
  { reg := fun r => ((List.range 8).find? (fun k => P k == r)).map (inWordW 8) }

/-- Bit `b` of slice `j`'s byte is bit `j` of block `b`'s. -/
def orthoPost (P : Nat → VReg) (e : ByteEval.Env (Nat × Nat)) : Bool :=
  (List.range 8).all fun j => outOkW 8 6 (e.reg (P j)) fun b => [8 * b + j]

theorem orthoA_check : ByteEval.check (lanes 8 6) (ortho A) (orthoEnv A) (orthoPost A) = true := by
  decide +kernel
theorem orthoB_check : ByteEval.check (lanes 8 6) (ortho B) (orthoEnv B) (orthoPost B) = true := by
  decide +kernel

theorem ortho_ok {P : Nat → VReg}
    (hchk : ByteEval.check (lanes 8 6) (ortho P) (orthoEnv P) (orthoPost P) = true) (s : State) :
    ∃ s', runBlock isa (ortho P) s = some s' ∧
      (∀ j < 8, ∀ i < 16, ∀ b < 8,
        (s'.v (P j)).getLsbD (8 * i + b) = (s.v (P b)).getLsbD (8 * i + j)) ∧ Keeps s s' := by
  obtain ⟨e', he, hpost⟩ := ByteEval.of_check _ hchk
  let W : Nat → Nat → BitVec 8 := fun i k => vbyte (s.v (P k)) i
  obtain ⟨s', hs', p⟩ := ByteEval.run (R := fun i => LaneRel 6 (assign (W i) (2 ^ 6)))
    (fun i _ => lanes_sound) (s := s) ⟨fun r a h i hi => by
      simp only [orthoEnv, Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      have hr := List.find?_some hk
      have hk8 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
      simp only [beq_iff_eq] at hr
      subst hr
      exact inWordW_rel (W i) (by omega_using [hk8]), fun v h => by cases h⟩ he
  refine ⟨s', hs', fun j hj i hi b hb => ?_, p.gpr, p.rd, p.wr, p.sp, p.mem ▸ Frame.refl _ _⟩
  obtain ⟨h1, h2⟩ := outOkW_spec (List.all_eq_true.mp hpost j (List.mem_range.mpr hj))
  have := outWordW_rel_of_lt h2 (p.rel.reg (P j) _ h1 i hi) b hb
  rw [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hj] at this
  simpa only [W, vbyte, BitVec.getLsbD_extractLsb', hb, hj, decide_true, Bool.true_and] using this

theorem nrel_of_in {Q Q' : Nat → BitVec 128} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ i < 16, ∀ b < 8, (Q' j).getLsbD (8 * i + b) = (Q b).getLsbD (8 * i + j))
    (hin : InRel Q S) : NRel Q' S :=
  fun j hj n hn k hk => by rw [h j hj n hn k hk, hin k hk n hn j hj]

theorem in_of_nrel {Q Q' : Nat → BitVec 128} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ i < 16, ∀ b < 8, (Q' j).getLsbD (8 * i + b) = (Q b).getLsbD (8 * i + j))
    (hbs : NRel Q S) : InRel Q' S :=
  fun b hb i hi j hj => by rw [h b hb i hi j hj, hbs j hj i hi b hb]

/-! ## The S-boxes -/

def sCfg : StraightV.Cfg := { base := sb, slots := 1 }

def sEnv : StraightV.Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => A k == r)).map sbIn, slot := fun _ => none }

def sPost (T : List Nat) (e : StraightV.Env Nat) : Bool :=
  (List.range 8).all fun j => e.reg (B j) == some (T.getD j 0)

theorem sbox_check : StraightV.check (table 64 256) sCfg subBytes sEnv (sPost sbox0T) = true := by
  decide +kernel
theorem invSbox_check :
    StraightV.check (table 64 256) sCfg invSubBytes sEnv (sPost invSbox0T) = true := by
  decide +kernel

theorem sCfg_ok {s : State} (h : ScrIn (s.gpr sb) s.wr) : StraightV.Ok sCfg s := by
  obtain ⟨L, hL, hL', hm⟩ := h
  refine ⟨fun k hk => ⟨_, hm, ?_⟩, by decide⟩
  simp only [sCfg] at hk ⊢
  exact Offset.contains_base _ (by omega_using [hk, hL]) (by omega_using [hk])

/-- A circuit that the check finds to be `g`, on every byte. -/
theorem circuit_ok {is : List Instr} {T : List Nat} {g : Byte → Byte}
    (hchk : StraightV.check (table 64 256) sCfg is sEnv (sPost T) = true)
    (hT : ∀ c < 256, ∀ j < 8, (T.getD j 0).testBit c = (g (BitVec.ofNat 8 c)).getLsbD j)
    (hx6 : is.all (fun i => (dsts i).isEmpty) = true)
    {s : State} (hscr : ScrIn (s.gpr sb) s.wr) {S : Nat → Spec.Aes.State}
    (hS : NRel (fun j => s.v (A j)) S) :
    ∃ s', runBlock isa is s = some s' ∧ NRel (fun j => s'.v (B j)) (fun k => (S k).map g) ∧
      Keeps s s' := by
  obtain ⟨e', he, hpost⟩ := StraightV.of_check _ _ hchk
  have hout : ∀ j < 8, e'.reg (B j) = some (T.getD j 0) := fun j hj => by
    simpa using List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
  let c : Nat → Byte := fun p => bsByte (fun j => s.v (A j)) p
  -- The run, on the input formed by the bits `p` of the slices.
  have key : ∀ t < 64, ∃ s', runBlock isa is s = some s' ∧
      StraightV.Post (fun q a (x : BitVec 64) => TableRel t (c (64 * q + t)).toNat a x) sCfg e' s s'
        (fun r => (is.all fun i => vdstOf i != some r) = false)
        (fun r => (is.all fun i => !clobbers i r) = false) := fun t ht => by
    refine StraightV.run (fun q _ => table_sound ht (c (64 * q + t)).isLt) (sCfg_ok hscr)
      ⟨fun r a h q hq => ?_, (fun _ _ _ h => by cases h), fun _ _ h => by cases h⟩ he
    simp only [sEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hr := List.find?_some hk
    have hk8 := List.mem_range.mp (List.mem_of_find?_eq_some hk)
    simp only [beq_iff_eq] at hr
    subst hr
    simp only [TableRel, sbIn, testBit_tableOf, (c (64 * q + t)).isLt, decide_true, Bool.true_and,
      BitVec.testBit_toNat, StraightV.getLsbD_vdword _ ht]
    exact getLsbD_bsByte _ _ hk8
  obtain ⟨s', hs', p₀⟩ := key 0 (by decide)
  refine ⟨s', hs', fun j hj n hn k hk => ?_, fun r _ => p₀.gpr r ?_, p₀.rd, p₀.wr, p₀.sp, p₀.frame⟩
  · let p := 8 * n + k
    obtain ⟨s'', hs'', p₁⟩ := key (p % 64) (Nat.mod_lt _ (by decide))
    obtain rfl : s'' = s' := by rw [hs''] at hs'; exact Option.some.inj hs'
    have hp : 64 * (p / 64) + p % 64 = p := Nat.div_add_mod p 64
    have h := p₁.rel.reg (B j) _ (hout j hj) (p / 64) (by omega_using [hn, hk])
    simp only [TableRel, StraightV.getLsbD_vdword _ (Nat.mod_lt p (show 0 < 64 by decide)), hp] at h
    rw [getD_map g _ hn, ← hS.byte hn hk]
    show (s''.v (B j)).getLsbD p = _
    rw [← h, hT _ (c p).isLt j hj, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [Bool.not_eq_false, List.all_eq_true]
    intro i hi
    rw [clobbers_eq_false_of_isEmpty (List.all_eq_true.mp hx6 i hi)]; rfl

theorem sbox_ok {s : State} (hscr : ScrIn (s.gpr sb) s.wr) {S : Nat → Spec.Aes.State}
    (hS : NRel (fun j => s.v (A j)) S) :
    ∃ s', runBlock isa subBytes s = some s' ∧
      NRel (fun j => s'.v (B j)) (fun k => (S k).map sbox0) ∧ Keeps s s' :=
  circuit_ok sbox_check (fun _ hc _ hj => sbox0T_bit hc hj) (by decide +kernel) hscr hS

theorem invSbox_ok {s : State} (hscr : ScrIn (s.gpr sb) s.wr) {S : Nat → Spec.Aes.State}
    (hS : NRel (fun j => s.v (A j)) S) :
    ∃ s', runBlock isa invSubBytes s = some s' ∧
      NRel (fun j => s'.v (B j)) (fun k => (S k).map invSbox0) ∧ Keeps s s' :=
  circuit_ok invSbox_check (fun _ hc _ hj => invSbox0T_bit hc hj) (by decide +kernel) hscr hS

/-! ## Permutations and columns -/

def insOf (P : Nat → VReg) : List (VReg × Nat) := (List.range 8).map fun j => (P j, j)

def outsOf (P : Nat → VReg) (T : Nat → Nat → List (Nat × Nat)) : List (VReg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (P j, fun p => (T j p).map fun t => 128 * t.1 + t.2)

/-- Nothing external is read. -/
def qCfg : StraightQ.Cfg := { ext := sb, exts := 0 }

/-- A linear block on the slices `P`, leaving them in `P'`, with indices in `cs`. -/
theorem lin_ok {is : List Instr} {P P' : Nat → VReg} {cs : List (VReg × BitVec 128)}
    {T : Nat → Nat → List (Nat × Nat)}
    (hchk : StraightQ.check (lanes 128 10) qCfg (StraightQ.linExt 8) is
      (StraightQ.linEnv (insOf P) cs) (StraightQ.linPost 10 (outsOf P' T)) = true)
    (hT : ∀ j < 8, ∀ p < 128, ∀ t ∈ T j p, t.2 < 128) {s : State}
    (hcs : ∀ r v, (r, v) ∈ cs → s.v r = v) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 128, (s'.v (P' j)).getLsbD p = termsXor (fun k => s.v (P k)) (T j p)) ∧
      Keeps s s' := by
  obtain ⟨s', hs', h, hv, _⟩ := StraightQ.linear_ok hchk (s := s)
    (fun k hk => absurd hk (Nat.not_lt_zero k)) (fun k => s.v (P k))
    (fun r i hri => by
      simp only [insOf, List.mem_map, List.mem_range] at hri
      obtain ⟨k, hk, he⟩ := hri
      cases he
      exact ⟨by omega_using [hk], rfl⟩) hcs (fun k hk => absurd hk (Nat.not_lt_zero k))
  refine ⟨s', hs', fun j hj p hp => ?_, .of_v hv⟩
  rw [h (P' j) _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) p hp]
  exact xorBits_map _ _ (hT j hj p hp)

/-- The bytes permuted: byte `n` is byte `f n`. -/
def permT (f : Nat → Nat) (j p : Nat) : List (Nat × Nat) := [(j, 8 * f (p / 8) + p % 8)]

/-- The product of the columns by the coefficients `cs`, of bytes permuted by `f`. -/
def mixT (f : Nat → Nat) (cs : List Nat) (j p : Nat) : List (Nat × Nat) :=
  (List.range 4).flatMap fun i =>
    (mulTerms (cs.getD i 0) j).map fun b => (b, 8 * f (down (p / 8) i) + p % 8)

theorem srSrc_lt : ∀ n < 16, srSrc n < 16 := by decide
theorem isrSrc_lt : ∀ n < 16, isrSrc n < 16 := by decide

theorem permT_lt {f : Nat → Nat} (hf : ∀ n < 16, f n < 16) :
    ∀ j < 8, ∀ p < 128, ∀ t ∈ permT f j p, t.2 < 128 := fun j _ p hp t ht => by
  simp only [permT, List.mem_singleton] at ht
  subst ht
  have := hf (p / 8) (by omega_using [hp])
  show 8 * f (p / 8) + p % 8 < 128
  omega_using [this]

theorem mixT_lt {f : Nat → Nat} (hf : ∀ n < 16, f n < 16) (cs : List Nat) :
    ∀ j < 8, ∀ p < 128, ∀ t ∈ mixT f cs j p, t.2 < 128 := fun j _ p hp t ht => by
  simp only [mixT, List.mem_flatMap, List.mem_map] at ht
  obtain ⟨i, _, b, _, rfl⟩ := ht
  have := hf (down (p / 8) i) (down_lt (by omega_using [hp]))
  show 8 * f (down (p / 8) i) + p % 8 < 128
  omega_using [this]

theorem srA_check : StraightQ.check (lanes 128 10) qCfg (StraightQ.linExt 8) ((permute srOff B).tail)
    (StraightQ.linEnv (insOf B) [(.v24, srIdx)])
    (StraightQ.linPost 10 (outsOf B (permT srSrc))) = true := by decide +kernel
theorem isrA_check : StraightQ.check (lanes 128 10) qCfg (StraightQ.linExt 8) ((permute isrOff A).tail)
    (StraightQ.linEnv (insOf A) [(.v24, isrIdx)])
    (StraightQ.linPost 10 (outsOf A (permT isrSrc))) = true := by decide +kernel
theorem mc_check : StraightQ.check (lanes 128 10) qCfg (StraightQ.linExt 8) mcCore
    (StraightQ.linEnv (insOf B) [(.v24, srRotIdx), (.v25, srIdx)])
    (StraightQ.linPost 10 (outsOf A (mixT srSrc mcCoeffs))) = true := by decide +kernel
theorem imc_check : StraightQ.check (lanes 128 10) qCfg (StraightQ.linExt 8) imcCore
    (StraightQ.linEnv (insOf B) [(.v24, rotIdx)])
    (StraightQ.linPost 10 (outsOf A (mixT id invMcCoeffs))) = true := by decide +kernel

theorem NRel.perm {Q Q' : Nat → BitVec 128} {S T : Nat → Spec.Aes.State} (h : NRel Q S)
    {f : Nat → Nat} (hf : ∀ n < 16, f n < 16)
    (hQ : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = termsXor Q (permT f j p))
    (hT : ∀ k < 8, ∀ n < 16, (T k).getD n 0 = (S k).getD (f n) 0) : NRel Q' T :=
  fun j hj n hn k hk => by
    rw [hQ j hj _ (by omega_using [hn, hk]), hT k hk n hn, ← h j hj _ (hf n hn) k hk]
    simp only [permT, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false]
    congr 1
    rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt hk, Nat.add_zero, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hk]

theorem nrow {Q : Nat → BitVec 128} {S : Nat → Spec.Aes.State} (h : NRel Q S) {m k : Nat}
    (hm : m < 16) (hk : k < 8) : ∀ (l : List Nat), (∀ b ∈ l, b < 8) →
    termsXor Q (l.map fun b => (b, 8 * m + k)) =
      l.foldr (fun i b => ((S k).getD m 0).getLsbD i ^^ b) false
  | [], _ => rfl
  | t :: l, hl => by
    have := nrow h hm hk l fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [termsXor, List.map_cons, List.foldr_cons] at this ⊢
    rw [this, h t (hl t List.mem_cons_self) m hm k hk]

theorem nmix_bit {Q : Nat → BitVec 128} {S : Nat → Spec.Aes.State} (h : NRel Q S) {f : Nat → Nat}
    (hf : ∀ n < 16, f n < 16) (cs : List Nat)
    (hc : ∀ i < 4, cs.getD i 0 ∈ [0x02, 0x03, 0x01, 0x0e, 0x0b, 0x0d, 0x09])
    {j n k : Nat} (hj : j < 8) (hn : n < 16) (hk : k < 8) :
    termsXor Q (mixT f cs j (8 * n + k)) =
      (Spec.Aes.mul (BitVec.ofNat 8 (cs.getD 0 0)) ((S k).getD (f (down n 0)) 0) ^^^
       Spec.Aes.mul (BitVec.ofNat 8 (cs.getD 1 0)) ((S k).getD (f (down n 1)) 0) ^^^
       Spec.Aes.mul (BitVec.ofNat 8 (cs.getD 2 0)) ((S k).getD (f (down n 2)) 0) ^^^
       Spec.Aes.mul (BitVec.ofNat 8 (cs.getD 3 0)) ((S k).getD (f (down n 3)) 0)).getLsbD j := by
  have e : (8 * n + k) / 8 = n := by omega_using [hk]
  have e' : (8 * n + k) % 8 = k := by omega_using [hk]
  simp only [mixT, show List.range 4 = [0, 1, 2, 3] from rfl, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, termsXor_append, e, e', BitVec.getLsbD_xor]
  rw [nrow h (hf _ (down_lt hn)) hk _ (mulTerms_lt _ _), nrow h (hf _ (down_lt hn)) hk _ (mulTerms_lt _ _),
    nrow h (hf _ (down_lt hn)) hk _ (mulTerms_lt _ _), nrow h (hf _ (down_lt hn)) hk _ (mulTerms_lt _ _),
    mulTerms_ok _ (hc 0 (by decide)) _ j hj, mulTerms_ok _ (hc 1 (by decide)) _ j hj,
    mulTerms_ok _ (hc 2 (by decide)) _ j hj, mulTerms_ok _ (hc 3 (by decide)) _ j hj]
  simp only [Bool.xor_assoc]

theorem nrel_mc {Q Q' : Nat → BitVec 128} {S : Nat → Spec.Aes.State} (h : NRel Q S)
    (hQ : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = termsXor Q (mixT srSrc mcCoeffs j p)) :
    NRel Q' fun k => Spec.Aes.mixColumns (Spec.Aes.shiftRows (S k)) := fun j hj n hn k hk => by
  have sr : ∀ m < 16, (S k).getD (srSrc m) 0 = (Spec.Aes.shiftRows (S k)).getD m 0 := fun m hm => by
    rw [Spec.Aes.shiftRows, getD_ofFn _ hm]; rfl
  show _ = ((Spec.Aes.mixColumns (Spec.Aes.shiftRows (S k))).getD n 0).getLsbD j
  rw [hQ j hj _ (by omega_using [hn, hk]), nmix_bit h srSrc_lt mcCoeffs (by decide) hj hn hk,
    sr _ (down_lt hn), sr _ (down_lt hn), sr _ (down_lt hn), sr _ (down_lt hn),
    Spec.Aes.mixColumns, getD_ofFn _ hn]
  simp only [mcCoeffs, List.getD_cons_zero, List.getD_cons_succ, down, mul_one_byte,
    show (BitVec.ofNat 8 1) = (1 : Byte) from rfl]
  rfl

theorem nrel_imc {Q Q' : Nat → BitVec 128} {S : Nat → Spec.Aes.State} (h : NRel Q S)
    (hQ : ∀ j < 8, ∀ p < 128, (Q' j).getLsbD p = termsXor Q (mixT id invMcCoeffs j p)) :
    NRel Q' fun k => Spec.Aes.invMixColumns (S k) := fun j hj n hn k hk => by
  show _ = ((Spec.Aes.invMixColumns (S k)).getD n 0).getLsbD j
  rw [hQ j hj _ (by omega_using [hn, hk]), nmix_bit (f := id) h (fun _ h => h) invMcCoeffs (by decide) hj hn hk,
    Spec.Aes.invMixColumns, getD_ofFn _ hn]
  rfl

/-! ## The indices, in their slots -/

/-- The indices are in their slots of the scratch buffer. -/
def IdxAt (m : Mem) (b : Addr) : Prop :=
  ∀ o v, (o, v) ∈ idxSlots → m.readW (b + BitVec.ofNat 64 o) 128 = v

theorem idx_load {s : State} (hscr : ScrIn (s.gpr sb) s.wr) (hi : IdxAt s.mem (s.gpr sb)) {o : Nat}
    {v : BitVec 128} (hov : (o, v) ∈ idxSlots) (d : VReg) :
    exec (.ldrq d sb o) s = some (s.setV d v) := by
  have ho : o % 16 = 0 ∧ o < 128 :=
    (by decide : ∀ o ∈ idxSlots.map (·.1), o % 16 = 0 ∧ o < 128) o (List.mem_map.mpr ⟨_, hov, rfl⟩)
  obtain ⟨L, hL, hL', hm⟩ := hscr
  have hin : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 o) 16 :=
    ⟨_, List.mem_append_right _ hm, Offset.contains_base _ (by omega_using [ho, hL]) (by omega_using [ho])⟩
  have ha : addr s 16 sb o = some (s.gpr sb + BitVec.ofNat 64 o) := by
    unfold addr; rw [ite_eq_left ⟨ho.1, by omega_using [ho]⟩]
  have hr := hi o v hov
  rw [← read16_readW] at hr
  simp [exec, ha, State.load, hin, hr]

theorem setV_keeps (s : State) (d : VReg) (v : BitVec 128) : Keeps s (s.setV d v) :=
  .of_v rfl

theorem shiftMix_ok {s : State} (hscr : ScrIn (s.gpr sb) s.wr) (hi : IdxAt s.mem (s.gpr sb))
    {S : Nat → Spec.Aes.State} (hS : NRel (fun j => s.v (B j)) S) :
    ∃ s', runBlock isa shiftMix s = some s' ∧
      NRel (fun j => s'.v (A j)) (fun k => Spec.Aes.mixColumns (Spec.Aes.shiftRows (S k))) ∧
      Keeps s s' := by
  let s₁ := s.setV .v24 srRotIdx
  let s₂ := s₁.setV .v25 srIdx
  obtain ⟨s', hs', h, hk⟩ := lin_ok mc_check (mixT_lt srSrc_lt _) (s := s₂) (fun r v hrv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrv
    rcases hrv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (RegUpd.v_setV_of_ne _ _ (by decide)).trans (RegUpd.v_setV_self _ _ _)
    · exact RegUpd.v_setV_self _ _ _)
  refine ⟨s', ?_, nrel_mc (hS.congrW fun j hj => ?_) h,
    ((setV_keeps s _ _).trans (setV_keeps s₁ _ _)).trans hk⟩
  · show runBlock isa (.ldrq .v24 sb srRotOff :: .ldrq .v25 sb srOff :: mcCore) s = _
    rw [runBlock_cons, idx_load hscr hi (v := srRotIdx) (by simp [idxSlots]) .v24, runStep_some, runBlock_cons,
      idx_load (s := s₁) hscr hi (v := srIdx) (by simp [idxSlots]) .v25, runStep_some, hs']
  · have hB : ∀ j < 8, B j ≠ .v24 ∧ B j ≠ .v25 := by decide
    show _ = ((s.setV .v24 _).setV .v25 _).v (B j)
    rw [RegUpd.v_setV_of_ne _ _ (hB j hj).2, RegUpd.v_setV_of_ne _ _ (hB j hj).1]

theorem invMix_ok {s : State} (hscr : ScrIn (s.gpr sb) s.wr) (hi : IdxAt s.mem (s.gpr sb))
    {S : Nat → Spec.Aes.State} (hS : NRel (fun j => s.v (B j)) S) :
    ∃ s', runBlock isa invMix s = some s' ∧
      NRel (fun j => s'.v (A j)) (fun k => Spec.Aes.invMixColumns (S k)) ∧ Keeps s s' := by
  let s₁ := s.setV .v24 rotIdx
  obtain ⟨s', hs', h, hk⟩ := lin_ok imc_check (mixT_lt (fun _ h => h) _) (s := s₁) (fun r v hrv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    exact RegUpd.v_setV_self _ _ _)
  refine ⟨s', ?_, nrel_imc (hS.congrW fun j hj => ?_) h, (setV_keeps s _ _).trans hk⟩
  · show runBlock isa (.ldrq .v24 sb rotOff :: imcCore) s = _
    rw [runBlock_cons, idx_load hscr hi (v := rotIdx) (by simp [idxSlots]) .v24, runStep_some, hs']
  · exact (RegUpd.v_setV_of_ne _ _ ((by decide : ∀ j < 8, B j ≠ .v24) j hj)).symm

theorem permute_ok {P : Nat → VReg} {o : Nat} {v : BitVec 128} {f : Nat → Nat}
    (hP : ∀ j < 8, P j ≠ .v24) (hov : (o, v) ∈ idxSlots) (hf : ∀ n < 16, f n < 16)
    (hchk : StraightQ.check (lanes 128 10) qCfg (StraightQ.linExt 8) ((permute o P).tail)
      (StraightQ.linEnv (insOf P) [(.v24, v)]) (StraightQ.linPost 10 (outsOf P (permT f))) = true)
    {s : State} (hscr : ScrIn (s.gpr sb) s.wr) (hi : IdxAt s.mem (s.gpr sb))
    {S T : Nat → Spec.Aes.State} (hS : NRel (fun j => s.v (P j)) S)
    (hT : ∀ k < 8, ∀ n < 16, (T k).getD n 0 = (S k).getD (f n) 0) :
    ∃ s', runBlock isa (permute o P) s = some s' ∧ NRel (fun j => s'.v (P j)) T ∧ Keeps s s' := by
  let s₁ := s.setV .v24 v
  obtain ⟨s', hs', h, hk⟩ := lin_ok hchk (permT_lt hf) (s := s₁) (fun r v hrv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrv
    obtain ⟨rfl, rfl⟩ := hrv
    exact RegUpd.v_setV_self _ _ _)
  refine ⟨s', ?_, NRel.perm (hS.congrW fun j hj => ?_) hf h hT, (setV_keeps s _ _).trans hk⟩
  · rw [permute, runBlock_cons, idx_load hscr hi hov .v24, runStep_some]; exact hs'
  · exact (RegUpd.v_setV_of_ne _ _ (hP j hj)).symm

theorem shiftB_ok {s : State} (hscr : ScrIn (s.gpr sb) s.wr) (hi : IdxAt s.mem (s.gpr sb))
    {S : Nat → Spec.Aes.State} (hS : NRel (fun j => s.v (B j)) S) :
    ∃ s', runBlock isa (permute srOff B) s = some s' ∧
      NRel (fun j => s'.v (B j)) (fun k => Spec.Aes.shiftRows (S k)) ∧ Keeps s s' :=
  permute_ok (by decide) (v := srIdx) (by simp [idxSlots]) srSrc_lt srA_check hscr hi hS fun k _ n hn => by
    rw [Spec.Aes.shiftRows, getD_ofFn _ hn]; rfl

theorem invShiftA_ok {s : State} (hscr : ScrIn (s.gpr sb) s.wr) (hi : IdxAt s.mem (s.gpr sb))
    {S : Nat → Spec.Aes.State} (hS : NRel (fun j => s.v (A j)) S) :
    ∃ s', runBlock isa (permute isrOff A) s = some s' ∧
      NRel (fun j => s'.v (A j)) (fun k => Spec.Aes.invShiftRows (S k)) ∧ Keeps s s' :=
  permute_ok (by decide) (v := isrIdx) (by simp [idxSlots]) isrSrc_lt isrA_check hscr hi hS fun k _ n hn => by
    rw [Spec.Aes.invShiftRows, getD_ofFn _ hn]; rfl

/-! ## AddRoundKey -/

/-- The slices `K` of a round key, the same for the eight blocks. -/
def KeyRel (K : Nat → BitVec 128) (rk : List Byte) : Prop := NRel K fun _ => rkState rk

theorem addKey_ok {P : Nat → VReg} (hP : ∀ i < 8, P i ≠ .v24 ∧ ∀ j < 8, i ≠ j → P i ≠ P j)
    (n : Nat) (hn : n ≤ 8) {s : State} {a : Addr} (ha : s.gpr kp = a)
    (hin : ∀ k < 8, InRegions (s.rd ++ s.wr) (vAddr a k) 16) :
    ∃ s', runBlock isa ((List.range n).flatMap fun j =>
        ([.ldrq .v24 kp (16 * j), veor (P j) (P j) .v24] : List Instr)) s = some s' ∧
      (∀ j < 8, s'.v (P j) = if j < n then s.v (P j) ^^^ s.mem.readW (vAddr a j) 128 else s.v (P j)) ∧
      s' = { s with v := s'.v } := by
  induction n with
  | zero => exact ⟨s, rfl, fun j _ => by simp, rfl⟩
  | succ n ih =>
    obtain ⟨t, ht, hv, he⟩ := ih (Nat.le_of_succ_le hn)
    have hn8 : n < 8 := hn
    let u := t.setV .v24 (s.mem.readW (vAddr a n) 128)
    have hu : exec (.ldrq .v24 kp (16 * n)) t = some u := by
      have hg : t.gpr kp = a := by rw [he]; exact ha
      have hm : t.mem = s.mem := by rw [he]
      have hin' : InRegions (t.rd ++ t.wr) (vAddr a n) 16 := by rw [he]; exact hin n hn8
      simp [exec, addr_slot (show 16 * n < 65536 by omega_using [hn8]), State.load, hin', read16_readW,
        hg, hm, u]
    let w := u.setV (P n) (u.v (P n) ^^^ u.v .v24)
    refine ⟨w, ?_, fun j hj => ?_, ?_⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine Tbl.runBlock_cat_some ht ?_
      rw [runBlock_cons, hu, runStep_some, runBlock_cons, veor, exec_vop_some rfl, runStep_some,
        runBlock_nil]
    · by_cases hjn : j = n
      · subst hjn
        simp only [w, u, RegUpd.v_setV_self, RegUpd.v_setV_of_ne _ _ (hP j hj).1, Nat.lt_succ_self, ite_true]
        rw [hv j hj, ite_eq_right (Nat.lt_irrefl j)]
      · simp only [w, u, RegUpd.v_setV_of_ne _ _ ((hP j hj).2 n hn8 hjn), RegUpd.v_setV_of_ne _ _ (hP j hj).1]
        rw [hv j hj]
        by_cases h : j < n
        · rw [ite_eq_left h, ite_eq_left (Nat.lt_succ_of_lt h)]
        · rw [ite_eq_right h, ite_eq_right (by omega_using [h, hjn])]
    · simp only [w, u, State.setV]; rw [he]

theorem addRoundKey_ok {P : Nat → VReg} (hP : ∀ i < 8, P i ≠ .v24 ∧ ∀ j < 8, i ≠ j → P i ≠ P j)
    {s : State} {a : Addr} (ha : s.gpr kp = a)
    (hin : ∀ k < 8, InRegions (s.rd ++ s.wr) (vAddr a k) 16) {rk : List Byte}
    (hK : KeyRel (fun k => s.mem.readW (vAddr a k) 128) rk) {S : Nat → Spec.Aes.State}
    (hS : NRel (fun j => s.v (P j)) S) :
    ∃ s', runBlock isa (Impl.Aes.AArch64.Neon.addRoundKey P) s = some s' ∧
      NRel (fun j => s'.v (P j)) (fun k => Spec.Aes.addRoundKey (S k) rk) ∧ Keeps s s' := by
  obtain ⟨s', hs', hv, he⟩ := addKey_ok hP 8 (Nat.le_refl 8) ha hin
  refine ⟨s', hs', fun j hj n hn k hk => ?_, .of_v he⟩
  have hK' := hK j hj n hn k hk
  rw [getD_rkState _ hn] at hK'
  show (s'.v (P j)).getLsbD (8 * n + k) = ((Spec.Aes.addRoundKey (S k) rk).getD n 0).getLsbD j
  rw [hv j hj, ite_eq_left hj, BitVec.getLsbD_xor, hS j hj n hn k hk, hK', Spec.Aes.addRoundKey,
    getD_ofFn _ hn, BitVec.getLsbD_xor]

end VG.Proof.Aes.AArch64.Neon
