module

public import VerifiedGarbage.Proof.Gcm.Arm.Ghash
public import VerifiedGarbage.Proof.Gcm.Slots
public import VerifiedGarbage.Proof.Gcm.Spread32
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# GHASH with integer multiplications on ARM

Untrusted: everything here is checked by Lean. The blocks of the code but for
its loads of `H`, `Y` and the data are run on an abstract machine, the
registers and the 64 words of `scratch` (`A`, `evalA`), which the machine
follows (`sound`).
-/

@[expose] public section

namespace VG.Proof.Gcm.Arm

open VG VG.Arm
open VG.Impl.Gcm.Arm
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

/-! ## The abstract machine -/

structure A where
  g : Reg → BitVec 32
  m : Nat → BitVec 32

namespace A

def set (a : A) (d : Reg) (v : BitVec 32) : A := ⟨fun r => if r = d then v else a.g r, a.m⟩
def put (a : A) (k : Nat) (v : BitVec 32) : A := ⟨a.g, fun j => if j = k then v else a.m j⟩

theorem g_set (a : A) (d : Reg) (v : BitVec 32) (r : Reg) : (a.set d v).g r = if r = d then v else a.g r := rfl
theorem m_set (a : A) (d : Reg) (v : BitVec 32) : (a.set d v).m = a.m := rfl
theorem g_put (a : A) (k : Nat) (v : BitVec 32) : (a.put k v).g = a.g := rfl
theorem m_put (a : A) (k : Nat) (v : BitVec 32) (j : Nat) : (a.put k v).m j = if j = k then v else a.m j := rfl

end A

def shiftA (v : BitVec 32) : Shift → Nat → BitVec 32
  | .lsl, n => v <<< n
  | .lsr, n => v >>> n
  | .ror, n => v.rotateRight n

def opA (a : A) : Op2 → Option (BitVec 32)
  | .imm v => if encodable v then some v else none
  | .reg r => some (a.g r)
  | .shifted r sh n => if 1 ≤ n ∧ n ≤ 31 then some (shiftA (a.g r) sh n) else none

def dpA (op : DpOp) (x y : BitVec 32) : BitVec 32 :=
  match op with
  | .add => x + y | .sub => x - y | .and => x &&& y | .orr => x ||| y | .eor => x ^^^ y | .bic => x &&& ~~~y

/-- The word of `scratch` at an offset from its address. -/
def slotOf (n : Reg) (off : Nat) : Option Nat :=
  if n = .r12 ∧ off % 4 = 0 ∧ off < 256 then some (off / 4) else none

theorem slotOf_slot {k : Nat} (hk : k < 64) : slotOf .r12 (4 * k) = some k := by
  rw [slotOf, ite_eq_left ⟨rfl, by omega, by omega⟩, Nat.mul_div_cancel_left k (by decide)]

def stepA : Instr → A → Option A
  | .mov d o, a => if d = .r12 then none else (opA a o).map (a.set d)
  | .dp op d n o, a => if d = .r12 then none else (opA a o).map fun y => a.set d (dpA op (a.g n) y)
  | .movw d v, a => if d = .r12 then none else some (a.set d (v.setWidth 32))
  | .movt d v, a => if d = .r12 then none else some (a.set d (v ++ (a.g d).extractLsb' 0 16 : BitVec 32))
  | .rev d m, a => if d = .r12 then none else some (a.set d (rev (a.g m)))
  | .mul d n m, a => if d = .r12 then none else some (a.set d (a.g n * a.g m))
  | .ldr t n off, a => if t = .r12 then none else (slotOf n off).map fun k => a.set t (a.m k)
  | .str t n off, a => (slotOf n off).map fun k => a.put k (a.g t)
  | _, _ => none

def evalA : List Instr → A → Option A
  | [], a => some a
  | i :: is, a => (stepA i a).bind (evalA is)

theorem evalA_append (l₁ l₂ : List Instr) (a : A) : evalA (l₁ ++ l₂) a = (evalA l₁ a).bind (evalA l₂) := by
  induction l₁ generalizing a with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, evalA, Option.bind_assoc]
    exact congrArg _ (funext fun a' => ih a')

/-- `scratch`'s address. -/
abbrev scr (s₀ : State) : BitVec 32 := stackArg s₀ 0

/-- What the machine's state is to the abstract one's: `s₀` is the state at
entry, whose memory outside `scratch` is unchanged. -/
structure Rel (s₀ : State) (s : State) (a : A) : Prop where
  g : s.gpr = a.g
  m : Slots32 s₀.mem s.mem (State.addr (scr s₀)) 64 a.m
  r12 : a.g .r12 = scr s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What of the state at entry the abstract machine's steps need. -/
structure Scr (s₀ : State) : Prop where
  mem : (⟨State.addr (scr s₀), 256⟩ : Region) ∈ s₀.wr
  fit : (scr s₀).toNat + 256 ≤ 2 ^ 32

namespace Rel

variable {s₀ s : State} {a : A}

theorem set (h : Rel s₀ s a) {d : Reg} (hd : d ≠ .r12) (v : BitVec 32) : Rel s₀ (s.setReg d v) (a.set d v) :=
  ⟨by funext r; show (if r = d then v else s.gpr r) = _; rw [h.g]; rfl, h.m,
    by rw [A.g_set, ite_eq_right (Ne.symm hd)]; exact h.r12, h.sp, h.rd, h.wr⟩

theorem op (h : Rel s₀ s a) {o : Op2} {v : BitVec 32} (hv : opA a o = some v) : o.eval s = some v := by
  rw [← hv]
  cases o with
  | imm v => rfl
  | reg r => simp only [Op2.eval, opA, h.g]
  | shifted r sh n => simp only [Op2.eval, opA, h.g]; cases sh <;> rfl

theorem slot (h : Rel s₀ s a) (hw : Scr s₀) {n : Reg} {off k : Nat} (hk : slotOf n off = some k) :
    off < 4096 ∧ k < 64 ∧ State.addr (s.gpr n + BitVec.ofNat 32 off) = State.addr (scr s₀) + BitVec.ofNat 64 (4 * k) ∧
      InRegions s.wr (State.addr (scr s₀) + BitVec.ofNat 64 (4 * k)) 4 := by
  have hf := hw.fit
  rw [slotOf] at hk
  split at hk
  · rename_i hc
    obtain ⟨rfl, h1, h2⟩ := hc
    cases hk
    refine ⟨by omega, by omega, ?_, _, by rw [h.wr]; exact hw.mem, Slots32.contains (n := 64) _ (by omega) (by decide)⟩
    rw [h.g, h.r12, addr_add (by omega), show 4 * (off / 4) = off by omega]
  · cases hk

end Rel

theorem exec_dp (op : DpOp) (d n : Reg) (o : Op2) (s : State) :
    exec (.dp op d n o) s = (o.eval s).map fun y => s.setReg d (dpA op (s.gpr n) y) := by cases op <;> rfl

theorem step_sound {s₀ s : State} {a a' : A} (h : Rel s₀ s a) (hw : Scr s₀) (i : Instr) (hi : stepA i a = some a') :
    ∃ s', exec i s = some s' ∧ Rel s₀ s' a' := by
  unfold stepA at hi
  split at hi
  · split at hi
    · cases hi
    · rename_i hd
      simp only [Option.map_eq_some_iff] at hi
      obtain ⟨v, hv, rfl⟩ := hi
      exact ⟨_, by rw [show exec _ s = (Op2.eval s _).map _ from rfl, h.op hv]; rfl, h.set hd v⟩
  · split at hi
    · cases hi
    · rename_i hd
      simp only [Option.map_eq_some_iff] at hi
      obtain ⟨v, hv, rfl⟩ := hi
      refine ⟨_, by rw [exec_dp, h.op hv]; rfl, ?_⟩
      rw [h.g]
      exact h.set hd _
  · split at hi
    · cases hi
    · rename_i hd; cases hi; exact ⟨_, rfl, h.set hd _⟩
  · split at hi
    · cases hi
    · rename_i hd; cases hi; refine ⟨_, rfl, ?_⟩; rw [h.g]; exact h.set hd _
  · split at hi
    · cases hi
    · rename_i hd; cases hi; refine ⟨_, rfl, ?_⟩; rw [h.g]; exact h.set hd _
  · split at hi
    · cases hi
    · rename_i hd; cases hi; refine ⟨_, rfl, ?_⟩; rw [h.g]; exact h.set hd _
  · split at hi
    · cases hi
    · rename_i hd
      simp only [Option.map_eq_some_iff] at hi
      obtain ⟨k, hk, rfl⟩ := hi
      obtain ⟨ho, hk, he, r, hr, hc⟩ := h.slot hw hk
      refine ⟨_, exec_ldr ho (by rw [he]; exact ⟨r, List.mem_append_right _ hr, hc⟩), ?_⟩
      rw [he, h.m.get k hk]
      exact h.set hd _
  · simp only [Option.map_eq_some_iff] at hi
    obtain ⟨k, hk, rfl⟩ := hi
    obtain ⟨ho, hk, he, hin⟩ := h.slot hw hk
    refine ⟨_, exec_str ho (by rw [he]; exact hin), ?_⟩
    rw [he, h.g]
    exact ⟨rfl, h.m.store hk (by decide) _, h.r12, h.sp, h.rd, h.wr⟩
  · cases hi

/-- The machine runs what the abstract machine runs. -/
theorem sound {s₀ : State} (hw : Scr s₀) {is : List Instr} {s : State} {a a' : A}
    (h : Rel s₀ s a) (he : evalA is a = some a') : WP isa (.block is) s fun s' => Rel s₀ s' a' := by
  induction is generalizing s a with
  | nil => cases he; exact WP.block_nil h
  | cons i is ih =>
    simp only [evalA, Option.bind_eq_some_iff] at he
    obtain ⟨a₁, h₁, h₂⟩ := he
    obtain ⟨s₁, e, r⟩ := step_sound h hw i h₁
    exact WP.block_cons_iff.mpr ⟨s₁, e, ih r h₂⟩

/-! ## Running blocks -/

def WA (is : List Instr) (a : A) (Q : A → Prop) : Prop := ∃ a', evalA is a = some a' ∧ Q a'

theorem WA.append {l₁ l₂ : List Instr} {a : A} {Q : A → Prop} (h : WA l₁ a fun a' => WA l₂ a' Q) :
    WA (l₁ ++ l₂) a Q := by
  obtain ⟨a₁, e₁, a₂, e₂, q⟩ := h
  exact ⟨a₂, by rw [evalA_append, e₁]; exact e₂, q⟩

theorem WA.mono {l : List Instr} {a : A} {Q R : A → Prop} (h : WA l a Q) (hq : ∀ a', Q a' → R a') : WA l a R := by
  obtain ⟨a', e, q⟩ := h; exact ⟨a', e, hq a' q⟩

/-- The machine runs what `WA` says. -/
theorem WA.sound {s₀ s : State} {a : A} {is : List Instr} {Q : A → Prop} (hp : Scr s₀) (h : Rel s₀ s a) (hw : WA is a Q) :
    WP isa (.block is) s fun s' => ∃ a', Rel s₀ s' a' ∧ Q a' := by
  obtain ⟨a', e, q⟩ := hw
  exact WP.mono (Arm.sound hp h e) fun s' r => ⟨a', r, q⟩

/-- Registers other than `rs` are unchanged. -/
def Keeps (rs : List Reg) (a a' : A) : Prop := ∀ r, r ∉ rs → a'.g r = a.g r

theorem Keeps.trans {rs : List Reg} {a b c : A} (h₁ : Keeps rs a b) (h₂ : Keeps rs b c) : Keeps rs a c :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

theorem Keeps.mono {rs rs' : List Reg} {a b : A} (h : Keeps rs a b) (hs : ∀ r ∈ rs, r ∈ rs') : Keeps rs' a b :=
  fun r hr => h r fun h' => hr (hs r h')

open Spread (c3 meet3 cm16 lo16 hi16 sum16 mul32 mulW4 W4 up32 dn32 redW4 mul_words32)

theorem mask_eq (r : Nat) : mask r = c3 r := by
  unfold mask c3; rfl

/-! ## The product of two words -/

/-- The registers hold the masks. -/
structure Masks (a : A) : Prop where
  m0 : a.g .r1 = c3 0
  m1 : a.g .r2 = c3 1
  m2 : a.g .r3 = c3 2

/-- What a product overwrites. -/
abbrev work : List Reg := [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem Masks.keeps {rs : List Reg} {a b : A} (h : Masks a) (k : Keeps rs a b) (h1 : Reg.r1 ∉ rs) (h2 : Reg.r2 ∉ rs)
    (h3 : Reg.r3 ∉ rs) : Masks b :=
  ⟨by rw [k _ h1, h.m0], by rw [k _ h2, h.m1], by rw [k _ h3, h.m2]⟩

theorem classes_ok (x : Reg) (j : Nat) (hj : j < 64) (a : A) (hM : Masks a) :
    WA (classes x j) a fun a' =>
      (a'.g .r4 = a.g x >>> 16 &&& c3 0 ∧ a'.g .r5 = a.g x >>> 16 &&& c3 1 ∧ a'.g .r6 = a.g x >>> 16 &&& c3 2) ∧
      (a'.g .r7 = a.m j &&& c3 0 ∧ a'.g .r8 = a.m j &&& c3 1 ∧ a'.g .r9 = a.m j &&& c3 2) ∧
      Keeps work a a' ∧ a'.m = a.m := by
  simp only [WA, classes, ld, lsrI, evalA, stepA, opA, dpA, shiftA, slotOf_slot hj, Option.map_some, Option.bind_some, A.g_set,
    A.m_set, hM.m0, hM.m1, hM.m2, reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left',
    Nat.reduceLeDiff, and_self, BitVec.and_comm (c3 _)]
  refine ⟨trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [A.g_set, hr, ite_false]

theorem classSum_ok (q : Reg) (hq : q = .r0 ∨ q = .r10) (r : Nat) (hr : r < 3) (x y : BitVec 32) (a : A) (hM : Masks a)
    (hx : a.g .r4 = x &&& c3 0 ∧ a.g .r5 = x &&& c3 1 ∧ a.g .r6 = x &&& c3 2)
    (hy : a.g .r7 = y &&& c3 0 ∧ a.g .r8 = y &&& c3 1 ∧ a.g .r9 = y &&& c3 2) :
    WA (classSum q r) a fun a' => a'.g q = meet3 x y r &&& c3 r ∧ Keeps [q, .r11] a a' ∧ a'.m = a.m := by
  have h3 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hq with rfl | rfl <;> rcases h3 with rfl | rfl | rfl <;>
  · simp only [WA, classSum, eor, kc, maskReg, evalA, stepA, opA, dpA, Option.map_some, Option.bind_some, A.g_set, A.m_set,
      hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2, hM.m0, hM.m1, hM.m2, reduceCtorEq, ite_false, ite_true,
      Option.some.injEq, exists_eq_left', meet3, Nat.reduceMod, Nat.reduceAdd]
    refine ⟨trivial, fun r hr => ?_, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem eor_ok (d n m : Reg) (hd : d ≠ .r12) (a : A) :
    WA [eor d n m] a fun a' => a'.g d = a.g n ^^^ a.g m ∧ Keeps [d] a a' ∧ a'.m = a.m := by
  simp only [WA, eor, evalA, stepA, opA, dpA, hd, Option.map_some, Option.bind_some, A.g_set, A.m_set, ite_false, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_set, hr, ite_false]

theorem prod_ok (x : Reg) (j : Nat) (hj : j < 64) (a : A) (hM : Masks a) :
    WA (prod x j) a fun a' => a'.g .r0 = cm16 (a.g x >>> 16) (a.m j) ∧ Keeps work a a' ∧ a'.m = a.m := by
  rw [prod, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WA.append ((classes_ok x j hj a hM).mono fun b ⟨hX, hY, kb, mb⟩ => ?_)
  have hMb := hM.keeps kb (by decide) (by decide) (by decide)
  refine WA.append ((classSum_ok .r0 (.inl rfl) 0 (by decide) _ _ b hMb hX hY).mono fun c ⟨e₀, kc, mc⟩ => ?_)
  have hMc := hMb.keeps kc (by decide) (by decide) (by decide)
  refine WA.append ((classSum_ok .r10 (.inr rfl) 1 (by decide) (a.g x >>> 16) (a.m j) c hMc
    ⟨by rw [kc _ (by decide), hX.1], by rw [kc _ (by decide), hX.2.1], by rw [kc _ (by decide), hX.2.2]⟩
    ⟨by rw [kc _ (by decide), hY.1], by rw [kc _ (by decide), hY.2.1], by rw [kc _ (by decide), hY.2.2]⟩).mono
    fun d ⟨e₁, kd, md⟩ => ?_)
  refine WA.append ((eor_ok .r0 .r0 .r10 (by decide) d).mono fun e ⟨e₂, ke, me⟩ => ?_)
  have kbe : Keeps [.r0, .r10, .r11] b e :=
    (kc.mono (by decide)).trans ((kd.mono (by decide)).trans (ke.mono (by decide)))
  have hMe := hMb.keeps kbe (by decide) (by decide) (by decide)
  refine WA.append ((classSum_ok .r10 (.inr rfl) 2 (by decide) (a.g x >>> 16) (a.m j) e hMe
    ⟨by rw [kbe _ (by decide), hX.1], by rw [kbe _ (by decide), hX.2.1], by rw [kbe _ (by decide), hX.2.2]⟩
    ⟨by rw [kbe _ (by decide), hY.1], by rw [kbe _ (by decide), hY.2.1], by rw [kbe _ (by decide), hY.2.2]⟩).mono
    fun f ⟨e₃, kf, mf⟩ => ?_)
  refine (eor_ok .r0 .r0 .r10 (by decide) f).mono fun g ⟨e₄, kg, mg⟩ => ⟨?_, ?_, ?_⟩
  · rw [e₄, kf _ (by decide), e₂, kd _ (by decide), e₀, e₁, e₃, cm16]
  · exact kb.trans ((kbe.mono (by decide)).trans ((kf.mono (by decide)).trans (kg.mono (by decide))))
  · rw [mg, mf, me, md, mc, mb]

/-- The halves of the key's word `t` and their sum. -/
def KeyOk (a : A) (t : Nat) (k : BitVec 32) : Prop :=
  a.m (3 * t) = lo16 k ∧ a.m (3 * t + 1) = hi16 k ∧ a.m (3 * t + 2) = lo16 k ^^^ hi16 k

abbrev workLr : List Reg := [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

theorem mul32_ok (k t : Nat) (hk : k < 48) (ht : t < 9) (kw : BitVec 32) (a : A) (hM : Masks a) (hK : KeyOk a t kw) :
    WA (VG.Impl.Gcm.Arm.mul32 k t) a fun a' =>
      a'.g .r4 = (mul32 (a.m k) kw).1 ∧ a'.g .r5 = (mul32 (a.m k) kw).2 ∧ Keeps workLr a a' ∧
      ∀ j, j < 48 ∨ 50 ≤ j → a'.m j = a.m j := by
  rw [VG.Impl.Gcm.Arm.mul32, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WA.append (WA.mono (Q := fun b => b.g .lr = a.m k ∧ b.g .r11 = a.m k <<< 16 ∧ Keeps workLr a b ∧ b.m = a.m)
    ?_ fun b ⟨l₁, r₁, k₁, m₁⟩ => ?_)
  · simp only [WA, ld, lslI, evalA, stepA, opA, shiftA, slotOf_slot (show k < 64 by omega), Option.map_some, Option.bind_some,
      A.g_set, A.m_set, reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left', Nat.reduceLeDiff, and_self]
    refine ⟨trivial, trivial, fun r hr => ?_, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]
  have hM₁ := hM.keeps k₁ (by decide) (by decide) (by decide)
  refine WA.append ((prod_ok .r11 (3 * t) (by omega) b hM₁).mono fun c ⟨e₂, k₂, m₂⟩ => ?_)
  refine WA.append (WA.mono (Q := fun d => d.g = c.g ∧ d.m t0S = c.g .r0 ∧ ∀ j, j ≠ t0S → d.m j = c.m j) ?_
    fun d ⟨g₃, e₃, m₃⟩ => ?_)
  · simp only [WA, st, t0S, evalA, stepA, slotOf_slot (show 48 < 64 by decide), Option.map_some, Option.bind_some,
      A.g_put, A.m_put, Option.some.injEq, exists_eq_left', ite_true]
    exact ⟨trivial, trivial, fun j hj => ite_eq_right hj⟩
  have k₃ : Keeps workLr a d := fun r hr => by
    rw [g₃, (k₂.mono (by decide) : Keeps workLr b c) r hr, k₁ r hr]
  have hM₃ := hM.keeps k₃ (by decide) (by decide) (by decide)
  have l₃ : d.g .lr = a.m k := by rw [g₃, k₂ _ (by decide), l₁]
  have M₃ : ∀ j, j < 48 ∨ 50 ≤ j → d.m j = a.m j := fun j hj => by rw [m₃ j (by unfold t0S; omega), m₂, m₁]
  refine WA.append ((prod_ok .lr (3 * t + 1) (by omega) d hM₃).mono fun e ⟨e₄, k₄, m₄⟩ => ?_)
  refine WA.append (WA.mono (Q := fun f => f.g .r11 = e.g .lr ^^^ e.g .lr <<< 16 ∧ Keeps [.r11] e f ∧
    f.m t1S = e.g .r0 ∧ ∀ j, j ≠ t1S → f.m j = e.m j) ?_ fun f ⟨r₅, k₅, e₅, m₅⟩ => ?_)
  · simp only [WA, st, t1S, evalA, stepA, opA, shiftA, dpA, slotOf_slot (show 49 < 64 by decide), Option.map_some,
      Option.bind_some, A.g_put, A.m_put, A.g_set, A.m_set, reduceCtorEq, Option.some.injEq, exists_eq_left', ite_true,
      ite_false, Nat.reduceLeDiff, and_self]
    refine ⟨trivial, fun r hr => ?_, trivial, fun j hj => ite_eq_right hj⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [A.g_set, A.g_put, hr, ite_false]
  have k₅' : Keeps workLr a f := k₃.trans ((k₄.mono (by decide)).trans (k₅.mono (by decide)))
  have hM₅ := hM.keeps k₅' (by decide) (by decide) (by decide)
  have M₅ : ∀ j, j < 48 ∨ 50 ≤ j → f.m j = a.m j := fun j hj => by rw [m₅ j (by unfold t1S; omega), m₄, M₃ j hj]
  refine WA.append ((prod_ok .r11 (3 * t + 2) (by omega) f hM₅).mono fun h ⟨e₆, k₆, m₆⟩ => ?_)
  have hp0 : h.m 48 = cm16 (lo16 (a.m k)) (lo16 kw) := by
    rw [m₆, m₅ 48 (by decide), m₄, show d.m 48 = c.g .r0 from e₃, e₂, r₁, m₁, hK.1]; rfl
  have hp1 : h.m 49 = cm16 (hi16 (a.m k)) (hi16 kw) := by
    rw [m₆, show f.m 49 = e.g .r0 from e₅, e₄, l₃, M₃ _ (by omega), hK.2.1]; rfl
  have hp2 : h.g .r0 = cm16 (lo16 (a.m k) ^^^ hi16 (a.m k)) (lo16 kw ^^^ hi16 kw) := by
    rw [e₆, r₅, k₄ _ (by decide), l₃, sum16, M₅ _ (by omega), hK.2.2]
  simp only [WA, ld, eor, t0S, t1S, evalA, stepA, opA, shiftA, dpA, slotOf_slot (show 48 < 64 by decide),
    slotOf_slot (show 49 < 64 by decide), Option.map_some, Option.bind_some, A.g_set, A.m_set, reduceCtorEq,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, Nat.reduceLeDiff, and_self, hp0, hp1, hp2, Spread.mul32]
  refine ⟨trivial, trivial, fun r hr => ?_, fun j hj => by rw [m₆, M₅ j hj]⟩
  have hk := (k₅'.trans (k₆.mono (by decide))) r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [A.g_set, hr, ite_false, hk]

theorem keep_ok (b : Nat) (hb : b + 1 < 64) (a : A) :
    WA (keep b) a fun a' => a'.m b = a.g .r4 ∧ a'.m (b + 1) = a.g .r5 ∧ (∀ j, j ≠ b → j ≠ b + 1 → a'.m j = a.m j) ∧
      a'.g = a.g := by
  simp only [WA, keep, st, evalA, stepA, slotOf_slot hb, slotOf_slot (Nat.lt_of_succ_lt hb), Option.map_some,
    Option.bind_some, A.g_put, A.m_put, Option.some.injEq, exists_eq_left', ite_true]
  exact ⟨ite_eq_right (Nat.ne_of_lt (Nat.lt_succ_self b)), trivial,
    fun j h1 h2 => by rw [ite_eq_right h2, ite_eq_right h1], trivial⟩

/-- The four words at `b`. -/
def At (a : A) (b : Nat) (w : W4) : Prop := a.m b = w.w0 ∧ a.m (b + 1) = w.w1 ∧ a.m (b + 2) = w.w2 ∧ a.m (b + 3) = w.w3

theorem mul64_ok (t b : Nat) (ht : t + 2 < 9) (hb : b = 36 ∨ b = 40 ∨ b = 44) (k0 k1 : BitVec 32) (a : A) (hM : Masks a)
    (hK : KeyOk a t k0 ∧ KeyOk a (t + 1) k1 ∧ KeyOk a (t + 2) (k0 ^^^ k1))
    (hS : a.m (27 + (t + 2)) = a.m (27 + t) ^^^ a.m (27 + (t + 1))) :
    WA (mul64 t b) a fun a' => At a' b (mulW4 Spread.mul32 (a.m (27 + (t + 1))) (a.m (27 + t)) k1 k0) ∧ Keeps workLr a a' ∧
      ∀ j, j < 48 ∨ 50 ≤ j → (j < b ∨ b + 4 ≤ j) → a'.m j = a.m j := by
  rw [mul64, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WA.append ((mul32_ok (27 + t) t (by omega) (by omega) k0 a hM hK.1).mono fun c ⟨p0, p1, kc, mc⟩ => ?_)
  refine WA.append ((keep_ok b (by omega) c).mono fun d ⟨q0, q1, md, gd⟩ => ?_)
  have kd : Keeps workLr a d := fun r hr => by rw [gd, kc r hr]
  have Md : ∀ j, j < 48 ∨ 50 ≤ j → j ≠ b → j ≠ b + 1 → d.m j = a.m j := fun j hj h1 h2 => by rw [md j h1 h2, mc j hj]
  have hKd : KeyOk d (t + 1) k1 := by
    obtain ⟨-, ⟨h1, h2, h3⟩, -⟩ := hK
    exact ⟨by rw [Md _ (by omega) (by omega) (by omega), h1], by rw [Md _ (by omega) (by omega) (by omega), h2],
      by rw [Md _ (by omega) (by omega) (by omega), h3]⟩
  refine WA.append ((mul32_ok (27 + (t + 1)) (t + 1) (by omega) (by omega) k1 d (hM.keeps kd (by decide) (by decide) (by decide))
    hKd).mono fun e ⟨p2, p3, ke, me⟩ => ?_)
  refine WA.append ((keep_ok (b + 2) (by omega) e).mono fun f ⟨q2, q3, mf, gf⟩ => ?_)
  have kf : Keeps workLr a f := fun r hr => by rw [gf, ke r hr, kd r hr]
  have Mf : ∀ j, j < 48 ∨ 50 ≤ j → (j < b ∨ b + 4 ≤ j) → f.m j = a.m j := fun j hj h => by
    rw [mf j (by omega) (by omega), me j hj, Md j hj (by omega) (by omega)]
  have hKf : KeyOk f (t + 2) (k0 ^^^ k1) := by
    obtain ⟨-, -, ⟨h1, h2, h3⟩⟩ := hK
    exact ⟨by rw [Mf _ (by omega) (by omega), h1], by rw [Mf _ (by omega) (by omega), h2],
      by rw [Mf _ (by omega) (by omega), h3]⟩
  refine WA.append ((mul32_ok (27 + (t + 2)) (t + 2) (by omega) (by omega) (k0 ^^^ k1) f
    (hM.keeps kf (by decide) (by decide) (by decide)) hKf).mono fun g ⟨p4, p5, kg, mg⟩ => ?_)
  rw [Mf _ (by omega) (by omega), hS] at p4 p5
  rw [Md _ (by omega) (by omega) (by omega)] at p2 p3
  have w0 : g.m b = (mul32 (a.m (27 + t)) k0).1 := by
    rw [mg _ (by omega), mf _ (by omega) (by omega), me _ (by omega), q0, p0]
  have w1 : g.m (b + 1) = (mul32 (a.m (27 + t)) k0).2 := by
    rw [mg _ (by omega), mf _ (by omega) (by omega), me _ (by omega), q1, p1]
  have w2 : g.m (b + 2) = (mul32 (a.m (27 + (t + 1))) k1).1 := by rw [mg _ (by omega), q2, p2]
  have w3 : g.m (b + 3) = (mul32 (a.m (27 + (t + 1))) k1).2 := by
    rw [mg _ (by omega), show f.m (b + 3) = e.g .r5 from q3, p3]
  simp only [WA, ld, st, eor, evalA, stepA, opA, dpA, slotOf_slot (show b < 64 by omega),
    slotOf_slot (show b + 1 < 64 by omega), slotOf_slot (show b + 2 < 64 by omega), slotOf_slot (show b + 3 < 64 by omega),
    Option.map_some, Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put, reduceCtorEq,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, w0, w1, w2, w3, p4, p5, At, mulW4,
    show ¬ b = b + 1 by omega, show ¬ b = b + 2 by omega, show ¬ b + 1 = b + 2 by omega,
    show ¬ b + 3 = b + 1 by omega, show ¬ b + 3 = b + 2 by omega]
  refine ⟨⟨trivial, trivial, trivial, trivial⟩, fun r hr => ?_, fun j hj h => ?_⟩
  · have hk := (kf.trans kg) r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, A.g_put, hr, ite_false, hk]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), mg j hj, Mf j hj h]

/-! ## The reduction and the key -/

theorem foldDn_ok (d q : Reg) (hd : d ≠ .r12) (hdq : q ≠ d) (a : A) :
    WA (foldDn d q) a fun a' => a'.g d = a.g d ^^^ dn32 (a.g q) ∧ Keeps [d] a a' ∧ a'.m = a.m := by
  simp only [WA, foldDn, evalA, stepA, opA, dpA, shiftA, hd, hdq, Option.map_some, Option.bind_some, A.g_set, A.m_set,
    ite_false, ite_true, Option.some.injEq, exists_eq_left', Nat.reduceLeDiff, and_self, dn32, BitVec.xor_assoc]
  refine ⟨trivial, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_set, hr, ite_false]

theorem foldUp_ok (d q : Reg) (hd : d ≠ .r12) (hdq : q ≠ d) (a : A) :
    WA (foldUp d q) a fun a' => a'.g d = a.g d ^^^ up32 (a.g q) ∧ Keeps [d] a a' ∧ a'.m = a.m := by
  simp only [WA, foldUp, evalA, stepA, opA, dpA, shiftA, hd, hdq, Option.map_some, Option.bind_some, A.g_set, A.m_set,
    ite_false, ite_true, Option.some.injEq, exists_eq_left', Nat.reduceLeDiff, and_self, up32, BitVec.xor_assoc]
  refine ⟨trivial, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_set, hr, ite_false]

theorem reduce_ok {a : A} {l h c : W4} (hl : At a 36 l) (hh : At a 40 h) (hc : At a 44 c) :
    WA reduce a fun a' => (a'.m 27 = (redW4 l h c).w0 ∧ a'.m 28 = (redW4 l h c).w1 ∧ a'.m 30 = (redW4 l h c).w2 ∧
      a'.m 31 = (redW4 l h c).w3) ∧ (∀ k, k ≠ 27 → k ≠ 28 → k ≠ 30 → k ≠ 31 → a'.m k = a.m k) ∧ Keeps workLr a a' := by
  obtain ⟨l0, l1, l2, l3⟩ := hl
  obtain ⟨h0, h1, h2, h3⟩ := hh
  obtain ⟨c0, c1, c2, c3⟩ := hc
  simp only [Nat.reduceAdd] at l1 l2 l3 h1 h2 h3 c1 c2 c3
  rw [reduce, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc]
  refine WA.append (WA.mono (Q := fun b => (b.g .r4 = l.w0 ∧ b.g .r5 = l.w1 ∧ b.g .r6 = l.w2 ∧ b.g .r7 = l.w3 ∧
      b.g .r8 = h.w0 ∧ b.g .r9 = h.w1 ∧ b.g .r10 = c.w0 ^^^ l.w0 ^^^ h.w0 ^^^ l.w2 ∧
      b.g .r11 = c.w1 ^^^ l.w1 ^^^ h.w1 ^^^ l.w3) ∧ Keeps workLr a b ∧ b.m = a.m) ?_
      fun b₁ ⟨⟨g4, g5, g6, g7, g8, g9, g10, g11⟩, k₁, m₁⟩ => ?_)
  · simp only [reduceCtorEq, Nat.reduceLT, Nat.reduceAdd, and_self, ↓reduceIte, WA, ld, eor, lS, hS, cS, evalA, stepA, opA, dpA, slotOf_slot, Option.map_some,
      Option.bind_some, A.g_set, A.m_set, Option.some.injEq, exists_eq_left', l0, l1, l2, l3, h0, h1,
      c0, c1]
    refine ⟨trivial, fun r hr => ?_, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]
  refine WA.append ((foldDn_ok .r11 .r4 (by decide) (by decide) b₁).mono fun b₂ ⟨e₂, k₂, m₂⟩ => ?_)
  rw [g11, g4] at e₂
  refine WA.append (WA.mono (Q := fun b => (b.g .r8 = h.w0 ^^^ (c.w2 ^^^ l.w2 ^^^ h.w2) ^^^ l.w0 ∧ b.g .lr = h.w2) ∧
      Keeps [.r0, .lr, .r8] b₂ b ∧ b.m = a.m) ?_ fun b₃ ⟨⟨e₃, lr₃⟩, k₃, m₃⟩ => ?_)
  · have e8 : b₂.g .r8 = h.w0 := by rw [k₂ _ (by decide), g8]
    have e6 : b₂.g .r6 = l.w2 := by rw [k₂ _ (by decide), g6]
    have e4 : b₂.g .r4 = l.w0 := by rw [k₂ _ (by decide), g4]
    simp only [reduceCtorEq, Nat.reduceLT, Nat.reduceAdd, and_self, ↓reduceIte, WA, ld, eor, hS, cS, evalA, stepA, opA, dpA, slotOf_slot, Option.map_some,
      Option.bind_some, A.g_set, A.m_set, Option.some.injEq, exists_eq_left', m₂, m₁, h2, c2, e8, e6, e4]
    refine ⟨trivial, fun r hr => ?_, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]
  refine WA.append ((foldUp_ok .r8 .r4 (by decide) (by decide) b₃).mono fun b₄ ⟨e₄, k₄, m₄⟩ => ?_)
  refine WA.append ((foldDn_ok .r8 .r5 (by decide) (by decide) b₄).mono fun b₅ ⟨e₅, k₅, m₅⟩ => ?_)
  rw [e₄, e₃, k₃ _ (by decide), k₂ _ (by decide), g4, k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide), g5,
    BitVec.xor_assoc _ (up32 _)] at e₅
  refine WA.append (WA.mono (Q := fun b => (b.g .r9 = h.w1 ^^^ (c.w3 ^^^ l.w3 ^^^ h.w3) ^^^ l.w1 ∧ b.g .r7 = h.w3) ∧
      Keeps [.r6, .r7, .r9] b₅ b ∧ b.m = a.m) ?_ fun b₆ ⟨⟨e₆, e₆'⟩, k₆, m₆⟩ => ?_)
  · have e9 : b₅.g .r9 = h.w1 := by rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide), g9]
    have e7 : b₅.g .r7 = l.w3 := by rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide), g7]
    have e5 : b₅.g .r5 = l.w1 := by rw [k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide), g5]
    simp only [reduceCtorEq, Nat.reduceLT, Nat.reduceAdd, and_self, ↓reduceIte, WA, ld, eor, hS, cS, evalA, stepA, opA, dpA, slotOf_slot, Option.map_some,
      Option.bind_some, A.g_set, A.m_set, Option.some.injEq, exists_eq_left', m₅, m₄, m₃, h3, c3, e9,
      e7, e5]
    refine ⟨trivial, fun r hr => ?_, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]
  refine WA.append ((foldUp_ok .r9 .r5 (by decide) (by decide) b₆).mono fun b₇ ⟨e₇, k₇, m₇⟩ => ?_)
  refine WA.append ((foldDn_ok .r9 .r10 (by decide) (by decide) b₇).mono fun b₈ ⟨e₈, k₈, m₈⟩ => ?_)
  have x10 : b₇.g .r10 = c.w0 ^^^ l.w0 ^^^ h.w0 ^^^ l.w2 := by
    rw [k₇ _ (by decide), k₆ _ (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide), g10]
  have x5 : b₆.g .r5 = l.w1 := by
    rw [k₆ _ (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide), g5]
  rw [e₇, e₆, x5, x10] at e₈
  refine WA.append ((eor_ok .lr .lr .r10 (by decide) b₈).mono fun b₉ ⟨e₉, k₉, m₉⟩ => ?_)
  refine WA.append ((foldUp_ok .lr .r10 (by decide) (by decide) b₉).mono fun b₁₀ ⟨e₁₀, k₁₀, m₁₀⟩ => ?_)
  refine WA.append ((foldDn_ok .lr .r11 (by decide) (by decide) b₁₀).mono fun b₁₁ ⟨e₁₁, k₁₁, m₁₁⟩ => ?_)
  have xlr : b₈.g .lr = h.w2 := by
    rw [k₈ _ (by decide), k₇ _ (by decide), k₆ _ (by decide), k₅ _ (by decide), k₄ _ (by decide), lr₃]
  have y10 : b₈.g .r10 = c.w0 ^^^ l.w0 ^^^ h.w0 ^^^ l.w2 := by rw [k₈ _ (by decide), x10]
  have x11 : b₁₀.g .r11 = c.w1 ^^^ l.w1 ^^^ h.w1 ^^^ l.w3 ^^^ dn32 l.w0 := by
    rw [k₁₀ _ (by decide), k₉ _ (by decide), k₈ _ (by decide), k₇ _ (by decide), k₆ _ (by decide), k₅ _ (by decide),
      k₄ _ (by decide), k₃ _ (by decide), e₂]
  rw [e₁₀, e₉, k₉ _ (by decide), xlr, y10, x11, BitVec.xor_assoc _ (up32 _)] at e₁₁
  refine WA.append ((eor_ok .r7 .r7 .r11 (by decide) b₁₁).mono fun b₁₂ ⟨e₁₂, k₁₂, m₁₂⟩ => ?_)
  refine WA.append ((foldUp_ok .r7 .r11 (by decide) (by decide) b₁₂).mono fun b₁₃ ⟨e₁₃, k₁₃, m₁₃⟩ => ?_)
  have x7 : b₁₁.g .r7 = h.w3 := by
    rw [k₁₁ _ (by decide), k₁₀ _ (by decide), k₉ _ (by decide), k₈ _ (by decide), k₇ _ (by decide), e₆']
  rw [e₁₂, k₁₂ _ (by decide), x7, k₁₁ _ (by decide), x11] at e₁₃
  have y8 : b₁₃.g .r8 = (redW4 l h c).w0 := by
    rw [k₁₃ _ (by decide), k₁₂ _ (by decide), k₁₁ _ (by decide), k₁₀ _ (by decide), k₉ _ (by decide), k₈ _ (by decide),
      k₇ _ (by decide), k₆ _ (by decide), e₅, redW4]
  have y9 : b₁₃.g .r9 = (redW4 l h c).w1 := by
    rw [k₁₃ _ (by decide), k₁₂ _ (by decide), k₁₁ _ (by decide), k₁₀ _ (by decide), k₉ _ (by decide), e₈, redW4]
  have ylr : b₁₃.g .lr = (redW4 l h c).w2 := by rw [k₁₃ _ (by decide), k₁₂ _ (by decide), e₁₁, redW4]
  have y7 : b₁₃.g .r7 = (redW4 l h c).w3 := by rw [e₁₃, redW4]
  have hm : b₁₃.m = a.m := by rw [m₁₃, m₁₂, m₁₁, m₁₀, m₉, m₈, m₇, m₆]
  have hk : Keeps workLr a b₁₃ :=
    k₁.trans <| (k₂.mono (by decide)).trans <| (k₃.mono (by decide)).trans <| (k₄.mono (by decide)).trans <|
    (k₅.mono (by decide)).trans <| (k₆.mono (by decide)).trans <| (k₇.mono (by decide)).trans <|
    (k₈.mono (by decide)).trans <| (k₉.mono (by decide)).trans <| (k₁₀.mono (by decide)).trans <|
    (k₁₁.mono (by decide)).trans <| (k₁₂.mono (by decide)).trans <| k₁₃.mono (by decide)
  simp only [Nat.reduceEqDiff, Nat.reduceLT, and_self, ↓reduceIte, WA, st, y0S, y1S, y2S, y3S, evalA, stepA, slotOf_slot, Option.map_some,
    Option.bind_some, A.g_put, A.m_put, Option.some.injEq, exists_eq_left', y8, y9, ylr, y7, hm]
  refine ⟨trivial, fun k h1 h2 h3 h4 => ?_, hk⟩
  rw [ite_eq_right h4, ite_eq_right h3, ite_eq_right h2, ite_eq_right h1]

theorem addX_ok (a : A) :
    WA addX a fun a' =>
      (a'.m 31 = rev (a.g .r4) ^^^ a.m 31 ∧ a'.m 30 = rev (a.g .r5) ^^^ a.m 30 ∧ a'.m 28 = rev (a.g .r6) ^^^ a.m 28 ∧
        a'.m 27 = rev (a.g .r7) ^^^ a.m 27) ∧
      (a'.m 29 = a'.m 27 ^^^ a'.m 28 ∧ a'.m 32 = a'.m 30 ^^^ a'.m 31 ∧ a'.m 33 = a'.m 27 ^^^ a'.m 30 ∧
        a'.m 34 = a'.m 28 ^^^ a'.m 31 ∧ a'.m 35 = a'.m 33 ^^^ a'.m 34) ∧
      (∀ k, k < 27 ∨ 36 ≤ k → a'.m k = a.m k) ∧ Keeps workLr a a' := by
  simp only [reduceCtorEq, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceAdd, and_self, ↓reduceIte, WA, addX, revBlk, List.cons_append, List.nil_append, ld, st, eor, y0S, y1S, y2S,
    y3S, opS, evalA, stepA, opA, dpA, slotOf_slot, Option.map_some, Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put,
    Option.some.injEq, exists_eq_left', and_self]
  refine ⟨trivial, trivial, fun k hk => ?_, fun r hr => ?_⟩
  · simp only [show ¬ k = 35 by omega, show ¬ k = 34 by omega, show ¬ k = 33 by omega, show ¬ k = 32 by omega,
      show ¬ k = 29 by omega, show ¬ k = 27 by omega, show ¬ k = 28 by omega, show ¬ k = 30 by omega,
      show ¬ k = 31 by omega, ite_false]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_put, A.g_set, hr, ite_false]

/-- The key's words, of which `h₃` is `H`'s first. -/
def kws (h3 h2 h1 h0 : BitVec 32) : W4 :=
  ⟨h0 <<< 1 ^^^ h3 >>> 31, h1 <<< 1 ^^^ h0 >>> 31, h2 <<< 1 ^^^ h1 >>> 31, h3 <<< 1 ^^^ h2 >>> 31 ^^^ dn32 (h3 >>> 31)⟩

theorem adjust_ok (a : A) :
    WA adjust a fun a' => (let k := kws (a.g .r4) (a.g .r5) (a.g .r6) (a.g .r7)
      a'.g .r4 = k.w3 ∧ a'.g .r5 = k.w2 ∧ a'.g .r6 = k.w1 ∧ a'.g .r7 = k.w0) ∧ Keeps workLr a a' ∧ a'.m = a.m := by
  rw [adjust]
  refine WA.append (WA.mono (Q := fun b => (b.g .r4 = a.g .r4 <<< 1 ^^^ a.g .r5 >>> 31 ∧
      b.g .r5 = a.g .r5 <<< 1 ^^^ a.g .r6 >>> 31 ∧ b.g .r6 = a.g .r6 <<< 1 ^^^ a.g .r7 >>> 31 ∧
      b.g .r7 = a.g .r7 <<< 1 ^^^ a.g .r4 >>> 31 ∧ b.g .r8 = a.g .r4 >>> 31) ∧ Keeps workLr a b ∧ b.m = a.m) ?_
      fun b ⟨⟨e4, e5, e6, e7, e8⟩, kb, mb⟩ => ?_)
  · simp only [reduceCtorEq, Nat.reduceLeDiff, and_self, ↓reduceIte, WA, lslI, lsrI, evalA, stepA, opA, dpA, shiftA, Option.map_some,
      Option.bind_some, A.g_set, A.m_set, Option.some.injEq, exists_eq_left', and_self]
    refine ⟨trivial, fun r hr => ?_, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]
  · refine (foldDn_ok .r4 .r8 (by decide) (by decide) b).mono fun c ⟨e, kc, mc⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [e, e4, e8]; rfl
    · rw [kc _ (by decide), e5]; rfl
    · rw [kc _ (by decide), e6]; rfl
    · rw [kc _ (by decide), e7]; rfl
    · exact kb.trans (kc.mono (by decide))
    · rw [mc, mb]

theorem keyWord_ok (t : Nat) (r : Reg) (hr : r ≠ .r9) (ht : t < 9) (a : A) :
    WA (keyWord t r) a fun a' => KeyOk a' t (a.g r) ∧ (∀ k, k < 3 * t ∨ 3 * t + 3 ≤ k → a'.m k = a.m k) ∧
      Keeps [.r9, .r10] a a' := by
  simp only [WA, keyWord, lslI, lsrI, st, eor, evalA, stepA, opA, dpA, shiftA, slotOf_slot (show 3 * t < 64 by omega),
    slotOf_slot (show 3 * t + 1 < 64 by omega), slotOf_slot (show 3 * t + 2 < 64 by omega), Option.map_some,
    Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put, hr, reduceCtorEq, ite_false, ite_true, Option.some.injEq,
    exists_eq_left', Nat.reduceLeDiff, and_self, KeyOk, show ¬ 3 * t = 3 * t + 1 by omega,
    show ¬ 3 * t = 3 * t + 2 by omega, show ¬ 3 * t + 1 = 3 * t + 2 by omega]
  refine ⟨⟨rfl, rfl, rfl⟩, fun k hk => ?_, fun q hq => ?_⟩
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [A.g_put, A.g_set, hq, ite_false]

/-- The words the code multiplies by. -/
def kt (k : W4) (t : Nat) : BitVec 32 :=
  match t with
  | 0 => k.w0 | 1 => k.w1 | 2 => k.w0 ^^^ k.w1 | 3 => k.w2 | 4 => k.w3 | 5 => k.w2 ^^^ k.w3
  | 6 => k.w0 ^^^ k.w2 | 7 => k.w1 ^^^ k.w3 | _ => (k.w0 ^^^ k.w2) ^^^ (k.w1 ^^^ k.w3)

/-- The first `n` of them are in place. -/
def KeysTo (a : A) (k : W4) (n : Nat) : Prop := ∀ t < n, KeyOk a t (kt k t)

theorem KeysTo.word {a b : A} {k : W4} {n : Nat} (h : KeysTo a k n) (hk : KeyOk b n (kt k n))
    (hm : ∀ j, j < 3 * n ∨ 3 * n + 3 ≤ j → b.m j = a.m j) : KeysTo b k (n + 1) := by
  intro t ht
  by_cases e : t = n
  · subst e; exact hk
  · obtain ⟨h1, h2, h3⟩ := h t (by omega)
    exact ⟨by rw [hm _ (by omega), h1], by rw [hm _ (by omega), h2], by rw [hm _ (by omega), h3]⟩

theorem KeysTo.mem {a b : A} {k : W4} {n : Nat} (h : KeysTo a k n) (hm : b.m = a.m) : KeysTo b k n := by
  intro t ht; rw [KeyOk, hm]; exact h t ht

/-- A word of the key, then a sum. -/
theorem step_key {a : A} {k : W4} {n : Nat} {r : Reg} {is : List Instr} {Q : A → Prop} (h : KeysTo a k n) (hn : n < 9)
    (hr : r ≠ .r9) (hv : a.g r = kt k n)
    (hq : ∀ b, KeysTo b k (n + 1) → Keeps [.r9, .r10] a b → (∀ j, 27 ≤ j → b.m j = a.m j) → WA is b Q) :
    WA (keyWord n r ++ is) a Q :=
  WA.append ((keyWord_ok n r hr hn a).mono fun b ⟨e, m, g⟩ =>
    hq b (h.word (hv ▸ e) m) g fun j hj => m j (by omega))

theorem step_sum {a : A} {is : List Instr} {Q : A → Prop} (d n m : Reg) (hd : d ≠ .r12)
    (hq : ∀ b, b.g d = a.g n ^^^ a.g m → Keeps [d] a b → b.m = a.m → WA is b Q) : WA (keySum d n m ++ is) a Q :=
  WA.append ((eor_ok d n m hd a).mono fun b ⟨e, g, m⟩ => hq b e g m)

theorem keyCode_ok (a : A) :
    WA keyCode a fun a' => KeysTo a' (kws (a.g .r4) (a.g .r5) (a.g .r6) (a.g .r7)) 9 ∧
      (∀ j, 27 ≤ j → a'.m j = a.m j) ∧ Keeps workLr a a' := by
  rw [keyCode]
  simp only [List.append_assoc]
  refine WA.append ((adjust_ok a).mono fun b ⟨⟨e4, e5, e6, e7⟩, gb, mb⟩ => ?_)
  generalize hk : kws (a.g .r4) (a.g .r5) (a.g .r6) (a.g .r7) = k at e4 e5 e6 e7 ⊢
  refine step_key (k := k) (n := 0) (fun t ht => absurd ht (Nat.not_lt_zero t)) (by decide) (by decide) e7 fun b₀ K₀ g₀ m₀ => ?_
  refine step_key K₀ (by decide) (by decide) (by rw [g₀ _ (by decide), e6]; rfl) fun b₁ K₁ g₁ m₁ => ?_
  have G₁ := g₀.trans g₁
  refine step_sum _ _ _ (by decide) fun b₂ e₂ g₂ m₂ => ?_
  rw [G₁ _ (by decide), G₁ _ (by decide), e6, e7] at e₂
  have G₂ : Keeps [.r8, .r9, .r10] b b₂ := (G₁.mono (by decide)).trans (g₂.mono (by decide))
  refine step_key (K₁.mem m₂) (by decide) (by decide) (by rw [e₂]; rfl) fun b₃ K₃ g₃ m₃ => ?_
  have G₃ : Keeps [.r8, .r9, .r10] b b₃ := G₂.trans (g₃.mono (by decide))
  refine step_key K₃ (by decide) (by decide) (by rw [G₃ _ (by decide), e5]; rfl) fun b₄ K₄ g₄ m₄ => ?_
  have G₄ : Keeps [.r8, .r9, .r10] b b₄ := G₃.trans (g₄.mono (by decide))
  refine step_key K₄ (by decide) (by decide) (by rw [G₄ _ (by decide), e4]; rfl) fun b₅ K₅ g₅ m₅ => ?_
  have G₅ : Keeps [.r8, .r9, .r10] b b₅ := G₄.trans (g₅.mono (by decide))
  refine step_sum _ _ _ (by decide) fun b₆ e₆ g₆ m₆ => ?_
  rw [G₅ _ (by decide), G₅ _ (by decide), e5, e4] at e₆
  have G₆ : Keeps [.r8, .r9, .r10] b b₆ := G₅.trans (g₆.mono (by decide))
  refine step_key (K₅.mem m₆) (by decide) (by decide) (by rw [e₆]; rfl) fun b₇ K₇ g₇ m₇ => ?_
  have G₇ : Keeps [.r8, .r9, .r10] b b₇ := G₆.trans (g₇.mono (by decide))
  refine step_sum _ _ _ (by decide) fun b₈ e₈ g₈ m₈ => ?_
  rw [G₇ _ (by decide), G₇ _ (by decide), e7, e5] at e₈
  have G₈ : Keeps [.r7, .r8, .r9, .r10] b b₈ := (G₇.mono (by decide)).trans (g₈.mono (by decide))
  refine step_key (K₇.mem m₈) (by decide) (by decide) (by rw [e₈]; rfl) fun b₉ K₉ g₉ m₉ => ?_
  have G₉ : Keeps [.r7, .r8, .r9, .r10] b b₉ := G₈.trans (g₉.mono (by decide))
  refine step_sum _ _ _ (by decide) fun c₀ f₀ h₀ n₀ => ?_
  rw [G₉ _ (by decide), G₉ _ (by decide), e6, e4] at f₀
  have H₀ : Keeps [.r6, .r7, .r8, .r9, .r10] b c₀ := (G₉.mono (by decide)).trans (h₀.mono (by decide))
  refine step_key (K₉.mem n₀) (by decide) (by decide) (by rw [f₀]; rfl) fun c₁ L₁ h₁ n₁ => ?_
  have H₁ : Keeps [.r6, .r7, .r8, .r9, .r10] b c₁ := H₀.trans (h₁.mono (by decide))
  refine step_sum _ _ _ (by decide) fun c₂ f₂ h₂ n₂ => ?_
  rw [h₁ _ (by decide), h₁ _ (by decide), f₀, h₀ _ (by decide), g₉ _ (by decide), e₈] at f₂
  have H₂ : Keeps [.r6, .r7, .r8, .r9, .r10] b c₂ := H₁.trans (h₂.mono (by decide))
  refine (keyWord_ok 8 .r8 (by decide) (by decide) c₂).mono fun c₃ ⟨f₃, n₃, h₃⟩ => ⟨?_, fun j hj => ?_, ?_⟩
  · exact (L₁.mem n₂).word ((congrArg (KeyOk c₃ 8) f₂).mp f₃) n₃
  · rw [n₃ j (by omega), n₂, n₁ j hj, n₀, m₉ j hj, m₈, m₇ j hj, m₆, m₅ j hj, m₄ j hj, m₃ j hj, m₂, m₁ j hj, m₀ j hj, mb]
  · exact gb.trans ((H₂.mono (by decide)).trans (h₃.mono (by decide)))

theorem setMask_ok (r : Nat) (a : A) :
    WA (setMask r) a fun a' => a'.g (maskReg r) = c3 r ∧ Keeps [maskReg r] a a' ∧ a'.m = a.m := by
  have hr : maskReg r ≠ .r12 := by unfold maskReg; split <;> decide
  simp only [WA, setMask, evalA, stepA, hr, Option.bind_some, A.g_set, A.m_set, ite_false, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hq => ?_, trivial⟩
  · rw [movw_movt, mask_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [A.g_set, hq, ite_false]

/-- A block's arithmetic, its words in `r4`–`r7`. -/
def core : List Instr := addX ++ mul64 0 lS ++ mul64 3 hS ++ mul64 6 cS ++ reduce

/-- The block of the words `y₃` to `y₀` in `scratch`. -/
def yOf (a : A) : BitVec 128 := w4 (a.m 31) (a.m 30) (a.m 28) (a.m 27)

theorem core_ok {a : A} {h3 h2 h1 h0 : BitVec 32} (hM : Masks a) (hK : KeysTo a (kws h3 h2 h1 h0) 9) :
    WA core a fun a' =>
      yOf a' = Spec.Gcm.mul (w4 (rev (a.g .r4) ^^^ a.m 31) (rev (a.g .r5) ^^^ a.m 30) (rev (a.g .r6) ^^^ a.m 28)
        (rev (a.g .r7) ^^^ a.m 27)) (w4 h3 h2 h1 h0) ∧
      (∀ k, k < 27 ∨ 50 ≤ k → a'.m k = a.m k) ∧ Keeps workLr a a' := by
  have hKm : ∀ {b : A}, (∀ k < 27, b.m k = a.m k) → KeysTo b (kws h3 h2 h1 h0) 9 := fun {b} hb t ht => by
    obtain ⟨k1, k2, k3⟩ := hK t ht
    exact ⟨by rw [hb _ (by omega), k1], by rw [hb _ (by omega), k2], by rw [hb _ (by omega), k3]⟩
  rw [core, List.append_assoc, List.append_assoc, List.append_assoc]
  refine WA.append ((addX_ok a).mono fun b ⟨⟨x3, x2, x1, x0⟩, ⟨s2, s5, s6, s7, s8⟩, mb, gb⟩ => ?_)
  have Kb := hKm (b := b) fun k hk => mb k (.inl hk)
  refine WA.append ((mul64_ok 0 36 (by decide) (.inl rfl) _ _ b (hM.keeps gb (by decide) (by decide) (by decide))
    ⟨Kb 0 (by decide), Kb 1 (by decide), Kb 2 (by decide)⟩ s2).mono fun c ⟨pc, gc, mc⟩ => ?_)
  have Kc := hKm (b := c) fun k hk => by rw [mc k (by omega) (by omega), mb k (.inl hk)]
  have gc' := gb.trans gc
  refine WA.append ((mul64_ok 3 40 (by decide) (.inr (.inl rfl)) _ _ c (hM.keeps gc' (by decide) (by decide) (by decide))
    ⟨Kc 3 (by decide), Kc 4 (by decide), Kc 5 (by decide)⟩ (by
      rw [mc _ (by decide) (by decide), mc _ (by decide) (by decide), mc _ (by decide) (by decide)]; exact s5)).mono
    fun d ⟨pd, gd, md⟩ => ?_)
  have Kd := hKm (b := d) fun k hk => by rw [md k (by omega) (by omega), mc k (by omega) (by omega), mb k (.inl hk)]
  have gd' := gc'.trans gd
  have Md : ∀ k < 36, d.m k = b.m k := fun k hk => by rw [md k (by omega) (by omega), mc k (by omega) (by omega)]
  refine WA.append ((mul64_ok 6 44 (by decide) (.inr (.inr rfl)) _ _ d (hM.keeps gd' (by decide) (by decide) (by decide))
    ⟨Kd 6 (by decide), Kd 7 (by decide), Kd 8 (by decide)⟩ (by
      rw [Md _ (by decide), Md _ (by decide), Md _ (by decide)]; exact s8)).mono
    fun e ⟨pe, ge, me⟩ => ?_)
  have pc' : At e 36 _ := ⟨by rw [me _ (by decide) (by decide), md _ (by decide) (by decide)]; exact pc.1,
    by rw [me _ (by decide) (by decide), md _ (by decide) (by decide)]; exact pc.2.1,
    by rw [me _ (by decide) (by decide), md _ (by decide) (by decide)]; exact pc.2.2.1,
    by rw [me _ (by decide) (by decide), md _ (by decide) (by decide)]; exact pc.2.2.2⟩
  have pd' : At e 40 _ := ⟨by rw [me _ (by decide) (by decide)]; exact pd.1, by rw [me _ (by decide) (by decide)]; exact pd.2.1,
    by rw [me _ (by decide) (by decide)]; exact pd.2.2.1, by rw [me _ (by decide) (by decide)]; exact pd.2.2.2⟩
  refine (reduce_ok pc' pd' pe).mono fun f ⟨⟨z0, z1, z2, z3⟩, mf, gf⟩ => ⟨?_, fun k hk => ?_, ?_⟩
  · have y33 : d.m 33 = b.m 27 ^^^ b.m 30 := by rw [Md _ (by decide), s6]
    have y34 : d.m 34 = b.m 28 ^^^ b.m 31 := by rw [Md _ (by decide), s7]
    have y30 : c.m 30 = b.m 30 := mc _ (by decide) (by decide)
    have y31 : c.m 31 = b.m 31 := mc _ (by decide) (by decide)
    simp only [Nat.reduceAdd, y33, y34, y30, y31] at z0 z1 z2 z3
    rw [yOf, z0, z1, z2, z3, ← x3, ← x2, ← x1, ← x0, w4_eq, w4_eq, w4_eq]
    exact mul_words32 Spread.isMul_mul32 ..
  · rw [mf k (by omega) (by omega) (by omega) (by omega), me k (by omega) (by omega), md k (by omega) (by omega),
      mc k (by omega) (by omega), mb k (by omega)]
  · exact gd'.trans (ge.trans gf)

/-! ## The whole function -/

section
variable (s₀ : State)

abbrev hA : Addr := State.addr (s₀.gpr .r0)
abbrev yp : Addr := State.addr (s₀.gpr .r1)
abbrev dp : Addr := State.addr (s₀.gpr .r2)
abbrev nb : Nat := (s₀.gpr .r3).toNat
abbrev hR : Region := ⟨hA s₀, 16⟩
abbrev yR : Region := ⟨yp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
abbrev scrR : Region := ⟨State.addr (scr s₀), 256⟩
abbrev H₀ : Block := blockAt s₀.mem (hA s₀)
abbrev Y₀ : Block := blockAt s₀.mem (yp s₀)

/-- The address of block `i`, in 32 bits. -/
abbrev blk (i : Nat) : BitVec 32 := s₀.gpr .r2 + BitVec.ofNat 32 (16 * i)

/-- The words of a block. -/
abbrev wd (p : Addr) (o : Nat) : BitVec 32 := rev (s₀.mem.readW (p + BitVec.ofNat 64 o) 32)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [hR s₀, dR s₀, argR s₀]
  wr : s₀.wr = [yR s₀, scrR s₀]
  h_s : (hR s₀).Disjoint (scrR s₀)
  y_s : (yR s₀).Disjoint (scrR s₀)
  d_s : (dR s₀).Disjoint (scrR s₀)
  fh : (s₀.gpr .r0).toNat + 16 ≤ 2 ^ 32
  fy : (s₀.gpr .r1).toNat + 16 ≤ 2 ^ 32
  fd : (s₀.gpr .r2).toNat + 16 * nb s₀ ≤ 2 ^ 32
  fs : (scr s₀).toNat + 256 ≤ 2 ^ 32
  fp : s₀.sp.toNat + 4 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : ghashArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, -, h4, -, h6, h7, -, -, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h4, h6, h7, h8, h9, h10, h11, h12⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem toScr : Scr s₀ := ⟨by rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..), h.fs⟩
theorem mem_h : hR s₀ ∈ s₀.rd ++ s₀.wr := by rw [h.rd]; exact List.mem_cons_self ..
theorem mem_d : dR s₀ ∈ s₀.rd ++ s₀.wr := by rw [h.rd]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
theorem mem_y : yR s₀ ∈ s₀.rd ++ s₀.wr := by rw [h.wr]; exact List.mem_append_right _ (List.mem_cons_self ..)

end Pre

/-- A load from a region disjoint from `scratch`. -/
theorem ext_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) {d b : Reg} (hd : d ≠ .r12) (o : Nat) (ho : o < 4096) {R : Region}
    {p : BitVec 32} (hR : R ∈ s₀.rd ++ s₀.wr) (hdis : R.Disjoint (scrR s₀)) (hp : a.g b = p) (hf : p.toNat + o < 2 ^ 32)
    (hc : R.Contains (State.addr p + BitVec.ofNat 64 o) 4) {is : List Instr} {Q : State → Prop}
    (hq : ∀ s', Rel s₀ s' (a.set d (s₀.mem.readW (State.addr p + BitVec.ofNat 64 o) 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr d b o :: is)) s Q := by
  have he : State.addr (s.gpr b + BitVec.ofNat 32 o) = State.addr p + BitVec.ofNat 64 o := by
    rw [h.g, hp, addr_add hf]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldr ho (by rw [he, h.rd, h.wr]; exact ⟨R, hR, hc⟩), hq _ ?_⟩
  rw [he, h.m.frame.readW hc (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hdis) (by decide)]
  exact h.set hd _

/-- The four words of a block, as loaded. -/
structure Blk (s₀ : State) (p : Addr) (a a' : A) : Prop where
  r4 : rev (a'.g .r4) = wd s₀ p 0
  r5 : rev (a'.g .r5) = wd s₀ p 4
  r6 : rev (a'.g .r6) = wd s₀ p 8
  r7 : rev (a'.g .r7) = wd s₀ p 12
  k : Keeps [.r4, .r5, .r6, .r7] a a'
  m : a'.m = a.m

theorem loadBlk_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) {b : Reg} (hb : b = .r0 ∨ b = .r1 ∨ b = .r11) {R : Region}
    {p : BitVec 32} (hR : R ∈ s₀.rd ++ s₀.wr) (hdis : R.Disjoint (scrR s₀)) (hp : a.g b = p) (hf : p.toNat + 16 ≤ 2 ^ 32)
    (hc : ∀ o ≤ 12, R.Contains (State.addr p + BitVec.ofNat 64 o) 4) :
    WP isa (.block (loadBlk b)) s fun s' => ∃ a', Rel s₀ s' a' ∧ Blk s₀ (State.addr p) a a' := by
  have hb' : ∀ q ∈ [Reg.r4, .r5, .r6, .r7], b ≠ q := by rcases hb with rfl | rfl | rfl <;> decide
  have b4 := hb' .r4 (by decide)
  have b5 := hb' .r5 (by decide)
  have b6 := hb' .r6 (by decide)
  refine ext_ok h (by decide) 0 (by decide) hR hdis hp (by omega) (hc 0 (by decide)) fun s₁ r₁ => ?_
  refine ext_ok r₁ (by decide) 4 (by decide) hR hdis (by simp only [A.g_set, b4, ite_false, hp]) (by omega)
    (hc 4 (by decide)) fun s₂ r₂ => ?_
  refine ext_ok r₂ (by decide) 8 (by decide) hR hdis (by simp only [A.g_set, b4, b5, ite_false, hp]) (by omega)
    (hc 8 (by decide)) fun s₃ r₃ => ?_
  refine ext_ok r₃ (by decide) 12 (by decide) hR hdis (by simp only [A.g_set, b4, b5, b6, ite_false, hp]) (by omega)
    (hc 12 (by decide)) fun s₄ r₄ => WP.block_nil ⟨_, r₄, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, rfl⟩
  · simp only [A.g_set, reduceCtorEq, ite_false, ite_true]
  · simp only [A.g_set, reduceCtorEq, ite_false, ite_true]
  · simp only [A.g_set, reduceCtorEq, ite_false, ite_true]
  · simp only [A.g_set, ite_true]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [A.g_set, hr, ite_false]

theorem wd_block (s₀ : State) (p : Addr) : w4 (wd s₀ p 0) (wd s₀ p 4) (wd s₀ p 8) (wd s₀ p 12) = blockAt s₀.mem p := by
  rw [blockAt_rev, wd, show p + BitVec.ofNat 64 0 = p from BitVec.add_zero p]

theorem w4_xor (a b c d e f g h : BitVec 32) :
    w4 (a ^^^ e) (b ^^^ f) (c ^^^ g) (d ^^^ h) = w4 a b c d ^^^ w4 e f g h := by
  rw [w4_eq, w4_eq, w4_eq, ← Spread.xor_append', ← Spread.xor_append']
  exact BitVec.xor_append.symm

/-! ### The invariant -/

structure InvA (s₀ : State) (i : Nat) (a : A) : Prop where
  masks : Masks a
  key : KeysTo a (kws (wd s₀ (hA s₀) 0) (wd s₀ (hA s₀) 4) (wd s₀ (hA s₀) 8) (wd s₀ (hA s₀) 12)) 9
  sav : ∀ q ∈ saved, a.m q.2 = s₀.gpr q.1
  y : yOf a = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)
  yp : a.m ypS = s₀.gpr .r1
  dp : a.m dpS = blk s₀ i
  n : a.m nS = BitVec.ofNat 32 (nb s₀ - i)

def Inv (s₀ : State) (i : Nat) (s : State) : Prop := i ≤ nb s₀ ∧ ∃ a, Rel s₀ s a ∧ InvA s₀ i a

theorem ofNat_sub_ofNat {n k : Nat} (h : k ≤ n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 32 n - BitVec.ofNat 32 k = BitVec.ofNat 32 (n - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem beq_ofNat_zero {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases h : k = 0
  · subst h; rfl
  · have : BitVec.ofNat 32 k ≠ 0 := fun e => h (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this)
    rw [beq_eq_false_iff_ne.mpr this]; simp only [h, decide_false]

/-- A comparison with zero. -/
theorem cmp_ok {s₀ s : State} {a : A} (h : Rel s₀ s a) {k : Nat} (hk : k < 2 ^ 32) (hn : a.g .r4 = BitVec.ofNat 32 k) :
    WP isa (.block [.cmp .r4 (.imm 0)]) s fun s' => Rel s₀ s' a ∧ s'.z = decide (k = 0) := by
  refine WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil ⟨⟨h.g, h.m, h.r12, h.sp, h.rd, h.wr⟩, ?_⟩⟩
  show (s.gpr .r4 - 0 == 0) = _
  rw [show s.gpr .r4 - 0 = s.gpr .r4 from BitVec.sub_zero _, h.g, hn, beq_ofNat_zero hk]

theorem load_ok (d : Reg) (hd : d ≠ .r12) (k : Nat) (hk : k < 64) (a : A) :
    WA [ld d k] a fun a' => a'.g d = a.m k ∧ Keeps [d] a a' ∧ a'.m = a.m := by
  simp only [WA, ld, evalA, stepA, hd, slotOf_slot hk, Option.map_some, Option.bind_some, A.g_set, A.m_set, ite_false,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_set, hr, ite_false]

theorem advance_ok (a : A) :
    WA [.dp .add .r11 .r11 (.imm 16), st .r11 dpS] a fun a' => a'.m dpS = a.g .r11 + 16 ∧
      (∀ k, k ≠ dpS → a'.m k = a.m k) ∧ Keeps [.r11] a a' := by
  have e : encodable 16 = true := by decide
  simp only [WA, st, dpS, evalA, stepA, opA, dpA, e, slotOf_slot (show 60 < 64 by decide), reduceCtorEq, Option.map_some,
    Option.bind_some, A.g_set, A.m_set, A.m_put, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun k hk => ite_eq_right hk, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_put, A.g_set, hr, ite_false]

theorem next_ok (a : A) :
    WA next a fun a' => a'.m nS = a.m nS - 1 ∧ a'.g .r4 = a.m nS - 1 ∧ (∀ k, k ≠ nS → a'.m k = a.m k) ∧
      Keeps [.r4] a a' := by
  have e : encodable 1 = true := by decide
  simp only [WA, next, ld, st, nS, evalA, stepA, opA, dpA, e, slotOf_slot (show 61 < 64 by decide), reduceCtorEq,
    Option.map_some, Option.bind_some, A.g_set, A.m_set, A.g_put, A.m_put, ite_false, ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, fun k hk => ite_eq_right hk, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [A.g_put, A.g_set, hr, ite_false]

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block body) s fun s' => Inv s₀ (i + 1) s' ∧ s'.z = decide (nb s₀ - (i + 1) = 0) := by
  have hf := hp.fd
  have hn : nb s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt
  obtain ⟨-, a, hr, ha⟩ := hI
  have hbody : body = [ld .r11 dpS] ++ (loadBlk .r11 ++ ([.dp .add .r11 .r11 (.imm 16), st .r11 dpS] ++
      (core ++ (next ++ [.cmp .r4 (.imm 0)])))) := by simp only [body, core, loadX, List.append_assoc]
  obtain ⟨hba, hbf⟩ : State.addr (blk s₀ i) = dp s₀ + BitVec.ofNat 64 (16 * i) ∧ (blk s₀ i).toNat + 16 ≤ 2 ^ 32 := by
    have e : (blk s₀ i).toNat = (s₀.gpr .r2).toNat + 16 * i := by
      rw [blk, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * i) (by omega), Nat.mod_eq_of_lt (by omega)]
    exact ⟨addr_add (by omega), by omega⟩
  rw [hbody, WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr hr (load_ok .r11 (by decide) dpS (by decide) a)) fun s₁ ⟨a₁, r₁, e₁, k₁, m₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadBlk_ok r₁ (.inr (.inr rfl)) hp.mem_d hp.d_s (e₁.trans ha.dp) hbf (fun o ho => by
    rw [hba, Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega))) fun s₂ ⟨a₂, r₂, B⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₂ (advance_ok a₂)) fun s₃ ⟨a₃, r₃, e₃, m₃, k₃⟩ => ?_
  have m₃' : ∀ k, k ≠ dpS → a₃.m k = a.m k := fun k hk => by rw [m₃ k hk, B.m, m₁]
  have K₃ : Keeps workLr a a₃ := (k₁.mono (by decide)).trans ((B.k.mono (by decide)).trans (k₃.mono (by decide)))
  have key₃ : KeysTo a₃ _ 9 := fun t ht => by
    obtain ⟨h1, h2, h3⟩ := ha.key t ht
    exact ⟨by rw [m₃' _ (by unfold dpS; omega), h1], by rw [m₃' _ (by unfold dpS; omega), h2],
      by rw [m₃' _ (by unfold dpS; omega), h3]⟩
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₃ (core_ok (ha.masks.keeps K₃ (by decide) (by decide) (by decide)) key₃))
    fun s₄ ⟨a₄, r₄, y₄, m₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₄ (next_ok a₄)) fun s₅ ⟨a₅, r₅, n₅, n₅', m₅, k₅⟩ => ?_
  have hcnt : a₄.m nS - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [m₄ nS (by decide), m₃' nS (by decide), ha.n]
    exact ofNat_sub_ofNat (k := 1) (by omega) (by omega)
  have m₅' : ∀ k, 50 ≤ k → k ≠ dpS → k ≠ nS → a₅.m k = a.m k := fun k h1 h2 h3 => by
    rw [m₅ k h3, m₄ k (.inr h1), m₃' k h2]
  have m₅'' : ∀ k, k < 27 → a₅.m k = a.m k := fun k h => by
    rw [m₅ k (by unfold nS; omega), m₄ k (.inl h), m₃' k (by unfold dpS; omega)]
  refine WP.mono (cmp_ok r₅ (by omega) (n₅'.trans hcnt)) fun s₆ ⟨r₆, z₆⟩ => ⟨⟨hi, a₅, r₆, ?_⟩, z₆⟩
  refine ⟨?_, fun t ht => ?_, fun q hq => ?_, ?_, ?_, ?_, n₅.trans hcnt⟩
  · exact ha.masks.keeps (K₃.trans (k₄.trans (k₅.mono (by decide)))) (by decide) (by decide) (by decide)
  · obtain ⟨h1, h2, h3⟩ := ha.key t ht
    exact ⟨by rw [m₅'' _ (by omega), h1], by rw [m₅'' _ (by omega), h2], by rw [m₅'' _ (by omega), h3]⟩
  · have hq' : ∀ q ∈ saved, 50 ≤ q.2 ∧ q.2 ≠ dpS ∧ q.2 ≠ nS := by decide
    obtain ⟨h1, h2, h3⟩ := hq' q hq
    rw [m₅' _ h1 h2 h3, ha.sav q hq]
  · have e : yOf a₅ = yOf a₄ := by
      rw [yOf, m₅ 31 (by decide), m₅ 30 (by decide), m₅ 28 (by decide), m₅ 27 (by decide)]; rfl
    rw [e, y₄, m₃' 31 (by decide), m₃' 30 (by decide), m₃' 28 (by decide), m₃' 27 (by decide), k₃ _ (by decide),
      k₃ _ (by decide), k₃ _ (by decide), k₃ _ (by decide), B.r4, B.r5, B.r6, B.r7, w4_xor, wd_block, wd_block, hba,
      ghashFrom_blocksAt_succ, ← ha.y, BitVec.xor_comm]
    rfl
  · rw [m₅' ypS (by decide) (by decide) (by decide), ha.yp]
  · rw [m₅ dpS (by decide), m₄ dpS (by decide), e₃, B.k _ (by decide), e₁, ha.dp, blk, blk, BitVec.add_assoc, Nat.mul_succ,
      BitVec.ofNat_add]
    rfl

/-! ### The prologue and the epilogue -/

theorem save_ok (a : A) :
    WA (save ++ [st .r1 ypS, st .r2 dpS, st .r3 nS]) a fun a' => (∀ q ∈ saved, a'.m q.2 = a.g q.1) ∧
      a'.m ypS = a.g .r1 ∧ a'.m dpS = a.g .r2 ∧ a'.m nS = a.g .r3 ∧ a'.g = a.g := by
  simp only [Nat.reduceEqDiff, Nat.reduceLT, and_self, ↓reduceIte, WA, save, saved, ypS, dpS, nS, st, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, evalA, stepA, slotOf_slot,
    Option.map_some, Option.bind_some, A.g_put, A.m_put, Option.some.injEq, exists_eq_left', List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_self]

theorem rev_ok (a : A) :
    WA revBlk a fun a' => (a'.g .r4 = rev (a.g .r4) ∧ a'.g .r5 = rev (a.g .r5) ∧ a'.g .r6 = rev (a.g .r6) ∧
      a'.g .r7 = rev (a.g .r7)) ∧ Keeps [.r4, .r5, .r6, .r7] a a' ∧ a'.m = a.m := by
  simp only [WA, revBlk, evalA, stepA, reduceCtorEq, Option.bind_some, A.g_set, A.m_set, ite_false, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨trivial, trivial, trivial, trivial⟩, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [A.g_set, hr, ite_false]

theorem storeYs_ok (a : A) :
    WA storeYs a fun a' => yOf a' = w4 (a.g .r4) (a.g .r5) (a.g .r6) (a.g .r7) ∧
      (∀ k, k < 27 ∨ 32 ≤ k → a'.m k = a.m k) ∧ a'.g = a.g := by
  simp only [Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte, WA, storeYs, yOf, st, y0S, y1S, y2S, y3S, evalA, stepA, slotOf_slot,
    Option.map_some, Option.bind_some, A.g_put, A.m_put, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun k hk => ?_, trivial⟩
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem masks_ok (a : A) :
    WA (setMask 0 ++ (setMask 1 ++ (setMask 2 ++ [ld .r4 nS]))) a fun a' => Masks a' ∧ a'.g .r4 = a.m nS ∧ a'.m = a.m := by
  refine WA.append ((setMask_ok 0 a).mono fun b ⟨e₁, k₁, m₁⟩ => ?_)
  refine WA.append ((setMask_ok 1 b).mono fun c ⟨e₂, k₂, m₂⟩ => ?_)
  refine WA.append ((setMask_ok 2 c).mono fun d ⟨e₃, k₃, m₃⟩ => ?_)
  refine (load_ok .r4 (by decide) nS (by decide) d).mono fun e ⟨e₄, k₄, m₄⟩ => ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide)]; exact e₁
  · rw [k₄ _ (by decide), k₃ _ (by decide)]; exact e₂
  · rw [k₄ _ (by decide)]; exact e₃
  · rw [e₄, m₃, m₂, m₁]
  · rw [m₄, m₃, m₂, m₁]

theorem revKey_ok {s₀ : State} {a₁ a : A} {p : Addr} (B : Blk s₀ p a₁ a) :
    WA (revBlk ++ keyCode) a fun a' => KeysTo a' (kws (wd s₀ p 0) (wd s₀ p 4) (wd s₀ p 8) (wd s₀ p 12)) 9 ∧
      (∀ j, 27 ≤ j → a'.m j = a.m j) ∧ Keeps workLr a a' := by
  refine WA.append ((rev_ok a).mono fun b ⟨⟨e4, e5, e6, e7⟩, gb, mb⟩ => ?_)
  refine (keyCode_ok b).mono fun c ⟨K, mc, gc⟩ => ⟨?_, fun j hj => by rw [mc j hj, mb], (gb.mono (by decide)).trans gc⟩
  rwa [e4, e5, e6, e7, B.r4, B.r5, B.r6, B.r7] at K

theorem revY_ok {s₀ : State} {a₁ a : A} {p : Addr} (B : Blk s₀ p a₁ a) :
    WA (revBlk ++ storeYs) a fun a' => yOf a' = w4 (wd s₀ p 0) (wd s₀ p 4) (wd s₀ p 8) (wd s₀ p 12) ∧
      (∀ k, k < 27 ∨ 32 ≤ k → a'.m k = a.m k) := by
  refine WA.append ((rev_ok a).mono fun b ⟨⟨e4, e5, e6, e7⟩, _, mb⟩ => ?_)
  refine (storeYs_ok b).mono fun c ⟨y, mc, _⟩ => ⟨?_, fun k hk => by rw [mc k hk, mb]⟩
  rw [y, e4, e5, e6, e7, B.r4, B.r5, B.r6, B.r7]

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block prologue) s₀ fun s' => Inv s₀ 0 s' ∧ s'.z = decide (nb s₀ = 0) := by
  have hpr : prologue = .ldrSp .r12 0 :: ((save ++ [st .r1 ypS, st .r2 dpS, st .r3 nS]) ++ (loadBlk .r0 ++
      ((revBlk ++ keyCode) ++ (loadBlk .r1 ++ ((revBlk ++ storeYs) ++ ((setMask 0 ++ (setMask 1 ++ (setMask 2 ++
      [ld .r4 nS]))) ++ [.cmp .r4 (.imm 0)])))))) := by
    simp only [prologue, List.append_assoc, List.cons_append, List.nil_append]
  have hsp : State.addr (s₀.sp + BitVec.ofNat 32 0) = stackArgAddr s₀ 0 := rfl
  have h0 : exec (.ldrSp .r12 0) s₀ = some (s₀.setReg .r12 (scr s₀)) := by
    show (if 0 < 4096 then (s₀.load32 _).map _ else none) = _
    rw [ite_eq_left (by decide), State.load32, hsp, ite_eq_left ⟨argR s₀, by
      rw [hp.rd]; exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
      Region.contains_self _ _⟩]
    rfl
  have r₀ : Rel s₀ (s₀.setReg .r12 (scr s₀)) ⟨(s₀.setReg .r12 (scr s₀)).gpr,
      fun k => s₀.mem.readW (State.addr (scr s₀) + BitVec.ofNat 64 (4 * k)) 32⟩ :=
    ⟨rfl, Slots32.init _ _ _, rfl, rfl, rfl, rfl⟩
  have gs : ∀ r, r ≠ .r12 → (s₀.setReg .r12 (scr s₀)).gpr r = s₀.gpr r := fun r hr => ite_eq_right hr
  rw [hpr]
  refine WP.block_cons_iff.mpr ⟨_, h0, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₀ (save_ok _)) fun s₁ ⟨a₁, r₁, hs, hy, hd, hn, hg⟩ => ?_
  have hg' : ∀ r, r ≠ .r12 → a₁.g r = s₀.gpr r := fun r hr => by rw [hg]; exact gs r hr
  rw [WP.block_append_iff]
  refine WP.mono (loadBlk_ok r₁ (.inl rfl) hp.mem_h hp.h_s (hg' .r0 (by decide)) hp.fh
    (fun o ho => Offset.contains_base _ (by omega) (by omega))) fun s₂ ⟨a₂, r₂, B⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₂ (revKey_ok B)) fun s₃ ⟨a₃, r₃, K₃, m₃, g₃⟩ => ?_
  rw [B.m] at m₃
  have G₃ : Keeps workLr a₁ a₃ := (B.k.mono (by decide)).trans g₃
  rw [WP.block_append_iff]
  refine WP.mono (loadBlk_ok r₃ (.inr (.inl rfl)) hp.mem_y hp.y_s ((G₃ _ (by decide)).trans (hg' .r1 (by decide))) hp.fy
    (fun o ho => Offset.contains_base _ (by omega) (by omega))) fun s₄ ⟨a₄, r₄, C⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₄ (revY_ok C)) fun s₅ ⟨a₅, r₅, y₅, m₅⟩ => ?_
  rw [C.m] at m₅
  rw [WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r₅ (masks_ok a₅)) fun s₆ ⟨a₆, r₆, M₆, n₆, m₆⟩ => ?_
  have hm : ∀ k, 32 ≤ k → a₆.m k = a₁.m k := fun k hk => by rw [m₆, m₅ k (.inr hk), m₃ k (by omega)]
  have hcnt : a₆.m nS = BitVec.ofNat 32 (nb s₀) := by
    rw [hm _ (by decide), hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact gs .r3 (by decide)
  refine WP.mono (cmp_ok r₆ (s₀.gpr .r3).isLt (n₆.trans (by rw [← m₆]; exact hcnt))) fun s₇ ⟨r₇, z₇⟩ =>
    ⟨⟨Nat.zero_le _, a₆, r₇, M₆, fun t ht => ?_, fun q hq => ?_, ?_, ?_, ?_, hcnt⟩, z₇⟩
  · obtain ⟨k1, k2, k3⟩ := K₃ t ht
    exact ⟨by rw [m₆, m₅ _ (by omega), k1], by rw [m₆, m₅ _ (by omega), k2], by rw [m₆, m₅ _ (by omega), k3]⟩
  · have hq' : ∀ q ∈ saved, 32 ≤ q.2 ∧ q.1 ≠ .r12 := by decide
    rw [hm _ (hq' q hq).1, hs q hq]; exact gs _ (hq' q hq).2
  · rw [yOf, m₆, ghashFrom_blocksAt_zero]; exact y₅.trans (wd_block s₀ (yp s₀))
  · rw [hm _ (by decide), hy]; exact gs .r1 (by decide)
  · rw [hm _ (by decide), hd]
    refine (gs .r2 (by decide)).trans ?_
    rw [blk, Nat.mul_zero]; exact (BitVec.add_zero _).symm

theorem restore_ok (a : A) :
    WA (([ld .r0 y3S, ld .r1 y2S, ld .r2 y1S, ld .r3 y0S, .rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3] : List Instr) ++
        restore) a
      fun a' => (a'.g .r0 = rev (a.m 31) ∧ a'.g .r1 = rev (a.m 30) ∧ a'.g .r2 = rev (a.m 28) ∧ a'.g .r3 = rev (a.m 27)) ∧
        (∀ q ∈ saved, a'.g q.1 = a.m q.2) ∧ a'.m = a.m := by
  simp only [reduceCtorEq, Nat.reduceLT, and_self, ↓reduceIte, WA, restore, saved, ld, y0S, y1S, y2S, y3S, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, evalA, stepA, slotOf_slot, Option.map_some, Option.bind_some, A.g_set, A.m_set,
    Option.some.injEq, exists_eq_left', List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, and_self]

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (nb s₀) s) :
    WP isa (.block epilogue) s fun s' => abiPreserved s₀ s' ∧ ghashArm.post s₀ s' := by
  obtain ⟨-, a, r, ha⟩ := hI
  have hfs := hp.fs
  have hfy := hp.fy
  rw [epilogue, WP.block_append_iff]
  refine WP.mono (WA.sound hp.toScr r (restore_ok a)) fun s₁ ⟨a₁, r₁, ⟨e0, e1, e2, e3⟩, hs, hm⟩ => ?_
  obtain ⟨ho, hk, he, q, hq, hc⟩ := r₁.slot hp.toScr (n := .r12) (off := 4 * ypS) (k := ypS) rfl
  have hl : exec (ld .r12 ypS) s₁ = some (s₁.setReg .r12 (s₀.gpr .r1)) := by
    rw [ld, exec_ldr ho (by rw [he]; exact ⟨q, List.mem_append_right _ hq, hc⟩), he, r₁.m.get _ hk, hm, ha.yp]
  refine WP.block_cons_iff.mpr ⟨_, hl, ?_⟩
  have hst : ∀ (s : State) (o : Nat) (q : Reg), o ≤ 12 → q ≠ .r12 → s.gpr = (s₁.setReg .r12 (s₀.gpr .r1)).gpr → s.wr = s₁.wr →
      exec (.str q .r12 o) s = some { s with mem := s.mem.writeW (yp s₀ + BitVec.ofNat 64 o) (a₁.g q) } := by
    intro s o q ho hq hgs hws
    have hb : State.addr (s.gpr .r12 + BitVec.ofNat 32 o) = yp s₀ + BitVec.ofNat 64 o := by
      rw [hgs, show (s₁.setReg .r12 (s₀.gpr .r1)).gpr .r12 = s₀.gpr .r1 from rfl]; exact addr_add (by omega)
    have hv : s.gpr q = a₁.g q := by rw [hgs, ← r₁.g]; exact ite_eq_right hq
    rw [exec_str (by omega) (by
      rw [hb, hws, r₁.wr, hp.wr]; exact ⟨yR s₀, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩), hb, hv]
  refine WP.block_cons_iff.mpr ⟨_, hst _ 0 .r0 (by decide) (by decide) rfl rfl, WP.block_cons_iff.mpr ⟨_,
    hst _ 4 .r1 (by decide) (by decide) rfl rfl, WP.block_cons_iff.mpr ⟨_,
    hst _ 8 .r2 (by decide) (by decide) rfl rfl, WP.block_cons_iff.mpr ⟨_,
    hst _ 12 .r3 (by decide) (by decide) rfl rfl, WP.block_nil ⟨?_, ?_⟩⟩⟩⟩⟩
  · refine ⟨fun q hq => ?_, r₁.sp⟩
    have hsv : ∀ p ∈ saved, a₁.g p.1 = s₀.gpr p.1 := fun p hp => by rw [hs p hp, ha.sav p hp]
    have hq' : ∀ q ∈ preserved, q ≠ .r12 ∧ ∃ p ∈ saved, p.1 = q := by decide
    obtain ⟨hn, p, hp, rfl⟩ := hq' q hq
    show (if p.1 = .r12 then _ else s₁.gpr p.1) = _
    rw [ite_eq_right hn, r₁.g, hsv p hp]
  · show blockAt ((((s₁.mem.writeW (yp s₀ + BitVec.ofNat 64 0) _).writeW (yp s₀ + BitVec.ofNat 64 4) _).writeW
      (yp s₀ + BitVec.ofNat 64 8) _).writeW (yp s₀ + BitVec.ofNat 64 12) _) (yp s₀) = _
    have sep : ∀ (m : Mem) (v : BitVec 32) (d e : Nat), d + 4 ≤ e → e < 16 →
        (m.writeW (yp s₀ + BitVec.ofNat 64 e) v).readW (yp s₀ + BitVec.ofNat 64 d) 32 =
          m.readW (yp s₀ + BitVec.ofNat 64 d) 32 := fun m v d e h h1 =>
      Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)
    have h0 : yp s₀ = yp s₀ + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
    rw [blockAt_rev]
    conv_lhs => rw [w4]
    rw [show ∀ m : Mem, m.readW (yp s₀) 32 = m.readW (yp s₀ + BitVec.ofNat 64 0) 32 from fun m => by rw [← h0]]
    rw [sep _ _ 0 12 (by decide) (by decide), sep _ _ 0 8 (by decide) (by decide), sep _ _ 0 4 (by decide) (by decide),
      sep _ _ 4 12 (by decide) (by decide), sep _ _ 4 8 (by decide) (by decide), sep _ _ 8 12 (by decide) (by decide),
      Mem.readW_writeW_self32, Mem.readW_writeW_self32, Mem.readW_writeW_self32, Mem.readW_writeW_self32, e0, e1, e2, e3,
      rev_rev, rev_rev, rev_rev, rev_rev]
    exact ha.y

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' => abiPreserved s₀ s' ∧ ghashArm.post s₀ s' := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hI, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (nb s₀)) ?_ fun s₂ hI₂ => epilogue_ok hp hI₂)
  refine WP.ite (decide (nb s₀ = 0)) (by simp only [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := of_decide_eq_true h
    exact WP.block_nil (h0.symm ▸ hI)
  · have h0 : 0 < nb s₀ := Nat.pos_of_ne_zero (of_decide_eq_false h)
    let I : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ Inv s₀ i s
    have hstep : ∀ m s, I m s → WP isa (.block body) s (fun s' =>
        (eval .ne s' = some false ∧ Inv s₀ (nb s₀) s') ∨ (eval .ne s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨i, rfl, hi, hI⟩
      refine WP.mono (body_ok hp hi hI) fun s' ⟨hI', hz'⟩ => ?_
      by_cases hl : nb s₀ - (i + 1) = 0
      · have : i + 1 = nb s₀ := by omega
        exact .inl ⟨by simp only [eval, hz', hl, decide_true, Bool.not_true], this ▸ hI'⟩
      · exact .inr ⟨by simp only [eval, hz', hl, decide_false, Bool.not_false], nb s₀ - (i + 1),
          by omega, i + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (nb s₀) s₁ ⟨0, rfl, h0, hI⟩

instance instGhashLaw : GhashLaw := ⟨fun s hs => by
  obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, h.1, h.2⟩⟩

end VG.Proof.Gcm.Arm
