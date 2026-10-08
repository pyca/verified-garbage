import VerifiedGarbage.Proof.X448.Arm.Call
import VerifiedGarbage.Spec.X448.Field16

/-!
# X448 on ARMv7: the field functions' contracts

The facts of the contracts of `Spec/X448/Field16.lean` on 32-bit ARM, by
name (`armPre`, `mulArm`, …: `ws`, `o`, `a` and `b` in `r0`–`r3`), and the
functions meet them (`mul_arm`, …): the specification's limbs and values are
the proofs' (`limbAt_eq`, `valAt_eq`), and what the functions keep is what
the contracts say (`keeps_of_field`).
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Spec.X448.Field16 (limbAt valAt Limbs Fits)

/-- What the binary functions' preconditions share, by register. -/
def armPre (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨State.addr (s.gpr .r0), 8192⟩] ∧ (s.gpr .r0).toNat + 8192 ≤ 2 ^ 32 ∧
    Fits (s.gpr .r1) ∧ Fits (s.gpr .r2) ∧ Fits (s.gpr .r3) ∧
    Limbs s.mem (State.addr (s.gpr .r0)) (s.gpr .r2) ∧ Limbs s.mem (State.addr (s.gpr .r0)) (s.gpr .r3)

/-- `mul_a24`'s precondition, by register. -/
def armPre1 (s : State) : Prop :=
  s.rd = [] ∧ s.wr = [⟨State.addr (s.gpr .r0), 8192⟩] ∧ (s.gpr .r0).toNat + 8192 ≤ 2 ^ 32 ∧
    Fits (s.gpr .r1) ∧ Fits (s.gpr .r2) ∧ Limbs s.mem (State.addr (s.gpr .r0)) (s.gpr .r2)

/-- The value at the offset in `r`. -/
abbrev argV (m : Mem) (s : State) (r : Reg) : Nat := valAt m (State.addr (s.gpr .r0)) (s.gpr r)

/-- What two runs agree on: the stack pointer and the arguments. -/
def armPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

def armPub1 (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

/-- The post of a binary function with the relation `r`. -/
def binArm (r : Nat → Nat → Nat → Prop) : Contract Arm.isa where
  pre := armPre
  post s s' := Limbs s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1) ∧
    r (argV s'.mem s .r1) (argV s.mem s .r2) (argV s.mem s .r3) ∧
    Spec.X448.Field16.Keeps (State.addr (s.gpr .r0)) (s.gpr .r1) s.mem s'.mem
  pub := armPub

def mulArm : Contract Arm.isa := binArm fun o a b => o % Spec.X448.P = a * b % Spec.X448.P
def addArm : Contract Arm.isa := binArm fun o a b => o % Spec.X448.P = (a + b) % Spec.X448.P
def subArm : Contract Arm.isa := binArm fun o a b => (o + b) % Spec.X448.P = a % Spec.X448.P

def mulA24Arm : Contract Arm.isa where
  pre := armPre1
  post s s' := Limbs s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1) ∧
    argV s'.mem s .r1 % Spec.X448.P = 39081 * argV s.mem s .r2 % Spec.X448.P ∧
    Spec.X448.Field16.Keeps (State.addr (s.gpr .r0)) (s.gpr .r1) s.mem s'.mem
  pub := armPub1

theorem limbAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) (i : Nat) :
    limbAt m ws o i = limbs m ws o.toNat i := rfl

theorem valN_eq (m : Mem) (ws : Addr) (o : BitVec 32) :
    ∀ n, Spec.X448.Field16.valN m ws o n = Radix16.valN (limbs m ws o.toNat) n
  | 0 => rfl
  | n + 1 => by
    rw [Spec.X448.Field16.valN, Radix16.valN, valN_eq m ws o n, limbAt_eq, radix, ← Nat.pow_mul]

theorem valAt_eq (m : Mem) (ws : Addr) (o : BitVec 32) : valAt m ws o = fe m ws o.toNat :=
  valN_eq m ws o 28

theorem slot_of_fits {o : BitVec 32} (h : Fits o) : Slot o.toNat := h

theorem bounded_of_limbs {m : Mem} {ws : Addr} {o : BitVec 32} (h : Limbs m ws o) :
    Bounded m ws o.toNat := h

theorem limbs_of_bounded {m : Mem} {ws : Addr} {o : BitVec 32} (h : Bounded m ws o.toNat) :
    Limbs m ws o := h

theorem keeps_of_field {ws : Addr} {o : BitVec 32} {m m' : Mem} (h : FieldMem ws o.toNat m m') :
    Spec.X448.Field16.Keeps ws o m m' := by
  intro i hi hown ho
  have e : ofs ws (ws + BitVec.ofNat 64 i) = i := Mem.sub_ofNat_toNat ws (by omega)
  refine h _ (by rw [e]; simp only [Spec.X448.Field16.elemBytes, Spec.X448.Field16.limbs] at ho; omega)
    (by rw [e]; simp only [Spec.X448.Field16.ownAt] at hown; simp only [ACC]; omega)

theorem entry_of {s : State} (h : armPre s) :
    Entry true s (State.addr (s.gpr .r0)) (s.gpr .r1).toNat (s.gpr .r2).toNat (s.gpr .r3).toNat :=
  ⟨⟨rfl, by rw [h.2.1]; exact List.mem_singleton_self _, h.2.2.1⟩, rfl, rfl, fun _ => rfl⟩

theorem entry_of1 {s : State} (h : armPre1 s) :
    Entry false s (State.addr (s.gpr .r0)) (s.gpr .r1).toNat (s.gpr .r2).toNat (s.gpr .r2).toNat :=
  ⟨⟨rfl, by rw [h.2.1]; exact List.mem_singleton_self _, h.2.2.1⟩, rfl, rfl, fun h => absurd h (by decide)⟩

theorem bin_arm {r : Nat → Nat → Nat → Prop} {c : Prog isa}
    (hc : ∀ (s : State) (base : Addr) (o a b : Nat), Entry true s base o a b → Slot o → Slot a → Slot b →
      Bounded s.mem base a → Bounded s.mem base b → WP isa c s (FnPost s base o a b r))
    (s : State) (hs : (binArm r).pre s) :
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (binArm r).post s s' := by
  obtain ⟨t, s', he, P, _, _, _, M, B, V⟩ := hc s _ _ _ _ (entry_of hs) hs.2.2.2.1 hs.2.2.2.2.1
    hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2
  refine ⟨t, s', he, ⟨P, Exec.sp he⟩, limbs_of_bounded B, ?_, keeps_of_field M⟩
  rw [argV, argV, argV, valAt_eq, valAt_eq, valAt_eq]
  exact V

theorem mul_arm (s : State) (hs : mulArm.pre s) :
    ∃ t s', Exec isa mulFn s t s' ∧ abiPreserved s s' ∧ mulArm.post s s' :=
  bin_arm (fun _ _ _ _ _ he ho ha hb ab bb => mulFn_ok he ho ha hb ab bb) s hs

theorem add_arm (s : State) (hs : addArm.pre s) :
    ∃ t s', Exec isa addFn s t s' ∧ abiPreserved s s' ∧ addArm.post s s' :=
  bin_arm (fun _ _ _ _ _ he ho ha hb ab bb => addFn_ok he ho ha hb ab bb) s hs

theorem sub_arm (s : State) (hs : subArm.pre s) :
    ∃ t s', Exec isa subFn s t s' ∧ abiPreserved s s' ∧ subArm.post s s' :=
  bin_arm (fun _ _ _ _ _ he ho ha hb ab bb => subFn_ok he ho ha hb ab bb) s hs

theorem mulA24_arm (s : State) (hs : mulA24Arm.pre s) :
    ∃ t s', Exec isa mulA24Fn s t s' ∧ abiPreserved s s' ∧ mulA24Arm.post s s' := by
  obtain ⟨t, s', he, P, _, _, _, M, B, V⟩ := mulA24Fn_ok (entry_of1 hs) hs.2.2.2.1 hs.2.2.2.2.1
    hs.2.2.2.2.2
  refine ⟨t, s', he, ⟨P, Exec.sp he⟩, limbs_of_bounded B, ?_, keeps_of_field M⟩
  rw [argV, argV, valAt_eq, valAt_eq]
  exact V

end VG.Proof.X448.Arm
