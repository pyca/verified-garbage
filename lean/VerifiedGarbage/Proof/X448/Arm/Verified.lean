import VerifiedGarbage.Impl.X448.Arm
import VerifiedGarbage.Proof.X448.Encoding
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X25519.Arm.Verified
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.X448.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Mem`. -/
section

/-!
# X448 on ARMv7: the working space
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 32 := m.readW (VG.Proof.X448.Arm.off base d) 32
abbrev limbs (m : Mem) (base : Addr) (o : Nat) (i : Nat) : Nat := (VG.Proof.X448.Arm.word m base (o + 4 * i)).toNat
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat := VG.Proof.X448.Radix16.valN (VG.Proof.X448.Arm.limbs m base o) 28

def Bounded (m : Mem) (base : Addr) (o : Nat) : Prop := ∀ i < 28, VG.Proof.X448.Arm.limbs m base o i < VG.Proof.X448.Radix16.radix

/-- The registers and permissions that an arithmetic operation preserves. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.refl (rs : List Reg) (s : State) : VG.Proof.X448.Arm.Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X448.Arm.Keeps rs s₁ s₂) (h₂ : VG.Proof.X448.Arm.Keeps rs s₂ s₃) :
    VG.Proof.X448.Arm.Keeps rs s₁ s₃ := ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1,
      h₂.2.2.trans h₁.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.X448.Arm.Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.X448.Arm.Keeps rs' s s' := ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keeps.then {rs rs' : List Reg} {s t u : State} (h : VG.Proof.X448.Arm.Keeps rs s t) (h' : VG.Proof.X448.Arm.Keeps rs' t u) :
    VG.Proof.X448.Arm.Keeps (rs ++ rs') s u :=
  (h.mono (fun _ hr => List.mem_append_left _ hr)).trans
    (h'.mono (fun _ hr => List.mem_append_right _ hr))

structure Scr (s : State) (base : Addr) : Prop where
  r0 : State.addr (s.gpr .r0) = base
  mask : s.gpr .r6 = 65535
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : (s.gpr .r0).toNat + 8192 ≤ 2 ^ 32

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base)
    (h : VG.Proof.X448.Arm.Keeps rs s s') (hr : .r0 ∉ rs ∧ .r6 ∉ rs) : VG.Proof.X448.Arm.Scr s' base :=
  ⟨by rw [h.1 _ hr.1]; exact hs.r0, (h.1 _ hr.2).trans hs.mask,
    h.2.2 ▸ hs.wr, by rw [h.1 _ hr.1]; exact hs.nowrap⟩

theorem Scr.ea {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {d : Nat} (hd : d < 8192) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = VG.Proof.X448.Arm.off base d := by
  rw [VG.Arm.addr_add (by have := hs.nowrap; omega), hs.r0]

theorem contains_sc {base : Addr} {d n : Nat} (h : d + n ≤ 8192) :
    (⟨base, 8192⟩ : Region).Contains (VG.Proof.X448.Arm.off base d) n :=
  Offset.contains_base base h (by omega)

theorem Scr.read {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (VG.Proof.X448.Arm.off base d) n :=
  ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X448.Arm.contains_sc hd⟩

theorem Scr.write {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions s.wr (VG.Proof.X448.Arm.off base d) n := ⟨_, hs.wr, VG.Proof.X448.Arm.contains_sc hd⟩

abbrev ofs (base x : Addr) : Nat := (x - base).toNat

def Outside (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (VG.Proof.X448.Arm.ofs base x < o ∨ o + n ≤ VG.Proof.X448.Arm.ofs base x) → m' x = m x

theorem Outside.refl (base : Addr) (o n : Nat) (m : Mem) : VG.Proof.X448.Arm.Outside base o n m m := fun _ _ => rfl

theorem Outside.trans {base : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.X448.Arm.Outside base o n m₁ m₂)
    (h₂ : VG.Proof.X448.Arm.Outside base o n m₂ m₃) : VG.Proof.X448.Arm.Outside base o n m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Outside.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base o n m m')
    (hl : o' ≤ o) (hr : o + n ≤ o' + n') : VG.Proof.X448.Arm.Outside base o' n' m m' :=
  fun x hx => h x (by omega)

theorem ofs_off (base : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    VG.Proof.X448.Arm.ofs base (VG.Proof.X448.Arm.off base d + BitVec.ofNat 64 i) = d + i := by
  simp only [VG.Proof.X448.Arm.ofs, VG.Proof.X448.Arm.off]
  rw [Offset.add_add, Mem.sub_ofNat_toNat base h]

theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base o n m m') {d : Nat}
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 8192) : VG.Proof.X448.Arm.word m' base d = VG.Proof.X448.Arm.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.Arm.ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.limbs {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base o n m m') {d : Nat}
    (hd : d + 112 ≤ o ∨ o + n ≤ d) (hd' : d + 112 ≤ 8192) {i : Nat} (hi : i < 28) :
    VG.Proof.X448.Arm.limbs m' base d i = VG.Proof.X448.Arm.limbs m base d i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega))

theorem Outside.fe {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base o n m m') {d : Nat}
    (hd : d + 112 ≤ o ∨ o + n ≤ d) (hd' : d + 112 ≤ 8192) : VG.Proof.X448.Arm.fe m' base d = VG.Proof.X448.Arm.fe m base d :=
  VG.Proof.X448.Radix16.valN_congr fun _ hi => h.limbs hd hd' hi

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 32) (h : d + 4 ≤ 8192) :
    VG.Proof.X448.Arm.Outside base d 4 m (m.writeW (VG.Proof.X448.Arm.off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [VG.Proof.X448.Arm.ofs] at hx
  omega

theorem word_write (m : Mem) (base : Addr) {o i j : Nat} (ho : o + 4 * (i + 1) ≤ 8192)
    (hj : o + 4 * (j + 1) ≤ 8192) (v : BitVec 32) :
    VG.Proof.X448.Arm.word (m.writeW (VG.Proof.X448.Arm.off base (o + 4 * i)) v) base (o + 4 * j) =
      if j = i then v else VG.Proof.X448.Arm.word m base (o + 4 * j) := by
  by_cases h : j = i
  · rw [ite_eq_left h, h, VG.Proof.X448.Arm.word, Mem.readW_writeW_self32]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- A field operation writes its result and its temporary coefficients. -/
def FieldMem (base : Addr) (o : Nat) (m m' : Mem) : Prop :=
  ∀ x, (VG.Proof.X448.Arm.ofs base x < o ∨ o + 112 ≤ VG.Proof.X448.Arm.ofs base x) →
    (VG.Proof.X448.Arm.ofs base x < VG.Impl.X448.Arm.ACC ∨ VG.Impl.X448.Arm.ACC + 512 ≤ VG.Proof.X448.Arm.ofs base x) → m' x = m x

theorem FieldMem.refl (base : Addr) (o : Nat) (m : Mem) : VG.Proof.X448.Arm.FieldMem base o m m := fun _ _ _ => rfl

theorem FieldMem.trans {base : Addr} {o : Nat} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.X448.Arm.FieldMem base o m₁ m₂)
    (h₂ : VG.Proof.X448.Arm.FieldMem base o m₂ m₃) : VG.Proof.X448.Arm.FieldMem base o m₁ m₃ :=
  fun x hx hw => (h₂ x hx hw).trans (h₁ x hx hw)

theorem FieldMem.output {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base o 112 m m') :
    VG.Proof.X448.Arm.FieldMem base o m m' := fun x hx _ => h x hx

theorem FieldMem.work {base : Addr} {o d n : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base d n m m')
    (hl : VG.Impl.X448.Arm.ACC ≤ d) (hr : d + n ≤ VG.Impl.X448.Arm.ACC + 512) : VG.Proof.X448.Arm.FieldMem base o m m' :=
  fun x _ hx => h.mono hl hr x hx

theorem FieldMem.word {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.FieldMem base o m m') {d : Nat}
    (hd : d + 4 ≤ o ∨ o + 112 ≤ d) (hw : d + 4 ≤ VG.Impl.X448.Arm.ACC) : VG.Proof.X448.Arm.word m' base d = VG.Proof.X448.Arm.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.Arm.ofs_off base (by simp only [VG.Impl.X448.Arm.ACC] at hw; omega)]; omega)
    (Or.inl (by rw [VG.Proof.X448.Arm.ofs_off base (by simp only [VG.Impl.X448.Arm.ACC] at hw; omega)]; omega))).symm).symm

theorem FieldMem.limbs {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.FieldMem base o m m') {d : Nat}
    (hd : d + 112 ≤ o ∨ o + 112 ≤ d) (hw : d + 112 ≤ VG.Impl.X448.Arm.ACC) {i : Nat} (hi : i < 28) :
    VG.Proof.X448.Arm.limbs m' base d i = VG.Proof.X448.Arm.limbs m base d i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega))

theorem FieldMem.fe {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.FieldMem base o m m') {d : Nat}
    (hd : d + 112 ≤ o ∨ o + 112 ≤ d) (hw : d + 112 ≤ VG.Impl.X448.Arm.ACC) : VG.Proof.X448.Arm.fe m' base d = VG.Proof.X448.Arm.fe m base d :=
  VG.Proof.X448.Radix16.valN_congr fun _ hi => h.limbs hd hw hi

/-- Memory outside two ranges, used by the conditional swap. -/
def Outside2 (base : Addr) (x nx y ny : Nat) (m m' : Mem) : Prop :=
  ∀ p, (VG.Proof.X448.Arm.ofs base p < x ∨ x + nx ≤ VG.Proof.X448.Arm.ofs base p) →
    (VG.Proof.X448.Arm.ofs base p < y ∨ y + ny ≤ VG.Proof.X448.Arm.ofs base p) → m' p = m p

theorem Outside2.refl (base : Addr) (x nx y ny : Nat) (m : Mem) : VG.Proof.X448.Arm.Outside2 base x nx y ny m m :=
  fun _ _ _ => rfl

theorem Outside2.trans {base : Addr} {x nx y ny : Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : VG.Proof.X448.Arm.Outside2 base x nx y ny m₁ m₂) (h₂ : VG.Proof.X448.Arm.Outside2 base x nx y ny m₂ m₃) :
    VG.Proof.X448.Arm.Outside2 base x nx y ny m₁ m₃ := fun p hx hy => (h₂ p hx hy).trans (h₁ p hx hy)

theorem Outside2.mono {base : Addr} {x nx y ny nx' ny' : Nat} {m m' : Mem}
    (h : VG.Proof.X448.Arm.Outside2 base x nx y ny m m') (hx : nx ≤ nx') (hy : ny ≤ ny') :
    VG.Proof.X448.Arm.Outside2 base x nx' y ny' m m' := fun p hp hq => h p (by omega) (by omega)

theorem Outside2.word {base : Addr} {x nx y ny : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside2 base x nx y ny m m')
    {d : Nat} (hx : d + 4 ≤ x ∨ x + nx ≤ d) (hy : d + 4 ≤ y ∨ y + ny ≤ d) (hd : d + 4 ≤ 8192) :
    VG.Proof.X448.Arm.word m' base d = VG.Proof.X448.Arm.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.Arm.ofs_off base (by omega)]; omega)
    (by rw [VG.Proof.X448.Arm.ofs_off base (by omega)]; omega)).symm).symm

/-- Aligned word stores read back as an update at one byte offset. -/
theorem word_write_aligned (m : Mem) (base : Addr) {d e : Nat} (hd : d + 4 ≤ 8192)
    (he : e + 4 ≤ 8192) (hdm : d % 4 = 0) (hem : e % 4 = 0) (v : BitVec 32) :
    VG.Proof.X448.Arm.word (m.writeW (VG.Proof.X448.Arm.off base d) v) base e = if e = d then v else VG.Proof.X448.Arm.word m base e := by
  by_cases h : e = d
  · rw [ite_eq_left h, h, VG.Proof.X448.Arm.word, Mem.readW_writeW_self32]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Step`. -/
section

/-!
# X448 on ARMv7: arithmetic steps
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_ldr)

/-- Load a coefficient and propagate its carry. -/
def carryBlock (o a i : Nat) : List Instr :=
  [ld .r3 (a + 4 * i)] ++ VG.Impl.X448.Arm.carryStep .r0 (o + 4 * i)

theorem carryStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {o a i : Nat}
    (ho : o + 4 * i + 4 ≤ 4096) (ha : a + 4 * i + 4 ≤ 4096)
    (hb : (VG.Proof.X448.Arm.word s.mem base (a + 4 * i)).toNat + (s.gpr .r5).toNat < 2 ^ 32) :
    let v := (VG.Proof.X448.Arm.word s.mem base (a + 4 * i)).toNat + (s.gpr .r5).toNat
    WP isa (.block (VG.Proof.X448.Arm.carryBlock o a i)) s fun s' =>
      (s'.gpr .r5).toNat = v / VG.Proof.X448.Radix16.radix ∧
      s'.mem = s.mem.writeW (VG.Proof.X448.Arm.off base (o + 4 * i)) (BitVec.ofNat 32 (v % VG.Proof.X448.Radix16.radix)) ∧
      VG.Proof.X448.Arm.Keeps [.r3, .r5, .r4] s s' := by
  intro v
  unfold VG.Proof.X448.Arm.carryBlock ld
  refine wp_ldr (a := VG.Proof.X448.Arm.off base (a + 4 * i)) (by omega) (hs.ea (by omega))
    (hs.read (by omega)) fun t ht => ?_
  have h5 : t.gpr .r5 = s.gpr .r5 := ht.other _ (by decide)
  have h3 : (t.gpr .r3).toNat = (VG.Proof.X448.Arm.word s.mem base (a + 4 * i)).toNat := by rw [ht.gpr]
  refine WP.mono (VG.Proof.X25519.Arm.carryStep_ok
    (a := VG.Proof.X448.Arm.off base (o + 4 * i)) (by decide) (by omega)
    (by rw [ht.other .r0 (by decide)]; exact hs.ea (by omega))
    (by rw [ht.wr]; exact hs.write (by omega))
    (by rw [ht.other .r6 (by decide)]; exact hs.mask)
    (by rw [h3, h5]; exact hb)) fun u ⟨hc, ⟨w, hw, hm⟩, hk⟩ => ?_
  rw [h3, h5] at hc hw
  refine ⟨hc, ?_, (fun r hr => ?_), hk.rd.trans ht.rd, hk.wr.trans ht.wr⟩
  · have he : w = BitVec.ofNat 32 (v % VG.Proof.X448.Radix16.radix) := by
      apply BitVec.eq_of_toNat_eq
      rw [hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v % VG.Proof.X448.Radix16.radix)
        (Nat.lt_trans (Nat.mod_lt v (by decide : 0 < VG.Proof.X448.Radix16.radix)) (by decide : VG.Proof.X448.Radix16.radix < 2 ^ 32))]
      rfl
    rw [hm, ht.mem, he]
  · have hr' : r ∉ [Reg.r3, .r4, .r5] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      exact ⟨hr.1, hr.2.2, hr.2.1⟩
    rw [hk.gpr r hr']
    apply ht.other
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact hr.1

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Carry`. -/
section

/-!
# X448 on ARMv7: carry propagation
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_mov op2_imm wp_ldr wp_dp op2_reg wp_str)

theorem rest_keeps {ws : List Reg} {s t : State} (h : VG.Proof.X25519.Arm.Rest ws s t) : VG.Proof.X448.Arm.Keeps ws s t :=
  ⟨h.gpr, h.rd, h.wr⟩

theorem zeroCarry_ok (s : State) :
    WP isa (.block [.mov .r5 (.imm 0)]) s fun t =>
      t.gpr .r5 = 0 ∧ t.mem = s.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r5, .r4] s t := by
  refine wp_mov (op2_imm (by decide)) fun t ht => WP.block_nil
    ⟨ht.gpr, ht.mem, VG.Proof.X448.Arm.rest_keeps (ht.rest (by decide))⟩

/-- An in-place pass only overwrites input limbs it has already consumed. -/
theorem pass_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {o a : Nat}
    (ho : o + 112 ≤ 4096) (ha : a + 112 ≤ 4096)
    (hsep : o = a ∨ o + 112 ≤ a ∨ a + 112 ≤ o)
    {f : Nat → Nat} (hf : ∀ i < 28, VG.Proof.X448.Arm.limbs s.mem base a i = f i)
    (hb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix) :
    WP isa (.block (pass o a)) s fun s' =>
      (∀ i < 28, VG.Proof.X448.Arm.limbs s'.mem base o i = VG.Proof.X448.Radix16.digit f i) ∧
      (s'.gpr .r5).toNat = VG.Proof.X448.Radix16.carry f 28 ∧ VG.Proof.X448.Arm.Outside base o 112 s.mem s'.mem ∧
      VG.Proof.X448.Arm.Keeps [.r3, .r5, .r4] s s' := by
  let inv := fun k (t : State) =>
    (∀ i < k, VG.Proof.X448.Arm.limbs t.mem base o i = VG.Proof.X448.Radix16.digit f i) ∧
    (∀ i, k ≤ i → i < 28 → VG.Proof.X448.Arm.limbs t.mem base a i = f i) ∧
    (t.gpr .r5).toNat = VG.Proof.X448.Radix16.carry f k ∧ VG.Proof.X448.Arm.Outside base o 112 s.mem t.mem ∧
    VG.Proof.X448.Arm.Keeps [.r3, .r5, .r4] s t
  have step : ∀ k t, k < 28 → inv k t → WP isa (.block (VG.Proof.X448.Arm.carryBlock o a k)) t (inv (k + 1)) := by
    intro k t hk ⟨hlo, hhi, hc, hm, ht⟩
    have hts := hs.of_keeps ht (by decide)
    have he := hhi k (by omega) hk
    have hsum : (VG.Proof.X448.Arm.word t.mem base (a + 4 * k)).toNat + (t.gpr .r5).toNat < 2 ^ 32 := by
      change VG.Proof.X448.Arm.limbs t.mem base a k + (t.gpr .r5).toNat < _
      rw [he, hc]
      have hcoeff := hb k hk
      have hcarry := VG.Proof.X448.Radix16.carry_bound (n := k) (fun i hi => hb i (by omega))
      simp only [VG.Proof.X448.Radix16.radix] at hcoeff
      omega
    refine WP.mono (VG.Proof.X448.Arm.carryStep_ok hts (by omega) (by omega) hsum) fun u ⟨hu, hmem, huKeep⟩ => ?_
    have he' : (VG.Proof.X448.Arm.word t.mem base (a + 4 * k)).toNat + (t.gpr .r5).toNat = f k + VG.Proof.X448.Radix16.carry f k := by
      change VG.Proof.X448.Arm.limbs t.mem base a k + (t.gpr .r5).toNat = _
      rw [he, hc]
    rw [he'] at hu hmem
    have out : VG.Proof.X448.Arm.Outside base (o + 4 * k) 4 t.mem u.mem := by
      rw [hmem]
      exact VG.Proof.X448.Arm.writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, hu, hm.trans (out.mono (by omega) (by omega)), ht.trans huKeep⟩
    · intro i hi
      change (VG.Proof.X448.Arm.word u.mem base (o + 4 * i)).toNat = _
      rw [hmem, VG.Proof.X448.Arm.word_write t.mem base (by omega) (by omega)]
      by_cases hik : i = k
      · rw [ite_eq_left hik, hik, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (f k + VG.Proof.X448.Radix16.carry f k) % VG.Proof.X448.Radix16.radix)
          (Nat.lt_trans (VG.Proof.X448.Radix16.digit_lt f k) (by decide))]
        rfl
      · rw [ite_eq_right hik]
        exact hlo i (by omega)
    · intro i hi hi'
      have sep : a + 4 * i + 4 ≤ o + 4 * k ∨ o + 4 * k + 4 ≤ a + 4 * i := by
        rcases hsep with h | h | h <;> omega
      change (VG.Proof.X448.Arm.word u.mem base (a + 4 * i)).toNat = _
      rw [out.word sep (by omega)]
      exact hhi i (by omega) hi'
  change WP isa (.block ([.mov .r5 (.imm 0)] ++ (List.range 28).flatMap (VG.Proof.X448.Arm.carryBlock o a))) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.zeroCarry_ok s) fun t ⟨hc, hm, ht⟩ => ?_
  refine WP.mono (wp_range_flatMap inv step 28 (by decide) t ?_) fun u ⟨hlo, _, hc, hm, ht⟩ =>
    ⟨hlo, hc, hm, ht⟩
  refine ⟨fun i hi => by omega, (fun i _ hi => ?_), ?_, ?_, ht⟩
  · rw [hm]; exact hf i hi
  · rw [hc]; rfl
  · rw [hm]; exact Outside.refl _ _ _ _

theorem foldStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {d : Nat}
    (hd : d + 4 ≤ 4096) :
    WP isa (.block [ld .r3 d, .dp .add .r3 .r3 (.reg .r5), st .r3 d]) s
      fun t => t.mem = s.mem.writeW (VG.Proof.X448.Arm.off base d) (VG.Proof.X448.Arm.word s.mem base d + s.gpr .r5) ∧
        VG.Proof.X448.Arm.Keeps [.r3] s t := by
  refine wp_ldr (a := VG.Proof.X448.Arm.off base d) (by omega) (hs.ea (by omega)) (hs.read (by omega)) fun t ht => ?_
  refine wp_dp (op2_reg _ _) fun u hu => ?_
  refine wp_str (a := VG.Proof.X448.Arm.off base d) (by omega)
    (by rw [hu.other .r0 (by decide), ht.other .r0 (by decide)]; exact hs.ea (by omega))
    (by rw [hu.wr, ht.wr]; exact hs.write (by omega)) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr]
    change s.mem.writeW _ (t.gpr .r3 + t.gpr .r5) = _
    rw [ht.gpr, ht.other .r5 (by decide)]
  · exact VG.Proof.X448.Arm.rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _)))

theorem foldLimb_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {k : Nat} (hk : k < 28)
    (hb : VG.Proof.X448.Arm.limbs s.mem base TMP k + (s.gpr .r5).toNat < 2 ^ 32) :
    WP isa (.block [ld .r3 (TMP + 4 * k), .dp .add .r3 .r3 (.reg .r5),
      st .r3 (TMP + 4 * k)]) s fun t =>
      (∀ i < 28, VG.Proof.X448.Arm.limbs t.mem base TMP i =
        if i = k then VG.Proof.X448.Arm.limbs s.mem base TMP i + (s.gpr .r5).toNat else VG.Proof.X448.Arm.limbs s.mem base TMP i) ∧
      VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3] s t := by
  have hd : TMP + 4 * k + 4 ≤ 4096 := by simp only [TMP]; omega
  refine WP.mono (VG.Proof.X448.Arm.foldStep_ok hs hd) fun t ⟨hm, ht⟩ => ?_
  refine ⟨?_, ?_, ht⟩
  · intro i hi
    change (VG.Proof.X448.Arm.word t.mem base (TMP + 4 * i)).toNat = _
    rw [hm, VG.Proof.X448.Arm.word_write s.mem base (by omega) (by simp only [TMP]; omega)]
    by_cases h : i = k
    · rw [ite_eq_left h, ite_eq_left h, h, BitVec.toNat_add, Nat.mod_eq_of_lt hb]
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [hm]
    exact (VG.Proof.X448.Arm.writeW_outside _ _ _ (by omega : TMP + 4 * k + 4 ≤ 8192)).mono (by omega) (by omega)

/-- The two stores implement the mathematical carry fold. -/
theorem fold_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 28, VG.Proof.X448.Arm.limbs s.mem base TMP i = VG.Proof.X448.Radix16.digit f i)
    (hc : (s.gpr .r5).toNat = VG.Proof.X448.Radix16.carry f 28) (hb : VG.Proof.X448.Radix16.carry f 28 < 2 ^ 16) :
    WP isa (.block fold) s fun s' =>
      (∀ i < 28, VG.Proof.X448.Arm.limbs s'.mem base TMP i = VG.Proof.X448.Radix16.folded f i) ∧
      VG.Proof.X448.Arm.Outside base TMP 112 s.mem s'.mem ∧ VG.Proof.X448.Arm.Keeps [.r3] s s' := by
  have bound : ∀ i < 28, VG.Proof.X448.Radix16.digit f i + VG.Proof.X448.Radix16.carry f 28 < 2 ^ 32 := by
    intro i _
    have h := VG.Proof.X448.Radix16.digit_lt f i
    simp only [VG.Proof.X448.Radix16.radix] at h
    omega
  change WP isa (.block
    (([ld .r3 (TMP + 4 * 0), .dp .add .r3 .r3 (.reg .r5),
       st .r3 (TMP + 4 * 0)] : List Instr) ++
     [ld .r3 (TMP + 4 * 14), .dp .add .r3 .r3 (.reg .r5),
       st .r3 (TMP + 4 * 14)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.foldLimb_ok hs (k := 0) (by decide) (by rw [hf 0 (by decide), hc]; exact bound 0 (by decide)))
    fun t ⟨htf, htm, ht⟩ => ?_
  have htc : (t.gpr .r5).toNat = VG.Proof.X448.Radix16.carry f 28 := by rw [ht.1 _ (by decide), hc]
  refine WP.mono (VG.Proof.X448.Arm.foldLimb_ok (hs.of_keeps ht (by decide)) (k := 14) (by decide) ?_)
    fun u ⟨huf, hum, hu⟩ => ?_
  · rw [htf 14 (by decide), ite_eq_right (by decide), hf 14 (by decide), htc]
    exact bound 14 (by decide)
  · refine ⟨?_, htm.trans hum, ht.trans hu⟩
    intro i hi
    rw [huf i hi, htf i hi, hf i hi, hc, htc]
    simp only [VG.Proof.X448.Radix16.folded]
    by_cases h0 : i = 0
    · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
    · by_cases h8 : i = 14
      · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
      · simp only [h0, h8, ite_false, false_or, Nat.add_zero]

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Normalize`. -/
section

/-!
# X448 on ARMv7: modular reduction
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

/-- Normalize the coefficients at `TMP` into a field-element slot. -/
theorem normalize_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {o : Nat}
    (ho : o + 112 ≤ ACC) {f : Nat → Nat}
    (hf : ∀ i < 28, VG.Proof.X448.Arm.limbs s.mem base TMP i = f i) (hb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix) :
    WP isa (.block (normalize o)) s fun t =>
      (∀ i < 28, VG.Proof.X448.Arm.limbs t.mem base o i = VG.Proof.X448.Radix16.normalized f i) ∧
      VG.Proof.X448.Arm.FieldMem base o s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r5, .r4] s t := by
  have htmp : TMP + 112 ≤ 4096 := by decide
  have hwork : ∀ {m m' : Mem}, VG.Proof.X448.Arm.Outside base TMP 112 m m' → VG.Proof.X448.Arm.FieldMem base o m m' :=
    fun h => FieldMem.work h (by decide) (by decide)
  have keep : ∀ {a b : State}, VG.Proof.X448.Arm.Keeps [.r3] a b → VG.Proof.X448.Arm.Keeps [.r3, .r5, .r4] a b :=
    fun h => h.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; decide)
  rw [normalize, show pass TMP TMP ++ fold ++ pass TMP TMP ++ fold ++ pass o TMP =
    pass TMP TMP ++ (fold ++ (pass TMP TMP ++ (fold ++ pass o TMP))) by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.pass_ok hs htmp htmp (Or.inl rfl) hf hb) fun s₁ ⟨f₁, c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.fold_ok hs₁ f₁ c₁ (VG.Proof.X448.Radix16.carry_bound hb)) fun s₂ ⟨f₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.pass_ok hs₂ htmp htmp (Or.inl rfl) f₂ (VG.Proof.X448.Radix16.folded_bound hb)) fun s₃ ⟨f₃, c₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.fold_ok hs₃ f₃ c₃ (VG.Proof.X448.Radix16.carry_bound (VG.Proof.X448.Radix16.folded_bound hb))) fun s₄ ⟨f₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have ho' : o + 112 ≤ TMP := Nat.le_trans ho (by decide)
  refine WP.mono (VG.Proof.X448.Arm.pass_ok hs₄ (Nat.le_trans ho (by decide)) htmp (Or.inr (Or.inl ho')) f₄
    (VG.Proof.X448.Radix16.folded_bound (VG.Proof.X448.Radix16.folded_bound hb))) fun s₅ ⟨f₅, _, m₅, k₅⟩ => ?_
  exact ⟨f₅, (hwork m₁).trans ((hwork m₂).trans ((hwork m₃).trans ((hwork m₄).trans (.output m₅)))),
    k₁.trans ((keep k₂).trans (k₃.trans ((keep k₄).trans k₅)))⟩

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Field`. -/
section

/-!
# X448 on ARMv7: field operations and their frame
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := toFe (VG.Proof.X448.Arm.fe m base o)

def clob : List Reg := [.r1, .r2, .r3, .r4, .r5, .r7, .r9]

structure Op (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.clob s t
  mem : VG.Proof.X448.Arm.FieldMem base o s.mem t.mem

theorem Op.scr {base : Addr} {o : Nat} {s t : State} (h : VG.Proof.X448.Arm.Op base o s t) (hs : VG.Proof.X448.Arm.Scr s base) :
    VG.Proof.X448.Arm.Scr t base := hs.of_keeps h.keeps (by decide)

abbrev Slot (o : Nat) : Prop := o + 112 ≤ ACC

/-- A register update preserving the working-space pointer and limb mask. -/
theorem Scr.of_upd {s t : State} {base : Addr} {r : Reg} {v : BitVec 32}
    (hs : VG.Proof.X448.Arm.Scr s base) (h : VG.Proof.X25519.Arm.Upd s t r v) (h0 : Reg.r0 ≠ r) (h6 : Reg.r6 ≠ r) :
    VG.Proof.X448.Arm.Scr t base :=
  ⟨by rw [h.other _ h0]; exact hs.r0, (h.other _ h6).trans hs.mask, h.wr ▸ hs.wr,
    by rw [h.other _ h0]; exact hs.nowrap⟩

theorem load_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {r : Reg} {d : Nat}
    (hd : d + 4 ≤ 4096) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.X25519.Arm.Upd s t r (VG.Proof.X448.Arm.word s.mem base d) → WP isa (.block is) t Q) :
    WP isa (.block (ld r d :: is)) s Q :=
  VG.Proof.X25519.Arm.wp_ldr (by omega) (hs.ea (by omega)) (hs.read (by omega)) k

theorem store_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {r : Reg} {d : Nat}
    (hd : d + 4 ≤ 4096) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.X25519.Arm.Mupd s t (s.mem.writeW (VG.Proof.X448.Arm.off base d) (s.gpr r)) →
      WP isa (.block is) t Q) : WP isa (.block (st r d :: is)) s Q :=
  VG.Proof.X25519.Arm.wp_str (by omega) (hs.ea (by omega)) (hs.write (by omega)) k

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Columns`. -/
section

/-!
# X448 on ARMv7: pointwise field operations

A pointwise operation fills `TMP` before the carry passes write the output,
permitting input/output aliasing.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

theorem columns_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {code : Nat → List Instr}
    {f : Nat → Nat} {rs : List Reg} (hr : .r0 ∉ rs ∧ .r6 ∉ rs) (hb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix)
    (step : ∀ i < 28, ∀ t, VG.Proof.X448.Arm.Scr t base → VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem → VG.Proof.X448.Arm.Keeps rs s t →
      WP isa (.block (code i)) t fun u =>
        u.mem = t.mem.writeW (VG.Proof.X448.Arm.off base (TMP + 4 * i)) (BitVec.ofNat 32 (f i)) ∧ VG.Proof.X448.Arm.Keeps rs t u) :
    WP isa (.block ((List.range 28).flatMap code)) s fun t =>
      (∀ i < 28, VG.Proof.X448.Arm.limbs t.mem base TMP i = f i) ∧ VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps rs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.Arm.limbs t.mem base TMP i = f i) ∧ VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps rs s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (code n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (step n hn t (hs.of_keeps tk hr) tm tk) fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.Arm.Outside base (TMP + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.Arm.writeW_outside _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (VG.Proof.X448.Arm.word u.mem base (TMP + 4 * i)).toNat = _
    rw [um, VG.Proof.X448.Arm.word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- Reading an input during a pointwise operation. -/
theorem input_limb {s t : State} {base : Addr} {a i : Nat} (h : VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem)
    (ha : VG.Proof.X448.Arm.Slot a) (hi : i < 28) : VG.Proof.X448.Arm.limbs t.mem base a i = VG.Proof.X448.Arm.limbs s.mem base a i :=
  h.limbs (Or.inl (Nat.le_trans ha (by decide))) (Nat.le_trans ha (by decide)) hi

/-- Carry propagation after a pointwise operation, with the common frame. -/
theorem columns_normalize {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {code : List Instr}
    {o : Nat} (ho : VG.Proof.X448.Arm.Slot o) {f : Nat → Nat} (hb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix)
    (hcode : WP isa (.block code) s fun t =>
      (∀ i < 28, VG.Proof.X448.Arm.limbs t.mem base TMP i = f i) ∧ VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.clob s t) :
    WP isa (.block (code ++ normalize o)) s fun t =>
      VG.Proof.X448.Arm.Op base o s t ∧ VG.Proof.X448.Arm.Bounded t.mem base o ∧ VG.Proof.X448.Arm.fe t.mem base o % Spec.X448.P = VG.Proof.X448.Radix16.valN f 28 % Spec.X448.P := by
  rw [WP.block_append_iff]
  refine WP.mono hcode fun t ⟨tf, tm, tk⟩ => ?_
  refine WP.mono (VG.Proof.X448.Arm.normalize_ok (hs.of_keeps tk (by decide)) ho tf hb) fun u ⟨uf, um, uk⟩ => ?_
  refine ⟨⟨tk.trans (uk.mono ?_), (FieldMem.work tm (by decide) (by decide)).trans um⟩, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro i hi; rw [uf i hi]; exact VG.Proof.X448.Radix16.digit_lt _ _
  · rw [show VG.Proof.X448.Arm.fe u.mem base o = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.normalized f) 28 from VG.Proof.X448.Radix16.valN_congr uf, VG.Proof.X448.Radix16.normalized_mod hb]

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.AddSub`. -/
section

/-!
# X448 on ARMv7: addition and subtraction

Twice the prime is added before subtraction, so no limb subtraction borrows.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_dp wp_movw op2_reg op2_imm)

theorem addStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {a b i : Nat}
    (ha : VG.Proof.X448.Arm.Slot a) (hb : VG.Proof.X448.Arm.Slot b) (hi : i < 28) :
    WP isa (.block [ld .r3 (a + 4 * i), ld .r2 (b + 4 * i),
      .dp .add .r3 .r3 (.reg .r2), st .r3 (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.Arm.off base (TMP + 4 * i))
        (BitVec.ofNat 32 (VG.Proof.X448.Arm.limbs s.mem base a i + VG.Proof.X448.Arm.limbs s.mem base b i)) ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.clob s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine VG.Proof.X448.Arm.load_ok hs (by omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide) (by decide)
  refine VG.Proof.X448.Arm.load_ok ts (by omega) fun u hu => ?_
  have us := ts.of_upd hu (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun v hv => ?_
  have vs := us.of_upd hv (by decide) (by decide)
  refine VG.Proof.X448.Arm.store_ok vs (by simp only [TMP]; omega) fun w hw => WP.block_nil ⟨?_, ?_⟩
  · rw [hw.mem, hv.mem, hu.mem, ht.mem, hv.gpr]
    change s.mem.writeW _ (u.gpr .r3 + u.gpr .r2) = _
    rw [hu.other .r3 (by decide), ht.gpr, hu.gpr, ht.mem]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  · exact VG.Proof.X448.Arm.rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans
      ((hv.rest (by decide)).trans (hw.rest _))))

theorem subK_nat (i : Nat) : ((VG.Impl.X448.Arm.subK i).setWidth 32 + (65536 : BitVec 32)).toNat = VG.Proof.X448.Radix16.bias i := by
  by_cases h : i = 14 <;> simp only [VG.Impl.X448.Arm.subK, VG.Proof.X448.Radix16.bias, h, ite_true, ite_false] <;> decide

theorem subStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {a b i : Nat}
    (ha : VG.Proof.X448.Arm.Slot a) (hb : VG.Proof.X448.Arm.Slot b) (hi : i < 28)
    (ab : VG.Proof.X448.Arm.limbs s.mem base a i < VG.Proof.X448.Radix16.radix) (bb : VG.Proof.X448.Arm.limbs s.mem base b i < VG.Proof.X448.Radix16.radix) :
    WP isa (.block [ld .r3 (a + 4 * i), .movw .r2 (VG.Impl.X448.Arm.subK i), .dp .add .r2 .r2 (.imm 65536),
      .dp .add .r3 .r3 (.reg .r2), ld .r2 (b + 4 * i), .dp .sub .r3 .r3 (.reg .r2),
      st .r3 (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.Arm.off base (TMP + 4 * i))
        (BitVec.ofNat 32 (VG.Proof.X448.Radix16.difference (VG.Proof.X448.Arm.limbs s.mem base a) (VG.Proof.X448.Arm.limbs s.mem base b) i)) ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.clob s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine VG.Proof.X448.Arm.load_ok hs (by omega) fun s1 h1 => ?_
  have hs1 := hs.of_upd h1 (by decide) (by decide)
  refine wp_movw fun s2 h2 => ?_
  have hs2 := hs1.of_upd h2 (by decide) (by decide)
  refine wp_dp (op2_imm (by decide)) fun s3 h3 => ?_
  have hs3 := hs2.of_upd h3 (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s4 h4 => ?_
  have hs4 := hs3.of_upd h4 (by decide) (by decide)
  refine VG.Proof.X448.Arm.load_ok hs4 (by omega) fun s5 h5 => ?_
  have hs5 := hs4.of_upd h5 (by decide) (by decide)
  refine wp_dp (op2_reg _ _) fun s6 h6 => ?_
  have hs6 := hs5.of_upd h6 (by decide) (by decide)
  refine VG.Proof.X448.Arm.store_ok hs6 (by simp only [TMP]; omega) fun s7 h7 => WP.block_nil ⟨?_, ?_⟩
  · rw [h7.mem, h6.mem, h5.mem, h4.mem, h3.mem, h2.mem, h1.mem, h6.gpr]
    change s.mem.writeW _ (s5.gpr .r3 - s5.gpr .r2) = _
    rw [h5.other .r3 (by decide), h4.gpr, h5.gpr, h4.mem, h3.mem, h2.mem, h1.mem]
    change s.mem.writeW _ (s3.gpr .r3 + s3.gpr .r2 - VG.Proof.X448.Arm.word s.mem base (b + 4 * i)) = _
    rw [h3.other .r3 (by decide), h2.other .r3 (by decide), h1.gpr, h3.gpr]
    change s.mem.writeW _ (VG.Proof.X448.Arm.word s.mem base (a + 4 * i) + (s2.gpr .r2 + 65536) - _) = _
    rw [h2.gpr]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, VG.Proof.X448.Arm.subK_nat, BitVec.toNat_ofNat]
    change (2 ^ 32 - VG.Proof.X448.Arm.limbs s.mem base b i + (VG.Proof.X448.Arm.limbs s.mem base a i + VG.Proof.X448.Radix16.bias i) % 2 ^ 32) % 2 ^ 32 =
      (VG.Proof.X448.Arm.limbs s.mem base a i + VG.Proof.X448.Radix16.bias i - VG.Proof.X448.Arm.limbs s.mem base b i) % 2 ^ 32
    have h := VG.Proof.X448.Radix16.bias_bound i
    simp only [VG.Proof.X448.Radix16.radix] at ab bb h
    omega
  · exact VG.Proof.X448.Arm.rest_keeps ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans
      ((h3.rest (by decide)).trans ((h4.rest (by decide)).trans ((h5.rest (by decide)).trans
      ((h6.rest (by decide)).trans (h7.rest _)))))))

theorem add_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.Arm.Slot o) (ha : VG.Proof.X448.Arm.Slot a) (hb : VG.Proof.X448.Arm.Slot b) (ab : VG.Proof.X448.Arm.Bounded s.mem base a) (bb : VG.Proof.X448.Arm.Bounded s.mem base b) :
    WP isa (.block (Impl.X448.Arm.add o a b)) s fun t =>
      VG.Proof.X448.Arm.Op base o s t ∧ VG.Proof.X448.Arm.Bounded t.mem base o ∧ VG.Proof.X448.Arm.F t.mem base o = VG.Proof.X448.Arm.F s.mem base a + VG.Proof.X448.Arm.F s.mem base b := by
  let f := fun i => VG.Proof.X448.Arm.limbs s.mem base a i + VG.Proof.X448.Arm.limbs s.mem base b i
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := by
    intro i hi
    have h1 := ab i hi
    have h2 := bb i hi
    change VG.Proof.X448.Arm.limbs s.mem base a i + VG.Proof.X448.Arm.limbs s.mem base b i ≤ _
    simp only [VG.Proof.X448.Radix16.radix] at h1 h2 ⊢
    omega
  refine WP.mono (VG.Proof.X448.Arm.columns_normalize hs ho fb (VG.Proof.X448.Arm.columns_ok hs (by decide : .r0 ∉ clob ∧ .r6 ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_add ?_⟩
  · intro i hi t ts tm _
    refine WP.mono (VG.Proof.X448.Arm.addStep_ok ts ha hb hi) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    rw [VG.Proof.X448.Arm.input_limb tm ha hi, VG.Proof.X448.Arm.input_limb tm hb hi] at um
    exact um
  · rw [tv, VG.Proof.X448.Radix16.valN_add]

theorem sub_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.Arm.Slot o) (ha : VG.Proof.X448.Arm.Slot a) (hb : VG.Proof.X448.Arm.Slot b) (ab : VG.Proof.X448.Arm.Bounded s.mem base a) (bb : VG.Proof.X448.Arm.Bounded s.mem base b) :
    WP isa (.block (Impl.X448.Arm.sub o a b)) s fun t =>
      VG.Proof.X448.Arm.Op base o s t ∧ VG.Proof.X448.Arm.Bounded t.mem base o ∧ VG.Proof.X448.Arm.F t.mem base o = VG.Proof.X448.Arm.F s.mem base a - VG.Proof.X448.Arm.F s.mem base b := by
  let f := VG.Proof.X448.Radix16.difference (VG.Proof.X448.Arm.limbs s.mem base a) (VG.Proof.X448.Arm.limbs s.mem base b)
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := fun i hi => Nat.le_of_lt (VG.Proof.X448.Radix16.difference_bound ab i hi)
  refine WP.mono (VG.Proof.X448.Arm.columns_normalize hs ho fb (VG.Proof.X448.Arm.columns_ok hs (by decide : .r0 ∉ clob ∧ .r6 ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_sub ?_⟩
  · intro i hi t ts tm _
    have ea := VG.Proof.X448.Arm.input_limb tm ha hi
    have eb := VG.Proof.X448.Arm.input_limb tm hb hi
    refine WP.mono (VG.Proof.X448.Arm.subStep_ok ts ha hb hi (ea ▸ ab i hi) (eb ▸ bb i hi)) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    simp only [VG.Proof.X448.Radix16.difference, ea, eb] at um
    exact um
  · rw [Nat.add_mod, tv, ← Nat.add_mod, VG.Proof.X448.Radix16.difference_val bb, Nat.add_mul_mod_self_right]

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.RowPass`. -/
section

/-!
# X448 on ARMv7: multiplication-row carry propagation

The instruction rules and carry-chain arithmetic are shared with X25519. This
pass handles the 28 limbs of X448.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X25519.Arm

/-- After `k` limbs of `carryPass rb o src` from `s0`, for the sums `c` and the
carry `cin`. -/
structure CarryInv (rb : Reg) (o : Nat) (s0 : State) (c : Nat → Nat) (cin k : Nat) (s : State) :
    Prop where
  rest : Rest [.r2, .r3, .r4, .r5] s0 s
  r5 : (s.gpr .r5).toNat = chain c cin k
  frame : Frame [⟨State.addr (s0.gpr rb) + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem (State.addr (s0.gpr rb)) (o + 4 * j) = VG.Proof.X25519.Arm.out c cin j

theorem carryPass_ok {rb : Reg} {o : Nat} {src : Nat → List Instr} {s0 : State} {c : Nat → Nat}
    {cin : Nat} (hrb : rb ∉ [.r2, .r3, .r4, .r5]) (ho : o + 112 ≤ 4096)
    (hfit : (s0.gpr rb).toNat + o + 112 ≤ 2 ^ 32)
    (hw : ∀ k < 28, InRegions s0.wr (State.addr (s0.gpr rb) + BitVec.ofNat 64 (o + 4 * k)) 4)
    (h6 : s0.gpr .r6 = mask16) (h5 : (s0.gpr .r5).toNat = cin)
    (hc : ∀ k < 28, c k + 65536 ≤ 2 ^ 32) (hcin : cin < 65536)
    (hsrc : ∀ k < 28, ∀ s, VG.Proof.X448.Arm.CarryInv rb o s0 c cin k s →
      WP isa (.block (src k)) s fun s' =>
        (s'.gpr .r3).toNat = c k ∧ Rest [.r2, .r3, .r4] s s' ∧ s'.mem = s.mem) :
    WP isa (.block (carryPass rb o src)) s0 (VG.Proof.X448.Arm.CarryInv rb o s0 c cin 28) := by
  have hr := not_mem4 hrb
  refine wp_range_flatMap (M := isa) (VG.Proof.X448.Arm.CarryInv rb o s0 c cin) (fun k s hk h => ?_) 28 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, by rw [h5]; rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  refine WP.append (hsrc k hk s h) fun s1 ⟨h3, hr1, hm1⟩ => ?_
  have hrb1 : s1.gpr rb = s0.gpr rb := by
    rw [hr1.gpr _ (by simp [hr.1, hr.2.1, hr.2.2.1]), h.rest.gpr _ hrb]
  have h51 : s1.gpr .r5 = s.gpr .r5 := hr1.gpr _ (by decide)
  have hsum := sum_lt hc hcin hk
  refine WP.mono (VG.Proof.X25519.Arm.carryStep_ok (a := State.addr (s0.gpr rb) + BitVec.ofNat 64 (o + 4 * k))
    ⟨hr.2.1, hr.2.2.1⟩ (by omega) (by rw [hrb1]; exact VG.Proof.X25519.Arm.ea (by omega))
    (by rw [hr1.wr, h.rest.wr]; exact hw k hk)
    (by rw [hr1.gpr _ (by decide), h.rest.gpr _ (by decide), h6])
    (by rw [h3, h51, h.r5]; exact hsum)) fun s2 ⟨e5, ⟨v, hv, hm2⟩, hr2⟩ => ?_
  rw [h3, h51, h.r5] at e5 hv
  rw [hm1] at hm2
  refine ⟨h.rest.trans ((hr1.mono (by decide)).trans (hr2.mono (by decide))), by rw [e5]; rfl, ?_,
    fun j hj => ?_⟩
  · rw [hm2]
    refine (h.frame.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) v (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    rw [List.mem_singleton.mp hr']
    exact Region.sub_prefix (by omega)
  · rw [hm2]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.outs j hj
    · rw [wd_write_self, hv]; rfl

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.RowMem`. -/
section

/-!
# X448 on ARMv7: the multiplication-row working space

A row uses a second pointer, `r7`, at a public word offset from the
working-space pointer in `r0`.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm
open VG.Proof.X25519.Arm

structure RowCtx (b : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = b
  fit : b.toNat + 4096 ≤ 2 ^ 32
  wr : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr

theorem RowCtx.of_rest {b : BitVec 32} {s t : State} {ws : List Reg} (h : VG.Proof.X448.Arm.RowCtx b s)
    (hr : Rest ws s t) (h0 : Reg.r0 ∉ ws) : VG.Proof.X448.Arm.RowCtx b t :=
  ⟨(hr.gpr _ h0).trans h.r0, h.fit, hr.wr ▸ h.wr⟩

theorem RowCtx.ea {b : BitVec 32} {s : State} (h : VG.Proof.X448.Arm.RowCtx b s) {d : Nat} (hd : d < 4096) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = State.addr b + BitVec.ofNat 64 d := by
  rw [h.r0]; exact addr_add (by have := h.fit; omega)

theorem RowCtx.inW {b : BitVec 32} {s : State} (h : VG.Proof.X448.Arm.RowCtx b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions s.wr (State.addr b + BitVec.ofNat 64 d) n := in_base h.wr (by omega) (by omega)

theorem RowCtx.inR {b : BitVec 32} {s : State} (h : VG.Proof.X448.Arm.RowCtx b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions (s.rd ++ s.wr) (State.addr b + BitVec.ofNat 64 d) n :=
  in_base (List.mem_append_right _ h.wr) (by omega) (by omega)

theorem rowLoad_ok {b : BitVec 32} {s : State} (hc : VG.Proof.X448.Arm.RowCtx b s) {t : Reg} {d : Nat}
    (hd : d + 4 ≤ 4096) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t (s.mem.readW (State.addr b + BitVec.ofNat 64 d) 32) →
      WP isa (.block is) s' Q) : WP isa (.block (ld t d :: is)) s Q :=
  wp_ldr (by omega) (hc.ea (by omega)) (hc.inR hd) k

abbrev accw (m : Mem) (B : Addr) (k : Nat) : Nat := wd m B (ACC + 4 * k)

theorem wd_shift (m : Mem) (B : Addr) (a d : Nat) : wd m (B + BitVec.ofNat 64 a) d = wd m B (a + d) := by
  unfold wd; rw [Offset.add_add]

theorem ACC_eq : ACC = 3584 := rfl

theorem chain_zero (c : Nat → Nat) (n : Nat) : chain c 0 n = Radix16.carry c n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [chain, Radix16.carry, ih]; rfl

theorem out_zero (c : Nat → Nat) (k : Nat) : VG.Proof.X25519.Arm.out c 0 k = Radix16.digit c k := by
  rw [VG.Proof.X25519.Arm.out, Radix16.digit, VG.Proof.X448.Arm.chain_zero]; rfl

section
variable {b : BitVec 32}

theorem addr7 (hfit : b.toNat + 4096 ≤ 2 ^ 32) {i : Nat} (hi : 4 * i < 4096) :
    State.addr (b + BitVec.ofNat 32 (4 * i)) = State.addr b + BitVec.ofNat 64 (4 * i) :=
  addr_add (by omega)

theorem toNat7 (hfit : b.toNat + 4096 ≤ 2 ^ 32) {i : Nat} (hi : 4 * i < 4096) :
    (b + BitVec.ofNat 32 (4 * i)).toNat = b.toNat + 4 * i := by
  rw [toNat_add_lt (by rw [toNat_imm (by omega)]; omega), toNat_imm (by omega)]

theorem ea7 (hfit : b.toNat + 4096 ≤ 2 ^ 32) {i d : Nat} (h : 4 * i + d < 4096) :
    State.addr (b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 d) =
      State.addr b + BitVec.ofNat 64 (4 * i + d) := by
  rw [Offset.add_add]; exact addr_add (by omega)

end

/-- After `i` rows the initialized product limbs represent `a[0..i] * b`. -/
structure RowInv (b : BitVec 32) (x y : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : VG.Proof.X448.Arm.RowCtx b s
  rest : Rest VG.Proof.X448.Arm.clob s0 s
  r6 : s.gpr .r6 = mask16
  r7 : s.gpr .r7 = b + BitVec.ofNat 32 (4 * i)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (28 - i)
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 224⟩] s0.mem s.mem
  lt : ∀ k < i + 28, VG.Proof.X448.Arm.accw s.mem (State.addr b) k < 65536
  val : Radix16.valN (VG.Proof.X448.Arm.accw s.mem (State.addr b)) (i + 28) =
    Radix16.valN (VG.Proof.X448.Arm.limbs s0.mem (State.addr b) x) i * VG.Proof.X448.Arm.fe s0.mem (State.addr b) y

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Init`. -/
section

/-!
# X448 on ARMv7: initialize multiplication

The first 28 accumulator words are zero; subsequent rows initialize the
remaining words.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X25519.Arm

variable {b : BitVec 32}

theorem rowStore_ok {s : State} (hc : VG.Proof.X448.Arm.RowCtx b s) {t : Reg} {d : Nat}
    (hd : d + 4 ≤ 4096) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd s s' (s.mem.writeW (State.addr b + BitVec.ofNat 64 d) (s.gpr t)) →
      WP isa (.block is) s' Q) : WP isa (.block (st t d :: is)) s Q :=
  wp_str (by omega) (hc.ea (by omega)) (hc.inW hd) k

theorem zeroAcc_ok {s : State} (hc : VG.Proof.X448.Arm.RowCtx b s) :
    WP isa (.block zeroAcc) s fun s' => (∀ j < 28, VG.Proof.X448.Arm.accw s'.mem (State.addr b) j = 0) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 112⟩] s.mem s'.mem ∧ Rest [.r3] s s' := by
  have hA := VG.Proof.X448.Arm.ACC_eq
  unfold zeroAcc
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ j < n, VG.Proof.X448.Arm.accw s'.mem (State.addr b) j = 0) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 112⟩] s1.mem s'.mem ∧ Rest [] s1 s' ∧ s'.gpr .r3 = 0)
    (fun n s' hn ⟨h1, h2, h3, h4⟩ => ?_) 28 (Nat.le_refl _) s1
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _, u1.gpr⟩)
    fun s' ⟨h1, h2, h3, _⟩ => ⟨h1, by rw [← u1.mem]; exact h2,
      (u1.rest (by decide)).trans (h3.mono (by decide))⟩
  refine VG.Proof.X448.Arm.rowStore_ok (hc1.of_rest h3 (by decide)) (d := ACC + 4 * n) (by omega) fun s2 u2 =>
    WP.block_nil ⟨fun j hj => ?_, ?_, h3.trans (u2.rest _), by rw [u2.gpr, h4]⟩
  · rw [VG.Proof.X448.Arm.accw, u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h1 j hj
    · rw [wd_write_self, h4]; rfl
  · rw [u2.mem]
    exact h2.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

theorem mulPre_ok {x y : Nat} {s : State} (hc : VG.Proof.X448.Arm.RowCtx b s) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block mulPre) s (VG.Proof.X448.Arm.RowInv b x y s 0) := by
  unfold mulPre
  refine WP.append (VG.Proof.X448.Arm.zeroAcc_ok hc) fun s1 ⟨hz, hf, hr⟩ => ?_
  have hc1 := hc.of_rest hr (by decide)
  refine wp_mov (op2_reg _ _) fun s2 h2 => wp_mov (op2_imm (by decide)) fun s3 h3 => WP.block_nil ?_
  have hr3 : Rest VG.Proof.X448.Arm.clob s s3 :=
    (hr.mono (by decide)).trans ((h2.rest (by decide)).trans (h3.rest (by decide)))
  have hm3 : s3.mem = s1.mem := by rw [h3.mem, h2.mem]
  refine ⟨hc.of_rest hr3 (by decide), hr3, (hr3.gpr _ (by decide)).trans h6,
    ?_, h3.gpr, ?_, fun k hk => ?_, ?_⟩
  · rw [h3.other .r7 (by decide), h2.gpr, hc1.r0]
    exact (BitVec.add_zero b).symm
  · rw [hm3]
    exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  · rw [hm3, hz k hk]; decide
  · rw [hm3, Radix16.valN_congr (g := fun _ => 0) (fun k hk => hz k hk), Radix16.valN_zero]
    exact (Nat.zero_mul _).symm

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Row`. -/
section

/-!
# X448 on ARMv7: one row of multiplication

The carries keep each multiply-add within a 32-bit word.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X25519.Arm

variable {b : BitVec 32}

theorem row_ok {x y : Nat} (hx : x + 112 ≤ ACC) (hy : y + 112 ≤ ACC) {s0 : State}
    (hlx : VG.Proof.X448.Arm.Bounded s0.mem (State.addr b) x) (hly : VG.Proof.X448.Arm.Bounded s0.mem (State.addr b) y) {i : Nat} (hi : i < 28)
    {s : State} (h : VG.Proof.X448.Arm.RowInv b x y s0 i s) :
    WP isa (.block (row x y)) s fun s' =>
      VG.Proof.X448.Arm.RowInv b x y s0 (i + 1) s' ∧ s'.z = decide (28 - (i + 1) = 0) := by
  have hA := VG.Proof.X448.Arm.ACC_eq
  have hfit := h.ctx.fit
  have hframe0 : ∀ z : Nat, z + 112 ≤ ACC → ∀ k < 28,
      VG.Proof.X448.Arm.limbs s.mem (State.addr b) z k = VG.Proof.X448.Arm.limbs s0.mem (State.addr b) z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  simp only [row, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * i)) (by omega)
    (by rw [h.r7, VG.Proof.X448.Arm.ea7 hfit (by omega), Nat.add_comm]) (h.ctx.inR (by omega)) fun s1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have hr2 : Rest [.r1, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : VG.Proof.X448.Arm.RowCtx b s2 := h.ctx.of_rest hr2 (by decide)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e1 : (s2.gpr .r1).toNat = VG.Proof.X448.Arm.limbs s0.mem (State.addr b) x i := by
    rw [u2.other _ (by decide), u1.gpr, ← hframe0 x hx i hi]
  have e7 : s2.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hr2.gpr _ (by decide), h.r7]
  have P7 : State.addr (s2.gpr .r7) = State.addr b + BitVec.ofNat 64 (4 * i) := by
    rw [e7]; exact VG.Proof.X448.Arm.addr7 hfit (by omega)
  have hlt : ∀ j < 28, Radix16.rowC (VG.Proof.X448.Arm.accw s.mem (State.addr b)) (VG.Proof.X448.Arm.limbs s0.mem (State.addr b) x)
      (VG.Proof.X448.Arm.limbs s0.mem (State.addr b) y) i j + 65536 ≤ 2 ^ 32 := fun j hj =>
    VG.Proof.X25519.Arm.rowC_le (hlx i hi) (hly j hj) (h.lt (i + j) (by omega))
  refine WP.append (VG.Proof.X448.Arm.carryPass_ok (rb := .r7) (o := ACC) (s0 := s2)
    (c := Radix16.rowC (VG.Proof.X448.Arm.accw s.mem (State.addr b)) (VG.Proof.X448.Arm.limbs s0.mem (State.addr b) x) (VG.Proof.X448.Arm.limbs s0.mem (State.addr b) y) i)
    (cin := 0) (by decide) (by omega) (by rw [e7, VG.Proof.X448.Arm.toNat7 hfit (by omega)]; omega)
    (fun k hk => by rw [P7, Offset.add_add]; exact hc2.inW (by omega))
    (by rw [hr2.gpr _ (by decide), h.r6]) (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    have hc' : VG.Proof.X448.Arm.RowCtx b s' := hc2.of_rest hp'.rest (by decide)
    have hf' : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [P7, Offset.add_add] at this
    change WP isa (.block [ld .r2 (y + 4 * k), .mul .r2 .r1 .r2,
      .ldr .r3 .r7 (ACC + 4 * k), .dp .add .r3 .r3 (.reg .r2)]) s' _
    refine VG.Proof.X448.Arm.rowLoad_ok hc' (d := y + 4 * k) (by omega) fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 4 * k))) (by omega)
      (by rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), e7,
        VG.Proof.X448.Arm.ea7 hfit (by omega)]) (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc'.inR (by omega))
      fun t3 v3 => ?_
    refine wp_dp (op2_reg _ _) fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have ey : (t1.gpr .r2).toNat = VG.Proof.X448.Arm.limbs s0.mem (State.addr b) y k := by
        rw [v1.gpr, ← hframe0 y hy k hk, ← hm2]
        show wd s'.mem _ _ = wd s2.mem _ _
        exact wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      have ea : (t1.gpr .r1).toNat = VG.Proof.X448.Arm.limbs s0.mem (State.addr b) x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      have hab := Nat.mul_le_mul (Nat.le_of_lt_succ (hlx i hi)) (Nat.le_of_lt_succ (hly k hk))
      have e2 : (t2.gpr .r2).toNat = VG.Proof.X448.Arm.limbs s0.mem (State.addr b) x i * VG.Proof.X448.Arm.limbs s0.mem (State.addr b) y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; omega), ea, ey]
      have e3 : (t3.gpr .r3).toNat = VG.Proof.X448.Arm.accw s.mem (State.addr b) (i + k) := by
        rw [v3.gpr, v2.mem, v1.mem, VG.Proof.X448.Arm.accw, ← hm2]
        show wd s'.mem _ _ = _
        rw [wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)]
        congr 1; omega
      have := hlt k hk
      rw [v4.gpr]
      show (t3.gpr .r3 + t3.gpr .r2).toNat = _
      rw [v3.other .r2 (by decide), toNat_add_lt (by rw [e3, e2]; simp only [Radix16.rowC] at this; omega), e3, e2,
        Radix16.rowC, Nat.add_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · -- The carry, and the next row.
    have hc3 : VG.Proof.X448.Arm.RowCtx b s3 := hc2.of_rest hp.rest (by decide)
    have e7' : s3.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hp.rest.gpr _ (by decide), e7]
    refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 112))) (by omega)
      (by rw [e7', VG.Proof.X448.Arm.ea7 hfit (by omega)]) (hc3.inW (by omega)) fun s4 u4 => ?_
    refine wp_dp (op2_imm (by decide)) fun s5 u5 => wp_subs (op2_imm (by decide)) fun s6 u6 hz => ?_
    refine WP.block_nil ?_
    have hr6 : Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s s6 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans (u6.rest (by decide)))))
    have hm6 : s6.mem = s3.mem.writeW (State.addr b + BitVec.ofNat 64 (4 * i + (ACC + 112))) (s3.gpr .r5) := by
      rw [u6.mem, u5.mem, u4.mem]
    have hpf : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + ACC), 112⟩] s.mem s3.mem := by
      have := hp.frame; rw [P7, Offset.add_add] at this; rw [← hm2]; exact this
    have hr9 : s6.gpr .r9 = BitVec.ofNat 32 (28 - (i + 1)) := by
      rw [u6.gpr, u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.r9]
      have t1 : (1 : BitVec 32).toNat = 1 := rfl
      apply BitVec.eq_of_toNat_eq
      rw [toNat_sub_le (by rw [toNat_imm (by omega), t1]; omega), toNat_imm (by omega), toNat_imm (by omega),
        t1]
      omega
    -- The limbs of `ACC` after the row.
    have hacc : ∀ k < i + 29, VG.Proof.X448.Arm.accw s6.mem (State.addr b) k =
        Radix16.rowAcc (VG.Proof.X448.Arm.accw s.mem (State.addr b)) (VG.Proof.X448.Arm.limbs s0.mem (State.addr b) x) (VG.Proof.X448.Arm.limbs s0.mem (State.addr b) y) i k := by
      intro k hk
      rw [VG.Proof.X448.Arm.accw, hm6]
      rcases Nat.lt_or_ge k (i + 28) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_frame hpf fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)]
          simp only [Radix16.rowAcc, hki, ite_true]
        · have := hp.outs (k - i) (by omega)
          rw [P7, VG.Proof.X448.Arm.wd_shift, show 4 * i + (ACC + 4 * (k - i)) = ACC + 4 * k by omega] at this
          rw [this, VG.Proof.X448.Arm.out_zero]
          simp only [Radix16.rowAcc, show ¬ k < i by omega, hk', ite_false, ite_true]
      · rw [show ACC + 4 * k = 4 * i + (ACC + 112) by omega, wd_write_self, hp.r5, VG.Proof.X448.Arm.chain_zero]
        simp only [Radix16.rowAcc, show ¬ k < i by omega, show ¬ k < i + 28 by omega, ite_false]
    refine ⟨⟨hc3.of_rest ((u4.rest [.r7, .r9]).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
        (by decide), h.rest.trans (hr6.mono (by decide)), by rw [hr6.gpr _ (by decide), h.r6],
      ?_, hr9, ?_, fun k hk => ?_, ?_⟩, ?_⟩
    · rw [u6.other _ (by decide), u5.gpr, u4.gpr, e7']
      show b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
      rw [Offset.add_add, Nat.mul_succ]
    · rw [hm6]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
    · rw [hacc k hk]
      exact Radix16.rowAcc_lt (fun k hk => h.lt k (by omega)) (fun j hj => by have := hlt j hj; change _ ≤ 2 ^ 32 - 65536; omega) k hk
    · rw [Radix16.valN_congr hacc]; exact Radix16.row_val h.val
    · rw [hz, ← u6.gpr, hr9, ofNat_beq_zero (by omega)]

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.MulLoop`. -/
section

/-!
# X448 on ARMv7: the multiplication loop

All 28 rows terminate at a public counter, producing 56 bounded product limbs.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X25519.Arm

theorem mulLoop_ok {b : BitVec 32} {x y : Nat} (hx : VG.Proof.X448.Arm.Slot x) (hy : VG.Proof.X448.Arm.Slot y)
    {s0 s : State} (hlx : VG.Proof.X448.Arm.Bounded s0.mem (State.addr b) x) (hly : VG.Proof.X448.Arm.Bounded s0.mem (State.addr b) y)
    (hs : VG.Proof.X448.Arm.RowInv b x y s0 0 s) :
    WP isa (.loop (.block (row x y)) .ne) s (VG.Proof.X448.Arm.RowInv b x y s0 28) := by
  refine WP.loop (M := isa)
    (fun n s' => ∃ i, n = 28 - i ∧ i < 28 ∧ VG.Proof.X448.Arm.RowInv b x y s0 i s') ?_ 28 s ⟨0, rfl, by decide, hs⟩
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (VG.Proof.X448.Arm.row_ok hx hy hlx hly hi hr) fun t ⟨ht, hz⟩ => ?_
  by_cases h28 : i + 1 = 28
  · refine .inl ⟨by rw [eval_ne, hz]; simp only [h28, decide_true, Bool.not_true], ?_⟩
    rw [h28] at ht
    exact ht
  · exact .inr ⟨by rw [eval_ne, hz]; simp; omega,
      28 - (i + 1), by omega, i + 1, rfl, by omega, ht⟩

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Reduce`. -/
section

/-!
# X448 on ARMv7: reducing product limbs

The upper half folds using `2^448 = 2^224 + 1` modulo the field prime.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_dp op2_reg)

theorem loadAdd_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {d : Nat} (hd : d + 4 ≤ 4096) :
    WP isa (.block [ld .r2 d, .dp .add .r3 .r3 (.reg .r2)]) s fun t =>
      t.gpr .r3 = s.gpr .r3 + VG.Proof.X448.Arm.word s.mem base d ∧ t.mem = s.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r2] s t := by
  refine VG.Proof.X448.Arm.load_ok hs hd fun t ht => wp_dp (op2_reg _ _) fun u hu => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hu.gpr]
    change t.gpr .r3 + t.gpr .r2 = _
    rw [ht.other .r3 (by decide), ht.gpr]
  · exact hu.mem.trans ht.mem
  · exact VG.Proof.X448.Arm.rest_keeps ((ht.rest (by decide)).trans (hu.rest (by decide)))

/-- A bounded sum of words, accumulated into `r3`. -/
def addWords (ds : List Nat) : List Instr :=
  ds.flatMap fun d => [ld .r2 d, .dp .add .r3 .r3 (.reg .r2)]

theorem addWords_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {ds : List Nat}
    (hd : ∀ d ∈ ds, d + 4 ≤ 4096) :
    WP isa (.block (VG.Proof.X448.Arm.addWords ds)) s fun t =>
      t.gpr .r3 = s.gpr .r3 + (ds.map fun d => VG.Proof.X448.Arm.word s.mem base d).sum ∧
      t.mem = s.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r2] s t := by
  induction ds generalizing s with
  | nil => exact WP.block_nil ⟨(BitVec.add_zero _).symm, rfl, Keeps.refl _ _⟩
  | cons d ds ih =>
    change WP isa (.block (([ld .r2 d, .dp .add .r3 .r3 (.reg .r2)] : List Instr) ++ VG.Proof.X448.Arm.addWords ds)) s _
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.X448.Arm.loadAdd_ok hs (hd d List.mem_cons_self)) fun t ⟨tv, tm, tk⟩ => ?_
    refine WP.mono (ih (hs.of_keeps tk (by decide)) (fun d h => hd d (List.mem_cons_of_mem _ h)))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um.trans tm, tk.trans uk⟩
    rw [uv, tv, tm]
    simp only [List.map_cons, List.sum_cons, BitVec.add_assoc]

/-- The extra offsets folded into product limb `k`. -/
def colOffsets (k : Nat) : List Nat :=
  [ACC + 4 * (k + 28)] ++
    if k < 14 then [ACC + 4 * (k + 42)] else [ACC + 4 * (k + 14), ACC + 4 * (k + 28)]

theorem colOffsets_bound {k : Nat} (hk : k < 28) : ∀ d ∈ VG.Proof.X448.Arm.colOffsets k, d + 4 ≤ 4096 := by
  intro d hd
  simp only [VG.Proof.X448.Arm.colOffsets, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | hd
  · simp only [ACC]; omega
  · split at hd <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    · subst d; simp only [ACC]; omega
    · rcases hd with rfl | rfl <;> simp only [ACC] <;> omega

theorem reduceCol_code (k : Nat) : reduceCol k =
    [ld .r3 (ACC + 4 * k)] ++ VG.Proof.X448.Arm.addWords (VG.Proof.X448.Arm.colOffsets k) ++ [st .r3 (TMP + 4 * k)] := by
  unfold reduceCol VG.Proof.X448.Arm.colOffsets
  split <;> rfl

theorem reduceCol_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {k : Nat} (hk : k < 28)
    {f : Nat → Nat} (hf : ∀ i < 56, VG.Proof.X448.Arm.limbs s.mem base ACC i = f i)
    (hb : ∀ i < 56, f i < VG.Proof.X448.Radix16.radix) :
    WP isa (.block (reduceCol k)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.Arm.off base (TMP + 4 * k)) (BitVec.ofNat 32 (VG.Proof.X448.Radix16.reduced f k)) ∧
      VG.Proof.X448.Arm.Keeps [.r3, .r2] s t := by
  rw [VG.Proof.X448.Arm.reduceCol_code, List.append_assoc]
  refine VG.Proof.X448.Arm.load_ok hs (by simp only [ACC]; omega) fun t ht => ?_
  change WP isa (.block (VG.Proof.X448.Arm.addWords (VG.Proof.X448.Arm.colOffsets k) ++ ([st .r3 (TMP + 4 * k)] : List Instr))) t _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.addWords_ok (hs.of_upd ht (by decide) (by decide)) (VG.Proof.X448.Arm.colOffsets_bound hk))
    fun u ⟨uv, um, uk⟩ => ?_
  have us := (hs.of_upd ht (by decide) (by decide)).of_keeps uk (by decide)
  refine VG.Proof.X448.Arm.store_ok us (by simp only [TMP]; omega) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, um, ht.mem, uv, ht.gpr, ht.mem]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    have f0 := hf k (by omega)
    have f1 := hf (k + 28) (by omega)
    have b0 := hb k (by omega)
    have b1 := hb (k + 28) (by omega)
    by_cases h : k < 14
    · have f2 := hf (k + 42) (by omega)
      have b2 := hb (k + 42) (by omega)
      simp only [VG.Proof.X448.Arm.colOffsets, h, ite_true, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, VG.Proof.X448.Radix16.reduced, h, ite_true]
      change (VG.Proof.X448.Arm.limbs s.mem base ACC k + (VG.Proof.X448.Arm.limbs s.mem base ACC (k + 28) +
        (VG.Proof.X448.Arm.limbs s.mem base ACC (k + 42)) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
      rw [f0, f1, f2]
      simp only [VG.Proof.X448.Radix16.radix] at b0 b1 b2
      omega
    · have f2 := hf (k + 14) (by omega)
      have b2 := hb (k + 14) (by omega)
      simp only [VG.Proof.X448.Arm.colOffsets, h, ite_false, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, VG.Proof.X448.Radix16.reduced, h, ite_false]
      change (VG.Proof.X448.Arm.limbs s.mem base ACC k + (VG.Proof.X448.Arm.limbs s.mem base ACC (k + 28) +
        (VG.Proof.X448.Arm.limbs s.mem base ACC (k + 14) + (VG.Proof.X448.Arm.limbs s.mem base ACC (k + 28)) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
      rw [f0, f1, f2]
      simp only [VG.Proof.X448.Radix16.radix] at b0 b1 b2
      omega
  · exact (VG.Proof.X448.Arm.rest_keeps (ht.rest (by decide))).trans (uk.trans (VG.Proof.X448.Arm.rest_keeps (hv.rest _)))

/-- Fold all fifty-six product limbs into twenty-eight, ready for carries. -/
theorem reduce_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 56, VG.Proof.X448.Arm.limbs s.mem base ACC i = f i) (hb : ∀ i < 56, f i < VG.Proof.X448.Radix16.radix) :
    WP isa (.block ((List.range 28).flatMap reduceCol)) s fun t =>
      (∀ i < 28, VG.Proof.X448.Arm.limbs t.mem base TMP i = VG.Proof.X448.Radix16.reduced f i) ∧
      VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r2] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.Arm.limbs t.mem base TMP i = VG.Proof.X448.Radix16.reduced f i) ∧
    VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r2] s t
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block (reduceCol n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have ft : ∀ i < 56, VG.Proof.X448.Arm.limbs t.mem base ACC i = f i := by
      intro i hi
      change (VG.Proof.X448.Arm.word t.mem base (ACC + 4 * i)).toNat = _
      rw [tm.word (Or.inl (by simp only [ACC, TMP]; omega)) (by simp only [ACC]; omega)]
      exact hf i hi
    refine WP.mono (VG.Proof.X448.Arm.reduceCol_ok (hs.of_keeps tk (by decide)) hn ft hb) fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.Arm.Outside base (TMP + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.Arm.writeW_outside _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (VG.Proof.X448.Arm.word u.mem base (TMP + 4 * i)).toNat = _
    rw [um, VG.Proof.X448.Arm.word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (VG.Proof.X448.Radix16.reduced_bound hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Mul`. -/
section

/-!
# X448 on ARMv7: field multiplication

The row loop produces the 56 limbs of the product, which are folded and
normalized modulo the prime.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

theorem frame_outside {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Frame [⟨VG.Proof.X448.Arm.off base o, n⟩] m m') (hn : o + n ≤ 8192) : VG.Proof.X448.Arm.Outside base o n m m' := by
  intro x hx
  refine h x fun r hr hc => ?_
  rw [List.mem_singleton.mp hr] at hc
  change (x - VG.Proof.X448.Arm.off base o).toNat + 1 ≤ n at hc
  simp only [VG.Proof.X448.Arm.off] at hc
  have hi := (Offset.lt_iff x base (d := o) (n := n) (by omega)).mp (by omega)
  simp only [VG.Proof.X448.Arm.ofs] at hx
  omega

theorem mul_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.Arm.Slot o) (ha : VG.Proof.X448.Arm.Slot a) (hb : VG.Proof.X448.Arm.Slot b) (ab : VG.Proof.X448.Arm.Bounded s.mem base a) (bb : VG.Proof.X448.Arm.Bounded s.mem base b) :
    WP isa (Impl.X448.Arm.mul o a b) s fun t =>
      VG.Proof.X448.Arm.Op base o s t ∧ VG.Proof.X448.Arm.Bounded t.mem base o ∧ VG.Proof.X448.Arm.F t.mem base o = VG.Proof.X448.Arm.F s.mem base a * VG.Proof.X448.Arm.F s.mem base b := by
  let ptr := s.gpr .r0
  have pe : State.addr ptr = base := hs.r0
  have ctx : VG.Proof.X448.Arm.RowCtx ptr s := ⟨rfl, by change (s.gpr .r0).toNat + 4096 ≤ 2 ^ 32; have := hs.nowrap; omega,
    by rw [pe]; exact hs.wr⟩
  rw [Impl.X448.Arm.mul, WP.seq_iff]
  refine WP.mono (VG.Proof.X448.Arm.mulPre_ok (x := a) (y := b) ctx hs.mask) fun t ht => ?_
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.X448.Arm.mulLoop_ok ha hb (by rw [pe]; exact ab) (by rw [pe]; exact bb) ht) fun u hu => ?_
  have uk : VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.clob s u := VG.Proof.X448.Arm.rest_keeps hu.rest
  have us := hs.of_keeps uk (by decide)
  let f := VG.Proof.X448.Arm.limbs u.mem base ACC
  have fb : ∀ i < 56, f i < VG.Proof.X448.Radix16.radix := by
    intro i hi
    have := hu.lt i hi
    rw [pe] at this
    exact this
  have fv : VG.Proof.X448.Radix16.valN f 56 = VG.Proof.X448.Arm.fe s.mem base a * VG.Proof.X448.Arm.fe s.mem base b := by
    have := hu.val
    rw [pe] at this
    exact this
  have um : VG.Proof.X448.Arm.Outside base ACC 224 s.mem u.mem := by
    have hf := hu.frame
    rw [pe] at hf
    exact VG.Proof.X448.Arm.frame_outside hf (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.reduce_ok us (fun _ _ => rfl) fb) fun v ⟨vf, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  refine WP.mono (VG.Proof.X448.Arm.normalize_ok vs ho vf (VG.Proof.X448.Radix16.reduced_bound fb)) fun w ⟨wf, wm, wk⟩ => ?_
  have value : VG.Proof.X448.Arm.fe w.mem base o % Spec.X448.P = (VG.Proof.X448.Arm.fe s.mem base a * VG.Proof.X448.Arm.fe s.mem base b) % Spec.X448.P := by
    rw [show VG.Proof.X448.Arm.fe w.mem base o = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.normalized (VG.Proof.X448.Radix16.reduced f)) 28 from VG.Proof.X448.Radix16.valN_congr wf,
      VG.Proof.X448.Radix16.normalized_mod (VG.Proof.X448.Radix16.reduced_bound fb), VG.Proof.X448.Radix16.reduced_mod, fv]
  refine ⟨⟨?_, ?_⟩, ?_, toFe_mul value⟩
  · exact uk.trans ((vk.mono (by decide)).trans (wk.mono (by decide)))
  · exact (FieldMem.work um (by omega) (by omega)).trans
      ((FieldMem.work vm (by decide) (by decide)).trans wm)
  · intro i hi
    rw [wf i hi]
    exact VG.Proof.X448.Radix16.digit_lt _ _

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Small`. -/
section

/-!
# X448 on ARMv7: multiplication by a24

The 16-bit limbs keep multiplication by 39081 within a 32-bit word.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_mul wp_movw)

theorem smallStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {a i : Nat}
    (ha : VG.Proof.X448.Arm.Slot a) (hi : i < 28) (hc : (s.gpr .r5).toNat = 39081) :
    WP isa (.block [ld .r3 (a + 4 * i), .mul .r3 .r3 .r5, st .r3 (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.Arm.off base (TMP + 4 * i)) (BitVec.ofNat 32 (39081 * VG.Proof.X448.Arm.limbs s.mem base a i)) ∧
      VG.Proof.X448.Arm.Keeps [.r3, .r2] s t := by
  have ha' : a + 112 ≤ 3584 := ha
  refine VG.Proof.X448.Arm.load_ok hs (by omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide) (by decide)
  refine wp_mul fun u hu => ?_
  have us := ts.of_upd hu (by decide) (by decide)
  refine VG.Proof.X448.Arm.store_ok us (by simp only [TMP]; omega) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr, ht.gpr, ht.other .r5 (by decide)]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, hc, Nat.mul_comm _ 39081, BitVec.toNat_ofNat]
  · exact VG.Proof.X448.Arm.rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _)))

theorem smallInit_ok (s : State) :
    WP isa (.block [.movw .r5 39081]) s fun t =>
      (t.gpr .r5).toNat = 39081 ∧ t.mem = s.mem ∧ VG.Proof.X448.Arm.Keeps [.r5] s t := by
  refine wp_movw fun t ht => WP.block_nil ⟨?_, ht.mem, VG.Proof.X448.Arm.rest_keeps (ht.rest (by decide))⟩
  rw [ht.gpr]
  rfl

theorem mulSmall_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {o a : Nat}
    (ho : VG.Proof.X448.Arm.Slot o) (ha : VG.Proof.X448.Arm.Slot a) (ab : VG.Proof.X448.Arm.Bounded s.mem base a) :
    WP isa (.block (mulSmall o a)) s fun t => VG.Proof.X448.Arm.Op base o s t ∧ VG.Proof.X448.Arm.Bounded t.mem base o ∧
      VG.Proof.X448.Arm.F t.mem base o = Spec.X448.a24 * VG.Proof.X448.Arm.F s.mem base a := by
  let f := fun i => 39081 * VG.Proof.X448.Arm.limbs s.mem base a i
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := by
    intro i hi
    have h := Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))
    have hr : 39081 * VG.Proof.X448.Radix16.radix ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := by decide
    exact Nat.le_trans h hr
  refine WP.mono (VG.Proof.X448.Arm.columns_normalize hs ho fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_a24 ?_⟩
  · rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.X448.Arm.smallInit_ok s) fun t ⟨tc, tm, tk⟩ => ?_
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (VG.Proof.X448.Arm.columns_ok ts (by decide : Reg.r0 ∉ [Reg.r3, Reg.r2] ∧ Reg.r6 ∉ [Reg.r3, Reg.r2]) fb ?_) fun u ⟨uf, um, uk⟩ => ?_
    · intro i hi u us um uk
      have uc : (u.gpr .r5).toNat = 39081 := by rw [uk.1 _ (by decide), tc]
      refine WP.mono (VG.Proof.X448.Arm.smallStep_ok us ha hi uc) fun v ⟨vm, vk⟩ => ⟨?_, vk⟩
      rw [VG.Proof.X448.Arm.input_limb um ha hi, tm] at vm
      exact vm
    · refine ⟨uf, ?_, (tk.mono ?_).trans (uk.mono ?_)⟩
      · rw [← tm]; exact um
      · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide
  · rw [tv, VG.Proof.X448.Radix16.valN_scale]

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Copy`. -/
section

/-!
# X448 on ARMv7: copying field elements

Equal or disjoint source and destination slots preserve the original limbs.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

theorem copyStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {o a i : Nat}
    (ho : o + 112 ≤ 4096) (ha : a + 112 ≤ 4096) (hi : i < 28) :
    WP isa (.block [ld .r3 (a + 4 * i), st .r3 (o + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.Arm.off base (o + 4 * i)) (VG.Proof.X448.Arm.word s.mem base (a + 4 * i)) ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.clob s t := by
  refine VG.Proof.X448.Arm.load_ok hs (by omega) fun t ht => ?_
  refine VG.Proof.X448.Arm.store_ok (hs.of_upd ht (by decide) (by decide)) (by omega) fun u hu => WP.block_nil ⟨?_, ?_⟩
  · rw [hu.mem, ht.mem, ht.gpr]
  · exact VG.Proof.X448.Arm.rest_keeps ((ht.rest (by decide)).trans (hu.rest _))

theorem copy_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {o a : Nat}
    (ho : o + 112 ≤ 4096) (ha : a + 112 ≤ 4096)
    (hsep : o = a ∨ o + 112 ≤ a ∨ a + 112 ≤ o) :
    WP isa (.block (copy o a)) s fun t =>
      (∀ i < 28, VG.Proof.X448.Arm.limbs t.mem base o i = VG.Proof.X448.Arm.limbs s.mem base a i) ∧
      VG.Proof.X448.Arm.Outside base o 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.Arm.limbs t.mem base o i = VG.Proof.X448.Arm.limbs s.mem base a i) ∧
    (∀ i, n ≤ i → i < 28 → VG.Proof.X448.Arm.limbs t.mem base a i = VG.Proof.X448.Arm.limbs s.mem base a i) ∧
    VG.Proof.X448.Arm.Outside base o 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.clob s t
  have st : ∀ n t, n < 28 → inv n t →
      WP isa (.block [ld .r3 (a + 4 * n), st .r3 (o + 4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, ta, tm, tk⟩
    refine WP.mono (VG.Proof.X448.Arm.copyStep_ok (hs.of_keeps tk (by decide)) ho ha hn) fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.Arm.Outside base (o + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.Arm.writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    · intro i hi
      change (VG.Proof.X448.Arm.word u.mem base (o + 4 * i)).toNat = _
      rw [um, VG.Proof.X448.Arm.word_write t.mem base (by omega) (by omega)]
      by_cases h : i = n
      · rw [ite_eq_left h, h]; exact ta n (by omega) hn
      · rw [ite_eq_right h]; exact tf i (by omega)
    · intro i hi hi'
      change (VG.Proof.X448.Arm.word u.mem base (a + 4 * i)).toNat = _
      rw [out.word (by rcases hsep with h | h | h <;> omega) (by omega)]
      exact ta i (by omega) hi'
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s ?_)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  exact ⟨fun _ hi => by omega, fun _ _ _ => rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Swap`. -/
section

/-!
# X448 on ARMv7: constant-time conditional swaps

An XOR mask swaps limbs without a secret-dependent branch or memory address.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_dp op2_reg)

def mask (sw : Bool) : BitVec 32 := if sw then BitVec.allOnes 32 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 32) :
    a ^^^ ((a ^^^ b) &&& VG.Proof.X448.Arm.mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& VG.Proof.X448.Arm.mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [VG.Proof.X448.Arm.mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [VG.Proof.X448.Arm.mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem swapStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {x y i : Nat}
    (hx : VG.Proof.X448.Arm.Slot x) (hy : VG.Proof.X448.Arm.Slot y) (hi : i < 28) {sw : Bool} (hc : s.gpr .r5 = VG.Proof.X448.Arm.mask sw) :
    WP isa (.block
      [ld .r3 (x + 4 * i), ld .r2 (y + 4 * i), .dp .eor .r4 .r3 (.reg .r2),
        .dp .and .r4 .r4 (.reg .r5), .dp .eor .r3 .r3 (.reg .r4),
        .dp .eor .r2 .r2 (.reg .r4), st .r3 (x + 4 * i), st .r2 (y + 4 * i)]) s fun t =>
      t.mem = (s.mem.writeW (VG.Proof.X448.Arm.off base (x + 4 * i))
        (if sw then VG.Proof.X448.Arm.word s.mem base (y + 4 * i) else VG.Proof.X448.Arm.word s.mem base (x + 4 * i))).writeW
        (VG.Proof.X448.Arm.off base (y + 4 * i)) (if sw then VG.Proof.X448.Arm.word s.mem base (x + 4 * i) else VG.Proof.X448.Arm.word s.mem base (y + 4 * i)) ∧
      VG.Proof.X448.Arm.Keeps [.r3, .r2, .r4] s t := by
  have hx' : x + 112 ≤ 3584 := hx
  have hy' : y + 112 ≤ 3584 := hy
  have lx := hs.read (d := x + 4 * i) (n := 4) (by omega)
  have ly := hs.read (d := y + 4 * i) (n := 4) (by omega)
  have wx := hs.write (d := x + 4 * i) (n := 4) (by omega)
  have wy := hs.write (d := y + 4 * i) (n := 4) (by omega)
  have xe := hs.ea (d := x + 4 * i) (by omega)
  have ye := hs.ea (d := y + 4 * i) (by omega)
  have xb : x + 4 * i < 4096 := by omega
  have yb : y + 4 * i < 4096 := by omega
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
    State.load32, State.store32, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, xe, ye, xb, yb, hc, lx, ly, wx, wy,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [(VG.Proof.X448.Arm.xor_sel sw _ _).1, (VG.Proof.X448.Arm.xor_sel sw _ _).2]
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

/-- Reading two disjoint words after writing a limb pair. -/
theorem pair_write {m : Mem} {base : Addr} {x y n j : Nat} (hx : VG.Proof.X448.Arm.Slot x) (hy : VG.Proof.X448.Arm.Slot y)
    (hxy : x + 112 ≤ y ∨ y + 112 ≤ x) (hn : n < 28) (hj : j < 28) (vx vy : BitVec 32) :
    let m' := (m.writeW (VG.Proof.X448.Arm.off base (x + 4 * n)) vx).writeW (VG.Proof.X448.Arm.off base (y + 4 * n)) vy
    VG.Proof.X448.Arm.limbs m' base x j = (if j = n then vx.toNat else VG.Proof.X448.Arm.limbs m base x j) ∧
    VG.Proof.X448.Arm.limbs m' base y j = (if j = n then vy.toNat else VG.Proof.X448.Arm.limbs m base y j) := by
  have xb : x + 112 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 112 ≤ 8192 := Nat.le_trans hy (by decide)
  dsimp only
  constructor
  · simp only [VG.Proof.X448.Arm.limbs, VG.Proof.X448.Arm.word]
    rw [Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)]
    rw [show m.readW (VG.Proof.X448.Arm.off base (x + 4 * j)) 32 = VG.Proof.X448.Arm.word m base (x + 4 * j) from rfl]
    change (VG.Proof.X448.Arm.word (m.writeW (VG.Proof.X448.Arm.off base (x + 4 * n)) vx) base (x + 4 * j)).toNat = _
    rw [VG.Proof.X448.Arm.word_write m base (by omega) (by omega)]
    split <;> rfl
  · change (VG.Proof.X448.Arm.word ((m.writeW (VG.Proof.X448.Arm.off base (x + 4 * n)) vx).writeW (VG.Proof.X448.Arm.off base (y + 4 * n)) vy)
      base (y + 4 * j)).toNat = _
    rw [VG.Proof.X448.Arm.word_write (m.writeW (VG.Proof.X448.Arm.off base (x + 4 * n)) vx) base (by omega) (by omega)]
    by_cases h : j = n
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      apply congrArg BitVec.toNat
      exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- Swap all twenty-eight limbs under the mask, preserving all other bytes. -/
theorem cswap_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {x y : Nat} (hx : VG.Proof.X448.Arm.Slot x) (hy : VG.Proof.X448.Arm.Slot y)
    (hxy : x + 112 ≤ y ∨ y + 112 ≤ x) {sw : Bool} (hc : s.gpr .r5 = VG.Proof.X448.Arm.mask sw) :
    WP isa (.block (cswap x y)) s fun t =>
      (∀ i < 28, VG.Proof.X448.Arm.limbs t.mem base x i = if sw then VG.Proof.X448.Arm.limbs s.mem base y i else VG.Proof.X448.Arm.limbs s.mem base x i) ∧
      (∀ i < 28, VG.Proof.X448.Arm.limbs t.mem base y i = if sw then VG.Proof.X448.Arm.limbs s.mem base x i else VG.Proof.X448.Arm.limbs s.mem base y i) ∧
      VG.Proof.X448.Arm.Outside2 base x 112 y 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r2, .r4] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.Arm.limbs t.mem base x i = if sw then VG.Proof.X448.Arm.limbs s.mem base y i else VG.Proof.X448.Arm.limbs s.mem base x i) ∧
    (∀ i < n, VG.Proof.X448.Arm.limbs t.mem base y i = if sw then VG.Proof.X448.Arm.limbs s.mem base x i else VG.Proof.X448.Arm.limbs s.mem base y i) ∧
    VG.Proof.X448.Arm.Outside2 base x (4 * n) y (4 * n) s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r2, .r4] s t
  have xb : x + 112 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 112 ≤ 8192 := Nat.le_trans hy (by decide)
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block
      [ld .r3 (x + 4 * n), ld .r2 (y + 4 * n), .dp .eor .r4 .r3 (.reg .r2),
        .dp .and .r4 .r4 (.reg .r5), .dp .eor .r3 .r3 (.reg .r4),
        .dp .eor .r2 .r2 (.reg .r4), st .r3 (x + 4 * n), st .r2 (y + 4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tc := (tk.1 .r5 (by decide)).trans hc
    refine WP.mono (VG.Proof.X448.Arm.swapStep_ok (hs.of_keeps tk (by decide)) hx hy hn tc) fun u ⟨um, uk⟩ => ?_
    have ex : VG.Proof.X448.Arm.limbs t.mem base x n = VG.Proof.X448.Arm.limbs s.mem base x n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have ey : VG.Proof.X448.Arm.limbs t.mem base y n = VG.Proof.X448.Arm.limbs s.mem base y n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have pair := fun (j : Nat) (hj : j < 28) => VG.Proof.X448.Arm.pair_write (m := t.mem) (base := base) hx hy hxy hn hj
      (if sw then VG.Proof.X448.Arm.word t.mem base (y + 4 * n) else VG.Proof.X448.Arm.word t.mem base (x + 4 * n))
      (if sw then VG.Proof.X448.Arm.word t.mem base (x + 4 * n) else VG.Proof.X448.Arm.word t.mem base (y + 4 * n))
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · intro j hj
      rw [um, (pair j (by omega)).1]
      by_cases h : j = n
      · rw [ite_eq_left h, h]
        cases sw <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> with_reducible assumption
      · rw [ite_eq_right h]; exact tx j (by omega)
    · intro j hj
      rw [um, (pair j (by omega)).2]
      by_cases h : j = n
      · rw [ite_eq_left h, h]
        cases sw <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;> with_reducible assumption
      · rw [ite_eq_right h]; exact ty j (by omega)
    · refine (tm.mono (by omega) (by omega)).trans ?_
      intro p hp hq
      rw [um, VG.Proof.X448.Arm.writeW_outside _ _ _ (by omega : y + 4 * n + 4 ≤ 8192) p (by omega),
        VG.Proof.X448.Arm.writeW_outside _ _ _ (by omega : x + 4 * n + 4 ≤ 8192) p (by omega)]
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hi => by omega, fun _ hi => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Env`. -/
section

/-!
# X448 on ARMv7: the working space as field-element slots

Field operations update one of twenty-two slots, preserving bounded limbs in
every slot. The frame excludes saved registers, the swap bit and the scalar's
decoded bits.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

abbrev Index := Fin 22
abbrev Env := VG.Proof.X448.Arm.Index → Spec.X448.Fe

def E (m : Mem) (base : Addr) (i : VG.Proof.X448.Arm.Index) : Spec.X448.Fe := VG.Proof.X448.Arm.F m base (slot i.val)
def BoundedEnv (m : Mem) (base : Addr) : Prop := ∀ i : VG.Proof.X448.Arm.Index, VG.Proof.X448.Arm.Bounded m base (slot i.val)

def workRegs : List Reg := .r4 :: VG.Proof.X448.Arm.clob

structure Keep (base : Addr) (s t : State) : Prop where
  regs : VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.workRegs s t
  mem : VG.Proof.X448.Arm.Outside2 base 64 2816 ACC 512 s.mem t.mem

theorem Keep.refl (base : Addr) (s : State) : VG.Proof.X448.Arm.Keep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem Keep.trans {base : Addr} {s t u : State} (h : VG.Proof.X448.Arm.Keep base s t) (h' : VG.Proof.X448.Arm.Keep base t u) :
    VG.Proof.X448.Arm.Keep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem Keep.scr {base : Addr} {s t : State} (h : VG.Proof.X448.Arm.Keep base s t) (hs : VG.Proof.X448.Arm.Scr s base) : VG.Proof.X448.Arm.Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem slot_bound (i : VG.Proof.X448.Arm.Index) : VG.Proof.X448.Arm.Slot (slot i.val) := by
  simp only [VG.Proof.X448.Arm.Slot, slot, ACC]
  have := i.isLt
  omega

theorem slot_sep {i j : VG.Proof.X448.Arm.Index} (h : i ≠ j) : slot i.val + 112 ≤ slot j.val ∨ slot j.val + 112 ≤ slot i.val := by
  have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
  simp only [slot]
  omega

theorem Op.keep {base : Addr} {o : VG.Proof.X448.Arm.Index} {s t : State} (h : VG.Proof.X448.Arm.Op base (slot o.val) s t) : VG.Proof.X448.Arm.Keep base s t := by
  refine ⟨h.keeps.mono (fun _ hr => List.mem_cons_of_mem _ hr), ?_⟩
  intro p hp hq
  apply h.mem p _ hq
  have := o.isLt
  simp only [slot]
  omega

theorem E_update {base : Addr} {m m' : Mem} {o : VG.Proof.X448.Arm.Index} (h : VG.Proof.X448.Arm.FieldMem base (slot o.val) m m') :
    VG.Proof.X448.Arm.E m' base = Function.update (VG.Proof.X448.Arm.E m base) o (VG.Proof.X448.Arm.F m' base (slot o.val)) := by
  funext i
  by_cases hi : i = o
  · subst i; simp only [Function.update_self, VG.Proof.X448.Arm.E]
  · rw [Function.update_of_ne hi]
    simp only [VG.Proof.X448.Arm.E, VG.Proof.X448.Arm.F]
    rw [h.fe (VG.Proof.X448.Arm.slot_sep hi) (VG.Proof.X448.Arm.slot_bound i)]

theorem bounded_update {base : Addr} {m m' : Mem} {o : VG.Proof.X448.Arm.Index} (h : VG.Proof.X448.Arm.FieldMem base (slot o.val) m m')
    (hm : VG.Proof.X448.Arm.BoundedEnv m base) (ho : VG.Proof.X448.Arm.Bounded m' base (slot o.val)) : VG.Proof.X448.Arm.BoundedEnv m' base := by
  intro i
  by_cases hi : i = o
  · subst i; exact ho
  · intro j hj
    rw [h.limbs (VG.Proof.X448.Arm.slot_sep hi) (VG.Proof.X448.Arm.slot_bound i) hj]
    exact hm i j hj

def opMul (o a b : VG.Proof.X448.Arm.Index) (e : VG.Proof.X448.Arm.Env) : VG.Proof.X448.Arm.Env := Function.update e o (e a * e b)
def opAdd (o a b : VG.Proof.X448.Arm.Index) (e : VG.Proof.X448.Arm.Env) : VG.Proof.X448.Arm.Env := Function.update e o (e a + e b)
def opSub (o a b : VG.Proof.X448.Arm.Index) (e : VG.Proof.X448.Arm.Env) : VG.Proof.X448.Arm.Env := Function.update e o (e a - e b)
def opA24 (o a : VG.Proof.X448.Arm.Index) (e : VG.Proof.X448.Arm.Env) : VG.Proof.X448.Arm.Env := Function.update e o (Spec.X448.a24 * e a)
def opCopy (o a : VG.Proof.X448.Arm.Index) (e : VG.Proof.X448.Arm.Env) : VG.Proof.X448.Arm.Env := Function.update e o (e a)
def opSwap (x y : VG.Proof.X448.Arm.Index) (sw : Bool) (e : VG.Proof.X448.Arm.Env) : VG.Proof.X448.Arm.Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

theorem mulE {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.BoundedEnv s.mem base) (o a b : VG.Proof.X448.Arm.Index) :
    WP isa (Impl.X448.Arm.mul (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      VG.Proof.X448.Arm.Keep base s t ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ VG.Proof.X448.Arm.E t.mem base = VG.Proof.X448.Arm.opMul o a b (VG.Proof.X448.Arm.E s.mem base) :=
  WP.mono (VG.Proof.X448.Arm.mul_ok hs (VG.Proof.X448.Arm.slot_bound o) (VG.Proof.X448.Arm.slot_bound a) (VG.Proof.X448.Arm.slot_bound b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.Arm.bounded_update h.mem hb bo, by rw [VG.Proof.X448.Arm.E_update h.mem, e]; rfl⟩

theorem addE {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.BoundedEnv s.mem base) (o a b : VG.Proof.X448.Arm.Index) :
    WP isa (.block (Impl.X448.Arm.add (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      VG.Proof.X448.Arm.Keep base s t ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ VG.Proof.X448.Arm.E t.mem base = VG.Proof.X448.Arm.opAdd o a b (VG.Proof.X448.Arm.E s.mem base) :=
  WP.mono (VG.Proof.X448.Arm.add_ok hs (VG.Proof.X448.Arm.slot_bound o) (VG.Proof.X448.Arm.slot_bound a) (VG.Proof.X448.Arm.slot_bound b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.Arm.bounded_update h.mem hb bo, by rw [VG.Proof.X448.Arm.E_update h.mem, e]; rfl⟩

theorem subE {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.BoundedEnv s.mem base) (o a b : VG.Proof.X448.Arm.Index) :
    WP isa (.block (Impl.X448.Arm.sub (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      VG.Proof.X448.Arm.Keep base s t ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ VG.Proof.X448.Arm.E t.mem base = VG.Proof.X448.Arm.opSub o a b (VG.Proof.X448.Arm.E s.mem base) :=
  WP.mono (VG.Proof.X448.Arm.sub_ok hs (VG.Proof.X448.Arm.slot_bound o) (VG.Proof.X448.Arm.slot_bound a) (VG.Proof.X448.Arm.slot_bound b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.Arm.bounded_update h.mem hb bo, by rw [VG.Proof.X448.Arm.E_update h.mem, e]; rfl⟩

theorem a24E {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.BoundedEnv s.mem base) (o a : VG.Proof.X448.Arm.Index) :
    WP isa (.block (mulSmall (slot o.val) (slot a.val))) s fun t =>
      VG.Proof.X448.Arm.Keep base s t ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ VG.Proof.X448.Arm.E t.mem base = VG.Proof.X448.Arm.opA24 o a (VG.Proof.X448.Arm.E s.mem base) :=
  WP.mono (VG.Proof.X448.Arm.mulSmall_ok hs (VG.Proof.X448.Arm.slot_bound o) (VG.Proof.X448.Arm.slot_bound a) (hb a)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.Arm.bounded_update h.mem hb bo, by rw [VG.Proof.X448.Arm.E_update h.mem, e]; rfl⟩

theorem copyE {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.BoundedEnv s.mem base) (o a : VG.Proof.X448.Arm.Index) :
    WP isa (.block (copy (slot o.val) (slot a.val))) s fun t =>
      VG.Proof.X448.Arm.Keep base s t ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ VG.Proof.X448.Arm.E t.mem base = VG.Proof.X448.Arm.opCopy o a (VG.Proof.X448.Arm.E s.mem base) := by
  have sep : slot o.val = slot a.val ∨ slot o.val + 112 ≤ slot a.val ∨ slot a.val + 112 ≤ slot o.val := by
    by_cases h : o = a
    · subst o; exact Or.inl rfl
    · exact Or.inr (VG.Proof.X448.Arm.slot_sep h)
  refine WP.mono (VG.Proof.X448.Arm.copy_ok hs (Nat.le_trans (VG.Proof.X448.Arm.slot_bound o) (by decide))
    (Nat.le_trans (VG.Proof.X448.Arm.slot_bound a) (by decide)) sep) fun t ⟨tf, tm, tk⟩ => ?_
  have op : VG.Proof.X448.Arm.Op base (slot o.val) s t := ⟨tk, FieldMem.output tm⟩
  refine ⟨op.keep, VG.Proof.X448.Arm.bounded_update op.mem hb (fun i hi => ?_), ?_⟩
  · rw [tf i hi]; exact hb a i hi
  · rw [VG.Proof.X448.Arm.E_update op.mem, show VG.Proof.X448.Arm.F t.mem base (slot o.val) = VG.Proof.X448.Arm.F s.mem base (slot a.val) from
      congrArg toFe (VG.Proof.X448.Radix16.valN_congr tf)]
    rfl

theorem cswapE {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.BoundedEnv s.mem base)
    (x y : VG.Proof.X448.Arm.Index) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .r5 = VG.Proof.X448.Arm.mask sw) :
    WP isa (.block (cswap (slot x.val) (slot y.val))) s fun t =>
      VG.Proof.X448.Arm.Keep base s t ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ t.gpr .r5 = s.gpr .r5 ∧
      VG.Proof.X448.Arm.E t.mem base = VG.Proof.X448.Arm.opSwap x y sw (VG.Proof.X448.Arm.E s.mem base) := by
  refine WP.mono (VG.Proof.X448.Arm.cswap_ok hs (VG.Proof.X448.Arm.slot_bound x) (VG.Proof.X448.Arm.slot_bound y) (VG.Proof.X448.Arm.slot_sep hxy) hm)
    fun t ⟨tx, ty, tm, tk⟩ => ?_
  have other : ∀ i : VG.Proof.X448.Arm.Index, i ≠ x → i ≠ y → ∀ j < 28,
      VG.Proof.X448.Arm.limbs t.mem base (slot i.val) j = VG.Proof.X448.Arm.limbs s.mem base (slot i.val) j := by
    intro i hix hiy j hj
    have ex := VG.Proof.X448.Arm.slot_sep hix
    have ey := VG.Proof.X448.Arm.slot_sep hiy
    have hi := VG.Proof.X448.Arm.slot_bound i
    change (VG.Proof.X448.Arm.word t.mem base (slot i.val + 4 * j)).toNat = _
    rw [tm.word (by omega) (by omega) (by change slot i.val + 112 ≤ 3584 at hi; omega)]
  have fx : VG.Proof.X448.Arm.E t.mem base x = if sw then VG.Proof.X448.Arm.E s.mem base y else VG.Proof.X448.Arm.E s.mem base x := by
    cases sw <;> apply congrArg toFe <;> apply VG.Proof.X448.Radix16.valN_congr <;> exact tx
  have fy : VG.Proof.X448.Arm.E t.mem base y = if sw then VG.Proof.X448.Arm.E s.mem base x else VG.Proof.X448.Arm.E s.mem base y := by
    cases sw <;> apply congrArg toFe <;> apply VG.Proof.X448.Radix16.valN_congr <;> exact ty
  refine ⟨⟨tk.mono ?_, ?_⟩, ?_, tk.1 _ (by decide), ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro p hp _
    have hx := x.isLt
    have hy := y.isLt
    apply tm p <;> simp only [slot] <;> omega
  · intro i j hj
    by_cases hix : i = x
    · subst i; rw [tx j hj]; cases sw <;> exact hb _ j hj
    · by_cases hiy : i = y
      · subst i; rw [ty j hj]; cases sw <;> exact hb _ j hj
      · rw [other i hix hiy j hj]; exact hb i j hj
  · funext i
    by_cases hiy : i = y
    · subst i; rw [VG.Proof.X448.Arm.opSwap, Function.update_self]; exact fy
    · rw [VG.Proof.X448.Arm.opSwap, Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst i; rw [Function.update_self]; exact fx
      · rw [Function.update_of_ne hix]
        exact congrArg toFe (VG.Proof.X448.Radix16.valN_congr (other i hix hiy))

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Ops`. -/
section

/-!
# X448 on ARMv7: sequences of field operations

Slot-indexed operations interpret the implementation's field-operation lists
as environment updates.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

inductive FieldOp
  | mul (o a b : VG.Proof.X448.Arm.Index)
  | add (o a b : VG.Proof.X448.Arm.Index)
  | sub (o a b : VG.Proof.X448.Arm.Index)
  | mulSmall (o a : VG.Proof.X448.Arm.Index)
  | copy (o a : VG.Proof.X448.Arm.Index)
  deriving DecidableEq

def FieldOp.impl : VG.Proof.X448.Arm.FieldOp → Impl.X448.Arm.Op
  | .mul o a b => .mul (slot o.val) (slot a.val) (slot b.val)
  | .add o a b => .add (slot o.val) (slot a.val) (slot b.val)
  | .sub o a b => .sub (slot o.val) (slot a.val) (slot b.val)
  | .mulSmall o a => .mulSmall (slot o.val) (slot a.val)
  | .copy o a => .copy (slot o.val) (slot a.val)

def FieldOp.apply : VG.Proof.X448.Arm.FieldOp → VG.Proof.X448.Arm.Env → VG.Proof.X448.Arm.Env
  | .mul o a b => VG.Proof.X448.Arm.opMul o a b
  | .add o a b => VG.Proof.X448.Arm.opAdd o a b
  | .sub o a b => VG.Proof.X448.Arm.opSub o a b
  | .mulSmall o a => VG.Proof.X448.Arm.opA24 o a
  | .copy o a => VG.Proof.X448.Arm.opCopy o a

def applyOps : List VG.Proof.X448.Arm.FieldOp → VG.Proof.X448.Arm.Env → VG.Proof.X448.Arm.Env
  | [], e => e
  | op :: rest, e => VG.Proof.X448.Arm.applyOps rest (op.apply e)

theorem fieldOp_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.BoundedEnv s.mem base) (op : VG.Proof.X448.Arm.FieldOp) :
    WP isa op.impl.code s fun t =>
      VG.Proof.X448.Arm.Keep base s t ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ VG.Proof.X448.Arm.E t.mem base = op.apply (VG.Proof.X448.Arm.E s.mem base) := by
  cases op with
  | mul o a b => exact VG.Proof.X448.Arm.mulE hs hb o a b
  | add o a b => exact VG.Proof.X448.Arm.addE hs hb o a b
  | sub o a b => exact VG.Proof.X448.Arm.subE hs hb o a b
  | mulSmall o a => exact VG.Proof.X448.Arm.a24E hs hb o a
  | copy o a => exact VG.Proof.X448.Arm.copyE hs hb o a

theorem ops_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.BoundedEnv s.mem base) (xs : List VG.Proof.X448.Arm.FieldOp) :
    WP isa (ops (xs.map FieldOp.impl)) s fun t =>
      VG.Proof.X448.Arm.Keep base s t ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ VG.Proof.X448.Arm.E t.mem base = VG.Proof.X448.Arm.applyOps xs (VG.Proof.X448.Arm.E s.mem base) := by
  induction xs generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hb, rfl⟩
  | cons op rest ih =>
    change WP isa (.seq op.impl.code (ops (rest.map FieldOp.impl))) s _
    rw [WP.seq_iff]
    refine WP.mono (VG.Proof.X448.Arm.fieldOp_ok hs hb op) fun t ⟨tk, tb, te⟩ => ?_
    refine WP.mono (ih (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, ?_⟩
    rw [ue, te]
    rfl

/-- The arithmetic part of one Montgomery-ladder step. -/
def stepFields : List VG.Proof.X448.Arm.FieldOp :=
  [.add 5 1 2, .mul 9 5 5, .sub 6 1 2, .mul 10 6 6, .sub 11 9 10,
    .add 7 3 4, .sub 8 3 4, .mul 12 8 5, .mul 13 7 6,
    .add 3 12 13, .mul 3 3 3, .sub 4 12 13, .mul 4 4 4, .mul 4 0 4,
    .mul 1 9 10, .mulSmall 2 11, .add 2 9 2, .mul 2 11 2]

theorem stepFields_impl : stepFields.map FieldOp.impl = stepOps := by decide +kernel

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.BitStep`. -/
section

/-!
# X448 on ARMv7: reading a scalar bit

Only the public loop counter selects an address; the bit affects an XOR mask.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

def stepPre : List Instr :=
  [.dp .sub .r11 .r11 (.imm 1), .dp .add .r7 .r0 (.reg .r11), .ldrb .r3 .r7 BITS,
    ld .r2 SWAP, .dp .eor .r2 .r2 (.reg .r3), st .r3 SWAP,
    .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r2)]

theorem mask_xor : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 32) - (BitVec.ofNat 32 a ^^^ (BitVec.ofNat 8 b).setWidth 32) =
      VG.Proof.X448.Arm.mask (decide (a ^^^ b = 1)) := by decide

theorem stepPre_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {t : Nat} (ht : t < 448)
    (hb : s.gpr .r11 = BitVec.ofNat 32 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (VG.Proof.X448.Arm.off base (BITS + t)) = BitVec.ofNat 8 kt)
    (hswap : VG.Proof.X448.Arm.word s.mem base SWAP = BitVec.ofNat 32 sw0) :
    WP isa (.block VG.Proof.X448.Arm.stepPre) s fun s' =>
      s'.gpr .r11 = BitVec.ofNat 32 t ∧ s'.gpr .r5 = VG.Proof.X448.Arm.mask (decide (sw0 ^^^ kt = 1)) ∧
      (∀ r, r ∉ [.r11, .r3, .r2, .r5, .r7] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (VG.Proof.X448.Arm.off base SWAP) (BitVec.ofNat 32 kt) := by
  have hb' : s.gpr .r11 - (1 : BitVec 32) = BitVec.ofNat 32 t := by
    change s.gpr .r11 - BitVec.ofNat 32 1 = _
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hin := hs.read (d := BITS + t) (n := 1) (by simp only [BITS]; omega)
  have hr := hs.read (d := SWAP) (n := 4) (by decide)
  have hw := hs.write (d := SWAP) (n := 4) (by decide)
  have ba : State.addr (s.gpr .r0 + BitVec.ofNat 32 t + BitVec.ofNat 32 BITS) = VG.Proof.X448.Arm.off base (BITS + t) := by
    rw [Offset.add_add, Nat.add_comm t BITS]
    exact hs.ea (by simp only [BITS]; omega)
  have sa := hs.ea (d := SWAP) (by decide)
  have se : SWAP < 4096 := by decide
  have be : BITS < 4096 := by decide
  have enc0 : encodable (0 : BitVec 32) = true := by decide
  have enc1 : encodable (1 : BitVec 32) = true := by decide
  apply WP.of_runBlock
  simp only [VG.Proof.X448.Arm.stepPre, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval,
    enc0, enc1, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    hb', ba, sa, se, be, State.load8, State.load32, State.store32, hin, hr, hw, hbit,
    hswap, Option.map_some, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  have ek : (BitVec.ofNat 8 kt).setWidth 32 = BitVec.ofNat 32 kt := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  refine ⟨trivial, VG.Proof.X448.Arm.mask_xor sw0 hsw kt hk, fun r hr => ?_, trivial, trivial, by rw [ek]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Counters`. -/
section

/-!
# X448 on ARMv7: public loop counters

Counters preserve memory and every other register; the zero flag controls loop
termination.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm
open VG.Proof.X25519.Arm (wp_movw wp_subs op2_imm ofNat_beq_zero)

theorem setCounter_ok (s : State) (k : Nat) (hk : k < 2 ^ 16) :
    WP isa (.block [.movw .r11 (BitVec.ofNat 16 k)]) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 k ∧ (∀ r, r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  refine wp_movw fun t ht => WP.block_nil ⟨?_, ht.other, ht.mem, ht.rd, ht.wr⟩
  rw [ht.gpr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk]

theorem decCounter_ok {s : State} {k : Nat} (hk : k < 2 ^ 16)
    (hb : s.gpr .r11 = BitVec.ofNat 32 (k + 1)) :
    WP isa (.block [.subs .r11 .r11 (.imm 1)]) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 k ∧ (∀ r, r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.z = decide (k = 0) := by
  have he : s.gpr .r11 - (1 : BitVec 32) = BitVec.ofNat 32 k := by
    change s.gpr .r11 - BitVec.ofNat 32 1 = _
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  refine wp_subs (op2_imm (by decide)) fun t ht hz => WP.block_nil
    ⟨ht.gpr.trans he, ht.other, ht.mem, ht.rd, ht.wr, ?_⟩
  rw [hz, he, ofNat_beq_zero (by omega)]

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Iter`. -/
section

/-!
# X448 on ARMv7: the Montgomery ladder

Each iteration consumes one scalar bit and updates the five field slots
according to `ladderStep`.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

def stepEnv (sw : Bool) (e : VG.Proof.X448.Arm.Env) : VG.Proof.X448.Arm.Env :=
  VG.Proof.X448.Arm.applyOps VG.Proof.X448.Arm.stepFields (VG.Proof.X448.Arm.opSwap 2 4 sw (VG.Proof.X448.Arm.opSwap 1 3 sw e))

theorem cswap_fst (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).1 = if decide (sw = 1) = true then b else a := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

theorem cswap_snd (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).2 = if decide (sw = 1) = true then a else b := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

theorem stepEnv_eval (e : VG.Proof.X448.Arm.Env) (st : Spec.X448.Ladder) (k : Nat) (u : Spec.X448.Fe) (t : Nat)
    (h0 : e 0 = u) (h1 : e 1 = st.x2) (h2 : e 2 = st.z2) (h3 : e 3 = st.x3) (h4 : e 4 = st.z3) :
    VG.Proof.X448.Arm.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 0 = u ∧
    VG.Proof.X448.Arm.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 1 = (Spec.X448.ladderStep k u st t).x2 ∧
    VG.Proof.X448.Arm.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 2 = (Spec.X448.ladderStep k u st t).z2 ∧
    VG.Proof.X448.Arm.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 3 = (Spec.X448.ladderStep k u st t).x3 ∧
    VG.Proof.X448.Arm.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 4 = (Spec.X448.ladderStep k u st t).z3 := by
  rw [VG.Proof.X448.ladderStep_eq]
  simp only [↓reduceIte, VG.Proof.X448.Arm.stepEnv, VG.Proof.X448.Arm.applyOps, VG.Proof.X448.Arm.stepFields, FieldOp.apply,
    VG.Proof.X448.Arm.opMul, VG.Proof.X448.Arm.opAdd, VG.Proof.X448.Arm.opSub, VG.Proof.X448.Arm.opA24, VG.Proof.X448.Arm.opSwap, Function.update_apply,
    VG.Proof.X448.Arm.cswap_fst, VG.Proof.X448.Arm.cswap_snd, h0, h1, h2, h3, h4]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem swaps_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.BoundedEnv s.mem base)
    {sw : Bool} (hm : s.gpr .r5 = VG.Proof.X448.Arm.mask sw) :
    WP isa (.block (cswap X2 X3 ++ cswap Z2 Z3)) s fun t =>
      VG.Proof.X448.Arm.Keep base s t ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ VG.Proof.X448.Arm.E t.mem base = VG.Proof.X448.Arm.opSwap 2 4 sw (VG.Proof.X448.Arm.opSwap 1 3 sw (VG.Proof.X448.Arm.E s.mem base)) := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.cswapE hs hb 1 3 (by decide) hm) fun t ⟨tk, tb, tc, te⟩ => ?_
  refine WP.mono (VG.Proof.X448.Arm.cswapE (tk.scr hs) tb 2 4 (by decide) (tc.trans hm)) fun u ⟨uk, ub, _, ue⟩ =>
    ⟨tk.trans uk, ub, by rw [ue, te]⟩

theorem counter_zero {s : State} {n : Nat} (hn : n < 2 ^ 32)
    (hc : s.gpr .r11 = BitVec.ofNat 32 n) : (s.gpr .r11 == 0) = decide (n = 0) := by
  rw [hc]
  rcases Nat.eq_zero_or_pos n with rfl | h
  · rfl
  · rw [decide_eq_false (by omega)]
    apply beq_false_of_ne
    intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    exact absurd this (by simp; omega)

/-- The complete loop invariant, including its memory frame. -/
structure LInv (base : Addr) (k : Nat) (u : Spec.X448.Fe) (s₀ s : State) (n : Nat) : Prop where
  scr : VG.Proof.X448.Arm.Scr s base
  bounded : VG.Proof.X448.Arm.BoundedEnv s.mem base
  regs : VG.Proof.X448.Arm.Keeps (.r11 :: VG.Proof.X448.Arm.workRegs) s₀ s
  r11 : s.gpr .r11 = BitVec.ofNat 32 n
  mem : VG.Proof.X448.Arm.Outside2 base 32 2848 ACC 512 s₀.mem s.mem
  x1 : VG.Proof.X448.Arm.E s.mem base 0 = u
  x2 : VG.Proof.X448.Arm.E s.mem base 1 = (VG.Proof.X448.ladderAfter k u n).x2
  z2 : VG.Proof.X448.Arm.E s.mem base 2 = (VG.Proof.X448.ladderAfter k u n).z2
  x3 : VG.Proof.X448.Arm.E s.mem base 3 = (VG.Proof.X448.ladderAfter k u n).x3
  z3 : VG.Proof.X448.Arm.E s.mem base 4 = (VG.Proof.X448.ladderAfter k u n).z3
  swap : VG.Proof.X448.Arm.word s.mem base SWAP = BitVec.ofNat 32 (VG.Proof.X448.ladderAfter k u n).swap

theorem ofs_off' (base : Addr) {d : Nat} (h : d < 2 ^ 64) : VG.Proof.X448.Arm.ofs base (VG.Proof.X448.Arm.off base d) = d :=
  Mem.sub_ofNat_toNat base h

theorem stepBody_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe} {n : Nat} (hn : n < 448)
    (hbits : ∀ t < 448, s₀.mem (VG.Proof.X448.Arm.off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : VG.Proof.X448.Arm.LInv base k u s₀ s (n + 1)) :
    WP isa stepBody s fun t => VG.Proof.X448.Arm.LInv base k u s₀ t n ∧ (t.gpr .r11 == 0) = decide (n = 0) := by
  have hs := hi.scr
  have bitval : s.mem (VG.Proof.X448.Arm.off base (BITS + n)) = BitVec.ofNat 8 (VG.Proof.X448.bit k n) := by
    rw [hi.mem _ (by rw [VG.Proof.X448.Arm.ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
      (by rw [VG.Proof.X448.Arm.ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)]
    exact hbits n hn
  rw [stepBody, WP.seq_iff,
    show stepHead = VG.Proof.X448.Arm.stepPre ++ (cswap X2 X3 ++ cswap Z2 Z3) by
      simp only [stepHead, VG.Proof.X448.Arm.stepPre, List.append_assoc], WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.stepPre_ok hs hn hi.r11 (by have := VG.Proof.X448.bit_le k n; omega)
    (by have := VG.Proof.X448.ladderAfter_swap_le k u (n := n + 1) (by omega); omega) bitval hi.swap)
    fun s₁ ⟨b₁, c₁, g₁, rd₁, wr₁, m₁⟩ => ?_
  have hs₁ : VG.Proof.X448.Arm.Scr s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.r0, (g₁ _ (by decide)).trans hs.mask,
    wr₁ ▸ hs.wr, by rw [g₁ _ (by decide)]; exact hs.nowrap⟩
  have out₁ : VG.Proof.X448.Arm.Outside base SWAP 4 s.mem s₁.mem := by
    rw [m₁]; exact VG.Proof.X448.Arm.writeW_outside _ _ _ (by decide)
  have l₁ : ∀ i : VG.Proof.X448.Arm.Index, ∀ j < 28, VG.Proof.X448.Arm.limbs s₁.mem base (slot i.val) j = VG.Proof.X448.Arm.limbs s.mem base (slot i.val) j := by
    intro i j hj
    exact out₁.limbs (Or.inr (by simp only [slot, SWAP]; omega))
      (Nat.le_trans (VG.Proof.X448.Arm.slot_bound i) (by decide)) hj
  have e₁ : VG.Proof.X448.Arm.E s₁.mem base = VG.Proof.X448.Arm.E s.mem base := by
    funext i; exact congrArg toFe (VG.Proof.X448.Radix16.valN_congr (l₁ i))
  have bb₁ : VG.Proof.X448.Arm.BoundedEnv s₁.mem base := by
    intro i j hj; rw [l₁ i j hj]; exact hi.bounded i j hj
  refine WP.mono (VG.Proof.X448.Arm.swaps_ok hs₁ bb₁ c₁) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_
  rw [← VG.Proof.X448.Arm.stepFields_impl]
  refine WP.mono (VG.Proof.X448.Arm.ops_ok (k₂.scr hs₁) bb₂ VG.Proof.X448.Arm.stepFields) fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_
  have core := k₂.trans k₃
  have b₃ : s₃.gpr .r11 = BitVec.ofNat 32 n := (core.regs.1 _ (by decide)).trans b₁
  have vals := VG.Proof.X448.Arm.stepEnv_eval (VG.Proof.X448.Arm.E s.mem base) (VG.Proof.X448.ladderAfter k u (n + 1)) k u n
    hi.x1 hi.x2 hi.z2 hi.x3 hi.z3
  have e₄ : VG.Proof.X448.Arm.E s₃.mem base = VG.Proof.X448.Arm.stepEnv (decide ((VG.Proof.X448.ladderAfter k u (n + 1)).swap ^^^ VG.Proof.X448.bit k n = 1))
      (VG.Proof.X448.Arm.E s.mem base) := by rw [e₃, e₂, e₁]; rfl
  rw [← VG.Proof.X448.ladderAfter_step k u hn, ← e₄] at vals
  refine ⟨⟨core.scr hs₁, bb₃, ?_, b₃, ?_, vals.1, vals.2.1, vals.2.2.1,
    vals.2.2.2.1, vals.2.2.2.2, ?_⟩, VG.Proof.X448.Arm.counter_zero (by omega) b₃⟩
  · refine hi.regs.trans ⟨?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    intro r hr
    have hwork : r ∉ VG.Proof.X448.Arm.workRegs := fun h => hr (List.mem_cons_of_mem _ h)
    have hpre : r ∉ [Reg.r11, .r3, .r2, .r5, .r7] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr (by subst r; decide), fun h => hr (by subst r; decide),
        fun h => hr (by subst r; decide), fun h => hr (by subst r; decide),
        fun h => hr (by subst r; decide)⟩
    rw [core.regs.1 r hwork, g₁ r hpre]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [core.mem p (by omega) hq, out₁ p (by simp only [SWAP]; omega)]
  · rw [core.mem.word (by simp only [SWAP]; omega) (by simp only [SWAP, ACC]; omega) (by decide),
      m₁, VG.Proof.X448.ladderAfter_step k u hn]
    exact Mem.readW_writeW_self32 _ _ _

/-- Comparing the public counter changes only flags. -/
theorem LInv.of_flags {base : Addr} {k n : Nat} {u : Spec.X448.Fe} {s0 s t : State}
    (h : VG.Proof.X448.Arm.LInv base k u s0 s n) (ht : VG.Proof.X25519.Arm.Fupd s t) : VG.Proof.X448.Arm.LInv base k u s0 t n := by
  refine ⟨?_, ht.mem ▸ h.bounded, ?_, ?_, ht.mem ▸ h.mem,
    ht.mem ▸ h.x1, ht.mem ▸ h.x2, ht.mem ▸ h.z2, ht.mem ▸ h.x3, ht.mem ▸ h.z3, ht.mem ▸ h.swap⟩
  · exact ⟨by rw [ht.gpr]; exact h.scr.r0, by rw [ht.gpr]; exact h.scr.mask,
      ht.wr ▸ h.scr.wr, by rw [ht.gpr]; exact h.scr.nowrap⟩
  · exact ⟨fun r hr => by rw [ht.gpr]; exact h.regs.1 r hr,
      ht.rd.trans h.regs.2.1, ht.wr.trans h.regs.2.2⟩
  · rw [ht.gpr]; exact h.r11

theorem step_ok {s0 s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe} {n : Nat} (hn : n < 448)
    (hbits : ∀ t < 448, s0.mem (VG.Proof.X448.Arm.off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : VG.Proof.X448.Arm.LInv base k u s0 s (n + 1)) :
    WP isa VG.Impl.X448.Arm.step s fun t => VG.Proof.X448.Arm.LInv base k u s0 t n ∧ t.z = decide (n = 0) := by
  rw [VG.Impl.X448.Arm.step, WP.seq_iff]
  refine WP.mono (VG.Proof.X448.Arm.stepBody_ok hn hbits hi) fun t ⟨ht, hz⟩ => ?_
  refine VG.Proof.X25519.Arm.wp_cmp (VG.Proof.X25519.Arm.op2_imm (by decide))
    fun u hu he => WP.block_nil ⟨ht.of_flags hu, ?_⟩
  rw [he]
  change (t.gpr .r11 - BitVec.ofNat 32 0 == 0) = _
  rw [BitVec.sub_zero]
  exact hz

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.BitWrite`. -/
section

/-!
# X448 on ARMv7: expanding scalar bytes

Each byte is expanded into eight bytes holding its bits, through public
offsets in the working space.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

theorem sub_toNat_lt_one (x a : Addr) : (x - a).toNat < 1 ↔ x = a := by
  constructor
  · intro h
    have h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : Addr).toNat = 0 from rfl]; omega)
    calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
      _ = a := by rw [h0]; exact BitVec.zero_add a
  · rintro rfl; simp

theorem writeW8_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    (m.writeW a v) x = if x = a then v else m x := by
  by_cases h : x = a
  · subst h; simp [Mem.writeW, Mem.write]
  · simp only [Mem.writeW, Mem.write, Nat.reduceDiv, VG.Proof.X448.Arm.sub_toNat_lt_one, h, ite_false]

theorem off_eq_iff (base : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) :
    VG.Proof.X448.Arm.off base d = VG.Proof.X448.Arm.off base e ↔ d = e := by
  constructor
  · intro h
    have := congrArg (fun x => VG.Proof.X448.Arm.ofs base x) h
    simp only [VG.Proof.X448.Arm.ofs_off' base hd, VG.Proof.X448.Arm.ofs_off' base he] at this
    exact this
  · intro h; rw [h]

theorem writeW8_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (hd : d < 2 ^ 64) {x : Addr}
    (hx : VG.Proof.X448.Arm.ofs base x ≠ d) : (m.writeW (VG.Proof.X448.Arm.off base d) v) x = m x := by
  rw [VG.Proof.X448.Arm.writeW8_apply, ite_eq_right_iff.mpr]
  intro h; subst h; exact absurd (VG.Proof.X448.Arm.ofs_off' base hd) hx

theorem write1_eq (m : Mem) (p : Addr) (v : BitVec 8) : m.write p 1 v = m.writeW p v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    ((b.setWidth 32 >>> j) &&& (1 : BitVec 32)).setWidth 8 =
      BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by decide +kernel

def bitJ (j : Nat) : List Instr :=
  [.mov .r2 (if j = 0 then .reg .r3 else .shifted .r3 .lsr j),
    .dp .and .r2 .r2 (.imm 1), .strb .r2 .r7 (BITS + j)]

theorem bitShift_eval (s : State) {j : Nat} (hj : j < 8) :
    Op2.eval s (if j = 0 then .reg .r3 else .shifted .r3 .lsr j) = some (s.gpr .r3 >>> j) := by
  by_cases hz : j = 0
  · subst j; simp only [ite_true, Op2.eval, BitVec.ushiftRight_zero]
  · rw [ite_eq_right hz]
    exact VG.Proof.X25519.Arm.op2_lsr (by omega)

theorem bitJ_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {i : Nat} (hi : i < 56)
    (hp : s.gpr .r7 = s.gpr .r0 + BitVec.ofNat 32 (8 * i))
    {b : BitVec 8} (ha : s.gpr .r3 = b.setWidth 32) {j : Nat} (hj : j < 8) :
    WP isa (.block (VG.Proof.X448.Arm.bitJ j)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.Arm.off base (BITS + (8 * i + j)))
        (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧ VG.Proof.X448.Arm.Keeps [.r2] s t := by
  unfold VG.Proof.X448.Arm.bitJ
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X448.Arm.bitShift_eval s hj) fun t ht => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  have ea : State.addr (u.gpr .r7 + BitVec.ofNat 32 (BITS + j)) = VG.Proof.X448.Arm.off base (BITS + (8 * i + j)) := by
    rw [hu.other .r7 (by decide), ht.other .r7 (by decide), hp,
      BitVec.add_assoc, ← BitVec.ofNat_add, hs.ea (by simp only [BITS]; omega)]
    congr 1; omega
  have wr := hs.write (d := BITS + (8 * i + j)) (n := 1) (by simp only [BITS]; omega)
  refine VG.Proof.X25519.Arm.wp_strb (by simp only [BITS]; omega) ea
    (by rw [hu.wr, ht.wr]; exact wr) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr]
    change s.mem.writeW _ ((t.gpr .r2 &&& (1 : BitVec 32)).setWidth 8) = _
    rw [ht.gpr, ha, VG.Proof.X448.Arm.bit_byte b j hj]
  · exact VG.Proof.X448.Arm.rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _)))

/-- Expanding eight bits preserves each byte already written. -/
theorem byteBits_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {i : Nat} (hi : i < 56)
    (hp : s.gpr .r7 = s.gpr .r0 + BitVec.ofNat 32 (8 * i))
    {b : BitVec 8} (ha : s.gpr .r3 = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap VG.Proof.X448.Arm.bitJ)) s fun t =>
      (∀ j < 8, t.mem (VG.Proof.X448.Arm.off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      VG.Proof.X448.Arm.Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r2] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (VG.Proof.X448.Arm.off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    VG.Proof.X448.Arm.Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r2] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (VG.Proof.X448.Arm.bitJ n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.X448.Arm.bitJ_ok (hs.of_keeps tk (by decide)) hi
      (by rw [tk.1 .r7 (by decide), tk.1 .r0 (by decide)]; exact hp)
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, VG.Proof.X448.Arm.writeW8_apply]
      have eq : VG.Proof.X448.Arm.off base (BITS + (8 * i + j)) = VG.Proof.X448.Arm.off base (BITS + (8 * i + n)) ↔ j = n := by
        rw [VG.Proof.X448.Arm.off_eq_iff base (by simp only [BITS]; omega) (by simp only [BITS]; omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact VG.Proof.X448.Arm.writeW8_outside _ _ _ (by simp only [BITS]; omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.BitBody`. -/
section

/-!
# X448 on ARMv7: one scalar byte

The public byte counter selects a scalar byte, expands it, and advances the
loop.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm
open VG.Proof.X25519.Arm (wp_dp wp_ldrb wp_cmp op2_reg op2_lsl op2_imm)

def bitHead : List Instr :=
  [.dp .add .r7 .r1 (.reg .r11), .ldrb .r3 .r7 0,
    .dp .add .r7 .r0 (.shifted .r11 .lsl 3)]

def bitTail : List Instr := [.dp .add .r11 .r11 (.imm 1), .cmp .r11 (.imm 56)]

def bitRegs : List Reg := [.r3, .r2, .r11, .r7]

theorem bitHead_ok {s : State} {base k : Addr} (_hs : VG.Proof.X448.Arm.Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 56 ≤ 2 ^ 32) {i : Nat} (hi : i < 56)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hkr : InRegions (s.rd ++ s.wr) (VG.Proof.X448.Arm.off k i) 1) :
    WP isa (.block VG.Proof.X448.Arm.bitHead) s fun t =>
      t.gpr .r3 = (s.mem (VG.Proof.X448.Arm.off k i)).setWidth 32 ∧
      t.gpr .r7 = t.gpr .r0 + BitVec.ofNat 32 (8 * i) ∧
      t.mem = s.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r7] s t := by
  unfold VG.Proof.X448.Arm.bitHead
  refine wp_dp (op2_reg _ _) fun t ht => ?_
  have ea : State.addr (t.gpr .r7 + BitVec.ofNat 32 0) = VG.Proof.X448.Arm.off k i := by
    rw [ht.gpr]; change State.addr (s.gpr .r1 + s.gpr .r11 + BitVec.ofNat 32 0) = _
    rw [BitVec.add_zero, hb, addr_add (by omega), hk]
  refine wp_ldrb (by decide) ea (by rw [ht.rd, ht.wr]; exact hkr) fun u hu => ?_
  refine wp_dp (op2_lsl (by decide)) fun v hv => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hv.other .r3 (by decide), hu.gpr, ht.mem]
  · rw [hv.gpr, hv.other .r0 (by decide)]
    change u.gpr .r0 + u.gpr .r11 <<< 3 = _
    rw [hu.other .r11 (by decide), ht.other .r11 (by decide), hb]
    apply congrArg (u.gpr .r0 + ·)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  · exact hv.mem.trans (hu.mem.trans ht.mem)
  · exact VG.Proof.X448.Arm.rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest (by decide))))

theorem bitTail_ok {s : State} {i : Nat} (hi : i < 56) (hb : s.gpr .r11 = BitVec.ofNat 32 i) :
    WP isa (.block VG.Proof.X448.Arm.bitTail) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 56) ∧
      t.mem = s.mem ∧ VG.Proof.X448.Arm.Keeps [.r11] s t := by
  have check : ∀ n < 56,
      ((BitVec.ofNat 32 n + (1 : BitVec 32) - (56 : BitVec 32)) == 0) = decide (n + 1 = 56) :=
    by decide +kernel
  unfold VG.Proof.X448.Arm.bitTail
  refine wp_dp (op2_imm (by decide)) fun t ht => ?_
  refine wp_cmp (op2_imm (by decide)) fun u hu hz => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hu.gpr, ht.gpr]; change s.gpr .r11 + BitVec.ofNat 32 1 = _
    rw [hb, ← BitVec.ofNat_add]
  · rw [hz, ht.gpr]; change ((s.gpr .r11 + 1 - 56) == 0) = _
    rw [hb]; exact check i hi
  · exact hu.mem.trans ht.mem
  · exact VG.Proof.X448.Arm.rest_keeps ((ht.rest (by decide)).trans (hu.rest _))

theorem bitsBody_ok {s : State} {base k : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 56 ≤ 2 ^ 32) {i : Nat} (hi : i < 56)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hkr : InRegions (s.rd ++ s.wr) (VG.Proof.X448.Arm.off k i) 1) :
    WP isa (.block bitsBody) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 56) ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.bitRegs s t ∧
      (∀ j < 8, t.mem (VG.Proof.X448.Arm.off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (VG.Proof.X448.Arm.off k i)).toNat >>> j) &&& 1)) ∧
      VG.Proof.X448.Arm.Outside base (BITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (VG.Proof.X448.Arm.bitHead ++ (List.range 8).flatMap VG.Proof.X448.Arm.bitJ ++ VG.Proof.X448.Arm.bitTail)) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.bitHead_ok hs hk hfit hi hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.byteBits_ok (hs.of_keeps tk (by decide)) hi tp ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .r11 = BitVec.ofNat 32 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (VG.Proof.X448.Arm.bitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, ?_, ?_, ?_⟩
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Clamp`. -/
section

/-!
# X448 on ARMv7: clamping the scalar bits

Clear bits zero and one, and set bit 447, as RFC 7748 requires.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

def clamp : List Instr :=
  [.mov .r3 (.imm 0), .strb .r3 .r0 BITS, .strb .r3 .r0 (BITS + 1),
    .mov .r3 (.imm 1), .strb .r3 .r0 (BITS + 447)]

def clampMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (VG.Proof.X448.Arm.off base BITS) (0 : BitVec 8)).writeW (VG.Proof.X448.Arm.off base (BITS + 1))
    (0 : BitVec 8)).writeW (VG.Proof.X448.Arm.off base (BITS + 447)) (1 : BitVec 8)

theorem storeByte_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {d : Nat} (hd : d < 4096) :
    WP isa (.block [.strb .r3 .r0 d]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.Arm.off base d) ((s.gpr .r3).setWidth 8) ∧ VG.Proof.X448.Arm.Keeps [] s t := by
  refine VG.Proof.X25519.Arm.wp_strb hd (hs.ea (by omega)) (hs.write (by omega))
    fun t ht => WP.block_nil ⟨ht.mem, VG.Proof.X448.Arm.rest_keeps (ht.rest _)⟩

theorem putByte_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {d : Nat} (hd : d < 4096)
    (v : BitVec 32) (hv : encodable v = true) :
    WP isa (.block [.mov .r3 (.imm v), .strb .r3 .r0 d]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.Arm.off base d) (v.setWidth 8) ∧
      t.gpr .r3 = v ∧ VG.Proof.X448.Arm.Keeps [.r3] s t := by
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm hv) fun t ht => ?_
  refine WP.mono (VG.Proof.X448.Arm.storeByte_ok (hs.of_upd ht (by decide) (by decide)) hd) fun u ⟨um, uk⟩ => ?_
  exact ⟨by rw [um, ht.mem, ht.gpr], (uk.1 _ (by decide)).trans ht.gpr,
    (VG.Proof.X448.Arm.rest_keeps (ht.rest (by decide))).trans (uk.mono (by simp))⟩

theorem clamp_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) :
    WP isa (.block VG.Proof.X448.Arm.clamp) s fun t => t.mem = VG.Proof.X448.Arm.clampMem s.mem base ∧ VG.Proof.X448.Arm.Keeps [.r3] s t := by
  change WP isa (.block (([.mov .r3 (.imm 0), .strb .r3 .r0 BITS] : List Instr) ++
    ([.strb .r3 .r0 (BITS + 1)] : List Instr) ++
    [.mov .r3 (.imm 1), .strb .r3 .r0 (BITS + 447)])) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.putByte_ok hs (by decide : BITS < 4096) 0 (by decide)) fun t ⟨tm, tv, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.storeByte_ok (hs.of_keeps tk (by decide)) (by decide : BITS + 1 < 4096))
    fun u ⟨um, uk⟩ => ?_
  refine WP.mono (VG.Proof.X448.Arm.putByte_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
    (by decide : BITS + 447 < 4096) 1 (by decide)) fun v ⟨vm, _, vk⟩ => ?_
  refine ⟨?_, tk.trans ((uk.mono (by simp)).trans vk)⟩
  rw [vm, um, tv, tm]
  rfl

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Bits`. -/
section

/-!
# X448 on ARMv7: the scalar's decoded bits

The loop expands all 56 bytes before applying the RFC 7748 scalar clamp.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448

/-- `bits`' loop invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : VG.Proof.X448.Arm.Scr s base
  r1 : State.addr (s.gpr .r1) = k
  fit : (s.gpr .r1).toNat + 56 ≤ 2 ^ 32
  r11 : s.gpr .r11 = BitVec.ofNat 32 i
  gpr : ∀ r, r ∉ VG.Proof.X448.Arm.bitRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : VG.Proof.X448.Arm.Outside base BITS 448 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (VG.Proof.X448.Arm.off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 56, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ VG.Proof.X448.Arm.ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 56 → VG.Proof.X448.Arm.BInv base k s₀ s i →
      WP isa (.loop (.block bitsBody) .ne) s fun s' => VG.Proof.X448.Arm.BInv base k s₀ s' 56 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block bitsBody) (c := .ne)
    (Q := fun s' => VG.Proof.X448.Arm.BInv base k s₀ s' 56)
    (fun m (s : State) => ∃ i, m = 56 - i ∧ i < 56 ∧ VG.Proof.X448.Arm.BInv base k s₀ s i) ?_ (56 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (VG.Proof.X448.Arm.bitsBody_ok hb.scr hb.r1 hb.fit hi hb.r11 (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : VG.Proof.X448.Arm.BInv base k s₀ s' (i + 1) := by
    refine ⟨hb.scr.of_keeps ⟨g', rd', wr'⟩ (by decide),
      (by rw [g' _ (by decide)]; exact hb.r1),
      (by rw [g' _ (by decide)]; exact hb.fit), b', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [VG.Proof.X448.Arm.ofs_off' base (by simp only [BITS]; omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, z']
  rcases Nat.lt_or_ge (i + 1) 56 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 56), Bool.not_false],
      56 - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · obtain rfl : i = 55 := by omega
    exact .inl ⟨rfl, inv⟩

theorem getD_bytesAt (m : Mem) (k : Addr) {q : Nat} (hq : q < 56) :
    (Spec.X448.bytesAt m k 56).getD q 0 = m (k + BitVec.ofNat 64 q) := by
  simp only [Spec.X448.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq, Option.map_some, Option.getD_some]

/-- `bits`: byte `t` of `BITS` is bit `t` of the decoded scalar, for `t < 448`. -/
theorem bits_ok {s : State} {base k : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hk : State.addr (s.gpr .r1) = k)
    (hfit : (s.gpr .r1).toNat + 56 ≤ 2 ^ 32)
    (hkr : ∀ q < 56, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ VG.Proof.X448.Arm.ofs base (k + BitVec.ofNat 64 q)) :
    WP isa VG.Impl.X448.Arm.bits s fun s' =>
      (∀ r, r ∉ VG.Proof.X448.Arm.bitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X448.Arm.Outside base BITS 448 s.mem s'.mem ∧
      ∀ t < 448, s'.mem (VG.Proof.X448.Arm.off base (BITS + t)) =
        BitVec.ofNat 8 (VG.Proof.X448.bit (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem k 56)) t) := by
  rw [VG.Impl.X448.Arm.bits]
  refine WP.seq (WP.mono (show WP isa (.block [.mov .r11 (.imm 0)]) s
      (fun s' => VG.Proof.X448.Arm.BInv base k s s' 0) by
    refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide))
      fun t ht => WP.block_nil ?_
    have keep : VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.bitRegs s t := VG.Proof.X448.Arm.rest_keeps (ht.rest (by decide))
    exact ⟨hs.of_keeps keep (by decide), by rw [ht.other .r1 (by decide)]; exact hk,
      by rw [ht.other .r1 (by decide)]; exact hfit, ht.gpr, keep.1, keep.2.1, keep.2.2,
      ht.mem ▸ Outside.refl _ _ _ _, fun _ hi => by omega⟩) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.bitsLoop_ok hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_)
  refine WP.mono (VG.Proof.X448.Arm.clamp_ok h₂.scr) fun s₃ ⟨m₃, k₃⟩ => ?_
  refine ⟨fun r hr => ?_, k₃.2.1.trans h₂.rd, k₃.2.2.trans h₂.wr, fun x hx => ?_, fun t ht => ?_⟩
  · rw [k₃.1 r (by intro he; simp only [List.mem_singleton] at he; subst r; exact hr (by decide))]
    exact h₂.gpr r hr
  · rw [m₃, VG.Proof.X448.Arm.clampMem]
    have o : ∀ d, BITS ≤ d → d < BITS + 448 → VG.Proof.X448.Arm.ofs base x ≠ d := fun d h₁ h₂ h => by omega
    rw [VG.Proof.X448.Arm.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 447) (by omega) (by omega)),
      VG.Proof.X448.Arm.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 1) (by omega) (by omega)),
      VG.Proof.X448.Arm.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o BITS (by omega) (by omega))]
    exact h₂.mem x hx
  · rw [m₃, VG.Proof.X448.Arm.clampMem, scalar_bit (length_bytesAt _ _ _) ht]
    simp (disch := simp only [BITS]; omega) only [VG.Proof.X448.Arm.writeW8_apply, VG.Proof.X448.Arm.off_eq_iff, Nat.add_left_cancel_iff,
      Nat.add_eq_left]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 447 ∨ (2 ≤ t ∧ t < 447)) with
      rfl | rfl | rfl | ⟨h₃, h₄⟩
    · rfl
    · rfl
    · rfl
    · simp only [show t ≠ 447 by omega, show t ≠ 1 by omega, show t ≠ 0 by omega,
        show ¬t < 2 by omega, ite_false]
      rw [h₂.bits t (by omega), VG.Proof.X448.Arm.getD_bytesAt _ _ (by omega)]

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Decode`. -/
section

/-!
# X448 on ARMv7: decoding a coordinate limb

Two byte loads construct a 16-bit limb, which is written to both initial
coordinate slots.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_ldrb wp_dp op2_lsl)

theorem decodeLimb_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {i : Nat}
    (hi : i < 28) (hp : State.addr (s.gpr .r2) = p) (hfit : (s.gpr .r2).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (VG.Proof.X448.Arm.off p j) 1) :
    WP isa (.block (decodeLimb i)) s fun t =>
      t.mem = (s.mem.writeW (VG.Proof.X448.Arm.off base (X1 + 4 * i)) (BitVec.ofNat 32 (VG.Proof.X448.Radix16.decoded s.mem p i))).writeW
        (VG.Proof.X448.Arm.off base (X3 + 4 * i)) (BitVec.ofNat 32 (VG.Proof.X448.Radix16.decoded s.mem p i)) ∧ VG.Proof.X448.Arm.Keeps [.r3, .r4] s t := by
  have ea0 : State.addr (s.gpr .r2 + BitVec.ofNat 32 (2 * i)) = VG.Proof.X448.Arm.off p (2 * i) := by
    rw [addr_add (by omega), hp]
  have ea1 : State.addr (s.gpr .r2 + BitVec.ofNat 32 (2 * i + 1)) = VG.Proof.X448.Arm.off p (2 * i + 1) := by
    rw [addr_add (by omega), hp]
  unfold decodeLimb
  refine wp_ldrb (a := VG.Proof.X448.Arm.off p (2 * i)) (by omega) ea0 (hr _ (by omega)) fun s1 h1 => ?_
  refine wp_ldrb (a := VG.Proof.X448.Arm.off p (2 * i + 1)) (by omega)
    (by rw [h1.other .r2 (by decide)]; exact ea1)
    (by rw [h1.rd, h1.wr]; exact hr _ (by omega)) fun s2 h2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s3 h3 => ?_
  have value : s3.gpr .r3 = BitVec.ofNat 32 (VG.Proof.X448.Radix16.decoded s.mem p i) := by
    rw [h3.gpr]
    change s2.gpr .r3 + s2.gpr .r4 <<< 8 = _
    rw [h2.other .r3 (by decide), h1.gpr, h2.gpr, h1.mem]
    apply BitVec.eq_of_toNat_eq
    have h0 := (s.mem (VG.Proof.X448.Arm.off p (2 * i))).isLt
    have h1 := (s.mem (VG.Proof.X448.Arm.off p (2 * i + 1))).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat, VG.Proof.X448.Radix16.decoded, VG.Proof.X448.Radix16.byteN]
    simp only [VG.Proof.X448.Arm.off] at h0 h1 ⊢
    omega
  have hs1 := hs.of_upd h1 (by decide) (by decide)
  have hs2 := hs1.of_upd h2 (by decide) (by decide)
  have hs3 := hs2.of_upd h3 (by decide) (by decide)
  refine VG.Proof.X448.Arm.store_ok hs3 (by simp only [X1, slot]; omega) fun s4 h4 => ?_
  have hs4 := hs3.of_keeps (VG.Proof.X448.Arm.rest_keeps (h4.rest [])) (by decide)
  refine VG.Proof.X448.Arm.store_ok hs4 (by simp only [X3, slot]; omega) fun s5 h5 => WP.block_nil ⟨?_, ?_⟩
  · rw [h5.mem, h4.mem, h3.mem, h2.mem, h1.mem, h4.gpr, value]
  · exact VG.Proof.X448.Arm.rest_keeps ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans
      ((h3.rest (by decide)).trans ((h4.rest _).trans (h5.rest _)))))

/-- The two coordinate words lie inside their respective slots. -/
theorem decodeLimb_outside (m : Mem) (base : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32) :
    VG.Proof.X448.Arm.Outside2 base X1 (4 * (i + 1)) X3 (4 * (i + 1)) m
      ((m.writeW (VG.Proof.X448.Arm.off base (X1 + 4 * i)) v).writeW (VG.Proof.X448.Arm.off base (X3 + 4 * i)) v) := by
  intro p hp hq
  rw [VG.Proof.X448.Arm.writeW_outside _ _ _ (by simp only [X3, slot]; omega) p (by omega),
    VG.Proof.X448.Arm.writeW_outside _ _ _ (by simp only [X1, slot]; omega) p (by omega)]

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.DecodeAll`. -/
section

/-!
# X448 on ARMv7: decoding the whole coordinate

The 28 limb loads fill two slots while preserving input bytes outside the
working space.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

theorem decoded_congr {m m' : Mem} {p : Addr} {i : Nat} (hi : i < 28)
    (h : ∀ j < 56, m' (VG.Proof.X448.Arm.off p j) = m (VG.Proof.X448.Arm.off p j)) : VG.Proof.X448.Radix16.decoded m' p i = VG.Proof.X448.Radix16.decoded m p i := by
  simp only [VG.Proof.X448.Radix16.decoded, VG.Proof.X448.Radix16.byteN]
  rw [h (2 * i) (by omega), h (2 * i + 1) (by omega)]

theorem decodeAll_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.Arm.Scr s base)
    (hp : State.addr (s.gpr .r2) = p) (hfit : (s.gpr .r2).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (VG.Proof.X448.Arm.off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ VG.Proof.X448.Arm.ofs base (VG.Proof.X448.Arm.off p j)) :
    WP isa (.block ((List.range 28).flatMap decodeLimb)) s fun t =>
      (∀ j < 28, VG.Proof.X448.Arm.limbs t.mem base X1 j = VG.Proof.X448.Radix16.decoded s.mem p j) ∧
      (∀ j < 28, VG.Proof.X448.Arm.limbs t.mem base X3 j = VG.Proof.X448.Radix16.decoded s.mem p j) ∧
      VG.Proof.X448.Arm.Outside2 base X1 112 X3 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r4] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, VG.Proof.X448.Arm.limbs t.mem base X1 j = VG.Proof.X448.Radix16.decoded s.mem p j) ∧
    (∀ j < n, VG.Proof.X448.Arm.limbs t.mem base X3 j = VG.Proof.X448.Radix16.decoded s.mem p j) ∧
    VG.Proof.X448.Arm.Outside2 base X1 (4 * n) X3 (4 * n) s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r4] s t
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block (decodeLimb n)) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tp : State.addr (t.gpr .r2) = p := by rw [tk.1 _ (by decide)]; exact hp
    have tfit : (t.gpr .r2).toNat + 56 ≤ 2 ^ 32 := by rw [tk.1 _ (by decide)]; exact hfit
    have tr : ∀ j < 56, InRegions (t.rd ++ t.wr) (VG.Proof.X448.Arm.off p j) 1 := by
      intro j hj; rw [tk.2.1, tk.2.2]; exact hr j hj
    have byte : ∀ j < 56, t.mem (VG.Proof.X448.Arm.off p j) = s.mem (VG.Proof.X448.Arm.off p j) := by
      intro j hj
      have h := hd j hj
      exact tm _ (Or.inr (by simp only [X1, slot]; omega)) (Or.inr (by simp only [X3, slot]; omega))
    have eq := VG.Proof.X448.Arm.decoded_congr hn byte
    refine WP.mono (VG.Proof.X448.Arm.decodeLimb_ok (hs.of_keeps tk (by decide)) hn tp tfit tr) fun u ⟨um, uk⟩ => ?_
    rw [eq] at um
    let v := BitVec.ofNat 32 (VG.Proof.X448.Radix16.decoded s.mem p n)
    have vn : v.toNat = VG.Proof.X448.Radix16.decoded s.mem p n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (decoded_lt s.mem p n) (by decide))]
    have pair := fun j (hj : j < 28) => VG.Proof.X448.Arm.pair_write (m := t.mem) (base := base)
      (x := X1) (y := X3) (by decide) (by decide) (by decide) hn hj v v
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · intro j hj
      rw [um, (pair j (by omega)).1]
      by_cases h : j = n
      · rw [ite_eq_left h, vn, h]
      · rw [ite_eq_right h]; exact tx j (by omega)
    · intro j hj
      rw [um, (pair j (by omega)).2]
      by_cases h : j = n
      · rw [ite_eq_left h, vn, h]
      · rw [ite_eq_right h]; exact ty j (by omega)
    · rw [um]
      exact (tm.mono (by omega) (by omega)).trans (VG.Proof.X448.Arm.decodeLimb_outside _ _ hn _)
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hj => by omega, fun _ hj => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Fill`. -/
section

/-!
# X448 on ARMv7: filling words with zero

Each store touches only its designated word in the working space.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

theorem storeOne_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {d : Nat}
    (hd : d + 4 ≤ 4096) (r : Reg) : WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.Arm.off base d) (s.gpr r) ∧ VG.Proof.X448.Arm.Keeps [] s t := by
  refine VG.Proof.X448.Arm.store_ok hs hd fun t ht => WP.block_nil ⟨ht.mem, VG.Proof.X448.Arm.rest_keeps (ht.rest _)⟩

theorem zeroR3_ok (s : State) : WP isa (.block [.mov .r3 (.imm 0)]) s fun t =>
    t.gpr .r3 = 0 ∧ t.mem = s.mem ∧ VG.Proof.X448.Arm.Keeps [.r3] s t := by
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide))
    fun t ht => WP.block_nil ⟨ht.gpr, ht.mem, VG.Proof.X448.Arm.rest_keeps (ht.rest (by decide))⟩

theorem fill_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {o n : Nat} (ho : o + 4 * n ≤ 4096)
    (hz : s.gpr .r3 = 0) :
    WP isa (.block ((List.range n).map (fun i => st .r3 (o + 4 * i)))) s fun t =>
      (∀ i < n, VG.Proof.X448.Arm.limbs t.mem base o i = 0) ∧ VG.Proof.X448.Arm.Outside base o (4 * n) s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [] s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, VG.Proof.X448.Arm.limbs t.mem base o i = 0) ∧ VG.Proof.X448.Arm.Outside base o (4 * n) s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [] s t
  have step : ∀ k t, k < n → inv k t →
      WP isa (.block [st .r3 (o + 4 * k)]) t (inv (k + 1)) := by
    intro k t hk ⟨tf, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (VG.Proof.X448.Arm.storeOne_ok ts (by omega) .r3) fun u ⟨um, uk⟩ => ?_
    rw [tk.1 .r3 (by decide), hz] at um
    have out : VG.Proof.X448.Arm.Outside base (o + 4 * k) 4 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.Arm.writeW_outside _ _ _ (by omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (VG.Proof.X448.Arm.word u.mem base (o + 4 * i)).toNat = _
    rw [um, VG.Proof.X448.Arm.word_write t.mem base (by omega) (by omega)]
    by_cases h : i = k
    · rw [ite_eq_left h]; rfl
    · rw [ite_eq_right h]; exact tf i (by omega)
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) (N := n) inv step n (by omega) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.FinalSwap`. -/
section

/-!
# X448 on ARMv7: the final ladder swap

The last swap bit selects the coordinates that are converted back to affine
form.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm
open VG.Proof.X25519.Arm (wp_mov op2_imm wp_dp op2_reg)

theorem mask_of : ∀ a < 2, (0 : BitVec 32) - BitVec.ofNat 32 a = VG.Proof.X448.Arm.mask (decide (a = 1)) := by decide

theorem swapMask_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : VG.Proof.X448.Arm.word s.mem base SWAP = BitVec.ofNat 32 sw) :
    WP isa (.block [ld .r2 SWAP, .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r2)]) s
      fun t => t.gpr .r5 = VG.Proof.X448.Arm.mask (decide (sw = 1)) ∧ t.mem = s.mem ∧ VG.Proof.X448.Arm.Keeps [.r2, .r5] s t := by
  refine VG.Proof.X448.Arm.load_ok hs (by decide) fun s1 h1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 h2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 h3 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [h3.gpr]
    change s2.gpr .r5 - s2.gpr .r2 = _
    rw [h2.gpr, h2.other .r2 (by decide), h1.gpr, hw]
    exact VG.Proof.X448.Arm.mask_of sw hsw
  · rw [h3.mem, h2.mem, h1.mem]
  · exact VG.Proof.X448.Arm.rest_keeps ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans (h3.rest (by decide))))

theorem lastSwap_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.BoundedEnv s.mem base)
    {sw : Nat} (hsw : sw < 2) (hw : VG.Proof.X448.Arm.word s.mem base SWAP = BitVec.ofNat 32 sw) :
    WP isa (.block lastSwap) s fun t => VG.Proof.X448.Arm.Keep base s t ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧
      VG.Proof.X448.Arm.E t.mem base = VG.Proof.X448.Arm.opSwap 2 4 (decide (sw = 1)) (VG.Proof.X448.Arm.opSwap 1 3 (decide (sw = 1)) (VG.Proof.X448.Arm.E s.mem base)) := by
  rw [lastSwap, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.swapMask_ok hs hsw hw) fun t ⟨tc, tm, tk⟩ => ?_
  have kt : VG.Proof.X448.Arm.Keep base s t := ⟨tk.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide), tm ▸ Outside2.refl _ _ _ _ _ _⟩
  refine WP.mono (VG.Proof.X448.Arm.swaps_ok (kt.scr hs) (tm ▸ hb) tc) fun u ⟨ku, bu, eu⟩ =>
    ⟨kt.trans ku, bu, by rw [eu, tm]⟩

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Save`. -/
section

/-!
# X448 on ARMv7: saving the callee-saved registers

The first eight working-space words preserve the incoming values until the
final restore.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm
open VG.Proof.X25519.Arm (wp_str wp_mov wp_movw op2_reg)

def Saved (base : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, VG.Proof.X448.Arm.word m base (4 * i) = g (saved[i]!)

theorem Saved.outside {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : VG.Proof.X448.Arm.Saved base g m)
    {o n : Nat} (ho : VG.Proof.X448.Arm.Outside base o n m m') (h32 : 32 ≤ o) : VG.Proof.X448.Arm.Saved base g m' := by
  intro i hi
  exact (ho.word (Or.inl (by omega)) (by omega)).trans (h i hi)

theorem Saved.outside2 {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : VG.Proof.X448.Arm.Saved base g m)
    {x nx y ny : Nat} (ho : VG.Proof.X448.Arm.Outside2 base x nx y ny m m') (hx : 32 ≤ x) (hy : 32 ≤ y) :
    VG.Proof.X448.Arm.Saved base g m' := by
  intro i hi
  exact (ho.word (Or.inl (by omega)) (Or.inl (by omega)) (by omega)).trans (h i hi)

theorem save_ok {s : State} {base : Addr} (hc : State.addr (s.gpr .r3) = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32) :
    WP isa (.block ((List.range 8).map (fun i => .str (saved[i]!) .r3 (4 * i)))) s fun t =>
      VG.Proof.X448.Arm.Saved base s.gpr t.mem ∧ VG.Proof.X448.Arm.Outside base 0 32 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.Arm.word t.mem base (4 * i) = s.gpr (saved[i]!)) ∧
      VG.Proof.X448.Arm.Outside base 0 32 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [] s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block [.str (saved[n]!) .r3 (4 * n)]) t (inv (n + 1)) := by
    intro n t hn' ⟨tv, tm, tk⟩
    have ea : State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * n)) = VG.Proof.X448.Arm.off base (4 * n) := by
      rw [tk.1 _ (by decide), addr_add (by omega), hc]
    have wr : InRegions t.wr (VG.Proof.X448.Arm.off base (4 * n)) 4 := by
      rw [tk.2.2]; exact ⟨_, hw, VG.Proof.X448.Arm.contains_sc (by omega)⟩
    refine wp_str (by omega) ea wr fun u hu => WP.block_nil ?_
    refine ⟨?_, tm.trans ?_, tk.trans (VG.Proof.X448.Arm.rest_keeps (hu.rest _))⟩
    · intro i hi
      rw [hu.mem, tk.1 _ (by simp)]
      have h := VG.Proof.X448.Arm.word_write (o := 0) (i := n) (j := i) t.mem base (by omega) (by omega) (s.gpr (saved[n]!))
      simp only [Nat.zero_add] at h
      rw [h]
      by_cases he : i = n
      · rw [ite_eq_left he, he]
      · rw [ite_eq_right he]; exact tv i (by omega)
    · rw [hu.mem]
      exact (VG.Proof.X448.Arm.writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

def setupHead : List Instr :=
  (List.range 8).map (fun i => .str (saved[i]!) .r3 (4 * i)) ++
    [.mov .r12 (.reg .r0), .mov .r0 (.reg .r3), .movw .r6 65535]

theorem setupHead_ok {s : State} {base : Addr} (hc : State.addr (s.gpr .r3) = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32) :
    WP isa (.block VG.Proof.X448.Arm.setupHead) s fun t =>
      VG.Proof.X448.Arm.Scr t base ∧ t.gpr .r12 = s.gpr .r0 ∧ VG.Proof.X448.Arm.Saved base s.gpr t.mem ∧
      VG.Proof.X448.Arm.Outside base 0 32 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r12, .r0, .r6] s t := by
  unfold VG.Proof.X448.Arm.setupHead
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.save_ok hc hw hn) fun t ⟨tv, tm, tk⟩ => ?_
  refine wp_mov (op2_reg _ _) fun u hu => ?_
  refine wp_mov (op2_reg _ _) fun v hv => ?_
  refine wp_movw fun w hw' => WP.block_nil ?_
  have kr : VG.Proof.X448.Arm.Keeps [.r12, .r0, .r6] t w := (VG.Proof.X448.Arm.rest_keeps (hu.rest (by decide))).trans
    ((VG.Proof.X448.Arm.rest_keeps (hv.rest (by decide))).trans (VG.Proof.X448.Arm.rest_keeps (hw'.rest (by decide))))
  refine ⟨⟨?_, hw'.gpr, ?_, ?_⟩, ?_, ?_, ?_, (tk.mono (by simp)).trans kr⟩
  · rw [hw'.other _ (by decide), hv.gpr, hu.other _ (by decide), tk.1 _ (by decide)]; exact hc
  · rw [hw'.wr, hv.wr, hu.wr, tk.2.2]; exact hw
  · rw [hw'.other _ (by decide), hv.gpr, hu.other _ (by decide), tk.1 _ (by decide)]; exact hn
  · rw [hw'.other _ (by decide), hv.other _ (by decide), hu.gpr, tk.1 _ (by decide)]
  · rw [hw'.mem, hv.mem, hu.mem]; exact tv
  · rw [hw'.mem, hv.mem, hu.mem]; exact tm

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Restore`. -/
section

/-!
# X448 on ARMv7: restoring the callee-saved registers

Each incoming register value is loaded from its designated working-space word.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

theorem saved_inj : ∀ i < 8, ∀ j < 8, saved[i]! = saved[j]! → i = j := by decide

theorem saved_mem : ∀ i < 8, saved[i]! ∈ saved := by decide

theorem restore_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {g : Reg → BitVec 32}
    (hsv : VG.Proof.X448.Arm.Saved base g s.mem) :
    WP isa (.block ((List.range 8).map (fun i => ld (saved[i]!) (4 * i)))) s fun t =>
      (∀ i < 8, t.gpr (saved[i]!) = g (saved[i]!)) ∧ t.mem = s.mem ∧ VG.Proof.X448.Arm.Keeps saved s t := by
  let inv := fun (n : Nat) (t : State) =>
    (∀ i < n, t.gpr (saved[i]!) = g (saved[i]!)) ∧ t.mem = s.mem ∧ VG.Proof.X448.Arm.Keeps saved s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block [ld (saved[n]!) (4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    have ea : State.addr (t.gpr .r0 + BitVec.ofNat 32 (4 * n)) = VG.Proof.X448.Arm.off base (4 * n) := by
      rw [tk.1 _ (by decide)]; exact hs.ea (by omega)
    have hr : InRegions (t.rd ++ t.wr) (VG.Proof.X448.Arm.off base (4 * n)) 4 := by
      rw [tk.2.1, tk.2.2]; exact hs.read (by omega)
    refine VG.Proof.X25519.Arm.wp_ldr (by omega) ea hr fun u hu => WP.block_nil ⟨?_, hu.mem.trans tm,
      tk.trans (VG.Proof.X448.Arm.rest_keeps (hu.rest (VG.Proof.X448.Arm.saved_mem n hn)))⟩
    intro i hi
    by_cases he : i = n
    · subst i; rw [hu.gpr, tm]; exact hsv n hn
    · rw [hu.other _ (fun h => he (VG.Proof.X448.Arm.saved_inj i (by omega) n hn h))]
      exact tv i (by omega)
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hi => by omega, rfl, Keeps.refl _ _⟩

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Initial`. -/
section

/-!
# X448 on ARMv7: initial field values

Every slot starts with bounded limbs. The decoded coordinates are retained,
and the ladder starts with X2 = 1, Z2 = 0, Z3 = 1, and a zero swap bit.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

def zeroSlots : List Instr :=
  [.mov .r3 (.imm 0)] ++ (List.range 64).map (fun i => st .r3 (X2 + 4 * i)) ++
    (List.range 576).map (fun i => st .r3 (Z3 + 4 * i))

theorem zeroSlots_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) :
    WP isa (.block VG.Proof.X448.Arm.zeroSlots) s fun t =>
      (∀ i : VG.Proof.X448.Arm.Index, ∀ j < 28, VG.Proof.X448.Arm.limbs t.mem base (slot i.val) j =
        if i = 0 ∨ i = 3 then VG.Proof.X448.Arm.limbs s.mem base (slot i.val) j else 0) ∧
      t.gpr .r3 = 0 ∧ VG.Proof.X448.Arm.Outside base X2 2688 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3] s t := by
  rw [VG.Proof.X448.Arm.zeroSlots, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.zeroR3_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  have ts := hs.of_keeps tk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.fill_ok ts (by decide : X2 + 4 * 64 ≤ 4096) tz) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (VG.Proof.X448.Arm.fill_ok (ts.of_keeps uk (by decide)) (by decide : Z3 + 4 * 576 ≤ 4096)
    ((uk.1 _ (by decide)).trans tz)) fun v ⟨vf, vm, vk⟩ => ?_
  refine ⟨?_, (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tz), ?_, ?_⟩
  · intro i j hj
    have il := i.isLt
    by_cases h0 : i = 0
    · subst i
      rw [ite_eq_left (Or.inl rfl)]
      change (VG.Proof.X448.Arm.word v.mem base (64 + 4 * j)).toNat = _
      rw [vm.word (by change 64 + 4 * j + 4 ≤ 576 ∨ _; omega) (by omega),
        um.word (by change 64 + 4 * j + 4 ≤ 192 ∨ _; omega) (by omega), tm]
      rfl
    · by_cases h3 : i = 3
      · subst i
        rw [ite_eq_left (Or.inr rfl)]
        change (VG.Proof.X448.Arm.word v.mem base (448 + 4 * j)).toNat = _
        rw [vm.word (by change 448 + 4 * j + 4 ≤ 576 ∨ _; omega) (by omega),
          um.word (by change _ ∨ 192 + 4 * 64 ≤ 448 + 4 * j; omega) (by omega), tm]
        rfl
      · rw [ite_eq_right (not_or_intro h0 h3)]
        have i0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
        have i3 : i.val ≠ 3 := fun h => h3 (Fin.ext h)
        rcases Nat.lt_or_ge i.val 3 with h | h
        · have index : slot i.val + 4 * j = X2 + 4 * (32 * (i.val - 1) + j) := by
            simp only [slot, X2]; omega
          change (VG.Proof.X448.Arm.word v.mem base (slot i.val + 4 * j)).toNat = 0
          rw [vm.word (Or.inl (by simp only [slot, Z3]; omega)) (by simp only [slot]; omega), index]
          exact uf _ (by omega)
        · have index : slot i.val + 4 * j = Z3 + 4 * (32 * (i.val - 4) + j) := by
            simp only [slot, Z3]; omega
          change (VG.Proof.X448.Arm.word v.mem base (slot i.val + 4 * j)).toNat = 0
          rw [index]
          exact vf _ (by omega)
  · rw [← tm]
    exact (um.mono (by omega) (by omega)).trans (vm.mono (by decide) (by decide))
  · exact tk.trans ((uk.trans vk).mono (fun _ hr => False.elim (List.not_mem_nil hr)))

def initialMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (VG.Proof.X448.Arm.off base SWAP) (0 : BitVec 32)).writeW (VG.Proof.X448.Arm.off base X2) (1 : BitVec 32)).writeW
    (VG.Proof.X448.Arm.off base Z3) (1 : BitVec 32)

theorem initialStores_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hz : s.gpr .r3 = 0) :
    WP isa (.block [st .r3 SWAP, .mov .r3 (.imm 1), st .r3 X2, st .r3 Z3]) s
      fun t => t.mem = VG.Proof.X448.Arm.initialMem s.mem base ∧ VG.Proof.X448.Arm.Keeps [.r3] s t := by
  refine VG.Proof.X448.Arm.store_ok hs (by decide) fun s1 h1 => ?_
  have hs1 := hs.of_keeps (VG.Proof.X448.Arm.rest_keeps (h1.rest [])) (by decide)
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun s2 h2 => ?_
  have hs2 := hs1.of_upd h2 (by decide) (by decide)
  refine VG.Proof.X448.Arm.store_ok hs2 (by decide) fun s3 h3 => ?_
  have hs3 := hs2.of_keeps (VG.Proof.X448.Arm.rest_keeps (h3.rest [])) (by decide)
  refine VG.Proof.X448.Arm.store_ok hs3 (by decide) fun s4 h4 => WP.block_nil ⟨?_, ?_⟩
  · rw [h4.mem, h3.mem, h2.mem, h1.mem, h3.gpr, h2.gpr, hz]
    rfl
  · exact VG.Proof.X448.Arm.rest_keeps ((h1.rest _).trans ((h2.rest (by decide)).trans ((h3.rest _).trans (h4.rest _))))

theorem initialMem_limb (m : Mem) (base : Addr) (i : VG.Proof.X448.Arm.Index) {j : Nat} (hj : j < 28) :
    VG.Proof.X448.Arm.limbs (VG.Proof.X448.Arm.initialMem m base) base (slot i.val) j =
      if (i = 1 ∨ i = 4) ∧ j = 0 then 1 else VG.Proof.X448.Arm.limbs m base (slot i.val) j := by
  have il := i.isLt
  have hd : slot i.val + 4 * j + 4 ≤ 8192 := by simp only [slot]; omega
  have hm : (slot i.val + 4 * j) % 4 = 0 := by simp only [slot]; omega
  have es : slot i.val + 4 * j ≠ SWAP := by simp only [slot, SWAP]; omega
  have ex : slot i.val + 4 * j = X2 ↔ i = 1 ∧ j = 0 := by
    simp only [slot, X2]
    constructor
    · intro h; exact ⟨Fin.ext (by omega), by omega⟩
    · rintro ⟨rfl, rfl⟩; rfl
  have ez : slot i.val + 4 * j = Z3 ↔ i = 4 ∧ j = 0 := by
    simp only [slot, Z3]
    constructor
    · intro h; exact ⟨Fin.ext (by omega), by omega⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [VG.Proof.X448.Arm.limbs, VG.Proof.X448.Arm.initialMem]
  rw [VG.Proof.X448.Arm.word_write_aligned _ base (by decide) hd (by decide) hm,
    VG.Proof.X448.Arm.word_write_aligned _ base (by decide) hd (by decide) hm,
    VG.Proof.X448.Arm.word_write_aligned _ base (by decide) hd (by decide) hm, ite_eq_right es]
  simp only [ex, ez]
  by_cases h1 : i = 1 <;> by_cases h4 : i = 4 <;> by_cases h0 : j = 0 <;>
    simp only [h1, h4, h0, and_true, and_false, or_true, or_false,
      true_or, ite_true, ite_false] <;> rfl

theorem initialMem_outside (m : Mem) (base : Addr) : VG.Proof.X448.Arm.Outside base 32 2848 m (VG.Proof.X448.Arm.initialMem m base) := by
  intro p hp
  simp only [VG.Proof.X448.Arm.initialMem]
  rw [VG.Proof.X448.Arm.writeW_outside _ _ _ (by decide : Z3 + 4 ≤ 8192) p (by simp only [Z3, slot]; omega),
    VG.Proof.X448.Arm.writeW_outside _ _ _ (by decide : X2 + 4 ≤ 8192) p (by simp only [X2, slot]; omega),
    VG.Proof.X448.Arm.writeW_outside _ _ _ (by decide : SWAP + 4 ≤ 8192) p (by simp only [SWAP]; omega)]

theorem initSlots_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base)
    (h0 : VG.Proof.X448.Arm.Bounded s.mem base X1) (h3 : VG.Proof.X448.Arm.Bounded s.mem base X3) :
    WP isa (.block initSlots) s fun t =>
      VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ VG.Proof.X448.Arm.E t.mem base 0 = VG.Proof.X448.Arm.E s.mem base 0 ∧ VG.Proof.X448.Arm.E t.mem base 1 = 1 ∧
      VG.Proof.X448.Arm.E t.mem base 2 = 0 ∧ VG.Proof.X448.Arm.E t.mem base 3 = VG.Proof.X448.Arm.E s.mem base 3 ∧ VG.Proof.X448.Arm.E t.mem base 4 = 1 ∧
      VG.Proof.X448.Arm.word t.mem base SWAP = 0 ∧ VG.Proof.X448.Arm.Outside base 32 2848 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3] s t := by
  change WP isa (.block (VG.Proof.X448.Arm.zeroSlots ++ [st .r3 SWAP, .mov .r3 (.imm 1),
    st .r3 X2, st .r3 Z3])) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.zeroSlots_ok hs) fun t ⟨tf, tz, tm, tk⟩ => ?_
  refine WP.mono (VG.Proof.X448.Arm.initialStores_ok (hs.of_keeps tk (by decide)) tz) fun u ⟨um, uk⟩ => ?_
  have lf : ∀ i : VG.Proof.X448.Arm.Index, ∀ j < 28, VG.Proof.X448.Arm.limbs u.mem base (slot i.val) j =
      if (i = 1 ∨ i = 4) ∧ j = 0 then 1 else
        if i = 0 ∨ i = 3 then VG.Proof.X448.Arm.limbs s.mem base (slot i.val) j else 0 := by
    intro i j hj
    rw [um, VG.Proof.X448.Arm.initialMem_limb _ _ i hj, tf i j hj]
  have zval : VG.Proof.X448.Radix16.valN (fun _ => 0) 28 = 0 := by decide
  have oval : VG.Proof.X448.Radix16.valN (fun j => if j = 0 then 1 else 0) 28 = 1 := by decide +kernel
  have l0 : ∀ j < 28, VG.Proof.X448.Arm.limbs u.mem base X1 j = VG.Proof.X448.Arm.limbs s.mem base X1 j := by
    intro j hj
    have h := lf (⟨0, by decide⟩ : VG.Proof.X448.Arm.Index) j hj
    dsimp only [X1]
    simpa (config := {decide := true}) only [false_or, false_and, ite_true, ite_false] using h
  have l1 : ∀ j < 28, VG.Proof.X448.Arm.limbs u.mem base X2 j = if j = 0 then 1 else 0 := by
    intro j hj
    have h := lf (⟨1, by decide⟩ : VG.Proof.X448.Arm.Index) j hj
    dsimp only [X2]
    simpa (config := {decide := true}) only [true_or, true_and, ite_false] using h
  have l2 : ∀ j < 28, VG.Proof.X448.Arm.limbs u.mem base Z2 j = 0 := by
    intro j hj
    have h := lf (⟨2, by decide⟩ : VG.Proof.X448.Arm.Index) j hj
    dsimp only [Z2]
    simpa (config := {decide := true}) only [false_or, false_and, ite_false] using h
  have l3 : ∀ j < 28, VG.Proof.X448.Arm.limbs u.mem base X3 j = VG.Proof.X448.Arm.limbs s.mem base X3 j := by
    intro j hj
    have h := lf (⟨3, by decide⟩ : VG.Proof.X448.Arm.Index) j hj
    dsimp only [X3]
    simpa (config := {decide := true}) only [false_or, false_and, ite_true, ite_false] using h
  have l4 : ∀ j < 28, VG.Proof.X448.Arm.limbs u.mem base Z3 j = if j = 0 then 1 else 0 := by
    intro j hj
    have h := lf (⟨4, by decide⟩ : VG.Proof.X448.Arm.Index) j hj
    dsimp only [Z3]
    simpa (config := {decide := true}) only [or_true, true_and, ite_false] using h
  refine ⟨?_, congrArg toFe (VG.Proof.X448.Radix16.valN_congr l0), ?_, ?_, congrArg toFe (VG.Proof.X448.Radix16.valN_congr l3), ?_, ?_, ?_, tk.trans uk⟩
  · intro i j hj
    rw [lf i j hj]
    split
    · decide
    · split
      · rename_i h
        rcases h with rfl | rfl
        · exact h0 j hj
        · exact h3 j hj
      · decide
  · change toFe (VG.Proof.X448.Arm.fe u.mem base X2) = 1
    rw [show VG.Proof.X448.Arm.fe u.mem base X2 = VG.Proof.X448.Radix16.valN (fun j => if j = 0 then 1 else 0) 28 from VG.Proof.X448.Radix16.valN_congr l1, oval]
    exact toFe_one
  · change toFe (VG.Proof.X448.Arm.fe u.mem base Z2) = 0
    rw [show VG.Proof.X448.Arm.fe u.mem base Z2 = VG.Proof.X448.Radix16.valN (fun _ => 0) 28 from VG.Proof.X448.Radix16.valN_congr l2, zval]
    exact toFe_zero
  · change toFe (VG.Proof.X448.Arm.fe u.mem base Z3) = 1
    rw [show VG.Proof.X448.Arm.fe u.mem base Z3 = VG.Proof.X448.Radix16.valN (fun j => if j = 0 then 1 else 0) 28 from VG.Proof.X448.Radix16.valN_congr l4, oval]
    exact toFe_one
  · rw [um, VG.Proof.X448.Arm.initialMem,
      VG.Proof.X448.Arm.word_write_aligned _ base (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      VG.Proof.X448.Arm.word_write_aligned _ base (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [um]
    exact (tm.mono (by decide) (by decide)).trans (VG.Proof.X448.Arm.initialMem_outside _ _)

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Setup`. -/
section

/-!
# X448 on ARMv7: reading the arguments

Setup saves the callee-saved registers, decodes the coordinate, and
initializes the ladder.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

def setupRegs : List Reg := [.r3, .r4, .r12, .r0, .r6]

theorem setup_ok {s : State} {base p : Addr} (hc : State.addr (s.gpr .r3) = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32) (hp : State.addr (s.gpr .r2) = p) (hfit : (s.gpr .r2).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (VG.Proof.X448.Arm.off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ VG.Proof.X448.Arm.ofs base (VG.Proof.X448.Arm.off p j)) :
    WP isa (.block setup) s fun t =>
      VG.Proof.X448.Arm.Scr t base ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ t.gpr .r12 = s.gpr .r0 ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.setupRegs s t ∧
      VG.Proof.X448.Arm.Outside base 0 8192 s.mem t.mem ∧ VG.Proof.X448.Arm.Saved base s.gpr t.mem ∧
      VG.Proof.X448.Arm.E t.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      VG.Proof.X448.Arm.E t.mem base 1 = 1 ∧ VG.Proof.X448.Arm.E t.mem base 2 = 0 ∧
      VG.Proof.X448.Arm.E t.mem base 3 = VG.Proof.X448.Arm.E t.mem base 0 ∧ VG.Proof.X448.Arm.E t.mem base 4 = 1 ∧ VG.Proof.X448.Arm.word t.mem base SWAP = 0 := by
  change WP isa (.block (VG.Proof.X448.Arm.setupHead ++ ((List.range 28).flatMap decodeLimb ++ initSlots))) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.setupHead_ok hc hw hn) fun t ⟨ts, tp, tv, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.decodeAll_ok ts (by rw [tk.1 _ (by decide)]; exact hp)
    (by rw [tk.1 _ (by decide)]; exact hfit)
    (by intro j hj; rw [tk.2.1, tk.2.2]; exact hr j hj) hd) fun u ⟨ux, uy, um, uk⟩ => ?_
  have ub0 : VG.Proof.X448.Arm.Bounded u.mem base X1 := by intro j hj; rw [ux j hj]; exact decoded_lt _ _ _
  have ub3 : VG.Proof.X448.Arm.Bounded u.mem base X3 := by intro j hj; rw [uy j hj]; exact decoded_lt _ _ _
  have uv0 : VG.Proof.X448.Arm.E u.mem base 0 = toFe (VG.Proof.X25519.leNum (Spec.X448.bytesAt t.mem p 56)) := by
    apply congrArg toFe
    exact (VG.Proof.X448.Radix16.valN_congr ux).trans (VG.Proof.X448.Radix16.decoded_val t.mem p 28).symm
  have uv3 : VG.Proof.X448.Arm.E u.mem base 3 = VG.Proof.X448.Arm.E u.mem base 0 := congrArg toFe ((VG.Proof.X448.Radix16.valN_congr uy).trans (VG.Proof.X448.Radix16.valN_congr ux).symm)
  have byte : Spec.X448.bytesAt t.mem p 56 = Spec.X448.bytesAt s.mem p 56 := by
    apply List.map_congr_left
    intro j hj
    exact tm _ (Or.inr (Nat.le_trans (by decide) (hd j (List.mem_range.mp hj))))
  rw [byte] at uv0
  refine WP.mono (VG.Proof.X448.Arm.initSlots_ok (ts.of_keeps uk (by decide)) ub0 ub3)
    fun v ⟨vb, v0, v1, v2, v3, v4, vw, vm, vk⟩ => ?_
  refine ⟨(ts.of_keeps uk (by decide)).of_keeps vk (by decide), vb,
    (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tp),
    (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_)),
    (tm.mono (by decide) (by decide)).trans ?_,
    (tv.outside2 um (by decide) (by decide)).outside vm (by decide),
    ?_, v1, v2, v3.trans (uv3.trans v0.symm), v4, vw⟩
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide
  · intro r h; simp only [List.mem_singleton] at h; subst r; decide
  · exact (show VG.Proof.X448.Arm.Outside base 0 8192 t.mem u.mem from fun q h =>
      um q (by simp only [X1, slot]; omega) (by simp only [X3, slot]; omega)).trans
      (vm.mono (by decide) (by decide))
  · rw [decodeUCoordinate_eq (length_bytesAt _ _ _)]
    exact v0.trans uv0

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Pack`. -/
section

/-!
# X448 on ARMv7: encoding a limb

Two byte stores encode each 16-bit limb in little-endian order without
requiring output alignment.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.X25519.Arm (wp_strb wp_mov op2_lsr)

def packMem (m : Mem) (p : Addr) (i : Nat) (v : BitVec 32) : Mem :=
  (m.writeW (VG.Proof.X448.Arm.off p (2 * i)) (v.setWidth 8)).writeW (VG.Proof.X448.Arm.off p (2 * i + 1)) ((v >>> 8).setWidth 8)

theorem packStep_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {i : Nat} (hi : i < 28)
    (hp : State.addr (s.gpr .r12) = p) (hfit : (s.gpr .r12).toNat + 56 ≤ 2 ^ 32)
    (hw : ∀ j < 2, InRegions s.wr (VG.Proof.X448.Arm.off p (2 * i + j)) 1) :
    WP isa (.block (packLimb i)) s fun t =>
      t.mem = VG.Proof.X448.Arm.packMem s.mem p i (VG.Proof.X448.Arm.word s.mem base (X2 + 4 * i)) ∧ VG.Proof.X448.Arm.Keeps [.r3] s t := by
  have ea : ∀ j < 2, State.addr (s.gpr .r12 + BitVec.ofNat 32 (2 * i + j)) = VG.Proof.X448.Arm.off p (2 * i + j) := by
    intro j hj; rw [addr_add (by omega), hp]
  unfold packLimb
  refine VG.Proof.X448.Arm.load_ok hs (by simp only [X2, slot]; omega) fun t ht => ?_
  refine wp_strb (a := VG.Proof.X448.Arm.off p (2 * i)) (by omega) (by rw [ht.other .r12 (by decide)]; exact ea 0 (by decide))
    (by rw [ht.wr]; exact hw 0 (by decide)) fun u hu => ?_
  refine wp_mov (op2_lsr (by decide)) fun v hv => ?_
  refine wp_strb (a := VG.Proof.X448.Arm.off p (2 * i + 1)) (by omega) (by rw [hv.other .r12 (by decide), hu.gpr, ht.other .r12 (by decide)]; exact ea 1 (by decide))
    (by rw [hv.wr, hu.wr, ht.wr]; exact hw 1 (by decide)) fun w hw' => WP.block_nil ⟨?_, ?_⟩
  · rw [hw'.mem, hv.mem, hu.mem, ht.mem, hv.gpr, hu.gpr, ht.gpr]; rfl
  · exact VG.Proof.X448.Arm.rest_keeps ((ht.rest (by decide)).trans ((hu.rest _).trans
      ((hv.rest (by decide)).trans (hw'.rest _))))

theorem packMem_decoded (m : Mem) (p : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32)
    (hv : v.toNat < VG.Proof.X448.Radix16.radix) : VG.Proof.X448.Radix16.decoded (VG.Proof.X448.Arm.packMem m p i v) p i = v.toNat := by
  have hn : VG.Proof.X448.Arm.off p (2 * i) ≠ VG.Proof.X448.Arm.off p (2 * i + 1) := by
    rw [ne_eq, VG.Proof.X448.Arm.off_eq_iff p (by omega) (by omega)]; omega
  simp only [VG.Proof.X448.Radix16.decoded, VG.Proof.X448.Radix16.byteN, VG.Proof.X448.Arm.packMem, VG.Proof.X448.Arm.writeW8_apply, hn, ite_false, ite_true,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [VG.Proof.X448.Radix16.radix] at hv
  omega

theorem packMem_outside (m : Mem) (p : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32) :
    VG.Proof.X448.Arm.Outside p (2 * i) 2 m (VG.Proof.X448.Arm.packMem m p i v) := by
  intro x hx
  rw [VG.Proof.X448.Arm.packMem, VG.Proof.X448.Arm.writeW8_outside _ _ _ (by omega) (by omega),
    VG.Proof.X448.Arm.writeW8_outside _ _ _ (by omega) (by omega)]

theorem packLimb_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.Bounded s.mem base X2)
    {i : Nat} (hi : i < 28) (hp : State.addr (s.gpr .r12) = p)
    (hfit : (s.gpr .r12).toNat + 56 ≤ 2 ^ 32)
    (hw : ∀ j < 2, InRegions s.wr (VG.Proof.X448.Arm.off p (2 * i + j)) 1) :
    WP isa (.block (packLimb i)) s fun t =>
      VG.Proof.X448.Radix16.decoded t.mem p i = VG.Proof.X448.Arm.limbs s.mem base X2 i ∧ VG.Proof.X448.Arm.Outside p (2 * i) 2 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.clob s t := by
  refine WP.mono (VG.Proof.X448.Arm.packStep_ok hs hi hp hfit hw) fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, tk.mono ?_⟩
  · rw [tm]; exact VG.Proof.X448.Arm.packMem_decoded _ _ hi _ (hb i hi)
  · rw [tm]; exact VG.Proof.X448.Arm.packMem_outside _ _ hi _
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Output`. -/
section

/-!
# X448 on ARMv7: the output buffer

Output stores cover exactly 56 bytes and preserve the disjoint working space.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

/-- Writes to the output preserve a word in the disjoint working space. -/
theorem output_word {m m' : Mem} {base p : Addr} {n d : Nat} (h : VG.Proof.X448.Arm.Outside p 0 n m m') (hn : n ≤ 56)
    (hd : d + 4 ≤ 8192) (hfar : ∀ j < 8192, 56 ≤ VG.Proof.X448.Arm.ofs p (VG.Proof.X448.Arm.off base j)) :
    VG.Proof.X448.Arm.word m' base d = VG.Proof.X448.Arm.word m base d := by
  apply Mem.readW_congr
  intro i hi
  rw [Offset.add_add]
  exact h _ (Or.inr (Nat.le_trans (by omega : 0 + n ≤ 56) (hfar _ (by omega))))

theorem output_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.Bounded s.mem base X2)
    (hp : State.addr (s.gpr .r12) = p)
    (hfit : (s.gpr .r12).toNat + 56 ≤ 2 ^ 32) (hw : ∀ j < 56, InRegions s.wr (VG.Proof.X448.Arm.off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ VG.Proof.X448.Arm.ofs p (VG.Proof.X448.Arm.off base j)) :
    WP isa (.block ((List.range 28).flatMap packLimb)) s fun t =>
      Spec.X448.bytesAt t.mem p 56 = VG.Proof.X25519.leBytes 56 (VG.Proof.X448.Arm.fe s.mem base X2) ∧
      VG.Proof.X448.Arm.Outside p 0 56 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.Radix16.decoded t.mem p i = VG.Proof.X448.Arm.limbs s.mem base X2 i) ∧ VG.Proof.X448.Arm.Outside p 0 (2 * n) s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.clob s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (packLimb n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have eq : ∀ j < 28, VG.Proof.X448.Arm.limbs t.mem base X2 j = VG.Proof.X448.Arm.limbs s.mem base X2 j := by
      intro j hj
      exact congrArg BitVec.toNat (VG.Proof.X448.Arm.output_word tm (by omega) (by simp only [X2, slot]; omega) hfar)
    have tb : VG.Proof.X448.Arm.Bounded t.mem base X2 := by intro j hj; rw [eq j hj]; exact hb j hj
    refine WP.mono (VG.Proof.X448.Arm.packLimb_ok (p := p) (hs.of_keeps tk (by decide)) tb hn (by rw [tk.1 _ (by decide)]; exact hp)
      (by rw [tk.1 _ (by decide)]; exact hfit)
      (by intro j hj; rw [tk.2.2]; exact hw _ (by omega))) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, (tm.mono (by decide) (by omega)).trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    by_cases h : i = n
    · subst i; exact uv.trans (eq n hn)
    · have byte : ∀ j < 2, u.mem (VG.Proof.X448.Arm.off p (2 * i + j)) = t.mem (VG.Proof.X448.Arm.off p (2 * i + j)) := by
        intro j hj
        exact um _ (Or.inl (by rw [VG.Proof.X448.Arm.ofs_off' p (by omega)]; omega))
      simp only [VG.Proof.X448.Radix16.decoded, VG.Proof.X448.Radix16.byteN]
      have b0 := byte 0 (by decide)
      have b1 := byte 1 (by decide)
      simp only [VG.Proof.X448.Arm.off, Nat.add_zero] at b0 b1
      rw [b0, b1]
      exact tf i (by omega)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ =>
    ⟨VG.Proof.X448.Radix16.packed_bytes tf, tm, tk⟩

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.FreezePrep`. -/
section

/-!
# X448 on ARMv7: preparing canonical reduction

Adding one in limbs zero and fourteen implements the addition of 1 + 2²²⁴
before carry propagation.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

theorem incrementStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {d : Nat}
    (hd : d + 4 ≤ 4096) :
    WP isa (.block [ld .r3 d, .dp .add .r3 .r3 (.imm 1), st .r3 d]) s
      fun s' => s'.mem = s.mem.writeW (VG.Proof.X448.Arm.off base d) (VG.Proof.X448.Arm.word s.mem base d + (1 : BitVec 32)) ∧
        VG.Proof.X448.Arm.Keeps [.r3] s s' := by
  refine VG.Proof.X448.Arm.load_ok hs hd fun t ht => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  refine VG.Proof.X448.Arm.store_ok ((hs.of_upd ht (by decide) (by decide)).of_upd hu (by decide) (by decide)) hd
    fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr, ht.gpr]; rfl
  · exact VG.Proof.X448.Arm.rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _)))

theorem incrementLimb_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {k : Nat} (hk : k < 28)
    (hb : VG.Proof.X448.Arm.limbs s.mem base TMP k + 1 < 2 ^ 32) :
    WP isa (.block [ld .r3 (TMP + 4 * k), .dp .add .r3 .r3 (.imm 1),
      st .r3 (TMP + 4 * k)]) s fun t =>
      (∀ i < 28, VG.Proof.X448.Arm.limbs t.mem base TMP i =
        if i = k then VG.Proof.X448.Arm.limbs s.mem base TMP i + 1 else VG.Proof.X448.Arm.limbs s.mem base TMP i) ∧
      VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3] s t := by
  have hd : TMP + 4 * k + 4 ≤ 4096 := by simp only [TMP]; omega
  refine WP.mono (VG.Proof.X448.Arm.incrementStep_ok hs hd) fun t ⟨hm, ht⟩ => ?_
  refine ⟨?_, ?_, ht⟩
  · intro i hi
    change (VG.Proof.X448.Arm.word t.mem base (TMP + 4 * i)).toNat = _
    rw [hm, VG.Proof.X448.Arm.word_write s.mem base (by omega) (by simp only [TMP]; omega)]
    by_cases h : i = k
    · rw [ite_eq_left h, ite_eq_left h, h, BitVec.toNat_add]
      change (VG.Proof.X448.Arm.limbs s.mem base TMP k + 1) % 2 ^ 32 = _
      exact Nat.mod_eq_of_lt hb
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [hm]
    exact (VG.Proof.X448.Arm.writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)

theorem freezePrep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.Bounded s.mem base X2) :
    WP isa (.block (copy TMP X2 ++ [0, 14].flatMap (fun i =>
      [ld .r3 (TMP + 4 * i), .dp .add .r3 .r3 (.imm 1),
        st .r3 (TMP + 4 * i)]))) s fun t =>
      (∀ i < 28, VG.Proof.X448.Arm.limbs t.mem base TMP i = VG.Proof.X448.Radix16.freezeCoeff (VG.Proof.X448.Arm.limbs s.mem base X2) i) ∧
      VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.clob s t := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.copy_ok hs (by decide) (by decide) (by decide)) fun t ⟨tf, tm, tk⟩ => ?_
  have bound : ∀ i < 28, VG.Proof.X448.Arm.limbs s.mem base X2 i + 1 < 2 ^ 32 := by
    intro i hi; have h := hb i hi; simp only [VG.Proof.X448.Radix16.radix] at h; omega
  change WP isa (.block
    (([ld .r3 (TMP + 4 * 0), .dp .add .r3 .r3 (.imm 1),
       st .r3 (TMP + 4 * 0)] : List Instr) ++
     [ld .r3 (TMP + 4 * 14), .dp .add .r3 .r3 (.imm 1),
       st .r3 (TMP + 4 * 14)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.incrementLimb_ok (hs.of_keeps tk (by decide)) (k := 0) (by decide)
    (by rw [tf 0 (by decide)]; exact bound 0 (by decide))) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (VG.Proof.X448.Arm.incrementLimb_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
    (k := 14) (by decide) (by
      rw [uf 14 (by decide), ite_eq_right (by decide), tf 14 (by decide)]
      exact bound 14 (by decide))) fun v ⟨vf, vm, vk⟩ => ?_
  refine ⟨?_, tm.trans (um.trans vm), tk.trans ((uk.trans vk).mono ?_)⟩
  · intro i hi
    rw [vf i hi, uf i hi, tf i hi]
    simp only [VG.Proof.X448.Radix16.freezeCoeff]
    by_cases h0 : i = 0
    · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
    · by_cases h8 : i = 14
      · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
      · simp only [h0, h8, ite_false, false_or, Nat.add_zero]
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Select`. -/
section

/-!
# X448 on ARMv7: selecting the canonical representative

An XOR mask selects each limb from the original value or the carried temporary
value.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

def selectStep (i : Nat) : List Instr :=
  [ld .r3 (X2 + 4 * i), ld .r2 (TMP + 4 * i), .dp .eor .r2 .r2 (.reg .r3),
    .dp .and .r2 .r2 (.reg .r4), .dp .eor .r3 .r3 (.reg .r2), st .r3 (X2 + 4 * i)]

theorem selectStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {i : Nat} (hi : i < 28)
    {sw : Bool} (hc : s.gpr .r4 = VG.Proof.X448.Arm.mask sw) :
    WP isa (.block (VG.Proof.X448.Arm.selectStep i)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.Arm.off base (X2 + 4 * i))
        (if sw then VG.Proof.X448.Arm.word s.mem base (TMP + 4 * i) else VG.Proof.X448.Arm.word s.mem base (X2 + 4 * i)) ∧
      VG.Proof.X448.Arm.Keeps [.r3, .r2] s t := by
  unfold VG.Proof.X448.Arm.selectStep
  refine VG.Proof.X448.Arm.load_ok hs (by simp only [X2, slot]; omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide) (by decide)
  refine VG.Proof.X448.Arm.load_ok ts (by simp only [TMP]; omega) fun u hu => ?_
  have us := ts.of_upd hu (by decide) (by decide)
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun v hv => ?_
  have vs := us.of_upd hv (by decide) (by decide)
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun w hw => ?_
  have ws := vs.of_upd hw (by decide) (by decide)
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun x hx => ?_
  have xs := ws.of_upd hx (by decide) (by decide)
  refine VG.Proof.X448.Arm.store_ok xs (by simp only [X2, slot]; omega) fun y hy => WP.block_nil ⟨?_, ?_⟩
  · rw [hy.mem, hx.mem, hw.mem, hv.mem, hu.mem, ht.mem, hx.gpr]
    change _ = s.mem.writeW _ _
    rw [hw.other .r3 (by decide), hv.other .r3 (by decide), hu.other .r3 (by decide), ht.gpr,
      hw.gpr, hv.gpr, hu.gpr, ht.mem, hu.other .r3 (by decide), ht.gpr,
      hv.other .r4 (by decide), hu.other .r4 (by decide), ht.other .r4 (by decide), hc]
    change s.mem.writeW _ (_ ^^^ ((_ ^^^ _) &&& VG.Proof.X448.Arm.mask sw)) = _
    rw [BitVec.xor_comm (VG.Proof.X448.Arm.word s.mem base (TMP + 4 * i)), (VG.Proof.X448.Arm.xor_sel sw _ _).1]
  · exact VG.Proof.X448.Arm.rest_keeps ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans
      ((hv.rest (by decide)).trans ((hw.rest (by decide)).trans ((hx.rest (by decide)).trans (hy.rest _))))))

theorem select_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) {sw : Bool} (hc : s.gpr .r4 = VG.Proof.X448.Arm.mask sw) :
    WP isa (.block ((List.range 28).flatMap VG.Proof.X448.Arm.selectStep)) s fun t =>
      (∀ i < 28, VG.Proof.X448.Arm.limbs t.mem base X2 i = if sw then VG.Proof.X448.Arm.limbs s.mem base TMP i else VG.Proof.X448.Arm.limbs s.mem base X2 i) ∧
      VG.Proof.X448.Arm.Outside base X2 112 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r2] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.Arm.limbs t.mem base X2 i = if sw then VG.Proof.X448.Arm.limbs s.mem base TMP i else VG.Proof.X448.Arm.limbs s.mem base X2 i) ∧
    VG.Proof.X448.Arm.Outside base X2 (4 * n) s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps [.r3, .r2] s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (VG.Proof.X448.Arm.selectStep n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.X448.Arm.selectStep_ok (hs.of_keeps tk (by decide)) hn ((tk.1 _ (by decide)).trans hc))
      fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.Arm.Outside base (X2 + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.Arm.writeW_outside _ _ _ (by simp only [X2, slot]; omega)
    refine ⟨?_, (tm.mono (by omega) (by omega)).trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (VG.Proof.X448.Arm.word u.mem base (X2 + 4 * i)).toNat = _
    rw [um, VG.Proof.X448.Arm.word_write t.mem base (by simp only [X2, slot]; omega) (by simp only [X2, slot]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h,
        tm.word (Or.inr (by simp only [X2, slot, TMP]; omega)) (by simp only [TMP]; omega),
        tm.word (Or.inr (by omega)) (by simp only [X2, slot]; omega)]
      cases sw <;> rfl
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Freeze`. -/
section

/-!
# X448 on ARMv7: canonical reduction

The final carry selects the unique representative below the prime, using only
a mask on secret data.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

theorem freezeMask_ok {s : State} {c : Nat} (hc : (s.gpr .r5).toNat = c) (hb : c < 2) :
    WP isa (.block [.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r5)]) s fun t =>
      t.gpr .r4 = VG.Proof.X448.Arm.mask (decide (c = 1)) ∧ t.mem = s.mem ∧ VG.Proof.X448.Arm.Keeps [.r4] s t := by
  have he : s.gpr .r5 = BitVec.ofNat 32 c := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm : ∀ a < 2, (0 : BitVec 32) - BitVec.ofNat 32 a = VG.Proof.X448.Arm.mask (decide (a = 1)) := by decide
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t ht => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u hu => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hu.gpr]; change t.gpr .r4 - t.gpr .r5 = _
    rw [ht.gpr, ht.other .r5 (by decide), he]; exact hm c hb
  · exact hu.mem.trans ht.mem
  · exact VG.Proof.X448.Arm.rest_keeps ((ht.rest (by decide)).trans (hu.rest (by decide)))

theorem freeze_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.Bounded s.mem base X2) :
    WP isa (.block freeze) s fun t =>
      VG.Proof.X448.Arm.Bounded t.mem base X2 ∧ VG.Proof.X448.Arm.fe t.mem base X2 = VG.Proof.X448.Arm.fe s.mem base X2 % Spec.X448.P ∧
      VG.Proof.X448.Arm.FieldMem base X2 s.mem t.mem ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.workRegs s t := by
  change WP isa (.block ((copy TMP X2 ++ [0, 14].flatMap (fun i =>
    [ld .r3 (TMP + 4 * i), .dp .add .r3 .r3 (.imm 1),
      st .r3 (TMP + 4 * i)])) ++ (pass TMP TMP ++
    (([.mov .r4 (.imm 0), .dp .sub .r4 .r4 (.reg .r5)] : List Instr) ++
      (List.range 28).flatMap VG.Proof.X448.Arm.selectStep)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.freezePrep_ok hs hb) fun t ⟨tf, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.pass_ok (hs.of_keeps tk (by decide)) (by decide) (by decide) (Or.inl rfl)
    tf (fun i hi => Nat.le_of_lt (VG.Proof.X448.Radix16.freezeCoeff_bound hb i hi))) fun u ⟨uf, uc, um, uk⟩ => ?_
  have cb : VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff (VG.Proof.X448.Arm.limbs s.mem base X2)) 28 < 2 := by
    rw [VG.Proof.X448.Radix16.freeze_carry hb]; split <;> decide
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.freezeMask_ok uc cb) fun v ⟨vc, vm, vk⟩ => ?_
  have vs := ((hs.of_keeps tk (by decide)).of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (VG.Proof.X448.Arm.select_ok vs vc) fun w ⟨wf, wm, wk⟩ => ?_
  have outside : VG.Proof.X448.Arm.Outside base TMP 112 s.mem v.mem := by rw [vm]; exact tm.trans um
  have lf : ∀ i < 28, VG.Proof.X448.Arm.limbs w.mem base X2 i =
      if VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff (VG.Proof.X448.Arm.limbs s.mem base X2)) 28 = 1 then
        VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.freezeCoeff (VG.Proof.X448.Arm.limbs s.mem base X2)) i else VG.Proof.X448.Arm.limbs s.mem base X2 i := by
    intro i hi
    rw [wf i hi, outside.limbs (d := X2) (by decide) (by decide) hi, vm, uf i hi]
    simp only [decide_eq_true_eq]
  refine ⟨?_, ?_, (FieldMem.work outside (by decide) (by decide)).trans (FieldMem.output wm),
    (tk.mono ?_).trans ((uk.mono ?_).trans ((vk.mono ?_).trans (wk.mono ?_)))⟩
  · intro i hi; rw [lf i hi]; split
    · exact VG.Proof.X448.Radix16.digit_lt _ _
    · exact hb i hi
  · change VG.Proof.X448.Radix16.valN (VG.Proof.X448.Arm.limbs w.mem base X2) 28 = _
    rw [VG.Proof.X448.Radix16.valN_congr lf]
    by_cases h : VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff (VG.Proof.X448.Arm.limbs s.mem base X2)) 28 = 1
    · simp only [h, ite_true]
      exact (ite_eq_left h).symm.trans (VG.Proof.X448.Radix16.freeze_value hb)
    · simp only [h, ite_false]
      exact (ite_eq_right h).symm.trans (VG.Proof.X448.Radix16.freeze_value hb)
  · intro r hr; exact List.mem_cons_of_mem _ hr
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Finish`. -/
section

/-!
# X448 on ARMv7: the result and restored registers

The final multiplication, canonical reduction and encoding produce the affine
coordinate. The eight callee-saved registers are then restored from the
disjoint working space.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

theorem Outside.frame {base : Addr} {n : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base 0 n m m') :
    Frame [⟨base, n⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this
  change 0 + n ≤ (x - base).toNat
  omega))

theorem FieldMem.whole {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.FieldMem base o m m')
    (ho : o + 112 ≤ 8192) : VG.Proof.X448.Arm.Outside base 0 8192 m m' := fun p hp =>
  h p (by omega) (by simp only [ACC]; omega)

theorem Outside2.whole {base : Addr} {x nx y ny : Nat} {m m' : Mem}
    (h : VG.Proof.X448.Arm.Outside2 base x nx y ny m m') (hx : x + nx ≤ 8192) (hy : y + ny ≤ 8192) :
    VG.Proof.X448.Arm.Outside base 0 8192 m m' := fun p hp => h p (by omega) (by omega)

theorem Saved.field {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : VG.Proof.X448.Arm.Saved base g m)
    {o : Nat} (hm : VG.Proof.X448.Arm.FieldMem base o m m') (ho : 32 ≤ o) : VG.Proof.X448.Arm.Saved base g m' := by
  intro i hi
  exact (hm.word (Or.inl (by omega)) (by simp only [ACC]; omega)).trans (h i hi)

def finishRegs : List Reg := saved ++ VG.Proof.X448.Arm.workRegs

theorem finish_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.BoundedEnv s.mem base)
    (hp : State.addr (s.gpr .r12) = p)
    (hfit : (s.gpr .r12).toNat + 56 ≤ 2 ^ 32) (hw : ∀ j < 56, InRegions s.wr (VG.Proof.X448.Arm.off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ VG.Proof.X448.Arm.ofs p (VG.Proof.X448.Arm.off base j)) {g : Reg → BitVec 32} (sv : VG.Proof.X448.Arm.Saved base g s.mem) :
    WP isa finish s fun t =>
      (∀ i < 8, t.gpr (saved[i]!) = g (saved[i]!)) ∧ VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.finishRegs s t ∧
      Frame [⟨base, 8192⟩, ⟨p, 56⟩] s.mem t.mem ∧
      Spec.X448.bytesAt t.mem p 56 = Spec.X448.encodeUCoordinate (VG.Proof.X448.Arm.E s.mem base 1 * VG.Proof.X448.Arm.E s.mem base 21) := by
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.mul_ok hs (o := X2) (a := X2) (b := T7) (by decide) (by decide)
    (by decide) (hb 1) (hb 21)) fun u ⟨uk, ub, uv⟩ => ?_)
  have us := hs.of_keeps uk.1 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.freeze_ok us ub) fun v ⟨vb, vv, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.Arm.output_ok (p := p) vs vb (by rw [vk.1 _ (by decide), uk.1.1 _ (by decide)]; exact hp)
    (by rw [vk.1 _ (by decide), uk.1.1 _ (by decide)]; exact hfit)
    (by intro j hj; rw [vk.2.2, uk.1.2.2]; exact hw j hj) hfar) fun w ⟨wv, wm, wk⟩ => ?_
  have ws := vs.of_keeps wk (by decide)
  have svv := (sv.field uk.2 (by decide)).field vm (by decide)
  have svw : VG.Proof.X448.Arm.Saved base g w.mem := by
    intro i hi
    exact (VG.Proof.X448.Arm.output_word wm (by decide) (by omega) hfar).trans (svv i hi)
  refine WP.mono (VG.Proof.X448.Arm.restore_ok ws svw) fun t ⟨tr, tm, tk⟩ => ?_
  refine ⟨tr, (uk.1.mono ?_).trans ((vk.mono ?_).trans ((wk.mono ?_).trans (tk.mono ?_))), ?_, ?_⟩
  · intro r hr; exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  · intro r hr; exact List.mem_append_right _ hr
  · intro r hr; exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  · intro r hr; exact List.mem_append_left _ hr
  · rw [tm]
    exact (((uk.2.whole (by decide)).trans (vm.whole (by decide))).frame.mono (by simp)).trans
      (wm.frame.mono (by simp))
  · rw [tm, wv, vv, encodeUCoordinate_eq]
    refine congrArg (VG.Proof.X25519.leBytes 56) ?_
    exact congrArg Fin.val uv

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Square`. -/
section

/-!
# X448 on ARMv7: runs of squarings

The inversion reuses field multiplication in a loop with its own counter. The
field slots and memory frame compose exactly as they do for straight-line
operation lists.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

structure IKeep (base : Addr) (s t : State) : Prop where
  regs : VG.Proof.X448.Arm.Keeps (.r11 :: VG.Proof.X448.Arm.workRegs) s t
  mem : VG.Proof.X448.Arm.Outside2 base 64 2816 ACC 512 s.mem t.mem

theorem IKeep.refl (base : Addr) (s : State) : VG.Proof.X448.Arm.IKeep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem IKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.X448.Arm.IKeep base s t) (h' : VG.Proof.X448.Arm.IKeep base t u) :
    VG.Proof.X448.Arm.IKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem IKeep.scr {base : Addr} {s t : State} (h : VG.Proof.X448.Arm.IKeep base s t) (hs : VG.Proof.X448.Arm.Scr s base) : VG.Proof.X448.Arm.Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem Keep.ikeep {base : Addr} {s t : State} (h : VG.Proof.X448.Arm.Keep base s t) : VG.Proof.X448.Arm.IKeep base s t :=
  ⟨h.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr), h.mem⟩

theorem counter_keep {base : Addr} {s t : State} (hg : ∀ r, r ≠ .r11 → t.gpr r = s.gpr r)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : VG.Proof.X448.Arm.IKeep base s t :=
  ⟨⟨fun r h => hg r (fun he => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
    hm ▸ Outside2.refl _ _ _ _ _ _⟩

def ISpec (base : Addr) (code : Prog isa) (f : VG.Proof.X448.Arm.Env → VG.Proof.X448.Arm.Env) : Prop :=
  ∀ s, VG.Proof.X448.Arm.Scr s base → VG.Proof.X448.Arm.BoundedEnv s.mem base → WP isa code s fun t =>
    VG.Proof.X448.Arm.IKeep base s t ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ VG.Proof.X448.Arm.E t.mem base = f (VG.Proof.X448.Arm.E s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : VG.Proof.X448.Arm.Env → VG.Proof.X448.Arm.Env}
    (h₁ : VG.Proof.X448.Arm.ISpec base c₁ f) (h₂ : VG.Proof.X448.Arm.ISpec base c₂ g) :
    VG.Proof.X448.Arm.ISpec base (.seq c₁ c₂) (fun e => g (f e)) := fun s hs hb =>
  WP.seq (WP.mono (h₁ s hs hb) fun t ⟨tk, tb, te⟩ =>
    WP.mono (h₂ t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, by rw [ue, te]⟩)

theorem opsI (base : Addr) (xs : List VG.Proof.X448.Arm.FieldOp) :
    VG.Proof.X448.Arm.ISpec base (ops (xs.map FieldOp.impl)) (VG.Proof.X448.Arm.applyOps xs) := fun _ hs hb =>
  WP.mono (VG.Proof.X448.Arm.ops_ok hs hb xs) fun _ ⟨tk, tb, te⟩ => ⟨tk.ikeep, tb, te⟩

def opSqn (o : VG.Proof.X448.Arm.Index) (n : Nat) (e : VG.Proof.X448.Arm.Env) : VG.Proof.X448.Arm.Env := Function.update e o (Proof.X448.sqn (e o) n)

theorem opMul_update (o : VG.Proof.X448.Arm.Index) (e : VG.Proof.X448.Arm.Env) (v : Spec.X448.Fe) :
    VG.Proof.X448.Arm.opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [VG.Proof.X448.Arm.opMul, Function.update_self, Function.update_idem]

theorem sqnI (base : Addr) (o : VG.Proof.X448.Arm.Index) {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 16) :
    VG.Proof.X448.Arm.ISpec base (Impl.X448.Arm.sqn (slot o.val) n) (VG.Proof.X448.Arm.opSqn o n) := by
  intro s hs hb
  rw [Impl.X448.Arm.sqn, WP.seq_iff]
  refine WP.mono (VG.Proof.X448.Arm.setCounter_ok s n hn') fun t ⟨tc, tg, tm, tr, tw⟩ => ?_
  have kt : VG.Proof.X448.Arm.IKeep base s t := VG.Proof.X448.Arm.counter_keep tg tm tr tw
  let inv := fun m (u : State) => 1 ≤ m ∧ m ≤ n ∧ VG.Proof.X448.Arm.IKeep base s u ∧ VG.Proof.X448.Arm.BoundedEnv u.mem base ∧
    u.gpr .r11 = BitVec.ofNat 32 m ∧
    VG.Proof.X448.Arm.E u.mem base = Function.update (VG.Proof.X448.Arm.E s.mem base) o (Proof.X448.sqn (VG.Proof.X448.Arm.E s.mem base o) (n - m))
  refine WP.loop (M := isa) inv ?_ n t ?_
  · intro m u ⟨hm, hm', ku, bu, cu, eu⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [WP.seq_iff]
    refine WP.mono (VG.Proof.X448.Arm.mulE (ku.scr hs) bu o o o) fun v ⟨kv, bv, ev⟩ => ?_
    have cv : v.gpr .r11 = BitVec.ofNat 32 (m + 1) := (kv.regs.1 _ (by decide)).trans cu
    refine WP.mono (VG.Proof.X448.Arm.decCounter_ok (by omega) cv) fun w ⟨cw, wg, wm, wr, ww, wz⟩ => ?_
    have kw : VG.Proof.X448.Arm.IKeep base s w := ku.trans (kv.ikeep.trans (VG.Proof.X448.Arm.counter_keep wg wm wr ww))
    have bw : VG.Proof.X448.Arm.BoundedEnv w.mem base := wm ▸ bv
    have ew : VG.Proof.X448.Arm.E w.mem base = Function.update (VG.Proof.X448.Arm.E s.mem base) o (Proof.X448.sqn (VG.Proof.X448.Arm.E s.mem base o) (n - m)) := by
      rw [wm, ev, eu, VG.Proof.X448.Arm.opMul_update, ← Proof.X448.sqn]
      rw [show (n - (m + 1)).succ = n - m by omega]
    simp only [eval, wz]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl ⟨rfl, kw, bw, ew⟩
    · refine Or.inr ⟨?_, m, by omega, hm, by omega, kw, bw, cw, ew⟩
      rw [decide_eq_false (by omega : ¬m = 0)]; rfl
  · refine ⟨hn, by omega, kt, tm ▸ hb, tc, ?_⟩
    rw [tm, Nat.sub_self, Proof.X448.sqn, Function.update_eq_self]

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Inv`. -/
section

/-!
# X448 on ARMv7: inversion

The addition chain updates slots 14–21 and leaves the ladder's coordinates
available for the final multiplication and encoding.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

/-- The field slots after the inversion's addition chain. -/
def invEnv (e : VG.Proof.X448.Arm.Env) : VG.Proof.X448.Arm.Env :=
  let e := VG.Proof.X448.Arm.applyOps [.copy 14 2] e
  let e := VG.Proof.X448.Arm.opSqn 14 1 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 14 14 2, .copy 15 14] e
  let e := VG.Proof.X448.Arm.opSqn 15 2 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 15 15 14, .copy 16 15] e
  let e := VG.Proof.X448.Arm.opSqn 16 4 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 16 16 15, .copy 17 16] e
  let e := VG.Proof.X448.Arm.opSqn 17 8 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 17 17 16, .copy 18 17] e
  let e := VG.Proof.X448.Arm.opSqn 18 16 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 18 18 17, .copy 19 18] e
  let e := VG.Proof.X448.Arm.opSqn 19 32 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 19 19 18, .copy 20 19] e
  let e := VG.Proof.X448.Arm.opSqn 20 64 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 20 20 19] e
  let e := VG.Proof.X448.Arm.opSqn 20 64 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 20 20 19] e
  let e := VG.Proof.X448.Arm.opSqn 20 16 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 20 20 17] e
  let e := VG.Proof.X448.Arm.opSqn 20 8 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 20 20 16] e
  let e := VG.Proof.X448.Arm.opSqn 20 4 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 20 20 15] e
  let e := VG.Proof.X448.Arm.opSqn 20 2 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 20 20 14, .copy 21 20] e
  let e := VG.Proof.X448.Arm.opSqn 21 1 e
  let e := VG.Proof.X448.Arm.applyOps [.mul 21 21 2] e
  let e := VG.Proof.X448.Arm.opSqn 21 225 e
  let e := VG.Proof.X448.Arm.opSqn 20 2 e
  VG.Proof.X448.Arm.applyOps [.mul 20 20 2, .mul 21 21 20] e

theorem invert_spec (base : Addr) : VG.Proof.X448.Arm.ISpec base Impl.X448.Arm.invert VG.Proof.X448.Arm.invEnv := by
  have h : VG.Proof.X448.Arm.ISpec base _ _ :=
    (VG.Proof.X448.Arm.opsI base [.copy 14 2]).seq <|
    (VG.Proof.X448.Arm.sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 14 14 2, .copy 15 14]).seq <|
    (VG.Proof.X448.Arm.sqnI base 15 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 15 15 14, .copy 16 15]).seq <|
    (VG.Proof.X448.Arm.sqnI base 16 (n := 4) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 16 16 15, .copy 17 16]).seq <|
    (VG.Proof.X448.Arm.sqnI base 17 (n := 8) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 17 17 16, .copy 18 17]).seq <|
    (VG.Proof.X448.Arm.sqnI base 18 (n := 16) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 18 18 17, .copy 19 18]).seq <|
    (VG.Proof.X448.Arm.sqnI base 19 (n := 32) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 19 19 18, .copy 20 19]).seq <|
    (VG.Proof.X448.Arm.sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 20 20 19]).seq <|
    (VG.Proof.X448.Arm.sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 20 20 19]).seq <|
    (VG.Proof.X448.Arm.sqnI base 20 (n := 16) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 20 20 17]).seq <|
    (VG.Proof.X448.Arm.sqnI base 20 (n := 8) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 20 20 16]).seq <|
    (VG.Proof.X448.Arm.sqnI base 20 (n := 4) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 20 20 15]).seq <|
    (VG.Proof.X448.Arm.sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 20 20 14, .copy 21 20]).seq <|
    (VG.Proof.X448.Arm.sqnI base 21 (n := 1) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 21 21 2]).seq <|
    (VG.Proof.X448.Arm.sqnI base 21 (n := 225) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.Arm.opsI base [.mul 20 20 2, .mul 21 21 20])
  exact h

theorem invEnv_eval (e : VG.Proof.X448.Arm.Env) : VG.Proof.X448.Arm.invEnv e 21 = Proof.X448.invert (e 2) := by
  simp only [↓reduceIte, VG.Proof.X448.Arm.invEnv, VG.Proof.X448.Arm.applyOps, FieldOp.apply, VG.Proof.X448.Arm.opMul, VG.Proof.X448.Arm.opCopy, VG.Proof.X448.Arm.opSqn,
    Function.update_apply]
  rfl

theorem invEnv_x2 (e : VG.Proof.X448.Arm.Env) : VG.Proof.X448.Arm.invEnv e 1 = e 1 := by
  simp (config := {decide := true}) only [VG.Proof.X448.Arm.invEnv, VG.Proof.X448.Arm.applyOps, FieldOp.apply, VG.Proof.X448.Arm.opMul, VG.Proof.X448.Arm.opCopy, VG.Proof.X448.Arm.opSqn,
    Function.update_apply, ite_true, ite_false]

theorem invert_ok {s : State} {base : Addr} (hs : VG.Proof.X448.Arm.Scr s base) (hb : VG.Proof.X448.Arm.BoundedEnv s.mem base) :
    WP isa Impl.X448.Arm.invert s fun t =>
      VG.Proof.X448.Arm.IKeep base s t ∧ VG.Proof.X448.Arm.BoundedEnv t.mem base ∧ VG.Proof.X448.Arm.E t.mem base = VG.Proof.X448.Arm.invEnv (VG.Proof.X448.Arm.E s.mem base) :=
  VG.Proof.X448.Arm.invert_spec base s hs hb

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Ladder`. -/
section

/-!
# X448 on ARMv7: all 448 ladder iterations

A decreasing public counter connects the loop to the specification's
descending fold over scalar bits.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (VG.Proof.X448.Arm.off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 448 → VG.Proof.X448.Arm.LInv base k u s₀ s n →
      WP isa (.loop VG.Impl.X448.Arm.step .ne) s fun s' => VG.Proof.X448.Arm.LInv base k u s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := VG.Impl.X448.Arm.step) (c := .ne)
    (Q := fun s' => VG.Proof.X448.Arm.LInv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 448 ∧ VG.Proof.X448.Arm.LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.X448.Arm.step_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

/-- The ladder: the counter set to 448, then the loop. -/
theorem ladder_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (VG.Proof.X448.Arm.off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : ∀ s', s'.gpr .r11 = BitVec.ofNat 32 448 → (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VG.Proof.X448.Arm.LInv base k u s₀ s' 448) :
    WP isa ladder s fun s' => VG.Proof.X448.Arm.LInv base k u s₀ s' 0 := by
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.setCounter_ok s 448 (by decide))
    fun s' ⟨h1, h2, h3, h4, h5⟩ => VG.Proof.X448.Arm.loop_ok hbits 448 s' (by omega) (by omega) (hi s' h1 h2 h3 h4 h5))

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Main`. -/
section

/-!
# X448 on ARMv7: the whole function

The contract the proof is written against (the facts of
`Spec.X448.x448Contract` it uses, stated for ARMv7), and the correctness of
`vg_x448` against it: every write is in the working space but the result's, so
the arguments are read unchanged, the callee-saved registers restored from the
working space, and the return address kept.
-/

namespace VG.Proof.X448

open VG VG.Arm in
/-- `vg_x448(out = r0, scalar = r1, point = r2, scratch = r3)`. -/
def x448Arm : Contract Arm.isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 56⟩
    let scalar : Region := ⟨State.addr (s.gpr .r1), 56⟩
    let point : Region := ⟨State.addr (s.gpr .r2), 56⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    s.rd = [scalar, point] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch ∧
      (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .r0).toNat + 56 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 56 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 56 ≤ 2 ^ 32
  post s s' := Spec.X448.bytesAt s'.mem (State.addr (s.gpr .r0)) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem (State.addr (s.gpr .r1)) 56)
      (Spec.X448.bytesAt s.mem (State.addr (s.gpr .r2)) 56)
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.sp = s₂.sp

end VG.Proof.X448

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448

section
variable (s₀ : State)
abbrev outR : Region := ⟨State.addr (s₀.gpr .r0), 56⟩
abbrev scalarR : Region := ⟨State.addr (s₀.gpr .r1), 56⟩
abbrev pointR : Region := ⟨State.addr (s₀.gpr .r2), 56⟩
abbrev scR : Region := ⟨State.addr (s₀.gpr .r3), 8192⟩
end

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.X448.Arm.scalarR s₀, VG.Proof.X448.Arm.pointR s₀]
  wr : s₀.wr = [VG.Proof.X448.Arm.outR s₀, VG.Proof.X448.Arm.scR s₀]
  out_sc : (VG.Proof.X448.Arm.outR s₀).Disjoint (VG.Proof.X448.Arm.scR s₀)
  scalar_sc : (VG.Proof.X448.Arm.scalarR s₀).Disjoint (VG.Proof.X448.Arm.scR s₀)
  point_sc : (VG.Proof.X448.Arm.pointR s₀).Disjoint (VG.Proof.X448.Arm.scR s₀)
  sc_fit : (s₀.gpr .r3).toNat + 8192 ≤ 2 ^ 32
  out_fit : (s₀.gpr .r0).toNat + 56 ≤ 2 ^ 32
  scalar_fit : (s₀.gpr .r1).toNat + 56 ≤ 2 ^ 32
  point_fit : (s₀.gpr .r2).toNat + 56 ≤ 2 ^ 32

theorem Pre.of (s₀ : State) (h : Proof.X448.x448Arm.pre s₀) : VG.Proof.X448.Arm.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ VG.Proof.X448.Arm.ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [VG.Proof.X448.Arm.ofs] at h; omega

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base 0 8192 m m')
    (hp : ∀ i < 56, 8192 ≤ VG.Proof.X448.Arm.ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X448.bytesAt m' p 56 = Spec.X448.bytesAt m p 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem far_output {base p : Addr} (hd : (⟨p, 56⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 56 ≤ VG.Proof.X448.Arm.ofs p (VG.Proof.X448.Arm.off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change VG.Proof.X448.Arm.ofs p (VG.Proof.X448.Arm.off base i) + 1 ≤ 56
  omega

theorem E_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base o n m m') (i : VG.Proof.X448.Arm.Index)
    (hi : slot i.val + 112 ≤ o ∨ o + n ≤ slot i.val) : VG.Proof.X448.Arm.E m' base i = VG.Proof.X448.Arm.E m base i := by
  simp only [VG.Proof.X448.Arm.E, VG.Proof.X448.Arm.F]
  rw [h.fe hi (by have := i.isLt; simp only [slot]; omega)]

theorem correct {s₀ : State} (hp : VG.Proof.X448.Arm.Pre s₀) :
    WP isa x448 s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.X448.x448Arm.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, State.addr (s₀.gpr .r3) = b := ⟨_, rfl⟩
  have hn := hp.sc_fit
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s₀.wr := by rw [hp.wr, ← hbase]; simp
  have hr : ∀ j < 56, InRegions (s₀.rd ++ s₀.wr) (VG.Proof.X448.Arm.off (State.addr (s₀.gpr .r2)) j) 1 := fun j hj =>
    ⟨VG.Proof.X448.Arm.pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hd : ∀ j < 56, 8192 ≤ VG.Proof.X448.Arm.ofs base (VG.Proof.X448.Arm.off (State.addr (s₀.gpr .r2)) j) :=
    fun j hj => VG.Proof.X448.Arm.far (hbase ▸ hp.point_sc) hj (by decide)
  have kd : ∀ j < 56, 8192 ≤ VG.Proof.X448.Arm.ofs base (VG.Proof.X448.Arm.off (State.addr (s₀.gpr .r1)) j) :=
    fun j hj => VG.Proof.X448.Arm.far (hbase ▸ hp.scalar_sc) hj (by decide)
  rw [x448]
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.setup_ok hbase hw₀ hn rfl hp.point_fit hr hd)
    fun s₁ ⟨hs₁, b₁, savedOut₁, k₁, o₁, sv₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  have kr : ∀ j < 56, InRegions (s₁.rd ++ s₁.wr) (VG.Proof.X448.Arm.off (State.addr (s₀.gpr .r1)) j) 1 := fun j hj =>
    ⟨VG.Proof.X448.Arm.scalarR s₀, by rw [k₁.2.1, hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.bits_ok (k := State.addr (s₀.gpr .r1)) hs₁ (by rw [k₁.1 _ (by decide)])
    (by rw [k₁.1 _ (by decide)]; exact hp.scalar_fit) kr kd)
    fun s₂ ⟨g₂, rd₂, wr₂, o₂, bits₂⟩ => ?_)
  have k₂ : VG.Proof.X448.Arm.Keeps VG.Proof.X448.Arm.bitRegs s₁ s₂ := ⟨g₂, rd₂, wr₂⟩
  have k02 := k₁.then k₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have sv₂ : VG.Proof.X448.Arm.Saved base s₀.gpr s₂.mem := by exact sv₁.outside o₂ (by decide)
  have e₂ : ∀ i : VG.Proof.X448.Arm.Index, VG.Proof.X448.Arm.E s₂.mem base i = VG.Proof.X448.Arm.E s₁.mem base i := by
    intro i; exact VG.Proof.X448.Arm.E_outside o₂ i (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
  have b₂ : VG.Proof.X448.Arm.BoundedEnv s₂.mem base := by
    intro i j hj
    rw [o₂.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) hj]
    exact b₁ i j hj
  have kb := VG.Proof.X448.Arm.bytesAt_outside o₁ kd
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.ladder_ok (s₀ := s₂) (s := s₂)
    (k := Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (State.addr (s₀.gpr .r1)) 56))
    (u := toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (State.addr (s₀.gpr .r2)) 56)))
    (fun t ht => by rw [bits₂ t ht, kb])
    (fun s' hb hg hm hr hw => ⟨
      ⟨by rw [hg _ (by decide)]; exact hs₂.r0, (hg _ (by decide)).trans hs₂.mask, hw ▸ hs₂.wr,
        by rw [hg _ (by decide)]; exact hs₂.nowrap⟩, hm ▸ b₂,
      ⟨fun r h => hg r (fun e => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
      hb, hm ▸ Outside2.refl _ _ _ _ _ _,
      by rw [hm, e₂ 0, x1₁], by rw [hm, e₂ 1, x2₁]; rfl,
      by rw [hm, e₂ 2, z2₁]; rfl, by rw [hm, e₂ 3, x3₁, x1₁]; rfl,
      by rw [hm, e₂ 4, z3₁]; rfl,
      by rw [hm, o₂.word (d := SWAP) (by decide) (by decide), sw₁]; rfl⟩)) fun s₄ L => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.lastSwap_ok L.scr L.bounded
    (by have := ladderAfter_swap_le
          (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (State.addr (s₀.gpr .r1)) 56))
          (toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (State.addr (s₀.gpr .r2)) 56)))
          (n := 0) (by decide); omega) L.swap) fun s₅ ⟨k₅, b₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr L.scr
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.invert_ok hs₅ b₅) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  have k26 := L.regs.then (k₅.regs.then k₆.regs)
  have sv₆ := ((sv₂.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have out₆ : s₆.gpr .r12 = s₀.gpr .r0 :=
    (k26.1 _ (by decide)).trans ((g₂ _ (by decide)).trans savedOut₁)
  have k06 := k02.then k26
  have hw₆ : ∀ j < 56, InRegions s₆.wr (VG.Proof.X448.Arm.off (State.addr (s₀.gpr .r0)) j) 1 := fun j hj =>
    ⟨VG.Proof.X448.Arm.outR s₀, by rw [k06.2.2, hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (VG.Proof.X448.Arm.finish_ok (k₆.scr hs₅) b₆ (congrArg State.addr out₆)
    (by rw [out₆]; exact hp.out_fit) hw₆
    (fun j hj => VG.Proof.X448.Arm.far_output (hbase ▸ hp.out_sc) hj) sv₆) fun s' ⟨restored, kf, fm, result⟩ => ?_
  have kall := k06.then kf
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact restored 0 (by decide)
    · exact restored 1 (by decide)
    · exact restored 2 (by decide)
    · exact restored 3 (by decide)
    · exact restored 4 (by decide)
    · exact restored 5 (by decide)
    · exact restored 6 (by decide)
    · exact restored 7 (by decide)
    · exact kall.1 _ (by decide)
  · change Spec.X448.bytesAt s'.mem (State.addr (s₀.gpr .r0)) 56 = _
    rw [result, x448_eq]
    apply congrArg Spec.X448.encodeUCoordinate
    rw [e₆, VG.Proof.X448.Arm.invEnv_x2, VG.Proof.X448.Arm.invEnv_eval, e₅]
    simp (config := {decide := true}) only [VG.Proof.X448.Arm.opSwap, Function.update_apply, ite_true, ite_false]
    rw [L.x2, L.x3, L.z2, L.z3, VG.Proof.X448.Arm.cswap_fst, VG.Proof.X448.Arm.cswap_fst]

end VG.Proof.X448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.Arm.Verified`. -/
section

/-!
# X448 on ARMv7: `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant or a counter),
satisfiability, and the shared contract of `Spec/`.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_ok (s : State) (hs : Proof.X448.x448Arm.pre s) :
    ∃ t s', Exec isa Impl.X448.Arm.x448 s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448Arm.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.X448.Arm.correct (Pre.of s hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he⟩, h.2⟩

theorem x448_ct : ConstantTime isa Proof.X448.x448Arm.pre Proof.X448.x448Arm.pub
    Impl.X448.Arm.x448 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, _⟩
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x448_verified :
    Verified Arm.target Impl.X448.Arm.x448 (Spec.X448.x448Contract Arm.abi) :=
  Verified.of_correct VG.Proof.X448.Arm.x448_ok VG.Proof.X448.Arm.x448_ct (by
    sig_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Proof.X448.x448Arm]
      [satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.X448.Arm.satState)

end VG.Proof.X448.Arm

end
