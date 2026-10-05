import VerifiedGarbage.Impl.X448.AArch64
import VerifiedGarbage.Proof.X448.Encoding
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Omega

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Mem`. -/
section

/-!
# X448 on AArch64: the working space

Field elements occupy sixteen words of the 8 KiB working space. `Outside`
tracks the bytes a block changes; `Keeps` tracks its registers and memory
permissions independently.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (VG.Proof.X448.AArch64.off base d) 64
abbrev limbs (m : Mem) (base : Addr) (o : Nat) (i : Nat) : Nat := (VG.Proof.X448.AArch64.word m base (o + 8 * i)).toNat
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat := VG.Proof.X448.valN (VG.Proof.X448.AArch64.limbs m base o) 16

def Bounded (m : Mem) (base : Addr) (o : Nat) : Prop := ∀ i < 16, VG.Proof.X448.AArch64.limbs m base o i < VG.Proof.X448.radix

/-- The registers and permissions that an arithmetic operation preserves. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.refl (rs : List Reg) (s : State) : VG.Proof.X448.AArch64.Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X448.AArch64.Keeps rs s₁ s₂) (h₂ : VG.Proof.X448.AArch64.Keeps rs s₂ s₃) :
    VG.Proof.X448.AArch64.Keeps rs s₁ s₃ := ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1,
      h₂.2.2.trans h₁.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.X448.AArch64.Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.X448.AArch64.Keeps rs' s s' := ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keeps.then {rs rs' : List Reg} {s t u : State} (h : VG.Proof.X448.AArch64.Keeps rs s t) (h' : VG.Proof.X448.AArch64.Keeps rs' t u) :
    VG.Proof.X448.AArch64.Keeps (rs ++ rs') s u :=
  (h.mono (fun _ hr => List.mem_append_left _ hr)).trans
    (h'.mono (fun _ hr => List.mem_append_right _ hr))

structure Scr (s : State) (base : Addr) : Prop where
  x3 : s.gpr .x3 = base
  mask : s.gpr .x12 = 0x0fffffff
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 8192 ≤ 2 ^ 64

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base)
    (h : VG.Proof.X448.AArch64.Keeps rs s s') (hr : .x3 ∉ rs ∧ .x12 ∉ rs) : VG.Proof.X448.AArch64.Scr s' base :=
  ⟨(h.1 _ hr.1).trans hs.x3, (h.1 _ hr.2).trans hs.mask, h.2.2 ▸ hs.wr, hs.nowrap⟩

theorem addr_word (s : State) (r : Reg) {d : Nat} (hd : d + 8 ≤ 8192) (ha : d % 8 = 0) :
    addr s 8 r d = some (VG.Proof.X448.AArch64.off (s.gpr r) d) := by
  rw [addr, ite_eq_left ⟨ha, by omega⟩]

theorem contains_sc {base : Addr} {d n : Nat} (h : d + n ≤ 8192) :
    (⟨base, 8192⟩ : Region).Contains (VG.Proof.X448.AArch64.off base d) n :=
  Offset.contains_base base h (by omega)

theorem Scr.read {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (VG.Proof.X448.AArch64.off base d) n :=
  ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X448.AArch64.contains_sc hd⟩

theorem Scr.write {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions s.wr (VG.Proof.X448.AArch64.off base d) n := ⟨_, hs.wr, VG.Proof.X448.AArch64.contains_sc hd⟩

theorem load_sc {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    s.load (VG.Proof.X448.AArch64.off base d) 8 = some (VG.Proof.X448.AArch64.word s.mem base d) := by
  rw [State.load, ite_eq_left (hs.read hd)]
  rfl

theorem read1_eq (m : Mem) (p : Addr) : m.read p 1 = m p := by
  change (0#0 ++ m p : BitVec (0 + 8)) = m p
  exact BitVec.zero_width_append _ _

theorem read8_eq (m : Mem) (p : Addr) : m.read p 8 = m.readW p 64 := by
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem write8_eq (m : Mem) (p : Addr) (v : BitVec 64) : m.write p 8 v = m.writeW p v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

abbrev ofs (base x : Addr) : Nat := (x - base).toNat

def Outside (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (VG.Proof.X448.AArch64.ofs base x < o ∨ o + n ≤ VG.Proof.X448.AArch64.ofs base x) → m' x = m x

theorem Outside.refl (base : Addr) (o n : Nat) (m : Mem) : VG.Proof.X448.AArch64.Outside base o n m m := fun _ _ => rfl

theorem Outside.trans {base : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.X448.AArch64.Outside base o n m₁ m₂)
    (h₂ : VG.Proof.X448.AArch64.Outside base o n m₂ m₃) : VG.Proof.X448.AArch64.Outside base o n m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Outside.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : VG.Proof.X448.AArch64.Outside base o n m m')
    (hl : o' ≤ o) (hr : o + n ≤ o' + n') : VG.Proof.X448.AArch64.Outside base o' n' m m' :=
  fun x hx => h x (by omega)

theorem ofs_off (base : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    VG.Proof.X448.AArch64.ofs base (VG.Proof.X448.AArch64.off base d + BitVec.ofNat 64 i) = d + i := by
  simp only [VG.Proof.X448.AArch64.ofs, VG.Proof.X448.AArch64.off]
  rw [Offset.add_add, Mem.sub_ofNat_toNat base h]

theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.AArch64.Outside base o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 ≤ 8192) : VG.Proof.X448.AArch64.word m' base d = VG.Proof.X448.AArch64.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.limbs {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.AArch64.Outside base o n m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + n ≤ d) (hd' : d + 128 ≤ 8192) {i : Nat} (hi : i < 16) :
    VG.Proof.X448.AArch64.limbs m' base d i = VG.Proof.X448.AArch64.limbs m base d i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega))

theorem Outside.fe {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.AArch64.Outside base o n m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + n ≤ d) (hd' : d + 128 ≤ 8192) : VG.Proof.X448.AArch64.fe m' base d = VG.Proof.X448.AArch64.fe m base d :=
  VG.Proof.X448.valN_congr fun _ hi => h.limbs hd hd' hi

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 ≤ 8192) :
    VG.Proof.X448.AArch64.Outside base d 8 m (m.writeW (VG.Proof.X448.AArch64.off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [VG.Proof.X448.AArch64.ofs] at hx
  omega

theorem word_write (m : Mem) (base : Addr) {o i j : Nat} (ho : o + 8 * (i + 1) ≤ 8192)
    (hj : o + 8 * (j + 1) ≤ 8192) (v : BitVec 64) :
    VG.Proof.X448.AArch64.word (m.writeW (VG.Proof.X448.AArch64.off base (o + 8 * i)) v) base (o + 8 * j) =
      if j = i then v else VG.Proof.X448.AArch64.word m base (o + 8 * j) := by
  by_cases h : j = i
  · rw [ite_eq_left h, h, VG.Proof.X448.AArch64.word, Mem.readW_writeW_self64]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- A field operation writes its result and its temporary coefficients. -/
def FieldMem (base : Addr) (o : Nat) (m m' : Mem) : Prop :=
  ∀ x, (VG.Proof.X448.AArch64.ofs base x < o ∨ o + 128 ≤ VG.Proof.X448.AArch64.ofs base x) →
    (VG.Proof.X448.AArch64.ofs base x < ACC ∨ ACC + 512 ≤ VG.Proof.X448.AArch64.ofs base x) → m' x = m x

theorem FieldMem.refl (base : Addr) (o : Nat) (m : Mem) : VG.Proof.X448.AArch64.FieldMem base o m m := fun _ _ _ => rfl

theorem FieldMem.trans {base : Addr} {o : Nat} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.X448.AArch64.FieldMem base o m₁ m₂)
    (h₂ : VG.Proof.X448.AArch64.FieldMem base o m₂ m₃) : VG.Proof.X448.AArch64.FieldMem base o m₁ m₃ :=
  fun x hx hw => (h₂ x hx hw).trans (h₁ x hx hw)

theorem FieldMem.output {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.AArch64.Outside base o 128 m m') :
    VG.Proof.X448.AArch64.FieldMem base o m m' := fun x hx _ => h x hx

theorem FieldMem.work {base : Addr} {o d n : Nat} {m m' : Mem} (h : VG.Proof.X448.AArch64.Outside base d n m m')
    (hl : ACC ≤ d) (hr : d + n ≤ ACC + 512) : VG.Proof.X448.AArch64.FieldMem base o m m' :=
  fun x _ hx => h.mono hl hr x hx

theorem FieldMem.word {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.AArch64.FieldMem base o m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + 128 ≤ d) (hw : d + 8 ≤ ACC) : VG.Proof.X448.AArch64.word m' base d = VG.Proof.X448.AArch64.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by simp only [ACC] at hw; omega)]; omega)
    (Or.inl (by rw [VG.Proof.X448.AArch64.ofs_off base (by simp only [ACC] at hw; omega)]; omega))).symm).symm

theorem FieldMem.limbs {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.AArch64.FieldMem base o m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + 128 ≤ d) (hw : d + 128 ≤ ACC) {i : Nat} (hi : i < 16) :
    VG.Proof.X448.AArch64.limbs m' base d i = VG.Proof.X448.AArch64.limbs m base d i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega))

theorem FieldMem.fe {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.AArch64.FieldMem base o m m') {d : Nat}
    (hd : d + 128 ≤ o ∨ o + 128 ≤ d) (hw : d + 128 ≤ ACC) : VG.Proof.X448.AArch64.fe m' base d = VG.Proof.X448.AArch64.fe m base d :=
  VG.Proof.X448.valN_congr fun _ hi => h.limbs hd hw hi

/-- Memory outside two ranges, used by the conditional swap. -/
def Outside2 (base : Addr) (x nx y ny : Nat) (m m' : Mem) : Prop :=
  ∀ p, (VG.Proof.X448.AArch64.ofs base p < x ∨ x + nx ≤ VG.Proof.X448.AArch64.ofs base p) →
    (VG.Proof.X448.AArch64.ofs base p < y ∨ y + ny ≤ VG.Proof.X448.AArch64.ofs base p) → m' p = m p

theorem Outside2.refl (base : Addr) (x nx y ny : Nat) (m : Mem) : VG.Proof.X448.AArch64.Outside2 base x nx y ny m m :=
  fun _ _ _ => rfl

theorem Outside2.trans {base : Addr} {x nx y ny : Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : VG.Proof.X448.AArch64.Outside2 base x nx y ny m₁ m₂) (h₂ : VG.Proof.X448.AArch64.Outside2 base x nx y ny m₂ m₃) :
    VG.Proof.X448.AArch64.Outside2 base x nx y ny m₁ m₃ := fun p hx hy => (h₂ p hx hy).trans (h₁ p hx hy)

theorem Outside2.mono {base : Addr} {x nx y ny nx' ny' : Nat} {m m' : Mem}
    (h : VG.Proof.X448.AArch64.Outside2 base x nx y ny m m') (hx : nx ≤ nx') (hy : ny ≤ ny') :
    VG.Proof.X448.AArch64.Outside2 base x nx' y ny' m m' := fun p hp hq => h p (by omega) (by omega)

theorem Outside2.word {base : Addr} {x nx y ny : Nat} {m m' : Mem} (h : VG.Proof.X448.AArch64.Outside2 base x nx y ny m m')
    {d : Nat} (hx : d + 8 ≤ x ∨ x + nx ≤ d) (hy : d + 8 ≤ y ∨ y + ny ≤ d) (hd : d + 8 ≤ 8192) :
    VG.Proof.X448.AArch64.word m' base d = VG.Proof.X448.AArch64.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)
    (by rw [VG.Proof.X448.AArch64.ofs_off base (by omega)]; omega)).symm).symm

/-- Aligned word stores read back as an update at one byte offset. -/
theorem word_write_aligned (m : Mem) (base : Addr) {d e : Nat} (hd : d + 8 ≤ 8192)
    (he : e + 8 ≤ 8192) (hdm : d % 8 = 0) (hem : e % 8 = 0) (v : BitVec 64) :
    VG.Proof.X448.AArch64.word (m.writeW (VG.Proof.X448.AArch64.off base d) v) base e = if e = d then v else VG.Proof.X448.AArch64.word m base e := by
  by_cases h : e = d
  · rw [ite_eq_left h, h, VG.Proof.X448.AArch64.word, Mem.readW_writeW_self64]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Init`. -/
section

/-!
# X448 on AArch64: initializing coefficient arrays

Zeroing a bounded range of words preserves all other memory and the registers.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem store_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) (hd8 : d % 8 = 0) (r : Reg) :
    WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.AArch64.off base d) (s.gpr r) ∧ VG.Proof.X448.AArch64.Keeps [] s t := by
  have enc : d % 8 = 0 ∧ d < 32768 := ⟨hd8, by omega⟩
  apply WP.of_runBlock
  simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    enc, and_self, hs.x3, State.store, State.read, BitVec.setWidth_eq,
    hs.write hd, ite_true, Option.bind_some, VG.Proof.X448.AArch64.write8_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl⟩

theorem zeroX4_ok (s : State) :
    WP isa (.block [.movz .x .x4 0 0]) s fun t =>
      t.gpr .x4 = 0 ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem fill_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o n : Nat} (ho : o + 8 * n ≤ 8192) (ho8 : o % 8 = 0)
    (hz : s.gpr .x4 = 0) :
    WP isa (.block ((List.range n).map (fun i => st .x4 (o + 8 * i)))) s fun t =>
      (∀ i < n, VG.Proof.X448.AArch64.limbs t.mem base o i = 0) ∧ VG.Proof.X448.AArch64.Outside base o (8 * n) s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [] s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, VG.Proof.X448.AArch64.limbs t.mem base o i = 0) ∧ VG.Proof.X448.AArch64.Outside base o (8 * n) s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [] s t
  have step : ∀ k t, k < n → inv k t →
      WP isa (.block [st .x4 (o + 8 * k)]) t (inv (k + 1)) := by
    intro k t hk ⟨tf, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (VG.Proof.X448.AArch64.store_ok ts (by omega) (by omega) .x4) fun u ⟨um, uk⟩ => ?_
    rw [tk.1 .x4 (by decide), hz] at um
    have out : VG.Proof.X448.AArch64.Outside base (o + 8 * k) 8 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (VG.Proof.X448.AArch64.word u.mem base (o + 8 * i)).toNat = _
    rw [um, VG.Proof.X448.AArch64.word_write t.mem base (by omega) (by omega)]
    by_cases h : i = k
    · rw [ite_eq_left h]; rfl
    · rw [ite_eq_right h]; exact tf i (by omega)
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) (N := n) inv step n (by omega) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- The row counter starts at zero and its pointer at the scratch base. -/
theorem counters_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) :
    WP isa (.block [.movz .x .x9 0 0, .addImm .x .x10 .x3 0]) s fun t =>
      t.gpr .x9 = 0 ∧ t.gpr .x10 = base ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x9, .x10] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero, BitVec.setWidth_eq,
    RegUpd.gpr_write, ite_false, reduceCtorEq, hs.x3, BitVec.add_zero,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem mulInit_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) :
    WP isa (.block (([.movz .x .x4 0 0] : List Instr) ++
      (List.range 32).map (fun i => st .x4 (ACC + 8 * i)) ++
      ([.movz .x .x9 0 0, .addImm .x .x10 .x3 0] : List Instr))) s fun t =>
      (∀ i < 32, VG.Proof.X448.AArch64.limbs t.mem base ACC i = 0) ∧ t.gpr .x9 = 0 ∧ t.gpr .x10 = base ∧
      VG.Proof.X448.AArch64.Outside base ACC 256 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x9, .x10] s t := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.zeroX4_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.fill_ok (hs.of_keeps tk (by decide)) (by decide : ACC + 8 * 32 ≤ 8192) (by decide) tz)
    fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.counters_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide)))
    fun v ⟨vc, vr, vm, vk⟩ => ?_
  refine ⟨?_, vc, vr, ?_, ?_⟩
  · intro i hi; rw [vm]; exact uf i hi
  · rw [vm, ← tm]; exact um
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; exact False.elim (List.not_mem_nil hr)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Step`. -/
section

/-!
# X448 on AArch64: arithmetic steps

Each short instruction block is executed once symbolically. Bounds exclude
overflow before interpreting machine words as natural numbers.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem and28 (x : BitVec 64) : (x &&& 0x0fffffff).toNat = x.toNat % VG.Proof.X448.radix := by
  rw [BitVec.toNat_and, show (0x0fffffff : BitVec 64).toNat = 2 ^ 28 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem shr28 (x : BitVec 64) : (x >>> 28).toNat = x.toNat / VG.Proof.X448.radix := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rfl

/-- A carry step writes the low 28 bits and retains the high bits in `x6`. -/
theorem carryStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o a i : Nat}
    (ho : o + 8 * i + 8 ≤ 8192) (ha : a + 8 * i + 8 ≤ 8192)
    (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hb : (VG.Proof.X448.AArch64.word s.mem base (a + 8 * i)).toNat + (s.gpr .x6).toNat < 2 ^ 64) :
    let v := (VG.Proof.X448.AArch64.word s.mem base (a + 8 * i)).toNat + (s.gpr .x6).toNat
    WP isa (.block (carryStep o a i)) s fun s' =>
      (s'.gpr .x6).toNat = v / VG.Proof.X448.radix ∧
      s'.mem = s.mem.writeW (VG.Proof.X448.AArch64.off base (o + 8 * i)) (BitVec.ofNat 64 (v % VG.Proof.X448.radix)) ∧
      VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5] s s' := by
  intro v
  have w := hs.write ho
  have l := hs.read ha
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 4096 * 8 := ⟨by omega, by omega⟩
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 4096 * 8 := ⟨by omega, by omega⟩
  apply WP.of_runBlock
  simp only [carryStep, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec,
    Size.bytes, Size.bits, addr, ae, oe, State.read, State.load, State.store, hs.x3, hs.mask, l, w,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write,
    BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    and_self, ite_true, ite_false, reduceCtorEq, Nat.reduceLT, Nat.reduceMul,
    VG.Proof.X448.AArch64.read8_eq, VG.Proof.X448.AArch64.write8_eq, Option.some.injEq, exists_eq_left']
  have hv : (VG.Proof.X448.AArch64.word s.mem base (a + 8 * i) + s.gpr .x6).toNat = v := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hb]
  refine ⟨?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [VG.Proof.X448.AArch64.shr28, hv]
  · apply congrArg (s.mem.writeW (VG.Proof.X448.AArch64.off base (o + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.X448.AArch64.and28, hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v % VG.Proof.X448.radix) (by
      have := Nat.mod_lt v (show 0 < VG.Proof.X448.radix by decide)
      have : VG.Proof.X448.radix < 2 ^ 64 := by decide
      omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- A bounded multiply-add is an ordinary natural-number multiply-add. -/
theorem mul_add_nat (a b c : BitVec 64) (h : a.toNat * b.toNat + c.toNat < 2 ^ 64) :
    (c + a * b).toNat = a.toNat * b.toNat + c.toNat := by
  have hp : a.toNat * b.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_mul, Nat.mod_eq_of_lt hp, Nat.add_comm c.toNat,
    Nat.mod_eq_of_lt h]

/-- One multiply-add updates exactly one coefficient. -/
theorem rowStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {b i j : Nat}
    (hb : b + 8 * j + 8 ≤ 8192) (hb8 : b % 8 = 0) (hi : i < 16) (hj : j < 16)
    (hr : s.gpr .x10 = VG.Proof.X448.AArch64.off base (8 * i))
    (hv : (VG.Proof.X448.AArch64.word s.mem base (b + 8 * j)).toNat * (s.gpr .x6).toNat +
      (VG.Proof.X448.AArch64.word s.mem base (ACC + 8 * (i + j))).toNat < 2 ^ 64) :
    let v := (VG.Proof.X448.AArch64.word s.mem base (b + 8 * j)).toNat * (s.gpr .x6).toNat +
      (VG.Proof.X448.AArch64.word s.mem base (ACC + 8 * (i + j))).toNat
    WP isa (.block (rowStep b j)) s fun s' =>
      s'.mem = s.mem.writeW (VG.Proof.X448.AArch64.off base (ACC + 8 * (i + j))) (BitVec.ofNat 64 v) ∧
      VG.Proof.X448.AArch64.Keeps [.x4, .x5] s s' := by
  intro v
  have hd : ACC + 8 * (i + j) + 8 ≤ 8192 := by simp only [ACC]; omega
  have l := hs.read hb
  have r := hs.read hd
  have w := hs.write hd
  have be : (b + 8 * j) % 8 = 0 ∧ b + 8 * j < 4096 * 8 := ⟨by omega, by omega⟩
  have ce : (ACC + 8 * j) % 8 = 0 ∧ ACC + 8 * j < 4096 * 8 := by
    simp only [ACC]; omega
  apply WP.of_runBlock
  simp only [rowStep, ld, runBlock_cons, runStep_some, runBlock_nil, exec,
    Size.bytes, Size.bits, addr, be, ce, State.read, State.load, State.store, hs.x3, hr,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, Option.map_some, Option.bind_some,
    VG.Proof.X448.AArch64.off, Offset.add_add, show 8 * i + (ACC + 8 * j) = ACC + 8 * (i + j) by omega,
    l, r, w, and_self, ite_true, ite_false, reduceCtorEq,
    VG.Proof.X448.AArch64.read8_eq, VG.Proof.X448.AArch64.write8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · apply congrArg (s.mem.writeW (VG.Proof.X448.AArch64.off base (ACC + 8 * (i + j))))
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.X448.AArch64.mul_add_nat _ _ _ hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Row`. -/
section

/-!
# X448 on AArch64: a row of multiplication

Sixteen multiply-adds update the coefficient array. Each coefficient is
visited once in a row, and the field operands are outside that array.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem rowBody_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {b i a : Nat}
    (hb : b + 128 ≤ ACC) (hb8 : b % 8 = 0) (hi : i < 16) (ha : a < VG.Proof.X448.radix)
    (hc : (s.gpr .x6).toNat = a) (hr : s.gpr .x10 = VG.Proof.X448.AArch64.off base (8 * i))
    {f g : Nat → Nat} (hf : ∀ k < 32, VG.Proof.X448.AArch64.limbs s.mem base ACC k = f k)
    (hg : ∀ k < 16, VG.Proof.X448.AArch64.limbs s.mem base b k = g k)
    (fb : ∀ k < 32, f k < 2 ^ 60) (gb : ∀ k < 16, g k < VG.Proof.X448.radix) :
    WP isa (.block ((List.range 16).flatMap (rowStep b))) s fun t =>
      (∀ k < 32, VG.Proof.X448.AArch64.limbs t.mem base ACC k = addRow f a g i 16 k) ∧
      VG.Proof.X448.AArch64.Outside base ACC 256 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t := by
  let inv := fun n (t : State) =>
    (∀ k < 32, VG.Proof.X448.AArch64.limbs t.mem base ACC k = addRow f a g i n k) ∧
    VG.Proof.X448.AArch64.Outside base ACC 256 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (rowStep b n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    have tc : (t.gpr .x6).toNat = a := by rw [tk.1 _ (by decide), hc]
    have tr : t.gpr .x10 = VG.Proof.X448.AArch64.off base (8 * i) := (tk.1 _ (by decide)).trans hr
    have tg : VG.Proof.X448.AArch64.limbs t.mem base b n = g n :=
      (tm.limbs (Or.inl hb) (Nat.le_trans hb (by decide)) hn).trans (hg n hn)
    have tv : VG.Proof.X448.AArch64.limbs t.mem base ACC (i + n) = f (i + n) := by
      rw [tf (i + n) (by omega), addRow_at, ite_eq_right (by omega), Nat.add_zero]
    have hp : g n * a < 2 ^ 56 := by
      have hm := Nat.mul_le_mul (Nat.le_of_lt (gb n hn)) (Nat.le_of_lt ha)
      have hb' : g n * a ≤ (VG.Proof.X448.radix - 1) * (VG.Proof.X448.radix - 1) := Nat.mul_le_mul (by have := gb n hn; omega) (by omega)
      have hpow : (VG.Proof.X448.radix - 1) * (VG.Proof.X448.radix - 1) < 2 ^ 56 := by decide
      exact Nat.lt_of_le_of_lt hb' hpow
    have sum : (VG.Proof.X448.AArch64.word t.mem base (b + 8 * n)).toNat * (t.gpr .x6).toNat +
        (VG.Proof.X448.AArch64.word t.mem base (ACC + 8 * (i + n))).toNat < 2 ^ 64 := by
      change VG.Proof.X448.AArch64.limbs t.mem base b n * (t.gpr .x6).toNat + VG.Proof.X448.AArch64.limbs t.mem base ACC (i + n) < _
      rw [tg, tc, tv]
      have := fb (i + n) (by omega)
      omega
    refine WP.mono (VG.Proof.X448.AArch64.rowStep_ok ts (by simp only [ACC] at hb; omega) hb8 hi hn tr sum)
      fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.AArch64.Outside base (ACC + 8 * (i + n)) 8 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.AArch64.writeW_outside _ _ _ (by simp only [ACC]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro k hk
    change (VG.Proof.X448.AArch64.word u.mem base (ACC + 8 * k)).toNat = _
    rw [um, VG.Proof.X448.AArch64.word_write t.mem base (by simp only [ACC]; omega) (by simp only [ACC]; omega)]
    by_cases he : k = i + n
    · rw [ite_eq_left he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt sum]
      change VG.Proof.X448.AArch64.limbs t.mem base b n * (t.gpr .x6).toNat + VG.Proof.X448.AArch64.limbs t.mem base ACC (i + n) = _
      rw [tg, tc, ← he, tf k hk, addRow, addAt, ite_eq_left he, Nat.mul_comm (g n), Nat.add_comm]
    · rw [ite_eq_right he]
      change VG.Proof.X448.AArch64.limbs t.mem base ACC k = _
      rw [tf k hk, addRow, addAt, ite_eq_right he]
  exact wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s
    ⟨hf, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- Load the current row's multiplier through its public pointer. -/
theorem rowHead_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {a i : Nat}
    (ha : a + 128 ≤ ACC) (ha8 : a % 8 = 0) (hi : i < 16)
    (hr : s.gpr .x10 = VG.Proof.X448.AArch64.off base (8 * i)) :
    WP isa (.block (rowHead a)) s fun t =>
      t.gpr .x6 = VG.Proof.X448.AArch64.word s.mem base (a + 8 * i) ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x6] s t := by
  have enc : a % 8 = 0 ∧ a < 32768 := ⟨ha8, by simp only [ACC] at ha; omega⟩
  have l := hs.read (d := a + 8 * i) (n := 8) (by simp only [ACC] at ha; omega)
  apply WP.of_runBlock
  simp only [rowHead, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    enc, and_self, hr, VG.Proof.X448.AArch64.off, Offset.add_add, Nat.add_comm (8 * i), State.load, l,
    ite_true, Option.map_some, Option.bind_some, BitVec.setWidth_eq,
    VG.Proof.X448.AArch64.read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq]
  · simp only [List.mem_singleton] at hr
    exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- Advance the row index and form the loop condition. -/
theorem rowTail_ok {s : State} {base : Addr} {i : Nat} (hi : i < 16)
    (hc : s.gpr .x9 = BitVec.ofNat 64 i) (hr : s.gpr .x10 = VG.Proof.X448.AArch64.off base (8 * i)) :
    WP isa (.block rowTail) s fun t =>
      t.gpr .x9 = BitVec.ofNat 64 (i + 1) ∧ t.gpr .x10 = VG.Proof.X448.AArch64.off base (8 * (i + 1)) ∧
      (t.gpr .x11 == 0) = decide (i + 1 = 16) ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x9, .x10, .x11] s t := by
  have eq : ((BitVec.ofNat 64 i + BitVec.ofNat 64 1 - BitVec.ofNat 64 16) == 0) = decide (i + 1 = 16) := by
    have check : ∀ n < 16,
        ((BitVec.ofNat 64 n + BitVec.ofNat 64 1 - BitVec.ofNat 64 16) == 0) = decide (n + 1 = 16) :=
      by decide +kernel
    exact check i hi
  apply WP.of_runBlock
  simp only [rowTail, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceLT, RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false,
    reduceCtorEq, hc, hr, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, eq, rfl, (fun r hr => ?_), rfl, rfl⟩
  · exact (BitVec.ofNat_add _ _).symm
  · rw [VG.Proof.X448.AArch64.off, Offset.add_add]; congr 2
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

/-- One loop iteration, including the public row counter. -/
theorem row_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {a b i : Nat}
    (ha : a + 128 ≤ ACC) (ha8 : a % 8 = 0) (hb : b + 128 ≤ ACC) (hb8 : b % 8 = 0) (hi : i < 16)
    (hc : s.gpr .x9 = BitVec.ofNat 64 i) (hr : s.gpr .x10 = VG.Proof.X448.AArch64.off base (8 * i))
    {f g : Nat → Nat} (hf : ∀ k < 32, VG.Proof.X448.AArch64.limbs s.mem base ACC k = f k)
    (hg : ∀ k < 16, VG.Proof.X448.AArch64.limbs s.mem base b k = g k)
    (fb : ∀ k < 32, f k < 2 ^ 60) (gb : ∀ k < 16, g k < VG.Proof.X448.radix)
    (ab : VG.Proof.X448.AArch64.limbs s.mem base a i < VG.Proof.X448.radix) :
    WP isa (.block (row a b)) s fun t =>
      (∀ k < 32, VG.Proof.X448.AArch64.limbs t.mem base ACC k = addRow f (VG.Proof.X448.AArch64.limbs s.mem base a i) g i 16 k) ∧
      t.gpr .x9 = BitVec.ofNat 64 (i + 1) ∧ t.gpr .x10 = VG.Proof.X448.AArch64.off base (8 * (i + 1)) ∧
      (t.gpr .x11 == 0) = decide (i + 1 = 16) ∧ VG.Proof.X448.AArch64.Outside base ACC 256 s.mem t.mem ∧
      VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5, .x9, .x10, .x11] s t := by
  rw [row, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.rowHead_ok hs ha ha8 hi hr) fun t ⟨tc, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.rowBody_ok (hs.of_keeps tk (by decide)) hb hb8 hi ab
    (by rw [tc]) ((tk.1 _ (by decide)).trans hr)
    (by intro k hk; rw [tm]; exact hf k hk)
    (by intro k hk; rw [tm]; exact hg k hk) fb gb) fun u ⟨uf, um, uk⟩ => ?_
  have uc : u.gpr .x9 = BitVec.ofNat 64 i :=
    (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hc)
  have ur : u.gpr .x10 = VG.Proof.X448.AArch64.off base (8 * i) :=
    (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hr)
  refine WP.mono (VG.Proof.X448.AArch64.rowTail_ok hi uc ur) fun v ⟨vc, vr, vz, vm, vk⟩ => ?_
  refine ⟨?_, vc, vr, vz, ?_, ?_⟩
  · intro k hk; rw [vm]; exact uf k hk
  · rw [vm, ← tm]; exact um
  · have k₁ : VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5, .x9, .x10, .x11] s t := tk.mono (by
      intro r h
      simp only [List.mem_singleton] at h
      subst r
      decide)
    have k₂ : VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5, .x9, .x10, .x11] t u := uk.mono (by
      intro r h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> decide)
    have k₃ : VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5, .x9, .x10, .x11] u v := vk.mono (by
      intro r h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> decide)
    exact k₁.trans (k₂.trans k₃)

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.MulLoop`. -/
section

/-!
# X448 on AArch64: multiplication loop

The invariant relates the 32 coefficients to the rows already accumulated,
retaining the two input field elements throughout the loop.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem mulLoop_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {a b : Nat}
    (ha : a + 128 ≤ ACC) (ha8 : a % 8 = 0) (hb : b + 128 ≤ ACC) (hb8 : b % 8 = 0)
    {f g : Nat → Nat} (hf : ∀ k < 16, VG.Proof.X448.AArch64.limbs s.mem base a k = f k)
    (hg : ∀ k < 16, VG.Proof.X448.AArch64.limbs s.mem base b k = g k)
    (fb : ∀ k < 16, f k < VG.Proof.X448.radix) (gb : ∀ k < 16, g k < VG.Proof.X448.radix)
    (hz : ∀ k < 32, VG.Proof.X448.AArch64.limbs s.mem base ACC k = 0)
    (hc : s.gpr .x9 = 0) (hr : s.gpr .x10 = base) :
    WP isa (.loop (.block (row a b)) (.nonzero .x .x11)) s fun t =>
      (∀ k < 32, VG.Proof.X448.AArch64.limbs t.mem base ACC k = rows f g 16 k) ∧
      VG.Proof.X448.AArch64.Outside base ACC 256 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5, .x9, .x10, .x11] s t := by
  let inv := fun n (t : State) => 1 ≤ n ∧ n ≤ 16 ∧
    (∀ k < 32, VG.Proof.X448.AArch64.limbs t.mem base ACC k = rows f g (16 - n) k) ∧
    t.gpr .x9 = BitVec.ofNat 64 (16 - n) ∧ t.gpr .x10 = VG.Proof.X448.AArch64.off base (8 * (16 - n)) ∧
    VG.Proof.X448.AArch64.Outside base ACC 256 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5, .x9, .x10, .x11] s t
  refine WP.loop (M := isa) inv ?_ 16 s ?_
  · intro n t ⟨hn, hn', tf, tc, tr, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    have ft : ∀ k < 16, VG.Proof.X448.AArch64.limbs t.mem base a k = f k := fun k hk =>
      (tm.limbs (Or.inl ha) (Nat.le_trans ha (by decide)) hk).trans (hf k hk)
    have gt : ∀ k < 16, VG.Proof.X448.AArch64.limbs t.mem base b k = g k := fun k hk =>
      (tm.limbs (Or.inl hb) (Nat.le_trans hb (by decide)) hk).trans (hg k hk)
    have bound : ∀ k < 32, rows f g (16 - n) k < 2 ^ 60 := by
      intro k _
      have h1 := rows_bound fb gb (n := 16 - n) (by omega) k
      have h2 := Nat.mul_le_mul_right ((VG.Proof.X448.radix - 1) ^ 2) (show 16 - n ≤ 16 by omega)
      have h3 : 16 * (VG.Proof.X448.radix - 1) ^ 2 < 2 ^ 60 := by decide
      omega
    refine WP.mono (VG.Proof.X448.AArch64.row_ok ts ha ha8 hb hb8 (by omega) tc tr tf gt bound gb
      (by rw [ft (16 - n) (by omega)]; exact fb _ (by omega))) fun u ⟨uf, uc, ur, uz, um, uk⟩ => ?_
    have uf' : ∀ k < 32, VG.Proof.X448.AArch64.limbs u.mem base ACC k = rows f g (16 - n + 1) k := by
      intro k hk
      rw [uf k hk, ft (16 - n) (by omega)]
      rfl
    have mem := tm.trans um
    have keep := tk.trans uk
    simp only [eval, State.read, BitVec.setWidth_eq, bne, uz]
    by_cases hn1 : n = 1
    · subst n
      exact Or.inl ⟨rfl, uf', mem, keep⟩
    · refine Or.inr ⟨?_, n - 1, by omega, by omega, by omega, ?_, ?_, ?_, mem, keep⟩
      · rw [decide_eq_false (by omega : ¬16 - n + 1 = 16)]; rfl
      · rw [show 16 - (n - 1) = 16 - n + 1 by omega]; exact uf'
      · rw [show 16 - (n - 1) = 16 - n + 1 by omega]; exact uc
      · rw [show 16 - (n - 1) = 16 - n + 1 by omega]; exact ur
  · refine ⟨by decide, by decide, hz, ?_, ?_, Outside.refl _ _ _ _, Keeps.refl _ _⟩
    · exact hc
    · simpa only [Nat.sub_self, Nat.mul_zero, VG.Proof.X448.AArch64.off, BitVec.add_zero] using hr

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Carry`. -/
section

/-!
# X448 on AArch64: carry propagation

The sixteen machine steps implement `digit` and `carry`; the inputs may be
normalized in place.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem zeroCarry_ok (s : State) :
    WP isa (.block [.movz .x .x6 0 0]) s fun s' =>
      s'.gpr .x6 = 0 ∧ s'.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero, BitVec.setWidth_eq,
    RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.2.1, ite_false]

/-- An in-place pass only overwrites input limbs it has already consumed. -/
theorem pass_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o a : Nat}
    (ho : o + 128 ≤ 8192) (ha : a + 128 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hsep : o = a ∨ o + 128 ≤ a ∨ a + 128 ≤ o)
    {f : Nat → Nat} (hf : ∀ i < 16, VG.Proof.X448.AArch64.limbs s.mem base a i = f i)
    (hb : ∀ i < 16, f i < 2 ^ 62) :
    WP isa (.block (pass o a)) s fun s' =>
      (∀ i < 16, VG.Proof.X448.AArch64.limbs s'.mem base o i = VG.Proof.X448.digit f i) ∧
      (s'.gpr .x6).toNat = VG.Proof.X448.carry f 16 ∧ VG.Proof.X448.AArch64.Outside base o 128 s.mem s'.mem ∧
      VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5] s s' := by
  let inv := fun k (t : State) =>
    (∀ i < k, VG.Proof.X448.AArch64.limbs t.mem base o i = VG.Proof.X448.digit f i) ∧
    (∀ i, k ≤ i → i < 16 → VG.Proof.X448.AArch64.limbs t.mem base a i = f i) ∧
    (t.gpr .x6).toNat = VG.Proof.X448.carry f k ∧ VG.Proof.X448.AArch64.Outside base o 128 s.mem t.mem ∧
    VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5] s t
  have step : ∀ k t, k < 16 → inv k t → WP isa (.block (carryStep o a k)) t (inv (k + 1)) := by
    intro k t hk ⟨hlo, hhi, hc, hm, ht⟩
    have hts := hs.of_keeps ht (by decide)
    have he := hhi k (by omega) hk
    have hsum : (VG.Proof.X448.AArch64.word t.mem base (a + 8 * k)).toNat + (t.gpr .x6).toNat < 2 ^ 64 := by
      change VG.Proof.X448.AArch64.limbs t.mem base a k + (t.gpr .x6).toNat < _
      rw [he, hc]
      have := hb k hk
      have := VG.Proof.X448.carry_bound (n := k) (fun i hi => hb i (by omega))
      omega
    refine WP.mono (VG.Proof.X448.AArch64.carryStep_ok hts (by omega) (by omega) ho8 ha8 hsum) fun u ⟨hu, hmem, huKeep⟩ => ?_
    have he' : (VG.Proof.X448.AArch64.word t.mem base (a + 8 * k)).toNat + (t.gpr .x6).toNat = f k + VG.Proof.X448.carry f k := by
      change VG.Proof.X448.AArch64.limbs t.mem base a k + (t.gpr .x6).toNat = _
      rw [he, hc]
    rw [he'] at hu hmem
    have out : VG.Proof.X448.AArch64.Outside base (o + 8 * k) 8 t.mem u.mem := by
      rw [hmem]
      exact VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, hu, hm.trans (out.mono (by omega) (by omega)), ht.trans huKeep⟩
    · intro i hi
      change (VG.Proof.X448.AArch64.word u.mem base (o + 8 * i)).toNat = _
      rw [hmem, VG.Proof.X448.AArch64.word_write t.mem base (by omega) (by omega)]
      by_cases hik : i = k
      · rw [ite_eq_left hik, hik, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (f k + VG.Proof.X448.carry f k) % VG.Proof.X448.radix)
          (Nat.lt_trans (VG.Proof.X448.digit_lt f k) (by decide))]
        rfl
      · rw [ite_eq_right hik]
        exact hlo i (by omega)
    · intro i hi hi'
      have sep : a + 8 * i + 8 ≤ o + 8 * k ∨ o + 8 * k + 8 ≤ a + 8 * i := by
        rcases hsep with h | h | h <;> omega
      change (VG.Proof.X448.AArch64.word u.mem base (a + 8 * i)).toNat = _
      rw [out.word sep (by omega)]
      exact hhi i (by omega) hi'
  change WP isa (.block ([.movz .x .x6 0 0] ++ (List.range 16).flatMap (carryStep o a))) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.zeroCarry_ok s) fun t ⟨hc, hm, ht⟩ => ?_
  refine WP.mono (wp_range_flatMap inv step 16 (by decide) t ?_) fun u ⟨hlo, _, hc, hm, ht⟩ =>
    ⟨hlo, hc, hm, ht⟩
  refine ⟨fun i hi => by omega, (fun i _ hi => ?_), ?_, ?_, ht⟩
  · rw [hm]; exact hf i hi
  · rw [hc]; rfl
  · rw [hm]; exact Outside.refl _ _ _ _

/-- Fold the carry into one word, preserving `x6` for the other fold. -/
theorem foldStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {d : Nat}
    (hd : d + 8 ≤ 8192) (hd8 : d % 8 = 0) :
    WP isa (.block [ld .x4 d, .add .x .x4 .x4 .x6, st .x4 d]) s
      fun s' => s'.mem = s.mem.writeW (VG.Proof.X448.AArch64.off base d) (VG.Proof.X448.AArch64.word s.mem base d + s.gpr .x6) ∧
        VG.Proof.X448.AArch64.Keeps [.x4] s s' := by
  have l := hs.read hd
  have w := hs.write hd
  have enc : d % 8 = 0 ∧ d < 32768 := ⟨hd8, by omega⟩
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bytes,
    Size.bits, addr, enc, State.read, State.load, State.store, hs.x3, l, w,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, BitVec.setWidth_eq,
    VG.Proof.X448.AArch64.read8_eq, VG.Proof.X448.AArch64.write8_eq, Option.bind_some, Option.map_some, and_self, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem foldLimb_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {k : Nat} (hk : k < 16)
    (hb : VG.Proof.X448.AArch64.limbs s.mem base TMP k + (s.gpr .x6).toNat < 2 ^ 64) :
    WP isa (.block [ld .x4 (TMP + 8 * k), .add .x .x4 .x4 .x6,
      st .x4 (TMP + 8 * k)]) s fun t =>
      (∀ i < 16, VG.Proof.X448.AArch64.limbs t.mem base TMP i =
        if i = k then VG.Proof.X448.AArch64.limbs s.mem base TMP i + (s.gpr .x6).toNat else VG.Proof.X448.AArch64.limbs s.mem base TMP i) ∧
      VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4] s t := by
  have hd : TMP + 8 * k + 8 ≤ 8192 := by simp only [TMP]; omega
  refine WP.mono (VG.Proof.X448.AArch64.foldStep_ok hs hd (by simp only [TMP]; omega)) fun t ⟨hm, ht⟩ => ?_
  refine ⟨?_, ?_, ht⟩
  · intro i hi
    change (VG.Proof.X448.AArch64.word t.mem base (TMP + 8 * i)).toNat = _
    rw [hm, VG.Proof.X448.AArch64.word_write s.mem base (by omega) (by simp only [TMP]; omega)]
    by_cases h : i = k
    · rw [ite_eq_left h, ite_eq_left h, h, BitVec.toNat_add, Nat.mod_eq_of_lt hb]
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [hm]
    exact (VG.Proof.X448.AArch64.writeW_outside _ _ _ hd).mono (by omega) (by omega)

/-- The two stores implement the mathematical carry fold. -/
theorem fold_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 16, VG.Proof.X448.AArch64.limbs s.mem base TMP i = VG.Proof.X448.digit f i)
    (hc : (s.gpr .x6).toNat = VG.Proof.X448.carry f 16) (hb : VG.Proof.X448.carry f 16 < 2 ^ 35) :
    WP isa (.block fold) s fun s' =>
      (∀ i < 16, VG.Proof.X448.AArch64.limbs s'.mem base TMP i = VG.Proof.X448.folded f i) ∧
      VG.Proof.X448.AArch64.Outside base TMP 128 s.mem s'.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4] s s' := by
  have bound : ∀ i < 16, VG.Proof.X448.digit f i + VG.Proof.X448.carry f 16 < 2 ^ 64 := by
    intro i _
    have h := VG.Proof.X448.digit_lt f i
    simp only [VG.Proof.X448.radix] at h
    omega
  change WP isa (.block
    (([ld .x4 (TMP + 8 * 0), .add .x .x4 .x4 .x6,
       st .x4 (TMP + 8 * 0)] : List Instr) ++
     [ld .x4 (TMP + 8 * 8), .add .x .x4 .x4 .x6,
       st .x4 (TMP + 8 * 8)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.foldLimb_ok hs (k := 0) (by decide) (by rw [hf 0 (by decide), hc]; exact bound 0 (by decide)))
    fun t ⟨htf, htm, ht⟩ => ?_
  have htc : (t.gpr .x6).toNat = VG.Proof.X448.carry f 16 := by rw [ht.1 _ (by decide), hc]
  refine WP.mono (VG.Proof.X448.AArch64.foldLimb_ok (hs.of_keeps ht (by decide)) (k := 8) (by decide) ?_)
    fun u ⟨huf, hum, hu⟩ => ?_
  · rw [htf 8 (by decide), ite_eq_right (by decide), hf 8 (by decide), htc]
    exact bound 8 (by decide)
  · refine ⟨?_, htm.trans hum, ht.trans hu⟩
    intro i hi
    rw [huf i hi, htf i hi, hf i hi, hc, htc]
    simp only [VG.Proof.X448.folded]
    by_cases h0 : i = 0
    · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
    · by_cases h8 : i = 8
      · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
      · simp only [h0, h8, ite_false, false_or, Nat.add_zero]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Normalize`. -/
section

/-!
# X448 on AArch64: modular reduction

Three carry passes and two folds normalize coefficients bounded by 2⁶²,
preserving their value modulo p.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- Normalize the coefficients at `TMP` into a field-element slot. -/
theorem normalize_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 16, VG.Proof.X448.AArch64.limbs s.mem base TMP i = f i) (hb : ∀ i < 16, f i < 2 ^ 62) :
    WP isa (.block (normalize o)) s fun t =>
      (∀ i < 16, VG.Proof.X448.AArch64.limbs t.mem base o i = VG.Proof.X448.normalized f i) ∧
      VG.Proof.X448.AArch64.FieldMem base o s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5] s t := by
  have htmp : TMP + 128 ≤ 8192 := by decide
  have hwork : ∀ {m m' : Mem}, VG.Proof.X448.AArch64.Outside base TMP 128 m m' → VG.Proof.X448.AArch64.FieldMem base o m m' :=
    fun h => FieldMem.work h (by decide) (by decide)
  have keep : ∀ {a b : State}, VG.Proof.X448.AArch64.Keeps [.x4] a b → VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5] a b :=
    fun h => h.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; decide)
  rw [normalize, show pass TMP TMP ++ fold ++ pass TMP TMP ++ fold ++ pass o TMP =
    pass TMP TMP ++ (fold ++ (pass TMP TMP ++ (fold ++ pass o TMP))) by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.pass_ok hs htmp htmp (by decide) (by decide) (Or.inl rfl) hf hb) fun s₁ ⟨f₁, c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.fold_ok hs₁ f₁ c₁ (VG.Proof.X448.carry_bound hb)) fun s₂ ⟨f₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.pass_ok hs₂ htmp htmp (by decide) (by decide) (Or.inl rfl) f₂ (VG.Proof.X448.folded_bound hb)) fun s₃ ⟨f₃, c₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.fold_ok hs₃ f₃ c₃ (VG.Proof.X448.carry_bound (VG.Proof.X448.folded_bound hb))) fun s₄ ⟨f₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have ho' : o + 128 ≤ TMP := Nat.le_trans ho (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.pass_ok hs₄ (Nat.le_trans ho (by decide)) htmp ho8 (by decide) (Or.inr (Or.inl ho')) f₄
    (VG.Proof.X448.folded_bound (VG.Proof.X448.folded_bound hb))) fun s₅ ⟨f₅, _, m₅, k₅⟩ => ?_
  exact ⟨f₅, (hwork m₁).trans ((hwork m₂).trans ((hwork m₃).trans ((hwork m₄).trans (.output m₅)))),
    k₁.trans ((keep k₂).trans (k₃.trans ((keep k₄).trans k₅)))⟩

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Reduce`. -/
section

/-!
# X448 on AArch64: reducing product coefficients

Coefficients 16–31 fold into the lower sixteen according to the relation 2⁴⁴⁸ =
2²²⁴ + 1 modulo p.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem reduceCol_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {k : Nat} (hk : k < 16)
    {f : Nat → Nat} (hf : ∀ i < 32, VG.Proof.X448.AArch64.limbs s.mem base ACC i = f i)
    (hb : ∀ i < 32, f i < 2 ^ 60) :
    WP isa (.block (reduceCol k)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.AArch64.off base (TMP + 8 * k)) (BitVec.ofNat 64 (VG.Proof.X448.reduced f k)) ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t := by
  have l : ∀ i < 32, InRegions (s.rd ++ s.wr) (VG.Proof.X448.AArch64.off base (ACC + 8 * i)) 8 :=
    fun i hi => hs.read (by simp only [ACC]; omega)
  have enc : ∀ i < 32, (ACC + 8 * i) % 8 = 0 ∧ ACC + 8 * i < 32768 := by
    intro i hi; simp only [ACC]; omega
  have outEnc : (TMP + 8 * k) % 8 = 0 ∧ TMP + 8 * k < 32768 := by
    simp only [TMP]; omega
  have w := hs.write (d := TMP + 8 * k) (n := 8) (by simp only [TMP]; omega)
  have f0 := hf k (by omega)
  have f1 := hf (k + 16) (by omega)
  have f2 := hf (k + 8) (by omega)
  have b0 := hb k (by omega)
  have b1 := hb (k + 16) (by omega)
  have b2 := hb (k + 8) (by omega)
  by_cases h : k < 8
  · have f3 := hf (k + 24) (by omega)
    have b3 := hb (k + 24) (by omega)
    apply WP.of_runBlock
    simp only [reduceCol, h, ite_true, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec, ld, st, Size.bytes, addr, State.load, State.store,
      State.read, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.mem_write,
      RegUpd.rd_write, RegUpd.wr_write, hs.x3, and_self, VG.Proof.X448.AArch64.read8_eq, VG.Proof.X448.AArch64.write8_eq,
      enc k (by omega), enc (k + 16) (by omega), outEnc,
      l k (by omega), l (k + 16) (by omega), l (k + 24) (by omega), enc (k + 24) (by omega), w,
      Option.map_some, Option.bind_some, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
    refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
    · apply congrArg (s.mem.writeW (VG.Proof.X448.AArch64.off base (TMP + 8 * k)))
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, VG.Proof.X448.reduced, h, ite_true]
      change ((VG.Proof.X448.AArch64.limbs s.mem base ACC k + VG.Proof.X448.AArch64.limbs s.mem base ACC (k + 16)) % 2 ^ 64 +
        VG.Proof.X448.AArch64.limbs s.mem base ACC (k + 24)) % 2 ^ 64 = (f k + f (k + 16) + f (k + 24)) % 2 ^ 64
      rw [f0, f1, f3, Nat.mod_eq_of_lt (show f k + f (k + 16) < 2 ^ 64 by omega)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  · apply WP.of_runBlock
    simp only [reduceCol, h, ite_false, List.cons_append, List.nil_append, runBlock_cons,
      runStep_some, runBlock_nil, exec, ld, st, Size.bytes, addr, State.load, State.store,
      State.read, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.mem_write,
      RegUpd.rd_write, RegUpd.wr_write, hs.x3, and_self, VG.Proof.X448.AArch64.read8_eq, VG.Proof.X448.AArch64.write8_eq,
      enc k (by omega), enc (k + 16) (by omega), outEnc,
      l k (by omega), l (k + 16) (by omega), l (k + 8) (by omega), enc (k + 8) (by omega), w,
      Option.map_some, Option.bind_some, reduceCtorEq, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
    · apply congrArg (s.mem.writeW (VG.Proof.X448.AArch64.off base (TMP + 8 * k)))
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, VG.Proof.X448.reduced, h, ite_false]
      change (((VG.Proof.X448.AArch64.limbs s.mem base ACC k + VG.Proof.X448.AArch64.limbs s.mem base ACC (k + 16)) % 2 ^ 64 +
        VG.Proof.X448.AArch64.limbs s.mem base ACC (k + 8)) % 2 ^ 64 + VG.Proof.X448.AArch64.limbs s.mem base ACC (k + 16)) % 2 ^ 64 =
        (f k + f (k + 16) + (f (k + 8) + f (k + 16))) % 2 ^ 64
      rw [f0, f1, f2, Nat.mod_eq_of_lt (show f k + f (k + 16) < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show f k + f (k + 16) + f (k + 8) < 2 ^ 64 by omega), Nat.add_assoc]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- Fold all thirty-two coefficients into sixteen, ready for carries. -/
theorem reduce_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 32, VG.Proof.X448.AArch64.limbs s.mem base ACC i = f i) (hb : ∀ i < 32, f i < 2 ^ 60) :
    WP isa (.block ((List.range 16).flatMap reduceCol)) s fun t =>
      (∀ i < 16, VG.Proof.X448.AArch64.limbs t.mem base TMP i = VG.Proof.X448.reduced f i) ∧
      VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.AArch64.limbs t.mem base TMP i = VG.Proof.X448.reduced f i) ∧
    VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t
  have step : ∀ n t, n < 16 → inv n t → WP isa (.block (reduceCol n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have ft : ∀ i < 32, VG.Proof.X448.AArch64.limbs t.mem base ACC i = f i := by
      intro i hi
      change (VG.Proof.X448.AArch64.word t.mem base (ACC + 8 * i)).toNat = _
      rw [tm.word (Or.inl (by simp only [ACC, TMP]; omega)) (by simp only [ACC]; omega)]
      exact hf i hi
    refine WP.mono (VG.Proof.X448.AArch64.reduceCol_ok (hs.of_keeps tk (by decide)) hn ft hb) fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.AArch64.Outside base (TMP + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.AArch64.writeW_outside _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (VG.Proof.X448.AArch64.word u.mem base (TMP + 8 * i)).toNat = _
    rw [um, VG.Proof.X448.AArch64.word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (VG.Proof.X448.reduced_bound hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Mul`. -/
section

/-!
# X448 on AArch64: field multiplication

The row loop, coefficient folds and carry passes together compute
multiplication modulo the field prime, with bounded output limbs. Either input
may also be the output.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := VG.Proof.X448.toFe (VG.Proof.X448.AArch64.fe m base o)

def clob : List Reg := [.x4, .x6, .x5, .x9, .x10, .x11, .x7, .x8, .x13, .x14, .x15, .x16]

structure Op (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : VG.Proof.X448.AArch64.Keeps VG.Proof.X448.AArch64.clob s t
  mem : VG.Proof.X448.AArch64.FieldMem base o s.mem t.mem

theorem Op.scr {base : Addr} {o : Nat} {s t : State} (h : VG.Proof.X448.AArch64.Op base o s t) (hs : VG.Proof.X448.AArch64.Scr s base) :
    VG.Proof.X448.AArch64.Scr t base := hs.of_keeps h.keeps (by decide)

abbrev Slot (o : Nat) : Prop := o + 128 ≤ ACC

theorem mul_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0)
    (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (ab : VG.Proof.X448.AArch64.Bounded s.mem base a) (bb : VG.Proof.X448.AArch64.Bounded s.mem base b) :
    WP isa (Impl.X448.AArch64.mul o a b) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.X448.AArch64.Bounded t.mem base o ∧ VG.Proof.X448.AArch64.F t.mem base o = VG.Proof.X448.AArch64.F s.mem base a * VG.Proof.X448.AArch64.F s.mem base b := by
  let f := VG.Proof.X448.AArch64.limbs s.mem base a
  let g := VG.Proof.X448.AArch64.limbs s.mem base b
  rw [Impl.X448.AArch64.mul, WP.seq_iff]
  refine WP.mono (VG.Proof.X448.AArch64.mulInit_ok hs) fun t ⟨tz, tc, tr, tm, tk⟩ => ?_
  have ts := hs.of_keeps tk (by decide)
  have ft : ∀ i < 16, VG.Proof.X448.AArch64.limbs t.mem base a i = f i := fun i hi =>
    tm.limbs (Or.inl ha) (Nat.le_trans ha (by decide)) hi
  have gt : ∀ i < 16, VG.Proof.X448.AArch64.limbs t.mem base b i = g i := fun i hi =>
    tm.limbs (Or.inl hb) (Nat.le_trans hb (by decide)) hi
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.X448.AArch64.mulLoop_ok ts ha ha8 hb hb8 ft gt ab bb tz tc tr) fun u ⟨uf, um, uk⟩ => ?_
  have us := ts.of_keeps uk (by decide)
  have rawBound : ∀ k < 32, rows f g 16 k < 2 ^ 60 := by
    intro k _
    exact Nat.lt_of_le_of_lt (rows_bound ab bb (by decide) k) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.reduce_ok us uf rawBound) fun v ⟨vf, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.normalize_ok vs ho ho8 vf (fun i hi => VG.Proof.X448.reduced_bound rawBound i hi))
    fun w ⟨wf, wm, wk⟩ => ?_
  have val : VG.Proof.X448.AArch64.fe w.mem base o % Spec.X448.P = (VG.Proof.X448.AArch64.fe s.mem base a * VG.Proof.X448.AArch64.fe s.mem base b) % Spec.X448.P := by
    rw [show VG.Proof.X448.AArch64.fe w.mem base o = VG.Proof.X448.valN (VG.Proof.X448.normalized (VG.Proof.X448.reduced (rows f g 16))) 16 from VG.Proof.X448.valN_congr wf,
      VG.Proof.X448.normalized_mod (fun i hi => VG.Proof.X448.reduced_bound rawBound i hi), VG.Proof.X448.reduced_mod, rows_val f g (by decide)]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have k₁ : VG.Proof.X448.AArch64.Keeps VG.Proof.X448.AArch64.clob s t := tk.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)
    have k₃ : VG.Proof.X448.AArch64.Keeps VG.Proof.X448.AArch64.clob u v := vk.mono (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide)
    have k₄ : VG.Proof.X448.AArch64.Keeps VG.Proof.X448.AArch64.clob v w := wk.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)
    exact k₁.trans ((uk.mono (by decide)).trans (k₃.trans k₄))
  · exact (FieldMem.work tm (by omega) (by omega)).trans
      ((FieldMem.work um (by omega) (by omega)).trans
      ((FieldMem.work vm (by decide) (by decide)).trans wm))
  · intro i hi; rw [wf i hi]; exact VG.Proof.X448.digit_lt _ _
  · exact VG.Proof.X448.toFe_mul val

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Columns`. -/
section

/-!
# X448 on AArch64: pointwise field operations

A pointwise operation fills `TMP` before the carry passes write the output,
permitting input/output aliasing.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem columns_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {code : Nat → List Instr}
    {f : Nat → Nat} {rs : List Reg} (hr : .x3 ∉ rs ∧ .x12 ∉ rs) (hb : ∀ i < 16, f i < 2 ^ 62)
    (step : ∀ i < 16, ∀ t, VG.Proof.X448.AArch64.Scr t base → VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem → VG.Proof.X448.AArch64.Keeps rs s t →
      WP isa (.block (code i)) t fun u =>
        u.mem = t.mem.writeW (VG.Proof.X448.AArch64.off base (TMP + 8 * i)) (BitVec.ofNat 64 (f i)) ∧ VG.Proof.X448.AArch64.Keeps rs t u) :
    WP isa (.block ((List.range 16).flatMap code)) s fun t =>
      (∀ i < 16, VG.Proof.X448.AArch64.limbs t.mem base TMP i = f i) ∧ VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps rs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.AArch64.limbs t.mem base TMP i = f i) ∧ VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps rs s t
  have st : ∀ n t, n < 16 → inv n t → WP isa (.block (code n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (step n hn t (hs.of_keeps tk hr) tm tk) fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.AArch64.Outside base (TMP + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.AArch64.writeW_outside _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (VG.Proof.X448.AArch64.word u.mem base (TMP + 8 * i)).toNat = _
    rw [um, VG.Proof.X448.AArch64.word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 16) inv st 16 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- Reading an input during a pointwise operation. -/
theorem input_limb {s t : State} {base : Addr} {a i : Nat} (h : VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem)
    (ha : VG.Proof.X448.AArch64.Slot a) (hi : i < 16) : VG.Proof.X448.AArch64.limbs t.mem base a i = VG.Proof.X448.AArch64.limbs s.mem base a i :=
  h.limbs (Or.inl (Nat.le_trans ha (by decide))) (Nat.le_trans ha (by decide)) hi

/-- Carry propagation after a pointwise operation, with the common frame. -/
theorem columns_normalize {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {code : List Instr}
    {o : Nat} (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) {f : Nat → Nat} (hb : ∀ i < 16, f i < 2 ^ 62)
    (hcode : WP isa (.block code) s fun t =>
      (∀ i < 16, VG.Proof.X448.AArch64.limbs t.mem base TMP i = f i) ∧ VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps VG.Proof.X448.AArch64.clob s t) :
    WP isa (.block (code ++ normalize o)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.X448.AArch64.Bounded t.mem base o ∧ VG.Proof.X448.AArch64.fe t.mem base o % Spec.X448.P = VG.Proof.X448.valN f 16 % Spec.X448.P := by
  rw [WP.block_append_iff]
  refine WP.mono hcode fun t ⟨tf, tm, tk⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.normalize_ok (hs.of_keeps tk (by decide)) ho ho8 tf hb) fun u ⟨uf, um, uk⟩ => ?_
  refine ⟨⟨tk.trans (uk.mono ?_), (FieldMem.work tm (by decide) (by decide)).trans um⟩, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro i hi; rw [uf i hi]; exact VG.Proof.X448.digit_lt _ _
  · rw [show VG.Proof.X448.AArch64.fe u.mem base o = VG.Proof.X448.valN (VG.Proof.X448.normalized f) 16 from VG.Proof.X448.valN_congr uf, VG.Proof.X448.normalized_mod hb]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.AddSub`. -/
section

/-!
# X448 on AArch64: addition and subtraction

Subtraction adds twice the prime limbwise before subtracting, so every
intermediate remains nonnegative.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem addStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {a b i : Nat}
    (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (hi : i < 16) :
    WP isa (.block [ld .x4 (a + 8 * i), ld .x5 (b + 8 * i), .add .x .x4 .x4 .x5, st .x4 (TMP + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.AArch64.off base (TMP + 8 * i))
        (BitVec.ofNat 64 (VG.Proof.X448.AArch64.limbs s.mem base a i + VG.Proof.X448.AArch64.limbs s.mem base b i)) ∧ VG.Proof.X448.AArch64.Keeps VG.Proof.X448.AArch64.clob s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega)
  have w := hs.write (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega
  have oe : (TMP + 8 * i) % 8 = 0 ∧ TMP + 8 * i < 32768 := by simp only [TMP]; omega
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, oe, and_self,
    hs.x3, la, lb, w, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, VG.Proof.X448.AArch64.read8_eq, VG.Proof.X448.AArch64.write8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · apply congrArg (s.mem.writeW (VG.Proof.X448.AArch64.off base (TMP + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  · have hr' : r ≠ .x4 := fun h => hr (by subst r; decide)
    have hr'' : r ≠ .x5 := fun h => hr (by subst r; decide)
    simp only [RegUpd.gpr_write, hr', hr'', ite_false]

theorem subK_nat (i : Nat) : ((subK i).setWidth 64 &&& ~~~((65535 : BitVec 64) <<< (16 : Nat)) ||| (8191 : BitVec 16).setWidth 64 <<< (16 : Nat)).toNat = VG.Proof.X448.bias i := by
  by_cases h : i = 8 <;> simp only [subK, VG.Proof.X448.bias, h, ite_true, ite_false] <;> decide

theorem subStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {a b i : Nat}
    (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (hi : i < 16)
    (ab : VG.Proof.X448.AArch64.limbs s.mem base a i < VG.Proof.X448.radix) (bb : VG.Proof.X448.AArch64.limbs s.mem base b i < VG.Proof.X448.radix) :
    WP isa (.block [ld .x4 (a + 8 * i), .movz .x .x5 (subK i) 0, .movk .x .x5 0x1fff 1,
      .add .x .x4 .x4 .x5, ld .x5 (b + 8 * i), .sub .x .x4 .x4 .x5, st .x4 (TMP + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.AArch64.off base (TMP + 8 * i))
        (BitVec.ofNat 64 (VG.Proof.X448.difference (VG.Proof.X448.AArch64.limbs s.mem base a) (VG.Proof.X448.AArch64.limbs s.mem base b) i)) ∧ VG.Proof.X448.AArch64.Keeps VG.Proof.X448.AArch64.clob s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega)
  have w := hs.write (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega)
  have biasb := VG.Proof.X448.bias_bound i
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega
  have oe : (TMP + 8 * i) % 8 = 0 ∧ TMP + 8 * i < 32768 := by simp only [TMP]; omega
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero, State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, oe, and_self,
    hs.x3, la, lb, w, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, VG.Proof.X448.AArch64.read8_eq, VG.Proof.X448.AArch64.write8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · apply congrArg (s.mem.writeW (VG.Proof.X448.AArch64.off base (TMP + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, VG.Proof.X448.AArch64.subK_nat, BitVec.toNat_ofNat, VG.Proof.X448.difference]
    change (2 ^ 64 - VG.Proof.X448.AArch64.limbs s.mem base b i + (VG.Proof.X448.AArch64.limbs s.mem base a i + VG.Proof.X448.bias i) % 2 ^ 64) % 2 ^ 64 =
      (VG.Proof.X448.AArch64.limbs s.mem base a i + VG.Proof.X448.bias i - VG.Proof.X448.AArch64.limbs s.mem base b i) % 2 ^ 64
    have hr : VG.Proof.X448.radix = 268435456 := rfl
    omega
  · have hr' : r ≠ .x4 := fun h => hr (by subst r; decide)
    have hr'' : r ≠ .x5 := fun h => hr (by subst r; decide)
    simp only [RegUpd.gpr_write, hr', hr'', ite_false]

theorem add_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (ab : VG.Proof.X448.AArch64.Bounded s.mem base a) (bb : VG.Proof.X448.AArch64.Bounded s.mem base b) :
    WP isa (.block (Impl.X448.AArch64.add o a b)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.X448.AArch64.Bounded t.mem base o ∧ VG.Proof.X448.AArch64.F t.mem base o = VG.Proof.X448.AArch64.F s.mem base a + VG.Proof.X448.AArch64.F s.mem base b := by
  let f := fun i => VG.Proof.X448.AArch64.limbs s.mem base a i + VG.Proof.X448.AArch64.limbs s.mem base b i
  have fb : ∀ i < 16, f i < 2 ^ 62 := by
    intro i hi
    have h1 := ab i hi
    have h2 := bb i hi
    change VG.Proof.X448.AArch64.limbs s.mem base a i + VG.Proof.X448.AArch64.limbs s.mem base b i < _
    simp only [VG.Proof.X448.radix] at h1 h2
    omega
  refine WP.mono (VG.Proof.X448.AArch64.columns_normalize hs ho ho8 fb (VG.Proof.X448.AArch64.columns_ok hs (by decide : .x3 ∉ clob ∧ .x12 ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_add ?_⟩
  · intro i hi t ts tm _
    refine WP.mono (VG.Proof.X448.AArch64.addStep_ok ts ha ha8 hb hb8 hi) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    rw [VG.Proof.X448.AArch64.input_limb tm ha hi, VG.Proof.X448.AArch64.input_limb tm hb hi] at um
    exact um
  · rw [tv, VG.Proof.X448.valN_add]

theorem sub_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (ab : VG.Proof.X448.AArch64.Bounded s.mem base a) (bb : VG.Proof.X448.AArch64.Bounded s.mem base b) :
    WP isa (.block (Impl.X448.AArch64.sub o a b)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.X448.AArch64.Bounded t.mem base o ∧ VG.Proof.X448.AArch64.F t.mem base o = VG.Proof.X448.AArch64.F s.mem base a - VG.Proof.X448.AArch64.F s.mem base b := by
  let f := VG.Proof.X448.difference (VG.Proof.X448.AArch64.limbs s.mem base a) (VG.Proof.X448.AArch64.limbs s.mem base b)
  have fb : ∀ i < 16, f i < 2 ^ 62 := VG.Proof.X448.difference_bound ab
  refine WP.mono (VG.Proof.X448.AArch64.columns_normalize hs ho ho8 fb (VG.Proof.X448.AArch64.columns_ok hs (by decide : .x3 ∉ clob ∧ .x12 ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_sub ?_⟩
  · intro i hi t ts tm _
    have ea := VG.Proof.X448.AArch64.input_limb tm ha hi
    have eb := VG.Proof.X448.AArch64.input_limb tm hb hi
    refine WP.mono (VG.Proof.X448.AArch64.subStep_ok ts ha ha8 hb hb8 hi (ea ▸ ab i hi) (eb ▸ bb i hi)) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    simp only [VG.Proof.X448.difference, ea, eb] at um
    exact um
  · rw [Nat.add_mod, tv, ← Nat.add_mod, VG.Proof.X448.difference_val bb, Nat.add_mul_mod_self_right]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Copy`. -/
section

/-!
# X448 on AArch64: copying field elements

Source and destination are equal or disjoint; every limb is copied without
changing its representation.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem copyStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o a i : Nat}
    (ho : o + 128 ≤ 8192) (ha : a + 128 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hi : i < 16) :
    WP isa (.block [ld .x4 (a + 8 * i), st .x4 (o + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.AArch64.off base (o + 8 * i)) (VG.Proof.X448.AArch64.word s.mem base (a + 8 * i)) ∧ VG.Proof.X448.AArch64.Keeps VG.Proof.X448.AArch64.clob s t := by
  have l := hs.read (d := a + 8 * i) (n := 8) (by omega)
  have w := hs.write (d := o + 8 * i) (n := 8) (by omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := ⟨by omega, by omega⟩
  have oe : (o + 8 * i) % 8 = 0 ∧ o + 8 * i < 32768 := ⟨by omega, by omega⟩
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.wr_write, BitVec.setWidth_eq, ae, oe, and_self, hs.x3, l, w,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, VG.Proof.X448.AArch64.read8_eq, VG.Proof.X448.AArch64.write8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (fun h => hr (by subst r; decide))

theorem copy_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o a : Nat}
    (ho : o + 128 ≤ 8192) (ha : a + 128 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (hsep : o = a ∨ o + 128 ≤ a ∨ a + 128 ≤ o) :
    WP isa (.block (copy o a)) s fun t =>
      (∀ i < 16, VG.Proof.X448.AArch64.limbs t.mem base o i = VG.Proof.X448.AArch64.limbs s.mem base a i) ∧
      VG.Proof.X448.AArch64.Outside base o 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps VG.Proof.X448.AArch64.clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.AArch64.limbs t.mem base o i = VG.Proof.X448.AArch64.limbs s.mem base a i) ∧
    (∀ i, n ≤ i → i < 16 → VG.Proof.X448.AArch64.limbs t.mem base a i = VG.Proof.X448.AArch64.limbs s.mem base a i) ∧
    VG.Proof.X448.AArch64.Outside base o 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps VG.Proof.X448.AArch64.clob s t
  have st : ∀ n t, n < 16 → inv n t →
      WP isa (.block [ld .x4 (a + 8 * n), st .x4 (o + 8 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, ta, tm, tk⟩
    refine WP.mono (VG.Proof.X448.AArch64.copyStep_ok (hs.of_keeps tk (by decide)) ho ha ho8 ha8 hn) fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.AArch64.Outside base (o + 8 * n) 8 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    · intro i hi
      change (VG.Proof.X448.AArch64.word u.mem base (o + 8 * i)).toNat = _
      rw [um, VG.Proof.X448.AArch64.word_write t.mem base (by omega) (by omega)]
      by_cases h : i = n
      · rw [ite_eq_left h, h]; exact ta n (by omega) hn
      · rw [ite_eq_right h]; exact tf i (by omega)
    · intro i hi hi'
      change (VG.Proof.X448.AArch64.word u.mem base (a + 8 * i)).toNat = _
      rw [out.word (by rcases hsep with h | h | h <;> omega) (by omega)]
      exact ta i (by omega) hi'
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv st 16 (by decide) s ?_)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  exact ⟨fun _ hi => by omega, fun _ _ _ => rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Decode`. -/
section

/-!
# X448 on AArch64: decoding the u-coordinate

Seven byte loads form each pair of 28-bit limbs; no load extends past the
56-byte input.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- Accumulate one byte from the high end of a seven-byte chunk. -/
def decodeByte (i j : Nat) : List Instr :=
  [.lsl .x .x4 .x4 8, .ldrb .x7 .x2 (7 * i + (6 - j)), .add .x .x4 .x4 .x7]

theorem decodeByte_ok {s : State} {p : Addr} {i j : Nat}
    (hp : s.gpr .x2 = p) (hi : i < 8) (hb : (s.gpr .x4).toNat < 2 ^ 48)
    (hr : InRegions (s.rd ++ s.wr) (VG.Proof.X448.AArch64.off p (7 * i + (6 - j))) 1) :
    WP isa (.block (VG.Proof.X448.AArch64.decodeByte i j)) s fun t =>
      (t.gpr .x4).toNat = 256 * (s.gpr .x4).toNat + (s.mem (VG.Proof.X448.AArch64.off p (7 * i + (6 - j)))).toNat ∧
      t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5, .x7] s t := by
  have byteb := (s.mem (VG.Proof.X448.AArch64.off p (7 * i + (6 - j)))).isLt
  have mulb : (s.gpr .x4).toNat * 256 < 2 ^ 64 := by omega
  have enc : (7 * i + (6 - j)) % 1 = 0 ∧ 7 * i + (6 - j) < 4096 := by omega
  apply WP.of_runBlock
  simp only [VG.Proof.X448.AArch64.decodeByte, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceLT, BitVec.setWidth_eq, addr, enc, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hp,
    State.load, hr, VG.Proof.X448.AArch64.read1_eq, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    change (((s.gpr .x4).toNat * 256) % 2 ^ 64 +
      ((s.mem (VG.Proof.X448.AArch64.off p (7 * i + (6 - j)))).toNat % 2 ^ 32) % 2 ^ 64) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt mulb, Nat.mod_eq_of_lt (by omega : (s.mem (off p (7 * i + (6 - j)))).toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : (s.mem (off p (7 * i + (6 - j)))).toNat < 2 ^ 64)]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.2, ite_false]

def readSeven (i : Nat) : List Instr :=
  [.movz .x .x4 0 0] ++ (List.range 7).flatMap (VG.Proof.X448.AArch64.decodeByte i)

theorem readSevenInit_ok (s : State) :
    WP isa (.block [.movz .x .x4 0 0]) s fun t =>
      (t.gpr .x4).toNat = 0 ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, ite_false]

theorem readSeven_ok {s : State} {p : Addr} {i : Nat} (hp : s.gpr .x2 = p) (hi : i < 8)
    (hr : ∀ j < 7, InRegions (s.rd ++ s.wr) (VG.Proof.X448.AArch64.off p (7 * i + j)) 1) :
    WP isa (.block (VG.Proof.X448.AArch64.readSeven i)) s fun t =>
      (t.gpr .x4).toNat = chunk s.mem p i ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5, .x7, .x8] s t := by
  rw [VG.Proof.X448.AArch64.readSeven, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.readSevenInit_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  let inv := fun n (u : State) =>
    (u.gpr .x4).toNat = suffix s.mem p i n ∧ u.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5, .x7] t u
  have step : ∀ n u, n < 7 → inv n u → WP isa (.block (VG.Proof.X448.AArch64.decodeByte i n)) u (inv (n + 1)) := by
    intro n u hn ⟨uv, um, uk⟩
    have up : u.gpr .x2 = p := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hp)
    have ub : (u.gpr .x4).toNat < 2 ^ 48 := by
      rw [uv]
      have h := suffix_bound s.mem p i n
      have hpow : 256 ^ n ≤ 256 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.lt_of_lt_of_le h hpow
    have ur : InRegions (u.rd ++ u.wr) (VG.Proof.X448.AArch64.off p (7 * i + (6 - n))) 1 := by
      rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2]; exact hr _ (by omega)
    refine WP.mono (VG.Proof.X448.AArch64.decodeByte_ok up hi ub ur) fun v ⟨vv, vm, vk⟩ => ⟨?_, vm.trans um, uk.trans vk⟩
    rw [vv, uv, um, suffix_succ _ _ _ hn]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv step 7 (by decide) t
    ⟨tz, tm, Keeps.refl _ _⟩) fun u ⟨uv, um, uk⟩ => ⟨?_, um, ?_⟩
  · exact uv
  · refine (tk.mono ?_).trans (uk.mono ?_)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.FreezePrep`. -/
section

/-!
# X448 on AArch64: preparing canonical reduction

Adding one in limbs zero and eight implements the addition of 1 + 2²²⁴ before
carry propagation.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem incrementStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {d : Nat}
    (hd : d + 8 ≤ 8192) (hd8 : d % 8 = 0) :
    WP isa (.block [ld .x4 d, .addImm .x .x4 .x4 1, st .x4 d]) s
      fun s' => s'.mem = s.mem.writeW (VG.Proof.X448.AArch64.off base d) (VG.Proof.X448.AArch64.word s.mem base d + (1 : BitVec 64)) ∧
        VG.Proof.X448.AArch64.Keeps [.x4] s s' := by
  have l := hs.read hd
  have w := hs.write hd
  have enc : d % 8 = 0 ∧ d < 32768 := ⟨hd8, by omega⟩
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.wr_write, BitVec.setWidth_eq, enc, and_self, hs.x3, l, w,
    Nat.reduceLT, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    VG.Proof.X448.AArch64.read8_eq, VG.Proof.X448.AArch64.write8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem incrementLimb_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {k : Nat} (hk : k < 16)
    (hb : VG.Proof.X448.AArch64.limbs s.mem base TMP k + 1 < 2 ^ 64) :
    WP isa (.block [ld .x4 (TMP + 8 * k), .addImm .x .x4 .x4 1,
      st .x4 (TMP + 8 * k)]) s fun t =>
      (∀ i < 16, VG.Proof.X448.AArch64.limbs t.mem base TMP i =
        if i = k then VG.Proof.X448.AArch64.limbs s.mem base TMP i + 1 else VG.Proof.X448.AArch64.limbs s.mem base TMP i) ∧
      VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4] s t := by
  have hd : TMP + 8 * k + 8 ≤ 8192 := by simp only [TMP]; omega
  refine WP.mono (VG.Proof.X448.AArch64.incrementStep_ok hs hd (by simp only [TMP]; omega)) fun t ⟨hm, ht⟩ => ?_
  refine ⟨?_, ?_, ht⟩
  · intro i hi
    change (VG.Proof.X448.AArch64.word t.mem base (TMP + 8 * i)).toNat = _
    rw [hm, VG.Proof.X448.AArch64.word_write s.mem base (by omega) (by simp only [TMP]; omega)]
    by_cases h : i = k
    · rw [ite_eq_left h, ite_eq_left h, h, BitVec.toNat_add]
      change (VG.Proof.X448.AArch64.limbs s.mem base TMP k + 1) % 2 ^ 64 = _
      exact Nat.mod_eq_of_lt hb
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [hm]
    exact (VG.Proof.X448.AArch64.writeW_outside _ _ _ hd).mono (by omega) (by omega)


theorem freezePrep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) (hb : VG.Proof.X448.AArch64.Bounded s.mem base X2) :
    WP isa (.block (copy TMP X2 ++ [0, 8].flatMap (fun i =>
      [ld .x4 (TMP + 8 * i), .addImm .x .x4 .x4 1,
        st .x4 (TMP + 8 * i)]))) s fun t =>
      (∀ i < 16, VG.Proof.X448.AArch64.limbs t.mem base TMP i = VG.Proof.X448.freezeCoeff (VG.Proof.X448.AArch64.limbs s.mem base X2) i) ∧
      VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps VG.Proof.X448.AArch64.clob s t := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.copy_ok hs (by decide) (by decide) (by decide) (by decide) (by decide)) fun t ⟨tf, tm, tk⟩ => ?_
  have bound : ∀ i < 16, VG.Proof.X448.AArch64.limbs s.mem base X2 i + 1 < 2 ^ 64 := by
    intro i hi; have h := hb i hi; simp only [VG.Proof.X448.radix] at h; omega
  change WP isa (.block
    (([ld .x4 (TMP + 8 * 0), .addImm .x .x4 .x4 1,
       st .x4 (TMP + 8 * 0)] : List Instr) ++
     [ld .x4 (TMP + 8 * 8), .addImm .x .x4 .x4 1,
       st .x4 (TMP + 8 * 8)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.incrementLimb_ok (hs.of_keeps tk (by decide)) (k := 0) (by decide)
    (by rw [tf 0 (by decide)]; exact bound 0 (by decide))) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.incrementLimb_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
    (k := 8) (by decide) (by
      rw [uf 8 (by decide), ite_eq_right (by decide), tf 8 (by decide)]
      exact bound 8 (by decide))) fun v ⟨vf, vm, vk⟩ => ?_
  refine ⟨?_, tm.trans (um.trans vm), tk.trans ((uk.trans vk).mono ?_)⟩
  · intro i hi
    rw [vf i hi, uf i hi, tf i hi]
    simp only [VG.Proof.X448.freezeCoeff]
    by_cases h0 : i = 0
    · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
    · by_cases h8 : i = 8
      · subst i; simp (config := {decide := true}) only [ite_true, ite_false]
      · simp only [h0, h8, ite_false, false_or, Nat.add_zero]
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.PointwiseAdd`. -/
section

/-! Untrusted: pointwise coefficient in registers, without an intermediate store. -/
namespace VG.Proof.X448.AArch64
open VG VG.AArch64 VG.Impl.X448.AArch64

theorem addEval_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {a b i : Nat}
    (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (hi : i < 16) :
    WP isa (.block (Pointwise.addEval a b i)) s fun t =>
      t.gpr .x4 = BitVec.ofNat 64 (VG.Proof.X448.AArch64.limbs s.mem base a i + VG.Proof.X448.AArch64.limbs s.mem base b i) ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega
  apply WP.of_runBlock
  simp only [Pointwise.addEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, and_self,
    hs.x3, la, lb, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, VG.Proof.X448.AArch64.read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.PointwiseCarry`. -/
section

/-! Untrusted: carry a coefficient directly from its register. -/
namespace VG.Proof.X448.AArch64
open VG VG.AArch64 VG.Impl.X448.AArch64

theorem pointwiseCarry_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {i : Nat} (hi : i < 16)
    (hb : (s.gpr .x4).toNat + (s.gpr .x6).toNat < 2 ^ 64) :
    let v := (s.gpr .x4).toNat + (s.gpr .x6).toNat
    WP isa (.block (Pointwise.carry i)) s fun s' =>
      (s'.gpr .x6).toNat = v / VG.Proof.X448.radix ∧
      s'.mem = s.mem.writeW (VG.Proof.X448.AArch64.off base (TMP + 8 * i)) (BitVec.ofNat 64 (v % VG.Proof.X448.radix)) ∧
      VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5] s s' := by
  intro v
  have ho : TMP + 8 * i + 8 ≤ 8192 := by simp only [TMP]; omega
  have w := hs.write ho
  have oe : (TMP + 8 * i) % 8 = 0 ∧ TMP + 8 * i < 4096 * 8 := ⟨by simp only [TMP]; omega, by omega⟩
  apply WP.of_runBlock
  simp only [Pointwise.carry, st, runBlock_cons, runStep_some, runBlock_nil, exec,
    Size.bytes, Size.bits, addr, oe, State.read, State.store, hs.x3, hs.mask, w,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write,
    BitVec.setWidth_eq, Option.bind_some,
    and_self, ite_true, ite_false, reduceCtorEq, Nat.reduceLT, Nat.reduceMul,
    VG.Proof.X448.AArch64.write8_eq, Option.some.injEq, exists_eq_left']
  have hv : (s.gpr .x4 + s.gpr .x6).toNat = v := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hb]
  refine ⟨?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [VG.Proof.X448.AArch64.shr28, hv]
  · apply congrArg (s.mem.writeW (VG.Proof.X448.AArch64.off base (TMP + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.X448.AArch64.and28, hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v % VG.Proof.X448.radix) (by
      have := Nat.mod_lt v (show 0 < VG.Proof.X448.radix by decide)
      have : VG.Proof.X448.radix < 2 ^ 64 := by decide
      omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.PointwiseFinish`. -/
section

/-!
# X448 on AArch64: modular reduction

Untrusted: everything here is checked by Lean. Three carry passes and two
folds normalize coefficients bounded by 2⁶², preserving their value modulo p.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- Normalize the coefficients at `TMP` into a field-element slot. -/
theorem pointwiseFinish_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o : Nat}
    (ho : o + 128 ≤ ACC) (ho8 : o % 8 = 0) {f : Nat → Nat}
    (hf : ∀ i < 16, VG.Proof.X448.AArch64.limbs s.mem base TMP i = VG.Proof.X448.digit f i) (hc : (s.gpr .x6).toNat = VG.Proof.X448.carry f 16)
    (hb : ∀ i < 16, f i < 2 ^ 62) :
    WP isa (.block (Pointwise.finish o)) s fun t =>
      (∀ i < 16, VG.Proof.X448.AArch64.limbs t.mem base o i = VG.Proof.X448.normalized f i) ∧
      VG.Proof.X448.AArch64.FieldMem base o s.mem t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5] s t := by
  have htmp : TMP + 128 ≤ 8192 := by decide
  have hwork : ∀ {m m' : Mem}, VG.Proof.X448.AArch64.Outside base TMP 128 m m' → VG.Proof.X448.AArch64.FieldMem base o m m' :=
    fun h => FieldMem.work h (by decide) (by decide)
  have keep : ∀ {a b : State}, VG.Proof.X448.AArch64.Keeps [.x4] a b → VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5] a b :=
    fun h => h.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; decide)
  rw [Pointwise.finish, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.fold_ok hs hf hc (VG.Proof.X448.carry_bound hb)) fun s₂ ⟨f₂, m₂, k₂⟩ => ?_
  have hs₂ := hs.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.pass_ok hs₂ htmp htmp (by decide) (by decide) (Or.inl rfl) f₂ (VG.Proof.X448.folded_bound hb)) fun s₃ ⟨f₃, c₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.fold_ok hs₃ f₃ c₃ (VG.Proof.X448.carry_bound (VG.Proof.X448.folded_bound hb))) fun s₄ ⟨f₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have ho' : o + 128 ≤ TMP := Nat.le_trans ho (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.pass_ok hs₄ (Nat.le_trans ho (by decide)) htmp ho8 (by decide) (Or.inr (Or.inl ho')) f₄
    (VG.Proof.X448.folded_bound (VG.Proof.X448.folded_bound hb))) fun s₅ ⟨f₅, _, m₅, k₅⟩ => ?_
  exact ⟨f₅, (hwork m₂).trans ((hwork m₃).trans ((hwork m₄).trans (.output m₅))),
    (keep k₂).trans (k₃.trans ((keep k₄).trans k₅))⟩

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.PointwiseFused`. -/
section

/-! Untrusted: fuse a pointwise coefficient with its first carry step. -/
namespace VG.Proof.X448.AArch64
open VG VG.AArch64 VG.Impl.X448.AArch64

theorem pointwiseFirst_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base)
    {code : Nat → List Instr} {f : Nat → Nat} (hb : ∀ i < 16, f i < 2 ^ 62)
    (heval : ∀ i < 16, ∀ t, VG.Proof.X448.AArch64.Scr t base → VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        u.gpr .x4 = BitVec.ofNat 64 (f i) ∧ u.mem = t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] t u) :
    WP isa (.block (([.movz .x .x6 0 0] : List Instr) ++
      (List.range 16).flatMap (fun i => code i ++ Pointwise.carry i))) s fun t =>
      (∀ i < 16, VG.Proof.X448.AArch64.limbs t.mem base TMP i = VG.Proof.X448.digit f i) ∧
      (t.gpr .x6).toNat = VG.Proof.X448.carry f 16 ∧ VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem ∧
      VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5] s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, VG.Proof.X448.AArch64.limbs t.mem base TMP i = VG.Proof.X448.digit f i) ∧
    (t.gpr .x6).toNat = VG.Proof.X448.carry f k ∧ VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem ∧
    VG.Proof.X448.AArch64.Keeps [.x4, .x6, .x5] s t
  have step : ∀ k t, k < 16 → inv k t →
      WP isa (.block (code k ++ Pointwise.carry k)) t (inv (k + 1)) := by
    intro k t hk ⟨tf, tc, tm, tk⟩
    rw [WP.block_append_iff]
    refine WP.mono (heval k hk t (hs.of_keeps tk (by decide)) tm) fun u ⟨uv, um, uk⟩ => ?_
    have uc : (u.gpr .x6).toNat = VG.Proof.X448.carry f k := by rw [uk.1 .x6 (by decide), tc]
    have u4 : (u.gpr .x4).toNat = f k := by
      rw [uv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (hb k hk) (by decide))]
    have cap : (u.gpr .x4).toNat + (u.gpr .x6).toNat < 2 ^ 64 := by
      rw [u4, uc]
      have c := VG.Proof.X448.carry_bound (n := k) (fun i hi => hb i (by omega))
      have h := hb k hk
      omega
    have us := (hs.of_keeps tk (by decide)).of_keeps uk (by decide)
    refine WP.mono (VG.Proof.X448.AArch64.pointwiseCarry_ok us hk cap) fun v ⟨vc, vm, vk⟩ => ?_
    rw [u4, uc] at vc vm
    have out : VG.Proof.X448.AArch64.Outside base (TMP + 8 * k) 8 t.mem v.mem := by
      rw [vm, um]; exact VG.Proof.X448.AArch64.writeW_outside _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, vc, tm.trans (out.mono (by omega) (by omega)),
      tk.trans ((uk.mono (by decide)).trans vk)⟩
    intro i hi
    change (VG.Proof.X448.AArch64.word v.mem base (TMP + 8 * i)).toNat = _
    rw [vm, um, VG.Proof.X448.AArch64.word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = k
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat]
      change VG.Proof.X448.digit f k % 2 ^ 64 = VG.Proof.X448.digit f k
      exact Nat.mod_eq_of_lt (Nat.lt_trans (VG.Proof.X448.digit_lt f k) (by decide : radix < 2 ^ 64))
    · rw [ite_eq_right h]; exact tf i (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.zeroCarry_ok s) fun u ⟨uc, um, uk⟩ => ?_
  exact wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) u
    ⟨fun _ hi => by omega, by rw [uc]; rfl, by rw [um]; exact Outside.refl _ _ _ _, uk⟩

theorem pointwiseFused_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base)
    {code : Nat → List Instr} {o : Nat} (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0)
    {f : Nat → Nat} (hb : ∀ i < 16, f i < 2 ^ 62)
    (heval : ∀ i < 16, ∀ t, VG.Proof.X448.AArch64.Scr t base → VG.Proof.X448.AArch64.Outside base TMP 128 s.mem t.mem →
      WP isa (.block (code i)) t fun u =>
        u.gpr .x4 = BitVec.ofNat 64 (f i) ∧ u.mem = t.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] t u) :
    WP isa (.block (Pointwise.fused code o)) s fun t =>
      VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.X448.AArch64.Bounded t.mem base o ∧
      VG.Proof.X448.AArch64.fe t.mem base o % Spec.X448.P = VG.Proof.X448.valN f 16 % Spec.X448.P := by
  rw [Pointwise.fused, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.pointwiseFirst_ok hs hb heval) fun u ⟨uf, uc, um, uk⟩ => ?_
  refine WP.mono (VG.Proof.X448.AArch64.pointwiseFinish_ok (hs.of_keeps uk (by decide)) ho ho8 uf uc hb)
    fun t ⟨tf, tm, tk⟩ => ?_
  refine ⟨⟨(uk.mono (by decide)).trans (tk.mono (by decide)),
    (FieldMem.work um (by decide) (by decide)).trans tm⟩, ?_, ?_⟩
  · intro i hi; rw [tf i hi]; exact VG.Proof.X448.digit_lt _ _
  · rw [show VG.Proof.X448.AArch64.fe t.mem base o = VG.Proof.X448.valN (VG.Proof.X448.normalized f) 16 from VG.Proof.X448.valN_congr tf, VG.Proof.X448.normalized_mod hb]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.Small`. -/
section

/-!
# X448 on AArch64: multiplication by a24

Each limb is multiplied by 39081 before the common carry passes reduce the
result.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem smallStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {a i : Nat}
    (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hi : i < 16) (hc : (s.gpr .x6).toNat = 39081) :
    WP isa (.block [ld .x4 (a + 8 * i), .mul .x .x4 .x4 .x6, st .x4 (TMP + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.AArch64.off base (TMP + 8 * i)) (BitVec.ofNat 64 (39081 * VG.Proof.X448.AArch64.limbs s.mem base a i)) ∧
      VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t := by
  have l := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have w := hs.write (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  have oe : (TMP + 8 * i) % 8 = 0 ∧ TMP + 8 * i < 32768 := by simp only [TMP]; omega
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.wr_write, BitVec.setWidth_eq, ae, oe, and_self, hs.x3, l, w,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, VG.Proof.X448.AArch64.read8_eq, VG.Proof.X448.AArch64.write8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · apply congrArg (s.mem.writeW (VG.Proof.X448.AArch64.off base (TMP + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, hc, Nat.mul_comm _ 39081, BitVec.toNat_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, ite_false]

theorem smallInit_ok (s : State) :
    WP isa (.block [.movz .x .x6 39081 0]) s fun t =>
      (t.gpr .x6).toNat = 39081 ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x6] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem mulSmall_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {o a : Nat}
    (ho : VG.Proof.X448.AArch64.Slot o) (ho8 : o % 8 = 0) (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (ab : VG.Proof.X448.AArch64.Bounded s.mem base a) :
    WP isa (.block (mulSmall o a)) s fun t => VG.Proof.X448.AArch64.Op base o s t ∧ VG.Proof.X448.AArch64.Bounded t.mem base o ∧
      VG.Proof.X448.AArch64.F t.mem base o = Spec.X448.a24 * VG.Proof.X448.AArch64.F s.mem base a := by
  let f := fun i => 39081 * VG.Proof.X448.AArch64.limbs s.mem base a i
  have fb : ∀ i < 16, f i < 2 ^ 62 := by
    intro i hi
    have h := Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))
    have hr : 39081 * VG.Proof.X448.radix < 2 ^ 62 := by decide
    exact Nat.lt_of_le_of_lt h hr
  refine WP.mono (VG.Proof.X448.AArch64.columns_normalize hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_a24 ?_⟩
  · rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.X448.AArch64.smallInit_ok s) fun t ⟨tc, tm, tk⟩ => ?_
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (VG.Proof.X448.AArch64.columns_ok ts (by decide : Reg.x3 ∉ [Reg.x4, Reg.x5] ∧ Reg.x12 ∉ [Reg.x4, Reg.x5]) fb ?_) fun u ⟨uf, um, uk⟩ => ?_
    · intro i hi u us um uk
      have uc : (u.gpr .x6).toNat = 39081 := by rw [uk.1 _ (by decide), tc]
      refine WP.mono (VG.Proof.X448.AArch64.smallStep_ok us ha ha8 hi uc) fun v ⟨vm, vk⟩ => ⟨?_, vk⟩
      rw [VG.Proof.X448.AArch64.input_limb um ha hi, tm] at vm
      exact vm
    · refine ⟨uf, ?_, (tk.mono ?_).trans (uk.mono ?_)⟩
      · rw [← tm]; exact um
      · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide
  · rw [tv, VG.Proof.X448.valN_scale]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.PointwiseSmall`. -/
section

/-! Untrusted: a24 coefficient in registers, without an intermediate store. -/
namespace VG.Proof.X448.AArch64
open VG VG.AArch64 VG.Impl.X448.AArch64

theorem smallEval_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {a i : Nat}
    (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hi : i < 16) :
    WP isa (.block (Pointwise.smallEval a i)) s fun t =>
      t.gpr .x4 = BitVec.ofNat 64 (39081 * VG.Proof.X448.AArch64.limbs s.mem base a i) ∧
      t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  apply WP.of_runBlock
  simp only [Pointwise.smallEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    BitVec.setWidth_eq, ae, and_self, hs.x3, la, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, VG.Proof.X448.AArch64.read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, show (BitVec.setWidth 64 (39081 : BitVec 16)).toNat = 39081 by decide,
      Nat.mul_comm _ 39081, BitVec.toNat_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.X448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.AArch64.PointwiseSub`. -/
section

/-! Untrusted: pointwise coefficient in registers, without an intermediate store. -/
namespace VG.Proof.X448.AArch64
open VG VG.AArch64 VG.Impl.X448.AArch64

theorem subEval_ok {s : State} {base : Addr} (hs : VG.Proof.X448.AArch64.Scr s base) {a b i : Nat}
    (ha : VG.Proof.X448.AArch64.Slot a) (ha8 : a % 8 = 0) (hb : VG.Proof.X448.AArch64.Slot b) (hb8 : b % 8 = 0) (hi : i < 16)
    (ab : VG.Proof.X448.AArch64.limbs s.mem base a i < VG.Proof.X448.radix) (bb : VG.Proof.X448.AArch64.limbs s.mem base b i < VG.Proof.X448.radix) :
    WP isa (.block (Pointwise.subEval a b i)) s fun t =>
      t.gpr .x4 = BitVec.ofNat 64 (VG.Proof.X448.difference (VG.Proof.X448.AArch64.limbs s.mem base a) (VG.Proof.X448.AArch64.limbs s.mem base b) i) ∧ t.mem = s.mem ∧ VG.Proof.X448.AArch64.Keeps [.x4, .x5] s t := by
  have la := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have lb := hs.read (d := b + 8 * i) (n := 8) (by change b + 128 ≤ 3584 at hb; omega)
  have biasb := VG.Proof.X448.bias_bound i
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  have be : (b + 8 * i) % 8 = 0 ∧ b + 8 * i < 32768 := by
    change b + 128 ≤ 3584 at hb; omega
  apply WP.of_runBlock
  simp only [Pointwise.subEval, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, Nat.reduceLT, Nat.reduceMul, BitVec.shiftLeft_zero, State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, ae, be, and_self,
    hs.x3, la, lb, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, VG.Proof.X448.AArch64.read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, VG.Proof.X448.AArch64.subK_nat, BitVec.toNat_ofNat, VG.Proof.X448.difference]
    change (2 ^ 64 - VG.Proof.X448.AArch64.limbs s.mem base b i + (VG.Proof.X448.AArch64.limbs s.mem base a i + VG.Proof.X448.bias i) % 2 ^ 64) % 2 ^ 64 =
      (VG.Proof.X448.AArch64.limbs s.mem base a i + VG.Proof.X448.bias i - VG.Proof.X448.AArch64.limbs s.mem base b i) % 2 ^ 64
    have hr : VG.Proof.X448.radix = 268435456 := rfl
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

end VG.Proof.X448.AArch64

end
