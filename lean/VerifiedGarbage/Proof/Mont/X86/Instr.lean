import VerifiedGarbage.Impl.Mont.X86
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.X86.Wp

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86.Words`. -/
section

/-!
# Montgomery arithmetic on x86 (32-bit): words in the working space

The working space is `size` bytes at `base`, whose low 32 bits `edi` holds
(`Scr`), below `2³²`. Its numbers are read as 32-bit words (`w32`, `val32`):
`k` of them at an offset are the same bytes, and the same number, as
`k / 2` 64-bit words (`wordsVal_eq_val32`), in which the other targets and
the target-independent proofs state them. The loads and stores of the
arithmetic, through `edi` or through `ebp`, which the multiplication moves
by 4 bytes a row (`ea_at`), and what changes (`Keeps`).
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-! ## The working space -/

/-- The working space: `edi` holds its base `base`, it is writable and it
lies below `2³²`. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  edi : (s.gpr .edi).setWidth 64 = base
  wr : (⟨base, size⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 32

theorem Scr.edi_toNat {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86.Scr s base size) :
    (s.gpr .edi).toNat = base.toNat := by
  rw [← hs.edi, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .edi).isLt
    (Nat.pow_le_pow_right (by decide) (by decide)))]

/-- `[edi + d]`. -/
theorem Scr.ea {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86.Scr s base size) {d : Nat}
    (hd : d < size) : s.ea (sc d) = off base d := by
  change addr (s.gpr .edi) d = _
  rw [addr_eq (by have := hs.nowrap; have := hs.edi_toNat; omega), hs.edi]

/-- `[ebp + d]`, with `ebp` at `4i` bytes into the working space. -/
theorem Scr.ea_at {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86.Scr s base size) {i d : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hd : 4 * i + d < size) :
    s.ea (at_ .ebp d) = off base (4 * i + d) := by
  change ((s.gpr .ebp + BitVec.ofNat 32 d).setWidth 64) = _
  rw [hp, Offset.add_add]
  exact hs.ea hd

theorem Scr.contains {base : Addr} {size d n : Nat} (hn : base.toNat + size ≤ 2 ^ 32) (h : d + n ≤ size) :
    (⟨base, size⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by omega)

theorem Scr.read {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86.Scr s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions (s.rd ++ s.wr) (off base d) n :=
  ⟨_, List.mem_append_right _ hs.wr, Scr.contains hs.nowrap hd⟩

theorem Scr.write {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86.Scr s base size) {d n : Nat}
    (hd : d + n ≤ size) : InRegions s.wr (off base d) n := ⟨_, hs.wr, Scr.contains hs.nowrap hd⟩

/-- The registers and permissions that a piece of code preserves. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.refl (rs : List Reg) (s : State) : VG.Proof.Mont.X86.Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Mont.X86.Keeps rs s₁ s₂) (h₂ : VG.Proof.Mont.X86.Keeps rs s₂ s₃) :
    VG.Proof.Mont.X86.Keeps rs s₁ s₃ := ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1,
      h₂.2.2.trans h₁.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.Mont.X86.Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.Mont.X86.Keeps rs' s s' := ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86.Scr s base size)
    (h : VG.Proof.Mont.X86.Keeps rs s s') (hr : .edi ∉ rs) : VG.Proof.Mont.X86.Scr s' base size :=
  ⟨by rw [h.1 _ hr]; exact hs.edi, h.2.2 ▸ hs.wr, hs.nowrap⟩

end VG.Proof.Mont.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Mont.X86.Instr`. -/
section

/-!
# Montgomery arithmetic on x86 (32-bit): instruction rules

Continuation-passing rules (as `Proof/Framework/X86/Wp.lean`) for the
instructions of the arithmetic, for any source operand (`readSrc`) and with
the carry flag they read and write: `mov`, `add`, `adc`, `sub`, `sbb`, the
logical operations, `cmp` and `mul` (`edx:eax`); and the loads and stores of
the working space, through `edi` or `ebp`.
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- `add`/`adc` of two words and a carry, as numbers. -/
theorem add3_toNat (a b : BitVec 32) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 32).toNat = (a.toNat + b.toNat + c.toNat) % 2 ^ 32 := by
  rw [BitVec.toNat_add, BitVec.toNat_add, Nat.mod_add_mod]
  cases c <;> rfl

/-- `sbb` of two words and a borrow, as numbers. -/
theorem sub3_toNat (a b : BitVec 32) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 32).toNat =
      (a.toNat + 2 ^ 32 * 2 - b.toNat - c.toNat) % 2 ^ 32 := by
  have ha := a.isLt
  have hb := b.isLt
  cases c <;> simp only [BitVec.toNat_sub, Bool.toNat_false, Bool.toNat_true] <;> simp <;> omega

/-- The words of a product. -/
theorem mul_words (a b : BitVec 32) :
    (BitVec.ofNat 32 (a.toNat * b.toNat)).toNat +
      2 ^ 32 * (BitVec.ofNat 32 (a.toNat * b.toNat / 2 ^ 32)).toNat = a.toNat * b.toNat ∧
    a.toNat * b.toNat / 2 ^ 32 < 2 ^ 32 - 1 := by
  have ha := a.isLt
  have hb := b.isLt
  have h : a.toNat * b.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hq : a.toNat * b.toNat / 2 ^ 32 < 2 ^ 32 - 1 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
  simp only [BitVec.toNat_ofNat]
  refine ⟨?_, hq⟩
  rw [Nat.mod_eq_of_lt (a := _ / 2 ^ 32) (by omega)]
  omega

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, src`. -/
theorem wp_movS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d v → t.cf = s.cf → WP isa (.block is) t Q) :
    WP isa (.block (.mov d src :: is)) s Q :=
  cons (s' := s.setReg d v) (by simp only [exec, h, Option.map_some]) (k _ (Upd.setReg _ _ _) rfl)

/-- `add d, src`, and the carry. -/
theorem wp_addS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d + v) →
      t.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `adc d, src`, with the carry `c`, and the carry out. -/
theorem wp_adcS {d : Reg} {src : Src} {v : BitVec 32} {c : Bool} (h : readSrc s src = some v)
    (hc : s.cf = some c)
    (k : ∀ t, Upd s t d (s.gpr d + v + (BitVec.ofBool c).setWidth 32) →
      t.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat + c.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .adc d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some, hc, Option.map_some]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `sub d, src`, and the borrow. -/
theorem wp_subS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d - v) →
      t.cf = some (decide ((s.gpr d).toNat < v.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .sub d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `sbb d, src`, with the borrow `c`, and the borrow out. -/
theorem wp_sbbS {d : Reg} {src : Src} {v : BitVec 32} {c : Bool} (h : readSrc s src = some v)
    (hc : s.cf = some c)
    (k : ∀ t, Upd s t d (s.gpr d - v - (BitVec.ofBool c).setWidth 32) →
      t.cf = some (decide ((s.gpr d).toNat < v.toNat + c.toNat)) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .sbb d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some, hc, Option.map_some]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `and`/`xor d, src`. -/
theorem wp_logicS {op : AluOp} (hop : op = .and ∨ op = .xor) {d : Reg} {src : Src} {v : BitVec 32}
    (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (if op = .and then s.gpr d &&& v else s.gpr d ^^^ v) → WP isa (.block is) t Q) :
    WP isa (.block (.alu op d src :: is)) s Q := by
  rcases hop with rfl | rfl
  · exact cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _))
  · exact cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

/-- `or d, src`. -/
theorem wp_orS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d ||| v) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .or d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

/-- `cmp d, src`: ZF is `d = src`. -/
theorem wp_cmpS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Fupd s t → t.zf = some (s.gpr d - v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp d src :: is)) s Q :=
  cons (s' := arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat)) (subOverflow (s.gpr d) v (s.gpr d - v)))
    (by simp only [exec, execAlu, h, Option.bind_some])
    (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)

/-- What `mul r` leaves: `edx:eax = eax · r`, and the rest. -/
structure MulUpd (s t : State) (r : Reg) : Prop where
  eax : t.gpr .eax = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat)
  edx : t.gpr .edx = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat / 2 ^ 32)
  other : ∀ q, q ≠ .eax → q ≠ .edx → t.gpr q = s.gpr q
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- `mul r`. -/
theorem wp_mul {r : Reg} (k : ∀ t, VG.Proof.Mont.X86.MulUpd s t r → WP isa (.block is) t Q) :
    WP isa (.block (.mul r :: is)) s Q := by
  refine cons (s' := execMul r s) rfl (k _ ⟨?_, ?_, fun q h1 h2 => ?_, rfl, rfl, rfl⟩)
  · simp only [execMul, State.setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [execMul, State.setReg, ite_true]
  · simp only [execMul, State.setReg, State.setFlags, h1, h2, ite_false]

/-- `mov [m], r`. -/
theorem wp_storeS {r : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hw : InRegions s.wr a 4)
    (k : ∀ t, Mupd s t (s.mem.writeW a (s.gpr r)) → WP isa (.block is) t Q) :
    WP isa (.block (.store m r :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) (by simp only [exec, ha, State.store32, hw, ite_true])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-- A load of the working space through `edi`. -/
theorem readSrc_sc {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86.Scr s base size) {d : Nat}
    (hd : d + 4 ≤ size) : readSrc s (.mem (sc d)) = some (s.mem.readW (off base d) 32) := by
  show s.load32 (s.ea (sc d)) = _
  rw [hs.ea (by omega), State.load32, ite_eq_left_iff.mpr fun h => absurd (hs.read hd) h]

/-- A load of the working space through `ebp`, at `4i` bytes into it. -/
theorem readSrc_at {s : State} {base : Addr} {size : Nat} (hs : VG.Proof.Mont.X86.Scr s base size) {i d : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hd : 4 * i + d + 4 ≤ size) :
    readSrc s (.mem (at_ .ebp d)) = some (s.mem.readW (off base (4 * i + d)) 32) := by
  show s.load32 (s.ea (at_ .ebp d)) = _
  rw [hs.ea_at hp (by omega), State.load32, ite_eq_left_iff.mpr fun h => absurd (hs.read hd) h]

theorem _root_.VG.X86.Wp.Upd.keeps {s t : State} {d : Reg} {v : BitVec 32} (h : Upd s t d v) : VG.Proof.Mont.X86.Keeps [d] s t :=
  ⟨fun r hr => h.other r (by simpa using hr), h.rd, h.wr⟩

theorem MulUpd.keeps {s t : State} {r : Reg} (h : VG.Proof.Mont.X86.MulUpd s t r) : VG.Proof.Mont.X86.Keeps [.eax, .edx] s t :=
  ⟨fun q hq => h.other q (by simp_all) (by simp_all), h.rd, h.wr⟩

theorem _root_.VG.X86.Wp.Mupd.keeps {s t : State} {m : Mem} (h : Mupd s t m) (rs : List Reg) : VG.Proof.Mont.X86.Keeps rs s t :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr⟩

theorem _root_.VG.X86.Wp.Fupd.keeps {s t : State} (h : Fupd s t) (rs : List Reg) : VG.Proof.Mont.X86.Keeps rs s t :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr⟩

/-- `Keeps` of a list of registers, widened to a larger one and composed. -/
theorem Keeps.widen {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Mont.X86.Keeps rs' s₁ s₂) (h₂ : VG.Proof.Mont.X86.Keeps rs s₂ s₃)
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : VG.Proof.Mont.X86.Keeps rs' s₁ s₃ :=
  h₁.trans (h₂.mono hs)

end VG.Proof.Mont.X86

end
