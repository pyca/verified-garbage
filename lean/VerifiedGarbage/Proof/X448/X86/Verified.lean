import VerifiedGarbage.Impl.X448.X86
import VerifiedGarbage.Proof.X448.Encoding
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.X25519.X86.Verified
import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.X448.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Mem`. -/
section

/-!
# X448 on x86 (32-bit): the working space
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 32 := m.readW (VG.Proof.X448.X86.off base d) 32
abbrev limbs (m : Mem) (base : Addr) (o : Nat) (i : Nat) : Nat := (VG.Proof.X448.X86.word m base (o + 4 * i)).toNat
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat := VG.Proof.X448.Radix16.valN (VG.Proof.X448.X86.limbs m base o) 28

def Bounded (m : Mem) (base : Addr) (o : Nat) : Prop := ∀ i < 28, VG.Proof.X448.X86.limbs m base o i < VG.Proof.X448.Radix16.radix

/-- The registers and permissions that an arithmetic operation preserves. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.refl (rs : List Reg) (s : State) : VG.Proof.X448.X86.Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X448.X86.Keeps rs s₁ s₂) (h₂ : VG.Proof.X448.X86.Keeps rs s₂ s₃) :
    VG.Proof.X448.X86.Keeps rs s₁ s₃ := ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1,
      h₂.2.2.trans h₁.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.X448.X86.Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.X448.X86.Keeps rs' s s' := ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keeps.then {rs rs' : List Reg} {s t u : State} (h : VG.Proof.X448.X86.Keeps rs s t) (h' : VG.Proof.X448.X86.Keeps rs' t u) :
    VG.Proof.X448.X86.Keeps (rs ++ rs') s u :=
  (h.mono (fun _ hr => List.mem_append_left _ hr)).trans
    (h'.mono (fun _ hr => List.mem_append_right _ hr))

structure Scr (s : State) (base : Addr) : Prop where
  edi : (s.gpr .edi).setWidth 64 = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : (s.gpr .edi).toNat + 8192 ≤ 2 ^ 32

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base)
    (h : VG.Proof.X448.X86.Keeps rs s s') (hr : .edi ∉ rs) : VG.Proof.X448.X86.Scr s' base :=
  ⟨by rw [h.1 _ hr]; exact hs.edi, h.2.2 ▸ hs.wr,
    by rw [h.1 _ hr]; exact hs.nowrap⟩

theorem Scr.ea {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {d : Nat} (hd : d < 8192) :
    s.ea (VG.Impl.X448.X86.sc d) = VG.Proof.X448.X86.off base d := by
  change VG.X86.addr (s.gpr .edi) d = _
  rw [addr_eq (by have := hs.nowrap; omega), hs.edi]

theorem contains_sc {base : Addr} {d n : Nat} (h : d + n ≤ 8192) :
    (⟨base, 8192⟩ : Region).Contains (VG.Proof.X448.X86.off base d) n :=
  Offset.contains_base base h (by omega)

theorem Scr.read {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (VG.Proof.X448.X86.off base d) n :=
  ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X448.X86.contains_sc hd⟩

theorem Scr.write {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions s.wr (VG.Proof.X448.X86.off base d) n := ⟨_, hs.wr, VG.Proof.X448.X86.contains_sc hd⟩

abbrev ofs (base x : Addr) : Nat := (x - base).toNat

def Outside (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (VG.Proof.X448.X86.ofs base x < o ∨ o + n ≤ VG.Proof.X448.X86.ofs base x) → m' x = m x

theorem Outside.refl (base : Addr) (o n : Nat) (m : Mem) : VG.Proof.X448.X86.Outside base o n m m := fun _ _ => rfl

theorem Outside.trans {base : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.X448.X86.Outside base o n m₁ m₂)
    (h₂ : VG.Proof.X448.X86.Outside base o n m₂ m₃) : VG.Proof.X448.X86.Outside base o n m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Outside.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.Outside base o n m m')
    (hl : o' ≤ o) (hr : o + n ≤ o' + n') : VG.Proof.X448.X86.Outside base o' n' m m' :=
  fun x hx => h x (by omega)

theorem ofs_off (base : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    VG.Proof.X448.X86.ofs base (VG.Proof.X448.X86.off base d + BitVec.ofNat 64 i) = d + i := by
  simp only [VG.Proof.X448.X86.ofs, VG.Proof.X448.X86.off]
  rw [Offset.add_add, Mem.sub_ofNat_toNat base h]

theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.Outside base o n m m') {d : Nat}
    (hd : d + 4 ≤ o ∨ o + n ≤ d) (hd' : d + 4 ≤ 8192) : VG.Proof.X448.X86.word m' base d = VG.Proof.X448.X86.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.X86.ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.limbs {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.Outside base o n m m') {d : Nat}
    (hd : d + 112 ≤ o ∨ o + n ≤ d) (hd' : d + 112 ≤ 8192) {i : Nat} (hi : i < 28) :
    VG.Proof.X448.X86.limbs m' base d i = VG.Proof.X448.X86.limbs m base d i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega))

theorem Outside.fe {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.Outside base o n m m') {d : Nat}
    (hd : d + 112 ≤ o ∨ o + n ≤ d) (hd' : d + 112 ≤ 8192) : VG.Proof.X448.X86.fe m' base d = VG.Proof.X448.X86.fe m base d :=
  VG.Proof.X448.Radix16.valN_congr fun _ hi => h.limbs hd hd' hi

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 32) (h : d + 4 ≤ 8192) :
    VG.Proof.X448.X86.Outside base d 4 m (m.writeW (VG.Proof.X448.X86.off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [VG.Proof.X448.X86.ofs] at hx
  omega

theorem word_write (m : Mem) (base : Addr) {o i j : Nat} (ho : o + 4 * (i + 1) ≤ 8192)
    (hj : o + 4 * (j + 1) ≤ 8192) (v : BitVec 32) :
    VG.Proof.X448.X86.word (m.writeW (VG.Proof.X448.X86.off base (o + 4 * i)) v) base (o + 4 * j) =
      if j = i then v else VG.Proof.X448.X86.word m base (o + 4 * j) := by
  by_cases h : j = i
  · rw [ite_eq_left h, h, VG.Proof.X448.X86.word, Mem.readW_writeW_self32]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- A field operation writes its result and its temporary coefficients. -/
def FieldMem (base : Addr) (o : Nat) (m m' : Mem) : Prop :=
  ∀ x, (VG.Proof.X448.X86.ofs base x < o ∨ o + 112 ≤ VG.Proof.X448.X86.ofs base x) →
    (VG.Proof.X448.X86.ofs base x < ACC ∨ ACC + 512 ≤ VG.Proof.X448.X86.ofs base x) → m' x = m x

theorem FieldMem.refl (base : Addr) (o : Nat) (m : Mem) : VG.Proof.X448.X86.FieldMem base o m m := fun _ _ _ => rfl

theorem FieldMem.trans {base : Addr} {o : Nat} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.X448.X86.FieldMem base o m₁ m₂)
    (h₂ : VG.Proof.X448.X86.FieldMem base o m₂ m₃) : VG.Proof.X448.X86.FieldMem base o m₁ m₃ :=
  fun x hx hw => (h₂ x hx hw).trans (h₁ x hx hw)

theorem FieldMem.output {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.Outside base o 112 m m') :
    VG.Proof.X448.X86.FieldMem base o m m' := fun x hx _ => h x hx

theorem FieldMem.work {base : Addr} {o d n : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.Outside base d n m m')
    (hl : ACC ≤ d) (hr : d + n ≤ ACC + 512) : VG.Proof.X448.X86.FieldMem base o m m' :=
  fun x _ hx => h.mono hl hr x hx

theorem FieldMem.word {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.FieldMem base o m m') {d : Nat}
    (hd : d + 4 ≤ o ∨ o + 112 ≤ d) (hw : d + 4 ≤ ACC) : VG.Proof.X448.X86.word m' base d = VG.Proof.X448.X86.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.X86.ofs_off base (by simp only [ACC] at hw; omega)]; omega)
    (Or.inl (by rw [VG.Proof.X448.X86.ofs_off base (by simp only [ACC] at hw; omega)]; omega))).symm).symm

theorem FieldMem.limbs {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.FieldMem base o m m') {d : Nat}
    (hd : d + 112 ≤ o ∨ o + 112 ≤ d) (hw : d + 112 ≤ ACC) {i : Nat} (hi : i < 28) :
    VG.Proof.X448.X86.limbs m' base d i = VG.Proof.X448.X86.limbs m base d i :=
  congrArg BitVec.toNat (h.word (by omega) (by omega))

theorem FieldMem.fe {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.FieldMem base o m m') {d : Nat}
    (hd : d + 112 ≤ o ∨ o + 112 ≤ d) (hw : d + 112 ≤ ACC) : VG.Proof.X448.X86.fe m' base d = VG.Proof.X448.X86.fe m base d :=
  VG.Proof.X448.Radix16.valN_congr fun _ hi => h.limbs hd hw hi

/-- Memory outside two ranges, used by the conditional swap. -/
def Outside2 (base : Addr) (x nx y ny : Nat) (m m' : Mem) : Prop :=
  ∀ p, (VG.Proof.X448.X86.ofs base p < x ∨ x + nx ≤ VG.Proof.X448.X86.ofs base p) →
    (VG.Proof.X448.X86.ofs base p < y ∨ y + ny ≤ VG.Proof.X448.X86.ofs base p) → m' p = m p

theorem Outside2.refl (base : Addr) (x nx y ny : Nat) (m : Mem) : VG.Proof.X448.X86.Outside2 base x nx y ny m m :=
  fun _ _ _ => rfl

theorem Outside2.trans {base : Addr} {x nx y ny : Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : VG.Proof.X448.X86.Outside2 base x nx y ny m₁ m₂) (h₂ : VG.Proof.X448.X86.Outside2 base x nx y ny m₂ m₃) :
    VG.Proof.X448.X86.Outside2 base x nx y ny m₁ m₃ := fun p hx hy => (h₂ p hx hy).trans (h₁ p hx hy)

theorem Outside2.mono {base : Addr} {x nx y ny nx' ny' : Nat} {m m' : Mem}
    (h : VG.Proof.X448.X86.Outside2 base x nx y ny m m') (hx : nx ≤ nx') (hy : ny ≤ ny') :
    VG.Proof.X448.X86.Outside2 base x nx' y ny' m m' := fun p hp hq => h p (by omega) (by omega)

theorem Outside2.word {base : Addr} {x nx y ny : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.Outside2 base x nx y ny m m')
    {d : Nat} (hx : d + 4 ≤ x ∨ x + nx ≤ d) (hy : d + 4 ≤ y ∨ y + ny ≤ d) (hd : d + 4 ≤ 8192) :
    VG.Proof.X448.X86.word m' base d = VG.Proof.X448.X86.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.X86.ofs_off base (by omega)]; omega)
    (by rw [VG.Proof.X448.X86.ofs_off base (by omega)]; omega)).symm).symm

/-- Aligned word stores read back as an update at one byte offset. -/
theorem word_write_aligned (m : Mem) (base : Addr) {d e : Nat} (hd : d + 4 ≤ 8192)
    (he : e + 4 ≤ 8192) (hdm : d % 4 = 0) (hem : e % 4 = 0) (v : BitVec 32) :
    VG.Proof.X448.X86.word (m.writeW (VG.Proof.X448.X86.off base d) v) base e = if e = d then v else VG.Proof.X448.X86.word m base e := by
  by_cases h : e = d
  · rw [ite_eq_left h, h, VG.Proof.X448.X86.word, Mem.readW_writeW_self32]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Instr`. -/
section

/-!
# X448 on x86 (32-bit): instruction rules

Single-step rules expose register and memory updates while keeping the rest of
each state folded.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

structure Upd (s t : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : t.gpr d = v
  other : ∀ r, r ≠ d → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : VG.Proof.X448.X86.Upd s (s.setReg d v) d v :=
  ⟨RegUpd.gpr_setReg_self _ _ _, fun _ h => RegUpd.gpr_setReg_of_ne _ _ h, rfl, rfl, rfl⟩

theorem Upd.flags (s : State) (d : Reg) (v : BitVec 32) (cf of zf sf : Option Bool) :
    VG.Proof.X448.X86.Upd s ((s.setFlags cf of zf sf).setReg d v) d v :=
  ⟨RegUpd.gpr_setReg_self _ _ _, fun _ h => RegUpd.gpr_setReg_of_ne _ _ h, rfl, rfl, rfl⟩

theorem Upd.rest {s t : State} {d : Reg} {v : BitVec 32} (h : VG.Proof.X448.X86.Upd s t d v) {rs : List Reg}
    (hd : d ∈ rs) : VG.Proof.X448.X86.Keeps rs s t :=
  ⟨fun r hr => h.other r (fun e => hr (e ▸ hd)), h.rd, h.wr⟩

structure Mupd (s t : State) (m : Mem) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = m
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Mupd.rest {s t : State} {m : Mem} (h : VG.Proof.X448.X86.Mupd s t m) (rs : List Reg) : VG.Proof.X448.X86.Keeps rs s t :=
  ⟨fun r _ => congrFun h.gpr r, h.rd, h.wr⟩

structure Fupd (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Fupd.rest {s t : State} (h : VG.Proof.X448.X86.Fupd s t) (rs : List Reg) : VG.Proof.X448.X86.Keeps rs s t :=
  ⟨fun r _ => congrFun h.gpr r, h.rd, h.wr⟩

theorem Scr.of_upd {s t : State} {base : Addr} {d : Reg} {v : BitVec 32}
    (hs : VG.Proof.X448.X86.Scr s base) (h : VG.Proof.X448.X86.Upd s t d v) (hd : .edi ≠ d) : VG.Proof.X448.X86.Scr t base :=
  ⟨by rw [h.other _ hd]; exact hs.edi, h.wr ▸ hs.wr,
    by rw [h.other _ hd]; exact hs.nowrap⟩

theorem WP.cons {i : Instr} {is : List Instr} {s t : State} {Q : State → Prop}
    (h : exec i s = some t) (k : WP isa (.block is) t Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨t, h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d : Reg} {src : Src} {v : BitVec 32} (h : VG.X86.readSrc s src = some v)
    (k : ∀ t, VG.Proof.X448.X86.Upd s t d v → WP isa (.block is) t Q) : WP isa (.block (.mov d src :: is)) s Q :=
  WP.cons (by simp only [exec, h, Option.map_some]) (k _ (Upd.setReg _ _ _))

/-- The ALU operations that write their result and do not read carry. -/
def plain (op : AluOp) : Prop := op = .add ∨ op = .sub ∨ op = .and ∨ op = .or ∨ op = .xor

def aluVal (op : AluOp) (a b : BitVec 32) : BitVec 32 := match op with
  | .add => a + b | .sub => a - b | .and => a &&& b | .or => a ||| b | .xor => a ^^^ b | _ => 0

theorem wp_alu {op : AluOp} {d : Reg} {src : Src} {v : BitVec 32} (hop : VG.Proof.X448.X86.plain op)
    (h : VG.X86.readSrc s src = some v)
    (k : ∀ t, VG.Proof.X448.X86.Upd s t d (VG.Proof.X448.X86.aluVal op (s.gpr d) v) →
      t.zf = some (VG.Proof.X448.X86.aluVal op (s.gpr d) v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu op d src :: is)) s Q := by
  rcases hop with rfl | rfl | rfl | rfl | rfl <;>
    refine WP.cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _ _) rfl)

theorem wp_shift {op : ShiftOp} {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ t, VG.Proof.X448.X86.Upd s t d (match op with | .shr => s.gpr d >>> n | .ror => (s.gpr d).rotateRight n) →
      WP isa (.block is) t Q) : WP isa (.block (.shift op d n :: is)) s Q := by
  cases op <;> refine WP.cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _ _))

theorem wp_load {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hr : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ t, VG.Proof.X448.X86.Upd s t d (s.mem.readW a 32) → WP isa (.block is) t Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q :=
  VG.Proof.X448.X86.wp_mov (by simp only [VG.X86.readSrc, ha, State.load32, hr, ite_true]) k

theorem wp_store {r : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hw : InRegions s.wr a 4)
    (k : ∀ t, VG.Proof.X448.X86.Mupd s t (s.mem.writeW a (s.gpr r)) → WP isa (.block is) t Q) :
    WP isa (.block (.store m r :: is)) s Q :=
  WP.cons (t := {s with mem := s.mem.writeW a (s.gpr r)}) (by simp only [exec, ha, State.store32, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl⟩)

theorem wp_load8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hr : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ t, VG.Proof.X448.X86.Upd s t d ((s.mem a).setWidth 32) → WP isa (.block is) t Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q :=
  WP.cons (by simp only [exec, ha, State.load8, hr, ite_true, Option.map_some])
    (k _ (Upd.setReg _ _ _))

theorem wp_store8 {r : Reg8} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hw : InRegions s.wr a 1)
    (k : ∀ t, VG.Proof.X448.X86.Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  WP.cons (t := {s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8)}) (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl⟩)


theorem load_ok {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {d : Reg} {o : Nat} (ho : o + 4 ≤ 8192)
    (k : ∀ t, VG.Proof.X448.X86.Upd s t d (VG.Proof.X448.X86.word s.mem base o) → WP isa (.block is) t Q) :
    WP isa (.block (ld d o :: is)) s Q :=
  VG.Proof.X448.X86.wp_load (hs.ea (by omega)) (hs.read ho) k

theorem store_ok {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {r : Reg} {o : Nat} (ho : o + 4 ≤ 8192)
    (k : ∀ t, VG.Proof.X448.X86.Mupd s t (s.mem.writeW (VG.Proof.X448.X86.off base o) (s.gpr r)) → WP isa (.block is) t Q) :
    WP isa (.block (st r o :: is)) s Q :=
  VG.Proof.X448.X86.wp_store (hs.ea (by omega)) (hs.write ho) k


theorem wp_mul {r : Reg}
    (k : ∀ t, t.gpr .eax = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat) →
      t.mem = s.mem → VG.Proof.X448.X86.Keeps [.eax, .edx] s t → WP isa (.block is) t Q) :
    WP isa (.block (.mul r :: is)) s Q := by
  refine WP.cons (t := execMul r s) rfl (k _ ?_ rfl ⟨?_, rfl, rfl⟩)
  · simp only [execMul, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true]
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [execMul, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hq.1, hq.2, ite_false]


theorem wp_cmp {r : Reg} {src : Src} {v : BitVec 32} (h : VG.X86.readSrc s src = some v)
    (k : ∀ t, VG.Proof.X448.X86.Fupd s t → t.zf = some (s.gpr r - v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .cmp r src :: is)) s Q :=
  WP.cons (t := arithFlags s (s.gpr r - v) ((s.gpr r).toNat < v.toNat)
    (subOverflow (s.gpr r) v (s.gpr r - v)))
    (by simp only [exec, execAlu, h, Option.bind_some]) (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl)

end

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Step`. -/
section

/-!
# X448 on x86 (32-bit): carry steps

A bounded sum splits into a 16-bit digit and a carry before the next
coefficient is added.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem and16_nat (v : BitVec 32) : (v &&& (65535 : BitVec 32)).toNat = v.toNat % VG.Proof.X448.Radix16.radix := by
  rw [BitVec.toNat_and, show (65535 : BitVec 32).toNat = 2 ^ 16 - 1 by rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem carryRaw_ok {s : State} {rb : Reg} {d : Nat} {a : Addr}
    (hr : rb ∉ [.eax, .ebx, .edx]) (ha : s.ea (VG.Impl.X448.X86.at_ rb d) = a) (hw : InRegions s.wr a 4)
    (hb : (s.gpr .eax).toNat + (s.gpr .ebx).toNat < 2 ^ 32) :
    let v := (s.gpr .eax).toNat + (s.gpr .ebx).toNat
    WP isa (.block (VG.Impl.X448.X86.carryStep rb d)) s fun t =>
      (t.gpr .ebx).toNat = v / VG.Proof.X448.Radix16.radix ∧
      t.mem = s.mem.writeW a (BitVec.ofNat 32 (v % VG.Proof.X448.Radix16.radix)) ∧ VG.Proof.X448.X86.Keeps [.eax, .ebx, .edx] s t := by
  intro v
  have hsum : (s.gpr .ebx + s.gpr .eax).toNat = v := by rw [BitVec.add_comm, BitVec.toNat_add, Nat.mod_eq_of_lt hb]
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  have mask : (s.gpr .ebx + s.gpr .eax) &&& (65535 : BitVec 32) = BitVec.ofNat 32 (v % VG.Proof.X448.Radix16.radix) := by
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.X448.X86.and16_nat, hsum, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := v % VG.Proof.X448.Radix16.radix) (Nat.lt_trans (Nat.mod_lt v (by decide : 0 < VG.Proof.X448.Radix16.radix)) (by decide : VG.Proof.X448.Radix16.radix < 2 ^ 32))]
  have hn : 1 ≤ (16 : Nat) ∧ 16 ≤ 31 := by decide
  simp only [State.ea, VG.Impl.X448.X86.at_] at ha
  apply WP.of_runBlock
  simp only [VG.Impl.X448.X86.carryStep, runBlock_cons, runStep_some, runBlock_nil, exec,
    execAlu, execShift, VG.X86.readSrc, Option.bind_some, Option.map_some,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.mem_setFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    State.ea, VG.Impl.X448.X86.at_, hr.2.1, hr.2.2, hn, and_self,
    ite_true, ite_false, reduceCtorEq, ha, State.store32, hw,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [BitVec.toNat_ushiftRight, hsum, Nat.shiftRight_eq_div_pow]; rfl
  · rw [mask]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.2.1, hr.2.2, ite_false]

/-- Load a coefficient and propagate its carry. -/
def carryBlock (o a i : Nat) : List Instr :=
  [ld .eax (a + 4 * i)] ++ VG.Impl.X448.X86.carryStep .edi (o + 4 * i)

theorem carryStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {o a i : Nat}
    (ho : o + 4 * i + 4 ≤ 4096) (ha : a + 4 * i + 4 ≤ 4096)
    (hb : (VG.Proof.X448.X86.word s.mem base (a + 4 * i)).toNat + (s.gpr .ebx).toNat < 2 ^ 32) :
    let v := (VG.Proof.X448.X86.word s.mem base (a + 4 * i)).toNat + (s.gpr .ebx).toNat
    WP isa (.block (VG.Proof.X448.X86.carryBlock o a i)) s fun t =>
      (t.gpr .ebx).toNat = v / VG.Proof.X448.Radix16.radix ∧
      t.mem = s.mem.writeW (VG.Proof.X448.X86.off base (o + 4 * i)) (BitVec.ofNat 32 (v % VG.Proof.X448.Radix16.radix)) ∧
      VG.Proof.X448.X86.Keeps [.eax, .ebx, .edx] s t := by
  intro v
  unfold VG.Proof.X448.X86.carryBlock
  refine VG.Proof.X448.X86.load_ok hs (by omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide)
  refine WP.mono (VG.Proof.X448.X86.carryRaw_ok (by decide) (ts.ea (by omega)) (ts.write (by omega))
    (by rw [ht.gpr, ht.other .ebx (by decide)]; exact hb)) fun u ⟨uc, um, uk⟩ => ?_
  rw [ht.gpr, ht.other .ebx (by decide)] at uc um
  exact ⟨uc, by rw [um, ht.mem], (ht.rest (by decide)).trans uk⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Carry`. -/
section

/-!
# X448 on x86 (32-bit): carry propagation
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16
theorem zeroCarry_ok (s : State) :
    WP isa (.block [.mov .ebx (.imm 0)]) s fun t =>
      t.gpr .ebx = 0 ∧ t.mem = s.mem ∧ VG.Proof.X448.X86.Keeps [.eax, .ebx, .edx] s t := by
  refine VG.Proof.X448.X86.wp_mov rfl fun t ht => WP.block_nil
    ⟨ht.gpr, ht.mem, ht.rest (by decide)⟩

/-- An in-place pass only overwrites input limbs it has already consumed. -/
theorem pass_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {o a : Nat}
    (ho : o + 112 ≤ 4096) (ha : a + 112 ≤ 4096)
    (hsep : o = a ∨ o + 112 ≤ a ∨ a + 112 ≤ o)
    {f : Nat → Nat} (hf : ∀ i < 28, VG.Proof.X448.X86.limbs s.mem base a i = f i)
    (hb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix) :
    WP isa (.block (pass o a)) s fun s' =>
      (∀ i < 28, VG.Proof.X448.X86.limbs s'.mem base o i = VG.Proof.X448.Radix16.digit f i) ∧
      (s'.gpr .ebx).toNat = VG.Proof.X448.Radix16.carry f 28 ∧ VG.Proof.X448.X86.Outside base o 112 s.mem s'.mem ∧
      VG.Proof.X448.X86.Keeps [.eax, .ebx, .edx] s s' := by
  let inv := fun k (t : State) =>
    (∀ i < k, VG.Proof.X448.X86.limbs t.mem base o i = VG.Proof.X448.Radix16.digit f i) ∧
    (∀ i, k ≤ i → i < 28 → VG.Proof.X448.X86.limbs t.mem base a i = f i) ∧
    (t.gpr .ebx).toNat = VG.Proof.X448.Radix16.carry f k ∧ VG.Proof.X448.X86.Outside base o 112 s.mem t.mem ∧
    VG.Proof.X448.X86.Keeps [.eax, .ebx, .edx] s t
  have step : ∀ k t, k < 28 → inv k t → WP isa (.block (VG.Proof.X448.X86.carryBlock o a k)) t (inv (k + 1)) := by
    intro k t hk ⟨hlo, hhi, hc, hm, ht⟩
    have hts := hs.of_keeps ht (by decide)
    have he := hhi k (by omega) hk
    have hsum : (VG.Proof.X448.X86.word t.mem base (a + 4 * k)).toNat + (t.gpr .ebx).toNat < 2 ^ 32 := by
      change VG.Proof.X448.X86.limbs t.mem base a k + (t.gpr .ebx).toNat < _
      rw [he, hc]
      have hcoeff := hb k hk
      have hcarry := VG.Proof.X448.Radix16.carry_bound (n := k) (fun i hi => hb i (by omega))
      simp only [VG.Proof.X448.Radix16.radix] at hcoeff
      omega
    refine WP.mono (VG.Proof.X448.X86.carryStep_ok hts (by omega) (by omega) hsum) fun u ⟨hu, hmem, huKeep⟩ => ?_
    have he' : (VG.Proof.X448.X86.word t.mem base (a + 4 * k)).toNat + (t.gpr .ebx).toNat = f k + VG.Proof.X448.Radix16.carry f k := by
      change VG.Proof.X448.X86.limbs t.mem base a k + (t.gpr .ebx).toNat = _
      rw [he, hc]
    rw [he'] at hu hmem
    have out : VG.Proof.X448.X86.Outside base (o + 4 * k) 4 t.mem u.mem := by
      rw [hmem]
      exact VG.Proof.X448.X86.writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, hu, hm.trans (out.mono (by omega) (by omega)), ht.trans huKeep⟩
    · intro i hi
      change (VG.Proof.X448.X86.word u.mem base (o + 4 * i)).toNat = _
      rw [hmem, VG.Proof.X448.X86.word_write t.mem base (by omega) (by omega)]
      by_cases hik : i = k
      · rw [ite_eq_left hik, hik, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (f k + VG.Proof.X448.Radix16.carry f k) % VG.Proof.X448.Radix16.radix)
          (Nat.lt_trans (VG.Proof.X448.Radix16.digit_lt f k) (by decide))]
        rfl
      · rw [ite_eq_right hik]
        exact hlo i (by omega)
    · intro i hi hi'
      have sep : a + 4 * i + 4 ≤ o + 4 * k ∨ o + 4 * k + 4 ≤ a + 4 * i := by
        rcases hsep with h | h | h <;> omega
      change (VG.Proof.X448.X86.word u.mem base (a + 4 * i)).toNat = _
      rw [out.word sep (by omega)]
      exact hhi i (by omega) hi'
  change WP isa (.block ([.mov .ebx (.imm 0)] ++ (List.range 28).flatMap (VG.Proof.X448.X86.carryBlock o a))) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.zeroCarry_ok s) fun t ⟨hc, hm, ht⟩ => ?_
  refine WP.mono (wp_range_flatMap inv step 28 (by decide) t ?_) fun u ⟨hlo, _, hc, hm, ht⟩ =>
    ⟨hlo, hc, hm, ht⟩
  refine ⟨fun i hi => by omega, (fun i _ hi => ?_), ?_, ?_, ht⟩
  · rw [hm]; exact hf i hi
  · rw [hc]; rfl
  · rw [hm]; exact Outside.refl _ _ _ _

theorem foldStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {d : Nat}
    (hd : d + 4 ≤ 4096) :
    WP isa (.block [ld .eax d, .alu .add .eax (.reg .ebx), st .eax d]) s
      fun t => t.mem = s.mem.writeW (VG.Proof.X448.X86.off base d) (VG.Proof.X448.X86.word s.mem base d + s.gpr .ebx) ∧
        VG.Proof.X448.X86.Keeps [.eax] s t := by
  refine VG.Proof.X448.X86.load_ok hs (by omega) fun t ht => ?_
  refine VG.Proof.X448.X86.wp_alu (Or.inl rfl) rfl fun u hu _ => ?_
  refine VG.Proof.X448.X86.store_ok ((hs.of_upd ht (by decide)).of_upd hu (by decide)) (by omega)
    fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr]
    change s.mem.writeW _ (t.gpr .eax + t.gpr .ebx) = _
    rw [ht.gpr, ht.other .ebx (by decide)]
  · exact (ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _))


theorem foldLimb_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {k : Nat} (hk : k < 28)
    (hb : VG.Proof.X448.X86.limbs s.mem base TMP k + (s.gpr .ebx).toNat < 2 ^ 32) :
    WP isa (.block [ld .eax (TMP + 4 * k), .alu .add .eax (.reg .ebx),
      st .eax (TMP + 4 * k)]) s fun t =>
      (∀ i < 28, VG.Proof.X448.X86.limbs t.mem base TMP i =
        if i = k then VG.Proof.X448.X86.limbs s.mem base TMP i + (s.gpr .ebx).toNat else VG.Proof.X448.X86.limbs s.mem base TMP i) ∧
      VG.Proof.X448.X86.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax] s t := by
  have hd : TMP + 4 * k + 4 ≤ 4096 := by simp only [TMP]; omega
  refine WP.mono (VG.Proof.X448.X86.foldStep_ok hs hd) fun t ⟨hm, ht⟩ => ?_
  refine ⟨?_, ?_, ht⟩
  · intro i hi
    change (VG.Proof.X448.X86.word t.mem base (TMP + 4 * i)).toNat = _
    rw [hm, VG.Proof.X448.X86.word_write s.mem base (by omega) (by simp only [TMP]; omega)]
    by_cases h : i = k
    · rw [ite_eq_left h, ite_eq_left h, h, BitVec.toNat_add, Nat.mod_eq_of_lt hb]
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [hm]
    exact (VG.Proof.X448.X86.writeW_outside _ _ _ (by omega : TMP + 4 * k + 4 ≤ 8192)).mono (by omega) (by omega)

/-- The two stores implement the mathematical carry fold. -/
theorem fold_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 28, VG.Proof.X448.X86.limbs s.mem base TMP i = VG.Proof.X448.Radix16.digit f i)
    (hc : (s.gpr .ebx).toNat = VG.Proof.X448.Radix16.carry f 28) (hb : VG.Proof.X448.Radix16.carry f 28 < 2 ^ 16) :
    WP isa (.block VG.Impl.X448.X86.fold) s fun s' =>
      (∀ i < 28, VG.Proof.X448.X86.limbs s'.mem base TMP i = VG.Proof.X448.Radix16.folded f i) ∧
      VG.Proof.X448.X86.Outside base TMP 112 s.mem s'.mem ∧ VG.Proof.X448.X86.Keeps [.eax] s s' := by
  have bound : ∀ i < 28, VG.Proof.X448.Radix16.digit f i + VG.Proof.X448.Radix16.carry f 28 < 2 ^ 32 := by
    intro i _
    have h := VG.Proof.X448.Radix16.digit_lt f i
    simp only [VG.Proof.X448.Radix16.radix] at h
    omega
  change WP isa (.block
    (([ld .eax (TMP + 4 * 0), .alu .add .eax (.reg .ebx),
       st .eax (TMP + 4 * 0)] : List Instr) ++
     [ld .eax (TMP + 4 * 14), .alu .add .eax (.reg .ebx),
       st .eax (TMP + 4 * 14)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.foldLimb_ok hs (k := 0) (by decide) (by rw [hf 0 (by decide), hc]; exact bound 0 (by decide)))
    fun t ⟨htf, htm, ht⟩ => ?_
  have htc : (t.gpr .ebx).toNat = VG.Proof.X448.Radix16.carry f 28 := by rw [ht.1 _ (by decide), hc]
  refine WP.mono (VG.Proof.X448.X86.foldLimb_ok (hs.of_keeps ht (by decide)) (k := 14) (by decide) ?_)
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

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Normalize`. -/
section

/-!
# X448 on x86 (32-bit): modular reduction
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- Normalize the coefficients at `TMP` into a field-element slot. -/
theorem normalize_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {o : Nat}
    (ho : o + 112 ≤ ACC) {f : Nat → Nat}
    (hf : ∀ i < 28, VG.Proof.X448.X86.limbs s.mem base TMP i = f i) (hb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix) :
    WP isa (.block (normalize o)) s fun t =>
      (∀ i < 28, VG.Proof.X448.X86.limbs t.mem base o i = VG.Proof.X448.Radix16.normalized f i) ∧
      VG.Proof.X448.X86.FieldMem base o s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax, .ebx, .edx] s t := by
  have htmp : TMP + 112 ≤ 4096 := by decide
  have hwork : ∀ {m m' : Mem}, VG.Proof.X448.X86.Outside base TMP 112 m m' → VG.Proof.X448.X86.FieldMem base o m m' :=
    fun h => FieldMem.work h (by decide) (by decide)
  have keep : ∀ {a b : State}, VG.Proof.X448.X86.Keeps [.eax] a b → VG.Proof.X448.X86.Keeps [.eax, .ebx, .edx] a b :=
    fun h => h.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; decide)
  rw [normalize, show pass TMP TMP ++ VG.Impl.X448.X86.fold ++ pass TMP TMP ++ VG.Impl.X448.X86.fold ++ pass o TMP =
    pass TMP TMP ++ (VG.Impl.X448.X86.fold ++ (pass TMP TMP ++ (VG.Impl.X448.X86.fold ++ pass o TMP))) by simp only [List.append_assoc],
    WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.pass_ok hs htmp htmp (Or.inl rfl) hf hb) fun s₁ ⟨f₁, c₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.fold_ok hs₁ f₁ c₁ (VG.Proof.X448.Radix16.carry_bound hb)) fun s₂ ⟨f₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.pass_ok hs₂ htmp htmp (Or.inl rfl) f₂ (VG.Proof.X448.Radix16.folded_bound hb)) fun s₃ ⟨f₃, c₃, m₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.fold_ok hs₃ f₃ c₃ (VG.Proof.X448.Radix16.carry_bound (VG.Proof.X448.Radix16.folded_bound hb))) fun s₄ ⟨f₄, m₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have ho' : o + 112 ≤ TMP := Nat.le_trans ho (by decide)
  refine WP.mono (VG.Proof.X448.X86.pass_ok hs₄ (Nat.le_trans ho (by decide)) htmp (Or.inr (Or.inl ho')) f₄
    (VG.Proof.X448.Radix16.folded_bound (VG.Proof.X448.Radix16.folded_bound hb))) fun s₅ ⟨f₅, _, m₅, k₅⟩ => ?_
  exact ⟨f₅, (hwork m₁).trans ((hwork m₂).trans ((hwork m₃).trans ((hwork m₄).trans (.output m₅)))),
    k₁.trans ((keep k₂).trans (k₃.trans ((keep k₄).trans k₅)))⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Field`. -/
section

/-!
# X448 on x86 (32-bit): field operations and their frame
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := VG.Proof.X448.toFe (VG.Proof.X448.X86.fe m base o)

def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]

structure Op (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s t
  mem : VG.Proof.X448.X86.FieldMem base o s.mem t.mem

theorem Op.scr {base : Addr} {o : Nat} {s t : State} (h : VG.Proof.X448.X86.Op base o s t) (hs : VG.Proof.X448.X86.Scr s base) :
    VG.Proof.X448.X86.Scr t base := hs.of_keeps h.keeps (by decide)

abbrev Slot (o : Nat) : Prop := o + 112 ≤ ACC


end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Columns`. -/
section

/-!
# X448 on x86 (32-bit): pointwise field operations

A pointwise operation fills `TMP` before the carry passes write the output,
permitting input/output aliasing.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem columns_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {code : Nat → List Instr}
    {f : Nat → Nat} {rs : List Reg} (hr : .edi ∉ rs) (hb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix)
    (step : ∀ i < 28, ∀ t, VG.Proof.X448.X86.Scr t base → VG.Proof.X448.X86.Outside base TMP 112 s.mem t.mem → VG.Proof.X448.X86.Keeps rs s t →
      WP isa (.block (code i)) t fun u =>
        u.mem = t.mem.writeW (VG.Proof.X448.X86.off base (TMP + 4 * i)) (BitVec.ofNat 32 (f i)) ∧ VG.Proof.X448.X86.Keeps rs t u) :
    WP isa (.block ((List.range 28).flatMap code)) s fun t =>
      (∀ i < 28, VG.Proof.X448.X86.limbs t.mem base TMP i = f i) ∧ VG.Proof.X448.X86.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps rs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.X86.limbs t.mem base TMP i = f i) ∧ VG.Proof.X448.X86.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps rs s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (code n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (step n hn t (hs.of_keeps tk hr) tm tk) fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.X86.Outside base (TMP + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.X86.writeW_outside _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (VG.Proof.X448.X86.word u.mem base (TMP + 4 * i)).toNat = _
    rw [um, VG.Proof.X448.X86.word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- Reading an input during a pointwise operation. -/
theorem input_limb {s t : State} {base : Addr} {a i : Nat} (h : VG.Proof.X448.X86.Outside base TMP 112 s.mem t.mem)
    (ha : VG.Proof.X448.X86.Slot a) (hi : i < 28) : VG.Proof.X448.X86.limbs t.mem base a i = VG.Proof.X448.X86.limbs s.mem base a i :=
  h.limbs (Or.inl (Nat.le_trans ha (by decide))) (Nat.le_trans ha (by decide)) hi

/-- Carry propagation after a pointwise operation, with the common frame. -/
theorem columns_normalize {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {code : List Instr}
    {o : Nat} (ho : VG.Proof.X448.X86.Slot o) {f : Nat → Nat} (hb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix)
    (hcode : WP isa (.block code) s fun t =>
      (∀ i < 28, VG.Proof.X448.X86.limbs t.mem base TMP i = f i) ∧ VG.Proof.X448.X86.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s t) :
    WP isa (.block (code ++ normalize o)) s fun t =>
      VG.Proof.X448.X86.Op base o s t ∧ VG.Proof.X448.X86.Bounded t.mem base o ∧ VG.Proof.X448.X86.fe t.mem base o % Spec.X448.P = VG.Proof.X448.Radix16.valN f 28 % Spec.X448.P := by
  rw [WP.block_append_iff]
  refine WP.mono hcode fun t ⟨tf, tm, tk⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86.normalize_ok (hs.of_keeps tk (by decide)) ho tf hb) fun u ⟨uf, um, uk⟩ => ?_
  refine ⟨⟨tk.trans (uk.mono ?_), (FieldMem.work tm (by decide) (by decide)).trans um⟩, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro i hi; rw [uf i hi]; exact VG.Proof.X448.Radix16.digit_lt _ _
  · rw [show VG.Proof.X448.X86.fe u.mem base o = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.normalized f) 28 from VG.Proof.X448.Radix16.valN_congr uf, VG.Proof.X448.Radix16.normalized_mod hb]

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.AddSub`. -/
section

/-!
# X448 on x86 (32-bit): addition and subtraction

Twice the prime is added before subtraction, so no limb subtraction borrows.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem addStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {a b i : Nat}
    (ha : VG.Proof.X448.X86.Slot a) (hb : VG.Proof.X448.X86.Slot b) (hi : i < 28) :
    WP isa (.block [ld .eax (a + 4 * i), .alu .add .eax (.mem (VG.Impl.X448.X86.sc (b + 4 * i))),
      st .eax (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.X86.off base (TMP + 4 * i))
        (BitVec.ofNat 32 (VG.Proof.X448.X86.limbs s.mem base a i + VG.Proof.X448.X86.limbs s.mem base b i)) ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine VG.Proof.X448.X86.load_ok hs (by omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide)
  have rd : VG.X86.readSrc t (.mem (VG.Impl.X448.X86.sc (b + 4 * i))) = some (VG.Proof.X448.X86.word t.mem base (b + 4 * i)) := by
    simp only [VG.X86.readSrc, ts.ea (d := b + 4 * i) (by omega), State.load32, ts.read (d := b + 4 * i) (n := 4) (by omega), ite_true]
  refine VG.Proof.X448.X86.wp_alu (Or.inl rfl) rd fun u hu _ => ?_
  refine VG.Proof.X448.X86.store_ok (ts.of_upd hu (by decide)) (by simp only [TMP]; omega) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr]
    change s.mem.writeW _ (t.gpr .eax + VG.Proof.X448.X86.word t.mem base (b + 4 * i)) = _
    rw [ht.gpr, ht.mem]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  · exact (ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _))

theorem subK_nat (i : Nat) : (VG.Impl.X448.X86.subK i).toNat = VG.Proof.X448.Radix16.bias i := by
  by_cases h : i = 14 <;> simp only [VG.Impl.X448.X86.subK, VG.Proof.X448.Radix16.bias, h, ite_true, ite_false] <;> decide

theorem subStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {a b i : Nat}
    (ha : VG.Proof.X448.X86.Slot a) (hb : VG.Proof.X448.X86.Slot b) (hi : i < 28)
    (ab : VG.Proof.X448.X86.limbs s.mem base a i < VG.Proof.X448.Radix16.radix) (bb : VG.Proof.X448.X86.limbs s.mem base b i < VG.Proof.X448.Radix16.radix) :
    WP isa (.block [ld .eax (a + 4 * i), .alu .add .eax (.imm (VG.Impl.X448.X86.subK i)),
      .alu .sub .eax (.mem (VG.Impl.X448.X86.sc (b + 4 * i))), st .eax (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.X86.off base (TMP + 4 * i))
        (BitVec.ofNat 32 (VG.Proof.X448.Radix16.difference (VG.Proof.X448.X86.limbs s.mem base a) (VG.Proof.X448.X86.limbs s.mem base b) i)) ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s t := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  refine VG.Proof.X448.X86.load_ok hs (by omega) fun t ht => ?_
  refine VG.Proof.X448.X86.wp_alu (Or.inl rfl) rfl fun u hu _ => ?_
  have us := (hs.of_upd ht (by decide)).of_upd hu (by decide)
  have rd : VG.X86.readSrc u (.mem (VG.Impl.X448.X86.sc (b + 4 * i))) = some (VG.Proof.X448.X86.word u.mem base (b + 4 * i)) := by
    simp only [VG.X86.readSrc, us.ea (d := b + 4 * i) (by omega), State.load32, us.read (d := b + 4 * i) (n := 4) (by omega), ite_true]
  refine VG.Proof.X448.X86.wp_alu (Or.inr (Or.inl rfl)) rd fun v hv _ => ?_
  refine VG.Proof.X448.X86.store_ok (us.of_upd hv (by decide)) (by simp only [TMP]; omega) fun w hw => WP.block_nil ⟨?_, ?_⟩
  · rw [hw.mem, hv.mem, hu.mem, ht.mem, hv.gpr]
    change s.mem.writeW _ (u.gpr .eax - VG.Proof.X448.X86.word u.mem base (b + 4 * i)) = _
    rw [hu.gpr, hu.mem, ht.mem]
    change s.mem.writeW _ (t.gpr .eax + VG.Impl.X448.X86.subK i - _) = _
    rw [ht.gpr]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, VG.Proof.X448.X86.subK_nat, BitVec.toNat_ofNat]
    change (2 ^ 32 - VG.Proof.X448.X86.limbs s.mem base b i + (VG.Proof.X448.X86.limbs s.mem base a i + VG.Proof.X448.Radix16.bias i) % 2 ^ 32) % 2 ^ 32 =
      (VG.Proof.X448.X86.limbs s.mem base a i + VG.Proof.X448.Radix16.bias i - VG.Proof.X448.X86.limbs s.mem base b i) % 2 ^ 32
    have h := VG.Proof.X448.Radix16.bias_bound i
    simp only [VG.Proof.X448.Radix16.radix] at ab bb h
    omega
  · exact (ht.rest (by decide)).trans ((hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest _)))

theorem add_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.X86.Slot o) (ha : VG.Proof.X448.X86.Slot a) (hb : VG.Proof.X448.X86.Slot b) (ab : VG.Proof.X448.X86.Bounded s.mem base a) (bb : VG.Proof.X448.X86.Bounded s.mem base b) :
    WP isa (.block (Impl.X448.X86.add o a b)) s fun t =>
      VG.Proof.X448.X86.Op base o s t ∧ VG.Proof.X448.X86.Bounded t.mem base o ∧ VG.Proof.X448.X86.F t.mem base o = VG.Proof.X448.X86.F s.mem base a + VG.Proof.X448.X86.F s.mem base b := by
  let f := fun i => VG.Proof.X448.X86.limbs s.mem base a i + VG.Proof.X448.X86.limbs s.mem base b i
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := by
    intro i hi
    have h1 := ab i hi
    have h2 := bb i hi
    change VG.Proof.X448.X86.limbs s.mem base a i + VG.Proof.X448.X86.limbs s.mem base b i ≤ _
    simp only [VG.Proof.X448.Radix16.radix] at h1 h2 ⊢
    omega
  refine WP.mono (VG.Proof.X448.X86.columns_normalize hs ho fb (VG.Proof.X448.X86.columns_ok hs (by decide : .edi ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_add ?_⟩
  · intro i hi t ts tm _
    refine WP.mono (VG.Proof.X448.X86.addStep_ok ts ha hb hi) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    rw [VG.Proof.X448.X86.input_limb tm ha hi, VG.Proof.X448.X86.input_limb tm hb hi] at um
    exact um
  · rw [tv, VG.Proof.X448.Radix16.valN_add]

theorem sub_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.X86.Slot o) (ha : VG.Proof.X448.X86.Slot a) (hb : VG.Proof.X448.X86.Slot b) (ab : VG.Proof.X448.X86.Bounded s.mem base a) (bb : VG.Proof.X448.X86.Bounded s.mem base b) :
    WP isa (.block (Impl.X448.X86.sub o a b)) s fun t =>
      VG.Proof.X448.X86.Op base o s t ∧ VG.Proof.X448.X86.Bounded t.mem base o ∧ VG.Proof.X448.X86.F t.mem base o = VG.Proof.X448.X86.F s.mem base a - VG.Proof.X448.X86.F s.mem base b := by
  let f := VG.Proof.X448.Radix16.difference (VG.Proof.X448.X86.limbs s.mem base a) (VG.Proof.X448.X86.limbs s.mem base b)
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := fun i hi => Nat.le_of_lt (VG.Proof.X448.Radix16.difference_bound ab i hi)
  refine WP.mono (VG.Proof.X448.X86.columns_normalize hs ho fb (VG.Proof.X448.X86.columns_ok hs (by decide : .edi ∉ clob) fb ?_))
    fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_sub ?_⟩
  · intro i hi t ts tm _
    have ea := VG.Proof.X448.X86.input_limb tm ha hi
    have eb := VG.Proof.X448.X86.input_limb tm hb hi
    refine WP.mono (VG.Proof.X448.X86.subStep_ok ts ha hb hi (ea ▸ ab i hi) (eb ▸ bb i hi)) fun u ⟨um, uk⟩ => ⟨?_, uk⟩
    simp only [VG.Proof.X448.Radix16.difference, ea, eb] at um
    exact um
  · rw [Nat.add_mod, tv, ← Nat.add_mod, VG.Proof.X448.Radix16.difference_val bb, Nat.add_mul_mod_self_right]

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Fill`. -/
section

/-!
# X448 on x86 (32-bit): filling words with zero

Each store touches only its designated word in the working space.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

theorem storeOne_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {d : Nat}
    (hd : d + 4 ≤ 4096) (r : Reg) : WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.X86.off base d) (s.gpr r) ∧ VG.Proof.X448.X86.Keeps [] s t := by
  refine VG.Proof.X448.X86.store_ok hs (by omega) fun t ht => WP.block_nil ⟨ht.mem, ht.rest _⟩

theorem zeroEax_ok (s : State) : WP isa (.block [.mov .eax (.imm 0)]) s fun t =>
    t.gpr .eax = 0 ∧ t.mem = s.mem ∧ VG.Proof.X448.X86.Keeps [.eax] s t := by
  refine VG.Proof.X448.X86.wp_mov rfl
    fun t ht => WP.block_nil ⟨ht.gpr, ht.mem, ht.rest (by decide)⟩

theorem fill_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {o n : Nat} (ho : o + 4 * n ≤ 4096)
    (hz : s.gpr .eax = 0) :
    WP isa (.block ((List.range n).map (fun i => st .eax (o + 4 * i)))) s fun t =>
      (∀ i < n, VG.Proof.X448.X86.limbs t.mem base o i = 0) ∧ VG.Proof.X448.X86.Outside base o (4 * n) s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [] s t := by
  let inv := fun k (t : State) =>
    (∀ i < k, VG.Proof.X448.X86.limbs t.mem base o i = 0) ∧ VG.Proof.X448.X86.Outside base o (4 * n) s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [] s t
  have step : ∀ k t, k < n → inv k t →
      WP isa (.block [st .eax (o + 4 * k)]) t (inv (k + 1)) := by
    intro k t hk ⟨tf, tm, tk⟩
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (VG.Proof.X448.X86.storeOne_ok ts (by omega) .eax) fun u ⟨um, uk⟩ => ?_
    rw [tk.1 .eax (by decide), hz] at um
    have out : VG.Proof.X448.X86.Outside base (o + 4 * k) 4 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.X86.writeW_outside _ _ _ (by omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (VG.Proof.X448.X86.word u.mem base (o + 4 * i)).toNat = _
    rw [um, VG.Proof.X448.X86.word_write t.mem base (by omega) (by omega)]
    by_cases h : i = k
    · rw [ite_eq_left h]; rfl
    · rw [ite_eq_right h]; exact tf i (by omega)
  rw [List.map_eq_flatMap]
  exact wp_range_flatMap (M := isa) (N := n) inv step n (by omega) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.RowPass`. -/
section

/-!
# X448 on x86 (32-bit): multiplication-row carry propagation

A pass stores one digit at a time and preserves the remaining coefficients for
the next step.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

structure CarryInv (base : Addr) (o : Nat) (s0 : State) (c : Nat → Nat) (k : Nat) (s : State) : Prop where
  regs : VG.Proof.X448.X86.Keeps [.eax, .ebx, .edx] s0 s
  carry : (s.gpr .ebx).toNat = Radix16.carry c k
  mem : VG.Proof.X448.X86.Outside base o (4 * k) s0.mem s.mem
  outs : ∀ j < k, VG.Proof.X448.X86.limbs s.mem base o j = VG.Proof.X448.Radix16.digit c j

theorem carryPass_ok {base : Addr} {o d : Nat} {rb : Reg} {src : Nat → List Instr} {s0 : State}
    {c : Nat → Nat} (hrb : rb ∉ [.eax, .ebx, .edx]) (ho : o + 112 ≤ 8192)
    (hea : ∀ k < 28, s0.ea (VG.Impl.X448.X86.at_ rb (d + 4 * k)) = VG.Proof.X448.X86.off base (o + 4 * k))
    (hw : ∀ k < 28, InRegions s0.wr (VG.Proof.X448.X86.off base (o + 4 * k)) 4)
    (hzero : (s0.gpr .ebx).toNat = 0) (hc : ∀ k < 28, c k ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix)
    (hsrc : ∀ k < 28, ∀ s, VG.Proof.X448.X86.CarryInv base o s0 c k s →
      WP isa (.block (src k)) s fun t =>
        (t.gpr .eax).toNat = c k ∧ VG.Proof.X448.X86.Keeps [.eax, .edx] s t ∧ t.mem = s.mem) :
    WP isa (.block (carryPass rb d src)) s0 (VG.Proof.X448.X86.CarryInv base o s0 c 28) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.X448.X86.CarryInv base o s0 c) (fun k s hk h => ?_) 28 (Nat.le_refl _) s0
    ⟨Keeps.refl _ _, hzero, Outside.refl _ _ _ _, fun j hj => by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (hsrc k hk s h) fun t ⟨tv, tk, tm⟩ => ?_
  have tb : t.gpr .ebx = s.gpr .ebx := tk.1 _ (by decide)
  have tk' : VG.Proof.X448.X86.Keeps [.eax, .ebx, .edx] s t := tk.mono (by decide)
  have trb : t.gpr rb = s0.gpr rb := (tk'.1 rb hrb).trans (h.regs.1 rb hrb)
  have ea : t.ea (VG.Impl.X448.X86.at_ rb (d + 4 * k)) = VG.Proof.X448.X86.off base (o + 4 * k) := by
    simpa only [State.ea, VG.Impl.X448.X86.at_, trb] using hea k hk
  have bound : c k + Radix16.carry c k < 2 ^ 32 := by
    have a := hc k hk
    have b := VG.Proof.X448.Radix16.carry_bound (n := k) (fun j hj => hc j (by omega))
    simp only [VG.Proof.X448.Radix16.radix] at a
    omega
  refine WP.mono (VG.Proof.X448.X86.carryRaw_ok hrb ea (by rw [tk.2.2, h.regs.2.2]; exact hw k hk)
    (by rw [tv, tb, h.carry]; exact bound)) fun u ⟨uc, um, uk⟩ => ?_
  rw [tv, tb, h.carry] at uc um
  rw [tm] at um
  refine ⟨h.regs.trans ((tk.mono (by decide)).trans uk), uc, ?_, ?_⟩
  · rw [um]
    exact (h.mem.mono (by omega) (by omega)).trans
      ((VG.Proof.X448.X86.writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))
  · intro j hj
    change (VG.Proof.X448.X86.word u.mem base (o + 4 * j)).toNat = _
    rw [um, VG.Proof.X448.X86.word_write s.mem base (by omega) (by omega)]
    by_cases he : j = k
    · rw [ite_eq_left he, he, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_trans (VG.Proof.X448.Radix16.digit_lt c k) (by decide : VG.Proof.X448.Radix16.radix < 2 ^ 32))
    · rw [ite_eq_right he]; exact h.outs j (by omega)

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.RowMem`. -/
section

/-!
# X448 on x86 (32-bit): multiplication-row memory

The public row pointer moves through the working space while all field inputs
remain unchanged.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

abbrev accw (m : Mem) (base : Addr) (k : Nat) : Nat := VG.Proof.X448.X86.limbs m base ACC k

theorem rowEa {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {i d : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) (hd : 4 * i + d < 8192) :
    s.ea (VG.Impl.X448.X86.at_ .ebp d) = VG.Proof.X448.X86.off base (4 * i + d) := by
  change ((s.gpr .ebp + BitVec.ofNat 32 d).setWidth 64) = _
  rw [hp, Offset.add_add]
  exact hs.ea hd

structure RowInv (base : Addr) (a b : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  scr : VG.Proof.X448.X86.Scr s base
  regs : VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s0 s
  ptr : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)
  mem : VG.Proof.X448.X86.Outside base ACC 224 s0.mem s.mem
  lt : ∀ k < i + 28, VG.Proof.X448.X86.accw s.mem base k < VG.Proof.X448.Radix16.radix
  val : VG.Proof.X448.Radix16.valN (VG.Proof.X448.X86.accw s.mem base) (i + 28) = VG.Proof.X448.Radix16.valN (VG.Proof.X448.X86.limbs s0.mem base a) i * VG.Proof.X448.X86.fe s0.mem base b

def rowSrc (b j : Nat) : List Instr :=
  [ld .eax (b + 4 * j), .mul .ecx, .alu .add .eax (.mem (VG.Impl.X448.X86.at_ .ebp (ACC + 4 * j)))]

theorem rowSrc_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {b i j : Nat}
    (hb : VG.Proof.X448.X86.Slot b) (hi : i < 28) (hj : j < 28)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hc : (s.gpr .ecx).toNat < VG.Proof.X448.Radix16.radix) (hy : VG.Proof.X448.X86.limbs s.mem base b j < VG.Proof.X448.Radix16.radix)
    (hacc : VG.Proof.X448.X86.accw s.mem base (i + j) < VG.Proof.X448.Radix16.radix) :
    WP isa (.block (VG.Proof.X448.X86.rowSrc b j)) s fun t =>
      (t.gpr .eax).toNat = (s.gpr .ecx).toNat * VG.Proof.X448.X86.limbs s.mem base b j + VG.Proof.X448.X86.accw s.mem base (i + j) ∧
      VG.Proof.X448.X86.Keeps [.eax, .edx] s t ∧ t.mem = s.mem := by
  have hb' : b + 112 ≤ 3584 := hb
  unfold VG.Proof.X448.X86.rowSrc
  refine VG.Proof.X448.X86.load_ok hs (by omega) fun t ht => ?_
  refine VG.Proof.X448.X86.wp_mul fun u uv um uk => ?_
  have us := (hs.of_upd ht (by decide)).of_keeps uk (by decide)
  have up : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [uk.1 _ (by decide), uk.1 _ (by decide), ht.other .ebp (by decide), ht.other .edi (by decide)]
    exact hp
  have ea : u.ea (VG.Impl.X448.X86.at_ .ebp (ACC + 4 * j)) = VG.Proof.X448.X86.off base (ACC + 4 * (i + j)) := by
    rw [VG.Proof.X448.X86.rowEa us up (by simp only [ACC]; omega), show 4 * i + (ACC + 4 * j) = ACC + 4 * (i + j) by omega]
  have rd : VG.X86.readSrc u (.mem (VG.Impl.X448.X86.at_ .ebp (ACC + 4 * j))) = some (VG.Proof.X448.X86.word u.mem base (ACC + 4 * (i + j))) := by
    simp only [VG.X86.readSrc, ea, State.load32, us.read (d := ACC + 4 * (i + j)) (n := 4) (by simp only [ACC]; omega), ite_true]
  refine VG.Proof.X448.X86.wp_alu (Or.inl rfl) rd fun v hv _ => WP.block_nil ⟨?_, ?_, hv.mem.trans (um.trans ht.mem)⟩
  · rw [hv.gpr]
    change (u.gpr .eax + VG.Proof.X448.X86.word u.mem base (ACC + 4 * (i + j))).toNat = _
    rw [uv, ht.gpr, ht.other .ecx (by decide), um, ht.mem, BitVec.toNat_add, BitVec.toNat_ofNat]
    have prod := Nat.mul_le_mul (Nat.le_of_lt_succ hc) (Nat.le_of_lt_succ hy)
    simp only [VG.Proof.X448.Radix16.radix] at hc hy hacc prod
    change ((VG.Proof.X448.X86.limbs s.mem base b j * (s.gpr .ecx).toNat) % 2 ^ 32 + VG.Proof.X448.X86.accw s.mem base (i + j)) % 2 ^ 32 = _
    rw [Nat.mul_comm (VG.Proof.X448.X86.limbs s.mem base b j)]
    omega
  · exact (ht.rest (by decide)).trans (uk.trans (hv.rest (by decide)))

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Init`. -/
section

/-!
# X448 on x86 (32-bit): initializing multiplication

The initial 28 zero digits represent the empty product prefix; each row adds
its final carry word.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem zeroAcc_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) :
    WP isa (.block VG.Impl.X448.X86.zeroAcc) s fun t =>
      (∀ i < 28, VG.Proof.X448.X86.accw t.mem base i = 0) ∧ VG.Proof.X448.X86.Outside base ACC 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax] s t := by
  unfold VG.Impl.X448.X86.zeroAcc
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.zeroEax_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  have hf := VG.Proof.X448.X86.fill_ok (hs.of_keeps tk (by decide)) (by decide : ACC + 4 * 28 ≤ 4096) tz
  rw [List.map_eq_flatMap] at hf
  refine WP.mono hf fun u ⟨uf, um, uk⟩ => ⟨uf, ?_, tk.trans (uk.mono (by simp))⟩
  rw [← tm]; exact um

theorem mulPre_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (a b : Nat) :
    WP isa (.block mulPre) s (VG.Proof.X448.X86.RowInv base a b s 0) := by
  unfold mulPre
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.zeroAcc_ok hs) fun t ⟨tf, tm, tk⟩ => ?_
  refine VG.Proof.X448.X86.wp_mov rfl fun u hu => WP.block_nil ?_
  have uk : VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s u := (tk.mono (by decide)).trans (hu.rest (by decide))
  refine ⟨hs.of_keeps uk (by decide), uk, ?_, ?_, ?_, ?_⟩
  · change u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 0
    rw [BitVec.add_zero, hu.gpr, hu.other .edi (by decide)]
  · rw [hu.mem]; exact tm.mono (by decide) (by decide)
  · intro i hi; rw [hu.mem, tf i hi]; decide
  · rw [hu.mem, VG.Proof.X448.Radix16.valN_congr tf, valN_zero]
    exact (Nat.zero_mul _).symm

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.RowTail`. -/
section

/-!
# X448 on x86 (32-bit): advancing the product row

The last carry becomes the next product word, and the public row pointer
controls loop termination.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

def rowTail : List Instr :=
  [.store (VG.Impl.X448.X86.at_ .ebp (ACC + 112)) .ebx, .alu .add .ebp (.imm 4),
    .mov .edx (.reg .edi), .alu .add .edx (.imm 112), .alu .cmp .ebp (.reg .edx)]

theorem rowTail_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {i : Nat} (hi : i < 28)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i)) :
    WP isa (.block VG.Proof.X448.X86.rowTail) s fun t =>
      t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (i + 1)) ∧
      t.zf = some (decide (i + 1 = 28)) ∧
      t.mem = s.mem.writeW (VG.Proof.X448.X86.off base (ACC + 4 * (i + 28))) (s.gpr .ebx) ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s t := by
  have ea : s.ea (VG.Impl.X448.X86.at_ .ebp (ACC + 112)) = VG.Proof.X448.X86.off base (ACC + 4 * (i + 28)) := by
    rw [VG.Proof.X448.X86.rowEa hs hp (by simp only [ACC]; omega), show 4 * i + (ACC + 112) = ACC + 4 * (i + 28) by omega]
  unfold VG.Proof.X448.X86.rowTail
  refine VG.Proof.X448.X86.wp_store ea (hs.write (by simp only [ACC]; omega)) fun t ht => ?_
  refine VG.Proof.X448.X86.wp_alu (Or.inl rfl) rfl fun u hu _ => ?_
  refine VG.Proof.X448.X86.wp_mov rfl fun v hv => ?_
  refine VG.Proof.X448.X86.wp_alu (Or.inl rfl) rfl fun w hw _ => ?_
  refine VG.Proof.X448.X86.wp_cmp rfl fun x hx hz => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hx.gpr, hw.other .ebp (by decide), hv.other .ebp (by decide), hu.gpr]
    change t.gpr .ebp + BitVec.ofNat 32 4 = _
    rw [ht.gpr, hp, Offset.add_add, Nat.mul_succ,
      hw.other .edi (by decide), hv.other .edi (by decide), hu.other .edi (by decide), ht.gpr]
  · rw [hz, hw.other .ebp (by decide), hv.other .ebp (by decide), hu.gpr, hw.gpr]
    apply congrArg some
    change ((t.gpr .ebp + (4 : BitVec 32) - (v.gpr .edx + (112 : BitVec 32))) == 0) = _
    rw [hv.gpr, hu.other .edi (by decide), ht.gpr, hp]
    change ((s.gpr .edi + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 - (s.gpr .edi + BitVec.ofNat 32 112)) == 0) = _
    rw [Offset.add_add, Offset.add_sub_add_left]
    have check : ∀ n < 28, ((BitVec.ofNat 32 (4 * n + 4) - BitVec.ofNat 32 112) == 0) = decide (n + 1 = 28) := by decide
    exact check i hi
  · rw [hx.mem, hw.mem, hv.mem, hu.mem, ht.mem]
  · exact (ht.rest _).trans ((hu.rest (by decide)).trans ((hv.rest (by decide)).trans
      ((hw.rest (by decide)).trans (hx.rest _))))

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Row`. -/
section

/-!
# X448 on x86 (32-bit): one multiplication row

Bounded input limbs and previous product digits keep every multiply-add within
a 32-bit word.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem acc_shift (m : Mem) (base : Addr) (i j : Nat) :
    VG.Proof.X448.X86.limbs m base (ACC + 4 * i) j = VG.Proof.X448.X86.accw m base (i + j) := by
  change (VG.Proof.X448.X86.word m base (ACC + 4 * i + 4 * j)).toNat = _
  rw [show ACC + 4 * i + 4 * j = ACC + 4 * (i + j) by omega]

theorem row_ok {base : Addr} {a b : Nat} (ha : VG.Proof.X448.X86.Slot a) (hb : VG.Proof.X448.X86.Slot b) {s0 s : State}
    (ab : VG.Proof.X448.X86.Bounded s0.mem base a) (bb : VG.Proof.X448.X86.Bounded s0.mem base b) {i : Nat} (hi : i < 28)
    (h : VG.Proof.X448.X86.RowInv base a b s0 i s) :
    WP isa (.block (row a b)) s fun t => VG.Proof.X448.X86.RowInv base a b s0 (i + 1) t ∧ t.zf = some (decide (i + 1 = 28)) := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  have input : ∀ o, VG.Proof.X448.X86.Slot o → ∀ j < 28, VG.Proof.X448.X86.limbs s.mem base o j = VG.Proof.X448.X86.limbs s0.mem base o j := by
    intro o ho j hj
    exact h.mem.limbs (Or.inl ho) (Nat.le_trans ho (by decide)) hj
  have ea : s.ea (VG.Impl.X448.X86.at_ .ebp a) = VG.Proof.X448.X86.off base (a + 4 * i) := by
    rw [VG.Proof.X448.X86.rowEa h.scr h.ptr (by omega), Nat.add_comm]
  change WP isa (.block (.mov .ecx (.mem (VG.Impl.X448.X86.at_ .ebp a)) :: .mov .ebx (.imm 0) ::
    (carryPass .ebp ACC (VG.Proof.X448.X86.rowSrc b) ++ VG.Proof.X448.X86.rowTail))) s _
  refine VG.Proof.X448.X86.wp_load ea (h.scr.read (by omega)) fun t ht => ?_
  refine VG.Proof.X448.X86.wp_mov rfl fun u hu => ?_
  have ku : VG.Proof.X448.X86.Keeps [.ecx, .ebx] s u := (ht.rest (by decide)).trans (hu.rest (by decide))
  have us := h.scr.of_keeps ku (by decide)
  have um : u.mem = s.mem := hu.mem.trans ht.mem
  have uc : (u.gpr .ecx).toNat = VG.Proof.X448.X86.limbs s0.mem base a i := by
    rw [hu.other .ecx (by decide), ht.gpr]; exact input a ha i hi
  have up : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [ku.1 _ (by decide), ku.1 _ (by decide)]; exact h.ptr
  let c := rowC (VG.Proof.X448.X86.accw s.mem base) (VG.Proof.X448.X86.limbs s0.mem base a) (VG.Proof.X448.X86.limbs s0.mem base b) i
  have cb : ∀ j < 28, c j ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := by
    intro j hj
    exact rowC_bound (ab i hi) (bb j hj) (h.lt (i + j) (by omega))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.carryPass_ok (s0 := u) (base := base) (o := ACC + 4 * i) (c := c)
    (by decide) (by simp only [ACC]; omega)
    (fun j hj => by
      rw [VG.Proof.X448.X86.rowEa us up (by simp only [ACC]; omega),
        show 4 * i + (ACC + 4 * j) = ACC + 4 * i + 4 * j by omega])
    (fun j hj => us.write (by simp only [ACC]; omega)) (by rw [hu.gpr]; rfl) cb ?_) fun v hv => ?_
  · intro j hj v hv
    have vs := us.of_keeps hv.regs (by decide)
    have vp : v.gpr .ebp = v.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [hv.regs.1 _ (by decide), hv.regs.1 _ (by decide)]; exact up
    have va : (v.gpr .ecx).toNat = VG.Proof.X448.X86.limbs s0.mem base a i := by rw [hv.regs.1 _ (by decide), uc]
    have vb : VG.Proof.X448.X86.limbs v.mem base b j = VG.Proof.X448.X86.limbs s0.mem base b j := by
      rw [hv.mem.limbs (Or.inl (by simp only [ACC]; omega)) (by omega) hj, um, input b hb j hj]
    have vacc : VG.Proof.X448.X86.accw v.mem base (i + j) = VG.Proof.X448.X86.accw s.mem base (i + j) := by
      change (VG.Proof.X448.X86.word v.mem base (ACC + 4 * (i + j))).toNat = _
      rw [hv.mem.word (Or.inr (by omega)) (by simp only [ACC]; omega), um]
    refine WP.mono (VG.Proof.X448.X86.rowSrc_ok vs hb hi hj vp (by rw [va]; exact ab i hi)
      (by rw [vb]; exact bb j hj) (by rw [vacc]; exact h.lt (i + j) (by omega))) fun w ⟨wv, wk, wm⟩ => ⟨?_, wk, wm⟩
    rw [va, vb, vacc] at wv
    exact wv
  · have vs := us.of_keeps hv.regs (by decide)
    have vp : v.gpr .ebp = v.gpr .edi + BitVec.ofNat 32 (4 * i) := by
      rw [hv.regs.1 _ (by decide), hv.regs.1 _ (by decide)]; exact up
    refine WP.mono (VG.Proof.X448.X86.rowTail_ok vs hi vp) fun w ⟨wp, wz, wm, wk⟩ => ?_
    have passMem : VG.Proof.X448.X86.Outside base (ACC + 4 * i) 112 s.mem v.mem := by rw [← um]; exact hv.mem
    have kv : VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s v := (ku.mono (by decide)).trans (hv.regs.mono (by decide))
    have limbsOut : ∀ k < i + 29, VG.Proof.X448.X86.accw w.mem base k =
        rowAcc (VG.Proof.X448.X86.accw s.mem base) (VG.Proof.X448.X86.limbs s0.mem base a) (VG.Proof.X448.X86.limbs s0.mem base b) i k := by
      intro k hk
      change (VG.Proof.X448.X86.word w.mem base (ACC + 4 * k)).toNat = _
      rw [wm, VG.Proof.X448.X86.word_write v.mem base (by simp only [ACC]; omega) (by simp only [ACC]; omega)]
      by_cases he : k = i + 28
      · rw [ite_eq_left he, hv.carry]
        simp only [c, rowAcc, he, show ¬i + 28 < i by omega, Nat.lt_irrefl, ite_false]
      · rw [ite_eq_right he]
        by_cases hk' : k < i
        · rw [passMem.word (Or.inl (by omega)) (by simp only [ACC]; omega)]
          simp only [rowAcc, hk', ite_true]
        · have out := hv.outs (k - i) (by omega)
          rw [VG.Proof.X448.X86.acc_shift, show i + (k - i) = k by omega] at out
          change VG.Proof.X448.X86.accw v.mem base k = _
          rw [out]
          simp only [c, rowAcc, hk', show k < i + 28 by omega, ite_false, ite_true]
    refine ⟨⟨vs.of_keeps wk (by decide), h.regs.trans (kv.trans wk), wp, ?_, ?_, ?_⟩, wz⟩
    · rw [wm]
      exact (h.mem.trans (passMem.mono (by omega) (by omega))).trans
        ((VG.Proof.X448.X86.writeW_outside _ _ _ (by simp only [ACC]; omega)).mono (by omega) (by omega))
    · intro k hk
      rw [limbsOut k hk]
      exact rowAcc_lt (fun k hk => h.lt k (by omega)) cb k hk
    · rw [VG.Proof.X448.Radix16.valN_congr limbsOut]
      exact row_val h.val

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.MulLoop`. -/
section

/-!
# X448 on x86 (32-bit): the multiplication loop

All 28 rows terminate at a public counter, producing 56 bounded product limbs.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem mulLoop_ok {base : Addr} {x y : Nat} (hx : VG.Proof.X448.X86.Slot x) (hy : VG.Proof.X448.X86.Slot y)
    {s0 s : State} (hlx : VG.Proof.X448.X86.Bounded s0.mem base x) (hly : VG.Proof.X448.X86.Bounded s0.mem base y)
    (hs : VG.Proof.X448.X86.RowInv base x y s0 0 s) :
    WP isa (.loop (.block (row x y)) .ne) s (VG.Proof.X448.X86.RowInv base x y s0 28) := by
  refine WP.loop (M := isa)
    (fun n s' => ∃ i, n = 28 - i ∧ i < 28 ∧ VG.Proof.X448.X86.RowInv base x y s0 i s') ?_ 28 s ⟨0, rfl, by decide, hs⟩
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (VG.Proof.X448.X86.row_ok hx hy hlx hly hi hr) fun t ⟨ht, hz⟩ => ?_
  by_cases h28 : i + 1 = 28
  · refine .inl ⟨by simp only [eval, hz, h28, decide_true, Option.map_some, Bool.not_true], ?_⟩
    rw [h28] at ht
    exact ht
  · exact .inr ⟨by simp only [eval, hz, decide_eq_false h28, Option.map_some, Bool.not_false],
      28 - (i + 1), by omega, i + 1, rfl, by omega, ht⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Reduce`. -/
section

/-!
# X448 on x86 (32-bit): reducing product limbs

The upper half folds using `2^448 = 2^224 + 1` modulo the field prime.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem loadAdd_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {d : Nat} (hd : d + 4 ≤ 4096) :
    WP isa (.block [.alu .add .eax (.mem (VG.Impl.X448.X86.sc d))]) s fun t =>
      t.gpr .eax = s.gpr .eax + VG.Proof.X448.X86.word s.mem base d ∧ t.mem = s.mem ∧ VG.Proof.X448.X86.Keeps [.eax] s t := by
  have rd : VG.X86.readSrc s (.mem (VG.Impl.X448.X86.sc d)) = some (VG.Proof.X448.X86.word s.mem base d) := by
    simp only [VG.X86.readSrc, hs.ea (d := d) (by omega), State.load32,
      hs.read (d := d) (n := 4) (by omega), ite_true]
  refine VG.Proof.X448.X86.wp_alu (Or.inl rfl) rd fun t ht _ => WP.block_nil ⟨ht.gpr, ht.mem, ht.rest (by decide)⟩

/-- A bounded sum of words, accumulated into `eax`. -/
def addWords (ds : List Nat) : List Instr :=
  ds.flatMap fun d => [.alu .add .eax (.mem (VG.Impl.X448.X86.sc d))]

theorem addWords_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {ds : List Nat}
    (hd : ∀ d ∈ ds, d + 4 ≤ 4096) :
    WP isa (.block (VG.Proof.X448.X86.addWords ds)) s fun t =>
      t.gpr .eax = s.gpr .eax + (ds.map fun d => VG.Proof.X448.X86.word s.mem base d).sum ∧
      t.mem = s.mem ∧ VG.Proof.X448.X86.Keeps [.eax] s t := by
  induction ds generalizing s with
  | nil => exact WP.block_nil ⟨(BitVec.add_zero _).symm, rfl, Keeps.refl _ _⟩
  | cons d ds ih =>
    change WP isa (.block (([.alu .add .eax (.mem (VG.Impl.X448.X86.sc d))] : List Instr) ++ VG.Proof.X448.X86.addWords ds)) s _
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.X448.X86.loadAdd_ok hs (hd d List.mem_cons_self)) fun t ⟨tv, tm, tk⟩ => ?_
    refine WP.mono (ih (hs.of_keeps tk (by decide)) (fun d h => hd d (List.mem_cons_of_mem _ h)))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um.trans tm, tk.trans uk⟩
    rw [uv, tv, tm]
    simp only [List.map_cons, List.sum_cons, BitVec.add_assoc]

/-- The extra offsets folded into product limb `k`. -/
def colOffsets (k : Nat) : List Nat :=
  [ACC + 4 * (k + 28)] ++
    if k < 14 then [ACC + 4 * (k + 42)] else [ACC + 4 * (k + 14), ACC + 4 * (k + 28)]

theorem colOffsets_bound {k : Nat} (hk : k < 28) : ∀ d ∈ VG.Proof.X448.X86.colOffsets k, d + 4 ≤ 4096 := by
  intro d hd
  simp only [VG.Proof.X448.X86.colOffsets, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | hd
  · simp only [ACC]; omega
  · split at hd <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    · subst d; simp only [ACC]; omega
    · rcases hd with rfl | rfl <;> simp only [ACC] <;> omega

theorem reduceCol_code (k : Nat) : reduceCol k =
    [ld .eax (ACC + 4 * k)] ++ VG.Proof.X448.X86.addWords (VG.Proof.X448.X86.colOffsets k) ++ [st .eax (TMP + 4 * k)] := by
  unfold reduceCol VG.Proof.X448.X86.colOffsets
  split <;> rfl

theorem reduceCol_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {k : Nat} (hk : k < 28)
    {f : Nat → Nat} (hf : ∀ i < 56, VG.Proof.X448.X86.limbs s.mem base ACC i = f i)
    (hb : ∀ i < 56, f i < VG.Proof.X448.Radix16.radix) :
    WP isa (.block (reduceCol k)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.X86.off base (TMP + 4 * k)) (BitVec.ofNat 32 (VG.Proof.X448.Radix16.reduced f k)) ∧
      VG.Proof.X448.X86.Keeps [.eax] s t := by
  rw [VG.Proof.X448.X86.reduceCol_code, List.append_assoc]
  refine VG.Proof.X448.X86.load_ok hs (by simp only [ACC]; omega) fun t ht => ?_
  change WP isa (.block (VG.Proof.X448.X86.addWords (VG.Proof.X448.X86.colOffsets k) ++ ([st .eax (TMP + 4 * k)] : List Instr))) t _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.addWords_ok (hs.of_upd ht (by decide)) (VG.Proof.X448.X86.colOffsets_bound hk))
    fun u ⟨uv, um, uk⟩ => ?_
  have us := (hs.of_upd ht (by decide)).of_keeps uk (by decide)
  refine VG.Proof.X448.X86.store_ok us (by simp only [TMP]; omega) fun v hv => WP.block_nil ⟨?_, ?_⟩
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
      simp only [VG.Proof.X448.X86.colOffsets, h, ite_true, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, VG.Proof.X448.Radix16.reduced, h, ite_true]
      change (VG.Proof.X448.X86.limbs s.mem base ACC k + (VG.Proof.X448.X86.limbs s.mem base ACC (k + 28) +
        (VG.Proof.X448.X86.limbs s.mem base ACC (k + 42)) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
      rw [f0, f1, f2]
      simp only [VG.Proof.X448.Radix16.radix] at b0 b1 b2
      omega
    · have f2 := hf (k + 14) (by omega)
      have b2 := hb (k + 14) (by omega)
      simp only [VG.Proof.X448.X86.colOffsets, h, ite_false, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, VG.Proof.X448.Radix16.reduced, h, ite_false]
      change (VG.Proof.X448.X86.limbs s.mem base ACC k + (VG.Proof.X448.X86.limbs s.mem base ACC (k + 28) +
        (VG.Proof.X448.X86.limbs s.mem base ACC (k + 14) + (VG.Proof.X448.X86.limbs s.mem base ACC (k + 28)) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
      rw [f0, f1, f2]
      simp only [VG.Proof.X448.Radix16.radix] at b0 b1 b2
      omega
  · exact (ht.rest (by decide)).trans (uk.trans (hv.rest _))

/-- Fold all fifty-six product limbs into twenty-eight, ready for carries. -/
theorem reduce_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 56, VG.Proof.X448.X86.limbs s.mem base ACC i = f i) (hb : ∀ i < 56, f i < VG.Proof.X448.Radix16.radix) :
    WP isa (.block ((List.range 28).flatMap reduceCol)) s fun t =>
      (∀ i < 28, VG.Proof.X448.X86.limbs t.mem base TMP i = VG.Proof.X448.Radix16.reduced f i) ∧
      VG.Proof.X448.X86.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.X86.limbs t.mem base TMP i = VG.Proof.X448.Radix16.reduced f i) ∧
    VG.Proof.X448.X86.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax] s t
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block (reduceCol n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have ft : ∀ i < 56, VG.Proof.X448.X86.limbs t.mem base ACC i = f i := by
      intro i hi
      change (VG.Proof.X448.X86.word t.mem base (ACC + 4 * i)).toNat = _
      rw [tm.word (Or.inl (by simp only [ACC, TMP]; omega)) (by simp only [ACC]; omega)]
      exact hf i hi
    refine WP.mono (VG.Proof.X448.X86.reduceCol_ok (hs.of_keeps tk (by decide)) hn ft hb) fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.X86.Outside base (TMP + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.X86.writeW_outside _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (VG.Proof.X448.X86.word u.mem base (TMP + 4 * i)).toNat = _
    rw [um, VG.Proof.X448.X86.word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (VG.Proof.X448.Radix16.reduced_bound hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Mul`. -/
section

/-!
# X448 on x86 (32-bit): field multiplication

The row loop produces the 56 limbs of the product, which are folded and
normalized modulo the prime.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem mul_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {o a b : Nat}
    (ho : VG.Proof.X448.X86.Slot o) (ha : VG.Proof.X448.X86.Slot a) (hb : VG.Proof.X448.X86.Slot b) (ab : VG.Proof.X448.X86.Bounded s.mem base a) (bb : VG.Proof.X448.X86.Bounded s.mem base b) :
    WP isa (Impl.X448.X86.mul o a b) s fun t =>
      VG.Proof.X448.X86.Op base o s t ∧ VG.Proof.X448.X86.Bounded t.mem base o ∧ VG.Proof.X448.X86.F t.mem base o = VG.Proof.X448.X86.F s.mem base a * VG.Proof.X448.X86.F s.mem base b := by
  rw [Impl.X448.X86.mul, WP.seq_iff]
  refine WP.mono (VG.Proof.X448.X86.mulPre_ok hs a b) fun t ht => ?_
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.X448.X86.mulLoop_ok ha hb ab bb ht) fun u hu => ?_
  have uk := hu.regs
  have us := hu.scr
  let f := VG.Proof.X448.X86.limbs u.mem base ACC
  have fb : ∀ i < 56, f i < VG.Proof.X448.Radix16.radix := hu.lt
  have fv : VG.Proof.X448.Radix16.valN f 56 = VG.Proof.X448.X86.fe s.mem base a * VG.Proof.X448.X86.fe s.mem base b := hu.val
  have um := hu.mem
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.reduce_ok us (fun _ _ => rfl) fb) fun v ⟨vf, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  refine WP.mono (VG.Proof.X448.X86.normalize_ok vs ho vf (VG.Proof.X448.Radix16.reduced_bound fb)) fun w ⟨wf, wm, wk⟩ => ?_
  have value : VG.Proof.X448.X86.fe w.mem base o % Spec.X448.P = (VG.Proof.X448.X86.fe s.mem base a * VG.Proof.X448.X86.fe s.mem base b) % Spec.X448.P := by
    rw [show VG.Proof.X448.X86.fe w.mem base o = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.normalized (VG.Proof.X448.Radix16.reduced f)) 28 from VG.Proof.X448.Radix16.valN_congr wf,
      VG.Proof.X448.Radix16.normalized_mod (VG.Proof.X448.Radix16.reduced_bound fb), VG.Proof.X448.Radix16.reduced_mod, fv]
  refine ⟨⟨?_, ?_⟩, ?_, VG.Proof.X448.toFe_mul value⟩
  · exact uk.trans ((vk.mono (by decide)).trans (wk.mono (by decide)))
  · exact (FieldMem.work um (by omega) (by omega)).trans
      ((FieldMem.work vm (by decide) (by decide)).trans wm)
  · intro i hi
    rw [wf i hi]
    exact VG.Proof.X448.Radix16.digit_lt _ _

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Small`. -/
section

/-!
# X448 on x86 (32-bit): multiplication by a24

The 16-bit limbs keep multiplication by 39081 within a 32-bit word.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem smallStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {a i : Nat}
    (ha : VG.Proof.X448.X86.Slot a) (hi : i < 28) (hc : (s.gpr .ecx).toNat = 39081) :
    WP isa (.block [ld .eax (a + 4 * i), .mul .ecx, st .eax (TMP + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.X86.off base (TMP + 4 * i)) (BitVec.ofNat 32 (39081 * VG.Proof.X448.X86.limbs s.mem base a i)) ∧
      VG.Proof.X448.X86.Keeps [.eax, .edx] s t := by
  have ha' : a + 112 ≤ 3584 := ha
  refine VG.Proof.X448.X86.load_ok hs (by omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide)
  refine VG.Proof.X448.X86.wp_mul fun u uv um uk => ?_
  refine VG.Proof.X448.X86.store_ok (ts.of_keeps uk (by decide)) (by simp only [TMP]; omega) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, um, ht.mem, uv, ht.gpr, ht.other .ecx (by decide), hc, Nat.mul_comm _ 39081]
  · exact (ht.rest (by decide)).trans (uk.trans (hv.rest _))

theorem smallInit_ok (s : State) :
    WP isa (.block [.mov .ecx (.imm 39081)]) s fun t =>
      (t.gpr .ecx).toNat = 39081 ∧ t.mem = s.mem ∧ VG.Proof.X448.X86.Keeps [.ecx] s t := by
  refine VG.Proof.X448.X86.wp_mov rfl fun t ht => WP.block_nil ⟨?_, ht.mem, ht.rest (by decide)⟩
  rw [ht.gpr]
  rfl


theorem mulSmall_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {o a : Nat}
    (ho : VG.Proof.X448.X86.Slot o) (ha : VG.Proof.X448.X86.Slot a) (ab : VG.Proof.X448.X86.Bounded s.mem base a) :
    WP isa (.block (VG.Impl.X448.X86.mulSmall o a)) s fun t => VG.Proof.X448.X86.Op base o s t ∧ VG.Proof.X448.X86.Bounded t.mem base o ∧
      VG.Proof.X448.X86.F t.mem base o = Spec.X448.a24 * VG.Proof.X448.X86.F s.mem base a := by
  let f := fun i => 39081 * VG.Proof.X448.X86.limbs s.mem base a i
  have fb : ∀ i < 28, f i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := by
    intro i hi
    have h := Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))
    have hr : 39081 * VG.Proof.X448.Radix16.radix ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := by decide
    exact Nat.le_trans h hr
  refine WP.mono (VG.Proof.X448.X86.columns_normalize hs ho fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, VG.Proof.X448.toFe_a24 ?_⟩
  · rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.X448.X86.smallInit_ok s) fun t ⟨tc, tm, tk⟩ => ?_
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (VG.Proof.X448.X86.columns_ok ts (by decide : Reg.edi ∉ [Reg.eax, Reg.edx]) fb ?_) fun u ⟨uf, um, uk⟩ => ?_
    · intro i hi u us um uk
      have uc : (u.gpr .ecx).toNat = 39081 := by rw [uk.1 _ (by decide), tc]
      refine WP.mono (VG.Proof.X448.X86.smallStep_ok us ha hi uc) fun v ⟨vm, vk⟩ => ⟨?_, vk⟩
      rw [VG.Proof.X448.X86.input_limb um ha hi, tm] at vm
      exact vm
    · refine ⟨uf, ?_, (tk.mono ?_).trans (uk.mono ?_)⟩
      · rw [← tm]; exact um
      · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide
  · rw [tv, VG.Proof.X448.Radix16.valN_scale]

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Copy`. -/
section

/-!
# X448 on x86 (32-bit): copying field elements

Equal or disjoint source and destination slots preserve the original limbs.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem copyStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {o a i : Nat}
    (ho : o + 112 ≤ 4096) (ha : a + 112 ≤ 4096) (hi : i < 28) :
    WP isa (.block [ld .eax (a + 4 * i), st .eax (o + 4 * i)]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.X86.off base (o + 4 * i)) (VG.Proof.X448.X86.word s.mem base (a + 4 * i)) ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s t := by
  refine VG.Proof.X448.X86.load_ok hs (by omega) fun t ht => ?_
  refine VG.Proof.X448.X86.store_ok (hs.of_upd ht (by decide)) (by omega) fun u hu => WP.block_nil ⟨?_, ?_⟩
  · rw [hu.mem, ht.mem, ht.gpr]
  · exact (ht.rest (by decide)).trans (hu.rest _)

theorem copy_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {o a : Nat}
    (ho : o + 112 ≤ 4096) (ha : a + 112 ≤ 4096)
    (hsep : o = a ∨ o + 112 ≤ a ∨ a + 112 ≤ o) :
    WP isa (.block (VG.Impl.X448.X86.copy o a)) s fun t =>
      (∀ i < 28, VG.Proof.X448.X86.limbs t.mem base o i = VG.Proof.X448.X86.limbs s.mem base a i) ∧
      VG.Proof.X448.X86.Outside base o 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.X86.limbs t.mem base o i = VG.Proof.X448.X86.limbs s.mem base a i) ∧
    (∀ i, n ≤ i → i < 28 → VG.Proof.X448.X86.limbs t.mem base a i = VG.Proof.X448.X86.limbs s.mem base a i) ∧
    VG.Proof.X448.X86.Outside base o 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s t
  have st : ∀ n t, n < 28 → inv n t →
      WP isa (.block [ld .eax (a + 4 * n), st .eax (o + 4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, ta, tm, tk⟩
    refine WP.mono (VG.Proof.X448.X86.copyStep_ok (hs.of_keeps tk (by decide)) ho ha hn) fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.X86.Outside base (o + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.X86.writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    · intro i hi
      change (VG.Proof.X448.X86.word u.mem base (o + 4 * i)).toNat = _
      rw [um, VG.Proof.X448.X86.word_write t.mem base (by omega) (by omega)]
      by_cases h : i = n
      · rw [ite_eq_left h, h]; exact ta n (by omega) hn
      · rw [ite_eq_right h]; exact tf i (by omega)
    · intro i hi hi'
      change (VG.Proof.X448.X86.word u.mem base (a + 4 * i)).toNat = _
      rw [out.word (by rcases hsep with h | h | h <;> omega) (by omega)]
      exact ta i (by omega) hi'
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s ?_)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  exact ⟨fun _ hi => by omega, fun _ _ _ => rfl, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Swap`. -/
section

/-!
# X448 on x86 (32-bit): constant-time conditional swaps

An XOR mask swaps limbs without a secret-dependent branch or memory address.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

def mask (sw : Bool) : BitVec 32 := if sw then BitVec.allOnes 32 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 32) :
    a ^^^ ((a ^^^ b) &&& VG.Proof.X448.X86.mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& VG.Proof.X448.X86.mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [VG.Proof.X448.X86.mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [VG.Proof.X448.X86.mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem swapStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {x y i : Nat}
    (hx : VG.Proof.X448.X86.Slot x) (hy : VG.Proof.X448.X86.Slot y) (hi : i < 28) {sw : Bool} (hc : s.gpr .ebx = VG.Proof.X448.X86.mask sw) :
    WP isa (.block
      [ld .eax (x + 4 * i), ld .ecx (y + 4 * i), .mov .edx (.reg .eax), .alu .xor .edx (.reg .ecx),
        .alu .and .edx (.reg .ebx), .alu .xor .eax (.reg .edx),
        .alu .xor .ecx (.reg .edx), st .eax (x + 4 * i), st .ecx (y + 4 * i)]) s fun t =>
      t.mem = (s.mem.writeW (VG.Proof.X448.X86.off base (x + 4 * i))
        (if sw then VG.Proof.X448.X86.word s.mem base (y + 4 * i) else VG.Proof.X448.X86.word s.mem base (x + 4 * i))).writeW
        (VG.Proof.X448.X86.off base (y + 4 * i)) (if sw then VG.Proof.X448.X86.word s.mem base (x + 4 * i) else VG.Proof.X448.X86.word s.mem base (y + 4 * i)) ∧
      VG.Proof.X448.X86.Keeps [.eax, .ecx, .edx] s t := by
  have hx' : x + 112 ≤ 3584 := hx
  have hy' : y + 112 ≤ 3584 := hy
  have lx := hs.read (d := x + 4 * i) (n := 4) (by omega)
  have ly := hs.read (d := y + 4 * i) (n := 4) (by omega)
  have wx := hs.write (d := x + 4 * i) (n := 4) (by omega)
  have wy := hs.write (d := y + 4 * i) (n := 4) (by omega)
  have xe := hs.ea (d := x + 4 * i) (by omega)
  have ye := hs.ea (d := y + 4 * i) (by omega)
  simp only [State.ea, VG.Impl.X448.X86.sc, VG.Impl.X448.X86.at_] at xe ye
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86.readSrc, State.ea, VG.Impl.X448.X86.sc, VG.Impl.X448.X86.at_,
    State.load32, State.store32, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, xe, ye, hc, lx, ly, wx, wy,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [(VG.Proof.X448.X86.xor_sel sw _ _).1, (VG.Proof.X448.X86.xor_sel sw _ _).2]
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

/-- Reading two disjoint words after writing a limb pair. -/
theorem pair_write {m : Mem} {base : Addr} {x y n j : Nat} (hx : VG.Proof.X448.X86.Slot x) (hy : VG.Proof.X448.X86.Slot y)
    (hxy : x + 112 ≤ y ∨ y + 112 ≤ x) (hn : n < 28) (hj : j < 28) (vx vy : BitVec 32) :
    let m' := (m.writeW (VG.Proof.X448.X86.off base (x + 4 * n)) vx).writeW (VG.Proof.X448.X86.off base (y + 4 * n)) vy
    VG.Proof.X448.X86.limbs m' base x j = (if j = n then vx.toNat else VG.Proof.X448.X86.limbs m base x j) ∧
    VG.Proof.X448.X86.limbs m' base y j = (if j = n then vy.toNat else VG.Proof.X448.X86.limbs m base y j) := by
  have xb : x + 112 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 112 ≤ 8192 := Nat.le_trans hy (by decide)
  dsimp only
  constructor
  · simp only [VG.Proof.X448.X86.limbs, VG.Proof.X448.X86.word]
    rw [Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)]
    rw [show m.readW (VG.Proof.X448.X86.off base (x + 4 * j)) 32 = VG.Proof.X448.X86.word m base (x + 4 * j) from rfl]
    change (VG.Proof.X448.X86.word (m.writeW (VG.Proof.X448.X86.off base (x + 4 * n)) vx) base (x + 4 * j)).toNat = _
    rw [VG.Proof.X448.X86.word_write m base (by omega) (by omega)]
    split <;> rfl
  · change (VG.Proof.X448.X86.word ((m.writeW (VG.Proof.X448.X86.off base (x + 4 * n)) vx).writeW (VG.Proof.X448.X86.off base (y + 4 * n)) vy)
      base (y + 4 * j)).toNat = _
    rw [VG.Proof.X448.X86.word_write (m.writeW (VG.Proof.X448.X86.off base (x + 4 * n)) vx) base (by omega) (by omega)]
    by_cases h : j = n
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      apply congrArg BitVec.toNat
      exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- Swap all twenty-eight limbs under the mask, preserving all other bytes. -/
theorem cswap_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {x y : Nat} (hx : VG.Proof.X448.X86.Slot x) (hy : VG.Proof.X448.X86.Slot y)
    (hxy : x + 112 ≤ y ∨ y + 112 ≤ x) {sw : Bool} (hc : s.gpr .ebx = VG.Proof.X448.X86.mask sw) :
    WP isa (.block (VG.Impl.X448.X86.cswap x y)) s fun t =>
      (∀ i < 28, VG.Proof.X448.X86.limbs t.mem base x i = if sw then VG.Proof.X448.X86.limbs s.mem base y i else VG.Proof.X448.X86.limbs s.mem base x i) ∧
      (∀ i < 28, VG.Proof.X448.X86.limbs t.mem base y i = if sw then VG.Proof.X448.X86.limbs s.mem base x i else VG.Proof.X448.X86.limbs s.mem base y i) ∧
      VG.Proof.X448.X86.Outside2 base x 112 y 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax, .ecx, .edx] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.X86.limbs t.mem base x i = if sw then VG.Proof.X448.X86.limbs s.mem base y i else VG.Proof.X448.X86.limbs s.mem base x i) ∧
    (∀ i < n, VG.Proof.X448.X86.limbs t.mem base y i = if sw then VG.Proof.X448.X86.limbs s.mem base x i else VG.Proof.X448.X86.limbs s.mem base y i) ∧
    VG.Proof.X448.X86.Outside2 base x (4 * n) y (4 * n) s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax, .ecx, .edx] s t
  have xb : x + 112 ≤ 8192 := Nat.le_trans hx (by decide)
  have yb : y + 112 ≤ 8192 := Nat.le_trans hy (by decide)
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block
      [ld .eax (x + 4 * n), ld .ecx (y + 4 * n), .mov .edx (.reg .eax), .alu .xor .edx (.reg .ecx),
        .alu .and .edx (.reg .ebx), .alu .xor .eax (.reg .edx),
        .alu .xor .ecx (.reg .edx), st .eax (x + 4 * n), st .ecx (y + 4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tc := (tk.1 .ebx (by decide)).trans hc
    refine WP.mono (VG.Proof.X448.X86.swapStep_ok (hs.of_keeps tk (by decide)) hx hy hn tc) fun u ⟨um, uk⟩ => ?_
    have ex : VG.Proof.X448.X86.limbs t.mem base x n = VG.Proof.X448.X86.limbs s.mem base x n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have ey : VG.Proof.X448.X86.limbs t.mem base y n = VG.Proof.X448.X86.limbs s.mem base y n :=
      congrArg BitVec.toNat (tm.word (by omega) (by omega) (by omega))
    have pair := fun (j : Nat) (hj : j < 28) => VG.Proof.X448.X86.pair_write (m := t.mem) (base := base) hx hy hxy hn hj
      (if sw then VG.Proof.X448.X86.word t.mem base (y + 4 * n) else VG.Proof.X448.X86.word t.mem base (x + 4 * n))
      (if sw then VG.Proof.X448.X86.word t.mem base (x + 4 * n) else VG.Proof.X448.X86.word t.mem base (y + 4 * n))
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
      rw [um, VG.Proof.X448.X86.writeW_outside _ _ _ (by omega : y + 4 * n + 4 ≤ 8192) p (by omega),
        VG.Proof.X448.X86.writeW_outside _ _ _ (by omega : x + 4 * n + 4 ≤ 8192) p (by omega)]
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hi => by omega, fun _ hi => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Env`. -/
section

/-!
# X448 on x86 (32-bit): the working space as field-element slots

Field operations update one of twenty-two slots, preserving bounded limbs in
every slot. The frame excludes saved registers, the swap bit and the scalar's
decoded bits.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

abbrev Index := Fin 22
abbrev Env := VG.Proof.X448.X86.Index → Spec.X448.Fe

def E (m : Mem) (base : Addr) (i : VG.Proof.X448.X86.Index) : Spec.X448.Fe := VG.Proof.X448.X86.F m base (slot i.val)
def BoundedEnv (m : Mem) (base : Addr) : Prop := ∀ i : VG.Proof.X448.X86.Index, VG.Proof.X448.X86.Bounded m base (slot i.val)

def workRegs : List Reg := .edx :: VG.Proof.X448.X86.clob

structure Keep (base : Addr) (s t : State) : Prop where
  regs : VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.workRegs s t
  mem : VG.Proof.X448.X86.Outside2 base 64 2816 ACC 512 s.mem t.mem

theorem Keep.refl (base : Addr) (s : State) : VG.Proof.X448.X86.Keep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem Keep.trans {base : Addr} {s t u : State} (h : VG.Proof.X448.X86.Keep base s t) (h' : VG.Proof.X448.X86.Keep base t u) :
    VG.Proof.X448.X86.Keep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem Keep.scr {base : Addr} {s t : State} (h : VG.Proof.X448.X86.Keep base s t) (hs : VG.Proof.X448.X86.Scr s base) : VG.Proof.X448.X86.Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem slot_bound (i : VG.Proof.X448.X86.Index) : VG.Proof.X448.X86.Slot (slot i.val) := by
  simp only [VG.Proof.X448.X86.Slot, slot, ACC]
  have := i.isLt
  omega

theorem slot_sep {i j : VG.Proof.X448.X86.Index} (h : i ≠ j) : slot i.val + 112 ≤ slot j.val ∨ slot j.val + 112 ≤ slot i.val := by
  have hn : i.val ≠ j.val := fun he => h (Fin.ext he)
  simp only [slot]
  omega

theorem Op.keep {base : Addr} {o : VG.Proof.X448.X86.Index} {s t : State} (h : VG.Proof.X448.X86.Op base (slot o.val) s t) : VG.Proof.X448.X86.Keep base s t := by
  refine ⟨h.keeps.mono (fun _ hr => List.mem_cons_of_mem _ hr), ?_⟩
  intro p hp hq
  apply h.mem p _ hq
  have := o.isLt
  simp only [slot]
  omega

theorem E_update {base : Addr} {m m' : Mem} {o : VG.Proof.X448.X86.Index} (h : VG.Proof.X448.X86.FieldMem base (slot o.val) m m') :
    VG.Proof.X448.X86.E m' base = Function.update (VG.Proof.X448.X86.E m base) o (VG.Proof.X448.X86.F m' base (slot o.val)) := by
  funext i
  by_cases hi : i = o
  · subst i; simp only [Function.update_self, VG.Proof.X448.X86.E]
  · rw [Function.update_of_ne hi]
    simp only [VG.Proof.X448.X86.E, VG.Proof.X448.X86.F]
    rw [h.fe (VG.Proof.X448.X86.slot_sep hi) (VG.Proof.X448.X86.slot_bound i)]

theorem bounded_update {base : Addr} {m m' : Mem} {o : VG.Proof.X448.X86.Index} (h : VG.Proof.X448.X86.FieldMem base (slot o.val) m m')
    (hm : VG.Proof.X448.X86.BoundedEnv m base) (ho : VG.Proof.X448.X86.Bounded m' base (slot o.val)) : VG.Proof.X448.X86.BoundedEnv m' base := by
  intro i
  by_cases hi : i = o
  · subst i; exact ho
  · intro j hj
    rw [h.limbs (VG.Proof.X448.X86.slot_sep hi) (VG.Proof.X448.X86.slot_bound i) hj]
    exact hm i j hj

def opMul (o a b : VG.Proof.X448.X86.Index) (e : VG.Proof.X448.X86.Env) : VG.Proof.X448.X86.Env := Function.update e o (e a * e b)
def opAdd (o a b : VG.Proof.X448.X86.Index) (e : VG.Proof.X448.X86.Env) : VG.Proof.X448.X86.Env := Function.update e o (e a + e b)
def opSub (o a b : VG.Proof.X448.X86.Index) (e : VG.Proof.X448.X86.Env) : VG.Proof.X448.X86.Env := Function.update e o (e a - e b)
def opA24 (o a : VG.Proof.X448.X86.Index) (e : VG.Proof.X448.X86.Env) : VG.Proof.X448.X86.Env := Function.update e o (Spec.X448.a24 * e a)
def opCopy (o a : VG.Proof.X448.X86.Index) (e : VG.Proof.X448.X86.Env) : VG.Proof.X448.X86.Env := Function.update e o (e a)
def opSwap (x y : VG.Proof.X448.X86.Index) (sw : Bool) (e : VG.Proof.X448.X86.Env) : VG.Proof.X448.X86.Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

theorem mulE {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.BoundedEnv s.mem base) (o a b : VG.Proof.X448.X86.Index) :
    WP isa (Impl.X448.X86.mul (slot o.val) (slot a.val) (slot b.val)) s fun t =>
      VG.Proof.X448.X86.Keep base s t ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = VG.Proof.X448.X86.opMul o a b (VG.Proof.X448.X86.E s.mem base) :=
  WP.mono (VG.Proof.X448.X86.mul_ok hs (VG.Proof.X448.X86.slot_bound o) (VG.Proof.X448.X86.slot_bound a) (VG.Proof.X448.X86.slot_bound b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.X86.bounded_update h.mem hb bo, by rw [VG.Proof.X448.X86.E_update h.mem, e]; rfl⟩

theorem addE {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.BoundedEnv s.mem base) (o a b : VG.Proof.X448.X86.Index) :
    WP isa (.block (Impl.X448.X86.add (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      VG.Proof.X448.X86.Keep base s t ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = VG.Proof.X448.X86.opAdd o a b (VG.Proof.X448.X86.E s.mem base) :=
  WP.mono (VG.Proof.X448.X86.add_ok hs (VG.Proof.X448.X86.slot_bound o) (VG.Proof.X448.X86.slot_bound a) (VG.Proof.X448.X86.slot_bound b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.X86.bounded_update h.mem hb bo, by rw [VG.Proof.X448.X86.E_update h.mem, e]; rfl⟩

theorem subE {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.BoundedEnv s.mem base) (o a b : VG.Proof.X448.X86.Index) :
    WP isa (.block (Impl.X448.X86.sub (slot o.val) (slot a.val) (slot b.val))) s fun t =>
      VG.Proof.X448.X86.Keep base s t ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = VG.Proof.X448.X86.opSub o a b (VG.Proof.X448.X86.E s.mem base) :=
  WP.mono (VG.Proof.X448.X86.sub_ok hs (VG.Proof.X448.X86.slot_bound o) (VG.Proof.X448.X86.slot_bound a) (VG.Proof.X448.X86.slot_bound b) (hb a) (hb b)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.X86.bounded_update h.mem hb bo, by rw [VG.Proof.X448.X86.E_update h.mem, e]; rfl⟩

theorem a24E {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.BoundedEnv s.mem base) (o a : VG.Proof.X448.X86.Index) :
    WP isa (.block (VG.Impl.X448.X86.mulSmall (slot o.val) (slot a.val))) s fun t =>
      VG.Proof.X448.X86.Keep base s t ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = VG.Proof.X448.X86.opA24 o a (VG.Proof.X448.X86.E s.mem base) :=
  WP.mono (VG.Proof.X448.X86.mulSmall_ok hs (VG.Proof.X448.X86.slot_bound o) (VG.Proof.X448.X86.slot_bound a) (hb a)) fun _ ⟨h, bo, e⟩ =>
    ⟨h.keep, VG.Proof.X448.X86.bounded_update h.mem hb bo, by rw [VG.Proof.X448.X86.E_update h.mem, e]; rfl⟩

theorem copyE {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.BoundedEnv s.mem base) (o a : VG.Proof.X448.X86.Index) :
    WP isa (.block (VG.Impl.X448.X86.copy (slot o.val) (slot a.val))) s fun t =>
      VG.Proof.X448.X86.Keep base s t ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = VG.Proof.X448.X86.opCopy o a (VG.Proof.X448.X86.E s.mem base) := by
  have sep : slot o.val = slot a.val ∨ slot o.val + 112 ≤ slot a.val ∨ slot a.val + 112 ≤ slot o.val := by
    by_cases h : o = a
    · subst o; exact Or.inl rfl
    · exact Or.inr (VG.Proof.X448.X86.slot_sep h)
  refine WP.mono (VG.Proof.X448.X86.copy_ok hs (Nat.le_trans (VG.Proof.X448.X86.slot_bound o) (by decide))
    (Nat.le_trans (VG.Proof.X448.X86.slot_bound a) (by decide)) sep) fun t ⟨tf, tm, tk⟩ => ?_
  have op : VG.Proof.X448.X86.Op base (slot o.val) s t := ⟨tk, FieldMem.output tm⟩
  refine ⟨op.keep, VG.Proof.X448.X86.bounded_update op.mem hb (fun i hi => ?_), ?_⟩
  · rw [tf i hi]; exact hb a i hi
  · rw [VG.Proof.X448.X86.E_update op.mem, show VG.Proof.X448.X86.F t.mem base (slot o.val) = VG.Proof.X448.X86.F s.mem base (slot a.val) from
      congrArg VG.Proof.X448.toFe (VG.Proof.X448.Radix16.valN_congr tf)]
    rfl

theorem cswapE {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.BoundedEnv s.mem base)
    (x y : VG.Proof.X448.X86.Index) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .ebx = VG.Proof.X448.X86.mask sw) :
    WP isa (.block (VG.Impl.X448.X86.cswap (slot x.val) (slot y.val))) s fun t =>
      VG.Proof.X448.X86.Keep base s t ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧ t.gpr .ebx = s.gpr .ebx ∧
      VG.Proof.X448.X86.E t.mem base = VG.Proof.X448.X86.opSwap x y sw (VG.Proof.X448.X86.E s.mem base) := by
  refine WP.mono (VG.Proof.X448.X86.cswap_ok hs (VG.Proof.X448.X86.slot_bound x) (VG.Proof.X448.X86.slot_bound y) (VG.Proof.X448.X86.slot_sep hxy) hm)
    fun t ⟨tx, ty, tm, tk⟩ => ?_
  have other : ∀ i : VG.Proof.X448.X86.Index, i ≠ x → i ≠ y → ∀ j < 28,
      VG.Proof.X448.X86.limbs t.mem base (slot i.val) j = VG.Proof.X448.X86.limbs s.mem base (slot i.val) j := by
    intro i hix hiy j hj
    have ex := VG.Proof.X448.X86.slot_sep hix
    have ey := VG.Proof.X448.X86.slot_sep hiy
    have hi := VG.Proof.X448.X86.slot_bound i
    change (VG.Proof.X448.X86.word t.mem base (slot i.val + 4 * j)).toNat = _
    rw [tm.word (by omega) (by omega) (by change slot i.val + 112 ≤ 3584 at hi; omega)]
  have fx : VG.Proof.X448.X86.E t.mem base x = if sw then VG.Proof.X448.X86.E s.mem base y else VG.Proof.X448.X86.E s.mem base x := by
    cases sw <;> apply congrArg VG.Proof.X448.toFe <;> apply VG.Proof.X448.Radix16.valN_congr <;> exact tx
  have fy : VG.Proof.X448.X86.E t.mem base y = if sw then VG.Proof.X448.X86.E s.mem base x else VG.Proof.X448.X86.E s.mem base y := by
    cases sw <;> apply congrArg VG.Proof.X448.toFe <;> apply VG.Proof.X448.Radix16.valN_congr <;> exact ty
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
    · subst i; rw [VG.Proof.X448.X86.opSwap, Function.update_self]; exact fy
    · rw [VG.Proof.X448.X86.opSwap, Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst i; rw [Function.update_self]; exact fx
      · rw [Function.update_of_ne hix]
        exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Radix16.valN_congr (other i hix hiy))

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Ops`. -/
section

/-!
# X448 on x86 (32-bit): sequences of field operations

Slot-indexed operations interpret the implementation's field-operation lists
as environment updates.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

inductive FieldOp
  | mul (o a b : VG.Proof.X448.X86.Index)
  | add (o a b : VG.Proof.X448.X86.Index)
  | sub (o a b : VG.Proof.X448.X86.Index)
  | mulSmall (o a : VG.Proof.X448.X86.Index)
  | copy (o a : VG.Proof.X448.X86.Index)
  deriving DecidableEq

def FieldOp.impl : VG.Proof.X448.X86.FieldOp → Impl.X448.X86.Op
  | .mul o a b => .mul (slot o.val) (slot a.val) (slot b.val)
  | .add o a b => .add (slot o.val) (slot a.val) (slot b.val)
  | .sub o a b => .sub (slot o.val) (slot a.val) (slot b.val)
  | .mulSmall o a => .mulSmall (slot o.val) (slot a.val)
  | .copy o a => .copy (slot o.val) (slot a.val)

def FieldOp.apply : VG.Proof.X448.X86.FieldOp → VG.Proof.X448.X86.Env → VG.Proof.X448.X86.Env
  | .mul o a b => VG.Proof.X448.X86.opMul o a b
  | .add o a b => VG.Proof.X448.X86.opAdd o a b
  | .sub o a b => VG.Proof.X448.X86.opSub o a b
  | .mulSmall o a => VG.Proof.X448.X86.opA24 o a
  | .copy o a => VG.Proof.X448.X86.opCopy o a

def applyOps : List VG.Proof.X448.X86.FieldOp → VG.Proof.X448.X86.Env → VG.Proof.X448.X86.Env
  | [], e => e
  | op :: rest, e => VG.Proof.X448.X86.applyOps rest (op.apply e)

theorem fieldOp_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.BoundedEnv s.mem base) (op : VG.Proof.X448.X86.FieldOp) :
    WP isa op.impl.code s fun t =>
      VG.Proof.X448.X86.Keep base s t ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = op.apply (VG.Proof.X448.X86.E s.mem base) := by
  cases op with
  | mul o a b => exact VG.Proof.X448.X86.mulE hs hb o a b
  | add o a b => exact VG.Proof.X448.X86.addE hs hb o a b
  | sub o a b => exact VG.Proof.X448.X86.subE hs hb o a b
  | mulSmall o a => exact VG.Proof.X448.X86.a24E hs hb o a
  | copy o a => exact VG.Proof.X448.X86.copyE hs hb o a

theorem ops_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.BoundedEnv s.mem base) (xs : List VG.Proof.X448.X86.FieldOp) :
    WP isa (VG.Impl.X448.X86.ops (xs.map FieldOp.impl)) s fun t =>
      VG.Proof.X448.X86.Keep base s t ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = VG.Proof.X448.X86.applyOps xs (VG.Proof.X448.X86.E s.mem base) := by
  induction xs generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hb, rfl⟩
  | cons op rest ih =>
    change WP isa (.seq op.impl.code (VG.Impl.X448.X86.ops (rest.map FieldOp.impl))) s _
    rw [WP.seq_iff]
    refine WP.mono (VG.Proof.X448.X86.fieldOp_ok hs hb op) fun t ⟨tk, tb, te⟩ => ?_
    refine WP.mono (ih (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, ?_⟩
    rw [ue, te]
    rfl

/-- The arithmetic part of one Montgomery-ladder step. -/
def stepFields : List VG.Proof.X448.X86.FieldOp :=
  [.add 5 1 2, .mul 9 5 5, .sub 6 1 2, .mul 10 6 6, .sub 11 9 10,
    .add 7 3 4, .sub 8 3 4, .mul 12 8 5, .mul 13 7 6,
    .add 3 12 13, .mul 3 3 3, .sub 4 12 13, .mul 4 4 4, .mul 4 0 4,
    .mul 1 9 10, .mulSmall 2 11, .add 2 9 2, .mul 2 11 2]

theorem stepFields_impl : stepFields.map FieldOp.impl = VG.Impl.X448.X86.stepOps := by decide +kernel

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.BitStep`. -/
section

/-!
# X448 on x86 (32-bit): reading a scalar bit

Only the public loop counter selects an address; the bit affects an XOR mask.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def stepPre : List Instr :=
  [.alu .sub .esi (.imm 1), .mov .ebp (.reg .edi), .alu .add .ebp (.reg .esi),
    .movzx8 .eax (VG.Impl.X448.X86.at_ .ebp VG.Impl.X448.X86.BITS), ld .ecx VG.Impl.X448.X86.SWAP, .alu .xor .ecx (.reg .eax), st .eax VG.Impl.X448.X86.SWAP,
    .mov .ebx (.imm 0), .alu .sub .ebx (.reg .ecx)]

theorem mask_xor : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 32) - (BitVec.ofNat 32 a ^^^ (BitVec.ofNat 8 b).setWidth 32) =
      VG.Proof.X448.X86.mask (decide (a ^^^ b = 1)) := by decide

theorem stepPre_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {t : Nat} (ht : t < 448)
    (hb : s.gpr .esi = BitVec.ofNat 32 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 kt)
    (hswap : VG.Proof.X448.X86.word s.mem base VG.Impl.X448.X86.SWAP = BitVec.ofNat 32 sw0) :
    WP isa (.block VG.Proof.X448.X86.stepPre) s fun s' =>
      s'.gpr .esi = BitVec.ofNat 32 t ∧ s'.gpr .ebx = VG.Proof.X448.X86.mask (decide (sw0 ^^^ kt = 1)) ∧
      (∀ r, r ∉ [.esi, .eax, .ecx, .ebx, .ebp] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (VG.Proof.X448.X86.off base VG.Impl.X448.X86.SWAP) (BitVec.ofNat 32 kt) := by
  have hb' : s.gpr .esi - (1 : BitVec 32) = BitVec.ofNat 32 t := by
    change s.gpr .esi - BitVec.ofNat 32 1 = _
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hin := hs.read (d := VG.Impl.X448.X86.BITS + t) (n := 1) (by simp only [VG.Impl.X448.X86.BITS]; omega)
  have hr := hs.read (d := VG.Impl.X448.X86.SWAP) (n := 4) (by decide)
  have hw := hs.write (d := VG.Impl.X448.X86.SWAP) (n := 4) (by decide)
  have ba : (s.gpr .edi + BitVec.ofNat 32 t + BitVec.ofNat 32 VG.Impl.X448.X86.BITS).setWidth 64 = VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + t) := by
    rw [Offset.add_add, Nat.add_comm t VG.Impl.X448.X86.BITS]
    exact hs.ea (by simp only [VG.Impl.X448.X86.BITS]; omega)
  have sa := hs.ea (d := VG.Impl.X448.X86.SWAP) (by decide)
  simp only [State.ea, VG.Impl.X448.X86.sc, VG.Impl.X448.X86.at_] at sa
  apply WP.of_runBlock
  simp only [VG.Proof.X448.X86.stepPre, ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86.readSrc,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    State.ea, VG.Impl.X448.X86.sc, VG.Impl.X448.X86.at_, hb', ba, sa, State.load8, State.load32, State.store32, hin, hr, hw, hbit,
    hswap, Option.map_some, Option.bind_some, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  have ek : (BitVec.ofNat 8 kt).setWidth 32 = BitVec.ofNat 32 kt := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  refine ⟨trivial, VG.Proof.X448.X86.mask_xor sw0 hsw kt hk, fun r hr => ?_, trivial, trivial, by rw [ek]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Counters`. -/
section

/-!
# X448 on x86 (32-bit): public loop counters

Counters preserve memory and every other register; the zero flag controls loop
termination.
-/

namespace VG.Proof.X448.X86

open VG VG.X86

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem setCounter_ok (s : State) (k : Nat) (_hk : k < 2 ^ 16) :
    WP isa (.block [.mov .esi (.imm (BitVec.ofNat 32 k))]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 k ∧ (∀ r, r ≠ .esi → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  refine VG.Proof.X448.X86.wp_mov rfl fun t ht => WP.block_nil ⟨ht.gpr, ht.other, ht.mem, ht.rd, ht.wr⟩


theorem decCounter_ok {s : State} {k : Nat} (hk : k < 2 ^ 16)
    (hb : s.gpr .esi = BitVec.ofNat 32 (k + 1)) :
    WP isa (.block [.alu .sub .esi (.imm 1)]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 k ∧ (∀ r, r ≠ .esi → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr ∧ t.zf = some (decide (k = 0)) := by
  have he : s.gpr .esi - (1 : BitVec 32) = BitVec.ofNat 32 k := by
    change s.gpr .esi - BitVec.ofNat 32 1 = _
    rw [hb, BitVec.ofNat_add, BitVec.add_sub_cancel]
  refine VG.Proof.X448.X86.wp_alu (Or.inr (Or.inl rfl)) rfl fun t ht hz => WP.block_nil
    ⟨ht.gpr.trans he, ht.other, ht.mem, ht.rd, ht.wr, ?_⟩
  rw [hz]
  change some (s.gpr .esi - (1 : BitVec 32) == 0) = _
  rw [he, VG.Proof.X448.X86.ofNat_beq_zero (by omega)]

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Iter`. -/
section

/-!
# X448 on x86 (32-bit): the Montgomery ladder

Each iteration consumes one scalar bit and updates the five field slots
according to `ladderStep`.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

def stepEnv (sw : Bool) (e : VG.Proof.X448.X86.Env) : VG.Proof.X448.X86.Env :=
  VG.Proof.X448.X86.applyOps VG.Proof.X448.X86.stepFields (VG.Proof.X448.X86.opSwap 2 4 sw (VG.Proof.X448.X86.opSwap 1 3 sw e))

theorem cswap_fst (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).1 = if decide (sw = 1) = true then b else a := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

theorem cswap_snd (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).2 = if decide (sw = 1) = true then a else b := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

theorem stepEnv_eval (e : VG.Proof.X448.X86.Env) (st : Spec.X448.Ladder) (k : Nat) (u : Spec.X448.Fe) (t : Nat)
    (h0 : e 0 = u) (h1 : e 1 = st.x2) (h2 : e 2 = st.z2) (h3 : e 3 = st.x3) (h4 : e 4 = st.z3) :
    VG.Proof.X448.X86.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 0 = u ∧
    VG.Proof.X448.X86.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 1 = (Spec.X448.ladderStep k u st t).x2 ∧
    VG.Proof.X448.X86.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 2 = (Spec.X448.ladderStep k u st t).z2 ∧
    VG.Proof.X448.X86.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 3 = (Spec.X448.ladderStep k u st t).x3 ∧
    VG.Proof.X448.X86.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 4 = (Spec.X448.ladderStep k u st t).z3 := by
  rw [VG.Proof.X448.ladderStep_eq]
  simp only [↓reduceIte, VG.Proof.X448.X86.stepEnv, VG.Proof.X448.X86.applyOps, VG.Proof.X448.X86.stepFields, FieldOp.apply,
    VG.Proof.X448.X86.opMul, VG.Proof.X448.X86.opAdd, VG.Proof.X448.X86.opSub, VG.Proof.X448.X86.opA24, VG.Proof.X448.X86.opSwap, Function.update_apply,
    VG.Proof.X448.X86.cswap_fst, VG.Proof.X448.X86.cswap_snd, h0, h1, h2, h3, h4]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem swaps_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.BoundedEnv s.mem base)
    {sw : Bool} (hm : s.gpr .ebx = VG.Proof.X448.X86.mask sw) :
    WP isa (.block (VG.Impl.X448.X86.cswap VG.Impl.X448.X86.X2 VG.Impl.X448.X86.X3 ++ VG.Impl.X448.X86.cswap VG.Impl.X448.X86.Z2 VG.Impl.X448.X86.Z3)) s fun t =>
      VG.Proof.X448.X86.Keep base s t ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = VG.Proof.X448.X86.opSwap 2 4 sw (VG.Proof.X448.X86.opSwap 1 3 sw (VG.Proof.X448.X86.E s.mem base)) := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.cswapE hs hb 1 3 (by decide) hm) fun t ⟨tk, tb, tc, te⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86.cswapE (tk.scr hs) tb 2 4 (by decide) (tc.trans hm)) fun u ⟨uk, ub, _, ue⟩ =>
    ⟨tk.trans uk, ub, by rw [ue, te]⟩

theorem counter_zero {s : State} {n : Nat} (hn : n < 2 ^ 32)
    (hc : s.gpr .esi = BitVec.ofNat 32 n) : (s.gpr .esi == 0) = decide (n = 0) := by
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
  scr : VG.Proof.X448.X86.Scr s base
  bounded : VG.Proof.X448.X86.BoundedEnv s.mem base
  regs : VG.Proof.X448.X86.Keeps (.esi :: VG.Proof.X448.X86.workRegs) s₀ s
  esi : s.gpr .esi = BitVec.ofNat 32 n
  mem : VG.Proof.X448.X86.Outside2 base 32 2848 ACC 512 s₀.mem s.mem
  x1 : VG.Proof.X448.X86.E s.mem base 0 = u
  x2 : VG.Proof.X448.X86.E s.mem base 1 = (VG.Proof.X448.ladderAfter k u n).x2
  z2 : VG.Proof.X448.X86.E s.mem base 2 = (VG.Proof.X448.ladderAfter k u n).z2
  x3 : VG.Proof.X448.X86.E s.mem base 3 = (VG.Proof.X448.ladderAfter k u n).x3
  z3 : VG.Proof.X448.X86.E s.mem base 4 = (VG.Proof.X448.ladderAfter k u n).z3
  swap : VG.Proof.X448.X86.word s.mem base VG.Impl.X448.X86.SWAP = BitVec.ofNat 32 (VG.Proof.X448.ladderAfter k u n).swap

theorem ofs_off' (base : Addr) {d : Nat} (h : d < 2 ^ 64) : VG.Proof.X448.X86.ofs base (VG.Proof.X448.X86.off base d) = d :=
  Mem.sub_ofNat_toNat base h

theorem stepBody_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe} {n : Nat} (hn : n < 448)
    (hbits : ∀ t < 448, s₀.mem (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : VG.Proof.X448.X86.LInv base k u s₀ s (n + 1)) :
    WP isa stepBody s fun t => VG.Proof.X448.X86.LInv base k u s₀ t n ∧ (t.gpr .esi == 0) = decide (n = 0) := by
  have hs := hi.scr
  have bitval : s.mem (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + n)) = BitVec.ofNat 8 (VG.Proof.X448.bit k n) := by
    rw [hi.mem _ (by rw [VG.Proof.X448.X86.ofs_off' base (by simp only [VG.Impl.X448.X86.BITS]; omega)]; simp only [VG.Impl.X448.X86.BITS]; omega)
      (by rw [VG.Proof.X448.X86.ofs_off' base (by simp only [VG.Impl.X448.X86.BITS]; omega)]; simp only [VG.Impl.X448.X86.BITS, ACC]; omega)]
    exact hbits n hn
  rw [stepBody, WP.seq_iff,
    show VG.Impl.X448.X86.stepHead = VG.Proof.X448.X86.stepPre ++ (VG.Impl.X448.X86.cswap VG.Impl.X448.X86.X2 VG.Impl.X448.X86.X3 ++ VG.Impl.X448.X86.cswap VG.Impl.X448.X86.Z2 VG.Impl.X448.X86.Z3) by
      simp only [VG.Impl.X448.X86.stepHead, VG.Proof.X448.X86.stepPre, List.append_assoc], WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.stepPre_ok hs hn hi.esi (by have := VG.Proof.X448.bit_le k n; omega)
    (by have := VG.Proof.X448.ladderAfter_swap_le k u (n := n + 1) (by omega); omega) bitval hi.swap)
    fun s₁ ⟨b₁, c₁, g₁, rd₁, wr₁, m₁⟩ => ?_
  have hs₁ : VG.Proof.X448.X86.Scr s₁ base := ⟨by rw [g₁ _ (by decide)]; exact hs.edi,
    wr₁ ▸ hs.wr, by rw [g₁ _ (by decide)]; exact hs.nowrap⟩
  have out₁ : VG.Proof.X448.X86.Outside base VG.Impl.X448.X86.SWAP 4 s.mem s₁.mem := by
    rw [m₁]; exact VG.Proof.X448.X86.writeW_outside _ _ _ (by decide)
  have l₁ : ∀ i : VG.Proof.X448.X86.Index, ∀ j < 28, VG.Proof.X448.X86.limbs s₁.mem base (slot i.val) j = VG.Proof.X448.X86.limbs s.mem base (slot i.val) j := by
    intro i j hj
    exact out₁.limbs (Or.inr (by simp only [slot, VG.Impl.X448.X86.SWAP]; omega))
      (Nat.le_trans (VG.Proof.X448.X86.slot_bound i) (by decide)) hj
  have e₁ : VG.Proof.X448.X86.E s₁.mem base = VG.Proof.X448.X86.E s.mem base := by
    funext i; exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Radix16.valN_congr (l₁ i))
  have bb₁ : VG.Proof.X448.X86.BoundedEnv s₁.mem base := by
    intro i j hj; rw [l₁ i j hj]; exact hi.bounded i j hj
  refine WP.mono (VG.Proof.X448.X86.swaps_ok hs₁ bb₁ c₁) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_
  rw [← VG.Proof.X448.X86.stepFields_impl]
  refine WP.mono (VG.Proof.X448.X86.ops_ok (k₂.scr hs₁) bb₂ VG.Proof.X448.X86.stepFields) fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_
  have core := k₂.trans k₃
  have b₃ : s₃.gpr .esi = BitVec.ofNat 32 n := (core.regs.1 _ (by decide)).trans b₁
  have vals := VG.Proof.X448.X86.stepEnv_eval (VG.Proof.X448.X86.E s.mem base) (VG.Proof.X448.ladderAfter k u (n + 1)) k u n
    hi.x1 hi.x2 hi.z2 hi.x3 hi.z3
  have e₄ : VG.Proof.X448.X86.E s₃.mem base = VG.Proof.X448.X86.stepEnv (decide ((VG.Proof.X448.ladderAfter k u (n + 1)).swap ^^^ VG.Proof.X448.bit k n = 1))
      (VG.Proof.X448.X86.E s.mem base) := by rw [e₃, e₂, e₁]; rfl
  rw [← VG.Proof.X448.ladderAfter_step k u hn, ← e₄] at vals
  refine ⟨⟨core.scr hs₁, bb₃, ?_, b₃, ?_, vals.1, vals.2.1, vals.2.2.1,
    vals.2.2.2.1, vals.2.2.2.2, ?_⟩, VG.Proof.X448.X86.counter_zero (by omega) b₃⟩
  · refine hi.regs.trans ⟨?_, core.regs.2.1.trans rd₁, core.regs.2.2.trans wr₁⟩
    intro r hr
    have hwork : r ∉ VG.Proof.X448.X86.workRegs := fun h => hr (List.mem_cons_of_mem _ h)
    have hpre : r ∉ [Reg.esi, .eax, .ecx, .ebx, .ebp] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr (by subst r; decide), fun h => hr (by subst r; decide),
        fun h => hr (by subst r; decide), fun h => hr (by subst r; decide),
        fun h => hr (by subst r; decide)⟩
    rw [core.regs.1 r hwork, g₁ r hpre]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [core.mem p (by omega) hq, out₁ p (by simp only [VG.Impl.X448.X86.SWAP]; omega)]
  · rw [core.mem.word (by simp only [VG.Impl.X448.X86.SWAP]; omega) (by simp only [VG.Impl.X448.X86.SWAP, ACC]; omega) (by decide),
      m₁, VG.Proof.X448.ladderAfter_step k u hn]
    exact Mem.readW_writeW_self32 _ _ _

/-- Comparing the public counter changes only flags. -/
theorem LInv.of_flags {base : Addr} {k n : Nat} {u : Spec.X448.Fe} {s0 s t : State}
    (h : VG.Proof.X448.X86.LInv base k u s0 s n) (ht : VG.Proof.X448.X86.Fupd s t) : VG.Proof.X448.X86.LInv base k u s0 t n := by
  refine ⟨?_, ht.mem ▸ h.bounded, ?_, ?_, ht.mem ▸ h.mem,
    ht.mem ▸ h.x1, ht.mem ▸ h.x2, ht.mem ▸ h.z2, ht.mem ▸ h.x3, ht.mem ▸ h.z3, ht.mem ▸ h.swap⟩
  · exact ⟨by rw [ht.gpr]; exact h.scr.edi,
      ht.wr ▸ h.scr.wr, by rw [ht.gpr]; exact h.scr.nowrap⟩
  · exact ⟨fun r hr => by rw [ht.gpr]; exact h.regs.1 r hr,
      ht.rd.trans h.regs.2.1, ht.wr.trans h.regs.2.2⟩
  · rw [ht.gpr]; exact h.esi

theorem step_ok {s0 s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe} {n : Nat} (hn : n < 448)
    (hbits : ∀ t < 448, s0.mem (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : VG.Proof.X448.X86.LInv base k u s0 s (n + 1)) :
    WP isa VG.Impl.X448.X86.step s fun t => VG.Proof.X448.X86.LInv base k u s0 t n ∧ t.zf = some (decide (n = 0)) := by
  rw [VG.Impl.X448.X86.step, WP.seq_iff]
  refine WP.mono (VG.Proof.X448.X86.stepBody_ok hn hbits hi) fun t ⟨ht, hz⟩ => ?_
  refine VG.Proof.X448.X86.wp_cmp rfl
    fun u hu he => WP.block_nil ⟨ht.of_flags hu, ?_⟩
  rw [he]
  apply congrArg some
  change (t.gpr .esi - BitVec.ofNat 32 0 == 0) = _
  rw [BitVec.sub_zero]
  exact hz

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.ByteMem`. -/
section

/-!
# X448 on x86 (32-bit): expanding scalar bytes

Each byte is expanded into eight bytes holding its bits, through public
offsets in the working space.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

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
  · simp only [Mem.writeW, Mem.write, Nat.reduceDiv, VG.Proof.X448.X86.sub_toNat_lt_one, h, ite_false]

theorem off_eq_iff (base : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) :
    VG.Proof.X448.X86.off base d = VG.Proof.X448.X86.off base e ↔ d = e := by
  constructor
  · intro h
    have := congrArg (fun x => VG.Proof.X448.X86.ofs base x) h
    simp only [VG.Proof.X448.X86.ofs_off' base hd, VG.Proof.X448.X86.ofs_off' base he] at this
    exact this
  · intro h; rw [h]

theorem writeW8_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (hd : d < 2 ^ 64) {x : Addr}
    (hx : VG.Proof.X448.X86.ofs base x ≠ d) : (m.writeW (VG.Proof.X448.X86.off base d) v) x = m x := by
  rw [VG.Proof.X448.X86.writeW8_apply, ite_eq_right_iff.mpr]
  intro h; subst h; exact absurd (VG.Proof.X448.X86.ofs_off' base hd) hx

theorem write1_eq (m : Mem) (p : Addr) (v : BitVec 8) : m.write p 1 v = m.writeW p v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    ((b.setWidth 32 >>> j) &&& (1 : BitVec 32)).setWidth 8 =
      BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by decide +kernel

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.BitWrite`. -/
section

/-!
# X448 on x86 (32-bit): expanding a scalar byte

Public shifts select each bit and write it to its own byte in the working
space.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

theorem bitShift_ok {s : State} {j : Nat} (hj : j < 8) :
    WP isa (.block (([.mov .edx (.reg .eax)] : List Instr) ++
      if j = 0 then [] else [.shift .shr .edx j])) s fun t =>
      t.gpr .edx = s.gpr .eax >>> j ∧ t.mem = s.mem ∧ VG.Proof.X448.X86.Keeps [.edx] s t := by
  refine VG.Proof.X448.X86.wp_mov rfl fun t ht => ?_
  by_cases hz : j = 0
  · subst j
    exact WP.block_nil ⟨ht.gpr, ht.mem, ht.rest (by decide)⟩
  · rw [ite_eq_right hz]
    refine VG.Proof.X448.X86.wp_shift (by omega) fun u hu => WP.block_nil ⟨?_, hu.mem.trans ht.mem,
      (ht.rest (by decide)).trans (hu.rest (by decide))⟩
    rw [hu.gpr, ht.gpr]

theorem bitJ_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {i : Nat} (hi : i < 56)
    {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32) {j : Nat} (hj : j < 8) :
    WP isa (.block (bitJ i j)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + (8 * i + j)))
        (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧ VG.Proof.X448.X86.Keeps [.edx] s t := by
  rw [bitJ, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.bitShift_ok hj) fun t ⟨tv, tm, tk⟩ => ?_
  refine VG.Proof.X448.X86.wp_alu (by simp [VG.Proof.X448.X86.plain]) rfl fun u hu _ => ?_
  have us := (hs.of_keeps tk (by decide)).of_upd hu (by decide)
  have ea := us.ea (d := VG.Impl.X448.X86.BITS + 8 * i + j) (by simp only [VG.Impl.X448.X86.BITS]; omega)
  have wr := us.write (d := VG.Impl.X448.X86.BITS + 8 * i + j) (n := 1) (by simp only [VG.Impl.X448.X86.BITS]; omega)
  refine VG.Proof.X448.X86.wp_store8 ea wr fun v hv => WP.block_nil ⟨?_, tk.trans ?_⟩
  · rw [hv.mem, hu.mem, tm, Reg8.reg, hu.gpr]
    change s.mem.writeW _ ((t.gpr .edx &&& (1 : BitVec 32)).setWidth 8) = _
    rw [tv, ha, VG.Proof.X448.X86.bit_byte b j hj, Nat.add_assoc]
  · exact (hu.rest (by decide)).trans (hv.rest _)

/-- Expanding eight bits preserves each byte already written. -/
theorem byteBits_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {i : Nat} (hi : i < 56)
    {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap (bitJ i))) s fun t =>
      (∀ j < 8, t.mem (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      VG.Proof.X448.X86.Outside base (VG.Impl.X448.X86.BITS + 8 * i) 8 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.edx] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    VG.Proof.X448.X86.Outside base (VG.Impl.X448.X86.BITS + 8 * i) 8 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.edx] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (bitJ i n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.X448.X86.bitJ_ok (hs.of_keeps tk (by decide)) hi
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, VG.Proof.X448.X86.writeW8_apply]
      have eq : VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + (8 * i + j)) = VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + (8 * i + n)) ↔ j = n := by
        rw [VG.Proof.X448.X86.off_eq_iff base (by simp only [VG.Impl.X448.X86.BITS]; omega) (by simp only [VG.Impl.X448.X86.BITS]; omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact VG.Proof.X448.X86.writeW8_outside _ _ _ (by simp only [VG.Impl.X448.X86.BITS]; omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Clamp`. -/
section

/-!
# X448 on x86 (32-bit): clamping the scalar bits

Clear bits zero and one, and set bit 447, as RFC 7748 requires.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def clamp : List Instr :=
  [.mov .edx (.imm 0), .store8 (VG.Impl.X448.X86.sc VG.Impl.X448.X86.BITS) .dl, .store8 (VG.Impl.X448.X86.sc (VG.Impl.X448.X86.BITS + 1)) .dl,
    .mov .edx (.imm 1), .store8 (VG.Impl.X448.X86.sc (VG.Impl.X448.X86.BITS + 447)) .dl]

def clampMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (VG.Proof.X448.X86.off base VG.Impl.X448.X86.BITS) (0 : BitVec 8)).writeW (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + 1))
    (0 : BitVec 8)).writeW (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + 447)) (1 : BitVec 8)

theorem storeByte_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {d : Nat} (hd : d < 4096) :
    WP isa (.block [.store8 (VG.Impl.X448.X86.sc d) .dl]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.X86.off base d) ((s.gpr .edx).setWidth 8) ∧ VG.Proof.X448.X86.Keeps [] s t := by
  refine VG.Proof.X448.X86.wp_store8 (hs.ea (d := d) (by omega)) (hs.write (d := d) (n := 1) (by omega))
    fun t ht => WP.block_nil ⟨ht.mem, (ht.rest _)⟩

theorem putByte_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {d : Nat} (hd : d < 4096)
    (v : BitVec 32) :
    WP isa (.block [.mov .edx (.imm v), .store8 (VG.Impl.X448.X86.sc d) .dl]) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.X86.off base d) (v.setWidth 8) ∧
      t.gpr .edx = v ∧ VG.Proof.X448.X86.Keeps [.edx] s t := by
  refine VG.Proof.X448.X86.wp_mov rfl fun t ht => ?_
  refine WP.mono (VG.Proof.X448.X86.storeByte_ok (hs.of_upd ht (by decide)) hd) fun u ⟨um, uk⟩ => ?_
  exact ⟨by rw [um, ht.mem, ht.gpr], (uk.1 _ (by decide)).trans ht.gpr,
    ((ht.rest (by decide))).trans (uk.mono (by simp))⟩

theorem clamp_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) :
    WP isa (.block VG.Proof.X448.X86.clamp) s fun t => t.mem = VG.Proof.X448.X86.clampMem s.mem base ∧ VG.Proof.X448.X86.Keeps [.edx] s t := by
  change WP isa (.block (([.mov .edx (.imm 0), .store8 (VG.Impl.X448.X86.sc VG.Impl.X448.X86.BITS) .dl] : List Instr) ++
    ([.store8 (VG.Impl.X448.X86.sc (VG.Impl.X448.X86.BITS + 1)) .dl] : List Instr) ++
    [.mov .edx (.imm 1), .store8 (VG.Impl.X448.X86.sc (VG.Impl.X448.X86.BITS + 447)) .dl])) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.putByte_ok hs (by decide : BITS < 4096) 0) fun t ⟨tm, tv, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.storeByte_ok (hs.of_keeps tk (by decide)) (by decide : BITS + 1 < 4096))
    fun u ⟨um, uk⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86.putByte_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
    (by decide : BITS + 447 < 4096) 1) fun v ⟨vm, _, vk⟩ => ?_
  refine ⟨?_, tk.trans ((uk.mono (by simp)).trans vk)⟩
  rw [vm, um, tv, tm]
  rfl

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Bits`. -/
section

/-!
# X448 on x86 (32-bit): decoding the scalar bits

The unrolled expansion reads exactly 56 bytes, then clears bits zero and one
and sets bit 447.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448

def bitRegs : List Reg := [.eax, .edx]

def expandBits : List Instr := (List.range 56).flatMap fun i =>
  [.movzx8 .eax (VG.Impl.X448.X86.at_ .esi i)] ++ (List.range 8).flatMap (bitJ i)

theorem expandBits_ok {s : State} {base k : Addr} (hs : VG.Proof.X448.X86.Scr s base)
    (hk : (s.gpr .esi).setWidth 64 = k) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ i < 56, InRegions (s.rd ++ s.wr) (VG.Proof.X448.X86.off k i) 1)
    (hd : ∀ i < 56, 8192 ≤ VG.Proof.X448.X86.ofs base (VG.Proof.X448.X86.off k i)) :
    WP isa (.block VG.Proof.X448.X86.expandBits) s fun t =>
      VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.bitRegs s t ∧ VG.Proof.X448.X86.Outside base VG.Impl.X448.X86.BITS 448 s.mem t.mem ∧
      ∀ j < 448, t.mem (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + j)) =
        BitVec.ofNat 8 (((s.mem (VG.Proof.X448.X86.off k (j / 8))).toNat >>> (j % 8)) &&& 1) := by
  let inv := fun n (t : State) => VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.bitRegs s t ∧ VG.Proof.X448.X86.Outside base VG.Impl.X448.X86.BITS (8 * n) s.mem t.mem ∧
    ∀ j < 8 * n, t.mem (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + j)) =
      BitVec.ofNat 8 (((s.mem (VG.Proof.X448.X86.off k (j / 8))).toNat >>> (j % 8)) &&& 1)
  have step : ∀ n t, n < 56 → inv n t → WP isa (.block
      ([.movzx8 .eax (VG.Impl.X448.X86.at_ .esi n)] ++ (List.range 8).flatMap (bitJ n))) t (inv (n + 1)) := by
    intro n t hn ⟨tk, tm, tb⟩
    have ea : t.ea (VG.Impl.X448.X86.at_ .esi n) = VG.Proof.X448.X86.off k n := by
      change VG.X86.addr (t.gpr .esi) n = _
      rw [tk.1 _ (by decide), addr_eq (by omega), hk]
    refine VG.Proof.X448.X86.wp_load8 ea (by rw [tk.2.1, tk.2.2]; exact hr n hn) fun u hu => ?_
    have us := (hs.of_keeps tk (by decide)).of_upd hu (by decide)
    refine WP.mono (VG.Proof.X448.X86.byteBits_ok us hn hu.gpr) fun v ⟨vb, vm, vk⟩ => ?_
    have byte : t.mem (VG.Proof.X448.X86.off k n) = s.mem (VG.Proof.X448.X86.off k n) :=
      tm _ (Or.inr (by have := hd n hn; simp only [VG.Impl.X448.X86.BITS]; omega))
    refine ⟨tk.trans ((hu.rest (by decide)).trans (vk.mono (by simp [VG.Proof.X448.X86.bitRegs]))), ?_, ?_⟩
    · rw [hu.mem] at vm
      exact (tm.mono (by omega) (by omega)).trans (vm.mono (by omega) (by omega))
    · intro j hj
      rcases Nat.lt_or_ge j (8 * n) with h | h
      · rw [vm _ (Or.inl (by rw [VG.Proof.X448.X86.ofs_off' base (by simp only [VG.Impl.X448.X86.BITS]; omega)]; omega)), hu.mem]
        exact tb j h
      · have e := vb (j - 8 * n) (by omega)
        rw [show 8 * n + (j - 8 * n) = j by omega, byte] at e
        rw [e, show j / 8 = n by omega, show j % 8 = j - 8 * n by omega]
  exact wp_range_flatMap (M := isa) (N := 56) inv step 56 (by decide) s
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ hj => by omega⟩

theorem getD_bytesAt (m : Mem) (k : Addr) {q : Nat} (hq : q < 56) :
    (Spec.X448.bytesAt m k 56).getD q 0 = m (k + BitVec.ofNat 64 q) := by
  simp only [Spec.X448.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq, Option.map_some, Option.getD_some]

/-- Expanded and clamped bytes are precisely the decoded scalar's bits. -/
theorem bitsData_ok {s : State} {base k : Addr} (hs : VG.Proof.X448.X86.Scr s base)
    (hk : (s.gpr .esi).setWidth 64 = k) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ i < 56, InRegions (s.rd ++ s.wr) (VG.Proof.X448.X86.off k i) 1)
    (hd : ∀ i < 56, 8192 ≤ VG.Proof.X448.X86.ofs base (VG.Proof.X448.X86.off k i)) :
    WP isa (.block (VG.Proof.X448.X86.expandBits ++ VG.Proof.X448.X86.clamp)) s fun t =>
      (∀ r, r ∉ VG.Proof.X448.X86.bitRegs → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      VG.Proof.X448.X86.Outside base VG.Impl.X448.X86.BITS 448 s.mem t.mem ∧
      ∀ j < 448, t.mem (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + j)) =
        BitVec.ofNat 8 (VG.Proof.X448.bit (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem k 56)) j) := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.expandBits_ok hs hk hfit hr hd) fun s₂ ⟨k₂, o₂, b₂⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86.clamp_ok (hs.of_keeps k₂ (by decide))) fun s₃ ⟨m₃, k₃⟩ => ?_
  refine ⟨fun r hr => ?_, k₃.2.1.trans k₂.2.1, k₃.2.2.trans k₂.2.2, fun x hx => ?_, fun t ht => ?_⟩
  · rw [k₃.1 r (by intro he; simp only [List.mem_singleton] at he; subst r; exact hr (by decide))]
    exact k₂.1 r hr
  · rw [m₃, VG.Proof.X448.X86.clampMem]
    have o : ∀ d, VG.Impl.X448.X86.BITS ≤ d → d < VG.Impl.X448.X86.BITS + 448 → VG.Proof.X448.X86.ofs base x ≠ d := fun d h₁ h₂ h => by omega
    rw [VG.Proof.X448.X86.writeW8_outside _ _ _ (by simp only [VG.Impl.X448.X86.BITS]; omega) (o (VG.Impl.X448.X86.BITS + 447) (by omega) (by omega)),
      VG.Proof.X448.X86.writeW8_outside _ _ _ (by simp only [VG.Impl.X448.X86.BITS]; omega) (o (VG.Impl.X448.X86.BITS + 1) (by omega) (by omega)),
      VG.Proof.X448.X86.writeW8_outside _ _ _ (by simp only [VG.Impl.X448.X86.BITS]; omega) (o VG.Impl.X448.X86.BITS (by omega) (by omega))]
    exact o₂ x hx
  · rw [m₃, VG.Proof.X448.X86.clampMem, scalar_bit (length_bytesAt _ _ _) ht]
    simp (disch := simp only [BITS]; omega) only [VG.Proof.X448.X86.writeW8_apply, VG.Proof.X448.X86.off_eq_iff, Nat.add_left_cancel_iff,
      Nat.add_eq_left]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 447 ∨ (2 ≤ t ∧ t < 447)) with
      rfl | rfl | rfl | ⟨h₃, h₄⟩
    · rfl
    · rfl
    · rfl
    · simp only [show t ≠ 447 by omega, show t ≠ 1 by omega, show t ≠ 0 by omega,
        show ¬t < 2 by omega, ite_false]
      rw [b₂ t (by omega), VG.Proof.X448.X86.getD_bytesAt _ _ (by omega)]


end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Contract`. -/
section

/-!
# X448 on x86 (32-bit): the contract the proof is written against

The facts of the shared contract (`Spec.X448.x448Contract`) the proof uses,
stated for x86; the shared contract implies it (`sig_implies`, in
`Main.lean`).
-/

namespace VG.Proof.X448

open VG VG.X86 in
/-- `vg_x448(out, scalar, point, scratch)`, whose arguments are on the
stack (cdecl). -/
def x448X86 : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 56⟩
    let scalar : Region := ⟨(arg s 1).setWidth 64, 56⟩
    let point : Region := ⟨(arg s 2).setWidth 64, 56⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [scalar, point, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 56 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 56 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 56 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' := Spec.X448.bytesAt s'.mem ((arg s 0).setWidth 64) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem ((arg s 1).setWidth 64) 56)
      (Spec.X448.bytesAt s.mem ((arg s 2).setWidth 64) 56)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

end VG.Proof.X448

namespace VG.Proof.X448.X86

open VG VG.X86

section
variable (s₀ : State)
/-- The arguments and the regions, on entry. -/
abbrev scR (b : BitVec 32) : Region := ⟨b.setWidth 64, 8192⟩
abbrev outR : Region := ⟨(arg s₀ 0).setWidth 64, 56⟩
abbrev scalarR : Region := ⟨(arg s₀ 1).setWidth 64, 56⟩
abbrev pointR : Region := ⟨(arg s₀ 2).setWidth 64, 56⟩
abbrev argsR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩
end

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.X448.X86.scalarR s₀, VG.Proof.X448.X86.pointR s₀, VG.Proof.X448.X86.argsR s₀]
  wr : s₀.wr = [VG.Proof.X448.X86.outR s₀, VG.Proof.X448.X86.scR (arg s₀ 3)]
  out_sc : (VG.Proof.X448.X86.outR s₀).Disjoint (VG.Proof.X448.X86.scR (arg s₀ 3))
  scalar_sc : (VG.Proof.X448.X86.scalarR s₀).Disjoint (VG.Proof.X448.X86.scR (arg s₀ 3))
  point_sc : (VG.Proof.X448.X86.pointR s₀).Disjoint (VG.Proof.X448.X86.scR (arg s₀ 3))
  args_out : (VG.Proof.X448.X86.argsR s₀).Disjoint (VG.Proof.X448.X86.outR s₀)
  args_sc : (VG.Proof.X448.X86.argsR s₀).Disjoint (VG.Proof.X448.X86.scR (arg s₀ 3))
  ret_out : (VG.Proof.X448.X86.retR s₀).Disjoint (VG.Proof.X448.X86.outR s₀)
  ret_sc : (VG.Proof.X448.X86.retR s₀).Disjoint (VG.Proof.X448.X86.scR (arg s₀ 3))
  out_fit : (arg s₀ 0).toNat + 56 ≤ 2 ^ 32
  scalar_fit : (arg s₀ 1).toNat + 56 ≤ 2 ^ 32
  point_fit : (arg s₀ 2).toNat + 56 ≤ 2 ^ 32
  sc_fit : (arg s₀ 3).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem Pre.of (s₀ : State) (h : Proof.X448.x448X86.pre s₀) : VG.Proof.X448.X86.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

theorem argAddr_eq (s : State) (i : Nat) : argAddr s i = addr (s.gpr .esp) (4 + 4 * i) := rfl

/-- An argument slot's address, in the argument region. -/
theorem arg_contains {s : State} (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat}
    (hi : i < 4) : (⟨argAddr s 0, 16⟩ : Region).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  VG.Proof.X25519.X86.sub_contains (x := s.gpr .esp) (a := 4) (k := 16) (by omega_using [hfit]) (by omega_using [])
    (by omega_using [hi]) (by decide)

namespace Pre
variable {s₀ : State} (hp : VG.Proof.X448.X86.Pre s₀)
include hp

theorem argIn {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨VG.Proof.X448.X86.argsR s₀, by rw [hp.rd]; simp, VG.Proof.X448.X86.arg_contains hp.sp_fit hi⟩

/-- An argument, in memory the code has written only in the working space. -/
theorem arg_same {m : Mem} (hf : Frame [VG.Proof.X448.X86.scR (arg s₀ 3)] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (VG.Proof.X448.X86.arg_contains hp.sp_fit hi)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.args_sc) (by decide)

theorem sc_in : VG.Proof.X448.X86.scR (arg s₀ 3) ∈ s₀.wr := by rw [hp.wr]; simp

theorem out_in : VG.Proof.X448.X86.outR s₀ ∈ s₀.wr := by rw [hp.wr]; simp

end Pre

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Frame`. -/
section

/-!
# X448 on x86 (32-bit): memory frames

Scratch-only writes preserve the cdecl arguments, which remain on the
unchanged stack.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

theorem Outside.frame {base : Addr} {n : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.Outside base 0 n m m') :
    Frame [⟨base, n⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this
  change 0 + n ≤ (x - base).toNat
  omega))

theorem FieldMem.whole {base : Addr} {o : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.FieldMem base o m m')
    (ho : o + 112 ≤ 8192) : VG.Proof.X448.X86.Outside base 0 8192 m m' := fun p hp =>
  h p (by omega) (by simp only [ACC]; omega)

theorem Outside2.whole {base : Addr} {x nx y ny : Nat} {m m' : Mem}
    (h : VG.Proof.X448.X86.Outside2 base x nx y ny m m') (hx : x + nx ≤ 8192) (hy : y + ny ≤ 8192) :
    VG.Proof.X448.X86.Outside base 0 8192 m m' := fun p hp => h p (by omega) (by omega)

theorem loadArg_ok {s₀ s : State} (hp : VG.Proof.X448.X86.Pre s₀)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr)
    (hm : VG.Proof.X448.X86.Outside ((arg s₀ 3).setWidth 64) 0 8192 s₀.mem s.mem)
    {i : Nat} (hi : i < 4) {d : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, VG.Proof.X448.X86.Upd s t d (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (.mov d (.mem (at_ .esp (4 + 4 * i))) :: is)) s Q := by
  refine VG.Proof.X448.X86.wp_load (a := addr (s₀.gpr .esp) (4 + 4 * i))
    (by change addr (s.gpr .esp) (4 + 4 * i) = _; rw [hsp])
    (by rw [hr, hw]; exact hp.argIn hi) fun t ht => ?_
  rw [hp.arg_same hm.frame hi] at ht
  exact k t ht

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.BitsInput`. -/
section

/-!
# X448 on x86 (32-bit): loading the scalar argument

Scratch-only setup leaves the scalar pointer and input bytes available for
expansion.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448

def bitsRegs : List Reg := [.esi, .eax, .edx]

theorem bits_ok {s₀ s : State} (pre : VG.Proof.X448.X86.Pre s₀)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr)
    {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base)
    (hm : VG.Proof.X448.X86.Outside base 0 8192 s₀.mem s.mem) (hs : VG.Proof.X448.X86.Scr s base)
    (hkd : ∀ i < 56, 8192 ≤ VG.Proof.X448.X86.ofs base (VG.Proof.X448.X86.off ((arg s₀ 1).setWidth 64) i)) :
    WP isa bits s fun t =>
      VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.bitsRegs s t ∧ VG.Proof.X448.X86.Outside base BITS 448 s.mem t.mem ∧
      ∀ j < 448, t.mem (VG.Proof.X448.X86.off base (BITS + j)) =
        BitVec.ofNat 8 (VG.Proof.X448.bit (Spec.X448.decodeScalar448
          (Spec.X448.bytesAt s.mem ((arg s₀ 1).setWidth 64) 56)) j) := by
  change WP isa (.block (.mov .esi (.mem (at_ .esp 8)) :: (VG.Proof.X448.X86.expandBits ++ VG.Proof.X448.X86.clamp))) s _
  refine VG.Proof.X448.X86.loadArg_ok pre hsp hr hw (hbase ▸ hm) (by decide : 1 < 4) fun u hu => ?_
  refine WP.mono (VG.Proof.X448.X86.bitsData_ok (hs.of_upd hu (by decide)) (by rw [hu.gpr])
    (by rw [hu.gpr]; exact pre.scalar_fit)
    (by intro i hi; rw [hu.rd, hu.wr, hr, hw]; exact ⟨VG.Proof.X448.X86.scalarR s₀,
      by rw [pre.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩)
    hkd) fun t ⟨tg, tr, tw, tm, tb⟩ => ?_
  rw [hu.mem] at tm tb
  exact ⟨(hu.rest (by decide)).trans ((show VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.bitRegs u t from ⟨tg, tr, tw⟩).mono
    (by simp [VG.Proof.X448.X86.bitRegs, VG.Proof.X448.X86.bitsRegs])), tm, tb⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Decode`. -/
section

/-!
# X448 on x86 (32-bit): decoding a coordinate limb

Two byte loads construct a 16-bit limb, which is written to both initial
coordinate slots.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16
theorem byte_rotate (b : BitVec 8) : (b.setWidth 32).rotateRight 24 = b.setWidth 32 <<< 8 := by
  have hz : b.setWidth 32 >>> 24 = 0 := by
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    change b.toNat % 2 ^ 32 / 2 ^ 24 = 0
    omega
  rw [BitVec.rotateRight_def, hz]
  exact BitVec.zero_or


theorem decodeLimb_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.X86.Scr s base) {i : Nat}
    (hi : i < 28) (hp : (s.gpr .esi).setWidth 64 = p) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (VG.Proof.X448.X86.off p j) 1) :
    WP isa (.block (decodeLimb i)) s fun t =>
      t.mem = (s.mem.writeW (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.X1 + 4 * i)) (BitVec.ofNat 32 (VG.Proof.X448.Radix16.decoded s.mem p i))).writeW
        (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.X3 + 4 * i)) (BitVec.ofNat 32 (VG.Proof.X448.Radix16.decoded s.mem p i)) ∧ VG.Proof.X448.X86.Keeps [.eax, .edx] s t := by
  have ea0 : (s.gpr .esi + BitVec.ofNat 32 (2 * i)).setWidth 64 = VG.Proof.X448.X86.off p (2 * i) := by
    change VG.X86.addr (s.gpr .esi) _ = _
    rw [VG.X86.addr_eq (by omega), hp]
  have ea1 : (s.gpr .esi + BitVec.ofNat 32 (2 * i + 1)).setWidth 64 = VG.Proof.X448.X86.off p (2 * i + 1) := by
    change VG.X86.addr (s.gpr .esi) _ = _
    rw [VG.X86.addr_eq (by omega), hp]
  unfold decodeLimb
  refine VG.Proof.X448.X86.wp_load8 (a := VG.Proof.X448.X86.off p (2 * i)) ea0 (hr _ (by omega)) fun s1 h1 => ?_
  refine VG.Proof.X448.X86.wp_load8 (a := VG.Proof.X448.X86.off p (2 * i + 1))
    (by change VG.X86.addr (s1.gpr .esi) _ = _; rw [h1.other .esi (by decide)]; exact ea1)
    (by rw [h1.rd, h1.wr]; exact hr _ (by omega)) fun s2 h2 => ?_
  refine VG.Proof.X448.X86.wp_shift (by decide) fun sr hrot => ?_
  refine VG.Proof.X448.X86.wp_alu (by simp [VG.Proof.X448.X86.plain]) rfl fun s3 h3 _ => ?_
  have value : s3.gpr .eax = BitVec.ofNat 32 (VG.Proof.X448.Radix16.decoded s.mem p i) := by
    rw [h3.gpr]
    change sr.gpr .eax + sr.gpr .edx = _
    rw [hrot.other .eax (by decide), hrot.gpr]
    rw [h2.other .eax (by decide), h1.gpr, h2.gpr, h1.mem, VG.Proof.X448.X86.byte_rotate]
    apply BitVec.eq_of_toNat_eq
    have h0 := (s.mem (VG.Proof.X448.X86.off p (2 * i))).isLt
    have h1 := (s.mem (VG.Proof.X448.X86.off p (2 * i + 1))).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat, VG.Proof.X448.Radix16.decoded, byteN]
    simp only [VG.Proof.X448.X86.off] at h0 h1 ⊢
    omega
  have hs1 := hs.of_upd h1 (by decide)
  have hs2 := hs1.of_upd h2 (by decide)
  have hsrot := hs2.of_upd hrot (by decide)
  have hs3 := hsrot.of_upd h3 (by decide)
  refine VG.Proof.X448.X86.store_ok hs3 (by simp only [VG.Impl.X448.X86.X1, slot]; omega) fun s4 h4 => ?_
  have hs4 := hs3.of_keeps ((h4.rest [])) (by decide)
  refine VG.Proof.X448.X86.store_ok hs4 (by simp only [VG.Impl.X448.X86.X3, slot]; omega) fun s5 h5 => WP.block_nil ⟨?_, ?_⟩
  · rw [h5.mem, h4.mem, h3.mem, hrot.mem, h2.mem, h1.mem, h4.gpr, value]
  · exact ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans
      ((hrot.rest (by decide)).trans ((h3.rest (by decide)).trans ((h4.rest _).trans (h5.rest _))))))

/-- The two coordinate words lie inside their respective slots. -/
theorem decodeLimb_outside (m : Mem) (base : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32) :
    VG.Proof.X448.X86.Outside2 base VG.Impl.X448.X86.X1 (4 * (i + 1)) VG.Impl.X448.X86.X3 (4 * (i + 1)) m
      ((m.writeW (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.X1 + 4 * i)) v).writeW (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.X3 + 4 * i)) v) := by
  intro p hp hq
  rw [VG.Proof.X448.X86.writeW_outside _ _ _ (by simp only [VG.Impl.X448.X86.X3, slot]; omega) p (by omega),
    VG.Proof.X448.X86.writeW_outside _ _ _ (by simp only [VG.Impl.X448.X86.X1, slot]; omega) p (by omega)]

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.DecodeAll`. -/
section

/-!
# X448 on x86 (32-bit): decoding the whole coordinate

The 28 limb loads fill two slots while preserving input bytes outside the
working space.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem decoded_congr {m m' : Mem} {p : Addr} {i : Nat} (hi : i < 28)
    (h : ∀ j < 56, m' (VG.Proof.X448.X86.off p j) = m (VG.Proof.X448.X86.off p j)) : VG.Proof.X448.Radix16.decoded m' p i = VG.Proof.X448.Radix16.decoded m p i := by
  simp only [VG.Proof.X448.Radix16.decoded, byteN]
  rw [h (2 * i) (by omega), h (2 * i + 1) (by omega)]

theorem decodeAll_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.X86.Scr s base)
    (hp : (s.gpr .esi).setWidth 64 = p) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (VG.Proof.X448.X86.off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ VG.Proof.X448.X86.ofs base (VG.Proof.X448.X86.off p j)) :
    WP isa (.block ((List.range 28).flatMap decodeLimb)) s fun t =>
      (∀ j < 28, VG.Proof.X448.X86.limbs t.mem base VG.Impl.X448.X86.X1 j = VG.Proof.X448.Radix16.decoded s.mem p j) ∧
      (∀ j < 28, VG.Proof.X448.X86.limbs t.mem base VG.Impl.X448.X86.X3 j = VG.Proof.X448.Radix16.decoded s.mem p j) ∧
      VG.Proof.X448.X86.Outside2 base VG.Impl.X448.X86.X1 112 VG.Impl.X448.X86.X3 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax, .edx] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, VG.Proof.X448.X86.limbs t.mem base VG.Impl.X448.X86.X1 j = VG.Proof.X448.Radix16.decoded s.mem p j) ∧
    (∀ j < n, VG.Proof.X448.X86.limbs t.mem base VG.Impl.X448.X86.X3 j = VG.Proof.X448.Radix16.decoded s.mem p j) ∧
    VG.Proof.X448.X86.Outside2 base VG.Impl.X448.X86.X1 (4 * n) VG.Impl.X448.X86.X3 (4 * n) s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax, .edx] s t
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block (decodeLimb n)) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tp : (t.gpr .esi).setWidth 64 = p := by rw [tk.1 _ (by decide)]; exact hp
    have tfit : (t.gpr .esi).toNat + 56 ≤ 2 ^ 32 := by rw [tk.1 _ (by decide)]; exact hfit
    have tr : ∀ j < 56, InRegions (t.rd ++ t.wr) (VG.Proof.X448.X86.off p j) 1 := by
      intro j hj; rw [tk.2.1, tk.2.2]; exact hr j hj
    have byte : ∀ j < 56, t.mem (VG.Proof.X448.X86.off p j) = s.mem (VG.Proof.X448.X86.off p j) := by
      intro j hj
      have h := hd j hj
      exact tm _ (Or.inr (by simp only [VG.Impl.X448.X86.X1, slot]; omega)) (Or.inr (by simp only [VG.Impl.X448.X86.X3, slot]; omega))
    have eq := VG.Proof.X448.X86.decoded_congr hn byte
    refine WP.mono (VG.Proof.X448.X86.decodeLimb_ok (hs.of_keeps tk (by decide)) hn tp tfit tr) fun u ⟨um, uk⟩ => ?_
    rw [eq] at um
    let v := BitVec.ofNat 32 (VG.Proof.X448.Radix16.decoded s.mem p n)
    have vn : v.toNat = VG.Proof.X448.Radix16.decoded s.mem p n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (decoded_lt s.mem p n) (by decide))]
    have pair := fun j (hj : j < 28) => VG.Proof.X448.X86.pair_write (m := t.mem) (base := base)
      (x := VG.Impl.X448.X86.X1) (y := VG.Impl.X448.X86.X3) (by decide) (by decide) (by decide) hn hj v v
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
      exact (tm.mono (by omega) (by omega)).trans (VG.Proof.X448.X86.decodeLimb_outside _ _ hn _)
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hj => by omega, fun _ hj => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.FinalSwap`. -/
section

/-!
# X448 on x86 (32-bit): the final ladder swap

The last swap bit selects the coordinates that are converted back to affine
form.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

theorem mask_of : ∀ a < 2, (0 : BitVec 32) - BitVec.ofNat 32 a = VG.Proof.X448.X86.mask (decide (a = 1)) := by decide

theorem swapMask_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : VG.Proof.X448.X86.word s.mem base VG.Impl.X448.X86.SWAP = BitVec.ofNat 32 sw) :
    WP isa (.block [ld .ecx VG.Impl.X448.X86.SWAP, .mov .ebx (.imm 0), .alu .sub .ebx (.reg .ecx)]) s
      fun t => t.gpr .ebx = VG.Proof.X448.X86.mask (decide (sw = 1)) ∧ t.mem = s.mem ∧ VG.Proof.X448.X86.Keeps [.ecx, .ebx] s t := by
  refine VG.Proof.X448.X86.load_ok hs (by decide) fun s1 h1 => ?_
  refine VG.Proof.X448.X86.wp_mov rfl fun s2 h2 => ?_
  refine VG.Proof.X448.X86.wp_alu (Or.inr (Or.inl rfl)) rfl fun s3 h3 _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [h3.gpr]
    change s2.gpr .ebx - s2.gpr .ecx = _
    rw [h2.gpr, h2.other .ecx (by decide), h1.gpr, hw]
    exact VG.Proof.X448.X86.mask_of sw hsw
  · rw [h3.mem, h2.mem, h1.mem]
  · exact (h1.rest (by decide)).trans ((h2.rest (by decide)).trans (h3.rest (by decide)))

theorem lastSwap_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.BoundedEnv s.mem base)
    {sw : Nat} (hsw : sw < 2) (hw : VG.Proof.X448.X86.word s.mem base VG.Impl.X448.X86.SWAP = BitVec.ofNat 32 sw) :
    WP isa (.block VG.Impl.X448.X86.lastSwap) s fun t => VG.Proof.X448.X86.Keep base s t ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧
      VG.Proof.X448.X86.E t.mem base = VG.Proof.X448.X86.opSwap 2 4 (decide (sw = 1)) (VG.Proof.X448.X86.opSwap 1 3 (decide (sw = 1)) (VG.Proof.X448.X86.E s.mem base)) := by
  rw [VG.Impl.X448.X86.lastSwap, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.swapMask_ok hs hsw hw) fun t ⟨tc, tm, tk⟩ => ?_
  have kt : VG.Proof.X448.X86.Keep base s t := ⟨tk.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide), tm ▸ Outside2.refl _ _ _ _ _ _⟩
  refine WP.mono (VG.Proof.X448.X86.swaps_ok (kt.scr hs) (tm ▸ hb) tc) fun u ⟨ku, bu, eu⟩ =>
    ⟨kt.trans ku, bu, by rw [eu, tm]⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Save`. -/
section

/-!
# X448 on x86 (32-bit): saving the callee-saved registers

Four scratch words hold the incoming values of ebx, esi, edi, and ebp until
the final restore.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- The callee-saved registers and their scratch words. -/
def savedSlots : Spill.Slots := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

theorem savedSlots_bound : ∀ p ∈ VG.Proof.X448.X86.savedSlots, p.2 + 4 ≤ 16 := by decide

abbrev Saved (base : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop := Spill.Saved m (VG.Proof.X448.X86.off base) g VG.Proof.X448.X86.savedSlots

theorem Saved.outside {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : VG.Proof.X448.X86.Saved base g m)
    {o n : Nat} (ho : VG.Proof.X448.X86.Outside base o n m m') (h16 : 16 ≤ o) : VG.Proof.X448.X86.Saved base g m' :=
  h.of_readW fun p hp => have := VG.Proof.X448.X86.savedSlots_bound p hp; ho.word (Or.inl (by omega)) (by omega)

theorem Saved.outside2 {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : VG.Proof.X448.X86.Saved base g m)
    {x nx y ny : Nat} (ho : VG.Proof.X448.X86.Outside2 base x nx y ny m m') (hx : 16 ≤ x) (hy : 16 ≤ y) :
    VG.Proof.X448.X86.Saved base g m' :=
  h.of_readW fun p hp => have := VG.Proof.X448.X86.savedSlots_bound p hp
    ho.word (Or.inl (by omega)) (Or.inl (by omega)) (by omega)

theorem Saved.field {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : VG.Proof.X448.X86.Saved base g m)
    {o : Nat} (hm : VG.Proof.X448.X86.FieldMem base o m m') (ho : 16 ≤ o) : VG.Proof.X448.X86.Saved base g m' :=
  h.of_readW fun p hp => have := VG.Proof.X448.X86.savedSlots_bound p hp
    hm.word (Or.inl (by omega)) (by simp only [ACC]; omega)

/-- A frame of the first `n` bytes at `base`. -/
theorem Outside.of_frame {base : Addr} {n : Nat} {m m' : Mem} (hf : Frame [⟨base, n⟩] m m') :
    VG.Proof.X448.X86.Outside base 0 n m m' :=
  fun x hx => hf x fun r hr => by
    rw [List.mem_singleton.mp hr]
    simp only [Region.Contains]
    simp only [VG.Proof.X448.X86.ofs] at hx
    omega

theorem save_ok {s : State} (hp : VG.Proof.X448.X86.Pre s) :
    WP isa (.block save) s fun t =>
      VG.Proof.X448.X86.Scr t ((arg s 3).setWidth 64) ∧ VG.Proof.X448.X86.Saved ((arg s 3).setWidth 64) s.gpr t.mem ∧
      VG.Proof.X448.X86.Outside ((arg s 3).setWidth 64) 0 16 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax, .edi] s t := by
  change WP isa (.block (.mov .eax (.mem (at_ .esp 16)) ::
    (Spill.saveCode .eax VG.Proof.X448.X86.savedSlots ++ [.mov .edi (.reg .eax)]))) s _
  refine VG.Proof.X448.X86.loadArg_ok hp rfl rfl rfl (Outside.refl _ _ _ _) (by decide : 3 < 4) fun t ht => ?_
  have hfit := hp.sc_fit
  refine Spill.save_ofNat_ok VG.Proof.X448.X86.savedSlots (n := 16) (by decide) (by rw [ht.gpr]; omega)
    (fun p h => by rw [ht.gpr, ht.wr]; exact ⟨_, hp.sc_in, VG.Proof.X448.X86.contains_sc (by have := VG.Proof.X448.X86.savedSlots_bound p h; omega)⟩)
    fun u hu => ?_
  have hm : u.mem = Spill.saveMem s.mem (VG.Proof.X448.X86.off ((arg s 3).setWidth 64)) s.gpr VG.Proof.X448.X86.savedSlots := by
    rw [hu.mem, ht.gpr, ht.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => ht.other _ (by revert p h; decide)
  refine VG.Proof.X448.X86.wp_mov rfl fun v hv => WP.block_nil ?_
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, (ht.rest (by decide)).trans
    (⟨fun r _ => by rw [hu.gpr], hu.rd, hu.wr⟩ : VG.Proof.X448.X86.Keeps [.eax, .edi] t u) |>.trans (hv.rest (by decide))⟩
  · rw [hv.gpr, hu.gpr, ht.gpr]
  · rw [hv.wr, hu.wr, ht.wr]; exact hp.sc_in
  · rw [hv.gpr, hu.gpr, ht.gpr]; exact hfit
  · rw [hv.mem, hm]; exact Spill.saveMem_saved_ofNat _ _ _ (n := 16) (by decide) (by decide)
  · rw [hv.mem, hm]
    exact Outside.of_frame (Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
      Offset.contains_base _ (VG.Proof.X448.X86.savedSlots_bound p h) (by have := VG.Proof.X448.X86.savedSlots_bound p h; omega))

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Restore`. -/
section

/-!
# X448 on x86 (32-bit): restoring the callee-saved registers

The address is retained in eax so edi can be restored after the other saved
registers.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def restoreRegs : List Reg := [.eax, .ebx, .esi, .ebp, .edi]

theorem restore_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {g : Reg → BitVec 32}
    (hsv : VG.Proof.X448.X86.Saved base g s.mem) :
    WP isa (.block restore) s fun t =>
      (∀ p ∈ VG.Proof.X448.X86.savedSlots, t.gpr p.1 = g p.1) ∧ t.mem = s.mem ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.restoreRegs s t := by
  rw [show restore = .mov .eax (.reg .edi) ::
    (Spill.restoreCode .eax [(.ebx, 0), (.esi, 4), (.ebp, 12), (.edi, 8)] ++ []) from rfl]
  refine VG.Proof.X448.X86.wp_mov rfl fun t ht => ?_
  have hb : (t.gpr .eax).setWidth 64 = base := by rw [ht.gpr]; exact hs.edi
  refine Spill.restore_ofNat_ok _ (n := 16) (by decide) (by rw [ht.gpr]; have := hs.nowrap; omega)
    (by decide) (fun p h => by
      rw [hb, ht.rd, ht.wr]; exact hs.read (by have := VG.Proof.X448.X86.savedSlots_bound p (by revert p h; decide); omega))
    (by rw [hb, ht.mem]; exact hsv.sub (by decide)) fun u hu => WP.block_nil ⟨fun p h => hu.gpr p (by
      revert p h; decide), by rw [hu.mem, ht.mem], fun r hr => ?_, by rw [hu.rd, ht.rd], by rw [hu.wr, ht.wr]⟩
  simp only [VG.Proof.X448.X86.restoreRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [hu.other r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2]), ht.other r hr.1]

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Initial`. -/
section

/-!
# X448 on x86 (32-bit): initial field values

Every slot starts with bounded limbs. The decoded coordinates are retained,
and the ladder starts with X2 = 1, Z2 = 0, Z3 = 1, and a zero swap bit.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem zeroSlotsHead_ok (s : State) :
    WP isa (.block [.alu .xor .eax (.reg .eax)]) s fun t =>
      t.gpr .eax = 0 ∧ t.mem = s.mem ∧ VG.Proof.X448.X86.Keeps [.eax] s t := by
  refine VG.Proof.X448.X86.wp_alu (by simp [VG.Proof.X448.X86.plain]) rfl fun t ht _ => WP.block_nil ⟨?_, ht.mem, ht.rest (by decide)⟩
  rw [ht.gpr]
  exact BitVec.xor_self

def zeroSlots : List Instr :=
  [.alu .xor .eax (.reg .eax)] ++ (List.range 64).map (fun i => st .eax (VG.Impl.X448.X86.X2 + 4 * i)) ++
    (List.range 576).map (fun i => st .eax (VG.Impl.X448.X86.Z3 + 4 * i))

theorem zeroSlots_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) :
    WP isa (.block VG.Proof.X448.X86.zeroSlots) s fun t =>
      (∀ i : VG.Proof.X448.X86.Index, ∀ j < 28, VG.Proof.X448.X86.limbs t.mem base (slot i.val) j =
        if i = 0 ∨ i = 3 then VG.Proof.X448.X86.limbs s.mem base (slot i.val) j else 0) ∧
      t.gpr .eax = 0 ∧ VG.Proof.X448.X86.Outside base VG.Impl.X448.X86.X2 2688 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax] s t := by
  rw [VG.Proof.X448.X86.zeroSlots, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.zeroSlotsHead_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  have ts := hs.of_keeps tk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.fill_ok ts (by decide : X2 + 4 * 64 ≤ 4096) tz) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86.fill_ok (ts.of_keeps uk (by decide)) (by decide : Z3 + 4 * 576 ≤ 4096)
    ((uk.1 _ (by decide)).trans tz)) fun v ⟨vf, vm, vk⟩ => ?_
  refine ⟨?_, (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tz), ?_, ?_⟩
  · intro i j hj
    have il := i.isLt
    by_cases h0 : i = 0
    · subst i
      rw [ite_eq_left (Or.inl rfl)]
      change (VG.Proof.X448.X86.word v.mem base (64 + 4 * j)).toNat = _
      rw [vm.word (by change 64 + 4 * j + 4 ≤ 576 ∨ _; omega) (by omega),
        um.word (by change 64 + 4 * j + 4 ≤ 192 ∨ _; omega) (by omega), tm]
      rfl
    · by_cases h3 : i = 3
      · subst i
        rw [ite_eq_left (Or.inr rfl)]
        change (VG.Proof.X448.X86.word v.mem base (448 + 4 * j)).toNat = _
        rw [vm.word (by change 448 + 4 * j + 4 ≤ 576 ∨ _; omega) (by omega),
          um.word (by change _ ∨ 192 + 4 * 64 ≤ 448 + 4 * j; omega) (by omega), tm]
        rfl
      · rw [ite_eq_right (not_or_intro h0 h3)]
        have i0 : i.val ≠ 0 := fun h => h0 (Fin.ext h)
        have i3 : i.val ≠ 3 := fun h => h3 (Fin.ext h)
        rcases Nat.lt_or_ge i.val 3 with h | h
        · have index : slot i.val + 4 * j = VG.Impl.X448.X86.X2 + 4 * (32 * (i.val - 1) + j) := by
            simp only [slot, VG.Impl.X448.X86.X2]; omega
          change (VG.Proof.X448.X86.word v.mem base (slot i.val + 4 * j)).toNat = 0
          rw [vm.word (Or.inl (by simp only [slot, VG.Impl.X448.X86.Z3]; omega)) (by simp only [slot]; omega), index]
          exact uf _ (by omega)
        · have index : slot i.val + 4 * j = VG.Impl.X448.X86.Z3 + 4 * (32 * (i.val - 4) + j) := by
            simp only [slot, VG.Impl.X448.X86.Z3]; omega
          change (VG.Proof.X448.X86.word v.mem base (slot i.val + 4 * j)).toNat = 0
          rw [index]
          exact vf _ (by omega)
  · rw [← tm]
    exact (um.mono (by omega) (by omega)).trans (vm.mono (by decide) (by decide))
  · exact tk.trans ((uk.trans vk).mono (fun _ hr => False.elim (List.not_mem_nil hr)))

def initialMem (m : Mem) (base : Addr) : Mem :=
  ((m.writeW (VG.Proof.X448.X86.off base VG.Impl.X448.X86.SWAP) (0 : BitVec 32)).writeW (VG.Proof.X448.X86.off base VG.Impl.X448.X86.X2) (1 : BitVec 32)).writeW
    (VG.Proof.X448.X86.off base VG.Impl.X448.X86.Z3) (1 : BitVec 32)

theorem initialStores_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hz : s.gpr .eax = 0) :
    WP isa (.block [st .eax VG.Impl.X448.X86.SWAP, .mov .eax (.imm 1), st .eax VG.Impl.X448.X86.X2, st .eax VG.Impl.X448.X86.Z3]) s
      fun t => t.mem = VG.Proof.X448.X86.initialMem s.mem base ∧ VG.Proof.X448.X86.Keeps [.eax] s t := by
  refine VG.Proof.X448.X86.store_ok hs (by decide) fun s1 h1 => ?_
  have hs1 := hs.of_keeps (h1.rest []) (by decide)
  refine VG.Proof.X448.X86.wp_mov rfl fun s2 h2 => ?_
  have hs2 := hs1.of_upd h2 (by decide)
  refine VG.Proof.X448.X86.store_ok hs2 (by decide) fun s3 h3 => ?_
  have hs3 := hs2.of_keeps (h3.rest []) (by decide)
  refine VG.Proof.X448.X86.store_ok hs3 (by decide) fun s4 h4 => WP.block_nil ⟨?_, ?_⟩
  · rw [h4.mem, h3.mem, h2.mem, h1.mem, h3.gpr, h2.gpr, hz]
    rfl
  · exact (h1.rest _).trans ((h2.rest (by decide)).trans ((h3.rest _).trans (h4.rest _)))

theorem initialMem_limb (m : Mem) (base : Addr) (i : VG.Proof.X448.X86.Index) {j : Nat} (hj : j < 28) :
    VG.Proof.X448.X86.limbs (VG.Proof.X448.X86.initialMem m base) base (slot i.val) j =
      if (i = 1 ∨ i = 4) ∧ j = 0 then 1 else VG.Proof.X448.X86.limbs m base (slot i.val) j := by
  have il := i.isLt
  have hd : slot i.val + 4 * j + 4 ≤ 8192 := by simp only [slot]; omega
  have hm : (slot i.val + 4 * j) % 4 = 0 := by simp only [slot]; omega
  have es : slot i.val + 4 * j ≠ VG.Impl.X448.X86.SWAP := by simp only [slot, VG.Impl.X448.X86.SWAP]; omega
  have ex : slot i.val + 4 * j = VG.Impl.X448.X86.X2 ↔ i = 1 ∧ j = 0 := by
    simp only [slot, VG.Impl.X448.X86.X2]
    constructor
    · intro h; exact ⟨Fin.ext (by omega), by omega⟩
    · rintro ⟨rfl, rfl⟩; rfl
  have ez : slot i.val + 4 * j = VG.Impl.X448.X86.Z3 ↔ i = 4 ∧ j = 0 := by
    simp only [slot, VG.Impl.X448.X86.Z3]
    constructor
    · intro h; exact ⟨Fin.ext (by omega), by omega⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [VG.Proof.X448.X86.limbs, VG.Proof.X448.X86.initialMem]
  rw [VG.Proof.X448.X86.word_write_aligned _ base (by decide) hd (by decide) hm,
    VG.Proof.X448.X86.word_write_aligned _ base (by decide) hd (by decide) hm,
    VG.Proof.X448.X86.word_write_aligned _ base (by decide) hd (by decide) hm, ite_eq_right es]
  simp only [ex, ez]
  by_cases h1 : i = 1 <;> by_cases h4 : i = 4 <;> by_cases h0 : j = 0 <;>
    simp only [h1, h4, h0, and_true, and_false, or_true, or_false,
      true_or, ite_true, ite_false] <;> rfl

theorem initialMem_outside (m : Mem) (base : Addr) : VG.Proof.X448.X86.Outside base 32 2848 m (VG.Proof.X448.X86.initialMem m base) := by
  intro p hp
  simp only [VG.Proof.X448.X86.initialMem]
  rw [VG.Proof.X448.X86.writeW_outside _ _ _ (by decide : Z3 + 4 ≤ 8192) p (by simp only [VG.Impl.X448.X86.Z3, slot]; omega),
    VG.Proof.X448.X86.writeW_outside _ _ _ (by decide : X2 + 4 ≤ 8192) p (by simp only [VG.Impl.X448.X86.X2, slot]; omega),
    VG.Proof.X448.X86.writeW_outside _ _ _ (by decide : SWAP + 4 ≤ 8192) p (by simp only [VG.Impl.X448.X86.SWAP]; omega)]

theorem initSlots_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base)
    (h0 : VG.Proof.X448.X86.Bounded s.mem base VG.Impl.X448.X86.X1) (h3 : VG.Proof.X448.X86.Bounded s.mem base VG.Impl.X448.X86.X3) :
    WP isa (.block initSlots) s fun t =>
      VG.Proof.X448.X86.BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base 0 = VG.Proof.X448.X86.E s.mem base 0 ∧ VG.Proof.X448.X86.E t.mem base 1 = 1 ∧
      VG.Proof.X448.X86.E t.mem base 2 = 0 ∧ VG.Proof.X448.X86.E t.mem base 3 = VG.Proof.X448.X86.E s.mem base 3 ∧ VG.Proof.X448.X86.E t.mem base 4 = 1 ∧
      VG.Proof.X448.X86.word t.mem base VG.Impl.X448.X86.SWAP = 0 ∧ VG.Proof.X448.X86.Outside base 32 2848 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax] s t := by
  change WP isa (.block (VG.Proof.X448.X86.zeroSlots ++ [st .eax VG.Impl.X448.X86.SWAP, .mov .eax (.imm 1),
    st .eax VG.Impl.X448.X86.X2, st .eax VG.Impl.X448.X86.Z3])) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.zeroSlots_ok hs) fun t ⟨tf, tz, tm, tk⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86.initialStores_ok (hs.of_keeps tk (by decide)) tz) fun u ⟨um, uk⟩ => ?_
  have lf : ∀ i : VG.Proof.X448.X86.Index, ∀ j < 28, VG.Proof.X448.X86.limbs u.mem base (slot i.val) j =
      if (i = 1 ∨ i = 4) ∧ j = 0 then 1 else
        if i = 0 ∨ i = 3 then VG.Proof.X448.X86.limbs s.mem base (slot i.val) j else 0 := by
    intro i j hj
    rw [um, VG.Proof.X448.X86.initialMem_limb _ _ i hj, tf i j hj]
  have zval : VG.Proof.X448.Radix16.valN (fun _ => 0) 28 = 0 := by decide
  have oval : VG.Proof.X448.Radix16.valN (fun j => if j = 0 then 1 else 0) 28 = 1 := by decide +kernel
  have l0 : ∀ j < 28, VG.Proof.X448.X86.limbs u.mem base VG.Impl.X448.X86.X1 j = VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X1 j := by
    intro j hj
    have h := lf (⟨0, by decide⟩ : VG.Proof.X448.X86.Index) j hj
    dsimp only [VG.Impl.X448.X86.X1]
    simpa (config := {decide := true}) only [false_or, false_and, ite_true, ite_false] using h
  have l1 : ∀ j < 28, VG.Proof.X448.X86.limbs u.mem base VG.Impl.X448.X86.X2 j = if j = 0 then 1 else 0 := by
    intro j hj
    have h := lf (⟨1, by decide⟩ : VG.Proof.X448.X86.Index) j hj
    dsimp only [VG.Impl.X448.X86.X2]
    simpa (config := {decide := true}) only [true_or, true_and, ite_false] using h
  have l2 : ∀ j < 28, VG.Proof.X448.X86.limbs u.mem base VG.Impl.X448.X86.Z2 j = 0 := by
    intro j hj
    have h := lf (⟨2, by decide⟩ : VG.Proof.X448.X86.Index) j hj
    dsimp only [VG.Impl.X448.X86.Z2]
    simpa (config := {decide := true}) only [false_or, false_and, ite_false] using h
  have l3 : ∀ j < 28, VG.Proof.X448.X86.limbs u.mem base VG.Impl.X448.X86.X3 j = VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X3 j := by
    intro j hj
    have h := lf (⟨3, by decide⟩ : VG.Proof.X448.X86.Index) j hj
    dsimp only [VG.Impl.X448.X86.X3]
    simpa (config := {decide := true}) only [false_or, false_and, ite_true, ite_false] using h
  have l4 : ∀ j < 28, VG.Proof.X448.X86.limbs u.mem base VG.Impl.X448.X86.Z3 j = if j = 0 then 1 else 0 := by
    intro j hj
    have h := lf (⟨4, by decide⟩ : VG.Proof.X448.X86.Index) j hj
    dsimp only [VG.Impl.X448.X86.Z3]
    simpa (config := {decide := true}) only [or_true, true_and, ite_false] using h
  refine ⟨?_, congrArg VG.Proof.X448.toFe (VG.Proof.X448.Radix16.valN_congr l0), ?_, ?_, congrArg VG.Proof.X448.toFe (VG.Proof.X448.Radix16.valN_congr l3), ?_, ?_, ?_, tk.trans uk⟩
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
  · change VG.Proof.X448.toFe (VG.Proof.X448.X86.fe u.mem base VG.Impl.X448.X86.X2) = 1
    rw [show VG.Proof.X448.X86.fe u.mem base VG.Impl.X448.X86.X2 = VG.Proof.X448.Radix16.valN (fun j => if j = 0 then 1 else 0) 28 from VG.Proof.X448.Radix16.valN_congr l1, oval]
    exact VG.Proof.X448.toFe_one
  · change VG.Proof.X448.toFe (VG.Proof.X448.X86.fe u.mem base VG.Impl.X448.X86.Z2) = 0
    rw [show VG.Proof.X448.X86.fe u.mem base VG.Impl.X448.X86.Z2 = VG.Proof.X448.Radix16.valN (fun _ => 0) 28 from VG.Proof.X448.Radix16.valN_congr l2, zval]
    exact VG.Proof.X448.toFe_zero
  · change VG.Proof.X448.toFe (VG.Proof.X448.X86.fe u.mem base VG.Impl.X448.X86.Z3) = 1
    rw [show VG.Proof.X448.X86.fe u.mem base VG.Impl.X448.X86.Z3 = VG.Proof.X448.Radix16.valN (fun j => if j = 0 then 1 else 0) 28 from VG.Proof.X448.Radix16.valN_congr l4, oval]
    exact VG.Proof.X448.toFe_one
  · rw [um, VG.Proof.X448.X86.initialMem,
      VG.Proof.X448.X86.word_write_aligned _ base (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide),
      VG.Proof.X448.X86.word_write_aligned _ base (by decide) (by decide) (by decide) (by decide), ite_eq_right (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [um]
    exact (tm.mono (by decide) (by decide)).trans (VG.Proof.X448.X86.initialMem_outside _ _)

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Setup`. -/
section

/-!
# X448 on x86 (32-bit): reading the arguments

Setup saves the callee-saved registers, decodes the coordinate, and
initializes the ladder.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

def setupRegs : List Reg := [.eax, .edx, .edi, .esi]

theorem setup_ok {s : State} (hp : VG.Proof.X448.X86.Pre s) {base p : Addr}
    (hc : (arg s 3).setWidth 64 = base) (hpoint : (arg s 2).setWidth 64 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (VG.Proof.X448.X86.off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ VG.Proof.X448.X86.ofs base (VG.Proof.X448.X86.off p j)) :
    WP isa (.block setup) s fun t =>
      VG.Proof.X448.X86.Scr t base ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.setupRegs s t ∧
      VG.Proof.X448.X86.Outside base 0 8192 s.mem t.mem ∧ VG.Proof.X448.X86.Saved base s.gpr t.mem ∧
      VG.Proof.X448.X86.E t.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      VG.Proof.X448.X86.E t.mem base 1 = 1 ∧ VG.Proof.X448.X86.E t.mem base 2 = 0 ∧
      VG.Proof.X448.X86.E t.mem base 3 = VG.Proof.X448.X86.E t.mem base 0 ∧ VG.Proof.X448.X86.E t.mem base 4 = 1 ∧ VG.Proof.X448.X86.word t.mem base SWAP = 0 := by
  simp only [setup, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.save_ok hp) fun t ⟨ts, tv, tm, tk⟩ => ?_
  refine VG.Proof.X448.X86.loadArg_ok hp (tk.1 _ (by decide)) tk.2.1 tk.2.2
    (tm.mono (by decide) (by decide)) (by decide : 2 < 4) fun t' ht => ?_
  rw [hc] at ts tv tm
  have ts' := ts.of_upd ht (by decide)
  have tm' : VG.Proof.X448.X86.Outside base 0 16 s.mem t'.mem := by rw [ht.mem]; exact tm
  have tk' : VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.setupRegs s t' := (tk.mono (by simp [VG.Proof.X448.X86.setupRegs])).trans (ht.rest (by decide))
  change WP isa (.block ((List.range 28).flatMap decodeLimb ++ initSlots)) t' _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.decodeAll_ok ts' (by rw [ht.gpr]; exact hpoint)
    (by rw [ht.gpr]; exact hp.point_fit)
    (by intro j hj; rw [tk'.2.1, tk'.2.2]; exact hr j hj) hd) fun u ⟨ux, uy, um, uk⟩ => ?_
  have ub0 : VG.Proof.X448.X86.Bounded u.mem base X1 := by intro j hj; rw [ux j hj]; exact decoded_lt _ _ _
  have ub3 : VG.Proof.X448.X86.Bounded u.mem base X3 := by intro j hj; rw [uy j hj]; exact decoded_lt _ _ _
  have uv0 : VG.Proof.X448.X86.E u.mem base 0 = toFe (VG.Proof.X25519.leNum (Spec.X448.bytesAt t'.mem p 56)) := by
    apply congrArg toFe
    exact (VG.Proof.X448.Radix16.valN_congr ux).trans (VG.Proof.X448.Radix16.decoded_val t'.mem p 28).symm
  have uv3 : VG.Proof.X448.X86.E u.mem base 3 = VG.Proof.X448.X86.E u.mem base 0 := congrArg toFe ((VG.Proof.X448.Radix16.valN_congr uy).trans (VG.Proof.X448.Radix16.valN_congr ux).symm)
  have byte : Spec.X448.bytesAt t'.mem p 56 = Spec.X448.bytesAt s.mem p 56 := by
    apply List.map_congr_left
    intro j hj
    exact tm' _ (Or.inr (Nat.le_trans (by decide) (hd j (List.mem_range.mp hj))))
  rw [byte] at uv0
  refine WP.mono (VG.Proof.X448.X86.initSlots_ok (ts'.of_keeps uk (by decide)) ub0 ub3)
    fun v ⟨vb, v0, v1, v2, v3, v4, vw, vm, vk⟩ => ?_
  refine ⟨(ts'.of_keeps uk (by decide)).of_keeps vk (by decide), vb,
    tk'.trans ((uk.mono ?_).trans (vk.mono ?_)),
    (tm'.mono (by decide) (by decide)).trans ?_,
    ((show VG.Proof.X448.X86.Saved base s.gpr t'.mem from ht.mem ▸ tv).outside2 um (by decide) (by decide)).outside vm (by decide),
    ?_, v1, v2, v3.trans (uv3.trans v0.symm), v4, vw⟩
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide
  · intro r h; simp only [List.mem_singleton] at h; subst r; decide
  · exact (show VG.Proof.X448.X86.Outside base 0 8192 t'.mem u.mem from fun q h =>
      um q (by simp only [X1, slot]; omega) (by simp only [X3, slot]; omega)).trans
      (vm.mono (by decide) (by decide))
  · rw [decodeUCoordinate_eq (length_bytesAt _ _ _)]
    exact v0.trans uv0

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Pack`. -/
section

/-!
# X448 on x86 (32-bit): encoding a limb

Two byte stores encode each 16-bit limb in little-endian order without
requiring output alignment.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

def packMem (m : Mem) (p : Addr) (i : Nat) (v : BitVec 32) : Mem :=
  (m.writeW (VG.Proof.X448.X86.off p (2 * i)) (v.setWidth 8)).writeW (VG.Proof.X448.X86.off p (2 * i + 1)) ((v >>> 8).setWidth 8)

theorem packStep_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.X86.Scr s base) {i : Nat} (hi : i < 28)
    (hp : (s.gpr .esi).setWidth 64 = p) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hw : ∀ j < 2, InRegions s.wr (VG.Proof.X448.X86.off p (2 * i + j)) 1) :
    WP isa (.block (packLimb i)) s fun t =>
      t.mem = VG.Proof.X448.X86.packMem s.mem p i (VG.Proof.X448.X86.word s.mem base (VG.Impl.X448.X86.X2 + 4 * i)) ∧ VG.Proof.X448.X86.Keeps [.eax] s t := by
  have ea : ∀ j < 2, VG.X86.addr (s.gpr .esi) (2 * i + j) = VG.Proof.X448.X86.off p (2 * i + j) := by
    intro j hj; rw [addr_eq (by omega), hp]
  unfold packLimb
  refine VG.Proof.X448.X86.load_ok hs (by simp only [VG.Impl.X448.X86.X2, slot]; omega) fun t ht => ?_
  refine VG.Proof.X448.X86.wp_store8 (a := VG.Proof.X448.X86.off p (2 * i)) (by change VG.X86.addr (t.gpr .esi) _ = _; rw [ht.other .esi (by decide)]; exact ea 0 (by decide))
    (by rw [ht.wr]; exact hw 0 (by decide)) fun u hu => ?_
  refine VG.Proof.X448.X86.wp_shift (by decide) fun v hv => ?_
  refine VG.Proof.X448.X86.wp_store8 (a := VG.Proof.X448.X86.off p (2 * i + 1)) (by change VG.X86.addr (v.gpr .esi) _ = _; rw [hv.other .esi (by decide), hu.gpr, ht.other .esi (by decide)]; exact ea 1 (by decide))
    (by rw [hv.wr, hu.wr, ht.wr]; exact hw 1 (by decide)) fun w hw' => WP.block_nil ⟨?_, ?_⟩
  · rw [hw'.mem, hv.mem, hu.mem, ht.mem, Reg8.reg, hv.gpr, hu.gpr, ht.gpr]; rfl
  · exact ((ht.rest (by decide)).trans ((hu.rest _).trans
      ((hv.rest (by decide)).trans (hw'.rest _))))

theorem packMem_decoded (m : Mem) (p : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32)
    (hv : v.toNat < VG.Proof.X448.Radix16.radix) : VG.Proof.X448.Radix16.decoded (VG.Proof.X448.X86.packMem m p i v) p i = v.toNat := by
  have hn : VG.Proof.X448.X86.off p (2 * i) ≠ VG.Proof.X448.X86.off p (2 * i + 1) := by
    rw [ne_eq, VG.Proof.X448.X86.off_eq_iff p (by omega) (by omega)]; omega
  simp only [VG.Proof.X448.Radix16.decoded, byteN, VG.Proof.X448.X86.packMem, VG.Proof.X448.X86.writeW8_apply, hn, ite_false, ite_true,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [VG.Proof.X448.Radix16.radix] at hv
  omega

theorem packMem_outside (m : Mem) (p : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32) :
    VG.Proof.X448.X86.Outside p (2 * i) 2 m (VG.Proof.X448.X86.packMem m p i v) := by
  intro x hx
  rw [VG.Proof.X448.X86.packMem, VG.Proof.X448.X86.writeW8_outside _ _ _ (by omega) (by omega),
    VG.Proof.X448.X86.writeW8_outside _ _ _ (by omega) (by omega)]

theorem packLimb_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.Bounded s.mem base VG.Impl.X448.X86.X2)
    {i : Nat} (hi : i < 28) (hp : (s.gpr .esi).setWidth 64 = p)
    (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hw : ∀ j < 2, InRegions s.wr (VG.Proof.X448.X86.off p (2 * i + j)) 1) :
    WP isa (.block (packLimb i)) s fun t =>
      VG.Proof.X448.Radix16.decoded t.mem p i = VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X2 i ∧ VG.Proof.X448.X86.Outside p (2 * i) 2 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s t := by
  refine WP.mono (VG.Proof.X448.X86.packStep_ok hs hi hp hfit hw) fun t ⟨tm, tk⟩ => ?_
  refine ⟨?_, ?_, tk.mono ?_⟩
  · rw [tm]; exact VG.Proof.X448.X86.packMem_decoded _ _ hi _ (hb i hi)
  · rw [tm]; exact VG.Proof.X448.X86.packMem_outside _ _ hi _
  · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Output`. -/
section

/-!
# X448 on x86 (32-bit): the output buffer

Output stores cover exactly 56 bytes and preserve the disjoint working space.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- Writes to the output preserve a word in the disjoint working space. -/
theorem output_word {m m' : Mem} {base p : Addr} {n d : Nat} (h : VG.Proof.X448.X86.Outside p 0 n m m') (hn : n ≤ 56)
    (hd : d + 4 ≤ 8192) (hfar : ∀ j < 8192, 56 ≤ VG.Proof.X448.X86.ofs p (VG.Proof.X448.X86.off base j)) :
    VG.Proof.X448.X86.word m' base d = VG.Proof.X448.X86.word m base d := by
  apply Mem.readW_congr
  intro i hi
  rw [Offset.add_add]
  exact h _ (Or.inr (Nat.le_trans (by omega : 0 + n ≤ 56) (hfar _ (by omega))))

theorem output_ok {s : State} {base p : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.Bounded s.mem base VG.Impl.X448.X86.X2)
    (hp : (s.gpr .esi).setWidth 64 = p)
    (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32) (hw : ∀ j < 56, InRegions s.wr (VG.Proof.X448.X86.off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ VG.Proof.X448.X86.ofs p (VG.Proof.X448.X86.off base j)) :
    WP isa (.block ((List.range 28).flatMap packLimb)) s fun t =>
      Spec.X448.bytesAt t.mem p 56 = VG.Proof.X25519.leBytes 56 (VG.Proof.X448.X86.fe s.mem base VG.Impl.X448.X86.X2) ∧
      VG.Proof.X448.X86.Outside p 0 56 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.Radix16.decoded t.mem p i = VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X2 i) ∧ VG.Proof.X448.X86.Outside p 0 (2 * n) s.mem t.mem ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (packLimb n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have eq : ∀ j < 28, VG.Proof.X448.X86.limbs t.mem base VG.Impl.X448.X86.X2 j = VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X2 j := by
      intro j hj
      exact congrArg BitVec.toNat (VG.Proof.X448.X86.output_word tm (by omega) (by simp only [VG.Impl.X448.X86.X2, slot]; omega) hfar)
    have tb : VG.Proof.X448.X86.Bounded t.mem base VG.Impl.X448.X86.X2 := by intro j hj; rw [eq j hj]; exact hb j hj
    refine WP.mono (VG.Proof.X448.X86.packLimb_ok (p := p) (hs.of_keeps tk (by decide)) tb hn (by rw [tk.1 _ (by decide)]; exact hp)
      (by rw [tk.1 _ (by decide)]; exact hfit)
      (by intro j hj; rw [tk.2.2]; exact hw _ (by omega))) fun u ⟨uv, um, uk⟩ => ?_
    refine ⟨?_, (tm.mono (by decide) (by omega)).trans (um.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    by_cases h : i = n
    · subst i; exact uv.trans (eq n hn)
    · have byte : ∀ j < 2, u.mem (VG.Proof.X448.X86.off p (2 * i + j)) = t.mem (VG.Proof.X448.X86.off p (2 * i + j)) := by
        intro j hj
        exact um _ (Or.inl (by rw [VG.Proof.X448.X86.ofs_off' p (by omega)]; omega))
      simp only [VG.Proof.X448.Radix16.decoded, byteN]
      have b0 := byte 0 (by decide)
      have b1 := byte 1 (by decide)
      simp only [VG.Proof.X448.X86.off, Nat.add_zero] at b0 b1
      rw [b0, b1]
      exact tf i (by omega)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tf, tm, tk⟩ =>
    ⟨VG.Proof.X448.Radix16.packed_bytes tf, tm, tk⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.FreezePrep`. -/
section

/-!
# X448 on x86 (32-bit): preparing canonical reduction

Adding one in limbs zero and fourteen implements the addition of 1 + 2²²⁴
before carry propagation.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem incrementStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {d : Nat}
    (hd : d + 4 ≤ 4096) :
    WP isa (.block [ld .eax d, .alu .add .eax (.imm 1), st .eax d]) s
      fun s' => s'.mem = s.mem.writeW (VG.Proof.X448.X86.off base d) (VG.Proof.X448.X86.word s.mem base d + (1 : BitVec 32)) ∧
        VG.Proof.X448.X86.Keeps [.eax] s s' := by
  refine VG.Proof.X448.X86.load_ok hs (by omega) fun t ht => ?_
  refine VG.Proof.X448.X86.wp_alu (by simp [VG.Proof.X448.X86.plain]) rfl fun u hu _ => ?_
  refine VG.Proof.X448.X86.store_ok ((hs.of_upd ht (by decide)).of_upd hu (by decide)) (by omega)
    fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, hu.mem, ht.mem, hu.gpr]; change _ = s.mem.writeW _ _; rw [ht.gpr]; rfl
  · exact ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans (hv.rest _)))

theorem incrementLimb_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {k : Nat} (hk : k < 28)
    (hb : VG.Proof.X448.X86.limbs s.mem base TMP k + 1 < 2 ^ 32) :
    WP isa (.block [ld .eax (TMP + 4 * k), .alu .add .eax (.imm 1),
      st .eax (TMP + 4 * k)]) s fun t =>
      (∀ i < 28, VG.Proof.X448.X86.limbs t.mem base TMP i =
        if i = k then VG.Proof.X448.X86.limbs s.mem base TMP i + 1 else VG.Proof.X448.X86.limbs s.mem base TMP i) ∧
      VG.Proof.X448.X86.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax] s t := by
  have hd : TMP + 4 * k + 4 ≤ 4096 := by simp only [TMP]; omega
  refine WP.mono (VG.Proof.X448.X86.incrementStep_ok hs hd) fun t ⟨hm, ht⟩ => ?_
  refine ⟨?_, ?_, ht⟩
  · intro i hi
    change (VG.Proof.X448.X86.word t.mem base (TMP + 4 * i)).toNat = _
    rw [hm, VG.Proof.X448.X86.word_write s.mem base (by omega) (by simp only [TMP]; omega)]
    by_cases h : i = k
    · rw [ite_eq_left h, ite_eq_left h, h, BitVec.toNat_add]
      change (VG.Proof.X448.X86.limbs s.mem base TMP k + 1) % 2 ^ 32 = _
      exact Nat.mod_eq_of_lt hb
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [hm]
    exact (VG.Proof.X448.X86.writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)

theorem freezePrep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.Bounded s.mem base VG.Impl.X448.X86.X2) :
    WP isa (.block (VG.Impl.X448.X86.copy TMP VG.Impl.X448.X86.X2 ++ [0, 14].flatMap (fun i =>
      [ld .eax (TMP + 4 * i), .alu .add .eax (.imm 1),
        st .eax (TMP + 4 * i)]))) s fun t =>
      (∀ i < 28, VG.Proof.X448.X86.limbs t.mem base TMP i = VG.Proof.X448.Radix16.freezeCoeff (VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X2) i) ∧
      VG.Proof.X448.X86.Outside base TMP 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.clob s t := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.copy_ok hs (by decide) (by decide) (by decide)) fun t ⟨tf, tm, tk⟩ => ?_
  have bound : ∀ i < 28, VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X2 i + 1 < 2 ^ 32 := by
    intro i hi; have h := hb i hi; simp only [VG.Proof.X448.Radix16.radix] at h; omega
  change WP isa (.block
    (([ld .eax (TMP + 4 * 0), .alu .add .eax (.imm 1),
       st .eax (TMP + 4 * 0)] : List Instr) ++
     [ld .eax (TMP + 4 * 14), .alu .add .eax (.imm 1),
       st .eax (TMP + 4 * 14)])) t _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.incrementLimb_ok (hs.of_keeps tk (by decide)) (k := 0) (by decide)
    (by rw [tf 0 (by decide)]; exact bound 0 (by decide))) fun u ⟨uf, um, uk⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86.incrementLimb_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide))
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

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Select`. -/
section

/-!
# X448 on x86 (32-bit): selecting the canonical representative

An XOR mask selects each limb from the original value or the carried temporary
value.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def selectStep (i : Nat) : List Instr :=
  [ld .eax (VG.Impl.X448.X86.X2 + 4 * i), ld .edx (TMP + 4 * i), .alu .xor .edx (.reg .eax),
    .alu .and .edx (.reg .ecx), .alu .xor .eax (.reg .edx), st .eax (VG.Impl.X448.X86.X2 + 4 * i)]

theorem selectStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {i : Nat} (hi : i < 28)
    {sw : Bool} (hc : s.gpr .ecx = VG.Proof.X448.X86.mask sw) :
    WP isa (.block (VG.Proof.X448.X86.selectStep i)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.X2 + 4 * i))
        (if sw then VG.Proof.X448.X86.word s.mem base (TMP + 4 * i) else VG.Proof.X448.X86.word s.mem base (VG.Impl.X448.X86.X2 + 4 * i)) ∧
      VG.Proof.X448.X86.Keeps [.eax, .edx] s t := by
  unfold VG.Proof.X448.X86.selectStep
  refine VG.Proof.X448.X86.load_ok hs (by simp only [VG.Impl.X448.X86.X2, slot]; omega) fun t ht => ?_
  have ts := hs.of_upd ht (by decide)
  refine VG.Proof.X448.X86.load_ok ts (by simp only [TMP]; omega) fun u hu => ?_
  have us := ts.of_upd hu (by decide)
  refine VG.Proof.X448.X86.wp_alu (by simp [VG.Proof.X448.X86.plain]) rfl fun v hv _ => ?_
  have vs := us.of_upd hv (by decide)
  refine VG.Proof.X448.X86.wp_alu (by simp [VG.Proof.X448.X86.plain]) rfl fun w hw _ => ?_
  have ws := vs.of_upd hw (by decide)
  refine VG.Proof.X448.X86.wp_alu (by simp [VG.Proof.X448.X86.plain]) rfl fun x hx _ => ?_
  have xs := ws.of_upd hx (by decide)
  refine VG.Proof.X448.X86.store_ok xs (by simp only [VG.Impl.X448.X86.X2, slot]; omega) fun y hy => WP.block_nil ⟨?_, ?_⟩
  · rw [hy.mem, hx.mem, hw.mem, hv.mem, hu.mem, ht.mem, hx.gpr]
    change _ = s.mem.writeW _ _
    simp only [VG.Proof.X448.X86.aluVal]
    rw [hw.other .eax (by decide), hv.other .eax (by decide), hu.other .eax (by decide), ht.gpr,
      hw.gpr, hv.gpr, VG.Proof.X448.X86.aluVal, hu.gpr, ht.mem, hu.other .eax (by decide), ht.gpr,
      hv.other .ecx (by decide), hu.other .ecx (by decide), ht.other .ecx (by decide), hc]
    change s.mem.writeW _ (_ ^^^ ((_ ^^^ _) &&& VG.Proof.X448.X86.mask sw)) = _
    rw [BitVec.xor_comm (VG.Proof.X448.X86.word s.mem base (TMP + 4 * i)), (VG.Proof.X448.X86.xor_sel sw _ _).1]
  · exact ((ht.rest (by decide)).trans ((hu.rest (by decide)).trans
      ((hv.rest (by decide)).trans ((hw.rest (by decide)).trans ((hx.rest (by decide)).trans (hy.rest _))))))

theorem select_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) {sw : Bool} (hc : s.gpr .ecx = VG.Proof.X448.X86.mask sw) :
    WP isa (.block ((List.range 28).flatMap VG.Proof.X448.X86.selectStep)) s fun t =>
      (∀ i < 28, VG.Proof.X448.X86.limbs t.mem base VG.Impl.X448.X86.X2 i = if sw then VG.Proof.X448.X86.limbs s.mem base TMP i else VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X2 i) ∧
      VG.Proof.X448.X86.Outside base VG.Impl.X448.X86.X2 112 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax, .edx] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.X86.limbs t.mem base VG.Impl.X448.X86.X2 i = if sw then VG.Proof.X448.X86.limbs s.mem base TMP i else VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X2 i) ∧
    VG.Proof.X448.X86.Outside base VG.Impl.X448.X86.X2 (4 * n) s.mem t.mem ∧ VG.Proof.X448.X86.Keeps [.eax, .edx] s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (VG.Proof.X448.X86.selectStep n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.X448.X86.selectStep_ok (hs.of_keeps tk (by decide)) hn ((tk.1 _ (by decide)).trans hc))
      fun u ⟨um, uk⟩ => ?_
    have out : VG.Proof.X448.X86.Outside base (VG.Impl.X448.X86.X2 + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact VG.Proof.X448.X86.writeW_outside _ _ _ (by simp only [VG.Impl.X448.X86.X2, slot]; omega)
    refine ⟨?_, (tm.mono (by omega) (by omega)).trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (VG.Proof.X448.X86.word u.mem base (VG.Impl.X448.X86.X2 + 4 * i)).toNat = _
    rw [um, VG.Proof.X448.X86.word_write t.mem base (by simp only [VG.Impl.X448.X86.X2, slot]; omega) (by simp only [VG.Impl.X448.X86.X2, slot]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h,
        tm.word (Or.inr (by simp only [VG.Impl.X448.X86.X2, slot, TMP]; omega)) (by simp only [TMP]; omega),
        tm.word (Or.inr (by omega)) (by simp only [VG.Impl.X448.X86.X2, slot]; omega)]
      cases sw <;> rfl
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Freeze`. -/
section

/-!
# X448 on x86 (32-bit): canonical reduction

The final carry selects the unique representative below the prime, using only
a mask on secret data.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem freezeMask_ok {s : State} {c : Nat} (hc : (s.gpr .ebx).toNat = c) (hb : c < 2) :
    WP isa (.block [.mov .ecx (.imm 0), .alu .sub .ecx (.reg .ebx)]) s fun t =>
      t.gpr .ecx = VG.Proof.X448.X86.mask (decide (c = 1)) ∧ t.mem = s.mem ∧ VG.Proof.X448.X86.Keeps [.ecx] s t := by
  have he : s.gpr .ebx = BitVec.ofNat 32 c := by rw [← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hm : ∀ a < 2, (0 : BitVec 32) - BitVec.ofNat 32 a = VG.Proof.X448.X86.mask (decide (a = 1)) := by decide
  refine VG.Proof.X448.X86.wp_mov rfl fun t ht => ?_
  refine VG.Proof.X448.X86.wp_alu (by simp [VG.Proof.X448.X86.plain]) rfl fun u hu _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hu.gpr]; change t.gpr .ecx - t.gpr .ebx = _
    rw [ht.gpr, ht.other .ebx (by decide), he]; exact hm c hb
  · exact hu.mem.trans ht.mem
  · exact ((ht.rest (by decide)).trans (hu.rest (by decide)))

theorem freeze_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.Bounded s.mem base VG.Impl.X448.X86.X2) :
    WP isa (.block VG.Impl.X448.X86.freeze) s fun t =>
      VG.Proof.X448.X86.Bounded t.mem base VG.Impl.X448.X86.X2 ∧ VG.Proof.X448.X86.fe t.mem base VG.Impl.X448.X86.X2 = VG.Proof.X448.X86.fe s.mem base VG.Impl.X448.X86.X2 % Spec.X448.P ∧
      VG.Proof.X448.X86.FieldMem base VG.Impl.X448.X86.X2 s.mem t.mem ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.workRegs s t := by
  simp only [VG.Impl.X448.X86.freeze, List.append_assoc]
  change WP isa (.block (VG.Impl.X448.X86.copy TMP VG.Impl.X448.X86.X2 ++ [0, 14].flatMap (fun i =>
    [ld .eax (TMP + 4 * i), .alu .add .eax (.imm 1),
      st .eax (TMP + 4 * i)]) ++ (pass TMP TMP ++
    (([.mov .ecx (.imm 0), .alu .sub .ecx (.reg .ebx)] : List Instr) ++
      (List.range 28).flatMap VG.Proof.X448.X86.selectStep)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.freezePrep_ok hs hb) fun t ⟨tf, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.pass_ok (hs.of_keeps tk (by decide)) (by decide) (by decide) (Or.inl rfl)
    tf (fun i hi => Nat.le_of_lt (VG.Proof.X448.Radix16.freezeCoeff_bound hb i hi))) fun u ⟨uf, uc, um, uk⟩ => ?_
  have cb : VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff (VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X2)) 28 < 2 := by
    rw [VG.Proof.X448.Radix16.freeze_carry hb]; split <;> decide
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.freezeMask_ok uc cb) fun v ⟨vc, vm, vk⟩ => ?_
  have vs := ((hs.of_keeps tk (by decide)).of_keeps uk (by decide)).of_keeps vk (by decide)
  refine WP.mono (VG.Proof.X448.X86.select_ok vs vc) fun w ⟨wf, wm, wk⟩ => ?_
  have outside : VG.Proof.X448.X86.Outside base TMP 112 s.mem v.mem := by rw [vm]; exact tm.trans um
  have lf : ∀ i < 28, VG.Proof.X448.X86.limbs w.mem base VG.Impl.X448.X86.X2 i =
      if VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff (VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X2)) 28 = 1 then
        VG.Proof.X448.Radix16.digit (VG.Proof.X448.Radix16.freezeCoeff (VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X2)) i else VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X2 i := by
    intro i hi
    rw [wf i hi, outside.limbs (d := VG.Impl.X448.X86.X2) (by decide) (by decide) hi, vm, uf i hi]
    simp only [decide_eq_true_eq]
  refine ⟨?_, ?_, (FieldMem.work outside (by decide) (by decide)).trans (FieldMem.output wm),
    (tk.mono ?_).trans ((uk.mono ?_).trans ((vk.mono ?_).trans (wk.mono ?_)))⟩
  · intro i hi; rw [lf i hi]; split
    · exact VG.Proof.X448.Radix16.digit_lt _ _
    · exact hb i hi
  · change VG.Proof.X448.Radix16.valN (VG.Proof.X448.X86.limbs w.mem base VG.Impl.X448.X86.X2) 28 = _
    rw [VG.Proof.X448.Radix16.valN_congr lf]
    by_cases h : VG.Proof.X448.Radix16.carry (VG.Proof.X448.Radix16.freezeCoeff (VG.Proof.X448.X86.limbs s.mem base VG.Impl.X448.X86.X2)) 28 = 1
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

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Finish`. -/
section

/-!
# X448 on x86 (32-bit): the result and restored registers

The final multiplication, canonical reduction and encoding produce the affine
coordinate. The four callee-saved registers are then restored from the
disjoint working space.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def finishRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem finish_ok {s₀ s : State} (pre : VG.Proof.X448.X86.Pre s₀)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base)
    (hm : VG.Proof.X448.X86.Outside base 0 8192 s₀.mem s.mem)
    (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.BoundedEnv s.mem base)
    (hfar : ∀ j < 8192, 56 ≤ VG.Proof.X448.X86.ofs ((arg s₀ 0).setWidth 64) (VG.Proof.X448.X86.off base j))
    (sv : VG.Proof.X448.X86.Saved base s₀.gpr s.mem) :
    WP isa finish s fun t =>
      (∀ p ∈ VG.Proof.X448.X86.savedSlots, t.gpr p.1 = s₀.gpr p.1) ∧ VG.Proof.X448.X86.Keeps VG.Proof.X448.X86.finishRegs s t ∧
      Frame [⟨base, 8192⟩, VG.Proof.X448.X86.outR s₀] s.mem t.mem ∧
      Spec.X448.bytesAt t.mem ((arg s₀ 0).setWidth 64) 56 =
        Spec.X448.encodeUCoordinate (VG.Proof.X448.X86.E s.mem base 1 * VG.Proof.X448.X86.E s.mem base 21) := by
  refine WP.seq (WP.mono (VG.Proof.X448.X86.mul_ok hs (o := X2) (a := X2) (b := T7) (by decide) (by decide)
    (by decide) (hb 1) (hb 21)) fun u ⟨uk, ub, uv⟩ => ?_)
  have us := hs.of_keeps uk.1 (by decide)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.freeze_ok us ub) fun v ⟨vb, vv, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  have frames := (uk.2.whole (by decide)).trans (vm.whole (by decide))
  have frame0 := hm.trans frames
  have ksv := uk.1.then vk
  have hvsp : v.gpr .esp = s₀.gpr .esp := (ksv.1 _ (by decide)).trans hsp
  have hvrd : v.rd = s₀.rd := ksv.2.1.trans hr
  have hvwr : v.wr = s₀.wr := ksv.2.2.trans hwr
  refine VG.Proof.X448.X86.loadArg_ok pre hvsp hvrd hvwr (hbase ▸ frame0) (by decide : 0 < 4) fun v' hv => ?_
  have vs' := vs.of_upd hv (by decide)
  change WP isa (.block ((List.range 28).flatMap packLimb ++ restore)) v' _
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86.output_ok vs' (hv.mem ▸ vb) (by rw [hv.gpr])
    (by rw [hv.gpr]; exact pre.out_fit)
    (by intro j hj; rw [hv.wr, hvwr]; exact ⟨VG.Proof.X448.X86.outR s₀, pre.out_in,
      Offset.contains_base _ (by omega) (by omega)⟩) hfar) fun w ⟨wv, wm, wk⟩ => ?_
  have ws := vs'.of_keeps wk (by decide)
  have svv := (sv.field uk.2 (by decide)).field vm (by decide)
  have svw : VG.Proof.X448.X86.Saved base s₀.gpr w.mem := svv.of_readW fun p hp => by
    have := VG.Proof.X448.X86.savedSlots_bound p hp
    rw [← hv.mem]; exact VG.Proof.X448.X86.output_word wm (by decide) (by omega) hfar
  refine WP.mono (VG.Proof.X448.X86.restore_ok ws svw) fun t ⟨tr, tm, tk⟩ => ?_
  refine ⟨tr, (uk.1.mono ?_).trans ((vk.mono ?_).trans ((hv.rest (by decide)).trans ((wk.mono ?_).trans (tk.mono ?_)))), ?_, ?_⟩
  · intro r hr; simp only [VG.Proof.X448.X86.clob, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr; simp only [VG.Proof.X448.X86.workRegs, VG.Proof.X448.X86.clob, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr; simp only [VG.Proof.X448.X86.clob, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr; simp only [VG.Proof.X448.X86.restoreRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [tm]
    rw [hv.mem] at wm
    exact (frames.frame.mono (by simp)).trans (wm.frame.mono (by simp [VG.Proof.X448.X86.outR]))
  · rw [tm, wv, hv.mem, vv, encodeUCoordinate_eq]
    refine congrArg (VG.Proof.X25519.leBytes 56) ?_
    exact congrArg Fin.val uv

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Square`. -/
section

/-!
# X448 on x86 (32-bit): runs of squarings

The inversion reuses field multiplication in a loop with its own counter. The
field slots and memory frame compose exactly as they do for straight-line
operation lists.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

structure IKeep (base : Addr) (s t : State) : Prop where
  regs : VG.Proof.X448.X86.Keeps (.esi :: VG.Proof.X448.X86.workRegs) s t
  mem : VG.Proof.X448.X86.Outside2 base 64 2816 ACC 512 s.mem t.mem

theorem IKeep.refl (base : Addr) (s : State) : VG.Proof.X448.X86.IKeep base s s :=
  ⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩

theorem IKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.X448.X86.IKeep base s t) (h' : VG.Proof.X448.X86.IKeep base t u) :
    VG.Proof.X448.X86.IKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem IKeep.scr {base : Addr} {s t : State} (h : VG.Proof.X448.X86.IKeep base s t) (hs : VG.Proof.X448.X86.Scr s base) : VG.Proof.X448.X86.Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem Keep.ikeep {base : Addr} {s t : State} (h : VG.Proof.X448.X86.Keep base s t) : VG.Proof.X448.X86.IKeep base s t :=
  ⟨h.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr), h.mem⟩

theorem counter_keep {base : Addr} {s t : State} (hg : ∀ r, r ≠ .esi → t.gpr r = s.gpr r)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : VG.Proof.X448.X86.IKeep base s t :=
  ⟨⟨fun r h => hg r (fun he => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
    hm ▸ Outside2.refl _ _ _ _ _ _⟩

def ISpec (base : Addr) (code : Prog isa) (f : VG.Proof.X448.X86.Env → VG.Proof.X448.X86.Env) : Prop :=
  ∀ s, VG.Proof.X448.X86.Scr s base → VG.Proof.X448.X86.BoundedEnv s.mem base → WP isa code s fun t =>
    VG.Proof.X448.X86.IKeep base s t ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = f (VG.Proof.X448.X86.E s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : VG.Proof.X448.X86.Env → VG.Proof.X448.X86.Env}
    (h₁ : VG.Proof.X448.X86.ISpec base c₁ f) (h₂ : VG.Proof.X448.X86.ISpec base c₂ g) :
    VG.Proof.X448.X86.ISpec base (.seq c₁ c₂) (fun e => g (f e)) := fun s hs hb =>
  WP.seq (WP.mono (h₁ s hs hb) fun t ⟨tk, tb, te⟩ =>
    WP.mono (h₂ t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, by rw [ue, te]⟩)

theorem opsI (base : Addr) (xs : List VG.Proof.X448.X86.FieldOp) :
    VG.Proof.X448.X86.ISpec base (VG.Impl.X448.X86.ops (xs.map FieldOp.impl)) (VG.Proof.X448.X86.applyOps xs) := fun _ hs hb =>
  WP.mono (VG.Proof.X448.X86.ops_ok hs hb xs) fun _ ⟨tk, tb, te⟩ => ⟨tk.ikeep, tb, te⟩

def opSqn (o : VG.Proof.X448.X86.Index) (n : Nat) (e : VG.Proof.X448.X86.Env) : VG.Proof.X448.X86.Env := Function.update e o (Proof.X448.sqn (e o) n)

theorem opMul_update (o : VG.Proof.X448.X86.Index) (e : VG.Proof.X448.X86.Env) (v : Spec.X448.Fe) :
    VG.Proof.X448.X86.opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [VG.Proof.X448.X86.opMul, Function.update_self, Function.update_idem]

theorem sqnI (base : Addr) (o : VG.Proof.X448.X86.Index) {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 16) :
    VG.Proof.X448.X86.ISpec base (Impl.X448.X86.sqn (slot o.val) n) (VG.Proof.X448.X86.opSqn o n) := by
  intro s hs hb
  rw [Impl.X448.X86.sqn, WP.seq_iff]
  refine WP.mono (VG.Proof.X448.X86.setCounter_ok s n hn') fun t ⟨tc, tg, tm, tr, tw⟩ => ?_
  have kt : VG.Proof.X448.X86.IKeep base s t := VG.Proof.X448.X86.counter_keep tg tm tr tw
  let inv := fun m (u : State) => 1 ≤ m ∧ m ≤ n ∧ VG.Proof.X448.X86.IKeep base s u ∧ VG.Proof.X448.X86.BoundedEnv u.mem base ∧
    u.gpr .esi = BitVec.ofNat 32 m ∧
    VG.Proof.X448.X86.E u.mem base = Function.update (VG.Proof.X448.X86.E s.mem base) o (Proof.X448.sqn (VG.Proof.X448.X86.E s.mem base o) (n - m))
  refine WP.loop (M := isa) inv ?_ n t ?_
  · intro m u ⟨hm, hm', ku, bu, cu, eu⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [WP.seq_iff]
    refine WP.mono (VG.Proof.X448.X86.mulE (ku.scr hs) bu o o o) fun v ⟨kv, bv, ev⟩ => ?_
    have cv : v.gpr .esi = BitVec.ofNat 32 (m + 1) := (kv.regs.1 _ (by decide)).trans cu
    refine WP.mono (VG.Proof.X448.X86.decCounter_ok (by omega) cv) fun w ⟨cw, wg, wm, wr, ww, wz⟩ => ?_
    have kw : VG.Proof.X448.X86.IKeep base s w := ku.trans (kv.ikeep.trans (VG.Proof.X448.X86.counter_keep wg wm wr ww))
    have bw : VG.Proof.X448.X86.BoundedEnv w.mem base := wm ▸ bv
    have ew : VG.Proof.X448.X86.E w.mem base = Function.update (VG.Proof.X448.X86.E s.mem base) o (Proof.X448.sqn (VG.Proof.X448.X86.E s.mem base o) (n - m)) := by
      rw [wm, ev, eu, VG.Proof.X448.X86.opMul_update, ← Proof.X448.sqn]
      rw [show (n - (m + 1)).succ = n - m by omega]
    simp only [eval, wz, Option.map_some]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl ⟨rfl, kw, bw, ew⟩
    · refine Or.inr ⟨?_, m, by omega, hm, by omega, kw, bw, cw, ew⟩
      rw [decide_eq_false (by omega : ¬m = 0)]; rfl
  · refine ⟨hn, by omega, kt, tm ▸ hb, tc, ?_⟩
    rw [tm, Nat.sub_self, Proof.X448.sqn, Function.update_eq_self]

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Inv`. -/
section

/-!
# X448 on x86 (32-bit): inversion

The addition chain updates slots 14–21 and leaves the ladder's coordinates
available for the final multiplication and encoding.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- The field slots after the inversion's addition chain. -/
def invEnv (e : VG.Proof.X448.X86.Env) : VG.Proof.X448.X86.Env :=
  let e := VG.Proof.X448.X86.applyOps [.copy 14 2] e
  let e := VG.Proof.X448.X86.opSqn 14 1 e
  let e := VG.Proof.X448.X86.applyOps [.mul 14 14 2, .copy 15 14] e
  let e := VG.Proof.X448.X86.opSqn 15 2 e
  let e := VG.Proof.X448.X86.applyOps [.mul 15 15 14, .copy 16 15] e
  let e := VG.Proof.X448.X86.opSqn 16 4 e
  let e := VG.Proof.X448.X86.applyOps [.mul 16 16 15, .copy 17 16] e
  let e := VG.Proof.X448.X86.opSqn 17 8 e
  let e := VG.Proof.X448.X86.applyOps [.mul 17 17 16, .copy 18 17] e
  let e := VG.Proof.X448.X86.opSqn 18 16 e
  let e := VG.Proof.X448.X86.applyOps [.mul 18 18 17, .copy 19 18] e
  let e := VG.Proof.X448.X86.opSqn 19 32 e
  let e := VG.Proof.X448.X86.applyOps [.mul 19 19 18, .copy 20 19] e
  let e := VG.Proof.X448.X86.opSqn 20 64 e
  let e := VG.Proof.X448.X86.applyOps [.mul 20 20 19] e
  let e := VG.Proof.X448.X86.opSqn 20 64 e
  let e := VG.Proof.X448.X86.applyOps [.mul 20 20 19] e
  let e := VG.Proof.X448.X86.opSqn 20 16 e
  let e := VG.Proof.X448.X86.applyOps [.mul 20 20 17] e
  let e := VG.Proof.X448.X86.opSqn 20 8 e
  let e := VG.Proof.X448.X86.applyOps [.mul 20 20 16] e
  let e := VG.Proof.X448.X86.opSqn 20 4 e
  let e := VG.Proof.X448.X86.applyOps [.mul 20 20 15] e
  let e := VG.Proof.X448.X86.opSqn 20 2 e
  let e := VG.Proof.X448.X86.applyOps [.mul 20 20 14, .copy 21 20] e
  let e := VG.Proof.X448.X86.opSqn 21 1 e
  let e := VG.Proof.X448.X86.applyOps [.mul 21 21 2] e
  let e := VG.Proof.X448.X86.opSqn 21 225 e
  let e := VG.Proof.X448.X86.opSqn 20 2 e
  VG.Proof.X448.X86.applyOps [.mul 20 20 2, .mul 21 21 20] e

theorem invert_spec (base : Addr) : VG.Proof.X448.X86.ISpec base Impl.X448.X86.invert VG.Proof.X448.X86.invEnv := by
  have h : VG.Proof.X448.X86.ISpec base _ _ :=
    (VG.Proof.X448.X86.opsI base [.copy 14 2]).seq <|
    (VG.Proof.X448.X86.sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 14 14 2, .copy 15 14]).seq <|
    (VG.Proof.X448.X86.sqnI base 15 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 15 15 14, .copy 16 15]).seq <|
    (VG.Proof.X448.X86.sqnI base 16 (n := 4) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 16 16 15, .copy 17 16]).seq <|
    (VG.Proof.X448.X86.sqnI base 17 (n := 8) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 17 17 16, .copy 18 17]).seq <|
    (VG.Proof.X448.X86.sqnI base 18 (n := 16) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 18 18 17, .copy 19 18]).seq <|
    (VG.Proof.X448.X86.sqnI base 19 (n := 32) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 19 19 18, .copy 20 19]).seq <|
    (VG.Proof.X448.X86.sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 20 20 19]).seq <|
    (VG.Proof.X448.X86.sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 20 20 19]).seq <|
    (VG.Proof.X448.X86.sqnI base 20 (n := 16) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 20 20 17]).seq <|
    (VG.Proof.X448.X86.sqnI base 20 (n := 8) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 20 20 16]).seq <|
    (VG.Proof.X448.X86.sqnI base 20 (n := 4) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 20 20 15]).seq <|
    (VG.Proof.X448.X86.sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 20 20 14, .copy 21 20]).seq <|
    (VG.Proof.X448.X86.sqnI base 21 (n := 1) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 21 21 2]).seq <|
    (VG.Proof.X448.X86.sqnI base 21 (n := 225) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86.opsI base [.mul 20 20 2, .mul 21 21 20])
  exact h

theorem invEnv_eval (e : VG.Proof.X448.X86.Env) : VG.Proof.X448.X86.invEnv e 21 = Proof.X448.invert (e 2) := by
  simp only [↓reduceIte, VG.Proof.X448.X86.invEnv, VG.Proof.X448.X86.applyOps, FieldOp.apply, VG.Proof.X448.X86.opMul, VG.Proof.X448.X86.opCopy, VG.Proof.X448.X86.opSqn,
    Function.update_apply]
  rfl

theorem invEnv_x2 (e : VG.Proof.X448.X86.Env) : VG.Proof.X448.X86.invEnv e 1 = e 1 := by
  simp (config := {decide := true}) only [VG.Proof.X448.X86.invEnv, VG.Proof.X448.X86.applyOps, FieldOp.apply, VG.Proof.X448.X86.opMul, VG.Proof.X448.X86.opCopy, VG.Proof.X448.X86.opSqn,
    Function.update_apply, ite_true, ite_false]

theorem invert_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86.Scr s base) (hb : VG.Proof.X448.X86.BoundedEnv s.mem base) :
    WP isa Impl.X448.X86.invert s fun t =>
      VG.Proof.X448.X86.IKeep base s t ∧ VG.Proof.X448.X86.BoundedEnv t.mem base ∧ VG.Proof.X448.X86.E t.mem base = VG.Proof.X448.X86.invEnv (VG.Proof.X448.X86.E s.mem base) :=
  VG.Proof.X448.X86.invert_spec base s hs hb

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Ladder`. -/
section

/-!
# X448 on x86 (32-bit): all 448 ladder iterations

A decreasing public counter connects the loop to the specification's
descending fold over scalar bits.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 448 → VG.Proof.X448.X86.LInv base k u s₀ s n →
      WP isa (.loop VG.Impl.X448.X86.step .ne) s fun s' => VG.Proof.X448.X86.LInv base k u s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := VG.Impl.X448.X86.step) (c := .ne)
    (Q := fun s' => VG.Proof.X448.X86.LInv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 448 ∧ VG.Proof.X448.X86.LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.X448.X86.step_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

/-- The ladder: the counter set to 448, then the loop. -/
theorem ladder_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (VG.Proof.X448.X86.off base (VG.Impl.X448.X86.BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : ∀ s', s'.gpr .esi = BitVec.ofNat 32 448 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VG.Proof.X448.X86.LInv base k u s₀ s' 448) :
    WP isa VG.Impl.X448.X86.ladder s fun s' => VG.Proof.X448.X86.LInv base k u s₀ s' 0 := by
  refine WP.seq (WP.mono (VG.Proof.X448.X86.setCounter_ok s 448 (by decide))
    fun s' ⟨h1, h2, h3, h4, h5⟩ => VG.Proof.X448.X86.loop_ok hbits 448 s' (by omega) (by omega) (hi s' h1 h2 h3 h4 h5))

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Main`. -/
section

/-!
# X448 on x86 (32-bit): the whole function

The contract the proof is written against (the facts of `Spec.X448.x448Contract`
it uses, stated for x86 (32-bit)), and the correctness of `vg_x448` against it:
every write is in the working space but the result's, so the arguments are read
unchanged, the callee-saved registers restored from the working space, and the
return address kept.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ VG.Proof.X448.X86.ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [VG.Proof.X448.X86.ofs] at h; omega

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : VG.Proof.X448.X86.Outside base 0 8192 m m')
    (hp : ∀ i < 56, 8192 ≤ VG.Proof.X448.X86.ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X448.bytesAt m' p 56 = Spec.X448.bytesAt m p 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem far_output {base p : Addr} (hd : (⟨p, 56⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 56 ≤ VG.Proof.X448.X86.ofs p (VG.Proof.X448.X86.off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change VG.Proof.X448.X86.ofs p (VG.Proof.X448.X86.off base i) + 1 ≤ 56
  omega

theorem E_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.X86.Outside base o n m m') (i : VG.Proof.X448.X86.Index)
    (hi : slot i.val + 112 ≤ o ∨ o + n ≤ slot i.val) : VG.Proof.X448.X86.E m' base i = VG.Proof.X448.X86.E m base i := by
  simp only [VG.Proof.X448.X86.E, VG.Proof.X448.X86.F]
  rw [h.fe hi (by have := i.isLt; simp only [slot]; omega)]

theorem correct {s₀ : State} (hp : VG.Proof.X448.X86.Pre s₀) :
    WP isa x448 s₀ fun s' => abiPreserved s₀ s' ∧ Proof.X448.x448X86.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, (arg s₀ 3).setWidth 64 = b := ⟨_, rfl⟩
  have hr : ∀ j < 56, InRegions (s₀.rd ++ s₀.wr) (VG.Proof.X448.X86.off ((arg s₀ 2).setWidth 64) j) 1 := fun j hj =>
    ⟨VG.Proof.X448.X86.pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hd : ∀ j < 56, 8192 ≤ VG.Proof.X448.X86.ofs base (VG.Proof.X448.X86.off ((arg s₀ 2).setWidth 64) j) :=
    fun j hj => VG.Proof.X448.X86.far (hbase ▸ hp.point_sc) hj (by decide)
  have kd : ∀ j < 56, 8192 ≤ VG.Proof.X448.X86.ofs base (VG.Proof.X448.X86.off ((arg s₀ 1).setWidth 64) j) :=
    fun j hj => VG.Proof.X448.X86.far (hbase ▸ hp.scalar_sc) hj (by decide)
  rw [x448]
  refine WP.seq (WP.mono (VG.Proof.X448.X86.setup_ok hp hbase rfl hr hd)
    fun s₁ ⟨hs₁, b₁, k₁, o₁, sv₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.X86.bits_ok hp (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 hbase o₁ hs₁ kd)
    fun s₂ ⟨k₂, o₂, bits₂⟩ => ?_)
  have k02 := k₁.then k₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have sv₂ : VG.Proof.X448.X86.Saved base s₀.gpr s₂.mem := by exact sv₁.outside o₂ (by decide)
  have e₂ : ∀ i : VG.Proof.X448.X86.Index, VG.Proof.X448.X86.E s₂.mem base i = VG.Proof.X448.X86.E s₁.mem base i := by
    intro i; exact VG.Proof.X448.X86.E_outside o₂ i (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
  have b₂ : VG.Proof.X448.X86.BoundedEnv s₂.mem base := by
    intro i j hj
    rw [o₂.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) hj]
    exact b₁ i j hj
  have kb := VG.Proof.X448.X86.bytesAt_outside o₁ kd
  refine WP.seq (WP.mono (VG.Proof.X448.X86.ladder_ok (s₀ := s₂) (s := s₂)
    (k := Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 56))
    (u := toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 56)))
    (fun t ht => by rw [bits₂ t ht, kb])
    (fun s' hb hg hm hr hw => ⟨
      ⟨by rw [hg _ (by decide)]; exact hs₂.edi, hw ▸ hs₂.wr,
        by rw [hg _ (by decide)]; exact hs₂.nowrap⟩, hm ▸ b₂,
      ⟨fun r h => hg r (fun e => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
      hb, hm ▸ Outside2.refl _ _ _ _ _ _,
      by rw [hm, e₂ 0, x1₁], by rw [hm, e₂ 1, x2₁]; rfl,
      by rw [hm, e₂ 2, z2₁]; rfl, by rw [hm, e₂ 3, x3₁, x1₁]; rfl,
      by rw [hm, e₂ 4, z3₁]; rfl,
      by rw [hm, o₂.word (d := SWAP) (by decide) (by decide), sw₁]; rfl⟩)) fun s₄ L => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.X86.lastSwap_ok L.scr L.bounded
    (by have := ladderAfter_swap_le
          (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 56))
          (toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 56)))
          (n := 0) (by decide); omega) L.swap) fun s₅ ⟨k₅, b₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr L.scr
  refine WP.seq (WP.mono (VG.Proof.X448.X86.invert_ok hs₅ b₅) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  have k26 := L.regs.then (k₅.regs.then k₆.regs)
  have sv₆ := ((sv₂.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have k06 := k02.then k26
  have o₆ := ((o₁.trans (o₂.mono (by decide) (by decide))).trans
    (L.mem.whole (by decide) (by decide))).trans
    ((k₅.mem.whole (by decide) (by decide)).trans (k₆.mem.whole (by decide) (by decide)))
  refine WP.mono (VG.Proof.X448.X86.finish_ok hp (k06.1 _ (by decide)) k06.2.1 k06.2.2 hbase o₆ (k₆.scr hs₅) b₆
    (fun j hj => VG.Proof.X448.X86.far_output (hbase ▸ hp.out_sc) hj) sv₆) fun s' ⟨restored, kf, fm, result⟩ => ?_
  have kall := k06.then kf
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact restored (.ebx, 0) (by decide)
      · exact restored (.esi, 4) (by decide)
      · exact restored (.edi, 8) (by decide)
      · exact restored (.ebp, 12) (by decide)
      · exact kall.1 _ (by decide)
    · have frame : Frame [VG.Proof.X448.X86.scR (arg s₀ 3), VG.Proof.X448.X86.outR s₀] s₀.mem s'.mem := by
        rw [← hbase] at fm o₆
        exact (o₆.frame.mono (by simp)).trans fm
      have ret : (VG.Proof.X448.X86.retR s₀).Contains ((s₀.gpr .esp).setWidth 64) 4 := by
        simpa only [BitVec.add_zero] using
          Offset.contains_base ((s₀.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
      exact frame.readW ret
        (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl; exact hp.ret_sc; exact hp.ret_out) (by decide)

  · change Spec.X448.bytesAt s'.mem ((arg s₀ 0).setWidth 64) 56 = _
    rw [result, x448_eq]
    apply congrArg Spec.X448.encodeUCoordinate
    rw [e₆, VG.Proof.X448.X86.invEnv_x2, VG.Proof.X448.X86.invEnv_eval, e₅]
    simp (config := {decide := true}) only [VG.Proof.X448.X86.opSwap, Function.update_apply, ite_true, ite_false]
    rw [L.x2, L.x3, L.z2, L.z3, VG.Proof.X448.X86.cswap_fst, VG.Proof.X448.X86.cswap_fst]

end VG.Proof.X448.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86.Verified`. -/
section

/-!
# X448 on x86 (32-bit): `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is a pointer plus a constant or the counter),
satisfiability, and the shared contract of `Spec/`.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [56, 8192], argLen := 20, argBases := [(4, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : VG.Proof.X448.X86.Pre s) : VG.X86.Taint.Wf VG.Proof.X448.X86.τ₀ s := by
  have hsc := hp.sc_fit; have ho := hp.out_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.X448.X86.τ₀], by simpa [hp.wr] using hp.out_sc, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hsc, ho]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [VG.Proof.X448.X86.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.X448.x448X86.pre s₁) (h₂ : Proof.X448.x448X86.pre s₂)
    (hpub : Proof.X448.x448X86.pub s₁ s₂) : VG.X86.Taint.Agree VG.Proof.X448.X86.τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := Pre.of _ h₁; have hp₂ := Pre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.X448.X86.wf₀ hp₁, VG.Proof.X448.X86.wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.X448.X86.τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.X448.X86.outR, a0, a3]
  · simp only [VG.Proof.X448.X86.τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.sp_fit h4 hk, VG.X86.Taint.argByte_eq hp₂.sp_fit h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega_using [hk]
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem x448_ct : ConstantTime isa Proof.X448.x448X86.pre Proof.X448.x448X86.pub
    Impl.X448.X86.x448 :=
  VG.Taint.constantTime (A := taint) VG.Proof.X448.X86.τ₀ (fun _ _ h₁ h₂ hp => VG.Proof.X448.X86.agree₀ h₁ h₂ hp) (by taint_decide)

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x4000` at `0x8004`. -/
def satMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30 else
  if a = 0x8011 then 0x40 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.X448.X86.satMem
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_ok (s : State) (hs : Proof.X448.x448X86.pre s) :
    ∃ t s', Exec isa Impl.X448.X86.x448 s t s' ∧ abiPreserved s s' ∧ Proof.X448.x448X86.post s s' :=
  VG.Proof.X448.X86.correct (Pre.of s hs)

theorem x448_verified :
    Verified X86.target Impl.X448.X86.x448 (Spec.X448.x448Contract X86.abi) :=
  Verified.of_correct VG.Proof.X448.X86.x448_ok VG.Proof.X448.X86.x448_ct (by
    have a0 : arg VG.Proof.X448.X86.satState 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.X448.X86.satState 1 = 0x2000 := by decide
    have a2 : arg VG.Proof.X448.X86.satState 2 = 0x3000 := by decide
    have a3 : arg VG.Proof.X448.X86.satState 3 = 0x4000 := by decide
    have e : argAddr VG.Proof.X448.X86.satState 0 = 0x8004 := by decide
    have esp : satState.gpr .esp = 0x8000 := rfl
    sig_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, Proof.X448.x448X86, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, e, esp] using Proof.X448.X86.satState)

end VG.Proof.X448.X86

end
