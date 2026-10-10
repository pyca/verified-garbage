import VerifiedGarbage.Proof.X25519.X86_64.Small
import VerifiedGarbage.Proof.X25519.X86_64.Sqr
import Mathlib.Logic.Function.Basic

/-!
# X25519 on x86-64: the working space as slots

The working space as 128 slots of 32 bytes (`E`), each read as a field
element: each field operation updates one slot (`Function.update`) and the
swap two, so that a sequence of operations is a chain of updates that `simp`
evaluates at any slot. The ladder's variables and temporaries are in the slots
2–19 (bytes 64–639), so the field operations change no byte outside `[64,
640)`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The working space as 128 field elements. -/
def E (m : Mem) (base : Addr) (i : Fin 128) : Spec.X25519.Fe := F m base (32 * i.val)

theorem Outside.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : Outside base o n m m')
    (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n') : Outside base o' n' m m' :=
  fun x hx => h x (by omega)

theorem E_update {base : Addr} {m m' : Mem} {o : Fin 128}
    (h : Outside base (32 * o.val) 32 m m') :
    E m' base = Function.update (E m base) o (F m' base (32 * o.val)) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp [E]
  · rw [Function.update_of_ne hi]
    simp only [E, F]
    have : i.val ≠ o.val := fun h' => hi (Fin.ext h')
    rw [h.fe (by omega) (by omega)]

/-- What the field operations keep: the registers but `clob`, the regions,
and the memory outside `[64, 640)`. -/
structure Keep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base 64 576 s.mem s'.mem

theorem Keep.refl (base : Addr) (s : State) : Keep base s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem Keep.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : Keep base s₁ s₂) (h₂ : Keep base s₂ s₃) :
    Keep base s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.mem.trans h₂.mem⟩

theorem Keep.scr {base : Addr} {s s' : State} (h : Keep base s s') (hs : Scr s base) : Scr s' base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Op.keep {base : Addr} {o : Nat} {s s' : State} (h : Op base o s s') (h₁ : 64 ≤ o)
    (h₂ : o + 32 ≤ 640) : Keep base s s' :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono h₁ (by omega)⟩

/-! ## The field multiplications -/

/-- What the rest of the proof needs of the field multiplications `fld`:
each writes the field element at `o` and nothing else of the working space,
and changes only the registers `clob` (`Op`). -/
structure FieldOk (fld : Field) : Prop where
  mul : ∀ {s : State} {base : Addr}, Scr s base → ∀ {o a b : Nat}, Slot o → Slot a → Slot b →
    WP isa (.block (fld.mul o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b
  sqr : ∀ {s : State} {base : Addr}, Scr s base → ∀ {o a : Nat}, Slot o → Slot a →
    WP isa (.block (fld.sqr o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a
  a24 : ∀ {s : State} {base : Addr}, Scr s base → ∀ {o a : Nat}, Slot o → Slot a →
    WP isa (.block (fld.a24 o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = Spec.X25519.a24 * F s.mem base a
  mul2 : ∀ {s : State} {base : Addr}, Scr s base → ∀ {o a b : Nat}, Slot o → Slot a → Slot b →
    WP isa (.block (fld.mul2 o a b)) s fun s' => Op base o s s' ∧
      F s'.mem base o = F s.mem base a * F s.mem base b + F s.mem base a * F s.mem base b
  sqr2 : ∀ {s : State} {base : Addr}, Scr s base → ∀ {o a : Nat}, Slot o → Slot a →
    WP isa (.block (fld.sqr2 o a)) s fun s' => Op base o s s' ∧
      F s'.mem base o = F s.mem base a * F s.mem base a + F s.mem base a * F s.mem base a
  /-- `mul`, whose product is at most `2p` (for the ladder's sums, `addCmov`). -/
  mulB : ∀ {s : State} {base : Addr}, Scr s base → ∀ {o a b : Nat}, Slot o → Slot a → Slot b →
    WP isa (.block (fld.mul o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b ∧
        fe s'.mem base o ≤ 2 * Spec.X25519.P
  /-- `sqr`, whose square is at most `2p`. -/
  sqrB : ∀ {s : State} {base : Addr}, Scr s base → ∀ {o a : Nat}, Slot o → Slot a →
    WP isa (.block (fld.sqr o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a ∧
        fe s'.mem base o ≤ 2 * Spec.X25519.P

theorem Op.trans {base : Addr} {o : Nat} {s t u : State} (h : Op base o s t) (k : Op base o t u) :
    Op base o s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, h.mem.trans k.mem⟩

/-- A field operation into `[o]`, then `[o] = [o] + [o]`. -/
theorem dbl_after {code : List Instr} {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (ho : Slot o) {v : Spec.X25519.Fe}
    (h : WP isa (.block code) s fun s' => Op base o s s' ∧ F s'.mem base o = v) :
    WP isa (.block (code ++ add o o o)) s fun s' => Op base o s s' ∧ F s'.mem base o = v + v := by
  rw [WP.block_append_iff]
  refine WP.mono h fun t ⟨ht, et⟩ => ?_
  refine WP.mono (add_ok (ht.scr hs) ho ho ho) fun u ⟨hu, eu⟩ => ⟨ht.trans hu, ?_⟩
  rw [eu, et]

theorem baseline_ok : FieldOk baseline where
  mul hs _ _ _ ho ha hb := mul_ok hs ho ha hb
  sqr hs _ _ ho ha := sqr_ok hs ho ha
  a24 hs _ _ ho ha := mulA24_ok hs ho ha
  mul2 hs _ _ _ ho ha hb := dbl_after hs ho (mul_ok hs ho ha hb)
  sqr2 hs _ _ ho ha := dbl_after hs ho (sqr_ok hs ho ha)
  mulB hs _ _ _ ho ha hb := mulBnd_ok hs ho ha hb
  sqrB hs _ _ ho ha := sqrBnd_ok hs ho ha

/-! ## The field operations on the slots -/

variable {fld : Field} (hf : FieldOk fld)

/-- Environments: the working space's slots. -/
abbrev Env := Fin 128 → Spec.X25519.Fe

def opMul (o a b : Fin 128) (e : Env) : Env := Function.update e o (e a * e b)
def opAdd (o a b : Fin 128) (e : Env) : Env := Function.update e o (e a + e b)
def opSub (o a b : Fin 128) (e : Env) : Env := Function.update e o (e a - e b)
def opA24 (o a : Fin 128) (e : Env) : Env := Function.update e o (Spec.X25519.a24 * e a)
def opSwap (x y : Fin 128) (sw : Bool) (e : Env) : Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

/-- A slot of the ladder's: 2 to 19. -/
abbrev LSlot (o : Fin 128) : Prop := 2 ≤ o.val ∧ o.val < 20

include hf in
theorem mulE {s : State} {base : Addr} (hs : Scr s base) (o a b : Fin 128) (ho : LSlot o) :
    WP isa (.block (fld.mul (32 * o.val) (32 * a.val) (32 * b.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opMul o a b (E s.mem base) :=
  WP.mono (hf.mul hs (by omega) (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [E_update h.mem, e]; rfl⟩

include hf in
theorem sqrE {s : State} {base : Addr} (hs : Scr s base) (o a : Fin 128) (ho : LSlot o) :
    WP isa (.block (fld.sqr (32 * o.val) (32 * a.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opMul o a a (E s.mem base) :=
  WP.mono (hf.sqr hs (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [E_update h.mem, e]; rfl⟩

theorem addE {s : State} {base : Addr} (hs : Scr s base) (o a b : Fin 128) (ho : LSlot o) :
    WP isa (.block (add (32 * o.val) (32 * a.val) (32 * b.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opAdd o a b (E s.mem base) :=
  WP.mono (add_ok hs (by omega) (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [E_update h.mem, e]; rfl⟩

theorem subE {s : State} {base : Addr} (hs : Scr s base) (o a b : Fin 128) (ho : LSlot o) :
    WP isa (.block (sub (32 * o.val) (32 * a.val) (32 * b.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opSub o a b (E s.mem base) :=
  WP.mono (sub_ok hs (by omega) (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [E_update h.mem, e]; rfl⟩

include hf in
theorem a24E {s : State} {base : Addr} (hs : Scr s base) (o a : Fin 128) (ho : LSlot o) :
    WP isa (.block (fld.a24 (32 * o.val) (32 * a.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opA24 o a (E s.mem base) :=
  WP.mono (hf.a24 hs (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [E_update h.mem, e]; rfl⟩

theorem cswapE {s : State} {base : Addr} (hs : Scr s base) (x y : Fin 128) (hx : LSlot x)
    (hy : LSlot y) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (cswap (32 * x.val) (32 * y.val))) s fun s' =>
      Keep base s s' ∧ s'.gpr .rcx = s.gpr .rcx ∧ E s'.mem base = opSwap x y sw (E s.mem base) := by
  have hne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  refine WP.mono (cswap_ok hs (by omega) (by omega) (by omega) hm)
    fun s' ⟨g, gc, rd, wr, ⟨m₁, o₁, o₂, f₁⟩, fx, fy⟩ => ?_
  refine ⟨⟨g, rd, wr, (o₁.mono (by omega) (by omega)).trans (o₂.mono (by omega) (by omega))⟩, gc, ?_⟩
  rw [E_update o₂, E_update o₁]
  simp only [F, f₁, fy]
  cases sw <;> rfl


/-! ## The ladder's operations, with the bytes they write

What the ladder's iteration needs to carry bounds of `2p` past later operations
(`Iter.lean`): each operation changes only the 32 bytes of its result. -/

include hf in
theorem mulEB {s : State} {base : Addr} (hs : Scr s base) (o a b : Fin 128) (ho : LSlot o) :
    WP isa (.block (fld.mul (32 * o.val) (32 * a.val) (32 * b.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opMul o a b (E s.mem base) ∧
        Outside base (32 * o.val) 32 s.mem s'.mem ∧ fe s'.mem base (32 * o.val) ≤ 2 * Spec.X25519.P :=
  WP.mono (hf.mulB hs (by omega) (by omega) (by omega)) fun _ ⟨h, e, hb⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [E_update h.mem, e]; rfl, h.mem, hb⟩

include hf in
theorem sqrEB {s : State} {base : Addr} (hs : Scr s base) (o a : Fin 128) (ho : LSlot o) :
    WP isa (.block (fld.sqr (32 * o.val) (32 * a.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opMul o a a (E s.mem base) ∧
        Outside base (32 * o.val) 32 s.mem s'.mem ∧ fe s'.mem base (32 * o.val) ≤ 2 * Spec.X25519.P :=
  WP.mono (hf.sqrB hs (by omega) (by omega)) fun _ ⟨h, e, hb⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [E_update h.mem, e]; rfl, h.mem, hb⟩

theorem addCmovE {s : State} {base : Addr} (hs : Scr s base) (o a b : Fin 128) (ho : LSlot o)
    (hab : fe s.mem base (32 * a.val) ≤ 2 * Spec.X25519.P ∨
      fe s.mem base (32 * b.val) ≤ 2 * Spec.X25519.P) :
    WP isa (.block (addCmov (32 * o.val) (32 * a.val) (32 * b.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opAdd o a b (E s.mem base) ∧
        Outside base (32 * o.val) 32 s.mem s'.mem :=
  WP.mono (addCmov_ok hs (by omega) (by omega) (by omega) hab) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [E_update h.mem, e]; rfl, h.mem⟩

theorem subCmovE {s : State} {base : Addr} (hs : Scr s base) (o a b : Fin 128) (ho : LSlot o)
    (hb2 : fe s.mem base (32 * b.val) ≤ 2 * Spec.X25519.P) :
    WP isa (.block (subCmov (32 * o.val) (32 * a.val) (32 * b.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opSub o a b (E s.mem base) ∧
        Outside base (32 * o.val) 32 s.mem s'.mem :=
  WP.mono (subCmov_ok hs (by omega) (by omega) (by omega) hb2) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [E_update h.mem, e]; rfl, h.mem⟩

include hf in
theorem a24EB {s : State} {base : Addr} (hs : Scr s base) (o a : Fin 128) (ho : LSlot o) :
    WP isa (.block (fld.a24 (32 * o.val) (32 * a.val))) s fun s' =>
      Keep base s s' ∧ E s'.mem base = opA24 o a (E s.mem base) ∧
        Outside base (32 * o.val) 32 s.mem s'.mem :=
  WP.mono (hf.a24 hs (by omega) (by omega)) fun _ ⟨h, e⟩ =>
    ⟨h.keep (by omega) (by omega), by rw [E_update h.mem, e]; rfl, h.mem⟩

theorem cswapEB {s : State} {base : Addr} (hs : Scr s base) (x y : Fin 128) (hx : LSlot x)
    (hy : LSlot y) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (cswap (32 * x.val) (32 * y.val))) s fun s' =>
      Keep base s s' ∧ s'.gpr .rcx = s.gpr .rcx ∧ E s'.mem base = opSwap x y sw (E s.mem base) ∧
        (∀ d, d + 32 ≤ 4096 → (d + 32 ≤ 32 * x.val ∨ 32 * x.val + 32 ≤ d) →
          (d + 32 ≤ 32 * y.val ∨ 32 * y.val + 32 ≤ d) → fe s'.mem base d = fe s.mem base d) ∧
        fe s'.mem base (32 * x.val) =
          (if sw then fe s.mem base (32 * y.val) else fe s.mem base (32 * x.val)) ∧
        fe s'.mem base (32 * y.val) =
          (if sw then fe s.mem base (32 * x.val) else fe s.mem base (32 * y.val)) := by
  have hne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  refine WP.mono (cswap_ok hs (by omega) (by omega) (by omega) hm)
    fun s' ⟨g, gc, rd, wr, ⟨m₁, o₁, o₂, f₁⟩, fx, fy⟩ => ?_
  refine ⟨⟨g, rd, wr, (o₁.mono (by omega) (by omega)).trans (o₂.mono (by omega) (by omega))⟩, gc, ?_,
    fun d hd h1 h2 => by rw [o₂.fe h2 (by omega), o₁.fe h1 (by omega)], fx, fy⟩
  rw [E_update o₂, E_update o₁]
  simp only [F, f₁, fy]
  cases sw <;> rfl

end VG.Proof.X25519.X86_64
