import VerifiedGarbage.Impl.X448.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.X448.Encoding
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Range
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Basic`. -/
section

/-!
# X448 on x86-64: the working space and words

The working space is 8 KiB at `base`, which `rdi` holds (`Scr`). Numbers of
several words are read from registers (`rv`, lowest first) or from memory
(`mv`, at consecutive offsets of the working space); a field element is the
seven words at an offset (`fe`). `Keeps rs` says that a block changed only
the registers `rs` (and the flags), and `Stable X s src v` that the source
operand `src` reads `v` in every state that agrees with `s` but on the
registers `X`. `Outside base o n` says that memory changed only in the bytes
`[o, o + n)` of the working space.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-- The registers of `s'` are those of `s` but for `rs`, and memory and the
regions are unchanged. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.refl (rs : List Reg) (s : State) : VG.Proof.X448.X86_64.Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X448.X86_64.Keeps rs s₁ s₂) (h₂ : VG.Proof.X448.X86_64.Keeps rs s₂ s₃) :
    VG.Proof.X448.X86_64.Keeps rs s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : VG.Proof.X448.X86_64.Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.X448.X86_64.Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

/-- The working space: `rdi` holds its base `base`, it is writable and it
does not wrap around. -/
structure Scr (s : State) (base : Addr) : Prop where
  rdi : s.gpr .rdi = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 8192 ≤ 2 ^ 64

/-- The word at `base + d`. -/
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (VG.Proof.X448.X86_64.off base d) 64

/-- The value of the registers `rs`, lowest first. -/
def rv (s : State) : List Reg → Nat
  | [] => 0
  | r :: rs => (s.gpr r).toNat + 2 ^ 64 * VG.Proof.X448.X86_64.rv s rs

/-- The value of the `n` words at `base + o`, lowest first. -/
def mv (m : Mem) (base : Addr) : Nat → Nat → Nat
  | _, 0 => 0
  | o, n + 1 => (VG.Proof.X448.X86_64.word m base o).toNat + 2 ^ 64 * VG.Proof.X448.X86_64.mv m base (o + 8) n

/-- The value of words, lowest first. -/
def wv : List (BitVec 64) → Nat
  | [] => 0
  | v :: vs => v.toNat + 2 ^ 64 * VG.Proof.X448.X86_64.wv vs

/-- The field element at `base + o`: seven words. -/
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat := VG.Proof.X448.X86_64.mv m base o 7

theorem pow64_succ (n : Nat) : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem rv_lt (s : State) : ∀ rs : List Reg, VG.Proof.X448.X86_64.rv s rs < 2 ^ (64 * rs.length)
  | [] => by simp [VG.Proof.X448.X86_64.rv]
  | r :: rs => by
    have h1 := (s.gpr r).isLt
    have h2 := VG.Proof.X448.X86_64.rv_lt s rs
    rw [VG.Proof.X448.X86_64.rv, List.length_cons, VG.Proof.X448.X86_64.pow64_succ]
    generalize 2 ^ (64 * rs.length) = P at *
    generalize VG.Proof.X448.X86_64.rv s rs = y at *
    have : 2 ^ 64 * (y + 1) ≤ 2 ^ 64 * P := Nat.mul_le_mul_left _ h2
    omega

theorem mv_lt (m : Mem) (base : Addr) : ∀ o n, VG.Proof.X448.X86_64.mv m base o n < 2 ^ (64 * n)
  | _, 0 => by simp [VG.Proof.X448.X86_64.mv]
  | o, n + 1 => by
    have h1 := (VG.Proof.X448.X86_64.word m base o).isLt
    have h2 := VG.Proof.X448.X86_64.mv_lt m base (o + 8) n
    rw [VG.Proof.X448.X86_64.mv, VG.Proof.X448.X86_64.pow64_succ]
    generalize 2 ^ (64 * n) = P at *
    generalize VG.Proof.X448.X86_64.mv m base (o + 8) n = y at *
    have : 2 ^ 64 * (y + 1) ≤ 2 ^ 64 * P := Nat.mul_le_mul_left _ h2
    omega

theorem wv_lt : ∀ vs : List (BitVec 64), VG.Proof.X448.X86_64.wv vs < 2 ^ (64 * vs.length)
  | [] => by simp [VG.Proof.X448.X86_64.wv]
  | v :: vs => by
    have h1 := v.isLt
    have h2 := VG.Proof.X448.X86_64.wv_lt vs
    rw [VG.Proof.X448.X86_64.wv, List.length_cons, VG.Proof.X448.X86_64.pow64_succ]
    generalize 2 ^ (64 * vs.length) = P at *
    generalize VG.Proof.X448.X86_64.wv vs = y at *
    have : 2 ^ 64 * (y + 1) ≤ 2 ^ 64 * P := Nat.mul_le_mul_left _ h2
    omega

theorem fe_lt (m : Mem) (base : Addr) (o : Nat) : VG.Proof.X448.X86_64.fe m base o < 2 ^ 448 := by
  have := VG.Proof.X448.X86_64.mv_lt m base o 7
  rwa [show 64 * 7 = 448 from rfl] at this

theorem rv_congr {s s' : State} : ∀ {rs : List Reg}, (∀ r ∈ rs, s'.gpr r = s.gpr r) →
    VG.Proof.X448.X86_64.rv s' rs = VG.Proof.X448.X86_64.rv s rs
  | [], _ => rfl
  | r :: rs, h => by
    simp only [VG.Proof.X448.X86_64.rv, h r List.mem_cons_self, VG.Proof.X448.X86_64.rv_congr (rs := rs) fun r' hr => h r' (List.mem_cons_of_mem _ hr)]

theorem ea_sc (s : State) (d : Nat) : s.ea (sc d) = VG.Proof.X448.X86_64.off (s.gpr .rdi) d := by
  simp only [State.ea, sc, at_, BitVec.ofInt_natCast]

theorem contains_sc {base : Addr} {d n : Nat} (h : d + n ≤ 8192) :
    (⟨base, 8192⟩ : Region).Contains (VG.Proof.X448.X86_64.off base d) n :=
  Offset.contains_base base h (by omega)

theorem Scr.read {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (VG.Proof.X448.X86_64.off base d) n :=
  ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X448.X86_64.contains_sc hd⟩

theorem Scr.write {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions s.wr (VG.Proof.X448.X86_64.off base d) n := ⟨_, hs.wr, VG.Proof.X448.X86_64.contains_sc hd⟩

theorem load_sc {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    s.load64 (s.ea (sc d)) = some (VG.Proof.X448.X86_64.word s.mem base d) := by
  rw [VG.Proof.X448.X86_64.ea_sc, hs.rdi, State.load64, ite_eq_left (hs.read hd)]

theorem readSrc_sc {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    VG.X86_64.readSrc s (.mem (sc d)) = some (VG.Proof.X448.X86_64.word s.mem base d) := VG.Proof.X448.X86_64.load_sc hs hd

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base)
    (h : VG.Proof.X448.X86_64.Keeps rs s s') (hr : .rdi ∉ rs) : VG.Proof.X448.X86_64.Scr s' base :=
  ⟨(h.1 _ hr).trans hs.rdi, h.2.2.2 ▸ hs.wr, hs.nowrap⟩

/-! ## Modulo `p`

`2⁴⁴⁸ ≡ 2²²⁴ + 1`. Lemmas about `P` are applied to explicit arguments:
unifying a pattern with `2 ^ 448` in it against another term makes Lean
try to evaluate the power. -/

open VG.Spec.X448 (P) in
theorem P_eq : 2 ^ 448 = P + (2 ^ 224 + 1) := by decide +kernel

open VG.Spec.X448 (P) in
theorem fold448 (a b : Nat) : (a + 2 ^ 448 * b) % P = (a + (2 ^ 224 + 1) * b) % P := by
  rewrite [VG.Proof.X448.X86_64.P_eq, Nat.add_mul, Nat.add_comm (P * b), ← Nat.add_assoc]
  exact Nat.add_mul_mod_self_left _ _ _

/-- A 32-bit load reads the low half of the word. -/
theorem readW32 (m : Mem) (p : Addr) : (m.readW p 32).toNat = (m.readW p 64).toNat % 2 ^ 32 := by
  rw [← X25519.leNum_bytesAt_32bit, ← X25519.leNum_bytesAt_64, show 8 = 4 + 4 from rfl,
    X25519.bytesAt_add, X25519.leNum_append, X25519.length_bytesAt]
  have := X25519.leNum_lt (Spec.X25519.bytesAt m p 4)
  rw [X25519.length_bytesAt] at this
  omega

/-! ## Stable sources -/

/-- `src` reads `v` in every state that agrees with `s` but on the registers
`X` and the flags. -/
def Stable (X : List Reg) (s : State) (src : Src) (v : BitVec 64) : Prop :=
  ∀ t, (∀ r, r ∉ X → t.gpr r = s.gpr r) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr →
    VG.X86_64.readSrc t src = some v

theorem Stable.read {X : List Reg} {s : State} {src : Src} {v : BitVec 64} (h : VG.Proof.X448.X86_64.Stable X s src v) :
    VG.X86_64.readSrc s src = some v := h s (fun _ _ => rfl) rfl rfl rfl

theorem Stable.mono {X Y : List Reg} {s : State} {src : Src} {v : BitVec 64} (h : VG.Proof.X448.X86_64.Stable Y s src v)
    (hXY : ∀ r ∈ X, r ∈ Y) : VG.Proof.X448.X86_64.Stable X s src v :=
  fun t hg hm hrd hwr => h t (fun r hr => hg r fun h' => hr (hXY r h')) hm hrd hwr

/-- A stable source of `s` is one of any state that agrees with `s` but on
`X`. -/
theorem Stable.of_keeps {X : List Reg} {s s' : State} {src : Src} {v : BitVec 64}
    (h : VG.Proof.X448.X86_64.Stable X s src v) (hk : VG.Proof.X448.X86_64.Keeps X s s') : VG.Proof.X448.X86_64.Stable X s' src v :=
  fun t hg hm hrd hwr => h t (fun r hr => (hg r hr).trans (hk.1 r hr)) (hm.trans hk.2.1)
    (hrd.trans hk.2.2.1) (hwr.trans hk.2.2.2)

theorem stable_reg {X : List Reg} (s : State) {r : Reg} (hr : r ∉ X) :
    VG.Proof.X448.X86_64.Stable X s (.reg r) (s.gpr r) :=
  fun _ hg _ _ _ => by rw [VG.X86_64.readSrc, hg r hr]

theorem stable_imm (X : List Reg) (s : State) (v : BitVec 32) :
    VG.Proof.X448.X86_64.Stable X s (.imm v) (v.signExtend 64) := fun _ _ _ _ _ => rfl

theorem stable_imm0 (X : List Reg) (s : State) : VG.Proof.X448.X86_64.Stable X s (.imm 0) 0 := fun _ _ _ _ _ => rfl

theorem stable_sc {X : List Reg} {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (hX : .rdi ∉ X)
    {d : Nat} (hd : d + 8 ≤ 8192) : VG.Proof.X448.X86_64.Stable X s (.mem (sc d)) (VG.Proof.X448.X86_64.word s.mem base d) :=
  fun t hg hm _ hwr => by
    rw [← hm]
    exact VG.Proof.X448.X86_64.readSrc_sc ⟨(hg _ hX).trans hs.rdi, hwr ▸ hs.wr, hs.nowrap⟩ hd

/-! ## Memory outside a range -/

/-- The offset of `x` from `base`. -/
abbrev ofs (base x : Addr) : Nat := (x - base).toNat

theorem ofs_off (base : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    VG.Proof.X448.X86_64.ofs base (VG.Proof.X448.X86_64.off base d + BitVec.ofNat 64 i) = d + i := by
  simp only [VG.Proof.X448.X86_64.ofs, VG.Proof.X448.X86_64.off]
  rw [Offset.add_add, Mem.sub_ofNat_toNat base h]

theorem ofs_off' (base : Addr) {d : Nat} (h : d < 2 ^ 64) : VG.Proof.X448.X86_64.ofs base (VG.Proof.X448.X86_64.off base d) = d :=
  Mem.sub_ofNat_toNat base h

/-- `m'` agrees with `m` but on the bytes at offsets `[o, o + n)` of `base`. -/
def Outside (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (VG.Proof.X448.X86_64.ofs base x < o ∨ o + n ≤ VG.Proof.X448.X86_64.ofs base x) → m' x = m x

theorem Outside.refl (base : Addr) (o n : Nat) (m : Mem) : VG.Proof.X448.X86_64.Outside base o n m m := fun _ _ => rfl

theorem Outside.trans {base : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : VG.Proof.X448.X86_64.Outside base o n m₁ m₂)
    (h₂ : VG.Proof.X448.X86_64.Outside base o n m₂ m₃) : VG.Proof.X448.X86_64.Outside base o n m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Outside.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : VG.Proof.X448.X86_64.Outside base o n m m')
    (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n') : VG.Proof.X448.X86_64.Outside base o' n' m m' :=
  fun x hx => h x (by omega)

/-- A word at an offset outside the bytes that changed. -/
theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.X86_64.Outside base o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 < 2 ^ 64) : VG.Proof.X448.X86_64.word m' base d = VG.Proof.X448.X86_64.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.X86_64.ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.mv {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.X86_64.Outside base o n m m') :
    ∀ {d k : Nat}, (d + 8 * k ≤ o ∨ o + n ≤ d) → d + 8 * k < 2 ^ 64 →
      VG.Proof.X448.X86_64.mv m' base d k = VG.Proof.X448.X86_64.mv m base d k
  | _, 0, _, _ => rfl
  | d, k + 1, hd, hd' => by
    simp only [X86_64.mv]
    rw [h.word (by omega) (by omega), h.mv (d := d + 8) (k := k) (by omega) (by omega)]

theorem Outside.fe {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.X86_64.Outside base o n m m') {d : Nat}
    (hd : d + 56 ≤ o ∨ o + n ≤ d) (hd' : d + 56 < 2 ^ 64) : VG.Proof.X448.X86_64.fe m' base d = VG.Proof.X448.X86_64.fe m base d :=
  h.mv (by omega) (by omega)

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 < 2 ^ 64) :
    VG.Proof.X448.X86_64.Outside base d 8 m (m.writeW (VG.Proof.X448.X86_64.off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [VG.Proof.X448.X86_64.ofs] at hx
  omega

theorem word_writeW_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) :
    VG.Proof.X448.X86_64.word (m.writeW (VG.Proof.X448.X86_64.off base d) v) base d = v := Mem.readW_writeW_self64 _ _ _

/-- Memory outside two ranges. -/
def Outside2 (base : Addr) (x nx y ny : Nat) (m m' : Mem) : Prop :=
  ∀ p, (VG.Proof.X448.X86_64.ofs base p < x ∨ x + nx ≤ VG.Proof.X448.X86_64.ofs base p) →
    (VG.Proof.X448.X86_64.ofs base p < y ∨ y + ny ≤ VG.Proof.X448.X86_64.ofs base p) → m' p = m p

theorem Outside2.refl (base : Addr) (x nx y ny : Nat) (m : Mem) : VG.Proof.X448.X86_64.Outside2 base x nx y ny m m :=
  fun _ _ _ => rfl

theorem Outside2.trans {base : Addr} {x nx y ny : Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : VG.Proof.X448.X86_64.Outside2 base x nx y ny m₁ m₂) (h₂ : VG.Proof.X448.X86_64.Outside2 base x nx y ny m₂ m₃) :
    VG.Proof.X448.X86_64.Outside2 base x nx y ny m₁ m₃ := fun p hx hy => (h₂ p hx hy).trans (h₁ p hx hy)

theorem Outside.left {base : Addr} {x nx : Nat} {m m' : Mem} (h : VG.Proof.X448.X86_64.Outside base x nx m m')
    (y ny : Nat) : VG.Proof.X448.X86_64.Outside2 base x nx y ny m m' := fun p hp _ => h p hp

theorem Outside.right {base : Addr} {y ny : Nat} {m m' : Mem} (h : VG.Proof.X448.X86_64.Outside base y ny m m')
    (x nx : Nat) : VG.Proof.X448.X86_64.Outside2 base x nx y ny m m' := fun p _ hp => h p hp

theorem Outside2.word {base : Addr} {x nx y ny : Nat} {m m' : Mem} (h : VG.Proof.X448.X86_64.Outside2 base x nx y ny m m')
    {d : Nat} (hx : d + 8 ≤ x ∨ x + nx ≤ d) (hy : d + 8 ≤ y ∨ y + ny ≤ d) (hd : d + 8 < 2 ^ 64) :
    VG.Proof.X448.X86_64.word m' base d = VG.Proof.X448.X86_64.word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [VG.Proof.X448.X86_64.ofs_off base (by omega)]; omega)
    (by rw [VG.Proof.X448.X86_64.ofs_off base (by omega)]; omega)).symm).symm

theorem Outside2.mv {base : Addr} {x nx y ny : Nat} {m m' : Mem} (h : VG.Proof.X448.X86_64.Outside2 base x nx y ny m m') :
    ∀ {d k : Nat}, (d + 8 * k ≤ x ∨ x + nx ≤ d) → (d + 8 * k ≤ y ∨ y + ny ≤ d) →
      d + 8 * k < 2 ^ 64 → VG.Proof.X448.X86_64.mv m' base d k = VG.Proof.X448.X86_64.mv m base d k
  | _, 0, _, _, _ => rfl
  | d, k + 1, hx, hy, hd' => by
    simp only [X86_64.mv]
    rw [h.word (by omega) (by omega) (by omega),
      h.mv (d := d + 8) (k := k) (by omega) (by omega) (by omega)]

theorem Outside2.outside {base : Addr} {x nx y ny : Nat} {m m' : Mem}
    (h : VG.Proof.X448.X86_64.Outside2 base x nx y ny m m') {o n : Nat} (hx : o ≤ x) (hx' : x + nx ≤ o + n) (hy : o ≤ y)
    (hy' : y + ny ≤ o + n) : VG.Proof.X448.X86_64.Outside base o n m m' :=
  fun p hp => h p (by omega) (by omega)

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Chain`. -/
section

/-!
# X448 on x86-64: carry chains, loads and stores

Proven once, by induction on the registers, for any number of words:

* `adcs_ok`, `add_chain_ok`: an `add` and `adc`s along registers, adding the
  values of stable sources, with the carry out;
* `sbbs_ok`, `sub_chain_ok`: the same for `sub` and `sbb`;
* `loads_ok`, `stores_ok`: words between registers and the working space;
* `fold_ok`, `unfold_ok`, `carryOut_ok`: `r15 · (1 + 2²²⁴)` added to (taken
  from) `r8–r14`, and the carry into `r15`;
* `mulStep_ok`: a multiply-accumulate step.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

theorem toNat_ofBool (c : Bool) : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by
  cases c <;> rfl

theorem se0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide

theorem add_carry (a b : BitVec 64) :
    (a + b).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat)).toNat = a.toNat + b.toNat := by
  have := a.isLt; have := b.isLt
  rw [BitVec.toNat_add]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem adc_carry (a b : BitVec 64) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 64).toNat +
        2 ^ 64 * (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat =
      a.toNat + b.toNat + c.toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, VG.Proof.X448.X86_64.toNat_ofBool]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem sub_borrow (a b : BitVec 64) :
    (a - b).toNat + b.toNat = a.toNat + 2 ^ 64 * (decide (a.toNat < b.toNat)).toNat := by
  have := a.isLt; have := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem sbb_borrow (a b : BitVec 64) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 64).toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ 64 * (decide (a.toNat < b.toNat + c.toNat)).toNat := by
  have := a.isLt; have := b.isLt; have := Bool.toNat_le c
  rw [BitVec.toNat_sub, BitVec.toNat_sub, VG.Proof.X448.X86_64.toNat_ofBool]
  by_cases h : a.toNat < b.toNat + c.toNat <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

theorem Keeps.setFlagsReg {X : List Reg} {s₀ s : State} (h : VG.Proof.X448.X86_64.Keeps X s₀ s) {r : Reg} (hr : r ∈ X)
    (v : BitVec 64) {w : Nat} (x : BitVec w) (c o : Bool) :
    VG.Proof.X448.X86_64.Keeps X s₀ ((arithFlags s x c o).setReg r v) := by
  refine ⟨fun r' hr' => ?_, h.2.1, h.2.2.1, h.2.2.2⟩
  rw [RegUpd.gpr_setReg_of_ne _ _ (fun e => hr' (by rw [e]; exact hr)), RegUpd.gpr_arithFlags]
  exact h.1 r' hr'

theorem keeps_setFlagsReg (s : State) (r : Reg) (v : BitVec 64) {w : Nat} (x : BitVec w)
    (c o : Bool) : VG.Proof.X448.X86_64.Keeps [r] s ((arithFlags s x c o).setReg r v) :=
  (Keeps.refl [r] s).setFlagsReg List.mem_cons_self v x c o

/-! ## Carry chains -/

/-- `adc`s along `rs`, adding the stable sources `ss` (values `vs`) and the
carry `c`. -/
theorem adcs_ok (X : List Reg) (s₀ : State) :
    ∀ (rs : List Reg) (ss : List Src) (vs : List (BitVec 64)) (s : State) (c : Bool),
      VG.Proof.X448.X86_64.Keeps X s₀ s → (∀ r ∈ rs, r ∈ X) → rs.Nodup → rs.length = ss.length →
      List.Forall₂ (VG.Proof.X448.X86_64.Stable X s₀) ss vs → s.cf = some c →
      WP isa (.block (chain .adc .adc rs ss)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
        VG.Proof.X448.X86_64.rv s' rs + 2 ^ (64 * rs.length) * c'.toNat = VG.Proof.X448.X86_64.rv s rs + VG.Proof.X448.X86_64.wv vs + c.toNat ∧ VG.Proof.X448.X86_64.Keeps rs s s'
  | [], ss, _, s, c, _, _, _, hl, hf, hc => by
    cases ss with
    | nil => cases hf; exact WP.block_nil ⟨c, hc, by simp [VG.Proof.X448.X86_64.rv, VG.Proof.X448.X86_64.wv], Keeps.refl _ _⟩
    | cons => simp at hl
  | r :: rs, [], _, _, _, _, _, _, hl, _, _ => by simp at hl
  | r :: rs, src :: ss, vs, s, c, hk, hX, hnd, hl, hf, hc => by
    cases hf with
    | cons hv hf =>
    rename_i v vs
    have hrX : r ∈ X := hX r List.mem_cons_self
    have hrs : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hv' : VG.X86_64.readSrc s src = some v :=
      hv s (fun r' hr' => hk.1 r' hr') hk.2.1 hk.2.2.1 hk.2.2.2
    let x := s.gpr r + v + (BitVec.ofBool c).setWidth 64
    let c1 := decide (2 ^ 64 ≤ (s.gpr r).toNat + v.toNat + c.toNat)
    let s1 := (arithFlags s x c1 (addOverflow (s.gpr r) v x)).setReg r x
    have he : exec (.alu .adc r src) s = some s1 := by
      simp only [exec, execAlu, hv', hc, Option.bind_some, Option.map_some]; rfl
    rw [chain, WP.block_cons_iff]
    refine ⟨s1, he, ?_⟩
    have hk1 : VG.Proof.X448.X86_64.Keeps X s₀ s1 := hk.setFlagsReg hrX x x c1 _
    refine WP.mono (VG.Proof.X448.X86_64.adcs_ok X s₀ rs ss vs s1 c1 hk1 (fun r' h => hX r' (List.mem_cons_of_mem _ h))
      (List.nodup_cons.mp hnd).2 (by simpa using hl) hf
      (by simp only [s1, RegUpd.cf_setReg, RegUpd.cf_arithFlags])) fun s' ⟨c', hc', he', hk'⟩ => ?_
    have k1 : VG.Proof.X448.X86_64.Keeps [r] s s1 := VG.Proof.X448.X86_64.keeps_setFlagsReg s r x x c1 _
    refine ⟨c', hc', ?_, ?_⟩
    · have g1 : s'.gpr r = x := by
        rw [hk'.1 r hrs]; exact RegUpd.gpr_setReg_self _ _ _
      have g2 : VG.Proof.X448.X86_64.rv s1 rs = VG.Proof.X448.X86_64.rv s rs :=
        VG.Proof.X448.X86_64.rv_congr fun r' hr' => k1.1 r' (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact fun e => hrs (e ▸ hr'))
      have ac : x.toNat + 2 ^ 64 * c1.toNat = (s.gpr r).toNat + v.toNat + c.toNat :=
        VG.Proof.X448.X86_64.adc_carry (s.gpr r) v c
      rw [VG.Proof.X448.X86_64.rv, g1, VG.Proof.X448.X86_64.rv, List.length_cons, VG.Proof.X448.X86_64.pow64_succ, VG.Proof.X448.X86_64.wv, Nat.mul_assoc]
      rw [g2] at he'
      generalize 2 ^ (64 * rs.length) * c'.toNat = Y at he' ⊢
      omega
    · refine ⟨fun r' hr' => ?_, hk'.2.1.trans k1.2.1, hk'.2.2.1.trans k1.2.2.1,
        hk'.2.2.2.trans k1.2.2.2⟩
      simp only [List.mem_cons, not_or] at hr'
      rw [hk'.1 r' hr'.2, k1.1 r' (by simp [hr'.1])]

/-- `add`, then `adc`s along `rs`, adding the stable sources `ss`. -/
theorem add_chain_ok (X : List Reg) (s : State) (r : Reg) (rs : List Reg) (src : Src) (ss : List Src)
    (v : BitVec 64) (vs : List (BitVec 64)) (hX : ∀ r' ∈ r :: rs, r' ∈ X) (hnd : (r :: rs).Nodup)
    (hl : rs.length = ss.length) (hv : VG.Proof.X448.X86_64.Stable X s src v) (hf : List.Forall₂ (VG.Proof.X448.X86_64.Stable X s) ss vs) :
    WP isa (.block (chain .add .adc (r :: rs) (src :: ss))) s fun s' => ∃ c' : Bool,
      s'.cf = some c' ∧ VG.Proof.X448.X86_64.rv s' (r :: rs) + 2 ^ (64 * (r :: rs).length) * c'.toNat =
        VG.Proof.X448.X86_64.rv s (r :: rs) + VG.Proof.X448.X86_64.wv (v :: vs) ∧ VG.Proof.X448.X86_64.Keeps (r :: rs) s s' := by
  have hrX : r ∈ X := hX r List.mem_cons_self
  have hrs : r ∉ rs := (List.nodup_cons.mp hnd).1
  let x := s.gpr r + v
  let c1 := decide (2 ^ 64 ≤ (s.gpr r).toNat + v.toNat)
  let s1 := (arithFlags s x c1 (addOverflow (s.gpr r) v x)).setReg r x
  have he : exec (.alu .add r src) s = some s1 := by
    simp only [exec, execAlu, hv.read, Option.bind_some]; rfl
  rw [chain, WP.block_cons_iff]
  refine ⟨s1, he, ?_⟩
  have hk1 : VG.Proof.X448.X86_64.Keeps X s s1 := (Keeps.refl X s).setFlagsReg hrX x x c1 _
  refine WP.mono (VG.Proof.X448.X86_64.adcs_ok X s rs ss vs s1 c1 hk1 (fun r' h => hX r' (List.mem_cons_of_mem _ h))
    (List.nodup_cons.mp hnd).2 hl hf
    (by simp only [s1, RegUpd.cf_setReg, RegUpd.cf_arithFlags])) fun s' ⟨c', hc', he', hk'⟩ => ?_
  have k1 : VG.Proof.X448.X86_64.Keeps [r] s s1 := VG.Proof.X448.X86_64.keeps_setFlagsReg s r x x c1 _
  refine ⟨c', hc', ?_, ?_⟩
  · have g1 : s'.gpr r = x := by
      rw [hk'.1 r hrs]; exact RegUpd.gpr_setReg_self _ _ _
    have g2 : VG.Proof.X448.X86_64.rv s1 rs = VG.Proof.X448.X86_64.rv s rs :=
      VG.Proof.X448.X86_64.rv_congr fun r' hr' => k1.1 r' (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact fun e => hrs (e ▸ hr'))
    have ac : x.toNat + 2 ^ 64 * c1.toNat = (s.gpr r).toNat + v.toNat := VG.Proof.X448.X86_64.add_carry (s.gpr r) v
    rw [VG.Proof.X448.X86_64.rv, g1, VG.Proof.X448.X86_64.rv, List.length_cons, VG.Proof.X448.X86_64.pow64_succ, VG.Proof.X448.X86_64.wv, Nat.mul_assoc]
    rw [g2] at he'
    generalize 2 ^ (64 * rs.length) * c'.toNat = Y at he' ⊢
    omega
  · refine ⟨fun r' hr' => ?_, hk'.2.1.trans k1.2.1, hk'.2.2.1.trans k1.2.2.1,
      hk'.2.2.2.trans k1.2.2.2⟩
    simp only [List.mem_cons, not_or] at hr'
    rw [hk'.1 r' hr'.2, k1.1 r' (by simp [hr'.1])]

/-- `sbb`s along `rs`, subtracting the stable sources `ss` (values `vs`) and
the borrow `c`. -/
theorem sbbs_ok (X : List Reg) (s₀ : State) :
    ∀ (rs : List Reg) (ss : List Src) (vs : List (BitVec 64)) (s : State) (c : Bool),
      VG.Proof.X448.X86_64.Keeps X s₀ s → (∀ r ∈ rs, r ∈ X) → rs.Nodup → rs.length = ss.length →
      List.Forall₂ (VG.Proof.X448.X86_64.Stable X s₀) ss vs → s.cf = some c →
      WP isa (.block (chain .sbb .sbb rs ss)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
        VG.Proof.X448.X86_64.rv s' rs + VG.Proof.X448.X86_64.wv vs + c.toNat = VG.Proof.X448.X86_64.rv s rs + 2 ^ (64 * rs.length) * c'.toNat ∧ VG.Proof.X448.X86_64.Keeps rs s s'
  | [], ss, _, s, c, _, _, _, hl, hf, hc => by
    cases ss with
    | nil => cases hf; exact WP.block_nil ⟨c, hc, by simp [VG.Proof.X448.X86_64.rv, VG.Proof.X448.X86_64.wv], Keeps.refl _ _⟩
    | cons => simp at hl
  | r :: rs, [], _, _, _, _, _, _, hl, _, _ => by simp at hl
  | r :: rs, src :: ss, vs, s, c, hk, hX, hnd, hl, hf, hc => by
    cases hf with
    | cons hv hf =>
    rename_i v vs
    have hrX : r ∈ X := hX r List.mem_cons_self
    have hrs : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hv' : VG.X86_64.readSrc s src = some v :=
      hv s (fun r' hr' => hk.1 r' hr') hk.2.1 hk.2.2.1 hk.2.2.2
    let x := s.gpr r - v - (BitVec.ofBool c).setWidth 64
    let c1 := decide ((s.gpr r).toNat < v.toNat + c.toNat)
    let s1 := (arithFlags s x c1 (subOverflow (s.gpr r) v x)).setReg r x
    have he : exec (.alu .sbb r src) s = some s1 := by
      simp only [exec, execAlu, hv', hc, Option.bind_some, Option.map_some]; rfl
    rw [chain, WP.block_cons_iff]
    refine ⟨s1, he, ?_⟩
    have hk1 : VG.Proof.X448.X86_64.Keeps X s₀ s1 := hk.setFlagsReg hrX x x c1 _
    refine WP.mono (VG.Proof.X448.X86_64.sbbs_ok X s₀ rs ss vs s1 c1 hk1 (fun r' h => hX r' (List.mem_cons_of_mem _ h))
      (List.nodup_cons.mp hnd).2 (by simpa using hl) hf
      (by simp only [s1, RegUpd.cf_setReg, RegUpd.cf_arithFlags])) fun s' ⟨c', hc', he', hk'⟩ => ?_
    have k1 : VG.Proof.X448.X86_64.Keeps [r] s s1 := VG.Proof.X448.X86_64.keeps_setFlagsReg s r x x c1 _
    refine ⟨c', hc', ?_, ?_⟩
    · have g1 : s'.gpr r = x := by
        rw [hk'.1 r hrs]; exact RegUpd.gpr_setReg_self _ _ _
      have g2 : VG.Proof.X448.X86_64.rv s1 rs = VG.Proof.X448.X86_64.rv s rs :=
        VG.Proof.X448.X86_64.rv_congr fun r' hr' => k1.1 r' (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact fun e => hrs (e ▸ hr'))
      have ac : x.toNat + v.toNat + c.toNat = (s.gpr r).toNat + 2 ^ 64 * c1.toNat :=
        VG.Proof.X448.X86_64.sbb_borrow (s.gpr r) v c
      rw [VG.Proof.X448.X86_64.rv, g1, VG.Proof.X448.X86_64.rv, List.length_cons, VG.Proof.X448.X86_64.pow64_succ, VG.Proof.X448.X86_64.wv, Nat.mul_assoc]
      rw [g2] at he'
      generalize 2 ^ (64 * rs.length) * c'.toNat = Y at he' ⊢
      omega
    · refine ⟨fun r' hr' => ?_, hk'.2.1.trans k1.2.1, hk'.2.2.1.trans k1.2.2.1,
        hk'.2.2.2.trans k1.2.2.2⟩
      simp only [List.mem_cons, not_or] at hr'
      rw [hk'.1 r' hr'.2, k1.1 r' (by simp [hr'.1])]

/-- `sub`, then `sbb`s along `rs`, subtracting the stable sources `ss`. -/
theorem sub_chain_ok (X : List Reg) (s : State) (r : Reg) (rs : List Reg) (src : Src) (ss : List Src)
    (v : BitVec 64) (vs : List (BitVec 64)) (hX : ∀ r' ∈ r :: rs, r' ∈ X) (hnd : (r :: rs).Nodup)
    (hl : rs.length = ss.length) (hv : VG.Proof.X448.X86_64.Stable X s src v) (hf : List.Forall₂ (VG.Proof.X448.X86_64.Stable X s) ss vs) :
    WP isa (.block (chain .sub .sbb (r :: rs) (src :: ss))) s fun s' => ∃ c' : Bool,
      s'.cf = some c' ∧ VG.Proof.X448.X86_64.rv s' (r :: rs) + VG.Proof.X448.X86_64.wv (v :: vs) =
        VG.Proof.X448.X86_64.rv s (r :: rs) + 2 ^ (64 * (r :: rs).length) * c'.toNat ∧ VG.Proof.X448.X86_64.Keeps (r :: rs) s s' := by
  have hrX : r ∈ X := hX r List.mem_cons_self
  have hrs : r ∉ rs := (List.nodup_cons.mp hnd).1
  let x := s.gpr r - v
  let c1 := decide ((s.gpr r).toNat < v.toNat)
  let s1 := (arithFlags s x c1 (subOverflow (s.gpr r) v x)).setReg r x
  have he : exec (.alu .sub r src) s = some s1 := by
    simp only [exec, execAlu, hv.read, Option.bind_some]; rfl
  rw [chain, WP.block_cons_iff]
  refine ⟨s1, he, ?_⟩
  have hk1 : VG.Proof.X448.X86_64.Keeps X s s1 := (Keeps.refl X s).setFlagsReg hrX x x c1 _
  refine WP.mono (VG.Proof.X448.X86_64.sbbs_ok X s rs ss vs s1 c1 hk1 (fun r' h => hX r' (List.mem_cons_of_mem _ h))
    (List.nodup_cons.mp hnd).2 hl hf
    (by simp only [s1, RegUpd.cf_setReg, RegUpd.cf_arithFlags])) fun s' ⟨c', hc', he', hk'⟩ => ?_
  have k1 : VG.Proof.X448.X86_64.Keeps [r] s s1 := VG.Proof.X448.X86_64.keeps_setFlagsReg s r x x c1 _
  refine ⟨c', hc', ?_, ?_⟩
  · have g1 : s'.gpr r = x := by
      rw [hk'.1 r hrs]; exact RegUpd.gpr_setReg_self _ _ _
    have g2 : VG.Proof.X448.X86_64.rv s1 rs = VG.Proof.X448.X86_64.rv s rs :=
      VG.Proof.X448.X86_64.rv_congr fun r' hr' => k1.1 r' (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact fun e => hrs (e ▸ hr'))
    have ac : x.toNat + v.toNat = (s.gpr r).toNat + 2 ^ 64 * c1.toNat := VG.Proof.X448.X86_64.sub_borrow (s.gpr r) v
    rw [VG.Proof.X448.X86_64.rv, g1, VG.Proof.X448.X86_64.rv, List.length_cons, VG.Proof.X448.X86_64.pow64_succ, VG.Proof.X448.X86_64.wv, Nat.mul_assoc]
    rw [g2] at he'
    generalize 2 ^ (64 * rs.length) * c'.toNat = Y at he' ⊢
    omega
  · refine ⟨fun r' hr' => ?_, hk'.2.1.trans k1.2.1, hk'.2.2.1.trans k1.2.2.1,
      hk'.2.2.2.trans k1.2.2.2⟩
    simp only [List.mem_cons, not_or] at hr'
    rw [hk'.1 r' hr'.2, k1.1 r' (by simp [hr'.1])]

/-! ## Loads and stores -/

/-- `loads o rs`: each register of `rs` holds its word of `[o]`. -/
theorem loads_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) :
    ∀ (o : Nat) (rs : List Reg), rs.Nodup → .rdi ∉ rs → o + 8 * rs.length ≤ 8192 →
      WP isa (.block (loads o rs)) s fun s' =>
        (∀ i < rs.length, ∀ d, s'.gpr (rs.getD i d) = VG.Proof.X448.X86_64.word s.mem base (o + 8 * i)) ∧
        VG.Proof.X448.X86_64.rv s' rs = VG.Proof.X448.X86_64.mv s.mem base o rs.length ∧ VG.Proof.X448.X86_64.Keeps rs s s'
  | _, [], _, _, _ => WP.block_nil ⟨fun _ h => by simp at h, rfl, Keeps.refl _ _⟩
  | o, r :: rs, hnd, hr, ho => by
    have hrs : r ∉ rs := (List.nodup_cons.mp hnd).1
    have hrd : r ≠ .rdi := fun e => hr (e ▸ List.mem_cons_self)
    have hl : (r :: rs).length = rs.length + 1 := rfl
    rw [loads, WP.block_cons_iff]
    refine ⟨s.setReg r (VG.Proof.X448.X86_64.word s.mem base o), by
      simp only [exec, VG.Proof.X448.X86_64.readSrc_sc hs (d := o) (by omega), Option.map_some], ?_⟩
    have hs1 : VG.Proof.X448.X86_64.Scr (s.setReg r (VG.Proof.X448.X86_64.word s.mem base o)) base :=
      ⟨by rw [RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hrd)]; exact hs.rdi, hs.wr, hs.nowrap⟩
    refine WP.mono (VG.Proof.X448.X86_64.loads_ok hs1 (o + 8) rs (List.nodup_cons.mp hnd).2
      (fun h => hr (List.mem_cons_of_mem _ h)) (by omega)) fun s' ⟨hw, hv, hk⟩ => ?_
    have g : s'.gpr r = VG.Proof.X448.X86_64.word s.mem base o := by
      rw [hk.1 r hrs]; exact RegUpd.gpr_setReg_self _ _ _
    refine ⟨fun i hi d => ?_, ?_, ?_⟩
    · cases i with
      | zero => simpa using g
      | succ i =>
        rw [List.getD_cons_succ, hw i (by simpa using hi) d, RegUpd.mem_setReg,
          show o + 8 + 8 * i = o + 8 * (i + 1) by omega]
    · rw [VG.Proof.X448.X86_64.rv, g, hv, List.length_cons, VG.Proof.X448.X86_64.mv]; rfl
    · refine ⟨fun r' hr' => ?_, hk.2.1, hk.2.2.1, hk.2.2.2⟩
      simp only [List.mem_cons, not_or] at hr'
      rw [hk.1 r' hr'.2, RegUpd.gpr_setReg_of_ne _ _ hr'.1]

/-- `stores o rs`: the words of `[o]` are the registers `rs`, and nothing
else changes. -/
theorem stores_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) :
    ∀ (o : Nat) (rs : List Reg), o + 8 * rs.length ≤ 8192 →
      WP isa (.block (stores o rs)) s fun s' =>
        VG.Proof.X448.X86_64.mv s'.mem base o rs.length = VG.Proof.X448.X86_64.rv s rs ∧ VG.Proof.X448.X86_64.Outside base o (8 * rs.length) s.mem s'.mem ∧
        (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | _, [], _ => WP.block_nil ⟨rfl, Outside.refl _ _ _ _, fun _ => rfl, rfl, rfl⟩
  | o, r :: rs, ho => by
    rw [stores, WP.block_cons_iff]
    have hl : (r :: rs).length = rs.length + 1 := rfl
    let s1 : State := { s with mem := s.mem.writeW (VG.Proof.X448.X86_64.off base o) (s.gpr r) }
    refine ⟨s1, by
      have hw := hs.write (d := o) (n := 8) (by omega)
      simp only [exec, VG.Proof.X448.X86_64.ea_sc, hs.rdi, State.store64, hw, ite_true]; rfl, ?_⟩
    have hs1 : VG.Proof.X448.X86_64.Scr s1 base := ⟨hs.rdi, hs.wr, hs.nowrap⟩
    refine WP.mono (VG.Proof.X448.X86_64.stores_ok hs1 (o + 8) rs (by omega)) fun s' ⟨hv, ho', hg, hrd, hwr⟩ => ?_
    have o1 : VG.Proof.X448.X86_64.Outside base o 8 s.mem s1.mem := VG.Proof.X448.X86_64.writeW_outside _ _ _ (by omega)
    refine ⟨?_, ?_, fun r' => hg r', hrd, hwr⟩
    · rw [List.length_cons, VG.Proof.X448.X86_64.mv, hv, VG.Proof.X448.X86_64.rv, ho'.word (by omega) (by omega)]
      simp only [s1, VG.Proof.X448.X86_64.word_writeW_self]
      rw [VG.Proof.X448.X86_64.rv_congr (s := s) (s' := s1) fun _ _ => rfl]
    · exact (o1.mono (by omega) (by omega)).trans (ho'.mono (by omega) (by omega))

theorem stable_scs {X : List Reg} {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (hX : .rdi ∉ X) :
    ∀ ds : List Nat, (∀ d ∈ ds, d + 8 ≤ 8192) →
      List.Forall₂ (VG.Proof.X448.X86_64.Stable X s) (ds.map fun d => .mem (sc d)) (ds.map fun d => VG.Proof.X448.X86_64.word s.mem base d)
  | [], _ => .nil
  | d :: ds, h => .cons (VG.Proof.X448.X86_64.stable_sc hs hX (h d List.mem_cons_self))
      (VG.Proof.X448.X86_64.stable_scs hs hX ds fun d' hd => h d' (List.mem_cons_of_mem _ hd))

/-! ## Folding the top word -/

theorem len_W : 64 * W.length = 448 := rfl

theorem W_nodup : W.Nodup := by decide

theorem W_lit : [Reg.r8, .r9, .r10, .r11, .r12, .r13, .r14] = W := rfl

theorem toNat_zero64 : (0 : BitVec 64).toNat = 0 := rfl

/-- `r15 = CF`. -/
theorem carryOut_ok (s : State) {c : Bool} (hc : s.cf = some c) :
    WP isa (.block carryOut) s fun s' => (s'.gpr .r15).toNat = c.toNat ∧ VG.Proof.X448.X86_64.Keeps [.r15] s s' := by
  apply WP.of_runBlock
  simp only [carryOut, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32,
    execAlu, State.setReg32, Option.map_some, Option.bind_some, RegUpd.gpr_setReg_self,
    RegUpd.cf_setReg, hc, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · cases c <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr]

theorem rotr32 (x : BitVec 64) (h : x.toNat < 2 ^ 32) :
    (x.rotateRight 32).toNat = x.toNat * 2 ^ 32 := by
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.reduceSub, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.div_eq_of_lt h, Nat.zero_or, Nat.mod_eq_of_lt (by omega)]

/-- `rax = r15 << 32`, for `r15 < 2³²`. -/
theorem shl32_ok (s : State) (h : (s.gpr .r15).toNat < 2 ^ 32) :
    WP isa (.block [.mov .rax (.reg .r15), .shift .ror .rax 32]) s fun s' =>
      (s'.gpr .rax).toNat = (s.gpr .r15).toNat * 2 ^ 32 ∧ VG.Proof.X448.X86_64.Keeps [.rax] s s' := by
  apply WP.of_runBlock
  have h32 : (1 ≤ 32 ∧ 32 ≤ 63) = True := by decide
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execShift, h32, ite_true,
    Option.map_some, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.X448.X86_64.rotr32 _ h, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

theorem Keeps.rv_eq {X rs : List Reg} {s s' : State} (h : VG.Proof.X448.X86_64.Keeps X s s') (hd : ∀ r ∈ rs, r ∉ X) :
    VG.Proof.X448.X86_64.rv s' rs = VG.Proof.X448.X86_64.rv s rs := VG.Proof.X448.X86_64.rv_congr fun r hr => h.1 r (hd r hr)

/-- The sources of `fold` and `unfold`: `r15` and `rax = r15 << 32` at words 0
and 3. -/
theorem fold_srcs (s : State) :
    List.Forall₂ (VG.Proof.X448.X86_64.Stable W s) [.imm 0, .imm 0, .reg .rax, .imm 0, .imm 0, .imm 0]
      [0, 0, s.gpr .rax, 0, 0, 0] :=
  .cons (VG.Proof.X448.X86_64.stable_imm0 _ _) <| .cons (VG.Proof.X448.X86_64.stable_imm0 _ _) <| .cons (VG.Proof.X448.X86_64.stable_reg s (by decide)) <|
    .cons (VG.Proof.X448.X86_64.stable_imm0 _ _) <| .cons (VG.Proof.X448.X86_64.stable_imm0 _ _) <| .cons (VG.Proof.X448.X86_64.stable_imm0 _ _) .nil

/-- `fold`: `r8–r14 + r15 (1 + 2²²⁴)`, with the carry out. -/
theorem fold_ok (s : State) (h : (s.gpr .r15).toNat < 2 ^ 32) :
    WP isa (.block fold) s fun s' => ∃ c : Bool, s'.cf = some c ∧
      VG.Proof.X448.X86_64.rv s' W + 2 ^ 448 * c.toNat = VG.Proof.X448.X86_64.rv s W + (s.gpr .r15).toNat * (1 + 2 ^ 224) ∧
      VG.Proof.X448.X86_64.Keeps (.rax :: W) s s' := by
  rw [fold, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.shl32_ok s h) fun s1 ⟨h1, k1⟩ => ?_
  have r15 : s1.gpr .r15 = s.gpr .r15 := k1.1 _ (by decide)
  refine WP.mono (VG.Proof.X448.X86_64.add_chain_ok W s1 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] (.reg .r15) _
    (s1.gpr .r15) _ (fun _ h => h) VG.Proof.X448.X86_64.W_nodup rfl (VG.Proof.X448.X86_64.stable_reg s1 (by decide)) (VG.Proof.X448.X86_64.fold_srcs s1))
    fun s' ⟨c, hc, he, hk⟩ => ⟨c, hc, ?_, (k1.mono (by decide)).trans (hk.mono (by decide))⟩
  have e1 : VG.Proof.X448.X86_64.rv s1 W = VG.Proof.X448.X86_64.rv s W := k1.rv_eq (by decide)
  rw [VG.Proof.X448.X86_64.W_lit, VG.Proof.X448.X86_64.len_W, e1] at he
  simp only [VG.Proof.X448.X86_64.wv, r15, VG.Proof.X448.X86_64.toNat_zero64] at he
  omega

/-- `unfold`: `r8–r14 - r15 (1 + 2²²⁴)`, with the borrow out. -/
theorem unfold_ok (s : State) (h : (s.gpr .r15).toNat < 2 ^ 32) :
    WP isa (.block unfold) s fun s' => ∃ c : Bool, s'.cf = some c ∧
      VG.Proof.X448.X86_64.rv s' W + (s.gpr .r15).toNat * (1 + 2 ^ 224) = VG.Proof.X448.X86_64.rv s W + 2 ^ 448 * c.toNat ∧
      VG.Proof.X448.X86_64.Keeps (.rax :: W) s s' := by
  rw [unfold, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.shl32_ok s h) fun s1 ⟨h1, k1⟩ => ?_
  have r15 : s1.gpr .r15 = s.gpr .r15 := k1.1 _ (by decide)
  refine WP.mono (VG.Proof.X448.X86_64.sub_chain_ok W s1 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] (.reg .r15) _
    (s1.gpr .r15) _ (fun _ h => h) VG.Proof.X448.X86_64.W_nodup rfl (VG.Proof.X448.X86_64.stable_reg s1 (by decide)) (VG.Proof.X448.X86_64.fold_srcs s1))
    fun s' ⟨c, hc, he, hk⟩ => ⟨c, hc, ?_, (k1.mono (by decide)).trans (hk.mono (by decide))⟩
  have e1 : VG.Proof.X448.X86_64.rv s1 W = VG.Proof.X448.X86_64.rv s W := k1.rv_eq (by decide)
  rw [VG.Proof.X448.X86_64.W_lit, VG.Proof.X448.X86_64.len_W, e1] at he
  simp only [VG.Proof.X448.X86_64.wv, r15, VG.Proof.X448.X86_64.toNat_zero64] at he
  omega

open VG.Spec.X448 (P) in
/-- `fold2`: `r8–r14 + 2⁴⁴⁸ r15` modulo `p`, in seven words. -/
theorem fold2_ok (s : State) (h : (s.gpr .r15).toNat < 2 ^ 32) :
    WP isa (.block fold2) s fun s' =>
      VG.Proof.X448.X86_64.rv s' W % P = (VG.Proof.X448.X86_64.rv s W + 2 ^ 448 * (s.gpr .r15).toNat) % P ∧
      VG.Proof.X448.X86_64.Keeps (.rax :: .r15 :: W) s s' := by
  rw [fold2, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.fold_ok s h) fun s1 ⟨c1, hc1, e1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.carryOut_ok s1 hc1) fun s2 ⟨e2, k2⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86_64.fold_ok s2 (by rw [e2]; cases c1 <;> decide)) fun s3 ⟨c3, _, e3, k3⟩ => ?_
  refine ⟨?_, ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))⟩
  have w2 : VG.Proof.X448.X86_64.rv s2 W = VG.Proof.X448.X86_64.rv s1 W := k2.rv_eq (by decide)
  rw [w2, e2] at e3
  have l0 := VG.Proof.X448.X86_64.rv_lt s W; have l1 := VG.Proof.X448.X86_64.rv_lt s1 W; have l3 := VG.Proof.X448.X86_64.rv_lt s3 W
  rw [VG.Proof.X448.X86_64.len_W] at l0 l1 l3
  have hc := Bool.toNat_le c1
  have hc3 : c3.toNat = 0 := by
    rcases Nat.lt_or_ge c3.toNat 1 with h3 | h3
    · omega
    · rcases Nat.lt_or_ge c1.toNat 1 with h1 | h1 <;> omega
  rw [VG.Proof.X448.X86_64.fold448 (VG.Proof.X448.X86_64.rv s W) (s.gpr .r15).toNat]
  have h1 : VG.Proof.X448.X86_64.rv s W + (2 ^ 224 + 1) * (s.gpr .r15).toNat = VG.Proof.X448.X86_64.rv s1 W + 2 ^ 448 * c1.toNat := by
    omega
  rw [h1, VG.Proof.X448.X86_64.fold448 (VG.Proof.X448.X86_64.rv s1 W) c1.toNat]
  exact congrArg (· % P) (by omega)

/-- The arithmetic of a multiply-accumulate step: the product's halves, the
carry word `c` added to the low half, and the sum added to `t`, each carry
going into the high half, which never overflows. -/
theorem step_arith (a v c t : BitVec 64) :
    let p := a.toNat * v.toNat
    let lo : BitVec 64 := BitVec.ofNat 64 p
    let hi : BitVec 64 := BitVec.ofNat 64 (p / 2 ^ 64)
    let r := lo + c
    let d := hi + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ lo.toNat + c.toNat))).setWidth 64
    (t + r).toNat + 2 ^ 64 *
        (d + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ t.toNat + r.toNat))).setWidth 64).toNat =
      t.toNat + c.toNat + a.toNat * v.toNat := by
  intro p lo hi r d
  have ha := a.isLt; have hv := v.isLt; have hc := c.isLt; have ht := t.isLt
  have hp : p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hlo : lo.toNat = p % 2 ^ 64 := BitVec.toNat_ofNat _ _
  have hhi : hi.toNat = p / 2 ^ 64 := by
    simp only [hi, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hdiv : p / 2 ^ 64 ≤ 2 ^ 64 - 2 := by omega
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  simp only [r, d, BitVec.toNat_add, VG.Proof.X448.X86_64.toNat_ofBool, hz, Nat.add_zero, hlo, hhi] at *
  by_cases h1 : 2 ^ 64 ≤ p % 2 ^ 64 + c.toNat <;>
  simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
  [by_cases h2 : 2 ^ 64 ≤ t.toNat + (p % 2 ^ 64 + c.toNat) % 2 ^ 64;
    by_cases h2 : 2 ^ 64 ≤ t.toNat + (p % 2 ^ 64 + c.toNat) % 2 ^ 64] <;>
  simp only [h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- A multiply-accumulate step: `t:c = t + c + ai · v`, where `ld` loads `v`
into `rax`. -/
theorem mulStep_ok (s : State) {t c ai : Reg} {ld : Instr} {v : BitVec 64}
    (hld : exec ld s = some (s.setReg .rax v)) (ht : t ≠ .rax) (ht' : t ≠ .rdx) (hc : c ≠ .rax)
    (hc' : c ≠ .rdx) (ha : ai ≠ .rax) (htc : t ≠ c) :
    WP isa (.block (VG.Impl.X448.X86_64.mulStep t c ai ld)) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr c).toNat =
        (s.gpr t).toNat + (s.gpr c).toNat + (s.gpr ai).toNat * v.toNat ∧
      VG.Proof.X448.X86_64.Keeps [t, c, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [VG.Impl.X448.X86_64.mulStep, runBlock_cons, hld, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execMul,
    execAlu, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ha, hc, ht, htc, hc', ht',
    Ne.symm htc, Ne.symm ht', ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', VG.Proof.X448.X86_64.se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := VG.Proof.X448.X86_64.step_arith (s.gpr ai) v (s.gpr c) (s.gpr t)
    simp only at e
    rw [Nat.mul_comm (s.gpr ai).toNat] at e ⊢
    exact e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2, ite_false]

/-- `ld` loads `v` into `rax` in every state that agrees with `s` but on the
registers `X`. -/
def LdStable (X : List Reg) (s : State) (ld : Instr) (v : BitVec 64) : Prop :=
  ∀ t, (∀ r, r ∉ X → t.gpr r = s.gpr r) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr →
    exec ld t = some (t.setReg .rax v)

theorem ldStable_sc {X : List Reg} {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (hX : .rdi ∉ X)
    {d : Nat} (hd : d + 8 ≤ 8192) :
    VG.Proof.X448.X86_64.LdStable X s (.mov .rax (.mem (sc d))) (VG.Proof.X448.X86_64.word s.mem base d) := fun t hg hm _ hwr => by
  have ht : VG.Proof.X448.X86_64.Scr t base := ⟨(hg _ hX).trans hs.rdi, hwr ▸ hs.wr, hs.nowrap⟩
  simp only [exec, VG.Proof.X448.X86_64.readSrc_sc ht hd, hm, Option.map_some]

theorem ldStable_sc32 {X : List Reg} {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (hX : .rdi ∉ X)
    {d : Nat} (hd : d + 8 ≤ 8192) :
    VG.Proof.X448.X86_64.LdStable X s (.mov32 .rax (.mem (sc d))) ((s.mem.readW (VG.Proof.X448.X86_64.off base d) 32).setWidth 64) :=
  fun t hg hm _ hwr => by
    have ht : VG.Proof.X448.X86_64.Scr t base := ⟨(hg _ hX).trans hs.rdi, hwr ▸ hs.wr, hs.nowrap⟩
    simp only [exec, VG.X86_64.readSrc32, State.load32, VG.Proof.X448.X86_64.ea_sc, ht.rdi, ht.read (d := d) (n := 4) (by omega),
      ite_true, hm, Option.map_some, State.setReg32]

/-- Multiply-accumulate steps along `ts`: `ts + 2^(64n) rbp = ts + rbp + rcx · vs`. -/
theorem mulSteps_ok (X : List Reg) (s₀ : State) :
    ∀ (ts : List Reg) (lds : List Instr) (vs : List (BitVec 64)) (s : State),
      VG.Proof.X448.X86_64.Keeps X s₀ s → (∀ r ∈ .rax :: .rdx :: .rbp :: ts, r ∈ X) → .rcx ∉ X →
      (.rax :: .rdx :: .rbp :: .rcx :: ts).Nodup → ts.length = lds.length →
      List.Forall₂ (VG.Proof.X448.X86_64.LdStable X s₀) lds vs →
      WP isa (.block (mulSteps ts lds)) s fun s' =>
        VG.Proof.X448.X86_64.rv s' ts + 2 ^ (64 * ts.length) * (s'.gpr .rbp).toNat =
          VG.Proof.X448.X86_64.rv s ts + (s.gpr .rbp).toNat + (s.gpr .rcx).toNat * VG.Proof.X448.X86_64.wv vs ∧
        VG.Proof.X448.X86_64.Keeps (.rax :: .rdx :: .rbp :: ts) s s'
  | [], lds, _, s, _, _, _, _, hl, hf => by
    cases lds with
    | nil => cases hf; exact WP.block_nil ⟨by simp [VG.Proof.X448.X86_64.rv, VG.Proof.X448.X86_64.wv], Keeps.refl _ _⟩
    | cons => simp at hl
  | t :: ts, [], _, _, _, _, _, _, hl, _ => by simp at hl
  | t :: ts, ld :: lds, vs, s, hk, hX, hcX, hnd, hl, hf => by
    cases hf with
    | cons hv hf =>
    rename_i v vs
    have hat : t ≠ .rax := fun e => by subst e; simp at hnd
    have hdt : t ≠ .rdx := fun e => by subst e; simp at hnd
    have hbt : t ≠ .rbp := fun e => by subst e; simp at hnd
    have hct : t ≠ .rcx := fun e => by subst e; simp at hnd
    have htt : t ∉ ts := fun e => by simp [e] at hnd
    rw [mulSteps, WP.block_append_iff]
    have hld := hv s hk.1 hk.2.1 hk.2.2.1 hk.2.2.2
    refine WP.mono (VG.Proof.X448.X86_64.mulStep_ok s hld hat hdt (by decide) (by decide)
      (by decide) hbt) fun s1 ⟨e1, k1⟩ => ?_
    have hXs : ∀ r ∈ [t, .rbp, .rax, .rdx], r ∈ X := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hX _ (by simp)
    have hk1 : VG.Proof.X448.X86_64.Keeps X s₀ s1 := hk.trans (k1.mono hXs)
    refine WP.mono (VG.Proof.X448.X86_64.mulSteps_ok X s₀ ts lds vs s1 hk1
      (fun r hr => hX r (by simp only [List.mem_cons] at hr ⊢; grind)) hcX
      (by simp only [List.nodup_cons, List.mem_cons, not_or] at hnd ⊢; grind) (by simpa using hl) hf)
      fun s' ⟨e', k'⟩ => ⟨?_, ?_⟩
    · have c1 : s1.gpr .rcx = s.gpr .rcx := k1.1 _ (by simp [Ne.symm hct])
      have g1 : s'.gpr t = s1.gpr t := k'.1 _ (by simp [hat, hdt, hbt, htt])
      have r1 : VG.Proof.X448.X86_64.rv s1 ts = VG.Proof.X448.X86_64.rv s ts := k1.rv_eq fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        refine ⟨fun e => htt (e ▸ hr), fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> subst e <;>
          simp at hnd <;> simp_all
      rw [c1, r1] at e'
      rw [VG.Proof.X448.X86_64.rv, VG.Proof.X448.X86_64.rv, g1, List.length_cons, VG.Proof.X448.X86_64.pow64_succ, VG.Proof.X448.X86_64.wv, Nat.mul_assoc]
      generalize 2 ^ (64 * ts.length) * (s'.gpr .rbp).toNat = Y at e' ⊢
      rw [Nat.mul_add, Nat.mul_left_comm]
      generalize (s.gpr .rcx).toNat * VG.Proof.X448.X86_64.wv vs = Z at e' ⊢
      omega
    · refine ⟨fun r hr => ?_, k'.2.1.trans k1.2.1, k'.2.2.1.trans k1.2.2.1, k'.2.2.2.trans k1.2.2.2⟩
      simp only [List.mem_cons, not_or] at hr
      rw [k'.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.2]),
        k1.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1])]

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Comba`. -/
section

/-!
# X448 on x86-64: products by columns

A product's term (`term_ok`): `x · y` (twice if doubled) added to a
three-word accumulator; a column's terms (`terms_ok`), by induction on them;
and the fourteen columns (`columns_ok`), by induction on the columns, each
storing its low word at `ACC` and passing the rest of its accumulator on, in
the registers `accR` rotated. Then the columns of `mul` and `sqr` sum to the
product and the square (`mulCols_sum`, `sqrCols_sum`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

/-- The registers a product's columns change. -/
def colX : List Reg := [.rax, .rdx, .r15, .rcx, .rbp]

/-- `x · y` in two words (`mul`). -/
theorem mul_halves (a b : BitVec 64) :
    (BitVec.ofNat 64 (a.toNat * b.toNat)).toNat +
        2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat = a.toNat * b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hp : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by omega)]
  omega

/-- `rax = x`, then `rdx:rax = x · y`. -/
theorem mov_mul_ok (s : State) {x : Src} {y : Reg} {vx : BitVec 64} (hx : VG.X86_64.readSrc s x = some vx)
    (hy : y ≠ .rax) :
    WP isa (.block [.mov .rax x, .mul y]) s fun s' =>
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat = vx.toNat * (s.gpr y).toNat ∧
      VG.Proof.X448.X86_64.Keeps [.rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hx, Option.map_some, execMul,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hy, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact VG.Proof.X448.X86_64.mul_halves vx (s.gpr y)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.2, RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setFlags,
      RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- `r0–r2 += rdx:rax`. -/
theorem acc_ok (s : State) {r0 r1 r2 : Reg} (hd : [r0, r1, r2, .rax, .rdx].Nodup)
    (hb : VG.Proof.X448.X86_64.rv s [r0, r1, r2] + ((s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rdx).toNat) < 2 ^ 192) :
    WP isa (.block [.alu .add r0 (.reg .rax), .alu .adc r1 (.reg .rdx), .alu .adc r2 (.imm 0)]) s
      fun s' => VG.Proof.X448.X86_64.rv s' [r0, r1, r2] =
          VG.Proof.X448.X86_64.rv s [r0, r1, r2] + ((s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rdx).toNat) ∧
        VG.Proof.X448.X86_64.Keeps [r0, r1, r2] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h0a, h0d⟩, ⟨h12, h1a, h1d⟩, ⟨h2a, h2d⟩, -⟩ := hd
  refine WP.mono (VG.Proof.X448.X86_64.add_chain_ok [r0, r1, r2] s r0 [r1, r2] (.reg .rax) [.reg .rdx, .imm 0]
    (s.gpr .rax) [s.gpr .rdx, 0] (fun _ h => h) (by simp [h01, h02, h12]) rfl
    (VG.Proof.X448.X86_64.stable_reg s (by simp [Ne.symm h0a, Ne.symm h1a, Ne.symm h2a]))
    (.cons (VG.Proof.X448.X86_64.stable_reg s (by simp [Ne.symm h0d, Ne.symm h1d, Ne.symm h2d]))
      (.cons (VG.Proof.X448.X86_64.stable_imm0 _ _) .nil))) fun s' ⟨c, _, he, hk⟩ => ⟨?_, hk⟩
  have hl : 64 * [r0, r1, r2].length = 192 := rfl
  rw [hl] at he
  simp only [VG.Proof.X448.X86_64.wv, VG.Proof.X448.X86_64.toNat_zero64] at he
  have := Bool.toNat_le c
  rcases Nat.lt_or_ge c.toNat 1 with h | h <;> omega

/-- A term's weight: 2 if it is doubled. -/
def termK (t : Term) : Nat := if t.dbl then 2 else 1

/-- A term's value. -/
def tv (xv yv : Nat → Nat) (t : Term) : Nat := VG.Proof.X448.X86_64.termK t * (xv t.i * yv t.j)

/-- `term`: `r0–r2 += x · y`, twice if `dbl`. -/
theorem term_ok (s : State) {x : Src} {y r0 r1 r2 : Reg} {vx : BitVec 64} (dbl : Bool)
    (hx : VG.X86_64.readSrc s x = some vx) (hy : y ≠ .rax) (hd : [r0, r1, r2, .rax, .rdx].Nodup)
    (hb : VG.Proof.X448.X86_64.rv s [r0, r1, r2] + (if dbl then 2 else 1) * (vx.toNat * (s.gpr y).toNat) < 2 ^ 192) :
    WP isa (.block (term x y r0 r1 r2 dbl)) s fun s' =>
      VG.Proof.X448.X86_64.rv s' [r0, r1, r2] = VG.Proof.X448.X86_64.rv s [r0, r1, r2] + (if dbl then 2 else 1) * (vx.toNat * (s.gpr y).toNat) ∧
      VG.Proof.X448.X86_64.Keeps [.rax, .rdx, r0, r1, r2] s s' := by
  have hd' := hd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd'
  obtain ⟨⟨_, _, h0a, h0d⟩, ⟨_, h1a, h1d⟩, ⟨h2a, h2d⟩, -⟩ := hd'
  rw [term, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.mov_mul_ok s hx hy) fun s1 ⟨e1, k1⟩ => ?_
  have r1 : VG.Proof.X448.X86_64.rv s1 [r0, r1, r2] = VG.Proof.X448.X86_64.rv s [r0, r1, r2] := k1.rv_eq (by simp [h0a, h1a, h2a, h0d, h1d, h2d])
  have hp := Nat.zero_le (vx.toNat * (s.gpr y).toNat)
  cases dbl with
  | false =>
    simp only [Bool.false_eq_true, ite_false, List.nil_append, Nat.one_mul] at hb ⊢
    refine WP.mono (VG.Proof.X448.X86_64.acc_ok s1 hd (by omega)) fun s2 ⟨e2, k2⟩ => ⟨by omega, ?_⟩
    exact (k1.mono (by simp)).trans (k2.mono (by simp))
  | true =>
    simp only [ite_true] at hb ⊢
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.X448.X86_64.acc_ok s1 hd (by omega)) fun s2 ⟨e2, k2⟩ => ?_
    have a2 : s2.gpr .rax = s1.gpr .rax := k2.1 _ (by simp [Ne.symm h0a, Ne.symm h1a, Ne.symm h2a])
    have d2 : s2.gpr .rdx = s1.gpr .rdx := k2.1 _ (by simp [Ne.symm h0d, Ne.symm h1d, Ne.symm h2d])
    refine WP.mono (VG.Proof.X448.X86_64.acc_ok s2 hd (by rw [a2, d2]; omega)) fun s3 ⟨e3, k3⟩ => ⟨?_, ?_⟩
    · rw [a2, d2] at e3; omega
    · exact ((k1.mono (by simp)).trans (k2.mono (by simp))).trans (k3.mono (by simp))

/-- The sum of a column's terms. -/
def colSum (xv yv : Nat → Nat) (ts : List Term) : Nat := (ts.map (VG.Proof.X448.X86_64.tv xv yv)).sum

theorem colSum_cons (xv yv : Nat → Nat) (t : Term) (ts : List Term) :
    VG.Proof.X448.X86_64.colSum xv yv (t :: ts) = VG.Proof.X448.X86_64.termK t * (xv t.i * yv t.j) + VG.Proof.X448.X86_64.colSum xv yv ts := by
  simp [VG.Proof.X448.X86_64.colSum, VG.Proof.X448.X86_64.tv]

/-- A column's terms, by induction on them. -/
theorem terms_ok (x : Nat → Src) (y : Nat → Reg) (xv : Nat → BitVec 64) {r0 r1 r2 : Reg}
    (hd : [r0, r1, r2, .rax, .rdx].Nodup) :
    ∀ (ts : List Term) (s : State),
      (∀ t ∈ ts, VG.Proof.X448.X86_64.Stable [.rax, .rdx, r0, r1, r2] s (x t.i) (xv t.i)) →
      (∀ t ∈ ts, y t.j ∉ [.rax, .rdx, r0, r1, r2]) →
      VG.Proof.X448.X86_64.rv s [r0, r1, r2] + VG.Proof.X448.X86_64.colSum (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat) ts < 2 ^ 192 →
      WP isa (.block (ts.flatMap fun t => term (x t.i) (y t.j) r0 r1 r2 t.dbl)) s fun s' =>
        VG.Proof.X448.X86_64.rv s' [r0, r1, r2] = VG.Proof.X448.X86_64.rv s [r0, r1, r2] +
          VG.Proof.X448.X86_64.colSum (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat) ts ∧
        VG.Proof.X448.X86_64.Keeps [.rax, .rdx, r0, r1, r2] s s'
  | [], s, _, _, _ => WP.block_nil ⟨by simp [VG.Proof.X448.X86_64.colSum], Keeps.refl _ _⟩
  | t :: ts, s, hx, hy, hb => by
    rw [List.flatMap_cons, WP.block_append_iff]
    have hyt := hy t List.mem_cons_self
    rw [VG.Proof.X448.X86_64.colSum_cons] at hb
    simp only [VG.Proof.X448.X86_64.termK] at hb
    refine WP.mono (VG.Proof.X448.X86_64.term_ok s t.dbl (hx t List.mem_cons_self).read
      (fun e => hyt (by simp [e])) hd (by omega)) fun s1 ⟨e1, k1⟩ => ?_
    have gy : ∀ t' ∈ t :: ts, s1.gpr (y t'.j) = s.gpr (y t'.j) := fun t' ht' => k1.1 _ (hy t' ht')
    have cs : VG.Proof.X448.X86_64.colSum (fun i => (xv i).toNat) (fun j => (s1.gpr (y j)).toNat) ts =
        VG.Proof.X448.X86_64.colSum (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat) ts := by
      simp only [VG.Proof.X448.X86_64.colSum]
      exact congrArg List.sum (List.map_congr_left fun t' ht' => by
        simp only [VG.Proof.X448.X86_64.tv, gy t' (List.mem_cons_of_mem _ ht')])
    refine WP.mono (VG.Proof.X448.X86_64.terms_ok x y xv hd ts s1
      (fun t' ht' => (hx t' (List.mem_cons_of_mem _ ht')).of_keeps k1)
      (fun t' ht' => hy t' (List.mem_cons_of_mem _ ht')) (by rw [cs, e1]; omega))
      fun s2 ⟨e2, k2⟩ => ⟨?_, k1.trans k2⟩
    rw [e2, cs, e1, VG.Proof.X448.X86_64.colSum_cons]
    simp only [VG.Proof.X448.X86_64.termK]
    omega

/-! ## Columns -/

/-- The accumulator of column `k`. -/
def acc (k : Nat) : List Reg := [accR k 0, accR k 1, accR k 2]

theorem accR_mod (k n : Nat) : accR k n = [Reg.r15, .rcx, .rbp].getD ((k + n) % 3) .r15 := rfl

theorem acc_succ (k : Nat) : VG.Proof.X448.X86_64.acc (k + 1) = [accR k 1, accR k 2, accR k 0] := by
  simp only [VG.Proof.X448.X86_64.acc, VG.Proof.X448.X86_64.accR_mod]
  refine List.cons_eq_cons.mpr ⟨by rw [Nat.add_right_comm], List.cons_eq_cons.mpr
    ⟨by rw [Nat.add_assoc], List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
  rw [show k + 1 + 2 = k + 3 by omega, Nat.add_mod_right, Nat.add_zero]

theorem acc_cases (k : Nat) :
    VG.Proof.X448.X86_64.acc k = [.r15, .rcx, .rbp] ∨ VG.Proof.X448.X86_64.acc k = [.rcx, .rbp, .r15] ∨ VG.Proof.X448.X86_64.acc k = [.rbp, .r15, .rcx] := by
  simp only [VG.Proof.X448.X86_64.acc, VG.Proof.X448.X86_64.accR_mod]
  have h := Nat.mod_lt k (show 0 < 3 by decide)
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h <;>
  simp only [Nat.add_mod k, h] <;> simp

theorem acc_nodup (k : Nat) : [accR k 0, accR k 1, accR k 2, .rax, .rdx].Nodup := by
  have := VG.Proof.X448.X86_64.acc_cases k
  simp only [VG.Proof.X448.X86_64.acc, List.cons.injEq, and_true] at this
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> decide

theorem acc_colX (k : Nat) : ∀ r ∈ [Reg.rax, .rdx, accR k 0, accR k 1, accR k 2], r ∈ VG.Proof.X448.X86_64.colX := by
  have := VG.Proof.X448.X86_64.acc_cases k
  simp only [VG.Proof.X448.X86_64.acc, List.cons.injEq, and_true] at this
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> decide

theorem accR_colX (k n : Nat) (hn : n < 3) : accR k n ∈ VG.Proof.X448.X86_64.colX := by
  have := VG.Proof.X448.X86_64.acc_colX k
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> exact this _ (by simp)

theorem rdi_colX : Reg.rdi ∉ VG.Proof.X448.X86_64.colX := by decide

/-- A column: its terms, its low word stored at `ACC + 8k`, and the rest of
the accumulator passed on. -/
theorem column_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (x : Nat → Src) (y : Nat → Reg)
    (xv : Nat → BitVec 64) (ts : List Term) (k : Nat) (hk : ACC + 8 * k + 8 ≤ 8192)
    (hx : ∀ t ∈ ts, VG.Proof.X448.X86_64.Stable VG.Proof.X448.X86_64.colX s (x t.i) (xv t.i)) (hy : ∀ t ∈ ts, y t.j ∉ VG.Proof.X448.X86_64.colX)
    (hb : VG.Proof.X448.X86_64.rv s (VG.Proof.X448.X86_64.acc k) + VG.Proof.X448.X86_64.colSum (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat) ts <
      2 ^ 192) :
    WP isa (.block (column x y ts k)) s fun s' =>
      (VG.Proof.X448.X86_64.word s'.mem base (ACC + 8 * k)).toNat + 2 ^ 64 * VG.Proof.X448.X86_64.rv s' (VG.Proof.X448.X86_64.acc (k + 1)) =
        VG.Proof.X448.X86_64.rv s (VG.Proof.X448.X86_64.acc k) + VG.Proof.X448.X86_64.colSum (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat) ts ∧
      (∀ r, r ∉ VG.Proof.X448.X86_64.colX → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X448.X86_64.Outside base (ACC + 8 * k) 8 s.mem s'.mem := by
  have hsub := VG.Proof.X448.X86_64.acc_colX k
  rw [column, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.terms_ok x y xv (VG.Proof.X448.X86_64.acc_nodup k) ts s (fun t ht => (hx t ht).mono hsub)
    (fun t ht h => hy t ht (hsub _ h)) hb) fun s1 ⟨e1, k1⟩ => ?_
  have hs1 : VG.Proof.X448.X86_64.Scr s1 base := hs.of_keeps k1 (fun h => VG.Proof.X448.X86_64.rdi_colX (hsub _ h))
  have hw := hs1.write (d := ACC + 8 * k) (n := 8) hk
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X448.X86_64.ea_sc, hs1.rdi, State.store64, hw,
    ite_true, VG.X86_64.readSrc32, Option.map_some, State.setReg32, Option.some.injEq,
    exists_eq_left']
  have hn := VG.Proof.X448.X86_64.acc_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨⟨h01, h02, -, -⟩, ⟨h12, -, -⟩, -, -⟩ := hn
  refine ⟨?_, fun r hr => ?_, k1.2.2.1, k1.2.2.2, ?_⟩
  · rw [VG.Proof.X448.X86_64.acc_succ]
    simp only [VG.Proof.X448.X86_64.rv, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm h01),
      RegUpd.gpr_setReg_of_ne _ _ (Ne.symm h02)]
    rw [RegUpd.mem_setReg]
    simp only [VG.Proof.X448.X86_64.word_writeW_self]
    simp only [VG.Proof.X448.X86_64.acc, VG.Proof.X448.X86_64.rv] at e1 ⊢
    have z : (BitVec.setWidth 64 (0 : BitVec 32)).toNat = 0 := rfl
    rw [z]
    omega
  · have hr0 : r ≠ accR k 0 := fun e => hr (e ▸ VG.Proof.X448.X86_64.accR_colX k 0 (by decide))
    rw [RegUpd.gpr_setReg_of_ne _ _ hr0]
    exact k1.1 r (fun h => hr (hsub _ h))
  · rw [← k1.2.1]; exact VG.Proof.X448.X86_64.writeW_outside _ _ _ (by omega)

theorem mv_succ_last (m : Mem) (base : Addr) :
    ∀ (o n : Nat), VG.Proof.X448.X86_64.mv m base o (n + 1) = VG.Proof.X448.X86_64.mv m base o n + 2 ^ (64 * n) * (VG.Proof.X448.X86_64.word m base (o + 8 * n)).toNat
  | o, 0 => by simp [VG.Proof.X448.X86_64.mv]
  | o, n + 1 => by
    rw [VG.Proof.X448.X86_64.mv, VG.Proof.X448.X86_64.mv_succ_last m base (o + 8) n, VG.Proof.X448.X86_64.mv, VG.Proof.X448.X86_64.pow64_succ,
      show o + 8 + 8 * n = o + 8 * (n + 1) by omega]
    generalize 2 ^ (64 * n) = Q
    grind

/-- The columns' values: `Σ_{m<n} 2^(64m) colSum (cols (k + m))`, in Horner
form, whose only power is `2⁶⁴`. -/
def colsVal (xv yv : Nat → Nat) (cols : Nat → List Term) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => VG.Proof.X448.X86_64.colSum xv yv (cols k) + 2 ^ 64 * VG.Proof.X448.X86_64.colsVal xv yv cols (k + 1) n

theorem colsVal_succ_last (xv yv : Nat → Nat) (cols : Nat → List Term) :
    ∀ k n, VG.Proof.X448.X86_64.colsVal xv yv cols k (n + 1) =
      VG.Proof.X448.X86_64.colsVal xv yv cols k n + 2 ^ (64 * n) * VG.Proof.X448.X86_64.colSum xv yv (cols (k + n))
  | k, 0 => by simp [VG.Proof.X448.X86_64.colsVal]
  | k, n + 1 => by
    rw [VG.Proof.X448.X86_64.colsVal, VG.Proof.X448.X86_64.colsVal_succ_last xv yv cols (k + 1) n, VG.Proof.X448.X86_64.colsVal, VG.Proof.X448.X86_64.pow64_succ,
      show k + 1 + n = k + (n + 1) by omega]
    generalize 2 ^ (64 * n) = Q
    grind

theorem colSum_le (xv yv : Nat → Nat) :
    ∀ ts : List Term, (∀ t ∈ ts, xv t.i < 2 ^ 64 ∧ yv t.j < 2 ^ 64) →
      VG.Proof.X448.X86_64.colSum xv yv ts ≤ (ts.map VG.Proof.X448.X86_64.termK).sum * ((2 ^ 64 - 1) * (2 ^ 64 - 1))
  | [], _ => by simp [VG.Proof.X448.X86_64.colSum]
  | t :: ts, h => by
    rw [VG.Proof.X448.X86_64.colSum_cons, List.map_cons, List.sum_cons, Nat.add_mul]
    have h1 := h t List.mem_cons_self
    have hp : xv t.i * yv t.j ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
    have := Nat.mul_le_mul_left (VG.Proof.X448.X86_64.termK t) hp
    have := VG.Proof.X448.X86_64.colSum_le xv yv ts fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    omega

theorem colSum_congr (xv yv yv' : Nat → Nat) (ts : List Term) (h : ∀ t ∈ ts, yv t.j = yv' t.j) :
    VG.Proof.X448.X86_64.colSum xv yv ts = VG.Proof.X448.X86_64.colSum xv yv' ts := by
  simp only [VG.Proof.X448.X86_64.colSum]
  exact congrArg List.sum (List.map_congr_left fun t ht => by simp only [VG.Proof.X448.X86_64.tv, h t ht])

/-- The first `n` columns of a product. -/
theorem columns_ok {s₀ : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s₀ base) (x : Nat → Src) (y : Nat → Reg)
    (xv : Nat → BitVec 64) (cols : Nat → List Term)
    (hx : ∀ s, (∀ r, r ∉ VG.Proof.X448.X86_64.colX → s.gpr r = s₀.gpr r) → s.rd = s₀.rd → s.wr = s₀.wr →
      VG.Proof.X448.X86_64.Outside base ACC 112 s₀.mem s.mem → ∀ i < 7, VG.Proof.X448.X86_64.Stable VG.Proof.X448.X86_64.colX s (x i) (xv i))
    (hy : ∀ j < 7, y j ∉ VG.Proof.X448.X86_64.colX) (hc : ∀ k < 14, ∀ t ∈ cols k, t.i < 7 ∧ t.j < 7)
    (hw : ∀ k < 14, ((cols k).map VG.Proof.X448.X86_64.termK).sum ≤ 7) (h0 : VG.Proof.X448.X86_64.rv s₀ (VG.Proof.X448.X86_64.acc 0) = 0) :
    ∀ n ≤ 14, WP isa (.block ((List.range n).flatMap fun k => column x y (cols k) k)) s₀ fun s =>
      (∀ r, r ∉ VG.Proof.X448.X86_64.colX → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧
      VG.Proof.X448.X86_64.Outside base ACC (8 * n) s₀.mem s.mem ∧
      VG.Proof.X448.X86_64.mv s.mem base ACC n + 2 ^ (64 * n) * VG.Proof.X448.X86_64.rv s (VG.Proof.X448.X86_64.acc n) =
        VG.Proof.X448.X86_64.colsVal (fun i => (xv i).toNat) (fun j => (s₀.gpr (y j)).toNat) cols 0 n ∧
      VG.Proof.X448.X86_64.rv s (VG.Proof.X448.X86_64.acc n) < 2 ^ 128
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, by simp [VG.Proof.X448.X86_64.mv, VG.Proof.X448.X86_64.colsVal, h0],
      by rw [h0]; decide⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.X448.X86_64.columns_ok hs x y xv cols hx hy hc hw h0 n (by omega))
      fun s ⟨g, rd, wr, o, e, b⟩ => ?_
    have hsS : VG.Proof.X448.X86_64.Scr s base := ⟨(g _ VG.Proof.X448.X86_64.rdi_colX).trans hs.rdi, wr ▸ hs.wr, hs.nowrap⟩
    have hxs := hx s g rd wr (o.mono (by omega) (by omega))
    have hcn := hc n (by omega)
    have gy : ∀ t ∈ cols n, (s.gpr (y t.j)).toNat = (s₀.gpr (y t.j)).toNat :=
      fun t ht => by rw [g _ (hy _ (hcn t ht).2)]
    have cs := VG.Proof.X448.X86_64.colSum_congr (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat)
      (fun j => (s₀.gpr (y j)).toNat) (cols n) gy
    have cb := VG.Proof.X448.X86_64.colSum_le (fun i => (xv i).toNat) (fun j => (s.gpr (y j)).toNat) (cols n)
      fun t _ => ⟨(xv t.i).isLt, (s.gpr (y t.j)).isLt⟩
    have hwn := Nat.mul_le_mul_right ((2 ^ 64 - 1) * (2 ^ 64 - 1)) (hw n (by omega))
    rw [List.flatMap_singleton]
    refine WP.mono (VG.Proof.X448.X86_64.column_ok hsS x y xv (cols n) n (by simp only [ACC]; omega)
      (fun t ht => hxs t.i (hcn t ht).1) (fun t ht => hy _ (hcn t ht).2) (by omega))
      fun s' ⟨e', g', rd', wr', o'⟩ => ?_
    refine ⟨fun r hr => (g' r hr).trans (g r hr), rd'.trans rd, wr'.trans wr,
      (o.mono (Nat.le_refl _) (by omega)).trans (o'.mono (by omega) (by omega)), ?_, ?_⟩
    · rw [VG.Proof.X448.X86_64.mv_succ_last, o'.mv (d := ACC) (k := n) (by omega) (by simp only [ACC]; omega),
        VG.Proof.X448.X86_64.colsVal_succ_last, Nat.zero_add, VG.Proof.X448.X86_64.pow64_succ, ← cs]
      rw [cs] at e'
      generalize 2 ^ (64 * n) = Q at e ⊢
      calc VG.Proof.X448.X86_64.mv s.mem base ACC n + Q * (VG.Proof.X448.X86_64.word s'.mem base (ACC + 8 * n)).toNat +
            2 ^ 64 * Q * VG.Proof.X448.X86_64.rv s' (VG.Proof.X448.X86_64.acc (n + 1))
          = VG.Proof.X448.X86_64.mv s.mem base ACC n + Q * ((VG.Proof.X448.X86_64.word s'.mem base (ACC + 8 * n)).toNat +
              2 ^ 64 * VG.Proof.X448.X86_64.rv s' (VG.Proof.X448.X86_64.acc (n + 1))) := by grind
        _ = VG.Proof.X448.X86_64.mv s.mem base ACC n + Q * VG.Proof.X448.X86_64.rv s (VG.Proof.X448.X86_64.acc n) + Q * VG.Proof.X448.X86_64.colSum (fun i => (xv i).toNat)
              (fun j => (s₀.gpr (y j)).toNat) (cols n) := by rw [e']; grind
        _ = _ := by rw [e, cs]
    · omega

/-! ## The columns of `mul` and `sqr` -/

/-- Seven words' value, in Horner form. -/
def val7 (f : Nat → Nat) : Nat :=
  f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * (f 3 + 2 ^ 64 * (f 4 + 2 ^ 64 * (f 5 +
    2 ^ 64 * f 6)))))

theorem mulCol_hc : ∀ k < 14, ∀ t ∈ mulCol k, t.i < 7 ∧ t.j < 7 := by decide
theorem mulCol_hw : ∀ k < 14, ((mulCol k).map VG.Proof.X448.X86_64.termK).sum ≤ 7 := by decide
theorem sqrCol_hc : ∀ k < 14, ∀ t ∈ sqrCol k, t.i < 7 ∧ t.j < 7 := by decide
theorem sqrCol_hw : ∀ k < 14, ((sqrCol k).map VG.Proof.X448.X86_64.termK).sum ≤ 7 := by decide

theorem range7 : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := rfl

theorem mulCols_sum (xv yv : Nat → Nat) : VG.Proof.X448.X86_64.colsVal xv yv mulCol 0 14 = VG.Proof.X448.X86_64.val7 xv * VG.Proof.X448.X86_64.val7 yv := by
  simp (config := {decide := true}) only [VG.Proof.X448.X86_64.colsVal, VG.Proof.X448.X86_64.colSum, mulCol, VG.Proof.X448.X86_64.range7, List.filter_cons,
    List.filter_nil, ite_true, ite_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    VG.Proof.X448.X86_64.tv, VG.Proof.X448.X86_64.termK, VG.Proof.X448.X86_64.val7, Nat.reduceAdd, Nat.reduceSub, Nat.one_mul]
  generalize 2 ^ 64 = B
  grind

theorem sqrCols_sum (xv : Nat → Nat) : VG.Proof.X448.X86_64.colsVal xv xv sqrCol 0 14 = VG.Proof.X448.X86_64.val7 xv * VG.Proof.X448.X86_64.val7 xv := by
  simp (config := {decide := true}) only [VG.Proof.X448.X86_64.colsVal, VG.Proof.X448.X86_64.colSum, sqrCol, VG.Proof.X448.X86_64.range7, List.filter_cons,
    List.filter_nil, ite_true, ite_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    VG.Proof.X448.X86_64.tv, VG.Proof.X448.X86_64.termK, VG.Proof.X448.X86_64.val7, Nat.reduceAdd, Nat.reduceSub, Nat.one_mul, List.append_nil, List.cons_append,
    List.nil_append, Nat.reduceDiv]
  generalize 2 ^ 64 = B
  grind

theorem mv7 (m : Mem) (base : Addr) (o : Nat) :
    VG.Proof.X448.X86_64.mv m base o 7 = VG.Proof.X448.X86_64.val7 fun i => (VG.Proof.X448.X86_64.word m base (o + 8 * i)).toNat := by
  simp only [VG.Proof.X448.X86_64.mv, VG.Proof.X448.X86_64.val7, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero, Nat.mul_zero]

theorem rvW (s : State) : VG.Proof.X448.X86_64.rv s W = VG.Proof.X448.X86_64.val7 fun i => (s.gpr (w i)).toNat := by
  simp only [VG.Proof.X448.X86_64.rv, W, VG.Proof.X448.X86_64.val7, w, List.getD_cons_succ, List.getD_cons_zero, Nat.mul_zero, Nat.add_zero]

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Reduce`. -/
section

/-!
# X448 on x86-64: the reduction of a product

`reduce o` takes the fourteen words `L + 2⁴⁴⁸ H` of a product at `ACC` to a
seven-word number congruent to it modulo `p` at `[o]`: `L + H`, plus
`H - H mod 2²²⁴`, plus `rot(H)` (`H` rotated by 224 bits), whose top word is
folded twice (`fold2`). `reduce_arith` is the congruence, as arithmetic.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64
open VG.Spec.X448 (P)

/-- `2⁴⁴⁸ H ≡ H + (H - H mod 2²²⁴) + rot(H)`, for `H`'s words `h₀, …, h₆`
and `h₃ = lo + 2³² hi` (`rax = h₃ - lo`). -/
theorem reduce_arith (L h0 h1 h2 h3 h4 h5 h6 lo hi rax : Nat) (hlo : lo + 2 ^ 32 * hi = h3)
    (hrax : rax + lo = h3) :
    (L + 2 ^ 448 * (h0 + 2 ^ 64 * (h1 + 2 ^ 64 * (h2 + 2 ^ 64 * (h3 + 2 ^ 64 * (h4 + 2 ^ 64 *
      (h5 + 2 ^ 64 * h6))))))) % P =
    (L + (h0 + 2 ^ 64 * (h1 + 2 ^ 64 * (h2 + 2 ^ 64 * (h3 + 2 ^ 64 * (h4 + 2 ^ 64 *
      (h5 + 2 ^ 64 * h6)))))) + 2 ^ 192 * rax + 2 ^ 256 * h4 + 2 ^ 320 * h5 + 2 ^ 384 * h6 + hi +
      2 ^ 32 * (h4 + 2 ^ 64 * (h5 + 2 ^ 64 * (h6 + 2 ^ 64 * (h0 + 2 ^ 64 * (h1 + 2 ^ 64 *
        (h2 + 2 ^ 64 * lo))))))) % P := by
  obtain ⟨H, hH⟩ : ∃ H, h0 + 2 ^ 64 * (h1 + 2 ^ 64 * (h2 + 2 ^ 64 * (h3 + 2 ^ 64 * (h4 + 2 ^ 64 *
      (h5 + 2 ^ 64 * h6))))) = H := ⟨_, rfl⟩
  rw [hH]
  have hP := VG.Proof.X448.X86_64.P_eq
  have e1 : 2 ^ 448 * H = P * H + (2 ^ 224 + 1) * H := by rw [hP, Nat.add_mul]
  obtain ⟨K, hK⟩ : ∃ K, hi + 2 ^ 32 * h4 + 2 ^ 96 * h5 + 2 ^ 160 * h6 = K := ⟨_, rfl⟩
  have e2 : 2 ^ 448 * K = P * K + (2 ^ 224 + 1) * K := by rw [hP, Nat.add_mul]
  have e : L + 2 ^ 448 * H = (L + H + 2 ^ 192 * rax + 2 ^ 256 * h4 + 2 ^ 320 * h5 +
      2 ^ 384 * h6 + hi + 2 ^ 32 * (h4 + 2 ^ 64 * (h5 + 2 ^ 64 * (h6 + 2 ^ 64 * (h0 + 2 ^ 64 *
        (h1 + 2 ^ 64 * (h2 + 2 ^ 64 * lo))))))) + P * (H + K) := by
    rw [Nat.mul_add P H K]
    generalize P * H = PH at e1 ⊢
    generalize P * K = PK at e2 ⊢
    clear hP
    omega
  rw [e, Nat.add_mul_mod_self_left]

/-! ## The blocks of `reduce` -/

theorem mov32_ok (s : State) (r : Reg) (v : BitVec 32) :
    WP isa (.block [.mov32 r (.imm v)]) s fun s' => s'.gpr r = v.setWidth 64 ∧ VG.Proof.X448.X86_64.Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r' hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [RegUpd.gpr_setReg_of_ne _ _ hr]

theorem toNat_setWidth32 (x : BitVec 64) : ((x.setWidth 32).setWidth 64).toNat = x.toNat % 2 ^ 32 := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))

theorem toNat_setWidth_32_64 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (by decide))

/-- `r = [d]`, split into its low half `t` and the rest `r`. -/
theorem splitLo_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {d : Nat} (hd : d + 8 ≤ 8192)
    {r t : Reg} (hrt : r ≠ t) :
    WP isa (.block [.mov r (.mem (sc d)), .mov32 t (.reg r), .alu .sub r (.reg t)]) s fun s' =>
      (s'.gpr t).toNat = (VG.Proof.X448.X86_64.word s.mem base d).toNat % 2 ^ 32 ∧
      (s'.gpr r).toNat + (s'.gpr t).toNat = (VG.Proof.X448.X86_64.word s.mem base d).toNat ∧
      VG.Proof.X448.X86_64.Keeps [r, t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    VG.Proof.X448.X86_64.load_sc hs hd, Option.map_some, Option.bind_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ hrt, State.setReg32, Option.some.injEq, exists_eq_left']
  have hx := VG.Proof.X448.X86_64.toNat_setWidth32 (VG.Proof.X448.X86_64.word s.mem base d)
  refine ⟨?_, ?_, fun r' hr => ?_, rfl, rfl, rfl⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hrt), RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_self, hx]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hrt), RegUpd.gpr_arithFlags,
      RegUpd.gpr_setReg_self, hx]
    have := VG.Proof.X448.X86_64.sub_borrow (VG.Proof.X448.X86_64.word s.mem base d) ((VG.Proof.X448.X86_64.word s.mem base d).setWidth 32 |>.setWidth 64)
    rw [hx] at this
    have : ¬(VG.Proof.X448.X86_64.word s.mem base d).toNat < (VG.Proof.X448.X86_64.word s.mem base d).toNat % 2 ^ 32 :=
      Nat.not_lt.mpr (Nat.mod_le _ _)
    simp only [this, decide_false, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at *
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr.2,
      RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- `h₃` split into its low half `rdx` and the rest `rax`. -/
theorem splitH_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) :
    WP isa (.block [.mov .rax (.mem (sc (h 10))), .mov32 .rdx (.reg .rax),
      .alu .sub .rax (.reg .rdx)]) s fun s' =>
      (s'.gpr .rdx).toNat = (VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat % 2 ^ 32 ∧
      (s'.gpr .rax).toNat + (s'.gpr .rdx).toNat = (VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat ∧
      VG.Proof.X448.X86_64.Keeps [.rax, .rdx] s s' :=
  VG.Proof.X448.X86_64.splitLo_ok hs (by simp only [h, ACC]; omega) (by decide)

/-- The word 4 bytes into the word at `d`: its high half, and the low half of
the next. -/
theorem word_mid (m : Mem) (base : Addr) (d : Nat) :
    (VG.Proof.X448.X86_64.word m base (d + 4)).toNat =
      (VG.Proof.X448.X86_64.word m base d).toNat / 2 ^ 32 + 2 ^ 32 * ((VG.Proof.X448.X86_64.word m base (d + 8)).toNat % 2 ^ 32) := by
  have e : ∀ e, (VG.Proof.X448.X86_64.word m base e).toNat = X25519.leNum (Spec.X25519.bytesAt m (VG.Proof.X448.X86_64.off base e) 4) +
      2 ^ 32 * X25519.leNum (Spec.X25519.bytesAt m (VG.Proof.X448.X86_64.off base (e + 4)) 4) := fun e => by
    rw [VG.Proof.X448.X86_64.word, ← X25519.leNum_bytesAt_64, show 8 = 4 + 4 from rfl, X25519.bytesAt_add,
      X25519.leNum_append, X25519.length_bytesAt, VG.Proof.X448.X86_64.off, Offset.add_add]
  have l : ∀ e, X25519.leNum (Spec.X25519.bytesAt m (VG.Proof.X448.X86_64.off base e) 4) < 2 ^ 32 := fun e => by
    have := X25519.leNum_lt (Spec.X25519.bytesAt m (VG.Proof.X448.X86_64.off base e) 4)
    rwa [X25519.length_bytesAt] at this
  rw [e d, e (d + 4), e (d + 8), show d + 4 + 4 = d + 8 by omega]
  have := l d; have := l (d + 4); have := l (d + 8); have := l (d + 8 + 4)
  omega

/-- The 32-bit word 4 bytes into the word at `d`: its high half. -/
theorem readW32_mid (m : Mem) (base : Addr) (d : Nat) :
    (m.readW (VG.Proof.X448.X86_64.off base (d + 4)) 32).toNat = (VG.Proof.X448.X86_64.word m base d).toNat / 2 ^ 32 := by
  rw [VG.Proof.X448.X86_64.readW32, ← VG.Proof.X448.X86_64.word, VG.Proof.X448.X86_64.word_mid]
  have := (VG.Proof.X448.X86_64.word m base d).isLt
  omega

/-- `rcx += [d]`'s low half, without overflow. -/
theorem addLo_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {d : Nat} (hd : d + 8 ≤ 8192)
    (hb : (s.gpr .rcx).toNat + (s.mem.readW (VG.Proof.X448.X86_64.off base d) 32).toNat < 2 ^ 64) :
    WP isa (.block [.mov32 .rdx (.mem (sc d)), .alu .add .rcx (.reg .rdx)]) s fun s' =>
      (s'.gpr .rcx).toNat = (s.gpr .rcx).toNat + (s.mem.readW (VG.Proof.X448.X86_64.off base d) 32).toNat ∧
      VG.Proof.X448.X86_64.Keeps [.rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    State.load32, VG.Proof.X448.X86_64.ea_sc, hs.rdi, hs.read (d := d) (n := 4) (by omega), ite_true, Option.map_some,
    Option.bind_some, State.setReg32, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.rcx = Reg.rdx), Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_add, VG.Proof.X448.X86_64.toNat_setWidth_32_64, Nat.mod_eq_of_lt hb]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr.2]

/-- `rot(H)` from its halves: `H`'s words `hⱼ = loⱼ + 2³² hiⱼ`. -/
theorem rot_arith (lo0 lo1 lo2 lo3 lo4 lo5 lo6 hi0 hi1 hi2 hi3 hi4 hi5 hi6 : Nat) :
    (hi3 + 2 ^ 32 * lo4) + 2 ^ 64 * ((hi4 + 2 ^ 32 * lo5) + 2 ^ 64 * ((hi5 + 2 ^ 32 * lo6) +
      2 ^ 64 * ((2 ^ 32 * lo0 + hi6) + 2 ^ 64 * ((hi0 + 2 ^ 32 * lo1) + 2 ^ 64 *
      ((hi1 + 2 ^ 32 * lo2) + 2 ^ 64 * (hi2 + 2 ^ 32 * lo3)))))) =
    hi3 + 2 ^ 32 * ((lo4 + 2 ^ 32 * hi4) + 2 ^ 64 * ((lo5 + 2 ^ 32 * hi5) + 2 ^ 64 *
      ((lo6 + 2 ^ 32 * hi6) + 2 ^ 64 * ((lo0 + 2 ^ 32 * hi0) + 2 ^ 64 * ((lo1 + 2 ^ 32 * hi1) +
      2 ^ 64 * ((lo2 + 2 ^ 32 * hi2) + 2 ^ 64 * lo3)))))) := by
  rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide]
  generalize 2 ^ 32 = C
  grind

/-- The registers the field arithmetic uses. -/
def clob : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

theorem rvW_split (s : State) :
    VG.Proof.X448.X86_64.rv s W = VG.Proof.X448.X86_64.rv s [.r8, .r9, .r10] + 2 ^ 192 * VG.Proof.X448.X86_64.rv s [.r11, .r12, .r13, .r14] := by
  simp only [VG.Proof.X448.X86_64.rv, W]; omega

theorem rv5_split (s : State) :
    VG.Proof.X448.X86_64.rv s [.r11, .r12, .r13, .r14, .r15] = VG.Proof.X448.X86_64.rv s [.r11, .r12, .r13, .r14] +
      2 ^ 256 * (s.gpr .r15).toNat := by
  simp only [VG.Proof.X448.X86_64.rv]; omega

theorem len64_1 {α : Type} (a : α) : 64 * [a].length = 64 := rfl
theorem len64_5 {α : Type} (a b c d e : α) : 64 * [a, b, c, d, e].length = 320 := rfl
theorem len64_7 {α : Type} (a b c d e f g : α) : 64 * [a, b, c, d, e, f, g].length = 448 := rfl

theorem mvH (m : Mem) (base : Addr) :
    VG.Proof.X448.X86_64.mv m base (ACC + 56) 7 = (VG.Proof.X448.X86_64.word m base (h 7)).toNat + 2 ^ 64 * ((VG.Proof.X448.X86_64.word m base (h 8)).toNat +
      2 ^ 64 * ((VG.Proof.X448.X86_64.word m base (h 9)).toNat + 2 ^ 64 * ((VG.Proof.X448.X86_64.word m base (h 10)).toNat +
      2 ^ 64 * ((VG.Proof.X448.X86_64.word m base (h 11)).toNat + 2 ^ 64 * ((VG.Proof.X448.X86_64.word m base (h 12)).toNat +
      2 ^ 64 * (VG.Proof.X448.X86_64.word m base (h 13)).toNat))))) := by
  simp only [VG.Proof.X448.X86_64.mv, h, ACC, Nat.reduceAdd, Nat.reduceMul, Nat.mul_zero, Nat.add_zero]

/-- `reduce o`: `[o] ≡ L + 2⁴⁴⁸ H`, for the product `L + 2⁴⁴⁸ H` at `ACC`. -/
theorem reduce_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {o : Nat} (ho : o + 56 ≤ ACC) :
    WP isa (.block (reduce o)) s fun s' =>
      VG.Proof.X448.X86_64.fe s'.mem base o % P = (VG.Proof.X448.X86_64.mv s.mem base ACC 7 + 2 ^ 448 * VG.Proof.X448.X86_64.mv s.mem base (ACC + 56) 7) % P ∧
      (∀ r, r ∉ VG.Proof.X448.X86_64.clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X448.X86_64.Outside base o 56 s.mem s'.mem := by
  simp only [reduce, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.mov32_ok s .r15 0) fun s1 ⟨z1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.loads_ok hs1 ACC W VG.Proof.X448.X86_64.W_nodup (by decide) (by decide)) fun s2 ⟨_, v2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff, show (List.range 7).map (fun i => Src.mem (sc (h (7 + i)))) =
    Src.mem (sc (h 7)) :: ([h 8, h 9, h 10, h 11, h 12, h 13].map fun d => Src.mem (sc d)) from rfl]
  refine WP.mono (VG.Proof.X448.X86_64.add_chain_ok W s2 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] _ _
    (VG.Proof.X448.X86_64.word s2.mem base (h 7)) _ (fun _ h => h) VG.Proof.X448.X86_64.W_nodup rfl
    (VG.Proof.X448.X86_64.stable_sc hs2 (by decide) (by simp only [h, ACC]; omega))
    (VG.Proof.X448.X86_64.stable_scs hs2 (by decide) _ (by simp only [h, ACC]; decide))) fun s3 ⟨c1, hc1, e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [show ([.alu .adc .r15 (.imm 0), .mov .rax (.mem (sc (h 10))), .mov32 .rdx (.reg .rax),
      .alu .sub .rax (.reg .rdx)] : List Instr) = [.alu .adc .r15 (.imm 0)] ++
      [.mov .rax (.mem (sc (h 10))), .mov32 .rdx (.reg .rax), .alu .sub .rax (.reg .rdx)] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.adcs_ok [.r15] s3 [.r15] [.imm 0] [0] s3 c1 (Keeps.refl _ _) (fun _ h => h)
    (by decide) rfl (.cons (VG.Proof.X448.X86_64.stable_imm0 _ _) .nil) hc1) fun s4 ⟨c4, _, e4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.splitH_ok hs4) fun s5 ⟨d5, a5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.add_chain_ok [.r11, .r12, .r13, .r14, .r15] s5 .r11 [.r12, .r13, .r14, .r15]
    (.reg .rax) [.mem (sc (h 11)), .mem (sc (h 12)), .mem (sc (h 13)), .imm 0] (s5.gpr .rax)
    [VG.Proof.X448.X86_64.word s5.mem base (h 11), VG.Proof.X448.X86_64.word s5.mem base (h 12), VG.Proof.X448.X86_64.word s5.mem base (h 13), 0] (fun _ h => h)
    (by decide) rfl (VG.Proof.X448.X86_64.stable_reg s5 (by decide))
    (.cons (VG.Proof.X448.X86_64.stable_sc hs5 (by decide) (by simp only [h, ACC]; omega))
      (.cons (VG.Proof.X448.X86_64.stable_sc hs5 (by decide) (by simp only [h, ACC]; omega))
        (.cons (VG.Proof.X448.X86_64.stable_sc hs5 (by decide) (by simp only [h, ACC]; omega))
          (.cons (VG.Proof.X448.X86_64.stable_imm0 _ _) .nil))))) fun s6 ⟨c6, _, e6, k6⟩ => ?_
  have hs6 := hs5.of_keeps k6 (by decide)
  rw [WP.block_append_iff, show ([.mov .rcx (.mem (sc (h 6 + 4))), .mov32 .rdx (.reg .rcx),
      .alu .sub .rcx (.reg .rdx), .mov32 .rdx (.mem (sc (h 13 + 4))), .alu .add .rcx (.reg .rdx)] :
      List Instr) = [.mov .rcx (.mem (sc (h 6 + 4))), .mov32 .rdx (.reg .rcx),
      .alu .sub .rcx (.reg .rdx)] ++ [.mov32 .rdx (.mem (sc (h 13 + 4))), .alu .add .rcx (.reg .rdx)]
      from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.splitLo_ok hs6 (d := h 6 + 4) (by simp only [h, ACC]; omega) (r := .rcx)
    (t := .rdx) (by decide)) fun s7 ⟨d7, a7, k7⟩ => ?_
  have hs7 := hs6.of_keeps k7 (by decide)
  have g := fun {x y : State} {rs : List Reg} (k : VG.Proof.X448.X86_64.Keeps rs x y) (r : Reg) (h : r ∉ rs) => k.1 r h
  -- Memory is only read until the stores.
  have m2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have m4 : s4.mem = s.mem := k4.2.1.trans (k3.2.1.trans m2)
  have m5 : s5.mem = s.mem := k5.2.1.trans m4
  have m6 : s6.mem = s.mem := k6.2.1.trans m5
  have m7 : s7.mem = s.mem := k7.2.1.trans m6
  -- `rcx`: word 3 of `rot(H)`.
  have wm6 := VG.Proof.X448.X86_64.word_mid s.mem base (h 6)
  rw [show h 6 + 8 = h 7 from rfl] at wm6
  have r7 : (s7.gpr .rcx).toNat = 2 ^ 32 * ((VG.Proof.X448.X86_64.word s.mem base (h 7)).toNat % 2 ^ 32) := by
    rw [m6] at d7 a7
    have := Nat.div_lt_of_lt_mul (m := (VG.Proof.X448.X86_64.word s.mem base (h 6)).toNat) (n := 2 ^ 32) (k := 2 ^ 32)
      (VG.Proof.X448.X86_64.word s.mem base (h 6)).isLt
    omega
  have hi13 := VG.Proof.X448.X86_64.readW32_mid s.mem base (h 13)
  have hb13 : (VG.Proof.X448.X86_64.word s.mem base (h 13)).toNat / 2 ^ 32 < 2 ^ 32 :=
    Nat.div_lt_of_lt_mul (VG.Proof.X448.X86_64.word s.mem base (h 13)).isLt
  have hl7 : (VG.Proof.X448.X86_64.word s.mem base (h 7)).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  refine WP.mono (VG.Proof.X448.X86_64.addLo_ok hs7 (d := h 13 + 4) (by simp only [h, ACC]; omega)
    (by rw [r7, m7, hi13]; omega)) fun s8 ⟨e8, k8⟩ => ?_
  have hs8 := hs7.of_keeps k8 (by decide)
  have m8 : s8.mem = s.mem := k8.2.1.trans m7
  rw [m7, hi13, r7] at e8
  -- `+ rot(H)`
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.add_chain_ok W s8 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] _ _
    (VG.Proof.X448.X86_64.word s8.mem base (h 10 + 4)) [VG.Proof.X448.X86_64.word s8.mem base (h 11 + 4), VG.Proof.X448.X86_64.word s8.mem base (h 12 + 4),
      s8.gpr .rcx, VG.Proof.X448.X86_64.word s8.mem base (h 7 + 4), VG.Proof.X448.X86_64.word s8.mem base (h 8 + 4),
      VG.Proof.X448.X86_64.word s8.mem base (h 9 + 4)] (fun _ h => h) VG.Proof.X448.X86_64.W_nodup rfl
    (VG.Proof.X448.X86_64.stable_sc hs8 (by decide) (by simp only [h, ACC]; omega))
    (.cons (VG.Proof.X448.X86_64.stable_sc hs8 (by decide) (by simp only [h, ACC]; omega))
      (.cons (VG.Proof.X448.X86_64.stable_sc hs8 (by decide) (by simp only [h, ACC]; omega))
        (.cons (VG.Proof.X448.X86_64.stable_reg s8 (by decide))
          (.cons (VG.Proof.X448.X86_64.stable_sc hs8 (by decide) (by simp only [h, ACC]; omega))
            (.cons (VG.Proof.X448.X86_64.stable_sc hs8 (by decide) (by simp only [h, ACC]; omega))
              (.cons (VG.Proof.X448.X86_64.stable_sc hs8 (by decide) (by simp only [h, ACC]; omega)) .nil)))))))
    fun s9 ⟨c9, hc9, e9, k9⟩ => ?_
  have hs9 := hs8.of_keeps k9 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.adcs_ok [.r15] s9 [.r15] [.imm 0] [0] s9 c9 (Keeps.refl _ _) (fun _ h => h)
    (by decide) rfl (.cons (VG.Proof.X448.X86_64.stable_imm0 _ _) .nil) hc9) fun s10 ⟨c10, _, e10, k10⟩ => ?_
  have hs10 := hs9.of_keeps k10 (by decide)
  -- `r15` along the way, and the bounds that exclude overflow.
  have r15_3 : s3.gpr .r15 = 0 := by rw [g k3 _ (by decide), g k2 _ (by decide), z1]; rfl
  rw [VG.Proof.X448.X86_64.len64_1] at e4
  simp only [VG.Proof.X448.X86_64.rv, VG.Proof.X448.X86_64.wv, r15_3, VG.Proof.X448.X86_64.toNat_zero64] at e4
  have hc1 := Bool.toNat_le c1
  have r15_5 : (s5.gpr .r15).toNat = c1.toNat := by rw [g k5 _ (by decide)]; omega
  have l6 := VG.Proof.X448.X86_64.rv_lt s6 [.r11, .r12, .r13, .r14]
  have l5 := VG.Proof.X448.X86_64.rv_lt s5 [.r11, .r12, .r13, .r14]
  rw [VG.Proof.X448.X86_64.len64_5] at e6
  rw [VG.Proof.X448.X86_64.rv5_split, VG.Proof.X448.X86_64.rv5_split, r15_5] at e6
  simp only [VG.Proof.X448.X86_64.wv, VG.Proof.X448.X86_64.toNat_zero64] at e6
  simp only [List.length_cons, List.length_nil] at l6 l5
  have hc6 : c6.toNat = 0 := by
    have := Bool.toNat_le c6
    have := (VG.Proof.X448.X86_64.word s5.mem base (h 11)).isLt; have := (VG.Proof.X448.X86_64.word s5.mem base (h 12)).isLt
    have := (VG.Proof.X448.X86_64.word s5.mem base (h 13)).isLt; have := (s5.gpr .rax).isLt
    have := (s6.gpr .r15).isLt
    rcases Nat.lt_or_ge c6.toNat 1 with h | h
    · omega
    · exfalso; omega
  rw [VG.Proof.X448.X86_64.len64_1] at e10
  simp only [VG.Proof.X448.X86_64.rv, VG.Proof.X448.X86_64.wv, VG.Proof.X448.X86_64.toNat_zero64] at e10
  have r15_9 : s9.gpr .r15 = s6.gpr .r15 := by
    rw [g k9 _ (by decide), g k8 _ (by decide), g k7 _ (by decide)]
  rw [m5] at e6
  rw [m4] at d5 a5
  rw [VG.Proof.X448.X86_64.len64_7, m2] at e3
  rw [VG.Proof.X448.X86_64.len64_7, m8, VG.Proof.X448.X86_64.W_lit] at e9
  rw [k1.2.1, show W.length = 7 from rfl] at v2
  -- The registers along the way.
  have w43 : VG.Proof.X448.X86_64.rv s4 W = VG.Proof.X448.X86_64.rv s3 W := k4.rv_eq (by decide)
  have w54 : VG.Proof.X448.X86_64.rv s5 W = VG.Proof.X448.X86_64.rv s4 W := k5.rv_eq (by decide)
  have w65 : VG.Proof.X448.X86_64.rv s6 [.r8, .r9, .r10] = VG.Proof.X448.X86_64.rv s5 [.r8, .r9, .r10] := k6.rv_eq (by decide)
  have w76 : VG.Proof.X448.X86_64.rv s7 W = VG.Proof.X448.X86_64.rv s6 W := k7.rv_eq (by decide)
  have w87 : VG.Proof.X448.X86_64.rv s8 W = VG.Proof.X448.X86_64.rv s7 W := k8.rv_eq (by decide)
  have sp5 := VG.Proof.X448.X86_64.rvW_split s5
  have sp6 := VG.Proof.X448.X86_64.rvW_split s6
  simp only [VG.Proof.X448.X86_64.wv, List.map_cons, List.map_nil] at e3 e9 e6
  rw [VG.Proof.X448.X86_64.W_lit] at e3
  -- `rot(H)`'s words.
  have mid := fun d => VG.Proof.X448.X86_64.word_mid s.mem base d
  have M10 := mid (h 10); have M11 := mid (h 11); have M12 := mid (h 12)
  have M7 := mid (h 7); have M8 := mid (h 8); have M9 := mid (h 9)
  rw [show h 10 + 8 = h 11 from rfl] at M10
  rw [show h 11 + 8 = h 12 from rfl] at M11
  rw [show h 12 + 8 = h 13 from rfl] at M12
  rw [show h 7 + 8 = h 8 from rfl] at M7
  rw [show h 8 + 8 = h 9 from rfl] at M8
  rw [show h 9 + 8 = h 10 from rfl] at M9
  have rot := VG.Proof.X448.X86_64.rot_arith ((VG.Proof.X448.X86_64.word s.mem base (h 7)).toNat % 2 ^ 32)
    ((VG.Proof.X448.X86_64.word s.mem base (h 8)).toNat % 2 ^ 32) ((VG.Proof.X448.X86_64.word s.mem base (h 9)).toNat % 2 ^ 32)
    ((VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat % 2 ^ 32) ((VG.Proof.X448.X86_64.word s.mem base (h 11)).toNat % 2 ^ 32)
    ((VG.Proof.X448.X86_64.word s.mem base (h 12)).toNat % 2 ^ 32) ((VG.Proof.X448.X86_64.word s.mem base (h 13)).toNat % 2 ^ 32)
    ((VG.Proof.X448.X86_64.word s.mem base (h 7)).toNat / 2 ^ 32) ((VG.Proof.X448.X86_64.word s.mem base (h 8)).toNat / 2 ^ 32)
    ((VG.Proof.X448.X86_64.word s.mem base (h 9)).toNat / 2 ^ 32) ((VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat / 2 ^ 32)
    ((VG.Proof.X448.X86_64.word s.mem base (h 11)).toNat / 2 ^ 32) ((VG.Proof.X448.X86_64.word s.mem base (h 12)).toNat / 2 ^ 32)
    ((VG.Proof.X448.X86_64.word s.mem base (h 13)).toNat / 2 ^ 32)
  simp only [Nat.mod_add_div] at rot
  rw [← M10, ← M11, ← M12, ← M7, ← M8, ← M9, ← e8] at rot
  -- The whole sum, before the folds.
  have tot : VG.Proof.X448.X86_64.rv s10 W + 2 ^ 448 * (s10.gpr .r15).toNat =
      VG.Proof.X448.X86_64.mv s.mem base ACC 7 + ((VG.Proof.X448.X86_64.word s.mem base (h 7)).toNat + 2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 8)).toNat +
        2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 9)).toNat + 2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat +
        2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 11)).toNat + 2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 12)).toNat +
        2 ^ 64 * (VG.Proof.X448.X86_64.word s.mem base (h 13)).toNat)))))) + 2 ^ 192 * (s5.gpr .rax).toNat +
      2 ^ 256 * (VG.Proof.X448.X86_64.word s.mem base (h 11)).toNat + 2 ^ 320 * (VG.Proof.X448.X86_64.word s.mem base (h 12)).toNat +
      2 ^ 384 * (VG.Proof.X448.X86_64.word s.mem base (h 13)).toNat + (VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat / 2 ^ 32 +
      2 ^ 32 * ((VG.Proof.X448.X86_64.word s.mem base (h 11)).toNat + 2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 12)).toNat +
        2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 13)).toNat + 2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 7)).toNat +
        2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 8)).toNat + 2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 9)).toNat +
        2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat % 2 ^ 32))))))) := by
    have w10 : VG.Proof.X448.X86_64.rv s10 W = VG.Proof.X448.X86_64.rv s9 W := k10.rv_eq (by decide)
    -- the first two additions
    have S6 : VG.Proof.X448.X86_64.rv s6 W + 2 ^ 448 * (s6.gpr .r15).toNat = VG.Proof.X448.X86_64.mv s.mem base ACC 7 +
        ((VG.Proof.X448.X86_64.word s.mem base (h 7)).toNat + 2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 8)).toNat +
        2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 9)).toNat + 2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat +
        2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 11)).toNat + 2 ^ 64 * ((VG.Proof.X448.X86_64.word s.mem base (h 12)).toNat +
        2 ^ 64 * (VG.Proof.X448.X86_64.word s.mem base (h 13)).toNat)))))) + 2 ^ 192 * (s5.gpr .rax).toNat +
        2 ^ 256 * (VG.Proof.X448.X86_64.word s.mem base (h 11)).toNat + 2 ^ 320 * (VG.Proof.X448.X86_64.word s.mem base (h 12)).toNat +
        2 ^ 384 * (VG.Proof.X448.X86_64.word s.mem base (h 13)).toNat := by
      omega_using [e3, e4, e6, v2, w43, w54, w65, sp5, sp6, hc6, r15_5, hc1]
    have r6 : (s6.gpr .r15).toNat ≤ 2 := by
      have b1 := VG.Proof.X448.X86_64.rv_lt s6 W; rw [VG.Proof.X448.X86_64.len_W] at b1
      have b2 := VG.Proof.X448.X86_64.mv_lt s.mem base ACC 7
      rw [show 64 * 7 = 448 from rfl] at b2
      have b7 := (VG.Proof.X448.X86_64.word s.mem base (h 7)).isLt; have b8 := (VG.Proof.X448.X86_64.word s.mem base (h 8)).isLt
      have b9 := (VG.Proof.X448.X86_64.word s.mem base (h 9)).isLt; have b10 := (VG.Proof.X448.X86_64.word s.mem base (h 10)).isLt
      have b11 := (VG.Proof.X448.X86_64.word s.mem base (h 11)).isLt; have b12 := (VG.Proof.X448.X86_64.word s.mem base (h 12)).isLt
      have b13 := (VG.Proof.X448.X86_64.word s.mem base (h 13)).isLt; have ba := (s5.gpr .rax).isLt
      omega_using [S6, b1, b2, b7, b8, b9, b10, b11, b12, b13, ba]
    have c10z : (s10.gpr .r15).toNat = (s6.gpr .r15).toNat + c9.toNat := by
      rw [r15_9] at e10
      have b9 := Bool.toNat_le c9; have b10 := Bool.toNat_le c10
      omega_using [e10, r6, b9, b10]
    rw [w10, c10z]
    simp only [Nat.mul_zero, Nat.add_zero] at e9
    rw [w87, w76, rot] at e9
    generalize (VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat / 2 ^ 32 = HI at e9 ⊢
    generalize (VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat % 2 ^ 32 = LO at e9 ⊢
    omega_using [S6, e9]
  have hsum : (s10.gpr .r15).toNat < 4 := by
    have hHI : (VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat / 2 ^ 32 < 2 ^ 32 :=
      Nat.div_lt_of_lt_mul (VG.Proof.X448.X86_64.word s.mem base (h 10)).isLt
    have hLO : (VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    generalize (VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat / 2 ^ 32 = HI at tot hHI
    generalize (VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat % 2 ^ 32 = LO at tot hLO
    have b1 := VG.Proof.X448.X86_64.rv_lt s10 W; rw [VG.Proof.X448.X86_64.len_W] at b1
    have b2 := VG.Proof.X448.X86_64.mv_lt s.mem base ACC 7
    rw [show 64 * 7 = 448 from rfl] at b2
    have b7 := (VG.Proof.X448.X86_64.word s.mem base (h 7)).isLt; have b8 := (VG.Proof.X448.X86_64.word s.mem base (h 8)).isLt
    have b9 := (VG.Proof.X448.X86_64.word s.mem base (h 9)).isLt; have b10 := (VG.Proof.X448.X86_64.word s.mem base (h 10)).isLt
    have b11 := (VG.Proof.X448.X86_64.word s.mem base (h 11)).isLt; have b12 := (VG.Proof.X448.X86_64.word s.mem base (h 12)).isLt
    have b13 := (VG.Proof.X448.X86_64.word s.mem base (h 13)).isLt; have ba := (s5.gpr .rax).isLt
    omega_using [tot, b1, b2, b7, b8, b9, b10, b11, b12, b13, ba, hHI, hLO]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.fold2_ok s10 (by omega)) fun s11 ⟨e11, k11⟩ => ?_
  have hs11 := hs10.of_keeps k11 (by decide)
  refine WP.mono (VG.Proof.X448.X86_64.stores_ok hs11 o W (by rw [show W.length = 7 from rfl]; simp only [ACC] at ho; omega)) fun s12 ⟨e12, o12, g12, rd12, wr12⟩ => ?_
  rw [show W.length = 7 from rfl] at e12 o12
  have K : VG.Proof.X448.X86_64.Keeps VG.Proof.X448.X86_64.clob s s11 := (k1.mono (by decide)).trans <| (k2.mono (by decide)).trans <|
    (k3.mono (by decide)).trans <| (k4.mono (by decide)).trans <| (k5.mono (by decide)).trans <|
    (k6.mono (by decide)).trans <| (k7.mono (by decide)).trans <| (k8.mono (by decide)).trans <|
    (k9.mono (by decide)).trans <| (k10.mono (by decide)).trans (k11.mono (by decide))
  refine ⟨?_, fun r hr => (g12 r).trans (K.1 r hr), rd12.trans K.2.2.1, wr12.trans K.2.2.2,
    by rw [← K.2.1]; exact o12⟩
  · show VG.Proof.X448.X86_64.mv s12.mem base o 7 % P = _
    rw [e12, e11, tot, VG.Proof.X448.X86_64.mvH]
    refine Eq.symm (VG.Proof.X448.X86_64.reduce_arith (VG.Proof.X448.X86_64.mv s.mem base ACC 7) (VG.Proof.X448.X86_64.word s.mem base (h 7)).toNat (VG.Proof.X448.X86_64.word s.mem base (h 8)).toNat (VG.Proof.X448.X86_64.word s.mem base (h 9)).toNat (VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat (VG.Proof.X448.X86_64.word s.mem base (h 11)).toNat (VG.Proof.X448.X86_64.word s.mem base (h 12)).toNat (VG.Proof.X448.X86_64.word s.mem base (h 13)).toNat ((VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat % 2 ^ 32) ((VG.Proof.X448.X86_64.word s.mem base (h 10)).toNat / 2 ^ 32) (s5.gpr .rax).toNat
      ?_ ?_)
    · exact Nat.mod_add_div _ _
    · rw [← d5]; exact a5

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Field`. -/
section

/-!
# X448 on x86-64: the field multiplications

Each field operation on the working space as a change of the field element
`F` it writes: the element at `o` becomes the result, the bytes outside it
and the product's words at `ACC` are unchanged, and so are the registers but
those the arithmetic uses (`Op`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448
open VG.Spec.X448 (P)

/-- The field element at `base + o`, in `GF(p)`. -/
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := toFe (VG.Proof.X448.X86_64.fe m base o)

/-- A field element's slot: below the product's words. -/
abbrev Slot (o : Nat) : Prop := o + 56 ≤ ACC

/-- A field operation's effect but for its result: the registers but `clob`,
the regions and the memory outside the 56 bytes at `base + o` and the
product's words are unchanged. -/
structure Op (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ VG.Proof.X448.X86_64.clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : VG.Proof.X448.X86_64.Outside2 base o 56 ACC 112 s.mem s'.mem

theorem Op.scr {base : Addr} {o : Nat} {s s' : State} (h : VG.Proof.X448.X86_64.Op base o s s') (hs : VG.Proof.X448.X86_64.Scr s base) :
    VG.Proof.X448.X86_64.Scr s' base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem mv_add (m : Mem) (base : Addr) :
    ∀ (o a b : Nat), VG.Proof.X448.X86_64.mv m base o (a + b) = VG.Proof.X448.X86_64.mv m base o a + 2 ^ (64 * a) * VG.Proof.X448.X86_64.mv m base (o + 8 * a) b
  | o, 0, b => by simp [VG.Proof.X448.X86_64.mv]
  | o, a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega, VG.Proof.X448.X86_64.mv, VG.Proof.X448.X86_64.mv, VG.Proof.X448.X86_64.mv_add m base (o + 8) a b, VG.Proof.X448.X86_64.pow64_succ,
      show o + 8 + 8 * a = o + 8 * (a + 1) by omega]
    generalize 2 ^ (64 * a) = Q
    grind

theorem zeroAcc_ok (s : State) :
    WP isa (.block zeroAcc) s fun s' => VG.Proof.X448.X86_64.rv s' (VG.Proof.X448.X86_64.acc 0) = 0 ∧ VG.Proof.X448.X86_64.Keeps [.r15, .rcx, .rbp] s s' := by
  apply WP.of_runBlock
  simp only [zeroAcc, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [VG.Proof.X448.X86_64.acc, VG.Proof.X448.X86_64.accR_mod, Nat.zero_add, Nat.reduceMod, List.getD_cons_zero,
      List.getD_cons_succ, VG.Proof.X448.X86_64.rv, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

/-- The product of an `a`-word and a `b`-word number has `a + b` words.
(Exponents are kept symbolic: Lean does not evaluate powers above `2²⁵⁶`.) -/
theorem prod_lt {x y a b : Nat} (hx : x < 2 ^ (64 * a)) (hy : y < 2 ^ (64 * b)) :
    x * y < 2 ^ (64 * (a + b)) := by
  rw [Nat.mul_add, Nat.pow_add]
  exact Nat.mul_lt_mul'' hx hy

/-- The columns and the reduction of a product `x · y`: given the columns'
result (`hcol`), `[o] ≡ x · y`. -/
theorem product_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {o : Nat} (ho : VG.Proof.X448.X86_64.Slot o)
    {x y : Nat} (hx : x < 2 ^ (64 * 7)) (hy : y < 2 ^ (64 * 7))
    (hcol : VG.Proof.X448.X86_64.mv s.mem base ACC (7 + 7) + 2 ^ (64 * (7 + 7)) * VG.Proof.X448.X86_64.rv s (VG.Proof.X448.X86_64.acc (7 + 7)) = x * y) :
    WP isa (.block (reduce o)) s fun s' =>
      VG.Proof.X448.X86_64.fe s'.mem base o % P = x * y % P ∧
      (∀ r, r ∉ VG.Proof.X448.X86_64.clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X448.X86_64.Outside base o 56 s.mem s'.mem := by
  refine WP.mono (VG.Proof.X448.X86_64.reduce_ok hs ho) fun s' ⟨e, g, rd, wr, out⟩ => ⟨?_, g, rd, wr, out⟩
  have hl := VG.Proof.X448.X86_64.prod_lt hx hy
  have h0 : VG.Proof.X448.X86_64.rv s (VG.Proof.X448.X86_64.acc (7 + 7)) = 0 := by
    rcases Nat.eq_zero_or_pos (VG.Proof.X448.X86_64.rv s (VG.Proof.X448.X86_64.acc (7 + 7))) with h | h
    · exact h
    · exfalso
      have := Nat.mul_le_mul_left (2 ^ (64 * (7 + 7))) h
      generalize 2 ^ (64 * (7 + 7)) = Q at *
      omega
  generalize 2 ^ (64 * (7 + 7)) = Q at hcol
  rw [h0, Nat.mul_zero, Nat.add_zero, VG.Proof.X448.X86_64.mv_add, show 64 * 7 = 448 from rfl,
    show ACC + 8 * 7 = ACC + 56 from rfl] at hcol
  rw [e, ← hcol]

theorem val7_congr {f g : Nat → Nat} (h : ∀ i < 7, f i = g i) : VG.Proof.X448.X86_64.val7 f = VG.Proof.X448.X86_64.val7 g := by
  simp only [VG.Proof.X448.X86_64.val7, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide)]

theorem colX_clob : ∀ r ∈ VG.Proof.X448.X86_64.colX, r ∈ VG.Proof.X448.X86_64.clob := by decide
theorem acc_clob : ∀ r ∈ [Reg.r15, .rcx, .rbp], r ∈ VG.Proof.X448.X86_64.clob := by decide
theorem w_acc : ∀ j < 7, w j ∉ [Reg.r15, .rcx, .rbp] := by decide
theorem W_clob : ∀ r ∈ W, r ∈ VG.Proof.X448.X86_64.clob := by decide

/-- The end of `mul` and `sqr`: the columns, then the reduction, with the
columns' operands `xv`, `yv` whose values are `x` and `y`. -/
theorem colsReduce_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {o : Nat} (ho : VG.Proof.X448.X86_64.Slot o)
    (xs : Nat → Src) (xv : Nat → BitVec 64) (cols : Nat → List Term)
    (hx : ∀ s', (∀ r, r ∉ VG.Proof.X448.X86_64.colX → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      VG.Proof.X448.X86_64.Outside base ACC 112 s.mem s'.mem → ∀ i < 7, VG.Proof.X448.X86_64.Stable VG.Proof.X448.X86_64.colX s' (xs i) (xv i))
    (hc : ∀ k < 14, ∀ t ∈ cols k, t.i < 7 ∧ t.j < 7) (hw : ∀ k < 14, ((cols k).map VG.Proof.X448.X86_64.termK).sum ≤ 7)
    (h0 : VG.Proof.X448.X86_64.rv s (VG.Proof.X448.X86_64.acc 0) = 0) {x y : Nat} (hxl : x < 2 ^ (64 * 7)) (hyl : y < 2 ^ (64 * 7))
    (hsum : VG.Proof.X448.X86_64.colsVal (fun i => (xv i).toNat) (fun j => (s.gpr (w j)).toNat) cols 0 14 = x * y) :
    WP isa (.block (columns xs w cols ++ reduce o)) s fun s' =>
      VG.Proof.X448.X86_64.fe s'.mem base o % P = x * y % P ∧ (∀ r, r ∉ VG.Proof.X448.X86_64.clob → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Proof.X448.X86_64.Outside2 base o 56 ACC 112 s.mem s'.mem := by
  rw [WP.block_append_iff, columns]
  refine WP.mono (VG.Proof.X448.X86_64.columns_ok hs xs w xv cols hx (by decide) hc hw h0 (7 + 7) (Nat.le_refl _))
    fun s1 ⟨g1, rd1, wr1, o1, e1, _⟩ => ?_
  have hs1 : VG.Proof.X448.X86_64.Scr s1 base := ⟨(g1 _ VG.Proof.X448.X86_64.rdi_colX).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (VG.Proof.X448.X86_64.product_ok hs1 ho hxl hyl (by rw [e1]; exact hsum)) fun s2 ⟨e2, g2, rd2, wr2, o2⟩ =>
    ⟨e2, fun r hr => (g2 r hr).trans (g1 r fun h => hr (VG.Proof.X448.X86_64.colX_clob r h)), rd2.trans rd1, wr2.trans wr1,
      (o1.right o 56).trans (o2.left ACC 112)⟩

/-- `[o] = [a] · [b]`. -/
theorem mul_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {o a b : Nat} (ho : VG.Proof.X448.X86_64.Slot o)
    (ha : VG.Proof.X448.X86_64.Slot a) (hb : VG.Proof.X448.X86_64.Slot b) :
    WP isa (.block (VG.Impl.X448.X86_64.mul o a b)) s fun s' =>
      VG.Proof.X448.X86_64.Op base o s s' ∧ VG.Proof.X448.X86_64.F s'.mem base o = VG.Proof.X448.X86_64.F s.mem base a * VG.Proof.X448.X86_64.F s.mem base b := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  rw [VG.Impl.X448.X86_64.mul, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.loads_ok hs b W VG.Proof.X448.X86_64.W_nodup (by decide)
    (by rw [show W.length = 7 from rfl]; omega)) fun s1 ⟨w1, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.zeroAcc_ok s1) fun s2 ⟨z2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have m2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  refine WP.mono (VG.Proof.X448.X86_64.colsReduce_ok hs2 ho (fun i => .mem (sc (a + 8 * i)))
    (fun i => VG.Proof.X448.X86_64.word s2.mem base (a + 8 * i)) mulCol
    (fun s' g _ wr out i hi => by
      have hsS : VG.Proof.X448.X86_64.Scr s' base := ⟨(g _ VG.Proof.X448.X86_64.rdi_colX).trans hs2.rdi, wr ▸ hs2.wr, hs2.nowrap⟩
      have := VG.Proof.X448.X86_64.stable_sc hsS VG.Proof.X448.X86_64.rdi_colX (d := a + 8 * i) (by omega)
      rwa [out.word (by simp only [ACC]; omega) (by omega)] at this)
    VG.Proof.X448.X86_64.mulCol_hc VG.Proof.X448.X86_64.mulCol_hw z2 (VG.Proof.X448.X86_64.mv_lt s.mem base a 7) (VG.Proof.X448.X86_64.mv_lt s.mem base b 7) ?_)
    fun s' ⟨e, g, rd, wr, out⟩ => ⟨⟨fun r hr => ?_, rd.trans (k2.2.2.1.trans k1.2.2.1),
      wr.trans (k2.2.2.2.trans k1.2.2.2), by rw [← m2]; exact out⟩, ?_⟩
  · rw [VG.Proof.X448.X86_64.mulCols_sum, VG.Proof.X448.X86_64.mv7, VG.Proof.X448.X86_64.mv7, m2]
    refine congrArg (VG.Proof.X448.X86_64.val7 _ * ·) (VG.Proof.X448.X86_64.val7_congr fun j hj => ?_)
    rw [k2.1 _ (VG.Proof.X448.X86_64.w_acc j hj)]
    exact congrArg BitVec.toNat (w1 j hj .r8)
  · rw [g r hr, k2.1 r (fun h => hr (VG.Proof.X448.X86_64.acc_clob r h)),
      k1.1 r (fun h => hr (VG.Proof.X448.X86_64.W_clob r h))]
  · exact toFe_mul e

theorem w_colX : ∀ j < 7, w j ∉ VG.Proof.X448.X86_64.colX := by decide

/-- `[o] = [a]²`. -/
theorem sqr_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {o a : Nat} (ho : VG.Proof.X448.X86_64.Slot o)
    (ha : VG.Proof.X448.X86_64.Slot a) :
    WP isa (.block (sqr o a)) s fun s' =>
      VG.Proof.X448.X86_64.Op base o s s' ∧ VG.Proof.X448.X86_64.F s'.mem base o = VG.Proof.X448.X86_64.F s.mem base a * VG.Proof.X448.X86_64.F s.mem base a := by
  have ha' : a + 56 ≤ 1536 := ha
  rw [sqr, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.loads_ok hs a W VG.Proof.X448.X86_64.W_nodup (by decide)
    (by rw [show W.length = 7 from rfl]; omega)) fun s1 ⟨w1, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.zeroAcc_ok s1) fun s2 ⟨z2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have m2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have v2 : VG.Proof.X448.X86_64.val7 (fun j => (s2.gpr (w j)).toNat) = VG.Proof.X448.X86_64.fe s.mem base a := by
    rw [VG.Proof.X448.X86_64.fe, VG.Proof.X448.X86_64.mv7]
    refine VG.Proof.X448.X86_64.val7_congr fun j hj => ?_
    rw [k2.1 _ (VG.Proof.X448.X86_64.w_acc j hj)]
    exact congrArg BitVec.toNat (w1 j hj .r8)
  refine WP.mono (VG.Proof.X448.X86_64.colsReduce_ok hs2 ho (fun i => .reg (w i)) (fun i => s2.gpr (w i)) sqrCol
    (fun s' g _ _ _ i hi => by
      have := VG.Proof.X448.X86_64.stable_reg (X := VG.Proof.X448.X86_64.colX) s' (VG.Proof.X448.X86_64.w_colX i hi)
      rwa [g _ (VG.Proof.X448.X86_64.w_colX i hi)] at this)
    VG.Proof.X448.X86_64.sqrCol_hc VG.Proof.X448.X86_64.sqrCol_hw z2 (VG.Proof.X448.X86_64.mv_lt s.mem base a 7) (VG.Proof.X448.X86_64.mv_lt s.mem base a 7)
    (by rw [VG.Proof.X448.X86_64.sqrCols_sum, v2]))
    fun s' ⟨e, g, rd, wr, out⟩ => ⟨⟨fun r hr => ?_, rd.trans (k2.2.2.1.trans k1.2.2.1),
      wr.trans (k2.2.2.2.trans k1.2.2.2), by rw [← m2]; exact out⟩, toFe_mul e⟩
  rw [g r hr, k2.1 r (fun h => hr (VG.Proof.X448.X86_64.acc_clob r h)), k1.1 r (fun h => hr (VG.Proof.X448.X86_64.W_clob r h))]

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.AddSub`. -/
section

/-!
# X448 on x86-64: addition, subtraction, `a24` and the swap

`add`, `sub` and `mulSmall` as carry chains, multiply-accumulate steps and
folds, and `cswap` word by word (`wp_range_flatMap`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448
open VG.Spec.X448 (P)

theorem words_eq (o : Nat) : words o =
    Src.mem (sc o) :: ([o + 8, o + 16, o + 24, o + 32, o + 40, o + 48].map fun d => Src.mem (sc d)) :=
  rfl

theorem wv_words (m : Mem) (base : Addr) (o : Nat) :
    VG.Proof.X448.X86_64.wv (VG.Proof.X448.X86_64.word m base o :: [o + 8, o + 16, o + 24, o + 32, o + 40, o + 48].map fun d => VG.Proof.X448.X86_64.word m base d) =
      VG.Proof.X448.X86_64.fe m base o := by
  simp only [VG.Proof.X448.X86_64.wv, List.map_cons, List.map_nil, VG.Proof.X448.X86_64.mv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero,
    Nat.add_zero]

theorem wv_words' (m : Mem) (base : Addr) (o : Nat) :
    VG.Proof.X448.X86_64.wv ([o, o + 8, o + 16, o + 24, o + 32, o + 40, o + 48].map fun d => VG.Proof.X448.X86_64.word m base d) =
      VG.Proof.X448.X86_64.fe m base o := VG.Proof.X448.X86_64.wv_words m base o

theorem W_len : W.length = 7 := rfl

/-- `[o] = [a] + [b]`. -/
theorem add_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {o a b : Nat} (ho : VG.Proof.X448.X86_64.Slot o)
    (ha : VG.Proof.X448.X86_64.Slot a) (hb : VG.Proof.X448.X86_64.Slot b) :
    WP isa (.block (add o a b)) s fun s' =>
      VG.Proof.X448.X86_64.Op base o s s' ∧ VG.Proof.X448.X86_64.F s'.mem base o = VG.Proof.X448.X86_64.F s.mem base a + VG.Proof.X448.X86_64.F s.mem base b := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  have ho' : o + 56 ≤ 1536 := ho
  rw [add, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.loads_ok hs a W VG.Proof.X448.X86_64.W_nodup (by decide) (by rw [VG.Proof.X448.X86_64.W_len]; omega))
    fun s1 ⟨_, v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff, VG.Proof.X448.X86_64.words_eq]
  refine WP.mono (VG.Proof.X448.X86_64.add_chain_ok W s1 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] _ _
    (VG.Proof.X448.X86_64.word s1.mem base b) _ (fun _ h => h) VG.Proof.X448.X86_64.W_nodup rfl (VG.Proof.X448.X86_64.stable_sc hs1 (by decide) (by omega))
    (VG.Proof.X448.X86_64.stable_scs hs1 (by decide) _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)))
    fun s2 ⟨c2, hc2, e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.carryOut_ok s2 hc2) fun s3 ⟨e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.fold2_ok s3 (by rw [e3]; cases c2 <;> decide)) fun s4 ⟨e4, k4⟩ => ?_
  have hs4 := ((hs1.of_keeps k2 (by decide)).of_keeps k3 (by decide)).of_keeps k4 (by decide)
  refine WP.mono (VG.Proof.X448.X86_64.stores_ok hs4 o W (by rw [VG.Proof.X448.X86_64.W_len]; omega)) fun s5 ⟨e5, o5, g5, rd5, wr5⟩ => ?_
  rw [VG.Proof.X448.X86_64.W_len] at e5 o5
  have K : VG.Proof.X448.X86_64.Keeps VG.Proof.X448.X86_64.clob s s4 := (k1.mono VG.Proof.X448.X86_64.W_clob).trans <| (k2.mono (by decide)).trans <|
    (k3.mono (by decide)).trans (k4.mono (by decide))
  refine ⟨⟨fun r hr => (g5 r).trans (K.1 r hr), rd5.trans K.2.2.1, wr5.trans K.2.2.2,
    by rw [← K.2.1]; exact o5.left ACC 112⟩, toFe_add ?_⟩
  have w32 : VG.Proof.X448.X86_64.rv s3 W = VG.Proof.X448.X86_64.rv s2 W := k3.rv_eq (by decide)
  rw [VG.Proof.X448.X86_64.len64_7, VG.Proof.X448.X86_64.W_lit, VG.Proof.X448.X86_64.wv_words, v1, VG.Proof.X448.X86_64.W_len] at e2
  rw [k1.2.1] at e2
  change VG.Proof.X448.X86_64.mv s5.mem base o 7 % P = (VG.Proof.X448.X86_64.mv s.mem base a 7 + VG.Proof.X448.X86_64.fe s.mem base b) % P
  rw [e5, e4, w32, e3, e2]

/-- `[o] = [a] - [b]`. -/
theorem sub_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {o a b : Nat} (ho : VG.Proof.X448.X86_64.Slot o)
    (ha : VG.Proof.X448.X86_64.Slot a) (hb : VG.Proof.X448.X86_64.Slot b) :
    WP isa (.block (sub o a b)) s fun s' =>
      VG.Proof.X448.X86_64.Op base o s s' ∧ VG.Proof.X448.X86_64.F s'.mem base o = VG.Proof.X448.X86_64.F s.mem base a - VG.Proof.X448.X86_64.F s.mem base b := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  have ho' : o + 56 ≤ 1536 := ho
  simp only [sub, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.loads_ok hs a W VG.Proof.X448.X86_64.W_nodup (by decide) (by rw [VG.Proof.X448.X86_64.W_len]; omega))
    fun s1 ⟨_, v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff, VG.Proof.X448.X86_64.words_eq]
  refine WP.mono (VG.Proof.X448.X86_64.sub_chain_ok W s1 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] _ _
    (VG.Proof.X448.X86_64.word s1.mem base b) _ (fun _ h => h) VG.Proof.X448.X86_64.W_nodup rfl (VG.Proof.X448.X86_64.stable_sc hs1 (by decide) (by omega))
    (VG.Proof.X448.X86_64.stable_scs hs1 (by decide) _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)))
    fun s2 ⟨c0, hc0, e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.carryOut_ok s2 hc0) fun s3 ⟨e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.unfold_ok s3 (by rw [e3]; cases c0 <;> decide)) fun s4 ⟨c1, hc1, e4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.carryOut_ok s4 hc1) fun s5 ⟨e5, k5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.unfold_ok s5 (by rw [e5]; cases c1 <;> decide)) fun s6 ⟨c2, _, e6, k6⟩ => ?_
  have hs6 := ((((hs1.of_keeps k2 (by decide)).of_keeps k3 (by decide)).of_keeps k4
    (by decide)).of_keeps k5 (by decide)).of_keeps k6 (by decide)
  refine WP.mono (VG.Proof.X448.X86_64.stores_ok hs6 o W (by rw [VG.Proof.X448.X86_64.W_len]; omega)) fun s7 ⟨e7, o7, g7, rd7, wr7⟩ => ?_
  rw [VG.Proof.X448.X86_64.W_len] at e7 o7
  have K : VG.Proof.X448.X86_64.Keeps VG.Proof.X448.X86_64.clob s s6 := (k1.mono VG.Proof.X448.X86_64.W_clob).trans <| (k2.mono (by decide)).trans <|
    (k3.mono (by decide)).trans <| (k4.mono (by decide)).trans <| (k5.mono (by decide)).trans
      (k6.mono (by decide))
  refine ⟨⟨fun r hr => (g7 r).trans (K.1 r hr), rd7.trans K.2.2.1, wr7.trans K.2.2.2,
    by rw [← K.2.1]; exact o7.left ACC 112⟩, toFe_sub ?_⟩
  have w32 : VG.Proof.X448.X86_64.rv s3 W = VG.Proof.X448.X86_64.rv s2 W := k3.rv_eq (by decide)
  have w54 : VG.Proof.X448.X86_64.rv s5 W = VG.Proof.X448.X86_64.rv s4 W := k5.rv_eq (by decide)
  rw [VG.Proof.X448.X86_64.len64_7, VG.Proof.X448.X86_64.W_lit, VG.Proof.X448.X86_64.wv_words, v1, VG.Proof.X448.X86_64.W_len, k1.2.1] at e2
  rw [e3, w32] at e4
  rw [e5, w54] at e6
  have l2 := VG.Proof.X448.X86_64.rv_lt s2 W; have l4 := VG.Proof.X448.X86_64.rv_lt s4 W; have l6 := VG.Proof.X448.X86_64.rv_lt s6 W
  rw [VG.Proof.X448.X86_64.len_W] at l2 l4 l6
  have b0 := Bool.toNat_le c0; have b1 := Bool.toNat_le c1; have b2 := Bool.toNat_le c2
  have hc2 : c2.toNat = 0 := by
    rcases Nat.lt_or_ge c1.toNat 1 with h | h
    · omega
    · rcases Nat.lt_or_ge c2.toNat 1 with h' | h'
      · omega
      · exfalso; omega
  have hP := VG.Proof.X448.X86_64.P_eq
  have p0 : 2 ^ 448 * c0.toNat = P * c0.toNat + (2 ^ 224 + 1) * c0.toNat := by
    rw [hP, Nat.add_mul]
  have p1 : 2 ^ 448 * c1.toNat = P * c1.toNat + (2 ^ 224 + 1) * c1.toNat := by
    rw [hP, Nat.add_mul]
  have key : VG.Proof.X448.X86_64.rv s6 W + VG.Proof.X448.X86_64.fe s.mem base b = VG.Proof.X448.X86_64.fe s.mem base a + P * (c0.toNat + c1.toNat) := by
    rw [Nat.mul_add P]
    generalize P * c0.toNat = q0 at p0 ⊢
    generalize P * c1.toNat = q1 at p1 ⊢
    clear hP
    simp only [VG.Proof.X448.X86_64.fe] at e2 ⊢
    omega
  change (VG.Proof.X448.X86_64.mv s7.mem base o 7 + VG.Proof.X448.X86_64.fe s.mem base b) % P = _
  rw [e7, key, Nat.add_mul_mod_self_left]

theorem init_ok (s : State) (k : BitVec 32) :
    WP isa (.block (([.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)] : List Instr) ++
      W.map fun r => .mov32 r (.imm 0))) s fun s' =>
      VG.Proof.X448.X86_64.rv s' W = 0 ∧ s'.gpr .rbp = 0 ∧ s'.gpr .rcx = k.setWidth 64 ∧ VG.Proof.X448.X86_64.Keeps (.rcx :: .rbp :: W) s s' := by
  apply WP.of_runBlock
  simp only [W, List.map_cons, List.map_nil, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some, State.setReg32,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [VG.Proof.X448.X86_64.rv, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem ldStable_scs {X : List Reg} {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (hX : .rdi ∉ X) :
    ∀ ds : List Nat, (∀ d ∈ ds, d + 8 ≤ 8192) →
      List.Forall₂ (VG.Proof.X448.X86_64.LdStable X s) (ds.map fun d => .mov .rax (.mem (sc d)))
        (ds.map fun d => VG.Proof.X448.X86_64.word s.mem base d)
  | [], _ => .nil
  | d :: ds, h => .cons (VG.Proof.X448.X86_64.ldStable_sc hs hX (h d List.mem_cons_self))
      (VG.Proof.X448.X86_64.ldStable_scs hs hX ds fun d' hd => h d' (List.mem_cons_of_mem _ hd))

/-- `[o] = k · [a]`, for `k < 2¹⁶`. -/
theorem mulSmall_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {o a : Nat} (ho : VG.Proof.X448.X86_64.Slot o)
    (ha : VG.Proof.X448.X86_64.Slot a) {k : BitVec 32} (hk : k.toNat < 2 ^ 16) :
    WP isa (.block (mulSmall o a k)) s fun s' =>
      VG.Proof.X448.X86_64.Op base o s s' ∧ VG.Proof.X448.X86_64.fe s'.mem base o % P = k.toNat * VG.Proof.X448.X86_64.fe s.mem base a % P := by
  have ha' : a + 56 ≤ 1536 := ha
  have ho' : o + 56 ≤ 1536 := ho
  simp only [mulSmall, List.append_assoc]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.init_ok s k) fun s1 ⟨z1, b1, c1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff, show (List.range 7).map (fun i => Instr.mov .rax (.mem (sc (a + 8 * i)))) =
    [a, a + 8, a + 16, a + 24, a + 32, a + 40, a + 48].map fun d => .mov .rax (.mem (sc d)) from rfl]
  refine WP.mono (VG.Proof.X448.X86_64.mulSteps_ok [.rax, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s1 W _
    _ s1 (Keeps.refl _ _) (by decide) (by decide) (by decide) rfl
    (VG.Proof.X448.X86_64.ldStable_scs hs1 (by decide) _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)))
    fun s2 ⟨e2, k2⟩ => ?_
  rw [VG.Proof.X448.X86_64.len_W, z1, b1, c1, VG.Proof.X448.X86_64.wv_words', k1.2.1] at e2
  have hk' : (k.setWidth 64).toNat = k.toNat := VG.Proof.X448.X86_64.toNat_setWidth_32_64 k
  rw [hk', VG.Proof.X448.X86_64.toNat_zero64] at e2
  rw [WP.block_append_iff]
  have hs2 := hs1.of_keeps k2 (by decide)
  refine WP.mono (show WP isa (.block [.mov .r15 (.reg .rbp)]) s2 fun s' =>
      s'.gpr .r15 = s2.gpr .rbp ∧ VG.Proof.X448.X86_64.Keeps [.r15] s2 s' by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, Option.map_some,
      RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr]) fun s3 ⟨e3, k3⟩ => ?_
  have hlt := VG.Proof.X448.X86_64.fe_lt s.mem base a
  have hb : (s2.gpr .rbp).toNat < 2 ^ 16 := by
    have h2 := Nat.mul_lt_mul'' hk hlt
    generalize k.toNat * VG.Proof.X448.X86_64.fe s.mem base a = X at e2 h2
    generalize (2 : Nat) ^ 448 = Q at e2 h2
    have h1 : Q * (s2.gpr .rbp).toNat ≤ X := by omega
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h1 (Nat.mul_comm (2 ^ 16) Q ▸ h2))
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.fold2_ok s3 (by rw [e3]; omega)) fun s4 ⟨e4, k4⟩ => ?_
  have hs4 := (hs2.of_keeps k3 (by decide)).of_keeps k4 (by decide)
  refine WP.mono (VG.Proof.X448.X86_64.stores_ok hs4 o W (by rw [VG.Proof.X448.X86_64.W_len]; omega)) fun s5 ⟨e5, o5, g5, rd5, wr5⟩ => ?_
  rw [VG.Proof.X448.X86_64.W_len] at e5 o5
  have K : VG.Proof.X448.X86_64.Keeps VG.Proof.X448.X86_64.clob s s4 := (k1.mono (by decide)).trans <| (k2.mono (by decide)).trans <|
    (k3.mono (by decide)).trans (k4.mono (by decide))
  refine ⟨⟨fun r hr => (g5 r).trans (K.1 r hr), rd5.trans K.2.2.1, wr5.trans K.2.2.2,
    by rw [← K.2.1]; exact o5.left ACC 112⟩, ?_⟩
  have w32 : VG.Proof.X448.X86_64.rv s3 W = VG.Proof.X448.X86_64.rv s2 W := k3.rv_eq (by decide)
  change VG.Proof.X448.X86_64.mv s5.mem base o 7 % P = _
  rw [e5, e4, w32, e3, e2, Nat.zero_add]

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Bits`. -/
section

/-!
# X448 on x86-64: the bits of the scalar

`bits` stores bit `j` of byte `i` of the scalar at byte `8i + j` of `BITS`,
then the clamped bits; so byte `t` of `BITS` is bit `t` of the decoded scalar
(`scalar_bit`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

/-- The body of `bits`' loop. -/
def bitsBody : List Instr :=
  [.movzx8 .rax { base := .rsi, index := some .rbx }] ++
    ((List.range 8).flatMap fun j =>
      [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
      [.alu .and .rdx (.imm 1),
        .store8 (bitAt j) .rdx]) ++
    [.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 56)]

theorem bitsBody_eq : VG.Proof.X448.X86_64.bitsBody =
    [.movzx8 .rax { base := .rsi, index := some .rbx },
    .mov .rdx (.reg .rax),
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 0) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 1,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 1) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 2,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 2) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 3,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 3) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 4,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 4) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 5,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 5) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 6,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 6) .rdx,
    .mov .rdx (.reg .rax),
    .shift .shr .rdx 7,
    .alu .and .rdx (.imm 1),
    .store8 (bitAt 7) .rdx,
    .alu .add .rbx (.imm 1),
    .alu .cmp .rbx (.imm 56)] := rfl

theorem bits_eq : bits = .seq (.block [.mov32 .rbx (.imm 0)]) (.seq (.loop (.block VG.Proof.X448.X86_64.bitsBody) .ne)
    (.block [.mov32 .rax (.imm 0), .store8 (sc BITS) .rax, .store8 (sc (BITS + 1)) .rax,
      .mov32 .rax (.imm 1), .store8 (sc (BITS + 447)) .rax])) := rfl

theorem ea_scalar (s : State) {k : Addr} (hk : s.gpr .rsi = k) {i : Nat}
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) :
    s.ea { base := .rsi, index := some .rbx } = k + BitVec.ofNat 64 i := by
  simp only [State.ea, hk, hb]
  rw [BitVec.mul_one, show BitVec.ofInt 64 (0 : Int) = BitVec.ofNat 64 0 from rfl, BitVec.add_zero]

theorem ea_bitAt (s : State) (j : Nat) :
    s.ea (bitAt j) = s.gpr .rdi + s.gpr .rbx * BitVec.ofNat 64 8 + BitVec.ofNat 64 (BITS + j) := by
  simp only [State.ea, bitAt, BitVec.ofInt_natCast]

theorem addr_bit (base : Addr) (i j : Nat) :
    base + BitVec.ofNat 64 i * BitVec.ofNat 64 8 + BitVec.ofNat 64 (BITS + j) =
      VG.Proof.X448.X86_64.off base (BITS + (8 * i + j)) := by
  rw [← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

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
  · simp only [Mem.writeW, Mem.write, Nat.reduceDiv, VG.Proof.X448.X86_64.sub_toNat_lt_one, h, ite_false]

theorem off_eq_iff (base : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) :
    VG.Proof.X448.X86_64.off base d = VG.Proof.X448.X86_64.off base e ↔ d = e := by
  constructor
  · intro h
    have := congrArg (fun x => VG.Proof.X448.X86_64.ofs base x) h
    simp only [VG.Proof.X448.X86_64.ofs_off' base hd, VG.Proof.X448.X86_64.ofs_off' base he] at this
    exact this
  · intro h; rw [h]

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    (((b.setWidth 64 >>> j) &&& BitVec.signExtend 64 (1 : BitVec 32)).setWidth 8 : BitVec 8) =
      BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by decide +kernel

/-- Bit `j` of `rax` (a byte) into `BITS[8 rbx + j]`. -/
def bitJ (j : Nat) : List Instr :=
  [.mov .rdx (.reg .rax)] ++ (if j = 0 then [] else [.shift .shr .rdx j]) ++
    [.alu .and .rdx (.imm 1), .store8 (bitAt j) .rdx]

theorem bitJ_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {i : Nat} (hi : i < 56)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {b : BitVec 8} (ha : s.gpr .rax = b.setWidth 64)
    {j : Nat} (hj : j < 8) :
    WP isa (.block (VG.Proof.X448.X86_64.bitJ j)) s fun s' =>
      (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (VG.Proof.X448.X86_64.off base (BITS + (8 * i + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) := by
  have w : InRegions s.wr (VG.Proof.X448.X86_64.off base (BITS + (8 * i + j))) 1 :=
    ⟨_, hs.wr, VG.Proof.X448.X86_64.contains_sc (by simp only [BITS]; omega)⟩
  have e := VG.Proof.X448.X86_64.bit_byte b j hj
  apply WP.of_runBlock
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [VG.Proof.X448.X86_64.bitJ, ite_true, List.nil_append, List.cons_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, VG.X86_64.readSrc, execAlu, State.store8, VG.Proof.X448.X86_64.ea_bitAt, RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg,
      RegUpd.mem_arithFlags, hs.rdi, hb, ha, VG.Proof.X448.X86_64.addr_bit, w, ite_false, reduceCtorEq, Option.map_some,
      Option.bind_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun r hr => ?_, rfl, by trivial, ?_⟩
    · simp only [hr, ite_false]
    · rw [← e]; rfl
  · simp only [VG.Proof.X448.X86_64.bitJ, show ¬j = 0 by omega, ite_false, List.nil_append, List.cons_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, execShift, State.store8,
    VG.Proof.X448.X86_64.ea_bitAt, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_setFlags, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags,
    RegUpd.mem_arithFlags, hs.rdi, hb, ha, VG.Proof.X448.X86_64.addr_bit, w, show 1 ≤ j ∧ j ≤ 63 from ⟨hj0, by omega⟩,
    ite_true, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    and_self]
    refine ⟨fun r hr => ?_, rfl, by trivial, ?_⟩
    · simp only [hr, ite_false]
    · rw [← e]

theorem writeW8_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (hd : d < 2 ^ 64) {x : Addr}
    (hx : VG.Proof.X448.X86_64.ofs base x ≠ d) : (m.writeW (VG.Proof.X448.X86_64.off base d) v) x = m x := by
  rw [VG.Proof.X448.X86_64.writeW8_apply, ite_eq_right_iff.mpr]
  intro h; subst h; exact absurd (VG.Proof.X448.X86_64.ofs_off' base hd) hx

theorem bitsBody_eq' : VG.Proof.X448.X86_64.bitsBody = ([.movzx8 .rax { base := .rsi, index := some .rbx }] : List Instr) ++
    (VG.Proof.X448.X86_64.bitJ 0 ++ (VG.Proof.X448.X86_64.bitJ 1 ++ (VG.Proof.X448.X86_64.bitJ 2 ++ (VG.Proof.X448.X86_64.bitJ 3 ++ (VG.Proof.X448.X86_64.bitJ 4 ++ (VG.Proof.X448.X86_64.bitJ 5 ++ (VG.Proof.X448.X86_64.bitJ 6 ++ (VG.Proof.X448.X86_64.bitJ 7 ++
      ([.alu .add .rbx (.imm 1), .alu .cmp .rbx (.imm 56)] : List Instr))))))))) := by
  rw [VG.Proof.X448.X86_64.bitsBody_eq]; rfl

theorem inc_eq (i : Nat) :
    BitVec.ofNat 64 i + BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (i + 1) := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add]

theorem cmp56 : ∀ i < 56,
    (BitVec.ofNat 64 (i + 1) - BitVec.signExtend 64 (56 : BitVec 32) == 0) = decide (i + 1 = 56) := by
  decide +kernel

theorem bitsBody_ok {s : State} {base k : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (hk : s.gpr .rsi = k)
    {i : Nat} (hi : i < 56) (hb : s.gpr .rbx = BitVec.ofNat 64 i)
    (hkr : InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 i) 1) :
    WP isa (.block VG.Proof.X448.X86_64.bitsBody) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (i + 1) ∧ s'.zf = some (decide (i + 1 = 56)) ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ j < 8, s'.mem (VG.Proof.X448.X86_64.off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (k + BitVec.ofNat 64 i)).toNat >>> j) &&& 1)) ∧
      VG.Proof.X448.X86_64.Outside base (BITS + 8 * i) 8 s.mem s'.mem := by
  rw [VG.Proof.X448.X86_64.bitsBody_eq', WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movzx8 .rax { base := .rsi, index := some .rbx }]) s
      (fun s' => s'.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 ∧
        (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X448.X86_64.ea_scalar s hk hb, State.load8, hkr,
      ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩)
    fun s₀ ⟨a0, g0, m0, rd0, wr0⟩ => ?_
  have hs₀ : VG.Proof.X448.X86_64.Scr s₀ base := ⟨(g0 _ (by decide)).trans hs.rdi, wr0 ▸ hs.wr, hs.nowrap⟩
  have hb₀ : s₀.gpr .rbx = BitVec.ofNat 64 i := (g0 _ (by decide)).trans hb
  -- The eight bits, each kept by the ones after it.
  have keep : ∀ {x y : State}, (∀ r, r ≠ .rdx → y.gpr r = x.gpr r) → y.rd = x.rd → y.wr = x.wr →
      VG.Proof.X448.X86_64.Scr x base → x.gpr .rbx = BitVec.ofNat 64 i → x.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 →
      VG.Proof.X448.X86_64.Scr y base ∧ y.gpr .rbx = BitVec.ofNat 64 i ∧ y.gpr .rax = (s.mem (k + BitVec.ofNat 64 i)).setWidth 64 :=
    fun g _ wr hx hbx hax => ⟨⟨(g _ (by decide)).trans hx.rdi, wr ▸ hx.wr, hx.nowrap⟩,
      (g _ (by decide)).trans hbx, (g _ (by decide)).trans hax⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.bitJ_ok hs₀ hi hb₀ a0 (j := 0) (by omega)) fun s₁ ⟨g1, rd1, wr1, m1⟩ => ?_
  obtain ⟨hs₁, hb₁, ha₁⟩ := keep g1 rd1 wr1 hs₀ hb₀ a0
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.bitJ_ok hs₁ hi hb₁ ha₁ (j := 1) (by omega)) fun s₂ ⟨g2, rd2, wr2, m2⟩ => ?_
  obtain ⟨hs₂, hb₂, ha₂⟩ := keep g2 rd2 wr2 hs₁ hb₁ ha₁
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.bitJ_ok hs₂ hi hb₂ ha₂ (j := 2) (by omega)) fun s₃ ⟨g3, rd3, wr3, m3⟩ => ?_
  obtain ⟨hs₃, hb₃, ha₃⟩ := keep g3 rd3 wr3 hs₂ hb₂ ha₂
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.bitJ_ok hs₃ hi hb₃ ha₃ (j := 3) (by omega)) fun s₄ ⟨g4, rd4, wr4, m4⟩ => ?_
  obtain ⟨hs₄, hb₄, ha₄⟩ := keep g4 rd4 wr4 hs₃ hb₃ ha₃
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.bitJ_ok hs₄ hi hb₄ ha₄ (j := 4) (by omega)) fun s₅ ⟨g5, rd5, wr5, m5⟩ => ?_
  obtain ⟨hs₅, hb₅, ha₅⟩ := keep g5 rd5 wr5 hs₄ hb₄ ha₄
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.bitJ_ok hs₅ hi hb₅ ha₅ (j := 5) (by omega)) fun s₆ ⟨g6, rd6, wr6, m6⟩ => ?_
  obtain ⟨hs₆, hb₆, ha₆⟩ := keep g6 rd6 wr6 hs₅ hb₅ ha₅
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.bitJ_ok hs₆ hi hb₆ ha₆ (j := 6) (by omega)) fun s₇ ⟨g7, rd7, wr7, m7⟩ => ?_
  obtain ⟨hs₇, hb₇, ha₇⟩ := keep g7 rd7 wr7 hs₆ hb₆ ha₆
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.bitJ_ok hs₇ hi hb₇ ha₇ (j := 7) (by omega)) fun s₈ ⟨g8, rd8, wr8, m8⟩ => ?_
  obtain ⟨hs₈, hb₈, ha₈⟩ := keep g8 rd8 wr8 hs₇ hb₇ ha₇
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hb₈, VG.Proof.X448.X86_64.inc_eq,
    ite_true, RegUpd.zf_arithFlags, RegUpd.rd_arithFlags, RegUpd.rd_setReg, RegUpd.wr_arithFlags,
    RegUpd.wr_setReg, RegUpd.mem_arithFlags, RegUpd.mem_setReg, VG.Proof.X448.X86_64.cmp56 i hi]
  have hm : s₀.mem = s.mem := m0
  refine ⟨trivial, trivial, fun r hr => ?_, ?_, ?_, fun j hj => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ite_eq_right hr.2.2, g8 r hr.2.1, g7 r hr.2.1, g6 r hr.2.1, g5 r hr.2.1, g4 r hr.2.1, g3 r hr.2.1,
      g2 r hr.2.1, g1 r hr.2.1, g0 r hr.1]
  · rw [rd8, rd7, rd6, rd5, rd4, rd3, rd2, rd1, rd0]
  · rw [wr8, wr7, wr6, wr5, wr4, wr3, wr2, wr1, wr0]
  · rw [m8, m7, m6, m5, m4, m3, m2, m1]
    have ne : ∀ a b, a < 8 → b < 8 → a ≠ b →
        VG.Proof.X448.X86_64.off base (BITS + (8 * i + a)) ≠ VG.Proof.X448.X86_64.off base (BITS + (8 * i + b)) := by
      intro a b ha hb hab h
      rw [VG.Proof.X448.X86_64.off_eq_iff base (by simp only [BITS]; omega) (by simp only [BITS]; omega)] at h
      omega
    have ne' : ∀ a b, a < 8 → b < 8 → a ≠ b →
        (VG.Proof.X448.X86_64.off base (BITS + (8 * i + a)) = VG.Proof.X448.X86_64.off base (BITS + (8 * i + b))) = False :=
      fun a b ha hb hab => eq_false (ne a b ha hb hab)
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [VG.Proof.X448.X86_64.writeW8_apply, ite_true, ne', ite_false]
  · intro x hx
    have hd : ∀ j < 8, VG.Proof.X448.X86_64.ofs base x ≠ BITS + (8 * i + j) := fun j hj h => by omega
    have hb : ∀ j < 8, BITS + (8 * i + j) < 2 ^ 64 := fun j hj => by simp only [BITS]; omega
    rw [m8, m7, m6, m5, m4, m3, m2, m1, VG.Proof.X448.X86_64.writeW8_outside _ _ _ (hb 7 (by omega)) (hd 7 (by omega)),
      VG.Proof.X448.X86_64.writeW8_outside _ _ _ (hb 6 (by omega)) (hd 6 (by omega)),
      VG.Proof.X448.X86_64.writeW8_outside _ _ _ (hb 5 (by omega)) (hd 5 (by omega)),
      VG.Proof.X448.X86_64.writeW8_outside _ _ _ (hb 4 (by omega)) (hd 4 (by omega)),
      VG.Proof.X448.X86_64.writeW8_outside _ _ _ (hb 3 (by omega)) (hd 3 (by omega)),
      VG.Proof.X448.X86_64.writeW8_outside _ _ _ (hb 2 (by omega)) (hd 2 (by omega)),
      VG.Proof.X448.X86_64.writeW8_outside _ _ _ (hb 1 (by omega)) (hd 1 (by omega)),
      VG.Proof.X448.X86_64.writeW8_outside _ _ _ (hb 0 (by omega)) (hd 0 (by omega)), hm]

/-- `bits`' loop invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : VG.Proof.X448.X86_64.Scr s base
  rsi : s.gpr .rsi = k
  rbx : s.gpr .rbx = BitVec.ofNat 64 i
  gpr : ∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : VG.Proof.X448.X86_64.Outside base BITS 448 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (VG.Proof.X448.X86_64.off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 56, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ VG.Proof.X448.X86_64.ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 56 → VG.Proof.X448.X86_64.BInv base k s₀ s i →
      WP isa (.loop (.block VG.Proof.X448.X86_64.bitsBody) .ne) s fun s' => VG.Proof.X448.X86_64.BInv base k s₀ s' 56 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block VG.Proof.X448.X86_64.bitsBody) (c := .ne)
    (Q := fun s' => VG.Proof.X448.X86_64.BInv base k s₀ s' 56)
    (fun m (s : State) => ∃ i, m = 56 - i ∧ i < 56 ∧ VG.Proof.X448.X86_64.BInv base k s₀ s i) ?_ (56 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (VG.Proof.X448.X86_64.bitsBody_ok hb.scr hb.rsi hi hb.rbx (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', g', rd', wr', bits', o'⟩ => ?_
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : VG.Proof.X448.X86_64.BInv base k s₀ s' (i + 1) := by
    refine ⟨⟨(g' _ (by decide)).trans hb.scr.rdi, wr' ▸ hb.scr.wr, hb.scr.nowrap⟩,
      (g' _ (by decide)).trans hb.rsi, b', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [VG.Proof.X448.X86_64.ofs_off' base (by simp only [BITS]; omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, z', Option.map_some]
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
theorem bits_ok {s : State} {base k : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (hk : s.gpr .rsi = k)
    (hkr : ∀ q < 56, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 56, 8192 ≤ VG.Proof.X448.X86_64.ofs base (k + BitVec.ofNat 64 q)) :
    WP isa bits s fun s' =>
      (∀ r, r ∉ [Reg.rax, .rdx, .rbx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X448.X86_64.Outside base BITS 448 s.mem s'.mem ∧
      ∀ t < 448, s'.mem (VG.Proof.X448.X86_64.off base (BITS + t)) =
        BitVec.ofNat 8 (VG.Proof.X448.bit (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s.mem k 56)) t) := by
  rw [VG.Proof.X448.X86_64.bits_eq]
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rbx (.imm 0)]) s (fun s' =>
      VG.Proof.X448.X86_64.BInv base k s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
      State.setReg32, Option.some.injEq, exists_eq_left']
    refine ⟨⟨hs.rdi, hs.wr, hs.nowrap⟩, hk, rfl, fun r hr => ?_, rfl, rfl, Outside.refl _ _ _ _,
      fun t ht => absurd ht (by omega)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.2.2, ite_false]) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.X86_64.bitsLoop_ok hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_)
  have hs₂ := h₂.scr
  have w : ∀ d, d + 1 ≤ 8192 → InRegions s₂.wr (VG.Proof.X448.X86_64.off base d) 1 :=
    fun d hd => ⟨_, hs₂.wr, VG.Proof.X448.X86_64.contains_sc hd⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
    State.setReg32, State.store8, VG.Proof.X448.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    hs₂.rdi, w BITS (by simp only [BITS]; omega), w (BITS + 1) (by simp only [BITS]; omega),
    w (BITS + 447) (by simp only [BITS]; omega),
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, by rw [RegUpd.rd_setReg]; exact h₂.rd, h₂.wr, fun x hx => ?_, fun t ht => ?_⟩
  · have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    simp only [hr'.1, ite_false]
    exact h₂.gpr r hr
  · have o : ∀ d, BITS ≤ d → d < BITS + 448 → VG.Proof.X448.X86_64.ofs base x ≠ d := fun d h₁ h₂ h => by omega
    rw [VG.Proof.X448.X86_64.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 447) (by omega) (by omega)),
      VG.Proof.X448.X86_64.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o (BITS + 1) (by omega) (by omega)),
      VG.Proof.X448.X86_64.writeW8_outside _ _ _ (by simp only [BITS]; omega) (o BITS (by omega) (by omega))]
    exact h₂.mem x hx
  · rw [scalar_bit (length_bytesAt _ _ _) ht]
    simp (disch := simp only [BITS]; omega) only [VG.Proof.X448.X86_64.writeW8_apply, VG.Proof.X448.X86_64.off_eq_iff, Nat.add_left_cancel_iff,
      Nat.add_eq_left]
    rcases (by omega : t = 0 ∨ t = 1 ∨ t = 447 ∨ (2 ≤ t ∧ t < 447)) with
      rfl | rfl | rfl | ⟨h₃, h₄⟩
    · rfl
    · rfl
    · rfl
    · simp only [show t ≠ 447 by omega, show t ≠ 1 by omega, show t ≠ 0 by omega,
        show ¬t < 2 by omega, ite_false]
      rw [h₂.bits t (by omega), VG.Proof.X448.X86_64.getD_bytesAt _ _ (by omega)]

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Swap`. -/
section

/-!
# X448 on x86-64: the conditional swap

An XOR mask exchanges the words without a branch or an address depending on
the swap bit, word by word (`wp_range_flatMap`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

def mask (sw : Bool) : BitVec 64 := if sw then BitVec.allOnes 64 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 64) :
    a ^^^ ((a ^^^ b) &&& VG.Proof.X448.X86_64.mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& VG.Proof.X448.X86_64.mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [VG.Proof.X448.X86_64.mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [VG.Proof.X448.X86_64.mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The registers (and regions) of `s'` are those of `s` but for `rs`. -/
def KeepsR (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem KeepsR.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X448.X86_64.KeepsR rs s₁ s₂)
    (h₂ : VG.Proof.X448.X86_64.KeepsR rs s₂ s₃) : VG.Proof.X448.X86_64.KeepsR rs s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem Scr.of_keepsR {rs : List Reg} {s s' : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base)
    (h : VG.Proof.X448.X86_64.KeepsR rs s s') (hr : .rdi ∉ rs) : VG.Proof.X448.X86_64.Scr s' base :=
  ⟨(h.1 _ hr).trans hs.rdi, h.2.2 ▸ hs.wr, hs.nowrap⟩

theorem swapStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {x y i : Nat}
    (hx : x + 56 ≤ 1536) (hy : y + 56 ≤ 1536) (hi : i < 7) {sw : Bool} (hc : s.gpr .rcx = VG.Proof.X448.X86_64.mask sw) :
    WP isa (.block
      [.mov .rax (.mem (sc (x + 8 * i))), .mov .rdx (.mem (sc (y + 8 * i))),
        .mov .r8 (.reg .rax), .alu .xor .r8 (.reg .rdx), .alu .and .r8 (.reg .rcx),
        .alu .xor .rax (.reg .r8), .alu .xor .rdx (.reg .r8),
        .store (sc (x + 8 * i)) .rax, .store (sc (y + 8 * i)) .rdx]) s fun t =>
      t.mem = (s.mem.writeW (VG.Proof.X448.X86_64.off base (x + 8 * i))
        (if sw then VG.Proof.X448.X86_64.word s.mem base (y + 8 * i) else VG.Proof.X448.X86_64.word s.mem base (x + 8 * i))).writeW
        (VG.Proof.X448.X86_64.off base (y + 8 * i)) (if sw then VG.Proof.X448.X86_64.word s.mem base (x + 8 * i) else VG.Proof.X448.X86_64.word s.mem base (y + 8 * i)) ∧
      VG.Proof.X448.X86_64.KeepsR [.rax, .rdx, .r8] s t := by
  have lx := hs.read (d := x + 8 * i) (n := 8) (by omega)
  have ly := hs.read (d := y + 8 * i) (n := 8) (by omega)
  have wx := hs.write (d := x + 8 * i) (n := 8) (by omega)
  have wy := hs.write (d := y + 8 * i) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, VG.Proof.X448.X86_64.ea_sc,
    State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, hs.rdi, hc, lx, ly, wx, wy, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [(VG.Proof.X448.X86_64.xor_sel sw _ _).1, (VG.Proof.X448.X86_64.xor_sel sw _ _).2]
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

theorem word_write (m : Mem) (base : Addr) {d e : Nat} (hd : d + 8 ≤ 8192) (he : e + 8 ≤ 8192)
    (hde : d + 8 ≤ e ∨ e + 8 ≤ d ∨ e = d) (v : BitVec 64) :
    VG.Proof.X448.X86_64.word (m.writeW (VG.Proof.X448.X86_64.off base d) v) base e = if e = d then v else VG.Proof.X448.X86_64.word m base e := by
  by_cases h : e = d
  · rw [ite_eq_left h, h, VG.Proof.X448.X86_64.word, Mem.readW_writeW_self64]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

/-- Swap the seven words under the mask, and nothing else. -/
theorem cswap_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {x y : Nat} (hx : x + 56 ≤ 1536)
    (hy : y + 56 ≤ 1536) (hxy : x + 56 ≤ y ∨ y + 56 ≤ x) {sw : Bool} (hc : s.gpr .rcx = VG.Proof.X448.X86_64.mask sw) :
    WP isa (.block (cswap x y)) s fun t =>
      (∀ i < 7, VG.Proof.X448.X86_64.word t.mem base (x + 8 * i) =
        if sw then VG.Proof.X448.X86_64.word s.mem base (y + 8 * i) else VG.Proof.X448.X86_64.word s.mem base (x + 8 * i)) ∧
      (∀ i < 7, VG.Proof.X448.X86_64.word t.mem base (y + 8 * i) =
        if sw then VG.Proof.X448.X86_64.word s.mem base (x + 8 * i) else VG.Proof.X448.X86_64.word s.mem base (y + 8 * i)) ∧
      VG.Proof.X448.X86_64.Outside2 base x 56 y 56 s.mem t.mem ∧ VG.Proof.X448.X86_64.KeepsR [.rax, .rdx, .r8] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, VG.Proof.X448.X86_64.word t.mem base (x + 8 * i) =
      if sw then VG.Proof.X448.X86_64.word s.mem base (y + 8 * i) else VG.Proof.X448.X86_64.word s.mem base (x + 8 * i)) ∧
    (∀ i < n, VG.Proof.X448.X86_64.word t.mem base (y + 8 * i) =
      if sw then VG.Proof.X448.X86_64.word s.mem base (x + 8 * i) else VG.Proof.X448.X86_64.word s.mem base (y + 8 * i)) ∧
    VG.Proof.X448.X86_64.Outside2 base x (8 * n) y (8 * n) s.mem t.mem ∧ VG.Proof.X448.X86_64.KeepsR [.rax, .rdx, .r8] s t
  have step : ∀ n t, n < 7 → inv n t → WP isa (.block
      [.mov .rax (.mem (sc (x + 8 * n))), .mov .rdx (.mem (sc (y + 8 * n))),
        .mov .r8 (.reg .rax), .alu .xor .r8 (.reg .rdx), .alu .and .r8 (.reg .rcx),
        .alu .xor .rax (.reg .r8), .alu .xor .rdx (.reg .r8),
        .store (sc (x + 8 * n)) .rax, .store (sc (y + 8 * n)) .rdx]) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tc := (tk.1 .rcx (by decide)).trans hc
    refine WP.mono (VG.Proof.X448.X86_64.swapStep_ok (hs.of_keepsR tk (by decide)) hx hy hn tc) fun u ⟨um, uk⟩ => ?_
    have ex : VG.Proof.X448.X86_64.word t.mem base (x + 8 * n) = VG.Proof.X448.X86_64.word s.mem base (x + 8 * n) :=
      tm.word (by omega) (by omega) (by omega)
    have ey : VG.Proof.X448.X86_64.word t.mem base (y + 8 * n) = VG.Proof.X448.X86_64.word s.mem base (y + 8 * n) :=
      tm.word (by omega) (by omega) (by omega)
    refine ⟨fun j hj => ?_, fun j hj => ?_, ?_, tk.trans uk⟩
    · rw [um, VG.Proof.X448.X86_64.word_write _ _ (by omega) (by omega) (by omega),
        VG.Proof.X448.X86_64.word_write _ _ (by omega) (by omega) (by omega)]
      by_cases h : j = n
      · subst h
        rw [ite_eq_right (by omega), ite_eq_left rfl, ex, ey]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact tx j (by omega)
    · rw [um, VG.Proof.X448.X86_64.word_write _ _ (by omega) (by omega) (by omega)]
      by_cases h : j = n
      · subst h
        rw [ite_eq_left rfl, ex, ey]
      · rw [ite_eq_right (by omega), VG.Proof.X448.X86_64.word_write _ _ (by omega) (by omega) (by omega),
          ite_eq_right (by omega)]
        exact ty j (by omega)
    · intro p hp hq
      rw [um, VG.Proof.X448.X86_64.writeW_outside _ _ _ (by omega : y + 8 * n + 8 < 2 ^ 64) p (by omega),
        VG.Proof.X448.X86_64.writeW_outside _ _ _ (by omega : x + 8 * n + 8 < 2 ^ 64) p (by omega)]
      exact tm p (by omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 7) inv step 7 (by decide) s
    ⟨fun _ hi => by omega, fun _ hi => by omega, Outside2.refl _ _ _ _ _ _,
      ⟨fun _ _ => rfl, rfl, rfl⟩⟩

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Env`. -/
section

/-!
# X448 on x86-64: the working space as slots

The working space as 22 slots of 64 bytes (`E`), each read as a field
element: each field operation updates one slot (`Function.update`) and the
swap two, so that a sequence of operations is a chain of updates that `simp`
evaluates at any slot. The field operations change no byte outside the slots
and the product's words, `[64, 1648)`.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

abbrev Index := Fin 22

/-- Environments: the working space's slots. -/
abbrev Env := VG.Proof.X448.X86_64.Index → Spec.X448.Fe

/-- The working space as 22 field elements. -/
def E (m : Mem) (base : Addr) (i : VG.Proof.X448.X86_64.Index) : Spec.X448.Fe := VG.Proof.X448.X86_64.F m base (VG.Impl.X448.X86_64.slot i.val)

theorem slot_lt (i : VG.Proof.X448.X86_64.Index) : VG.Impl.X448.X86_64.slot i.val + 56 ≤ ACC := by
  have := i.isLt; simp only [VG.Impl.X448.X86_64.slot, ACC]; omega

theorem slot_ge (i : VG.Proof.X448.X86_64.Index) : 64 ≤ VG.Impl.X448.X86_64.slot i.val := by simp only [VG.Impl.X448.X86_64.slot]; omega

theorem slot_sep {i j : VG.Proof.X448.X86_64.Index} (h : i ≠ j) :
    VG.Impl.X448.X86_64.slot i.val + 56 ≤ VG.Impl.X448.X86_64.slot j.val ∨ VG.Impl.X448.X86_64.slot j.val + 56 ≤ VG.Impl.X448.X86_64.slot i.val := by
  have : i.val ≠ j.val := fun e => h (Fin.ext e)
  simp only [VG.Impl.X448.X86_64.slot]; omega

theorem E_update {base : Addr} {m m' : Mem} {o : VG.Proof.X448.X86_64.Index}
    (h : VG.Proof.X448.X86_64.Outside2 base (VG.Impl.X448.X86_64.slot o.val) 56 ACC 112 m m') :
    VG.Proof.X448.X86_64.E m' base = Function.update (VG.Proof.X448.X86_64.E m base) o (VG.Proof.X448.X86_64.F m' base (VG.Impl.X448.X86_64.slot o.val)) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp [VG.Proof.X448.X86_64.E]
  · rw [Function.update_of_ne hi]
    have := VG.Proof.X448.X86_64.slot_lt i
    simp only [ACC] at this
    show toFe (VG.Proof.X448.X86_64.mv m' base (VG.Impl.X448.X86_64.slot i.val) 7) = toFe (VG.Proof.X448.X86_64.mv m base (VG.Impl.X448.X86_64.slot i.val) 7)
    rw [h.mv (VG.Proof.X448.X86_64.slot_sep hi) (Or.inl (by simp only [ACC]; omega)) (by omega)]

/-- What the field operations keep: the registers but `clob`, the regions,
and the memory outside `[64, 1648)`. -/
structure Keep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ VG.Proof.X448.X86_64.clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : VG.Proof.X448.X86_64.Outside base 64 1584 s.mem s'.mem

theorem Keep.refl (base : Addr) (s : State) : VG.Proof.X448.X86_64.Keep base s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem Keep.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X448.X86_64.Keep base s₁ s₂) (h₂ : VG.Proof.X448.X86_64.Keep base s₂ s₃) :
    VG.Proof.X448.X86_64.Keep base s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.mem.trans h₂.mem⟩

theorem Keep.scr {base : Addr} {s s' : State} (h : VG.Proof.X448.X86_64.Keep base s s') (hs : VG.Proof.X448.X86_64.Scr s base) : VG.Proof.X448.X86_64.Scr s' base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

theorem Op.keep {base : Addr} {o : VG.Proof.X448.X86_64.Index} {s s' : State} (h : VG.Proof.X448.X86_64.Op base (VG.Impl.X448.X86_64.slot o.val) s s') :
    VG.Proof.X448.X86_64.Keep base s s' :=
  ⟨h.gpr, h.rd, h.wr, h.mem.outside (VG.Proof.X448.X86_64.slot_ge o) (by have := VG.Proof.X448.X86_64.slot_lt o; simp only [ACC] at *; omega)
    (by decide) (by decide)⟩

/-! ## The field multiplications -/

/-- What the rest of the proof needs of the field multiplications `fld`:
each writes the field element at `o` and the product's words, and nothing
else of the working space, and changes only the registers `clob` (`Op`). -/
structure FieldOk (fld : Field) : Prop where
  mul : ∀ {s : State} {base : Addr}, VG.Proof.X448.X86_64.Scr s base → ∀ {o a b : Nat}, VG.Proof.X448.X86_64.Slot o → VG.Proof.X448.X86_64.Slot a → VG.Proof.X448.X86_64.Slot b →
    WP isa (.block (fld.mul o a b)) s fun s' =>
      VG.Proof.X448.X86_64.Op base o s s' ∧ VG.Proof.X448.X86_64.F s'.mem base o = VG.Proof.X448.X86_64.F s.mem base a * VG.Proof.X448.X86_64.F s.mem base b
  sqr : ∀ {s : State} {base : Addr}, VG.Proof.X448.X86_64.Scr s base → ∀ {o a : Nat}, VG.Proof.X448.X86_64.Slot o → VG.Proof.X448.X86_64.Slot a →
    WP isa (.block (fld.sqr o a)) s fun s' =>
      VG.Proof.X448.X86_64.Op base o s s' ∧ VG.Proof.X448.X86_64.F s'.mem base o = VG.Proof.X448.X86_64.F s.mem base a * VG.Proof.X448.X86_64.F s.mem base a
  a24 : ∀ {s : State} {base : Addr}, VG.Proof.X448.X86_64.Scr s base → ∀ {o a : Nat}, VG.Proof.X448.X86_64.Slot o → VG.Proof.X448.X86_64.Slot a →
    WP isa (.block (fld.a24 o a)) s fun s' =>
      VG.Proof.X448.X86_64.Op base o s s' ∧ VG.Proof.X448.X86_64.F s'.mem base o = Spec.X448.a24 * VG.Proof.X448.X86_64.F s.mem base a

theorem baseline_ok : VG.Proof.X448.X86_64.FieldOk baseline where
  mul hs _ _ _ ho ha hb := VG.Proof.X448.X86_64.mul_ok hs ho ha hb
  sqr hs _ _ ho ha := VG.Proof.X448.X86_64.sqr_ok hs ho ha
  a24 hs _ _ ho ha := WP.mono (VG.Proof.X448.X86_64.mulSmall_ok hs ho ha (k := a24) (by decide)) fun _ ⟨h, e⟩ =>
    ⟨h, toFe_a24 e⟩

/-! ## The field operations on the slots -/

variable {fld : Field} (hf : VG.Proof.X448.X86_64.FieldOk fld)

def opMul (o a b : VG.Proof.X448.X86_64.Index) (e : VG.Proof.X448.X86_64.Env) : VG.Proof.X448.X86_64.Env := Function.update e o (e a * e b)
def opAdd (o a b : VG.Proof.X448.X86_64.Index) (e : VG.Proof.X448.X86_64.Env) : VG.Proof.X448.X86_64.Env := Function.update e o (e a + e b)
def opSub (o a b : VG.Proof.X448.X86_64.Index) (e : VG.Proof.X448.X86_64.Env) : VG.Proof.X448.X86_64.Env := Function.update e o (e a - e b)
def opA24 (o a : VG.Proof.X448.X86_64.Index) (e : VG.Proof.X448.X86_64.Env) : VG.Proof.X448.X86_64.Env := Function.update e o (Spec.X448.a24 * e a)
def opSwap (x y : VG.Proof.X448.X86_64.Index) (sw : Bool) (e : VG.Proof.X448.X86_64.Env) : VG.Proof.X448.X86_64.Env :=
  Function.update (Function.update e x (if sw then e y else e x)) y (if sw then e x else e y)

include hf in
theorem mulE {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (o a b : VG.Proof.X448.X86_64.Index) :
    WP isa (.block (fld.mul (VG.Impl.X448.X86_64.slot o.val) (VG.Impl.X448.X86_64.slot a.val) (VG.Impl.X448.X86_64.slot b.val))) s fun s' =>
      VG.Proof.X448.X86_64.Keep base s s' ∧ VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.X448.X86_64.opMul o a b (VG.Proof.X448.X86_64.E s.mem base) :=
  WP.mono (hf.mul hs (VG.Proof.X448.X86_64.slot_lt o) (VG.Proof.X448.X86_64.slot_lt a) (VG.Proof.X448.X86_64.slot_lt b)) fun _ ⟨h, e⟩ =>
    ⟨h.keep, by rw [VG.Proof.X448.X86_64.E_update h.mem, e]; rfl⟩

include hf in
theorem sqrE {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (o a : VG.Proof.X448.X86_64.Index) :
    WP isa (.block (fld.sqr (VG.Impl.X448.X86_64.slot o.val) (VG.Impl.X448.X86_64.slot a.val))) s fun s' =>
      VG.Proof.X448.X86_64.Keep base s s' ∧ VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.X448.X86_64.opMul o a a (VG.Proof.X448.X86_64.E s.mem base) :=
  WP.mono (hf.sqr hs (VG.Proof.X448.X86_64.slot_lt o) (VG.Proof.X448.X86_64.slot_lt a)) fun _ ⟨h, e⟩ =>
    ⟨h.keep, by rw [VG.Proof.X448.X86_64.E_update h.mem, e]; rfl⟩

theorem addE {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (o a b : VG.Proof.X448.X86_64.Index) :
    WP isa (.block (add (VG.Impl.X448.X86_64.slot o.val) (VG.Impl.X448.X86_64.slot a.val) (VG.Impl.X448.X86_64.slot b.val))) s fun s' =>
      VG.Proof.X448.X86_64.Keep base s s' ∧ VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.X448.X86_64.opAdd o a b (VG.Proof.X448.X86_64.E s.mem base) :=
  WP.mono (VG.Proof.X448.X86_64.add_ok hs (VG.Proof.X448.X86_64.slot_lt o) (VG.Proof.X448.X86_64.slot_lt a) (VG.Proof.X448.X86_64.slot_lt b)) fun _ ⟨h, e⟩ =>
    ⟨h.keep, by rw [VG.Proof.X448.X86_64.E_update h.mem, e]; rfl⟩

theorem subE {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (o a b : VG.Proof.X448.X86_64.Index) :
    WP isa (.block (sub (VG.Impl.X448.X86_64.slot o.val) (VG.Impl.X448.X86_64.slot a.val) (VG.Impl.X448.X86_64.slot b.val))) s fun s' =>
      VG.Proof.X448.X86_64.Keep base s s' ∧ VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.X448.X86_64.opSub o a b (VG.Proof.X448.X86_64.E s.mem base) :=
  WP.mono (VG.Proof.X448.X86_64.sub_ok hs (VG.Proof.X448.X86_64.slot_lt o) (VG.Proof.X448.X86_64.slot_lt a) (VG.Proof.X448.X86_64.slot_lt b)) fun _ ⟨h, e⟩ =>
    ⟨h.keep, by rw [VG.Proof.X448.X86_64.E_update h.mem, e]; rfl⟩

include hf in
theorem a24E {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (o a : VG.Proof.X448.X86_64.Index) :
    WP isa (.block (fld.a24 (VG.Impl.X448.X86_64.slot o.val) (VG.Impl.X448.X86_64.slot a.val))) s fun s' =>
      VG.Proof.X448.X86_64.Keep base s s' ∧ VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.X448.X86_64.opA24 o a (VG.Proof.X448.X86_64.E s.mem base) :=
  WP.mono (hf.a24 hs (VG.Proof.X448.X86_64.slot_lt o) (VG.Proof.X448.X86_64.slot_lt a)) fun _ ⟨h, e⟩ =>
    ⟨h.keep, by rw [VG.Proof.X448.X86_64.E_update h.mem, e]; rfl⟩

theorem fe_sel {m m' : Mem} {base : Addr} {x y : Nat} {sw : Bool}
    (h : ∀ i < 7, VG.Proof.X448.X86_64.word m' base (x + 8 * i) =
      if sw then VG.Proof.X448.X86_64.word m base (y + 8 * i) else VG.Proof.X448.X86_64.word m base (x + 8 * i)) :
    VG.Proof.X448.X86_64.fe m' base x = if sw then VG.Proof.X448.X86_64.fe m base y else VG.Proof.X448.X86_64.fe m base x := by
  rw [VG.Proof.X448.X86_64.fe, VG.Proof.X448.X86_64.mv7, VG.Proof.X448.X86_64.fe, VG.Proof.X448.X86_64.fe, VG.Proof.X448.X86_64.mv7, VG.Proof.X448.X86_64.mv7]
  cases sw
  · simp only [Bool.false_eq_true, ite_false] at h ⊢
    exact VG.Proof.X448.X86_64.val7_congr fun i hi => by rw [h i hi]
  · simp only [ite_true] at h ⊢
    exact VG.Proof.X448.X86_64.val7_congr fun i hi => by rw [h i hi]

theorem cswapE {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (x y : VG.Proof.X448.X86_64.Index) (hxy : x ≠ y) {sw : Bool}
    (hm : s.gpr .rcx = VG.Proof.X448.X86_64.mask sw) :
    WP isa (.block (cswap (VG.Impl.X448.X86_64.slot x.val) (VG.Impl.X448.X86_64.slot y.val))) s fun s' =>
      VG.Proof.X448.X86_64.Keep base s s' ∧ s'.gpr .rcx = s.gpr .rcx ∧ VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.X448.X86_64.opSwap x y sw (VG.Proof.X448.X86_64.E s.mem base) := by
  have hx := VG.Proof.X448.X86_64.slot_lt x; have hy := VG.Proof.X448.X86_64.slot_lt y
  have gx := VG.Proof.X448.X86_64.slot_ge x; have gy := VG.Proof.X448.X86_64.slot_ge y
  simp only [ACC] at hx hy
  refine WP.mono (VG.Proof.X448.X86_64.cswap_ok hs hx hy (VG.Proof.X448.X86_64.slot_sep hxy) hm) fun s' ⟨fx, fy, out, k⟩ => ?_
  refine ⟨⟨fun r hr => k.1 r fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;> decide), k.2.1, k.2.2,
    out.outside gx (by omega) gy (by omega)⟩, k.1 _ (by decide), ?_⟩
  funext i
  have ex : VG.Proof.X448.X86_64.E s'.mem base x = if sw then VG.Proof.X448.X86_64.E s.mem base y else VG.Proof.X448.X86_64.E s.mem base x := by
    simp only [VG.Proof.X448.X86_64.E, VG.Proof.X448.X86_64.F, VG.Proof.X448.X86_64.fe_sel fx]; cases sw <;> rfl
  have ey : VG.Proof.X448.X86_64.E s'.mem base y = if sw then VG.Proof.X448.X86_64.E s.mem base x else VG.Proof.X448.X86_64.E s.mem base y := by
    simp only [VG.Proof.X448.X86_64.E, VG.Proof.X448.X86_64.F, VG.Proof.X448.X86_64.fe_sel fy]; cases sw <;> rfl
  by_cases hiy : i = y
  · subst hiy; rw [VG.Proof.X448.X86_64.opSwap, Function.update_self]; exact ey
  · rw [VG.Proof.X448.X86_64.opSwap, Function.update_of_ne hiy]
    by_cases hix : i = x
    · subst hix; rw [Function.update_self]; exact ex
    · rw [Function.update_of_ne hix]
      have hi := VG.Proof.X448.X86_64.slot_lt i
      simp only [ACC] at hi
      show toFe (VG.Proof.X448.X86_64.mv s'.mem base (VG.Impl.X448.X86_64.slot i.val) 7) = toFe (VG.Proof.X448.X86_64.mv s.mem base (VG.Impl.X448.X86_64.slot i.val) 7)
      rw [out.mv (VG.Proof.X448.X86_64.slot_sep hix) (VG.Proof.X448.X86_64.slot_sep hiy) (by omega)]

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Freeze`. -/
section

/-!
# X448 on x86-64: the full reduction

`freeze a` leaves `[a] mod p` in `r8–r14`: `y = x + 1 + 2²²⁴` (a `fold` of
`r15 = 1`) carries out of 448 bits exactly when `x ≥ p`, and then
`y mod 2⁴⁴⁸ = x - p`, which the mask `r15 = -carry` selects word by word.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448
open VG.Spec.X448 (P)

theorem sel_word (sw : Bool) (x y : BitVec 64) :
    ((y ^^^ x) &&& VG.Proof.X448.X86_64.mask sw) ^^^ x = if sw then y else x := by
  cases sw
  · show (y ^^^ x) &&& 0#64 ^^^ x = x
    rw [BitVec.and_zero, BitVec.zero_xor]
  · simp only [VG.Proof.X448.X86_64.mask, ite_true, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self,
      BitVec.xor_zero]

theorem w_ne_rax : ∀ i < 7, w i ≠ .rax := by decide
theorem w_ne_r15 : ∀ i < 7, w i ≠ .r15 := by decide
theorem w_mem : ∀ i < 7, w i ∈ W := by decide

/-- A word: `r = sw ? r : [d]`, with the mask in `r15`. -/
theorem selStep_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {d : Nat} (hd : d + 8 ≤ 8192)
    {r : Reg} (hr : r ≠ .rax) (hr' : r ≠ .r15) {sw : Bool} (hm : s.gpr .r15 = VG.Proof.X448.X86_64.mask sw) :
    WP isa (.block [.mov .rax (.mem (sc d)), .alu .xor r (.reg .rax),
      .alu .and r (.reg .r15), .alu .xor r (.reg .rax)]) s fun s' =>
      s'.gpr r = (if sw then s.gpr r else VG.Proof.X448.X86_64.word s.mem base d) ∧
      VG.Proof.X448.X86_64.KeepsR [.rax, r] s s' ∧ s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, Option.bind_some,
    VG.Proof.X448.X86_64.load_sc hs hd, Option.map_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hr'), RegUpd.gpr_arithFlags,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hr),
    RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.r15 = Reg.rax), RegUpd.mem_setReg,
    RegUpd.mem_arithFlags,
    Option.some.injEq, exists_eq_left', hm]
  refine ⟨VG.Proof.X448.X86_64.sel_word _ _ _, ⟨fun r' hr'' => ?_, rfl, rfl⟩, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr''
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr''.2, RegUpd.gpr_arithFlags,
    RegUpd.gpr_setReg_of_ne _ _ hr''.1]

theorem w_inj : ∀ i < 7, ∀ j < 7, w i = w j → i = j := by decide

/-- The selection of every word. -/
theorem sel_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {a : Nat} (ha : a + 56 ≤ 8192)
    {sw : Bool} (hm : s.gpr .r15 = VG.Proof.X448.X86_64.mask sw) :
    WP isa (.block ((List.range 7).flatMap fun i =>
      [.mov .rax (.mem (sc (a + 8 * i))), .alu .xor (w i) (.reg .rax),
        .alu .and (w i) (.reg .r15), .alu .xor (w i) (.reg .rax)])) s fun s' =>
      (∀ i < 7, s'.gpr (w i) = if sw then s.gpr (w i) else VG.Proof.X448.X86_64.word s.mem base (a + 8 * i)) ∧
      VG.Proof.X448.X86_64.KeepsR (.rax :: W) s s' ∧ s'.mem = s.mem := by
  let inv := fun n (t : State) =>
    (∀ i < 7, t.gpr (w i) = if i < n then (if sw then s.gpr (w i) else VG.Proof.X448.X86_64.word s.mem base (a + 8 * i))
      else s.gpr (w i)) ∧ VG.Proof.X448.X86_64.KeepsR (.rax :: W) s t ∧ t.mem = s.mem
  have step : ∀ n t, n < 7 → inv n t → WP isa (.block
      [.mov .rax (.mem (sc (a + 8 * n))), .alu .xor (w n) (.reg .rax),
        .alu .and (w n) (.reg .r15), .alu .xor (w n) (.reg .rax)]) t (inv (n + 1)) := by
    intro n t hn ⟨tw, tk, tm⟩
    have ht : VG.Proof.X448.X86_64.Scr t base := hs.of_keepsR tk (by decide)
    have tr : t.gpr .r15 = VG.Proof.X448.X86_64.mask sw := (tk.1 _ (by decide)).trans hm
    refine WP.mono (VG.Proof.X448.X86_64.selStep_ok ht (d := a + 8 * n) (by omega) (VG.Proof.X448.X86_64.w_ne_rax n hn) (VG.Proof.X448.X86_64.w_ne_r15 n hn) tr)
      fun u ⟨uw, uk, um⟩ => ⟨fun i hi => ?_, ?_, um.trans tm⟩
    · by_cases h : i = n
      · subst h
        rw [uw, tw i hi, tm, ite_eq_right (Nat.lt_irrefl i), ite_eq_left (Nat.lt_succ_self i)]
      · have hne : w i ∉ [Reg.rax, w n] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨VG.Proof.X448.X86_64.w_ne_rax i hi, fun e => h (VG.Proof.X448.X86_64.w_inj i hi n hn e)⟩
        rw [uk.1 _ hne, tw i hi]
        by_cases h' : i < n
        · simp only [h', show i < n + 1 by omega, ite_true]
        · simp only [h', show ¬i < n + 1 by omega, ite_false]
    · refine tk.trans ⟨fun r hr => uk.1 r fun h => hr ?_, uk.2.1, uk.2.2⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (VG.Proof.X448.X86_64.w_mem n hn)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv step 7 (by decide) s
    ⟨fun i hi => by rw [ite_eq_right (by omega)], ⟨fun _ _ => rfl, rfl, rfl⟩, rfl⟩)
    fun t ⟨tw, tk, tm⟩ => ⟨fun i hi => by rw [tw i hi, ite_eq_left hi], tk, tm⟩

/-- `freeze a`: `r8–r14` hold `[a] mod p`. -/
theorem freeze_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {a : Nat} (ha : VG.Proof.X448.X86_64.Slot a) :
    WP isa (.block (freeze a)) s fun s' =>
      VG.Proof.X448.X86_64.rv s' W = VG.Proof.X448.X86_64.fe s.mem base a % P ∧ VG.Proof.X448.X86_64.Keeps (.rax :: .r15 :: W) s s' := by
  have ha' : a + 56 ≤ 1536 := ha
  simp only [freeze, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.mov32_ok s .r15 1) fun s1 ⟨e1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.loads_ok hs1 a W VG.Proof.X448.X86_64.W_nodup (by decide) (by rw [VG.Proof.X448.X86_64.W_len]; omega))
    fun s2 ⟨_, v2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have r15 : (s2.gpr .r15).toNat = 1 := by rw [k2.1 _ (by decide), e1]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.fold_ok s2 (by rw [r15]; decide)) fun s3 ⟨c, hc, e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.alu .sbb .r15 (.reg .r15)]) s3 fun s' =>
      s'.gpr .r15 = VG.Proof.X448.X86_64.mask c ∧ VG.Proof.X448.X86_64.Keeps [.r15] s3 s' by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu, hc,
      Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, Option.some.injEq,
      exists_eq_left', BitVec.sub_self]
    refine ⟨by cases c <;> decide, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]) fun s4 ⟨m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  refine WP.mono (VG.Proof.X448.X86_64.sel_ok hs4 (a := a) (by omega) m4) fun s5 ⟨w5, k5, mem5⟩ => ⟨?_, ?_⟩
  · have mm4 : s4.mem = s.mem := k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1))
    rw [VG.Proof.X448.X86_64.W_len, k1.2.1] at v2
    rw [v2, r15] at e3
    have w43 : VG.Proof.X448.X86_64.rv s4 W = VG.Proof.X448.X86_64.rv s3 W := k4.rv_eq (by decide)
    have hP := VG.Proof.X448.X86_64.P_eq
    have hlt := VG.Proof.X448.X86_64.fe_lt s.mem base a
    change VG.Proof.X448.X86_64.rv s3 W + _ = VG.Proof.X448.X86_64.fe s.mem base a + _ at e3
    cases c with
    | false =>
      have : VG.Proof.X448.X86_64.rv s5 W = VG.Proof.X448.X86_64.fe s.mem base a := by
        rw [VG.Proof.X448.X86_64.rvW, VG.Proof.X448.X86_64.fe, VG.Proof.X448.X86_64.mv7]
        refine VG.Proof.X448.X86_64.val7_congr fun i hi => ?_
        rw [w5 i hi]; simp only [Bool.false_eq_true, ite_false, mm4]
      rw [this, Nat.mod_eq_of_lt]
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e3
      have := VG.Proof.X448.X86_64.rv_lt s3 W; rw [VG.Proof.X448.X86_64.len_W] at this
      omega
    | true =>
      have : VG.Proof.X448.X86_64.rv s5 W = VG.Proof.X448.X86_64.rv s3 W := by
        rw [VG.Proof.X448.X86_64.rvW, VG.Proof.X448.X86_64.rvW]
        refine VG.Proof.X448.X86_64.val7_congr fun i hi => ?_
        rw [w5 i hi, ite_eq_left rfl, k4.1 _ (by simp [VG.Proof.X448.X86_64.w_ne_r15 i hi])]
      simp only [Bool.toNat_true, Nat.mul_one] at e3
      rw [this, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, not_or] at hr
      rw [k5.1 r (by simp [hr.1, hr.2.2]), k4.1 r (by simp [hr.2.1]),
        k3.1 r (by simp [hr.1, hr.2.2]), k2.1 r hr.2.2, k1.1 r (by simp [hr.2.1])]
    · rw [mem5, k4.2.1, k3.2.1, k2.2.1, k1.2.1]
    · rw [k5.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
    · rw [k5.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Setup`. -/
section

/-!
# X448 on x86-64: reading the arguments

`setup` saves the callee-saved registers at the start of the working space,
reads the u-coordinate (seven words: all 448 bits are used), and sets the
ladder's variables to their initial values.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = VG.Proof.X448.X86_64.off (s.gpr b) d := rfl

/-- A number of bytes is its words. -/
theorem leNum_bytesAt_mv (m : Mem) (p : Addr) :
    ∀ (o n : Nat), X25519.leNum (Spec.X448.bytesAt m (VG.Proof.X448.X86_64.off p o) (8 * n)) = VG.Proof.X448.X86_64.mv m p o n
  | _, 0 => by simp [Spec.X448.bytesAt, X25519.leNum, VG.Proof.X448.X86_64.mv]
  | o, n + 1 => by
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, bytesAt_add, X25519.leNum_append, length_bytesAt,
      leNum_bytesAt_read, VG.Proof.X448.X86_64.mv, show VG.Proof.X448.X86_64.off p o + BitVec.ofNat 64 8 = VG.Proof.X448.X86_64.off p (o + 8) by
        simp only [VG.Proof.X448.X86_64.off, BitVec.add_assoc, BitVec.ofNat_add],
      VG.Proof.X448.X86_64.leNum_bytesAt_mv m p (o + 8) n]
    simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

theorem decode_mv (m : Mem) (p : Addr) :
    Spec.X448.decodeUCoordinate (Spec.X448.bytesAt m p 56) = VG.Proof.X448.X86_64.mv m p 0 7 := by
  have h := VG.Proof.X448.X86_64.leNum_bytesAt_mv m p 0 7
  rw [show VG.Proof.X448.X86_64.off p 0 = p from BitVec.add_zero p] at h
  rw [decodeUCoordinate_eq (length_bytesAt _ _ _)]
  exact h

/-- The u-coordinate, as seven words. -/
theorem loadU_ok (s : State) {p : Addr} (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 56 → InRegions (s.rd ++ s.wr) (VG.Proof.X448.X86_64.off p d) 8) :
    WP isa (.block ((List.range 7).map fun i => .mov (w i) (.mem (at_ .rdx (8 * i))))) s fun s' =>
      VG.Proof.X448.X86_64.rv s' W = VG.Proof.X448.X86_64.mv s.mem p 0 7 ∧ VG.Proof.X448.X86_64.Keeps W s s' := by
  apply WP.of_runBlock
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, w, W, List.getD_cons_succ,
    List.getD_cons_zero, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, State.load64,
    VG.Proof.X448.X86_64.ea_at, hp, hr 0 (by omega), hr 8 (by omega), hr 16 (by omega), hr 24 (by omega),
    hr 32 (by omega), hr 40 (by omega), hr 48 (by omega), Nat.reduceMul,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [VG.Proof.X448.X86_64.rv, VG.Proof.X448.X86_64.mv, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Nat.reduceAdd]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2, ite_false]

/-! ## Saving the callee-saved registers -/

/-- The callee-saved registers of `g`, saved at the start of the working space. -/
abbrev Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop := Spill.Saved m base g saved

theorem saved_lt : ∀ rd ∈ saved, rd.2 + 8 ≤ 48 := by decide

theorem Saved.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : VG.Proof.X448.X86_64.Saved base g m)
    {o n : Nat} (ho : VG.Proof.X448.X86_64.Outside base o n m m') (h48 : 48 ≤ o) : VG.Proof.X448.X86_64.Saved base g m' := fun rd hrd => by
  have := VG.Proof.X448.X86_64.saved_lt rd hrd
  exact (ho.word (by omega) (by omega)).trans (h rd hrd)

theorem save_ok {s : State} {base : Addr} (hc : s.gpr .rcx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block save) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Proof.X448.X86_64.Outside base 0 48 s.mem s'.mem ∧
      VG.Proof.X448.X86_64.Saved base s.gpr s'.mem := by
  refine WP.mono (Spill.save_ok .rcx saved s fun p hp => ?_) fun s' ⟨hg, hrd, hwr, hm⟩ =>
    ⟨hg, hrd, hwr, ?_, ?_⟩
  · have := VG.Proof.X448.X86_64.saved_lt p hp; rw [hc]; exact ⟨_, hw, VG.Proof.X448.X86_64.contains_sc (by omega)⟩
  · rw [hm, hc]
    intro x hx
    refine Spill.saveMem_frame_base _ _ _ _ VG.Proof.X448.X86_64.saved_lt (by decide) x fun r hr hx' => ?_
    rw [List.mem_singleton.mp hr] at hx'
    simp only [Region.Contains, VG.Proof.X448.X86_64.ofs] at hx hx'
    omega
  · rw [hm, hc]; exact Spill.saveMem_saved _ _ _ _ (by decide)

/-! ## The initial values -/

theorem movs_ok (s : State) :
    WP isa (.block ([.mov .r15 (.reg .rdi), .mov .rdi (.reg .rcx)] : List Instr)) s fun s' =>
      s'.gpr .r15 = s.gpr .rdi ∧ s'.gpr .rdi = s.gpr .rcx ∧ VG.Proof.X448.X86_64.Keeps [.r15, .rdi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem consts_ok (s : State) :
    WP isa (.block ([.mov32 .rax (.imm 0), .mov32 .rdx (.imm 1)] : List Instr)) s fun s' =>
      s'.gpr .rax = 0 ∧ s'.gpr .rdx = 1 ∧ VG.Proof.X448.X86_64.Keeps [.rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem storeSwap_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) :
    WP isa (.block ([.store (sc SWAP) .rax] : List Instr)) s fun s' =>
      s'.mem = s.mem.writeW (VG.Proof.X448.X86_64.off base SWAP) (s.gpr .rax) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X448.X86_64.ea_sc, hs.rdi, State.store64,
    show InRegions s.wr (VG.Proof.X448.X86_64.off base SWAP) 8 from ⟨_, hs.wr, VG.Proof.X448.X86_64.contains_sc (by decide)⟩, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- Stores into a slot, as an update of the slots. -/
theorem stores_E {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (i : VG.Proof.X448.X86_64.Index) (rs : List Reg)
    (hl : rs.length = 7) :
    WP isa (.block (stores (slot i.val) rs)) s fun s' =>
      VG.Proof.X448.X86_64.E s'.mem base = Function.update (VG.Proof.X448.X86_64.E s.mem base) i (toFe (VG.Proof.X448.X86_64.rv s rs)) ∧
      VG.Proof.X448.X86_64.Outside base (slot i.val) 56 s.mem s'.mem ∧
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hi := VG.Proof.X448.X86_64.slot_lt i
  refine WP.mono (VG.Proof.X448.X86_64.stores_ok hs (slot i.val) rs (by rw [hl]; simp only [ACC] at hi; omega))
    fun s' ⟨e, o, g, rd, wr⟩ => ?_
  rw [hl] at e o
  refine ⟨?_, o, g, rd, wr⟩
  rw [VG.Proof.X448.X86_64.E_update (o.left ACC 112)]
  congr 1
  simp only [VG.Proof.X448.X86_64.F, VG.Proof.X448.X86_64.fe, e]

theorem setup_eq : setup = save ++ (([.mov .r15 (.reg .rdi), .mov .rdi (.reg .rcx)] : List Instr) ++
    ((List.range 7).map (fun i => .mov (w i) (.mem (at_ .rdx (8 * i)))) ++
    (stores X1 W ++ (stores X3 W ++ (([.mov32 .rax (.imm 0), .mov32 .rdx (.imm 1)] : List Instr) ++
    (stores X2 ([.rdx, .rax, .rax, .rax, .rax, .rax, .rax] : List Reg) ++
    (stores Z2 ([.rax, .rax, .rax, .rax, .rax, .rax, .rax] : List Reg) ++
    (stores Z3 ([.rdx, .rax, .rax, .rax, .rax, .rax, .rax] : List Reg) ++
    ([.store (sc SWAP) .rax] : List Instr))))))))) := by
  simp only [setup, List.append_assoc]

/-- `setup`: the ladder's initial state, from the u-coordinate at `p`. -/
theorem setup_ok {s : State} {base p : Addr} (hc : s.gpr .rcx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 56 → InRegions (s.rd ++ s.wr) (VG.Proof.X448.X86_64.off p d) 8)
    (hd : ∀ j < 56, 8192 ≤ VG.Proof.X448.X86_64.ofs base (VG.Proof.X448.X86_64.off p j)) :
    WP isa (.block setup) s fun s' =>
      VG.Proof.X448.X86_64.Scr s' base ∧ s'.gpr .r15 = s.gpr .rdi ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ VG.Proof.X448.X86_64.Outside base 0 8192 s.mem s'.mem ∧ VG.Proof.X448.X86_64.Saved base s.gpr s'.mem ∧
      VG.Proof.X448.X86_64.E s'.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      VG.Proof.X448.X86_64.E s'.mem base 1 = 1 ∧ VG.Proof.X448.X86_64.E s'.mem base 2 = 0 ∧
      VG.Proof.X448.X86_64.E s'.mem base 3 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      VG.Proof.X448.X86_64.E s'.mem base 4 = 1 ∧ VG.Proof.X448.X86_64.word s'.mem base SWAP = 0 := by
  rw [VG.Proof.X448.X86_64.setup_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.save_ok hc hw) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.movs_ok s₁) fun s₂ ⟨r15₂, rdi₂, k₂⟩ => ?_
  have hs₂ : VG.Proof.X448.X86_64.Scr s₂ base := ⟨by rw [rdi₂, g₁, hc], by rw [k₂.2.2.2, wr₁]; exact hw, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.loadU_ok s₂ (p := p) (by rw [k₂.1 _ (by decide), g₁, hp])
    fun d hd' => by rw [k₂.2.2.1, k₂.2.2.2, rd₁, wr₁]; exact hr d hd') fun s₃ ⟨u₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  -- The coordinate's bytes are outside the working space, which is all `save` wrote.
  have hu : Spec.X448.bytesAt s₂.mem p 56 = Spec.X448.bytesAt s.mem p 56 := by
    rw [k₂.2.1]
    simp only [Spec.X448.bytesAt]
    refine List.map_congr_left fun i hi => o₁ _ (Or.inr ?_)
    simp only [List.mem_range] at hi
    have := hd i hi
    exact Nat.le_trans (by decide) this
  rw [← VG.Proof.X448.X86_64.decode_mv, hu] at u₃
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.stores_E hs₃ 0 W rfl) fun s₄ ⟨e₄, o₄, g₄, rd₄, wr₄⟩ => ?_
  have hs₄ : VG.Proof.X448.X86_64.Scr s₄ base := ⟨(g₄ _).trans hs₃.rdi, wr₄ ▸ hs₃.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.stores_E hs₄ 3 W rfl) fun s₅ ⟨e₅, o₅, g₅, rd₅, wr₅⟩ => ?_
  have hs₅ : VG.Proof.X448.X86_64.Scr s₅ base := ⟨(g₅ _).trans hs₄.rdi, wr₅ ▸ hs₄.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.consts_ok s₅) fun s₆ ⟨rax₆, rdx₆, k₆⟩ => ?_
  have hs₆ : VG.Proof.X448.X86_64.Scr s₆ base := hs₅.of_keeps k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.stores_E hs₆ 1 _ rfl) fun s₇ ⟨e₇, o₇, g₇, rd₇, wr₇⟩ => ?_
  have hs₇ : VG.Proof.X448.X86_64.Scr s₇ base := ⟨(g₇ _).trans hs₆.rdi, wr₇ ▸ hs₆.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.stores_E hs₇ 2 _ rfl) fun s₈ ⟨e₈, o₈, g₈, rd₈, wr₈⟩ => ?_
  have hs₈ : VG.Proof.X448.X86_64.Scr s₈ base := ⟨(g₈ _).trans hs₇.rdi, wr₈ ▸ hs₇.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.stores_E hs₈ 4 _ rfl) fun s₉ ⟨e₉, o₉, g₉, rd₉, wr₉⟩ => ?_
  have hs₉ : VG.Proof.X448.X86_64.Scr s₉ base := ⟨(g₉ _).trans hs₈.rdi, wr₉ ▸ hs₈.wr, hn⟩
  refine WP.mono (VG.Proof.X448.X86_64.storeSwap_ok hs₉) fun s' ⟨m', g', rd', wr'⟩ => ?_
  have G : ∀ r, r ∉ [Reg.rax, .rdx] → s'.gpr r = s₃.gpr r := fun r hr => by
    rw [g', g₉, g₈, g₇, k₆.1 r hr, g₅, g₄]
  have e' : VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.X448.X86_64.E s₉.mem base := by
    funext i
    have := VG.Proof.X448.X86_64.slot_ge i; have := VG.Proof.X448.X86_64.slot_lt i
    simp only [VG.Proof.X448.X86_64.E, VG.Proof.X448.X86_64.F]
    rw [m', ((VG.Proof.X448.X86_64.writeW_outside _ _ _ (by decide)).fe (d := slot i.val) (Or.inr (by simp only [SWAP]; omega))
      (by simp only [ACC] at *; omega))]
  have one : toFe (VG.Proof.X448.X86_64.rv s₆ [.rdx, .rax, .rax, .rax, .rax, .rax, .rax]) = 1 := by
    simp only [VG.Proof.X448.X86_64.rv, rax₆, rdx₆]; rfl
  have zero : toFe (VG.Proof.X448.X86_64.rv s₇ [.rax, .rax, .rax, .rax, .rax, .rax, .rax]) = 0 := by
    simp only [VG.Proof.X448.X86_64.rv, g₇, rax₆]; rfl
  have one' : toFe (VG.Proof.X448.X86_64.rv s₈ [.rdx, .rax, .rax, .rax, .rax, .rax, .rax]) = 1 := by
    simp only [VG.Proof.X448.X86_64.rv, g₈, g₇, rax₆, rdx₆]; rfl
  have w₄ : VG.Proof.X448.X86_64.rv s₄ W = VG.Proof.X448.X86_64.rv s₃ W := VG.Proof.X448.X86_64.rv_congr fun r _ => g₄ r
  have o₃ : VG.Proof.X448.X86_64.Outside base 0 8192 s.mem s₃.mem := by
    rw [k₃.2.1, k₂.2.1]; exact o₁.mono (by omega) (by omega)
  have o' : VG.Proof.X448.X86_64.Outside base 48 1424 s₃.mem s'.mem := by
    have q : ∀ (i : VG.Proof.X448.X86_64.Index) {m m' : Mem}, VG.Proof.X448.X86_64.Outside base (slot i.val) 56 m m' →
        VG.Proof.X448.X86_64.Outside base 48 1424 m m' := fun i {_ _} h => Outside.mono h (by have := VG.Proof.X448.X86_64.slot_ge i; omega)
          (by have := i.isLt; simp only [slot]; omega)
    refine ((((q 0 o₄).trans (q 3 o₅)).trans ?_).trans ((q 1 o₇).trans ((q 2 o₈).trans (q 4 o₉)))).trans ?_
    · rw [k₆.2.1]; exact Outside.refl _ _ _ _
    · intro x hx
      rw [m']
      exact (VG.Proof.X448.X86_64.writeW_outside _ _ _ (by decide)).mono (by simp only [SWAP]; omega)
        (by simp only [SWAP]; omega) x hx
  refine ⟨⟨by rw [g']; exact hs₉.rdi, wr' ▸ hs₉.wr, hn⟩, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [G _ (by decide), k₃.1 _ (by decide), r15₂, g₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [G r (by simp [hr.1, hr.2.1]), k₃.1 r (by simp [W, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1]),
      k₂.1 r (by simp [hr.2.2.1, hr.2.2.2.2.2.2.2.2.2.2]), g₁]
  · rw [rd', rd₉, rd₈, rd₇, k₆.2.2.1, rd₅, rd₄, k₃.2.2.1, k₂.2.2.1, rd₁]
  · rw [wr', wr₉, wr₈, wr₇, k₆.2.2.2, wr₅, wr₄, k₃.2.2.2, k₂.2.2.2, wr₁]
  · exact o₃.trans (o'.mono (by omega) (by omega))
  · have sv : VG.Proof.X448.X86_64.Saved base s.gpr s₃.mem := by rw [k₃.2.1, k₂.2.1]; exact sv₁
    exact sv.outside o' (by omega)
  · rw [e', e₉, e₈, e₇, k₆.2.1, e₅, e₄]
    simp (config := {decide := true}) only [Function.update_apply, ite_true, ite_false]
    rw [one, zero, one', w₄, u₃]
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [m', VG.Proof.X448.X86_64.word_writeW_self, g₉, g₈, g₇, rax₆]

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Iter`. -/
section

/-!
# X448 on x86-64: the ladder

The start of an iteration (`stepPre`): the counter `rbx` counts down to the
bit `t`, whose byte of the array `BITS` is `k_t`; `swap ^ k_t` becomes the
mask in `rcx`, and `k_t` the new `swap` (a word at `SWAP`).
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

/-- The start of `step`. -/
def stepPre : List Instr :=
  [.alu .sub .rbx (.imm 1), .movzx8 .rax { base := .rdi, index := some .rbx, disp := BITS },
    .mov .rdx (.mem (sc SWAP)), .alu .xor .rdx (.reg .rax), .store (sc SWAP) .rax,
    .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)]

theorem ea_bits {s : State} {base : Addr} (hr : s.gpr .rdi = base) {t : Nat}
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) :
    s.ea { base := .rdi, index := some .rbx, disp := BITS } = VG.Proof.X448.X86_64.off base (BITS + t) := by
  simp only [State.ea, hr, hb, VG.Proof.X448.X86_64.off, BITS, BitVec.ofInt_natCast]
  rw [BitVec.mul_one, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm t 2048]

theorem mask_xor : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 64) - (BitVec.ofNat 64 a ^^^ (BitVec.ofNat 8 b).setWidth 64) =
      VG.Proof.X448.X86_64.mask (decide (a ^^^ b = 1)) := by decide

theorem stepPre_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {t : Nat} (ht : t < 448)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) {kt sw0 : Nat} (hk : kt < 2) (hsw : sw0 < 2)
    (hbit : s.mem (VG.Proof.X448.X86_64.off base (BITS + t)) = BitVec.ofNat 8 kt)
    (hswap : VG.Proof.X448.X86_64.word s.mem base SWAP = BitVec.ofNat 64 sw0) :
    WP isa (.block VG.Proof.X448.X86_64.stepPre) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.gpr .rcx = VG.Proof.X448.X86_64.mask (decide (sw0 ^^^ kt = 1)) ∧
      (∀ r, r ∉ [.rbx, .rax, .rdx, .rcx] → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (VG.Proof.X448.X86_64.off base SWAP) (BitVec.ofNat 64 kt) ∧ s'.xmm = s.xmm ∧
      s'.ymmHi = s.ymmHi := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 t := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hin : InRegions (s.rd ++ s.wr) (VG.Proof.X448.X86_64.off base (BITS + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X448.X86_64.contains_sc (by simp only [BITS]; omega)⟩
  have hw : InRegions s.wr (VG.Proof.X448.X86_64.off base SWAP) 8 := ⟨_, hs.wr, VG.Proof.X448.X86_64.contains_sc (by simp only [SWAP]; omega)⟩
  have hr : InRegions (s.rd ++ s.wr) (VG.Proof.X448.X86_64.off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X448.X86_64.contains_sc (by simp only [SWAP]; omega)⟩
  apply WP.of_runBlock
  simp only [VG.Proof.X448.X86_64.stepPre, runBlock_cons, runStep_some, exec, VG.X86_64.readSrc, execAlu, State.load8,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hb', Option.bind_some]
  rw [VG.Proof.X448.X86_64.ea_bits (base := base) (t := t) (by simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
                         ite_false, reduceCtorEq, hs.rdi]) (by simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg,
                         ite_true])]
  have hswap' : s.mem.readW (VG.Proof.X448.X86_64.off base SWAP) 64 = BitVec.ofNat 64 sw0 := hswap
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    State.load64, State.store64, VG.Proof.X448.X86_64.ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, hin, hbit, hr, hw, hswap', ite_true,
    ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', State.setReg32]
  have e0 : BitVec.setWidth 64 (0 : BitVec 32) = 0 := rfl
  have ek : BitVec.setWidth 64 (BitVec.ofNat 8 kt) = BitVec.ofNat 64 kt := by
    rcases (by omega : kt = 0 ∨ kt = 1) with rfl | rfl <;> rfl
  refine ⟨trivial, by rw [e0]; exact VG.Proof.X448.X86_64.mask_xor sw0 hsw kt hk, fun r hr => ?_, trivial, trivial,
    by rw [ek], rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

variable {fld : Field} (hf : VG.Proof.X448.X86_64.FieldOk fld)

def opsList (fld : Field) : List Instr :=
  cswap (VG.Impl.X448.X86_64.slot (1 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (3 : VG.Proof.X448.X86_64.Index).val) ++
  cswap (VG.Impl.X448.X86_64.slot (2 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (4 : VG.Proof.X448.X86_64.Index).val) ++
  add (VG.Impl.X448.X86_64.slot (5 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (1 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (2 : VG.Proof.X448.X86_64.Index).val) ++
  sub (VG.Impl.X448.X86_64.slot (6 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (1 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (2 : VG.Proof.X448.X86_64.Index).val) ++
  add (VG.Impl.X448.X86_64.slot (7 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (3 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (4 : VG.Proof.X448.X86_64.Index).val) ++
  sub (VG.Impl.X448.X86_64.slot (8 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (3 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (4 : VG.Proof.X448.X86_64.Index).val) ++
  fld.sqr (VG.Impl.X448.X86_64.slot (9 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (5 : VG.Proof.X448.X86_64.Index).val) ++
  fld.sqr (VG.Impl.X448.X86_64.slot (10 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (6 : VG.Proof.X448.X86_64.Index).val) ++
  fld.mul (VG.Impl.X448.X86_64.slot (12 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (8 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (5 : VG.Proof.X448.X86_64.Index).val) ++
  fld.mul (VG.Impl.X448.X86_64.slot (13 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (7 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (6 : VG.Proof.X448.X86_64.Index).val) ++
  sub (VG.Impl.X448.X86_64.slot (11 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (9 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (10 : VG.Proof.X448.X86_64.Index).val) ++
  sub (VG.Impl.X448.X86_64.slot (4 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (12 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (13 : VG.Proof.X448.X86_64.Index).val) ++
  add (VG.Impl.X448.X86_64.slot (3 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (12 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (13 : VG.Proof.X448.X86_64.Index).val) ++
  fld.a24 (VG.Impl.X448.X86_64.slot (2 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (11 : VG.Proof.X448.X86_64.Index).val) ++
  fld.sqr (VG.Impl.X448.X86_64.slot (4 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (4 : VG.Proof.X448.X86_64.Index).val) ++
  fld.sqr (VG.Impl.X448.X86_64.slot (3 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (3 : VG.Proof.X448.X86_64.Index).val) ++
  add (VG.Impl.X448.X86_64.slot (2 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (9 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (2 : VG.Proof.X448.X86_64.Index).val) ++
  fld.mul (VG.Impl.X448.X86_64.slot (4 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (0 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (4 : VG.Proof.X448.X86_64.Index).val) ++
  fld.mul (VG.Impl.X448.X86_64.slot (1 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (9 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (10 : VG.Proof.X448.X86_64.Index).val) ++
  fld.mul (VG.Impl.X448.X86_64.slot (2 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (11 : VG.Proof.X448.X86_64.Index).val) (VG.Impl.X448.X86_64.slot (2 : VG.Proof.X448.X86_64.Index).val)

theorem step_eq : VG.Impl.X448.X86_64.step fld = VG.Proof.X448.X86_64.stepPre ++ (VG.Proof.X448.X86_64.opsList fld ++ ([.alu .test .rbx (.reg .rbx)] : List Instr)) := by
  simp only [VG.Impl.X448.X86_64.step, VG.Proof.X448.X86_64.stepPre, VG.Proof.X448.X86_64.opsList, List.append_assoc]
  rfl

/-- The slots after the field operations of an iteration. -/
def stepEnv (sw : Bool) (e : VG.Proof.X448.X86_64.Env) : VG.Proof.X448.X86_64.Env :=
  VG.Proof.X448.X86_64.opMul 2 11 2 (VG.Proof.X448.X86_64.opMul 1 9 10 (VG.Proof.X448.X86_64.opMul 4 0 4 (VG.Proof.X448.X86_64.opAdd 2 9 2 (VG.Proof.X448.X86_64.opMul 3 3 3 (VG.Proof.X448.X86_64.opMul 4 4 4 (VG.Proof.X448.X86_64.opA24 2 11
    (VG.Proof.X448.X86_64.opAdd 3 12 13 (VG.Proof.X448.X86_64.opSub 4 12 13 (VG.Proof.X448.X86_64.opSub 11 9 10 (VG.Proof.X448.X86_64.opMul 13 7 6 (VG.Proof.X448.X86_64.opMul 12 8 5 (VG.Proof.X448.X86_64.opMul 10 6 6
    (VG.Proof.X448.X86_64.opMul 9 5 5 (VG.Proof.X448.X86_64.opSub 8 3 4 (VG.Proof.X448.X86_64.opAdd 7 3 4 (VG.Proof.X448.X86_64.opSub 6 1 2 (VG.Proof.X448.X86_64.opAdd 5 1 2 (VG.Proof.X448.X86_64.opSwap 2 4 sw
    (VG.Proof.X448.X86_64.opSwap 1 3 sw e)))))))))))))))))))

include hf in
/-- The field operations of an iteration, with the mask `rcx` of the swap
bit `sw`. -/
theorem ops_ok {s1 : State} {base : Addr} (hs1 : VG.Proof.X448.X86_64.Scr s1 base) {sw : Bool}
    (hm : s1.gpr .rcx = VG.Proof.X448.X86_64.mask sw) :
    WP isa (.block (VG.Proof.X448.X86_64.opsList fld)) s1 fun s' =>
      VG.Proof.X448.X86_64.Keep base s1 s' ∧ VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.X448.X86_64.stepEnv sw (VG.Proof.X448.X86_64.E s1.mem base) := by
  simp only [VG.Proof.X448.X86_64.opsList, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.cswapE hs1 1 3 (by decide) hm) fun s2 ⟨k2, c2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.cswapE hs2 2 4 (by decide) (c2.trans hm)) fun s3 ⟨k3, c3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.addE hs3 5 1 2) fun s4 ⟨k4, e4⟩ => ?_
  have hs4 := k4.scr hs3
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.subE hs4 6 1 2) fun s5 ⟨k5, e5⟩ => ?_
  have hs5 := k5.scr hs4
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.addE hs5 7 3 4) fun s6 ⟨k6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.subE hs6 8 3 4) fun s7 ⟨k7, e7⟩ => ?_
  have hs7 := k7.scr hs6
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.sqrE hf hs7 9 5) fun s8 ⟨k8, e8⟩ => ?_
  have hs8 := k8.scr hs7
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.sqrE hf hs8 10 6) fun s9 ⟨k9, e9⟩ => ?_
  have hs9 := k9.scr hs8
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.mulE hf hs9 12 8 5) fun s10 ⟨k10, e10⟩ => ?_
  have hs10 := k10.scr hs9
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.mulE hf hs10 13 7 6) fun s11 ⟨k11, e11⟩ => ?_
  have hs11 := k11.scr hs10
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.subE hs11 11 9 10) fun s12 ⟨k12, e12⟩ => ?_
  have hs12 := k12.scr hs11
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.subE hs12 4 12 13) fun s13 ⟨k13, e13⟩ => ?_
  have hs13 := k13.scr hs12
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.addE hs13 3 12 13) fun s14 ⟨k14, e14⟩ => ?_
  have hs14 := k14.scr hs13
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.a24E hf hs14 2 11) fun s15 ⟨k15, e15⟩ => ?_
  have hs15 := k15.scr hs14
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.sqrE hf hs15 4 4) fun s16 ⟨k16, e16⟩ => ?_
  have hs16 := k16.scr hs15
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.sqrE hf hs16 3 3) fun s17 ⟨k17, e17⟩ => ?_
  have hs17 := k17.scr hs16
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.addE hs17 2 9 2) fun s18 ⟨k18, e18⟩ => ?_
  have hs18 := k18.scr hs17
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.mulE hf hs18 4 0 4) fun s19 ⟨k19, e19⟩ => ?_
  have hs19 := k19.scr hs18
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.mulE hf hs19 1 9 10) fun s20 ⟨k20, e20⟩ => ?_
  have hs20 := k20.scr hs19
  refine WP.mono (VG.Proof.X448.X86_64.mulE hf hs20 2 11 2) fun s21 ⟨k21, e21⟩ => ?_
  refine ⟨(k2.trans (k3.trans (k4.trans (k5.trans (k6.trans (k7.trans (k8.trans (k9.trans (k10.trans (k11.trans (k12.trans (k13.trans (k14.trans (k15.trans (k16.trans (k17.trans (k18.trans (k19.trans (k20.trans k21))))))))))))))))))), ?_⟩
  rw [e21, e20, e19, e18, e17, e16, e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2]
  rfl

/-- The ladder's loop invariant, with the counter `rbx = n`: the slots
`x1, x2, z2, x3, z3` (0–4) and the word `swap` hold the ladder's state after
the bits 447 down to `n`, and since the loop's start (`s₀`) nothing else
changed but the registers `clob` and the bytes `[48, 1648)`. -/
structure LInv (base : Addr) (k : Nat) (u : Spec.X448.Fe) (s₀ s : State) (n : Nat) : Prop where
  scr : VG.Proof.X448.X86_64.Scr s base
  gpr : ∀ r, r ∉ VG.Proof.X448.X86_64.clob → r ≠ .rbx → s.gpr r = s₀.gpr r
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : VG.Proof.X448.X86_64.Outside base 48 1600 s₀.mem s.mem
  x1 : VG.Proof.X448.X86_64.E s.mem base 0 = u
  x2 : VG.Proof.X448.X86_64.E s.mem base 1 = (ladderAfter k u n).x2
  z2 : VG.Proof.X448.X86_64.E s.mem base 2 = (ladderAfter k u n).z2
  x3 : VG.Proof.X448.X86_64.E s.mem base 3 = (ladderAfter k u n).x3
  z3 : VG.Proof.X448.X86_64.E s.mem base 4 = (ladderAfter k u n).z3
  swap : VG.Proof.X448.X86_64.word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u n).swap

theorem cswap_fst (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).1 = if decide (sw = 1) = true then b else a := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

theorem cswap_snd (sw : Nat) (a b : Spec.X448.Fe) :
    (Spec.X448.cswap sw a b).2 = if decide (sw = 1) = true then a else b := by
  simp only [Spec.X448.cswap, decide_eq_true_eq]; split <;> rfl

/-- The slots of the ladder's variables after an iteration's field operations
are those of `ladderStep`. -/
theorem stepEnv_eval (e : VG.Proof.X448.X86_64.Env) (st : Spec.X448.Ladder) (k : Nat) (u : Spec.X448.Fe) (t : Nat)
    (h0 : e 0 = u) (h1 : e 1 = st.x2) (h2 : e 2 = st.z2) (h3 : e 3 = st.x3) (h4 : e 4 = st.z3) :
    VG.Proof.X448.X86_64.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 0 = u ∧
    VG.Proof.X448.X86_64.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 1 = (Spec.X448.ladderStep k u st t).x2 ∧
    VG.Proof.X448.X86_64.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 2 = (Spec.X448.ladderStep k u st t).z2 ∧
    VG.Proof.X448.X86_64.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 3 = (Spec.X448.ladderStep k u st t).x3 ∧
    VG.Proof.X448.X86_64.stepEnv (decide (st.swap ^^^ VG.Proof.X448.bit k t = 1)) e 4 = (Spec.X448.ladderStep k u st t).z3 := by
  rw [ladderStep_eq]
  simp only [↓reduceIte, VG.Proof.X448.X86_64.stepEnv, VG.Proof.X448.X86_64.opMul, VG.Proof.X448.X86_64.opAdd, VG.Proof.X448.X86_64.opSub, VG.Proof.X448.X86_64.opA24, VG.Proof.X448.X86_64.opSwap,
    Function.update_apply, VG.Proof.X448.X86_64.cswap_fst, VG.Proof.X448.X86_64.cswap_snd, h0, h1, h2, h3, h4]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

include hf in
/-- One iteration of the ladder: from the state after the bits down to
`n + 1` to the state after the bits down to `n`. -/
theorem step_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe} {n : Nat} (hn : n < 448)
    (hbits : ∀ t < 448, s₀.mem (VG.Proof.X448.X86_64.off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : VG.Proof.X448.X86_64.LInv base k u s₀ s (n + 1)) :
    WP isa (.block (VG.Impl.X448.X86_64.step fld)) s fun s' => VG.Proof.X448.X86_64.LInv base k u s₀ s' n ∧ s'.zf = some (decide (n = 0)) := by
  have hs := hi.scr
  have hbit : s.mem (VG.Proof.X448.X86_64.off base (BITS + n)) = BitVec.ofNat 8 (VG.Proof.X448.bit k n) := by
    rw [hi.mem _ (by rw [VG.Proof.X448.X86_64.ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)]
    exact hbits n hn
  rw [VG.Proof.X448.X86_64.step_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.stepPre_ok hs hn hi.rbx (by have := bit_le k n; omega)
    (by have := ladderAfter_swap_le k u (n := n + 1) (by omega); omega) hbit hi.swap)
    fun s1 ⟨b1, m1, g1, rd1, wr1, mem1, _, _⟩ => ?_
  have hs1 : VG.Proof.X448.X86_64.Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  have o8 : VG.Proof.X448.X86_64.Outside base SWAP 8 s.mem s1.mem := by
    rw [mem1]; exact VG.Proof.X448.X86_64.writeW_outside _ _ _ (by simp only [SWAP]; omega)
  have e1 : ∀ i : VG.Proof.X448.X86_64.Index, VG.Proof.X448.X86_64.E s1.mem base i = VG.Proof.X448.X86_64.E s.mem base i := fun i => by
    have := VG.Proof.X448.X86_64.slot_ge i
    simp only [VG.Proof.X448.X86_64.E, VG.Proof.X448.X86_64.F]
    rw [o8.fe (Or.inr (by simp only [SWAP]; omega)) (by have := VG.Proof.X448.X86_64.slot_lt i; simp only [ACC] at this; omega)]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.ops_ok hf hs1 m1) fun s2 ⟨K, e2⟩ => ?_
  have hs2 := K.scr hs1
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have zf : (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
    rw [BitVec.and_self]
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rfl
    · rw [decide_eq_false (by omega)]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by simp; omega)
  obtain ⟨v0, v1, v2, v3, v4⟩ := VG.Proof.X448.X86_64.stepEnv_eval (VG.Proof.X448.X86_64.E s1.mem base) (ladderAfter k u (n + 1)) k u n
    (by rw [e1]; exact hi.x1) (by rw [e1]; exact hi.x2) (by rw [e1]; exact hi.z2)
    (by rw [e1]; exact hi.x3) (by rw [e1]; exact hi.z3)
  rw [← ladderAfter_step k u hn, ← e2] at v1 v2 v3 v4
  rw [← e2] at v0
  refine ⟨⟨⟨hs2.rdi, hs2.wr, hs2.nowrap⟩, fun r hr hb => ?_, ?_, ?_, ?_, ?_, v0, v1, v2, v3, v4, ?_⟩,
    ?_⟩
  · have h' : r ∉ [Reg.rbx, .rax, .rdx, .rcx] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hb, fun h => hr (h ▸ by decide), fun h => hr (h ▸ by decide),
        fun h => hr (h ▸ by decide)⟩
    rw [RegUpd.gpr_arithFlags, K.gpr r hr, g1 r h', hi.gpr r hr hb]
  · rw [RegUpd.gpr_arithFlags, K.gpr _ (by decide), b1]
  · rw [RegUpd.rd_arithFlags, K.rd, rd1, hi.rd]
  · rw [RegUpd.wr_arithFlags, K.wr, wr1, hi.wr]
  · rw [RegUpd.mem_arithFlags]
    exact hi.mem.trans ((o8.mono (by simp only [SWAP]; omega) (by simp only [SWAP]; omega)).trans
      (K.mem.mono (by omega) (by omega)))
  · rw [RegUpd.mem_arithFlags, K.mem.word (by simp only [SWAP]; omega) (by simp only [SWAP]; omega),
      mem1, ladderAfter_step k u hn]
    simp only [X86_64.word, Mem.readW_writeW_self64]
    rfl
  · rw [RegUpd.zf_arithFlags, K.gpr .rbx (by decide), b1, zf]

include hf in
/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (VG.Proof.X448.X86_64.off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 448 → VG.Proof.X448.X86_64.LInv base k u s₀ s n →
      WP isa (.loop (.block (VG.Impl.X448.X86_64.step fld)) .ne) s fun s' => VG.Proof.X448.X86_64.LInv base k u s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := .block (VG.Impl.X448.X86_64.step fld)) (c := .ne)
    (Q := fun s' => VG.Proof.X448.X86_64.LInv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 448 ∧ VG.Proof.X448.X86_64.LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.X448.X86_64.step_ok hf (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

include hf in
/-- The ladder: the counter set to 448, then the loop. -/
theorem ladder_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (VG.Proof.X448.X86_64.off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t))
    (hi : ∀ s', s'.gpr .rbx = BitVec.ofNat 64 448 → (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VG.Proof.X448.X86_64.LInv base k u s₀ s' 448) :
    WP isa (ladder fld) s fun s' => VG.Proof.X448.X86_64.LInv base k u s₀ s' 0 := by
  refine WP.seq (WP.mono (show WP isa (.block [.mov32 .rbx (.imm 448)]) s (fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 448 ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
      State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
    exact ⟨rfl, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩)
    fun s' ⟨h1, h2, h3, h4, h5⟩ => VG.Proof.X448.X86_64.loop_ok hf hbits 448 s' (by omega) (by omega) (hi s' h1 h2 h3 h4 h5))

/-- What a ladder leaves: the slots `x2, z2, x3, z3` (1–4) and the word
`swap` hold the ladder's final state, and since its start (`s₀`) nothing else
changed but the registers `clob` and `rbx`, and the bytes `[48, 2048)`. -/
structure LPost (base : Addr) (k : Nat) (u : Spec.X448.Fe) (s₀ s : State) : Prop where
  scr : VG.Proof.X448.X86_64.Scr s base
  gpr : ∀ r, r ∉ VG.Proof.X448.X86_64.clob → r ≠ .rbx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : VG.Proof.X448.X86_64.Outside base 48 2000 s₀.mem s.mem
  x2 : VG.Proof.X448.X86_64.E s.mem base 1 = (ladderAfter k u 0).x2
  z2 : VG.Proof.X448.X86_64.E s.mem base 2 = (ladderAfter k u 0).z2
  x3 : VG.Proof.X448.X86_64.E s.mem base 3 = (ladderAfter k u 0).x3
  z3 : VG.Proof.X448.X86_64.E s.mem base 4 = (ladderAfter k u 0).z3
  swap : VG.Proof.X448.X86_64.word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u 0).swap

theorem LInv.post {base : Addr} {k : Nat} {u : Spec.X448.Fe} {s₀ s : State} (h : VG.Proof.X448.X86_64.LInv base k u s₀ s 0) :
    VG.Proof.X448.X86_64.LPost base k u s₀ s :=
  ⟨h.scr, h.gpr, h.rd, h.wr, h.mem.mono (by decide) (by decide), h.x2, h.z2, h.x3, h.z3, h.swap⟩

/-- What a ladder starts from: the bits of `k` in `BITS`, `x1 = u` and the
ladder's first state in the slots 0–4, and `swap = 0`. -/
structure LPre (base : Addr) (k : Nat) (u : Spec.X448.Fe) (s : State) : Prop where
  scr : VG.Proof.X448.X86_64.Scr s base
  bits : ∀ t < 448, s.mem (VG.Proof.X448.X86_64.off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.X448.bit k t)
  x1 : VG.Proof.X448.X86_64.E s.mem base 0 = u
  x2 : VG.Proof.X448.X86_64.E s.mem base 1 = 1
  z2 : VG.Proof.X448.X86_64.E s.mem base 2 = 0
  x3 : VG.Proof.X448.X86_64.E s.mem base 3 = u
  z3 : VG.Proof.X448.X86_64.E s.mem base 4 = 1
  swap : VG.Proof.X448.X86_64.word s.mem base SWAP = 0

include hf in
/-- `ladder`, as a ladder: from `LPre` to `LPost`. -/
theorem ladder_post {s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe} (h : VG.Proof.X448.X86_64.LPre base k u s) :
    WP isa (ladder fld) s (VG.Proof.X448.X86_64.LPost base k u s) :=
  WP.mono (VG.Proof.X448.X86_64.ladder_ok hf h.bits fun s' hb g m rd wr => ⟨⟨by rw [g _ (by decide)]; exact h.scr.rdi,
      by rw [wr]; exact h.scr.wr, h.scr.nowrap⟩, fun r _ hr => g r hr, hb, rd, wr,
      by rw [m]; exact Outside.refl _ _ _ _, by rw [m, h.x1], by rw [m, h.x2]; rfl, by rw [m, h.z2]; rfl,
      by rw [m, h.x3]; rfl, by rw [m, h.z3]; rfl, by rw [m, h.swap]; rfl⟩)
    fun _ hl => hl.post

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Finish`. -/
section

/-!
# X448 on x86-64: the last swap and the result
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

theorem mask_of : ∀ a < 2, BitVec.setWidth 64 (0 : BitVec 32) - BitVec.ofNat 64 a =
    VG.Proof.X448.X86_64.mask (decide (a = 1)) := by decide

theorem swapMask_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : VG.Proof.X448.X86_64.word s.mem base SWAP = BitVec.ofNat 64 sw) :
    WP isa (.block ([.mov .rdx (.mem (sc SWAP)), .mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx)] :
      List Instr)) s fun s' => s'.gpr .rcx = VG.Proof.X448.X86_64.mask (decide (sw = 1)) ∧ VG.Proof.X448.X86_64.Keeps [.rdx, .rcx] s s' := by
  have hr : InRegions (s.rd ++ s.wr) (VG.Proof.X448.X86_64.off base SWAP) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X448.X86_64.contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, VG.X86_64.readSrc32, execAlu,
    State.load64, VG.Proof.X448.X86_64.ea_sc, hs.rdi, hr, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, hw, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.X448.X86_64.mask_of sw hsw, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

theorem lastSwap_eq : lastSwap = ([.mov .rdx (.mem (sc SWAP)), .mov32 .rcx (.imm 0),
    .alu .sub .rcx (.reg .rdx)] : List Instr) ++ (cswap X2 X3 ++ cswap Z2 Z3) := by
  simp only [lastSwap, List.append_assoc]

/-- The swap after the loop, by the ladder's `swap`. -/
theorem lastSwap_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {st : Spec.X448.Ladder}
    (hsw : st.swap < 2) (hw : VG.Proof.X448.X86_64.word s.mem base SWAP = BitVec.ofNat 64 st.swap)
    (h1 : VG.Proof.X448.X86_64.E s.mem base 1 = st.x2) (h2 : VG.Proof.X448.X86_64.E s.mem base 2 = st.z2) (h3 : VG.Proof.X448.X86_64.E s.mem base 3 = st.x3)
    (h4 : VG.Proof.X448.X86_64.E s.mem base 4 = st.z3) :
    WP isa (.block lastSwap) s fun s' =>
      VG.Proof.X448.X86_64.Keep base s s' ∧ VG.Proof.X448.X86_64.E s'.mem base 1 = (Spec.X448.cswap st.swap st.x2 st.x3).1 ∧
        VG.Proof.X448.X86_64.E s'.mem base 2 = (Spec.X448.cswap st.swap st.z2 st.z3).1 := by
  rw [VG.Proof.X448.X86_64.lastSwap_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.swapMask_ok hs hsw hw) fun s₁ ⟨m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have g₁ : ∀ r, r ∉ VG.Proof.X448.X86_64.clob → s₁.gpr r = s.gpr r := fun r hr => k₁.1 r fun h => hr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
  have K₁ : VG.Proof.X448.X86_64.Keep base s s₁ := ⟨g₁, k₁.2.2.1, k₁.2.2.2, by rw [k₁.2.1]; exact Outside.refl _ _ _ _⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.cswapE hs₁ 1 3 (by decide) m₁) fun s₂ ⟨K₂, c₂, e₂⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86_64.cswapE (K₂.scr hs₁) 2 4 (by decide) (c₂.trans m₁)) fun s₃ ⟨K₃, _, e₃⟩ => ?_
  refine ⟨(K₁.trans K₂).trans K₃, ?_, ?_⟩
  · rw [e₃, e₂, VG.Proof.X448.X86_64.cswap_fst, ← h1, ← h3, ← k₁.2.1]
    simp (config := {decide := true}) only [VG.Proof.X448.X86_64.opSwap, Function.update_apply, ite_true, ite_false]
  · rw [e₃, e₂, VG.Proof.X448.X86_64.cswap_fst, ← h2, ← h4, ← k₁.2.1]
    simp (config := {decide := true}) only [VG.Proof.X448.X86_64.opSwap, Function.update_apply, ite_true, ite_false]

/-! ## The result -/

theorem restore_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) {g : Reg → BitVec 64}
    (hsv : VG.Proof.X448.X86_64.Saved base g s.mem) :
    WP isa (.block restore) s fun s' =>
      (∀ rd ∈ saved, s'.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (Spill.restore_ok .rdi saved g s (by decide) (fun p hp => ?_) (by rw [hs.rdi]; exact hsv))
    fun s' ⟨h₁, h₂, hm, hrd, hwr⟩ => ⟨fun rd hrd => h₁ _ (List.mem_map_of_mem hrd), h₂, hm, hrd, hwr⟩
  have := VG.Proof.X448.X86_64.saved_lt p hp
  rw [hs.rdi]; exact ⟨_, List.mem_append_right _ hs.wr, VG.Proof.X448.X86_64.contains_sc (by omega)⟩

/-- Stores relative to a register `b`, as a list. -/
def storesR (b : Reg) : Nat → List Reg → List Instr
  | _, [] => []
  | o, r :: rs => .store (at_ b o) r :: VG.Proof.X448.X86_64.storesR b (o + 8) rs

theorem outStores_eq : (List.range 7).map (fun i => Instr.store (at_ .rsi (8 * i)) (w i)) =
    VG.Proof.X448.X86_64.storesR .rsi 0 W := rfl

/-- Words stored at `q + o`, … into the writable region `R`. -/
theorem storesR_ok {q : Addr} {R : Region} :
    ∀ (s : State) (o : Nat) (rs : List Reg), s.gpr .rsi = q → R ∈ s.wr →
      (∀ d, o ≤ d → d + 8 ≤ o + 8 * rs.length → R.Contains (VG.Proof.X448.X86_64.off q d) 8) →
      o + 8 * rs.length < 2 ^ 64 →
      WP isa (.block (VG.Proof.X448.X86_64.storesR .rsi o rs)) s fun s' =>
        VG.Proof.X448.X86_64.mv s'.mem q o rs.length = VG.Proof.X448.X86_64.rv s rs ∧ VG.Proof.X448.X86_64.Outside q o (8 * rs.length) s.mem s'.mem ∧
        Frame [R] s.mem s'.mem ∧ (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | s, _, [], _, _, _, _ =>
    WP.block_nil ⟨rfl, Outside.refl _ _ _ _, Frame.refl _ _, fun _ => rfl, rfl, rfl⟩
  | s, o, r :: rs, hq, hR, hc, hn => by
    rw [VG.Proof.X448.X86_64.storesR, WP.block_cons_iff]
    have hl : (r :: rs).length = rs.length + 1 := rfl
    let s1 : State := { s with mem := s.mem.writeW (VG.Proof.X448.X86_64.off q o) (s.gpr r) }
    have hw : InRegions s.wr (VG.Proof.X448.X86_64.off q o) 8 := ⟨R, hR, hc o (Nat.le_refl _) (by omega)⟩
    refine ⟨s1, by simp only [exec, VG.Proof.X448.X86_64.ea_at, hq, State.store64, hw, ite_true]; rfl, ?_⟩
    refine WP.mono (VG.Proof.X448.X86_64.storesR_ok s1 (o + 8) rs hq hR (fun d h₁ h₂ => hc d (by omega) (by omega))
      (by omega)) fun s' ⟨hv, ho', hf, hg, hrd, hwr⟩ => ?_
    have o1 : VG.Proof.X448.X86_64.Outside q o 8 s.mem s1.mem := VG.Proof.X448.X86_64.writeW_outside _ _ _ (by omega)
    refine ⟨?_, (o1.mono (by omega) (by omega)).trans (ho'.mono (by omega) (by omega)), ?_,
      fun r' => hg r', hrd, hwr⟩
    · rw [List.length_cons, VG.Proof.X448.X86_64.mv, hv, VG.Proof.X448.X86_64.rv, ho'.word (by omega) (by omega)]
      simp only [s1, VG.Proof.X448.X86_64.word_writeW_self]
      rw [VG.Proof.X448.X86_64.rv_congr (s := s) (s' := s1) fun _ _ => rfl]
    · exact (Frame.refl _ _ |>.writeW (List.mem_singleton_self R) _ (hc o (Nat.le_refl _) (by omega))).trans hf

/-- The bytes of seven words. -/
theorem bytesAt_mv (m : Mem) (q : Addr) :
    Spec.X448.bytesAt m q 56 = X25519.leBytes 56 (VG.Proof.X448.X86_64.mv m q 0 7) := by
  have h := VG.Proof.X448.X86_64.leNum_bytesAt_mv m q 0 7
  rw [show VG.Proof.X448.X86_64.off q 0 = q from BitVec.add_zero q] at h
  have e : Spec.X448.bytesAt m q 56 = X25519.leBytes 56 (m.read q 56).toNat :=
    X25519.bytesAt_leBytes m q 56
  rw [e, ← leNum_bytesAt_read]
  exact congrArg _ h

theorem movRsi_ok (s : State) :
    WP isa (.block ([.mov .rsi (.reg .r15)] : List Instr)) s fun s' =>
      s'.gpr .rsi = s.gpr .r15 ∧ VG.Proof.X448.X86_64.Keeps [.rsi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, RegUpd.gpr_setReg,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Inv`. -/
section

/-!
# X448 on x86-64: the inversion

The inversion `invert` writes only the temporaries `T0`–`T7` (slots 14–21)
and the product's words (bytes `[960, 1648)`) and, in its runs of squarings,
the counter `rbx`; slot 21 (`T7`) ends as `VG.Proof.X448.invert` of slot 2
(`Z2`). Each part of it is an `ISpec`: a change of the slots by a function of
them, keeping everything else.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

/-- What the inversion keeps: the registers but `clob` and `rbx`, the regions,
and the memory outside `[960, 1648)`. -/
structure IKeep (base : Addr) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ VG.Proof.X448.X86_64.clob → r ≠ .rbx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : VG.Proof.X448.X86_64.Outside base 960 688 s.mem s'.mem

theorem IKeep.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.X448.X86_64.IKeep base s₁ s₂)
    (h₂ : VG.Proof.X448.X86_64.IKeep base s₂ s₃) : VG.Proof.X448.X86_64.IKeep base s₁ s₃ :=
  ⟨fun r hr hb => (h₂.gpr r hr hb).trans (h₁.gpr r hr hb), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₁.mem.trans h₂.mem⟩

theorem IKeep.scr {base : Addr} {s s' : State} (h : VG.Proof.X448.X86_64.IKeep base s s') (hs : VG.Proof.X448.X86_64.Scr s base) :
    VG.Proof.X448.X86_64.Scr s' base :=
  ⟨(h.gpr _ (by decide) (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-- `c` changes the slots by `f`, and keeps everything else (`IKeep`). -/
def ISpec (base : Addr) (c : Prog isa) (f : VG.Proof.X448.X86_64.Env → VG.Proof.X448.X86_64.Env) : Prop :=
  ∀ s, VG.Proof.X448.X86_64.Scr s base → WP isa c s fun s' => VG.Proof.X448.X86_64.IKeep base s s' ∧ VG.Proof.X448.X86_64.E s'.mem base = f (VG.Proof.X448.X86_64.E s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : VG.Proof.X448.X86_64.Env → VG.Proof.X448.X86_64.Env} (h₁ : VG.Proof.X448.X86_64.ISpec base c₁ f)
    (h₂ : VG.Proof.X448.X86_64.ISpec base c₂ g) : VG.Proof.X448.X86_64.ISpec base (.seq c₁ c₂) fun e => g (f e) := fun s hs =>
  WP.seq (WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scr hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩)

theorem ISpec.append {base : Addr} {l₁ l₂ : List Instr} {f g : VG.Proof.X448.X86_64.Env → VG.Proof.X448.X86_64.Env}
    (h₁ : VG.Proof.X448.X86_64.ISpec base (.block l₁) f) (h₂ : VG.Proof.X448.X86_64.ISpec base (.block l₂) g) :
    VG.Proof.X448.X86_64.ISpec base (.block (l₁ ++ l₂)) fun e => g (f e) := fun s hs => by
  rw [WP.block_append_iff]
  exact WP.mono (h₁ s hs) fun _ ⟨k₁, e₁⟩ =>
    WP.mono (h₂ _ (k₁.scr hs)) fun _ ⟨k₂, e₂⟩ => ⟨k₁.trans k₂, by rw [e₂, e₁]⟩

/-- A slot of the inversion's: 14 to 21. -/
abbrev ISlot (o : VG.Proof.X448.X86_64.Index) : Prop := 14 ≤ o.val

theorem islot_out {base : Addr} {o : VG.Proof.X448.X86_64.Index} (ho : VG.Proof.X448.X86_64.ISlot o) {m m' : Mem}
    (h : VG.Proof.X448.X86_64.Outside2 base (VG.Impl.X448.X86_64.slot o.val) 56 ACC 112 m m') : VG.Proof.X448.X86_64.Outside base 960 688 m m' :=
  h.outside (by simp only [VG.Impl.X448.X86_64.slot]; omega) (by have := VG.Proof.X448.X86_64.slot_lt o; simp only [ACC] at *; omega)
    (by decide) (by decide)

variable {fld : Field} (hf : VG.Proof.X448.X86_64.FieldOk fld)

include hf in
/-- A multiplication into a slot of the inversion's, which also keeps `rbx`. -/
theorem mulI_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (o a b : VG.Proof.X448.X86_64.Index) (ho : VG.Proof.X448.X86_64.ISlot o) :
    WP isa (.block (fld.mul (VG.Impl.X448.X86_64.slot o.val) (VG.Impl.X448.X86_64.slot a.val) (VG.Impl.X448.X86_64.slot b.val))) s fun s' =>
      VG.Proof.X448.X86_64.IKeep base s s' ∧ s'.gpr .rbx = s.gpr .rbx ∧ VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.X448.X86_64.opMul o a b (VG.Proof.X448.X86_64.E s.mem base) :=
  WP.mono (hf.mul hs (VG.Proof.X448.X86_64.slot_lt o) (VG.Proof.X448.X86_64.slot_lt a) (VG.Proof.X448.X86_64.slot_lt b)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, VG.Proof.X448.X86_64.islot_out ho h.mem⟩,
      h.gpr _ (by decide), by rw [VG.Proof.X448.X86_64.E_update h.mem, e]; rfl⟩

include hf in
/-- A square into a slot of the inversion's, which also keeps `rbx`. -/
theorem sqrI_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) (o a : VG.Proof.X448.X86_64.Index) (ho : VG.Proof.X448.X86_64.ISlot o) :
    WP isa (.block (fld.sqr (VG.Impl.X448.X86_64.slot o.val) (VG.Impl.X448.X86_64.slot a.val))) s fun s' =>
      VG.Proof.X448.X86_64.IKeep base s s' ∧ s'.gpr .rbx = s.gpr .rbx ∧ VG.Proof.X448.X86_64.E s'.mem base = VG.Proof.X448.X86_64.opMul o a a (VG.Proof.X448.X86_64.E s.mem base) :=
  WP.mono (hf.sqr hs (VG.Proof.X448.X86_64.slot_lt o) (VG.Proof.X448.X86_64.slot_lt a)) fun _ ⟨h, e⟩ =>
    ⟨⟨fun r hr _ => h.gpr r hr, h.rd, h.wr, VG.Proof.X448.X86_64.islot_out ho h.mem⟩,
      h.gpr _ (by decide), by rw [VG.Proof.X448.X86_64.E_update h.mem, e]; rfl⟩

include hf in
theorem mulI (base : Addr) (o a b : VG.Proof.X448.X86_64.Index) (ho : VG.Proof.X448.X86_64.ISlot o) :
    VG.Proof.X448.X86_64.ISpec base (.block (fld.mul (VG.Impl.X448.X86_64.slot o.val) (VG.Impl.X448.X86_64.slot a.val) (VG.Impl.X448.X86_64.slot b.val))) (VG.Proof.X448.X86_64.opMul o a b) :=
  fun _ hs => WP.mono (VG.Proof.X448.X86_64.mulI_ok hf hs o a b ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

include hf in
theorem sqrI (base : Addr) (o a : VG.Proof.X448.X86_64.Index) (ho : VG.Proof.X448.X86_64.ISlot o) :
    VG.Proof.X448.X86_64.ISpec base (.block (fld.sqr (VG.Impl.X448.X86_64.slot o.val) (VG.Impl.X448.X86_64.slot a.val))) (VG.Proof.X448.X86_64.opMul o a a) :=
  fun _ hs => WP.mono (VG.Proof.X448.X86_64.sqrI_ok hf hs o a ho) fun _ ⟨k, _, e⟩ => ⟨k, e⟩

/-! ## Runs of squarings -/

/-- `rbx = k`. -/
theorem setRbx_ok (s : State) (k : Nat) (hk : k < 2 ^ 32) :
    WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 k))]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega)]

/-- `rbx -= 1`, from `rbx = k + 1`: the flag `ZF` says whether `k = 0`. -/
theorem decRbx_ok {s : State} {k : Nat} (hk : k < 2 ^ 32)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (k + 1)) :
    WP isa (.block [.alu .sub .rbx (.imm 1)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 k ∧ (∀ r, r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (k = 0)) := by
  have hb' : s.gpr .rbx - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 k := by
    have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    rw [hb, e1, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have zf : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rfl
    · rw [decide_eq_false (by omega)]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by simp; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, VG.X86_64.readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left', hb', RegUpd.gpr_setReg_self, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.zf_setReg, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, zf]
  exact ⟨trivial, fun r hr => by simp only [RegUpd.gpr_setReg, hr, ite_false,
    RegUpd.gpr_arithFlags], trivial, trivial, trivial, trivial⟩

/-- Slot `o` becomes slot `a` squared `n` times. -/
def opSqn (o a : VG.Proof.X448.X86_64.Index) (n : Nat) (e : VG.Proof.X448.X86_64.Env) : VG.Proof.X448.X86_64.Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : VG.Proof.X448.X86_64.Index) (e : VG.Proof.X448.X86_64.Env) (v : Spec.X448.Fe) :
    VG.Proof.X448.X86_64.opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [VG.Proof.X448.X86_64.opMul, Function.update_self, Function.update_idem]

include hf in
/-- The loop of `sqn`, with the counter `rbx = m` and slot `o` squared
`n - m` times since `s₀`. -/
theorem sqLoop_ok {s₀ : State} {base : Addr} (hs₀ : VG.Proof.X448.X86_64.Scr s₀ base) (o : VG.Proof.X448.X86_64.Index) (ho : VG.Proof.X448.X86_64.ISlot o)
    (x : Spec.X448.Fe) (n : Nat) (hn : n < 2 ^ 32) :
    ∀ m s, 1 ≤ m → m < n → VG.Proof.X448.X86_64.IKeep base s₀ s → s.gpr .rbx = BitVec.ofNat 64 m →
      VG.Proof.X448.X86_64.E s.mem base = Function.update (VG.Proof.X448.X86_64.E s₀.mem base) o (sqn x (n - m)) →
      WP isa (.loop (.block (fld.sqr (VG.Impl.X448.X86_64.slot o.val) (VG.Impl.X448.X86_64.slot o.val) ++
          ([.alu .sub .rbx (.imm 1)] : List Instr))) .ne) s fun s' =>
        VG.Proof.X448.X86_64.IKeep base s₀ s' ∧ VG.Proof.X448.X86_64.E s'.mem base = Function.update (VG.Proof.X448.X86_64.E s₀.mem base) o (sqn x n) := by
  intro m s h1 h2 hk hb he
  refine WP.loop (M := isa) (Inv := fun m (s : State) => 1 ≤ m ∧ m < n ∧ VG.Proof.X448.X86_64.IKeep base s₀ s ∧
    s.gpr .rbx = BitVec.ofNat 64 m ∧
    VG.Proof.X448.X86_64.E s.mem base = Function.update (VG.Proof.X448.X86_64.E s₀.mem base) o (sqn x (n - m))) ?_ m s ⟨h1, h2, hk, hb, he⟩
  intro m s ⟨h1, h2, hk, hb, he⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.sqrI_ok hf (hk.scr hs₀) o o ho) fun s1 ⟨k1, b1, e1⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86_64.decRbx_ok (by omega) (b1.trans hb)) fun s2 ⟨b2, g2, m2, rd2, wr2, z2⟩ => ?_
  have k2 : VG.Proof.X448.X86_64.IKeep base s₀ s2 := hk.trans (k1.trans ⟨fun r _ hr => g2 r hr, rd2, wr2,
    by rw [m2]; exact Outside.refl _ _ _ _⟩)
  have e2 : VG.Proof.X448.X86_64.E s2.mem base = Function.update (VG.Proof.X448.X86_64.E s₀.mem base) o (sqn x (n - m)) := by
    rw [m2, e1, he, VG.Proof.X448.X86_64.opMul_update]
    congr 2
    rw [show n - m = (n - (m + 1)) + 1 by omega]
    rfl
  simp only [eval, z2, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, k2, by rw [e2, Nat.sub_zero]⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, k2, b2, e2⟩

include hf in
/-- `sqn o a n`: slot `o` becomes slot `a` squared `n` times (`o` may be `a`). -/
theorem sqnI (base : Addr) (o a : VG.Proof.X448.X86_64.Index) (ho : VG.Proof.X448.X86_64.ISlot o) (n : Nat) (hn : 1 ≤ n)
    (hn' : n < 2 ^ 32) :
    VG.Proof.X448.X86_64.ISpec base (Impl.X448.X86_64.sqn fld (VG.Impl.X448.X86_64.slot o.val) (VG.Impl.X448.X86_64.slot a.val) n) (VG.Proof.X448.X86_64.opSqn o a n) := by
  intro s hs
  rw [Impl.X448.X86_64.sqn]
  by_cases h1 : n = 1
  · subst h1
    rw [ite_eq_left rfl]
    exact WP.mono (VG.Proof.X448.X86_64.sqrI_ok hf hs o a ho) fun _ ⟨k, _, e⟩ => ⟨k, by rw [e]; rfl⟩
  rw [ite_eq_right h1]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.sqrI_ok hf hs o a ho) fun s1 ⟨k1, _, e1⟩ => ?_
  refine WP.mono (VG.Proof.X448.X86_64.setRbx_ok s1 (n - 1) (by omega)) fun s2 ⟨b2, g2, m2, rd2, wr2⟩ => ?_
  have k2 : VG.Proof.X448.X86_64.IKeep base s s2 := k1.trans ⟨fun r _ hr => g2 r hr, rd2, wr2,
    by rw [m2]; exact Outside.refl _ _ _ _⟩
  refine VG.Proof.X448.X86_64.sqLoop_ok hf hs o ho (VG.Proof.X448.X86_64.E s.mem base a) n hn' (n - 1) s2 (by omega) (by omega) k2 b2 ?_
  rw [m2, e1, show n - (n - 1) = 1 by omega]
  rfl

/-! ## The inversion -/

/-- The slots after the inversion. -/
def invEnv (e : VG.Proof.X448.X86_64.Env) : VG.Proof.X448.X86_64.Env :=
  VG.Proof.X448.X86_64.opMul 21 21 20 (VG.Proof.X448.X86_64.opMul 20 20 2 (VG.Proof.X448.X86_64.opSqn 20 20 2 (VG.Proof.X448.X86_64.opSqn 21 21 225 (VG.Proof.X448.X86_64.opMul 21 21 2 (VG.Proof.X448.X86_64.opSqn 21 20 1
    (VG.Proof.X448.X86_64.opMul 20 20 14 (VG.Proof.X448.X86_64.opSqn 20 20 2 (VG.Proof.X448.X86_64.opMul 20 20 15 (VG.Proof.X448.X86_64.opSqn 20 20 4 (VG.Proof.X448.X86_64.opMul 20 20 16 (VG.Proof.X448.X86_64.opSqn 20 20 8
    (VG.Proof.X448.X86_64.opMul 20 20 17 (VG.Proof.X448.X86_64.opSqn 20 20 16 (VG.Proof.X448.X86_64.opMul 20 20 19 (VG.Proof.X448.X86_64.opSqn 20 20 64 (VG.Proof.X448.X86_64.opMul 20 20 19 (VG.Proof.X448.X86_64.opSqn 20 19 64
    (VG.Proof.X448.X86_64.opMul 19 19 18 (VG.Proof.X448.X86_64.opSqn 19 18 32 (VG.Proof.X448.X86_64.opMul 18 18 17 (VG.Proof.X448.X86_64.opSqn 18 17 16 (VG.Proof.X448.X86_64.opMul 17 17 16 (VG.Proof.X448.X86_64.opSqn 17 16 8
    (VG.Proof.X448.X86_64.opMul 16 16 15 (VG.Proof.X448.X86_64.opSqn 16 15 4 (VG.Proof.X448.X86_64.opMul 15 15 14 (VG.Proof.X448.X86_64.opSqn 15 14 2 (VG.Proof.X448.X86_64.opMul 14 14 2
    (VG.Proof.X448.X86_64.opSqn 14 2 1 e)))))))))))))))))))))))))))))

include hf in
theorem invert_spec (base : Addr) : VG.Proof.X448.X86_64.ISpec base (Impl.X448.X86_64.invert fld) VG.Proof.X448.X86_64.invEnv := by
  have h : VG.Proof.X448.X86_64.ISpec base _ _ :=
    (VG.Proof.X448.X86_64.sqnI hf base 14 2 (by decide) 1 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 14 14 2 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 15 14 (by decide) 2 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 15 15 14 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 16 15 (by decide) 4 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 16 16 15 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 17 16 (by decide) 8 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 17 17 16 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 18 17 (by decide) 16 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 18 18 17 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 19 18 (by decide) 32 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 19 19 18 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 20 19 (by decide) 64 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 20 20 19 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 20 20 (by decide) 64 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 20 20 19 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 20 20 (by decide) 16 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 20 20 17 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 20 20 (by decide) 8 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 20 20 16 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 20 20 (by decide) 4 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 20 20 15 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 20 20 (by decide) 2 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 20 20 14 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 21 20 (by decide) 1 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.mulI hf base 21 21 2 (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 21 21 (by decide) 225 (by decide) (by decide)).seq <|
    (VG.Proof.X448.X86_64.sqnI hf base 20 20 (by decide) 2 (by decide) (by decide)).seq
    ((VG.Proof.X448.X86_64.mulI hf base 20 20 2 (by decide)).append (VG.Proof.X448.X86_64.mulI hf base 21 21 20 (by decide)))
  exact h

theorem invEnv_eval (e : VG.Proof.X448.X86_64.Env) : VG.Proof.X448.X86_64.invEnv e 21 = VG.Proof.X448.invert (e 2) := by
  simp only [↓reduceIte, VG.Proof.X448.X86_64.invEnv, VG.Proof.X448.X86_64.opMul, VG.Proof.X448.X86_64.opSqn, Function.update_apply]
  rfl

include hf in
theorem invert_ok {s : State} {base : Addr} (hs : VG.Proof.X448.X86_64.Scr s base) :
    WP isa (Impl.X448.X86_64.invert fld) s fun s' =>
      (∀ r, r ∉ VG.Proof.X448.X86_64.clob → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X448.X86_64.Outside base 960 688 s.mem s'.mem ∧
      VG.Proof.X448.X86_64.E s'.mem base 21 = VG.Proof.X448.invert (VG.Proof.X448.X86_64.E s.mem base 2) :=
  WP.mono (VG.Proof.X448.X86_64.invert_spec hf base s hs) fun _ ⟨k, e⟩ =>
    ⟨k.gpr, k.rd, k.wr, k.mem, by rw [e, VG.Proof.X448.X86_64.invEnv_eval]⟩

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Main`. -/
section

/-!
# X448 on x86-64: the whole function

The contract the proof is written against (the facts of
`Spec.X448.x448Contract` it uses, stated for x86-64), and the correctness of
`vg_x448` against it: every write is in the working space but the result's, so
the arguments are read unchanged, the callee-saved registers restored from the
working space, and the return address kept.
-/

namespace VG.Proof.X448

open VG VG.X86_64 in
/-- `vg_x448(out = rdi, scalar = rsi, point = rdx, scratch = rcx)`. -/
def x448X86_64 : Contract X86_64.isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, 56⟩
    let scalar : Region := ⟨s.gpr .rsi, 56⟩
    let point : Region := ⟨s.gpr .rdx, 56⟩
    let scratch : Region := ⟨s.gpr .rcx, 8192⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [scalar, point] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (s.gpr .rcx).toNat + 8192 ≤ 2 ^ 64
  post s s' := Spec.X448.bytesAt s'.mem (s.gpr .rdi) 56 =
    Spec.X448.x448 (Spec.X448.bytesAt s.mem (s.gpr .rsi) 56)
      (Spec.X448.bytesAt s.mem (s.gpr .rdx) 56)
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

end VG.Proof.X448

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

section
variable (s₀ : State)
abbrev outR : Region := ⟨s₀.gpr .rdi, 56⟩
abbrev scalarR : Region := ⟨s₀.gpr .rsi, 56⟩
abbrev pointR : Region := ⟨s₀.gpr .rdx, 56⟩
abbrev scR : Region := ⟨s₀.gpr .rcx, 8192⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
end

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.X448.X86_64.scalarR s₀, VG.Proof.X448.X86_64.pointR s₀]
  wr : s₀.wr = [VG.Proof.X448.X86_64.outR s₀, VG.Proof.X448.X86_64.scR s₀]
  out_sc : (VG.Proof.X448.X86_64.outR s₀).Disjoint (VG.Proof.X448.X86_64.scR s₀)
  scalar_sc : (VG.Proof.X448.X86_64.scalarR s₀).Disjoint (VG.Proof.X448.X86_64.scR s₀)
  point_sc : (VG.Proof.X448.X86_64.pointR s₀).Disjoint (VG.Proof.X448.X86_64.scR s₀)
  ret_out : (VG.Proof.X448.X86_64.retR s₀).Disjoint (VG.Proof.X448.X86_64.outR s₀)
  ret_sc : (VG.Proof.X448.X86_64.retR s₀).Disjoint (VG.Proof.X448.X86_64.scR s₀)
  sc_fit : (s₀.gpr .rcx).toNat + 8192 ≤ 2 ^ 64

theorem Pre.of (s₀ : State) (h : Proof.X448.x448X86_64.pre s₀) : VG.Proof.X448.X86_64.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ VG.Proof.X448.X86_64.ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [VG.Proof.X448.X86_64.ofs] at h; omega

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : VG.Proof.X448.X86_64.Outside base 0 8192 m m')
    (hp : ∀ i < 56, 8192 ≤ VG.Proof.X448.X86_64.ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X448.bytesAt m' p 56 = Spec.X448.bytesAt m p 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem E_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.X86_64.Outside base o n m m') (i : VG.Proof.X448.X86_64.Index)
    (hi : slot i.val + 56 ≤ o ∨ o + n ≤ slot i.val) : VG.Proof.X448.X86_64.E m' base i = VG.Proof.X448.X86_64.E m base i := by
  have := VG.Proof.X448.X86_64.slot_lt i
  simp only [ACC] at this
  simp only [VG.Proof.X448.X86_64.E, VG.Proof.X448.X86_64.F]
  show toFe (VG.Proof.X448.X86_64.mv m' base (slot i.val) 7) = toFe (VG.Proof.X448.X86_64.mv m base (slot i.val) 7)
  rw [h.mv (by omega) (by omega)]

theorem Outside.frame {base : Addr} {m m' : Mem} (h : VG.Proof.X448.X86_64.Outside base 0 8192 m m') :
    Frame [⟨base, 8192⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this; show 0 + 8192 ≤ (x - base).toNat; omega))

/-- A word of the working space, after writes to a region disjoint from it. -/
theorem word_frame {base : Addr} {m m' : Mem} {R : Region} (hF : Frame [R] m m')
    (hd : R.Disjoint ⟨base, 8192⟩) {d : Nat} (hd8 : d + 8 ≤ 8192) :
    VG.Proof.X448.X86_64.word m' base d = VG.Proof.X448.X86_64.word m base d := by
  refine (Mem.readW_congr fun i hi => (hF _ fun r hr hc => ?_).symm).symm
  rw [List.mem_singleton.mp hr] at hc
  refine hd _ hc ?_
  rw [Offset.add_add]
  exact Offset.contains_base base (d := d + i) (n := 1) (by omega) (by omega)

variable {fld : Field} (hf : VG.Proof.X448.X86_64.FieldOk fld)

theorem finish_eq : finish fld = fld.mul X2 X2 T7 ++ (freeze X2 ++ (VG.Proof.X448.X86_64.storesR .rsi 0 W ++ restore)) := by
  simp only [finish, List.append_assoc, VG.Proof.X448.X86_64.outStores_eq]

theorem x448_eq' (lad : Prog isa) : x448Of fld lad = .seq (.block setup) (.seq bits (.seq
    (.block ([.mov .rsi (.reg .r15)] : List Instr)) (.seq lad (.seq (.block lastSwap)
    (.seq (Impl.X448.X86_64.invert fld) (.block (finish fld))))))) := rfl

include hf in
/-- X448 with any ladder `lad` that leaves the ladder's final state as
`ladder` does (`LPost`). -/
theorem correct_of {lad : Prog isa}
    (hlad : ∀ {s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}, VG.Proof.X448.X86_64.LPre base k u s →
      WP isa lad s (VG.Proof.X448.X86_64.LPost base k u s))
    {s₀ : State} (hp : VG.Proof.X448.X86_64.Pre s₀) :
    WP isa (x448Of fld lad) s₀ fun s' => gprPreserved s₀ s' ∧ Proof.X448.x448X86_64.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, s₀.gpr .rcx = b := ⟨_, rfl⟩
  have hn : base.toNat + 8192 ≤ 2 ^ 64 := hbase ▸ hp.sc_fit
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s₀.wr := by rw [hp.wr, ← hbase]; simp
  have hwo : VG.Proof.X448.X86_64.outR s₀ ∈ s₀.wr := by rw [hp.wr]; simp
  have hr : ∀ d, d + 8 ≤ 56 → InRegions (s₀.rd ++ s₀.wr) (VG.Proof.X448.X86_64.off (s₀.gpr .rdx) d) 8 := fun d hd =>
    ⟨VG.Proof.X448.X86_64.pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ hd (by omega)⟩
  have hd : ∀ j < 56, 8192 ≤ VG.Proof.X448.X86_64.ofs base (VG.Proof.X448.X86_64.off (s₀.gpr .rdx) j) :=
    fun j hj => VG.Proof.X448.X86_64.far (hbase ▸ hp.point_sc) hj (by decide)
  rw [VG.Proof.X448.X86_64.x448_eq']
  refine WP.seq (WP.mono (VG.Proof.X448.X86_64.setup_ok hbase hw₀ hn rfl hr hd)
    fun s₁ ⟨hs₁, r15₁, g₁, rd₁, wr₁, o₁, sv₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  have hkr : ∀ q < 56, InRegions (s₁.rd ++ s₁.wr) (s₀.gpr .rsi + BitVec.ofNat 64 q) 1 :=
    fun q hq => ⟨VG.Proof.X448.X86_64.scalarR s₀, by rw [rd₁, hp.rd]; simp,
      Offset.contains_base _ (d := q) (n := 1) (k := 56) (by omega) (by omega)⟩
  have hkd : ∀ q < 56, 8192 ≤ VG.Proof.X448.X86_64.ofs base (s₀.gpr .rsi + BitVec.ofNat 64 q) :=
    fun q hq => VG.Proof.X448.X86_64.far (hbase ▸ hp.scalar_sc) hq (by decide)
  refine WP.seq (WP.mono (VG.Proof.X448.X86_64.bits_ok hs₁ (g₁ _ (by decide)) hkr hkd)
    fun s₂ ⟨g₂, rd₂, wr₂, o₂, b₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.X86_64.movRsi_ok s₂) fun s₃ ⟨rsi₃, k₃⟩ => ?_)
  have hs₃ : VG.Proof.X448.X86_64.Scr s₃ base :=
    ⟨by rw [k₃.1 _ (by decide), g₂ _ (by decide)]; exact hs₁.rdi,
      by rw [k₃.2.2.2, wr₂]; exact hs₁.wr, hn⟩
  have hkb := VG.Proof.X448.X86_64.bytesAt_outside o₁ hkd
  have e₃ : ∀ i : VG.Proof.X448.X86_64.Index, VG.Proof.X448.X86_64.E s₃.mem base i = VG.Proof.X448.X86_64.E s₁.mem base i :=
    fun i => by
      rw [k₃.2.1]; exact VG.Proof.X448.X86_64.E_outside o₂ i (Or.inl (by have := VG.Proof.X448.X86_64.slot_lt i; simp only [BITS, ACC] at *; omega))
  refine WP.seq (WP.mono (hlad (s := s₃)
    (k := Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .rsi) 56))
    (u := toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .rdx) 56)))
    ⟨hs₃, fun t ht => by rw [k₃.2.1, b₂ t ht, hkb],
      by rw [e₃ 0, x1₁], by rw [e₃ 1, x2₁], by rw [e₃ 2, z2₁],
      by rw [e₃ 3, x3₁], by rw [e₃ 4, z3₁],
      by rw [k₃.2.1, o₂.word (by decide) (by decide), sw₁]⟩) fun s₄ L => ?_)
  refine WP.seq (WP.mono (VG.Proof.X448.X86_64.lastSwap_ok L.scr
    (by have := ladderAfter_swap_le
          (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem (s₀.gpr .rsi) 56))
          (toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem (s₀.gpr .rdx) 56)))
          (n := 0) (by omega)
        omega) L.swap L.x2 L.z2 L.x3 L.z3) fun s₅ ⟨K₅, e1₅, e2₅⟩ => ?_)
  have hs₅ := K₅.scr L.scr
  refine WP.seq (WP.mono (VG.Proof.X448.X86_64.invert_ok hf hs₅) fun s₆ ⟨g₆, rd₆, wr₆, o₆, e₆⟩ => ?_)
  have hs₆ : VG.Proof.X448.X86_64.Scr s₆ base := ⟨(g₆ _ (by decide) (by decide)).trans hs₅.rdi, wr₆ ▸ hs₅.wr, hn⟩
  rw [VG.Proof.X448.X86_64.finish_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.mulE hf hs₆ 1 1 21) fun s₇ ⟨K₇, e₇⟩ => ?_
  have hs₇ := K₇.scr hs₆
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.freeze_ok hs₇ (a := X2) (by decide)) fun s₈ ⟨v₈, k₈⟩ => ?_
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  have rsi₈ : s₈.gpr .rsi = s₀.gpr .rdi := by
    rw [k₈.1 _ (by decide), K₇.gpr _ (by decide), g₆ _ (by decide) (by decide),
      K₅.gpr _ (by decide), L.gpr _ (by decide) (by decide), rsi₃, g₂ _ (by decide), r15₁]
  have hwo₈ : VG.Proof.X448.X86_64.outR s₀ ∈ s₈.wr := by
    rw [k₈.2.2.2, K₇.wr, wr₆, K₅.wr, L.wr, k₃.2.2.2, wr₂, wr₁]; exact hwo
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.X86_64.storesR_ok s₈ 0 W rsi₈ hwo₈
    (fun d _ hd => by rw [VG.Proof.X448.X86_64.W_len] at hd; exact Offset.contains_base _ (by omega) (by omega))
    (by decide))
    fun s₉ ⟨v₉, _, F₉, g₉, rd₉, wr₉⟩ => ?_
  have sv₈ : VG.Proof.X448.X86_64.Saved base s₀.gpr s₈.mem := by
    have sv₃ : VG.Proof.X448.X86_64.Saved base s₀.gpr s₃.mem := by rw [k₃.2.1]; exact sv₁.outside o₂ (by decide)
    rw [k₈.2.1]
    exact (((sv₃.outside L.mem (by decide)).outside K₅.mem (by decide)).outside o₆
      (by decide)).outside K₇.mem (by decide)
  have sv₉ : VG.Proof.X448.X86_64.Saved base s₀.gpr s₉.mem := fun rd hrd => by
    have := VG.Proof.X448.X86_64.saved_lt rd hrd
    rw [← sv₈ rd hrd]
    exact VG.Proof.X448.X86_64.word_frame F₉ (hbase ▸ hp.out_sc) (by omega)
  have hs₉ : VG.Proof.X448.X86_64.Scr s₉ base := ⟨(g₉ _).trans hs₈.rdi, wr₉ ▸ hs₈.wr, hn⟩
  refine WP.mono (VG.Proof.X448.X86_64.restore_ok hs₉ sv₉) fun s' ⟨r', g', m', rd', wr'⟩ => ?_
  have O₃ : VG.Proof.X448.X86_64.Outside base 0 8192 s₀.mem s₃.mem := by
    rw [k₃.2.1]; exact o₁.trans (o₂.mono (by decide) (by decide))
  have O : VG.Proof.X448.X86_64.Outside base 0 8192 s₀.mem s₈.mem := by
    rw [k₈.2.1]
    exact (((O₃.trans (L.mem.mono (by decide) (by decide))).trans
      (K₅.mem.mono (by decide) (by decide))).trans (o₆.mono (by decide) (by decide))).trans
      (K₇.mem.mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r' (.rbx, 0) (by decide)
    · exact r' (.rbp, 8) (by decide)
    · rw [g' _ (by decide), g₉, k₈.1 _ (by decide), K₇.gpr _ (by decide),
        g₆ _ (by decide) (by decide), K₅.gpr _ (by decide), L.gpr _ (by decide) (by decide),
        k₃.1 _ (by decide), g₂ _ (by decide), g₁ _ (by decide)]
    · exact r' (.r12, 16) (by decide)
    · exact r' (.r13, 24) (by decide)
    · exact r' (.r14, 32) (by decide)
    · exact r' (.r15, 40) (by decide)
  · have F₁ : Frame [VG.Proof.X448.X86_64.scR s₀, VG.Proof.X448.X86_64.outR s₀] s₀.mem s'.mem := by
      rw [m']
      exact ((hbase ▸ O.frame).mono (by simp)).trans (F₉.mono (by simp))
    exact F₁.readW (r := VG.Proof.X448.X86_64.retR s₀) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.ret_sc
      · exact hp.ret_out) (by decide)
  · show Spec.X448.bytesAt s'.mem (s₀.gpr .rdi) 56 = _
    rw [m', VG.Proof.X448.X86_64.bytesAt_mv, x448_eq]
    rw [VG.Proof.X448.X86_64.W_len] at v₉
    rw [v₉, v₈]
    dsimp only
    rw [encodeUCoordinate_eq]
    refine congrArg (X25519.leBytes 56) ?_
    rw [← toFe_val]
    change (VG.Proof.X448.X86_64.E s₇.mem base 1).val = _
    rw [e₇]
    simp only [VG.Proof.X448.X86_64.opMul, Function.update_self]
    rw [VG.Proof.X448.X86_64.E_outside o₆ 1 (by decide), e1₅, e₆, e2₅]

include hf in
theorem correct {s₀ : State} (hp : VG.Proof.X448.X86_64.Pre s₀) :
    WP isa (x448With fld) s₀ fun s' => gprPreserved s₀ s' ∧ Proof.X448.x448X86_64.post s₀ s' :=
  VG.Proof.X448.X86_64.correct_of hf (fun h => VG.Proof.X448.X86_64.ladder_post hf h) hp

end VG.Proof.X448.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X448.X86_64.Verified`. -/
section

/-!
# X448 on x86-64: `Verified`

Constant time (by taint tracking: the only branches are on the loop counters,
and every address is an argument plus a constant or a counter),
satisfiability, and the shared contract of `Spec/`.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_ok (s : State) (hs : Proof.X448.x448X86_64.pre s) :
    ∃ t s', Exec isa Impl.X448.X86_64.x448 s t s' ∧ abiPreserved s s' ∧
      Proof.X448.x448X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.X448.X86_64.correct VG.Proof.X448.X86_64.baseline_ok (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem x448_ct : ConstantTime isa Proof.X448.x448X86_64.pre Proof.X448.x448X86_64.pub
    Impl.X448.X86_64.x448 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x448_verified :
    Verified X86_64.target Impl.X448.X86_64.x448 (Spec.X448.x448Contract X86_64.abi) :=
  Verified.of_correct VG.Proof.X448.X86_64.x448_ok VG.Proof.X448.X86_64.x448_ct (by
    sig_implies [Spec.X448.x448Contract, Spec.X448.x448Sig, X86_64.abi, X86_64.argRegs,
      Proof.X448.x448X86_64] [satState] using VG.Proof.X448.X86_64.satState)

end VG.Proof.X448.X86_64

end
