module

public import VerifiedGarbage.Proof.X448.X86_64.Chain
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X448.Field
public import VerifiedGarbage.Proof.X448.X86_64.Comba
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86_64.Basic
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! ### `X448.X86_64.Swap`, which the modules that import this one used -/

section

/-!
# X448 on x86-64: the conditional swap

An XOR mask exchanges the words without a branch or an address depending on
the swap bit, word by word (`wp_range_flatMap`).
-/

@[expose] public section

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

def mask (sw : Bool) : BitVec 64 := if sw then BitVec.allOnes 64 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 64) :
    a ^^^ ((a ^^^ b) &&& mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The registers (and regions) of `s'` are those of `s` but for `rs`. -/
def KeepsR (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem KeepsR.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : KeepsR rs s₁ s₂)
    (h₂ : KeepsR rs s₂ s₃) : KeepsR rs s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem Scr.of_keepsR {rs : List Reg} {s s' : State} {base : Addr} (hs : Scr s base)
    (h : KeepsR rs s s') (hr : .rdi ∉ rs) : Scr s' base :=
  ⟨(h.1 _ hr).trans hs.rdi, h.2.2 ▸ hs.wr, hs.nowrap⟩

theorem swapStep_ok {s : State} {base : Addr} (hs : Scr s base) {x y i : Nat}
    (hx : x + 56 ≤ 1536) (hy : y + 56 ≤ 1536) (hi : i < 7) {sw : Bool} (hc : s.gpr .rcx = mask sw) :
    WP isa (.block
      [.mov .rax (.mem (sc (x + 8 * i))), .mov .rdx (.mem (sc (y + 8 * i))),
        .mov .r8 (.reg .rax), .alu .xor .r8 (.reg .rdx), .alu .and .r8 (.reg .rcx),
        .alu .xor .rax (.reg .r8), .alu .xor .rdx (.reg .r8),
        .store (sc (x + 8 * i)) .rax, .store (sc (y + 8 * i)) .rdx]) s fun t =>
      t.mem = (s.mem.writeW (off base (x + 8 * i))
        (if sw then word s.mem base (y + 8 * i) else word s.mem base (x + 8 * i))).writeW
        (off base (y + 8 * i)) (if sw then word s.mem base (x + 8 * i) else word s.mem base (y + 8 * i)) ∧
      KeepsR [.rax, .rdx, .r8] s t := by
  have lx := hs.read (d := x + 8 * i) (n := 8) (by omega_arith)
  have ly := hs.read (d := y + 8 * i) (n := 8) (by omega_arith)
  have wx := hs.write (d := x + 8 * i) (n := 8) (by omega_arith)
  have wy := hs.write (d := y + 8 * i) (n := 8) (by omega_arith)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execAlu, ea_sc,
    State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, RegUpd.rd_arithFlags, hs.rdi, hc, lx, ly, wx, wy, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [(xor_sel sw _ _).1, (xor_sel sw _ _).2]
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

theorem word_write (m : Mem) (base : Addr) {d e : Nat} (hd : d + 8 ≤ 8192) (he : e + 8 ≤ 8192)
    (hde : d + 8 ≤ e ∨ e + 8 ≤ d ∨ e = d) (v : BitVec 64) :
    word (m.writeW (off base d) v) base e = if e = d then v else word m base e := by
  by_cases h : e = d
  · rw [ite_eq_left h, h, word, Mem.readW_writeW_self64]
  · rw [ite_eq_right h]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)

/-- Swap the seven words under the mask, and nothing else. -/
theorem cswap_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : x + 56 ≤ 1536)
    (hy : y + 56 ≤ 1536) (hxy : x + 56 ≤ y ∨ y + 56 ≤ x) {sw : Bool} (hc : s.gpr .rcx = mask sw) :
    WP isa (.block (cswap x y)) s fun t =>
      (∀ i < 7, word t.mem base (x + 8 * i) =
        if sw then word s.mem base (y + 8 * i) else word s.mem base (x + 8 * i)) ∧
      (∀ i < 7, word t.mem base (y + 8 * i) =
        if sw then word s.mem base (x + 8 * i) else word s.mem base (y + 8 * i)) ∧
      Outside2 base x 56 y 56 s.mem t.mem ∧ KeepsR [.rax, .rdx, .r8] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, word t.mem base (x + 8 * i) =
      if sw then word s.mem base (y + 8 * i) else word s.mem base (x + 8 * i)) ∧
    (∀ i < n, word t.mem base (y + 8 * i) =
      if sw then word s.mem base (x + 8 * i) else word s.mem base (y + 8 * i)) ∧
    Outside2 base x (8 * n) y (8 * n) s.mem t.mem ∧ KeepsR [.rax, .rdx, .r8] s t
  have step : ∀ n t, n < 7 → inv n t → WP isa (.block
      [.mov .rax (.mem (sc (x + 8 * n))), .mov .rdx (.mem (sc (y + 8 * n))),
        .mov .r8 (.reg .rax), .alu .xor .r8 (.reg .rdx), .alu .and .r8 (.reg .rcx),
        .alu .xor .rax (.reg .r8), .alu .xor .rdx (.reg .r8),
        .store (sc (x + 8 * n)) .rax, .store (sc (y + 8 * n)) .rdx]) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tc := (tk.1 .rcx (by decide)).trans hc
    refine WP.mono (swapStep_ok (hs.of_keepsR tk (by decide)) hx hy hn tc) fun u ⟨um, uk⟩ => ?_
    have ex : word t.mem base (x + 8 * n) = word s.mem base (x + 8 * n) :=
      tm.word (by omega_arith) (by omega_arith) (by omega_arith)
    have ey : word t.mem base (y + 8 * n) = word s.mem base (y + 8 * n) :=
      tm.word (by omega_arith) (by omega_arith) (by omega_arith)
    refine ⟨fun j hj => ?_, fun j hj => ?_, ?_, tk.trans uk⟩
    · rw [um, word_write _ _ (by omega_arith) (by omega_arith) (by omega_arith),
        word_write _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      by_cases h : j = n
      · subst h
        rw [ite_eq_right (by omega_arith), ite_eq_left rfl, ex, ey]
      · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
        exact tx j (by omega_arith)
    · rw [um, word_write _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      by_cases h : j = n
      · subst h
        rw [ite_eq_left rfl, ex, ey]
      · rw [ite_eq_right (by omega_arith), word_write _ _ (by omega_arith) (by omega_arith) (by omega_arith),
          ite_eq_right (by omega_arith)]
        exact ty j (by omega_arith)
    · intro p hp hq
      rw [um, writeW_outside _ _ _ (by omega_arith : y + 8 * n + 8 < 2 ^ 64) p (by omega_arith),
        writeW_outside _ _ _ (by omega_arith : x + 8 * n + 8 < 2 ^ 64) p (by omega_arith)]
      exact tm p (by omega_arith) (by omega_arith)
  exact wp_range_flatMap (M := isa) (N := 7) inv step 7 (by decide) s
    ⟨fun _ hi => by omega_arith, fun _ hi => by omega_arith, Outside2.refl _ _ _ _ _ _,
      ⟨fun _ _ => rfl, rfl, rfl⟩⟩

end VG.Proof.X448.X86_64

end

end

/-! ### `X448.X86_64.Field`, which this module and modules that import it used -/

section

/-! ### `X448.X86_64.Reduce`, which this module and modules that import it used -/

section

/-!
# X448 on x86-64: the reduction of a product

`reduce o` takes the fourteen words `L + 2⁴⁴⁸ H` of a product at `ACC` to a
seven-word number congruent to it modulo `p` at `[o]`: `L + H`, plus
`H - H mod 2²²⁴`, plus `rot(H)` (`H` rotated by 224 bits), whose top word is
folded twice (`fold2`). `reduce_arith` is the congruence, as arithmetic.
-/

@[expose] public section

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
  have hP := P_eq
  obtain e1 : 2 ^ 448 * H = P * H + (2 ^ 224 + 1) * H := by rw [hP, Nat.add_mul]
  obtain ⟨K, hK⟩ : ∃ K, hi + 2 ^ 32 * h4 + 2 ^ 96 * h5 + 2 ^ 160 * h6 = K := ⟨_, rfl⟩
  obtain e2 : 2 ^ 448 * K = P * K + (2 ^ 224 + 1) * K := by rw [hP, Nat.add_mul]
  obtain e : L + 2 ^ 448 * H = (L + H + 2 ^ 192 * rax + 2 ^ 256 * h4 + 2 ^ 320 * h5 +
      2 ^ 384 * h6 + hi + 2 ^ 32 * (h4 + 2 ^ 64 * (h5 + 2 ^ 64 * (h6 + 2 ^ 64 * (h0 + 2 ^ 64 *
        (h1 + 2 ^ 64 * (h2 + 2 ^ 64 * lo))))))) + P * (H + K) := by
    rw [Nat.mul_add P H K]
    generalize P * H = PH at e1 ⊢
    generalize P * K = PK at e2 ⊢
    clear hP
    omega_arith
  rw [e, Nat.add_mul_mod_self_left]

/-! ## The blocks of `reduce` -/

theorem mov32_ok (s : State) (r : Reg) (v : BitVec 32) :
    WP isa (.block [.mov32 r (.imm v)]) s fun s' => s'.gpr r = v.setWidth 64 ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
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
theorem splitLo_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192)
    {r t : Reg} (hrt : r ≠ t) :
    WP isa (.block [.mov r (.mem (sc d)), .mov32 t (.reg r), .alu .sub r (.reg t)]) s fun s' =>
      (s'.gpr t).toNat = (word s.mem base d).toNat % 2 ^ 32 ∧
      (s'.gpr r).toNat + (s'.gpr t).toNat = (word s.mem base d).toNat ∧
      Keeps [r, t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    load_sc hs hd, Option.map_some, Option.bind_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ hrt, State.setReg32, Option.some.injEq, exists_eq_left']
  obtain hx := toNat_setWidth32 (word s.mem base d)
  refine ⟨?_, ?_, fun r' hr => ?_, rfl, rfl, rfl⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hrt), RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_self, hx]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hrt), RegUpd.gpr_arithFlags,
      RegUpd.gpr_setReg_self, hx]
    have := sub_borrow (word s.mem base d) ((word s.mem base d).setWidth 32 |>.setWidth 64)
    rw [hx] at this
    have : ¬(word s.mem base d).toNat < (word s.mem base d).toNat % 2 ^ 32 :=
      Nat.not_lt.mpr (Nat.mod_le _ _)
    simp only [this, decide_false, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at *
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hr.2,
      RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- `h₃` split into its low half `rdx` and the rest `rax`. -/
theorem splitH_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block [.mov .rax (.mem (sc (h 10))), .mov32 .rdx (.reg .rax),
      .alu .sub .rax (.reg .rdx)]) s fun s' =>
      (s'.gpr .rdx).toNat = (word s.mem base (h 10)).toNat % 2 ^ 32 ∧
      (s'.gpr .rax).toNat + (s'.gpr .rdx).toNat = (word s.mem base (h 10)).toNat ∧
      Keeps [.rax, .rdx] s s' :=
  splitLo_ok hs (by simp only [h, ACC]; omega_arith) (by decide)

/-- The word 4 bytes into the word at `d`: its high half, and the low half of
the next. -/
theorem word_mid (m : Mem) (base : Addr) (d : Nat) :
    (word m base (d + 4)).toNat =
      (word m base d).toNat / 2 ^ 32 + 2 ^ 32 * ((word m base (d + 8)).toNat % 2 ^ 32) := by
  obtain e : ∀ e, (word m base e).toNat = X25519.leNum (Spec.X25519.bytesAt m (off base e) 4) +
      2 ^ 32 * X25519.leNum (Spec.X25519.bytesAt m (off base (e + 4)) 4) := fun e => by
    rw [word, ← X25519.leNum_bytesAt_64, show 8 = 4 + 4 from rfl, X25519.bytesAt_add,
      X25519.leNum_append, X25519.length_bytesAt, off, Offset.add_add]
  obtain l : ∀ e, X25519.leNum (Spec.X25519.bytesAt m (off base e) 4) < 2 ^ 32 := fun e => by
    have := X25519.leNum_lt (Spec.X25519.bytesAt m (off base e) 4)
    rwa [X25519.length_bytesAt] at this
  rw [e d, e (d + 4), e (d + 8), show d + 4 + 4 = d + 8 by omega_arith]
  have := l d; have := l (d + 4); have := l (d + 8); have := l (d + 8 + 4)
  omega_arith

/-- The 32-bit word 4 bytes into the word at `d`: its high half. -/
theorem readW32_mid (m : Mem) (base : Addr) (d : Nat) :
    (m.readW (off base (d + 4)) 32).toNat = (word m base d).toNat / 2 ^ 32 := by
  rw [readW32, ← word, word_mid]
  have := (word m base d).isLt
  omega_arith

/-- `rcx += [d]`'s low half, without overflow. -/
theorem addLo_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192)
    (hb : (s.gpr .rcx).toNat + (s.mem.readW (off base d) 32).toNat < 2 ^ 64) :
    WP isa (.block [.mov32 .rdx (.mem (sc d)), .alu .add .rcx (.reg .rdx)]) s fun s' =>
      (s'.gpr .rcx).toNat = (s.gpr .rcx).toNat + (s.mem.readW (off base d) 32).toNat ∧
      Keeps [.rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    State.load32, ea_sc, hs.rdi, hs.read (d := d) (n := 4) (by omega_arith), ite_true, Option.map_some,
    Option.bind_some, State.setReg32, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.rcx = Reg.rdx), Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_add, toNat_setWidth_32_64, Nat.mod_eq_of_lt hb]
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
    rv s W = rv s [.r8, .r9, .r10] + 2 ^ 192 * rv s [.r11, .r12, .r13, .r14] := by
  simp only [rv, W]; omega_arith

theorem rv5_split (s : State) :
    rv s [.r11, .r12, .r13, .r14, .r15] = rv s [.r11, .r12, .r13, .r14] +
      2 ^ 256 * (s.gpr .r15).toNat := by
  simp only [rv]; omega_arith

theorem len64_1 {α : Type} (a : α) : 64 * [a].length = 64 := rfl
theorem len64_5 {α : Type} (a b c d e : α) : 64 * [a, b, c, d, e].length = 320 := rfl
theorem len64_7 {α : Type} (a b c d e f g : α) : 64 * [a, b, c, d, e, f, g].length = 448 := rfl

theorem mvH (m : Mem) (base : Addr) :
    mv m base (ACC + 56) 7 = (word m base (h 7)).toNat + 2 ^ 64 * ((word m base (h 8)).toNat +
      2 ^ 64 * ((word m base (h 9)).toNat + 2 ^ 64 * ((word m base (h 10)).toNat +
      2 ^ 64 * ((word m base (h 11)).toNat + 2 ^ 64 * ((word m base (h 12)).toNat +
      2 ^ 64 * (word m base (h 13)).toNat))))) := by
  simp only [mv, h, ACC, Nat.reduceAdd, Nat.reduceMul, Nat.mul_zero, Nat.add_zero]

/-- `reduce o`: `[o] ≡ L + 2⁴⁴⁸ H`, for the product `L + 2⁴⁴⁸ H` at `ACC`. -/
theorem reduce_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 56 ≤ ACC) :
    WP isa (.block (reduce o)) s fun s' =>
      fe s'.mem base o % P = (mv s.mem base ACC 7 + 2 ^ 448 * mv s.mem base (ACC + 56) 7) % P ∧
      (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base o 56 s.mem s'.mem := by
  simp only [reduce, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (mov32_ok s .r15 0) fun s1 ⟨z1, k1⟩ => ?_
  obtain hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs1 ACC W W_nodup (by decide) (by decide)) fun s2 ⟨_, v2, k2⟩ => ?_
  obtain hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff, show (List.range 7).map (fun i => Src.mem (sc (h (7 + i)))) =
    Src.mem (sc (h 7)) :: ([h 8, h 9, h 10, h 11, h 12, h 13].map fun d => Src.mem (sc d)) from rfl]
  refine WP.mono (add_chain_ok W s2 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] _ _
    (word s2.mem base (h 7)) _ (fun _ h => h) W_nodup rfl
    (stable_sc hs2 (by decide) (by simp only [h, ACC]; omega_arith))
    (stable_scs hs2 (by decide) _ (by simp only [h, ACC]; decide))) fun s3 ⟨c1, hc1, e3, k3⟩ => ?_
  obtain hs3 := hs2.of_keeps k3 (by decide)
  rw [show ([.alu .adc .r15 (.imm 0), .mov .rax (.mem (sc (h 10))), .mov32 .rdx (.reg .rax),
      .alu .sub .rax (.reg .rdx)] : List Instr) = [.alu .adc .r15 (.imm 0)] ++
      [.mov .rax (.mem (sc (h 10))), .mov32 .rdx (.reg .rax), .alu .sub .rax (.reg .rdx)] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (adcs_ok [.r15] s3 [.r15] [.imm 0] [0] s3 c1 (Keeps.refl _ _) (fun _ h => h)
    (by decide) rfl (.cons (stable_imm0 _ _) .nil) hc1) fun s4 ⟨c4, _, e4, k4⟩ => ?_
  obtain hs4 := hs3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (splitH_ok hs4) fun s5 ⟨d5, a5, k5⟩ => ?_
  obtain hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (add_chain_ok [.r11, .r12, .r13, .r14, .r15] s5 .r11 [.r12, .r13, .r14, .r15]
    (.reg .rax) [.mem (sc (h 11)), .mem (sc (h 12)), .mem (sc (h 13)), .imm 0] (s5.gpr .rax)
    [word s5.mem base (h 11), word s5.mem base (h 12), word s5.mem base (h 13), 0] (fun _ h => h)
    (by decide) rfl (stable_reg s5 (by decide))
    (.cons (stable_sc hs5 (by decide) (by simp only [h, ACC]; omega_arith))
      (.cons (stable_sc hs5 (by decide) (by simp only [h, ACC]; omega_arith))
        (.cons (stable_sc hs5 (by decide) (by simp only [h, ACC]; omega_arith))
          (.cons (stable_imm0 _ _) .nil))))) fun s6 ⟨c6, _, e6, k6⟩ => ?_
  obtain hs6 := hs5.of_keeps k6 (by decide)
  rw [WP.block_append_iff, show ([.mov .rcx (.mem (sc (h 6 + 4))), .mov32 .rdx (.reg .rcx),
      .alu .sub .rcx (.reg .rdx), .mov32 .rdx (.mem (sc (h 13 + 4))), .alu .add .rcx (.reg .rdx)] :
      List Instr) = [.mov .rcx (.mem (sc (h 6 + 4))), .mov32 .rdx (.reg .rcx),
      .alu .sub .rcx (.reg .rdx)] ++ [.mov32 .rdx (.mem (sc (h 13 + 4))), .alu .add .rcx (.reg .rdx)]
      from rfl, WP.block_append_iff]
  refine WP.mono (splitLo_ok hs6 (d := h 6 + 4) (by simp only [h, ACC]; omega_arith) (r := .rcx)
    (t := .rdx) (by decide)) fun s7 ⟨d7, a7, k7⟩ => ?_
  obtain hs7 := hs6.of_keeps k7 (by decide)
  obtain g := fun {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg) (h : r ∉ rs) => k.1 r h
  -- Memory is only read until the stores.
  obtain m2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  obtain m4 : s4.mem = s.mem := k4.2.1.trans (k3.2.1.trans m2)
  obtain m5 : s5.mem = s.mem := k5.2.1.trans m4
  obtain m6 : s6.mem = s.mem := k6.2.1.trans m5
  obtain m7 : s7.mem = s.mem := k7.2.1.trans m6
  -- `rcx`: word 3 of `rot(H)`.
  obtain wm6 := word_mid s.mem base (h 6)
  rw [show h 6 + 8 = h 7 from rfl] at wm6
  obtain r7 : (s7.gpr .rcx).toNat = 2 ^ 32 * ((word s.mem base (h 7)).toNat % 2 ^ 32) := by
    rw [m6] at d7 a7
    have := Nat.div_lt_of_lt_mul (m := (word s.mem base (h 6)).toNat) (n := 2 ^ 32) (k := 2 ^ 32)
      (word s.mem base (h 6)).isLt
    omega_arith
  obtain hi13 := readW32_mid s.mem base (h 13)
  obtain hb13 : (word s.mem base (h 13)).toNat / 2 ^ 32 < 2 ^ 32 :=
    Nat.div_lt_of_lt_mul (word s.mem base (h 13)).isLt
  obtain hl7 : (word s.mem base (h 7)).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  refine WP.mono (addLo_ok hs7 (d := h 13 + 4) (by simp only [h, ACC]; omega_arith)
    (by rw [r7, m7, hi13]; omega_arith)) fun s8 ⟨e8, k8⟩ => ?_
  obtain hs8 := hs7.of_keeps k8 (by decide)
  obtain m8 : s8.mem = s.mem := k8.2.1.trans m7
  rw [m7, hi13, r7] at e8
  -- `+ rot(H)`
  rw [WP.block_append_iff]
  refine WP.mono (add_chain_ok W s8 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] _ _
    (word s8.mem base (h 10 + 4)) [word s8.mem base (h 11 + 4), word s8.mem base (h 12 + 4),
      s8.gpr .rcx, word s8.mem base (h 7 + 4), word s8.mem base (h 8 + 4),
      word s8.mem base (h 9 + 4)] (fun _ h => h) W_nodup rfl
    (stable_sc hs8 (by decide) (by simp only [h, ACC]; omega_arith))
    (.cons (stable_sc hs8 (by decide) (by simp only [h, ACC]; omega_arith))
      (.cons (stable_sc hs8 (by decide) (by simp only [h, ACC]; omega_arith))
        (.cons (stable_reg s8 (by decide))
          (.cons (stable_sc hs8 (by decide) (by simp only [h, ACC]; omega_arith))
            (.cons (stable_sc hs8 (by decide) (by simp only [h, ACC]; omega_arith))
              (.cons (stable_sc hs8 (by decide) (by simp only [h, ACC]; omega_arith)) .nil)))))))
    fun s9 ⟨c9, hc9, e9, k9⟩ => ?_
  obtain hs9 := hs8.of_keeps k9 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (adcs_ok [.r15] s9 [.r15] [.imm 0] [0] s9 c9 (Keeps.refl _ _) (fun _ h => h)
    (by decide) rfl (.cons (stable_imm0 _ _) .nil) hc9) fun s10 ⟨c10, _, e10, k10⟩ => ?_
  obtain hs10 := hs9.of_keeps k10 (by decide)
  -- `r15` along the way, and the bounds that exclude overflow.
  obtain r15_3 : s3.gpr .r15 = 0 := by rw [g k3 _ (by decide), g k2 _ (by decide), z1]; rfl
  rw [len64_1] at e4
  simp only [rv, wv, r15_3, toNat_zero64] at e4
  obtain hc1 := Bool.toNat_le c1
  obtain r15_5 : (s5.gpr .r15).toNat = c1.toNat := by rw [g k5 _ (by decide)]; omega_arith
  obtain l6 := rv_lt s6 [.r11, .r12, .r13, .r14]
  obtain l5 := rv_lt s5 [.r11, .r12, .r13, .r14]
  rw [len64_5] at e6
  rw [rv5_split, rv5_split, r15_5] at e6
  simp only [wv, toNat_zero64] at e6
  simp only [List.length_cons, List.length_nil] at l6 l5
  obtain hc6 : c6.toNat = 0 := by
    have := Bool.toNat_le c6
    have := (word s5.mem base (h 11)).isLt; have := (word s5.mem base (h 12)).isLt
    have := (word s5.mem base (h 13)).isLt; have := (s5.gpr .rax).isLt
    have := (s6.gpr .r15).isLt
    rcases Nat.lt_or_ge c6.toNat 1 with h | h
    · omega_arith
    · exfalso; omega_arith
  rw [len64_1] at e10
  simp only [rv, wv, toNat_zero64] at e10
  obtain r15_9 : s9.gpr .r15 = s6.gpr .r15 := by
    rw [g k9 _ (by decide), g k8 _ (by decide), g k7 _ (by decide)]
  rw [m5] at e6
  rw [m4] at d5 a5
  rw [len64_7, m2] at e3
  rw [len64_7, m8, W_lit] at e9
  rw [k1.2.1, show W.length = 7 from rfl] at v2
  -- The registers along the way.
  obtain w43 : rv s4 W = rv s3 W := k4.rv_eq (by decide)
  obtain w54 : rv s5 W = rv s4 W := k5.rv_eq (by decide)
  obtain w65 : rv s6 [.r8, .r9, .r10] = rv s5 [.r8, .r9, .r10] := k6.rv_eq (by decide)
  obtain w76 : rv s7 W = rv s6 W := k7.rv_eq (by decide)
  obtain w87 : rv s8 W = rv s7 W := k8.rv_eq (by decide)
  obtain sp5 := rvW_split s5
  obtain sp6 := rvW_split s6
  simp only [wv, List.map_cons, List.map_nil] at e3 e9 e6
  rw [W_lit] at e3
  -- `rot(H)`'s words.
  obtain mid := fun d => word_mid s.mem base d
  obtain M10 := mid (h 10); have M11 := mid (h 11); have M12 := mid (h 12)
  obtain M7 := mid (h 7); have M8 := mid (h 8); have M9 := mid (h 9)
  rw [show h 10 + 8 = h 11 from rfl] at M10
  rw [show h 11 + 8 = h 12 from rfl] at M11
  rw [show h 12 + 8 = h 13 from rfl] at M12
  rw [show h 7 + 8 = h 8 from rfl] at M7
  rw [show h 8 + 8 = h 9 from rfl] at M8
  rw [show h 9 + 8 = h 10 from rfl] at M9
  obtain rot := rot_arith ((word s.mem base (h 7)).toNat % 2 ^ 32)
    ((word s.mem base (h 8)).toNat % 2 ^ 32) ((word s.mem base (h 9)).toNat % 2 ^ 32)
    ((word s.mem base (h 10)).toNat % 2 ^ 32) ((word s.mem base (h 11)).toNat % 2 ^ 32)
    ((word s.mem base (h 12)).toNat % 2 ^ 32) ((word s.mem base (h 13)).toNat % 2 ^ 32)
    ((word s.mem base (h 7)).toNat / 2 ^ 32) ((word s.mem base (h 8)).toNat / 2 ^ 32)
    ((word s.mem base (h 9)).toNat / 2 ^ 32) ((word s.mem base (h 10)).toNat / 2 ^ 32)
    ((word s.mem base (h 11)).toNat / 2 ^ 32) ((word s.mem base (h 12)).toNat / 2 ^ 32)
    ((word s.mem base (h 13)).toNat / 2 ^ 32)
  simp only [Nat.mod_add_div] at rot
  rw [← M10, ← M11, ← M12, ← M7, ← M8, ← M9, ← e8] at rot
  -- The whole sum, before the folds.
  obtain tot : rv s10 W + 2 ^ 448 * (s10.gpr .r15).toNat =
      mv s.mem base ACC 7 + ((word s.mem base (h 7)).toNat + 2 ^ 64 * ((word s.mem base (h 8)).toNat +
        2 ^ 64 * ((word s.mem base (h 9)).toNat + 2 ^ 64 * ((word s.mem base (h 10)).toNat +
        2 ^ 64 * ((word s.mem base (h 11)).toNat + 2 ^ 64 * ((word s.mem base (h 12)).toNat +
        2 ^ 64 * (word s.mem base (h 13)).toNat)))))) + 2 ^ 192 * (s5.gpr .rax).toNat +
      2 ^ 256 * (word s.mem base (h 11)).toNat + 2 ^ 320 * (word s.mem base (h 12)).toNat +
      2 ^ 384 * (word s.mem base (h 13)).toNat + (word s.mem base (h 10)).toNat / 2 ^ 32 +
      2 ^ 32 * ((word s.mem base (h 11)).toNat + 2 ^ 64 * ((word s.mem base (h 12)).toNat +
        2 ^ 64 * ((word s.mem base (h 13)).toNat + 2 ^ 64 * ((word s.mem base (h 7)).toNat +
        2 ^ 64 * ((word s.mem base (h 8)).toNat + 2 ^ 64 * ((word s.mem base (h 9)).toNat +
        2 ^ 64 * ((word s.mem base (h 10)).toNat % 2 ^ 32))))))) := by
    obtain w10 : rv s10 W = rv s9 W := k10.rv_eq (by decide)
    -- the first two additions
    obtain S6 : rv s6 W + 2 ^ 448 * (s6.gpr .r15).toNat = mv s.mem base ACC 7 +
        ((word s.mem base (h 7)).toNat + 2 ^ 64 * ((word s.mem base (h 8)).toNat +
        2 ^ 64 * ((word s.mem base (h 9)).toNat + 2 ^ 64 * ((word s.mem base (h 10)).toNat +
        2 ^ 64 * ((word s.mem base (h 11)).toNat + 2 ^ 64 * ((word s.mem base (h 12)).toNat +
        2 ^ 64 * (word s.mem base (h 13)).toNat)))))) + 2 ^ 192 * (s5.gpr .rax).toNat +
        2 ^ 256 * (word s.mem base (h 11)).toNat + 2 ^ 320 * (word s.mem base (h 12)).toNat +
        2 ^ 384 * (word s.mem base (h 13)).toNat := by
      omega_using [e3, e4, e6, v2, w43, w54, w65, sp5, sp6, hc6, r15_5, hc1]
    obtain r6 : (s6.gpr .r15).toNat ≤ 2 := by
      obtain b1 := rv_lt s6 W; rw [len_W] at b1
      obtain b2 := mv_lt s.mem base ACC 7
      rw [show 64 * 7 = 448 from rfl] at b2
      obtain b7 := (word s.mem base (h 7)).isLt; have b8 := (word s.mem base (h 8)).isLt
      obtain b9 := (word s.mem base (h 9)).isLt; have b10 := (word s.mem base (h 10)).isLt
      obtain b11 := (word s.mem base (h 11)).isLt; have b12 := (word s.mem base (h 12)).isLt
      obtain b13 := (word s.mem base (h 13)).isLt; have ba := (s5.gpr .rax).isLt
      omega_using [S6, b1, b2, b7, b8, b9, b10, b11, b12, b13, ba]
    obtain c10z : (s10.gpr .r15).toNat = (s6.gpr .r15).toNat + c9.toNat := by
      rw [r15_9] at e10
      obtain b9 := Bool.toNat_le c9; have b10 := Bool.toNat_le c10
      omega_using [e10, r6, b9, b10]
    rw [w10, c10z]
    simp only [Nat.mul_zero, Nat.add_zero] at e9
    rw [w87, w76, rot] at e9
    generalize (word s.mem base (h 10)).toNat / 2 ^ 32 = HI at e9 ⊢
    generalize (word s.mem base (h 10)).toNat % 2 ^ 32 = LO at e9 ⊢
    omega_using [S6, e9]
  obtain hsum : (s10.gpr .r15).toNat < 4 := by
    obtain hHI : (word s.mem base (h 10)).toNat / 2 ^ 32 < 2 ^ 32 :=
      Nat.div_lt_of_lt_mul (word s.mem base (h 10)).isLt
    obtain hLO : (word s.mem base (h 10)).toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    generalize (word s.mem base (h 10)).toNat / 2 ^ 32 = HI at tot hHI
    generalize (word s.mem base (h 10)).toNat % 2 ^ 32 = LO at tot hLO
    obtain b1 := rv_lt s10 W; rw [len_W] at b1
    obtain b2 := mv_lt s.mem base ACC 7
    rw [show 64 * 7 = 448 from rfl] at b2
    obtain b7 := (word s.mem base (h 7)).isLt; have b8 := (word s.mem base (h 8)).isLt
    obtain b9 := (word s.mem base (h 9)).isLt; have b10 := (word s.mem base (h 10)).isLt
    obtain b11 := (word s.mem base (h 11)).isLt; have b12 := (word s.mem base (h 12)).isLt
    obtain b13 := (word s.mem base (h 13)).isLt; have ba := (s5.gpr .rax).isLt
    omega_using [tot, b1, b2, b7, b8, b9, b10, b11, b12, b13, ba, hHI, hLO]
  rw [WP.block_append_iff]
  refine WP.mono (fold2_ok s10 (by omega_arith)) fun s11 ⟨e11, k11⟩ => ?_
  obtain hs11 := hs10.of_keeps k11 (by decide)
  refine WP.mono (stores_ok hs11 o W (by rw [show W.length = 7 from rfl]; simp only [ACC] at ho; omega_arith)) fun s12 ⟨e12, o12, g12, rd12, wr12⟩ => ?_
  rw [show W.length = 7 from rfl] at e12 o12
  obtain K : Keeps clob s s11 := (k1.mono (by decide)).trans <| (k2.mono (by decide)).trans <|
    (k3.mono (by decide)).trans <| (k4.mono (by decide)).trans <| (k5.mono (by decide)).trans <|
    (k6.mono (by decide)).trans <| (k7.mono (by decide)).trans <| (k8.mono (by decide)).trans <|
    (k9.mono (by decide)).trans <| (k10.mono (by decide)).trans (k11.mono (by decide))
  refine ⟨?_, fun r hr => (g12 r).trans (K.1 r hr), rd12.trans K.2.2.1, wr12.trans K.2.2.2,
    by rw [← K.2.1]; exact o12⟩
  · show mv s12.mem base o 7 % P = _
    rw [e12, e11, tot, mvH]
    refine Eq.symm (reduce_arith (mv s.mem base ACC 7) (word s.mem base (h 7)).toNat (word s.mem base (h 8)).toNat (word s.mem base (h 9)).toNat (word s.mem base (h 10)).toNat (word s.mem base (h 11)).toNat (word s.mem base (h 12)).toNat (word s.mem base (h 13)).toNat ((word s.mem base (h 10)).toNat % 2 ^ 32) ((word s.mem base (h 10)).toNat / 2 ^ 32) (s5.gpr .rax).toNat
      ?_ ?_)
    · exact Nat.mod_add_div _ _
    · rw [← d5]; exact a5

end VG.Proof.X448.X86_64

end

end

/-!
# X448 on x86-64: the field multiplications

Each field operation on the working space as a change of the field element
`F` it writes: the element at `o` becomes the result, the bytes outside it
and the product's words at `ACC` are unchanged, and so are the registers but
those the arithmetic uses (`Op`).
-/

@[expose] public section

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448
open VG.Spec.X448 (P)

/-- The field element at `base + o`, in `GF(p)`. -/
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X448.Fe := toFe (fe m base o)

/-- A field element's slot: below the product's words. -/
abbrev Slot (o : Nat) : Prop := o + 56 ≤ ACC

/-- A field operation's effect but for its result: the registers but `clob`,
the regions and the memory outside the 56 bytes at `base + o` and the
product's words are unchanged. -/
structure Op (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside2 base o 56 ACC 112 s.mem s'.mem

theorem mv_add (m : Mem) (base : Addr) :
    ∀ (o a b : Nat), mv m base o (a + b) = mv m base o a + 2 ^ (64 * a) * mv m base (o + 8 * a) b
  | o, 0, b => by simp [mv]
  | o, a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega_using [], mv, mv, mv_add m base (o + 8) a b, pow64_succ,
      show o + 8 + 8 * a = o + 8 * (a + 1) by omega_using []]
    generalize 2 ^ (64 * a) = Q
    grind

theorem zeroAcc_ok (s : State) :
    WP isa (.block zeroAcc) s fun s' => rv s' (acc 0) = 0 ∧ Keeps [.r15, .rcx, .rbp] s s' := by
  apply WP.of_runBlock
  simp only [zeroAcc, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [acc, accR_mod, Nat.zero_add, Nat.reduceMod, List.getD_cons_zero,
      List.getD_cons_succ, rv, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]
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
theorem product_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : Slot o)
    {x y : Nat} (hx : x < 2 ^ (64 * 7)) (hy : y < 2 ^ (64 * 7))
    (hcol : mv s.mem base ACC (7 + 7) + 2 ^ (64 * (7 + 7)) * rv s (acc (7 + 7)) = x * y) :
    WP isa (.block (reduce o)) s fun s' =>
      fe s'.mem base o % P = x * y % P ∧
      (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base o 56 s.mem s'.mem := by
  refine WP.mono (reduce_ok hs ho) fun s' ⟨e, g, rd, wr, out⟩ => ⟨?_, g, rd, wr, out⟩
  have hl := prod_lt hx hy
  have h0 : rv s (acc (7 + 7)) = 0 := by
    rcases Nat.eq_zero_or_pos (rv s (acc (7 + 7))) with h | h
    · exact h
    · exfalso
      have := Nat.mul_le_mul_left (2 ^ (64 * (7 + 7))) h
      generalize 2 ^ (64 * (7 + 7)) = Q at *
      omega_using [hcol, hl, this]
  generalize 2 ^ (64 * (7 + 7)) = Q at hcol
  rw [h0, Nat.mul_zero, Nat.add_zero, mv_add, show 64 * 7 = 448 from rfl,
    show ACC + 8 * 7 = ACC + 56 from rfl] at hcol
  rw [e, ← hcol]

theorem val7_congr {f g : Nat → Nat} (h : ∀ i < 7, f i = g i) : val7 f = val7 g := by
  simp only [val7, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
    h 4 (by decide), h 5 (by decide), h 6 (by decide)]

theorem colX_clob : ∀ r ∈ colX, r ∈ clob := by decide
theorem acc_clob : ∀ r ∈ [Reg.r15, .rcx, .rbp], r ∈ clob := by decide
theorem w_acc : ∀ j < 7, w j ∉ [Reg.r15, .rcx, .rbp] := by decide
theorem W_clob : ∀ r ∈ W, r ∈ clob := by decide

/-- The end of `mul` and `sqr`: the columns, then the reduction, with the
columns' operands `xv`, `yv` whose values are `x` and `y`. -/
theorem colsReduce_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : Slot o)
    (xs : Nat → Src) (xv : Nat → BitVec 64) (cols : Nat → List Term)
    (hx : ∀ s', (∀ r, r ∉ colX → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Outside base ACC 112 s.mem s'.mem → ∀ i < 7, Stable colX s' (xs i) (xv i))
    (hc : ∀ k < 14, ∀ t ∈ cols k, t.i < 7 ∧ t.j < 7) (hw : ∀ k < 14, ((cols k).map termK).sum ≤ 7)
    (h0 : rv s (acc 0) = 0) {x y : Nat} (hxl : x < 2 ^ (64 * 7)) (hyl : y < 2 ^ (64 * 7))
    (hsum : colsVal (fun i => (xv i).toNat) (fun j => (s.gpr (w j)).toNat) cols 0 14 = x * y) :
    WP isa (.block (columns xs w cols ++ reduce o)) s fun s' =>
      fe s'.mem base o % P = x * y % P ∧ (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside2 base o 56 ACC 112 s.mem s'.mem := by
  rw [WP.block_append_iff, columns]
  refine WP.mono (columns_ok hs xs w xv cols hx (by decide) hc hw h0 (7 + 7) (Nat.le_refl _))
    fun s1 ⟨g1, rd1, wr1, o1, e1, _⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ rdi_colX).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (product_ok hs1 ho hxl hyl (by rw [e1]; exact hsum)) fun s2 ⟨e2, g2, rd2, wr2, o2⟩ =>
    ⟨e2, fun r hr => (g2 r hr).trans (g1 r fun h => hr (colX_clob r h)), rd2.trans rd1, wr2.trans wr1,
      (o1.right o 56).trans (o2.left ACC 112)⟩

/-- `[o] = [a] · [b]`. -/
theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mul o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  rw [mul, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok hs b W W_nodup (by decide)
    (by rw [show W.length = 7 from rfl]; omega_using [hb'])) fun s1 ⟨w1, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroAcc_ok s1) fun s2 ⟨z2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have m2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  refine WP.mono (colsReduce_ok hs2 ho (fun i => .mem (sc (a + 8 * i)))
    (fun i => word s2.mem base (a + 8 * i)) mulCol
    (fun s' g _ wr out i hi => by
      have hsS : Scr s' base := ⟨(g _ rdi_colX).trans hs2.rdi, wr ▸ hs2.wr, hs2.nowrap⟩
      have := stable_sc hsS rdi_colX (d := a + 8 * i) (by omega_using [ha', hi])
      rwa [out.word (by simp only [ACC]; omega_using [ha', hi]) (by omega_using [ha', hi])] at this)
    mulCol_hc mulCol_hw z2 (mv_lt s.mem base a 7) (mv_lt s.mem base b 7) ?_)
    fun s' ⟨e, g, rd, wr, out⟩ => ⟨⟨fun r hr => ?_, rd.trans (k2.2.2.1.trans k1.2.2.1),
      wr.trans (k2.2.2.2.trans k1.2.2.2), by rw [← m2]; exact out⟩, ?_⟩
  · rw [mulCols_sum, mv7, mv7, m2]
    refine congrArg (val7 _ * ·) (val7_congr fun j hj => ?_)
    rw [k2.1 _ (w_acc j hj)]
    exact congrArg BitVec.toNat (w1 j hj .r8)
  · rw [g r hr, k2.1 r (fun h => hr (acc_clob r h)),
      k1.1 r (fun h => hr (W_clob r h))]
  · exact toFe_mul e

theorem w_colX : ∀ j < 7, w j ∉ colX := by decide

/-- `[o] = [a]²`. -/
theorem sqr_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqr o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a := by
  have ha' : a + 56 ≤ 1536 := ha
  rw [sqr, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok hs a W W_nodup (by decide)
    (by rw [show W.length = 7 from rfl]; omega_using [ha'])) fun s1 ⟨w1, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroAcc_ok s1) fun s2 ⟨z2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have m2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have v2 : val7 (fun j => (s2.gpr (w j)).toNat) = fe s.mem base a := by
    rw [fe, mv7]
    refine val7_congr fun j hj => ?_
    rw [k2.1 _ (w_acc j hj)]
    exact congrArg BitVec.toNat (w1 j hj .r8)
  refine WP.mono (colsReduce_ok hs2 ho (fun i => .reg (w i)) (fun i => s2.gpr (w i)) sqrCol
    (fun s' g _ _ _ i hi => by
      have := stable_reg (X := colX) s' (w_colX i hi)
      rwa [g _ (w_colX i hi)] at this)
    sqrCol_hc sqrCol_hw z2 (mv_lt s.mem base a 7) (mv_lt s.mem base a 7)
    (by rw [sqrCols_sum, v2]))
    fun s' ⟨e, g, rd, wr, out⟩ => ⟨⟨fun r hr => ?_, rd.trans (k2.2.2.1.trans k1.2.2.1),
      wr.trans (k2.2.2.2.trans k1.2.2.2), by rw [← m2]; exact out⟩, toFe_mul e⟩
  rw [g r hr, k2.1 r (fun h => hr (acc_clob r h)), k1.1 r (fun h => hr (W_clob r h))]

end VG.Proof.X448.X86_64

end

end

/-!
# X448 on x86-64: addition, subtraction, `a24` and the swap

`add`, `sub` and `mulSmall` as carry chains, multiply-accumulate steps and
folds, and `cswap` word by word (`wp_range_flatMap`).
-/

@[expose] public section

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448
open VG.Spec.X448 (P)

theorem words_eq (o : Nat) : words o =
    Src.mem (sc o) :: ([o + 8, o + 16, o + 24, o + 32, o + 40, o + 48].map fun d => Src.mem (sc d)) :=
  rfl

theorem wv_words (m : Mem) (base : Addr) (o : Nat) :
    wv (word m base o :: [o + 8, o + 16, o + 24, o + 32, o + 40, o + 48].map fun d => word m base d) =
      fe m base o := by
  simp only [wv, List.map_cons, List.map_nil, mv, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero,
    Nat.add_zero]

theorem wv_words' (m : Mem) (base : Addr) (o : Nat) :
    wv ([o, o + 8, o + 16, o + 24, o + 32, o + 40, o + 48].map fun d => word m base d) =
      fe m base o := wv_words m base o

theorem W_len : W.length = 7 := rfl

/-- `[o] = [a] + [b]`. -/
theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (add o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a + F s.mem base b := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  have ho' : o + 56 ≤ 1536 := ho
  rw [add, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok hs a W W_nodup (by decide) (by rw [W_len]; omega_arith))
    fun s1 ⟨_, v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff, words_eq]
  refine WP.mono (add_chain_ok W s1 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] _ _
    (word s1.mem base b) _ (fun _ h => h) W_nodup rfl (stable_sc hs1 (by decide) (by omega_arith))
    (stable_scs hs1 (by decide) _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega_arith)))
    fun s2 ⟨c2, hc2, e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (carryOut_ok s2 hc2) fun s3 ⟨e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fold2_ok s3 (by rw [e3]; cases c2 <;> decide)) fun s4 ⟨e4, k4⟩ => ?_
  have hs4 := ((hs1.of_keeps k2 (by decide)).of_keeps k3 (by decide)).of_keeps k4 (by decide)
  refine WP.mono (stores_ok hs4 o W (by rw [W_len]; omega_arith)) fun s5 ⟨e5, o5, g5, rd5, wr5⟩ => ?_
  rw [W_len] at e5 o5
  have K : Keeps clob s s4 := (k1.mono W_clob).trans <| (k2.mono (by decide)).trans <|
    (k3.mono (by decide)).trans (k4.mono (by decide))
  refine ⟨⟨fun r hr => (g5 r).trans (K.1 r hr), rd5.trans K.2.2.1, wr5.trans K.2.2.2,
    by rw [← K.2.1]; exact o5.left ACC 112⟩, toFe_add ?_⟩
  have w32 : rv s3 W = rv s2 W := k3.rv_eq (by decide)
  rw [len64_7, W_lit, wv_words, v1, W_len] at e2
  rw [k1.2.1] at e2
  change mv s5.mem base o 7 % P = (mv s.mem base a 7 + fe s.mem base b) % P
  rw [e5, e4, w32, e3, e2]

/-- `[o] = [a] - [b]`. -/
theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (sub o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a - F s.mem base b := by
  have ha' : a + 56 ≤ 1536 := ha
  have hb' : b + 56 ≤ 1536 := hb
  have ho' : o + 56 ≤ 1536 := ho
  simp only [sub, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs a W W_nodup (by decide) (by rw [W_len]; omega_arith))
    fun s1 ⟨_, v1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff, words_eq]
  refine WP.mono (sub_chain_ok W s1 .r8 [.r9, .r10, .r11, .r12, .r13, .r14] _ _
    (word s1.mem base b) _ (fun _ h => h) W_nodup rfl (stable_sc hs1 (by decide) (by omega_arith))
    (stable_scs hs1 (by decide) _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega_arith)))
    fun s2 ⟨c0, hc0, e2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (carryOut_ok s2 hc0) fun s3 ⟨e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (unfold_ok s3 (by rw [e3]; cases c0 <;> decide)) fun s4 ⟨c1, hc1, e4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (carryOut_ok s4 hc1) fun s5 ⟨e5, k5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (unfold_ok s5 (by rw [e5]; cases c1 <;> decide)) fun s6 ⟨c2, _, e6, k6⟩ => ?_
  have hs6 := ((((hs1.of_keeps k2 (by decide)).of_keeps k3 (by decide)).of_keeps k4
    (by decide)).of_keeps k5 (by decide)).of_keeps k6 (by decide)
  refine WP.mono (stores_ok hs6 o W (by rw [W_len]; omega_arith)) fun s7 ⟨e7, o7, g7, rd7, wr7⟩ => ?_
  rw [W_len] at e7 o7
  have K : Keeps clob s s6 := (k1.mono W_clob).trans <| (k2.mono (by decide)).trans <|
    (k3.mono (by decide)).trans <| (k4.mono (by decide)).trans <| (k5.mono (by decide)).trans
      (k6.mono (by decide))
  refine ⟨⟨fun r hr => (g7 r).trans (K.1 r hr), rd7.trans K.2.2.1, wr7.trans K.2.2.2,
    by rw [← K.2.1]; exact o7.left ACC 112⟩, toFe_sub ?_⟩
  have w32 : rv s3 W = rv s2 W := k3.rv_eq (by decide)
  have w54 : rv s5 W = rv s4 W := k5.rv_eq (by decide)
  rw [len64_7, W_lit, wv_words, v1, W_len, k1.2.1] at e2
  rw [e3, w32] at e4
  rw [e5, w54] at e6
  have l2 := rv_lt s2 W; have l4 := rv_lt s4 W; have l6 := rv_lt s6 W
  rw [len_W] at l2 l4 l6
  have b0 := Bool.toNat_le c0; have b1 := Bool.toNat_le c1; have b2 := Bool.toNat_le c2
  have hc2 : c2.toNat = 0 := by
    rcases Nat.lt_or_ge c1.toNat 1 with h | h
    · omega_arith
    · rcases Nat.lt_or_ge c2.toNat 1 with h' | h'
      · omega_arith
      · exfalso; omega_arith
  have hP := P_eq
  have p0 : 2 ^ 448 * c0.toNat = P * c0.toNat + (2 ^ 224 + 1) * c0.toNat := by
    rw [hP, Nat.add_mul]
  have p1 : 2 ^ 448 * c1.toNat = P * c1.toNat + (2 ^ 224 + 1) * c1.toNat := by
    rw [hP, Nat.add_mul]
  have key : rv s6 W + fe s.mem base b = fe s.mem base a + P * (c0.toNat + c1.toNat) := by
    rw [Nat.mul_add P]
    generalize P * c0.toNat = q0 at p0 ⊢
    generalize P * c1.toNat = q1 at p1 ⊢
    clear hP
    simp only [fe] at e2 ⊢
    omega_arith
  change (mv s7.mem base o 7 + fe s.mem base b) % P = _
  rw [e7, key, Nat.add_mul_mod_self_left]

theorem init_ok (s : State) (k : BitVec 32) :
    WP isa (.block (([.mov32 .rcx (.imm k), .mov32 .rbp (.imm 0)] : List Instr) ++
      W.map fun r => .mov32 r (.imm 0))) s fun s' =>
      rv s' W = 0 ∧ s'.gpr .rbp = 0 ∧ s'.gpr .rcx = k.setWidth 64 ∧ Keeps (.rcx :: .rbp :: W) s s' := by
  apply WP.of_runBlock
  simp only [W, List.map_cons, List.map_nil, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, readSrc32, Option.map_some, State.setReg32,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [rv, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]; rfl
  · simp only [RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2, ite_false]

theorem ldStable_scs {X : List Reg} {s : State} {base : Addr} (hs : Scr s base) (hX : .rdi ∉ X) :
    ∀ ds : List Nat, (∀ d ∈ ds, d + 8 ≤ 8192) →
      List.Forall₂ (LdStable X s) (ds.map fun d => .mov .rax (.mem (sc d)))
        (ds.map fun d => word s.mem base d)
  | [], _ => .nil
  | d :: ds, h => .cons (ldStable_sc hs hX (h d List.mem_cons_self))
      (ldStable_scs hs hX ds fun d' hd => h d' (List.mem_cons_of_mem _ hd))

/-- `[o] = k · [a]`, for `k < 2¹⁶`. -/
theorem mulSmall_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) {k : BitVec 32} (hk : k.toNat < 2 ^ 16) :
    WP isa (.block (mulSmall o a k)) s fun s' =>
      Op base o s s' ∧ fe s'.mem base o % P = k.toNat * fe s.mem base a % P := by
  have ha' : a + 56 ≤ 1536 := ha
  have ho' : o + 56 ≤ 1536 := ho
  simp only [mulSmall, List.append_assoc]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (init_ok s k) fun s1 ⟨z1, b1, c1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff, show (List.range 7).map (fun i => Instr.mov .rax (.mem (sc (a + 8 * i)))) =
    [a, a + 8, a + 16, a + 24, a + 32, a + 40, a + 48].map fun d => .mov .rax (.mem (sc d)) from rfl]
  refine WP.mono (mulSteps_ok [.rax, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14] s1 W _
    _ s1 (Keeps.refl _ _) (by decide) (by decide) (by decide) rfl
    (ldStable_scs hs1 (by decide) _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega_arith)))
    fun s2 ⟨e2, k2⟩ => ?_
  rw [len_W, z1, b1, c1, wv_words', k1.2.1] at e2
  have hk' : (k.setWidth 64).toNat = k.toNat := toNat_setWidth_32_64 k
  rw [hk', toNat_zero64] at e2
  rw [WP.block_append_iff]
  have hs2 := hs1.of_keeps k2 (by decide)
  refine WP.mono (show WP isa (.block [.mov .r15 (.reg .rbp)]) s2 fun s' =>
      s'.gpr .r15 = s2.gpr .rbp ∧ Keeps [.r15] s2 s' by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr]) fun s3 ⟨e3, k3⟩ => ?_
  have hlt := fe_lt s.mem base a
  have hb : (s2.gpr .rbp).toNat < 2 ^ 16 := by
    have h2 := Nat.mul_lt_mul'' hk hlt
    generalize k.toNat * fe s.mem base a = X at e2 h2
    generalize (2 : Nat) ^ 448 = Q at e2 h2
    have h1 : Q * (s2.gpr .rbp).toNat ≤ X := by omega_arith
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h1 (Nat.mul_comm (2 ^ 16) Q ▸ h2))
  rw [WP.block_append_iff]
  refine WP.mono (fold2_ok s3 (by rw [e3]; omega_arith)) fun s4 ⟨e4, k4⟩ => ?_
  have hs4 := (hs2.of_keeps k3 (by decide)).of_keeps k4 (by decide)
  refine WP.mono (stores_ok hs4 o W (by rw [W_len]; omega_arith)) fun s5 ⟨e5, o5, g5, rd5, wr5⟩ => ?_
  rw [W_len] at e5 o5
  have K : Keeps clob s s4 := (k1.mono (by decide)).trans <| (k2.mono (by decide)).trans <|
    (k3.mono (by decide)).trans (k4.mono (by decide))
  refine ⟨⟨fun r hr => (g5 r).trans (K.1 r hr), rd5.trans K.2.2.1, wr5.trans K.2.2.2,
    by rw [← K.2.1]; exact o5.left ACC 112⟩, ?_⟩
  have w32 : rv s3 W = rv s2 W := k3.rv_eq (by decide)
  change mv s5.mem base o 7 % P = _
  rw [e5, e4, w32, e3, e2, Nat.zero_add]

end VG.Proof.X448.X86_64
