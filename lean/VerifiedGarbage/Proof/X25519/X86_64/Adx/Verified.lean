import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Proof.X25519.X86_64.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Adx.Steps`. -/
section

/-!
# X25519 on x86-64: the steps of the BMI2/ADX field arithmetic

The steps `mulX`, `sqrX` and `a24X` are made of (see
`Impl/X25519/X86_64/Adx.lean`), each run symbolically once, for any registers:
a product whose low half is added through CF (`mulAcc`), or through OF while
its high half is added through CF (`madd`), the last of a row (`maddLast`), a
word doubled through CF while another is added through OF (`dblAdd`), and the
instructions around them. Each states what it computes as an equation on
numbers, the carries in and out included, which `omega` composes.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

theorem of_setReg (s : State) (r : Reg) (v : BitVec 64) : (s.setReg r v).of = s.of := rfl
theorem of_setFlags (s : State) (a b c d : Option Bool) : (s.setFlags a b c d).of = b := rfl

/-- `mulx hi, lo, src` runs as `setReg lo` then `setReg hi`. -/
theorem execMulx_eq {s : State} {hi lo : Reg} {src : Src} {v : BitVec 64}
    (hsrc : VG.X86_64.readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) :
    execMulx hi lo src s = some ((s.setReg lo (BitVec.ofNat 64 ((s.gpr .rdx).toNat *
      v.toNat))).setReg hi (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64))) := by
  cases src with
  | imm n => exact absurd rfl (himm n)
  | reg r => simp only [execMulx, hsrc, Option.map_some]
  | mem m => simp only [execMulx, hsrc, Option.map_some]

/-- `xor ebp, ebp`. -/
theorem clear_ok (s : State) :
    WP isa (.block [clear]) s fun s' =>
      s'.gpr .rbp = 0 ∧ s'.cf = some false ∧ s'.of = some false ∧ Keeps [.rbp] s s' := by
  apply WP.of_runBlock
  simp only [clear, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, VG.X86_64.readSrc32,
    Option.bind_some, State.setReg32, RegUpd.gpr_setReg_self, BitVec.xor_self,
    RegUpd.cf_setReg, VG.Proof.X25519.X86_64.of_setReg, arithFlags, State.setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `mov rdx, src`. -/
theorem movRdx_ok (s : State) {src : Src} {v : BitVec 64} (hsrc : VG.X86_64.readSrc s src = some v) :
    WP isa (.block [.mov .rdx src]) s fun s' =>
      s'.gpr .rdx = v ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hsrc, Option.map_some,
    RegUpd.gpr_setReg_self, RegUpd.cf_setReg, VG.Proof.X25519.X86_64.of_setReg, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `mov edx, k`. -/
theorem movRdxImm_ok (s : State) (k : BitVec 32) :
    WP isa (.block [.mov32 .rdx (.imm k)]) s fun s' =>
      (s'.gpr .rdx).toNat = k.toNat ∧ s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, VG.Proof.X25519.X86_64.of_setReg, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le k.isLt (by decide))]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `mulx hi, lo, src`: `lo + 2⁶⁴ hi = rdx · src`, the flags unchanged. -/
theorem mulx_ok (s : State) {hi lo : Reg} {src : Src} {v : BitVec 64}
    (hsrc : VG.X86_64.readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hhl : hi ≠ lo) :
    WP isa (.block [.mulx hi lo src]) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat = (s.gpr .rdx).toNat * v.toNat ∧
      s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [hi, lo] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X25519.X86_64.execMulx_eq hsrc himm,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hhl), RegUpd.cf_setReg, VG.Proof.X25519.X86_64.of_setReg,
    Option.some.injEq, exists_eq_left']
  refine ⟨mulx_arith _ _, (by trivial), (by trivial), fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2]

/-- `adcx x, rbp` with `rbp = 0`: the carry CF added into `x`. -/
theorem carryC_ok (s : State) {x : Reg} {c : Bool} (hc : s.cf = some c) (hz : s.gpr .rbp = 0) :
    WP isa (.block [.adcx x (.reg .rbp)]) s fun s' =>
      ∃ c', s'.cf = some c' ∧ s'.of = s.of ∧
        (s'.gpr x).toNat + 2 ^ 64 * c'.toNat = (s.gpr x).toNat + c.toNat ∧ Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdcx, VG.X86_64.readSrc, hz, hc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.cf_setReg,
    RegUpd.cf_setFlags, VG.Proof.X25519.X86_64.of_setReg, VG.Proof.X25519.X86_64.of_setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have := adc_carry (s.gpr x) 0 c
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at this ⊢
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `mulx y, rax, src`, `adcx x, rax`: `rdx · src` added at `x` through CF,
its high half into `y`. -/
theorem mulAcc_ok (s : State) {x y : Reg} {src : Src} {v : BitVec 64} {c : Bool}
    (hsrc : VG.X86_64.readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hc : s.cf = some c)
    (hxa : x ≠ .rax) (hya : y ≠ .rax) (hxy : x ≠ y) :
    WP isa (.block (mulAcc x y src)) s fun s' =>
      ∃ c', s'.cf = some c' ∧ s'.of = s.of ∧
        (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr y).toNat + 2 ^ 64 * c'.toNat =
          (s.gpr x).toNat + c.toNat + (s.gpr .rdx).toNat * v.toNat ∧
        Keeps [.rax, x, y] s s' := by
  apply WP.of_runBlock
  simp only [mulAcc, runBlock_cons, runStep_some, runBlock_nil, exec, VG.Proof.X25519.X86_64.execMulx_eq hsrc himm,
    execAdcx, VG.X86_64.readSrc, Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hya), RegUpd.gpr_setReg_of_ne _ _ hxy,
    RegUpd.gpr_setReg_of_ne _ _ hxa, RegUpd.cf_setReg, RegUpd.cf_setFlags, VG.Proof.X25519.X86_64.of_setReg,
    VG.Proof.X25519.X86_64.of_setFlags, hc, Option.some.injEq, exists_eq_left']
  refine ⟨(by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · simp only [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxy),
      RegUpd.gpr_setFlags]
    have e1 := adc_carry (s.gpr x) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat)) c
    have e2 := mulx_arith (s.gpr .rdx) v
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2.1, RegUpd.gpr_setFlags,
      RegUpd.gpr_setReg_of_ne _ _ hr.2.2, RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- `mulx rcx, rax, src`, `adox x, rax`, `adcx y, rcx`: the product
`rdx · src` added at `x` (with the carry OF) and `y` (the next word, with the
carry CF), the carries out in OF (into `y`'s word) and CF (into the next). -/
theorem madd_ok (s : State) {x y : Reg} {src : Src} {v : BitVec 64} {c o : Bool}
    (hsrc : VG.X86_64.readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hc : s.cf = some c)
    (ho : s.of = some o) (hxh : x ≠ .rcx) (hxl : x ≠ .rax) (hyh : y ≠ .rcx) (hyl : y ≠ .rax)
    (hxy : x ≠ y) :
    WP isa (.block (madd x y src)) s fun s' =>
      ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
        (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr y).toNat + 2 ^ 64 * o'.toNat + 2 ^ 128 * c'.toNat =
          (s.gpr x).toNat + 2 ^ 64 * (s.gpr y).toNat + o.toNat + 2 ^ 64 * c.toNat +
            (s.gpr .rdx).toNat * v.toNat ∧
        Keeps [.rcx, .rax, x, y] s s' := by
  apply WP.of_runBlock
  simp only [madd, runBlock_cons, exec, VG.Proof.X25519.X86_64.execMulx_eq hsrc himm, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, execAdcx, VG.X86_64.readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hxh,
    RegUpd.gpr_setReg_of_ne _ _ hxl, RegUpd.gpr_setReg_of_ne _ _ (by decide : Reg.rax ≠ .rcx),
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxh),
    RegUpd.gpr_setReg_of_ne _ _ hyh, RegUpd.gpr_setReg_of_ne _ _ hyl,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxy), RegUpd.gpr_setFlags, VG.Proof.X25519.X86_64.of_setReg, VG.Proof.X25519.X86_64.of_setFlags,
    RegUpd.cf_setReg, RegUpd.cf_setFlags, ho, hc, Option.some.injEq, exists_eq_left']
  refine ⟨_, _, (by trivial), (by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · simp only [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hxy, RegUpd.gpr_setFlags]
    have e1 := adc_carry (s.gpr x) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat)) o
    have e2 := adc_carry (s.gpr y) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64)) c
    have e3 := mulx_arith (s.gpr .rdx) v
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.1,
      RegUpd.gpr_setFlags, RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.1]

/-- `mulx y, rax, src`, `adox x, rax`, `adcx y, rbp`, `adox y, rbp`, with
`rbp = 0`: the product added at `x` (with the carry OF), its high half into
`y` (overwritten) with the carry CF, and the carry out of `x` into `y` too. -/
theorem maddLast_ok (s : State) {x y : Reg} {src : Src} {v : BitVec 64} {c o : Bool}
    (hsrc : VG.X86_64.readSrc s src = some v) (himm : ∀ n, src ≠ .imm n) (hc : s.cf = some c)
    (ho : s.of = some o) (hz : s.gpr .rbp = 0) (hxa : x ≠ .rax) (hya : y ≠ .rax)
    (hxb : x ≠ .rbp) (hyb : y ≠ .rbp) (hxy : x ≠ y) :
    WP isa (.block (maddLast x y src)) s fun s' =>
      ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
        (s'.gpr x).toNat + 2 ^ 64 * (s'.gpr y).toNat + 2 ^ 128 * (c'.toNat + o'.toNat) =
          (s.gpr x).toNat + o.toNat + 2 ^ 64 * c.toNat + (s.gpr .rdx).toNat * v.toNat ∧
        Keeps [.rax, x, y] s s' := by
  apply WP.of_runBlock
  simp only [maddLast, runBlock_cons, exec, VG.Proof.X25519.X86_64.execMulx_eq hsrc himm, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, execAdcx, VG.X86_64.readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ hxy,
    RegUpd.gpr_setReg_of_ne _ _ hxa, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hya),
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxy), RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hyb),
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxb), RegUpd.gpr_setReg_of_ne _ _ (by decide : Reg.rbp ≠ .rax),
    hz, RegUpd.gpr_setFlags, VG.Proof.X25519.X86_64.of_setReg, VG.Proof.X25519.X86_64.of_setFlags, RegUpd.cf_setReg, RegUpd.cf_setFlags, ho, hc,
    Option.some.injEq, exists_eq_left']
  refine ⟨_, _, (by trivial), (by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have e1 := adc_carry (s.gpr x) (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat)) o
    have e2 := adc_carry (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64)) 0 c
    have e3 := adc_carry (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat / 2 ^ 64) + 0 +
      (BitVec.ofBool c).setWidth 64) 0 (decide (2 ^ 64 ≤ (s.gpr x).toNat +
        (BitVec.ofNat 64 ((s.gpr .rdx).toNat * v.toNat)).toNat + o.toNat))
    have e4 := mulx_arith (s.gpr .rdx) v
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at e2 e3 ⊢
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr.2.2, RegUpd.gpr_setReg_of_ne _ _ hr.2.1,
      RegUpd.gpr_setFlags, RegUpd.gpr_setReg_of_ne _ _ hr.1]

/-- `adcx x, x`, `adox x, s`: `x` doubled (with the carry CF), `s` added
(with the carry OF), both carries out into the next word. -/
theorem dblAdd_ok (s : State) {x y : Reg} {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o)
    (hxy : x ≠ y) :
    WP isa (.block (dblAdd x y)) s fun s' =>
      ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
        (s'.gpr x).toNat + 2 ^ 64 * (c'.toNat + o'.toNat) =
          2 * (s.gpr x).toNat + (s.gpr y).toNat + c.toNat + o.toNat ∧
        Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [dblAdd, runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, execAdcx, VG.X86_64.readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxy),
    RegUpd.gpr_setFlags, VG.Proof.X25519.X86_64.of_setReg, VG.Proof.X25519.X86_64.of_setFlags, RegUpd.cf_setReg, RegUpd.cf_setFlags, ho, hc,
    Option.some.injEq, exists_eq_left']
  refine ⟨_, _, (by trivial), (by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have e1 := adc_carry (s.gpr x) (s.gpr x) c
    have e2 := adc_carry (s.gpr x + s.gpr x + (BitVec.ofBool c).setWidth 64) (s.gpr y) o
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

/-- `adcx x, rbp`, `adox x, rbp` with `rbp = 0`: both carries added into `x`. -/
theorem carries_ok (s : State) {x : Reg} {c o : Bool} (hc : s.cf = some c) (ho : s.of = some o)
    (hz : s.gpr .rbp = 0) (hxb : x ≠ .rbp) :
    WP isa (.block [.adcx x (.reg .rbp), .adox x (.reg .rbp)]) s fun s' =>
      ∃ c' o', s'.cf = some c' ∧ s'.of = some o' ∧
        (s'.gpr x).toNat + 2 ^ 64 * (c'.toNat + o'.toNat) = (s.gpr x).toNat + c.toNat + o.toNat ∧
        Keeps [x] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAdox, execAdcx, VG.X86_64.readSrc,
    Option.bind_some, Option.map_some, RegUpd.gpr_setReg_self,
    RegUpd.gpr_setReg_of_ne _ _ (Ne.symm hxb), hz, RegUpd.gpr_setFlags, VG.Proof.X25519.X86_64.of_setReg, VG.Proof.X25519.X86_64.of_setFlags,
    RegUpd.cf_setReg, RegUpd.cf_setFlags, ho, hc, Option.some.injEq, exists_eq_left']
  refine ⟨_, _, (by trivial), (by trivial), ?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · have e1 := adc_carry (s.gpr x) 0 c
    have e2 := adc_carry (s.gpr x + 0 + (BitVec.ofBool c).setWidth 64) 0 o
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at e1 e2 ⊢
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul`. -/
section

/-!
# X25519 on x86-64: multiplication with BMI2 and ADX

The rows of a product (`rowX0`, and `rowX` for any five registers), the
reduction (`reduceX`), and the multiplication `mulX o a b`, as `mul_ok` states
`mul`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem noImm_mem (m : MemOp) : ∀ n, (Src.mem m) ≠ .imm n := fun _ h => nomatch h
theorem noImm_reg (r : Reg) : ∀ n, (Src.reg r) ≠ .imm n := fun _ h => nomatch h

/-- A number times four words, word by word. -/
theorem mul_val4 (v x y z w : Nat) : v * (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) =
    v * x + 2 ^ 64 * (v * y) + 2 ^ 128 * (v * z) + 2 ^ 192 * (v * w) := by
  simp only [Nat.mul_add, Nat.mul_left_comm v]

/-- A word times four words. -/
theorem word_mul_lt (w : BitVec 64) (f : Nat) (hf : f < 2 ^ 256) :
    w.toNat * f ≤ (2 ^ 64 - 1) * (2 ^ 256 - 1) :=
  Nat.mul_le_mul (by have := w.isLt; omega) (by omega)

/-! ## Row 0 -/

theorem rowX0_eq (a b : Nat) : rowX0 a b = ([.mov .rdx (.mem (sc b))] : List Instr) ++ (([clear] : List Instr) ++
    (([.mulx .r9 .r8 (.mem (sc a))] : List Instr) ++ (mulAcc .r9 .r10 (.mem (sc (a + 8))) ++
      (mulAcc .r10 .r11 (.mem (sc (a + 16))) ++ (mulAcc .r11 .r12 (.mem (sc (a + 24))) ++
        ([.adcx .r12 (.reg .rbp)] : List Instr)))))) := rfl

/-- Row 0: `r8–r12 = b₀ · a`. -/
theorem rowX0_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat} (ha : Slot a)
    (hb : b + 8 ≤ 4096) :
    WP isa (.block (rowX0 a b)) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * (s'.gpr .r12).toNat =
        (word s.mem base b).toNat * fe s.mem base a ∧
      s'.gpr .rdx = word s.mem base b ∧ s'.gpr .rbp = 0 ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rdx, .rbp] s s' := by
  rw [VG.Proof.X25519.X86_64.rowX0_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.movRdx_ok s (readSrc_sc hs hb)) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.clear_ok s1) fun s2 ⟨z2, c2, _, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulx_ok s2 (readSrc_sc hs2 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) (by decide))
    fun s3 ⟨e3, c3, _, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulAcc_ok s3 (readSrc_sc hs3 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) (c3.trans c2)
    (by decide) (by decide) (by decide)) fun s4 ⟨c4, hc4, _, e4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulAcc_ok s4 (readSrc_sc hs4 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) hc4
    (by decide) (by decide) (by decide)) fun s5 ⟨c5, hc5, _, e5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulAcc_ok s5 (readSrc_sc hs5 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) hc5
    (by decide) (by decide) (by decide)) fun s6 ⟨c6, hc6, _, e6, k6⟩ => ?_
  have z6 : s6.gpr .rbp = 0 := by
    rw [k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), z2]
  refine WP.mono (VG.Proof.X25519.X86_64.carryC_ok s6 hc6 z6) fun s7 ⟨c7, _, _, e7, k7⟩ => ?_
  have K : Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rdx, .rbp] s s7 :=
    ((((((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide))).trans (k5.mono (by decide))).trans (k6.mono (by decide))).trans
      (k7.mono (by decide))
  -- `rdx` and the memory along the way.
  have D2 : s2.gpr .rdx = word s.mem base b := (k2.1 _ (by decide)).trans d1
  have D3 : s3.gpr .rdx = word s.mem base b := (k3.1 _ (by decide)).trans D2
  have D4 : s4.gpr .rdx = word s.mem base b := (k4.1 _ (by decide)).trans D3
  have D5 : s5.gpr .rdx = word s.mem base b := (k5.1 _ (by decide)).trans D4
  have M2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have M3 : s3.mem = s.mem := k3.2.1.trans M2
  have M4 : s4.mem = s.mem := k4.2.1.trans M3
  have M5 : s5.mem = s.mem := k5.2.1.trans M4
  refine ⟨?_, by rw [k7.1 _ (by decide), k6.1 _ (by decide), D5], by rw [k7.1 _ (by decide), z6],
    K⟩
  rw [D2, M2] at e3
  rw [D3, M3] at e4
  rw [D4, M4] at e5
  rw [D5, M5] at e6
  have b1 := VG.Proof.X25519.X86_64.word_mul_lt (word s.mem base b) _ (fe_lt s.mem base a)
  simp only [X86_64.fe, val4, VG.Proof.X25519.X86_64.mul_val4] at b1 ⊢
  rw [k7.1 .r8 (by decide), k6.1 .r8 (by decide), k5.1 .r8 (by decide), k4.1 .r8 (by decide),
    k7.1 .r9 (by decide), k6.1 .r9 (by decide), k5.1 .r9 (by decide), k7.1 .r10 (by decide),
    k6.1 .r10 (by decide), k7.1 .r11 (by decide)]
  simp only [Bool.toNat_false, Nat.add_zero] at e4
  have := Bool.toNat_le c7
  omega

/-! ## Rows 1 to 3 -/

/-- `r ∉ [...]` and `a ≠ b` from the distinctness hypotheses in context. -/
local macro "nm" : tactic =>
  `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, ne_eq] <;>
    (repeat' constructor) <;>
    first | with_reducible assumption | exact Ne.symm (by with_reducible assumption) | decide))

/-- A row `i ≥ 1`, for any five registers. -/
def rowR' (a b i : Nat) (r0 r1 r2 r3 r4 : Reg) : List Instr :=
  [.mov .rdx (.mem (sc (b + 8 * i)))] ++ ([clear] ++ (madd r0 r1 (.mem (sc a)) ++
    (madd r1 r2 (.mem (sc (a + 8))) ++ (madd r2 r3 (.mem (sc (a + 16))) ++
      maddLast r3 r4 (.mem (sc (a + 24)))))))

theorem rowX_eq (a b i : Nat) :
    rowX a b i = VG.Proof.X25519.X86_64.rowR' a b i (t i) (t (i + 1)) (t (i + 2)) (t (i + 3)) (t (i + 4)) := by
  simp only [rowX, VG.Proof.X25519.X86_64.rowR', List.append_assoc]; rfl

/-- A row: `r0–r3 + b_i · a` into `r0–r4`. -/
theorem rowR'_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat} (ha : Slot a)
    (hb : b + 8 * i + 8 ≤ 4096) {r0 r1 r2 r3 r4 : Reg}
    (hd : ([r0, r1, r2, r3, r4, .rax, .rcx, .rdx, .rbp, .rdi] : List Reg).Nodup) :
    WP isa (.block (VG.Proof.X25519.X86_64.rowR' a b i r0 r1 r2 r3 r4)) s fun s' =>
      val4 (s'.gpr r0) (s'.gpr r1) (s'.gpr r2) (s'.gpr r3) + 2 ^ 256 * (s'.gpr r4).toNat =
        val4 (s.gpr r0) (s.gpr r1) (s.gpr r2) (s.gpr r3) +
          (word s.mem base (b + 8 * i)).toNat * fe s.mem base a ∧
      Keeps [r0, r1, r2, r3, r4, .rax, .rcx, .rdx, .rbp] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h0a, h0c, h0d, h0b, h0i⟩, ⟨h12, h13, h14, h1a, h1c, h1d, h1b, h1i⟩,
    ⟨h23, h24, h2a, h2c, h2d, h2b, h2i⟩, ⟨h34, h3a, h3c, h3d, h3b, h3i⟩,
    ⟨h4a, h4c, h4d, h4b, h4i⟩, -⟩ := hd
  rw [VG.Proof.X25519.X86_64.rowR', WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.movRdx_ok s (readSrc_sc hs hb)) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.clear_ok s1) fun s2 ⟨z2, c2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.madd_ok s2 (readSrc_sc hs2 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) c2 o2
    (by nm) (by nm) (by nm) (by nm) (by nm)) fun s3 ⟨c3, o3, hc3, ho3, e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by nm)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.madd_ok s3 (readSrc_sc hs3 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) hc3 ho3
    (by nm) (by nm) (by nm) (by nm) (by nm)) fun s4 ⟨c4, o4, hc4, ho4, e4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by nm)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.madd_ok s4 (readSrc_sc hs4 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) hc4 ho4
    (by nm) (by nm) (by nm) (by nm) (by nm)) fun s5 ⟨c5, o5, hc5, ho5, e5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by nm)
  have z5 : s5.gpr .rbp = 0 := by
    rw [k5.1 _ (by nm), k4.1 _ (by nm), k3.1 _ (by nm), z2]
  refine WP.mono (VG.Proof.X25519.X86_64.maddLast_ok s5 (readSrc_sc hs5 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) hc5 ho5 z5
    (by nm) (by nm) (by nm) (by nm) (by nm)) fun s6 ⟨c6, o6, _, _, e6, k6⟩ => ?_
  have K : Keeps [r0, r1, r2, r3, r4, .rax, .rcx, .rdx, .rbp] s s6 :=
    (((((k1.mono (by simp)).trans (k2.mono (by simp))).trans (k3.mono (by simp))).trans
      (k4.mono (by simp))).trans (k5.mono (by simp))).trans (k6.mono (by simp))
  refine ⟨?_, K⟩
  -- `rdx`, the memory and the registers along the way.
  have D2 : s2.gpr .rdx = word s.mem base (b + 8 * i) := (k2.1 _ (by nm)).trans d1
  have D3 : s3.gpr .rdx = word s.mem base (b + 8 * i) := (k3.1 _ (by nm)).trans D2
  have D4 : s4.gpr .rdx = word s.mem base (b + 8 * i) := (k4.1 _ (by nm)).trans D3
  have D5 : s5.gpr .rdx = word s.mem base (b + 8 * i) := (k5.1 _ (by nm)).trans D4
  have M2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have M3 : s3.mem = s.mem := k3.2.1.trans M2
  have M4 : s4.mem = s.mem := k4.2.1.trans M3
  have M5 : s5.mem = s.mem := k5.2.1.trans M4
  rw [D2, M2, k2.1 r0 (by nm), k1.1 r0 (by nm), k2.1 r1 (by nm), k1.1 r1 (by nm)] at e3
  rw [D3, M3, k3.1 r2 (by nm), k2.1 r2 (by nm), k1.1 r2 (by nm)] at e4
  rw [D4, M4, k4.1 r3 (by nm), k3.1 r3 (by nm), k2.1 r3 (by nm), k1.1 r3 (by nm)] at e5
  rw [D5, M5] at e6
  have b1 := VG.Proof.X25519.X86_64.word_mul_lt (word s.mem base (b + 8 * i)) _ (fe_lt s.mem base a)
  have b2 : val4 (s.gpr r0) (s.gpr r1) (s.gpr r2) (s.gpr r3) < 2 ^ 256 := by
    simp only [val4]
    have := (s.gpr r0).isLt; have := (s.gpr r1).isLt; have := (s.gpr r2).isLt
    have := (s.gpr r3).isLt
    omega
  simp only [X86_64.fe, val4, VG.Proof.X25519.X86_64.mul_val4] at b1 b2 ⊢
  rw [k6.1 r0 (by nm), k5.1 r0 (by nm), k4.1 r0 (by nm), k6.1 r1 (by nm), k5.1 r1 (by nm),
    k6.1 r2 (by nm)]
  simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e3
  have := Bool.toNat_le c6; have := Bool.toNat_le o6
  omega

/-! ## The reduction -/

theorem reduceX_eq : reduceX = ([.mov32 .rdx (.imm 38)] : List Instr) ++ (([clear] : List Instr) ++ (madd .r8 .r9 (.reg .r12) ++
    (madd .r9 .r10 (.reg .r13) ++ (madd .r10 .r11 (.reg .r14) ++ (maddLast .r11 .r12 (.reg .r15) ++
      (([.mulx .rcx .rax (.reg .r12)] : List Instr) ++ carry38)))))) := rfl

open VG.Spec.X25519 (P) in
/-- `r8–r11 + 2²⁵⁶ r12–r15`, reduced into `r8–r11` (modulo `p`). -/
theorem reduceX_ok (s : State) :
    WP isa (.block reduceX) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)) % P ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [VG.Proof.X25519.X86_64.reduceX_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.movRdxImm_ok s 38) fun s1 ⟨d1, _, _, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.clear_ok s1) fun s2 ⟨z2, c2, o2, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.madd_ok s2 rfl (VG.Proof.X25519.X86_64.noImm_reg _) c2 o2 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s3 ⟨c3, o3, hc3, ho3, e3, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.madd_ok s3 rfl (VG.Proof.X25519.X86_64.noImm_reg _) hc3 ho3 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s4 ⟨c4, o4, hc4, ho4, e4, k4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.madd_ok s4 rfl (VG.Proof.X25519.X86_64.noImm_reg _) hc4 ho4 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s5 ⟨c5, o5, hc5, ho5, e5, k5⟩ => ?_
  have z5 : s5.gpr .rbp = 0 := by
    rw [k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), z2]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.maddLast_ok s5 rfl (VG.Proof.X25519.X86_64.noImm_reg _) hc5 ho5 z5 (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s6 ⟨c6, o6, _, _, e6, k6⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulx_ok s6 rfl (VG.Proof.X25519.X86_64.noImm_reg _) (by decide)) fun s7 ⟨e7, _, _, k7⟩ => ?_
  -- `rdx = 38` along the way.
  have D : ∀ x : State, x.gpr .rdx = s1.gpr .rdx → (x.gpr .rdx).toNat = 38 := fun x h => h ▸ d1
  have D2 := D s2 (k2.1 _ (by decide))
  have D3 := D s3 ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))
  have D4 := D s4 ((k4.1 _ (by decide)).trans ((k3.1 _ (by decide)).trans (k2.1 _ (by decide))))
  have D5 := D s5 ((k5.1 _ (by decide)).trans ((k4.1 _ (by decide)).trans
    ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))))
  have D6 := D s6 ((k6.1 _ (by decide)).trans ((k5.1 _ (by decide)).trans ((k4.1 _ (by decide)).trans
    ((k3.1 _ (by decide)).trans (k2.1 _ (by decide))))))
  rw [D2, k2.1 .r12 (by decide), k1.1 .r12 (by decide), k2.1 .r8 (by decide), k1.1 .r8 (by decide),
    k2.1 .r9 (by decide), k1.1 .r9 (by decide)] at e3
  rw [D3, k3.1 .r13 (by decide), k2.1 .r13 (by decide), k1.1 .r13 (by decide),
    k3.1 .r10 (by decide), k2.1 .r10 (by decide), k1.1 .r10 (by decide)] at e4
  rw [D4, k4.1 .r14 (by decide), k3.1 .r14 (by decide), k2.1 .r14 (by decide),
    k1.1 .r14 (by decide), k4.1 .r11 (by decide), k3.1 .r11 (by decide), k2.1 .r11 (by decide),
    k1.1 .r11 (by decide)] at e5
  rw [D5, k5.1 .r15 (by decide), k4.1 .r15 (by decide), k3.1 .r15 (by decide),
    k2.1 .r15 (by decide), k1.1 .r15 (by decide)] at e6
  rw [D6] at e7
  simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e3
  -- The carry word `r12` is at most 38, so `rax = 38 r12` exactly.
  have hB : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
      38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) < 39 * 2 ^ 256 := by
    simp only [val4]
    have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
    have := (s.gpr .r11).isLt; have := (s.gpr .r12).isLt; have := (s.gpr .r13).isLt
    have := (s.gpr .r14).isLt; have := (s.gpr .r15).isLt
    omega
  have hv : val4 (s6.gpr .r8) (s6.gpr .r9) (s6.gpr .r10) (s6.gpr .r11) +
      2 ^ 256 * (s6.gpr .r12).toNat =
        val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) := by
    rw [k6.1 .r8 (by decide), k5.1 .r8 (by decide), k4.1 .r8 (by decide), k6.1 .r9 (by decide),
      k5.1 .r9 (by decide), k6.1 .r10 (by decide)]
    simp only [val4] at hB ⊢
    have := (s6.gpr .r11).isLt; have := (s6.gpr .r12).isLt
    have := Bool.toNat_le c6; have := Bool.toNat_le o6
    omega
  have h12 : (s6.gpr .r12).toNat < 39 := by
    simp only [val4] at hv hB
    omega
  have hax : (s7.gpr .rax).toNat = 38 * (s6.gpr .r12).toNat := by
    have := (s7.gpr .rax).isLt
    omega
  refine WP.mono (carry38_ok s7 (by omega)) fun s8 ⟨e8, k8⟩ => ?_
  refine ⟨?_, ((((((((k1.mono (by decide)).trans (k2.mono (by decide))).trans
    (k3.mono (by decide))).trans (k4.mono (by decide))).trans (k5.mono (by decide))).trans
    (k6.mono (by decide))).trans (k7.mono (by decide))).trans (k8.mono (by decide)))⟩
  rw [e8, hax, k7.1 .r8 (by decide), k7.1 .r9 (by decide), k7.1 .r10 (by decide),
    k7.1 .r11 (by decide), ← fold256, hv, fold256]

/-! ## The multiplication -/

theorem mulX_eq (o a b : Nat) : mulX o a b = rowX0 a b ++ (VG.Proof.X25519.X86_64.rowR' a b 1 .r9 .r10 .r11 .r12 .r13 ++
    (VG.Proof.X25519.X86_64.rowR' a b 2 .r10 .r11 .r12 .r13 .r14 ++ (VG.Proof.X25519.X86_64.rowR' a b 3 .r11 .r12 .r13 .r14 .r15 ++
      (reduceX ++ store4 o)))) := by
  simp only [mulX, VG.Proof.X25519.X86_64.rowX_eq, List.append_assoc]; rfl

/-- `[o] = [a] · [b]`. -/
theorem mulX_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mulX o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b := by
  rw [VG.Proof.X25519.X86_64.mulX_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.rowX0_ok hs ha (by omega)) fun s₁ ⟨e1, _, _, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.rowR'_ok hs₁ ha (by omega) (by decide)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.rowR'_ok hs₂ ha (by omega) (by decide)) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.rowR'_ok hs₃ ha (by omega) (by decide)) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.reduceX_ok s₄) fun s₅ ⟨e5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  refine WP.mono (store4_ok hs₅ ho) fun s₆ ⟨m6, g6, rd6, wr6⟩ => ?_
  have M : s₅.mem = s.mem := k5.2.1.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1)))
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g6, k5.1 r (by simp [*]), k4.1 r (by simp [*]), k3.1 r (by simp [*]),
      k2.1 r (by simp [*]), k1.1 r (by simp [*])]
  · rw [rd6, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
  · rw [wr6, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]
  · rw [m6, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul
    rw [m6, fe_st4 _ _ (by omega), e5]
    -- Every row read the same memory.
    rw [k1.2.1] at e2
    rw [k2.2.1, k1.2.1] at e3
    rw [k3.2.1, k2.2.1, k1.2.1] at e4
    have r1 := k2.1 .r8 (by decide); have r2 := k3.1 .r8 (by decide)
    have r3 := k4.1 .r8 (by decide); have q2 := k3.1 .r9 (by decide)
    have q3 := k4.1 .r9 (by decide); have q4 := k4.1 .r10 (by decide)
    congr 1
    have hb' : fe s.mem base b = val4 (word s.mem base b) (word s.mem base (b + 8))
        (word s.mem base (b + 16)) (word s.mem base (b + 24)) := rfl
    rw [hb']
    simp only [val4] at e1 e2 e3 e4 ⊢
    rw [VG.Proof.X25519.X86_64.mul_val4 (fe s.mem base a), Nat.mul_comm (fe s.mem base a), Nat.mul_comm (fe s.mem base a),
      Nat.mul_comm (fe s.mem base a), Nat.mul_comm (fe s.mem base a)]
    simp only [Nat.mul_one, Nat.reduceMul] at e2 e3 e4
    rw [r3, r2, r1, q3, q2, q4]
    omega_using [e1, e2, e3, e4]

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr`. -/
section

/-!
# X25519 on x86-64: squaring with BMI2 and ADX

`sqrX o a` in four phases: the products `a₀ a_j`, `a₁ a_j` and `a₂ a₃` into
`r9–r14` (`sqrA`–`sqrC`), then those doubled while the squares `a_i²` are
added (`sqrD`), and reduced as in `mulX`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- `r ∉ [...]` and `a ≠ b` for literal registers. -/
local macro "nd" : tactic => `(tactic| decide)

theorem sqrA_eq (a : Nat) : sqrA a = ([.mov .rdx (.mem (sc a))] : List Instr) ++ (([clear] : List Instr) ++
    (([.mulx .r10 .r9 (.mem (sc (a + 8)))] : List Instr) ++ (mulAcc .r10 .r11 (.mem (sc (a + 16))) ++
      (mulAcc .r11 .r12 (.mem (sc (a + 24))) ++ ([.adcx .r12 (.reg .rbp)] : List Instr))))) := rfl

theorem sqrB_eq (a : Nat) : sqrB a = ([.mov .rdx (.mem (sc (a + 8)))] : List Instr) ++ (([clear] : List Instr) ++
    (madd .r11 .r12 (.mem (sc (a + 16))) ++ maddLast .r12 .r13 (.mem (sc (a + 24))))) := rfl

theorem sqrC_eq (a : Nat) : sqrC a = ([.mov .rdx (.mem (sc (a + 16)))] : List Instr) ++ (([clear] : List Instr) ++
    (mulAcc .r13 .r14 (.mem (sc (a + 24))) ++ ([.adcx .r14 (.reg .rbp)] : List Instr))) := rfl

theorem sqrD_eq (a : Nat) : sqrD a = ([clear] : List Instr) ++ (sqWord a .rax .r8 ++ (dblAdd .r9 .rax ++
    (sqWord (a + 8) .rcx .rax ++ (dblAdd .r10 .rax ++ (dblAdd .r11 .rcx ++
      (sqWord (a + 16) .rcx .rax ++ (dblAdd .r12 .rax ++ (dblAdd .r13 .rcx ++
        (sqWord (a + 24) .r15 .rax ++ (dblAdd .r14 .rax ++
          ([.adcx .r15 (.reg .rbp), .adox .r15 (.reg .rbp)] : List Instr))))))))))) := by
  simp only [sqrD, List.append_assoc]

theorem sqrX_eq (o a : Nat) :
    sqrX o a = sqrA a ++ (sqrB a ++ (sqrC a ++ (sqrD a ++ (reduceX ++ store4 o)))) := by
  simp only [sqrX, List.append_assoc]

/-- `r9–r12 = a₀ · (a₁, a₂, a₃)`. -/
theorem sqrA_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (sqrA a)) s fun s' =>
      (s'.gpr .r9).toNat + 2 ^ 64 * (s'.gpr .r10).toNat + 2 ^ 128 * (s'.gpr .r11).toNat +
          2 ^ 192 * (s'.gpr .r12).toNat =
        (word s.mem base a).toNat * (word s.mem base (a + 8)).toNat +
          2 ^ 64 * ((word s.mem base a).toNat * (word s.mem base (a + 16)).toNat) +
          2 ^ 128 * ((word s.mem base a).toNat * (word s.mem base (a + 24)).toNat) ∧
      Keeps [.r9, .r10, .r11, .r12, .rax, .rdx, .rbp] s s' := by
  rw [VG.Proof.X25519.X86_64.sqrA_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.movRdx_ok s (readSrc_sc hs (d := a) (by omega))) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.clear_ok s1) fun s2 ⟨z2, c2, _, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulx_ok s2 (readSrc_sc hs2 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) (by nd))
    fun s3 ⟨e3, c3, _, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulAcc_ok s3 (readSrc_sc hs3 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) (c3.trans c2)
    (by nd) (by nd) (by nd)) fun s4 ⟨c4, hc4, _, e4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulAcc_ok s4 (readSrc_sc hs4 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) hc4
    (by nd) (by nd) (by nd)) fun s5 ⟨c5, hc5, _, e5, k5⟩ => ?_
  have z5 : s5.gpr .rbp = 0 := by
    rw [k5.1 _ (by nd), k4.1 _ (by nd), k3.1 _ (by nd), z2]
  refine WP.mono (VG.Proof.X25519.X86_64.carryC_ok s5 hc5 z5) fun s6 ⟨c6, _, _, e6, k6⟩ => ?_
  refine ⟨?_, (((((k1.mono (by nd)).trans (k2.mono (by nd))).trans (k3.mono (by nd))).trans
    (k4.mono (by nd))).trans (k5.mono (by nd))).trans (k6.mono (by nd))⟩
  have D2 : s2.gpr .rdx = word s.mem base a := (k2.1 _ (by nd)).trans d1
  have D3 : s3.gpr .rdx = word s.mem base a := (k3.1 _ (by nd)).trans D2
  have D4 : s4.gpr .rdx = word s.mem base a := (k4.1 _ (by nd)).trans D3
  have M2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have M3 : s3.mem = s.mem := k3.2.1.trans M2
  have M4 : s4.mem = s.mem := k4.2.1.trans M3
  rw [D2, M2] at e3
  rw [D3, M3] at e4
  rw [D4, M4] at e5
  have b1 : (word s.mem base a).toNat * ((word s.mem base (a + 8)).toNat +
      2 ^ 64 * (word s.mem base (a + 16)).toNat + 2 ^ 128 * (word s.mem base (a + 24)).toNat) ≤
        (2 ^ 64 - 1) * (2 ^ 192 - 1) := by
    have := (word s.mem base a).isLt; have := (word s.mem base (a + 8)).isLt
    have := (word s.mem base (a + 16)).isLt; have := (word s.mem base (a + 24)).isLt
    exact Nat.mul_le_mul (by omega) (by omega)
  simp only [Nat.mul_add, Nat.mul_left_comm (word s.mem base a).toNat] at b1
  rw [k6.1 .r9 (by nd), k5.1 .r9 (by nd), k4.1 .r9 (by nd), k6.1 .r10 (by nd),
    k5.1 .r10 (by nd), k6.1 .r11 (by nd)]
  simp only [Bool.toNat_false, Nat.add_zero] at e4
  have := Bool.toNat_le c6
  omega

/-- `r11–r13 += a₁ · (a₂, a₃)`. -/
theorem sqrB_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (sqrB a)) s fun s' =>
      (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .r12).toNat + 2 ^ 128 * (s'.gpr .r13).toNat =
        (s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat +
          (word s.mem base (a + 8)).toNat * (word s.mem base (a + 16)).toNat +
          2 ^ 64 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 24)).toNat) ∧
      Keeps [.r11, .r12, .r13, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [VG.Proof.X25519.X86_64.sqrB_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.movRdx_ok s (readSrc_sc hs (d := a + 8) (by omega))) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.clear_ok s1) fun s2 ⟨z2, c2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.madd_ok s2 (readSrc_sc hs2 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) c2 o2 (by nd) (by nd)
    (by nd) (by nd) (by nd)) fun s3 ⟨c3, o3, hc3, ho3, e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by nd)
  have z3 : s3.gpr .rbp = 0 := by rw [k3.1 _ (by nd), z2]
  refine WP.mono (VG.Proof.X25519.X86_64.maddLast_ok s3 (readSrc_sc hs3 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) hc3 ho3 z3 (by nd)
    (by nd) (by nd) (by nd) (by nd)) fun s4 ⟨c4, o4, _, _, e4, k4⟩ => ?_
  refine ⟨?_, (((k1.mono (by nd)).trans (k2.mono (by nd))).trans (k3.mono (by nd))).trans
    (k4.mono (by nd))⟩
  have D2 : s2.gpr .rdx = word s.mem base (a + 8) := (k2.1 _ (by nd)).trans d1
  have D3 : s3.gpr .rdx = word s.mem base (a + 8) := (k3.1 _ (by nd)).trans D2
  have M2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have M3 : s3.mem = s.mem := k3.2.1.trans M2
  rw [D2, M2, k2.1 .r11 (by nd), k1.1 .r11 (by nd), k2.1 .r12 (by nd), k1.1 .r12 (by nd)] at e3
  rw [D3, M3] at e4
  simp only [Bool.toNat_false, Nat.add_zero, Nat.mul_zero] at e3
  have b1 : (word s.mem base (a + 8)).toNat * ((word s.mem base (a + 16)).toNat +
      2 ^ 64 * (word s.mem base (a + 24)).toNat) ≤ (2 ^ 64 - 1) * (2 ^ 128 - 1) := by
    have := (word s.mem base (a + 8)).isLt; have := (word s.mem base (a + 16)).isLt
    have := (word s.mem base (a + 24)).isLt
    exact Nat.mul_le_mul (by omega) (by omega)
  simp only [Nat.mul_add, Nat.mul_left_comm (word s.mem base (a + 8)).toNat] at b1
  rw [k4.1 .r11 (by nd)]
  have := (s.gpr .r11).isLt; have := (s.gpr .r12).isLt
  have := Bool.toNat_le c4; have := Bool.toNat_le o4
  omega

/-- `r13–r14 += a₂ a₃`. -/
theorem sqrC_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (sqrC a)) s fun s' =>
      (s'.gpr .r13).toNat + 2 ^ 64 * (s'.gpr .r14).toNat =
        (s.gpr .r13).toNat + (word s.mem base (a + 16)).toNat * (word s.mem base (a + 24)).toNat ∧
      Keeps [.r13, .r14, .rax, .rdx, .rbp] s s' := by
  rw [VG.Proof.X25519.X86_64.sqrC_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.movRdx_ok s (readSrc_sc hs (d := a + 16) (by omega))) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.clear_ok s1) fun s2 ⟨z2, c2, _, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulAcc_ok s2 (readSrc_sc hs2 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) c2 (by nd) (by nd)
    (by nd)) fun s3 ⟨c3, hc3, _, e3, k3⟩ => ?_
  have z3 : s3.gpr .rbp = 0 := by rw [k3.1 _ (by nd), z2]
  refine WP.mono (VG.Proof.X25519.X86_64.carryC_ok s3 hc3 z3) fun s4 ⟨c4, _, _, e4, k4⟩ => ?_
  refine ⟨?_, (((k1.mono (by nd)).trans (k2.mono (by nd))).trans (k3.mono (by nd))).trans
    (k4.mono (by nd))⟩
  have D2 : s2.gpr .rdx = word s.mem base (a + 16) := (k2.1 _ (by nd)).trans d1
  have M2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  rw [D2, M2, k2.1 .r13 (by nd), k1.1 .r13 (by nd)] at e3
  simp only [Bool.toNat_false, Nat.add_zero] at e3
  have b1 : (word s.mem base (a + 16)).toNat * (word s.mem base (a + 24)).toNat ≤
      (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
    have := (word s.mem base (a + 16)).isLt; have := (word s.mem base (a + 24)).isLt
    exact Nat.mul_le_mul (by omega) (by omega)
  rw [k4.1 .r13 (by nd)]
  have := (s.gpr .r13).isLt; have := Bool.toNat_le c4
  omega

/-- `hi:lo = [d]²`. -/
theorem sqWord_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 4096)
    {hi lo : Reg} (hhl : hi ≠ lo) :
    WP isa (.block (sqWord d hi lo)) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat =
        (word s.mem base d).toNat * (word s.mem base d).toNat ∧
      s'.cf = s.cf ∧ s'.of = s.of ∧ Keeps [.rdx, hi, lo] s s' := by
  rw [sqWord, show ([.mov .rdx (.mem (sc d)), .mulx hi lo (.reg .rdx)] : List Instr) =
    [.mov .rdx (.mem (sc d))] ++ [.mulx hi lo (.reg .rdx)] from rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.movRdx_ok s (readSrc_sc hs hd)) fun s1 ⟨d1, c1, o1, k1⟩ => ?_
  refine WP.mono (VG.Proof.X25519.X86_64.mulx_ok s1 rfl (VG.Proof.X25519.X86_64.noImm_reg _) hhl) fun s2 ⟨e2, c2, o2, k2⟩ => ?_
  refine ⟨by rw [e2, d1], c2.trans c1, o2.trans o1, (k1.mono (by simp)).trans (k2.mono (by simp))⟩

/-- `r8–r15 = 2 · r9–r14 + Σ a_i²`, with a carry out `co`. -/
theorem sqrD_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (sqrD a)) s fun s' => ∃ co : Nat,
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) +
          2 ^ 256 * val4 (s'.gpr .r12) (s'.gpr .r13) (s'.gpr .r14) (s'.gpr .r15) +
          2 ^ 256 * (2 ^ 256 * co) =
        2 * (2 ^ 64 * (s.gpr .r9).toNat + 2 ^ 128 * (s.gpr .r10).toNat +
          2 ^ 192 * (s.gpr .r11).toNat + 2 ^ 256 * (s.gpr .r12).toNat +
          2 ^ 256 * (2 ^ 64 * (s.gpr .r13).toNat) + 2 ^ 256 * (2 ^ 128 * (s.gpr .r14).toNat)) +
        (word s.mem base a).toNat * (word s.mem base a).toNat +
        2 ^ 128 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 8)).toNat) +
        2 ^ 256 * ((word s.mem base (a + 16)).toNat * (word s.mem base (a + 16)).toNat) +
        2 ^ 256 * (2 ^ 128 * ((word s.mem base (a + 24)).toNat * (word s.mem base (a + 24)).toNat)) ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [VG.Proof.X25519.X86_64.sqrD_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.clear_ok s) fun s1 ⟨z1, c1, o1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqWord_ok hs1 (d := a) (by omega) (by nd)) fun s2 ⟨e2, c2, o2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.dblAdd_ok s2 (c2.trans c1) (o2.trans o1) (by nd))
    fun s3 ⟨c3, o3, hc3, ho3, e3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqWord_ok hs3 (d := a + 8) (by omega) (by nd)) fun s4 ⟨e4, c4, o4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.dblAdd_ok s4 (c4.trans hc3) (o4.trans ho3) (by nd))
    fun s5 ⟨c5, o5, hc5, ho5, e5, k5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.dblAdd_ok s5 hc5 ho5 (by nd)) fun s6 ⟨c6, o6, hc6, ho6, e6, k6⟩ => ?_
  have hs6 := (hs4.of_keeps k5 (by nd)).of_keeps k6 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqWord_ok hs6 (d := a + 16) (by omega) (by nd)) fun s7 ⟨e7, c7, o7, k7⟩ => ?_
  have hs7 := hs6.of_keeps k7 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.dblAdd_ok s7 (c7.trans hc6) (o7.trans ho6) (by nd))
    fun s8 ⟨c8, o8, hc8, ho8, e8, k8⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.dblAdd_ok s8 hc8 ho8 (by nd)) fun s9 ⟨c9, o9, hc9, ho9, e9, k9⟩ => ?_
  have hs9 := (hs7.of_keeps k8 (by nd)).of_keeps k9 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqWord_ok hs9 (d := a + 24) (by omega) (by nd)) fun s10 ⟨e10, c10, o10, k10⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.dblAdd_ok s10 (c10.trans hc9) (o10.trans ho9) (by nd))
    fun s11 ⟨c11, o11, hc11, ho11, e11, k11⟩ => ?_
  have z11 : s11.gpr .rbp = 0 := by
    rw [k11.1 _ (by nd), k10.1 _ (by nd), k9.1 _ (by nd), k8.1 _ (by nd), k7.1 _ (by nd),
      k6.1 _ (by nd), k5.1 _ (by nd), k4.1 _ (by nd), k3.1 _ (by nd), k2.1 _ (by nd), z1]
  refine WP.mono (VG.Proof.X25519.X86_64.carries_ok s11 hc11 ho11 z11 (by nd)) fun s12 ⟨c12, o12, _, _, e12, k12⟩ => ?_
  refine ⟨c12.toNat + o12.toNat, ?_, ((((((((((((k1.mono (by nd)).trans (k2.mono (by nd))).trans
    (k3.mono (by nd))).trans (k4.mono (by nd))).trans (k5.mono (by nd))).trans
    (k6.mono (by nd))).trans (k7.mono (by nd))).trans (k8.mono (by nd))).trans
    (k9.mono (by nd))).trans (k10.mono (by nd))).trans (k11.mono (by nd))).trans
    (k12.mono (by nd)))⟩
  -- The memory the squares read, and the registers along the way.
  have M1 : s1.mem = s.mem := k1.2.1
  have M3 : s3.mem = s.mem := k3.2.1.trans (k2.2.1.trans M1)
  have M6 : s6.mem = s.mem := k6.2.1.trans (k5.2.1.trans (k4.2.1.trans M3))
  have M9 : s9.mem = s.mem := k9.2.1.trans (k8.2.1.trans (k7.2.1.trans M6))
  rw [M1] at e2
  rw [M3] at e4
  rw [M6] at e7
  rw [M9] at e10
  rw [k2.1 .r9 (by nd), k1.1 .r9 (by nd)] at e3
  rw [k4.1 .r10 (by nd), k3.1 .r10 (by nd), k2.1 .r10 (by nd), k1.1 .r10 (by nd)] at e5
  rw [k5.1 .rcx (by nd), k5.1 .r11 (by nd), k4.1 .r11 (by nd), k3.1 .r11 (by nd),
    k2.1 .r11 (by nd), k1.1 .r11 (by nd)] at e6
  rw [k7.1 .r12 (by nd), k6.1 .r12 (by nd), k5.1 .r12 (by nd), k4.1 .r12 (by nd),
    k3.1 .r12 (by nd), k2.1 .r12 (by nd), k1.1 .r12 (by nd)] at e8
  rw [k8.1 .rcx (by nd), k8.1 .r13 (by nd), k7.1 .r13 (by nd), k6.1 .r13 (by nd),
    k5.1 .r13 (by nd), k4.1 .r13 (by nd), k3.1 .r13 (by nd), k2.1 .r13 (by nd),
    k1.1 .r13 (by nd)] at e9
  rw [k10.1 .r14 (by nd), k9.1 .r14 (by nd), k8.1 .r14 (by nd), k7.1 .r14 (by nd),
    k6.1 .r14 (by nd), k5.1 .r14 (by nd), k4.1 .r14 (by nd), k3.1 .r14 (by nd),
    k2.1 .r14 (by nd), k1.1 .r14 (by nd)] at e11
  rw [k11.1 .r15 (by nd)] at e12
  simp only [Bool.toNat_false, Nat.add_zero] at e3
  simp only [val4]
  rw [k12.1 .r8 (by nd), k11.1 .r8 (by nd), k10.1 .r8 (by nd), k9.1 .r8 (by nd),
    k8.1 .r8 (by nd), k7.1 .r8 (by nd), k6.1 .r8 (by nd), k5.1 .r8 (by nd), k4.1 .r8 (by nd),
    k3.1 .r8 (by nd),
    k12.1 .r9 (by nd), k11.1 .r9 (by nd), k10.1 .r9 (by nd), k9.1 .r9 (by nd),
    k8.1 .r9 (by nd), k7.1 .r9 (by nd), k6.1 .r9 (by nd), k5.1 .r9 (by nd), k4.1 .r9 (by nd),
    k12.1 .r10 (by nd), k11.1 .r10 (by nd), k10.1 .r10 (by nd), k9.1 .r10 (by nd),
    k8.1 .r10 (by nd), k7.1 .r10 (by nd), k6.1 .r10 (by nd),
    k12.1 .r11 (by nd), k11.1 .r11 (by nd), k10.1 .r11 (by nd), k9.1 .r11 (by nd),
    k8.1 .r11 (by nd), k7.1 .r11 (by nd),
    k12.1 .r12 (by nd), k11.1 .r12 (by nd), k10.1 .r12 (by nd), k9.1 .r12 (by nd),
    k12.1 .r13 (by nd), k11.1 .r13 (by nd), k10.1 .r13 (by nd),
    k12.1 .r14 (by nd)]
  omega

/-- `[o] = [a]²`. -/
theorem sqrX_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqrX o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a := by
  rw [VG.Proof.X25519.X86_64.sqrX_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqrA_ok hs ha) fun s₁ ⟨e1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqrB_ok hs₁ ha) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqrC_ok hs₂ ha) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.sqrD_ok hs₃ ha) fun s₄ ⟨co, e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by nd)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.reduceX_ok s₄) fun s₅ ⟨e5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by nd)
  refine WP.mono (store4_ok hs₅ ho) fun s₆ ⟨m6, g6, rd6, wr6⟩ => ?_
  have M : s₅.mem = s.mem := k5.2.1.trans (k4.2.1.trans (k3.2.1.trans (k2.2.1.trans k1.2.1)))
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [g6, k5.1 r (by simp [*]), k4.1 r (by simp [*]), k3.1 r (by simp [*]),
      k2.1 r (by simp [*]), k1.1 r (by simp [*])]
  · rw [rd6, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
  · rw [wr6, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]
  · rw [m6, M]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul
    rw [m6, fe_st4 _ _ (by omega), e5]
    congr 1
    -- Every phase read the same memory.
    rw [k1.2.1] at e2
    rw [k2.2.1, k1.2.1] at e3
    rw [k3.2.1, k2.2.1, k1.2.1] at e4
    -- The products into `r9–r14` along the way.
    rw [k3.1 .r9 (by nd), k2.1 .r9 (by nd), k3.1 .r10 (by nd), k2.1 .r10 (by nd),
      k3.1 .r11 (by nd), k3.1 .r12 (by nd)] at e4
    have hb : fe s.mem base a * fe s.mem base a < 2 ^ 256 * 2 ^ 256 :=
      Nat.mul_lt_mul'' (fe_lt _ _ _) (fe_lt _ _ _)
    simp only [X86_64.fe, val4, sq_words] at hb ⊢
    simp only [val4] at e4
    omega

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Adx.A24`. -/
section

/-!
# X25519 on x86-64: multiplication by `a24` with BMI2 and ADX, and `adx_ok`

`a24X o a`: `r8–r12 = a24 · [a]` through CF (as row 0 of a product), then
`r12` folded as 38; and the field multiplications `adx` satisfy `FieldOk`.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem a24X_eq (o a : Nat) : a24X o a = ([.mov32 .rdx (.imm a24)] : List Instr) ++ (([clear] : List Instr) ++
    (([.mulx .r9 .r8 (.mem (sc a))] : List Instr) ++ (mulAcc .r9 .r10 (.mem (sc (a + 8))) ++
      (mulAcc .r10 .r11 (.mem (sc (a + 16))) ++ (mulAcc .r11 .r12 (.mem (sc (a + 24))) ++
        (([.adcx .r12 (.reg .rbp)] : List Instr) ++ (([.mov32 .rdx (.imm 38)] : List Instr) ++
          (([.mulx .rcx .rax (.reg .r12)] : List Instr) ++ (carry38 ++ store4 o))))))))) := by
  simp only [a24X, List.append_assoc]; rfl

/-- `[o] = a24 · [a]`. -/
theorem a24X_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (a24X o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = Spec.X25519.a24 * F s.mem base a := by
  rw [VG.Proof.X25519.X86_64.a24X_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.movRdxImm_ok s a24) fun s1 ⟨d1, _, _, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.clear_ok s1) fun s2 ⟨z2, c2, _, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulx_ok s2 (readSrc_sc hs2 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) (by decide))
    fun s3 ⟨e3, c3, _, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulAcc_ok s3 (readSrc_sc hs3 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) (c3.trans c2)
    (by decide) (by decide) (by decide)) fun s4 ⟨c4, hc4, _, e4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulAcc_ok s4 (readSrc_sc hs4 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) hc4
    (by decide) (by decide) (by decide)) fun s5 ⟨c5, hc5, _, e5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulAcc_ok s5 (readSrc_sc hs5 (by omega)) (VG.Proof.X25519.X86_64.noImm_mem _) hc5
    (by decide) (by decide) (by decide)) fun s6 ⟨c6, hc6, _, e6, k6⟩ => ?_
  have z6 : s6.gpr .rbp = 0 := by
    rw [k6.1 _ (by decide), k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), z2]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.carryC_ok s6 hc6 z6) fun s7 ⟨c7, _, _, e7, k7⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.movRdxImm_ok s7 38) fun s8 ⟨d8, _, _, k8⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.X25519.X86_64.mulx_ok s8 rfl (VG.Proof.X25519.X86_64.noImm_reg _) (by decide)) fun s9 ⟨e9, _, _, k9⟩ => ?_
  -- `rdx = a24` for the products, and the memory they read.
  have D : ∀ x : State, x.gpr .rdx = s1.gpr .rdx → (x.gpr .rdx).toNat = 121665 :=
    fun x h => h ▸ d1
  have D2 := D s2 (k2.1 _ (by decide))
  have D3 := D s3 ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))
  have D4 := D s4 ((k4.1 _ (by decide)).trans ((k3.1 _ (by decide)).trans (k2.1 _ (by decide))))
  have D5 := D s5 ((k5.1 _ (by decide)).trans ((k4.1 _ (by decide)).trans
    ((k3.1 _ (by decide)).trans (k2.1 _ (by decide)))))
  have M2 : s2.mem = s.mem := k2.2.1.trans k1.2.1
  have M3 : s3.mem = s.mem := k3.2.1.trans M2
  have M4 : s4.mem = s.mem := k4.2.1.trans M3
  have M5 : s5.mem = s.mem := k5.2.1.trans M4
  rw [D2, M2] at e3
  rw [D3, M3] at e4
  rw [D4, M4] at e5
  rw [D5, M5] at e6
  rw [show (s8.gpr .rdx).toNat = 38 from d8] at e9
  simp only [Bool.toNat_false, Nat.add_zero] at e4
  -- `r8–r11 + 2²⁵⁶ r12 = a24 · [a]`, so `r12 < a24` and `rax = 38 r12`.
  have hv : val4 (s7.gpr .r8) (s7.gpr .r9) (s7.gpr .r10) (s7.gpr .r11) +
      2 ^ 256 * (s7.gpr .r12).toNat = 121665 * fe s.mem base a := by
    have hA := fe_lt s.mem base a
    simp only [X86_64.fe, val4] at hA ⊢
    rw [k7.1 .r8 (by decide), k6.1 .r8 (by decide), k5.1 .r8 (by decide), k4.1 .r8 (by decide),
      k7.1 .r9 (by decide), k6.1 .r9 (by decide), k5.1 .r9 (by decide), k7.1 .r10 (by decide),
      k6.1 .r10 (by decide), k7.1 .r11 (by decide)]
    have := Bool.toNat_le c7
    omega
  have h12 : (s7.gpr .r12).toNat < 121665 := by
    have hA := fe_lt s.mem base a
    simp only [val4] at hv
    omega
  rw [k8.1 .r12 (by decide)] at e9
  have hax : (s9.gpr .rax).toNat = 38 * (s7.gpr .r12).toNat := by
    have := (s9.gpr .rax).isLt
    omega
  have hs9 := ((((hs5.of_keeps k6 (by decide)).of_keeps k7 (by decide)).of_keeps k8
    (by decide)).of_keeps k9 (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (carry38_ok s9 (by omega)) fun s10 ⟨e10, k10⟩ => ?_
  have hs10 := hs9.of_keeps k10 (by decide)
  refine WP.mono (store4_ok hs10 ho) fun s11 ⟨m11, g11, rd11, wr11⟩ => ?_
  have K : Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s10 :=
    (((((((((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
      (k4.mono (by decide))).trans (k5.mono (by decide))).trans (k6.mono (by decide))).trans
      (k7.mono (by decide))).trans (k8.mono (by decide))).trans (k9.mono (by decide))).trans
      (k10.mono (by decide))
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g11, K.1 r (by simp [hr])]
  · rw [rd11, K.2.2.1]
  · rw [wr11, K.2.2.2]
  · rw [m11, K.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_a24
    rw [m11, fe_st4 _ _ (by omega), e10, hax, k9.1 .r8 (by decide), k9.1 .r9 (by decide),
      k9.1 .r10 (by decide), k9.1 .r11 (by decide), k8.1 .r8 (by decide), k8.1 .r9 (by decide),
      k8.1 .r10 (by decide), k8.1 .r11 (by decide), ← fold256, hv]

/-- The field multiplications with BMI2 and ADX. -/
theorem adx_ok : FieldOk adx where
  mul hs _ _ _ ho ha hb := VG.Proof.X25519.X86_64.mulX_ok hs ho ha hb
  sqr hs _ _ ho ha := VG.Proof.X25519.X86_64.sqrX_ok hs ho ha
  a24 hs _ _ ho ha := VG.Proof.X25519.X86_64.a24X_ok hs ho ha

end VG.Proof.X25519.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.X86_64.Adx.Verified`. -/
section

/-!
# X25519 on x86-64 with BMI2 and ADX: `Verified`

The proof of `vg_x25519` (`Proof/X25519/X86_64/Verified.lean`) for the field
multiplications `adx` (`adx_ok`): correctness from `correct`, constant time by
taint tracking (the only branches are on the loop counters, and every address
is an argument plus a constant or a counter), satisfiability, and the shared
contract.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64

theorem x25519Adx_ok (s : State) (hs : Proof.X25519.x25519X86_64.pre s) :
    ∃ t s', Exec isa Impl.X25519.X86_64.x25519Adx s t s' ∧ abiPreserved s s' ∧
      Proof.X25519.x25519X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct VG.Proof.X25519.X86_64.adx_ok (Pre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem x25519Adx_ct : ConstantTime isa Proof.X25519.x25519X86_64.pre
    Proof.X25519.x25519X86_64.pub Impl.X25519.X86_64.x25519Adx := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨_, h1, h2, h3, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem x25519Adx_verified :
    Verified X86_64.target Impl.X25519.X86_64.x25519Adx (Spec.X25519.x25519Contract X86_64.abi) :=
  Verified.of_correct VG.Proof.X25519.X86_64.x25519Adx_ok VG.Proof.X25519.X86_64.x25519Adx_ct (by
    sig_implies [Spec.X25519.x25519Contract, Spec.X25519.x25519Sig, X86_64.abi, X86_64.argRegs,
      Proof.X25519.x25519X86_64] [satState] using satState)

end VG.Proof.X25519.X86_64

end
