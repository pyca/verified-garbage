module

public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Impl.Weierstrass.PPC64LE
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.PPC64LE.Loop
public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.Call
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontFn
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Covers

/-! ### `Weierstrass.PPC64LE.MontCall`, which this module and modules that import it used -/

section

/-!
# Calls of the Montgomery arithmetic's functions, on PPC64LE

`callOp f body o a b` (`Impl/Weierstrass/PPC64LE/Call.lean`) calls the
function `f`, whose code is `body`, on the working space in `r3` and the
offsets `o`, `a` and `b` (`callOp_ok`): from a state whose writable regions
include the `8192` bytes of the working space (`WsReg`), it changes only the
registers `fnClob` (and the link register), the number at `o` and the
functions' own working space (`CallKeep`), and does what `body` does.
`mulCall_ok`, `addCall_ok` and `subCall_ok` are the calls of `mulFn`,
`addFn` and `subFn` (`MontFn.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Mont VG.Proof.Mont.PPC64LE

/-- The working space: its base in `r3`, its `8192` bytes writable, not
wrapping around. -/
structure WsReg (s : State) (base : Addr) : Prop where
  r3 : s.gpr .r3 = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 8192 ≤ 2 ^ 64

/-- What a call writing `[o]` keeps: the registers but `fnClob`, the
regions, the stack pointer, and the memory but `[o]` and the functions' own
working space. -/
structure CallKeep (n : Nat) (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ fnClob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : Kept n base o s.mem s'.mem

theorem WsReg.of_keep {s s' : State} {base : Addr} (h : WsReg s base) (hg : s'.gpr .r3 = s.gpr .r3)
    (hw : s'.wr = s.wr) : WsReg s' base :=
  ⟨hg.trans h.r3, hw ▸ h.wr, h.nowrap⟩

/-- A number apart from every range that changed. -/
theorem outs_wordsVal {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d k : Nat} (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    wordsVal m' base d k = wordsVal m base d k := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact h.val32 (fun r hr => by have := hd r hr; omega_using [this]) (by omega_using [hd'])

theorem lo_li {x : Nat} (hx : x < 2 ^ 32) : ((BitVec.ofNat 64 x).setWidth 32).toNat = x := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hx]

/-- A call of `body`, which from the working space in `r3` and the offsets
`o`, `a` and `b` in `r4`–`r6` changes only `[o]`, its own working space and
`fnClob`, and relates the memory before and after by `V`. -/
theorem callOp_ok {f : String} {body : Prog isa} (hn : body.noFrames = true) {n : Nat} {s : State}
    {base : Addr} (hw : WsReg s base) {o a b : Nat} (ho : o < 2 ^ 15) (ha : a < 2 ^ 15) (hb : b < 2 ^ 15)
    {V : Mem → Mem → Prop}
    (hbody : ∀ t, t.rd = [] → t.wr = [⟨base, 8192⟩] → t.gpr .r3 = base → lo t .r4 = o → lo t .r5 = a →
      lo t .r6 = b → t.mem = s.mem →
      ∃ tr t', Exec isa body t tr t' ∧ abiPreserved t t' ∧ (∀ r, r ∉ fnClob → t'.gpr r = t.gpr r) ∧
        Kept n base o t.mem t'.mem ∧ V t.mem t'.mem) :
    WP isa (callOp f body o a b) s fun s' => CallKeep n base o s s' ∧ V s.mem s'.mem := by
  rw [callOp]
  refine WP.seq (wp_step (exec_li ho) (wp_step (exec_li ha) (wp_step (exec_li hb) (WP.block_nil ?_))))
  generalize hs₃ : ((s.write .r4 (BitVec.ofNat 64 o)).write .r5 (BitVec.ofNat 64 a)).write .r6
    (BitVec.ofNat 64 b) = s₃
  have K₃ : Kp fnClob s s₃ := by
    rw [← hs₃]; exact ((Kp.write s _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))
  have g4 : lo s₃ .r4 = o := by rw [← hs₃]; simp only [lo, write_gpr, reduceCtorEq, ite_false, ite_true]; exact lo_li (by omega_using [ho])
  have g5 : lo s₃ .r5 = a := by rw [← hs₃]; simp only [lo, write_gpr, reduceCtorEq, ite_false, ite_true]; exact lo_li (by omega_using [ha])
  have g6 : lo s₃ .r6 = b := by rw [← hs₃]; simp only [lo, write_gpr, reduceCtorEq, ite_false, ite_true]; exact lo_li (by omega_using [hb])
  have g3 : s₃.gpr .r3 = base := by rw [K₃.g]; exact hw.r3
  have hcov : Covers [⟨base, 8192⟩] s₃.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [K₃.wr]; exact hw.wr
  refine WP.call (k := ⟨fun t => t.rd = [] ∧ t.wr = [⟨base, 8192⟩] ∧ t.gpr .r3 = base ∧ lo t .r4 = o ∧
      lo t .r5 = a ∧ lo t .r6 = b ∧ t.mem = s.mem,
      fun t t' => (∀ r, r ∉ fnClob → t'.gpr r = t.gpr r) ∧ Kept n base o t.mem t'.mem ∧ V t.mem t'.mem,
      fun _ _ => True⟩)
    (fun t ⟨h1, h2, h3, h4, h5, h6, h7⟩ => by
      obtain ⟨tr, t', he, A, G, K, W⟩ := hbody t h1 h2 h3 h4 h5 h6 h7
      exact ⟨tr, t', he, A, G, K, W⟩)
    (rd := []) (wr := [⟨base, 8192⟩])
    ⟨rfl, rfl, by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g3],
      by simp only [lo, State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide)]; exact g4,
      by simp only [lo, State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide)]; exact g5,
      by simp only [lo, State.withRegions_gpr]; rw [State.callEntry_gpr _ (by decide)]; exact g6,
      by rw [State.withRegions_mem, State.callEntry_mem, ← hs₃]; rfl⟩
    (Covers.right hcov) hcov ?_ hn
  intro s' r' w' p' _ _ _ ⟨G, K, W⟩
  simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr] at G K W
  have m₃ : s₃.mem = s.mem := by rw [← hs₃]; rfl
  rw [m₃] at K W
  refine ⟨⟨fun r hr => ?_, by rw [r', K₃.rd], by rw [w', K₃.wr], by rw [p', K₃.sp], K⟩, W⟩
  have hl : r ∉ linkRegs := not_mem_sub hr
  rw [G r hr, State.callEntry_gpr _ hl, K₃.gpr r hr]

theorem own_lt (n : Nat) : own n < 2 ^ 15 := by
  simp only [own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]; omega_using []

/-- The arguments of a call, as the functions' precondition has them. -/
theorem pre_of_call {n : Nat} {base : Addr} (hn : base.toNat + 8192 ≤ 2 ^ 64) {o a b : Nat}
    (ho : o + 8 * n ≤ own n) (ha : a + 8 * n ≤ own n) (hb : b + 8 * n ≤ own n) {t : State}
    (h2 : t.wr = [⟨base, 8192⟩]) (h3 : t.gpr .r3 = base) (h4 : lo t .r4 = o) (h5 : lo t .r5 = a)
    (h6 : lo t .r6 = b) : Pre n t :=
  ⟨by rw [h2, h3], by rw [h3]; exact hn, by rw [h4]; exact ho, by rw [h5]; exact ha, by rw [h6]; exact hb⟩

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`.
It keeps every register but `fnClob`, but the constant-time analysis takes
`r15`–`r24` as secret after it (`Impl/Weierstrass/PPC64LE/Call.lean`):
keep public values in `r14` or `r25`–`r31`. -/
theorem mulCall_ok {S : Impl.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) {s : State} {base : Addr}
    (hw : WsReg s base) {o a b : Nat} (ho : o + 8 * S.k ≤ own S.k)
    (ha : a + 8 * S.k ≤ own S.k) (hb : b + 8 * S.k ≤ own S.k) (hB : wordsVal s.mem base b S.k < S.m) :
    WP isa (mulCall S o a b) s fun s' => CallKeep S.k base o s s' ∧
      wordsVal s'.mem base o S.k < S.m ∧
      wordsVal s'.mem base o S.k * 2 ^ (64 * S.k) % S.m =
        wordsVal s.mem base a S.k * wordsVal s.mem base b S.k % S.m := by
  have := own_lt S.k
  exact callOp_ok (V := fun m m' => wordsVal m' base o S.k < S.m ∧
      wordsVal m' base o S.k * 2 ^ (64 * S.k) % S.m = wordsVal m base a S.k * wordsVal m base b S.k % S.m)
    (mulFn_noFrames _ _) hw (by omega_using [ho, this]) (by omega_using [ha, this]) (by omega_using [hb, this]) fun t _ h2 h3 h4 h5 h6 h7 => by
      obtain ⟨tr, t', he, A, G, V, C, K⟩ := mulFn_ok hM (pre_of_call hw.nowrap ho ha hb h2 h3 h4 h5 h6)
        (by rw [h3, h6, h7]; exact hB)
      rw [h3, h4, h5, h6] at *
      exact ⟨tr, t', he, A, G, K, V, C⟩

/-- `[o] = [a] + [b] mod m` by a call of `vg_<curve>_add_mod_<p|n>`. -/
theorem addCall_ok {S : Impl.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) {s : State} {base : Addr}
    (hw : WsReg s base) {o a b : Nat} (ho : o + 8 * S.k ≤ own S.k)
    (ha : a + 8 * S.k ≤ own S.k) (hb : b + 8 * S.k ≤ own S.k)
    (hAB : wordsVal s.mem base a S.k + wordsVal s.mem base b S.k < 2 * S.m) :
    WP isa (addCall S o a b) s fun s' => CallKeep S.k base o s s' ∧
      wordsVal s'.mem base o S.k = (wordsVal s.mem base a S.k + wordsVal s.mem base b S.k) % S.m := by
  have := own_lt S.k
  exact callOp_ok (V := fun m m' => wordsVal m' base o S.k = (wordsVal m base a S.k + wordsVal m base b S.k) % S.m)
    rfl hw (by omega_using [ho, this]) (by omega_using [ha, this]) (by omega_using [hb, this]) fun t _ h2 h3 h4 h5 h6 h7 => by
      obtain ⟨tr, t', he, A, G, V, K⟩ := addFn_ok hM (pre_of_call hw.nowrap ho ha hb h2 h3 h4 h5 h6)
        (by rw [h3, h5, h6, h7]; exact hAB)
      rw [h3, h4, h5, h6] at *
      exact ⟨tr, t', he, A, G, K, V⟩

/-- `[o] = [a] - [b] mod m` by a call of `vg_<curve>_sub_mod_<p|n>`. -/
theorem subCall_ok {S : Impl.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) {s : State} {base : Addr}
    (hw : WsReg s base) {o a b : Nat} (ho : o + 8 * S.k ≤ own S.k)
    (ha : a + 8 * S.k ≤ own S.k) (hb : b + 8 * S.k ≤ own S.k)
    (hA : wordsVal s.mem base a S.k < S.m) (hB : wordsVal s.mem base b S.k < S.m) :
    WP isa (subCall S o a b) s fun s' => CallKeep S.k base o s s' ∧
      wordsVal s'.mem base o S.k = (wordsVal s.mem base a S.k + S.m - wordsVal s.mem base b S.k) % S.m := by
  have := own_lt S.k
  exact callOp_ok (V := fun m m' => wordsVal m' base o S.k = (wordsVal m base a S.k + S.m - wordsVal m base b S.k) % S.m)
    rfl hw (by omega_using [ho, this]) (by omega_using [ha, this]) (by omega_using [hb, this]) fun t _ h2 h3 h4 h5 h6 h7 => by
      obtain ⟨tr, t', he, A, G, V, K⟩ := subFn_ok hM (pre_of_call hw.nowrap ho ha hb h2 h3 h4 h5 h6)
        (by rw [h3, h5, h7]; exact hA) (by rw [h3, h6, h7]; exact hB)
      rw [h3, h4, h5, h6] at *
      exact ⟨tr, t', he, A, G, K, V⟩

end VG.Proof.Weierstrass.PPC64LE.Mont

end

end

/-! ### `Weierstrass.PPC64LE.Keep`, which this module and modules that import it used -/

section

/-!
# What the curves' code keeps, on PPC64LE

Code that calls the Montgomery functions changes the link register, which
the functions built on it save; what the code keeps is the registers but
some, the regions and the stack pointer (`Rk`), whether it is a block
(`Kp.rk`) or a call (`Mont.CallKeep.rk`). The working space, its base in
`r3` (`Mont.WsReg`), gives the blocks' working space (`WsReg.ws`) and `r3`
at its base (`WsReg.at3`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass.PPC64LE.Mont

/-- `s'` agrees with `s` but on the registers `rs`, the link register and
memory. -/
structure Rk (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Rk.refl (rs : List Reg) (s : State) : Rk rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Rk.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Rk rs s₁ s₂) (h₂ : Rk rs s₂ s₃) : Rk rs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem Rk.mono {rs rs' : List Reg} {s s' : State} (h : Rk rs s s') (hs : ∀ r ∈ rs, r ∈ rs' := by decide) :
    Rk rs' s s' := ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

theorem Rk.g {rs : List Reg} {s s' : State} (h : Rk rs s s') {r : Reg} (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

theorem _root_.VG.Proof.Mont.PPC64LE.Kp.rk {rs rs' : List Reg} {s s' : State} (h : Kp rs s s') (hs : ∀ r ∈ rs, r ∈ rs' := by decide) :
    Rk rs' s s' := ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

theorem _root_.VG.Proof.Weierstrass.PPC64LE.Mont.CallKeep.rk {n : Nat} {base : Addr} {o : Nat} {s s' : State}
    (h : CallKeep n base o s s') {rs : List Reg} (hs : ∀ r ∈ fnClob, r ∈ rs := by decide) : Rk rs s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

theorem _root_.VG.Proof.Weierstrass.PPC64LE.Mont.WsReg.ws {s : State} {base : Addr} (h : WsReg s base) :
    Ws s base 8192 :=
  ⟨⟨8192, Nat.le_refl _, h.wr, h.nowrap⟩, by decide⟩

theorem _root_.VG.Proof.Weierstrass.PPC64LE.Mont.WsReg.at3 {s : State} {base : Addr} (h : WsReg s base) :
    At s base .r3 0 := by
  rw [At, h.r3, off]; exact (BitVec.add_zero _).symm

theorem _root_.VG.Proof.Weierstrass.PPC64LE.Mont.WsReg.of_rk {s s' : State} {base : Addr} (h : WsReg s base)
    {rs : List Reg} (k : Rk rs s s') (hr : Reg.r3 ∉ rs := by decide) : WsReg s' base :=
  h.of_keep (k.gpr _ hr) k.wr

theorem _root_.VG.Proof.Weierstrass.PPC64LE.Mont.WsReg.of_kp {s s' : State} {base : Addr} (h : WsReg s base)
    {rs : List Reg} (k : Kp rs s s') (hr : Reg.r3 ∉ rs := by decide) : WsReg s' base :=
  h.of_keep (k.gpr _ hr) k.wr

end VG.Proof.Weierstrass.PPC64LE

end

end

/-! ### `Weierstrass.PPC64LE.Bits`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.PPC64LE.Loop`, which this module and modules that import it used -/

section

/-!
# Short Weierstrass curves on PPC64LE: loops counted down in `r31`

The ladder, the powers and the tables of bits loop with `r31` counting down:
the body starts with `subi r31, r31, 1` (`wp_decCounter`), and the loop runs
while `r31 ≠ 0` (`more`). `countLoop_ok` runs such a loop `n ≥ 1` times from
an invariant indexed by `r31`, as on 32-bit ARM
(`Proof/Weierstrass/Arm/Loop.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE

/-- A loop whose body takes the invariant from `j` to `j - 1`, with `r31 = j`
in the invariant, run from `n ≥ 1` (below `2⁶⁴`). -/
theorem countLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n : Nat}
    (hr : ∀ j s, Inv j s → s.gpr .r31 = BitVec.ofNat 64 j)
    (hstep : ∀ j s, 1 ≤ j → j ≤ n → Inv j s → WP isa body s fun s' => Inv (j - 1) s')
    (hQ : ∀ s, Inv 0 s → Q s) (hn : 1 ≤ n) (hn64 : n < 2 ^ 64) {s : State} (hs : Inv n s) :
    WP isa (.loop body more) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ n ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) n s
    ⟨hn, Nat.le_refl _, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' hi' => ?_
  have he := eval_nonzero_ofNat (hr _ _ hi') (x := j - 1) (by omega_using [hn64, h2])
  by_cases hj : j - 1 = 0
  · exact .inl ⟨by rw [he]; simp [hj], hQ s' (by rw [hj] at hi'; exact hi')⟩
  · exact .inr ⟨by rw [he]; simp [hj], j - 1, by omega_using [h1], by omega_using [hj], by omega_using [h2], hi'⟩

theorem ofNat_pred64 {j : Nat} (hj : 1 ≤ j) : BitVec.ofNat 64 j - BitVec.ofNat 64 1 = BitVec.ofNat 64 (j - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [hj]

/-- `r31 -= 1`. -/
theorem wp_decCounter {is : List Instr} {s : State} {Q : State → Prop} {j : Nat} (hj : 1 ≤ j)
    (hb : s.gpr .r31 = BitVec.ofNat 64 j)
    (k : WP isa (.block is) (s.write .r31 (BitVec.ofNat 64 (j - 1))) Q) :
    WP isa (.block (decCounter :: is)) s Q := by
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  rw [hb, ofNat_pred64 hj]; exact k

end VG.Proof.Weierstrass.PPC64LE

end

end

/-!
# Short Weierstrass curves on PPC64LE: tables of bits, and masks of bits

`bits src dst (8 n)` writes the bits of the `n`-word number at `src`, one byte
each, to the table at `dst` (`bits_ok`): a loop over its bytes, from the top
one down, each giving eight bytes of the table (`bitsBody_ok`). `bitMask d`
makes the mask `r10` of the byte `r31` of the table at `d` (`bitMask_ok`):
all ones for a 1, zero for a 0 (`bitMask_bool_ok`). As on 32-bit ARM
(`Proof/Weierstrass/Arm/Bits.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE

/-! ## Bytes through a register -/

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega_arith, dite_true]

/-- `lbz t, d(r)` with `r` at `K` bytes into the working space. -/
theorem lbz_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t r : Reg} {K d : Nat}
    (hr : At s base r K) (hr0 : r ≠ .r0) (hd : K + d + 1 ≤ size) :
    exec (.lbz t r d) s = some (s.write t ((s.mem (off base (K + d))).setWidth 64)) := by
  have hs15 := hs.small
  rw [exec_lbz hr0 (by omega_arith) (by rw [hr, off_add]; exact hs.read hd), hr, off_add, read_one]

/-- `stb t, d(r)` with `r` at `K` bytes into the working space. -/
theorem stb_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {t r : Reg} {K d : Nat}
    (hr : At s base r K) (hr0 : r ≠ .r0) (hd : K + d + 1 ≤ size) :
    exec (.stb t r d) s =
      some { s with mem := s.mem.writeW (off base (K + d)) ((s.gpr t).setWidth 8 : BitVec 8) } := by
  have hs15 := hs.small
  rw [exec_stb hr0 (by omega_arith) (by rw [hr, off_add]; exact hs.wrIn hd), hr, off_add]
  rfl

/-- `d = r3 + r` for `r = k`, with `r3` the working space's base. -/
theorem add_at {s : State} {base : Addr} {r : Reg} {k : Nat} (h3 : At s base .r3 0)
    (hr : s.gpr r = BitVec.ofNat 64 k) : s.gpr .r3 + s.gpr r = off base k := by
  rw [h3, hr, off_add, Nat.zero_add]

/-! ## Masks -/

/-- `r10 = -[r3 + r31 + d]`, the byte zero-extended. -/
theorem bitMask_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {d t : Nat} (ht : s.gpr .r31 = BitVec.ofNat 64 t) (hd : t + d + 1 ≤ size) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .r10 = 0 - (s.mem (off base (d + t))).setWidth 64 ∧ Kp [.r4, .r5, .r10] s s' ∧
        s'.mem = s.mem := by
  simp only [bitMask]
  refine wp_step exec_add ?_
  have a₁ : At (s.write .r4 (s.gpr .r3 + s.gpr .r31)) base .r4 t := by
    show s.gpr .r3 + s.gpr .r31 = _
    exact add_at h3 ht
  refine wp_step (lbz_ok (hs.write _ _) a₁ (by decide) hd) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub (WP.block_nil ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩)
  · simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
    rw [Nat.add_comm d t]; rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false]

theorem neg_bit (c : Bool) :
    0 - ((if c then 1 else 0 : BitVec 8)).setWidth 64 = (if c then BitVec.allOnes 64 else 0) := by
  cases c <;> decide

/-- The mask of a byte that is 0 or 1. -/
theorem bitMask_bool_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {d t : Nat} (ht : s.gpr .r31 = BitVec.ofNat 64 t) (hd : t + d + 1 ≤ size) {c : Bool}
    (hc : s.mem (off base (d + t)) = if c then 1 else 0) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .r10 = (if c then BitVec.allOnes 64 else 0) ∧ Kp [.r4, .r5, .r10] s s' ∧ s'.mem = s.mem :=
  WP.mono (bitMask_ok hs h3 ht hd) fun _ ⟨e, k, m⟩ => ⟨by rw [e, hc, neg_bit], k, m⟩

/-! ## The table of bits -/

/-- The body of `bits`' loop. -/
def bitsBody (src dst : Nat) : List Instr :=
  [decCounter, .add .r4 wb .r31, .lbz .r4 .r4 src, .lsl .r5 .r31 3, .add .r5 wb .r5, .li .r7 1] ++
    (List.range 8).flatMap (bitJ dst)

theorem bits_eq (src dst nbytes : Nat) :
    bits src dst nbytes = .seq (.block [.li .r31 nbytes]) (.loop (.block (bitsBody src dst)) more) :=
  rfl

theorem bit_byte (b : BitVec 8) (j : Nat) :
    ((((b.setWidth 64 >>> j) &&& BitVec.ofNat 64 1).setWidth 8) : BitVec 8) = if b.getLsbD j then 1 else 0 :=
  bitByte_getLsbD 64 (by decide) b j

theorem bit_byte0 (b : BitVec 8) :
    (((b.setWidth 64 &&& BitVec.ofNat 64 1).setWidth 8) : BitVec 8) = if b.getLsbD 0 then 1 else 0 := by
  rw [← BitVec.ushiftRight_zero (b.setWidth 64)]; exact bit_byte b 0

/-- What `bitJ` keeps. -/
abbrev bitClob : List Reg := [.r6]

/-- Byte `j` of the eight at `r5 + dst`: bit `j` of the byte in `r4`. -/
theorem bitJ_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {i : Nat}
    {dst : Nat} (hb : At s base .r5 (8 * i)) {b : BitVec 8}
    (ha : s.gpr .r4 = b.setWidth 64) (h7 : s.gpr .r7 = BitVec.ofNat 64 1) {j : Nat} (hj : j < 8)
    (hd : dst + (8 * i + j) + 1 ≤ size) :
    WP isa (.block (bitJ dst j)) s fun s' => Kp bitClob s s' ∧
      s'.mem = s.mem.writeW (off base (dst + (8 * i + j))) (if b.getLsbD j then 1 else 0 : BitVec 8) := by
  have e : 8 * i + (dst + j) = dst + (8 * i + j) := by omega_arith
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [bitJ, ite_true, List.cons_append, List.nil_append]
    refine wp_step exec_logic ?_
    refine wp_step (stb_ok (hs.write _ _) (hb.write _) (by decide) (by omega_arith)) (WP.block_nil ?_)
    simp only [write_gpr, ite_true]
    refine ⟨(Kp.write s _ (by decide)).trans (Kp.store _ _ _), ?_⟩
    simp only [write_mem]
    rw [e, ha, h7, bit_byte0]
  · simp only [bitJ, show ¬j = 0 by omega_arith, ite_false, List.cons_append, List.nil_append]
    refine wp_step (exec_lsr_d (by omega_arith)) ?_
    refine wp_step exec_logic ?_
    refine wp_step (stb_ok ((hs.write _ _).write _ _) ((hb.write _).write _) (by decide) (by omega_arith))
      (WP.block_nil ?_)
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    refine ⟨((Kp.write s _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.store _ _ _), ?_⟩
    simp only [write_mem]
    rw [e, ha, h7, bit_byte]

/-- The first `k` bits of the byte in `r4`. -/
theorem bitJs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    {i dst : Nat} (hb : At s base .r5 (8 * i)) {b : BitVec 8}
    (ha : s.gpr .r4 = b.setWidth 64) (h7 : s.gpr .r7 = BitVec.ofNat 64 1) (hd : dst + 8 * i + 8 ≤ size) :
    ∀ k ≤ 8,
    WP isa (.block ((List.range k).flatMap (bitJ dst))) s fun s' => Kp bitClob s s' ∧
      (∀ j < k, s'.mem (off base (dst + (8 * i + j))) = if b.getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) k s.mem s'.mem
  | 0, _ => WP.block_nil ⟨Kp.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine wp_append (WP.mono (bitJs_ok hs hb ha h7 hd k (by omega_arith)) fun s₁ ⟨k₁, e₁, O₁⟩ => ?_)
    refine WP.mono (bitJ_ok (k₁.ws hs) (k₁.at hb) (b := b) (by rw [k₁.g]; exact ha) (by rw [k₁.g]; exact h7)
      (j := k) (by omega_arith) (by omega_arith)) fun s₂ ⟨k₂, m₂⟩ => ?_
    have O₂ : Outside base (dst + (8 * i + k)) 1 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW8_outside _ _ _ (by omega_arith)
    refine ⟨k₁.trans k₂, fun j hj => ?_,
      (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂ _ (by rw [ofs_off0 base (d := dst + (8 * i + j)) (by omega_arith)]; omega_arith), e₁ j h]
    · obtain rfl : j = k := by omega_arith
      rw [m₂, writeW8_self]

theorem shl3 (i : Nat) : BitVec.ofNat 64 i <<< 3 = BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]
  congr 1; omega_arith

/-- What the loop of `bits` changes. -/
abbrev bitsClob : List Reg := [.r4, .r5, .r6, .r7, .r31]

/-- One byte of the number at `src`, the one below `r31 = i + 1`: its bits to
the table at `dst`. -/
theorem bitsBody_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {src dst i : Nat} (ht : s.gpr .r31 = BitVec.ofNat 64 (i + 1))
    (hsrc : i + src + 1 ≤ size) (hd : dst + 8 * i + 8 ≤ size) :
    WP isa (.block (bitsBody src dst)) s fun s' =>
      s'.gpr .r31 = BitVec.ofNat 64 i ∧ Kp bitsClob s s' ∧
      (∀ j < 8, s'.mem (off base (dst + (8 * i + j))) =
        if (s.mem (off base (src + i))).getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) 8 s.mem s'.mem := by
  have hs15 := hs.small
  simp only [bitsBody, List.cons_append]
  refine wp_decCounter (j := i + 1) (by omega_arith) ht ?_
  rw [Nat.add_sub_cancel]
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 i) = s₁
  have K₁ : Kp bitsClob s s₁ := by rw [← hs₁]; exact Kp.write s _ (by decide)
  have c₁ : s₁.gpr .r31 = BitVec.ofNat 64 i := by rw [← hs₁]; simp only [write_gpr, ite_true]
  have h3₁ := K₁.at h3
  refine wp_step exec_add ?_
  have a₂ : At (s₁.write .r4 (s₁.gpr .r3 + s₁.gpr .r31)) base .r4 i := by
    show s₁.gpr .r3 + s₁.gpr .r31 = _
    exact add_at h3₁ c₁
  refine wp_step (lbz_ok (K₁.ws hs |>.write _ _) a₂ (by decide) hsrc) ?_
  refine wp_step (exec_lsl (by decide)) ?_
  refine wp_step exec_add ?_
  refine wp_step (exec_li (by decide)) ?_
  generalize hs₂ : ((((s₁.write .r4 (s₁.gpr .r3 + s₁.gpr .r31)).write .r4 _).write .r5 _).write .r5 _).write
    .r7 (BitVec.ofNat 64 1) = s₂
  have K₂ : Kp bitsClob s₁ s₂ := by
    rw [← hs₂]
    exact ((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))
  have m₂ : s₂.mem = s.mem := by rw [← hs₂, ← hs₁]; rfl
  have r4₂ : s₂.gpr .r4 = (s.mem (off base (src + i))).setWidth 64 := by
    rw [← hs₂]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true, write_mem]
    rw [← hs₁, Nat.add_comm i src]; rfl
  have r7₂ : s₂.gpr .r7 = BitVec.ofNat 64 1 := by rw [← hs₂]; simp only [write_gpr, ite_true]
  have r5₂ : At s₂ base .r5 (8 * i) := by
    rw [← hs₂]; simp only [At, write_gpr, reduceCtorEq, ite_false, ite_true]
    rw [c₁, shl3 i, h3₁, off_add, Nat.zero_add]
  have c₂ : s₂.gpr .r31 = BitVec.ofNat 64 i := by
    rw [← hs₂]; simp only [write_gpr, reduceCtorEq, ite_false]; exact c₁
  refine WP.mono (bitJs_ok (K₂.ws (K₁.ws hs)) r5₂ r4₂ r7₂ hd 8 (Nat.le_refl _)) fun s₃ ⟨k₃, e₃, O₃⟩ =>
    ⟨by rw [k₃.g, c₂], (K₁.trans K₂).trans (k₃.mono), e₃, by rw [← m₂]; exact O₃⟩

/-- `bits`' loop invariant, at `r31 = i`: the bytes from `i` up are done. -/
structure BInv (base : Addr) (size src dst n : Nat) (s₀ s : State) (i : Nat) : Prop where
  ws : Ws s base size
  r3 : At s base .r3 0
  r31 : s.gpr .r31 = BitVec.ofNat 64 i
  keep : Kp bitsClob s₀ s
  mem : Outside base dst (64 * n) s₀.mem s.mem
  bits : ∀ t, 8 * i ≤ t → t < 64 * n → s.mem (off base (dst + t)) =
    if (s₀.mem (off base (src + t / 8))).getLsbD (t % 8) then 1 else 0

/-- `bits src dst (8 n)`: byte `t` of the table at `dst` is bit `t` of the
`n`-word number at `src`. -/
theorem bits_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {n src dst : Nat} (hn0 : 0 < n) (hsrc : src + 8 * n ≤ size) (hdst : dst + 64 * n ≤ size)
    (hsep : src + 8 * n ≤ dst ∨ dst + 64 * n ≤ src) :
    WP isa (bits src dst (8 * n)) s fun s' =>
      (∀ t < 64 * n, s'.mem (off base (dst + t)) =
        if (wordsVal s.mem base src n).testBit t then 1 else 0) ∧
      Kp bitsClob s s' ∧ Outside base dst (64 * n) s.mem s'.mem := by
  have hnw := hs.nowrap
  have hs15 := hs.small
  rw [bits_eq]
  refine WP.seq (wp_step (exec_li (by omega_arith)) (WP.block_nil ?_))
  have h₁ : BInv base size src dst n s (s.write .r31 (BitVec.ofNat 64 (8 * n))) (8 * n) :=
    ⟨hs.write _ _, h3.write _, by simp only [write_gpr, ite_true], Kp.write s _ (by decide), Outside.refl _ _ _ _,
      fun t ht ht' => absurd ht' (by omega_arith)⟩
  refine countLoop_ok (Inv := fun j s' => BInv base size src dst n s s' j) (n := 8 * n)
    (fun j s' hb => hb.r31) (fun j s' h1 h2 hb => ?_) (fun s' hb => ⟨fun t ht => ?_, hb.keep, hb.mem⟩)
    (by omega_arith) (by omega_arith) h₁
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega_arith⟩
    refine WP.mono (bitsBody_ok hb.ws hb.r3 hb.r31 (by omega_arith) (by omega_arith))
      fun s'' ⟨b', k', bits', O'⟩ => ?_
    have hbyte : s'.mem (off base (src + i)) = s.mem (off base (src + i)) :=
      hb.mem _ (by rw [ofs_off0 base (d := src + i) (by omega_arith)]; omega_arith)
    refine ⟨k'.ws hb.ws, k'.at hb.r3, by rw [b', Nat.add_sub_cancel], hb.keep.trans k',
      hb.mem.trans (O'.mono (by omega_arith) (by omega_arith)), fun t ht ht' => ?_⟩
    rcases Nat.lt_or_ge t (8 * (i + 1)) with h | h
    · have e := bits' (t - 8 * i) (by omega_arith)
      rw [show 8 * i + (t - 8 * i) = t by omega_arith, hbyte] at e
      rw [e, show t / 8 = i by omega_arith, show t % 8 = t - 8 * i by omega_arith]
    · rw [O' _ (by rw [ofs_off0 base (d := dst + t) (by omega_arith)]; omega_arith), hb.bits t (by omega_arith) ht']
  · rw [hb.bits t (by omega_arith) ht, show t = 8 * (t / 8) + t % 8 from (Nat.div_add_mod t 8).symm,
      VG.Proof.Weierstrass.testBit_byte s.mem base (a := src) (n := n) (by omega_arith) (Nat.mod_lt _ (by decide))]
    simp only [show (8 * (t / 8) + t % 8) / 8 = t / 8 by omega_arith, show (8 * (t / 8) + t % 8) % 8 = t % 8 by omega_arith]

end VG.Proof.Weierstrass.PPC64LE

end

end

/-!
# Short Weierstrass curves on PPC64LE: powers

`pow P S` leaves `[acc]` reading (in Montgomery form) as `[base]^e`, for
the exponent `e` whose bits are the table at `P.bits` (`pow_ok`): an
iteration squares the accumulator, multiplies it by the base into `[tmp]`
and keeps that product if the exponent's bit is set (`powBody_ok`), by
calls of the functions of `S`, as on 32-bit ARM
(`Proof/Weierstrass/Arm/Ladder.lean`). The functions hold their own copy of the
modulus, in their own working space, which is above the power's slots and
below its table (`PowLayP`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
  VG.Impl.Weierstrass.PPC64LE.Mont VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass
  VG.Proof.Weierstrass.PPC64LE.Mont

/-- The registers a power or the ladder changes. -/
def powClob : List Reg := .r31 :: fnClob

/-- What a power writes, for numbers of `k` words: the accumulator, the
temporary and the functions' own working space. -/
def powWx (P : PowCfg) (k : Nat) : List (Nat × Nat) :=
  [(P.acc, 8 * k), (P.tmp, 8 * k), (own k, 64 * k)]

/-- Where a power's slots and table are, for numbers of `k` words: the slots
below the functions' own working space, at multiples of 4, the table above it
in the working space, and what it reads apart from what it writes. -/
structure PowLayP (P : PowCfg) (k : Nat) : Prop where
  acc : P.acc + 8 * k ≤ own k
  tmp : P.tmp + 8 * k ≤ own k
  base : P.base + 8 * k ≤ own k
  one : P.one + 8 * k ≤ own k
  own : own k + 64 * k ≤ P.bits
  bits : P.bits + P.nbits ≤ 8192
  nbits : 1 ≤ P.nbits ∧ P.nbits < 2 ^ 15
  acc_tmp : P.acc + 8 * k ≤ P.tmp ∨ P.tmp + 8 * k ≤ P.acc
  acc_one : P.acc + 8 * k ≤ P.one ∨ P.one + 8 * k ≤ P.acc
  base_acc : P.base + 8 * k ≤ P.acc ∨ P.acc + 8 * k ≤ P.base
  base_tmp : P.base + 8 * k ≤ P.tmp ∨ P.tmp + 8 * k ≤ P.base
  acc4 : P.acc % 4 = 0
  tmp4 : P.tmp % 4 = 0
  one4 : P.one % 4 = 0

/-- The loop's invariant at `r31 = j`: the accumulator reads as
`B^(e >>> j)`, for `B` what the base reads as at the start. -/
structure PowInv (P : PowCfg) (k : Nat) (base : Addr) (m e : Nat) [NeZero m] (s₀ s : State)
    (j : Nat) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = BitVec.ofNat 64 j
  keep : Rk powClob s₀ s
  unch : Unch base (powWx P k) s₀.mem s.mem
  lt : wordsVal s.mem base P.acc k < m
  val : toM m (2 ^ (64 * k)) (wordsVal s.mem base P.acc k) =
    toM m (2 ^ (64 * k)) (wordsVal s₀.mem base P.base k) ^ (e >>> j)

/-- An iteration. -/
theorem powBody_ok {P : PowCfg} {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m)
    (hk : P.M.n = S.k) (hL : PowLayP P S.k) (hm : UnitMod S.m (2 ^ (64 * S.k))) {base : Addr} {e : Nat}
    {s₀ : State} (hB : wordsVal s₀.mem base P.base S.k < S.m)
    (hbits : ∀ t < P.nbits, s₀.mem (off base (P.bits + t)) = if e.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ P.nbits) (hI : PowInv P S.k base S.m e s₀ s j) :
    WP isa (powBody P S) s fun s' => PowInv P S.k base S.m e s₀ s' (j - 1) := by
  have hn := hI.ws.nowrap
  have := hL.acc; have := hL.tmp; have := hL.base; have := hL.own; have := hL.bits
  have hat := hL.acc_tmp
  have hba := hL.base_acc
  have hbt := hL.base_tmp
  have hBs : wordsVal s.mem base P.base S.k = wordsVal s₀.mem base P.base S.k :=
    hI.unch.wordsVal (fun w hw => by
      simp only [powWx, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hba
      · exact hbt
      · exact .inl hL.base) (by omega_arith)
  -- `r31 -= 1` and `acc = acc²`.
  rw [powBody]
  refine WP.seq (wp_decCounter hj hI.r31 (WP.block_nil ?_))
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 (j - 1)) = s₁
  have K₁ : Kp [.r31] s s₁ := by rw [← hs₁]; exact Kp.write _ _ (by decide)
  have w₁ := hI.ws.of_rk (K₁.rk (rs' := powClob))
  have m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  have c₁ : s₁.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hs₁]; simp only [write_gpr, ite_true]
  refine WP.seq (WP.mono (mulCall_ok hM w₁ hL.acc hL.acc hL.acc (by rw [m₁]; exact hI.lt))
    fun s₂ ⟨K₂, lt₂, e₂⟩ => ?_)
  have v₂ : toM S.m (2 ^ (64 * S.k)) (wordsVal s₂.mem base P.acc S.k) =
      toM S.m (2 ^ (64 * S.k)) (wordsVal s.mem base P.acc S.k) ^ 2 := by
    rw [toM_mul hm e₂, m₁, Lean.Grind.Semiring.pow_two]
  have U₂ : Unch base [(P.acc, 8 * S.k), (own S.k, 64 * S.k)] s.mem s₂.mem := by rw [← m₁]; exact K₂.mem
  have hB₂ : wordsVal s₂.mem base P.base S.k = wordsVal s₀.mem base P.base S.k := by
    rw [U₂.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hba
      · exact .inl hL.base) (by omega_arith), hBs]
  -- `tmp = acc · base`.
  have w₂ := w₁.of_rk (K₂.rk (rs := powClob))
  refine WP.seq (WP.mono (mulCall_ok hM w₂ hL.tmp hL.acc hL.base (by rw [hB₂]; exact hB))
    fun s₃ ⟨K₃, lt₃, e₃⟩ => ?_)
  have U₃ : Unch base [(P.tmp, 8 * S.k), (own S.k, 64 * S.k)] s₂.mem s₃.mem := K₃.mem
  have hA₃ : wordsVal s₃.mem base P.acc S.k = wordsVal s₂.mem base P.acc S.k :=
    U₃.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hat
      · exact .inl hL.acc) (by omega_arith)
  have v₃ : toM S.m (2 ^ (64 * S.k)) (wordsVal s₃.mem base P.tmp S.k) =
      toM S.m (2 ^ (64 * S.k)) (wordsVal s₂.mem base P.acc S.k) *
        toM S.m (2 ^ (64 * S.k)) (wordsVal s₀.mem base P.base S.k) := by
    rw [toM_mul hm e₃, hB₂]
  -- The mask of bit `j - 1`, and the selection.
  have hU₃ : Unch base (powWx P S.k) s₀.mem s₃.mem := by
    refine ((hI.unch.trans U₂).trans U₃).mono fun w hw => ?_
    simp only [powWx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with ((h | h | h) | h | h) | h | h <;> simp [h]
  have hbyte : s₃.mem (off base (P.bits + (j - 1))) = if e.testBit (j - 1) then 1 else 0 := by
    rw [hU₃.byte (fun w hw => by
      simp only [powWx, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> (simp only; omega_arith)) (by omega_using [hjn, this]), hbits _ (by omega_using [hj, hjn])]
  have w₃ := w₂.of_rk (K₃.rk (rs := powClob))
  have c₃ : s₃.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [K₃.gpr _ (by decide), K₂.gpr _ (by decide), c₁]
  refine wp_append (WP.mono (bitMask_bool_ok w₃.ws w₃.at3 c₃ (by omega_using [hj, hjn, this]) hbyte) fun s₄ ⟨g₄, k₄, m₄⟩ => ?_)
  rw [hk]
  refine WP.mono (sel_ok (e.testBit (j - 1)) S.k (k₄.ws w₃.ws) (k₄.at w₃.at3) g₄ (o := P.acc) (a := P.acc)
    (b := P.tmp) hL.acc4 hL.acc4 hL.tmp4 (by omega_arith) (by omega_arith) (by omega_arith) (Or.inl (Nat.le_refl _))
    (by omega_using [hat])) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have k₅' : Rk powClob s₃ s₅ := (k₄.rk (rs' := powClob)).trans (k₅.rk (rs' := powClob))
  refine ⟨w₃.of_rk k₅', by rw [k₅.g, k₄.g, c₃],
    (((hI.keep.trans (K₁.rk (rs' := powClob))).trans (K₂.rk (rs := powClob))).trans (K₃.rk (rs := powClob))).trans
      k₅', fun x hx => ?_, ?_, ?_⟩
  · rw [O₅ x (hx _ (List.mem_cons_self ..)), m₄]
    exact hU₃ x hx
  · rw [e₅, m₄]
    split
    · exact lt₃
    · rw [hA₃]; exact lt₂
  · rw [e₅, m₄, pow_shiftRight _ e (j - 1), Nat.sub_add_cancel hj, ← hI.val]
    split
    · rw [v₃, v₂]
    · rw [hA₃, v₂, Lean.Grind.Semiring.mul_one]

/-- `pow_ok`, for the modulus's own numbers. -/
theorem pow_ok' {P : PowCfg} {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m)
    (hk : P.M.n = S.k) (hL : PowLayP P S.k) (hm : UnitMod S.m (2 ^ (64 * S.k))) {base : Addr} {e : Nat}
    {s : State} (hs : WsReg s base) (hB : wordsVal s.mem base P.base S.k < S.m)
    (hO : wordsVal s.mem base P.one S.k = 2 ^ (64 * S.k) % S.m)
    (hbits : ∀ t < P.nbits, s.mem (off base (P.bits + t)) = if e.testBit t then 1 else 0)
    (he : e < 2 ^ P.nbits) :
    WP isa (pow P S) s fun s' => Rk powClob s s' ∧ Unch base (powWx P S.k) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc S.k < S.m ∧
      toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem base P.acc S.k) =
        toM S.m (2 ^ (64 * S.k)) (wordsVal s.mem base P.base S.k) ^ e := by
  have hn := hs.nowrap
  have hnb := hL.nbits
  have hm0 : 0 < S.m := m_pos hB
  have := hL.acc; have := hL.one; have := hL.own; have := hL.bits
  have hao := hL.acc_one
  rw [pow, hk]
  refine WP.seq (wp_append (WP.mono (copy_ok S.k hs.ws hs.at3 (o := P.acc) (a := P.one) hL.acc4 hL.one4
    (by omega_arith) (by omega_arith) (by omega_using [hao])) fun s₁ ⟨e₁, k₁, O₁⟩ =>
      wp_step (exec_li hnb.2) (WP.block_nil ?_)))
  refine countLoop_ok (Inv := fun j s' => PowInv P S.k base S.m e s s' j) (n := P.nbits)
    (fun j s' hi => hi.r31) (fun j s' h1 h2 hi => powBody_ok hM hk hL hm hB hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.lt, by rw [hi.val, Nat.shiftRight_zero]⟩) hnb.1 (by omega_using [hnb]) ?_
  have hv : wordsVal (s₁.write .r31 (BitVec.ofNat 64 P.nbits)).mem base P.acc S.k =
      wordsVal s.mem base P.one S.k := by
    rw [write_mem, e₁]
  have K : Kp powClob s (s₁.write .r31 (BitVec.ofNat 64 P.nbits)) :=
    (k₁.mono (by decide)).trans (Kp.write _ _ (by decide))
  refine ⟨hs.of_rk (K.rk (rs' := powClob)), by simp only [write_gpr, ite_true], K.rk, ?_, ?_, ?_⟩
  · rw [write_mem]
    exact O₁.unch.mono fun w hw => by simp at hw; simp [hw, powWx]
  · rw [hv, hO]; exact Nat.mod_lt _ hm0
  · rw [hv, hO, toM_one hm, shiftRight_eq_zero he, Lean.Grind.Semiring.pow_zero]

/-- `[acc] = [base]^e` in Montgomery form, for the exponent `e < 2^nbits`
whose bits are the table at `P.bits`, modulo `m` on numbers of `k` words
(the functions' `S.m` and `S.k`); only `powClob` and `powWx` change. -/
theorem pow_ok {P : PowCfg} {S : Impl.Weierstrass.Mont.Modulus} {k m : Nat} [NeZero m] (hkS : S.k = k)
    (hmS : S.m = m) (hM : ModOk k m) (hk : P.M.n = k) (hL : PowLayP P k) (hm : UnitMod m (2 ^ (64 * k)))
    {base : Addr} {e : Nat} {s : State} (hs : WsReg s base) (hB : wordsVal s.mem base P.base k < m)
    (hO : wordsVal s.mem base P.one k = 2 ^ (64 * k) % m)
    (hbits : ∀ t < P.nbits, s.mem (off base (P.bits + t)) = if e.testBit t then 1 else 0)
    (he : e < 2 ^ P.nbits) :
    WP isa (pow P S) s fun s' => Rk powClob s s' ∧ Unch base (powWx P k) s.mem s'.mem ∧
      wordsVal s'.mem base P.acc k < m ∧
      toM m (2 ^ (64 * k)) (wordsVal s'.mem base P.acc k) =
        toM m (2 ^ (64 * k)) (wordsVal s.mem base P.base k) ^ e := by
  obtain ⟨cv, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  exact pow_ok' (S := ⟨cv, w, m', k', d⟩) hM hk hL hm hs hB hO hbits he

end VG.Proof.Weierstrass.PPC64LE
