module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.Call
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontFn
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

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
  exact h.val32 (fun r hr => by have := hd r hr; omega) (by omega)

theorem lo_li {x : Nat} (hx : x < 2 ^ 32) : ((BitVec.ofNat 64 x).setWidth 32).toNat = x := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

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
  have g4 : lo s₃ .r4 = o := by rw [← hs₃]; simp only [lo, write_gpr, reduceCtorEq, ite_false, ite_true]; exact lo_li (by omega)
  have g5 : lo s₃ .r5 = a := by rw [← hs₃]; simp only [lo, write_gpr, reduceCtorEq, ite_false, ite_true]; exact lo_li (by omega)
  have g6 : lo s₃ .r6 = b := by rw [← hs₃]; simp only [lo, write_gpr, reduceCtorEq, ite_false, ite_true]; exact lo_li (by omega)
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
  simp only [own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]; omega

/-- The arguments of a call, as the functions' precondition has them. -/
theorem pre_of_call {n : Nat} {base : Addr} (hn : base.toNat + 8192 ≤ 2 ^ 64) {o a b : Nat}
    (ho : o + 8 * n ≤ own n) (ha : a + 8 * n ≤ own n) (hb : b + 8 * n ≤ own n) {t : State}
    (h2 : t.wr = [⟨base, 8192⟩]) (h3 : t.gpr .r3 = base) (h4 : lo t .r4 = o) (h5 : lo t .r5 = a)
    (h6 : lo t .r6 = b) : Pre n t :=
  ⟨by rw [h2, h3], by rw [h3]; exact hn, by rw [h4]; exact ho, by rw [h5]; exact ha, by rw [h6]; exact hb⟩

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`. -/
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
    rfl hw (by omega) (by omega) (by omega) fun t _ h2 h3 h4 h5 h6 h7 => by
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
    rfl hw (by omega) (by omega) (by omega) fun t _ h2 h3 h4 h5 h6 h7 => by
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
    rfl hw (by omega) (by omega) (by omega) fun t _ h2 h3 h4 h5 h6 h7 => by
      obtain ⟨tr, t', he, A, G, V, K⟩ := subFn_ok hM (pre_of_call hw.nowrap ho ha hb h2 h3 h4 h5 h6)
        (by rw [h3, h5, h7]; exact hA) (by rw [h3, h6, h7]; exact hB)
      rw [h3, h4, h5, h6] at *
      exact ⟨tr, t', he, A, G, K, V⟩

end VG.Proof.Weierstrass.PPC64LE.Mont
