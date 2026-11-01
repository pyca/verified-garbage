module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.Mont
public import VerifiedGarbage.Proof.Mont.PPC64LE.Ops
import VerifiedGarbage.Proof.Mont.PPC64LE.Const
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
public import VerifiedGarbage.Proof.Mont.Words32

/-!
# Montgomery arithmetic modulo a curve's `p` or `n`, as functions, on PPC64LE

`fn n m op` (`Impl/Weierstrass/PPC64LE/Mont.lean`), from a state `Pre n`
(`ws` in `r3`, the offsets in the low halves of `r4`–`r6`, the working
space writable and the numbers below the own working space), runs the entry
(`entry_ok`): the pointers to the numbers in `r4`–`r6` and the modulus
stored; then the operation (`mulFn_ok`, `addFn_ok`, `subFn_ok`). The
functions write only volatile registers (`fnClob`), and change the memory
only at `[o]` and in the own working space (`Kept`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Mont

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Mont.PPC64LE VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Mont VG.Proof.Mont.PPC64LE

/-- What the functions need of the modulus `m` of `n` words. -/
structure ModOk (n m : Nat) : Prop where
  n1 : 1 ≤ n
  n9 : n ≤ 9
  m0 : 0 < m
  m_lt : m < 2 ^ (64 * n)
  inv : (m * minv m + 1) % 2 ^ 64 = 0

/-- The offset argument in `r`: its low 32 bits. -/
abbrev lo (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- The precondition, on the registers. -/
structure Pre (n : Nat) (s : State) : Prop where
  wr : s.wr = [⟨s.gpr .r3, 8192⟩]
  fit : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 64
  o : lo s .r4 + 8 * n ≤ own n
  a : lo s .r5 + 8 * n ≤ own n
  b : lo s .r6 + 8 * n ≤ own n

/-- The registers the functions write. -/
def fnClob : List Reg := [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

/-- The memory changes only at `[o]` and in the own working space. -/
def Kept (n : Nat) (base : Addr) (o : Nat) (m m' : Mem) : Prop :=
  Outs base [(o, 8 * n), (own n, 64 * n)] m m'

theorem own_le (n : Nat) (h : n ≤ 9) : own n + 64 * n = 4096 := by
  simp only [own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]; omega

theorem ext_lo (x : BitVec 64) : ((x.setWidth 32).rotateRight 0).setWidth 64 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  rw [rotr0]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem minv_lt (m : Nat) : minv m < 2 ^ 64 := Nat.mod_lt _ (by decide)

/-- The layout of the operations in the function. -/
theorem lay {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n s) :
    OpLay (mod n m) 4096 (own n) (lo s .r4) (lo s .r5) (lo s .r6) := by
  have := own_le n hM.n9
  have := hM.n1
  have := hp.o
  have := hp.a
  have := hp.b
  simp only [own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try dsimp only [mod, tmpAt, moAt, own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]) <;> omega

/-- The state after the zero-extension of the offsets. -/
def zextState (s : State) : State :=
  ((s.write .r4 (BitVec.ofNat 64 (lo s .r4))).write .r5 (BitVec.ofNat 64 (lo s .r5))).write .r6
    (BitVec.ofNat 64 (lo s .r6))

theorem exec_zext {s s' : State} {t : List Leak} (h : Exec isa (.block zext) s t s') :
    t = [] ∧ s' = zextState s := by
  cases h with
  | block b =>
    simp only [zext, execBlock, exec_rotr_w (show 0 < 32 by decide), addrs, Option.map_some, List.map_nil,
      List.nil_append, Option.some.injEq, Prod.mk.injEq, ext_lo] at b
    refine ⟨b.2.symm, b.1.symm.trans ?_⟩
    simp only [zextState, lo, write_gpr, reduceCtorEq, ite_false]

theorem zext_wp (s : State) : WP isa (.block zext) s (· = zextState s) := by
  refine wp_step (exec_rotr_w (by decide)) (wp_step (exec_rotr_w (by decide))
    (wp_step (exec_rotr_w (by decide)) (WP.block_nil ?_)))
  simp only [zextState, lo, write_gpr, reduceCtorEq, ite_false, ext_lo]

/-- What the entry leaves. -/
theorem entry_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n s) :
    WP isa (.block (entry n m)) (zextState s) fun u =>
      OpPre (mod n m) (s.gpr .r3) 4096 (lo s .r4) (lo s .r5) (lo s .r6) m u ∧
      Outside (s.gpr .r3) (moAt n) (8 * n) s.mem u.mem ∧ Kp fnClob s u := by
  have h9 := own_le n hM.n9
  have hn1 := hM.n1
  have hs : Ws s (s.gpr .r3) 4096 := ⟨⟨8192, by decide, by rw [hp.wr]; simp, hp.fit⟩, by decide⟩
  have h3 : At s (s.gpr .r3) .r3 0 := by simp [At, off]
  simp only [entry, List.cons_append, List.nil_append]
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  refine wp_step exec_add ?_
  simp only [zextState, write_gpr, ite_true, reduceCtorEq, ite_false]
  refine WP.mono (setConst_ok ((((((hs.write _ _).write _ _).write _ _).write _ _).write _ _).write _ _)
    ((((((h3.write _).write _).write _).write _).write _).write _)
    (o := moAt n) (n := n) (x := m) (by simp only [moAt, tmpAt]; omega) hM.m_lt) fun u ⟨O, V, K⟩ => ?_
  simp only [write_mem] at O V
  have K₀ : Kp fnClob s u := (((((((Kp.write s _ (by decide)).trans (Kp.write _ _ (by decide))).trans
    (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
    (Kp.write _ _ (by decide)))).trans (K.mono (by decide))
  refine ⟨⟨K₀.ws hs, ?_, ?_, ?_, ?_, V, hM.m0⟩, O, K₀⟩
  · rw [At, K.g]; simp only [write_gpr, reduceCtorEq, ite_false]; exact h3
  · rw [At, K.g]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
  · rw [At, K.g]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
  · rw [At, K.g]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]

/-- The function of an operation, from what the entry leaves. -/
theorem fn_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n s) {op : Prog isa} {Q : State → Prop}
    (hop : ∀ u, OpPre (mod n m) (s.gpr .r3) 4096 (lo s .r4) (lo s .r5) (lo s .r6) m u →
      Outside (s.gpr .r3) (moAt n) (8 * n) s.mem u.mem → Kp fnClob s u → WP isa op u Q) :
    WP isa (fn n m op) s Q :=
  WP.seq (WP.mono (zext_wp s) fun _ hz => hz ▸ WP.seq (WP.mono (entry_ok hM hp) fun u ⟨P, O, K⟩ => hop u P O K))

/-- What the functions keep. -/
theorem abi_of_kp {s u : State} (h : Kp fnClob s u) : abiPreserved s u :=
  ⟨fun r hr => h.gpr r (fun h' => absurd h' ((by decide : ∀ r ∈ preserved, r ∉ fnClob) r hr)), h.sp, h.lr⟩

/-- The memory the function changes: the entry's modulus and the operation's ranges. -/
theorem kept_of {n m : Nat} (hM : ModOk n m) {base : Addr} {O : Nat} {m₀ m₁ m₂ : Mem}
    (h₁ : Outside base (moAt n) (8 * n) m₀ m₁) (h₂ : Outs base (opOuts (mod n m) (own n) O) m₁ m₂) :
    Kept n base O m₀ m₂ := by
  have := own_le n hM.n9
  have := hM.n1
  refine (Outs.cover (Outs.of_outside h₁ (List.mem_singleton_self _)) ?_).trans (Outs.cover h₂ ?_)
  · intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    exact ⟨(own n, 64 * n), by simp, by simp only [moAt, tmpAt]; omega, by simp only [moAt, tmpAt]; omega⟩
  · intro r hr
    simp only [opOuts, mod, tmpAt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨(own n, 64 * n), by simp, by simp, by dsimp only; omega⟩
    · exact ⟨(own n, 64 * n), by simp, by dsimp only; omega, by dsimp only; omega⟩
    · exact ⟨(O, 8 * n), by simp, by simp, by simp⟩

theorem exec_of_wp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    ∃ t s', Exec isa c s t s' ∧ Q s' := h

/-- `vg_<curve>_mul_mod_<p|n>`. -/
theorem mulFn_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n s)
    (hb : wordsVal s.mem (s.gpr .r3) (lo s .r6) n < m) :
    ∃ t s', Exec isa (mulFn n m) s t s' ∧ abiPreserved s s' ∧ (∀ r, r ∉ fnClob → s'.gpr r = s.gpr r) ∧
      wordsVal s'.mem (s.gpr .r3) (lo s .r4) n < m ∧
      wordsVal s'.mem (s.gpr .r3) (lo s .r4) n * 2 ^ (64 * n) % m =
        wordsVal s.mem (s.gpr .r3) (lo s .r5) n * wordsVal s.mem (s.gpr .r3) (lo s .r6) n % m ∧
      Kept n (s.gpr .r3) (lo s .r4) s.mem s'.mem := by
  have h9 := own_le n hM.n9
  refine exec_of_wp (fn_ok hM hp fun u P O₁ K₁ => ?_)
  have hbu : wordsVal u.mem (s.gpr .r3) (lo s .r6) (mod n m).n < m := by
    rw [show (mod n m).n = n from rfl, O₁.wordsVal (by have := hp.b; simp only [moAt, tmpAt]; omega) (by have := hp.fit; have := hp.a; have := hp.b; omega)]; exact hb
  have hinv : (m * (mod n m).minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [show (mod n m).minv = BitVec.ofNat 64 (minv m) from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (minv_lt m)]
    exact hM.inv
  have en : (mod n m).n = n := rfl
  refine WP.mono (mul_ok P (lay hM hp) hinv hbu) fun v ⟨V, C, O₂, K₂⟩ => ⟨abi_of_kp (K₁.trans (K₂.mono (by decide))), (K₁.trans (K₂.mono (by decide))).gpr,
    by rw [en] at V; exact V, ?_, kept_of hM O₁ O₂⟩
  rw [en] at C
  rw [C]
  have ha := O₁.wordsVal (d := lo s .r5) (k := n) (by have := hp.a; simp only [moAt, tmpAt]; omega)
    (by have := hp.fit; have := hp.a; have := hp.b; omega)
  have hb' := O₁.wordsVal (d := lo s .r6) (k := n) (by have := hp.b; simp only [moAt, tmpAt]; omega)
    (by have := hp.fit; have := hp.a; have := hp.b; omega)
  rw [ha, hb']

/-- `vg_<curve>_add_mod_<p|n>`. -/
theorem addFn_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n s)
    (hab : wordsVal s.mem (s.gpr .r3) (lo s .r5) n + wordsVal s.mem (s.gpr .r3) (lo s .r6) n < 2 * m) :
    ∃ t s', Exec isa (addFn n m) s t s' ∧ abiPreserved s s' ∧ (∀ r, r ∉ fnClob → s'.gpr r = s.gpr r) ∧
      wordsVal s'.mem (s.gpr .r3) (lo s .r4) n =
        (wordsVal s.mem (s.gpr .r3) (lo s .r5) n + wordsVal s.mem (s.gpr .r3) (lo s .r6) n) % m ∧
      Kept n (s.gpr .r3) (lo s .r4) s.mem s'.mem := by
  have h9 := own_le n hM.n9
  refine exec_of_wp (fn_ok hM hp fun u P O₁ K₁ => ?_)
  have ha := O₁.wordsVal (d := lo s .r5) (k := n) (by have := hp.a; simp only [moAt, tmpAt]; omega)
    (by have := hp.fit; have := hp.a; have := hp.b; omega)
  have hb' := O₁.wordsVal (d := lo s .r6) (k := n) (by have := hp.b; simp only [moAt, tmpAt]; omega)
    (by have := hp.fit; have := hp.a; have := hp.b; omega)
  refine WP.mono (add_ok (M := mod n m) P (lay hM hp) (by simp only [mod]; rw [ha, hb']; exact hab))
    fun v ⟨V, O₂, K₂⟩ => ⟨abi_of_kp (K₁.trans (K₂.mono (by decide))), (K₁.trans (K₂.mono (by decide))).gpr, ?_, kept_of hM O₁ O₂⟩
  have en : (mod n m).n = n := rfl
  rw [en] at V; rw [V, ha, hb']

/-- `vg_<curve>_sub_mod_<p|n>`. -/
theorem subFn_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n s)
    (ha : wordsVal s.mem (s.gpr .r3) (lo s .r5) n < m) (hb : wordsVal s.mem (s.gpr .r3) (lo s .r6) n < m) :
    ∃ t s', Exec isa (subFn n m) s t s' ∧ abiPreserved s s' ∧ (∀ r, r ∉ fnClob → s'.gpr r = s.gpr r) ∧
      wordsVal s'.mem (s.gpr .r3) (lo s .r4) n =
        (wordsVal s.mem (s.gpr .r3) (lo s .r5) n + m - wordsVal s.mem (s.gpr .r3) (lo s .r6) n) % m ∧
      Kept n (s.gpr .r3) (lo s .r4) s.mem s'.mem := by
  have h9 := own_le n hM.n9
  refine exec_of_wp (fn_ok hM hp fun u P O₁ K₁ => ?_)
  have ha' := O₁.wordsVal (d := lo s .r5) (k := n) (by have := hp.a; simp only [moAt, tmpAt]; omega)
    (by have := hp.fit; have := hp.a; have := hp.b; omega)
  have hb' := O₁.wordsVal (d := lo s .r6) (k := n) (by have := hp.b; simp only [moAt, tmpAt]; omega)
    (by have := hp.fit; have := hp.a; have := hp.b; omega)
  refine WP.mono (sub_ok (M := mod n m) P (lay hM hp) (by simp only [mod]; rw [ha']; exact ha)
    (by simp only [mod]; rw [hb']; exact hb))
    fun v ⟨V, O₂, K₂⟩ => ⟨abi_of_kp (K₁.trans (K₂.mono (by decide))), (K₁.trans (K₂.mono (by decide))).gpr, ?_, kept_of hM O₁ O₂⟩
  have en : (mod n m).n = n := rfl
  rw [en] at V; rw [V, ha', hb']

end VG.Proof.Weierstrass.PPC64LE.Mont
