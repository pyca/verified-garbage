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

theorem zext_wp (s : State) : WP isa (.block zext) s (· = zextState s) := by
  refine wp_step (exec_rotr_w (by decide)) (wp_step (exec_rotr_w (by decide))
    (wp_step (exec_rotr_w (by decide)) (WP.block_nil ?_)))
  simp only [zextState, lo, write_gpr, reduceCtorEq, ite_false, ext_lo]

/-- `r11` stored at `[r3 + o + 8j]` for `j < k`. -/
theorem stores_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {o : Nat} (ho4 : o % 4 = 0) : ∀ {k : Nat}, o + 8 * k ≤ size →
    WP isa (.block ((List.range k).map fun j => .store .d .r11 wb (o + 8 * j))) s fun u =>
      (∀ j < k, word u.mem base (o + 8 * j) = s.gpr .r11) ∧ Outside base o (8 * k) s.mem u.mem ∧ Kp [] s u
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, Kp.refl _ _⟩
  | k + 1, hk => by
    have hs15 := hs.small
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine WP.block_append (WP.mono (stores_ok hs h3 ho4 (k := k) (by omega)) fun s₁ ⟨V₁, O₁, K₁⟩ => ?_)
    refine wp_step (std_ok (K₁.ws hs) (K₁.at h3 (by simp)) (by decide) (by omega) (d := o + 8 * k) (by omega))
      (WP.block_nil ?_)
    rw [Nat.zero_add, K₁.gpr _ (by simp)]
    refine ⟨fun j hj => ?_, ?_, ⟨fun r _ => K₁.gpr r (by simp), K₁.rd, K₁.wr, K₁.sp, K₁.lr⟩⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · show word (s₁.mem.writeW _ _) base _ = _
        rw [(writeW_outside s₁.mem base _ (by omega)).word (by omega) (by omega), V₁ j hj]
      · exact word_writeW_self _ _ _ _
    · exact (O₁.mono (Nat.le_refl _) (by omega)).trans
        ((writeW_outside s₁.mem base (d := o + 8 * k) _ (by omega)).mono (by omega) (by omega))

theorem wordsVal_ones {mem : Mem} {base : Addr} {o : Nat} :
    ∀ {k : Nat}, (∀ j < k, word mem base (o + 8 * j) = BitVec.ofNat 64 (2 ^ 64 - 1)) →
      wordsVal mem base o k + 1 = 2 ^ (64 * k)
  | 0, _ => rfl
  | k + 1, h => by
    rw [wordsVal_succ_top, h k (by omega), BitVec.toNat_ofNat, Nat.add_right_comm,
      wordsVal_ones fun j hj => h j (by omega), show 64 * (k + 1) = 64 * k + 64 by omega, Nat.pow_add]
    have : (2 ^ 64 - 1) % 2 ^ 64 = 2 ^ 64 - 1 := by decide
    rw [this]
    have : 1 ≤ 2 ^ 64 := by decide
    generalize 2 ^ (64 * k) = P
    grind

/-- `setMers`: the Mersenne modulus `m = 2^(64 (n - 1) + k) - 1` stored, as
`setConst` stores it. -/
theorem setMers_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {n k o m : Nat}
    (h3 : At s base .r3 0) (ho : o + 8 * n ≤ size) (ho4 : o % 4 = 0) (hn : 2 ≤ n) (hk : k < 64)
    (hm : m + 1 = 2 ^ (64 * (n - 1) + k)) :
    WP isa (.block (setMers n k o)) s fun u =>
      Outside base o (8 * n) s.mem u.mem ∧ val32 u.mem base o (2 * n) = m ∧ Kp [.r11] s u := by
  have hs15 := hs.small
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hm
  have hk1 : 2 ^ k - 1 < 2 ^ 64 := by
    have : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  simp only [setMers, Nat.add_sub_cancel, List.append_assoc]
  refine movImm64_ok (by decide) ?_
  refine WP.block_append (WP.mono (stores_ok (hs.write _ _) (h3.write _) ho4 (k := N) (by omega))
    fun s₁ ⟨V₁, O₁, K₁⟩ => ?_)
  refine movImm64_ok hk1 ?_
  have hs₁ : Ws (s₁.write .r11 (BitVec.ofNat 64 (2 ^ k - 1))) base size := (K₁.ws (hs.write _ _)).write _ _
  have h3₁ : At (s₁.write .r11 (BitVec.ofNat 64 (2 ^ k - 1))) base .r3 0 := (K₁.at (h3.write _) (by simp)).write _
  refine wp_step (std_ok hs₁ h3₁ (by decide) (by omega) (d := o + 8 * N) (by omega)) (WP.block_nil ?_)
  simp only [write_mem, write_gpr, ite_true, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · exact (O₁.mono (Nat.le_refl _) (by omega)).trans
      ((writeW_outside s₁.mem base (d := o + 8 * N) _ (by have := hs.nowrap; omega)).mono (by omega) (by omega))
  · rw [← wordsVal_eq_val32, wordsVal_succ_top, word_writeW_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk1]
    have hlow : wordsVal (s₁.mem.writeW (off base (o + 8 * N)) (BitVec.ofNat 64 (2 ^ k - 1))) base o N =
        wordsVal s₁.mem base o N :=
      (writeW_outside s₁.mem base _ (by have := hs.nowrap; omega)).wordsVal (by omega) (by have := hs.nowrap; omega)
    rw [hlow]
    have hw := wordsVal_ones (mem := s₁.mem) (base := base) (o := o) (k := N) fun j hj => by
      rw [V₁ j hj]; simp only [write_gpr, ite_true]
    rw [Nat.pow_add] at hm
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    generalize 2 ^ (64 * N) = P at *
    generalize 2 ^ k = K at *
    generalize wordsVal s₁.mem base o N = W at *
    have : P * (K - 1) + P = P * K := by
      rw [Nat.mul_sub, Nat.mul_one]; have := Nat.le_mul_of_pos_right P (show 0 < K by omega); omega
    omega
  · exact ((Kp.write _ _ (by simp)).trans (K₁.mono (by simp))).trans ((Kp.write _ _ (by simp)).trans
      ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩)

/-- What the entry leaves. -/
theorem entry_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n s) :
    WP isa (.block (entry n m)) (zextState s) fun u =>
      RegPre (s.gpr .r3) 4096 (lo s .r4) (lo s .r5) (lo s .r6) m u ∧
      (¬n ≤ 4 → val32 u.mem (s.gpr .r3) (moAt n) (2 * n) = m) ∧
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
  have K₀ : Kp fnClob s ((((((s.write .r4 (BitVec.ofNat 64 (lo s .r4))).write .r5 (BitVec.ofNat 64 (lo s .r5))).write .r6
      (BitVec.ofNat 64 (lo s .r6))).write .r4 (s.gpr .r3 + BitVec.ofNat 64 (lo s .r4))).write .r5
      (s.gpr .r3 + BitVec.ofNat 64 (lo s .r5))).write .r6 (s.gpr .r3 + BitVec.ofNat 64 (lo s .r6))) :=
    (((((Kp.write s _ (by decide)).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))
  split
  · refine WP.block_nil ⟨⟨K₀.ws hs, ?_, ?_, ?_, ?_, hM.m0⟩, fun h => absurd ‹_› h, Outside.refl _ _ _ _, K₀⟩
    · rw [At, K₀.g]; exact h3
    · rw [At]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
    · rw [At]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
    · rw [At]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
  rename_i h4
  have hstore : WP isa (.block (if 0 < mersK n m then setMers n (mersK n m) (moAt n) else setConst n (moAt n) m))
      (((((((s.write .r4 (BitVec.ofNat 64 (lo s .r4))).write .r5 (BitVec.ofNat 64 (lo s .r5))).write .r6
        (BitVec.ofNat 64 (lo s .r6))).write .r4 (s.gpr .r3 + BitVec.ofNat 64 (lo s .r4))).write .r5
        (s.gpr .r3 + BitVec.ofNat 64 (lo s .r5))).write .r6 (s.gpr .r3 + BitVec.ofNat 64 (lo s .r6))))
      fun u => Outside (s.gpr .r3) (moAt n) (8 * n) s.mem u.mem ∧ val32 u.mem (s.gpr .r3) (moAt n) (2 * n) = m ∧
        Kp [.r11] (((((((s.write .r4 (BitVec.ofNat 64 (lo s .r4))).write .r5 (BitVec.ofNat 64 (lo s .r5))).write .r6
          (BitVec.ofNat 64 (lo s .r6))).write .r4 (s.gpr .r3 + BitVec.ofNat 64 (lo s .r4))).write .r5
          (s.gpr .r3 + BitVec.ofNat 64 (lo s .r5))).write .r6 (s.gpr .r3 + BitVec.ofNat 64 (lo s .r6)))) u := by
    have h3₀ : At (((((((s.write .r4 (BitVec.ofNat 64 (lo s .r4))).write .r5 (BitVec.ofNat 64 (lo s .r5))).write .r6
        (BitVec.ofNat 64 (lo s .r6))).write .r4 (s.gpr .r3 + BitVec.ofNat 64 (lo s .r4))).write .r5
        (s.gpr .r3 + BitVec.ofNat 64 (lo s .r5))).write .r6 (s.gpr .r3 + BitVec.ofNat 64 (lo s .r6)))) (s.gpr .r3) .r3 0 :=
      ((((((h3.write _).write _).write _).write _).write _).write _)
    split
    · rename_i hF
      obtain ⟨hn2, hk64, hmk⟩ := mersK_spec hF
      have ho : moAt n + 8 * n ≤ 4096 := by simp only [moAt, tmpAt]; omega
      have ho4 : moAt n % 4 = 0 := by
        simp only [moAt, tmpAt, own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]; omega
      exact setMers_ok ((((((hs.write _ _).write _ _).write _ _).write _ _).write _ _).write _ _) h3₀ ho ho4
        hn2 hk64 hmk
    · exact setConst_ok ((((((hs.write _ _).write _ _).write _ _).write _ _).write _ _).write _ _) h3₀
        (o := moAt n) (n := n) (x := m) (by simp only [moAt, tmpAt]; omega) hM.m_lt
  refine WP.mono hstore fun u ⟨O, V, K⟩ => ?_
  have K₀ : Kp fnClob s u := (((((((Kp.write s _ (by decide)).trans (Kp.write _ _ (by decide))).trans
    (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
    (Kp.write _ _ (by decide)))).trans (K.mono (by decide))
  refine ⟨⟨K₀.ws hs, ?_, ?_, ?_, ?_, hM.m0⟩, fun _ => V, O, K₀⟩
  · rw [At, K.g]; simp only [write_gpr, reduceCtorEq, ite_false]; exact h3
  · rw [At, K.g]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
  · rw [At, K.g]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]
  · rw [At, K.g]; simp only [write_gpr, reduceCtorEq, ite_false, ite_true]

/-- The function of an operation, from what the entry leaves. -/
theorem fn_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n s) {op : Prog isa} {Q : State → Prop}
    (hop : ∀ u, RegPre (s.gpr .r3) 4096 (lo s .r4) (lo s .r5) (lo s .r6) m u →
      (¬n ≤ 4 → val32 u.mem (s.gpr .r3) (moAt n) (2 * n) = m) →
      Outside (s.gpr .r3) (moAt n) (8 * n) s.mem u.mem → Kp fnClob s u → WP isa op u Q) :
    WP isa (fn n m op) s Q :=
  WP.seq (WP.mono (zext_wp s) fun _ hz => hz ▸ WP.seq (WP.mono (entry_ok hM hp) fun u ⟨P, V, O, K⟩ => hop u P V O K))

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

/-- The multiplication pushes no frame. -/
theorem mulFn_noFrames (n m : Nat) : (mulFn n m).noFrames = true := by
  rfl

/-- `vg_<curve>_mul_mod_<p|n>`. -/
theorem mulFn_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n s)
    (hb : wordsVal s.mem (s.gpr .r3) (lo s .r6) n < m) :
    ∃ t s', Exec isa (mulFn n m) s t s' ∧ abiPreserved s s' ∧ (∀ r, r ∉ fnClob → s'.gpr r = s.gpr r) ∧
      wordsVal s'.mem (s.gpr .r3) (lo s .r4) n < m ∧
      wordsVal s'.mem (s.gpr .r3) (lo s .r4) n * 2 ^ (64 * n) % m =
        wordsVal s.mem (s.gpr .r3) (lo s .r5) n * wordsVal s.mem (s.gpr .r3) (lo s .r6) n % m ∧
      Kept n (s.gpr .r3) (lo s .r4) s.mem s'.mem := by
  have h9 := own_le n hM.n9
  refine exec_of_wp (fn_ok hM hp fun u P V₀ O₁ K₁ => ?_)
  have hbu : wordsVal u.mem (s.gpr .r3) (lo s .r6) (mod n m).n < m := by
    rw [show (mod n m).n = n from rfl, O₁.wordsVal (by have := hp.b; simp only [moAt, tmpAt]; omega) (by have := hp.fit; have := hp.a; have := hp.b; omega)]; exact hb
  have hinv : (m * (mod n m).minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [show (mod n m).minv = BitVec.ofNat 64 (minv m) from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (minv_lt m)]
    exact hM.inv
  have en : (mod n m).n = n := rfl
  have hop : WP isa (rmulSel (mod n m) m (own n)) u fun v =>
      wordsVal v.mem (s.gpr .r3) (lo s .r4) (mod n m).n < m ∧
      wordsVal v.mem (s.gpr .r3) (lo s .r4) (mod n m).n * 2 ^ (64 * (mod n m).n) % m =
        wordsVal u.mem (s.gpr .r3) (lo s .r5) (mod n m).n * wordsVal u.mem (s.gpr .r3) (lo s .r6) (mod n m).n % m ∧
      Outs (s.gpr .r3) (opOuts (mod n m) (own n) (lo s .r4)) u.mem v.mem ∧ Kp (.r6 :: opClob) u v := by
    rw [rmulSel_eq]
    split
    · rename_i h4
      have := hp.a
      have := hp.b
      exact rmul4_ok P (lay hM hp) h4 hM.m_lt
        (by simp only [mod, tmpAt]; omega) (by simp only [mod, tmpAt]; omega) hinv hbu
    · rename_i h4
      exact WP.mono (rmul_ok ⟨P.ws, P.r3, P.r4, P.r5, P.r6, V₀ h4, P.m0⟩ (lay hM hp) hM.n9 hinv hbu) fun v ⟨a, b, c, d⟩ => ⟨a, b, c, d.mono (by decide)⟩
  refine WP.mono hop fun v ⟨V, C, O₂, K₂⟩ => ⟨abi_of_kp (K₁.trans (K₂.mono (by decide))), (K₁.trans (K₂.mono (by decide))).gpr,
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
  refine exec_of_wp (fn_ok hM hp fun u P V₀ O₁ K₁ => ?_)
  have ha := O₁.wordsVal (d := lo s .r5) (k := n) (by have := hp.a; simp only [moAt, tmpAt]; omega)
    (by have := hp.fit; have := hp.a; have := hp.b; omega)
  have hb' := O₁.wordsVal (d := lo s .r6) (k := n) (by have := hp.b; simp only [moAt, tmpAt]; omega)
    (by have := hp.fit; have := hp.a; have := hp.b; omega)
  have hop : WP isa (.block (if n ≤ 4 then add4 n m else add (mod n m) (own n))) u fun v =>
      wordsVal v.mem (s.gpr .r3) (lo s .r4) (mod n m).n =
        (wordsVal u.mem (s.gpr .r3) (lo s .r5) (mod n m).n + wordsVal u.mem (s.gpr .r3) (lo s .r6) (mod n m).n) % m ∧
      Outs (s.gpr .r3) (opOuts (mod n m) (own n) (lo s .r4)) u.mem v.mem ∧ Kp fnClob u v := by
    split
    · rename_i h4
      have := hp.o; have := hp.a; have := hp.b; have := hM.n1
      exact WP.mono (add4_ok ⟨P.ws, P.r4, P.r5, P.r6, hM.n1, h4, by omega, by omega, by omega⟩ hM.m_lt
        (by rw [ha, hb']; exact hab)) fun v ⟨V, O₂, K₂⟩ =>
          ⟨V, Outs.of_outside O₂ (by simp [opOuts, mod]), K₂.mono (by decide)⟩
    · rename_i h4
      exact WP.mono (add_ok (M := mod n m) ⟨P.ws, P.r3, P.r4, P.r5, P.r6, V₀ h4, P.m0⟩ (lay hM hp)
        (by simp only [mod]; rw [ha, hb']; exact hab)) fun v ⟨V, O₂, K₂⟩ => ⟨V, O₂, K₂.mono (by decide)⟩
  refine WP.mono hop fun v ⟨V, O₂, K₂⟩ => ⟨abi_of_kp (K₁.trans K₂), (K₁.trans K₂).gpr, ?_, kept_of hM O₁ O₂⟩
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
  refine exec_of_wp (fn_ok hM hp fun u P V₀ O₁ K₁ => ?_)
  have ha' := O₁.wordsVal (d := lo s .r5) (k := n) (by have := hp.a; simp only [moAt, tmpAt]; omega)
    (by have := hp.fit; have := hp.a; have := hp.b; omega)
  have hb' := O₁.wordsVal (d := lo s .r6) (k := n) (by have := hp.b; simp only [moAt, tmpAt]; omega)
    (by have := hp.fit; have := hp.a; have := hp.b; omega)
  have hop : WP isa (.block (if n ≤ 4 then sub4 n m else sub (mod n m) (own n))) u fun v =>
      wordsVal v.mem (s.gpr .r3) (lo s .r4) (mod n m).n =
        (wordsVal u.mem (s.gpr .r3) (lo s .r5) (mod n m).n + m - wordsVal u.mem (s.gpr .r3) (lo s .r6) (mod n m).n) % m ∧
      Outs (s.gpr .r3) (opOuts (mod n m) (own n) (lo s .r4)) u.mem v.mem ∧ Kp fnClob u v := by
    split
    · rename_i h4
      have := hp.o; have := hp.a; have := hp.b; have := hM.n1
      exact WP.mono (sub4_ok ⟨P.ws, P.r4, P.r5, P.r6, hM.n1, h4, by omega, by omega, by omega⟩ hM.m_lt
        (by rw [ha']; exact ha) (by rw [hb']; exact hb)) fun v ⟨V, O₂, K₂⟩ =>
          ⟨V, Outs.of_outside O₂ (by simp [opOuts, mod]), K₂.mono (by decide)⟩
    · rename_i h4
      exact WP.mono (sub_ok (M := mod n m) ⟨P.ws, P.r3, P.r4, P.r5, P.r6, V₀ h4, P.m0⟩ (lay hM hp)
        (by simp only [mod]; rw [ha']; exact ha) (by simp only [mod]; rw [hb']; exact hb))
        fun v ⟨V, O₂, K₂⟩ => ⟨V, O₂, K₂.mono (by decide)⟩
  refine WP.mono hop fun v ⟨V, O₂, K₂⟩ => ⟨abi_of_kp (K₁.trans K₂), (K₁.trans K₂).gpr, ?_, kept_of hM O₁ O₂⟩
  have en : (mod n m).n = n := rfl
  rw [en] at V; rw [V, ha', hb']

end VG.Proof.Weierstrass.PPC64LE.Mont
