import VerifiedGarbage.Impl.Weierstrass.Arm.Mont
import VerifiedGarbage.Proof.Mont.Arm.Ops
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.TCB.Arm.Target

/-!
# Montgomery arithmetic modulo a curve's `p` or `n`, as functions, on 32-bit ARM

`fn n m op` (`Impl/Weierstrass/Arm/Mont.lean`), from a state `Pre n m`
(`ws`, `o`, `a` and `b` in `r0`–`r3`, the working space the only region, the
numbers below the own working space and the operands below `m`), runs the
entry (`entry_ok`): `r12 = ws`, the callee-saved registers saved, the
pointers to the numbers in `r1`, `r10` and `r11` (`Ptrs`) and the modulus
stored (`ModOkW`); then the operation, and the registers restored
(`fn_ok`). The function restores the callee-saved registers, keeps `sp` and
`lr` (`abiPreserved`), and changes the memory only at `[o]` and in its own
working space (`Kept`).
-/

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_reg dpVal)

/-- What the functions need of the modulus `m` of `n` words. -/
structure ModOk (n m : Nat) : Prop where
  n3 : 3 ≤ n
  n9 : n ≤ 9
  m_lt : m < 2 ^ (64 * n)
  inv : (m * minv m + 1) % 2 ^ 64 = 0
  red : (mod n m).ok m = true

/-- The precondition, on the registers. -/
structure Pre (n m : Nat) (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = [⟨State.addr (s.gpr .r0), 8192⟩]
  fit : (s.gpr .r0).toNat + 8192 ≤ 2 ^ 32
  o : (s.gpr .r1).toNat + 8 * n ≤ own n
  a : (s.gpr .r2).toNat + 8 * n ≤ own n
  b : (s.gpr .r3).toNat + 8 * n ≤ own n

/-- The memory changes only at `[o]` and in the own working space. -/
def Kept (n : Nat) (base : Addr) (o : Nat) (m m' : Mem) : Prop :=
  Outs base [(o, 8 * n), (own n, 64 * n)] m m'

theorem own_le (n : Nat) (h : n ≤ 9) : own n + 64 * n = 4096 := by
  simp only [own, Spec.Weierstrass.Mont.ownAt, Spec.Weierstrass.Mont.ownBytes]; omega

theorem saves_off (n : Nat) : ∀ p ∈ saves n, saveAt n ≤ p.2 ∧ p.2 + 4 ≤ saveAt n + 32 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have : q.2 + 4 ≤ 32 := (by decide : ∀ q ∈ savedRegs, q.2 + 4 ≤ 32) q hq
  dsimp only; omega

theorem saves_pairwise (n : Nat) : (saves n).Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  rw [saves, List.pairwise_map]
  exact List.Pairwise.imp (fun h => by dsimp only; omega)
    (by decide : savedRegs.Pairwise fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2)

theorem saves_regs (n : Nat) : (saves n).map Prod.fst = savedRegs.map Prod.fst := by
  rw [saves, List.map_map]; rfl

theorem saves_mem (n : Nat) {r : Reg} {d : Nat} (h : (r, d) ∈ savedRegs) : (r, saveAt n + d) ∈ saves n :=
  List.mem_map_of_mem (f := fun p : Reg × Nat => (p.1, saveAt n + p.2)) h

theorem saves_nodup (n : Nat) : ((saves n).map Prod.fst).Nodup := by rw [saves_regs]; decide

theorem saves_r12 (n : Nat) : ∀ p ∈ saves n, p.1 ≠ .r12 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (by decide : ∀ q ∈ savedRegs, q.1 ≠ .r12) q hq

/-- What the entry leaves, with `[b]` at `rb`: the working space, the
modulus, the pointers to the numbers, the registers saved, `r10` and `r11`
as they were, and the memory but the own working space unchanged. -/
structure Entered (n m : Nat) (rb : Reg) (s s₁ : State) : Prop where
  scr : Scr s₁ (State.addr (s.gpr .r0)) 4096
  mod : ModOkW (mod n m) 4096 m s₁.mem (State.addr (s.gpr .r0))
  r12 : s₁.gpr .r12 = s.gpr .r0
  ra : s₁.gpr .r1 = s₁.gpr .r12 + BitVec.ofNat 32 (s.gpr .r2).toNat
  rb : s₁.gpr rb = s₁.gpr .r12 + BitVec.ofNat 32 (s.gpr .r3).toNat
  ro : s₁.gpr .lr = s₁.gpr .r12 + BitVec.ofNat 32 (s.gpr .r1).toNat
  keep : ∀ r ∈ [Reg.r10, .r11], s₁.gpr r = s.gpr r
  saved : ∀ p ∈ saves n, s₁.mem.readW (off (State.addr (s.gpr .r0)) p.2) 32 = s.gpr p.1
  mem : Outs (State.addr (s.gpr .r0)) [(own n, 64 * n)] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp

end VG.Proof.Weierstrass.Arm.Mont

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp op2_reg dpVal)

/-- Changes within ranges are within any ranges that contain them. -/
theorem Outs.sub {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs base rs' m m' :=
  fun x hx => h x fun r hr => by
    obtain ⟨r', hr', h1, h2⟩ := hs r hr
    have := hx r' hr'
    omega

theorem minv_lt (m : Nat) : minv m < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem sum_reg (x y : BitVec 32) : x + y = x + BitVec.ofNat 32 y.toNat := by simp

theorem entry_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s) {rb : Reg}
    (hrb : rb ∉ [.r1, .r3, .r10, .r11, .r12, .lr]) :
    WP isa (.block (entry n m rb)) s (Entered n m rb s) := by
  have hn3 := hM.n3
  have hn9 := hM.n9
  have hown := own_le n hn9
  have hfit := hp.fit
  simp only [entry, List.cons_append, List.append_assoc]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have hs₁ : Scr s₁ (State.addr (s.gpr .r0)) 4096 := ⟨by rw [u₁.gpr], ⟨8192, by decide, by decide,
    by rw [u₁.wr, hp.wr]; simp⟩, by rw [VG.Proof.X25519.Arm.addr_toNat]; omega, by decide⟩
  -- The saves.
  refine VG.Proof.X25519.Arm.WP.append (strs_ok hs₁ (saves n) (fun p hp' => by
    have := saves_off n p hp'; simp only [saveAt, moAt, tmpAt] at this; omega) (saves_pairwise n))
    fun s₂ ⟨K₂, O₂, V₂⟩ => ?_
  have hs₂ := hs₁.of_rest K₂ (by decide)
  -- The modulus.
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs₂ (o := moAt n) (n := n) (by
    simp only [moAt, tmpAt]; omega) hM.m_lt) fun s₃ ⟨V₃, K₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_rest K₃ (by decide)
  -- The pointers.
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  have hrb' : ∀ r ∈ [Reg.r1, .r3, .r10, .r11, .r12, .lr], rb ≠ r := fun r hr h => hrb (h ▸ hr)
  have hb1 : rb ≠ .r1 := hrb' .r1 (by simp)
  have hb10 : rb ≠ .r10 := hrb' .r10 (by simp)
  have hb11 : rb ≠ .r11 := hrb' .r11 (by simp)
  have hb12 : rb ≠ .r12 := hrb' .r12 (by simp)
  have hblr : rb ≠ .lr := hrb' .lr (by simp)
  have K₆ : Rest [.lr, .r1, rb] s₃ s₆ :=
    (u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp)))
  have g₃ : ∀ r, r ≠ .r12 → r ≠ .r4 → s₃.gpr r = s.gpr r := fun r h12 h4 => by
    rw [K₃.gpr _ (by simp [h4]), K₂.gpr _ (by simp), u₁.other _ h12]
  have w₃ : s₃.gpr .r12 = s.gpr .r0 := by rw [K₃.gpr _ (by decide), K₂.gpr _ (by simp), u₁.gpr]
  have w₆ : s₆.gpr .r12 = s.gpr .r0 := by rw [K₆.gpr _ (by simp [Ne.symm hb12]), w₃]
  have m₆ : s₆.mem = s₃.mem := by rw [u₆.mem, u₅.mem, u₄.mem]
  refine ⟨hs₃.of_rest K₆ (by simp [Ne.symm hb12]), ⟨by simp only [mod]; omega,
    by simp only [mod, moAt, tmpAt]; omega, by simp only [mod, tmpAt]; omega,
    .inr (by simp only [mod, moAt]; omega), by rw [m₆]; exact V₃,
    by rw [show (mod n m).minv = BitVec.ofNat 64 (minv m) from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (minv_lt m)]; exact hM.inv, hM.red⟩, w₆, ?_, ?_, ?_, fun r hr => ?_, fun p hp' => ?_, ?_,
    by rw [u₆.rd, u₅.rd, u₄.rd, K₃.rd, K₂.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, K₃.wr, K₂.wr, u₁.wr],
    by rw [u₆.sp, u₅.sp, u₄.sp, K₃.sp, K₂.sp, u₁.sp]⟩
  · rw [u₆.other _ hb1.symm, u₅.gpr, dpVal, w₆, u₄.other _ (by decide), w₃,
      u₄.other _ (by decide), g₃ _ (by decide) (by decide), sum_reg]
  · rw [u₆.gpr, dpVal, w₆, u₅.other _ (by decide), u₄.other _ (by decide), w₃, u₅.other _ (by decide),
      u₄.other _ (by decide), g₃ _ (by decide) (by decide), sum_reg]
  · rw [u₆.other _ hblr.symm, u₅.other _ (by decide), u₄.gpr, dpVal, w₆, w₃,
      g₃ _ (by decide) (by decide), sum_reg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [u₆.other _ hb10.symm, u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide) (by decide)]
    · rw [u₆.other _ hb11.symm, u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide) (by decide)]
  · have := saves_off n p hp'
    rw [← u₁.other p.1 (saves_r12 n p hp'), ← V₂ p hp', m₆]
    refine Mem.readW_congr fun i hi => O₃ _ ?_
    simp only [moAt, saveAt, tmpAt] at this ⊢
    rw [ofs_off _ (by omega)]
    omega
  · have hsv : ∀ p ∈ saves n, own n ≤ p.2 ∧ p.2 + 4 ≤ own n + 64 * n := fun p hp' => by
      have := saves_off n p hp'; simp only [saveAt, moAt, tmpAt] at this; omega
    rw [m₆]
    refine (Outs.sub (rs := (saves n).map fun p => (p.2, 4)) (m' := s₂.mem) ?_ ?_).trans
      (Outs.sub (rs := [(moAt n, 8 * n)]) ?_ ?_)
    · rw [← u₁.mem]; exact O₂
    · intro r hr
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr
      exact ⟨_, List.mem_singleton_self _, (hsv p hp').1, (hsv p hp').2⟩
    · exact Outs.of_outside O₃ (List.mem_singleton_self _)
    · intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      exact ⟨_, List.mem_singleton_self _, by simp only [moAt, tmpAt]; omega, by simp only [moAt, tmpAt]; omega⟩

/-- The function of an operation that, from the entry's state, keeps what
an operation keeps (`OpKeep`) and leaves memory satisfying `R`: the
callee-saved registers and `sp` are those of the entry (`r10` and `r11`
never change), `r12` is `ws`, the memory changed only at `[o]` and in the
own working space, and `R` holds. -/
theorem fn_ok {n m : Nat} (hM : ModOk n m) {rb : Reg} (hrb : rb ∉ [.r1, .r3, .r10, .r11, .r12, .lr])
    {op : Prog isa} {R : Mem → Prop} {s : State} (hp : Pre n m s)
    (hop : ∀ s₁, Entered n m rb s s₁ → WP isa op s₁ fun s₂ =>
      OpKeep (mod n m) (State.addr (s.gpr .r0)) (own n) (s.gpr .r1).toNat s₁ s₂ ∧ R s₂.mem) :
    WP isa (fn n m rb op) s fun s' => abiPreserved s s' ∧
      Kept n (State.addr (s.gpr .r0)) (s.gpr .r1).toNat s.mem s'.mem ∧ R s'.mem ∧
      s'.gpr .r12 = s.gpr .r0 := by
  have hn3 := hM.n3
  have hn9 := hM.n9
  have hown := own_le n hn9
  have ho := hp.o
  refine WP.seq (WP.mono (entry_ok hM hp hrb) fun s₁ E => ?_)
  refine WP.seq (WP.mono (hop s₁ E) fun s₂ ⟨K, hR⟩ => ?_)
  have hs₂ := E.scr.of_rest K.rest (by decide)
  have hsv : ∀ p ∈ saves n, saveAt n ≤ p.2 ∧ p.2 + 4 ≤ saveAt n + 32 := saves_off n
  have hsa : saveAt n + 32 ≤ 4096 := by simp only [saveAt, moAt, tmpAt]; omega
  refine WP.mono (ldrs_ok hs₂ (saves n) (fun p hp' => by have := hsv p hp'; omega) (saves_nodup n)
    (saves_r12 n)) fun s₃ ⟨M₃, K₃, V₃⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_, by rw [M₃]; exact hR, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    have hsave : ∀ p ∈ saves n, s₃.gpr p.1 = s.gpr p.1 := fun p hp' => by
      have := hsv p hp'
      rw [V₃ p hp', ← E.saved p hp']
      refine Unch.readW32 (VG.Proof.Weierstrass.Arm.Outs.unch K.mem) (fun w hw => ?_) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp only [mod, saveAt, moAt, tmpAt, accLen, digits] at this hw ⊢
      rcases hw with rfl | rfl | rfl <;> dsimp only <;> omega
    have hkeep : ∀ r ∈ [Reg.r10, .r11], s₃.gpr r = s.gpr r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [K₃.gpr _ (by rw [saves_regs]; decide), K.rest.gpr _ (by decide), E.keep _ (by simp)]
      · rw [K₃.gpr _ (by rw [saves_regs]; decide), K.rest.gpr _ (by decide), E.keep _ (by simp)]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsave _ (saves_mem n (by decide : (Reg.r4, 0) ∈ savedRegs))
    · exact hsave _ (saves_mem n (by decide : (Reg.r5, 4) ∈ savedRegs))
    · exact hsave _ (saves_mem n (by decide : (Reg.r6, 8) ∈ savedRegs))
    · exact hsave _ (saves_mem n (by decide : (Reg.r7, 12) ∈ savedRegs))
    · exact hsave _ (saves_mem n (by decide : (Reg.r8, 16) ∈ savedRegs))
    · exact hsave _ (saves_mem n (by decide : (Reg.r9, 20) ∈ savedRegs))
    · exact hkeep _ (by decide)
    · exact hkeep _ (by decide)
    · exact hsave _ (saves_mem n (by decide : (Reg.lr, 24) ∈ savedRegs))
  · rw [K₃.sp, K.rest.sp, E.sp]
  · rw [M₃]
    refine (Outs.sub (rs := [(own n, 64 * n)]) E.mem fun r hr => ?_).trans
      (Outs.sub K.mem fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, Nat.le_refl _, by simp [mod]⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simp only [mod, tmpAt]; omega,
          by simp only [mod, tmpAt]; omega⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _,
          by simp only [mod, accLen, digits]; omega⟩
  · rw [K₃.gpr _ (by rw [saves_regs]; decide), K.rest.gpr _ (by decide), E.r12]

/-- The operations' layout: the numbers below the own working space, its
accumulator, temporary area and modulus apart. -/
theorem opLay {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s) :
    OpLay (mod n m) 4096 (own n) (s.gpr .r1).toNat (s.gpr .r2).toNat (s.gpr .r3).toNat := by
  have hown := own_le n hM.n9
  have := hM.n3; have := hp.o; have := hp.a; have := hp.b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [mod, accLen, digits, moAt, tmpAt] <;> omega

/-- The entry's numbers are those of `s`. -/
theorem Entered.val {n m : Nat} (hM : ModOk n m) {rb : Reg} {s s₁ : State} (E : Entered n m rb s s₁) {d : Nat}
    (hd : d + 8 * n ≤ own n) : wordsVal s₁.mem (State.addr (s.gpr .r0)) d n =
      wordsVal s.mem (State.addr (s.gpr .r0)) d n :=
  Outs.wordsVal E.mem (fun r hr => by rw [List.mem_singleton] at hr; subst hr; omega)
    (by have := own_le n hM.n9; omega)

/-- The pointers of the entry. -/
def Entered.ptrs {n m : Nat} {rb : Reg} {s s₁ : State} (E : Entered n m rb s s₁) :
    Ptrs s₁ .r1 rb .lr 0 0 0 (s.gpr .r2).toNat (s.gpr .r3).toNat (s.gpr .r1).toNat :=
  ⟨_, _, _, E.ra, E.rb, E.ro, rfl, rfl, rfl⟩

/-- `vg_<curve>_mul_mod_<p|n>`: `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mulFn_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s)
    (hb : wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n < m) :
    WP isa (mulFn n m) s fun s' => abiPreserved s s' ∧
      Kept n (State.addr (s.gpr .r0)) (s.gpr .r1).toNat s.mem s'.mem ∧
      (wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n < m ∧
      wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n * 2 ^ (64 * n) % m =
        wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n *
          wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n % m) ∧
      s'.gpr .r12 = s.gpr .r0 := by
  refine fn_ok (R := fun mem => wordsVal mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n < m ∧
    wordsVal mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n * 2 ^ (64 * n) % m =
      wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n *
        wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n % m) hM (by decide) hp fun s₁ E => ?_
  refine WP.mono (mulR_ok E.scr E.mod (opLay hM hp) E.ptrs (by decide) (by decide) (by decide)
    (by change wordsVal _ _ _ n < m; rw [E.val hM hp.b]; exact hb)) fun s₂ ⟨K, V, C⟩ => ⟨K, V, ?_⟩
  have e : (mod n m).n = n := rfl
  rw [e, E.val hM hp.a, E.val hM hp.b] at C
  exact C

/-- `vg_<curve>_add_mod_<p|n>`: `[o] = [a] + [b] mod m`. -/
theorem addFn_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s)
    (hab : wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n +
      wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n < 2 * m) :
    WP isa (addFn n m) s fun s' => abiPreserved s s' ∧
      Kept n (State.addr (s.gpr .r0)) (s.gpr .r1).toNat s.mem s'.mem ∧
      wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n =
        (wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n +
          wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n) % m ∧
      s'.gpr .r12 = s.gpr .r0 := by
  refine fn_ok (R := fun mem => wordsVal mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n =
    (wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n +
      wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n) % m) hM (by decide) hp fun s₁ E => ?_
  refine WP.mono (addR_ok E.scr E.mod (opLay hM hp) E.ptrs (by decide) (by decide) (by decide)
    (by change wordsVal _ _ _ n + wordsVal _ _ _ n < 2 * m; rw [E.val hM hp.a, E.val hM hp.b]
        exact hab)) fun s₂ ⟨K, V⟩ => ⟨K, ?_⟩
  have e : (mod n m).n = n := rfl
  rw [e, E.val hM hp.a, E.val hM hp.b] at V
  exact V

/-- `vg_<curve>_sub_mod_<p|n>`: `[o] = [a] - [b] mod m`. -/
theorem subFn_ok {n m : Nat} (hM : ModOk n m) {s : State} (hp : Pre n m s)
    (ha : wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n < m)
    (hb : wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n < m) :
    WP isa (subFn n m) s fun s' => abiPreserved s s' ∧
      Kept n (State.addr (s.gpr .r0)) (s.gpr .r1).toNat s.mem s'.mem ∧
      wordsVal s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n =
        (wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n + m -
          wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n) % m ∧
      s'.gpr .r12 = s.gpr .r0 := by
  refine fn_ok (R := fun mem => wordsVal mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat n =
    (wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r2).toNat n + m -
      wordsVal s.mem (State.addr (s.gpr .r0)) (s.gpr .r3).toNat n) % m) hM (by decide) hp fun s₁ E => ?_
  refine WP.mono (subR_ok E.scr E.mod (opLay hM hp) E.ptrs (by decide) (by decide) (by decide)
    (by change wordsVal _ _ _ n < m; rw [E.val hM hp.a]; exact ha)
    (by change wordsVal _ _ _ n < m; rw [E.val hM hp.b]; exact hb)) fun s₂ ⟨K, V⟩ => ⟨K, ?_⟩
  have e : (mod n m).n = n := rfl
  rw [e, E.val hM hp.a, E.val hM hp.b] at V
  exact V

end VG.Proof.Weierstrass.Arm.Mont
