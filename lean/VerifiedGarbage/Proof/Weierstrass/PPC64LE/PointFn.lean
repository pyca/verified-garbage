module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointFprog
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.RangeCover

/-!
# Complete point addition and doubling as functions, on PPC64LE: correctness

`fn S dbl` (`Impl/Weierstrass/PPC64LE/Point.lean`), from a state that its
precondition describes (`PrePt`: the working space at `r3`, writable, and
every coordinate it reads below the prime), returns with the callee-saved
registers, `sp` and `lr` kept, the registers but `fnClob` kept, the memory
changed only at `O` and in the own working space, and `O`'s coordinates
below the prime, standing for `rcbAdd` of what the constants and the
operands stand for (`fn_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)

/-- The numbers of the layout, for `omega`. -/
theorem lay_nums {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) :
    ownAt k + 64 + 6 * elemBytes k = own k ∧ own k + 64 * k = 4096 ∧ elemBytes k = 8 * k ∧
    b3At k + elemBytes k = ownAt k ∧ aAt k + elemBytes k = b3At k ∧
    qAt k + 3 * elemBytes k = aAt k ∧ pAt k + 3 * elemBytes k = qAt k ∧
    oAt k + 3 * elemBytes k = pAt k ∧ 1000 ≤ oAt k ∧ ownAt k % 8 = 0 := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  all_goals decide +kernel

/-- The slots the function reads first lie below its own working space. -/
theorem enc_rIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ x ∈ rIds, enc k dbl x + 8 * k ≤ ownAt k := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  all_goals cases dbl <;> decide +kernel

/-- The slots `enc` gives are laid out as the program needs. -/
theorem enc_lay {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) : LayR k 17 wIds (enc k dbl) := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  all_goals cases dbl <;> exact ⟨by decide +kernel, by decide +kernel⟩

/-- Those it writes lie apart from the saved `lr` and within `O` or the own
working space. -/
theorem enc_wIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ w ∈ wIds, (enc k dbl w + 8 * k ≤ ownAt k ∨ ownAt k + 8 ≤ enc k dbl w) ∧
      ((oAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ pAt k) ∨
        (ownAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ 4096)) := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  all_goals cases dbl <;> decide +kernel

/-- The precondition of the function, on the state: the working space at
`r3`, its `8192` bytes writable, and the numbers it reads below `m`. -/
structure PrePt (k m : Nat) (dbl : Bool) (s : State) : Prop where
  wr : s.wr = [⟨s.gpr .r3, 8192⟩]
  fit : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 64
  k3 : 3 ≤ k
  k6 : k ≤ 6
  lt : ∀ x ∈ rIds, wordsVal s.mem (s.gpr .r3) (enc k dbl x) k < m

/-- The environment of the entry: what the numbers of the slots stand for. -/
def E₀ (k m : Nat) [NeZero m] (dbl : Bool) (s : State) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal s.mem (s.gpr .r3) (enc k dbl x) k)

theorem rIds_lt : ∀ x ∈ rIds, x < 17 := by decide

/-- A function of field operations `ops` that write only the result and the
temporaries (`OpsOk`): the registers but `fnClob`, `sp` and `lr` kept, the
memory changed only at `O` and in the own working space, and `O`'s
coordinates below the prime, standing for what `ops` computes from what the
slots stand for. -/
theorem fnOps_ok {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m) (hodd : S.m % 2 = 1)
    {dbl : Bool} {ops : List FOp} (hO : OpsOk ops) {s : State} (hp : PrePt S.k S.m dbl s) :
    WP isa (Point.fnOps S dbl ops) s fun s' => abiPreserved s s' ∧ (∀ r, r ∉ fnClob → s'.gpr r = s.gpr r) ∧
      Outs (s.gpr .r3) [(oAt S.k, 3 * elemBytes S.k), (ownAt S.k, 4096 - ownAt S.k)] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem (s.gpr .r3) (enc S.k dbl j) S.k < S.m) ∧
      (toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (s.gpr .r3) (enc S.k dbl 0) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (s.gpr .r3) (enc S.k dbl 1) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (s.gpr .r3) (enc S.k dbl 2) S.k)) =
        (runOps ops (E₀ S.k S.m dbl s) 0, runOps ops (E₀ S.k S.m dbl s) 1,
          runOps ops (E₀ S.k S.m dbl s) 2) := by
  have hl := lay_nums hp.k3 hp.k6
  have hR := enc_rIds hp.k3 hp.k6 dbl
  have hW := enc_wIds hp.k3 hp.k6 dbl
  have hfit := hp.fit
  have hs : Ws s (s.gpr .r3) 4096 := ⟨⟨8192, by decide, by rw [hp.wr]; simp, hfit⟩, by decide⟩
  have h3 : At s (s.gpr .r3) .r3 0 := by simp [At, off]
  rw [Point.fnOps]
  -- The entry: `lr` saved.
  have hent : WP isa (.block (entry S.k)) s fun s₁ => Kp fnClob s s₁ ∧
      s₁.mem = s.mem.writeW (off (s.gpr .r3) (saveAt S.k)) s.lr := by
    refine wp_step exec_mflr (wp_step (std_ok (hs.write _ _) (h3.write _) (by decide) (d := saveAt S.k)
      (by simp only [saveAt]; omega) (by simp only [saveAt]; omega)) (WP.block_nil ?_))
    simp only [write_gpr, ite_true, Nat.zero_add]
    exact ⟨(Kp.write s _ (by decide)).trans (Kp.store _ _ _), rfl⟩
  refine WP.seq (WP.mono hent fun s₁ ⟨K₁, m₁⟩ => ?_)
  have O₁ := writeW_outside s.mem (s.gpr .r3) (d := saveAt S.k) s.lr (by simp only [saveAt]; omega)
  rw [← m₁] at O₁
  have hI : InvR S.k 17 (enc S.k dbl) (s.gpr .r3) S.m rIds (E₀ S.k S.m dbl s) s₁ := by
    have heq : ∀ x ∈ rIds, wordsVal s₁.mem (s.gpr .r3) (enc S.k dbl x) S.k =
        wordsVal s.mem (s.gpr .r3) (enc S.k dbl x) S.k := fun x hx =>
      O₁.wordsVal (by have := hR x hx; simp only [saveAt]; omega) (by have := hR x hx; omega)
    exact ⟨⟨by rw [K₁.g], by rw [K₁.wr, hp.wr]; simp, hfit⟩, rIds_lt,
      fun x hx => by rw [heq x hx]; exact hp.lt x hx, fun x hx => by rw [heq x hx]; rfl⟩
  refine WP.seq (WP.mono (opsR_ok hM rfl (enc_lay hp.k3 hp.k6 dbl) (unitMod_pow_two hodd _) hO hI)
    fun s₂ ⟨K, I₂⟩ => ?_)
  -- The restore.
  have hs₂ : Ws s₂ (s.gpr .r3) 4096 := ⟨⟨8192, by decide, by rw [K.wr, K₁.wr, hp.wr]; simp, hfit⟩, by decide⟩
  have h3₂ : At s₂ (s.gpr .r3) .r3 0 := by rw [At, K.gpr _ (by decide), K₁.g]; exact h3
  have hsv : word s₂.mem (s.gpr .r3) (saveAt S.k) = s.lr := by
    rw [Outs.word K.mem (fun r hr => ?_) (by simp only [saveAt]; omega), m₁, word_writeW_self]
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨x, hx, rfl⟩ | rfl
    · rcases (hW x hx).1 with h | h <;> [exact .inr (by simp only [saveAt]; omega);
        exact .inl (by simp only [saveAt]; omega)]
    · exact .inl (by simp only [saveAt]; omega)
  refine wp_step (ld_ok hs₂ h3₂ (by decide) (by simp only [saveAt]; omega) (d := saveAt S.k)
    (by simp only [saveAt]; omega)) (wp_step exec_mtlr (WP.block_nil ?_))
  simp only [write_gpr, ite_true, Nat.zero_add, hsv]
  refine ⟨⟨fun r hr => ?_, ?_, rfl⟩, fun r hr => ?_, ?_, fun j hj => ?_, ?_⟩
  · have hr' : r ∉ fnClob := fun h => absurd h ((by decide : ∀ r ∈ preserved, r ∉ fnClob) r hr)
    have : r ≠ .r0 := fun h => hr' (h ▸ by decide)
    simp only [write_gpr, this, ite_false]
    rw [K.gpr r hr', K₁.gpr r hr']
  · simp only [write_sp]; rw [K.sp, K₁.sp]
  · have : r ≠ .r0 := fun h => hr (h ▸ by decide)
    simp only [this, ite_false]
    rw [K.gpr r hr, K₁.gpr r hr]
  · simp only [write_mem]
    refine (Outs.cover (rs := [(saveAt S.k, 8)]) ?_ fun r hr => ?_).trans (Outs.cover K.mem fun r hr => ?_)
    · rw [m₁]; exact Outs.of_outside (writeW_outside s.mem _ s.lr (by simp only [saveAt]; omega))
        (List.mem_singleton_self _)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simp only [saveAt]; omega,
        by simp only [saveAt]; omega⟩
    · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
      rcases hr with ⟨x, hx, rfl⟩ | rfl
      · rcases (hW x hx).2 with h | h
        · exact ⟨_, List.mem_cons_self, h.1, by dsimp only; omega⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.1, by dsimp only; omega⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by dsimp only; omega, by dsimp only; omega⟩
  · simp only [write_mem]; exact I₂.lt j (hO.outs j hj)
  · simp only [write_mem]
    rw [I₂.val 0 (hO.outs 0 (by decide)), I₂.val 1 (hO.outs 1 (by decide)),
      I₂.val 2 (hO.outs 2 (by decide))]

/-- `fnOps_ok` for the complete addition: `O`'s coordinates stand for
`rcbAdd` of what the constants and the operands stand for. -/
theorem fn_ok {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m) (hodd : S.m % 2 = 1)
    {dbl : Bool} {s : State} (hp : PrePt S.k S.m dbl s) :
    WP isa (Point.fn S dbl) s fun s' => abiPreserved s s' ∧ (∀ r, r ∉ fnClob → s'.gpr r = s.gpr r) ∧
      Outs (s.gpr .r3) [(oAt S.k, 3 * elemBytes S.k), (ownAt S.k, 4096 - ownAt S.k)] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem (s.gpr .r3) (enc S.k dbl j) S.k < S.m) ∧
      (toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (s.gpr .r3) (enc S.k dbl 0) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (s.gpr .r3) (enc S.k dbl 1) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (s.gpr .r3) (enc S.k dbl 2) S.k)) =
        VG.Proof.Weierstrass.rcbAdd (E₀ S.k S.m dbl s 9) (E₀ S.k S.m dbl s 10) (E₀ S.k S.m dbl s 3)
          (E₀ S.k S.m dbl s 4) (E₀ S.k S.m dbl s 5) (E₀ S.k S.m dbl s 6) (E₀ S.k S.m dbl s 7)
          (E₀ S.k S.m dbl s 8) :=
  WP.mono (fnOps_ok hM hodd rcbIds_opsOk hp) fun _ ⟨A, G, O, L, V⟩ =>
    ⟨A, G, O, L, V.trans (rcb_run rcbIds_apart _)⟩

end VG.Proof.Weierstrass.PPC64LE.Point
