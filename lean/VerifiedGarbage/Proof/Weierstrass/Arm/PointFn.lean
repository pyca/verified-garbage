module

public import VerifiedGarbage.Proof.Weierstrass.Arm.PointFprog
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves

/-!
# Complete point addition and doubling as functions, on 32-bit ARM: correctness

`fn S dbl` (`Impl/Weierstrass/Arm/Point.lean`), from a state that its
precondition describes (`PrePt`: the working space at `r0`, writable, and
every coordinate it reads below the prime), returns with the callee-saved
registers and `sp` kept, `r12 = ws`, the memory changed only at `O` and in
the own working space, and `O`'s coordinates below the prime, standing for
`rcbAdd` of what the constants and the operands stand for (`fn_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
  VG.Proof.Weierstrass.Arm.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov op2_reg wp_str wp_ldr)

/-- The numbers of the layout, for `omega_arith`. -/
theorem lay_nums {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) :
    Impl.Weierstrass.Point.ownAt k + 64 + 6 * Impl.Weierstrass.Point.elemBytes k = own k ∧ own k + 64 * k = 4096 ∧ Impl.Weierstrass.Point.elemBytes k = 8 * k ∧
    Impl.Weierstrass.Point.b3At k + Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.ownAt k ∧ Impl.Weierstrass.Point.aAt k + Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.b3At k ∧
    Impl.Weierstrass.Point.qAt k + 3 * Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.aAt k ∧ Impl.Weierstrass.Point.pAt k + 3 * Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.qAt k ∧
    Impl.Weierstrass.Point.oAt k + 3 * Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.pAt k ∧ 1000 ≤ Impl.Weierstrass.Point.oAt k := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  all_goals decide +kernel

/-- The slots the function reads first lie below its own working space. -/
theorem enc_rIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ x ∈ rIds, enc k dbl x + 8 * k ≤ Impl.Weierstrass.Point.ownAt k := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  all_goals cases dbl <;> decide +kernel

/-- The slots `enc` gives are laid out as the program needs, and those it
writes lie apart from the saved `lr` and within `O` or the own working
space. -/
theorem enc_lay {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) : LayR k 17 wIds (enc k dbl) := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  all_goals cases dbl <;> exact ⟨by decide +kernel, by decide +kernel⟩

theorem enc_wIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ w ∈ wIds, (enc k dbl w + 8 * k ≤ Impl.Weierstrass.Point.ownAt k ∨ Impl.Weierstrass.Point.ownAt k + 4 ≤ enc k dbl w) ∧
      ((Impl.Weierstrass.Point.oAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ Impl.Weierstrass.Point.pAt k) ∨
        (Impl.Weierstrass.Point.ownAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ 4096)) := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  all_goals cases dbl <;> decide +kernel

/-- The precondition of the function, on the state: the working space at
`r0`, its `8192` bytes writable, and the numbers it reads below `m`. -/
structure PrePt (k m : Nat) (dbl : Bool) (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = [⟨State.addr (s.gpr .r0), 8192⟩]
  fit : (s.gpr .r0).toNat + 8192 ≤ 2 ^ 32
  k3 : 3 ≤ k
  k6 : k ≤ 6
  lt : ∀ x ∈ rIds, wordsVal s.mem (State.addr (s.gpr .r0)) (enc k dbl x) k < m

/-- What the entry leaves: `r12 = ws`, the other registers, `lr` saved, and
the memory but those 4 bytes. -/
structure EnteredPt (k : Nat) (s s₁ : State) : Prop where
  scr : Scr s₁ (State.addr (s.gpr .r0)) 4096
  far : Far s₁ (State.addr (s.gpr .r0)) 8192
  r12 : s₁.gpr .r12 = s.gpr .r0
  keep : ∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp
  mem : Outs (State.addr (s.gpr .r0)) [(Impl.Weierstrass.Point.ownAt k, 4)] s.mem s₁.mem
  saved : s₁.mem.readW (off (State.addr (s.gpr .r0)) (Impl.Weierstrass.Point.ownAt k)) 32 = s.gpr .lr

theorem entry_ok {k m : Nat} {dbl : Bool} {s : State} (hp : PrePt k m dbl s) :
    WP isa (.block (Impl.Weierstrass.Arm.Point.entry k)) s (EnteredPt k s) := by
  have hl := lay_nums hp.k3 hp.k6
  have hfit := hp.fit
  have hown : own k ≤ 4096 := Nat.sub_le _ _
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have hs₁ : Scr s₁ (State.addr (s.gpr .r0)) 4096 := ⟨by rw [u₁.gpr], ⟨8192, by decide, by decide,
    by rw [u₁.wr, hp.wr]; simp⟩, by rw [VG.Proof.X25519.Arm.addr_toNat]; omega_arith, by decide⟩
  refine VG.Proof.X25519.Arm.WP.append (strs_ok hs₁ [(.lr, Impl.Weierstrass.Point.ownAt k)] (by simp; omega_arith) (by simp))
    fun s₂ ⟨K₂, O₂, V₂⟩ => WP.block_nil ?_
  refine ⟨hs₁.of_rest K₂ (by simp), ⟨by rw [K₂.wr, u₁.wr, hp.wr]; simp,
    by rw [VG.Proof.X25519.Arm.addr_toNat]; exact hp.fit⟩, by rw [K₂.gpr _ (by simp), u₁.gpr],
    fun r hr => by rw [K₂.gpr _ (by simp), u₁.other _ hr], by rw [K₂.rd, u₁.rd], by rw [K₂.wr, u₁.wr],
    by rw [K₂.sp, u₁.sp], by rw [← u₁.mem]; simpa using O₂, ?_⟩
  rw [V₂ (.lr, Impl.Weierstrass.Point.ownAt k) (by simp), u₁.other .lr (by decide)]

/-- The environment of the entry: what the numbers of the slots stand for. -/
def E₀ (k m : Nat) [NeZero m] (dbl : Bool) (s : State) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal s.mem (State.addr (s.gpr .r0)) (enc k dbl x) k)

theorem rIds_lt : ∀ x ∈ rIds, x < 17 := by decide

/-- A function of field operations `ops` that write only the result and the
temporaries (`OpsOk`): the callee-saved registers and `sp` kept, `r12 = ws`,
the memory changed only at `O` and in the own working space, and `O`'s
coordinates below the prime, standing for what `ops` computes from what the
slots stand for. -/
theorem fnOps_ok {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m) (hodd : S.m % 2 = 1)
    {dbl : Bool} {ops : List FOp} (hO : OpsOk ops) {s : State} (hp : PrePt S.k S.m dbl s) {u : Bool} :
    WP isa (Impl.Weierstrass.Arm.Point.fnOps S dbl ops u) s fun s' => abiPreserved s s' ∧
      Outs (State.addr (s.gpr .r0)) [(Impl.Weierstrass.Point.oAt S.k, 3 * Impl.Weierstrass.Point.elemBytes S.k),
        (Impl.Weierstrass.Point.ownAt S.k, 4096 - Impl.Weierstrass.Point.ownAt S.k)] s.mem s'.mem ∧
      s'.gpr .r12 = s.gpr .r0 ∧
      (∀ j < 3, wordsVal s'.mem (State.addr (s.gpr .r0)) (enc S.k dbl j) S.k < S.m) ∧
      (toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (State.addr (s.gpr .r0)) (enc S.k dbl 0) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (State.addr (s.gpr .r0)) (enc S.k dbl 1) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (State.addr (s.gpr .r0)) (enc S.k dbl 2) S.k)) =
        (runOps ops (E₀ S.k S.m dbl s) 0, runOps ops (E₀ S.k S.m dbl s) 1,
          runOps ops (E₀ S.k S.m dbl s) 2) := by
  have hl := lay_nums hp.k3 hp.k6
  have hR := enc_rIds hp.k3 hp.k6 dbl
  have hW := enc_wIds hp.k3 hp.k6 dbl
  rw [Impl.Weierstrass.Arm.Point.fnOps]
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ E => ?_)
  have hI : InvR S.k 17 (enc S.k dbl) (State.addr (s.gpr .r0)) S.m rIds (E₀ S.k S.m dbl s) s₁ := by
    have heq : ∀ x ∈ rIds, wordsVal s₁.mem (State.addr (s.gpr .r0)) (enc S.k dbl x) S.k =
        wordsVal s.mem (State.addr (s.gpr .r0)) (enc S.k dbl x) S.k := fun x hx =>
      Outs.wordsVal E.mem (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact .inl (hR x hx)) (by have := hR x hx; omega_arith)
    exact ⟨E.scr, E.far, rIds_lt, fun x hx => by rw [heq x hx]; exact hp.lt x hx,
      fun x hx => by rw [heq x hx]; rfl⟩
  refine WP.seq (WP.mono (opsR_ok hM rfl (enc_lay hp.k3 hp.k6 dbl) (unitMod_pow_two hodd _) hO hI)
    fun s₂ ⟨K, I₂⟩ => ?_)
  refine WP.mono (ldrs_ok I₂.scr [(.lr, Impl.Weierstrass.Point.ownAt S.k)] (by simp; omega_arith) (by simp) (by simp))
    fun s₃ ⟨M₃, K₃, V₃⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_, fun j hj => ?_, ?_⟩
  · -- The callee-saved registers.
    by_cases hlr : r = .lr
    · subst hlr
      rw [V₃ (.lr, Impl.Weierstrass.Point.ownAt S.k) (by simp), ← E.saved]
      refine Unch.readW32 (Outs.unch K.mem) (fun w hw => ?_) (by omega_arith)
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
      rcases hw with ⟨x, hx, rfl⟩ | rfl
      · rcases (hW x hx).1 with h | h <;> [exact .inr (by dsimp only; omega_arith); exact .inl (by dsimp only; omega_arith)]
      · exact .inl (by dsimp only; omega_arith)
    · have hr' : r ∉ [Reg.r0, .r1, .r2, .r3, .r12, .lr] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      rw [K₃.gpr r (by simp [hlr]), K.rest.gpr r hr', E.keep r (by intro h; simp [h] at hr')]
  · rw [K₃.sp, K.rest.sp, E.sp]
  · -- The memory.
    rw [M₃]
    refine (Outs.sub (rs := [(Impl.Weierstrass.Point.ownAt S.k, 4)]) E.mem fun r hr => ?_).trans
      (Outs.sub K.mem fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, by dsimp only; omega_arith⟩
    · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
      rcases hr with ⟨x, hx, rfl⟩ | rfl
      · rcases (hW x hx).2 with h | h
        · exact ⟨_, List.mem_cons_self, h.1, by dsimp only; omega_arith⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.1, by dsimp only; omega_arith⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by dsimp only; omega_arith, by dsimp only; omega_arith⟩
  · rw [K₃.gpr _ (by simp), K.r12, E.r12]
  · rw [M₃]; exact I₂.lt j (hO.outs j hj)
  · rw [M₃, I₂.val 0 (hO.outs 0 (by decide)), I₂.val 1 (hO.outs 1 (by decide)),
      I₂.val 2 (hO.outs 2 (by decide))]

/-- `fnOps_ok` for the complete addition: `O`'s coordinates stand for
`rcbAdd` of what the constants and the operands stand for. -/
theorem fn_ok {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m) (hodd : S.m % 2 = 1)
    {dbl : Bool} {s : State} (hp : PrePt S.k S.m dbl s) {u : Bool} :
    WP isa (Impl.Weierstrass.Arm.Point.fn S dbl u) s fun s' => abiPreserved s s' ∧
      Outs (State.addr (s.gpr .r0)) [(Impl.Weierstrass.Point.oAt S.k, 3 * Impl.Weierstrass.Point.elemBytes S.k),
        (Impl.Weierstrass.Point.ownAt S.k, 4096 - Impl.Weierstrass.Point.ownAt S.k)] s.mem s'.mem ∧
      s'.gpr .r12 = s.gpr .r0 ∧
      (∀ j < 3, wordsVal s'.mem (State.addr (s.gpr .r0)) (enc S.k dbl j) S.k < S.m) ∧
      (toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (State.addr (s.gpr .r0)) (enc S.k dbl 0) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (State.addr (s.gpr .r0)) (enc S.k dbl 1) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (State.addr (s.gpr .r0)) (enc S.k dbl 2) S.k)) =
        VG.Proof.Weierstrass.rcbAdd (E₀ S.k S.m dbl s 9) (E₀ S.k S.m dbl s 10) (E₀ S.k S.m dbl s 3)
          (E₀ S.k S.m dbl s 4) (E₀ S.k S.m dbl s 5) (E₀ S.k S.m dbl s 6) (E₀ S.k S.m dbl s 7)
          (E₀ S.k S.m dbl s 8) :=
  WP.mono (fnOps_ok hM hodd rcbIds_opsOk hp) fun _ ⟨A, O, R, L, V⟩ =>
    ⟨A, O, R, L, V.trans (rcb_run rcbIds_apart _)⟩

end VG.Proof.Weierstrass.Arm.Point
