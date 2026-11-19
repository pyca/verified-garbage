module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Impl.Bignum.X86.PrivPre
meta import VerifiedGarbage.Impl.Bignum.X86.PrivPre
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTop
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.X86.CrtInstalled
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
import VerifiedGarbage.Proof.Mont.X86.PowerInit
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Primes
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Top
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86.CrtSave

/-! ### `Bignum.X86.PrivPre.Fn`, which this module and modules that import it used -/

section

/-! # The factors' values of an RSA private key on x86: the internal function

`primes`, with `vg_rsa_private_crt`'s arguments and precondition
(`primesContract`, `Proof.Rsa.privateCrtContract`'s but for its
postcondition): it returns the low bit of the mask of `p q = n`, leaves
`R_p² mod p` (`w_p = max(2, ⌈p_len / 8⌉)` words of 32 bits, twice) in the
working space's wide slot 16 and `R_q² mod q` in 17, and changes no memory
but the working space's and the stack's below the stack pointer
(`primes_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrivPre

open VG VG.X86 VG.X86.Spill VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Bignum.X86.Crt (componentValue componentArguments)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.PrivPre (primes primesBody)

/-- What `primes` leaves (see the module docs). -/
def primesPost (s t : State) : Prop :=
  t.gpr .eax = BitVec.ofNat 32 (decide (componentValue s.mem (arg s) 6 * componentValue s.mem (arg s) 8 =
    componentValue s.mem (arg s) 2)).toNat ∧
  (xIn s.mem (arg s) (arg s 3).toNat % safeM (componentValue s.mem (arg s) 6) =
      2 ^ fixB (arg s 3).toNat % safeM (componentValue s.mem (arg s) 6) →
    val32 t.mem (argumentPointer s 16) (lo (arg s 3).toNat (.slot .wide 16))
        (2 * Spec.Rsa.primeWords (arg s 7).toNat) =
      2 ^ r2Exp (arg s 7).toNat % safeM (componentValue s.mem (arg s) 6)) ∧
  (xIn s.mem (arg s) (arg s 3).toNat % safeM (componentValue s.mem (arg s) 8) =
      2 ^ fixB (arg s 3).toNat % safeM (componentValue s.mem (arg s) 8) →
    val32 t.mem (argumentPointer s 16) (lo (arg s 3).toNat (.slot .wide 17))
        (2 * Spec.Rsa.primeWords (arg s 9).toNat) =
      2 ^ r2Exp (arg s 9).toNat % safeM (componentValue s.mem (arg s) 8)) ∧
  Frame [⟨argumentPointer s 16, (arg s 17).toNat * 8⟩, below (s.gpr .esp) 96] s.mem t.mem

/-- `primes`' contract: `vg_rsa_private_crt`'s precondition and publics, and `primesPost`. -/
def primesContract : Contract isa :=
  { Proof.Rsa.privateCrtContract abi 96 with post := primesPost }

theorem primes_ok {s : State} (A : CrtABI s) :
    WP isa primes s fun t => primesPost s t ∧ abiPreserved s t := by
  have low : 48 ≤ (arg s 17).toNat * 8 := by have := A.used; omega_using [this]
  have high : (arg s 17).toNat * 8 ≤ 2 ^ 64 := by have := A.scratchBound; omega_using []
  unfold primes
  rw [entry_eq]
  refine WP.seq (WP.mono (Crt.installed_ok A) fun u ⟨I, S, K, O⟩ => ?_)
  have hI : RIn (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) u :=
    In.ofInputs I (need_le A.lengths.1 A.scratchLength)
      (by simp only [argumentPointer, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (Nat.lt_trans (arg s 16).isLt (by decide : 2 ^ 32 < 2 ^ 64))]) rfl
  refine WP.seq (WP.mono (primesBody_ok hI) fun v ⟨F, V16, V17, eax, Kv⟩ => ?_)
  have espu : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have props := bodyR_props hI
  -- The registers saved at bytes 32 to 48 of the working space are kept.
  have Saved : Saved v.mem (off (argumentPointer s 16)) s.gpr Crt.savedRegisters := by
    intro p hp
    have B : 32 ≤ p.2 ∧ p.2 + 4 ≤ 48 := by
      simp only [Crt.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    refine (F.readW (r := ⟨off (argumentPointer s 16) 32, 16⟩)
      (Offset.contains _ B.1 (by omega_using [B]) (by decide)) ?_ (by decide)).trans (S p hp)
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [espu]
      have Z := I.room.apart
      rw [espu] at Z
      exact (Z.sub_right (Offset.sub_base _ (by omega_using [low]))).symm
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      rcases (props q hq).2 with h48 | h32
      · exact Offset.disjoint _ (.inl (by omega_using [h48])) (by omega_using []) (by have := (props q hq).1; omega_using [this])
      · exact Offset.disjoint _ (.inr (by omega_using [h32])) (by omega_using []) (by have := (props q hq).1; omega_using [h32])
  rw [espu] at F
  have Whole : Frame [⟨argumentPointer s 16, (arg s 17).toNat * 8⟩, below (s.gpr .esp) 96] s.mem v.mem := by
    have Start := VG.Proof.Bignum.outside_frame O (by omega_using [])
    simp only [BitVec.add_zero] at Start
    refine (Start.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)).trans
      (F.sub fun r hr => ?_)
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨_, by simp, fun _ h => h⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (props q hq).1⟩
  have Ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    apply Whole.readW (Region.contains_self _ 4) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact A.retScratch
    · exact ret_zone40 A.stackLow
  rw [restore_eq]
  refine WP.mono (Crt.entryRestore_ok (I.scratch.of_keeps Kv (by decide) (by decide)) low Saved) fun t R => ?_
  refine ⟨?_, restored_abi R ((Kv.1 _ (by decide)).trans (K.1 _ (by decide))) Ret⟩
  have B (i : Nat) (hi : i ∈ componentArguments) :
      Spec.Rsa.bytesAt u.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat =
        Spec.Rsa.bytesAt s.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat := by
    apply VG.Proof.Bignum.scratch_bytes O (by have := (arg s (i + 1)).isLt; omega_using [])
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.nScratch
    · exact A.inScratch
    · exact A.pScratch
    · exact A.qScratch
    · exact A.dpScratch
    · exact A.dqScratch
    · exact A.qiScratch
  have cv : ∀ i ∈ componentArguments, componentValue u.mem (arg s) i = componentValue s.mem (arg s) i :=
    fun i hi => by simp only [componentValue]; rw [B i hi]
  have xi : xIn u.mem (arg s) (arg s 3).toNat = xIn s.mem (arg s) (arg s 3).toNat := by
    have e5 : (arg s 5).toNat = (arg s 3).toNat := by rw [hI.extra.inLen, BitVec.toNat_ofNat]; omega_using []
    have := B 4 (by decide)
    rw [e5] at this
    simp only [xIn]
    congr 1
    apply Mem.read_congr
    intro i hi
    have L := congrArg (fun l => l[i]?) this
    simpa [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi] using L
  rw [cv 2 (by decide), cv 6 (by decide), cv 8 (by decide)] at eax
  rw [xi] at V16 V17
  rw [cv 6 (by decide)] at V16
  rw [cv 8 (by decide)] at V17
  refine ⟨by rw [R.other .eax (by decide)]; exact eax, by rw [R.mem]; exact V16, by rw [R.mem]; exact V17,
    by rw [R.mem]; exact Whole⟩

end VG.Proof.Bignum.X86.PrivPre

end

end

/-! # The factors' values of an RSA private key on x86: constant time

`primesBody` is constant time on runs narrowed to the output and the
working space as `CrtRt.sized`'s (`body_relCT`), from runs that agree
(`CrtRt.Run`): its parts are checked by the taint analysis from `τA` between
the runs' invariants (`Run`, and `WSt` in a context), the factor's test of
its width and `r2Fast`'s of its squares choosing the same branches in both
(by the lengths, `factorTest_ok`, `r2Test_ok`), and the squares are
`CrtRt.prepare`'s (`squares4_relCT`); the entry and the return are private CRT's
(`Crt.entry_relCT`, `Crt.restore_relCT`): `primes` is constant time
(`primes_constantTime`), and with `primes_ok`, `primes_verified`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrivPre

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Bignum.X86.PublicRt (Both setWidth_toNat relCT_narrow)
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Proof.Dsa.X86 (wp_result)
open VG.Impl.Bignum.X86.CrtRt
open VG.Proof.Bignum.X86.Crt (componentArguments)
open VG.Impl.Bignum.X86.PrivPre (primes primesBody check factor factorTest primeIn prepCore reduceX fixStart fixStep
  fixMore r2Fix loadX shl)
open VG.Impl.Bignum.X86.PublicRt (widthB)

/-- `r2Fix`'s subtraction. -/
abbrev fixSub : List Instr :=
  widthB 0 .ebx ++ shl .ebx 4 ++ [.alu .sub .esi (.reg .ebx)]

/-- Code checked by the taint analysis from `τAs` (`esi` public). -/
abbrev SCheck (p : Prog isa) : Prop := (VG.Taint.check taint τAs p (VG.Taint.hintOf taint τAs p)).isSome = true

/-- Code checked by the SIMD taint analysis from `τAs`. -/
abbrev SXCheck (p : Prog isa) : Prop :=
  (VG.Taint.check sseTaint τAs p (VG.Taint.hintOf sseTaint τAs p)).isSome = true

/-- The taint checks of a context's part of `primeIn`, but the factor's. -/
structure CChecks (c : Ctx) : Prop where
  core : XCheck (prepCore c)
  low : ACheck (copy (.slot .wide 18) (.slot c 5) (one c))
  m453 : MulCheck c 4 5 3
  m443 : MulCheck c 4 4 3
  step : SCheck (.block (fixStep c))
  sub : SCheck (.block fixSub)
  dbl : SXCheck (doubleStep c)
  skip : ACheck (.block [])

theorem cChecks (c : Ctx) : CChecks c := by
  cases c <;> constructor <;> dsimp only [ACheck, XCheck, MulCheck, SCheck, SXCheck] <;> taint_decide

/-- The taint checks of the half context's reduction of `x`. -/
structure HChecks : Prop where
  high : ACheck (copyHigh 18 6)
  m563 : MulCheck .half 5 6 3
  add : XCheck (addMod .half 4 4 5)

theorem hChecks : HChecks := by
  constructor <;> dsimp only [ACheck, XCheck, MulCheck] <;> taint_decide

/-- The taint checks of a factor's part of `primesBody`. -/
structure FChecks (f i o : Nat) : Prop where
  test : ACheck (.block (factorTest i))
  load : ∀ c, ACheck (copy (.slot .wide f) (.slot c 0) (one c))
  start : ∀ c, ACheck (.block (fixStart i c))
  save : ∀ c, ACheck (copy (.slot c 4) (.slot .wide o) (one c))

theorem fChecks_p : FChecks 10 7 16 := by
  constructor <;> (try intro c; cases c) <;> dsimp only [ACheck, XCheck] <;> taint_decide
theorem fChecks_q : FChecks 11 9 17 := by
  constructor <;> (try intro c; cases c) <;> dsimp only [ACheck, XCheck] <;> taint_decide
theorem loadX_check : ACheck loadX := by dsimp only [ACheck]; taint_decide
theorem check_check : XCheck check := by dsimp only [XCheck]; taint_decide
theorem tail_check : ACheck (.block [.mov .eax (.mem (sc accOff)), .alu .and .eax (.imm 1)]) := by
  dsimp only [ACheck]; taint_decide

section
variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32} {s : State}

theorem runKeepF (R : Run Ex base bytes len args sp s) {t : State} {regs : List Reg} (K : Keeps regs s t)
    {ws : List (Nat × Nat)} (F : Frame (frameR base (s.gpr .esp) ws) s.mem t.mem)
    (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes) (di : .edi ∉ regs := by decide) (spn : .esp ∉ regs := by decide) :
    Run Ex base bytes len args sp t :=
  ⟨R.1.keepF K di spn F hfit, R.2.1.keep K spn, (K.1 _ spn).trans R.2.2⟩

theorem wstRegs {c : Ctx} {ks : List Nat} (W : WSt Ex base bytes len args sp c ks 0 s) {t : State} {regs : List Reg}
    (K : Keeps regs s t) (m : t.mem = s.mem) (di : .edi ∉ regs := by decide) (spn : .esp ∉ regs := by decide) :
    WSt Ex base bytes len args sp c ks 0 t :=
  let ⟨M, C, Hk, _, A, e⟩ := W
  ⟨M, C.regs K m di spn, fun j hj => by simp only [sv]; rw [m]; exact Hk j hj, fun j hj => absurd hj (Nat.not_lt_zero _),
    A.keep K spn, (K.1 _ spn).trans e⟩

/-- A run in a context with `esi` at `v`. -/
abbrev FS (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (c : Ctx) (v : BitVec 32) (u : State) : Prop :=
  WSt Ex base bytes len args sp c [3, 4] 0 u ∧ u.gpr .esi = v

theorem FS.agree {c : Ctx} {v : BitVec 32} {t : State} (F₁ : FS Ex base bytes len args sp c v s)
    (F₂ : FS Ex base bytes len args sp c v t) : VG.X86.Taint.Agree τAs s t := by
  obtain ⟨⟨_, C₁, -, -, A₁, e₁⟩, v₁⟩ := F₁
  obtain ⟨⟨_, C₂, -, -, A₂, e₂⟩, v₂⟩ := F₂
  exact agreeAs C₁.inp C₂.inp A₁ A₂ (e₁.trans e₂.symm) (v₁.trans v₂.symm)

theorem factorTest_run {i : Nat} (hi : i < 18) (R : Run Ex base bytes len args sp s) :
    WP isa (.block (factorTest i)) s fun u => Run Ex base bytes len args sp u ∧
      isa.eval .b u = some (decide ((args i).toNat < bc len .half + 1)) :=
  WP.mono (factorTest_ok R.1 hi) fun _ ⟨K, m, e⟩ => ⟨R.keep K (by rw [m]; exact Outside.refl _ _ _ _), e⟩

theorem prepCore_wst (R : Run Ex base bytes len args sp s) (c : Ctx) :
    WP isa (prepCore c) s (WSt Ex base bytes len args sp c [3] 0) :=
  WP.mono (prepCore_ok R.1 c) fun _ ⟨F, M, one, I, K⟩ =>
    ⟨_, ⟨R.1.keepF K (by decide) (by decide) F (baseR_fit R.1 c), M, safeM_gt _, safeM_odd _, I⟩,
      fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        subst hj; rw [one]; exact safeM_gt _,
      fun j hj => absurd hj (Nat.not_lt_zero _), R.2.1.keep K, (K.1 _ (by decide)).trans R.2.2⟩

/-- Slot 5 or 6 written keeps slot 3. -/
theorem slot3_apart {c : Ctx} {d : Nat} (hd5 : 5 ≤ d) :
    lo len (.slot c 3) + bc len c ≤ lo len (.slot c d) := by
  have est : st len c = 2 * bc len c + 32 := rfl
  have e3 : lo len (.slot c 3) = numBase + 3 * st len c := rfl
  have ed : lo len (.slot c d) = numBase + d * st len c := rfl
  have := Nat.mul_le_mul_right (st len c) hd5
  omega_arith

/-- `x`'s low chunk into slot 5. -/
theorem low_wst {c : Ctx} (W : WSt Ex base bytes len args sp c [3] 0 s) :
    WP isa (copy (.slot .wide 18) (.slot c 5) (one c)) s (WSt Ex base bytes len args sp c [3] 0) := by
  have h := W.run.1
  have bl := h.bytes_lt
  obtain W18 := h.wide_fit (j := 18) (by decide)
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  have estw : st len .wide = 2 * bc len .wide + 32 := rfl
  have est : st len c = 2 * bc len c + 32 := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  obtain bwc := bc_le_wide len c
  obtain s58 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have e5 : lo len (.slot c 5) = numBase + 5 * st len c := rfl
  obtain top : lo len (.slot c 8) + st len c ≤ lo len (.slot .wide 9) := by
    cases c
    · exact sl_le .wide (by decide)
    · exact half_in_wide h (by decide)
  obtain cb1 : cb len (one c) = bc len c := by simp [cb, one]
  refine WP.mono (copy_ok h (x := .slot .wide 18) (d := .slot c 5) (one_ok c) (by rw [cb1]; omega_arith)
    (by rw [cb1]; omega_arith) (by rw [cb1]; exact .inl (by omega_arith))) fun u ⟨O, _, K⟩ => ?_
  rw [cb1] at O
  refine W.keepFr K (by decide) (by decide) (ws := [(lo len (.slot c 5), bc len c)])
    (frameR_of_outside O (by omega_arith) (by simp)) (by simp; omega_arith) (by simp; omega_arith)
    fun i hi => ⟨hi, ?_, fun p hp => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hp
    subst hi; subst hp
    exact .inl (slot3_apart (d := 5) (by decide))

/-- `x`'s high chunk into the half slot 6. -/
theorem high_wst (W : WSt Ex base bytes len args sp .half [3] 0 s) :
    WP isa (copyHigh 18 6) s (WSt Ex base bytes len args sp .half [3] 0) := by
  have h := W.run.1
  have bl := h.bytes_lt
  obtain ⟨cwle, cw8, bh, h0, h5, h8, sth, top⟩ := HalfLay.mk' h
  obtain W18 := h.wide_fit (j := 18) (by decide)
  obtain bhw := bc_le_wide len .half
  have estw : st len .wide = 2 * bc len .wide + 32 := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  have h6 : lo len (.slot .half 6) = numBase + 6 * st len .half := rfl
  refine WP.mono (copyHigh_ok h (j := 18) (d := 6) (by omega_arith) (by omega_arith) (by omega_arith))
    fun u ⟨O, _, K⟩ => ?_
  refine W.keepFr K (by decide) (by decide) (ws := [(lo len (.slot .half 6), bc len .half)])
    (frameR_of_outside O (by omega_arith) (by simp)) (by simp; omega_arith) (by simp; omega_arith)
    fun i hi => ⟨hi, ?_, fun p hp => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hp
    subst hi; subst hp
    exact .inl (slot3_apart (d := 6) (by decide))

/-- The two halves' terms added into slot 4. -/
theorem add445_wst (W : WSt Ex base bytes len args sp .half [5, 4, 3] 0 s) :
    WP isa (addMod .half 4 4 5) s (WSt Ex base bytes len args sp .half [3, 4] 0) := by
  obtain ⟨M, C, Hk, He, A, sp₀⟩ := W
  have h := C.inp
  have nw := h.scratch.nowrap
  have bl := h.bytes_lt
  obtain f8 := h.slot_fit .half (j := 8) (by decide)
  have est : st len .half = 2 * bc len .half + 32 := rfl
  obtain e1 : lo len (.slot .half 1) = numBase + st len .half := by simp [lo]
  have e3 : lo len (.slot .half 3) = numBase + 3 * st len .half := rfl
  have e4 : lo len (.slot .half 4) = numBase + 4 * st len .half := rfl
  have e8 : lo len (.slot .half 8) = numBase + 8 * st len .half := rfl
  obtain bw := bc_eq_cwc len .half
  obtain hM : 0 < M := by have := C.gt; omega_arith
  refine WP.mono (addMod_ok h .half (o := 4) (a := 4) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [C.mod]; exact Hk 4 (by simp)) (by rw [C.mod]; exact Hk 5 (by simp)))
    fun u ⟨F, V, K⟩ => ?_
  obtain fit : ∀ p ∈ [(lo len (.slot .half 1), bc len .half + 4), (lo len (.slot .half 4), bc len .half)],
      p.1 + p.2 ≤ bytes := by simp; omega_arith
  refine ⟨M, C.keepF K (by decide) (by decide) F fit (by simp; omega_arith), fun j hj => ?_,
    fun j hj => absurd hj (Nat.not_lt_zero _), A.keep K, (K.1 _ (by decide)).trans sp₀⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl
  · simp only [sv]
    rw [frameR_val32 F h.room nw (by omega_arith) (by simp; omega_arith) fit]
    exact Hk 3 (by simp)
  · rw [V, C.mod]; exact Nat.mod_lt _ hM

/-- `reduceX`, from runs that agree. -/
theorem reduceX_relCT {c : Ctx} (hc : CChecks c) (hh : HChecks) :
    RelCT isa (Both (WSt Ex base bytes len args sp c [3] 0)) (reduceX c)
      (Both (WSt Ex base bytes len args sp c [3, 4] 0)) := by
  cases c with
  | wide =>
    simp only [reduceX]
    refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.low fun _ W => low_wst W) ?_
    exact mul_wst_relCT0 (o := 4) (a := 5) (b := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hc.m453 (by simp) (by decide) (by decide)
  | half =>
    simp only [reduceX]
    refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hc.low fun _ W => low_wst W) ?_
    refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hh.high fun _ W => high_wst W) ?_
    refine VG.RelCT.seq (mul_wst_relCT0 (o := 4) (a := 5) (b := 3) (ks' := [3, 4]) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hc.m453 (by simp) (by decide) (by decide)) ?_
    refine VG.RelCT.seq (mul_wst_relCT0 (o := 4) (a := 4) (b := 3) (ks' := [3, 4]) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hc.m443 (by simp) (by decide) (by decide)) ?_
    refine VG.RelCT.seq (mul_wst_relCT0 (o := 5) (a := 6) (b := 3) (ks' := [5, 4, 3]) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hh.m563 (by simp) (by decide) (by decide)) ?_
    exact PublicRt.relCT_both (VG.RelCT.taint (A := sseTaint) τA (fun _ _ h => h.1.agree h.2) hh.add)
      fun _ W => add445_wst W

theorem skip_relCT {c : Ctx} (hc : CChecks c) {P : State → Prop} (hP : ∀ u, P u → WSt Ex base bytes len args sp c [3, 4] 0 u) :
    RelCT isa (Both P) (.block []) (Both P) :=
  taint_both (fun _ _ W₁ W₂ => (hP _ W₁).agree (hP _ W₂)) _ hc.skip fun _ h => WP.block_nil h

/-- One more reduction, from runs with `esi` at `A`. -/
theorem fixMore_relCT {c : Ctx} (hc : CChecks c) {A : Nat} (hA : A + 8 * bc len c < 2 ^ 32) :
    RelCT isa (Both (FS Ex base bytes len args sp c (BitVec.ofNat 32 A))) (fixMore c)
      (Both fun u => FS Ex base bytes len args sp c (BitVec.ofNat 32 (A + 8 * bc len c)) u ∧
        isa.eval .b u = some (decide (A + 8 * bc len c < fixB len))) := by
  unfold fixMore
  refine VG.RelCT.seq (mul_wst_relCT (o := 4) (a := 4) (b := 3) (ks' := [3, 4])
    (X := fun u => u.gpr .esi = BitVec.ofNat 32 A) (X' := fun u => u.gpr .esi = BitVec.ofNat 32 A)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.m443 (by simp) (by decide) (by decide)
    fun _ _ e K => (K.1 _ (by decide)).trans e) ?_
  refine taint_both (fun _ _ F₁ F₂ => FS.agree F₁ F₂) _ hc.step fun _ ⟨W, e⟩ => ?_
  obtain hA' : A < 2 ^ 32 := by omega_arith
  refine WP.mono (fixStep_ok W.run.1 (A := A) (by rw [e, BitVec.toNat_ofNat]; omega_arith) hA)
    fun u ⟨K, m, esi, _, cf⟩ => ⟨⟨wstRegs W K m, BitVec.eq_of_toNat_eq (by rw [esi, BitVec.toNat_ofNat]; omega_arith)⟩, cf⟩

/-- The doublings, from runs with `esi` at the count. -/
theorem dbl_relCT {c : Ctx} (hc : CChecks c) {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 32) :
    RelCT isa (Both (FS Ex base bytes len args sp c (BitVec.ofNat 32 N))) (.loop (doubleStep c) .ne)
      (Both (WSt Ex base bytes len args sp c [3, 4] 0)) := by
  refine (relCT_countLoop (N := N) (I := fun j u => FS Ex base bytes len args sp c (BitVec.ofNat 32 (N - j)) u) hN
    fun j hj => ?_).mono (fun _ _ h => by simpa using h) fun _ _ h => ⟨h.1.1, h.2.1⟩
  refine PublicRt.relCT_both (VG.RelCT.taint (A := sseTaint) τAs (fun _ _ h => FS.agree h.1 h.2) hc.dbl)
    fun t ⟨⟨M, C, Hk, _, A, sp₀⟩, e⟩ => ?_
  have h := C.inp
  have nw := h.scratch.nowrap
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  obtain s34 : lo len (.slot c 3) + st len c ≤ lo len (.slot c 4) := sl_le c (by decide)
  obtain s48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  have e3 : lo len (.slot c 3) = numBase + 3 * st len c := rfl
  obtain bw := bc_eq_cwc len c
  obtain hM : 0 < M := by have := C.gt; omega_arith
  refine WP.mono (doubleStep_ok h c (by rw [C.mod]; exact Hk 4 (by simp))) fun u ⟨F, V, esiu, zu, K⟩ => ?_
  obtain fit : ∀ p ∈ [(lo len (.slot c 1), bc len c + 4), (lo len (.slot c 4), bc len c)], p.1 + p.2 ≤ bytes := by
    simp; omega_arith
  obtain sub : BitVec.ofNat 32 (N - j) - 1 = BitVec.ofNat 32 (N - (j + 1)) := by
    rw [VG.Proof.Mont.X86.Dynamic.counter_sub (by omega_arith) (by omega_arith)]; congr 1
  refine ⟨⟨⟨M, C.keepF K (by decide) (by decide) F fit (by simp; omega_arith), fun k hk => ?_,
    fun k hk => absurd hk (Nat.not_lt_zero _), A.keep K, (K.1 _ (by decide)).trans sp₀⟩, by rw [esiu, e, sub]⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · simp only [sv]
      rw [frameR_val32 F h.room nw (by omega_arith) (by simp; omega_arith) fit]
      exact Hk 3 (by simp)
    · rw [V, C.mod]; exact Nat.mod_lt _ hM
  · have z := VG.Proof.Mont.X86.Dynamic.counter_zero (k := N - j) (by omega_arith) (by omega_arith)
    have z0 : ∀ x : BitVec 32, x - 0 = x := BitVec.sub_zero
    rw [z0, Nat.sub_sub] at z
    rw [zu, e, sub, z]
    congr 2
    exact propext (by omega_arith)

/-- `r2Fix`, from runs that agree. -/
theorem r2Fix_relCT {c : Ctx} (hc : CChecks c) {i : Nat} (hi : i < 18) (hL1 : 1 ≤ (args i).toNat)
    (hL : (args i).toNat ≤ len) (hS : ACheck (.block (fixStart i c))) (hup : len ≤ 1024) :
    RelCT isa (Both (WSt Ex base bytes len args sp c [3, 4] 0)) (r2Fix i c)
      (Both (WSt Ex base bytes len args sp c [3, 4] 0)) := by
  obtain hb := bc_le hup c
  obtain hA := fixA_le hL hup c
  unfold r2Fix
  refine VG.RelCT.seq (taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ hS fun _ W =>
    WP.mono (fixStart_ok W.run.1 hi c hL1 hL) fun u ⟨K, m, esi, _, cf⟩ =>
      (⟨⟨wstRegs W K m, BitVec.eq_of_toNat_eq (by rw [esi, BitVec.toNat_ofNat]; omega_arith)⟩, cf⟩ :
        FS Ex base bytes len args sp c (BitVec.ofNat 32 (fixA (args i).toNat len c)) u ∧ _)) ?_
  let A := fixA (args i).toNat len c
  refine VG.RelCT.seq (R := fun (s t : State) => ∃ E : Nat,
    Both (FS Ex base bytes len args sp c (BitVec.ofNat 32 (A + 8 * bc len c * E))) s t)
    (VG.RelCT.ite (fun _ _ h => h.1.2.trans h.2.2.symm) ?_ ?_) ?_
  · refine VG.RelCT.seq ((fixMore_relCT hc (A := A) (by omega_arith)).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩)
      fun _ _ h => h) ?_
    refine VG.RelCT.ite (fun _ _ h => h.1.2.trans h.2.2.symm) ?_ ?_
    · refine ((fixMore_relCT hc (A := A + 8 * bc len c) (by omega_arith)).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩)
        fun _ _ h => ⟨2, ?_⟩)
      rw [show A + 8 * bc len c * 2 = A + 8 * bc len c + 8 * bc len c by omega_arith]
      exact ⟨h.1.1, h.2.1⟩
    · refine (skip_relCT hc (P := FS Ex base bytes len args sp c (BitVec.ofNat 32 (A + 8 * bc len c)))
        fun _ h => h.1).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => ⟨1, by rw [Nat.mul_one]; exact h⟩
  · refine (skip_relCT hc (P := FS Ex base bytes len args sp c (BitVec.ofNat 32 A)) fun _ h => h.1).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => ⟨0, by rw [Nat.mul_zero, Nat.add_zero]; exact h⟩
  refine VG.RelCT.exists_ fun E => ?_
  let V := BitVec.ofNat 32 (A + 8 * bc len c * E) - BitVec.ofNat 32 (fixB len)
  refine VG.RelCT.seq (taint_both (fun _ _ F₁ F₂ => FS.agree F₁ F₂) _ hc.sub fun _ ⟨W, e⟩ =>
    WP.mono (subBv_ok W.run.1) fun u ⟨K, m, esi, z⟩ =>
      (⟨⟨wstRegs W K m, by rw [esi, e]⟩, by rw [z, esi, e]⟩ :
        FS Ex base bytes len args sp c V u ∧ u.zf = some (V == 0))) ?_
  refine VG.RelCT.ite (fun _ _ h => by simp only [eval]; rw [h.1.2, h.2.2]) ?_ ?_
  · exact (skip_relCT hc (P := FS Ex base bytes len args sp c V) fun _ h => h.1).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => ⟨h.1.1, h.2.1⟩
  · by_cases hV : V = 0
    · refine VG.RelCT.of_false ?_
      rintro _ _ ⟨⟨⟨_, z⟩, _⟩, ev⟩
      simp only [eval, z, hV] at ev
      simp at ev
    · have hN : 0 < V.toNat := Nat.pos_of_ne_zero fun e => hV (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
      refine (dbl_relCT hc hN V.isLt).mono (fun _ _ h => ⟨⟨h.1.1.1.1, ?_⟩, h.1.2.1.1, ?_⟩) fun _ _ h => h
      · rw [h.1.1.1.2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rw [h.1.2.1.2, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem save4_run {c : Ctx} {o : Nat} (ho16 : 16 ≤ o) (ho : o ≤ 17) (R : Run Ex base bytes len args sp s) :
    WP isa (copy (.slot c 4) (.slot .wide o) (one c)) s (Run Ex base bytes len args sp) := by
  have h := R.1
  obtain cb1 : cb len (one c) = bc len c := by simp [cb, one]
  obtain fo := h.slot_fit .wide (j := o) (by omega_arith)
  obtain f4 := h.slot_fit c (j := 4) (by decide)
  have est : st len c = 2 * bc len c + 32 := rfl
  have estw : st len .wide = 2 * bc len .wide + 32 := rfl
  obtain bwc := bc_le_wide len c
  obtain lo9 : lo len (.slot .wide 9) ≤ lo len (.slot .wide o) := by
    have := Nat.mul_le_mul_right (st len .wide) (show 9 ≤ o by omega_arith)
    simp only [lo]; omega_arith
  obtain h4o : lo len (.slot c 4) + bc len c ≤ lo len (.slot .wide o) :=
    Nat.le_trans (primeR_below h c (lo len (.slot c 4), bc len c) (by simp)).1 lo9
  refine WP.mono (copy_ok h (x := .slot c 4) (d := .slot .wide o) (one_ok c) (by rw [cb1]; omega_arith)
    (by rw [cb1]; omega_arith) (by rw [cb1]; exact .inr h4o)) fun u ⟨O, _, K⟩ => ?_
  rw [cb1] at O
  exact R.keep K (O.mono (Nat.zero_le _) (by omega_arith))

theorem load_run {f : Nat} (hf9 : 9 ≤ f) (hf : f ≤ 17) (c : Ctx) (R : Run Ex base bytes len args sp s) :
    WP isa (copy (.slot .wide f) (.slot c 0) (one c)) s (Run Ex base bytes len args sp) := by
  cases c
  · exact copyDown_run hf9 hf (by decide) R
  · exact toHalf_run hf9 hf (by decide) R

/-- A factor's `R_p² mod p`, in a context, from runs that agree. -/
theorem primeIn_relCT {f i o : Nat} (hc : FChecks f i o) (hf9 : 9 ≤ f) (hf : f ≤ 17) (hi : i < 18)
    (ho16 : 16 ≤ o) (ho : o ≤ 17) (hL1 : 1 ≤ (args i).toNat) (hL : (args i).toNat ≤ len) (hup : len ≤ 1024)
    (c : Ctx) :
    RelCT isa (Both (Run Ex base bytes len args sp)) (primeIn f i o c) (Both (Run Ex base bytes len args sp)) := by
  obtain cc := cChecks c
  unfold primeIn
  refine VG.RelCT.seq (taint_both (fun _ _ R₁ R₂ => R₁.agree R₂) _
    (hc.load c) fun _ R => load_run hf9 hf c R) ?_
  refine VG.RelCT.seq (PublicRt.relCT_both (VG.RelCT.taint (A := sseTaint) τA (fun _ _ h => h.1.agree h.2) cc.core)
    fun _ R => prepCore_wst R c) ?_
  refine VG.RelCT.seq (reduceX_relCT cc hChecks) ?_
  refine VG.RelCT.seq (r2Fix_relCT cc hi hL1 hL (hc.start c) hup) ?_
  exact taint_both (fun _ _ W₁ W₂ => W₁.agree W₂) _ (hc.save c) fun _ W => save4_run ho16 ho W.run

/-- A factor's part of `primesBody`, from runs that agree. -/
theorem factor_relCT {f i o : Nat} (hc : FChecks f i o) (hf9 : 9 ≤ f) (hf : f ≤ 17) (hi : i < 18)
    (ho16 : 16 ≤ o) (ho : o ≤ 17) (hL1 : 1 ≤ (args i).toNat) (hL : (args i).toNat ≤ len) (hup : len ≤ 1024) :
    RelCT isa (Both (Run Ex base bytes len args sp)) (factor f i o) (Both (Run Ex base bytes len args sp)) := by
  unfold factor
  refine VG.RelCT.seq (taint_both (fun _ _ R₁ R₂ => R₁.agree R₂) _ hc.test fun _ R => factorTest_run hi R) ?_
  exact VG.RelCT.ite (fun _ _ h => h.1.2.trans h.2.2.symm)
    ((primeIn_relCT hc hf9 hf hi ho16 ho hL1 hL hup .half).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)
    ((primeIn_relCT hc hf9 hf hi ho16 ho hL1 hL hup .wide).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)

end

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {s : State}

theorem check_run (R : Run (CrtExtra base bytes len args) base bytes len args sp s) :
    WP isa check s (Run (CrtExtra base bytes len args) base bytes len args sp) := by
  have h := R.1
  obtain f18 := h.slot_fit .wide (j := 18) (by decide)
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e18 : lo len (.slot .wide 18) = numBase + 18 * st len .wide := rfl
  unfold check
  refine WP.seq (WP.mono (importComponents_ok h) fun u₁ ⟨O₁, n₁, _, p₁, q₁, _, _, _, K₁⟩ => ?_)
  obtain R₁ := R.keep K₁ (O₁.mono (Nat.zero_le _) (by omega_arith))
  exact WP.mono (pqCheck_ok R₁.1 n₁ p₁ q₁ (h.extra.positive 6 (by simp [componentArguments]))
    (h.extra.bounded 6 (by simp [componentArguments])) (h.extra.positive 8 (by simp [componentArguments]))
    (h.extra.bounded 8 (by simp [componentArguments])) (component_lt _ _ 6) (component_lt _ _ 8))
    fun _ ⟨F₂, _, K₂⟩ => runKeepF R₁ K₂ F₂ (valR_fit R₁.1)

/-- `primesBody`, from runs that agree. -/
theorem primesBody_relCT :
    RelCT isa (Both (Run (CrtExtra base bytes len args) base bytes len args sp)) primesBody fun _ _ => True := by
  obtain lens : ∀ {v : State}, Run (CrtExtra base bytes len args) base bytes len args sp v →
      (1 ≤ (args 7).toNat ∧ (args 7).toNat ≤ len) ∧ (1 ≤ (args 9).toNat ∧ (args 9).toNat ≤ len) :=
    fun R => ⟨⟨R.1.extra.positive 6 (by simp [componentArguments]), R.1.extra.bounded 6 (by simp [componentArguments])⟩,
      ⟨R.1.extra.positive 8 (by simp [componentArguments]), R.1.extra.bounded 8 (by simp [componentArguments])⟩⟩
  refine (VG.RelCT.exists_ (P := fun (_ : (1 ≤ (args 7).toNat ∧ (args 7).toNat ≤ len) ∧
    (1 ≤ (args 9).toNat ∧ (args 9).toNat ≤ len)) => Both (Run (CrtExtra base bytes len args) base bytes len args sp))
    fun H => ?_).mono (fun _ _ h => ⟨lens h.1, h⟩) fun _ _ h => h
  refine (VG.RelCT.exists_ (P := fun (_ : len ≤ 1024) => _) fun hup => ?_).mono
    (fun _ _ h => ⟨h.1.1.upper', h⟩) fun _ _ h => h
  unfold primesBody
  refine VG.RelCT.seq (taint_both (fun _ _ R₁ R₂ => R₁.agree R₂) _ loadX_check fun _ R => WP.mono (loadX_ok R.1)
    fun _ ⟨O, _, K⟩ => R.keep K (O.mono (Nat.zero_le _) (by
      have := R.1.wide_fit (j := 18) (by decide); omega_arith))) ?_
  refine VG.RelCT.seq (PublicRt.relCT_both (VG.RelCT.taint (A := sseTaint) τA (fun _ _ h => h.1.agree h.2)
    check_check) fun _ R => check_run R) ?_
  refine VG.RelCT.seq (factor_relCT fChecks_p (by decide) (by decide) (by decide) (by decide) (by decide)
    H.1.1 H.1.2 hup) ?_
  refine VG.RelCT.seq (factor_relCT fChecks_q (by decide) (by decide) (by decide) (by decide) (by decide)
    H.2.1 H.2.2 hup) ?_
  exact VG.RelCT.taint (A := taint) τA (fun _ _ h => h.1.agree h.2) tail_check

end

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {s : State}

theorem side_in (S : Side base bytes len args sp s) :
    RIn base bytes len args (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) := by
  obtain ⟨h, _, _, _⟩ := S
  have x := h.extra
  refine ⟨⟨h.scratch.edi, by simp, h.scratch.nowrap, h.scratch.stk⟩, h.lower, h.upper,
    fun i hi => ⟨⟨?_, (h.stack i hi).stack.apart⟩, (h.stack i hi).value⟩, h.outLen, h.room, h.top, h.need,
    h.hbase, h.hbytes, ⟨x.space, x.nLen, x.inLen, x.pShort, x.qShort, x.dpLen, x.dqLen, x.qiLen, x.outFit,
    ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩, x.outApart, x.positive, x.bounded, x.fits,
    fun i hi => ?_, x.apart⟩⟩
  · obtain ⟨r, hr, hc⟩ := (h.stack i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := x.readable i hi
    exact ⟨r, List.mem_append_left _ hr, hc⟩

theorem side_run (S : Side base bytes len args sp s) :
    Run (CrtExtra base bytes len args) base bytes len args sp
      (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) := by
  refine ⟨side_in S, ⟨S.1.top, fun r hr => ?_⟩, S.2.1⟩
  simp only [State.withRegions, narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact S.2.2.1
  · exact S.2.2.2

theorem body_relCT (sp : BitVec 32) :
    RelCT isa (Both (Side base bytes len args sp)) primesBody fun _ _ => True := by
  refine relCT_narrow (Pn := Both (Run (CrtExtra base bytes len args) base bytes len args sp))
    (fun s => s.rd ++ s.wr) (fun _ => narrowW base bytes len args) (fun s₁ s₂ ⟨S₁, S₂⟩ => ?_)
    primesBody_relCT
  obtain cov : ∀ {s : State}, Side base bytes len args sp s → Covers (narrowW base bytes len args) s.wr := by
    intro s S
    rintro a n ⟨r, hr, hc⟩
    simp only [narrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one S.1.crt.outWrite a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, S.1.scratch.wr, hc⟩
  obtain wp : ∀ {s : State}, Side base bytes len args sp s →
      ∃ F, WP isa primesBody (s.withRegions (s.rd ++ s.wr) (narrowW base bytes len args)) F :=
    fun S => ⟨_, primesBody_ok (side_in S)⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂,
    side_run S₁, side_run S₂⟩

end

theorem primes_trace {s t : State} (A : TopABI s) (B : TopABI t)
    (args : ∀ i < 18, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa primes s tr sf) (F : Exec isa primes t ur tf) : tr = ur := by
  obtain A0 := args 0 (by decide)
  obtain A1 := args 1 (by decide)
  obtain A3 := args 3 (by decide)
  obtain A8 := args 16 (by decide)
  obtain A9 := args 17 (by decide)
  obtain hb : (arg s 16).toNat = (argumentPointer s 16).toNat := (setWidth_toNat _).symm
  cases E with
  | @seq _ _ _ u _ _ _ E1 Erest =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 Frest =>
      obtain T1 := (Crt.entry_relCT _ _ _ _ _ _
        ⟨SP, A8, (A.abi.stackArgument (by decide : 16 < 18)).readSrc,
          (B.abi.stackArgument (by decide : 16 < 18)).readSrc⟩ E1 F1).1
      obtain ⟨Is, _, Ks, _⟩ := wp_result (Crt.installed_ok A.abi) E1
      obtain ⟨It, _, Kt, _⟩ := wp_result (Crt.installed_ok B.abi) F1
      obtain Iv : Crt.Inputs (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) v := by
        obtain J := It.argsEq (fun i hi => (args i hi).symm)
        simpa only [argumentPointer, ← A8, ← A9, ← A3] using J
      obtain need := need_le A.abi.lengths.1 A.abi.scratchLength
      obtain espu : u.gpr .esp = s.gpr .esp := Ks.1 _ (by decide)
      obtain espv : v.gpr .esp = s.gpr .esp := (Kt.1 _ (by decide)).trans SP.symm
      obtain Su : Side (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) (s.gpr .esp) u := by
        refine ⟨In.ofInputs Is need hb rfl, espu, ?_, ?_⟩
        · rw [espu, ← A.abi.outLength]; exact args_apart A A.abi.retOut A.outArgs.symm
        · rw [espu]; exact args_apart A A.abi.retScratch A.abi.scratchArgs.symm
      obtain Sv : Side (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) (s.gpr .esp) v := by
        refine ⟨In.ofInputs Iv need hb rfl, espv, ?_, ?_⟩
        · rw [espv]
          obtain D := args_apart B B.abi.retOut B.outArgs.symm
          simp only [argumentPointer, ← A0, ← A1, ← SP] at D
          rw [← A.abi.outLength]; exact D
        · rw [espv]
          obtain D := args_apart B B.abi.retScratch B.abi.scratchArgs.symm
          simp only [argumentPointer, ← A8, ← A9, ← SP] at D
          exact D
      cases Erest with
      | @seq _ _ _ w _ _ _ E2 E3 =>
        cases Frest with
        | @seq _ _ _ z _ _ _ F2 F3 =>
          obtain T2 := (body_relCT (s.gpr .esp) _ _ _ _ _ _ ⟨Su, Sv⟩ E2 F2).1
          obtain ⟨-, -, -, -, Ksu⟩ := wp_result (primesBody_ok Su.1) E2
          obtain ⟨-, -, -, -, Ktv⟩ := wp_result (primesBody_ok Sv.1) F2
          obtain Agree : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) w z :=
            agree_regs (by
              intro r hr
              obtain rfl := List.mem_singleton.mp hr
              rw [Ksu.1 _ (by decide), Ktv.1 _ (by decide)]
              exact (Su.pair Sv).agree.rf.1 _ (by decide))
          obtain T3 := (Crt.restore_relCT _ _ _ _ _ _ Agree E3 F3).1
          rw [T1, T2, T3]

theorem primes_constantTime : ConstantTime isa primesContract.pre primesContract.pub primes := by
  intro s t tr ur sf tf S T H E F
  obtain Args := Crt.arguments H
  exact primes_trace (topABI_of S) (topABI_of T) Args.2 Args.1 E F

theorem primes_correct (s : State) (h : primesContract.pre s) :
    ∃ trace t, Exec isa primes s trace t ∧ abiPreserved s t ∧ primesContract.post s t := by
  obtain ⟨trace, t, E, P, R⟩ := primes_ok (crtABI_of h)
  exact ⟨trace, t, E, R, P⟩

theorem primes_verified : Verified target primes primesContract :=
  ⟨primes_correct, primes_constantTime, CrtRt.satisfiable⟩

end VG.Proof.Bignum.X86.PrivPre
