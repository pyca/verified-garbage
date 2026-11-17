module

public import VerifiedGarbage.Proof.Ed448.Arm.VerifyMain
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyLocal
import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.X448.Arm.Counters
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyMain
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyLocal
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Spec.Ed448.Contract

/-!
# Ed448 verification's equation on ARMv7: `Verified`

Correctness including the ABI, given the reference computations' agreement
with the specification (`RecoverOk`, `VerifyEqCombOk`, which the registration
file passes in, from `Proof/Ed448/Facts.lean` and `CombFacts.lean`), and constant time.

The code branches on the bits of `S` and of the challenge, which the contract
declares public, so its constant time relates two runs (`RelCT`):

* what comes before the loop (`vbefore`) and after it (`vafter`) is constant
  time by taint tracking, from the arguments and from the working space's
  address: their only branches are on loop counters, and every address is an
  argument plus a constant or a counter;
* the two runs enter the loop with the same bits of `S` and `k` at `VBITS`,
  as correctness says (`vbefore_ok`), and each iteration keeps the loop's
  invariant in both (`vload_ok`, `vdoubleAdd_ok`), so both load the same byte
  into `r8`; from there the doubling, the comb's row (in the last 114 bits,
  a test of the counter; its selection scans the whole table), the test of
  `r8` and the addition are constant time by taint tracking, with `r8` and
  the counter public, which the field functions never write.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (RecoverOk VerifyEqCombOk)
open VG.Proof.Ed25519.Arm (CT ctRegs ctBoth)
open VG.Spec.Ed448 (bytesAt decodeLE)

theorem VerifyPre.of {s : State} (h : verifyEquationLocal.pre s) : VerifyPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2⟩

theorem verifyEquation_ok (hR : RecoverOk) (hE : VerifyEqCombOk) (s : State) (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verifyEquation_main hR hE (VerifyPre.of hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he⟩, h.2⟩

/-! ## Constant time -/

/-- The working space's address is the same in two runs with the same working space. -/
theorem scr_agree {base : Addr} {x y : State} (hx : Scr x base) (hy : Scr y base) :
    x.gpr .r0 = y.gpr .r0 := by
  apply BitVec.eq_of_toNat_eq
  rw [← VG.Proof.X25519.Arm.addr_toNat, ← VG.Proof.X25519.Arm.addr_toNat, hx.r0, hy.r0]

/-- A run before the loop: the state the function was entered in is some state. -/
def Start (base : Addr) (S K : Nat) (x : State) : Prop := ∃ s pk sig, VMid s base pk sig S K x

/-- A run before bit `n - 1`: the loop's invariant, from some state before the loop with the
bits of `S` and `k`. -/
def Run (base : Addr) (S K n : Nat) (x : State) : Prop :=
  ∃ A s₀, (∀ t < 456, s₀.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pair2 S K t)) ∧
    VInv base S K A s₀ x n

/-- A run with the byte of bit `n` loaded. -/
def Loaded (base : Addr) (S K n : Nat) (x : State) : Prop :=
  ∃ A s₀, (∀ t < 456, s₀.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pair2 S K t)) ∧
    VBit base S K A s₀ x n

/-- `ctRegs`, by the analysis of the code without its offsets (`Taint.check_eraseOff`). -/
theorem ctRegsErased {P : State → State → Prop} {c c' : Prog isa} (rs : List Reg)
    (hp : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) (he : Arm.Code.eraseOff c = c')
    {hint : VG.Taint.Hint taint.T} (hc : (taint.check (Taint.ofRegs rs) c' hint).isSome = true) :
    CT P c (fun _ _ => True) :=
  ctRegs rs hp (hint := hint) (Taint.check_eraseOff c hint (Taint.noBase_ofRegs rs) ▸ he ▸ hc)

theorem vbefore_ct :
    CT (fun x y => verifyEquationLocal.pre x ∧ verifyEquationLocal.pre y ∧ verifyEquationLocal.pub x y)
      vbefore (fun _ _ => True) := by
  apply ctRegsErased [.r0, .r1, .r2, .r3] _ (c' := vbeforeErased) rfl (by native_taint_decide)
  intro x y h r hr
  obtain ⟨h0, h1, h2, h3, _⟩ := h.2.2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem counter_ct (base : Addr) (S K : Nat) :
    CT (fun x y => Start base S K x ∧ Start base S K y) (.block [.movw .r11 456])
      (fun x y => Run base S K 456 x ∧ Run base S K 456 y) := by
  apply ctBoth
  · apply ctRegs [] _ (by native_taint_decide)
    exact fun _ _ _ r hr => (List.not_mem_nil hr).elim
  · rintro x ⟨s, pk, sig, M⟩
    exact WP.mono (setCounter_ok x 456 (by decide)) fun x' ⟨h1, h2, h3, h4, h5⟩ =>
      ⟨_, x, M.bits, M.inv h1 h2 h3 h4 h5⟩

theorem vload_ct (base : Addr) (S K : Nat) {n : Nat} (hn : n < 456) :
    CT (fun x y => Run base S K (n + 1) x ∧ Run base S K (n + 1) y) (.block vload)
      (fun x y => Loaded base S K n x ∧ Loaded base S K n y) := by
  apply ctBoth
  · apply ctRegs [.r0, .r11] _ (by native_taint_decide)
    intro x y h r hr
    obtain ⟨⟨_, _, _, hx⟩, ⟨_, _, _, hy⟩⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scr_agree hx.scr hy.scr
    · exact hx.r11.trans hy.r11.symm
  · rintro x ⟨A, s₀, hb, hi⟩
    exact WP.mono (vload_ok hn hb hi) fun u hu => ⟨A, s₀, hb, hu⟩

theorem vdoubleAdd_ct (base : Addr) (S K : Nat) {n : Nat} (hn : n < 456) :
    CT (fun x y => Loaded base S K n x ∧ Loaded base S K n y) vdoubleAdd
      (fun x y => (Run base S K n x ∧ x.z = decide (n = 0)) ∧ (Run base S K n y ∧ y.z = decide (n = 0))) := by
  apply ctBoth
  · apply ctRegs [.r0, .r8, .r11] _ (by native_taint_decide)
    intro x y h r hr
    obtain ⟨⟨_, _, _, hx⟩, ⟨_, _, _, hy⟩⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact scr_agree hx.scr hy.scr
    · exact hx.r8.trans hy.r8.symm
    · exact hx.r11.trans hy.r11.symm
  · rintro x ⟨A, s₀, hb, hi⟩
    exact WP.mono (vdoubleAdd_ok hn hb hi) fun u ⟨hu, hz⟩ => ⟨⟨A, s₀, hb, hu⟩, hz⟩

theorem vloop_ct (base : Addr) (S K : Nat) :
    CT (fun x y => Start base S K x ∧ Start base S K y) vloop
      (fun x y => Run base S K 0 x ∧ Run base S K 0 y) := by
  refine RelCT.seq (counter_ct base S K) ?_
  refine (RelCT.loop (M := isa) (Q := fun x y => Run base S K 0 x ∧ Run base S K 0 y)
    (fun n x y => 0 < n ∧ n ≤ 456 ∧ Run base S K n x ∧ Run base S K n y)
    (fun n => ?_) 456).mono (fun x y h => ⟨by decide, Nat.le_refl _, h.1, h.2⟩) fun _ _ h => h
  by_cases hn : 0 < n ∧ n ≤ 456
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hn]⟩
    have hm : m < 456 := by omega_using [hn]
    refine (RelCT.seq (vload_ct base S K hm) (vdoubleAdd_ct base S K hm)).mono
      (fun x y h => ⟨h.2.2.1, h.2.2.2⟩) fun u v h => ?_
    obtain ⟨⟨ru, zu⟩, ⟨rv, zv⟩⟩ := h
    refine ⟨by show some (!u.z) = some (!v.z); rw [zu, zv], fun hf => ?_, fun ht => ?_⟩
    · have e : some (!u.z) = some false := hf
      rw [zu] at e
      have hm0 : m = 0 := by
        by_contra h0
        rw [decide_eq_false h0] at e
        cases e
      subst hm0
      exact ⟨ru, rv⟩
    · have e : some (!u.z) = some true := ht
      rw [zu] at e
      have hm0 : m ≠ 0 := by
        intro h0
        subst h0
        cases e
      exact ⟨m, by omega_arith, by omega_using [hm0], by omega_using [hn], ru, rv⟩
  · exact RelCT.of_false fun x y h => hn ⟨h.1, h.2.1⟩

theorem vafter_ct (base : Addr) (S K : Nat) :
    CT (fun x y => Run base S K 0 x ∧ Run base S K 0 y) vafter (fun _ _ => True) := by
  apply ctRegs [.r0] _ (by native_taint_decide)
  intro x y h r hr
  obtain ⟨⟨_, _, _, hx⟩, ⟨_, _, _, hy⟩⟩ := h
  rw [List.mem_singleton] at hr
  subst r
  exact scr_agree hx.scr hy.scr

theorem verifyEquation_ct (hR : RecoverOk) :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold verifyEquation
  have hb := vbefore_ct.wpDep
    (F := fun (σ t : State) => VMid σ (State.addr (σ.gpr .r3)) (State.addr (σ.gpr .r0)) (State.addr (σ.gpr .r1))
      (decodeLE (bytesAt σ.mem (State.addr (σ.gpr .r1) + BitVec.ofNat 64 57) 57))
      (decodeLE (bytesAt σ.mem (State.addr (σ.gpr .r2)) 57)) t)
    (fun s₁ s₂ h => ⟨vbefore_ok hR (VerifyPre.of h.1) rfl rfl rfl rfl rfl rfl,
      vbefore_ok hR (VerifyPre.of h.2.1) rfl rfl rfl rfl rfl rfl⟩)
  refine RelCT.seq (hb.mono (fun _ _ h => h)
    (Q' := fun x y => ∃ base S K, Start base S K x ∧ Start base S K y) ?_) ?_
  · rintro x y ⟨-, σ₁, σ₂, ⟨-, -, -, -, -, h3, -, hsig, hch⟩, f₁, f₂⟩
    refine ⟨_, _, _, ⟨_, _, _, f₁⟩, ?_⟩
    rw [h3, ← bytesAt_drop57, hsig, bytesAt_drop57, hch]
    exact ⟨_, _, _, f₂⟩
  · refine RelCT.exists_ fun base => RelCT.exists_ fun S => RelCT.exists_ fun K => ?_
    exact RelCT.seq (vloop_ct base S K) (vafter_ct base S K)

end VG.Proof.Ed448.Arm
