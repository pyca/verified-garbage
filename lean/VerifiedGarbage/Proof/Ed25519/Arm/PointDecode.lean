module

public import VerifiedGarbage.Impl.Ed25519.Arm.PointDecode
import VerifiedGarbage.Proof.Ed25519.Arm.PointEncode
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Decode
public import VerifiedGarbage.Proof.Ed25519.Arm.Packed
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.Arm.MulKeep
import VerifiedGarbage.Proof.Ed25519.Arm.UnpackField
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Ed25519.Recover
public import VerifiedGarbage.Impl.Ed25519.Arm.RecoverSign

/-! ### `Ed25519.Arm.RecoverPoint`, which this module and modules that import it used -/

section

/-! ### `Ed25519.Arm.RecoverSign`, which this module and modules that import it used -/

section

/-! ### `Ed25519.Arm.RecoverAdjust`, which only this module used -/

section

/-! Merged from `Proof.Ed25519.Arm.RecoverParity`. -/

@[expose] public section

section
/-! Merged from `Proof.Ed25519.Arm.FieldCheck`. -/
section
/-! Merged from `Proof.Ed25519.Arm.WordsZero`. -/
section
/-! Summing sixteen bounded limbs cannot overflow and detects zero. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def limbSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => limbSum f n + f n

theorem limbSum_bound {f : Nat → Nat} {n : Nat} (hf : ∀ k < n, f k < 65536) :
    limbSum f n ≤ 65535 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := ih (fun k hk => hf k (by omega_arith))
    have hn := hf n (by omega_arith)
    simp only [limbSum, Nat.mul_succ]
    omega_arith

theorem limbSum_zero (f : Nat → Nat) (n : Nat) : limbSum f n = 0 ↔ val16 f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [limbSum, val16_succ, Nat.add_eq_zero_iff, Nat.mul_eq_zero,
      Nat.ne_of_gt (Nat.two_pow_pos _), false_or, ih]

structure SumInv (b : BitVec 32) (o : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r3, .r9] s₀ s
  mem : s.mem = s₀.mem
  value : (s.gpr .r9).toNat = limbSum (limb s₀.mem (State.addr b) o) k

theorem sumLimbs_ok {b : BitVec 32} {s₀ : State} (hc : Ctx b s₀) (o : Nat) (ho : o + 64 ≤ 4096)
    (hl : Lim s₀.mem (State.addr b) o) (hz : (s₀.gpr .r9).toNat = 0) :
    WP isa (.block ((List.range 16).flatMap (sumLimb o))) s₀ fun t => Rest [.r3, .r9] s₀ t ∧
      t.mem = s₀.mem ∧ (t.gpr .r9).toNat = limbSum (limb s₀.mem (State.addr b) o) 16 := by
  refine WP.mono (wp_range_flatMap (M := isa) (SumInv b o s₀) (fun k s hk h => ?_)
    16 (Nat.le_refl _) s₀ ⟨Rest.refl _ _, rfl, hz⟩) fun t ht => ⟨ht.rest, ht.mem, ht.value⟩
  refine ldr0_ok (hc.of_rest h.rest (by decide)) (by omega_arith) fun u hu =>
    wp_dp (op2_reg _ _) fun t ht => WP.block_nil ?_
  have el : (u.gpr .r3).toNat = limb s₀.mem (State.addr b) o k := by rw [hu.gpr, h.mem]; rfl
  have es : (u.gpr .r9).toNat = limbSum (limb s₀.mem (State.addr b) o) k := by
    rw [hu.other _ (by decide), h.value]
  refine ⟨h.rest.trans ((hu.rest (by decide)).trans (ht.rest (by decide))),
    by rw [ht.mem, hu.mem, h.mem], ?_⟩
  rw [ht.gpr]
  change (u.gpr .r9 + u.gpr .r3).toNat = _
  rw [toNat_add_lt (by
    rw [es, el]
    have := limbSum_bound (fun j hj => hl j (by omega_arith) : ∀ j < k, limb s₀.mem (State.addr b) o j < 65536)
    have := hl k hk
    omega_arith), es, el]
  rfl

theorem wordsZero_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (o : Nat) (ho : o + 64 ≤ 4096)
    (hl : Lim s.mem (State.addr b) o) :
    WP isa (.block (wordsZero o)) s fun t => Rest [.r3, .r9] s t ∧ t.mem = s.mem ∧
      t.z = decide (V s.mem (State.addr b) o = 0) := by
  unfold wordsZero
  rw [List.append_assoc, WP.block_append_iff]
  refine wp_mov (op2_imm (by decide)) fun u hu => WP.block_nil ?_
  rw [WP.block_append_iff]
  refine WP.mono (sumLimbs_ok (hc.of_rest (hu.rest (ws := [.r9]) (by decide)) (by decide)) o ho
    (by rw [hu.mem]; exact hl) (by rw [hu.gpr]; rfl)) fun v ⟨vr, vm, vv⟩ => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (vr.trans (ht.rest _)), by rw [ht.mem, vm, hu.mem], ?_⟩
  have ve : v.gpr .r9 = BitVec.ofNat 32 (limbSum (limb s.mem (State.addr b) o) 16) := by
    apply BitVec.eq_of_toNat_eq
    rw [vv, hu.mem, toNat_imm (by have := limbSum_bound hl; omega_arith)]
  have he : v.gpr .r9 - (0 : BitVec 32) = v.gpr .r9 := BitVec.sub_zero _
  rw [hz, he, ve, ofNat_beq_zero (by have := limbSum_bound hl; omega_arith)]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact limbSum_zero _ _

end VG.Proof.Ed25519.Arm
end

/-! Canonical representatives give exact field comparisons. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem fieldZero_ok {s : State} {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b) (a : Slot) :
    WP isa (fieldZero a) s fun t => Keep b s t ∧ AllLim t.mem b ∧ env t.mem b = env s.mem b ∧
      t.z = decide (env s.mem b a = 0) := by
  refine WP.seq (WP.mono (freeze_ok hc hl a) fun u ⟨uk, ul, ue, uf, uv⟩ => ?_)
  refine WP.mono (wordsZero_ok (uk.ctx hc) FR (by decide) uf) fun t ⟨tr, tm, tz⟩ => ?_
  refine ⟨uk.trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩,
    tm ▸ ul, (congrArg (fun m => env m b) tm).trans ue, ?_⟩
  rw [tz, uv]
  have he : (env s.mem b a).val = 0 ↔ env s.mem b a = 0 :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  simp only [he]

theorem fieldEqual_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (a b : Slot) :
    WP isa (fieldEqual a b) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      (∀ i : Slot, i ≠ 21 → env t.mem base i = env s.mem base i) ∧
      t.z = decide (env s.mem base a = env s.mem base b) := by
  refine WP.seq (WP.mono (fieldCode_ok [.sub 21 a b] hc hl) fun u ⟨uk, ul, ue⟩ => ?_)
  refine WP.mono (fieldZero_ok (uk.ctx hc) ul 21) fun t ⟨tk, tl, te, tz⟩ => ?_
  refine ⟨uk.trans tk, tl, fun i hi => ?_, ?_⟩
  · rw [te, ue]
    exact Function.update_of_ne hi _ _
  · rw [tz, ue]
    change decide (env s.mem base a - env s.mem base b = 0) = _
    simp only [show ∀ u v : VG.Spec.X25519.Fe, u - v = 0 ↔ u = v from
      -- `-lia`: Lean 4.36's `grind` builds a proof the kernel rejects from `lia`
      -- over `Fin` of a non-literal modulus (lean4#15857, fixed in 4.37).
      fun _ _ => ⟨fun _ => by grind -lia, fun _ => by grind -lia⟩]

end VG.Proof.Ed25519.Arm
end

/-! Sign checks use the canonical x-coordinate and the saved sign bit. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem IKeep.sign {base : BitVec 32} {s t : State} (h : IKeep base s t) :
    t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
      s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 := by
  apply BitVec.eq_of_toNat_eq
  exact wd_frame h.frame fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)

theorem Keep.sign {base : BitVec 32} {s t : State} (h : Keep base s t) :
    t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
      s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 := (IKeep.of_keep h).sign

theorem parity_match (x : Nat) (b : Bool) : decide (x % 2 = b.toNat) = ((x % 2 == 1) == b) := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (b : Bool)
    (hl : Lim s.mem (State.addr base) FR)
    (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (.block recoverParity) s fun t => Rest [.r2, .r3, .r9] s t ∧ t.mem = s.mem ∧
      t.z = ((V s.mem (State.addr base) FR % 2 == 1) == b) := by
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_dp (op2_imm (by decide)) fun s2 u2 => ?_
  have r2 : Rest [.r2, .r3, .r9] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  refine ldr0_ok (hc.of_rest r2 (by decide)) (by decide) fun s3 u3 =>
    wp_dp (op2_reg _ _) fun s4 u4 => wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  have he : (s3.gpr .r9).toNat = V s.mem (State.addr base) FR % 2 := by
    rw [u3.other _ (by decide), u2.gpr]
    change (s1.gpr .r3 &&& (1 : BitVec 32)).toNat = _
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, u1.gpr]
    exact (parity_limb hl).symm
  have es : s3.gpr .r2 = BitVec.ofNat 32 b.toNat := by rw [u3.gpr, u2.mem, u1.mem]; exact hb
  refine ⟨r2.trans ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans (ht.rest _))),
    by rw [ht.mem, u4.mem, u3.mem, u2.mem, u1.mem], ?_⟩
  have sub0 : s4.gpr .r9 - (0 : BitVec 32) = s4.gpr .r9 := BitVec.sub_zero _
  rw [hz, sub0, u4.gpr]
  change (s3.gpr .r9 ^^^ s3.gpr .r2 == 0) = _
  rw [← parity_match]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  change (s3.gpr .r9 ^^^ s3.gpr .r2 = 0#32) ↔ _
  rw [BitVec.xor_eq_zero_iff]
  have en : (s3.gpr .r2).toNat = b.toNat := by rw [es, toNat_imm (by cases b <;> decide)]
  constructor
  · intro h
    exact he.symm.trans ((congrArg BitVec.toNat h).trans en)
  · intro h
    exact BitVec.eq_of_toNat_eq (he.trans (h.trans en.symm))

end VG.Proof.Ed25519.Arm
end

/-! Choose the encoded sign and finish the extended coordinates. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {umaal : Bool}

def recoveredPoint (x y : Spec.X25519.Fe) : Spec.Ed25519.Point := ⟨x, y, 1, x * y⟩
def signedX (x : Spec.X25519.Fe) (b : Bool) : Spec.X25519.Fe :=
  if (x.val % 2 == 1) == b then x else 0 - x

theorem returnFlag_ok (s : State) (b : Bool) :
    WP isa (.block [.mov .r9 (.imm b.toNat)]) s fun t =>
      Rest [.r9] s t ∧ t.mem = s.mem ∧ t.gpr .r9 = BitVec.ofNat 32 b.toNat := by
  refine wp_mov (op2_imm (by cases b <;> decide)) fun t ht => WP.block_nil ⟨ht.rest (by decide), ht.mem, ht.gpr⟩

theorem recoverSuccess_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa (recoverSuccess umaal) s fun t => Keep base s t ∧ AllLim t.mem base ∧ t.gpr .r9 = 1 ∧
      point (env t.mem base) 0 1 2 3 = recoveredPoint (env s.mem base 0) (env s.mem base 1) := by
  refine WP.seq (WP.mono (fieldCode_ok recoverSuccessOps hc hl) fun u ⟨uk, ul, ue⟩ => ?_)
  refine WP.mono (returnFlag_ok u true) fun t ⟨tr, tm, tv⟩ => ?_
  refine ⟨uk.trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩, tm ▸ ul, tv, ?_⟩
  rw [tm, ue]
  rfl

theorem adjustBranch_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hz : s.z = (((env s.mem base 0).val % 2 == 1) == b)) :
    WP isa (.ite .eq (.block []) (fieldCode false [.const 5 0, .sub 0 5 0])) s fun t =>
      Keep base s t ∧ AllLim t.mem base ∧ env t.mem base 0 = signedX (env s.mem base 0) b ∧
      env t.mem base 1 = env s.mem base 1 := by
  apply WP.ite (((env s.mem base 0).val % 2 == 1) == b) (by simp only [VG.Arm.eval, hz])
  · intro h
    exact WP.block_nil ⟨Keep.refl _ _, hl, by simp only [signedX, h, ite_true], rfl⟩
  · intro h
    refine WP.mono (fieldCode_ok [.const 5 0, .sub 0 5 0] hc hl) fun t ⟨tk, tl, te⟩ => ?_
    refine ⟨tk, tl, ?_, ?_⟩
    · rw [te]
      change 0 - env s.mem base 0 = signedX (env s.mem base 0) b
      simp only [signedX, h, Bool.false_eq_true, ite_false]
    · rw [te]; rfl

theorem recoverAdjustSign_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (recoverAdjustSign umaal) s fun t => Keep base s t ∧ AllLim t.mem base ∧ t.gpr .r9 = 1 ∧
      point (env t.mem base) 0 1 2 3 = recoveredPoint (signedX (env s.mem base 0) b) (env s.mem base 1) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok hc hl 0) fun a ⟨ak, al, ae, af, av⟩ => ?_
  refine WP.mono (recoverParity_ok (ak.ctx hc) b af (ak.sign.trans hb)) fun c ⟨cr, cm, cz⟩ => ?_
  have ck : Keep base s c := ak.trans ⟨cr.mono (by decide), by rw [cm]; exact Frame.refl _ _⟩
  have ce : env c.mem base = env s.mem base := (congrArg (fun m => env m base) cm).trans ae
  have ch : c.z = (((env c.mem base 0).val % 2 == 1) == b) := by rw [cz, av, ce]
  refine WP.seq (WP.mono (adjustBranch_ok (ck.ctx hc) (cm ▸ al) b ch) fun d ⟨dk, dl, dx, dy⟩ => ?_)
  refine WP.mono (recoverSuccess_ok ((ck.trans dk).ctx hc) dl) fun t ⟨tk, tl, tr, tp⟩ => ?_
  exact ⟨(ck.trans dk).trans tk, tl, tr, by rw [tp, dx, dy, ce]⟩

end VG.Proof.Ed25519.Arm

end

end


/-! Reject negative zero and otherwise return the selected sign. -/

@[expose] public section

namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {umaal : Bool}

def DecodeResult (base : BitVec 32) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .r9 = 0
  | some p => s.gpr .r9 = 1 ∧ point (env s.mem base) 0 1 2 3 = p

def signResult (x y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if x = 0 && b then none else some (recoveredPoint (signedX x b) y)

theorem recoverInvalid_ok (s : State) (base : BitVec 32) :
    WP isa recoverInvalid s fun t => Keep base s t ∧ t.mem = s.mem ∧ DecodeResult base none t :=
  WP.mono (returnFlag_ok s false) fun _ ⟨tr, tm, tv⟩ =>
    ⟨⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩, tm, tv⟩

theorem signTest_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (b : Bool)
    (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (.block signTest) s fun t => Rest [.r3] s t ∧ t.mem = s.mem ∧ t.z = !b := by
  refine ldr0_ok hc (by decide) fun u hu => wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (ht.rest _), by rw [ht.mem, hu.mem], ?_⟩
  rw [hz, hu.gpr, hb]
  cases b <;> rfl

theorem recoverSign_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (recoverSign umaal) s fun t => Keep base s t ∧ AllLim t.mem base ∧
      DecodeResult base (signResult (env s.mem base 0) (env s.mem base 1) b) t := by
  refine WP.seq (WP.mono (fieldZero_ok hc hl 0) fun a ⟨ak, al, ae, az⟩ => ?_)
  apply WP.ite (decide (env s.mem base 0 = 0)) (by simp only [VG.Arm.eval, az])
  · intro hzero
    have hz : env s.mem base 0 = 0 := of_decide_eq_true hzero
    refine WP.seq (WP.mono (signTest_ok (ak.ctx hc) b (ak.sign.trans hb)) fun c ⟨cr, cm, cz⟩ => ?_)
    have ck : Keep base s c := ak.trans ⟨cr.mono (by decide), by rw [cm]; exact Frame.refl _ _⟩
    have cl : AllLim c.mem base := cm ▸ al
    have ce : env c.mem base = env s.mem base := (congrArg (fun m => env m base) cm).trans ae
    apply WP.ite b (by simp only [VG.Arm.eval, cz, Bool.not_not])
    · intro ht
      refine WP.mono (recoverInvalid_ok c base) fun t ⟨tk, tm, tr⟩ => ?_
      refine ⟨ck.trans tk, tm ▸ cl, ?_⟩
      simpa only [signResult, hz, ht, decide_true, Bool.and_self, ite_true] using tr
    · intro hf
      refine WP.mono (recoverAdjustSign_ok (ck.ctx hc) cl b (ck.sign.trans hb)) fun t ⟨tk, tl, tr, tv⟩ => ?_
      refine ⟨ck.trans tk, tl, ?_⟩
      simp only [signResult, hf, Bool.and_false, Bool.false_eq_true, ite_false, DecodeResult]
      exact ⟨tr, by rw [tv, ce, hf]⟩
  · intro hnonzero
    have hn : env s.mem base 0 ≠ 0 := of_decide_eq_false hnonzero
    refine WP.mono (recoverAdjustSign_ok (ak.ctx hc) al b (ak.sign.trans hb)) fun t ⟨tk, tl, tr, tv⟩ => ?_
    refine ⟨ak.trans tk, tl, ?_⟩
    simp only [signResult, hn, decide_false, Bool.false_and, Bool.false_eq_true, ite_false, DecodeResult]
    exact ⟨tr, by rw [tv, ae]⟩

end VG.Proof.Ed25519.Arm

end

end

/-! Merged from `Proof.Ed25519.Arm.RecoverCandidate`. -/

@[expose] public section

section
/-! Candidate root and its square check agree with the decoding specification. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {umaal : Bool}

private theorem recoverInit_eval (e : Env) :
    evalOps recoverInitOps e 1 = e 1 ∧
    evalOps recoverInitOps e 6 = rootU (e 1) ∧
    evalOps recoverInitOps e 7 = rootV (e 1) ∧
    evalOps recoverInitOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
    evalOps recoverInitOps e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact pow_three _
  · exact congrArg (rootU (e 1) * ·) (pow_seven _)

private theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧
    evalOps recoverFinishOps e 1 = e 1 ∧
    evalOps recoverFinishOps e 5 = 0 ∧
    evalOps recoverFinishOps e 6 = e 6 ∧
    evalOps recoverFinishOps e 7 = e 7 ∧
    evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
    evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rootEnv_low (e : Env) (i : Slot) (hi : i.val < 14) : rootEnv e i = e i := by
  have h14 : i ≠ 14 := by intro h; have := congrArg Fin.val h; omega_using [hi, this]
  have h15 : i ≠ 15 := by intro h; have := congrArg Fin.val h; omega_using [hi, this]
  have h16 : i ≠ 16 := by intro h; have := congrArg Fin.val h; omega_using [hi, this]
  have h17 : i ≠ 17 := by intro h; have := congrArg Fin.val h; omega_using [hi, this]
  simp only [rootEnv, power250Env, opMul, opSqn, Function.update_of_ne h14,
    Function.update_of_ne h15, Function.update_of_ne h16, Function.update_of_ne h17]

theorem recoverCandidate_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa (recoverCandidate umaal) s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      env t.mem base 0 = rootX (env s.mem base 1) ∧
      env t.mem base 1 = env s.mem base 1 ∧
      env t.mem base 5 = 0 ∧ env t.mem base 6 = rootU (env s.mem base 1) ∧
      env t.mem base 7 = rootV (env s.mem base 1) ∧
      env t.mem base 11 = rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) ∧
      env t.mem base 12 = 0 - rootU (env s.mem base 1) := by
  refine WP.seq (WP.mono (fieldCode_ok recoverInitOps hc hl) fun a ⟨ka, la, va⟩ => ?_)
  refine WP.seq (WP.mono (rootPower_spec base a (ka.ctx hc) la) fun b ⟨kb, lb, vb⟩ => ?_)
  have be : ∀ i : Slot, i.val < 14 → env b.mem base i = env a.mem base i := by
    intro i hi
    rw [vb, rootEnv_low _ i hi]
  refine WP.mono (fieldCode_ok recoverFinishOps (kb.ctx (ka.ctx hc)) lb) fun t ⟨kt, lt, vt⟩ => ?_
  have ay := (recoverInit_eval (env s.mem base)).1
  have au := (recoverInit_eval (env s.mem base)).2.1
  have av := (recoverInit_eval (env s.mem base)).2.2.1
  have av3 := (recoverInit_eval (env s.mem base)).2.2.2.1
  have az := (recoverInit_eval (env s.mem base)).2.2.2.2
  have bx : env b.mem base 6 * env b.mem base 9 * env b.mem base 15 = rootX (env s.mem base 1) := by
    rw [be 6 (by decide), be 9 (by decide), vb, rootEnv_eval, rootPower_eq, va, au, av3, az]
    rfl
  refine ⟨(IKeep.of_keep ka).trans (kb.trans (IKeep.of_keep kt)), lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vt, (recoverFinish_eval _).1, bx]
  · rw [vt, (recoverFinish_eval _).2.1, be 1 (by decide), va, ay]
  · rw [vt, (recoverFinish_eval _).2.2.1]
  · rw [vt, (recoverFinish_eval _).2.2.2.1, be 6 (by decide), va, au]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.1, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.1, bx, be 7 (by decide), va, av]
  · rw [vt, (recoverFinish_eval _).2.2.2.2.2.2, be 6 (by decide), va, au]

end VG.Proof.Ed25519.Arm
end

/-! Candidate validation implements RFC 8032 recovery exactly. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {umaal : Bool}

def recoverResult (y : Spec.X25519.Fe) (b : Bool) : Option Spec.Ed25519.Point :=
  if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
  else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b
  else none

private theorem signResult_map (x y : Spec.X25519.Fe) (b : Bool) :
    signResult x y b = (do
      let z ← some x
      if z = 0 && b then none else some (signedX z b)).map (fun z => recoveredPoint z y) := by
  unfold signResult
  change (if x = 0 && b then none else some (recoveredPoint (signedX x b) y)) =
    (if x = 0 && b then none else some (signedX x b)).map (fun z => recoveredPoint z y)
  split <;> rfl

theorem recoverResult_spec (y : Spec.X25519.Fe) (b : Bool) :
    recoverResult y b = (Spec.Ed25519.recoverX y b).map (fun x => recoveredPoint x y) := by
  unfold recoverResult Spec.Ed25519.recoverX
  change (if rootV y * rootX y * rootX y = rootU y then signResult (rootX y) y b
    else if rootV y * rootX y * rootX y = 0 - rootU y then signResult (rootX y * Spec.Ed25519.sqrtM1) y b else none) =
    (if rootV y * rootX y * rootX y = rootU y then (do
        let z ← some (rootX y)
        if z = 0 && b then none else some (signedX z b))
      else if rootV y * rootX y * rootX y = 0 - rootU y then (do
        let z ← some (rootX y * Spec.Ed25519.sqrtM1)
        if z = 0 && b then none else some (signedX z b))
      else none).map (fun x => recoveredPoint x y)
  by_cases h : rootV y * rootX y * rootX y = rootU y
  · rw [ite_eq_left h, ite_eq_left h]
    exact signResult_map _ _ _
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h' : rootV y * rootX y * rootX y = 0 - rootU y
    · rw [ite_eq_left h', ite_eq_left h']
      exact signResult_map _ _ _
    · rw [ite_eq_right h', ite_eq_right h']
      rfl


private theorem sign_known {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat)
    (x y : Spec.X25519.Fe) (hx : env s.mem base 0 = x) (hy : env s.mem base 1 = y) :
    WP isa (recoverSign umaal) s fun t => IKeep base s t ∧ AllLim t.mem base ∧ DecodeResult base (signResult x y b) t := by
  refine WP.mono (recoverSign_ok hc hl b hb) fun t ⟨tk, tl, tr⟩ => ?_
  exact ⟨IKeep.of_keep tk, tl, by rw [hx, hy] at tr; exact tr⟩

theorem recoverPoint_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (b : Bool) (hb : s.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 = BitVec.ofNat 32 b.toNat) :
    WP isa (recoverPoint umaal) s fun t => IKeep base s t ∧ AllLim t.mem base ∧
      DecodeResult base ((Spec.Ed25519.recoverX (env s.mem base 1) b).map
        (fun x => recoveredPoint x (env s.mem base 1))) t := by
  rw [← recoverResult_spec, recoverPoint]
  refine WP.seq (WP.mono (recoverCandidate_ok hc hl) fun a ⟨ka, la, ax, ay, _, au, _, avx, anu⟩ => ?_)
  refine WP.seq (WP.mono (fieldEqual_ok (ka.ctx hc) la 11 6) fun c ⟨kc, lc, ce, cz⟩ => ?_)
  have kac := ka.trans (IKeep.of_keep kc)
  have cx : env c.mem base 0 = rootX (env s.mem base 1) := (ce 0 (by decide)).trans ax
  have cy : env c.mem base 1 = env s.mem base 1 := (ce 1 (by decide)).trans ay
  apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
    rootU (env s.mem base 1))) (by simp only [VG.Arm.eval, cz, avx, au])
  · intro ht
    have ht' := of_decide_eq_true ht
    refine WP.mono (sign_known (kac.ctx hc) lc b (kac.sign.trans hb) _ _ cx cy) fun t ⟨kt, lt, tr⟩ => ?_
    exact ⟨kac.trans kt, lt, by simpa only [recoverResult, ht', ite_true] using tr⟩
  · intro hf
    have hf' := of_decide_eq_false hf
    refine WP.seq (WP.mono (fieldEqual_ok (kac.ctx hc) lc 11 12) fun d ⟨kd, ld, de, dz⟩ => ?_)
    have kacd := kac.trans (IKeep.of_keep kd)
    have dx : env d.mem base 0 = rootX (env s.mem base 1) := (de 0 (by decide)).trans cx
    have dy : env d.mem base 1 = env s.mem base 1 := (de 1 (by decide)).trans cy
    apply WP.ite (decide (rootV (env s.mem base 1) * rootX (env s.mem base 1) * rootX (env s.mem base 1) =
      0 - rootU (env s.mem base 1))) (by simp only [VG.Arm.eval, dz, ce 11 (by decide), ce 12 (by decide), avx, anu])
    · intro ht
      have ht' := of_decide_eq_true ht
      refine WP.seq (WP.mono (fieldCode_ok [.const 18 Spec.Ed25519.sqrtM1, .mulc 0 0 18] (kacd.ctx hc) ld)
        fun e ⟨ke, le, ve⟩ => ?_)
      have ex : env e.mem base 0 = rootX (env s.mem base 1) * Spec.Ed25519.sqrtM1 := by
        rw [ve]; change env d.mem base 0 * Spec.Ed25519.sqrtM1 = _; rw [dx]
      have ey : env e.mem base 1 = env s.mem base 1 := by rw [ve]; exact dy
      have kacde := kacd.trans (IKeep.of_keep ke)
      refine WP.mono (sign_known (kacde.ctx hc) le b (kacde.sign.trans hb) _ _ ex ey) fun t ⟨kt, lt, tr⟩ => ?_
      exact ⟨kacde.trans kt, lt, by rw [recoverResult, ite_eq_right hf', ite_eq_left ht']; exact tr⟩
    · intro hf2
      have hf2' := of_decide_eq_false hf2
      refine WP.mono (recoverInvalid_ok d base) fun t ⟨kt, tm, tr⟩ => ?_
      exact ⟨kacd.trans (IKeep.of_keep kt), tm ▸ ld,
        by simpa only [recoverResult, hf', hf2', ite_false] using tr⟩

end VG.Proof.Ed25519.Arm

end

end

/-! ### `Ed25519.Arm.DecodeKeep`, which this module and modules that import it used -/

section

/-! Decoding writes the saved sign and field workspace only. -/

@[expose] public section

namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

structure DecodeKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest (.r10 :: fclob) s t
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 60, 4⟩, FA b] s.mem t.mem

theorem DecodeKeep.ctx {b : BitVec 32} {s t : State} (h : DecodeKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)
theorem DecodeKeep.trans {b : BitVec 32} {s t u : State} (h : DecodeKeep b s t) (k : DecodeKeep b t u) :
    DecodeKeep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩
theorem DecodeKeep.of_ikeep {b : BitVec 32} {s t : State} (h : IKeep b s t) : DecodeKeep b s t :=
  ⟨h.rest, h.frame.mono (fun _ hr => List.mem_cons_of_mem _ hr)⟩
theorem DecodeKeep.of_keep {b : BitVec 32} {s t : State} (h : Keep b s t) : DecodeKeep b s t :=
  DecodeKeep.of_ikeep (IKeep.of_keep h)

end VG.Proof.Ed25519.Arm

end

end

/-! Merged from `Proof.Ed25519.Arm.SplitYSign`. -/

@[expose] public section

section
/-! Separate bit 255 while retaining all bounded field limbs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem bitNat_eq {q : Nat} (hq : q ≤ 1) : (q == 1).toNat = q := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl <;> rfl

theorem splitYSign_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa (.block splitYSign) s fun t => DecodeKeep base s t ∧ AllLim t.mem base ∧
      V t.mem (State.addr base) (offset 1) = V s.mem (State.addr base) (offset 1) % 2 ^ 255 ∧
      t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
        BitVec.ofNat 32 (V s.mem (State.addr base) (offset 1) / 2 ^ 255 == 1).toNat := by
  let f := limb s.mem (State.addr base) (offset 1)
  have hoff : offset (1 : Slot) = 128 := rfl
  have mf := mask15_facts (hl 1)
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  have r2 : Rest [.r2, .r3, .r4] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have e2 : (s2.gpr .r2).toNat = f 15 / 32768 := by rw [u2.gpr, toNat_shr, u1.gpr]; rfl
  refine str0_ok (hc.of_rest r2 (by decide)) (by decide) fun s3 u3 => ?_
  have m3 : s3.mem = s.mem.writeW (State.addr base + BitVec.ofNat 64 60) (s2.gpr .r2) := by
    rw [u3.mem, u2.mem, u1.mem]
  have f3 : Frame [⟨State.addr base + BitVec.ofNat 64 60, 4⟩] s.mem s3.mem := by
    rw [m3]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have r3 : Rest [.r2, .r3, .r4] s s3 := r2.trans (u3.rest _)
  refine wp_movw fun s4 u4 => wp_dp (op2_reg _ _) fun s5 u5 => ?_
  have r5 : Rest [.r2, .r3, .r4] s s5 := r3.trans ((u4.rest (by decide)).trans (u5.rest (by decide)))
  have e5 : (s5.gpr .r3).toNat = f 15 % 32768 := by
    rw [u5.gpr]
    change (s4.gpr .r3 &&& s4.gpr .r4).toNat = _
    rw [BitVec.toNat_and, u4.gpr, u4.other _ (by decide), u3.gpr, u2.other _ (by decide), u1.gpr]
    change f 15 &&& (2 ^ 15 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  refine str0_ok (hc.of_rest r5 (by decide)) (by decide) fun t ht => WP.block_nil ?_
  have mt : t.mem = s3.mem.writeW (State.addr base + BitVec.ofNat 64 (offset 1 + 60)) (s5.gpr .r3) := by
    rw [ht.mem, u5.mem, u4.mem]
  have ft : Frame [⟨State.addr base + BitVec.ofNat 64 (offset 1), 64⟩] s3.mem t.mem := by
    rw [mt]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (State.addr base) (d := offset 1 + 60) (n := 4) (e := offset 1) (k := 64)
        (by decide) (by decide) (by decide))
  have ys : ∀ k < 16, limb s3.mem (State.addr base) (offset 1) k = f k :=
    limb_frame f3 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by decide)
  have yt : ∀ k < 16, limb t.mem (State.addr base) (offset 1) k = mask15 f k := by
    intro k hk
    rw [limb, mt]
    by_cases hk15 : k = 15
    · subst hk15
      rw [wd_write_self, e5]
      rfl
    · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      change limb s3.mem (State.addr base) (offset 1) k = _
      rw [ys k hk]
      simp only [mask15, hk15, ite_false]
  have lt : AllLim t.mem base := (field_update 1 (smallFrame_lim f3 (by decide) hl) (frame_o16 ft)
    (fun k hk => by rw [yt k hk]; exact mf.2.2.1 k hk)).1
  refine ⟨⟨(r5.trans (ht.rest _)).mono (by decide), ?_⟩, lt, ?_, ?_⟩
  · exact (f3.mono (fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..)).trans
      (ft.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩)
  · rw [V, val16_congr yt]
    have hv : V s.mem (State.addr base) (offset 1) = val16 (mask15 f) 16 + 2 ^ 255 * (f 15 / 32768) := mf.1
    have hb : val16 (mask15 f) 16 < 2 ^ 255 := mf.2.1
    omega_arith
  · apply BitVec.eq_of_toNat_eq
    have hz : wd t.mem (State.addr base) 60 = (s2.gpr .r2).toNat := by
      rw [wd_frame ft (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)),
        wd, m3, Mem.readW_writeW_self32]
    change wd t.mem (State.addr base) 60 = _
    rw [hz, e2, toNat_imm (by have := Bool.toNat_le (V s.mem (State.addr base) (offset 1) / 2 ^ 255 == 1); omega_arith)]
    have he : V s.mem (State.addr base) (offset 1) / 2 ^ 255 = f 15 / 32768 := by
      have hv : V s.mem (State.addr base) (offset 1) = val16 (mask15 f) 16 + 2 ^ 255 * (f 15 / 32768) := mf.1
      have hb : val16 (mask15 f) 16 < 2 ^ 255 := mf.2.1
      omega_arith
    rw [he, bitNat_eq mf.2.2.2]

end VG.Proof.Ed25519.Arm
end

/-! Merged from `Proof.Ed25519.Arm.DecodeLoad`. -/
section
/-! Merged from `Proof.Ed25519.Arm.CanonicalY`. -/
section
/-! Merged from `Proof.Ed25519.Arm.WordsEqual`. -/
section
/-! Compare bounded fields before modular reduction. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem val16_inj {f g : Nat → Nat} {n : Nat} (hf : ∀ k < n, f k < 65536)
    (hg : ∀ k < n, g k < 65536) : (∀ k < n, f k = g k) ↔ val16 f n = val16 g n := by
  refine ⟨val16_congr, fun h k hk => ?_⟩
  exact (val16_div hf hk).symm.trans ((congrArg (fun x => x / 2 ^ (16 * k) % 65536) h).trans (val16_div hg hk))

structure EqualInv (base : BitVec 32) (a b : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r2, .r3, .r9] s₀ s
  mem : s.mem = s₀.mem
  zero : s.gpr .r9 = 0#32 ↔ ∀ i < k, limb s₀.mem (State.addr base) a i = limb s₀.mem (State.addr base) b i

theorem equalLimbs_ok {base : BitVec 32} {s₀ : State} (hc : Ctx base s₀) (a b : Nat)
    (ha : a + 64 ≤ 4096) (hb : b + 64 ≤ 4096) (hz : s₀.gpr .r9 = 0#32) :
    WP isa (.block ((List.range 16).flatMap (equalLimb a b))) s₀ fun t =>
      EqualInv base a b s₀ 16 t := by
  refine wp_range_flatMap (M := isa) (EqualInv base a b s₀) (fun k s hk h => ?_) 16 (Nat.le_refl _) s₀
    ⟨Rest.refl _ _, rfl, ⟨fun _ _ h => by omega_arith, fun _ => hz⟩⟩
  have hcs := hc.of_rest h.rest (by decide)
  refine ldr0_ok hcs (by omega_arith) fun s1 u1 =>
    ldr0_ok (hcs.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)) (by omega_arith) fun s2 u2 =>
    wp_dp (op2_reg _ _) fun s3 u3 => wp_dp (op2_reg _ _) fun t ht => WP.block_nil ?_
  have el : (s2.gpr .r3).toNat = limb s₀.mem (State.addr base) a k := by
    rw [u2.other _ (by decide), u1.gpr, h.mem]; rfl
  have er : (s2.gpr .r2).toNat = limb s₀.mem (State.addr base) b k := by
    rw [u2.gpr, u1.mem, h.mem]; rfl
  have eqv : s2.gpr .r3 = s2.gpr .r2 ↔ limb s₀.mem (State.addr base) a k = limb s₀.mem (State.addr base) b k :=
    ⟨fun h => el.symm.trans ((congrArg BitVec.toNat h).trans er),
      fun h => BitVec.eq_of_toNat_eq (el.trans (h.trans er.symm))⟩
  refine ⟨h.rest.trans ((u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans (ht.rest (by decide))))), by rw [ht.mem, u3.mem, u2.mem, u1.mem, h.mem], ?_⟩
  rw [ht.gpr]
  change (s3.gpr .r9 ||| s3.gpr .r3 = 0#32) ↔ _
  rw [BitVec.or_eq_zero_iff, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), h.zero,
    u3.gpr]
  change (_ ∧ (s2.gpr .r3 ^^^ s2.gpr .r2 = 0#32)) ↔ _
  rw [BitVec.xor_eq_zero_iff, eqv]
  constructor
  · rintro ⟨hpre, hlast⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hpre i hi
    · exact hlast
  · intro h
    exact ⟨fun i hi => h i (by omega_arith), h k (by omega_arith)⟩

theorem wordsEqual_ok {base : BitVec 32} {s : State} (hc : Ctx base s) (a b : Nat)
    (ha : a + 64 ≤ 4096) (hb : b + 64 ≤ 4096)
    (hla : Lim s.mem (State.addr base) a) (hlb : Lim s.mem (State.addr base) b) :
    WP isa (.block (wordsEqual a b)) s fun t => Rest [.r2, .r3, .r9] s t ∧ t.mem = s.mem ∧
      t.z = decide (V s.mem (State.addr base) a = V s.mem (State.addr base) b) := by
  unfold wordsEqual
  rw [List.append_assoc, WP.block_append_iff]
  refine wp_mov (op2_imm (by decide)) fun u hu => WP.block_nil ?_
  rw [WP.block_append_iff]
  refine WP.mono (equalLimbs_ok (hc.of_rest (hu.rest (ws := [.r9]) (by decide)) (by decide)) a b ha hb hu.gpr)
    fun v hv => ?_
  refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
  refine ⟨(hu.rest (by decide)).trans (hv.rest.trans (ht.rest _)), by rw [ht.mem, hv.mem, hu.mem], ?_⟩
  have he : v.gpr .r9 - (0 : BitVec 32) = v.gpr .r9 := BitVec.sub_zero _
  rw [hz, he]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  change (v.gpr .r9 = 0#32) ↔ _
  rw [hv.zero, hu.mem]
  exact val16_inj hla hlb

end VG.Proof.Ed25519.Arm
end

/-! Equality with the canonical representative rejects y >= p. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem canonicalY_ok {s : State} {base : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base) :
    WP isa canonicalY s fun t => Keep base s t ∧ AllLim t.mem base ∧ env t.mem base = env s.mem base ∧
      t.z = decide (V s.mem (State.addr base) (offset 1) < Spec.X25519.P) := by
  refine WP.seq (WP.mono (freezeRaw_ok hc hl 1) fun u ⟨uk, ul, ue, uf, uv, uraw⟩ => ?_)
  refine WP.mono (wordsEqual_ok (uk.ctx hc) (offset 1) FR (by decide) (by decide) (ul 1) uf)
    fun t ⟨tr, tm, tz⟩ => ?_
  refine ⟨uk.trans ⟨tr.mono (by decide), by rw [tm]; exact Frame.refl _ _⟩,
    tm ▸ ul, (congrArg (fun m => env m base) tm).trans ue, ?_⟩
  have vy : V u.mem (State.addr base) (offset 1) = V s.mem (State.addr base) (offset 1) :=
    val16_congr (uraw 1)
  rw [tz, vy, uv]
  change decide (V s.mem (State.addr base) (offset 1) = V s.mem (State.addr base) (offset 1) % Spec.X25519.P) = _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact h ▸ Nat.mod_lt _ (by decide)
  · intro h
    exact (Nat.mod_eq_of_lt h).symm

end VG.Proof.Ed25519.Arm
end

/-! Read canonical y and the encoded sign from the 32 input bytes. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem packedV_decode (m : Mem) (p : Addr) :
    packedV m p = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) := by
  rw [decodeLE_eq]
  exact (leNum_bytesAt2 m p 16).symm

theorem pointDecodeLoad_ok {s : State} {base ptr : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa pointDecodeLoad s fun t => DecodeKeep base s t ∧ AllLim t.mem base ∧
      t.mem.readW (State.addr base + BitVec.ofNat 64 60) 32 =
        BitVec.ofNat 32 (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) / 2 ^ 255 == 1).toNat ∧
      env t.mem base 1 = VG.Proof.X25519.toFe
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255) ∧
      t.z = decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255 < Spec.X25519.P) := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (unpackField_ok hc (o := offset 1) (src := 0) (by decide) (by decide) hp
    (by omega_arith) (by simpa only [Nat.zero_add] using hr) ?_) fun u ⟨ur, uf, ul, uv⟩ => ?_
  · have hp0 : State.addr ptr + BitVec.ofNat 64 0 = State.addr ptr := BitVec.add_zero _
    rw [hp0]
    exact hsep.sub_right (Offset.sub_base _ (by decide))
  have vu : V u.mem (State.addr base) (offset 1) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) :=
    uv.trans ((congrArg (packedV s.mem) (BitVec.add_zero _)).trans (packedV_decode _ _))
  obtain ⟨uk, ull, _⟩ := field_finish 1 hl (ur.mono (by decide)) (frame_o16 uf) ul (v := FS u.mem (State.addr base) (offset 1)) rfl
  refine WP.mono (splitYSign_ok (uk.ctx hc) ull) fun v ⟨vk, vl, vy, vs⟩ => ?_
  have kv : DecodeKeep base s v := (DecodeKeep.of_keep uk).trans vk
  have ve : env v.mem base 1 = VG.Proof.X25519.toFe
      (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255) :=
    congrArg VG.Proof.X25519.toFe (vy.trans (congrArg (· % 2 ^ 255) vu))
  refine WP.mono (canonicalY_ok (kv.ctx hc) vl) fun t ⟨tk, tl, te, tz⟩ => ?_
  refine ⟨kv.trans (DecodeKeep.of_keep tk), tl, ?_, (congrFun te 1).trans ve, ?_⟩
  · rw [tk.sign, vs, vu]
  · rw [tz, vy, vu]

end VG.Proof.Ed25519.Arm
end

/-! The public byte decoder matches the reviewed strict specification. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {umaal : Bool}

theorem pointDecode_ok {s : State} {base ptr : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa (pointDecode umaal) s fun t => DecodeKeep base s t ∧ AllLim t.mem base ∧
      DecodeResult base (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32)) t := by
  have hlen : (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  refine WP.seq (WP.mono (pointDecodeLoad_ok hc hl hp hfit hr hsep) fun a ⟨ak, al, asign, ay, az⟩ => ?_)
  apply WP.ite (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255 < Spec.X25519.P))
    (by simp only [VG.Arm.eval, az])
  · intro ht
    have hy := of_decide_eq_true ht
    refine WP.mono (recoverPoint_ok (ak.ctx hc) al _ asign) fun t ⟨tk, tl, tr⟩ => ?_
    refine ⟨ak.trans (DecodeKeep.of_ikeep tk), tl, ?_⟩
    rw [decodePoint32 _ hlen, ite_eq_left hy]
    rw [ay] at tr
    exact tr
  · intro hf
    have hy := of_decide_eq_false hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨tk, tm, tr⟩ => ?_
    refine ⟨ak.trans (DecodeKeep.of_keep tk), tm ▸ al, ?_⟩
    rw [decodePoint32 _ hlen, ite_eq_right hy]
    exact tr

end VG.Proof.Ed25519.Arm
