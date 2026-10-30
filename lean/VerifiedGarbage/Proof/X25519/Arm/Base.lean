module

public import VerifiedGarbage.Impl.X25519.Arm.Base
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
meta import VerifiedGarbage.Impl.X25519.Arm.Base
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseVerified
public import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.Ed25519.Arm.CombLoop
meta import VerifiedGarbage.Proof.Ed25519.Arm.CombLoop
import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
meta import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
meta import VerifiedGarbage.Proof.Ed25519.Arm.PointAffine
import VerifiedGarbage.Proof.Ed25519.Arm.Freeze
meta import VerifiedGarbage.Proof.Ed25519.Arm.Freeze
import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg
meta import VerifiedGarbage.Proof.Ed25519.Arm.FieldProg
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
meta import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.X25519.Bytes
meta import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.X25519.Edwards.Base
meta import VerifiedGarbage.Proof.X25519.Edwards.Base
import VerifiedGarbage.Proof.X25519.Edwards.Ladder
meta import VerifiedGarbage.Proof.X25519.Edwards.Ladder
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Arm.NativeTaint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# X25519 of the base point on ARMv7

The scalar's copy, clamped (`clampBytes_ok`), decodes to `decodeScalar25519` of the scalar
(`decode_clamp`); the comb computes `[k] B` from it (`combFrom_ok`), and `uEncode` its
u-coordinate `(Z + Y) / (Z - Y)`, which `Proof/X25519/Edwards/Ladder.lean` shows is
`X25519(k, 9)` (`engine_ok`). The wrapper is `vg_ed25519_scalar_base`'s, whose contract it
shares but for the result.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm.Base

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Impl.X25519.Arm.Base
open VG.Proof.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Proof.Ed25519 (Rep baseAff)

/-! ## The clamp -/

/-- `decodeScalar25519`'s clamping of 32 bytes. -/
def clampL (kb : List Byte) : List Byte :=
  let k := kb.set 0 (kb.getD 0 0 &&& 248)
  k.set 31 ((k.getD 31 0 &&& 127) ||| 64)

theorem decode_clamp {kb : List Byte} (hk : kb.length = 32) :
    Spec.X25519.decodeScalar25519 kb = Spec.Ed25519.decodeLE (clampL kb) := by
  have hl : (clampL kb).length = 32 := by simp [clampL, hk]
  rw [Proof.Ed25519.decodeLE_eq, ← Proof.X25519.take_32 hl, ← Proof.X25519.decodeLittleEndian_eq]
  rfl

private theorem and248 : ∀ x : BitVec 8, ((x.setWidth 32 &&& (248 : BitVec 32)).setWidth 8) = x &&& 248 := by
  decide

private theorem clamp31 : ∀ x : BitVec 8,
    (((x.setWidth 32 &&& (127 : BitVec 32)) ||| (64 : BitVec 32)).setWidth 8) = (x &&& 127) ||| 64 := by
  decide

theorem clampBytes_ok {s : State} {b : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx b s) :
    WP isa (.block clampBytes) s fun t => Rest [.r1] s t ∧ Frame [scalR b] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr b + BitVec.ofNat 64 SCAL) 32 =
        clampL (Spec.Ed25519.bytesAt s.mem (State.addr b + BitVec.ofNat 64 SCAL) 32) := by
  have hfb := hc.fit
  let a : Nat → Addr := fun k => State.addr b + BitVec.ofNat 64 (SCAL + k)
  have ha : ∀ k, k < 32 → State.addr (s.gpr .r0 + BitVec.ofNat 32 (SCAL + k)) = a k := fun k hk => by
    rw [hc.r0]; exact addr_add (by simp only [SCAL]; omega)
  have hin : ∀ k, k < 32 → InRegions s.wr (a k) 1 := fun k hk =>
    in_base hc.wr (by simp only [SCAL]; omega) (by simp only [SCAL]; omega)
  have ne : ∀ i k, i < 32 → k < 32 → i ≠ k → a i ≠ a k := fun i k hi hk hik he =>
    Offset.disjoint (State.addr b) (d := SCAL + i) (n := 1) (e := SCAL + k) (k := 1)
      (by omega) (by simp only [SCAL]; omega) (by simp only [SCAL]; omega) _
      (Region.contains_self _ _)
      (by change Region.Contains ⟨a k, 1⟩ (a i) 1; rw [he]; exact Region.contains_self _ _)
  have a0 : State.addr b + BitVec.ofNat 64 SCAL = a 0 := rfl
  unfold clampBytes
  refine wp_ldrb (a := a 0) (by decide) (ha 0 (by decide))
    (by obtain ⟨r, hr, hc'⟩ := hin 0 (by decide); exact ⟨r, List.mem_append_right _ hr, hc'⟩)
    fun s₁ u₁ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_strb (a := a 0) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact ha 0 (by decide))
    (by rw [u₂.wr, u₁.wr]; exact hin 0 (by decide)) fun s₃ u₃ => ?_
  have m3 : s₃.mem = s.mem.writeW (a 0) (s.mem (a 0) &&& 248) := by
    rw [u₃.mem, u₂.gpr, dpVal, u₁.gpr, u₂.mem, u₁.mem, and248]
  refine wp_ldrb (a := a 31) (by decide)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]; exact ha 31 (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        obtain ⟨r, hr, hc'⟩ := hin 31 (by decide); exact ⟨r, List.mem_append_right _ hr, hc'⟩)
    fun s₄ u₄ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₅ u₅ => wp_dp (op2_imm (by decide)) fun s₆ u₆ => ?_
  refine wp_strb (a := a 31) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]; exact ha 31 (by decide))
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hin 31 (by decide))
    fun t u₇ => WP.block_nil ?_
  have v31 : s₃.mem (a 31) = s.mem (a 31) := by
    rw [m3, VG.WriteBytes.writeW8_apply, ite_eq_right (ne 31 0 (by decide) (by decide) (by decide))]
  have mt : t.mem = (s.mem.writeW (a 0) (s.mem (a 0) &&& 248)).writeW (a 31)
      ((s.mem (a 31) &&& 127) ||| 64) := by
    rw [u₇.mem, u₆.gpr, dpVal, u₅.gpr, dpVal, u₄.gpr, u₆.mem, u₅.mem, u₄.mem, clamp31, v31, m3]
  refine ⟨(u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest _).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans (u₇.rest _)))))),
    ?_, ?_⟩
  · rw [mt]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by simp only [SCAL]; omega) (by simp only [SCAL]; omega) (by simp only [SCAL]; omega))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains _ (by simp only [SCAL]; omega) (by simp only [SCAL]; omega) (by simp only [SCAL]; omega))
  · apply List.ext_getElem
    · simp [Spec.Ed25519.bytesAt, clampL]
    · intro i hi _
      have hi' : i < 32 := by simpa [Spec.Ed25519.bytesAt] using hi
      have ai : State.addr b + BitVec.ofNat 64 SCAL + BitVec.ofNat 64 i = a i := Offset.add_add _ _ _
      simp only [Spec.Ed25519.bytesAt, clampL, List.getElem_map, List.getElem_range, List.getElem_set,
        List.getD_eq_getElem?_getD, List.getElem?_set, List.length_map,
        List.length_range, ai, mt, VG.WriteBytes.writeW8_apply]
      by_cases h31 : i = 31
      · subst h31
        simp [a, Offset.add_add]
      · by_cases h0 : i = 0
        · subst h0
          simp
          rw [ite_eq_right (ne 0 31 (by decide) (by decide) (by decide))]
          rfl
        · simp [ne i 31 hi' (by decide) h31, ne i 0 hi' (by decide) h0, Ne.symm h31, Ne.symm h0]

/-! ## The engine -/

theorem uOps_eval (e : Env) :
    evalOps uOps e 0 = e 2 + e 1 ∧ evalOps uOps e 2 = e 2 - e 1 := by
  simp [uOps, evalOps, evalOp, Function.update]

/-- The slots cleared, and the scalar copied and clamped. -/
theorem prep_ok {s : State} {base ptr T : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩)
    (hT : TblAt s T) (hsym : s.syms combSym = T) (apart : (TBL T).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa (.block (initFields ++ combCopy ++ clampBytes)) s fun v => PointKeep base s v ∧
      AllLim v.mem base ∧ TblAt v T ∧ v.syms combSym = T ∧
      Spec.Ed25519.bytesAt v.mem (State.addr (base + BitVec.ofNat 32 SCAL)) 32 =
        clampL (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) := by
  have hfb := hc.fit
  have fa : (VG.Proof.Ed25519.Arm.FA base).Sub ⟨State.addr base, 8192⟩ := Offset.sub_base _ (by decide)
  have sub : (scalR base).Sub ⟨State.addr base, 8192⟩ := Offset.sub_base _ (by decide)
  have hk : (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (initFields_rest hc) fun a ⟨ak, ar, al, _⟩ sya => ?_
  have hca := ak.ctx hc
  rw [WP.block_append_iff]
  refine WP.mono_syms (combCopy_ok hca ((ar.gpr _ (by decide)).trans hp) hfit
    (by rw [ak.rest.rd, ak.rest.wr]; exact hr) (hsep.sub_right sub)) fun u ⟨ru, fu, cu⟩ syu => ?_
  have hcu := hca.of_rest ru (by decide)
  refine WP.mono_syms (clampBytes_ok hcu) fun v ⟨rv, fv, cv⟩ syv => ?_
  have kav : PointKeep base a v := (PointKeep.of_small ru (by decide) fu (by decide) (by decide)).trans
    (PointKeep.of_small rv (by decide) fv (by decide) (by decide))
  have hcv := kav.ctx hca
  have apartS : ∀ sl : Slot, ∀ k < 16, (⟨State.addr base + BitVec.ofNat 64 (offset sl + 4 * k), 4⟩ : Region).Disjoint
      (scalR base) := fun sl =>
    slot_apart sl (.inr (by simp only [offset, SCAL]; have := sl.isLt; omega)) (by decide)
  have lv : AllLim v.mem base := fun sl =>
    (env_frame fv sl (apartS sl)).2 ((env_frame fu sl (apartS sl)).2 (al sl))
  have tsc : ∀ r ∈ [scalR base], (TBL T).Disjoint r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right sub
  have tv : TblAt v T :=
    (((hT.of_frame (by rw [ak.rest.rd, ak.rest.wr]) ak.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact apart.sub_right fa).of_frame (by rw [ru.rd, ru.wr]) fu tsc).of_frame
      (by rw [rv.rd, rv.wr]) fv tsc)
  have ua : Spec.Ed25519.bytesAt a.mem (State.addr ptr) 32 = Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 := by
    unfold Spec.Ed25519.bytesAt
    exact List.map_congr_left fun n hn => ak.frame.bytes (R := ⟨State.addr ptr, 32⟩)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hsep.sub_right fa)
      (show (32 : Nat) ≤ 2 ^ 64 by decide) (List.mem_range.mp hn)
  have hsc : Spec.Ed25519.bytesAt u.mem (State.addr base + BitVec.ofNat 64 SCAL) 32 =
      Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32 := by
    rw [← ua]
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun n hn => ?_
    rw [Offset.add_add]
    exact cu n (List.mem_range.mp hn)
  have hpa : State.addr (base + BitVec.ofNat 32 SCAL) = State.addr base + BitVec.ofNat 64 SCAL :=
    addr_add (by simp only [SCAL]; omega)
  exact ⟨(PointKeep.of_keep ak).trans kav, lv, tv, by rw [syv, syu, sya]; exact hsym, by rw [hpa, cv, hsc]⟩

theorem engine_ok {s : State} {base ptr T : BitVec 32} (hc : VG.Proof.Ed25519.Arm.Ctx base s)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩)
    (hT : TblAt s T) (hsym : s.syms combSym = T) (apart : (TBL T).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa engine s fun t => PointKeep base s t ∧ Lim t.mem (State.addr base) FR ∧
      Spec.X25519.x25519 (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) Spec.X25519.basePoint =
        Spec.Ed25519.encodeLE 32 (V t.mem (State.addr base) FR) := by
  have hk : (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  rw [engine]
  refine WP.seq (WP.mono (prep_ok hc hp hfit hr hsep hT hsym apart) fun v ⟨kav, lv, tv, syv, cv⟩ => ?_)
  have hcv := kav.ctx hc
  refine WP.seq (WP.mono (combInit_ok hcv lv tv syv apart) fun w ⟨kw, E, I⟩ => ?_)
  rw [cv, ← decode_clamp hk] at I
  have hS : Spec.X25519.decodeScalar25519 (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) < 2 ^ 256 := by
    have h := VG.Proof.X25519.Edwards.decodeScalar25519_shift hk
    rw [Nat.shiftRight_eq_div_pow] at h
    have := (Nat.div_eq_zero_iff_lt (by positivity)).mp h
    omega
  refine WP.seq (WP.mono (combFrom_ok E I hS) fun x ⟨kx, lx, rx⟩ => ?_)
  have hcx := (kav.trans (kw.trans kx)).ctx hc
  rw [uEncode]
  refine WP.seq (WP.mono (fieldCode_ok uOps hcx lx) fun y ⟨ky, ly, ey⟩ => ?_)
  have hcy := ky.ctx hcx
  refine WP.seq (WP.mono (pointAffine_ok hcy ly) fun z ⟨kz, lz, zx, _⟩ => ?_)
  have hcz := (PointKeep.of_ikeep kz).ctx hcy
  refine WP.mono (freeze_ok hcz lz 0) fun t ⟨kt, _, _, lt, vt⟩ => ?_
  refine ⟨(kav.trans (kw.trans (kx.trans ((PointKeep.of_keep ky).trans
    ((PointKeep.of_ikeep kz).trans (PointKeep.of_keep kt)))))), lt, ?_⟩
  rw [VG.Proof.X25519.Edwards.x25519_basePoint hk _ (VG.Proof.X25519.Edwards.u_rep rx), vt, zx, ey,
    (uOps_eval _).1, (uOps_eval _).2]
  rfl

/-! ## The wrapper -/

/-- `vg_ed25519_scalar_base`'s contract, with X25519's result. -/
def baseLocal : Contract Arm.isa :=
  { scalarBaseLocal with
    post := fun s t => Spec.Ed25519.bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
      Spec.X25519.x25519 (Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32) Spec.X25519.basePoint }

theorem x25519Base_correct {s : State} (h : ScalarBasePre s) :
    WP isa x25519Base s fun t => abiPreserved s t ∧ baseLocal.post s t := by
  refine WP.seq (WP.mono_syms (scalarBaseSetup_ok h) fun u ⟨hcu, pu, su, ou, lu, ku, fu⟩ syu => ?_)
  have input : (⟨State.addr (s.gpr .r1), 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine WP.seq (WP.mono (engine_ok hcu pu h.f1
    (fun n hn => by rw [ku.rd, ku.wr]; exact in_base input (by omega) (by omega)) h.scalar_ws
    (h.tbl_of (by rw [ku.rd, ku.wr]) fu) (by rw [syu]) h.tbl_ws)
    fun v ⟨kv, lv, vv⟩ => ?_)
  have sv : ScalarSaved (State.addr (s.gpr .r2)) s.gpr v.mem :=
    su.frame kv.frame fun r hr i hi => by
      simp only [pointRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  have ov : v.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 48) 32 = s.gpr .r0 :=
    (kv.word 48 (.inl rfl) (by decide)).trans ou
  refine WP.mono (scalarBaseFinish_ok (kv.ctx hcu) lv ov h.f0
    (by rw [kv.rest.wr, ku.wr, h.wr]; simp) h.out_ws sv) fun t ⟨gt, kt, lt, _, bt⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [kt.sp, kv.rest.sp, ku.sp]⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact gt 0 (by decide)
    · exact gt 1 (by decide)
    · exact gt 2 (by decide)
    · exact gt 3 (by decide)
    · exact gt 4 (by decide)
    · exact gt 5 (by decide)
    · exact gt 6 (by decide)
    · exact gt 7 (by decide)
    · rw [lt, kv.word LRS (.inr (by decide)) (by decide), lu]
  · have hb : Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r1)) 32 =
        Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32 := by
      unfold Spec.Ed25519.bytesAt
      refine List.map_congr_left fun n hn => fu.bytes (R := ⟨State.addr (s.gpr .r1), 32⟩)
        (fun r hr => ?_) (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hn)
      rw [List.mem_singleton.mp hr]
      exact h.scalar_ws.sub_right (Region.sub_prefix (by decide))
    change Spec.Ed25519.bytesAt t.mem _ 32 =
      Spec.X25519.x25519 (Spec.Ed25519.bytesAt s.mem _ 32) Spec.X25519.basePoint
    rw [bt, ← hb, vv]


/-! ## Constant time -/

/-- Between the preparation and the comb's start, in each run. -/
def Mid (b T : BitVec 32) (s : State) : Prop :=
  VG.Proof.Ed25519.Arm.Ctx b s ∧ AllLim s.mem b ∧ TblAt s T ∧ s.syms combSym = T ∧
    (TBL T).Disjoint ⟨State.addr b, 8192⟩

def prepCT : Prog isa := .block (initFields ++ combCopy ++ clampBytes)
def initCT : Prog isa := combInit

materialize_code prepCT
materialize_code initCT
materialize_code uEncode

theorem engine_ct (b p T : BitVec 32) :
    CT (fun x y => BaseCTPre b p T x ∧ BaseCTPre b p T y) engine (fun _ _ => True) := by
  have h1 : CT (fun x y => BaseCTPre b p T x ∧ BaseCTPre b p T y) prepCT
      (fun x y => Mid b T x ∧ Mid b T y) := by
    apply ctBoth
    · apply ctRegs [.r0, .r12] _ (by native_taint_decide)
      intro x y h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.r0.trans h.2.1.r0.symm
      · exact h.1.2.1.trans h.2.2.1.symm
    · intro s ⟨hc, hp, hfit, hr, hsep, hT, hsym, apart⟩
      exact WP.mono (prep_ok hc hp hfit hr hsep hT hsym apart) fun v ⟨kv, lv, tv, sv, _⟩ =>
        ⟨kv.ctx hc, lv, tv, sv, apart⟩
  have h2 : CT (fun x y => Mid b T x ∧ Mid b T y) initCT
      (fun x y => CombRun b T 0 x ∧ CombRun b T 0 y) := by
    apply ctBoth
    · apply ctRegs [.r0] _ (by native_taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · intro s ⟨hc, hl, hT, hsym, apart⟩
      exact WP.mono (combInit_ok hc hl hT hsym apart) fun w ⟨_, E, I⟩ => ⟨w, _, _, E, I⟩
  have h4 : CT (fun x y => VG.Proof.Ed25519.Arm.Ctx b x ∧ VG.Proof.Ed25519.Arm.Ctx b y) uEncode
      (fun _ _ => True) := by
    apply ctRegs [.r0] _ (by native_taint_decide)
    intro x y h r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.1.r0.trans h.2.r0.symm
  exact RelCT.seq h1 (RelCT.seq h2 (RelCT.seq (combLoop_ct b T) h4))

theorem work_ct (b p out T : BitVec 32) :
    CT (fun x y => BaseWorkCTPre b p out T x ∧ BaseWorkCTPre b p out T y)
      engine (fun x y => BaseFinishCTPre b out x ∧ BaseFinishCTPre b out y) := by
  apply ctBoth
  · exact (engine_ct b p T).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h)
  · intro s ⟨⟨hc, hp, hf, hr, hsep, hT, hsym, apart⟩, ho⟩
    refine WP.mono (engine_ok hc hp hf hr hsep hT hsym apart) fun t ⟨tk, _, _⟩ => ?_
    exact ⟨tk.ctx hc, (tk.word 48 (.inl rfl) (by decide)).trans ho⟩

theorem x25519Base_ct : ConstantTime isa baseLocal.pre baseLocal.pub x25519Base := by
  have hct (b p out T : BitVec 32) :
      CT (fun x y => BaseWrapCTPre b p out T x ∧ BaseWrapCTPre b p out T y) x25519Base (fun _ _ => True) :=
    RelCT.seq (scalarBaseSetup_ct b p out T)
      (RelCT.seq (work_ct b p out T) (scalarBaseFinish_ct b out))
  intro s t tx ty u v hs ht ⟨_, h0, h1, h2, hT⟩ ex ey
  exact (hct (s.gpr .r2) (s.gpr .r1) (s.gpr .r0) (s.syms combSym) _ _ _ _ _ _
    ⟨⟨hs, rfl, rfl, rfl, rfl⟩, ⟨ht, h0.symm, h1.symm, h2.symm, hT.symm⟩⟩ ex ey).1

/-! ## The contract -/

abbrev baseSpec : Contract isa := Spec.X25519.x25519BaseContract (Arm.abi.withConsts combConsts)

theorem base_abi_pre {s : State} (h : (Spec.X25519.x25519BaseContract Arm.abi).pre s) :
    s.rd = [⟨State.addr (s.gpr .r1), 32⟩] ∧ s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r2), 8192⟩] ∧
      (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 32⟩ ∧
      (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩ ∧
      (⟨State.addr (s.gpr .r1), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩ ∧
      (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32 := by
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
     Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
  exact h.2

theorem base_pre {s : State} (h : baseSpec.pre s) : baseLocal.pre s := by
  have hp : (Spec.X25519.x25519BaseContract Arm.abi).pre (stripConsts combConsts s) ∧
      ConstsOk combConsts 0 s := pre_consts.mp h
  obtain ⟨rd, wr, d1, d2, d3, f0, f1, f2⟩ := base_abi_pre hp.1
  simp only [stripConsts, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr] at rd wr d1 d2 d3 f0 f1 f2
  have hk := hp.2
  have mem : (combSym, combWords) ∈ combConsts := List.mem_singleton_self _
  have fit := hk.fit mem
  rw [combWords_length] at fit
  have dj : ∀ r ∈ s.wr, (TBL (s.syms combSym)).Disjoint r :=
    (hk.2.2.1 _ (by rw [combConsts_regs]; exact List.mem_singleton_self _)).2.1
  refine ⟨?_, wr, d1, d2, d3, f0, f1, f2, fit, fun j hj => ?_,
    dj _ (by rw [wr]; exact List.mem_cons_self), dj _ (by rw [wr]; exact List.mem_cons_of_mem _ List.mem_cons_self)⟩
  · have e1 := hk.1
    rw [combConsts_regs] at e1
    have hl : combConsts.length = 1 := rfl
    rw [hl] at e1 rd
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, e1, rd, List.singleton_append]
  · have hw := hk.2.1 _ mem j (by rw [combWords_length]; exact hj)
    dsimp only at hw
    rw [combWords_getD hj] at hw
    exact hw

theorem x25519Base_ok (s : State) (hs : baseLocal.pre s) :
    ∃ t s', Exec isa x25519Base s t s' ∧ abiPreserved s s' ∧ baseLocal.post s s' :=
  x25519Base_correct (ScalarBasePre.of hs)

theorem base_sat : baseSpec.pre baseSatState := by
  have held := baseSatMem_held
  generalize eqs : baseSatState = s
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
     Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr,
    combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst s
  rw [combWords_length]
  rw [combWords_length] at held
  refine ⟨by decide, by decide, held, by decide, ?_, by decide, by decide, by decide,
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), by decide, by decide, by decide⟩
  intro r hr
  change r ∈ [⟨0x1000, 32⟩, ⟨0x3000, 8192⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)


theorem base_implies : baseLocal.Implies baseSpec where
  pre _ h := base_pre h
  post := by
    intro s s' _ h
    sig_post [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig, 
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, combConsts_eq, Abi.withConsts]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig, 
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, combConsts_eq,
      Abi.withConsts] at h
    obtain ⟨hsp, hsy, h0, h1, h2⟩ := h
    exact ⟨hsp, h0, h1, h2, hsy⟩
  sat := ⟨baseSatState, base_sat⟩

theorem x25519Base_verified : Verified Arm.target x25519Base baseSpec :=
  Verified.of_correct x25519Base_ok x25519Base_ct base_implies


end VG.Proof.X25519.Arm.Base
