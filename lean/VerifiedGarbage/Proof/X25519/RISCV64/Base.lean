module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarBase
public import VerifiedGarbage.Impl.X25519.RISCV64.Base
public import VerifiedGarbage.Spec.X25519
import VerifiedGarbage.Proof.Ed25519.RISCV64.Comb
import VerifiedGarbage.Proof.Ed25519.RISCV64.Encode
import VerifiedGarbage.Proof.Ed25519.RISCV64.Freeze
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointScalar
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.X25519.Edwards.Base
import VerifiedGarbage.Proof.X25519.Edwards.Ladder
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# `vg_x25519_base` on RISC-V: correctness

As on ARMv7 (`Proof/X25519/Arm/Base.lean`): the scalar's copy, clamped
(`clampCopy_ok`), is `decodeScalar25519`'s (`decode_clamp`); the comb
computes `[k] B` from it (`combRun_ok`), and `uEncode` its u-coordinate
`(Z + Y) / (Z - Y)`, which `Proof/X25519/Edwards/Ladder.lean` shows is
`X25519(k, 9)` (`engine_ok`). The wrapper is `vg_ed25519_scalar_base`'s
(`baseWrap_ok`), whose precondition it shares but for the result.
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64.Base

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Impl.X25519.RISCV64.Base
open VG.Proof.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
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

private theorem and248 : ∀ x : BitVec 8,
    ((x.setWidth 64 &&& BitVec.ofInt 64 248).setWidth 8) = x &&& 248 := by
  decide

private theorem clamp31 : ∀ x : BitVec 8,
    (((x.setWidth 64 &&& BitVec.ofInt 64 127) ||| BitVec.ofInt 64 64).setWidth 8) = (x &&& 127) ||| 64 := by
  decide

theorem wp_ori {s : State} {is : List Instr} {Q : State → Prop} {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n ||| BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .or d n imm :: is)) s Q :=
  WP.cons (exec_logicImm h) (k _ (Upd.write _ _ _))

theorem clampCopy_ok {s : State} {b : Addr} (hc : Ctx8 b s) :
    WP isa (.block clampCopy) s fun t => Rest [.a4] s t ∧ Frame [scalR b] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (scalAt b) 32 = clampL (Spec.Ed25519.bytesAt s.mem (scalAt b) 32) := by
  have hS : SCAL = 1152 := rfl
  let a : Nat → Addr := fun k => b + BitVec.ofNat 64 (SCAL + k)
  have hin : ∀ k, k < 32 → InRegions s.wr (a k) 1 := fun k hk =>
    in_base hc.wr (d := SCAL + k) (n := 1) (by omega) (by omega)
  have ne : ∀ i k, i < 32 → k < 32 → i ≠ k → a i ≠ a k := fun i k hi hk hik he =>
    Offset.disjoint b (d := SCAL + i) (n := 1) (e := SCAL + k) (k := 1)
      (by omega) (by omega) (by omega) _ (Region.contains_self _ _)
      (by change Region.Contains ⟨a k, 1⟩ (a i) 1; rw [he]; exact Region.contains_self _ _)
  have a0 : b + BitVec.ofNat 64 SCAL = a 0 := rfl
  unfold clampCopy
  refine wp_lbu (a := a 0) (by decide) (by rw [hc.a3]; rfl) (by
      obtain ⟨r, hr, hc'⟩ := hin 0 (by decide); exact ⟨r, List.mem_append_right _ hr, hc'⟩)
    fun s₁ u₁ => ?_
  refine wp_andi' (by decide) fun s₂ u₂ => ?_
  refine wp_sb (a := a 0) (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hc.a3]; rfl)
    (by rw [u₂.wr, u₁.wr]; exact hin 0 (by decide)) fun s₃ u₃ => ?_
  have m3 : s₃.mem = s.mem.writeW (a 0) (s.mem (a 0) &&& 248) := by
    rw [u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, and248]
  refine wp_lbu (a := a 31) (by decide)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hc.a3])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        obtain ⟨r, hr, hc'⟩ := hin 31 (by decide); exact ⟨r, List.mem_append_right _ hr, hc'⟩)
    fun s₄ u₄ => ?_
  refine wp_andi' (by decide) fun s₅ u₅ => wp_ori (by decide) fun s₆ u₆ => ?_
  refine wp_sb (a := a 31) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), hc.a3])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hin 31 (by decide))
    fun t u₇ => WP.block_nil ?_
  have v31 : s₃.mem (a 31) = s.mem (a 31) := by
    rw [m3, VG.WriteBytes.writeW8_apply, ite_eq_right (ne 31 0 (by decide) (by decide) (by decide))]
  have mt : t.mem = (s.mem.writeW (a 0) (s.mem (a 0) &&& 248)).writeW (a 31)
      ((s.mem (a 31) &&& 127) ||| 64) := by
    rw [u₇.mem, u₆.gpr, u₅.gpr, u₄.gpr, u₆.mem, u₅.mem, u₄.mem, clamp31, v31, m3]
  refine ⟨(u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest _).trans
    ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans (u₇.rest _)))))),
    ?_, ?_⟩
  · rw [mt]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  · apply List.ext_getElem
    · simp [Spec.Ed25519.bytesAt, clampL]
    · intro i hi _
      have hi' : i < 32 := by simpa [Spec.Ed25519.bytesAt] using hi
      have ai : scalAt b + BitVec.ofNat 64 i = a i := Offset.add_add _ _ _
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

theorem engine_ok : EngineOk engine (fun kb => Spec.X25519.x25519 kb Spec.X25519.basePoint) := by
  intro b s p T hc hws h14 hin hpd hT hsym apart
  have hk : (Spec.Ed25519.bytesAt s.mem p 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  have sub : (scalR b).Sub ⟨b, 8192⟩ := Offset.sub_base _ (by decide)
  have hF := FR_eq
  unfold engine
  refine WP.seq (WP.mono_syms (initFields_ok hc.ctx) fun s1 ⟨r1, f1⟩ sy1 => ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest r1 (by decide)
  have hb1 : Spec.Ed25519.bytesAt s1.mem p 32 = Spec.Ed25519.bytesAt s.mem p 32 := by
    simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
    intro i hi
    exact bytes_ws f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega)) hpd (by decide)
      (List.mem_range.mp hi)
  have hT1 : TblAt s1 T := hT.of_frame (by rw [r1.rd, r1.wr]) f1 fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right (Offset.sub_base _ (by decide))
  rw [combClamped, WP.seq_iff]
  refine WP.seq (WP.mono_syms (combCopy_ok hc1 (by rw [r1.gpr _ (by decide), h14])
    (fun i hi => by rw [r1.rd, r1.wr]; exact hin i hi) (hpd.sub_right sub)) fun u ⟨ru, fu, cu⟩ syu => ?_)
  have hcu : Ctx8 b u := hc1.of_rest ru (by decide)
  refine WP.seq (WP.mono_syms (clampCopy_ok hcu) fun v ⟨rv, fv, cv⟩ syv => ?_)
  have hcv : Ctx8 b v := hcu.of_rest rv (by decide)
  have tsc : ∀ r ∈ [scalR b], (TBL T).Disjoint r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right sub
  have hTv : TblAt v T := (hT1.of_frame (by rw [ru.rd, ru.wr]) fu tsc).of_frame (by rw [rv.rd, rv.wr]) fv tsc
  have hsc : Spec.Ed25519.bytesAt u.mem (scalAt b) 32 = Spec.Ed25519.bytesAt s.mem p 32 := by
    rw [← hb1]
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun n hn => ?_
    rw [scalAt, Offset.add_add]
    exact cu n (List.mem_range.mp hn)
  refine WP.mono (combRun_ok hcv (((hws.of_rest r1).of_rest ru).of_rest rv) hTv (by rw [syv, syu, sy1, hsym]) apart)
    fun x ⟨rx, fx, px⟩ => ?_
  rw [cv, hsc, ← decode_clamp hk] at px
  have hcx : Ctx8 b x := hcv.of_rest rx (by decide)
  have wsx : WS b x := (((hws.of_rest r1).of_rest ru).of_rest rv).of_rest rx
  unfold uEncode
  refine WP.seq (WP.mono (fieldCode_ok uOps hcx.ctx wsx) fun y ⟨ky, ey⟩ => ?_)
  have hcy : Ctx8 b y := hcx.of_keep ky
  refine WP.seq (WP.mono (pointAffine_ok hcy) fun z ⟨kz, e0, _⟩ => ?_)
  have hcz : Ctx8 b z := hcy.of_keep kz
  refine WP.mono (freeze_ok hcz.ctx 0) fun t ⟨rt, ft, _, vt⟩ => ⟨?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((ru.mono (by decide)).trans ((rv.mono (by decide)).trans
      ((rx.mono (by decide)).trans ((ky.rest.mono (by decide)).trans ((kz.rest.mono (by decide)).trans
        (rt.mono (by decide)))))))
  · have fr : ∀ r ∈ ([⟨b + BitVec.ofNat 64 FR, 64⟩] : List Region), ∃ r' ∈ [FA b], r.Sub r' := fun r hr =>
      ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩
    exact (f1.mono (by simp)).trans ((fu.mono (by simp)).trans ((fv.mono (by simp)).trans
      ((fx.mono (by simp)).trans ((ky.frame.mono (by simp)).trans ((kz.frame.mono (by simp)).trans
        ((ft.sub fr).mono (by simp)))))))
  · show _ = Spec.X25519.x25519 _ _
    rw [VG.Proof.X25519.Edwards.x25519_basePoint hk (env z.mem b 0) ?_]
    · rw [vt, ← env_val]; rfl
    · rw [e0, ey, (uOps_eval _).1, (uOps_eval _).2]
      exact VG.Proof.X25519.Edwards.u_rep px

/-! ## The function -/

theorem x25519Base_ok {s : State} (hp : BasePre s) :
    WP isa x25519Base s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.gpr .ra = s.gpr .ra ∧
      Spec.Ed25519.bytesAt t.mem (s.gpr .a0) 32 =
        Spec.X25519.x25519 (Spec.Ed25519.bytesAt s.mem (s.gpr .a1) 32) Spec.X25519.basePoint := by
  unfold x25519Base
  exact baseWrap_ok (R := fun kb => Spec.X25519.x25519 kb Spec.X25519.basePoint)
    (fun hc hws h14 hin hpd hT hsym apart => engine_ok hc hws h14 hin hpd hT hsym apart) hp

end VG.Proof.X25519.RISCV64.Base
