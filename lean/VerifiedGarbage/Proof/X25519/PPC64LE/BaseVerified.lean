module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Comb
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Comb
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
public import VerifiedGarbage.Impl.X25519.PPC64LE.Base
public import VerifiedGarbage.Spec.X25519
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Encode
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointScalar
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointMul
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
import VerifiedGarbage.Proof.X25519.Edwards.Base
import VerifiedGarbage.Proof.X25519.Edwards.Ladder
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
meta import VerifiedGarbage.Impl.X25519.PPC64LE.Base
meta import VerifiedGarbage.Spec.X25519
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Encode
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointScalar
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointMul
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
meta import VerifiedGarbage.Proof.X25519.Edwards.Base
meta import VerifiedGarbage.Proof.X25519.Edwards.Ladder
meta import VerifiedGarbage.Proof.X25519.Bytes
meta import VerifiedGarbage.Proof.Ed25519.Bytes
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `X25519.PPC64LE.Base`, which only this module used -/

section

/-!
# `vg_x25519_base` on PPC64LE: correctness

As on RISC-V (`Proof/X25519/RISCV64/Base.lean`): the scalar's nibbles, clamped
(`clampCopy_ok`), are those of `decodeScalar25519`'s (`clamp_nib`); the comb computes
`[k] B` from them (`combRun_ok`), and `uEncode` its u-coordinate `(Z + Y) / (Z - Y)`, which
`Proof/X25519/Edwards/Ladder.lean` shows is `X25519(k, 9)` (`engine_ok`). The wrapper is
`vg_ed25519_scalar_base`'s (`baseWrap_ok`), whose precondition it shares but for the result.
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE.Base

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Impl.X25519.PPC64LE.Base
open VG.Proof.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Proof.Ed25519 (Rep baseAff)

/-! ## The clamp -/

/-- `decodeScalar25519`'s clamping of 32 bytes. -/
def clampL (kb : List Byte) : List Byte :=
  let k := kb.set 0 (kb.getD 0 0 &&& 248)
  k.set 31 ((k.getD 31 0 &&& 127) ||| 64)

theorem decode_clamp {kb : List Byte} (hk : kb.length = 32) :
    Spec.X25519.decodeScalar25519 kb = Spec.Ed25519.decodeLE (clampL kb) := by
  obtain hl : (clampL kb).length = 32 := by simp [clampL, hk]
  rw [Proof.Ed25519.decodeLE_eq, ← Proof.X25519.take_32 hl, ← Proof.X25519.decodeLittleEndian_eq]
  rfl

theorem clampL_getD {kb : List Byte} (hk : kb.length = 32) {j : Nat} (hj : j < 32) :
    (clampL kb).getD j 0 = if j = 31 then (kb.getD 31 0 &&& 127) ||| 64 else
      if j = 0 then kb.getD 0 0 &&& 248 else kb.getD j 0 := by
  unfold clampL
  by_cases h31 : j = 31
  · subst h31
    simp [List.getD_eq_getElem?_getD, hk]
  · by_cases h0 : j = 0
    · subst h0
      simp [List.getD_eq_getElem?_getD, hk]
    · simp [List.getD_eq_getElem?_getD, hk, h31, h0, Ne.symm h31, Ne.symm h0]

/-- Nibble `j` of the bytes `kb`. -/
def nibL (kb : List Byte) (j : Nat) : Nat := (kb.getD (j / 2) 0).toNat / 16 ^ (j % 2) % 16

/-- What the clamp does to the nibbles `f`: nibble 0 `&&& 8`, nibble 63 `&&& 7 ||| 4`. -/
def clampN (f : Nat → Nat) (i : Nat) : Nat :=
  if i = 0 then f 0 &&& 8 else if i = 63 then (f 63 &&& 7) ||| 4 else f i

private theorem clamp_facts : ∀ x : BitVec 8,
    (x &&& 248).toNat / 16 ^ 0 % 16 = x.toNat / 16 ^ 0 % 16 &&& 8 ∧
    (x &&& 248).toNat / 16 ^ 1 % 16 = x.toNat / 16 ^ 1 % 16 ∧
    ((x &&& 127) ||| 64).toNat / 16 ^ 0 % 16 = x.toNat / 16 ^ 0 % 16 ∧
    ((x &&& 127) ||| 64).toNat / 16 ^ 1 % 16 = (x.toNat / 16 ^ 1 % 16 &&& 7) ||| 4 := by
  decide

/-- The clamped scalar's nibbles are the bytes' nibbles, clamped. -/
theorem clamp_nib {kb : List Byte} (hk : kb.length = 32) {i : Nat} (hi : i < 64) :
    Proof.Ed25519.nib (Spec.X25519.decodeScalar25519 kb) i = clampN (nibL kb) i := by
  rw [decode_clamp hk, nib_decodeLE, clampL_getD hk (by omega_using [hi])]
  obtain f0 := clamp_facts (kb.getD 0 0)
  obtain f31 := clamp_facts (kb.getD 31 0)
  unfold clampN nibL
  by_cases h0 : i = 0
  · subst h0; simp only [show (0 : Nat) / 2 = 0 from rfl, show (0 : Nat) % 2 = 0 from rfl, ↓reduceIte]
    exact f0.1
  by_cases h1 : i = 1
  · subst h1; simp only [show (1 : Nat) / 2 = 0 from rfl, show (1 : Nat) % 2 = 1 from rfl, ↓reduceIte]
    exact f0.2.1
  by_cases h62 : i = 62
  · subst h62; simp only [show (62 : Nat) / 2 = 31 from rfl, show (62 : Nat) % 2 = 0 from rfl, ↓reduceIte]
    exact f31.2.2.1
  by_cases h63 : i = 63
  · subst h63; simp only [show (63 : Nat) / 2 = 31 from rfl, show (63 : Nat) % 2 = 1 from rfl, ↓reduceIte]
    exact f31.2.2.2
  rw [ite_eq_right (show i / 2 ≠ 31 by omega_using [h62, h63]), ite_eq_right (show i / 2 ≠ 0 by omega_using [h0, h1]), ite_eq_right h0,
    ite_eq_right h63]

private theorem clamp_regs : ∀ x : BitVec 8,
    ((BitVec.ofNat 64 x.toNat &&& BitVec.ofNat 64 8).setWidth 8).toNat = x.toNat &&& 8 ∧
    (((BitVec.ofNat 64 x.toNat &&& BitVec.ofNat 64 7) ||| (4 : BitVec 16).setWidth 64).setWidth 8).toNat =
      (x.toNat &&& 7) ||| 4 := by
  decide

theorem clampCopy_ok {s : State} {b : Addr} (hc : Ctx8 b s) :
    WP isa (.block clampCopy) s fun t => Rest [.r7, .r8] s t ∧ Frame [scalR b] s.mem t.mem ∧
      ∀ i < 64, nibC t.mem b i = clampN (nibC s.mem b) i := by
  have hS : SCAL = 1152 := rfl
  let a : Nat → Addr := fun k => b + BitVec.ofNat 64 (SCAL + k)
  obtain ne : ∀ i k, i < 64 → k < 64 → i ≠ k → a i ≠ a k := fun i k hi hk hik he =>
    Offset.disjoint b (d := SCAL + i) (n := 1) (e := SCAL + k) (k := 1)
      (by omega_using [hik]) (by omega_using [hS, hi]) (by omega_using [hS, hk]) _ (Region.contains_self _ _)
      (by change Region.Contains ⟨a k, 1⟩ (a i) 1; rw [he]; exact Region.contains_self _ _)
  unfold clampCopy
  refine wp_lbz (a := a 0) (by decide) (by decide) (by rw [hc.r6]; rfl) (hc.inR (by omega_using [hS])) fun s₁ u₁ => ?_
  refine wp_li (by decide) fun s₂ u₂ => wp_and fun s₃ u₃ => ?_
  refine wp_stb (a := a 0) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hc.r6]; rfl)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hc.inW (by omega_using [hS])) fun s₄ u₄ => ?_
  obtain c0 := clamp_regs (s.mem (a 0))
  obtain m4 : s₄.mem = s.mem.writeW (a 0) (BitVec.ofNat 8 (nibC s.mem b 0 &&& 8)) := by
    rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [u₃.gpr, u₂.gpr, u₂.other .r7 (by decide), u₁.gpr, c0.1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))]
    rfl
  obtain hc4 : Ctx8 b s₄ := hc.of_rest ((u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans
    ((u₃.rest (by decide)).trans (u₄.rest [.r7, .r8])))) (by decide)
  refine wp_lbz (a := a 63) (by decide) (by decide) (by rw [hc4.r6]) (hc4.inR (by omega_using [hS])) fun s₅ u₅ => ?_
  refine wp_li (by decide) fun s₆ u₆ => wp_and fun s₇ u₇ => wp_ori fun s₈ u₈ => ?_
  refine wp_stb (a := a 63) (by decide) (by decide)
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      hc4.r6])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr]; exact hc4.inW (by omega_using [hS])) fun t u₉ => WP.block_nil ?_
  obtain v63 : s₄.mem (a 63) = s.mem (a 63) := by
    rw [m4, VG.WriteBytes.writeW8_apply, ite_eq_right (ne 63 0 (by decide) (by decide) (by decide))]
  obtain c63 := clamp_regs (s.mem (a 63))
  obtain hb63 : ∀ x : Nat, (x &&& 7) ||| 4 < 2 ^ 8 := fun x =>
    Nat.or_lt_two_pow (Nat.lt_of_le_of_lt Nat.and_le_right (by decide)) (by decide)
  obtain mt : t.mem = (s.mem.writeW (a 0) (BitVec.ofNat 8 (nibC s.mem b 0 &&& 8))).writeW (a 63)
      (BitVec.ofNat 8 ((nibC s.mem b 63 &&& 7) ||| 4)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, ← m4]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [u₈.gpr, u₇.gpr, u₆.gpr, u₆.other .r7 (by decide), u₅.gpr, v63, c63.2,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hb63 _)]
    rfl
  refine ⟨(u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
    ((u₄.rest _).trans ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans
      ((u₈.rest (by decide)).trans (u₉.rest _)))))))), ?_, fun i hi => ?_⟩
  · rw [mt]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [hS]))).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [hS]))
  · have lt8 : ∀ n, n < 16 → n < 2 ^ 8 := fun n h => by omega_using [h]
    unfold nibC clampN
    rw [mt, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
    by_cases h63 : i = 63
    · subst h63
      rw [ite_eq_left rfl, BitVec.toNat_ofNat, ite_eq_right (by decide), ite_eq_left rfl,
        Nat.mod_eq_of_lt (hb63 _)]
      rfl
    · rw [ite_eq_right (ne i 63 hi (by decide) h63)]
      by_cases h0 : i = 0
      · subst h0
        rw [ite_eq_left rfl, BitVec.toNat_ofNat, ite_eq_left rfl,
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right (by decide))]
        rfl
      · rw [ite_eq_right (ne i 0 hi (by decide) h0), ite_eq_right h0, ite_eq_right h63]

/-! ## The engine -/

theorem uOps_eval (e : Env) :
    evalOps uOps e 0 = e 2 + e 1 ∧ evalOps uOps e 2 = e 2 - e 1 := by
  simp [uOps, evalOps, evalOp, Function.update]

theorem engine_ok : EngineOk engine (fun kb => Spec.X25519.x25519 kb Spec.X25519.basePoint) := by
  intro b s p T hc h14 hin hpd hT hsym apart
  obtain hk : (Spec.Ed25519.bytesAt s.mem p 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  obtain sub : (scalR b).Sub ⟨b, 8192⟩ := Offset.sub_base _ (by decide)
  have hF := FR_eq
  unfold engine
  refine WP.seq (WP.mono_syms (initFields_ok hc.ctx) fun s1 ⟨r1, f1⟩ sy1 => ?_)
  obtain hc1 : Ctx8 b s1 := hc.of_rest r1 (by decide)
  obtain hb1 : Spec.Ed25519.bytesAt s1.mem p 32 = Spec.Ed25519.bytesAt s.mem p 32 := by
    simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
    intro i hi
    exact bytes_ws f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_using [])) hpd (by decide)
      (List.mem_range.mp hi)
  obtain hT1 : TblAt s1 T := hT.of_frame (by rw [r1.rd, r1.wr]) f1 fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right (Offset.sub_base _ (by decide))
  rw [combClamped, WP.seq_iff]
  refine WP.seq (WP.mono_syms (combCopy_ok hc1 (by rw [r1.gpr _ (by decide), h14])
    (fun i hi => by rw [r1.rd, r1.wr]; exact hin i hi) (hpd.sub_right sub)) fun u ⟨ru, fu, cu⟩ syu => ?_)
  obtain hcu : Ctx8 b u := hc1.of_rest ru (by decide)
  refine WP.seq (WP.mono_syms (clampCopy_ok hcu) fun v ⟨rv, fv, cv⟩ syv => ?_)
  obtain hcv : Ctx8 b v := hcu.of_rest rv (by decide)
  obtain tsc : ∀ r ∈ [scalR b], (TBL T).Disjoint r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right sub
  obtain hTv : TblAt v T := (hT1.of_frame (by rw [ru.rd, ru.wr]) fu tsc).of_frame (by rw [rv.rd, rv.wr]) fv tsc
  -- The clamped nibbles are the clamped scalar's.
  obtain hnu : ∀ j < 64, nibC u.mem b j = nibL (Spec.Ed25519.bytesAt s.mem p 32) j := fun j hj => by
    rw [cu j hj, nibAt_eq _ _ hj, nib_decodeLE, hb1]; rfl
  obtain hn : ∀ i < 64, nibC v.mem b i =
      Proof.Ed25519.nib (Spec.X25519.decodeScalar25519 (Spec.Ed25519.bytesAt s.mem p 32)) i := fun i hi => by
    rw [cv i hi, clamp_nib hk hi]
    unfold clampN
    rw [hnu 0 (by decide), hnu 63 (by decide), hnu i hi]
  obtain hS : Spec.X25519.decodeScalar25519 (Spec.Ed25519.bytesAt s.mem p 32) < 2 ^ 256 := by
    rw [decode_clamp hk]
    have := Proof.Ed25519.decodeLE_lt (clampL (Spec.Ed25519.bytesAt s.mem p 32))
    rw [show (clampL (Spec.Ed25519.bytesAt s.mem p 32)).length = 32 by simp [clampL, hk]] at this
    exact Nat.lt_of_lt_of_le this (by decide)
  refine WP.mono (combRun_ok hcv hTv (by rw [syv, syu, sy1, hsym]) apart hS hn) fun x ⟨rx, fx, px⟩ => ?_
  obtain hcx : Ctx8 b x := hcv.of_rest rx (by decide)
  unfold uEncode
  refine WP.seq (WP.mono (fieldCode_ok uOps hcx.ctx) fun y ⟨ky, ey⟩ => ?_)
  obtain hcy : Ctx8 b y := hcx.of_keep ky
  refine WP.seq (WP.mono (pointAffine_ok hcy) fun z ⟨kz, e0, _⟩ => ?_)
  obtain hcz : Ctx8 b z := hcy.of_keep kz
  refine WP.mono (freeze_ok hcz.ctx 0) fun t ⟨rt, ft, _, vt⟩ => ⟨?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((ru.mono (by decide)).trans ((rv.mono (by decide)).trans
      ((rx.mono (by decide)).trans ((ky.rest.mono (by decide)).trans ((kz.rest.mono (by decide)).trans
        (rt.mono (by decide)))))))
  · have fr : ∀ r ∈ ([⟨b + BitVec.ofNat 64 FR, 64⟩] : List Region), ∃ r' ∈ [FA b], r.Sub r' := fun r hr =>
      ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_using [hF]) (by omega_using [hF])⟩
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
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧
      Spec.Ed25519.bytesAt t.mem (s.gpr .r3) 32 =
        Spec.X25519.x25519 (Spec.Ed25519.bytesAt s.mem (s.gpr .r4) 32) Spec.X25519.basePoint := by
  unfold x25519Base
  exact baseWrap_ok (R := fun kb => Spec.X25519.x25519 kb Spec.X25519.basePoint)
    (fun hc h14 hin hpd hT hsym apart => engine_ok hc h14 hin hpd hT hsym apart) hp

end VG.Proof.X25519.PPC64LE.Base

end

end

/-!
# `vg_x25519_base` on PPC64LE, verified

The function meets `x25519BaseContract` under `abi.withConsts combConsts`
(the comb's table), with no stack: the proof against the contract's facts
by register (`baseC`: `baseR` without the table, and what the table adds),
which it implies (`consts_implies`), and a state satisfying it, with the
table at `0x100000`. Only the pointers and the table's address are public
(`x25519Base_ct`, by taint tracking: the scalar's digits select the table's
entries and the signs only by masks).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE.Base

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Impl.X25519.PPC64LE.Base
open VG.Proof.Ed25519.PPC64LE

/-- `x25519BaseContract` by register, without the table: `out` in `r3`, `scalar` in `r4`,
`scratch` in `r5`. -/
def baseR : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 32⟩
    let sc : Region := ⟨s.gpr .r4, 32⟩
    let ws : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [sc] ∧ s.wr = [out, ws] ∧ out.Disjoint ws ∧ sc.Disjoint ws
  post s s' := Spec.Ed25519.bytesAt s'.mem (s.gpr .r3) 32 =
    Spec.X25519.x25519 (Spec.Ed25519.bytesAt s.mem (s.gpr .r4) 32) Spec.X25519.basePoint
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp

/-- `baseR` with the comb's table (`abi.withConsts`). -/
def baseC : Contract isa where
  pre s := baseR.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 0 s
  post := baseR.post
  pub s₁ s₂ := baseR.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym

theorem base_ok' (s : State) (hs : baseC.pre s) :
    ∃ t s', Exec isa x25519Base s t s' ∧ abiPreserved s s' ∧ baseC.post s s' := by
  obtain ⟨⟨a, b, c, d⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at *
  obtain ⟨-, tfit, words, twr, -⟩ := tbl_of_consts hk
  have hrd : s.rd = [⟨s.gpr .r4, 32⟩, TBL (s.syms combSym)] := rd_of_consts hk a
  obtain ⟨t, s', he, hg, hsp, hra, hq⟩ := x25519Base_ok
    ⟨hrd, b, c, d, tfit, words, twr _ (by rw [b]; simp)⟩
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hq⟩

theorem x25519Base_ct : ConstantTime isa baseC.pre baseC.pub x25519Base :=
  VG.Taint.constantTime (A := taintSym [combSym]) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨⟨h0, h1, h2, hsp⟩, hsy⟩ => ⟨⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩, fun n hn => by simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩)
    (by taint_decide)

/-- A state satisfying the precondition, without the table. -/
def baseSat : State where
  gpr r := match r with | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 8192⟩]

theorem baseR_implies : baseR.Implies (Spec.X25519.x25519BaseContract PPC64LE.abi) := by
  contract_implies [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig, baseR,
    PPC64LE.abi, PPC64LE.argRegs] [baseSat] using baseSat

/-- The comb's table at `0x100000`. -/
@[irreducible] def tblMem : Mem := constMem 0x100000 combWords

theorem tblMem_held : ∀ i < combWords.length,
    tblMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  have h := constMem_held 0x100000 combWords (by rw [combWords_length]; decide)
  unfold tblMem
  exact h

/-- `baseSat` with the table. -/
def baseSatC : State :=
  { baseSat with mem := tblMem, rd := baseSat.rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem baseC_sat : (Spec.X25519.x25519BaseContract (PPC64LE.abi.withConsts combConsts)).pre baseSatC := by
  have hl := combWords_length
  have held := tblMem_held
  change (Spec.X25519.x25519BaseContract (PPC64LE.abi.withConsts [(combSym, combWords)])).pre baseSatC
  generalize combWords = W' at hl held ⊢
  generalize e : baseSatC = s
  sig_pre [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig, PPC64LE.abi, PPC64LE.argRegs,
    Abi.withConsts, Abi.constRegions_cons, Abi.constRegions_nil, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 32⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem x25519Base_verified :
    Verified PPC64LE.target x25519Base (Spec.X25519.x25519BaseContract (PPC64LE.abi.withConsts combConsts)) :=
  Verified.of_correct base_ok' x25519Base_ct
    (consts_implies (kR := baseR) baseR_implies (fun _ _ h => h) (fun _ _ h => h) ⟨baseSatC, baseC_sat⟩)

end VG.Proof.X25519.PPC64LE.Base
