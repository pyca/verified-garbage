module

import VerifiedGarbage.Proof.Ed25519.RISCV64.RecoverCand
public import VerifiedGarbage.Proof.Ed25519.RecoverResult
import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldTest
import VerifiedGarbage.Proof.Ed25519.RISCV64.Freeze
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.X25519.RISCV64.Bits
import VerifiedGarbage.Proof.X25519.Limbs
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.X25519.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Recover
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointOps
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Field

/-!
# Ed25519 on RISC-V: the sign and the checks of a decoding

A decoding's result is `s3`, 1 for a point (in slots 0–3) and 0 for none
(`DecodeResult`), and it writes `fclob`, `s3` and the field area (`DKeep`).
The sign it took from the encoding is the word at `SIGN` (`SignAt`).
`recoverSign_ok`: from the candidate `x` in slot 0, `signResult`;
`recoverPoint_ok`: the checks of `v x²`, as `recoverResult`, which is the
spec's `recoverX` (`recoverResult_spec`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519 (val32_div)
open VG.Spec.X25519 (P)
open VG.Proof.Ed25519 (rootU rootV rootX recoveredPoint signedX signResult recoverResult)

/-- What a decoding writes. -/
structure DKeep (b : Addr) (s t : State) : Prop where
  rest : Rest (.s3 :: fclob) s t
  frame : Frame [FA b] s.mem t.mem

theorem DKeep.of_keep {b : Addr} {s t : State} (h : Keep b s t) : DKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩

theorem DKeep.trans {b : Addr} {s t u : State} (h : DKeep b s t) (k : DKeep b t u) : DKeep b s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

/-- The result of a decoding. -/
def DecodeResult (b : Addr) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .s3 = 0
  | some p => s.gpr .s3 = 1 ∧ point (env s.mem b) 0 1 2 3 = p

/-- The sign of the encoding, at `SIGN`. -/
def SignAt (b : Addr) (sg : Bool) (m : Mem) : Prop :=
  (m.readW (b + BitVec.ofNat 64 SIGN) 32).setWidth 64 = BitVec.ofNat 64 sg.toNat

theorem SignAt.frame {b : Addr} {sg : Bool} {m m' : Mem} (h : SignAt b sg m) (hf : Frame [FA b] m m') :
    SignAt b sg m' := by
  have hS : SIGN = 24 := rfl
  unfold SignAt
  rw [hf.readW (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by decide)]
  exact h

section
variable {b : Addr}

theorem frame_FR {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 FR, 64⟩] m m') : Frame [FA b] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub b (by decide) (by decide)⟩

theorem env_FR {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 FR, 64⟩] m m') : env m' b = env m b :=
  funext fun i => env_keep hf i fun r hr => by
    have := slot_range i
    have hX : FR = 864 := rfl
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)

theorem recoverInvalid_ok (s : State) :
    WP isa recoverInvalid s fun t => DKeep b s t ∧ t.mem = s.mem ∧ DecodeResult b none t :=
  wp_li (by decide) fun t u => WP.block_nil ⟨⟨u.rest (by decide), by rw [u.mem]; exact Frame.refl _ _⟩, u.mem,
    show t.gpr .s3 = 0 by rw [u.gpr]; rfl⟩

theorem recoverSuccess_ok {s : State} (hc : Ctx8 b s) :
    WP isa recoverSuccess s fun t => DKeep b s t ∧
      DecodeResult b (some (recoveredPoint (env s.mem b 0) (env s.mem b 1))) t := by
  unfold recoverSuccess
  refine WP.seq (WP.mono (fieldCode_ok _ hc.ctx hc.ws) fun s1 ⟨k1, e1⟩ => ?_)
  refine wp_li (by decide) fun t u => WP.block_nil ⟨(DKeep.of_keep k1).trans
    ⟨u.rest (by decide), by rw [u.mem]; exact Frame.refl _ _⟩, u.gpr, ?_⟩
  rw [u.mem, e1]
  rfl

/-- A residue's parity is its low limb's. -/
theorem V_mod2' (m : Mem) (o : Nat) : V m b o % 2 = limb m b o 0 % 2 := by
  have h := val32_div (r := limb m b o) (n := 8) (fun k _ => limb_lt _ _ _ _) (k := 0) (by decide)
  rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h
  rw [V, ← h, Nat.mod_mod_of_dvd _ (by decide)]

theorem parity_ok {s : State} (hc : Ctx b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa (.block recoverParity) s fun t =>
      Rest [.a2, .a4, .a5] s t ∧ t.mem = s.mem ∧ (t.gpr .a2 = 0 ↔ limb s.mem b FR 0 % 2 = sg.toNat) := by
  unfold recoverParity
  refine lw0_ok hc (d := FR) (by decide) (by decide) fun s1 u1 => wp_sll (by decide) fun s2 u2 => wp_srl (by decide) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc.of_rest ((u1.rest (ws := [.a4]) (by decide)).trans ((u2.rest (by decide)).trans
    (u3.rest (by decide)))) (by decide)
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine lw0_ok hc3 (d := SIGN) (by decide) (by decide) fun s4 u4 => wp_xor fun s5 u5 => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  · rw [u5.mem, u4.mem, m3]
  · have e7 : (s4.gpr .a4).toNat = limb s.mem b FR 0 % 2 := by
      have hb := bit_shift (s1.gpr .a4) (j := 0) (by decide)
      rw [Nat.sub_zero, Nat.shiftRight_zero, Nat.and_one_is_mod] at hb
      rw [u4.other _ (by decide), u3.gpr, u2.gpr, hb, u1.gpr, toNat_ext32]
      rfl
    have e8 : s4.gpr .a5 = BitVec.ofNat 64 sg.toNat := by rw [u4.gpr, m3]; exact hs
    have xor0 : ∀ x y : BitVec 64, x ^^^ y = 0 ↔ x = y := fun _ _ => BitVec.xor_eq_zero_iff
    rw [u5.gpr, xor0, ← BitVec.toNat_inj, e7, e8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := sg.toNat) (by cases sg <;> decide)]

theorem sign_iff (v : Nat) (sg : Bool) : (((v % 2 == 1) == sg) = true) ↔ v % 2 = sg.toNat := by
  have := Nat.mod_lt v (show 0 < 2 by decide)
  cases sg <;> simp <;> omega

/-- The reduced `x`'s parity against the sign: `a2` zero exactly when they match. -/
theorem adjParity_ok {s : State} (hc : Ctx8 b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa (.block (freeze 0 ++ recoverParity)) s fun t => DKeep b s t ∧ env t.mem b = env s.mem b ∧
      (t.gpr .a2 = 0 ↔ (((env s.mem b 0).val % 2 == 1) == sg) = true) := by
  refine WP.append (freeze_ok hc.ctx 0) fun s1 ⟨r1, f1, _, v1⟩ => ?_
  have hc1 : Ctx b s1 := hc.ctx.of_rest r1 (by decide)
  refine WP.mono (parity_ok hc1 (hs.frame (frame_FR f1))) fun s2 ⟨r2, m2, h2⟩ =>
    ⟨⟨r1.trans (r2.mono (by decide)) |>.mono (by decide), by rw [m2]; exact frame_FR f1⟩,
      by rw [m2, env_FR f1], ?_⟩
  have hp : limb s1.mem b FR 0 % 2 = (env s.mem b 0).val % 2 := by
    rw [← V_mod2', v1]; rfl
  rw [hp, ← sign_iff] at h2
  exact h2

/-- **The sign applied**, and the point. -/
theorem recoverAdjust_ok {s : State} (hc : Ctx8 b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa recoverAdjustSign s fun t => DKeep b s t ∧
      DecodeResult b (some (recoveredPoint (signedX (env s.mem b 0) sg) (env s.mem b 1))) t := by
  unfold recoverAdjustSign
  refine WP.seq (WP.mono (adjParity_ok hc hs) fun s2 ⟨hk2, he2, h2⟩ => ?_)
  have hc2 : Ctx8 b s2 := hc.of_rest hk2.rest (by decide)
  refine WP.seq (WP.ite (s2.gpr .a2 == 0) (eval_zero s2 .a2) (fun h => ?_) (fun h => ?_))
  · refine WP.block_nil (WP.mono (recoverSuccess_ok hc2) fun t ⟨kt, dt⟩ => ⟨hk2.trans kt, ?_⟩)
    have hsg : signedX (env s.mem b 0) sg = env s.mem b 0 := by
      unfold signedX; rw [iteT (h2.mp (beq_iff_eq.mp h))]
    rw [hsg, ← he2]; exact dt
  · refine WP.mono (fieldCode_ok _ hc2.ctx hc2.ws) fun s3 ⟨k3, e3⟩ => ?_
    refine WP.mono (recoverSuccess_ok (hc2.of_keep k3)) fun t ⟨kt, dt⟩ => ⟨hk2.trans ((DKeep.of_keep k3).trans kt), ?_⟩
    have hsg : signedX (env s.mem b 0) sg = 0 - env s.mem b 0 := by
      unfold signedX
      exact iteF fun hq => absurd (beq_iff_eq.mpr (h2.mpr hq)) (by simpa using h)
    have hx : env s3.mem b 0 = 0 - env s.mem b 0 := by rw [e3, he2]; rfl
    have hy : env s3.mem b 1 = env s.mem b 1 := by rw [e3, he2]; rfl
    rw [hsg]; rw [hx, hy] at dt; exact dt

/-- **The sign**, for the candidate in slot 0 and `y` in slot 1. -/
theorem recoverSign_ok {s : State} (hc : Ctx8 b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa recoverSign s fun t => DKeep b s t ∧
      DecodeResult b (signResult (env s.mem b 0) (env s.mem b 1) sg) t := by
  unfold recoverSign
  refine WP.seq (WP.mono (fieldZero_ok hc.ctx 0) fun s1 ⟨r1, f1, h1⟩ => ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest r1 (by decide)
  have he1 : env s1.mem b = env s.mem b := env_FR f1
  have hk1 : DKeep b s s1 := ⟨r1.mono (by decide), frame_FR f1⟩
  have hs1 : SignAt b sg s1.mem := hs.frame (frame_FR f1)
  have hz : (env s.mem b 0 = 0) ↔ V s.mem b (offset 0) % P = 0 := by
    rw [Fin.ext_iff]; exact Iff.rfl
  rw [← hz] at h1
  have adj : WP isa recoverAdjustSign s1 fun t => DKeep b s t ∧
      DecodeResult b (some (recoveredPoint (signedX (env s.mem b 0) sg) (env s.mem b 1))) t :=
    WP.mono (recoverAdjust_ok hc1 hs1) fun t ⟨kt, dt⟩ => ⟨hk1.trans kt, by rw [he1] at dt; exact dt⟩
  refine WP.ite (s1.gpr .a2 == 0) (eval_zero s1 .a2) (fun h => ?_) (fun h => ?_)
  · have hx : env s.mem b 0 = 0 := h1.mp (beq_iff_eq.mp h)
    unfold signTest
    refine WP.seq (lw0_ok hc1.ctx (d := SIGN) (by decide) (by decide) fun s2 u2 => WP.block_nil ?_)
    have e5 : s2.gpr .a2 = BitVec.ofNat 64 sg.toNat := by rw [u2.gpr]; exact hs1
    have hc2 : Ctx8 b s2 := hc1.of_rest (u2.rest (ws := [.a2]) (by decide)) (by decide)
    have hk2 : DKeep b s1 s2 := ⟨u2.rest (by decide), by rw [u2.mem]; exact Frame.refl _ _⟩
    refine WP.ite (s2.gpr .a2 != 0) (eval_nonzero s2 .a2) (fun h' => ?_) (fun h' => ?_)
    · have hsg : sg = true := by
        cases sg with
        | false => rw [e5] at h'; exact absurd h' (by decide)
        | true => rfl
      refine WP.mono (recoverInvalid_ok s2) fun t ⟨kt, _, dt⟩ => ⟨hk1.trans (hk2.trans kt), ?_⟩
      unfold signResult; rw [hx, hsg]; exact dt
    · have hsg : sg = false := by
        cases sg with
        | false => rfl
        | true => rw [e5] at h'; exact absurd h' (by decide)
      refine WP.mono (recoverAdjust_ok hc2 (sg := sg) (by rw [u2.mem]; exact hs1)) fun t ⟨kt, dt⟩ =>
        ⟨hk1.trans (hk2.trans kt), ?_⟩
      have e2 : env s2.mem b = env s.mem b := by rw [u2.mem, he1]
      rw [e2] at dt
      subst hsg
      unfold signResult; rw [iteF (by simp)]; exact dt
  · refine WP.mono adj fun t ⟨kt, dt⟩ => ⟨kt, ?_⟩
    have hx : ¬ env s.mem b 0 = 0 := fun hx => absurd (beq_iff_eq.mpr (h1.mpr hx)) (by simpa using h)
    unfold signResult; rw [iteF (by simp [hx])]; exact dt

/-- **A candidate checked**, for `y` in slot 1: `recoverResult`. -/
theorem recoverPoint_ok {s : State} (hc : Ctx8 b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa recoverPoint s fun t => DKeep b s t ∧ DecodeResult b (recoverResult (env s.mem b 1) sg) t := by
  unfold recoverPoint
  refine WP.seq (WP.mono (recoverCandidate_ok hc) fun a ⟨ka, ax, ay, au, _, avx, anu⟩ => ?_)
  have hca : Ctx8 b a := hc.of_keep ka
  refine WP.seq (WP.mono (fieldEqual_ok hca.ctx hca.ws 11 6) fun c ⟨kc, ec, hc5⟩ => ?_)
  have hcc : Ctx8 b c := hca.of_keep kc
  have hkc : DKeep b s c := DKeep.of_keep (ka.trans kc)
  have hsc : SignAt b sg c.mem := hs.frame (ka.trans kc).frame
  have cx : env c.mem b 0 = rootX (env s.mem b 1) := by rw [ec, ← ax]; rfl
  have cy : env c.mem b 1 = env s.mem b 1 := by rw [ec, ← ay]; rfl
  rw [avx, au] at hc5
  refine WP.ite (c.gpr .a2 == 0) (eval_zero c .a2) (fun h => ?_) (fun h => ?_)
  · refine WP.mono (recoverSign_ok hcc hsc) fun t ⟨kt, dt⟩ => ⟨hkc.trans kt, ?_⟩
    unfold recoverResult; rw [iteT (hc5.mp (beq_iff_eq.mp h))]
    rw [cx, cy] at dt; exact dt
  · have hne : ¬ rootV (env s.mem b 1) * rootX (env s.mem b 1) * rootX (env s.mem b 1) = rootU (env s.mem b 1) :=
      fun he => absurd (beq_iff_eq.mpr (hc5.mpr he)) (by simpa using h)
    refine WP.seq (WP.mono (fieldEqual_ok hcc.ctx hcc.ws 11 12) fun d ⟨kd, ed, hd5⟩ => ?_)
    have hcd : Ctx8 b d := hcc.of_keep kd
    have hkd : DKeep b s d := hkc.trans (DKeep.of_keep kd)
    have hsd : SignAt b sg d.mem := hsc.frame kd.frame
    have c11 : env c.mem b 11 = env a.mem b 11 := by rw [ec]; rfl
    have c12 : env c.mem b 12 = env a.mem b 12 := by rw [ec]; rfl
    rw [c11, c12, avx, anu] at hd5
    refine WP.ite (d.gpr .a2 == 0) (eval_zero d .a2) (fun h' => ?_) (fun h' => ?_)
    · refine WP.seq (WP.mono (fieldCode_ok _ hcd.ctx hcd.ws) fun f ⟨kf, ef⟩ => ?_)
      refine WP.mono (recoverSign_ok (hcd.of_keep kf) (hsd.frame kf.frame)) fun t ⟨kt, dt⟩ =>
        ⟨hkd.trans ((DKeep.of_keep kf).trans kt), ?_⟩
      have fx : env f.mem b 0 = rootX (env s.mem b 1) * Spec.Ed25519.sqrtM1 := by
        rw [ef, ← cx, show env c.mem b 0 = env d.mem b 0 by rw [ed]; rfl]; rfl
      have fy : env f.mem b 1 = env s.mem b 1 := by
        rw [ef, ← cy, show env c.mem b 1 = env d.mem b 1 by rw [ed]; rfl]; rfl
      unfold recoverResult; rw [iteF hne, iteT (hd5.mp (beq_iff_eq.mp h'))]
      rw [fx, fy] at dt; exact dt
    · have hne' : ¬ rootV (env s.mem b 1) * rootX (env s.mem b 1) * rootX (env s.mem b 1) =
          0 - rootU (env s.mem b 1) :=
        fun he => absurd (beq_iff_eq.mpr (hd5.mpr he)) (by simpa using h')
      refine WP.mono (recoverInvalid_ok d) fun t ⟨kt, _, dt⟩ => ⟨hkd.trans kt, ?_⟩
      unfold recoverResult; rw [iteF hne, iteF hne']; exact dt

end

end VG.Proof.Ed25519.RISCV64
