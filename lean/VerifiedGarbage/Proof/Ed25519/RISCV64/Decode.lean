module

public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldTest
import VerifiedGarbage.Proof.Ed25519.RISCV64.Freeze
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarReduce
import VerifiedGarbage.Proof.Ed25519.Decode
import VerifiedGarbage.Proof.X25519.RISCV64.Instr
import VerifiedGarbage.Proof.X25519.RISCV64.Invert
import VerifiedGarbage.Proof.X25519.Limbs
import VerifiedGarbage.Proof.X25519.RISCV64.Freeze
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Field
import VerifiedGarbage.Proof.Ed25519.RISCV64.RecoverCand
public import VerifiedGarbage.Proof.Ed25519.RecoverResult
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
import VerifiedGarbage.Proof.X25519.RISCV64.Bits
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Recover

/-! ### `Ed25519.RISCV64.RecoverSign`, which this module and modules that import it used -/

section

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
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hS])) (by omega_using [hS]) (by omega_using [])) (by decide)]
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
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [this, hX])) (by omega_using [this]) (by omega_using [hX])

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

end

end

/-!
# Ed25519 on RISC-V: decoding a point

`pointDecode` with the encoding at `s0`: its words into slot 1, bit 255
split off to `SIGN` (`split_ok`), `y` canonical (`pointDecodeLoad_ok`), and
the recovery of `x` (`recoverPoint_ok`): `decodePoint` of the 32 bytes
(`pointDecode_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519 (val32_succ val32_lt val32_congr)
open VG.Spec.X25519 (P)
open VG.Spec.Ed25519 (decodeLE bytesAt)

/-- What a decoding writes, with its sign. -/
structure DecKeep (b : Addr) (s t : State) : Prop where
  rest : Rest (.s3 :: fclob) s t
  frame : Frame [⟨b + BitVec.ofNat 64 SIGN, 4⟩, FA b] s.mem t.mem

theorem DecKeep.trans {b : Addr} {s t u : State} (h : DecKeep b s t) (k : DecKeep b t u) : DecKeep b s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem DecKeep.of_dkeep {b : Addr} {s t : State} (h : DKeep b s t) : DecKeep b s t :=
  ⟨h.rest, h.frame.mono (by simp)⟩

theorem toNat_beq_one {x : Nat} (h : x < 2) : (x == 1).toNat = x := by
  rcases (by omega_arith : x = 0 ∨ x = 1) with rfl | rfl <;> rfl

section
variable {b : Addr}

/-- **Bit 255 of slot 1**, to `SIGN`, and cleared. -/
theorem split_ok {s : State} (hc : Ctx b s) :
    WP isa (.block splitYSign) s fun t =>
      Rest [.a4, .a5] s t ∧
      Frame [⟨b + BitVec.ofNat 64 SIGN, 4⟩, ⟨b + BitVec.ofNat 64 (offset 1 + 28), 4⟩] s.mem t.mem ∧
      SignAt b (limb s.mem b (offset 1) 7 / 2 ^ 31 == 1) t.mem ∧
      limb t.mem b (offset 1) 7 = limb s.mem b (offset 1) 7 % 2 ^ 31 ∧
      ∀ j < 7, limb t.mem b (offset 1) j = limb s.mem b (offset 1) j := by
  have hS : SIGN = 24 := rfl
  have h1 : offset 1 = 96 := rfl
  unfold splitYSign VG.Impl.X25519.RISCV64.low31
  simp only [List.cons_append, List.nil_append]
  refine lw0_ok hc (d := offset 1 + 28) (by decide) (by decide) fun s2 u2 => wp_srl (by decide) fun s3 u3 => ?_
  have hr3 : Rest [.a4, .a5] s s3 := (u2.rest (by decide)).trans (u3.rest (by decide))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  refine sw0_ok hc3 (d := SIGN) (by decide) (by decide) fun s4 u4 => ?_
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest []) (by decide)
  refine wp_sll (by decide) fun s5 u5 => wp_srl (by decide) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := hc4.of_rest ((u5.rest (ws := [.a4]) (by decide)).trans (u6.rest (by decide))) (by decide)
  refine sw0_ok hc6 (d := offset 1 + 28) (by decide) (by decide) fun s7 u7 => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hr3.trans ((u4.rest _).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest _))))
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem]
    refine Frame.writeW (Frame.writeW (Frame.refl _ _) List.mem_cons_self _ ?_)
      (List.mem_cons_of_mem _ List.mem_cons_self) _ ?_ <;> exact Region.contains_self _ _
  · have hw : (s2.gpr .a4).toNat = limb s.mem b (offset 1) 7 := by rw [u2.gpr, toNat_ext32]; rfl
    have hx : limb s.mem b (offset 1) 7 / 2 ^ 31 < 2 := by have := limb_lt s.mem b (offset 1) 7; omega_arith
    unfold SignAt
    rw [u7.mem, Mem.readW_writeW_sep (Offset.sep b (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), u6.mem,
      u5.mem, u4.mem, Mem.readW_writeW_self32]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_ext32, toNat_lo32, u3.gpr, toNat_shr, hw, BitVec.toNat_ofNat, toNat_beq_one hx, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
  · show wd s7.mem b (offset 1 + 28) = _
    rw [u7.mem, wd_write_self, toNat_lo32, u6.gpr, u5.gpr, low31_val, u4.gpr, u3.other _ (by decide), u2.gpr,
      toNat_ext32]
    show (s.mem.readW (b + BitVec.ofNat 64 (offset 1 + 28)) 32).toNat % 2 ^ 31 % 2 ^ 32 = _
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
    rfl
  · intro j hj
    show wd s7.mem b (offset 1 + 4 * j) = wd s.mem b (offset 1 + 4 * j)
    rw [u7.mem, wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), u6.mem, u5.mem, u4.mem, wd,
      Mem.readW_writeW_sep (Offset.sep b (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), u3.mem, u2.mem]
    rfl

/-- **The encoding loaded**: `y` (bit 255 cleared) in slot 1, the sign at `SIGN`, and `a2` zero exactly
when `y < p`. -/
theorem pointDecodeLoad_ok {s : State} (hc : Ctx8 b s) {q : Addr} (h14 : s.gpr .s0 = q)
    (hr : ∀ k < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (0 + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 0, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 (offset 1), 32⟩) :
    WP isa pointDecodeLoad s fun t => DecKeep b s t ∧
      SignAt b (decodeLE (bytesAt s.mem q 32) / 2 ^ 255 == 1) t.mem ∧
      env t.mem b 1 = Proof.X25519.toFe (decodeLE (bytesAt s.mem q 32) % 2 ^ 255) ∧
      (t.gpr .a2 = 0 ↔ decodeLE (bytesAt s.mem q 32) % 2 ^ 255 < P) := by
  have h1 : offset 1 = 96 := rfl
  have hX := FR_eq
  unfold pointDecodeLoad canonicalY
  refine WP.seq (WP.append (unpackField_ok hc.ctx (by decide) h14 (o := offset 1) (src := 0) (by decide) (by decide) (by decide) hr hd)
    fun s1 ⟨r1, f1, l1⟩ => ?_)
  have hn : decodeLE (bytesAt s.mem q 32) = V s1.mem b (offset 1) :=
    bytes_of_words fun j hj => by rw [l1 j hj, Nat.zero_add]
  have hc1 : Ctx b s1 := hc.ctx.of_rest r1 (by decide)
  refine WP.mono (split_ok hc1) fun s2 ⟨r2, f2, sg2, l7, lj⟩ => ?_
  -- `y`, and the sign, from the top limb.
  have hv1 := val32_succ (limb s1.mem b (offset 1)) 7
  have hv2 := val32_succ (limb s2.mem b (offset 1)) 7
  have hA := val32_lt (f := limb s1.mem b (offset 1)) (n := 7) fun k _ => limb_lt _ _ _ _
  have hL := limb_lt s1.mem b (offset 1) 7
  rw [val32_congr lj, l7] at hv2
  rw [show (2 : Nat) ^ (32 * 7) = 2 ^ 224 from rfl] at hv1 hv2 hA
  have hy : V s2.mem b (offset 1) = decodeLE (bytesAt s.mem q 32) % 2 ^ 255 := by
    rw [hn, V, V, hv1, hv2]; omega_arith
  have hsg : decodeLE (bytesAt s.mem q 32) / 2 ^ 255 = limb s1.mem b (offset 1) 7 / 2 ^ 31 := by
    rw [hn, V, hv1]; omega_arith
  rw [← hsg] at sg2
  have r12 : Rest [.a4, .a5] s s2 := (r1.mono (by decide)).trans r2
  have hc2 : Ctx8 b s2 := hc.of_rest r12 (by decide)
  have hF2 : Frame [⟨b + BitVec.ofNat 64 SIGN, 4⟩, FA b] s.mem s2.mem := by
    refine (f1.sub fun r hr => ⟨FA b, by simp, ?_⟩).trans (f2.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega_arith) (by omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨FA b, by simp, Offset.sub b (by omega_arith) (by omega_arith)⟩
  -- `y` canonical.
  refine WP.seq (WP.mono (freeze_ok hc2.ctx 1) fun s3 ⟨r3, f3, _, v3⟩ => ?_)
  have hc3 : Ctx b s3 := hc2.ctx.of_rest r3 (by decide)
  refine WP.mono (wordsEqual_ok hc3 (a := offset 1) (c := FR) (by decide) (by decide) (by decide) (by decide)) fun t ⟨r4, m4, h4⟩ => ?_
  have hs3 : V s3.mem b (offset 1) = V s2.mem b (offset 1) := by
    unfold V
    exact val32_congr (limb_frame f3 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
  refine ⟨⟨(r12.mono (by decide)).trans ((r3.mono (by decide)).trans (r4.mono (by decide))),
    hF2.trans (by rw [m4]; exact (frame_FR f3).mono (by simp))⟩, ?_, ?_, ?_⟩
  · rw [m4]; exact sg2.frame (frame_FR f3)
  · rw [m4, ← hy, ← hs3]; rfl
  · rw [h4, hs3, v3, hy]
    generalize decodeLE (bytesAt s.mem q 32) % 2 ^ 255 = y
    rw [eq_comm, Nat.mod_eq_iff_lt (by decide)]

/-- **A point decoded**, from the 32 bytes at `s0`. -/
theorem pointDecode_ok {s : State} (hc : Ctx8 b s) {q : Addr} (h14 : s.gpr .s0 = q)
    (hr : ∀ k < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (0 + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 0, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 (offset 1), 32⟩) :
    WP isa pointDecode s fun t => DecKeep b s t ∧
      ∃ o, Spec.Ed25519.decodePoint (bytesAt s.mem q 32) = o ∧ DecodeResult b o t := by
  have hl : (bytesAt s.mem q 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  rw [Proof.Ed25519.decodePoint32 _ hl]
  unfold pointDecode
  refine WP.seq (WP.mono (pointDecodeLoad_ok hc h14 hr hd) fun s1 ⟨k1, sg1, y1, h5⟩ => ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest k1.rest (by decide)
  refine WP.ite (s1.gpr .a2 == 0) (eval_zero s1 .a2) (fun h => ?_) (fun h => ?_)
  · have hy := h5.mp (beq_iff_eq.mp h)
    refine WP.mono (recoverPoint_ok hc1 sg1) fun t ⟨kt, dt⟩ => ⟨k1.trans (DecKeep.of_dkeep kt), _, ?_, dt⟩
    rw [iteT hy, Proof.Ed25519.recoverResult_spec, y1]; rfl
  · have hy : ¬ decodeLE (bytesAt s.mem q 32) % 2 ^ 255 < P := fun hy =>
      absurd (beq_iff_eq.mpr (h5.mpr hy)) (by simpa using h)
    refine WP.mono (recoverInvalid_ok s1) fun t ⟨kt, _, dt⟩ => ⟨k1.trans (DecKeep.of_dkeep kt), none, ?_, dt⟩
    rw [iteF hy]

end

end VG.Proof.Ed25519.RISCV64
