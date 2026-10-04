import VerifiedGarbage.Impl.X25519.AArch64.Base
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseEngine
import VerifiedGarbage.Proof.Ed25519.AArch64.BitByte
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.X25519.Edwards.Ladder

/-!
# X25519 of the base point on AArch64: the engine

The expanded bits of the scalar, clamped (`clampBits_ok`), are those of
`decodeScalar25519` (`clamped_bit`); the comb computes `[k] B` from them
(`combMultiply_ok`), and `uEncode` its u-coordinate `(Z + Y) / (Z - Y)`, which
`Proof/X25519/Edwards/Ladder.lean` shows is `X25519(k, 9)` (`engine_ok`).
-/

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519 (Rep dZ baseAff toZ_add toZ_sub toZ_mul toZ_pow)
open VG.Spec.X25519 (Fe P decodeScalar25519)
open VG.Proof.Ed25519.Word64 (val4)

/-! ## The clamped bits -/

/-- A bit of the decoded scalar of 32 bytes is that of the bytes read as a
number, but for the clamped ones. -/
theorem clamped_bit {kb : List Byte} (hk : kb.length = 32) {q : Nat} (hq : q < 256) :
    (decodeScalar25519 kb / 2 ^ q) % 2 =
      if q < 3 ∨ q = 255 then 0 else if q = 254 then 1 else (Spec.Ed25519.decodeLE kb / 2 ^ q) % 2 := by
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.and_one_is_mod,
    ← Nat.and_one_is_mod]
  by_cases h255 : q = 255
  · subst h255
    rw [Edwards.decodeScalar25519_shift hk]; rfl
  · have hb := X25519.scalar_bit hk (t := q) (by omega)
    simp only [X25519.bit] at hb
    rw [hb, Proof.Ed25519.decodeLE_eq, X25519.leNum_bit]
    by_cases h3 : q < 3
    · simp only [h3, true_or, ↓reduceIte]
    · simp only [h3, h255, or_self, ↓reduceIte]

/-- A byte store at `base + d`, read at `base + e`. -/
theorem write1_off (m : Mem) (base : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64)
    (v : BitVec (8 * 1)) :
    (m.write (off base d) 1 v) (off base e) = if e = d then v.extractLsb' 0 8 else m (off base e) := by
  by_cases h : e = d
  · subst h; simp [Mem.write]
  · have hne : off base e ≠ off base d := fun h' => h ((off_eq_iff base he hd).mp h')
    simp only [Mem.write, sub_toNat_lt_one, hne, h, ite_false]

/-- A byte store at `base + d` leaves the other bytes. -/
theorem write1_outside (m : Mem) (base : Addr) {d : Nat} (hd : d < 2 ^ 64) {x : Addr}
    (hx : ofs base x ≠ d) (v : BitVec (8 * 1)) : (m.write (off base d) 1 v) x = m x := by
  have hne : x ≠ off base d := fun h => hx (by rw [h]; exact ofs_off' base hd)
  simp only [Mem.write, sub_toNat_lt_one, hne, ite_false]

/-- Clamping the expanded bits: five byte stores at `768 + q`. -/
theorem clampBits_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block clampBits) s fun t => PowersKeep base 56 7368 s t ∧
      ∀ q < 256, t.mem (off base (768 + q)) =
        if q < 3 ∨ q = 255 then 0 else if q = 254 then 1 else s.mem (off base (768 + q)) := by
  have _hcap : workSize true = 8192 := rfl
  have hw : ∀ d, 768 ≤ d → d < 1024 → InRegions s.wr (off base d) 1 := fun d h1 h2 =>
    ⟨_, hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have hx0 := hs.x0
  have e768 : base + 768#64 = off base 768 := rfl
  have e769 : base + 769#64 = off base 769 := rfl
  have e770 : base + 770#64 = off base 770 := rfl
  have e1022 : base + 1022#64 = off base 1022 := rfl
  have e1023 : base + 1023#64 = off base 1023 := rfl
  apply WP.of_runBlock
  simp only [clampBits, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    addr, State.store, RegUpd.gpr_write, RegUpd.wr_write, RegUpd.mem_write,
    hx0, hw 768 (by decide) (by decide), hw 769 (by decide) (by decide),
    hw 770 (by decide) (by decide), hw 1022 (by decide) (by decide), hw 1023 (by decide) (by decide),
    show 16 * 0 < Size.w.bits from by decide, Nat.mod_one, and_self,
    show 768 < 4096 * 1 from by decide, show 769 < 4096 * 1 from by decide,
    show 770 < 4096 * 1 from by decide, show 1022 < 4096 * 1 from by decide,
    show 1023 < 4096 * 1 from by decide,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [e768, e769, e770, e1022, e1023]
  dsimp only [RegUpd.mem_write, RegUpd.wr_write, RegUpd.rd_write, RegUpd.sp_write]
  refine ⟨⟨fun r _ _ hc => ?_, rfl, rfl, rfl, fun p _ hp => ?_⟩, fun q hq => ?_⟩
  · have : r ≠ .x9 := fun h => hc (by subst h; decide)
    simp only [RegUpd.gpr_write, this, ite_false]
  · dsimp only [RegUpd.mem_write]
    rw [write1_outside _ _ (by decide) (by omega), write1_outside _ _ (by decide) (by omega),
      write1_outside _ _ (by decide) (by omega), write1_outside _ _ (by decide) (by omega),
      write1_outside _ _ (by decide) (by omega)]
  · have he : 768 + q < 2 ^ 64 := by omega
    rw [write1_off _ _ (by decide) he, write1_off _ _ (by decide) he, write1_off _ _ (by decide) he,
      write1_off _ _ (by decide) he, write1_off _ _ (by decide) he]
    split_ifs <;> first | rfl | decide | (exfalso; omega)

/-! ## The u-coordinate -/

theorem uOps_eval (e : Env) :
    evalOps uOps e 0 = e 2 + e 1 ∧ evalOps uOps e 2 = e 2 - e 1 := by
  simp [uOps, evalOps, evalOp, Function.update]

theorem uEncode_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa uEncode s fun t => CounterKeep base s t ∧
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) =
        ((env s.mem base 2 + env s.mem base 1) *
          Spec.X25519.pow (env s.mem base 2 - env s.mem base 1) (P - 2)).val := by
  rw [uEncode]
  refine WP.seq (WP.mono (fieldCode_ok uOps hs) fun a ⟨ka, va⟩ => ?_)
  have kac : CounterKeep base s a := ⟨fun r hr _ => ka.gpr r hr, ka.rd, ka.wr, ka.sp, ka.mem⟩
  refine WP.seq (WP.mono (pointAffine_ok (kac.scr hs)) fun b ⟨kb, bx, _⟩ => ?_)
  refine WP.mono (freezeField_ok ((kb.scr (kac.scr hs))) 0) fun t ⟨tv, kt⟩ => ?_
  refine ⟨(kac.trans kb).trans (CounterKeep.of_keeps kt (by decide)), ?_⟩
  rw [tv, bx, va, (uOps_eval _).1, (uOps_eval _).2]

/-! ## The engine -/

/-- `(Z + Y) / (Z - Y)` of a representative of `a` is `(1 + y) / (1 - y)`. -/
theorem u_rep {p : Spec.Ed25519.Point} {a : VG.Proof.Ed25519.Edwards.EPoint dZ} (h : Rep p a) :
    Proof.Ed25519.toZ ((p.Z + p.Y) * Spec.X25519.pow (p.Z - p.Y) (P - 2)) = (1 + a.y) / (1 - a.y) := by
  rw [toZ_mul, toZ_add, toZ_pow, toZ_sub, Edwards.pow_P_sub_two, h.y]
  have hz := h.z
  by_cases hy : 1 - a.y = 0
  · rw [show Proof.Ed25519.toZ p.Z - a.y * Proof.Ed25519.toZ p.Z = (1 - a.y) * Proof.Ed25519.toZ p.Z by ring,
      hy]
    simp
  · rw [show Proof.Ed25519.toZ p.Z - a.y * Proof.Ed25519.toZ p.Z = (1 - a.y) * Proof.Ed25519.toZ p.Z by ring,
      show Proof.Ed25519.toZ p.Z + a.y * Proof.Ed25519.toZ p.Z = (1 + a.y) * Proof.Ed25519.toZ p.Z by ring]
    field_simp

theorem engine_ok {s : State} {base k : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa engine s fun t => PowersKeep base 56 7368 s t ∧ ∃ w : Fe,
      val4 (t.gpr .x4) (t.gpr .x5) (t.gpr .x6) (t.gpr .x7) = w.val ∧
      Spec.X25519.x25519 (Spec.Ed25519.bytesAt s.mem k 32) Spec.X25519.basePoint =
        Spec.X25519.encodeUCoordinate w := by
  have hk : (Spec.Ed25519.bytesAt s.mem k 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  set kb := Spec.Ed25519.bytesAt s.mem k 32
  rw [engine]
  refine WP.seq (WP.mono (scalarBasePrepare_ok hs hp hr hd) fun b ⟨kab, bbits, _⟩ => ?_)
  have hsb := kab.scratch hs
  refine WP.seq (WP.mono (clampBits_ok hsb) fun c ⟨kbc, cbits⟩ => ?_)
  have hsc := kbc.scratch hsb
  have hS : decodeScalar25519 kb < 2 ^ 256 := by
    have h := Edwards.decodeScalar25519_shift hk
    rw [Nat.shiftRight_eq_div_pow] at h
    have := (Nat.div_eq_zero_iff_lt (by positivity)).mp h
    omega
  have cb : ∀ q < 256, c.mem (off base (768 + q)) = BitVec.ofNat 8 ((decodeScalar25519 kb / 2 ^ q) % 2) := by
    intro q hq
    rw [cbits q hq, clamped_bit hk hq]
    split_ifs
    · rfl
    · rfl
    · exact bbits q (by simpa using hq)
  refine WP.seq (WP.mono (combMultiply_ok hsc hS cb) fun d ⟨dp, kd⟩ => ?_)
  refine WP.mono (uEncode_ok (kd.scr hsc)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨((kab.trans kbc).trans kd.powers).trans
    ⟨fun r hb _ hr => kt.gpr r hr hb, kt.rd, kt.wr, kt.sp, TableFrame.workspace kt.mem⟩, _, tv, ?_⟩
  exact VG.Proof.X25519.Edwards.x25519_basePoint hk _ (u_rep dp)

end VG.Proof.X25519.AArch64.Base
