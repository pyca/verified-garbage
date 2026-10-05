import VerifiedGarbage.Impl.X25519.AArch64.Base
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseVerified
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.Signing
import VerifiedGarbage.Proof.X25519.Edwards.Ladder
import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Base.Main`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Base.Engine`. -/
section

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
    rw [VG.Proof.X25519.AArch64.Base.write1_outside _ _ (by decide) (by omega), VG.Proof.X25519.AArch64.Base.write1_outside _ _ (by decide) (by omega),
      VG.Proof.X25519.AArch64.Base.write1_outside _ _ (by decide) (by omega), VG.Proof.X25519.AArch64.Base.write1_outside _ _ (by decide) (by omega),
      VG.Proof.X25519.AArch64.Base.write1_outside _ _ (by decide) (by omega)]
  · have he : 768 + q < 2 ^ 64 := by omega
    rw [VG.Proof.X25519.AArch64.Base.write1_off _ _ (by decide) he, VG.Proof.X25519.AArch64.Base.write1_off _ _ (by decide) he, VG.Proof.X25519.AArch64.Base.write1_off _ _ (by decide) he,
      VG.Proof.X25519.AArch64.Base.write1_off _ _ (by decide) he, VG.Proof.X25519.AArch64.Base.write1_off _ _ (by decide) he]
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
  rw [tv, bx, va, (VG.Proof.X25519.AArch64.Base.uOps_eval _).1, (VG.Proof.X25519.AArch64.Base.uOps_eval _).2]

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
  refine WP.seq (WP.mono (VG.Proof.X25519.AArch64.Base.clampBits_ok hsb) fun c ⟨kbc, cbits⟩ => ?_)
  have hsc := kbc.scratch hsb
  have hS : decodeScalar25519 kb < 2 ^ 256 := by
    have h := Edwards.decodeScalar25519_shift hk
    rw [Nat.shiftRight_eq_div_pow] at h
    have := (Nat.div_eq_zero_iff_lt (by positivity)).mp h
    omega
  have cb : ∀ q < 256, c.mem (off base (768 + q)) = BitVec.ofNat 8 ((decodeScalar25519 kb / 2 ^ q) % 2) := by
    intro q hq
    rw [cbits q hq, VG.Proof.X25519.AArch64.Base.clamped_bit hk hq]
    split_ifs
    · rfl
    · rfl
    · exact bbits q (by simpa using hq)
  refine WP.seq (WP.mono (combMultiply_ok hsc hS cb) fun d ⟨dp, kd⟩ => ?_)
  refine WP.mono (VG.Proof.X25519.AArch64.Base.uEncode_ok (kd.scr hsc)) fun t ⟨kt, tv⟩ => ?_
  refine ⟨((kab.trans kbc).trans kd.powers).trans
    ⟨fun r hb _ hr => kt.gpr r hr hb, kt.rd, kt.wr, kt.sp, TableFrame.workspace kt.mem⟩, _, tv, ?_⟩
  exact VG.Proof.X25519.Edwards.x25519_basePoint hk _ (VG.Proof.X25519.AArch64.Base.u_rep dp)

end VG.Proof.X25519.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Base.Erase`. -/
section

/-!
# X25519 of the base point on AArch64: the code without its immediates

Untrusted: everything here is checked by Lean. As for Ed25519's `scalarBase`
(`Proof/Ed25519/AArch64/CombErase.lean`): without the immediates of `movz` and
`movk`, the comb's 32 selections are table 0's (`engine_eraseImm`), so the
kernel builds and checks one selection, and no table's immediates, in the
constant-time analysis of `engine0` and the `keepsV` check of `x25519Base0`,
the code's only evaluations; the code has no literal.
-/

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64 (combMultiply0 combMultiply_eraseImm)

/-- `engine`, with every table's selection table 0's. -/
def engine0 : Prog isa :=
  .seq scalarBasePrepare (.seq (.block clampBits) (.seq combMultiply0 uEncode))

/-- `x25519Base`, with every table's selection table 0's. -/
def x25519Base0 : Prog isa :=
  .seq (.block (scalarSave ++ scalarBaseSetup)) (.seq VG.Proof.X25519.AArch64.Base.engine0 scalarBaseFinish)

theorem engine_eraseImm : Code.eraseImm engine = Code.eraseImm VG.Proof.X25519.AArch64.Base.engine0 := by
  simp only [engine, VG.Proof.X25519.AArch64.Base.engine0, Code.eraseImm, combMultiply_eraseImm]

theorem x25519Base_eraseImm : Code.eraseImm x25519Base = Code.eraseImm VG.Proof.X25519.AArch64.Base.x25519Base0 := by
  simp only [x25519Base, VG.Proof.X25519.AArch64.Base.x25519Base0, Code.eraseImm, VG.Proof.X25519.AArch64.Base.engine_eraseImm]

end VG.Proof.X25519.AArch64.Base

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Base.Main`. -/
section

/-!
# X25519 of the base point on AArch64: memory and ABI obligations

As Ed25519's `scalarBase` (`Proof/Ed25519/AArch64/ScalarBaseMain.lean`), with
the engine of `Engine.lean` and its result read as a u-coordinate.
-/

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64 (val4)
open VG.Spec.Ed25519 (bytesAt)

def baseLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x1, 32⟩] ∧ s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
    (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64
  post s t := Spec.X25519.bytesAt t.mem (s.gpr .x0) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem (s.gpr .x1) 32) Spec.X25519.basePoint
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2

theorem x25519Base_correct {s : State} (hs : baseLocal.pre s) :
    WP isa x25519Base s fun t => abiPreserved s t ∧ baseLocal.post s t := by
  apply WP.withPreservedV
    (hc := Code.allInstrs_keepsV_of_eraseImm VG.Proof.X25519.AArch64.Base.x25519Base_eraseImm (by lit_decide))
  obtain ⟨hr, hw, hd, hn⟩ := hs
  have hws : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [x25519Base]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok rfl hws) fun a ⟨ga, ra, wa, spa, ma, sva⟩ => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, wa]; exact hws
  refine WP.mono (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, spb, ob, mb⟩ => ?_
  rw [ga] at pb ob mb
  have hb : Scr b (s.gpr .x2) := ⟨pb, by rw [wb, wa]; exact hws, hn⟩
  have fm : Frame [⟨s.gpr .x2, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  have svb : Saved (s.gpr .x2) s.gpr b.mem := sva.outside mb (by decide)
  have input : bytesAt b.mem (s.gpr .x1) 32 = bytesAt s.mem (s.gpr .x1) 32 := bytesAt32_frame fm hd
  apply WP.seq
  refine WP.mono (VG.Proof.X25519.AArch64.Base.engine_ok hb ((gb _ (by decide)).trans (congrFun ga _))
    (fun q hq => ⟨⟨s.gpr .x1, 32⟩, by rw [rb, ra, hr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩)
    (fun q hq => farScr hd hq (by decide))) fun c ⟨kc, w, vc, xc⟩ => ?_
  have mc := powersKeep_outside kc
  have svc : Saved (s.gpr .x2) s.gpr c.mem := svb.outside mc (by decide)
  have oc : c.mem.readW (off (s.gpr .x2) 48) 64 = s.gpr .x0 :=
    (mc.word (d := 48) (Or.inl (by decide)) (by decide)).trans ob
  have wc : c.wr = s.wr := kc.wr.trans (wb.trans wa)
  rw [scalarBaseFinish]
  apply WP.seq
  refine WP.mono (scalarBaseFinishArgs_ok (kc.scratch hb)) fun d ⟨pd, od, kd⟩ => ?_
  have x2d : d.gpr .x2 = s.gpr .x2 := pd
  have x0d : d.gpr .x0 = s.gpr .x0 := od.trans oc
  have wd : d.wr = s.wr := kd.wr.trans wc
  rw [scalarFinish, WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) x2d (wd ▸ hws) (by rw [kd.mem]; exact svc))
    fun e ⟨re, ke⟩ => ?_
  have x0e : e.gpr .x0 = s.gpr .x0 := (ke.gpr _ (by decide)).trans x0d
  have hwo : (⟨s.gpr .x0, 32⟩ : Region) ∈ e.wr := by rw [ke.wr, wd, hw]; simp
  refine WP.mono (scalarOut_ok x0e hwo) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact re (.x19, 0) (by decide)
    · exact re (.x20, 8) (by decide)
    · exact re (.x21, 16) (by decide)
    · exact re (.x22, 24) (by decide)
    · exact re (.x23, 32) (by decide)
    · exact re (.x24, 40) (by decide)
    all_goals
      rw [ke.gpr _ (by decide), kd.gpr _ (by decide), kc.gpr _ (by decide) (by decide) (by decide),
        gb _ (by decide), ga]
  · exact ke.sp.trans (kd.sp.trans (kc.sp.trans (spb.trans spa)))
  · change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    change _ = Spec.X25519.x25519 (bytesAt s.mem (s.gpr .x1) 32) Spec.X25519.basePoint
    rw [bytesAt_st4, ← input, xc, Proof.X25519.encodeUCoordinate_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    rw [ke.gpr .x4 (by decide), ke.gpr .x5 (by decide), ke.gpr .x6 (by decide), ke.gpr .x7 (by decide),
      kd.gpr .x4 (by decide), kd.gpr .x5 (by decide), kd.gpr .x6 (by decide), kd.gpr .x7 (by decide)]
    exact vc

end VG.Proof.X25519.AArch64.Base

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.X25519.AArch64.Base.Verified`. -/
section

/-!
# X25519 of the base point on AArch64: constant time and the contract

As for Ed25519's `scalarBase`: the scalar's bits, the comb and the encoding
have a public trace (one taint check of the engine, whose addresses are the
working space `x0` plus constants or public counters), and so do the setup and
the finish.
-/

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64

theorem engine_ct (base k : Addr) :
    CT (fun x y => BaseEnginePre base k x ∧ BaseEnginePre base k y) engine (fun _ _ => True) := by
  apply CT.taint (Taint.ofRegs [.x0, .x1]) _
    (Taint.isSome_check_of_eraseImm engine_eraseImm (by taint_decide))
  intro x y h
  apply agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.x0.trans h.2.1.x0.symm
  · exact h.1.2.1.trans h.2.2.1.symm

private def BaseStart (base k out : Addr) (s : State) : Prop :=
  baseLocal.pre s ∧ s.gpr .x0 = out ∧ s.gpr .x1 = k ∧ s.gpr .x2 = base

private def BasePrepared (base k out : Addr) (s : State) : Prop :=
  BaseEnginePre base k s ∧ s.mem.readW (off base 48) 64 = out

private def BaseReady (base out : Addr) (s : State) : Prop :=
  Scr s base ∧ s.mem.readW (off base 48) 64 = out

private theorem start_ok {base k out : Addr} {s : State} (hs : BaseStart base k out s) :
    WP isa (.block (scalarSave ++ scalarBaseSetup)) s (BasePrepared base k out) := by
  obtain ⟨⟨hr, hw, hd, hn⟩, ho, hk, hb⟩ := hs
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hb]; simp
  rw [WP.block_append_iff]
  refine WP.mono (scalarSave_ok hb hws) fun a ⟨ga, ra, wa, _, _, _⟩ => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, hb, wa]; exact hws
  refine WP.mono (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, _, ob, _⟩ => ?_
  rw [ga, hb] at pb ob
  refine ⟨⟨⟨pb, by rw [wb, wa]; exact hws, by rw [← hb]; exact hn⟩,
    (gb _ (by decide)).trans ((congrFun ga _).trans hk), ?_, ?_⟩, ob.trans ho⟩
  · intro q hq
    exact ⟨⟨k, 32⟩, by rw [rb, ra, hr, hk]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  · intro q hq
    rw [hk, hb] at hd
    exact farScr hd hq (by decide)

private theorem start_ct (base k out : Addr) :
    CT (fun x y => BaseStart base k out x ∧ BaseStart base k out y)
      (.block (scalarSave ++ scalarBaseSetup))
      (fun x y => BasePrepared base k out x ∧ BasePrepared base k out y) := by
  have hc : CT (fun x y => BaseStart base k out x ∧ BaseStart base k out y)
      (.block (scalarSave ++ scalarBaseSetup)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0, .x1, .x2]) _ (by taint_decide)
    intro x y h
    apply agree_ofRegs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1.2.1.trans h.2.2.1.symm
    · exact h.1.2.2.1.trans h.2.2.2.1.symm
    · exact h.1.2.2.2.trans h.2.2.2.2.symm
  exact (hc.wp (fun _ _ h => ⟨start_ok h.1, start_ok h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem engine_ready {base k out : Addr} {s : State} (hs : BasePrepared base k out s) :
    WP isa engine s (BaseReady base out) := by
  refine WP.mono (engine_ok hs.1.1 hs.1.2.1 hs.1.2.2.1 hs.1.2.2.2) fun t ⟨kt, _⟩ => ?_
  exact ⟨kt.scratch hs.1.1, ((powersKeep_outside kt).word
    (d := 48) (Or.inl (by decide)) (by decide)).trans hs.2⟩

private theorem engine_ct' (base k out : Addr) :
    CT (fun x y => BasePrepared base k out x ∧ BasePrepared base k out y)
      engine (fun x y => BaseReady base out x ∧ BaseReady base out y) := by
  have hc := (engine_ct base k).mono
    (fun _ _ (h : BasePrepared base k out _ ∧ BasePrepared base k out _) => ⟨h.1.1, h.2.1⟩)
    (fun _ _ h => h)
  exact (hc.wp (fun _ _ h => ⟨engine_ready h.1, engine_ready h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

private theorem finish_ct (base out : Addr) :
    CT (fun x y => BaseReady base out x ∧ BaseReady base out y)
      scalarBaseFinish (fun _ _ => True) := by
  have hc : CT (fun x y => BaseReady base out x ∧ BaseReady base out y)
      (.block scalarBaseFinishArgs) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    intro x y h
    exact agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r; exact h.1.1.x0.trans h.2.1.x0.symm)
  have hw : ∀ s, BaseReady base out s → WP isa (.block scalarBaseFinishArgs) s
      (fun t => t.gpr .x2 = base ∧ t.gpr .x0 = out) := by
    intro s h
    exact WP.mono (scalarBaseFinishArgs_ok h.1) fun _ ht => ⟨ht.1, ht.2.1.trans h.2⟩
  have hc' := (hc.wp (fun _ _ h => ⟨hw _ h.1, hw _ h.2⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)
  rw [scalarBaseFinish]
  refine CT.seq hc' ?_
  apply CT.taint (Taint.ofRegs [.x2, .x0]) _ (by taint_decide)
  intro x y h
  apply agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.trans h.2.2.symm

theorem x25519Base_ct : ConstantTime isa baseLocal.pre baseLocal.pub x25519Base := by
  intro x y tx ty x' y' hx hy ⟨hsp, ho, hk, hb⟩ ex ey
  have hc := CT.seq (start_ct (x.gpr .x2) (x.gpr .x1) (x.gpr .x0))
    (CT.seq (engine_ct' (x.gpr .x2) (x.gpr .x1) (x.gpr .x0))
      (finish_ct (x.gpr .x2) (x.gpr .x0)))
  exact (hc _ _ _ _ _ _ ⟨hsp, ⟨hx, rfl, rfl, rfl⟩, ⟨hy, ho.symm, hk.symm, hb.symm⟩⟩ ex ey).1

theorem x25519Base_ok (s : State) (hs : baseLocal.pre s) :
    ∃ t s', Exec isa x25519Base s t s' ∧ abiPreserved s s' ∧ baseLocal.post s s' :=
  x25519Base_correct hs

theorem x25519Base_verified :
    Verified AArch64.target x25519Base (Spec.X25519.x25519BaseContract AArch64.abi) :=
  Verified.of_correct x25519Base_ok x25519Base_ct (by
    sig_implies [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig,
      AArch64.abi, AArch64.argRegs, baseLocal]
      [baseSatState] using baseSatState)

end VG.Proof.X25519.AArch64.Base

end
