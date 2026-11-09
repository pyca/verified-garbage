module

public import VerifiedGarbage.Proof.Ed448.RISCV64.VDecodeNeg
public import VerifiedGarbage.Proof.Ed448.RISCV64.VDecodeX
public import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.Proof.Ed448.Recover
import VerifiedGarbage.Proof.Ed448.Root
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseBits
import VerifiedGarbage.Proof.X448.RISCV64.Setup
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.X448.Invert
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Ed448.RISCV64.VerifyEquation
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
import VerifiedGarbage.Proof.Ed448.RISCV64.VDecodeCheck
public import VerifiedGarbage.Proof.Ed448.RISCV64.VDecodeY
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Ladder

/-!
# Ed448's verification on RISCV64: decoding a point

`decode p xo yo` decodes the 57 bytes at `p` (RFC 8032 §5.2.3): `BAD` stays 0
exactly when they encode a point, and then `xo` and `yo` hold the
coordinates of its negation (`decode_ok`), by `decodePoint_impl`.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (X2 Y ACC)
open VG.Spec.X448 (P Fe)
open VG.Spec.Ed448 (Point)

theorem fin_neg_neg {n : Nat} [NeZero n] (x : Fin n) : 0 - (0 - x) = x := by grind

theorem fin_neg_sub {n : Nat} [NeZero n] (x : Fin n) : (x - x) - x = 0 - x := by rw [Fin.sub_self]

/-- The negation of the decoded x-coordinate, as `decodeNeg` selects it. -/
theorem neg_pick (x : Fe) {sg : Nat} (hsg : sg ≤ 1) :
    pick (x.val % 2 ^^^ sg) ((x - x) - x) x =
      0 - (if (x.val % 2 == 1) == (sg == 1) then x else (x - x) - x) := by
  rw [fin_neg_sub]
  rcases Nat.mod_two_eq_zero_or_one x.val with h | h <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsg with rfl | rfl <;>
    simp only [h, pick, VG.Proof.X25519.sel, Nat.reduceXor, ↓reduceIte, beq_self_eq_true,
      Nat.zero_ne_one, beq_iff_eq] <;> first | rfl | exact (fin_neg_neg x).symm

/-- The regions `decode` writes. -/
abbrev decW (b : Addr) (xo yo : Nat) : List Region :=
  yW b ++ [⟨b + BitVec.ofNat 64 DECODE_RA, 8⟩, ⟨b + BitVec.ofNat 64 xo, 56⟩, ⟨b + BitVec.ofNat 64 yo, 56⟩]

section
variable {b : Addr}

theorem decode_eq (p xo yo : Nat) : decode p xo yo =
    .seq (.block (decodeY p)) (.seq decodeCoreCall (.block (decodeNeg xo yo))) := rfl

/-- The 57 bytes at `p` in terms of the words and the last byte. -/
theorem bytes57 (m : Mem) (p : Nat) :
    Spec.Ed448.decodeLE ((Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 p) 57).take 56) = yw m b p ∧
      ((Spec.Ed448.bytesAt m (b + BitVec.ofNat 64 p) 57).getD 56 0).toNat =
        (m (b + BitVec.ofNat 64 (p + 56))).toNat := by
  constructor
  · rw [show (57 : Nat) = 56 + 1 from rfl, Proof.Ed448.bytesAt_eq, Proof.X25519.bytesAt_add,
      List.take_left' (by simp [Spec.X25519.bytesAt]), Proof.Ed448.decodeLE_eq, show (56 : Nat) = 4 * 14 from rfl]
    rw [show Spec.X25519.bytesAt m (b + BitVec.ofNat 64 p) (4 * 14) =
      VG.Spec.X448.bytesAt m (b + BitVec.ofNat 64 p) (4 * 14) from rfl, leNum_bytesAt4]
    exact val32_congr fun k _ => wd_shift _ _ _ _
  · rw [getD_bytesAt _ _ (by decide), Offset.add_add]

/-- The writes of the shared core and its return-address slot. -/
abbrev coreW (b : Addr) : List Region := yW b ++ [⟨b + BitVec.ofNat 64 DECODE_RA, 8⟩]

/-- The decoded candidate, sign, canonical bytes and accumulated checks. -/
def CoreFacts (b : Addr) (y : Fe) (sg : Nat) (m : Mem) (t : State) : Prop :=
  FS t.mem b DXX = xOf y ∧ FS t.mem b DY = y ∧ FS t.mem b DK = Spec.Ed448.d ∧
  t.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg ∧
  VG.Spec.X448.bytesAt t.mem (b + BitVec.ofNat 64 OUT) 56 = Proof.X25519.leBytes 56 (xOf y).val ∧
  (bad t.mem b = 0 ↔ bad m b = 0 ∧ vOf y * (xOf y * xOf y) = uOf y ∧ ¬ (xOf y = 0 ∧ sg = 1))

theorem decodeCore_ok {s : State} (hc : VCtx b s) {y : Fe} (hy : FS s.mem b DY = y)
    (hon : FS s.mem b DON = 1) (hd : FS s.mem b DK = Spec.Ed448.d) {sg : Nat}
    (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa decodeCore s fun t => VCtx b t ∧ Rest R64.work s t ∧ Frame (yW b) s.mem t.mem ∧
      CoreFacts b y sg s.mem t := by
  unfold decodeCore
  refine WP.seq (WP.mono (decodeX_ok hc.ctx hy hon hd)
    fun s2 ⟨hst2, hc2', hx2, hv2, hu2, hy2, hd2⟩ => ?_)
  have hc2 : VCtx b s2 := hc.of_rest hst2.rest (by decide) (by decide)
  have hs2 : s2.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg := by
    rw [← hs]
    exact hst2.frame _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun h => Offset.disjoint_base b (d := SIGN) (n := 1) (k := ACC + 112) (by decide) (by decide) _
        (Region.contains_self _ _) h
  refine WP.mono (decodeCheck_ok hc2 hx2 hv2 hu2 hsg hs2)
    fun s3 ⟨hc3, hr3, hf3, hk3, hs3, hout3, hb3⟩ => ?_
  have hb2 : bad s2.mem b = bad s.mem b := by
    unfold bad
    rw [hst2.frame.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by decide) (by decide)) (by decide)]
  exact ⟨hc3, hst2.rest.trans hr3, (hst2.frame.mono (by simp [yW])).trans hf3,
    by rw [hk3 DXX (by simp), hx2], by rw [hk3 DY (by simp), hy2],
    by rw [hk3 DK (by simp), hd2], hs3.trans hs2, hout3, by rwa [hb2] at hb3⟩

/-- The shared decode call preserves its caller's return address, including
across its nested exponentiation call. -/
theorem decodeCoreCall_ok {s : State} (hc : VCtx b s) {y : Fe} (hy : FS s.mem b DY = y)
    (hon : FS s.mem b DON = 1) (hd : FS s.mem b DK = Spec.Ed448.d) {sg : Nat}
    (hsg : sg ≤ 1) (hs : s.mem (b + BitVec.ofNat 64 SIGN) = BitVec.ofNat 8 sg) :
    WP isa decodeCoreCall s fun t => VCtx b t ∧ Rest R64.work s t ∧ Frame (coreW b) s.mem t.mem ∧
      CoreFacts b y sg s.mem t := by
  unfold decodeCoreCall
  refine WP.seq (R64.sd_ok hc.ctx (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  have hc1 := hc.of_rest (u1.rest []) (by decide) (by decide)
  have fs : Frame [⟨b + BitVec.ofNat 64 DECODE_RA, 8⟩] s.mem s1.mem := by
    rw [u1.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have keepFS {q : Nat} (hq : q + 56 ≤ DECODE_RA) : FS s1.mem b q = FS s.mem b q := by
    have e := limb_frame fs (o := q) fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      have hRA : DECODE_RA = 1712 := rfl
      exact Offset.disjoint b (.inl (by omega)) (by omega) (by decide)
    rw [FS, V, val32_congr e]; rfl
  have hsign : s1.mem (b + BitVec.ofNat 64 SIGN) = s.mem (b + BitVec.ofNat 64 SIGN) :=
    fs _ fun r hr hcon => by
      rw [List.mem_singleton.mp hr] at hcon
      exact Offset.disjoint b (d := SIGN) (n := 1) (e := DECODE_RA) (k := 8)
        (by decide) (by decide) (by decide) _ (Region.contains_self _ _) hcon
  have hbad : bad s1.mem b = bad s.mem b := by
    unfold bad
    rw [fs.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint b (by decide) (by decide) (by decide)) (by decide)]
  have hcE : VCtx b s1.callEntry := ⟨⟨hc1.ctx.a3, hc1.ctx.al, hc1.ctx.wr⟩, hc1.ws, hc1.a0⟩
  obtain ⟨tr, s2, he, hc2, hr2, hf2, facts⟩ := decodeCore_ok hcE
    ((keepFS (q := DY) (by decide)).trans hy) ((keepFS (q := DON) (by decide)).trans hon)
    ((keepFS (q := DK) (by decide)).trans hd) hsg (hsign.trans hs)
  have hra := hr2.gpr .ra (by decide)
  have hret : isa.ret s1.callEntry s2 = some s2 := by simp only [isa, ret, hra, ↓reduceIte]
  refine WP.seq ⟨_, s2, Exec.call (call_callEntry s1) he hret, ?_⟩
  have saved : s2.mem.readW (b + BitVec.ofNat 64 DECODE_RA) 64 = s.gpr .ra := by
    rw [hf2.readW (Region.contains_self _ (64 / 8)) ?_ (by decide), State.callEntry_mem,
      u1.mem, Mem.readW_writeW_self64]
    intro r hr
    simp only [yW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base b (by decide) (by decide)
    all_goals exact Offset.disjoint b (by decide) (by decide) (by decide)
  refine R64.ld_ok hc2.ctx (by decide) (by decide) fun s3 u3 => WP.block_nil ?_
  have rest : Rest R64.work s s3 := by
    refine ⟨?_, u3.rd.trans (hr2.rd.trans u1.rd), u3.wr.trans (hr2.wr.trans u1.wr),
      u3.sp.trans (hr2.sp.trans u1.sp)⟩
    intro r hr
    by_cases er : r = .ra
    · subst r; exact u3.gpr.trans saved
    · rw [u3.other r er, hr2.gpr r hr,
        State.callEntry_gpr s1 (by
          have hn : ∀ (r : Reg), r ∉ R64.work → r ≠ Reg.ra → r ∉ linkRegs := by
            intro r; cases r <;> simp [R64.work, linkRegs]
          exact hn r hr er), u1.gpr]
  refine ⟨hc2.of_rest (u3.rest (ws := [.ra]) (by decide)) (by decide) (by decide), rest, ?_, ?_⟩
  · rw [u3.mem]
    exact (fs.mono (by simp [coreW])).trans (hf2.mono (by simp [coreW]))
  · unfold CoreFacts at facts ⊢
    rw [u3.mem]
    simpa only [State.callEntry_mem, hbad] using facts

theorem decode_ok (hR : Proof.Ed448.RecoverOk) {s : State} (hc : VCtx b s) {p : Nat} (hp : 1064 ≤ p)
    (hp' : p + 57 ≤ 1696) (hp4 : p % 4 = 0) {xo yo : Nat} (ho : NegOut xo yo) (hd : FS s.mem b DK = Spec.Ed448.d) :
    WP isa (decode p xo yo) s fun t => VCtx b t ∧ Rest R64.work s t ∧ Frame (decW b xo yo) s.mem t.mem ∧
      FS t.mem b DK = Spec.Ed448.d ∧
      (bad t.mem b = 0 ↔ bad s.mem b = 0 ∧
        (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57)).isSome) ∧
      ∀ pt, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57) = some pt →
        FS t.mem b xo = 0 - pt.X ∧ FS t.mem b yo = pt.Y ∧ pt.Z = 1 := by
  rw [decode_eq]
  refine WP.seq (WP.mono (decodeY_ok hc hp hp' hp4) fun s1 ⟨hc1, hr1, hf1, hy1, hon1, hk1, hs1, hb1⟩ => ?_)
  generalize hB : (s.mem (b + BitVec.ofNat 64 (p + 56))).toNat = B at hs1 hb1
  have hBl : B < 256 := by rw [← hB]; exact BitVec.isLt _
  have hsg : B / 128 ≤ 1 := by omega
  generalize hY : VG.Proof.X448.toFe (yw s.mem b p) = y
  have hy : FS s1.mem b DY = y := by rw [FS, hy1, hY]
  have hon : FS s1.mem b DON = 1 := by rw [FS, hon1]; rfl
  refine WP.seq (WP.mono (decodeCoreCall_ok hc1 hy hon (hk1.trans hd) hsg hs1)
    fun s3 ⟨hc3, hr3, hf3, hx3, hy3, hd3, hs3, hout3, hb3⟩ => ?_)
  refine WP.mono (decodeNeg_ok hc3 ho hx3 hy3 hout3 hsg hs3)
    fun t ⟨hct, hrt, hft, hxt, hyt, hkt⟩ => ?_
  obtain ⟨ho1, ho2, ho3, ho4, ho5, -, -⟩ := ho
  have hPK : PK = 1456 := rfl
  obtain ⟨o1, o2, o3, o4⟩ := offs
  -- The code's view of `decodePoint`.
  obtain ⟨e56, eB⟩ := bytes57 (b := b) s.mem p
  rw [hB] at eB
  have hdp := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem (b + BitVec.ofNat 64 p) 57)
    (by simp [Spec.Ed448.bytesAt]) _ B e56 eB y (uOf y) (vOf y) (tOf y) (xOf y) hY rfl rfl rfl (by
      rw [xOf, Proof.Ed448.rootPow_eq, VG.Proof.X448.pow_pw]; rfl)
  have hbt : bad t.mem b = bad s3.mem b := by
    unfold bad
    rw [hft.readW (Region.contains_self _ (64 / 8)) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint_base _ (by decide) (by decide)
      all_goals exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)]
  refine ⟨hct, hr1.mono (by decide) |>.trans (hr3.trans (hrt.mono (by decide))), ?_,
    by rw [hkt, hd3], ?_, ?_⟩
  · -- The frame.
    refine (hf1.mono (by simp [decW])).trans ((hf3.mono (by simp [coreW, decW])).trans (hft.mono ?_))
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [decW]
  · -- The checks.
    rw [hbt, hb3, hb1, hdp]
    by_cases hC : (B % 128 = 0 ∧ yw s.mem b p < P) ∧ vOf y * (xOf y * xOf y) = uOf y ∧
        ¬ (xOf y = 0 ∧ B / 128 = 1)
    · rw [ite_eq_left hC, Option.isSome_some]
      exact ⟨fun h => ⟨h.1.1, rfl⟩, fun h => ⟨⟨h.1, hC.1.2, hC.1.1⟩, hC.2⟩⟩
    · rw [ite_eq_right hC, Option.isSome_none]
      exact ⟨fun ⟨⟨h1, h2, h3⟩, h4⟩ => absurd ⟨⟨h3, h2⟩, h4⟩ hC, fun h => absurd h.2 (by decide)⟩
  · intro pt hpt
    rw [hdp] at hpt
    by_cases hC : (B % 128 = 0 ∧ yw s.mem b p < P) ∧ vOf y * (xOf y * xOf y) = uOf y ∧
        ¬ (xOf y = 0 ∧ B / 128 = 1)
    · rw [ite_eq_left hC] at hpt
      cases Option.some.inj hpt
      exact ⟨by rw [hxt, neg_pick _ hsg], hyt, rfl⟩
    · rw [ite_eq_right hC] at hpt
      exact absurd hpt (by simp)

end

end VG.Proof.Ed448.RISCV64
