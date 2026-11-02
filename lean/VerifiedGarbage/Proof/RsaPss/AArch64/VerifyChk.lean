module

public import VerifiedGarbage.Proof.RsaPss.AArch64.VerifySpec
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncCall
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.AArch64.SignCEnc

/-!
# RSASSA-PSS verification on AArch64, around the check of the encoding: its call

After the public-key operation (`AfterCall`), `chkArgs` sets `x26` to 1 if
`lo = 0` or RSAVP1's first byte is zero, and `checkEncoding`'s arguments:
the last `emLen` bytes of RSAVP1's output, and the working space from the
next multiple of 8 (`chkArgs_ok`, `AtChkC`), which meet its contract
(`chkOk_of`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Vfy

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_add wp_sub wp_addImm wp_subImm wp_movz wp_and wp_lsr wp_lsl
  wp_ldrb)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_mov)
open VG.Proof.RsaPss.AArch64 (off ChkOk stkR shr3_ofNat shl3_ofNat)
open VG.Proof.RsaPss.AArch64.Sgn (stk kR kb fb fb_eq frame_sub0 below_sub in_frame)

/-- The working space's words that RSAVP1's output takes. -/
abbrev cwV (s : State) : Nat := ((s.gpr .x1).toNat + 7) / 8

/-- The flag: `lo = 0`, or the leading byte zero. -/
theorem flag_eq (b : Byte) {lo : Nat} (hlo : lo ≤ 1) :
    ((b.setWidth 64 &&& ((BitVec.ofNat 16 0).setWidth 64 - BitVec.ofNat 64 lo)) - BitVec.ofNat 64 1) >>> 63 =
      if lo = 0 ∨ b = 0 then 1 else 0 := by
  rcases (by omega : lo = 0 ∨ lo = 1) with rfl | rfl
  · simp
  · have e : ((BitVec.ofNat 16 0).setWidth 64 - BitVec.ofNat 64 1 : BitVec 64) = BitVec.allOnes 64 := by decide
    rw [e, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    have hb := b.isLt
    by_cases h : b = 0
    · subst h; decide
    · have h' : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
      rw [ite_eq_right fun h1 => h1.elim (by omega) h]
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      rw [show (0 : BitVec 64).toNat = 0 from rfl]
      omega

/-- At the call of `checkEncoding`. -/
structure AtChkC (K : Nat) (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [kR K s, sR s] s.mem t.mem
  fr : Fr s t.mem
  res : Cons s → Spec.Rsa.bytesAt t.mem (scr s) (s.gpr .x1).toNat = pubX s
  x0 : t.gpr .x0 = s.gpr .x4
  x1 : t.gpr .x1 = off (scr s) (loS s)
  x2 : t.gpr .x2 = BitVec.ofNat 64 (elS s)
  x3 : t.gpr .x3 = BitVec.ofNat 64 (ebS s)
  x4 : t.gpr .x4 = s.gpr .x7
  x5 : t.gpr .x5 = anyV s
  x6 : t.gpr .x6 = off (scr s) (8 * cwV s)
  x7 : t.gpr .x7 = stackArg s 2 - BitVec.ofNat 64 (cwV s)
  x26 : t.gpr .x26 = if loS s = 0 ∨ t.mem (scr s) = 0 then 1 else 0

theorem written_getD {m : Mem} {out : Addr} {n : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (h : Spec.Rsa.written m out n r o) : Spec.Rsa.bytesAt m out n = o.getD (Spec.RsaPss.zeros n) := by
  cases o with
  | none => exact h.2
  | some x => exact h.2

theorem chkArgs_ok {D K : Nat} {s t : State} (hp : PreV D K s) (h0 : s.mem (s.gpr .x0) ≠ 0)
    (ha : AfterCall K s (ebS s) (elS s) (loS s) t) : WP isa (.block chkArgs) t (AtChkC K s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  obtain ⟨-, -, -, hlo⟩ := eb_bounds hk1 hk2 h0
  have rsl : ∀ {u : State} {d : Nat}, u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      d + 8 ≤ frameBytes → InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr hd => by
    rw [hsp, hrd, hwr]
    exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega_arith)))
  unfold chkArgs ld movi
  refine wp_add fun u₁ o₁ e₁ => wp_ldrb (by decide) (a := scr s) (by rw [o₁.get .x20, ha.x20, BitVec.add_zero])
    (by
      rw [o₁.rd, o₁.wr, ha.rd, ha.wr]
      have hc := Offset.contains_base (scr s) (d := 0) (n := 1) (k := (stackArg s 2).toNat * 8)
        (by have := hp.hs; omega_arith) (by decide)
      rw [BitVec.add_zero] at hc
      exact InRegions_append_cons.mpr (.inr ⟨sR s, List.mem_append_right _ hp.hws, hc⟩))
    fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ => wp_sub fun u₄ o₄ e₄ => wp_and fun u₅ o₅ e₅ =>
    wp_subImm (by decide) fun u₆ o₆ e₆ => wp_lsr (by decide) fun u₇ o₇ e₇ => ?_
  have O₇ : Only [.x1, .x9, .x10, .x26] t u₇ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans
    (o₆.trans o₇)))))).mono
  have x26₇ : u₇.gpr .x26 = if loS s = 0 ∨ t.mem (scr s) = 0 then 1 else 0 := by
    rw [e₇, e₆, e₅, e₄, e₃, o₃.get .x26, o₂.get .x26, o₁.get .x26, ha.x26, o₄.get .x9, o₃.get .x9, e₂,
      o₁.mem, flag_eq _ hlo]
  have sp₇ : u₇.sp = fb s := by rw [O₇.sp, ha.sp]
  have rd₇ : u₇.rd = s.rd := by rw [O₇.rd, ha.rd]
  have wr₇ : u₇.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [O₇.wr, ha.wr]
  have mem₇ : u₇.mem = t.mem := O₇.mem
  refine wp_ldrSp (by decide) (rsl sp₇ rd₇ wr₇ (by decide)) fun u₈ o₈ e₈ => wp_mov fun u₉ o₉ e₉ =>
    wp_mov fun u₁₀ o₁₀ e₁₀ => ?_
  have sp₁₀ : u₁₀.sp = fb s := by rw [o₁₀.sp, o₉.sp, o₈.sp, sp₇]
  have rd₁₀ : u₁₀.rd = s.rd := by rw [o₁₀.rd, o₉.rd, o₈.rd, rd₇]
  have wr₁₀ : u₁₀.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₁₀.wr, o₉.wr, o₈.wr, wr₇]
  have mem₁₀ : u₁₀.mem = t.mem := by rw [o₁₀.mem, o₉.mem, o₈.mem, mem₇]
  refine wp_ldrSp (by decide) (rsl sp₁₀ rd₁₀ wr₁₀ (by decide)) fun u₁₁ o₁₁ e₁₁ => ?_
  refine wp_ldrSp (by decide) (by rw [o₁₁.sp, o₁₁.rd, o₁₁.wr]; exact rsl sp₁₀ rd₁₀ wr₁₀ (by decide))
    fun u₁₂ o₁₂ e₁₂ => wp_addImm (by decide) fun u₁₃ o₁₃ e₁₃ => wp_lsr (by decide) fun u₁₄ o₁₄ e₁₄ => ?_
  have sp₁₄ : u₁₄.sp = fb s := by rw [o₁₄.sp, o₁₃.sp, o₁₂.sp, o₁₁.sp, sp₁₀]
  have rd₁₄ : u₁₄.rd = s.rd := by rw [o₁₄.rd, o₁₃.rd, o₁₂.rd, o₁₁.rd, rd₁₀]
  have wr₁₄ : u₁₄.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₁₄.wr, o₁₃.wr, o₁₂.wr, o₁₁.wr, wr₁₀]
  have mem₁₄ : u₁₄.mem = t.mem := by rw [o₁₄.mem, o₁₃.mem, o₁₂.mem, o₁₁.mem, mem₁₀]
  refine wp_ldrSp (by decide) (rsl sp₁₄ rd₁₄ wr₁₄ (by decide)) fun u₁₅ o₁₅ e₁₅ => wp_sub fun u₁₆ o₁₆ e₁₆ =>
    wp_lsl (by decide) fun u₁₇ o₁₇ e₁₇ => wp_add fun u₁₈ o₁₈ e₁₈ => wp_nil ?_
  have O : Only [.x0, .x2, .x3, .x4, .x5, .x6, .x7, .x9] u₇ u₁₈ :=
    (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans (o₁₂.trans (o₁₃.trans (o₁₄.trans (o₁₅.trans (o₁₆.trans
      (o₁₇.trans o₁₈)))))))))).mono
  have x9₁₄ : u₁₄.gpr .x9 = BitVec.ofNat 64 (cwV s) := by
    rw [e₁₄, e₁₃, o₁₂.get .x23, o₁₁.get .x23, o₁₀.get .x23, o₉.get .x23, o₈.get .x23, O₇.get .x23, ha.x23,
      ← (BitVec.ofNat_toNat 64 (s.gpr .x1)).trans (BitVec.setWidth_eq _), BitVec.ofNat_add_ofNat,
      shr3_ofNat (by omega)]
  have hcw : cwV s < 2 ^ 60 := by unfold cwV; omega
  have F := ha.fr
  rw [sp₇, mem₇, F.rs (.x4, sDig) (by simp [regSlots])] at e₈
  rw [sp₁₀, mem₁₀, F.rs (.x7, sSaltLen) (by simp [regSlots])] at e₁₁
  rw [o₁₁.sp, sp₁₀, o₁₁.mem, mem₁₀, F.any] at e₁₂
  rw [sp₁₄, mem₁₄, F.scr] at e₁₅
  have mem : u₁₈.mem = t.mem := by rw [O.mem, mem₇]
  exact {
    sp := by rw [O.sp, sp₇]
    rd := by rw [O.rd, rd₇]
    wr := by rw [O.wr, wr₇]
    v := fun r hr => by rw [O.vcs r hr, O₇.vcs r hr, ha.v r hr]
    mem := by rw [mem]; exact ha.mem
    fr := by rw [mem]; exact F
    res := fun hc => by rw [mem]; exact written_getD (ha.res hc)
    x0 := by
      rw [o₁₈.get .x0, o₁₇.get .x0, o₁₆.get .x0, o₁₅.get .x0, o₁₄.get .x0, o₁₃.get .x0, o₁₂.get .x0,
        o₁₁.get .x0, o₁₀.get .x0, o₉.get .x0, e₈]
    x1 := by
      rw [O.get .x1, o₇.get .x1, o₆.get .x1, o₅.get .x1, o₄.get .x1, o₃.get .x1, o₂.get .x1, e₁, ha.x20, ha.x26]
    x2 := by
      rw [o₁₈.get .x2, o₁₇.get .x2, o₁₆.get .x2, o₁₅.get .x2, o₁₄.get .x2, o₁₃.get .x2, o₁₂.get .x2,
        o₁₁.get .x2, o₁₀.get .x2, e₉, o₈.get .x25, O₇.get .x25, ha.x25]
    x3 := by
      rw [o₁₈.get .x3, o₁₇.get .x3, o₁₆.get .x3, o₁₅.get .x3, o₁₄.get .x3, o₁₃.get .x3, o₁₂.get .x3,
        o₁₁.get .x3, e₁₀, o₉.get .x24, o₈.get .x24, O₇.get .x24, ha.x24]
    x4 := by
      rw [o₁₈.get .x4, o₁₇.get .x4, o₁₆.get .x4, o₁₅.get .x4, o₁₄.get .x4, o₁₃.get .x4, o₁₂.get .x4, e₁₁]
    x5 := by rw [o₁₈.get .x5, o₁₇.get .x5, o₁₆.get .x5, o₁₅.get .x5, o₁₄.get .x5, o₁₃.get .x5, e₁₂]
    x6 := by
      rw [e₁₈, o₁₇.get .x20, o₁₆.get .x20, o₁₅.get .x20, o₁₄.get .x20, o₁₃.get .x20, o₁₂.get .x20,
        o₁₁.get .x20, o₁₀.get .x20, o₉.get .x20, o₈.get .x20, O₇.get .x20, ha.x20, e₁₇, o₁₆.get .x9,
        o₁₅.get .x9, x9₁₄, shl3_ofNat hcw]
    x7 := by rw [o₁₈.get .x7, o₁₇.get .x7, e₁₆, e₁₅, o₁₅.get .x9, x9₁₄]
    x26 := by rw [O.get .x26, x26₇, mem] }

theorem cw_toNat {D K : Nat} {s : State} (hp : PreV D K s) :
    (stackArg s 2 - BitVec.ofNat 64 (cwV s)).toNat = (stackArg s 2).toNat - cwV s := by
  have := hp.hs; have := hp.k2
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := (stackArg s 2).isLt
  unfold cwV at *
  omega

/-- The call's arguments meet `checkEncoding`'s contract. -/
theorem chkOk_of {D K : Nat} {s t : State} (hp : PreV D K s) {cK : Nat} (hcK : cK ≤ K)
    (h0 : s.mem (s.gpr .x0) ≠ 0) (ha : AtChkC K s t) : ChkOk D cK t := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hws : (scr s).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 := hp.ws
  have hhs := hp.hs
  have hsc := cw_toNat hp
  obtain ⟨hb1, hb2, hlok, hlo⟩ := eb_bounds hk1 hk2 h0
  have hcw : (s.gpr .x1).toNat ≤ 8 * cwV s ∧ 8 * cwV s ≤ (s.gpr .x1).toNat + 7 := by unfold cwV; omega
  have hK := Sgn.below_kR (K := K) (cK := cK) s hcK
  have hSem : Region.Sub ⟨off (scr s) (loS s), elS s⟩ (sR s) := Offset.sub_base _ (by omega)
  have hSsc : Region.Sub ⟨off (scr s) (8 * cwV s), (stackArg s 2 - BitVec.ofNat 64 (cwV s)).toNat * 8⟩ (sR s) :=
    Offset.sub_base _ (by rw [hsc]; omega)
  have he : (BitVec.ofNat 64 (elS s)).toNat = elS s := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show elS s < 2 ^ 64 by omega)]
  have hb : (BitVec.ofNat 64 (ebS s)).toNat = ebS s := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ebS s < 2 ^ 64 by unfold Proof.RsaPss.maxEmBits at hb2; omega)]
  have hwem : (off (scr s) (loS s)).toNat + elS s ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hwsc : (off (scr s) (8 * cwV s)).toNat + (stackArg s 2 - BitVec.ofNat 64 (cwV s)).toNat * 8 ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; rw [hsc]; omega
  exact {
    sp1 := by rw [ha.sp]; unfold stk at *; omega
    hrd := by
      simp only [VG.Proof.RsaPss.AArch64.chkRd]
      rw [ha.x0, ha.x1, ha.x2, he, ha.rd, ha.wr]
      refine Covers.cons (Covers.left (Covers.trans (Covers.of_mem fun x hx => by
        rw [List.mem_singleton.mp hx]; simp) hp.hrd)) (Covers.right (Covers.one ⟨sR s, List.mem_cons_of_mem _ hp.hws,
          Offset.contains_base _ (by omega) (by omega)⟩))
    hwr := by
      simp only [VG.Proof.RsaPss.AArch64.chkWr]
      rw [ha.x6, ha.x7, ha.wr]
      exact Covers.one ⟨sR s, List.mem_cons_of_mem _ hp.hws, Offset.contains_base _ (by rw [hsc]; omega)
        (by omega)⟩
    ds := by rw [ha.x0, ha.x6, ha.x7]; exact hp.dgs.sub_right hSsc
    es := by
      rw [ha.x1, ha.x2, ha.x6, ha.x7, he]
      exact Offset.disjoint _ (Or.inl (by omega)) (by omega) (by rw [hsc]; omega)
    kd := by rw [stkR, ha.sp, ha.x0]; exact hp.kdg.sub_left hK
    ke := by rw [stkR, ha.sp, ha.x1, ha.x2, he]; exact (hp.ks.sub_left hK).sub_right hSem
    ks := by rw [stkR, ha.sp, ha.x6, ha.x7]; exact (hp.ks.sub_left hK).sub_right hSsc
    wd := by rw [ha.x0]; exact hp.wdg
    we := by rw [ha.x1, ha.x2, he]; exact hwem
    ws := by rw [ha.x6, ha.x7]; exact hwsc
    b1 := by rw [ha.x3, hb]; exact hb1
    b2 := by rw [ha.x3, hb]; exact hb2
    hel := by rw [ha.x2, ha.x3, he, hb]
    hs := by rw [ha.x7, hsc]; unfold Proof.RsaPss.encodingScratchWords cwV at *; omega }

end VG.Proof.RsaPss.AArch64.Vfy
