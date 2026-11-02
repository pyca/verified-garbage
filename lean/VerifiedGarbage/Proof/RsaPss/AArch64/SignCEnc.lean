module

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCArgs
public import VerifiedGarbage.Proof.RsaPss.AArch64.EncCall
import VerifiedGarbage.Proof.RsaPss.AArch64.SignFrame
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPss.AArch64.CtComp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PSS signing on AArch64, around the encoding: the call of `encode`

With the parameters in `x24`–`x26` (`AtPar`), `encArgs` writes a zero byte at
`EM` and sets `encode`'s arguments (`encArgs_ok`, `AtEnc`), which meet its
contract (`encOk_of`); after the call, `EM` holds `lo` zero bytes and the
encoding, or `encode` returned 0 (`encCall_ok`, `AfterEnc`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_addImm wp_subImm wp_movz wp_add wp_strb)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_mov)
open VG.Proof.RsaPss.AArch64 (off off_add EncImpl EncOk encCall encWr stkR ebV)

/-- The parameters: `emBits = eb`, `emLen = el` and `lo` in `x24`–`x26`. -/
structure AtPar (K : Nat) (s : State) (eb el lo : Nat) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame (wrS K s) s.mem t.mem
  fr : Fr s t.mem
  x20 : t.gpr .x20 = scr s
  x23 : t.gpr .x23 = s.gpr .x3
  x24 : t.gpr .x24 = BitVec.ofNat 64 eb
  x25 : t.gpr .x25 = BitVec.ofNat 64 el
  x26 : t.gpr .x26 = BitVec.ofNat 64 lo

/-- At the call of `encode`: a zero byte at `EM`, `em` after it. -/
structure AtEnc (K : Nat) (s : State) (eb el lo : Nat) (t : State) : Prop extends AtPar K s eb el lo t where
  x0 : t.gpr .x0 = off (scr s) (oEm + lo)
  x1 : t.gpr .x1 = BitVec.ofNat 64 el
  x2 : t.gpr .x2 = stackArg s 8
  x3 : t.gpr .x3 = stackArg s 9
  x4 : t.gpr .x4 = stackArg s 10
  x5 : t.gpr .x5 = BitVec.ofNat 64 eb
  x6 : t.gpr .x6 = off (scr s) oEnc
  x7 : t.gpr .x7 = stackArg s 12 - BitVec.ofNat 64 (oEnc / 8)
  z : t.mem (off (scr s) oEm) = 0

/-- Bytes of our working space are writable. -/
theorem scr_wr {D K : Nat} {s t : State} (hp : PreS D K s) (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) {o n : Nat}
    (h : o + n ≤ 8 * 1024) : InRegions t.wr (off (scr s) o) n := by
  have := hp.hs; have := hp.ws
  rw [hwr]
  exact ⟨sR s, List.mem_cons_of_mem _ hp.hws, Offset.contains_base _ (by omega) (by omega)⟩

/-- A region of our working space is apart from the frame's slots. -/
theorem scr_frA {D K : Nat} {s : State} (hp : PreS D K s) {o n : Nat} (h : o + n ≤ 8 * 1024) :
    (frA s).Disjoint ⟨off (scr s) o, n⟩ ∧ (frB s).Disjoint ⟨off (scr s) o, n⟩ := by
  have := hp.hs
  have hs : Region.Sub ⟨off (scr s) o, n⟩ (sR s) := Offset.sub_base _ (by omega)
  exact ⟨(hp.ks.sub_left (frame_sub K s (d := 96) (n := 152) (by decide))).sub_right hs,
    (hp.ks.sub_left (frame_sub K s (d := 288) (n := 16) (by decide))).sub_right hs⟩

theorem encArgs_ok {D K : Nat} {s t : State} (hp : PreS D K s) {eb el lo : Nat} (ha : AtPar K s eb el lo t) :
    WP isa (.block encArgs) t (AtEnc K s eb el lo) := by
  have hk2 := hp.k2
  have hin : ∀ {u : State} {d : Nat}, u.sp = fb s → u.rd = s.rd → u.wr = ⟨fb s, frameBytes⟩ :: s.wr →
      d + 8 ≤ frameBytes → InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 d) 8 := fun hsp hrd hwr hd => by
    rw [hsp, hrd, hwr]
    exact InRegions_append_cons.mpr (.inl (Offset.contains_base _ hd (by unfold frameBytes at hd; omega)))
  unfold encArgs ld
  refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => ?_
  have x0₂ : u₂.gpr .x0 = off (scr s) oEm := by rw [o₂.get .x0, e₁, ha.x20]
  refine wp_strb (a := off (scr s) oEm) (by decide) (by rw [x0₂, BitVec.add_zero])
    (by rw [o₂.wr, o₁.wr]; exact scr_wr hp ha.wr (by unfold oEm; omega)) fun u₃ m₃ => ?_
  have O₂ : Only [.x0, .x9] t u₂ := (o₁.trans o₂).mono
  have hm₃ : u₃.mem = t.mem.writeW (off (scr s) oEm) (0 : Byte) := by rw [m₃.mem, O₂.mem, e₂]; rfl
  have f₃ : Frame [⟨off (scr s) oEm, 1⟩] t.mem u₃.mem := by
    rw [hm₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fr₃ : Fr s u₃.mem := ha.fr.frame f₃
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact (scr_frA hp (by unfold oEm; omega)).1)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact (scr_frA hp (by unfold oEm; omega)).2)
  have sp₃ : u₃.sp = fb s := by rw [m₃.sp, O₂.sp, ha.sp]
  have rd₃ : u₃.rd = s.rd := by rw [m₃.rd, O₂.rd, ha.rd]
  have wr₃ : u₃.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [m₃.wr, O₂.wr, ha.wr]
  refine wp_add fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ => ?_
  have O₅ : Only [.x0, .x1] u₃ u₅ := (o₄.trans o₅).mono
  refine wp_ldrSp (by decide) (hin (by rw [O₅.sp, sp₃]) (by rw [O₅.rd, rd₃]) (by rw [O₅.wr, wr₃]) (by decide))
    fun u₆ o₆ e₆ => ?_
  refine wp_ldrSp (by decide) (hin (by rw [o₆.sp, O₅.sp, sp₃]) (by rw [o₆.rd, O₅.rd, rd₃])
    (by rw [o₆.wr, O₅.wr, wr₃]) (by decide)) fun u₇ o₇ e₇ => ?_
  have O₇ : Only [.x0, .x1, .x2, .x3] u₃ u₇ := (O₅.trans (o₆.trans o₇)).mono
  refine wp_ldrSp (by decide) (hin (by rw [O₇.sp, sp₃]) (by rw [O₇.rd, rd₃]) (by rw [O₇.wr, wr₃]) (by decide))
    fun u₈ o₈ e₈ => wp_mov fun u₉ o₉ e₉ => wp_addImm (by unfold oEnc oY; omega) fun u₁₀ o₁₀ e₁₀ => ?_
  have O₁₀ : Only [.x0, .x1, .x2, .x3, .x4, .x5, .x6] u₃ u₁₀ := (O₇.trans (o₈.trans (o₉.trans o₁₀))).mono
  refine wp_ldrSp (by decide) (hin (by rw [O₁₀.sp, sp₃]) (by rw [O₁₀.rd, rd₃]) (by rw [O₁₀.wr, wr₃]) (by decide))
    fun u₁₁ o₁₁ e₁₁ => wp_subImm (by unfold oEnc oY; omega) fun u₁₂ o₁₂ e₁₂ => wp_nil ?_
  have O : Only [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] u₃ u₁₂ := (O₁₀.trans (o₁₁.trans o₁₂)).mono
  have mem : ∀ {u : State}, Only [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] u₃ u → u.mem = u₃.mem := fun o => o.mem
  have g : ∀ r ∈ [Reg.x20, .x23, .x24, .x25, .x26], u₁₂.gpr r = t.gpr r := fun r hr => by
    rw [O.gpr r (by revert r; decide), m₃.gpr, O₂.gpr r (by revert r; decide)]
  refine {
    sp := by rw [O.sp, sp₃]
    rd := by rw [O.rd, rd₃]
    wr := by rw [O.wr, wr₃]
    v := fun r hr => by rw [O.vcs r hr, m₃.vcs r hr, O₂.vcs r hr, ha.v r hr]
    mem := by
      rw [O.mem]
      exact ha.mem.trans (f₃.sub fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ⟨sR s, by simp, Offset.sub_base _ (by have := hp.hs; unfold oEm; omega)⟩)
    fr := by rw [O.mem]; exact fr₃
    x20 := by rw [g .x20 (by decide), ha.x20]
    x23 := by rw [g .x23 (by decide), ha.x23]
    x24 := by rw [g .x24 (by decide), ha.x24]
    x25 := by rw [g .x25 (by decide), ha.x25]
    x26 := by rw [g .x26 (by decide), ha.x26]
    x0 := by
      rw [o₁₂.get .x0, o₁₁.get .x0, o₁₀.get .x0, o₉.get .x0, o₈.get .x0, o₇.get .x0, o₆.get .x0, o₅.get .x0, e₄,
        m₃.gpr, x0₂, O₂.get .x26, ha.x26, off_add]
    x1 := by
      rw [o₁₂.get .x1, o₁₁.get .x1, o₁₀.get .x1, o₉.get .x1, o₈.get .x1, o₇.get .x1, o₆.get .x1, e₅, o₄.get .x25,
        m₃.gpr, O₂.get .x25, ha.x25]
    x2 := by
      rw [o₁₂.get .x2, o₁₁.get .x2, o₁₀.get .x2, o₉.get .x2, o₈.get .x2, o₇.get .x2, e₆, O₅.mem, O₅.sp, sp₃]
      exact fr₃.dig
    x3 := by
      rw [o₁₂.get .x3, o₁₁.get .x3, o₁₀.get .x3, o₉.get .x3, o₈.get .x3, e₇, o₆.mem, O₅.mem, o₆.sp, O₅.sp, sp₃]
      exact fr₃.salt
    x4 := by
      rw [o₁₂.get .x4, o₁₁.get .x4, o₁₀.get .x4, o₉.get .x4, e₈, O₇.mem, O₇.sp, sp₃]
      exact fr₃.sl
    x5 := by
      rw [o₁₂.get .x5, o₁₁.get .x5, o₁₀.get .x5, e₉, o₈.get .x24, O₇.get .x24, m₃.gpr, O₂.get .x24, ha.x24]
    x6 := by
      rw [o₁₂.get .x6, o₁₁.get .x6, e₁₀, o₉.get .x20, o₈.get .x20, O₇.get .x20, m₃.gpr, O₂.get .x20, ha.x20]
    x7 := by
      rw [e₁₂, e₁₁, O₁₀.mem, O₁₀.sp, sp₃]
      rw [fr₃.scr]
    z := by rw [O.mem, hm₃, writeW8_apply, ite_eq_left rfl] }

/-- The `cK ≤ K` bytes below the frame are in the stack the function uses. -/
theorem below_kR {K cK : Nat} (s : State) (hcK : cK ≤ K) :
    Region.Sub ⟨fb s - BitVec.ofNat 64 cK, cK⟩ (kR K s) := fun a h =>
  (Offset.sub_below (fb s) (a := cK) (b := K) (n := cK) (m := K) hcK (by omega_using [hcK]) a h) |>
    fun h' => by
      have e : fb s - BitVec.ofNat 64 K = kb K s := by rw [fb_eq K, BitVec.add_sub_cancel]
      rw [e] at h'
      exact Region.sub_prefix (by unfold stk; omega_using []) a h'

theorem oEnc_toNat {D K : Nat} {s : State} (hp : PreS D K s) :
    (stackArg s 12 - BitVec.ofNat 64 (oEnc / 8)).toNat = (stackArg s 12).toNat - oEnc / 8 := by
  have := hp.hs
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := (stackArg s 12).isLt
  unfold oEnc oY at *
  omega

/-- The call's arguments meet `encode`'s contract. -/
theorem encOk_of {D K : Nat} {s t : State} (hp : PreS D K s) {cK : Nat} (hcK : cK ≤ K) {eb el lo : Nat}
    (ha : AtEnc K s eb el lo t) (hlo : lo + el ≤ (s.gpr .x3).toNat) (hel : el = Spec.RsaPss.emLength eb)
    (hb1 : 1 ≤ eb) (hb2 : eb ≤ Proof.RsaPss.maxEmBits) : EncOk D cK t := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp
  have hkb := kb_toNat hp
  have hws : (scr s).toNat + (stackArg s 12).toNat * 8 ≤ 2 ^ 64 := hp.ws
  have hhs := hp.hs
  have hsc := oEnc_toNat hp
  have hK := below_kR (K := K) (cK := cK) s hcK
  have hSem : Region.Sub ⟨off (scr s) (oEm + lo), el⟩ (sR s) :=
    Offset.sub_base _ (by unfold oEm; omega)
  have hSsc : Region.Sub ⟨off (scr s) oEnc, (stackArg s 12 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩ (sR s) :=
    Offset.sub_base _ (by rw [hsc]; unfold oEnc oY at *; omega)
  have hwem : (off (scr s) (oEm + lo)).toNat + el ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEm at *; omega
  have hwsc : (off (scr s) oEnc).toNat + (stackArg s 12 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8 ≤ 2 ^ 64 := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; rw [hsc]; unfold oEnc oY at *; omega
  have he : (BitVec.ofNat 64 el).toNat = el := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show el < 2 ^ 64 by omega)]
  have hb : (BitVec.ofNat 64 eb).toNat = eb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show eb < 2 ^ 64 by unfold Proof.RsaPss.maxEmBits at hb2; omega)]
  have hcov : Covers [(⟨stackArg s 8, D⟩ : Region), ⟨stackArg s 9, (stackArg s 10).toNat⟩] (t.rd ++ t.wr) := by
    rw [ha.rd]
    exact Covers.left (Covers.trans (Covers.of_mem fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp) hp.hrd)
  have hcw : Covers [(⟨off (scr s) (oEm + lo), el⟩ : Region),
      ⟨off (scr s) oEnc, (stackArg s 12 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩] t.wr := by
    rw [ha.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨sR s, List.mem_cons_of_mem _ hp.hws, oEm + lo, rfl,
        by show oEm + lo + el ≤ (stackArg s 12).toNat * 8; unfold oEm; omega⟩
    · exact ⟨sR s, List.mem_cons_of_mem _ hp.hws, oEnc, rfl,
        by show oEnc + (stackArg s 12 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8 ≤ (stackArg s 12).toNat * 8
           rw [hsc]; unfold oEnc oY at *; omega⟩
  exact {
    sp1 := by rw [ha.sp]; unfold stk at *; omega
    hrd := by simp only [VG.Proof.RsaPss.AArch64.encRd, ha.x2, ha.x3, ha.x4]; exact hcov
    hwr := by simp only [encWr, ha.x0, ha.x1, ha.x6, ha.x7, he]; exact hcw
    ed := by rw [ha.x0, ha.x1, ha.x2, he]; exact (hp.dgs.symm.sub_left hSem)
    esa := by rw [ha.x0, ha.x1, ha.x3, ha.x4, he]; exact (hp.sls.symm.sub_left hSem)
    es := by
      rw [ha.x0, ha.x1, ha.x6, ha.x7, he]
      exact Offset.disjoint _ (Or.inl (by unfold oEm oEnc oY; omega)) (by unfold oEm; omega)
        (by rw [hsc]; unfold oEnc oY at *; omega)
    ds := by rw [ha.x2, ha.x6, ha.x7]; exact hp.dgs.sub_right hSsc
    sas := by rw [ha.x3, ha.x4, ha.x6, ha.x7]; exact hp.sls.sub_right hSsc
    ke := by rw [stkR, ha.sp, ha.x0, ha.x1, he]; exact (hp.ks.sub_left hK).sub_right hSem
    kd := by rw [stkR, ha.sp, ha.x2]; exact hp.kdg.sub_left hK
    ksa := by rw [stkR, ha.sp, ha.x3, ha.x4]; exact hp.ksl.sub_left hK
    ks := by rw [stkR, ha.sp, ha.x6, ha.x7]; exact (hp.ks.sub_left hK).sub_right hSsc
    we := by rw [ha.x0, ha.x1, he]; exact hwem
    wd := by rw [ha.x2]; exact hp.wdg
    wsa := by rw [ha.x3, ha.x4]; exact hp.wsl
    ws := by rw [ha.x6, ha.x7]; exact hwsc
    b1 := by rw [ha.x5, hb]; exact hb1
    b2 := by rw [ha.x5, hb]; exact hb2
    hel := by rw [ha.x1, ha.x5, he, hb]; exact hel
    hs := by rw [ha.x7, hsc]; unfold Proof.RsaPss.encodingScratchWords oEnc oY; omega }

variable (G : Spec.Mgf1.Hash) in
/-- After the call of `encode`: its result, and `EM` holding `lo` zero bytes
and the encoding if it fits. -/
structure AfterEnc (K : Nat) (s : State) (eb el lo : Nat) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  v : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  fr : Fr s t.mem
  mem : Frame (wrS K s) s.mem t.mem
  x20 : t.gpr .x20 = scr s
  x23 : t.gpr .x23 = s.gpr .x3
  z : lo = 1 → t.mem (off (scr s) oEm) = 0
  res : match Spec.RsaPss.encode G G (Spec.Rsa.bytesAt s.mem (stackArg s 8) G.len)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat) eb with
    | some e => (t.gpr .x0).setWidth 32 = (1 : BitVec 32) ∧
        Spec.Rsa.bytesAt t.mem (off (scr s) (oEm + lo)) el = e
    | none => (t.gpr .x0).setWidth 32 = (0 : BitVec 32)

theorem encCall_ok {G : Spec.Mgf1.Hash} (c : EncImpl G) {K : Nat} {s t : State} (hp : PreS G.len K s)
    (hcK : c.stack ≤ K) {eb el lo : Nat} (ha : AtEnc K s eb el lo t) (hlo : lo + el ≤ (s.gpr .x3).toNat)
    (hel : el = Spec.RsaPss.emLength eb) (hb1 : 1 ≤ eb) (hb2 : eb ≤ Proof.RsaPss.maxEmBits) :
    WP isa (.call c.name c.code) t (AfterEnc G K s eb el lo) := by
  have hk2 := hp.k2
  have hhs := hp.hs
  have hws : (scr s).toNat + (stackArg s 12).toNat * 8 ≤ 2 ^ 64 := hp.ws
  have hcl := c.le
  have hd := c.depth
  have hsc := oEnc_toNat hp
  have he : (BitVec.ofNat 64 el).toNat = el := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show el < 2 ^ 64 by omega)]
  have hb : (BitVec.ofNat 64 eb).toNat = eb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show eb < 2 ^ 64 by unfold Proof.RsaPss.maxEmBits at hb2; omega)]
  refine encCall c (encOk_of hp hcK ha hlo hel hb1 hb2) fun s' hrd' hwr' hsp' hf hpres hvs hpost => ?_
  simp only [encWr] at hf
  rw [ha.x0, ha.x1, ha.x6, ha.x7, ha.sp, he] at hf
  have hl : ∀ {p : Addr} {len : Nat}, p.toNat + len ≤ 2 ^ 64 → len ≤ 2 ^ 64 := fun h => by omega
  rw [ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, he, hb, bytes_wrS ha.mem hp.kdg hp.dgs (hl hp.wdg),
    bytes_wrS ha.mem hp.ksl hp.sls (hl hp.wsl)] at hpost
  have hSem : Region.Sub ⟨off (scr s) (oEm + lo), el⟩ (sR s) := Offset.sub_base _ (by unfold oEm; omega)
  have hSsc : Region.Sub ⟨off (scr s) oEnc, (stackArg s 12 - BitVec.ofNat 64 (oEnc / 8)).toNat * 8⟩ (sR s) :=
    Offset.sub_base _ (by rw [hsc]; unfold oEnc oY at *; omega)
  have hB : Region.Sub (below (fb s) (16 * c.code.aarch64Depth)) (below (fb s) K) :=
    Offset.sub_below _ (by omega) (by omega)
  exact {
    sp := hsp'.trans ha.sp
    rd := hrd'.trans ha.rd
    wr := hwr'.trans ha.wr
    v := fun r hr => (hvs r hr).trans (ha.v r hr)
    fr := ha.fr.below (n := 16 * c.code.aarch64Depth) (by omega) hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (scr_frA hp (by unfold oEm; omega)).1
        · exact (hp.ks.sub_left (frame_sub K s (d := 96) (n := 152) (by decide))).sub_right hSsc)
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact (scr_frA hp (by unfold oEm; omega)).2
        · exact (hp.ks.sub_left (frame_sub K s (d := 288) (n := 16) (by decide))).sub_right hSsc)
    mem := ha.mem.trans (hf.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sR s, by simp, hSem⟩
      · exact ⟨sR s, by simp, hSsc⟩
      · exact ⟨below (fb s) K, by simp, hB⟩)
    x20 := (hpres .x20 (by decide) (by decide)).trans ha.x20
    x23 := (hpres .x23 (by decide) (by decide)).trans ha.x23
    z := fun h1 => by
      subst h1
      rw [hf _ fun r hr hc => ?_]
      · exact ha.z
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      have hc0 : (⟨off (scr s) oEm, 1⟩ : Region).Contains (off (scr s) oEm) 1 := Region.contains_self _ _
      rcases hr with rfl | rfl | rfl
      · exact Offset.disjoint _ (Or.inl (by omega)) (by unfold oEm; omega) (by unfold oEm; omega) _ hc0 hc
      · exact Offset.disjoint _ (Or.inl (by unfold oEm oEnc oY; omega)) (by unfold oEm; omega)
          (by rw [hsc]; unfold oEnc oY at *; omega) _ hc0 hc
      · exact (hp.ks.sub_left (below_kR (cK := 16 * c.code.aarch64Depth) s (by omega))).sub_right
          (Offset.sub_base _ (by unfold oEm; omega) : Region.Sub ⟨off (scr s) oEm, 1⟩ (sR s)) _ hc hc0
    res := hpost }

end VG.Proof.RsaPss.AArch64.Sgn
