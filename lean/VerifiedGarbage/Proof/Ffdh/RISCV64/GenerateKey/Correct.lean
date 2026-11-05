module

-- separate module: built alongside CT

public import VerifiedGarbage.Proof.Ffdh.RISCV64.GenerateKey.Body
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Correct
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_ffdh_generate_key` on RISC-V: correctness

`generateKey` runs the front (`gkFront_ok`), loads and checks p
(`loadP_X`), and for a valid p cuts x from `rand` (`scalar_ok`), runs
`vg_ffdh_derive_public`'s body (`Derive.body_ok`) and zeros x but for the
status 1 (`gkBody_ok`); then it restores the callee-saved registers
(`gk_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.GenerateKey

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Derive VG.Impl.Ffdh.RISCV64.GenerateKey
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.RISCV64.Derive (AR bnd DPost body_ok)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pub (savW savR)

/-- The status of x, from its value. -/
def stat (x : XD) (m : Mem) (sv : Nat) : Nat :=
  if ¬ (0 < sv ∧ sv < bnd m x.D x.k x.L x.p) then 2 else
    if 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt m x.Y x.k) ^ sv % x.p ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt m x.Y x.k) ^ sv % x.p < x.p - 1 then 1 else 3

/-- What the branches leave, from `s` after p's check. -/
def GPost (x : XD) (R : Addr) (s t : State) : Prop :=
  (Spec.Rsa.modulusValid x.p x.k = true →
    let sv := Spec.Rsa.os2ip (gkOct s.mem x.D R x.k x.L)
    let z := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.Y x.k) ^ sv % x.p
    t.gpr .a0 = BitVec.ofNat 64 (stat x s.mem sv) ∧
      Spec.Rsa.bytesAt t.mem x.O x.k = (if stat x s.mem sv = 1 then Spec.Rsa.i2osp z x.k else List.replicate x.k 0) ∧
      Spec.Rsa.bytesAt t.mem x.X x.k = (if stat x s.mem sv = 1 then gkOct s.mem x.D R x.k x.L
        else List.replicate x.k 0)) ∧
  t.gpr .s6 = x.S ∧ ∀ d, d + 8 ≤ 256 → word t.mem x.S d = word s.mem x.S d

theorem stat_lt (x : XD) (m : Mem) (sv : Nat) : stat x m sv < 4 := by
  unfold stat; split <;> [decide; split <;> decide]

/-- For a valid p: the scalar, `vg_ffdh_derive_public`'s body, and the mask of
x. -/
theorem gkBody_ok {x : XD} {R : Addr} {s : State} (h : X4 x s) (hz : s.gpr .s0 = 0) (ha : AR x s) (hx : XR x R s)
    (h1 : s.gpr .t1 = R) (hYD : x.Y = off x.D x.k) : WP isa gkBody s (GPost x R s) := by
  have hv := h.2.2.mp hz
  have hb := h.1
  have hc := hb.ctx
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  have hk := hc.k64
  have hk' := hc.k1024
  unfold slot hdrBytes at hZ
  unfold gkBody
  refine WP.seq (WP.mono (WP.rdwr (scalar_ok hb ha hx h1)) fun s₁ ⟨⟨⟨xb, xo, z0⟩, k1⟩, r1, w1, _⟩ => ?_)
  have hc1 := Ctx.ofX hc hx r1 w1 xo
  have os1 := outX_scr xo hx.sepSX
  have hb1 : Base x s₁ := ⟨hc1, (k1.gpr (by decide)).trans hb.s6, (k1.gpr (by decide)).trans hb.a7,
    (k1.gpr (by decide)).trans hb.s5, (k1.gpr (by decide)).trans hb.t0, (k1.gpr (by decide)).trans hb.s7,
    (k1.gpr (by decide)).trans hb.s8, (k1.gpr (by decide)).trans hb.s10, (k1.gpr (by decide)).trans hb.s11⟩
  have e0 : slot x.w 0 = 256 := by simp [slot, hdrBytes]
  have h41 : X4 x s₁ := ⟨hb1, by rw [Outside.wordsVal os1 (Or.inl (by omega_arith)) (by omega_arith)]; exact h.2.1,
    fun _ => hv, fun _ => z0⟩
  have hx1 := hx.keep r1 w1
  have hxk : x.xl = x.k := hx.xl
  refine WP.seq (WP.mono (WP.rdwr (body_ok h41 z0 (ha.keep k1))) fun s₂ ⟨⟨dp, d6, m, am, om⟩, r2, w2, _⟩ => ?_)
  obtain ⟨db, da⟩ := dp hv
  -- The header and x, after the body.
  have hw2 : ∀ d, d + 8 ≤ 256 → word s₂.mem x.S d = word s₁.mem x.S d := fun d hd => by
    refine (Pub.Outside.word_apart om hx.sepSO (by omega_arith) (by omega_arith) hn).trans ?_
    show Mont.word m _ _ = _
    exact Outside.word am (Or.inl hd) (by omega_arith)
  have hX2 : Spec.Rsa.bytesAt s₂.mem x.X x.k = Spec.Rsa.bytesAt s₁.mem x.X x.k := by
    rw [Pub.bytes_apart (Z := x.k) om (by omega_arith) hx.sepXO]
    exact Pub.bytes_apart (Z := x.Z) am (by omega_arith) (by rw [← hxk]; exact hc1.sepX)
  have hw1 : ∀ d, d + 8 ≤ 256 → word s₁.mem x.S d = word s.mem x.S d := fun d hd =>
    Pub.Outside.word_apart xo hx.sepSX (by omega_arith) (by omega_arith) hn
  simp only [hxk] at db da
  rw [xb] at db da
  rw [xb] at hX2
  generalize hsv : Spec.Rsa.os2ip (gkOct s.mem x.D R x.k x.L) = sv at db da
  have hY1 : Spec.Rsa.bytesAt s₁.mem x.Y x.k = Spec.Rsa.bytesAt s.mem x.Y x.k :=
    Pub.bytes_apart (Z := x.k) xo (by omega_arith) fun i hi y hy => by
      have hL := hc.hL
      have h' := hx.sepDX (x.k + i) (by omega_arith) y hy
      rw [← Derive.off_off, ← hYD] at h'; exact h'
  have hB1 : bnd s₁.mem x.D x.k x.L x.p = bnd s.mem x.D x.k x.L x.p := by
    unfold bnd
    by_cases hq : x.L = 3 * x.k
    · rw [ite_eq_left hq, ite_eq_left hq, Pub.bytes_apart (Z := x.k) xo (by omega_arith) fun i hi y hy => by
        have h' := hx.sepDX (2 * x.k + i) (by omega_arith) y hy
        rw [← Derive.off_off] at h'; exact h']
    · rw [ite_eq_right hq, ite_eq_right hq]
  rw [hY1, hB1] at db da
  have hst : (if ¬(0 < sv ∧ sv < bnd s.mem x.D x.k x.L x.p) then 2 else
      if 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.Y x.k) ^ sv % x.p ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.Y x.k) ^ sv % x.p < x.p - 1 then 1 else 3) = stat x s.mem sv := rfl
  rw [hst] at da
  -- The mask of x.
  unfold maskX
  have hs2 := hc1.scr.congr w2
  refine WP.seq (WP.mono (maskPre_ok (X := x.X) (k := x.k) hs2 (by omega_arith) d6 da (stat_lt _ _ _)
    (by rw [hw2 8 (by decide)]; exact hc1.hX)
    (by rw [hw2 16 (by decide), hc1.hXL, hxk])) fun s₃ ⟨⟨m4, ma1, mt5, mm⟩, k3⟩ => ?_)
  refine WP.mono (masked_ok (c := decide (stat x s.mem sv = 1)) (by omega_arith) (by omega_arith) hx.nwX
    (by rw [k3.2.2, w2, w1]; exact hx.wX) ma1 (by rw [m4]; simp) mt5) fun t ⟨⟨tb, to⟩, kt⟩ => ⟨fun _ => ?_, ?_, ?_⟩
  · dsimp only
    rw [hsv]
    refine ⟨by rw [kt.gpr (by decide), k3.gpr (by decide), da], ?_, ?_⟩
    · rw [Pub.bytes_apart (Z := x.k) to (by omega_arith) hx.sepOX, mm, db]
      unfold stat
      by_cases h1 : 0 < sv ∧ sv < bnd s.mem x.D x.k x.L x.p
      · by_cases h2 : 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.Y x.k) ^ sv % x.p ∧
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem x.Y x.k) ^ sv % x.p < x.p - 1
        · simp only [h1, h2, and_self, not_true_eq_false, ↓reduceIte]
        · simp [h1, h2]
      · simp [h1]
    · rw [tb, mm, hX2]
      by_cases h1 : stat x s.mem sv = 1 <;> simp [h1]
  · exact (kt.gpr (by decide)).trans ((k3.gpr (by decide)).trans d6)
  · intro d hd
    refine (Pub.Outside.word_apart to hx.sepSX (by omega_arith) (by omega_arith) hn).trans ?_
    show Mont.word s₃.mem _ _ = _
    rw [mm, hw2 d hd, hw1 d hd]

/-- After p's check: the body for a valid p, else the status 0. -/
theorem branch_ok {x : XD} {R : Addr} {s : State} (h : X4 x s) (ha : AR x s) (hx : XR x R s)
    (h1 : s.gpr .t1 = R) (hYD : x.Y = off x.D x.k) :
    WP isa (.ite (.zero .s0) gkBody (.block [.li .a0 0])) s (GPost x R s) := by
  refine WP.ite (s.gpr .s0 == 0) (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · exact gkBody_ok h (by simpa using hb) ha hx h1 hYD
  · have hz : s.gpr .s0 ≠ 0 := by simpa using hb
    refine WP.mono (WP.keep [.a0] (Q := fun t => t.mem = s.mem) (by brun [exec_li]) (by rfl) (by rfl))
      fun t ⟨tm, kt⟩ => ⟨fun hv => absurd (h.2.2.mpr hv) hz, (kt.gpr (by decide)).trans h.1.s6,
        fun d _ => by rw [tm]⟩

theorem ret_status (n : Nat) (hn : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- Every register but `ra`. -/
def gkNotRa : List Reg :=
  [.t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10,
    .s11, .t3, .t4, .t5, .t6]

theorem pres_saved : ∀ r ∈ preserved, ∃ i < 12, r = PublicChecked.saved i := by decide

theorem gk_correct (s : State) (h : gkContract.pre s) :
    ∃ tr t, Exec isa generateKey s tr t ∧ abiPreserved s t ∧ gkContract.post s t := by
  show WP isa generateKey s fun t => abiPreserved s t ∧ gkContract.post s t
  suffices main : WP isa generateKey s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ gkContract.post s t from
    WP.mono (WP.rdwr (WP.keep gkNotRa main (by rfl))) fun t ⟨⟨⟨hp, hpost⟩, kra⟩, _, _, hsp⟩ =>
      ⟨⟨hp, hsp, kra.gpr (by decide)⟩, hpost⟩
  have hpre := h
  obtain ⟨hrd, hwr, dXY, dXD, dXR, dXS, dXA, dYD, dYR, dYS, dYA, dDS, dRS, dSA, nwX, nwY, nwD, nwR, nwS,
    ⟨hk, hk'⟩, hL, hxl, hyl, hrl, hsl, alS, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hLk : 2 * (s.gpr .a6).toNat ≤ (s.gpr .a5).toNat ∧ (s.gpr .a5).toNat ≤ 3 * (s.gpr .a6).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  unfold generateKey
  refine WP.seq (WP.mono (WP.rdwr (gkFront_ok hpre)) fun s₃ ⟨⟨hb3, ha3, ht1, hsv, k3, o3⟩, r3, w3, _⟩ => ?_)
  have hx3 : XR (gxOf s) (s.gpr .a7) s₃ := xr_of_pre hpre r3 w3
  refine WP.seq (WP.mono (WP.rdwr (WP.keep [.a0, .s0, .t3, .t4, .t5] (loadP_X hb3) (by rfl)))
    fun s₄ ⟨⟨⟨h4, a4⟩, k4⟩, r4, w4, _⟩ => ?_)
  refine WP.seq (WP.mono (WP.rdwr (branch_ok h4 (ha3.keep k4) (hx3.keep r4 w4) ((k4.gpr (by decide)).trans ht1) rfl))
    fun t₅ ⟨⟨tpost, t6, tw⟩, r5, w5, _⟩ => ?_)
  have hc := hb3.ctx
  have hnS := hc.scr.nowrap
  change Outside (stackArg s 1) 256 ((stackArg s 2).toNat * 8 - 256) s₃.mem s₄.mem at a4
  change (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 at hnS
  -- The saved registers' words.
  have hin : ∀ i < 12, InRegions t₅.wr (off (savW (stackArg s 1)) (8 * i)) 8 := fun i hi => by
    rw [w5, w4, w3, hwr]
    show InRegions _ (stackArg s 1 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hsav : ∀ i < 12, t₅.mem.readW (off (savW (stackArg s 1)) (8 * i)) 64 = s.gpr (PublicChecked.saved i) :=
      fun i hi => by
    have e : off (savW (stackArg s 1)) (8 * i) = off (stackArg s 1) (128 + 8 * i) := by
      rw [off, off, Offset.add_add]
    rw [← hsv i hi, e]
    show word t₅.mem (stackArg s 1) (128 + 8 * i) = word s₃.mem (stackArg s 1) (128 + 8 * i)
    exact (tw (128 + 8 * i) (by omega_arith)).trans (Outside.word a4 (Or.inl (by omega_arith)) (by omega_arith))
  refine WP.mono (Pub.restore_ok t₅ (S := stackArg s 1) (v := fun i => s.gpr (PublicChecked.saved i)) t6 hin
    (fun i hi => Pub.sav_al alS (by omega_arith) hi) hsav) fun u ⟨urs, uot, um, _, _, _⟩ => ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pres_saved r hr
    exact urs i hi
  · intro hdv
    -- The memory apart from the working space, before the branch.
    have hOZ : Outside (stackArg s 1) 0 ((stackArg s 2).toNat * 8) s.mem s₄.mem :=
      (o3.mono (Nat.le_refl _) (by omega_arith)).trans (a4.mono (by omega_arith) (by omega_arith))
    have hsep : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off Q i ≠ y) →
        Spec.Rsa.bytesAt s₄.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq =>
      Pub.bytes_apart (o := 0) hOZ (by omega_arith) hq
    have hsepD : ∀ j n, j + n ≤ (s.gpr .a5).toNat →
        Spec.Rsa.bytesAt s₄.mem (off (s.gpr .a4) j) n = Spec.Rsa.bytesAt s.mem (off (s.gpr .a4) j) n :=
      fun j n hjn => hsep _ _ fun i hi => by
        have h' := hc.sepD (j + i) (by change _ < (s.gpr .a5).toNat; omega_arith); rw [← Derive.off_off] at h'; exact h'
    have bY : Spec.Rsa.bytesAt s₄.mem (gxOf s).Y (gxOf s).k =
        Spec.Rsa.bytesAt s.mem (off (s.gpr .a4) (s.gpr .a6).toNat) (s.gpr .a6).toNat :=
      hsepD (s.gpr .a6).toNat (s.gpr .a6).toNat (by omega_arith)
    have bD : Spec.Rsa.bytesAt s₄.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat :=
      hsep _ _ hc.sepD
    have bB : bnd s₄.mem (gxOf s).D (gxOf s).k (gxOf s).L (gxOf s).p =
        bnd s.mem (s.gpr .a4) (s.gpr .a6).toNat (s.gpr .a5).toNat (gxOf s).p := by
      unfold bnd
      by_cases hq : (gxOf s).L = 3 * (gxOf s).k
      · have hq' : (s.gpr .a5).toNat = 3 * (s.gpr .a6).toNat := hq
        rw [ite_eq_left hq, ite_eq_left hq']
        exact congrArg Spec.Rsa.os2ip (hsepD (2 * (s.gpr .a6).toNat) (s.gpr .a6).toNat (by omega_arith))
      · rw [ite_eq_right hq, ite_eq_right (show ¬ (s.gpr .a5).toNat = 3 * (s.gpr .a6).toNat from hq)]
    have bG : gkOct s₄.mem (gxOf s).D (s.gpr .a7) (gxOf s).k (gxOf s).L =
        gkOct s.mem (s.gpr .a4) (s.gpr .a7) (s.gpr .a6).toNat (s.gpr .a5).toNat := by
      refine gkOct_congr (hsep _ _ fun i hi => Pub.ne_of_disjoint dRS (Nat.le_of_lt (stackArg s 0).isLt) i
        (by rw [hrl]; exact hi)) ?_
      unfold bptr
      by_cases hq : (gxOf s).L = 3 * (gxOf s).k
      · have hq' : (s.gpr .a5).toNat = 3 * (s.gpr .a6).toNat := hq
        rw [ite_eq_left hq]
        exact hsepD (2 * (s.gpr .a6).toNat) (s.gpr .a6).toNat (by omega_arith)
      · have hq' : ¬ (s.gpr .a5).toNat = 3 * (s.gpr .a6).toNat := hq
        rw [ite_eq_right hq]
        have := hsepD 0 (s.gpr .a6).toNat (by omega_arith)
        simp only [off, add_ofNat_zero] at this
        exact this
    have hmod := Proof.Ffdh.domainValid_mod hdv
    have hpe : (Spec.Ffdh.domainOf (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)).p =
        (gxOf s).p := by
      rw [Proof.Ffdh.domainOf_p _ _ hLk.1]
      show _ = Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat).take (s.gpr .a6).toNat)
      rw [Proof.Ffdh.take_bytesAt _ _ (by omega_arith)]
    have hpD : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a6).toNat) = (gxOf s).p := by
      rw [← hpe, Proof.Ffdh.domainOf_p _ _ hLk.1]
    rw [hpe] at hmod
    have hf := VG.Proof.Bignum.valid_facts hmod hk
    obtain ⟨ta, tO, tX⟩ := tpost hmod
    have hL' : (s.gpr .a5).toNat = 2 * (s.gpr .a6).toNat ∨ (s.gpr .a5).toNat = 3 * (s.gpr .a6).toNat := hL
    have hsc := gkOct_eq s.mem (s.gpr .a4) (s.gpr .a7) (by omega_arith) hL' (fun _ => by rw [hpD]; exact ⟨hf.1, hf.2.1⟩)
    have hst : stat (gxOf s) s₄.mem (Spec.Rsa.os2ip (gkOct s₄.mem (gxOf s).D (s.gpr .a7) (gxOf s).k (gxOf s).L)) =
        Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat))
          (Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf (s.gpr .a6).toNat
            (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)) (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)) := by
      rw [Derive.keyStatus_dom (by omega_arith) hL' hdv, hrl, ← hsc, bG, hpD]
      unfold stat
      rw [bY, bB]
    have hz : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₄.mem (gxOf s).Y (gxOf s).k) ^
        Spec.Rsa.os2ip (gkOct s₄.mem (gxOf s).D (s.gpr .a7) (gxOf s).k (gxOf s).L) % (gxOf s).p =
        Spec.Rsa.powMod (Spec.Ffdh.domainOf (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)).g
          (Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf (s.gpr .a6).toNat
            (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)) (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat))
          (Spec.Ffdh.domainOf (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)).p := by
      rw [VG.Proof.Bignum.powMod_eq, Proof.Ffdh.domainOf_g _ _ hLk.1, hpe, bY, bG, hsc, hrl]
    rw [hst] at ta tO tX
    rw [hz] at tO
    rw [bG] at tX
    show _ ∧ _
    rw [um, uot .a0 (by decide), ta, ret_status _ (by
      have := stat_lt (gxOf s) s₄.mem (Spec.Rsa.os2ip (gkOct s₄.mem (gxOf s).D (s.gpr .a7) (gxOf s).k (gxOf s).L))
      rw [hst] at this; omega_arith)]
    refine ⟨rfl, ?_⟩
    rw [show (gxOf s).O = s.gpr .a2 from rfl, show (gxOf s).k = (s.gpr .a6).toNat from rfl] at tO
    rw [show (gxOf s).X = s.gpr .a0 from rfl, show (gxOf s).k = (s.gpr .a6).toNat from rfl] at tX
    rw [tO, tX]
    split
    · refine ⟨?_, rfl⟩
      rw [hrl, ← hsc]
      have := VG.Proof.Rsa.i2osp_os2ip (gkOct s.mem (s.gpr .a4) (s.gpr .a7) (s.gpr .a6).toNat (s.gpr .a5).toNat)
      rw [gkOct_length _ _ _ (by omega_arith)] at this
      exact this.symm
    · exact ⟨rfl, rfl⟩

end VG.Proof.Ffdh.RISCV64.GenerateKey
