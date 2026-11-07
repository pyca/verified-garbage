module

public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignBody
public import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedSignFn
public import VerifiedGarbage.Impl.Dsa.RISCV64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
import VerifiedGarbage.Proof.Dsa.RISCV64.SignR
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA private-key validation on RISC-V: the contract on the registers, and the function

`vpkContract`: `vg_dsa_validate_private_key(key = a0, key_len = a1,
p_len = a2, q_len = a3, scratch = a4, scratch_len = a5)`, `vkContract`'s
registers with the packed private key p||q||g||y||x. `validatePriv_correct`:
after `Params.entry`, `checkSignKey` checks the domain and `1 < y < p`; then
`keyPair` puts the mask of `g^x mod p = y` in `hMask` and `xRange` returns
its low bit and that of `0 < x < q` (`vrest_ok`). With the domain's
`g^q mod p = 1`, `g^x mod p = y` makes `y^q mod p = 1`, so these are the
specification's checks (`privChecks_iff`, `validatePrivate_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- `vg_dsa_validate_private_key`, on the registers. -/
def vpkContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let scr : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat * 8⟩
    s.rd = [key] ∧ s.wr = [scr] ∧ key.Disjoint scr ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a5).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .a2).toNat (s.gpr .a3).toNat ∧
      (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat + 2 * (s.gpr .a3).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .a2).toNat ≤ (s.gpr .a5).toNat ∧
      (s.gpr .a4).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat = if Spec.Dsa.validatePrivateKeyBytes (s.gpr .a2).toNat (s.gpr .a3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) then 1 else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .a2).toNat (s₁.gpr .a3).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat) ++
        [if Spec.Dsa.validatePrivateKeyBytes (s₁.gpr .a2).toNat (s₁.gpr .a3).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat) then 1 else 0] =
      Spec.Dsa.publicBytesLeak (s₂.gpr .a2).toNat (s₂.gpr .a3).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat) ++
        [if Spec.Dsa.validatePrivateKeyBytes (s₂.gpr .a2).toNat (s₂.gpr .a3).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat) then 1 else 0]

/-- With the domain's checks and `1 < y < p`, validation is `g^x mod p = y`
and `0 < x < q`. -/
theorem privChecks_iff {p q g y x : Nat}
    (hP : VG.Proof.Dsa.shapeValid p q ∧ (1 < g ∧ g < p) ∧ (p - 1) % q = 0 ∧ g ^ q % p = 1)
    (hy : 1 < y ∧ y < p) :
    (VG.Proof.Dsa.shapeValid p q ∧ VG.Proof.Dsa.publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ g ^ x % p = y) ↔
      (g ^ x % p = y ∧ (0 < x ∧ x < q)) :=
  ⟨fun ⟨_, _, hx, hg⟩ => ⟨hg, hx⟩, fun ⟨hg, hx⟩ =>
    ⟨hP.1, ⟨⟨hP.2.1, hy⟩, hP.2.2.1, hP.2.2.2, pow_order_of_gen (by omega) hP.2.2.2 hg⟩, hx, hg⟩⟩

/-- The registers `xRange` writes. -/
def xRangePRegs : List Reg :=
  enterRegs ++ [.s0, .t3, .t5] ++ ptrRegs ++ loadRegs ++ [.a4] ++ inRangeRegs ++ [.a0]

/-- `xRange`: in the Q space, `a0 :=` the low bit of the mask in `hMask` and
of `0 < x < q`. Memory changes only past the header. -/
theorem xRangeP_ok {s : State} {L : Lay} {key sig : Addr} {b : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hm : word s.mem L.S hMask = mask b) :
    WP isa PrevalidatedSign.xRange s fun t =>
      (t.gpr .a0 = BitVec.ofNat 64 (if b && decide (0 < xOf s.mem L key ∧ xOf s.mem L key < arrQ s.mem L 0)
          then 1 else 0) ∧ QS t L key sig ∧ Body L s.mem t.mem) ∧ Keep xRangePRegs s t := by
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have hZ := hL.z256
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  have e0 := e 0; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7
  have e8 := e 8; have e28 := e 28
  unfold PrevalidatedSign.xRange
  refine WP.seq (WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_)
  have Q1 : QS s₁ L key sig := ⟨q1, hs.congr k1.2.2, hr.keepM k1 m1⟩
  refine WP.seq (WP.mono (zeroArr_ok Q1.inq.env (j := 7) (by decide)) fun s₂ ⟨⟨z7, o2⟩, k2⟩ => ?_)
  have Q2 := Q1.step k2 (Body.ofQ hL o2 (by omega))
  refine WP.seq (WP.mono (ptrX_ok Q2.scr hL Q2.regs) fun s₃ ⟨⟨c7, c8, m3⟩, k3⟩ => ?_)
  have Q3 := Q2.stepM k3 m3
  have k13 := (k1.trans k2).trans k3
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q3 hL (by decide)
      ((hk.keep k13.2.1 k13.2.2).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega)) c7 c8
      (by omega) (by omega)) fun s₄ ⟨⟨Q4, v5, top5, o4⟩, k4⟩ => ?_)
  have b2 : Body L s.mem s₂.mem := by rw [← m1]; exact Body.ofQ hL o2 (by omega)
  have b4 : Body L s.mem s₄.mem := b2.trans (by rw [← m3]; exact Body.ofQ hL o4 (by omega))
  obtain ⟨hld, hal⟩ := ScrL.hdr Q4.scr hL (d := 0) (by decide) (by decide)
  have hw4 : word s₄.mem L.S hMask = mask b := by rw [b4.word (by decide)]; exact hm
  refine WP.seq (WP.mono (WP.keep [.a4] (Q := fun u => u.gpr .a4 = mask b ∧ u.mem = s₄.mem)
    (by brun [hMask, Q4.regs.s6, hld, hal]; exact hw4) (by decide) (by rfl)) fun s₅ ⟨⟨a4, m5⟩, k5⟩ => ?_)
  have Q5 := Q4.stepM k5 m5
  have z7' : wordsVal s₅.mem L.Q (slot L.wq 7) L.wq = 0 := by
    rw [m5, show wordsVal s₄.mem L.Q (slot L.wq 7) L.wq = arrQ s₄.mem L 7 from rfl,
      qa_eq hL o4 (by decide) (by omega), m3]
    exact z7
  have top5' : word s₅.mem L.Q (slot L.wq 5 + 8 * L.wq) = 0 := by rw [m5]; exact top5
  refine WP.seq (WP.mono (inRange_ok Q5.inq.env (a := 5) (b := b) (by decide) (by decide) (by decide) top5' z7' a4)
    fun s₆ ⟨⟨c4, o6⟩, k6⟩ => ?_)
  have Q6 := Q5.step k6 (Body.ofQ hL o6 (by omega))
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 (if (b && decide
      (0 < wordsVal s₅.mem L.Q (slot L.wq 5) L.wq ∧
        wordsVal s₅.mem L.Q (slot L.wq 5) L.wq < wordsVal s₅.mem L.Q (slot L.wq 0) L.wq)) then 1 else 0) ∧
      u.mem = s₆.mem)
    (by brun [c4, mask_low]) (by decide) (by rfl)) fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  have A5 : wordsVal s₅.mem L.Q (slot L.wq 5) L.wq = xOf s.mem L key := by
    rw [m5]
    refine v5.trans ?_
    rw [xOf, m3, (hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega)).bytes b2 (by omega)]
  have A0 : wordsVal s₅.mem L.Q (slot L.wq 0) L.wq = arrQ s.mem L 0 := by
    rw [m5, show wordsVal s₄.mem L.Q (slot L.wq 0) L.wq = arrQ s₄.mem L 0 from rfl,
      qa_eq hL o4 (by decide) (by omega), m3, qa_eq hL o2 (by decide) (by omega), m1]
  rw [A5, A0] at t0
  refine ⟨⟨t0, Q6.stepM kt mt, ?_⟩, ?_⟩
  · rw [mt]; exact b4.trans (by rw [← m5]; exact Body.ofQ hL o6 (by omega))
  · exact ((((k13.trans k4).trans k5).trans k6).trans kt).mono (by decide)

/-- The registers `keyPair; xRange` write. -/
def vrestRegs : List Reg := keyPairRegs ++ xRangePRegs

/-- `keyPair; xRange` after `checkSignKey`: `a0 :=` 1 exactly when
`g^x mod p = y` and `0 < x < q`. Memory changes only in `hMask` and past the
header. -/
theorem vrest_ok {s₀ s : State} {L : Lay} {key sig : Addr} {d : Nat} (hL : L.Ok) (hK : ParamsOk s₀.mem L key)
    (hc : Checked s₀ s L key sig d) (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) :
    WP isa (.seq Sign.keyPair PrevalidatedSign.xRange) s fun t =>
      (t.gpr .a0 = BitVec.ofNat 64 (if gOf s₀.mem L key ^ xOf s.mem L key % pOf s₀.mem L key = yOf s₀.mem L key ∧
          (0 < xOf s.mem L key ∧ xOf s.mem L key < qOf s₀.mem L key) then 1 else 0) ∧
        t.gpr .s6 = L.S ∧ ScrL t L ∧ BKept L s.mem t.mem) ∧ Keep vrestRegs s t := by
  have hk3 : Src s L key (3 * L.pl + L.ql) := hk.take (by omega)
  have hk2 : Src s L key (2 * L.pl + L.ql) := hk.take (by omega)
  obtain ⟨-, eq, eg⟩ := params_kept hk2 hkp
  have ey := y_kept hk3 hkp
  have ep := (params_kept hk2 hkp).1
  have B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hpo : pOf s₀.mem L key % 2 = 1 := hK.1.2.2
  refine WP.seq (WP.mono (keyPair_ok hL hc.scr hc.regs hc.inp hc.inv hk hc.p0 (by omega) hpo hc.p24)
    fun s₁ ⟨⟨mx₁, _, _, m, o₁, w₁⟩, k₁⟩ => ?_)
  have K₁ : BKept L s.mem s₁.mem := (BKept.ofBody hL (PLow.body hL o₁)).trans (BKept.ofMask hL w₁)
  have q0₁ : arrQ s₁.mem L 0 = qOf s₀.mem L key := by
    rw [keepQ_arr0 hL (mask_keepQ hL w₁), keepQ_arr0 hL (PLow.keepQ hL o₁)]; exact hc.q0
  refine WP.mono (xRangeP_ok hL (hc.scr.congr k₁.2.2) (hc.regs.ofBKept k₁ K₁) (hk.keep k₁.2.1 k₁.2.2) mx₁)
    fun t ⟨⟨t0, Qt, bt⟩, kt⟩ => ⟨⟨?_, Qt.regs.s6, Qt.scr, K₁.trans (BKept.ofBody hL bt)⟩, k₁.trans kt⟩
  have ex : xOf s₁.mem L key = xOf s.mem L key := by
    simp only [xOf]; rw [(hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega)).bytes K₁.out (by omega)]
  rw [t0, q0₁, ex, eg, ey]
  congr 1
  by_cases h₁ : gOf s₀.mem L key ^ xOf s.mem L key % pOf s₀.mem L key = yOf s₀.mem L key <;>
    by_cases h₂ : 0 < xOf s.mem L key ∧ xOf s.mem L key < qOf s₀.mem L key <;> simp [h₁, h₂]

theorem validatePriv_correct (s : State) (h : vpkContract.pre s) :
    ∃ tr t, Exec isa PrevalidatedSign.validate s tr t ∧ abiPreserved s t ∧ vpkContract.post s t := by
  show WP isa PrevalidatedSign.validate s fun t => abiPreserved s t ∧ vpkContract.post s t
  have hL : (playOf s).Ok := playOf_ok_of h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
  have hZ := hL.z256
  obtain ⟨hrd, hwr, dKS, -, nw, hv, hkl, -, alS, -⟩ := h
  have hplq : 3 * (playOf s).pl + 2 * (playOf s).ql = (s.gpr .a1).toNat := by simp only [playOf]; omega
  have src : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr →
      Src t (playOf s) (s.gpr .a0) (3 * (playOf s).pl + 2 * (playOf s).ql) :=
    fun hr hw => psrc_of hrd dKS (Nat.le_of_eq hplq) hr hw
  have hkey : Spec.Dsa.privateKeyBytes (s.gpr .a2).toNat (s.gpr .a3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) =
      ⟨⟨pOf s.mem (playOf s) (s.gpr .a0), qOf s.mem (playOf s) (s.gpr .a0), gOf s.mem (playOf s) (s.gpr .a0)⟩,
        yOf s.mem (playOf s) (s.gpr .a0), some (xOf s.mem (playOf s) (s.gpr .a0))⟩ := by
    rw [VG.Proof.Dsa.privateKeyBytes_at s.mem (s.gpr .a0) (by simp only [playOf] at hplq; omega),
      VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .a0) (by simp only [playOf] at hplq; omega)]
    rfl
  have hspec := validatePrivate_eq hv (by rw [VG.Proof.Bignum.bytesAt_length]; exact hkl) hkey
  suffices main : WP isa PrevalidatedSign.validate s fun w =>
      ((∀ r ∈ preserved, w.gpr r = s.gpr r) ∧ w.gpr .ra = s.gpr .ra) ∧
        ((w.gpr .a0).setWidth 32).toNat = if Spec.Dsa.validatePrivateKeyBytes (s.gpr .a2).toNat
          (s.gpr .a3).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) then 1 else 0 from
    WP.mono (WP.rdwr main) fun w ⟨⟨⟨hp, hra⟩, w0⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, w0⟩
  rw [hspec]
  unfold PrevalidatedSign.validate
  refine WP.seq (WP.mono (pfront_ok_of hL hwr nw alS) fun s₁ ⟨F, k₁⟩ => ?_)
  have hsav' : ∀ u : State, Kept (playOf s) s₁.mem u.mem → ∀ i < 13,
      word u.mem (s.gpr .a4) (saveOff i) = s.gpr (saved i) := fun u hu i hi =>
    (hu.word (Or.inr ⟨by simp only [saveOff, hLens]; omega, by simp only [saveOff]; omega⟩)).trans (F.sav i hi)
  have Out₁ : Outside (playOf s).S 0 (playOf s).Z s.mem s₁.mem :=
    F.out.mono (Nat.le_refl _) (by simp only [playOf] at hZ ⊢; omega)
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := keyVals_kept ((src rfl rfl).take (k := 3 * (playOf s).pl + (playOf s).ql)
    (by omega)) Out₁
  have hKs : SignKeyOk s₁.mem (playOf s) (s.gpr .a0) ↔ SignKeyOk s.mem (playOf s) (s.gpr .a0) := by
    simp only [SignKeyOk, ParamsOk, ep₁, eq₁, eg₁, ey₁]
  refine WP.seq (checkSignKey_ok hL F.scr F.regs F.lens (by decide) ((src k₁.2.1 k₁.2.2).take (by omega))
    (fun t hK hc Kd kc => ?_) (fun t hn Kd hrt scrt kc => ?_))
  · have kt := k₁.trans kc
    refine WP.mono (vrest_ok hL hK.1 hc Kd (src kt.2.1 kt.2.2)) fun u ⟨⟨u0, u6, scru, Ku⟩, _⟩ => ?_
    refine WP.mono (sfinish_ok u6
      (fun i hi => by
        rw [← saveOff_eq]; exact scru.st (d := saveOff i) (by simp only [saveOff, playOf] at hZ ⊢; omega_arith))
      (fun i hi => by
        rw [← saveOff_eq]
        exact scru.al8 (d := saveOff i) (by simp only [saveOff, playOf] at hZ ⊢; omega_arith)
          (by simp only [saveOff]; omega))
      (fun i hi => (Ku.word (by simp only [saveOff]; omega) (by simp only [saveOff]; omega)).trans
        (hsav' t Kd i hi))) fun w ⟨hab, w0, _⟩ => ⟨hab, ?_⟩
    have Ot : Outside (playOf s).S 0 (playOf s).Z s.mem t.mem := Out₁.trans Kd.out
    have ex : xOf t.mem (playOf s) (s.gpr .a0) = xOf s.mem (playOf s) (s.gpr .a0) := by
      simp only [xOf]
      rw [((src rfl rfl).sub (o := 3 * (playOf s).pl + (playOf s).ql) (k := (playOf s).ql) (by omega)).bytes Ot
        (by omega)]
    have hKt := hKs.mp hK
    rw [w0, u0, ep₁, eq₁, eg₁, ey₁, ex]
    have e := privChecks_iff (x := xOf s.mem (playOf s) (s.gpr .a0)) hKt.1 hKt.2
    by_cases hc' : gOf s.mem (playOf s) (s.gpr .a0) ^ xOf s.mem (playOf s) (s.gpr .a0) %
        pOf s.mem (playOf s) (s.gpr .a0) = yOf s.mem (playOf s) (s.gpr .a0) ∧
        (0 < xOf s.mem (playOf s) (s.gpr .a0) ∧ xOf s.mem (playOf s) (s.gpr .a0) < qOf s.mem (playOf s) (s.gpr .a0))
    · rw [ite_eq_left hc', ite_eq_left (decide_eq_true (e.mpr hc'))]; rfl
    · rw [ite_eq_right hc', ite_eq_right (fun hx => hc' (e.mp (of_decide_eq_true hx)))]; rfl
  · refine WP.mono (pret_ok (c := 0) (Or.inl rfl) hL hrt.s6 scrt (hsav' t Kd)) fun u hu =>
      WP.mono hu fun w ⟨hab, w0⟩ => ⟨hab, ?_⟩
    rw [w0, ite_eq_right]
    intro hx
    obtain ⟨hsh, hpub, -, -⟩ := of_decide_eq_true hx
    exact hn (hKs.mpr ⟨⟨hsh, hpub.1.1, hpub.2.1, hpub.2.2.1⟩, hpub.1.2⟩)

end VG.Proof.Dsa.RISCV64
