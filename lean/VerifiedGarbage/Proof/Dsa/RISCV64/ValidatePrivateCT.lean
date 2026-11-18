module

import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
public import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignCTB
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.RISCV64.SignKeyPair
import VerifiedGarbage.Proof.Dsa.RISCV64.SignCommon
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Flat
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsCT
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTParams
meta import VerifiedGarbage.Proof.Dsa.RISCV64.CTBodyB
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignCTB
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignKeyPair
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignCommon
meta import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.RISCV64.Arr
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Flat
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
public import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedSignFn
public import VerifiedGarbage.Impl.Dsa.RISCV64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyComb
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
meta import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedSignFn
meta import VerifiedGarbage.Impl.Dsa.RISCV64.PrevalidatedSign
meta import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
meta import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
meta import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyComb
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.Accepted
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Dsa.RISCV64.ValidatePrivateFn`, which this module and modules that import it used -/

section

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
    ⟨hP.1, ⟨⟨hP.2.1, hy⟩, hP.2.2.1, hP.2.2.2, pow_order_of_gen (by omega_using [hy]) hP.2.2.2 hg⟩, hx, hg⟩⟩

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
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
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
  have Q2 := Q1.step k2 (Body.ofQ hL o2 (by omega_using [hwq, e7]))
  refine WP.seq (WP.mono (ptrX_ok Q2.scr hL Q2.regs) fun s₃ ⟨⟨c7, c8, m3⟩, k3⟩ => ?_)
  have Q3 := Q2.stepM k3 m3
  have k13 := (k1.trans k2).trans k3
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q3 hL (by decide)
      ((hk.keep k13.2.1 k13.2.2).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_using [])) c7 c8
      (by omega_using [hql]) (by omega_using [hwq])) fun s₄ ⟨⟨Q4, v5, top5, o4⟩, k4⟩ => ?_)
  have b2 : Body L s.mem s₂.mem := by rw [← m1]; exact Body.ofQ hL o2 (by omega_using [hwq, e7])
  have b4 : Body L s.mem s₄.mem := b2.trans (by rw [← m3]; exact Body.ofQ hL o4 (by omega_using [hwq, e5]))
  obtain ⟨hld, hal⟩ := ScrL.hdr Q4.scr hL (d := 0) (by decide) (by decide)
  have hw4 : word s₄.mem L.S hMask = mask b := by rw [b4.word (by decide)]; exact hm
  refine WP.seq (WP.mono (WP.keep [.a4] (Q := fun u => u.gpr .a4 = mask b ∧ u.mem = s₄.mem)
    (by brun [hMask, Q4.regs.s6, hld, hal]; exact hw4) (by decide) (by rfl)) fun s₅ ⟨⟨a4, m5⟩, k5⟩ => ?_)
  have Q5 := Q4.stepM k5 m5
  have z7' : wordsVal s₅.mem L.Q (slot L.wq 7) L.wq = 0 := by
    rw [m5, show wordsVal s₄.mem L.Q (slot L.wq 7) L.wq = arrQ s₄.mem L 7 from rfl,
      qa_eq hL o4 (by decide) (by omega_using [e5, e7]), m3]
    exact z7
  have top5' : word s₅.mem L.Q (slot L.wq 5 + 8 * L.wq) = 0 := by rw [m5]; exact top5
  refine WP.seq (WP.mono (inRange_ok Q5.inq.env (a := 5) (b := b) (by decide) (by decide) (by decide) top5' z7' a4)
    fun s₆ ⟨⟨c4, o6⟩, k6⟩ => ?_)
  have Q6 := Q5.step k6 (Body.ofQ hL o6 (by omega_using [hwq, e3]))
  refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = BitVec.ofNat 64 (if (b && decide
      (0 < wordsVal s₅.mem L.Q (slot L.wq 5) L.wq ∧
        wordsVal s₅.mem L.Q (slot L.wq 5) L.wq < wordsVal s₅.mem L.Q (slot L.wq 0) L.wq)) then 1 else 0) ∧
      u.mem = s₆.mem)
    (by brun [c4, mask_low]) (by decide) (by rfl)) fun t ⟨⟨t0, mt⟩, kt⟩ => ?_
  have A5 : wordsVal s₅.mem L.Q (slot L.wq 5) L.wq = xOf s.mem L key := by
    rw [m5]
    refine v5.trans ?_
    rw [xOf, m3, (hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_using [])).bytes b2 (by omega_using [hZ])]
  have A0 : wordsVal s₅.mem L.Q (slot L.wq 0) L.wq = arrQ s.mem L 0 := by
    rw [m5, show wordsVal s₄.mem L.Q (slot L.wq 0) L.wq = arrQ s₄.mem L 0 from rfl,
      qa_eq hL o4 (by decide) (by omega_using [e0, e5]), m3, qa_eq hL o2 (by decide) (by omega_using [e0, e7]), m1]
  rw [A5, A0] at t0
  refine ⟨⟨t0, Q6.stepM kt mt, ?_⟩, ?_⟩
  · rw [mt]; exact b4.trans (by rw [← m5]; exact Body.ofQ hL o6 (by omega_using [hwq, e3]))
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
  have hk3 : Src s L key (3 * L.pl + L.ql) := hk.take (by omega_using [])
  have hk2 : Src s L key (2 * L.pl + L.ql) := hk.take (by omega_using [])
  obtain ⟨-, eq, eg⟩ := params_kept hk2 hkp
  have ey := y_kept hk3 hkp
  have ep := (params_kept hk2 hkp).1
  have B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hpo : pOf s₀.mem L key % 2 = 1 := hK.1.2.2
  refine WP.seq (WP.mono (keyPair_ok hL hc.scr hc.regs hc.inp hc.inv hk hc.p0 (by omega_using [B]) hpo hc.p24)
    fun s₁ ⟨⟨mx₁, _, _, m, o₁, w₁⟩, k₁⟩ => ?_)
  have K₁ : BKept L s.mem s₁.mem := (BKept.ofBody hL (PLow.body hL o₁)).trans (BKept.ofMask hL w₁)
  have q0₁ : arrQ s₁.mem L 0 = qOf s₀.mem L key := by
    rw [keepQ_arr0 hL (mask_keepQ hL w₁), keepQ_arr0 hL (PLow.keepQ hL o₁)]; exact hc.q0
  refine WP.mono (xRangeP_ok hL (hc.scr.congr k₁.2.2) (hc.regs.ofBKept k₁ K₁) (hk.keep k₁.2.1 k₁.2.2) mx₁)
    fun t ⟨⟨t0, Qt, bt⟩, kt⟩ => ⟨⟨?_, Qt.regs.s6, Qt.scr, K₁.trans (BKept.ofBody hL bt)⟩, k₁.trans kt⟩
  have ex : xOf s₁.mem L key = xOf s.mem L key := by
    simp only [xOf]; rw [(hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_using [])).bytes K₁.out (by omega_using [])]
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
  have hplq : 3 * (playOf s).pl + 2 * (playOf s).ql = (s.gpr .a1).toNat := by simp only [playOf]; omega_using [hkl]
  have src : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr →
      Src t (playOf s) (s.gpr .a0) (3 * (playOf s).pl + 2 * (playOf s).ql) :=
    fun hr hw => psrc_of hrd dKS (Nat.le_of_eq hplq) hr hw
  have hkey : Spec.Dsa.privateKeyBytes (s.gpr .a2).toNat (s.gpr .a3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) =
      ⟨⟨pOf s.mem (playOf s) (s.gpr .a0), qOf s.mem (playOf s) (s.gpr .a0), gOf s.mem (playOf s) (s.gpr .a0)⟩,
        yOf s.mem (playOf s) (s.gpr .a0), some (xOf s.mem (playOf s) (s.gpr .a0))⟩ := by
    rw [VG.Proof.Dsa.privateKeyBytes_at s.mem (s.gpr .a0) (by simp only [playOf] at hplq; omega_using [hkl]),
      VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .a0) (by simp only [playOf] at hplq; omega_using [hkl])]
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
    (hu.word (Or.inr ⟨by simp only [saveOff, hLens]; omega_using [], by simp only [saveOff]; omega_using [hi]⟩)).trans (F.sav i hi)
  have Out₁ : Outside (playOf s).S 0 (playOf s).Z s.mem s₁.mem :=
    F.out.mono (Nat.le_refl _) (by simp only [playOf] at hZ ⊢; omega_using [hZ])
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := keyVals_kept ((src rfl rfl).take (k := 3 * (playOf s).pl + (playOf s).ql)
    (by omega_using [])) Out₁
  have hKs : SignKeyOk s₁.mem (playOf s) (s.gpr .a0) ↔ SignKeyOk s.mem (playOf s) (s.gpr .a0) := by
    simp only [SignKeyOk, ParamsOk, ep₁, eq₁, eg₁, ey₁]
  refine WP.seq (checkSignKey_ok hL F.scr F.regs F.lens (by decide) ((src k₁.2.1 k₁.2.2).take (by omega_using []))
    (fun t hK hc Kd kc => ?_) (fun t hn Kd hrt scrt kc => ?_))
  · have kt := k₁.trans kc
    refine WP.mono (vrest_ok hL hK.1 hc Kd (src kt.2.1 kt.2.2)) fun u ⟨⟨u0, u6, scru, Ku⟩, _⟩ => ?_
    refine WP.mono (sfinish_ok u6
      (fun i hi => by
        rw [← saveOff_eq]; exact scru.st (d := saveOff i) (by simp only [saveOff, playOf] at hZ ⊢; omega_arith))
      (fun i hi => by
        rw [← saveOff_eq]
        exact scru.al8 (d := saveOff i) (by simp only [saveOff, playOf] at hZ ⊢; omega_arith)
          (by simp only [saveOff]; omega_using []))
      (fun i hi => (Ku.word (by simp only [saveOff]; omega_using []) (by simp only [saveOff]; omega_using [hi])).trans
        (hsav' t Kd i hi))) fun w ⟨hab, w0, _⟩ => ⟨hab, ?_⟩
    have Ot : Outside (playOf s).S 0 (playOf s).Z s.mem t.mem := Out₁.trans Kd.out
    have ex : xOf t.mem (playOf s) (s.gpr .a0) = xOf s.mem (playOf s) (s.gpr .a0) := by
      simp only [xOf]
      rw [((src rfl rfl).sub (o := 3 * (playOf s).pl + (playOf s).ql) (k := (playOf s).ql) (by omega_using [])).bytes Ot
        (by omega_using [])]
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

end

end

-- separate module: the taint checks of its levels cost more than their imports, and the registration
-- states the result without them

/-!
# DSA private-key validation on RISC-V: constant time

`vg_dsa_validate_private_key` (`PrevalidatedSign.validate`) runs
`vg_dsa_validate_public_key`'s entry, then `checkSignKey`'s checks of the
domain and of y's range, then `keyPair; xRange` (`VR`). Its public data
(`vdV`) are the key's public octets p||q||g||y (not x), and `scratch`. Its
levels up to y's range are validation's (`ValidateCT.lean`), but the key's
level has no `elemOrder`, as signing's (`SignCT.lean`). `VR` is cut as
signing's body is in `keyPair` (2, 12, 53), then after it (64), after
`enterQ` (65) and after `ptrX` (69); between them the phase `VK` carries the
P space's facts and x's region. Nothing branches on x: the result is the
mask's low bit.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.CT

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Proof.Dsa.RISCV64
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_taint)
open VG.Proof.Bignum.RISCV64 (At chain_cons chain_start at_zero_inv take_split)
open VG.Proof.Bignum (slot)

/-! ## The entry -/

/-- A call's public data: the key's public octets. -/
def vdV (s : State) : VD :=
  ⟨playOf s, s.gpr .a0, 0, 0, 0, Spec.Rsa.bytesAt s.mem (s.gpr .a0) (3 * (s.gpr .a2).toNat + (s.gpr .a3).toNat),
    3 * (s.gpr .a2).toNat + (s.gpr .a3).toNat, 0, false, none⟩

/-- On entry. -/
def C0v (v : VD) (s : State) : Prop := vpkContract.pre s ∧ vdV s = v

theorem frontV : ∀ v s, C0v v s → WP isa (.block Params.entry) s (P0 v) := by
  rintro _ s ⟨h, rfl⟩
  have hL : (playOf s).Ok := playOf_ok_of h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
  have hZ := hL.z256
  obtain ⟨hrd, hwr, dKS, -, nw, -, hkl, -, alS, -⟩ := h
  refine WP.mono (pfront_ok_of hL hwr nw alS) fun t ⟨F, k⟩ => ?_
  have hK : Src t (playOf s) (s.gpr .a0) (3 * (s.gpr .a2).toNat + (s.gpr .a3).toNat) :=
    psrc_of hrd dKS (by omega_using [hkl]) k.2.1 k.2.2
  exact ⟨⟨hL, F.regs, F.scr, hK, src_nil rfl, src_nil (Nat.zero_min _),
    hK.bytes F.out (by simp only [playOf] at hZ ⊢; omega_using [hZ]), (by simp only [vdV, playOf]; omega_using []),
    (fun h => nomatch h), fun _ h => nomatch h⟩, F.lens.trans (congrArg _ (Nat.zero_min _).symm)⟩

theorem kyC0v : ∀ v s, C0v v s → KY v := by
  rintro _ s ⟨-, rfl⟩
  exact Nat.le_refl _

/-- x's octets, with the key's, may be read, apart from `scratch`. -/
abbrev XS (v : VD) (u : State) : Prop := Src u v.L v.key (3 * v.L.pl + 2 * v.L.ql)

theorem xsC0v : ∀ v s, C0v v s → XS v s := by
  rintro _ s ⟨h, rfl⟩
  obtain ⟨hrd, -, dKS, -, -, -, hkl, -⟩ := h
  exact psrc_of hrd dKS (by simp only [vdV, playOf]; omega_using [hkl]) rfl rfl

theorem xs_at {Φ : VD → State → Prop} {F : List (Prog isa)} {n : Nat} (h : ∀ v s, Φ v s → XS v s) {v : VD}
    {u : State} (hu : At Φ F n v u) : XS v u := by
  obtain ⟨s₀, t, h₀, e⟩ := hu
  obtain ⟨hr, hw, -⟩ := Exec.rdwr e
  exact (h v s₀ h₀).keep hr hw

/-! ## The levels -/

abbrev VR : Prog isa := .seq Sign.keyPair PrevalidatedSign.xRange
abbrev RKv : Prog isa := andThen (.seq (.block ptrY) (.seq (loadArr 4) elemRange)) VR fail0
abbrev R3v : Prog isa := .seq setupP (andThen (.seq (.block ptrG) checkElem) RKv fail0)
abbrev R2v : Prog isa := andThen pModQ R3v fail0
abbrev R1v : Prog isa := andThen (.block (ptrQ ++ odd)) R2v fail0
abbrev R0v : Prog isa := odds R2v fail0
abbrev X2v : Prog isa :=
  .seq (.block [.addi .a3 .a1 0, .shift .sll .d .t3 .a1 32, .load .d .t4 .s6 hLens, .add .t4 .t4 .t3,
    .store .d .t4 .s6 hLens]) (andThen pairs R0v fail0)
abbrev X1v : Prog isa := .seq (.block [.addi .a2 .a1 0]) (andThen (.seq (.block ptrQ) bytesBits) X2v fail0)

abbrev FTv : List (Prog isa) := Code.flat PrevalidatedSign.validate
abbrev FX1v : List (Prog isa) := Code.flat X1v
abbrev FX2v : List (Prog isa) := Code.flat X2v
abbrev FR0v : List (Prog isa) := Code.flat R0v
abbrev FR1v : List (Prog isa) := Code.flat R1v
abbrev FR2v : List (Prog isa) := Code.flat R2v
abbrev FR3v : List (Prog isa) := Code.flat R3v
abbrev FKv : List (Prog isa) := Code.flat RKv
abbrev FVR : List (Prog isa) := Code.flat VR

abbrev ΦX1v (v : VD) (u : State) : Prop := At C0v FTv 5 v u ∧ u.gpr .a0 = 0
abbrev ΦX2v (v : VD) (u : State) : Prop := At ΦX1v FX1v 5 v u ∧ u.gpr .a0 = 0
abbrev ΦR0v (v : VD) (u : State) : Prop := At ΦX2v FX2v 12 v u ∧ u.gpr .a0 = 0
abbrev ΦR1v (v : VD) (u : State) : Prop := At ΦR0v FR0v 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR2v (v : VD) (u : State) : Prop := At ΦR1v FR1v 1 v u ∧ u.gpr .a0 = 0
abbrev ΦR3v (v : VD) (u : State) : Prop := At ΦR2v FR2v 23 v u ∧ u.gpr .a0 = 0
abbrev ΦEgv (v : VD) (u : State) : Prop := At ΦR3v FR3v 45 v u ∧ u.gpr .a0 = 0
abbrev ΦKv (v : VD) (u : State) : Prop := At ΦR3v FR3v 46 v u ∧ u.gpr .a0 = 0
abbrev ΦVR (v : VD) (u : State) : Prop := At ΦKv FKv 28 v u ∧ u.gpr .a0 = 0

theorem hFTv : (FTv.drop 5).take 1 = [.ite (.zero .a0) X1v fail0] := rfl
theorem hFX1v : (FX1v.drop 5).take 1 = [.ite (.zero .a0) X2v fail0] := rfl
theorem hFX2v : (FX2v.drop 12).take 1 = [.ite (.zero .a0) R0v fail0] := rfl
theorem hFR0v : (FR0v.drop 1).take 1 = [.ite (.zero .a0) R1v fail0] := rfl
theorem hFR1v : (FR1v.drop 1).take 1 = [.ite (.zero .a0) R2v fail0] := rfl
theorem hFR2v : (FR2v.drop 23).take 1 = [.ite (.zero .a0) R3v fail0] := rfl
theorem hFR3gv : (FR3v.drop 45).take 1 = [.ite (.zero .a0) elemOrder (.block [])] := rfl
theorem hFR3v : (FR3v.drop 46).take 1 = [.ite (.zero .a0) RKv fail0] := rfl
theorem hFKv : (FKv.drop 28).take 1 = [.ite (.zero .a0) VR fail0] := rfl

theorem runTv : ∀ v s, C0v v s → WP isa (Code.seqL FTv) s fun _ => True := fun _ s h =>
  let ⟨tr, t, e, _⟩ := validatePriv_correct s h.1
  ⟨tr, t, exec_flat.mp e, trivial⟩

theorem runX1v : ∀ v s, ΦX1v v s → WP isa (Code.seqL FX1v) s fun _ => True := run_then runTv hFTv
theorem runX2v : ∀ v s, ΦX2v v s → WP isa (Code.seqL FX2v) s fun _ => True := run_then runX1v hFX1v
theorem runR0v : ∀ v s, ΦR0v v s → WP isa (Code.seqL FR0v) s fun _ => True := run_then runX2v hFX2v
theorem runR1v : ∀ v s, ΦR1v v s → WP isa (Code.seqL FR1v) s fun _ => True := run_then runR0v hFR0v
theorem runR2v : ∀ v s, ΦR2v v s → WP isa (Code.seqL FR2v) s fun _ => True := run_then runR1v hFR1v
theorem runR3v : ∀ v s, ΦR3v v s → WP isa (Code.seqL FR3v) s fun _ => True := run_then runR2v hFR2v
theorem runEgv : ∀ v s, ΦEgv v s → WP isa (Code.seqL FE) s fun _ => True := run_then runR3v hFR3gv
theorem runKv : ∀ v s, ΦKv v s → WP isa (Code.seqL FKv) s fun _ => True := run_then runR3v hFR3v
theorem runVR : ∀ v s, ΦVR v s → WP isa (Code.seqL FVR) s fun _ => True := run_then runKv hFKv

theorem onX1v : ∀ v u, ΦX1v v u → SX1 v u := fun _ _ h => semX1 frontV ⟨atL rfl h.1, h.2⟩
theorem onX2v : ∀ v u, ΦX2v v u → SX2 v u := fun _ _ h => semX2 onX1v ⟨atL rfl h.1, h.2⟩
theorem onR0v : ∀ v u, ΦR0v v u → P1 v u := fun _ _ h => semR0 onX2v ⟨atL rfl h.1, h.2⟩
theorem onR1v : ∀ v u, ΦR1v v u → P1 v u ∧ v.p % 2 = 1 := fun _ _ h => semR1 onR0v ⟨atL rfl h.1, h.2⟩
theorem onR2v : ∀ v u, ΦR2v v u → SR2 v u := fun _ _ h => semR2 onR1v ⟨atL rfl h.1, h.2⟩
theorem onR3v : ∀ v u, ΦR3v v u → SR3 v u := fun _ _ h => semR3 onR2v ⟨atL rfl h.1, h.2⟩

theorem kyR3v : ∀ v u, ΦR3v v u → KY v := fun _ _ h =>
  at_pure (G := KY) (fun _ _ h => at_pure (G := KY) (fun _ _ h => at_pure (G := KY) (fun _ _ h =>
    at_pure (G := KY) (fun _ _ h => at_pure (G := KY) (fun _ _ h => at_pure (G := KY) kyC0v h.1) h.1) h.1) h.1)
      h.1) h.1

theorem xsKv : ∀ v u, ΦKv v u → XS v u := fun _ _ h =>
  xs_at (fun _ _ h => xs_at (fun _ _ h => xs_at (fun _ _ h => xs_at (fun _ _ h => xs_at (fun _ _ h =>
    xs_at (fun _ _ h => xs_at xsC0v h.1) h.1) h.1) h.1) h.1) h.1) h.1

theorem onKv : ∀ v u, ΦKv v u → SK v u := fun _ _ h => semK onR3v kyR3v ⟨atL rfl h.1, h.2⟩

theorem midKv {v : VD} {s : State} (h : ΦKv v s) : WP isa (Code.seqL (FKv.take 28)) s (MKs v) := by
  obtain ⟨c, km, eg, ky⟩ := onKv _ _ h
  exact WP.of_flat (c := .seq (.block ptrY) (.seq (loadArr 4) elemRange)) rfl
    (WP.seq ((ptr_CK c (ptrY_ok c.base.scr c.base.ok c.base.regs)).mono fun _ ⟨⟨c', a7, a8⟩, _⟩ =>
      (yrange_CK c' (by omega) a7 a8).mono fun _ ⟨c'', a0⟩ => ⟨⟨c'', km, eg, ky⟩, a0⟩))

theorem zeroKv : ∀ v s₁ s₂, At ΦKv FKv 28 v s₁ → At ΦKv FKv 28 v s₂ → (s₁.gpr .a0 == 0) = (s₂.gpr .a0 == 0) :=
  zero_at (fun v => ERange v (2 * v.L.pl + v.L.ql)) fun _ _ h => (midKv h).mono fun _ h => h.2

/-! ## `VR` -/

/-- `VR`'s phase: the P space as the checks leave it, q in the Q space's array
0, and x's region. -/
structure VK (v : VD) (t : State) : Prop where
  cb : CB v t
  q0 : arrQ t.mem v.L 0 = v.q
  xs : XS v t

theorem VK.keepM {v : VD} {s t : State} {rs : List Reg} (h : VK v s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ inRegs ++ regsRegs ++ ([.t1] : List Reg), r ∉ rs := by decide) : VK v t :=
  ⟨⟨h.cb.1.keepM k hm fun r hm' => hr r (by simp [hm']),
    h.cb.2.1.keep k fun r hm' => hr r (by simp [hm']),
    by show ((word t.mem v.L.S (slot v.L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
       rw [hm, k.gpr (fun hm' => hr .t1 (by simp) hm')]; exact h.cb.2.2.1,
    by rw [arrP, hm]; exact h.cb.2.2.2.1, by rw [arrP, hm]; exact h.cb.2.2.2.2⟩,
    by rw [arrQ, hm]; exact h.q0, h.xs.keep k.2.1 k.2.2⟩

/-- `VR`'s states are in its phase. -/
theorem onVR {v : VD} {u : State} (h : ΦVR v u) : VK v u ∧ KM v := by
  have m := at_sem (Φ := ΦKv) (F := FKv) (n := 28) (M := MKs) (fun _ _ h => midKv h) h.1
  obtain ⟨⟨c, km, -⟩, -⟩ := m
  exact ⟨⟨⟨c.base, c.inp, c.inv, c.p0, c.p24⟩, c.q0, xs_at xsKv h.1⟩, km⟩

/-- `keyPair`'s first block: x's and g's pointers. -/
theorem stKV0 {v : VD} {s : State} {c : Prog isa} {Q : State → Prop} (h : VK v s)
    (hc : ∀ t, VK v t → t.gpr .s7 = off v.key (v.L.pl + v.L.ql) → t.gpr .s8 = BitVec.ofNat 64 v.L.pl →
      t.gpr .s9 = off v.key (3 * v.L.pl + v.L.ql) → WP isa c t Q) :
    WP isa (.seq (.block KP0) c) s Q := by
  have B := h.cb.1
  have hL := B.ok
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (ptrX_ok B.scr hL B.regs) fun s₁ ⟨⟨a7, _, m1⟩, k1⟩ =>
    WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = off v.key (3 * v.L.pl + v.L.ql) ∧ u.mem = s₁.mem)
      (by brun [a7, BitVec.add_zero]) (by decide) (by rfl)) fun s₂ ⟨⟨a9, m2⟩, k2⟩ => ?_)))
  have h2 := (h.keepM k1 m1).keepM k2 m2
  exact WP.mono (ptrG_ok h2.cb.1.scr hL h2.cb.1.regs) fun t ⟨⟨b7, b8, m3⟩, k3⟩ =>
    hc t (h2.keepM k3 m3) b7 b8 ((k3.gpr (by decide)).trans a9)

theorem pinsV0 : Pins (At ΦVR FVR 0) [.s6, .s11, .ra, .a7, .s5, .t0] :=
  pins_at_fix (fun v => fixB v ++ envP v) (fun _ => rfl) fun _ _ h =>
    ⟨[], _, .block rfl, fix_CB (onVR h).1.cb⟩

theorem pinsV2 : Pins (At ΦVR FVR 2) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8, .s9] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl),
      (.s9, off v.key (3 * v.L.pl + v.L.ql))]) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq (.block KP0) (.block (getP .s8))) (by decide +kernel)
      (stKV0 (onVR h).1 fun _ c a7 _ a9 =>
        WP.mono (getP_ok c.cb.1.scr c.cb.1.ok c.cb.1.regs .s8) fun _ ⟨⟨a8, m⟩, k⟩ =>
          (fix_CB (c.keepM k m).cb).app
            ⟨(k.gpr (r := .s7) (by decide)).trans a7, a8, (k.gpr (r := .s9) (by decide)).trans a9, trivial⟩)

theorem pinsV12 : Pins (At ΦVR FVR 12) [.s6, .s11, .ra, .a7, .s5, .t0, .s9, .s10] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s9, off v.key (3 * v.L.pl + v.L.ql)), (.s10, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq (.block KP0) (.seq (.block (getP .s8)) (.seq (loadArr 4) (.seq (copy 1 24)
      (.block (getQ .s10)))))) (by decide +kernel)
      (stKV0 (onVR h).1 fun _ c a7 _ a9 =>
        powP_pre c.cb (c.cb.1.hk.sub (by have := c.cb.1.kn; omega_using [this])) a7 a9)

/-- A power in the P space, from its pointers. -/
theorem powV {v : VD} {s : State} {N E : Addr} (h : VK v s) (hN : Src s v.L N v.L.pl) (h7 : s.gpr .s7 = N)
    (hE : Src s v.L E v.L.ql) (h9 : s.gpr .s9 = E) (hp : 2 ≤ v.p) (hpo : v.p % 2 = 1) :
    WP isa Verify.powP s fun t => VK v t := by
  have B := h.cb.1; have ip := h.cb.2.1; have I := h.cb.2.2.1; have p0 := h.cb.2.2.2.1
  have p24 := h.cb.2.2.2.2
  have hL := B.ok
  have e := Lay.slot_eq v.L.wp
  have e0 := e 0; have e1 := e 1; have e24 := e 24; have hw := hL.wp_ge
  refine WP.mono (powSrc_ok hL B.scr B.regs ip I hN h7 hE h9 p0 hp hpo p24) fun t ⟨⟨_, ip', I', o⟩, k⟩ => ?_
  have hb := p_arrays_body hL o
  exact ⟨⟨B.body k hb, ip', I', (o.wordsVal (by omega_using [e0, e1]) (by omega_arith)).trans p0,
    (o.wordsVal (by omega_using [e1, e24]) (by omega_arith)).trans p24⟩, (keepQ_arr0 hL (PLow.keepQ hL o)).trans h.q0,
    h.xs.keep k.2.1 k.2.2⟩

theorem pinsV53 : Pins (At ΦVR FVR 53) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envP v ++ [(.s7, off v.key (2 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.pl)])
    (fun _ => rfl) fun _ _ h => by
    obtain ⟨V, hsz, hpo, -⟩ := onVR h
    have bd := VG.Proof.Dsa.supported_bounds hsz
    exact WP.of_flat (c := .seq (.block KP0) (.seq Verify.powP (.block ptrY))) (by kernel_rfl)
      (stKV0 V fun _ c a7 _ a9 => WP.seq (WP.mono (powV c
        (c.cb.1.hk.sub (by have := c.cb.1.kn; omega_using [this])) a7 (c.xs.sub (by omega_using [])) a9 (by omega_using [bd]) hpo) fun _ c' =>
        WP.mono (ptrY_ok c'.cb.1.scr c'.cb.1.ok c'.cb.1.regs) fun _ ⟨⟨b7, b8, m⟩, k⟩ =>
          (fix_CB (c'.keepM k m).cb).app ⟨b7, b8, trivial⟩))

/-- `keyPair`, from `VR`'s phase: `Base` kept. -/
theorem kpV {v : VD} {s : State} (h : ΦVR v s) : WP isa Sign.keyPair s (Base v) := by
  obtain ⟨V, hsz, hpo, -⟩ := onVR h
  have bd := VG.Proof.Dsa.supported_bounds hsz
  have B := V.cb.1
  have hL := B.ok
  refine WP.mono (keyPair_ok hL B.scr B.regs V.cb.2.1 V.cb.2.2.1 V.xs V.cb.2.2.2.1 (by omega_using [bd]) hpo V.cb.2.2.2.2)
    fun t ⟨⟨_, _, _, m, o, w⟩, k⟩ => ?_
  have K : BKept v.L s.mem t.mem := (BKept.ofBody hL (PLow.body hL o)).trans (BKept.ofMask hL w)
  exact B.step (B.regs.ofBKept k K) k.2.1 k.2.2 K.out (K.word (by decide) (by decide)) (K.word (by decide) (by decide))

theorem pinsV64 : Pins (At ΦVR FVR 64) [.s6, .s11, .ra] :=
  pins_at_fix fixB (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := Sign.keyPair) (by kernel_rfl) ((kpV h).mono fun _ B => B.fixB)

theorem pinsV65 : Pins (At ΦVR FVR 65) [.s6, .s11, .ra, .a7, .s5, .t0] :=
  pins_at_fix (fun v => fixB v ++ envQ v) (fun _ => rfl) fun _ _ h =>
    WP.of_flat (c := .seq Sign.keyPair (.block enterQ)) (by kernel_rfl)
      (WP.seq ((kpV h).mono fun _ B => WP.mono (enterQ_ok B.ok B.scr B.regs) fun _ ⟨⟨iq, m⟩, k⟩ =>
        (B.keepM k m).fixB.app (fix_envQ iq)))

theorem pinsV69 : Pins (At ΦVR FVR 69) [.s6, .s11, .ra, .a7, .s5, .t0, .s7, .s8] :=
  pins_at_fix (fun v => fixB v ++ envQ v ++ [(.s7, off v.key (3 * v.L.pl + v.L.ql)), (.s8, BitVec.ofNat 64 v.L.ql)])
    (fun _ => rfl) fun v _ h =>
    WP.of_flat (c := .seq Sign.keyPair (.seq (.block enterQ) (.seq (zeroArr 7) (.block Sign.ptrX))))
      (by kernel_rfl)
      (WP.seq ((kpV h).mono fun _ B => WP.seq (WP.mono (enterQ_ok B.ok B.scr B.regs) fun _ ⟨⟨iq, m⟩, k⟩ => by
        have B1 := B.keepM k m
        have hL := B.ok
        have hwq := hL.wq_ge
        have hqs := hL.qslot
        have e : ∀ j, slot v.L.wq j = 256 + j * (8 * (v.L.wq + 2)) := fun _ => rfl
        have e7 := e 7; have e8 := e 8; have e28 := e 28
        refine WP.seq (WP.mono (zeroArr_ok iq.env (j := 7) (by decide)) fun _ ⟨⟨_, o⟩, k'⟩ => ?_)
        have B2 := B1.body k' (Body.ofQ hL o (by omega_using [hwq, e7]))
        have iq2 := iq.keep k'
        exact WP.mono (ptrX_ok B2.scr hL B2.regs) fun _ ⟨⟨c7, c8, m'⟩, k''⟩ =>
          ((B2.keepM k'' m').fixB.app (fix_envQ (iq2.keep k''))).app ⟨c7, c8, trivial⟩)))

theorem VR_rel : RelCT isa (Two ΦVR) VR fun _ _ => True := by
  refine chain_start (chain_cons runVR (m := 2) (by decide) (two_taint _ pinsV0 (by taint_decide)) ?_)
  refine chain_cons runVR (m := 12) (by decide) (two_taint _ pinsV2 (by taint_decide)) ?_
  refine chain_cons runVR (m := 53) (by decide) (two_taint _ pinsV12 (by taint_decide)) ?_
  refine chain_cons runVR (m := 64) (by decide) (two_taint _ pinsV53 (by taint_decide)) ?_
  refine chain_cons runVR (m := 65) (by decide) (two_taint _ pinsV64 (by taint_decide)) ?_
  refine chain_cons runVR (m := 69) (by decide) (two_taint _ pinsV65 (by taint_decide)) ?_
  exact two_taint _ pinsV69 (by taint_decide)

/-! ## The levels' relations -/

theorem Kv_rel : RelCT isa (Two ΦKv) RKv fun _ _ => True := by
  refine chain_start (chain_cons runKv (m := 1) (by decide)
    (two_taint _ (pinsL rfl (pinsK_0 onKv)) (by taint_decide)) ?_)
  refine chain_cons runKv (m := 28) (by decide) (two_taint _ (pinsL rfl (pinsK_1 onKv)) (by taint_decide)) ?_
  exact chain_cons runKv (m := 29) (by decide) (rel_ite_at hFKv zeroKv VR_rel fail_rel) nil_rel

theorem R3v_rel : RelCT isa (Two ΦR3v) R3v fun _ _ => True := by
  refine chain_start (chain_cons runR3v (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsR3_0 onR3v)) (by taint_decide)) ?_)
  refine chain_cons runR3v (m := 18) (by decide) (two_taint _ (pinsL rfl (pinsR3_2 onR3v)) (by taint_decide)) ?_
  refine chain_cons runR3v (m := 45) (by decide) (two_taint _ (pinsL rfl (pinsR3_18 onR3v)) (by taint_decide)) ?_
  refine chain_cons runR3v (m := 46) (by decide) (rel_ite_at hFR3gv (zeroL rfl (zeroEg onR3v))
    (eo_rel runEgv fun _ _ h => semEg onR3v ⟨atL rfl h.1, h.2⟩) nil_rel) ?_
  exact chain_cons runR3v (m := 47) (by decide) (rel_ite_at hFR3v (zeroL rfl (zeroR3 onR3v)) Kv_rel fail_rel)
    nil_rel

theorem R2v_rel : RelCT isa (Two ΦR2v) R2v fun _ _ => True := by
  refine chain_start (chain_cons runR2v (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsR2_0 onR2v)) (by taint_decide)) ?_)
  refine chain_cons runR2v (m := 10) (by decide) (two_taint _ (pinsL rfl (pinsR2_2 onR2v)) (by taint_decide)) ?_
  refine chain_cons runR2v (m := 23) (by decide) (two_taint _ (pinsL rfl (pinsR2_10 onR2v)) (by taint_decide)) ?_
  exact chain_cons runR2v (m := 24) (by decide) (rel_ite_at hFR2v (zeroL rfl (zeroR2 onR2v)) R3v_rel fail_rel)
    nil_rel

theorem R1v_rel : RelCT isa (Two ΦR1v) R1v fun _ _ => True :=
  chain_start (chain_cons runR1v (m := 1) (by decide) (relL rfl rfl (relR1 onR1v))
    (chain_cons runR1v (m := 2) (by decide) (rel_ite_at hFR1v (zeroL rfl (zeroR1 onR1v)) R2v_rel fail_rel)
      nil_rel))

theorem R0v_rel : RelCT isa (Two ΦR0v) R0v fun _ _ => True :=
  chain_start (chain_cons runR0v (m := 1) (by decide) (relL rfl rfl (relR0 onR0v))
    (chain_cons runR0v (m := 2) (by decide) (rel_ite_at hFR0v (zeroL rfl (zeroR0 onR0v)) R1v_rel fail_rel)
      nil_rel))

theorem X2v_rel : RelCT isa (Two ΦX2v) X2v fun _ _ => True :=
  chain_start (chain_cons runX2v (m := 12) (by decide)
    (two_taint _ (pinsL rfl (pinsX2_0 onX2v)) (by taint_decide))
    (chain_cons runX2v (m := 13) (by decide) (rel_ite_at hFX2v (zeroL rfl (zeroX2 onX2v)) R0v_rel fail_rel)
      nil_rel))

theorem X1v_rel : RelCT isa (Two ΦX1v) X1v fun _ _ => True := by
  refine chain_start (chain_cons runX1v (m := 2) (by decide)
    (two_taint _ (pinsL rfl (pinsX1_0 onX1v)) (by taint_decide)) ?_)
  refine chain_cons runX1v (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsX1_2 onX1v)) (by taint_decide)) ?_
  refine chain_cons runX1v (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsX1_4 onX1v)) (by taint_decide)) ?_
  exact chain_cons runX1v (m := 6) (by decide) (rel_ite_at hFX1v (zeroL rfl (zeroX1 onX1v)) X2v_rel fail_rel)
    nil_rel

theorem s6_keptv : ∀ i ∈ instrs (seg FTv 1 6), dstOf i ≠ some .s6 := by
  have h : (instrs (seg FTv 1 6)).all (fun i => dstOf i != some .s6) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem pinsTv6 : Pins (At C0v FTv 6) [.s6] :=
  pins_fix (fun v => [(.s6, v.L.S)]) (fun _ => rfl) fun v u ⟨s₀, t, h₀, e⟩ => by
    rw [take_split FTv (n := 1) (m := 6) (by decide)] at e
    obtain ⟨_, _, u₁, -, e₁, e₂⟩ := exec_seqL_append.mp e
    have h₁ : u₁.gpr .s6 = v.L.S := (at_sem (Φ := C0v) (F := FTv) (n := 1) (M := P0)
      (fun _ _ h => WP.of_flat (c := .block Params.entry) rfl (frontV _ _ h)) ⟨s₀, _, h₀, e₁⟩).1.regs.s6
    exact ⟨(Exec.gpr_callFree s6_keptv e₂ rfl).trans h₁, trivial⟩

theorem pins_a4v {Φ : VD → State → Prop} (h : ∀ v s, Φ v s → vdV s = v) : Pins Φ [.a4] := by
  intro v s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact congrArg (fun v : VD => v.L.S) ((h _ _ h₁).trans (h _ _ h₂).symm)

theorem validatePriv_rel : RelCT isa (Two C0v) PrevalidatedSign.validate fun _ _ => True := by
  refine chain_start (chain_cons runTv (m := 1) (by decide)
    (two_taint _ (pins_mono (pins_a4v fun _ _ h => h.2) fun _ _ h => at_zero_inv h) (by taint_decide)) ?_)
  refine chain_cons runTv (m := 2) (by decide) (two_taint _ (pinsL rfl (pinsT1 frontV)) (by taint_decide)) ?_
  refine chain_cons runTv (m := 4) (by decide) (two_taint _ (pinsL rfl (pinsT2 frontV)) (by taint_decide)) ?_
  refine chain_cons runTv (m := 5) (by decide) (two_taint _ (pinsL rfl (pinsT4 frontV)) (by taint_decide)) ?_
  refine chain_cons runTv (m := 6) (by decide) (rel_ite_at hFTv (zeroL rfl (zeroT frontV)) X1v_rel fail_rel) ?_
  exact two_taint _ pinsTv6 (by taint_decide)

/-- Runs that agree on the contract's public data have the same public data `vdV`. -/
theorem vdV_eq {s t : State} (hs : vpkContract.pre s) (hp : vpkContract.pub s t) : vdV s = vdV t := by
  obtain ⟨-, e0, e1, e2, e3, e4, e5, hl⟩ := hp
  have hk := hs.2.2.2.2.2.2.1
  obtain ⟨hl, -⟩ := List.append_inj' hl rfl
  simp only [Spec.Dsa.publicBytesLeak, bytesAt_take] at hl
  have e := (List.map_inj_right fun _ _ h => BitVec.eq_of_toNat_eq h).mp hl
  rw [← e0, ← e1, ← e2, ← e3, Nat.min_eq_right (by omega_using [hk])] at e
  simp only [vdV, playOf]
  rw [e, e0, e2, e3, e4, e5]

theorem validatePriv_ct : ConstantTime isa vpkContract.pre vpkContract.pub PrevalidatedSign.validate :=
  RelCT.constantTime (validatePriv_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdV s, ⟨hs, rfl⟩, ⟨ht, (vdV_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.RISCV64.CT
