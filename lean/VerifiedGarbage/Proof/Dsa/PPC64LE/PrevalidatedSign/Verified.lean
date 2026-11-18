module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.CT
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyCT
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.CT
meta import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFn
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.X
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Contract
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFn
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.X
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Dsa.PPC64LE.PrevalidatedSign.ValidateCT`, which only this module used -/

section

/-! ### `Dsa.PPC64LE.PrevalidatedSign.Validate`, which this module and modules that import it used -/

section

/-!
# DSA private-key validation on PPC64LE: the contract on the registers, and the function

`vpkContract`: `vg_dsa_validate_private_key(key = r3, key_len = r4,
p_len = r5, q_len = r6, scratch = r7, scratch_len = r8)`, `vkContract`'s
registers with the packed private key p||q||g||y||x.

`privateChecks_ok`: after `checkKey`, `privateChecks` leaves in `r3` 1 or 0 as
`g^x mod p = y` (`keyPair_ok`) and `0 < x < q` (`xRange_ok`, with `r28` at
x's octets) hold or not. `validatePrivate_correct`: `vg_dsa_validate_private_key`
meets `vpkContract`: after `vg_dsa_check_parameters`'s entry (`pfront_ok_of`),
`checkKey` either runs `privateChecks` (`checkKey_ok`) or leaves 0, which
with `validatePrivate_spec` is the specification's validation.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

/-- The result of validation, on entry. -/
abbrev vpkRes (s : State) : Bool :=
  Spec.Dsa.validatePrivateKeyBytes (s.gpr .r5).toNat (s.gpr .r6).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)

/-- `vg_dsa_validate_private_key`, on the registers. -/
def vpkContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let scr : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat * 8⟩
    s.rd = [key] ∧ s.wr = [scr] ∧ key.Disjoint scr ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .r5).toNat (s.gpr .r6).toNat ∧
      (s.gpr .r4).toNat = 3 * (s.gpr .r5).toNat + 2 * (s.gpr .r6).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .r5).toNat ≤ (s.gpr .r8).toNat
  post s t := ((t.gpr .r3).setWidth 32).toNat = if vpkRes s then 1 else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .r5).toNat (s₁.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat) ++ [if vpkRes s₁ then 1 else 0] =
        Spec.Dsa.publicBytesLeak (s₂.gpr .r5).toNat (s₂.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat) ++ [if vpkRes s₂ then 1 else 0]

theorem vpkContract_lay {s : State} (h : vpkContract.pre s) : (playOf s).Ok :=
  playOf_ok_of h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2

/-- The registers `privateChecks` writes. -/
def privRegs : List Reg := keyPairRegs ++ [.r0, .r6, .r12, .r22, .r28] ++ xRangeRegs ++ [.r0, .r3]

theorem privateChecks_ok {s₀ s : State} {L : Lay} {key : Addr} (hL : L.Ok) (hK : KeyOk s₀.mem L key)
    (hc : Checked s₀ s L key 0 0 0) (hb : Body L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) :
    WP isa PrevalidatedSign.privateChecks s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if PrivOk s₀.mem L key then 1 else 0) ∧ Kept L s.mem t.mem ∧
        t.gpr .r21 = L.S ∧ ScrL t L) ∧ Keep privRegs s t := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hnw := hL.nowrap
  have hw16 := hL.wp_ge
  have hw8 := hL.wp_eq
  have hbe := hL.buf_end
  have e8 := Lay.slot_eq L.wp 8; have e24 := Lay.slot_eq L.wp 24; have e28 := Lay.slot_eq L.wp 28
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have hqZ : slot L.wp 28 + 1600 ≤ L.Z := by simp only [Lay.bOff, Lay.qOff] at hbe; omega_arith
  obtain ⟨ip, scr, regs, p0, -, p8, q0, -, -⟩ := hc
  have hk3 : Src s L key (3 * L.pl + L.ql) := hk.take (by omega_arith)
  obtain ⟨ep, eq, eg, ey⟩ := key_kept hk3 (Kept.ofBody hL hb).out
  have B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hpo : pOf s₀.mem L key % 2 = 1 := hK.1.2.2
  have hxs : Src s L (off key (3 * L.pl + L.ql)) L.ql := hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_arith)
  have ex : xOf s.mem L key = xOf s₀.mem L key := by
    simp only [xOf]
    rw [((hk.keep rfl rfl).sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_arith)).kept (Kept.ofBody hL hb).out]
  unfold PrevalidatedSign.privateChecks
  -- The mask of `g^x mod p = y`.
  refine WP.seq (WP.mono (keyPair_ok (p := pOf s₀.mem L key) hL scr regs ip hk p0 B.1 hpo p8)
    fun s₁ ⟨⟨mx₁, ip₁, o₁, _, _, sav₁, _⟩, k₁⟩ => ?_)
  rw [eg, ey, ex] at mx₁
  have K₁ : Kept L s.mem s₁.mem := ⟨o₁.mono (Nat.zero_le _) (by omega_arith), sav₁⟩
  have q0₁ : arrQ s₁.mem L 0 = qOf s₀.mem L key := by
    rw [arrQ, arr, Outside.val32 (keepQ_of hL fun x hx => o₁ x (Or.inr (by omega_arith))) (by decide) (by decide)]
    exact q0
  -- `r28` at x, the mask into `r22`.
  refine WP.seq ?_
  unfold PrevalidatedSign.pointX
  rw [WP.block_append_iff]
  refine WP.mono (ptrX_ok (regs.keep k₁)) fun s₂ ⟨⟨a12, _, m2⟩, k₂⟩ => ?_
  have k₁₂ := k₁.trans k₂
  have h21 : s₂.gpr .r21 = L.S := (k₁₂.gpr .r21 (by decide)).trans regs.r21
  have hld : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .r21 + BitVec.ofNat 64 hMask) 8 := by
    rw [h21]; exact (scr.congr k₁₂.wr).ld (show hMask + 8 ≤ L.Z by simp only [hMask]; omega_arith)
  refine WP.mono (WP.keep [.r22, .r28] (Q := fun u => u.gpr .r28 = off key (3 * L.pl + L.ql) ∧
      u.gpr .r22 = word s₁.mem L.S hMask ∧ u.mem = s₂.mem)
    (by prun [a12, exec_ld (by decide) hld, BitVec.add_zero]; rw [h21, m2]) (by decide))
    fun s₃ ⟨⟨a28, a22, m3⟩, k₃⟩ => ?_
  have k₁₃ := k₁₂.trans k₃
  have hm3 : s₃.mem = s₁.mem := m3.trans m2
  have hr₃ : Regs s₃ L key (off key (3 * L.pl + L.ql)) 0 :=
    ⟨(k₁₃.gpr .r21 (by decide)).trans regs.r21, (k₁₃.gpr .r27 (by decide)).trans regs.r27, a28,
      (k₁₃.gpr .r26 (by decide)).trans regs.r26, by rw [k₁₃.gpr .r2 (by decide)]; exact regs.pl,
      by rw [k₁₃.gpr .r2 (by decide)]; exact regs.ql⟩
  -- The mask of `0 < x < q`.
  refine WP.seq (WP.mono (xRange_ok hL (scr.congr k₁₃.wr) hr₃ (hxs.keep k₁₃.rd k₁₃.wr) (a22.trans mx₁))
    fun s₄ ⟨⟨c20, _, qa₄⟩, k₄⟩ => ?_)
  have ek : kOf s₃.mem L (off key (3 * L.pl + L.ql)) = xOf s₀.mem L key := by
    rw [← ex]; simp only [kOf, xOf, hm3]; rw [hxs.kept K₁.out]
  rw [ek, hm3, q0₁] at c20
  have K₄ := K₁.trans (by rw [← hm3]; exact Kept.ofBody hL (qa₄.qbody.body hL))
  -- The result.
  refine WP.mono (WP.keep [.r0, .r3] (Q := fun u => u.gpr .r3 =
      BitVec.ofNat 64 (if (decide (gOf s₀.mem L key ^ xOf s₀.mem L key % pOf s₀.mem L key = yOf s₀.mem L key) &&
        decide (0 < xOf s₀.mem L key ∧ xOf s₀.mem L key < qOf s₀.mem L key)) then 1 else 0) ∧ u.mem = s₄.mem)
    (by prun [c20, mask_low]) (by decide)) fun t ⟨⟨t3, mt⟩, kt⟩ => ?_
  have kall := (k₁₃.trans k₄).trans kt
  refine ⟨⟨?_, by rw [mt]; exact K₄, (kall.gpr .r21 (by decide)).trans regs.r21, scr.congr kall.wr⟩,
    kall.mono (by decide)⟩
  rw [t3]
  refine congrArg (BitVec.ofNat 64) (ite_congr (propext ?_) (fun _ => rfl) fun _ => rfl)
  simp only [PrivOk, hK, true_and, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩

theorem validatePrivate_correct (s : State) (h : vpkContract.pre s) :
    ∃ tr t, Exec isa PrevalidatedSign.validate s tr t ∧ abiPreserved s t ∧ vpkContract.post s t := by
  show WP isa PrevalidatedSign.validate s fun t => abiPreserved s t ∧ vpkContract.post s t
  have hL := vpkContract_lay h
  have hZ := hL.z256
  obtain ⟨hrd, hwr, dKS, -, nw, hv, hkl, -⟩ := h
  have hplq : 3 * (playOf s).pl + 2 * (playOf s).ql = (s.gpr .r4).toNat := by simp only [playOf]; omega_using [hkl]
  have hspec : vpkRes s = decide (PrivOk s.mem (playOf s) (s.gpr .r3)) := by
    show Spec.Dsa.validatePrivateKeyBytes (playOf s).pl (playOf s).ql _ = _
    rw [← hplq]; exact validatePrivate_spec hv
  have src : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr →
      Src t (playOf s) (s.gpr .r3) (3 * (playOf s).pl + 2 * (playOf s).ql) :=
    fun hr hw => psrc_of hrd dKS (Nat.le_of_eq hplq) hr hw
  unfold PrevalidatedSign.validate
  refine WP.seq (WP.mono (pfront_ok_of hL hwr nw) fun s₁ ⟨⟨hr₁, scr₁, r2₁, sav₁, out₁⟩, k₁⟩ => ?_)
  have hwr' : ∀ u : State, ScrL u (playOf s) → ∀ i < 19, InRegions u.wr (off (savW (s.gpr .r7)) (8 * i)) 8 :=
    fun u hu i hi => by rw [← saveOff_eq]; exact hu.st (d := 104 + 8 * i) (by simp only [playOf] at hZ ⊢; omega_using [hZ, hi])
  have Out₁ : Outside (playOf s).S 0 (playOf s).Z s.mem s₁.mem :=
    out₁.mono (Nat.le_refl _) (by simp only [playOf] at hZ ⊢; omega_using [hZ])
  have hPs : PrivOk s₁.mem (playOf s) (s.gpr .r3) ↔ PrivOk s.mem (playOf s) (s.gpr .r3) := by
    obtain ⟨ep, eq, eg, ey⟩ := key_kept ((src rfl rfl).take (by omega_using [])) Out₁
    have ex : xOf s₁.mem (playOf s) (s.gpr .r3) = xOf s.mem (playOf s) (s.gpr .r3) := by
      simp only [xOf]
      rw [((src rfl rfl).sub (o := 3 * (playOf s).pl + (playOf s).ql) (k := (playOf s).ql) (by omega_using [])).kept Out₁]
    simp only [PrivOk, KeyOk, ep, eq, eg, ey, ex]
  refine WP.seq (checkKey_ok hL scr₁ hr₁ r2₁ (by decide) ((src k₁.rd k₁.wr).take (by omega_using []))
    (fun t hK hc hb kc => ?_) (fun t hn hb hrt scrt kc => ?_))
  · have kt := k₁.trans kc
    refine WP.mono (privateChecks_ok hL hK hc hb (src kt.rd kt.wr)) fun u ⟨⟨u3, Ku, h21u, scru⟩, ku⟩ => ?_
    refine WP.mono (finish_ok h21u (hwr' u scru)
      (fun i hi => (Ku.sav i hi).trans (((Kept.ofBody hL hb).sav i hi).trans (sav₁ i hi))) (kt.trans ku))
      fun w ⟨hab, w3⟩ => ⟨hab, ?_⟩
    show ((w.gpr .r3).setWidth 32).toNat = _
    rw [w3, u3, hspec]
    by_cases hp : PrivOk s.mem (playOf s) (s.gpr .r3)
    · rw [ite_eq_left (hPs.mpr hp), ite_eq_left (decide_eq_true hp)]; rfl
    · rw [ite_eq_right (fun hx => hp (hPs.mp hx)), ite_eq_right (by simpa using hp)]; rfl
  · refine WP.mono (WP.keep [.r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 0 ∧ u.mem = t.mem)
      (by prun) (by decide)) fun u ⟨⟨u3, um⟩, ku⟩ => ?_
    refine WP.mono (finish_ok ((ku.gpr .r21 (by decide)).trans hrt.r21) (hwr' u (scrt.congr ku.wr))
      (fun i hi => by rw [um]; exact ((Kept.ofBody hL hb).sav i hi).trans (sav₁ i hi)) ((k₁.trans kc).trans ku))
      fun w ⟨hab, w3⟩ => ⟨hab, ?_⟩
    show ((w.gpr .r3).setWidth 32).toNat = _
    have hnp : ¬ PrivOk s.mem (playOf s) (s.gpr .r3) := fun hx => hn (hPs.mpr hx).1
    rw [w3, u3, hspec, ite_eq_right (by simpa using hnp)]; rfl

end VG.Proof.Dsa.PPC64LE

end

end

/-!
# DSA private-key validation on PPC64LE: constant time

`validatePrivate_ct`: two runs from states that satisfy `vpkContract` and
agree on its public data (the arguments' registers, the key's public part
and the result) leak the same trace. The entry is
`vg_dsa_check_parameters`'s (`pentry_taint`, `pfront_S0_of`, for the public
data `vpkvdOf`: the key's public octets), the check of the key's public part
verification's (`checkKey_rel`), then `privateChecks`, which branches on
nothing (`privateChecks_rel`), and `restore`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE

/-- A call's public data: the layout and the key's public octets. -/
def vpkvdOf (s : State) : VD := pvdN (3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat) s

/-- On entry. -/
def VPK0 (v : VD) (s : State) : Prop := vpkContract.pre s ∧ vpkvdOf s = v

theorem vpkfront_S0 {v : VD} {s : State} (h : VPK0 v s) :
    WP isa (.block Params.entry) s fun t => S0 v t ∧ KY v := by
  obtain ⟨hp, rfl⟩ := h
  have hL := vpkContract_lay hp
  obtain ⟨hrd, hwr, dKS, -, nw, -, hkl, -⟩ := hp
  exact (pfront_S0_of hL hwr nw (fun hr hw => psrc_of hrd dKS (by omega_using [hkl]) hr hw)
    (by simp only [playOf]; omega_using [])).mono fun _ h => ⟨h, by simp only [KY, vpkvdOf, pvdN, playOf]; omega_using []⟩

/-- The checks of the key leave the P space's registers fixed. -/
theorem pins_K9P : Pins K9 (coreRegs ++ envRegs') := by
  intro v s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (pins_fixL _ _ fun _ => rfl : Pins K9 (coreRegs ++ [])) v s₁ s₂ h₁ h₂ r (List.mem_append_left _ hr)
  · rw [show envRegs' = (envP v).map Prod.fst from rfl] at hr
    obtain ⟨p, hm, rfl⟩ := List.mem_map.mp hr
    rw [envP_of h₁.2.2.2.1.1 p hm, envP_of h₂.2.2.2.1.1 p hm]

theorem privateChecks_rel : RelCT isa (Two K9) PrevalidatedSign.privateChecks (Two End) :=
  rel_end (two_taintR _ pins_K9P (by taint_decide_rel)) (fun _ _ h => h.1.regs.r21)
    (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem validatePrivate_rel : RelCT isa (Two VPK0) PrevalidatedSign.validate fun _ _ => True := by
  unfold PrevalidatedSign.validate
  exact RelCT.seq (two_post (pentry_taint (pins_pvd fun _ _ h => h.2)) fun _ _ h => vpkfront_S0 h)
    (RelCT.seq (checkKey_rel privateChecks_rel) (two_taint _ pins_End (by taint_decide)))

/-- Runs that agree on the contract's public data have the same public data `vpkvdOf`. -/
theorem vpkvdOf_eq {s t : State} (hs : vpkContract.pre s) (hp : vpkContract.pub s t) : vpkvdOf s = vpkvdOf t := by
  obtain ⟨-, h3, h4, h5, h6, h7, h8, hl⟩ := hp
  have hk := hs.2.2.2.2.2.2.1
  obtain ⟨e, -⟩ := List.append_inj' hl rfl
  simp only [Spec.Dsa.publicBytesLeak, bytesAt_take] at e
  have e := map_toNat_inj e
  rw [← h3, ← h4, ← h5, ← h6, Nat.min_eq_right (by omega_using [hk])] at e
  simp only [vpkvdOf, pvdN, playOf, ← h3, ← h5, ← h6, ← h7, ← h8, e]

theorem validatePrivate_ct : ConstantTime isa vpkContract.pre vpkContract.pub PrevalidatedSign.validate :=
  RelCT.constantTime (validatePrivate_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vpkvdOf s, ⟨hs, rfl⟩, ⟨ht, (vpkvdOf_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.PPC64LE

end

end

/-!
# `vg_dsa_validate_private_key` on PPC64LE: verified against the shared contract

`vpkContract` states the shared contract on the registers
(`validatePrivate_implies`); with correctness (`validatePrivate_correct`) and
constant time (`validatePrivate_ct`), `PrevalidatedSign.validate` is verified
(`validatePrivate_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- A state meeting `vpkContract.pre`: 1024-bit p and 160-bit q, the key at
`0x1000` and the working space at `0x10000`. -/
def validatePrivateSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 424 | .r5 => 128 | .r6 => 20 | .r7 => 0x10000 | .r8 => 2048 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 424⟩]
  wr := [⟨0x10000, 16384⟩]

theorem validatePrivate_implies : vpkContract.Implies (Spec.Dsa.validatePrivateKeyContract abi) := by
  sig_implies [Spec.Dsa.validatePrivateKeyContract, Spec.Dsa.validatePrivateKeySig, abi, argRegs, vpkContract,
    vpkRes, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append]
    [validatePrivateSatState] using validatePrivateSatState

/-- `vg_dsa_validate_private_key`. -/
theorem validatePrivate_verified :
    Verified target PrevalidatedSign.validate (Spec.Dsa.validatePrivateKeyContract abi) :=
  Verified.of_correct validatePrivate_correct validatePrivate_ct validatePrivate_implies

end VG.Proof.Dsa.PPC64LE
