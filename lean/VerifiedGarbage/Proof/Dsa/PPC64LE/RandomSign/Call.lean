module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Sampler
public import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Save
public import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Setup
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Body
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFn
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite

/-! ### `Dsa.PPC64LE.PrevalidatedSign.Fn`, which this module and modules that import it used -/

section

/-!
# DSA prevalidated signing on PPC64LE: the function

`psign_correct`: `vg_dsa_sign_prevalidated` meets `spContract`. The key
passes validation (`validatePrivate_spec`), so after `Sign.entry`
(`sfront_ok`), `Prevalidated.setup` leaves what `checkKey` would
(`setup_ok`), `Sign.body` signs (`sbody_ok`, with `g^x mod p = y`), and
`restore` gives back the nonvolatile registers (`sfinish_ok`); the result is
the specification's by `Proof/Dsa/Accepted.lean`'s `signBytes_compute`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE
open VG.Impl.Dsa.PPC64LE.Sign (hOut)

theorem psign_correct (s : State) (h' : spContract.pre s) :
    ∃ tr t, Exec isa PrevalidatedSign.sign s tr t ∧ abiPreserved s t ∧ spContract.post s t := by
  show WP isa PrevalidatedSign.sign s fun t => abiPreserved s t ∧ sContract.post s t
  obtain ⟨h, hval⟩ := h'
  have hL := slayOf_ok h
  have hZ := hL.z256
  have hql := hL.ql
  have hpre := h
  obtain ⟨-, hrd, hwr, -, -, -, dOS, -, dKS, dNS, dDS, -, nwO, nwK, nwN, nwD, -, hv, hol, hkl, -⟩ := h
  have mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd ++ s.wr →
      (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (slayOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact hm,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩, fun i hi => Pub.ne_of_disjoint hd (by omega_arith) i (by omega_arith)⟩
  have h4 : (s.gpr .r4).toNat = 2 * (slayOf s).ql := hol
  have h6 : (s.gpr .r6).toNat = 3 * (slayOf s).pl + 2 * (slayOf s).ql := hkl
  have srcK := mkSrc (A := s.gpr .r5) (k := 3 * (slayOf s).pl + 2 * (slayOf s).ql)
    (List.mem_append_left _ (by rw [hrd]; simp)) dKS nwK (s.gpr .r6).isLt (by omega_arith)
  have srcK3 : ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (slayOf s) (s.gpr .r5) (3 * (slayOf s).pl + (slayOf s).ql) :=
    fun t hr hw => (srcK t hr hw).take (by omega_arith)
  have srcN := mkSrc (A := s.gpr .r8) (k := (slayOf s).ql) (List.mem_append_left _ (by rw [hrd]; simp)) dNS nwN
    (s.gpr .r9).isLt (Nat.le_refl _)
  have srcD := mkSrc (A := s.gpr .r10) (k := (stackArg s 0).toNat) (List.mem_append_left _ (by rw [hrd]; simp))
    dDS nwD (stackArg s 0).isLt (Nat.le_refl _)
  have srcO := mkSrc (A := s.gpr .r3) (k := 2 * (slayOf s).ql) (List.mem_append_right _ (by rw [hwr]; simp)) dOS nwO
    (s.gpr .r4).isLt (by omega_arith)
  have scrO : ∀ t : State, t.wr = s.wr → Scr t (s.gpr .r3) (2 * (slayOf s).ql) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr, ← h4]; simp) (by omega_arith)
  -- A change in `out` keeps the saved registers.
  have outSep : ∀ {m m' : Mem}, Outside (s.gpr .r3) 0 (2 * (slayOf s).ql) m m' → ∀ i < 19,
      word m' (slayOf s).S (saveOff i) = word m (slayOf s).S (saveOff i) := fun ho i hi =>
    Outside.word_sep (Zp := 2 * (slayOf s).ql) ho (fun x hx => by
        by_contra hc
        exact (srcO s rfl rfl).sep (VG.Proof.Bignum.ofs (s.gpr .r3) x)
          (by simp only [VG.Proof.Bignum.ofs] at hc ⊢; omega_arith) x hx (off_ofs _ x))
      (by omega_arith) (by simp only [saveOff]; omega_arith) hL.nowrap
  -- The specification's values.
  have hkey : Spec.Dsa.privateKeyBytes (s.gpr .r7).toNat (s.gpr .r9).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) =
      ⟨⟨pOf s.mem (slayOf s) (s.gpr .r5), qOf s.mem (slayOf s) (s.gpr .r5), gOf s.mem (slayOf s) (s.gpr .r5)⟩,
        yOf s.mem (slayOf s) (s.gpr .r5), some (xOf s.mem (slayOf s) (s.gpr .r5))⟩ := by
    rw [VG.Proof.Dsa.privateKeyBytes_at s.mem (s.gpr .r5) (by simp only [slayOf] at h6; omega_arith),
      VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .r5) (by simp only [slayOf] at h6; omega_arith)]
    rfl
  have hspec : ∀ {n : Nat}, VG.Proof.Dsa.shapeValid (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5)) →
      Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) = 8 * n →
      sRes s = if VG.Proof.Dsa.publicChecks (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5))
            (gOf s.mem (slayOf s) (s.gpr .r5)) (yOf s.mem (slayOf s) (s.gpr .r5)) ∧
          SignOk (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5))
            (gOf s.mem (slayOf s) (s.gpr .r5)) (yOf s.mem (slayOf s) (s.gpr .r5))
            (xOf s.mem (slayOf s) (s.gpr .r5)) (kOf s.mem (slayOf s) (s.gpr .r8))
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (min (stackArg s 0).toNat n)))
        then some (Spec.Dsa.encodeBE (slayOf s).ql (sigR (pOf s.mem (slayOf s) (s.gpr .r5))
              (qOf s.mem (slayOf s) (s.gpr .r5)) (gOf s.mem (slayOf s) (s.gpr .r5)) (kOf s.mem (slayOf s) (s.gpr .r8))) ++
            Spec.Dsa.encodeBE (slayOf s).ql (sigS (qOf s.mem (slayOf s) (s.gpr .r5)) (xOf s.mem (slayOf s) (s.gpr .r5))
              (kOf s.mem (slayOf s) (s.gpr .r8))
              (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (min (stackArg s 0).toNat n)))
              (sigR (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5))
                (gOf s.mem (slayOf s) (s.gpr .r5)) (kOf s.mem (slayOf s) (s.gpr .r8)))))
        else none := fun {n} hs hq8 => by
    have hc := VG.Proof.Dsa.signBytes_compute (n := n) (k := kOf s.mem (slayOf s) (s.gpr .r8))
      (nonce := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (digest := Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat) hv hs
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact h6) (VG.Proof.Bignum.bytesAt_length _ _ _) hkey rfl hq8
    dsimp only at hc
    unfold sRes
    rw [hc, bytesAt_take]
    rfl
  have hP : PrivOk s.mem (slayOf s) (s.gpr .r5) := by
    have e := validatePrivate_spec (m := s.mem) (L := slayOf s) (key := s.gpr .r5) hv
    rw [show 3 * (slayOf s).pl + 2 * (slayOf s).ql = (s.gpr .r6).toNat from h6.symm] at e
    exact of_decide_eq_true (e.symm.trans hval)
  unfold PrevalidatedSign.sign
  refine WP.seq (WP.mono (sfront_ok hpre) fun s₁ ⟨⟨hr₁, scr₁, r2₁, hout₁, sav₁, out₁⟩, k₁⟩ => ?_)
  have hwr' : ∀ u : State, ScrL u (slayOf s) → ∀ i < 19, InRegions u.wr (off (savW (stackArg s 1)) (8 * i)) 8 :=
    fun u hu i hi => by
      rw [← saveOff_eq]; exact hu.st (d := 104 + 8 * i) (by simp only [slayOf] at hZ ⊢; omega_arith)
  have Out₁ : Outside (slayOf s).S 0 (slayOf s).Z s.mem s₁.mem :=
    out₁.mono (Nat.le_refl _) (by simp only [slayOf] at hZ ⊢; omega_arith)
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := key_kept (srcK3 s rfl rfl) Out₁
  have hKs : KeyOk s₁.mem (slayOf s) (s.gpr .r5) ↔ KeyOk s.mem (slayOf s) (s.gpr .r5) := by
    simp only [KeyOk, ep₁, eq₁, eg₁, ey₁]
  refine WP.seq (setup_ok hL scr₁ hr₁ r2₁ (by omega_arith) (srcK3 s₁ k₁.rd k₁.wr) (hKs.mpr hP.1)
    fun t hK hc Bd kc => ?_)
  have kt := k₁.trans kc
  have Kd := Kept.ofBody hL Bd
  have hKt := hKs.mp hK
  have Ot : Outside (slayOf s).S 0 (slayOf s).Z s.mem t.mem := Out₁.trans Kd.out
  have hq8 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) =
      8 * (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) := by
    have := hKt.1.1; unfold Spec.Dsa.supportedSizes at this; omega_arith
  have hn32 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8 ≤ 32 := by
    have := hKt.1.1; unfold Spec.Dsa.supportedSizes at this; omega_arith
  have ex : xOf t.mem (slayOf s) (s.gpr .r5) = xOf s.mem (slayOf s) (s.gpr .r5) := by
    simp only [xOf]
    rw [((srcK s rfl rfl).sub (o := 3 * (slayOf s).pl + (slayOf s).ql) (k := (slayOf s).ql) (by omega_arith)).kept Ot]
  have hgx : gOf s₁.mem (slayOf s) (s.gpr .r5) ^ xOf t.mem (slayOf s) (s.gpr .r5) % pOf s₁.mem (slayOf s) (s.gpr .r5) =
      yOf s₁.mem (slayOf s) (s.gpr .r5) := by
    rw [ep₁, eg₁, ey₁, ex]; exact hP.2.2
  refine WP.mono (sbody_ok hL hK hgx hc Kd (srcK t kt.rd kt.wr) (srcN t kt.rd kt.wr) (by omega_arith)
    ((srcD t kt.rd kt.wr).take (Nat.min_le_left _ _)) ((Body.hOut Bd).trans hout₁) (scrO t kt.wr)
    (srcO t kt.rd kt.wr)) fun u ⟨⟨ob, r3u, ⟨m, Km, Om⟩, h21u, scru⟩, ku⟩ => ?_
  refine WP.mono (sfinish_ok h21u (hwr' u scru)
    (fun i hi => ((outSep Om i hi).trans (Km.sav i hi)).trans ((Kd.sav i hi).trans (sav₁ i hi)))
    (kt.trans ku)) fun w ⟨hab, w3, wm⟩ => ⟨hab, ?_⟩
  have ek : kOf t.mem (slayOf s) (s.gpr .r8) = kOf s.mem (slayOf s) (s.gpr .r8) := by
    simp only [kOf]; rw [(srcN s rfl rfl).kept Ot]
  rw [ep₁, eq₁, eg₁, ey₁, ex, ek] at ob r3u
  have ed : Spec.Rsa.bytesAt t.mem (s.gpr .r10)
      (min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8)) =
      Spec.Rsa.bytesAt s.mem (s.gpr .r10)
        (min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8)) := by
    rw [show min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) =
      min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) by omega_arith]
    exact ((srcD s rfl rfl).take (Nat.min_le_left _ _)).kept Ot
  rw [ed] at ob r3u
  have hres := hspec hKt.1 hq8
  simp only [hKt.2, true_and] at hres
  refine ⟨?_, ?_⟩
  · show ((w.gpr .r3).setWidth 32).toNat = _
    rw [w3, r3u, ret_ofNat, hres, signStatus_ite]
  · rw [wm, h4, ob, hres]
    split <;> rfl

end VG.Proof.Dsa.PPC64LE

end

end

/-!
# Randomized DSA signing on PPC64LE: the call of `vg_dsa_sign_prevalidated`

`callArgs` passes `out`, the key, the nonce (in the frame) and the digest,
with their lengths, and the frame holds the arguments on the stack
(`digest_len`, `scratch`, `scratch_len`), so `vg_dsa_sign_prevalidated`'s
contract on the registers (`spContract`) holds, with the regions it is given
(`signRd`, `signWr`): the key, which the frame keeps, passes validation as
on entry. `sign_ok` runs the call by `WP.call` from `psign_correct`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd

/-- The regions `vg_dsa_sign_prevalidated` may read. -/
abbrev signRd (L : RL) : List Region :=
  [L.keyR, ⟨off L.F oNonce, L.ql⟩, L.digR, ⟨off L.F oArgs, 24⟩]

/-- The regions `vg_dsa_sign_prevalidated` may write. -/
abbrev signWr (L : RL) : List Region := [L.outR, L.scrR]

/-- The registers `callArgs` writes. -/
def argRegs' : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- The state after `callArgs`. -/
structure Args (L : RL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r3 : t.gpr .r3 = L.out
  r4 : t.gpr .r4 = BitVec.ofNat 64 (2 * L.ql)
  r5 : t.gpr .r5 = L.key
  r6 : t.gpr .r6 = BitVec.ofNat 64 L.kl
  r7 : t.gpr .r7 = BitVec.ofNat 64 L.pl
  r8 : t.gpr .r8 = off L.F oNonce
  r9 : t.gpr .r9 = BitVec.ofNat 64 L.ql
  r10 : t.gpr .r10 = L.dig

theorem callArgs_ok {L : RL} {s₀ t : State} (hL : L.Ok) (hc : Ctx L s₀ t) :
    WP isa (.block callArgs) t fun t' => Args L s₀ t' ∧ t'.mem = t.mem ∧ Keep argRegs' t t' := by
  have hp := hL.pl
  have hq := hL.ql
  have hdis : ∀ r ∈ ctxRegs, r ∉ argRegs' := by decide
  refine WP.mono (WP.keep argRegs' (Q := fun t' => t'.gpr .r3 = L.out ∧ t'.gpr .r4 = BitVec.ofNat 64 (2 * L.ql) ∧
    t'.gpr .r5 = L.key ∧ t'.gpr .r6 = BitVec.ofNat 64 L.kl ∧ t'.gpr .r7 = BitVec.ofNat 64 L.pl ∧
    t'.gpr .r8 = off L.F oNonce ∧ t'.gpr .r9 = BitVec.ofNat 64 L.ql ∧ t'.gpr .r10 = L.dig ∧ t'.mem = t.mem)
    ?_ (by decide)) fun t' ⟨⟨a3, a4, a5, a6, a7, a8, a9, a10, am⟩, k⟩ =>
      ⟨⟨hc.step hL k.sp k.rd k.wr (fun r hr => k.gpr r (hdis r hr)) (by rw [am]; exact Frame.refl _ _),
        a3, a4, a5, a6, a7, a8, a9, a10⟩, am, k⟩
  unfold callArgs
  prun [hc.r18, hc.r19, hc.r20, hc.r21, hc.r22, hc.sp, exec_addSp (show oNonce < 2 ^ 15 by decide), add0,
    ← BitVec.ofNat_add]
  refine ⟨by congr 1; omega_using [], by simp only [RL.kl]; congr 1; omega_using []⟩

/-- The arguments' values in the state `vg_dsa_sign_prevalidated` is entered in. -/
theorem entry_gpr (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := State.callEntry_gpr t h

theorem entry_stackArg (t : State) (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (t.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 := rfl

/-- The signature `vg_dsa_sign_prevalidated` computes from the state `t` it is called in. -/
abbrev sresOf (L : RL) (m : Mem) : Option (List Byte) :=
  Spec.Dsa.signBytes L.pl L.ql (Spec.Rsa.bytesAt m L.key L.kl) (Spec.Rsa.bytesAt m (off L.F oNonce) L.ql)
    (Spec.Rsa.bytesAt m L.dig L.dl)

/-- `vg_dsa_sign`'s contract on the registers holds when it is called. -/
theorem sign_pre' {s₀ t : State} (h : rsContract.pre s₀) (ha : Args (rlOf s₀) s₀ t) :
    sContract.pre (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) := by
  have hL := rlOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  have hF := hL.fnw
  have hsw := hL.sw
  have hk := hL.nwKey
  simp only [frameBytes] at hF
  have g3 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r3) (by decide)).trans ha.r3
  have g4 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r4) (by decide)).trans ha.r4
  have g5 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r5) (by decide)).trans ha.r5
  have g6 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r6) (by decide)).trans ha.r6
  have g7 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r7) (by decide)).trans ha.r7
  have g8 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r8) (by decide)).trans ha.r8
  have g9 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r9) (by decide)).trans ha.r9
  have g10 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r10) (by decide)).trans ha.r10
  have sa0 : stackArg (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) 0 =
      BitVec.ofNat 64 (rlOf s₀).dl := by rw [entry_stackArg, hc.sp]; exact hc.a0
  have sa1 : stackArg (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) 1 = (rlOf s₀).scr := by
    rw [entry_stackArg, hc.sp]; exact hc.a1
  have sa2 : stackArg (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) 2 =
      BitVec.ofNat 64 (rlOf s₀).sl := by rw [entry_stackArg, hc.sp]; exact hc.a2
  have ssp : (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).sp = (rlOf s₀).F := hc.sp
  have sargs : sStackArgs (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) =
      ⟨off (rlOf s₀).F oArgs, 24⟩ := by
    simp only [sStackArgs, stackArgAddr, ssp]; rfl
  have tn : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n hn => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hdl := hL.dl
  have hsl := hL.sl
  have ekl : (rlOf s₀).kl = 3 * (rlOf s₀).pl + 2 * (rlOf s₀).ql := rfl
  have nwN : (off (rlOf s₀).F oNonce).toNat + (rlOf s₀).ql ≤ 2 ^ 64 := by
    rw [off, BitVec.toNat_add, tn _ (by decide), Nat.mod_eq_of_lt (by simp only [oNonce]; omega_using [hF])]
    simp only [oNonce]; omega_using [hq, hF]
  unfold sContract
  dsimp only
  rw [g3, g4, g5, g6, g7, g8, g9, g10, sa0, sa1, sa2, sargs, ssp, tn (2 * (rlOf s₀).ql) (by omega_using [hq]),
    tn (rlOf s₀).kl (by omega_using [hp, hq, ekl]), tn (rlOf s₀).ql (by omega_using [hq]), tn (rlOf s₀).pl (by omega_using [hp]), tn _ hdl, tn _ hsl]
  refine ⟨by omega_using [hF], rfl, rfl, hL.dOK, ?_, hL.dOD, hL.dOS, ?_, hL.dKS, ?_, hL.dDS, ?_, hL.nwOut, hk, nwN, hL.nwDig,
    hL.nwScr, hL.lv, by omega_using [], by omega_using [ekl], by simp only [Spec.Dsa.scratchWords]; omega_using [hsw]⟩
  · exact (RL.Ok.frame_disj (d := oNonce) (n := (rlOf s₀).ql) hL.dFO (by simp only [oNonce, frameBytes]; omega_using [hq])).symm
  · exact (RL.Ok.frame_disj (d := oArgs) (n := 24) hL.dFO (by decide)).symm
  · exact RL.Ok.frame_disj (d := oNonce) (n := (rlOf s₀).ql) hL.dFS (by simp only [oNonce, frameBytes]; omega_using [hq])
  · exact (RL.Ok.frame_disj (d := oArgs) (n := 24) hL.dFS (by decide)).symm

/-- The key passes validation, on entry. -/
theorem rs_valid {s₀ : State} (h : rsContract.pre s₀) :
    Spec.Dsa.validatePrivateKeyBytes (rlOf s₀).pl (rlOf s₀).ql
      (Spec.Rsa.bytesAt s₀.mem (rlOf s₀).key (rlOf s₀).kl) = true := by
  have hkl : (rlOf s₀).kl = (s₀.gpr .r7).toNat := by
    have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    simp only [RL.kl, rlOf]; omega_using [this]
  rw [hkl]
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- `vg_dsa_sign_prevalidated`'s contract on the registers holds when it is called. -/
theorem sign_pre {s₀ t : State} (h : rsContract.pre s₀) (ha : Args (rlOf s₀) s₀ t) :
    spContract.pre (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) := by
  refine ⟨sign_pre' h ha, ?_⟩
  have hL := rlOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) hr
  simp only [State.withRegions_mem, State.callEntry_mem]
  rw [g .r5 (by decide), g .r6 (by decide), g .r7 (by decide), g .r9 (by decide), ha.r5, ha.r6, ha.r7, ha.r9]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (rlOf s₀).pl) (by omega_using [hp]), Nat.mod_eq_of_lt (a := (rlOf s₀).ql) (by omega_using [hq]),
    Nat.mod_eq_of_lt (a := (rlOf s₀).kl) (by simp only [RL.kl]; omega_using [hp, hq]), ha.ctx.key]
  exact rs_valid h

/-- What the call leaves. -/
structure Signed (L : RL) (s₀ : State) (t t' : State) : Prop where
  ctx : Ctx L s₀ t'
  pres : ∀ r ∈ preserved, t'.gpr r = t.gpr r
  frame : Frame (signWr L) t.mem t'.mem
  r3 : ((t'.gpr .r3).setWidth 32).toNat = Spec.Dsa.signStatus (sresOf L t.mem)
  out : Spec.Rsa.bytesAt t'.mem L.out (2 * L.ql) = (sresOf L t.mem).getD (List.replicate (2 * L.ql) 0)

/-- The regions given to `vg_dsa_sign_prevalidated` are within the caller's. -/
theorem sign_cov {s₀ t : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) :
    Covers (signRd (rlOf s₀) ++ signWr (rlOf s₀)) (t.rd ++ t.wr) ∧ Covers (signWr (rlOf s₀)) t.wr := by
  have hL := rlOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hrd, hwr⟩ := regions_eq h
  have inF : ∀ d n, 32 ≤ d → d + n ≤ frameBytes → InRegions (t.rd ++ t.wr) (off (rlOf s₀).F d) n := fun d n h₁ h₂ =>
    ⟨_, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), frameR_contains hL rfl h₁ h₂⟩
  have hcov : Covers (signRd (rlOf s₀) ++ signWr (rlOf s₀)) (t.rd ++ t.wr) := by
    refine VG.Covers.of_forall fun r hr => ?_
    simp only [signRd, signWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_left _ (by rw [hc.rd, hrd]; exact List.mem_cons_self ..)
    · exact VG.Covers.one (inF _ _ (by decide) (by simp only [oNonce, frameBytes]; omega_using [hq]))
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_left _ (by rw [hc.rd, hrd]; simp)
    · exact VG.Covers.one (inF _ _ (by decide) (by decide))
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
  have hcovw : Covers (signWr (rlOf s₀)) t.wr := VG.Covers.of_mem fun r hr => by
    rw [hc.wr, hwr]
    simp only [signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  exact ⟨hcov, hcovw⟩

/-- The result `vg_dsa_sign_prevalidated` computes, from the state the call enters. -/
theorem sres_eq {s₀ t : State} (h : rsContract.pre s₀) (ha : Args (rlOf s₀) s₀ t) :
    sRes (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) = sresOf (rlOf s₀) t.mem := by
  have hL := rlOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) hr
  have hdl := hL.dl
  simp only [sRes, State.withRegions_mem, State.callEntry_mem]
  rw [g .r5 (by decide), g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), g .r9 (by decide),
    g .r10 (by decide), ha.r5, ha.r6, ha.r7, ha.r8, ha.r9, ha.r10, entry_stackArg, hc.sp]
  have a0' : t.mem.readW ((rlOf s₀).F + BitVec.ofNat 64 (32 + 8 * (8 + 0))) 64 = BitVec.ofNat 64 (rlOf s₀).dl := hc.a0
  rw [a0']
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (rlOf s₀).pl) (by omega_using [hp]), Nat.mod_eq_of_lt (a := (rlOf s₀).ql) (by omega_using [hq]),
    Nat.mod_eq_of_lt (a := (rlOf s₀).kl) (by simp only [RL.kl]; omega_using [hp, hq]), Nat.mod_eq_of_lt hdl]

theorem sign_ok {s₀ t : State} (h : rsContract.pre s₀) (ha : Args (rlOf s₀) s₀ t) :
    WP isa (.call "vg_dsa_sign_prevalidated" Impl.Dsa.PPC64LE.PrevalidatedSign.sign) t (Signed (rlOf s₀) s₀ t) := by
  have hL := rlOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hcov, hcovw⟩ := sign_cov h hc
  refine WP.call (k := spContract) psign_correct (sign_pre h ha) hcov hcovw
    fun t' hrd' hwr' hsp' hf hpres _ hpost => ?_
  have hdis : ∀ r ∈ ctxRegs, r ∈ preserved := by decide
  obtain ⟨p3, pout⟩ := hpost
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) hr
  have es := sres_eq h ha
  rw [es] at p3 pout
  refine ⟨hc.step hL hsp' hrd' hwr' (fun r hr => hpres r (hdis r hr)) (hf.mono (by simp)), hpres, hf, p3, ?_⟩
  simp only [State.withRegions_mem, State.withRegions_gpr] at pout
  rw [State.callEntry_gpr t (r := .r3) (by decide), State.callEntry_gpr t (r := .r4) (by decide), ha.r3, ha.r4,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 * (rlOf s₀).ql) (by omega_using [hq])] at pout
  exact pout

end VG.Proof.Dsa.PPC64LE.RS
