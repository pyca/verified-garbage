module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Loop
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Wide

/-!
# Deterministic ECDSA on PPC64LE: the whole signature

Steps a–g: `h = bits2octets(digest)`, `V = 0x01…`, `K = 0x00…` (`stageA_ok`),
then the two keys and `V`s (`stageB_ok`, `stageC_ok`) and the number of
candidates: `K` and `V` are RFC 6979's (`kv0_eq`), and the loop runs
(`rest_ok`). The candidate the loop stops at has RFC 6979's signature
(`result_eq`), and it stops after the candidates RFC 6979 counts, or after
all of them if `d` is invalid (`exitAt`, `go_iff`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp wp_step)
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB hashToInt_takeQ bits2octets_eqQ rlenQ toBytes_ofBytes
  searchB_ok searchB_fail searchB_pos searchB_shift)

variable {P : Rfc} {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-! ## Steps a–g -/

/-- `h`, RFC 6979's `bits2octets` of the digest, and the private key's bytes. -/
abbrev hSpec (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.C (hBOf P L m₀)
abbrev dB (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d L.q

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_q (hq : L.q = P.c.len) : Spec.Ecdsa.Rfc6979.rlen P.C = L.q := by
  cases hw : L.wide
  · exact rlenQ (narrow_q hq hw).2.2.2
  · obtain ⟨hq66, -, -, hB⟩ := wide_q hq hw
    exact rlenR (by omega) (by omega)

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (hq : L.q = P.c.len) :
    kv0 P L m₀ =
      let K₁ := Spec.Hmac.hmac P.Hf (List.replicate P.I.hashLen 0)
        (List.replicate P.I.hashLen 1 ++ BitVec.ofNat 8 0 :: (dB P L m₀ ++ hSpec P L m₀))
      let V₁ := Spec.Hmac.hmac P.Hf K₁ (List.replicate P.I.hashLen 1)
      let K₂ := Spec.Hmac.hmac P.Hf K₁ (V₁ ++ BitVec.ofNat 8 1 :: (dB P L m₀ ++ hSpec P L m₀))
      (K₂, Spec.Hmac.hmac P.Hf K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets P.C (xOf P L m₀) = dB P L m₀ := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_q hq,
      show L.q = (dB P L m₀).length from (Proof.Hmac.Common.bytesAt_length _ _ _).symm, toBytes_ofBytes]
  simp only [kv0, Spec.Ecdsa.Rfc6979.init, hi]
  rfl

theorem mul_pow_lt {x a b c : Nat} (hx : x < 2 ^ a) (h : a + b ≤ c) : x * 2 ^ b < 2 ^ c :=
  calc x * 2 ^ b < 2 ^ a * 2 ^ b := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos _)
    _ = 2 ^ (a + b) := (Nat.pow_add _ _ _).symm
    _ ≤ 2 ^ c := Nat.pow_le_pow_right (by omega) h

/-- Unless `wide`, `core` reads the digest itself, whose leftmost `Q` bytes
are the integer. -/
theorem dgOk_narrow (hL : L.Ok) (hq : L.q = P.c.len) (hw : L.wide = false) {u : State} (hc : Ctx L g lr m₀ u) :
    DgOk P L m₀ u.mem := by
  obtain ⟨-, -, hqd, hB⟩ := narrow_q hq hw
  unfold DgOk
  simp only [dgAddr, hw, Bool.false_eq_true, ite_false, eOf, hBOf]
  rw [hc.dgBytes hL hqd, hashToInt_takeQ hB (by rw [Proof.Hmac.Common.bytesAt_length]),
    List.take_of_length_le (by rw [Proof.Hmac.Common.bytesAt_length]),
    hashToInt_takeQ hB (by rw [Proof.Hmac.Common.bytesAt_length]; exact hqd), ← bytesAt_take _ _ hqd]

/-- After step d: `h` as the messages of steps d and f have it, `V = 0x01…`,
`K = 0x00…`, and the digest `core` reads. -/
structure QA (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : tailOf P.K L u.mem = hSpec P L m₀
  k : keyOf P.K L u.mem = List.replicate P.I.hashLen 0
  v : vOf P.K L u.mem = List.replicate P.I.hashLen 1
  dg : DgOk P L m₀ u.mem

theorem stageA_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa P.c.start t fun u => Ctx L g lr m₀ u ∧ QA P L m₀ u := by
  have hnB := hL.nB
  cases hw : L.wide
  · have hcw : P.c.wide = false := (wideL hq).symm.trans hw
    obtain ⟨-, -, hqd, hB⟩ := narrow_q hq hw
    have hq4 : 4 * P.k = L.q := by rw [hq, P.hk hcw]
    simp only [Cfg.start, hcw, Bool.false_eq_true, ite_false]
    rw [WP.block_append_iff]
    have hok := lq_ok hq hw
    refine WP.mono (reduce_ok hL (P.hk hcw) (P.hk16 hcw) (by rw [hq4]; exact hqd) (by rw [P.hk hcw, ← hq4])
      P.hcD hok (P.hn₁ hcw) (P.hn₂ hcw) hc) fun u ⟨hcu, _, hr⟩ => ?_
    refine WP.mono (initKV_ok hL hcu) fun v ⟨hcv, hf, hkv⟩ => ⟨hcv, ?_, ?_, ?_, dgOk_narrow hL hq hw hcv⟩
    · have ⟨hq₁, hq₂⟩ := hok
      have hne := hcu.ne
      have hh : hOf L v.mem = hOf L u.mem := bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega)
      simp only [tailOf, hw, Bool.false_eq_true, ite_false]
      rw [hh, hSpec, bits2octets_eqQ hB (by rw [Proof.Hmac.Common.bytesAt_length]; exact hqd),
        ← bytesAt_take _ _ hqd, P.hcn.symm, ← hq4, ← hr]
      rw [hq4]
      have e := toBytes_ofBytes (hOf L u.mem)
      rw [Proof.Hmac.Common.bytesAt_length] at e
      exact e.symm
    · exact (hkv P.K.H.D P.K.hH.hD64).2.trans (by rw [P.hD])
    · exact (hkv P.K.H.D P.K.hH.hD64).1.trans (by rw [P.hD])
  · have hcw : P.c.wide = true := (wideL hq).symm.trans hw
    obtain ⟨hq66, hD64, he, hB⟩ := wide_q hq hw
    obtain ⟨hcD, hcl, -⟩ := P.hW hcw
    have hKD : P.K.H.D = 64 := by rw [← P.hD, hD64]
    have e64 : Spec.Sha256.bytesAt m₀ L.dg P.I.hashLen = Spec.Sha256.bytesAt m₀ L.dg 64 := congrArg _ hD64
    have hn0 : P.C.n ≠ 0 := fun h => by
      simp only [Spec.Ecdsa.nBits, h] at hB; exact absurd hB (by decide)
    simp only [Cfg.start, hcw, ite_true]
    refine WP.seq (WP.mono (coreDigest_ok hL hcl hcD (P.hcw hcw) (P.hsh hcw) he (by omega) hc) fun u ⟨hcu, _, hx⟩ => ?_)
    refine WP.mono (initKV_ok hL hcu) fun v ⟨hcv, hf, hkv⟩ => ⟨hcv, ?_, ?_, ?_, ?_⟩
    · simp only [tailOf, hw, ite_true]
      rw [hcv.dgBytes hL (by rw [P.hD]), hSpec, bits2octets_short (R := 66) (by omega) (by omega)
        (by rw [hBOf, Proof.Hmac.Common.bytesAt_length]; omega) hn0, hBOf, Proof.Hmac.Common.bytesAt_length,
        hq66, hKD, e64, show 66 - P.I.hashLen = 66 - 64 by omega]
    · exact (hkv P.K.H.D P.K.hH.hD64).2.trans (by rw [P.hD])
    · exact (hkv P.K.H.D P.K.hH.hD64).1.trans (by rw [P.hD])
    · -- `core`'s digest: the digest's number `e`, shifted left by 7 bits.
      have hX : Spec.Sha256.bytesAt v.mem (L.B + BitVec.ofNat 64 352) 66 = Spec.Weierstrass.toBytes 66
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg 64) * 2 ^ 7) := by
        rw [bytesAt_frame hf (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
            (by omega), hx, hc.dgBytes hL (by omega)]
      have h64 := ofBytes_lt (Spec.Sha256.bytesAt m₀ L.dg 64)
      rw [Proof.Hmac.Common.bytesAt_length] at h64
      have hlt := mul_pow_lt (b := 7) (c := 8 * 66) h64 (by omega)
      have hl₁ : (Spec.Weierstrass.toBytes 66
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg 64) * 2 ^ 7)).length = 66 := by
        simp [Spec.Weierstrass.toBytes]
      unfold DgOk
      simp only [dgAddr, hw, ite_true, eOf, hBOf]
      rw [hq66, hX, hashToInt_takeR (R := 66) (by omega) (by rw [hl₁]), List.take_of_length_le (by rw [hl₁]),
        ofBytes_toBytes _ _ hlt, show 8 * 66 - Spec.Ecdsa.nBits P.C = 7 by omega, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _), e64,
        (hashToInt_short (h := Spec.Sha256.bytesAt m₀ L.dg 64) (by rw [Proof.Hmac.Common.bytesAt_length]; omega)
          hn0).1]

/-- The keys and `V`s of steps d–g. -/
abbrev K₁ (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Hmac.hmac P.Hf (List.replicate P.I.hashLen 0)
    (List.replicate P.I.hashLen 1 ++ BitVec.ofNat 8 0 :: (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Hmac.hmac P.Hf (K₁ P L m₀) (List.replicate P.I.hashLen 1)
abbrev K₂ (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Hmac.hmac P.Hf (K₁ P L m₀) (V₁ P L m₀ ++ BitVec.ofNat 8 1 :: (dB P L m₀ ++ hSpec P L m₀))

/-- After step e or g. -/
structure QB (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) (K V : List Byte) (u : State) : Prop where
  h : tailOf P.K L u.mem = hSpec P L m₀
  k : keyOf P.K L u.mem = K
  v : vOf P.K L u.mem = V
  dg : DgOk P L m₀ u.mem

theorem e_eq (hq : L.q = P.c.len) : extra P.c.hHigh P.c.wide = L.e := by
  unfold Lay.e; rw [L.hHigh_eq hq.symm P.hcD, L.wide_eq hq.symm P.hcD]

/-- `h` in the messages, kept by code that keeps the frame's `h`. -/
theorem tail_keep (hL : L.Ok) {u u' : State} (hc : Ctx L g lr m₀ u) (hc' : Ctx L g lr m₀ u')
    (hh : hOf L u'.mem = hOf L u.mem) : tailOf P.K L u'.mem = tailOf P.K L u.mem := by
  cases hw : L.wide
  · simp only [tailOf, hw, Bool.false_eq_true, ite_false]; exact hh
  · simp only [tailOf, hw, ite_true]
    have hD : P.K.H.D ≤ P.I.hashLen := by rw [P.hD]
    rw [hc'.dgBytes hL hD, hc.dgBytes hL hD]

theorem rekeyFull_okP (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) {b : Nat} (hb : b < 2) :
    WP isa (P.c.rekeyFull b) t (Rekeyed P.K L g lr m₀ t
      (vOf P.K L t.mem ++ BitVec.ofNat 8 b :: (Spec.Sha256.bytesAt t.mem L.d L.q ++ tailOf P.K L t.mem))) :=
  rekeyFull_ok P.K P.hcH hq.symm P.hcD hL (lfar hq) (fun hw => ⟨lq_ok hq hw, (narrow_q hq hw).2.1⟩)
    (fun hw => Nat.le_of_eq (wide_q hq hw).1) hc hb

theorem stageB_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) (ha : QA P L m₀ t) :
    WP isa (P.c.rekeyFull 0) t fun u => Ctx L g lr m₀ u ∧ QB P L m₀ (K₁ P L m₀) (V₁ P L m₀) u :=
  WP.mono (rekeyFull_okP hL hq hc (b := 0) (by decide)) fun u h =>
    ⟨h.ctx, (tail_keep hL hc h.ctx h.h).trans ha.h, by rw [h.key, ha.k, ha.v, ha.h, hc.dBytes hL (Nat.le_refl _)],
      by rw [h.v, h.key, ha.k, ha.v, ha.h, hc.dBytes hL (Nat.le_refl _)], ha.dg.frame hL hq h.frame kvW_dg⟩

theorem stageC_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t)
    (hb : QB P L m₀ (K₁ P L m₀) (V₁ P L m₀) t) :
    WP isa (P.c.rekeyFull 1) t fun u => Ctx L g lr m₀ u ∧ QB P L m₀ (kv0 P L m₀).1 (kv0 P L m₀).2 u :=
  WP.mono (rekeyFull_okP hL hq hc (b := 1) (by decide)) fun u h =>
    ⟨h.ctx, (tail_keep hL hc h.ctx h.h).trans hb.h,
      by rw [h.key, hb.k, hb.v, hb.h, hc.dBytes hL (Nat.le_refl _), kv0_eq hq],
      by rw [h.v, h.key, hb.k, hb.v, hb.h, hc.dBytes hL (Nat.le_refl _), kv0_eq hq],
      hb.dg.frame hL hq h.frame kvW_dg⟩

theorem stageD_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t)
    (hb : QB P L m₀ (kv0 P L m₀).1 (kv0 P L m₀).2 t) :
    WP isa (.block P.c.initCnt) t fun u => Ctx L g lr m₀ u ∧ LoopInv P L m₀ 0 u := by
  have hnB := hL.nB
  have hD := P.K.hH.hD64
  refine WP.mono (initCnt_ok hL P.hT' hc) fun u ⟨hcu, hf, hcnt⟩ => ⟨hcu, P.hT, ?_, ?_, hcnt, fun j hj => absurd hj
    (Nat.not_lt_zero _), hb.dg.frame hL hq hf cnt_dg⟩
  · refine (bytesAt_frame hf ?_ (by omega)).trans hb.k
    simp only [List.mem_singleton]; rintro r rfl; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · refine (bytesAt_frame hf ?_ (by omega)).trans hb.v
    simp only [List.mem_singleton]; rintro r rfl; exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- From the arguments saved to the wiped frame: the loop has stopped at a candidate. -/
theorem rest_ok (hL : L.Ok) (hq : L.q = P.c.len) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.seq P.c.start (.seq (P.c.rekeyFull 0) (.seq (P.c.rekeyFull 1)
      (.seq (.block P.c.initCnt) (.seq (.loop P.c.tryOne (.nonzero .d .r12))
        (.block (Cfg.wipe P.c.hHigh P.c.wide))))))) t
      fun u => Ctx L g lr m₀ u ∧ ∃ i, Exit P L m₀ i u := by
  have hnB := hL.nB
  refine WP.seq (WP.mono (stageA_ok hL hq hc) fun u₁ ⟨hc₁, ha⟩ => ?_)
  refine WP.seq (WP.mono (stageB_ok hL hq hc₁ ha) fun u₂ ⟨hc₂, hb⟩ => ?_)
  refine WP.seq (WP.mono (stageC_ok hL hq hc₂ hb) fun u₃ ⟨hc₃, hb₃⟩ => ?_)
  refine WP.seq (WP.mono (stageD_ok hL hq hc₃ hb₃) fun u₄ ⟨hc₄, h₀⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hL hq hc₄ h₀) fun u₅ ⟨hc₅, i, hx⟩ => ?_)
  refine WP.mono (wipe_ok hL (by rw [e_eq hq]) hc₅) fun u ⟨hcu, K, hf⟩ => ⟨hcu, i, hx.lt, hx.fails, hx.last,
    hx.res.keep (by rw [K.gpr _ (by decide)]) (bytesAt_frame hf ?_ (by have := hL.no; omega))⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hL.stk_OUT (by omega)).symm
  · exact (hL.stk_OUT (by omega)).symm

/-! ## The result -/

theorem k_pos (P : Rfc) (hw : P.c.wide = false) : 1 ≤ P.k := by
  rcases Nat.eq_zero_or_pos P.k with h | h
  · have h₁ := P.hn₁ hw; have h₂ := P.hn₂ hw
    rw [h] at h₁ h₂
    simp only [Nat.mul_zero, Nat.pow_zero] at h₁ h₂
    omega
  · exact h

/-- Each candidate is `nb` `V`s: one, or two if `wide`. -/
theorem blocks_eq (P : Rfc) : Spec.Ecdsa.Rfc6979.blocks P.C P.I.hashLen = P.nb := by
  cases hw : P.c.wide
  · have := k_pos P hw
    have hb := P.hbits hw; have hk := P.hk hw; have hQ := P.hQD hw
    simp only [Rfc.nb, hw, Bool.false_eq_true, ite_false]
    rw [Spec.Ecdsa.Rfc6979.blocks]
    exact Nat.div_eq_of_lt_le (by simp only [Rfc.C] at *; omega) (by simp only [Rfc.C] at *; omega)
  · obtain ⟨hD, -, hb⟩ := P.hW hw
    have hD' : P.I.hashLen = 64 := by rw [← P.hcD, hD]
    simp only [Rfc.nb, hw, ite_true, Spec.Ecdsa.Rfc6979.blocks, hD', Rfc.C, hb]

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold (hq : L.q = P.c.len) :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.C.n then
        Spec.Ecdsa.Rfc6979.search P.C P.Hf P.I.hashLen (xOf P L m₀) (eOf P L m₀) (kv0 P L m₀).1 (kv0 P L m₀).2
          P.c.tries
      else (none, 0) := by
  have hl : P.I.ecdsa.curve.len = L.q := by rw [hq, P.hcl, P.hE]
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.sign, hl, P.hct]
  rw [P.hE, P.hHash]
  rfl

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq (hq : L.q = P.c.len) {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold hq]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.C.n
  · simp only [hv, and_self, ite_true]
    rw [searchB_shift (blocks_eq P) i P.c.tries (by have := hx.lt; omega) hx.fails,
      show P.c.tries - i = (P.c.tries - 1 - i) + 1 by have := hx.lt; omega]
    cases hs : sigI P L m₀ i with
    | some rs => rw [searchB_ok (blocks_eq P) hs]
    | none =>
      have h7 : i + 1 = P.c.tries := hx.last.resolve_left (by simp [hs])
      rw [searchB_fail (blocks_eq P) hs, show P.c.tries - 1 - i = 0 by omega]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

theorem ite_le_of_not {c : Prop} [Decidable c] {a b i : Nat} (hc : ¬c) (hb : b ≤ i) :
    (if c then a else b) ≤ i := by
  simp only [hc, ite_false]; exact hb

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : Rfc) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  if (result P.I m₀ L.d L.dg).2 = 0 then P.c.tries - 1 else (result P.I m₀ L.d L.dg).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff (hq : L.q = P.c.len) {i : Nat} (hi : i < P.c.tries) (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < P.c.tries) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold hq]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.C.n
  · simp only [hv, and_self, ite_true]
    rw [searchB_shift (blocks_eq P) i P.c.tries (by omega) hf,
      show P.c.tries - i = (P.c.tries - 1 - i) + 1 by omega]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [searchB_ok (blocks_eq P) hs]
      simp
    | none =>
      rw [searchB_fail (blocks_eq P) hs]
      by_cases h7 : i + 1 < P.c.tries
      · have := searchB_pos (C := P.C) (H := P.Hf) (hlen := P.I.hashLen)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.c.tries - 2 - i)
          (K := (stepB P.Hf P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.Hf P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
        rw [show P.c.tries - 1 - i = P.c.tries - 2 - i + 1 by omega]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega
      · rw [show P.c.tries - 1 - i = 0 by omega]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega) (by omega)
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega

/-! ## The whole function -/

theorem lay_q (P : Rfc) (s : State) : (lay P.I.hashLen P.I.ecdsa.curve.len s).q = P.c.len := by
  show P.I.ecdsa.curve.len = _; rw [P.hE, P.hcl]

theorem pre_conv {s : State} (h : (rfcPPC P.I (400 + extra P.c.hHigh P.c.wide)).pre s) :
    (rfcPPC P.I (400 + extraOf P.I.hashLen P.I.ecdsa.curve.len)).pre s := by
  have hlen : P.I.ecdsa.curve.len = P.c.len := by rw [P.hE, P.hcl]
  rw [hlen, extraOf, ← P.hcD]; exact h

/-- The signature, with the frames: the return address saved in the outer
one, the arguments in the inner one, and both popped. -/
theorem sign_ok {s : State} (h : (rfcPPC P.I (400 + extra P.c.hHigh P.c.wide)).pre s) :
    WP isa P.c.sign s fun s' => abiPreserved s s' ∧ (rfcPPC P.I (400 + extra P.c.hHigh P.c.wide)).post s s' := by
  have h' := pre_conv h
  have hL := lay_ok h'
  have hq := lay_q P s
  have he : extra P.c.hHigh P.c.wide = (lay P.I.hashLen P.I.ecdsa.curve.len s).e := e_eq hq
  have hsp : 400 + extra P.c.hHigh P.c.wide ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨L, hl⟩ : ∃ L, lay P.I.hashLen P.I.ecdsa.curve.len s = L := ⟨_, rfl⟩
  have hB : s.sp = L.B + BitVec.ofNat 64 (400 + L.e) := by
    rw [← hl]
    show s.sp = s.sp - BitVec.ofNat 64 (400 + (lay P.I.hashLen P.I.ecdsa.curve.len s).e) +
      BitVec.ofNat 64 (400 + (lay P.I.hashLen P.I.ecdsa.curve.len s).e)
    rw [BitVec.sub_add_cancel]
  rw [hl] at he
  have hne := L.e_le
  have hn16 := L.e_mod
  have hnB := hL.nB
  rw [Cfg.sign, frameBytes, he]
  refine WP.seq (wp_step exec_mflr (wp_nil ?_))
  refine WP.seq (WP.frame (by show 48 ≤ s.sp.toNat; omega) (WP.alloc (by omega)
    (by show 256 + L.e ≤ (s.sp - 48).toNat; rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 48 ≤ s.sp.toNat; omega)]
        show 256 + L.e ≤ s.sp.toNat - 48; omega) ?_))
  rw [Cfg.body]
  have hent := entry_ok h'
  rw [hl] at hent
  refine WP.seq (WP.mono hent fun t hc => ?_)
  rw [hl] at hL hq
  refine WP.mono (rest_ok hL hq hc) fun u ⟨hcu, i, hx⟩ => ?_
  refine wp_step exec_mtlr (wp_nil ?_)
  have hsu := hcu.sp
  -- The return address and the stack pointer, as on entry.
  have hr0 : (popped .r0 (freed (256 + L.e) u)).gpr .r0 = s.lr := by
    show (freed (256 + L.e) u).mem.read ((freed (256 + L.e) u).sp + 32) 8 = _
    rw [show (freed (256 + L.e) u).sp + 32 = L.B + BitVec.ofNat 64 (384 + L.e) by
      show u.sp + BitVec.ofNat 64 (256 + L.e) + 32 = _
      rw [hsu, fr_add, BitVec.add_assoc]
      congr 1
      rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, BitVec.ofNat_add_ofNat]; congr 1; omega, read8]
    exact hcu.lr
  refine ⟨⟨fun r hr => ?_, ?_, hr0⟩, ?_⟩
  · show (popped .r0 (freed (256 + L.e) u)).gpr r = _
    have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hr (by decide)
    show ((freed (256 + L.e) u).write .r0 _).gpr r = _
    rw [Proof.Mont.PPC64LE.write_gpr]; simp only [h0, ↓reduceIte]
    exact hcu.cs r hr
  · show u.sp + BitVec.ofNat 64 (256 + L.e) + 48 = s.sp
    rw [hsu, hB, fr_add, BitVec.add_assoc]
    congr 1
    rw [show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, BitVec.ofNat_add_ofNat]; congr 1; omega
  · have hr := result_eq hq hx
    have hm : (popped .r0 (freed (256 + L.e) u)).mem = u.mem := rfl
    have h3 : (popped .r0 (freed (256 + L.e) u)).gpr .r3 = u.gpr .r3 := rfl
    have hd : s.gpr .r4 = L.d := by rw [← hl]; rfl
    have hg : s.gpr .r5 = L.dg := by rw [← hl]; rfl
    have ho : s.gpr .r3 = L.out := by rw [← hl]; rfl
    have hlq : P.I.ecdsa.curve.len = L.q := by rw [← hl]; rfl
    show match (result P.I s.mem (s.gpr .r4) (s.gpr .r5)).1 with
      | some rs => ((popped .r0 (freed (256 + L.e) u)).gpr .r3).setWidth 32 = 1 ∧
          Spec.Ecdsa.bytesAt (popped .r0 (freed (256 + L.e) u)).mem (s.gpr .r3) (2 * P.I.ecdsa.curve.len) =
            Spec.Ecdsa.encode P.I.ecdsa.curve rs
      | none => ((popped .r0 (freed (256 + L.e) u)).gpr .r3).setWidth 32 = 0 ∧
          Spec.Ecdsa.bytesAt (popped .r0 (freed (256 + L.e) u)).mem (s.gpr .r3) (2 * P.I.ecdsa.curve.len) =
            List.replicate (2 * P.I.ecdsa.curve.len) 0
    rw [hd, hg, hr, hm, h3, ho, hlq, P.hE]
    have := hx.res
    unfold ResultIs at this
    exact this

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
