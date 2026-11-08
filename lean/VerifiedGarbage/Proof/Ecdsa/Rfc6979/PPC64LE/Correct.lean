module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Loop
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Prep
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Reduce
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.PPC64LE.Step

/-!
# Deterministic ECDSA on PPC64LE: correctness

The loop leaves it at a candidate that is suitable or the last
(`tries_ok`); before it, `h`, `K`, `V`, `core`'s digest and the count are
as RFC 6979's steps a–g make them (`stageX_ok` … `stageE_ok`); and the
signature of that candidate is RFC 6979's (`result_eq`), for the hash
function `P`'s instance of the contract, with the frames pushed and popped
around the body (`sign_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp wp_step)
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB rlenR hashToInt_takeQ hashToInt_short hashToInt_takeR
  bits2octets_short ofBytes_zeros ofBytes_lt ofBytes_toBytes toBytes_ofBytes)
open VG.Proof.Hmac.Common (bytesAt_length)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-! ## Steps a–g -/

theorem RfcCurve.n_ne (R : RfcCurve) : R.C.E.curve.n ≠ 0 := Nat.pos_iff_ne_zero.mp R.n_pos

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.C.E.curve = P.Q :=
  rlenR (nBits_len P).2 (nBits_len P).1

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : RfcHash) {x : Nat} {dB hB h : List Byte} (hd : dB.length = P.Q)
    (hx : x = Spec.Weierstrass.ofBytes dB) (hh : Spec.Ecdsa.Rfc6979.bits2octets P.R.C.E.curve hB = h) :
    Spec.Ecdsa.Rfc6979.init P.R.C.E.curve P.v.ok.SH.H P.v.H.D x hB =
      let K₁ := P.mac (List.replicate P.v.H.D 0) (List.replicate P.v.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.v.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets P.R.C.E.curve x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_eq, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.C.E.curve (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.v.H.D 0) (List.replicate P.v.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (K₁ P L m₀) (List.replicate P.v.H.D 1)

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (bytesAt_length _ _ _) rfl rfl

/-- The digest's integer is `X`'s, `Q - m` zero bytes then the digest's first
`m = min(D, Q)`, if the scalars have `8 Q` bits. -/
theorem x_eq {C : Spec.Weierstrass.Curve} {Q D : Nat} (hq : Spec.Ecdsa.nBits C = 8 * Q) (hn : C.n ≠ 0)
    {hB : List Byte} (hl : hB.length = D) :
    Spec.Weierstrass.ofBytes (List.replicate (Q - min D Q) 0 ++ hB.take (min D Q)) = Spec.Ecdsa.hashToInt C hB := by
  by_cases h : Q ≤ D
  · rw [Nat.min_eq_right h, Nat.sub_self, List.replicate_zero, List.nil_append,
      hashToInt_takeQ hq (by rw [hl]; exact h)]
  · rw [Nat.min_eq_left (by omega), List.take_of_length_le (by rw [hl]), ofBytes_zeros,
      (hashToInt_short (by rw [hl, hq]; omega) hn).1]

theorem Ctx.dgBytes (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {n : Nat} (hn : n ≤ P.I.hashLen) :
    Spec.Sha256.bytesAt t.mem L.dg n = Spec.Sha256.bytesAt m₀ L.dg n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (by have := List.mem_range.mp hi; omega)

/-- `h`, kept by memory that changed apart from it. -/
theorem hOf_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, ∀ {d n : Nat}, 328 ≤ d → d + n ≤ 472 → Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r) :
    hOf P L m' = hOf P L m := by
  have := fHo_le P
  exact bytesAt_frame hf (fun r hr => hd r hr (by omega) (by omega)) (by have := Q_le P; omega)

/-- `core`'s digest, kept by memory that changed apart from it. -/
theorem DgOk.frameD {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, ∀ {d n : Nat}, 272 ≤ d → d + n ≤ 544 → Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r) :
    DgOk P L m₀ m' := by
  have := Q_le P
  obtain ⟨d, hd', h₁, h₂⟩ := dgArg_off P L
  unfold DgOk
  rw [bytesAt_frame hf (fun r hr => by rw [hd']; exact hd r hr h₁ h₂) (by omega)]
  exact h

/-- After `X` and `h`: `h`, and `core`'s digest. -/
structure QA (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  dg : DgOk P L m₀ u.mem

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.v.H.D 0
  v : vOf P L u.mem = List.replicate P.v.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)
  /-- `d ‖ h`, after the message's first byte. -/
  tail : tailOf P L u.mem = Spec.Sha256.bytesAt m₀ L.d P.Q ++ hSpec P L m₀

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)

/-- After `X`: `Q - m` zero bytes, then the digest's first `m = min(D, Q)`. -/
abbrev QX (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop :=
  Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + fX)) P.Q =
    List.replicate (P.Q - min P.v.H.D P.Q) 0 ++ (hBOf P L m₀).take (min P.v.H.D P.Q)

theorem stageX_ok (hL : L.Ok) (hq : HOk P L) {u : State} (hc : Ctx L g lr m₀ u) :
    WP isa (cfgOf P).prepX u fun u' => Ctx L g lr m₀ u' ∧ QX P L m₀ u' := by
  have hD : P.v.H.D = P.I.hashLen := P.len.symm
  have hdg : Spec.Sha256.bytesAt u.mem L.dg (min P.v.H.D P.Q) = (hBOf P L m₀).take (min P.v.H.D P.Q) := by
    rw [hc.dgBytes hL (by rw [← hD]; omega), hBOf, ← bytesAt_take _ _ (Nat.min_le_left _ _)]
  exact WP.mono (prepX_ok hL hq.2.1 (by rw [← hD]) hc) fun u₁ ⟨hc₁, _, hx₁⟩ =>
    ⟨hc₁, by show Spec.Sha256.bytesAt _ _ _ = _; rw [hx₁, hdg]⟩

theorem fHo_small (h : P.R.big = false) : (cfgOf P).fHo = fH := by
  simp only [Cfg.fHo, show (cfgOf P).big = false from h, Bool.false_eq_true, ite_false]

theorem fHo_big (h : P.R.big = true) : (cfgOf P).fHo = fX := by
  simp only [Cfg.fHo, show (cfgOf P).big = true from h, ite_true]

/-- `h` (step c's `h1` as `bits2octets`), and `core`'s digest. -/
theorem stageH_ok (hL : L.Ok) (hq : HOk P L) {u₁ : State} (hc₁ : Ctx L g lr m₀ u₁) (hx₁ : QX P L m₀ u₁) :
    WP isa (cfgOf P).prepH u₁ fun u' => Ctx L g lr m₀ u' ∧ QA P L m₀ u' := by
  have hD : P.v.H.D = P.I.hashLen := P.len.symm
  have hl := nBits_len P
  have hs := P.sizes
  have hlB : (hBOf P L m₀).length = P.v.H.D := bytesAt_length _ _ _
  have hnB := hL.nB
  unfold QX at hx₁
  cases hb : P.R.big
  · obtain ⟨hQ5, -, hq8, hn2⟩ := P.R.sizesA hb
    have hq' : Spec.Ecdsa.nBits P.R.C.E.curve = 8 * P.Q := hq8
    have hk4 : (cfgOf P).len = 4 * (P.Q / 4) := by
      show P.R.Q = _; simp only [RfcHash.Q] at *; omega
    have hk16 : P.Q / 4 ≤ 16 := by simp only [RfcHash.Q] at *; omega
    have e32 : 32 * (P.Q / 4) = 8 * P.Q := by simp only [RfcHash.Q] at *; omega
    have hn₁ : (cfgOf P).n < 2 ^ (32 * (P.Q / 4)) := by
      show P.R.C.E.curve.n < _
      rw [e32, ← hq', Spec.Ecdsa.nBits]; exact Nat.lt_log2_self
    have hn₂ : 2 ^ (32 * (P.Q / 4)) < 2 * (cfgOf P).n := by rw [e32]; exact hn2
    have hX : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (xA L) P.Q) = eOf P L m₀ := by
      rw [show xA L = L.B + BitVec.ofNat 64 (96 + fX) from rfl, hx₁, x_eq hq' P.R.n_ne hlB]
    rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by
      simp only [Cfg.prepH, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    refine WP.mono (reduce_ok hL hk4 hk16 hn₁ hn₂ hc₁) fun u₂ ⟨hc₂, hf₂, hh₂⟩ => ⟨hc₂, ?_, ?_⟩
    · have e4 : 4 * (P.Q / 4) = P.Q := by simp only [RfcHash.Q] at *; omega
      rw [e4, show (cfgOf P).n = P.R.C.E.curve.n from rfl, hX] at hh₂
      show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (96 + (cfgOf P).fHo)) P.Q = _
      rw [fHo_small hb, ← toBytes_ofBytes (Spec.Sha256.bytesAt u₂.mem _ P.Q), bytesAt_length, hh₂, hSpec,
        Spec.Ecdsa.Rfc6979.bits2octets, Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlen_eq]
    · unfold DgOk
      simp only [dgArg, hb, Bool.false_eq_true, ite_false]
      have hQ64 : P.Q ≤ 64 := by simp only [RfcHash.Q] at *; omega
      rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (.inr (by simp only [fX]; omega)) (by simp only [fX]; omega) (by omega)
          · exact Offset.disjoint _ (.inr (by simp only [fX]; omega)) (by simp only [fX]; omega)
              (by omega)) (by omega),
        hashToInt_takeQ hq' (by rw [bytesAt_length]), List.take_of_length_le (by rw [bytesAt_length])]
      exact hX
  · obtain ⟨-, hQ66', hQD⟩ := P.R.sizesW hb
    have hQ66 : P.Q = 66 := hQ66'
    have hN : 8 * P.v.H.D < Spec.Ecdsa.nBits P.R.C.E.curve := by rw [hQD]; omega
    have hm : min P.v.H.D P.Q = P.v.H.D := Nat.min_eq_left (by omega)
    rw [hm, List.take_of_length_le (by rw [hlB])] at hx₁
    rw [show (cfgOf P).prepH = (cfgOf P).prepC by
      simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true]]
    refine WP.mono (prepC_ok hL hq.2.1 hb (by rw [← hD]) hc₁) fun u₂ ⟨hc₂, hf₂, hx₂⟩ => ⟨hc₂, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (96 + (cfgOf P).fHo)) P.Q = _
      rw [fHo_big hb, bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_scr (by simp only [fX]; omega) (by decide)
          · exact Offset.disjoint _ (.inl (by simp only [fX, fXc]; omega)) (by simp only [fX]; omega)
              (by simp only [fXc]; omega)) (by omega),
        hx₁, hSpec, bits2octets_short (R := P.Q) hl.2 hl.1 (by rw [hlB]; exact hN) P.R.n_ne, hlB]
    · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
      have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (hBOf P L m₀) :=
        (hashToInt_short (by rw [hlB]; exact hN) P.R.n_ne).1
      rw [hc₁.dgBytes hL (by rw [← hD])] at hx₂
      have hsh : P.R.sh = 7 := P.R.sh7 hb
      have hlt : Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh < 2 ^ (8 * P.Q) := by
        have := ofBytes_lt (hBOf P L m₀)
        rw [hlB] at this
        calc _ < 2 ^ (8 * P.v.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by
            rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
      have hl₁ : (Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh)).length =
          P.Q := by simp [Spec.Weierstrass.toBytes]
      unfold DgOk
      simp only [dgArg, hb, ite_true]
      rw [hx₂, hashToInt_takeR (R := P.Q) hl.2 (by rw [hl₁]),
        List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.C.E.curve = P.R.sh from P.R.sh_eq.symm, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _), e₂]

theorem kvw_h (hL : L.Ok) : ∀ r ∈ KVW L, ∀ {d n : Nat}, 328 ≤ d → d + n ≤ 472 →
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  have := hL.nB
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl) d n h₁ h₂
  · exact hL.stk_SCR (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)

/-- `V = 0x01…` and `K = 0x00…`. -/
theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g lr m₀ u) (hq : QA P L m₀ u) :
    WP isa Cfg.initKV u fun u' => Ctx L g lr m₀ u' ∧ QB P L m₀ u' := by
  have hs := P.sizes
  have := hL.nB
  have kv : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 128, 128⟩ : Region)], ∀ {d n : Nat}, 256 ≤ d → d + n ≤ 736 →
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := fun r hr d n h₁ h₂ => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  exact WP.mono (initKV_ok hL hc) fun u₂ ⟨hc₂, hf₂, hkv₂⟩ =>
    ⟨hc₂, ⟨(hOf_frame hf₂ fun r hr _ _ h₁ h₂ => kv r hr (by omega) (by omega)).trans hq.h,
      (hkv₂ _ (by omega)).2, (hkv₂ _ (by omega)).1,
      hq.dg.frameD hf₂ fun r hr _ _ h₁ h₂ => kv r hr (by omega) (by omega)⟩⟩

theorem stageC_ok (hL : L.Ok) (hq : HOk P L) {u : State} (hc : Ctx L g lr m₀ u) (hb : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g lr m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hq hc 0 (by decide) (fun h => absurd rfl h) fun h => absurd rfl h)
    fun u' ⟨hc', hf', hk', hv', hS', ht'⟩ =>
    ⟨hc', (hOf_frame hf' (kvw_h hL)).trans hb.h,
      by rw [hk', hb.k, hb.v, hb.h, hc.dBytes hL hq.1],
      by rw [hv', hk', hb.k, hb.v, hb.h, hc.dBytes hL hq.1], hb.dg.frameA hL hf' kvw_away, hS',
      by rw [ht', hb.h, hc.dBytes hL hq.1]⟩

theorem stageD_ok (hL : L.Ok) (hq : HOk P L) {u : State} (hc : Ctx L g lr m₀ u) (hb : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g lr m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hq hc 1 (by decide) (fun _ => hb.saved)
    fun _ => by rw [hb.tail, hb.h, hc.dBytes hL hq.1]) fun u' ⟨hc', hf', hk', hv', hS', _⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hb.k, hb.v, hb.h, hc.dBytes hL hq.1],
      by rw [kv0_eq', hv', hk', hb.k, hb.v, hb.h, hc.dBytes hL hq.1], hb.dg.frameA hL hf' kvw_away, hS'⟩

theorem stageE_ok (hL : L.Ok) {u : State} (hc : Ctx L g lr m₀ u) (hb : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g lr m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL P.tries_lt hc) fun u' ⟨hc', hf', hn'⟩ => by
    obtain ⟨ek, ev⟩ := kv_keep (P := P) hf' (cntw_kv hL)
    refine ⟨hc', P.tries_pos, ek.trans hb.k, ev.trans hb.v, by rw [hn', Nat.sub_zero]; rfl,
      fun j hj => absurd hj (Nat.not_lt_zero _), hb.dg.frame hL hf' (fun r hr => by
        simp only [List.mem_singleton] at hr; exact .inr hr), ?_⟩
    rw [ek]
    exact hb.saved.frame (blockKey_length (bytesAt_length _ _ _)) hf' fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_scr (by omega) (by decide)).symm

theorem stageG_ok (hL : L.Ok) (hq : HOk P L) {u : State} (hc : Ctx L g lr m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa Cfg.wipe u fun u' => Ctx L g lr m₀ u' ∧ Exit P L m₀ i u' :=
  WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, K₇, hf₇⟩ => ⟨hc₇, hx.lt, hx.fails, hx.last,
    hx.res.keep (by rw [K₇.gpr _ (by decide)]) (out_keep (P := P) hL hq.1 hf₇ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega)).symm
      · exact (hL.stk_OUT (by omega)).symm)⟩

/-- The body after the arguments are saved. -/
theorem rest_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.seq (cfgOf P).prepX (.seq (cfgOf P).prepH (.seq Cfg.initKV (.seq ((cfgOf P).rekeyFull 0)
      (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne (.nonzero .d .r12)) Cfg.wipe))))))) t
      fun t' => Ctx L g lr m₀ t' ∧ ∃ i, Exit P L m₀ i t' :=
  WP.seq (WP.mono (stageX_ok hL hq hc) fun _ ⟨h₀, q₀⟩ =>
    WP.seq (WP.mono (stageH_ok hL hq h₀ q₀) fun _ ⟨h₁, q₁⟩ =>
    WP.seq (WP.mono (stageB_ok hL h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
      WP.seq (WP.mono (stageC_ok hL hq h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
        WP.seq (WP.mono (stageD_ok hL hq h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
          WP.seq (WP.mono (stageE_ok hL h₄ q₄) fun _ ⟨h₅, q₅⟩ =>
            WP.seq (WP.mono (tries_ok hL hq h₅ q₅) fun _ ⟨h₆, i, q₆⟩ =>
              WP.mono (stageG_ok hL hq h₆ q₆) fun _ ⟨h₇, q₇⟩ => ⟨h₇, i, q₇⟩)))))))

/-! ## RFC 6979's result -/

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.C.E.curve.n then
        Spec.Ecdsa.Rfc6979.search P.R.C.E.curve P.v.ok.SH.H P.v.H.D (xOf P L m₀) (eOf P L m₀)
          (kv0 P L m₀).1 (kv0 P L m₀).2 P.I.tries
      else (none, 0) := by
  simp only [result, Proof.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.sign, P.ecdsa, P.hash, P.len,
    Proof.Ecdsa.Rfc6979.ecdsa_bytesAt]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.C.E.curve.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (nV_eq P) i P.I.tries (by have := hx.lt; omega) hx.fails,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by have := hx.lt; omega]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (nV_eq P) hs]
    | none =>
      have h7 : i + 1 = P.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (nV_eq P) hs, show P.I.tries - 1 - i = 0 by omega]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-! ## The whole function -/

/-- The contract the code for `P`'s hash function is proven against, with
`P`'s table and the functions `ns`' addresses public. -/
abbrev rfcP (P : RfcHash) (ns : List String) : Contract isa :=
  rfcPPC P.I 736 (tabFacts P.v P.f) ns P.R.C.cs

/-- The layout of a call from `s`. -/
abbrev layOf (P : RfcHash) (s : State) : Lay P.I.hashLen := lay P.I.hashLen P.I.ecdsa.curve.len P.v P.f s P.R.C.cs

theorem hok_lay (P : RfcHash) (s : State) : HOk P (layOf P s) :=
  ⟨show P.I.ecdsa.curve.len = P.R.C.E.curve.len by rw [P.ecdsa], ⟨rfl, rfl⟩, rfl⟩

theorem freed_mem (n : Nat) (u : State) : (freed n u).mem = u.mem := rfl
theorem freed_sp (n : Nat) (u : State) : (freed n u).sp = u.sp + BitVec.ofNat 64 n := rfl
theorem freed_gpr (n : Nat) (u : State) : (freed n u).gpr = u.gpr := rfl
theorem popped_mem (r : Reg) (u : State) : (popped r u).mem = u.mem := rfl
theorem popped_sp (r : Reg) (u : State) : (popped r u).sp = u.sp + 48 := rfl
theorem popped_gpr (r r' : Reg) (u : State) :
    (popped r u).gpr r' = (u.write r (u.mem.read (u.sp + 32) 8)).gpr r' := rfl

/-- The signature, with the frames: the return address saved in the outer
one, the arguments in the inner one, and both popped. -/
theorem sign_ok {ns : List String} {s : State} (h : (rfcP P ns).pre s) :
    WP isa (cfgOf P).sign s fun s' => abiPreserved s s' ∧ (rfcP P ns).post s s' := by
  have hL : (layOf P s).Ok := lay_ok h
  have hq := hok_lay P s
  have hsp : 736 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨L, hl⟩ : ∃ L, layOf P s = L := ⟨_, rfl⟩
  have hB : s.sp = L.B + BitVec.ofNat 64 736 := by
    rw [← hl]
    show s.sp = s.sp - BitVec.ofNat 64 736 + BitVec.ofNat 64 736
    rw [BitVec.sub_add_cancel]
  have hnB : L.B.toNat + 736 ≤ 2 ^ 64 := by rw [← hl]; exact hL.nB
  rw [Cfg.sign, frameBytes]
  refine WP.seq (wp_step exec_mflr (wp_nil ?_))
  refine WP.seq (WP.frame (by show 48 ≤ s.sp.toNat; omega) (WP.alloc (by omega)
    (by show 592 ≤ (s.sp - 48).toNat; rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 48 ≤ s.sp.toNat; omega)]
        show 592 ≤ s.sp.toNat - 48; omega) ?_))
  rw [Cfg.body]
  have hent := entry_ok h
  refine WP.seq (WP.mono hent fun t (hc : Ctx (layOf P s) s.gpr s.lr s.mem t) => ?_)
  rw [hl] at hL hq hc
  refine WP.mono (rest_ok hL hq hc) fun u ⟨hcu, i, hx⟩ => ?_
  refine wp_step exec_mtlr (wp_nil ?_)
  have hsu := hcu.sp
  have hfm : (freed 592 u).mem = u.mem := freed_mem _ _
  have hfs : (freed 592 u).sp = L.B + BitVec.ofNat 64 688 := by rw [freed_sp, hsu, fr_add]
  have hpm : (popped .r0 (freed 592 u)).mem = u.mem := by rw [popped_mem, hfm]
  have hpg : ∀ r, r ≠ .r0 → (popped .r0 (freed 592 u)).gpr r = u.gpr r := fun r h0 => by
    rw [popped_gpr, Proof.Mont.PPC64LE.write_gpr, freed_gpr]; simp only [h0, ↓reduceIte]
  -- The return address and the stack pointer, as on entry.
  have hr0 : (popped .r0 (freed 592 u)).gpr .r0 = s.lr := by
    rw [popped_gpr, Proof.Mont.PPC64LE.write_gpr]; simp only [↓reduceIte]
    rw [hfm, hfs,
      show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, fr_add, read8]
    exact hcu.lr
  refine ⟨⟨fun r hr => ?_, ?_, hr0⟩, ?_⟩
  · rw [hpg r fun e => by subst e; exact absurd hr (by decide)]
    exact hcu.cs r hr
  · rw [popped_sp, hfs, hB, show (48 : BitVec 64) = BitVec.ofNat 64 48 from rfl, fr_add]
  · have hr := result_eq hx
    have h3 : (popped .r0 (freed 592 u)).gpr .r3 = u.gpr .r3 := hpg _ (by decide)
    have hd : s.gpr .r4 = L.d := by rw [← hl]; rfl
    have hg : s.gpr .r5 = L.dg := by rw [← hl]; rfl
    have ho : s.gpr .r3 = L.out := by rw [← hl]; rfl
    have hlq : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa]
    generalize popped .r0 (freed 592 u) = v at h3 hpm ⊢
    show match (result P.I s.mem (s.gpr .r4) (s.gpr .r5)).1 with
      | some rs => (v.gpr .r3).setWidth 32 = 1 ∧
          Spec.Ecdsa.bytesAt v.mem (s.gpr .r3) (2 * P.I.ecdsa.curve.len) =
            Spec.Ecdsa.encode P.I.ecdsa.curve rs
      | none => (v.gpr .r3).setWidth 32 = 0 ∧
          Spec.Ecdsa.bytesAt v.mem (s.gpr .r3) (2 * P.I.ecdsa.curve.len) =
            List.replicate (2 * P.I.ecdsa.curve.len) 0
    rw [hd, hg, hr, hpm, h3, ho, hlq, P.ecdsa]
    have := hx.res
    unfold ResultIs at this
    exact this

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
