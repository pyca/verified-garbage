module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Loop
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Prep
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# Deterministic ECDSA on 32-bit ARM: correctness

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Correct.lean`): the loop leaves it
at a candidate that is suitable or the last (`tries_ok`); before it, `h`,
`K`, `V`, `core`'s digest and the count are as RFC 6979's steps a–g make
them (`stageX_ok` … `stageE_ok`); and the signature of that candidate is
RFC 6979's (`result_eq`), for the hash function `P`'s instance of the
contract with the table of its HMAC functions (`tabFacts`). The frame's
allocation, and our caller's registers saved in it and restored, give the
whole function (`sign_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)
open VG.Proof.X25519.Arm (wp_mov wp_str wp_ldr op2_reg)
open VG.Proof.HmacTable.Arm (TabOK TabMem tA)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The loop -/

theorem tries_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne .ne) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (P.I.tries - n) s ∧ n ≤ P.I.tries)
    ?_ P.I.tries t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega_arith
  refine WP.mono (tryOne_ok hL hk hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega_arith, hc', ?_, by omega_arith⟩
    rwa [show P.I.tries - (n - 1) = P.I.tries - n + 1 by omega_arith]

/-! ## Steps a–g -/

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.E.C = P.Q := by
  have := P.R.nBits_len
  exact rlenR (by show _ ≤ 8 * P.R.E.C.len; omega_arith) (by show 8 * P.R.E.C.len < _; omega_arith)

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : RfcHash) {x : Nat} {dB hB h : List Byte} (hd : dB.length = P.Q)
    (hx : x = Spec.Weierstrass.ofBytes dB) (hh : Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C hB = h) :
    Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.hH.SH.H P.F.H.D x hB =
      let K₁ := P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.F.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets P.R.E.C x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_eq, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte :=
  Spec.Sha256.bytesAt m₀ (State.addr L.d) P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.F.H.D 1)

/-- After `X` and `h`: `h`, and `core`'s digest. -/
structure QA (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  dg : DgOk P L m₀ u.mem

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.F.H.D 0
  v : vOf P L u.mem = List.replicate P.F.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

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

/-- After `X`: `Q - m` zero bytes, then the digest's first `m = min(D, Q)`. -/
abbrev QX (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop :=
  Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 216) P.Q =
    List.replicate (P.Q - min P.F.H.D P.Q) 0 ++ (hBOf P L m₀).take (min P.F.H.D P.Q)

theorem stageX_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (cfgOf P).prepX u fun u' => Ctx L g m₀ u' ∧ QX P L m₀ u' := by
  have hD : P.F.H.D = P.I.hashLen := P.len.symm
  have hdg : Spec.Sha256.bytesAt u.mem (State.addr L.dg) (min P.F.H.D P.Q) =
      (hBOf P L m₀).take (min P.F.H.D P.Q) := by
    rw [hc.dgBytes hL (by rw [← hD]; omega), hBOf, ← bytesAt_take _ _ (Nat.min_le_left _ _)]
  exact WP.mono (prepX_ok hL hk.2.2.1 hk.2.2.2 hc) fun u₁ ⟨hc₁, _, hx₁⟩ => ⟨hc₁, by rw [QX, hx₁, hdg]⟩

/-- `h` (step c's `h1` as `bits2octets`), and `core`'s digest. -/
theorem stageH_ok (hL : L.Ok) (hk : CoreOk P L) {u₁ : State} (hc₁ : Ctx L g m₀ u₁) (hx₁ : QX P L m₀ u₁) :
    WP isa (cfgOf P).prepH u₁ fun u' => Ctx L g m₀ u' ∧ QA P L m₀ u' := by
  have hD : P.F.H.D = P.I.hashLen := P.len.symm
  have hl := P.R.nBits_len
  have hbf := hL.B_fit
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  have hlB : (hBOf P L m₀).length = P.F.H.D := length_bytesAt _ _ _
  unfold QX at hx₁
  cases hb : P.R.big
  · have hq : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := (P.R.sizesA hb).2.2.1
    obtain ⟨hQk, -, hQ64⟩ := P.sizesA hb
    have hX : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (xA L) P.Q) = eOf P L m₀ := by
      rw [show xA L = L.B + BitVec.ofNat 64 216 from rfl, hx₁, x_eq hq P.R.n_ne hlB]
    rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by simp only [Cfg.prepH, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false]]
    refine WP.mono (reduce_ok hb hL hc₁) fun u₂ ⟨hc₂, hf₂, hh₂⟩ => ⟨hc₂, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (24 + (cfgOf P).fHo)) P.Q = _
      rw [show (cfgOf P).fHo = fH by simp only [Cfg.fHo, show (cfgOf P).big = false from hb, Bool.false_eq_true,
        ite_false], show 24 + fH = hB from rfl]
      rw [← hQk] at hh₂
      rw [← toBytes_ofBytes (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 hB) P.Q), length_bytesAt, hh₂, hX,
        hSpec, Spec.Ecdsa.Rfc6979.bits2octets, Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlen_eq]
    · unfold DgOk
      rw [show dgAddr P L = L.B + BitVec.ofNat 64 216 by
        simp only [dgAddr, Cfg.fDg, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false, fX]]
      rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
          · exact Offset.disjoint _ (.inr (by simp only [hB]; omega)) (by omega) (by simp only [hB]; omega))
          (by omega),
        hashToInt_takeQ hq (by rw [length_bytesAt]), List.take_of_length_le (by rw [length_bytesAt])]
      exact hX
  · obtain ⟨-, hQ66', -, hQD⟩ := P.sizesW hb
    have hN : 8 * P.F.H.D < Spec.Ecdsa.nBits P.R.E.C := by
      have : P.F.H.D < P.R.E.C.len := hQD
      omega
    have hm : min P.F.H.D P.Q = P.F.H.D := Nat.min_eq_left (by omega)
    rw [hm, List.take_of_length_le (by rw [hlB])] at hx₁
    rw [show (cfgOf P).prepH = (cfgOf P).prepC by simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true]]
    refine WP.mono (prepC_ok hL hk.2.2.1 hb hk.2.2.2 hc₁) fun u₂ ⟨hc₂, hf₂, hx₂⟩ => ⟨hc₂, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (24 + (cfgOf P).fHo)) P.Q = _
      rw [show (cfgOf P).fHo = fX by simp only [Cfg.fHo, show (cfgOf P).big = true from hb, ite_true],
        show 24 + fX = 216 from rfl,
        bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_scr (by omega) (by decide)
          · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by omega),
        hx₁, hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega)
          (by show 8 * P.R.E.C.len < _; omega) (by rw [hlB]; exact hN) P.R.n_ne, hlB]
    · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
      have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (hBOf P L m₀) :=
        (hashToInt_short (by rw [hlB]; exact hN) P.R.n_ne).1
      rw [hc₁.dgBytes hL (by rw [← hD])] at hx₂
      have hlt : Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh < 2 ^ (8 * P.Q) := by
        have := ofBytes_lt (hBOf P L m₀)
        rw [hlB] at this
        calc _ < 2 ^ (8 * P.F.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by
            rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by simp only [RfcHash.Q]; omega)
      have hl₁ : (Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh)).length = P.Q := by
        simp [Spec.Weierstrass.toBytes]
      unfold DgOk
      rw [show dgAddr P L = L.B + BitVec.ofNat 64 284 by
        simp only [dgAddr, Cfg.fDg, show (cfgOf P).big = true from hb, ite_true, fXc]]
      rw [hx₂, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega) (by rw [hl₁]),
        List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _), e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_frame (hL : L.Ok) {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, r = L.SCR ∨ r = ⟨L.B, 152⟩ ∨ ∃ o n, r = ⟨L.B + BitVec.ofNat 64 o, n⟩ ∧ o + n ≤ 152) :
    hOf P L m' = hOf P L m := by
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  have hbf := hL.B_fit
  have hho : 152 ≤ 24 + (cfgOf P).fHo ∧ 24 + (cfgOf P).fHo + P.Q ≤ 284 := by
    cases hb : P.R.big
    · have := P.sizesA hb
      simp only [Cfg.fHo, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false, fH]; omega
    · simp only [Cfg.fHo, show (cfgOf P).big = true from hb, ite_true, fX]; omega
  refine bytesAt_frame hf (fun r hr => ?_) (by omega)
  rcases hd r hr with rfl | rfl | ⟨o, n, rfl, hon⟩
  · exact hL.stk_SCR (by omega)
  · exact Offset.disjoint_base _ hho.1 (by omega)
  · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

theorem hOf_kvw (hL : L.Ok) {m m' : Mem} (hf : Frame (KVW L) m m') : hOf P L m' = hOf P L m :=
  hOf_frame hL hf fun r hr => by
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)

/-- `V = 0x01…` and `K = 0x00…`. -/
theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QA P L m₀ u) :
    WP isa (.block Cfg.initKV) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  have hbf := hL.B_fit
  exact WP.mono (initKV_ok hL hc) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
    ⟨hc₂, ⟨(hOf_frame hL hf₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inr (.inr ⟨24, 128, rfl, by omega⟩)).trans hq.h,
      hk₂ _ hD64, hv₂ _ hD64, hq.dg.frame hf₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dg_apart hL (r := ⟨L.B, 152⟩) (.inr (.inr (.inl rfl)))).sub_right
          (Offset.sub_base _ (by omega))⟩⟩

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk.2.2.1 (by rw [hk.1]) hc (b := 0) (by decide)) fun u' ⟨hc', _, hf', hk', hv'⟩ =>
    ⟨hc', (hOf_kvw hL hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk.2.2.1 (by rw [hk.1]) hc (b := 1) (by decide)) fun u' ⟨hc', _, hf', hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart⟩

theorem stageE_ok {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hc) fun u' ⟨hc', hm', hn'⟩ => ⟨hc', P.tries_pos, hm' ▸ hq.k, hm' ▸ hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _), hm' ▸ hq.dg⟩

/-- After the wiping: the result, and our caller's registers. -/
structure Fin (P : RfcHash) (L : Lay P.I.hashLen) (g : Reg → BitVec 32) (m₀ : Mem) (u : State) : Prop where
  sp : u.sp = L.fp
  saved : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, u.gpr p.1 = g p.1
  exit : ∃ i, Exit P L m₀ i u

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) : WP isa Cfg.wipe u (Fin P L g m₀) := by
  have hbf := hL.B_fit
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  exact WP.mono (wipe_ok hL hc) fun _ ⟨_, _, hsp, hs, ha, hf⟩ => ⟨hsp.trans hc.sp, hs, i,
    hx.lt, hx.fails, hx.last, hx.res.keep ha (bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_OUT (d := 24) (n := 4 * wipeWords) (by decide)).symm.sub_left
        (Region.sub_prefix (by rw [hk.1]))) (by omega))⟩

/-- The body, after the prologue. -/
theorem body_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (cfgOf P).prepX (.seq (cfgOf P).prepH (.seq (.block Cfg.initKV) (.seq ((cfgOf P).rekeyFull 0)
      (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt) (.seq (.loop (cfgOf P).tryOne .ne)
        Cfg.wipe))))))) t (Fin P L g m₀) :=
  WP.seq (WP.mono (stageX_ok hL hk hc) fun _ ⟨h₀, q₀⟩ =>
    WP.seq (WP.mono (stageH_ok hL hk h₀ q₀) fun _ ⟨h₁, q₁⟩ =>
    WP.seq (WP.mono (stageB_ok hL h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
          WP.seq (WP.mono (stageE_ok h₄ q₄) fun _ ⟨h₅, q₅⟩ =>
            WP.seq (WP.mono (tries_ok hL hk h₅ q₅) fun _ ⟨h₆, _, q₆⟩ => stageG_ok hL hk h₆ q₆)))))))

/-! ## RFC 6979's result -/

/-- RFC 6979's number of blocks is the candidates' `V`s. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.F.H.D = P.nV := nV_eq P

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ (State.addr L.d) (State.addr L.dg) =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.hH.SH.H P.F.H.D (xOf P L m₀) (eOf P L m₀) K V P.I.tries
      else (none, 0) := by
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve, P.hash, P.len,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ (State.addr L.d) (State.addr L.dg)).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by have := hx.lt; omega_arith) hx.fails,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by have := hx.lt; omega_arith]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
    | none =>
      have h7 : i + 1 = P.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs, show P.I.tries - 1 - i = 0 by omega_arith]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-! ## The entry -/

/-- What the contract says of the table at `stackArg s 1`: it holds `F`'s
HMAC functions, which an indirect call of `f`'s reaches, then its digest
length and HMAC's block size. -/
def tabFacts (F : Impl.Pbkdf2.Whole.Arm.Fns) (f : Fns) (s : State) : Prop :=
  TabOK F f s.syms ∧ TabMem F s.syms (stackArg s 1) s.mem ∧
    s.mem.readW (tA (stackArg s 1) tD) 32 = BitVec.ofNat 32 F.H.D ∧
    s.mem.readW (tA (stackArg s 1) tB) 32 = BitVec.ofNat 32 F.H.B

/-- The layout of a call from `s`. -/
def lay (dn q : Nat) (cs : List (String × List (BitVec 64))) (F : Impl.Pbkdf2.Whole.Arm.Fns) (f : Fns)
    (s : State) : Lay dn where
  out := s.gpr .r0
  d := s.gpr .r1
  dg := s.gpr .r2
  scr := stackArg s 0
  tab := stackArg s 1
  sp := s.sp
  q := q
  cs := cs
  sy n := if n ∈ cs.map Prod.fst then s.syms n else 0
  F := F
  f := f
  fa n := if n ∈ [F.hiN, F.H.updN, F.hfN] then s.syms n else 0

section
variable {dn q : Nat} {cs : List (String × List (BitVec 64))} {F : Impl.Pbkdf2.Whole.Arm.Fns} {f : Fns}

theorem lay_sy (s : State) {c : String × List (BitVec 64)} (hc : c ∈ cs) :
    (lay dn q cs F f s).sy c.1 = s.syms c.1 := by
  simp only [lay, List.mem_map_of_mem hc, ↓reduceIte]

theorem lay_tbls (s : State) :
    (lay dn q cs F f s).TBLs = Abi.constRegions (fun n => State.addr (s.syms n)) cs := by
  apply List.map_congr_left
  intro c hc
  simp only [lay_sy (dn := dn) (q := q) (cs := cs) (F := F) (f := f) s hc]

theorem lay_ok {I : Spec.Ecdsa.Rfc6979.Instance} {ns : List String} {s : State}
    (h : (rfcArm I stackT cs (tabFacts F f) ns).pre s) : (lay I.hashLen I.ecdsa.curve.len cs F f s).Ok := by
  obtain ⟨-, -, od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, nB, na, ao, ac, nt, to, tc, tk, tables, -⟩ := h
  refine ⟨od, og, oc, dc, gc, ko, kd, kg, kc, no, nd, ng, nc, nt, to, tc, tk, ao, ac, nB, na, ?_⟩
  intro r hr
  rw [lay_tbls] at hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  have tc := tables c hc
  refine ⟨?_, tc.2.2.1, tc.2.2.2⟩
  simpa only [toNat_addr] using tc.2.1
end

/-- Words stored at offsets apart from a range below them change nothing outside it. -/
theorem Outs.frame {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} {n : Nat}
    (h : VG.Proof.Mont.Outs base rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ n) : Frame [⟨base, n⟩] m m' :=
  fun x hx => h x fun r hr' => .inr (by
    have := hx _ (List.mem_singleton_self _)
    simp only [Region.Contains] at this
    simp only [VG.Proof.Mont.ofs]
    have := hr r hr'; omega_arith)

theorem saved_ne12 : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, p.1 ≠ .r12 := by decide

theorem saved_pairwise : Impl.Ecdsa.Rfc6979.Arm.saved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  decide

/-- The contract the code for `P`'s hash function is proven against, with
`P`'s table and the functions `ns`' addresses public. -/
abbrev rfcP (P : RfcHash) (ns : List String) : Contract isa :=
  rfcArm P.I stackT P.R.coreConsts (tabFacts P.F P.f) ns

/-- The layout of a call from `s`. -/
abbrev layOf (P : RfcHash) (s : State) : Lay P.I.hashLen :=
  lay P.I.hashLen P.I.ecdsa.curve.len P.R.coreConsts P.F P.f s

theorem coreOk_lay (P : RfcHash) (s : State) : CoreOk P (layOf P s) :=
  ⟨P.curveLen, rfl, ⟨rfl, rfl⟩, by rw [P.len]⟩

theorem fp_arg {s : State} {o : Nat} :
    (layOf P s).fp + BitVec.ofNat 32 (512 + o) = s.sp + BitVec.ofNat 32 o := by
  apply BitVec.eq_of_toNat_eq
  have := s.sp.isLt
  simp only [Lay.fp, layOf, lay, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

/-- The prologue: our caller's registers into the frame, and the pointers to the registers that keep them. -/
theorem entry_ok {ns : List String} {s : State} (h : (rfcP P ns).pre s) :
    WP isa (.block Cfg.prologue) (allocated frameBytes s) (Ctx (layOf P s) s.gpr s.mem) := by
  apply WP.of_syms
  have hL : (layOf P s).Ok := lay_ok h
  have hN : 536 ≤ s.sp.toNat := hL.nB
  have hna : s.sp.toNat + 8 ≤ 2 ^ 32 := hL.na
  have htf : tabFacts P.F P.f s := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have tables := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hrd, hwr, -⟩ := h
  have hA : State.addr (layOf P s).fp = (layOf P s).B + BitVec.ofNat 64 24 := hL.fpA0
  have hb := hL.B_fit
  have hBt : (layOf P s).B.toNat = s.sp.toNat - 536 := hL.B_toNat
  have hS : State.addr s.sp = (layOf P s).B + BitVec.ofNat 64 536 := Lay.Ok.spA (L := layOf P s)
  simp only [Cfg.prologue, List.cons_append]
  refine wp_addSp (d := .r12) (imm := 0) (by decide) fun u₁ v₁ => ?_
  have h12 : u₁.gpr .r12 = (layOf P s).fp := by rw [v₁.gpr, BitVec.add_zero]; rfl
  have hs : VG.Proof.Mont.Arm.Scr u₁ ((layOf P s).B + BitVec.ofNat 64 24) 512 :=
    ⟨by rw [h12, hA], ⟨512, Nat.le_refl _, by decide, by
      rw [v₁.wr]; show _ ∈ ⟨State.addr (layOf P s).fp, 512⟩ :: s.wr; rw [hA]; exact List.mem_cons_self⟩,
      by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith, by decide⟩
  rw [WP.block_append_iff]
  refine WP.mono (Proof.Weierstrass.Arm.strs_ok hs _ (fun p hp => by have := saved_off p hp; omega_arith)
    saved_pairwise) fun u₂ ⟨K₂, O₂, V₂⟩ => ?_
  have g₂ : ∀ r, r ≠ .r12 → u₂.gpr r = s.gpr r := fun r hr => by rw [K₂.gpr r (by simp), v₁.other _ hr]; rfl
  have f₂ : Frame [(layOf P s).STK] s.mem u₂.mem := by
    rw [show s.mem = u₁.mem from v₁.mem.symm]
    refine (Outs.frame O₂ (n := 504) fun r hr => ?_).sub fun r hr => ?_
    · simp only [List.mem_map] at hr
      obtain ⟨q, hq, rfl⟩ := hr
      exact (saved_off q hq).2
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega_arith)⟩
  refine wp_mov (op2_reg _ _) fun u₃ v₃ => wp_mov (op2_reg _ _) fun u₄ v₄ => ?_
  have K₄ : VG.Proof.X25519.Arm.Rest [.r4, .r5] u₂ u₄ := (v₃.rest (by simp)).trans (v₄.rest (by simp))
  have h12₄ : u₄.gpr .r12 = (layOf P s).fp := by rw [K₄.gpr _ (by simp), K₂.gpr _ (by simp), h12]
  have hW : State.addr (u₄.gpr .r12 + BitVec.ofNat 32 fDigest) = (layOf P s).B + BitVec.ofNat 64 528 := by
    rw [h12₄, hL.fpA (by decide)]; rfl
  refine wp_str (by decide) hW ⟨(layOf P s).FR, by
      rw [K₄.wr, K₂.wr, v₁.wr]; show _ ∈ ⟨State.addr (layOf P s).fp, 512⟩ :: s.wr; rw [hA]; exact List.mem_cons_self,
    Offset.contains _ (by decide) (by decide) (by omega_arith)⟩ fun u₅ v₅ => ?_
  have m₅ : u₅.mem = u₂.mem.writeW ((layOf P s).B + BitVec.ofNat 64 528) (s.gpr .r2) := by
    rw [v₅.mem, v₄.mem, v₃.mem, K₄.gpr _ (by simp), g₂ _ (by decide)]
  have f₅' : Frame [⟨(layOf P s).B + BitVec.ofNat 64 528, 4⟩] u₂.mem u₅.mem := by
    rw [m₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have f₅ : Frame [(layOf P s).STK] s.mem u₅.mem := by
    rw [m₅]; exact f₂.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have hargs : ∀ o, o + 4 ≤ 8 → u₅.mem.readW (State.addr (s.sp + BitVec.ofNat 32 o)) 32 =
      s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 o)) 32 := fun o ho => by
    rw [addr_add (by omega_arith), hS, Offset.add_add]
    exact f₅.readW (r := ⟨(layOf P s).B + BitVec.ofNat 64 536, 8⟩) (Offset.contains _ (by omega_arith)
      (by omega_arith) (by omega_arith)) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint_base _ (by decide) (by omega_arith)) (by decide)
  have h12₅ : u₅.gpr .r12 = (layOf P s).fp := by rw [v₅.gpr, h12₄]
  have hin : ∀ o, o + 4 ≤ 8 → InRegions (u₅.rd ++ u₅.wr) (State.addr (s.sp + BitVec.ofNat 32 o)) 4 := by
    intro o ho
    refine ⟨(layOf P s).ARGS, ?_, ?_⟩
    · rw [v₅.rd, K₄.rd, K₂.rd, v₁.rd]
      show _ ∈ s.rd ++ _
      rw [hrd]
      exact List.mem_append_left _ (List.mem_append_left _ (.tail _ (.tail _ (.tail _ (.head _)))))
    · rw [addr_add (by omega_arith)]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  refine wp_ldr (by decide) (by rw [h12₅, show frameBytes = 512 + 0 from rfl, fp_arg])
    (hin 0 (by decide)) fun u₆ v₆ => ?_
  refine wp_ldr (by decide) (by rw [v₆.other _ (by decide), h12₅, show frameBytes + 4 = 512 + 4 from rfl,
    fp_arg]) (by rw [v₆.rd, v₆.wr]; exact hin 4 (by decide)) fun u₇ v₇ => ?_
  refine wp_mov (op2_reg _ _) fun u₈ v₈ => WP.block_nil (fun syEnd => ?_)
  have K₈ : VG.Proof.X25519.Arm.Rest [.r4, .r5, .r11, .r6, .r8] u₂ u₈ :=
    (K₄.mono (by simp)).trans <| (v₅.rest _).trans <| (v₆.rest (by simp)).trans <| (v₇.rest (by simp)).trans
      (v₈.rest (by simp))
  have hm : u₈.mem = u₅.mem := by rw [v₈.mem, v₇.mem, v₆.mem]
  refine ⟨by rw [K₈.rd, K₂.rd, v₁.rd, lay_tbls]; exact hrd, ?_, by rw [K₈.sp, K₂.sp, v₁.sp]; rfl, ?_, ?_, ?_, ?_, ?_,
    fun p hp => ?_, ?_, by rw [hm]; exact f₅.sub fun r hr => ⟨r, by simp at hr; simp [hr], sub_refl _⟩,
    fun c hc => by rw [syEnd]; exact (lay_sy s hc).symm, fun c hc i hi => ?_, by rw [syEnd]; exact htf.1,
    by rw [syEnd]; exact htf.2.1, htf.2.2.1, htf.2.2.2, fun n hn => by
      rw [syEnd]
      show s.syms n = (if n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN] then s.syms n else 0)
      exact (ite_eq_left_of_eq_true _ _ (eq_true hn)).symm⟩
  · rw [K₈.wr, K₂.wr, v₁.wr]
    show ⟨State.addr (layOf P s).fp, frameBytes⟩ :: s.wr = _
    rw [hA, hwr]
    rfl
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide),
      v₃.gpr, g₂ _ (by decide)]; rfl
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide), v₅.gpr, v₄.gpr,
      v₃.other _ (by decide), g₂ _ (by decide)]; rfl
  · rw [v₈.other _ (by decide), v₇.gpr, v₆.mem, hargs 4 (by decide)]; rfl
  · rw [v₈.gpr, v₇.other _ (by decide), v₆.other _ (by decide), h12₅]
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.gpr, hargs 0 (by decide)]; rfl
  · have := saved_off p hp
    rw [hm, f₅'.readW (r := ⟨(layOf P s).B + BitVec.ofNat 64 (24 + p.2), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide)]
    have h₂ := V₂ p hp
    rw [VG.Proof.Mont.off, Offset.add_add] at h₂
    rw [h₂, v₁.other _ (saved_ne12 p hp)]; rfl
  · rw [hm, m₅, show 24 + fDigest = 528 from rfl, Mem.readW_writeW_self32]; rfl
  · change s.mem.readW (State.addr ((layOf P s).sy c.1) + BitVec.ofNat 64 (8 * i)) 64 = c.2.getD i 0
    rw [lay_sy (cs := P.R.coreConsts) s hc]
    exact (tables c hc).1 i hi

theorem low_preserved : ∀ r ∈ preserved, r ∈ Impl.Ecdsa.Rfc6979.Arm.saved.map Prod.fst := by decide

theorem frameBytes_ok :
    0 < frameBytes ∧ frameBytes < 4096 ∧ frameBytes % 8 = 0 ∧ encodable (BitVec.ofNat 32 frameBytes) = true := by
  decide

/-- `vg_ecdsa_<curve>_sign` for `P`'s hash function meets `rfcP P` and keeps
the callee-saved registers and the stack pointer. -/
theorem sign_ok {ns : List String} {s : State} (h : (rfcP P ns).pre s) :
    WP isa (cfgOf P).sign s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (rfcP P ns).post s s' := by
  have hL : (layOf P s).Ok := lay_ok h
  have hN : 536 ≤ s.sp.toNat := hL.nB
  have hk := coreOk_lay P s
  refine WP.alloc frameBytes_ok (by show 512 ≤ _; omega_arith) ?_
  rw [Cfg.body]
  refine WP.seq (WP.mono (entry_ok h) fun t hc => WP.mono (body_ok hL hk hc) fun v hv => ?_)
  obtain ⟨hsp, hs, i, hx⟩ := hv
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · show (freed frameBytes v).gpr r = _
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (low_preserved r hr)
    exact hs p hp
  · show v.sp + BitVec.ofNat 32 frameBytes = s.sp
    rw [hsp]; exact BitVec.sub_add_cancel _ _
  · show match (result P.I s.mem (State.addr (layOf P s).d) (State.addr (layOf P s).dg)).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    have e₂ : P.I.ecdsa.curve = P.R.E.C := by rw [P.ecdsa, P.R.curve]
    rw [e₁, e₂]
    have hr := hx.res
    unfold ResultIs at hr
    show match sigI P (layOf P s) s.mem i with | some rs => _ | none => _
    cases hsig : sigI P (layOf P s) s.mem i <;> rw [hsig] at hr <;>
      exact ⟨by rw [low_word]; exact hr.1, hr.2⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
