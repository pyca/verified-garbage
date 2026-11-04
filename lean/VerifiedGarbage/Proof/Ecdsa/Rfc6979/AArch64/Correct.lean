module

import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Loop
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-!
# Deterministic ECDSA on AArch64: correctness

The loop leaves it at a candidate that is suitable or the last (`loop_ok`);
before it, `h` (or, if two `V`s make a candidate, the zero bytes and the
digest after `d` in the messages of steps d and f), `K`, `V`, `core`'s
digest and the count are as RFC 6979's steps a–g make them (`stageB_ok` …
`stageE_ok`); and the signature of that candidate is RFC 6979's
(`result_eq`), for the hash function `P`'s instance of the contract.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The loop -/

theorem loop_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne (.nonzero .x .x12)) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
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
    Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.SH.H P.H.D x hB =
      let K₁ := P.mac (List.replicate P.H.D 0) (List.replicate P.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets P.R.E.C x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_eq, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m₀ : Mem) : List Byte :=
  Spec.Sha256.bytesAt m₀ L.d P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.H.D 0) (List.replicate P.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.H.D 1)

/-- After step c: `d ‖ h` as the messages of steps d and f have it, `V = 0x01…`,
`K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.H.D 0
  v : vOf P L u.mem = List.replicate P.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

/-- `core`'s digest, unless the hash is shorter than the scalars: the
digest, whose leftmost `Q` bytes it reads. -/
theorem dgOk_narrow (hL : L.Ok) (hw : P.wide = false) {u : State} (hc : Ctx L g m₀ u) :
    DgOk P L m₀ u.mem := by
  obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
  have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
    have h₁ := (P.R.sizesA (P.curveA hw)).2.1; have h₂ := (P.R.sizesA (P.curveA hw)).2.2.1
    show _ = 8 * P.R.E.C.len; omega_arith
  have hD : P.Q ≤ P.I.hashLen := by rw [P.len]; exact hQD
  unfold DgOk
  simp only [dgAddr, hw, Bool.false_eq_true, ite_false, eOf, hBOf]
  rw [hc.dgBytes hL hD, hashToInt_takeQ hB (by rw [length_bytesAt]),
    List.take_of_length_le (by rw [length_bytesAt]), hashToInt_takeQ hB (by rw [length_bytesAt]; exact hQD),
    ← bytesAt_take _ _ hQD]

theorem stageB_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (h1 : u.gpr .x1 = L.dg)
    (h0 : P.wide = true → u.gpr .x0 = L.scr) :
    WP isa (.block (cfgOf P).prep) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  have hD : P.H.D = P.I.hashLen := P.len.symm
  have nB := hL.nB
  rw [Cfg.prep, WP.block_append_iff]
  cases hw : P.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
      have h₁ := (P.R.sizesA (P.curveA hw)).2.1; have h₂ := (P.R.sizesA (P.curveA hw)).2.2.1
      show _ = 8 * P.R.E.C.len; omega_arith
    have hwc : (cfgOf P).wide = false := hw
    have hb₀ := hB_ge P
    obtain ⟨-, -, hb₃, -, -, -⟩ := hb_facts hw hk.e_eq
    simp only [hwc, Bool.false_eq_true, ite_false]
    refine WP.mono (reduce_ok (P := P) hw hk.e_eq hL hc h1 (by rw [← hD]; exact hQD)) fun u₁ ⟨hc₁, _, hh₁⟩ => ?_
    refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
      ⟨hc₂, ?_, hk₂ _ (by anums), hv₂ _ (by anums), dgOk_narrow hL hw hc₂⟩
    have e₁ : hOf P L u₂.mem = hOf P L u₁.mem := bytesAt_frame (p := L.B + BitVec.ofNat 64 P.hB) (n := P.Q) hf₂
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      (by omega_arith)
    rw [e₁, hOf, hh₁]
    rw [hSpec, bits2octets_eqQ hB (by rw [hBOf, length_bytesAt]; exact hQD), hBOf,
      ← bytesAt_take m₀ L.dg hQD]
  · have hl := P.R.nBits_len
    have hz := P.sizes
    have hQD : P.H.D < P.Q := by simpa [RfcHash.wide] using hw
    have hN : 8 * P.H.D < Spec.Ecdsa.nBits P.R.E.C := by
      have : P.H.D < P.R.E.C.len := hQD
      omega_arith
    have hwc : (cfgOf P).wide = true := hw
    have he : L.e = 272 := e272 hk.2.2.1 hw
    have hb : P.hB = 240 := by simp only [RfcHash.hB, hw, Bool.true_or, ite_true]
    simp only [hwc, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (hPrep_ok hL hk.2.2.1 hw (by rw [← hD]) hc h1) fun u₁ ⟨hc₁, hg₁, h15₁, hf₁, hh₁⟩ => ?_
    have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt m₀ L.dg P.H.D :=
      hc₁.dgBytes hL (by rw [← hD])
    rw [hc.dgBytes hL (by rw [← hD])] at hh₁
    -- `h`, kept by what follows it: `K`, `V` and the digest for `core`.
    have hdis : ∀ {ws : List Region} {m m' : Mem}, Frame ws m m' →
        (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 240, P.Q⟩ r) →
        Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 240) P.Q = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 240) P.Q :=
      fun hf hd => bytesAt_frame hf hd (by anums)
    -- `h` is `bits2octets` of the digest, and `core`'s digest has the digest's number.
    have hS : hSpec P L m₀ = List.replicate (P.Q - P.H.D) 0 ++ Spec.Sha256.bytesAt m₀ L.dg P.H.D := by
      rw [hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_arith)
        (by show 8 * P.R.E.C.len < _; omega_arith) (by rw [hBOf, length_bytesAt]; exact hN) P.R.n_ne,
        hBOf, length_bytesAt]
    have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) :=
      (hashToInt_short (h := Spec.Sha256.bytesAt m₀ L.dg P.H.D) (by rw [length_bytesAt]; exact hN) P.R.n_ne).1
    have hKV : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 16, 128⟩ : Region)],
        Region.Disjoint ⟨L.B + BitVec.ofNat 64 240, P.Q⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl; exact Offset.disjoint _ (by omega) (by anums) (by anums)
    by_cases hsh : P.R.sh = 0
    · have e : (cfgOf P).xPrep = [] := by simp only [Cfg.xPrep, show (cfgOf P).sh = 0 from hsh, ite_true]
      rw [e]
      refine WP.block_nil (WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
        ⟨hc₂, ?_, hk₂ _ (by anums), hv₂ _ (by anums), ?_⟩)
      · simp only [hOf, hb]
        rw [hdis hf₂ hKV, hh₁, hS]
      · unfold DgOk
        simp only [dgAddr, hw, hsh, ite_true]
        have hB8 : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
          have := hl.2.2
          show _ = 8 * P.R.E.C.len
          omega_arith
        rw [hdis hf₂ hKV, hh₁, hashToInt_takeQ hB8 (by simp [length_bytesAt]; omega_arith),
          List.take_of_length_le (by simp [length_bytesAt]; omega_arith), ofBytes_zeros, e₂]
    · refine WP.mono (xPrep_ok hL hk.2.2.1 (by rw [← hD]) hsh hc₁
        ((hg₁ _ (by decide) (by decide) (by decide) (by decide)).trans h1)
        ((hg₁ _ (by decide) (by decide) (by decide) (by decide)).trans (h0 hw)) h15₁)
        fun u₂ ⟨hc₂, hf₂, hx₂⟩ => ?_
      rw [hdg₁] at hx₂
      refine WP.mono (initKV_ok hL hc₂) fun u₃ ⟨hc₃, hf₃, hv₃, hk₃⟩ =>
        ⟨hc₃, ?_, hk₃ _ (by anums), hv₃ _ (by anums), ?_⟩
      · simp only [hOf, hb]
        rw [hdis hf₃ hKV, hdis hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_scr (by rw [he]; anums) (by decide)
          · exact Offset.disjoint _ (by anums) (by anums) (by anums)), hh₁, hS]
      · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
        have hX : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 312) P.Q = Spec.Weierstrass.toBytes P.Q
            (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ P.R.sh) := by
          rw [bytesAt_frame hf₃ (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact Offset.disjoint _ (by omega_arith) (by anums) (by anums)) (by anums), hx₂]
        have hlt : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ P.R.sh < 2 ^ (8 * P.Q) := by
          have := ofBytes_lt (Spec.Sha256.bytesAt m₀ L.dg P.H.D)
          rw [length_bytesAt] at this
          calc _ < 2 ^ (8 * P.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
            _ ≤ 2 ^ (8 * P.Q) := by
              rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega_arith) (by omega_arith)
        have hl₁ : (Spec.Weierstrass.toBytes P.Q
            (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ P.R.sh)).length = P.Q := by
          simp [Spec.Weierstrass.toBytes]
        have e₁ : Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 312) P.Q) =
            Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) := by
          rw [hX, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_arith) (by rw [hl₁]),
            List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
            show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
            Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
        unfold DgOk
        simp only [dgAddr, hw, hsh, ite_true, ite_false]
        rw [e₁, e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_kvw (hL : L.Ok) (hLe : L.e = P.e) {m m' : Mem} (hf : Frame (KVW L) m m') : hOf P L m' = hOf P L m := by
  have hs := P.sizes
  have nB := hL.nB
  simp only [hOf]
  cases hw : P.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    obtain ⟨-, -, hb₃, -, -, -⟩ := hb_facts hw hLe
    have hb₀ := hB_ge P
    have hb₉ := hB_le P
    refine bytesAt_frame hf (fun r hr => ?_) (by omega_arith)
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_SCR (by omega_arith)
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · have he : L.e = 272 := e272 hLe hw
    have hb : P.hB = 240 := by simp only [RfcHash.hB, hw, Bool.true_or, ite_true]
    rw [hb]
    refine bytesAt_frame hf (fun r hr => ?_) (by anums)
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_SCR (by rw [he]; anums)
    · exact Offset.disjoint_base _ (by omega) (by anums)

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc 0) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨hc', (hOf_kvw hL hk.2.2.1 hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hk hf' kvw_apart⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc 1) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hk hf' kvw_apart⟩

theorem stageE_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', P.tries_pos,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _),
    hq.dg.frameOf hL hk hf' fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [DgApart]⟩

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block (cfgOf P).wipe) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' := by
  have := L.he
  have := hL.nB
  exact WP.mono (wipe_ok hL hk.2.2.1 hc) fun _ ⟨hc₇, ha₇, hf₇⟩ => ⟨hc₇, hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by anums))⟩

/-- The frame's body, once the arguments are saved. -/
theorem body_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block (cfgOf P).digestPtr)
      (.seq (.block (cfgOf P).prep)
      (.seq ((cfgOf P).rekeyFull 0)
      (.seq ((cfgOf P).rekeyFull 1)
      (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne (.nonzero .x .x12))
        (.block (cfgOf P).wipe))))))) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' :=
  WP.seq (WP.mono (digestPtr_ok hL hc) fun _ ⟨h₀, _, h1, h0⟩ =>
    WP.seq (WP.mono (stageB_ok hL hk h₀ h1 h0) fun _ ⟨h₁, q₁⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
          WP.seq (WP.mono (stageE_ok hL hk h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
            WP.seq (WP.mono (loop_ok hL hk h₄ q₄) fun _ ⟨h₅, i, q₅⟩ =>
              WP.mono (stageG_ok hL hk h₅ q₅) fun _ ⟨h₆, q₆⟩ => ⟨h₆, i, q₆⟩))))))

/-! ## RFC 6979's result -/

/-- One `V` makes a candidate, or `m` if the hash is shorter than the scalars. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = P.nb := by
  have hs := P.sizes
  have hl := P.R.nBits_len
  rw [Spec.Ecdsa.Rfc6979.blocks]
  cases hw : P.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have h₂ := (P.R.sizesA (P.curveA hw)).2.2.1
    simp only [RfcHash.nb, hw, Bool.false_eq_true, ite_false]
    exact Nat.div_eq_of_lt_le (by simp only [RfcHash.Q, RfcHash.w] at *; omega_arith)
      (by simp only [RfcHash.Q, RfcHash.w] at *; omega_arith)
  · simp only [RfcHash.nb, hw, ite_true, Cfg.m]
    show _ = (8 * P.R.E.C.len - P.R.sh + 8 * P.H.D - 1) / (8 * P.H.D)
    rw [hl.2.2, show 8 * P.R.E.C.len - (8 * P.R.E.C.len - Spec.Ecdsa.nBits P.R.E.C) = Spec.Ecdsa.nBits P.R.E.C by
      omega_arith]

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.SH.H P.H.D (xOf P L m₀) (eOf P L m₀) K V P.I.tries
      else (none, 0) := by
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve, P.hash, P.len,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by have := hx.lt; omega_arith) hx.fails,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by have := hx.lt; omega_arith]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
    | none =>
      have h7 : i + 1 = P.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs, show P.I.tries - 1 - i = 0 by omega]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-! ## How many candidates -/

theorem ite_le_of_not {c : Prop} [Decidable c] {a b i : Nat} (hc : ¬c) (hb : b ≤ i) :
    (if c then a else b) ≤ i := by
  simp only [hc, ite_false]; exact hb

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : Nat :=
  if (result P.I m₀ L.d L.dg).2 = 0 then P.I.tries - 1 else (result P.I m₀ L.d L.dg).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {i : Nat} (hi : i < P.I.tries) (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < P.I.tries) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by omega_arith) hf,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by omega_arith]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs]
      by_cases h7 : i + 1 < P.I.tries
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.SH.H) (hlen := P.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.I.tries - 2 - i)
          (K := (stepB P.ok.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
        rw [show P.I.tries - 1 - i = P.I.tries - 2 - i + 1 by omega_arith]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega_arith
      · rw [show P.I.tries - 1 - i = 0 by omega_arith]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega) (by omega)
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega_arith

/-! ## The whole function -/

/-- The contract the code for `P`'s hash function is proven against, with
`P`'s table and the functions `ns`' addresses public. -/
abbrev rfcP (P : RfcHash) (ns : List String) : Contract isa :=
  rfcAArch64 P.R.E P.I (256 + P.e) (tabFacts P.H.stream P.f) ns

theorem coreOk_lay (P : RfcHash) (s : State) :
    CoreOk P (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E P.e P.e_eq P.H.stream P.f s) :=
  ⟨P.curveLen, fun hw => by show P.Q ≤ P.I.hashLen; rw [P.len]; exact (P.sizesA hw).2.2, rfl, rfl, rfl⟩

/-- `sign` for `P`'s hash function meets `rfcP P` and keeps the callee-saved
registers and the stack pointer. -/
theorem sign_ok {ns : List String} {s : State} (h : (rfcP P ns).pre s) :
    WP isa (cfgOf P).sign s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (rfcP P ns).post s s' := by
  have hL := lay_ok (he := P.e_eq) h
  have hN : 256 + P.e ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk := coreOk_lay P s
  have he : P.e ≤ 272 := by anums
  have hfb : (cfgOf P).frameBytes = 224 + P.e := frameBytes_eq P
  have hfa : 0 < (cfgOf P).frameBytes ∧ (cfgOf P).frameBytes < 4096 ∧ (cfgOf P).frameBytes % 16 = 0 := by
    rw [hfb]; rcases P.e_eq with h | h | h <;> rw [h] <;> decide
  have hfe : 16 + (cfgOf P).frameBytes =
      240 + (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E P.e P.e_eq P.H.stream P.f s).e := by
    rw [hfb]; show 16 + (224 + P.e) = 240 + P.e; omega_arith
  have hft : 16 + ((cfgOf P).frameBytes + 16) = 256 + P.e := by rw [hfb]; omega_arith
  refine WP.frame (by omega_arith) (WP.alloc hfa ?_ ?_)
  · show (cfgOf P).frameBytes ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_arith), hfb]
    show 224 + P.e ≤ s.sp.toNat - 16
    omega_arith
  · rw [hfb]
    show WP isa (cfgOf P).body (entered P.e s) _
    rw [Cfg.body]
    refine WP.seq (WP.mono (entry_ok (he := P.e_eq) h) fun t hc => ?_)
    refine WP.mono (body_ok hL hk hc) fun u ⟨hu, i, hx⟩ => ?_
    have lr : u.mem.read (u.sp + BitVec.ofNat 64 (224 + P.e)) 8 = s.gpr .x30 := by
      rw [hu.sp, Offset.add_add, read8, ← hfb, hfe]; exact hu.lr
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · show ((freed (224 + P.e) u).write .x .x30 (u.mem.read (u.sp + BitVec.ofNat 64 (224 + P.e)) 8)).gpr r = _
      rw [lr, RegUpd.gpr_write]
      by_cases h30 : r = .x30
      · subst r; simp only [ite_true, BitVec.setWidth_eq]
      · simp only [h30, ite_false]
        exact hu.cs r hr h30
    · show u.sp + BitVec.ofNat 64 (224 + P.e) + BitVec.ofNat 64 16 = s.sp
      rw [hu.sp, Offset.add_add, Offset.add_add, ← hfb, hft]
      exact BitVec.sub_add_cancel _ _
    · show match (result P.I s.mem (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E P.e P.e_eq P.H.stream P.f s).d
          (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E P.e P.e_eq P.H.stream P.f s).dg).1 with
        | some rs => _ | none => _
      have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
      have e₂ : Spec.Ecdsa.encode P.I.ecdsa.curve = Spec.Ecdsa.encode P.R.E.C := by rw [P.ecdsa, P.R.curve]
      rw [result_eq hx, e₁, e₂]
      exact hx.res.keep (by
        show ((freed (224 + P.e) u).write .x .x30 (u.mem.read (u.sp + BitVec.ofNat 64 (224 + P.e)) 8)).gpr .x0 = _
        exact RegUpd.gpr_write_of_ne _ _ _ (by decide)) rfl

end VG.Proof.Ecdsa.Rfc6979.AArch64
