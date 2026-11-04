module

import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Loop
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on 32-bit ARM: correctness

As on x86 (`Proof/Ecdsa/Rfc6979/X86/Correct.lean`): the loop leaves it at a
candidate that is suitable or the last (`loop_ok`); before it, `h`, `K`,
`V`, `core`'s digest and the count are as RFC 6979's steps a–g make them
(`stageB_ok` … `stageE_ok`); and the signature of that candidate is RFC
6979's (`result_eq`), for the hash function `P`'s instance of the contract. The frame's allocation, and our caller's registers
saved in it and restored, give the whole function (`sign_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)
open VG.Proof.X25519.Arm (wp_mov op2_reg wp_ldr wp_str)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The loop -/

theorem loop_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
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
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte :=
  Spec.Sha256.bytesAt m₀ (State.addr L.d) P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.H.D 0) (List.replicate P.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.H.D 1)

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.H.D 0
  v : vOfP P L u.mem = List.replicate P.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOfP P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOfP P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

/-- `core`'s digest, unless two `V`s make a candidate: the digest, whose
leftmost `Q` bytes it reads. -/
theorem dgOk_narrow (hL : L.Ok) (hk : CoreOk P L) (hw : P.wide = false) {u : State} (hc : Ctx L g m₀ u) :
    DgOk P L m₀ u.mem := by
  obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
  have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := (P.R.sizesA (P.curveA hw)).2.2.1
  have hD : P.Q ≤ P.I.hashLen := by rw [P.len]; exact hQD
  have hLw : L.wide = false := hk.2.2.1.trans hw
  unfold DgOk
  simp only [dgAddr, hLw, Bool.false_eq_true, ite_false, eOf, hBOf]
  rw [hc.dgBytes hL hD, hashToInt_takeQ hB (by rw [length_bytesAt]),
    List.take_of_length_le (by rw [length_bytesAt]), hashToInt_takeQ hB (by rw [length_bytesAt]; exact hQD),
    ← bytesAt_take _ _ hQD]

theorem stageB_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block ((cfgOf P).prep ++ Cfg.initKV)) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  have hD : P.H.D = P.I.hashLen := P.len.symm
  have nB := hL.nB
  have hb := hL.B_fit
  rw [Cfg.prep, WP.block_append_iff]
  cases hw : P.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := (P.R.sizesA (P.curveA hw)).2.2.1
    have e4 : 4 * P.k = P.Q := hQ8.symm
    have hwc : (cfgOf P).wide = false := hw
    simp only [hwc, Bool.false_eq_true, ite_false]
    obtain ⟨hb₁, hb₂, -, -⟩ := hb_facts hw hk.e_eq
    refine WP.mono (reduce_ok (P := P) hw hk.e_eq hL hc (by rw [e4, ← hD]; exact hQD)) fun u₁ ⟨hc₁, _, hh₁⟩ => ?_
    rw [e4] at hh₁ hb₂
    refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
      ⟨hc₂, ?_, hk₂ _ (by anums), hv₂ _ (by anums), dgOk_narrow hL hk hw hc₂⟩
    simp only [hOf]
    rw [bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith))
      (by omega_arith)]
    rw [hSpec, bits2octets_eqQ hB (by rw [hBOf, length_bytesAt]; exact hQD), hBOf,
      ← bytesAt_take m₀ (State.addr L.dg) hQD, ← hh₁]
    have e := toBytes_ofBytes (Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 P.hB) P.Q)
    rw [length_bytesAt] at e
    exact e.symm
  · have hl := P.R.nBits_len
    have hz := P.wsizes
    have hQD : P.H.D < P.Q := by simpa [RfcHash.wide] using hw
    have hN : 8 * P.H.D < Spec.Ecdsa.nBits P.R.E.C := by
      have : P.H.D < P.R.E.C.len := hQD
      omega_arith
    have hwc : (cfgOf P).wide = true := hw
    have hLw : L.wide = true := hk.2.2.1.trans hw
    have he : L.e = 68 := e68 hk.e_eq hw
    have hb' : P.hB = 240 := hB_wide hw
    simp only [hwc, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (hPrep_ok hL hk.e_eq hw (by rw [← hD]) hc) fun u₁ ⟨hc₁, _, hf₁, hh₁⟩ => ?_
    have hdg₁ : Spec.Sha256.bytesAt u₁.mem (State.addr L.dg) P.H.D =
        Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.H.D := hc₁.dgBytes hL (by rw [← hD])
    rw [hc.dgBytes hL (by rw [← hD])] at hh₁
    have hdis : ∀ {ws : List Region} {m m' : Mem}, Frame ws m m' →
        (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 240, P.Q⟩ r) →
        Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 240) P.Q =
          Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 240) P.Q :=
      fun hf hd => bytesAt_frame hf hd (by omega_arith)
    have hS : hSpec P L m₀ = List.replicate (P.Q - P.H.D) 0 ++ Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.H.D := by
      rw [hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_arith)
        (by show 8 * P.R.E.C.len < _; omega_arith) (by rw [hBOf, length_bytesAt]; exact hN) P.R.n_ne,
        hBOf, length_bytesAt]
    have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.H.D) :=
      (hashToInt_short (h := Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.H.D) (by rw [length_bytesAt]; exact hN)
        P.R.n_ne).1
    have hKV : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 24, 128⟩ : Region)],
        Region.Disjoint ⟨L.B + BitVec.ofNat 64 240, P.Q⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    by_cases hsh : P.R.sh = 0
    · have e : (cfgOf P).xPrep = [] := by simp only [Cfg.xPrep, show (cfgOf P).sh = 0 from hsh, ↓reduceIte]
      rw [e]
      refine WP.block_nil (WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
        ⟨hc₂, ?_, hk₂ _ (by anums), hv₂ _ (by anums), ?_⟩)
      · simp only [hOf, hb']
        rw [hdis hf₂ hKV, hh₁, hS]
      · unfold DgOk
        simp only [dgAddr, hLw, dgO, hsh, ↓reduceIte]
        have hB8 : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
          have := hl.2.2
          show _ = 8 * P.R.E.C.len
          omega_arith
        show Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) P.Q) = _
        rw [hdis hf₂ hKV, hh₁, hashToInt_takeQ hB8 (by simp [length_bytesAt]; omega_arith),
          List.take_of_length_le (by simp [length_bytesAt]; omega_arith), ofBytes_zeros, e₂]
    · refine WP.mono (xPrep_ok hL hk.e_eq hw (by rw [← hD]) hsh hc₁) fun u₂ ⟨hc₂, _, hf₂, hx₂⟩ => ?_
      rw [hdg₁] at hx₂
      refine WP.mono (initKV_ok hL hc₂) fun u₃ ⟨hc₃, hf₃, hv₃, hk₃⟩ =>
        ⟨hc₃, ?_, hk₃ _ (by anums), hv₃ _ (by anums), ?_⟩
      · simp only [hOf, hb']
        rw [hdis hf₃ hKV, hdis hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_scr (by rw [he]; omega_arith) (by decide)
          · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)), hh₁, hS]
      · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
        have hX : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 312) P.Q = Spec.Weierstrass.toBytes P.Q
            (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.H.D) * 2 ^ P.R.sh) := by
          rw [bytesAt_frame hf₃ (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by omega_arith), hx₂]
        have hlt : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.H.D) * 2 ^ P.R.sh <
            2 ^ (8 * P.Q) := by
          have := ofBytes_lt (Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.H.D)
          rw [length_bytesAt] at this
          calc _ < 2 ^ (8 * P.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
            _ ≤ 2 ^ (8 * P.Q) := by
              rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega_arith) (by omega_arith)
        have hl₁ : (Spec.Weierstrass.toBytes P.Q
            (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.H.D) * 2 ^ P.R.sh)).length =
            P.Q := by
          simp [Spec.Weierstrass.toBytes]
        have e₁ : Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 312) P.Q) =
            Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.H.D) := by
          rw [hX, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_arith) (by rw [hl₁]),
            List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
            show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
            Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
        unfold DgOk
        simp only [dgAddr, hLw, dgO, hsh, ↓reduceIte]
        show Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 312) P.Q) = _
        rw [e₁, e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_kvw (hL : L.Ok) (hLe : L.e = P.e) {m m' : Mem} (hf : Frame (KVW L) m m') :
    hOf P L m' = hOf P L m := by
  have hz := P.wsizes
  have hb := hL.B_fit
  simp only [hOf]
  cases hw : P.wide
  · obtain ⟨hQ8, -, -⟩ := P.sizesA hw
    obtain ⟨hb₁, hb₂, -, -⟩ := hb_facts hw hLe
    rw [← hQ8] at hb₂
    refine bytesAt_frame hf (fun r hr => ?_) (by omega_arith)
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_SCR hb₂
    · exact Offset.disjoint_base _ hb₁ (by omega_arith)
  · have he : L.e = 68 := e68 hLe hw
    rw [hB_wide hw]
    refine bytesAt_frame hf (fun r hr => ?_) (by omega_arith)
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_SCR (by rw [he]; omega_arith)
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk.2.2.2 (hok_of hk) hc (b := 0) (by decide)) fun u' ⟨hc', _, hf', hk', hv'⟩ =>
    ⟨hc', (hOf_kvw hL hk.e_eq hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hk hf' kvw_apart⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk.2.2.2 (hok_of hk) hc (b := 1) (by decide)) fun u' ⟨hc', _, hf', hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hk hf' kvw_apart⟩

theorem stageE_ok {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok (P := P) hc) fun u' ⟨hc', hm', hn'⟩ => ⟨hc', P.tries_pos, hm' ▸ hq.k, hm' ▸ hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _), hm' ▸ hq.dg⟩

/-- After the wiping: the result, and our caller's registers. -/
structure Fin (P : RfcHash) (L : Lay P.I.hashLen) (g : Reg → BitVec 32) (m₀ : Mem) (u : State) : Prop where
  wr : u.wr = [L.FR, L.OUT, L.SCR]
  sp : u.sp = L.fp
  saved : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, u.gpr p.1 = g p.1
  exit : ∃ i, Exit P L m₀ i u

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block (Cfg.wipe (cfgOf P).wide (cfgOf P).hHigh)) u (Fin P L g m₀) := by
  have hw : (cfgOf P).wide = L.wide := hk.2.2.1.symm
  have hh : (cfgOf P).hHigh = L.hHigh := hk.2.1.2.1.symm
  have := L.he
  have := hL.B_fit
  rw [hw, hh]
  exact WP.mono (wipe_ok hL hc) fun _ ⟨_, hwr, hsp, hs, ha, hf⟩ => ⟨hwr.trans hc.wr, hsp.trans hc.sp, hs, i,
    hx.lt, hx.fails, hx.last, hx.res.keep ha (bytesAt_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by anums))⟩

/-- The body, after `h`, `V` and `K`. -/
theorem rest_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hq : QB P L m₀ t) :
    WP isa (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne .ne) (.block (Cfg.wipe (cfgOf P).wide (cfgOf P).hHigh)))))) t (Fin P L g m₀) :=
  WP.seq (WP.mono (stageC_ok hL hk hc hq) fun _ ⟨h₂, q₂⟩ =>
    WP.seq (WP.mono (stageD_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
      WP.seq (WP.mono (stageE_ok h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
        WP.seq (WP.mono (loop_ok hL hk h₄ q₄) fun _ ⟨h₅, _, q₅⟩ => stageG_ok hL hk h₅ q₅))))

/-! ## RFC 6979's result -/

/-- One `V` makes a candidate, or `m` if the hash is shorter than the scalars. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = P.nb := by
  have hs := P.sizes
  have hl := P.R.nBits_len
  rw [Spec.Ecdsa.Rfc6979.blocks]
  cases hw : P.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have h₂ := (P.R.sizesA (P.curveA hw)).2.2.1
    have hz := P.wsizes
    simp only [RfcHash.nb, hw, Bool.false_eq_true, ite_false]
    exact Nat.div_eq_of_lt_le (by simp only [RfcHash.Q] at *; omega_arith)
      (by simp only [RfcHash.Q] at *; omega_arith)
  · simp only [RfcHash.nb, hw, ite_true, Cfg.m]
    show _ = (8 * P.R.E.C.len - P.R.sh + 8 * P.H.D - 1) / (8 * P.H.D)
    rw [hl.2.2, show 8 * P.R.E.C.len - (8 * P.R.E.C.len - Spec.Ecdsa.nBits P.R.E.C) = Spec.Ecdsa.nBits P.R.E.C by
      omega_arith]

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ (State.addr L.d) (State.addr L.dg) =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.SH.H P.H.D (xOf P L m₀) (eOf P L m₀) K V P.I.tries
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
def exitAt (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  if (result P.I m₀ (State.addr L.d) (State.addr L.dg)).2 = 0 then P.I.tries - 1 else (result P.I m₀ (State.addr L.d) (State.addr L.dg)).2 - 1

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
  rfcArm P.I (240 + 4 * P.e) P.R.coreConsts (tabFacts P.H P.f) ns

/-- The layout of a state meeting `rfcP P`. -/
abbrev layP (P : RfcHash) (s : State) : Lay P.I.hashLen :=
  lay P.I.hashLen P.I.ecdsa.curve.len P.wide P.R.hHigh P.H P.f s P.R.coreConsts

/-- Stack argument `i`, through the frame's base. -/
theorem fp_arg {dn : Nat} (L : Lay dn) (i : Nat) :
    L.fp + BitVec.ofNat 32 (216 + 4 * L.e + 4 * i) = L.sp + BitVec.ofNat 32 (4 * i) := by
  rw [BitVec.ofNat_add (216 + 4 * L.e) (4 * i), ← BitVec.add_assoc]
  unfold Lay.fp
  rw [BitVec.sub_add_cancel]

/-- The prologue: our caller's registers into the frame, the table to `r4`,
`out` to the frame, and the pointers to the registers that keep them. -/
theorem entry_ok {ns : List String} {s : State} (h : (rfcP P ns).pre s) :
    WP isa (.block (cfgOf P).prologue) (allocated (cfgOf P).fb s) (Ctx (layP P s) s.gpr s.mem) := by
  apply WP.of_syms
  have hL : (layP P s).Ok := lay_ok h
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, tables, tabF⟩ := h
  have hA : State.addr (layP P s).fp = (layP P s).B + BitVec.ofNat 64 24 := hL.fpA0
  have hb := hL.B_fit
  have he := (layP P s).he
  have hna : s.sp.toNat + 8 ≤ 2 ^ 32 := hL.na
  have hAR : argsR s = (layP P s).ARGS := by
    show (⟨State.addr (s.sp + BitVec.ofNat 32 (4 * 0)), 8⟩ : Region) = ⟨State.addr s.sp, 8⟩
    rw [Nat.mul_zero, BitVec.add_zero]
  have hfb : (cfgOf P).fb = 216 + 4 * (layP P s).e := rfl
  simp only [Cfg.prologue, List.cons_append]
  refine wp_addSp (d := .r12) (imm := 0) (by decide) fun u₁ v₁ => ?_
  have h12 : u₁.gpr .r12 = (layP P s).fp := by rw [v₁.gpr, BitVec.add_zero]; rfl
  have hs : VG.Proof.Mont.Arm.Scr u₁ (State.addr (layP P s).fp) 216 :=
    ⟨by rw [h12], ⟨(cfgOf P).fb, by rw [hfb]; omega_arith, by rw [hfb]; omega_arith,
      by rw [v₁.wr]; exact List.mem_cons_self⟩,
      by rw [hA, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith, by omega_arith⟩
  rw [WP.block_append_iff]
  refine WP.mono (Proof.Weierstrass.Arm.strs_ok hs _ (fun p hp => (saved_off p hp).2) saved_pairwise)
    fun u₂ ⟨K₂, O₂, V₂⟩ => ?_
  have hs₂ := hs.of_rest K₂ (by simp)
  have g12 : u₂.gpr .r12 = (layP P s).fp := (K₂.gpr _ (by simp)).trans h12
  -- What the saves changed: the frame's words 180 … 216.
  have hF₂ : Frame [(layP P s).STK] s.mem u₂.mem := by
    rw [show s.mem = u₁.mem from v₁.mem.symm]
    refine (Outs.frame O₂ (n := 216) fun r hr => ?_).sub fun r hr => ?_
    · simp only [List.mem_map] at hr
      obtain ⟨q, hq, rfl⟩ := hr
      exact (saved_off q hq).2
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨(layP P s).STK, by simp, by rw [hA]; exact Offset.sub_base _ (by omega_arith)⟩
  have hArg : ∀ i < 2, stackArgAddr s i = State.addr (layP P s).sp + BitVec.ofNat 64 (4 * i) := fun i hi =>
    addr_add (by show s.sp.toNat + 4 * i < _; omega_arith)
  have hRd : ∀ {u : State}, u.rd = s.rd → ∀ i < 2, InRegions (u.rd ++ u.wr) (stackArgAddr s i) 4 := by
    intro u hu i hi
    refine ⟨(layP P s).ARGS, ?_, by rw [hArg i hi]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    rw [hu, hrd, hAR]
    simp
  have hArgRd : ∀ {m : Mem}, Frame [(layP P s).STK] s.mem m → ∀ i < 2,
      m.readW (stackArgAddr s i) 32 = stackArg s i := fun hf i hi =>
    hf.readW (r := (layP P s).ARGS) (by rw [hArg i hi]; exact Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.ak) (by decide)
  -- The table, stack argument 1, to `r4`.
  refine wp_ldr (a := stackArgAddr s 1) (by rw [hfb]; omega_arith)
    (by rw [g12, hfb, show 216 + 4 * (layP P s).e + 4 = 216 + 4 * (layP P s).e + 4 * 1 from rfl, fp_arg]; rfl)
    (hRd (by rw [K₂.rd, v₁.rd]; rfl) 1 (by decide)) fun u₃ v₃ => ?_
  have hs₃ := hs₂.of_rest (v₃.rest (ws := [.r4]) (by simp)) (by simp)
  -- `out` to the frame.
  refine wp_str (hs₃.off_lt (d := fOut) (by decide)) (hs₃.ea (by decide)) (hs₃.write (n := 4) (by decide))
    fun u₄ v₄ => ?_
  have hoff : VG.Proof.Mont.off (State.addr (layP P s).fp) fOut = (layP P s).B + BitVec.ofNat 64 200 := by
    rw [hA, VG.Proof.Mont.off, Offset.add_add]; rfl
  have hF₄ : Frame [(layP P s).STK] s.mem u₄.mem := by
    rw [v₄.mem, v₃.mem]
    refine hF₂.writeW (List.mem_singleton_self _) _ ?_
    rw [hoff]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hs₄ := hs₃.of_rest (v₄.rest []) (by simp)
  refine wp_mov (op2_reg _ _) fun u₅ v₅ => wp_mov (op2_reg _ _) fun u₆ v₆ => ?_
  -- `scratch`, stack argument 0, to `r11`.
  have g12₆ : u₆.gpr .r12 = (layP P s).fp := by
    rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide), g12]
  refine wp_ldr (a := stackArgAddr s 0) (by rw [hfb]; omega_arith)
    (by rw [g12₆, hfb, show 216 + 4 * (layP P s).e = 216 + 4 * (layP P s).e + 4 * 0 from rfl, fp_arg]; rfl)
    (hRd (by rw [v₆.rd, v₅.rd, v₄.rd, v₃.rd, K₂.rd, v₁.rd]; rfl) 0 (by decide)) fun u₇ v₇ => ?_
  refine wp_mov (op2_reg _ _) fun u₈ v₈ => WP.block_nil (fun syEnd => ?_)
  have hm₈ : u₈.mem = u₄.mem := by rw [v₈.mem, v₇.mem, v₆.mem, v₅.mem]
  have hm₄ : u₄.mem = u₃.mem.writeW (VG.Proof.Mont.off (State.addr (layP P s).fp) fOut) (u₃.gpr .r0) := v₄.mem
  have g₂ : ∀ r, r ≠ .r12 → u₂.gpr r = s.gpr r := fun r hr => by rw [K₂.gpr r (by simp), v₁.other _ hr]; rfl
  have hr0 : u₃.gpr .r0 = s.gpr .r0 := by rw [v₃.other _ (by decide), g₂ _ (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun p hp => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, K₂.rd, v₁.rd, lay_tbls]
    show s.rd = _
    rw [hrd, hAR]
    rfl
  · rw [v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, K₂.wr, v₁.wr]
    show ⟨State.addr (layP P s).fp, (cfgOf P).fb⟩ :: s.wr = _
    rw [hA, hwr]
    rfl
  · rw [v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, K₂.sp, v₁.sp]; rfl
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr,
      v₃.gpr, hArgRd hF₂ 1 (by decide)]; rfl
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.other _ (by decide), v₅.gpr, v₄.gpr,
      v₃.other _ (by decide), g₂ _ (by decide)]; rfl
  · rw [v₈.other _ (by decide), v₇.other _ (by decide), v₆.gpr, v₅.other _ (by decide), v₄.gpr,
      v₃.other _ (by decide), g₂ _ (by decide)]; rfl
  · rw [v₈.gpr, v₇.other _ (by decide), g12₆]
  · rw [v₈.other _ (by decide), v₇.gpr, show u₆.mem = u₄.mem by rw [v₆.mem, v₅.mem], hArgRd hF₄ 0 (by decide)]
    rfl
  · have ho := saved_off p hp
    rw [hm₈, hm₄, Frame.readW (rs := [⟨VG.Proof.Mont.off (State.addr (layP P s).fp) fOut, 4⟩])
      ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
      (r := ⟨(layP P s).B + BitVec.ofNat 64 (24 + p.2), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [hoff]
        exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide),
      v₃.mem, ← Offset.add_add, ← hA, ← VG.Proof.Mont.off, V₂ p hp, v₁.other _ (saved_ne12 p hp)]; rfl
  · rw [hm₈, hm₄, ← hoff, Mem.readW_writeW_self32, hr0]; rfl
  · rw [hm₈]; exact hF₄.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, sub_refl _⟩
  · intro c hc
    rw [syEnd]
    exact (lay_sy P.I.hashLen P.I.ecdsa.curve.len P.wide P.R.hHigh P.H P.f s P.R.coreConsts hc).symm
  · intro c hc i hi
    change s.mem.readW (State.addr ((layP P s).sy c.1) + BitVec.ofNat 64 (8 * i)) 64 = c.2.getD i 0
    rw [lay_sy P.I.hashLen P.I.ecdsa.curve.len P.wide P.R.hHigh P.H P.f s P.R.coreConsts hc]
    exact (tables c hc).1 i hi
  · rw [syEnd]; exact tabF.1
  · rw [syEnd]; exact tabF.2
  · rw [syEnd]; exact fun n hn => lay_fa P.I.hashLen P.I.ecdsa.curve.len P.wide P.R.hHigh P.H P.f s P.R.coreConsts n hn

theorem low_preserved : ∀ r ∈ preserved, r ∈ Impl.Ecdsa.Rfc6979.Arm.saved.map Prod.fst := by decide

theorem coreOk_lay (P : RfcHash) (s : State) : CoreOk P (layP P s) :=
  ⟨P.curveLen, ⟨fun hw => by show P.Q ≤ P.I.hashLen; rw [P.len]; exact (P.sizesA hw).2.2, rfl, rfl⟩, rfl, rfl, rfl⟩

theorem frameBytes_ok (wide hHigh : Bool) :
    0 < frameBytes wide hHigh ∧ frameBytes wide hHigh < 4096 ∧ frameBytes wide hHigh % 8 = 0 ∧
      encodable (BitVec.ofNat 32 (frameBytes wide hHigh)) = true := by
  cases wide <;> cases hHigh <;> decide

/-- `sign` for `P`'s hash function meets `rfcP P` and keeps the
callee-saved registers and the stack pointer. -/
theorem sign_ok {ns : List String} {s : State} (h : (rfcP P ns).pre s) :
    WP isa (cfgOf P).sign s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (rfcP P ns).post s s' := by
  have hL : (layP P s).Ok := lay_ok h
  have hN : 240 + 4 * P.e ≤ s.sp.toNat := hL.nB
  have hk := coreOk_lay P s
  have hfb : (cfgOf P).fb = 216 + 4 * P.e := rfl
  refine WP.alloc (frameBytes_ok (cfgOf P).wide (cfgOf P).hHigh) (by rw [hfb]; omega_arith) ?_
  rw [Cfg.body, List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok h) fun t hc => WP.mono (stageB_ok hL hk hc) fun u ⟨hu, hq⟩ => ?_
  refine WP.mono (rest_ok hL hk hu hq) fun v ⟨hwr, hsp, hs, i, hx⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · show (freed (cfgOf P).fb v).gpr r = _
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (low_preserved r hr)
    exact hs p hp
  · show v.sp + BitVec.ofNat 32 (cfgOf P).fb = s.sp
    rw [hsp]; exact BitVec.sub_add_cancel _ _
  · show match (result P.I s.mem (State.addr (layP P s).d) (State.addr (layP P s).dg)).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    have e₂ : P.I.ecdsa.curve = P.R.E.C := by rw [P.ecdsa, P.R.curve]
    rw [e₁, e₂]
    have hr := hx.res
    unfold ResultIs at hr
    show match sigI P (layP P s) s.mem i with | some rs => _ | none => _
    cases hsig : sigI P (layP P s) s.mem i <;> rw [hsig] at hr <;>
      exact ⟨by rw [low_word]; exact hr.1, hr.2⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
