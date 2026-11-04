module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Loop
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.RsaPss.X86.NoSp

/-!
# Deterministic ECDSA on x86 (32-bit): correctness

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Correct.lean`): the loop leaves it
at a candidate that is suitable or the last (`loop_ok`); before it, `h`, `K`,
`V`, `core`'s digest and the count are as RFC 6979's steps a–g make them
(`stageB_ok` … `stageE_ok`); and the signature of that candidate is RFC
6979's (`result_eq`), for the hash function `P`'s instance of the contract.
The frame's allocation, our caller's registers saved and restored, and the
return address kept give the whole function (`sign_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

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
abbrev dB (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.H.D 0) (List.replicate P.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.H.D 1)

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.H.D 0
  v : vOf P L u.mem = List.replicate P.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

/-- `core`'s digest, unless two `V`s make a candidate: the digest, whose
leftmost `Q` bytes it reads. -/
theorem dgOk_narrow (hL : L.Ok) (hk : CoreOk P L) (hw : P.wide = false) {u : State} (hc : Ctx L g m₀ u) :
    DgOk P L m₀ u.mem := by
  obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
  have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
    have h₁ := (P.R.sizesA (P.curveA hw)).2.1; have h₂ := (P.R.sizesA (P.curveA hw)).2.2.1
    show _ = 8 * P.R.E.C.len; omega_arith
  have hD : P.Q ≤ P.I.hashLen := by rw [P.len]; exact hQD
  have hLw : L.wide = false := hk.2.2.1.trans hw
  unfold DgOk
  simp only [dgAddr, hLw, Bool.false_eq_true, ite_false, eOf, hBOf]
  rw [hc.dgBytes hL hD, hashToInt_takeQ hB (by rw [length_bytesAt]),
    List.take_of_length_le (by rw [length_bytesAt]), hashToInt_takeQ hB (by rw [length_bytesAt]; exact hQD),
    ← bytesAt_take _ _ hQD]

theorem stageB_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hsi : u.gpr .esi = L.a2)
    (hdi : P.wide = true → u.gpr .edi = L.a4) :
    WP isa (.block (cfgOf P).prep) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  have hD : P.H.D = P.I.hashLen := P.len.symm
  have nB := hL.nB
  rw [Cfg.prep, WP.block_append_iff]
  cases hw : P.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
      have h₁ := (P.R.sizesA (P.curveA hw)).2.1; have h₂ := (P.R.sizesA (P.curveA hw)).2.2.1
      show _ = 8 * P.R.E.C.len; omega_arith
    have e4 : 4 * P.k = P.Q := by simp only [RfcHash.k, RfcHash.Q] at *; omega_arith
    have hwc : (cfgOf P).wide = false := hw
    simp only [hwc, Bool.false_eq_true, ite_false]
    obtain ⟨hb₁, hb₂, -, -⟩ := hb_facts hw hk.e_eq
    have := L.he
    refine WP.mono (reduce_ok (P := P) hw hk.e_eq hL hc hsi (by rw [e4, ← hD]; exact hQD)) fun u₁ ⟨hc₁, _, hh₁⟩ => ?_
    rw [e4] at hh₁
    refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
      ⟨hc₂, ?_, hk₂ _ (by nums), hv₂ _ (by nums), dgOk_narrow hL hk hw hc₂⟩
    simp only [hOf, hPart]
    rw [bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)]
    rw [hSpec, bits2octets_eqQ hB (by rw [hBOf, length_bytesAt]; exact hQD), hBOf, ← bytesAt_take m₀ L.dg hQD,
      ← hh₁]
    have e := toBytes_ofBytes (Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 P.hB) P.Q)
    rw [length_bytesAt] at e
    exact e.symm
  · have hl := P.R.nBits_len
    have hz := P.sizes
    have hQD : P.H.D < P.Q := by simpa [RfcHash.wide] using hw
    have hN : 8 * P.H.D < Spec.Ecdsa.nBits P.R.E.C := by
      have : P.H.D < P.R.E.C.len := hQD
      omega_arith
    have hwc : (cfgOf P).wide = true := hw
    have hLw : L.wide = true := hk.2.2.1.trans hw
    have he : L.e = 68 := e68 hk.e_eq hw
    have hb : P.hB = 272 := by simp only [RfcHash.hB, hw, Bool.true_or, ite_true]
    simp only [hwc, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (hPrep_ok hL hk.e_eq hw (by rw [← hD]) hc hsi) fun u₁ ⟨hc₁, hg₁, hf₁, hh₁⟩ => ?_
    have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = Spec.Sha256.bytesAt m₀ L.dg P.H.D :=
      hc₁.dgBytes hL (by rw [← hD])
    rw [hc.dgBytes hL (by rw [← hD])] at hh₁
    -- `h`, kept by what follows it: `K`, `V` and the digest for `core`.
    have hdis : ∀ {ws : List Region} {m m' : Mem}, Frame ws m m' →
        (∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 272, P.Q⟩ r) →
        Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 272) P.Q = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 272) P.Q :=
      fun hf hd => bytesAt_frame hf hd (by nums)
    -- `h` is `bits2octets` of the digest, and `core`'s digest has the digest's number.
    have hS : hSpec P L m₀ = List.replicate (P.Q - P.H.D) 0 ++ Spec.Sha256.bytesAt m₀ L.dg P.H.D := by
      rw [hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_arith)
        (by show 8 * P.R.E.C.len < _; omega_arith) (by rw [hBOf, length_bytesAt]; exact hN) P.R.n_ne,
        hBOf, length_bytesAt]
    have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) :=
      (hashToInt_short (h := Spec.Sha256.bytesAt m₀ L.dg P.H.D) (by rw [length_bytesAt]; exact hN) P.R.n_ne).1
    have hKV : ∀ r ∈ [(⟨L.B + BitVec.ofNat 64 76, 128⟩ : Region)],
        Region.Disjoint ⟨L.B + BitVec.ofNat 64 272, P.Q⟩ r := by
      simp only [List.mem_singleton]; rintro r rfl; exact Offset.disjoint _ (by omega) (by nums) (by nums)
    by_cases hsh : P.R.sh = 0
    · have e : (cfgOf P).xPrep = [] := by simp only [Cfg.xPrep, show (cfgOf P).sh = 0 from hsh, ite_true]
      rw [e]
      refine WP.block_nil (WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
        ⟨hc₂, ?_, hk₂ _ (by nums), hv₂ _ (by nums), ?_⟩)
      · simp only [hOf, hPart, hb]
        rw [hdis hf₂ hKV, hh₁, hS]
      · unfold DgOk
        simp only [dgAddr, hLw, hsh, ite_true]
        have hB8 : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
          have := hl.2.2
          show _ = 8 * P.R.E.C.len
          omega_arith
        rw [hdis hf₂ hKV, hh₁, hashToInt_takeQ hB8 (by simp [length_bytesAt]; omega_arith),
          List.take_of_length_le (by simp [length_bytesAt]; omega_arith), ofBytes_zeros, e₂]
    · refine WP.mono (xPrep_ok hL hk.e_eq hw (by rw [← hD]) hsh hc₁ ((hg₁ _ (by decide)).trans hsi)
        ((hg₁ _ (by decide)).trans (hdi hw))) fun u₂ ⟨hc₂, _, hf₂, hx₂⟩ => ?_
      rw [hdg₁] at hx₂
      refine WP.mono (initKV_ok hL hc₂) fun u₃ ⟨hc₃, hf₃, hv₃, hk₃⟩ =>
        ⟨hc₃, ?_, hk₃ _ (by nums), hv₃ _ (by nums), ?_⟩
      · simp only [hOf, hPart, hb]
        rw [hdis hf₃ hKV, hdis hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_scr (by rw [he]; nums) (by decide)
          · exact Offset.disjoint _ (by nums) (by nums) (by nums)), hh₁, hS]
      · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
        have hX : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 344) P.Q = Spec.Weierstrass.toBytes P.Q
            (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ P.R.sh) := by
          rw [bytesAt_frame hf₃ (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact Offset.disjoint _ (by omega_arith) (by nums) (by nums)) (by nums), hx₂]
        have hlt : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ P.R.sh < 2 ^ (8 * P.Q) := by
          have := ofBytes_lt (Spec.Sha256.bytesAt m₀ L.dg P.H.D)
          rw [length_bytesAt] at this
          calc _ < 2 ^ (8 * P.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
            _ ≤ 2 ^ (8 * P.Q) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega_arith) (by omega_arith)
        have hl₁ : (Spec.Weierstrass.toBytes P.Q
            (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ P.R.sh)).length = P.Q := by
          simp [Spec.Weierstrass.toBytes]
        have e₁ : Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 344) P.Q) =
            Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) := by
          rw [hX, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_arith) (by rw [hl₁]),
            List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
            show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
            Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
        unfold DgOk
        simp only [dgAddr, hLw, hsh, ite_true, ite_false]
        rw [e₁, e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_kvw (hL : L.Ok) (hk : CoreOk P L) {m m' : Mem} (hf : Frame (KVW L) m m') :
    hOf P L m' = hOf P L m := by
  have hs := P.sizes
  have nB := hL.nB
  simp only [hOf, hPart]
  cases hw : P.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    obtain ⟨hb₁, hb₂, -, -⟩ := hb_facts hw hk.e_eq
    refine bytesAt_frame hf (fun r hr => ?_) (by omega_arith)
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_SCR (by omega_arith)
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · have he : L.e = 68 := e68 hk.e_eq hw
    have hb : P.hB = 272 := by simp only [RfcHash.hB, hw, Bool.true_or, ite_true]
    rw [hb]
    refine bytesAt_frame hf (fun r hr => ?_) (by nums)
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_SCR (by rw [he]; nums)
    · exact Offset.disjoint_base _ (by omega) (by nums)

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc 0 fun h => absurd rfl h) fun u' ⟨hc', hf', hk', hv', hS'⟩ =>
    ⟨(hOf_kvw hL hk hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hk hf' kvw_apart, hS'⟩ |>
    fun h => ⟨hc', h⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc 1 fun _ => hq.saved) fun u' ⟨hc', hf', hk', hv', hS'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hk hf' kvw_apart, hS'⟩

theorem stageE_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ =>
    have hk' : kOf P L u'.mem = kOf P L u.mem := bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums)) (by nums)
    ⟨hc', P.tries_pos, hk'.trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _), hq.dg.frameOf hL hk hf' (by simp [DgApart]),
    by
      rw [hk']
      exact hq.saved.frame hf' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_scr (by nums) (by nums)).symm⟩

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block (cfgOf P).wipe) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' ∧
      ∀ p ∈ saved, u'.gpr p.1 = g p.1 :=
  WP.mono (wipe_ok hL hk.tabL.cw hk.tabL.ch hc) fun _ ⟨hc₇, ha₇, hf₇, hs₇⟩ => ⟨hc₇, ⟨hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      have := L.he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by nums))⟩, hs₇⟩

/-- `digest` in `esi`, and, if `wide`, `scratch` in `edi`. -/
theorem digestPtr_ok (hL : L.Ok) {c : Cfg} (hw : c.wide = L.wide) (hh : c.hHigh = L.hHigh) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (.block c.digestPtr) t fun u => Ctx L g m₀ u ∧ u.gpr .esi = L.a2 ∧
      (L.wide = true → u.gpr .edi = L.a4) := by
  rw [Cfg.digestPtr, WP.block_append_iff]
  refine WP.mono (argC_ok hL hw hh hc (d := .esi) (by decide) (i := 2) (by omega_arith)) fun u₁ h₁ => ?_
  rw [hw]
  by_cases hw' : L.wide = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hw')]
    exact WP.mono (argC_ok hL hw hh h₁.ctx (d := .edi) (by decide) (i := 4) (by omega_arith)) fun u₂ h₂ =>
      ⟨h₂.ctx, by rw [h₂.keep _ (by decide), h₁.val]; rfl, fun _ => h₂.val⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hw')]
    exact WP.block_nil ⟨h₁.ctx, h₁.val, fun h => absurd h hw'⟩

/-- The body, after our caller's registers are saved. -/
theorem rest_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).digestPtr) t fun u =>
      WP isa (.seq (.block (cfgOf P).prep)
        (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
        (.seq (.loop (cfgOf P).tryOne .ne) (.block (cfgOf P).wipe)))))) u
      fun t' => Ctx L g m₀ t' ∧ (∃ i, Exit P L m₀ i t') ∧ ∀ p ∈ saved, t'.gpr p.1 = g p.1 :=
  WP.mono (digestPtr_ok hL hk.tabL.cw hk.tabL.ch hc) fun _ ⟨h₀, hsi, hdi⟩ =>
    WP.seq (WP.mono (stageB_ok hL hk h₀ hsi fun hw => hdi (hk.2.2.1.trans hw)) fun _ ⟨h₁, q₁⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
          WP.seq (WP.mono (stageE_ok hL hk h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
            WP.seq (WP.mono (loop_ok hL hk h₄ q₄) fun _ ⟨h₅, i, q₅⟩ =>
              WP.mono (stageG_ok hL hk h₅ q₅) fun _ ⟨h₆, q₆, s₆⟩ => ⟨h₆, ⟨i, q₆⟩, s₆⟩)))))

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
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs, show P.I.tries - 1 - i = 0 by omega_arith]
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
        exact ite_le_of_not (by omega_arith) (by omega_arith)
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega_arith

/-! ## The whole function -/

section NoSp

open VG.Proof.RsaPkcs1Sig.X86 (noSp_seq noSp_loop noSp_call noSp_frame)
open VG.Proof.RsaPss.X86 (noSp_ite)
open VG.Proof.RsaOaep.X86 (icalls_noSp)

variable (P : RfcHash)

/-- The code's blocks, for `P`'s sizes, as the curve's file checks them. -/
theorem rfcT_of : RfcT (cfgOf P) :=
  have h := P.R.blkT P.H.D P.H.B P.hDB
  { msgF := h.msgF,
    msgF₁ := h.msgF₁,
    msgN := h.msgN,
    prepW := h.prepW,
    coreArgs := h.coreArgs,
    keepV := h.keepV,
    candTop := h.candTop,
    wipe := h.wipe,
    digestPtr := h.digestPtr,
    padI := h.padI,
    padO := h.padO,
    hfinCopyK := h.hfinCopyK,
    hfinCopyV := h.hfinCopyV,
    iMsgF₀ := h.iMsgF₀,
    iMsgF₁ := h.iMsgF₁,
    iMsgN := h.iMsgN,
    iPrep := h.iPrep,
    iCoreArgs := h.iCoreArgs,
    iKeepV := h.iKeepV,
    iCandTop := h.iCandTop,
    iWipe := h.iWipe,
    iDigestPtr := h.iDigestPtr,
    iPadI := h.iPadI,
    iPadO := h.iPadO,
    iCopyK := h.iCopyK,
    iCopyV := h.iCopyV,
    m8 := h.m8,
    mD := h.mD }

variable {c : Cfg}

/-- What the code needs of the functions it may call through the table:
none writes `esp` but through its frames. -/
abbrev FnsNs (f : Impl.RsaOaep.X86.Fns) : Prop :=
  (∀ q ∈ f.init, NoSp q.2) ∧ (∀ q ∈ f.upd, NoSp q.2) ∧ (∀ q ∈ f.fin, NoSp q.2)

theorem okB_noSp {is : List Instr} (h : OkB is) : NoSp (.block is : Prog isa) := NoSp.of_all h

theorem tcall_ns {j : Nat} {ts : List (String × Prog isa)} {rs : List Reg} (h : ∀ q ∈ ts, NoSp q.2) :
    NoSp (c.tcall j ts rs) :=
  noSp_seq (NoSp.of_all rfl) (noSp_seq (NoSp.of_all rfl) (noSp_frame rfl rfl (icalls_noSp rfl h)))

theorem initCall_ns (hf : FnsNs c.f) (o : Nat) : NoSp (c.initCall o) := noSp_seq (NoSp.of_all rfl) (tcall_ns hf.1)

theorem updCall_ns (hf : FnsNs c.f) (o cnt : Nat) {dataA : List Instr}
    (hd : (∃ a, dataA = c.scr .edx a) ∨ (∃ a, dataA = Cfg.fr .edx a)) (len : Nat) :
    NoSp (c.updCall o cnt dataA len) := by
  refine noSp_seq (NoSp.of_all ?_) (tcall_ns hf.2.1)
  rcases hd with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rfl

theorem finCall_ns (hf : FnsNs c.f) (o cnt : Nat) : NoSp (c.finCall o cnt) :=
  noSp_seq (NoSp.of_all rfl) (tcall_ns hf.2.2)

theorem hinit_ns (hT : RfcT c) (hf : FnsNs c.f) : NoSp c.hinit :=
  noSp_seq (initCall_ns hf _) (noSp_seq (initCall_ns hf _) (noSp_seq (okB_noSp hT.iPadI) (noSp_seq
    (updCall_ns hf _ _ (.inl ⟨_, rfl⟩) _) (noSp_seq (okB_noSp hT.iPadO) (updCall_ns hf _ _ (.inl ⟨_, rfl⟩) _)))))

theorem hfin_ns (hT : RfcT c) (hf : FnsNs c.f) (len : Nat) {dst : Nat} (hd : dst = fK ∨ dst = fV) :
    NoSp (c.hfin len dst) :=
  noSp_seq (finCall_ns hf _ _) (noSp_seq (updCall_ns hf _ _ (.inl ⟨_, rfl⟩) _)
    (noSp_seq (finCall_ns hf _ _) (hd.elim (fun h => by subst h; exact okB_noSp hT.iCopyK)
      (fun h => by subst h; exact okB_noSp hT.iCopyV))))

theorem blkApp_ns {a b : List Instr} (ha : NoSp (.block a : Prog isa)) (hb : NoSp (.block b : Prog isa)) :
    NoSp (.block (a ++ b) : Prog isa) := fun i hi => by
  simp only [instrs, List.mem_append] at hi
  rcases hi with hi | hi
  exacts [ha i hi, hb i hi]

theorem copyN_ns (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) :
    NoSp (.block (Cfg.copyN k src so dst d) : Prog isa) := fun i hi => by
  simp only [instrs, Cfg.copyN, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨j, -, rfl | rfl⟩ := hi <;> rfl

theorem copyStates_ns (c : Cfg) (b : Bool) : NoSp (.block (c.scrPtr ++ Cfg.copyStates b) : Prog isa) :=
  blkApp_ns (NoSp.of_all rfl) (by cases b <;> exact copyN_ns _ _ _ _ _)

section Mac

variable (hT : RfcT c) (hf : FnsNs c.f) {dataA : List Instr}
  (hd : (∃ a, dataA = c.scr .edx a) ∨ (∃ a, dataA = Cfg.fr .edx a)) (len : Nat) {dst : Nat}
  (hdst : dst = fK ∨ dst = fV)
include hT hf hd hdst

theorem hmac_ns : NoSp (c.hmac dataA len dst) :=
  noSp_seq (hinit_ns hT hf) (noSp_seq (updCall_ns hf _ _ hd _) (hfin_ns hT hf _ hdst))

theorem hmacS_ns : NoSp (c.hmacS dataA len dst) :=
  noSp_seq (hinit_ns hT hf) (noSp_seq (copyStates_ns c _) (noSp_seq (updCall_ns hf _ _ hd _) (hfin_ns hT hf _ hdst)))

theorem hmacR_ns : NoSp (c.hmacR dataA len dst) :=
  noSp_seq (copyStates_ns c _) (noSp_seq (updCall_ns hf _ _ hd _) (hfin_ns hT hf _ hdst))

end Mac

section Body

variable (hT : RfcT c) (hf : FnsNs c.f)
include hT hf

theorem hmacVS_ns : NoSp c.hmacVS := hmacS_ns hT hf (.inr ⟨_, rfl⟩) _ (.inr rfl)

theorem hmacVR_ns : NoSp c.hmacVR := hmacR_ns hT hf (.inr ⟨_, rfl⟩) _ (.inr rfl)

theorem rekeyFull_ns (b : Nat) (hb : b < 2) : NoSp (c.rekeyFull b) := by
  unfold Cfg.rekeyFull
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · exact noSp_seq (NoSp.of_all rfl) (noSp_seq (okB_noSp hT.iMsgF₀)
      (noSp_seq (hmac_ns hT hf (.inl ⟨_, rfl⟩) _ (.inl rfl)) (hmacVS_ns hT hf)))
  · exact noSp_seq (NoSp.of_all rfl) (noSp_seq (okB_noSp hT.iMsgF₁)
      (noSp_seq (hmacR_ns hT hf (.inl ⟨_, rfl⟩) _ (.inl rfl)) (hmacVS_ns hT hf)))

theorem rekey_ns : NoSp c.rekey :=
  noSp_seq (NoSp.of_all rfl) (noSp_seq (okB_noSp hT.iMsgN)
    (noSp_seq (hmac_ns hT hf (.inl ⟨_, rfl⟩) _ (.inl rfl)) (hmacVS_ns hT hf)))

theorem candW_ns : ∀ k, k ≤ 8 → NoSp (c.candW k)
  | 0, _ => NoSp.of_all rfl
  | k + 1, hk => noSp_seq (candW_ns k (by omega)) (noSp_seq (hmacVR_ns hT hf)
      (okB_noSp (hT.iKeepV k (by omega))))

theorem cand_ns : NoSp c.cand := by
  unfold Cfg.cand
  split
  · exact noSp_seq (candW_ns hT hf _ hT.m8) (okB_noSp hT.iCandTop)
  · exact hmacVR_ns hT hf

theorem tryOne_ns (hcore : NoSp c.coreC) : NoSp c.tryOne :=
  noSp_seq (cand_ns hT hf) (noSp_seq (okB_noSp hT.iCoreArgs) (noSp_seq
    (noSp_frame rfl rfl (noSp_call hcore)) (noSp_seq (NoSp.of_all rfl)
    (noSp_ite (noSp_seq (rekey_ns hT hf) (NoSp.of_all rfl)) (NoSp.of_all rfl)))))

/-- No instruction of the body writes `esp`: not those of the functions it
calls, which `hf` and `hcore` say, nor its own, which each curve's file
checks for each size of hash function (`RfcT`). -/
theorem body_noSp' (hcore : NoSp c.coreC) : NoSp c.body :=
  noSp_seq (okB_noSp hT.iDigestPtr) (noSp_seq (okB_noSp hT.iPrep)
    (noSp_seq (rekeyFull_ns hT hf 0 (by decide)) (noSp_seq (rekeyFull_ns hT hf 1 (by decide))
    (noSp_seq (NoSp.of_all rfl) (noSp_seq (noSp_loop (tryOne_ns hT hf hcore)) (okB_noSp hT.iWipe))))))

end Body

/-- No instruction of the body for `P` writes `esp`. -/
theorem body_nosp : NoSp (cfgOf P).body := body_noSp' (rfcT_of P) ⟨P.fInit, P.fUpd, P.fFin⟩ P.R.coreNs

end NoSp

theorem released_gpr {e : Nat} {s₂ : State} {r : Reg} (hr : r ≠ .esp) : (released e s₂).gpr r = s₂.gpr r :=
  (Wp.Upd.setReg s₂ .esp _).other r hr

theorem released_esp (e : Nat) (s₂ : State) :
    (released e s₂).gpr .esp = s₂.gpr .esp + BitVec.ofNat 32 (196 + 4 * e) :=
  (Wp.Upd.setReg s₂ .esp _).gpr

/-- The contract the code for `P`'s hash function is proven against, with
`P`'s table and the functions `ns`' addresses public. -/
abbrev rfcP (P : RfcHash) (ns : List String) : Contract isa :=
  rfcX86 P.I (272 + 4 * P.e) P.R.E.combConsts (tabFacts P.H P.f) ns

/-- The layout of a call from `s`. -/
abbrev layP (P : RfcHash) (s : State) : Lay P.I.hashLen :=
  lay P.I.hashLen P.I.ecdsa.curve.len P.wide P.R.hHigh s P.R.E.combConsts P.H P.f

theorem coreOk_lay (P : RfcHash) (s : State) : CoreOk P (layP P s) :=
  ⟨P.curveLen, ⟨fun hw => by show P.Q ≤ P.I.hashLen; rw [P.len]; exact (P.sizesA hw).2.2, rfl⟩, rfl, rfl, rfl, rfl⟩

/-- `sign` for `P`'s hash function meets `rfcP P` and keeps the callee-saved
registers and its return address. -/
theorem sign_ok {ns : List String} {s : State} (h : (rfcP P ns).pre s) :
    WP isa (cfgOf P).sign s fun s' => abiPreserved s s' ∧ (rfcP P ns).post s s' := by
  have hL : (layP P s).Ok := lay_ok h
  have nB := hL.nB
  have he : P.e ≤ 68 := by nums
  have le : (layP P s).e = P.e := rfl
  refine WP.alloc (e := P.e) he (by have := h.1; omega_arith) (body_nosp P) (WP.seq ?_)
  refine save_ok h fun t hc _ => WP.mono (rest_ok hL (coreOk_lay P s) hc) fun u hu => hu.mono ?_
  intro u' ⟨hc', ⟨i, hx⟩, hs'⟩
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [released_gpr (by decide)]; exact hs' (.ebx, 180) (by decide)
    · rw [released_gpr (by decide)]; exact hs' (.esi, 184) (by decide)
    · rw [released_gpr (by decide)]; exact hs' (.edi, 188) (by decide)
    · rw [released_gpr (by decide)]; exact hs' (.ebp, 192) (by decide)
    · rw [released_esp, hc'.esp]; exact BitVec.sub_add_cancel _ _
  · have hret : (s.gpr .esp).setWidth 64 = (layP P s).B + BitVec.ofNat 64 (272 + 4 * P.e) := by
      have le : (layP P s).e = P.e := rfl
      rw [hL.B_eq, le, BitVec.sub_add_cancel]; rfl
    show u'.mem.readW _ 32 = _
    rw [hret]
    refine hc'.frame.readW (r := (layP P s).RET) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.ro
    · exact hL.rc
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · show match (result P.I s.mem (layP P s).d (layP P s).dg).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    have e₂ : P.I.ecdsa.curve = P.R.E.C := by rw [P.ecdsa, P.R.curve]
    rw [e₁]
    have hr := hx.res
    have ha : (released P.e u').gpr .eax = u'.gpr .eax := released_gpr (by decide)
    revert hr
    cases sigI P (layP P s) s.mem i with
    | some rs => exact fun ⟨h₁, h₂⟩ => ⟨by rw [BitVec.setWidth_append_eq_right, ha]; exact h₁, by rw [e₂]; exact h₂⟩
    | none => exact fun ⟨h₁, h₂⟩ => ⟨by rw [BitVec.setWidth_append_eq_right, ha]; exact h₁, h₂⟩

end VG.Proof.Ecdsa.Rfc6979.X86
