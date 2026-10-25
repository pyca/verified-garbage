module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Loop
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Framework.Offset

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
abbrev dB (P : RfcHash) {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.F.H.D 1)

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

/-- `core`'s digest, unless two `V`s make a candidate: the digest, whose
leftmost `Q` bytes it reads. -/
theorem dgOk_narrow (hL : L.Ok) (hk : CoreOk P L) (hw : P.R.wide = false) {u : State} (hc : Ctx L g m₀ u) :
    DgOk P L m₀ u.mem := by
  obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
  have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
    have h₁ := (P.R.sizesA hw).2.1; have h₂ := (P.R.sizesA hw).2.2.1; show _ = 8 * P.R.E.C.len; omega_arith
  have hD : P.Q ≤ P.I.hashLen := by rw [P.len]; exact hQD
  have hLw : L.wide = false := hk.2.2.1.trans hw
  unfold DgOk
  simp only [dgAddr, hLw, Bool.false_eq_true, ite_false, eOf, hBOf]
  rw [hc.dgBytes hL hD, hashToInt_takeQ hB (by rw [length_bytesAt]),
    List.take_of_length_le (by rw [length_bytesAt]), hashToInt_takeQ hB (by rw [length_bytesAt]; exact hQD),
    ← bytesAt_take _ _ hQD]

theorem stageB_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hsi : u.gpr .esi = L.a2)
    (hdi : P.R.wide = true → u.gpr .edi = L.a3) :
    WP isa (.block ((if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++ Cfg.initKV)) u
      fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  have hD : P.F.H.D = P.I.hashLen := P.len.symm
  have nB := hL.nB
  rw [WP.block_append_iff]
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
      have h₁ := (P.R.sizesA hw).2.1; have h₂ := (P.R.sizesA hw).2.2.1; show _ = 8 * P.R.E.C.len; omega_arith
    have e4 : 4 * P.k = P.Q := by simp only [RfcHash.k, RfcHash.Q] at *; omega_arith
    have hwc : (cfgOf P).wide = false := hw
    simp only [hwc, Bool.false_eq_true, ite_false]
    obtain ⟨hb₁, hb₂, -, -⟩ := hb_facts hw hk.e_eq
    have := L.he
    refine WP.mono (reduce_ok (P := P) hw hk.e_eq hL hc hsi (by rw [e4, ← hD]; exact hQD)) fun u₁ ⟨hc₁, _, hh₁⟩ => ?_
    rw [e4] at hh₁
    refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
      ⟨hc₂, ?_, hk₂ _ (by nums), hv₂ _ (by nums), dgOk_narrow hL hk hw hc₂⟩
    simp only [hOf, hPart, hw, Bool.false_eq_true, ite_false]
    rw [bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)]
    rw [hSpec, bits2octets_eqQ hB (by rw [hBOf, length_bytesAt]; exact hQD), hBOf, ← bytesAt_take m₀ L.dg hQD,
      ← hh₁]
    have e := toBytes_ofBytes (Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 P.hB) P.Q)
    rw [length_bytesAt] at e
    exact e.symm
  · obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hw
    have hl := P.R.nBits_len
    have hN := (P.R.sizesW hw).2.2
    have hsh := sh7 hw
    have hwc : (cfgOf P).wide = true := hw
    have hLw : L.wide = true := hk.2.2.1.trans hw
    have he : L.e = 36 := e36 hk.2.2.1 hw
    simp only [hwc, ite_true]
    refine WP.mono (coreDigest_ok hL hk.2.2.1 hw (by rw [← hD]) hc hsi (hdi hw)) fun u₁ ⟨hc₁, hf₁, hx₁⟩ => ?_
    refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
      ⟨hc₂, ?_, hk₂ _ (by nums), hv₂ _ (by nums), ?_⟩
    · simp only [hOf, hPart, hw, ite_true]
      rw [hc₂.dgBytes hL (by rw [← hD]), hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_arith)
        (by show 8 * P.R.E.C.len < _; omega_arith) (by rw [hBOf, length_bytesAt]; omega_arith) P.R.n_ne,
        hBOf, length_bytesAt]
    · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
      have hX : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 272) P.Q = Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D) * 2 ^ P.R.sh) := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
            (by omega_arith), hx₁, hc.dgBytes hL (by rw [← hD])]
      have hlt : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D) * 2 ^ P.R.sh < 2 ^ (8 * P.Q) := by
        have := ofBytes_lt (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D)
        rw [length_bytesAt] at this
        calc _ < 2 ^ (8 * P.F.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega_arith) (by omega_arith)
      have hl₁ : (Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D) * 2 ^ P.R.sh)).length = P.Q := by
        simp [Spec.Weierstrass.toBytes]
      have e₁ : Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 272) P.Q) =
          Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D) := by
        rw [hX, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_arith) (by rw [hl₁]),
          List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
          show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
          Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.F.H.D) :=
        (hashToInt_short (h := Spec.Sha256.bytesAt m₀ L.dg P.F.H.D) (by rw [length_bytesAt]; omega_arith) P.R.n_ne).1
      unfold DgOk
      simp only [dgAddr, hLw, ite_true]
      rw [e₁, e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_kvw (hL : L.Ok) (hk : CoreOk P L) {m m' : Mem} (hf : Frame (KVW L) m m') :
    hOf P L m' = hOf P L m := by
  have hs := P.sizes
  have nB := hL.nB
  simp only [hOf, hPart]
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    obtain ⟨hb₁, hb₂, -, -⟩ := hb_facts hw hk.e_eq
    simp only [Bool.false_eq_true, ite_false]
    refine bytesAt_frame hf (fun r hr => ?_) (by omega_arith)
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_SCR (by omega_arith)
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · simp only [ite_true]
    refine congrArg (_ ++ ·) (bytesAt_frame hf (fun r hr => ?_) (by nums))
    have hD : Region.Sub ⟨L.dg, P.F.H.D⟩ L.DG := Region.sub_prefix (by rw [P.len])
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.gc.sub_left hD
    · exact (hL.kg.symm.sub_left hD).sub_right (Region.sub_prefix (by omega_arith))

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc 0) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨(hOf_kvw hL hk hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hk hf' kvw_apart⟩ |>
    fun h => ⟨hc', h⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc 1) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hk hf' kvw_apart⟩

theorem stageE_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', P.tries_pos,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _), hq.dg.frameOf hL hk hf' (by simp [DgApart])⟩

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block (Cfg.wipe L.wide L.hHigh)) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' ∧
      ∀ p ∈ saved, u'.gpr p.1 = g p.1 :=
  WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, ha₇, hf₇, hs₇⟩ => ⟨hc₇, ⟨hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      have := L.he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by nums))⟩, hs₇⟩

/-- `digest` in `esi`, and, if `wide`, `scratch` in `edi`. -/
theorem digestPtr_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (Cfg.digestPtr L.wide L.hHigh)) t fun u => Ctx L g m₀ u ∧ u.gpr .esi = L.a2 ∧
      (L.wide = true → u.gpr .edi = L.a3) := by
  rw [Cfg.digestPtr, WP.block_append_iff]
  refine WP.mono (arg_ok hL hc (d := .esi) (by decide) (i := 2) (by omega_arith)) fun u₁ h₁ => ?_
  by_cases hw : L.wide = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hw)]
    exact WP.mono (arg_ok hL h₁.ctx (d := .edi) (by decide) (i := 3) (by omega_arith)) fun u₂ h₂ =>
      ⟨h₂.ctx, by rw [h₂.keep _ (by decide), h₁.val]; rfl, fun _ => h₂.val⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hw)]
    exact WP.block_nil ⟨h₁.ctx, h₁.val, fun h => absurd h hw⟩

/-- The body, after our caller's registers are saved. -/
theorem rest_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (Cfg.digestPtr P.R.wide P.R.hHigh)) t fun u =>
      WP isa (.seq (.block ((if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++ Cfg.initKV))
        (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
        (.seq (.loop (cfgOf P).tryOne .ne) (.block (Cfg.wipe P.R.wide P.R.hHigh))))))) u
      fun t' => Ctx L g m₀ t' ∧ (∃ i, Exit P L m₀ i t') ∧ ∀ p ∈ saved, t'.gpr p.1 = g p.1 := by
  rw [← hk.2.2.1, ← hk.2.1.2]
  exact WP.mono (digestPtr_ok hL hc) fun _ ⟨h₀, hsi, hdi⟩ =>
    WP.seq (WP.mono (stageB_ok hL hk h₀ hsi fun hw => hdi (hk.2.2.1.trans hw)) fun _ ⟨h₁, q₁⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
          WP.seq (WP.mono (stageE_ok hL hk h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
            WP.seq (WP.mono (loop_ok hL hk h₄ q₄) fun _ ⟨h₅, i, q₅⟩ =>
              WP.mono (stageG_ok hL hk h₅ q₅) fun _ ⟨h₆, q₆, s₆⟩ => ⟨h₆, ⟨i, q₆⟩, s₆⟩)))))



/-! ## RFC 6979's result -/

/-- One `V` makes a candidate, or two if `wide`. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.F.H.D = P.nb := by
  have hs := P.sizes
  rw [Spec.Ecdsa.Rfc6979.blocks]
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have h₁ := (P.R.sizesA hw).2.1; have h₂ := (P.R.sizesA hw).2.2.1
    simp only [RfcHash.nb, hw, Bool.false_eq_true, ite_false]
    exact Nat.div_eq_of_lt_le (by simp only [RfcHash.Q, RfcHash.w] at *; omega_arith)
      (by simp only [RfcHash.Q, RfcHash.w] at *; omega_arith)
  · obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hw
    have h₂ := (P.R.sizesW hw).2.2
    simp only [RfcHash.nb, hw, ite_true, h₂, hD64]

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.hH.SH.H P.F.H.D (xOf P L m₀) (eOf P L m₀) K V P.I.tries
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
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.hH.SH.H) (hlen := P.F.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.I.tries - 2 - i)
          (K := (stepB P.ok.hH.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.hH.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
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

theorem cfgOf_F : (cfgOf P).F = P.F := rfl
theorem coreC_eq : (cfgOf P).coreC = P.R.coreC := rfl

theorem allInstrs_of_noSp {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi; simp [h i hi]

theorem subWord_nosp (c : Cfg) (j : Nat) : (c.subWord j).all (fun i => !Taint.clobbers i .esp) = true := by
  cases j <;> rfl

theorem selWord_nosp (c : Cfg) (j : Nat) : (c.selWord j).all (fun i => !Taint.clobbers i .esp) = true := rfl

/-- `h = bits2octets(digest)`, `K` and `V`: no instruction writes `esp`,
whatever the code's `n`. -/
theorem reduceKV_nosp (c : Cfg) :
    (Code.block (c.reduce ++ Cfg.initKV) : Prog isa).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  simp only [instrs, Cfg.reduce, List.all_append, List.all_flatMap, subWord_nosp, selWord_nosp]
  rw [show ∀ l : List Nat, (l.all fun _ => true) = true from fun l => List.all_eq_true.mpr fun _ _ => rfl]
  decide


/-- No instruction of the body writes `esp`: not those of the functions it
calls, by what `P` and the proofs of HMAC's functions know of them, nor its
own, which the kernel evaluates for each size of curve and hash function. -/
theorem body_nosp (P : RfcHash) : NoSp (cfgOf P).body := by
  have hI := allInstrs_of_noSp P.ok.hiSp
  have hU := allInstrs_of_noSp P.ok.hH.updSp
  have hF := allInstrs_of_noSp P.ok.hfSp
  have hK := allInstrs_of_noSp P.R.coreNs
  have hw : (cfgOf P).w = 2 * P.R.E.n - (if P.R.E.C.len = 28 then 1 else 0) := rfl
  have hl : (cfgOf P).len = P.R.E.C.len := rfl
  have hwd : (cfgOf P).wide = P.R.wide := rfl
  have hsh : (cfgOf P).sh = P.R.sh := rfl
  refine NoSp.of_all ?_
  -- The count's initial store writes no `esp`, whatever the count.
  have initCnt_nosp : (Code.block (cfgOf P).initCnt : Prog isa).allInstrs (fun i => !Taint.clobbers i .esp) = true :=
    rfl
  cases hW : P.R.wide
  · have hR := reduceKV_nosp (cfgOf P)
    have hlen := P.lengthsA hW
    have hhq : (cfgOf P).hHigh = decide (P.Q = 64) := hHigh_q P hW
    simp only [Cfg.body, Cfg.tryOne, Cfg.cand, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac, Code.allInstrs.eq_2,
      Code.allInstrs.eq_3, Code.allInstrs.eq_4, Code.allInstrs.eq_5, Code.allInstrs.eq_6, hwd, hW,
      Bool.false_eq_true, ite_false, cfgOf_F, coreC_eq, hI, hU, hF, hK, hR, initCnt_nosp, Bool.and_true,
      Bool.true_and, hhq, fHo_q P hW]
    simp only [hl]
    rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rcases hlen with h'' | h'' | h'' | h'' | h'' <;>
      simp only [show P.R.E.C.len = P.Q from rfl, h, h', h'', Nat.reduceEqDiff, decide_true, decide_false,
        ite_true, ite_false] <;> decide +kernel
  · obtain ⟨hn, hlen, -⟩ := P.R.sizesW hW
    obtain ⟨-, -, hD, hB⟩ := P.sizesW hW
    have h7 := sh7 hW
    simp only [Cfg.body, Cfg.tryOne, Cfg.cand, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac, Code.allInstrs.eq_2,
      Code.allInstrs.eq_3, Code.allInstrs.eq_4, Code.allInstrs.eq_5, Code.allInstrs.eq_6, hwd, hW, ite_true,
      cfgOf_F, coreC_eq, hI, hU, hF, hK, initCnt_nosp, Bool.and_true, Cfg.coreDigest, Cfg.keepV,
      Cfg.candTop, Cfg.conv]
    simp only [hw, hl, hsh, hn, hlen, h7, hD, hB, show (cfgOf P).hHigh = false from hHigh_wide P hW,
      fHo_wide P hW]
    decide +kernel

theorem released_gpr {e : Nat} {s₂ : State} {r : Reg} (hr : r ≠ .esp) : (released e s₂).gpr r = s₂.gpr r :=
  (Wp.Upd.setReg s₂ .esp _).other r hr

theorem released_esp (e : Nat) (s₂ : State) :
    (released e s₂).gpr .esp = s₂.gpr .esp + BitVec.ofNat 32 (196 + 4 * e) :=
  (Wp.Upd.setReg s₂ .esp _).gpr

theorem coreOk_lay (P : RfcHash) (s : State) :
    CoreOk P (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide P.R.hHigh s P.R.E.combConsts) :=
  ⟨P.curveLen, ⟨fun hw => by show P.Q ≤ P.I.hashLen; rw [P.len]; exact (P.sizesA hw).2.2, rfl⟩, rfl, rfl⟩

/-- `vg_ecdsa_<curve>_<hash>_sign` meets `rfcX86 P.I` and keeps the
callee-saved registers and its return address. -/
theorem sign_ok {s : State} (h : (rfcX86 P.I (272 + 4 * P.e) P.R.E.combConsts).pre s) :
    WP isa (cfgOf P).sign s fun s' => abiPreserved s s' ∧ (rfcX86 P.I (272 + 4 * P.e) P.R.E.combConsts).post s s' := by
  have hL := lay_ok h
  have nB := hL.nB
  have he : P.e ≤ 36 := by nums
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
  · have hret : (s.gpr .esp).setWidth 64 =
        (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide P.R.hHigh s P.R.E.combConsts).B + BitVec.ofNat 64 (272 + 4 * P.e) := by
      have le : (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide P.R.hHigh s P.R.E.combConsts).e = P.e := rfl
      rw [hL.B_eq, le, BitVec.sub_add_cancel]; rfl
    show u'.mem.readW _ 32 = _
    rw [hret]
    refine hc'.frame.readW (r := (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide P.R.hHigh s P.R.E.combConsts).RET) (Region.contains_self _ _) ?_
      (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.ro
    · exact hL.rc
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · show match (result P.I s.mem (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide P.R.hHigh s P.R.E.combConsts).d
        (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide P.R.hHigh s P.R.E.combConsts).dg).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    have e₂ : P.I.ecdsa.curve = P.R.E.C := by rw [P.ecdsa, P.R.curve]
    rw [e₁]
    have hr := hx.res
    have ha : (released P.e u').gpr .eax = u'.gpr .eax := released_gpr (by decide)
    revert hr
    cases sigI P (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide P.R.hHigh s P.R.E.combConsts) s.mem i with
    | some rs => exact fun ⟨h₁, h₂⟩ => ⟨by rw [BitVec.setWidth_append_eq_right, ha]; exact h₁, by rw [e₂]; exact h₂⟩
    | none => exact fun ⟨h₁, h₂⟩ => ⟨by rw [BitVec.setWidth_append_eq_right, ha]; exact h₁, h₂⟩

end VG.Proof.Ecdsa.Rfc6979.X86
