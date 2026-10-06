import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Loop

/-!
# Deterministic ECDSA on 32-bit ARM: correctness

As on x86 (`Proof/Ecdsa/Rfc6979/X86/Correct.lean`): the loop leaves it at a
candidate that is suitable or the last (`loop_ok`); before it, `h`, `K`,
`V`, `core`'s digest and the count are as RFC 6979's steps a–g make them
(`stageB_ok` … `stageE_ok`); and the signature of that candidate is RFC
6979's (`result_eq`), for the hash function `P`'s instance of the contract. The frame's allocation, and our caller's registers
saved in it and restored, give the whole function (`sign_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)
open VG.Proof.X25519.Arm (wp_mov op2_reg)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem}

/-! ## The loop -/

theorem loop_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne .ne) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (8 - n) s ∧ n ≤ 8) ?_ 8 t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega
  refine WP.mono (tryOne_ok hL hk hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega, hc', ?_, by omega⟩
    rwa [show 8 - (n - 1) = 8 - n + 1 by omega]

/-! ## Steps a–g -/

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.E.C = P.Q := by
  have := P.R.nBits_len
  exact rlenR (by show _ ≤ 8 * P.R.E.C.len; omega) (by show 8 * P.R.E.C.len < _; omega)

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

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.F.H.D 0
  v : vOfP P L u.mem = List.replicate P.F.H.D 1
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
theorem dgOk_narrow (hL : L.Ok) (hk : CoreOk P L) (hw : P.R.wide = false) {u : State} (hc : Ctx L g m₀ u) :
    DgOk P L m₀ u.mem := by
  obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
  have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
    have h₁ := (P.R.sizesA hw).2.1; have h₂ := (P.R.sizesA hw).2.2.1; show _ = 8 * P.R.E.C.len; omega
  have hD : P.Q ≤ P.I.hashLen := by rw [P.len]; exact hQD
  have hLw : L.wide = false := hk.2.2.trans hw
  unfold DgOk
  simp only [dgAddr, hLw, Bool.false_eq_true, ite_false, eOf, hBOf]
  rw [hc.dgBytes hL hD, hashToInt_takeQ hB (by rw [length_bytesAt]),
    List.take_of_length_le (by rw [length_bytesAt]), hashToInt_takeQ hB (by rw [length_bytesAt]; exact hQD),
    ← bytesAt_take _ _ hQD]

theorem stageB_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block ((if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++ Cfg.initKV)) u
      fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  have hD : P.F.H.D = P.I.hashLen := P.len.symm
  have nB := hL.nB
  have hb := hL.B_fit
  rw [WP.block_append_iff]
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
      have h₁ := (P.R.sizesA hw).2.1; have h₂ := (P.R.sizesA hw).2.2.1; show _ = 8 * P.R.E.C.len; omega
    have e4 : 4 * P.k = P.Q := by simp only [RfcHash.k, RfcHash.Q, RfcHash.w] at *; omega
    have hwc : (cfgOf P).wide = false := hw
    simp only [hwc, Bool.false_eq_true, ite_false]
    refine WP.mono (reduce_ok (P := P) hw hL hc (by rw [e4, ← hD]; exact hQD)) fun u₁ ⟨hc₁, _, hh₁⟩ => ?_
    rw [e4] at hh₁
    refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
      ⟨hc₂, ?_, hk₂ _ (by anums), hv₂ _ (by anums), dgOk_narrow hL hk hw hc₂⟩
    simp only [hOf, hPart, hw, Bool.false_eq_true, ite_false]
    rw [bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by omega)]
    rw [hSpec, bits2octets_eqQ hB (by rw [hBOf, length_bytesAt]; exact hQD), hBOf,
      ← bytesAt_take m₀ (State.addr L.dg) hQD, ← hh₁]
    have e := toBytes_ofBytes (Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 152) P.Q)
    rw [length_bytesAt] at e
    exact e.symm
  · obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hw
    have hl := P.R.nBits_len
    have hN := (P.R.sizesW hw).2.2
    have hsh := sh7 hw
    have hwc : (cfgOf P).wide = true := hw
    have hLw : L.wide = true := hk.2.2.trans hw
    have he : L.e = 36 := e36 hk.2.2 hw
    simp only [hwc, ite_true]
    refine WP.mono (coreDigest_ok hL hk.2.2 hw (by rw [← hD]) hc) fun u₁ ⟨hc₁, hf₁, hx₁⟩ => ?_
    refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
      ⟨hc₂, ?_, hk₂ _ (by anums), hv₂ _ (by anums), ?_⟩
    · simp only [hOf, hPart, hw, ite_true]
      rw [hc₂.dgBytes hL (by rw [← hD]), hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega)
        (by show 8 * P.R.E.C.len < _; omega) (by rw [hBOf, length_bytesAt]; omega) P.R.n_ne,
        hBOf, length_bytesAt]
    · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
      have hX : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) P.Q = Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.F.H.D) * 2 ^ P.R.sh) := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
            (by omega), hx₁, hc.dgBytes hL (by rw [← hD])]
      have hlt : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.F.H.D) * 2 ^ P.R.sh <
          2 ^ (8 * P.Q) := by
        have := ofBytes_lt (Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.F.H.D)
        rw [length_bytesAt] at this
        calc _ < 2 ^ (8 * P.F.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
      have hl₁ : (Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.F.H.D) * 2 ^ P.R.sh)).length =
          P.Q := by
        simp [Spec.Weierstrass.toBytes]
      have e₁ : Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) P.Q) =
          Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.F.H.D) := by
        rw [hX, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega) (by rw [hl₁]),
          List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
          show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
          Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.F.H.D) :=
        (hashToInt_short (h := Spec.Sha256.bytesAt m₀ (State.addr L.dg) P.F.H.D) (by rw [length_bytesAt]; omega)
          P.R.n_ne).1
      unfold DgOk
      simp only [dgAddr, hLw, ite_true]
      rw [e₁, e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_kvw (hL : L.Ok) {m m' : Mem} (hf : Frame (KVW L) m m') : hOf P L m' = hOf P L m := by
  have nB := hL.nB
  have hb := hL.B_fit
  simp only [hOf, hPart]
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    simp only [Bool.false_eq_true, ite_false]
    refine bytesAt_frame hf (fun r hr => ?_) (by simp only [RfcHash.Q, RfcHash.w] at *; omega)
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_SCR (by simp only [RfcHash.Q, RfcHash.w] at *; omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)
  · simp only [ite_true]
    refine congrArg (_ ++ ·) (bytesAt_frame hf (fun r hr => ?_) (by anums))
    have hD : Region.Sub ⟨State.addr L.dg, P.F.H.D⟩ L.DG := Region.sub_prefix (by rw [P.len])
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.gc.sub_left hD
    · exact (hL.kg.symm.sub_left hD).sub_right (Region.sub_prefix (by omega))

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc (b := 0) (by decide)) fun u' ⟨hc', _, hf', hk', hv'⟩ =>
    ⟨hc', (hOf_kvw hL hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hk hf' kvw_apart⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc (b := 1) (by decide)) fun u' ⟨hc', _, hf', hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hk hf' kvw_apart⟩

theorem stageE_ok {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok (P := P) hc) fun u' ⟨hc', hm', hn'⟩ => ⟨hc', by omega, hm' ▸ hq.k, hm' ▸ hq.v,
    by rw [hn'], fun j hj => absurd hj (Nat.not_lt_zero _), hm' ▸ hq.dg⟩

/-- After the wiping: the result, and our caller's registers. -/
structure Fin (P : RfcHash) (L : Lay P.I.hashLen) (g : Reg → BitVec 32) (m₀ : Mem) (u : State) : Prop where
  wr : u.wr = [L.FR, L.OUT, L.SCR]
  sp : u.sp = L.fp
  saved : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, u.gpr p.1 = g p.1
  exit : ∃ i, Exit P L m₀ i u

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block (Cfg.wipe (cfgOf P).wide)) u (Fin P L g m₀) := by
  have hw : (cfgOf P).wide = L.wide := hk.2.2.symm
  have := L.he
  have := hL.B_fit
  rw [hw]
  exact WP.mono (wipe_ok hL hc) fun _ ⟨_, hwr, hsp, hs, ha, hf⟩ => ⟨hwr.trans hc.wr, hsp.trans hc.sp, hs, i,
    hx.lt, hx.fails, hx.last, hx.res.keep ha (bytesAt_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (by omega)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by anums))⟩

/-- The body, after `h`, `V` and `K`. -/
theorem rest_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hq : QB P L m₀ t) :
    WP isa (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne .ne) (.block (Cfg.wipe (cfgOf P).wide)))))) t (Fin P L g m₀) :=
  WP.seq (WP.mono (stageC_ok hL hk hc hq) fun _ ⟨h₂, q₂⟩ =>
    WP.seq (WP.mono (stageD_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
      WP.seq (WP.mono (stageE_ok h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
        WP.seq (WP.mono (loop_ok hL hk h₄ q₄) fun _ ⟨h₅, _, q₅⟩ => stageG_ok hL hk h₅ q₅))))

/-! ## RFC 6979's result -/

/-- One `V` makes a candidate, or two if `wide`. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.F.H.D = P.nb := by
  have hs := P.sizes
  have h4 := P.R.n4
  rw [Spec.Ecdsa.Rfc6979.blocks]
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have h₁ := (P.R.sizesA hw).2.1; have h₂ := (P.R.sizesA hw).2.2.1
    simp only [RfcHash.nb, hw, Bool.false_eq_true, ite_false]
    exact Nat.div_eq_of_lt_le (by simp only [RfcHash.Q, RfcHash.w] at *; omega)
      (by simp only [RfcHash.Q, RfcHash.w] at *; omega)
  · obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hw
    have h₂ := (P.R.sizesW hw).2.2
    simp only [RfcHash.nb, hw, ite_true, h₂, hD64]

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ (State.addr L.d) (State.addr L.dg) =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.hH.SH.H P.F.H.D (xOf P L m₀) (eOf P L m₀) K V 8
      else (none, 0) := by
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve, P.hash, P.tries, P.len,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ (State.addr L.d) (State.addr L.dg)).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i 8 (by have := hx.lt; omega) hx.fails,
      show 8 - i = (7 - i) + 1 by have := hx.lt; omega]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
    | none =>
      have h7 : i = 7 := hx.last.resolve_left (by simp [hs])
      subst h7
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-! ## How many candidates -/

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  if (result P.I m₀ (State.addr L.d) (State.addr L.dg)).2 = 0 then 7 else (result P.I m₀ (State.addr L.d) (State.addr L.dg)).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {i : Nat} (hi : i < 8) (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < 8) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i 8 (by omega) hf, show 8 - i = (7 - i) + 1 by omega]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs]
      by_cases h7 : i + 1 < 8
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.hH.SH.H) (hlen := P.F.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := 6 - i)
          (K := (stepB P.ok.hH.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.hH.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
        rw [show 7 - i = 6 - i + 1 by omega]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega
      · have hi7 : i = 7 := by omega
        subst hi7
        simp [Spec.Ecdsa.Rfc6979.search]
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega

/-! ## The whole function -/

/-- Words stored at offsets apart from a range below them change nothing outside it. -/
theorem Outs.frame {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} {n : Nat}
    (h : VG.Proof.Mont.Outs base rs m m') (hr : ∀ r ∈ rs, r.1 + r.2 ≤ n) : Frame [⟨base, n⟩] m m' :=
  fun x hx => h x fun r hr' => .inr (by
    have := hx _ (List.mem_singleton_self _)
    simp only [Region.Contains] at this
    simp only [VG.Proof.Mont.ofs]
    have := hr r hr'; omega)

theorem saved_ne12 : ∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, p.1 ≠ .r12 := by decide

theorem saved_pairwise : Impl.Ecdsa.Rfc6979.Arm.saved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  decide

/-- The prologue: our caller's registers into the frame, and the pointers to the registers that keep them. -/
theorem entry_ok {s : State} (h : (rfcArm P.I (240 + 4 * P.e)).pre s) :
    WP isa (.block Cfg.prologue) (allocated (frameBytes P.R.wide) s)
      (Ctx (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s) s.gpr s.mem) := by
  have hL := lay_ok h
  obtain ⟨hrd, hwr, -⟩ := h
  have hA : State.addr (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s).fp =
      (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s).B + BitVec.ofNat 64 24 := hL.fpA0
  have hb := hL.B_fit
  have he := (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s).he
  simp only [Cfg.prologue, List.cons_append]
  refine wp_addSp (d := .r12) (imm := 0) (by decide) fun u₁ v₁ => ?_
  have h12 : u₁.gpr .r12 = (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s).fp := by
    rw [v₁.gpr, BitVec.add_zero]; rfl
  have hs : VG.Proof.Mont.Arm.Scr u₁ (State.addr (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s).fp) 216 :=
    ⟨by rw [h12], ⟨frameBytes P.R.wide, by simp only [frameBytes]; omega,
      by simp only [frameBytes]; have : extra P.R.wide ≤ 36 := by simp only [extra]; split <;> omega
         omega, by rw [v₁.wr]; exact List.mem_cons_self⟩,
      by rw [hA, Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega)]; omega, by omega⟩
  rw [WP.block_append_iff]
  refine WP.mono (Proof.Ecdsa.Arm.strs_ok hs _ (fun p hp => (saved_off p hp).2) saved_pairwise)
    fun u₂ ⟨K₂, O₂, V₂⟩ => ?_
  refine wp_mov (op2_reg _ _) fun u₃ v₃ => wp_mov (op2_reg _ _) fun u₄ v₄ => wp_mov (op2_reg _ _) fun u₅ v₅ => ?_
  refine wp_mov (op2_reg _ _) fun u₆ v₆ => wp_mov (op2_reg _ _) fun u₇ v₇ => WP.block_nil ?_
  have K : VG.Proof.X25519.Arm.Rest [.r4, .r5, .r6, .r11, .r8] u₂ u₇ :=
    (v₃.rest (by simp)).trans <| (v₄.rest (by simp)).trans <| (v₅.rest (by simp)).trans <|
    (v₆.rest (by simp)).trans (v₇.rest (by simp))
  have hm : u₇.mem = u₂.mem := by rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem]
  have g₂ : ∀ r, r ≠ .r12 → u₂.gpr r = s.gpr r := fun r hr => by rw [K₂.gpr r (by simp), v₁.other _ hr]; rfl
  refine ⟨by rw [K.rd, K₂.rd, v₁.rd]; exact hrd, ?_, by rw [K.sp, K₂.sp, v₁.sp]; rfl, ?_, ?_, ?_, ?_, ?_,
    fun p hp => ?_, ?_⟩
  · rw [K.wr, K₂.wr, v₁.wr]
    show ⟨State.addr (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s).fp, frameBytes P.R.wide⟩ :: s.wr = _
    rw [hA, hwr]
    rfl
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      g₂ _ (by decide)]; rfl
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr,
      v₃.other _ (by decide), g₂ _ (by decide)]; rfl
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide),
      v₃.other _ (by decide), g₂ _ (by decide)]; rfl
  · rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), K₂.gpr _ (by simp), h12]
  · rw [v₇.other _ (by decide), v₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), g₂ _ (by decide)]; rfl
  · rw [hm, ← Offset.add_add, ← hA, ← VG.Proof.Mont.off, V₂ p hp, v₁.other _ (saved_ne12 p hp)]; rfl
  · rw [hm, show s.mem = u₁.mem from v₁.mem.symm]
    refine (Outs.frame O₂ (n := 216) fun r hr => ?_).sub fun r hr => ?_
    · simp only [List.mem_map] at hr
      obtain ⟨q, hq, rfl⟩ := hr
      exact (saved_off q hq).2
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨(lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s).STK, by simp, by rw [hA]; exact Offset.sub_base _ (by omega)⟩

theorem low_preserved : ∀ r ∈ preserved, r ∈ Impl.Ecdsa.Rfc6979.Arm.saved.map Prod.fst := by decide

/-- `vg_ecdsa_<curve>_<hash>_sign` meets `rfcArm P.I` and keeps the
callee-saved registers and the stack pointer. -/
theorem coreOk_lay (P : RfcHash) (s : State) : CoreOk P (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s) :=
  ⟨P.curveLen, fun hw => by show P.Q ≤ P.I.hashLen; rw [P.len]; exact (P.sizesA hw).2.2, rfl⟩

theorem frameBytes_ok (wide : Bool) :
    0 < frameBytes wide ∧ frameBytes wide < 4096 ∧ frameBytes wide % 8 = 0 ∧
      encodable (BitVec.ofNat 32 (frameBytes wide)) = true := by
  cases wide <;> decide

/-- `vg_ecdsa_<curve>_<hash>_sign` meets `rfcArm P.I` and keeps the
callee-saved registers and the stack pointer. -/
theorem sign_ok {s : State} (h : (rfcArm P.I (240 + 4 * P.e)).pre s) :
    WP isa (cfgOf P).sign s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (rfcArm P.I (240 + 4 * P.e)).post s s' := by
  have hL := lay_ok h
  have hN : 240 + 4 * P.e ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hk := coreOk_lay P s
  have hfb : frameBytes (cfgOf P).wide = 216 + 4 * P.e := rfl
  refine WP.alloc (frameBytes_ok _) (by rw [hfb]; omega) ?_
  rw [Cfg.body, show Cfg.prologue ++ (if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++
    Cfg.initKV = Cfg.prologue ++ ((if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++
      Cfg.initKV) from List.append_assoc _ _ _]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok h) fun t hc => WP.mono (stageB_ok hL hk hc) fun u ⟨hu, hq⟩ => ?_
  refine WP.mono (rest_ok hL hk hu hq) fun v ⟨hwr, hsp, hs, i, hx⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · show (freed (frameBytes (cfgOf P).wide) v).gpr r = _
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (low_preserved r hr)
    exact hs p hp
  · show v.sp + BitVec.ofNat 32 (frameBytes (cfgOf P).wide) = s.sp
    rw [hsp]; exact BitVec.sub_add_cancel _ _
  · show match (result P.I s.mem (State.addr (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s).d) (State.addr (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s).dg)).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    have e₂ : P.I.ecdsa.curve = P.R.E.C := by rw [P.ecdsa, P.R.curve]
    rw [e₁, e₂]
    have hr := hx.res
    unfold ResultIs at hr
    show match sigI P (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s) s.mem i with | some rs => _ | none => _
    cases hsig : sigI P (lay P.I.hashLen P.I.ecdsa.curve.len P.R.wide s) s.mem i <;> rw [hsig] at hr <;>
      exact ⟨by rw [low_word]; exact hr.1, hr.2⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
