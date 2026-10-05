import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Loop

/-!
# Deterministic ECDSA on x86-64: correctness

The loop leaves it at a candidate that is suitable or the last (`loop_ok`);
before it, `h`, `K`, `V`, `core`'s digest and the count are as RFC 6979's
steps a–g make them (`stageB_ok` … `stageE_ok`); and the signature of that
candidate is RFC 6979's (`result_eq`), for the hash function `P`'s instance
of the contract.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {m₀ : Mem}

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
theorem dgOk_narrow (hL : L.Ok) (hw : P.R.wide = false) {u : State} (hc : Ctx L g m₀ u) : DgOk P L m₀ u.mem := by
  obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
  have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
    have h₁ := (P.R.sizesA hw).2.1; have h₂ := (P.R.sizesA hw).2.2.1; show _ = 8 * P.R.E.C.len; omega
  have hD : P.Q ≤ P.I.hashLen := by rw [P.len]; exact hQD
  unfold DgOk
  simp only [dgArg, hw, Bool.false_eq_true, ite_false, eOf, hBOf]
  rw [hc.dgBytes hL hD, hashToInt_takeQ hB (by rw [length_bytesAt]),
    List.take_of_length_le (by rw [length_bytesAt]), hashToInt_takeQ hB (by rw [length_bytesAt]; exact hQD),
    ← bytesAt_take _ _ hQD]

theorem stageB_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hsi : u.gpr .rsi = L.dg)
    (hdi : P.R.wide = true → u.gpr .rdi = L.scr) :
    WP isa (.block ((if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++ Cfg.initKV)) u
      fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  have hD : P.H.D = P.I.hashLen := P.len.symm
  rw [WP.block_append_iff]
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
      have h₁ := (P.R.sizesA hw).2.1; have h₂ := (P.R.sizesA hw).2.2.1; show _ = 8 * P.R.E.C.len; omega
    have hwc : (cfgOf P).wide = false := hw
    simp only [hwc, Bool.false_eq_true, ite_false]
    refine WP.mono (reduce_ok (P := P) hw hL hc hsi (by rw [← hD]; omega)) fun u₁ ⟨hc₁, _, hh₁⟩ => ?_
    refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
      ⟨hc₂, ?_, hk₂ _ (by nums), hv₂ _ (by nums), dgOk_narrow hL hw hc₂⟩
    simp only [hOf, hPart, hw, Bool.false_eq_true, ite_false]
    rw [bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
    rw [hSpec, bits2octets_eqQ hB (by rw [hBOf, length_bytesAt]; exact hQD), hBOf, ← bytesAt_take m₀ L.dg hQD]
    rw [show P.Q = 8 * P.w by omega]
    exact hh₁
  · obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hw
    have hl := P.R.nBits_len
    have hN := (P.R.sizesW hw).2.2
    have hsh := sh7 hw
    have hwc : (cfgOf P).wide = true := hw
    simp only [hwc, ite_true]
    refine WP.mono (coreDigest_ok hL hk.2.2.1 hw (by rw [← hD]) hc hsi (hdi hw)) fun u₁ ⟨hc₁, hf₁, hx₁⟩ => ?_
    refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
      ⟨hc₂, ?_, hk₂ _ (by nums), hv₂ _ (by nums), ?_⟩
    · simp only [hOf, hPart, hw, ite_true]
      rw [hc₂.dgBytes hL (by rw [← hD]), hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega)
        (by show 8 * P.R.E.C.len < _; omega) (by rw [hBOf, length_bytesAt]; omega) P.R.n_ne,
        hBOf, length_bytesAt]
    · have he : L.e = 18 := e18 hk.2.2.1 hw
      -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
      have hX : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) P.Q = Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ P.R.sh) := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
            (by omega), hx₁, hc.dgBytes hL (by rw [← hD])]
      have hlt : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ P.R.sh < 2 ^ (8 * P.Q) := by
        have := ofBytes_lt (Spec.Sha256.bytesAt m₀ L.dg P.H.D)
        rw [length_bytesAt] at this
        calc _ < 2 ^ (8 * P.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by omega)
      have hl₁ : (Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ P.R.sh)).length = P.Q := by
        simp [Spec.Weierstrass.toBytes]
      have e₁ : Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) P.Q) =
          Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) := by
        rw [hX, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega) (by rw [hl₁]),
          List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
          show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
          Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) :=
        (hashToInt_short (h := Spec.Sha256.bytesAt m₀ L.dg P.H.D) (by rw [length_bytesAt]; omega) P.R.n_ne).1
      unfold DgOk
      simp only [dgArg, hw, ite_true]
      rw [e₁, e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_kvw (hL : L.Ok) {m m' : Mem} (hf : Frame (KVW L) m m') : hOf P L m' = hOf P L m := by
  have hs := P.sizes
  simp only [hOf, hPart]
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    simp only [Bool.false_eq_true, ite_false]
    refine bytesAt_frame hf (fun r hr => ?_) (by omega)
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.stk_SCR (by omega)
    · exact Offset.disjoint_base _ (by omega) (by omega)
  · simp only [ite_true]
    refine congrArg (_ ++ ·) (bytesAt_frame hf (fun r hr => ?_) (by nums))
    have hD : Region.Sub ⟨L.dg, P.H.D⟩ L.DG := Region.sub_prefix (by rw [P.len])
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.gc.sub_left hD
    · exact (hL.kg.symm.sub_left hD).sub_right (Region.sub_prefix (by omega))

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc 0) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨(hOf_kvw hL hf').trans hq.h,
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
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', by omega,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.v,
    by rw [hn'], fun j hj => absurd hj (Nat.not_lt_zero _), hq.dg.frameOf hL hk hf' (by simp [DgApart])⟩

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block (cfgOf P).wipe) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' :=
  WP.mono (wipe_ok hL hk.2.2.1 hc) fun _ ⟨hc₇, ha₇, hf₇⟩ => ⟨hc₇, hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      have := L.he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (by omega)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by nums))⟩

theorem body_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).body t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' :=
  WP.seq (WP.mono (digestPtr_ok hL hc) fun _ ⟨h₀, _, hsi, hdi⟩ =>
    WP.seq (WP.mono (stageB_ok hL hk h₀ hsi hdi) fun _ ⟨h₁, q₁⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
          WP.seq (WP.mono (stageE_ok hL hk h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
            WP.seq (WP.mono (loop_ok hL hk h₄ q₄) fun _ ⟨h₅, i, q₅⟩ =>
              WP.mono (stageG_ok hL hk h₅ q₅) fun _ ⟨h₆, q₆⟩ => ⟨h₆, i, q₆⟩))))))

/-! ## RFC 6979's result -/

/-- One `V` makes a candidate, or two if `wide`. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = P.nb := by
  have hs := P.sizes
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
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.SH.H P.H.D (xOf P L m₀) (eOf P L m₀) K V 8
      else (none, 0) := by
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve, P.hash, P.tries, P.len,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
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
  if (result P.I m₀ L.d L.dg).2 = 0 then 7 else (result P.I m₀ L.d L.dg).2 - 1

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
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.SH.H) (hlen := P.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := 6 - i)
          (K := (stepB P.ok.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.SH.H P.nb (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
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

theorem pop_rsp (B : Addr) (e : Nat) :
    B + BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * (27 + e)) = B + BitVec.ofNat 64 (240 + 8 * e) := by
  rw [Offset.add_add, show 24 + 8 * (27 + e) = 240 + 8 * e by omega]

theorem sign_eq (P : RfcHash) :
    (cfgOf P).sign = .frame (.push (pushRs P.e)) (cfgOf P).body (.pop .rcx (pushRs P.e).length) := by
  rw [pushRs_length]; rfl

theorem coreOk_lay (P : RfcHash) (he : P.e ≤ 18) (s : State) :
    CoreOk P (lay P.I.hashLen P.I.ecdsa.curve.len P.e he P.R.E.combConsts s) :=
  ⟨P.curveLen, fun hw => by show P.Q ≤ P.I.hashLen; rw [P.len]; exact (P.sizesA hw).2.2, rfl, rfl⟩

/-- `vg_ecdsa_<curve>_<hash>_sign` meets `rfcX86_64 P.I` and keeps the
callee-saved registers and its return address. -/
theorem sign_ok {s : State} (h : (rfcX86_64 P.R.E.combConsts P.I (240 + 8 * P.e)).pre s) :
    WP isa (cfgOf P).sign s fun s' =>
      gprPreserved s s' ∧ (rfcX86_64 P.R.E.combConsts P.I (240 + 8 * P.e)).post s s' := by
  have he : P.e ≤ 18 := by nums
  have hL := lay_ok he h
  have hc := push_ctx he h
  rw [sign_eq]
  refine WP.frame (rs := pushRs P.e) (by simp [pushRs]) (by simp [pushRs]) (by decide)
    (by rw [pushRs_length]; have := h.1; omega)
    (WP.mono (body_ok hL (coreOk_lay P he s) hc) fun u ⟨hu, i, hx⟩ =>
      ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rcx (pushRs P.e).length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, pushRs_length, pop_rsp, lay_ret]
    refine ⟨fun r hr => ?_, ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (lay P.I.hashLen P.I.ecdsa.curve.len P.e he P.R.E.combConsts s).RET) ?_ ?_ (by decide)
      · show (⟨_ + BitVec.ofNat 64 (240 + 8 * P.e), 8⟩ : Region).Contains (s.gpr .rsp) 8
        rw [lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · have := (lay P.I.hashLen P.I.ecdsa.curve.len P.e he P.R.E.combConsts s).he
          exact Offset.disjoint_base _ (by omega) (by omega)
  · show match (result P.I s.mem (lay P.I.hashLen P.I.ecdsa.curve.len P.e he P.R.E.combConsts s).d
        (lay P.I.hashLen P.I.ecdsa.curve.len P.e he P.R.E.combConsts s).dg).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    have e₂ : P.I.ecdsa.curve = P.R.E.C := by rw [P.ecdsa, P.R.curve]
    rw [e₁, e₂]
    exact hx.res.keep (popped_gpr _ _ _ (by decide) (by decide)) (by rw [popped_mem])

end VG.Proof.Ecdsa.Rfc6979.X86_64
