import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Loop

/-!
# Deterministic ECDSA on AArch64: correctness

The loop leaves it at a candidate that is suitable or the last (`loop_ok`);
before it, `h` (or, if two `V`s make a candidate, the zero bytes and the
digest after `d` in the messages of steps d and f), `K`, `V`, `core`'s
digest and the count are as RFC 6979's steps a–g make them (`stageB_ok` …
`stageE_ok`); and the signature of that candidate is RFC 6979's
(`result_eq`), for the hash function `P`'s instance of the contract.
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The loop -/

theorem loop_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne (.nonzero .x .x12)) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (8 - n) s ∧ n ≤ 8) ?_ 8 t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega_arith
  refine WP.mono (tryOne_ok hL hk hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega_arith, hc', ?_, by omega_arith⟩
    rwa [show 8 - (n - 1) = 8 - n + 1 by omega_arith]

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
  h : tailOf P L P.R.wide u.mem = dB P L m₀ ++ hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.H.D 0
  v : vOf P L u.mem = List.replicate P.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  h : tailOf P L P.R.wide u.mem = dB P L m₀ ++ hSpec P L m₀
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

/-- `core`'s digest, unless two `V`s make a candidate: the digest, whose
leftmost `Q` bytes it reads. -/
theorem dgOk_narrow (hL : L.Ok) (hk : CoreOk P L) (hw : P.R.wide = false) {u : State} (hc : Ctx L g m₀ u) :
    DgOk P L m₀ u.mem := by
  obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
  have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
    have h₁ := (P.R.sizesA hw).2.1; have h₂ := (P.R.sizesA hw).2.2.1; show _ = 8 * P.R.E.C.len; omega_arith
  have hD : P.Q ≤ P.I.hashLen := by rw [P.len]; exact hQD
  have hLw : L.wide = false := hk.2.2.trans hw
  unfold DgOk
  simp only [dgAddr, hLw, Bool.false_eq_true, ite_false, eOf, hBOf]
  rw [hc.dgBytes hL hD, hashToInt_takeQ hB (by rw [length_bytesAt]),
    List.take_of_length_le (by rw [length_bytesAt]), hashToInt_takeQ hB (by rw [length_bytesAt]; exact hQD),
    ← bytesAt_take _ _ hQD]

theorem stageB_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hsi : u.gpr .x1 = L.dg) :
    WP isa (cfgOf P).start u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  have hD : P.H.D = P.I.hashLen := P.len.symm
  have nB := hL.nB
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
      have h₁ := (P.R.sizesA hw).2.1; have h₂ := (P.R.sizesA hw).2.2.1; show _ = 8 * P.R.E.C.len; omega_arith
    have hwc : (cfgOf P).wide = false := hw
    have hLw : L.wide = false := hk.2.2.trans hw
    have he : L.e = 0 := by rw [L.ew, hLw]; rfl
    simp only [Cfg.start, hwc, Bool.false_eq_true, ite_false]
    rw [WP.block_append_iff]
    refine WP.mono (reduce_ok (P := P) hw hL hc hsi (by rw [← hD]; exact hQD)) fun u₁ ⟨hc₁, _, hh₁⟩ => ?_
    refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
      ⟨hc₂, ?_, hk₂ _ (by anums), hv₂ _ (by anums), dgOk_narrow hL hk hw hc₂⟩
    have e₁ : hOf P L u₂.mem = hOf P L u₁.mem := bytesAt_frame (p := L.B + BitVec.ofNat 64 144) (n := P.Q) hf₂
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      (by omega_arith)
    have e₂ : Spec.Sha256.bytesAt u₂.mem L.d P.Q = dB P L m₀ := hc₂.dBytes hL (by rw [hk.1])
    simp only [tailOf, hw, Bool.false_eq_true, ite_false]
    rw [e₁, e₂, hOf, hh₁]
    rw [hSpec, bits2octets_eqQ hB (by rw [hBOf, length_bytesAt]; exact hQD), hBOf,
      ← bytesAt_take m₀ L.dg hQD]
  · obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hw
    have hl := P.R.nBits_len
    have hN := (P.R.sizesW hw).2.2
    have hwc : (cfgOf P).wide = true := hw
    have hLw : L.wide = true := hk.2.2.trans hw
    have he : L.e = 144 := e144 hk.2.2 hw
    simp only [Cfg.start, hwc, ite_true]
    refine WP.seq (WP.mono (coreDigest_ok hL hk.2.2 hw (by rw [← hD]) hc hsi) fun u₁ ⟨hc₁, hf₁, hx₁⟩ => ?_)
    refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
      ⟨hc₂, ?_, hk₂ _ (by anums), hv₂ _ (by anums), ?_⟩
    · simp only [tailOf, hw, ite_true]
      rw [hc₂.dBytes hL (by rw [hk.1]), hc₂.dgBytes hL (by rw [← hD]), hSpec,
        bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_arith)
        (by show 8 * P.R.E.C.len < _; omega_arith) (by rw [hBOf, length_bytesAt]; omega_arith) P.R.n_ne,
        hBOf, length_bytesAt, List.append_assoc]
    · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
      have hX : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) P.Q = Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ P.R.sh) := by
        rw [bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
            (by omega_arith), hx₁, hc.dgBytes hL (by rw [← hD])]
      have hlt : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ P.R.sh <
          2 ^ (8 * P.Q) := by
        have := ofBytes_lt (Spec.Sha256.bytesAt m₀ L.dg P.H.D)
        rw [length_bytesAt] at this
        calc _ < 2 ^ (8 * P.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega_arith) (by omega_arith)
      have hl₁ : (Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) * 2 ^ P.R.sh)).length = P.Q := by
        simp [Spec.Weierstrass.toBytes]
      have e₁ : Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) P.Q) =
          Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) := by
        rw [hX, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_arith) (by rw [hl₁]),
          List.take_of_length_le (by rw [hl₁]), ofBytes_toBytes _ _ hlt,
          show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
          Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.dg P.H.D) :=
        (hashToInt_short (h := Spec.Sha256.bytesAt m₀ L.dg P.H.D) (by rw [length_bytesAt]; omega_arith)
          P.R.n_ne).1
      unfold DgOk
      simp only [dgAddr, hLw, ite_true]
      rw [e₁, e₂]

theorem kvw_h (hL : L.Ok) {n : Nat} (hn : n ≤ 48) :
    ∀ r ∈ KVW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 144, n⟩ r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hL.stk_SCR (by omega_arith)
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

/-- `d ‖ h` in the messages, kept by the steps on `K` and `V`. -/
theorem tailOf_kvw (hL : L.Ok) (hk : CoreOk P L) {m m' : Mem} (hf : Frame (KVW L) m m') :
    tailOf P L P.R.wide m' = tailOf P L P.R.wide m := by
  have nB := hL.nB
  have hs := P.wsizes
  have hdk : ∀ {n : Nat}, n ≤ L.q → ∀ r ∈ KVW L, Region.Disjoint ⟨L.d, n⟩ r := fun hn r hr => by
    have hD : Region.Sub ⟨L.d, _⟩ L.D := Region.sub_prefix hn
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.dc.sub_left hD
    · exact (hL.kd.symm.sub_left hD).sub_right (Region.sub_prefix (by omega_arith))
  cases hw : P.R.wide
  · obtain ⟨hQ8, h6, hQD⟩ := P.sizesA hw
    simp only [tailOf, Bool.false_eq_true, ite_false]
    refine congrArg₂ (· ++ ·) (bytesAt_frame hf (hdk (by rw [hk.1])) (by omega_arith)) ?_
    exact bytesAt_frame hf (kvw_h hL (by omega_arith)) (by omega_arith)
  · simp only [tailOf, ite_true]
    have hDG : Region.Sub ⟨L.dg, P.H.D⟩ L.DG := Region.sub_prefix (by rw [P.len])
    refine congrArg₂ (· ++ ·) (congrArg (· ++ _) (bytesAt_frame hf (hdk (by rw [hk.1])) (by omega_arith)))
      (bytesAt_frame hf (fun r hr => ?_) (by anums))
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hL.gc.sub_left hDG
    · exact (hL.kg.symm.sub_left hDG).sub_right (Region.sub_prefix (by omega_arith))

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk.1 P.len hc 0) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨hc', (tailOf_kvw hL hk hf').trans hq.h, by rw [hk', hq.k, hq.v, hq.h],
      by rw [hv', hk', hq.k, hq.v, hq.h], hq.dg.frameOf hL hk hf' kvw_apart⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk.1 P.len hc 1) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h], by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h],
      hq.dg.frameOf hL hk hf' kvw_apart⟩

theorem stageE_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', by omega_arith,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hq.v,
    by rw [hn'], fun j hj => absurd hj (Nat.not_lt_zero _),
    hq.dg.frameOf hL hk hf' fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [DgApart]⟩

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block (Cfg.wipe (cfgOf P).wide)) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' := by
  have hw : (cfgOf P).wide = L.wide := hk.2.2.symm
  have := L.he
  have := hL.nB
  rw [hw]
  exact WP.mono (wipe_ok hL hc L.ew.symm) fun _ ⟨hc₇, ha₇, hf₇⟩ => ⟨hc₇, hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (by omega_arith)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by anums))⟩

/-- The frame's body, once the arguments are saved. -/
theorem body_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block Cfg.digestPtr)
      (.seq (cfgOf P).start
      (.seq ((cfgOf P).rekeyFull 0)
      (.seq ((cfgOf P).rekeyFull 1)
      (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne (.nonzero .x .x12))
        (.block (Cfg.wipe (cfgOf P).wide)))))))) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' :=
  WP.seq (WP.mono (digestPtr_ok hL hc) fun _ h₀ =>
    WP.seq (WP.mono (stageB_ok hL hk h₀.ctx h₀.val) fun _ ⟨h₁, q₁⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
          WP.seq (WP.mono (stageE_ok hL hk h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
            WP.seq (WP.mono (loop_ok hL hk h₄ q₄) fun _ ⟨h₅, i, q₅⟩ =>
              WP.mono (stageG_ok hL hk h₅ q₅) fun _ ⟨h₆, q₆⟩ => ⟨h₆, i, q₆⟩))))))

/-! ## RFC 6979's result -/

/-- One `V` makes a candidate, or two if `wide`. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = P.nb := by
  have hs := P.sizes
  have h4 := P.R.n4
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
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i 8 (by have := hx.lt; omega_arith) hx.fails,
      show 8 - i = (7 - i) + 1 by have := hx.lt; omega_arith]
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
def exitAt (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : Nat :=
  if (result P.I m₀ L.d L.dg).2 = 0 then 7 else (result P.I m₀ L.d L.dg).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {i : Nat} (hi : i < 8) (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < 8) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i 8 (by omega_arith) hf, show 8 - i = (7 - i) + 1 by omega_arith]
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
        rw [show 7 - i = 6 - i + 1 by omega_arith]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega_arith
      · have hi7 : i = 7 := by omega_arith
        subst hi7
        simp [Spec.Ecdsa.Rfc6979.search]
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega_arith

/-! ## The whole function -/

theorem coreOk_lay (P : RfcHash) (s : State) : CoreOk P (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E P.R.wide s) :=
  ⟨P.curveLen, fun hw => by show P.Q ≤ P.I.hashLen; rw [P.len]; exact (P.sizesA hw).2.2, rfl⟩

/-- `vg_ecdsa_<curve>_<hash>_sign` meets `rfcAArch64 P.R.E P.I` and keeps the
callee-saved registers and the stack pointer. -/
theorem sign_ok {s : State} (h : (rfcAArch64 P.R.E P.I (256 + P.e)).pre s) :
    WP isa (cfgOf P).sign s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (rfcAArch64 P.R.E P.I (256 + P.e)).post s s' := by
  have hL := lay_ok h
  have hN : 256 + P.e ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk := coreOk_lay P s
  have he : P.e ≤ 144 := P.wsizes.2.2.2.2.2.2
  have hfb : frameBytes (cfgOf P).wide = 224 + P.e := rfl
  have hfa : ∀ w, 0 < frameBytes w ∧ frameBytes w < 4096 ∧ frameBytes w % 16 = 0 := fun w => by
    cases w <;> decide
  have hfe : 16 + frameBytes (cfgOf P).wide = 240 + (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E P.R.wide s).e := by
    show 16 + (224 + extra P.R.wide) = 240 + extra P.R.wide; omega_arith
  have hft : 16 + (frameBytes (cfgOf P).wide + 16) = 256 + extra P.R.wide := by
    show 16 + (224 + extra P.R.wide + 16) = 256 + extra P.R.wide; omega_arith
  refine WP.frame (by omega_arith) (WP.alloc (hfa _) ?_ ?_)
  · show frameBytes (cfgOf P).wide ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_arith), hfb]
    show 224 + P.e ≤ s.sp.toNat - 16
    omega_arith
  · show WP isa (cfgOf P).body (entered P.R.wide s) _
    refine WP.seq (WP.mono (entry_ok h) fun t hc => ?_)
    refine WP.mono (body_ok hL hk hc) fun u ⟨hu, i, hx⟩ => ?_
    have lr : u.mem.read (u.sp + BitVec.ofNat 64 (frameBytes (cfgOf P).wide)) 8 = s.gpr .x30 := by
      rw [hu.sp, Offset.add_add, read8, hfe]; exact hu.lr
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · show ((freed (frameBytes (cfgOf P).wide) u).write .x .x30
        (u.mem.read (u.sp + BitVec.ofNat 64 (frameBytes (cfgOf P).wide)) 8)).gpr r = _
      rw [lr, RegUpd.gpr_write]
      by_cases h30 : r = .x30
      · subst r; simp only [ite_true, BitVec.setWidth_eq]
      · simp only [h30, ite_false]
        exact hu.cs r hr h30
    · show u.sp + BitVec.ofNat 64 (frameBytes (cfgOf P).wide) + BitVec.ofNat 64 16 = s.sp
      rw [hu.sp, Offset.add_add, Offset.add_add, hft]
      exact lay_top _ _ _ _ s
    · show match (result P.I s.mem (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E P.R.wide s).d
          (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E P.R.wide s).dg).1 with
        | some rs => _ | none => _
      have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
      have e₂ : Spec.Ecdsa.encode P.I.ecdsa.curve = Spec.Ecdsa.encode P.R.E.C := by rw [P.ecdsa, P.R.curve]
      rw [result_eq hx, e₁, e₂]
      exact hx.res.keep (by
        show ((freed (frameBytes (cfgOf P).wide) u).write .x .x30
          (u.mem.read (u.sp + BitVec.ofNat 64 (frameBytes (cfgOf P).wide)) 8)).gpr .x0 = _
        exact RegUpd.gpr_write_of_ne _ _ _ (by decide)) rfl

end VG.Proof.Ecdsa.Rfc6979.AArch64
