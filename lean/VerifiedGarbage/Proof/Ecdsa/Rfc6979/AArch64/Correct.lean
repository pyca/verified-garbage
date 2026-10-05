import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Loop

/-!
# Deterministic ECDSA on AArch64: correctness

The loop leaves it at a candidate that is suitable or the last (`loop_ok`);
before it, `h`, `K`, `V` and the count are as RFC 6979's steps a–g make them
(`pre_ok`); and the signature of that candidate is RFC 6979's (`result_eq`),
for the hash function `P`'s instance of the contract.
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Ecdsa.Rfc6979 (kvAt candAt step)

variable {P : RfcHash} {L : Lay P.I.hashLen P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- HMAC's output is the hash function's. -/
theorem mac_length (P : RfcHash) (K t : List Byte) : (P.mac K t).length = P.H.D := by
  have := P.ok.sizes.DN
  simp only [RfcHash.mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.ok.hash, List.length_take,
    Proof.MdStream.Md.hash, P.ok.md.digest_length]
  omega

/-! ## The loop -/

theorem loop_ok (hL : L.Ok) (hq : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne (.nonzero .x .x12)) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (8 - n) s ∧ n ≤ 8) ?_ 8 t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega
  refine WP.mono (tryOne_ok hL hq hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega, hc', ?_, by omega⟩
    rwa [show 8 - (n - 1) = 8 - n + 1 by omega]

/-! ## Steps a–g -/

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : RfcHash) {x : Nat} {dB hB h : List Byte} (hd : dB.length = 8 * P.w)
    (hx : x = Spec.Weierstrass.ofBytes dB) (hh : Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C hB = h) :
    Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.SH.H P.H.D x hB =
      let K₁ := P.mac (List.replicate P.H.D 0) (List.replicate P.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * (8 * P.w) := by rw [P.R.nBits]; show 64 * P.w = _; omega
  have hi : Spec.Ecdsa.Rfc6979.int2octets P.R.E.C x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlenQ hB, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d (8 * P.w)

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.H.D 0) (List.replicate P.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.H.D 1)

/-- After step c: `h`, `V = 0x01…` and `K = 0x00…`. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.H.D 0
  v : vOf P L u.mem = List.replicate P.H.D 1

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hsi : u.gpr .x1 = L.dg) :
    WP isa (.block ((cfgOf P).reduce ++ Cfg.initKV)) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  have hD : 8 * P.w ≤ P.H.D := by anums
  have h6 : P.w ≤ 6 := by anums
  have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * (8 * P.w) := by rw [P.R.nBits]; show 64 * P.w = _; omega
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok (P := P) hL hc hsi P.lenQ) fun u₁ ⟨hc₁, _, hh₁⟩ => ?_
  refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
    ⟨hc₂, ?_, hk₂ _ (by anums), hv₂ _ (by anums)⟩
  rw [show hOf P L u₂.mem = hOf P L u₁.mem from bytesAt_frame hf₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
  rw [hSpec, bits2octets_eqQ hB (by rw [hBOf, length_bytesAt]; exact hD), hBOf, ← bytesAt_take m₀ L.dg hD]
  exact hh₁

theorem kvw_h (hL : L.Ok) {n : Nat} (hn : n ≤ 48) :
    ∀ r ∈ KVW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 144, n⟩ r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hL.stk_SCR (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)

theorem stageC_ok (hL : L.Ok) (hw : L.q = 8 * P.w) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (by rw [hw]) hc 0) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨hc', (bytesAt_frame hf' (kvw_h hL (by anums)) (by anums)).trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hw])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hw])]⟩

theorem stageD_ok (hL : L.Ok) (hw : L.q = 8 * P.w) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (by rw [hw]) hc 1) fun u' ⟨hc', _, hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hw])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hw])]⟩

theorem stageE_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', by omega,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hq.v,
    by rw [hn'], fun j hj => absurd hj (Nat.not_lt_zero _)⟩

theorem stageG_ok (hL : L.Ok) (hw : L.q = 8 * P.w) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block Cfg.wipe) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' :=
  WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, ha₇, hf₇⟩ => ⟨hc₇, hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_OUT (by omega)).symm.sub_left (Region.sub_prefix (by rw [hw]; omega))) (by anums))⟩

/-- The frame's body, once the arguments are saved. -/
theorem body_ok (hL : L.Ok) (hw : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block Cfg.digestPtr)
      (.seq (.block ((cfgOf P).reduce ++ Cfg.initKV))
      (.seq ((cfgOf P).rekeyFull 0)
      (.seq ((cfgOf P).rekeyFull 1)
      (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne (.nonzero .x .x12))
        (.block Cfg.wipe))))))) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' :=
  WP.seq (WP.mono (digestPtr_ok hL hc) fun _ h₀ =>
    WP.seq (WP.mono (stageB_ok hL h₀.ctx h₀.val) fun _ ⟨h₁, q₁⟩ =>
      WP.seq (WP.mono (stageC_ok hL hw h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
        WP.seq (WP.mono (stageD_ok hL hw h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
          WP.seq (WP.mono (stageE_ok hL h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
            WP.seq (WP.mono (loop_ok hL hw h₄ q₄) fun _ ⟨h₅, i, q₅⟩ =>
              WP.mono (stageG_ok hL hw h₅ q₅) fun _ ⟨h₆, q₆⟩ => ⟨h₆, i, q₆⟩))))))

/-! ## RFC 6979's result -/

/-- One `V` makes a candidate. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = 1 := by
  have hD : 8 * P.w ≤ P.H.D := by anums
  have h4 : 4 ≤ P.w := by anums
  have hw : P.w = P.R.E.n := rfl
  rw [Spec.Ecdsa.Rfc6979.blocks, P.R.nBits]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

theorem bits2int_cand (i : Nat) :
    Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i ++ []) =
      Spec.Weierstrass.ofBytes ((candI P L m₀ i).take (8 * P.w)) := by
  have hl : (candI P L m₀ i).length = P.H.D := mac_length P _ _
  have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * (8 * P.w) := by rw [P.R.nBits]; show 64 * P.w = _; omega
  rw [List.append_nil, Spec.Ecdsa.Rfc6979.bits2int, hashToInt_takeQ hB (by rw [hl]; anums)]

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.SH.H P.H.D (xOf P L m₀) (eOf P L m₀) K V 8
      else (none, 0) := by
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve, P.R.len, P.hash, P.tries, P.len,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    have hf : ∀ j < i, Spec.Ecdsa.signWith P.R.E.C (xOf P L m₀) (eOf P L m₀)
        (Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ j ++ [])) = none := fun j hj => by
      rw [bits2int_cand]; exact hx.fails j hj
    rw [Proof.Ecdsa.Rfc6979.search_shift (blocks_eq P) i 8 (by have := hx.lt; omega) hf,
      show 8 - i = (7 - i) + 1 by have := hx.lt; omega]
    have hc : Spec.Hmac.hmac P.ok.SH.H (kvI P L m₀ i).1 (kvI P L m₀ i).2 = candI P L m₀ i := rfl
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.search_ok (blocks_eq P) (by rw [hc, bits2int_cand]; exact hs)]
    | none =>
      have h7 : i = 7 := hx.last.resolve_left (by simp [hs])
      subst h7
      rw [Proof.Ecdsa.Rfc6979.search_fail (blocks_eq P) (by rw [hc, bits2int_cand]; exact hs)]
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
    have hf' : ∀ j < i, Spec.Ecdsa.signWith P.R.E.C (xOf P L m₀) (eOf P L m₀)
        (Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ j ++ [])) = none := fun j hj => by
      rw [bits2int_cand]; exact hf j hj
    rw [Proof.Ecdsa.Rfc6979.search_shift (blocks_eq P) i 8 (by omega) hf', show 8 - i = (7 - i) + 1 by omega]
    have hc : Spec.Hmac.hmac P.ok.SH.H (kvI P L m₀ i).1 (kvI P L m₀ i).2 = candI P L m₀ i := rfl
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.search_ok (blocks_eq P) (by rw [hc, bits2int_cand]; exact hs)]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.search_fail (blocks_eq P) (by rw [hc, bits2int_cand]; exact hs)]
      by_cases h7 : i + 1 < 8
      · have := Proof.Ecdsa.Rfc6979.search_pos (C := P.R.E.C) (H := P.ok.SH.H) (hlen := P.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := 6 - i)
          (K := (step P.ok.SH.H (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (step P.ok.SH.H (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
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

/-- `vg_ecdsa_<curve>_<hash>_sign` meets `rfcAArch64 P.R.E P.I` and keeps the
callee-saved registers and the stack pointer. -/
theorem sign_ok {s : State} (h : (rfcAArch64 P.R.E P.I).pre s) :
    WP isa (cfgOf P).sign s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (rfcAArch64 P.R.E P.I).post s s' := by
  have hL := lay_ok h
  have h256 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hw : (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E s).q = 8 * P.w := P.curveLen
  refine WP.frame (by omega) (WP.alloc (by decide) ?_ ?_)
  · show 224 ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega)]
    show 224 ≤ s.sp.toNat - 16
    omega
  · show WP isa (cfgOf P).body (entered s) _
    refine WP.seq (WP.mono (entry_ok h) fun t hc => ?_)
    refine WP.mono (body_ok hL hw hc) fun u ⟨hu, i, hx⟩ => ?_
    have lr : u.mem.read (u.sp + BitVec.ofNat 64 frameBytes) 8 = s.gpr .x30 := by
      rw [hu.sp, Offset.add_add, read8]; exact hu.lr
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · show ((freed frameBytes u).write .x .x30 (u.mem.read (u.sp + BitVec.ofNat 64 frameBytes) 8)).gpr r = _
      rw [lr, RegUpd.gpr_write]
      by_cases h30 : r = .x30
      · subst r; simp only [ite_true, BitVec.setWidth_eq]
      · simp only [h30, ite_false]
        exact hu.cs r hr h30
    · show u.sp + BitVec.ofNat 64 frameBytes + BitVec.ofNat 64 16 = s.sp
      rw [hu.sp, Offset.add_add, Offset.add_add]
      exact lay_top _ _ _ s
    · show match (result P.I s.mem (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E s).d
          (lay P.I.hashLen P.I.ecdsa.curve.len P.R.E s).dg).1 with
        | some rs => _ | none => _
      have e₁ : 2 * P.I.ecdsa.curve.len = 16 * P.w := by rw [P.curveLen]; omega
      have e₂ : Spec.Ecdsa.encode P.I.ecdsa.curve = Spec.Ecdsa.encode P.R.E.C := by rw [P.ecdsa, P.R.curve]
      rw [result_eq hx, e₁, e₂]
      exact hx.res.keep (by
        show ((freed frameBytes u).write .x .x30 (u.mem.read (u.sp + BitVec.ofNat 64 frameBytes) 8)).gpr .x0 = _
        exact RegUpd.gpr_write_of_ne _ _ _ (by decide)) rfl

end VG.Proof.Ecdsa.Rfc6979.AArch64
