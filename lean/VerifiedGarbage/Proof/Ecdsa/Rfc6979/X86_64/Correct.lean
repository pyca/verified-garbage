module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Loop
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Prep

/-!
# Deterministic ECDSA on x86-64: correctness

The loop leaves it at a candidate that is suitable or the last (`loop_ok`);
before it, `h`, `K`, `V`, `core`'s digest and the count are as RFC 6979's
steps a–g make them (`stageB_ok` … `stageE_ok`); and the signature of that
candidate is RFC 6979's (`result_eq`), for the hash function `P`'s instance
of the contract.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The loop -/

theorem loop_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne .ne) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (P.I.tries - n) s ∧ n ≤ P.I.tries)
    ?_ P.I.tries t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega_using [this]
  refine WP.mono (tryOne_ok hL hk hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega_using [hn1], hc', ?_, by omega_using [hn]⟩
    rwa [show P.I.tries - (n - 1) = P.I.tries - n + 1 by omega_using [hn, hn1]]

/-! ## Steps a–g -/

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.E.C = P.Q := by
  have := P.R.nBits_len
  exact rlenR (by show _ ≤ 8 * P.R.E.C.len; omega_using [this]) (by show 8 * P.R.E.C.len < _; omega_using [this])

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

/-! ## `bits2octets` and `bits2int` of the digest -/

/-- For a curve whose `nBits` is `8 Q` and whose order is above `2^(8 Q - 1)`:
`bits2octets` of a digest is its `X` modulo `n`, and `bits2int` is `X`. -/
theorem xOfDg_spec {C : Spec.Weierstrass.Curve} {Q : Nat} (hB : Spec.Ecdsa.nBits C = 8 * Q)
    (hn : C.n ≠ 0) {dg : List Byte} :
    Spec.Ecdsa.Rfc6979.bits2octets C dg =
        Spec.Weierstrass.toBytes Q (Spec.Weierstrass.ofBytes (xOfDg Q dg) % C.n) ∧
      Spec.Ecdsa.hashToInt C dg = Spec.Weierstrass.ofBytes (xOfDg Q dg) := by
  unfold xOfDg
  by_cases h : Q ≤ dg.length
  · rw [Nat.min_eq_right h, Nat.sub_self, List.replicate_zero, List.nil_append]
    exact ⟨bits2octets_eqQ hB h, hashToInt_takeQ hB h⟩
  · have hl : 8 * dg.length < Spec.Ecdsa.nBits C := by omega
    obtain ⟨e₁, e₂⟩ := hashToInt_short hl hn
    rw [Nat.min_eq_left (by omega), List.take_of_length_le (by omega), ofBytes_zeros]
    refine ⟨?_, e₁⟩
    rw [bits2octets_short (R := Q) (by omega) (by omega) hl hn, Nat.mod_eq_of_lt e₂,
      show Q = (Q - dg.length) + dg.length by omega, toBytes_pad _ _ _ (ofBytes_lt dg), toBytes_ofBytes]
    congr 2; omega

/-- `hashToInt` of a `Q`-byte `X`, for a curve whose `nBits` is `8 Q`, is its number. -/
theorem hashToInt_q {C : Spec.Weierstrass.Curve} {Q : Nat} (hB : Spec.Ecdsa.nBits C = 8 * Q) {x : List Byte}
    (hx : x.length = Q) : Spec.Ecdsa.hashToInt C x = Spec.Weierstrass.ofBytes x := by
  rw [hashToInt_takeQ hB (by omega), List.take_of_length_le (by omega)]

/-- `h`, `core`'s digest, and that nothing else changed but the frame's
working places and `scratch`. -/
structure Prepped (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  dg : DgOk P L m₀ u.mem

theorem prep_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = L.dg)
    (hdi : t.gpr .rdi = L.scr) :
    WP isa (cfgOf P).prep t fun u => Ctx L g m₀ u ∧ Prepped P L m₀ u := by
  have hq := hk.2.1
  have hdn : P.H.D ≤ P.I.hashLen := Nat.le_refl _
  have he := L.he
  have hfY : fY = 216 := rfl
  have hdg : Spec.Sha256.bytesAt t.mem L.dg P.H.D = hBOf P L m₀ := hc.dgBytes hL hdn
  have hlen : (hBOf P L m₀).length = P.H.D := length_bytesAt _ _ _
  refine WP.seq (WP.mono (prepZero_ok hL hq hc) fun u₁ ⟨hc₁, hg₁, hax, hf₁, hz₁⟩ => ?_)
  have hsi₁ : u₁.gpr .rsi = L.dg := (hg₁ _ (by decide) (by decide)).trans hsi
  have hdi₁ : u₁.gpr .rdi = L.scr := (hg₁ _ (by decide) (by decide)).trans hdi
  have hdg₁ : Spec.Sha256.bytesAt u₁.mem L.dg P.H.D = hBOf P L m₀ := (hc₁.dgBytes hL hdn)
  refine WP.seq (dispatch_ok P (f := fun H => .block ((cfgOf P).prepCase H.D)) hax fun u₂ hfl => ?_)
  have hc₂ := hc₁.flags hL hfl
  have hm₂ : u₂.mem = u₁.mem := hfl.mem
  have hsi₂ : u₂.gpr .rsi = L.dg := (hfl.gpr _).trans hsi₁
  have hdi₂ : u₂.gpr .rdi = L.scr := (hfl.gpr _).trans hdi₁
  have hdg₂ : Spec.Sha256.bytesAt u₂.mem L.dg P.H.D = hBOf P L m₀ := (hc₂.dgBytes hL hdn)
  cases hw : P.R.wide
  · -- `X` in `Y`, `h` its residue.
    have hz : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) 72 = List.replicate 72 0 := by
      rw [hm₂]; simpa [nz, hw] using hz₁
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := (P.R.sizesA hw).2.2.1
    have hw8 := (P.sizesA hw).2.1
    obtain ⟨e₁, e₂⟩ := xOfDg_spec hB P.R.n_ne (dg := hBOf P L m₀)
    refine WP.mono (prepCaseA_ok hL hw hc₂ hdn hsi₂ hz) fun u₃ ⟨hc₃, hf₃, hb₃⟩ => ?_
    rw [hdg₂] at hb₃
    have e : (cfgOf P).prepPost = Cfg.fr .rsi fY ++ (cfgOf P).reduce := by
      simp only [Cfg.prepPost, cfgOf, hw, Bool.false_eq_true, ite_false]
    rw [e, WP.block_append_iff]
    refine WP.mono (fr_ok hL hc₃ (d := .rsi) (by decide) (o := fY) (by decide)) fun u₄ h₄ => ?_
    refine WP.mono (reduce_ok hw hL h₄.ctx (by rw [h₄.val]; rfl)) fun u ⟨hcu, hfu, hhu⟩ => ⟨hcu, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 312) P.Q = _
      rw [hhu, h₄.mem, hb₃, hSpec, e₁]
    · have hY : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 240) P.Q = xOfDg P.Q (hBOf P L m₀) := by
        obtain ⟨-, hb₂, -, -, hQw, -⟩ := hb_facts (P := P) hw
        rw [← hb₃, ← h₄.mem]
        refine bytesAt_frame hfu (fun r hr => ?_) (by nums)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega) (by nums) (by omega)
        · exact Offset.disjoint _ (by omega) (by nums) (by omega)
      unfold DgOk
      rw [hY, hashToInt_q hB (by simp [xOfDg, hlen]; omega), eOf, e₂]
  · -- The digest shifted in `Y`, and after zero bytes in `h`.
    obtain ⟨hw9, hQ66⟩ := P.sizesW hw
    have hsh : P.R.sh = 7 := sh7 hw
    have hl := P.R.nBits_len
    have hN := (P.R.sizesW hw).2.2
    have hz : Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 240) 144 = List.replicate 144 0 := by
      rw [hm₂]; simpa [nz, hw] using hz₁
    refine WP.mono (prepCaseW_ok hL hw hc₂ hdn hsi₂ hz) fun u₃ ⟨hc₃, hf₃, hg₃, hY₃, hh₃⟩ => ?_
    rw [hdg₂] at hY₃ hh₃
    have e : (cfgOf P).prepPost = (cfgOf P).conv fY 1 := by
      simp only [Cfg.prepPost, cfgOf, hw, ite_true, hsh]
    rw [e]
    refine WP.mono (conv_ok hL hw hc₃ ((hg₃ _ (by decide)).trans hdi₂) (o := fY) (s := 1) (by decide) (by decide)
      (by decide) (by decide)) fun u ⟨hcu, _, hfu, hbu⟩ => ⟨hcu, ?_, ?_⟩
    · show hPart P.Q L u.mem = _
      have hk : hPart P.Q L u.mem = hPart P.Q L u₃.mem := bytesAt_frame hfu (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by omega) (by omega)
        · exact Offset.disjoint _ (by simp only [fY]; omega) (by omega) (by omega)) (by omega)
      rw [hk, hPart, hh₃, hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega)
        (by show 8 * P.R.E.C.len < _; omega) (by rw [hlen]; nums) P.R.n_ne, hlen]
    · unfold DgOk
      simp only [dgArg]
      have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (hBOf P L m₀) :=
        (hashToInt_short (by rw [hlen]; nums) P.R.n_ne).1
      have hX : Spec.Weierstrass.ofBytes (List.replicate (P.Q - P.H.D - 1) 0 ++ hBOf P L m₀ ++ [0]) =
          Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ 8 := by
        rw [List.append_assoc, ofBytes_zeros, show ([0] : List Byte) = List.replicate 1 0 from rfl,
          ofBytes_append_zeros]
      have hlt : Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ 7 < 2 ^ (8 * P.Q) := by
        have := ofBytes_lt (hBOf P L m₀)
        rw [hlen] at this
        calc _ < 2 ^ (8 * P.H.D) * 2 ^ 7 := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega) (by nums)
      have hlY : (Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ 7)).length = P.Q := by
        simp [Spec.Weierstrass.toBytes]
      rw [show L.B + BitVec.ofNat 64 240 = L.B + BitVec.ofNat 64 (24 + fY) from rfl, hbu,
        show L.B + BitVec.ofNat 64 (24 + fY) = L.B + BitVec.ofNat 64 240 from rfl, hY₃, hX,
        show (Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ 8) >>> 1 = Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ 7 by
          rw [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 8 = 2 ^ 7 * 2 ^ 1 from rfl, ← Nat.mul_assoc,
            Nat.mul_div_cancel _ (Nat.two_pow_pos _)],
        hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega) (by rw [hlY]),
        List.take_of_length_le (by rw [hlY]), ofBytes_toBytes _ _ hlt,
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = 7 by show 8 * P.R.E.C.len - _ = 7; omega,
        Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos _), e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_kvw (hL : L.Ok) {m m' : Mem} (hf : Frame (KVW L) m m') : hOf P L m' = hOf P L m := by
  have he := L.he
  refine bytesAt_frame hf (fun r hr => ?_) (by nums)
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hL.stk_SCR (by nums)
  · exact Offset.disjoint_base _ (by omega) (by nums)

/-- After `h` and `core`'s digest: `V = 0x01…` and `K = 0x00…` (step c). -/
theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hp : Prepped P L m₀ u) :
    WP isa (.block Cfg.initKV) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  have he := L.he
  refine WP.mono (initKV_ok hL hc) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ => ⟨hc₂, ?_, hk₂ _ (by nums), hv₂ _ (by nums), ?_⟩
  · exact (bytesAt_frame hf₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by nums) (by omega)) (by nums)).trans hp.h
  · exact hp.dg.frame hf₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by nums) (by omega)

theorem stageC_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc 0) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨(hOf_kvw hL hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart⟩ |>
    fun h => ⟨hc', h⟩

theorem stageD_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL (hok_of hk) hc 1) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart⟩

theorem stageE_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', P.tries_pos,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _), hq.dg.frameOf hL hf' (by simp [DgApart])⟩

theorem stageG_ok (hL : L.Ok) (hk : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block Cfg.wipe) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' :=
  WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, ha₇, hf₇⟩ => ⟨hc₇, hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      have := L.he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega_using [this])).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (by omega_using [this])).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by nums))⟩

theorem body_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).body t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' :=
  WP.seq (WP.mono (digestPtr_ok hL hc) fun _ ⟨h₀, _, hsi, hdi⟩ =>
    WP.seq (WP.mono (prep_ok hL hk h₀ hsi hdi) fun _ ⟨h₀', p₀⟩ =>
    WP.seq (WP.mono (stageB_ok hL h₀' p₀) fun _ ⟨h₁, q₁⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
          WP.seq (WP.mono (stageE_ok hL h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
            WP.seq (WP.mono (loop_ok hL hk h₄ q₄) fun _ ⟨h₅, i, q₅⟩ =>
              WP.mono (stageG_ok hL hk h₅ q₅) fun _ ⟨h₆, q₆⟩ => ⟨h₆, i, q₆⟩)))))))

/-! ## RFC 6979's result -/

/-- A candidate is RFC 6979's `blocks` `V`s. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = P.nb := rfl

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.SH.H P.H.D (xOf P L m₀) (eOf P L m₀) K V P.I.tries
      else (none, 0) := by
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve, P.len,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by have := hx.lt; omega_using [this]) hx.fails,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by have := hx.lt; omega_using [this]]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
    | none =>
      have h7 : i + 1 = P.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs, show P.I.tries - 1 - i = 0 by omega_using [h7]]
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
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by omega_using [hi]) hf,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by omega_using [hi]]
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
        rw [show P.I.tries - 1 - i = P.I.tries - 2 - i + 1 by omega_using [h7]]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega
      · rw [show P.I.tries - 1 - i = 0 by omega_using [h7]]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega_using []) (by omega_using [])
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega_using []

/-! ## The whole function -/

theorem pop_rsp (B : Addr) :
    B + BitVec.ofNat 64 24 + BitVec.ofNat 64 (8 * 65) = B + BitVec.ofNat 64 (240 + 8 * 38) := by
  rw [Offset.add_add]

theorem coreOk_lay (P : RfcHash) (s : State) :
    CoreOk P (lay P.I.hashLen P.I.ecdsa.curve.len P.k P.H.D P.H.P.B P.R.E.combConsts s) :=
  ⟨P.curveLen, ⟨rfl, rfl, rfl⟩, rfl⟩

/-- `scratch` in `rcx`, and the hash function's number, output length and
block size in `rax`, `r10` and `r11` (by a dispatch on `hash`), then `c`. -/
theorem entry_ok {s : State} (h : (rfcX86_64 P.R.E.combConsts P.I P.k 544).pre s) {c : Prog isa}
    {Q : State → Prop} (hk : ∀ s', Entered s P.k P.H.D P.H.P.B s' → WP isa c s' Q) :
    WP isa (.seq (.block Cfg.entry)
      (.seq (Impl.Dispatch.X86_64.chain ((cfgOf P).hs.map fun p => (p.1, .block (Cfg.sizes p.2.D p.2.P.B)))) c))
      s Q := by
  have hk32 : P.k < 2 ^ 32 := by
    have := P.hk; simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons, List.not_mem_nil, or_false] at this; omega
  have hr9 : (s.gpr .r9).setWidth 32 = BitVec.ofNat 32 P.k := h.1
  have h₁ : WP isa (.block Cfg.entry) s fun (s₁ : State) => s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mem = s.mem ∧
      s₁.syms = s.syms ∧ s₁.gpr .rax = BitVec.ofNat 64 P.k ∧ s₁.gpr .rcx = s.gpr .r8 ∧
      ∀ r, r ≠ .rax → r ≠ .rcx → s₁.gpr r = s.gpr r := by
    apply WP.of_runBlock
    simp only [Cfg.entry, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, State.setReg32,
      Option.map_some, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
      reduceCtorEq, ite_true, ite_false, hr9, zx32 hk32, Option.some.injEq, exists_eq_left']
    refine ⟨by triv, by triv, by triv, by triv, trivial, trivial, fun r h₁ h₂ => ?_⟩
    simp only [h₁, h₂, ite_false]
  refine WP.seq (WP.mono h₁ fun (s₁ : State) ⟨hrd, hwr, hm, hsy, hax, hcx, hg⟩ => WP.seq
    (dispatch_ok P (f := fun H => .block (Cfg.sizes H.D H.P.B)) hax fun s₂ hf => ?_))
  have hD : P.H.D < 2 ^ 32 := by nums
  have hB : P.H.P.B < 2 ^ 32 := by nums
  refine WP.mono (Q := Entered s P.k P.H.D P.H.P.B) ?_ hk
  apply WP.of_runBlock
  simp only [Cfg.sizes, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    Option.map_some, zx32 hD, zx32 hB, Option.some.injEq, exists_eq_left']
  have g : ∀ r, r ≠ .r10 → r ≠ .r11 → ((s₂.setReg .r10 (BitVec.ofNat 64 P.H.D)).setReg .r11
      (BitVec.ofNat 64 P.H.P.B)).gpr r = s₂.gpr r := fun r h₁ h₂ => by
    rw [RegUpd.gpr_setReg_of_ne _ _ h₂, RegUpd.gpr_setReg_of_ne _ _ h₁]
  have g' : ∀ r, r ≠ .r10 → r ≠ .r11 → r ≠ .rax → r ≠ .rcx → ((s₂.setReg .r10 (BitVec.ofNat 64 P.H.D)).setReg .r11
      (BitVec.ofNat 64 P.H.P.B)).gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g r h₁ h₂, hf.gpr, hg r h₃ h₄]
  exact ⟨by rw [RegUpd.rd_setReg, RegUpd.rd_setReg, hf.rd, hrd], by rw [RegUpd.wr_setReg, RegUpd.wr_setReg, hf.wr, hwr],
    by rw [RegUpd.mem_setReg, RegUpd.mem_setReg, hf.mem, hm],
    by obtain ⟨_, _, _, _, rfl⟩ := hf; exact hsy,
    g' _ (by decide) (by decide) (by decide) (by decide),
    fun r hr => g' r (ne_cs hr (by decide)) (ne_cs hr (by decide)) (ne_cs hr (by decide)) (ne_cs hr (by decide)),
    g' _ (by decide) (by decide) (by decide) (by decide), g' _ (by decide) (by decide) (by decide) (by decide),
    g' _ (by decide) (by decide) (by decide) (by decide),
    by rw [g _ (by decide) (by decide), hf.gpr, hcx], by rw [g _ (by decide) (by decide), hf.gpr, hax],
    by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_self], RegUpd.gpr_setReg_self _ _ _⟩

/-- `vg_ecdsa_<curve>_rfc6979_sign` with `P`'s hash function meets
`rfcX86_64 P.I P.k` and keeps the callee-saved registers and its return
address. -/
theorem sign_ok {s : State} (h : (rfcX86_64 P.R.E.combConsts P.I P.k 544).pre s) :
    WP isa (cfgOf P).sign s fun s' =>
      gprPreserved s s' ∧ (rfcX86_64 P.R.E.combConsts P.I P.k 544).post s s' := by
  have hL := lay_ok (I := P.I) P.k P.H.D P.H.P.B h
  rw [Cfg.sign]
  refine entry_ok h fun s' he => ?_
  have hc := push_ctx h he
  refine WP.frame (rs := pushRs) (by decide) (by decide) (by decide)
    (by rw [pushRs_length, he.rsp]; have := h.2.1; omega_using [this])
    (WP.mono (body_ok hL (coreOk_lay P s) hc) fun u ⟨hu, i, hx⟩ =>
      ⟨hu.rsp.trans hc.rsp.symm, hu.wr.trans hc.wr.symm, ?_, ?_⟩)
  · have hrsp : (popped .rcx pushRs.length u).gpr .rsp = s.gpr .rsp := by
      rw [popped_rsp, hu.rsp, pushRs_length, pop_rsp, lay_ret]
    refine ⟨fun r hr => ?_, ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'; exact hrsp
      · rw [popped_gpr _ _ _ hr' (ne_cs hr (by decide)), hu.cs r hr hr']
    · rw [popped_mem]
      refine hu.frame.readW (r := (lay P.I.hashLen P.I.ecdsa.curve.len P.k P.H.D P.H.P.B P.R.E.combConsts s).RET)
        ?_ ?_ (by decide)
      · show (⟨_ + BitVec.ofNat 64 (240 + 8 * 38), 8⟩ : Region).Contains (s.gpr .rsp) 8
        rw [lay_ret]; exact Region.contains_self _ _
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hL.ro
        · exact hL.rc
        · exact Offset.disjoint_base (d := 240 + 8 * 38) (n := 8) (k := 240 + 8 * 38) _ (by omega_using [])
            (by omega_using [])
  · show match (result P.I s.mem (lay P.I.hashLen P.I.ecdsa.curve.len P.k P.H.D P.H.P.B P.R.E.combConsts s).d
        (lay P.I.hashLen P.I.ecdsa.curve.len P.k P.H.D P.H.P.B P.R.E.combConsts s).dg).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
    have e₂ : P.I.ecdsa.curve = P.R.E.C := by show P.I0.ecdsa.curve = _; rw [P.ecdsa, P.R.curve]
    rw [e₁, e₂]
    exact hx.res.keep (popped_gpr _ _ _ (by decide) (by decide)) (by rw [popped_mem])

end VG.Proof.Ecdsa.Rfc6979.X86_64
