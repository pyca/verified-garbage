import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Loop

/-!
# Deterministic ECDSA on x86 (32-bit): correctness

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Correct.lean`): the loop leaves it
at a candidate that is suitable or the last (`loop_ok`); before it, `h`, `K`,
`V` and the count are as RFC 6979's steps a–g make them; and the signature of
that candidate is RFC 6979's (`result_eq`), for the hash function `P`'s
instance of the contract. The frame's allocation, our caller's registers
saved and restored, and the return address kept give the whole function
(`sign_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Ecdsa.Rfc6979 (kvAt candAt step)

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem}

/-- HMAC's output is the hash function's. -/
theorem mac_length (P : RfcHash) (K t : List Byte) : (P.mac K t).length = P.F.H.D := by
  simp only [RfcHash.mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.macLen]

/-! ## The loop -/

theorem loop_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne .ne) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (8 - n) s ∧ n ≤ 8) ?_ 8 t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega
  refine WP.mono (tryOne_ok hL hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega, hc', ?_, by omega⟩
    rwa [show 8 - (n - 1) = 8 - n + 1 by omega]

/-! ## Steps a–g -/

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : RfcHash) {x : Nat} {dB hB h : List Byte} (hd : dB.length = 32)
    (hx : x = Spec.Weierstrass.ofBytes dB) (hh : Spec.Ecdsa.Rfc6979.bits2octets Spec.P256.curve hB = h) :
    Spec.Ecdsa.Rfc6979.init Spec.P256.curve P.ok.hH.SH.H P.F.H.D x hB =
      let K₁ := P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.F.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets Spec.P256.curve x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_p256, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets Spec.P256.curve (hBOf P L m₀)
abbrev dB {dn : Nat} (L : Lay dn) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d 32

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.F.H.D 0) (List.replicate P.F.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.F.H.D 1)

/-- After step c: `h`, `V = 0x01…` and `K = 0x00…`. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.F.H.D 0
  v : vOf P L u.mem = List.replicate P.F.H.D 1

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  h : hOf L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hsi : u.gpr .esi = L.a2) :
    WP isa (.block ((cfgOf P).reduce ++ Cfg.initKV)) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  have hD : 32 ≤ P.F.H.D := by nums
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok (P := P) hL hc hsi P.len32) fun u₁ ⟨hc₁, _, hh₁⟩ => ?_
  refine WP.mono (initKV_ok hL hc₁) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
    ⟨hc₂, ?_, hk₂ _ (by nums), hv₂ _ (by nums)⟩
  rw [show hOf L u₂.mem = hOf L u₁.mem from bytesAt_frame hf₂ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)]
  rw [hSpec, bits2octets_eq (by rw [hBOf, length_bytesAt]; exact hD), hBOf, ← bytesAt_take m₀ L.dg hD, ← hh₁]
  have e := toBytes_ofBytes (hOf L u₁.mem)
  rw [length_bytesAt] at e
  exact e.symm

theorem kvw_h (hL : L.Ok) : ∀ r ∈ KVW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 204, 32⟩ r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hL.stk_SCR (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)

theorem stageC_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hc 0) fun u' ⟨hc', hf', hk', hv'⟩ =>
    ⟨hc', (bytesAt_frame hf' (kvw_h hL) (by omega)).trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL]⟩

theorem stageD_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hc 1) fun u' ⟨hc', _, hk', hv'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL]⟩

theorem stageE_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', by omega,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums))
      (by nums)).trans hq.v,
    by rw [hn'], fun j hj => absurd hj (Nat.not_lt_zero _)⟩

theorem stageG_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {i : Nat} (hx : Exit P L m₀ i u) :
    WP isa (.block Cfg.wipe) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' ∧ ∀ p ∈ saved, u'.gpr p.1 = g p.1 :=
  WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, ha₇, hf₇, hs₇⟩ => ⟨hc₇, ⟨hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_OUT (by omega)).symm) (by omega))⟩, hs₇⟩

/-- The body, after `esi` is set to `digest`. -/
theorem rest_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .esi = L.a2) :
    WP isa (.seq (.block ((cfgOf P).reduce ++ Cfg.initKV)) (.seq ((cfgOf P).rekeyFull 0)
      (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne .ne) (.block Cfg.wipe)))))) t
      fun t' => Ctx L g m₀ t' ∧ (∃ i, Exit P L m₀ i t') ∧ ∀ p ∈ saved, t'.gpr p.1 = g p.1 :=
  WP.seq (WP.mono (stageB_ok hL hc hsi) fun _ ⟨h₁, q₁⟩ =>
    WP.seq (WP.mono (stageC_ok hL h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
      WP.seq (WP.mono (stageD_ok hL h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
        WP.seq (WP.mono (stageE_ok hL h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
          WP.seq (WP.mono (loop_ok hL h₄ q₄) fun _ ⟨h₅, i, q₅⟩ =>
            WP.mono (stageG_ok hL h₅ q₅) fun _ ⟨h₆, q₆, s₆⟩ => ⟨h₆, ⟨i, q₆⟩, s₆⟩)))))

/-! ## RFC 6979's result -/

/-- One `V` makes a candidate. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks Spec.P256.curve P.F.H.D = 1 := by
  have hD : 32 ≤ P.F.H.D := by nums
  rw [Spec.Ecdsa.Rfc6979.blocks, nBits_p256]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

theorem bits2int_cand (i : Nat) :
    Spec.Ecdsa.Rfc6979.bits2int Spec.P256.curve (candI P L m₀ i ++ []) =
      Spec.Weierstrass.ofBytes ((candI P L m₀ i).take 32) := by
  have hl : (candI P L m₀ i).length = P.F.H.D := mac_length P _ _
  rw [List.append_nil, Spec.Ecdsa.Rfc6979.bits2int, hashToInt_take (by rw [hl]; nums)]

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf L m₀ ∧ xOf L m₀ < Spec.P256.curve.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search Spec.P256.curve P.ok.hH.SH.H P.F.H.D (xOf L m₀) (eOf P L m₀) K V 8
      else (none, 0) := by
  have hlen : Spec.P256.curve.len = 32 := rfl
  simp only [result, Spec.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.hash, P.tries, P.len, Spec.Ecdsa.P256.inst,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign, hlen]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf L m₀ ∧ xOf L m₀ < Spec.P256.curve.n
  · simp only [hv, and_self, ite_true]
    have hf : ∀ j < i, Spec.Ecdsa.signWith Spec.P256.curve (xOf L m₀) (eOf P L m₀)
        (Spec.Ecdsa.Rfc6979.bits2int Spec.P256.curve (candI P L m₀ j ++ [])) = none := fun j hj => by
      rw [bits2int_cand]; exact hx.fails j hj
    rw [Proof.Ecdsa.Rfc6979.search_shift (blocks_eq P) i 8 (by have := hx.lt; omega) hf,
      show 8 - i = (7 - i) + 1 by have := hx.lt; omega]
    have hc : Spec.Hmac.hmac P.ok.hH.SH.H (kvI P L m₀ i).1 (kvI P L m₀ i).2 = candI P L m₀ i := rfl
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
def exitAt (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  if (result P.I m₀ L.d L.dg).2 = 0 then 7 else (result P.I m₀ L.d L.dg).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {i : Nat} (hi : i < 8) (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < 8) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf L m₀ ∧ xOf L m₀ < Spec.P256.curve.n
  · simp only [hv, and_self, ite_true]
    have hf' : ∀ j < i, Spec.Ecdsa.signWith Spec.P256.curve (xOf L m₀) (eOf P L m₀)
        (Spec.Ecdsa.Rfc6979.bits2int Spec.P256.curve (candI P L m₀ j ++ [])) = none := fun j hj => by
      rw [bits2int_cand]; exact hf j hj
    rw [Proof.Ecdsa.Rfc6979.search_shift (blocks_eq P) i 8 (by omega) hf', show 8 - i = (7 - i) + 1 by omega]
    have hc : Spec.Hmac.hmac P.ok.hH.SH.H (kvI P L m₀ i).1 (kvI P L m₀ i).2 = candI P L m₀ i := rfl
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.search_ok (blocks_eq P) (by rw [hc, bits2int_cand]; exact hs)]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.search_fail (blocks_eq P) (by rw [hc, bits2int_cand]; exact hs)]
      by_cases h7 : i + 1 < 8
      · have := Proof.Ecdsa.Rfc6979.search_pos (C := Spec.P256.curve) (H := P.ok.hH.SH.H) (hlen := P.F.H.D)
          (d := xOf L m₀) (e := eOf P L m₀) (n := 6 - i)
          (K := (step P.ok.hH.SH.H (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (step P.ok.hH.SH.H (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
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

theorem cfgOf_F : (cfgOf P).F = P.F := rfl
theorem coreC_eq : (cfgOf P).coreC = Impl.Ecdsa.X86.signP256 := rfl

theorem allInstrs_of_noSp {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi; simp [h i hi]

theorem subWord_nosp (c : Cfg) (j : Nat) : (c.subWord j).all (fun i => !Taint.clobbers i .esp) = true := by
  cases j <;> rfl

/-- `h = bits2octets(digest)`, `K` and `V`: no instruction writes `esp`,
whatever the code's `n`. -/
theorem reduceKV_nosp (c : Cfg) :
    (Code.block (c.reduce ++ Cfg.initKV) : Prog isa).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq]
  simp only [instrs, Cfg.reduce, List.all_append, List.all_flatMap, subWord_nosp]
  decide

theorem tries_eq : (cfgOf P).tries = 8 := rfl

/-- No instruction of the body writes `esp`: not those of the functions it
calls, by what `P` and the proofs of HMAC's functions know of them, nor its
own, which the kernel evaluates for each size of hash function. -/
theorem body_nosp (P : RfcHash) : NoSp (cfgOf P).body := by
  have hI := allInstrs_of_noSp P.ok.hiSp
  have hU := allInstrs_of_noSp P.ok.hH.updSp
  have hF := allInstrs_of_noSp P.ok.hfSp
  have hK := allInstrs_of_noSp core_nosp
  have hR := reduceKV_nosp (cfgOf P)
  refine NoSp.of_all ?_
  simp only [Cfg.body, Cfg.tryOne, Cfg.rekeyFull, Cfg.rekey, Cfg.hmacV, Cfg.hmac, Code.allInstrs.eq_2,
    Code.allInstrs.eq_3, Code.allInstrs.eq_4, Code.allInstrs.eq_5, Code.allInstrs.eq_6,
    cfgOf_F, coreC_eq, hI, hU, hF, hK, hR, Cfg.initCnt, tries_eq, Bool.and_true, Bool.true_and]
  rcases P.hDB with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp only [h, h'] <;> decide +kernel

theorem released_gpr {s₂ : State} {r : Reg} (hr : r ≠ .esp) : (released s₂).gpr r = s₂.gpr r :=
  (Wp.Upd.setReg s₂ .esp _).other r hr

theorem released_esp (s₂ : State) :
    (released s₂).gpr .esp = s₂.gpr .esp + BitVec.ofNat 32 Impl.Ecdsa.Rfc6979.X86.frameBytes :=
  (Wp.Upd.setReg s₂ .esp _).gpr

/-- `vg_ecdsa_p256_<hash>_sign` meets `rfcX86 P.I` and keeps the
callee-saved registers and its return address. -/
theorem sign_ok {s : State} (h : (rfcX86 P.I).pre s) :
    WP isa (cfgOf P).sign s fun s' => abiPreserved s s' ∧ (rfcX86 P.I).post s s' := by
  have hL := lay_ok h
  have nB := hL.nB
  refine WP.alloc (by show 180 ≤ _; have := h.1; omega) (body_nosp P) (WP.seq ?_)
  refine save_ok h fun t hc _ => WP.mono (arg_ok hL hc (d := .esi) (by decide) (i := 2) (by omega)) fun u hu => ?_
  refine WP.mono (rest_ok hL hu.ctx hu.val) fun u' ⟨hc', ⟨i, hx⟩, hs'⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [released_gpr (by decide)]; exact hs' (.ebx, 164) (by decide)
    · rw [released_gpr (by decide)]; exact hs' (.esi, 168) (by decide)
    · rw [released_gpr (by decide)]; exact hs' (.edi, 172) (by decide)
    · rw [released_gpr (by decide)]; exact hs' (.ebp, 176) (by decide)
    · rw [released_esp, hc'.esp]; exact BitVec.sub_add_cancel _ _
  · have hret : (s.gpr .esp).setWidth 64 = (lay P.I.hashLen s).B + BitVec.ofNat 64 256 := by
      rw [hL.B_eq, BitVec.sub_add_cancel]; rfl
    show u'.mem.readW _ 32 = _
    rw [hret]
    refine hc'.frame.readW (r := (lay P.I.hashLen s).RET) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.ro
    · exact hL.rc
    · exact Offset.disjoint_base _ (by omega) (by omega)
  · show match (result P.I s.mem (lay P.I.hashLen s).d (lay P.I.hashLen s).dg).1 with
      | some rs => _ | none => _
    rw [result_eq hx]
    have hr := hx.res
    have ha : (released u').gpr .eax = u'.gpr .eax := released_gpr (by decide)
    revert hr
    cases sigI P (lay P.I.hashLen s) s.mem i with
    | some rs => exact fun ⟨h₁, h₂⟩ => ⟨by rw [BitVec.setWidth_append_eq_right, ha]; exact h₁, h₂⟩
    | none => exact fun ⟨h₁, h₂⟩ => ⟨by rw [BitVec.setWidth_append_eq_right, ha]; exact h₁, h₂⟩

end VG.Proof.Ecdsa.Rfc6979.X86
