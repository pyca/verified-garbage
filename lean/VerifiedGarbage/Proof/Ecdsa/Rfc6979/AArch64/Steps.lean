import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg

/-!
# Deterministic ECDSA on AArch64: the steps on `K` and `V`

`V = HMAC_K(V)` (`hmacV_ok`); `K = HMAC_K(V ‖ b ‖ d ‖ h)` (or, if two `V`s
make a candidate, `‖ d ‖ 0 0 ‖ digest`), then `V = HMAC_K(V)`
(`rekeyFull_ok`, steps d–g); and `K = HMAC_K(V ‖ 0x00)`,
then `V = HMAC_K(V)` (`rekey_ok`, step h.3). Each changes only `scratch`,
the stack below the frame, and `K` and `V`.
-/

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `K` and `V` (of the hash function's output length) and `h`, in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte := keyOf P L m
abbrev vOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 80) P.H.D
abbrev hOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 144) P.Q

/-- What follows `V ‖ b` in the message of steps d and f: `d ‖ h`, or, if
`wide`, `d ‖ 0 0 ‖ digest`. -/
abbrev tailOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (wide : Bool) (m : Mem) :
    List Byte :=
  if wide then Spec.Sha256.bytesAt m L.d P.Q ++ List.replicate (P.Q - P.H.D) 0 ++ Spec.Sha256.bytesAt m L.dg P.H.D
  else Spec.Sha256.bytesAt m L.d P.Q ++ hOf P L m

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : List Region := [L.SCR, ⟨L.B, 144⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 144⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 144⟩, by simp, h⟩

theorem done_kvw {dst : Nat} (h : dst + P.H.D ≤ 128) :
    ∀ r ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 16⟩, ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩],
      ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega))
    · exact .inr (Region.sub_prefix (by omega))
    · exact .inr (Offset.sub_base _ (by omega))

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacV t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) := by
  refine WP.mono (hmac_ok (P := P) hL hc (da := L.B + BitVec.ofNat 64 (16 + 64)) (len := P.H.D) (dst := 64)
    (fun u hu => fr_ok hL hu (d := .x2) (by decide) (o := 64) (by decide))
    (.inl ⟨80, rfl, by omega, by anums⟩) (by anums) (by anums)) fun t' h =>
    ⟨h.ctx, h.frame.sub (done_kvw (by anums)), bytesAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.stk_scr0 (by anums) (by omega)
      · exact Offset.disjoint_base _ (by omega) (by anums)
      · exact Offset.disjoint _ (by anums) (by anums) (by anums)) (by anums), h.mac⟩

/-- `K = HMAC_K(m)`, for the message `m` of `len` bytes at `scratch + 2256`. -/
theorem hmacK_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256) :
    WP isa ((cfgOf P).hmac (Cfg.scr .x2 sMsg) len fK) t fun t' => Ctx L g m₀ t' ∧
      Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  refine WP.mono (hmac_ok (P := P) hL hc (da := L.scr + BitVec.ofNat 64 2256) (len := len) (dst := 0)
    (fun u hu => scr_ok hL hu (d := .x2) (by decide) (a := 2256) (by decide))
    (.inr ⟨2256, rfl, by omega, by omega⟩) hlen (by anums)) fun t' h =>
    ⟨h.ctx, h.frame.sub (done_kvw (by anums)), bytesAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.stk_scr0 (by anums) (by omega)
      · exact Offset.disjoint_base _ (by omega) (by anums)
      · exact Offset.disjoint _ (by anums) (by anums) (by anums)) (by anums), h.mac⟩

/-- The message of a step, `V ‖ b (‖ d ‖ h)`, or, if `wide`, `V ‖ b ‖ d ‖ 0 0 ‖
digest`: its frame and its bytes. -/
theorem msgAny_ok (hL : L.Ok) (hq : L.q = P.Q) (hdn : dn = P.H.D) {t : State} (hc : Ctx L g m₀ t)
    (h9 : t.gpr .x9 = L.scr) (h10 : t.gpr .x10 = L.d) (h15 : t.gpr .x15 = L.B + BitVec.ofNat 64 16)
    (b : Nat) (full wide : Bool) (h8 : wide = true → t.gpr .x8 = L.dg)
    (hW : wide = true → full = true ∧ P.R.wide = true) (hA : full = true → wide = false → P.R.wide = false) :
    WP isa (.block (Cfg.msg P.w P.Q P.H.D b full wide)) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, 224⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256)
          (if full then P.H.D + 2 * P.Q + 1 else P.H.D + 1) =
        vOf P L t.mem ++ [BitVec.ofNat 8 b] ++ (if full then tailOf P L wide t.mem else []) := by
  cases wide
  · refine WP.mono (msg_ok hL hc h9 h10 h15 b full (D := P.H.D) (w := P.w) (Q := P.Q) (by anums) (by anums)
      fun hf => ?_) fun t' ⟨hc', hf', hb'⟩ => ⟨hc', hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, ?_⟩
    · have := P.sizesA (hA hf rfl)
      exact ⟨by anums, by omega, by omega⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by anums)
    · cases full
      · simpa using hb'
      · simp only [ite_true, tailOf, hOf, Bool.false_eq_true, ite_false] at hb' ⊢
        exact hb'
  · obtain ⟨hfull, hRW⟩ := hW rfl
    subst hfull
    obtain ⟨hw9, hQ66, hD64, -⟩ := P.sizesW hRW
    have hq' : 66 ≤ L.q := by omega
    have hdn' : 64 ≤ dn := by omega
    rw [hQ66, hD64]
    refine WP.mono (msgW_ok hL hc h9 h10 h15 (h8 rfl) b (w := P.w) hq' hdn') fun t' ⟨hc', hf', hb'⟩ =>
      ⟨hc', hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
    · simp only [ite_true]
      rw [hb']
      show _ = Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 80) P.H.D ++ _ ++
        (Spec.Sha256.bytesAt t.mem L.d P.Q ++ List.replicate (P.Q - P.H.D) 0 ++
          Spec.Sha256.bytesAt t.mem L.dg P.H.D)
      rw [hQ66, hD64]

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ tail)`. -/
theorem rekey_gen (hL : L.Ok) (hq : L.q = P.Q) (hdn : dn = P.H.D) {t : State} (hc : Ctx L g m₀ t) {b : Nat}
    {full wide : Bool} (hW : wide = true → full = true ∧ P.R.wide = true)
    (hA : full = true → wide = false → P.R.wide = false)
    {len : Nat} (hlen : len = if full then P.H.D + 2 * P.Q + 1 else P.H.D + 1) :
    WP isa (.seq (.block (Cfg.msgPtrs wide)) (.seq (.block (Cfg.msg P.w P.Q P.H.D b full wide))
      (.seq ((cfgOf P).hmac (Cfg.scr .x2 sMsg) len fK) (cfgOf P).hmacV))) t
      fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then tailOf P L wide t.mem else [])) ∧
        vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) := by
  refine WP.seq (WP.mono (ptrs_ok hL hc wide) fun p ⟨hcp, hmp, h9, h10, h15, h8⟩ => ?_)
  rw [← hmp]
  refine WP.seq (WP.mono (msgAny_ok hL hq hdn hcp h9 h10 h15 b full wide h8 hW hA)
    fun u ⟨hcu, hfu, hbu⟩ => ?_)
  have hlen' : len ≤ 256 := by
    have := P.wsizes
    subst hlen
    cases full
    · simp only [Bool.false_eq_true, ↓reduceIte]; anums
    · simp only [ite_true]
      cases hRW : P.R.wide
      · have := P.sizesA hRW; anums
      · have := P.sizesW hRW; omega
  refine WP.seq (WP.mono (hmacK_ok (P := P) hL hcu (len := len) hlen') fun w ⟨hcw, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacV_ok hL hcw) fun t' ⟨hc', hf', hk', hv'⟩ => ⟨hc', ?_, ?_, ?_⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by anums)))).trans hfw).trans hf'
  · have hku : kOf P L u.mem = kOf P L p.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    rw [hk', hkw, hku, hlen, hbu]
  · have hvu : vOf P L u.mem = vOf P L p.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ tail)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) (hq : L.q = P.Q) (hdn : dn = P.H.D) {t : State} (hc : Ctx L g m₀ t) (b : Nat) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
        tailOf P L P.R.wide t.mem) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) :=
  WP.mono (rekey_gen (full := true) (wide := P.R.wide) hL hq hdn hc (fun h => ⟨rfl, h⟩) (fun _ h => h) rfl)
    fun _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; rfl, h.2.2.2⟩

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hq : L.q = P.Q) (hdn : dn = P.H.D) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [0]) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) :=
  WP.mono (rekey_gen (b := 0) (full := false) (wide := false) hL hq hdn hc (fun h => nomatch h)
    (fun h => nomatch h) rfl) fun _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; simp, h.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64
