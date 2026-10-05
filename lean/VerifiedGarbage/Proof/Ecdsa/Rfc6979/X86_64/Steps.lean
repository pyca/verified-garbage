import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Msg

/-!
# Deterministic ECDSA on x86-64: the steps on `K` and `V`

`V = HMAC_K(V)` (`hmacV_ok`); `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then
`V = HMAC_K(V)` (`rekeyFull_ok`, steps d–g); and `K = HMAC_K(V ‖ 0x00)`,
then `V = HMAC_K(V)` (`rekey_ok`, step h.3). Each changes only `scratch`,
the stack below the frame, and `K` and `V`.
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `K` and `V` (of the hash function's output length) and `h`, in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := keyOf P L m
abbrev vOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 88) P.H.D
abbrev hOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := hPart P.R.wide P.Q P.H.D L m

/-- HMAC's output is the hash function's. -/
theorem mac_length (P : RfcHash) (K t : List Byte) : (P.mac K t).length = P.H.D := by
  have := P.ok.hDN
  simp only [RfcHash.mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.ok.hash, List.length_take,
    Proof.MdStream.Md.hash, P.ok.md.digest_length]
  omega

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 152⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 152⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 152⟩, by simp, h⟩

theorem done_kvw {dst : Nat} (h : dst + P.H.D ≤ 128) :
    ∀ r ∈ [(⟨L.scr, 2256⟩ : Region), ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩],
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
  refine WP.mono (hmac_ok (P := P) hL hc (da := L.B + BitVec.ofNat 64 (24 + 64)) (len := P.H.D) (dst := 64)
    (fun u hu => fr_ok hL hu (d := .rdx) (by decide) (o := 64) (by decide))
    (.inl ⟨88, rfl, by omega, by nums⟩) (by nums) (by nums)) fun t' h =>
    ⟨h.ctx, h.frame.sub (done_kvw (by nums)), bytesAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.stk_scr0 (by nums) (by omega)
      · exact Offset.disjoint_base _ (by omega) (by nums)
      · exact Offset.disjoint _ (by nums) (by nums) (by nums)) (by nums), h.mac⟩

/-- `K = HMAC_K(m)`, for the message `m` of `len` bytes at `scratch + 2256`. -/
theorem hmacK_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256) :
    WP isa ((cfgOf P).hmac (Cfg.scr .rdx sMsg) len fK) t fun t' => Ctx L g m₀ t' ∧
      Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  refine WP.mono (hmac_ok (P := P) hL hc (da := L.scr + BitVec.ofNat 64 2256) (len := len) (dst := 0)
    (fun u hu => scr_ok hL hu (d := .rdx) (by decide) (a := 2256) (by decide))
    (.inr ⟨2256, rfl, by omega, by omega⟩) hlen (by nums)) fun t' h =>
    ⟨h.ctx, h.frame.sub (done_kvw (by nums)), bytesAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.stk_scr0 (by nums) (by omega)
      · exact Offset.disjoint_base _ (by omega) (by nums)
      · exact Offset.disjoint _ (by nums) (by nums) (by nums)) (by nums), h.mac⟩

/-- What the message's `h` needs of the layout: unless two `V`s make a
candidate, `h` in the frame; if they do, the digest. -/
def HOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := P.Q ≤ L.q ∧ (P.R.wide = true → P.H.D ≤ dn)

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) {b : Nat} {full wd : Bool}
    (hwd : full = true → wd = P.R.wide) {len : Nat}
    (hlen : len = if full then P.H.D + 2 * P.Q + 1 else P.H.D + 1) :
    WP isa (.seq (.block (Cfg.msgPtrs wd)) (.seq (.block (Cfg.msg P.Q P.H.D b full wd))
      (.seq ((cfgOf P).hmac (Cfg.scr .rdx sMsg) len fK) (cfgOf P).hmacV))) t
      fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else [])) ∧
        vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) := by
  refine WP.seq (WP.mono (ptrs_ok hL hc wd) fun p ⟨hcp, hmp, hdip, hsip, hdxp⟩ => ?_)
  rw [← hmp]
  have hmsg := msg_ok hL hcp hdip hsip b full wd hdxp (D := P.H.D) (Q := P.Q) (by nums) (by nums) (by nums)
    (by nums) hq.1 (fun hf hw => by
      have := P.sizesA (hw ▸ hwd hf).symm; exact ⟨by rw [this.1]; omega, by omega⟩)
    (fun hf hw => by
      have := P.sizesW (hw ▸ hwd hf).symm; exact ⟨by omega, by omega, hq.2 (hw ▸ hwd hf).symm⟩)
  have hh : (if full then Spec.Sha256.bytesAt p.mem L.d P.Q ++ hPart wd P.Q P.H.D L p.mem else []) =
      (if full then Spec.Sha256.bytesAt p.mem L.d P.Q ++ hOf P L p.mem else []) := by
    cases full
    · rfl
    · rw [hwd rfl]
  rw [hh] at hmsg
  refine WP.seq (WP.mono hmsg fun u ⟨hcu, hfu, hbu⟩ => ?_)
  refine WP.seq (WP.mono (hmacK_ok (P := P) hL hcu (len := len) (by cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> nums))
    fun w ⟨hcw, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacV_ok hL hcw) fun t' ⟨hc', hf', hk', hv'⟩ => ⟨hc', ?_, ?_, ?_⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by nums)))).trans hfw).trans hf'
  · have hku : kOf P L u.mem = kOf P L p.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by nums) (by nums)) (by nums)
    rw [hk', hkw, hku, hlen]
    rw [hbu]
  · have hvu : vOf P L u.mem = vOf P L p.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by nums) (by nums)) (by nums)
    rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) (b : Nat) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem)) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) :=
  rekey_gen (full := true) hL hq hc (fun _ => rfl) rfl

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [0]) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) :=
  WP.mono (rekey_gen (b := 0) (full := false) (wd := false) hL hq hc (fun h => absurd h (by decide)) rfl)
    fun _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; simp, h.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64
