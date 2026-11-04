module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Msg
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.HmacSave
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Reduce
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Deterministic ECDSA on x86 (32-bit): the steps on `K` and `V`

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Steps.lean`): `V = HMAC_K(V)`
(`hmacVS_ok`, `hmacVR_ok`); `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then
`V = HMAC_K(V)` (`rekeyFull_ok`, steps d–g); and `K = HMAC_K(V ‖ 0x00)`,
then `V = HMAC_K(V)` (`rekey_ok`, step h.3). Each changes only `scratch`,
the stack below the frame, and `K` and `V`. The `V = HMAC_K(V)` after a new
`K` saves HMAC's states for it (`hmacVS_ok`, `SavedK`), from which the next
HMAC with that `K` starts (`hmacVR_ok`, and step f's `K = HMAC_K(…)`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `K` and `V` (of the hash function's output length) and `h`, in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := keyOf P L m
abbrev vOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 140) P.H.D
abbrev hOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := hPart P.Q P.hB L m

/-- HMAC's output is the hash function's. -/
theorem mac_length (P : RfcHash) (K t : List Byte) : (P.mac K t).length = P.H.D := by
  simp only [RfcHash.mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.macLen]

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 204⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 204⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 204⟩, by simp, h⟩

theorem done_kvw {w dst : Nat} (hw : w ≤ 8192) (h : dst + P.H.D ≤ 128) :
    ∀ r ∈ [(⟨L.scr, w⟩ : Region), ⟨L.B, 76⟩, ⟨L.B + BitVec.ofNat 64 (76 + dst), P.H.D⟩],
      ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix hw)
    · exact .inr (Region.sub_prefix (by omega_arith))
    · exact .inr (Offset.sub_base _ (by omega_arith))

/-- `scratch + 2256`, where the messages are. -/
theorem msgDA (hL : L.Ok) (hT : TabL P L) : ∀ u, Ctx L g m₀ u →
    WP isa (.block ((cfgOf P).scr .edx sMsg)) u (Upd L g m₀ u .edx (L.a4 + BitVec.ofNat 32 2256)) :=
  fun _ hu => scr_ok hL hT.cw hT.ch hu (d := .edx) (by decide) 2256

/-- `V`, in the frame. -/
theorem vDA (hL : L.Ok) : ∀ u, Ctx L g m₀ u →
    WP isa (.block (Cfg.fr .edx fV)) u (Upd L g m₀ u .edx (L.F + BitVec.ofNat 32 64)) :=
  fun _ hu => fr_ok hL hu (d := .edx) (by decide) 64

/-- `K = HMAC_K(m)`, for the message `m` of `len` bytes at `scratch + 2256`. -/
theorem hmacK_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256) :
    WP isa ((cfgOf P).hmac ((cfgOf P).scr .edx sMsg) len fK) t fun t' => Ctx L g m₀ t' ∧
      Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  have nB := hL.nB
  refine WP.mono (hmac_ok (P := P) hL hT hc (dv := L.a4 + BitVec.ofNat 32 2256) (len := len) (dst := 0)
    (msgDA hL hT) (.inr ⟨2256, rfl, by omega_arith, by omega_arith⟩) hlen (by nums)) fun t' h =>
    ⟨h.ctx, h.frame.sub (done_kvw (by decide) (by nums)), bytesAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.stk_scr0 (by nums) (by omega_arith)
      · exact Offset.disjoint_base _ (by omega_arith) (by nums)
      · exact Offset.disjoint _ (by nums) (by nums) (by nums)) (by nums), by
      have m := h.mac; rw [hL.scrv (by omega_arith)] at m; exact m⟩

/-- `K` and `V` survive what an HMAC writes, for a frame of `w ≤ 8192` bytes of `scratch`. -/
theorem kv_done {w dst : Nat} (hL : L.Ok) (hw : w ≤ 8192) {m m' : Mem}
    (hf : Frame [(⟨L.scr, w⟩ : Region), ⟨L.B, 76⟩, ⟨L.B + BitVec.ofNat 64 (76 + dst), P.H.D⟩] m m')
    {o : Nat} (ho : 76 ≤ o) (hod : o + P.H.D ≤ 76 + dst ∨ 76 + dst + P.H.D ≤ o) (hoe : o + P.H.D ≤ 272)
    (hdst : dst + P.H.D ≤ 180) :
    Spec.Sha256.bytesAt m' (L.B + BitVec.ofNat 64 o) P.H.D = Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 o) P.H.D :=
  bytesAt_frame hf (fun r hr => by
    have := L.he
    have := hL.nB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.stk_scr0 (by omega) hw
    · exact Offset.disjoint_base _ ho (by nums)
    · exact Offset.disjoint _ hod (by omega) (by omega)) (by nums)

theorem vData (hL : L.Ok) : Region.Disjoint ⟨(L.F + BitVec.ofNat 32 64).setWidth 64, P.H.D⟩ (SaveR L) := by
  rw [hL.frv (by omega_arith)]; exact hL.stk_scr (by nums) (by nums)

theorem vMac (hL : L.Ok) {m : Mem} :
    Spec.Sha256.bytesAt m ((L.F + BitVec.ofNat 32 64).setWidth 64) P.H.D = vOf P L m := by
  rw [hL.frv (by omega_arith)]

/-- `V = HMAC_K(V)`, HMAC's states for `K` saved. -/
theorem hmacVS_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacVS t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.mono (hmacS_ok (P := P) hL hT hc (dv := L.F + BitVec.ofNat 32 64) (len := P.H.D) (dst := 64)
    (vDA hL) (.inl ⟨64, rfl, by nums⟩) (vData hL) (by nums) (by nums)) fun t' h => ?_
  have hk : kOf P L t'.mem = kOf P L t.mem := kv_done hL (by decide) h.frame (o := 76) (by decide) (.inl (by nums)) (by nums) (by nums)
  exact ⟨h.ctx, h.frame.sub (done_kvw (by decide) (by nums)), hk, by rw [← vMac hL (m := t.mem)]; exact h.mac,
    by rw [hk]; exact h.saved⟩

/-- `V = HMAC_K(V)`, from the saved states for `K`, which it keeps. -/
theorem hmacVR_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).hmacVR t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) ∧
      SavedK P L t'.mem (kOf P L t'.mem) := by
  refine WP.mono (hmacR_ok (P := P) hL hT hc hS (dv := L.F + BitVec.ofNat 32 64) (len := P.H.D) (dst := 64)
    (vDA hL) (.inl ⟨64, rfl, by nums⟩) (by nums) (by nums)) fun t' ⟨h, hS'⟩ => ?_
  have hk : kOf P L t'.mem = kOf P L t.mem := kv_done hL (by decide) h.frame (o := 76) (by decide) (.inl (by nums)) (by nums) (by nums)
  exact ⟨h.ctx, h.frame.sub (done_kvw (by decide) (by nums)), hk, by rw [← vMac hL (m := t.mem)]; exact h.mac,
    by rw [hk]; exact hS'⟩

/-- `K = HMAC_K(m)` as `hmacK_ok`, from the saved states for `K` if `rs`. -/
theorem hmacKB_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256) (rs : Bool)
    (hS : rs = true → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa ((if rs then (cfgOf P).hmacR else (cfgOf P).hmac) ((cfgOf P).scr .edx sMsg) len fK) t fun t' =>
      Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := by
  cases rs
  · exact hmacK_ok hL hT hc hlen
  · refine WP.mono (hmacR_ok (P := P) hL hT hc (hS rfl) (dv := L.a4 + BitVec.ofNat 32 2256) (len := len) (dst := 0)
      (msgDA hL hT) (.inr ⟨2256, rfl, by omega, by omega⟩) hlen (by nums)) fun t' ⟨h, _⟩ =>
      ⟨h.ctx, h.frame.sub (done_kvw (by decide) (by nums)),
        kv_done hL (by decide) h.frame (o := 140) (by decide) (.inr (by nums)) (by nums) (by nums), by
        have m := h.mac; rw [hL.scrv (by omega_arith)] at m; exact m⟩

/-- What the steps need of the layout: the scalars' bytes, and the table
and the frame of `P`. -/
def HOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := P.Q ≤ L.q ∧ TabL P L

/-- `h`'s place fits above `K` and `V`, in the frame. -/
theorem hB_fit (hq : HOk P L) : 76 + (P.hB - 76) + P.Q ≤ 272 + 4 * L.e := by
  rw [hq.2.2.2.1]
  have hQ := P.sizes
  cases hw : P.wide
  · have hF := P.hFits hw
    have hh := hHigh_q P hw
    simp only [RfcHash.hB, RfcHash.e, Impl.Ecdsa.Rfc6979.X86.extra, hw, hh, Bool.false_or, Bool.false_eq_true,
      ite_false] at ⊢
    by_cases h64 : P.Q = 64
    · simp only [h64, decide_true, ite_true]; omega
    · simp only [h64, decide_false, Bool.false_eq_true, ite_false]
      have : P.w ≠ 8 := fun h => h64 (hF.1 h)
      have := hF.2 this; omega
  · simp only [RfcHash.hB, RfcHash.e, Impl.Ecdsa.Rfc6979.X86.extra, hw, Bool.true_or, ite_true]; nums

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) {b : Nat} {full : Bool}
    {ho : Nat} (hho : full = true → ho = P.hB - 76) {len : Nat}
    (hlen : len = if full then P.H.D + 2 * P.Q + 1 else P.H.D + 1) (rs : Bool)
    (hS : rs = true → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (.seq (.block (cfgOf P).msgPtrs) (.seq (.block (Cfg.msg P.Q P.H.D b full ho))
      (.seq ((if rs then (cfgOf P).hmacR else (cfgOf P).hmac) ((cfgOf P).scr .edx sMsg) len fK) (cfgOf P).hmacVS))) t
      fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else [])) ∧
        vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) := by
  have nB := hL.nB
  have hT := hq.2
  refine WP.seq (WP.mono (ptrs_ok hL hT.cw hT.ch hc) fun p ⟨hcp, hmp, hdip, hsip⟩ => ?_)
  rw [← hmp] at hS ⊢
  have hmsg := msg_ok hL hcp hdip hsip b full ho (D := P.H.D) (Q := P.Q) (by nums) (by nums) (by nums)
    (by nums) hq.1 (fun hf => by rw [hho hf]; exact hB_fit hq)
  have hh : (if full then Spec.Sha256.bytesAt p.mem L.d P.Q ++ hPart P.Q (76 + ho) L p.mem else []) =
      (if full then Spec.Sha256.bytesAt p.mem L.d P.Q ++ hOf P L p.mem else []) := by
    cases full
    · rfl
    · have := hB_ge P
      rw [hho rfl, show 76 + (P.hB - 76) = P.hB by omega]
  rw [hh] at hmsg
  refine WP.seq (WP.mono hmsg fun u ⟨hcu, hfu, hbu⟩ => ?_)
  have hku : kOf P L u.mem = kOf P L p.mem := bytesAt_frame hfu (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hL.stk_scr (by nums) (by nums)) (by nums)
  have hSu : rs = true → SavedK P L u.mem (kOf P L u.mem) := fun h => hku ▸ (hS h).frame hfu fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (by nums) (by nums) (by nums)
  refine WP.seq (WP.mono (hmacKB_ok (P := P) hL hT hcu (len := len)
    (by cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> nums) rs hSu)
    fun w ⟨hcw, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacVS_ok hL hT hcw) fun t' ⟨hc', hf', hk', hv', hs'⟩ => ⟨hc', ?_, ?_, ?_, hs'⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by nums)))).trans hfw).trans hf'
  · rw [hk', hkw, hku, hlen]
    rw [hbu]
  · have hvu : vOf P L u.mem = vOf P L p.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by nums) (by nums)) (by nums)
    rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) (b : Nat)
    (hS : b ≠ 0 → SavedK P L t.mem (kOf P L t.mem)) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem)) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) := by
  unfold Cfg.rekeyFull
  split
  · exact rekey_gen (full := true) hL hq hc (ho := (cfgOf P).fHo) (fun _ => fHo_eq P) rfl false
      (fun h => absurd h (by decide))
  · exact rekey_gen (full := true) hL hq hc (ho := (cfgOf P).fHo) (fun _ => fHo_eq P) rfl true
      fun _ => hS ‹_›

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [0]) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) ∧ SavedK P L t'.mem (kOf P L t'.mem) :=
  WP.mono (rekey_gen (b := 0) (full := false) hL hq hc (ho := fH)
    (fun h => absurd h (by decide)) rfl false (fun h => absurd h (by decide)))
    fun _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; simp, h.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.X86
