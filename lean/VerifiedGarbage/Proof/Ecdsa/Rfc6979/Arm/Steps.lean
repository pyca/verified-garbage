import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Msg

/-!
# Deterministic ECDSA on 32-bit ARM: the steps on `K` and `V`

`V = HMAC_K(V)` (`hmacV_ok`); `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then
`V = HMAC_K(V)` (`rekeyFull_ok`, steps d–g); and `K = HMAC_K(V ‖ 0x00)`,
then `V = HMAC_K(V)` (`rekey_ok`, step h.3). Each changes only `scratch`,
the stack below the frame, and `K` and `V`.
-/

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `K` and `V`, of the hash function's output length, in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := keyOf P L m
abbrev vOfP (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := vOf L P.F.H.D m

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 152⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 152⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 152⟩, by simp, h⟩

theorem done_kvw {dst : Nat} (h : dst + P.F.H.D ≤ 128) :
    ∀ r ∈ [WK L, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), P.F.H.D⟩], ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega))
    · exact .inr (Region.sub_prefix (by omega))
    · exact .inr (Offset.sub_base _ (by omega))

/-- The data of `V = HMAC_K(V)`: `V`, in the frame. -/
theorem dataV : DataA L g m₀ [.dp .add .r1 .r8 (.imm (BitVec.ofNat 32 fV))] (L.fp + BitVec.ofNat 32 64) := fun _ _ _ hc k =>
  fpAdd_ok hc (d := .r1) (by decide) (o := fV) (by decide) fun u' c' m' v' k' =>
    k u' c' m' v' fun r h1 _ => k' r h1

/-- The data of the other steps: the message, in `scratch`. -/
theorem dataM : DataA L g m₀ (scrAt .r1 sMsg) (L.scr + BitVec.ofNat 32 2256) := fun _ _ _ hc k =>
  scrAt_ok hc (d := .r1) (by decide) (o := sMsg) (by decide) fun u' c' m' v' k' => k u' c' m' v' k'

theorem kv_disj {d : Nat} (hd : d = 0 ∨ d = 64) (hL : L.Ok) :
    ∀ r ∈ [WK L, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + (64 - d)), P.F.H.D⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 (24 + d), P.F.H.D⟩ r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hL.kc.sub_left (Offset.sub_base _ (by rcases hd with rfl | rfl <;> anums))).sub_right
      (Region.sub_prefix (by omega))
  · exact Offset.disjoint_base _ (by omega) (by rcases hd with rfl | rfl <;> anums)
  · exact Offset.disjoint _ (by rcases hd with rfl | rfl <;> anums) (by rcases hd with rfl | rfl <;> anums)
      (by rcases hd with rfl | rfl <;> anums)

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacV t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOfP P L t'.mem = P.mac (kOf P L t.mem) (vOfP P L t.mem) := by
  have hv : State.addr (L.fp + BitVec.ofNat 32 64) = L.B + BitVec.ofNat 64 88 := hL.fpA (by decide)
  refine WP.mono (hmac_ok (P := P) hL hc (da := L.fp + BitVec.ofNat 32 64) (len := P.F.H.D) (dst := 64)
    dataV (.inl ⟨64, rfl, by anums⟩) (by anums) (by anums) (by decide)) fun t' h => ?_
  have hm := h.mac
  rw [hv] at hm
  exact ⟨h.ctx, h.r9, h.frame.sub (done_kvw (by anums)),
    bytesAt_frame (p := L.B + BitVec.ofNat 64 (24 + 0)) h.frame (kv_disj (d := 0) (.inl rfl) hL) (by anums), hm⟩

/-- `K = HMAC_K(m)`, for the message `m` of `len` bytes at `scratch + 2256`. -/
theorem hmacK_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 192) :
    WP isa ((cfgOf P).hmac (scrAt .r1 sMsg) len fK) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧
      Frame (KVW L) t.mem t'.mem ∧ vOfP P L t'.mem = vOfP P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (Spec.Sha256.bytesAt t.mem (msgA L) len) := by
  have hm : State.addr (L.scr + BitVec.ofNat 32 2256) = msgA L := scrA hL (by decide)
  refine WP.mono (hmac_ok (P := P) hL hc (da := L.scr + BitVec.ofNat 32 2256) (len := len) (dst := 0)
    dataM (.inr ⟨2256, rfl, by omega, by omega⟩) hlen (by anums) (by decide)) fun t' h => ?_
  have hmac := h.mac
  rw [hm] at hmac
  exact ⟨h.ctx, h.r9, h.frame.sub (done_kvw (by anums)),
    bytesAt_frame (p := L.B + BitVec.ofNat 64 (24 + 64)) h.frame (kv_disj (d := 64) (.inr rfl) hL) (by anums), hmac⟩

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen (hL : L.Ok) (hq : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) {b : Nat} (hb : b < 2)
    {full : Bool} {len : Nat} (hlen : len = if full then P.F.H.D + 8 * P.k + 1 else P.F.H.D + 1) :
    WP isa (.seq (.block (Cfg.msg P.k P.F.H.D b full))
      (.seq ((cfgOf P).hmac (scrAt .r1 sMsg) len fK) (cfgOf P).hmacV)) t
      fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOfP P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem (State.addr L.d) (8 * P.w) ++ hOf P L t.mem else [])) ∧
        vOfP P L t'.mem = P.mac (kOf P L t'.mem) (vOfP P L t.mem) := by
  have hD4 : P.F.H.D % 4 = 0 := by anums
  refine WP.seq (WP.mono (msg_ok hL hc hb full (D := P.F.H.D) (by anums) hD4 (by rw [hq]; anums) (by anums))
    fun u ⟨hcu, h9u, hfu, hbu⟩ => ?_)
  have e4 : 4 * P.k = 8 * P.w := by anums
  rw [e4] at hbu
  refine WP.seq (WP.mono (hmacK_ok (P := P) hL hcu (len := len)
    (by cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> anums))
    fun w ⟨hcw, h9w, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacV_ok hL hcw) fun t' ⟨hc', h9', hf', hk', hv'⟩ => ⟨hc', by rw [h9', h9w, h9u], ?_, ?_, ?_⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by anums)))).trans hfw).trans hf'
  · have hku : kOf P L u.mem = kOf P L t.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    rw [hk', hkw, hku, hlen, hbu]
  · have hvu : vOfP P L u.mem = vOfP P L t.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) (hq : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) {b : Nat} (hb : b < 2) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧
      Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOfP P L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem (State.addr L.d) (8 * P.w) ++ hOf P L t.mem)) ∧
      vOfP P L t'.mem = P.mac (kOf P L t'.mem) (vOfP P L t.mem) :=
  rekey_gen (full := true) hL hq hc hb rfl

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hq : L.q = 8 * P.w) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOfP P L t.mem ++ [0]) ∧
      vOfP P L t'.mem = P.mac (kOf P L t'.mem) (vOfP P L t.mem) :=
  WP.mono (rekey_gen hL hq hc (b := 0) (by decide) (full := false) rfl) fun _ h => ⟨h.1, h.2.1, h.2.2.1, by
    rw [h.2.2.2.1]; simp, h.2.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
