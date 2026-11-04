module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Msg
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on 32-bit ARM: the steps on `K` and `V`

`V = HMAC_K(V)` (`hmacV_ok`); `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then
`V = HMAC_K(V)` (`rekeyFull_ok`, steps d–g); and `K = HMAC_K(V ‖ 0x00)`,
then `V = HMAC_K(V)` (`rekey_ok`, step h.3). Each changes only `scratch`,
the stack below the frame, and `K` and `V`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `K` and `V`, of the hash function's output length, in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := keyOf P L m
abbrev vOfP (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := vOf L P.H.D m
/-- `h` in the messages of steps d and f. -/
abbrev hOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 P.hB) P.Q

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} (L : Lay dn) : List Region := [L.SCR, ⟨L.B, 152⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 152⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 152⟩, by simp, h⟩

theorem done_kvw {dst : Nat} (h : dst + P.H.D ≤ 128) :
    ∀ r ∈ [WK L, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + dst), P.H.D⟩], ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega_arith))
    · exact .inr (Region.sub_prefix (by omega_arith))
    · exact .inr (Offset.sub_base _ (by omega_arith))

/-- The data of `V = HMAC_K(V)`: `V`, in the frame. -/
theorem dataV : DataA L g m₀ [.dp .add .r1 .r8 (.imm (BitVec.ofNat 32 fV))] (L.fp + BitVec.ofNat 32 64) := fun _ _ _ hc k =>
  fpAdd_ok hc (d := .r1) (by decide) (o := fV) (by decide) fun u' c' m' v' k' =>
    k u' c' m' v' fun r h1 _ => k' r h1

/-- The data of the other steps: the message, in `scratch`. -/
theorem dataM : DataA L g m₀ (scrAt .r1 sMsg) (L.scr + BitVec.ofNat 32 2256) := fun _ _ _ hc k =>
  scrAt_ok hc (d := .r1) (by decide) (o := sMsg) (by decide) fun u' c' m' v' k' => k u' c' m' v' k'

theorem kv_disj {d : Nat} (hd : d = 0 ∨ d = 64) (hL : L.Ok) :
    ∀ r ∈ [WK L, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + (64 - d)), P.H.D⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 (24 + d), P.H.D⟩ r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hL.kc.sub_left (Offset.sub_base _ (by rcases hd with rfl | rfl <;> anums))).sub_right
      (Region.sub_prefix (by omega_arith))
  · exact Offset.disjoint_base _ (by omega_arith) (by rcases hd with rfl | rfl <;> anums)
  · exact Offset.disjoint _ (by rcases hd with rfl | rfl <;> anums) (by rcases hd with rfl | rfl <;> anums)
      (by rcases hd with rfl | rfl <;> anums)

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacV t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOfP P L t'.mem = P.mac (kOf P L t.mem) (vOfP P L t.mem) := by
  have hv : State.addr (L.fp + BitVec.ofNat 32 64) = L.B + BitVec.ofNat 64 88 := hL.fpA (by omega_arith)
  refine WP.mono (hmac_ok (P := P) hL hT hc (da := L.fp + BitVec.ofNat 32 64) (len := P.H.D) (dst := 64)
    dataV (.inl ⟨64, rfl, by anums⟩) (by anums) (by anums)) fun t' h => ?_
  have hm := h.mac
  rw [hv] at hm
  exact ⟨h.ctx, h.r9, h.frame.sub (done_kvw (by anums)),
    bytesAt_frame (p := L.B + BitVec.ofNat 64 (24 + 0)) h.frame (kv_disj (d := 0) (.inl rfl) hL) (by anums), hm⟩

/-- `K = HMAC_K(m)`, for the message `m` of `len` bytes at `scratch + 2256`. -/
theorem hmacK_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256) :
    WP isa ((cfgOf P).hmac (scrAt .r1 sMsg) len fK) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧
      Frame (KVW L) t.mem t'.mem ∧ vOfP P L t'.mem = vOfP P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (Spec.Sha256.bytesAt t.mem (msgA L) len) := by
  have hm : State.addr (L.scr + BitVec.ofNat 32 2256) = msgA L := scrA hL (by decide)
  refine WP.mono (hmac_ok (P := P) hL hT hc (da := L.scr + BitVec.ofNat 32 2256) (len := len) (dst := 0)
    dataM (.inr ⟨2256, rfl, by omega_arith, by omega_arith⟩) hlen (by anums)) fun t' h => ?_
  have hmac := h.mac
  rw [hm] at hmac
  exact ⟨h.ctx, h.r9, h.frame.sub (done_kvw (by anums)),
    bytesAt_frame (p := L.B + BitVec.ofNat 64 (24 + 64)) h.frame (kv_disj (d := 64) (.inr rfl) hL) (by anums), hmac⟩

/-- What the message's `h` needs of the layout: the scalars' length, and
the words at the frame's top. -/
def HOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := P.Q ≤ L.q ∧ L.e = P.e

/-- `h` fits the frame. -/
theorem hB_fit (P : RfcHash) : P.hB + P.Q ≤ 240 + 4 * P.e := by
  have := P.wsizes
  cases hw : P.wide
  · have := P.sizesA hw; have hF := P.hFits hw; have hh := P.R.hHigh_eq
    by_cases h8 : P.R.E.n = 8
    · have hq := hF.1 h8
      simp only [h8, decide_true] at hh
      simp only [RfcHash.hB, RfcHash.e, Impl.Ecdsa.Rfc6979.Arm.extra, hw, hh, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte]
      omega_arith
    · have hq := hF.2 h8
      simp only [h8, decide_false] at hh
      simp only [RfcHash.hB, RfcHash.e, Impl.Ecdsa.Rfc6979.Arm.extra, hw, hh, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte]
      omega_arith
  · simp only [RfcHash.hB, RfcHash.e, Impl.Ecdsa.Rfc6979.Arm.extra, hw, Bool.true_or, ↓reduceIte]
    omega_arith

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen (hL : L.Ok) (hT : TabL P L) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) {b : Nat} (hb : b < 2)
    {full : Bool} {ho : Nat} (hho : full = true → ho = P.hB - 24) {len : Nat}
    (hlen : len = if full then P.H.D + 2 * P.Q + 1 else P.H.D + 1) :
    WP isa (.seq (.block (Cfg.msg P.Q P.H.D b full ho))
      (.seq ((cfgOf P).hmac (scrAt .r1 sMsg) len fK) (cfgOf P).hmacV)) t
      fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOfP P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q ++ hOf P L t.mem else [])) ∧
        vOfP P L t'.mem = P.mac (kOf P L t'.mem) (vOfP P L t.mem) := by
  have hD4 : P.H.D % 4 = 0 := by anums
  obtain ⟨hq, hLe⟩ := hq
  have hmsg := msg_ok hL hc hb full ho (D := P.H.D) (Q := P.Q) (by anums) hD4 (by anums) (by anums) hq
    (fun hf => by
      have := hB_fit P; have := hB_ge P
      rw [hho hf, hLe]; omega_arith)
  have hh : (if full then Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q ++
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 (24 + ho)) P.Q
      else []) = (if full then Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q ++ hOf P L t.mem else []) := by
    cases full
    · rfl
    · have := hB_ge P
      rw [hho rfl, show 24 + (P.hB - 24) = P.hB by omega_arith]
  rw [hh] at hmsg
  refine WP.seq (WP.mono hmsg fun u ⟨hcu, h9u, hfu, hbu⟩ => ?_)
  refine WP.seq (WP.mono (hmacK_ok (P := P) hL hT hcu (len := len)
    (by cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> anums))
    fun w ⟨hcw, h9w, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacV_ok hL hT hcw) fun t' ⟨hc', h9', hf', hk', hv'⟩ => ⟨hc', by rw [h9', h9w, h9u], ?_, ?_, ?_⟩
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
theorem rekeyFull_ok (hL : L.Ok) (hT : TabL P L) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) {b : Nat} (hb : b < 2) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧
      Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOfP P L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q ++ hOf P L t.mem)) ∧
      vOfP P L t'.mem = P.mac (kOf P L t'.mem) (vOfP P L t.mem) :=
  rekey_gen (full := true) hL hT hq hc hb (ho := (cfgOf P).fHo) (fun _ => fHo_eq P) rfl

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hT : TabL P L) (hq : HOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOfP P L t.mem ++ [0]) ∧
      vOfP P L t'.mem = P.mac (kOf P L t'.mem) (vOfP P L t.mem) :=
  WP.mono (rekey_gen hL hT hq hc (b := 0) (by decide) (full := false) (ho := fH)
    (fun h => absurd h (by decide)) rfl) fun _ h => ⟨h.1, h.2.1, h.2.2.1, by
    rw [h.2.2.2.1]; simp, h.2.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
