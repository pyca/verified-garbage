module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Deterministic ECDSA on 32-bit ARM: the steps on `K` and `V`

`V = HMAC_K(V)` (`hmacV_ok`); `K = HMAC_K(V ‖ m)` for the message `m` at
`scratch + 2256` (`hmacK_ok`); `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then
`V = HMAC_K(V)` (`rekeyFull_ok`, steps d–g); and `K = HMAC_K(V ‖ 0x00)`,
then `V = HMAC_K(V)` (`rekey_ok`, step h.3). Each changes only `scratch`,
the stack below the frame, and `K` and `V`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `K` and `V`, of the hash function's output length, in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} (L : Lay dn) (m : Mem) : List Byte := keyOf P L m

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
    · exact .inl (Region.sub_prefix (by omega_arith))
    · exact .inr (Region.sub_prefix (by omega_arith))
    · exact .inr (Offset.sub_base _ (by omega_arith))

theorem st_disj (hL : L.Ok) {d n : Nat} (hd : 24 ≤ d) (hn : d + n ≤ 536) :
    ∀ r ∈ [WK L, ⟨L.B, 24⟩], Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hL.kc.sub_left (Offset.sub_base _ hn)).sub_right (Region.sub_prefix (by omega_arith))
  · exact Offset.disjoint_base _ hd (by omega_arith)

theorem kv_disj {d : Nat} (hd : d = 0 ∨ d = 64) (hL : L.Ok) :
    ∀ r ∈ [WK L, ⟨L.B, 24⟩, ⟨L.B + BitVec.ofNat 64 (24 + (64 - d)), P.F.H.D⟩],
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 (24 + d), P.F.H.D⟩ r := fun r hr => by
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
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) := by
  unfold Cfg.hmacV
  refine WP.seq (WP.mono (init_step hL hT hc) fun u hu => ?_)
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w hw => ?_)
  have hv : vOf P L u.mem = vOf P L t.mem :=
    bytesAt_frame hu.frame (st_disj hL (by decide) (by anums)) (by anums)
  rw [hv] at hw
  refine WP.mono (fin_step (len := 0) (dst := 64) hL hT hw (by simp [vOf, Spec.Sha256.bytesAt]) (by decide)
    (by anums) (by decide) (by decide)) fun t' h => ?_
  exact ⟨h.ctx, h.r9, h.frame.sub (done_kvw (by anums)),
    bytesAt_frame (p := L.B + BitVec.ofNat 64 (24 + 0)) h.frame (kv_disj (d := 0) (.inl rfl) hL) (by anums),
    h.mac⟩

/-- `K = HMAC_K(V ‖ m)`, for the message `m` of `len` bytes at `scratch + 2256`. -/
theorem hmacK_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {len : Nat} (hlen : len ≤ 256)
    (hle : encodable (BitVec.ofNat 32 len) = true) :
    WP isa ((cfgOf P).hmacK len) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧
      Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ Spec.Sha256.bytesAt t.mem (msgA L) len) := by
  unfold Cfg.hmacK
  refine WP.seq (WP.mono (init_step hL hT hc) fun u hu => ?_)
  refine WP.seq (WP.mono (updV_step hL hT hu) fun w hw => ?_)
  have hv : vOf P L u.mem = vOf P L t.mem :=
    bytesAt_frame hu.frame (st_disj hL (by decide) (by anums)) (by anums)
  rw [hv] at hw
  refine WP.seq (WP.mono (updM_step hL hT hw (by simp [vOf, Spec.Sha256.bytesAt]) hlen) fun w' hw' => ?_)
  have hm : Spec.Sha256.bytesAt w.mem (msgA L) len = Spec.Sha256.bytesAt t.mem (msgA L) len := by
    have hf := hw.frame
    refine bytesAt_frame hf (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact (low_scr hL (by omega_arith) (by omega_arith)).symm
  rw [hm] at hw'
  refine WP.mono (fin_step (len := len) (dst := 0) hL hT hw' (by simp [vOf, Spec.Sha256.bytesAt]) hlen
    (by anums) (by decide) hle) fun t' h => ?_
  exact ⟨h.ctx, h.r9, h.frame.sub (done_kvw (by anums)),
    bytesAt_frame (p := L.B + BitVec.ofNat 64 (24 + 64)) h.frame (kv_disj (d := 64) (.inr rfl) hL) (by anums),
    h.mac⟩

/-- `K = HMAC_K(V ‖ b (‖ d ‖ h))`, then `V = HMAC_K(V)`. -/
theorem rekey_gen (hL : L.Ok) (hT : TabL P L) (hq : P.Q ≤ L.q) {t : State} (hc : Ctx L g m₀ t) {b : Nat}
    (hb : b < 2) (full : Bool) {len : Nat} (hlen : len = if full then 1 + 2 * P.Q else 1) :
    WP isa (.seq (.block ((cfgOf P).msg b full)) (.seq ((cfgOf P).hmacK len) (cfgOf P).hmacV)) t
      fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q ++ hOf P L t.mem else [])) ∧
        vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) := by
  refine WP.seq (WP.mono (msg_ok hL hq hc hb full) fun u ⟨hcu, h9u, hfu, hbu⟩ => ?_)
  have hl : len ≤ 256 := by cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> anums
  have he : encodable (BitVec.ofNat 32 len) = true := encodable_lt (by
    cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> anums)
  refine WP.seq (WP.mono (hmacK_ok hL hT hcu (len := len) hl he) fun w ⟨hcw, h9w, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacV_ok hL hT hcw) fun t' ⟨hc', h9', hf', hk', hv'⟩ => ⟨hc', by rw [h9', h9w, h9u], ?_, ?_, ?_⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by anums)))).trans hfw).trans hf'
  · have hku : kOf P L u.mem = kOf P L t.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    have hvu : vOf P L u.mem = vOf P L t.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    rw [hk', hkw, hku, hvu, List.append_assoc, hlen, hbu]
  · have hvu : vOf P L u.mem = vOf P L t.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) (hT : TabL P L) (hq : P.Q ≤ L.q) {t : State} (hc : Ctx L g m₀ t) {b : Nat}
    (hb : b < 2) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧
      Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
        (Spec.Sha256.bytesAt t.mem (State.addr L.d) P.Q ++ hOf P L t.mem)) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) :=
  rekey_gen hL hT hq hc hb true (len := 1 + 2 * (cfgOf P).len) rfl

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hT : TabL P L) (hq : P.Q ≤ L.q) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g m₀ t' ∧ t'.gpr .r9 = t.gpr .r9 ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [0]) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) :=
  WP.mono (rekey_gen hL hT hq hc (b := 0) (by decide) false (len := 1) rfl) fun _ h => ⟨h.1, h.2.1, h.2.2.1, by
    rw [h.2.2.2.1]; simp, h.2.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.Arm
