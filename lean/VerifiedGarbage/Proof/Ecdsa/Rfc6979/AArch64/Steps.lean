module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce

/-!
# Deterministic ECDSA on AArch64: the steps on `K` and `V`

`V = HMAC_K(V)` (`hmacV_ok`); `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then
`V = HMAC_K(V)` (`rekeyFull_ok`, steps d–g); and `K = HMAC_K(V ‖ 0x00)`,
then `V = HMAC_K(V)` (`rekey_ok`, step h.3). Each changes only `scratch`,
the stack below the frame, and `K` and `V`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {P : RfcHash} {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `K` and `V` (of the hash function's output length) and `h`, in the frame. -/
abbrev kOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte := keyOf P L m
abbrev vOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 80) P.H.D
abbrev hOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 144) P.Q

/-- What follows `V ‖ b` in the message of steps d and f: `d ‖ h`. -/
abbrev tailOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m L.d P.Q ++ hOf P L m

/-- What the steps change: `scratch`, the stack below the frame, `K` and `V`. -/
abbrev KVW {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : List Region := [L.SCR, ⟨L.B, 144⟩]

theorem kvw_of {rs : List Region} (h : ∀ r ∈ rs, Region.Sub r L.SCR ∨ Region.Sub r ⟨L.B, 144⟩) :
    ∀ r ∈ rs, ∃ r' ∈ KVW L, Region.Sub r r' := fun r hr => by
  rcases h r hr with h | h
  · exact ⟨_, by simp, h⟩
  · exact ⟨⟨L.B, 144⟩, by simp, h⟩

theorem done_kvw {dst : Nat} (h : dst + P.H.D ≤ 128) :
    ∀ r ∈ [(⟨L.scr, 2432⟩ : Region), ⟨L.B, 16⟩, ⟨L.B + BitVec.ofNat 64 (16 + dst), P.H.D⟩],
      ∃ r' ∈ KVW L, Region.Sub r r' :=
  kvw_of fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (Region.sub_prefix (by omega))
    · exact .inr (Region.sub_prefix (by omega))
    · exact .inr (Offset.sub_base _ (by omega))

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ok (hL : L.Ok) (hdn : dn = P.H.D) (hh : HashOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).hmacV t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = kOf P L t.mem ∧ vOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem) := by
  refine WP.mono (hmac_ok (P := P) hL hdn hh hc (da := L.B + BitVec.ofNat 64 (16 + 64)) (ex := 0) (dst := 64)
    (fun u hu => fr_ok hL hu (d := .x2) (by decide) (o := 64) (by decide))
    (.inl ⟨80, rfl, by omega, by anums⟩) (by anums) (by anums)) fun t' h =>
    ⟨h.ctx, h.frame.sub (done_kvw (by anums)), bytesAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.stk_scr0 (by anums) (by omega)
      · exact Offset.disjoint_base _ (by omega) (by anums)
      · exact Offset.disjoint _ (by anums) (by anums) (by anums)) (by anums), h.mac⟩

/-- `K = HMAC_K(m)`, for the message `m` of `D + ex` bytes at `scratch + 2432`. -/
theorem hmacK_ok (hL : L.Ok) (hdn : dn = P.H.D) (hh : HashOk P L) {t : State} (hc : Ctx L g m₀ t) {ex : Nat}
    (hlen : P.H.D + ex ≤ 256) :
    WP isa ((cfgOf P).hmac (Cfg.scr .x2 sMsg) ex fK) t fun t' => Ctx L g m₀ t' ∧
      Frame (KVW L) t.mem t'.mem ∧ vOf P L t'.mem = vOf P L t.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem)
        (Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2432) (P.H.D + ex)) := by
  refine WP.mono (hmac_ok (P := P) hL hdn hh hc (da := L.scr + BitVec.ofNat 64 2432) (ex := ex) (dst := 0)
    (fun u hu => scr_ok hL hu (d := .x2) (by decide) (a := 2432) (by decide))
    (.inr ⟨2432, rfl, by omega, by omega⟩) hlen (by anums)) fun t' h =>
    ⟨h.ctx, h.frame.sub (done_kvw (by anums)), bytesAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hL.stk_scr0 (by anums) (by omega)
      · exact Offset.disjoint_base _ (by omega) (by anums)
      · exact Offset.disjoint _ (by anums) (by anums) (by anums)) (by anums), h.mac⟩

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen (hL : L.Ok) (hq : L.q = P.Q) (hdn : dn = P.H.D) (hh : HashOk P L) {t : State}
    (hc : Ctx L g m₀ t) {b : Nat} {full : Bool}
    {ex : Nat} (hex : ex = if full then 2 * P.Q + 1 else 1) :
    WP isa (.seq (.block Cfg.msgPtrs) (.seq (.block (Cfg.msg P.w P.Q b full))
      (.seq ((cfgOf P).hmac (Cfg.scr .x2 sMsg) ex fK) (cfgOf P).hmacV))) t
      fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
        kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++
          (if full then tailOf P L t.mem else [])) ∧
        vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) := by
  refine WP.seq (WP.mono (ptrs_ok hL hc) fun p ⟨hcp, hmp, h9, h10, h15, h8⟩ => ?_)
  rw [← hmp]
  have hs := P.wsizes
  refine WP.seq (WP.mono (msg_ok hL hcp h9 h10 h15 h8 b full (w := P.w) (Q := P.Q) (by rw [hdn]; anums)
    fun _ => ⟨by omega, by omega, by omega, by omega⟩) fun u ⟨hcu, hfu, hbu⟩ => ?_)
  have hlen' : P.H.D + ex ≤ 256 := by subst hex; cases full <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> anums
  refine WP.seq (WP.mono (hmacK_ok (P := P) hL hdn hh hcu (ex := ex) hlen') fun w ⟨hcw, hfw, hvw, hkw⟩ => ?_)
  refine WP.mono (hmacV_ok hL hdn hh hcw) fun t' ⟨hc', hf', hk', hv'⟩ => ⟨hc', ?_, ?_, ?_⟩
  · exact ((hfu.sub (kvw_of fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (Offset.sub_base _ (by anums)))).trans hfw).trans hf'
  · have hku : kOf P L u.mem = kOf P L p.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    have e : P.H.D + ex = if full then dn + 2 * P.Q + 1 else dn + 1 := by
      subst hex hdn; cases full <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    rw [hk', hkw, hku, e, hbu]
    subst hdn
    rfl
  · have hvu : vOf P L u.mem = vOf P L p.mem := bytesAt_frame hfu (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hL.stk_scr (by anums) (by anums)) (by anums)
    rw [hv', hk', hvw, hvu]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (hL : L.Ok) (hq : L.q = P.Q) (hdn : dn = P.H.D) (hh : HashOk P L)
    {t : State} (hc : Ctx L g m₀ t) (b : Nat) :
    WP isa ((cfgOf P).rekeyFull b) t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [BitVec.ofNat 8 b] ++ tailOf P L t.mem) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) :=
  WP.mono (rekey_gen (full := true) hL hq hdn hh hc rfl)
    fun _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; rfl, h.2.2.2⟩

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (hL : L.Ok) (hq : L.q = P.Q) (hdn : dn = P.H.D) (hh : HashOk P L) {t : State}
    (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).rekey t fun t' => Ctx L g m₀ t' ∧ Frame (KVW L) t.mem t'.mem ∧
      kOf P L t'.mem = P.mac (kOf P L t.mem) (vOf P L t.mem ++ [0]) ∧
      vOf P L t'.mem = P.mac (kOf P L t'.mem) (vOf P L t.mem) :=
  WP.mono (rekey_gen (b := 0) (full := false) hL hq hdn hh hc rfl)
    fun _ h => ⟨h.1, h.2.1, by rw [h.2.2.1]; simp, h.2.2.2⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64
