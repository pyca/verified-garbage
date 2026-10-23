module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Msg
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on PPC64LE: the steps on `K` and `V`

`V = HMAC_K(V)` (`hmacV_ok`); `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then
`V = HMAC_K(V)` (`rekeyFull_ok`, steps d–g); and `K = HMAC_K(V ‖ 0x00)`,
then `V = HMAC_K(V)` (`rekey_ok`, step h.3). Each changes only `scratch`,
the stack below the frame, and `K` and `V`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- `V`: the first `D` bytes of the frame's `V`. -/
abbrev vOf (P : Kit) (L : Lay dn) (m : Mem) : List Byte := Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 192) P.H.D

/-- `h`: the frame's `Q` bytes at `h`. -/
abbrev hOf (L : Lay dn) (m : Mem) : List Byte := Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 256) L.q

/-- What a step on `K` and `V` changes: `scratch`'s first part, the stack
below the frame, `K` and `V`. -/
abbrev kvW (L : Lay dn) : List Region :=
  [⟨L.scr, 8192⟩, ⟨L.B, 96⟩, ⟨L.B + BitVec.ofNat 64 128, 128⟩]

/-- The frame of an HMAC's writes, within a step's. -/
theorem macd_frame {P : Kit} {t u : State} {da : Addr} {len dst : Nat} (h : Macd P L g lr m₀ t da len dst u)
    (hdst : 32 ≤ dst ∧ dst + 64 ≤ 160) (hD : P.H.D ≤ 64) : Frame (kvW L) t.mem u.mem :=
  h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨L.scr, 8192⟩, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨⟨L.B, 96⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 128, 128⟩, by simp, Offset.sub _ (by omega) (by omega)⟩

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ok (P : Kit) {c : Cfg} (hcH : c.H = P.hm) (hL : L.Ok) (hq : L.q ≤ 48) {t : State}
    (hc : Ctx L g lr m₀ t) :
    WP isa c.hmacV t fun u => Ctx L g lr m₀ u ∧ Frame (kvW L) t.mem u.mem ∧
      keyOf P L u.mem = keyOf P L t.mem ∧ hOf L u.mem = hOf L t.mem ∧
      vOf P L u.mem = Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem) (vOf P L t.mem) := by
  have hD := P.hH.hD64
  have hnB := hL.nB
  have hB : P.H.B ≤ 128 := by rcases P.hH.dims.B with h | h <;> omega
  rw [Cfg.hmacV, hcH]
  refine WP.mono (hmac_ok P hcH hL hc (dataA := [.addSp .r5 fV]) (da := L.B + BitVec.ofNat 64 192) (len := P.H.D)
    (dst := 96) (.inl ⟨192, rfl, by omega, by omega⟩) (by omega) ⟨by omega, by omega⟩
    fun u hu _ => dataV_ok hc u (by rw [hu.sp, hc.sp])) fun u hm => ?_
  have hf := macd_frame hm ⟨by omega, by omega⟩ hD
  refine ⟨hm.ctx, hf, ?_, ?_, ?_⟩
  · exact bytesAt_frame hm.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · have := hL.stk_scr (d := 128) (n := P.H.D) (e := 0) (k := 2256) (by omega) (by omega)
        rwa [BitVec.add_zero] at this
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
  · exact bytesAt_frame hm.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · have := hL.stk_scr (d := 256) (n := L.q) (e := 0) (k := 2256) (by omega) (by omega)
        rwa [BitVec.add_zero] at this
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
  · exact hm.mac

/-- What `K`, `V` and `h` are after a step's HMAC into `K` and the
`V = HMAC_K(V)` after it. -/
structure Rekeyed (P : Kit) (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (t : State) (msg : List Byte)
    (u : State) : Prop where
  ctx : Ctx L g lr m₀ u
  frame : Frame (kvW L) t.mem u.mem
  key : keyOf P L u.mem = Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem) msg
  v : vOf P L u.mem = Spec.Hmac.hmac P.hH.SH.H (keyOf P L u.mem) (vOf P L t.mem)
  h : hOf L u.mem = hOf L t.mem

/-- The HMAC of the message at `scratch + 2256` into `K`, then `V = HMAC_K(V)`. -/
theorem rekeyTail_ok (P : Kit) {c : Cfg} (hcH : c.H = P.hm) (hL : L.Ok) (hq : L.q ≤ 48) {t₀ t : State}
    (hc : Ctx L g lr m₀ t) {len : Nat} (hlen : len ≤ 161) (hf : Frame (kvW L) t₀.mem t.mem)
    (hK : keyOf P L t.mem = keyOf P L t₀.mem) (hV : vOf P L t.mem = vOf P L t₀.mem) (hH : hOf L t.mem = hOf L t₀.mem) :
    WP isa (.seq (c.hmac [.addi .r5 .r12 sMsg] len fK) c.hmacV) t
      (Rekeyed P L g lr m₀ t₀ (Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len)) := by
  have hD := P.hH.hD64
  have hnB := hL.nB
  have hB : P.H.B ≤ 128 := by rcases P.hH.dims.B with h | h <;> omega
  refine WP.seq (WP.mono (hmac_ok P hcH hL hc (dataA := [.addi .r5 .r12 sMsg]) (da := L.scr + BitVec.ofNat 64 2256)
    (len := len) (dst := 32) (.inr ⟨2256, rfl, by omega, by omega⟩) (by omega) ⟨by omega, by omega⟩
    fun u _ hr => dataM_ok u hr) fun u₁ hm => ?_)
  have hf₁ := macd_frame hm ⟨by omega, by omega⟩ hD
  have kv₁ : vOf P L u₁.mem = vOf P L t.mem := bytesAt_frame hm.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · have := hL.stk_scr (d := 192) (n := P.H.D) (e := 0) (k := 2256) (by omega) (by omega)
        rwa [BitVec.add_zero] at this
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
  have kh₁ : hOf L u₁.mem = hOf L t.mem := bytesAt_frame hm.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · have := hL.stk_scr (d := 256) (n := L.q) (e := 0) (k := 2256) (by omega) (by omega)
        rwa [BitVec.add_zero] at this
      · exact Offset.disjoint_base _ (by omega) (by omega)
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
  refine WP.mono (hmacV_ok P hcH hL hq hm.ctx) fun u ⟨hcu, hfu, hku, hhu, hvu⟩ => ?_
  have hmac₁ : keyOf P L u₁.mem = Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem)
      (Spec.Sha256.bytesAt t.mem (L.scr + BitVec.ofNat 64 2256) len) := hm.mac
  refine ⟨hcu, (hf.trans hf₁).trans hfu, ?_, ?_, ?_⟩
  · rw [hku, hmac₁, hK]
  · rw [hvu, kv₁, hV, hku]
  · rw [hhu, kh₁, hH]

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)` (steps d–e, f–g). -/
theorem rekeyFull_ok (P : Kit) {c : Cfg} (hcH : c.H = P.hm) (hcl : c.len = L.q) (hL : L.Ok) (hq : L.q ≤ 48)
    (hq4 : L.q % 4 = 0) {t : State} (hc : Ctx L g lr m₀ t) {b : Nat} (hb : b < 2) :
    WP isa (c.rekeyFull b) t (Rekeyed P L g lr m₀ t
      (vOf P L t.mem ++ BitVec.ofNat 8 b :: (Spec.Sha256.bytesAt t.mem L.d L.q ++ hOf L t.mem))) := by
  have hD := P.hH.hD64
  have hD4 := P.hH.hD4
  have hnB := hL.nB
  rw [Cfg.rekeyFull, hcl, hcH]
  refine WP.seq (WP.mono (msg_ok hL hc (D := P.H.D) (b := b) true hD4 hD hq4 hq (by omega)) fun u ⟨hcu, hfu, hmu⟩ => ?_)
  simp only [ite_true] at hmu
  have keep : ∀ {p : Addr} {n : Nat}, Region.Disjoint ⟨p, n⟩ ⟨L.scr + BitVec.ofNat 64 2256, P.H.D + 1 + 2 * L.q⟩ →
      n ≤ 8192 → Spec.Sha256.bytesAt u.mem p n = Spec.Sha256.bytesAt t.mem p n :=
    fun h hn => bytesAt_frame hfu (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h) (by omega)
  have hf : Frame (kvW L) t.mem u.mem := hfu.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨L.scr, 8192⟩, by simp, Offset.sub_base _ (by omega)⟩
  refine WP.mono (rekeyTail_ok P hcH hL hq hcu (len := P.H.D + 2 * L.q + 1) (by omega) hf (keep (hL.stk_scr (by omega) (by omega)) (by omega))
    (keep (hL.stk_scr (by omega) (by omega)) (by omega)) (keep (hL.stk_scr (by omega) (by omega)) (by omega)))
    fun v hv => ?_
  rw [show P.H.D + 2 * L.q + 1 = P.H.D + 1 + 2 * L.q by omega, hmu] at hv
  simpa only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using hv

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)` (step h.3). -/
theorem rekey_ok (P : Kit) {c : Cfg} (hcH : c.H = P.hm) (hcl : c.len = L.q) (hL : L.Ok) (hq : L.q ≤ 48)
    (hq4 : L.q % 4 = 0) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa c.rekey t (Rekeyed P L g lr m₀ t (vOf P L t.mem ++ [0])) := by
  have hD := P.hH.hD64
  have hD4 := P.hH.hD4
  have hnB := hL.nB
  rw [Cfg.rekey, hcl, hcH]
  refine WP.seq (WP.mono (msg_ok hL hc (D := P.H.D) (b := 0) false hD4 hD hq4 hq (by omega)) fun u ⟨hcu, hfu, hmu⟩ => ?_)
  simp only [Bool.false_eq_true, ite_false, List.append_nil, Nat.add_zero] at hmu
  have keep : ∀ {p : Addr} {n : Nat}, Region.Disjoint ⟨p, n⟩ ⟨L.scr + BitVec.ofNat 64 2256, P.H.D + 1 + 2 * L.q⟩ →
      n ≤ 8192 → Spec.Sha256.bytesAt u.mem p n = Spec.Sha256.bytesAt t.mem p n :=
    fun h hn => bytesAt_frame hfu (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h) (by omega)
  have hf : Frame (kvW L) t.mem u.mem := hfu.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨L.scr, 8192⟩, by simp, Offset.sub_base _ (by omega)⟩
  refine WP.mono (rekeyTail_ok P hcH hL hq hcu (len := P.H.D + 1) (by omega) hf (keep (hL.stk_scr (by omega) (by omega)) (by omega))
    (keep (hL.stk_scr (by omega) (by omega)) (by omega)) (keep (hL.stk_scr (by omega) (by omega)) (by omega)))
    fun v hv => ?_
  rw [hmu] at hv
  exact hv

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
