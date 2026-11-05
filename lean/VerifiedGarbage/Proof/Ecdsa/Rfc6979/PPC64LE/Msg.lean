module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Hmac
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step

/-!
# Deterministic ECDSA on PPC64LE: the messages of steps d, f and h.3

The byte `b`, and `‖ d ‖ h` if `full`, at `scratch + 2256` (`msg_ok`), after
the pointers (`msgPtrs_ok`): the byte, then the private key and `h`, `Q` bytes
each, copied a 32-bit word, then a byte, at a time (`copyN_ok`). HMAC's text
is `V` (`D` bytes, from the frame, the table's `update` with it), then this
message.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)
open VG.Proof.Hmac.Common (bytesAt_add)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- The pointers: the frame's base in `r11`, `scratch` in `r9`, `d` in `r10`. -/
theorem msgPtrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun u => Ctx L g lr m₀ u ∧ u.mem = t.mem ∧ Kp [.r9, .r10, .r11] t u ∧
      u.gpr .r11 = L.B + BitVec.ofNat 64 96 ∧ u.gpr .r9 = L.scr ∧ u.gpr .r10 = L.d := by
  refine WP.of_syms (stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 272) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc.inFrK k₁ (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 288) (by decide) (by decide)
    (by rw [k₂.gpr _ (by decide), hb, fr_add]; rfl) (hc.inFrK (k₁.mono.trans k₂.mono (rs := [.r11, .r9])) (by omega) (by omega))
    fun t₃ k₃ m₃ v₃ => wp_nil fun hsy => ?_
  have K : Kp [.r9, .r10, .r11] t t₃ := (k₁.mono.trans k₂.mono).trans k₃.mono
  have hm : t₃.mem = t.mem := by rw [m₃, m₂, m₁]
  exact ⟨hc.kp hL K hm hsy, hm, K, by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), hb],
    by rw [k₃.gpr _ (by decide), v₂, m₁, hc.pScr], by rw [v₃, m₂, m₁, hc.pD]⟩

theorem bytesAt_byte (m : Mem) (a : Addr) (v : BitVec 8) : Spec.Sha256.bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [Spec.Sha256.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero, Mem.writeW,
    Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero, List.cons.injEq, and_true]
  exact BitVec.eq_of_toNat_eq (by simp)

variable {P : RfcHash}

/-- `h` in the frame. -/
abbrev hOf (P : RfcHash) (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (96 + (cfgOf P).fHo)) P.Q

/-- The length of the message. -/
abbrev mlen (P : RfcHash) (full : Bool) : Nat := if full then 1 + 2 * P.Q else 1

/-- Where `h` is in the frame: `fH`, or `X`'s place if `big`. -/
theorem fHo_le (P : RfcHash) : 232 ≤ (cfgOf P).fHo ∧ (cfgOf P).fHo + P.Q ≤ 376 := by
  have := P.sizes
  simp only [Cfg.fHo, cfgOf]
  rcases Bool.eq_false_or_eq_true P.R.big with h | h <;>
    simp only [h, fX, fH, ite_true, ite_false, Bool.false_eq_true] <;> nums

/-- The message `b` (`‖ d ‖ h` if `full`, `Q` bytes each) at `scratch + 2256`. -/
theorem msg_ok (hL : L.Ok) (hq : L.q = P.Q) {t : State} (hc : Ctx L g lr m₀ t)
    (h11 : t.gpr .r11 = L.B + BitVec.ofNat 64 96) (h9 : t.gpr .r9 = L.scr) (h10 : t.gpr .r10 = L.d)
    {b : Nat} (hb : b < 2 ^ 15) (full : Bool) :
    WP isa (.block ((cfgOf P).msg b full)) t fun t' => Ctx L g lr m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (mlen P full) =
        [BitVec.ofNat 8 b] ++ (if full then Spec.Sha256.bytesAt t.mem L.d P.Q ++ hOf P L t.mem else []) := by
  have hnB := hL.nB
  have hnc := hL.nc
  have hnd := hL.nd
  have hQ := P.sizes
  have hho := fHo_le P
  have hlen : (cfgOf P).len = P.Q := rfl
  refine WP.of_syms ?_
  simp only [Cfg.msg, List.cons_append, List.nil_append]
  -- The byte.
  refine stepLi hb fun t₃ k₃ m₃ v₃ => ?_
  refine stepStb (a := L.scr + BitVec.ofNat 64 2256) (by decide) (by decide)
    (by rw [k₃.gpr _ (by decide), h9]; rfl) (by rw [k₃.wr]; exact hc.inScrW (by omega))
    fun t₄ k₄ g₄ m₄ => ?_
  have hb₄ : Spec.Sha256.bytesAt t₄.mem (L.scr + BitVec.ofNat 64 2256) 1 = [BitVec.ofNat 8 b] := by
    rw [m₄, bytesAt_byte, v₃]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd _ (by decide)
  have f₄ : Frame [⟨L.scr + BitVec.ofNat 64 2256, 1⟩] t.mem t₄.mem := by
    rw [m₄, m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have K₄ : Kp [.r8] t t₄ := k₃.trans k₄.mono
  have keep : ∀ {u u' : State} {o n o' n' : Nat}, Frame [⟨L.scr + BitVec.ofNat 64 o', n'⟩] u.mem u'.mem →
      o + n ≤ o' ∨ o' + n' ≤ o → o' + n' ≤ 8192 → o + n ≤ 8192 →
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 o) n = Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 o) n :=
    fun f h h₁ h₂ => bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ h (by omega) (by omega)) (by omega)
  have keepS : ∀ {u u' : State} {p : Addr} {n o' n' : Nat}, Frame [⟨L.scr + BitVec.ofNat 64 o', n'⟩] u.mem u'.mem →
      Region.Disjoint ⟨p, n⟩ ⟨L.scr + BitVec.ofNat 64 o', n'⟩ → n ≤ 8192 →
      Spec.Sha256.bytesAt u'.mem p n = Spec.Sha256.bytesAt u.mem p n :=
    fun f h hn => bytesAt_frame f (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h) (by omega)
  have sub : ∀ {o n : Nat}, 2256 ≤ o → o + n ≤ 2256 + (1 + 2 * P.Q) →
      ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 o, n⟩ : Region)],
        ∃ r' ∈ [(⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩ : Region)], Region.Sub r r' :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ h₁ h₂⟩
  have safeM : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩ : Region)], Safe L r := by
    simp only [List.mem_singleton]; rintro r rfl; exact safe_scr L (by nums)
  cases full
  · simp only [Bool.false_eq_true, ite_false, mlen]
    refine wp_nil fun hsy => ⟨hc.keep hL K₄.rd K₄.wr K₄.sp (fun r hr => K₄.gpr r (by
        intro h; simp at h; subst h; simp [preserved] at hr)) (f₄.sub (sub (by omega) (by omega))) safeM hsy,
      f₄.sub (sub (by omega) (by omega)), hb₄⟩
  · simp only [ite_true, mlen]
    rw [WP.block_append_iff]
    -- `d`.
    refine WP.mono (copyN_ok (S := L.d) (D := L.scr) (so := 0) (d := sMsg + 1) (n := P.Q)
      (by decide) (by decide) (by decide) (by decide)
      (by
        rw [BitVec.add_zero]
        exact (hL.dc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by simp only [sMsg]; nums)))
      (by nums) (by simp only [sMsg]; nums) t₄
      (by rw [K₄.gpr _ (by decide), h10]) (by rw [K₄.gpr _ (by decide), h9])
      (fun j k hjk => by rw [K₄.rd, K₄.wr, Nat.zero_add]; exact hc.inD (by omega) (by nums))
      (fun j k hjk => by rw [K₄.wr]; exact hc.inScrW (by simp only [sMsg]; nums)))
      fun t₅ ⟨k₅, f₅, v₅⟩ => ?_
    -- `h`.
    refine WP.mono (copyN_ok (S := L.B + BitVec.ofNat 64 96) (D := L.scr) (so := (cfgOf P).fHo)
      (d := sMsg + 1 + P.Q) (n := P.Q) (by decide) (by decide) (by decide) (by decide)
      (by rw [fr_add]; exact hL.stk_scr (by omega) (by simp only [sMsg]; nums)) (by omega)
      (by simp only [sMsg]; nums) t₅
      (by rw [k₅.gpr _ (by decide), K₄.gpr _ (by decide), h11])
      (by rw [k₅.gpr _ (by decide), K₄.gpr _ (by decide), h9])
      (fun j k hjk => by rw [k₅.rd, k₅.wr, K₄.rd, K₄.wr, fr_add]; exact hc.inFr (by omega) (by omega))
      (fun j k hjk => by rw [k₅.wr, K₄.wr]; exact hc.inScrW (by simp only [sMsg]; nums)))
      fun t₆ ⟨k₆, f₆, v₆⟩ hsy => ?_
    simp only [sMsg] at f₅ v₅ f₆ v₆
    have F : Frame [⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩] t.mem t₆.mem :=
      ((f₄.sub (sub (by omega) (by omega))).trans (f₅.sub (sub (by omega) (by omega)))).trans
        (f₆.sub (sub (by omega) (by omega)))
    have K : Kp [.r8] t t₆ := (K₄.trans k₅).trans k₆
    refine ⟨hc.keep hL K.rd K.wr K.sp (fun r hr => K.gpr r (by
        intro h; simp at h; subst h; simp [preserved] at hr)) F safeM hsy, F, ?_⟩
    -- `d` and `h`, as on entry.
    have hd₄ : Spec.Sha256.bytesAt t₄.mem L.d P.Q = Spec.Sha256.bytesAt t.mem L.d P.Q :=
      keepS f₄ ((hL.dc.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by omega)))
        (by omega)
    have hh₅ : Spec.Sha256.bytesAt t₅.mem (L.B + BitVec.ofNat 64 (96 + (cfgOf P).fHo)) P.Q = hOf P L t.mem := by
      rw [keepS f₅ (hL.stk_scr (by omega) (by nums)) (by omega), keepS f₄ (hL.stk_scr (by omega) (by omega))
        (by omega)]
    rw [show 1 + 2 * P.Q = 1 + P.Q + P.Q by omega, bytesAt_add, bytesAt_add, Offset.add_add, Offset.add_add,
      keep (o := 2256) (n := 1) f₆ (by omega) (by nums) (by omega),
      keep (o := 2256) (n := 1) f₅ (by omega) (by nums) (by omega), hb₄,
      keep (o := 2256 + 1) (n := P.Q) f₆ (by omega) (by nums) (by nums), v₅, BitVec.add_zero, hd₄,
      show 2256 + (1 + P.Q) = 2256 + 1 + P.Q by omega, v₆, fr_add, hh₅]
    rfl

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
