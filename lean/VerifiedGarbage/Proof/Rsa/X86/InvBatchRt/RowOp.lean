module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ops
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Row
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Weierstrass.X86.InvUnsigned
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob

/-! # Product rows at `Ref`s

`mulRow_ok`: `mulRow` at `Ref`s, `n + e` words of the source; `rowAdd_ok` with
its multiplier from a header word; `linearUnsigned_ok`: `InvMemory.linearUnsigned`'s
sum of two unsigned products, the first row written and the second added.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- `mulRow set acc src (nBytes .esi e)`: `[acc] = ecx · [src]` (`set`) or `[acc] += ecx · [src]`,
over `n + e` words of the source and `n + e + 2` of the accumulator. -/
theorem mulRow_gen {set : Bool} {s : State} (h : Bx L s B Z len N) {acc src : Ref} {e : Nat} (he : e ≤ 4)
    (hsh : src.half = 0)
    (haz : rv (kw len) acc + 4 * (nw len + e + 2) ≤ Z) (hsz : rv (kw len) src + 4 * (nw len + e) ≤ Z)
    (sep : rv (kw len) src + 4 * (nw len + e) ≤ rv (kw len) acc ∨
      rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) src) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.mulRow L set acc src (nBytes .esi e)) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) acc) (4 * (nw len + e + 2)) s.mem t.mem ∧
      ((set = false → val32 s.mem B (rv (kw len) acc) (nw len + e + 2) +
        (s.gpr .ecx).toNat * val32 s.mem B (rv (kw len) src) (nw len + e) < 2 ^ (32 * (nw len + e + 2))) →
      val32 t.mem B (rv (kw len) acc) (nw len + e + 2) =
        (if set then 0 else val32 s.mem B (rv (kw len) acc) (nw len + e + 2)) +
          (s.gpr .ecx).toNat * val32 s.mem B (rv (kw len) src) (nw len + e)) ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := by
  have hn := h.nowrap
  have hw := kw_bound h.ws.lenLe
  have hpos := h.ws.kw_pos
  have ke := kw_eq len
  have hZ := h.halfZ
  unfold VG.Impl.Rsa.X86.InvBatchRt.mulRow
  simp only [List.append_assoc]
  -- The pointers, the count, no carry.
  refine WP.seq (ptr_ok h.ws h.slots hZ (by decide) (by decide) (by decide) (by decide) (by intro e; cases e)
    (by omega) fun u₁ K₁ m₁ p₁ => ?_)
  have h₁ : Bx L u₁ B Z len N := h.keep K₁ (by decide) (by decide) (by rw [m₁]; exact Outside.refl _ _ _ _)
    (rv_ge _ acc) haz
  refine nBytes_ok h₁.ws.ws.workspace h₁.slots hZ (by omega) he fun u₂ K₂ m₂ c₂ => ?_
  have h₂ : Bx L u₂ B Z len N := h₁.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
    (rv_ge _ acc) haz
  refine ptr_ok h₂.ws h₂.slots hZ (by decide) (by decide) (by decide) (by decide) (fun _ => hsh)
    (by omega) fun u₃ K₃ m₃ p₃ => wp_movS rfl fun u U _ => WP.block_nil ?_
  have K : Keeps [.ebx, .edx, .ebp, .edi, .esi] s u :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans (U.keeps.mono (by decide))
  have m : u.mem = s.mem := by rw [U.mem, m₃, m₂, m₁]
  have ecx : u.gpr .ecx = s.gpr .ecx := K.1 _ (by decide)
  have hwu := h.ws.rt.of_keeps K
  -- The loop.
  refine WP.seq (WP.mono (rowLoop_ok (set := set) hwu (N := nw len + e) (x := rv (kw len) src)
    (y := rv (kw len) acc) (by omega) hsz haz sep
    (by rw [PtrAt, U.other _ (by decide)]; exact p₃)
    (by rw [PtrAt, U.other _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁)
    (by rw [U.other _ (by decide), K₃.1 _ (by decide), c₂]; omega) U.gpr) fun t R => ?_)
  -- The tail, and `edi` back.
  have post : ∀ v, Keeps [.eax] t v → Outside B (rv (kw len) acc) (4 * (nw len + e + 2)) u.mem v.mem →
      ((set = false → val32 u.mem B (rv (kw len) acc) (nw len + e + 2) +
        (u.gpr .ecx).toNat * val32 u.mem B (rv (kw len) src) (nw len + e) < 2 ^ (32 * (nw len + e + 2))) →
      val32 v.mem B (rv (kw len) acc) (nw len + e + 2) =
        (if set then 0 else val32 u.mem B (rv (kw len) acc) (nw len + e + 2)) +
          (u.gpr .ecx).toNat * val32 u.mem B (rv (kw len) src) (nw len + e)) →
      WP isa (.block (restoreEdi L)) v fun t =>
        Bx L t B Z len N ∧ Outside B (rv (kw len) acc) (4 * (nw len + e + 2)) s.mem t.mem ∧
        ((set = false → val32 s.mem B (rv (kw len) acc) (nw len + e + 2) +
          (s.gpr .ecx).toNat * val32 s.mem B (rv (kw len) src) (nw len + e) < 2 ^ (32 * (nw len + e + 2))) →
        val32 t.mem B (rv (kw len) acc) (nw len + e + 2) =
          (if set then 0 else val32 s.mem B (rv (kw len) acc) (nw len + e + 2)) +
            (s.gpr .ecx).toNat * val32 s.mem B (rv (kw len) src) (nw len + e)) ∧
        Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := by
    intro v Kv O V
    rw [m] at O V
    rw [ecx] at V
    have KK : Keeps [.eax, .ebx, .edx, .ebp, .esi, .edi] s v :=
      ((K.mono (by decide)).trans (R.keep.mono (by decide))).trans (Kv.mono (by decide))
    have O0 : Outside B 0 Z s.mem v.mem := O.mono (Nat.zero_le _) (by omega)
    unfold restoreEdi
    refine wp_movS (h.ws.wsArg.keep KK (by decide) O0).readSrc fun t₁ U₁ _ => WP.block_nil ?_
    have K' : Keeps [.eax, .ebx, .edx, .ebp, .esi] s t₁ :=
      VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp, .esi])
        (KK.trans (U₁.keeps.mono (by decide))) (U₁.gpr.trans (RtWs.edi_eq h.ws).symm)
    exact ⟨h.keep K' (by decide) (by decide) (by rw [U₁.mem]; exact O) (rv_ge _ acc) haz,
      by rw [U₁.mem]; exact O, by rw [U₁.mem]; exact V, K'⟩
  cases set
  · refine tailAdd_ok hwu haz R fun v Kv O V => ?_
    exact post v Kv O fun hlt => by simpa only [Bool.false_eq_true, ite_false] using V (hlt rfl)
  · refine tailSet_ok hwu haz R fun v Kv O V => ?_
    exact post v Kv O fun _ => by simpa only [ite_true, Nat.zero_add] using V

theorem mulRow_ok {set : Bool} {s : State} (h : Bx L s B Z len N) {acc src : Ref} {e : Nat} (he : e ≤ 4)
    (hsh : src.half = 0)
    (haz : rv (kw len) acc + 4 * (nw len + e + 2) ≤ Z) (hsz : rv (kw len) src + 4 * (nw len + e) ≤ Z)
    (sep : rv (kw len) src + 4 * (nw len + e) ≤ rv (kw len) acc ∨
      rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) src)
    (hlt : set = false → val32 s.mem B (rv (kw len) acc) (nw len + e + 2) +
      (s.gpr .ecx).toNat * val32 s.mem B (rv (kw len) src) (nw len + e) < 2 ^ (32 * (nw len + e + 2))) :
    WP isa (VG.Impl.Rsa.X86.InvBatchRt.mulRow L set acc src (nBytes .esi e)) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) acc) (4 * (nw len + e + 2)) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) acc) (nw len + e + 2) =
        (if set then 0 else val32 s.mem B (rv (kw len) acc) (nw len + e + 2)) +
          (s.gpr .ecx).toNat * val32 s.mem B (rv (kw len) src) (nw len + e) ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi] s t :=
  WP.mono (mulRow_gen h he hsh haz hsz sep) fun _ ⟨H, O, V, K⟩ => ⟨H, O, V hlt, K⟩

/-- `rowAdd set c acc src (nBytes .esi e)`: the row with the multiplier the header word `c`. -/
theorem rowAdd_ok {set : Bool} {s : State} (h : Bx L s B Z len N) {c : Nat} (hc : c + 4 ≤ 160)
    {acc src : Ref} {e : Nat} (he : e ≤ 4) (hsh : src.half = 0)
    (haz : rv (kw len) acc + 4 * (nw len + e + 2) ≤ Z) (hsz : rv (kw len) src + 4 * (nw len + e) ≤ Z)
    (sep : rv (kw len) src + 4 * (nw len + e) ≤ rv (kw len) acc ∨
      rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) src)
    (hlt : set = false → val32 s.mem B (rv (kw len) acc) (nw len + e + 2) +
      w32 s.mem B c * val32 s.mem B (rv (kw len) src) (nw len + e) < 2 ^ (32 * (nw len + e + 2))) :
    WP isa (rowAdd L set c acc src (nBytes .esi e)) s fun t =>
      Bx L t B Z len N ∧ Outside B (rv (kw len) acc) (4 * (nw len + e + 2)) s.mem t.mem ∧
      val32 t.mem B (rv (kw len) acc) (nw len + e + 2) =
        (if set then 0 else val32 s.mem B (rv (kw len) acc) (nw len + e + 2)) +
          w32 s.mem B c * val32 s.mem B (rv (kw len) src) (nw len + e) ∧
      Keeps VG.Proof.Weierstrass.X86.Inv.wordClob s t := by
  have hZ := h.halfZ
  have ra := rv_ge (kw len) acc
  unfold rowAdd
  refine WP.seq (wp_movS (readSrc_sc h.ws.ws.workspace (d := c) (by omega)) fun u U _ => WP.block_nil ?_)
  have hu : Bx L u B Z len N := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)
    (rv_ge _ acc) haz
  have ecx : (u.gpr .ecx).toNat = w32 s.mem B c := by rw [U.gpr]
  refine WP.mono (mulRow_ok hu he hsh haz hsz sep (by rw [U.mem, ecx]; exact hlt)) fun t ⟨H, O, V, K⟩ =>
    ⟨H, by rw [U.mem] at O; exact O, by rw [V, U.mem, ecx], (U.keeps.mono (by decide)).trans (K.mono (by decide))⟩

/-- `linearUnsigned u v acc a b (nBytes .esi e)`: `[acc] = [u] [a] + [v] [b]`, `n + e` words of each
input, as unsigned products, over `n + e + 2` words. -/
theorem linearUnsigned_ok {s : State} (h : Bx L s B Z len N) {u v : Nat} (hu : u + 4 ≤ 160) (hv : v + 4 ≤ 160)
    {acc a b : Ref} {e : Nat} (he : e ≤ 4) (hah : a.half = 0) (hbh : b.half = 0)
    (haccz : rv (kw len) acc + 4 * (nw len + e + 2) ≤ Z)
    (haz : rv (kw len) a + 4 * (nw len + e) ≤ Z) (hbz : rv (kw len) b + 4 * (nw len + e) ≤ Z)
    (sa : rv (kw len) a + 4 * (nw len + e) ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) a)
    (sb : rv (kw len) b + 4 * (nw len + e) ≤ rv (kw len) acc ∨ rv (kw len) acc + 4 * (nw len + e + 2) ≤ rv (kw len) b) :
    WP isa (linearUnsigned L u v acc a b (nBytes .esi e)) s fun z =>
      Bx L z B Z len N ∧ Outside B (rv (kw len) acc) (4 * (nw len + e + 2)) s.mem z.mem ∧
      val32 z.mem B (rv (kw len) acc) (nw len + e + 2) =
        w32 s.mem B u * val32 s.mem B (rv (kw len) a) (nw len + e) +
          w32 s.mem B v * val32 s.mem B (rv (kw len) b) (nw len + e) ∧
      Keeps VG.Proof.Weierstrass.X86.Inv.wordClob s z := by
  have hn := h.nowrap
  have ra := rv_ge (kw len) acc
  unfold linearUnsigned
  refine WP.seq (WP.mono (rowAdd_ok (set := true) h hu he hah haccz haz sa (fun e => nomatch e))
    fun s₁ ⟨H₁, O₁, V₁, K₁⟩ => ?_)
  simp only [ite_true, Nat.zero_add] at V₁
  have U₁ : w32 s₁.mem B v = w32 s.mem B v := O₁.w32 (.inl (by omega)) (by omega)
  have B₁ : val32 s₁.mem B (rv (kw len) b) (nw len + e) = val32 s.mem B (rv (kw len) b) (nw len + e) :=
    O₁.val32 sb (by omega)
  have bound := VG.Proof.Weierstrass.X86.Inv.products_bound s.mem B u v (rv (kw len) a) (rv (kw len) b) (nw len + e)
  refine WP.mono (rowAdd_ok (set := false) H₁ hv he hbh haccz hbz sb (fun _ => by rw [V₁, U₁, B₁]; exact bound))
    fun z ⟨H, O, V, K⟩ => ⟨H, O₁.trans O, ?_, K₁.trans K⟩
  simp only [Bool.false_eq_true, ite_false] at V
  rw [V, V₁, U₁, B₁]

end VG.Proof.Rsa.X86.InvBatchRt
