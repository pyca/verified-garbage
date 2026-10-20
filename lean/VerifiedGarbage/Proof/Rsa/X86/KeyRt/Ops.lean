module

public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.X86.WordOps

/-! # The key workspace's operations at a run-time width: differences and selections

`sub3_ok`, `copy_ok` and `sel_ok` state what `Keys`' per-width lemmas do, for
the run-time width's code, on `RtWs`: a difference with its borrow in `ebx`,
and selections of whole arrays (`selectIn_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.KeyRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S arr_mono arr_end arr_disj)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem kk_false (len : Nat) : kk len false = kw len := rfl

/-- `[o] = [a] - [b]`, `w` words, and `ebx` the borrow. -/
theorem sub3_ok {s : State} (h : RtWs L s B Z len N) {o a b : Nat} (ho : o < N) (ha : a < N) (hb : b < N) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.sub3 L o a b) s fun t =>
      RtWs L t B Z len N ∧ Keep B (kw len) [o] [] s.mem t.mem ∧
      num t.mem B (kw len) o + num s.mem B (kw len) b =
        num s.mem B (kw len) a + 2 ^ (32 * kw len) * (t.gpr .ebx).toNat ∧
      (t.gpr .ebx).toNat ≤ 1 ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Rsa.X86.KeyRt.sub3
  refine WP.seq (WP.mono (chainSub_ok h ho ha hb false) fun u ⟨F, Kp, ⟨c, carry, value⟩, Ku⟩ => ?_)
  refine wp_movS rfl fun v V _ => ?_
  refine wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
  have r : Keeps [.ebx] u t := V.keeps.trans T.keeps
  have mem : t.mem = u.mem := T.mem.trans V.mem
  have bit : (t.gpr .ebx).toNat = c.toNat := by
    rw [T.gpr, V.gpr, carry, ite_eq_left rfl]
    cases c <;> rfl
  refine ⟨F.keep r (by decide) (by decide) (by rw [mem]; exact Outside.refl _ _ _ _), by rw [mem]; exact Kp, ?_, ?_,
    Ku.trans (r.mono (by decide))⟩
  · rw [num, num, num, mem, bit]; exact value
  · rw [bit]; cases c <;> decide

/-- `[o] = [a]` where the mask `ecx` is all ones, else kept: `K` words, `o ≠ a`. -/
theorem selectIn_ok {s : State} (h : RtWs L s B Z len N) {o a : Nat} (ho : o < N) (ha : a < N) (hoa : o ≠ a)
    (extra : Bool) {k : Bool} (hk : s.gpr .ecx = cmask k) :
    WP isa (selectIn L o a extra) s fun t =>
      RtWs L t B Z len N ∧ Outside B (arr (kw len) o) (4 * kk len extra) s.mem t.mem ∧
      val32 t.mem B (arr (kw len) o) (kk len extra) =
        (if k then val32 s.mem B (arr (kw len) a) (kk len extra) else val32 s.mem B (arr (kw len) o) (kk len extra)) ∧
      Keeps [.eax, .ebx, .edx, .ebp] s t := by
  have hn := h.ws.workspace.nowrap
  have fa := h.ws.arr_fit ha
  have fo := h.ws.arr_fit ho
  have sep := arr_disj (w := kw len) hoa
  have hK : 4 * kk len extra ≤ 4 * (kw len + 2) := by
    have := Bool.toNat_le extra; simp only [kk]; omega
  simp only [S] at fa fo sep
  have hl := lenSrc h
  have hle := h.lenLe
  unfold selectIn
  rw [show count L .edi extra = count L .edi extra ++ [] from (List.append_nil _).symm]
  simp only [List.append_assoc]
  refine WP.seq (arrPtr_ok hl hle h.edi (by decide) (by decide) (by omega) fun u₁ K₁ m₁ p₁ _ => ?_)
  have hl₁ := (src_keep K₁ (by decide) m₁).trans hl
  have edi₁ : (u₁.gpr .edi).toNat = B.toNat := by rw [K₁.1 _ (by decide)]; exact h.edi
  refine arrPtr_ok hl₁ hle edi₁ (by decide) (by decide) (by omega) fun u₂ K₂ m₂ p₂ _ => ?_
  have hl₂ := (src_keep K₂ (by decide) m₂).trans hl₁
  refine count_ok hl₂ hle fun u K₃ m₃ c₃ => WP.block_nil ?_
  have K : Keeps [.ebx, .edx, .ebp, .edi] s u :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide)))
  have m : u.mem = s.mem := by rw [m₃, m₂, m₁]
  have ecx : u.gpr .ecx = cmask k := by rw [K.1 _ (by decide)]; exact hk
  refine WP.seq (WP.mono (VG.Proof.Bignum.X86.PublicRt.selectLoop_ok (h.rt.of_keeps K) (x := arr (kw len) a) (d := arr (kw len) o) (N := kk len extra) k
    (by have := h.kw_pos; simp only [kk]; omega) (by omega) (by omega) (by omega)
    (by rw [PtrAt, K₃.1 _ (by decide), K₂.1 _ (by decide)]; exact p₁)
    (by rw [PtrAt, K₃.1 _ (by decide)]; exact p₂) c₃ ecx) fun t ⟨O, V, _, Kt⟩ => ?_)
  rw [m] at O V
  have KK : Keeps [.eax, .ebx, .edx, .ebp, .edi] s t := (K.mono (by decide)).trans Kt
  have O0 : Outside B 0 Z s.mem t.mem := O.mono (Nat.zero_le _) (by omega)
  unfold restoreEdi
  refine wp_movS (h.wsArg.keep KK (by decide) O0).readSrc fun t₁ U _ => WP.block_nil ?_
  have K' : Keeps [.eax, .ebx, .edx, .ebp] s t₁ :=
    VG.Proof.Bignum.X86.PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .edx, .ebp])
      (KK.trans (U.keeps.mono (by decide))) (U.gpr.trans (RtWs.edi_eq h).symm)
  exact ⟨h.keep K' (by decide) (by decide) (by rw [U.mem]; exact O0), by rw [U.mem]; exact O,
    by rw [U.mem]; exact V, K'⟩

/-- `[o] = [a]`, `w` words. -/
theorem copy_ok {s : State} (h : RtWs L s B Z len N) {o a : Nat} (ho : o < N) (ha : a < N) (hoa : o ≠ a) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.copy L o a) s fun t => RtWs L t B Z len N ∧ Keep B (kw len) [o] [] s.mem t.mem ∧
      num t.mem B (kw len) o = num s.mem B (kw len) a ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      w32 t.mem B (arr (kw len) o + 4 * kw len) =
        w32 s.mem B (arr (kw len) o + 4 * kw len) := by
  have fo := h.ws.arr_fit ho
  simp only [S] at fo
  unfold VG.Impl.Rsa.X86.KeyRt.copy
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  have hu := h.keep U.keeps (by decide) (by decide) (by rw [U.mem]; exact Outside.refl _ _ _ _)
  refine WP.mono (selectIn_ok hu ho ha hoa false (k := true) U.gpr) fun t ⟨F, O, V, K⟩ => ?_
  rw [U.mem] at O V
  refine ⟨F, Keep.of_arr (d := 0) (by simpa using O) (by simp only [S, kk_false]; omega) (by simp), ?_,
    (U.keeps.mono (by decide)).trans (K.mono (by decide)), ?_⟩
  · simp only [num, ite_true, kk_false] at V ⊢; exact V
  · exact O.w32 (by simp only [kk_false]; omega) (by have := h.ws.workspace.nowrap; omega)

open VG.Proof.Rsa.X86.Keys (slot) in
/-- The mask of a header word zero or one: all ones where it is one. -/
theorem mask_slot {s : State} (h : RtWs L s B Z len N) {sl : Nat} (hs : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr)
    (bit : slot s.mem B sl ≤ 1) :
    readSrc s (.mem (sc sl)) = some (BitVec.ofNat 32 (slot s.mem B sl)) ∧
      (0 - BitVec.ofNat 32 (slot s.mem B sl) = cmask (decide (slot s.mem B sl ≠ 0))) ∧
      (BitVec.ofNat 32 (slot s.mem B sl) - 1 = cmask (decide (slot s.mem B sl = 0))) := by
  have := h.ws.hdr_le
  refine ⟨by rw [readSrc_sc h.ws.workspace (by omega)]; simp [slot, w32], ?_⟩
  rcases (show slot s.mem B sl = 0 ∨ slot s.mem B sl = 1 by omega) with e | e <;> rw [e] <;> decide

open VG.Proof.Rsa.X86.Keys (slot) in
/-- `[o]` set to `[b]` where the header word `sl` is one, else kept. -/
theorem maskSel_ok {s : State} (h : RtWs L s B Z len N) {o b sl : Nat} (ho : o < N) (hb : b < N) (hob : o ≠ b)
    (hs : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (bit : slot s.mem B sl ≤ 1) :
    WP isa (.seq (.block [.mov .ecx (.imm 0), .alu .sub .ecx (.mem (sc sl))]) (selectIn L o b false)) s fun t =>
      RtWs L t B Z len N ∧ Keep B (kw len) [o] [] s.mem t.mem ∧
      num t.mem B (kw len) o = (if slot s.mem B sl = 0 then num s.mem B (kw len) o else num s.mem B (kw len) b) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have fo := h.ws.arr_fit ho
  simp only [S] at fo
  obtain ⟨rd, m0, _⟩ := mask_slot h hs bit
  refine WP.seq (wp_movS rfl fun u U _ => ?_)
  have rd' : readSrc u (.mem (sc sl)) = some (BitVec.ofNat 32 (slot s.mem B sl)) := by
    rw [← rd]; exact src_keep' U.keeps U.mem
  refine wp_subS rd' fun v V _ => WP.block_nil ?_
  have K : Keeps [.ecx] s v := U.keeps.trans V.keeps
  have mv : v.mem = s.mem := V.mem.trans U.mem
  have hv := h.keep K (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _)
  have mask : v.gpr .ecx = cmask (decide (slot s.mem B sl ≠ 0)) := by rw [V.gpr, U.gpr]; exact m0
  refine WP.mono (selectIn_ok hv ho hb hob false mask) fun t ⟨F, O, V', Kt⟩ => ?_
  rw [mv] at O V'
  refine ⟨F, Keep.of_arr (d := 0) (by simpa using O) (by simp only [S, kk_false]; omega) (by simp), ?_,
    (K.mono (by decide)).trans (Kt.mono (by decide))⟩
  simp only [num, kk_false] at V' ⊢
  rw [V']
  by_cases e : slot s.mem B sl = 0 <;> simp [e]

open VG.Proof.Rsa.X86.Keys (slot) in
/-- `[o] = [b]` if the header word `sl` is one, else `[a]`, for `o` apart from `a` or `b`. -/
theorem sel_ok {s : State} (h : RtWs L s B Z len N) {o a b sl : Nat} (ho : o < N) (ha : a < N) (hb : b < N)
    (hs : sl + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (bit : slot s.mem B sl ≤ 1) (hab : o ≠ a ∨ o ≠ b) :
    WP isa (VG.Impl.Rsa.X86.KeyRt.sel L o a b sl) s fun t =>
      RtWs L t B Z len N ∧ Keep B (kw len) [o] [] s.mem t.mem ∧
      num t.mem B (kw len) o = (if slot s.mem B sl = 0 then num s.mem B (kw len) a else num s.mem B (kw len) b) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have fo := h.ws.arr_fit ho
  simp only [S] at fo
  unfold VG.Impl.Rsa.X86.KeyRt.sel
  by_cases hob : o = b
  · subst hob
    have hoa : o ≠ a := hab.resolve_right (fun e => e rfl)
    rw [ite_eq_left rfl]
    obtain ⟨rd, _, m1⟩ := mask_slot h hs bit
    refine WP.seq (wp_movS rd fun u U _ => wp_subS rfl fun v V _ => WP.block_nil ?_)
    have K : Keeps [.ecx] s v := U.keeps.trans V.keeps
    have mv : v.mem = s.mem := V.mem.trans U.mem
    have hv := h.keep K (by decide) (by decide) (by rw [mv]; exact Outside.refl _ _ _ _)
    have mask : v.gpr .ecx = cmask (decide (slot s.mem B sl = 0)) := by rw [V.gpr, U.gpr]; exact m1
    refine WP.mono (selectIn_ok hv ho ha hoa false mask) fun t ⟨F, O, V', Kt⟩ => ?_
    rw [mv] at O V'
    refine ⟨F, Keep.of_arr (d := 0) (by simpa using O) (by simp only [S, kk_false]; omega) (by simp), ?_,
      (K.mono (by decide)).trans (Kt.mono (by decide))⟩
    simp only [num, kk_false] at V' ⊢
    rw [V']
    by_cases e : slot s.mem B sl = 0 <;> simp [e]
  · rw [ite_eq_right hob]
    by_cases hoa : o = a
    · subst hoa
      rw [ite_eq_left rfl]
      refine WP.seq (WP.block_nil ?_)
      exact maskSel_ok h ho hb hob hs bit
    · rw [ite_eq_right hoa]
      refine WP.seq (WP.mono (copy_ok h ho ha hoa) fun u ⟨F, Kp, V, Ku, _⟩ => ?_)
      have hsl : slot u.mem B sl = slot s.mem B sl :=
        Kp.slot hs (by simp)
      refine WP.mono (maskSel_ok F ho hb hob hs (by rw [hsl]; exact bit)) fun t ⟨F', Kp', V', Kt⟩ => ?_
      refine ⟨F', Kp.trans Kp', ?_, Ku.trans Kt⟩
      rw [V', hsl, V]
      have nb : num u.mem B (kw len) b = num s.mem B (kw len) b := Kp.num (by simp; omega) (by simp)
        (h.ws.fit64 hb)
      rw [nb]

end VG.Proof.Rsa.X86.KeyRt
