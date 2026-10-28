module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ops
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega

/-! # Filling the header's slots

`slots_ok`: `slots` stores each cached array's address and `2 w`, establishing `Slots`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (arr)
open VG.Proof.Weierstrass

variable {L : Lay} {B : Addr} {Z len N : Nat} {is : List Instr} {Q : State → Prop}

theorem cached_idx : ∀ j ∈ cached, cached.idxOf j < 11 := by decide

theorem cached_inj : ∀ j ∈ cached, ∀ j' ∈ cached, j ≠ j' → cached.idxOf j ≠ cached.idxOf j' := by decide

theorem cached_lt : ∀ j ∈ cached, j < 16 := by decide

theorem slot_some {j d : Nat} (h : slot j = some d) : j ∈ cached ∧ d = slotBase + 4 * cached.idxOf j := by
  simp only [slot, Option.map_eq_some_iff] at h
  obtain ⟨i, hi, rfl⟩ := h
  obtain ⟨hlt, hget, _⟩ := List.idxOf?_eq_some_iff.mp hi
  have hm : j ∈ cached := hget ▸ List.getElem_mem hlt
  refine ⟨hm, ?_⟩
  have T : ∀ j ∈ cached, cached.idxOf? j = some (cached.idxOf j) := by decide
  rw [Option.some.inj ((T j hm).symm.trans hi)]

/-- The slot words of a list of arrays. -/
def slotWords (l : List Nat) : List (Nat × Nat) := l.map fun j => (slotBase + 4 * cached.idxOf j, 4)

/-- The slot stores of a list of cached arrays without repeats. -/
theorem slotList_ok (hroom : 16 ≤ N) (l : List Nat) (hl : l.Nodup) (hc : ∀ j ∈ l, j ∈ cached) :
    ∀ {s : State}, RtWs L s B Z len N →
    (∀ u, RtWs L u B Z len N → Keeps [.eax, .edx] s u →
      (∀ j ∈ l, w32 u.mem B (slotBase + 4 * cached.idxOf j) =
        (B.toNat + VG.Impl.Rsa.X86.InvBatchRt.offset (kw len) j) % 2 ^ 32) →
      Unch B (slotWords l) s.mem u.mem → WP isa (.block is) u Q) →
    WP isa (.block (l.flatMap (fun j => arrPtr L .eax j .edx ++
      ([.store (sc (slotBase + 4 * cached.idxOf j)) .eax] : List Instr)) ++ is)) s Q := by
  induction l with
  | nil =>
    intro s h k
    exact k s h (Keeps.refl _ _) (by simp) (Unch.refl _ _ _)
  | cons j l ih =>
    intro s h k
    obtain ⟨hjl, hl'⟩ := List.nodup_cons.mp hl
    have hjc := hc j (by simp)
    have hn := h.ws.workspace.nowrap
    have hf : VG.Impl.Rsa.X86.Keys.hdr + N * VG.Proof.Rsa.X86.Keys.S (kw len) ≤ Z := h.ws.fits
    rw [show VG.Impl.Rsa.X86.Keys.hdr = 160 from rfl] at hf
    have hw := kw_bound h.lenLe
    have hi := cached_idx j hjc
    have hj16 := cached_lt j hjc
    have e52 : slotBase = 52 := rfl
    have hjN : (j + 1) * VG.Proof.Rsa.X86.Keys.S (kw len) ≤ N * VG.Proof.Rsa.X86.Keys.S (kw len) :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at hjN
    have hS : 8 ≤ VG.Proof.Rsa.X86.Keys.S (kw len) := by show 8 ≤ 4 * (kw len + 2); omega
    have harr : arr (kw len) j < 2 ^ 32 := by
      show VG.Impl.Rsa.X86.Keys.hdr + j * VG.Proof.Rsa.X86.Keys.S (kw len) < 2 ^ 32
      rw [show VG.Impl.Rsa.X86.Keys.hdr = 160 from rfl]; omega
    simp only [List.flatMap_cons, List.append_assoc]
    refine arrPtr_ok (r := .eax) (t := .edx) (lenSrc h) h.lenLe h.edi (by decide) (by decide) harr
      fun u₁ K₁ m₁ p₁ _ => ?_
    simp only [List.cons_append, List.nil_append]
    have hs₁ := h.ws.workspace.of_keeps K₁ (by decide)
    refine wp_storeS (hs₁.ea (by omega)) (hs₁.write (d := slotBase + 4 * cached.idxOf j) (n := 4) (by omega))
      fun s₂ U₂ => ?_
    have O₂ : Outside B (slotBase + 4 * cached.idxOf j) 4 s.mem s₂.mem := by
      rw [U₂.mem, m₁]; exact writeW32_outside _ _ _ (by omega)
    have W₂ : w32 s₂.mem B (slotBase + 4 * cached.idxOf j) =
        (B.toNat + VG.Impl.Rsa.X86.InvBatchRt.offset (kw len) j) % 2 ^ 32 := by
      rw [U₂.mem, w32_write_self, offset_eq]; exact p₁
    have K₂ : Keeps [.eax, .edx] s s₂ := K₁.trans (U₂.keeps _)
    have h₂ : RtWs L s₂ B Z len N := h.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega))
    refine ih hl' (fun j' hj' => hc j' (by simp [hj'])) h₂ fun u hu Ku Vu Fu => k u hu (K₂.trans Ku) ?_ ?_
    · intro j' hj'
      rcases List.mem_cons.mp hj' with rfl | hj'
      · rw [VG.Proof.Weierstrass.X86.Inv.word_unch Fu (by
          intro w hw
          simp only [slotWords, List.mem_map] at hw
          obtain ⟨i, hil, rfl⟩ := hw
          have hne : j' ≠ i := fun e => hjl (e ▸ hil)
          have := cached_inj j' hjc i (hc i (by simp [hil])) hne
          simp only; omega) (by omega)]
        exact W₂
      · exact Vu j' hj'
    · intro x hx
      rw [Fu x fun w hw => hx w (by simp only [slotWords, List.map_cons, List.mem_cons]; exact .inr hw),
        O₂ x (hx (slotBase + 4 * cached.idxOf j, 4) (by simp [slotWords]))]

/-- `slots`: the cached arrays' addresses and `2 w` into the header. -/
theorem slots_ok {s : State} (h : RtWs L s B Z len N) (hroom : 16 ≤ N)
    (k : ∀ u, Bx L u B Z len N → Keeps [.eax, .edx] s u → Outside B slotBase 48 s.mem u.mem →
      WP isa (.block is) u Q) :
    WP isa (.block (slots L ++ is)) s Q := by
  have hn := h.ws.workspace.nowrap
  have hf : VG.Impl.Rsa.X86.Keys.hdr + N * VG.Proof.Rsa.X86.Keys.S (kw len) ≤ Z := h.ws.fits
  rw [show VG.Impl.Rsa.X86.Keys.hdr = 160 from rfl] at hf
  have hw := kw_bound h.lenLe
  have hpos := h.ws.wpos
  have e52 : slotBase = 52 := rfl
  have e96 : halfSlot = 96 := rfl
  unfold slots
  simp only [List.append_assoc]
  refine slotList_ok hroom cached (by decide) (fun _ h => h) h fun u₁ h₁ K₁ V₁ F₁ => ?_
  refine bytesB_ok (r := .eax) (lenSrc h₁) h₁.lenLe fun u₂ K₂ m₂ e₂ => ?_
  simp only [List.cons_append, List.nil_append]
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₃ U₃ => ?_
  have hs₃ := (h₁.ws.workspace.of_keeps K₂ (by decide)).of_keeps U₃.keeps (by decide)
  refine wp_storeS (hs₃.ea (by omega)) (hs₃.write (d := halfSlot) (n := 4) (by omega)) fun u U₄ => ?_
  have O₄ : Outside B halfSlot 4 u₁.mem u.mem := by
    rw [U₄.mem, U₃.mem, m₂]; exact writeW32_outside _ _ _ (by omega)
  have K : Keeps [.eax, .edx] s u :=
    ((K₁.trans (K₂.mono (by decide))).trans (U₃.keeps.mono (by decide))).trans (U₄.keeps _)
  have hu : RtWs L u B Z len N :=
    h₁.keep (((K₂.mono (by decide)).trans (U₃.keeps.mono (by decide))).trans (U₄.keeps _) : Keeps [.eax] u₁ u)
      (by decide) (by decide) (O₄.mono (Nat.zero_le _) (by omega))
  have F : Unch B (slotWords cached) s.mem u₁.mem := F₁
  refine k u ⟨hu, ⟨fun j d hd => ?_, ?_, by omega⟩, hroom⟩ K ?_
  · obtain ⟨hj, rfl⟩ := slot_some hd
    have hi := cached_idx j hj
    rw [O₄.w32 (by omega) (by omega)]
    exact V₁ j hj
  · rw [U₄.mem, w32_write_self, U₃.gpr, BitVec.toNat_ushiftRight, e₂]
    simp only [Nat.shiftRight_eq_div_pow]; omega
  · intro x hx
    rw [O₄ x (by omega), F x fun w hw => by
      simp only [slotWords, List.mem_map] at hw
      obtain ⟨i, hi, rfl⟩ := hw
      have := cached_idx i hi
      simp only; omega]

end VG.Proof.Rsa.X86.InvBatchRt
