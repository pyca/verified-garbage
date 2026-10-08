import VerifiedGarbage.Proof.AesGcm.X86.Gather.Fn
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.Taint

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86: constant time

Untrusted: everything here is checked by Lean. Two runs whose stack pointer,
arguments and descriptors agree (`gatherPub`) leak the same trace, related
piece by piece from given states (`Eq2`), as on ARMv7
(`Proof/AesGcm/Arm/Gather/CT.lean`): the frame's words and our arguments are
read and written at `esp`, the same in both runs (the taint analysis from
`esp`); the gathering loads the descriptors from where they are, and copies
each slice from and to the addresses they give, with branches on the number
of slices and their lengths (`copySlice_rel`, `gather_rel`, by the taint
analysis from the registers the correctness proof pins to the same values in
both runs); and the call is constant time by its callee's contract, whose
public arguments agree (`sealGather_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86.Gather

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.SealGather
open VG.Spec.Gcm (gathered gatheredLen)

/-! ## Relating two runs -/

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (VG.X86.taint.check (τr rs) c h).isSome = true) : RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := VG.X86.taint) _ (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact agree_regs hr) hc

/-- An empty block. -/
theorem rel_skip {σ₁ σ₂ : State} : RelCT isa (Eq2 σ₁ σ₂) (.block []) TT :=
  RelCT.nil fun _ _ _ => trivial

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (Eq2 σ₁ σ₂) t TT)
    (hf : b = false → RelCT isa (Eq2 σ₁ σ₂) e TT) : RelCT isa (Eq2 σ₁ σ₂) (.ite c t e) TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- Constant time, from related runs from every pair of states. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem alloc_eq {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) : a = allocated n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

/-- A frame that reserves stack, around a body whose runs leak the same. -/
theorem rel_alloc {n : Nat} {body : Prog isa} {σ₁ σ₂ : State}
    (hb : RelCT isa (Eq2 (allocated n σ₁) (allocated n σ₂)) body TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.frame (.alloc n) body (.free n)) TT := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨rfl, rfl⟩ := hp
  cases e₁ with
  | frame p₁ b₁ _ =>
    cases e₂ with
    | frame p₂ b₂ _ =>
      have ea := alloc_eq p₁
      have eb := alloc_eq p₂
      subst ea eb
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨rfl, rfl⟩ b₁ b₂
      refine ⟨?_, trivial⟩
      rw [ht]
      rfl

/-! ## Copying a slice -/

/-- `copySlice` in two runs copying the same slice: the branches are on its
length, the addresses are its and the descriptor's. -/
theorem copySlice_rel {σ₁ σ₂ : State} {A₀ S D : BitVec 32} {n : Nat} (h₁ : SlicePre σ₁ A₀ S D n)
    (h₂ : SlicePre σ₂ A₀ S D n) : RelCT isa (Eq2 σ₁ σ₂) copySlice TT := by
  have tw : ∃ h, (VG.X86.taint.check (τr [.edi, .edx, .ecx]) copyWords h).isSome = true :=
    ⟨_, by taint_decide⟩
  have tl : ∃ h, (VG.X86.taint.check (τr [.edi, .edx, .ecx]) copyLoop h).isSome = true :=
    ⟨_, by taint_decide⟩
  refine rel_seq (rel_taint [.esi] (by simp [h₁.esi, h₂.esi]) ⟨_, by taint_decide⟩)
    (wordsArg_wp h₁) (wordsArg_wp h₂) fun τ₁ τ₂ w₁ w₂ => ?_
  refine rel_seq (rel_ite w₁.zf w₂.zf (fun _ => rel_skip) fun _ =>
      rel_taint [.edi, .edx, .ecx] (by simp [w₁.edi, w₂.edi, w₁.edx, w₂.edx, w₁.ecx, w₂.ecx]) tw)
    (words_wp h₁ w₁) (words_wp h₂ w₂) fun v₁ v₂ x₁ x₂ => ?_
  refine rel_seq (rel_taint [.esi] (by simp [x₁.esi, x₂.esi]) ⟨_, by taint_decide⟩)
    (bytesArg_wp h₁ x₁) (bytesArg_wp h₂ x₂) fun b₁ b₂ y₁ y₂ => ?_
  exact rel_ite y₁.zf y₂.zf (fun _ => rel_skip) fun _ =>
    rel_taint [.edi, .edx, .ecx] (by simp [y₁.edi, y₂.edi, y₁.edx, y₂.edx, y₁.ecx, y₂.ecx]) tl

/-! ## Gathering -/

/-- The descriptors agree in two memories: so do the slices they list. -/
theorem desc_agree {m₁ m₂ : Mem} {Src : Addr} {cnt : Nat}
    (hd : ∀ j < cnt * 8, m₁ (Src + BitVec.ofNat 64 j) = m₂ (Src + BitVec.ofNat 64 j)) {i : Nat} (hi : i ≤ cnt) :
    ∀ a, (Sig.descRegion 32 Src i).Contains a 1 → m₁ a = m₂ a := by
  intro a ha
  simp only [Sig.descRegion, Region.Contains] at ha
  have e : Src + BitVec.ofNat 64 (a - Src).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [← e]
  exact hd _ (by have := Nat.mul_le_mul_right 8 hi; simp only [show 2 * (32 / 8) = 8 from rfl] at ha; omega)

section
variable {m₁ m₂ : Mem} {Src : BitVec 32} {cnt : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32)
  (hd : ∀ j < cnt * 8, m₁ (w64 Src + BitVec.ofNat 64 j) = m₂ (w64 Src + BitVec.ofNat 64 j))
include hd

omit hdw in
theorem gl_agree {i : Nat} (hi : i ≤ cnt) : gatheredLen 32 m₁ (w64 Src) i = gatheredLen 32 m₂ (w64 Src) i := by
  simp only [gatheredLen]
  rw [Sig.listed_congr 32 .u8 (w64 Src) i (desc_agree hd hi)]

omit hdw in
theorem desc_word {d : Nat} (h : d + 4 ≤ cnt * 8) :
    m₁.readW (w64 Src + BitVec.ofNat 64 d) 32 = m₂.readW (w64 Src + BitVec.ofNat 64 d) 32 :=
  Mem.readW_congr fun k hk => by
    rw [Offset.add_ofNat_add_ofNat]; exact hd _ (by simp at hk; omega)

include hdw

theorem sb_agree {i : Nat} (hi : i < cnt) : sb m₁ Src i = sb m₂ Src i := by
  simp only [sb]
  rw [← descA0 hdw hi]
  exact desc_word hd (by omega)

theorem sl_agree {i : Nat} (hi : i < cnt) : sl m₁ Src i = sl m₂ Src i := by
  simp only [sl]
  rw [← descA hdw hi 4 (by decide), Offset.add_ofNat_add_ofNat, desc_word hd (by omega)]

end

section
variable {t₁ t₂ : State} {Src Dst : BitVec 32} {cnt L : Nat}
  (hd : ∀ j < cnt * 8, t₁.mem (w64 Src + BitVec.ofNat 64 j) = t₂.mem (w64 Src + BitVec.ofNat 64 j))
  (h₁ : GatherPre t₁ Src Dst cnt L) (h₂ : GatherPre t₂ Src Dst cnt L)
include hd h₁ h₂

/-- One iteration of the loop, in two runs. -/
theorem body_rel {i : Nat} (hi : i < cnt) :
    RelCT isa (fun u₁ u₂ => GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i) (.seq copySlice (.block next))
      (fun u₁ u₂ => (GInv t₁ u₁ Src Dst cnt (i + 1) ∧ u₁.zf = some (decide (i + 1 = cnt))) ∧
        (GInv t₂ u₂ Src Dst cnt (i + 1) ∧ u₂.zf = some (decide (i + 1 = cnt)))) := by
  have hT : RelCT isa (fun u₁ u₂ => GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i)
      (.seq copySlice (.block next)) TT := by
    intro σ₁ σ₂ x₁ x₂ σ₁' σ₂' ⟨g₁, g₂⟩ e₁ e₂
    have p₁ := slicePre_of h₁ hi g₁
    have p₂ := slicePre_of h₂ hi g₂
    rw [← sb_agree h₁.dw hd hi, ← sl_agree h₁.dw hd hi, ← gl_agree hd (Nat.le_of_lt hi)] at p₂
    refine rel_seq (copySlice_rel p₁ p₂) (copySlice_wp σ₁ p₁) (copySlice_wp σ₂ p₂) (fun τ₁ τ₂ c₁ c₂ => ?_)
      σ₁ σ₂ x₁ x₂ σ₁' σ₂' ⟨rfl, rfl⟩ e₁ e₂
    refine rel_taint [.esi, .ebx] ?_ ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨by rw [c₁.2.2.gpr _ (by decide), c₂.2.2.gpr _ (by decide), g₁.esi, g₂.esi],
      by rw [c₁.2.2.gpr _ (by decide), c₂.2.2.gpr _ (by decide), g₁.ebx, g₂.ebx]⟩
  exact (hT.wp fun u₁ u₂ ⟨g₁, g₂⟩ => ⟨body_wp h₁ hi g₁, body_wp h₂ hi g₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- `gatherLoop`, in two runs. -/
theorem gatherLoop_rel (hpos : cnt ≠ 0) : RelCT isa (Eq2 t₁ t₂) gatherLoop TT := by
  refine (RelCT.loop (Q := TT) (fun n u₁ u₂ => ∃ i, n = cnt - i ∧ i < cnt ∧
      GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i) (fun n => ?_) (cnt - 0)).mono
    (fun a b ⟨ha, hb⟩ => by subst ha hb; exact ⟨0, rfl, by omega, GInv.init h₁, GInv.init h₂⟩) fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases hin : n = cnt - i ∧ i < cnt
  · obtain ⟨rfl, hi⟩ := hin
    refine (body_rel hd h₁ h₂ hi).mono (fun _ _ h => h.2.2) ?_
    rintro u₁ u₂ ⟨⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩
    have ev₁ : isa.eval .ne u₁ = some !decide (i + 1 = cnt) := by show u₁.zf.map (!·) = _; rw [z₁]; rfl
    have ev₂ : isa.eval .ne u₂ = some !decide (i + 1 = cnt) := by show u₂.zf.map (!·) = _; rw [z₂]; rfl
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
    rw [ev₁] at ht
    have : i + 1 < cnt := by simp at ht; omega
    exact ⟨cnt - (i + 1), by omega, i + 1, rfl, this, g₁, g₂⟩
  · exact RelCT.of_false fun _ _ h => hin ⟨h.1, h.2.1⟩

end

/-- `gather`, in two runs. -/
theorem gather_rel {e₁ e₂ : State} {Src Dst : BitVec 32} {cnt L : Nat}
    (hd : ∀ j < cnt * 8, e₁.mem (w64 Src + BitVec.ofNat 64 j) = e₂.mem (w64 Src + BitVec.ofNat 64 j))
    (h₁ : GatherPre e₁ Src Dst cnt L) (h₂ : GatherPre e₂ Src Dst cnt L) : RelCT isa (Eq2 e₁ e₂) gather TT := by
  obtain ⟨t₁, run₁, z₁, g₁, m₁, rd₁, wr₁⟩ := cmp_ok e₁ h₁.ebx h₁.hcnt
  obtain ⟨t₂, run₂, z₂, g₂, m₂, rd₂, wr₂⟩ := cmp_ok e₂ h₂.ebx h₂.hcnt
  refine rel_seq (rel_taint [.ebx] (by simp [h₁.ebx, h₂.ebx]) ⟨_, by taint_decide⟩)
    (WP.of_runBlock ⟨t₁, run₁, rfl⟩) (WP.of_runBlock ⟨t₂, run₂, rfl⟩) fun τ₁ τ₂ ht₁ ht₂ => ?_
  subst ht₁ ht₂
  refine rel_ite z₁ z₂ (fun _ => rel_skip) fun hf => ?_
  exact gatherLoop_rel (by rw [m₁, m₂]; exact hd) (h₁.of_eq g₁ m₁ rd₁ wr₁) (h₂.of_eq g₂ m₂ rd₂ wr₂)
    (by simpa using hf)

/-! ## The function -/

theorem sealGather_ct (F : SealFn) : ConstantTime isa gatherPre gatherPub (sealGather F.name F.code) := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨qsp, qa, hdesc⟩ := hq
  have a (i : Nat) (hi : i < 11) := qa i hi
  have hP : Pf σ₁ = Pf σ₂ := by simp only [Pf, qsp]
  refine rel_alloc ?_
  -- The entry.
  refine rel_seq (rel_taint [.esp] (by simp [hP]) ⟨_, by taint_decide⟩)
    (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← a 6 (by decide), ← a 7 (by decide), ← a 8 (by decide), ← a 9 (by decide)] at g₂
  have hd : ∀ j < Cnt σ₁ * 8,
      e₁.mem (w64 (Src σ₁) + BitVec.ofNat 64 j) = e₂.mem (w64 (Src σ₁) + BitVec.ofNat 64 j) := by
    intro j hj
    have hx : (dsR σ₁).Contains (w64 (Src σ₁) + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by have := h₁.ods; omega)
    have hx₂ : (dsR σ₂).Contains (w64 (Src σ₁) + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← a 6 (by decide), ← a 7 (by decide)]; exact hx
    rw [he₁.mem, he₂.mem, h₁.keepE h₁.bds.symm hx, h₂.keepE h₂.bds.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel hd g₁ g₂) (gathered_wp h₁ he₁) (gathered_wp h₂ he₂) fun u₁ u₂ hg₁ hg₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by
    simp only [rdC, kR, nR, aR, K, Nn, NL, Ad, AL, ← a 0 (by decide), ← a 2 (by decide), ← a 3 (by decide),
      ← a 4 (by decide), ← a 5 (by decide)]
  have hwr : wrC σ₂ = wrC σ₁ := by
    simp only [wrC, dR, tgR, Dst, L, Tg, Bs, ← a 8 (by decide), ← a 9 (by decide), ← a 10 (by decide), qsp]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hg₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hg₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨s0₁, s1₁, s2₁, s3₁, s4₁, s5₁, s6₁, s7₁, s8₁⟩ := hg₁.args h₁ (rdC σ₁) (wrC σ₁)
  obtain ⟨s0₂, s1₂, s2₂, s3₂, s4₂, s5₂, s6₂, s7₂, s8₂⟩ := hg₂.args h₂ (rdC σ₁) (wrC σ₁)
  refine rel_seq (RelCT.call F.verified.1 F.verified.2.1 (rdC σ₁) (wrC σ₁) fun x y ⟨hx, hy⟩ => by
      subst hx hy
      refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ⟨?_, fun i hi => ?_⟩, cv₁, cw₁, cv₂, cw₂,
        by rw [hg₁.esp, hg₂.esp, hP]⟩
      · simp only [State.withRegions_gpr, State.callEntry_esp, hg₁.esp, hg₂.esp, hP]
      · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [s0₁, s0₂]; exact a 0 (by decide)
        · rw [s1₁, s1₂]; exact a 1 (by decide)
        · rw [s2₁, s2₂]; exact a 2 (by decide)
        · rw [s3₁, s3₂]; exact a 3 (by decide)
        · rw [s4₁, s4₂]; exact a 4 (by decide)
        · rw [s5₁, s5₂]; exact a 5 (by decide)
        · rw [s6₁, s6₂]; exact a 8 (by decide)
        · rw [s7₁, s7₂]; exact a 9 (by decide)
        · rw [s8₁, s8₂]; exact a 10 (by decide))
    (called_wp F h₁ hg₁) (called_wp F h₂ hg₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- Our caller's registers back.
  exact rel_taint [.esp] (by simp [hz₁.esp, hz₂.esp, hP]) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.X86.Gather
