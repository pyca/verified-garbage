module
public import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.State

import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Prepare
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Finishing (x86)

`finish` zeros `out` unless a key was derived, clears the scalar, writes
the consumed bytes to `used`, and restores the callee-saved registers.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

/-- Registers but `esp` and memory where the body may write change. -/
theorem Ready.congrW {s₀ t u : State} {rs : List Reg} {ws : List Region} (h : Ready s₀ t) (hk : Keeps rs t u)
    (hm : Frame ws t.mem u.mem) (hws : ∀ r ∈ ws, r ∈ rWrites s₀) (hsp : .esp ∉ rs := by decide) : Ready s₀ u :=
  ⟨h.rf.of_keeps hk hsp, hk.2.1.trans h.rd, hk.2.2.trans h.wr, h.frame.trans (hm.mono hws)⟩

/-- The output, after `k` of its bytes are zeroed. -/
structure ZeroInv (s₀ t₀ : State) (k : Nat) (t : State) : Prop where
  ready : Ready s₀ t
  esi : t.gpr .esi = X86.arg s₀ 0 + BitVec.ofNat 32 k
  ecx : t.gpr .ecx = BitVec.ofNat 32 ((X86.arg s₀ 1).toNat - k)
  eax : t.gpr .eax = 0
  frame : Frame [rOut s₀] t₀.mem t.mem
  zero : ∀ i < k, t.mem (argumentPointer s₀ 0 + BitVec.ofNat 64 i) = 0
  keeps : Keeps [.eax, .ecx, .esi] t₀ t

theorem zeroStep_ok {s₀ t₀ t : State} (A : KeyABI s₀) {k : Nat} (hk : k < (X86.arg s₀ 1).toNat)
    (I : ZeroInv s₀ t₀ k t) :
    WP isa (.block [.store8 (at_ .esi 0) .al, .alu .add .esi (.imm 1), .alu .sub .ecx (.imm 1)]) t
      fun u => ZeroInv s₀ t₀ (k + 1) u ∧ u.zf = some (decide ((X86.arg s₀ 1).toNat - (k + 1) = 0)) := by
  have hb := A.outBound
  have hp : t.ea (at_ .esi 0) = argumentPointer s₀ 0 + BitVec.ofNat 64 k := by
    rw [ea_at0, I.esi]; exact ptr_add (by omega)
  have hw : InRegions t.wr (argumentPointer s₀ 0 + BitVec.ofNat 64 k) 1 :=
    ⟨rOut s₀, by rw [I.ready.wr, A.wr]; simp [rOut], Offset.contains_base _ (by omega) (by omega)⟩
  refine wp_store8 hp hw fun u₁ m₁ => wp_addi fun u₂ v₂ => wp_subi fun u₃ v₃ _ z₃ => WP.block_nil ?_
  have hv : (t.gpr (Reg8.al).reg).setWidth 8 = 0 := by show (t.gpr .eax).setWidth 8 = 0; rw [I.eax]; rfl
  rw [hv] at m₁
  have kk : Keeps [.eax, .ecx, .esi] t u₃ :=
    ((m₁.keeps _).trans (v₂.keeps.mono (by decide))).trans (v₃.keeps.mono (by decide))
  have mem₃ : u₃.mem = t.mem.writeW (argumentPointer s₀ 0 + BitVec.ofNat 64 k) (0 : BitVec 8) := by
    rw [v₃.mem, v₂.mem, m₁.mem]
  have fr : Frame [rOut s₀] t.mem u₃.mem := by
    rw [mem₃]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))
  refine ⟨⟨I.ready.congrW kk fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites]),
    ?_, ?_, ?_, I.frame.trans fr, fun i hi => ?_, I.keeps.trans kk⟩, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, I.esi, Offset.add_ofNat_add_one]
  · rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr, I.ecx, ofNat_pred (by omega)]; rfl
  · rw [v₃.other _ (by decide), v₂.other _ (by decide), m₁.gpr, I.eax]
  · rw [mem₃]
    by_cases hik : i = k
    · subst hik; exact writeW8_self _ _ _
    · rw [writeW8_outside _ _ (d := k) _ (by omega) _ (by rw [ofs_off0 _ (by omega)]; omega)]
      exact I.zero i (by omega)
  · rw [z₃, v₂.other _ (by decide), m₁.gpr, I.ecx, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

theorem zeroOut_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    WP isa zeroOut t fun u => Ready s₀ u ∧ Frame [rOut s₀] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (argumentPointer s₀ 0) (X86.arg s₀ 1).toNat =
        List.replicate (X86.arg s₀ 1).toNat 0 ∧ Keeps [.eax, .ecx, .esi] t u := by
  have hL : 0 < (X86.arg s₀ 1).toNat := by
    have := A.outLength; have := A.lengths; unfold Spec.Dsa.lengthsValid at *; omega
  unfold zeroOut
  refine WP.seq (wp_movS (h.argSrc A (j := 0) (by decide)) fun t₁ u₁ _ => ?_)
  have h₁ := h.upd u₁ (by decide)
  refine wp_movS (h₁.argSrc A (j := 1) (by decide)) fun t₂ u₂ _ => wp_movS rfl fun t₃ u₃ _ => WP.block_nil ?_
  have k₃ : Keeps [.eax, .ecx, .esi] t t₃ :=
    ((u₁.keeps.mono (by decide)).trans (u₂.keeps.mono (by decide))).trans (u₃.keeps.mono (by decide))
  have m₃ : t₃.mem = t.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have I₀ : ZeroInv s₀ t 0 t₃ := ⟨h.congr k₃ (by rw [m₃]; exact Frame.refl _ _),
    by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, BitVec.add_zero],
    by rw [u₃.other _ (by decide), u₂.gpr, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    u₃.gpr, by rw [m₃]; exact Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _), k₃⟩
  refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ k, n = (X86.arg s₀ 1).toNat - k ∧
      k < (X86.arg s₀ 1).toNat ∧ ZeroInv s₀ t k u) (fun n u hu => ?_) _ t₃ ⟨0, rfl, hL, I₀⟩
  obtain ⟨k, rfl, hk, I⟩ := hu
  refine WP.mono (zeroStep_ok A hk I) fun v ⟨J, z⟩ => ?_
  by_cases he : (X86.arg s₀ 1).toNat - (k + 1) = 0
  · left
    refine ⟨by simp only [eval, z, he, decide_true, Option.map_some, Bool.not_true], J.ready, J.frame, ?_,
      J.keeps⟩
    apply List.ext_getElem
    · simp [Spec.Rsa.bytesAt]
    · intro i h₁ _
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h₁
      exact J.zero i (by omega)
  · right
    exact ⟨by simp only [eval, z, he, decide_false, Option.map_some, Bool.not_false], _, by omega,
      k + 1, rfl, by omega, J⟩

/-- A write apart from the stack keeps the frame's slots. -/
theorem apart_slot {s₀ : State} {m m' : Mem} {r : Region} (hf : Frame [r] m m') (hd : (rStack s₀).Disjoint r)
    {d : Nat} (hd' : d + 4 ≤ 120) : slot m' (rBase s₀) d = slot m (rBase s₀) d :=
  hf.readW (r := ⟨off (rBase s₀) d, 4⟩)
    (by have := Offset.contains_base (off (rBase s₀) d) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
        rwa [BitVec.add_zero] at this)
    (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      exact hd.sub_left (by rw [rBase_off]; exact stk_sub s₀ (by omega))) (by decide)

/-- After the attempts, ready to finish. -/
structure Fin (s₀ t : State) : Prop where
  ready : Ready s₀ t
  usedW : slot t.mem (rBase s₀) oUsed = BitVec.ofNat 32 (rResult s₀).used
  status : slot t.mem (rBase s₀) oStatus = BitVec.ofNat 32 (rResult s₀).status
  out : (rResult s₀).status = 1 → Spec.Rsa.bytesAt t.mem (argumentPointer s₀ 0) (X86.arg s₀ 1).toNat =
    (rResult s₀).key.getD (List.replicate (X86.arg s₀ 1).toNat 0)
  saved : Saved s₀ t.mem

/-- Clear the scalar, publish the consumption, restore the registers. -/
theorem finalBlock_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) (sv : Saved s₀ t.mem)
    {used st : BitVec 32} (hu : slot t.mem (rBase s₀) oUsed = used)
    (hs : slot t.mem (rBase s₀) oStatus = st) :
    WP isa (.block (clearNonce ++ ([.mov .edx (.mem (KeyRandom.arg aUsed)), .mov .eax (.mem (sp oUsed)),
        .store (at_ .edx 0) .eax, .mov .eax (.imm 0), .store (at_ .edx 4) .eax,
        .mov .ebx (.mem (sp oSaveEbx)), .mov .esi (.mem (sp oSaveEsi)),
        .mov .edi (.mem (sp oSaveEdi)), .mov .ebp (.mem (sp oSaveEbp)),
        .mov .eax (.mem (sp oStatus))] : List Instr))) t fun u =>
      Ready s₀ u ∧ u.gpr .eax = st ∧ u.gpr .ebx = s₀.gpr .ebx ∧ u.gpr .esi = s₀.gpr .esi ∧
      u.gpr .edi = s₀.gpr .edi ∧ u.gpr .ebp = s₀.gpr .ebp ∧ Frame [rStack s₀, rUsed s₀] t.mem u.mem ∧
      slot u.mem (argumentPointer s₀ 2) 0 = used ∧ slot u.mem (argumentPointer s₀ 2) 4 = 0 := by
  have hub := A.usedBound
  refine clearNonce_ok h.rf fun t₁ f₁ m₁ k₁ _ => ?_
  have fr₁ : Frame [rStack s₀] t.mem t₁.mem := by rw [m₁]; exact clearMem_frame s₀ _ 8 (by decide)
  have h₁ : Ready s₀ t₁ := h.congr k₁ fr₁
  have o₁ : Outs (rBase s₀) [(oNonce, 32)] t.mem t₁.mem := by
    rw [m₁]; exact Outs.of_outside (clearMem_outside _ _ 8 (by decide)) (List.mem_singleton_self _)
  have sl₁ : ∀ d, d + 4 ≤ oNonce → slot t₁.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd =>
    slot_outs o₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact .inl hd)
      (by unfold oNonce at hd; omega)
  refine wp_movS (h₁.argSrc A (j := 2) (by decide)) fun t₂ u₂ _ => ?_
  have h₂ := h₁.upd u₂ (by decide)
  have hu₁ : slot t₁.mem (rBase s₀) oUsed = used := (sl₁ _ (by decide)).trans hu
  refine wp_movS (v := used) (by rw [h₂.rf.readSlot (by decide), u₂.mem]; exact congrArg some hu₁)
    fun t₃ u₃ _ => ?_
  have h₃ := h₂.upd u₃ (by decide)
  have hU : (⟨argumentPointer s₀ 2, 8⟩ : Region) ∈ t₃.wr := by rw [h₃.wr, A.wr]; simp
  refine wp_storeS (a := argumentPointer s₀ 2)
    (by rw [ea_at0, u₃.other _ (by decide), u₂.gpr]) ⟨_, hU, by
      have := Offset.contains_base (argumentPointer s₀ 2) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
      rwa [BitVec.add_zero] at this⟩ fun t₄ m₄ => wp_movS rfl fun t₅ u₅ _ => ?_
  have e₅ : t₅.gpr .edx = X86.arg s₀ 2 := by rw [u₅.other _ (by decide), m₄.gpr, u₃.other _ (by decide), u₂.gpr]
  have hw₅ : InRegions t₅.wr (argumentPointer s₀ 2 + BitVec.ofNat 64 4) 4 :=
    ⟨_, by rw [u₅.wr, m₄.wr]; exact hU, Offset.contains_base _ (by decide) (by decide)⟩
  refine wp_storeS (a := argumentPointer s₀ 2 + BitVec.ofNat 64 4)
    (by show addr (t₅.gpr .edx) 4 = _; rw [e₅]; exact addr_eq (by omega)) hw₅ fun t₆ m₆ => ?_
  have mem₆ : t₆.mem = (t₃.mem.writeW (off (argumentPointer s₀ 2) 0) used).writeW
      (off (argumentPointer s₀ 2) 4) (0 : BitVec 32) := by
    rw [m₆.mem, u₅.gpr, u₅.mem, m₄.mem, u₃.gpr, off, BitVec.add_zero]
  have fu : Frame [rUsed s₀] t₃.mem t₆.mem := by
    rw [mem₆]
    exact (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide)
      (by decide))).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have ap : ∀ d, d + 4 ≤ 120 → slot t₆.mem (rBase s₀) d = slot t₃.mem (rBase s₀) d := fun d hd =>
    apart_slot fu A.stackUsed hd
  have k₆ : Keeps [.eax, .edx] t₁ t₆ :=
    ((((u₂.keeps.mono (by decide)).trans (u₃.keeps.mono (by decide))).trans (m₄.keeps _)).trans
      (u₅.keeps.mono (by decide))).trans (m₆.keeps _)
  have m₃ : t₃.mem = t₁.mem := by rw [u₃.mem, u₂.mem]
  have h₆ : Ready s₀ t₆ := h₁.congrW k₆ (by rw [← m₃]; exact fu)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp [rWrites])
  have sv₆ : Saved s₀ t₆.mem := sv.of_slots fun d h₁' hd => by
    rw [ap d (by omega), m₃, sl₁ d (by unfold oNonce; omega)]
  refine wp_movS (v := s₀.gpr .ebx) (by rw [h₆.rf.readSlot (by decide)]; exact congrArg some sv₆.1)
    fun t₇ u₇ _ => ?_
  have h₇ := h₆.upd u₇ (by decide)
  refine wp_movS (v := s₀.gpr .esi) (by rw [h₇.rf.readSlot (by decide), u₇.mem]; exact congrArg some sv₆.2.1)
    fun t₈ u₈ _ => ?_
  have h₈ := h₇.upd u₈ (by decide)
  refine wp_movS (v := s₀.gpr .edi)
    (by rw [h₈.rf.readSlot (by decide), u₈.mem, u₇.mem]; exact congrArg some sv₆.2.2.1) fun t₉ u₉ _ => ?_
  have h₉ := h₈.upd u₉ (by decide)
  refine wp_movS (v := s₀.gpr .ebp)
    (by rw [h₉.rf.readSlot (by decide), u₉.mem, u₈.mem, u₇.mem]; exact congrArg some sv₆.2.2.2)
    fun t₁₀ u₁₀ _ => ?_
  have h₁₀ := h₉.upd u₁₀ (by decide)
  have hst₆ : slot t₆.mem (rBase s₀) oStatus = st := by rw [ap _ (by decide), m₃, sl₁ _ (by decide), hs]
  refine wp_movS (v := st)
    (by rw [h₁₀.rf.readSlot (by decide), u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]; exact congrArg some hst₆)
    fun t₁₁ u₁₁ _ => WP.block_nil ?_
  have m₁₁ : t₁₁.mem = t₆.mem := by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  refine ⟨h₁₀.upd u₁₁ (by decide), u₁₁.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.gpr]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr]
  · rw [u₁₁.other _ (by decide), u₁₀.gpr]
  · rw [m₁₁]
    exact (fr₁.mono (by simp)).trans ((show Frame [rUsed s₀] t₁.mem t₆.mem by rw [← m₃]; exact fu).mono (by simp))
  · rw [m₁₁, mem₆, slot_write_ne _ _ _ (by decide) (by decide) (by decide), slot_write_self]
  · rw [m₁₁, mem₆, slot_write_self]

/-- What the callee returns, writes and publishes. -/
structure Finished (s₀ u : State) : Prop where
  ready : Ready s₀ u
  eax : u.gpr .eax = BitVec.ofNat 32 (rResult s₀).status
  ebx : u.gpr .ebx = s₀.gpr .ebx
  esi : u.gpr .esi = s₀.gpr .esi
  edi : u.gpr .edi = s₀.gpr .edi
  ebp : u.gpr .ebp = s₀.gpr .ebp
  out : Spec.Rsa.bytesAt u.mem (argumentPointer s₀ 0) (X86.arg s₀ 1).toNat =
    (rResult s₀).key.getD (List.replicate (X86.arg s₀ 1).toNat 0)
  usedLo : slot u.mem (argumentPointer s₀ 2) 0 = BitVec.ofNat 32 (rResult s₀).used
  usedHi : slot u.mem (argumentPointer s₀ 2) 4 = 0

theorem finish_ok {s₀ t : State} (A : KeyABI s₀) (F : Fin s₀ t) (hR : (rResult s₀).status ≤ 2)
    (hsig : (rResult s₀).status ≠ 1 → (rResult s₀).key = none) :
    WP isa finish t fun u => Finished s₀ u := by
  have h := F.ready
  have hb := A.outBound
  have hout : ∀ {m m' : Mem}, Frame [rStack s₀, rUsed s₀] m m' →
      Spec.Rsa.bytesAt m' (argumentPointer s₀ 0) (X86.arg s₀ 1).toNat =
        Spec.Rsa.bytesAt m (argumentPointer s₀ 0) (X86.arg s₀ 1).toNat := fun hf =>
    rBytes_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact A.stackOut.symm
      · exact A.outUsed) (by omega)
  unfold finish
  refine WP.seq (wp_movS (v := BitVec.ofNat 32 (rResult s₀).status)
    (by rw [h.rf.readSlot (by decide)]; exact congrArg some F.status)
    fun t₁ u₁ _ => wp_cmpi fun t₂ f₂ _ z₂ => WP.block_nil ?_)
  have h₂ := (h.upd u₁ (by decide)).fupd f₂
  have m₂ : t₂.mem = t.mem := by rw [f₂.mem, u₁.mem]
  rw [u₁.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)] at z₂
  have fin : ∀ v : State, Ready s₀ v → Saved s₀ v.mem →
      slot v.mem (rBase s₀) oUsed = BitVec.ofNat 32 (rResult s₀).used →
      slot v.mem (rBase s₀) oStatus = BitVec.ofNat 32 (rResult s₀).status →
      Spec.Rsa.bytesAt v.mem (argumentPointer s₀ 0) (X86.arg s₀ 1).toNat =
        (rResult s₀).key.getD (List.replicate (X86.arg s₀ 1).toNat 0) →
      WP isa (.block _) v fun u => Finished s₀ u := fun v hv sv hu hs ho =>
    WP.mono (finalBlock_ok A hv sv hu hs) fun u ⟨hu', e, b, si, di, bp, fr, lo, hi⟩ =>
      ⟨hu', e, b, si, di, bp, by rw [hout fr]; exact ho, lo, hi⟩
  by_cases h1 : (rResult s₀).status = 1
  · refine WP.seq (WP.ite false (by simp only [eval, z₂, h1, decide_true, Option.map_some, Bool.not_true])
      (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_))
    exact fin t₂ h₂ (by rw [m₂]; exact F.saved) (by rw [m₂]; exact F.usedW) (by rw [m₂]; exact F.status)
      (by rw [m₂]; exact F.out h1)
  · refine WP.seq (WP.ite true (by simp only [eval, z₂, h1, decide_false, Option.map_some, Bool.not_false])
      (fun _ => WP.mono (zeroOut_ok A h₂) fun v ⟨hv, fv, zv, _⟩ => ?_) (fun e => Bool.noConfusion e))
    have ap : ∀ d, d + 4 ≤ 120 → slot v.mem (rBase s₀) d = slot t.mem (rBase s₀) d := fun d hd => by
      rw [apart_slot fv A.stackOut hd, m₂]
    exact fin v hv (F.saved.of_slots fun d _ hd => ap d (by omega)) (by rw [ap _ (by decide)]; exact F.usedW)
      (by rw [ap _ (by decide)]; exact F.status) (by rw [zv, hsig h1]; rfl)

end VG.Proof.Dsa.X86.KeyRandom
