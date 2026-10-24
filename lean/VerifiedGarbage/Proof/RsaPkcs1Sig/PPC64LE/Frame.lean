module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Impl.RsaPkcs1Sig.PPC64LE.Frame
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PKCS1-v1_5 on PPC64LE: the frame

Untrusted: everything here is checked by Lean. The frame of
`vg_rsa_pkcs1_verify_precomputed` and `vg_rsa_pkcs1_recover_precomputed`
(`Impl/RsaPkcs1Sig/PPC64LE/Frame.lean`): it is all of the stack the function
uses, `kR`, from its base `fb`; the push makes its local variable space `fr`
writable. `save_ok`: the saves of `r28`–`r31` and of the return address.
`Mid`: in the frame, the saved values in their slots, four values kept in
`r28`–`r31` and the other callee-saved registers as on entry; it is kept by
code writing other registers and the frame above the slots (`Mid.keep`,
`Mid.frameW`). `restore_ok`: the restores give back the caller's registers.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE

/-! ## Addresses -/

/-- The frame's base: the stack pointer in the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses: the frame. -/
abbrev kR (s : State) : Region := ⟨fb s, frameBytes⟩

/-- The frame's local variable space, which its push makes writable. -/
abbrev fr (s : State) : Region := ⟨fb s + BitVec.ofNat 64 32, frameBytes - 32⟩

/-- The working space, and the arguments on the stack. -/
abbrev sR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 40⟩

theorem frameR_eq (s : State) : frameR frameBytes s = fr s := rfl

theorem fb_toNat {s : State} (h : frameBytes ≤ s.sp.toNat) : (fb s).toNat + frameBytes = s.sp.toNat := by
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

/-- A region of the frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := Offset.sub_base _ h

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (kR s).Contains (fb s + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by unfold frameBytes at h; omega)

/-- The local variable space is writable. -/
theorem in_fr (s : State) (rs : List Region) {d n : Nat} (h₁ : 32 ≤ d) (h : d + n ≤ frameBytes) :
    InRegions (fr s :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., Offset.contains _ h₁ (by unfold frameBytes at *; omega)
    (by unfold frameBytes; omega)⟩

theorem in_fr' (s : State) (rd rs : List Region) {d n : Nat} (h₁ : 32 ≤ d) (h : d + n ≤ frameBytes) :
    InRegions (rd ++ fr s :: rs) (fb s + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := in_fr s rs h₁ h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- Our stack arguments, from the frame. -/
theorem stackArgAddr_fb (s : State) (j : Nat) :
    stackArgAddr s j = fb s + BitVec.ofNat 64 (arg j) := by
  have e : BitVec.ofNat 64 (arg j) = BitVec.ofNat 64 frameBytes + BitVec.ofNat 64 (32 + 8 * (8 + j)) := by
    rw [BitVec.ofNat_add_ofNat]; unfold arg; congr 1; omega
  rw [stackArgAddr, e, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The call's stack arguments, in the frame. -/
theorem stackArgAddr_in (t : State) (j : Nat) :
    stackArgAddr t j = t.sp + BitVec.ofNat 64 (96 + 8 * j) := by
  rw [stackArgAddr, show 32 + 8 * (8 + j) = 96 + 8 * j by omega]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.add_zero]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, show 32 + 8 * 8 + 8 * j = 32 + 8 * (8 + j) by omega]

theorem in_aR {s : State} {j : Nat} (hj : j < 5) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-! ## The saves -/

/-- The slots of our caller's `r28`–`r31`. -/
def saved : List (Reg × Nat) := [(.r28, oSave), (.r29, oSave + 8), (.r30, oSave + 16), (.r31, oSave + 24)]

/-- The callee-saved registers other than `r28`–`r31`. -/
def hiRegs : List Reg := [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
  .r27]

/-- The registers `Mid` keeps. -/
def kept : List Reg := [.r28, .r29, .r30, .r31] ++ hiRegs

theorem save_eq : save = ([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
    ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) :=
  rfl

theorem restore_eq :
    restore = ([.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0] : List Instr) ++ Spill.restoreCode .r12 saved :=
  rfl

theorem saved_offs : ∀ p ∈ saved, oSave ≤ p.2 ∧ p.2 + 8 ≤ oSave + 32 := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem preserved_split {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst ∨ r ∈ hiRegs := by
  revert r; decide

/-- In the frame, from the entry state `s`: our caller's registers and
return address in their slots, `a`–`d` in `r28`–`r31`, the other
callee-saved registers as on entry, memory changed only in the stack the
function uses and the working space. -/
structure Mid (s : State) (a b c d : BitVec 64) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = fr s :: s.wr
  r28 : t.gpr .r28 = a
  r29 : t.gpr .r29 = b
  r30 : t.gpr .r30 = c
  r31 : t.gpr .r31 = d
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  mem : Frame [kR s, sR s] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  ls : t.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

section
variable {s t w : State} {a b c d : BitVec 64} {rs : List Reg}

theorem not_kept {r : Reg} (hrs : ∀ r ∈ rs, r ∉ kept) (hr : r ∈ kept) : r ∉ rs := fun h => hrs r h hr

theorem Mid.of (h : Mid s a b c d t) (hg : ∀ r ∈ kept, w.gpr r = t.gpr r) (hsp : w.sp = t.sp) (hrd : w.rd = t.rd)
    (hwr : w.wr = t.wr) (hm : Frame [kR s, sR s] s.mem w.mem) (hsv : Spill.Saved (fb s) s.gpr saved w.mem)
    (hls : w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr) : Mid s a b c d w where
  sp := hsp.trans h.sp
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r28 := (hg _ (by decide)).trans h.r28
  r29 := (hg _ (by decide)).trans h.r29
  r30 := (hg _ (by decide)).trans h.r30
  r31 := (hg _ (by decide)).trans h.r31
  hi := fun r hr => (hg _ (List.mem_append_right _ hr)).trans (h.hi r hr)
  mem := hm
  sv := hsv
  ls := hls

/-- `Mid` is kept by code writing registers other than those it keeps, and
memory `hm` says is kept. -/
theorem Mid.keep (h : Mid s a b c d t) (o : Keep rs t w) (hm : Frame [kR s, sR s] s.mem w.mem)
    (hsv : Spill.Saved (fb s) s.gpr saved w.mem) (hls : w.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Mid s a b c d w :=
  h.of (fun r hr => o.gpr r (not_kept hrs hr)) o.sp o.rd o.wr hm hsv hls

/-- `Mid` is kept by code writing registers other than those it keeps. -/
theorem Mid.only (h : Mid s a b c d t) (o : Only rs t w) (hrs : ∀ r ∈ rs, r ∉ kept := by decide) :
    Mid s a b c d w :=
  h.keep o.keep (by rw [o.mem]; exact h.mem) (by rw [o.mem]; exact h.sv) (by rw [o.mem]; exact h.ls) hrs

/-- Writes of the frame above the slots and of the working space keep
`Mid`'s memory. -/
theorem Mid.frameMem (h : Mid s a b c d t) (hks : (kR s).Disjoint (sR s)) {e n : Nat} {m : Mem}
    (he : oLr + 8 ≤ e) (hen : e + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 e, n⟩, sR s] t.mem m) :
    Frame [kR s, sR s] s.mem m ∧ Spill.Saved (fb s) s.gpr saved m ∧
      m.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr := by
  have hd : ∀ {d' k : Nat}, d' + k ≤ oLr + 8 → ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 e, n⟩ : Region), sR s],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d', k⟩ r := fun hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inl (by omega)) (by unfold oLr at hk; omega) (by unfold frameBytes at hen; omega)
    · exact hks.sub_left (frame_sub s (by unfold oLr frameBytes at *; omega))
  refine ⟨h.mem.trans (hm.sub fun r hr => ?_), h.sv.frame_in saved_offs hm (hd (by decide)), ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., frame_sub s hen⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  · rw [hm.readW (Region.contains_self _ _) (hd (by decide)) (by decide)]; exact h.ls

/-- `Mid` is kept by code writing registers other than those it keeps, the
frame above the slots and the working space. -/
theorem Mid.frameW (h : Mid s a b c d t) (o : Keep rs t w) (hks : (kR s).Disjoint (sR s)) {e n : Nat}
    (he : oLr + 8 ≤ e) (hen : e + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 e, n⟩, sR s] t.mem w.mem)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Mid s a b c d w :=
  have hf := h.frameMem hks he hen hm
  h.keep o hf.1 hf.2.1 hf.2.2 hrs

/-- `Mid.frameW` for a write of the frame alone. -/
theorem Mid.frameW1 (h : Mid s a b c d t) (o : Keep rs t w) (hks : (kR s).Disjoint (sR s)) {e n : Nat}
    (he : oLr + 8 ≤ e) (hen : e + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 e, n⟩] t.mem w.mem)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Mid s a b c d w :=
  h.frameW o hks he hen (hm.mono fun _ hr => by
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..) hrs

end

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [kR s, sR s] s.mem m) {p : Addr}
    {len : Nat} (hk : (kR s).Disjoint ⟨p, len⟩) (hs : (sR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hk.symm
  · exact hs.symm

theorem words_of_frame {s : State} {m : Mem} (hf : Frame [kR s, sR s] s.mem m) {p : Addr}
    {n : Nat} (hk : (kR s).Disjoint ⟨p, n * 8⟩) (hs : (sR s).Disjoint ⟨p, n * 8⟩) (hl : p.toNat + n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt s.mem p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => hf.readW (r := ⟨p, n * 8⟩) ?_ (fun r hr => ?_) (by decide)
  · have := List.mem_range.mp hi
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hk.symm
    · exact hs.symm

/-- The saves, from the state after the frame's push (`u`): `r12` holds
the frame's base, `r28`–`r31` and the return address are in their slots, and
memory is changed only in the frame. -/
theorem save_ok {s u : State} (hsp : u.sp = fb s) (hwr : u.wr = fr s :: s.wr)
    (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r ∈ preserved, u.gpr r = s.gpr r) (hlr : u.lr = s.lr)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, Keep [.r12, .r0] u v → v.gpr .r12 = fb s → Frame [kR s] s.mem v.mem →
      Spill.Saved (fb s) s.gpr saved v.mem → v.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr →
      WP isa (.block rest) v Q) :
    WP isa (.block (save ++ rest)) u Q := by
  rw [save_eq]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  refine Spill.save_ok (b := .r12) (l := saved) (by decide) saved_ho (fun p hp => ?_) ?_
  · have := saved_offs p hp
    rw [e₁, o₁.wr, hwr]; exact in_fr s _ (by unfold oSave at this; omega) (by unfold oSave frameBytes at *; omega)
  generalize hu₂ : ({ u₁ with mem := Spill.saveMem u₁.mem (u₁.gpr .r12) u₁.gpr saved } : State) = u₂
  have g₂ : u₂.gpr = u₁.gpr := by rw [← hu₂]
  have m₂ : u₂.mem = Spill.saveMem u.mem (fb s) u₁.gpr saved := by rw [← hu₂, e₁, o₁.mem]
  have k₂ : Keep [.r12] u u₂ := by
    rw [← hu₂]; exact ⟨fun r hr => o₁.gpr r hr, o₁.rd, o₁.wr, o₁.sp, o₁.lr⟩
  refine wp_mflr fun u₃ o₃ e₃ => wp_std (a := fb s + BitVec.ofNat 64 oLr)
    (by rw [o₃.get .r12, g₂, e₁]) (by rw [o₃.wr, k₂.wr, hwr]; exact in_fr s _ (by decide) (by decide))
    fun u₄ m₄ => ?_
  have fr₂ : Frame [kR s] s.mem u₂.mem := by
    rw [m₂]
    exact hm.trans (Spill.saveMem_frame_base (fun p hp => by
      have := saved_offs p hp; unfold oSave frameBytes at *; omega) (by decide) _ _ _)
  have sv₂ : Spill.Saved (fb s) s.gpr saved u₂.mem := by
    rw [m₂]
    refine fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans ?_
    have h12 : p.1 ∉ [Reg.r12] := by revert p; decide
    rw [o₁.gpr _ h12, hg _ (by revert p; decide)]
  have hd : ∀ p ∈ saved, ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 oLr, 8⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 p.2, 8⟩ r := fun p hp r hr => by
    have := saved_offs p hp
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by unfold oSave oLr at *; omega)) (by unfold oSave at *; omega) (by decide)
  have fw : Frame [⟨fb s + BitVec.ofNat 64 oLr, 8⟩] u₃.mem u₄.mem := by
    rw [m₄.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k u₄ ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
  · have h0 : r ∉ [Reg.r0] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; exact fun h => hr (.inr h)
    have h12 : r ∉ [Reg.r12] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; exact fun h => hr (.inl h)
    rw [m₄.gpr, o₃.gpr r h0, k₂.gpr r h12]
  · rw [m₄.rd, o₃.rd, k₂.rd]
  · rw [m₄.wr, o₃.wr, k₂.wr]
  · rw [m₄.sp, o₃.sp, k₂.sp]
  · rw [m₄.lr, o₃.lr, k₂.lr]
  · rw [m₄.gpr, o₃.get .r12, g₂, e₁]
  · rw [m₄.mem, o₃.mem]
    exact fr₂.writeW (List.mem_singleton_self _) _ (frame_contains s (by decide))
  · have : Spill.Saved (fb s) s.gpr saved u₃.mem := by rw [o₃.mem]; exact sv₂
    exact this.frame fw hd
  · rw [m₄.mem, Mem.readW_writeW_self64, e₃, k₂.lr, hlr]

/-- What the restores need: the frame, our caller's registers and return
address in their slots, and the other callee-saved registers as on entry. -/
structure Saves (s t : State) : Prop where
  sp : t.sp = fb s
  wr : t.wr = fr s :: s.wr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  ls : t.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr

theorem Mid.saves {s t : State} {a b c d : BitVec 64} (h : Mid s a b c d t) : Saves s t :=
  ⟨h.sp, h.wr, h.hi, h.sv, h.ls⟩

/-- `Saves` is kept by code writing registers other than the callee-saved
ones, and memory apart from the frame. -/
theorem Saves.keep {s t w : State} {rs : List Reg} (h : Saves s t) (o : Keep rs t w) {R : List Region}
    (hm : Frame R t.mem w.mem) (hR : ∀ r ∈ R, (kR s).Disjoint r) (hrs : ∀ r ∈ rs, r ∉ kept := by decide) :
    Saves s w where
  sp := o.sp.trans h.sp
  wr := o.wr.trans h.wr
  hi := fun r hr => (o.gpr _ (not_kept hrs (List.mem_append_right _ hr))).trans (h.hi r hr)
  sv := h.sv.frame hm fun p hp r hr => (hR r hr).sub_left (frame_sub s (by
    have := saved_offs p hp; unfold oSave frameBytes at *; omega))
  ls := by rw [hm.readW (Region.contains_self _ _) (fun r hr => (hR r hr).sub_left (frame_sub s (by decide)))
    (by decide)]; exact h.ls

theorem freed_lr (n : Nat) (s : State) : (freed n s).lr = s.lr := rfl
theorem freed_gpr (n : Nat) (s : State) : (freed n s).gpr = s.gpr := rfl
theorem freed_mem (n : Nat) (s : State) : (freed n s).mem = s.mem := rfl

theorem allocated_sp (n : Nat) (s : State) : (allocated n s).sp = s.sp - BitVec.ofNat 64 n := rfl
theorem allocated_rd (n : Nat) (s : State) : (allocated n s).rd = s.rd := rfl
theorem allocated_wr (n : Nat) (s : State) : (allocated n s).wr = frameR n s :: s.wr := rfl
theorem allocated_gpr (n : Nat) (s : State) : (allocated n s).gpr = s.gpr := rfl
theorem allocated_lr (n : Nat) (s : State) : (allocated n s).lr = s.lr := rfl
theorem allocated_mem (n : Nat) (s : State) :
    (allocated n s).mem = s.mem.write (s.sp - BitVec.ofNat 64 n) 8 s.sp := rfl

/-- The frame's push stores the back chain at its base. -/
theorem fb_contains (s : State) : (kR s).Contains (fb s) 8 := by
  have := frame_contains s (d := 0) (n := 8) (by decide)
  rwa [BitVec.add_zero] at this

/-- The restores: the caller's registers and return address are back, and
`r3` and memory are kept. -/
theorem restore_ok {s w : State} (hm : Saves s w) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ w'.gpr .r3 = w.gpr .r3 ∧ w'.mem = w.mem := by
  rw [restore_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun w₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  have hin : ∀ {e : Nat}, oSave ≤ e → e + 8 ≤ oLr + 8 →
      InRegions (w₁.rd ++ w₁.wr) (fb s + BitVec.ofNat 64 e) 8 := fun h₁ h₂ => by
    rw [o₁.wr, hm.wr]; exact in_fr' s _ _ (by unfold oSave at h₁; omega) (by unfold oLr frameBytes at *; omega)
  refine wp_ld (a := fb s + BitVec.ofNat 64 oLr) (by rw [e₁]) (hin (by decide) (by decide)) fun w₂ o₂ e₂ =>
    wp_mtlr fun w₃ g₃ m₃ rd₃ wr₃ sp₃ lr₃ => ?_
  refine WP.mono (Spill.restore_wp (b := .r12) (l := saved) (B := fb s) (g := s.gpr) (by decide)
    (by rw [g₃, o₂.get .r12, e₁]) saved_ho (by decide)
    (fun p hp => by
      have := saved_offs p hp
      rw [rd₃, wr₃, o₂.rd, o₂.wr]; exact hin this.1 (by unfold oSave oLr at *; omega))
    (by rw [m₃, o₂.mem, o₁.mem]; exact hm.sv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, ?_⟩, ?_, ?_⟩
  · show w'.gpr r = s.gpr r
    rcases preserved_split hr' with h | h
    · exact hr.gpr_of (.inl h)
    · have h0 : r ∉ saved.map Prod.fst := by revert r; decide
      have h1 : r ∉ [Reg.r0] := by revert r; decide
      have h2 : r ∉ [Reg.r12] := by revert r; decide
      rw [hr.other r h0, g₃, o₂.gpr r h1, o₁.gpr r h2]; exact hm.hi r h
  · show w'.sp + BitVec.ofNat 64 frameBytes = s.sp
    rw [hr.sp, sp₃, o₂.sp, o₁.sp, hm.sp, BitVec.sub_add_cancel]
  · have h₁ := hr.lr
    have h₂ : w₁.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr := by rw [o₁.mem]; exact hm.ls
    rw [freed_lr]; exact h₁.trans (lr₃.trans (e₂.trans h₂))
  · show w'.gpr .r3 = w.gpr .r3
    rw [hr.other .r3 (by decide), g₃, o₂.get .r3, o₁.get .r3]
  · rw [hr.mem, m₃, o₂.mem, o₁.mem]

end VG.Proof.RsaPkcs1Sig.PPC64LE
