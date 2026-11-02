module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Frame
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PKCS1-v1_5 on RISC-V: the frame

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/Frame.lean`), for the frame of
`vg_rsa_pkcs1_verify_precomputed` and `vg_rsa_pkcs1_recover_precomputed`
(`Impl/RsaPkcs1Sig/RISCV64/Frame.lean`): it is all of the stack the function
uses, `kR`, from its base `fb`, and the allocation makes it writable.
`save_ok`: the saves of `s1`–`s4` and of the return address `ra`. `Mid`: in
the frame, the saved values in their slots, four values kept in `s1`–`s4`
and the other callee-saved registers as on entry; it is kept by code writing
other registers and the frame above the slots (`Mid.keep`, `Mid.frameW`).
`restore_ok`: the restores give back the caller's registers.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64

/-! ## Addresses -/

/-- The frame's base: the stack pointer in the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses: the frame. -/
abbrev kR (s : State) : Region := ⟨fb s, frameBytes⟩

/-- The working space, and the arguments on the stack. -/
abbrev sR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
abbrev aR (s : State) : Region := ⟨stackArgAddr s 0, 40⟩

theorem fb_toNat {s : State} (h : frameBytes ≤ s.sp.toNat) : (fb s).toNat + frameBytes = s.sp.toNat := by
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega

/-- A region of the frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := Offset.sub_base _ h

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (kR s).Contains (fb s + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by unfold frameBytes at h; omega)

/-- The frame is writable. -/
theorem in_fr (s : State) (rs : List Region) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (kR s :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., frame_contains s h⟩

theorem in_fr' (s : State) (rd rs : List Region) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (rd ++ kR s :: rs) (fb s + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := in_fr s rs h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- Our stack arguments, from the frame. -/
theorem stackArgAddr_fb (s : State) (j : Nat) :
    stackArgAddr s j = fb s + BitVec.ofNat 64 (frameBytes + 8 * j) := by
  rw [stackArgAddr, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem in_aR {s : State} {j : Nat} (hj : j < 5) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-! ## The saves -/

/-- The slots of our caller's `s1`–`s4` and return address. -/
def saved : List (Reg × Nat) := [(.s1, oSave), (.s2, oSave + 8), (.s3, oSave + 16), (.s4, oSave + 24), (.ra, oRa)]

/-- The callee-saved registers other than `s1`–`s4`. -/
def hiRegs : List Reg := [.s0, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

/-- The registers `Mid` keeps. -/
def kept : List Reg := [.s1, .s2, .s3, .s4] ++ hiRegs

theorem save_eq : save = ([.addSp .t0 0] : List Instr) ++ Spill.saveCode .t0 saved := rfl

theorem restore_eq : restore = ([.addSp .t0 0] : List Instr) ++ Spill.restoreCode .t0 saved := rfl

theorem saved_offs : ∀ p ∈ saved, oSave ≤ p.2 ∧ p.2 + 8 ≤ oSave + 40 := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem preserved_split {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst ∨ r ∈ hiRegs := by
  revert r; decide

/-- In the frame, from the entry state `s`: our caller's registers and
return address in their slots, `a`–`d` in `s1`–`s4`, the other callee-saved
registers as on entry, memory changed only in the stack the function uses
and the working space `S`. -/
structure Mid (S : Region) (s : State) (a b c d : BitVec 64) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = kR s :: s.wr
  s1 : t.gpr .s1 = a
  s2 : t.gpr .s2 = b
  s3 : t.gpr .s3 = c
  s4 : t.gpr .s4 = d
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  mem : Frame [kR s, S] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem

section
variable {S : Region} {s t w : State} {a b c d : BitVec 64} {rs : List Reg}

theorem not_kept {r : Reg} (hrs : ∀ r ∈ rs, r ∉ kept) (hr : r ∈ kept) : r ∉ rs := fun h => hrs r h hr

theorem Mid.of (h : Mid S s a b c d t) (hg : ∀ r ∈ kept, w.gpr r = t.gpr r) (hsp : w.sp = t.sp) (hrd : w.rd = t.rd)
    (hwr : w.wr = t.wr) (hm : Frame [kR s, S] s.mem w.mem) (hsv : Spill.Saved (fb s) s.gpr saved w.mem) :
    Mid S s a b c d w where
  sp := hsp.trans h.sp
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  s1 := (hg _ (by decide)).trans h.s1
  s2 := (hg _ (by decide)).trans h.s2
  s3 := (hg _ (by decide)).trans h.s3
  s4 := (hg _ (by decide)).trans h.s4
  hi := fun r hr => (hg _ (List.mem_append_right _ hr)).trans (h.hi r hr)
  mem := hm
  sv := hsv

/-- `Mid` is kept by code writing registers other than those it keeps, and
memory `hm` says is kept. -/
theorem Mid.keep (h : Mid S s a b c d t) (o : Kept rs t w) (hm : Frame [kR s, S] s.mem w.mem)
    (hsv : Spill.Saved (fb s) s.gpr saved w.mem) (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Mid S s a b c d w :=
  h.of (fun r hr => o.gpr r (not_kept hrs hr)) o.sp o.rd o.wr hm hsv

/-- `Mid` is kept by code writing registers other than those it keeps. -/
theorem Mid.only (h : Mid S s a b c d t) (o : Only rs t w) (hrs : ∀ r ∈ rs, r ∉ kept := by decide) :
    Mid S s a b c d w :=
  h.keep o.keep (by rw [o.mem]; exact h.mem) (by rw [o.mem]; exact h.sv) hrs

/-- Writes of the frame above the slots and of the working space keep
`Mid`'s memory. -/
theorem Mid.frameMem (h : Mid S s a b c d t) (hks : (kR s).Disjoint S) {e n : Nat} {m : Mem}
    (he : oRa + 8 ≤ e) (hen : e + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 e, n⟩, S] t.mem m) :
    Frame [kR s, S] s.mem m ∧ Spill.Saved (fb s) s.gpr saved m := by
  have hd : ∀ {d' k : Nat}, d' + k ≤ oRa + 8 → ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 e, n⟩ : Region), S],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d', k⟩ r := fun hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inl (by omega)) (by unfold oRa at hk; omega) (by unfold frameBytes at hen; omega)
    · exact hks.sub_left (frame_sub s (by unfold oRa frameBytes at *; omega))
  refine ⟨h.mem.trans (hm.sub fun r hr => ?_), h.sv.frame_in saved_offs hm (hd (by decide))⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., frame_sub s hen⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩

/-- `Mid` is kept by code writing registers other than those it keeps, the
frame above the slots and the working space. -/
theorem Mid.frameW (h : Mid S s a b c d t) (o : Kept rs t w) (hks : (kR s).Disjoint S) {e n : Nat}
    (he : oRa + 8 ≤ e) (hen : e + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 e, n⟩, S] t.mem w.mem)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Mid S s a b c d w :=
  have hf := h.frameMem hks he hen hm
  h.keep o hf.1 hf.2 hrs

/-- `Mid.frameW` for a write of the frame alone. -/
theorem Mid.frameW1 (h : Mid S s a b c d t) (o : Kept rs t w) (hks : (kR s).Disjoint S) {e n : Nat}
    (he : oRa + 8 ≤ e) (hen : e + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 e, n⟩] t.mem w.mem)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Mid S s a b c d w :=
  h.frameW o hks he hen (hm.mono fun _ hr => by
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..) hrs

end

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {S : Region} {s : State} {m : Mem} (hf : Frame [kR s, S] s.mem m) {p : Addr}
    {len : Nat} (hk : (kR s).Disjoint ⟨p, len⟩) (hs : S.Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hk.symm
  · exact hs.symm

theorem words_of_frame {S : Region} {s : State} {m : Mem} (hf : Frame [kR s, S] s.mem m) {p : Addr}
    {n : Nat} (hk : (kR s).Disjoint ⟨p, n * 8⟩) (hs : S.Disjoint ⟨p, n * 8⟩) (hl : p.toNat + n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt s.mem p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => hf.readW (r := ⟨p, n * 8⟩) ?_ (fun r hr => ?_) (by decide)
  · have := List.mem_range.mp hi
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hk.symm
    · exact hs.symm

/-- The saves, from the state after the allocation (`u`): `t0` holds the
frame's base, `s1`–`s4` and the return address are in their slots, and
memory is changed only in the frame. -/
theorem save_ok {s u : State} (hsp : u.sp = fb s) (hwr : u.wr = kR s :: s.wr) (hal : (fb s).toNat % 8 = 0)
    (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r ∈ preserved ++ ([.ra] : List Reg), u.gpr r = s.gpr r)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, Kept [.t0] u v → v.gpr .t0 = fb s → Frame [kR s] s.mem v.mem →
      Spill.Saved (fb s) s.gpr saved v.mem → WP isa (.block rest) v Q) :
    WP isa (.block (save ++ rest)) u Q := by
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  refine Spill.save_ok (b := .t0) (l := saved) (by rw [e₁]; exact hal) saved_ho (fun p hp => ?_) ?_
  · have := saved_offs p hp
    rw [e₁, o₁.wr, hwr]; exact in_fr s _ (by unfold oSave frameBytes at *; omega)
  refine k _ ⟨fun r hr => o₁.gpr r hr, o₁.rd, o₁.wr, o₁.sp⟩ e₁ ?_ ?_
  · show Frame [kR s] s.mem (Spill.saveMem u₁.mem (u₁.gpr .t0) u₁.gpr saved)
    rw [e₁, o₁.mem]
    exact hm.trans (Spill.saveMem_frame_base (fun p hp => by
      have := saved_offs p hp; unfold oSave frameBytes at *; omega) (by decide) _ _ _)
  · show Spill.Saved (fb s) s.gpr saved (Spill.saveMem u₁.mem (u₁.gpr .t0) u₁.gpr saved)
    rw [e₁]
    refine fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans ?_
    have h0 : p.1 ∉ [Reg.t0] := by revert p; decide
    rw [o₁.gpr _ h0, hg _ (by revert p; decide)]

/-- What the restores need: the frame, our caller's registers and return
address in their slots, and the other callee-saved registers as on entry. -/
structure Saves (s t : State) : Prop where
  sp : t.sp = fb s
  wr : t.wr = kR s :: s.wr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  sv : Spill.Saved (fb s) s.gpr saved t.mem

theorem Mid.saves {S : Region} {s t : State} {a b c d : BitVec 64} (h : Mid S s a b c d t) : Saves s t :=
  ⟨h.sp, h.wr, h.hi, h.sv⟩

/-- `Saves` is kept by code writing registers other than the callee-saved
ones, and memory apart from the frame. -/
theorem Saves.keep {s t w : State} {rs : List Reg} (h : Saves s t) (o : Kept rs t w) {R : List Region}
    (hm : Frame R t.mem w.mem) (hR : ∀ r ∈ R, (kR s).Disjoint r) (hrs : ∀ r ∈ rs, r ∉ kept := by decide) :
    Saves s w where
  sp := o.sp.trans h.sp
  wr := o.wr.trans h.wr
  hi := fun r hr => (o.gpr _ (not_kept hrs (List.mem_append_right _ hr))).trans (h.hi r hr)
  sv := h.sv.frame hm fun p hp r hr => (hR r hr).sub_left (frame_sub s (by
    have := saved_offs p hp; unfold oSave frameBytes at *; omega))

/-- The restores: the caller's registers and return address are back, and
`a0` and memory are kept. -/
theorem restore_ok {s w : State} (hm : Saves s w) (hal : (fb s).toNat % 8 = 0) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ w'.gpr .a0 = w.gpr .a0 ∧ w'.mem = w.mem := by
  rw [restore_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun w₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  refine WP.mono (Spill.restore_wp (b := .t0) (l := saved) (B := fb s) (g := s.gpr) hal
    e₁ saved_ho (by decide)
    (fun p hp => by
      have := saved_offs p hp
      rw [o₁.rd, o₁.wr, hm.wr]; exact in_fr' s _ _ (by unfold oSave frameBytes at *; omega))
    (by rw [o₁.mem]; exact hm.sv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, ?_⟩, ?_, ?_⟩
  · show w'.gpr r = s.gpr r
    rcases preserved_split hr' with h | h
    · exact hr.gpr_of (.inl h)
    · have h0 : r ∉ saved.map Prod.fst := by revert r; decide
      have h2 : r ∉ [Reg.t0] := by revert r; decide
      rw [hr.other r h0, o₁.gpr r h2]; exact hm.hi r h
  · show w'.sp + BitVec.ofNat 64 frameBytes = s.sp
    rw [hr.sp, o₁.sp, hm.sp, BitVec.sub_add_cancel]
  · show w'.gpr .ra = s.gpr .ra
    exact hr.gpr_of (.inl (by simp [saved]))
  · show w'.gpr .a0 = w.gpr .a0
    rw [hr.other .a0 (by decide), o₁.get .a0]
  · rw [hr.mem, o₁.mem]

end VG.Proof.RsaPkcs1Sig.RISCV64
