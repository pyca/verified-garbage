module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Sign.Pre
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_pkcs1_sign` on RISC-V: the frame

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/SignFrame.lean`): the stack the function uses,
`kR`, is `vg_rsa_private_checked`'s frame (from `kb`) and then ours (`frR`,
from `fb`), which the allocation makes writable. `save_ok`: the saves of
`s1`–`s5` and of the return address `ra`. `Mid`: in the frame, the saved
values in their slots, five values kept in `s1`–`s5` and the other
callee-saved registers as on entry, memory changed only in the stack and in
the regions `S`; it is kept by code writing other registers and the frame
above the slots (`Mid.keep`, `Mid.frameW`). `restore_ok`: the restores give
back the caller's registers.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64.Sign

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64.Sign

/-! ## Addresses -/

/-- The base of the stack the function and its callee use. -/
abbrev kb (s : State) : Addr := s.sp - BitVec.ofNat 64 stackBytes

/-- Our frame, which the allocation makes writable. -/
abbrev frR (s : State) : Region := ⟨fb s, frameBytes⟩

theorem fb_eq (s : State) : fb s = kb s + BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes := by
  apply BitVec.eq_of_toNat_eq
  simp only [fb, kb, stackBytes, frameBytes, Impl.Rsa.RISCV64.Priv.frameBytes, BitVec.toNat_sub,
    BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem fb_off (s : State) (d : Nat) :
    fb s + BitVec.ofNat 64 d = kb s + BitVec.ofNat 64 (Impl.Rsa.RISCV64.Priv.frameBytes + d) := by
  rw [fb_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem fb_toNat {s : State} (h : SPre s) : (fb s).toNat + frameBytes = s.sp.toNat := by
  have := h.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stackBytes frameBytes at *
  unfold Impl.Rsa.RISCV64.Priv.frameBytes at *; omega

theorem kb_toNat {s : State} (h : SPre s) : (kb s).toNat + stackBytes = s.sp.toNat := by
  have := h.sp1
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stackBytes frameBytes at *
  unfold Impl.Rsa.RISCV64.Priv.frameBytes at *; omega

theorem fb_al {s : State} (h : SPre s) : (fb s).toNat % 16 = 0 := by
  have := fb_toNat h; have := h.sp16; unfold frameBytes at *; omega

theorem fb_al8 {s : State} (h : SPre s) {d : Nat} (hd : d % 8 = 0) : (fb s + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  Spill.al8 (by have := fb_al h; omega) hd

/-- A region of our frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := by
  rw [fb_off]
  exact Offset.sub_base _ (by unfold stackBytes frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at *; omega)

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (kR s).Contains (fb s + BitVec.ofNat 64 d) n := by
  rw [fb_off]
  exact Offset.contains_base _ (by unfold stackBytes frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at *; omega)
    (by unfold frameBytes Impl.Rsa.RISCV64.Priv.frameBytes at *; omega)

theorem frR_sub (s : State) : Region.Sub (frR s) (kR s) := by
  have := frame_sub s (d := 0) (n := frameBytes) (Nat.le_refl _)
  rwa [BitVec.add_zero] at this

/-- The callee's frame is in the stack the function uses. -/
theorem callee_sub (s : State) :
    Region.Sub ⟨fb s - BitVec.ofNat 64 Impl.Rsa.RISCV64.Priv.frameBytes,
      Impl.Rsa.RISCV64.Priv.frameBytes⟩ (kR s) := by
  rw [fb_eq, BitVec.add_sub_cancel]
  have := Offset.sub_base (kb s) (d := 0) (n := Impl.Rsa.RISCV64.Priv.frameBytes) (k := stackBytes)
    (by unfold stackBytes; omega)
  rwa [BitVec.add_zero] at this

/-- Our frame is writable. -/
theorem in_fr (s : State) (rs : List Region) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (frR s :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by unfold frameBytes at h; omega)⟩

theorem in_fr' (s : State) (rd rs : List Region) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (rd ++ frR s :: rs) (fb s + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := in_fr s rs h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- Our stack arguments, from the frame. -/
theorem stackArgAddr_fb (s : State) (j : Nat) :
    stackArgAddr s j = fb s + BitVec.ofNat 64 (frameBytes + 8 * j) := by
  rw [stackArgAddr, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem in_aR {s : State} {j : Nat} (hj : j < 13) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

/-! ## The saves -/

/-- The slots of our caller's `s1`–`s5` and return address. -/
def saved : List (Reg × Nat) :=
  [(.s1, oSave), (.s2, oSave + 8), (.s3, oSave + 16), (.s4, oSave + 24), (.s5, oSave + 32), (.ra, oRa)]

/-- The callee-saved registers other than `s1`–`s5`. -/
def hiRegs : List Reg := [.s0, .s6, .s7, .s8, .s9, .s10, .s11]

/-- The registers `Mid` keeps. -/
def kept : List Reg := [.s1, .s2, .s3, .s4, .s5] ++ hiRegs

/-- The saves of `s1`–`s5` and `ra`. -/
abbrev spill : List Instr := ([.addSp .t0 0] : List Instr) ++ Spill.saveCode .t0 saved

/-- The moves into `s1`–`s5`. -/
abbrev moves : List Instr :=
  [Impl.RsaPkcs1Sig.RISCV64.mov .s1 .a0, Impl.RsaPkcs1Sig.RISCV64.mov .s2 .a2,
    Impl.RsaPkcs1Sig.RISCV64.mov .s3 .a3, Impl.RsaPkcs1Sig.RISCV64.mov .s4 .a4,
    Impl.RsaPkcs1Sig.RISCV64.mov .s5 .a5]

theorem save_eq : save = spill ++ moves := rfl

theorem restore_eq : restore = ([.addSp .t0 0] : List Instr) ++ Spill.restoreCode .t0 saved := rfl

theorem saved_offs : ∀ p ∈ saved, oSave ≤ p.2 ∧ p.2 + 8 ≤ oRa + 8 := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem preserved_split {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst ∨ r ∈ hiRegs := by
  revert r; decide

/-- In the frame, from the entry state `s`: our caller's registers and
return address in their slots, `a`–`e` in `s1`–`s5`, the other callee-saved
registers as on entry, memory changed only in the stack the function uses
and the regions `S`. -/
structure Mid (S : List Region) (s : State) (a b c d e : BitVec 64) (t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = frR s :: s.wr
  s1 : t.gpr .s1 = a
  s2 : t.gpr .s2 = b
  s3 : t.gpr .s3 = c
  s4 : t.gpr .s4 = d
  s5 : t.gpr .s5 = e
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  mem : Frame (kR s :: S) s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem

section
variable {S : List Region} {s t w : State} {a b c d e : BitVec 64} {rs : List Reg}

theorem not_kept {r : Reg} (hrs : ∀ r ∈ rs, r ∉ kept) (hr : r ∈ kept) : r ∉ rs := fun h => hrs r h hr

theorem Mid.of (h : Mid S s a b c d e t) (hg : ∀ r ∈ kept, w.gpr r = t.gpr r) (hsp : w.sp = t.sp)
    (hrd : w.rd = t.rd) (hwr : w.wr = t.wr) (hm : Frame (kR s :: S) s.mem w.mem)
    (hsv : Spill.Saved (fb s) s.gpr saved w.mem) : Mid S s a b c d e w where
  sp := hsp.trans h.sp
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  s1 := (hg _ (by decide)).trans h.s1
  s2 := (hg _ (by decide)).trans h.s2
  s3 := (hg _ (by decide)).trans h.s3
  s4 := (hg _ (by decide)).trans h.s4
  s5 := (hg _ (by decide)).trans h.s5
  hi := fun r hr => (hg _ (List.mem_append_right _ hr)).trans (h.hi r hr)
  mem := hm
  sv := hsv

/-- `Mid` is kept by code writing registers other than those it keeps, and
memory `hm` says is kept. -/
theorem Mid.keep (h : Mid S s a b c d e t) (o : Kept rs t w) (hm : Frame (kR s :: S) s.mem w.mem)
    (hsv : Spill.Saved (fb s) s.gpr saved w.mem) (hrs : ∀ r ∈ rs, r ∉ kept := by decide) :
    Mid S s a b c d e w :=
  h.of (fun r hr => o.gpr r (not_kept hrs hr)) o.sp o.rd o.wr hm hsv

/-- `Mid` is kept by code writing registers other than those it keeps. -/
theorem Mid.only (h : Mid S s a b c d e t) (o : Only rs t w) (hrs : ∀ r ∈ rs, r ∉ kept := by decide) :
    Mid S s a b c d e w :=
  h.keep o.keep (by rw [o.mem]; exact h.mem) (by rw [o.mem]; exact h.sv) hrs

/-- Writes of the frame apart from the slots keep `Mid`'s memory. -/
theorem Mid.frameMem (h : Mid S s a b c d e t) {f n : Nat} {m : Mem}
    (he : oRa + 8 ≤ f ∨ f + n ≤ oSave) (hen : f + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 f, n⟩] t.mem m) :
    Frame (kR s :: S) s.mem m ∧ Spill.Saved (fb s) s.gpr saved m := by
  refine ⟨h.mem.trans (hm.sub fun r hr => ?_), h.sv.frame hm fun p hp r hr => ?_⟩
  · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., frame_sub s hen⟩
  · have := saved_offs p hp
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (by unfold oRa oSave at *; omega) (by unfold oRa at *; omega)
      (by unfold frameBytes at hen; omega)

/-- `Mid` is kept by code writing registers other than those it keeps and the
frame apart from the slots. -/
theorem Mid.frameW (h : Mid S s a b c d e t) (o : Kept rs t w) {f n : Nat}
    (he : oRa + 8 ≤ f ∨ f + n ≤ oSave) (hen : f + n ≤ frameBytes) (hm : Frame [⟨fb s + BitVec.ofNat 64 f, n⟩] t.mem w.mem)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) : Mid S s a b c d e w :=
  have hf := h.frameMem he hen hm
  h.keep o hf.1 hf.2 hrs

end

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {s : State} {rs : List Region} {m : Mem} (hf : Frame rs s.mem m) {p : Addr}
    {len : Nat} (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, len⟩ r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) hd hl (List.mem_range.mp hi)

/-- The saves, from the state after the allocation (`u`): `t0` holds the
frame's base, `s1`–`s5` and the return address are in their slots, and
memory is changed only in the frame. -/
theorem save_ok {s u : State} (hsp : u.sp = fb s) (hwr : u.wr = frR s :: s.wr) (hal : (fb s).toNat % 8 = 0)
    (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r ∈ preserved ++ ([.ra] : List Reg), u.gpr r = s.gpr r)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, Kept [.t0] u v → v.gpr .t0 = fb s → Frame [kR s] s.mem v.mem →
      Spill.Saved (fb s) s.gpr saved v.mem → WP isa (.block rest) v Q) :
    WP isa (.block (spill ++ rest)) u Q := by
  simp only [spill, List.cons_append, List.nil_append]
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  refine Spill.save_ok (b := .t0) (l := saved) (by rw [e₁]; exact hal) saved_ho (fun p hp => ?_) ?_
  · have := saved_offs p hp
    rw [e₁, o₁.wr, hwr]; exact in_fr s _ (by unfold oRa frameBytes at *; omega)
  refine k _ ⟨fun r hr => o₁.gpr r hr, o₁.rd, o₁.wr, o₁.sp⟩ e₁ ?_ ?_
  · show Frame [kR s] s.mem (Spill.saveMem u₁.mem (u₁.gpr .t0) u₁.gpr saved)
    rw [e₁, o₁.mem]
    exact hm.trans ((Spill.saveMem_frame_base (n := frameBytes) (fun p hp => by
      have := saved_offs p hp; unfold oRa frameBytes at *; omega) (by decide) _ _ _).sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, frR_sub s⟩)
  · show Spill.Saved (fb s) s.gpr saved (Spill.saveMem u₁.mem (u₁.gpr .t0) u₁.gpr saved)
    rw [e₁]
    refine fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans ?_
    have h0 : p.1 ∉ [Reg.t0] := by revert p; decide
    rw [o₁.gpr _ h0, hg _ (by revert p; decide)]

/-- What the restores need: the frame, our caller's registers and return
address in their slots, and the other callee-saved registers as on entry. -/
structure Saves (s t : State) : Prop where
  sp : t.sp = fb s
  wr : t.wr = frR s :: s.wr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  sv : Spill.Saved (fb s) s.gpr saved t.mem

theorem Mid.saves {S : List Region} {s t : State} {a b c d e : BitVec 64} (h : Mid S s a b c d e t) :
    Saves s t :=
  ⟨h.sp, h.wr, h.hi, h.sv⟩

/-- The restores: the caller's registers and return address are back, and
`a0` and memory are kept. -/
theorem restore_ok {s w : State} (h : SPre s) (hm : Saves s w) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ w'.gpr .a0 = w.gpr .a0 ∧ w'.mem = w.mem := by
  rw [restore_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun w₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  refine WP.mono (Spill.restore_wp (b := .t0) (l := saved) (B := fb s) (g := s.gpr) (by
      have := fb_al8 h (d := 0) (by decide); rwa [BitVec.add_zero] at this)
    e₁ saved_ho (by decide)
    (fun p hp => by
      have := saved_offs p hp
      rw [o₁.rd, o₁.wr, hm.wr]; exact in_fr' s _ _ (by unfold oRa frameBytes at *; omega))
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

end VG.Proof.RsaPkcs1Sig.RISCV64.Sign
