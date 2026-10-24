module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSAES-OAEP encryption on PPC64LE: the frame

Untrusted: everything here is checked by Lean. The frame of
`vg_rsa_oaep_<H>_mgf1_<G>_encrypt_precomputed` (`Impl/RsaOaep/PPC64LE.lean`),
from its base `fb`, and the 48 bytes below it that the streaming hash
functions use (`cR`): the stack the function uses, `kR`, the 304 bytes below
the stack pointer on entry. As for RSASSA-PKCS1-v1_5
(`Proof/RsaPkcs1Sig/PPC64LE/Frame.lean`): `save_ok`, the saves of
`r14`–`r29` and of the return address; `Saves`, what the restores need, kept
by code writing other registers and memory apart from the slots;
`restore_ok`, the restores giving back the caller's registers.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_addSp wp_mflr wp_std wp_ld wp_mtlr)

/-! ## Addresses -/

/-- The frame's base: the stack pointer in the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses: the frame and the 48 bytes below it. -/
abbrev kR (s : State) : Region := below s.sp 304

/-- The frame's local variable space, which its push makes writable. -/
abbrev fr (s : State) : Region := ⟨fb s + BitVec.ofNat 64 32, frameBytes - 32⟩

/-- The 48 bytes below the frame, which the streaming hash functions use. -/
abbrev cR (s : State) : Region := below (fb s) 48

theorem frameR_eq (s : State) : frameR frameBytes s = fr s := rfl

/-- An address of the frame, from the base of `kR`. -/
theorem fb_off (s : State) (d : Nat) :
    fb s + BitVec.ofNat 64 d = (s.sp - BitVec.ofNat 64 304) + BitVec.ofNat 64 (48 + d) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_comm, show (304 : Nat) = frameBytes + 48 from rfl]
  bv_omega

theorem cR_eq (s : State) : cR s = ⟨s.sp - BitVec.ofNat 64 304, 48⟩ := by
  simp only [cR, below, Region.mk.injEq, and_true]
  rw [BitVec.sub_sub]; rfl

/-- A region of the frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := by
  rw [fb_off]; exact Offset.sub_base _ (by unfold frameBytes at h; omega)

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (kR s).Contains (fb s + BitVec.ofNat 64 d) n := by
  rw [fb_off]
  exact Offset.contains_base _ (by unfold frameBytes at h; omega) (by unfold frameBytes at h; omega)

theorem cR_sub (s : State) : Region.Sub (cR s) (kR s) := by
  have := Offset.sub_base (s.sp - BitVec.ofNat 64 304) (d := 0) (n := 48) (k := 304) (by omega)
  rw [BitVec.add_zero] at this; rw [cR_eq]; exact this

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

/-! ## The saves -/

/-- The callee-saved registers other than `r14`–`r29`. -/
def hiRegs : List Reg := [.r2, .r30, .r31]

/-- The callee-saved registers. -/
def kept : List Reg := saved.map Prod.fst ++ hiRegs

theorem save_eq : save = ([.addSp .r12 0] : List Instr) ++ Spill.saveCode .r12 saved ++
    ([.mflr .r0, .store .d .r0 .r12 oLr] : List Instr) :=
  rfl

theorem restore_eq :
    restore = ([.addSp .r12 0, .load .d .r0 .r12 oLr, .mtlr .r0] : List Instr) ++ Spill.restoreCode .r12 saved :=
  rfl

theorem saved_offs : ∀ p ∈ saved, 112 ≤ p.2 ∧ p.2 + 8 ≤ oLr := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem preserved_split {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst ∨ r ∈ hiRegs := by
  revert r; decide

theorem not_kept {rs : List Reg} {r : Reg} (hrs : ∀ r ∈ rs, r ∉ kept) (hr : r ∈ kept) : r ∉ rs :=
  fun h => hrs r h hr

/-- The saves, from the state after the frame's push (`u`): `r12` holds
the frame's base, `r14`–`r29` and the return address are in their slots, and
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
    rw [e₁, o₁.wr, hwr]; exact in_fr s _ (by omega) (by unfold oLr frameBytes at *; omega)
  generalize hu₂ : ({ u₁ with mem := Spill.saveMem u₁.mem (u₁.gpr .r12) u₁.gpr saved } : State) = u₂
  have g₂ : u₂.gpr = u₁.gpr := by rw [← hu₂]
  have m₂ : u₂.mem = Spill.saveMem u.mem (fb s) u₁.gpr saved := by rw [← hu₂, e₁, o₁.mem]
  have k₂ : Keep [.r12] u u₂ := by
    rw [← hu₂]; exact ⟨fun r hr => o₁.gpr r hr, o₁.rd, o₁.wr, o₁.sp, o₁.lr⟩
  refine wp_mflr fun u₃ o₃ e₃ => wp_std (a := fb s + BitVec.ofNat 64 oLr)
    (by rw [o₃.get .r12, g₂, e₁]) (by rw [o₃.wr, k₂.wr, hwr]; exact in_fr s _ (by decide) (by decide))
    fun u₄ m₄ => ?_
  have hsl : Frame [⟨fb s, frameBytes⟩] u.mem u₂.mem := by
    rw [m₂]
    exact Spill.saveMem_frame_base (fun p hp => by
      have := saved_offs p hp; unfold oLr frameBytes at *; omega) (by decide) _ _ _
  have hfk : Region.Sub ⟨fb s, frameBytes⟩ (kR s) := by
    have := frame_sub s (d := 0) (n := frameBytes) (by omega); rwa [BitVec.add_zero] at this
  have fr₂ : Frame [kR s] s.mem u₂.mem :=
    hm.trans (hsl.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, hfk⟩)
  have sv₂ : Spill.Saved (fb s) s.gpr saved u₂.mem := by
    rw [m₂]
    refine fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans ?_
    have h12 : p.1 ∉ [Reg.r12] := by revert p; decide
    rw [o₁.gpr _ h12, hg _ (by revert p; decide)]
  have hd : ∀ p ∈ saved, ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 oLr, 8⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 p.2, 8⟩ r := fun p hp r hr => by
    have := saved_offs p hp
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inl (by omega)) (by unfold oLr at *; omega) (by decide)
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

/-- The slots: the saves and the return address. -/
abbrev slR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 112, oLr + 8 - 112⟩

theorem slR_sub (s : State) : Region.Sub (slR s) (kR s) := frame_sub s (by decide)

/-- `Saves` is kept by code writing registers other than the callee-saved
ones, and memory apart from the slots. -/
theorem Saves.keep {s t w : State} {rs : List Reg} (h : Saves s t) (o : Keep rs t w) {R : List Region}
    (hm : Frame R t.mem w.mem) (hR : ∀ r ∈ R, (slR s).Disjoint r) (hrs : ∀ r ∈ rs, r ∉ hiRegs := by decide) :
    Saves s w where
  sp := o.sp.trans h.sp
  wr := o.wr.trans h.wr
  hi := fun r hr => (o.gpr _ fun h' => hrs r h' hr).trans (h.hi r hr)
  sv := h.sv.frame hm fun p hp r hr => (hR r hr).sub_left (by
    have := saved_offs p hp
    exact Offset.sub _ (n := 8) (by omega) (by unfold oLr at *; omega))
  ls := by
    rw [hm.readW (Region.contains_self _ _) (fun r hr => (hR r hr).sub_left
      (Offset.sub _ (n := 8) (by decide) (by decide))) (by decide)]
    exact h.ls

/-- The restores: the caller's registers and return address are back, and
`r3` and memory are kept. -/
theorem restore_ok {s w : State} (hm : Saves s w) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ w'.gpr .r3 = w.gpr .r3 ∧ w'.mem = w.mem := by
  rw [restore_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun w₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  have hin : ∀ {e : Nat}, 112 ≤ e → e + 8 ≤ oLr + 8 →
      InRegions (w₁.rd ++ w₁.wr) (fb s + BitVec.ofNat 64 e) 8 := fun h₁ h₂ => by
    rw [o₁.wr, hm.wr]; exact in_fr' s _ _ (by omega) (by unfold oLr frameBytes at *; omega)
  refine wp_ld (a := fb s + BitVec.ofNat 64 oLr) (by rw [e₁]) (hin (by decide) (by decide)) fun w₂ o₂ e₂ =>
    wp_mtlr fun w₃ g₃ m₃ rd₃ wr₃ sp₃ lr₃ => ?_
  refine WP.mono (Spill.restore_wp (b := .r12) (l := saved) (B := fb s) (g := s.gpr) (by decide)
    (by rw [g₃, o₂.get .r12, e₁]) saved_ho (by decide)
    (fun p hp => by
      have := saved_offs p hp
      rw [rd₃, wr₃, o₂.rd, o₂.wr]; exact hin this.1 (by omega))
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
    exact h₁.trans (lr₃.trans (e₂.trans h₂))
  · show w'.gpr .r3 = w.gpr .r3
    rw [hr.other .r3 (by decide), g₃, o₂.get .r3, o₁.get .r3]
  · rw [hr.mem, m₃, o₂.mem, o₁.mem]

end VG.Proof.RsaOaep.PPC64LE
