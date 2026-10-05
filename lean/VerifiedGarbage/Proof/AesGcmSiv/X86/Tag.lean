import VerifiedGarbage.Proof.AesGcmSiv.X86.Polyval

/-!
# AES-GCM-SIV on x86: a block encrypted with the encryption key (`tag`)

Untrusted: everything here is checked by Lean. `tag o` copies the block at
`W + 96` to `W + 112` (`copyMem`), zeroes the block at `W + o`, and calls
`vg_aes_ctr32` on that one block with the copy as the counter block: the
encryption of the block at `W + 96` with the encryption key's schedule at
`W + 512` (`tag_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq GcmImpl readW_writeW_off zero4_fold)

theorem blockAt_zero4 (m : Mem) (p : Addr) : Spec.Gcm.blockAt (Proof.Cmac.zero4 m p) p = 0 := by
  rw [Spec.Gcm.blockAt, Proof.Cmac.zero4_bytes]
  decide

/-- The memory after the copy of the counter block. -/
def copyMem (m : Mem) (W : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) (m.readW (W + BitVec.ofNat 64 96) 32)
    (m.readW (W + BitVec.ofNat 64 100) 32) (m.readW (W + BitVec.ofNat 64 104) 32)
    (m.readW (W + BitVec.ofNat 64 108) 32)

theorem copyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] m (copyMem m W) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem copyMem_bytes (m : Mem) (W : Addr) :
    bytesAt (copyMem m W) (W + BitVec.ofNat 64 112) 16 = bytesAt m (W + BitVec.ofNat 64 96) 16 := by
  rw [copyMem, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.bytesAt_split4]
  simp only [add_ofNat_assoc, Nat.reduceAdd]

/-- The blocks a tag may be written to. -/
abbrev TagO (o : Nat) : Prop := o = 0 ∨ o = 224 ∨ o = 240

/-- What `tag o` writes. -/
abbrev tagWr (p : Prm) (o : Nat) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩,
    stk p]

theorem inMut_tagWr (p : Prm) {o : Nat} (ho : TagO o) : InMut p (tagWr p o) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · rcases ho with rfl | rfl | rfl
    · exact inMut_w p (.inl (by decide))
    · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact inMut_stk p

/-- What `tag o` leaves, from `t`. -/
structure TagPost (p : Prm) (o : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = t.gpr .esi
  frame : Frame (tagWr p o) t.mem t'.mem
  out : bytesAt t'.mem (w64 p.W + BitVec.ofNat 64 o) 16 =
    Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 96) 16)

/-- What `tag o`'s block leaves: the arguments of its call. -/
structure TagCall (p : Prm) (o : Nat) (t t₁ : State) : Prop where
  mem : t₁.mem = Proof.Cmac.zero4 (copyMem t.mem (w64 p.W)) (w64 p.W + BitVec.ofNat 64 o)
  eax : t₁.gpr .eax = p.W + BitVec.ofNat 32 512
  ecx : t₁.gpr .ecx = BitVec.ofNat 32 p.R
  edx : t₁.gpr .edx = p.W + BitVec.ofNat 32 112
  ebx : t₁.gpr .ebx = p.W + BitVec.ofNat 32 o
  edi : t₁.gpr .edi = BitVec.ofNat 32 1
  esi : t₁.gpr .esi = t.gpr .esi
  rd : t₁.rd = t.rd
  wr : t₁.wr = t.wr
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o, 16⟩] t.mem t₁.mem
  env : Env p t₁
  dst : Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.W + BitVec.ofNat 32 o) (16 * 1)

/-- `tag o`'s block. -/
theorem tagArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {o : Nat} (ho : TagO o) :
    ∃ t₁, runBlock isa (copy16 cbO ccO ++ zero4 o ++ ctrArgs o) t = some t₁ ∧ TagCall p o t t₁ := by
  have hw := L.ww
  have o₁ : o + 16 ≤ 2816 := by omega
  have hR := E.slots.rounds
  simp only [slotv_eq, roundsO] at hR
  have hz := zero4_fold (copyMem t.mem (w64 p.W)) p.W o
  have rR : (copyMem t.mem (w64 p.W)).readW (w64 p.W + BitVec.ofNat 64 148) 32 = BitVec.ofNat 32 p.R := by
    rw [copyMem, Proof.Cmac.store4]
    simp (disch := decide) only [add_ofNat_assoc, Nat.reduceAdd, readW_writeW_off]
    exact hR
  have rR' : (Proof.Cmac.zero4 (copyMem t.mem (w64 p.W)) (w64 p.W + BitVec.ofNat 64 o)).readW
      (w64 p.W + BitVec.ofNat 64 148) 32 = BitVec.ofNat 32 p.R := by
    rw [← hz]
    rcases ho with rfl | rfl | rfl <;> simp (disch := decide) only [Nat.reduceAdd, readW_writeW_off] <;> exact rR
  obtain ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, bp₁, sp₁, si₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa
      (copy16 cbO ccO ++ zero4 o ++ ctrArgs o) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero4 (copyMem t.mem (w64 p.W)) (w64 p.W + BitVec.ofNat 64 o) ∧
      t₁.gpr .eax = p.W + BitVec.ofNat 32 512 ∧ t₁.gpr .ecx = BitVec.ofNat 32 p.R ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 112 ∧ t₁.gpr .ebx = p.W + BitVec.ofNat 32 o ∧
      t₁.gpr .edi = BitVec.ofNat 32 1 ∧ t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧ t₁.gpr .esi = t.gpr .esi ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    have hcp : ((((t.mem.writeW (w64 p.W + BitVec.ofNat 64 112) (t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32)).writeW
        (w64 p.W + BitVec.ofNat 64 116) (t.mem.readW (w64 p.W + BitVec.ofNat 64 100) 32)).writeW
        (w64 p.W + BitVec.ofNat 64 120) (t.mem.readW (w64 p.W + BitVec.ofNat 64 104) 32)).writeW
        (w64 p.W + BitVec.ofNat 64 124) (t.mem.readW (w64 p.W + BitVec.ofNat 64 108) 32)) =
        copyMem t.mem (w64 p.W) := by
      simp only [copyMem, Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]
    rcases ho with rfl | rfl | rfl <;>
    refine ⟨_, by simp only [copy16, zero4, ctrArgs]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hcp, hz, rR'],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | (gmems [hcp, hz]; done)
      | (gregs [E.ebp, rR']; done)
      | (gregs [E.ebp, E.esp]; done)
      | (gregs []; done)
      | rfl
  have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o, 16⟩] t.mem t₁.mem := by
    rw [hm₁, Proof.Cmac.zero4]
    exact ((copyMem_frame _ _).mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; simp)
  have E₁ : Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut f₁ fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact inMut_w p (.inl (by decide))
    · exact inMut_tagWr p ho _ (by simp))
  have hD : Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.W + BitVec.ofNat 32 o) (16 * 1) :=
    dstW L E₁.perm (q := o) (by rcases ho with rfl | rfl | rfl <;> decide)
      (by rw [L.aW (by decide)]; exact Lay.w_w (.inr (by omega)) (by decide) (by omega))
  exact ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, si₁, rd₁, wr₁, f₁, E₁, hD⟩

theorem tag_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {o : Nat} (ho : TagO o) :
    WP isa (tag v.callees o) t (TagPost p o t) := by
  have hw := L.ww
  have o₁ : o + 16 ≤ 2816 := by omega
  obtain ⟨t₁, run₁, ⟨hm₁, eax, ecx, edx, ebx, edi, si₁, rd₁, wr₁, f₁, E₁, hD⟩⟩ := tagArgs_ok L E ho
  have dO : (⟨w64 p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 112, 16⟩ :=
    Lay.w_w (by omega) (by omega) (by decide)
  have hb₁ : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 112) 16 = bytesAt t.mem (w64 p.W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, Proof.Cmac.zero4, Proof.AesGcm.X86.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dO.symm) (by decide), copyMem_bytes]
  have hz₁ : Spec.Gcm.blockAt t₁.mem (w64 p.W + BitVec.ofNat 64 o) = 0 := by rw [hm₁]; exact blockAt_zero4 _ _
  have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
      Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (Lay.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le)
      · exact (Lay.w_w (.inr (by omega)) (by decide) (by omega)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega)]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (callCtr_ok v L E₁ (keyS L E₁.perm) hD
    (by rw [L.aW (by omega)]; exact inMut_tagWr p ho _ (by simp)) eax ecx edx ebx edi) fun t₂ P => ?_
  have fc := P.frame
  have hout := P.out
  rw [L.aW (by omega)] at fc hout
  refine ⟨P.env, by rw [P.rd, rd₁], by rw [P.wr, wr₁], by rw [P.saved _ (by decide), si₁],
    (f₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp).trans (fc.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp), ?_⟩
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
  rw [L.aW (by decide)] at hout
  rw [Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
    show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 512) (16 * (p.R + 1))) =
      Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R from rfl, ek₁, hb₁]

end VG.Proof.AesGcmSiv.X86
