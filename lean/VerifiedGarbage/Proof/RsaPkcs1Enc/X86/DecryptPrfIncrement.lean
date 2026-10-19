module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashLocal

/-! # Advance a PRF block counter and branch only on the public block count -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem prfIncr_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} {i nb : Nat}
    (h : Context g bs s) (counter : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = BitVec.ofNat 32 i)
    (blocks : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oNB) 32 = BitVec.ofNat 32 nb) :
    WP isa (.block incr) s fun t => Context g bs t ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 oI, 4⟩] s.mem t.mem ∧ Keeps [.eax] s t ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = BitVec.ofNat 32 (i + 1) ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oNB) 32 = BitVec.ofNat 32 nb ∧
      t.zf = some (BitVec.ofNat 32 (i + 1) - BitVec.ofNat 32 nb == 0) := by
  have code : incr = [.mov .eax (.mem (stackAt oI)), .alu .add .eax (.imm 1)] ++
      [.store (stackAt oI) .eax] ++ [.alu .cmp .eax (.mem (stackAt oNB))] := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  unfold stackAt
  refine wp_ldm rfl (by
    rw [h.address (by decide : oI < VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes + 20 + 92)]
    exact h.inner.read (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)) fun a A => ?_
  refine wp_addS rfl fun b B _ => WP.block_nil ?_
  have Kb : Keeps [.eax] s b := A.keeps.trans B.keeps
  have Mb : b.mem = s.mem := B.mem.trans A.mem
  have hb := h.after (by rw [Mb]; exact Frame.refl _ _) Kb (Kb.1 .esp (by decide))
  have ax : b.gpr .eax = BitVec.ofNat 32 (i + 1) := by
    rw [B.gpr, A.gpr, h.address (by decide : oI < VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes + 20 + 92), counter]
    change BitVec.ofNat 32 i + BitVec.ofNat 32 1 = _
    exact (BitVec.ofNat_add _ _).symm
  refine WP.mono (storeLocal_ok hb .eax (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)) ?_
  rintro c ⟨hc, Mc, Fc, Kc⟩
  have nbC : c.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oNB) 32 = BitVec.ofNat 32 nb := by
    apply Eq.trans (Fc.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 oNB, 4⟩)
      (Region.contains_self _ _) ?_ (by decide))
    · rw [Mb]; exact blocks
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (Or.inr (by decide : oI + 4 ≤ oNB)) (by decide) (by decide)
  have readNB : readSrc c (.mem ⟨.esp, oNB⟩) = some (BitVec.ofNat 32 nb) := by
    have readable : InRegions (c.rd ++ c.wr) (addr (c.gpr .esp) oNB) 4 := by
      rw [hc.address (by decide : oNB < VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes + 20 + 92)]
      exact hc.inner.read (by decide : oNB + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)
    have raw := readSrc_mem rfl readable
    rw [hc.address (by decide : oNB < VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes + 20 + 92), nbC] at raw
    exact raw
  refine wp_cmpS readNB fun t T Z => WP.block_nil ?_
  have M : t.mem = c.mem := T.mem
  have K : Keeps [.eax] s t := Kb.trans ((Kc.mono (by simp)).trans (T.keeps _))
  have F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 oI, 4⟩] s.mem t.mem := by rw [M, ← Mb]; exact Fc
  refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), F, K, ?_, by rw [M]; exact nbC, ?_⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)⟩
  · rw [M, Mc, Mem.readW_writeW_self32, ax]
  · rw [Kc.1 .eax (by decide)] at Z
    rw [ax] at Z
    exact Z

end VG.Proof.RsaPkcs1Enc.X86.Dec
