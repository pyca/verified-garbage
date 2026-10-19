module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfInit

/-! # The alternative-message PRF rounds its public byte length up to blocks -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem amInit_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block amInit) s fun t => Context g bs t ∧ Frame (rejectionWrites g) s.mem t.mem ∧ Keeps [.eax] s t ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = 0 ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oNB) 32 = BitVec.ofNat 32 ((g.length + 31) / 32) ∧
      ∀ o n, o + n ≤ 8448 → Spec.Rsa.bytesAt t.mem (g.scratch o n).base n =
        Spec.Rsa.bytesAt s.mem (g.scratch o n).base n := by
  have code : amInit = [.mov .eax (.imm 0), .store (stackAt oI) .eax] ++
      [.mov .eax (.mem (incoming 4)), .alu .add .eax (.imm 31), .shift .shr .eax 5, .store (stackAt oNB) .eax] := rfl
  rw [code, WP.block_append_iff]
  refine WP.mono (prfZero_ok h) ?_
  rintro a ⟨ha, Fa, Ka, zero⟩
  unfold incoming
  refine wp_ldm rfl (ha.readArg (by decide : 4 < 23)) fun b B => ?_
  refine wp_addS rfl fun c C _ => ?_
  refine wp_shr (by decide) fun d D _ => ?_
  have Kd : Keeps [.eax] a d := B.keeps.trans (C.keeps.trans D.keeps)
  have Md : d.mem = a.mem := D.mem.trans (C.mem.trans B.mem)
  have hd := ha.after (by rw [Md]; exact Frame.refl _ _) Kd (Kd.1 .esp (by decide))
  have ax : d.gpr .eax = BitVec.ofNat 32 ((g.length + 31) / 32) := by
    rw [D.gpr, C.gpr, B.gpr, ha.argumentValue (by decide : 4 < 23)]
    change (BitVec.ofNat 32 g.length + BitVec.ofNat 32 31) >>> 5 = _
    rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    have := ha.valid.maxLength
    omega
  refine WP.mono (storeLocal_ok hd .eax (by decide : oNB + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)) ?_
  rintro t ⟨ht, M, F, K⟩
  have Ft : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 oNB, 4⟩] a.mem t.mem := by rw [Md] at F; exact F
  refine ⟨ht, (localFrame_rejection (Or.inl rfl) Fa).trans
    (localFrame_rejection (Or.inr rfl) Ft),
    Ka.trans (Kd.trans (K.mono (by simp))), ?_, by rw [M, Mem.readW_writeW_self32, ax], ?_⟩
  · apply Eq.trans (Ft.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 oI, 4⟩)
      (Region.contains_self _ _) ?_ (by decide)) zero
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint _ (Or.inl (by decide : oI + 4 ≤ oNB)) (by decide) (by decide)
  · intro o n fit
    exact (localFrame_scratch ha (by decide : oNB + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes) fit Ft).trans
      (localFrame_scratch h (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes) fit Fa)

end VG.Proof.RsaPkcs1Enc.X86.Dec
