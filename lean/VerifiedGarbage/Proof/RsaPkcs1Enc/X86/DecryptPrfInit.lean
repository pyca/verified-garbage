module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfInvariant

/-! # Initialize the public PRF counter and fixed length-output block count -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem localFrame_rejection {g : Geometry} {m m' : Mem} {d : Nat}
    (slot : d = oI ∨ d = oNB)
    (F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 d, 4⟩] m m') : Frame (rejectionWrites g) m m' := F.sub (by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rcases slot with rfl | rfl <;> exact ⟨_, by simp [rejectionWrites], fun _ hx => hx⟩)

theorem localFrame_scratch {g : Geometry} {bs : Fin 9 → List Byte} {s t : State} {d o n : Nat}
    (h : Context g bs s) (fit : d + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes) (scratchFit : o + n ≤ 8448)
    (F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 d, 4⟩] s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (g.scratch o n).base n = Spec.Rsa.bytesAt s.mem (g.scratch o n).base n := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by omega)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ((h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x
    (Offset.sub_base _ fit x hx))).sub_right (h.valid.scratchSub scratchFit)).symm

theorem prfZero_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block [.mov .eax (.imm 0), .store (stackAt oI) .eax]) s fun t => Context g bs t ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 oI, 4⟩] s.mem t.mem ∧ Keeps [.eax] s t ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = 0 := by
  refine wp_movS rfl fun a A _ => ?_
  have ha := h.after (by rw [A.mem]; exact Frame.refl _ _) A.keeps (A.other .esp (by decide))
  refine WP.mono (storeLocal_ok ha .eax (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)) ?_
  rintro t ⟨ht, M, F, K⟩
  exact ⟨ht, by rw [A.mem] at F; exact F, A.keeps.trans (K.mono (by simp)),
    by rw [M, Mem.readW_writeW_self32, A.gpr]⟩

theorem clInit_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block clInit) s fun t => Context g bs t ∧ Frame (rejectionWrites g) s.mem t.mem ∧ Keeps [.eax] s t ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = 0 ∧
      t.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oNB) 32 = BitVec.ofNat 32 8 ∧
      ∀ o n, o + n ≤ 8448 → Spec.Rsa.bytesAt t.mem (g.scratch o n).base n =
        Spec.Rsa.bytesAt s.mem (g.scratch o n).base n := by
  have code : clInit = [.mov .eax (.imm 0), .store (stackAt oI) .eax] ++
      [.mov .eax (.imm 8), .store (stackAt oNB) .eax] := rfl
  rw [code, WP.block_append_iff]
  refine WP.mono (prfZero_ok h) ?_
  rintro a ⟨ha, Fa, Ka, zero⟩
  refine wp_movS rfl fun b B _ => ?_
  have hb := ha.after (by rw [B.mem]; exact Frame.refl _ _) B.keeps (B.other .esp (by decide))
  refine WP.mono (storeLocal_ok hb .eax (by decide : oNB + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes)) ?_
  rintro t ⟨ht, M, F, K⟩
  have Ft : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 oNB, 4⟩] a.mem t.mem := by rw [B.mem] at F; exact F
  refine ⟨ht, (localFrame_rejection (Or.inl rfl) Fa).trans
    (localFrame_rejection (Or.inr rfl) Ft),
    Ka.trans (B.keeps.trans (K.mono (by simp))), ?_, by rw [M, Mem.readW_writeW_self32, B.gpr]; rfl, ?_⟩
  · apply Eq.trans (Ft.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 oI, 4⟩)
      (Region.contains_self _ _) ?_ (by decide)) zero
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Offset.disjoint _ (Or.inl (by decide : oI + 4 ≤ oNB)) (by decide) (by decide)
  · intro o n fit
    exact (localFrame_scratch ha (by decide : oNB + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes) fit Ft).trans
      (localFrame_scratch h (by decide : oI + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes) fit Fa)

end VG.Proof.RsaPkcs1Enc.X86.Dec
