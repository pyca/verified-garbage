module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptStackWord

/-! # Local words and constant or scratch-pointer call arguments -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem storeLocal_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (r : Reg) {d : Nat} (fit : d + 4 ≤ VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes) :
    WP isa (.block [.store (stackAt d) r]) s fun t => Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 d) (s.gpr r) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 d, 4⟩] s.mem t.mem ∧ Keeps [] s t := by
  unfold stackAt
  refine wp_stm (B := s.gpr .esp) rfl
    (by rw [h.address (by omega)]; exact h.inner.write fit) fun t T => WP.block_nil ?_
  have M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 d) (s.gpr r) := by
    rw [T.mem, h.address (by omega)]
  have F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 d, 4⟩] s.mem t.mem := by
    rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have K : Keeps [] s t := T.keeps _
  refine ⟨h.after (F.sub ?_) K (congrFun T.gpr .esp), M, F, K⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ fit⟩

theorem immArg_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (v : Nat) {j : Nat} (bound : j < 20) :
    WP isa (.block (immArg v j)) s fun t => Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) (BitVec.ofNat 32 v) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold immArg
  refine wp_movS rfl fun u U _ => ?_
  have hu := h.after (by rw [U.mem]; exact Frame.refl _ _) U.keeps (U.other .esp (by decide))
  refine WP.mono (storeLocal_ok hu .eax (by unfold VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes; omega)) ?_
  rintro t ⟨ht, M, F, K⟩
  exact ⟨ht, by rw [U.mem, U.gpr] at M; exact M, by rw [U.mem] at F; exact F,
    U.keeps.trans (K.mono (by simp))⟩

theorem scratchArg_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (d : Nat) {j : Nat} (bound : j < 20) :
    WP isa (.block (scratchArg d j)) s fun t => Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) (g.workspace + BitVec.ofNat 32 d) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold scratchArg
  refine wp_ldm rfl (h.readArg (by decide : 21 < 23)) fun a A => ?_
  refine wp_addS rfl fun b B _ => ?_
  have Kpre : Keeps [.eax] s b := A.keeps.trans B.keeps
  have Mpre : b.mem = s.mem := B.mem.trans A.mem
  have hb := h.after (by rw [Mpre]; exact Frame.refl _ _) Kpre (Kpre.1 .esp (by decide))
  refine WP.mono (storeLocal_ok hb .eax (by unfold VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes; omega)) ?_
  rintro t ⟨ht, M, F, K⟩
  refine ⟨ht, ?_, by rw [Mpre] at F; exact F, Kpre.trans (K.mono (by simp))⟩
  rw [Mpre, B.gpr, A.gpr, h.argumentValue (by decide : 21 < 23)] at M
  exact M

theorem inputAddArg_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) {i j : Nat} (inputBound : i < 23) (bound : j < 20) (v : Nat) :
    WP isa (.block [.mov .eax (.mem (incoming i)), .alu .add .eax (.imm (BitVec.ofNat 32 v)),
      .store (stackAt (4 * j)) .eax]) s fun t => Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j))
        (g.argument i + BitVec.ofNat 32 v) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold incoming
  refine wp_ldm rfl (h.readArg inputBound) fun a A => ?_
  refine wp_addS rfl fun b B _ => ?_
  have Kpre : Keeps [.eax] s b := A.keeps.trans B.keeps
  have Mpre : b.mem = s.mem := B.mem.trans A.mem
  have hb := h.after (by rw [Mpre]; exact Frame.refl _ _) Kpre (Kpre.1 .esp (by decide))
  refine WP.mono (storeLocal_ok hb .eax (by unfold VG.Impl.RsaPkcs1Enc.X86.Decrypt.frameBytes; omega)) ?_
  rintro t ⟨ht, M, F, K⟩
  refine ⟨ht, ?_, by rw [Mpre] at F; exact F, Kpre.trans (K.mono (by simp))⟩
  rw [Mpre, B.gpr, A.gpr, h.argumentValue inputBound] at M
  exact M

end VG.Proof.RsaPkcs1Enc.X86.Dec
