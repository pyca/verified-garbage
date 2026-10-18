module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptCallArgs

/-! # The padding validity word is separate from all outgoing arguments -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Encrypt

def savedFlag (g : Geometry) (s : State) : BitVec 32 :=
  s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 zeroOffset) 32

theorem savedFlag_frame {g : Geometry} {s t : State}
    (F : Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem) : savedFlag g t = savedFlag g s := by
  apply F.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 zeroOffset, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Offset.disjoint_base _ (by decide : 40 ≤ zeroOffset) (by decide)

theorem storeFlag_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block [.store (stackAt zeroOffset) .ebx]) s fun t => Context g bs t ∧
      Frame [⟨byteAddr g.stack, 44⟩] s.mem t.mem ∧ Keeps [] s t ∧ savedFlag g t = s.gpr .ebx := by
  unfold stackAt
  refine wp_stm (B := s.gpr .esp) rfl
    (by rw [h.address (by decide)]; exact h.inner.write (by decide)) fun t T => WP.block_nil ?_
  have M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 zeroOffset) (s.gpr .ebx) := by
    rw [T.mem, h.address (by decide)]
  have F : Frame [⟨byteAddr g.stack, 44⟩] s.mem t.mem := by
    rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  have K : Keeps [] s t := T.keeps _
  refine ⟨h.after (F.sub ?_) K (congrFun T.gpr .esp), F, K, ?_⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide)⟩
  · unfold savedFlag
    rw [M, Mem.readW_writeW_self32]

theorem callArgs_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block callArgs) s fun t => Context g bs t ∧ Arguments g (publicArgument g) 10 t ∧
      Frame [⟨byteAddr g.stack, 44⟩] s.mem t.mem ∧ Keeps [.eax] s t ∧ savedFlag g t = s.gpr .ebx := by
  have code : callArgs = [.store (stackAt zeroOffset) .ebx] ++ (List.range 10).flatMap prepare := rfl
  rw [code, WP.block_append_iff]
  refine WP.mono (storeFlag_ok h) ?_
  rintro u ⟨hu, F, K, flag⟩
  refine WP.mono (publicArgs_ok hu) ?_
  rintro t ⟨ht, args, Ft, Kt⟩
  refine ⟨ht, args, F.trans (Ft.sub ?_), (K.mono (by simp)).trans Kt, (savedFlag_frame Ft).trans flag⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩

end VG.Proof.RsaPkcs1Enc.X86.Enc
