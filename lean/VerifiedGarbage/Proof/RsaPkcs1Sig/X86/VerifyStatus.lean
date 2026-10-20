module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyLocal
import VerifiedGarbage.Proof.Rsa.X86.PrivZeroTest
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyStackWord
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract

/-! # Save and mask the public operation's status without branching on it -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify

def savedStatus (g : Geometry) (s : State) : BitVec 32 :=
  s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 statusOffset) 32

theorem save_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block [.store (stackAt statusOffset) .eax]) s fun t => Context g bs t ∧
      savedStatus g t = s.gpr .eax ∧ Frame [localRegion g statusOffset 4] s.mem t.mem ∧ Keeps [] s t := by
  unfold stackAt
  refine wp_stm rfl (by rw [h.address (by decide)]; exact h.inner.write (by decide)) fun t T => WP.block_nil ?_
  have M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 statusOffset) (s.gpr .eax) := by
    rw [T.mem, h.address (by decide)]
  have F : Frame [localRegion g statusOffset 4] s.mem t.mem := by
    rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.after (F.sub ?_) (T.keeps []) (congrFun T.gpr .esp), ?_, F, T.keeps []⟩
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], localSub (by decide)⟩
  · unfold savedStatus
    rw [M, Mem.readW_writeW_self32]

theorem result_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block result) s fun t => Context g bs t ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx] s t ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (s.gpr .ebp = 0)).toNat &&& savedStatus g s := by
  unfold result
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86.PrivChecked.zeroTest_ok s) ?_
  rintro a ⟨value, M, K⟩
  have ha := h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide))
  unfold stackAt
  refine wp_ldm rfl (by rw [ha.address (by decide)]; exact ha.inner.read (by decide)) fun b B => ?_
  refine wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
  have kt : Keeps [.eax, .ecx] s t := (K.mono (by decide)).trans
    ((B.keeps.mono (by decide)).trans (T.keeps.mono (by decide)))
  have mt := T.mem.trans (B.mem.trans M)
  refine ⟨h.after (by rw [mt]; exact Frame.refl _ _) kt (kt.1 .esp (by decide)), mt, kt, ?_⟩
  rw [T.gpr, B.other .eax (by decide), value, B.gpr, ha.address (by decide), M]
  rfl

end VG.Proof.RsaPkcs1Sig.X86.Ver
