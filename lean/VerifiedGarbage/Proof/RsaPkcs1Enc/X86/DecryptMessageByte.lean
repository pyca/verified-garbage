module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptScratch
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps
public import VerifiedGarbage.Proof.Framework.WriteBytes

/-! # Public PRF message bytes are written within their scratch buffer -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem messageStore_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (ptr : s.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg)
    {n : Nat} (bound : n < 16) (r : Reg8) :
    WP isa (.block [.store8 ⟨.edi, n⟩ r]) s fun t => Context g bs t ∧
      t.mem = s.mem.writeW ((g.scratch sMsg 16).base + BitVec.ofNat 64 n) ((s.gpr r.reg).setWidth 8) ∧
      Frame [g.scratch sMsg 16] s.mem t.mem ∧ Keeps [] s t := by
  have address : s.ea ⟨.edi, n⟩ = (g.scratch sMsg 16).base + BitVec.ofNat 64 n := by
    change byteAddr (s.gpr .edi + BitVec.ofNat 32 n) = _
    rw [ptr, BitVec.add_assoc, ← BitVec.ofNat_add,
      h.valid.scratchAddress (by unfold sMsg; omega : sMsg + n < 8448)]
    exact (Offset.add_add (byteAddr g.workspace) sMsg n).symm
  have write : InRegions s.wr ((g.scratch sMsg 16).base + BitVec.ofNat 64 n) 1 := by
    have raw := h.scratchWrite (by unfold sMsg; omega : sMsg + n + 1 ≤ 8448)
    change InRegions s.wr (byteAddr g.workspace + BitVec.ofNat 64 (sMsg + n)) 1 at raw
    rw [← Offset.add_add] at raw
    exact raw
  refine wp_storeByte address write fun t T => WP.block_nil ?_
  have F : Frame [g.scratch sMsg 16] s.mem t.mem := by
    rw [T.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega : n + 8 / 8 ≤ 16) (by omega))
  have K : Keeps [] s t := T.keeps _
  refine ⟨h.after (F.sub ?_) K (congrFun T.gpr .esp), T.mem, F, K⟩
  intro R hR
  obtain rfl := List.mem_singleton.mp hR
  exact ⟨g.workspaceRegion, by simp [bodyWrites], h.valid.scratchSub (by decide : sMsg + 16 ≤ 8448)⟩

theorem messagePut_ok {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (ptr : s.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg)
    {n : Nat} (bound : n < 16) (v : Nat) :
    WP isa (.block (putByte n v)) s fun t => Context g bs t ∧
      t.mem = s.mem.writeW ((g.scratch sMsg 16).base + BitVec.ofNat 64 n) (BitVec.ofNat 8 v) ∧
      Frame [g.scratch sMsg 16] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold putByte
  refine wp_movS rfl fun a A _ => ?_
  have ha := h.after (by rw [A.mem]; exact Frame.refl _ _) A.keeps (A.other .esp (by decide))
  refine WP.mono (messageStore_ok ha ((A.other .edi (by decide)).trans ptr) bound .al) ?_
  rintro t ⟨ht, M, F, K⟩
  refine ⟨ht, ?_, by rw [A.mem] at F; exact F, A.keeps.trans (K.mono (by simp))⟩
  change t.mem = a.mem.writeW ((g.scratch sMsg 16).base + BitVec.ofNat 64 n) ((a.gpr .eax).setWidth 8) at M
  rw [A.mem, A.gpr] at M
  simpa only [BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 32)] using M

end VG.Proof.RsaPkcs1Enc.X86.Dec
