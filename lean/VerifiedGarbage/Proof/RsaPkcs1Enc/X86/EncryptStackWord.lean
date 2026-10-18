module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncryptContext
public import VerifiedGarbage.Proof.Framework.CallLay

/-! # Copying cdecl arguments into the local outgoing call area -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Enc
open VG VG.X86 VG.X86.Wp VG.Impl.RsaPkcs1Enc.X86.Encrypt VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem Context.address {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) {d : Nat} (hd : d < VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes + 20 + 56) :
    addr (s.gpr .esp) d = byteAddr g.stack + BitVec.ofNat 64 d := by
  rw [h.sp]
  exact h.valid.offsetAddr hd

theorem Context.readArg {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) {j : Nat} (hj : j < 14) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes + 20 + 4 * j)) 4 := by
  rw [h.address (by omega)]
  have read := CallLay.inRegions_sub (off := 4 * j) h.argumentsRead (l := 4) (by omega) (by decide)
  change InRegions (s.rd ++ s.wr)
    (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes + 20) + BitVec.ofNat 64 (4 * j)) 4 at read
  rw [Offset.add_add] at read
  exact read

theorem Context.argumentValue {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) {j : Nat} (hj : j < 14) :
    s.mem.readW (addr (s.gpr .esp) (VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes + 20 + 4 * j)) 32 = g.argument j := by
  rw [h.address (by omega)]
  exact h.arguments j hj

theorem copyArgument_ok (s : State) {g : Geometry} {bs : Fin 5 → List Byte}
    (h : Context g bs s) {i j : Nat} (hi : i < 14) (hj : j < 10) :
    WP isa (.block (copyArgument i j)) s fun t =>
      Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) (g.argument i) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold copyArgument incoming stackAt
  refine wp_ldm rfl (h.readArg hi) fun u U => ?_
  refine wp_stm (B := s.gpr .esp) (U.other .esp (by decide))
    (by rw [U.wr, h.address (by omega)]; exact h.inner.write (by simp only [VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes]; omega))
    fun t T => WP.block_nil ?_
  have M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) (g.argument i) := by
    rw [T.mem, U.gpr, U.mem, h.argumentValue hi, h.address (by omega)]
  have K : Keeps [.eax] s t := U.keeps.trans (T.keeps _)
  have F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem := by
    rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), M, F, K⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by simp only [VG.Impl.RsaPkcs1Enc.X86.Encrypt.frameBytes]; omega)⟩

end VG.Proof.RsaPkcs1Enc.X86.Enc
