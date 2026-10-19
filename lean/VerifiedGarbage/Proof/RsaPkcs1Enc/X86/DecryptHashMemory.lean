module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashInit
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptHashLayout

/-! # Hash argument preparation preserves scratch buffers and hash representations -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem argsFrame_hash {g : Geometry} {m m' : Mem}
    (F : Frame [⟨byteAddr g.stack, 80⟩] m m') : Frame (hashWrites g) m m' := F.sub (by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, by simp [hashWrites], fun _ hx => hx⟩)

theorem scratchBytes_args {g : Geometry} {bs : Fin 9 → List Byte} {s t : State} {d n : Nat}
    (h : Context g bs s) (fit : d + n ≤ 8448) (F : Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem) :
    Spec.Rsa.bytesAt t.mem (g.scratch d n).base n = Spec.Rsa.bytesAt s.mem (g.scratch d n).base n := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by omega)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact (h.argsScratch (by decide : 80 ≤ 160) fit).symm

theorem repr_args {g : Geometry} {bs : Fin 9 → List Byte} {s t : State} {msg : List Byte}
    (h : Context g bs s) (F : Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem)
    (repr : Spec.Sha256.Repr s.mem (g.scratch sSt 96).base msg) :
    Spec.Sha256.Repr t.mem (g.scratch sSt 96).base msg := by
  apply repr_frame F ?_ repr
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact (h.argsScratch (by decide : 80 ≤ 160) (by decide : sSt + 96 ≤ 8448)).symm

theorem scratchBytes_callee {g : Geometry} {bs : Fin 9 → List Byte} {s t : State} {d n : Nat} {wr : List Region}
    (h : Context g bs s) (fit : d + n ≤ 8448) (F : Frame (wr ++ [g.calleeRegion]) s.mem t.mem)
    (separate : ∀ r ∈ wr, (g.scratch d n).Disjoint r) :
    Spec.Rsa.bytesAt t.mem (g.scratch d n).base n = Spec.Rsa.bytesAt s.mem (g.scratch d n).base n := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by omega)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact separate r hr
  · obtain rfl := List.mem_singleton.mp hr
    exact (h.calleeScratch fit).symm

end VG.Proof.RsaPkcs1Enc.X86.Dec
