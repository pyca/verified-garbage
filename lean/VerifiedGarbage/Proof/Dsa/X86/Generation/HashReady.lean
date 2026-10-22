module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashAbsorb

/-! # Public streaming-call inputs, independent of seed contents and initial scratch -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

structure HashReady {H : Hash} (ok : HashOK H) (st data digest scratch sp : BitVec 32) (len : Nat) (s : State) : Prop where
  geometry : HashGeometry ok st data digest scratch len s
  registers : HashRegisters st data scratch len s
  stack : s.gpr .esp = sp

structure UpdateReady {H : Hash} (ok : HashOK H) (st data digest scratch sp : BitVec 32) (len : Nat) (s : State) : Prop
    extends HashReady ok st data digest scratch sp len s where
  edx : s.gpr .edx = data
  ecx : s.gpr .ecx = BitVec.ofNat 32 len
  eax : s.gpr .eax = 0

theorem HashReady.after {H : Hash} {ok : HashOK H} {st data digest scratch sp : BitVec 32} {len : Nat} {s t : State} {ws : List Region}
    (h : HashReady ok st data digest scratch sp len s) (A : After s ws t) : HashReady ok st data digest scratch sp len t :=
  ⟨h.geometry.after A, h.registers.after A, A.esp.trans h.stack⟩

theorem hash_init_ready {H : Hash} {ok : HashOK H} {st data digest scratch sp : BitVec 32} {len : Nat} {s : State}
    (h : HashReady ok st data digest scratch sp len s) :
    WP isa (H.callInit .ebx) s (HashReady ok st data digest scratch sp len) :=
  init_frame ok (h.geometry.init_args h.registers) (fun _ A _ => h.after A)

theorem hash_update_ready {H : Hash} {ok : HashOK H} {st data digest scratch sp : BitVec 32} {len : Nat} {s : State}
    (h : HashReady ok st data digest scratch sp len s) :
    WP isa (.block [.mov .edx (.reg .esi), .mov .ecx (.reg .edi), .mov .eax (.imm 0)]) s
      (UpdateReady ok st data digest scratch sp len) := by
  refine WP.mono (hash_update_setup h.registers) ?_
  rintro t ⟨R, edx, ecx, eax, _, K⟩
  exact ⟨⟨h.geometry.of_regions K.2.1 K.2.2 (K.1 _ (by decide)), R,
    (K.1 _ (by decide)).trans h.stack⟩, edx, ecx, eax⟩

end VG.Proof.Dsa.X86.Generation
