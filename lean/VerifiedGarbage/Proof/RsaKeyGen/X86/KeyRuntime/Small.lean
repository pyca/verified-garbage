module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Zero
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Omega

/-! # Small constants need one store after a shared runtime zero loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Mont.X86.Rt (PtrAt)

theorem write_zero {m : Mem} {B : Addr} {Z o k : Nat} (nw : B.toNat + Z ≤ 2 ^ 32)
    (fit : o + 4 * (k + 1) ≤ Z) (zero : val32 m B o (k + 1) = 0) (x : BitVec 32) :
    val32 (m.writeW (off B o) x) B o (k + 1) = x.toNat := by
  rw [val32] at zero ⊢
  have above : val32 m B (o + 4) k = 0 := by omega
  rw [w32_write_self]
  have O := writeW32_outside m B (d := o) x (by omega)
  rw [O.val32 (by omega) (by omega), above, Nat.mul_zero, Nat.add_zero]

theorem small_ok {s : State} {B : Addr} {Z n N j : Nat} (h : Ws s B Z n N)
    (w : Width) (x : BitVec 32)
    (fit : (Loc.array w j).offset n + 4 * (w.words n + 2) ≤ Z) :
    WP isa (small w j x) s fun t => Ws t B Z n N ∧
      Outside B (Loc.offset n (.array w j)) (4 * (w.words n + 2)) s.mem t.mem ∧
      val32 t.mem B (Loc.offset n (.array w j)) (w.words n + 2) = x.toNat ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have nowrap := h.old.workspace.nowrap
  unfold small
  refine WP.seq (WP.mono (zero_ok h w (.array w j) fit) fun a ⟨ha, Oa, V, Ka⟩ => ?_)
  refine ha.ptr_ok (.array w j) (by decide) (by decide) (by omega) fun b Kb mb P => ?_
  refine wp_movS rfl fun c C _ => ?_
  have Kac : Keeps [.eax, .ecx, .edx, .ebp] a c := (Kb.mono (by decide)).trans
    (C.keeps.mono (by decide))
  have hw := ha.full.rt.of_keeps Kac
  have pc : PtrAt c B .ebp (Loc.offset n (.array w j)) := by
    rw [PtrAt, C.other _ (by decide)]; exact P
  refine wp_storeS (VG.Proof.Mont.X86.Rt.ea_ptr hw pc (d := 0) (by omega))
    (VG.Proof.Mont.X86.Rt.ws_write hw (y := Loc.offset n (.array w j) + 0) (n := 4)
      (by omega)) fun t T => WP.block_nil ?_
  have memory : t.mem = a.mem.writeW (off B (Loc.offset n (.array w j))) x := by
    rw [T.mem, C.mem, mb, C.gpr, Nat.add_zero]
  have Ot : Outside B (Loc.offset n (.array w j)) 4 a.mem t.mem := by
    rw [memory]; exact writeW32_outside _ _ _ (by omega)
  have Kall : Keeps [.eax, .ecx, .edx, .ebp] s t := Ka.trans
    (Kac.trans (T.keeps _))
  have Oall := Oa.trans (Ot.mono (Nat.le_refl _) (by omega))
  refine ⟨h.keep Kall (Oall.mono (Nat.zero_le _) (by omega)), Oall, ?_, Kall⟩
  rw [memory]
  exact write_zero nowrap fit V x

end VG.Proof.RsaKeyGen.X86.KeyRuntime
