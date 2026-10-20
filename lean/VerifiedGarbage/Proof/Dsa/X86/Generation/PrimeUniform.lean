module
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeControl

/-! # Count only uniform witnesses, without reducing out-of-range draws -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Ecdsa.X86

theorem primeUniformUpdate_ok {s : State} {base : Addr} {size uniform checks : Nat} {isUniform : Bool}
    (S : Scr s base size) (room : primeIsUniform + 4 ≤ size)
    (bound : uniform + 1 < 2 ^ 32) (checks32 : checks < 2 ^ 32)
    (flag : s.mem.readW (off base primeIsUniform) 32 = mask32 (isUniform = true))
    (count : s.mem.readW (off base primeUniform) 32 = BitVec.ofNat 32 uniform) :
    WP isa (.block (primeUniformUpdate checks)) s fun t =>
      t.mem.readW (off base primeUniform) 32 = BitVec.ofNat 32 (uniform + isUniform.toNat) ∧
      t.cf = some (decide (uniform + isUniform.toNat < checks)) ∧
      Outside base primeUniform 4 s.mem t.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold primeUniformUpdate
  refine wp_movS (v := mask32 (isUniform = true)) (by rw [readSrc_sc S room, flag]) fun a sa _ =>
    wp_movS rfl fun b ab _ => wp_subS rfl fun c bc _ => ?_
  have Kc : Keeps [.eax, .ecx] s c := ((sa.keeps.mono (by decide)).widen ab.keeps).widen bc.keeps
  have Sc := S.of_keeps Kc (by decide)
  have cr : primeUniform + 4 ≤ size := by unfold primeUniform primeIsUniform at *; omega
  have mc : c.mem = s.mem := by rw [bc.mem, ab.mem, sa.mem]
  refine wp_movS (v := BitVec.ofNat 32 uniform) (by rw [readSrc_sc Sc cr, mc, count]) fun d cd _ =>
    wp_addS rfl fun e de _ => ?_
  have value : e.gpr .eax = BitVec.ofNat 32 (uniform + isUniform.toNat) := by
    rw [de.gpr, cd.gpr, cd.other _ (by decide), bc.gpr, ab.gpr, ab.other _ (by decide), sa.gpr]
    have negmask : (0 : BitVec 32) - mask32 (isUniform = true) = BitVec.ofNat 32 isUniform.toNat := by
      cases isUniform <;> decide +kernel
    rw [negmask, ← BitVec.ofNat_add]
  have Ke := (Kc.widen cd.keeps).widen de.keeps
  have Se := S.of_keeps Ke (by decide)
  refine wp_storeS (Se.ea (by omega)) (Se.write cr) fun f ef => wp_cmpi fun t ft ct _ => WP.block_nil ?_
  refine ⟨by rw [ft.mem, ef.mem, Mem.readW_writeW_self32, value], ?_, ?_, Ke.trans ((ef.keeps _).trans (ft.keeps _))⟩
  · rw [ct, ef.gpr, value, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by cases isUniform <;> simp only [Bool.toNat_true, Bool.toNat_false] <;> omega),
      Nat.mod_eq_of_lt checks32]
  · rw [ft.mem, ef.mem, de.mem, cd.mem, mc]
    exact writeW32_outside _ _ _ (by have := S.nowrap; omega)
end VG.Proof.Dsa.X86.Generation
