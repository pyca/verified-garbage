module

public import VerifiedGarbage.Proof.Blake2.RISCV64.Round
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Words64

/-!
# BLAKE2 on RISC-V: words of either size

The accesses of the BLAKE2 code to words of `z.bits` bits, each proven once
for both sizes: the little-endian loads and stores a byte at a time
(`ldLE_ok`, `stLE_ok`) of the argument buffers, the aligned loads and stores
of the scratch space (`ld_ok`, `st_ok`), and the constants (`movImm_ok`).
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64

open VG VG.RISCV64
open VG.Impl.Blake2.RISCV64 (sz wd ws wreg T RT SB ldLE stLE movImm)

/-- What a block that writes the registers `a`, `b` and `c` leaves. -/
def Keeps3 (s s' : State) (a b c : Reg) : Prop :=
  (∀ q, q ≠ a → q ≠ b → q ≠ c → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
    s'.wr = s.wr

theorem zB_mul_le (z : Size) {j N : Nat} (hj : j < N) : zB z * j + zB z ≤ zB z * N := by
  have := Nat.mul_le_mul_left (zB z) (show j + 1 ≤ N by omega)
  rw [Nat.mul_succ] at this; exact this

theorem ldLE_ok {z : Size} {s : State} {d tmp tmp2 n : Reg} {off : Nat}
    (hdn : d ≠ n) (htn : tmp ≠ n) (hdt : d ≠ tmp) (h2n : tmp2 ≠ n) (h2t : tmp2 ≠ tmp)
    (hd2 : d ≠ tmp2) (ho : off + 7 < 2048)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) (zB z)) :
    WP isa (.block (ldLE z.bits d tmp tmp2 n off)) s fun s' =>
      (s'.gpr d).setWidth z.bits = s.mem.readW (s.gpr n + BitVec.ofNat 64 off) z.bits ∧
      Keeps3 s s' d tmp tmp2 := by
  cases z
  · simp only [ldLE, Size.bits, show (32 : Nat) ≠ 64 by decide, ite_false]
    refine WP.mono (ByteLoad.loadLE32_ok hdn htn hdt (by omega) h) fun s' e => ?_
    subst e
    refine ⟨by rw [RegUpd.gpr_write_self, lo32_ext], fun r h1 h2 _ => ?_, rfl, rfl, rfl⟩
    rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]
  · simp only [ldLE, Size.bits, ite_true]
    refine WP.mono (Words64.loadLE64_ok hdn htn hdt h2n h2t hd2 ho h) fun s' h => ?_
    exact ⟨by rw [h.gpr, BitVec.setWidth_eq], h.other, h.mem, h.rd, h.wr⟩

theorem stLE_ok {z : Size} {s : State} {v tmp tmp2 n : Reg} {off : Nat}
    (htv : tmp ≠ v) (htn : tmp ≠ n) (h2t : tmp2 ≠ tmp) (h2n : tmp2 ≠ n) (ho : off + 7 < 2048)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) (zB z)) :
    WP isa (.block (stLE z.bits v tmp tmp2 n off)) s fun s' =>
      (∀ r, r ≠ tmp → r ≠ tmp2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr v).setWidth z.bits) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases z
  · simp only [stLE, Size.bits, show (32 : Nat) ≠ 64 by decide, ite_false]
    refine WP.mono (ByteLoad.storeLE32_ok htv htn (by omega) h) fun s' e => ?_
    subst e
    exact ⟨fun r h1 _ => RegUpd.gpr_write_of_ne _ _ h1, rfl, rfl, rfl⟩
  · simp only [stLE, Size.bits, ite_true]
    refine WP.mono (Words64.storeLE64_ok htv htn h2t h2n ho h) fun s' h => ?_
    exact ⟨h.1, by rw [h.2.1, BitVec.setWidth_eq], h.2.2.1, h.2.2.2.1⟩

theorem ld_ok {z : Size} {s : State} {t n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % zB z = 0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) (zB z)) :
    WP isa (.block [.load (wd z.bits) t n off]) s fun s' =>
      (s'.gpr t).setWidth z.bits = s.mem.readW (s.gpr n + BitVec.ofNat 64 off) z.bits ∧
      (∀ q, q ≠ t → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ld ho ha h, RegUpd.gpr_write_self,
    ext_trunc, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun q hq => RegUpd.gpr_write_of_ne _ _ hq, rfl, rfl, rfl⟩

theorem st_ok {z : Size} {s : State} {t n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % zB z = 0)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) (zB z)) :
    WP isa (.block [.store (wd z.bits) t n off]) s fun s' =>
      s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr t).setWidth z.bits) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_st ho ha h, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem movImm_ok {z : Size} {s : State} {d : Reg} (hd : d ≠ T) (x : BitVec z.bits) :
    WP isa (.block (movImm z.bits d (x.setWidth 64))) s fun s' =>
      (s'.gpr d).setWidth z.bits = x ∧ (∀ q, q ≠ d → q ≠ T → s'.gpr q = s.gpr q) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases z
  · simp only [movImm, Size.bits, show (32 : Nat) ≠ 64 by decide, ite_false]
    refine WP.mono (ByteLoad.li32_ok _) fun s' e => ?_
    subst e
    refine ⟨by rw [RegUpd.gpr_write_self, lo32_sext, lo32_ext], fun q h1 _ => ?_, rfl, rfl, rfl⟩
    exact RegUpd.gpr_write_of_ne _ _ h1
  · simp only [movImm, Size.bits, ite_true]
    refine WP.mono (Words64.movImm64_ok hd _) fun s' h => ?_
    exact ⟨by rw [h.1, BitVec.setWidth_eq, BitVec.setWidth_eq], h.2.1, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2.1⟩

end VG.Proof.Blake2.RISCV64
