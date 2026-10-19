module
public import VerifiedGarbage.Impl.Rsa.X86.Div
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Insert one division bit into an even native-word array -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Div

theorem insertBit_raw {s : State} {base : Addr} {size dst : Nat} (hs : Scr s base size)
    (fit : dst + 4 ≤ size) :
    WP isa (.block (insertBit dst)) s fun t =>
      t.mem = s.mem.writeW (off base dst) (s.mem.readW (off base dst) 32 + s.gpr .ebx) ∧
      Keeps [.eax] s t := by
  unfold insertBit
  refine wp_movS (readSrc_sc hs fit) fun u U _ => ?_
  refine wp_addS rfl fun v V _ => ?_
  have hv := (hs.of_keeps U.keeps (by decide)).of_keeps V.keeps (by decide)
  refine wp_storeS (hv.ea (by omega)) (hv.write fit) fun t T => WP.block_nil ?_
  refine ⟨?_, (U.keeps.trans V.keeps).trans (T.keeps _)⟩
  rw [T.mem, V.mem, U.mem, V.gpr, U.gpr, U.other .ebx (by decide)]

theorem insertBit_ok {s : State} {base : Addr} {size n dst : Nat} (hs : Scr s base size)
    (hn : 0 < n) (fit : dst + 4 * n ≤ size) (bit : (s.gpr .ebx).toNat ≤ 1) :
    WP isa (.block (insertBit dst)) s fun t =>
      Outside base dst (4 * n) s.mem t.mem ∧ Keeps [.eax] s t ∧
      (val32 s.mem base dst n % 2 = 0 →
        val32 t.mem base dst n = val32 s.mem base dst n + (s.gpr .ebx).toNat) := by
  refine WP.mono (insertBit_raw hs (by omega)) ?_
  rintro t ⟨mem, rest⟩
  have outside := writeW32_outside s.mem base (d := dst)
    (s.mem.readW (off base dst) 32 + s.gpr .ebx) (by have := hs.nowrap; omega)
  rw [← mem] at outside
  refine ⟨outside.mono (Nat.le_refl _) (by omega), rest, ?_⟩
  intro even
  have low (m : Mem) : val32 m base dst n =
      w32 m base dst + 2 ^ 32 * val32 m base (dst + 4) (n - 1) := by
    rw [show n = (n - 1) + 1 by omega]
    rfl
  rw [low s.mem] at even
  have lowEven : (s.mem.readW (off base dst) 32).toNat % 2 = 0 := by
    change w32 s.mem base dst % 2 = 0
    omega
  have wordBound := (s.mem.readW (off base dst) 32).isLt
  have nowrap := hs.nowrap
  have high := outside.val32 (d := dst + 4) (k := n - 1) (by omega) (by omega)
  rw [low t.mem, low s.mem, high]
  have head : w32 t.mem base dst = w32 s.mem base dst + (s.gpr .ebx).toNat := by
    rw [mem, w32_write_self, BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  rw [head]
  omega
end VG.Proof.Rsa.X86.Div
