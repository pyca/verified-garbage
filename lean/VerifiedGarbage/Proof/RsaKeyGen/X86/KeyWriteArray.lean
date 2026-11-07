module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Bignum.X86.StoreBE
import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.X86.ExportBE
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Masked native key output preserves every other array and header word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key
open VG.Proof.Bignum.X86 (byteAddr)

theorem output_word {s : State} {B : Addr} {Z n d : Nat} {m m' : Mem} {p : BitVec 32} {len : Nat}
    (h : Ws s B Z n 32) (separate : Region.Disjoint ⟨B, Z⟩ ⟨p.setWidth 64, len⟩)
    (F : Frame [⟨p.setWidth 64, len⟩] m m') (bound : d + 4 ≤ Z) : w32 m' B d = w32 m B d := by
  unfold w32
  rw [F.readW (r := ⟨B, Z⟩) (a := off B d) (w := 32)
    (Scr.contains h.workspace.nowrap bound)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)]

theorem output_num {s : State} {B : Addr} {Z n j : Nat} {m m' : Mem} {p : BitVec 32} {len : Nat}
    (h : Ws s B Z n 32) (separate : Region.Disjoint ⟨B, Z⟩ ⟨p.setWidth 64, len⟩)
    (F : Frame [⟨p.setWidth 64, len⟩] m m') (index : j < 32) : num m' B n j = num m B n j := by
  apply val32_congr
  intro k hk
  have fits := h.arr_fit index
  unfold S at fits
  exact output_word h separate F (by omega)

end VG.Proof.RsaKeyGen.X86.Key
