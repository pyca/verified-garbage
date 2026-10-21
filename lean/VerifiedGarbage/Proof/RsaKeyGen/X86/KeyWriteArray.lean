module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Proof.Bignum.X86.ExportTruncated
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

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

theorem writeArray_ok {s : State} {B : Addr} {Z n j pointer length len : Nat} {p : BitVec 32}
    (h : Ws s B Z n 32) (hj : j < 32)
    (hp : pointer + 4 ≤ hdr) (hl : length + 4 ≤ hdr)
    (pointerEq : s.mem.readW (off B pointer) 32 = p)
    (lengthEq : s.mem.readW (off B length) 32 = BitVec.ofNat 32 len)
    (positive : 0 < len) (bound : len ≤ 4 * n)
    (fit : p.toNat + len ≤ 2 ^ 32) (write : InRegions s.wr (p.setWidth 64) len)
    (separate : Region.Disjoint ⟨B, Z⟩ ⟨p.setWidth 64, len⟩)
    (zero : num s.mem B n aZero = 0) (accept : Bool)
    (mask : slot s.mem B kOk = if accept then 1 else 0) :
    WP isa (writeArray n j pointer length) s fun t =>
      Ws t B Z n 32 ∧
      Spec.Rsa.bytesAt t.mem (p.setWidth 64) len =
        Spec.Rsa.i2osp ((if accept then num s.mem B n j else 0) % 2 ^ (8 * len)) len ∧
      Frame [⟨off B (arr n j), S n⟩, ⟨p.setWidth 64, len⟩] s.mem t.mem ∧
      (∀ d, d + 4 ≤ hdr → slot t.mem B d = slot s.mem B d) ∧
      (∀ k, k < 32 → k ≠ j → num t.mem B n k = num s.mem B n k) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fits := h.arr_fit hj
  have fit64 := h.fit64 hj
  have head := h.hdr_le
  unfold writeArray seqs
  refine WP.seq (WP.mono (sel_ok h hj (by decide) hj (by decide)
    (by rw [mask]; cases accept <;> decide)) fun u ⟨hu, Ou, selected, Ku⟩ => ?_)
  have raw : Outside B (arr n j) (S n) s.mem u.mem := by
    intro a ha
    apply Ou a
    intro r hr
    change r ∈ [(arr n j, S n)] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact ha
  have ownFrame := VG.Proof.Bignum.outside_frame raw fit64
  have chosen : num u.mem B n j = if accept then num s.mem B n j else 0 := by
    rw [selected, mask, zero]
    cases accept <;> rfl
  have Pu : u.mem.readW (off B pointer) 32 = p := by
    apply BitVec.eq_of_toNat_eq
    exact (Ou.slot hp (by simp)).trans (congrArg BitVec.toNat pointerEq)
  have Lu : u.mem.readW (off B length) 32 = BitVec.ofNat 32 len := by
    apply BitVec.eq_of_toNat_eq
    exact (Ou.slot hl (by simp)).trans (congrArg BitVec.toNat lengthEq)
  refine WP.seq (wp_movS (readSrc_sc hu.workspace (by omega)) fun a A _ => ?_)
  have ha := hu.rest A.keeps
  refine wp_movS (readSrc_sc ha.workspace (by omega)) fun v V _ => WP.block_nil ?_
  have K : Keeps [.ebx, .ecx] u v := (A.keeps.mono (by decide)).trans (V.keeps.mono (by decide))
  have memory : v.mem = u.mem := V.mem.trans A.mem
  have dest : v.gpr .ebx = p := by rw [V.other _ (by decide), A.gpr, Pu]
  have count : v.gpr .ecx = BitVec.ofNat 32 len := by rw [V.gpr, A.mem, Lu]
  have hv := hu.rest K
  refine WP.mono (VG.Proof.Bignum.X86.storeBE_truncated_ok hv.workspace positive bound
    (by change arr n j + 4 * n ≤ Z; unfold S at fits; omega) count
    (by rw [dest]; exact fit) (by rw [dest, K.2.2, Ku.2.2]; exact write)
    (by rw [dest]; exact separate.sub_left (Offset.sub_base B
      (by change arr n j + len ≤ Z; unfold S at fits; omega))))
    fun t ⟨value, F, Kt⟩ => ?_
  rw [dest, memory] at value F
  change Frame [⟨p.setWidth 64, len⟩] u.mem t.mem at F
  change Spec.Rsa.bytesAt t.mem (p.setWidth 64) len =
    Spec.Rsa.i2osp (num u.mem B n j % 2 ^ (8 * len)) len at value
  have all : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
    (Ku.mono (by decide)).trans ((K.mono (by decide)).trans (Kt.mono (by decide)))
  refine ⟨h.rest all, ?_, ?_, ?_, ?_, all⟩
  · rw [chosen] at value
    exact value
  · exact (ownFrame.mono (by simp)).trans (F.mono (by simp))
  · intro d hd
    change w32 t.mem B d = w32 s.mem B d
    rw [output_word h separate F (by omega)]
    exact Ou.slot hd (by simp)
  · intro k hk different
    rw [output_num h separate F hk]
    exact Ou.num (by intro a ha; obtain rfl := List.mem_singleton.mp ha; exact Ne.symm different)
      (by simp) (h.fit64 hk)

end VG.Proof.RsaKeyGen.X86.Key
