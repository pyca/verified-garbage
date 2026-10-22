module

public import VerifiedGarbage.Proof.MillerRabin.X86.Transfer
public import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset

/-! # Disjoint workspace and stack buffers for the saved protected bytes -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86

structure ProtectedContext (s : State) (base : Addr) (bytes : Nat) : Prop where
  ws : Scr s base bytes
  stack : InRegions s.wr (byteAddr (s.gpr .esp)) VG.Impl.MillerRabin.X86.frameBytes
  stackFit : (s.gpr .esp).toNat + VG.Impl.MillerRabin.X86.frameBytes ≤ 2 ^ 32
  apart : Region.Disjoint ⟨base, bytes⟩
    ⟨byteAddr (s.gpr .esp), VG.Impl.MillerRabin.X86.frameBytes⟩

theorem byteAddr_toNat (p : BitVec 32) : (byteAddr p).toNat = p.toNat := by
  rw [byteAddr, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans p.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

namespace ProtectedContext

theorem ea_stack {s : State} {base : Addr} {bytes d : Nat}
    (h : ProtectedContext s base bytes) (hd : d < VG.Impl.MillerRabin.X86.frameBytes) :
    s.ea (VG.Impl.MillerRabin.X86.sp d) = off (byteAddr (s.gpr .esp)) d :=
  addr_eq (by
    change (s.gpr .esp).toNat + d < 2 ^ 32
    have := h.stackFit
    omega)

theorem read_sp {s : State} {base : Addr} {bytes d : Nat}
    (h : ProtectedContext s base bytes) (hd : d + 4 ≤ VG.Impl.MillerRabin.X86.frameBytes) :
    readSrc s (.mem (VG.Impl.MillerRabin.X86.sp d)) =
      some (s.mem.readW (off (byteAddr (s.gpr .esp)) d) 32) := by
  show s.load32 (s.ea (VG.Impl.MillerRabin.X86.sp d)) = _
  have rd : InRegions (s.rd ++ s.wr) (off (byteAddr (s.gpr .esp)) d) 4 := by
    obtain ⟨r, hr, hc⟩ := VG.CallLay.inRegions_sub h.stack hd (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [h.ea_stack (by omega), State.load32, ite_eq_left rd]

theorem write_sp {s : State} {base : Addr} {bytes d : Nat}
    (h : ProtectedContext s base bytes) (hd : d + 4 ≤ VG.Impl.MillerRabin.X86.frameBytes) :
    InRegions s.wr (off (byteAddr (s.gpr .esp)) d) 4 :=
  VG.CallLay.inRegions_sub h.stack hd (by decide)

theorem stack_address {s : State} {base : Addr} {bytes d : Nat}
    (h : ProtectedContext s base bytes) (hd : d < VG.Impl.MillerRabin.X86.frameBytes) :
    byteAddr (ptr32 (byteAddr (s.gpr .esp)) d) = off (byteAddr (s.gpr .esp)) d :=
  ptr32_addr (by rw [byteAddr_toNat]; have := h.stackFit; omega)

theorem stack_piece_apart {s : State} {base : Addr} {bytes f n : Nat}
    (h : ProtectedContext s base bytes) (hf : f + n ≤ VG.Impl.MillerRabin.X86.frameBytes) :
    Region.Disjoint ⟨base, bytes⟩ ⟨off (byteAddr (s.gpr .esp)) f, n⟩ :=
  h.apart.sub_right (Offset.sub_base _ hf)

theorem stack_frame_read {s : State} {base : Addr} {bytes f n d k : Nat} {m m' : Mem}
    (h : ProtectedContext s base bytes) (hf : f + n ≤ VG.Impl.MillerRabin.X86.frameBytes)
    (F : Frame [⟨off (byteAddr (s.gpr .esp)) f, n⟩] m m') (hd : d + k ≤ bytes) :
    m'.read (off base d) k = m.read (off base d) k := by
  have nw := h.ws.nowrap
  exact F.read (r := ⟨base, bytes⟩) (Offset.contains_base _ hd (by omega))
    (by intro r hr; rw [List.mem_singleton.mp hr]; exact h.stack_piece_apart hf) (by omega)

theorem stack_frame_readW {s : State} {base : Addr} {bytes f n d : Nat} {m m' : Mem}
    (h : ProtectedContext s base bytes) (hf : f + n ≤ VG.Impl.MillerRabin.X86.frameBytes)
    (F : Frame [⟨off (byteAddr (s.gpr .esp)) f, n⟩] m m') (hd : d + 4 ≤ bytes) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  simpa only [Mem.readW] using congrArg (BitVec.setWidth 32) (h.stack_frame_read hf F hd)

theorem ws_frame_read {s : State} {base : Addr} {bytes d n f k : Nat} {m m' : Mem}
    (h : ProtectedContext s base bytes) (hd : d + n ≤ bytes)
    (F : Frame [⟨off base d, n⟩] m m') (hf : f + k ≤ VG.Impl.MillerRabin.X86.frameBytes) :
    m'.read (off (byteAddr (s.gpr .esp)) f) k = m.read (off (byteAddr (s.gpr .esp)) f) k := by
  exact F.read (r := ⟨off (byteAddr (s.gpr .esp)) f, k⟩) (Region.contains_self _ _)
    (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact (h.apart.symm.sub_left (Offset.sub_base _ hf)).sub_right (Offset.sub_base _ hd))
    (by simp only [VG.Impl.MillerRabin.X86.frameBytes] at hf; omega)

theorem of_keeps {s t : State} {base : Addr} {bytes : Nat} {rs : List Reg}
    (h : ProtectedContext s base bytes) (K : Keeps rs s t)
    (di : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : ProtectedContext t base bytes := by
  have sp : t.gpr .esp = s.gpr .esp := K.1 _ esp
  exact ⟨h.ws.of_keeps K di esp, by rw [K.2.2, sp]; exact h.stack,
    by rw [sp]; exact h.stackFit, by rw [sp]; exact h.apart⟩

theorem to_stack {s : State} {base : Addr} {bytes d f n : Nat} {setup : List Instr}
    (h : ProtectedContext s base bytes) (positive : 0 < n) (small : n < 2 ^ 32)
    (hd : d + n ≤ bytes) (hf : f + n ≤ VG.Impl.MillerRabin.X86.frameBytes)
    (prepare : WP isa (.block setup) s fun t =>
      Keeps transferClobbers s t ∧ t.mem = s.mem ∧
      t.gpr .esi = ptr32 base d ∧ t.gpr .ebx = ptr32 (byteAddr (s.gpr .esp)) f ∧
      t.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa (.seq (.block setup) VG.Impl.Bignum.X86.copyBytes) s
      (TransferResult s (ptr32 base d) (ptr32 (byteAddr (s.gpr .esp)) f) n) := by
  have wfit := h.ws.nowrap
  have sfit := h.stackFit
  have wa := ptr32_addr (base := base) (d := d) (by omega)
  have sa := ptr32_addr (base := byteAddr (s.gpr .esp)) (d := f)
    (by rw [byteAddr_toNat]; omega)
  apply transfer_ok positive small
    (by rw [ptr32_toNat (by omega)]; omega)
    (by rw [ptr32_toNat (by rw [byteAddr_toNat]; omega), byteAddr_toNat]; omega)
    (by rw [wa]; exact h.ws.read hd)
    (by rw [sa]; exact VG.CallLay.inRegions_sub h.stack hf (by decide))
    (by rw [wa, sa]; exact (h.apart.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ hf))
    prepare

theorem from_stack {s : State} {base : Addr} {bytes d f n : Nat} {setup : List Instr}
    (h : ProtectedContext s base bytes) (positive : 0 < n) (small : n < 2 ^ 32)
    (hd : d + n ≤ bytes) (hf : f + n ≤ VG.Impl.MillerRabin.X86.frameBytes)
    (prepare : WP isa (.block setup) s fun t =>
      Keeps transferClobbers s t ∧ t.mem = s.mem ∧
      t.gpr .esi = ptr32 (byteAddr (s.gpr .esp)) f ∧ t.gpr .ebx = ptr32 base d ∧
      t.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa (.seq (.block setup) VG.Impl.Bignum.X86.copyBytes) s
      (TransferResult s (ptr32 (byteAddr (s.gpr .esp)) f) (ptr32 base d) n) := by
  have wfit := h.ws.nowrap
  have sfit := h.stackFit
  have wa := ptr32_addr (base := base) (d := d) (by omega)
  have sa := ptr32_addr (base := byteAddr (s.gpr .esp)) (d := f)
    (by rw [byteAddr_toNat]; omega)
  have readStack : InRegions (s.rd ++ s.wr) (off (byteAddr (s.gpr .esp)) f) n := by
    obtain ⟨r, hr, hc⟩ := VG.CallLay.inRegions_sub h.stack hf (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply transfer_ok positive small
    (by rw [ptr32_toNat (by rw [byteAddr_toNat]; omega), byteAddr_toNat]; omega)
    (by rw [ptr32_toNat (by omega)]; omega)
    (by rw [sa]; exact readStack)
    (by rw [wa]; exact h.ws.write hd)
    (by rw [wa, sa]; exact ((h.apart.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ hf)).symm)
    prepare

end ProtectedContext
end VG.Proof.MillerRabin.X86
