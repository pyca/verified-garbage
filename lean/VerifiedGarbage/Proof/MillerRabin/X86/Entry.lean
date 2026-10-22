module

public import VerifiedGarbage.Proof.MillerRabin.X86.EntryArgs
import VerifiedGarbage.Proof.Framework.Offset

/-! # Save registers and retain incoming arguments in the allocated frame -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86

structure EntryReady (s t : State) : Prop where
  context : ProtectedContext t (wsOf s) (bytesOf s)
  room : CallRoom (t.gpr .esp) (wsOf s) (bytesOf s)
  frame : Frame [entryFrame s] s.mem t.mem
  saved : Spill.Saved t.mem (off (byteAddr (t.gpr .esp)))
    (allocFrame VG.Impl.MillerRabin.X86.frameBytes s).gpr savedRegisters
  length : t.mem.readW (off (byteAddr (t.gpr .esp)) savedLength) 32 = arg s 1
  keeps : Keeps [.eax, .edi] (allocFrame VG.Impl.MillerRabin.X86.frameBytes s) t

theorem entry_ok {s : State} (A : RoundABI s) :
    WP isa (.block entry) (allocFrame VG.Impl.MillerRabin.X86.frameBytes s) (EntryReady s) := by
  let a := allocFrame VG.Impl.MillerRabin.X86.frameBytes s
  have slotsFit : Spill.Fits VG.Impl.MillerRabin.X86.frameBytes savedRegisters := by decide
  have stackFit : (a.gpr .esp).toNat + VG.Impl.MillerRabin.X86.frameBytes ≤ 2 ^ 32 := by
    rw [A.allocated_sp]
    have := (s.gpr .esp).isLt
    change (s.gpr .esp).toNat - 1132 + 1132 ≤ 2 ^ 32
    omega
  have contains (p : Reg × Nat) (hp : p ∈ savedRegisters) :
      (entryFrame s).Contains (off (byteAddr (a.gpr .esp)) p.2) 4 :=
    Offset.contains_base _ (slotsFit.1 p hp) (by have := slotsFit.1 p hp; change p.2 + 4 ≤ 1132 at this; omega)
  change WP isa (.block (Spill.saveCode .esp savedRegisters ++ _)) a _
  refine Spill.save_ofNat_ok savedRegisters slotsFit stackFit (fun p hp => ?_) fun u M => ?_
  · exact ⟨_, List.mem_cons_self, contains p hp⟩
  have frameU : Frame [entryFrame s] s.mem u.mem := by
    rw [M.mem]
    exact Spill.saveMem_frame (R := entryFrame s) (by simp) _ _ _ _ contains
  have savedU : Spill.Saved u.mem (off (byteAddr (a.gpr .esp))) a.gpr savedRegisters := by
    rw [M.mem]
    exact Spill.saveMem_saved_ofNat _ _ _ slotsFit (by decide)
  have spU : u.gpr .esp = a.gpr .esp := congrFun M.gpr .esp
  have rdU : u.rd = s.rd := M.rd
  refine wp_movS (A.read_argument (i := 0) (by decide) spU rdU frameU) fun v Uv _ => ?_
  have spV : v.gpr .esp = a.gpr .esp := (Uv.other .esp (by decide)).trans spU
  have frameV : Frame [entryFrame s] s.mem v.mem := by rw [Uv.mem]; exact frameU
  refine wp_movS (A.read_argument (i := 1) (by decide) spV (Uv.rd.trans rdU) frameV) fun z Uz _ => ?_
  have spZ : z.gpr .esp = a.gpr .esp := (Uz.other .esp (by decide)).trans spV
  have ctxZ := A.context spZ (Uz.wr.trans (Uv.wr.trans M.wr))
    ((Uz.other .edi (by decide)).trans Uv.gpr)
  refine wp_storeS (ctxZ.ea_stack (by decide)) (ctxZ.write_sp (by decide)) fun t Mt => WP.block_nil ?_
  have K : Keeps [.eax, .edi] a t :=
    (((M.keeps _).trans (Uv.keeps.mono (by decide))).trans (Uz.keeps.mono (by decide))).trans (Mt.keeps _)
  have spT : t.gpr .esp = a.gpr .esp := K.1 _ (by decide)
  have memory : t.mem = u.mem.writeW (off (byteAddr (a.gpr .esp)) savedLength) (arg s 1) := by
    rw [Mt.mem, spZ, Uz.gpr, Uz.mem, Uv.mem]
  have frameT : Frame [entryFrame s] s.mem t.mem := by
    rw [memory]
    exact frameU.writeW (r := entryFrame s) (by simp) _
      (Offset.contains_base (byteAddr (a.gpr .esp)) (k := VG.Impl.MillerRabin.X86.frameBytes)
        (by decide : savedLength + 4 ≤ VG.Impl.MillerRabin.X86.frameBytes) (by decide))
  refine ⟨ctxZ.of_keeps (Mt.keeps []), A.call_room spT, frameT, ?_, ?_, K⟩
  · rw [spT]
    apply savedU.of_readW
    intro p hp
    rw [memory, Mem.readW_writeW_sep ?_ (by decide)]
    have small : p.2 + 4 ≤ savedLength := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    exact Offset.sep _ (.inl small) (by have := slotsFit.1 p hp; omega) (by decide)
  · rw [spT, memory, Mem.readW_writeW_self32]

end VG.Proof.MillerRabin.X86
