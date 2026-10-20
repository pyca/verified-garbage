module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialFrame
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialTable
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The trial loop writes only its control frame -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.RsaKeyGen

def trialRegs : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp]

structure TrialInputs (s : State) (base : Addr) (input table : BitVec 32) (len entries : Nat) : Prop where
  frame : TrialFrame s base
  lenPos : 2 ≤ len
  lenEven : len % 2 = 0
  lenBound : len < 2 ^ 32
  entriesPos : 1 ≤ entries
  entriesBound : entries ≤ 1024
  inputFit : input.toNat + len ≤ 2 ^ 32
  tableFit : table.toNat + 8 * entries ≤ 2 ^ 32
  inputRead : ∀ i < len, InRegions (s.rd ++ s.wr) (off (input.setWidth 64) i) 1
  tableRead : ∀ d, d + 4 ≤ 8 * entries → InRegions (s.rd ++ s.wr) (off (table.setWidth 64) d) 4
  inputApart : Region.Disjoint ⟨input.setWidth 64, len⟩ ⟨base, 16⟩
  tableApart : Region.Disjoint ⟨table.setWidth 64, 8 * entries⟩ ⟨base, 16⟩
  values : TrialTableReady s.mem (table.setWidth 64) entries

structure TrialContext (s : State) (base : Addr) (t : State) : Prop where
  frame : TrialFrame t base
  mem : Frame [⟨base, 16⟩] s.mem t.mem
  keeps : Keeps trialRegs s t

theorem TrialContext.refl {s : State} {base : Addr} (F : TrialFrame s base) : TrialContext s base s :=
  ⟨F, Frame.refl _ _, Keeps.refl _ _⟩

theorem TrialContext.after {s t u : State} {base : Addr} {rs : List Reg} (C : TrialContext s base t)
    (K : Keeps rs t u) (regs : ∀ r ∈ rs, r ∈ trialRegs) (mem : Frame [⟨base, 16⟩] t.mem u.mem) :
    TrialContext s base u :=
  ⟨C.frame.keeps (K.mono regs) (by decide), C.mem.trans mem, C.keeps.trans (K.mono regs)⟩

theorem TrialContext.unchanged {s t u : State} {base : Addr} {rs : List Reg} (C : TrialContext s base t)
    (K : Keeps rs t u) (regs : ∀ r ∈ rs, r ∈ trialRegs) (mem : u.mem = t.mem) : TrialContext s base u :=
  C.after K regs (by rw [mem]; exact Frame.refl _ _)

theorem TrialContext.upd {s t u : State} {base : Addr} {r : Reg} {v : BitVec 32}
    (C : TrialContext s base t) (U : Upd t u r v) (hr : r ≠ .esp) : TrialContext s base u := by
  refine C.unchanged U.keeps ?_ U.mem
  intro q hq
  obtain rfl := List.mem_singleton.mp hq
  cases q <;> simp_all [trialRegs]

theorem TrialContext.store {s t u : State} {base : Addr} {d : Nat} {v : BitVec 32}
    (C : TrialContext s base t) (U : Mupd t u (t.mem.writeW (off base d) v)) (hd : d + 4 ≤ 16) :
    TrialContext s base u :=
  C.after (U.keeps trialRegs) (fun _ h => h) (by rw [U.mem]; exact trialFrame_store hd v)

theorem TrialContext.fupd {s t u : State} {base : Addr}
    (C : TrialContext s base t) (U : Fupd t u) : TrialContext s base u :=
  C.unchanged (U.keeps trialRegs) (fun _ h => h) U.mem

theorem TrialContext.inputByte {s t : State} {base : Addr} {input table : BitVec 32} {len entries i : Nat}
    (R : TrialInputs s base input table len entries) (C : TrialContext s base t) (hi : i < len) :
    t.mem (off (input.setWidth 64) i) = s.mem (off (input.setWidth 64) i) :=
  C.mem.bytes (R := ⟨input.setWidth 64, len⟩) (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact R.inputApart)
    (by show len ≤ 2 ^ 64; have := R.lenBound; omega) hi

theorem TrialContext.tableWord {s t : State} {base : Addr} {input table : BitVec 32} {len entries d : Nat}
    (R : TrialInputs s base input table len entries) (C : TrialContext s base t) (hd : d + 4 ≤ 8 * entries) :
    t.mem.readW (off (table.setWidth 64) d) 32 = s.mem.readW (off (table.setWidth 64) d) 32 := by
  exact C.mem.readW (r := ⟨table.setWidth 64, 8 * entries⟩) (Offset.contains_base _ hd (by have := R.entriesBound; omega))
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact R.tableApart) (by decide)

theorem TrialContext.inputBytes {s t : State} {base : Addr} {input table : BitVec 32} {len entries : Nat}
    (R : TrialInputs s base input table len entries) (C : TrialContext s base t) :
    Spec.Rsa.bytesAt t.mem (input.setWidth 64) len = Spec.Rsa.bytesAt s.mem (input.setWidth 64) len := by
  apply List.map_congr_left
  intro i hi
  exact C.inputByte R (List.mem_range.mp hi)
end VG.Proof.Dsa.X86.Generation
