module

public import VerifiedGarbage.Proof.Dsa.X86.StreamTiming
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Dsa.X86.Stream

/-! # Interpreting the streaming taint certificate with one scratch region -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86

theorem stream_wf {s : State} {base : Addr} {size : Nat} (S : Scr s base size)
    (hw : s.wr = [⟨base, size⟩]) (hz : 1408 ≤ size) : VG.X86.Taint.Wf streamEntryTaint s := by
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _
    rw [hw]
    refine ⟨List.Forall₂.cons hz .nil, by simp, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact S.nowrap
  · intro p hp
    obtain rfl := List.mem_singleton.mp hp
    change addr (s.gpr .edi) 0 = (VG.X86.Taint.region s 0).base
    simpa only [addr, BitVec.add_zero, VG.X86.Taint.region, hw, List.getD_cons_zero] using S.edi
  · intro p hp; cases hp
  · intro h; cases h
  · intro p hp; cases hp

theorem stream_slot {i k : Nat} (H : streamEntryTaint.slots.has i k = true) : i = 0 ∧ 20 ≤ k ∧ k < 24 := by
  change (Slots.ofList [(0, 20, 4)]).has i k = true at H
  rw [Slots.has_ofList] at H
  obtain ⟨slot, Hslot, I, Lo, Hi⟩ := H
  obtain rfl := List.mem_singleton.mp Hslot
  exact ⟨I.symm, Lo, Hi⟩

theorem stream_agree {s t : State} {base : Addr} {size : Nat}
    (S : Scr s base size) (T : Scr t base size)
    (ws : s.wr = [⟨base, size⟩]) (wt : t.wr = [⟨base, size⟩]) (hz : 1408 ≤ size)
    (P : s.mem.readW (off base sourcePointer) 32 = t.mem.readW (off base sourcePointer) 32) :
    VG.X86.Taint.Agree streamEntryTaint s t := by
  refine ⟨⟨?_, fun h => nomatch h⟩, fun _ => ws.trans wt.symm,
    stream_wf S ws hz, stream_wf T wt hz, ?_, ?_, (fun h => nomatch h), ?_⟩
  · intro reg hr
    have H : reg = .edi := List.mem_singleton.mp (RegSet.mem_ofList.mp hr)
    subst reg
    exact BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)
  · intro i k hk
    obtain ⟨rfl, Lo, Hi⟩ := stream_slot hk
    change k < 1408
    omega
  · intro i k hk
    obtain ⟨rfl, Lo, Hi⟩ := stream_slot hk
    change s.mem ((s.wr.getD 0 ⟨0, 0⟩).base + BitVec.ofNat 64 k) =
      t.mem ((t.wr.getD 0 ⟨0, 0⟩).base + BitVec.ofNat 64 k)
    rw [ws, wt]
    change s.mem (base + BitVec.ofNat 64 k) = t.mem (base + BitVec.ofNat 64 k)
    have A : base + BitVec.ofNat 64 k = off base sourcePointer + BitVec.ofNat 64 (k - 20) := by
      rw [off, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      change k = 20 + (k - 20)
      omega
    rw [A, Mem.readW_byte s.mem (off base sourcePointer) (i := k - 20) (by omega), Mem.readW_byte t.mem (off base sourcePointer) (i := k - 20) (by omega), P]
  · intro k _ hk; exact (Nat.not_lt_zero _ hk).elim

end VG.Proof.Dsa.X86
