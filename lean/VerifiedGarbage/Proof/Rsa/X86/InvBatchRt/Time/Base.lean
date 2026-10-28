module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ops
public import VerifiedGarbage.Proof.Rsa.X86.InvTimeBase
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Weierstrass.X86.InvClob
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Slots
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Constant time of the batched inverse, one operation at a time

The constant-time analysis forgets the public words of the working space at a
store of a secret through a pointer it cannot place, as every array loop does,
while the code reads the arrays' addresses and the count from the header's
slots before every operation. So each operation is checked on its own
(`leaf`), from states whose slots agree because both runs satisfy `Bx` (the
slots hold addresses and lengths that depend only on the working space and the
modulus's length), in a view of the state with the working space as its only
writable region; the operations are joined by `RelCT.seq`, with `Bx` carried
through each by its correctness lemma.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt.Time

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt
open VG.Proof.Rsa.X86.InvTiming (Public)
open VG.Proof.Weierstrass.X86.Inv (wordClob)

/-- What each operation's check starts from: `edi` the working space, the slots and the count
public, the arguments public, the workspace's address the 15th. -/
def τS : VG.X86.Taint.T :=
  { regs := .ofList [.edi, .esp], flags := false, lens := [160], bases := [(.edi, 0, 0)],
    slots := VG.Slots.ofList [(0, 52, 48)], argLen := 68, argBases := [(60, 0)] }

/-- The state with every region readable and only the working space writable. -/
def view (s : State) (B : Addr) (Z : Nat) : State := s.withRegions (s.rd ++ s.wr) [⟨B, Z⟩]

theorem lift_exec {s z : State} {B : Addr} {Z : Nat} {c : Prog isa} {tr : List Leak}
    (hs : (⟨B, Z⟩ : Region) ∈ s.wr) (he : Exec isa c (view s B Z) tr z) :
    Exec isa c s tr (z.withRegions s.rd s.wr) := by
  have cw : Covers (view s B Z).wr s.wr := by
    apply Covers.of_mem
    intro r hr
    simp only [view, State.withRegions_wr, List.mem_singleton] at hr
    subst r
    exact hs
  have cr : Covers ((view s B Z).rd ++ (view s B Z).wr) (s.rd ++ s.wr) := by
    simp only [view, State.withRegions_rd]
    exact Covers.append_left (Covers.refl _) (cw.trans (Covers.of_mem fun r hr => List.mem_append_right _ hr))
  have E := VG.X86.Exec.widen he cr cw
  simpa only [view, State.withRegions_withRegions, State.withRegions_self] using E

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem callArg_view {s : State} {i : Nat} {v : BitVec 32}
    (h : VG.Proof.Bignum.X86.CallArgument s B Z i v) : VG.Proof.Bignum.X86.CallArgument (view s B Z) B Z i v := by
  obtain ⟨r, hr, hc⟩ := h.stack.read
  exact ⟨⟨⟨r, by simp only [view, State.withRegions_rd, State.withRegions_wr]; exact List.mem_append_left _ hr, hc⟩,
    h.stack.apart⟩, h.value⟩

theorem Bx.view {s : State} (h : Bx L s B Z len N) : Bx L (view s B Z) B Z len N := by
  obtain ⟨⟨⟨⟨edi, _, nw, stk⟩, fits, wpos, wle⟩, lenArg, wsArg, lenLe, layLen⟩, slots, room⟩ := h
  exact ⟨⟨⟨⟨edi, List.mem_singleton_self _, nw, stk⟩, fits, wpos, wle⟩,
    lenArg.imp fun _ ⟨l, e, c⟩ => ⟨l, e, callArg_view c⟩, callArg_view wsArg, lenLe, layLen⟩, slots, room⟩

/-- Both runs hold the same slot words: the arrays' addresses and the half count. -/
theorem slot_words {s t : State} (hs : Bx L s B Z len N) (ht : Bx L t B Z len N) :
    ∀ q < 12, w32 s.mem B (52 + 4 * q) = w32 t.mem B (52 + 4 * q) := by
  intro q hq
  rcases Nat.lt_or_ge q 11 with h | h
  · have e : ∀ q < 11, slot (cached.getD q 0) = some (52 + 4 * q) := by decide
    rw [hs.slots.addr _ _ (e q h), ht.slots.addr _ _ (e q h)]
  · have e : 52 + 4 * q = halfSlot := by simp only [halfSlot]; omega
    rw [e, hs.slots.half, ht.slots.half]

/-- The runs a leaf starts from: the context, and the call's public data, in both. -/
structure Rel (L : Lay) (B : Addr) (Z len N : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s t : State) : Prop where
  bs : Bx L s B Z len N
  bt : Bx L t B Z len N
  ps : Public args B Z sp s
  pt : Public args B Z sp t

theorem agreeS {s t : State} {args : Nat → BitVec 32} {sp : BitVec 32} (hL : L.ws = 14)
    (h : Rel L B Z len N args sp s t) : VG.X86.Taint.Agree τS (view s B Z) (view t B Z) := by
  have hn := h.bs.nowrap
  have hf := h.bs.fits
  simp only [VG.Impl.Rsa.X86.InvBatch.offset] at hf
  have wf : ∀ {u : State}, Bx L u B Z len N → Public args B Z sp u → VG.X86.Taint.Wf τS (view u B Z) := by
    intro u hu pu
    refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨List.Forall₂.cons (show 160 ≤ Z by omega) List.Forall₂.nil,
      List.pairwise_singleton _ _, fun r hr => by
        cases hr with
        | head => exact hn
        | tail _ h => cases h⟩, ?_, ?_,
      fun _ => ⟨pu.argsOk.1, fun r hr => by
        simp only [view, State.withRegions_wr, List.mem_singleton] at hr; subst r
        exact pu.argsOk.2 _ hu.ws.ws.workspace.wr⟩, ?_⟩
    · intro p hp
      simp only [τS, List.mem_singleton] at hp
      subst p
      show addr (u.gpr .edi) 0 = B
      simpa only [addr, BitVec.add_zero] using hu.ws.ws.workspace.edi
    · intro p hp; cases hp
    · intro p hp
      simp only [τS, List.mem_singleton] at hp
      subst p
      refine ⟨by decide, ?_⟩
      have v := hu.ws.wsArg.value
      rw [hL] at v
      show addr (u.mem.readW (addr (u.gpr .esp) 60) 32) 0 = B
      change u.mem.readW (addr (u.gpr .esp) (4 + 4 * 14)) 32 = _ at v
      rw [show (4 + 4 * 14 : Nat) = 60 from rfl] at v
      rw [v]
      simp only [addr, BitVec.add_zero]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have := B.isLt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨⟨?_, fun h => nomatch h⟩, fun _ => rfl, wf h.bs h.ps, wf h.bt h.pt,
    VG.X86.Taint.slotsOk_of_list rfl (by decide), ?_, fun _ => h.ps.stack.trans h.pt.stack.symm, ?_⟩
  · intro r hr
    simp only [τS, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h.bs.ws.ws.workspace.edi_toNat.trans h.bt.ws.ws.workspace.edi_toNat.symm)
    · exact h.ps.stack.trans h.pt.stack.symm
  · intro i k hk
    simp only [τS, VG.Slots.has_ofList, List.mem_singleton] at hk
    obtain ⟨_, rfl, rfl, h₁, h₂⟩ := hk
    simp only at h₁ h₂
    change s.mem (B + BitVec.ofNat 64 k) = t.mem (B + BitVec.ofNat 64 k)
    have W := slot_words h.bs h.bt ((k - 52) / 4) (by omega)
    have e : B + BitVec.ofNat 64 k = off B (52 + 4 * ((k - 52) / 4)) + BitVec.ofNat 64 ((k - 52) % 4) := by
      simp only [off]; rw [VG.Offset.add_add]; congr 2; omega
    rw [e, Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (BitVec.eq_of_toNat_eq W)
  · intro k h4 hk
    simp only [τS] at hk
    change s.mem (VG.X86.Taint.argByte s (VG.X86.Taint.depth τS.stk + k)) =
      t.mem (VG.X86.Taint.argByte t (VG.X86.Taint.depth τS.stk + k))
    rw [show VG.X86.Taint.depth τS.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq h.ps.argsOk.1 h4 hk, VG.X86.Taint.argByte_eq h.pt.argsOk.1 h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ ((h.ps.arguments _ (by omega)).value.trans (h.pt.arguments _ (by omega)).value.symm)

end VG.Proof.Rsa.X86.InvBatchRt.Time
