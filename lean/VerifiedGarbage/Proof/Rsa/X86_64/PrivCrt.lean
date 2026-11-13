module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-!
# `vg_rsa_private_checked` on x86-64: the call of the CRT

The CRT runs with the stack arguments the frame holds at `rsp`, writing
`M` at `oM` (`crt_pre`), and returns with `M` written and the frame's
slots kept (`crt_call`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

variable {X : List Region}

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The return address of a call from the frame. -/
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 (frameBytes + 8)

theorem fb_sub8 (s : State) : fb s - 8 = kb s := by
  simp only [fb, kb, BitVec.sub_sub]; rfl

theorem fb_kb (s : State) : fb s = kb s + BitVec.ofNat 64 8 := by
  rw [← fb_sub8]; exact (BitVec.sub_add_cancel _ _).symm

theorem fb_off (s : State) (d : Nat) : off (fb s) d = kb s + BitVec.ofNat 64 (8 + d) := by
  rw [fb_kb, off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem kb_toNat {s : State} (hp : PreF X s) : (kb s).toNat + (frameBytes + 8) + 8 + 112 ≤ 2 ^ 64 ∧
    (kb s).toNat + (frameBytes + 8) = (s.gpr .rsp).toNat ∧ 8 ≤ (kb s).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stackBytes frameBytes at *; omega_arith

theorem toNat_off {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (off p d).toNat = p.toNat + d := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat} (hi : i < 400) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hsep := Offset.sep (kb s) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega_arith) (by omega_arith) (by omega_arith)
  rw [show kb s + BitVec.ofNat 64 0 = kb s from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, fb_sub8]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  rw [fb_kb, ← off, off_off, show 8 + 8 * i = 8 * (i + 1) by omega_arith]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, fb_sub8]
  rw [fb_kb]

/-- What the CRT writes: `M` and the working space. -/
def crtWr (s : State) : List Region :=
  [⟨off (fb s) oM, (s.gpr .rcx).toNat⟩, ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩]

/-- The return address of the CRT's calls is in the stack the function
uses, below its own. -/
theorem hole_sub (s : State) : Region.Sub (hole (kb s)) (stkR s) := by
  rw [show hole (kb s) = ⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, 8⟩ by
    simp only [hole, kb, BitVec.sub_sub]; rfl]
  exact Region.sub_prefix (by decide)

/-- Frame bytes at `d` are apart from the return address of the CRT's calls. -/
theorem frame_hole {s : State} (hp : PreF X s) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Disjoint ⟨kb s + BitVec.ofNat 64 (8 + d), n⟩ (hole (kb s)) := by
  have ⟨hK1, _, _⟩ := kb_toNat hp
  exact Offset.disjoint_below (kb s) (n := 8) (by unfold frameBytes at h hK1; omega_arith)

/-! ## Memory across a call from the frame -/

/-- The return address a call from the frame stores. -/
theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = fb s) : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- A buffer of the caller that the function does not write, from memory
changed only where it may write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [stkR s, outR s, scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

/-- The return address's bytes are in the stack the function uses. -/
theorem below_sub (s : State) : Region.Sub (below (fb s) 8) (stkR s) := ret_sub s

/-- Memory changed by a call from the frame, within regions in the stack
the function uses, `out` or the working space. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame [stkR s, outR s, scrR s] m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, Region.Sub r (stkR s) ∨ Region.Sub r (outR s) ∨ Region.Sub r (scrR s)) :
    Frame [stkR s, outR s, scrR s] m₁ m₃ :=
  h₁.trans (h₂.sub fun r hr => by
    rcases hs r hr with h | h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h⟩)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- A slot kept by a call that writes regions apart from it. -/
theorem slot_keep {s : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, (⟨off (fb s) d, 8⟩ : Region).Disjoint r) : word m' (fb s) d = word m (fb s) d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-! ## The call -/

/-- The slots are apart from `M`, the working space and the return address. -/
theorem slot_apart {s : State} (hp : PreF X s) {d : Nat} (hd' : d + 8 ≤ oM) :
    ∀ r ∈ crtWr s ++ [below (fb s) 16], (⟨off (fb s) d, 8⟩ : Region).Disjoint r := by
  have e2 : oM = 168 := rfl
  have hk2 := hp.k2
  intro r hr
  simp only [crtWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  · exact (hp.dKs.sub_left (frame_sub s (by unfold frameBytes; omega_arith)))
  · exact Offset.disjoint_below (fb s) (n := 16) (by omega_arith)

end VG.Proof.Rsa.X86_64
