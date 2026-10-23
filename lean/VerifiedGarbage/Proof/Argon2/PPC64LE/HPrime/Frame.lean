module
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call

import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.Proof.Blake2.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-! # H′: the memory changed by hashing a workspace buffer -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.HPrime

open VG VG.PPC64LE

/-- Join the hash's individual writable buffers into its first 832 bytes. -/
theorem workspace_frame {m m' : Mem} (p sp : Addr) (rs : List (Nat × Nat)) (stack : Nat)
    (bounds : ∀ r ∈ rs, r.1 + r.2 ≤ 832) (depth : stack ≤ 48)
    (h : Frame (rs.map (fun r => ⟨p + BitVec.ofNat 64 r.1, r.2⟩) ++ [below sp stack]) m m') :
    Frame [⟨p, 832⟩, below sp 48] m m' := by
  apply h.sub
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact ⟨_, List.mem_cons_self .., Offset.sub_base p (bounds q hq)⟩
  · simp only [List.mem_singleton] at hr; subst r
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), below_sub depth (by decide)⟩

theorem init_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩] m m') : Frame [⟨p, 832⟩, below sp 48] m m' := by
  apply h.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨p, 832⟩, List.mem_cons_self .., Region.sub_prefix (by decide)⟩

theorem update_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, ⟨p + 192, 576⟩, below sp 48] m m') :
    Frame [⟨p, 832⟩, below sp 48] m m' := by
  apply workspace_frame p sp [(0, 192), (192, 576)] 48 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero,
    show BitVec.ofNat 64 192 = (192 : Addr) from rfl] using h

theorem finalize_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, ⟨p + 768, 64⟩, ⟨p + 192, 576⟩, below sp 48] m m') :
    Frame [⟨p, 832⟩, below sp 48] m m' := by
  apply workspace_frame p sp [(0, 192), (768, 64), (192, 576)] 48 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero,
    show BitVec.ofNat 64 192 = (192 : Addr) from rfl,
    show BitVec.ofNat 64 768 = (768 : Addr) from rfl] using h

/-- The caller's registers and permissions, and its saved registers above
832, survive every hash operation. -/
structure Keeps (s t : State) : Prop where
  regs : ∀ r ∈ preserved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .r31, 832⟩, below s.sp 48] s.mem t.mem

theorem Keeps.r31 {s t : State} (h : Keeps s t) : t.gpr .r31 = s.gpr .r31 :=
  h.regs _ (by decide)

theorem Keeps.trans {s t u : State} (h : Keeps s t) (h' : Keeps t u) : Keeps s u where
  regs r hr := (h'.regs r hr).trans (h.regs r hr)
  rd := h'.rd.trans h.rd
  wr := h'.wr.trans h.wr
  sp := h'.sp.trans h.sp
  frame := h.frame.trans (by simpa only [h.r31, h.sp] using h'.frame)

theorem Keeps.bytes {s t : State} (h : Keeps s t) (r : Region) (bound : r.len ≤ 2 ^ 64)
    (work : r.Disjoint ⟨s.gpr .r31, 832⟩) (stack : r.Disjoint (below s.sp 48)) :
    Spec.Blake2.bytesAt t.mem r.base r.len = Spec.Blake2.bytesAt s.mem r.base r.len := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := r) _ bound hi
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · exact work
  · exact stack

theorem Keeps.prefix {s t : State} (h : Keeps s t)
    (stackWork : (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩) :
    Spec.Blake2.bytesAt t.mem (s.gpr .r31 + 832) 4 =
      Spec.Blake2.bytesAt s.mem (s.gpr .r31 + 832) 4 :=
  h.bytes ⟨s.gpr .r31 + 832, 4⟩ (show 4 ≤ 2 ^ 64 by decide)
    (Offset.base_disjoint _ (e := 832) (n := 4) (k := 832) (by decide) (by decide)).symm
    (stackWork.sub_right (Offset.sub_base _ (by decide : 832 + 4 ≤ 16384))).symm

end VG.Proof.Argon2.PPC64LE.HPrime
