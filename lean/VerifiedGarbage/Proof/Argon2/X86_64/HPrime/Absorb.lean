module

public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Update
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Argon2.X86_64.HPrime
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.Proof.Blake2.Stream

/-! ### `Argon2.X86_64.HPrime.Frame`, which this module and modules that import it used -/

section

/-! # H′: the memory changed by hashing a workspace buffer -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64

/-- Join the hash's individual writable buffers into its first 832 bytes. -/
theorem workspace_frame {m m' : Mem} (p sp : Addr) (rs : List (Nat × Nat)) (stack : Nat)
    (bounds : ∀ r ∈ rs, r.1 + r.2 ≤ 832) (depth : stack ≤ 16)
    (h : Frame (rs.map (fun r => ⟨p + BitVec.ofNat 64 r.1, r.2⟩) ++ [below sp stack]) m m') :
    Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply h.sub
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
    exact ⟨_, List.mem_cons_self .., Offset.sub_base p (bounds q hq)⟩
  · simp only [List.mem_singleton] at hr; subst r
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), below_sub depth (by decide)⟩

theorem init_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, below sp 8] m m') : Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply workspace_frame p sp [(0, 192)] 8 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero] using h

theorem update_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, ⟨p + 192, 576⟩, below sp 16] m m') :
    Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply workspace_frame p sp [(0, 192), (192, 576)] 16 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero,
    show BitVec.ofNat 64 192 = (192 : Addr) from rfl] using h

theorem finalize_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, ⟨p + 768, 64⟩, ⟨p + 192, 576⟩, below sp 16] m m') :
    Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply workspace_frame p sp [(0, 192), (768, 64), (192, 576)] 16 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero,
    show BitVec.ofNat 64 192 = (192 : Addr) from rfl,
    show BitVec.ofNat 64 768 = (768 : Addr) from rfl] using h

/-- The caller's registers and permissions, and its saved registers above
832, survive every hash operation. -/
structure Keeps (s t : State) : Prop where
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16] s.mem t.mem

theorem Keeps.rbx {s t : State} (h : Keeps s t) : t.gpr .rbx = s.gpr .rbx :=
  h.regs _ (by decide)

theorem Keeps.rsp {s t : State} (h : Keeps s t) : t.gpr .rsp = s.gpr .rsp :=
  h.regs _ (by decide)

theorem Keeps.trans {s t u : State} (h : Keeps s t) (h' : Keeps t u) : Keeps s u where
  regs r hr := (h'.regs r hr).trans (h.regs r hr)
  rd := h'.rd.trans h.rd
  wr := h'.wr.trans h.wr
  frame := h.frame.trans (by simpa only [h.rbx, h.rsp] using h'.frame)

theorem Keeps.bytes {s t : State} (h : Keeps s t) (r : Region) (bound : r.len ≤ 2 ^ 64)
    (work : r.Disjoint ⟨s.gpr .rbx, 832⟩) (stack : r.Disjoint (below (s.gpr .rsp) 16)) :
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
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    Spec.Blake2.bytesAt t.mem (s.gpr .rbx + 832) 4 =
      Spec.Blake2.bytesAt s.mem (s.gpr .rbx + 832) 4 :=
  h.bytes ⟨s.gpr .rbx + 832, 4⟩ (show 4 ≤ 2 ^ 64 by decide)
    (Offset.base_disjoint _ (e := 832) (n := 4) (k := 832) (by decide) (by decide)).symm
    (stackWork.sub_right (Offset.sub_base _ (by decide : 832 + 4 ≤ 16384))).symm

end VG.Proof.Argon2.X86_64.HPrime

end

end

/-! ### `Argon2.X86_64.HPrime.Fixed`, which this module and modules that import it used -/

section

/-! # H′: arguments for a fixed workspace buffer -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure FixedArgs (s t : State) (offset size : Nat) : Prop where
  count : t.gpr .rsi = 0
  data : t.gpr .rdx = s.gpr .rbx + BitVec.ofNat 64 offset
  size : t.gpr .rcx = BitVec.ofNat 64 size
  other : ∀ r, r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem fixedArgs_ok (s : State) (offset size : Nat) (ho : offset < 2 ^ 31) (hn : size < 2 ^ 32) :
    WP isa (.block (fixedArgs offset size)) s fun t => FixedArgs s t offset size := by
  have hoff := Proof.MdStream.X86_64.sx_ofNat ho
  have hsize : (BitVec.ofNat 32 size).setWidth 64 = BitVec.ofNat 64 size := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (by omega_using [hn] : size < 2 ^ 64)]
  apply WP.of_runBlock
  simp only [fixedArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, execAlu, State.setReg32, RegUpd.gpr_setReg,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_true, ite_false, hoff]
  · simp only [RegUpd.gpr_setReg, ite_true, hsize]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, ite_false]

end VG.Proof.Argon2.X86_64.HPrime

end

end

/-! # H′: absorbing the length prefix or previous digest -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem absorbFixed_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (offset size : Nat)
    (offsetLower : 768 ≤ offset) (sizeBound : offset + size ≤ 16384)
    (repr : Repr b h0 s.mem (s.gpr .rbx) [])
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (absorbFixed (hash v) offset size) s fun t =>
      Repr b h0 t.mem (s.gpr .rbx) (bytesAt s.mem (s.gpr .rbx + BitVec.ofNat 64 offset) size) ∧
      Keeps s t := by
  unfold absorbFixed
  refine WP.seq ((fixedArgs_ok s offset size (by omega_using [sizeBound]) (by omega_using [sizeBound])).mono fun u hu => ?_)
  have p : u.gpr .rbx = s.gpr .rbx := hu.other _ (by decide) (by decide) (by decide)
  have sp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide) (by decide)
  have len : (u.gpr .rcx).toNat = size := by
    rw [hu.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [sizeBound])]
  have wr : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [p, hu.wr]; exact hwr
  have hr : Repr b h0 u.mem (u.gpr .rbx) [] := by rw [hu.mem, p]; exact repr
  have hc : u.gpr .rsi = BitVec.ofNat 64 ([] : List Byte).length := hu.count
  have hb : ([] : List Byte).length + (u.gpr .rcx).toNat < 2 ^ 64 := by simp only [List.length_nil, Nat.zero_add, len]; omega_using [sizeBound]
  have cover : Covers [⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩] (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .rbx, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), offset, hu.data, ?_⟩
    change offset + (u.gpr .rcx).toNat ≤ 16384
    rw [len]; exact sizeBound
  have ds : (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region).Disjoint ⟨u.gpr .rbx, 192⟩ := by
    rw [hu.data, len, p]
    exact (Offset.base_disjoint _ (by omega_using [offsetLower]) (by omega_using [sizeBound])).symm
  have dw : (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region).Disjoint ⟨u.gpr .rbx + 192, 576⟩ := by
    rw [hu.data, len, p]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega_using [offsetLower]) (by omega_using [sizeBound]) (by decide)
  have sw : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
    rw [sp, p]; exact stackWork
  have sd : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ := by
    rw [sp, hu.data, len]
    exact stackWork.sub_right (Offset.sub_base _ sizeBound)
  refine (update_ok v u h0 [] hr hc hb wr cover ds dw sw sd).mono ?_
  rintro t ⟨repr', regs, rd, wr', frame⟩
  simp only [p, hu.data, len, hu.mem, List.nil_append] at repr'
  refine ⟨repr', fun r hr => (regs r hr).trans ?_, rd.trans hu.rd, wr'.trans hu.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · simpa only [p, sp, hu.mem] using update_frame (u.gpr .rbx) (u.gpr .rsp) frame

end VG.Proof.Argon2.X86_64.HPrime
