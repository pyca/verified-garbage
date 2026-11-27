module

public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb
import VerifiedGarbage.Proof.Blake2.X86_64.Stream.CT
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy
import VerifiedGarbage.Proof.MdStream.X86_64.Common
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.HPrime
public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init
public import VerifiedGarbage.Impl.Argon2.X86_64.HPrime
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Update
public import VerifiedGarbage.Spec.Argon2
public import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Argon2.X86_64.HPrime.Setup`, which this module and modules that import it used -/

section

/-! # H′: saving the caller and writing the length prefix -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

/-- Save the six caller registers and then the four-byte length prefix. -/
def setupMem (s : State) : Mem :=
  (saved.foldl (fun m rd => m.writeW (s.gpr .r8 + BitVec.ofNat 64 rd.2) (s.gpr rd.1)) s.mem).writeW
    (s.gpr .r8 + 832) ((s.gpr .rcx).setWidth 32)

theorem setupMem_frame (s : State) :
    Frame [⟨s.gpr .r8 + 832, 56⟩] s.mem (setupMem s) := by
  have store {m : Mem} (h : Frame [⟨s.gpr .r8 + 832, 56⟩] s.mem m)
      (d w : Nat) (v : BitVec w) (lo : 832 ≤ d) (hi : d + w / 8 ≤ 888) :
      Frame [⟨s.gpr .r8 + 832, 56⟩] s.mem (m.writeW (s.gpr .r8 + BitVec.ofNat 64 d) v) :=
    h.writeW (List.mem_singleton_self _) v (Offset.contains _ lo hi (by decide))
  unfold setupMem saved
  simp only [List.foldl_cons, List.foldl_nil]
  apply store (d := 832) (w := 32) _ _ (by decide) (by decide)
  apply store (d := 880) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 872) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 864) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 856) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 848) (w := 64) _ _ (by decide) (by decide)
  exact store (Frame.refl _ _) 840 64 _ (by decide) (by decide)

theorem setupMem_prefix (s : State) :
    Spec.Blake2.bytesAt (setupMem s) (s.gpr .r8 + 832) 4 =
      Spec.Argon2.le32 (s.gpr .rcx).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl)]
  unfold setupMem
  rw [Mem.readW_writeW_self32]
  rfl

theorem setupMem_saved (s : State) (r : Reg) (d : Nat) (hr : (r, d) ∈ saved) :
    (setupMem s).readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  have skip64 (m : Mem) (v : BitVec 64) (d e : Nat)
      (sep : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
      (m.writeW (s.gpr .r8 + BitVec.ofNat 64 e) v).readW
        (s.gpr .r8 + BitVec.ofNat 64 d) 64 = m.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 :=
    Mem.readW_writeW_sep (Offset.sep _ sep hd he) (by decide)
  have skip32 (m : Mem) (v : BitVec 32) (d : Nat) (lo : 836 ≤ d) (hi : d + 8 ≤ 2 ^ 64) :
      (m.writeW (s.gpr .r8 + 832) v).readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 =
        m.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 :=
    Mem.readW_writeW_sep (Offset.sep _ (Or.inr lo) hi (by decide)) (by decide)
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp (disch := decide) only [setupMem, saved, List.foldl_cons, List.foldl_nil,
      skip32, skip64, Mem.readW_writeW_self64]

structure Setup (s t : State) : Prop where
  workspace : t.gpr .rbx = s.gpr .r8
  input : t.gpr .r12 = s.gpr .rdi
  length : t.gpr .r13 = s.gpr .rsi
  output : t.gpr .r14 = s.gpr .rdx
  remaining : t.gpr .r15 = s.gpr .rcx
  other : ∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  mem : t.mem = setupMem s
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem setup_ok (s : State) (hw : (⟨s.gpr .r8, 16384⟩ : Region) ∈ s.wr) :
    WP isa (.block setup) s (Setup s) := by
  have write (d n : Nat) (h : d + n ≤ 16384) :
      InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 d) n :=
    ⟨_, hw, Offset.contains_base _ h (by omega_using [h])⟩
  have w832 := write 832 4 (by decide)
  have w840 := write 840 8 (by decide)
  have w848 := write 848 8 (by decide)
  have w856 := write 856 8 (by decide)
  have w864 := write 864 8 (by decide)
  have w872 := write 872 8 (by decide)
  have w880 := write 880 8 (by decide)
  apply WP.of_runBlock
  simp only [setup, saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.store64, State.store32,
    ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    w832, w840, w848, w856, w864, w872, w880, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun r h1 h2 h3 h4 h5 => ?_, ?_, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg, h1, h2, h3, h4, h5, ite_false]
  · rfl

end VG.Proof.Argon2.X86_64.HPrime

end

end

/-! ### `Argon2.X86_64.HPrime.Length`, which this module and modules that import it used -/

section

/-! # H′: selecting the first digest length -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov wp_cmpi wp_mov32i)

theorem chooseLength_ok (s : State) :
    WP isa chooseLength s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 (min (s.gpr .r15).toNat 64) ∧ Keeps s t := by
  unfold chooseLength
  refine WP.seq (wp_mov fun a ha _ _ => wp_cmpi fun u gu mu ru wu cf _ => WP.block_nil ?_)
  have n : a.gpr .rsi = s.gpr .r15 := ha.gpr
  have ku : Keeps s u := by
    refine ⟨fun r hr => ?_, ru.trans ha.rd, wu.trans ha.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [gu]; exact ha.other r hn
    · rw [mu, ha.mem]; exact Frame.refl _ _
  have flag : isa.eval .b u = some (decide ((s.gpr .r15).toNat < 65)) := by
    simp only [eval, cf, n]
    rfl
  refine WP.ite (decide ((s.gpr .r15).toNat < 65)) flag ?_ ?_
  · intro h
    have hn : (s.gpr .r15).toNat ≤ 64 := by
      have h' := of_decide_eq_true h
      omega_using [h']
    apply WP.block_nil
    refine ⟨?_, ku⟩
    rw [gu, n, Nat.min_eq_left hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro h
    have hn : 64 ≤ (s.gpr .r15).toNat := by
      have h' := of_decide_eq_false h
      omega_using [h']
    refine wp_mov32i fun t ht _ _ => WP.block_nil ?_
    refine ⟨?_, ku.trans ⟨fun r hr => ?_, ht.rd, ht.wr, ?_⟩⟩
    · rw [Nat.min_eq_right hn]; exact ht.gpr
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact ht.other r hn
    · rw [ht.mem]; exact Frame.refl _ _

end VG.Proof.Argon2.X86_64.HPrime

end

end

/-! ### `Argon2.X86_64.HPrime.Input`, which this module and modules that import it used -/

section

/-! # H′: arguments for the caller's input -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure InputArgs (s t : State) : Prop where
  count : t.gpr .rsi = 4
  data : t.gpr .rdx = s.gpr .r12
  size : t.gpr .rcx = s.gpr .r13
  other : ∀ r, r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem inputArgs_ok (s : State) : WP isa (.block inputArgs) s (InputArgs s) := by
  apply WP.of_runBlock
  simp only [inputArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, RegUpd.gpr_setReg, reduceCtorEq, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, h1, h2, h3, ite_false]

theorem InputArgs.keeps {s t : State} (h : InputArgs s t) : Keeps s t := by
  refine ⟨fun r hr => ?_, h.rd, h.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r hn.1 hn.2.1 hn.2.2
  · rw [h.mem]; exact Frame.refl _ _

open VG.Spec.Blake2 (b Repr bytesAt)

theorem absorbInput_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (headBytes : List Byte) (prefixLen : headBytes.length = 4)
    (repr : Repr b h0 s.mem (s.gpr .rbx) headBytes) (len : (s.gpr .r13).toNat < 2 ^ 32)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .r12, (s.gpr .r13).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .r12, (s.gpr .r13).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r12, (s.gpr .r13).toNat⟩) :
    WP isa (absorbInput (hash v)) s fun t =>
      Repr b h0 t.mem (s.gpr .rbx) (headBytes ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat) ∧
      Keeps s t := by
  unfold absorbInput
  refine WP.seq ((inputArgs_ok s).mono fun u hu => ?_)
  have ku := hu.keeps
  have repr' : Repr b h0 u.mem (u.gpr .rbx) headBytes := by rw [hu.mem, ku.rbx]; exact repr
  have count : u.gpr .rsi = BitVec.ofNat 64 headBytes.length := by rw [prefixLen]; exact hu.count
  have bound : headBytes.length + (u.gpr .rcx).toNat < 2 ^ 64 := by rw [prefixLen, hu.size]; omega_using [len]
  have wr : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ku.rbx, ku.wr]; exact hwr
  have cover : Covers [⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩] (u.rd ++ u.wr) := by
    rw [hu.data, hu.size, hu.rd, hu.wr]; exact hdata
  have ds : (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region).Disjoint ⟨u.gpr .rbx, 192⟩ := by
    rw [hu.data, hu.size, ku.rbx]
    exact dataWork.sub_right (Region.sub_prefix (by decide))
  have dw : (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region).Disjoint ⟨u.gpr .rbx + 192, 576⟩ := by
    rw [hu.data, hu.size, ku.rbx]
    exact dataWork.sub_right (Offset.sub_base _ (by decide))
  have sw : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
    rw [ku.rbx, ku.rsp]; exact stackWork
  have sd : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ := by
    rw [hu.data, hu.size, ku.rsp]; exact stackData
  refine (update_ok v u h0 headBytes repr' count bound wr cover ds dw sw sd).mono ?_
  rintro t ⟨result, regs, rd, wr', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', update_frame _ _ frame⟩⟩
  simpa only [ku.rbx, hu.mem, hu.data, hu.size] using result

end VG.Proof.Argon2.X86_64.HPrime

end

end

/-! ### `Argon2.X86_64.HPrime.Space`, which this module and modules that import it used -/

section

/-! ### `Argon2.X86_64.HPrime.Output`, which this module and modules that import it used -/

section

/-! # H′: emitting a digest or its 32-byte prefix -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov wp_addi wp_mov32i wp_subi)
open VG.Spec.Blake2 (bytesAt)
open VG.WriteBytes

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hn, hi] : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesAt_take (m : Mem) (p : Addr) (n k : Nat) (hn : n ≤ k) :
    (bytesAt m p k).take n = bytesAt m p n := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]

structure Copied (s : State) (k : Nat) (t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + BitVec.ofNat 64 k
  other : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r14 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = writeBytes s.mem (s.gpr .r14) (bytesAt s.mem (s.gpr .rbx + 768) k)

theorem copy_ok (s : State) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 64)
    (count : s.gpr .rax = BitVec.ofNat 64 k)
    (work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < k, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .rbx + 768, k⟩ : Region).Disjoint ⟨s.gpr .r14, k⟩) :
    WP isa copy s (Copied s k) := by
  unfold copy
  refine WP.seq (wp_mov fun a ha _ _ => wp_addi fun u hu => WP.block_nil ?_)
  have src : u.gpr .rdx = s.gpr .rbx + 768 := by rw [hu.gpr, ha.gpr]; rfl
  have other : ∀ r, r ≠ .rdx → u.gpr r = s.gpr r := fun r hr =>
    (hu.other r hr).trans (ha.other r hr)
  have mem : u.mem = s.mem := hu.mem.trans ha.mem
  have rd : u.rd = s.rd := hu.rd.trans ha.rd
  have wr : u.wr = s.wr := hu.wr.trans ha.wr
  have read : ∀ i < k, InRegions (u.rd ++ u.wr)
      (s.gpr .rbx + 768 + BitVec.ofNat 64 i) 1 := by
    intro i hi'
    rw [rd, wr, BitVec.add_assoc,
      show (768 : Addr) = BitVec.ofNat 64 768 from rfl, ← BitVec.ofNat_add]
    exact ⟨_, List.mem_append_right _ work,
      Offset.contains_base _ (by omega_using [hi, hi'] : 768 + i + 1 ≤ 16384) (by omega_using [hi, hi'])⟩
  refine (copyLoop_ok u _ _ k lo (by omega_using [hi]) src (other .r14 (by decide))
    ((other .rax (by decide)).trans count) read ?_ sep).mono ?_
  · intro i hi'; rw [wr]; exact out i hi'
  · intro t ht
    refine ⟨ht.destination, fun r h1 h2 h3 h4 => (ht.other r h1 h2 h3 h4).trans (other r h3),
      ht.rd.trans rd, ht.wr.trans wr, ?_⟩
    rw [ht.mem, mem, List.take_of_length_le]
    simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl]

theorem Copied.frame {s t : State} {k : Nat} (h : Copied s k t) :
    Frame [⟨s.gpr .r14, k⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .r14) (d := 0) (n := k) (k := k) (by omega_using []) (by decide)

structure Emitted (s t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + 32
  remaining : t.gpr .r15 = s.gpr .r15 - 32
  other : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = writeBytes s.mem (s.gpr .r14) (bytesAt s.mem (s.gpr .rbx + 768) 32)

theorem emitPrefix_ok (s : State)
    (work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .rbx + 768, 32⟩ : Region).Disjoint ⟨s.gpr .r14, 32⟩) :
    WP isa emitPrefix s (Emitted s) := by
  unfold emitPrefix
  refine WP.seq (wp_mov32i fun a ha _ _ => WP.block_nil ?_)
  have base : a.gpr .rbx = s.gpr .rbx := ha.other _ (by decide)
  have dst : a.gpr .r14 = s.gpr .r14 := ha.other _ (by decide)
  have workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact work
  have outA : ∀ i < 32, InRegions a.wr (a.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact out
  have sepA : (⟨a.gpr .rbx + 768, 32⟩ : Region).Disjoint ⟨a.gpr .r14, 32⟩ := by
    rw [base, dst]; exact sep
  refine WP.seq ((copy_ok a 32 (by decide) (by decide) ha.gpr workA outA sepA).mono ?_)
  intro u hu
  refine wp_subi fun t ht _ => WP.block_nil ?_
  refine ⟨?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ht.rd.trans (hu.rd.trans ha.rd),
    ht.wr.trans (hu.wr.trans ha.wr), ?_⟩
  · rw [ht.other _ (by decide), hu.output, dst]; rfl
  · rw [ht.gpr, hu.other _ (by decide) (by decide) (by decide) (by decide), ha.other _ (by decide)]
    rfl
  · exact (ht.other r h5).trans ((hu.other r h1 h2 h3 h4).trans (ha.other r h1))
  · rw [ht.mem, hu.mem, ha.mem, base, dst]

theorem Emitted.frame {s t : State} (h : Emitted s t) :
    Frame [⟨s.gpr .r14, 32⟩] s.mem t.mem := by
  rw [h.mem]
  apply writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .r14) (d := 0) (n := 32) (k := 32) (by decide) (by decide)

theorem Emitted.digest {s t : State} (h : Emitted s t)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32⟩) :
    bytesAt t.mem (s.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .rbx + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))

end VG.Proof.Argon2.X86_64.HPrime

end

end

/-! ### `Argon2.X86_64.HPrime.Chain`, which only this module used -/

section

/-! Merged from `Proof.Argon2.X86_64.HPrime.Next`. -/

@[expose] public section

section
/-! # H′: hashing the previous 64-byte digest -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.X86_64 (wp_mov32i)

theorem next_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (next (hash v)) s fun t =>
      (bytesAt t.mem (s.gpr .rbx + 768) 64).take (s.gpr .rsi).toNat =
        Spec.Argon2.H (s.gpr .rsi).toNat (bytesAt s.mem (s.gpr .rbx + 768) 64) ∧ Keeps s t := by
  unfold next
  have retSub : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by decide) (by decide)
  have retState := (stackWork.sub_left retSub).sub_right
    (Region.sub_prefix (base := s.gpr .rbx) (len := 192) (len' := 16384) (by decide))
  refine WP.seq ((init_ok v s hlen hwr retState).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, frameA⟩
  have ka : Keeps s a := ⟨regsA, rdA, wrA, init_frame _ _ frameA⟩
  have digest : bytesAt a.mem (a.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
    rw [ka.rbx]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply frameA.bytes (R := ⟨s.gpr .rbx + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (Offset.base_disjoint _ (e := 768) (n := 64) (k := 192) (by decide) (by decide)).symm
    · exact ((stackWork.sub_left retSub).sub_right (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))).symm
  have reprA' : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) a.mem (a.gpr .rbx) [] := by
    rw [ka.rbx]; exact reprA
  have wrA' : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [ka.rbx, ka.wr]; exact hwr
  have swA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ka.rbx, ka.rsp]; exact stackWork
  refine WP.seq ((absorbFixed_ok v a _ 768 64 (by decide) (by decide) reprA' wrA' swA).mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) u.mem (u.gpr .rbx)
      (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [ku.rbx]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_mov32i fun w hw _ _ => WP.block_nil ?_)
  have kw : Keeps u w := by
    refine ⟨fun r hr => ?_, hw.rd, hw.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hw.other r hn
    · rw [hw.mem]; exact Frame.refl _ _
  have ksw := ksu.trans kw
  have reprW : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) w.mem (w.gpr .rbx)
      (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [hw.mem, kw.rbx]; exact reprU'
  have length : (bytesAt s.mem (s.gpr .rbx + 768) 64).length = 64 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have count : w.gpr .rsi = BitVec.ofNat 64 (bytesAt s.mem (s.gpr .rbx + 768) 64).length := by
    rw [length]; exact hw.gpr
  have bound : (bytesAt s.mem (s.gpr .rbx + 768) 64).length < 2 ^ 64 := by rw [length]; decide
  have wrW : (⟨w.gpr .rbx, 16384⟩ : Region) ∈ w.wr := by rw [ksw.rbx, ksw.wr]; exact hwr
  have swW : (below (w.gpr .rsp) 16).Disjoint ⟨w.gpr .rbx, 16384⟩ := by
    rw [ksw.rbx, ksw.rsp]; exact stackWork
  refine (finalize_ok v w _ _ reprW count bound wrW swW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, finalize_frame _ _ frameT⟩⟩
  have result := congrArg (List.take (s.gpr .rsi).toNat) out
  rw [ksw.rbx] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.ChainStep`. -/
section
/-! # H′: one hash-and-prefix iteration -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov32i wp_cmpi)
open VG.Spec.Blake2 (bytesAt)

structure ChainStep (s t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + 32
  remaining : t.gpr .r15 = s.gpr .r15 - 32
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, 32⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .rbx + 768) 64 =
    Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64)
  bytes : bytesAt t.mem (s.gpr .r14) 32 =
    (Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64)).take 32
  cf : t.cf = some (decide ((s.gpr .r15 - 32).toNat < 65))

theorem chainStep_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (.seq (.block [.mov32 .rsi (.imm 64)])
      (.seq (next (hash v)) (.seq emitPrefix (.block [.alu .cmp .r15 (.imm 65)]))))
      s (ChainStep s) := by
  refine WP.seq (wp_mov32i fun a ha _ _ => WP.block_nil ?_)
  have ka : Keeps s a := by
    refine ⟨fun r hr => ?_, ha.rd, ha.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact ha.other r hn
    · rw [ha.mem]; exact Frame.refl _ _
  have workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [ka.rbx, ka.wr]; exact work
  have stackA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ka.rbx, ka.rsp]; exact stackWork
  have lengthA : (a.gpr .rsi).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((next_ok v a (by rw [lengthA]; decide) workA stackA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .r14 = s.gpr .r14 := ksu.regs _ (by decide)
  have digestU : bytesAt u.mem (s.gpr .rbx + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    simpa only [lengthA, ka.rbx, ha.mem, bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ksu.rbx, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .rbx + 768, 32⟩ : Region).Disjoint ⟨u.gpr .r14, 32⟩ := by
    rw [ksu.rbx, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  refine wp_cmpi fun t gt mt rt wt cf _ => WP.block_nil ?_
  have fw : Frame [⟨s.gpr .r14, 32⟩] u.mem w.mem := by
    rw [← dstU]; exact hw.frame
  refine ⟨?_, ?_, fun r hr h14 h15 => ?_, rt.trans (hw.rd.trans ksu.rd),
    wt.trans (hw.wr.trans ksu.wr), ?_, ?_, ?_, ?_⟩
  · rw [gt, hw.output, dstU]
  · rw [gt, hw.remaining, ksu.regs _ (by decide)]
  · rw [gt]
    have hrax : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hw.other r hrax hrcx hrdx h14 h15).trans (ksu.regs r hr)
  · rw [mt]
    apply Frame.trans (ksu.frame.sub ?_) (fw.sub ?_)
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    · intro r hr
      exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [mt, ← digestU]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply fw.bytes (R := ⟨s.gpr .rbx + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  · rw [mt, hw.mem, dstU, ksu.rbx, ← digestU, bytesAt_take _ _ 32 64 (by decide)]
    exact bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
  · rw [cf, hw.remaining, ksu.regs _ (by decide)]
    rfl

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: repeating the hash-and-prefix iteration -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

structure ChainResult (s : State) (n : Nat) (t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + BitVec.ofNat 64 (32 * n)
  remaining : t.gpr .r15 = s.gpr .r15 - BitVec.ofNat 64 (32 * n)
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, 32 * n⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .rbx + 768) 64 =
    chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64)
  bytes : bytesAt t.mem (s.gpr .r14) (32 * n) =
    chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)

theorem ChainResult.refl (s : State) : ChainResult s 0 s :=
  ⟨by simp, by simp, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem ChainResult.cons {s u t : State} {n : Nat} (step : ChainStep s u)
    (tail : ChainResult u n t) (bound : 32 * (n + 1) < 2 ^ 64)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32 * (n + 1)⟩)
    (stackOut : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, 32 * (n + 1)⟩) :
    ChainResult s (n + 1) t := by
  have base := step.regs .rbx (by decide) (by decide) (by decide)
  have sp := step.regs .rsp (by decide) (by decide) (by decide)
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega_using []
  have sumBV : BitVec.ofNat 64 (32 * (n + 1)) = 32 + BitVec.ofNat 64 (32 * n) := by
    rw [sum, BitVec.ofNat_add]; rfl
  have tf : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
      ⟨s.gpr .r14 + 32, 32 * n⟩] u.mem t.mem := by
    rw [← base, ← sp, ← step.output]; exact tail.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ 32 * (n + 1))
      (h : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, 32 * (n + 1)⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ hk⟩
  refine ⟨?_, ?_, fun r hr h1 h2 => (tail.regs r hr h1 h2).trans (step.regs r hr h1 h2),
    tail.rd.trans step.rd, tail.wr.trans step.wr, ?_, ?_, ?_⟩
  · rw [tail.output, step.output, sumBV, BitVec.add_assoc]
  · rw [tail.remaining, step.remaining, sumBV, BitVec.sub_sub]
  · exact (extend 0 32 (by omega_using []) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega_using []) tf)
  · rw [← base, tail.digest, base, step.digest, Proof.Argon2.chainDigest]
  · have before : bytesAt t.mem (s.gpr .r14) 32 = bytesAt u.mem (s.gpr .r14) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .r14, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left
          (Region.sub_prefix (by omega_using []))
      · exact stackOut.symm.sub_left (Region.sub_prefix (by omega_using []))
      · exact Offset.base_disjoint _ (e := 32) (n := 32 * n) (k := 32) (by decide) (by omega_using [bound])
    rw [sum, Proof.Blake2.bytesAt_add, before, step.bytes,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl, ← step.output, tail.bytes,
      base, step.digest]
    rw [Proof.Argon2.chainPrefixes]

theorem chain_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (positive : 1 ≤ n) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (bound : 32 * n + lastLen < 2 ^ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen))
    (work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32 * n, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32 * n⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackOut : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, 32 * n⟩) :
    WP isa (chain (hash v)) s (ChainResult s n) := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega_using [hi])
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega_using []))
    obtain ⟨trace, u, run, step⟩ := chainStep_ok v s work out32 sep32 stackWork
    have base := step.regs .rbx (by decide) (by decide) (by decide)
    have sp := step.regs .rsp (by decide) (by decide) (by decide)
    have countU : u.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega_using [] : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_using []]
    have cfU : u.cf = some (decide (32 * n + lastLen < 65)) := by
      rw [step.cf, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [bound])]
    cases n with
    | zero =>
      have flag : isa.eval .ae u = some false := by
        simp only [eval, cfU, show 32 * 0 + lastLen < 65 by omega_using [last], decide_true,
          Option.map_some, Bool.not_true]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega_using []) sep stackOut⟩
    | succ n =>
      have workU : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .r14 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega_using [hi])
      have suffix : Region.Sub ⟨u.gpr .r14, 32 * (n + 1)⟩ ⟨s.gpr .r14, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega_using [] : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .rbx, 16384⟩ : Region).Disjoint ⟨u.gpr .r14, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      have swU : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
        rw [sp, base]; exact stackWork
      have soU : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .r14, 32 * (n + 1)⟩ := by
        rw [sp]; exact stackOut.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega_using []) (by omega_using [bound]) countU workU outU sepU swU soU
      have flag : isa.eval .ae u = some true := by
        simp only [eval, cfU, show ¬ 32 * (n + 1) + lastLen < 65 by omega_using [last], decide_false,
          Option.map_some, Bool.not_false]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega_using [bound]) sep stackOut⟩

end VG.Proof.Argon2.X86_64.HPrime

end

end


/-! Merged from `Proof.Argon2.X86_64.HPrime.Written`. -/

@[expose] public section

section
/-! # H′: composing output fragments -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64
open VG.Spec.Blake2 (bytesAt)

/-- An output fragment, allowing hashing in the workspace between writes. -/
structure Written (s : State) (xs : List Byte) (t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + BitVec.ofNat 64 xs.length
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, xs.length⟩] s.mem t.mem
  bytes : bytesAt t.mem (s.gpr .r14) xs.length = xs

theorem Written.rbx {s t : State} {xs : List Byte} (h : Written s xs t) :
    t.gpr .rbx = s.gpr .rbx := h.regs _ (by decide) (by decide) (by decide)

theorem Written.rsp {s t : State} {xs : List Byte} (h : Written s xs t) :
    t.gpr .rsp = s.gpr .rsp := h.regs _ (by decide) (by decide) (by decide)

theorem Written.of_keeps {s t : State} (h : Keeps s t) : Written s [] t := by
  refine ⟨?_, fun r hr _ _ => h.regs r hr, h.rd, h.wr, ?_, rfl⟩
  · exact (h.regs .r14 (by decide)).trans (BitVec.add_zero _).symm
  · exact h.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩

theorem Written.before_keeps {s u t : State} {xs : List Byte} (h : Written u xs t)
    (k : Keeps s u) : Written s xs t := by
  have dst := k.regs .r14 (by decide)
  refine ⟨by rw [h.output, dst], fun r hr h1 h2 => (h.regs r hr h1 h2).trans (k.regs r hr),
    h.rd.trans k.rd, h.wr.trans k.wr, ?_, ?_⟩
  · have before : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14, xs.length⟩] s.mem u.mem :=
      k.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    exact before.trans (by simpa only [dst, k.rbx, k.rsp] using h.frame)
  · rw [← dst]; exact h.bytes

theorem Written.of_copied {s t : State} {k : Nat} (h : Copied s k t) (hk : k < 2 ^ 64) :
    Written s (bytesAt s.mem (s.gpr .rbx + 768) k) t := by
  have len : (bytesAt s.mem (s.gpr .rbx + 768) k).length = k := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr h14 _ => ?_, h.rd, h.wr, ?_, ?_⟩
  · have h1 : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h3 : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h1 h2 h3 h14
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [h.mem]
    exact bytesAt_writeBytes _ _ _ (by rw [len]; exact hk)

theorem Written.of_emitted {s t : State} (h : Emitted s t) :
    Written s (bytesAt s.mem (s.gpr .rbx + 768) 32) t := by
  have len : (bytesAt s.mem (s.gpr .rbx + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  refine ⟨by rw [len]; exact h.output, fun r hr h14 h15 => ?_, h.rd, h.wr, ?_, ?_⟩
  · have h1 : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h2 : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h3 : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r h1 h2 h3 h14 h15
  · rw [len]
    exact h.frame.sub fun r hr =>
      ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [h.mem]
    exact bytesAt_writeBytes _ _ _ (by rw [len]; decide)

theorem Written.of_chain {s t : State} {n : Nat} (h : ChainResult s n t) :
    Written s (Proof.Argon2.chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)) t := by
  refine ⟨?_, h.regs, h.rd, h.wr, ?_, ?_⟩
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.output
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.frame
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.bytes

theorem Written.trans {s u t : State} {xs ys : List Byte} (first : Written s xs u)
    (last : Written u ys t) (bound : xs.length + ys.length < 2 ^ 64)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, xs.length + ys.length⟩)
    (stack : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, xs.length + ys.length⟩) :
    Written s (xs ++ ys) t := by
  have tf : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
      ⟨s.gpr .r14 + BitVec.ofNat 64 xs.length, ys.length⟩] u.mem t.mem := by
    rw [← first.rbx, ← first.rsp, ← first.output]; exact last.frame
  have extend {m m' : Mem} (d k : Nat) (hk : d + k ≤ xs.length + ys.length)
      (h : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14 + BitVec.ofNat 64 d, k⟩] m m') :
      Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14, (xs ++ ys).length⟩] m m' := by
    apply h.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ hx => hx⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
        Offset.sub_base _ (by simpa only [List.length_append] using hk)⟩
  refine ⟨?_, fun r hr h1 h2 => (last.regs r hr h1 h2).trans (first.regs r hr h1 h2),
    last.rd.trans first.rd, last.wr.trans first.wr, ?_, ?_⟩
  · rw [last.output, first.output, List.length_append, BitVec.ofNat_add, BitVec.add_assoc]
  · exact (extend 0 xs.length (by omega_using []) (by simpa only [BitVec.add_zero] using first.frame)).trans
      (extend xs.length ys.length (by omega_using []) tf)
  · have before : bytesAt t.mem (s.gpr .r14) xs.length = bytesAt u.mem (s.gpr .r14) xs.length := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .r14, xs.length⟩) _ (show xs.length ≤ 2 ^ 64 by omega_using [bound]) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by omega_using []))
      · exact stack.symm.sub_left (Region.sub_prefix (by omega_using []))
      · exact Offset.base_disjoint _ (by omega_using []) (by omega_using [bound])
    rw [List.length_append, Proof.Blake2.bytesAt_add, before, first.bytes, ← first.output, last.bytes]

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: permissions and separation at an output cursor -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov)
open VG.Spec.Blake2 (bytesAt)

structure Space (s : State) (n : Nat) : Prop where
  bound : n < 2 ^ 64
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  out : ∀ i < n, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1
  sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, n⟩
  stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackOut : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, n⟩

theorem Space.advance {s t : State} {xs : List Byte} {n k : Nat}
    (h : Space s n) (written : Written s xs t) (size : xs.length + k ≤ n) : Space t k := by
  have suffix : Region.Sub ⟨t.gpr .r14, k⟩ ⟨s.gpr .r14, n⟩ := by
    rw [written.output]; exact Offset.sub_base _ size
  refine ⟨by have := h.bound; omega_using [size, this], ?_, ?_, ?_, ?_, ?_⟩
  · rw [written.wr, written.rbx]; exact h.work
  · intro i hi
    rw [written.wr, written.output, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.out (xs.length + i) (by omega_using [size, hi])
  · rw [written.rbx]; exact h.sep.sub_right suffix
  · rw [written.rbx, written.rsp]; exact h.stackWork
  · rw [written.rsp]; exact h.stackOut.sub_right suffix

theorem Space.keeps {s t : State} {n : Nat} (h : Space s n) (k : Keeps s t) : Space t n :=
  h.advance (Written.of_keeps k) (by simp only [List.length_nil, Nat.zero_add, Nat.le_refl])

theorem Space.prefix {s : State} {n k : Nat} (h : Space s n) (hk : k ≤ n) : Space s k := by
  refine ⟨by have := h.bound; omega_using [hk, this], h.work, fun i hi => h.out i (by omega_using [hk, hi]),
    h.sep.sub_right (Region.sub_prefix hk), h.stackWork, h.stackOut.sub_right (Region.sub_prefix hk)⟩

theorem Space.join {s u t : State} {xs ys : List Byte} {n : Nat} (h : Space s n)
    (first : Written s xs u) (last : Written u ys t) (size : xs.length + ys.length ≤ n) :
    Written s (xs ++ ys) t :=
  first.trans last (by have := h.bound; omega_using [size, this])
    (h.sep.sub_right (Region.sub_prefix size)) (h.stackOut.sub_right (Region.sub_prefix size))

theorem copyRemaining_ok (s : State) (n : Nat) (space : Space s n)
    (lo : 1 ≤ n) (hi : n ≤ 64) (count : s.gpr .r15 = BitVec.ofNat 64 n) :
    WP isa copyRemaining s fun t => Written s (bytesAt s.mem (s.gpr .rbx + 768) n) t := by
  unfold copyRemaining
  refine WP.seq (wp_mov fun a ha _ _ => WP.block_nil ?_)
  have base := ha.other .rbx (by decide)
  have dst := ha.other .r14 (by decide)
  have workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact space.work
  have outA : ∀ i < n, InRegions a.wr (a.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact space.out
  have sepA : (⟨a.gpr .rbx + 768, n⟩ : Region).Disjoint ⟨a.gpr .r14, n⟩ := by
    rw [base, dst]; exact space.sep.sub_left (Offset.sub_base _ (by omega_using [hi] : 768 + n ≤ 16384))
  refine (copy_ok a n lo hi (ha.gpr.trans count) workA outA sepA).mono ?_
  intro t ht
  have result := Written.of_copied ht space.bound
  refine ⟨?_, fun r hr h1 h2 => ?_, result.rd.trans ha.rd, result.wr.trans ha.wr, ?_, ?_⟩
  · simpa only [dst, ha.mem, base] using result.output
  · have hrax : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (result.regs r hr h1 h2).trans (ha.other r hrax)
  · simpa only [base, dst, ha.mem, ha.other .rsp (by decide)] using result.frame
  · simpa only [base, dst, ha.mem] using result.bytes

end VG.Proof.Argon2.X86_64.HPrime

end

end

/-! ### `Argon2.X86_64.HPrime.Contract`, which this module and modules that import it used -/

section

/-! # H′: a local x86-64 contract -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64

def inputR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def outputR (s : State) : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
def workR (s : State) : Region := ⟨s.gpr .r8, 16384⟩
def retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩
def stackR (s : State) : Region := below (s.gpr .rsp) 16

def localContract : Contract isa where
  pre s := s.rd = [inputR s] ∧ s.wr = [outputR s, workR s] ∧
    (s.gpr .rsi).toNat < 2 ^ 32 ∧ 1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat < 2 ^ 32 ∧
    (inputR s).Disjoint (workR s) ∧ (outputR s).Disjoint (workR s) ∧
    (stackR s).Disjoint (inputR s) ∧ (stackR s).Disjoint (outputR s) ∧ (stackR s).Disjoint (workR s) ∧
    (retR s).Disjoint (outputR s) ∧ (retR s).Disjoint (workR s)
  post s t := Spec.Blake2.bytesAt t.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    Spec.Argon2.hPrime (s.gpr .rcx).toNat (Spec.Blake2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s t := s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .rsp = t.gpr .rsp

end VG.Proof.Argon2.X86_64.HPrime

end

end

/-! Merged from `Proof.Argon2.X86_64.HPrime.Restore`. -/

@[expose] public section

section
/-! # H′: restoring the caller's registers -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem restore_ok (original s : State) (base : s.gpr .rbx = original.gpr .r8)
    (sp : s.gpr .rsp = original.gpr .rsp)
    (readable : (⟨original.gpr .r8, 16384⟩ : Region) ∈ s.rd ++ s.wr)
    (values : ∀ r d, (r, d) ∈ saved →
      s.mem.readW (original.gpr .r8 + BitVec.ofNat 64 d) 64 = original.gpr r) :
    WP isa (.block restore) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = original.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have read (d : Nat) (h : d + 8 ≤ 16384) :
      InRegions (s.rd ++ s.wr) (original.gpr .r8 + BitVec.ofNat 64 d) 8 :=
    ⟨_, readable, Offset.contains_base _ h (by omega_arith)⟩
  obtain r840 := read 840 (by decide)
  obtain r848 := read 848 (by decide)
  obtain r856 := read 856 (by decide)
  obtain r864 := read 864 (by decide)
  obtain r872 := read 872 (by decide)
  obtain r880 := read 880 (by decide)
  obtain v840 := values .rbp 840 (by decide)
  obtain v848 := values .r12 848 (by decide)
  obtain v856 := values .r13 856 (by decide)
  obtain v864 := values .r14 864 (by decide)
  obtain v872 := values .r15 872 (by decide)
  obtain v880 := values .rbx 880 (by decide)
  apply WP.of_runBlock
  simp only [restore, saved, List.map_cons, List.map_nil, runBlock_cons,
    runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    base, r840, r848, r856, r864, r872, r880, v840, v848, v856, v864, v872, v880,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [reduceCtorEq, ite_true, ite_false, sp]

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.First`. -/
section
/-! Merged from `Proof.Argon2.X86_64.HPrime.FinishInput`. -/
section
/-! # H′: finalizing the prefixed input -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.X86_64 (wp_mov wp_addi)

theorem finishInput_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .rbx) d)
    (length : d.length = 4 + (s.gpr .r13).toNat) (bound : (s.gpr .r13).toNat < 2 ^ 32)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (finishInput (hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbx + 768) 64 = Spec.Blake2.finalHash b h0 d ∧ Keeps s t := by
  unfold finishInput
  refine WP.seq (wp_mov fun a ha _ _ => wp_addi fun u hu => WP.block_nil ?_)
  obtain ku : Keeps s u := by
    refine ⟨fun r hr => ?_, hu.rd.trans ha.rd, hu.wr.trans ha.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hu.other r hn).trans (ha.other r hn)
    · rw [hu.mem, ha.mem]; exact Frame.refl _ _
  obtain repr' : Repr b h0 u.mem (u.gpr .rbx) d := by rw [hu.mem, ha.mem, ku.rbx]; exact repr
  obtain count : u.gpr .rsi = BitVec.ofNat 64 d.length := by
    rw [hu.gpr, ha.gpr, length, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_comm _ _
  obtain len : d.length < 2 ^ 64 := by rw [length]; omega_arith
  obtain wr : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ku.rbx, ku.wr]; exact hwr
  obtain sw : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
    rw [ku.rbx, ku.rsp]; exact stackWork
  refine (finalize_ok v u h0 d repr' count len wr sw).mono ?_
  rintro t ⟨out, regs, rd, wr', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', finalize_frame _ _ frame⟩⟩
  simpa only [ku.rbx] using out

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: the hash of the length prefix and input -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)

theorem first_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .r15).toNat ∧ (s.gpr .r15).toNat < 2 ^ 32)
    (len : (s.gpr .r13).toNat < 2 ^ 32)
    (headBytes : bytesAt s.mem (s.gpr .rbx + 832) 4 = Spec.Argon2.le32 (s.gpr .r15).toNat)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .r12, (s.gpr .r13).toNat⟩] (s.rd ++ s.wr))
    (dataWork : (⟨s.gpr .r12, (s.gpr .r13).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r12, (s.gpr .r13).toNat⟩) :
    WP isa (first (hash v)) s fun t =>
      (bytesAt t.mem (s.gpr .rbx + 768) 64).take (min (s.gpr .r15).toNat 64) =
        Spec.Argon2.H (min (s.gpr .r15).toNat 64)
          (Spec.Argon2.le32 (s.gpr .r15).toNat ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat) ∧
      Keeps s t := by
  unfold first
  refine WP.seq ((chooseLength_ok s).mono ?_)
  rintro a ⟨lengthA, ka⟩
  obtain na : (a.gpr .rsi).toNat = min (s.gpr .r15).toNat 64 := by
    rw [lengthA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  obtain wrA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [ka.rbx, ka.wr]; exact hwr
  obtain swA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ka.rbx, ka.rsp]; exact stackWork
  obtain retA : (below (a.gpr .rsp) 8).Disjoint ⟨a.gpr .rbx, 192⟩ :=
    (swA.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))
  obtain lenA : 1 ≤ (a.gpr .rsi).toNat ∧ (a.gpr .rsi).toNat ≤ 64 := by rw [na]; omega_arith
  refine WP.seq ((init_ok v a lenA wrA retA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, frameU⟩
  obtain ku : Keeps a u := ⟨regsU, rdU, wrU, init_frame _ _ frameU⟩
  obtain ksu := ka.trans ku
  obtain reprU' : Repr b (Spec.Blake2.init b (min (s.gpr .r15).toNat 64) 0) u.mem (u.gpr .rbx) [] := by
    rw [ku.rbx]; simpa only [na] using reprU
  obtain wrU' : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ksu.rbx, ksu.wr]; exact hwr
  obtain swU : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
    rw [ksu.rbx, ksu.rsp]; exact stackWork
  obtain headU : bytesAt u.mem (u.gpr .rbx + 832) 4 = Spec.Argon2.le32 (s.gpr .r15).toNat := by
    rw [ksu.rbx, ksu.prefix stackWork]; exact headBytes
  refine WP.seq ((absorbFixed_ok v u _ 832 4 (by decide) (by decide) reprU' wrU' swU).mono ?_)
  rintro w ⟨reprW, kw⟩
  obtain ksw := ksu.trans kw
  obtain r12 : w.gpr .r12 = s.gpr .r12 := ksw.regs _ (by decide)
  obtain r13 : w.gpr .r13 = s.gpr .r13 := ksw.regs _ (by decide)
  obtain headLen : (Spec.Argon2.le32 (s.gpr .r15).toNat).length = 4 := by
    simp only [Spec.Argon2.le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]
  obtain reprW' : Repr b (Spec.Blake2.init b (min (s.gpr .r15).toNat 64) 0) w.mem (w.gpr .rbx)
      (Spec.Argon2.le32 (s.gpr .r15).toNat) := by
    rw [kw.rbx]
    simpa only [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, headU] using reprW
  obtain wrW : (⟨w.gpr .rbx, 16384⟩ : Region) ∈ w.wr := by rw [ksw.rbx, ksw.wr]; exact hwr
  obtain dataW : Covers [⟨w.gpr .r12, (w.gpr .r13).toNat⟩] (w.rd ++ w.wr) := by
    rw [r12, r13, ksw.rd, ksw.wr]; exact hdata
  obtain dwW : (⟨w.gpr .r12, (w.gpr .r13).toNat⟩ : Region).Disjoint ⟨w.gpr .rbx, 16384⟩ := by
    rw [r12, r13, ksw.rbx]; exact dataWork
  obtain swW : (below (w.gpr .rsp) 16).Disjoint ⟨w.gpr .rbx, 16384⟩ := by
    rw [ksw.rsp, ksw.rbx]; exact stackWork
  obtain sdW : (below (w.gpr .rsp) 16).Disjoint ⟨w.gpr .r12, (w.gpr .r13).toNat⟩ := by
    rw [ksw.rsp, r12, r13]; exact stackData
  obtain inputW : bytesAt w.mem (w.gpr .r12) (w.gpr .r13).toNat =
      bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat := by
    rw [r12, r13]
    exact ksw.bytes _ (show (s.gpr .r13).toNat ≤ 2 ^ 64 by omega_arith)
      (dataWork.sub_right (Region.sub_prefix (by decide))) stackData.symm
  refine WP.seq ((absorbInput_ok v w _ _ headLen reprW' (by rw [r13]; exact len)
    wrW dataW dwW swW sdW).mono ?_)
  rintro x ⟨reprX, kx⟩
  obtain ksx := ksw.trans kx
  obtain reprX' : Repr b (Spec.Blake2.init b (min (s.gpr .r15).toNat 64) 0) x.mem (x.gpr .rbx)
      (Spec.Argon2.le32 (s.gpr .r15).toNat ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat) := by
    rw [kx.rbx]; simpa only [inputW] using reprX
  obtain r13X : x.gpr .r13 = s.gpr .r13 := ksx.regs _ (by decide)
  obtain length : (Spec.Argon2.le32 (s.gpr .r15).toNat ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat).length =
      4 + (x.gpr .r13).toNat := by
    rw [List.length_append, headLen, r13X]
    simp only [bytesAt, List.length_map, List.length_range]
  obtain wrX : (⟨x.gpr .rbx, 16384⟩ : Region) ∈ x.wr := by rw [ksx.rbx, ksx.wr]; exact hwr
  obtain swX : (below (x.gpr .rsp) 16).Disjoint ⟨x.gpr .rbx, 16384⟩ := by
    rw [ksx.rsp, ksx.rbx]; exact stackWork
  refine (finishInput_ok v x _ _ reprX' length (by rw [r13X]; exact len) wrX swX).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, ksx.trans kt⟩
  obtain result := congrArg (List.take (min (s.gpr .r15).toNat 64)) out
  rw [ksx.rbx] at result
  exact result.trans (Proof.Argon2.H_stream _ _).symm

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.Finish`. -/
section
/-! Merged from `Proof.Argon2.X86_64.HPrime.Extend`. -/
section
/-! # H′: the prefixes and final digest of a long output -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov wp_cmpi)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

theorem maybeChain_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * n + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen))
    (cf : s.cf = some (decide (32 * n + lastLen < 65))) :
    WP isa (.ite .b (.block []) (chain (hash v))) s (ChainResult s n) := by
  refine WP.ite (decide (32 * n + lastLen < 65)) (by simp only [eval, cf]) ?_ ?_
  · intro h
    obtain hn : n = 0 := by have := of_decide_eq_true h; omega_arith
    subst n
    exact WP.block_nil (ChainResult.refl s)
  · intro h
    obtain hn : 1 ≤ n := by have := of_decide_eq_false h; omega_arith
    obtain p := space.prefix (show 32 * n ≤ 32 * n + lastLen by omega_arith)
    exact chain_ok v n lastLen s hn last space.bound count p.work p.out p.sep p.stackWork p.stackOut

theorem extendDigest_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (extendDigest (hash v)) s fun t =>
      Written s ((bytesAt s.mem (s.gpr .rbx + 768) 64).take 32 ++
        chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)) t ∧
      (bytesAt t.mem (s.gpr .rbx + 768) 64).take lastLen =
        Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64)) ∧
      t.gpr .r15 = BitVec.ofNat 64 lastLen := by
  unfold extendDigest
  obtain short := space.prefix (show 32 ≤ 32 * (n + 1) + lastLen by omega_arith)
  obtain sep32 := short.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok s short.work short.out sep32).mono ?_)
  intro a ha
  obtain wa := Written.of_emitted ha
  obtain lenA : (bytesAt s.mem (s.gpr .rbx + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  obtain spaceA : Space a (32 * n + lastLen) := space.advance wa (by rw [lenA]; omega_arith)
  obtain countA : a.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen) := by
    rw [ha.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
      Offset.ofNat_sub_ofNat (by omega_arith : 32 ≤ 32 * (n + 1) + lastLen)]
    rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega_arith]
  obtain digestA : bytesAt a.mem (a.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
    rw [wa.rbx]; exact ha.digest short.sep
  refine WP.seq (wp_cmpi fun u gu mu ru wu cf _ => WP.block_nil ?_)
  obtain ku : Keeps a u := ⟨fun r _ => congrFun gu r, ru, wu, by rw [mu]; exact Frame.refl _ _⟩
  obtain countU : u.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen) := (congrFun gu _).trans countA
  obtain cfU : u.cf = some (decide (32 * n + lastLen < 65)) := by
    rw [cf, countA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt spaceA.bound]; rfl
  refine WP.seq ((maybeChain_ok v n lastLen u (spaceA.keeps ku) last countU cfU).mono ?_)
  intro w hw
  obtain ww := (Written.of_chain hw).before_keeps ku
  obtain digestU : bytesAt u.mem (u.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
    rw [mu, gu]; exact digestA
  obtain ww' : Written a (chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)) w := by
    simpa only [digestU] using ww
  obtain wsw := space.join wa ww' (by rw [lenA, Proof.Argon2.chainPrefixes_length]; omega_arith)
  obtain produced : ((bytesAt s.mem (s.gpr .rbx + 768) 32) ++
      chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)).length = 32 * (n + 1) := by
    rw [List.length_append, lenA, Proof.Argon2.chainPrefixes_length]; omega_arith
  obtain spaceW : Space w lastLen := space.advance wsw (by rw [produced])
  obtain countW : w.gpr .r15 = BitVec.ofNat 64 lastLen := by
    rw [hw.remaining, countU, Offset.ofNat_sub_ofNat (by omega_arith : 32 * n ≤ 32 * n + lastLen)]
    rw [Nat.add_sub_cancel_left]
  obtain digestW : bytesAt w.mem (w.gpr .rbx + 768) 64 =
      chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [hw.regs .rbx (by decide) (by decide) (by decide), hw.digest, digestU]
  refine WP.seq (wp_mov fun x hx _ _ => WP.block_nil ?_)
  obtain kx : Keeps w x := by
    refine ⟨fun r hr => ?_, hx.rd, hx.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hx.other r hn
    · rw [hx.mem]; exact Frame.refl _ _
  obtain spaceX := spaceW.keeps kx
  obtain lenX : (x.gpr .rsi).toNat = lastLen := by
    rw [hx.gpr, countW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt spaceW.bound]
  refine (next_ok v x (by rw [lenX]; omega_arith) spaceX.work spaceX.stackWork).mono ?_
  rintro t ⟨dt, kt⟩
  obtain wwt := Written.of_keeps (kx.trans kt)
  obtain written := space.join wsw wwt (by rw [produced, List.length_nil]; omega_arith)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_nil, bytesAt_take _ _ 32 64 (by decide)] using written
  · rw [lenX, kx.rbx, hx.mem, digestW, wsw.rbx] at dt
    exact dt
  · rw [kt.regs _ (by decide), kx.regs _ (by decide)]; exact countW

theorem longOutput_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (space : Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (.seq (extendDigest (hash v)) copyRemaining) s fun t =>
      Written s (Spec.Argon2.longHash lastLen (n + 1) (bytesAt s.mem (s.gpr .rbx + 768) 64)) t := by
  refine WP.seq ((extendDigest_ok v n lastLen s space last count).mono ?_)
  rintro u ⟨written, digest, remaining⟩
  obtain len : ((bytesAt s.mem (s.gpr .rbx + 768) 64).take 32 ++
      chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)).length = 32 * (n + 1) := by
    simp only [List.length_append, List.length_take, bytesAt, List.length_map,
      List.length_range, Proof.Argon2.chainPrefixes_length]
    omega_arith
  obtain spaceU : Space u lastLen := space.advance written (by rw [len])
  refine (copyRemaining_ok u lastLen spaceU (by omega_arith) last.2 remaining).mono ?_
  intro t copied
  obtain out : bytesAt u.mem (u.gpr .rbx + 768) lastLen =
      Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64)) := by
    rw [written.rbx, ← bytesAt_take _ _ lastLen 64 last.2]; exact digest
  obtain all := space.join written copied (by
    rw [len]; simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl])
  rw [out, ← Proof.Argon2.longHash_chain] at all
  exact all

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: emitting the complete short or long output -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_cmpi)
open VG.Spec.Blake2 (bytesAt)

theorem finishOutput_ok (v : Proof.Blake2.X86_64.Backend) (s : State) (n : Nat) (input : List Byte)
    (space : Space s n) (positive : 1 ≤ n) (count : s.gpr .r15 = BitVec.ofNat 64 n)
    (digest : (bytesAt s.mem (s.gpr .rbx + 768) 64).take (min n 64) =
      Spec.Argon2.H (min n 64) (Spec.Argon2.le32 n ++ input)) :
    WP isa (finishOutput (hash v)) s (Written s (Spec.Argon2.hPrime n input)) := by
  unfold finishOutput
  refine WP.seq (wp_cmpi fun u gu mu ru wu cf _ => WP.block_nil ?_)
  obtain ku : Keeps s u := ⟨fun r _ => congrFun gu r, ru, wu, by rw [mu]; exact Frame.refl _ _⟩
  obtain countU : u.gpr .r15 = BitVec.ofNat 64 n := (congrFun gu _).trans count
  obtain cfU : u.cf = some (decide (n < 65)) := by
    rw [cf, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt space.bound]; rfl
  apply WP.seq
  refine WP.ite (decide (n < 65)) (by simp only [eval, cfU]) ?_ ?_
  · intro h
    obtain short : n ≤ 64 := by have := of_decide_eq_true h; omega_arith
    apply WP.block_nil
    refine (copyRemaining_ok u n (space.keeps ku) positive short countU).mono ?_
    intro t ht
    obtain result := ht.before_keeps ku
    obtain value : bytesAt u.mem (u.gpr .rbx + 768) n = Spec.Argon2.hPrime n input := by
      rw [mu, gu, ← bytesAt_take _ _ n 64 short]
      simpa only [Nat.min_eq_left short, Spec.Argon2.hPrime, ite_eq_left short] using digest
    rw [value] at result
    exact result
  · intro h
    obtain long : 64 < n := by have := of_decide_eq_false h; omega_arith
    let r := (n + 31) / 32 - 2
    let lastLen := n - 32 * r
    obtain bounds : 1 ≤ r ∧ 33 ≤ lastLen ∧ lastLen ≤ 64 ∧ 32 * r + lastLen = n :=
      Proof.Argon2.longHash_bounds n long
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega_arith)
    change r = q + 1 at hq
    obtain size : 32 * (q + 1) + lastLen = n := by rw [← hq]; exact bounds.2.2.2
    obtain spaceU : Space u (32 * (q + 1) + lastLen) := by rw [size]; exact space.keeps ku
    obtain countLong : u.gpr .r15 = BitVec.ofNat 64 (32 * (q + 1) + lastLen) := by rw [size]; exact countU
    apply WP.seq_iff.mp
    refine (longOutput_ok v q lastLen u spaceU ⟨bounds.2.1, bounds.2.2.1⟩ countLong).mono ?_
    intro t ht
    obtain result := ht.before_keeps ku
    obtain digestU : bytesAt u.mem (u.gpr .rbx + 768) 64 =
        Spec.Argon2.H 64 (Spec.Argon2.le32 n ++ input) := by
      rw [mu, gu]
      simpa only [Nat.min_eq_right (show 64 ≤ n by omega_arith), bytesAt_take _ _ 64 64 (by decide)] using digest
    obtain value : Spec.Argon2.longHash lastLen (q + 1) (bytesAt u.mem (u.gpr .rbx + 768) 64) =
        Spec.Argon2.hPrime n input := by
      rw [digestU, ← hq, Spec.Argon2.hPrime, ite_eq_right (show ¬ n ≤ 64 by omega_arith)]
    rw [value] at result
    exact result

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: functional correctness of the complete x86-64 program -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (bytesAt)

theorem code_wp (v : Proof.Blake2.X86_64.Backend) (s : State) (pre : localContract.pre s) :
    WP isa (code (hash v)) s fun t => localContract.post s t ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame [outputR s, workR s, stackR s] s.mem t.mem := by
  obtain ⟨rd, wr, len, lo, hi, dw, ow, sd, so, sw, _, _⟩ := pre
  obtain work : (workR s) ∈ s.wr := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold code
  refine WP.seq ((setup_ok s work).mono ?_)
  intro a ha
  obtain sp : a.gpr .rsp = s.gpr .rsp := ha.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by
    rw [ha.workspace, ha.wr]; exact work
  obtain dataA : Covers [⟨a.gpr .r12, (a.gpr .r13).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.input, ha.length, ha.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  obtain dwA : (⟨a.gpr .r12, (a.gpr .r13).toNat⟩ : Region).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ha.input, ha.length, ha.workspace]; exact dw
  obtain swA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [sp, ha.workspace]; exact sw
  obtain sdA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .r12, (a.gpr .r13).toNat⟩ := by
    rw [sp, ha.input, ha.length]; exact sd
  obtain inputA : bytesAt a.mem (a.gpr .r12) (a.gpr .r13).toNat =
      bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat := by
    rw [ha.input, ha.length, ha.mem]
    apply Proof.Blake2.bytesAt_congr
    intro i hi'
    apply (setupMem_frame s).bytes (R := inputR s) _ (show (s.gpr .rsi).toNat ≤ 2 ^ 64 by omega_arith) hi'
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact dw.sub_right (Offset.sub_base _ (by decide : 832 + 56 ≤ 16384))
  obtain headA : bytesAt a.mem (a.gpr .rbx + 832) 4 = Spec.Argon2.le32 (a.gpr .r15).toNat := by
    rw [ha.mem, ha.workspace, ha.remaining]; exact setupMem_prefix s
  obtain spaceA : Space a (s.gpr .rcx).toNat := by
    refine ⟨by omega_arith, workA, ?_, ?_, swA, ?_⟩
    · intro i hi'
      rw [ha.wr, ha.output, wr]
      exact ⟨outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [ha.workspace, ha.output]; exact ow.symm
    · rw [sp, ha.output]; exact so
  refine WP.seq ((first_ok v a (by rw [ha.remaining]; exact ⟨lo, hi⟩)
    (by rw [ha.length]; exact len) headA workA dataA dwA swA sdA).mono ?_)
  rintro b ⟨digestB, kb⟩
  obtain spaceB := spaceA.keeps kb
  obtain countB : b.gpr .r15 = BitVec.ofNat 64 (s.gpr .rcx).toNat := by
    rw [kb.regs _ (by decide), ha.remaining, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain digestB' : (bytesAt b.mem (b.gpr .rbx + 768) 64).take (min (s.gpr .rcx).toNat 64) =
      Spec.Argon2.H (min (s.gpr .rcx).toNat 64)
        (Spec.Argon2.le32 (s.gpr .rcx).toNat ++ bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) := by
    rw [kb.rbx]
    simpa only [ha.remaining, inputA] using digestB
  refine WP.seq ((finishOutput_ok v b (s.gpr .rcx).toNat
    (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) spaceB lo countB digestB').mono ?_)
  intro x hx
  obtain baseB : b.gpr .rbx = s.gpr .r8 := kb.rbx.trans ha.workspace
  obtain spB : b.gpr .rsp = s.gpr .rsp := kb.rsp.trans sp
  obtain dstB : b.gpr .r14 = s.gpr .rdx := (kb.regs _ (by decide)).trans ha.output
  obtain wrX : x.wr = s.wr := hx.wr.trans (kb.wr.trans ha.wr)
  obtain frame : Frame [⟨s.gpr .r8, 832⟩, stackR s, outputR s] a.mem x.mem := by
    obtain fb : Frame [⟨s.gpr .r8, 832⟩, stackR s, outputR s] a.mem b.mem := by
      apply kb.frame.sub
      intro r hr
      rw [ha.workspace, sp] at hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    exact fb.trans (by simpa only [baseB, spB, dstB, stackR, outputR, Proof.Argon2.hPrime_length] using hx.frame)
  obtain values : ∀ r d, (r, d) ∈ saved →
      x.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hr
    obtain bounds : ∀ rd ∈ saved, 832 ≤ rd.2 ∧ rd.2 + 8 ≤ 16384 := by decide
    obtain ⟨dlo, dhi⟩ := bounds (r, d) hr
    obtain keep : x.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 =
        a.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 := by
      apply frame.readW (r := ⟨s.gpr .r8 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact (Offset.base_disjoint _ dlo (by omega_arith)).symm
      · exact (sw.sub_right (Offset.sub_base _ dhi)).symm
      · exact (ow.sub_right (Offset.sub_base _ dhi)).symm
    rw [keep, ha.mem]; exact setupMem_saved s r d hr
  obtain baseX := hx.rbx.trans baseB
  obtain spX := hx.rsp.trans spB
  obtain readable : workR s ∈ x.rd ++ x.wr := List.mem_append_right _ (wrX.symm ▸ work)
  refine (restore_ok s x baseX spX readable values).mono ?_
  rintro t ⟨regs, mem, _, _⟩
  refine ⟨?_, regs, ?_⟩
  · change bytesAt t.mem (s.gpr .rdx) (s.gpr .rcx).toNat = _
    rw [mem]
    simpa only [dstB, Proof.Argon2.hPrime_length] using hx.bytes
  · rw [mem]
    obtain setupFrame : Frame [outputR s, workR s, stackR s] s.mem a.mem := by
      rw [ha.mem]
      apply (setupMem_frame s).sub
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        Offset.sub_base _ (by decide : 832 + 56 ≤ 16384)⟩
    apply setupFrame.trans
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨stackR s, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
    · exact ⟨outputR s, List.mem_cons_self .., fun _ h => h⟩

theorem code_mxcsr (v : Proof.Blake2.X86_64.Backend) :
    (code (hash v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  obtain init : (hash v).init.allInstrs (fun i => !loadsMxcsr i) = true := by
    change (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).allInstrs _ = true
    lit_decide
  have update : (hash v).update.allInstrs (fun i => !loadsMxcsr i) = true := v.updateMxcsr
  have finalize : (hash v).finalize.allInstrs (fun i => !loadsMxcsr i) = true := v.finalizeMxcsr
  simp only [code, setup, saved, first, chooseLength, Impl.Argon2.X86_64.HPrime.init,
    initArgs, absorbFixed, fixedArgs, Impl.Argon2.X86_64.HPrime.update, updateArgs,
    absorbInput, inputArgs, finishInput, Impl.Argon2.X86_64.HPrime.finalize, finalizeArgs,
    finishOutput, extendDigest, emitPrefix, copy, copyByte, chain, next, copyRemaining,
    restore, Code.allInstrs]
  rw [init, update, finalize]
  decide +kernel

theorem code_correct (v : Proof.Blake2.X86_64.Backend) (s : State) (pre : localContract.pre s) :
    ∃ tr t, Exec isa (code (hash v)) s tr t ∧ abiPreserved s t ∧ localContract.post s t := by
  obtain ⟨tr, t, run, post, regs, frame⟩ := code_wp v s pre
  refine ⟨tr, t, run, abiPreserved_of_exec (code_mxcsr v) run ⟨regs, ?_⟩, post⟩
  apply frame.readW (r := retR s) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  obtain ⟨_, _, _, _, _, _, _, _, _, _, retOut, retWork⟩ := pre
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact retOut
  · exact retWork
  · exact Offset.base_disjoint_below _ (by decide)

end VG.Proof.Argon2.X86_64.HPrime
