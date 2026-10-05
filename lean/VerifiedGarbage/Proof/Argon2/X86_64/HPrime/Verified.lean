import VerifiedGarbage.Impl.Argon2.X86_64.HPrime
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Blake2.X86_64.Backend
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Copy`. -/
section

/-! # H′: copying digest bytes -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem ea_at (s : State) (r : Reg) (d : Nat) :
    s.ea (at_ r d) = s.gpr r + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, BitVec.ofInt_natCast]

theorem copyByte_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdx) 1)
    (hw : InRegions s.wr (s.gpr .r14) 1) :
    WP isa (.block copyByte) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r14) (s.mem (s.gpr .rdx)) ∧
      t.gpr .rdx = s.gpr .rdx + 1 ∧ t.gpr .r14 = s.gpr .r14 + 1 ∧
      t.gpr .rax = s.gpr .rax - 1 ∧ t.zf = some (s.gpr .rax - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r14 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [copyByte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load8, State.store8, execAlu, ea_at, BitVec.add_zero,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.zf_setReg,
    show (BitVec.signExtend 64 (1 : BitVec 32)) = 1 from rfl,
    hr, hw, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  exact ⟨trivial, trivial, trivial, trivial, trivial,
    fun r h1 h2 h3 h4 => by simp only [h1, h2, h3, h4, ite_false], trivial, trivial⟩

open VG.WriteBytes
open VG.Spec.Blake2 (bytesAt)

/-- The prefix already copied, with every other register preserved. -/
structure CopyI (s₀ : State) (src dst : Addr) (k j : Nat) (s : State) : Prop where
  bound : j ≤ k
  source : s.gpr .rdx = src + BitVec.ofNat 64 j
  destination : s.gpr .r14 = dst + BitVec.ofNat 64 j
  count : s.gpr .rax = BitVec.ofNat 64 (k - j)
  other : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r14 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)

theorem copyLoop_ok (s₀ : State) (src dst : Addr) (k : Nat)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 64)
    (hs : s₀.gpr .rdx = src) (hd : s₀.gpr .r14 = dst)
    (hn : s₀.gpr .rax = BitVec.ofNat 64 k)
    (hr : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < k, InRegions s₀.wr (dst + BitVec.ofNat 64 i) 1)
    (hsep : Region.Disjoint ⟨src, k⟩ ⟨dst, k⟩) :
    WP isa (.loop (.block copyByte) .ne) s₀ (CopyI s₀ src dst k k) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = k - j ∧ j < k ∧ CopyI s₀ src dst k j s)
    ?_ k s₀ ⟨0, by omega, hk, by omega, by simpa using hs, by simpa using hd,
      by simpa using hn, fun _ _ _ _ _ => rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hlen : (bytesAt s₀.mem src k).length = k := by simp [bytesAt]
  have htake : ((bytesAt s₀.mem src k).take j).length = j := by
    rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
  have hb : s.mem (src + BitVec.ofNat 64 j) = s₀.mem (src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    apply (writeBytes_frame s₀.mem dst _ (R := ⟨dst, k⟩)
      (by simpa only [BitVec.add_zero, htake] using
        (Offset.contains_base dst (k := k) (d := 0) (n := j) (by omega) (by decide)))).bytes
        (R := ⟨src, k⟩) _ (show k ≤ 2 ^ 64 by omega) hj
    simpa using hsep
  have hr' : InRegions (s.rd ++ s.wr) (s.gpr .rdx) 1 := by
    rw [h.rd, h.wr, h.source]; exact hr j hj
  have hw' : InRegions s.wr (s.gpr .r14) 1 := by
    rw [h.wr, h.destination]; exact hw j hj
  refine (copyByte_ok s hr' hw').mono ?_
  rintro t ⟨hm, hs', hd', hn', hz, ho, hrd, hwr⟩
  have hc : BitVec.ofNat 64 (k - j) - 1 = BitVec.ofNat 64 (k - (j + 1)) := by
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat (by omega : 1 ≤ k - j)]
    congr 1
  have hi : CopyI s₀ src dst k (j + 1) t := by
    refine ⟨by omega, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, hrd.trans h.rd, hwr.trans h.wr, ?_⟩
    · rw [hs', h.source, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hd', h.destination, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    · rw [hn', h.count, hc]
    · exact (ho r h1 h2 h3 h4).trans (h.other r h1 h2 h3 h4)
    · have hj' : j < (bytesAt s₀.mem src k).length := by omega
      rw [hm, h.source, h.destination, hb, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [htake]; omega), htake]
      refine congrArg (fun b => (writeBytes s₀.mem dst ((bytesAt s₀.mem src k).take j)).writeW
        (dst + BitVec.ofNat 64 j) b) ?_
      simp only [bytesAt, List.getElem_map, List.getElem_range]
  have hz' : t.zf = some (decide (k - (j + 1) = 0)) := by
    rw [hz, h.count, hc]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have ht := congrArg BitVec.toNat he
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k - (j + 1) < 2 ^ 64), show (0 : BitVec 64).toNat = 0 from rfl] using ht
    · intro he; rw [he]; rfl
  by_cases he : j + 1 = k
  · refine .inl ⟨?_, he ▸ hi⟩
    simp only [eval, hz', show k - (j + 1) = 0 by omega, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega, j + 1, rfl, by omega, hi⟩
    simp only [eval, hz', show k - (j + 1) ≠ 0 by omega, decide_false, Option.map_some, Bool.not_false]

end VG.Proof.Argon2.X86_64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Init`. -/
section

/-! Merged from `Proof.Argon2.X86_64.HPrime.Hash`. -/
section
/-!
# H′: the BLAKE2b streaming callee

The H′ proof uses the shared BLAKE2b streaming contracts. Its hash
implementation is supplied by a variant, including the stack bounds and
instruction properties needed to compose verified calls. No compression
implementation is chosen here.
-/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

/-- Obligations of any streaming BLAKE2b backend used by H′. -/
structure HashOk (h : Hash) : Prop where
  init : Verified X86_64.target h.init (Spec.Blake2.initBContract X86_64.abi)
  update : Verified X86_64.target h.update (Spec.Blake2.updateBScratchContract X86_64.abi 8)
  finalize : Verified X86_64.target h.finalize (Spec.Blake2.finalizeBScratchContract X86_64.abi 8)
  initNoSp : NoSp h.init
  updateNoSp : NoSp h.update
  finalizeNoSp : NoSp h.finalize
  initDepth : h.init.depth = 0
  updateDepth : h.update.depth = 1
  finalizeDepth : h.finalize.depth = 1

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.Backend`. -/
section
/-! # H′ uses any BLAKE2b backend -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64

/-- The symbols and code of one BLAKE2b streaming backend. -/
def hash (v : Proof.Blake2.X86_64.Backend) : Impl.Argon2.X86_64.HPrime.Hash where
  initName := Spec.Blake2.initBApi.name
  init := v.init
  updateName := v.updateName
  update := v.update
  finalizeName := v.finalizeName
  finalize := v.finalize

private theorem nosp_of_check {c : Prog isa}
    (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa only [Bool.not_eq_true'] using List.all_eq_true.mp h i hi

private theorem callee_check (v : Proof.Blake2.X86_64.Backend) :
    v.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  simpa only [Bool.not_eq_true'] using v.callee.nosp i hi

open Impl.Blake2.X86_64.Stream in
private theorem update_nosp (v : Proof.Blake2.X86_64.Backend) : NoSp v.update := by
  apply nosp_of_check
  simp only [Proof.Blake2.X86_64.Backend.update, Proof.Blake2.X86_64.Backend.hashCallee,
    update, updateStart, save, saved, bufLen, head, fill, copyLoop, compressBuf,
    compressWith, rest, direct, tail, restore, Code.allInstrs]
  rw [callee_check v]
  decide +kernel

open Impl.Blake2.X86_64.Stream in
private theorem finalize_nosp (v : Proof.Blake2.X86_64.Backend) : NoSp v.finalize := by
  apply nosp_of_check
  simp only [Proof.Blake2.X86_64.Backend.finalize, Proof.Blake2.X86_64.Backend.hashCallee,
    finalize, save, saved, bufLen, pad, zeroLoop, compressLast, compressWith, output,
    restore, Code.allInstrs]
  rw [callee_check v]
  decide +kernel

open Impl.Blake2.X86_64.Stream in
theorem hash_ok (v : Proof.Blake2.X86_64.Backend) : HashOk (hash v) := by
  refine ⟨v.init_verified, v.update_verified, v.finalize_verified, ?_, update_nosp v,
    finalize_nosp v, ?_, ?_, ?_⟩
  · apply nosp_of_check
    change (init Spec.Blake2.b).allInstrs _ = true
    lit_decide
  · rfl
  · simp only [hash, Proof.Blake2.X86_64.Backend.update, Proof.Blake2.X86_64.Backend.hashCallee,
      update, bufLen, head, fill, copyLoop, compressBuf, compressWith, rest, direct, tail,
      Code.depth, v.callee.depth]
    rfl
  · simp only [hash, Proof.Blake2.X86_64.Backend.finalize, Proof.Blake2.X86_64.Backend.hashCallee,
      finalize, bufLen, pad, zeroLoop, compressLast, compressWith, Code.depth, v.callee.depth]
    rfl

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: initializing an unkeyed BLAKE2b computation -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure InitArgs (s t : State) : Prop where
  state : t.gpr .rdi = s.gpr .rbx
  key : t.gpr .rdx = s.gpr .rbx + 832
  keylen : t.gpr .rcx = 0
  other : ∀ r, r ≠ .rdi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem initArgs_ok (s : State) : WP isa (.block initArgs) s (InitArgs s) := by
  apply WP.of_runBlock
  simp only [initArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, execAlu, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, ite_false]

/-- The narrowed BLAKE2b call and its permissions, shared by correctness and timing. -/
theorem init_call_hyps (s u : State) (hu : InitArgs s u)
    (hlen : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (hret : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rbx, 192⟩) :
    (Proof.Blake2.initX86_64 Spec.Blake2.b).pre
      (u.callEntry.withRegions [⟨s.gpr .rbx + 832, 0⟩] [⟨s.gpr .rbx, 192⟩]) ∧
    Covers [⟨s.gpr .rbx + 832, 0⟩, ⟨s.gpr .rbx, 192⟩] (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .rbx, 192⟩] u.wr := by
  have hsp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide) (by decide)
  have hlen' : u.gpr .rsi = s.gpr .rsi := hu.other _ (by decide) (by decide) (by decide)
  have g : ∀ r, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have hp : (Proof.Blake2.initX86_64 Spec.Blake2.b).pre
      (u.callEntry.withRegions [⟨s.gpr .rbx + 832, 0⟩] [⟨s.gpr .rbx, 192⟩]) := by
    simp only [Proof.Blake2.initX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp),
      g _ (by decide : Reg.rdx ≠ .rsp), g _ (by decide : Reg.rcx ≠ .rsp),
      g _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_rsp,
      hu.state, hu.key, hu.keylen, hlen', hsp]
    refine ⟨rfl, rfl, ?_, hret, hlen.1, hlen.2, by decide⟩
    exact (Offset.base_disjoint (s.gpr .rbx) (e := 832) (n := 0) (k := 192) (by decide) (by decide)).symm
  have cover : Covers [⟨s.gpr .rbx + 832, 0⟩, ⟨s.gpr .rbx, 192⟩] (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .rbx, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), ?_⟩
    rcases hr with rfl | rfl
    · exact ⟨832, rfl, by change 832 ≤ 16384; decide⟩
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
  have writes : Covers [⟨s.gpr .rbx, 192⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨⟨s.gpr .rbx, 16384⟩, hu.wr.symm ▸ hwr, 0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
  exact ⟨hp, cover, writes⟩

theorem init_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (hlen : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (hret : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rbx, 192⟩) :
    WP isa (init (hash v)) s fun t =>
      Spec.Blake2.Repr Spec.Blake2.b (Spec.Blake2.init Spec.Blake2.b (s.gpr .rsi).toNat 0)
        t.mem (s.gpr .rbx) [] ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨s.gpr .rbx, 192⟩, below (s.gpr .rsp) 8] s.mem t.mem := by
  unfold init
  refine WP.seq ((initArgs_ok s).mono fun u hu => ?_)
  have hsp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide) (by decide)
  have hlen' : u.gpr .rsi = s.gpr .rsi := hu.other _ (by decide) (by decide) (by decide)
  have g : ∀ r, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  obtain ⟨hp, cover, writes⟩ := init_call_hyps s u hu hlen hwr hret
  refine WP.call (k := Proof.Blake2.initX86_64 Spec.Blake2.b)
    Proof.Blake2.X86_64.Stream.initB_correct (hash_ok v).initNoSp
    (by decide) hp cover writes ?_
  intro t rd wr cs frame keep ⟨t', hm, hg, post⟩
  have post' := post
  simp only [Proof.Blake2.initX86_64, State.withRegions_gpr, g _ (by decide : Reg.rdi ≠ .rsp),
    g _ (by decide : Reg.rsi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
    g _ (by decide : Reg.rcx ≠ .rsp), hu.state, hu.key, hu.keylen, hlen', hm,
    Spec.Blake2.bytesAt, Spec.Blake2.keyBlock] at post'
  refine ⟨post', fun r hr => (cs r hr).trans ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · simpa only [show (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).depth = 0 from rfl, Nat.zero_add, Nat.mul_one, hsp, hu.mem,
      List.singleton_append, List.nil_append] using frame

end VG.Proof.Argon2.X86_64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Update`. -/
section

/-! # H′: absorbing bytes with the selected BLAKE2b backend -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.X86_64 (callEntry_byte)

structure UpdateArgs (s t : State) : Prop where
  state : t.gpr .rdi = s.gpr .rbx
  scratch : t.gpr .r8 = s.gpr .rbx + 192
  other : ∀ r, r ≠ .rdi → r ≠ .r8 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem updateArgs_ok (s : State) : WP isa (.block updateArgs) s (VG.Proof.Argon2.X86_64.HPrime.UpdateArgs s) := by
  apply WP.of_runBlock
  simp only [updateArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, ite_false]

/-- The narrowed streaming call, without assumptions about message contents. -/
theorem update_call_hyps (s u : State) (hu : VG.Proof.Argon2.X86_64.HPrime.UpdateArgs s u)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 192⟩)
    (dataScratch : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx + 192, 576⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) :
    (Proof.Blake2.updateX86_64 b).pre (u.callEntry.withRegions
      [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 192, 576⟩]) ∧
    Covers ([⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ++
      [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 192, 576⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 192, 576⟩] u.wr := by
  have g : ∀ r, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide)
  have src : u.gpr .rdx = s.gpr .rdx := hu.other _ (by decide) (by decide)
  have len : u.gpr .rcx = s.gpr .rcx := hu.other _ (by decide) (by decide)
  have subState : Region.Sub ⟨s.gpr .rbx, 192⟩ ⟨s.gpr .rbx, 16384⟩ := Region.sub_prefix (by decide)
  have subScratch : Region.Sub ⟨s.gpr .rbx + 192, 576⟩ ⟨s.gpr .rbx, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have retSub : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by decide) (by decide)
  have nestSub := below_callee (s.gpr .rsp) 8
  have hp : (Proof.Blake2.updateX86_64 b).pre (u.callEntry.withRegions
      [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩]
      [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 192, 576⟩]) := by
    simp only [Proof.Blake2.updateX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
      g _ (by decide : Reg.rcx ≠ .rsp), g _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_rsp,
      hu.state, hu.scratch, src, len, sp]
    exact ⟨trivial, rfl, Offset.base_disjoint _ (by decide) (by decide), dataState, dataScratch,
      (stackWork.sub_left retSub).sub_right subState, (stackWork.sub_left retSub).sub_right subScratch,
      (stackWork.sub_left nestSub).sub_right subState, stackData.sub_left nestSub,
      (stackWork.sub_left nestSub).sub_right subScratch⟩
  have writes : Covers [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 192, 576⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .rbx, 16384⟩, hu.wr.symm ▸ hwr, ?_⟩
    rcases hr with rfl | rfl
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
    · exact ⟨192, rfl, by change 192 + 576 ≤ 16384; decide⟩
  have cover : Covers ([⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] ++
      [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 192, 576⟩]) (u.rd ++ u.wr) := by
    intro a n ⟨r, hr, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · rw [hu.rd, hu.wr]; exact hdata a n ⟨r, hr, hc⟩
    · obtain ⟨r', hr', hc'⟩ := writes a n ⟨r, hr, hc⟩
      exact ⟨r', List.mem_append_right _ hr', hc'⟩
  exact ⟨hp, cover, writes⟩

theorem update_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .rbx) d)
    (count : s.gpr .rsi = BitVec.ofNat 64 d.length)
    (bound : d.length + (s.gpr .rcx).toNat < 2 ^ 64)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (hdata : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] (s.rd ++ s.wr))
    (dataState : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 192⟩)
    (dataScratch : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx + 192, 576⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩) :
    WP isa (update (hash v)) s fun t =>
      Repr b h0 t.mem (s.gpr .rbx) (d ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 192, 576⟩, below (s.gpr .rsp) 16] s.mem t.mem := by
  unfold update
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.updateArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide)
  have src : u.gpr .rdx = s.gpr .rdx := hu.other _ (by decide) (by decide)
  have len : u.gpr .rcx = s.gpr .rcx := hu.other _ (by decide) (by decide)
  have cnt : u.gpr .rsi = s.gpr .rsi := hu.other _ (by decide) (by decide)
  have subState : Region.Sub ⟨s.gpr .rbx, 192⟩ ⟨s.gpr .rbx, 16384⟩ := Region.sub_prefix (by decide)
  have subScratch : Region.Sub ⟨s.gpr .rbx + 192, 576⟩ ⟨s.gpr .rbx, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have retSub : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by decide) (by decide)
  have nestSub := below_callee (s.gpr .rsp) 8
  obtain ⟨hp, cover, writes⟩ := VG.Proof.Argon2.X86_64.HPrime.update_call_hyps s u hu hwr hdata dataState dataScratch stackWork stackData
  have retState : (below (u.gpr .rsp) 8).Disjoint ⟨s.gpr .rbx, 192⟩ := by
    rw [sp]; exact (stackWork.sub_left retSub).sub_right subState
  have retData : (below (u.gpr .rsp) 8).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ := by
    rw [sp]; exact stackData.sub_left retSub
  have repr' : Repr b h0 u.callEntry.mem (s.gpr .rbx) d := by
    apply Proof.Blake2.X86_64.Stream.Update.repr_congr Proof.Blake2.X86_64.Stream.okB
      (mem := s.mem) _ repr
    intro i hi
    rw [callEntry_byte u retState (show 192 ≤ 2 ^ 64 by decide) hi, hu.mem]
  have bytes : bytesAt u.callEntry.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
      bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    rw [callEntry_byte u retData (Nat.le_of_lt (s.gpr .rcx).isLt) hi, hu.mem]
  refine WP.call (k := Proof.Blake2.updateX86_64 b) v.update_correct (hash_ok v).updateNoSp
    (by change 8 * (hash v).update.depth + 16 < 2 ^ 64; rw [(hash_ok v).updateDepth]; decide)
    hp cover writes ?_
  intro t rd wr cs frame keep ⟨t', hm, hg, post⟩
  simp only [Proof.Blake2.updateX86_64, State.withRegions_gpr, State.withRegions_mem,
    g _ (by decide : Reg.rdi ≠ .rsp), g _ (by decide : Reg.rsi ≠ .rsp),
    g _ (by decide : Reg.rdx ≠ .rsp), g _ (by decide : Reg.rcx ≠ .rsp),
    hu.state, src, len, cnt, hm] at post
  have result := post h0 d repr' count bound
  rw [bytes] at result
  refine ⟨result, fun r hr => (cs r hr).trans ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .r8 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2
  · change Frame (_ ++ [below (u.gpr .rsp) (8 * ((hash v).update.depth + 1))]) u.mem t.mem at frame
    simpa only [(hash_ok v).updateDepth, sp, hu.mem, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.X86_64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Finalize`. -/
section

/-! # H′: finishing a BLAKE2b hash -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Spec.Blake2 (b Repr bytesAt)
open VG.Proof.MdStream.X86_64 (callEntry_byte)

structure FinalizeArgs (s t : State) : Prop where
  state : t.gpr .rdi = s.gpr .rbx
  digest : t.gpr .rdx = s.gpr .rbx + 768
  scratch : t.gpr .rcx = s.gpr .rbx + 192
  other : ∀ r, r ≠ .rdi → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem finalizeArgs_ok (s : State) : WP isa (.block finalizeArgs) s (VG.Proof.Argon2.X86_64.HPrime.FinalizeArgs s) := by
  apply WP.of_runBlock
  simp only [finalizeArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h1, h2, h3, ite_false]

/-- The narrowed finalization call, independently of the represented message. -/
theorem finalize_call_hyps (s u : State) (hu : VG.Proof.Argon2.X86_64.HPrime.FinalizeArgs s u)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    (Proof.Blake2.finalizeX86_64 b).pre (u.callEntry.withRegions []
      [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩, ⟨s.gpr .rbx + 192, 576⟩]) ∧
    Covers ([] ++ [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩,
      ⟨s.gpr .rbx + 192, 576⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩, ⟨s.gpr .rbx + 192, 576⟩] u.wr := by
  have g : ∀ r, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide) (by decide)
  have subState : Region.Sub ⟨s.gpr .rbx, 192⟩ ⟨s.gpr .rbx, 16384⟩ := Region.sub_prefix (by decide)
  have subDigest : Region.Sub ⟨s.gpr .rbx + 768, 64⟩ ⟨s.gpr .rbx, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have subScratch : Region.Sub ⟨s.gpr .rbx + 192, 576⟩ ⟨s.gpr .rbx, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have retSub : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by decide) (by decide)
  have nestSub := below_callee (s.gpr .rsp) 8
  have hp : (Proof.Blake2.finalizeX86_64 b).pre (u.callEntry.withRegions []
      [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩, ⟨s.gpr .rbx + 192, 576⟩]) := by
    simp only [Proof.Blake2.finalizeX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, g _ (by decide : Reg.rdi ≠ .rsp), g _ (by decide : Reg.rdx ≠ .rsp),
      g _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_rsp, hu.state, hu.digest, hu.scratch, sp]
    exact ⟨trivial, rfl, Offset.base_disjoint _ (by decide) (by decide),
      Offset.base_disjoint _ (by decide) (by decide), (Offset.disjoint _ (by decide) (by decide) (by decide)).symm,
      (stackWork.sub_left retSub).sub_right subState, (stackWork.sub_left retSub).sub_right subDigest,
      (stackWork.sub_left retSub).sub_right subScratch, (stackWork.sub_left nestSub).sub_right subState,
      (stackWork.sub_left nestSub).sub_right subDigest, (stackWork.sub_left nestSub).sub_right subScratch⟩
  have writes : Covers [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩, ⟨s.gpr .rbx + 192, 576⟩] u.wr := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨⟨s.gpr .rbx, 16384⟩, hu.wr.symm ▸ hwr, ?_⟩
    rcases hr with rfl | rfl | rfl
    · exact ⟨0, (BitVec.add_zero _).symm, by change 192 ≤ 16384; decide⟩
    · exact ⟨768, rfl, by change 768 + 64 ≤ 16384; decide⟩
    · exact ⟨192, rfl, by change 192 + 576 ≤ 16384; decide⟩
  have cover : Covers ([] ++ [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩,
      ⟨s.gpr .rbx + 192, 576⟩]) (u.rd ++ u.wr) := by
    intro a n h
    obtain ⟨r, hr, hc⟩ := writes a n h
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  exact ⟨hp, cover, writes⟩

theorem finalize_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (h0 : Spec.Blake2.HashValue 64) (d : List Byte)
    (repr : Repr b h0 s.mem (s.gpr .rbx) d)
    (count : s.gpr .rsi = BitVec.ofNat 64 d.length) (bound : d.length < 2 ^ 64)
    (hwr : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (finalize (hash v)) s fun t =>
      bytesAt t.mem (s.gpr .rbx + 768) 64 = Spec.Blake2.finalHash b h0 d ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨s.gpr .rbx, 192⟩, ⟨s.gpr .rbx + 768, 64⟩,
        ⟨s.gpr .rbx + 192, 576⟩, below (s.gpr .rsp) 16] s.mem t.mem := by
  unfold finalize
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.finalizeArgs_ok s).mono fun u hu => ?_)
  have g : ∀ r, r ≠ .rsp → u.callEntry.gpr r = u.gpr r := fun r hr => State.callEntry_gpr u hr
  have sp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide) (by decide)
  have cnt : u.gpr .rsi = s.gpr .rsi := hu.other _ (by decide) (by decide) (by decide)
  have subState : Region.Sub ⟨s.gpr .rbx, 192⟩ ⟨s.gpr .rbx, 16384⟩ := Region.sub_prefix (by decide)
  have subDigest : Region.Sub ⟨s.gpr .rbx + 768, 64⟩ ⟨s.gpr .rbx, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have subScratch : Region.Sub ⟨s.gpr .rbx + 192, 576⟩ ⟨s.gpr .rbx, 16384⟩ :=
    Offset.sub_base _ (by decide)
  have retSub : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by decide) (by decide)
  have nestSub := below_callee (s.gpr .rsp) 8
  obtain ⟨hp, cover, writes⟩ := VG.Proof.Argon2.X86_64.HPrime.finalize_call_hyps s u hu hwr stackWork
  have retState : (below (u.gpr .rsp) 8).Disjoint ⟨s.gpr .rbx, 192⟩ := by
    rw [sp]; exact (stackWork.sub_left retSub).sub_right subState
  have repr' : Repr b h0 u.callEntry.mem (s.gpr .rbx) d := by
    apply Proof.Blake2.X86_64.Stream.Update.repr_congr Proof.Blake2.X86_64.Stream.okB
      (mem := s.mem) _ repr
    intro i hi
    rw [callEntry_byte u retState (show 192 ≤ 2 ^ 64 by decide) hi, hu.mem]
  refine WP.call (k := Proof.Blake2.finalizeX86_64 b) v.finalize_correct (hash_ok v).finalizeNoSp
    (by change 8 * (hash v).finalize.depth + 16 < 2 ^ 64; rw [(hash_ok v).finalizeDepth]; decide)
    hp cover writes ?_
  intro t rd wr cs frame keep ⟨t', hm, hg, post⟩
  simp only [Proof.Blake2.finalizeX86_64, State.withRegions_gpr, State.withRegions_mem,
    g _ (by decide : Reg.rdi ≠ .rsp), g _ (by decide : Reg.rsi ≠ .rsp),
    g _ (by decide : Reg.rdx ≠ .rsp), hu.state, hu.digest, cnt, hm] at post
  refine ⟨post h0 d repr' bound count, fun r hr => (cs r hr).trans ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · change Frame (_ ++ [below (u.gpr .rsp) (8 * ((hash v).finalize.depth + 1))]) u.mem t.mem at frame
    simpa only [(hash_ok v).finalizeDepth, sp, hu.mem, List.cons_append, List.nil_append] using frame

end VG.Proof.Argon2.X86_64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Fixed`. -/
section

/-! # H′: arguments for a fixed workspace buffer -/

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
    WP isa (.block (fixedArgs offset size)) s fun t => VG.Proof.Argon2.X86_64.HPrime.FixedArgs s t offset size := by
  have hoff := Proof.MdStream.X86_64.sx_ofNat ho
  have hsize : (BitVec.ofNat 32 size).setWidth 64 = BitVec.ofNat 64 size := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (by omega : size < 2 ^ 64)]
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

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Frame`. -/
section

/-! # H′: the memory changed by hashing a workspace buffer -/

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
  apply VG.Proof.Argon2.X86_64.HPrime.workspace_frame p sp [(0, 192)] 8 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero] using h

theorem update_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, ⟨p + 192, 576⟩, below sp 16] m m') :
    Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply VG.Proof.Argon2.X86_64.HPrime.workspace_frame p sp [(0, 192), (192, 576)] 16 (by decide) (by decide)
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, BitVec.add_zero,
    show BitVec.ofNat 64 192 = (192 : Addr) from rfl] using h

theorem finalize_frame {m m' : Mem} (p sp : Addr)
    (h : Frame [⟨p, 192⟩, ⟨p + 768, 64⟩, ⟨p + 192, 576⟩, below sp 16] m m') :
    Frame [⟨p, 832⟩, below sp 16] m m' := by
  apply VG.Proof.Argon2.X86_64.HPrime.workspace_frame p sp [(0, 192), (768, 64), (192, 576)] 16 (by decide) (by decide)
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

theorem Keeps.rbx {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.Keeps s t) : t.gpr .rbx = s.gpr .rbx :=
  h.regs _ (by decide)

theorem Keeps.rsp {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.Keeps s t) : t.gpr .rsp = s.gpr .rsp :=
  h.regs _ (by decide)

theorem Keeps.trans {s t u : State} (h : VG.Proof.Argon2.X86_64.HPrime.Keeps s t) (h' : VG.Proof.Argon2.X86_64.HPrime.Keeps t u) : VG.Proof.Argon2.X86_64.HPrime.Keeps s u where
  regs r hr := (h'.regs r hr).trans (h.regs r hr)
  rd := h'.rd.trans h.rd
  wr := h'.wr.trans h.wr
  frame := h.frame.trans (by simpa only [h.rbx, h.rsp] using h'.frame)

theorem Keeps.bytes {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.Keeps s t) (r : Region) (bound : r.len ≤ 2 ^ 64)
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

theorem Keeps.prefix {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.Keeps s t)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    Spec.Blake2.bytesAt t.mem (s.gpr .rbx + 832) 4 =
      Spec.Blake2.bytesAt s.mem (s.gpr .rbx + 832) 4 :=
  h.bytes ⟨s.gpr .rbx + 832, 4⟩ (show 4 ≤ 2 ^ 64 by decide)
    (Offset.base_disjoint _ (e := 832) (n := 4) (k := 832) (by decide) (by decide)).symm
    (stackWork.sub_right (Offset.sub_base _ (by decide : 832 + 4 ≤ 16384))).symm

end VG.Proof.Argon2.X86_64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Absorb`. -/
section

/-! # H′: absorbing the length prefix or previous digest -/

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
      VG.Proof.Argon2.X86_64.HPrime.Keeps s t := by
  unfold absorbFixed
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.fixedArgs_ok s offset size (by omega) (by omega)).mono fun u hu => ?_)
  have p : u.gpr .rbx = s.gpr .rbx := hu.other _ (by decide) (by decide) (by decide)
  have sp : u.gpr .rsp = s.gpr .rsp := hu.other _ (by decide) (by decide) (by decide)
  have len : (u.gpr .rcx).toNat = size := by
    rw [hu.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have wr : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [p, hu.wr]; exact hwr
  have hr : Repr b h0 u.mem (u.gpr .rbx) [] := by rw [hu.mem, p]; exact repr
  have hc : u.gpr .rsi = BitVec.ofNat 64 ([] : List Byte).length := hu.count
  have hb : ([] : List Byte).length + (u.gpr .rcx).toNat < 2 ^ 64 := by simp only [List.length_nil, Nat.zero_add, len]; omega
  have cover : Covers [⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩] (u.rd ++ u.wr) := by
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .rbx, 16384⟩, List.mem_append_right _ (hu.wr.symm ▸ hwr), offset, hu.data, ?_⟩
    change offset + (u.gpr .rcx).toNat ≤ 16384
    rw [len]; exact sizeBound
  have ds : (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region).Disjoint ⟨u.gpr .rbx, 192⟩ := by
    rw [hu.data, len, p]
    exact (Offset.base_disjoint _ (by omega) (by omega)).symm
  have dw : (⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ : Region).Disjoint ⟨u.gpr .rbx + 192, 576⟩ := by
    rw [hu.data, len, p]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega) (by omega) (by decide)
  have sw : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
    rw [sp, p]; exact stackWork
  have sd : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rdx, (u.gpr .rcx).toNat⟩ := by
    rw [sp, hu.data, len]
    exact stackWork.sub_right (Offset.sub_base _ sizeBound)
  refine (VG.Proof.Argon2.X86_64.HPrime.update_ok v u h0 [] hr hc hb wr cover ds dw sw sd).mono ?_
  rintro t ⟨repr', regs, rd, wr', frame⟩
  simp only [p, hu.data, len, hu.mem, List.nil_append] at repr'
  refine ⟨repr', fun r hr => (regs r hr).trans ?_, rd.trans hu.rd, wr'.trans hu.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact hu.other r hn.1 hn.2.1 hn.2.2
  · simpa only [p, sp, hu.mem] using VG.Proof.Argon2.X86_64.HPrime.update_frame (u.gpr .rbx) (u.gpr .rsp) frame

end VG.Proof.Argon2.X86_64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Output`. -/
section

/-! # H′: emitting a digest or its 32-byte prefix -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov wp_addi wp_mov32i wp_subi)
open VG.Spec.Blake2 (bytesAt)
open VG.WriteBytes

theorem bytesAt_writeBytes (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (VG.WriteBytes.writeBytes m p xs) p xs.length = xs := by
  apply List.ext_getElem (by simp only [bytesAt, List.length_map, List.length_range])
  intro i _ hi
  simp only [bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeBytes,
    Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    hi, ite_true, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem bytesAt_take (m : Mem) (p : Addr) (n k : Nat) (hn : n ≤ k) :
    (bytesAt m p k).take n = bytesAt m p n := by
  simp only [bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left hn]

structure Copied (s : State) (k : Nat) (t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + BitVec.ofNat 64 k
  other : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r14 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .r14) (bytesAt s.mem (s.gpr .rbx + 768) k)

theorem copy_ok (s : State) (k : Nat) (lo : 1 ≤ k) (hi : k ≤ 64)
    (count : s.gpr .rax = BitVec.ofNat 64 k)
    (work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < k, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .rbx + 768, k⟩ : Region).Disjoint ⟨s.gpr .r14, k⟩) :
    WP isa VG.Impl.Argon2.X86_64.HPrime.copy s (VG.Proof.Argon2.X86_64.HPrime.Copied s k) := by
  unfold VG.Impl.Argon2.X86_64.HPrime.copy
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
      Offset.contains_base _ (by omega : 768 + i + 1 ≤ 16384) (by omega)⟩
  refine (VG.Proof.Argon2.X86_64.HPrime.copyLoop_ok u _ _ k lo (by omega) src (other .r14 (by decide))
    ((other .rax (by decide)).trans count) read ?_ sep).mono ?_
  · intro i hi'; rw [wr]; exact out i hi'
  · intro t ht
    refine ⟨ht.destination, fun r h1 h2 h3 h4 => (ht.other r h1 h2 h3 h4).trans (other r h3),
      ht.rd.trans rd, ht.wr.trans wr, ?_⟩
    rw [ht.mem, mem, List.take_of_length_le]
    simp only [bytesAt, List.length_map, List.length_range, Nat.le_refl]

theorem Copied.frame {s t : State} {k : Nat} (h : VG.Proof.Argon2.X86_64.HPrime.Copied s k t) :
    Frame [⟨s.gpr .r14, k⟩] s.mem t.mem := by
  rw [h.mem]
  apply VG.WriteBytes.writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .r14) (d := 0) (n := k) (k := k) (by omega) (by decide)

structure Emitted (s t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + 32
  remaining : t.gpr .r15 = s.gpr .r15 - 32
  other : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .r14) (bytesAt s.mem (s.gpr .rbx + 768) 32)

theorem emitPrefix_ok (s : State)
    (work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .rbx + 768, 32⟩ : Region).Disjoint ⟨s.gpr .r14, 32⟩) :
    WP isa emitPrefix s (VG.Proof.Argon2.X86_64.HPrime.Emitted s) := by
  unfold emitPrefix
  refine WP.seq (wp_mov32i fun a ha _ _ => WP.block_nil ?_)
  have base : a.gpr .rbx = s.gpr .rbx := ha.other _ (by decide)
  have dst : a.gpr .r14 = s.gpr .r14 := ha.other _ (by decide)
  have workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact work
  have outA : ∀ i < 32, InRegions a.wr (a.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact out
  have sepA : (⟨a.gpr .rbx + 768, 32⟩ : Region).Disjoint ⟨a.gpr .r14, 32⟩ := by
    rw [base, dst]; exact sep
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.copy_ok a 32 (by decide) (by decide) ha.gpr workA outA sepA).mono ?_)
  intro u hu
  refine wp_subi fun t ht _ => WP.block_nil ?_
  refine ⟨?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, ht.rd.trans (hu.rd.trans ha.rd),
    ht.wr.trans (hu.wr.trans ha.wr), ?_⟩
  · rw [ht.other _ (by decide), hu.output, dst]; rfl
  · rw [ht.gpr, hu.other _ (by decide) (by decide) (by decide) (by decide), ha.other _ (by decide)]
    rfl
  · exact (ht.other r h5).trans ((hu.other r h1 h2 h3 h4).trans (ha.other r h1))
  · rw [ht.mem, hu.mem, ha.mem, base, dst]

theorem Emitted.frame {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.Emitted s t) :
    Frame [⟨s.gpr .r14, 32⟩] s.mem t.mem := by
  rw [h.mem]
  apply VG.WriteBytes.writeBytes_frame
  simpa only [bytesAt, List.length_map, List.length_range, BitVec.add_zero] using
    Offset.contains_base (s.gpr .r14) (d := 0) (n := 32) (k := 32) (by decide) (by decide)

theorem Emitted.digest {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.Emitted s t)
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

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Chain`. -/
section

/-! Merged from `Proof.Argon2.X86_64.HPrime.Next`. -/
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
        Spec.Argon2.H (s.gpr .rsi).toNat (bytesAt s.mem (s.gpr .rbx + 768) 64) ∧ VG.Proof.Argon2.X86_64.HPrime.Keeps s t := by
  unfold next
  have retSub : Region.Sub (below (s.gpr .rsp) 8) (below (s.gpr .rsp) 16) := below_sub (by decide) (by decide)
  have retState := (stackWork.sub_left retSub).sub_right
    (Region.sub_prefix (base := s.gpr .rbx) (len := 192) (len' := 16384) (by decide))
  refine WP.seq ((init_ok v s hlen hwr retState).mono ?_)
  rintro a ⟨reprA, regsA, rdA, wrA, frameA⟩
  have ka : VG.Proof.Argon2.X86_64.HPrime.Keeps s a := ⟨regsA, rdA, wrA, VG.Proof.Argon2.X86_64.HPrime.init_frame _ _ frameA⟩
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
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.absorbFixed_ok v a _ 768 64 (by decide) (by decide) reprA' wrA' swA).mono ?_)
  rintro u ⟨reprU, ku⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (s.gpr .rsi).toNat 0) u.mem (u.gpr .rbx)
      (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [ku.rbx]
    simpa only [show BitVec.ofNat 64 768 = (768 : Addr) from rfl, digest] using reprU
  refine WP.seq (wp_mov32i fun w hw _ _ => WP.block_nil ?_)
  have kw : VG.Proof.Argon2.X86_64.HPrime.Keeps u w := by
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
  refine (VG.Proof.Argon2.X86_64.HPrime.finalize_ok v w _ _ reprW count bound wrW swW).mono ?_
  rintro t ⟨out, regsT, rdT, wrT, frameT⟩
  refine ⟨?_, ksw.trans ⟨regsT, rdT, wrT, VG.Proof.Argon2.X86_64.HPrime.finalize_frame _ _ frameT⟩⟩
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
      s (VG.Proof.Argon2.X86_64.HPrime.ChainStep s) := by
  refine WP.seq (wp_mov32i fun a ha _ _ => WP.block_nil ?_)
  have ka : VG.Proof.Argon2.X86_64.HPrime.Keeps s a := by
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
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.next_ok v a (by rw [lengthA]; decide) workA stackA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .r14 = s.gpr .r14 := ksu.regs _ (by decide)
  have digestU : bytesAt u.mem (s.gpr .rbx + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    simpa only [lengthA, ka.rbx, ha.mem, VG.Proof.Argon2.X86_64.HPrime.bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ksu.rbx, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .rbx + 768, 32⟩ : Region).Disjoint ⟨u.gpr .r14, 32⟩ := by
    rw [ksu.rbx, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.emitPrefix_ok u workU outU sepU).mono ?_)
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
  · rw [mt, hw.mem, dstU, ksu.rbx, ← digestU, VG.Proof.Argon2.X86_64.HPrime.bytesAt_take _ _ 32 64 (by decide)]
    exact VG.Proof.Argon2.X86_64.HPrime.bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
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

theorem ChainResult.refl (s : State) : VG.Proof.Argon2.X86_64.HPrime.ChainResult s 0 s :=
  ⟨by simp, by simp, fun _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem ChainResult.cons {s u t : State} {n : Nat} (step : VG.Proof.Argon2.X86_64.HPrime.ChainStep s u)
    (tail : VG.Proof.Argon2.X86_64.HPrime.ChainResult u n t) (bound : 32 * (n + 1) < 2 ^ 64)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32 * (n + 1)⟩)
    (stackOut : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, 32 * (n + 1)⟩) :
    VG.Proof.Argon2.X86_64.HPrime.ChainResult s (n + 1) t := by
  have base := step.regs .rbx (by decide) (by decide) (by decide)
  have sp := step.regs .rsp (by decide) (by decide) (by decide)
  have sum : 32 * (n + 1) = 32 + 32 * n := by omega
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
  · exact (extend 0 32 (by omega) (by simpa only [BitVec.add_zero] using step.frame)).trans
      (extend 32 (32 * n) (by omega) tf)
  · rw [← base, tail.digest, base, step.digest]
    rfl
  · have before : bytesAt t.mem (s.gpr .r14) 32 = bytesAt u.mem (s.gpr .r14) 32 := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .r14, 32⟩) _ (show 32 ≤ 2 ^ 64 by decide) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left
          (Region.sub_prefix (by omega))
      · exact stackOut.symm.sub_left (Region.sub_prefix (by omega))
      · exact Offset.base_disjoint _ (e := 32) (n := 32 * n) (k := 32) (by decide) (by omega)
    rw [sum, Proof.Blake2.bytesAt_add, before, step.bytes,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl, ← step.output, tail.bytes,
      base, step.digest]
    rfl

theorem chain_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (positive : 1 ≤ n) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (bound : 32 * n + lastLen < 2 ^ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen))
    (work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32 * n, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32 * n⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩)
    (stackOut : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, 32 * n⟩) :
    WP isa (chain (hash v)) s (VG.Proof.Argon2.X86_64.HPrime.ChainResult s n) := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    have out32 : ∀ i < 32, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1 :=
      fun i hi => out i (by omega)
    have sep32 := sep.sub_right (Region.sub_prefix (show 32 ≤ 32 * (n + 1) by omega))
    obtain ⟨trace, u, run, step⟩ := VG.Proof.Argon2.X86_64.HPrime.chainStep_ok v s work out32 sep32 stackWork
    have base := step.regs .rbx (by decide) (by decide) (by decide)
    have sp := step.regs .rsp (by decide) (by decide) (by decide)
    have countU : u.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen) := by
      rw [step.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
        Offset.ofNat_sub_ofNat (by omega : 32 ≤ 32 * (n + 1) + lastLen)]
      rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega]
    have cfU : u.cf = some (decide (32 * n + lastLen < 65)) := by
      rw [step.cf, ← step.remaining, countU, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    cases n with
    | zero =>
      have flag : isa.eval .ae u = some false := by
        simp only [eval, cfU, show 32 * 0 + lastLen < 65 by omega, decide_true,
          Option.map_some, Bool.not_true]
      exact ⟨_, u, .loopExit run flag, (ChainResult.refl u).cons step (by omega) sep stackOut⟩
    | succ n =>
      have workU : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [base, step.wr]; exact work
      have outU : ∀ i < 32 * (n + 1), InRegions u.wr (u.gpr .r14 + BitVec.ofNat 64 i) 1 := by
        intro i hi
        rw [step.wr, step.output, BitVec.add_assoc,
          show (32 : Addr) = BitVec.ofNat 64 32 from rfl, ← BitVec.ofNat_add]
        exact out (32 + i) (by omega)
      have suffix : Region.Sub ⟨u.gpr .r14, 32 * (n + 1)⟩ ⟨s.gpr .r14, 32 * (n + 1 + 1)⟩ := by
        rw [step.output]
        exact Offset.sub_base _ (by omega : 32 + 32 * (n + 1) ≤ 32 * (n + 1 + 1))
      have sepU : (⟨u.gpr .rbx, 16384⟩ : Region).Disjoint ⟨u.gpr .r14, 32 * (n + 1)⟩ := by
        rw [base]; exact sep.sub_right suffix
      have swU : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
        rw [sp, base]; exact stackWork
      have soU : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .r14, 32 * (n + 1)⟩ := by
        rw [sp]; exact stackOut.sub_right suffix
      obtain ⟨trace', t, run', result⟩ := ih u (by omega) (by omega) countU workU outU sepU swU soU
      have flag : isa.eval .ae u = some true := by
        simp only [eval, cfU, show ¬ 32 * (n + 1) + lastLen < 65 by omega, decide_false,
          Option.map_some, Bool.not_false]
      exact ⟨_, t, .loopNext run flag run', result.cons step (by omega) sep stackOut⟩

end VG.Proof.Argon2.X86_64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Contract`. -/
section

/-! # H′: a local x86-64 contract -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64

def inputR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def outputR (s : State) : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
def workR (s : State) : Region := ⟨s.gpr .r8, 16384⟩
def retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩
def stackR (s : State) : Region := below (s.gpr .rsp) 16

def localContract : Contract isa where
  pre s := s.rd = [VG.Proof.Argon2.X86_64.HPrime.inputR s] ∧ s.wr = [VG.Proof.Argon2.X86_64.HPrime.outputR s, VG.Proof.Argon2.X86_64.HPrime.workR s] ∧
    (s.gpr .rsi).toNat < 2 ^ 32 ∧ 1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat < 2 ^ 32 ∧
    (VG.Proof.Argon2.X86_64.HPrime.inputR s).Disjoint (VG.Proof.Argon2.X86_64.HPrime.workR s) ∧ (VG.Proof.Argon2.X86_64.HPrime.outputR s).Disjoint (VG.Proof.Argon2.X86_64.HPrime.workR s) ∧
    (VG.Proof.Argon2.X86_64.HPrime.stackR s).Disjoint (VG.Proof.Argon2.X86_64.HPrime.inputR s) ∧ (VG.Proof.Argon2.X86_64.HPrime.stackR s).Disjoint (VG.Proof.Argon2.X86_64.HPrime.outputR s) ∧ (VG.Proof.Argon2.X86_64.HPrime.stackR s).Disjoint (VG.Proof.Argon2.X86_64.HPrime.workR s) ∧
    (VG.Proof.Argon2.X86_64.HPrime.retR s).Disjoint (VG.Proof.Argon2.X86_64.HPrime.outputR s) ∧ (VG.Proof.Argon2.X86_64.HPrime.retR s).Disjoint (VG.Proof.Argon2.X86_64.HPrime.workR s)
  post s t := Spec.Blake2.bytesAt t.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    Spec.Argon2.hPrime (s.gpr .rcx).toNat (Spec.Blake2.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s t := s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .rsp = t.gpr .rsp

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x4000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1⟩]
  wr := [⟨0x2000, 1⟩, ⟨0x4000, 16384⟩]

theorem contract_implies : localContract.Implies (Spec.Argon2.hPrimeContract X86_64.abi 16) := by
  sig_implies [Spec.Argon2.hPrimeContract, Spec.Argon2.hPrimeSig, VG.Proof.Argon2.X86_64.HPrime.localContract,
    VG.Proof.Argon2.X86_64.HPrime.inputR, VG.Proof.Argon2.X86_64.HPrime.outputR, VG.Proof.Argon2.X86_64.HPrime.workR, VG.Proof.Argon2.X86_64.HPrime.retR, VG.Proof.Argon2.X86_64.HPrime.stackR, below, X86_64.abi, X86_64.argRegs] [satState] using VG.Proof.Argon2.X86_64.HPrime.satState

end VG.Proof.Argon2.X86_64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Space`. -/
section

/-! Merged from `Proof.Argon2.X86_64.HPrime.Written`. -/
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

theorem Written.rbx {s t : State} {xs : List Byte} (h : VG.Proof.Argon2.X86_64.HPrime.Written s xs t) :
    t.gpr .rbx = s.gpr .rbx := h.regs _ (by decide) (by decide) (by decide)

theorem Written.rsp {s t : State} {xs : List Byte} (h : VG.Proof.Argon2.X86_64.HPrime.Written s xs t) :
    t.gpr .rsp = s.gpr .rsp := h.regs _ (by decide) (by decide) (by decide)

theorem Written.of_keeps {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.Keeps s t) : VG.Proof.Argon2.X86_64.HPrime.Written s [] t := by
  refine ⟨?_, fun r hr _ _ => h.regs r hr, h.rd, h.wr, ?_, rfl⟩
  · exact (h.regs .r14 (by decide)).trans (BitVec.add_zero _).symm
  · exact h.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩

theorem Written.before_keeps {s u t : State} {xs : List Byte} (h : VG.Proof.Argon2.X86_64.HPrime.Written u xs t)
    (k : VG.Proof.Argon2.X86_64.HPrime.Keeps s u) : VG.Proof.Argon2.X86_64.HPrime.Written s xs t := by
  have dst := k.regs .r14 (by decide)
  refine ⟨by rw [h.output, dst], fun r hr h1 h2 => (h.regs r hr h1 h2).trans (k.regs r hr),
    h.rd.trans k.rd, h.wr.trans k.wr, ?_, ?_⟩
  · have before : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16,
        ⟨s.gpr .r14, xs.length⟩] s.mem u.mem :=
      k.frame.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    exact before.trans (by simpa only [dst, k.rbx, k.rsp] using h.frame)
  · rw [← dst]; exact h.bytes

theorem Written.of_copied {s t : State} {k : Nat} (h : VG.Proof.Argon2.X86_64.HPrime.Copied s k t) (hk : k < 2 ^ 64) :
    VG.Proof.Argon2.X86_64.HPrime.Written s (bytesAt s.mem (s.gpr .rbx + 768) k) t := by
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
    exact VG.Proof.Argon2.X86_64.HPrime.bytesAt_writeBytes _ _ _ (by rw [len]; exact hk)

theorem Written.of_emitted {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.Emitted s t) :
    VG.Proof.Argon2.X86_64.HPrime.Written s (bytesAt s.mem (s.gpr .rbx + 768) 32) t := by
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
    exact VG.Proof.Argon2.X86_64.HPrime.bytesAt_writeBytes _ _ _ (by rw [len]; decide)

theorem Written.of_chain {s t : State} {n : Nat} (h : VG.Proof.Argon2.X86_64.HPrime.ChainResult s n t) :
    VG.Proof.Argon2.X86_64.HPrime.Written s (Proof.Argon2.chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)) t := by
  refine ⟨?_, h.regs, h.rd, h.wr, ?_, ?_⟩
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.output
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.frame
  · simpa only [Proof.Argon2.chainPrefixes_length] using h.bytes

theorem Written.trans {s u t : State} {xs ys : List Byte} (first : VG.Proof.Argon2.X86_64.HPrime.Written s xs u)
    (last : VG.Proof.Argon2.X86_64.HPrime.Written u ys t) (bound : xs.length + ys.length < 2 ^ 64)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, xs.length + ys.length⟩)
    (stack : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r14, xs.length + ys.length⟩) :
    VG.Proof.Argon2.X86_64.HPrime.Written s (xs ++ ys) t := by
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
  · exact (extend 0 xs.length (by omega) (by simpa only [BitVec.add_zero] using first.frame)).trans
      (extend xs.length ys.length (by omega) tf)
  · have before : bytesAt t.mem (s.gpr .r14) xs.length = bytesAt u.mem (s.gpr .r14) xs.length := by
      apply Proof.Blake2.bytesAt_congr
      intro i hi
      apply tf.bytes (R := ⟨s.gpr .r14, xs.length⟩) _ (show xs.length ≤ 2 ^ 64 by omega) hi
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (sep.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by omega))
      · exact stack.symm.sub_left (Region.sub_prefix (by omega))
      · exact Offset.base_disjoint _ (by omega) (by omega)
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
    (h : VG.Proof.Argon2.X86_64.HPrime.Space s n) (written : VG.Proof.Argon2.X86_64.HPrime.Written s xs t) (size : xs.length + k ≤ n) : VG.Proof.Argon2.X86_64.HPrime.Space t k := by
  have suffix : Region.Sub ⟨t.gpr .r14, k⟩ ⟨s.gpr .r14, n⟩ := by
    rw [written.output]; exact Offset.sub_base _ size
  refine ⟨by have := h.bound; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [written.wr, written.rbx]; exact h.work
  · intro i hi
    rw [written.wr, written.output, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.out (xs.length + i) (by omega)
  · rw [written.rbx]; exact h.sep.sub_right suffix
  · rw [written.rbx, written.rsp]; exact h.stackWork
  · rw [written.rsp]; exact h.stackOut.sub_right suffix

theorem Space.keeps {s t : State} {n : Nat} (h : VG.Proof.Argon2.X86_64.HPrime.Space s n) (k : VG.Proof.Argon2.X86_64.HPrime.Keeps s t) : VG.Proof.Argon2.X86_64.HPrime.Space t n :=
  h.advance (Written.of_keeps k) (by simp only [List.length_nil, Nat.zero_add, Nat.le_refl])

theorem Space.prefix {s : State} {n k : Nat} (h : VG.Proof.Argon2.X86_64.HPrime.Space s n) (hk : k ≤ n) : VG.Proof.Argon2.X86_64.HPrime.Space s k := by
  refine ⟨by have := h.bound; omega, h.work, fun i hi => h.out i (by omega),
    h.sep.sub_right (Region.sub_prefix hk), h.stackWork, h.stackOut.sub_right (Region.sub_prefix hk)⟩

theorem Space.join {s u t : State} {xs ys : List Byte} {n : Nat} (h : VG.Proof.Argon2.X86_64.HPrime.Space s n)
    (first : VG.Proof.Argon2.X86_64.HPrime.Written s xs u) (last : VG.Proof.Argon2.X86_64.HPrime.Written u ys t) (size : xs.length + ys.length ≤ n) :
    VG.Proof.Argon2.X86_64.HPrime.Written s (xs ++ ys) t :=
  first.trans last (by have := h.bound; omega)
    (h.sep.sub_right (Region.sub_prefix size)) (h.stackOut.sub_right (Region.sub_prefix size))

theorem copyRemaining_ok (s : State) (n : Nat) (space : VG.Proof.Argon2.X86_64.HPrime.Space s n)
    (lo : 1 ≤ n) (hi : n ≤ 64) (count : s.gpr .r15 = BitVec.ofNat 64 n) :
    WP isa copyRemaining s fun t => VG.Proof.Argon2.X86_64.HPrime.Written s (bytesAt s.mem (s.gpr .rbx + 768) n) t := by
  unfold copyRemaining
  refine WP.seq (wp_mov fun a ha _ _ => WP.block_nil ?_)
  have base := ha.other .rbx (by decide)
  have dst := ha.other .r14 (by decide)
  have workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact space.work
  have outA : ∀ i < n, InRegions a.wr (a.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact space.out
  have sepA : (⟨a.gpr .rbx + 768, n⟩ : Region).Disjoint ⟨a.gpr .r14, n⟩ := by
    rw [base, dst]; exact space.sep.sub_left (Offset.sub_base _ (by omega : 768 + n ≤ 16384))
  refine (VG.Proof.Argon2.X86_64.HPrime.copy_ok a n lo hi (ha.gpr.trans count) workA outA sepA).mono ?_
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

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Input`. -/
section

/-! # H′: arguments for the caller's input -/

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

theorem inputArgs_ok (s : State) : WP isa (.block inputArgs) s (VG.Proof.Argon2.X86_64.HPrime.InputArgs s) := by
  apply WP.of_runBlock
  simp only [inputArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, RegUpd.gpr_setReg, reduceCtorEq, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_setReg, h1, h2, h3, ite_false]

theorem InputArgs.keeps {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.InputArgs s t) : VG.Proof.Argon2.X86_64.HPrime.Keeps s t := by
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
      VG.Proof.Argon2.X86_64.HPrime.Keeps s t := by
  unfold absorbInput
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.inputArgs_ok s).mono fun u hu => ?_)
  have ku := hu.keeps
  have repr' : Repr b h0 u.mem (u.gpr .rbx) headBytes := by rw [hu.mem, ku.rbx]; exact repr
  have count : u.gpr .rsi = BitVec.ofNat 64 headBytes.length := by rw [prefixLen]; exact hu.count
  have bound : headBytes.length + (u.gpr .rcx).toNat < 2 ^ 64 := by rw [prefixLen, hu.size]; omega
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
  refine (VG.Proof.Argon2.X86_64.HPrime.update_ok v u h0 headBytes repr' count bound wr cover ds dw sw sd).mono ?_
  rintro t ⟨result, regs, rd, wr', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', VG.Proof.Argon2.X86_64.HPrime.update_frame _ _ frame⟩⟩
  simpa only [ku.rbx, hu.mem, hu.data, hu.size] using result

end VG.Proof.Argon2.X86_64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Length`. -/
section

/-! # H′: selecting the first digest length -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov wp_cmpi wp_mov32i)

theorem chooseLength_ok (s : State) :
    WP isa chooseLength s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 (min (s.gpr .r15).toNat 64) ∧ VG.Proof.Argon2.X86_64.HPrime.Keeps s t := by
  unfold chooseLength
  refine WP.seq (wp_mov fun a ha _ _ => wp_cmpi fun u gu mu ru wu cf _ => WP.block_nil ?_)
  have n : a.gpr .rsi = s.gpr .r15 := ha.gpr
  have ku : VG.Proof.Argon2.X86_64.HPrime.Keeps s u := by
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
      omega
    apply WP.block_nil
    refine ⟨?_, ku⟩
    rw [gu, n, Nat.min_eq_left hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro h
    have hn : 64 ≤ (s.gpr .r15).toNat := by
      have h' := of_decide_eq_false h
      omega
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

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Setup`. -/
section

/-! # H′: saving the caller and writing the length prefix -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

/-- Save the six caller registers and then the four-byte length prefix. -/
def setupMem (s : State) : Mem :=
  (saved.foldl (fun m rd => m.writeW (s.gpr .r8 + BitVec.ofNat 64 rd.2) (s.gpr rd.1)) s.mem).writeW
    (s.gpr .r8 + 832) ((s.gpr .rcx).setWidth 32)

theorem setupMem_frame (s : State) :
    Frame [⟨s.gpr .r8 + 832, 56⟩] s.mem (VG.Proof.Argon2.X86_64.HPrime.setupMem s) := by
  have store {m : Mem} (h : Frame [⟨s.gpr .r8 + 832, 56⟩] s.mem m)
      (d w : Nat) (v : BitVec w) (lo : 832 ≤ d) (hi : d + w / 8 ≤ 888) :
      Frame [⟨s.gpr .r8 + 832, 56⟩] s.mem (m.writeW (s.gpr .r8 + BitVec.ofNat 64 d) v) :=
    h.writeW (List.mem_singleton_self _) v (Offset.contains _ lo hi (by decide))
  unfold VG.Proof.Argon2.X86_64.HPrime.setupMem VG.Impl.Argon2.X86_64.HPrime.saved
  simp only [List.foldl_cons, List.foldl_nil]
  apply store (d := 832) (w := 32) _ _ (by decide) (by decide)
  apply store (d := 880) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 872) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 864) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 856) (w := 64) _ _ (by decide) (by decide)
  apply store (d := 848) (w := 64) _ _ (by decide) (by decide)
  exact store (Frame.refl _ _) 840 64 _ (by decide) (by decide)

theorem setupMem_prefix (s : State) :
    Spec.Blake2.bytesAt (VG.Proof.Argon2.X86_64.HPrime.setupMem s) (s.gpr .r8 + 832) 4 =
      Spec.Argon2.le32 (s.gpr .rcx).toNat := by
  rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (Or.inl rfl)]
  unfold VG.Proof.Argon2.X86_64.HPrime.setupMem
  rw [Mem.readW_writeW_self32]
  rfl

theorem setupMem_saved (s : State) (r : Reg) (d : Nat) (hr : (r, d) ∈ VG.Impl.Argon2.X86_64.HPrime.saved) :
    (VG.Proof.Argon2.X86_64.HPrime.setupMem s).readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 = s.gpr r := by
  have skip64 (m : Mem) (v : BitVec 64) (d e : Nat)
      (sep : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
      (m.writeW (s.gpr .r8 + BitVec.ofNat 64 e) v).readW
        (s.gpr .r8 + BitVec.ofNat 64 d) 64 = m.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 :=
    Mem.readW_writeW_sep (Offset.sep _ sep hd he) (by decide)
  have skip32 (m : Mem) (v : BitVec 32) (d : Nat) (lo : 836 ≤ d) (hi : d + 8 ≤ 2 ^ 64) :
      (m.writeW (s.gpr .r8 + 832) v).readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 =
        m.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 :=
    Mem.readW_writeW_sep (Offset.sep _ (Or.inr lo) hi (by decide)) (by decide)
  simp only [VG.Impl.Argon2.X86_64.HPrime.saved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
  rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp (disch := decide) only [VG.Proof.Argon2.X86_64.HPrime.setupMem, VG.Impl.Argon2.X86_64.HPrime.saved, List.foldl_cons, List.foldl_nil,
      skip32, skip64, Mem.readW_writeW_self64]

structure Setup (s t : State) : Prop where
  workspace : t.gpr .rbx = s.gpr .r8
  input : t.gpr .r12 = s.gpr .rdi
  length : t.gpr .r13 = s.gpr .rsi
  output : t.gpr .r14 = s.gpr .rdx
  remaining : t.gpr .r15 = s.gpr .rcx
  other : ∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  mem : t.mem = VG.Proof.Argon2.X86_64.HPrime.setupMem s
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem setup_ok (s : State) (hw : (⟨s.gpr .r8, 16384⟩ : Region) ∈ s.wr) :
    WP isa (.block VG.Impl.Argon2.X86_64.HPrime.setup) s (VG.Proof.Argon2.X86_64.HPrime.Setup s) := by
  have write (d n : Nat) (h : d + n ≤ 16384) :
      InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 d) n :=
    ⟨_, hw, Offset.contains_base _ h (by omega)⟩
  have w832 := write 832 4 (by decide)
  have w840 := write 840 8 (by decide)
  have w848 := write 848 8 (by decide)
  have w856 := write 856 8 (by decide)
  have w864 := write 864 8 (by decide)
  have w872 := write 872 8 (by decide)
  have w880 := write 880 8 (by decide)
  apply WP.of_runBlock
  simp only [VG.Impl.Argon2.X86_64.HPrime.setup, VG.Impl.Argon2.X86_64.HPrime.saved, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, State.store64, State.store32,
    VG.Proof.Argon2.X86_64.HPrime.ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    w832, w840, w848, w856, w864, w872, w880, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun r h1 h2 h3 h4 h5 => ?_, ?_, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg, h1, h2, h3, h4, h5, ite_false]
  · rfl

end VG.Proof.Argon2.X86_64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Correct`. -/
section

/-! Merged from `Proof.Argon2.X86_64.HPrime.Restore`. -/
section
/-! # H′: restoring the caller's registers -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem saved_read {m m' : Mem} (p sp : Addr)
    (frame : Frame [⟨p, 832⟩, below sp 16] m m')
    (stack : (below sp 16).Disjoint ⟨p, 16384⟩)
    (d : Nat) (lo : 832 ≤ d) (hi : d + 8 ≤ 16384) :
    m'.readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 := by
  apply frame.readW (r := ⟨p + BitVec.ofNat 64 d, 8⟩) ?_ ?_ (by decide)
  · simpa only [BitVec.add_zero] using
      Offset.contains_base (p + BitVec.ofNat 64 d) (d := 0) (n := 8) (k := 8) (by decide) (by decide)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (Offset.base_disjoint p lo (by omega)).symm
    · exact (stack.sub_right (Offset.sub_base p hi)).symm

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
    ⟨_, readable, Offset.contains_base _ h (by omega)⟩
  have r840 := read 840 (by decide)
  have r848 := read 848 (by decide)
  have r856 := read 856 (by decide)
  have r864 := read 864 (by decide)
  have r872 := read 872 (by decide)
  have r880 := read 880 (by decide)
  have v840 := values .rbp 840 (by decide)
  have v848 := values .r12 848 (by decide)
  have v856 := values .r13 856 (by decide)
  have v864 := values .r14 864 (by decide)
  have v872 := values .r15 872 (by decide)
  have v880 := values .rbx 880 (by decide)
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
      bytesAt t.mem (s.gpr .rbx + 768) 64 = Spec.Blake2.finalHash b h0 d ∧ VG.Proof.Argon2.X86_64.HPrime.Keeps s t := by
  unfold finishInput
  refine WP.seq (wp_mov fun a ha _ _ => wp_addi fun u hu => WP.block_nil ?_)
  have ku : VG.Proof.Argon2.X86_64.HPrime.Keeps s u := by
    refine ⟨fun r hr => ?_, hu.rd.trans ha.rd, hu.wr.trans ha.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hu.other r hn).trans (ha.other r hn)
    · rw [hu.mem, ha.mem]; exact Frame.refl _ _
  have repr' : Repr b h0 u.mem (u.gpr .rbx) d := by rw [hu.mem, ha.mem, ku.rbx]; exact repr
  have count : u.gpr .rsi = BitVec.ofNat 64 d.length := by
    rw [hu.gpr, ha.gpr, length, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_comm _ _
  have len : d.length < 2 ^ 64 := by rw [length]; omega
  have wr : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ku.rbx, ku.wr]; exact hwr
  have sw : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
    rw [ku.rbx, ku.rsp]; exact stackWork
  refine (VG.Proof.Argon2.X86_64.HPrime.finalize_ok v u h0 d repr' count len wr sw).mono ?_
  rintro t ⟨out, regs, rd, wr', frame⟩
  refine ⟨?_, ku.trans ⟨regs, rd, wr', VG.Proof.Argon2.X86_64.HPrime.finalize_frame _ _ frame⟩⟩
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
      VG.Proof.Argon2.X86_64.HPrime.Keeps s t := by
  unfold first
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.chooseLength_ok s).mono ?_)
  rintro a ⟨lengthA, ka⟩
  have na : (a.gpr .rsi).toNat = min (s.gpr .r15).toNat 64 := by
    rw [lengthA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have wrA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [ka.rbx, ka.wr]; exact hwr
  have swA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ka.rbx, ka.rsp]; exact stackWork
  have retA : (below (a.gpr .rsp) 8).Disjoint ⟨a.gpr .rbx, 192⟩ :=
    (swA.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))
  have lenA : 1 ≤ (a.gpr .rsi).toNat ∧ (a.gpr .rsi).toNat ≤ 64 := by rw [na]; omega
  refine WP.seq ((init_ok v a lenA wrA retA).mono ?_)
  rintro u ⟨reprU, regsU, rdU, wrU, frameU⟩
  have ku : VG.Proof.Argon2.X86_64.HPrime.Keeps a u := ⟨regsU, rdU, wrU, VG.Proof.Argon2.X86_64.HPrime.init_frame _ _ frameU⟩
  have ksu := ka.trans ku
  have reprU' : Repr b (Spec.Blake2.init b (min (s.gpr .r15).toNat 64) 0) u.mem (u.gpr .rbx) [] := by
    rw [ku.rbx]; simpa only [na] using reprU
  have wrU' : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ksu.rbx, ksu.wr]; exact hwr
  have swU : (below (u.gpr .rsp) 16).Disjoint ⟨u.gpr .rbx, 16384⟩ := by
    rw [ksu.rbx, ksu.rsp]; exact stackWork
  have headU : bytesAt u.mem (u.gpr .rbx + 832) 4 = Spec.Argon2.le32 (s.gpr .r15).toNat := by
    rw [ksu.rbx, ksu.prefix stackWork]; exact headBytes
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.absorbFixed_ok v u _ 832 4 (by decide) (by decide) reprU' wrU' swU).mono ?_)
  rintro w ⟨reprW, kw⟩
  have ksw := ksu.trans kw
  have r12 : w.gpr .r12 = s.gpr .r12 := ksw.regs _ (by decide)
  have r13 : w.gpr .r13 = s.gpr .r13 := ksw.regs _ (by decide)
  have headLen : (Spec.Argon2.le32 (s.gpr .r15).toNat).length = 4 := by
    simp only [Spec.Argon2.le32, Spec.Blake2.wordBytes, List.length_map, List.length_range]
  have reprW' : Repr b (Spec.Blake2.init b (min (s.gpr .r15).toNat 64) 0) w.mem (w.gpr .rbx)
      (Spec.Argon2.le32 (s.gpr .r15).toNat) := by
    rw [kw.rbx]
    simpa only [show BitVec.ofNat 64 832 = (832 : Addr) from rfl, headU] using reprW
  have wrW : (⟨w.gpr .rbx, 16384⟩ : Region) ∈ w.wr := by rw [ksw.rbx, ksw.wr]; exact hwr
  have dataW : Covers [⟨w.gpr .r12, (w.gpr .r13).toNat⟩] (w.rd ++ w.wr) := by
    rw [r12, r13, ksw.rd, ksw.wr]; exact hdata
  have dwW : (⟨w.gpr .r12, (w.gpr .r13).toNat⟩ : Region).Disjoint ⟨w.gpr .rbx, 16384⟩ := by
    rw [r12, r13, ksw.rbx]; exact dataWork
  have swW : (below (w.gpr .rsp) 16).Disjoint ⟨w.gpr .rbx, 16384⟩ := by
    rw [ksw.rsp, ksw.rbx]; exact stackWork
  have sdW : (below (w.gpr .rsp) 16).Disjoint ⟨w.gpr .r12, (w.gpr .r13).toNat⟩ := by
    rw [ksw.rsp, r12, r13]; exact stackData
  have inputW : bytesAt w.mem (w.gpr .r12) (w.gpr .r13).toNat =
      bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat := by
    rw [r12, r13]
    exact ksw.bytes _ (show (s.gpr .r13).toNat ≤ 2 ^ 64 by omega)
      (dataWork.sub_right (Region.sub_prefix (by decide))) stackData.symm
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.absorbInput_ok v w _ _ headLen reprW' (by rw [r13]; exact len)
    wrW dataW dwW swW sdW).mono ?_)
  rintro x ⟨reprX, kx⟩
  have ksx := ksw.trans kx
  have reprX' : Repr b (Spec.Blake2.init b (min (s.gpr .r15).toNat 64) 0) x.mem (x.gpr .rbx)
      (Spec.Argon2.le32 (s.gpr .r15).toNat ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat) := by
    rw [kx.rbx]; simpa only [inputW] using reprX
  have r13X : x.gpr .r13 = s.gpr .r13 := ksx.regs _ (by decide)
  have length : (Spec.Argon2.le32 (s.gpr .r15).toNat ++ bytesAt s.mem (s.gpr .r12) (s.gpr .r13).toNat).length =
      4 + (x.gpr .r13).toNat := by
    rw [List.length_append, headLen, r13X]
    simp only [bytesAt, List.length_map, List.length_range]
  have wrX : (⟨x.gpr .rbx, 16384⟩ : Region) ∈ x.wr := by rw [ksx.rbx, ksx.wr]; exact hwr
  have swX : (below (x.gpr .rsp) 16).Disjoint ⟨x.gpr .rbx, 16384⟩ := by
    rw [ksx.rsp, ksx.rbx]; exact stackWork
  refine (VG.Proof.Argon2.X86_64.HPrime.finishInput_ok v x _ _ reprX' length (by rw [r13X]; exact len) wrX swX).mono ?_
  rintro t ⟨out, kt⟩
  refine ⟨?_, ksx.trans kt⟩
  have result := congrArg (List.take (min (s.gpr .r15).toNat 64)) out
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
    (space : VG.Proof.Argon2.X86_64.HPrime.Space s (32 * n + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen))
    (cf : s.cf = some (decide (32 * n + lastLen < 65))) :
    WP isa (.ite .b (.block []) (chain (hash v))) s (VG.Proof.Argon2.X86_64.HPrime.ChainResult s n) := by
  refine WP.ite (decide (32 * n + lastLen < 65)) (by simp only [eval, cf]) ?_ ?_
  · intro h
    have hn : n = 0 := by have := of_decide_eq_true h; omega
    subst n
    exact WP.block_nil (ChainResult.refl s)
  · intro h
    have hn : 1 ≤ n := by have := of_decide_eq_false h; omega
    have p := space.prefix (show 32 * n ≤ 32 * n + lastLen by omega)
    exact VG.Proof.Argon2.X86_64.HPrime.chain_ok v n lastLen s hn last space.bound count p.work p.out p.sep p.stackWork p.stackOut

theorem extendDigest_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (space : VG.Proof.Argon2.X86_64.HPrime.Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (extendDigest (hash v)) s fun t =>
      VG.Proof.Argon2.X86_64.HPrime.Written s ((bytesAt s.mem (s.gpr .rbx + 768) 64).take 32 ++
        chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)) t ∧
      (bytesAt t.mem (s.gpr .rbx + 768) 64).take lastLen =
        Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64)) ∧
      t.gpr .r15 = BitVec.ofNat 64 lastLen := by
  unfold extendDigest
  have short := space.prefix (show 32 ≤ 32 * (n + 1) + lastLen by omega)
  have sep32 := short.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.emitPrefix_ok s short.work short.out sep32).mono ?_)
  intro a ha
  have wa := Written.of_emitted ha
  have lenA : (bytesAt s.mem (s.gpr .rbx + 768) 32).length = 32 := by
    simp only [bytesAt, List.length_map, List.length_range]
  have spaceA : VG.Proof.Argon2.X86_64.HPrime.Space a (32 * n + lastLen) := space.advance wa (by rw [lenA]; omega)
  have countA : a.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen) := by
    rw [ha.remaining, count, show (32 : Addr) = BitVec.ofNat 64 32 from rfl,
      Offset.ofNat_sub_ofNat (by omega : 32 ≤ 32 * (n + 1) + lastLen)]
    rw [show 32 * (n + 1) + lastLen - 32 = 32 * n + lastLen by omega]
  have digestA : bytesAt a.mem (a.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
    rw [wa.rbx]; exact ha.digest short.sep
  refine WP.seq (wp_cmpi fun u gu mu ru wu cf _ => WP.block_nil ?_)
  have ku : VG.Proof.Argon2.X86_64.HPrime.Keeps a u := ⟨fun r _ => congrFun gu r, ru, wu, by rw [mu]; exact Frame.refl _ _⟩
  have countU : u.gpr .r15 = BitVec.ofNat 64 (32 * n + lastLen) := (congrFun gu _).trans countA
  have cfU : u.cf = some (decide (32 * n + lastLen < 65)) := by
    rw [cf, countA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt spaceA.bound]; rfl
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.maybeChain_ok v n lastLen u (spaceA.keeps ku) last countU cfU).mono ?_)
  intro w hw
  have ww := (Written.of_chain hw).before_keeps ku
  have digestU : bytesAt u.mem (u.gpr .rbx + 768) 64 = bytesAt s.mem (s.gpr .rbx + 768) 64 := by
    rw [mu, gu]; exact digestA
  have ww' : VG.Proof.Argon2.X86_64.HPrime.Written a (chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)) w := by
    simpa only [digestU] using ww
  have wsw := space.join wa ww' (by rw [lenA, Proof.Argon2.chainPrefixes_length]; omega)
  have produced : ((bytesAt s.mem (s.gpr .rbx + 768) 32) ++
      chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)).length = 32 * (n + 1) := by
    rw [List.length_append, lenA, Proof.Argon2.chainPrefixes_length]; omega
  have spaceW : VG.Proof.Argon2.X86_64.HPrime.Space w lastLen := space.advance wsw (by rw [produced])
  have countW : w.gpr .r15 = BitVec.ofNat 64 lastLen := by
    rw [hw.remaining, countU, Offset.ofNat_sub_ofNat (by omega : 32 * n ≤ 32 * n + lastLen)]
    rw [Nat.add_sub_cancel_left]
  have digestW : bytesAt w.mem (w.gpr .rbx + 768) 64 =
      chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    rw [hw.regs .rbx (by decide) (by decide) (by decide), hw.digest, digestU]
  refine WP.seq (wp_mov fun x hx _ _ => WP.block_nil ?_)
  have kx : VG.Proof.Argon2.X86_64.HPrime.Keeps w x := by
    refine ⟨fun r hr => ?_, hx.rd, hx.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hx.other r hn
    · rw [hx.mem]; exact Frame.refl _ _
  have spaceX := spaceW.keeps kx
  have lenX : (x.gpr .rsi).toNat = lastLen := by
    rw [hx.gpr, countW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt spaceW.bound]
  refine (VG.Proof.Argon2.X86_64.HPrime.next_ok v x (by rw [lenX]; omega) spaceX.work spaceX.stackWork).mono ?_
  rintro t ⟨dt, kt⟩
  have wwt := Written.of_keeps (kx.trans kt)
  have written := space.join wsw wwt (by rw [produced, List.length_nil]; omega)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.append_nil, VG.Proof.Argon2.X86_64.HPrime.bytesAt_take _ _ 32 64 (by decide)] using written
  · rw [lenX, kx.rbx, hx.mem, digestW, wsw.rbx] at dt
    exact dt
  · rw [kt.regs _ (by decide), kx.regs _ (by decide)]; exact countW

theorem longOutput_ok (v : Proof.Blake2.X86_64.Backend) (n lastLen : Nat) (s : State)
    (space : VG.Proof.Argon2.X86_64.HPrime.Space s (32 * (n + 1) + lastLen)) (last : 33 ≤ lastLen ∧ lastLen ≤ 64)
    (count : s.gpr .r15 = BitVec.ofNat 64 (32 * (n + 1) + lastLen)) :
    WP isa (.seq (extendDigest (hash v)) copyRemaining) s fun t =>
      VG.Proof.Argon2.X86_64.HPrime.Written s (Spec.Argon2.longHash lastLen (n + 1) (bytesAt s.mem (s.gpr .rbx + 768) 64)) t := by
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.extendDigest_ok v n lastLen s space last count).mono ?_)
  rintro u ⟨written, digest, remaining⟩
  have len : ((bytesAt s.mem (s.gpr .rbx + 768) 64).take 32 ++
      chainPrefixes n (bytesAt s.mem (s.gpr .rbx + 768) 64)).length = 32 * (n + 1) := by
    simp only [List.length_append, List.length_take, bytesAt, List.length_map,
      List.length_range, Proof.Argon2.chainPrefixes_length]
    omega
  have spaceU : VG.Proof.Argon2.X86_64.HPrime.Space u lastLen := space.advance written (by rw [len])
  refine (VG.Proof.Argon2.X86_64.HPrime.copyRemaining_ok u lastLen spaceU (by omega) last.2 remaining).mono ?_
  intro t copied
  have out : bytesAt u.mem (u.gpr .rbx + 768) lastLen =
      Spec.Argon2.H lastLen (chainDigest n (bytesAt s.mem (s.gpr .rbx + 768) 64)) := by
    rw [written.rbx, ← VG.Proof.Argon2.X86_64.HPrime.bytesAt_take _ _ lastLen 64 last.2]; exact digest
  have all := space.join written copied (by
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
    (space : VG.Proof.Argon2.X86_64.HPrime.Space s n) (positive : 1 ≤ n) (count : s.gpr .r15 = BitVec.ofNat 64 n)
    (digest : (bytesAt s.mem (s.gpr .rbx + 768) 64).take (min n 64) =
      Spec.Argon2.H (min n 64) (Spec.Argon2.le32 n ++ input)) :
    WP isa (finishOutput (hash v)) s (VG.Proof.Argon2.X86_64.HPrime.Written s (Spec.Argon2.hPrime n input)) := by
  unfold finishOutput
  refine WP.seq (wp_cmpi fun u gu mu ru wu cf _ => WP.block_nil ?_)
  have ku : VG.Proof.Argon2.X86_64.HPrime.Keeps s u := ⟨fun r _ => congrFun gu r, ru, wu, by rw [mu]; exact Frame.refl _ _⟩
  have countU : u.gpr .r15 = BitVec.ofNat 64 n := (congrFun gu _).trans count
  have cfU : u.cf = some (decide (n < 65)) := by
    rw [cf, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt space.bound]; rfl
  apply WP.seq
  refine WP.ite (decide (n < 65)) (by simp only [eval, cfU]) ?_ ?_
  · intro h
    have short : n ≤ 64 := by have := of_decide_eq_true h; omega
    apply WP.block_nil
    refine (VG.Proof.Argon2.X86_64.HPrime.copyRemaining_ok u n (space.keeps ku) positive short countU).mono ?_
    intro t ht
    have result := ht.before_keeps ku
    have value : bytesAt u.mem (u.gpr .rbx + 768) n = Spec.Argon2.hPrime n input := by
      rw [mu, gu, ← VG.Proof.Argon2.X86_64.HPrime.bytesAt_take _ _ n 64 short]
      simpa only [Nat.min_eq_left short, Spec.Argon2.hPrime, ite_eq_left short] using digest
    rw [value] at result
    exact result
  · intro h
    have long : 64 < n := by have := of_decide_eq_false h; omega
    let r := (n + 31) / 32 - 2
    let lastLen := n - 32 * r
    have bounds : 1 ≤ r ∧ 33 ≤ lastLen ∧ lastLen ≤ 64 ∧ 32 * r + lastLen = n :=
      Proof.Argon2.longHash_bounds n long
    obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
    change r = q + 1 at hq
    have size : 32 * (q + 1) + lastLen = n := by rw [← hq]; exact bounds.2.2.2
    have spaceU : VG.Proof.Argon2.X86_64.HPrime.Space u (32 * (q + 1) + lastLen) := by rw [size]; exact space.keeps ku
    have countLong : u.gpr .r15 = BitVec.ofNat 64 (32 * (q + 1) + lastLen) := by rw [size]; exact countU
    apply WP.seq_iff.mp
    refine (VG.Proof.Argon2.X86_64.HPrime.longOutput_ok v q lastLen u spaceU ⟨bounds.2.1, bounds.2.2.1⟩ countLong).mono ?_
    intro t ht
    have result := ht.before_keeps ku
    have digestU : bytesAt u.mem (u.gpr .rbx + 768) 64 =
        Spec.Argon2.H 64 (Spec.Argon2.le32 n ++ input) := by
      rw [mu, gu]
      simpa only [Nat.min_eq_right (show 64 ≤ n by omega), VG.Proof.Argon2.X86_64.HPrime.bytesAt_take _ _ 64 64 (by decide)] using digest
    have value : Spec.Argon2.longHash lastLen (q + 1) (bytesAt u.mem (u.gpr .rbx + 768) 64) =
        Spec.Argon2.hPrime n input := by
      rw [digestU, ← hq, Spec.Argon2.hPrime, ite_eq_right (show ¬ n ≤ 64 by omega)]
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
      Frame [VG.Proof.Argon2.X86_64.HPrime.outputR s, VG.Proof.Argon2.X86_64.HPrime.workR s, VG.Proof.Argon2.X86_64.HPrime.stackR s] s.mem t.mem := by
  obtain ⟨rd, wr, len, lo, hi, dw, ow, sd, so, sw, _, _⟩ := pre
  have work : (VG.Proof.Argon2.X86_64.HPrime.workR s) ∈ s.wr := by rw [wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  unfold code
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.setup_ok s work).mono ?_)
  intro a ha
  have sp : a.gpr .rsp = s.gpr .rsp := ha.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by
    rw [ha.workspace, ha.wr]; exact work
  have dataA : Covers [⟨a.gpr .r12, (a.gpr .r13).toNat⟩] (a.rd ++ a.wr) := by
    rw [ha.input, ha.length, ha.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  have dwA : (⟨a.gpr .r12, (a.gpr .r13).toNat⟩ : Region).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ha.input, ha.length, ha.workspace]; exact dw
  have swA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [sp, ha.workspace]; exact sw
  have sdA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .r12, (a.gpr .r13).toNat⟩ := by
    rw [sp, ha.input, ha.length]; exact sd
  have inputA : bytesAt a.mem (a.gpr .r12) (a.gpr .r13).toNat =
      bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat := by
    rw [ha.input, ha.length, ha.mem]
    apply Proof.Blake2.bytesAt_congr
    intro i hi'
    apply (VG.Proof.Argon2.X86_64.HPrime.setupMem_frame s).bytes (R := VG.Proof.Argon2.X86_64.HPrime.inputR s) _ (show (s.gpr .rsi).toNat ≤ 2 ^ 64 by omega) hi'
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact dw.sub_right (Offset.sub_base _ (by decide : 832 + 56 ≤ 16384))
  have headA : bytesAt a.mem (a.gpr .rbx + 832) 4 = Spec.Argon2.le32 (a.gpr .r15).toNat := by
    rw [ha.mem, ha.workspace, ha.remaining]; exact VG.Proof.Argon2.X86_64.HPrime.setupMem_prefix s
  have spaceA : VG.Proof.Argon2.X86_64.HPrime.Space a (s.gpr .rcx).toNat := by
    refine ⟨by omega, workA, ?_, ?_, swA, ?_⟩
    · intro i hi'
      rw [ha.wr, ha.output, wr]
      exact ⟨VG.Proof.Argon2.X86_64.HPrime.outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
    · rw [ha.workspace, ha.output]; exact ow.symm
    · rw [sp, ha.output]; exact so
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.first_ok v a (by rw [ha.remaining]; exact ⟨lo, hi⟩)
    (by rw [ha.length]; exact len) headA workA dataA dwA swA sdA).mono ?_)
  rintro b ⟨digestB, kb⟩
  have spaceB := spaceA.keeps kb
  have countB : b.gpr .r15 = BitVec.ofNat 64 (s.gpr .rcx).toNat := by
    rw [kb.regs _ (by decide), ha.remaining, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have digestB' : (bytesAt b.mem (b.gpr .rbx + 768) 64).take (min (s.gpr .rcx).toNat 64) =
      Spec.Argon2.H (min (s.gpr .rcx).toNat 64)
        (Spec.Argon2.le32 (s.gpr .rcx).toNat ++ bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) := by
    rw [kb.rbx]
    simpa only [ha.remaining, inputA] using digestB
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.finishOutput_ok v b (s.gpr .rcx).toNat
    (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) spaceB lo countB digestB').mono ?_)
  intro x hx
  have baseB : b.gpr .rbx = s.gpr .r8 := kb.rbx.trans ha.workspace
  have spB : b.gpr .rsp = s.gpr .rsp := kb.rsp.trans sp
  have dstB : b.gpr .r14 = s.gpr .rdx := (kb.regs _ (by decide)).trans ha.output
  have wrX : x.wr = s.wr := hx.wr.trans (kb.wr.trans ha.wr)
  have frame : Frame [⟨s.gpr .r8, 832⟩, VG.Proof.Argon2.X86_64.HPrime.stackR s, VG.Proof.Argon2.X86_64.HPrime.outputR s] a.mem x.mem := by
    have fb : Frame [⟨s.gpr .r8, 832⟩, VG.Proof.Argon2.X86_64.HPrime.stackR s, VG.Proof.Argon2.X86_64.HPrime.outputR s] a.mem b.mem := by
      apply kb.frame.sub
      intro r hr
      rw [ha.workspace, sp] at hr
      exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    exact fb.trans (by simpa only [baseB, spB, dstB, VG.Proof.Argon2.X86_64.HPrime.stackR, VG.Proof.Argon2.X86_64.HPrime.outputR, Proof.Argon2.hPrime_length] using hx.frame)
  have values : ∀ r d, (r, d) ∈ saved →
      x.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 = s.gpr r := by
    intro r d hr
    have bounds : ∀ rd ∈ saved, 832 ≤ rd.2 ∧ rd.2 + 8 ≤ 16384 := by decide
    obtain ⟨dlo, dhi⟩ := bounds (r, d) hr
    have keep : x.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 =
        a.mem.readW (s.gpr .r8 + BitVec.ofNat 64 d) 64 := by
      apply frame.readW (r := ⟨s.gpr .r8 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact (Offset.base_disjoint _ dlo (by omega)).symm
      · exact (sw.sub_right (Offset.sub_base _ dhi)).symm
      · exact (ow.sub_right (Offset.sub_base _ dhi)).symm
    rw [keep, ha.mem]; exact VG.Proof.Argon2.X86_64.HPrime.setupMem_saved s r d hr
  have baseX := hx.rbx.trans baseB
  have spX := hx.rsp.trans spB
  have readable : VG.Proof.Argon2.X86_64.HPrime.workR s ∈ x.rd ++ x.wr := List.mem_append_right _ (wrX.symm ▸ work)
  refine (VG.Proof.Argon2.X86_64.HPrime.restore_ok s x baseX spX readable values).mono ?_
  rintro t ⟨regs, mem, _, _⟩
  refine ⟨?_, regs, ?_⟩
  · change bytesAt t.mem (s.gpr .rdx) (s.gpr .rcx).toNat = _
    rw [mem]
    simpa only [dstB, Proof.Argon2.hPrime_length] using hx.bytes
  · rw [mem]
    have setupFrame : Frame [VG.Proof.Argon2.X86_64.HPrime.outputR s, VG.Proof.Argon2.X86_64.HPrime.workR s, VG.Proof.Argon2.X86_64.HPrime.stackR s] s.mem a.mem := by
      rw [ha.mem]
      apply (VG.Proof.Argon2.X86_64.HPrime.setupMem_frame s).sub
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact ⟨VG.Proof.Argon2.X86_64.HPrime.workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        Offset.sub_base _ (by decide : 832 + 56 ≤ 16384)⟩
    apply setupFrame.trans
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Argon2.X86_64.HPrime.workR s, List.mem_cons_of_mem _ (List.mem_cons_self ..), Region.sub_prefix (by decide)⟩
    · exact ⟨VG.Proof.Argon2.X86_64.HPrime.stackR s, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), fun _ h => h⟩
    · exact ⟨VG.Proof.Argon2.X86_64.HPrime.outputR s, List.mem_cons_self .., fun _ h => h⟩

theorem code_mxcsr (v : Proof.Blake2.X86_64.Backend) :
    (code (hash v)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have init : (hash v).init.allInstrs (fun i => !loadsMxcsr i) = true := by
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
  obtain ⟨tr, t, run, post, regs, frame⟩ := VG.Proof.Argon2.X86_64.HPrime.code_wp v s pre
  refine ⟨tr, t, run, abiPreserved_of_exec (VG.Proof.Argon2.X86_64.HPrime.code_mxcsr v) run ⟨regs, ?_⟩, post⟩
  apply frame.readW (r := VG.Proof.Argon2.X86_64.HPrime.retR s) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  obtain ⟨_, _, _, _, _, _, _, _, _, _, retOut, retWork⟩ := pre
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact retOut
  · exact retWork
  · exact Offset.base_disjoint_below _ (by decide)

end VG.Proof.Argon2.X86_64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.FixedCT`. -/
section

/-! Merged from `Proof.Argon2.X86_64.HPrime.UpdateCT`. -/
section
/-! # H′: constant time of a BLAKE2b update -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure UpdateReady (s : State) : Prop where
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  data : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] (s.rd ++ s.wr)
  dataState : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 192⟩
  dataScratch : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx + 192, 576⟩
  stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩

theorem update_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : VG.Proof.Argon2.X86_64.HPrime.UpdateReady s) :
    WP isa (update (hash v)) s (VG.Proof.Argon2.X86_64.HPrime.Keeps s) := by
  unfold update
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.updateArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := VG.Proof.Argon2.X86_64.HPrime.update_call_hyps s u hu h.work h.data
    h.dataState h.dataScratch h.stackWork h.stackData
  refine WP.call (k := Proof.Blake2.updateX86_64 Spec.Blake2.b) v.update_correct (hash_ok v).updateNoSp
    (by change 8 * (hash v).update.depth + 16 < 2 ^ 64; rw [(hash_ok v).updateDepth]; decide)
    pre cover writes ?_
  intro t rd wr regs frame _ _
  refine ⟨fun r hr => ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .r8 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr).trans (hu.other r hn.1 hn.2)
  · apply VG.Proof.Argon2.X86_64.HPrime.update_frame
    change Frame (_ ++ [below (u.gpr .rsp) (8 * ((hash v).update.depth + 1))]) u.mem t.mem at frame
    simpa only [(hash_ok v).updateDepth, hu.other .rsp (by decide) (by decide), hu.mem,
      List.cons_append, List.nil_append] using frame

theorem update_rel (v : Proof.Blake2.X86_64.Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Argon2.X86_64.HPrime.UpdateReady s₁ ∧ VG.Proof.Argon2.X86_64.HPrime.UpdateReady s₂ ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (update (hash v)) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block updateArgs) (by taint_decide)).wpDep
    (F := VG.Proof.Argon2.X86_64.HPrime.UpdateArgs) fun s₁ s₂ _ => ⟨VG.Proof.Argon2.X86_64.HPrime.updateArgs_ok s₁, VG.Proof.Argon2.X86_64.HPrime.updateArgs_ok s₂⟩
  have call := RelCT.callEx (n := (hash v).updateName) (k := Proof.Blake2.updateX86_64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ VG.Proof.Argon2.X86_64.HPrime.UpdateArgs σ₁ s₁ ∧ VG.Proof.Argon2.X86_64.HPrime.UpdateArgs σ₂ s₂)
    v.update_correct v.updateCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, data, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := VG.Proof.Argon2.X86_64.HPrime.update_call_hyps σ₁ s₁ h₁ p₁.work p₁.data
        p₁.dataState p₁.dataScratch p₁.stackWork p₁.stackData
      obtain ⟨pre₂, cover₂, writes₂⟩ := VG.Proof.Argon2.X86_64.HPrime.update_call_hyps σ₂ s₂ h₂ p₂.work p₂.data
        p₂.dataState p₂.dataScratch p₂.stackWork p₂.stackData
      have sp' : s₁.gpr .rsp = s₂.gpr .rsp := by
        rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), sp]
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂, sp'⟩
      simp only [Proof.Blake2.updateX86_64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_rsp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), count],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), data],
        by rw [h₁.other _ (by decide) (by decide), h₂.other _ (by decide) (by decide), len],
        by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.RelatedCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.HPrime.InitCT`. -/
section
/-! # H′: constant time of BLAKE2b initialization -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure InitReady (s : State) : Prop where
  length : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.gpr .rsp) 8).Disjoint ⟨s.gpr .rbx, 192⟩

theorem init_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : VG.Proof.Argon2.X86_64.HPrime.InitReady s) :
    WP isa (init (hash v)) s (VG.Proof.Argon2.X86_64.HPrime.Keeps s) :=
  (init_ok v s h.length h.work h.stack).mono fun _ ⟨_, regs, rd, wr, frame⟩ =>
    ⟨regs, rd, wr, VG.Proof.Argon2.X86_64.HPrime.init_frame _ _ frame⟩

theorem init_rel (v : Proof.Blake2.X86_64.Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Argon2.X86_64.HPrime.InitReady s₁ ∧ VG.Proof.Argon2.X86_64.HPrime.InitReady s₂ ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (init (hash v)) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block initArgs) (by taint_decide)).wpDep
    (F := InitArgs) fun s₁ s₂ _ => ⟨initArgs_ok s₁, initArgs_ok s₂⟩
  have call := RelCT.callEx (n := (hash v).initName) (k := Proof.Blake2.initX86_64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ InitArgs σ₁ s₁ ∧ InitArgs σ₂ s₂)
    Proof.Blake2.X86_64.Stream.initB_correct Proof.Blake2.X86_64.Stream.initB_ct
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, len, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := init_call_hyps σ₁ s₁ h₁ p₁.length p₁.work p₁.stack
      obtain ⟨pre₂, cover₂, writes₂⟩ := init_call_hyps σ₂ s₂ h₂ p₂.length p₂.work p₂.stack
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂, ?_⟩
      · simp only [Proof.Blake2.initX86_64, State.withRegions_gpr,
          State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp)]
        exact ⟨by rw [h₁.state, h₂.state, base],
          by rw [h₁.other _ (by decide) (by decide) (by decide),
            h₂.other _ (by decide) (by decide) (by decide), len],
          by rw [h₁.key, h₂.key, base], by rw [h₁.keylen, h₂.keylen]⟩
      · rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), sp]
  exact args.seq call

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.FinalizeCT`. -/
section
/-! # H′: constant time of BLAKE2b finalization -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure FinalizeReady (s : State) : Prop where
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  stack : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩

theorem FinalizeReady.keeps {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.FinalizeReady s) (k : VG.Proof.Argon2.X86_64.HPrime.Keeps s t) : VG.Proof.Argon2.X86_64.HPrime.FinalizeReady t := by
  constructor
  · rw [k.wr, k.rbx]; exact h.work
  · rw [k.rsp, k.rbx]; exact h.stack

theorem finalize_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : VG.Proof.Argon2.X86_64.HPrime.FinalizeReady s) :
    WP isa (finalize (hash v)) s (VG.Proof.Argon2.X86_64.HPrime.Keeps s) := by
  unfold finalize
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.finalizeArgs_ok s).mono fun u hu => ?_)
  obtain ⟨pre, cover, writes⟩ := VG.Proof.Argon2.X86_64.HPrime.finalize_call_hyps s u hu h.work h.stack
  refine WP.call (k := Proof.Blake2.finalizeX86_64 Spec.Blake2.b) v.finalize_correct (hash_ok v).finalizeNoSp
    (by change 8 * (hash v).finalize.depth + 16 < 2 ^ 64; rw [(hash_ok v).finalizeDepth]; decide)
    pre cover writes ?_
  intro t rd wr regs frame _ _
  refine ⟨fun r hr => ?_, rd.trans hu.rd, wr.trans hu.wr, ?_⟩
  · have hn : r ≠ .rdi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (regs r hr).trans (hu.other r hn.1 hn.2.1 hn.2.2)
  · apply VG.Proof.Argon2.X86_64.HPrime.finalize_frame
    change Frame (_ ++ [below (u.gpr .rsp) (8 * ((hash v).finalize.depth + 1))]) u.mem t.mem at frame
    simpa only [(hash_ok v).finalizeDepth, hu.other .rsp (by decide) (by decide) (by decide), hu.mem,
      List.cons_append, List.nil_append] using frame

theorem finalize_rel (v : Proof.Blake2.X86_64.Backend) {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Argon2.X86_64.HPrime.FinalizeReady s₁ ∧ VG.Proof.Argon2.X86_64.HPrime.FinalizeReady s₂ ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P (finalize (hash v)) fun _ _ => True := by
  have args := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block finalizeArgs) (by taint_decide)).wpDep
    (F := VG.Proof.Argon2.X86_64.HPrime.FinalizeArgs) fun s₁ s₂ _ => ⟨VG.Proof.Argon2.X86_64.HPrime.finalizeArgs_ok s₁, VG.Proof.Argon2.X86_64.HPrime.finalizeArgs_ok s₂⟩
  have call := RelCT.callEx (n := (hash v).finalizeName) (k := Proof.Blake2.finalizeX86_64 Spec.Blake2.b)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ VG.Proof.Argon2.X86_64.HPrime.FinalizeArgs σ₁ s₁ ∧ VG.Proof.Argon2.X86_64.HPrime.FinalizeArgs σ₂ s₂)
    v.finalize_correct v.finalizeCT
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨p₁, p₂, base, count, sp⟩ := hP _ _ hp
      obtain ⟨pre₁, cover₁, writes₁⟩ := VG.Proof.Argon2.X86_64.HPrime.finalize_call_hyps σ₁ s₁ h₁ p₁.work p₁.stack
      obtain ⟨pre₂, cover₂, writes₂⟩ := VG.Proof.Argon2.X86_64.HPrime.finalize_call_hyps σ₂ s₂ h₂ p₂.work p₂.stack
      have sp' : s₁.gpr .rsp = s₂.gpr .rsp := by
        rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), sp]
      refine ⟨_, _, _, _, pre₁, pre₂, ?_, cover₁, writes₁, cover₂, writes₂, sp'⟩
      simp only [Proof.Blake2.finalizeX86_64, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_rsp]
      exact ⟨by rw [h₁.state, h₂.state, base],
        by rw [h₁.other _ (by decide) (by decide) (by decide),
          h₂.other _ (by decide) (by decide) (by decide), count],
        by rw [h₁.digest, h₂.digest, base], by rw [h₁.scratch, h₂.scratch, base], by rw [sp']⟩
  exact args.seq call

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.BlocksCT`. -/
section
/-! # H′: constant time of argument handling and output loops -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

def publicRegs : List Reg := [.rbx, .r12, .r13, .r14, .r15, .rsp]

def AgreeRegs (rs : List Reg) (s t : State) : Prop := ∀ r ∈ rs, s.gpr r = t.gpr r

theorem publicRegs_callee : ∀ r ∈ VG.Proof.Argon2.X86_64.HPrime.publicRegs, r ∈ calleeSaved := by decide

theorem setup_rel :
    RelCT isa (VG.Proof.Argon2.X86_64.HPrime.AgreeRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) (.block setup)
      (VG.Proof.Argon2.X86_64.HPrime.AgreeRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
    (fun _ _ hp => Taint.agree_ofRegs hp) VG.Proof.Argon2.X86_64.HPrime.publicRegs (by taint_decide)

theorem chooseLength_rel : RelCT isa (VG.Proof.Argon2.X86_64.HPrime.AgreeRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs) chooseLength
    (VG.Proof.Argon2.X86_64.HPrime.AgreeRegs (.rsi :: VG.Proof.Argon2.X86_64.HPrime.publicRegs)) :=
  RelCT.taintRegs (τ := Taint.ofRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs)
    (fun _ _ hp => Taint.agree_ofRegs hp) (.rsi :: VG.Proof.Argon2.X86_64.HPrime.publicRegs) (by taint_decide)

theorem copy_rel : RelCT isa (VG.Proof.Argon2.X86_64.HPrime.AgreeRegs (.rax :: VG.Proof.Argon2.X86_64.HPrime.publicRegs)) copy (VG.Proof.Argon2.X86_64.HPrime.AgreeRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs (.rax :: VG.Proof.Argon2.X86_64.HPrime.publicRegs))
    (fun _ _ hp => Taint.agree_ofRegs hp) VG.Proof.Argon2.X86_64.HPrime.publicRegs (by taint_decide)

theorem emitPrefix_rel : RelCT isa (VG.Proof.Argon2.X86_64.HPrime.AgreeRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs) emitPrefix (VG.Proof.Argon2.X86_64.HPrime.AgreeRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs)
    (fun _ _ hp => Taint.agree_ofRegs hp) VG.Proof.Argon2.X86_64.HPrime.publicRegs (by taint_decide)

theorem copyRemaining_rel : RelCT isa (VG.Proof.Argon2.X86_64.HPrime.AgreeRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs) copyRemaining (VG.Proof.Argon2.X86_64.HPrime.AgreeRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs) :=
  RelCT.taintRegs (τ := Taint.ofRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs)
    (fun _ _ hp => Taint.agree_ofRegs hp) VG.Proof.Argon2.X86_64.HPrime.publicRegs (by taint_decide)

theorem restore_rel : RelCT isa (VG.Proof.Argon2.X86_64.HPrime.AgreeRegs [.rbx]) (.block restore) fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbx]) (fun _ _ hp => Taint.agree_ofRegs hp)
    (by taint_decide)

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: retaining public caller state across hash calls -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

/-- Caller conditions that survive hashing in the workspace. -/
structure Stable (F : State → Prop) : Prop where
  ready : ∀ s, F s → VG.Proof.Argon2.X86_64.HPrime.FinalizeReady s
  keeps : ∀ s t, F s → VG.Proof.Argon2.X86_64.HPrime.Keeps s t → F t

def Related (F : State → Prop) (s t : State) : Prop := F s ∧ F t ∧ VG.Proof.Argon2.X86_64.HPrime.AgreeRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs s t

theorem Related.keeps {F : State → Prop} (stable : VG.Proof.Argon2.X86_64.HPrime.Stable F) {s₁ s₂ t₁ t₂ : State}
    (h : VG.Proof.Argon2.X86_64.HPrime.Related F s₁ s₂) (k₁ : VG.Proof.Argon2.X86_64.HPrime.Keeps s₁ t₁) (k₂ : VG.Proof.Argon2.X86_64.HPrime.Keeps s₂ t₂) : VG.Proof.Argon2.X86_64.HPrime.Related F t₁ t₂ := by
  refine ⟨stable.keeps _ _ h.1 k₁, stable.keeps _ _ h.2.1 k₂, fun r hr => ?_⟩
  rw [k₁.regs _ (VG.Proof.Argon2.X86_64.HPrime.publicRegs_callee r hr), k₂.regs _ (VG.Proof.Argon2.X86_64.HPrime.publicRegs_callee r hr)]
  exact h.2.2 r hr

theorem keeps_rel {F : State → Prop} (stable : VG.Proof.Argon2.X86_64.HPrime.Stable F) {P : State → State → Prop} {c : Prog isa}
    (ct : RelCT isa P c fun _ _ => True)
    (wp : ∀ s₁ s₂, P s₁ s₂ → WP isa c s₁ (VG.Proof.Argon2.X86_64.HPrime.Keeps s₁) ∧ WP isa c s₂ (VG.Proof.Argon2.X86_64.HPrime.Keeps s₂))
    (pre : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.Argon2.X86_64.HPrime.Related F s₁ s₂) : RelCT isa P c (VG.Proof.Argon2.X86_64.HPrime.Related F) :=
  (ct.wpDep wp).mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    (pre _ _ hp).keeps stable k₁ k₂

theorem stable_init_rel (v : Proof.Blake2.X86_64.Backend) {F : State → Prop} (stable : VG.Proof.Argon2.X86_64.HPrime.Stable F) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi)
      (init (hash v)) (VG.Proof.Argon2.X86_64.HPrime.Related F) := by
  have ready (s : State) (hs : F s) (len : 1 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64) :
      VG.Proof.Argon2.X86_64.HPrime.InitReady s := by
    have h := stable.ready s hs
    exact ⟨len, h.work, (h.stack.sub_left (below_sub (by decide) (by decide))).sub_right
      (Region.sub_prefix (by decide))⟩
  apply VG.Proof.Argon2.X86_64.HPrime.keeps_rel stable (VG.Proof.Argon2.X86_64.HPrime.init_rel v ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨ready s₁ h.1 len, ready s₂ h.2.1 (by rw [← eq]; exact len),
      h.2.2 _ (by decide), eq, h.2.2 _ (by decide)⟩
  · intro s₁ s₂ ⟨h, len, eq⟩
    exact ⟨VG.Proof.Argon2.X86_64.HPrime.init_keeps v s₁ (ready s₁ h.1 len),
      VG.Proof.Argon2.X86_64.HPrime.init_keeps v s₂ (ready s₂ h.2.1 (by rw [← eq]; exact len))⟩

theorem stable_finalize_rel (v : Proof.Blake2.X86_64.Backend) {F : State → Prop} (stable : VG.Proof.Argon2.X86_64.HPrime.Stable F) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related F s₁ s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi)
      (finalize (hash v)) (VG.Proof.Argon2.X86_64.HPrime.Related F) := by
  apply VG.Proof.Argon2.X86_64.HPrime.keeps_rel stable (VG.Proof.Argon2.X86_64.HPrime.finalize_rel v ?_) ?_ (fun _ _ h => h.1)
  · intro s₁ s₂ ⟨h, count⟩
    exact ⟨stable.ready _ h.1, stable.ready _ h.2.1,
      h.2.2 _ (by decide), count, h.2.2 _ (by decide)⟩
  · intro s₁ s₂ ⟨h, _⟩
    exact ⟨VG.Proof.Argon2.X86_64.HPrime.finalize_keeps v s₁ (stable.ready _ h.1), VG.Proof.Argon2.X86_64.HPrime.finalize_keeps v s₂ (stable.ready _ h.2.1)⟩

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: constant time of hashing a fixed workspace buffer -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem FixedArgs.keeps {s t : State} {offset size : Nat} (h : VG.Proof.Argon2.X86_64.HPrime.FixedArgs s t offset size) : VG.Proof.Argon2.X86_64.HPrime.Keeps s t := by
  refine ⟨fun r hr => ?_, h.rd, h.wr, ?_⟩
  · have hn : r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact h.other r hn.1 hn.2.1 hn.2.2
  · rw [h.mem]; exact Frame.refl _ _

theorem fixed_ready {s t : State} {offset size : Nat} (ready : VG.Proof.Argon2.X86_64.HPrime.FinalizeReady s)
    (h : VG.Proof.Argon2.X86_64.HPrime.FixedArgs s t offset size) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    VG.Proof.Argon2.X86_64.HPrime.UpdateReady t := by
  have k := h.keeps
  have len : (t.gpr .rcx).toNat = size := by
    rw [h.size, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨(ready.keeps k).work, ?_, ?_, ?_, (ready.keeps k).stack, ?_⟩
  · apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨⟨s.gpr .rbx, 16384⟩, List.mem_append_right _ (k.wr.symm ▸ ready.work), offset, h.data, ?_⟩
    change offset + (t.gpr .rcx).toNat ≤ 16384
    rw [len]; exact hi
  · rw [h.data, len, k.rbx]
    exact (Offset.base_disjoint _ (by omega) (by omega)).symm
  · rw [h.data, len, k.rbx]
    exact Offset.disjoint _ (d := offset) (n := size) (e := 192) (k := 576) (by omega) (by omega) (by decide)
  · rw [k.rsp, h.data, len]
    exact ready.stack.sub_right (Offset.sub_base _ hi)

theorem absorbFixed_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (offset size : Nat)
    (ready : VG.Proof.Argon2.X86_64.HPrime.FinalizeReady s) (lo : 768 ≤ offset) (hi : offset + size ≤ 16384) :
    WP isa (absorbFixed (hash v) offset size) s (VG.Proof.Argon2.X86_64.HPrime.Keeps s) := by
  unfold absorbFixed
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.fixedArgs_ok s offset size (by omega) (by omega)).mono fun u hu => ?_)
  exact (VG.Proof.Argon2.X86_64.HPrime.update_keeps v u (VG.Proof.Argon2.X86_64.HPrime.fixed_ready ready hu lo hi)).mono fun _ h => hu.keeps.trans h

theorem absorbFixed_rel (v : Proof.Blake2.X86_64.Backend) (offset size : Nat)
    (lo : 768 ≤ offset) (hi : offset + size ≤ 16384)
    (ct : ∃ hint, (taint.check (Taint.ofRegs []) (.block (fixedArgs offset size)) hint).isSome = true)
    {F : State → Prop} (stable : VG.Proof.Argon2.X86_64.HPrime.Stable F) :
    RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related F) (absorbFixed (hash v) offset size) (VG.Proof.Argon2.X86_64.HPrime.Related F) := by
  obtain ⟨_, ct⟩ := ct
  have args := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.X86_64.HPrime.Related F) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block (fixedArgs offset size))
    ct).wpDep (F := fun s t => VG.Proof.Argon2.X86_64.HPrime.FixedArgs s t offset size)
    fun s₁ s₂ _ => ⟨VG.Proof.Argon2.X86_64.HPrime.fixedArgs_ok s₁ offset size (by omega) (by omega),
      VG.Proof.Argon2.X86_64.HPrime.fixedArgs_ok s₂ offset size (by omega) (by omega)⟩
  have call := VG.Proof.Argon2.X86_64.HPrime.update_rel v (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, VG.Proof.Argon2.X86_64.HPrime.Related F σ₁ σ₂ ∧ VG.Proof.Argon2.X86_64.HPrime.FixedArgs σ₁ s₁ offset size ∧ VG.Proof.Argon2.X86_64.HPrime.FixedArgs σ₂ s₂ offset size)
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      have base := hp.2.2 .rbx (by decide)
      have sp := hp.2.2 .rsp (by decide)
      exact ⟨VG.Proof.Argon2.X86_64.HPrime.fixed_ready (stable.ready _ hp.1) h₁ lo hi, VG.Proof.Argon2.X86_64.HPrime.fixed_ready (stable.ready _ hp.2.1) h₂ lo hi,
        by rw [h₁.keeps.rbx, h₂.keeps.rbx, base], by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data, base], by rw [h₁.size, h₂.size], by rw [h₁.keeps.rsp, h₂.keeps.rsp, sp]⟩
  exact VG.Proof.Argon2.X86_64.HPrime.keeps_rel stable (args.seq call)
    (fun s₁ s₂ hp => ⟨VG.Proof.Argon2.X86_64.HPrime.absorbFixed_keeps v s₁ offset size (stable.ready _ hp.1) lo hi,
      VG.Proof.Argon2.X86_64.HPrime.absorbFixed_keeps v s₂ offset size (stable.ready _ hp.2.1) lo hi⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.HPrime

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified`. -/
section

/-! Merged from `Proof.Argon2.X86_64.HPrime.OutputCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.HPrime.NextCT`. -/
section
/-! # H′: constant time of hashing the previous digest -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov32i)

theorem count64_ok (s : State) : WP isa (.block [.mov32 .rsi (.imm 64)]) s fun t =>
    VG.Proof.Argon2.X86_64.HPrime.Keeps s t ∧ t.gpr .rsi = 64 := by
  refine wp_mov32i fun t ht _ _ => WP.block_nil ⟨?_, ht.gpr⟩
  refine ⟨fun r hr => ?_, ht.rd, ht.wr, ?_⟩
  · have hn : r ≠ .rsi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ht.other r hn
  · rw [ht.mem]; exact Frame.refl _ _

theorem count64_rel {F : State → Prop} (stable : VG.Proof.Argon2.X86_64.HPrime.Stable F) :
    RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related F) (.block [.mov32 .rsi (.imm 64)])
      (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related F s₁ s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.X86_64.HPrime.Related F) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block [.mov32 .rsi (.imm 64)])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨VG.Proof.Argon2.X86_64.HPrime.count64_ok s₁, VG.Proof.Argon2.X86_64.HPrime.count64_ok s₂⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, k₁, k₂⟩ =>
    ⟨hp.keeps stable k₁.1 k₂.1, k₁.2.trans k₂.2.symm⟩

theorem next_rel (v : Proof.Blake2.X86_64.Backend) {F : State → Prop} (stable : VG.Proof.Argon2.X86_64.HPrime.Stable F) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related F s₁ s₂ ∧
      (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi)
      (next (hash v)) (VG.Proof.Argon2.X86_64.HPrime.Related F) :=
  (VG.Proof.Argon2.X86_64.HPrime.stable_init_rel v stable).seq
    ((VG.Proof.Argon2.X86_64.HPrime.absorbFixed_rel v 768 64 (by decide) (by decide) ⟨_, by taint_decide⟩ stable).seq
      ((VG.Proof.Argon2.X86_64.HPrime.count64_rel stable).seq (VG.Proof.Argon2.X86_64.HPrime.stable_finalize_rel v stable)))

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.InputCT`. -/
section
/-! # H′: public input bounds and constant-time absorption -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

structure OutputReady (s : State) : Prop where
  space : VG.Proof.Argon2.X86_64.HPrime.Space s (s.gpr .r15).toNat
  positive : 1 ≤ (s.gpr .r15).toNat
  bound : (s.gpr .r15).toNat < 2 ^ 32

theorem output_stable : VG.Proof.Argon2.X86_64.HPrime.Stable VG.Proof.Argon2.X86_64.HPrime.OutputReady where
  ready _ h := ⟨h.space.work, h.space.stackWork⟩
  keeps s t h k := by
    have n := k.regs .r15 (by decide)
    refine ⟨?_, ?_, ?_⟩
    · rw [n]; exact h.space.keeps k
    · rw [n]; exact h.positive
    · rw [n]; exact h.bound

structure FirstReady (s : State) : Prop extends VG.Proof.Argon2.X86_64.HPrime.OutputReady s where
  length : (s.gpr .r13).toNat < 2 ^ 32
  data : Covers [⟨s.gpr .r12, (s.gpr .r13).toNat⟩] (s.rd ++ s.wr)
  dataWork : (⟨s.gpr .r12, (s.gpr .r13).toNat⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackData : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .r12, (s.gpr .r13).toNat⟩

theorem first_stable : VG.Proof.Argon2.X86_64.HPrime.Stable VG.Proof.Argon2.X86_64.HPrime.FirstReady where
  ready _ h := output_stable.ready _ h.toOutputReady
  keeps s t h k := by
    have ptr := k.regs .r12 (by decide)
    have len := k.regs .r13 (by decide)
    refine ⟨output_stable.keeps s t h.toOutputReady k, ?_, ?_, ?_, ?_⟩
    · rw [len]; exact h.length
    · rw [ptr, len, k.rd, k.wr]; exact h.data
    · rw [ptr, len, k.rbx]; exact h.dataWork
    · rw [ptr, len, k.rsp]; exact h.stackData

theorem input_ready {s t : State} (ready : VG.Proof.Argon2.X86_64.HPrime.FirstReady s) (h : VG.Proof.Argon2.X86_64.HPrime.InputArgs s t) : VG.Proof.Argon2.X86_64.HPrime.UpdateReady t := by
  have k := h.keeps
  refine ⟨(first_stable.ready _ (first_stable.keeps _ _ ready k)).work, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.data, h.size, h.rd, h.wr]; exact ready.data
  · rw [h.data, h.size, k.rbx]; exact ready.dataWork.sub_right (Region.sub_prefix (by decide))
  · rw [h.data, h.size, k.rbx]; exact ready.dataWork.sub_right (Offset.sub_base _ (by decide))
  · rw [k.rbx, k.rsp]; exact ready.space.stackWork
  · rw [h.data, h.size, k.rsp]; exact ready.stackData

theorem absorbInput_keeps (v : Proof.Blake2.X86_64.Backend) (s : State) (h : VG.Proof.Argon2.X86_64.HPrime.FirstReady s) :
    WP isa (absorbInput (hash v)) s (VG.Proof.Argon2.X86_64.HPrime.Keeps s) := by
  unfold absorbInput
  refine WP.seq ((VG.Proof.Argon2.X86_64.HPrime.inputArgs_ok s).mono fun u hu => ?_)
  exact (VG.Proof.Argon2.X86_64.HPrime.update_keeps v u (VG.Proof.Argon2.X86_64.HPrime.input_ready h hu)).mono fun _ ht => hu.keeps.trans ht

theorem absorbInput_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady) (absorbInput (hash v)) (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady) := by
  have args := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block inputArgs) (by taint_decide)).wpDep
    (F := VG.Proof.Argon2.X86_64.HPrime.InputArgs) fun s₁ s₂ _ => ⟨VG.Proof.Argon2.X86_64.HPrime.inputArgs_ok s₁, VG.Proof.Argon2.X86_64.HPrime.inputArgs_ok s₂⟩
  have call := VG.Proof.Argon2.X86_64.HPrime.update_rel v (P := fun s₁ s₂ => True ∧
      ∃ σ₁ σ₂, VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady σ₁ σ₂ ∧ VG.Proof.Argon2.X86_64.HPrime.InputArgs σ₁ s₁ ∧ VG.Proof.Argon2.X86_64.HPrime.InputArgs σ₂ s₂)
    fun _ _ ⟨_, _, _, hp, h₁, h₂⟩ => by
      exact ⟨VG.Proof.Argon2.X86_64.HPrime.input_ready hp.1 h₁, VG.Proof.Argon2.X86_64.HPrime.input_ready hp.2.1 h₂,
        by rw [h₁.keeps.rbx, h₂.keeps.rbx]; exact hp.2.2 _ (by decide),
        by rw [h₁.count, h₂.count],
        by rw [h₁.data, h₂.data]; exact hp.2.2 _ (by decide),
        by rw [h₁.size, h₂.size]; exact hp.2.2 _ (by decide),
        by rw [h₁.keeps.rsp, h₂.keeps.rsp]; exact hp.2.2 _ (by decide)⟩
  exact VG.Proof.Argon2.X86_64.HPrime.keeps_rel VG.Proof.Argon2.X86_64.HPrime.first_stable (args.seq call)
    (fun s₁ s₂ hp => ⟨VG.Proof.Argon2.X86_64.HPrime.absorbInput_keeps v s₁ hp.1, VG.Proof.Argon2.X86_64.HPrime.absorbInput_keeps v s₂ hp.2.1⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.FirstCT`. -/
section
/-! # H′: constant time of the initial length-prefixed hash -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov wp_addi)

theorem chooseFirst_rel : RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady) chooseLength
    (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady s₁ s₂ ∧
      (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  have ct := (chooseLength_rel.mono (P' := VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady)
    (fun _ _ hp => hp.2.2) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ _ => ⟨VG.Proof.Argon2.X86_64.HPrime.chooseLength_ok s₁, VG.Proof.Argon2.X86_64.HPrime.chooseLength_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨pub, s₁, s₂, hp, ⟨len₁, k₁⟩, ⟨_, k₂⟩⟩
  refine ⟨hp.keeps VG.Proof.Argon2.X86_64.HPrime.first_stable k₁ k₂, ?_, pub _ (List.mem_cons_self ..)⟩
  rw [len₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : min (s₁.gpr .r15).toNat 64 < 2 ^ 64)]
  have := hp.1.positive
  omega

theorem inputCount_ok (s : State) :
    WP isa (.block [.mov .rsi (.reg .r13), .alu .add .rsi (.imm 4)]) s fun t =>
      VG.Proof.Argon2.X86_64.HPrime.Keeps s t ∧ t.gpr .rsi = s.gpr .r13 + 4 := by
  refine wp_mov fun a ha _ _ => wp_addi fun t ht => WP.block_nil ⟨?_, ?_⟩
  · refine ⟨fun r hr => ?_, ht.rd.trans ha.rd, ht.wr.trans ha.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (ht.other r hn).trans (ha.other r hn)
    · rw [ht.mem, ha.mem]; exact Frame.refl _ _
  · rw [ht.gpr, ha.gpr]; rfl

theorem inputCount_rel :
    RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady) (.block [.mov .rsi (.reg .r13), .alu .add .rsi (.imm 4)])
      (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady s₁ s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov .rsi (.reg .r13), .alu .add .rsi (.imm 4)]) (by taint_decide)).wpDep
    (fun s₁ s₂ _ => ⟨VG.Proof.Argon2.X86_64.HPrime.inputCount_ok s₁, VG.Proof.Argon2.X86_64.HPrime.inputCount_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, hp, ⟨k₁, c₁⟩, ⟨k₂, c₂⟩⟩
  refine ⟨hp.keeps VG.Proof.Argon2.X86_64.HPrime.first_stable k₁ k₂, ?_⟩
  rw [c₁, c₂, hp.2.2 .r13 (by decide)]

theorem first_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady) (first (hash v)) (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady) :=
  chooseFirst_rel.seq ((VG.Proof.Argon2.X86_64.HPrime.stable_init_rel v VG.Proof.Argon2.X86_64.HPrime.first_stable).seq
    ((VG.Proof.Argon2.X86_64.HPrime.absorbFixed_rel v 832 4 (by decide) (by decide) ⟨_, by taint_decide⟩ VG.Proof.Argon2.X86_64.HPrime.first_stable).seq
    ((VG.Proof.Argon2.X86_64.HPrime.absorbInput_rel v).seq (inputCount_rel.seq (VG.Proof.Argon2.X86_64.HPrime.stable_finalize_rel v VG.Proof.Argon2.X86_64.HPrime.first_stable)))))

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: public output counters and prefix emission -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_cmpi)

def LoopReady (s : State) : Prop := VG.Proof.Argon2.X86_64.HPrime.OutputReady s ∧ 65 ≤ (s.gpr .r15).toNat

theorem loop_stable : VG.Proof.Argon2.X86_64.HPrime.Stable VG.Proof.Argon2.X86_64.HPrime.LoopReady where
  ready _ h := output_stable.ready _ h.1
  keeps s t h k := ⟨output_stable.keeps s t h.1 k,
    by rw [k.regs .r15 (by decide)]; exact h.2⟩

theorem sub32_nat (v : BitVec 64) (h : 32 ≤ v.toNat) : (v - 32).toNat = v.toNat - 32 := by
  have eq : v - 32 = BitVec.ofNat 64 (v.toNat - 32) := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq,
      show BitVec.ofNat 64 32 = (32 : Addr) from rfl] using (Offset.ofNat_sub_ofNat (w := 64) h)
  rw [eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.isLt; omega)]

theorem Emitted.ready {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.Emitted s t) (pre : VG.Proof.Argon2.X86_64.HPrime.LoopReady s) : VG.Proof.Argon2.X86_64.HPrime.OutputReady t := by
  have count : (t.gpr .r15).toNat = (s.gpr .r15).toNat - 32 := by
    rw [h.remaining, VG.Proof.Argon2.X86_64.HPrime.sub32_nat _ (by have := pre.2; omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [count]
    apply pre.1.space.advance (Written.of_emitted h)
    simp only [Spec.Blake2.bytesAt, List.length_map, List.length_range]
    have := pre.2
    omega
  · rw [count]; have := pre.2; omega
  · rw [count]; have := pre.1.bound; omega

theorem emit_ready (v : State) (h : VG.Proof.Argon2.X86_64.HPrime.LoopReady v) : WP isa emitPrefix v (VG.Proof.Argon2.X86_64.HPrime.Emitted v) := by
  have space := h.1.space.prefix (show 32 ≤ (v.gpr .r15).toNat by have := h.2; omega)
  exact VG.Proof.Argon2.X86_64.HPrime.emitPrefix_ok v space.work space.out
    (space.sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384)))

theorem emit_rel : RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.LoopReady) emitPrefix (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady) := by
  have ct := (emitPrefix_rel.mono (P' := VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.LoopReady)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨VG.Proof.Argon2.X86_64.HPrime.emit_ready s₁ hp.1, VG.Proof.Argon2.X86_64.HPrime.emit_ready s₂ hp.2.1⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨pub, _, _, hp, h₁, h₂⟩ =>
    ⟨h₁.ready hp.1, h₂.ready hp.2.1, pub⟩

theorem count64_init_rel {F : State → Prop} (stable : VG.Proof.Argon2.X86_64.HPrime.Stable F) :
    RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related F) (.block [.mov32 .rsi (.imm 64)])
      (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related F s₁ s₂ ∧
        (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  have ct := (VG.Proof.Argon2.X86_64.HPrime.count64_rel stable).wpDep (fun s₁ s₂ _ => ⟨VG.Proof.Argon2.X86_64.HPrime.count64_ok s₁, VG.Proof.Argon2.X86_64.HPrime.count64_ok s₂⟩)
  exact ct.mono (fun _ _ h => h) fun _ _ ⟨⟨hp, eq⟩, _, _, _, ⟨_, len⟩, _⟩ =>
    ⟨hp, by rw [len]; decide, eq⟩

theorem compare_ok (s : State) : WP isa (.block [.alu .cmp .r15 (.imm 65)]) s fun t =>
    VG.Proof.Argon2.X86_64.HPrime.Keeps s t ∧ t.cf = some (decide ((s.gpr .r15).toNat < 65)) := by
  refine wp_cmpi fun t gt mt rt wt cf _ => WP.block_nil ⟨?_, cf⟩
  exact ⟨fun r _ => congrFun gt r, rt, wt, by rw [mt]; exact Frame.refl _ _⟩

theorem compare_rel {F : State → Prop} (stable : VG.Proof.Argon2.X86_64.HPrime.Stable F) :
    RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related F) (.block [.alu .cmp .r15 (.imm 65)])
      (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related F s₁ s₂ ∧ s₁.cf = s₂.cf ∧
        s₁.cf = some (decide ((s₁.gpr .r15).toNat < 65))) := by
  have ct := (RelCT.taint (A := taint) (P := VG.Proof.Argon2.X86_64.HPrime.Related F) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block [.alu .cmp .r15 (.imm 65)])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨VG.Proof.Argon2.X86_64.HPrime.compare_ok s₁, VG.Proof.Argon2.X86_64.HPrime.compare_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, hp, ⟨k₁, cf₁⟩, ⟨k₂, cf₂⟩⟩
  refine ⟨hp.keeps stable k₁ k₂, ?_, ?_⟩
  · rw [cf₁, cf₂, hp.2.2 .r15 (by decide)]
  · rw [k₁.regs .r15 (by decide)]; exact cf₁

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.FinishCT`. -/
section
/-! Merged from `Proof.Argon2.X86_64.HPrime.ChainCT`. -/
section
/-! # H′: constant time of the long-output loop -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem chainBody_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.LoopReady)
      (.seq (.block [.mov32 .rsi (.imm 64)])
        (.seq (next (hash v)) (.seq emitPrefix (.block [.alu .cmp .r15 (.imm 65)]))))
      (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady s₁ s₂ ∧ s₁.cf = s₂.cf ∧
        s₁.cf = some (decide ((s₁.gpr .r15).toNat < 65))) :=
  (VG.Proof.Argon2.X86_64.HPrime.count64_init_rel VG.Proof.Argon2.X86_64.HPrime.loop_stable).seq ((VG.Proof.Argon2.X86_64.HPrime.next_rel v VG.Proof.Argon2.X86_64.HPrime.loop_stable).seq
    (emit_rel.seq (VG.Proof.Argon2.X86_64.HPrime.compare_rel VG.Proof.Argon2.X86_64.HPrime.output_stable)))

theorem chainStep_ready (v : Proof.Blake2.X86_64.Backend) (s : State) (h : VG.Proof.Argon2.X86_64.HPrime.LoopReady s) :
    WP isa (.seq (.block [.mov32 .rsi (.imm 64)])
      (.seq (next (hash v)) (.seq emitPrefix (.block [.alu .cmp .r15 (.imm 65)])))) s (VG.Proof.Argon2.X86_64.HPrime.ChainStep s) := by
  have space := h.1.space.prefix (show 32 ≤ (s.gpr .r15).toNat by have := h.2; omega)
  exact VG.Proof.Argon2.X86_64.HPrime.chainStep_ok v s space.work space.out space.sep space.stackWork

theorem chain_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.LoopReady) (chain (hash v))
      (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64) := by
  let I := fun n s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.LoopReady s₁ s₂ ∧ (s₁.gpr .r15).toNat = n
  have step (n : Nat) := ((VG.Proof.Argon2.X86_64.HPrime.chainBody_rel v).mono (P' := I n)
    (fun _ _ h => h.1) (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨VG.Proof.Argon2.X86_64.HPrime.chainStep_ready v s₁ hp.1.1, VG.Proof.Argon2.X86_64.HPrime.chainStep_ready v s₂ hp.1.2.1⟩)
  have loops (n : Nat) : RelCT isa (I n) (chain (hash v))
      (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64) := by
    unfold chain
    apply RelCT.loop (M := isa) I ?_ n
    intro m
    apply (step m).mono (fun _ _ h => h)
    rintro t₁ t₂ ⟨⟨ready, cf, value⟩, s₁, s₂, hp, h₁, _⟩
    refine ⟨by simp only [eval, cf], ?_, ?_⟩
    · intro flag
      refine ⟨ready, ?_⟩
      by_contra h
      have hn : ¬ (t₁.gpr .r15).toNat < 65 := by omega
      simp only [eval, value, hn, decide_false, Option.map_some, Bool.not_false] at flag
      contradiction
    intro flag
    have lo : 65 ≤ (t₁.gpr .r15).toNat := by
      by_contra h
      have lt : (t₁.gpr .r15).toNat < 65 := by omega
      simp only [eval, value, lt, decide_true, Option.map_some, Bool.not_true] at flag
      contradiction
    have remain : (t₁.gpr .r15).toNat = (s₁.gpr .r15).toNat - 32 := by
      rw [h₁.remaining, VG.Proof.Argon2.X86_64.HPrime.sub32_nat _ (by have := hp.1.1.2; omega)]
    refine ⟨(t₁.gpr .r15).toNat, ?_, ⟨⟨ready.1, lo⟩, ⟨ready.2.1, ?_⟩, ready.2.2⟩, rfl⟩
    · have before : 65 ≤ (s₁.gpr .r15).toNat := hp.1.1.2
      have count : (s₁.gpr .r15).toNat = m := hp.2
      omega
    · rw [← ready.2.2 .r15 (by decide)]; exact lo
  exact (RelCT.exists_ loops).mono (fun s₁ _ h => ⟨(s₁.gpr .r15).toNat, h, rfl⟩) (fun _ _ h => h)

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # H′: constant time of the final hash and output -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov)

def Compared (s t : State) : Prop := VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady s t ∧ s.cf = t.cf ∧
  s.cf = some (decide ((s.gpr .r15).toNat < 65))

theorem Compared.short {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.Compared s t) (flag : isa.eval .b s = some true) :
    (s.gpr .r15).toNat ≤ 64 := by
  by_contra hn
  have n : ¬ (s.gpr .r15).toNat < 65 := by omega
  simp only [eval, h.2.2, n, decide_false] at flag
  contradiction

theorem Compared.long {s t : State} (h : VG.Proof.Argon2.X86_64.HPrime.Compared s t) (flag : isa.eval .b s = some false) :
    VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.LoopReady s t := by
  have n : 65 ≤ (s.gpr .r15).toNat := by
    by_contra hn
    have n : (s.gpr .r15).toNat < 65 := by omega
    simp only [eval, h.2.2, n, decide_true] at flag
    contradiction
  exact ⟨⟨h.1.1, n⟩, ⟨h.1.2.1, by rw [← h.1.2.2 .r15 (by decide)]; exact n⟩, h.1.2.2⟩

theorem maybeChain_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa VG.Proof.Argon2.X86_64.HPrime.Compared (.ite .b (.block []) (chain (hash v)))
      (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64) :=
  RelCT.ite (fun _ _ h => by simp only [eval, h.2.1])
    (RelCT.block_nil fun _ _ ⟨h, flag⟩ => ⟨h.1, h.short flag⟩)
    ((VG.Proof.Argon2.X86_64.HPrime.chain_rel v).mono (fun _ _ ⟨h, flag⟩ => h.long flag) (fun _ _ h => h))

theorem lastCount_ok (s : State) : WP isa (.block [.mov .rsi (.reg .r15)]) s fun t =>
    VG.Proof.Argon2.X86_64.HPrime.Keeps s t ∧ t.gpr .rsi = s.gpr .r15 := by
  refine wp_mov fun t ht _ _ => WP.block_nil ⟨?_, ht.gpr⟩
  refine ⟨fun r hr => ?_, ht.rd, ht.wr, ?_⟩
  · have hn : r ≠ .rsi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact ht.other r hn
  · rw [ht.mem]; exact Frame.refl _ _

theorem lastCount_rel :
    RelCT isa (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64)
      (.block [.mov .rsi (.reg .r15)])
      (fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady s₁ s₂ ∧
        (1 ≤ (s₁.gpr .rsi).toNat ∧ (s₁.gpr .rsi).toNat ≤ 64) ∧ s₁.gpr .rsi = s₂.gpr .rsi) := by
  let P := fun s₁ s₂ => VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady s₁ s₂ ∧ (s₁.gpr .r15).toNat ≤ 64
  have ct := (RelCT.taint (A := taint) (P := P) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block [.mov .rsi (.reg .r15)])
    (by taint_decide)).wpDep (fun s₁ s₂ _ => ⟨VG.Proof.Argon2.X86_64.HPrime.lastCount_ok s₁, VG.Proof.Argon2.X86_64.HPrime.lastCount_ok s₂⟩)
  apply ct.mono (fun _ _ h => h)
  rintro t₁ t₂ ⟨_, s₁, s₂, ⟨hp, bound⟩, ⟨k₁, n₁⟩, ⟨k₂, n₂⟩⟩
  exact ⟨hp.keeps VG.Proof.Argon2.X86_64.HPrime.output_stable k₁ k₂, by rw [n₁]; exact ⟨hp.1.positive, bound⟩,
    by rw [n₁, n₂]; exact hp.2.2 _ (by decide)⟩

theorem extendDigest_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.LoopReady) (extendDigest (hash v)) (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady) :=
  emit_rel.seq ((VG.Proof.Argon2.X86_64.HPrime.compare_rel VG.Proof.Argon2.X86_64.HPrime.output_stable).seq
    ((VG.Proof.Argon2.X86_64.HPrime.maybeChain_rel v).seq (lastCount_rel.seq (VG.Proof.Argon2.X86_64.HPrime.next_rel v VG.Proof.Argon2.X86_64.HPrime.output_stable))))

theorem finishOutput_rel (v : Proof.Blake2.X86_64.Backend) :
    RelCT isa (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady) (finishOutput (hash v)) (VG.Proof.Argon2.X86_64.HPrime.AgreeRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs) := by
  have branches : RelCT isa VG.Proof.Argon2.X86_64.HPrime.Compared (.ite .b (.block []) (extendDigest (hash v))) (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady) :=
    RelCT.ite (fun _ _ h => by simp only [eval, h.2.1])
      (RelCT.block_nil fun _ _ h => h.1.1)
      ((VG.Proof.Argon2.X86_64.HPrime.extendDigest_rel v).mono (fun _ _ ⟨h, flag⟩ => h.long flag) (fun _ _ h => h))
  exact (VG.Proof.Argon2.X86_64.HPrime.compare_rel VG.Proof.Argon2.X86_64.HPrime.output_stable).seq (branches.seq
    (copyRemaining_rel.mono (fun _ _ h => h.2.2) (fun _ _ h => h)))

end VG.Proof.Argon2.X86_64.HPrime
end

/-! Merged from `Proof.Argon2.X86_64.HPrime.CT`. -/
section
/-! # H′: constant time of the complete x86-64 program -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem setup_work (s : State) (h : localContract.pre s) :
    (⟨s.gpr .r8, 16384⟩ : Region) ∈ s.wr := by
  rw [h.2.1]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem setup_ready {s t : State} (h : localContract.pre s) (ht : VG.Proof.Argon2.X86_64.HPrime.Setup s t) : VG.Proof.Argon2.X86_64.HPrime.FirstReady t := by
  obtain ⟨rd, wr, len, lo, hi, dw, ow, sd, so, sw, _, _⟩ := h
  have sp : t.gpr .rsp = s.gpr .rsp := ht.other _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have space : VG.Proof.Argon2.X86_64.HPrime.Space t (s.gpr .rcx).toNat := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ht.workspace, ht.wr, wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · intro i hi'
      rw [ht.wr, ht.output, wr]
      exact ⟨VG.Proof.Argon2.X86_64.HPrime.outputR s, List.mem_cons_self .., Offset.contains_base _ (by omega) (by omega)⟩
    · rw [ht.workspace, ht.output]; exact ow.symm
    · rw [sp, ht.workspace]; exact sw
    · rw [sp, ht.output]; exact so
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [ht.remaining]; exact space
  · rw [ht.remaining]; exact lo
  · rw [ht.remaining]; exact hi
  · rw [ht.length]; exact len
  · rw [ht.input, ht.length, ht.rd, rd]
    intro p n ⟨r, hr, hc⟩
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · rw [ht.input, ht.length, ht.workspace]; exact dw
  · rw [sp, ht.input, ht.length]; exact sd

theorem code_ct (v : Proof.Blake2.X86_64.Backend) :
    ConstantTime isa localContract.pre localContract.pub (code (hash v)) := by
  let P := fun s₁ s₂ => localContract.pre s₁ ∧ localContract.pre s₂ ∧ localContract.pub s₁ s₂
  have setupCT := (setup_rel.mono (P' := P) (fun s₁ s₂ hp => by
      obtain ⟨di, si, dx, cx, r8, sp⟩ := hp.2.2
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption)
    (fun _ _ h => h)).wpDep
    (fun s₁ s₂ hp => ⟨VG.Proof.Argon2.X86_64.HPrime.setup_ok s₁ (VG.Proof.Argon2.X86_64.HPrime.setup_work s₁ hp.1), VG.Proof.Argon2.X86_64.HPrime.setup_ok s₂ (VG.Proof.Argon2.X86_64.HPrime.setup_work s₂ hp.2.1)⟩)
  have start : RelCT isa P (.block setup) (VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.FirstReady) :=
    setupCT.mono (fun _ _ h => h) fun _ _ ⟨pub, _, _, hp, h₁, h₂⟩ =>
      ⟨VG.Proof.Argon2.X86_64.HPrime.setup_ready hp.1 h₁, VG.Proof.Argon2.X86_64.HPrime.setup_ready hp.2.1 h₂, pub⟩
  have firstCT := (VG.Proof.Argon2.X86_64.HPrime.first_rel v).mono (fun _ _ h => h)
    (fun _ _ h => (show VG.Proof.Argon2.X86_64.HPrime.Related VG.Proof.Argon2.X86_64.HPrime.OutputReady _ _ from ⟨h.1.toOutputReady, h.2.1.toOutputReady, h.2.2⟩))
  have restoreCT := restore_rel.mono (P' := VG.Proof.Argon2.X86_64.HPrime.AgreeRegs VG.Proof.Argon2.X86_64.HPrime.publicRegs) (fun _ _ hp => by
      intro r hr
      simp only [List.mem_singleton] at hr; subst r
      exact hp _ (by decide)) (fun _ _ h => h)
  exact (start.seq (firstCT.seq ((VG.Proof.Argon2.X86_64.HPrime.finishOutput_rel v).seq restoreCT))).constantTime

end VG.Proof.Argon2.X86_64.HPrime
end

/-! # Verified H′ for any x86-64 BLAKE2b backend -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem verified (v : Proof.Blake2.X86_64.Backend) :
    Verified X86_64.target (code (hash v)) (Spec.Argon2.hPrimeContract X86_64.abi 16) :=
  Verified.of_correct (VG.Proof.Argon2.X86_64.HPrime.code_correct v) (VG.Proof.Argon2.X86_64.HPrime.code_ct v) VG.Proof.Argon2.X86_64.HPrime.contract_implies

theorem spSafe (v : Proof.Blake2.X86_64.Backend) : (code (hash v)).all (fun i => !isa.writesSp i) = true := by
  have init : (hash v).init.all (fun i => !isa.writesSp i) = true := by
    apply Code.all_of_allInstrs
    change (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).allInstrs _ = true
    lit_decide
  have update : (hash v).update.all (fun i => !isa.writesSp i) = true := v.updateSpSafe
  have finalize : (hash v).finalize.all (fun i => !isa.writesSp i) = true := v.finalizeSpSafe
  simp only [code, setup, saved, first, chooseLength, Impl.Argon2.X86_64.HPrime.init,
    initArgs, absorbFixed, fixedArgs, Impl.Argon2.X86_64.HPrime.update, updateArgs,
    absorbInput, inputArgs, finishInput, Impl.Argon2.X86_64.HPrime.finalize, finalizeArgs,
    finishOutput, extendDigest, emitPrefix, copy, copyByte, chain, next, copyRemaining,
    restore, Code.all]
  rw [init, update, finalize]
  decide +kernel

end VG.Proof.Argon2.X86_64.HPrime

end

end
