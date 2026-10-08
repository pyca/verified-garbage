import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.CmacAes.X86.Save
import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
import VerifiedGarbage.Impl.AesCbc.X86

/-!
# AES-CBC on x86: the contracts, and a call of a block function

The artifacts' contracts are the shared ones of `Spec/Cbc/Contract.lean`,
which imply these (`Verified.lean`): `cbcX86 enc`, for encryption
(`enc = true`) and decryption, `modeX86` for CBC (`cbcMode`). The arguments
are on the stack, from `[esp + 4]` (cdecl). Each call of a block function
pushes its five arguments and the return address in the 24 bytes below
`esp`, which may not overlap any buffer.

`blk_call`: the frame that pushes the five arguments of an implementation of
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` (`f` being
`Spec.Aes.cipher` or `Spec.Aes.invCipher`) around its call (`eax` the
schedule, `ecx` the rounds, `ebx` the block `D`, `edi = 1` and `ebp` the
working space `S`): `D` then holds `f` of it, and only `D`, `S` and the 24
bytes below `esp` change in memory. `blk_rel`: such calls are constant time,
by the block function's own proof.
-/

namespace VG.Proof.AesCbc.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cbc_encrypt` (`enc`) or `vg_aes_cbc_decrypt` `(schedule, rounds, iv, data, n, scratch)`. -/
def modeX86 (M : Mode) : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 24, 24⟩
    s.rd = [sched, args] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧ iv.Disjoint scr ∧
      data.Disjoint scr ∧ args.Disjoint iv ∧ args.Disjoint data ∧ args.Disjoint scr ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    let w := bytesAt s.mem ((arg s 0).setWidth 64) (16 * ((arg s 1).toNat + 1))
    let iv := bytesAt s.mem ((arg s 2).setWidth 64) 16
    let xs := Spec.Cbc.blocksAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat
    Spec.Cbc.blocksAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat = M.out (arg s 1).toNat w iv xs ∧
      bytesAt s'.mem ((arg s 2).setWidth 64) 16 = M.chain (arg s 1).toNat w iv xs
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- `vg_aes_cbc_encrypt` (`enc`) or `vg_aes_cbc_decrypt`. -/
abbrev cbcX86 (enc : Bool) : Contract isa := modeX86 (cbcMode enc)

/-! ## A call of a block function -/

/-- The registers the call pushes, as the block function's arguments. -/
abbrev blkRegs : List Reg := [.ebp, .edi, .ebx, .ecx, .eax]

theorem hrs : Reg.esp ∉ blkRegs := by decide

/-- What a call of a block function on one block needs. -/
structure BlkPre (s : State) (W D S : BitVec 32) (R : Nat) : Prop where
  eax : s.gpr .eax = W
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  ebx : s.gpr .ebx = D
  edi : s.gpr .edi = 1
  ebp : s.gpr .ebp = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  esp : 24 ≤ (s.gpr .esp).toNat
  wd : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨D.setWidth 64, 16⟩
  ws : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨S.setWidth 64, 2048⟩
  ds : (⟨D.setWidth 64, 16⟩ : Region).Disjoint ⟨S.setWidth 64, 2048⟩
  bw : (below (s.gpr .esp) 24).Disjoint ⟨W.setWidth 64, 240⟩
  bd : (below (s.gpr .esp) 24).Disjoint ⟨D.setWidth 64, 16⟩
  bs : (below (s.gpr .esp) 24).Disjoint ⟨S.setWidth 64, 2048⟩
  hW : W.toNat + 240 ≤ 2 ^ 32
  hD : D.toNat + 16 ≤ 2 ^ 32
  hS : S.toNat + 2048 ≤ 2 ^ 32
  reads : Covers [⟨W.setWidth 64, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨D.setWidth 64, 16⟩, ⟨S.setWidth 64, 2048⟩] s.wr

/-- What a call of a block function on one block leaves. -/
structure BlkPost (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s : State) (W D S : BitVec 32)
    (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨D.setWidth 64, 16⟩, ⟨S.setWidth 64, 2048⟩, below (s.gpr .esp) 24] s.mem s'.mem
  out : bytesAt s'.mem (D.setWidth 64) 16 =
    (f R (bytesAt s.mem (W.setWidth 64) (16 * (R + 1))) (Spec.Aes.stateAt s.mem (D.setWidth 64))).toList

/-- The regions the block function is called with. -/
abbrev blkRd (E W : BitVec 32) : List Region := [⟨W.setWidth 64, 240⟩, ⟨(E - BitVec.ofNat 32 20).setWidth 64, 20⟩]
abbrev blkWr (D S : BitVec 32) : List Region := [⟨D.setWidth 64, 16⟩, ⟨S.setWidth 64, 2048⟩]

theorem toNat_rounds {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 32 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)

namespace BlkPre
variable {s : State} {W D S : BitVec 32} {R : Nat} (h : BlkPre s W D S R)
include h

theorem fit : 4 * blkRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : arg (pushed blkRegs s).callEntry 0 = W ∧ arg (pushed blkRegs s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed blkRegs s).callEntry 2 = D ∧ arg (pushed blkRegs s).callEntry 3 = 1 ∧
    arg (pushed blkRegs s).callEntry 4 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit hrs (by decide)] <;> simp [h.eax, h.ecx, h.ebx, h.edi, h.ebp]

theorem sub20 : Region.Sub (below (s.gpr .esp) 20) (below (s.gpr .esp) 24) := below_sub (by omega) h.esp

theorem sub4 : Region.Sub ⟨(s.gpr .esp - BitVec.ofNat 32 24).setWidth 64, 4⟩ (below (s.gpr .esp) 24) := by
  have := below_inner (sp := s.gpr .esp) (a := 4) (b := 24) (k := 20) (by omega) h.esp
  rw [show s.gpr .esp - BitVec.ofNat 32 24 = s.gpr .esp - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
    rw [← VG.Offset.sub_add_eq]; rfl]
  exact this

theorem callPre {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} :
    CallPre (Proof.Aes.blocksX86 f) blkRegs (blkRd (s.gpr .esp) W) (blkWr D S) s := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := h.args
  have hR := toNat_rounds h.rounds
  have eA : argAddr (pushed blkRegs s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed blkRegs s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 24 := by
    rw [callEntry_esp']; rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.blocksX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, hR,
      show (1 : BitVec 32).toNat = 1 from rfl, Nat.mul_one]
    refine ⟨trivial, trivial, h.wd, h.ws, h.ds, h.bd.sub_left h.sub20, h.bs.sub_left h.sub20,
      h.bd.sub_left h.sub4, h.bs.sub_left h.sub4, h.hW, h.hD, h.hS, ?_, h.rounds⟩
    rw [sub_toNat (by have := h.esp; omega)]; have := (s.gpr .esp).isLt; omega
  · intro a n ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a n ⟨_, List.mem_singleton_self _, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a n ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a n hi
    obtain ⟨r', hr', hc'⟩ := h.writes a n hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end BlkPre

theorem blk_call {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (nosp : NoSp b.code) (stack : stackUse b.code = 0)
    {s : State} {W D S : BitVec 32} {R : Nat} (h : BlkPre s W D S R) :
    WP isa (Impl.AesCbc.X86.blkCall b) s (BlkPost f s W D S R) := by
  have hR := toNat_rounds h.rounds
  have hR' : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  unfold Impl.AesCbc.X86.blkCall
  refine WP.callWith (rs := blkRegs) (k := Proof.Aes.blocksX86 f) ok nosp (by decide) hrs
    (by rw [stack]; have := h.esp; simp only [List.length_cons, List.length_nil]; omega) h.callPre
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4⟩ := h.args
  rw [stack] at f'
  have fE := callEntry_frame h.fit hrs
  rw [show 4 * blkRegs.length + 4 = 24 from rfl] at fE
  have keep : ∀ {p : BitVec 32} {n k : Nat}, (below (s.gpr .esp) 24).Disjoint ⟨p.setWidth 64, n⟩ → k ≤ n →
      n ≤ 240 → bytesAt (pushed blkRegs s).callEntry.mem (p.setWidth 64) k = bytesAt s.mem (p.setWidth 64) k :=
    fun hd hk hn => Proof.Cmac.bytesAt_frame fE (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hd.sub_right (Region.sub_prefix hk)).symm) (by omega)
  simp only [Proof.Aes.blocksX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, hR,
    show (1 : BitVec 32).toNat = 1 from rfl, m₂] at post
  refine ⟨rd', wr', cs', ?_, ?_⟩
  · exact f'.mono fun r hr => by simp only [List.cons_append, List.nil_append] at hr; simpa using hr
  · rw [bytesAt_of_statesAt post, keep h.bw hR' (Nat.le_refl _), ← ofFn_bytesAt,
      keep h.bd (Nat.le_refl _) (by decide), ofFn_bytesAt]

/-- Calls of a block function on one block, with the same arguments and
stack pointer in both runs, are constant time. -/
theorem blk_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86 f).pre (Proof.Aes.blocksX86 f).pub b.code)
    {W D S E : BitVec 32} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → BlkPre s₁ W D S R ∧ BlkPre s₂ W D S R ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P (Impl.AesCbc.X86.blkCall b) fun _ _ => True := by
  refine RelCT.callWith ok ct (blkRd E W) (blkWr D S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.callPre (f := f)
  have p₂ := h₂.callPre (f := f)
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]

end VG.Proof.AesCbc.X86
