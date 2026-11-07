module

public import VerifiedGarbage.Impl.Aes.X86.Ctr32
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Aes.X86.Common
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Aes.X86.Ctr32
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Aes.X86.Common
meta import VerifiedGarbage.Spec.Gcm
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES counter mode on x86 (32-bit): the contract, and constant time

The contract the proof is written against, and the constant-time half of
the proof: the taint analysis (`VG.X86.Taint`) starts with `esp` public
and knows where the arguments are and which of them are the base addresses
of the counter block, the data and the scratch buffer. The data pointer
and the count round-trip through public slots of the scratch buffer; the
stores of the keystream through the data pointer forget them, and the code
stores them again from the registers.
-/

@[expose] public section

namespace VG.Proof.Aes

open Spec.Gcm

open _root_.VG.X86 in
/-- X86 (32-bit) contract for `vg_aes_ctr32(schedule: *const [u8; 240], rounds:
usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut
[u64; 256])`, whose arguments are on the stack: XORs the AES counter-mode
keystream from the counter block at `counter` into the `n` blocks at `data`, and
advances the counter block by `n`.

The code may read `schedule` (240 bytes) and the arguments (24 bytes above
the return address), and read and write `counter` (16 bytes), `data`
(`16 n` bytes) and `scratch` (2048 bytes, whose contents on exit are
unspecified). The writable buffers may not overlap each other, `schedule`,
the arguments or the return address; nothing may wrap around the end of the
(32-bit) address space. `rounds` is 10, 12 or 14. `esp` and the arguments
are public; the key schedule, the counter block and the data are secret. -/
def ctr32X86 : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let counter : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 2048⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint counter ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint counter ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2048 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    let ciph := aesWith (arg s 1).toNat
      (Spec.Aes.bytesAt s.mem ((arg s 0).setWidth 64) (16 * ((arg s 1).toNat + 1)))
    blocksAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
        ctr32 ciph (blockAt s.mem ((arg s 2).setWidth 64))
          (blocksAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) ∧
      blockAt s'.mem ((arg s 2).setWidth 64) =
        Nat.repeat inc32 (arg s 4).toNat (blockAt s.mem ((arg s 2).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

open _root_.VG.X86 in
/-- X86 (32-bit) contract for `vg_aes_ctr32_to(schedule: *const [u8; 240],
rounds: usize, counter: *mut [u8; 16], src: *const [u8; 16], n: usize,
scratch: *mut [u64; 256], dst: *mut [u8; 16])`: `ctr32X86` out of place, the
`n` blocks at `src` XORed with the keystream and written to `dst`, a buffer
apart from every other; `src` is only read. The arguments are 28 bytes above
the return address, all public, in two regions: the first six, which a
caller pushes, and `dst`, which it may store in a frame of its own. -/
def ctr32ToX86 : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let counter : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let src : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
    let dst : Region := ⟨(arg s 6).setWidth 64, 16 * (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 2048⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let last : Region := ⟨argAddr s 6, 4⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args, last, src] ∧ s.wr = [counter, dst, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint dst ∧ sched.Disjoint scratch ∧
    counter.Disjoint dst ∧ counter.Disjoint scratch ∧ dst.Disjoint scratch ∧
    src.Disjoint counter ∧ src.Disjoint dst ∧ src.Disjoint scratch ∧
    args.Disjoint counter ∧ args.Disjoint dst ∧ args.Disjoint scratch ∧
    last.Disjoint counter ∧ last.Disjoint dst ∧ last.Disjoint scratch ∧
    ret.Disjoint counter ∧ ret.Disjoint dst ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + 2048 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    let ciph := aesWith (arg s 1).toNat
      (Spec.Aes.bytesAt s.mem ((arg s 0).setWidth 64) (16 * ((arg s 1).toNat + 1)))
    blocksAt s'.mem ((arg s 6).setWidth 64) (arg s 4).toNat =
        ctr32 ciph (blockAt s.mem ((arg s 2).setWidth 64))
          (blocksAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) ∧
      blockAt s'.mem ((arg s 2).setWidth 64) =
        Nat.repeat inc32 (arg s 4).toNat (blockAt s.mem ((arg s 2).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

end VG.Proof.Aes

namespace VG.Proof.Aes.X86

open VG VG.X86

/-! ## The precondition -/

section
variable (s : State)

abbrev schP : BitVec 32 := arg s 0
abbrev nRounds : Nat := (arg s 1).toNat
abbrev ctrP : BitVec 32 := arg s 2
abbrev datP : BitVec 32 := arg s 3
abbrev nBlk : Nat := (arg s 4).toNat
abbrev scrP : BitVec 32 := arg s 5
abbrev schR : Region := reg32 (schP s) 240
abbrev ctrR : Region := reg32 (ctrP s) 16
abbrev datR : Region := reg32 (datP s) (16 * nBlk s)
abbrev scrR : Region := reg32 (scrP s) 2048
abbrev argR : Region := ⟨argAddr s 0, 24⟩
abbrev retR : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩

end

/-- `ctr32X86.pre`, by name. -/
structure CPre (s : State) : Prop where
  rd : s.rd = [schR s, argR s]
  wr : s.wr = [ctrR s, datR s, scrR s]
  dSC : (schR s).Disjoint (ctrR s)
  dSD : (schR s).Disjoint (datR s)
  dSB : (schR s).Disjoint (scrR s)
  dCD : (ctrR s).Disjoint (datR s)
  dCB : (ctrR s).Disjoint (scrR s)
  dDB : (datR s).Disjoint (scrR s)
  aC : (argR s).Disjoint (ctrR s)
  aD : (argR s).Disjoint (datR s)
  aB : (argR s).Disjoint (scrR s)
  rC : (retR s).Disjoint (ctrR s)
  rD : (retR s).Disjoint (datR s)
  rB : (retR s).Disjoint (scrR s)
  fS : (schP s).toNat + 240 ≤ 2 ^ 32
  fC : (ctrP s).toNat + 16 ≤ 2 ^ 32
  fD : (datP s).toNat + 16 * nBlk s ≤ 2 ^ 32
  fB : (scrP s).toNat + 2048 ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  rounds : nRounds s = 10 ∨ nRounds s = 12 ∨ nRounds s = 14

theorem CPre.of {s : State} (h : Proof.Aes.ctr32X86.pre s) : CPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩

/-! ## In place or out of place -/

section
variable (to : Bool) (s : State)

/-- Where the result goes: the data in place, `dst` (argument 6) out of place. -/
abbrev dstP : BitVec 32 := if to then arg s 6 else arg s 3
abbrev srcR : Region := reg32 (datP s) (16 * nBlk s)
abbrev dstR : Region := reg32 (dstP to s) (16 * nBlk s)
/-- The bytes from the return address to the end of the arguments. -/
abbrev argN : Nat := if to then 32 else 28
abbrev argRg : Region := ⟨argAddr s 0, argN to - 4⟩

end

/-- What `ctr32X86.pre` and `ctr32ToX86.pre` give, by name: the data at
`src`, read, and the result written to `dst` (the same bytes in place, or
apart). -/
structure GPre (to : Bool) (s : State) : Prop where
  rS : schR s ∈ s.rd
  rA : ∀ i, i < 6 ∨ (to = true ∧ i = 6) → InRegions s.rd (addr (s.gpr .esp) (4 + 4 * i)) 4
  wC : ctrR s ∈ s.wr
  wD : dstR to s ∈ s.wr
  wB : scrR s ∈ s.wr
  rSrc : srcR s ∈ s.rd ++ s.wr
  dSC : (schR s).Disjoint (ctrR s)
  dSB : (schR s).Disjoint (scrR s)
  dSD : (schR s).Disjoint (dstR to s)
  dCD : (ctrR s).Disjoint (dstR to s)
  dCS : (ctrR s).Disjoint (srcR s)
  dCB : (ctrR s).Disjoint (scrR s)
  dDB : (dstR to s).Disjoint (scrR s)
  dSrcB : (srcR s).Disjoint (scrR s)
  sd : SrcDst ((datP s).setWidth 64) ((dstP to s).setWidth 64) (nBlk s)
  aC : (argRg to s).Disjoint (ctrR s)
  aD : (argRg to s).Disjoint (dstR to s)
  aB : (argRg to s).Disjoint (scrR s)
  rC : (retR s).Disjoint (ctrR s)
  rD : (retR s).Disjoint (dstR to s)
  rB : (retR s).Disjoint (scrR s)
  fS : (schP s).toNat + 240 ≤ 2 ^ 32
  fC : (ctrP s).toNat + 16 ≤ 2 ^ 32
  fSrc : (datP s).toNat + 16 * nBlk s ≤ 2 ^ 32
  fD : (dstP to s).toNat + 16 * nBlk s ≤ 2 ^ 32
  fB : (scrP s).toNat + 2048 ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + argN to ≤ 2 ^ 32
  rounds : nRounds s = 10 ∨ nRounds s = 12 ∨ nRounds s = 14

/-- The argument `i` is within the arguments. -/
theorem argRg_contains {to : Bool} {s : State} (hsp : (s.gpr .esp).toNat + argN to ≤ 2 ^ 32) {i : Nat}
    (hi : i < 6 ∨ (to = true ∧ i = 6)) : (argRg to s).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4 := by
  have := hsp
  rcases hi with hi | ⟨rfl, rfl⟩
  · cases to <;> simp only [argRg, argN, Bool.false_eq_true, ↓reduceIte] at this ⊢ <;>
      exact part_contains this (by omega) (by omega) (by omega) (by decide)
  · simp only [argRg, argN, ↓reduceIte] at this ⊢
    exact part_contains this (by omega) (by omega) (by omega) (by decide)

theorem GPre.argC {to : Bool} {s : State} (hp : GPre to s) {i : Nat} (hi : i < 6 ∨ (to = true ∧ i = 6)) :
    (argRg to s).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  argRg_contains hp.fSp hi

theorem CPre.gpre {s : State} (hp : CPre s) : GPre false s :=
  { rS := by rw [hp.rd]; exact List.mem_cons_self ..
    rA := fun i hi => ⟨_, by rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _),
      argRg_contains (to := false) hp.fSp hi⟩
    wC := by rw [hp.wr]; exact List.mem_cons_self ..
    wD := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    wB := by rw [hp.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    rSrc := by rw [hp.wr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    dSC := hp.dSC, dSB := hp.dSB, dSD := hp.dSD, dCD := hp.dCD, dCS := hp.dCD, dCB := hp.dCB, dDB := hp.dDB,
    dSrcB := hp.dDB, sd := .inl rfl, aC := hp.aC, aD := hp.aD, aB := hp.aB, rC := hp.rC, rD := hp.rD,
    rB := hp.rB, fS := hp.fS, fC := hp.fC, fSrc := hp.fD, fD := hp.fD, fB := hp.fB, fSp := hp.fSp,
    rounds := hp.rounds }

/-- Two regions, one after the other, apart from a third: the one they make
up is. -/
theorem disj_join {a : Addr} {X : Region} (h₁ : (⟨a, 24⟩ : Region).Disjoint X)
    (h₂ : (⟨a + BitVec.ofNat 64 24, 4⟩ : Region).Disjoint X) : (⟨a, 28⟩ : Region).Disjoint X := by
  intro x hx hX
  simp only [Region.Contains] at hx
  by_cases hlt : (x - a).toNat < 24
  · exact h₁ x (by simp only [Region.Contains]; omega) hX
  · refine h₂ x ?_ hX
    simp only [Region.Contains]
    bv_omega

theorem argAddr6 {s : State} (h : (s.gpr .esp).toNat + 32 ≤ 2 ^ 32) :
    argAddr s 6 = argAddr s 0 + BitVec.ofNat 64 24 := by
  simp only [argAddr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem GPre.ofTo {s : State} (h : Proof.Aes.ctr32ToX86.pre s) : GPre true s := by
  obtain ⟨hrd, hwr, dSC, dSD, dSB, dCD, dCB, dDB, dSrcC, dSrcD, dSrcB, aC, aD, aB, lC, lD, lB, rC, rD, rB, fS, fC,
    fSrc, fD, fB, fSp, hR⟩ := h
  have e6 := argAddr6 (s := s) fSp
  rw [e6] at lC lD lB
  exact
  { rS := by rw [hrd]; exact List.mem_cons_self ..
    rA := fun i hi => by
      rcases hi with hi | ⟨-, rfl⟩
      · exact ⟨_, by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..),
          argRg_contains (to := false) (by simp only [argN, Bool.false_eq_true, ↓reduceIte]; omega) (.inl hi)⟩
      · refine ⟨_, by rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), ?_⟩
        rw [show addr (s.gpr .esp) (4 + 4 * 6) = argAddr s 6 from rfl]
        exact Region.contains_self _ _
    wC := by rw [hwr]; exact List.mem_cons_self ..
    wD := by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    wB := by rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    rSrc := by rw [hrd]; exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    dSC := dSC, dSB := dSB, dSD := dSD, dCD := dCD, dCS := dSrcC.symm, dCB := dCB, dDB := dDB, dSrcB := dSrcB,
    sd := .inr dSrcD, aC := disj_join aC lC, aD := disj_join aD lD, aB := disj_join aB lB, rC := rC, rD := rD, rB := rB, fS := fS, fC := fC,
    fSrc := fSrc, fD := fD, fB := fB, fSp := fSp, rounds := hR }

theorem GPre.argSub {to : Bool} {s : State} (hp : GPre to s) {i : Nat} (hi : i < 6 ∨ (to = true ∧ i = 6)) :
    Region.Sub ⟨addr (s.gpr .esp) (4 + 4 * i), 4⟩ (argRg to s) := by
  have := hp.fSp
  rcases hi with hi | ⟨rfl, rfl⟩
  · cases to <;> simp only [argRg, argN, Bool.false_eq_true, ↓reduceIte] at this ⊢ <;>
      exact part_sub this (by omega) (by omega) (by omega)
  · simp only [argRg, argN, ↓reduceIte] at this ⊢
    exact part_sub this (by omega) (by omega) (by omega)

/-! ## Constant time -/

/-- The taint analysis starts with `esp` public, and the words holding
`counter`, `data` and `scratch` known to be the base addresses of the
writable regions. -/
def ctrτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [16, 0, 2048], argLen := 28,
    argBases := [(12, 0), (16, 1), (24, 2)] }

theorem ctr_wf₀ {s : State} (hp : CPre s) : VG.X86.Taint.Wf ctrτ₀ s := by
  have hC := hp.fC; have hD := hp.fD; have hB := hp.fB; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ctrτ₀]; omega, ?_⟩, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil))
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.dCD, hp.dCB⟩, hp.dDB, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [toNat_setWidth32] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.rC hp.aC
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.rD hp.aD
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [ctrτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem ctr_agree₀ {s₁ s₂ : State} (h₁ : Proof.Aes.ctr32X86.pre s₁) (h₂ : Proof.Aes.ctr32X86.pre s₂)
    (hpub : Proof.Aes.ctr32X86.pub s₁ s₂) : VG.X86.Taint.Agree ctrτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := CPre.of h₁; have hp₂ := CPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ctr_wf₀ hp₁, ctr_wf₀ hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ctrτ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [ctrR, datR, scrR, ctrP, datP, nBlk, scrP, ha 2 (by omega), ha 3 (by omega),
      ha 4 (by omega), ha 5 (by omega)]
  · simp only [ctrτ₀] at hk
    rw [show VG.X86.Taint.depth ctrτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 28) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 28) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32X86.pre Proof.Aes.ctr32X86.pub Impl.Aes.X86.ctr32 :=
  VG.Taint.constantTime (A := VG.X86.taint) ctrτ₀ (fun _ _ h₁ h₂ hp => ctr_agree₀ h₁ h₂ hp)
    (by taint_decide)

/-- Out of place: the arguments 28 bytes above the return address, and the
word holding `dst` (at 28) the base address of the writable region it gives. -/
def ctrToτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [16, 0, 2048], argLen := 32,
    argBases := [(12, 0), (28, 1), (24, 2)] }

theorem ctrTo_wf₀ {s : State} (hp : Proof.Aes.ctr32ToX86.pre s) : VG.X86.Taint.Wf ctrToτ₀ s := by
  obtain ⟨-, hwr, -, -, -, dCD, dCB, dDB, -, -, -, aC, aD, aB, lC, lD, lB, rC, rD, rB, -, fC, -, fD, fB, fSp, -⟩ := hp
  have e6 := argAddr6 (s := s) fSp
  rw [e6] at lC lD lB
  replace aC := disj_join aC lC
  replace aD := disj_join aD lD
  replace aB := disj_join aB lB
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ctrToτ₀]; omega, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨dCD, dCB⟩, dDB, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [toNat_setWidth32] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 28) (by omega) rC aC
    · exact VG.X86.Taint.frame_disjoint (n := 28) (by omega) rD aD
    · exact VG.X86.Taint.frame_disjoint (n := 28) (by omega) rB aB
  · intro p hp'
    simp only [ctrToτ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

theorem ctrTo_agree₀ {s₁ s₂ : State} (h₁ : Proof.Aes.ctr32ToX86.pre s₁) (h₂ : Proof.Aes.ctr32ToX86.pre s₂)
    (hpub : Proof.Aes.ctr32ToX86.pub s₁ s₂) : VG.X86.Taint.Agree ctrToτ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have fSp₁ : (s₁.gpr .esp).toNat + 32 ≤ 2 ^ 32 := (GPre.ofTo h₁).fSp
  have fSp₂ : (s₂.gpr .esp).toNat + 32 ≤ 2 ^ 32 := (GPre.ofTo h₂).fSp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ctrTo_wf₀ h₁, ctrTo_wf₀ h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ctrToτ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [h₁.2.1, h₂.2.1]
    simp only [ha 2 (by omega), ha 4 (by omega), ha 5 (by omega), ha 6 (by omega)]
  · simp only [ctrToτ₀] at hk
    rw [show VG.X86.Taint.depth ctrToτ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 32) fSp₁ h4 hk, VG.X86.Taint.argByte_eq (n := 32) fSp₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem ctr32To_ct :
    ConstantTime isa Proof.Aes.ctr32ToX86.pre Proof.Aes.ctr32ToX86.pub Impl.Aes.X86.ctr32To :=
  VG.Taint.constantTime (A := VG.X86.taint) ctrToτ₀ (fun _ _ h₁ h₂ hp => ctrTo_agree₀ h₁ h₂ hp)
    (by taint_decide)

end VG.Proof.Aes.X86
