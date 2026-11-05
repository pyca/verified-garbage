module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillABI
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Refill
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameStore
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets

-- separate module: the entry's symbolic execution, which a change to the loop's proofs does not re-elaborate

/-! # The refillable-tape search's entry on x86-64

The entry stores the arguments in the attempts' frame and the controller's
words. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Impl.Bignum.X86_64 (at0)

/-- The entry's stores of registers and constants. -/
def headerA (pLen qLen : Nat) : List Instr :=
  [.store (sp 48) .rdi, .store (sp 56) .rsi, .store (Impl.Dsa.X86_64.Generation.Refill.ctl 0) .rdx,
   .store (sp 64) .rcx, .store (sp 72) .r8, .store (sp 104) .rcx, .store (sp 120) .r8,
   .store (sp 88) .rcx, .mov32 .rax (.imm 0), .store (sp 96) .rax, .store (sp 80) .rax,
   .store (sp 40) .r9,
   .mov32 .rax (.imm (BitVec.ofNat 32 pLen)), .store (sp 136) .rax,
   .mov32 .rax (.imm (BitVec.ofNat 32 qLen)), .store (sp 144) .rax, .store (sp 224) .rax]

/-- The entry's loads of `state` and `state[0]`. -/
def headerB : List Instr :=
  [.mov .rax (.mem (sp (Impl.Dsa.X86_64.Generation.Refill.frameBytes + 32 + 48 + 16))),
   .store (Impl.Dsa.X86_64.Generation.Refill.ctl 1) .rax,
   .mov .rax (.mem (at0 .rax)), .store (Impl.Dsa.X86_64.Generation.Refill.ctl 2) .rax]

theorem entryHeader_eq (pLen qLen : Nat) :
    Impl.Dsa.X86_64.Generation.Refill.entryHeader pLen qLen = headerA pLen qLen ++ headerB := rfl

/-- The memory after `headerA`. -/
def chainA (m : Mem) (F : Addr) (g : Reg → BitVec 64) (pLen qLen : Nat) : Mem :=
  ((((((((((((((m.writeW (off F 48) (g .rdi)).writeW (off F 56) (g .rsi)).writeW (off F 296) (g .rdx)).writeW
    (off F 64) (g .rcx)).writeW (off F 72) (g .r8)).writeW (off F 104) (g .rcx)).writeW (off F 120) (g .r8)).writeW
    (off F 88) (g .rcx)).writeW (off F 96) (0 : BitVec 64)).writeW (off F 80) (0 : BitVec 64)).writeW
    (off F 40) (g .r9)).writeW (off F 136) (BitVec.ofNat 64 pLen)).writeW (off F 144) (BitVec.ofNat 64 qLen)).writeW
    (off F 224) (BitVec.ofNat 64 qLen))

theorem zext_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem headerA_ok {s : State} {F : Addr} (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) (hctl : ctlRegion F ∈ s.wr)
    (hb : F.toNat + 328 ≤ 2 ^ 64) {pLen qLen : Nat} (hp : pLen < 2 ^ 31) (hq : qLen < 2 ^ 31) :
    WP isa (.block (headerA pLen qLen)) s fun t =>
      t.mem = chainA s.mem F s.gpr pLen qLen ∧ Keep [.rax] s t := by
  have fs : Scr s F frameBytes := Scr.of_mem hfr (by unfold frameBytes; omega)
  have cs : Scr s (off F 296) 32 := Scr.of_mem hctl (by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have c0 : InRegions s.wr (off F 296) 8 := by simpa [off_off] using cs.st (d := 0) (by decide)
  refine WP.keep [.rax] ?_ rfl
  xrun [headerA, chainA, Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes,
    ea_sp, hsp, c0, fs.st (d := 48) (by decide), fs.st (d := 56) (by decide), fs.st (d := 64) (by decide),
    fs.st (d := 72) (by decide), fs.st (d := 104) (by decide), fs.st (d := 120) (by decide),
    fs.st (d := 88) (by decide), fs.st (d := 96) (by decide), fs.st (d := 80) (by decide),
    fs.st (d := 40) (by decide), fs.st (d := 136) (by decide), fs.st (d := 144) (by decide),
    fs.st (d := 224) (by decide), Nat.mul_zero, Nat.add_zero, zext_ofNat (by omega : pLen < 2 ^ 32),
    zext_ofNat (by omega : qLen < 2 ^ 32), zext_ofNat (by decide : 0 < 2 ^ 32)]
  rfl

/-! ## The controller's words -/

theorem ctl_contains (F : Addr) {k : Nat} (hk : k < 4) :
    (ctlRegion F).Contains (off F (296 + 8 * k)) 8 :=
  Offset.contains F (e := 296) (by omega) (by omega) (by omega)

theorem ctl_frame (F : Addr) :
    (ctlRegion F).Disjoint ⟨F, frameBytes⟩ :=
  (Offset.base_disjoint F (e := 296) (n := 32) (k := frameBytes) (by decide) (by omega)).symm

theorem ctl_below (F : Addr) :
    (ctlRegion F).Disjoint (below F 192) :=
  Offset.disjoint_below F (n := 192) (d := 296) (k := 32) (by omega)

theorem ctl_write (m : Mem) (F : Addr) {k : Nat} (hk : k < 4) (v : BitVec 64) :
    Frame [ctlRegion F] m (m.writeW (off F (296 + 8 * k)) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) v (ctl_contains F hk)

theorem ctlWord_frame {rs : List Region} {m m' : Mem} {F : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (ctlRegion F).Disjoint r) {k : Nat} (hk : k < 4) :
    ctlWord m' F k = ctlWord m F k :=
  hf.readW (ctl_contains F hk) hd (by decide)

theorem ctlWord_write_self (m : Mem) (F : Addr) (k : Nat) (v : BitVec 64) :
    ctlWord (m.writeW (off F (296 + 8 * k)) v) F k = v := Mem.readW_writeW_self64 ..

theorem ctlWord_write_other (m : Mem) (F : Addr) {j k : Nat} (hj : j < 4)
    (hk : k < 4) (hne : j ≠ k) (v : BitVec 64) :
    ctlWord (m.writeW (off F (296 + 8 * k)) v) F j = ctlWord m F j := by
  unfold ctlWord
  rw [Mem.readW_writeW_sep (Offset.sep F (d := 296 + 8 * j) (n := 8) (e := 296 + 8 * k) (k := 8) (by omega)
    (by omega) (by omega)) (by decide)]

theorem rep_ctl {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    (hS : (ctlRegion F).Disjoint ⟨S, oRsa⟩) {k : Nat} (hk : k < 4) (v : BitVec 64) :
    Rep (m.writeW (off F (296 + 8 * k)) v) F S V W :=
  rep_of_disjoint_frame R (ctl_write m F hk v)
    (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact (ctl_frame F).symm)
    (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact hS.symm)

/-! ## The entry -/

/-- The frame words after `headerA`. -/
def wordsA (W : Nat → BitVec 64) (g : Reg → BitVec 64) (pLen qLen : Nat) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd W 6 (g .rdi)) 7 (g .rsi)) 8 (g .rcx)) 9 (g .r8))
    13 (g .rcx)) 15 (g .r8)) 11 (g .rcx)) 12 0) 10 0) 5 (g .r9)) 17 (BitVec.ofNat 64 pLen))
    18 (BitVec.ofNat 64 qLen)) 28 (BitVec.ofNat 64 qLen)

theorem chainA_rep {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) (hS : (ctlRegion F).Disjoint ⟨S, oRsa⟩)
    (g : Reg → BitVec 64) (pLen qLen : Nat) :
    Rep (chainA m F g pLen qLen) F S V (wordsA W g pLen qLen) := by
  have R2 := (R.wf G (k := 6) (by decide) (g .rdi)).wf G (k := 7) (by decide) (g .rsi)
  have R3 := rep_ctl R2 hS (k := 0) (by decide) (g .rdx)
  exact ((((((((((R3.wf G (k := 8) (by decide) _).wf
    G (k := 9) (by decide) _).wf G (k := 13) (by decide) _).wf G (k := 15) (by decide) _).wf G (k := 11) (by decide)
    _).wf G (k := 12) (by decide) _).wf G (k := 10) (by decide) _).wf G (k := 5) (by decide) _).wf
    G (k := 17) (by decide) _).wf G (k := 18) (by decide) _).wf G (k := 28) (by decide) _

theorem chainA_frame (m : Mem) (F : Addr) (g : Reg → BitVec 64) (pLen qLen : Nat) :
    Frame [⟨F, frameBytes⟩, ctlRegion F] m (chainA m F g pLen qLen) := by
  have fc : ∀ d, d + 8 ≤ frameBytes → (⟨F, frameBytes⟩ : Region).Contains (off F d) 8 := fun d hd =>
    Offset.contains_base F hd (by unfold frameBytes at hd; omega)
  unfold chainA
  refine Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW
    (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.refl _ _)
    (List.mem_cons_self ..) _ (fc 48 (by decide))) (List.mem_cons_self ..) _ (fc 56 (by decide)))
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (ctl_contains F (k := 0) (by decide)))
    (List.mem_cons_self ..) _ (fc 64 (by decide))) (List.mem_cons_self ..) _ (fc 72 (by decide)))
    (List.mem_cons_self ..) _ (fc 104 (by decide))) (List.mem_cons_self ..) _ (fc 120 (by decide)))
    (List.mem_cons_self ..) _ (fc 88 (by decide))) (List.mem_cons_self ..) _ (fc 96 (by decide)))
    (List.mem_cons_self ..) _ (fc 80 (by decide))) (List.mem_cons_self ..) _ (fc 40 (by decide)))
    (List.mem_cons_self ..) _ (fc 136 (by decide))) (List.mem_cons_self ..) _ (fc 144 (by decide)))
    (List.mem_cons_self ..) _ (fc 224 (by decide))

theorem ea_at0' (t : State) (b : Reg) : t.ea (at0 b) = t.gpr b := by
  simp only [State.ea, at0, BitVec.ofInt_ofNat, BitVec.add_zero]

theorem headerB_ok {s : State} {F : Addr} (hsp : s.gpr .rsp = F) (hctl : ctlRegion F ∈ s.wr)
    (hb : F.toNat + 328 ≤ 2 ^ 64) {a v : BitVec 64}
    (ha : InRegions (s.rd ++ s.wr) (off F 392) 8) (hav : s.mem.readW (off F 392) 64 = a)
    (hv : InRegions (s.rd ++ s.wr) a 8) (hvv : (s.mem.writeW (off F 304) a).readW a 64 = v) :
    WP isa (.block headerB) s fun t =>
      t.mem = (s.mem.writeW (off F 304) a).writeW (off F 312) v ∧ Keep [.rax] s t := by
  have cs : Scr s (off F 296) 32 := Scr.of_mem hctl (by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have c1 : InRegions s.wr (off F 304) 8 := by simpa [off_off] using cs.st (d := 8) (by decide)
  have c2 : InRegions s.wr (off F 312) 8 := by simpa [off_off] using cs.st (d := 16) (by decide)
  refine WP.keep [.rax] ?_ rfl
  xrun [headerB, Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes,
    ea_sp, ea_at0', hsp, c1, c2, ha, hav, hv, hvv]

/-- The memory after the first three stores, which the rest of `headerA` keeps outside the frame. -/
def chainA₀ (m : Mem) (F : Addr) (g : Reg → BitVec 64) : Mem :=
  ((m.writeW (off F 48) (g .rdi)).writeW (off F 56) (g .rsi)).writeW (off F 296) (g .rdx)

theorem chainA_ctl (m : Mem) (F : Addr) (g : Reg → BitVec 64) (pLen qLen : Nat) :
    ctlWord (chainA m F g pLen qLen) F 0 = g .rdx := by
  have fc : ∀ d, d + 8 ≤ frameBytes → (⟨F, frameBytes⟩ : Region).Contains (off F d) 8 := fun d hd =>
    Offset.contains_base F hd (by unfold frameBytes at hd; omega)
  have hf : Frame [⟨F, frameBytes⟩] (chainA₀ m F g) (chainA m F g pLen qLen) := by
    unfold chainA
    refine Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW
      (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.refl _ _)
      (List.mem_cons_self ..) _ (fc 64 (by decide))) (List.mem_cons_self ..) _ (fc 72 (by decide)))
      (List.mem_cons_self ..) _ (fc 104 (by decide))) (List.mem_cons_self ..) _ (fc 120 (by decide)))
      (List.mem_cons_self ..) _ (fc 88 (by decide))) (List.mem_cons_self ..) _ (fc 96 (by decide)))
      (List.mem_cons_self ..) _ (fc 80 (by decide))) (List.mem_cons_self ..) _ (fc 40 (by decide)))
      (List.mem_cons_self ..) _ (fc 136 (by decide))) (List.mem_cons_self ..) _ (fc 144 (by decide)))
      (List.mem_cons_self ..) _ (fc 224 (by decide))
  rw [ctlWord_frame hf (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact ctl_frame F) (by decide)]
  exact ctlWord_write_self _ F 0 _

theorem contains_head (a : Addr) {n k : Nat} (h : n ≤ k) : (⟨a, k⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

/-- The state the body starts from: the three frames allocated and the
callee-saved registers saved. -/
structure RefillAllocated {pBytes : Nat} {s₀ : State} (h : RefillABI pBytes s₀) (u : State) : Prop where
  rsp : u.gpr .rsp = refillBase s₀
  frame : (⟨refillBase s₀, frameBytes⟩ : Region) ∈ u.wr
  ctl : ctlRegion (refillBase s₀) ∈ u.wr
  wr : ∀ r ∈ s₀.wr, r ∈ u.wr
  rd : u.rd = s₀.rd
  regs : ∀ r, r ≠ .rsp → u.gpr r = s₀.gpr r
  mem : Frame [⟨off (low s₀) 520, 48⟩] s₀.mem u.mem

theorem refillBase_bound {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (refillBase s).toNat + 328 ≤ 2 ^ 64 := by
  rw [refillBase_toNat h]; have := (s.gpr .rsp).isLt; have : 568 ≤ (s.gpr .rsp).toNat := h.stackLower; omega

theorem refillBase_args (s : State) : off (refillBase s) 392 = stackArgAddr s 1 := by
  simp only [refillBase, low, off, stackArgAddr, refillStack]
  bv_omega

/-- The stack's regions are disjoint from each buffer. -/
theorem RefillABI.frame_disjoint {pBytes : Nat} {s : State} (h : RefillABI pBytes s) {r : Region}
    (hr : r = inOut s ∨ r = inUsed s ∨ r = inRand s ∨ r = inScr s ∨ r = inState s ∨ r = inArgs s) :
    ∀ q ∈ [(⟨off (low s) 520, 48⟩ : Region), ⟨refillBase s, frameBytes⟩, ctlRegion (refillBase s)], r.Disjoint q := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact (h.stack_disjoint (by decide) hr).symm
  · exact (h.stack_disjoint (d := 192) (n := 296) (by decide) hr).symm
  · rw [ctlRegion_eq]; exact (h.stack_disjoint (by decide) hr).symm

theorem RefillABI.geo {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    Geo (refillBase s) (refillGeometry h).hash := by
  have hh := (refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  exact ⟨by have := refillBase_bound h; unfold frameBytes; omega, (refillGeometry h).part_bound hh,
    (refillGeometry h).frame_part hh,
    ((refillGeometry h).stack_part hh).sub_left (below_sub (a := 16) (by decide) (by decide))⟩

theorem RefillABI.ctl_arena {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (ctlRegion (refillBase s)).Disjoint ⟨s.gpr .r9, VG.Impl.Dsa.Generation.Layout.usedBytes pBytes⟩ := by
  rw [ctlRegion_eq]
  exact (h.stack_disjoint (r := inScr s) (by decide) (by simp)).sub_right h.arena_sub

theorem RefillABI.ctl_hash {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (ctlRegion (refillBase s)).Disjoint ⟨(refillGeometry h).hash, oRsa⟩ :=
  h.ctl_arena.sub_right ((refillGeometry h).part_sub
    ((refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)))

theorem RefillAllocated.randMemory {pBytes : Nat} {s₀ u v : State} {h : RefillABI pBytes s₀}
    (a : RefillAllocated h u) (hf : Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem v.mem)
    (hr : v.rd = u.rd) : GenerationTapeMemory (randTape h) v where
  cover := by
    intro x n hx
    simp only [randTape, bytesAt_length, InRegions, List.mem_singleton] at hx
    obtain ⟨r, rfl, hx⟩ := hx
    refine ⟨_, List.mem_append_left _ ?_, hx⟩
    rw [hr, a.rd, h.rd]; exact List.mem_cons_self ..
  bytes := by
    change Spec.Rsa.bytesAt v.mem (s₀.gpr .rcx) (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat).length = _
    rw [bytesAt_length]
    have hall : Frame [(⟨off (low s₀) 520, 48⟩ : Region), ⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)]
        s₀.mem v.mem :=
      (a.mem.mono (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)).trans
      (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
    exact VG.Proof.Dsa.Generation.frame_bytesAt hall (h.frame_disjoint (r := inRand s₀) (by simp))
      (Nat.le_of_lt (s₀.gpr .r8).isLt)

theorem entry_ok {pBytes qBytes : Nat} {s₀ u : State} (h : RefillABI pBytes s₀) (a : RefillAllocated h u)
    (hq : qBytes = Spec.Dsa.generationQLen pBytes) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.Refill.entryHeader pBytes qBytes ++
        Impl.Dsa.X86_64.Generation.entryDerived)) u fun v =>
      ∃ W, GenerationMemory (refillContext h) W v ∧ W 16 = 0 ∧ W 10 = 0 ∧
        ctlWord v.mem (refillBase s₀) 0 = s₀.gpr .rdx ∧ ctlWord v.mem (refillBase s₀) 1 = stackArg s₀ 1 ∧
        ctlWord v.mem (refillBase s₀) 2 = s₀.mem.readW (stackArg s₀ 1) 64 ∧
        Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem v.mem ∧ Keep [.rax] u v := by
  have hp : pBytes < 2 ^ 31 := by have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega
  have hq' : qBytes < 2 ^ 31 := by have := h.lengths; unfold Spec.Dsa.generationLengthsValid at this; omega
  have hb := refillBase_bound h
  have G := h.geo
  have hS := h.ctl_hash
  rw [entryHeader_eq, List.append_assoc]
  apply WP.block_append
  refine WP.mono (headerA_ok a.rsp a.frame a.ctl hb hp hq') fun t ⟨hm, kt⟩ => ?_
  have RA := chainA_rep G (initialRep u.mem (refillBase s₀) (refillGeometry h).hash) hS u.gpr pBytes qBytes
  rw [← hm] at RA
  have fA : Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem t.mem := by
    rw [hm]; exact chainA_frame _ _ _ _ _
  -- the arguments and `state[0]`, through the stores so far
  have argsC : (inArgs s₀).Contains (off (refillBase s₀) 392) 8 := by
    rw [refillBase_args]
    exact Offset.contains (s₀.gpr .rsp) (e := 8) (d := 16) (by decide) (by decide) (by decide)
  have hall : ∀ {m : Mem}, Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem m →
      Frame [(⟨off (low s₀) 520, 48⟩ : Region), ⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] s₀.mem m :=
    fun hf => (a.mem.mono (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)).trans
      (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
  have hav : t.mem.readW (off (refillBase s₀) 392) 64 = stackArg s₀ 1 := by
    rw [(hall fA).readW argsC (h.frame_disjoint (r := inArgs s₀) (by simp)) (by decide), refillBase_args]; rfl
  have ha : InRegions (t.rd ++ t.wr) (off (refillBase s₀) 392) 8 :=
    ⟨inArgs s₀, List.mem_append_left _ (by rw [kt.2.1, a.rd, h.rd]; simp), argsC⟩
  have stC : (inState s₀).Contains (stackArg s₀ 1) 8 := contains_head _ (by decide)
  have hv : InRegions (t.rd ++ t.wr) (stackArg s₀ 1) 8 :=
    ⟨inState s₀, List.mem_append_right _ (by rw [kt.2.2]; exact a.wr _ (by rw [h.wr]; simp)), stC⟩
  have fA1 : Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem
      (t.mem.writeW (off (refillBase s₀) 304) (stackArg s₀ 1)) :=
    fA.writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (ctl_contains _ (k := 1) (by decide))
  have hvv : (t.mem.writeW (off (refillBase s₀) 304) (stackArg s₀ 1)).readW (stackArg s₀ 1) 64 =
      s₀.mem.readW (stackArg s₀ 1) 64 :=
    (hall fA1).readW stC (h.frame_disjoint (r := inState s₀) (by simp)) (by decide)
  apply WP.block_append
  refine WP.mono (headerB_ok ((kt.gpr (by decide)).trans a.rsp) (by rw [kt.2.2]; exact a.ctl) hb ha hav hv hvv)
    fun t₂ ⟨hm₂, kt₂⟩ => ?_
  have RB := rep_ctl (rep_ctl RA hS (k := 1) (by decide) (stackArg s₀ 1)) hS (k := 2) (by decide)
    (s₀.mem.readW (stackArg s₀ 1) 64)
  rw [← hm₂] at RB
  have fB : Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem t₂.mem := by
    rw [hm₂]; exact fA1.writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (ctl_contains _ (k := 2) (by decide))
  have sp₂ : t₂.gpr .rsp = refillBase s₀ := (kt₂.gpr (by decide)).trans ((kt.gpr (by decide)).trans a.rsp)
  have wr₂ : t₂.wr = u.wr := kt₂.2.2.trans kt.2.2
  refine WP.mono (entryDerived_ok G RB sp₂ (by rw [wr₂]; exact a.frame) (B := u.gpr .r9) rfl)
    fun v ⟨Rv, fv, kv⟩ => ?_
  have fV : Frame [⟨refillBase s₀, frameBytes⟩, ctlRegion (refillBase s₀)] u.mem v.mem :=
    fB.trans (fv.mono fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact List.mem_cons_self ..)
  have kV : Keep [.rax] u v := ((kt.trans kt₂).trans kv).mono (by decide)
  have spv : v.gpr .rsp = refillBase s₀ := (kv.gpr (by decide)).trans sp₂
  have r9 : u.gpr .r9 = s₀.gpr .r9 := a.regs _ (by decide)
  have scr : Scr v (s₀.gpr .r9) (VG.Impl.Dsa.Generation.Layout.usedBytes pBytes) :=
    ⟨⟨s₀.gpr .r9, 0, (stackArg s₀ 0).toNat * 8, by rw [kV.2.2]; exact a.wr _ (by rw [h.wr]; simp [inScr]),
      by simp [off], by have := h.scratchSize; omega, by have := h.scrBound; omega⟩,
      by have := h.scrBound; have := h.scratchSize; omega⟩
  have hh := (refillGeometry h).small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  have ctl₂ : ∀ k < 4, ctlWord v.mem (refillBase s₀) k = ctlWord t₂.mem (refillBase s₀) k := fun k hk =>
    ctlWord_frame fv (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact ctl_frame _) hk
  refine ⟨_, ⟨?_, ⟨_, Rv⟩, ?_, scr, a.randMemory fV kV.2.1, ?_, a.randMemory fV kV.2.1⟩, ?_, ?_, ?_, ?_, ?_, fV, kV⟩
  · exact { rsp := spv, fr := by rw [kV.2.2]; exact a.frame
            F8 := by show 8 ≤ (refillBase s₀).toNat; have := refillBase_toNat h; have : 568 ≤ (s₀.gpr .rsp).toNat := h.stackLower; omega
            Fw := G.Fw, sc := scr.sub hh (by decide)
            slot := by
              show Bignum.word v.mem (refillBase s₀) (8 * 14) = off (s₀.gpr .r9) VG.Impl.Dsa.Generation.Layout.hash
              rw [Rv.fr 14 (by decide)]
              simp only [workspaceWords, derivedWords, workspaceSlots, List.foldl, upd, r9]
              rfl
            dFS := G.dFS, dRS := G.dRS }
  · intro k hk
    simp only [generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [workspaceWords, derivedWords, workspaceSlots, List.foldl, wordsA, upd, refillContext,
      refillWords, r9, a.regs _ (by decide : Reg.rdi ≠ .rsp), a.regs _ (by decide : Reg.rsi ≠ .rsp),
      a.regs _ (by decide : Reg.rcx ≠ .rsp), a.regs _ (by decide : Reg.r8 ≠ .rsp), hq]
    all_goals first | rfl | simp [off]
  · exact GenerationTapeMemory.slice (a.randMemory fV kV.2.1) (Nat.zero_le _)
  · simp [workspaceWords, upd]
  · simp [workspaceWords, derivedWords, workspaceSlots, wordsA, upd]
  · rw [ctl₂ 0 (by decide), hm₂, ctlWord_write_other _ _ (j := 0) (k := 2) (by decide) (by decide) (by decide),
      ctlWord_write_other _ _ (j := 0) (k := 1) (by decide) (by decide) (by decide), hm, chainA_ctl,
      a.regs _ (by decide)]
  · rw [ctl₂ 1 (by decide), hm₂, ctlWord_write_other _ _ (j := 1) (k := 2) (by decide) (by decide) (by decide)]
    exact ctlWord_write_self _ _ 1 _
  · rw [ctl₂ 2 (by decide), hm₂]
    exact ctlWord_write_self _ _ 2 _

end VG.Proof.Dsa.X86_64.Generation.Refill
