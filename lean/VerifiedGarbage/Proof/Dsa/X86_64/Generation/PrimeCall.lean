module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PrimeCall
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeState
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # Calling the probable-prime test, which returns its cursor and status to the generation frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

/-- What calling the test of `bits` bits needs of the generation's state: the
frame, the scratch base `A` in frame word 5, the witness tape `rand` at `rp`
with `used` octets read, and the candidate `N` at its offset of the scratch. -/
structure PrimeCallInputs (bits : Nat) (F S A rp : Addr) (rand : List Byte) (N used : Nat)
    (W : Nat → BitVec 64) (V : Nat → Byte) (s : State) : Prop where
  layout : Lay s F S
  rep : Rep s.mem F S V W
  arena : W 5 = A
  arenaWrite : Scr s A domainCheck
  tapePtr : W 13 = rp
  tapeLength : W 15 = BitVec.ofNat 64 rand.length
  usedSlot : W 16 = BitVec.ofNat 64 used
  usedBound : used ≤ rand.length
  tapeSize : rand.length < 2 ^ 64
  tapeCover : Covers [⟨rp, rand.length⟩] (s.rd ++ s.wr)
  tapeBytes : Spec.Rsa.bytesAt s.mem rp rand.length = rand
  candidate : Spec.Dsa.decodeBE
    (Spec.Rsa.bytesAt s.mem (off A (Impl.Dsa.X86_64.ProbablePrime.candidate bits)) (bits / 8)) = N
  odd : N % 2 = 1
  bitLen : Spec.Dsa.bitLength N = bits

/-- Where the test's arguments lie, relative to each other and the stack. -/
structure PrimeCallGeometry (bits : Nat) (F S A rp : Addr) (n : Nat) : Prop where
  stackSize : 192 ≤ F.toNat
  arenaBound : A.toNat + domainCheck ≤ 2 ^ 64
  tapeBound : rp.toNat + n ≤ 2 ^ 64
  tapeArena : (⟨rp, n⟩ : Region).Disjoint ⟨A, domainCheck⟩
  tapeFrame : (⟨rp, n⟩ : Region).Disjoint ⟨F, frameBytes⟩
  tapeStack : (⟨rp, n⟩ : Region).Disjoint (below F 192)
  arenaFrame : (⟨A, domainCheck⟩ : Region).Disjoint ⟨F, frameBytes⟩
  arenaStack : (⟨A, domainCheck⟩ : Region).Disjoint (below F 192)
  hashTest : ∀ r ∈ [(⟨off A arithmetic, arithmeticBytes⟩ : Region),
    ⟨off A witness, bits / 8⟩, below F 192], (⟨S, oRsa⟩ : Region).Disjoint r

/-- What the call may change. -/
def primeCallChanged (bits : Nat) (F A : Addr) : List Region :=
  [⟨off A arithmetic, arithmeticBytes⟩, ⟨off A witness, bits / 8⟩, below F 192, ⟨F, frameBytes⟩]

theorem bytes_of_src {s : State} {B p : Addr} {Z : Nat} {bs : List Byte} (h : Src s B Z p bs) :
    Spec.Rsa.bytesAt s.mem p bs.length = bs := by
  apply List.ext_getElem (by simp [bytesAt_length])
  intro i h₁ h₂
  simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
  exact h.val i h₂

/-- The arguments, from the frame. -/
theorem primeCallArgs_ok {bits : Nat} (hb : ProbablePrime.Supported bits) {F S A rp : Addr}
    {rand : List Byte} {N used : Nat} {W : Nat → BitVec 64} {V : Nat → Byte} {s : State}
    (h : PrimeCallInputs bits F S A rp rand N used W V s) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.primeCallArgs bits)) s fun u =>
      u.gpr .rdi = A ∧ u.gpr .rsi = BitVec.ofNat 64 (domainCheck / 8) ∧
      u.gpr .rdx = rp + BitVec.ofNat 64 used ∧ u.gpr .rcx = BitVec.ofNat 64 (rand.length - used) ∧
      u.gpr .r8 = off F 152 ∧ u.gpr .r9 = BitVec.ofNat 64 bits ∧ u.mem = s.mem ∧
      Keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] s u := by
  have L := h.layout
  have w5 : s.mem.readW (F + BitVec.ofNat 64 40) 64 = A := (h.rep.fr 5 (by decide)).trans h.arena
  have w13 : s.mem.readW (F + BitVec.ofNat 64 104) 64 = rp := (h.rep.fr 13 (by decide)).trans h.tapePtr
  have w15 : s.mem.readW (F + BitVec.ofNat 64 120) 64 = BitVec.ofNat 64 rand.length :=
    (h.rep.fr 15 (by decide)).trans h.tapeLength
  have w16 : s.mem.readW (F + BitVec.ofNat 64 128) 64 = BitVec.ofNat 64 used :=
    (h.rep.fr 16 (by decide)).trans h.usedSlot
  have hsub : BitVec.ofNat 64 rand.length - BitVec.ofNat 64 used = BitVec.ofNat 64 (rand.length - used) := by
    have := h.usedBound
    have := h.tapeSize
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have h9 : (BitVec.ofNat 32 bits).setWidth 64 = BitVec.ofNat 64 bits := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := hb.le
    omega
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u =>
      u.gpr .rdi = A ∧ u.gpr .rsi = BitVec.ofNat 64 (domainCheck / 8) ∧
      u.gpr .rdx = rp + BitVec.ofNat 64 used ∧ u.gpr .rcx = BitVec.ofNat 64 (rand.length - used) ∧
      u.gpr .r8 = off F 152 ∧ u.gpr .r9 = BitVec.ofNat 64 bits ∧ u.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.primeCallArgs, Impl.Mgf1.X86_64.sp, State.ea, BitVec.ofInt_natCast,
      L.rsp, L.ld (d := 40) (by decide), L.ld (d := 104) (by decide), L.ld (d := 120) (by decide),
      L.ld (d := 128) (by decide), w5, w13, w15, w16, hsub, h9]
    exact congrArg (F + ·) (by decide)) rfl)
    fun u ⟨hu, hk⟩ => ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2.1, hu.2.2.2.2.2.2, hk⟩

/-- The test's regions: the rest of the tape; the scratch space and `used`. -/
def primeCallRd (rp : Addr) (rand : List Byte) (used : Nat) : List Region :=
  [⟨rp + BitVec.ofNat 64 used, rand.length - used⟩]

def primeCallWr (F A : Addr) : List Region :=
  [⟨A, domainCheck⟩, ⟨off F 152, 8⟩]

/-- The regions the call involves, as subregions of the generation's. -/
theorem primeCall_rest_sub (rp : Addr) {used n : Nat} (h : used ≤ n) :
    Region.Sub ⟨rp + BitVec.ofNat 64 used, n - used⟩ ⟨rp, n⟩ :=
  Offset.sub_base _ (by omega)

theorem primeCall_used_sub (F : Addr) : Region.Sub ⟨off F 152, 8⟩ ⟨F, frameBytes⟩ :=
  Offset.sub_base _ (by decide)

theorem primeCall_ret_sub (F : Addr) : Region.Sub ⟨F - 8, 8⟩ (below F 192) :=
  Offset.sub_below _ (by decide) (by decide)

theorem primeCall_stack_sub (F : Addr) : Region.Sub ⟨F - 8 - 184#64, 184⟩ (below F 192) := by
  rw [BitVec.sub_sub]
  exact Offset.sub_below _ (by decide) (by decide)

theorem primeCall_frame_below (F : Addr) : (⟨F, frameBytes⟩ : Region).Disjoint (below F 192) :=
  Offset.base_disjoint_below F (by decide)

theorem primeCall_pre {bits : Nat} (hb : ProbablePrime.Supported bits) {F S A rp : Addr} {rand : List Byte}
    {N used : Nat} {W : Nat → BitVec 64} {V : Nat → Byte} {s u : State}
    (h : PrimeCallInputs bits F S A rp rand N used W V s) (g : PrimeCallGeometry bits F S A rp rand.length)
    (hdi : u.gpr .rdi = A) (hsi : u.gpr .rsi = BitVec.ofNat 64 (domainCheck / 8))
    (hdx : u.gpr .rdx = rp + BitVec.ofNat 64 used) (hcx : u.gpr .rcx = BitVec.ofNat 64 (rand.length - used))
    (h8 : u.gpr .r8 = off F 152) (h9 : u.gpr .r9 = BitVec.ofNat 64 bits) (hm : u.mem = s.mem)
    (hsp : u.gpr .rsp = F) :
    ProbablePrime.contract.pre
      (u.callEntry.withRegions (primeCallRd rp rand used) (primeCallWr F A)) := by
  have hbits : (BitVec.ofNat 64 bits).toNat = bits := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hb.le; omega)]
  have hdc : (BitVec.ofNat 64 (domainCheck / 8)).toNat * 8 = domainCheck := by decide
  have hn := h.tapeSize
  have hl : (BitVec.ofNat 64 (rand.length - used)).toNat = rand.length - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hFw := h.layout.Fw
  have rest := primeCall_rest_sub rp h.usedBound
  have hcand : (Impl.Dsa.X86_64.ProbablePrime.layout bits).candidate + bits / 8 ≤ domainCheck := by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have hval : Proof.Dsa.ProbablePrime.candidateAt (Impl.Dsa.X86_64.ProbablePrime.layout bits)
      (u.mem.writeW (F - 8) (u.unknowns 0)) A = N := by
    unfold Proof.Dsa.ProbablePrime.candidateAt
    rw [VG.Proof.Dsa.Generation.frame_bytesAt ((Frame.refl _ _).writeW (r := ⟨F - 8, 8⟩)
      List.mem_cons_self _ (Region.contains_self _ _)) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact (g.arenaStack.sub_left (Offset.sub_base _ hcand)).sub_right (primeCall_ret_sub F))
      (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide), hm]
    exact h.candidate
  sig_pre [ProbablePrime.contract, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig,
    abi, argRegs]
  sig_and_intros
  all_goals simp only [hdi, hsi, hdx, hcx, h8, h9, hsp, hdc, hl, hbits]
  · have := g.stackSize
    change 184 ≤ (F - 8).toNat
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 8 ≤ F.toNat; omega)]
    change 184 ≤ F.toNat - 8
    omega
  · rfl
  · rfl
  · exact g.tapeArena.symm.sub_right rest
  · exact g.arenaFrame.sub_right (primeCall_used_sub F)
  · exact (g.tapeFrame.sub_left rest).sub_right (primeCall_used_sub F)
  · exact (g.arenaStack.sub_left (fun _ h => h)).symm.sub_left (primeCall_ret_sub F)
  · exact (g.tapeStack.sub_left rest).symm.sub_left (primeCall_ret_sub F)
  · exact (primeCall_frame_below F).symm.sub_left (primeCall_ret_sub F) |>.sub_right (primeCall_used_sub F)
  · exact g.arenaStack.symm.sub_left (primeCall_stack_sub F)
  · exact (g.tapeStack.sub_left rest).symm.sub_left (primeCall_stack_sub F)
  · exact (primeCall_frame_below F).symm.sub_left (primeCall_stack_sub F) |>.sub_right (primeCall_used_sub F)
  · exact g.arenaBound
  · have := g.tapeBound
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := h.usedBound
    have : used % 2 ^ 64 = used := Nat.mod_eq_of_lt (by omega)
    rw [this]
    have := Nat.mod_le (rp.toNat + used) (2 ^ 64)
    omega
  · simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := Nat.mod_le (F.toNat + 152 % 2 ^ 64) (2 ^ 64)
    unfold frameBytes at hFw
    omega
  · exact hb.mem
  · decide
  · rw [hval]; exact h.odd
  · rw [hval]; exact h.bitLen

/-- What the call itself leaves, before its result is stored. -/
structure PrimeCalled (bits : Nat) (F S A rp : Addr) (rand : List Byte) (N used : Nat)
    (s u t : State) : Prop where
  rd : t.rd = u.rd
  wr : t.wr = u.wr
  rsp : t.gpr .rsp = F
  status : (t.gpr .rax).setWidth 32 =
    BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime N (rand.drop used)))
  read : ∀ b rest, Spec.Dsa.probablePrime N (rand.drop used) = some (b, rest) →
    word t.mem F 152 = BitVec.ofNat 64 (rand.length - used - rest.length)
  frame : Frame [⟨off A arithmetic, arithmeticBytes⟩, ⟨off A witness, bits / 8⟩, below F 192,
    ⟨off F 152, 8⟩] s.mem t.mem

/-- What the callee starts from: its precondition, regions of the caller's,
and the candidate and the tape it reads. -/
structure PrimeEntry (bits : Nat) (F A rp : Addr) (rand : List Byte) (N used : Nat) (u : State) : Prop where
  pre : ProbablePrime.contract.pre
    (u.callEntry.withRegions (primeCallRd rp rand used) (primeCallWr F A))
  reads : Covers (primeCallRd rp rand used ++ primeCallWr F A) (u.rd ++ u.wr)
  writes : Covers (primeCallWr F A) u.wr
  candidate : Proof.Dsa.ProbablePrime.candidateAt (Impl.Dsa.X86_64.ProbablePrime.layout bits)
    (u.mem.writeW (F - 8) (u.unknowns 0)) A = N
  tape : Spec.Rsa.bytesAt (u.mem.writeW (F - 8) (u.unknowns 0)) (rp + BitVec.ofNat 64 used)
    (rand.length - used) = rand.drop used

theorem primeCall_entry {bits : Nat} (hb : ProbablePrime.Supported bits)
    {F S A rp : Addr} {rand : List Byte} {N used : Nat} {W : Nat → BitVec 64} {V : Nat → Byte} {s u : State}
    (h : PrimeCallInputs bits F S A rp rand N used W V s) (g : PrimeCallGeometry bits F S A rp rand.length)
    (hdi : u.gpr .rdi = A) (hsi : u.gpr .rsi = BitVec.ofNat 64 (domainCheck / 8))
    (hdx : u.gpr .rdx = rp + BitVec.ofNat 64 used) (hcx : u.gpr .rcx = BitVec.ofNat 64 (rand.length - used))
    (h8 : u.gpr .r8 = off F 152) (h9 : u.gpr .r9 = BitVec.ofNat 64 bits) (hm : u.mem = s.mem)
    (hsp : u.gpr .rsp = F) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) :
    PrimeEntry bits F A rp rand N used u := by
  have hn := h.tapeSize
  have hu := h.usedBound
  have rest := primeCall_rest_sub rp hu
  -- The memory the callee starts from: its return address below `F`.
  have hcand : (Impl.Dsa.X86_64.ProbablePrime.layout bits).candidate + bits / 8 ≤ domainCheck := by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have entry : Frame [⟨F - 8, 8⟩] u.mem (u.mem.writeW (F - 8) (u.unknowns 0)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have hval : Proof.Dsa.ProbablePrime.candidateAt (Impl.Dsa.X86_64.ProbablePrime.layout bits)
      (u.mem.writeW (F - 8) (u.unknowns 0)) A = N := by
    unfold Proof.Dsa.ProbablePrime.candidateAt
    rw [VG.Proof.Dsa.Generation.frame_bytesAt entry (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact (g.arenaStack.sub_left (Offset.sub_base _ hcand)).sub_right (primeCall_ret_sub F))
      (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide), hm]
    exact h.candidate
  have htape : Spec.Rsa.bytesAt (u.mem.writeW (F - 8) (u.unknowns 0)) (rp + BitVec.ofNat 64 used)
      (rand.length - used) = rand.drop used := by
    rw [VG.Proof.Dsa.Generation.frame_bytesAt entry (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact (g.tapeStack.sub_left rest).sub_right (primeCall_ret_sub F)) (by omega), hm]
    have happ := VG.Proof.Dsa.Generation.bytesAt_append s.mem rp used (rand.length - used)
    rw [show used + (rand.length - used) = rand.length by omega, h.tapeBytes] at happ
    generalize rand.length = L at happ ⊢
    rw [happ, List.drop_left' (bytesAt_length _ _ _)]
  have hl : (BitVec.ofNat 64 (rand.length - used)).toNat = rand.length - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  -- The callee's regions are the generation's.
  have cA : Covers [⟨A, domainCheck⟩] u.wr := by
    obtain ⟨⟨B₀, o, L₀, hmem, hbase, hle, _⟩, _⟩ := h.arenaWrite
    rw [hwr]
    exact Covers.of_sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, hmem, o, hbase, hle⟩
  have cU : Covers [⟨off F 152, 8⟩] u.wr := by
    rw [hwr]
    exact Covers.of_sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, h.layout.fr, 152, rfl, by change 152 + 8 ≤ frameBytes; decide⟩
  have cR : Covers (primeCallRd rp rand used) (u.rd ++ u.wr) := by
    rw [hrd, hwr]
    refine Covers.trans (Covers.of_sub fun r hr => ?_) h.tapeCover
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨rp, rand.length⟩, List.mem_cons_self, used, rfl, by simp only; omega⟩
  have cW : Covers (primeCallWr F A) u.wr := cA.cons (cU.cons Covers.nil)
  exact ⟨primeCall_pre hb h g hdi hsi hdx hcx h8 h9 hm hsp, cR.append_left cW.right, cW, hval, htape⟩

theorem primeCall_call_ok (T : PrimeTest) {bits : Nat} (hb : ProbablePrime.Supported bits)
    {F S A rp : Addr} {rand : List Byte} {N used : Nat} {W : Nat → BitVec 64} {V : Nat → Byte} {s u : State}
    (h : PrimeCallInputs bits F S A rp rand N used W V s) (g : PrimeCallGeometry bits F S A rp rand.length)
    (hdi : u.gpr .rdi = A) (hsi : u.gpr .rsi = BitVec.ofNat 64 (domainCheck / 8))
    (hdx : u.gpr .rdx = rp + BitVec.ofNat 64 used) (hcx : u.gpr .rcx = BitVec.ofNat 64 (rand.length - used))
    (h8 : u.gpr .r8 = off F 152) (h9 : u.gpr .r9 = BitVec.ofNat 64 bits) (hm : u.mem = s.mem)
    (hsp : u.gpr .rsp = F) (hrd : u.rd = s.rd) (hwr : u.wr = s.wr) :
    WP isa T.run u (PrimeCalled bits F S A rp rand N used s u) := by
  have hn := h.tapeSize
  have hd := T.depth
  have hbits : (BitVec.ofNat 64 bits).toNat = bits := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hb.le; omega)]
  have E := primeCall_entry hb h g hdi hsi hdx hcx h8 h9 hm hsp hrd hwr
  have hl : (BitVec.ofNat 64 (rand.length - used)).toNat = rand.length - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.usedBound; omega)]
  have hval := E.candidate
  have htape := E.tape
  have entry : Frame [⟨F - 8, 8⟩] u.mem (u.mem.writeW (F - 8) (u.unknowns 0)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  refine WP.callF T.verified.1 (SpSafe.of_all T.safe.sp)
    (by have : ProbablePrime.stack = 184 := rfl; omega) E.pre E.reads E.writes ?_
  intro t hrd' hwr' hcs hf ⟨s₂, hm₂, hg₂, hpost⟩ _
  sig_post [ProbablePrime.contract, Proof.Dsa.ProbablePrime.sizedContract,
    Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs] at hpost
  rw [hsp, hdi, hsi, hdx, hcx, h9, hbits, hl, hval, htape] at hpost
  obtain ⟨hr, hkeeps, hused⟩ := hpost
  have hrax : t.gpr .rax = s₂.gpr .rax := (hg₂ .rax (by decide)).symm
  have hst : Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime N (rand.drop used)) < 3 := by
    rcases Spec.Dsa.probablePrime N (rand.drop used) with _ | ⟨_ | _, _⟩ <;>
      simp only [Proof.Dsa.ProbablePrime.status] <;> decide
  refine ⟨hrd', hwr', (hcs .rsp (by decide)).trans hsp, ?_, ?_, ?_⟩
  · rw [hrax]
    apply BitVec.eq_of_toNat_eq
    rw [hr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · intro b r hres
    have hw := hused b r hres
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, List.cons.injEq,
      and_true] at hw
    rw [h8, show off F 152 + BitVec.ofNat 64 0 = off F 152 from BitVec.add_zero _, hm₂] at hw
    exact hw
  · intro x hx
    have hxl : ∀ (d n : Nat), d + n ≤ 2 ^ 64 → ¬ (⟨off A d, n⟩ : Region).Contains x 1 →
        ¬ (d ≤ (x - A).toNat ∧ (x - A).toNat < d + n) := fun d n hdn hc h' =>
      hc (by unfold Region.Contains; have := (Offset.lt_iff x A hdn).mpr h'; simp only [off]; omega)
    by_cases hxA : (⟨A, domainCheck⟩ : Region).Contains x 1
    · have hi : (x - A).toNat < domainCheck := by unfold Region.Contains at hxA; simp only at hxA; omega
      have hx' : x = A + BitVec.ofNat 64 (x - A).toNat := by
        rw [ofNat_toNat64, BitVec.add_comm A, BitVec.sub_add_cancel]
      have h1 := hxl arithmetic arithmeticBytes (by decide) (hx _ List.mem_cons_self)
      have h2 := hxl witness (bits / 8) (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
        (hx _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have hk := hkeeps (x - A).toNat (by
        have : 8 * (BitVec.ofNat 64 (domainCheck / 8)).toNat = domainCheck := by decide
        omega) (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simp only [Impl.Dsa.X86_64.ProbablePrime.len]; omega
        · simp only; omega)
      rw [← hx'] at hk
      rw [← hm₂, hk, entry x (fun r hr hc => by
        obtain rfl := List.mem_singleton.mp hr
        exact (g.arenaStack.sub_right (primeCall_ret_sub F)) x hxA hc), hm]
    · rw [hf x (fun r hr hc => by
        simp only [primeCallWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (rfl | rfl) | rfl
        · exact hxA hc
        · exact hx _ (by simp) hc
        · rw [hsp] at hc
          exact hx (below F 192) (by simp) (below_sub (by have : ProbablePrime.stack = 184 := rfl; omega)
            (by decide) x hc)), hm]

/-- The status `k` the test returned, stored as the generation's (2 as 3), and
the octets read added to the cursor if the tape sufficed. -/
theorem primeCallResult_ok {t : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay t F S) (R : Rep t.mem F S V W) {k : Nat} (hk : k < 3)
    (hrax : (t.gpr .rax).setWidth 32 = BitVec.ofNat 32 k) :
    WP isa Impl.Dsa.X86_64.Generation.primeCallResult t fun t' =>
      Lay t' F S ∧
      Rep t'.mem F S V (upd (upd W 16 (if k = 0 then W 16 else W 19 + W 16)) 19 (BitVec.ofNat 64 (k + k / 2))) ∧
      Frame [⟨F, frameBytes⟩] t.mem t'.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  unfold Impl.Dsa.X86_64.Generation.primeCallResult
  have hz : ((t.gpr .rax).setWidth 32).setWidth 64 = BitVec.ofNat 64 k := by
    rw [hrax]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u => u.gpr .rax = BitVec.ofNat 64 k ∧ u.mem = t.mem)
    (by xrun [hz]) rfl) fun x ⟨⟨hrx, hmx⟩, kx⟩ => ?_)
  unfold Impl.Dsa.X86_64.Generation.primeCallStatus
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u => u.gpr .rax = BitVec.ofNat 64 k ∧
      u.zf = some (BitVec.ofNat 64 k == 0) ∧ u.mem = t.mem) (by
    xrun [hrx, hmx]
    rw [BitVec.and_self]) rfl) fun u ⟨⟨hra, hzf, hmu⟩, ku'⟩ => ?_)
  have ku := kx.trans ku'
  have Lu : Lay u F S := L.congr (ku.gpr (by decide)) ku.2.2 (by rw [hmu])
  have Ru : Rep u.mem F S V W := hmu ▸ R
  have hk0 : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> rfl
  refine WP.seq (WP.mono (Q := fun (v : State) => Lay v F S ∧
      Rep v.mem F S V (upd W 16 (if k = 0 then W 16 else W 19 + W 16)) ∧ v.gpr .rax = BitVec.ofNat 64 k ∧
      Frame [⟨F, frameBytes⟩] t.mem v.mem ∧ v.rd = t.rd ∧ v.wr = t.wr)
    (WP.ite (decide (k = 0)) (by simp only [eval, hzf, hk0]) (fun h0 => ?_) (fun h0 => ?_)) fun v hv => ?_)
  · have h0' : k = 0 := of_decide_eq_true h0
    refine WP.block_nil ⟨Lu, ?_, hra, by rw [hmu]; exact Frame.refl _ _, ku.2.1, ku.2.2⟩
    have : upd W 16 (W 16) = W := by funext i; by_cases hi : i = 16 <;> simp [upd, hi]
    simpa only [h0', ite_true, this] using Ru
  · have h0' : k ≠ 0 := of_decide_eq_false h0
    have w19 : u.mem.readW (F + BitVec.ofNat 64 152) 64 = W 19 := Ru.fr 19 (by decide)
    have w16 : u.mem.readW (F + BitVec.ofNat 64 128) 64 = W 16 := Ru.fr 16 (by decide)
    refine WP.mono (WP.keep [.rcx] (Q := fun (v : State) => v.mem = u.mem.writeW (off F (8 * 16)) (W 19 + W 16))
      (by
        xrun [Impl.Mgf1.X86_64.sp, State.ea, BitVec.ofInt_natCast, Lu.rsp, Lu.ld (d := 152) (by decide),
          Lu.ld (d := 128) (by decide), Lu.st (d := 128) (by decide), w19, w16, Nat.reduceMul]) rfl)
      fun v ⟨hm, kv⟩ => ?_
    have Rv : Rep v.mem F S V (upd W 16 (W 19 + W 16)) := hm ▸ Ru.wf Lu.geo (by decide) _
    refine ⟨lay_of_rep Lu Ru Rv (by simp [upd]) (kv.gpr (by decide)) kv.2.2, by simpa only [h0', ite_false] using Rv,
      (kv.gpr (by decide)).trans hra, ?_, kv.2.1.trans ku.2.1, kv.2.2.trans ku.2.2⟩
    rw [hm, hmu]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  · obtain ⟨Lv, Rv, hrv, fv, rdv, wrv⟩ := hv
    have hsum : BitVec.ofNat 64 k + BitVec.ofNat 64 k >>> 1 = BitVec.ofNat 64 (k + k / 2) := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide
    refine WP.mono (WP.keep [.rax, .rcx] (Q := fun (x : State) => x.mem = v.mem.writeW (off F (8 * 19))
        (BitVec.ofNat 64 (k + k / 2))) (by
      xrun [Impl.Mgf1.X86_64.sp, State.ea, BitVec.ofInt_natCast, Lv.rsp, Lv.st (d := 152) (by decide), hrv,
        Nat.reduceMul]
      rw [hsum]) rfl) fun x ⟨hm, kx⟩ => ?_
    have Rx : Rep x.mem F S V _ := hm ▸ Rv.wf Lv.geo (by decide : 19 < nW) (BitVec.ofNat 64 (k + k / 2))
    refine ⟨lay_of_rep Lv Rv Rx (by simp [upd]) (kx.gpr (by decide)) kx.2.2, Rx, ?_, kx.2.1.trans rdv,
      kx.2.2.trans wrv⟩
    rw [hm]
    exact fv.trans ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide)))

theorem primeCall_ok (T : PrimeTest) {bits : Nat} (hb : ProbablePrime.Supported bits)
    {F S A rp : Addr} {rand : List Byte} {N used : Nat} {W : Nat → BitVec 64} {V : Nat → Byte} {s : State}
    (h : PrimeCallInputs bits F S A rp rand N used W V s) (g : PrimeCallGeometry bits F S A rp rand.length) :
    WP isa (Impl.Dsa.X86_64.Generation.primeCall T.run bits) s fun t =>
      let res := Spec.Dsa.probablePrime N (rand.drop used)
      ∃ used' status, used' ≤ rand.length ∧ Lay t F S ∧
        Rep t.mem F S V (upd (upd W 16 (BitVec.ofNat 64 used')) 19 status) ∧
        (res = none → status = BitVec.ofNat 64 0) ∧
        (∀ b rest, res = some (b, rest) → status = BitVec.ofNat 64 (if b then 1 else 3) ∧
          used' = rand.length - rest.length) ∧
        Frame (primeCallChanged bits F A) s.mem t.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have L := h.layout
  have R := h.rep
  unfold Impl.Dsa.X86_64.Generation.primeCall
  refine WP.seq (WP.mono (primeCallArgs_ok hb h) fun u ⟨hdi, hsi, hdx, hcx, h8, h9, hm, ku⟩ => ?_)
  have hsp : u.gpr .rsp = F := (ku.gpr (by decide)).trans L.rsp
  refine WP.seq (WP.mono (primeCall_call_ok T hb h g hdi hsi hdx hcx h8 h9 hm hsp ku.2.1 ku.2.2)
    fun t C => ?_)
  -- The frame and the hash workspace, but for word 19, are as they were.
  have fused : ∀ {k : Nat}, k < nW → k ≠ 19 →
      (⟨off F (8 * k), 8⟩ : Region).Disjoint ⟨off F 152, 8⟩ := fun hk hne =>
    Offset.disjoint F (by omega) (by have : nW = 37 := rfl; omega) (by decide)
  have hlist : ∀ r ∈ [(⟨off A arithmetic, arithmeticBytes⟩ : Region), ⟨off A witness, bits / 8⟩, below F 192],
      Region.Sub r ⟨A, domainCheck⟩ ∨ r = below F 192 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl (Offset.sub_base _ (by decide))
    · exact Or.inl (Offset.sub_base _ (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide))
    · exact Or.inr rfl
  have Rt : Rep t.mem F S V (upd W 19 (word t.mem F 152)) := by
    refine ⟨fun o ho => ?_, fun k hk => ?_⟩
    · rw [C.frame _ (fun r hr hc => ?_)]
      · exact R.scr o ho
      have hS := cS S (o := o) (n := 1) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact g.hashTest _ List.mem_cons_self _ (hS.byte (by rw [BitVec.sub_self]; decide)) hc
      · exact g.hashTest _ (List.mem_cons_of_mem _ List.mem_cons_self) _ (hS.byte (by rw [BitVec.sub_self]; decide)) hc
      · exact g.hashTest _ (by simp) _ (hS.byte (by rw [BitVec.sub_self]; decide)) hc
      · exact L.dFS.symm.sub_right (primeCall_used_sub F) _ (hS.byte (by rw [BitVec.sub_self]; decide)) hc
    · by_cases h19 : k = 19
      · subst h19; simp [upd]
      · rw [show upd W 19 (word t.mem F 152) k = W k by simp [upd, h19], ← R.fr k hk]
        refine C.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have hf : Region.Sub ⟨off F (8 * k), 8⟩ ⟨F, frameBytes⟩ :=
          Offset.sub_base _ (by have : nW = 37 := rfl; have : frameBytes = 296 := rfl; omega)
        rcases hr with rfl | rfl | rfl | rfl
        · exact (g.arenaFrame.symm.sub_left hf).sub_right (Offset.sub_base _ (by decide))
        · exact (g.arenaFrame.symm.sub_left hf).sub_right
            (Offset.sub_base _ (by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide))
        · exact (primeCall_frame_below F).sub_left hf
        · exact fused hk h19
  have Lt : Lay t F S := lay_of_rep L R Rt (by simp [upd]) (C.rsp.trans L.rsp.symm) (C.wr.trans ku.2.2)
  have hk : Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime N (rand.drop used)) < 3 := by
    rcases Spec.Dsa.probablePrime N (rand.drop used) with _ | ⟨_ | _, _⟩ <;>
      simp only [Proof.Dsa.ProbablePrime.status] <;> decide
  refine WP.mono (primeCallResult_ok Lt Rt hk C.status) fun t' ⟨Lt', Rt', ft', rdt', wrt'⟩ => ?_
  have hn := h.tapeSize
  have hframe : Frame (primeCallChanged bits F A) s.mem t'.mem := by
    refine (Frame.sub C.frame fun r hr => ?_).trans (ft'.mono (by simp [primeCallChanged]))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [primeCallChanged], fun _ h => h⟩
    · exact ⟨_, by simp [primeCallChanged], fun _ h => h⟩
    · exact ⟨_, by simp [primeCallChanged], fun _ h => h⟩
    · exact ⟨_, by simp [primeCallChanged], primeCall_used_sub F⟩
  have hrd : t'.rd = s.rd := rdt'.trans (C.rd.trans ku.2.1)
  have hwr : t'.wr = s.wr := wrt'.trans (C.wr.trans ku.2.2)
  cases hres : Spec.Dsa.probablePrime N (rand.drop used) with
  | none =>
    simp only [hres, Proof.Dsa.ProbablePrime.status] at Rt'
    refine ⟨used, BitVec.ofNat 64 0, h.usedBound, Lt', ?_, fun _ => rfl, fun _ _ h' => absurd h' (by simp),
      hframe, hrd, hwr⟩
    have e : upd (upd W 16 (BitVec.ofNat 64 used)) 19 (BitVec.ofNat 64 0) =
        upd (upd (upd W 19 (word t.mem F 152)) 16 (upd W 19 (word t.mem F 152) 16)) 19
          (BitVec.ofNat 64 (0 + 0 / 2)) := by
      funext i
      by_cases h16 : i = 16 <;> by_cases h19 : i = 19 <;> simp [upd, h16, h19, h.usedSlot]
    rw [e]; exact Rt'
  | some r =>
    obtain ⟨b, rest⟩ := r
    have hsuf := (VG.Proof.Dsa.Generation.probablePrime_suffix hres).length_le
    rw [List.length_drop] at hsuf
    have hw19 := C.read b rest hres
    have hu := h.usedBound
    have hsum : BitVec.ofNat 64 (rand.length - used - rest.length) + BitVec.ofNat 64 used =
        BitVec.ofNat 64 (rand.length - rest.length) := by
      rw [← BitVec.ofNat_add]; congr 1; omega
    refine ⟨rand.length - rest.length, BitVec.ofNat 64 (if b then 1 else 3), by omega, Lt', ?_, fun h' => by simp at h',
      fun b' rest' h' => ?_, hframe, hrd, hwr⟩
    · have hk0 : Proof.Dsa.ProbablePrime.status (some (b, rest)) ≠ 0 := by
        cases b <;> simp [Proof.Dsa.ProbablePrime.status]
      simp only [hres, hk0, ite_false] at Rt'
      have e : upd (upd W 16 (BitVec.ofNat 64 (rand.length - rest.length))) 19
            (BitVec.ofNat 64 (if b then 1 else 3)) =
          upd (upd (upd W 19 (word t.mem F 152)) 16
            (upd W 19 (word t.mem F 152) 19 + upd W 19 (word t.mem F 152) 16)) 19
            (BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (some (b, rest)) +
              Proof.Dsa.ProbablePrime.status (some (b, rest)) / 2)) := by
        funext i
        simp only [upd]
        by_cases h19 : i = 19
        · subst h19; simp only [ite_true]; cases b <;> simp [Proof.Dsa.ProbablePrime.status]
        · by_cases h16 : i = 16
          · subst h16
            simp only [show (16 : Nat) ≠ 19 by decide, ite_false, ite_true, hw19, h.usedSlot, hsum]
          · simp only [h19, h16, ite_false]
      rw [e]; exact Rt'
    · simp only [Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨rfl, rfl⟩

/-- A test of the generation's: its parameters, and where they lie. -/
structure PrimeCallPlan where
  prime : PrimeParams
  hash : Addr
  W : Nat → BitVec 64
  bits : Nat
  supported : ProbablePrime.Supported bits
  len : prime.len = bits / 8
  base : prime.B = off (W 5) arithmetic
  witnessPtr : prime.p = off (W 5) witness
  tapePtr : W 13 = prime.rp
  tapeLength : W 15 = BitVec.ofNat 64 prime.rand.length
  geometry : PrimeCallGeometry bits prime.sp hash (W 5) prime.rp prime.rand.length

def PrimeCallPlan.changed (p : PrimeCallPlan) : List Region :=
  [⟨p.prime.B, arithmeticBytes⟩, ⟨p.prime.p, p.prime.len⟩, below p.prime.sp 192, ⟨p.prime.sp, frameBytes⟩]

theorem PrimeCallPlan.changed_eq (p : PrimeCallPlan) :
    p.changed = primeCallChanged p.bits p.prime.sp (p.W 5) := by
  rw [PrimeCallPlan.changed, primeCallChanged, p.base, p.witnessPtr, p.len]

/-- A shaped candidate of `8 * len` bits has exactly that many: from the plan's
`PrimeParams`. -/
theorem PrimeParams.bitLength_eq (P : PrimeParams) : Spec.Dsa.bitLength P.N = 8 * P.len := by
  have hk : 0 < 8 * P.len := by have := P.len2; omega
  obtain ⟨hlo, hhi⟩ := (VG.Proof.Dsa.bitLength_iff_bounds hk).mp
    (show Spec.Dsa.bitLength (P.N - 1) = 8 * P.len from P.predBits)
  apply (VG.Proof.Dsa.bitLength_iff_bounds hk).mpr
  have ho := P.odd
  have h3 := P.n3
  have heven : 2 ^ (8 * P.len) % 2 = 0 := by
    rw [show 8 * P.len = (8 * P.len - 1) + 1 by omega, Nat.pow_succ]; omega
  constructor <;> omega

end VG.Proof.Dsa.X86_64.Generation
