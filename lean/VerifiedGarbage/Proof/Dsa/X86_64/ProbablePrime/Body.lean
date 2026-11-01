module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Params
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeBytes
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Impl.Dsa.X86_64.ProbablePrime
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Exit
import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Args
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFootprint
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.WorkFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
/-! # The probable-prime test's body, between its frame's push and pop -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/ProbablePrime/Save.lean`, which only this module imported.
section

/-! # The probable-prime test keeps the callee-saved registers in its frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.X86_64.Spill VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime

def spillSlots : List (Reg × Nat) :=
  [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40)]

theorem spillSlots_fit : ∀ p ∈ spillSlots, p.2 + 8 ≤ 56 := by decide

theorem save_ok {s : State} (hw : (⟨s.gpr .rsp, 56⟩ : Region) ∈ s.wr) :
    WP isa (.block saveRegisters) s fun t =>
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Saved t.mem (s.gpr .rsp) s.gpr spillSlots ∧
      Frame [⟨s.gpr .rsp, 48⟩] s.mem t.mem := by
  change WP isa (.block (saveCode .rsp spillSlots)) s _
  apply WP.mono (VG.X86_64.Spill.save_ok .rsp spillSlots s (fun p hp =>
    ⟨_, hw, Offset.contains_base _ (spillSlots_fit p hp) (by have := spillSlots_fit p hp; omega)⟩))
  intro t ⟨hg, hr, hw, hm⟩
  refine ⟨hg, hr, hw, ?_, ?_⟩
  · rw [hm]; exact saveMem_saved _ _ _ _ (by decide)
  · rw [hm]; exact saveMem_frame_base _ _ _ _ (fun p hp => by revert p; decide) (by decide)

theorem restore_ok {s : State} (g : Reg → BitVec 64)
    (hw : (⟨s.gpr .rsp, 56⟩ : Region) ∈ s.wr)
    (hs : Saved s.mem (s.gpr .rsp) g spillSlots) :
    WP isa (.block restoreRegisters) s fun t =>
      (∀ r ∈ spillSlots.map Prod.fst, t.gpr r = g r) ∧
      (∀ r, r ∉ spillSlots.map Prod.fst → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  change WP isa (.block (restoreCode .rsp spillSlots)) s _
  exact VG.X86_64.Spill.restore_ok .rsp spillSlots g s (by decide) (fun p hp =>
    ⟨_, List.mem_append_right _ hw, Offset.contains_base _ (spillSlots_fit p hp)
      (by have := spillSlots_fit p hp; omega)⟩) hs

end VG.Proof.Dsa.X86_64.ProbablePrime
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/ProbablePrime/Entry.lean`, which only this module imported.
section

/-! # The probable-prime test's entry: `used` in the frame, the size in `r8`, the arithmetic workspace in `rdi` -/

section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime

theorem entry_ok {s : State} (hf : Scr s (s.gpr .rsp) 56) :
    WP isa (.block entry) s fun t =>
      t.gpr .rdi = off (s.gpr .rdi) Impl.Dsa.Generation.Layout.arithmetic ∧
      t.gpr .rsi = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rdx ∧ t.gpr .r8 = s.gpr .r9 ∧
      t.mem = s.mem.writeW (off (s.gpr .rsp) 48) (s.gpr .r8) ∧
      Keep [.rdi, .rsi, .r9, .r8] s t := by
  refine WP.mono (WP.keep [.rdi, .rsi, .r9, .r8] (Q := fun t =>
      t.gpr .rdi = off (s.gpr .rdi) Impl.Dsa.Generation.Layout.arithmetic ∧
      t.gpr .rsi = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rdx ∧ t.gpr .r8 = s.gpr .r9 ∧
      t.mem = s.mem.writeW (off (s.gpr .rsp) 48) (s.gpr .r8)) (by
    xrun [entry, sp, State.ea, BitVec.ofInt_natCast, hf.st (d := 48) (by decide)]
    rw [show BitVec.signExtend 64 (BitVec.ofNat 32 Impl.Dsa.Generation.Layout.arithmetic) =
      BitVec.ofNat 64 Impl.Dsa.Generation.Layout.arithmetic by decide]) rfl)
    fun _ ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hk⟩

end VG.Proof.Dsa.X86_64.ProbablePrime
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/ProbablePrime/Workspace.lean`, which only this module imported.
section

/-! # The probable-prime test's arithmetic workspace, of the words in `r12`

As `Generation.workspace_ok`, with the words from `r12` rather than an
immediate. -/

section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

theorem sizedWorkspace_ok {s : State} {B : Addr} {Z w : Nat}
    (h : Scr s B Z) (hdi : s.gpr .rdi = B) (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hZ : slot w 16 ≤ Z)
    (hw1 : 2 ≤ w) (hw2 : w < 2 ^ 24) :
    WP isa Impl.Dsa.X86_64.ProbablePrime.sizedWorkspace s fun t =>
      Ws t B Z w ∧ Good t B Z w 0 ∧
      Frm B [(48, 80), (224, 8)] s.mem t.mem ∧ Keep [.rax, .rdx] s t := by
  have hz : 256 ≤ Z := Nat.le_trans (Nat.le_add_right 256 _) hZ
  unfold Impl.Dsa.X86_64.ProbablePrime.sizedWorkspace
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun u =>
      u.mem = (s.mem.writeW (off B 48) (BitVec.ofNat 64 w)).writeW (off B 56) (0#64)) (by
    xrun [State.ea, hdr, hdrOff, sW, sMinv, hdi, h12, h.st (d := 48) (by omega), h.st (d := 56) (by omega)]
    rfl) rfl) fun u ⟨hm, ku⟩ => ?_)
  have hu := h.congr ku.2.2
  have hudi := (ku.gpr (by decide)).trans hdi
  have hu12 := (ku.gpr (by decide)).trans h12
  refine WP.seq (WP.mono (setBases_ok hu hudi hu12 (by unfold sArr; omega))
    fun v ⟨harr, fv, kv⟩ => ?_)
  have hv := hu.congr kv.2.2
  have hvdi := (kv.gpr (by decide)).trans hudi
  have hv12 := (kv.gpr (by decide)).trans hu12
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = v.mem.writeW (off B 224) (BitVec.ofNat 64 (8 * (w + 2)))) (by
    xrun [State.ea, hdr, hdrOff, sStride, sFn, hvdi, hv12, hv.st (d := 224) (by omega)]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      show (2 : BitVec 64).toNat = 2 from rfl]
    omega) rfl) fun t ⟨htm, kt⟩ => ?_
  have ft : Outside B 224 8 v.mem t.mem := by rw [htm]; exact writeW_outside _ _ _ (by decide)
  have allk := (ku.trans kv).trans kt
  have hw : word t.mem B 48 = BitVec.ofNat 64 w := by
    rw [ft.word (Or.inl (by decide)) (by decide), fv.word (Or.inl (by decide)) (by decide), hm,
      (writeW_outside _ B _ (d := 56) (by decide)).word (Or.inl (by decide)) (by decide), word_writeW_self]
  have hminv : word t.mem B 56 = 0 := by
    rw [ft.word (Or.inl (by decide)) (by decide), fv.word (Or.inl (by decide)) (by decide), hm, word_writeW_self]
    rfl
  have ha : ∀ j < 8, word t.mem B (8 * sArr j) = off B (slot w j) := by
    intro j hj
    rw [ft.word (Or.inl (by unfold sArr; omega)) (by unfold sArr; omega)]
    exact harr j hj
  have hs := h.congr allk.2.2
  have ht := allk.gpr (by decide) |>.trans hdi
  refine ⟨⟨hs, ht, hw, ?_, ha, hZ, hw1, hw2⟩, ⟨hs, ht, ⟨hw, hminv, ha⟩⟩, ?_, allk.mono (by decide)⟩
  · rw [htm]; exact word_writeW_self _ _ _ _
  · have fh : Outside B 48 16 s.mem u.mem := by
      rw [hm]
      exact ((writeW_outside _ B _ (d := 48) (by decide)).mono (by decide) (by decide)).trans
        ((writeW_outside _ B _ (d := 56) (by decide)).mono (by decide) (by decide))
    have fhv : Outside B 48 80 s.mem v.mem :=
      (fh.mono (by decide) (by decide)).trans (fv.mono (by decide) (by decide))
    exact (Frm.of_outside fhv (by simp)).trans (Frm.of_outside ft (by simp))

end VG.Proof.Dsa.X86_64.ProbablePrime
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.X86_64.Spill VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.ProbablePrime VG.Impl.Dsa.Generation.Layout
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin.X86_64
open VG.Proof.Dsa.X86_64.Generation (PrimeParams PrimeArguments primeExtras primeRanges)
open VG.Impl.Bignum.X86_64 (seqs)

/-- The body of the function, inside its frame. -/
abbrev body (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) : Prog isa :=
  .seq setup
    (seqs [Impl.Dsa.X86_64.Generation.primeBytes mul round, .block exit, .block restoreRegisters])

/-- The memory the test may change. -/
def changed (bits : Nat) (s : State) : List Region :=
  [⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩, ⟨off (s.gpr .rdi) witness, len bits⟩,
    below (frameSp s) 128, ⟨frameSp s, 56⟩, ⟨s.gpr .r8, 8⟩]

/-- The test's result as the function returns it. -/
def BodyPost (bits : Nat) (s t : State) : Prop :=
  let res := Spec.Dsa.probablePrime (candidateOf bits s)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  t.gpr .rax = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status res) ∧
  (∀ b rest, res = some (b, rest) →
    t.mem.readW (s.gpr .r8) 64 = BitVec.ofNat 64 ((s.gpr .rcx).toNat - rest.length)) ∧
  Frame (changed bits s) s.mem t.mem ∧
  (∀ r ∈ spillSlots.map Prod.fst, t.gpr r = s.gpr r)

/-- What the test has set up when the shared prime test starts. -/
structure Ready {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) (u : State) : Prop where
  args : PrimeArguments (params hb A) 0 0 u
  ptr : word u.mem (params hb A).B 160 = off (s.gpr .rdi) (candidate bits)
  src : Src u (params hb A).B (params hb A).Z (off (s.gpr .rdi) (candidate bits))
    (Spec.Rsa.bytesAt s.mem (off (s.gpr .rdi) (candidate bits)) (len bits))
  saved : Saved u.mem (frameSp s) s.gpr spillSlots
  used : word u.mem (frameSp s) 48 = s.gpr .r8
  frame : Frame [⟨frameSp s, 56⟩, ⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩] s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = (allocState 56 s).wr

theorem prep_ok {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) :
    WP isa setup (allocState 56 s) (Ready hb A) := by
  have hsize : domainCheck ≤ (s.gpr .rsi).toNat * 8 := by have := A.size; omega
  have hws : wsRegion s ∈ s.wr := by rw [A.wr]; exact List.mem_cons_self
  have hS0 : Scr (allocState 56 s) (s.gpr .rdi) ((s.gpr .rsi).toNat * 8) :=
    Scr.of_mem (List.mem_cons_of_mem _ hws) A.wsBound
  have hF : (allocState 56 s).gpr .rsp = frameSp s := rfl
  have hFw : (⟨frameSp s, 56⟩ : Region) ∈ (allocState 56 s).wr := List.mem_cons_self
  have hFn : (frameSp s).toNat + 56 ≤ 2 ^ 64 := by
    have : 184 ≤ (s.gpr .rsp).toNat := A.stackLower
    change (s.gpr .rsp - BitVec.ofNat 64 56).toNat + 56 ≤ 2 ^ 64
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega)]
    have := (s.gpr .rsp).isLt
    simp only [BitVec.toNat_ofNat]
    omega
  have hg0 : ∀ r, r ≠ .rsp → (allocState 56 s).gpr r = s.gpr r := fun r h => by
    simp [allocState, State.setReg, h]
  -- Regions of the frame and of `ws` are disjoint.
  have fws : ∀ {d n e k : Nat}, d + n ≤ 56 → e + k ≤ domainCheck →
      Region.Disjoint ⟨off (frameSp s) d, n⟩ ⟨off (s.gpr .rdi) e, k⟩ := fun h h' =>
    (A.stackWs.sub_left (frame_stack_sub s h)).sub_right (ws_sub A h')
  simp only [setup, seqs]
  -- Save the callee-saved registers.
  refine WP.seq (WP.mono (save_ok (s := allocState 56 s) (by rw [hF]; exact hFw)) ?_)
  rintro u1 ⟨g1, r1, w1, sv1, f1⟩
  -- `used` in the frame; the arithmetic workspace in `rdi`.
  have hF1 : Scr u1 (u1.gpr .rsp) 56 := by
    rw [g1, hF]; exact Scr.of_mem (by rw [w1]; exact hFw) hFn
  refine WP.seq (WP.mono (entry_ok hF1) ?_)
  rintro u2 ⟨di2, si2, r92, r82, m2, k2⟩
  have h82 : u2.gpr .r8 = BitVec.ofNat 64 bits := by rw [r82, g1, hg0 _ (by decide)]; exact A.width
  refine WP.seq (WP.mono (sizeWords_ok hb h82) ?_)
  rintro u2' ⟨h12, r82', m2', k2'⟩
  have hdi2' : u2'.gpr .rdi = u2.gpr .rdi := k2'.gpr (by decide)
  have w2 : u2.wr = (allocState 56 s).wr := k2.2.2.trans w1
  have hS2 : Scr u2 (params hb A).B (params hb A).Z :=
    (hS0.congr w2).sub (o := arithmetic) (n := arithmeticBytes)
      (by have : arithmetic + arithmeticBytes = domainCheck := rfl; omega) (by decide)
  have hdi2 : u2.gpr .rdi = (params hb A).B := by
    rw [di2, g1, hg0 _ (by decide)]; rfl
  refine WP.seq (WP.mono (sizedWorkspace_ok (hS2.congr k2'.2.2) (hdi2'.trans hdi2) h12
    (by change _ ≤ arithmeticBytes; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by change 2 ≤ words bits; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by change words bits < _; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)) ?_)
  rintro u3 ⟨_, gd3, f3, k3⟩
  have hB3 : Scr u3 (params hb A).B 256 := by
    simpa only [off, BitVec.add_zero] using gd3.scr.sub (o := 0) (n := 256)
      (by change 0 + 256 ≤ arithmeticBytes; decide) (by decide)
  refine WP.mono (args_ok hb hB3 gd3.rdi ((k3.gpr (by decide)).trans (r82'.trans h82))) ?_
  rintro u4 ⟨m4, k4⟩
  -- Registers.
  have hrsi : u3.gpr .rsi = s.gpr .rdi := by
    rw [k3.gpr (by decide), k2'.gpr (by decide), si2, g1, hg0 _ (by decide)]
  have hr9 : u3.gpr .r9 = s.gpr .rdx := by
    rw [k3.gpr (by decide), k2'.gpr (by decide), r92, g1, hg0 _ (by decide)]
  have hrcx : u3.gpr .rcx = s.gpr .rcx := by
    rw [k3.gpr (by decide), k2'.gpr (by decide), k2.gpr (by decide), g1, hg0 _ (by decide)]
  have hrsp : u4.gpr .rsp = frameSp s := by
    rw [k4.gpr (by decide), k3.gpr (by decide), k2'.gpr (by decide), k2.gpr (by decide), g1, hF]
  have rd4 : u4.rd = s.rd := k4.2.1.trans (k3.2.1.trans (k2'.2.1.trans (k2.2.1.trans r1)))
  have wr4 : u4.wr = (allocState 56 s).wr := k4.2.2.trans (k3.2.2.trans (k2'.2.2.trans w2))
  -- Memory.
  have ho : Outside (params hb A).B 128 128 u3.mem u4.mem := by
    rw [m4]; exact VG.Proof.Dsa.X86_64.Generation.argumentWrites_outside _ _ _ _ (argList_fits hb.le.2)
  have F12 : Frame [⟨off (frameSp s) 48, 8⟩] u1.mem u2.mem := by
    rw [m2, g1, hF]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have F23 : Frame [⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩] u2.mem u3.mem :=
    VG.Proof.Dsa.X86_64.Generation.prime_global_frame (extra := []) (m2' ▸ f3.work) (by decide)
  have F34 : Frame [⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩] u3.mem u4.mem :=
    VG.Proof.Dsa.X86_64.Generation.prime_global_frame (extra := [])
      (Frm.of_outside (rs := [(128, 128)]) ho List.mem_cons_self).work (by decide)
  have F14 : Frame [⟨off (frameSp s) 48, 8⟩, ⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩] u1.mem u4.mem :=
    (F12.mono (by simp)).trans ((F23.mono (by simp)).trans (F34.mono (by simp)))
  have F04 : Frame [⟨frameSp s, 56⟩, ⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩] s.mem u4.mem := by
    have F01 : Frame [⟨frameSp s, 56⟩] s.mem u1.mem :=
      Frame.sub f1 fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
    refine (F01.mono (by simp)).trans (Frame.sub F14 fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  have wh (k : Nat) (hk32 : k < 32) : word u4.mem (params hb A).B (8 * k) =
      VG.Proof.Dsa.X86_64.Generation.argumentWords (argWords u3)
        (fun j => word u3.mem (params hb A).B (8 * j)) (argList bits) k := by
    rw [m4]; exact VG.Proof.Dsa.X86_64.Generation.argumentWrites_word _ _ _ _ (argList_fits hb.le.2) hk32
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have hcand : candidate bits + len bits ≤ witness := by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  -- The candidate's and the tape's bytes are outside the frame and the workspace.
  have candOut : ∀ i < len bits, ∀ r ∈ [(⟨frameSp s, 56⟩ : Region),
      ⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩],
      ¬ r.Contains (off (s.gpr .rdi) (candidate bits) + BitVec.ofNat 64 i) 1 := by
    intro i hi r hr hc
    have hb' := contains_byte (off (s.gpr .rdi) (candidate bits)) hi (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := fws (d := 0) (n := 56) (e := candidate bits) (k := len bits) (by decide)
        (by have : witness ≤ domainCheck := (by decide); omega)
      simp only [off, BitVec.add_zero] at this
      exact this _ hc hb'
    · exact Offset.disjoint (s.gpr .rdi) (d := candidate bits) (n := len bits) (e := arithmetic)
        (k := arithmeticBytes) (Or.inl (by have : witness ≤ arithmetic := (by decide); omega))
        (by have : witness < 2 ^ 64 := (by decide); omega) (by decide) _ hb' hc
  have randOut : ∀ i < (s.gpr .rcx).toNat, ∀ r ∈ [(⟨frameSp s, 56⟩ : Region),
      ⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩],
      ¬ r.Contains (s.gpr .rdx + BitVec.ofNat 64 i) 1 := by
    intro i hi r hr hc
    have hb' := contains_byte (s.gpr .rdx) hi (by have := A.randBound; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hs := frame_stack_sub s (d := 0) (n := 56) (by decide)
      simp only [off, BitVec.add_zero] at hs
      exact A.stackRand _ (hs _ hc) hb'
    · exact A.wsRand _ (ws_sub A (by decide) _ hc) hb'
  refine ⟨⟨⟨gd3.scr.congr k4.2.2, (k4.gpr (by decide)).trans gd3.rdi,
      gd3.hdr.of_frm (Frm.of_outside (rs := [(128, 128)]) ho List.mem_cons_self) (by simp)⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, F04, rd4, wr4⟩
  · rw [wh kOut (by decide)]
    simp only [argList, VG.Proof.Dsa.X86_64.Generation.argumentWords,
      VG.Proof.Dsa.X86_64.Generation.argumentValue, argWords, kOut, kLen, kUsedP, kChecks, kE,
      kRand, kRandLen, kUsed, VG.Impl.Bignum.sFn, Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, hrsi]
    rfl
  · rw [wh kUsedP (by decide)]; rfl
  · rw [wh kLen (by decide)]; rfl
  · rw [wh kRand (by decide)]
    simp only [argList, VG.Proof.Dsa.X86_64.Generation.argumentWords,
      VG.Proof.Dsa.X86_64.Generation.argumentValue, argWords, kOut, kLen, kUsedP, kChecks, kE,
      kRand, kRandLen, kUsed, VG.Impl.Bignum.sFn, Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false,
      hr9, BitVec.add_zero, Nat.one_ne_zero]
    rfl
  · rw [wh kRandLen (by decide)]
    simp only [argList, VG.Proof.Dsa.X86_64.Generation.argumentWords,
      VG.Proof.Dsa.X86_64.Generation.argumentValue, argWords, kOut, kLen, kUsedP, kChecks, kE,
      kRand, kRandLen, kUsed, VG.Impl.Bignum.sFn, Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false,
      hrcx, BitVec.add_zero]
    change s.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).length
    rw [bytesAt_length, ofNat_toNat64]
  · rw [wh kUsed (by decide)]; rfl
  · rw [wh kChecks (by decide)]; rfl
  · change Src u4 (off (s.gpr .rdi) arithmetic) arithmeticBytes (s.gpr .rdx)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [bytesAt_length] at hi
      refine ⟨_, List.mem_append_left _ (by rw [rd4, A.rd]; exact List.mem_cons_self), ?_⟩
      exact contains_byte _ hi (by have := A.randBound; omega)
    · have hi' : i < (s.gpr .rcx).toNat := by rw [bytesAt_length] at hi; exact hi
      rw [F04 _ (randOut i hi')]
      simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
    · have hi' : i < (s.gpr .rcx).toNat := by rw [bytesAt_length] at hi; exact hi
      exact out_scr ((A.wsRand.symm).sub_right (ws_sub A (by decide)))
        (contains_byte _ hi' (by have := A.randBound; omega))
  · change ∀ i < len bits, InRegions u4.wr (off (off (s.gpr .rdi) witness) i) 1
    intro i hi
    refine ⟨_, by rw [wr4]; exact List.mem_cons_of_mem _ hws, ?_⟩
    change (wsRegion s).Contains (off (off (s.gpr .rdi) witness) i) 1
    rw [show off (off (s.gpr .rdi) witness) i = off (s.gpr .rdi) (witness + i) by
      simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
    exact Offset.contains_base _ (by have : witness + 384 ≤ domainCheck := (by decide); omega)
      (by have : witness + 384 < 2 ^ 64 := (by decide); omega)
  · exact hrsp
  · rw [wh 20 (by decide)]
    simp only [argList, VG.Proof.Dsa.X86_64.Generation.argumentWords,
      VG.Proof.Dsa.X86_64.Generation.argumentValue, argWords, kOut, kLen, kUsedP, kChecks, kE,
      kRand, kRandLen, kUsed, VG.Impl.Bignum.sFn, Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, hrsi]
  · change Src u4 (off (s.gpr .rdi) arithmetic) arithmeticBytes (off (s.gpr .rdi) (candidate bits))
      (Spec.Rsa.bytesAt s.mem (off (s.gpr .rdi) (candidate bits)) (len bits))
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [bytesAt_length] at hi
      refine ⟨_, List.mem_append_right _ (by rw [wr4]; exact List.mem_cons_of_mem _ hws), ?_⟩
      rw [show off (s.gpr .rdi) (candidate bits) + BitVec.ofNat 64 i = off (s.gpr .rdi) (candidate bits + i) by
        simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
      exact Offset.contains_base _ (by have : witness ≤ domainCheck := (by decide); omega)
        (by have : witness < 2 ^ 64 := (by decide); omega)
    · have hi' : i < len bits := by rw [bytesAt_length] at hi; exact hi
      rw [F04 _ (candOut i hi')]
      simp only [bytesAt_eq, List.getElem_map, List.getElem_range]
    · have hi' : i < len bits := by rw [bytesAt_length] at hi; exact hi
      refine out_scr (r := ⟨off (s.gpr .rdi) (candidate bits), len bits⟩) ?_
        (contains_byte _ hi' (by omega))
      exact Offset.disjoint (s.gpr .rdi) (Or.inl (by have : witness ≤ arithmetic := (by decide); omega))
        (by have : witness < 2 ^ 64 := (by decide); omega) (by decide)
  · intro p hp
    have hne : p.1 ≠ .rsp := by revert p; decide
    have hp48 : ∀ q ∈ spillSlots, q.2 + 8 ≤ 48 := by decide
    rw [← hg0 _ hne, ← sv1 p hp, hF]
    exact F14.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (Or.inl (hp48 p hp)) (by have := hp48 p hp; omega) (by decide)
      · exact fws (by have := hp48 p hp; omega) (by decide)) (by decide)
  · have h2 : word u2.mem (frameSp s) 48 = s.gpr .r8 := by
      rw [m2, g1, hF, hg0 _ (by decide)]; exact word_writeW_self _ _ _ _
    rw [← h2]
    exact (F23.trans F34).readW (Region.contains_self _ _)
      (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact fws (by decide) (by decide)) (by decide)

/-- What the test leaves. -/
structure Tested {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) (u : State) : Prop where
  input : ∃ mi' used', VG.Proof.Dsa.X86_64.Generation.PrimeInput (params hb A) mi' used' u ∧
    used' ≤ (params hb A).rand.length ∧
    (Spec.Dsa.probablePrime (params hb A).N ((params hb A).rand.drop 0) = none →
      word u.mem (params hb A).B (8 * kStat) = BitVec.ofNat 64 0) ∧
    (∀ b rest, Spec.Dsa.probablePrime (params hb A).N ((params hb A).rand.drop 0) = some (b, rest) →
      word u.mem (params hb A).B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
      used' = (params hb A).rand.length - rest.length)
  saved : Saved u.mem (frameSp s) s.gpr spillSlots
  used : word u.mem (frameSp s) 48 = s.gpr .r8
  frame : Frame [⟨frameSp s, 56⟩, ⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩,
    ⟨off (s.gpr .rdi) witness, len bits⟩, below (frameSp s) 128] s.mem u.mem
  rd : u.rd = s.rd
  wr : u.wr = (allocState 56 s).wr

theorem test_ok (M : Mont) (K : Kernel) {bits : Nat} (hb : Supported bits) {s : State}
    (A : PrimeABI bits s) {u4 : State} (R : Ready hb A u4) :
    WP isa (Impl.Dsa.X86_64.Generation.primeBytes M.mm K.run) u4 (Tested hb A) := by
  have fws : ∀ {d n e k : Nat}, d + n ≤ 56 → e + k ≤ domainCheck →
      Region.Disjoint ⟨off (frameSp s) d, n⟩ ⟨off (s.gpr .rdi) e, k⟩ := fun h h' =>
    (A.stackWs.sub_left (frame_stack_sub s h)).sub_right (ws_sub A h')
  have fused : ∀ {d n : Nat}, d + n ≤ 56 →
      Region.Disjoint ⟨off (frameSp s) d, n⟩ ⟨s.gpr .r8, 8⟩ := fun h =>
    A.stackUsed.sub_left (frame_stack_sub s h)
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have hw : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  -- The test.
  have hlow := ((bitLength_iff_bounds (by have := hb.le; omega)).mp A.bits).1
  refine WP.mono (VG.Proof.Dsa.X86_64.Generation.primeBytes_ok M K R.args R.ptr
    (bytesAt_length _ _ _) rfl R.src (Nat.zero_le _) hw
    (by change Bignum.slot (words bits) aTab + 2048 ≤ arithmeticBytes
        rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      change 8161 < candidateOf bits s
      have h2 : 2 ^ 159 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by have := hb.le; omega)
      have : (8161 : Nat) < 2 ^ 159 := by decide
      exact Nat.lt_of_lt_of_le this (Nat.le_trans h2 hlow))
    (by
      change 1024 < Spec.Dsa.bitLength (candidateOf bits s) ↔ 16 < words bits
      rw [A.bits]; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by
      change checks bits = Spec.Dsa.primeChecks (Spec.Dsa.bitLength (candidateOf bits s))
      rw [A.bits]; rfl)) ?_
  rintro u5 ⟨mi', used', inp, hub, hnone, hsome, wf5, k5⟩
  have F45 : Frame [⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩, ⟨off (s.gpr .rdi) witness, len bits⟩,
      below (frameSp s) 128] u4.mem u5.mem :=
    VG.Proof.Dsa.X86_64.Generation.prime_global_frame wf5 (fun r hr =>
      VG.Proof.Dsa.X86_64.Generation.checkPrimeRanges_bound hw r
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
  have frameOut : ∀ {d n : Nat}, d + n ≤ 56 → ∀ r ∈ [(⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩ : Region),
      ⟨off (s.gpr .rdi) witness, len bits⟩, below (frameSp s) 128],
      Region.Disjoint ⟨off (frameSp s) d, n⟩ r := by
    intro d n h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact fws h (by decide)
    · exact fws h (by have : witness + 384 ≤ domainCheck := (by decide); omega)
    · exact Offset.disjoint_below _ (by omega)
  have hp48 : ∀ q ∈ spillSlots, q.2 + 8 ≤ 48 := by decide
  refine ⟨⟨mi', used', inp, hub, hnone, hsome⟩,
    R.saved.frame F45 fun p hp r hr => frameOut (by have := hp48 p hp; omega) r hr,
    by rw [← R.used]; exact F45.readW (Region.contains_self _ _) (frameOut (by decide)) (by decide),
    ?_, k5.2.1.trans R.rd, k5.2.2.trans R.wr⟩
  refine (Frame.sub R.frame ?_).trans (Frame.sub F45 ?_)
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · intro r hr
    exact ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩

theorem finish_ok {bits : Nat} (hb : Supported bits) {s : State}
    (A : PrimeABI bits s) {u5 : State} (T : Tested hb A u5) :
    WP isa (.seq (.block exit) (.block restoreRegisters)) u5 fun t =>
      t.gpr .rsp = (allocState 56 s).gpr .rsp ∧ t.wr = (allocState 56 s).wr ∧ t.rd = s.rd ∧
      BodyPost bits s t := by
  have fws : ∀ {d n e k : Nat}, d + n ≤ 56 → e + k ≤ domainCheck →
      Region.Disjoint ⟨off (frameSp s) d, n⟩ ⟨off (s.gpr .rdi) e, k⟩ := fun h h' =>
    (A.stackWs.sub_left (frame_stack_sub s h)).sub_right (ws_sub A h')
  have fused : ∀ {d n : Nat}, d + n ≤ 56 →
      Region.Disjoint ⟨off (frameSp s) d, n⟩ ⟨s.gpr .r8, 8⟩ := fun h =>
    A.stackUsed.sub_left (frame_stack_sub s h)
  have hlen : len bits ≤ 384 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have hw : words bits ≤ 48 := by rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have frameOut : ∀ {d n : Nat}, d + n ≤ 56 → ∀ r ∈ [(⟨off (s.gpr .rdi) arithmetic, arithmeticBytes⟩ : Region),
      ⟨off (s.gpr .rdi) witness, len bits⟩, below (frameSp s) 128],
      Region.Disjoint ⟨off (frameSp s) d, n⟩ r := by
    intro d n h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact fws h (by decide)
    · exact fws h (by have : witness + 384 ≤ domainCheck := (by decide); omega)
    · exact Offset.disjoint_below _ (by omega)
  obtain ⟨⟨mi', used', inp, hub, hnone, hsome⟩, sv5, hu5, F05, rd5, wr5⟩ := T
  have hsp5 : u5.gpr .rsp = frameSp s := inp.stack
  -- The exit.
  have hU : (⟨s.gpr .r8, 8⟩ : Region) ∈ s.wr := by rw [A.wr]; simp
  refine WP.seq (WP.mono (exit_ok (U := s.gpr .r8) inp.good.rdi
    (inp.good.scr.ld (d := 200) (by change _ ≤ arithmeticBytes; decide))
    (inp.good.scr.ld (d := 232) (by change _ ≤ arithmeticBytes; decide))
    ⟨_, List.mem_append_right _ (by rw [wr5]; exact List.mem_cons_self),
      by rw [hsp5]; exact Offset.contains_base _ (by decide) (by decide)⟩
    (by rw [hsp5]; exact hu5)
    ⟨⟨s.gpr .r8, 8⟩, by rw [wr5]; exact List.mem_cons_of_mem _ hU, Region.contains_self _ _⟩
    (by
      have h := (A.wsUsed.sub_left (ws_sub A (d := arithmetic + 232) (n := 8) (by decide)))
      rw [show off (s.gpr .rdi) (arithmetic + 232) = off (params hb A).B 232 by
        simp only [params, off, BitVec.add_assoc, BitVec.ofNat_add]] at h
      exact fun x h₁ h₂ => h x h₁ h₂)) ?_)
  rintro u6 ⟨rax6, m6, k6⟩
  have F56 : Frame [⟨s.gpr .r8, 8⟩] u5.mem u6.mem := by
    rw [m6]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have hsp6 : u6.gpr .rsp = frameSp s := (k6.gpr (by decide)).trans hsp5
  have wr6 : u6.wr = (allocState 56 s).wr := k6.2.2.trans wr5
  have hp48 : ∀ q ∈ spillSlots, q.2 + 8 ≤ 48 := by decide
  have sv6 : Saved u6.mem (u6.gpr .rsp) s.gpr spillSlots := by
    rw [hsp6]
    refine sv5.frame F56 ?_
    intro p hp r hr
    obtain rfl := List.mem_singleton.mp hr
    exact fused (by have := hp48 p hp; omega)
  -- Restore the callee-saved registers.
  refine WP.mono (restore_ok s.gpr (by rw [hsp6, wr6]; exact List.mem_cons_self) sv6) ?_
  rintro u7 ⟨g7, k7, m7, rd7, wr7⟩
  refine ⟨by rw [k7 _ (by decide), hsp6]; rfl, wr7.trans wr6, rd7.trans (k6.2.1.trans rd5),
    ?_, ?_, ?_, g7⟩
  · rw [k7 _ (by decide), rax6]
    change returned (word u5.mem (params hb A).B (8 * kStat)) = BitVec.ofNat 64
      (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime (params hb A).N (List.drop 0 (params hb A).rand)))
    cases h : Spec.Dsa.probablePrime (params hb A).N (List.drop 0 (params hb A).rand) with
    | none => rw [hnone h]; decide
    | some r =>
      obtain ⟨b, rest⟩ := r
      rw [(hsome b rest h).1]
      cases b <;> simp only [Proof.Dsa.ProbablePrime.status] <;> decide
  · intro b rest h
    have h' : Spec.Dsa.probablePrime (params hb A).N (List.drop 0 (params hb A).rand) = some (b, rest) := h
    rw [m7, m6, Mem.readW_writeW_self64]
    change word u5.mem (params hb A).B (8 * kUsed) = _
    rw [inp.used, (hsome b rest h').2]
    change BitVec.ofNat 64 ((Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat).length - rest.length) = _
    rw [bytesAt_length]
  · rw [m7]
    refine (Frame.sub F05 ?_).trans (Frame.sub F56 ?_)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp [changed], fun _ h => h⟩
      · exact ⟨_, by simp [changed], fun _ h => h⟩
      · exact ⟨_, by simp [changed], fun _ h => h⟩
      · exact ⟨_, by simp [changed], fun _ h => h⟩
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp [changed], fun _ h => h⟩


theorem body_ok (M : Mont) (K : Kernel) {bits : Nat} (hb : Supported bits) {s : State}
    (A : PrimeABI bits s) :
    WP isa (body M.mm K.run) (allocState 56 s) fun t =>
      t.gpr .rsp = (allocState 56 s).gpr .rsp ∧ t.wr = (allocState 56 s).wr ∧ t.rd = s.rd ∧
      BodyPost bits s t :=
  WP.seq (WP.mono (prep_ok hb A) fun _ R =>
    WP.seq (WP.mono (test_ok M K hb A R) fun _ T => finish_ok hb A T))

end VG.Proof.Dsa.X86_64.ProbablePrime
