module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Front
import Mathlib.Tactic.Set
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: retained candidate inputs -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.Ffdh.X86_64

structure CandidateP where
  B : Addr
  Z : Nat
  k : Nat
  bits : Nat
  gen : Nat
  op : Addr
  up : Addr
  rp : Addr
  rand : List Byte
  sp : Addr

def CandidateP.prefix (p : CandidateP) : List Byte := p.rand.take p.k
def CandidateP.P (p : CandidateP) : Nat := Spec.Ffdh.candidateOf p.bits (Spec.Rsa.os2ip p.prefix)
def CandidateP.Q (p : CandidateP) : Nat := (p.P - 1) / 2

def CandidateP.headers (p : CandidateP) : List (Nat × BitVec 64) :=
  [(oOut, p.op), (oLen, BitVec.ofNat 64 p.k), (oUsedP, p.up),
    (oBits, BitVec.ofNat 64 p.bits), (oGen, BitVec.ofNat 64 p.gen), (oRandStart, p.rp)]

def CandidateFrame (p : CandidateP) (m m' : Mem) : Prop :=
  ∀ a, p.Z ≤ ofs p.B a → (∀ i < p.k, a ≠ off p.op i) →
    ¬(below p.sp 128).Contains a 1 → m' a = m a

theorem CandidateFrame.refl (p : CandidateP) (m : Mem) : CandidateFrame p m m := fun _ _ _ _ => rfl

theorem CandidateFrame.trans {p : CandidateP} {m₁ m₂ m₃ : Mem}
    (h : CandidateFrame p m₁ m₂) (h' : CandidateFrame p m₂ m₃) : CandidateFrame p m₁ m₃ :=
  fun a ha ho hb => (h' a ha ho hb).trans (h a ha ho hb)

theorem CandidateFrame.of_scr {p : CandidateP} {m m' : Mem} (h : InScr p.B p.Z m m') :
    CandidateFrame p m m' := fun a ha _ _ => h a ha

theorem CandidateFrame.of_bytes {p : CandidateP} {m m' : Mem}
    (h : ∀ a, (∀ i < p.k, a ≠ off p.op i) → m' a = m a) : CandidateFrame p m m' :=
  fun a _ ho _ => h a ho

def CandidateSaved (p : CandidateP) (m m' : Mem) : Prop :=
  ∀ j < 12, word m' p.B (8 * j) = word m p.B (8 * j)

theorem CandidateSaved.refl (p : CandidateP) (m : Mem) : CandidateSaved p m m := fun _ _ => rfl

theorem CandidateSaved.trans {p : CandidateP} {m₁ m₂ m₃ : Mem}
    (h : CandidateSaved p m₁ m₂) (h' : CandidateSaved p m₂ m₃) : CandidateSaved p m₁ m₃ :=
  fun j hj => (h' j hj).trans (h j hj)

structure CandidateBase (p : CandidateP) (s : State) : Prop where
  bits1 : 512 ≤ p.bits
  bits2 : p.bits ≤ 8192
  len : p.k = (p.bits + 7) / 8
  gen : p.gen = 2 ∨ p.gen = 5
  randLen : p.rand.length < 2 ^ 64
  room : 128 * p.k + 256 ≤ p.Z
  scr : Scr s p.B p.Z
  out : OutOk s p.B p.Z p.op p.k
  used : Scr s p.up 8
  usedOut : OutOk s p.B p.Z p.up 8
  rand : Src s p.B p.Z p.rp p.rand
  outRand : Apart p.op p.k p.rp p.rand.length
  outUsed : Apart p.op p.k p.up 8
  sp : s.gpr .rsp = p.sp
  stackSize : 128 ≤ p.sp.toNat
  stackRoot : Region.Disjoint ⟨p.B, p.Z⟩ (below p.sp 128)
  stackRand : ∀ i < p.rand.length, ¬(below p.sp 128).Contains (off p.rp i) 1
  hdr : Slots s.mem p.B p.headers

theorem CandidateBase.widths {p : CandidateP} {s : State} (h : CandidateBase p s) : 64 ≤ p.k ∧ p.k ≤ 1024 := by
  omega_using [h.bits1, h.bits2, h.len]

theorem CandidateBase.header_room {p : CandidateP} {s : State} (h : CandidateBase p s) : 256 ≤ p.Z := by
  omega_using [h.room]

theorem CandidateBase.size64 {p : CandidateP} {s : State} (h : CandidateBase p s) : p.Z ≤ 2 ^ 64 :=
  Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap

theorem CandidateBase.inner_changes {p : CandidateP} {s t : State} {rs : List (Nat × Nat)}
    (h : CandidateBase p s) (hf : Frm (off p.B 256) rs s.mem t.mem)
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z - 256) : InScr p.B p.Z s.mem t.mem := by
  have hf' := hf.rebase (by decide : 256 < 2 ^ 64) (fun r hr => by
    have hb := hrs r hr
    omega_using [hb, h.size64])
  apply InScr.of_frm hf'
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  have hb := hrs r' hr'
  dsimp only
  omega_using [hb, h.header_room]

theorem CandidateBase.inner_header {p : CandidateP} {s t : State} {rs : List (Nat × Nat)}
    (h : CandidateBase p s) (hf : Frm (off p.B 256) rs s.mem t.mem)
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z - 256) :
    ∀ j < 32, word t.mem p.B (8 * j) = word s.mem p.B (8 * j) := by
  intro j hj
  exact hf.word_below hrs (by omega_using [h.header_room, h.size64]) (by decide) (by omega)

theorem CandidateBase.output_eq {p : CandidateP} {s : State} {m' : Mem}
    (h : CandidateBase p s) (hf : InScr p.B p.Z s.mem m') :
    Spec.Rsa.bytesAt m' p.op p.k = Spec.Rsa.bytesAt s.mem p.op p.k := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf _ (h.out.sep i (List.mem_range.mp hi))

theorem CandidateBase.keep {p : CandidateP} {s t : State} {regs : List Reg}
    (h : CandidateBase p s) (hf : CandidateFrame p s.mem t.mem) (hs : CandidateSaved p s.mem t.mem)
    (k : Keep regs s t) (hsp : t.gpr .rsp = p.sp) : CandidateBase p t := by
  refine ⟨h.bits1, h.bits2, h.len, h.gen, h.randLen, h.room, h.scr.congr k.2.2,
    ⟨fun i hi => by rw [k.2.2]; exact h.out.wr i hi, h.out.sep⟩, h.used.congr k.2.2,
    ⟨fun i hi => by rw [k.2.2]; exact h.usedOut.wr i hi, h.usedOut.sep⟩,
    ⟨?_, ?_, h.rand.out⟩, h.outRand, h.outUsed, hsp, h.stackSize, h.stackRoot, h.stackRand, ?_⟩
  · intro i hi; rw [k.2.1, k.2.2]; exact h.rand.rd i hi
  · intro i hi
    rw [hf _ (h.rand.out i hi) (fun j hj he => h.outRand j hj i hi he.symm) (h.stackRand i hi)]
    exact h.rand.val i hi
  · intro e he
    have hi : e.1 < 12 := by
      simp only [CandidateP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
    exact (hs e.1 hi).trans (h.hdr e he)

/-- The outer tape counters at any candidate phase boundary. -/
structure CandidateTape (p : CandidateP) (used : Nat) (s : State) : Prop where
  base : CandidateBase p s
  bound : used ≤ p.rand.length
  ptr : word s.mem p.B (8 * oRandPtr) = off p.rp used
  left : word s.mem p.B (8 * oRandLeft) = BitVec.ofNat 64 (p.rand.length - used)
  usedWord : word s.mem p.B (8 * oUsed) = BitVec.ofNat 64 used

theorem CandidateTape.keep {p : CandidateP} {used : Nat} {s t : State} {regs : List Reg}
    (h : CandidateTape p used s) (hf : CandidateFrame p s.mem t.mem)
    (hh : ∀ j < 15, word t.mem p.B (8 * j) = word s.mem p.B (8 * j))
    (k : Keep regs s t) (hsp : t.gpr .rsp = p.sp) : CandidateTape p used t :=
  ⟨h.base.keep hf (fun j hj => hh j (by omega)) k hsp, h.bound,
    (hh _ (by decide)).trans h.ptr, (hh _ (by decide)).trans h.left, (hh _ (by decide)).trans h.usedWord⟩

theorem CandidateTape.keep_inner {p : CandidateP} {used : Nat} {s t : State} {regs : List Reg}
    {rs : List (Nat × Nat)} (h : CandidateTape p used s) (hf : Frm (off p.B 256) rs s.mem t.mem)
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z - 256) (k : Keep regs s t) (hsp : .rsp ∉ regs) : CandidateTape p used t :=
  h.keep (CandidateFrame.of_scr (h.base.inner_changes hf hrs))
    (fun j hj => h.base.inner_header hf hrs j (by omega)) k ((k.gpr hsp).trans h.base.sp)

theorem CandidateTape.after_bytes {p : CandidateP} {used : Nat} {s t : State} {regs : List Reg}
    (h : CandidateTape p used s)
    (hf : ∀ a, (∀ i < p.k, a ≠ off p.op i) → t.mem a = s.mem a)
    (k : Keep regs s t) (hrsp : .rsp ∉ regs) :
    CandidateTape p used t ∧ CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem := by
  have hw := words_outside_bytes h.base.size64 hf h.base.out.sep
  have hh : ∀ j < 15, word t.mem p.B (8 * j) = word s.mem p.B (8 * j) :=
    fun j hj => hw _ (by omega_using [hj, h.base.header_room])
  exact ⟨h.keep (CandidateFrame.of_bytes hf) hh k ((k.gpr hrsp).trans h.base.sp),
    fun j hj => hh j (by omega), CandidateFrame.of_bytes hf⟩

theorem CandidateTape.same_mem {p : CandidateP} {used : Nat} {s t : State} {regs : List Reg}
    (h : CandidateTape p used s) (hm : t.mem = s.mem) (k : Keep regs s t) (hsp : .rsp ∉ regs) :
    CandidateTape p used t ∧ CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem := by
  have hf : CandidateFrame p s.mem t.mem := by rw [hm]; exact CandidateFrame.refl _ _
  have hh : ∀ j < 15, word t.mem p.B (8 * j) = word s.mem p.B (8 * j) := fun _ _ => by rw [hm]
  exact ⟨h.keep hf hh k ((k.gpr hsp).trans h.base.sp), fun j hj => hh j (by omega), hf⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
