module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Bignum.WorkFrame
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerPre
public import VerifiedGarbage.Proof.RsaKeyGen.Slots

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: the shared round's stack footprint -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin VG.Proof.MillerRabin.X86_64

structure RoundRoom (p : WitnessParams) (rp : Addr) (bs : List Byte) (s : State) : Prop where
  size : 128 ≤ (s.gpr .rsp).toNat
  root : Region.Disjoint ⟨p.O, p.Z⟩ (below (s.gpr .rsp) 128)
  rand : ∀ i < bs.length, ¬(below (s.gpr .rsp) 128).Contains (off rp i) 1

theorem RoundRoom.call {p : WitnessParams} {rp : Addr} {bs : List Byte} {s : State}
    (h : RoundRoom p rp bs s) : Caller.Room s p.I p.IZ :=
  ⟨h.size, h.root.sub_left (Offset.sub_base p.O (by omega_using [p.space_bounds.2.2]))⟩

theorem RoundRoom.congr {p : WitnessParams} {rp : Addr} {bs : List Byte} {s t : State}
    (h : RoundRoom p rp bs s) (hsp : t.gpr .rsp = s.gpr .rsp) : RoundRoom p rp bs t :=
  ⟨by rw [hsp]; exact h.size, by rw [hsp]; exact h.root, by rw [hsp]; exact h.rand⟩

theorem RoundRoom.after_draw {p : WitnessParams} {rp : Addr} {bs : List Byte} {s t : State}
    {regs : List Reg} (h : RoundRoom p rp bs s) (k : Keep regs s t) (hsp : .rsp ∉ regs) (n : Nat) :
    RoundRoom p (off rp n) (bs.drop n) t := by
  have hs := k.gpr hsp
  refine ⟨by rw [hs]; exact h.size, by rw [hs]; exact h.root, ?_⟩
  intro i hi
  rw [hs]
  change ¬(below (s.gpr .rsp) 128).Contains (off (off rp n) i) 1
  rw [off_off]
  exact h.rand (n + i) (by rw [List.length_drop] at hi; omega)

def RoundFrame (p : WitnessParams) (sp : Addr) (m m' : Mem) : Prop :=
  ∀ a, p.Z ≤ ofs p.O a → (∀ i < p.len, a ≠ off p.op i) →
    ¬(below sp 128).Contains a 1 → m' a = m a

def RoundSaved (p : WitnessParams) (m m' : Mem) : Prop :=
  ∀ j < 32, j ≠ 12 → j ≠ 13 → j ≠ 14 → j ≠ 18 → j ≠ 19 →
    word m' p.O (8 * j) = word m p.O (8 * j)

theorem RoundSaved.refl (p : WitnessParams) (m : Mem) : RoundSaved p m m := fun _ _ _ _ _ _ _ => rfl

theorem RoundSaved.trans {p : WitnessParams} {m₁ m₂ m₃ : Mem}
    (h : RoundSaved p m₁ m₂) (h' : RoundSaved p m₂ m₃) : RoundSaved p m₁ m₃ :=
  fun j hj h12 h13 h14 h18 h19 => (h' j hj h12 h13 h14 h18 h19).trans (h j hj h12 h13 h14 h18 h19)

theorem DrawSaved.round {p : WitnessParams} {m m' : Mem} (h : DrawSaved p m m') : RoundSaved p m m' :=
  fun j hj h12 h13 h14 _ h19 => h j hj h12 h13 h14 h19

theorem RoundFrame.refl (p : WitnessParams) (sp : Addr) (m : Mem) : RoundFrame p sp m m := fun _ _ _ _ => rfl

theorem RoundFrame.trans {p : WitnessParams} {sp : Addr} {m₁ m₂ m₃ : Mem}
    (h : RoundFrame p sp m₁ m₂) (h' : RoundFrame p sp m₂ m₃) : RoundFrame p sp m₁ m₃ :=
  fun a ha ho hb => (h' a ha ho hb).trans (h a ha ho hb)

theorem DrawFrame.round {p : WitnessParams} {sp : Addr} {m m' : Mem} (h : DrawFrame p m m') :
    RoundFrame p sp m m' := fun a ha ho _ => h a ha ho

theorem RoundFrame.of_inner {p : WitnessParams} {sp : Addr} {m m' : Mem} {rs : List (Nat × Nat)}
    (hf : WorkFrame p.I rs [below sp 128] m m') (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ p.IZ)
    (hz : p.Z ≤ 2 ^ 64) : RoundFrame p sp m m' := by
  intro a ha _ hb
  apply hf a (by simpa only [List.forall_mem_singleton] using hb)
  intro r hr
  have hfit := hrs r hr
  rcases ofs_rebase p.O a (o := 256) (by decide) with ⟨_, he⟩ | ⟨_, he⟩
  · right
    change r.1 + r.2 ≤ ofs (off p.O 256) a
    rw [he]
    unfold WitnessParams.IZ at hfit
    omega_using [ha, hfit]
  · right
    change r.1 + r.2 ≤ ofs (off p.O 256) a
    unfold WitnessParams.IZ at hfit
    omega_using [he, hfit, hz]

theorem round_outer_header {p : WitnessParams} {rp : Addr} {bs : List Byte} {s t : State}
    {rs : List (Nat × Nat)} (hr : RoundRoom p rp bs s)
    (hf : WorkFrame p.I rs [below (s.gpr .rsp) 128] s.mem t.mem)
    (hrs : ∀ r ∈ rs, r.1 + r.2 ≤ p.IZ) (hz : p.Z ≤ 2 ^ 64) :
    ∀ j < 32, word t.mem p.O (8 * j) = word s.mem p.O (8 * j) := by
  intro j hj
  apply Mem.readW_congr
  intro i hi
  apply hf
  · intro r hmem
    simp only [List.mem_singleton] at hmem
    subst hmem
    apply hr.root
    have hc := Offset.contains_base p.O (d := 8 * j + i) (n := 1) (k := p.Z)
      (by omega_using [hj, hi, p.space_bounds.1]) (by omega)
    simpa only [off, BitVec.add_assoc, BitVec.ofNat_add] using hc
  · intro r hmem
    have hfit := hrs r hmem
    have ho := ofs_off p.O (d := 8 * j) (i := i) (by omega)
    rcases ofs_rebase p.O (off p.O (8 * j) + BitVec.ofNat 64 i) (o := 256) (by decide) with ⟨hl, _⟩ | ⟨_, he⟩
    · omega_using [ho, hl, hj, hi]
    · right
      change r.1 + r.2 ≤ ofs (off p.O 256) (off p.O (8 * j) + BitVec.ofNat 64 i)
      unfold WitnessParams.IZ at hfit
      omega_using [he, hfit, hz]

theorem DrawState.after_round {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s t : State}
    {regs : List Reg} (h : DrawState p rp used bs s) (hroom : RoundRoom p rp bs s)
    (hr : ModulusReady t p.I p.IZ p.w p.mi p.N)
    (hl : word t.mem p.I (8 * VG.Impl.Rsa.X86_64.Crt.sLink) = p.O)
    (hh : ∀ j < 32, word t.mem p.O (8 * j) = word s.mem p.O (8 * j))
    (hf : RoundFrame p (s.gpr .rsp) s.mem t.mem) (k : Keep regs s t) : DrawState p rp used bs t := by
  refine ⟨h.scr.congr k.2.2, hr, hl, (hh _ (by decide)).trans h.outPtr,
    (hh _ (by decide)).trans h.bits, (hh _ (by decide)).trans h.len,
    (hh _ (by decide)).trans h.ptr, (hh _ (by decide)).trans h.left, (hh _ (by decide)).trans h.usedWord,
    h.countBound, ⟨?_, ?_, h.rand.out⟩,
    ⟨fun i hi => by rw [k.2.2]; exact h.out.wr i hi, h.out.sep⟩, h.apart⟩
  · intro i hi; rw [k.2.1, k.2.2]; exact h.rand.rd i hi
  · intro i hi
    rw [hf _ (h.rand.out i hi) (fun j hj he => h.apart j hj i hi he.symm) (hroom.rand i hi)]
    exact h.rand.val i hi

end VG.Proof.Ffdh.X86_64.ParameterCandidate
