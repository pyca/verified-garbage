module

public import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Step
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Small
open VG VG.AArch64
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (TPre st dp tp L bp stR dR tR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream bytesAt serialize block)

/-- The scalar stream after `n` blocks of the vector kernel. -/
theorem tail_ok {s₀ : State} (hp : TPre s₀) {n : Nat} {s : State} (h : Prefix s₀ n s) (hle : 64*n ≤ L s₀) :
    WP isa Impl.ChaCha20.AArch64.Xor.xor s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 :=
  (Xor.rest_ok BlockImpl.scalar.xorNoFrames (fun s hs _ => Xor.xor_gpr BlockImpl.scalar s hs) hp
    (n := 64*n) hle (by omega) h.x0 h.x1 h.x2 h.x3 h.x4 h.rd h.wr
    (by rw [h.cnt, show 64*n/64 = n by omega]) h.data h.src).mono fun _ ⟨ha, hpost, h0, h1⟩ =>
    ⟨⟨fun r hr => (ha.1 r hr).trans (h.cs r hr), ha.2.trans h.sp⟩, hpost, h0, h1⟩

structure CheckKeep (s a : State) : Prop where
  gpr : ∀ r, r ≠ .x5 → r ≠ .x6 → a.gpr r = s.gpr r
  mem : a.mem = s.mem
  rd : a.rd = s.rd
  wr : a.wr = s.wr
  sp : a.sp = s.sp

theorem CheckKeep.pre {s a : State} (h : CheckKeep s a) (hp : xorAArch64.pre s) :
    xorAArch64.pre a := by
  simpa only [xorAArch64,h.rd,h.wr,h.gpr .x0 (by decide) (by decide),h.gpr .x1 (by decide) (by decide),
    h.gpr .x2 (by decide) (by decide),h.gpr .x3 (by decide) (by decide),
    h.gpr .x4 (by decide) (by decide)] using hp

theorem CheckKeep.finish {s a u : State} (h : CheckKeep s a)
    (hu : GprAbi a u ∧ xorAArch64.post a u ∧ u.gpr .x0=a.gpr .x0 ∧ u.gpr .x1=a.gpr .x3) :
    GprAbi s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  obtain ⟨hab,hp,h0,h1⟩ := hu
  refine ⟨⟨?_,hab.2.trans h.sp⟩,?_,h0.trans (h.gpr _ (by decide) (by decide)),
    h1.trans (h.gpr _ (by decide) (by decide))⟩
  · intro r hr
    have hn : r ≠ .x5 ∧ r ≠ .x6 := by revert hr; decide +revert
    exact (hab.1 r hr).trans (h.gpr r hn.1 hn.2)
  · simpa only [xorAArch64,h.mem,h.gpr .x0 (by decide) (by decide),h.gpr .x1 (by decide) (by decide),
      h.gpr .x2 (by decide) (by decide),h.gpr .x4 (by decide) (by decide)] using hp

theorem check_ok (s : State) (b : Nat) (hb : b < 64) :
    WP isa (.block [.lsr .x .x5 .x2 b]) s fun a =>
      CheckKeep s a ∧ a.gpr .x5=BitVec.ofNat 64 (L s / 2^b) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons,runBlock_nil,exec,State.read,
    Size.bits,hb,Option.some.injEq,isa,runStep_some,exists_eq_left']
  refine ⟨⟨?_,rfl,rfl,rfl,rfl⟩,?_⟩
  · intro r hr _; exact RegUpd.gpr_write_of_ne _ _ _ hr
  · rw [RegUpd.gpr_write_self,BitVec.setWidth_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.setWidth_eq,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (s.gpr .x2).isLt)).symm

theorem check_zero {s : State} {n b : Nat} (_hb : b < 64) (hn : n < 2^64)
    (h : s.gpr .x5=BitVec.ofNat 64 (n/2^b)) :
    isa.eval (.zero .x .x5) s = some (decide (n < 2^b)) := by
  rw [show isa.eval (.zero .x .x5) s = some (s.gpr .x5 == 0) from Xor.eval_zero s .x5,h,Xor.ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]
  congr 2
  simp only [Nat.div_eq_zero_iff,show 2^b ≠ 0 from Nat.ne_of_gt (Nat.two_pow_pos b),false_or]

theorem check3_ok (s : State) (hl : L s < 256) :
    WP isa (.block [.lsr .x .x5 .x2 6,.subImm .x .x5 .x5 3,.lsr .x .x5 .x5 63]) s fun a =>
      CheckKeep s a ∧ a.gpr .x5=BitVec.ofNat 64 (if L s < 192 then 1 else 0) ∧
      a.gpr .x6 = s.gpr .x6 := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, runBlock_cons,runBlock_nil,exec,State.read,
    Size.bits,Option.some.injEq,isa,runStep_some,exists_eq_left',
    RegUpd.gpr_write_self]
  refine ⟨⟨?_,rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · intro r hr _;simp only [RegUpd.gpr_write,hr,ite_false]
  · simp only [BitVec.setWidth_eq]
    have he : s.gpr .x2 >>> 6 = BitVec.ofNat 64 (L s/64) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (by omega_arith)).symm
    rw [he]
    have hq : L s/64 < 4 := by omega_arith
    have hcases : L s/64=0 ∨ L s/64=1 ∨ L s/64=2 ∨ L s/64=3 := by omega_arith
    rcases hcases with h|h|h|h <;>
      simp only [show (L s < 192) ↔ (L s/64 < 3) by omega_arith,h] <;> decide
  · simp only [RegUpd.gpr_write,show Reg.x6 ≠ .x5 by decide,ite_false]

theorem check3_nonzero {s : State} {n : Nat}
    (h : s.gpr .x5=BitVec.ofNat 64 (if n < 192 then 1 else 0)) :
    isa.eval (.nonzero .x .x5) s = some (decide (n < 192)) := by
  rw [show isa.eval (.nonzero .x .x5) s = some (!(s.gpr .x5 == 0)) from Xor.eval_nonzero s .x5,h]
  by_cases hn : n < 192 <;> simp [hn]

/-- `short`'s first block: the check, and the destination copied to `x6`. -/
theorem check7_ok (s : State) :
    WP isa (.block [.lsr .x .x5 .x2 7, Impl.ChaCha20.AArch64.Xor.mov .x6 .x4]) s fun a =>
      CheckKeep s a ∧ a.gpr .x5=BitVec.ofNat 64 (L s / 2^7) ∧ a.gpr .x6 = s.gpr .x4 := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, runBlock_cons,runBlock_nil,exec,State.read,
    Impl.ChaCha20.AArch64.Xor.mov,Size.bits,Option.some.injEq,isa,runStep_some,exists_eq_left',
    BitVec.add_zero]
  refine ⟨⟨?_,rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · intro r h5 h6; simp only [RegUpd.gpr_write,h5,h6,ite_false]
  · simp only [RegUpd.gpr_write,show Reg.x5 ≠ .x6 by decide,ite_false,ite_true,BitVec.setWidth_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (s.gpr .x2).isLt)).symm
  · simp only [RegUpd.gpr_write,ite_true,show Reg.x4 ≠ .x5 by decide,ite_false,BitVec.setWidth_eq]

theorem short_ok {sve : Bool} (s : State) (hp : xorAArch64.pre s) (hl : L s < 256) :
    WP isa (Impl.ChaCha20.AArch64.Small.short sve) s fun u =>
      GprAbi s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  apply WP.seq
  refine (check7_ok s).mono fun a ⟨ha,h5,h6⟩ => ?_
  apply WP.ite (decide (L s < 128)) (check_zero (by decide) (Xor.L_lt s) h5)
  · intro _
    exact (Xor.xor_gpr BlockImpl.scalar a (ha.pre hp)).mono fun _ h => ha.finish h
  · intro hshort
    have hge : 128 ≤ L s := by have := of_decide_eq_false hshort;omega_arith
    apply WP.seq
    apply WP.seq
    refine (check3_ok a (by simpa only [L,ha.gpr .x2 (by decide) (by decide)] using hl)).mono
      fun b ⟨hb,hb5,hb6⟩ => ?_
    have hla : L a=L s := by simp only [L,ha.gpr .x2 (by decide) (by decide)]
    rw [hla] at hb5
    have hpb := Xor.TPre.of b (hb.pre (ha.pre hp))
    have hb6' : b.gpr .x6 = tp b := by
      rw [hb6, h6, ← ha.gpr .x4 (by decide) (by decide), ← hb.gpr .x4 (by decide) (by decide)]
    apply WP.ite (decide (L s < 192)) (check3_nonzero hb5)
    · intro h192
      have hlen : 128 ≤ L b := by
        simp only [L,hb.gpr .x2 (by decide) (by decide),ha.gpr .x2 (by decide) (by decide)];exact hge
      exact ((step_ok (sve := sve) b hpb hb6' 2 (by decide) hlen).mono fun c hc =>
        (tail_ok hpb hc hlen).mono fun _ hu => ha.finish (hb.finish hu))
    · intro h192
      have hge192 : 192 ≤ L s := by have := of_decide_eq_false h192;omega_arith
      have hlen : 192 ≤ L b := by
        simp only [L,hb.gpr .x2 (by decide) (by decide),ha.gpr .x2 (by decide) (by decide)];exact hge192
      exact ((step_ok (sve := sve) b hpb hb6' 3 (by decide) hlen).mono fun c hc =>
        (tail_ok hpb hc hlen).mono fun _ hu => ha.finish (hb.finish hu))

theorem short_noFrames (sve : Bool) : (Impl.ChaCha20.AArch64.Small.short sve).noFrames = true := by
  cases sve <;> lit_decide

/-- `short` after the four-block chunks: run on the data the chunks left. -/
theorem tail_short {sve : Bool} {s₀ : State} (hp : TPre s₀) {t : Nat} {s : State} (h : Neon4.LInv s₀ t s)
    (hlt : L s₀ - 256 * t < 256) :
    WP isa (Impl.ChaCha20.AArch64.Small.short sve) s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 :=
  (Xor.rest_ok (short_noFrames sve) (fun s hs hl => short_ok (sve := sve) s hs (by rw [hl]; exact hlt))
    hp (n := 256 * t) h.le (by omega) h.x0 h.x1 h.x2 h.x3 h.x4 h.rd h.wr
    (by rw [h.cnt, show 256 * t / 64 = 4 * t by omega]) h.data h.src).mono fun _ ⟨ha, hpost, h0, h1⟩ =>
    ⟨⟨fun r hr => (ha.1 r hr).trans (h.keep r (by intro he; subst he; simp [preserved] at hr)
      (by intro he; subst he; simp [preserved] at hr) (by intro he; subst he; simp [preserved] at hr)
      (by intro he; subst he; simp [preserved] at hr) (by intro he; subst he; simp [preserved] at hr)),
      ha.2.trans h.sp⟩, hpost, h0, h1⟩

theorem correct {sve : Bool} (s : State) (hp : xorAArch64.pre s) :
    WP isa (Impl.ChaCha20.AArch64.Small.xor sve) s fun u =>
      abiPreserved s u ∧ xorAArch64.post s u ∧ u.gpr .x0=s.gpr .x0 ∧ u.gpr .x1=s.gpr .x3 := by
  apply WP.withPreservedV (hc := by cases sve <;> lit_decide)
  apply WP.seq
  refine (Neon4.init_ok s).mono fun u ⟨hi, h5⟩ => ?_
  apply WP.seq
  refine (Neon4.bulk_ok (Xor.TPre.of s hp) hi h5).mono fun v ⟨t, hlt, hv⟩ => ?_
  exact tail_short (sve := sve) (Xor.TPre.of s hp) hv hlt

theorem xor_noFrames (sve : Bool) : (Impl.ChaCha20.AArch64.Small.xor sve).noFrames = true := by
  cases sve <;> lit_decide

end VG.Proof.ChaCha20.AArch64.Small
