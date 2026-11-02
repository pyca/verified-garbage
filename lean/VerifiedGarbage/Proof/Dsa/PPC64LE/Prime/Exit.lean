module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Body
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Load

/-!
# DSA's probable-prime test on PPC64LE: the exit

`exit_ok`: after the body (`BOut`), with the registers saved at the entry
still in `ws`: the status into `r3`, our caller's registers and return
address back (`Spill.restore_wp`), and the octets read into `used` unless
the tape ran out.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.MillerRabin.PPC64LE.Search
open VG.Proof.Bignum (word off slot)

/-- What the exit leaves. -/
structure XOut (bits : Nat) (σ t f : State) : Prop where
  abi : abiPreserved σ f
  r3 : f.gpr .r3 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ))
  frame : Frame [cU σ] t.mem f.mem
  used : ∀ b rest, res bits σ = some (b, rest) →
    Spec.Rsa.wordsAt f.mem (σ.gpr .r7) 1 = [BitVec.ofNat 64 ((σ.gpr .r6).toNat - rest.length)]

theorem status_le (x : Option (Bool × Spec.RsaKeyGen.Rand)) : Proof.Dsa.ProbablePrime.status x ≤ 2 := by
  rcases x with _ | ⟨_ | _, _⟩ <;> simp [Proof.Dsa.ProbablePrime.status]

theorem status_eq_zero {x : Option (Bool × Spec.RsaKeyGen.Rand)} (h : Proof.Dsa.ProbablePrime.status x = 0) :
    x = none := by
  rcases x with _ | ⟨_ | _, _⟩ <;> first | rfl | cases h

/-- The restores' slots: `savedSlots` but the return address. -/
theorem restore_eq : restore = ([.load .d .r0 .r9 saveOff, .mtlr .r0] : List Instr) ++ Spill.restoreCode .r9 savedSlots.tail := rfl

theorem tail_fits : ∀ p ∈ savedSlots.tail, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide
theorem tail_restorable : Spill.Restorable .r9 savedSlots.tail := by decide
theorem tail_in : ∀ p ∈ savedSlots.tail, saveOff ≤ p.2 ∧ p.2 + 8 ≤ saveOff + 168 := by decide
theorem tail_regs : savedSlots.tail.map Prod.fst =
    [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31,
      .r7, .r2] := by decide

/-- After the exit's first block: the calling convention's registers back,
the status in `r3`, `hUsed` in `r5` and `used` in `r7`. -/
def XMid (bits : Nat) (σ t f : State) : Prop :=
  abiPreserved σ f ∧ f.gpr .r3 = BitVec.ofNat 64 (Proof.Dsa.ProbablePrime.status (res bits σ)) ∧
    f.gpr .r5 = word t.mem (wsB σ) (8 * hUsed) ∧ f.gpr .r7 = σ.gpr .r7 ∧ f.mem = t.mem ∧ f.wr = t.wr

theorem exitA_ok {bits : Nat} {σ s t : State} (h : CIn bits σ) (o : BOut bits σ s t)
    (svd : Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots t.mem) :
    WP isa (.block ([ldh .r3 hStat, ldh .r5 hUsed, .subi .r9 .r31 keyOff] ++ restore)) t (XMid bits σ t) := by
  have hsc : Scr t (wsB σ) (8 * keyWords bits) := scr_of h o.wr
  have hnw := hsc.nowrap
  have hsz := h.size
  have hfw := h.fw
  have hst := status_le (res bits σ)
  have hwsW : cW σ ∈ t.wr := by rw [o.wr, h.wr]; exact List.mem_cons_self
  have inWs : ∀ d, d + 8 ≤ (σ.gpr .r4).toNat * 8 → InRegions (t.rd ++ t.wr) (σ.gpr .r3 + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hwsW, by
      simp only [Region.Contains, Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega)]; omega⟩
  have hkw : 32 ≤ keyWords bits := by unfold keyWords; omega
  rw [restore_eq, WP.block_append_iff]
  have r31 := o.r31
  generalize hB : wsB σ = B at hsc hnw r31
  refine WP.mono (WP.keep [.r3, .r5, .r9] (Q := fun (u : State) =>
      u.gpr .r3 = word t.mem B (8 * hStat) ∧ u.gpr .r5 = word t.mem B (8 * hUsed) ∧
      u.gpr .r9 = B - BitVec.ofNat 64 552 ∧ u.mem = t.mem) ?_ (by decide))
    fun u ⟨⟨u3, u5, u9, um⟩, ku⟩ => ?_
  · simp only [ldh, hStat, hUsed, keyOff]
    prun [r31, hsc.ld (d := 160) (n := 8) (by omega), hsc.ld (d := 152) (n := 8) (by omega)]
    done
  have u9' : u.gpr .r9 = σ.gpr .r3 := by
    rw [u9, ← hB]; simp only [wsB]; exact BitVec.add_sub_cancel _ _
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (v : State) => v.lr = σ.lr ∧ (∀ r, r ≠ .r0 → v.gpr r = u.gpr r) ∧ v.mem = u.mem ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp) ?_ fun v ⟨vlr, vg, vm, vrd, vwr, vsp⟩ => ?_
  · have hin := inWs saveOff (by simp only [saveOff, keyOff] at hsz ⊢; omega)
    simp only [saveOff] at hin ⊢
    refine WP.cons (exec_load_d (by decide) (by decide) (by rw [u9', ku.rd, ku.wr]; exact hin)) ?_
    refine WP.cons exec_mtlr (WP.block_nil ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩)
    · have := svd (.r0, saveOff) (by decide)
      simp only [State.write, ↓reduceIte, saveOff] at this ⊢
      rw [um, u9']; exact this
    · simp only [State.write, hr, ↓reduceIte]
  · have hpres : ∀ r ∈ preserved, r ∈ savedSlots.tail.map Prod.fst := by rw [tail_regs]; decide
    have gsv : ∀ r, r ≠ .r0 → (σ.write .r0 σ.lr).gpr r = σ.gpr r := fun r hr => by
      simp only [State.write, hr, ↓reduceIte]
    refine WP.mono (Spill.restore_wp (b := .r9) (B := σ.gpr .r3) (by decide) (by rw [vg _ (by decide)]; exact u9')
      tail_fits tail_restorable (fun p hp => by
        rw [vrd, vwr, ku.rd, ku.wr]
        exact inWs _ (by have := tail_in p hp; simp only [saveOff, keyOff] at *; omega))
      (by rw [vm, um]; exact svd.sub fun p hp => List.mem_of_mem_tail hp)) fun f hf => ?_
    have o3 : f.gpr .r3 = u.gpr .r3 := (hf.other _ (by rw [tail_regs]; decide)).trans (vg _ (by decide))
    have o5 : f.gpr .r5 = u.gpr .r5 := (hf.other _ (by rw [tail_regs]; decide)).trans (vg _ (by decide))
    refine ⟨⟨fun r hr => (hf.gpr_of (.inl (hpres r hr))).trans (gsv r (by revert hr; decide +revert)),
        hf.sp.trans (vsp.trans (ku.sp.trans o.sp)), hf.lr.trans vlr⟩, ?_, ?_,
      (hf.gpr (.r7, saveOff + 152) (by decide)).trans (gsv _ (by decide)),
      hf.mem.trans (vm.trans um), hf.wr.trans (vwr.trans ku.wr)⟩
    · rw [o3, u3, ← hB]; exact o.stat
    · rw [o5, u5, ← hB]

theorem exit_ok {bits : Nat} {σ s t : State} (h : CIn bits σ) (o : BOut bits σ s t)
    (svd : Spill.Saved (σ.gpr .r3) (σ.write .r0 σ.lr).gpr savedSlots t.mem) :
    WP isa exit t (XOut bits σ t) := by
  have hst := status_le (res bits σ)
  unfold exit
  refine WP.seq (WP.mono (exitA_ok h o svd) fun f ⟨fa, f3, f5, f7, fm, fwr⟩ => ?_)
  refine WP.ite _ (eval_zero_ofNat f .r3 (by omega) f3) (fun hz => ?_) (fun hz => ?_)
  · have h0 : Proof.Dsa.ProbablePrime.status (res bits σ) = 0 := by simpa using hz
    exact WP.block_nil ⟨fa, f3, by rw [fm]; exact Frame.refl _ _, fun b rest hr => by
      rw [status_eq_zero h0] at hr; cases hr⟩
  · have hU : InRegions f.wr (f.gpr .r7 + BitVec.ofNat 64 0) 8 := ⟨cU σ, by rw [fwr, o.wr, h.wr]; simp, by
      rw [f7]; simp only [Region.Contains, BitVec.add_zero, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
    refine WP.cons (exec_store_d (by decide) (by decide) hU) (WP.block_nil ⟨?_, f3, ?_, fun b rest hr => ?_⟩)
    · exact fa
    · rw [f7, fm, BitVec.add_zero]
      exact (Frame.refl _ _).writeW List.mem_cons_self _ (by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
      rw [f7, Mem.readW_writeW_self64, f5, o.used b rest hr]

end VG.Proof.Dsa.PPC64LE.Prime
