module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubSave
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.BytesFrame

/-!
# The RSA public-key operation on RISC-V: the function

`fnContract`: `vg_rsa_public_precomputed_checked` on the registers and the
stack, its working space and length the arguments in memory.

`fn_correct`: `publicChecked` reads the working space's address from the
stack, saves the callee-saved registers in its header, runs `mid_ok` from
the state `setup` leaves (`Mid`), and restores them.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)

/-- The arguments on the stack: `scratch` and `scratch_len`. -/
abbrev stackArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- `vg_rsa_public_precomputed_checked`, on the registers and the stack. -/
def fnContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let pre : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat * 8⟩
    let e : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
    let inp : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    s.rd = [pre, e, inp, stackArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint pre ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint scr ∧ out.Disjoint (stackArgs s) ∧
      pre.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ scr.Disjoint (stackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat * 8 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .a1).toNat ∧ (s.gpr .a3).toNat = Spec.Rsa.precomputedWords (s.gpr .a1).toNat ∧
      (s.gpr .a7).toNat = (s.gpr .a1).toNat ∧ 1 ≤ (s.gpr .a5).toNat ∧
      (s.gpr .a5).toNat ≤ (s.gpr .a1).toNat ∧ Spec.Rsa.publicScratchWords (s.gpr .a1).toNat ≤ (stackArg s 1).toNat ∧
      (s.gpr .a2).toNat % 8 = 0 ∧ (stackArg s 0).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s s' :=
    ∀ nB : List Byte, nB.length = (s.gpr .a1).toNat →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) →
      Spec.Rsa.written s'.mem (s.gpr .a0) (s.gpr .a1).toNat ((s'.gpr .a0).setWidth 32)
        (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a1).toNat))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧
      (Spec.Rsa.wordsAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a4) (s₁.gpr .a5).toNat).map (·.toNat) =
        (Spec.Rsa.wordsAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a4) (s₂.gpr .a5).toNat).map (·.toNat)

/-- The public data of a state on entry. -/
def dataOf (s : State) : PD :=
  ⟨s.gpr .a0, (s.gpr .a1).toNat, s.gpr .a2, s.gpr .a4, (s.gpr .a5).toNat, s.gpr .a6, stackArg s 0,
    (stackArg s 1).toNat * 8⟩

theorem sep_of_disjoint {A S : Addr} {n Z : Nat} (h : (⟨A, n⟩ : Region).Disjoint ⟨S, Z⟩) :
    ∀ x, ofs A x < n → Z ≤ ofs S x := fun x hx => by
  by_contra hc
  exact h x (by simp only [Region.Contains]; simp only [ofs] at hx; omega_arith)
    (by simp only [Region.Contains]; simp only [ofs] at hc; omega_arith)

theorem ne_of_disjoint {A S : Addr} {n Z : Nat} (h : (⟨A, n⟩ : Region).Disjoint ⟨S, Z⟩) (hn : n ≤ 2 ^ 64) :
    ∀ i < n, ∀ x, ofs S x < Z → off A i ≠ x := fun i hi x hx e => by
  subst e
  exact h _ (Offset.contains_base (d := i) _ (by omega_arith) (by omega_arith))
    (by simp only [Region.Contains]; simp only [ofs, off] at hx; omega_arith)

theorem saved_ne_t0 : ∀ i < 12, PublicChecked.saved i ≠ .t0 := by decide

theorem sav_al {S : Addr} (hS : S.toNat % 8 = 0) (hn : S.toNat + 256 ≤ 2 ^ 64) {i : Nat} (hi : i < 12) :
    (off (savW S) (8 * i)).toNat % 8 = 0 := by
  have e : off (savW S) (8 * i) = S + BitVec.ofNat 64 (128 + 8 * i) := by
    show S + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i) = _
    rw [Offset.add_add]
  have h2 : (S + BitVec.ofNat 64 (128 + 8 * i)).toNat = S.toNat + (128 + 8 * i) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [e, h2]
  omega

/-- `save` and `setup`: `Mid`, with the callee-saved registers saved. -/
theorem front_ok {s : State} (h : fnContract.pre s) :
    WP isa (.block (PublicChecked.save ++ setup)) s fun s₃ =>
      Mid (dataOf s) s₃ ∧
        (∀ i < 12, s₃.mem.readW (off (savW (stackArg s 0)) (8 * i)) 64 = s.gpr (PublicChecked.saved i)) ∧
        Keep (([.t0, .s6] : List Reg) ++ ([.a7, .s5, .s10, .s11, .t0] : List Reg)) s s₃ ∧
        Frame [savR (savW (stackArg s 0))] s.mem s₃.mem := by
  obtain ⟨hrd, hwr, dOP, dOE, dOX, dOS, dOA, dPS, dES, dXS, dSA, nwO, nwP, nwE, nwX, nwS, ⟨hk, hk'⟩, hpl,
    hxl, hL1, hLk, hsl, alP, alS, alsp⟩ := h
  simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords] at hpl hsl
  unfold PublicChecked.save
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (loadS_ok s ⟨stackArgs s, List.mem_append_left _ (by rw [hrd]; simp),
    by simp [Region.Contains]⟩ (by omega_arith)) fun s₁ ⟨⟨a0', m1, sp1⟩, k1⟩ => ?_)
  have hin : ∀ i < 12, InRegions s₁.wr (off (savW (s₁.gpr .t0)) (8 * i)) 8 := fun i hi => by
    rw [a0', k1.2.2, hwr]
    show InRegions _ (stackArg s 0 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.block_append (WP.mono (save_ok s₁ hin (fun i hi => by
    rw [a0']; exact sav_al alS (by omega_arith) hi)) fun s₂ hS => ?_)
  have k12 := k1.trans hS.keep
  have e1 : s₂.gpr .a1 = BitVec.ofNat 64 (s.gpr .a1).toNat :=
    (k12.gpr (by decide)).trans (by simp)
  refine WP.mono (setup_ok (O := s.gpr .a0) (k := (s.gpr .a1).toNat) (k12.gpr (by decide)) e1
    (hS.s6.trans a0') hk') fun s₃ ⟨⟨j10, j11, j0, j5, j7, jm⟩, k₃⟩ => ?_
  have k := k12.trans k₃
  have hrd₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [k.2.1, k.2.2]
  have hh : hdrBytes = 256 := rfl
  have hwd : (dataOf s).w = ((s.gpr .a1).toNat + 7) / 8 := rfl
  have hk1 : (s.gpr .a1).toNat < 2 ^ 64 := (s.gpr .a1).isLt
  refine ⟨⟨Scr.of_mem (by rw [k.2.2, hwr]; simp [dataOf]) nwS alS,
    fun i hi => ⟨⟨s.gpr .a0, (s.gpr .a1).toNat⟩, by rw [k.2.2, hwr]; simp,
      Offset.contains_base _ (by change i < (s.gpr .a1).toNat at hi; omega_arith)
        (by change i < (s.gpr .a1).toNat at hi; omega_arith)⟩, nwO,
    hk, hk', by show slot (((s.gpr .a1).toNat + 7) / 8) 8 ≤ (stackArg s 1).toNat * 8; unfold slot; rw [hh]; omega_arith,
    hL1, hLk, by show (s.gpr .a2).toNat + 16 * (((s.gpr .a1).toNat + 7) / 8) ≤ 2 ^ 64; omega_arith, alP,
    fun x hx => sep_of_disjoint dPS x (by
      change ofs (s.gpr .a2) x < 16 * (((s.gpr .a1).toNat + 7) / 8) at hx; omega_arith), sep_of_disjoint dOS,
    ne_of_disjoint dES (Nat.le_of_lt (s.gpr .a5).isLt),
    fun i hi => ne_of_disjoint dXS (Nat.le_of_lt (s.gpr .a7).isLt) i (by
      change i < (s.gpr .a1).toNat at hi; omega_arith),
    fun i hi => ⟨⟨s.gpr .a2, (s.gpr .a3).toNat * 8⟩, by rw [hrd₃, hrd]; simp, Offset.contains_base _ (by
      change i < 2 * (((s.gpr .a1).toNat + 7) / 8) at hi; omega_arith) (by
      change i < 2 * (((s.gpr .a1).toNat + 7) / 8) at hi; omega_arith)⟩,
    fun i hi => ⟨⟨s.gpr .a4, (s.gpr .a5).toNat⟩, by rw [hrd₃, hrd]; simp, Offset.contains_base _ (by
      change i < (s.gpr .a5).toNat at hi; omega_arith) (by change i < (s.gpr .a5).toNat at hi; omega_arith)⟩,
    fun i hi => ⟨⟨s.gpr .a6, (s.gpr .a7).toNat⟩, by rw [hrd₃, hrd]; simp, Offset.contains_base _ (by
      change i < (s.gpr .a1).toNat at hi; omega_arith) (by change i < (s.gpr .a1).toNat at hi; omega_arith)⟩,
    by rw [k.gpr (by decide)]; simp [dataOf, off], by rw [k.gpr (by decide)]; simp [dataOf, off],
    by rw [k.gpr (by decide)]; simp [dataOf], k.gpr (by decide),
    (k₃.gpr (by decide)).trans (hS.s6.trans a0'),
    by rw [j10]; simp [dataOf, off], j11, j7, j0,
    by rw [j5, hwd, Nat.mul_add]⟩, fun i hi => ?_, k, ?_⟩
  · rw [jm, ← a0', hS.saved i hi, k1.gpr fun h => saved_ne_t0 i hi (List.mem_singleton.mp h)]
  · rw [jm, ← m1, ← a0']; exact hS.frame

/-- `e`'s bytes, apart from the saved registers. -/
theorem front_e {s s₃ : State} (h : fnContract.pre s) (fr : Frame [savR (savW (stackArg s 0))] s.mem s₃.mem) :
    Spec.Rsa.bytesAt s₃.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, dES, -, -, -, -, -, -, nwS, -, -, -, -, -, hsl, -, -, -⟩ := h
  simp only [Spec.Rsa.publicScratchWords] at hsl
  have savR_sub : Region.Sub (savR (savW (stackArg s 0))) ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ :=
    Offset.sub_base _ (by omega_arith)
  refine VG.Proof.Rsa.rsa_bytes_frame fr (s.gpr .a5).isLt fun r hr => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  exact dES.sub_right savR_sub

theorem ra_free : Reg.ra ∉ midRegs ∧ Reg.ra ∉ (([.t0, .s6] : List Reg) ++ ([.a7, .s5, .s10, .s11, .t0] : List Reg)) ∧
    ∀ i < 12, Reg.ra ≠ PublicChecked.saved i := by decide

theorem pres_saved : ∀ r ∈ preserved, ∃ i < 12, r = PublicChecked.saved i := by decide

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa publicChecked s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  show WP isa publicChecked s fun t => abiPreserved s t ∧ fnContract.post s t
  suffices main : WP isa publicChecked s fun t =>
      ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ fnContract.post s t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  have hpre := h
  obtain ⟨hrd, hwr, dOP, dOE, dOX, dOS, dOA, dPS, dES, dXS, dSA, nwO, nwP, nwE, nwX, nwS, ⟨hk, hk'⟩, hpl,
    hxl, hL1, hLk, hsl, alP, alS, alsp⟩ := h
  simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords] at hpl hsl
  have hh : hdrBytes = 256 := rfl
  have sav_sub : ∀ i < 12, Region.Sub ⟨off (savW (stackArg s 0)) (8 * i), 8⟩
      ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ := fun i hi => by
    show Region.Sub ⟨stackArg s 0 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i), 8⟩ _
    rw [Offset.add_add]; exact Offset.sub_base _ (by omega_arith)
  have savR_sub : Region.Sub (savR (savW (stackArg s 0))) ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ :=
    Offset.sub_base _ (by omega_arith)
  unfold publicChecked
  refine WP.seq (WP.mono (front_ok hpre) fun s₃ ⟨hM, hsv, k3, fr3⟩ => ?_)
  refine mid_ok hM fun t ⟨hpost, hfr, kt⟩ => ?_
  have hin : ∀ i < 12, InRegions t.wr (off (savW (stackArg s 0)) (8 * i)) 8 := fun i hi => by
    rw [kt.2.2, k3.2.2, hwr]
    show InRegions _ (stackArg s 0 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hsav : ∀ i < 12, t.mem.readW (off (savW (stackArg s 0)) (8 * i)) 64 = s.gpr (PublicChecked.saved i) :=
    fun i hi => by
      rw [hfr.readW (r := ⟨off (savW (stackArg s 0)) (8 * i), 8⟩) (by simp [Region.Contains]) ?_ (by decide)]
      · exact hsv i hi
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl
        · show Region.Disjoint ⟨stackArg s 0 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i), 8⟩
            ⟨stackArg s 0 + BitVec.ofNat 64 (slot (dataOf s).w 0), _⟩
          rw [Offset.add_add]
          exact Offset.disjoint _ (Or.inl (by unfold slot; rw [hh]; omega_arith)) (by omega_arith)
            (by have := hM.hZ; unfold slot at this ⊢; rw [hh] at this ⊢; show _ ≤ 2 ^ 64
                have := hM.scr.nowrap; omega_arith)
        · exact (dOS.symm.sub_left (sav_sub i hi))
  refine WP.mono (restore_ok t (S := stackArg s 0) (v := fun i => s.gpr (PublicChecked.saved i))
    (by rw [kt.gpr (by decide)]; exact hM.s6) hin (fun i hi => sav_al alS (by omega_arith) hi) hsav)
    fun u ⟨urs, uot, um, _, _, _⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pres_saved r hr
    exact urs i hi
  · rw [uot .ra ra_free.2.2, kt.gpr ra_free.1, k3.gpr ra_free.2.1]
  · intro nB hl hpp
    rw [uot .a0 (by decide), um]
    have hP : Spec.Rsa.wordsAt s₃.mem (s.gpr .a2) (2 * (dataOf s).w) =
        Spec.Rsa.wordsAt s.mem (s.gpr .a2) (s.gpr .a3).toNat := by
      rw [show 2 * (dataOf s).w = (s.gpr .a3).toNat by show 2 * (((s.gpr .a1).toNat + 7) / 8) = _; omega_arith]
      refine VG.Proof.Rsa.wordsAt_frame fr3 (by omega_arith) fun r hr => ?_
      simp only [List.mem_singleton] at hr
      subst hr
      exact (dPS.sub_left (Region.sub_prefix (by omega_arith))).sub_right savR_sub
    have hE := front_e hpre fr3
    have hX : Spec.Rsa.bytesAt s₃.mem (s.gpr .a6) (s.gpr .a1).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a1).toNat := by
      refine VG.Proof.Rsa.rsa_bytes_frame fr3 (s.gpr .a1).isLt fun r hr => ?_
      simp only [List.mem_singleton] at hr
      subst hr
      exact (dXS.sub_left (Region.sub_prefix (by omega_arith))).sub_right savR_sub
    have := hpost nB hl (by rw [hpp]; exact congrArg some hP.symm)
    simp only [dataOf] at this
    rw [hE, hX] at this
    exact this

end VG.Proof.Bignum.RISCV64.Pub
