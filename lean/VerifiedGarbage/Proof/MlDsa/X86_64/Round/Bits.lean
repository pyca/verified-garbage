module

import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
public import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Contracts
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Contracts
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
meta import VerifiedGarbage.Proof.MlDsa.Round.Decompose

/-! ### `MlDsa.X86_64.Round.OneOut`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86-64: the functions with `γ₂` and one output

`vg_mldsa_high_bits`, `vg_mldsa_low_bits` and `vg_mldsa_use_hint` compare `γ₂`
(in `gr`) with `(q - 1)/32`, move their output pointer (in `oa`) to `r10`, and
run the loop of the body for the `γ₂` they found. `oneOut_ok` proves this
once, from a body that stores `F γ₂ x` for the coefficients `x p` of the
inputs `p`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Proof.MlDsa (coeffAt gamma2s)
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)

/-- `x - k` is zero exactly when `x = k`. -/
theorem sub_beq_zero32 (x k : BitVec 32) : (x - k == 0) = decide (x = k) := by
  by_cases h : x = k
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; apply h; bv_omega

theorem gamma_cases {s₀ : State} {gr : Reg} (hg : arg32 s₀ gr ∈ gamma2s) :
    (BitVec.setWidth 32 (s₀.gpr gr) = BitVec.ofNat 32 g32 → arg32 s₀ gr = g32) ∧
      (BitVec.setWidth 32 (s₀.gpr gr) ≠ BitVec.ofNat 32 g32 → arg32 s₀ gr = g88) := by
  refine ⟨fun h => by rw [arg32, h]; rfl, fun h => ?_⟩
  rcases mem_gamma2s hg with e | e
  · exact e
  · exact absurd (BitVec.eq_of_toNat_eq (e.trans rfl)) h

/-- What the prologue does: `γ₂` compared, and the output pointer in `r10`. -/
def Prologue (gr oa : Reg) (s s' : State) : Prop :=
  (s'.gpr .r10 = s.gpr oa ∧ s'.zf = some (BitVec.setWidth 32 (s.gpr gr) - BitVec.ofNat 32 g32 == 0) ∧
    s'.mem = s.mem) ∧ Keep [gr, .r10] s s'

theorem prologue_rsi_rdx (s : State) :
    WP isa (.block (gammaCmp .rsi ++ ([.mov .r10 (.reg .rdx)] : List Instr))) s (Prologue .rsi .rdx s) := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  unfold gammaCmp
  xrun [List.cons_append, List.nil_append]

theorem prologue_rdx_rcx (s : State) :
    WP isa (.block (gammaCmp .rdx ++ ([.mov .r10 (.reg .rcx)] : List Instr))) s (Prologue .rdx .rcx s) := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  unfold gammaCmp
  xrun [List.cons_append, List.nil_append]

theorem oneOut_ok {s₀ : State} {ins : List Reg} {gr oa : Reg} {clob : List Reg} {body : Nat → List Instr}
    {F : Nat → List (BitVec 32) → BitVec 32}
    (hrd : ∀ p ∈ ins, pR (s₀.gpr p) ∈ s₀.rd) (hwr : s₀.wr = [pR (s₀.gpr oa)])
    (hdis : ∀ p ∈ ins, (pR (s₀.gpr p)).Disjoint (pR (s₀.gpr oa))) (hg : arg32 s₀ gr ∈ gamma2s)
    (hpro : WP isa (.block (gammaCmp gr ++ ([.mov .r10 (.reg oa)] : List Instr))) s₀ (Prologue gr oa s₀)) (hins : ∀ p ∈ ins, p ≠ gr ∧ p ≠ .r10) (hfix : ∀ r ∈ Reg.r10 :: ins, r ∉ clob)
    (hcx : .rcx ∈ clob)
    (hbody : ∀ g, (g = g32 ∨ g = g88) → ∀ s, (∀ p ∈ ins, InRegions (s.rd ++ s.wr) (cfAddr (s.gpr p) (s.gpr .rcx)) 4) →
      InRegions s.wr (cfAddr (s.gpr .r10) (s.gpr .rcx)) 4 →
      WP isa (.block (body g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
        (s'.mem = s.mem.writeW (cfAddr (s.gpr .r10) (s.gpr .rcx))
            (F g (ins.map fun p => s.mem.readW (cfAddr (s.gpr p) (s.gpr .rcx)) 32)) ∧
          s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep clob s s') :
    WP isa (.seq (.block (gammaCmp gr ++ ([.mov .r10 (.reg oa)] : List Instr))) (.ite .e (mapLoop (body g32)) (mapLoop (body g88))))
      s₀ fun s' =>
        (∀ k < 256, coeffAt s'.mem (s₀.gpr oa) k = F (arg32 s₀ gr) (ins.map fun p => coeffAt s₀.mem (s₀.gpr p) k)) ∧
          Frame [pR (s₀.gpr oa)] s₀.mem s'.mem := by
  refine WP.seq (WP.mono hpro fun s₁ ⟨⟨h10, hz, hm⟩, hk⟩ => ?_)
  have hp : ∀ p ∈ ins, s₁.gpr p = s₀.gpr p := fun p hp' =>
    hk.gpr (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact hins p hp')
  have hL : Layout s₁ ins [.r10] :=
    { rd := fun p hp' => by rw [hp p hp', hk.2.1, hk.2.2]; exact List.mem_append_left _ (hrd p hp')
      wr := fun o ho => by
        simp only [List.mem_singleton] at ho; subst ho; rw [h10, hk.2.2, hwr]; exact List.mem_singleton_self _
      dis := fun p hp' o ho => by
        simp only [List.mem_singleton] at ho; subst ho; rw [h10, hp p hp']; exact hdis p hp'
      pw := List.pairwise_singleton _ _ }
  have go : ∀ g, arg32 s₀ gr = g → WP isa (mapLoop (body g)) s₁ fun s' =>
      (∀ k < 256, coeffAt s'.mem (s₀.gpr oa) k = F (arg32 s₀ gr) (ins.map fun p => coeffAt s₀.mem (s₀.gpr p) k)) ∧
        Frame [pR (s₀.gpr oa)] s₀.mem s'.mem := by
    intro g hge
    refine WP.mono (loop_ok (fixed := .r10 :: ins) (V := fun _ k => F g (ins.map fun p => coeffAt s₀.mem (s₀.gpr p) k))
      (J := fun _ _ => True) hL hfix hcx (fun _ _ _ _ => trivial) fun i hi s hI hc => ?_) fun s' hI => ?_
    · have ha : ∀ p ∈ Reg.r10 :: ins, cfAddr (s.gpr p) (s.gpr .rcx) = coeffAddr (s₁.gpr p) (255 - i) :=
        fun p hp' => hI.addr hc hi hp'
      have hg' : g = g32 ∨ g = g88 := by
        rcases mem_gamma2s hg with e | e <;> rw [e] at hge <;> subst hge <;> decide
      refine WP.mono (hbody g hg' s (fun p hp' => by
          rw [ha p (List.mem_cons_of_mem _ hp')]; exact hI.inR hL hp' (by omega_using []))
        (by rw [ha _ List.mem_cons_self]; exact hI.inW hL List.mem_cons_self (by omega_using [])))
        fun s' ⟨⟨hm', hc', hz'⟩, hk'⟩ => ⟨⟨?_, hc', hz', trivial⟩, hk'⟩
      rw [hm', ha _ List.mem_cons_self]
      refine congrArg (Mem.writeW _ _ <| F g ·) (List.map_congr_left fun p hp' => ?_)
      rw [ha p (List.mem_cons_of_mem _ hp'), hI.read hL hp' (by omega_using []), hm, hp p hp']
    · refine ⟨fun k hk => ?_, ?_⟩
      · rw [← h10, hI.done .r10 List.mem_cons_self k (by omega_using []) hk, hge]
      · have := hI.frame
        rw [hm, List.map_singleton, h10] at this
        exact this
  refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from hz) (fun h => ?_) (fun h => ?_)
  · rw [sub_beq_zero32, decide_eq_true_eq] at h
    exact go _ ((gamma_cases hg).1 h)
  · rw [sub_beq_zero32, decide_eq_false_iff_not] at h
    exact go _ ((gamma_cases hg).2 h)

end VG.Proof.MlDsa.X86_64.Round

end

end

/-!
# ML-DSA on x86-64: `vg_mldsa_high_bits` and `vg_mldsa_low_bits`
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep gprPreserved_of)

theorem dShift_ge (g : Nat) : 1 ≤ dShift g := by unfold dShift; split <;> decide
theorem dShift_le (g : Nat) : dShift g ≤ 63 := by unfold dShift; split <;> decide

/-! ## The bodies -/

/-- The `r₁` the body of `highBits` stores. -/
def hbS (g : Nat) (x : BitVec 32) : BitVec 32 := BitVec.setWidth 32 (hbV g (BitVec.setWidth 64 x))

/-- The `r₀` the body of `lowBits` stores. -/
def lbS (g : Nat) (x : BitVec 32) : BitVec 32 :=
  BitVec.setWidth 32 (condAddV (BitVec.setWidth 64 x)
    (BitVec.ofNat 64 ((hbV g (BitVec.setWidth 64 x)).toNat * (BitVec.setWidth 64 (BitVec.ofNat 32 (2 * g))).toNat))
    qImm)

theorem hbBody_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (h1 : InRegions (s.rd ++ s.wr) (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 4)
    (h2 : InRegions s.wr (cfAddr (s.gpr .r10) (s.gpr .rcx)) 4) :
    WP isa (.block (hbBody g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      (s'.mem = s.mem.writeW (cfAddr (s.gpr .r10) (s.gpr .rcx))
          (hbS g (s.mem.readW (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32)) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdx, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by rcases hg with rfl | rfl <;> decide))
  unfold hbBody hb hbRaw condAdd
  xrun [h1, h2, ea_cf, List.cons_append, List.nil_append, hbS, hbV, hbRawV, condAddV, dShift_ge, dShift_le]
  rfl

theorem lbBody_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (h1 : InRegions (s.rd ++ s.wr) (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 4)
    (h2 : InRegions s.wr (cfAddr (s.gpr .r10) (s.gpr .rcx)) 4) :
    WP isa (.block (lbBody g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      (s'.mem = s.mem.writeW (cfAddr (s.gpr .r10) (s.gpr .rcx))
          (lbS g (s.mem.readW (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32)) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdx, .r8, .r11, .rcx] s s' := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by rcases hg with rfl | rfl <;> decide))
  unfold lbBody hb hbRaw condAdd
  xrun [h1, h2, ea_cf, List.cons_append, List.nil_append, lbS, hbV, hbRawV, condAddV, dShift_ge, dShift_le]
  rfl

/-! ## The values -/

theorem hbS_toNat {g : Nat} (h : g ∈ gamma2s) {x : BitVec 32} (hx : x.toNat < q) :
    (hbS g x).toNat = hbF g x.toNat % Proof.MlDsa.Round.hbM g := by
  have hx' : (BitVec.setWidth 64 x).toNat < q := by rw [setWidth64_toNat]; exact hx
  have hM : Proof.MlDsa.Round.hbM g ≤ 44 := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have := Nat.mod_lt (hbF g x.toNat) (show Proof.MlDsa.Round.hbM g > 0 by rcases mem_gamma2s h with rfl | rfl <;> decide)
  rw [hbS, BitVec.toNat_setWidth, hbV_toNat h hx', setWidth64_toNat]
  omega_arith

theorem lbS_toNat {g : Nat} (h : g ∈ gamma2s) {x : BitVec 32} (hx : x.toNat < q) :
    (lbS g x).toNat = (ofInt (lowBits g (Fin.ofNat q x.toNat))).val := by
  have hx' : (BitVec.setWidth 64 x).toNat < q := by rw [setWidth64_toNat]; exact hx
  have hv : (Fin.ofNat q x.toNat).val = x.toNat := Nat.mod_eq_of_lt hx
  rw [lowBits_val h, hv]
  have hM := hbM_mul h
  have hlt : hbF g x.toNat % Proof.MlDsa.Round.hbM g < Proof.MlDsa.Round.hbM g :=
    Nat.mod_lt _ (by rcases mem_gamma2s h with rfl | rfl <;> decide)
  have hle : hbF g x.toNat % Proof.MlDsa.Round.hbM g * (2 * g) ≤ q - 1 := by
    have := Nat.mul_le_mul_right (2 * g) (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hlt))
    have := Nat.mul_le_mul_right (2 * g) (Nat.le_of_lt hlt)
    rw [← hM]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
  have hg : 2 * g < 2 ^ 31 := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have e1 : (BitVec.ofNat 64 ((hbV g (BitVec.setWidth 64 x)).toNat *
      (BitVec.setWidth 64 (BitVec.ofNat 32 (2 * g))).toNat)).toNat =
      hbF g x.toNat % Proof.MlDsa.Round.hbM g * (2 * g) := by
    rw [BitVec.toNat_ofNat, hbV_toNat h hx', setWidth64_toNat, setWidth64_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 * g < 2 ^ 32 by omega_arith)]
    rw [q_eq] at hle
    omega_arith
  have hq : qImm.toNat = q := rfl
  rw [lbS, BitVec.toNat_setWidth, condAddV_toNat (by decide) (by rw [e1, hq, setWidth64_toNat]; omega_arith), e1, hq,
    setWidth64_toNat]
  rw [q_eq] at hx hle ⊢
  split <;> omega_arith

/-! ## The functions -/

section
variable {post : State → State → Prop} {s₀ : State} (hp : (bitsK post).pre s₀)
include hp

theorem bits_ok {body : Nat → List Instr} {F : Nat → List (BitVec 32) → BitVec 32} {clob : List Reg}
    (hfix : ∀ r ∈ [Reg.r10, .rdi], r ∉ clob) (hcx : .rcx ∈ clob)
    (hbody : ∀ g, (g = g32 ∨ g = g88) → ∀ s, (∀ p ∈ [Reg.rdi], InRegions (s.rd ++ s.wr) (cfAddr (s.gpr p) (s.gpr .rcx)) 4) →
      InRegions s.wr (cfAddr (s.gpr .r10) (s.gpr .rcx)) 4 →
      WP isa (.block (body g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
        (s'.mem = s.mem.writeW (cfAddr (s.gpr .r10) (s.gpr .rcx))
            (F g ([Reg.rdi].map fun p => s.mem.readW (cfAddr (s.gpr p) (s.gpr .rcx)) 32)) ∧
          s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep clob s s') :
    WP isa (.seq (.block (gammaCmp .rsi ++ ([.mov .r10 (.reg .rdx)] : List Instr))) (.ite .e (mapLoop (body g32)) (mapLoop (body g88))))
      s₀ fun s' =>
        (∀ k < 256, coeffAt s'.mem (s₀.gpr .rdx) k = F (arg32 s₀ .rsi) [coeffAt s₀.mem (s₀.gpr .rdi) k]) ∧
          Frame [pR (s₀.gpr .rdx)] s₀.mem s'.mem :=
  oneOut_ok (ins := [.rdi]) (fun p h => by simp only [List.mem_singleton] at h; subst h; rw [hp.1]; simp) hp.2.1
    (fun p h => by simp only [List.mem_singleton] at h; subst h; exact hp.2.2.1) hp.2.2.2.2.2.1
    (prologue_rsi_rdx s₀) (fun p h => by simp only [List.mem_singleton] at h; subst h; decide) hfix hcx hbody

end

theorem highBits_correct (s₀ : State) (hp : highBitsK.pre s₀) :
    ∃ t s', Exec isa highBits s₀ t s' ∧ abiPreserved s₀ s' ∧ highBitsK.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hv, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rsi, .r8, .r10]
    (bits_ok hp (F := fun g xs => hbS g (xs.headD 0)) (by decide) (by decide)
      fun g hg s h1 h2 => hbBody_ok hg s (h1 _ (List.mem_singleton_self _)) h2) (by decide)
  have hr : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf ?_), ?_⟩
  · simpa using hp.2.2.2.2.1
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [hv k hk, map_get _ _ hk, List.headD_cons, hbS_toNat hp.2.2.2.2.2.1 (hr k hk), highBits_eq hp.2.2.2.2.2.1,
      polyAt_val hr hk]
    exact (Int.toNat_natCast _).symm

theorem lowBits_correct (s₀ : State) (hp : lowBitsK.pre s₀) :
    ∃ t s', Exec isa lowBits s₀ t s' ∧ abiPreserved s₀ s' ∧ lowBitsK.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hv, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rsi, .r8, .r10, .r11]
    (bits_ok hp (F := fun g xs => lbS g (xs.headD 0)) (by decide) (by decide)
      fun g hg s h1 h2 => lbBody_ok hg s (h1 _ (List.mem_singleton_self _)) h2) (by decide)
  have hr : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf ?_), ?_⟩
  · simpa using hp.2.2.2.2.1
  · refine polyIs_of_toNat fun k hk => ?_
    rw [hv k hk, map_get _ _ hk, List.headD_cons, lbS_toNat hp.2.2.2.2.2.1 (hr k hk), polyAt_get _ _ hk]

/-- The pointers and `rsp` are public, and `γ₂`. -/
def bitsτ : X86_64.Taint.T := regsLo [.rdi, .rdx, .rsp] [.rsi]

theorem bits_agree {post : State → State → Prop} (s₁ s₂ : State) (_ : (bitsK post).pre s₁)
    (_ : (bitsK post).pre s₂) (hp : (bitsK post).pub s₁ s₂) : X86_64.Taint.Agree bitsτ s₁ s₂ :=
  agree_regsLo (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.2.2.2

theorem highBits_ct : ConstantTime isa highBitsK.pre highBitsK.pub highBits :=
  VG.Taint.constantTime (A := X86_64.taint) bitsτ bits_agree (by taint_decide)

theorem lowBits_ct : ConstantTime isa lowBitsK.pre lowBitsK.pub lowBits :=
  VG.Taint.constantTime (A := X86_64.taint) bitsτ bits_agree (by taint_decide)

/-- A state satisfying the precondition. -/
def bitsSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 95232 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x3000, 1024⟩]

theorem highBits_verified : Verified X86_64.target highBits (highBitsContract X86_64.abi) :=
  Verified.of_correct highBits_correct highBits_ct (by
    round_implies [highBitsContract, bitsSig, highBitsK, bitsK, X86_64.abi, X86_64.argRegs] [bitsSat]
      using bitsSat)

theorem lowBits_verified : Verified X86_64.target lowBits (lowBitsContract X86_64.abi) :=
  Verified.of_correct lowBits_correct lowBits_ct (by
    round_implies [lowBitsContract, bitsSig, lowBitsK, bitsK, X86_64.abi, X86_64.argRegs] [bitsSat]
      using bitsSat)

end VG.Proof.MlDsa.X86_64.Round
