module

public import VerifiedGarbage.Proof.MlDsa.Arm.Pack.BitPack
import VerifiedGarbage.Proof.MlKem.Arm.Add
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.MlDsa.Arm.Pack.BitPack
meta import VerifiedGarbage.Proof.MlKem.Arm.Add
meta import VerifiedGarbage.Proof.MlDsa.Pack.Arith
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
public import VerifiedGarbage.Proof.MlDsa.Arm.Round.Loop
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
meta import VerifiedGarbage.Proof.MlDsa.Arm.Round.Loop
meta import VerifiedGarbage.Proof.MlKem.Arm.Common
meta import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Basic
public import VerifiedGarbage.Proof.MlDsa.Round.Decompose
public import VerifiedGarbage.Impl.MlDsa.Arm.Round.Round
meta import Lean.Elab.Tactic.Omega.Frontend
import VerifiedGarbage.Proof.Framework.InstancePriority
import Batteries.Tactic.Init
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.MlDsa.Round.Decompose
meta import VerifiedGarbage.Impl.MlDsa.Arm.Round.Round
meta import VerifiedGarbage.Proof.Framework.InstancePriority
meta import Batteries.Tactic.Init
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Framework.Lit

/-! ### `MlDsa.Arm.Round.Bits`, which the modules that import this one used -/

section

/-! ### `MlDsa.Arm.Round.Hb`, which this module and modules that import it used -/

section

/-!
# ML-DSA on 32-bit ARM: the values of `Decompose`

What `hbRaw`, `csubM` and `hb` leave in their register, as functions on words
(`bhbRaw`, `bcsubM`, `bhb`), and their values: `f` (`bhbRaw_toNat`, from
`hbF_eq`) and `f mod m`, the `r₁` of `Decompose` (`bhb_toNat`), for both
values of `γ₂`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Round

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (q n Zq)
open VG.Proof.MlDsa (gamma2s)

/-- `γ₂` is one of the two values. -/
def G2 (g : Nat) : Prop := g = g32 ∨ g = g88

theorem G2.mem {g : Nat} (h : G2 g) : g ∈ gamma2s := by
  rcases h with rfl | rfl <;> decide

/-- What `csubM g r t` leaves in `r`. -/
def bcsubM (g : Nat) (x : BitVec 32) : BitVec 32 :=
  if g = 261888 then x - BitVec.ofNat 32 (dMod g) + (x - BitVec.ofNat 32 (dMod g)) >>> 31 <<< 4
  else x - BitVec.ofNat 32 (dMod g) + (x - BitVec.ofNat 32 (dMod g)) >>> 31 <<< 5 +
    (x - BitVec.ofNat 32 (dMod g)) >>> 31 <<< 3 + (x - BitVec.ofNat 32 (dMod g)) >>> 31 <<< 2

/-- What `hbRaw g x t` leaves in `x`. -/
def bhbRaw (g : Nat) (a : BitVec 32) : BitVec 32 :=
  ((a + 127) >>> 7 * (BitVec.ofNat 16 (dMul g)).setWidth 32 + BitVec.ofNat 32 (dAdd g)) >>> dShift g

/-- What `hb g x t` leaves in `x`. -/
def bhb (g : Nat) (a : BitVec 32) : BitVec 32 := bcsubM g (bhbRaw g a)

theorem hbM_dMod {g : Nat} (h : G2 g) : hbM g = dMod g := by rcases h with rfl | rfl <;> rfl

theorem bhbRaw_32 {a : BitVec 32} (ha : a.toNat < q) : (bhbRaw g32 a).toNat = hbF g32 a.toNat := by
  rw [hbF_eq (by decide) ha]
  have e1 : (BitVec.ofNat 16 (dMul g32)).setWidth 32 = (1025 : BitVec 32) := by decide
  have e2 : BitVec.ofNat 32 (dAdd g32) = (2097152 : BitVec 32) := by decide
  have e3 : dShift g32 = 22 := rfl
  have e4 : hbMul g32 = 1025 := rfl
  have e5 : hbAdd g32 = 2 ^ 21 := rfl
  have e6 : hbShift g32 = 22 := rfl
  unfold bhbRaw
  rw [e1, e2, e3, e4, e5, e6]
  rw [q_eq] at ha
  bv_omega

theorem bhbRaw_88 {a : BitVec 32} (ha : a.toNat < q) : (bhbRaw g88 a).toNat = hbF g88 a.toNat := by
  rw [hbF_eq (by decide) ha]
  have e1 : (BitVec.ofNat 16 (dMul g88)).setWidth 32 = (11275 : BitVec 32) := by decide
  have e2 : BitVec.ofNat 32 (dAdd g88) = (8388608 : BitVec 32) := by decide
  have e3 : dShift g88 = 24 := rfl
  have e4 : hbMul g88 = 11275 := rfl
  have e5 : hbAdd g88 = 2 ^ 23 := rfl
  have e6 : hbShift g88 = 24 := rfl
  unfold bhbRaw
  rw [e1, e2, e3, e4, e5, e6]
  rw [q_eq] at ha
  bv_omega

theorem bhbRaw_toNat {g : Nat} (hg : G2 g) {a : BitVec 32} (ha : a.toNat < q) :
    (bhbRaw g a).toNat = hbF g a.toNat := by
  rcases hg with rfl | rfl
  exacts [bhbRaw_32 ha, bhbRaw_88 ha]

theorem bcsubM_toNat {g : Nat} (hg : G2 g) {x : BitVec 32} (hx : x.toNat ≤ dMod g) :
    (bcsubM g x).toNat = x.toNat % dMod g := by
  unfold bcsubM
  rcases hg with rfl | rfl
  · rw [ite_eq_left (show g32 = 261888 from rfl), show dMod g32 = 16 from rfl] at *
    by_cases h : x.toNat < 16
    · rw [Nat.mod_eq_of_lt h]; bv_omega
    · bv_omega
  · rw [ite_eq_right (show ¬g88 = 261888 by decide), show dMod g88 = 44 from rfl] at *
    by_cases h : x.toNat < 44
    · rw [Nat.mod_eq_of_lt h]; bv_omega
    · bv_omega

/-- `r₁` of `Decompose(a)`. -/
theorem bhb_toNat {g : Nat} (hg : G2 g) {a : BitVec 32} (ha : a.toNat < q) :
    (bhb g a).toNat = hbF g a.toNat % hbM g := by
  unfold bhb
  rw [bcsubM_toNat hg (by rw [bhbRaw_toNat hg ha, ← hbM_dMod hg]; exact hbF_le hg.mem ha), bhbRaw_toNat hg ha,
    hbM_dMod hg]

theorem bhb_highBits {g : Nat} (hg : G2 g) (r : Zq) :
    (bhb g (BitVec.ofNat 32 r.val)).toNat = (VG.Spec.MlDsa.highBits g r).toNat := by
  have : r.val < 8380417 := r.isLt
  have e : (BitVec.ofNat 32 r.val).toNat = r.val := by rw [BitVec.toNat_ofNat]; omega_using [this]
  rw [bhb_toNat hg (by rw [e]; exact r.isLt), e, highBits_eq hg.mem, Int.toNat_natCast]

end VG.Proof.MlDsa.Arm.Round

end

end

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_high_bits` and `vg_mldsa_low_bits`

`γ₂` selects one of two loops (`bits_ok`); each loop body is symbolically
executed once for each value of `γ₂` (`hbBody_ok`, `lbBody_ok`), and its
values are those of `HighBits` and `LowBits` (`bhb_highBits`, `blb_lowBits`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Round.Bits

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round VG.Proof.MlDsa.Arm.Round
open VG.Spec.MlDsa (q n Poly Zq ofInt highBits lowBits)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs NatPolyIs natPolyAt gamma2s)
open VG.Proof.MlDsa.Arm.Arith.AddSub (fixS)
open VG.Impl.MlDsa.Arm.Arith (fixupS)
open VG.Proof.MlKem.Arm (cmp_z)

/-! ## Values -/

/-- `2γ₂`, as `load2g` builds it. -/
def w2g (g : Nat) : BitVec 32 :=
  BitVec.ofNat 16 (2 * g / 65536) ++ ((BitVec.ofNat 16 (2 * g % 65536)).setWidth 32).extractLsb' 0 16

theorem w2g_val {g : Nat} (hg : G2 g) : w2g g = BitVec.ofNat 32 (2 * g) := by
  rcases hg with rfl | rfl <;> decide

/-- What the body of `lowBits` stores. -/
def blb (g : Nat) (a : BitVec 32) : BitVec 32 := fixS (a - bhb g a * w2g g)

theorem blb_lowBits {g : Nat} (hg : G2 g) (r : Zq) :
    (blb g (BitVec.ofNat 32 r.val)).toNat = (ofInt (lowBits g r)).val := by
  have hr : r.val < 8380417 := r.isLt
  have e : (BitVec.ofNat 32 r.val).toNat = r.val := by rw [BitVec.toNat_ofNat]; omega_using [hr]
  have hb := bhb_toNat hg (a := BitVec.ofNat 32 r.val) (by rw [e]; exact r.isLt)
  rw [e] at hb
  have hm := hbM_mul hg.mem
  have hlt : hbF g r.val % hbM g < hbM g := Nat.mod_lt _ (by rcases hg with rfl | rfl <;> decide)
  have hX : hbF g r.val % hbM g * (2 * g) ≤ q - 1 - 2 * g := by
    have := Nat.mul_le_mul_right (2 * g) (Nat.le_sub_one_of_lt hlt)
    rw [Nat.sub_mul, Nat.one_mul, hm] at this; exact this
  have hg' : 2 * g < 2 ^ 20 := by rcases hg with rfl | rfl <;> decide
  unfold blb fixS
  rw [lowBits_val hg.mem, w2g_val hg]
  generalize bhb g (BitVec.ofNat 32 r.val) = B at hb
  generalize hbF g r.val % hbM g = f at hb hlt hX
  generalize r.val = v at *
  rw [q_eq] at hX ⊢
  have hBm : (B * BitVec.ofNat 32 (2 * g)).toNat = f * (2 * g) := by
    rw [BitVec.toNat_mul, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 * g) (by omega_using [hg'])]
    exact Nat.mod_eq_of_lt (by omega_using [hX])
  generalize B * BitVec.ofNat 32 (2 * g) = X at hBm
  generalize f * (2 * g) = x at hBm hX
  split <;> bv_omega

/-! ## The bodies -/

section
variable {s : State} {x w c : BitVec 32} (h0 : s.gpr .r0 = x) (h1 : s.gpr .r1 = c) (h2 : s.gpr .r2 = w)
  (iR : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
  (oO : InRegions s.wr (State.addr (w + BitVec.ofNat 32 0)) 4)
include h0 h1 h2 iR oO

/-- What a body does, for the value `v` of the coefficient it reads. -/
def BStep (s : State) (x w c v : BitVec 32) (s' : State) : Prop :=
  s'.mem = s.mem.writeW (State.addr (w + BitVec.ofNat 32 0)) v ∧ s'.gpr .r0 = x + 4 ∧ s'.gpr .r2 = w + 4 ∧
    s'.gpr .r1 = c - 1 ∧ s'.z = (c - 1 == 0) ∧
    (∀ r ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr], s'.gpr r = s.gpr r) ∧
    s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem hbBody_ok {g : Nat} (hg : G2 g) :
    WP isa (.block (hbBody g)) s (BStep s x w c (bhb g (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32))) := by
  rcases hg with rfl | rfl <;>
  · run_block [hbBody, hb, hbRaw, csubM, addMaskM, tail02, BStep, bhb, bcsubM, bhbRaw, h0, h1, h2, iR, oO,
      List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

theorem lbBody_ok {g : Nat} (hg : G2 g) :
    WP isa (.block (lbBody g)) s (BStep s x w c (blb g (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32))) := by
  rcases hg with rfl | rfl <;>
  · run_block [lbBody, hb, hbRaw, csubM, addMaskM, load2g, fixupS, tail02, BStep, blb, fixS, w2g, bhb, bcsubM,
      bhbRaw, h0, h1, h2, iR, oO, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self,
      and_true]

end

/-! ## The loops -/

/-- The precondition of both functions, on entry. -/
structure Pre (s : State) : Prop where
  rd : s.rd = [pR (P s .r0)]
  wr : s.wr = [pR (P s .r2)]
  d : (pR (P s .r0)).Disjoint (pR (P s .r2))
  f0 : (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32
  g : (s.gpr .r1).toNat ∈ gamma2s
  red : Reduced s.mem (P s .r0)

/-- The registers the loops keep. -/
abbrev fixedR : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

theorem layout {s : State} (hp : Pre s) : Layout s [.r0] [.r2] := by
  refine ⟨fun p hp' => ?_, fun o ho => ?_, fun p hp' o ho => ?_, List.pairwise_singleton _ _, fun p hp' => ?_⟩
  · simp only [List.mem_singleton] at hp'; subst hp'; rw [hp.rd]; simp
  · simp only [List.mem_singleton] at ho; subst ho; rw [hp.wr]; simp
  · simp only [List.mem_singleton] at hp' ho; subst hp' ho; exact hp.d
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    exacts [hp.f0, hp.f2]

/-- A loop, with the body `B g` that stores `F (a)` for each coefficient `a`. -/
theorem bits_loop {s s₁ : State} (hp : Pre s) {B : List Instr} {F : BitVec 32 → BitVec 32}
    (hB : ∀ {s : State} {x w c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = c → s.gpr .r2 = w →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (w + BitVec.ofNat 32 0)) 4 →
      WP isa (.block B) s (BStep s x w c (F (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32))))
    (hg : s₁.gpr = s.gpr) (hm : s₁.mem = s.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) (hsp : s₁.sp = s.sp) :
    WP isa (mapLoop .r1 B) s₁ fun s' => (∀ r ∈ fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      ∀ k < 256, coeffAt s'.mem (P s .r2) k = F (coeffAt s.mem (P s .r0) k) := by
  have e : ∀ r, P s₁ r = P s r := fun r => by simp only [P, hg]
  have hp₁ : Pre s₁ := ⟨by rw [hrd, e, hp.rd], by rw [hwr, e, hp.wr], by rw [e, e]; exact hp.d,
    by rw [hg]; exact hp.f0, by rw [hg]; exact hp.f2, by rw [hg]; exact hp.g, by rw [hm, e]; exact hp.red⟩
  have hL := layout hp₁
  refine WP.mono (loop_ok (ptrs := [.r0, .r2]) (fixed := fixedR) (V := fun _ i => F (coeffAt s₁.mem (P s₁ .r0) i))
    (J := fun _ _ => True) hL (by decide) (by decide) (fun _ _ _ => trivial) fun i hi s' hI => ?_)
    fun s' hI => ⟨fun r hr => (hI.fixed r hr).trans (congrFun hg r), hI.sp.trans hsp, fun k hk => ?_⟩
  · refine WP.mono (hB rfl rfl rfl (hI.inR hL hi (by simp) (by simp)) (hI.inW hL hi (by simp) (by simp)))
      fun s'' ⟨hm', r0, r2, r1, hz, hf, rd, wr, sp⟩ => ⟨?_, ?_, r1, hz, hf, rd, wr, sp, trivial⟩
    · rw [hm', hI.read hL hi (by simp) (by simp), hI.addr hL hi (p := .r2) (by simp) (by simp)]; rfl
    · intro p hp'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl
      exacts [r0, r2]
  · rw [← e, ← e, hI.done .r2 (by simp) k hk, hm]

/-- The comparison of `γ₂` and the two loops. -/
theorem bits_ok {s : State} (hp : Pre s) {B : Nat → List Instr} {F : Nat → BitVec 32 → BitVec 32}
    (hB : ∀ g, G2 g → ∀ {s : State} {x w c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = c → s.gpr .r2 = w →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (w + BitVec.ofNat 32 0)) 4 →
      WP isa (.block (B g)) s (BStep s x w c (F g (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)))) :
    WP isa (.seq (.block [gammaCmp .r1]) (.ite .eq (mapLoop .r1 (B g88)) (mapLoop .r1 (B g32)))) s fun s' =>
      (∀ r ∈ fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      ∀ k < 256, coeffAt s'.mem (P s .r2) k = F (s.gpr .r1).toNat (coeffAt s.mem (P s .r0) k) := by
  have he : encodable (BitVec.ofNat 32 g88) = true := by decide
  refine WP.seq (WP.of_runBlock ⟨_, by
    simp only [gammaCmp, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, he, ite_true, Option.map_some]
    rfl, ?_⟩)
  have hz := cmp_z (s.gpr .r1) g88 (by decide)
  refine WP.ite (decide ((s.gpr .r1).toNat = g88)) (by simp only [eval, subFlags, hz]) (fun h => ?_)
    (fun h => ?_)
  · have e : (s.gpr .r1).toNat = g88 := of_decide_eq_true h
    rw [e]
    exact bits_loop hp (hB g88 (.inr rfl)) rfl rfl rfl rfl rfl
  · have e : (s.gpr .r1).toNat = g32 := by
      have := of_decide_eq_false h
      rcases mem_gamma2s hp.g with h' | h'
      · exact absurd h' this
      · exact h'
    rw [e]
    exact bits_loop hp (hB g32 (.inl rfl)) rfl rfl rfl rfl rfl

/-! ## Verified -/

theorem pre_high {s : State} (h : (Proof.MlDsa.highBitsContract Arm.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.highBitsContract, Proof.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem pre_low {s : State} (h : (Proof.MlDsa.lowBitsContract Arm.abi).pre s) : Pre s := by
  sig_pre [Proof.MlDsa.lowBitsContract, Proof.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem preserved_of {s s' : State} (h : ∀ r ∈ fixedR, s'.gpr r = s.gpr r) :
    ∀ r ∈ preserved, s'.gpr r = s.gpr r := fun r hr => h r (by revert r; decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 95232 | .r2 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := [⟨0x2000, 1024⟩]

theorem ct {k : Contract isa} {c : Prog isa} (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → s₁.gpr .r0 = s₂.gpr .r0 ∧
      (s₁.gpr .r1).setWidth 32 = (s₂.gpr .r1).setWidth 32 ∧ s₁.gpr .r2 = s₂.gpr .r2)
    {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs [.r0, .r1, .r2]) c hc).isSome = true) :
    ConstantTime isa k.pre k.pub c :=
  VG.Proof.MlDsa.Arm.Arith.AddSub.ctRegs [.r0, .r1, .r2] (fun s₁ s₂ hp r hr => by
    obtain ⟨h0, h1, h2⟩ := hpub s₁ s₂ hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h0
    · simpa using h1
    · exact h2) h

theorem high_verified :
    Verified Arm.target Impl.MlDsa.Arm.Round.highBits (Proof.MlDsa.highBitsContract Arm.abi) := by
  refine ⟨fun s hs => ?_, ct (fun s₁ s₂ h => ?_) (by native_taint_decide), ?_⟩
  · have hp := pre_high hs
    obtain ⟨t, s', he, hf, hsp, hk⟩ := bits_ok hp (B := hbBody) (F := bhb) fun g hg _ _ _ _ h0 h1 h2 iR oO => hbBody_ok h0 h1 h2 iR oO hg
    refine ⟨t, s', he, ⟨preserved_of hf, hsp⟩, ?_⟩
    sig_post [Proof.MlDsa.highBitsContract, Proof.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    refine natPolyIs_of_toNat fun k hk' => ?_
    have hr := hp.red k hk'
    show (coeffAt s'.mem (P s .r2) k).toNat = ((polyAt s.mem (P s .r0)).map _)[k]!
    rw [hk k hk', map_get _ _ hk', polyAt_get _ _ hk', ← bhb_highBits (mem_gamma2s hp.g |>.elim .inr .inl),
      word_of_reduced hr]
  · sig_pub [Proof.MlDsa.highBitsContract, Proof.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2⟩ := h
    exact ⟨h0, by rw [h1], h2⟩
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.highBitsContract, Proof.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

theorem low_verified :
    Verified Arm.target Impl.MlDsa.Arm.Round.lowBits (Proof.MlDsa.lowBitsContract Arm.abi) := by
  refine ⟨fun s hs => ?_, ct (fun s₁ s₂ h => ?_) (by native_taint_decide), ?_⟩
  · have hp := pre_low hs
    obtain ⟨t, s', he, hf, hsp, hk⟩ := bits_ok hp (B := lbBody) (F := blb)
      fun g hg _ _ _ _ h0 h1 h2 iR oO => lbBody_ok h0 h1 h2 iR oO hg
    refine ⟨t, s', he, ⟨preserved_of hf, hsp⟩, ?_⟩
    sig_post [Proof.MlDsa.lowBitsContract, Proof.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    refine polyIs_of_toNat fun k hk' => ?_
    have hr := hp.red k hk'
    show (coeffAt s'.mem (P s .r2) k).toNat = (((polyAt s.mem (P s .r0)).map _)[k]! : Zq).val
    rw [hk k hk', map_get _ _ hk', polyAt_get _ _ hk', ← blb_lowBits (mem_gamma2s hp.g |>.elim .inr .inl),
      word_of_reduced hr]
  · sig_pub [Proof.MlDsa.lowBitsContract, Proof.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2⟩ := h
    exact ⟨h0, by rw [h1], h2⟩
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Proof.MlDsa.lowBitsContract, Proof.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _

end VG.Proof.MlDsa.Arm.Round.Bits

end

end

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_bit_unpack` and `vg_mldsa_unpack_t1`

The coefficient of a field `y` is `b - y`, plus `q` if that is negative
(`bm`), which is `b - y` in `ℤ_q` (`Pack/Arith.lean`), or `y · 2¹³`. The loop
is proven once for every width (`unpackLoop_ok`); `unpackLoop_buFin_ok` states
what the loop of `buFin B` does for any state, which `vg_mldsa_bit_unpack` (by
its five cases, in its frame) and ExpandMask use.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Pack

open VG VG.Arm VG.Impl.MlDsa.Arm.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (bytesAt_frame)
open VG.Proof.MlDsa.Pack

/-! ## The coefficients -/

/-- The word `buFin B` stores for the field `y`. -/
abbrev buWord (B y : Nat) : BitVec 32 := bm (BitVec.ofNat 32 B) (BitVec.ofNat 32 y)

theorem buFin_ok {B : Nat} (hB : encodable (BitVec.ofNat 32 B) = true) (d : Nat) : FinOk (buFin B) d (buWord B) :=
  fun j s hj hout _ => by
    refine WP.keep _ ?_ rfl
    unfold buFin bMinus addQNeg
    run_block [hj, hout, hB, buWord, bm, BitVec.ofNat_toNat, BitVec.setWidth_eq, and_true]

/-- The word `t1Fin` stores for the field `y`. -/
abbrev t1Word (y : Nat) : BitVec 32 := BitVec.ofNat 32 y <<< 13

theorem t1Fin_ok : FinOk t1Fin 10 t1Word := fun j s hj hout _ => by
  refine WP.keep _ ?_ rfl
  unfold t1Fin
  run_block [hj, hout, t1Word, BitVec.ofNat_toNat, BitVec.setWidth_eq, and_true]

/-- A field of `d ≤ 20` bits of the input. -/
theorem field_lt (X d k : Nat) (hd : d ≤ 20) : X / 2 ^ (d * k) % 2 ^ d < 2 ^ 20 :=
  Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos d)) (Nat.pow_le_pow_right (by decide) hd)

/-! ## The loop of `BitUnpack`, for any state

`unpackLoop (buFin B) d c nb` for `BitUnpack(v, a, B)` with `bitlen (a + B) = d`
(ExpandMask runs it for `(B, d, c, nb)` = `(2¹⁷, 18, 4, 9)` and
`(2¹⁹, 20, 2, 5)`, with `a = B - 1`), from any state in which `r0` holds
the address of `32 d` readable bytes and `r1` that of a writable
polynomial, disjoint and not wrapping around: it writes `BitUnpack` of the
bytes to the polynomial, reduced, and changes nothing else but the
registers `r0`–`r4` and `r12` (`unpackRegs`) and the flags.
-/

theorem unpackLoop_buFin_ok {B d c nb : Nat} (hs : Shape d c nb) (hB : encodable (BitVec.ofNat 32 B) = true)
    (hB19 : B ≤ 2 ^ 19) {a : Nat} (hd : bitlen (a + B) = d) {s : State}
    (hin : (⟨State.addr (s.gpr .r0), 32 * d⟩ : Region) ∈ s.rd ++ s.wr)
    (hout : polyRegion (State.addr (s.gpr .r1)) ∈ s.wr)
    (hsep : Region.Disjoint ⟨State.addr (s.gpr .r0), 32 * d⟩ (polyRegion (State.addr (s.gpr .r1))))
    (fitV : (s.gpr .r0).toNat + 32 * d ≤ 2 ^ 32) (fitP : (s.gpr .r1).toNat + 1024 ≤ 2 ^ 32) :
    WP isa (unpackLoop (buFin B) d c nb) s fun s' =>
      PolyIs s'.mem (State.addr (s.gpr .r1)) (toRq (bitUnpack (bytesAt s.mem (State.addr (s.gpr .r0)) (32 * d)) a B)) ∧
        Frame [polyRegion (State.addr (s.gpr .r1))] s.mem s'.mem ∧ Keep unpackRegs s s' := by
  refine WP.mono (unpackLoop_ok (buFin_ok hB d) hs hin hout hsep fitV fitP rfl rfl rfl rfl rfl)
    fun s' ⟨hc, hf, hk⟩ => ⟨?_, hf, hk⟩
  have hq := q_eq
  refine polyIs_of_toNat fun i hi => ?_
  have hy := field_lt (inNum s.mem (State.addr (s.gpr .r0)) d) d i hs.d20
  have hy' := hy
  unfold inNum at hy'
  rw [hc i hi, buWord, bm_toNat (by rw [BitVec.toNat_ofNat]; omega_arith) (by rw [BitVec.toNat_ofNat]; omega_arith),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show B < 2 ^ 32 by omega_arith),
    Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega_arith), toRq, Vector.getElem_map, bitUnpack_get _ _ _ hi, hd,
    ofInt_sub (by omega_arith)]

/-! ## `vg_mldsa_bit_unpack` -/

theorem ldrSp_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 4) :
    WP isa (.block [.ldrSp .r12 0]) s fun s' =>
      (s'.gpr .r12 = stackArg s 0 ∧ s'.mem = s.mem) ∧ Keep [.r12] s s' := by
  have h' : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 0)) 4 := h
  refine WP.keep _ ?_ rfl
  run_block [h', and_true]
  rfl

theorem buPro_ok (s : State) :
    WP isa (.block [.mov .r1 (.reg .r12)]) s fun s' => (s'.gpr .r1 = s.gpr .r12 ∧ s'.mem = s.mem) ∧ Keep [.r1] s s' := by
  refine WP.keep _ ?_ rfl
  run_block [and_true]

/-- What `bitUnpack` leaves. -/
def BuPost (s₀ s' : State) : Prop :=
  PolyIs s'.mem (State.addr (stackArg s₀ 0))
    (toRq (bitUnpack (bytesAt s₀.mem (State.addr (s₀.gpr .r0)) (s₀.gpr .r1).toNat) (s₀.gpr .r2).toNat
      (s₀.gpr .r3).toNat)) ∧ abiPreserved s₀ s'

theorem bu_wp {s₀ : State} (hp : BuPre s₀) : WP isa Impl.MlDsa.Arm.Pack.bitUnpack s₀ (BuPost s₀) := by
  unfold Impl.MlDsa.Arm.Pack.bitUnpack
  refine WP.seq (WP.mono (ldrSp_ok s₀ ⟨_, by rw [hp.rd]; simp, Region.contains_self _ _⟩)
    fun s₁ ⟨⟨g₁, m₁⟩, k₁⟩ => ?_)
  have sp₁ : s₁.sp = s₀.sp := k₁.2.2.2
  have hsp : 4 ≤ s₁.sp.toNat := by rw [sp₁]; exact hp.sp4
  have eb : below4 s₁ = below4 s₀ := by rw [below4, below4, sp₁]
  refine WP.frame (rs := [.r4]) (r := .r4) rfl (by simpa using hsp) (by decide) ?_
  refine WP.seq (WP.mono (buPro_ok _) fun s₂ ⟨⟨g₂, m₂⟩, k₂⟩ => ?_)
  have ab := mem_bitPackParams hp.ab
  have g0 : ∀ r, r ≠ .r12 → r ≠ .r1 → s₂.gpr r = s₀.gpr r := fun r h12 h1 => by
    rw [k₂.gpr (by simp [h1]), pushed_gpr, k₁.gpr (by simp [h12])]
  have go : ∀ {d c nb B : Nat}, Shape d c nb → (s₀.gpr .r3).toNat = B → B ≤ 2 ^ 19 →
      encodable (BitVec.ofNat 32 B) = true → bitlen ((s₀.gpr .r2).toNat + B) = d → ∀ s : State, Same s₂ s →
      WP isa (unpackLoop (buFin B) d c nb) s fun s₃ => ∀ m u,
        Frame [⟨State.addr (s₁.sp - BitVec.ofNat 32 (4 * [Reg.r4].length)), 4 * [Reg.r4].length⟩] s₃.mem m →
          BuPost s₀ { popped .r4 4 s₃ with mem := m, unknowns := u } := by
    intro d c nb B hs hB hB19 hBe hd s hS
    have hlen := hp.len
    rw [hB, hd] at hlen
    have x0 : s.gpr .r0 = s₀.gpr .r0 := by rw [hS.1, g0 _ (by decide) (by decide)]
    have x1 : s.gpr .r1 = stackArg s₀ 0 := by rw [hS.1, g₂, pushed_gpr, g₁]
    have xrd : s.rd = s₀.rd := by rw [hS.2.2.1, k₂.2.1, pushed_rd, k₁.2.1]
    have xwr : s.wr = ⟨State.addr (s₁.sp - BitVec.ofNat 32 (4 * [Reg.r4].length)), 4 * [Reg.r4].length⟩ :: s₀.wr := by
      rw [hS.2.2.2.1, k₂.2.2.1, pushed_wr, k₁.2.2.1]
    have xm : s.mem = (pushed [.r4] s₁).mem := by rw [hS.2.1, m₂]
    refine WP.mono (unpackLoop_buFin_ok (s := s) hs hBe hB19 hd
      (by rw [x0, xrd, hp.rd, ← hlen]; exact List.mem_append_left _ (List.mem_cons_self ..))
      (by rw [x1, xwr, hp.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
      (by rw [x0, x1, ← hlen]; exact hp.disj) (by rw [x0, ← hlen]; exact hp.fitV) (by rw [x1]; exact hp.fitP))
      fun s₃ ⟨hpoly, hf, hk⟩ mL uL hfl => ⟨?_, ⟨fun r hr => ?_, ?_⟩⟩
    · dsimp only
      rw [← x1, hlen]
      rw [x0, xm, bytesAt_frame (pushed4_frame hsp) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [eb, ← hlen]; exact hp.bV.symm) (by omega_arith), m₁,
        ← hB] at hpoly
      -- The polynomial is apart from the released frame.
      have e4 : State.addr (s₁.sp - BitVec.ofNat 32 (4 * [Reg.r4].length)) = State.addr s₁.sp - 4 := addr_sub hsp
      rw [e4] at hfl
      have hd : ∀ r ∈ [below4 s₁], (polyRegion (State.addr (s.gpr .r1))).Disjoint r := fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [x1, eb]; exact hp.bP.symm
      exact polyIs_of_toNat fun i hi => by
        rw [coeffAt_frame hfl hd hi, ← polyAt_val hpoly.1 hi, hpoly.2]
    · -- The registers: `r4` from the frame, the others kept.
      have hsp₃ : s₃.sp = s₁.sp - 4 := by rw [hk.2.2.2, hS.2.2.2.2, k₂.2.2.2, pushed4_sp]
      dsimp only
      by_cases h4 : r = .r4
      · subst h4
        rw [(popped4 hsp hsp₃ ?_).1, k₁.gpr (by decide)]
        rw [hf.readW (r := below4 s₁) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [x1, eb]; exact hp.bP) (by decide),
          xm, pushed4_mem hsp, Mem.readW_writeW_self32]
      · have hr' : r ∉ unpackRegs := by
          simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl h4 | decide
        have h12 : r ≠ .r12 := fun e => hr' (by rw [e]; decide)
        have h1 : r ≠ .r1 := fun e => hr' (by rw [e]; decide)
        rw [popped_gpr h4, hk.gpr hr', hS.1, g0 r h12 h1]
    · have hsp₃ : s₃.sp = s₁.sp - 4 := by rw [hk.2.2.2, hS.2.2.2.2, k₂.2.2.2, pushed4_sp]
      dsimp only
      rw [popped_sp, hsp₃, ← sp₁]; exact BitVec.sub_add_cancel _ _
  have e3 : ∀ s, Same s₂ s → (s.gpr .r3).toNat = (s₀.gpr .r3).toNat := fun s h => by
    rw [h.1, g0 _ (by decide) (by decide)]
  refine sel_ok .r3 2 (by decide) (by decide) _ _ s₂ (fun s₃ h₃ e => ?_) (fun s₃ h₃ n2 => ?_)
  · rw [e3 s₂ ⟨rfl, rfl, rfl, rfl, rfl⟩] at e
    exact go (d := 3) (c := 8) (nb := 3) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r2).toNat = 2 by omega_arith]; decide) s₃ h₃
  rw [e3 s₂ ⟨rfl, rfl, rfl, rfl, rfl⟩] at n2
  refine sel_ok .r3 4 (by decide) (by decide) _ _ s₃ (fun s₄ h₄ e => ?_) (fun s₄ h₄ n4 => ?_)
  · rw [e3 s₃ h₃] at e
    exact go (d := 4) (c := 2) (nb := 1) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r2).toNat = 4 by omega_arith]; decide) s₄ (h₃.trans h₄)
  rw [e3 s₃ h₃] at n4
  refine sel_ok .r3 4096 (by decide) (by decide) _ _ s₄ (fun s₅ h₅ e => ?_) (fun s₅ h₅ n4096 => ?_)
  · rw [e3 s₄ (h₃.trans h₄)] at e
    exact go (d := 13) (c := 8) (nb := 13) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r2).toNat = 4095 by omega_arith]; decide) s₅ ((h₃.trans h₄).trans h₅)
  rw [e3 s₄ (h₃.trans h₄)] at n4096
  refine sel_ok .r3 131072 (by decide) (by decide) _ _ s₅ (fun s₆ h₆ e => ?_) (fun s₆ h₆ n17 => ?_)
  · rw [e3 s₅ ((h₃.trans h₄).trans h₅)] at e
    exact go (d := 18) (c := 4) (nb := 9) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r2).toNat = 131071 by omega_arith]; decide) s₆ (((h₃.trans h₄).trans h₅).trans h₆)
  · rw [e3 s₅ ((h₃.trans h₄).trans h₅)] at n17
    have e : (s₀.gpr .r3).toNat = 524288 := by omega_arith
    exact go (d := 20) (c := 2) (nb := 5) (by constructor <;> decide) e (by decide) (by decide)
      (by rw [show (s₀.gpr .r2).toNat = 524287 by omega_arith]; decide) s₆ (((h₃.trans h₄).trans h₅).trans h₆)

theorem relct_ldrSp {P : State → State → Prop} {t : Reg} {off : Nat} (hsp : ∀ a b, P a b → a.sp = b.sp) :
    RelCT isa P (.block [.ldrSp t off]) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  have tr : ∀ {s s' : State} {tr : List Leak}, execBlock isa [.ldrSp t off] s = some (s', tr) →
      tr = [Leak.addr (State.addr (s.sp + BitVec.ofNat 32 off))] := fun {s s' tr} e => by
    simp only [execBlock] at e
    split at e
    · cases e
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.2]; rfl
  rw [tr e₁, tr e₂, hsp _ _ hp]
  exact ⟨rfl, trivial⟩

theorem bitUnpack_ct :
    ConstantTime isa (bitUnpackContract Arm.abi 4).pre (bitUnpackContract Arm.abi 4).pub
      Impl.MlDsa.Arm.Pack.bitUnpack := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp₁ hp₂ hpub e₁ e₂
  have q₁ := BuPre.of hp₁
  have q₂ := BuPre.of hp₂
  sig_pub [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
  obtain ⟨hsp, h0, h1, h2, h3, harg⟩ := hpub
  have A := (relct_ldrSp (t := .r12) (off := 0) (P := fun a b => a = s₁ ∧ b = s₂)
    (fun a b h => by rw [h.1, h.2]; exact hsp)).wp
    (F₁ := fun (a : State) => (a.gpr .r12 = stackArg s₁ 0 ∧ a.mem = s₁.mem) ∧ Keep [.r12] s₁ a)
    (F₂ := fun (a : State) => (a.gpr .r12 = stackArg s₂ 0 ∧ a.mem = s₂.mem) ∧ Keep [.r12] s₂ a)
    fun a b h => by
      rw [h.1, h.2]
      exact ⟨ldrSp_ok s₁ ⟨_, by rw [q₁.rd]; simp, Region.contains_self _ _⟩,
        ldrSp_ok s₂ ⟨_, by rw [q₂.rd]; simp, Region.contains_self _ _⟩⟩
  have B := frame4_ct (body := bitUnpackBody) [.r0, .r1, .r2, .r3, .r12] (by native_taint_decide)
    (P := fun a b => True ∧ ((a.gpr .r12 = stackArg s₁ 0 ∧ a.mem = s₁.mem) ∧ Keep [.r12] s₁ a) ∧
      ((b.gpr .r12 = stackArg s₂ 0 ∧ b.mem = s₂.mem) ∧ Keep [.r12] s₂ b))
    (fun a b ⟨_, ⟨_, ka⟩, ⟨_, kb⟩⟩ => by rw [ka.2.2.2, kb.2.2.2]; exact hsp)
    (fun a b ⟨_, ⟨⟨a12, _⟩, ka⟩, ⟨⟨b12, _⟩, kb⟩⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [ka.gpr (by decide), kb.gpr (by decide)]; exact h0
      · rw [ka.gpr (by decide), kb.gpr (by decide)]; exact h1
      · rw [ka.gpr (by decide), kb.gpr (by decide)]; exact h2
      · rw [ka.gpr (by decide), kb.gpr (by decide)]; exact h3
      · rw [a12, b12]; exact harg)
  exact ((A.seq B) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying the precondition: `f` = `0x2000` on the stack. -/
def buSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 96 | .r2 => 2 | .r3 => 2 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x4001 then 0x20 else 0
  rd := [⟨0x1000, 96⟩, ⟨0x4000, 4⟩]
  wr := [⟨0x2000, 1024⟩]

example : ∃ pre post leak, bitUnpackContract Arm.abi 4 =
    bitUnpackSig.contract Arm.target.abi pre post true 4 leak := ⟨_, _, _, rfl⟩

theorem bitUnpack_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.bitUnpack (bitUnpackContract Arm.abi 4) := by
  refine ⟨fun s hs => ?_, bitUnpack_ct, ?_⟩
  · obtain ⟨t, s', he, hb, habi⟩ := bu_wp (BuPre.of hs)
    refine ⟨t, s', he, habi, ?_⟩
    sig_post [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact hb
  · refine ⟨buSat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [bitUnpackContract, bitUnpackSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | (simp only [bitPackParams]; decide +kernel)
        | decide +kernel

/-! ## `vg_mldsa_unpack_t1` -/

theorem t1_wp {s₀ : State} (hp : T1Pre s₀) :
    WP isa Impl.MlDsa.Arm.Pack.unpackT1 s₀ fun s' =>
      PolyIs s'.mem (State.addr (s₀.gpr .r1))
        ((simpleBitUnpack (bytesAt s₀.mem (State.addr (s₀.gpr .r0)) 320) t1Max).map fun c => ofInt (c * 2 ^ d : Nat)) ∧
        Keep unpackRegs s₀ s' := by
  refine WP.mono (unpackLoop_ok t1Fin_ok (c := 4) (nb := 5) (by constructor <;> decide) (pv := s₀.gpr .r0)
    (pp := s₀.gpr .r1) (m₀ := s₀.mem) (rd := s₀.rd) (wr := s₀.wr)
    (by rw [hp.rd]; exact List.mem_append_left _ (List.mem_singleton_self _))
    (by rw [hp.wr]; exact List.mem_singleton_self _) hp.disj hp.fitV hp.fitP rfl rfl rfl rfl rfl)
    fun s' ⟨hc, _, hk⟩ => ⟨?_, hk⟩
  refine polyIs_of_toNat fun i hi => ?_
  have hy : inNum s₀.mem (State.addr (s₀.gpr .r0)) 10 / 2 ^ (10 * i) % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (by decide)
  rw [hc i hi, t1Word, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega_arith), Nat.mod_eq_of_lt (show _ < 2 ^ 32 by omega_arith), Vector.getElem_map,
    simpleBitUnpack_get _ _ hi, show bitlen t1Max = 10 by decide, ofInt_t1 hy]

/-- `unpackT1` writes no register the ABI preserves. -/
theorem t1_preserves : ∀ r ∈ preserved, ∀ i ∈ instrs Impl.MlDsa.Arm.Pack.unpackT1, clobbers i r = false := by
  have h : (instrs Impl.MlDsa.Arm.Pack.unpackT1).all
      (fun i => preserved.all fun r => !clobbers i r) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using this

/-- A state satisfying the precondition. -/
def t1Sat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 320⟩]
  wr := [⟨0x2000, 1024⟩]

example : ∃ pre post leak, unpackT1Contract Arm.abi =
    unpackT1Sig.contract Arm.target.abi pre post true 0 leak := ⟨_, _, _, rfl⟩

theorem unpackT1_verified :
    Verified Arm.target Impl.MlDsa.Arm.Pack.unpackT1 (unpackT1Contract Arm.abi) := by
  refine ⟨fun s hs => ?_, Proof.MlKem.Arm.Add.ctRegs [.r0, .r1] (fun s₁ s₂ h => ?_) (by native_taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpost, hk⟩ := t1_wp (T1Pre.of hs)
    refine ⟨t, s', he, ⟨fun r hr => Exec.gpr (t1_preserves r hr) he, hk.2.2.2⟩, ?_⟩
    sig_post [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact hpost
  · sig_pub [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨-, h0, h1⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · refine ⟨t1Sat, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [unpackT1Contract, unpackT1Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals decide +kernel

end VG.Proof.MlDsa.Arm.Pack
