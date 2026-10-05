import VerifiedGarbage.Proof.MlDsa.Arm.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Round.Hb`. -/
section

/-!
# ML-DSA on 32-bit ARM: the values of `Decompose`

What `hbRaw`, `csubM` and `hb` leave in their register, as functions on words
(`bhbRaw`, `bcsubM`, `bhb`), and their values: `f` (`bhbRaw_toNat`, from
`hbF_eq`) and `f mod m`, the `r₁` of `Decompose` (`bhb_toNat`), for both
values of `γ₂`.
-/

namespace VG.Proof.MlDsa.Arm.Round

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa (q n Zq gamma2s)

/-- `γ₂` is one of the two values. -/
def G2 (g : Nat) : Prop := g = g32 ∨ g = g88

theorem G2.mem {g : Nat} (h : VG.Proof.MlDsa.Arm.Round.G2 g) : g ∈ gamma2s := by
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
def bhb (g : Nat) (a : BitVec 32) : BitVec 32 := VG.Proof.MlDsa.Arm.Round.bcsubM g (VG.Proof.MlDsa.Arm.Round.bhbRaw g a)

theorem hbM_dMod {g : Nat} (h : VG.Proof.MlDsa.Arm.Round.G2 g) : hbM g = dMod g := by rcases h with rfl | rfl <;> rfl

theorem bhbRaw_32 {a : BitVec 32} (ha : a.toNat < q) : (VG.Proof.MlDsa.Arm.Round.bhbRaw g32 a).toNat = hbF g32 a.toNat := by
  rw [hbF_eq (by decide) ha]
  have e1 : (BitVec.ofNat 16 (dMul g32)).setWidth 32 = (1025 : BitVec 32) := by decide
  have e2 : BitVec.ofNat 32 (dAdd g32) = (2097152 : BitVec 32) := by decide
  have e3 : dShift g32 = 22 := rfl
  have e4 : hbMul g32 = 1025 := rfl
  have e5 : hbAdd g32 = 2 ^ 21 := rfl
  have e6 : hbShift g32 = 22 := rfl
  unfold VG.Proof.MlDsa.Arm.Round.bhbRaw
  rw [e1, e2, e3, e4, e5, e6]
  rw [q_eq] at ha
  bv_omega

theorem bhbRaw_88 {a : BitVec 32} (ha : a.toNat < q) : (VG.Proof.MlDsa.Arm.Round.bhbRaw g88 a).toNat = hbF g88 a.toNat := by
  rw [hbF_eq (by decide) ha]
  have e1 : (BitVec.ofNat 16 (dMul g88)).setWidth 32 = (11275 : BitVec 32) := by decide
  have e2 : BitVec.ofNat 32 (dAdd g88) = (8388608 : BitVec 32) := by decide
  have e3 : dShift g88 = 24 := rfl
  have e4 : hbMul g88 = 11275 := rfl
  have e5 : hbAdd g88 = 2 ^ 23 := rfl
  have e6 : hbShift g88 = 24 := rfl
  unfold VG.Proof.MlDsa.Arm.Round.bhbRaw
  rw [e1, e2, e3, e4, e5, e6]
  rw [q_eq] at ha
  bv_omega

theorem bhbRaw_toNat {g : Nat} (hg : VG.Proof.MlDsa.Arm.Round.G2 g) {a : BitVec 32} (ha : a.toNat < q) :
    (VG.Proof.MlDsa.Arm.Round.bhbRaw g a).toNat = hbF g a.toNat := by
  rcases hg with rfl | rfl
  exacts [VG.Proof.MlDsa.Arm.Round.bhbRaw_32 ha, VG.Proof.MlDsa.Arm.Round.bhbRaw_88 ha]

theorem bcsubM_toNat {g : Nat} (hg : VG.Proof.MlDsa.Arm.Round.G2 g) {x : BitVec 32} (hx : x.toNat ≤ dMod g) :
    (VG.Proof.MlDsa.Arm.Round.bcsubM g x).toNat = x.toNat % dMod g := by
  unfold VG.Proof.MlDsa.Arm.Round.bcsubM
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
theorem bhb_toNat {g : Nat} (hg : VG.Proof.MlDsa.Arm.Round.G2 g) {a : BitVec 32} (ha : a.toNat < q) :
    (VG.Proof.MlDsa.Arm.Round.bhb g a).toNat = hbF g a.toNat % hbM g := by
  unfold VG.Proof.MlDsa.Arm.Round.bhb
  rw [VG.Proof.MlDsa.Arm.Round.bcsubM_toNat hg (by rw [VG.Proof.MlDsa.Arm.Round.bhbRaw_toNat hg ha, ← VG.Proof.MlDsa.Arm.Round.hbM_dMod hg]; exact hbF_le hg.mem ha), VG.Proof.MlDsa.Arm.Round.bhbRaw_toNat hg ha,
    VG.Proof.MlDsa.Arm.Round.hbM_dMod hg]

theorem bhb_highBits {g : Nat} (hg : VG.Proof.MlDsa.Arm.Round.G2 g) (r : Zq) :
    (VG.Proof.MlDsa.Arm.Round.bhb g (BitVec.ofNat 32 r.val)).toNat = (VG.Spec.MlDsa.highBits g r).toNat := by
  have : r.val < 8380417 := r.isLt
  have e : (BitVec.ofNat 32 r.val).toNat = r.val := by rw [BitVec.toNat_ofNat]; omega
  rw [VG.Proof.MlDsa.Arm.Round.bhb_toNat hg (by rw [e]; exact r.isLt), e, highBits_eq hg.mem, Int.toNat_natCast]

end VG.Proof.MlDsa.Arm.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Round.Bits`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_high_bits` and `vg_mldsa_low_bits`

`γ₂` selects one of two loops (`bits_ok`); each loop body is symbolically
executed once for each value of `γ₂` (`hbBody_ok`, `lbBody_ok`), and its
values are those of `HighBits` and `LowBits` (`bhb_highBits`, `blb_lowBits`).
-/

namespace VG.Proof.MlDsa.Arm.Round.Bits

open VG VG.Arm VG.Impl.MlDsa.Arm.Round VG.Proof.MlDsa.Round VG.Proof.MlDsa.Arm.Round
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs NatPolyIs natPolyAt ofInt gamma2s highBits lowBits)
open VG.Proof.MlDsa.Arm.Arith.AddSub (fixS)
open VG.Impl.MlDsa.Arm.Arith (fixupS)
open VG.Proof.MlKem.Arm (cmp_z)

/-! ## Values -/

/-- `2γ₂`, as `load2g` builds it. -/
def w2g (g : Nat) : BitVec 32 :=
  BitVec.ofNat 16 (2 * g / 65536) ++ ((BitVec.ofNat 16 (2 * g % 65536)).setWidth 32).extractLsb' 0 16

theorem w2g_val {g : Nat} (hg : VG.Proof.MlDsa.Arm.Round.G2 g) : VG.Proof.MlDsa.Arm.Round.Bits.w2g g = BitVec.ofNat 32 (2 * g) := by
  rcases hg with rfl | rfl <;> decide

/-- What the body of `lowBits` stores. -/
def blb (g : Nat) (a : BitVec 32) : BitVec 32 := fixS (a - VG.Proof.MlDsa.Arm.Round.bhb g a * VG.Proof.MlDsa.Arm.Round.Bits.w2g g)

theorem blb_lowBits {g : Nat} (hg : VG.Proof.MlDsa.Arm.Round.G2 g) (r : Zq) :
    (VG.Proof.MlDsa.Arm.Round.Bits.blb g (BitVec.ofNat 32 r.val)).toNat = (ofInt (lowBits g r)).val := by
  have hr : r.val < 8380417 := r.isLt
  have e : (BitVec.ofNat 32 r.val).toNat = r.val := by rw [BitVec.toNat_ofNat]; omega
  have hb := VG.Proof.MlDsa.Arm.Round.bhb_toNat hg (a := BitVec.ofNat 32 r.val) (by rw [e]; exact r.isLt)
  rw [e] at hb
  have hm := hbM_mul hg.mem
  have hlt : hbF g r.val % hbM g < hbM g := Nat.mod_lt _ (by rcases hg with rfl | rfl <;> decide)
  have hX : hbF g r.val % hbM g * (2 * g) ≤ q - 1 - 2 * g := by
    have := Nat.mul_le_mul_right (2 * g) (Nat.le_sub_one_of_lt hlt)
    rw [Nat.sub_mul, Nat.one_mul, hm] at this; exact this
  have hg' : 2 * g < 2 ^ 20 := by rcases hg with rfl | rfl <;> decide
  unfold VG.Proof.MlDsa.Arm.Round.Bits.blb fixS
  rw [lowBits_val hg.mem, VG.Proof.MlDsa.Arm.Round.Bits.w2g_val hg]
  generalize VG.Proof.MlDsa.Arm.Round.bhb g (BitVec.ofNat 32 r.val) = B at hb
  generalize hbF g r.val % hbM g = f at hb hlt hX
  generalize r.val = v at *
  rw [q_eq] at hX ⊢
  have hBm : (B * BitVec.ofNat 32 (2 * g)).toNat = f * (2 * g) := by
    rw [BitVec.toNat_mul, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 * g) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
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

theorem hbBody_ok {g : Nat} (hg : VG.Proof.MlDsa.Arm.Round.G2 g) :
    WP isa (.block (hbBody g)) s (VG.Proof.MlDsa.Arm.Round.Bits.BStep s x w c (VG.Proof.MlDsa.Arm.Round.bhb g (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32))) := by
  rcases hg with rfl | rfl <;>
  · run_block [hbBody, hb, hbRaw, csubM, addMaskM, tail02, VG.Proof.MlDsa.Arm.Round.Bits.BStep, VG.Proof.MlDsa.Arm.Round.bhb, VG.Proof.MlDsa.Arm.Round.bcsubM, VG.Proof.MlDsa.Arm.Round.bhbRaw, h0, h1, h2, iR, oO,
      List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self, and_true]

theorem lbBody_ok {g : Nat} (hg : VG.Proof.MlDsa.Arm.Round.G2 g) :
    WP isa (.block (lbBody g)) s (VG.Proof.MlDsa.Arm.Round.Bits.BStep s x w c (VG.Proof.MlDsa.Arm.Round.Bits.blb g (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32))) := by
  rcases hg with rfl | rfl <;>
  · run_block [lbBody, hb, hbRaw, csubM, addMaskM, load2g, fixupS, tail02, VG.Proof.MlDsa.Arm.Round.Bits.BStep, VG.Proof.MlDsa.Arm.Round.Bits.blb, fixS, VG.Proof.MlDsa.Arm.Round.Bits.w2g, VG.Proof.MlDsa.Arm.Round.bhb, VG.Proof.MlDsa.Arm.Round.bcsubM,
      VG.Proof.MlDsa.Arm.Round.bhbRaw, h0, h1, h2, iR, oO, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_self,
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

theorem layout {s : State} (hp : VG.Proof.MlDsa.Arm.Round.Bits.Pre s) : Layout s [.r0] [.r2] := by
  refine ⟨fun p hp' => ?_, fun o ho => ?_, fun p hp' o ho => ?_, List.pairwise_singleton _ _, fun p hp' => ?_⟩
  · simp only [List.mem_singleton] at hp'; subst hp'; rw [hp.rd]; simp
  · simp only [List.mem_singleton] at ho; subst ho; rw [hp.wr]; simp
  · simp only [List.mem_singleton] at hp' ho; subst hp' ho; exact hp.d
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    exacts [hp.f0, hp.f2]

/-- A loop, with the body `B g` that stores `F (a)` for each coefficient `a`. -/
theorem bits_loop {s s₁ : State} (hp : VG.Proof.MlDsa.Arm.Round.Bits.Pre s) {B : List Instr} {F : BitVec 32 → BitVec 32}
    (hB : ∀ {s : State} {x w c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = c → s.gpr .r2 = w →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (w + BitVec.ofNat 32 0)) 4 →
      WP isa (.block B) s (VG.Proof.MlDsa.Arm.Round.Bits.BStep s x w c (F (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32))))
    (hg : s₁.gpr = s.gpr) (hm : s₁.mem = s.mem) (hrd : s₁.rd = s.rd) (hwr : s₁.wr = s.wr) (hsp : s₁.sp = s.sp) :
    WP isa (mapLoop .r1 B) s₁ fun s' => (∀ r ∈ VG.Proof.MlDsa.Arm.Round.Bits.fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      ∀ k < 256, coeffAt s'.mem (P s .r2) k = F (coeffAt s.mem (P s .r0) k) := by
  have e : ∀ r, P s₁ r = P s r := fun r => by simp only [P, hg]
  have hp₁ : VG.Proof.MlDsa.Arm.Round.Bits.Pre s₁ := ⟨by rw [hrd, e, hp.rd], by rw [hwr, e, hp.wr], by rw [e, e]; exact hp.d,
    by rw [hg]; exact hp.f0, by rw [hg]; exact hp.f2, by rw [hg]; exact hp.g, by rw [hm, e]; exact hp.red⟩
  have hL := VG.Proof.MlDsa.Arm.Round.Bits.layout hp₁
  refine WP.mono (VG.Proof.MlDsa.Arm.Round.loop_ok (ptrs := [.r0, .r2]) (fixed := VG.Proof.MlDsa.Arm.Round.Bits.fixedR) (V := fun _ i => F (coeffAt s₁.mem (P s₁ .r0) i))
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
theorem bits_ok {s : State} (hp : VG.Proof.MlDsa.Arm.Round.Bits.Pre s) {B : Nat → List Instr} {F : Nat → BitVec 32 → BitVec 32}
    (hB : ∀ g, VG.Proof.MlDsa.Arm.Round.G2 g → ∀ {s : State} {x w c : BitVec 32}, s.gpr .r0 = x → s.gpr .r1 = c → s.gpr .r2 = w →
      InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4 →
      InRegions s.wr (State.addr (w + BitVec.ofNat 32 0)) 4 →
      WP isa (.block (B g)) s (VG.Proof.MlDsa.Arm.Round.Bits.BStep s x w c (F g (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32)))) :
    WP isa (.seq (.block [gammaCmp .r1]) (.ite .eq (mapLoop .r1 (B g88)) (mapLoop .r1 (B g32)))) s fun s' =>
      (∀ r ∈ VG.Proof.MlDsa.Arm.Round.Bits.fixedR, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
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
    exact VG.Proof.MlDsa.Arm.Round.Bits.bits_loop hp (hB g88 (.inr rfl)) rfl rfl rfl rfl rfl
  · have e : (s.gpr .r1).toNat = g32 := by
      have := of_decide_eq_false h
      rcases mem_gamma2s hp.g with h' | h'
      · exact absurd h' this
      · exact h'
    rw [e]
    exact VG.Proof.MlDsa.Arm.Round.Bits.bits_loop hp (hB g32 (.inl rfl)) rfl rfl rfl rfl rfl

/-! ## Verified -/

theorem pre_high {s : State} (h : (Spec.MlDsa.highBitsContract Arm.abi).pre s) : VG.Proof.MlDsa.Arm.Round.Bits.Pre s := by
  sig_pre [Spec.MlDsa.highBitsContract, Spec.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem pre_low {s : State} (h : (Spec.MlDsa.lowBitsContract Arm.abi).pre s) : VG.Proof.MlDsa.Arm.Round.Bits.Pre s := by
  sig_pre [Spec.MlDsa.lowBitsContract, Spec.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem preserved_of {s s' : State} (h : ∀ r ∈ VG.Proof.MlDsa.Arm.Round.Bits.fixedR, s'.gpr r = s.gpr r) :
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
    Verified Arm.target Impl.MlDsa.Arm.Round.highBits (Spec.MlDsa.highBitsContract Arm.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlDsa.Arm.Round.Bits.ct (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := VG.Proof.MlDsa.Arm.Round.Bits.pre_high hs
    obtain ⟨t, s', he, hf, hsp, hk⟩ := VG.Proof.MlDsa.Arm.Round.Bits.bits_ok hp (B := hbBody) (F := VG.Proof.MlDsa.Arm.Round.bhb) fun g hg _ _ _ _ h0 h1 h2 iR oO => VG.Proof.MlDsa.Arm.Round.Bits.hbBody_ok h0 h1 h2 iR oO hg
    refine ⟨t, s', he, ⟨VG.Proof.MlDsa.Arm.Round.Bits.preserved_of hf, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.highBitsContract, Spec.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    refine natPolyIs_of_toNat fun k hk' => ?_
    have hr := hp.red k hk'
    show (coeffAt s'.mem (P s .r2) k).toNat = ((polyAt s.mem (P s .r0)).map _)[k]!
    rw [hk k hk', map_get _ _ hk', polyAt_get _ _ hk', ← VG.Proof.MlDsa.Arm.Round.bhb_highBits (mem_gamma2s hp.g |>.elim .inr .inl),
      word_of_reduced hr]
  · sig_pub [Spec.MlDsa.highBitsContract, Spec.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2⟩ := h
    exact ⟨h0, by rw [h1], h2⟩
  · refine ⟨VG.Proof.MlDsa.Arm.Round.Bits.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.highBitsContract, Spec.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact VG.Proof.MlDsa.Round.reduced_zero _

theorem low_verified :
    Verified Arm.target Impl.MlDsa.Arm.Round.lowBits (Spec.MlDsa.lowBitsContract Arm.abi) := by
  refine ⟨fun s hs => ?_, VG.Proof.MlDsa.Arm.Round.Bits.ct (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · have hp := VG.Proof.MlDsa.Arm.Round.Bits.pre_low hs
    obtain ⟨t, s', he, hf, hsp, hk⟩ := VG.Proof.MlDsa.Arm.Round.Bits.bits_ok hp (B := lbBody) (F := VG.Proof.MlDsa.Arm.Round.Bits.blb)
      fun g hg _ _ _ _ h0 h1 h2 iR oO => VG.Proof.MlDsa.Arm.Round.Bits.lbBody_ok h0 h1 h2 iR oO hg
    refine ⟨t, s', he, ⟨VG.Proof.MlDsa.Arm.Round.Bits.preserved_of hf, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.lowBitsContract, Spec.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    refine polyIs_of_toNat fun k hk' => ?_
    have hr := hp.red k hk'
    show (coeffAt s'.mem (P s .r2) k).toNat = (((polyAt s.mem (P s .r0)).map _)[k]! : Zq).val
    rw [hk k hk', map_get _ _ hk', polyAt_get _ _ hk', ← VG.Proof.MlDsa.Arm.Round.Bits.blb_lowBits (mem_gamma2s hp.g |>.elim .inr .inl),
      word_of_reduced hr]
  · sig_pub [Spec.MlDsa.lowBitsContract, Spec.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at h
    obtain ⟨-, h0, h1, h2⟩ := h
    exact ⟨h0, by rw [h1], h2⟩
  · refine ⟨VG.Proof.MlDsa.Arm.Round.Bits.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.lowBitsContract, Spec.MlDsa.bitsSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
        Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact VG.Proof.MlDsa.Round.reduced_zero _

end VG.Proof.MlDsa.Arm.Round.Bits

end
