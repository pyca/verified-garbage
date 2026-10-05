import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Impl.MlDsa.Arm.Arith.Ntt
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Mul
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttBfly`. -/
section

/-!
# ML-DSA on 32-bit ARM: the butterflies of `NTT` and `NTT⁻¹`

Each butterfly is three blocks, each symbolically executed once for any state:
before `mulz`, `mulz` (`mulz_ok`), and after it; their values are those of
`bfly` and `bflyInv` (`bfly_spec`, `bflyInv_spec`): what `BflyOk` states of a
butterfly's code, for the loops (`NttLoop.lean`).
-/

namespace VG.Proof.MlDsa.Arm.Arith

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.Arm (addr_ptr inRegions_of)

/-- The pieces of the zeta `z`, and `q`, in `r4`–`r7`. -/
def ZetaIn (z : Zq) (s : State) : Prop :=
  s.gpr .r4 = Qw ∧ s.gpr .r5 = BitVec.ofNat 32 z.val >>> 14 ∧ s.gpr .r6 = BitVec.ofNat 32 z.val <<< 18 >>> 25 ∧
    s.gpr .r7 = BitVec.ofNat 32 z.val <<< 25 >>> 25

/-- The registers the loops of the transforms keep. -/
abbrev bflyKeep : List Reg := [.r1, .r2, .r4, .r5, .r6, .r7, .r11, .lr]

/-- The code `code len` does what the butterfly `op` does, on the
coefficients `j` and `j + len` of the polynomial at `p`, with `r0` pointing
at coefficient `j`, the zeta's pieces in `r5`–`r7`, and `r3` counting down. -/
def BflyOk (code : Nat → List Instr) (op : Poly → Nat → Nat → Zq → Poly) : Prop :=
  ∀ (p : BitVec 32) (len j : Nat), 0 < len → len ≤ 128 → j + len < 256 → p.toNat + 1024 ≤ 2 ^ 32 →
    ∀ (z : Zq) (G : Poly) (s : State), s.gpr .r0 = p + BitVec.ofNat 32 (4 * j) → VG.Proof.MlDsa.Arm.Arith.ZetaIn z s →
      PolyIs s.mem (State.addr p) G → polyRegion (State.addr p) ∈ s.wr →
      WP isa (.block (code len)) s fun s' =>
        PolyIs s'.mem (State.addr p) (op G j len z) ∧ Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (j + 1)) ∧ s'.gpr .r3 = s.gpr .r3 - 1 ∧
        s'.z = (s.gpr .r3 - 1 == 0) ∧ VG.Proof.MlDsa.Arm.Arith.Keep VG.Proof.MlDsa.Arm.Arith.bflyKeep s s'

/-! ## Loads, stores and values -/

/-- A pointer to coefficient `j`, plus the offset of coefficient `j + k`. -/
theorem addr_at {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {j k : Nat} (h : j + k < 256) :
    State.addr (p + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 (4 * k)) = coeffAddr (State.addr p) (j + k) := by
  rw [addr_ptr _ _ _ (by omega), ← Nat.mul_add]

theorem addr_at0 {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {j : Nat} (h : j < 256) :
    State.addr (p + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 0) = coeffAddr (State.addr p) j :=
  VG.Proof.MlDsa.Arm.Arith.addr_at (k := 0) hp h

theorem wr_at {p : BitVec 32} {s : State} (hw : polyRegion (State.addr p) ∈ s.wr) {j : Nat} (h : j < 256) :
    InRegions s.wr (coeffAddr (State.addr p) j) 4 :=
  inRegions_of hw (coeff_contains _ h)

theorem rd_at {p : BitVec 32} {s : State} (hw : polyRegion (State.addr p) ∈ s.wr) {j : Nat} (h : j < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (State.addr p) j) 4 :=
  inRegions_of (List.mem_append_right _ hw) (coeff_contains _ h)

theorem ptr_next (p : BitVec 32) (j : Nat) :
    p + BitVec.ofNat 32 (4 * j) + 4 = p + BitVec.ofNat 32 (4 * (j + 1)) := by
  rw [BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add, Nat.mul_succ]

/-- The word stored for a coefficient, as a value of `ℤ_q`. -/
theorem word_val {m : Mem} {P : Addr} {G : Poly} (h : PolyIs m P G) {j : Nat} (hj : j < 256) :
    m.readW (coeffAddr P j) 32 = BitVec.ofNat 32 (G[j]!).val := by
  rw [← coeffAt_eq]; exact ofNat_val_eq (polyIs_toNat h hj)

/-- `csub` after `mulz` of stored values. -/
theorem mulz_val (b z : Zq) :
    bcsub (bmulz (BitVec.ofNat 32 b.val) (BitVec.ofNat 32 z.val >>> 14) (BitVec.ofNat 32 z.val <<< 18 >>> 25)
      (BitVec.ofNat 32 z.val <<< 25 >>> 25)) = BitVec.ofNat 32 (z * b).val := by
  refine ofNat_val_eq ?_
  rw [bcsub_mulz (by rw [toNat_val]; exact b.isLt) (by rw [toNat_val]; exact z.isLt), toNat_val, toNat_val,
    val_mul, Nat.mul_comm]

theorem sub_val (a t : Zq) : bfix (BitVec.ofNat 32 a.val - BitVec.ofNat 32 t.val) = BitVec.ofNat 32 (a - t).val := by
  refine ofNat_val_eq ?_
  rw [bfix_sub (by rw [toNat_val]; exact a.isLt) (by rw [toNat_val]; exact t.isLt), toNat_val, toNat_val, val_sub',
    Nat.add_sub_assoc (Nat.le_of_lt t.isLt)]

theorem add_val (a t : Zq) : bcsub (BitVec.ofNat 32 a.val + BitVec.ofNat 32 t.val) = BitVec.ofNat 32 (a + t).val := by
  refine ofNat_val_eq ?_
  rw [bcsub_add (by rw [toNat_val]; exact a.isLt) (by rw [toNat_val]; exact t.isLt), toNat_val, toNat_val, val_add']

/-! ## `NTT` -/

/-- The butterfly of `NTT` after the load and `mulz`. -/
def bflyRest (len : Nat) : List Instr :=
  csub .r9 .r12 .r4 ++ [.ldr .r8 .r0 0, .dp .sub .r10 .r8 (.reg .r9)] ++ VG.Impl.MlDsa.Arm.Arith.fixup .r10 .r12 .r4 ++
    [.str .r10 .r0 (4 * len), .dp .add .r8 .r8 (.reg .r9)] ++ csub .r8 .r12 .r4 ++
    [.str .r8 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]

theorem bfly_split (len : Nat) :
    Impl.MlDsa.Arm.Arith.bfly len = ([.ldr .r8 .r0 (4 * len)] : List Instr) ++ (mulz .r9 .r8 .r12 ++ VG.Proof.MlDsa.Arm.Arith.bflyRest len) := by
  simp only [Impl.MlDsa.Arm.Arith.bfly, VG.Proof.MlDsa.Arm.Arith.bflyRest, List.append_assoc, List.cons_append, List.nil_append]

section
variable {s : State} {x c v : BitVec 32} {len : Nat} (hlen : 4 * len < 4096) (h0 : s.gpr .r0 = x)
  (h3 : s.gpr .r3 = c) (h4 : s.gpr .r4 = Qw) (h9 : s.gpr .r9 = v)
  (iA : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
  (oA : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
  (oB : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * len))) 4)
include hlen h0 h3 h4 h9 iA oA oB

theorem bflyRest_ok :
    WP isa (.block (VG.Proof.MlDsa.Arm.Arith.bflyRest len)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * len)))
          (bfix (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 - bcsub v))).writeW
        (State.addr (x + BitVec.ofNat 32 0)) (bcsub (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 + bcsub v)) ∧
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ VG.Proof.MlDsa.Arm.Arith.Keep VG.Proof.MlDsa.Arm.Arith.bflyKeep s s' := by
  run_block [VG.Proof.MlDsa.Arm.Arith.bflyRest, csub, VG.Impl.MlDsa.Arm.Arith.fixup, bcsub, bfix, VG.Proof.MlDsa.Arm.Arith.Keep, h0, h3, h4, h9, iA, oA, oB, hlen, List.mem_cons,
    List.not_mem_nil, or_false]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> rfl

end

theorem bfly_spec : VG.Proof.MlDsa.Arm.Arith.BflyOk Impl.MlDsa.Arm.Arith.bfly VG.Proof.MlDsa.Arith.bfly := by
  intro p len j hl hl' hj hp z G s h0 hz hG hw
  obtain ⟨z4, z5, z6, z7⟩ := hz
  have eB := VG.Proof.MlDsa.Arm.Arith.addr_at hp hj (j := j) (k := len)
  have eA := VG.Proof.MlDsa.Arm.Arith.addr_at0 hp (j := j) (by omega)
  rw [VG.Proof.MlDsa.Arm.Arith.bfly_split, WP.block_append_iff]
  have iB : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * len))) 4 := by
    rw [h0, eB]; exact VG.Proof.MlDsa.Arm.Arith.rd_at hw hj
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_ldr (by omega) iB, runStep_some, runBlock_nil], ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (mulz_ok (s := s.setReg .r8 _) (b := s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * len))) 32)
    (z₂ := BitVec.ofNat 32 z.val >>> 14) (z₁ := BitVec.ofNat 32 z.val <<< 18 >>> 25)
    (z₀ := BitVec.ofNat 32 z.val <<< 25 >>> 25) (by simp [State.setReg, z4]) (by simp [State.setReg, z5])
    (by simp [State.setReg, z6]) (by simp [State.setReg, z7]) (by simp [State.setReg]))
    fun s₁ ⟨e9, eo, m₁, rd₁, wr₁, sp₁⟩ => ?_
  have g : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r12 → s₁.gpr r = s.gpr r := fun r a8 a9 a12 => by
    rw [eo r a9 a12]; simp [State.setReg, a8]
  have hw₁ : polyRegion (State.addr p) ∈ s₁.wr := by rw [wr₁]; exact hw
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.bflyRest_ok (s := s₁) (x := p + BitVec.ofNat 32 (4 * j)) (by omega)
    ((g _ (by decide) (by decide) (by decide)).trans h0) rfl ((g _ (by decide) (by decide) (by decide)).trans z4)
    e9 (by rw [eA]; exact VG.Proof.MlDsa.Arm.Arith.rd_at hw₁ (by omega)) (by rw [eA]; exact VG.Proof.MlDsa.Arm.Arith.wr_at hw₁ (by omega))
    (by rw [eB]; exact VG.Proof.MlDsa.Arm.Arith.wr_at hw₁ hj)) fun s' ⟨hm, r0, r3, hzf, hk⟩ => ?_
  have nk : ∀ r ∈ VG.Proof.MlDsa.Arm.Arith.bflyKeep, r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r12 := by decide
  have k₁ : VG.Proof.MlDsa.Arm.Arith.Keep VG.Proof.MlDsa.Arm.Arith.bflyKeep s s₁ := ⟨fun r hr => g r (nk r hr).1 (nk r hr).2.1 (nk r hr).2.2, rd₁, wr₁, sp₁⟩
  have e3 : s₁.gpr .r3 = s.gpr .r3 := g _ (by decide) (by decide) (by decide)
  have hjn : j < n := by rw [n_eq]; omega
  have hjl : j + len < n := by rw [n_eq]; omega
  refine ⟨?_, ?_, by rw [r0]; exact VG.Proof.MlDsa.Arm.Arith.ptr_next p j, by rw [r3, e3], by rw [hzf, e3], k₁.trans hk⟩
  · rw [hm, m₁, eA, eB]
    simp only [State.setReg]
    rw [h0, eB, VG.Proof.MlDsa.Arm.Arith.word_val hG hj, VG.Proof.MlDsa.Arm.Arith.word_val hG (by omega), VG.Proof.MlDsa.Arm.Arith.mulz_val, VG.Proof.MlDsa.Arm.Arith.sub_val, VG.Proof.MlDsa.Arm.Arith.add_val]
    have h1 := polyIs_writeW hG hj (G[j]! - z * G[j + len]!) (toNat_val _)
    have h2 := polyIs_writeW h1 hjn (G[j]! + z * G[j + len]!) (toNat_val _)
    simp only [VG.Proof.MlDsa.Arith.bfly]
    rwa [getElem!_set!_ne _ hjn (by omega)]
  · rw [hm, m₁, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hj)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjn)

/-! ## `NTT⁻¹` -/

/-- The butterfly of `NTT⁻¹` before `mulz`. -/
def bflyInvPre (len : Nat) : List Instr :=
  [.ldr .r8 .r0 0, .ldr .r9 .r0 (4 * len), .dp .add .r10 .r8 (.reg .r9)] ++ csub .r10 .r12 .r4 ++
    [.str .r10 .r0 0, .dp .sub .r8 .r8 (.reg .r9)] ++ VG.Impl.MlDsa.Arm.Arith.fixup .r8 .r12 .r4

/-- The butterfly of `NTT⁻¹` after `mulz`. -/
def bflyInvPost (len : Nat) : List Instr :=
  csub .r9 .r12 .r4 ++ [.str .r9 .r0 (4 * len), .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]

theorem bflyInv_split (len : Nat) :
    Impl.MlDsa.Arm.Arith.bflyInv len = VG.Proof.MlDsa.Arm.Arith.bflyInvPre len ++ (mulz .r9 .r8 .r12 ++ VG.Proof.MlDsa.Arm.Arith.bflyInvPost len) := by
  simp only [Impl.MlDsa.Arm.Arith.bflyInv, VG.Proof.MlDsa.Arm.Arith.bflyInvPre, VG.Proof.MlDsa.Arm.Arith.bflyInvPost, List.append_assoc, List.cons_append,
    List.nil_append]

section
variable {s : State} {x : BitVec 32} {len : Nat} (hlen : 4 * len < 4096) (h0 : s.gpr .r0 = x)
  (h4 : s.gpr .r4 = Qw)
  (iA : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4)
  (iB : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * len))) 4)
  (oA : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include hlen h0 h4 iA iB oA

theorem bflyInvPre_ok :
    WP isa (.block (VG.Proof.MlDsa.Arm.Arith.bflyInvPre len)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0))
        (bcsub (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 +
          s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * len))) 32)) ∧
      s'.gpr .r8 = bfix (s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 -
          s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * len))) 32) ∧
      s'.gpr .r0 = x ∧ s'.gpr .r3 = s.gpr .r3 ∧ VG.Proof.MlDsa.Arm.Arith.Keep VG.Proof.MlDsa.Arm.Arith.bflyKeep s s' := by
  run_block [VG.Proof.MlDsa.Arm.Arith.bflyInvPre, csub, VG.Impl.MlDsa.Arm.Arith.fixup, bcsub, bfix, h0, h4, iA, iB, oA, hlen]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> rfl

end

section
variable {s : State} {x c v : BitVec 32} {len : Nat} (hlen : 4 * len < 4096) (h0 : s.gpr .r0 = x)
  (h3 : s.gpr .r3 = c) (h4 : s.gpr .r4 = Qw) (h9 : s.gpr .r9 = v)
  (oB : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * len))) 4)
include hlen h0 h3 h4 h9 oB

theorem bflyInvPost_ok :
    WP isa (.block (VG.Proof.MlDsa.Arm.Arith.bflyInvPost len)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * len))) (bcsub v) ∧
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ VG.Proof.MlDsa.Arm.Arith.Keep VG.Proof.MlDsa.Arm.Arith.bflyKeep s s' := by
  run_block [VG.Proof.MlDsa.Arm.Arith.bflyInvPost, csub, VG.Impl.MlDsa.Arm.Arith.fixup, bcsub, bfix, h0, h3, h4, h9, oB, hlen]
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h <;> subst h <;> rfl

end

/-- The inverse butterfly as two writes. -/
theorem bflyInv_eq (G : Poly) {j len : Nat} (hl : 0 < len) (hj : j + len < n) (z : Zq) :
    VG.Proof.MlDsa.Arith.bflyInv G j len z =
      (G.set! j (G[j]! + G[j + len]!)).set! (j + len) (z * (G[j]! - G[j + len]!)) := by
  refine ext_getElem! fun i hi => ?_
  rw [bflyInv_get _ hl hj _ hi]
  rcases (by omega : i = j ∨ i = j + len ∨ (i ≠ j ∧ i ≠ j + len)) with rfl | rfl | ⟨h1, h2⟩
  · rw [ite_eq_left rfl, getElem!_set!_ne _ hi (by omega), getElem!_set!_self _ hi]
  · rw [ite_eq_right (by omega), ite_eq_left rfl, getElem!_set!_self _ hi]
  · rw [ite_eq_right h1, ite_eq_right h2, getElem!_set!_ne _ hi (Ne.symm h2), getElem!_set!_ne _ hi (Ne.symm h1)]

theorem bflyInv_spec : VG.Proof.MlDsa.Arm.Arith.BflyOk Impl.MlDsa.Arm.Arith.bflyInv VG.Proof.MlDsa.Arith.bflyInv := by
  intro p len j hl hl' hj hp z G s h0 hz hG hw
  obtain ⟨z4, z5, z6, z7⟩ := hz
  have eB := VG.Proof.MlDsa.Arm.Arith.addr_at hp hj (j := j) (k := len)
  have eA := VG.Proof.MlDsa.Arm.Arith.addr_at0 hp (j := j) (by omega)
  have hjn : j < n := by rw [n_eq]; omega
  have hjl : j + len < n := by rw [n_eq]; omega
  rw [VG.Proof.MlDsa.Arm.Arith.bflyInv_split, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.bflyInvPre_ok (len := len) (by omega) h0 z4 (by rw [eA]; exact VG.Proof.MlDsa.Arm.Arith.rd_at hw hjn)
    (by rw [eB]; exact VG.Proof.MlDsa.Arm.Arith.rd_at hw hj) (by rw [eA]; exact VG.Proof.MlDsa.Arm.Arith.wr_at hw hjn)) fun s₁ ⟨m₁, e8, e0, e3, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulz_ok (k₁.gpr .r4 (by decide) ▸ z4) (k₁.gpr .r5 (by decide) ▸ z5)
    (k₁.gpr .r6 (by decide) ▸ z6) (k₁.gpr .r7 (by decide) ▸ z7) e8)
    fun s₂ ⟨e9, eo, m₂, rd₂, wr₂, sp₂⟩ => ?_
  have nk : ∀ r ∈ VG.Proof.MlDsa.Arm.Arith.bflyKeep, r ≠ .r9 ∧ r ≠ .r12 := by decide
  have k₂ : VG.Proof.MlDsa.Arm.Arith.Keep VG.Proof.MlDsa.Arm.Arith.bflyKeep s₁ s₂ := ⟨fun r hr => eo r (nk r hr).1 (nk r hr).2, rd₂, wr₂, sp₂⟩
  have hw₂ : polyRegion (State.addr p) ∈ s₂.wr := by rw [k₂.wr, k₁.wr]; exact hw
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.bflyInvPost_ok (s := s₂) (x := p + BitVec.ofNat 32 (4 * j)) (len := len) (by omega)
    ((eo _ (by decide) (by decide)).trans e0) rfl ((k₁.trans k₂).gpr .r4 (by decide) ▸ z4) e9
    (by rw [eB]; exact VG.Proof.MlDsa.Arm.Arith.wr_at hw₂ hj)) fun s' ⟨hm, r0, r3, hzf, k₃⟩ => ?_
  have e3' : s₂.gpr .r3 = s.gpr .r3 := (eo _ (by decide) (by decide)).trans e3
  refine ⟨?_, ?_, by rw [r0]; exact VG.Proof.MlDsa.Arm.Arith.ptr_next p j, by rw [r3, e3'], by rw [hzf, e3'], (k₁.trans k₂).trans k₃⟩
  · rw [hm, m₂, m₁, eA, eB, VG.Proof.MlDsa.Arm.Arith.word_val hG hjn, VG.Proof.MlDsa.Arm.Arith.word_val hG hj, VG.Proof.MlDsa.Arm.Arith.add_val, VG.Proof.MlDsa.Arm.Arith.sub_val, VG.Proof.MlDsa.Arm.Arith.mulz_val, VG.Proof.MlDsa.Arm.Arith.bflyInv_eq _ hl hjl]
    have h1 := polyIs_writeW hG hjn (G[j]! + G[j + len]!) (toNat_val _)
    exact polyIs_writeW h1 hjl (z * (G[j]! - G[j + len]!)) (toNat_val _)
  · rw [hm, m₂, m₁, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjn)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hj)

end VG.Proof.MlDsa.Arm.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttLoop`. -/
section

/-!
# ML-DSA on 32-bit ARM: the table, blocks and layers of `NTT` and `NTT⁻¹`

`storeTab t 256` leaves the `u32`s `t 0, …, t 255` at `r1` (`Tab`,
`storeTab_ok`). The loops of `nttBlk` and `nttLay`, for any butterfly code
that does what a butterfly `op` of the specification does (`BflyOk`): a block
runs `len` butterflies (`blockN`), and a layer its `128 / len` blocks
(`layerN`), with the zetas `Z (zi c)`, whose values `tab` the table at `zB`
holds.
-/

namespace VG.Proof.MlDsa.Arm.Arith

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr inRegions_of)

/-! ## The table -/

/-- The `u32`s at `P` are the table `t`. -/
def Tab (t : Nat → Nat) (m : Mem) (P : Addr) : Prop := ∀ k < 256, coeffAt m P k = BitVec.ofNat 32 (t k)

/-- The table `tab` holds the values of the zetas `Z`. -/
def TabOf (tab : Nat → Nat) (Z : Nat → Zq) : Prop := ∀ k < 256, tab k = (Z k).val

theorem tab_word {t : Nat → Nat} (ht : ∀ k < 256, t k < q) (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 16 (t i / 65536) ++ ((BitVec.ofNat 16 (t i % 65536)).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 (t i) := by
  have := ht i hi
  rw [q_eq] at this
  generalize t i = v at *
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_zero, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

theorem tabStep_ok (t : Nat → Nat) (ht : ∀ k < 256, t k < q) {i : Nat} (hi : i < 256) (s : State) {zB : BitVec 32}
    (h1 : s.gpr .r1 = zB) (hw : InRegions s.wr (State.addr (zB + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block (tabStep t i)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (zB + BitVec.ofNat 32 (4 * i))) (BitVec.ofNat 32 (t i)) ∧
        VG.Proof.MlDsa.Arm.Arith.Keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' := by
  have ho : 4 * i < 4096 := by omega
  run_block [tabStep, h1, hw, ho, VG.Proof.MlDsa.Arm.Arith.tab_word ht i hi]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl

/-- The table, stored in the 1024 bytes at `r1`. -/
theorem storeTab_ok (t : Nat → Nat) (ht : ∀ k < 256, t k < q) (s : State) {zB : BitVec 32}
    (h1 : s.gpr .r1 = zB) (hfit : zB.toNat + 1024 ≤ 2 ^ 32) (hw : polyRegion (State.addr zB) ∈ s.wr) :
    WP isa (.block (storeTab t 256)) s fun s' =>
      VG.Proof.MlDsa.Arm.Arith.Tab t s'.mem (State.addr zB) ∧ Frame [polyRegion (State.addr zB)] s.mem s'.mem ∧
        VG.Proof.MlDsa.Arm.Arith.Keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s' => VG.Proof.MlDsa.Arm.Arith.Keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9,
      .r10, .r11, .lr] s s' ∧ Frame [polyRegion (State.addr zB)] s.mem s'.mem ∧
      ∀ j < k, coeffAt s'.mem (State.addr zB) j = BitVec.ofNat 32 (t j))
    (fun k s' hk ⟨hk', hf, ht'⟩ => ?_) 256 (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s' ⟨hk, hf, ht'⟩ => ⟨ht', hf, hk⟩
  have e : State.addr (zB + BitVec.ofNat 32 (4 * k)) = coeffAddr (State.addr zB) k := by
    have := addr_ptr zB (4 * k) 0 (by omega)
    simp only [Nat.add_zero, BitVec.add_zero] at this
    exact this
  have hk256 : k < n := by rw [n_eq]; exact hk
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.tabStep_ok t ht hk s' ((hk'.gpr .r1 (by decide)).trans h1)
      (by rw [e, hk'.wr]; exact inRegions_of hw (coeff_contains _ hk256)))
    fun s'' ⟨hm', hk''⟩ => ⟨hk'.trans hk'', ?_, fun j hj => ?_⟩
  · rw [hm', e]
    exact hf.writeW (List.mem_singleton_self _) _ (coeff_contains _ hk256)
  · rw [hm', e, coeffAt_writeW _ _ (show j < n by rw [n_eq]; omega) hk256]
    by_cases e' : k = j
    · subst e'; rw [ite_eq_left rfl]
    · rw [ite_eq_right e']; exact ht' j (by omega)

/-- Writes elsewhere keep the table. -/
theorem Tab.frame {t : Nat → Nat} {m m' : Mem} {P : Addr} (h : VG.Proof.MlDsa.Arm.Arith.Tab t m P) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (polyRegion P).Disjoint r) : VG.Proof.MlDsa.Arm.Arith.Tab t m' P :=
  fun k hk => by rw [coeffAt_frame hf hd (show k < n by rw [n_eq]; exact hk)]; exact h k hk

/-! ## A block -/

section
variable {code : Nat → List Instr} {op : Poly → Nat → Nat → Zq → Poly} (hb : VG.Proof.MlDsa.Arm.Arith.BflyOk code op)
include hb

/-- The `len` butterflies of a block. -/
theorem bflys_ok {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {len start : Nat} (hlen : 0 < len)
    (hl : len ≤ 128) (hs : start + 2 * len ≤ 256) (z : Zq) (G : Poly) (s : State)
    (h0 : s.gpr .r0 = p + BitVec.ofNat 32 (4 * start)) (hz : VG.Proof.MlDsa.Arm.Arith.ZetaIn z s) (hG : PolyIs s.mem (State.addr p) G)
    (hw : polyRegion (State.addr p) ∈ s.wr) (h3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (len - 0))) :
    WP isa (.loop (.block (code len)) .ne) s fun s' =>
      PolyIs s'.mem (State.addr p) (blockN op G len z start len) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + len)) ∧ VG.Proof.MlDsa.Arm.Arith.Keep VG.Proof.MlDsa.Arm.Arith.bflyKeep s s' := by
  refine wp_loop_ne (fun t s' => PolyIs s'.mem (State.addr p) (blockN op G len z start t) ∧
      Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + t)) ∧
      s'.gpr .r3 = BitVec.ofNat 32 (1 * (len - t)) ∧ VG.Proof.MlDsa.Arm.Arith.Keep VG.Proof.MlDsa.Arm.Arith.bflyKeep s s') hlen
    (fun t ht s' ⟨hP, hf, h0', h3', hk⟩ => ?_) (fun _ ⟨hP, hf, h0', _, hk⟩ => ⟨hP, hf, h0', hk⟩)
    ⟨hG, Frame.refl _ _, by rw [h0, Nat.add_zero], h3, Keep.refl _ _⟩
  obtain ⟨z4, z5, z6, z7⟩ := hz
  have hz' : VG.Proof.MlDsa.Arm.Arith.ZetaIn z s' := ⟨(hk.gpr .r4 (by decide)).trans z4, (hk.gpr .r5 (by decide)).trans z5,
    (hk.gpr .r6 (by decide)).trans z6, (hk.gpr .r7 (by decide)).trans z7⟩
  refine WP.mono (hb p len (start + t) hlen hl (by omega) hp z _ s' h0' hz' hP (by rw [hk.wr]; exact hw))
    fun s'' ⟨hP', hf', h0'', h3'', hz'', hk'⟩ => ⟨⟨?_, hf.trans hf', ?_, ?_, hk.trans hk'⟩, ?_⟩
  · rw [blockN_succ]; exact hP'
  · rw [h0'', Nat.add_assoc]
  · rw [h3'', h3']; exact count_sub (k := 1) ht
  · rw [hz'', h3']; exact count_z (k := 1) ht (by decide) (by omega)

omit hb in
theorem blkPre_ok (len : Nat) (hl : len ≤ 128) (op : DpOp) (hop : op = .add ∨ op = .sub) (s : State)
    {x : BitVec 32} (h1 : s.gpr .r1 = x) (hi : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 0)) 4) :
    WP isa (.block (([.ldr .r8 .r1 0] : List Instr) ++ zPieces .r8 ++
      ([.dp op .r1 .r1 (.imm 4), .mov .r3 (.imm (BitVec.ofNat 32 len))] : List Instr))) s fun s' =>
      s'.gpr .r5 = s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 >>> 14 ∧
      s'.gpr .r6 = s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 <<< 18 >>> 25 ∧
      s'.gpr .r7 = s.mem.readW (State.addr (x + BitVec.ofNat 32 0)) 32 <<< 25 >>> 25 ∧
      s'.gpr .r1 = (if op = .add then x + 4 else x - 4) ∧ s'.gpr .r3 = BitVec.ofNat 32 len ∧
      s'.mem = s.mem ∧ VG.Proof.MlDsa.Arm.Arith.Keep [.r0, .r2, .r4, .r11, .lr] s s' := by
  have he : encodable (BitVec.ofNat 32 len) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 l) = true := by decide
    exact this len (by omega)
  rcases hop with rfl | rfl <;>
  · run_block [zPieces, h1, hi, he]
    keep_simp

omit hb in
theorem blkPost_ok (len : Nat) (hl : len ≤ 128) (s : State) :
    WP isa (.block [.dp .add .r0 .r0 (.imm (BitVec.ofNat 32 (4 * len))), .subs .r2 .r2 (.imm 1)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 + BitVec.ofNat 32 (4 * len) ∧ s'.gpr .r2 = s.gpr .r2 - 1 ∧
        s'.z = (s.gpr .r2 - 1 == 0) ∧ s'.mem = s.mem ∧ VG.Proof.MlDsa.Arm.Arith.Keep [.r1, .r4, .r5, .r6, .r7, .r11, .lr] s s' := by
  have he : encodable (BitVec.ofNat 32 (4 * len)) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 (4 * l)) = true := by decide
    exact this len (by omega)
  run_block [he]
  keep_simp

/-- The pointer to the next zeta. -/
def nextZ (op : DpOp) (x : BitVec 32) : BitVec 32 := if op = .add then x + 4 else x - 4

/-- A block, with the zeta `Z k` at `r1`. -/
theorem blk_ok {tab : Nat → Nat} {Z : Nat → Zq} (hZ : VG.Proof.MlDsa.Arm.Arith.TabOf tab Z) {p zB : BitVec 32}
    (hp : p.toNat + 1024 ≤ 2 ^ 32) (hzf : zB.toNat + 1024 ≤ 2 ^ 32) {len start k : Nat}
    (hlen : 0 < len) (hl : len ≤ 128) (hs : start + 2 * len ≤ 256) (hk : k < 256) (dop : DpOp)
    (hop : dop = .add ∨ dop = .sub) (G : Poly) (s : State) (h0 : s.gpr .r0 = p + BitVec.ofNat 32 (4 * start))
    (h1 : s.gpr .r1 = zB + BitVec.ofNat 32 (4 * k)) (h4 : s.gpr .r4 = Qw) (hG : PolyIs s.mem (State.addr p) G)
    (hw : polyRegion (State.addr p) ∈ s.wr) (hzw : polyRegion (State.addr zB) ∈ s.rd ++ s.wr)
    (ht : VG.Proof.MlDsa.Arm.Arith.Tab tab s.mem (State.addr zB)) :
    WP isa (nttBlk (code len) len dop) s fun s' =>
      PolyIs s'.mem (State.addr p) (blockN op G len (Z k) start len) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (start + 2 * len)) ∧ s'.gpr .r1 = VG.Proof.MlDsa.Arm.Arith.nextZ dop (s.gpr .r1) ∧
        s'.gpr .r2 = s.gpr .r2 - 1 ∧ s'.z = (s.gpr .r2 - 1 == 0) ∧ VG.Proof.MlDsa.Arm.Arith.Keep [.r4, .r11, .lr] s s' := by
  have eZ : State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0) = coeffAddr (State.addr zB) k :=
    VG.Proof.MlDsa.Arm.Arith.addr_at0 hzf hk
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Arith.blkPre_ok len hl dop hop s h1 (by
    rw [eZ]; exact inRegions_of hzw (coeff_contains _ (show k < n by rw [n_eq]; exact hk))))
    fun s₁ ⟨e5, e6, e7, e1, e3, m₁, k₁⟩ => ?_)
  have hwv : s.mem.readW (State.addr (zB + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0)) 32 =
      BitVec.ofNat 32 (Z k).val := by
    rw [eZ, ← coeffAt_eq, ht k hk, hZ k hk]
  rw [hwv] at e5 e6 e7
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Arith.bflys_ok hb hp hlen hl hs (Z k) G s₁ ((k₁.gpr .r0 (by decide)).trans h0)
    ⟨(k₁.gpr .r4 (by decide)).trans h4, e5, e6, e7⟩ (by rw [m₁]; exact hG) (by rw [k₁.wr]; exact hw)
    (by rw [e3]; simp)) fun s₂ ⟨hP, hf, h0₂, k₂⟩ => ?_)
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.blkPost_ok len hl s₂) fun s' ⟨h0', h2', hz', m', k₃⟩ => ⟨by rw [m']; exact hP,
    by rw [m', ← m₁]; exact hf, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0', h0₂, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  · rw [k₃.gpr .r1 (by decide), k₂.gpr .r1 (by decide), e1, h1]; rfl
  · rw [h2', k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · rw [hz', k₂.gpr .r2 (by decide), k₁.gpr .r2 (by decide)]
  · exact ((k₁.mono (rs' := [.r4, .r11, .lr]) (by decide)).trans (k₂.mono (by decide))).trans
      (k₃.mono (by decide))

omit hb in
theorem layPre_ok (c : Nat) (hc : c ≤ 128) (s : State) :
    WP isa (.block [.mov .r2 (.imm (BitVec.ofNat 32 c))]) s fun s' =>
      s'.gpr .r2 = BitVec.ofNat 32 c ∧ s'.mem = s.mem ∧ VG.Proof.MlDsa.Arm.Arith.Keep [.r0, .r1, .r4, .r11, .lr] s s' := by
  have he : encodable (BitVec.ofNat 32 c) = true := by
    have : ∀ l < 129, encodable (BitVec.ofNat 32 l) = true := by decide
    exact this c (by omega)
  run_block [he]
  keep_simp

omit hb in
theorem layPost_ok (s : State) :
    WP isa (.block [.dp .sub .r0 .r0 (.imm 1024)]) s fun s' =>
      s'.gpr .r0 = s.gpr .r0 - 1024 ∧ s'.mem = s.mem ∧ VG.Proof.MlDsa.Arm.Arith.Keep [.r1, .r4, .r11, .lr] s s' := by
  run_block []
  keep_simp

omit hb in
/-- The facts about the lengths of the layers. -/
theorem lens_facts : ∀ len ∈ nttLens, 0 < len ∧ len ≤ 128 ∧ 2 * len * (128 / len) = 256 ∧ 0 < 128 / len ∧
    128 / len ≤ 128 := by
  decide

/-- A layer, from `r0` = `f` and the zeta of its first block at `r1`. -/
theorem lay_ok {tab : Nat → Nat} {Z : Nat → Zq} (hZ : VG.Proof.MlDsa.Arm.Arith.TabOf tab Z) {p zB : BitVec 32}
    (hp : p.toNat + 1024 ≤ 2 ^ 32) (hzf : zB.toNat + 1024 ≤ 2 ^ 32) {len : Nat} (hlen : len ∈ nttLens)
    (dop : DpOp) (hop : dop = .add ∨ dop = .sub) (zi : Nat → Nat) (hzi : ∀ c < 128 / len, zi c < 256)
    (hstep : ∀ c < 128 / len, VG.Proof.MlDsa.Arm.Arith.nextZ dop (zB + BitVec.ofNat 32 (4 * zi c)) = zB + BitVec.ofNat 32 (4 * zi (c + 1)))
    (F : Poly) (s : State) (h0 : s.gpr .r0 = p) (h1 : s.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi 0))
    (h4 : s.gpr .r4 = Qw) (hF : PolyIs s.mem (State.addr p) F) (hw : polyRegion (State.addr p) ∈ s.wr)
    (hzw : polyRegion (State.addr zB) ∈ s.rd ++ s.wr)
    (hd : (polyRegion (State.addr zB)).Disjoint (polyRegion (State.addr p))) (ht : VG.Proof.MlDsa.Arm.Arith.Tab tab s.mem (State.addr zB)) :
    WP isa (nttLay (code len) len dop) s fun s' =>
      PolyIs s'.mem (State.addr p) (layerN op F len (fun c => Z (zi c)) (128 / len)) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p ∧
        s'.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi (128 / len)) ∧ VG.Proof.MlDsa.Arm.Arith.Keep [.r4, .r11, .lr] s s' := by
  obtain ⟨hl0, hl1, hl2, hl3, hl4⟩ := VG.Proof.MlDsa.Arm.Arith.lens_facts len hlen
  have hdd : ∀ r ∈ [polyRegion (State.addr p)], (polyRegion (State.addr zB)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hd
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Arith.layPre_ok (128 / len) hl4 s) fun s₁ ⟨e2, m₁, k₁⟩ => WP.seq ?_)
  refine WP.mono (Q := fun (s₂ : State) => PolyIs s₂.mem (State.addr p) (layerN op F len (fun c => Z (zi c)) (128 / len)) ∧
      Frame [polyRegion (State.addr p)] s.mem s₂.mem ∧ s₂.gpr .r0 = p + BitVec.ofNat 32 (4 * 256) ∧
      s₂.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi (128 / len)) ∧ VG.Proof.MlDsa.Arm.Arith.Keep [.r4, .r11, .lr] s s₂) ?_
    fun s₂ ⟨hP, hf, h0₂, h1₂, k₂⟩ => ?_
  · refine wp_loop_ne (fun c s' => PolyIs s'.mem (State.addr p) (layerN op F len (fun c => Z (zi c)) c) ∧
        Frame [polyRegion (State.addr p)] s.mem s'.mem ∧ s'.gpr .r0 = p + BitVec.ofNat 32 (4 * (2 * len * c)) ∧
        s'.gpr .r1 = zB + BitVec.ofNat 32 (4 * zi c) ∧ s'.gpr .r2 = BitVec.ofNat 32 (1 * (128 / len - c)) ∧
        VG.Proof.MlDsa.Arm.Arith.Keep [.r4, .r11, .lr] s s') hl3 (fun c hc s' ⟨hP, hf, h0', h1', h2', hk⟩ => ?_)
      (fun s' ⟨hP, hf, h0', h1', _, hk⟩ => ⟨hP, hf, by rw [h0', hl2], h1', hk⟩)
      ⟨by rw [m₁]; exact hF, by rw [m₁]; exact Frame.refl _ _, by rw [k₁.gpr .r0 (by decide), h0]; simp,
        by rw [k₁.gpr .r1 (by decide), h1], by rw [e2]; simp, k₁.mono (by decide)⟩
    have hcm : 2 * len * c + 2 * len ≤ 256 := by
      have : 2 * len * (c + 1) ≤ 2 * len * (128 / len) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this; omega
    refine WP.mono (VG.Proof.MlDsa.Arm.Arith.blk_ok hb hZ hp hzf hl0 hl1 hcm (hzi c hc) dop hop _ s' h0' h1'
      ((hk.gpr .r4 (by decide)).trans h4) hP (by rw [hk.wr]; exact hw) (by rw [hk.rd, hk.wr]; exact hzw)
      (ht.frame hf hdd)) fun s'' ⟨hP', hf', h0'', h1'', h2'', hz'', hk'⟩ => ⟨⟨?_, hf.trans hf', ?_, ?_, ?_,
        hk.trans hk'⟩, ?_⟩
    · rw [layerN_succ]; exact hP'
    · rw [h0'', Nat.mul_succ]
    · rw [h1'', h1', hstep c hc]
    · rw [h2'', h2']; exact count_sub (k := 1) hc
    · rw [hz'', h2']; exact count_z (k := 1) hc (by decide) (by omega)
  · refine WP.mono (VG.Proof.MlDsa.Arm.Arith.layPost_ok s₂) fun s' ⟨h0', m', k₃⟩ => ⟨by rw [m']; exact hP, by rw [m']; exact hf, ?_,
      by rw [k₃.gpr .r1 (by decide), h1₂], k₂.trans (k₃.mono (by decide))⟩
    rw [h0', h0₂]
    exact BitVec.add_sub_cancel _ _

end

end VG.Proof.MlDsa.Arm.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Arith.Ntt`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_ntt`

The table stored and `q` loaded (`pro_ok`); each layer is `nttLayer` (`lay_ok`
with `bfly_spec`), and the eight layers are `NTT` (`ntt_eq_layers`), all in
the frames that save `r4`–`r10` (`wp_saving`). `LI`, `pro_ok`, `PreE` and
`pre_entry` serve `NTT⁻¹` too.
-/

namespace VG.Proof.MlDsa.Arm.Arith.Ntt

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arm.Arith.AddSub (reduced_zero)

section
variable (s : State)

abbrev pf : BitVec 32 := s.gpr .r0
abbrev ps : BitVec 32 := s.gpr .r1
abbrev F : Addr := State.addr (VG.Proof.MlDsa.Arm.Arith.Ntt.pf s)
abbrev S : Addr := State.addr (VG.Proof.MlDsa.Arm.Arith.Ntt.ps s)

end

/-- The precondition of both transforms, on entry. -/
structure PreE (s : State) : Prop where
  sp : 28 ≤ s.sp.toNat
  rd : s.rd = []
  wr : s.wr = [polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.F s), polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.S s)]
  fs : (polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.F s)).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.S s))
  sF : (belowA s.sp 28).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.F s))
  sS : (belowA s.sp 28).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.S s))
  fitF : (VG.Proof.MlDsa.Arm.Arith.Ntt.pf s).toNat + 1024 ≤ 2 ^ 32
  fitS : (VG.Proof.MlDsa.Arm.Arith.Ntt.ps s).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s)

/-- What the transforms need of the state after the pushes. -/
structure PreB (s : State) : Prop where
  wF : polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.F s) ∈ s.wr
  wS : polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.S s) ∈ s.wr
  fs : (polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.F s)).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.S s))
  fitF : (VG.Proof.MlDsa.Arm.Arith.Ntt.pf s).toNat + 1024 ≤ 2 ^ 32
  fitS : (VG.Proof.MlDsa.Arm.Arith.Ntt.ps s).toNat + 1024 ≤ 2 ^ 32
  red : Reduced s.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s)

theorem pre_entry {s s₁ : State} (hp : VG.Proof.MlDsa.Arm.Arith.Ntt.PreE s) (hE : Entry 28 s s₁) :
    VG.Proof.MlDsa.Arm.Arith.Ntt.PreB s₁ ∧ polyAt s₁.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s₁) = polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s) ∧ VG.Proof.MlDsa.Arm.Arith.Ntt.F s₁ = VG.Proof.MlDsa.Arm.Arith.Ntt.F s ∧ VG.Proof.MlDsa.Arm.Arith.Ntt.S s₁ = VG.Proof.MlDsa.Arm.Arith.Ntt.S s := by
  have g := hE.gpr
  have eF : VG.Proof.MlDsa.Arm.Arith.Ntt.F s₁ = VG.Proof.MlDsa.Arm.Arith.Ntt.F s := by simp only [VG.Proof.MlDsa.Arm.Arith.Ntt.F, VG.Proof.MlDsa.Arm.Arith.Ntt.pf, g]
  have eS : VG.Proof.MlDsa.Arm.Arith.Ntt.S s₁ = VG.Proof.MlDsa.Arm.Arith.Ntt.S s := by simp only [VG.Proof.MlDsa.Arm.Arith.Ntt.S, VG.Proof.MlDsa.Arm.Arith.Ntt.ps, g]
  have dF : ∀ r ∈ [belowA s.sp 28], (polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.F s)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.sF.symm
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [eF]; exact polyAt_frame hE.frame dF, eF, eS⟩
  · rw [eF]; exact hE.wr _ (by rw [hp.wr]; simp)
  · rw [eS]; exact hE.wr _ (by rw [hp.wr]; simp)
  · rw [eF, eS]; exact hp.fs
  · simp only [VG.Proof.MlDsa.Arm.Arith.Ntt.pf, g]; exact hp.fitF
  · simp only [VG.Proof.MlDsa.Arm.Arith.Ntt.ps, g]; exact hp.fitS
  · rw [eF]; exact reduced_frame hE.frame dF hp.red

/-- Between layers: the polynomial `G` at `f`, the table `tab` at `scratch`,
and entry `k` of the table at `r1`, from the state `s₁` after the pushes. -/
structure LI (tab : Nat → Nat) (s₁ : State) (G : Poly) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = VG.Proof.MlDsa.Arm.Arith.Ntt.pf s₁
  r1 : s.gpr .r1 = VG.Proof.MlDsa.Arm.Arith.Ntt.ps s₁ + BitVec.ofNat 32 (4 * k)
  r4 : s.gpr .r4 = Qw
  poly : PolyIs s.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s₁) G
  tab : VG.Proof.MlDsa.Arm.Arith.Tab tab s.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.S s₁)
  frame : Frame [polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.F s₁), polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.S s₁)] s₁.mem s.mem
  keep : VG.Proof.MlDsa.Arm.Arith.Keep [.r11, .lr] s₁ s

theorem LI.step {tab : Nat → Nat} {s₁ : State} {G G' : Poly} {k k' : Nat} {s s' : State}
    (hI : VG.Proof.MlDsa.Arm.Arith.Ntt.LI tab s₁ G k s) (hP : PolyIs s'.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s₁) G') (hf : Frame [polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.F s₁)] s.mem s'.mem)
    (h0 : s'.gpr .r0 = VG.Proof.MlDsa.Arm.Arith.Ntt.pf s₁) (h1 : s'.gpr .r1 = VG.Proof.MlDsa.Arm.Arith.Ntt.ps s₁ + BitVec.ofNat 32 (4 * k'))
    (hk : VG.Proof.MlDsa.Arm.Arith.Keep [.r4, .r11, .lr] s s') (hd : (polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.S s₁)).Disjoint (polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.F s₁))) :
    VG.Proof.MlDsa.Arm.Arith.Ntt.LI tab s₁ G' k' s' :=
  ⟨h0, h1, (hk.gpr .r4 (by decide)).trans hI.r4, hP,
    hI.tab.frame hf (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd),
    hI.frame.trans (hf.mono (by simp)), hI.keep.trans (hk.mono (by decide))⟩

/-- The chain of zeta indices of the layers `ls` of `NTT`, from `k`. -/
def Chain : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 128 / len ∧ VG.Proof.MlDsa.Arm.Arith.Ntt.Chain (256 / len) ls

theorem lens_fwd : ∀ len ∈ nttLens, 128 / len + 128 / len = 256 / len ∧ 256 / len ≤ 256 := by decide

theorem zetaTab_of : VG.Proof.MlDsa.Arm.Arith.TabOf zetaTab zetas := fun k _ => zetaNat_eq k

theorem zetaTab_lt : ∀ k < 256, zetaTab k < q := fun k _ => zetaNat_lt k

theorem lays_ok {s₁ : State} (hp : VG.Proof.MlDsa.Arm.Arith.Ntt.PreB s₁) :
    ∀ (ls : List Nat) (G : Poly) (k : Nat) (s : State), (∀ len ∈ ls, len ∈ nttLens) → VG.Proof.MlDsa.Arm.Arith.Ntt.Chain k ls →
      VG.Proof.MlDsa.Arm.Arith.Ntt.LI zetaTab s₁ G k s →
      WP isa (nttLays ls) s fun s' => ∃ k', VG.Proof.MlDsa.Arm.Arith.Ntt.LI zetaTab s₁ (ls.foldl nttLayer G) k' s'
  | [], G, k, s, _, _, hI => WP.block_nil ⟨k, hI⟩
  | len :: ls, G, k, s, hls, ⟨hk, hc⟩, hI => by
    have hlen := hls len (List.mem_cons_self ..)
    obtain ⟨h1, h2⟩ := VG.Proof.MlDsa.Arm.Arith.Ntt.lens_fwd len hlen
    refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Arith.lay_ok VG.Proof.MlDsa.Arm.Arith.bfly_spec VG.Proof.MlDsa.Arm.Arith.Ntt.zetaTab_of hp.fitF hp.fitS hlen .add (.inl rfl)
      (fun c => 128 / len + c) (fun c hc => by omega)
      (fun c _ => by
        simp only [VG.Proof.MlDsa.Arm.Arith.nextZ, ite_true, BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
          ← BitVec.ofNat_add]
        congr 2)
      G s hI.r0 (by rw [hI.r1, hk]; rfl) hI.r4 hI.poly (by rw [hI.keep.wr]; exact hp.wF)
      (by rw [hI.keep.wr]; exact List.mem_append_right _ hp.wS) hp.fs.symm hI.tab)
      fun s' ⟨hP, hf, h0, h1', hk'⟩ => ?_)
    exact VG.Proof.MlDsa.Arm.Arith.Ntt.lays_ok hp ls _ (256 / len) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf h0 (by rw [h1', ← h1]) hk' hp.fs.symm)

/-- The table `tab` to `scratch`, `q` to `r4`, and `r1` at entry `k`. -/
theorem pro_ok {s : State} (hp : VG.Proof.MlDsa.Arm.Arith.Ntt.PreB s) (tab : Nat → Nat) (ht : ∀ k < 256, tab k < q) (d : BitVec 32) (k : Nat)
    (hd : BitVec.ofNat 32 (4 * k) = d) (he : encodable d = true) :
    WP isa (.block (storeTab tab 256 ++ loadQ .r4 ++ ([.dp .add .r1 .r1 (.imm d)] : List Instr))) s
      (VG.Proof.MlDsa.Arm.Arith.Ntt.LI tab s (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s)) k) := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.storeTab_ok tab ht s (zB := VG.Proof.MlDsa.Arm.Arith.Ntt.ps s) rfl hp.fitS hp.wS) fun s₁ ⟨ht₁, hf₁, k₁⟩ => ?_
  have e1 : s₁.gpr .r1 = VG.Proof.MlDsa.Arm.Arith.Ntt.ps s := k₁.gpr .r1 (by decide)
  have e0 : s₁.gpr .r0 = VG.Proof.MlDsa.Arm.Arith.Ntt.pf s := k₁.gpr .r0 (by decide)
  run_block [loadQ, e0, e1, he, loadQ_val]
  refine ⟨by simp [e0], by simp [hd], by simp, ?_, ht₁, hf₁.mono (by simp), ?_⟩
  · exact polyIs_frame hf₁ (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.fs) ⟨hp.red, rfl⟩
  · exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [k₁.gpr _ (by decide : Reg.r11 ∈ _), k₁.gpr _ (by decide : Reg.lr ∈ _)],
      k₁.rd, k₁.wr, k₁.sp⟩

theorem chain_fwd : VG.Proof.MlDsa.Arm.Arith.Ntt.Chain 1 nttLens := by simp only [nttLens, VG.Proof.MlDsa.Arm.Arith.Ntt.Chain]; decide

theorem pre_of {s : State} (h : (Spec.MlDsa.nttContract Arm.abi 28).pre s) : VG.Proof.MlDsa.Arm.Arith.Ntt.PreE s := by
  sig_pre [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- The frames' region is disjoint from the buffers. -/
theorem stack_disj {s : State} (hp : VG.Proof.MlDsa.Arm.Arith.Ntt.PreE s) :
    ∀ R ∈ [polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.F s), polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.S s)], (belowA s.sp (4 * nttSaved.length)).Disjoint R := by
  intro R hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl
  exacts [hp.sF, hp.sS]

/-- The callee-saved registers, from those `saving nttSaved` restores. -/
theorem preserved_of {s s' s₂ : State}
    (hg : ∀ r, s'.gpr r = if r ∈ nttSaved then s.gpr r else s₂.gpr r)
    (h11 : s₂.gpr .r11 = s.gpr .r11) (hlr : s₂.gpr .lr = s.gpr .lr) : ∀ r ∈ preserved, s'.gpr r = s.gpr r :=
  preserved_of_saving hg fun r hr hn => by
    simp only [preserved, nttSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hn
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hn
    exacts [h11, hlr]

theorem correct {s : State} (hp : VG.Proof.MlDsa.Arm.Arith.Ntt.PreE s) :
    WP isa Impl.MlDsa.Arm.Arith.ntt s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s) (Spec.MlDsa.ntt (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s))) := by
  refine WP.mono (wp_saving nttSaved _ (W := [polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.F s), polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.S s)])
    (fun s₂ => s₂.gpr .r11 = s.gpr .r11 ∧ s₂.gpr .lr = s.gpr .lr ∧
      PolyIs s₂.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s) (Spec.MlDsa.ntt (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s))))
    s hp.sp (VG.Proof.MlDsa.Arm.Arith.Ntt.stack_disj hp) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨h11, hlr, hq⟩, hm, _, hsp, _, hg⟩ => ⟨VG.Proof.MlDsa.Arm.Arith.Ntt.preserved_of hg h11 hlr, hsp, hm ▸ hq⟩
  obtain ⟨hpB, eP, eF, eS⟩ := VG.Proof.MlDsa.Arm.Arith.Ntt.pre_entry hp hE
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Arith.Ntt.pro_ok hpB zetaTab VG.Proof.MlDsa.Arm.Arith.Ntt.zetaTab_lt 4 1 rfl (by decide)) fun s₂ hI => ?_)
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.Ntt.lays_ok hpB nttLens _ 1 s₂ (fun _ h => h) VG.Proof.MlDsa.Arm.Arith.Ntt.chain_fwd hI) fun s₃ ⟨k, hI'⟩ => ?_
  refine ⟨by rw [← eF, ← eS]; exact hI'.frame, ?_, ?_, ?_⟩
  · rw [hI'.keep.gpr .r11 (by decide)]; exact congrFun hE.gpr _
  · rw [hI'.keep.gpr .lr (by decide)]; exact congrFun hE.gpr _
  · rw [← eP, ← eF, VG.Proof.MlDsa.Arith.ntt_eq_layers]; exact hI'.poly

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Arith.ntt (Spec.MlDsa.nttContract Arm.abi 28) := by
  refine ⟨fun s hs => ?_, ct_of_saving nttSaved _ [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := VG.Proof.MlDsa.Arm.Arith.Ntt.correct (VG.Proof.MlDsa.Arm.Arith.Ntt.pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · refine ⟨VG.Proof.MlDsa.Arm.Arith.Ntt.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.nttContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi,
        Arm.argRegs, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact VG.Proof.MlDsa.Arm.Arith.AddSub.reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.Ntt

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttInv`. -/
section

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_inv_ntt`

As `vg_mldsa_ntt` (`Ntt.lean`), with the negated zetas, from the last, and
`bflyInv_spec`: the eight layers are those of `NTT⁻¹` (`nttInvLayer`); then
every coefficient is multiplied by `8347681 = 256⁻¹ mod q` (`scale_ok`), which
`nttInv_eq_layers` says is `NTT⁻¹`.
-/

namespace VG.Proof.MlDsa.Arm.Arith.NttInv

open VG VG.Arm VG.Impl.MlDsa.Arm.Arith
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs zetas)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arm.Arith.Ntt
open VG.Proof.MlKem.Arm (wp_loop_ne count_z count_sub addr_ptr inRegions_of)
open VG.Proof.MlDsa.Arm.Arith.AddSub (reduced_zero)

/-! ## The layers -/

/-- The chain of zeta indices of the layers `ls` of `NTT⁻¹`, from `k`. -/
def ChainInv : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 256 / len - 1 ∧ VG.Proof.MlDsa.Arm.Arith.NttInv.ChainInv (128 / len - 1) ls

theorem lens_inv : ∀ len ∈ nttInvLens, len ∈ nttLens ∧ 128 / len ≤ 256 / len - 1 ∧ 256 / len ≤ 256 ∧
    256 / len = 2 * (128 / len) := by decide

theorem negZetaTab_of : VG.Proof.MlDsa.Arm.Arith.TabOf negZetaTab (fun m => -zetas m) := fun k _ => negZetaNat_eq k

theorem negZetaTab_lt : ∀ k < 256, negZetaTab k < q := fun k _ => negZetaNat_lt k

theorem lays_ok {s₁ : State} (hp : VG.Proof.MlDsa.Arm.Arith.Ntt.PreB s₁) :
    ∀ (ls : List Nat) (G : Poly) (k : Nat) (s : State), (∀ len ∈ ls, len ∈ nttInvLens) → VG.Proof.MlDsa.Arm.Arith.NttInv.ChainInv k ls →
      VG.Proof.MlDsa.Arm.Arith.Ntt.LI negZetaTab s₁ G k s →
      WP isa (nttInvLays ls) s fun s' => ∃ k', VG.Proof.MlDsa.Arm.Arith.Ntt.LI negZetaTab s₁ (ls.foldl nttInvLayer G) k' s'
  | [], G, k, s, _, _, hI => WP.block_nil ⟨k, hI⟩
  | len :: ls, G, k, s, hls, ⟨hk, hc⟩, hI => by
    obtain ⟨hlen, h1, h2, h3⟩ := VG.Proof.MlDsa.Arm.Arith.NttInv.lens_inv len (hls len (List.mem_cons_self ..))
    have hl0 := (VG.Proof.MlDsa.Arm.Arith.lens_facts len hlen).2.2.2.1
    refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Arith.lay_ok VG.Proof.MlDsa.Arm.Arith.bflyInv_spec VG.Proof.MlDsa.Arm.Arith.NttInv.negZetaTab_of hp.fitF hp.fitS hlen .sub (.inr rfl)
      (fun c => 256 / len - 1 - c) (fun c hc => by omega)
      (fun c hc => by
        simp only [VG.Proof.MlDsa.Arm.Arith.nextZ, reduceCtorEq, ite_false]
        rw [show 4 * (256 / len - 1 - c) = 4 * (256 / len - 1 - (c + 1)) + 4 by omega, BitVec.ofNat_add,
          ← BitVec.add_assoc]
        exact BitVec.add_sub_cancel _ _)
      G s hI.r0 (by rw [hI.r1, hk]; rfl) hI.r4 hI.poly (by rw [hI.keep.wr]; exact hp.wF)
      (by rw [hI.keep.wr]; exact List.mem_append_right _ hp.wS) hp.fs.symm hI.tab)
      fun s' ⟨hP, hf, h0, h1', hk'⟩ => ?_)
    refine VG.Proof.MlDsa.Arm.Arith.NttInv.lays_ok hp ls _ (128 / len - 1) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc
      (hI.step hP hf h0 (by rw [h1']; congr 3; omega) hk' hp.fs.symm)

theorem chain_inv : VG.Proof.MlDsa.Arm.Arith.NttInv.ChainInv 255 nttInvLens := by simp only [nttInvLens, VG.Proof.MlDsa.Arm.Arith.NttInv.ChainInv]; decide

/-! ## The scaling -/

/-- The scaling after the load and `mulz`. -/
def scaleRest : List Instr :=
  csub .r9 .r12 .r4 ++ [.str .r9 .r0 0, .dp .add .r0 .r0 (.imm 4), .subs .r3 .r3 (.imm 1)]

theorem scale_split : scaleBody = ([.ldr .r8 .r0 0] : List Instr) ++ (mulz .r9 .r8 .r12 ++ VG.Proof.MlDsa.Arm.Arith.NttInv.scaleRest) := by
  simp only [scaleBody, VG.Proof.MlDsa.Arm.Arith.NttInv.scaleRest, List.append_assoc, List.cons_append, List.nil_append]

section
variable {s : State} {x c v : BitVec 32} (h0 : s.gpr .r0 = x) (h3 : s.gpr .r3 = c) (h4 : s.gpr .r4 = Qw)
  (h9 : s.gpr .r9 = v) (oA : InRegions s.wr (State.addr (x + BitVec.ofNat 32 0)) 4)
include h0 h3 h4 h9 oA

theorem scaleRest_ok :
    WP isa (.block VG.Proof.MlDsa.Arm.Arith.NttInv.scaleRest) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (x + BitVec.ofNat 32 0)) (bcsub v) ∧
      s'.gpr .r0 = x + 4 ∧ s'.gpr .r3 = c - 1 ∧ s'.z = (c - 1 == 0) ∧ VG.Proof.MlDsa.Arm.Arith.Keep VG.Proof.MlDsa.Arm.Arith.bflyKeep s s' := by
  run_block [VG.Proof.MlDsa.Arm.Arith.NttInv.scaleRest, csub, VG.Impl.MlDsa.Arm.Arith.fixup, bcsub, bfix, h0, h3, h4, h9, oA]
  keep_simp

end

/-- The multiplier of the scaling. -/
abbrev cInv : Zq := 8347681

/-- After `t` coefficients of the polynomial `G` at `p` are scaled. -/
structure SInv (p : BitVec 32) (m₀ : Mem) (G : Poly) (s₀ : State) (t : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = p + BitVec.ofNat 32 (4 * t)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (1 * (256 - t))
  zeta : VG.Proof.MlDsa.Arm.Arith.ZetaIn VG.Proof.MlDsa.Arm.Arith.NttInv.cInv s
  keep : VG.Proof.MlDsa.Arm.Arith.Keep VG.Proof.MlDsa.Arm.Arith.bflyKeep s₀ s
  frame : Frame [polyRegion (State.addr p)] m₀ s.mem
  coeff : ∀ j < 256, coeffAt s.mem (State.addr p) j =
    if j < t then BitVec.ofNat 32 (G[j]! * VG.Proof.MlDsa.Arm.Arith.NttInv.cInv).val else coeffAt m₀ (State.addr p) j

theorem scale_step {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {m₀ : Mem} {G : Poly}
    (hG : PolyIs m₀ (State.addr p) G) {s₀ : State} (hw : polyRegion (State.addr p) ∈ s₀.wr) {t : Nat}
    (ht : t < 256) {s : State} (h : VG.Proof.MlDsa.Arm.Arith.NttInv.SInv p m₀ G s₀ t s) :
    WP isa (.block scaleBody) s fun s' => VG.Proof.MlDsa.Arm.Arith.NttInv.SInv p m₀ G s₀ (t + 1) s' ∧ s'.z = decide (t + 1 = 256) := by
  obtain ⟨z4, z5, z6, z7⟩ := h.zeta
  have htn : t < n := by rw [n_eq]; exact ht
  have eA := VG.Proof.MlDsa.Arm.Arith.addr_at0 hp ht
  have hw' : polyRegion (State.addr p) ∈ s.wr := by rw [h.keep.wr]; exact hw
  have hv : s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 0)) 32 = BitVec.ofNat 32 (G[t]!).val := by
    rw [h.r0, eA, ← coeffAt_eq, h.coeff t ht, ite_eq_right (Nat.lt_irrefl t), coeffAt_eq, VG.Proof.MlDsa.Arm.Arith.word_val hG ht]
  rw [VG.Proof.MlDsa.Arm.Arith.NttInv.scale_split, WP.block_append_iff]
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_ldr (by omega) (by rw [h.r0, eA]; exact VG.Proof.MlDsa.Arm.Arith.rd_at hw' htn), runStep_some, runBlock_nil], ?_⟩
  rw [WP.block_append_iff, hv]
  refine WP.mono (mulz_ok (s := s.setReg .r8 _) (b := BitVec.ofNat 32 (G[t]!).val)
    (z₂ := BitVec.ofNat 32 cInv.val >>> 14) (z₁ := BitVec.ofNat 32 cInv.val <<< 18 >>> 25)
    (z₀ := BitVec.ofNat 32 cInv.val <<< 25 >>> 25) (by simp [State.setReg, z4]) (by simp [State.setReg, z5])
    (by simp [State.setReg, z6]) (by simp [State.setReg, z7]) (by simp [State.setReg]))
    fun s₁ ⟨e9, eo, m₁, rd₁, wr₁, sp₁⟩ => ?_
  have g : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r12 → s₁.gpr r = s.gpr r := fun r a8 a9 a12 => by
    rw [eo r a9 a12]; simp [State.setReg, a8]
  have nk : ∀ r ∈ VG.Proof.MlDsa.Arm.Arith.bflyKeep, r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r12 := by decide
  have k₁ : VG.Proof.MlDsa.Arm.Arith.Keep VG.Proof.MlDsa.Arm.Arith.bflyKeep s s₁ := ⟨fun r hr => g r (nk r hr).1 (nk r hr).2.1 (nk r hr).2.2, rd₁, wr₁, sp₁⟩
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.NttInv.scaleRest_ok ((g _ (by decide) (by decide) (by decide)).trans h.r0)
    ((g _ (by decide) (by decide) (by decide)).trans h.r3) ((g _ (by decide) (by decide) (by decide)).trans z4) e9
    (by rw [eA, wr₁]; exact VG.Proof.MlDsa.Arm.Arith.wr_at hw' htn)) fun s' ⟨hm, r0, r3, hzf, k₂⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [r0]; exact VG.Proof.MlDsa.Arm.Arith.ptr_next p t
  · rw [r3]; exact count_sub (k := 1) ht
  · have k := k₁.trans k₂
    exact ⟨(k.gpr .r4 (by decide)).trans z4, (k.gpr .r5 (by decide)).trans z5, (k.gpr .r6 (by decide)).trans z6,
      (k.gpr .r7 (by decide)).trans z7⟩
  · exact (h.keep.trans k₁).trans k₂
  · rw [hm, m₁, eA]
    exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ htn)
  · intro j hj
    rw [hm, m₁, eA, VG.Proof.MlDsa.Arm.Arith.mulz_val, coeffAt_writeW _ _ (show j < n by rw [n_eq]; exact hj) htn]
    simp only [State.setReg]
    rw [h.coeff j hj]
    by_cases e : t = j
    · subst e; rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self t), Fin.mul_comm]
    · rw [ite_eq_right e]
      by_cases hj' : j < t
      · rw [ite_eq_left hj', ite_eq_left (by omega)]
      · rw [ite_eq_right hj', ite_eq_right (by omega)]
  · rw [hzf]; exact count_z (k := 1) ht (by decide) (by decide)

theorem scale_ok {p : BitVec 32} (hp : p.toNat + 1024 ≤ 2 ^ 32) {G : Poly} {s : State}
    (hG : PolyIs s.mem (State.addr p) G) (hw : polyRegion (State.addr p) ∈ s.wr) (h0 : s.gpr .r0 = p)
    (h4 : s.gpr .r4 = Qw) :
    WP isa (.seq (.block [.movw .r5 509, .movw .r6 64, .movw .r7 33, .mov .r3 (.imm 256)])
      (.loop (.block scaleBody) .ne)) s fun s' =>
      PolyIs s'.mem (State.addr p) (G.map (· * VG.Proof.MlDsa.Arm.Arith.NttInv.cInv)) ∧ Frame [polyRegion (State.addr p)] s.mem s'.mem ∧
        VG.Proof.MlDsa.Arm.Arith.Keep [.r4, .r11, .lr] s s' := by
  refine WP.seq (WP.mono (Q := fun s₁ => VG.Proof.MlDsa.Arm.Arith.NttInv.SInv p s.mem G s₁ 0 s₁ ∧ VG.Proof.MlDsa.Arm.Arith.Keep [.r4, .r11, .lr] s s₁) ?_
    fun s₁ ⟨h₁, k₁⟩ => ?_)
  · run_block [h0, h4]
    refine ⟨⟨by simp [h0], by simp, ⟨by simp [h4], by simp; decide, by simp; decide, by simp; decide⟩, Keep.refl _ _,
      Frame.refl _ _, fun j _ => by simp⟩, ?_⟩
    keep_simp
  · refine wp_loop_ne (VG.Proof.MlDsa.Arm.Arith.NttInv.SInv p s.mem G s₁) (N := 256) (by decide)
      (fun t ht s' h => VG.Proof.MlDsa.Arm.Arith.NttInv.scale_step hp hG (by rw [k₁.wr]; exact hw) ht h) (fun s' h => ?_) h₁
    refine ⟨polyIs_of_toNat fun j hj => ?_, h.frame, k₁.trans (h.keep.mono (by decide))⟩
    rw [h.coeff j (by rw [n_eq] at hj; exact hj), ite_eq_left (by rw [n_eq] at hj; exact hj), toNat_val,
      map_mul_get _ _ hj]

theorem pre_of {s : State} (h : (Spec.MlDsa.nttInvContract Arm.abi 28).pre s) : VG.Proof.MlDsa.Arm.Arith.Ntt.PreE s := by
  sig_pre [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h1, -, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem correct {s : State} (hp : VG.Proof.MlDsa.Arm.Arith.Ntt.PreE s) :
    WP isa Impl.MlDsa.Arm.Arith.nttInv s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      PolyIs s'.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s) (Spec.MlDsa.nttInv (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s))) := by
  refine WP.mono (wp_saving nttSaved _ (W := [polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.F s), polyRegion (VG.Proof.MlDsa.Arm.Arith.Ntt.S s)])
    (fun s₂ => s₂.gpr .r11 = s.gpr .r11 ∧ s₂.gpr .lr = s.gpr .lr ∧
      PolyIs s₂.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s) (Spec.MlDsa.nttInv (polyAt s.mem (VG.Proof.MlDsa.Arm.Arith.Ntt.F s))))
    s hp.sp (VG.Proof.MlDsa.Arm.Arith.Ntt.stack_disj hp) fun s₁ hE => ?_)
    fun s' ⟨s₂, ⟨h11, hlr, hq⟩, hm, _, hsp, _, hg⟩ => ⟨VG.Proof.MlDsa.Arm.Arith.Ntt.preserved_of hg h11 hlr, hsp, hm ▸ hq⟩
  obtain ⟨hpB, eP, eF, eS⟩ := VG.Proof.MlDsa.Arm.Arith.Ntt.pre_entry hp hE
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Arith.Ntt.pro_ok hpB negZetaTab VG.Proof.MlDsa.Arm.Arith.NttInv.negZetaTab_lt 1020 255 rfl (by decide)) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.Arm.Arith.NttInv.lays_ok hpB nttInvLens _ 255 s₂ (fun _ h => h) VG.Proof.MlDsa.Arm.Arith.NttInv.chain_inv hI) fun s₃ ⟨k, hI'⟩ => ?_)
  refine WP.mono (VG.Proof.MlDsa.Arm.Arith.NttInv.scale_ok hpB.fitF hI'.poly (by rw [hI'.keep.wr]; exact hpB.wF) hI'.r0 hI'.r4)
    fun s₄ ⟨hP, hf, k₄⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [← eF, ← eS]; exact hI'.frame.trans (hf.mono (by simp))
  · rw [k₄.gpr .r11 (by decide), hI'.keep.gpr .r11 (by decide)]; exact congrFun hE.gpr _
  · rw [k₄.gpr .lr (by decide), hI'.keep.gpr .lr (by decide)]; exact congrFun hE.gpr _
  · rw [← eP, ← eF, VG.Proof.MlDsa.Arith.nttInv_eq_layers]; exact hP

theorem verified : Verified Arm.target Impl.MlDsa.Arm.Arith.nttInv (Spec.MlDsa.nttInvContract Arm.abi 28) := by
  refine ⟨fun s hs => ?_, ct_of_saving nttSaved _ [.r0, .r1] (fun s₁ s₂ h => ?_) (by taint_decide), ?_⟩
  · obtain ⟨t, s', he, hpres, hsp, h⟩ := VG.Proof.MlDsa.Arm.Arith.NttInv.correct (VG.Proof.MlDsa.Arm.Arith.NttInv.pre_of hs)
    refine ⟨t, s', he, ⟨hpres, hsp⟩, ?_⟩
    sig_post [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    exact h
  · sig_pub [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    obtain ⟨hsp, h0, h1⟩ := h
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · refine ⟨VG.Proof.MlDsa.Arm.Arith.Ntt.satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.nttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, Arm.abi,
        Arm.argRegs, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | exact VG.Proof.MlDsa.Arm.Arith.AddSub.reduced_zero _

end VG.Proof.MlDsa.Arm.Arith.NttInv

end
