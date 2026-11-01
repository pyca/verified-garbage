module

public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
public import VerifiedGarbage.Proof.Gcm.Clmul.Arith
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import Mathlib.Tactic.Ring.RingNF
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: isolate product and key-power proofs from the bulk-loop composition.
/-! # Packed polynomial products for POWER8 GHASH -/

@[expose] public section
namespace VG.Proof.Gcm.PPC64LE.Vpmsum
open VG VG.PPC64LE
open VG.Proof.Gcm.Clmul VG.Proof.Gcm.Poly
open VG.VectorCrypto (polyMul)
open VG.Impl.Gcm.PPC64LE.Vpmsum (Y C U LO MID HI A T H MASK Z)

def lowPair (a b : BitVec 128) : BitVec 128 := Clmul.vdword a 0 ++ Clmul.vdword b 0

def highPair (a b : BitVec 128) : BitVec 128 := Clmul.vdword a 1 ++ Clmul.vdword b 1

def pmPair (a b : BitVec 128) : BitVec 128 :=
  polyMul (Clmul.vdword a 0) (Clmul.vdword b 0) ^^^ polyMul (Clmul.vdword a 1) (Clmul.vdword b 1)

def pairedProd (a b ka kb : BitVec 128) : VG.Proof.Gcm.Clmul.Prod :=
  ⟨pmPair (highPair a b) (lowPair ka kb),
   pmPair (lowPair a b) (lowPair ka kb) ^^^ pmPair (highPair a b) (highPair ka kb),
   pmPair (lowPair a b) (highPair ka kb)⟩

theorem pairedProd_eq (a b ka kb : BitVec 128) :
    pairedProd a b ka kb =
      (VG.Proof.Gcm.Clmul.Prod.zero.acc a (ext8 ka ka) ka).acc b (ext8 kb kb) kb := by
  simp only [pairedProd, pmPair, lowPair, highPair, VG.Proof.Gcm.Clmul.Prod.acc,
      VG.Proof.Gcm.Clmul.Prod.zero, vdword_append_0, vdword_append_1,
      vdword_ext8_0, vdword_ext8_1]
  congr 1 <;> ac_rfl

theorem pairedProd_val (a b ka kb : BitVec 128) :
    (pairedProd a b ka kb).val = x * ρ a * φ ka + x * ρ b * φ kb := by
  rw [pairedProd_eq, VG.Proof.Gcm.Clmul.Prod.val_acc,
    VG.Proof.Gcm.Clmul.Prod.val_acc, VG.Proof.Gcm.Clmul.Prod.val_zero, zero_add]

def addProd (p q : VG.Proof.Gcm.Clmul.Prod) : VG.Proof.Gcm.Clmul.Prod :=
  ⟨p.lo ^^^ q.lo, p.mid ^^^ q.mid, p.hi ^^^ q.hi⟩

theorem addProd_val (p q : VG.Proof.Gcm.Clmul.Prod) : (addProd p q).val = p.val + q.val := by
  simp only [addProd, VG.Proof.Gcm.Clmul.Prod.val, φ_xor]
  ring

theorem half_swap_right (a b : BitVec 128) : half a (half b b) = lowPair a b := by
  rw [half, half, vdword_append_1]
  rfl

theorem swap_half_swap_left (a b : BitVec 128) :
    half (half (half b b) a) (half (half b b) a) = highPair a b := by
  rw [half_self, ext8_eq, half, half, vdword_append_0, vdword_append_1, vdword_append_0]
  rfl


def keyValue (h : BitVec 128) : Nat → BitVec 128
  | 0 => h
  | n+1 => ext8 (mulV (ext8 (keyValue h n) (keyValue h n)) h)
      (mulV (ext8 (keyValue h n) (keyValue h n)) h)

theorem keyValue_class (h : BitVec 128) (n : Nat) :
    x * φ (keyValue h n) = (x * φ h)^(n+1) := by
  induction n with
  | zero => simp only [keyValue, Nat.zero_add, pow_one]
  | succ n ih =>
    rw [keyValue, Clmul.φ_ext8_self, ρ_mulV, ρ_ext8_self, pow_succ]
    calc
      x * (x * φ (keyValue h n) * φ h) = (x * φ (keyValue h n)) * (x * φ h) := by ring
      _ = _ := by rw [ih]

theorem packedProducts_ok (loKey hiKey : VReg) (ka kb : BitVec 128) (s : State)
    (hl : Free loKey) (hh : Free hiKey)
    (hlo : s.vpr loKey = lowPair ka kb) (hhi : s.vpr hiKey = highPair ka kb) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.packedProducts loKey hiKey)) s fun t =>
      prod t = pairedProd (s.vpr A) (s.vpr HI) ka kb ∧ VOnly [HI, U, T, LO, MID] s t := by
  obtain ⟨hl2, hl3, -, hl5, hl7⟩ := hl
  obtain ⟨hh2, hh3, hh4, hh5, hh7⟩ := hh
  apply WP.of_runBlock
  simp only [Impl.Gcm.PPC64LE.Vpmsum.packedProducts, runBlock_cons, runStep_some, runBlock_nil,
    exec_shift8, exec_pm, exec_xor, vpr_writeV, Option.some.injEq, exists_eq_left',
    hl2, hl3, hl5, hl7, hh2, hh3, hh4, hh5, hh7, ite_true, ite_false, reduceCtorEq]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · simp only [prod, vpr_writeV, ite_true, ite_false, reduceCtorEq, hlo, hhi,
      half_swap_right, swap_half_swap_left, pairedProd, pmPair]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]


theorem swap_ok (d n : VReg) (s : State) :
    WP isa (.block [.vop (.sldoi d n n 8)]) s fun t =>
      t.vpr d = ext8 (s.vpr n) (s.vpr n) ∧ VOnly [d] s t := by
  refine WP.mono (vector_step _ d _ s (exec_shift8 d n n s)) fun t ⟨hv, hf⟩ => ?_
  exact ⟨hv.trans (half_self _), hf⟩

def nextKey (a h : BitVec 128) : BitVec 128 :=
  ext8 (mulV (ext8 a a) h) (mulV (ext8 a a) h)

theorem keyStep_ok (prev dest : VReg) (s : State)
    (hc : s.vpr C = Impl.Gcm.Clmul.poly ++ Impl.Gcm.Clmul.poly) (hz : s.vpr Z = 0) :
    WP isa (.block (([.vop (.sldoi A prev prev 8)] : List Instr) ++
      Impl.Gcm.PPC64LE.Vpmsum.mul dest A H ++ ([.vop (.sldoi dest dest dest 8)] : List Instr))) s fun t =>
      t.vpr dest = nextKey (s.vpr prev) (s.vpr H) ∧ VOnly [A,U,LO,MID,HI,T,dest] s t := by
  repeat rw [WP.block_append_iff]
  refine WP.mono (swap_ok A prev s) fun u ⟨ha, hu⟩ => ?_
  have hcu : u.vpr C = Impl.Gcm.Clmul.poly ++ Impl.Gcm.Clmul.poly := (hu.v C (by decide)).trans hc
  have hzu : u.vpr Z = 0 := (hu.v Z (by decide)).trans hz
  refine WP.mono (mul_ok dest A H u (by unfold Free; decide) (by unfold Free; decide) hcu hzu)
    fun v ⟨hv, hvf⟩ => ?_
  refine WP.mono (swap_ok dest dest v) fun t ⟨ht, htf⟩ => ?_
  refine ⟨?_, (hu.trans (hvf.trans htf)).weaken (by simp [or_left_comm, or_comm])⟩
  rw [ht, hv, ha, hu.v H (by decide)]
  rfl


open VG.Impl.Gcm.PPC64LE.Vpmsum (powerReg powerStep preparePowers)

def powerWritten : List VReg := [A,U,LO,MID,HI,T,.v8,.v9,.v10,.v11,.v12,.v13,.v14]

theorem power_free : ∀ j : Fin 8,
    powerReg (j+1) ≠ A ∧ powerReg (j+1) ≠ U ∧ powerReg (j+1) ≠ LO ∧
      powerReg (j+1) ≠ MID ∧ powerReg (j+1) ≠ HI ∧ powerReg (j+1) ≠ T := by decide

theorem power_injective : ∀ i j : Fin 8, powerReg (i+1) = powerReg (j+1) → i.val = j.val := by decide

theorem power_written : ∀ i : Fin 7, powerReg (i+2) ∈ powerWritten := by decide

theorem powers_ok (n : Nat) (hn : 0 < n) (hn8 : n ≤ 8) (s : State)
    (hc : s.vpr C = Impl.Gcm.Clmul.poly ++ Impl.Gcm.Clmul.poly) (hz : s.vpr Z = 0) :
    WP isa (.block (preparePowers n)) s fun t =>
      (∀ j < n, t.vpr (powerReg (j+1)) = keyValue (s.vpr H) j) ∧ VOnly powerWritten s t := by
  let I : Nat → State → Prop := fun k t =>
    (∀ j ≤ k, t.vpr (powerReg (j+1)) = keyValue (s.vpr H) j) ∧ VOnly powerWritten s t
  have step : ∀ k t, k < n-1 → I k t → WP isa (.block (powerStep k)) t (I (k+1)) := by
    rintro k t hk ⟨hvals, hf⟩
    have hk7 : k < 7 := by omega
    have hct : t.vpr C = Impl.Gcm.Clmul.poly ++ Impl.Gcm.Clmul.poly := (hf.v C (by decide)).trans hc
    have hzt : t.vpr Z = 0 := (hf.v Z (by decide)).trans hz
    unfold powerStep
    refine WP.mono (keyStep_ok (powerReg (k+1)) (powerReg (k+2)) t hct hzt) fun u ⟨hv, hu⟩ => ?_
    refine ⟨?_, (hf.trans hu).weaken ?_⟩
    · intro j hj
      by_cases hjk : j = k+1
      · subst j
        rw [show k+1+1 = k+2 by omega, hv, hvals k (Nat.le_refl _), hf.v H (by decide)]
        rfl
      · have hjk' : j ≤ k := by omega
        have hj8 : j < 8 := by omega
        have f := power_free ⟨j,hj8⟩
        have hne : powerReg (j+1) ≠ powerReg (k+2) := by
          intro he
          have he' := power_injective ⟨j,hj8⟩ ⟨k+1,by omega⟩ he
          exact hjk he'
        rw [hu.v (powerReg (j+1)) (by simp [f.1, f.2.1, f.2.2.1, f.2.2.2.1,
          f.2.2.2.2.1, f.2.2.2.2.2, hne])]
        exact hvals j hjk'
    · intro r hr
      simp only [List.mem_append] at hr
      rcases hr with hr | hr
      · exact hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try { simp [powerWritten] }
        exact power_written ⟨k,hk7⟩
  refine WP.mono (wp_range_flatMap (M := isa) I step (n-1) (Nat.le_refl _) s ?_) fun t ⟨hv,hf⟩ =>
    ⟨fun j hj => hv j (by omega), hf⟩
  refine ⟨?_, VOnly.refl _ _⟩
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  rfl


theorem exec_or (d n m : VReg) (s : State) :
    exec (.vop (.logic .or d n m)) s = some (s.writeV d (s.vpr n ||| s.vpr m)) := rfl

theorem packKeys_ok (a b lo hi : VReg) (s : State)
    (ha : a ≠ A) (hat : a ≠ T) (hlt : lo ≠ T) (hlh : lo ≠ hi) :
    WP isa (.block [.vop (.sldoi A b b 8),
      .vop (.sldoi T A a 8), .vop (.sldoi T T T 8),
      .vop (.sldoi lo a A 8), .vop (.logic .or hi T T)]) s fun t =>
      t.vpr lo = lowPair (s.vpr a) (s.vpr b) ∧
      t.vpr hi = highPair (s.vpr a) (s.vpr b) ∧ VOnly [A,T,lo,hi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_shift8, exec_or,
    vpr_writeV, ha, hat, ite_true, ite_false, reduceCtorEq, BitVec.or_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · simp only [hlh, ite_false, half_swap_right]
  · simp only [Ne.symm hlt, ite_false, swap_half_swap_left]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]


open VG.Impl.Gcm.PPC64LE.Vpmsum (keyLow keyHigh packKeyStep packedKeys)

def packedWritten : List VReg := [A,T,.v8,.v9,.v10,.v11,.v12,.v13,.v14,.v15]

theorem pair_key_free : ∀ j : Fin 4,
    Free (keyLow j) ∧ Free (keyHigh j) ∧ keyLow j ≠ A ∧ keyHigh j ≠ A ∧ keyLow j ≠ keyHigh j := by unfold Free; decide

theorem pair_key_disjoint : ∀ i j : Fin 4, i.val ≠ j.val →
    keyLow i ≠ keyLow j ∧ keyLow i ≠ keyHigh j ∧ keyHigh i ≠ keyLow j ∧ keyHigh i ≠ keyHigh j := by decide

theorem pair_key_remaining : ∀ i : Fin 8, ∀ j : Fin 4, i.val < 8-2*(j.val+1) →
    powerReg (i+1) ≠ keyLow j ∧ powerReg (i+1) ≠ keyHigh j := by decide

theorem pair_key_written : ∀ j : Fin 4, keyLow j ∈ packedWritten ∧ keyHigh j ∈ packedWritten := by decide

def PackedKeys (h : BitVec 128) (k : Nat) (s : State) : Prop :=
  ∀ j < k,
    s.vpr (keyLow j) = lowPair (keyValue h (7-2*j)) (keyValue h (6-2*j)) ∧
    s.vpr (keyHigh j) = highPair (keyValue h (7-2*j)) (keyValue h (6-2*j))

theorem packedKeys_ok (h : BitVec 128) (s : State)
    (hv : ∀ j < 8, s.vpr (powerReg (j+1)) = keyValue h j) :
    WP isa (.block packedKeys) s fun t => PackedKeys h 4 t ∧ VOnly packedWritten s t := by
  let I : Nat → State → Prop := fun k t => PackedKeys h k t ∧
    (∀ j < 8-2*k, t.vpr (powerReg (j+1)) = keyValue h j) ∧ VOnly packedWritten s t
  have step : ∀ k t, k < 4 → I k t → WP isa (.block (packKeyStep k)) t (I (k+1)) := by
    rintro k t hk ⟨hpacked,hplain,hf⟩
    have f := pair_key_free ⟨k,hk⟩
    have fa := power_free ⟨7-2*k,by omega⟩
    have ha : powerReg (8-2*k) ≠ A := by simpa only [show 7-2*k+1=8-2*k by omega] using fa.1
    have hat : powerReg (8-2*k) ≠ T := by simpa only [show 7-2*k+1=8-2*k by omega] using fa.2.2.2.2.2
    unfold packKeyStep
    refine WP.mono (packKeys_ok (powerReg (8-2*k)) (powerReg (7-2*k)) (keyLow k) (keyHigh k) t
      ha hat f.1.2.2.2.2 f.2.2.2.2) fun u ⟨hlo,hhi,hu⟩ => ?_
    have hpa : t.vpr (powerReg (8-2*k)) = keyValue h (7-2*k) := by
      simpa only [show 7-2*k+1=8-2*k by omega] using hplain (7-2*k) (by omega)
    have hpb : t.vpr (powerReg (7-2*k)) = keyValue h (6-2*k) := by
      simpa only [show 6-2*k+1=7-2*k by omega] using hplain (6-2*k) (by omega)
    refine ⟨?_, ?_, (hf.trans hu).weaken ?_⟩
    · intro j hj
      by_cases he : j=k
      · subst j
        exact ⟨hlo.trans (by rw [hpa,hpb]), hhi.trans (by rw [hpa,hpb])⟩
      · have hjk : j < k := by omega
        have fj := pair_key_free ⟨j,by omega⟩
        have fd := pair_key_disjoint ⟨j,by omega⟩ ⟨k,hk⟩ he
        have hlo' := hu.v (keyLow j) (by simp [fj.2.2.1, fj.1.2.2.2.2, fd.1, fd.2.1])
        have hhi' := hu.v (keyHigh j) (by simp [fj.2.2.2.1, fj.2.1.2.2.2.2, fd.2.2.1, fd.2.2.2])
        exact ⟨hlo'.trans (hpacked j hjk).1, hhi'.trans (hpacked j hjk).2⟩
    · intro j hj
      have fj := power_free ⟨j,by omega⟩
      have fd := pair_key_remaining ⟨j,by omega⟩ ⟨k,hk⟩ hj
      rw [hu.v (powerReg (j+1)) (by simp [fj.1, fj.2.2.2.2.2, fd.1, fd.2])]
      exact hplain j (by omega)
    · intro r hr
      simp only [List.mem_append] at hr
      rcases hr with hr | hr
      · exact hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · simp [packedWritten]
        · simp [packedWritten]
        · exact (pair_key_written ⟨k,hk⟩).1
        · exact (pair_key_written ⟨k,hk⟩).2
  refine WP.mono (wp_range_flatMap (M := isa) I step 4 (Nat.le_refl _) s ?_) fun t ⟨hp,_,hf⟩ => ⟨hp,hf⟩
  exact ⟨fun j hj => by omega, hv, VOnly.refl _ _⟩


noncomputable def pairTerm (h y : BitVec 128) (f : Nat → BitVec 128) (j : Nat) : Q :=
  x * ρ (if j=0 then f (2*j) ^^^ y else f (2*j)) * φ (keyValue h (7-2*j)) +
    x * ρ (f (2*j+1)) * φ (keyValue h (6-2*j))

noncomputable def pairSum (h y : BitVec 128) (f : Nat → BitVec 128) (n : Nat) : Q :=
  (List.range n).foldl (fun q j => q + pairTerm h y f j) 0

theorem pairSum_zero (h y : BitVec 128) (f : Nat → BitVec 128) : pairSum h y f 0 = 0 := rfl

theorem pairSum_succ (h y : BitVec 128) (f : Nat → BitVec 128) (n : Nat) :
    pairSum h y f (n+1) = pairSum h y f n + pairTerm h y f n := by
  simp only [pairSum, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

noncomputable def hashField (h y : Q) (f : Nat → Q) : Nat → Q
  | 0 => y
  | n+1 => (hashField h y f n + f n) * h

theorem keyValue_term (h a : BitVec 128) (n : Nat) :
    x * ρ a * φ (keyValue h n) = ρ a * (x * φ h)^(n+1) := by
  calc
    _ = ρ a * (x * φ (keyValue h n)) := by ring
    _ = _ := by rw [keyValue_class]

theorem pairSum_hash (h y : BitVec 128) (f : Nat → BitVec 128) :
    pairSum h y f 4 = hashField (x * φ h) (ρ y) (fun j => ρ (f j)) 8 := by
  simp only [pairSum_succ, pairSum_zero, pairTerm, Nat.reduceMul, Nat.reduceSub,
    Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, ↓keyValue_term, ρ_xor, hashField]
  ring

def accProd (s : State) : VG.Proof.Gcm.Clmul.Prod := ⟨s.vpr Y, s.vpr .v16, s.vpr .v17⟩

def savedProd (k : Nat) (s : State) : VG.Proof.Gcm.Clmul.Prod :=
  if k=4 then prod s else accProd s

theorem packedSave_ok (j : Nat) (hj : j < 4) (s : State) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.packedSave j)) s fun t =>
      savedProd (j+1) t = (if j=0 then prod s else addProd (accProd s) (prod s)) ∧
      VOnly [Y,.v16,.v17,LO,MID,HI] s t := by
  by_cases h0 : j=0
  · subst j
    apply WP.of_runBlock
    simp only [Impl.Gcm.PPC64LE.Vpmsum.packedSave, Impl.Gcm.PPC64LE.Vpmsum.packedAccs,
      ↓reduceIte, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
      exec_or, vpr_writeV, reduceCtorEq, BitVec.or_self,
      Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
      by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
      by simp only [lr_writeV]⟩⟩
    · simp only [savedProd, show 0+1≠4 by decide, ite_false, accProd, prod,
        vpr_writeV, reduceCtorEq, ite_true, ite_false]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2.1, ite_false]
  · by_cases h3 : j=3
    · subst j
      apply WP.of_runBlock
      simp only [Impl.Gcm.PPC64LE.Vpmsum.packedSave, Impl.Gcm.PPC64LE.Vpmsum.packedAccs,
        ↓reduceIte, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
        exec_xor, vpr_writeV, reduceCtorEq,
        Option.some.injEq, exists_eq_left']
      refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
        by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
        by simp only [lr_writeV]⟩⟩
      · simp only [savedProd, show 3+1=4 from rfl, ite_true, prod, accProd, addProd,
          vpr_writeV, reduceCtorEq, ite_true, ite_false]
        congr 1 <;> exact BitVec.xor_comm _ _
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [vpr_writeV, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    · apply WP.of_runBlock
      simp only [Impl.Gcm.PPC64LE.Vpmsum.packedSave, Impl.Gcm.PPC64LE.Vpmsum.packedAccs,
        h0, h3, ite_false, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
        exec_xor, vpr_writeV, reduceCtorEq,
        Option.some.injEq, exists_eq_left']
      refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
        by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
        by simp only [lr_writeV]⟩⟩
      · simp only [savedProd, show j+1≠4 by omega, ite_false, accProd, prod, addProd,
          vpr_writeV, reduceCtorEq, ite_true, ite_false]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp only [vpr_writeV, hr.1, hr.2.1, hr.2.2.1, ite_false]


theorem advanceVector {rs : List VReg} {s t : State} (h : VOnly rs s t) (n : BitVec 64) :
    VOnly rs (s.write .r5 (s.gpr .r5+n)) (t.write .r5 (t.gpr .r5+n)) := by
  refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [vpr_write] using h.v r hr
  · funext r
    simp only [RegUpd.gpr_write, h.gpr]
  · rw [RegUpd.mem_write, RegUpd.mem_write, h.mem]
  · rw [RegUpd.rd_write, RegUpd.rd_write, h.rd]
  · rw [RegUpd.wr_write, RegUpd.wr_write, h.wr]
  · rw [RegUpd.sp_write, RegUpd.sp_write, h.sp]
  · rw [RegUpd.lr_write, RegUpd.lr_write, h.lr]

theorem advance16 (s : State) :
    WP isa (.block [.addi .r5 .r5 16]) s (· = s.write .r5 (s.gpr .r5+16)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_addi' (d := .r5) (n := .r5) (imm := 16) (by decide), Option.some.injEq, exists_eq_left']
  rfl

theorem advance_twice (s : State) :
    (s.write .r5 (s.gpr .r5+16)).write .r5 ((s.write .r5 (s.gpr .r5+16)).gpr .r5+16) =
      s.write .r5 (s.gpr .r5+32) := by
  rw [RegUpd.gpr_write_self, write_overwrite, BitVec.add_assoc]
  rfl

theorem xorFirst_ok (j : Nat) (s : State) :
    WP isa (.block (if j=0 then [.vop (.logic .xor A A Y)] else [])) s fun t =>
      t.vpr A = (if j=0 then s.vpr A ^^^ s.vpr Y else s.vpr A) ∧ VOnly [A] s t := by
  by_cases hj : j=0
  · rw [ite_eq_left hj, ite_eq_left hj]
    exact vector_step _ A _ s (exec_xor A A Y s)
  · rw [ite_eq_right hj, ite_eq_right hj]
    apply WP.of_runBlock
    simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
    exact ⟨True.intro, VOnly.refl _ _⟩

def loadedAt (s : State) (offset : Nat) : BitVec 128 :=
  ext8 (Spec.Gcm.blockAt s.mem (s.gpr .r5 + BitVec.ofNat 64 offset))
    (Spec.Gcm.blockAt s.mem (s.gpr .r5 + BitVec.ofNat 64 offset))

theorem packedRead_ok (j : Nat) (s : State) (h0 : s.gpr .r0 = 0)
    (hm : s.vpr MASK = Impl.Gcm.PPC64LE.Vpmsum.reverseMask)
    (hr0 : InRegions (s.rd ++ s.wr) (s.gpr .r5) 16)
    (hr1 : InRegions (s.rd ++ s.wr) (s.gpr .r5+16) 16) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.packedRead j)) s fun t =>
      t.vpr A = (if j=0 then loadedAt s 0 ^^^ s.vpr Y else loadedAt s 0) ∧
      t.vpr HI = loadedAt s 16 ∧ VOnly [A,HI] (s.write .r5 (s.gpr .r5+32)) t := by
  unfold Impl.Gcm.PPC64LE.Vpmsum.packedRead
  repeat rw [WP.block_append_iff]
  refine WP.mono (loadRev_ok A .r5 s (by decide) h0 hm (by decide) hr0) fun u ⟨ha,hu⟩ => ?_
  refine WP.mono (advance16 u) fun v hv => ?_
  subst v
  have hu' := advanceVector hu 16
  refine WP.mono (xorFirst_ok j _) fun v ⟨hx,hv⟩ => ?_
  have hf := hu'.trans hv
  have hv0 : v.gpr .r0 = 0 := by
    rw [hf.gpr, RegUpd.gpr_write, ite_eq_right (by decide)]
    exact h0
  have hvm : v.vpr MASK = Impl.Gcm.PPC64LE.Vpmsum.reverseMask :=
    (hf.v MASK (by decide)).trans (by simpa only [vpr_write] using hm)
  have hrv : InRegions (v.rd ++ v.wr) (v.gpr .r5) 16 := by
    rw [hf.rd, hf.wr, hf.gpr, RegUpd.rd_write, RegUpd.wr_write, RegUpd.gpr_write_self]
    exact hr1
  refine WP.mono (loadRev_ok HI .r5 v (by decide) hv0 hvm (by decide) hrv) fun w ⟨hb,hw⟩ => ?_
  refine WP.mono (advance16 w) fun t ht => ?_
  subst t
  have hout := advanceVector (hf.trans hw) 16
  rw [advance_twice] at hout
  refine ⟨?_, ?_, hout.weaken (by simp)⟩
  · rw [vpr_write, hw.v A (by decide), hx, vpr_write,
      hu.v Y (by decide), ha]
    simp only [loadedAt, BitVec.add_zero]
  · rw [vpr_write, hb, hf.mem, hf.gpr, RegUpd.mem_write, RegUpd.gpr_write_self]
    rfl


def bulkWritten : List VReg := [Y,U,LO,MID,HI,A,T,.v16,.v17]

theorem accProd_kept {rs : List VReg} {s t : State} (hf : VOnly rs s t)
    (hy : Y ∉ rs) (h16 : .v16 ∉ rs) (h17 : .v17 ∉ rs) : accProd t = accProd s := by
  unfold accProd
  rw [hf.v Y hy, hf.v .v16 h16, hf.v .v17 h17]

theorem packedPair_ok (j : Nat) (hj : j < 4) (h : BitVec 128) (s : State)
    (h0 : s.gpr .r0 = 0) (hm : s.vpr MASK = Impl.Gcm.PPC64LE.Vpmsum.reverseMask)
    (hk : PackedKeys h 4 s)
    (hr0 : InRegions (s.rd ++ s.wr) (s.gpr .r5) 16)
    (hr1 : InRegions (s.rd ++ s.wr) (s.gpr .r5+16) 16) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.packedPair j)) s fun t =>
      savedProd (j+1) t =
        (if j=0 then
          pairedProd (loadedAt s 0 ^^^ s.vpr Y) (loadedAt s 16)
            (keyValue h (7-2*j)) (keyValue h (6-2*j))
        else addProd (accProd s) (pairedProd (loadedAt s 0) (loadedAt s 16)
            (keyValue h (7-2*j)) (keyValue h (6-2*j)))) ∧
      VOnly bulkWritten (s.write .r5 (s.gpr .r5+32)) t := by
  unfold Impl.Gcm.PPC64LE.Vpmsum.packedPair
  repeat rw [WP.block_append_iff]
  refine WP.mono (packedRead_ok j s h0 hm hr0 hr1) fun u ⟨ha,hb,hu⟩ => ?_
  have f := pair_key_free ⟨j,hj⟩
  have hul : u.vpr (keyLow j) = lowPair (keyValue h (7-2*j)) (keyValue h (6-2*j)) := by
    rw [hu.v (keyLow j) (by simp [f.2.2.1, f.1.2.2.2.1]), vpr_write]
    exact (hk j hj).1
  have huh : u.vpr (keyHigh j) = highPair (keyValue h (7-2*j)) (keyValue h (6-2*j)) := by
    rw [hu.v (keyHigh j) (by simp [f.2.2.2.1, f.2.1.2.2.2.1]), vpr_write]
    exact (hk j hj).2
  refine WP.mono (packedProducts_ok (keyLow j) (keyHigh j) _ _ u f.1 f.2.1 hul huh) fun v ⟨hp,hv⟩ => ?_
  refine WP.mono (packedSave_ok j hj v) fun t ⟨ht,hs⟩ => ?_
  have haccv : accProd v = accProd s := by
    rw [accProd_kept hv (by decide) (by decide) (by decide),
      accProd_kept hu (by decide) (by decide) (by decide)]
    simp only [accProd, vpr_write]
  refine ⟨?_, (hu.trans (hv.trans hs)).weaken (by simp [bulkWritten, or_left_comm, or_comm])⟩
  rw [ht, hp, ha, hb, haccv]
  by_cases he : j=0 <;> simp only [he, ↓reduceIte]


theorem advance_at (s : State) (a b : BitVec 64) :
    (s.write .r5 (s.gpr .r5+a)).write .r5 ((s.write .r5 (s.gpr .r5+a)).gpr .r5+b) =
      s.write .r5 (s.gpr .r5+(a+b)) := by
  rw [RegUpd.gpr_write_self, write_overwrite, BitVec.add_assoc]

theorem loadedAt_frame {rs : List VReg} {s t : State} (j : Nat)
    (hf : VOnly rs (s.write .r5 (s.gpr .r5+BitVec.ofNat 64 (32*j))) t) (k : Nat) :
    loadedAt t (16*k) = loadedAt s (16*(2*j+k)) := by
  unfold loadedAt
  rw [hf.mem, hf.gpr, RegUpd.mem_write, RegUpd.gpr_write_self, Offset.add_add,
    show 32*j+16*k=16*(2*j+k) by omega]

theorem packedKeys_frame {s t : State} (h : BitVec 128) (ptr : BitVec 64)
    (hk : PackedKeys h 4 s) (hf : VOnly bulkWritten (s.write .r5 ptr) t) : PackedKeys h 4 t := by
  intro j hj
  have f : keyLow j ∉ bulkWritten ∧ keyHigh j ∉ bulkWritten := by
    have f : ∀ j : Fin 4, keyLow j ∉ bulkWritten ∧ keyHigh j ∉ bulkWritten := by decide
    exact f ⟨j,hj⟩
  rw [hf.v (keyLow j) f.1, hf.v (keyHigh j) f.2, vpr_write]
  exact hk j hj

structure PairInv (h : BitVec 128) (base : State) (j : Nat) (s : State) : Prop where
  effects : VOnly bulkWritten (base.write .r5 (base.gpr .r5+BitVec.ofNat 64 (32*j))) s
  first : j=0 → s.vpr Y = base.vpr Y
  sum : 0 < j → (savedProd j s).val = pairSum h (base.vpr Y) (fun i => loadedAt base (16*i)) j

theorem pair_loop_step (h : BitVec 128) (base : State) (j : Nat) (hj : j < 4)
    (h0 : base.gpr .r0 = 0) (hm : base.vpr MASK = Impl.Gcm.PPC64LE.Vpmsum.reverseMask)
    (hk : PackedKeys h 4 base)
    (hr : ∀ k < 8, InRegions (base.rd ++ base.wr) (base.gpr .r5+BitVec.ofNat 64 (16*k)) 16)
    (s : State) (hs : PairInv h base j s) :
    WP isa (.block (Impl.Gcm.PPC64LE.Vpmsum.packedPair j)) s (PairInv h base (j+1)) := by
  have hs0 : s.gpr .r0 = 0 := by
    rw [hs.effects.gpr, RegUpd.gpr_write, ite_eq_right (by decide)]
    exact h0
  have hsm : s.vpr MASK = Impl.Gcm.PPC64LE.Vpmsum.reverseMask := by
    rw [hs.effects.v MASK (by decide), vpr_write]
    exact hm
  have hsr0 : InRegions (s.rd ++ s.wr) (s.gpr .r5) 16 := by
    rw [hs.effects.rd, hs.effects.wr, hs.effects.gpr,
      RegUpd.rd_write, RegUpd.wr_write, RegUpd.gpr_write_self, show 32*j=16*(2*j) by omega]
    exact hr (2*j) (by omega)
  have hsr1 : InRegions (s.rd ++ s.wr) (s.gpr .r5+16) 16 := by
    rw [hs.effects.rd, hs.effects.wr, hs.effects.gpr,
      RegUpd.rd_write, RegUpd.wr_write, RegUpd.gpr_write_self]
    change InRegions (base.rd ++ base.wr) (base.gpr .r5+BitVec.ofNat 64 (32*j)+BitVec.ofNat 64 16) 16
    rw [Offset.add_add, show 32*j+16=16*(2*j+1) by omega]
    exact hr (2*j+1) (by omega)
  refine WP.mono (packedPair_ok j hj h s hs0 hsm (packedKeys_frame h _ hk hs.effects) hsr0 hsr1)
    fun t ⟨ht,hf⟩ => ?_
  have he := (advanceVector hs.effects 32).trans hf
  rw [advance_at] at he
  have hoff : BitVec.ofNat 64 (32*j)+32=BitVec.ofNat 64 (32*(j+1)) := by
    change BitVec.ofNat 64 (32*j)+BitVec.ofNat 64 32 = _
    rw [← BitVec.ofNat_add, show 32*j+32=32*(j+1) by omega]
  rw [hoff] at he
  refine ⟨he.weaken (by simp), fun he => by omega, ?_⟩
  intro _
  rw [ht]
  have ha : loadedAt s 0 = loadedAt base (16*(2*j)) := by
    simpa only [Nat.mul_zero, Nat.add_zero] using loadedAt_frame j hs.effects 0
  have hb : loadedAt s 16 = loadedAt base (16*(2*j+1)) := by
    exact loadedAt_frame j hs.effects 1
  rw [ha,hb,pairSum_succ]
  by_cases hj0 : j=0
  · rw [ite_eq_left hj0, hs.first hj0]
    rw [pairedProd_val]
    subst j
    simp only [pairSum_zero, zero_add, pairTerm, ite_true]
  · rw [ite_eq_right hj0, addProd_val, pairedProd_val]
    have hprev : (accProd s).val = pairSum h (base.vpr Y) (fun i => loadedAt base (16*i)) j := by
      have he := hs.sum (by omega)
      simpa only [savedProd, show j≠4 by omega, ite_false] using he
    rw [hprev]
    simp only [pairTerm, hj0, ite_false]


theorem vector_self_pointer (rs : List VReg) (s : State) :
    VOnly rs (s.write .r5 (s.gpr .r5)) s := by
  refine ⟨fun r _ => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vpr_write]
  · funext r
    simp only [RegUpd.gpr_write]
    split <;> rename_i he
    · subst r
      rfl
    · rfl
  · rw [RegUpd.mem_write]
  · rw [RegUpd.rd_write]
  · rw [RegUpd.wr_write]
  · rw [RegUpd.sp_write]
  · rw [RegUpd.lr_write]

theorem writeVector {rs : List VReg} {s t : State} (h : VOnly rs s t) (d : Reg) (v : BitVec 64) :
    VOnly rs (s.write d v) (t.write d v) := by
  refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [vpr_write] using h.v r hr
  · funext r
    simp only [RegUpd.gpr_write, h.gpr]
  · rw [RegUpd.mem_write, RegUpd.mem_write, h.mem]
  · rw [RegUpd.rd_write, RegUpd.rd_write, h.rd]
  · rw [RegUpd.wr_write, RegUpd.wr_write, h.wr]
  · rw [RegUpd.sp_write, RegUpd.sp_write, h.sp]
  · rw [RegUpd.lr_write, RegUpd.lr_write, h.lr]

theorem packedBody_ok (h : BitVec 128) (s : State) (hc : Config s) (hk : PackedKeys h 4 s)
    (hr : ∀ k < 8, InRegions (s.rd ++ s.wr) (s.gpr .r5+BitVec.ofNat 64 (16*k)) 16) :
    WP isa (.block Impl.Gcm.PPC64LE.Vpmsum.packedBody) s fun t =>
      ρ (t.vpr Y) = hashField (x * φ h) (ρ (s.vpr Y)) (fun j => ρ (loadedAt s (16*j))) 8 ∧
      VOnly bulkWritten ((s.write .r5 (s.gpr .r5+128)).write .r6 (s.gpr .r6-8)) t := by
  have hpairs : WP isa (.block ((List.range 4).flatMap Impl.Gcm.PPC64LE.Vpmsum.packedPair)) s
      (PairInv h s 4) := by
    refine wp_range_flatMap (M := isa) (PairInv h s)
      (fun j t hj ht => pair_loop_step h s j hj hc.zero hc.mask hk hr t ht) 4 (Nat.le_refl _) s ?_
    refine ⟨?_, fun _ => rfl, fun hj => by omega⟩
    simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using vector_self_pointer bulkWritten s
  unfold Impl.Gcm.PPC64LE.Vpmsum.packedBody
  repeat rw [WP.block_append_iff]
  refine WP.mono hpairs fun u hu => ?_
  have hcu : u.vpr C = Impl.Gcm.Clmul.poly ++ Impl.Gcm.Clmul.poly := by
    rw [hu.effects.v C (by decide), vpr_write]
    exact hc.c
  have hzu : u.vpr Z = 0 := by
    rw [hu.effects.v Z (by decide), vpr_write]
    exact hc.z
  refine WP.mono (reduce_ok Y u hcu hzu) fun v ⟨hy,hv⟩ => ?_
  have hclass : ρ (v.vpr Y) =
      hashField (x * φ h) (ρ (s.vpr Y)) (fun j => ρ (loadedAt s (16*j))) 8 := by
    rw [hy, ρ_reduce]
    have he := hu.sum (by decide)
    rw [savedProd, ite_eq_left (by decide), pairSum_hash] at he
    exact he
  have hf : VOnly bulkWritten (s.write .r5 (s.gpr .r5+BitVec.ofNat 64 (32*4))) v :=
    (hu.effects.trans hv).weaken (by simp [bulkWritten])
  have hptr : BitVec.ofNat 64 (32*4) = 128 := by decide
  rw [hptr] at hf
  have h6 : v.gpr .r6 = s.gpr .r6 := by
    rw [hf.gpr, RegUpd.gpr_write, ite_eq_right (by decide)]
  have hlast : WP isa (.block [.subi .r6 .r6 8]) v (· = v.write .r6 (s.gpr .r6-8)) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil,
      exec_subi' (d := .r6) (n := .r6) (imm := 8) (by decide), h6,
      Option.some.injEq, exists_eq_left']
    rfl
  refine WP.mono hlast fun t ht => ?_
  subst t
  exact ⟨by simpa only [vpr_write] using hclass, writeVector hf .r6 (s.gpr .r6-8)⟩


theorem hashField_ghash (h y : BitVec 128) (m : Mem) (p : Addr) (i n : Nat) :
    φ (Spec.Gcm.ghashFrom h y (Spec.Gcm.blocksAt m p (i+n))) =
      hashField (φ h) (φ (Spec.Gcm.ghashFrom h y (Spec.Gcm.blocksAt m p i)))
        (fun j => φ (Spec.Gcm.blockAt m (p+BitVec.ofNat 64 (16*(i+j))))) n := by
  induction n with
  | zero => simp only [Nat.add_zero, hashField]
  | succ n ih =>
    rw [Nat.add_succ, Proof.Gcm.ghashFrom_blocksAt_succ, φ_mul, φ_xor, ih, hashField]


theorem recoverKey_ok (h : BitVec 128) (s : State) (hk : PackedKeys h 4 s) :
    WP isa (.block [.vop (.sldoi A (keyLow 3) (keyLow 3) 8), .vop (.sldoi H (keyHigh 3) A 8)]) s fun t =>
      t.vpr H = h ∧ VOnly [A,H] s t := by
  have hp := hk 3 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_shift8,
    vpr_writeV, show keyHigh 3 ≠ A by decide, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · simp only [ite_true, hp.1, hp.2, half, lowPair, highPair,
      vdword_append_0, vdword_append_1, show 6-2*3=0 by decide, keyValue]
    exact (vdwords h).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2, ite_false]

end VG.Proof.Gcm.PPC64LE.Vpmsum
