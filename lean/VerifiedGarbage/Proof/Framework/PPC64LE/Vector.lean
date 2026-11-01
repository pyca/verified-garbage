module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Impl.Vector.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
public meta import VerifiedGarbage.Proof.Framework.UnfoldStep

/-! # PPC64LE vector execution and constant-time analysis

Vector contents are secret. Only GPRs and the stack pointer can contribute
to addresses or branch conditions. Vector loads/stores require public
address operands; extracting a doubleword produces a secret GPR value.
-/

@[expose] public section
namespace VG.PPC64LE

theorem choice_select {n : Nat} (e f g : BitVec n) :
    (g &&& ~~~e) ||| (f &&& e) = ((f ^^^ g) &&& e) ^^^ g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
    hi, decide_true, Bool.true_and]
  cases he : e.getLsbD i <;> cases hf : f.getLsbD i <;> cases hg : g.getLsbD i <;> rfl

theorem majority_xor_select {n : Nat} (a b c : BitVec n) :
    ((c ^^^ b) &&& (a ^^^ b)) ^^^ b = ((a ||| b) &&& c) ||| (a &&& b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases ha : a.getLsbD i <;> cases hb : b.getLsbD i <;> cases hc : c.getLsbD i <;> rfl

theorem vpr_writeV (s : State) (d : VReg) (x : BitVec 128) (r : VReg) :
    (s.writeV d x).vpr r = if r = d then x else s.vpr r := rfl

theorem gpr_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).gpr = s.gpr := rfl
theorem mem_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).mem = s.mem := rfl
theorem rd_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).rd = s.rd := rfl
theorem wr_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).wr = s.wr := rfl
theorem sp_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).sp = s.sp := rfl
theorem lr_writeV (s : State) (d : VReg) (x : BitVec 128) : (s.writeV d x).lr = s.lr := rfl


theorem vpr_write (s : State) (d : Reg) (x : BitVec 64) :
    (s.write d x).vpr = s.vpr := rfl

theorem write_overwrite (s : State) (d : Reg) (x y : BitVec 64) :
    (s.write d x).write d y = s.write d y := by
  simp only [State.write]
  congr 1
  funext r
  split <;> rfl

/-- A vector-only computation preserves the scalar state and memory. -/
structure VOnly (rs : List VReg) (s s' : State) : Prop where
  v : ∀ r, r ∉ rs → s'.vpr r = s.vpr r
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr

theorem VOnly.refl (rs : List VReg) (s : State) : VOnly rs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem VOnly.trans {rs ts : List VReg} {s u v : State}
    (h : VOnly rs s u) (h' : VOnly ts u v) : VOnly (rs ++ ts) s v :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    exact (h'.v r hr.2).trans (h.v r hr.1),
   h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd,
   h'.wr.trans h.wr, h'.sp.trans h.sp, h'.lr.trans h.lr⟩

theorem VOnly.weaken {rs ts : List VReg} {s u : State} (h : VOnly rs s u)
    (hs : ∀ r ∈ rs, r ∈ ts) : VOnly ts s u :=
  ⟨fun r hr => h.v r (fun h' => hr (hs r h')), h.gpr, h.mem, h.rd, h.wr, h.sp, h.lr⟩

theorem sldoi8_eq (n m : BitVec 128) :
    ((n ++ m) <<< 64).extractLsb' 128 128 = n.extractLsb' 0 64 ++ m.extractLsb' 64 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append,
    hi, decide_true, Bool.true_and]
  simp only [show 128 + i < 128 + 128 by omega, show ¬ 128 + i < 64 by omega,
    decide_true, decide_false, Bool.not_false, Bool.true_and]
  by_cases h : i < 64
  · simp only [h, show 128 + i - 64 < 128 by omega, decide_true, ite_true, Bool.true_and]
    exact congrArg m.getLsbD (by omega)
  · simp only [h, show ¬ 128 + i - 64 < 128 by omega, show i - 64 < 64 by omega,
      decide_true, ite_false, Bool.true_and, Nat.zero_add]
    exact congrArg n.getLsbD (by omega)

theorem vector_step (i : Instr) (d : VReg) (v : BitVec 128) (s : State)
    (he : exec i s = some (s.writeV d v)) :
    WP isa (.block [i]) s fun t => t.vpr d = v ∧ VOnly [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, he, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨by simp only [vpr_writeV, ite_true], ⟨fun r hr => ?_, gpr_writeV ..,
    mem_writeV .., rd_writeV .., wr_writeV .., sp_writeV .., lr_writeV ..⟩⟩
  simp only [vpr_writeV, show r ≠ d by simpa only [List.mem_singleton] using hr, ite_false]

theorem exec_sldoi8 (d n m : VReg) (s : State) :
    exec (.vop (.sldoi d n m 8)) s = some (s.writeV d
      ((s.vpr n).extractLsb' 0 64 ++ (s.vpr m).extractLsb' 64 64)) := by
  change some (s.writeV d (((s.vpr n ++ s.vpr m) <<< 64).extractLsb' 128 128)) = _
  rw [sldoi8_eq]

theorem const64_ok (d : Reg) (x : BitVec 64) (s : State) :
    WP isa (.block (Impl.Vector.PPC64LE.const64 d x)) s (· = s.write d x) := by
  apply WP.of_runBlock
  simp only [Impl.Vector.PPC64LE.const64, runBlock_cons, runStep_some,
    runBlock_nil, reduceExec, show 32 < 64 by decide, ite_true,
    RegUpd.gpr_write_self, write_overwrite, movImm64_eq, Option.some.injEq, exists_eq_left']

theorem pair_ok (d tmp zero : VReg) (hi lo : Reg) (s : State)
    (hd : d ≠ tmp) (hdz : d ≠ zero) (htz : tmp ≠ zero) (hz : s.vpr zero = 0) :
    WP isa (.block (Impl.Vector.PPC64LE.pair d tmp zero hi lo)) s fun s' =>
      s'.vpr d = s.gpr hi ++ s.gpr lo ∧ VOnly [d, tmp] s s' := by
  apply WP.of_runBlock
  simp only [Impl.Vector.PPC64LE.pair, runBlock_cons, runStep_some, runBlock_nil,
    exec_sldoi8, reduceExec, vpr_writeV, gpr_writeV, Option.some.injEq, exists_eq_left',
    hd, Ne.symm hd, Ne.symm hdz, Ne.symm htz, ite_true, ite_false]
  refine ⟨?_, ⟨fun r hr => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · simp only [hz, BitVec.ofNat_eq_ofNat, BitVec.extractLsb'_zero,
      BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [vpr_writeV, hr.1, hr.2, ite_false]

theorem ofVBytes_congr (f g : Nat → BitVec 8) (h : ∀ i < 16, f i = g i) :
    ofVBytes f = ofVBytes g := by
  have e : (List.range 16).map (fun i => (f i).setWidth 128 <<< (8 * (15 - i))) =
      (List.range 16).map (fun i => (g i).setWidth 128 <<< (8 * (15 - i))) := by
    apply List.map_congr_left
    intro i hi
    rw [h i (List.mem_range.mp hi)]
  simpa only [ofVBytes, List.foldl_map] using
    congrArg (fun xs : List (BitVec 128) => xs.foldl (fun a b => a ||| b) 0) e

theorem byteTerm_bit (f : Nat → BitVec 8) {k j r : Nat}
    (hk : k < 16) (hj : j < 16) (hr : r < 8) :
    ((f k).setWidth 128 <<< (8 * (15-k))).getLsbD (8*j+r) =
      if j = 15-k then (f k).getLsbD r else false := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j = 15-k
  · subst j
    simp only [show ¬8*(15-k)+r < 8*(15-k) by omega, decide_false,
      Bool.not_false, Nat.add_sub_cancel_left, show 8*(15-k)+r < 128 by omega,
      show r < 128 by omega, decide_true, Bool.true_and, ite_true]
  · have h' : 8*j+r < 8*(15-k) ∨ 8 ≤ 8*j+r-8*(15-k) := by omega
    rcases h' with h' | h' <;> simp [h, h']

theorem packed_bit (f : Nat → BitVec 8) {j r : Nat} (hj : j < 16) (hr : r < 8) :
    ∀ k, k ≤ 16 →
    ((List.range k).foldl (fun x i => x ||| ((f i).setWidth 128 <<< (8*(15-i)))) (0#128)).getLsbD (8*j+r) =
      if 15-j < k then (f (15-j)).getLsbD r else false
  | 0, _ => by simp
  | k+1, hk => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      BitVec.getLsbD_or, packed_bit f hj hr k (by omega), byteTerm_bit f (by omega) hj hr]
    by_cases h : 15-j < k
    · simp [h, show 15-j < k+1 by omega, show j ≠ 15-k by omega]
    · by_cases e : j = 15-k
      · rw [ite_eq_right h, ite_eq_left e, ite_eq_left (show 15-j < k+1 by omega), Bool.false_or]
        exact congrArg (fun i => (f i).getLsbD r) (by omega)
      · simp [h, e, show ¬15-j < k+1 by omega]

theorem getLsbD_packed (f : Nat → BitVec 8) {j r : Nat} (hj : j < 16) (hr : r < 8) :
    (VG.PPC64LE.ofVBytes f).getLsbD (8*j+r) = (f (15-j)).getLsbD r := by
  simpa only [VG.PPC64LE.ofVBytes, BitVec.ofNat_eq_ofNat, show 15-j < 16 by omega, ite_true] using
    packed_bit f hj hr 16 (by decide)


theorem getLsbD_rev128 (x : BitVec 128) {i : Nat} (hi : i < 128) :
    (rev128 x).getLsbD i = x.getLsbD (8*(15-i/8)+i%8) := by
  have he : i = 8*(i/8)+i%8 := by omega
  calc
    _ = (rev128 x).getLsbD (8*(i/8)+i%8) := congrArg (rev128 x).getLsbD he
    _ = _ := by
      rw [rev128, getLsbD_packed _ (by omega) (by omega)]
      simp only [vbyte, BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega,
        decide_true, Bool.true_and]
      exact congrArg x.getLsbD (by omega)

theorem rev128_rev128 (x : BitVec 128) : rev128 (rev128 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rev128 _ hi, getLsbD_rev128 _ (by omega)]
  exact congrArg x.getLsbD (by omega)

theorem swapDwords_append (a b : BitVec 64) : swapDwords (a ++ b) = b ++ a := by
  simp only [swapDwords, vdword, Nat.reduceSub, Nat.mul_zero, Nat.mul_one,
    BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]

theorem swapDwords_involutive (x : BitVec 128) : swapDwords (swapDwords x) = x := by
  change swapDwords (x.extractLsb' 0 64 ++ x.extractLsb' 64 64) = x
  rw [swapDwords_append]
  exact BitVec.extractLsb'_append_extractLsb'

theorem getLsbD_swapDwords (x : BitVec 128) {i : Nat} (hi : i < 128) :
    (swapDwords x).getLsbD i = x.getLsbD (if i < 64 then 64+i else i-64) := by
  simp only [swapDwords, vdword, Nat.reduceSub, Nat.mul_zero, Nat.mul_one,
    BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', Nat.zero_add]
  by_cases h : i < 64
  · simp only [h, ite_true, decide_true, Bool.true_and]
  · simp only [h, ite_false, show i-64 < 64 by omega, decide_true, Bool.true_and]

theorem rev128_swapDwords (x : BitVec 128) : rev128 (swapDwords x) = swapDwords (rev128 x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rev128 _ hi, getLsbD_swapDwords _ (by omega), getLsbD_swapDwords _ hi,
    getLsbD_rev128 _ (by split <;> omega)]
  exact congrArg x.getLsbD (by split <;> split <;> omega)

theorem rev128_xor (a b : BitVec 128) : rev128 (a ^^^ b) = rev128 a ^^^ rev128 b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_rev128 _ hi, BitVec.getLsbD_xor, BitVec.getLsbD_xor,
    getLsbD_rev128 _ hi, getLsbD_rev128 _ hi]

theorem vbyte_packed (f : Nat → BitVec 8) {i : Nat} (hi : i < 16) :
    vbyte (ofVBytes f) i = f i := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and]
  rw [getLsbD_packed f (by omega) hr, show 15-(15-i) = i by omega]

theorem ext_vbyte {a b : BitVec 128} (h : ∀ i < 16, vbyte a i = vbyte b i) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have he := congrArg (BitVec.getLsbD · (j % 8)) (h (15-j/8) (by omega))
  simp only [vbyte, BitVec.getLsbD_extractLsb', show j % 8 < 8 by omega,
    decide_true, Bool.true_and] at he
  exact (congrArg a.getLsbD (by omega)).symm.trans (he.trans (congrArg b.getLsbD (by omega)))

theorem vbyte_rev128 (x : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (rev128 x) i = vbyte x (15-i) := by
  rw [rev128, vbyte_packed _ hi]

theorem vbyte_swapDwords (x : BitVec 128) {i : Nat} (hi : i < 16) :
    vbyte (swapDwords x) i = vbyte x (if i < 8 then i+8 else i-8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and]
  rw [getLsbD_swapDwords _ (by omega)]
  exact congrArg x.getLsbD (by split <;> split <;> omega)

def permSelf (x control : BitVec 128) : BitVec 128 :=
  ofVBytes fun i =>
    let j := (vbyte control i).toNat % 32
    if j < 16 then vbyte x j else vbyte x (j-16)

theorem exec_permSelf (d n c : VReg) (s : State) :
    exec (.vop (.perm d n n c)) s = some (s.writeV d (permSelf (s.vpr n) (s.vpr c))) := rfl

theorem exec_lxvd2x (d : VReg) (a b : Reg) (s : State) (ha : a ≠ .r0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr a + s.gpr b) 16) :
    exec (.lxvd2x d a b) s = some (s.writeV d (swapDwords (s.mem.read (s.gpr a + s.gpr b) 16))) := by
  simp only [reduceExec, addrX, ha, ne_eq, not_false_eq_true, ite_true,
    Option.bind_some, State.load, hr, Option.map_some]



theorem exec_stxvd2x (n : VReg) (a b : Reg) (s : State) (ha : a ≠ .r0)
    (hr : InRegions s.wr (s.gpr a + s.gpr b) 16) :
    exec (.stxvd2x n a b) s = some {s with
      mem := s.mem.write (s.gpr a + s.gpr b) 16 (swapDwords (s.vpr n))} := by
  simp only [reduceExec, addrX, ha, ne_eq, not_false_eq_true, ite_true,
    Option.bind_some, State.store, hr]

theorem loadPerm_ok (d : VReg) (p : Reg) (c : VReg) (control : BitVec 128) (s : State)
    (hp : p ≠ .r0) (hd : d ≠ c) (h0 : s.gpr .r0 = 0) (hc : s.vpr c = control)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr p) 16) :
    WP isa (.block (Impl.Vector.PPC64LE.loadPerm d p c)) s fun t =>
      t.vpr d = permSelf (swapDwords (s.mem.read (s.gpr p) 16)) control ∧ VOnly [d] s t := by
  have hr' : InRegions (s.rd ++ s.wr) (s.gpr p + s.gpr .r0) 16 := by
    simpa only [h0, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hr
  apply WP.of_runBlock
  simp only [Impl.Vector.PPC64LE.loadPerm, runBlock_cons, runStep_some, runBlock_nil,
    exec_lxvd2x d p .r0 s hp hr', exec_permSelf, vpr_writeV, Ne.symm hd, ite_false, ite_true,
    hc, h0, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hn => ?_, by simp only [gpr_writeV], by simp only [mem_writeV],
    by simp only [rd_writeV], by simp only [wr_writeV], by simp only [sp_writeV],
    by simp only [lr_writeV]⟩⟩
  · trivial
  · simp only [List.mem_singleton] at hn
    simp only [vpr_writeV, hn, ite_false]

/-- Apply an independent vector operation to each distinct state register,
using a key register outside the list. -/
theorem vector_map (is : VReg → Instr) (f : BitVec 128 → BitVec 128 → BitVec 128) (k : VReg)
    (he : ∀ b s, exec (is b) s = some (s.writeV b (f (s.vpr b) (s.vpr k)))) :
    ∀ (rs : List VReg) (s : State), rs.Nodup → k ∉ rs →
      WP isa (.block (rs.map is)) s fun t =>
        (∀ b ∈ rs, t.vpr b = f (s.vpr b) (s.vpr k)) ∧ VOnly rs s t
  | [], s, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, VOnly.refl _ _⟩
  | b :: bs, s, hn, hk => by
    have hb : b ∉ bs := (List.nodup_cons.mp hn).1
    have hk' : k ∉ bs := fun h => hk (List.mem_cons_of_mem _ h)
    have hkb : k ≠ b := fun h => hk (h ▸ List.mem_cons_self ..)
    change WP isa (.block ([is b] ++ bs.map is)) s _
    rw [WP.block_append_iff]
    refine WP.mono (vector_step (is b) b _ s (he b s)) fun u ⟨hv, ho⟩ => ?_
    refine WP.mono (vector_map is f k he bs u (List.nodup_cons.mp hn).2 hk') fun t ⟨hv', ho'⟩ => ⟨?_, ho.trans ho'⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [ho'.v _ hb, hv]
    · have hcb : c ≠ b := fun h => hb (h ▸ hc)
      rw [hv' c hc, ho.v c (by simpa only [List.mem_singleton] using hcb),
        ho.v k (by simpa only [List.mem_singleton] using hkb)]


theorem extract_high_word_byte (v : BitVec 128) {q : Nat} (hq : q < 4) :
    ((v.extractLsb' 64 64).setWidth 32).extractLsb' (8*q) 8 = vbyte v (7-q) := by
  apply BitVec.eq_of_getLsbD_eq
  intro r hr
  simp only [vbyte, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    hr, show 8*q+r < 32 by omega, show 8*q+r < 64 by omega,
    decide_true, Bool.true_and]
  exact congrArg v.getLsbD (by omega)

namespace VectorTaint
open VG.PPC64LE.Taint (T pub set Agree)

def step (τ : T) : Instr → Option T
  | .vop _ | .mtvsrd .. => some τ
  | .lxvd2x _ a b | .stxvd2x _ a b => if pub τ a && pub τ b then some τ else none
  | .lxvd2xTbl _ _ b .. => if pub τ b then some τ else none
  -- A static's address may vary between runs; only the table index leaks.
  | .adrSym d _ => some (set τ d false)
  | .mfvsrd d _ => some (set τ d false)
  | i => Taint.step τ i

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State}
    (ha : Agree τ s₁ s₂) (hs : step τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | vop op =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨⟨_, _⟩, -, rfl⟩ := e₁
    obtain ⟨⟨_, _⟩, -, rfl⟩ := e₂
    exact ⟨rfl, ha⟩
  | mtvsrd d n =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha⟩
  | mfvsrd d n =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [reduceExec, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, ha.write d fun h => by cases h⟩
  | lxvd2x d a b =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hp; cases hs
    simp only [Bool.and_eq_true] at hp
    refine ⟨by simp only [addrs, ha.reg hp.1, ha.reg hp.2], ?_⟩
    simp only [reduceExec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨_, -, _, -, rfl⟩ := e₁
    obtain ⟨_, -, _, -, rfl⟩ := e₂
    exact ha
  | lxvd2xTbl d a b name ws =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hp; cases hs
    refine ⟨by simp only [addrs, ha.reg hp], ?_⟩
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    split at e₂ <;> [skip; cases e₂]
    cases e₁; cases e₂
    exact ha
  | adrSym d name =>
    simp only [step, Option.some.injEq] at hs; subst hs
    simp only [reduceExec] at e₁ e₂
    split at e₁ <;> [skip; cases e₁]
    rename_i hd
    rw [ite_eq_left_of_eq_true _ _ (eq_true hd)] at e₂
    cases e₁; cases e₂
    exact ⟨rfl, ha.write d fun h => by cases h⟩
  | stxvd2x n a b =>
    simp only [step] at hs
    split at hs <;> [skip; cases hs]
    rename_i hp; cases hs
    simp only [Bool.and_eq_true] at hp
    refine ⟨by simp only [addrs, ha.reg hp.1, ha.reg hp.2], ?_⟩
    simp only [reduceExec, Option.bind_eq_some_iff, State.store] at e₁ e₂
    obtain ⟨_, -, e₁⟩ := e₁; obtain ⟨_, -, e₂⟩ := e₂
    split at e₁ <;> [cases e₁; cases e₁]
    split at e₂ <;> [cases e₂; cases e₂]
    exact ha
  | _ => exact Taint.step_sound ha hs e₁ e₂

end VectorTaint

def vectorTaint : VG.Taint isa := { taint with
  step := VectorTaint.step
  step_sound := VectorTaint.step_sound }

end VG.PPC64LE

public meta section
namespace VG.PPC64LE

dsimproc reduceVOpEval (VOp.eval _ _) := fun e => do
  let some e' ← unfoldStep? e | return .continue
  return .visit e'

end VG.PPC64LE
