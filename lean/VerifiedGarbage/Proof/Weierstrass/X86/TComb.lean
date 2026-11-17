module

public import VerifiedGarbage.Proof.Weierstrass.X86.Ladder
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombLay
public import VerifiedGarbage.Proof.Weierstrass.X86.Rcb3
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.Proof.Weierstrass.Law3
public import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.X25519.X86.Column
public import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Framework.X86.SseDword
public import VerifiedGarbage.Proof.Weierstrass.Pow
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Mmx
public import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Mont.Words128
public import VerifiedGarbage.Proof.Mont.X86.Chain
public import VerifiedGarbage.Proof.Mont.X86.Csub
public import VerifiedGarbage.Proof.Mont.X86.RedRow
public import VerifiedGarbage.Proof.Mont.X86.Row
public import VerifiedGarbage.Proof.Mont.X86.Step
public import VerifiedGarbage.Proof.Rc2.Memory32
public import VerifiedGarbage.Proof.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.X86.Loop
public import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareArithmetic
public import VerifiedGarbage.Proof.Weierstrass.X86.MontSquareRed
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.X25519.X86.Arith
public import VerifiedGarbage.Proof.X25519.X86.Fold
public import VerifiedGarbage.Impl.Weierstrass.TCombWords
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.X86.TCombScan

/-! ### `Weierstrass.X86.TCombSelect`, which this module and modules that import it used -/

section

/-! # Constant-time table selection for the x86 comb -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont

/-- The words the selection stores: those of entry `a` of the table at `X`
if `1 ≤ a ≤ H`, else zero. -/
theorem accVal_word {mem mem' : Mem} {base X : Addr} {n a H o : Nat}
    (h : ∀ c < n, mem'.readW (off base (o + 16 * c)) 128 = accVal mem X n a H c) :
    ∀ i < 2 * n, word mem' base (o + 8 * i) =
      if 1 ≤ a ∧ a ≤ H then word mem X (16 * n * (a - 1) + 8 * i) else 0 := by
  intro i hi
  obtain ⟨c, q, hq, rfl⟩ : ∃ c q, q < 2 ∧ i = 2 * c + q := ⟨i / 2, i % 2, Nat.mod_lt _ (by decide), by omega_using []⟩
  have e := readW_extract mem' (off base (o + 16 * c)) (w := 128) (k := 8 * q) (n := 8) (by omega_using [hq])
  rw [show 8 * 8 = 64 from rfl, off, Offset.add_add, show o + 16 * c + 8 * q = o + 8 * (2 * c + q) by omega_using []] at e
  rw [Mont.word, off, ← e, h c (by omega_using [hi]), accVal]
  split
  · have e2 := readW_extract mem (X + BitVec.ofNat 64 (16 * n * (a - 1) + 16 * c)) (w := 128)
      (k := 8 * q) (n := 8) (by omega_using [hq])
    rw [show 8 * 8 = 64 from rfl, Offset.add_add] at e2
    rw [e2, Mont.word, off]
    rw [show 16 * n * (a - 1) + 16 * c + 8 * q = 16 * n * (a - 1) + 8 * (2 * c + q) by omega_using []]
  · simp

/-- Numbers with the same words. -/
theorem wordsVal_congr₂ {m m' : Mem} {b b' : Addr} : ∀ (o o' k : Nat),
    (∀ i < k, word m' b' (o' + 8 * i) = word m b (o + 8 * i)) → wordsVal m' b' o' k = wordsVal m b o k
  | _, _, 0, _ => rfl
  | o, o', k + 1, h => by
    have h0 := h 0 (by omega_using [])
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [wordsVal, wordsVal, h0, wordsVal_congr₂ (o + 8) (o' + 8) k fun i hi => by
      rw [show o + 8 + 8 * i = o + 8 * (i + 1) by omega_using [], show o' + 8 + 8 * i = o' + 8 * (i + 1) by omega_using []]
      exact h (i + 1) (by omega_using [hi])]

theorem Unch.split {base : Addr} {o k : Nat} {m m' : Mem} (h : Unch base [(o, 2 * k)] m m') :
    Unch base [(o, k), (o + k, k)] m m' := fun x hx => h x fun w hw => by
  simp only [List.mem_singleton] at hw; subst hw
  have h1 := hx _ (List.mem_cons_self ..)
  have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  dsimp only at h1 h2 ⊢; omega_using [h1, h2]

/-- What the selection leaves: in `E`, entry `a`'s `x` and `y` (of the table
at `X`) and `R` if `a ≥ 1`, else `(0, R, 0)`. -/
structure SelPost (K : TCombCfg) (base : Addr) (s : State) (a : Nat) (X : Addr) (t : State) : Prop where
  x : wordsVal t.mem base K.E.x K.M.n = if 1 ≤ a then wordsVal s.mem X (16 * K.M.n * (a - 1)) K.M.n else 0
  y : wordsVal t.mem base K.E.y K.M.n =
    if 1 ≤ a then wordsVal s.mem X (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n else K.one
  z : wordsVal t.mem base K.E.z K.M.n = if 1 ≤ a then K.one else 0
  keep : Keeps [.eax, .ecx, .edx] s t
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem

/-- Zero words. -/
theorem wordsVal_zeros {m : Mem} {b : Addr} {o k : Nat} (h : ∀ i < k, word m b (o + 8 * i) = 0) :
    wordsVal m b o k = 0 :=
  wordsVal_of_shifts m b o k 0 (Nat.two_pow_pos _) fun i hi => by rw [h i hi, Nat.zero_shiftRight]; rfl

/-- Load the retained public table pointer and add the window offset. -/
theorem selSetup_ok (K : TCombCfg) {s : State} {base : Addr} {size j : Nat} {T : BitVec 32}
    (hs : Scr s base size) (hptr : K.ptr + 4 ≤ size)
    (hb : s.gpr .esi = BitVec.ofNat 32 j) (hT : s.mem.readW (off base K.ptr) 32 = T)
    (htb : K.tblBytes < 2 ^ 32) :
    WP isa (.block K.selSetup) s fun t => t.gpr .edx = T + BitVec.ofNat 32 (j * K.tblBytes) ∧
      CKeeps [.eax, .ecx, .edx] s t := by
  have hea : (s.gpr .edi + BitVec.ofNat 32 K.ptr).setWidth 64 = off base K.ptr :=
    hs.ea (d := K.ptr) (by omega_using [hptr])
  have hread := hs.read hptr
  apply WP.of_runBlock
  simp only [TCombCfg.selSetup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, execMul, State.load32, State.ea, sc, at_, hb, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.mem_setFlags, hea, hread, hT,
    Option.map_some, Option.bind_some, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt htb, Nat.mod_mul_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2,
      ite_false]

/-- The retained table pointer addresses every entry; the scalar magnitude
only controls masks. The selected point is neutral when its magnitude is zero. -/
theorem select_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 1 ≤ K.M.n ∧ K.M.n ≤ 6) (hH : K.H < 2 ^ 31) (htb : K.tblBytes < 2 ^ 32)
    (hptr : K.ptr + 4 ≤ size) (hexy : K.E.y = K.E.x + 8 * K.M.n)
    (hy : K.E.y + 8 * K.M.n ≤ size) (hz : K.E.z + 8 * K.M.n ≤ size)
    (hxz : K.E.x + 16 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x)
    (hzero : K.zero + 8 * K.M.n ≤ size)
    (h0xy : K.zero + 8 * K.M.n ≤ K.E.x ∨ K.E.x + 16 * K.M.n ≤ K.zero)
    (h0z : K.zero + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.zero)
    (hone : K.one < 2 ^ (64 * K.M.n)) (h0 : wordsVal s.mem base K.zero K.M.n = 0)
    {j a : Nat} {T : BitVec 32} (hb : s.gpr .esi = BitVec.ofNat 32 j)
    (h8 : s.gpr .ebx = BitVec.ofNat 32 a) (ha : a ≤ K.H)
    (hT : s.mem.readW (off base K.ptr) 32 = T)
    (hreg : InRegions (s.rd ++ s.wr) ((T + BitVec.ofNat 32 (j * K.tblBytes)).setWidth 64) K.tblBytes)
    (hX : ((T + BitVec.ofNat 32 (j * K.tblBytes)).setWidth 64).toNat + K.tblBytes ≤ 2 ^ 32) :
    WP isa (.block K.select) s
      (SelPost K base s a ((T + BitVec.ofNat 32 (j * K.tblBytes)).setWidth 64)) := by
  have hnw := hs.nowrap
  have htbe : K.tblBytes = 16 * K.M.n * K.H := rfl
  rw [TCombCfg.select, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (selSetup_ok K hs hptr hb hT htb) fun s₁ ⟨x₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁.keeps (by decide)
  have h8₁ : s₁.gpr .ebx = BitVec.ofNat 32 a := by rw [k₁.1 _ (by decide), h8]
  have hr : ∀ e < K.H, ∀ c < K.M.n, InRegions (s₁.rd ++ s₁.wr)
      ((T + BitVec.ofNat 32 (j * K.tblBytes)).setWidth 64 +
        BitVec.ofNat 64 (16 * K.M.n * e + 16 * c)) 16 := by
    intro e he c hc
    rw [k₁.2.2.1, k₁.2.2.2]
    refine VG.CallLay.inRegions_sub hreg ?_ (by omega_using [htb])
    have := Nat.mul_le_mul_left (16 * K.M.n) (show e + 1 ≤ K.H by omega_using [he])
    rw [Nat.mul_add, Nat.mul_one] at this; omega_using [hn, htb, hy, hz, hxz, hzero, h0xy, h0z, hX, htbe, he, hc, this]
  refine WP.mono (selPass_ok K hs₁ hn.2 hH (by omega_using [hH, ha]) h8₁ (congrArg (BitVec.setWidth 64) x₁)
    hr hX (by omega_using [hexy, hy])) fun s₂ ⟨a₂, O₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have h8₂ : s₂.gpr .ebx = BitVec.ofNat 32 a := by rw [k₂.1 _ (by decide), h8₁]
  have h0₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by
    rw [O₂.wordsVal h0xy (by omega_using [hzero, hnw]), k₁.2.1, h0]
  refine WP.mono (selOne_ok K hs₂ (by omega_using [hH, ha]) h8₂ hy hz hzero (by omega_using [hexy, hxz]) (by omega_using [hexy, h0xy]) h0z hone h0₂)
    fun t ⟨ey, ez, k₃, U₃⟩ => ?_
  have W := accVal_word a₂
  rw [k₁.2.1] at W
  have hxw : ∀ i < K.M.n, word t.mem base (K.E.x + 8 * i) = word s₂.mem base (K.E.x + 8 * i) := fun i hi =>
    U₃.word (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> omega_arith) (by omega_using [hexy, hy, hnw, hi])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases h1 : 1 ≤ a
    · rw [ite_eq_left h1]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [hxw i hi, W i (by omega_using [hi]), ite_eq_left ⟨h1, ha⟩]
    · rw [ite_eq_right h1]
      exact wordsVal_zeros fun i hi => by
        rw [hxw i hi, W i (by omega_using [hi]), ite_eq_right (by omega_using [h1])]
  · by_cases h1 : 1 ≤ a
    · rw [ite_eq_left h1, ey, ite_eq_right (by omega_using [h1])]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [hexy, show K.E.x + 8 * K.M.n + 8 * i = K.E.x + 8 * (K.M.n + i) by omega_using [],
          W _ (by omega_using [hi]), ite_eq_left ⟨h1, ha⟩]
        rw [show 16 * K.M.n * (a - 1) + 8 * (K.M.n + i) =
          16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i by omega_using []]
    · rw [ite_eq_right h1, ey, ite_eq_left (by omega_using [h1])]
  · rw [ez]; split <;> split <;> omega
  · exact (k₁.keeps.trans (k₂.mono (by decide))).trans k₃
  · have U₂ : Unch base [(K.E.x, 8 * K.M.n), (K.E.x + 8 * K.M.n, 8 * K.M.n)] s.mem s₂.mem := by
      rw [← k₁.2.1]
      exact Unch.split (by rw [show 2 * (8 * K.M.n) = 16 * K.M.n by omega_using []]; exact O₂.unch)
    rw [← hexy] at U₂
    exact (U₂.trans U₃).mono fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h | h <;> simp [h]

end VG.Proof.Weierstrass.X86

end

end

/-! ## `TCombEntry` -/

@[expose] public section

section

/-!
# The fixed-base comb from tables in memory on x86 (32-bit)

What the comb (`TCombJ.lean`) needs of its tables and constants
(`TCombVals`): the selection's words are the entries' coordinates in
Montgomery form (`tbl_entry`).
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

/-- What the comb needs of its tables `tbl` (affine points, whose Montgomery
forms `tcombWords` are in memory) and constants: `J` tables of `H` entries,
entry `m` of table `j` the point `[(m + 1) 2^(wj)]G`, the start (in
Montgomery form) `[H Σ_{i<J} 2^(wi)]G`, and `R mod p` one. -/
structure TCombVals (K : TCombCfg) (C : Curve) (tbl : List (List (Nat × Nat))) : Prop where
  len : tbl.length = K.J
  lenH : ∀ j < K.J, (tbl.getD j []).length = K.H
  unit : UnitMod C.p (2 ^ (64 * K.M.n))
  one_lt : K.one < C.p
  one : toM C.p (2 ^ (64 * K.M.n)) K.one = 1
  entry : ∀ j < K.J, ∀ m < K.H, Rep C (Fin.ofNat C.p (combAt tbl j m).1)
    (Fin.ofNat C.p (combAt tbl j m).2) 1 (combPtW C K.w j (m + 1))
  start_lt : K.start.1 < C.p ∧ K.start.2 < C.p
  start : Rep C (toM C.p (2 ^ (64 * K.M.n)) K.start.1) (toM C.p (2 ^ (64 * K.M.n)) K.start.2) 1
    (mul (K.H * geomW K.w K.J) (G C))
  /-- The functions of the field arithmetic, of `n` words modulo `p`. -/
  fn : K.F.k = K.M.n ∧ K.F.m = C.p ∧ Mont.FnOk K.F

/-- `x ∈ l` for the comb's lists, through `toComb`. -/
macro "tcomb_mem" : tactic => `(tactic| plain_simp_names first
                   | list_mem
                   | (simp only [List.mem_cons, List.mem_append, List.mem_singleton, true_or, or_true, combSlots,
                       combWs, combRo, rcbW, rcbR, List.cons_append, List.nil_append, TCombCfg.toComb]))

/-- `a ≠ b` (or a conjunction of such, or `a ∉ [b, …]`) from `h`, the conjunction of `¬ x = y`
that a `Nodup` of the slots simplifies to, in either orientation: not `grind`, which takes a tenth
of a second for each. -/
macro "nd_ne " h:ident : tactic => `(tactic| plain_simp_names (
                   try simp only [ne_eq, List.mem_cons, List.not_mem_nil, or_false, not_or]
                   repeat' apply And.intro
                   all_goals first
                     | nd_find $h:ident
                     | simp only [ne_eq, $h:ident, not_false_eq_true]
                     | exact Ne.symm (by simp only [ne_eq, $h:ident, not_false_eq_true])))

end VG.Proof.Weierstrass.X86

end

/-! ## `TCombInv` -/

section

/-! # State and memory invariants for the x86 comb -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont
open Spec.Weierstrass

structure TCombFixed (K : TCombCfg) (C : Curve) (base : Addr) (size : Nat) (s₀ : State) (k : Nat)
    (T : Addr) (ws : List (BitVec 64)) : Prop where
  a : tmv C K.M.n base s₀ K.S.a = Fin.ofNat C.p C.a
  b : tmv C K.M.n base s₀ K.S.b3 = Fin.ofNat C.p C.b
  ro_lt : ∀ x ∈ combRo K.toComb, wordsVal s₀.mem base x K.M.n < C.p
  zero : wordsVal s₀.mem base K.zero K.M.n = 0
  bits : ∀ t < K.kbytes, s₀.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0
  k_lt : k < 2 ^ K.kbytes
  tsym : (s₀.mem.readW (off base K.ptr) 32).setWidth 64 = T
  tbl : TblMem s₀ T ws
  out : ∀ i < ws.length, ∀ b < 8, size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)
  /-- The tables are apart from the writable regions and the stack the calls use. -/
  apart : ∀ r ∈ s₀.wr ++ [below (s₀.gpr .esp) 20], Region.Disjoint ⟨T, 8 * ws.length⟩ r
  sp_lo : 20 ≤ (s₀.gpr .esp).toNat

/-- The tables survive code from a state that keeps the regions and `esp` of
`s₀` and uses 20 bytes of stack. -/
theorem TCombFixed.tblAt {K : TCombCfg} {C : Curve} {base : Addr} {size : Nat} {s₀ : State} {k : Nat}
    {T : Addr} {ws : List (BitVec 64)} (hF : TCombFixed K C base size s₀ k T ws) {s s' : State}
    (hwr : s.wr = s₀.wr) (hsp : s.gpr .esp = s₀.gpr .esp) (h : TblMem s T ws)
    (hrd : s'.rd ++ s'.wr = s.rd ++ s.wr) (hf : Frame (s.wr ++ [below (s.gpr .esp) 20]) s.mem s'.mem) :
    TblMem s' T ws :=
  h.of_frame hrd hf (by rw [hwr, hsp]; exact hF.apart)

theorem tcombW_mo {K : TCombCfg} {size m : Nat} {mem : Mem} {base : Addr} (hL : TCombLay K size)
    (hM : ModOkW K.M size m mem base) : ∀ w ∈ tcombW K, K.M.mo + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ K.M.mo := by
  intro w hw
  simp only [tcombW, combWx, combW, List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at hw
  rcases hw with ((⟨y, hy, rfl⟩ | rfl) | rfl | rfl) | rfl
  · have := hL.comb.lay.mo y (combWs_slots _ y hy); dsimp only [TCombCfg.toComb] at this ⊢; omega_arith
  · have := hM.sep; dsimp only [TCombCfg.toComb] at this ⊢; omega_arith
  · exact .inl hL.wmo
  · have := hM.mo; have := hL.sz; exact .inl (by dsimp only [Mont.outW]; omega_arith)
  · have := hL.bits_sl K.M.mo (List.mem_cons_self ..); dsimp only; omega_arith

theorem tcombW_ro {K : TCombCfg} {size : Nat} (hL : TCombLay K size) {x : Nat}
    (hx : x ∈ combRo K.toComb) : ∀ w ∈ tcombW K, x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  have hxs := combRo_slots x hx
  simp only [tcombW, combWx, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (hw | rfl | rfl) | rfl
  · exact combW_ro hL.comb hx w hw
  · exact .inl (hL.wsl x hxs)
  · have h1 := hL.comb.lay.le x hxs; have := hL.sz; dsimp only [TCombCfg.toComb] at h1
    exact .inl (by dsimp only [Mont.outW]; omega_arith)
  · have := hL.bits_sl x (List.mem_cons_of_mem _ hxs); dsimp only; omega_arith

theorem combW_bits {K : TCombCfg} {size : Nat} (hL : TCombLay K size) {t : Nat} (ht : t < K.w * K.J) :
    ∀ w ∈ combWx K, K.bits + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ K.bits + t := by
  have : K.w * K.J ≤ K.kbytes + 4 * K.zw := by unfold TCombCfg.zw; have := hL.kbytes; omega_arith
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · have := hL.bits_w w hw; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · rcases hL.wk_bits with h | h
      · exact .inl (by omega_arith)
      · exact .inr (by omega_arith)
    · have := hL.bits; have := hL.sz; exact .inl (by dsimp only [Mont.outW]; omega_arith)

theorem combW_ptr {K : TCombCfg} {size : Nat} (hL : TCombLay K size) :
    ∀ w ∈ combWx K, K.ptr + 4 ≤ w.1 ∨ w.1 + w.2 ≤ K.ptr := by
  intro w hw
  simp only [combWx, combW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hw
  rcases hw with (⟨x, hx, rfl⟩ | rfl) | rfl | rfl
  · exact hL.ptr_sl x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (combWs_slots _ x hx)))
  · exact hL.ptr_sl K.M.tmp (by simp)
  · exact .inl hL.ptr_wk
  · have := hL.ptr_le; have := hL.sz; exact .inl (by dsimp only [Mont.outW]; omega_arith)

theorem unch_read32 {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Unch base W m m')
    {d : Nat} (hd : d + 4 ≤ 2 ^ 64) (hW : ∀ w ∈ W, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 := by
  apply Mem.readW_congr
  intro i hi
  rw [off, Offset.add_add]
  exact h.byte (fun w hw => by have := hW w hw; omega_arith) (by omega_arith)

theorem copyWords_ok {s : State} {base : Addr} {size n o a : Nat} (hs : Scr s base size)
    (ho : o + 8 * n ≤ size) (ha : a + 8 * n ≤ size) (hsep : o ≤ a ∨ a + 8 * n ≤ o) :
    WP isa (.block (copy (2 * n) o a)) s fun t =>
      wordsVal t.mem base o n = wordsVal s.mem base a n ∧ Keeps [.eax] s t ∧
      Outside base o (8 * n) s.mem t.mem := by
  refine WP.mono (copy_ok (2 * n) hs (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨v, k, O⟩ =>
    ⟨by simpa only [wordsVal_eq_val32] using v, k, by simpa only [show 4 * (2 * n) = 8 * n by omega_arith] using O⟩

/-- `o = a`, a point, for `o`'s slots apart from each other and from `a`'s. -/
theorem copyPt_ok {s : State} {base : Addr} {size n : Nat} (hs : Scr s base size) {o a : Pt}
    (hle : ∀ x ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x + 8 * n ≤ size)
    (hap : ∀ x ∈ [o.x, o.y, o.z], ∀ y ∈ [o.x, o.y, o.z, a.x, a.y, a.z], x ≠ y →
      x + 8 * n ≤ y ∨ y + 8 * n ≤ x)
    (hne : ∀ x ∈ [o.x, o.y, o.z], x ∉ [a.x, a.y, a.z]) (ho : o.x ≠ o.y ∧ o.x ≠ o.z ∧ o.y ≠ o.z) :
    WP isa (.block (copyPt n o a)) s fun t =>
      wordsVal t.mem base o.x n = wordsVal s.mem base a.x n ∧
      wordsVal t.mem base o.y n = wordsVal s.mem base a.y n ∧
      wordsVal t.mem base o.z n = wordsVal s.mem base a.z n ∧
      KeepRegs [.eax] s t ∧ Unch base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem t.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, not_or] at hle hap hne
  obtain ⟨⟨xa, xb, xc⟩, ⟨ya, yb, yc⟩, ⟨za, zb, zc⟩⟩ := hne
  have pxy := hap.1.2.1 ho.1
  have pxz := hap.1.2.2.1 ho.2.1
  have pyz := hap.2.1.2.2.1 ho.2.2
  have pxa := hap.1.2.2.2.1 xa
  have pxb := hap.1.2.2.2.2.1 xb
  have pxc := hap.1.2.2.2.2.2 xc
  have pyb := hap.2.1.2.2.2.2.1 yb
  have pyc := hap.2.1.2.2.2.2.2 yc
  have pzc := hap.2.2.2.2.2.2.2 zc
  rw [copyPt, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyWords_ok hs (o := o.x) (a := a.x) hle.1 hle.2.2.2.1 (by omega_using [ho, hle, hap, xa, xb, xc, ya, za, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (copyWords_ok hs₁ (o := o.y) (a := a.y) hle.2.1 hle.2.2.2.2.1 (by omega_using [ho, hle, hap, xb, ya, yb, yc, zb, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (copyWords_ok hs₂ (o := o.z) (a := a.z) hle.2.2.1 hle.2.2.2.2.2 (by omega_using [ho, hle, hap, xc, yc, za, zb, zc, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc]))
    fun t ⟨e₃, k₃, O₃⟩ => ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.wordsVal (by omega_using [ho, hle, hap, xa, xb, xc, za, zb, zc, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc]) (by omega_using [ho, hn, hle, hap, xa, xb, xc, ya, yb, yc, za, zb, zc, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc]), O₂.wordsVal (by omega_using [ho, hle, hap, xa, xb, xc, ya, yb, yc, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc]) (by omega_using [ho, hn, hle, hap, xa, xb, xc, ya, yb, yc, za, zb, zc, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc]), e₁]
  · rw [O₃.wordsVal (by omega_using [ho, hle, hap, ya, yb, yc, za, zb, zc, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc]) (by omega_using [ho, hn, hle, hap, xa, xb, xc, ya, yb, yc, za, zb, zc, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc]), e₂, O₁.wordsVal (by omega_using [ho, hle, hap, xa, xb, xc, yb, zb, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc]) (by omega_using [ho, hn, hle, hap, xa, xb, xc, ya, yb, yc, za, zb, zc, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc])]
  · rw [e₃, O₂.wordsVal (by omega_using [ho, hle, hap, xc, ya, yb, yc, zc, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc]) (by omega_using [ho, hn, hle, hap, xa, xb, xc, ya, yb, yc, za, zb, zc, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc]), O₁.wordsVal (by omega_using [ho, hle, hap, xa, xb, xc, yc, zc, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc]) (by omega_using [ho, hn, hle, hap, xa, xb, xc, ya, yb, yc, za, zb, zc, pxy, pxz, pyz, pxa, pxb, pxc, pyb, pyc, pzc])]
  · exact (O₁.unch.trans (O₂.unch.trans O₃.unch)).mono fun w hw => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h <;> simp [h]

theorem clob_powClob : ∀ r ∈ clob, r ∈ powClob := fun _ h => List.mem_cons_of_mem _ h

end VG.Proof.Weierstrass.X86

end

/-! ## `TCombInit` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont
open Spec.Weierstrass

theorem tcombW_ptr {K : TCombCfg} {size : Nat} (hL : TCombLay K size) :
    ∀ w ∈ combWx K ++ [(K.bits + K.kbytes, 4 * K.zw)], K.ptr + 4 ≤ w.1 ∨ w.1 + w.2 ≤ K.ptr := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact combW_ptr hL w hw
  · simp only [List.mem_singleton] at hw; subst hw
    have := hL.ptr_bits; dsimp only; omega_arith

/-- Zero stored to the `m` words at `o`, from `rax = 0`. -/
theorem zstores_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hz : s.gpr .eax = 0)
    {o : Nat} : ∀ m, o + 4 * m ≤ size →
    WP isa (.block ((List.range m).map fun i => .store (sc (o + 4 * i)) .eax)) s fun s' =>
      KeepRegs [] s s' ∧ Outside base o (4 * m) s.mem s'.mem ∧
        ∀ d < 4 * m, s'.mem (off base (o + d)) = 0
  | 0, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _,
      fun d hd => absurd hd (by omega_arith)⟩
  | m + 1, hm => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zstores_ok hs hz m (by omega_arith)) fun s₁ ⟨k₁, O₁, z₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by simp)
    have hrax : s₁.gpr .eax = 0 := (k₁.gpr _ (by simp)).trans hz
    simp only [List.map_cons, List.map_nil]
    refine wp_storeS (hs₁.ea (d := o + 4 * m) (by omega_arith)) (hs₁.write (d := o + 4 * m) (n := 4) (by omega_arith))
      fun s₂ u₂ => WP.block_nil ?_
    have Ow : Outside base (o + 4 * m) 4 s₁.mem s₂.mem := by
      rw [u₂.mem]; exact writeW32_outside _ _ _ (by omega_arith)
    refine ⟨k₁.trans (u₂.keeps _), fun x hx => (Ow x (by omega_arith)).trans (O₁ x (by omega_arith)),
      fun d hd => ?_⟩
    by_cases hd' : d < 4 * m
    · rw [Ow _ (by rw [ofs_off0 base (by omega_arith)]; omega_arith)]; exact z₁ d hd'
    · have e : off base (o + d) - off base (o + 4 * m) = BitVec.ofNat 64 (d - 4 * m) := by
        simp only [off]; rw [show o + d = o + 4 * m + (d - 4 * m) by omega_arith, Offset.add_ofNat_add_sub]
      rw [u₂.mem, hrax]
      simp only [Mem.writeW, Mem.write, e, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show d - 4 * m < 2 ^ 64 by omega_arith), show d - 4 * m < 32 / 8 by omega_arith,
        ↓reduceIte]
      simp

theorem zeroEax_ok (s : State) :
    WP isa (.block [.mov .eax (.imm 0)]) s fun t => t.gpr .eax = 0 ∧ CKeeps [.eax] s t :=
  wp_movS rfl fun _t u _ => WP.block_nil ⟨u.gpr, u.keeps.1, u.mem, u.keeps.2⟩

theorem movEsi_ok (s : State) {j : Nat} (_hj : j < 2^31) :
    WP isa (.block [.mov .esi (.imm (BitVec.ofNat 32 j))]) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 j ∧ CKeeps [.esi] s t :=
  wp_movS rfl fun _t u _ => WP.block_nil ⟨u.gpr, u.keeps.1, u.mem, u.keeps.2⟩

end VG.Proof.Weierstrass.X86

end

/-! ## `TComb` -/

section

/-! # Correctness of the 32-bit x86 fixed-base comb -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont
open Spec.Weierstrass

/-- Save the table address in the scratch header before initializing the comb. -/
theorem savePtr_ok {K : TCombCfg} {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hL : TCombLay K size) :
    WP isa (.block [.store (sc K.ptr) .eax]) s fun t =>
      t.mem.readW (off base K.ptr) 32 = s.gpr .eax ∧ Keeps [] s t ∧
        Outside base K.ptr 4 s.mem t.mem := by
  have hn := hs.nowrap
  have hp := hL.ptr_le
  refine wp_storeS (hs.ea (by omega_arith)) (hs.write (n := 4) hp) fun t u => WP.block_nil ?_
  refine ⟨?_, u.keeps _, ?_⟩
  · rw [u.mem, Mem.readW_writeW_self32]
  · rw [u.mem]; exact writeW32_outside _ _ _ (by omega_arith)

end VG.Proof.Weierstrass.X86

end
