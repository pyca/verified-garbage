import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Avx2

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase`. -/
section

/-!
# ML-DSA on x86-64: coefficients in the lanes of AVX2 registers

The AVX2 code does to each 128-bit lane what the SSE2 code does to a register
(`toY`), so the proofs of the SSE2 code hold of each lane (`ylanes`,
ML-KEM's): `YConsts` is `VConsts` in both lanes (`yconsts_ok`); a 256-bit load
of coefficient `j` puts coefficients `j + 4l` to `j + 4l + 3` in lane `l`
(`dlanes_loadY`), and a 256-bit store of a register whose lanes hold `a` and `a
(· + 4)` puts `a` at coefficients `j` to `j + 7` (`polyIs_write2Y`,
`ylanes_ymm`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly XKeep YOnly ylanes yld_ok yconst_ok ifp ifn)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt PolyIs)

/-- `VConsts` in both lanes. -/
def YConsts (s : State) : Prop := ∀ l < 2, VConsts (s.proj l)

theorem yonly_yconsts {rs : List XReg} {s s' : State} (h : YOnly rs s s') (hc : VG.Proof.MlDsa.X86_64.Arith.YConsts s)
    (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) : VG.Proof.MlDsa.X86_64.Arith.YConsts s' := fun l hl =>
  ⟨by rw [State.proj_xmm, h.lane _ h15 l hl]; exact (hc l hl).q,
    by rw [State.proj_xmm, h.lane _ h14 l hl]; exact (hc l hl).qinv⟩

/-- The constants in both lanes. -/
theorem yconsts_ok (s : State) :
    WP isa (.block yconsts) s fun s' => VG.Proof.MlDsa.X86_64.Arith.YConsts s' ∧ Keep [.rax] s s' ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr ∧ ∀ r, r ≠ .xmm15 → r ≠ .xmm14 → ∀ l < 2, s'.lane r l = s.lane r l := by
  rw [yconsts, WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm15 _ s) fun s1 ⟨l1, k1, m1, x1, o1⟩ =>
    WP.mono (yconst_ok .xmm14 _ s1) fun s2 ⟨l2, k2, m2, x2, o2⟩ =>
      ⟨fun l hl => ⟨?_, ?_⟩, (k1.trans k2).mono (by simp), m2.trans m1, x2.trans x1,
        fun r h15 h14 l hl => by rw [o2 r h14 l hl, o1 r h15 l hl]⟩
  · rw [State.proj_xmm, o2 _ (by decide) l hl, l1 l hl]; decide
  · rw [State.proj_xmm, l2 l hl]; decide

/-- The eight doublewords of a 256-bit value, as those of its lanes. -/
theorem extract_ymm (hi lo : BitVec 128) {e : Nat} (he : e < 8) :
    (hi ++ lo).extractLsb' (32 * e) 32 = if e < 4 then dword lo e else dword hi (e - 4) := by
  by_cases h4 : e < 4
  · rw [ifp h4]
    apply BitVec.eq_of_getLsbD_eq; intro i hi'
    simp only [dword, BitVec.getLsbD_extractLsb', hi', decide_true, Bool.true_and, BitVec.getLsbD_append,
      ifp (show 32 * e + i < 128 by omega)]
  · rw [ifn h4]
    apply BitVec.eq_of_getLsbD_eq; intro i hi'
    simp only [dword, BitVec.getLsbD_extractLsb', hi', decide_true, Bool.true_and, BitVec.getLsbD_append,
      ifn (show ¬32 * e + i < 128 by omega)]
    exact congrArg _ (by omega)

/-- The doublewords of a 256-bit value are the coefficients `a`. -/
def YLanes (x : BitVec 256) (a : Nat → Zq) : Prop := ∀ e < 8, (x.extractLsb' (32 * e) 32).toNat = (a e).val

/-- A register whose lanes hold `a` and `a (· + 4)`. -/
theorem ylanes_ymm {s : State} {r : XReg} {a : Nat → Zq} (h0 : DLanes (s.lane r 0) a)
    (h1 : DLanes (s.lane r 1) (fun e => a (e + 4))) : VG.Proof.MlDsa.X86_64.Arith.YLanes (s.ymm r) a := fun e he => by
  have h0' : DLanes (s.xmm r) a := h0
  have h1' : DLanes (s.ymmHi r) (fun e => a (e + 4)) := h1
  rw [State.ymm, VG.Proof.MlDsa.X86_64.Arith.extract_ymm _ _ he]
  split
  · exact h0' e (by omega)
  · rw [h1' (e - 4) (by omega)]; dsimp only; rw [show e - 4 + 4 = e by omega]

/-- Coefficient `i` after storing `x` at coefficient `j`. -/
theorem coeffAt_write256 (m : Mem) (p : Addr) {j : Nat} (hj : j + 8 ≤ 256) (x : BitVec 256) {i : Nat}
    (hi : i < 256) :
    coeffAt (m.writeW (coeffAddr p j) x) p i =
      if j ≤ i ∧ i < j + 8 then x.extractLsb' (32 * (i - j)) 32 else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq, show coeffAddr p i = coeffAddr p j + BitVec.ofNat 64 (4 * (i - j)) by
      rw [coeffAddr_add, show j + (i - j) = i by omega]]
    rw [show 32 * (i - j) = 8 * (4 * (i - j)) by omega]
    exact readW_writeW_inside (k := 4 * (i - j)) (n := 4) _ _ _ (by omega) (by decide)
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- Two vectors of eight coefficients stored into a polynomial. -/
theorem polyIs_write2Y {m : Mem} {p : Addr} {P R : Poly} (hP : PolyIs m p P) {j j' : Nat}
    (hj : j + 8 ≤ 256) (hj' : j' + 8 ≤ 256) (hsep : j + 8 ≤ j' ∨ j' + 8 ≤ j) {x y : BitVec 256}
    {a b : Nat → Zq} (hx : VG.Proof.MlDsa.X86_64.Arith.YLanes x a) (hy : VG.Proof.MlDsa.X86_64.Arith.YLanes y b)
    (hR : ∀ i < 256, R[i]! = if j ≤ i ∧ i < j + 8 then a (i - j)
      else if j' ≤ i ∧ i < j' + 8 then b (i - j') else P[i]!) :
    PolyIs ((m.writeW (coeffAddr p j) x).writeW (coeffAddr p j') y) p R := polyIs_of_toNat fun i hi => by
  rw [n_eq] at hi
  rw [VG.Proof.MlDsa.X86_64.Arith.coeffAt_write256 _ _ hj' _ hi, VG.Proof.MlDsa.X86_64.Arith.coeffAt_write256 _ _ hj _ hi, hR i hi]
  by_cases h1 : j' ≤ i ∧ i < j' + 8
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true h1)]
    exact hy _ (by omega)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : j ≤ i ∧ i < j + 8
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true h2)]
      exact hx _ (by omega)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact polyIs_toNat hP (by rw [n_eq]; exact hi)

theorem pR_contains32 (p : Addr) {j : Nat} (hj : j + 8 ≤ 256) : (pR p).Contains (coeffAddr p j) 32 :=
  Offset.contains_base p (by omega) (by omega)

theorem f_in32 {rs : List Region} {fP : Addr} (hw : pR fP ∈ rs) {j : Nat} (hj : j + 8 ≤ 256) :
    InRegions rs (coeffAddr fP j) 32 :=
  ⟨_, hw, VG.Proof.MlDsa.X86_64.Arith.pR_contains32 fP hj⟩

theorem frame_write2Y {m m' : Mem} {p : Addr} (hf : Frame [pR p] m m') {j j' : Nat} (hj : j + 8 ≤ 256)
    (hj' : j' + 8 ≤ 256) (x y : BitVec 256) :
    Frame [pR p] m ((m'.writeW (coeffAddr p j) x).writeW (coeffAddr p j') y) :=
  (hf.writeW (List.mem_singleton_self _) x (VG.Proof.MlDsa.X86_64.Arith.pR_contains32 p hj)).writeW (List.mem_singleton_self _) y
    (VG.Proof.MlDsa.X86_64.Arith.pR_contains32 p hj')

/-- Lane `l` of a 256-bit load of coefficient `j`. -/
theorem lane_load {p : Addr} {j l : Nat} :
    coeffAddr p j + BitVec.ofNat 64 (16 * l) = coeffAddr p (j + 4 * l) := by
  rw [show 16 * l = 4 * (4 * l) by omega, coeffAddr_add]

/-- The lanes of a 256-bit load of coefficient `j` of `F`. -/
theorem dlanes_loadY {m : Mem} {p : Addr} {F : Poly} (h : PolyIs m p F) {j : Nat} (hj : j + 8 ≤ 256)
    {l : Nat} (hl : l < 2) :
    DLanes (m.readW (coeffAddr p j + BitVec.ofNat 64 (16 * l)) 128) (fun e => F[j + 4 * l + e]!) := by
  rw [VG.Proof.MlDsa.X86_64.Arith.lane_load]
  exact dlanes_load h (by omega)

end VG.Proof.MlDsa.X86_64.Arith

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YAddSub`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_add_avx2` and `vg_mldsa_sub_avx2`

Each iteration of the loop loads eight coefficients of `f` and of `g` and, in
each lane, does what an iteration of `vg_mldsa_add` (`vg_mldsa_sub`) does
(`AddSub.lean`), whose proof holds of each lane (`ylanes`), and stores the
eight results to `f` (`YAddSub.step`); the loop leaves `f` with all 256
(`YAddSub.fn_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok yconst_ok WP.keep writesOnly gprPreserved_of ifp ifn
  ptr_step GOnly wp_rcxLoopY add_ofNat_zero lane_setReg lane_setFlags sx32 State.setMem_ymm)
open VG.Impl.MlKem.X86_64 (xb xmov toY yconst)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt Reduced PolyIs)

theorem addFixX_ok (s : State) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block (xb .paddd .xmm0 .xmm1 :: vcsub .xmm0 .xmm2)) s fun s' =>
      s'.xmm .xmm0 = addV (s.xmm .xmm0) (s.xmm .xmm1) ∧ XOnly [.xmm0, .xmm2] s s' := by
  simp only [vcsub, vcadd, xmov, xb]
  vrun [eval_movdqa]
  rw [hq]
  exact ⟨rfl, by xonly⟩

theorem subFixX_ok (s : State) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block (xb .psubd .xmm0 .xmm1 :: vcadd .xmm0 .xmm2)) s fun s' =>
      s'.xmm .xmm0 = subV (s.xmm .xmm0) (s.xmm .xmm1) ∧ XOnly [.xmm0, .xmm2] s s' := by
  simp only [vcadd, xmov, xb]
  vrun [eval_movdqa]
  rw [hq]
  exact ⟨rfl, by xonly⟩

theorem lane_addFix : laneSseBlock (toY (xb .paddd .xmm0 .xmm1 :: vcsub .xmm0 .xmm2)) =
    some (xb .paddd .xmm0 .xmm1 :: vcsub .xmm0 .xmm2) := by decide +kernel

theorem lane_subFix : laneSseBlock (toY (xb .psubd .xmm0 .xmm1 :: vcadd .xmm0 .xmm2)) =
    some (xb .psubd .xmm0 .xmm1 :: vcadd .xmm0 .xmm2) := by decide +kernel

namespace YAddSub

/-- After `i` vectors of eight, each coefficient before `8i` is `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (32 * i)
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  q : ∀ l < 2, s.lane .xmm15 l = qV
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdi) k = if k < 8 * i then v k else coeffAt s₀.mem (s₀.gpr .rdi) k

section
variable {t : Poly → Poly → Poly} {s₀ : State} (hp : (accK t).pre s₀)
  {op : XBinOp} {fix : List Instr} {F : BitVec 128 → BitVec 128 → BitVec 128}
  {L : BitVec 32 → BitVec 32 → BitVec 32}
  (hF : ∀ (s : State), s.xmm .xmm15 = qV →
    WP isa (.block (xb op .xmm0 .xmm1 :: fix)) s fun s' =>
      s'.xmm .xmm0 = F (s.xmm .xmm0) (s.xmm .xmm1) ∧ XOnly [.xmm0, .xmm2] s s')
  (hY : laneSseBlock (toY (xb op .xmm0 .xmm1 :: fix)) = some (xb op .xmm0 .xmm1 :: fix))
  (hL : ∀ x y : BitVec 128, ∀ e < 4, dword (F x y) e = L (dword x e) (dword y e))
include hp hF hY hL

/-- An iteration, which stores `F` of the vectors of `f` and `g` in each lane. -/
theorem step {i : Nat} (hi : i < 32) {s : State}
    (hI : VG.Proof.MlDsa.X86_64.Arith.YAddSub.Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) i s) :
    WP isa (.block (yaccBody op fix ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      VG.Proof.MlDsa.X86_64.Arith.YAddSub.Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have hw : pR (s₀.gpr .rdi) ∈ s.wr := by rw [hI.wr, hp.2.1]; simp
  have hr : pR (s₀.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hI.rd, hI.wr, hp.1]; simp
  have e1 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]; congr 2; omega
  have e2 : s.gpr .rsi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rsi) (8 * i) := by
    rw [add_ofNat_zero, hI.rsi]; congr 2; omega
  rw [yaccBody, List.append_assoc, List.append_assoc, WP.block_append_iff,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1]; exact VG.Proof.MlDsa.X86_64.Arith.f_in32 (List.mem_append_right _ hw) j0)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, e2]; exact ⟨_, hr, VG.Proof.MlDsa.X86_64.Arith.pR_contains32 _ j0⟩))
    fun s2 ⟨L2, o2⟩ => ?_
  rw [WP.block_append_iff]
  have o12 := o1.trans o2
  refine WP.mono (ylanes hY (P := fun l t => t.xmm .xmm0 = F ((s2.proj l).xmm .xmm0) ((s2.proj l).xmm .xmm1))
    fun l hl => hF _ (by rw [State.proj_xmm, o12.lane _ (by decide) l hl]; exact hI.q l hl))
    fun s3 ⟨B3, o3⟩ => ?_
  have o13 := o12.trans o3
  have g3 : s3.gpr .rdi = coeffAddr (s₀.gpr .rdi) (8 * i) := by rw [o13.gpr, ← e1, add_ofNat_zero]
  have g3' : s3.gpr .rsi = coeffAddr (s₀.gpr .rsi) (8 * i) := by rw [o13.gpr, ← e2, add_ofNat_zero]
  have w0 : InRegions s3.wr (s3.gpr .rdi) 32 := by rw [o13.wr, g3]; exact VG.Proof.MlDsa.X86_64.Arith.f_in32 hw j0
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, w0, sx32]
  refine ⟨⟨?_, ?_, ?_, ?_, fun l hl => ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rdi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rsi]; exact ptr_step _ i 32
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr, hI.wr]
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]; rw [o13.lane _ (by decide) l hl]; exact hI.q l hl
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem]; exact hI.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.MlDsa.X86_64.Arith.pR_contains32 _ j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem, VG.Proof.MlDsa.X86_64.Arith.coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega), State.ymm, VG.Proof.MlDsa.X86_64.Arith.extract_ymm _ _ (by omega)]
      have hc : ∀ l < 2, ∀ e < 4, dword (s3.lane .xmm0 l) e =
          L (coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + 4 * l + e)) (coeffAt s₀.mem (s₀.gpr .rsi) (8 * i + 4 * l + e)) :=
        fun l hl e he => by
          rw [← State.proj_xmm, B3 l hl, hL _ _ _ he, State.proj_xmm, State.proj_xmm,
            o2.lane _ (by decide) l hl, L1 l hl, L2 l hl, o1.gpr, o1.mem, e1, e2, dword_readW _ _ he,
            dword_readW _ _ he, VG.Proof.MlDsa.X86_64.Arith.lane_load, VG.Proof.MlDsa.X86_64.Arith.lane_load, coeffAddr_add, coeffAddr_add, ← coeffAt_eq, ← coeffAt_eq,
            hI.coeff _ (by omega), ifn (by omega),
            coeffAt_frame hI.frame (by simpa using hp.2.2.1.symm) (by rw [n_eq]; omega)]
      split
      · rename_i h4
        have := hc 0 (by decide) (k - 8 * i) h4
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega] at this
        exact this
      · rename_i h4
        have := hc 1 (by decide) (k - 8 * i - 4) (by omega)
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega] at this
        exact this
    · rename_i h
      rw [hI.coeff k hk]
      by_cases h' : k < 8 * i
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]
  · exact ⟨by rw [o13.gpr], by rw [o13.gpr]⟩

/-- The whole function, from its precondition. -/
theorem fn_ok (hv : ∀ k < 256, (L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat =
      ((t (polyAt s₀.mem (s₀.gpr .rdi)) (polyAt s₀.mem (s₀.gpr .rsi)))[k]!).val)
    (hc : writesOnly [.rax, .rdi, .rsi, .rcx] (.seq (.block (yconst .xmm15 8380417))
      (.seq (VG.Impl.MlKem.X86_64.rcxLoop 32 (yaccBody op fix)) (.block yepi))) = true)
    (hm : Code.allInstrs (fun i => !loadsMxcsr i) (.seq (.block (yconst .xmm15 8380417))
      (.seq (VG.Impl.MlKem.X86_64.rcxLoop 32 (yaccBody op fix)) (.block yepi)) : Prog isa) = true) :
    ∃ tr s', Exec isa (.seq (.block (yconst .xmm15 8380417))
        (.seq (VG.Impl.MlKem.X86_64.rcxLoop 32 (yaccBody op fix)) (.block yepi))) s₀ tr s' ∧
      abiPreserved s₀ s' ∧ (accK t).post s₀ s' := by
  have hW : WP isa (.seq (.block (yconst .xmm15 8380417))
      (.seq (VG.Impl.MlKem.X86_64.rcxLoop 32 (yaccBody op fix)) (.block yepi))) s₀ fun s' =>
      Frame [pR (s₀.gpr .rdi)] s₀.mem s'.mem ∧ ∀ k < 256, coeffAt s'.mem (s₀.gpr .rdi) k =
        L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k) := by
    refine WP.seq (WP.mono (yconst_ok .xmm15 _ s₀) fun w ⟨lq, k1, m1, _, _⟩ => ?_)
    refine WP.seq (WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide) _ (fun u o hy _ =>
      ⟨by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero],
        by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero],
        by rw [o.keep.2.1, k1.2.1], by rw [o.keep.2.2, k1.2.2],
        fun l hl => by
          rw [show u.lane .xmm15 l = w.lane .xmm15 l by simp only [State.lane]; rw [o.xmm, hy], lq l hl]; decide,
        by rw [o.mem, m1]; exact Frame.refl _ _, fun k _ => by rw [o.mem, m1, ifn (by omega)]⟩)
      fun i hi u hI => VG.Proof.MlDsa.X86_64.Arith.YAddSub.step hp hF hY hL hi hI) fun u hI => ?_)
    refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem) (by simp only [yepi]; vrund; rfl) fun u' hm' => ?_
    rw [hm']
    exact ⟨hI.frame, fun k hk => by rw [hI.coeff k hk, ifp (by omega)]⟩
  obtain ⟨tr, s', he, ⟨hf, hco⟩, hk⟩ := WP.keep _ hW hc
  refine ⟨tr, s', he, abiPreserved_of_exec hm he (gprPreserved_of hk (by decide) hf ?_),
    polyIs_of_toNat fun k hk => ?_⟩
  · simpa using hp.2.2.2.1
  · rw [n_eq] at hk
    rw [hco k hk]
    exact hv k hk

end

end YAddSub

end VG.Proof.MlDsa.X86_64.Arith

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa (n)

theorem addY_correct (s : State) (hs : (accK Spec.MlDsa.add).pre s) :
    ∃ t s', Exec isa addAvx2 s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlDsa.add).post s s' :=
  YAddSub.fn_ok hs (op := .paddd) (fix := vcsub .xmm0 .xmm2) (L := fun a b => csubL (a + b)) VG.Proof.MlDsa.X86_64.Arith.addFixX_ok
    VG.Proof.MlDsa.X86_64.Arith.lane_addFix (fun x y e he => dword_addV x y he)
    (fun k hk => by
      have hk' : k < n := by rw [n_eq]; exact hk
      rw [add_get _ _ hk', addD_toNat (by rw [← polyAt_val hs.2.2.2.2.2.1 hk']; exact val_lt _)
          (by rw [← polyAt_val hs.2.2.2.2.2.2 hk']; exact val_lt _),
        ← polyAt_val hs.2.2.2.2.2.1 hk', ← polyAt_val hs.2.2.2.2.2.2 hk', val_add])
    (by decide +kernel) (by decide +kernel)

theorem subY_correct (s : State) (hs : (accK Spec.MlDsa.sub).pre s) :
    ∃ t s', Exec isa subAvx2 s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlDsa.sub).post s s' :=
  YAddSub.fn_ok hs (op := .psubd) (fix := vcadd .xmm0 .xmm2) (L := fun a b => caddL (a - b)) VG.Proof.MlDsa.X86_64.Arith.subFixX_ok
    VG.Proof.MlDsa.X86_64.Arith.lane_subFix (fun x y e he => dword_subV x y he)
    (fun k hk => by
      have hk' : k < n := by rw [n_eq]; exact hk
      rw [sub_get _ _ hk', subD_toNat (by rw [← polyAt_val hs.2.2.2.2.2.1 hk']; exact val_lt _)
          (by rw [← polyAt_val hs.2.2.2.2.2.2 hk']; exact val_lt _),
        ← polyAt_val hs.2.2.2.2.2.1 hk', ← polyAt_val hs.2.2.2.2.2.2 hk', val_sub])
    (by decide +kernel) (by decide +kernel)

theorem addY_ct : ConstantTime isa (accK Spec.MlDsa.add).pre (accK Spec.MlDsa.add).pub addAvx2 :=
  VG.Taint.constantTime (A := taint) VG.Proof.MlDsa.X86_64.Arith.accτ VG.Proof.MlDsa.X86_64.Arith.acc_agree (by taint_decide)

theorem subY_ct : ConstantTime isa (accK Spec.MlDsa.sub).pre (accK Spec.MlDsa.sub).pub subAvx2 :=
  VG.Taint.constantTime (A := taint) VG.Proof.MlDsa.X86_64.Arith.accτ VG.Proof.MlDsa.X86_64.Arith.acc_agree (by taint_decide)

theorem addY_verified : Verified X86_64.target addAvx2 (Spec.MlDsa.addContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Arith.addY_correct VG.Proof.MlDsa.X86_64.Arith.addY_ct (by
    mldsa_implies [Spec.MlDsa.addContract, Spec.MlDsa.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using VG.Proof.MlDsa.X86_64.Arith.accSat)

theorem subY_verified : Verified X86_64.target subAvx2 (Spec.MlDsa.subContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Arith.subY_correct VG.Proof.MlDsa.X86_64.Arith.subY_ct (by
    mldsa_implies [Spec.MlDsa.subContract, Spec.MlDsa.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using VG.Proof.MlDsa.X86_64.Arith.accSat)

end VG.Proof.MlDsa.X86_64.Arith

end
