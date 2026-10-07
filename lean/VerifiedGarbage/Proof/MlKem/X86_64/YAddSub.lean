import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2

/-!
# ML-KEM on x86-64: `vg_mlkem_add_avx2` and `vg_mlkem_sub_avx2`

Each iteration of the loop loads eight coefficients of `f` and of `g` and, in
each lane, does what an iteration of `vg_mlkem_add` (`vg_mlkem_sub`) does
(`AddSub.lean`): the same arithmetic (`addArith_ok`, `subArith_ok`), whose
proof holds of each lane (`ylanes`); it stores the eight results to `f`
(`YAddSub.step`), and the loop leaves `f` with all 256 (`YAddSub.fn_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## The arithmetic of a lane -/

theorem addArith_ok (s : State) (hq : s.xmm .xmm15 = qD) :
    WP isa (.block addArith) s fun s' =>
      (∀ j < 4, dword (s'.xmm .xmm0) j = cadd32 (dword (s.xmm .xmm0) j + dword (s.xmm .xmm1) j - 3329#32)) ∧
        XOnly [.xmm0, .xmm1] s s' := by
  simp only [addArith, dcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  refine ⟨fun j hj => ?_, by xonly⟩
  simp only [dword_paddd _ _ hj, dword_psubd _ _ hj, dword_pand, dword_psrad31 _ hj, hq, dword_qD hj]
  rfl

theorem subArith_ok (s : State) (hq : s.xmm .xmm15 = qD) :
    WP isa (.block subArith) s fun s' =>
      (∀ j < 4, dword (s'.xmm .xmm0) j = cadd32 (dword (s.xmm .xmm0) j - dword (s.xmm .xmm1) j)) ∧
        XOnly [.xmm0, .xmm1] s s' := by
  simp only [subArith, dcadd, xmov, xb]
  vrun [eval_movdqa]
  refine ⟨fun j hj => ?_, by xonly⟩
  simp only [dword_psubd _ _ hj, dword_paddd _ _ hj, dword_pand, dword_psrad31 _ hj, hq, dword_qD hj]
  rfl

theorem lane_addArith : laneSseBlock (toY addArith) = some addArith := by decide +kernel

theorem lane_subArith : laneSseBlock (toY subArith) = some subArith := by decide +kernel

/-! ## The loop -/

namespace YAddSub

/-- After `i` vectors of eight, each coefficient before `8i` is `v k`. -/
structure Inv (s₀ : State) (v : Nat → BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = coeffAddr (s₀.gpr .rdi) (8 * i)
  rsi : s.gpr .rsi = coeffAddr (s₀.gpr .rsi) (8 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  q : ∀ l < 2, s.lane .xmm15 l = qD
  frame : Frame [pR (s₀.gpr .rdi)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rdi) k = if k < 8 * i then v k else coeffAt s₀.mem (s₀.gpr .rdi) k

theorem in32 {rs : List Region} {p : Addr} (hw : pR p ∈ rs) {j : Nat} (hj : j + 8 ≤ 256) :
    InRegions rs (coeffAddr p j) 32 :=
  ⟨_, hw, Offset.contains_base _ (by omega) (by omega)⟩

/-- Doubleword `e` of lane `l` of a 256-bit load of coefficient `j`. -/
theorem lane_coeff (m : Mem) (p : Addr) (j l e : Nat) (he : e < 4) :
    dword (m.readW (coeffAddr p j + BitVec.ofNat 64 (16 * l)) 128) e = coeffAt m p (j + 4 * l + e) := by
  rw [dword_readW _ _ he, show 16 * l = 4 * (4 * l) by omega, coeffAddr_off p j (4 * l),
    coeffAddr_off p (j + 4 * l) e, ← coeffAt_eq]

section
variable {t : Poly → Poly → Poly} {s₀ : State} (hp : (accK t).pre s₀) {ar : List Instr}
  {L : BitVec 32 → BitVec 32 → BitVec 32}
  (hF : ∀ (s : State), s.xmm .xmm15 = qD →
    WP isa (.block ar) s fun s' =>
      (∀ j < 4, dword (s'.xmm .xmm0) j = L (dword (s.xmm .xmm0) j) (dword (s.xmm .xmm1) j)) ∧
        XOnly [.xmm0, .xmm1] s s')
  (hY : laneSseBlock (toY ar) = some ar)
include hp hF hY

/-- An iteration, which stores `L` of the coefficients of `f` and `g`. -/
theorem step {i : Nat} (hi : i < 32) {s : State}
    (hI : Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) i s) :
    WP isa (.block (yaccBody ar ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ (fun k => L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) (i + 1) s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have hw : pR (s₀.gpr .rdi) ∈ s.wr := by rw [hI.wr, hp.2.1]; simp
  have hr : pR (s₀.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hI.rd, hI.wr, hp.1]; simp
  have e1 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]
  have e2 : s.gpr .rsi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rsi) (8 * i) := by
    rw [add_ofNat_zero, hI.rsi]
  rw [yaccBody, List.append_assoc, List.append_assoc, WP.block_append_iff,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1]; exact in32 (List.mem_append_right _ hw) j0)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, e2]; exact in32 hr j0)) fun s2 ⟨L2, o2⟩ => ?_
  rw [WP.block_append_iff]
  have o12 := o1.trans o2
  refine WP.mono (ylanes hY (P := fun l t => ∀ j < 4, dword (t.xmm .xmm0) j =
      L (dword ((s2.proj l).xmm .xmm0) j) (dword ((s2.proj l).xmm .xmm1) j))
    fun l hl => hF _ (by rw [State.proj_xmm, o12.lane _ (by decide) l hl]; exact hI.q l hl))
    fun s3 ⟨B3, o3⟩ => ?_
  have o13 := o12.trans o3
  have g3 : s3.gpr .rdi = coeffAddr (s₀.gpr .rdi) (8 * i) := by rw [o13.gpr, ← e1, add_ofNat_zero]
  have w0 : InRegions s3.wr (s3.gpr .rdi) 32 := by rw [o13.wr, g3]; exact in32 hw j0
  vrunm [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, w0, sx32]
  refine ⟨⟨?_, ?_, ?_, ?_, fun l hl => ?_, ?_, fun k hk => ?_⟩, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rdi, show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_off, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rsi, show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_off, Nat.mul_succ]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr, hI.wr]
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]; rw [o13.lane _ (by decide) l hl]; exact hI.q l hl
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [g3, o13.mem, coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega)]
      obtain ⟨l, e, hl, he, hk'⟩ : ∃ l e, l < 2 ∧ e < 4 ∧ k = 8 * i + 4 * l + e :=
        ⟨(k - 8 * i) / 4, (k - 8 * i) % 4, by omega, by omega, by omega⟩
      subst hk'
      rw [show 8 * (4 * (8 * i + 4 * l + e - 8 * i)) = 8 * (16 * l + 4 * e) by omega, extract_ymm _ _ hl he,
        ← State.proj_xmm, B3 l hl e he, State.proj_xmm, State.proj_xmm, o2.lane _ (by decide) l hl, L1 l hl,
        L2 l hl, o1.gpr, o1.mem, e1, e2, lane_coeff _ _ _ _ _ he, lane_coeff _ _ _ _ _ he,
        hI.coeff _ (by omega), ifn (by omega),
        coeffAt_congr (bytes_frame hI.frame (by simpa using hp.2.2.1.symm) (by decide)) (by rw [n_eq]; omega)]
    · rename_i h
      rw [hI.coeff k hk]
      by_cases h' : k < 8 * i
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]
  · exact ⟨by rw [o13.gpr], by rw [o13.gpr]⟩

/-- The whole function, from its precondition. -/
theorem fn_ok (hv : ∀ k < 256, (L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat =
      ((t (polyAt s₀.mem (s₀.gpr .rdi)) (polyAt s₀.mem (s₀.gpr .rsi)))[k]!).val)
    (hc : writesOnly [.rax, .rdi, .rsi, .rcx] (accAvx2 ar) = true)
    (hm : Code.allInstrs (fun i => !loadsMxcsr i) (accAvx2 ar : Prog isa) = true) :
    ∃ tr s', Exec isa (accAvx2 ar) s₀ tr s' ∧ abiPreserved s₀ s' ∧ (accK t).post s₀ s' := by
  have hW : WP isa (accAvx2 ar) s₀ fun s' =>
      Frame [pR (s₀.gpr .rdi)] s₀.mem s'.mem ∧ ∀ k < 256, coeffAt s'.mem (s₀.gpr .rdi) k =
        L (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k) := by
    refine WP.seq (WP.mono (yconst_ok .xmm15 _ s₀) fun w ⟨lq, k1, m1, _, _⟩ => ?_)
    refine WP.seq (WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide) _ (fun u o hy _ =>
      ⟨by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm,
        by rw [o.keep.gpr (by decide), k1.gpr (by decide), Nat.mul_zero]; exact (BitVec.add_zero _).symm,
        by rw [o.keep.2.1, k1.2.1], by rw [o.keep.2.2, k1.2.2],
        fun l hl => by
          rw [show u.lane .xmm15 l = w.lane .xmm15 l by simp only [State.lane]; rw [o.xmm, hy], lq l hl]; decide,
        by rw [o.mem, m1]; exact Frame.refl _ _, fun k _ => by rw [o.mem, m1, ifn (by omega)]⟩)
      fun i hi u hI => step hp hF hY hi hI) fun u hI => ?_)
    refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem) (by vrunm; rfl) fun u' hm' => ?_
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

/-! ## The functions -/

theorem addY_correct (s : State) (hs : (accK Spec.MlKem.add).pre s) :
    ∃ t s', Exec isa addAvx2 s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlKem.add).post s s' :=
  YAddSub.fn_ok hs (L := fun a b => cadd32 (a + b - 3329#32)) addArith_ok lane_addArith
    (fun i hi => by
      rw [add_lane (hs.2.2.2.2.2.1 i (by rw [n_eq]; exact hi)) (hs.2.2.2.2.2.2 i (by rw [n_eq]; exact hi)),
        add_get _ _ (by rw [n_eq]; exact hi), val_add,
        polyAt_val hs.2.2.2.2.2.1 (by rw [n_eq]; exact hi), polyAt_val hs.2.2.2.2.2.2 (by rw [n_eq]; exact hi)])
    (by decide +kernel) (by decide +kernel)

theorem subY_correct (s : State) (hs : (accK Spec.MlKem.sub).pre s) :
    ∃ t s', Exec isa subAvx2 s t s' ∧ abiPreserved s s' ∧ (accK Spec.MlKem.sub).post s s' :=
  YAddSub.fn_ok hs (L := fun a b => cadd32 (a - b)) subArith_ok lane_subArith
    (fun i hi => by
      rw [sub_lane (hs.2.2.2.2.2.1 i (by rw [n_eq]; exact hi)) (hs.2.2.2.2.2.2 i (by rw [n_eq]; exact hi)),
        sub_get _ _ (by rw [n_eq]; exact hi), val_sub,
        polyAt_val hs.2.2.2.2.2.1 (by rw [n_eq]; exact hi), polyAt_val hs.2.2.2.2.2.2 (by rw [n_eq]; exact hi)])
    (by decide +kernel) (by decide +kernel)

theorem addY_ct : ConstantTime isa (accK Spec.MlKem.add).pre (accK Spec.MlKem.add).pub addAvx2 :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

theorem subY_ct : ConstantTime isa (accK Spec.MlKem.sub).pre (accK Spec.MlKem.sub).pub subAvx2 :=
  VG.Taint.constantTime (A := taint) accτ acc_agree (by taint_decide)

theorem addY_verified : Verified X86_64.target addAvx2 (Spec.MlKem.addContract X86_64.abi) :=
  Verified.of_correct addY_correct addY_ct (by
    mlkem_implies [Spec.MlKem.addContract, Spec.MlKem.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using accSat)

theorem subY_verified : Verified X86_64.target subAvx2 (Spec.MlKem.subContract X86_64.abi) :=
  Verified.of_correct subY_correct subY_ct (by
    mlkem_implies [Spec.MlKem.subContract, Spec.MlKem.accSig, accK, X86_64.abi, X86_64.argRegs]
      [accSat] using accSat)

end VG.Proof.MlKem.X86_64
