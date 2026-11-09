module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on x86-64: pieces of the layers of the NTT and its inverse with `len` = 2 and 1 on AVX2 registers

Each iteration of these layers (`ybody21`, `LazyLay21.lean`) loads sixteen
coefficients, from `j`, into `ymm0` and `ymm1` (or `ymm2`), and in each lane
`l` runs `vlay2`'s or `vlay1`'s gathering (`gath2_ok`, `gath1_ok`),
butterflies and interleaving back (`scat2_ok`, `scat1_ok`) on the four
coefficients from `j + 4l` and the four from `j + 8 + 4l`, with the zetas of
their blocks in lane `l` of `ymm13` (`yzeta8_ok`, `yzeta8R_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly XKeep YOnly ylanes yld_ok ifp ifn sel sel_lt add_ofNat_zero GOnly
  addR_ok wp_rcxLoopY wp_cons_iff lane_setReg lane_setFlags State.setMem_ymm State.setMem_setMem q256lo q256hi
  lo4 hi4)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq zetas)
open VG.Proof.MlDsa (coeffAt polyAt PolyIs)

/-! ## An iteration -/

/-- The body of the loop of the layers with `len` = 2 and 1. -/
abbrev ybody21 (r2 : XReg) (zl core : List Instr) (dz : BitVec 32) : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdx 0)] ++ ([.vmovdquLoad .l256 r2 (at_ .rdx 32)] ++ (zl ++
    ([.alu .add .r8 (.imm dz)] ++ (toY core ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1, .alu .add .rdx (.imm 64),
      .alu .sub .rcx (.imm 1)]))))

/-! ## The gatherings, the butterflies and the interleavings back of a lane -/

theorem gath2_ok (t : State) :
    WP isa (.block gath2) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (t.xmm .xmm0) (t.xmm .xmm1) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (t.xmm .xmm0) (t.xmm .xmm1)) ∧ XOnly [.xmm2, .xmm0, .xmm1] t t' := by
  simp only [gath2, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem scat2_ok (t : State) :
    WP isa (.block scat2) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (t.xmm .xmm0) (t.xmm .xmm3) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (t.xmm .xmm0) (t.xmm .xmm3)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [scat2, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem gath1_ok (t : State) :
    WP isa (.block gath1) t fun t' =>
      (t'.xmm .xmm0 = XBinOp.eval .punpcklqdq (shufDwords (t.xmm .xmm0) 0xD8) (shufDwords (t.xmm .xmm2) 0xD8) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhqdq (shufDwords (t.xmm .xmm0) 0xD8) (shufDwords (t.xmm .xmm2) 0xD8)) ∧
        XOnly [.xmm0, .xmm2, .xmm1] t t' := by
  simp only [gath1, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

theorem scat1_ok (t : State) :
    WP isa (.block scat1) t fun t' => (t'.xmm .xmm0 = XBinOp.eval .punpckldq (t.xmm .xmm0) (t.xmm .xmm3) ∧
      t'.xmm .xmm1 = XBinOp.eval .punpckhdq (t.xmm .xmm0) (t.xmm .xmm3)) ∧ XOnly [.xmm1, .xmm0] t t' := by
  simp only [scat1, xmov, xb]
  vrun [eval_movdqa]
  exact ⟨by first | trivial | simp, by xonly⟩

/-! ## The zetas of the layer with `len = 1` -/

/-- A doubleword of four of the zetas, at index `i` of the table. -/
theorem dword_tab {m : Mem} {zP : Addr} (ht : Tab zmTab m zP 256) {j e i : Nat} (he : e < 4) (hi : j + e = i)
    (hi' : i < 256) : (dword (m.readW (coeffAddr zP j) 128) e).toNat = (zetas i).val * 2 ^ 32 % q := by
  subst hi; rw [dword_readW _ _ he, coeffAddr_add]; exact tab_zeta ht hi'

/-- `vpermq` with `0x27`: lane 0 is `punpckhqdq` of the upper and the lower lane, lane 1 their `punpcklqdq`. -/
theorem perm27 (a b : BitVec 128) :
    permQwords (b ++ a) 0x27 = qword256 (b ++ a) 0 ++ qword256 (b ++ a) (2 + 0) ++
      qword256 (b ++ a) 1 ++ qword256 (b ++ a) (2 + 1) := rfl

theorem perm27_lo (a b : BitVec 128) :
    (permQwords (b ++ a) 0x27).extractLsb' 0 128 = XBinOp.eval .punpckhqdq b a := by
  rw [perm27, q256hi, q256hi, q256lo _ _ (by decide), q256lo _ _ (by decide), lo4]; rfl

theorem perm27_hi (a b : BitVec 128) :
    (permQwords (b ++ a) 0x27).extractLsb' 128 128 = XBinOp.eval .punpcklqdq b a := by
  rw [perm27, q256hi, q256hi, q256lo _ _ (by decide), q256lo _ _ (by decide), hi4]; rfl

/-- `vpermq d, r, 0x27`. -/
theorem ypermq27_ok {d r : XReg} (s : State) :
    WP isa (.block [.vop (.vpermq d r 0x27)]) s fun s' =>
      s'.lane d 0 = XBinOp.eval .punpckhqdq (s.lane r 1) (s.lane r 0) ∧
      s'.lane d 1 = XBinOp.eval .punpcklqdq (s.lane r 1) (s.lane r 0) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r' hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl, ifp rfl, State.ymm_eq, perm27_lo]
  · rw [State.lane_setV256, ifp rfl, ifn (by decide), State.ymm_eq, perm27_hi]
  · rw [State.lane_setV256, ifn (by simpa using hr)]

/-- The eight zetas at index `k` of the table, in the order of the blocks of
`ylay1` for `NTT`: in lane `l`, zetas `k + 2l`, `k + 2l + 1`, `k + 2l + 4`
and `k + 2l + 5`. -/
theorem yzeta8_ok {zP : Addr} {k : Nat} (hk : k + 8 ≤ 256) {s : State} (h8 : s.gpr .r8 = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 32) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block yzeta8) s fun s' =>
      (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun e => zetas (k + (2 * l + e + 2 * (e / 2)))) ∧
        ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm12] s s' := by
  rw [yzeta8, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (yld_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.ypermq_ok s1) fun s2 ⟨e0, e1, o2⟩ => ?_
  refine WP.mono (yF5_ok s2) fun s3 ⟨f3, o3⟩ => ⟨fun l hl => ?_, ((o1.trans o2).trans o3).mono (by simp)⟩
  rw [f3 l hl, o3.lane _ (by decide) l hl]
  refine ⟨fun e he => ?_, zodd_F5 _⟩
  have a : ∀ l < 2, s1.lane .xmm13 l = s.mem.readW (coeffAddr zP (k + 4 * l)) 128 := fun l hl => by
    rw [L1 l hl, h8, add_ofNat_zero, lane_load]
  rcases lane01 hl with rfl | rfl
  · rw [e0, dword_punpcklqdq _ _ he, a 0 (by decide), a 1 (by decide)]
    split
    · exact dword_tab ht he (by omega_arith) (by omega_arith)
    · exact dword_tab ht (by omega_arith) (by omega_arith) (by omega_arith)
  · rw [e1, dword_punpckhqdq _ _ he, a 0 (by decide), a 1 (by decide)]
    split
    · exact dword_tab ht (by omega_arith) (by omega_arith) (by omega_arith)
    · exact dword_tab ht he (by omega_arith) (by omega_arith)

theorem dword_b1 (x : BitVec 128) {e : Nat} (he : e < 4) :
    dword (shufDwords x 0xB1) e = dword x (if e % 2 = 0 then e + 1 else e - 1) := by
  rw [dword_shufDwords _ _ he]
  rcases cases4 he with rfl | rfl | rfl | rfl <;> rfl

theorem zsseR_ok (t : State) :
    WP isa (.block [.xop (.pshufd .xmm13 .xmm13 0xB1), .xop (.pshufd .xmm12 .xmm13 0xF5)]) t fun t' =>
      (t'.xmm .xmm13 = shufDwords (t.xmm .xmm13) 0xB1 ∧
        t'.xmm .xmm12 = shufDwords (shufDwords (t.xmm .xmm13) 0xB1) 0xF5) ∧ XOnly [.xmm13, .xmm12] t t' := by
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

/-- The eight zetas at index `k` of the table, in the order of the blocks of
`ylay1` for `NTT⁻¹`, which take them in decreasing order: in lane `l`, zetas
`k + 7 - 2l`, `k + 6 - 2l`, `k + 3 - 2l` and `k + 2 - 2l`. -/
theorem yzeta8R_ok {zP : Addr} {k : Nat} (hk : k + 8 ≤ 256) {s : State} (h8 : s.gpr .r8 = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 32) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block yzeta8R) s fun s' =>
      (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun e => zetas (k + 7 - (2 * l + e + 2 * (e / 2)))) ∧
        ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm12] s s' := by
  rw [yzeta8R, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (yld_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (ypermq27_ok s1) fun s2 ⟨e0, e1, o2⟩ => ?_
  refine WP.mono (ylanes (by decide) (P := fun l t => t.xmm .xmm13 = shufDwords (s2.lane .xmm13 l) 0xB1 ∧
      t.xmm .xmm12 = shufDwords (shufDwords (s2.lane .xmm13 l) 0xB1) 0xF5)
    fun l _ => zsseR_ok (s2.proj l)) fun s3 ⟨l3, o3⟩ => ⟨fun l hl => ?_, ((o1.trans o2).trans o3).mono (by simp)⟩
  have e13 : s3.lane .xmm13 l = _ := (l3 l hl).1
  have e12 : s3.lane .xmm12 l = _ := (l3 l hl).2
  rw [e12, e13]
  refine ⟨fun e he => ?_, zodd_F5 _⟩
  have a : ∀ l < 2, s1.lane .xmm13 l = s.mem.readW (coeffAddr zP (k + 4 * l)) 128 := fun l hl => by
    rw [L1 l hl, h8, add_ofNat_zero, lane_load]
  have he' : (if e % 2 = 0 then e + 1 else e - 1) < 4 := by split <;> omega_arith
  rw [dword_b1 _ he]
  generalize hf : (if e % 2 = 0 then e + 1 else e - 1) = f at he'
  have hf' : f = if e % 2 = 0 then e + 1 else e - 1 := hf.symm
  rcases lane01 hl with rfl | rfl
  · rw [e0, dword_punpckhqdq _ _ he', a 0 (by decide), a 1 (by decide)]
    split
    · exact dword_tab ht (by omega_arith) (by split at hf' <;> omega_arith) (by omega_arith)
    · exact dword_tab ht he' (by split at hf' <;> omega_arith) (by omega_arith)
  · rw [e1, dword_punpcklqdq _ _ he', a 0 (by decide), a 1 (by decide)]
    split
    · exact dword_tab ht he' (by split at hf' <;> omega_arith) (by omega_arith)
    · exact dword_tab ht (by omega_arith) (by split at hf' <;> omega_arith) (by omega_arith)

end VG.Proof.MlDsa.X86_64.Arith
