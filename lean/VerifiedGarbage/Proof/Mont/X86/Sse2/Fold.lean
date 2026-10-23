module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Input
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

/-! # A column's sums folded

`fold` adds each sum's two lanes, stores the column's sum modulo `2⁶⁴` at
`S` and its high words' sum `H` at `S + 8`, and adds the carry at `S + 16`:
`edx:eax = (P + c) mod 2⁶⁴` (`fold_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.X86.RegUpd VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt

/-! ## Scalar instructions, keeping `mcdt` and the XMM registers -/

section
variable {s : State} {is : List Instr} {Q : State → Prop}

theorem wp_adcX {d : Reg} {src : Src} {v : BitVec 32} {c : Bool} (h : readSrc s src = some v)
    (hc : s.cf = some c)
    (k : ∀ t, Upd s t d (s.gpr d + v + (BitVec.ofBool c).setWidth 32) →
      t.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat + c.toNat)) → t.mcdt = s.mcdt → t.xmm = s.xmm →
      WP isa (.block is) t Q) :
    WP isa (.block (.alu .adc d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some, hc, Option.map_some]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _) rfl rfl rfl)

theorem wp_storeX {r : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hw : InRegions s.wr a 4)
    (k : ∀ t, Mupd s t (s.mem.writeW a (s.gpr r)) → t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.store m r :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) (by simp only [exec, ha, State.store32, hw, ite_true])
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem wp_movqStoreX {x : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hw : InRegions s.wr a 8)
    (k : ∀ t, Mupd s t (s.mem.writeW a (qword (s.xmm x) 0)) → t.mcdt = s.mcdt → t.xmm = s.xmm →
      WP isa (.block is) t Q) :
    WP isa (.block (.movqStore m x :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a (qword (s.xmm x) 0) })
    (by simp only [exec, ha, State.store64, hw, ite_true]; rfl) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl)

theorem wp_movC {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d v → t.cf = s.cf → t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.mov d src :: is)) s Q :=
  cons (s' := s.setReg d v) (by simp only [exec, h, Option.map_some]) (k _ (Upd.setReg _ _ _) rfl rfl rfl)

theorem wp_mulX {r : Reg} (k : ∀ t, MulUpd s t r → t.mcdt = s.mcdt → t.xmm = s.xmm → WP isa (.block is) t Q) :
    WP isa (.block (.mul r :: is)) s Q := by
  refine cons (s' := execMul r s) rfl (k _ ⟨?_, ?_, fun q h1 h2 => ?_, rfl, rfl, rfl⟩ rfl rfl)
  · simp only [execMul, State.setReg, reduceCtorEq, ite_false, ite_true]
  · simp only [execMul, State.setReg, ite_true]
  · simp only [execMul, State.setReg, State.setFlags, h1, h2, ite_false]

end

/-! ## Words of the scratch -/

/-- An 8-byte store's two words. -/
theorem w32_write64 (m : Mem) (W : Addr) (d : Nat) (v : BitVec 64) :
    w32 (m.writeW (off W d) v) W d + 2 ^ 32 * w32 (m.writeW (off W d) v) W (d + 4) = v.toNat := by
  rw [← word_eq_w32, word, Mem.readW_writeW_self64]

theorem movdqa_eval (a b : BitVec 128) : XBinOp.eval .movdqa a b = b := rfl

theorem fold_lane (x : BitVec 128) :
    qword (XBinOp.eval .paddq x (XShiftOp.eval .psrldq x 8)) 0 = qword x 0 + qword x 1 := by
  rw [qword_paddq _ _ (by decide), qword_psrldq_0]

/-- The sums' lanes added: `fold`'s SSE instructions. -/
theorem lanes_run (s : State) :
    ∃ t, runBlock isa [.xop (.bin .movdqa .xmm2 .xmm0), .xop (.shift .psrldq .xmm2 8),
      .xop (.bin .paddq .xmm0 .xmm2), .xop (.bin .movdqa .xmm2 .xmm1), .xop (.shift .psrldq .xmm2 8),
      .xop (.bin .paddq .xmm1 .xmm2)] s = some t ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mcdt = s.mcdt ∧
      qword (t.xmm .xmm0) 0 = qword (s.xmm .xmm0) 0 + qword (s.xmm .xmm0) 1 ∧
      qword (t.xmm .xmm1) 0 = qword (s.xmm .xmm1) 0 + qword (s.xmm .xmm1) 1 := by
  simp only [runBlock_cons, exec, runStep_some, runBlock_nil, XOp.exec, Option.some.injEq, exists_eq_left',
    xmm_setXmm, reduceCtorEq, ↓reduceIte, movdqa_eval, fold_lane, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm,
    mcdt_setXmm]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- `add` then `adc` of two-word numbers. -/
theorem add64_words (x0 x1 y0 y1 : BitVec 32) :
    (x0 + y0).toNat + 2 ^ 32 * (x1 + y1 + (BitVec.ofBool (decide (2 ^ 32 ≤ x0.toNat + y0.toNat))).setWidth 32).toNat =
      (x0.toNat + 2 ^ 32 * x1.toNat + (y0.toNat + 2 ^ 32 * y1.toNat)) % 2 ^ 64 := by
  rw [add3_toNat, BitVec.toNat_add]
  have := x0.isLt
  have := x1.isLt
  have := y0.isLt
  have := y1.isLt
  by_cases h : 2 ^ 32 ≤ x0.toNat + y0.toNat
  · simp only [h, decide_true, Bool.toNat_true]; omega
  · simp only [h, decide_false, Bool.toNat_false]; omega

/-- `fold`: the lanes added and stored, the column's sum `P` modulo `2⁶⁴` at
`S` and `H` at `S + 8`, and `edx:eax = (P + c) mod 2⁶⁴` for the carry `c`
at `S + 16`. -/
theorem fold_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S P H n c : Nat}
    (C : ColEnv t W L V N k) (hS : (V pS).toNat = (W.toNat + S) % 2 ^ 32) (hs : S + 24 ≤ L)
    (A : Acc (t.xmm .xmm0) (t.xmm .xmm1) P H n) (hH : H < 2 ^ 64)
    (hc : w32 t.mem W (S + 16) + 2 ^ 32 * w32 t.mem W (S + 20) = c) :
    WP isa (.block fold) t fun u =>
      (u.gpr .eax).toNat + 2 ^ 32 * (u.gpr .edx).toNat = (P + c) % 2 ^ 64 ∧ PtrAt u W .ebx S ∧
      w32 u.mem W (S + 8) + 2 ^ 32 * w32 u.mem W (S + 12) = H ∧
      w32 u.mem W (S + 16) + 2 ^ 32 * w32 u.mem W (S + 20) = c ∧
      Outs W [(S, 16)] t.mem u.mem ∧ Keeps [.eax, .ebx, .edx] t u ∧ u.mcdt = t.mcdt := by
  have hn := C.ws.nowrap
  obtain ⟨v, run, g, m, rd, wr, mc, q0, q1⟩ := lanes_run t
  rw [show fold = [.xop (.bin .movdqa .xmm2 .xmm0), .xop (.shift .psrldq .xmm2 8),
      .xop (.bin .paddq .xmm0 .xmm2), .xop (.bin .movdqa .xmm2 .xmm1), .xop (.shift .psrldq .xmm2 8),
      .xop (.bin .paddq .xmm1 .xmm2)] ++ [.mov .ebx (.mem (kp pS)), .movqStore (at_ .ebx 0) .xmm0,
      .movqStore (at_ .ebx 8) .xmm1, .mov .eax (.mem (at_ .ebx 0)), .alu .add .eax (.mem (at_ .ebx 16)),
      .mov .edx (.mem (at_ .ebx 4)), .alu .adc .edx (.mem (at_ .ebx 20))] from rfl]
  refine WP.block_append (WP.of_runBlock ⟨v, run, ?_⟩)
  have Kv : Keeps [] t v := ⟨fun r _ => by rw [g], rd, wr⟩
  have Cv := C.of_keeps Kv m mc
  refine wp_movX (Cv.prm.read pS (by decide)) fun t1 u1 m1 x1 => ?_
  have p1 : PtrAt t1 W .ebx S := ptr_of_param u1.gpr hS
  have hw1 : Ws t1 W L := Cv.ws.of_keeps u1.keeps
  refine wp_movqStoreX (by rw [ea_ptr hw1 p1 (by omega), Nat.add_zero]) (ws_write hw1 (y := S) (n := 8) (by omega))
    fun t2 M2 m2 x2 => ?_
  have p2 : PtrAt t2 W .ebx S := by rw [PtrAt, M2.gpr]; exact p1
  have hw2 : Ws t2 W L := hw1.of_wr M2.wr
  refine wp_movqStoreX (ea_ptr hw2 p2 (by omega)) (ws_write hw2 (y := S + 8) (n := 8) (by omega))
    fun t3 M3 m3 x3 => ?_
  have p3 : PtrAt t3 W .ebx S := by rw [PtrAt, M3.gpr]; exact p2
  have hw3 : Ws t3 W L := hw2.of_wr M3.wr
  refine wp_movX (readSrc_ptr hw3 p3 (d := 0) (by omega)) fun t4 u4 m4 x4 => ?_
  have p4 : PtrAt t4 W .ebx S := by rw [PtrAt, u4.other _ (by decide)]; exact p3
  have hw4 : Ws t4 W L := hw3.of_keeps u4.keeps
  refine wp_addX (readSrc_ptr hw4 p4 (d := 16) (by omega)) fun t5 u5 c5 m5 x5 => ?_
  have p5 : PtrAt t5 W .ebx S := by rw [PtrAt, u5.other _ (by decide)]; exact p4
  have hw5 : Ws t5 W L := hw4.of_keeps u5.keeps
  refine wp_movC (readSrc_ptr hw5 p5 (d := 4) (by omega)) fun t6 u6 f6 m6 x6 => ?_
  have p6 : PtrAt t6 W .ebx S := by rw [PtrAt, u6.other _ (by decide)]; exact p5
  have hw6 : Ws t6 W L := hw5.of_keeps u6.keeps
  refine wp_adcX (readSrc_ptr hw6 p6 (d := 20) (by omega)) (by rw [f6, c5])
    fun t7 u7 c7 m7 x7 => WP.block_nil ?_
  have hP : qword (v.xmm .xmm0) 0 = BitVec.ofNat 64 P := by rw [q0, A.sums.low]
  have hHv : (qword (v.xmm .xmm1) 0).toNat = H := by
    rw [q1, BitVec.toNat_add, A.sums.high, Nat.mod_eq_of_lt hH]
  have mem2 : t2.mem = t.mem.writeW (off W S) (BitVec.ofNat 64 P) := by
    rw [M2.mem, x1, hP, u1.mem, m]
  have mem3 : t3.mem = t2.mem.writeW (off W (S + 8)) (qword (v.xmm .xmm1) 0) := by rw [M3.mem, x2, x1]
  have O2 : Outside W S 8 t.mem t2.mem := by rw [mem2]; exact writeW_outside _ _ _ (by omega)
  have O3 : Outside W (S + 8) 8 t2.mem t3.mem := by rw [mem3]; exact writeW_outside _ _ _ (by omega)
  have mem7 : t7.mem = t3.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem]
  have lo : w32 t3.mem W S + 2 ^ 32 * w32 t3.mem W (S + 4) = P % 2 ^ 64 := by
    rw [O3.w32 (by omega) (by omega), O3.w32 (by omega) (by omega), mem2, w32_write64, BitVec.toNat_ofNat]
  have hi : w32 t3.mem W (S + 8) + 2 ^ 32 * w32 t3.mem W (S + 12) = H := by
    rw [mem3, w32_write64, hHv]
  have cc : w32 t3.mem W (S + 16) + 2 ^ 32 * w32 t3.mem W (S + 20) = c := by
    rw [O3.w32 (by omega) (by omega), O3.w32 (by omega) (by omega), O2.w32 (by omega) (by omega),
      O2.w32 (by omega) (by omega), hc]
  refine ⟨?_, ?_, by rw [mem7]; exact hi, by rw [mem7]; exact cc, ?_, ?_, by rw [m7, m6, m5, m4, m3, m2, m1, mc]⟩
  · rw [u7.other _ (by decide), u7.gpr, u6.gpr, u6.other _ (by decide), u5.gpr, u4.gpr, add64_words]
    simp only [u6.mem, u5.mem, u4.mem, Nat.add_zero] at lo cc ⊢
    simp only [w32] at lo cc
    rw [lo, cc]
    omega
  · rw [PtrAt, u7.other _ (by decide)]; exact p6
  · rw [mem7]
    exact (Outs.of_outside (O2.mono (by omega) (by omega)) (List.mem_singleton_self _)).trans
      (Outs.of_outside (O3.mono (by omega) (by omega)) (List.mem_singleton_self _))
  · refine ⟨fun r hr => ?_, by rw [u7.rd, u6.rd, u5.rd, u4.rd, M3.rd, M2.rd, u1.rd, rd],
      by rw [u7.wr, u6.wr, u5.wr, u4.wr, M3.wr, M2.wr, u1.wr, wr]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u7.other _ hr.2.2, u6.other _ hr.2.2, u5.other _ hr.1, u4.other _ hr.1, M3.gpr, M2.gpr, u1.other _ hr.2.1, g]

/-! ## The column's digit -/

/-- `adc` of a word, its carry from an `add`. -/
theorem add_adc (x0 y0 x1 y1 : BitVec 32) :
    (x0 + y0).toNat + 2 ^ 32 * (x1 + y1 + (BitVec.ofBool (decide (2 ^ 32 ≤ x0.toNat + y0.toNat))).setWidth 32).toNat =
      (x0.toNat + y0.toNat + 2 ^ 32 * (x1.toNat + y1.toNat)) % 2 ^ 64 := by
  rw [add64_words]; congr 1; omega

/-- `k < N`: the digit `q = Z_lo (-M⁻¹) mod 2³²` stored at word `k`, `q M_0`
added to `Z` (`edx` its high word) and its high word to `H` at `S + 8`. -/
theorem digit_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S mo inv Z H : Nat}
    (hw : Ws t W L) (P : Params t W L V 12) (hcx : t.gpr .ecx = BitVec.ofNat 32 (4 * k)) (hkN : k < N)
    (hM : (V pM).toNat = (W.toNat + mo) % 2 ^ 32) (hI : (V pInv).toNat = (W.toNat + inv) % 2 ^ 32)
    (hs : S + 24 + 4 * N ≤ L) (hm : mo + 4 ≤ L) (hi : inv + 4 ≤ L)
    (sep : mo + 4 ≤ S + 24 + 4 * k ∨ S + 24 + 4 * k + 4 ≤ mo)
    (hb : PtrAt t W .ebx S) (hz : (t.gpr .eax).toNat + 2 ^ 32 * (t.gpr .edx).toNat = Z)
    (hH : w32 t.mem W (S + 8) + 2 ^ 32 * w32 t.mem W (S + 12) = H) :
    WP isa (.block digit) t fun u =>
      (u.gpr .edx).toNat = (Z + (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 * w32 t.mem W mo) % 2 ^ 64 / 2 ^ 32 ∧
      w32 u.mem W (S + 24 + 4 * k) = (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 ∧
      w32 u.mem W (S + 8) + 2 ^ 32 * w32 u.mem W (S + 12) =
        (H + (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 * w32 t.mem W mo / 2 ^ 32) % 2 ^ 64 ∧
      Outs W [(S + 8, 8), (S + 24 + 4 * k, 4)] t.mem u.mem ∧
      Keeps [.eax, .edx, .esi, .edi] t u ∧ u.mcdt = t.mcdt := by
  have hn := hw.nowrap
  unfold digit
  simp only [offW, offH]
  refine wp_movX rfl fun t1 u1 m1 x1 => wp_movX rfl fun t2 u2 m2 x2 => ?_
  have K2 : Sk [.eax, .edx, .esi, .edi] t t2 :=
    (Sk.of_upd [.eax, .edx, .esi, .edi] u1 m1 x1).trans (Sk.of_upd [.edi] u2 m2 x2)
  refine wp_movX (P.readSk K2 (i := pInv) (by decide)) fun t3 u3 m3 x3 => ?_
  have K3 := K2.trans (Sk.of_upd [.edx] u3 m3 x3)
  have hw3 := hw.of_keeps K3.keep
  refine wp_movX (readSrc_ptr hw3 (ptr_of_param u3.gpr hI) (d := 0) (by omega)) fun t4 u4 m4 x4 => ?_
  have K4 := K3.trans (Sk.of_upd [.edx] u4 m4 x4)
  refine wp_mulX fun t5 u5 m5 x5 => ?_
  have K5 : Sk [.eax, .edx, .esi, .edi] t t5 := K4.trans ⟨u5.keeps, u5.mem, m5, x5⟩
  refine wp_movX rfl fun t6 u6 m6 x6 => wp_addX rfl fun t7 u7 _ m7 x7 => ?_
  have K7 := (K5.trans (Sk.of_upd [.edx] u6 m6 x6)).trans (Sk.of_upd [.edx] u7 m7 x7)
  have hw7 := hw.of_keeps K7.keep
  have p7 : PtrAt t7 W .edx (S + 4 * k) := by
    have := (t.gpr .ebx).isLt
    rw [PtrAt, u7.gpr, u6.gpr, u6.other _ (by decide), K5.keep.1 _ (by decide), K5.keep.1 _ (by decide),
      BitVec.toNat_add, hb, hcx, toNat_ofNat_lt (by omega)]
    omega
  refine wp_storeX (ea_ptr hw7 p7 (by omega)) (ws_write hw7 (y := S + 4 * k + 24) (n := 4) (by omega))
    fun t8 M8 m8 x8 => ?_
  have O8 : Outside W (S + 24 + 4 * k) 4 t.mem t8.mem := by
    rw [M8.mem, K7.mem, show S + 4 * k + 24 = S + 24 + 4 * k by omega]; exact writeW32_outside _ _ _ (by omega)
  have Ot8 : Outs W [(0, L)] t.mem t8.mem := Outs.of_outside (O8.mono (by omega) (by omega)) (List.mem_singleton_self _)
  have K8k : Keeps [.eax, .edx, .esi, .edi] t t8 := K7.keep.trans (M8.keeps _)
  have P8 : Params t8 W L V 12 := P.keep Ot8 (K8k.1 _ (by decide)) K8k.2.1 K8k.2.2
  have hw8 := hw.of_keeps K8k
  refine wp_movX (P8.read pM (by decide)) fun t9 u9 m9 x9 => ?_
  have hw9 := hw8.of_keeps u9.keeps
  refine wp_movX (readSrc_ptr hw9 (ptr_of_param u9.gpr hM) (d := 0) (by omega)) fun t10 u10 m10 x10 => ?_
  refine wp_mulX fun t11 u11 m11 x11 => wp_addX rfl fun t12 u12 c12 m12 x12 => ?_
  refine wp_adcX rfl c12 fun t13 u13 _ m13 x13 => ?_
  have K13 : Keeps [.eax, .edx, .esi, .edi] t t13 :=
    ((((K8k.widen u9.keeps).widen u10.keeps).widen u11.keeps).widen u12.keeps).widen u13.keeps
  have hw13 := hw.of_keeps K13
  have b13 : PtrAt t13 W .ebx S := by rw [PtrAt, K13.1 _ (by decide)]; exact hb
  have mem13 : t13.mem = t8.mem := by rw [u13.mem, u12.mem, u11.mem, u10.mem, u9.mem]
  refine wp_movC (readSrc_ptr hw13 b13 (d := 8) (by omega)) fun t14 u14 f14 m14 x14 =>
    wp_addX rfl fun t15 u15 c15 m15 x15 => ?_
  have K15 : Keeps [.eax, .edx, .esi, .edi] t t15 := (K13.widen u14.keeps).widen u15.keeps
  have hw15 := hw.of_keeps K15
  have b15 : PtrAt t15 W .ebx S := by rw [PtrAt, K15.1 _ (by decide)]; exact hb
  refine wp_storeX (ea_ptr hw15 b15 (d := 8) (by omega)) (ws_write hw15 (y := S + 8) (n := 4) (by omega))
    fun t16 M16 m16 x16 => ?_
  have hw16 := hw15.of_wr M16.wr
  have b16 : PtrAt t16 W .ebx S := by rw [PtrAt, M16.gpr]; exact b15
  refine wp_movC (readSrc_ptr hw16 b16 (d := 12) (by omega)) fun t17 u17 f17 m17 x17 =>
    wp_adcX rfl (by rw [f17, M16.cf, c15]) fun t18 u18 _ m18 x18 => ?_
  have K18 : Keeps [.eax, .edx, .esi, .edi] t t18 := ((K15.widen (M16.keeps [])).widen u17.keeps).widen u18.keeps
  have hw18 := hw.of_keeps K18
  have b18 : PtrAt t18 W .ebx S := by rw [PtrAt, K18.1 _ (by decide)]; exact hb
  refine wp_storeX (ea_ptr hw18 b18 (d := 12) (by omega)) (ws_write hw18 (y := S + 12) (n := 4) (by omega))
    fun t19 M19 m19 x19 => wp_movX rfl fun t20 u20 m20 x20 => WP.block_nil ?_
  -- The values.
  have ezl : (t.gpr .eax).toNat = Z % 2 ^ 32 := by have := (t.gpr .eax).isLt; omega
  have iv : (t4.gpr .edx).toNat = w32 t.mem W inv := by
    rw [u4.gpr, K3.mem, Nat.add_zero]
  have q5 : (t5.gpr .eax).toNat = (Z % 2 ^ 32 * w32 t.mem W inv) % 2 ^ 32 := by
    rw [u5.eax, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide),
      BitVec.toNat_ofNat, ezl, iv]
  have m0 : (t10.gpr .edx).toNat = w32 t.mem W mo := by
    rw [u10.gpr, u9.mem, M8.mem]
    simp only [Nat.add_zero]
    have := O8.w32 (d := mo) (by omega) (by omega)
    rw [M8.mem] at this
    simp only [w32] at this
    rw [this]
  have e11 : t10.gpr .eax = t5.gpr .eax := by
    rw [u10.other _ (by decide), u9.other _ (by decide), M8.gpr, u7.other _ (by decide), u6.other _ (by decide)]
  have mw := mul_words (t10.gpr .eax) (t10.gpr .edx)
  rw [← u11.eax, ← u11.edx] at mw
  have zl12 : t11.gpr .edi = t.gpr .eax := by
    rw [u11.other _ (by decide) (by decide), u10.other _ (by decide), u9.other _ (by decide), M8.gpr,
      u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide) (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, u1.other _ (by decide)]
  have zh12 : t12.gpr .esi = t.gpr .edx := by
    rw [u12.other _ (by decide), u11.other _ (by decide) (by decide), u10.other _ (by decide),
      u9.other _ (by decide), M8.gpr, u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide) (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.gpr]
  have hi12 : t12.gpr .edx = t11.gpr .edx := u12.other _ (by decide)
  have sum := add_adc (t11.gpr .eax) (t11.gpr .edi) (t12.gpr .esi) (t12.gpr .edx)
  rw [← u12.gpr, ← u13.gpr] at sum
  rw [zl12, zh12, hi12] at sum
  rw [e11] at mw
  have q10 : (t10.gpr .edx).toNat = w32 t.mem W mo := m0
  rw [q5, q10] at mw
  -- Memory.
  have mem8 : t8.mem = t.mem.writeW (off W (S + 24 + 4 * k)) (t5.gpr .eax) := by
    rw [M8.mem, K7.mem, u7.other _ (by decide), u6.other _ (by decide), show S + 4 * k + 24 = S + 24 + 4 * k by omega]
  have mem16 : t16.mem = t8.mem.writeW (off W (S + 8)) (t15.gpr .eax) := by
    rw [M16.mem, u15.mem, u14.mem, mem13]
  have mem20 : t20.mem = t16.mem.writeW (off W (S + 12)) (t18.gpr .eax) := by
    rw [u20.mem, M19.mem, u18.mem, u17.mem]
  have esi20 : t20.gpr .edx = t13.gpr .esi := by
    rw [u20.gpr, M19.gpr, u18.other _ (by decide), u17.other _ (by decide), M16.gpr, u15.other _ (by decide),
      u14.other _ (by decide)]
  have hlo : (t14.gpr .eax).toNat = w32 t.mem W (S + 8) := by
    rw [u14.gpr, mem13, mem8]
    exact w32_write_ne (size := L) (o := S + 24 + 4 * k) (d := S + 8) hn (by omega) (by omega) (by omega) _
  have hhi : (t17.gpr .eax).toNat = w32 t.mem W (S + 12) := by
    rw [u17.gpr, mem16, mem8]
    exact (w32_write_ne (size := L) (o := S + 8) (d := S + 12) hn (by omega) (by omega) (by omega) _).trans
      (w32_write_ne (size := L) (o := S + 24 + 4 * k) (d := S + 12) hn (by omega) (by omega) (by omega) _)
  have e14 : t14.gpr .edx = t11.gpr .edx := by
    rw [u14.other _ (by decide), u13.other _ (by decide), hi12]
  have hsum := add_adc (t14.gpr .eax) (t14.gpr .edx) (t17.gpr .eax) 0
  rw [← u15.gpr, ← u18.gpr, hlo, hhi, e14] at hsum
  have hz13 := (t12.gpr .eax).isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [esi20]
    have := mw.1
    omega
  · rw [mem20, w32_write_ne (size := L) (o := S + 12) (d := S + 24 + 4 * k) hn (by omega) (by omega) (by omega),
      mem16, w32_write_ne (size := L) (o := S + 8) (d := S + 24 + 4 * k) hn (by omega) (by omega) (by omega), mem8,
      w32_write_self, q5]
  · rw [mem20, w32_write_ne (size := L) (o := S + 12) (d := S + 8) hn (by omega) (by omega) (by omega),
      w32_write_self, mem16, w32_write_self]
    have := mw.1
    have z0 : (0 : BitVec 32).toNat = 0 := rfl
    rw [z0, Nat.add_zero] at hsum
    omega
  · rw [mem20, mem16]
    have O16 : Outside W (S + 8) 4 t8.mem (t8.mem.writeW (off W (S + 8)) (t15.gpr .eax)) :=
      writeW32_outside _ _ _ (by omega)
    have O20 : Outside W (S + 12) 4 (t8.mem.writeW (off W (S + 8)) (t15.gpr .eax))
        ((t8.mem.writeW (off W (S + 8)) (t15.gpr .eax)).writeW (off W (S + 12)) (t18.gpr .eax)) :=
      writeW32_outside _ _ _ (by omega)
    exact ((Outs.of_outside O8 (by simp)).trans
      (Outs.of_outside (O16.mono (o' := S + 8) (n' := 8) (by omega) (by omega)) (by simp))).trans
      (Outs.of_outside (O20.mono (o' := S + 8) (n' := 8) (by omega) (by omega)) (by simp))
  · exact (K18.widen (M19.keeps [])).widen u20.keeps
  · rw [m20, m19, m18, m17, m16, m15, m14, m13, m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1]

/-- `k ≥ N`: `Z_lo` stored at word `k`. -/
theorem word_ok {t : State} {W : Addr} {L : Nat} {N k S : Nat} (hw : Ws t W L)
    (hcx : t.gpr .ecx = BitVec.ofNat 32 (4 * k)) (hk : k < 2 * N) (hs : S + 24 + 8 * N ≤ L)
    (hb : PtrAt t W .ebx S) :
    WP isa (.block VG.Impl.Mont.X86.Sse2.word) t fun u =>
      w32 u.mem W (S + 24 + 4 * k) = (t.gpr .eax).toNat ∧ Outs W [(S + 24 + 4 * k, 4)] t.mem u.mem ∧
      Keeps [.esi] t u ∧ u.mcdt = t.mcdt := by
  have hn := hw.nowrap
  unfold VG.Impl.Mont.X86.Sse2.word
  simp only [offW]
  refine wp_movX rfl fun t1 u1 m1 x1 => wp_addX rfl fun t2 u2 _ m2 x2 => ?_
  have K2 : Keeps [.esi] t t2 := u1.keeps.widen u2.keeps
  have hw2 := hw.of_keeps K2
  have p2 : PtrAt t2 W .esi (S + 4 * k) := by
    have := (t.gpr .ebx).isLt
    rw [PtrAt, u2.gpr, u1.gpr, u1.other _ (by decide), BitVec.toNat_add, hb, hcx, toNat_ofNat_lt (by omega)]
    omega
  refine wp_storeX (ea_ptr hw2 p2 (by omega)) (ws_write hw2 (y := S + 4 * k + 24) (n := 4) (by omega))
    fun t3 M3 m3 x3 => WP.block_nil ⟨?_, ?_, K2.widen (M3.keeps []), by rw [m3, m2, m1]⟩
  · rw [M3.mem, show S + 4 * k + 24 = S + 24 + 4 * k by omega, w32_write_self, u2.other _ (by decide),
      u1.other _ (by decide)]
  · rw [M3.mem, u2.mem, u1.mem, show S + 4 * k + 24 = S + 24 + 4 * k by omega]
    exact Outs.of_outside (writeW32_outside _ _ _ (by omega)) (by simp)

/-- The carry stored: its low word `edx`, its high word `H_hi + [edx < H_lo]`;
then `ecx` up a word, ZF after the last column. -/
theorem carry_ok {t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k S : Nat} (hw : Ws t W L)
    (P : Params t W L V 12) (hN : (V pN4).toNat = 4 * N) (hcx : t.gpr .ecx = BitVec.ofNat 32 (4 * k))
    (hk : k < 2 * N) (hN28 : N < 2 ^ 29) (hs : S + 24 ≤ L) (hb : PtrAt t W .ebx S) :
    WP isa (.block (carry ++ ([.alu .add .ecx (.imm 4), .mov .eax (.mem (kp pN4)), .alu .add .eax (.reg .eax),
      .alu .cmp .ecx (.reg .eax)] : List Instr))) t fun u =>
      w32 u.mem W (S + 16) = (t.gpr .edx).toNat ∧
      w32 u.mem W (S + 20) = (w32 t.mem W (S + 12) +
        (decide ((t.gpr .edx).toNat < w32 t.mem W (S + 8))).toNat) % 2 ^ 32 ∧
      Outs W [(S + 16, 8)] t.mem u.mem ∧ u.gpr .ecx = BitVec.ofNat 32 (4 * (k + 1)) ∧
      u.zf = some (decide (k + 1 = 2 * N)) ∧ Keeps [.eax, .ecx] t u ∧ u.mcdt = t.mcdt := by
  have hn := hw.nowrap
  simp only [carry, offC, offH, List.cons_append, List.nil_append]
  refine wp_storeX (ea_ptr hw hb (d := 16) (by omega)) (ws_write hw (y := S + 16) (n := 4) (by omega))
    fun t1 M1 m1 x1 => ?_
  have hw1 := hw.of_wr M1.wr
  have b1 : PtrAt t1 W .ebx S := by rw [PtrAt, M1.gpr]; exact hb
  refine wp_cmpX (readSrc_ptr hw1 b1 (d := 8) (by omega)) fun t2 f2 c2 _ m2 x2 => ?_
  have b2 : PtrAt t2 W .ebx S := by rw [PtrAt, f2.gpr]; exact b1
  have hw2 := hw1.of_wr f2.wr
  refine wp_movC (readSrc_ptr hw2 b2 (d := 12) (by omega)) fun t3 u3 f3 m3 x3 =>
    wp_adcX rfl (by rw [f3, c2]) fun t4 u4 _ m4 x4 => ?_
  have K4 : Keeps [.eax] t t4 := (((M1.keeps [.eax]).widen (f2.keeps [])).widen u3.keeps).widen u4.keeps
  have hw4 := hw.of_keeps K4
  have b4 : PtrAt t4 W .ebx S := by rw [PtrAt, K4.1 _ (by decide)]; exact hb
  refine wp_storeX (ea_ptr hw4 b4 (d := 20) (by omega)) (ws_write hw4 (y := S + 20) (n := 4) (by omega))
    fun t5 M5 m5 x5 => ?_
  have K5 : Keeps [.eax] t t5 := K4.widen (M5.keeps [])
  have O1 : Outside W (S + 16) 4 t.mem t1.mem := by rw [M1.mem]; exact writeW32_outside _ _ _ (by omega)
  have mem5 : t5.mem = t1.mem.writeW (off W (S + 20)) (t4.gpr .eax) := by
    rw [M5.mem, u4.mem, u3.mem, f2.mem]
  have O5 : Outside W (S + 20) 4 t1.mem t5.mem := by rw [mem5]; exact writeW32_outside _ _ _ (by omega)
  have P5 : Params t5 W L V 12 := P.keep
    ((Outs.of_outside (O1.mono (o' := 0) (n' := L) (by omega) (by omega)) (by simp)).trans
      (Outs.of_outside (O5.mono (o' := 0) (n' := L) (by omega) (by omega)) (by simp)))
    (K5.1 _ (by decide)) K5.2.1 K5.2.2
  refine wp_addX rfl fun t6 u6 _ m6 x6 => wp_movX (P5.readSk (Sk.of_upd [.ecx] u6 m6 x6) (i := pN4) (by decide))
    fun t7 u7 m7 x7 => wp_addX rfl fun t8 u8 _ m8 x8 => wp_cmpX rfl fun t9 f9 _ z9 m9 x9 => WP.block_nil ?_
  have ecx8 : t8.gpr .ecx = BitVec.ofNat 32 (4 * (k + 1)) := by
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr, K5.1 _ (by decide), hcx]
    apply ofNat_of_toNat
    rw [BitVec.toNat_add, toNat_ofNat_lt (by omega), show (4 : BitVec 32).toNat = 4 from rfl]
    omega
  have ecx9 : t9.gpr .ecx = BitVec.ofNat 32 (4 * (k + 1)) := by rw [f9.gpr, ecx8]
  have mem9 : t9.mem = t5.mem := by rw [f9.mem, u8.mem, u7.mem, u6.mem]
  have hv := (V pN4).isLt
  refine ⟨?_, ?_, ?_, ecx9, ?_, ?_, ?_⟩
  · rw [mem9, mem5, w32_write_ne (size := L) (o := S + 20) (d := S + 16) hn (by omega) (by omega) (by omega),
      M1.mem, w32_write_self]
  · have r12 : (t1.mem.readW (off W (S + 12)) 32).toNat = w32 t.mem W (S + 12) := by
      rw [M1.mem]; exact w32_write_ne (size := L) (o := S + 16) (d := S + 12) hn (by omega) (by omega) (by omega) _
    have r8 : (t1.mem.readW (off W (S + 8)) 32).toNat = w32 t.mem W (S + 8) := by
      rw [M1.mem]; exact w32_write_ne (size := L) (o := S + 16) (d := S + 8) hn (by omega) (by omega) (by omega) _
    rw [mem9, mem5, w32_write_self, u4.gpr, add3_toNat, u3.gpr, f2.mem,
      show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, r12, r8, M1.gpr]
  · rw [mem9]
    exact (Outs.of_outside (O1.mono (o' := S + 16) (n' := 8) (by omega) (by omega)) (by simp)).trans
      (Outs.of_outside (O5.mono (o' := S + 16) (n' := 8) (by omega) (by omega)) (by simp))
  · rw [z9, ecx8, u8.gpr, u7.gpr, ofNat_of_toNat hN, ← BitVec.ofNat_add, sub_beq (by omega) (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · exact ((((K5.mono (rs' := [.eax, .ecx]) (by decide)).widen u6.keeps).widen u7.keeps).widen u8.keeps).widen
      (f9.keeps [])
  · rw [m9, m8, m7, m6, m5, m4, m3, m2, m1]

end VG.Proof.Mont.X86.Sse2
