module

public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeAcc
public import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: sums of products in words, with AVX2

The accumulator of `Bodies.avx2` (`Impl/MlKem/X86_64/KpkeAccY.lean`): word
`w` at `p` is coefficient `accIdx w` of the polynomial (`Acc16`, `accY`),
and the table of the products is `gTabY` at `scratch + 3328` (`tabY`).
`zeroAccY` stores zeros (`zeroAccY_correct`), `tabAccY` stores the table
(`tabAccY_wp`), and `mulAccY` adds a product (`MulAccY.correct`): each
iteration loads and deinterleaves its factors (`yload4_ok`, `deintS`) and
runs `vbase` (`MulAvx2.lean`), whose lanes hold the products of the pairs
`pairY i l e`, which are the coefficients of words `32i + 8l + e` and
`32i + 16 + 8l + e` of the accumulator; each is added to its word, in each
lane (`vacc_ok`, `accStore_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## The accumulator and the table -/

/-- The polynomial `F` as the accumulator of `Bodies.avx2` at `p`. -/
def Acc16 (m : Mem) (p : Addr) (F : Poly) : Prop := ∀ w < 256, (wordAt m p w).toNat = (F[accIdx w]!).val

theorem accIdx_eq {i h l e : Nat} (hh : h < 2) (hl : l < 2) (he : e < 8) :
    accIdx (32 * i + 16 * h + 8 * l + e) = 2 * pairY i l e + h := by
  unfold accIdx pairY; omega_arith

theorem accIdx_lt {w : Nat} (hw : w < 256) : accIdx w < 256 := by unfold accIdx; omega_arith

/-- Words of the 1024 bytes at `p`, in memory that writes elsewhere kept. -/
theorem wordAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (pR p).Disjoint r) {w : Nat} (hw : w < 512) : wordAt m' p w = wordAt m p w :=
  hf.readW (r := pR p) (Offset.contains_base p (by omega_arith) (by omega_arith)) hd (by decide)

def accY : AccRep := ⟨Acc16, fun hf _ _ hd h w hw => by rw [wordAt_frame hf hd (by omega_arith)]; exact h w hw⟩

/-- The table of `mulAccY` at `C + 3328`. -/
def TabY (m : Mem) (C : Addr) : Prop := ∀ k < 128, (wordAt m (C + BitVec.ofNat 64 3328) k).toNat = gTabY k

def tabY : TabRep := ⟨TabY, fun hf _ hd h k hk => by
  rw [wordAt, hf.readW (r := tabR _) (Offset.contains_base _ (by omega_arith) (by omega_arith)) hd (by decide)]
  exact h k hk⟩

/-! ## A sum of words, reduced -/

/-- The sum of two words less than `q`, reduced (`paddw`, `vcsub`). -/
theorem addW {a b : BitVec 16} {x y : Zq} (ha : a.toNat = x.val) (hb : b.toNat = y.val) :
    (W.csubW (a + b)).toNat = (x + y).val := by
  have hx := val_lt x
  have hy := val_lt y
  have ai := W.toInt_of_lt (a := a) (by rw [ha]; exact hx)
  have bi := W.toInt_of_lt (a := b) (by rw [hb]; exact hy)
  rw [ha] at ai
  rw [hb] at bi
  obtain ⟨⟨p1, p2, p3, p4⟩, _⟩ :=
    W.addsub_int (A := a.toInt) (T := b.toInt) (by rw [ai]; omega_arith) (by rw [bi]; omega_arith)
  rw [← W.toInt_add16 p1 p2] at p3 p4
  have c1 := W.csubW_spec p3 p4
  rw [W.toInt_add16 p1 p2] at c1
  have n1 := W.toNat_of_toInt (a := W.csubW (a + b)) (by rw [c1]; exact Int.emod_nonneg _ (by decide))
  have v1 : (x + y).val = (x.val + y.val) % 3329 := val_add' _ _
  rw [v1]
  rw [c1, ai, bi] at n1
  omega_arith

/-- `h ← h + xmm5`, reduced, on the words of an SSE2 register. -/
theorem vacc_ok {h : XReg} (h3 : XReg.xmm3 ≠ h) (h14 : XReg.xmm14 ≠ h)
    (h15 : XReg.xmm15 ≠ h) {s : State} (hc : VConsts s) {x y : Nat → Zq} (hx : Lanes (s.xmm h) x)
    (hy : Lanes (s.xmm .xmm5) y) :
    WP isa (.block (xb .paddw h .xmm5 :: vcsub h .xmm3)) s fun s' =>
      Lanes (s'.xmm h) (fun e => x e + y e) ∧ XOnly [h, .xmm3] s s' := by
  rw [block_cons_iff]
  refine WP.mono (paddw_ok (d := h) (e := .xmm5)) fun s1 ⟨l1, o1⟩ => ?_
  have c1 := o1.consts hc (by simpa using h14) (by simpa using h15)
  refine WP.mono (vcsub_ok (d := h) (t := .xmm3) h3 h15 (by decide) h14 c1) fun s2 ⟨l2, o2⟩ =>
    ⟨fun e he => ?_, (o1.trans o2).mono (by simp)⟩
  rw [l2 e he]
  dsimp only
  rw [l1 e he]
  exact addW (hx e he) (hy e he)

theorem lane_acc1 :
    laneSseBlock (toY (xb .paddw .xmm1 .xmm5 :: vcsub .xmm1 .xmm3)) = some (xb .paddw .xmm1 .xmm5 :: vcsub .xmm1 .xmm3) := by
  decide +kernel

theorem lane_acc2 :
    laneSseBlock (toY (xb .paddw .xmm2 .xmm5 :: vcsub .xmm2 .xmm3)) = some (xb .paddw .xmm2 .xmm5 :: vcsub .xmm2 .xmm3) := by
  decide +kernel

/-- A 256-bit store. -/
theorem yst_ok {s : State} {h : XReg} {off : Nat} (hin : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 off) 32) :
    WP isa (.block [.vmovdquStore .l256 (at_ .rdi off) h]) s fun s' =>
      s' = s.setMem (s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 off) (s.ymm h)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store256_eq, ea_at, hin, ite_true,
    Option.some.injEq, exists_eq_left']

/-- `accStore h off`: the words of `h` added to the 32 bytes at `rdi + off`, reduced, and stored there. -/
theorem accStore_ok {h : XReg} (hl : laneSseBlock (toY (xb .paddw h .xmm5 :: vcsub h .xmm3)) =
      some (xb .paddw h .xmm5 :: vcsub h .xmm3))
    (h3 : XReg.xmm3 ≠ h) (h5 : XReg.xmm5 ≠ h) (h14 : XReg.xmm14 ≠ h) (h15 : XReg.xmm15 ≠ h)
    {off : Nat} {s : State} (hc : YConsts s) (hin : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 off) 32)
    {x y : Nat → Nat → Zq} (hx : ∀ l < 2, Lanes (s.lane h l) (x l))
    (hy : ∀ l < 2, Lanes (s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 off + BitVec.ofNat 64 (16 * l)) 128) (y l)) :
    WP isa (.block (accStore h off)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 off) (s'.ymm h) ∧
      (∀ l < 2, Lanes (s'.lane h l) (fun e => x l e + y l e)) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr ∧ YConsts s' ∧
      ∀ r, r ∉ [XReg.xmm5, h, .xmm3] → ∀ l < 2, s'.lane r l = s.lane r l := by
  have hin' : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 off) 32 :=
    let ⟨r, hr, hc⟩ := hin; ⟨r, List.mem_append_right _ hr, hc⟩
  simp only [accStore, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok hin') fun s1 ⟨L1, o1⟩ => ?_
  have c1 := o1.consts hc (by decide) (by decide)
  rw [WP.block_append_iff]
  have X1 : ∀ l < 2, Lanes ((s1.proj l).xmm h) (x l) := fun l hl' => by
    rw [State.proj_xmm, o1.lane _ (by simpa using h5.symm) l hl']; exact hx l hl'
  have Y1 : ∀ l < 2, Lanes ((s1.proj l).xmm .xmm5) (y l) := fun l hl' => by
    rw [State.proj_xmm, L1 l hl']; exact hy l hl'
  refine WP.mono (ylanes hl (P := fun l t => Lanes (t.xmm h) (fun e => x l e + y l e))
    fun l hl' => vacc_ok h3 h14 h15 (c1 l hl') (X1 l hl') (Y1 l hl')) fun s2 ⟨L2, o2⟩ => ?_
  have o12 := o1.trans o2
  refine WP.mono (yst_ok (h := h) (by rw [o12.wr, o12.gpr]; exact hin)) fun s3 e3 => ?_
  subst e3
  refine ⟨by simp only [State.setMem_mem, State.setMem_ymm]; rw [o12.mem, o12.gpr], fun l hl' => ?_,
    by simp only [State.setMem_gpr]; exact o12.gpr, by simp only [State.setMem_rd]; exact o12.rd,
    by simp only [State.setMem_wr]; exact o12.wr, ?_, ?_, fun r hr l hl' => ?_⟩
  · simp only [State.setMem_lane]; exact L2 l hl'
  · rw [show (s2.setMem _).mxcsr = s2.mxcsr by cases s2; rfl]; exact o12.mxcsr
  · exact lanes_gpr (s := s2) (fun r l => by simp only [State.setMem_lane]) o12 hc
      (by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, h14, by decide⟩)
      (by simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, h15, by decide⟩)
  · simp only [State.setMem_lane]; exact o12.lane r (by simpa [or_comm, or_left_comm] using hr) l hl'

/-! ## The zero accumulator -/

theorem vpxor0_ok (s : State) :
    WP isa (.block [yb .vpxor .xmm0 .xmm0 .xmm0]) s fun s' =>
      s'.ymm .xmm0 = 0 ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [yb, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  rw [State.ymm_eq, lane_vbin256, lane_vbin256, ifp rfl, ifp rfl]
  simp only [VBinOp.sse, pxor_self]
  rfl

theorem zeroAccY_wp {s : State} (hw : pR (s.gpr .rdi) ∈ s.wr) :
    WP isa zeroAccY s fun s' => Acc16 s'.mem (s.gpr .rdi) zero ∧ Frame [pR (s.gpr .rdi)] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold zeroAccY
  rw [show ∀ (a : Instr) (l : List Instr), a :: l = [a] ++ l from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (vpxor0_ok s) fun s1 ⟨hz, hm, hg, hrd, hwr⟩ => ?_
  rw [List.map_eq_flatMap]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) (fun i t => t.ymm .xmm0 = 0 ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ Frame [pR (s.gpr .rdi)] s.mem t.mem ∧ ∀ w < 16 * i, wordAt t.mem (s.gpr .rdi) w = 0)
    (fun k t hk ⟨tz, tg, trd, twr, tf, tw⟩ => ?_) 16 (Nat.le_refl _) s1 ⟨hz, hg, hrd, hwr, by rw [hm]; exact Frame.refl _ _,
      fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun t ⟨_, tg, trd, twr, tf, tw⟩ => ⟨fun w hw' => ?_, tf, tg, trd, twr⟩
  · have hin : InRegions t.wr (t.gpr .rdi + BitVec.ofNat 64 (32 * k)) 32 := by
      rw [twr, tg]; exact ⟨_, hw, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    refine WP.mono (yst_ok (h := .xmm0) hin) fun t' e' => ?_
    subst e'
    simp only [State.setMem_ymm, State.setMem_gpr, State.setMem_rd, State.setMem_wr, State.setMem_mem]
    have ea : t.gpr .rdi + BitVec.ofNat 64 (32 * k) = wAddr (s.gpr .rdi) (16 * k) := by
      rw [tg, wAddr, show 2 * (16 * k) = 32 * k by omega_arith]
    refine ⟨tz, tg, trd, twr, ?_, fun w hw' => ?_⟩
    · rw [ea]; exact tf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
    · rw [ea, wordAt_write256 _ _ (by omega_arith) _ (by omega_arith), tz]
      split
      · exact BitVec.eq_of_toNat_eq (by simp)
      · exact tw w (by omega_arith)
  · rw [tw w (by omega_arith), zero, getElem!_pos _ _ (by rw [n_eq]; exact accIdx_lt hw')]
    simp

theorem zeroAccY_correct (s : State) (hs : (zeroK accY).pre s) :
    ∃ t s', Exec isa zeroAccY s t s' ∧ abiPreserved s s' ∧ (zeroK accY).post s s' := by
  obtain ⟨t, s', he, ⟨hP, hf, _⟩, hk⟩ := WP.keep [] (zeroAccY_wp (s := s) (by rw [hs.2.1]; simp))
    (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2)), hP⟩

/-! ## The table -/

theorem contains_off {R : Region} {a : Addr} {n d k : Nat} (h : R.Contains a n) (hdk : d + k ≤ n) :
    R.Contains (a + BitVec.ofNat 64 d) k := by
  simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h ⊢
  omega_arith

/-- `wordTab_gen` (`VPack.lean`), for a table in any writable region. -/
theorem wordTab_in (t : Nat → Nat) (ht : ∀ k, t k < 65536) {r : Reg} (hr : r ≠ .r9) {sP : Addr} {s : State}
    (hsi : s.gpr r = sP) (hw : InRegions s.wr sP 256) :
    WP isa (.block (wordTab t 128 r 0)) s fun s' => (∀ k < 128, (wordAt s'.mem sP k).toNat = t k) ∧
      Frame [⟨sP, 256⟩] s.mem s'.mem ∧ Keep [.r9] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (N := 32) (fun i w =>
      (∀ k < 4 * i, (wordAt w.mem sP k).toNat = t k) ∧ Frame [⟨sP, 256⟩] s.mem w.mem ∧ Keep [.r9] s w)
    (fun i w hi ⟨hT, hf, hk⟩ => ?_) 32 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_arith), Frame.refl _ _, Keep.refl _ _⟩)
    fun w ⟨hT, hf, hk⟩ => ⟨fun k hk' => hT k (by omega_arith), hf, hk⟩
  have hsi' : w.gpr r = sP := by
    rw [hk.gpr (by simp only [List.mem_singleton]; exact hr), hsi]
  have w0 : InRegions w.wr (sP + BitVec.ofNat 64 (0 + 8 * i)) 8 := by
    obtain ⟨R, hR, hc⟩ := hw
    exact ⟨R, by rw [hk.2.2]; exact hR, contains_off hc (by omega_arith)⟩
  have hV : ∀ e < 4, ((BitVec.ofNat 64 (t (4 * i) + 2 ^ 16 * t (4 * i + 1) +
      2 ^ 32 * t (4 * i + 2) + 2 ^ 48 * t (4 * i + 3))).extractLsb' (16 * e) 16).toNat =
        t (4 * i + e) := fun e he => by
    rw [quad_word (ht _) (ht _) (ht _) (ht _) he]
    rcases (by omega_arith : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;> rfl
  vrunm [hsi', w0, hr]
  generalize BitVec.ofNat 64 (t (4 * i) + 2 ^ 16 * t (4 * i + 1) +
      2 ^ 32 * t (4 * i + 2) + 2 ^ 48 * t (4 * i + 3)) = V at hV ⊢
  refine ⟨fun k hk' => ?_, hf.writeW (List.mem_singleton_self _) _
      (Offset.contains_base sP (by omega_arith) (by omega_arith)), ⟨fun r hr => ?_, hk.2.1, hk.2.2⟩⟩
  · by_cases h : 4 * i ≤ k
    · rw [wordAt, wAddr, show sP + BitVec.ofNat 64 (2 * k) =
          sP + BitVec.ofNat 64 (0 + 8 * i) + BitVec.ofNat 64 (2 * (k - 4 * i)) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact congrArg _ (congrArg _ (by omega_arith)),
        readW_writeW64_16 _ _ _ (by omega_arith), hV _ (by omega_arith), show 4 * i + (k - 4 * i) = k by omega_arith]
    · rw [wordAt, Mem.readW_writeW_sep (Offset.sep sP (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact hT k (by omega_arith)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
    exact hk.1 r (by simp [hr])

theorem tabAccY_wp (s : State) (hin : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 3328) 256) :
    WP isa (.block tabAccY) s fun s' => tabY.is s'.mem (s.gpr .rcx) ∧ Frame [tabR (s.gpr .rcx)] s.mem s'.mem ∧
      Keep [.r9, .r10] s s' := by
  simp only [tabAccY, leaR, oTabY]
  rw [show ∀ (a b : Instr) (l : List Instr), [a, b] ++ l = [a, b] ++ l from fun _ _ _ => rfl, WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => s1.gpr .r10 = s.gpr .rcx + BitVec.ofNat 64 3328 ∧ s1.mem = s.mem ∧
      Keep [.r10] s s1) (by
        vrunm [sx_ofNat (show 3328 < 2 ^ 31 by decide)]
        refine ⟨fun r hr => ?_, rfl, rfl⟩
        simp only [List.mem_singleton] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s1 ⟨h10, hm1, k1⟩ => ?_
  refine WP.mono (wordTab_in gTabY gTabY_lt (by decide) h10 (by rw [k1.2.2]; exact hin))
    fun s2 ⟨hT, hf, k2⟩ => ⟨fun k hk => hT k hk, by rw [← hm1]; exact hf, (k1.trans k2).mono (by simp)⟩

/-! ## A product added to the accumulator -/

/-- The doublewords of lane `l` of a load of 32 coefficients from `j` of a polynomial. -/
theorem loadsY_of {m : Mem} {p : Addr} {P : Poly} (hP : PolyIs m p P) {j : Nat} (hj : j + 32 ≤ 256) {t l : Nat}
    (ht : t < 4) (hl : l < 2) (off : Nat) (hoff : off = 32 * t) (f : Nat → Nat)
    (hfe : ∀ e < 4, f e = j + 8 * t + 4 * l + e) :
    ∀ e < 4, (dword (m.readW (coeffAddr p j + BitVec.ofNat 64 off + BitVec.ofNat 64 (16 * l)) 128) e).toNat =
      (P[f e]!).val := fun e he => by
  rw [dword_readW _ _ he, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add, hoff,
    show 32 * t + (16 * l + 4 * e) = 4 * (8 * t + 4 * l + e) by omega_arith, coeffAddr_off, ← coeffAt_eq,
    polyIs_toNat hP (by rw [n_eq]; omega_arith), hfe e he]
  exact congrArg (fun k : Nat => ((P[k]! : Zq)).val) (by omega_arith)

/-- The lanes `deint` leaves of the 32 coefficients from `j` of a polynomial, in lane `l`. -/
theorem deintY_of {m : Mem} {p : Addr} {P : Poly} (hP : PolyIs m p P) {j : Nat} (hj : j + 32 ≤ 256) {l : Nat}
    (hl : l < 2) (a : Addr) (ha : a = coeffAddr p j) :
    (∀ e < 8, (word (deE (m.readW (a + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * l)) 128)
      (m.readW (a + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128)
      (m.readW (a + BitVec.ofNat 64 64 + BitVec.ofNat 64 (16 * l)) 128)
      (m.readW (a + BitVec.ofNat 64 96 + BitVec.ofNat 64 (16 * l)) 128)) e).toNat =
        (P[j + 8 * (2 * e / 4) + 4 * l + 2 * e % 4]!).val) ∧
    (∀ e < 8, (word (deO (m.readW (a + BitVec.ofNat 64 0 + BitVec.ofNat 64 (16 * l)) 128)
      (m.readW (a + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l)) 128)
      (m.readW (a + BitVec.ofNat 64 64 + BitVec.ofNat 64 (16 * l)) 128)
      (m.readW (a + BitVec.ofNat 64 96 + BitVec.ofNat 64 (16 * l)) 128)) e).toNat =
        (P[j + 8 * ((2 * e + 1) / 4) + 4 * l + (2 * e + 1) % 4]!).val) := by
  subst ha
  exact deint_lanes (c := fun k => (P[j + 8 * (k / 4) + 4 * l + k % 4]!).val)
    (loadsY_of hP hj (t := 0) (by decide) hl 0 rfl (fun e => j + 8 * (e / 4) + 4 * l + e % 4)
      (fun e he => by omega_arith))
    (loadsY_of hP hj (t := 1) (by decide) hl 32 rfl (fun e => j + 8 * ((4 + e) / 4) + 4 * l + (4 + e) % 4)
      (fun e he => by omega_arith))
    (loadsY_of hP hj (t := 2) (by decide) hl 64 rfl (fun e => j + 8 * ((8 + e) / 4) + 4 * l + (8 + e) % 4)
      (fun e he => by omega_arith))
    (loadsY_of hP hj (t := 3) (by decide) hl 96 rfl (fun e => j + 8 * ((12 + e) / 4) + 4 * l + (12 + e) % 4)
      (fun e he => by omega_arith))
    (fun k _ => by have := val_lt (P[j + 8 * (k / 4) + 4 * l + k % 4]!); omega_arith)

theorem prod_even (F G : Poly) {p : Nat} (hp : p < 128) :
    (multiplyNTTs F G)[2 * p]! = F[2 * p]! * G[2 * p]! + F[2 * p + 1]! * G[2 * p + 1]! * gamma p := by
  rw [multiplyNTTs_get F G (by rw [n_eq]; omega_arith), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)),
    show 2 * p / 2 = p by omega_arith]

theorem prod_odd (F G : Poly) {p : Nat} (hp : p < 128) :
    (multiplyNTTs F G)[2 * p + 1]! = F[2 * p]! * G[2 * p + 1]! + F[2 * p + 1]! * G[2 * p]! := by
  rw [multiplyNTTs_get F G (by rw [n_eq]; omega_arith), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)),
    show 2 * p + 1 - 1 = 2 * p by omega_arith]

namespace MulAccY

section
variable (s₀ : State)

abbrev aP : Addr := s₀.gpr .rdi
abbrev fP : Addr := s₀.gpr .rsi
abbrev gP : Addr := s₀.gpr .rdx
abbrev tP : Addr := s₀.gpr .rcx + BitVec.ofNat 64 3328
abbrev F : Poly := polyAt s₀.mem (fP s₀)
abbrev G : Poly := polyAt s₀.mem (gP s₀)

/-- After `i` groups of 32 coefficients, with `A` the accumulator at the start. -/
structure Inv (A : Poly) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = coeffAddr (fP s₀) (32 * i)
  rdx : s.gpr .rdx = coeffAddr (gP s₀) (32 * i)
  rdi : s.gpr .rdi = wAddr (aP s₀) (32 * i)
  r8 : s.gpr .r8 = wAddr (tP s₀) (16 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : YConsts s
  r2 : ∀ l < 2, s.lane .xmm12 l = r2V
  frame : Frame [pR (aP s₀)] s₀.mem s.mem
  done : ∀ w < 256, (wordAt s.mem (aP s₀) w).toNat =
    ((if w < 32 * i then add A (multiplyNTTs (F s₀) (G s₀)) else A)[accIdx w]!).val

end

/-- What the products need of the arguments, of `mulAccK` and `mulSetK`. -/
structure ProdPre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (fP s₀), pR (gP s₀), tabR (s₀.gpr .rcx)]
  wr : pR (aP s₀) ∈ s₀.wr
  dF : (pR (aP s₀)).Disjoint (pR (fP s₀))
  dG : (pR (aP s₀)).Disjoint (pR (gP s₀))
  dT : (pR (aP s₀)).Disjoint (tabR (s₀.gpr .rcx))
  redF : Reduced s₀.mem (fP s₀)
  redG : Reduced s₀.mem (gP s₀)
  tab : TabY s₀.mem (s₀.gpr .rcx)

theorem ProdPre.ofAcc {s₀ : State} {o : Nat} (hp : (mulAccK accY tabY o).pre s₀) : ProdPre s₀ :=
  let ⟨hrd, hwr, dF, dG, _, _, dT, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rF, rG, hT, _⟩ := hp
  ⟨hrd, by rw [hwr]; simp, dF, dG, dT, rF, rG, hT⟩

theorem ProdPre.ofSet {s₀ : State} (hp : (mulSetK accY tabY).pre s₀) : ProdPre s₀ :=
  let ⟨hrd, hwr, dF, dG, _, _, dT, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rF, rG, hT⟩ := hp
  ⟨hrd, by rw [hwr]; simp, dF, dG, dT, rF, rG, hT⟩

section
variable {s₀ : State} (hp : ProdPre s₀)
include hp

theorem fs_poly {m : Mem} (hf : Frame [pR (aP s₀)] s₀.mem m) : PolyIs m (fP s₀) (F s₀) :=
  polyIs_frame hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dF.symm) ⟨hp.redF, rfl⟩

theorem gs_poly {m : Mem} (hf : Frame [pR (aP s₀)] s₀.mem m) : PolyIs m (gP s₀) (G s₀) :=
  polyIs_frame hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dG.symm) ⟨hp.redG, rfl⟩

theorem tab_words {m : Mem} (hf : Frame [pR (aP s₀)] s₀.mem m) {k : Nat} (hk : k < 128) :
    (wordAt m (tP s₀) k).toNat = gTabY k :=
  tabY.frame hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dT.symm) hp.tab k hk

theorem inRdY {p : Addr} (hp' : p = fP s₀ ∨ p = gP s₀) {j : Nat} (hj : j + 32 ≤ 256) {t : Nat} (ht : t < 4) :
    InRegions (s₀.rd ++ s₀.wr) (coeffAddr p j + BitVec.ofNat 64 (32 * t)) 32 := by
  rw [show 32 * t = 4 * (8 * t) by omega_arith, coeffAddr_off, hp.1]
  rcases hp' with rfl | rfl
  · exact ⟨pR _, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · exact ⟨pR _, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

omit hp in
/-- Word `e < 16` of a 256-bit store of `h` at word `j`, as a lane's word. -/
theorem wordAt_ystore (s : State) (h : XReg) (m : Mem) (p : Addr) {j : Nat} (hj : j + 16 ≤ 256) {w : Nat}
    (hw : w < 256) (hjw : j ≤ w) (hwj : w < j + 16) :
    wordAt (m.writeW (wAddr p j) (s.ymm h)) p w = word (s.lane h ((w - j) / 8)) ((w - j) % 8) := by
  rw [wordAt_write256 _ _ hj _ hw, ite_eq_left_of_eq_true _ _ (eq_true ⟨hjw, hwj⟩), word_ymm _ _ (by omega_arith)]

set_option linter.unusedSimpArgs false in
/-- The products of iteration `i`, in `ymm1` and `ymm2`. -/
theorem prod_ok {i : Nat} (hi : i < 8) {s : State} (hrsi : s.gpr .rsi = coeffAddr (fP s₀) (32 * i))
    (hrdx : s.gpr .rdx = coeffAddr (gP s₀) (32 * i)) (hr8 : s.gpr .r8 = wAddr (tP s₀) (16 * i))
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hc : YConsts s) (hr2 : ∀ l < 2, s.lane .xmm12 l = r2V)
    (hf : Frame [pR (aP s₀)] s₀.mem s.mem) :
    WP isa (.block mulProdY) s fun s6 =>
      (∀ l < 2, Lanes ((s6.proj l).xmm .xmm1) (fun e => (multiplyNTTs (F s₀) (G s₀))[2 * pairY i l e]!) ∧
        Lanes ((s6.proj l).xmm .xmm2) (fun e => (multiplyNTTs (F s₀) (G s₀))[2 * pairY i l e + 1]!)) ∧
      ∃ rs, YOnly rs s s6 ∧ XReg.xmm12 ∉ rs ∧ XReg.xmm14 ∉ rs ∧ XReg.xmm15 ∉ rs := by
  have hrr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hrd, hwr]
  have hj : 32 * i + 32 ≤ 256 := by omega_arith
  have rF : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 (32 * t)) 32 := fun t ht => by
    rw [hrr, hrsi]; exact inRdY hp (.inl rfl) hj ht
  have rG : ∀ t < 4, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (32 * t)) 32 := fun t ht => by
    rw [hrr, hrdx]; exact inRdY hp (.inr rfl) hj ht
  have hFs := fs_poly hp hf
  have hGs := gs_poly hp hf
  simp only [mulProdY, List.append_assoc]
  -- the loads of `f` and their lanes
  rw [WP.block_append_iff]
  refine WP.mono (yload4_ok (p := .rsi) (a := .xmm0) (b := .xmm1) (c := .xmm2) (d := .xmm3) (by decide)
    (rF 0 (by decide)) (rF 1 (by decide)) (rF 2 (by decide)) (rF 3 (by decide))) fun s1 ⟨A1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_deintS0 (P := fun l t =>
      t.xmm .xmm0 = deE (s1.lane .xmm0 l) (s1.lane .xmm1 l) (s1.lane .xmm2 l) (s1.lane .xmm3 l) ∧
      t.xmm .xmm4 = deO (s1.lane .xmm0 l) (s1.lane .xmm1 l) (s1.lane .xmm2 l) (s1.lane .xmm3 l))
    fun l _ => deintS_ok0 (s1.proj l)) fun s2 ⟨D2, o2⟩ => ?_
  -- the loads of `g` and their lanes
  have rG' : ∀ t < 4, InRegions (s2.rd ++ s2.wr) (s2.gpr .rdx + BitVec.ofNat 64 (32 * t)) 32 := fun t ht => by
    rw [o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact rG t ht
  rw [WP.block_append_iff]
  refine WP.mono (yload4_ok (p := .rdx) (a := .xmm6) (b := .xmm7) (c := .xmm8) (d := .xmm9) (by decide)
    (rG' 0 (by decide)) (rG' 1 (by decide)) (rG' 2 (by decide)) (rG' 3 (by decide))) fun s3 ⟨A3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_deintS6 (P := fun l t =>
      t.xmm .xmm6 = deE (s3.lane .xmm6 l) (s3.lane .xmm7 l) (s3.lane .xmm8 l) (s3.lane .xmm9 l) ∧
      t.xmm .xmm10 = deO (s3.lane .xmm6 l) (s3.lane .xmm7 l) (s3.lane .xmm8 l) (s3.lane .xmm9 l))
    fun l _ => deintS_ok6 (s3.proj l)) fun s4 ⟨D4, o4⟩ => ?_
  have o14 := ((o1.trans o2).trans o3).trans o4
  -- the `γ`s
  have hz : InRegions (s4.rd ++ s4.wr) (s4.gpr .r8 + BitVec.ofNat 64 0) 32 := by
    rw [o14.rd, o14.wr, o14.gpr, hrr, hr8, hp.1, wAddr, BitVec.add_assoc, ← BitVec.ofNat_add, tP,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨tabR (s₀.gpr .rcx), by simp, Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)⟩
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok hz) fun s5 ⟨Z5, o5⟩ => ?_
  have o15 := o14.trans o5
  have c5 : YConsts s5 := o15.consts hc (by decide) (by decide)
  -- the lanes `vbase` multiplies
  have m4 : s4.mem = s.mem := o14.mem
  have g4 : s4.gpr = s.gpr := o14.gpr
  have idx : ∀ l < 2, ∀ e < 8, 32 * i + 8 * (2 * e / 4) + 4 * l + 2 * e % 4 = 2 * pairY i l e ∧
      32 * i + 8 * ((2 * e + 1) / 4) + 4 * l + (2 * e + 1) % 4 = 2 * pairY i l e + 1 := fun l _ e _ => by
    unfold pairY; omega_arith
  have LF : ∀ l < 2, Lanes (s5.lane .xmm0 l) (fun e => (F s₀)[2 * pairY i l e]!) ∧
      Lanes (s5.lane .xmm4 l) (fun e => (F s₀)[2 * pairY i l e + 1]!) := fun l hl => by
    have d := deintY_of hFs hj hl _ hrsi
    rw [o5.lane _ (by decide) l hl, o4.lane _ (by decide) l hl, o3.lane _ (by decide) l hl,
      o5.lane _ (by decide) l hl, o4.lane _ (by decide) l hl, o3.lane _ (by decide) l hl]
    have e0 : s2.lane .xmm0 l = _ := (D2 l hl).1
    have e4 : s2.lane .xmm4 l = _ := (D2 l hl).2
    rw [e0, e4, (A1 l hl).1, (A1 l hl).2.1, (A1 l hl).2.2.1, (A1 l hl).2.2.2]
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rw [d.1 e he, (idx l hl e he).1]
    · rw [d.2 e he, (idx l hl e he).2]
  have LG : ∀ l < 2, Lanes (s5.lane .xmm6 l) (fun e => (G s₀)[2 * pairY i l e]!) ∧
      Lanes (s5.lane .xmm10 l) (fun e => (G s₀)[2 * pairY i l e + 1]!) := fun l hl => by
    have d := deintY_of (m := s2.mem) (by rw [o2.mem, o1.mem]; exact hGs) hj hl
      (s2.gpr .rdx) (by rw [o2.gpr, o1.gpr, hrdx])
    rw [o5.lane _ (by decide) l hl, o5.lane _ (by decide) l hl]
    have e6 : s4.lane .xmm6 l = _ := (D4 l hl).1
    have e10 : s4.lane .xmm10 l = _ := (D4 l hl).2
    rw [e6, e10, (A3 l hl).1, (A3 l hl).2.1, (A3 l hl).2.2.1, (A3 l hl).2.2.2]
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rw [d.1 e he, (idx l hl e he).1]
    · rw [d.2 e he, (idx l hl e he).2]
  have LZ : ∀ l < 2, ZLanes (s5.lane .xmm13 l) (fun e => gamma (pairY i l e)) := fun l hl e he => by
    rw [Z5 l hl, m4, g4, hr8, word_readW _ _ he, wAddr, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
      show 2 * (16 * i) + (0 + (16 * l + 2 * e)) = 2 * (16 * i + 8 * l + e) by omega_arith, ← wAddr, ← wordAt,
      tab_words hp hf (by omega_arith), gTabY, gIdxY_eq hl he, gTab_eq]
  have R5 : ∀ l < 2, s5.lane .xmm12 l = r2V := fun l hl => by rw [o15.lane _ (by decide) l hl, hr2 l hl]
  refine WP.mono (ylanes lane_vbase (P := fun l t =>
      Lanes (t.xmm .xmm1) (fun e => (multiplyNTTs (F s₀) (G s₀))[2 * pairY i l e]!) ∧
      Lanes (t.xmm .xmm2) (fun e => (multiplyNTTs (F s₀) (G s₀))[2 * pairY i l e + 1]!))
    fun l hl => WP.mono (vbase_ok (c5 l hl) (R5 l hl) (LF l hl).1 (LF l hl).2 (LG l hl).1 (LG l hl).2 (LZ l hl))
      fun _ ⟨a, b, c⟩ => ⟨⟨fun e he => by rw [a e he]; dsimp only; rw [prod_even _ _ (by unfold pairY; omega_arith)],
        fun e he => by rw [b e he]; dsimp only; rw [prod_odd _ _ (by unfold pairY; omega_arith)]⟩, c⟩)
    fun s6 ⟨V6, o6⟩ => ⟨V6, _, o15.trans o6, by decide, by decide, by decide⟩

set_option linter.unusedSimpArgs false in
theorem step {A : Poly} {i : Nat} (hi : i < 8) {s : State} (hI : Inv s₀ A i s) :
    WP isa (.block (mulAccBodyY ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ A (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hj : 32 * i + 32 ≤ 256 := by omega_arith
  simp only [mulAccBodyY, mulNextY, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (prod_ok hp hi hI.rsi hI.rdx hI.r8 hI.rd hI.wr hI.c hI.r2 hI.frame)
    fun s6 ⟨V6, _, o16, n12, n14, n15⟩ => ?_
  have c6 : YConsts s6 := o16.consts hI.c n14 n15
  have di6 : s6.gpr .rdi = wAddr (aP s₀) (32 * i) := by rw [o16.gpr, hI.rdi]
  have hw6 : ∀ d, d + 32 ≤ 64 → InRegions s6.wr (s6.gpr .rdi + BitVec.ofNat 64 d) 32 := fun d hd => by
    rw [o16.wr, hI.wr, di6, wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨pR (aP s₀), hp.wr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  -- the words of the accumulator the stores replace
  have hAw : ∀ (m : Mem), m = s.mem → ∀ h < 2, ∀ l < 2,
      Lanes (m.readW (wAddr (aP s₀) (32 * i) + BitVec.ofNat 64 (32 * h) + BitVec.ofNat 64 (16 * l)) 128)
        (fun e => A[2 * pairY i l e + h]!) := fun m hm h hh l hl e he => by
    rw [word_readW _ _ he, wAddr, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add,
      show 2 * (32 * i) + (32 * h + (16 * l + 2 * e)) = 2 * (32 * i + 16 * h + 8 * l + e) by omega_arith, ← wAddr,
      ← wordAt, hm, hI.done _ (by omega_arith), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)),
      accIdx_eq hh hl he]
  -- the first half
  rw [WP.block_append_iff]
  refine WP.mono (accStore_ok lane_acc1 (by decide) (by decide) (by decide) (by decide) c6 (hw6 0 (by decide))
    (x := fun l e => (multiplyNTTs (F s₀) (G s₀))[2 * pairY i l e]!) (y := fun l e => A[2 * pairY i l e + 0]!)
    (fun l hl => (V6 l hl).1) (fun l hl => by
      rw [di6, show (0 : Nat) = 32 * 0 from rfl]; exact hAw _ (by rw [o16.mem]) 0 (by decide) l hl))
    fun s7 ⟨hm7, L7, g7, rd7, wr7, mx7, c7, o7⟩ => ?_
  -- the second half
  have hw7 : InRegions s7.wr (s7.gpr .rdi + BitVec.ofNat 64 32) 32 := by rw [wr7, g7]; exact hw6 32 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (accStore_ok lane_acc2 (by decide) (by decide) (by decide) (by decide) c7 hw7
    (x := fun l e => (multiplyNTTs (F s₀) (G s₀))[2 * pairY i l e + 1]!) (y := fun l e => A[2 * pairY i l e + 1]!)
    (fun l hl => by rw [o7 _ (by decide) l hl]; exact (V6 l hl).2) (fun l hl => ?_))
    fun s8 ⟨hm8, L8, g8, rd8, wr8, mx8, c8, o8⟩ => ?_
  · have ea : s7.gpr .rdi + BitVec.ofNat 64 32 + BitVec.ofNat 64 (16 * l) = wAddr (aP s₀) (32 * i + 16 + 8 * l) := by
      rw [g7, di6, wAddr, wAddr, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      exact congrArg _ (congrArg _ (by omega_arith))
    have e0 : s6.gpr .rdi + BitVec.ofNat 64 0 = wAddr (aP s₀) (32 * i) := by rw [di6, add_ofNat_zero]
    intro e he
    rw [ea, word_readW _ _ he, wAddr_add, ← wordAt, hm7, e0, wordAt_write256 _ _ (by omega_arith) _ (by omega_arith),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), o16.mem, hI.done _ (by omega_arith),
      ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)),
      show 32 * i + 16 + 8 * l + e = 32 * i + 16 * 1 + 8 * l + e by omega_arith, accIdx_eq (by decide) hl he]
  -- the pointers and the count
  have sx128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 (4 * 32) := by decide
  have sx64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (2 * 32) := by decide
  have e0 : s6.gpr .rdi + BitVec.ofNat 64 0 = wAddr (aP s₀) (32 * i) := by rw [di6, add_ofNat_zero]
  have e32 : s7.gpr .rdi + BitVec.ofNat 64 32 = wAddr (aP s₀) (32 * i + 16) := by
    rw [g7, di6, show (BitVec.ofNat 64 32) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add]
  rw [e0] at hm7
  rw [e32] at hm8
  vrunm [g8, g7, sx32, sx128, sx64]
  refine ⟨?_, by rw [o16.gpr], by rw [o16.gpr]⟩
  constructor
  all_goals try simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, setReg_mem, setFlags_mem, reduceCtorEq, ite_true, ite_false]
  case rsi => rw [o16.gpr, hI.rsi, coeffAddr_off, Nat.mul_succ]
  case rdx => rw [o16.gpr, hI.rdx, coeffAddr_off, Nat.mul_succ]
  case rdi => rw [di6, wAddr_add, Nat.mul_succ]
  case r8 => rw [o16.gpr, hI.r8, show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add, Nat.mul_succ]
  case rd => rw [rd8, rd7, o16.rd, hI.rd]
  case wr => rw [wr8, wr7, o16.wr, hI.wr]
  case c =>
    exact lanes_gpr (s := s8) (fun r l => by simp only [lane_setReg, lane_setFlags]) (YOnly.refl [] s8) c8
      (by decide) (by decide)
  case r2 =>
    intro l hl
    simp only [lane_setReg, lane_setFlags]
    rw [o8 _ (by decide) l hl, o7 _ (by decide) l hl, o16.lane _ n12 l hl, hI.r2 l hl]
  case frame =>
    rw [hm8, hm7, o16.mem]
    exact (hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  case done =>
    intro w hw
    rw [hm8, hm7, o16.mem]
    have hadd : ∀ q < 256, (add A (multiplyNTTs (F s₀) (G s₀)))[q]! = (multiplyNTTs (F s₀) (G s₀))[q]! + A[q]! :=
      fun q hq => by rw [add_get _ _ (by rw [n_eq]; exact hq)]; exact Fin.ext (by rw [val_add', val_add', Nat.add_comm])
    by_cases h1 : w < 32 * i
    · rw [wordAt_write256 _ _ (by omega_arith) _ hw, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)),
        wordAt_write256 _ _ (by omega_arith) _ hw, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), hI.done w hw,
        ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))]
    by_cases h2 : w < 32 * i + 16
    · rw [wordAt_write256 _ _ (by omega_arith) _ hw, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)),
        wordAt_ystore s7 _ _ _ (by omega_arith) hw (by omega_arith) h2, ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)),
        (L7 _ (by omega_arith)) _ (Nat.mod_lt _ (by omega_arith))]
      dsimp only
      have ew : w = 32 * i + 16 * 0 + 8 * ((w - 32 * i) / 8) + (w - 32 * i) % 8 := by omega_arith
      rw [ew, accIdx_eq (by decide) (by omega_arith) (Nat.mod_lt _ (by omega_arith)), hadd _ (by unfold pairY; omega_arith), ← ew]
      rfl
    by_cases h3 : w < 32 * i + 32
    · rw [wordAt_ystore s8 _ _ _ (by omega_arith) hw (by omega_arith) (by omega_arith), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)),
        (L8 _ (by omega_arith)) _ (Nat.mod_lt _ (by omega_arith))]
      dsimp only
      have ew : w = 32 * i + 16 * 1 + 8 * ((w - (32 * i + 16)) / 8) + (w - (32 * i + 16)) % 8 := by omega_arith
      rw [ew, accIdx_eq (by decide) (by omega_arith) (Nat.mod_lt _ (by omega_arith)), hadd _ (by unfold pairY; omega_arith), ← ew]
    · rw [wordAt_write256 _ _ (by omega_arith) _ hw, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)),
        wordAt_write256 _ _ (by omega_arith) _ hw, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), hI.done w hw,
        ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]

omit hp in
theorem pro_ok (s : State) :
    WP isa (.block mulAccProY) s fun s' => YConsts s' ∧ (∀ l < 2, s'.lane .xmm12 l = r2V) ∧
      s'.gpr .r8 = s.gpr .rcx + BitVec.ofNat 64 3328 ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr ∧
      Keep [.rax, .r8] s s' := by
  simp only [mulAccProY, yconsts, leaR, oTabY]
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm15 _ s) fun s1 ⟨q1, k1, m1, x1, o1⟩ => ?_
  refine WP.mono (yconst_ok .xmm14 _ s1) fun s2 ⟨q2, k2, m2, x2, o2⟩ => ?_
  refine WP.mono (yconst_ok .xmm12 _ s2) fun s3 ⟨q3, k3, m3, x3, o3⟩ => ?_
  vrunm [sx_ofNat (show 3328 < 2 ^ 31 by decide)]
  refine ⟨fun l hl => ⟨?_, ?_⟩, fun l hl => ?_, ?_, by rw [m3, m2, m1], by rw [x3, x2, x1], ?_⟩
  · simp only [State.proj_xmm, lane_setReg, lane_setFlags]
    rw [o3 _ (by decide) l hl, o2 _ (by decide) l hl, q1 l hl]; decide
  · simp only [State.proj_xmm, lane_setReg, lane_setFlags]
    rw [o3 _ (by decide) l hl, q2 l hl]; decide
  · simp only [lane_setReg, lane_setFlags]; rw [q3 l hl]; decide
  · rw [k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide)]
  · exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.2, ite_false]
      rw [k3.gpr (by simpa using hr.1), k2.gpr (by simpa using hr.1), k1.gpr (by simpa using hr.1)],
      by simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; rw [k3.2.1, k2.2.1, k1.2.1],
      by simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; rw [k3.2.2, k2.2.2, k1.2.2]⟩

end

end MulAccY

/-- `w` with `accIdx w = c`. -/
def accPos (c : Nat) : Nat :=
  32 * (c / 2 / 16) + 16 * (c % 2) + 8 * (c / 2 % 16 / 2 % 2) + 2 * (c / 2 % 16 / 4) + c / 2 % 16 % 2

theorem accPos_ok : ∀ c < 256, accPos c < 256 ∧ accIdx (accPos c) = c := by decide +kernel

theorem accIdx_accPos {c : Nat} (hc : c < 256) : accPos c < 256 ∧ accIdx (accPos c) = c := accPos_ok c hc

theorem acc16_unique {m : Mem} {p : Addr} {A B : Poly} (hA : Acc16 m p A) (hB : Acc16 m p B) : A = B :=
  Vector.ext fun c hc => by
    have hc' : c < 256 := by rw [← n_eq]; exact hc
    obtain ⟨h1, h2⟩ := accIdx_accPos hc'
    have e := (hA _ h1).symm.trans (hB _ h1)
    rw [h2, getElem!_eq _ hc, getElem!_eq _ hc] at e
    exact Fin.ext e

namespace MulAccY

theorem correct {o : Nat} {s₀ : State} (hp : (mulAccK accY tabY o).pre s₀) :
    ∃ t s', Exec isa mulAccY s₀ t s' ∧ abiPreserved s₀ s' ∧ (mulAccK accY tabY o).post s₀ s' := by
  have hp' := hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rA, _, _, _, _, _, _, _, _, _, _, A0, hA0⟩ := hp'
  have hW : WP isa mulAccY s₀ fun s' => Acc16 s'.mem (aP s₀) (add A0 (multiplyNTTs (F s₀) (G s₀))) ∧
      Frame [pR (aP s₀)] s₀.mem s'.mem := by
    unfold mulAccY
    refine WP.seq (WP.mono (pro_ok s₀) fun s1 ⟨hc1, hr1, h81, hm1, _, k1⟩ => ?_)
    refine WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide) (Inv s₀ A0) (fun s g hy _ => ?_)
      fun i hi s hI => step (ProdPre.ofAcc hp) hi hI) fun s5 hI => ⟨fun w hw => ?_, hI.frame⟩
    · have k := k1.trans g.keep
      have hl : ∀ r l, s.lane r l = s1.lane r l := fun r l => by
        simp only [State.lane]; rw [g.xmm, hy]
      refine ⟨?_, ?_, ?_, ?_, by rw [k.2.1], by rw [k.2.2], ?_, ?_, ?_, fun w hw => ?_⟩
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
      · rw [g.keep.gpr (by decide), h81]; exact (add_ofNat_zero _).symm
      · exact fun l hl' => ⟨by rw [State.proj_xmm, hl]; exact (hc1 l hl').q,
          by rw [State.proj_xmm, hl]; exact (hc1 l hl').qinv⟩
      · exact fun l hl' => by rw [hl]; exact hr1 l hl'
      · rw [g.mem, hm1]; exact Frame.refl _ _
      · rw [g.mem, hm1, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]; exact hA0 w hw
    · rw [hI.done w hw, ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))]
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rdi, .rsi, .r8] hW (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using rA)), fun A hA => ?_⟩
  rw [acc16_unique hA hA0]
  exact hP

end MulAccY


/-! ## The first product, stored -/

/-- A 256-bit store, as the facts a step needs. -/
theorem ystore_ok {h : XReg} {off : Nat} {s : State} (hin : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 off) 32) :
    WP isa (.block [.vmovdquStore .l256 (at_ .rdi off) h]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 off) (s.ymm h) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ ∀ r l, s'.lane r l = s.lane r l :=
  WP.mono (yst_ok hin) fun _ e => by
    subst e
    exact ⟨by simp only [State.setMem_mem], by simp only [State.setMem_gpr], by simp only [State.setMem_rd],
      by simp only [State.setMem_wr], fun _ _ => by simp only [State.setMem_lane]⟩

namespace MulSetY

open MulAccY (aP fP gP tP F G wordAt_ystore)

/-- After `i` groups of 32 coefficients. -/
structure Inv (s₀ : State) (i : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = coeffAddr (fP s₀) (32 * i)
  rdx : s.gpr .rdx = coeffAddr (gP s₀) (32 * i)
  rdi : s.gpr .rdi = wAddr (aP s₀) (32 * i)
  r8 : s.gpr .r8 = wAddr (tP s₀) (16 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  c : YConsts s
  r2 : ∀ l < 2, s.lane .xmm12 l = r2V
  frame : Frame [pR (aP s₀)] s₀.mem s.mem
  done : ∀ w < 32 * i, (wordAt s.mem (aP s₀) w).toNat = ((multiplyNTTs (F s₀) (G s₀))[accIdx w]!).val

section
variable {s₀ : State} (hp : MulAccY.ProdPre s₀)
include hp

set_option linter.unusedSimpArgs false in
theorem step {i : Nat} (hi : i < 8) {s : State} (hI : Inv s₀ i s) :
    WP isa (.block (mulSetBodyY ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  simp only [mulSetBodyY, mulNextY, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (MulAccY.prod_ok hp hi hI.rsi hI.rdx hI.r8 hI.rd hI.wr hI.c hI.r2 hI.frame)
    fun s6 ⟨V6, _, o16, n12, n14, n15⟩ => ?_
  have c6 : YConsts s6 := o16.consts hI.c n14 n15
  have di6 : s6.gpr .rdi = wAddr (aP s₀) (32 * i) := by rw [o16.gpr, hI.rdi]
  have hw6 : ∀ d, d + 32 ≤ 64 → InRegions s6.wr (s6.gpr .rdi + BitVec.ofNat 64 d) 32 := fun d hd => by
    rw [o16.wr, hI.wr, di6, wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨pR (aP s₀), hp.wr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  rw [List.cons_append, block_cons_iff]
  refine WP.mono (ystore_ok (h := .xmm1) (hw6 0 (by decide))) fun s7 ⟨hm7, g7, rd7, wr7, l7⟩ => ?_
  rw [List.cons_append, block_cons_iff]
  refine WP.mono (ystore_ok (h := .xmm2) (by rw [wr7, g7]; exact hw6 32 (by decide)))
    fun s8 ⟨hm8, g8, rd8, wr8, l8⟩ => ?_
  have sx128 : BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 (4 * 32) := by decide
  have sx64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (2 * 32) := by decide
  have e0 : s6.gpr .rdi + BitVec.ofNat 64 0 = wAddr (aP s₀) (32 * i) := by rw [di6, add_ofNat_zero]
  have e32 : s7.gpr .rdi + BitVec.ofNat 64 32 = wAddr (aP s₀) (32 * i + 16) := by
    rw [g7, di6, show (BitVec.ofNat 64 32) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add]
  rw [e0] at hm7
  rw [e32] at hm8
  have c8 : YConsts s8 := fun l hl =>
    ⟨by rw [State.proj_xmm, l8, l7]; exact (c6 l hl).q, by rw [State.proj_xmm, l8, l7]; exact (c6 l hl).qinv⟩
  vrunm [g8, g7, sx32, sx128, sx64]
  refine ⟨?_, by rw [o16.gpr], by rw [o16.gpr]⟩
  constructor
  all_goals try simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, setReg_mem, setFlags_mem, reduceCtorEq, ite_true, ite_false]
  case rsi => rw [o16.gpr, hI.rsi, coeffAddr_off, Nat.mul_succ]
  case rdx => rw [o16.gpr, hI.rdx, coeffAddr_off, Nat.mul_succ]
  case rdi => rw [di6, wAddr_add, Nat.mul_succ]
  case r8 => rw [o16.gpr, hI.r8, show (32 : BitVec 64) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add, Nat.mul_succ]
  case rd => rw [rd8, rd7, o16.rd, hI.rd]
  case wr => rw [wr8, wr7, o16.wr, hI.wr]
  case c =>
    exact lanes_gpr (s := s8) (fun r l => by simp only [lane_setReg, lane_setFlags]) (YOnly.refl [] s8) c8
      (by decide) (by decide)
  case r2 =>
    intro l hl
    simp only [lane_setReg, lane_setFlags]
    rw [l8, l7, o16.lane _ n12 l hl, hI.r2 l hl]
  case frame =>
    rw [hm8, hm7, o16.mem]
    exact (hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  case done =>
    intro w hw
    rw [hm8, hm7, o16.mem]
    by_cases h1 : w < 32 * i
    · rw [wordAt_write256 _ _ (by omega_arith) _ (by omega_arith), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)),
        wordAt_write256 _ _ (by omega_arith) _ (by omega_arith), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), hI.done w h1]
    by_cases h2 : w < 32 * i + 16
    · rw [wordAt_write256 _ _ (by omega_arith) _ (by omega_arith), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)),
        wordAt_ystore s6 _ _ _ (by omega_arith) (by omega_arith) (by omega_arith) h2,
        show accIdx w = 2 * pairY i ((w - 32 * i) / 8) ((w - 32 * i) % 8) by unfold accIdx pairY; omega_arith]
      exact (V6 _ (by omega_arith)).1 _ (Nat.mod_lt _ (by omega_arith))
    · rw [wordAt_ystore s7 _ _ _ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith), l7,
        show accIdx w = 2 * pairY i ((w - (32 * i + 16)) / 8) ((w - (32 * i + 16)) % 8) + 1 by
          unfold accIdx pairY; omega_arith]
      exact (V6 _ (by omega_arith)).2 _ (Nat.mod_lt _ (by omega_arith))

end

theorem correct {s₀ : State} (hp : (mulSetK accY tabY).pre s₀) :
    ∃ t s', Exec isa mulSetY s₀ t s' ∧ abiPreserved s₀ s' ∧ (mulSetK accY tabY).post s₀ s' := by
  have hp' := hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rA, _, _, _, _, _, _, _, _, _⟩ := hp'
  have hW : WP isa mulSetY s₀ fun s' => Acc16 s'.mem (aP s₀) (multiplyNTTs (F s₀) (G s₀)) ∧
      Frame [pR (aP s₀)] s₀.mem s'.mem := by
    unfold mulSetY
    refine WP.seq (WP.mono (MulAccY.pro_ok s₀) fun s1 ⟨hc1, hr1, h81, hm1, _, k1⟩ => ?_)
    refine WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide) (Inv s₀) (fun s g hy _ => ?_)
      fun i hi s hI => step (MulAccY.ProdPre.ofSet hp) hi hI) fun s5 hI => ⟨fun w hw => hI.done w (by omega_arith), hI.frame⟩
    have k := k1.trans g.keep
    have hl : ∀ r l, s.lane r l = s1.lane r l := fun r l => by
      simp only [State.lane]; rw [g.xmm, hy]
    refine ⟨?_, ?_, ?_, ?_, by rw [k.2.1], by rw [k.2.2], ?_, ?_, ?_, fun w hw => absurd hw (by omega_arith)⟩
    · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
    · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
    · rw [k.gpr (by decide)]; exact (add_ofNat_zero _).symm
    · rw [g.keep.gpr (by decide), h81]; exact (add_ofNat_zero _).symm
    · exact fun l hl' => ⟨by rw [State.proj_xmm, hl]; exact (hc1 l hl').q,
        by rw [State.proj_xmm, hl]; exact (hc1 l hl').qinv⟩
    · exact fun l hl' => by rw [hl]; exact hr1 l hl'
    · rw [g.mem, hm1]; exact Frame.refl _ _
  obtain ⟨t, s', he, ⟨hP, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rdi, .rsi, .r8] hW (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf
    (by simpa using rA)), hP⟩

end MulSetY

end VG.Proof.MlKem.X86_64
