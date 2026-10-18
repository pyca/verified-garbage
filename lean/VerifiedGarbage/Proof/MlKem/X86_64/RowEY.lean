module

public import VerifiedGarbage.Proof.MlKem.X86_64.RowY
meta import VerifiedGarbage.Proof.MlKem.X86_64.RowY
public import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
meta import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
public import VerifiedGarbage.Proof.MlKem.X86_64.VMem
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-KEM on x86-64: a row of products to an accumulator (`rowEY`)

`rowEY o k` sums the `k` products of the polynomials `fs` (`u32`s, `o` bytes
apart) and `gs` (accumulators, 512 bytes apart) as `rowY` does (`RowY.lean`),
and stores the sum, reduced, to the accumulator at `rdi` (`Acc16`), as
`mulSetY` stores a product (`AccY.lean`). The words of `g` are already in
`vbase`'s order, so each product loads them as they are (`acc_word`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## A product of a block -/

/-- The address of lane `l` of half `h` of block `b` of accumulator `j`. -/
theorem addrG (p : Addr) (b j h l : Nat) :
    wAddr p (32 * b) + BitVec.ofNat 64 (512 * j + 32 * h) + BitVec.ofNat 64 (16 * l) =
      wAddr (p + BitVec.ofNat 64 (512 * j)) (32 * b) + BitVec.ofNat 64 (32 * h) + BitVec.ofNat 64 (16 * l) := by
  simp only [wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (p + ·) (congrArg _ (by omega))

theorem addrBG (p : Addr) (b j h : Nat) :
    wAddr p (32 * b) + BitVec.ofNat 64 (512 * j + 32 * h) = p + BitVec.ofNat 64 (512 * j) + BitVec.ofNat 64 (64 * b + 32 * h) := by
  simp only [wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact congrArg (p + ·) (congrArg _ (by omega))

/-- Product `j` of block `b`, of `F` (stored as `R` says at `fB + o j`) and
`G` (the accumulator at `gB + 512 j`), in `ymm1` and `ymm2`, within `2q`. -/
theorem mulREg_ok {o : Nat} (R : FRep o) {fB gB : Addr} {F G : Poly} {b j : Nat} (hb : b < 8) {s : State}
    (hrsi : s.gpr .rsi = fB + BitVec.ofNat 64 (R.st * b)) (hrdx : s.gpr .rdx = wAddr gB (32 * b))
    (hF : R.Is s.mem (fB + BitVec.ofNat 64 (o * j)) F) (hG : Acc16 s.mem (gB + BitVec.ofNat 64 (512 * j)) G)
    (rF : InRegions (s.rd ++ s.wr) (fB + BitVec.ofNat 64 (o * j)) R.sz)
    (rG : ∀ h < 2, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (512 * j + 32 * h)) 32)
    (hc : YConsts s) (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun e => gamma (pairY b l e))) :
    WP isa (.block (rowMulEg R.ld j)) s fun s' =>
      (∀ l < 2, LanesR (RepR 2) ((s'.proj l).xmm .xmm1) (fun e => (multiplyNTTs F G)[2 * pairY b l e]!) ∧
        LanesR (RepR 2) ((s'.proj l).xmm .xmm2) (fun e => (multiplyNTTs F G)[2 * pairY b l e + 1]!)) ∧
      YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10] s s' := by
  simp only [rowMulEg, List.append_assoc]
  -- the loads of `f`, its even and odd coefficients
  rw [WP.block_append_iff]
  refine WP.mono (R.ok hb hrsi hF rF) fun s2 ⟨D2, o2⟩ => ?_
  -- the loads of `g`, its words in `vbase`'s order
  have rG' : ∀ h < 2, InRegions (s2.rd ++ s2.wr) (s2.gpr .rdx + BitVec.ofNat 64 (512 * j + 32 * h)) 32 :=
    fun h hh => by rw [o2.rd, o2.wr, o2.gpr]; exact rG h hh
  rw [WP.block_append_iff, show ∀ x y : Instr, [x, y] = [x] ++ [y] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (yld_ok (p := .rdx) (off := 512 * j) (d := .xmm6) (by simpa using rG' 0 (by decide)))
    fun s3 ⟨L3, o3⟩ => ?_
  have r10 : InRegions (s3.rd ++ s3.wr) (s3.gpr .rdx + BitVec.ofNat 64 (512 * j + 32)) 32 := by
    rw [o3.rd, o3.wr, o3.gpr]; simpa using rG' 1 (by decide)
  refine WP.mono (yld_ok (p := .rdx) (off := 512 * j + 32) (d := .xmm10) r10) fun s4 ⟨L4, o4⟩ => ?_
  have o14 := (o2.trans o3).trans o4
  have c4 : YConsts s4 := o14.consts hc (by decide) (by decide)
  have LF : ∀ l < 2, Lanes (s4.lane .xmm0 l) (fun e => F[2 * pairY b l e]!) ∧
      Lanes (s4.lane .xmm4 l) (fun e => F[2 * pairY b l e + 1]!) := fun l hl => by
    rw [o4.lane _ (by decide) l hl, o3.lane _ (by decide) l hl, o4.lane _ (by decide) l hl,
      o3.lane _ (by decide) l hl]
    exact D2 l hl
  have m2 : s2.mem = s.mem := o2.mem
  have g2 : s2.gpr .rdx = wAddr gB (32 * b) := by rw [o2.gpr, hrdx]
  have LG : ∀ l < 2, Lanes (s4.lane .xmm6 l) (fun e => G[2 * pairY b l e]!) ∧
      Lanes (s4.lane .xmm10 l) (fun e => G[2 * pairY b l e + 1]!) := fun l hl => by
    have e6 : s4.lane .xmm6 l = s.mem.readW (wAddr (gB + BitVec.ofNat 64 (512 * j)) (32 * b) +
        BitVec.ofNat 64 (32 * 0) + BitVec.ofNat 64 (16 * l)) 128 := by
      rw [o4.lane _ (by decide) l hl, L3 l hl, g2, m2, ← addrG, Nat.mul_zero, Nat.add_zero]
    have e10 : s4.lane .xmm10 l = s.mem.readW (wAddr (gB + BitVec.ofNat 64 (512 * j)) (32 * b) +
        BitVec.ofNat 64 (32 * 1) + BitVec.ofNat 64 (16 * l)) 128 := by
      rw [L4 l hl, o3.gpr, o3.mem, g2, m2, ← addrG, Nat.mul_one]
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rw [e6, acc_word _ _ _ _ _ he, hG _ (by omega), accIdx_eq (by decide) hl he, Nat.add_zero]
    · rw [e10, acc_word _ _ _ _ _ he, hG _ (by omega), accIdx_eq (by decide) hl he]
  have LZ : ∀ l < 2, ZLanes (s4.lane .xmm13 l) (fun e => gamma (pairY b l e)) := fun l hl => by
    rw [o14.lane _ (by decide) l hl]; exact hz l hl
  refine WP.mono (ylanes lane_vbaseL (P := fun l t =>
      LanesR (RepR 2) (t.xmm .xmm1) (fun e => (multiplyNTTs F G)[2 * pairY b l e]!) ∧
      LanesR (RepR 2) (t.xmm .xmm2) (fun e => (multiplyNTTs F G)[2 * pairY b l e + 1]!))
    fun l hl => WP.mono (vbaseL_ok (c4 l hl) (LF l hl).1 (LF l hl).2 (LG l hl).1 (LG l hl).2 (LZ l hl))
      fun _ ⟨a, b', c⟩ => ⟨⟨fun e he => rel_of_eq (a e he) (prod_even _ _ (by unfold pairY; omega)).symm,
        fun e he => rel_of_eq (b' e he) (prod_odd _ _ (by unfold pairY; omega)).symm⟩, c⟩)
    fun s5 ⟨V5, o5⟩ => ⟨V5, (o14.trans o5).mono (by simp)⟩

/-! ## The products of a block -/

/-- The products `0, …, n` of block `b`, of the polynomials `fs` (from `fB`,
`o` bytes apart) and the accumulators `gs` (from `gB`, 512 bytes apart),
summed in `ymm11` and `ymm12`, within `2(n + 1)q`. -/
theorem prodsREg_ok {o : Nat} (R : FRep o) {fB gB : Addr} {fs gs : List Poly} {b : Nat} (hb : b < 8) {s : State}
    (hrsi : s.gpr .rsi = fB + BitVec.ofNat 64 (R.st * b)) (hrdx : s.gpr .rdx = wAddr gB (32 * b))
    (hc : YConsts s) (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun e => gamma (pairY b l e))) :
    ∀ {n : Nat}, n + 1 ≤ 4 → n + 1 ≤ fs.length → n + 1 ≤ gs.length →
    (∀ j < n + 1, R.Is s.mem (fB + BitVec.ofNat 64 (o * j)) fs[j]!) →
    (∀ j < n + 1, Acc16 s.mem (gB + BitVec.ofNat 64 (512 * j)) gs[j]!) →
    (∀ j < n + 1, InRegions (s.rd ++ s.wr) (fB + BitVec.ofNat 64 (o * j)) R.sz) →
    (∀ j < n + 1, ∀ h < 2, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (512 * j + 32 * h)) 32) →
    WP isa (.block (rowSums (rowMulEg R.ld) (n + 1))) s fun s' =>
      (∀ l < 2, LanesR (RepR (2 * (n + 1))) ((s'.proj l).xmm .xmm11)
          (fun e => (dotP fs gs (n + 1))[2 * pairY b l e]!) ∧
        LanesR (RepR (2 * (n + 1))) ((s'.proj l).xmm .xmm12)
          (fun e => (dotP fs gs (n + 1))[2 * pairY b l e + 1]!)) ∧
      YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12] s s' := by
  intro n
  induction n with
  | zero =>
    intro _ hfl hgl hF hG rF rG
    have e1 : dotP fs gs (0 + 1) = multiplyNTTs fs[0]! gs[0]! := by
      rw [dotP_succ (by omega) (by omega), dotP_zero, zero_add_poly]
    rw [e1]
    simp only [rowSums, rowSum, List.nil_append, ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (mulREg_ok R (j := 0) (F := fs[0]!) (G := gs[0]!) hb hrsi hrdx (hF 0 (by decide)) (hG 0 (by decide))
      (rF 0 (by decide)) (rG 0 (by decide)) hc hz) fun s1 ⟨V1, o1⟩ => ?_
    refine WP.mono (ylanes lane_accSet (P := fun l t =>
        t.xmm .xmm11 = (s1.proj l).xmm .xmm1 ∧ t.xmm .xmm12 = (s1.proj l).xmm .xmm2)
      fun l _ => accSet_ok (s1.proj l)) fun s2 ⟨S2, o2⟩ => ⟨fun l hl => ?_, (o1.trans o2).mono (by simp)⟩
    rw [(S2 l hl).1, (S2 l hl).2]
    exact V1 l hl
  | succ n ih =>
    intro hn hfl hgl hF hG rF rG
    have e1 : dotP fs gs (n + 1 + 1) = VG.Spec.MlKem.add (dotP fs gs (n + 1)) (multiplyNTTs fs[n + 1]! gs[n + 1]!) :=
      dotP_succ (by omega) (by omega)
    rw [show rowSums (rowMulEg R.ld) (n + 1 + 1) = rowSums (rowMulEg R.ld) (n + 1) ++ rowSum (rowMulEg R.ld) (n + 1)
      from rfl,
      WP.block_append_iff]
    refine WP.mono (ih (by omega) (by omega) (by omega) (fun j hj => hF j (by omega)) (fun j hj => hG j (by omega))
      (fun j hj => rF j (by omega)) (fun j hj => rG j (by omega))) fun s1 ⟨A1, o1⟩ => ?_
    simp only [rowSum, Nat.add_one_ne_zero, ite_false]
    rw [WP.block_append_iff]
    refine WP.mono (mulREg_ok R (j := n + 1) (F := fs[n + 1]!) (G := gs[n + 1]!) hb (by rw [o1.gpr, hrsi])
      (by rw [o1.gpr, hrdx]) (by rw [o1.mem]; exact hF (n + 1) (by omega)) (by rw [o1.mem]; exact hG (n + 1) (by omega))
      (by rw [o1.rd, o1.wr]; exact rF (n + 1) (by omega))
      (by rw [o1.rd, o1.wr, o1.gpr]; exact rG (n + 1) (by omega)) (o1.consts hc (by decide) (by decide))
      (fun l hl => by rw [o1.lane _ (by decide) l hl]; exact hz l hl)) fun s2 ⟨V2, o2⟩ => ?_
    refine WP.mono (ylanes lane_accAdd (P := fun l t =>
        (∀ i < 8, word (t.xmm .xmm11) i = word ((s2.proj l).xmm .xmm11) i + word ((s2.proj l).xmm .xmm1) i) ∧
        (∀ i < 8, word (t.xmm .xmm12) i = word ((s2.proj l).xmm .xmm12) i + word ((s2.proj l).xmm .xmm2) i))
      fun l _ => WP.mono (accAdd_ok (s2.proj l)) fun _ ⟨a, b', c⟩ => ⟨⟨a, b'⟩, c⟩)
      fun s3 ⟨S3, o3⟩ => ⟨fun l hl => ⟨fun e he => ?_, fun e he => ?_⟩, ((o1.trans o2).trans o3).mono (by simp)⟩
    · have a11 : (s2.proj l).xmm .xmm11 = (s1.proj l).xmm .xmm11 := by
        rw [State.proj_xmm, State.proj_xmm, o2.lane _ (by decide) l hl]
      rw [(S3 l hl).1 e he, a11, e1]
      dsimp only
      rw [add_get _ _ (pairY_lt hb hl he |> Nat.lt_of_succ_lt)]
      exact (RepR.add ((A1 l hl).1 e he) ((V2 l hl).1 e he) (show 2 * (n + 1) + 2 ≤ 9 by omega))
    · have a12 : (s2.proj l).xmm .xmm12 = (s1.proj l).xmm .xmm12 := by
        rw [State.proj_xmm, State.proj_xmm, o2.lane _ (by decide) l hl]
      rw [(S3 l hl).2 e he, a12, e1]
      dsimp only
      rw [add_get _ _ (pairY_lt hb hl he)]
      exact (RepR.add ((A1 l hl).2 e he) ((V2 l hl).2 e he) (show 2 * (n + 1) + 2 ≤ 9 by omega))

/-! ## A block of a row -/

/-- An accumulator, in memory that writes elsewhere kept. -/
theorem acc16_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (sR p).Disjoint r) {F : Poly} (h : Acc16 m p F) : Acc16 m' p F := fun w hw => by
  rw [show wordAt m' p w = wordAt m p w from
    hf.readW (r := sR p) (Offset.contains_base p (by omega) (by omega)) hd (by decide)]
  exact h w hw

namespace RowEY

/-- What a row needs of its arguments: the accumulator at `aP`, the `k`
polynomials of `fs` from `fB` (`o` bytes apart) and the accumulators of `gs`
from `gB` (512 bytes apart), the table of the `γ`s at `C + 3328`, in the
memory `m₀` and the regions `RD` and `WR`. -/
structure Ctx (o k : Nat) (fB gB aP C : Addr) (fs gs : List Poly) (m₀ : Mem) (RD WR : List Region) : Prop where
  k1 : 1 ≤ k
  k4 : k ≤ 4
  fl : k ≤ fs.length
  gl : k ≤ gs.length
  F : ∀ j < k, PolyIs m₀ (fB + BitVec.ofNat 64 (o * j)) fs[j]!
  G : ∀ j < k, Acc16 m₀ (gB + BitVec.ofNat 64 (512 * j)) gs[j]!
  dF : ∀ j < k, (sR aP).Disjoint (pR (fB + BitVec.ofNat 64 (o * j)))
  dG : ∀ j < k, (sR aP).Disjoint (sR (gB + BitVec.ofNat 64 (512 * j)))
  dT : (sR aP).Disjoint (tabR C)
  inF : ∀ j < k, InRegions (RD ++ WR) (fB + BitVec.ofNat 64 (o * j)) 1024
  inG : ∀ j < k, InRegions (RD ++ WR) (gB + BitVec.ofNat 64 (512 * j)) 512
  inTab : InRegions (RD ++ WR) (C + BitVec.ofNat 64 3328) 256
  inA : InRegions WR aP 512
  tab : TabY m₀ C

/-- `Ctx` of polynomials `f` stored as `R` says. -/
structure CtxG {o : Nat} (R : FRep o) (k : Nat) (fB gB aP C : Addr) (fs gs : List Poly) (m₀ : Mem)
    (RD WR : List Region) : Prop where
  k1 : 1 ≤ k
  k4 : k ≤ 4
  fl : k ≤ fs.length
  gl : k ≤ gs.length
  F : ∀ j < k, R.Is m₀ (fB + BitVec.ofNat 64 (o * j)) fs[j]!
  G : ∀ j < k, Acc16 m₀ (gB + BitVec.ofNat 64 (512 * j)) gs[j]!
  dF : ∀ j < k, (sR aP).Disjoint ⟨fB + BitVec.ofNat 64 (o * j), R.sz⟩
  dG : ∀ j < k, (sR aP).Disjoint (sR (gB + BitVec.ofNat 64 (512 * j)))
  dT : (sR aP).Disjoint (tabR C)
  inF : ∀ j < k, InRegions (RD ++ WR) (fB + BitVec.ofNat 64 (o * j)) R.sz
  inG : ∀ j < k, InRegions (RD ++ WR) (gB + BitVec.ofNat 64 (512 * j)) 512
  inTab : InRegions (RD ++ WR) (C + BitVec.ofNat 64 3328) 256
  inA : InRegions WR aP 512
  tab : TabY m₀ C

theorem Ctx.toG {o k : Nat} {fB gB aP C : Addr} {fs gs : List Poly} {m₀ : Mem} {RD WR : List Region}
    (h : Ctx o k fB gB aP C fs gs m₀ RD WR) : CtxG (FRep.u32 o) k fB gB aP C fs gs m₀ RD WR :=
  ⟨h.k1, h.k4, h.fl, h.gl, h.F, h.G, h.dF, h.dG, h.dT, h.inF, h.inG, h.inTab, h.inA, h.tab⟩

/-- After `b` blocks of a row. -/
structure Inv {o : Nat} (R : FRep o) (k : Nat) (fB gB aP C : Addr) (fs gs : List Poly) (m₀ : Mem)
    (RD WR : List Region) (b : Nat) (s : State) : Prop where
  rsi : s.gpr .rsi = fB + BitVec.ofNat 64 (R.st * b)
  rdx : s.gpr .rdx = wAddr gB (32 * b)
  rdi : s.gpr .rdi = wAddr aP (32 * b)
  r8 : s.gpr .r8 = wAddr (C + BitVec.ofNat 64 3328) (16 * b)
  rd : s.rd = RD
  wr : s.wr = WR
  c : YConsts s
  frame : Frame [sR aP] m₀ s.mem
  done : ∀ w < 32 * b, (wordAt s.mem aP w).toNat = ((dotP fs gs k)[accIdx w]!).val

section
variable {o k : Nat} {R : FRep o} {fB gB aP C : Addr} {fs gs : List Poly} {m₀ : Mem} {RD WR : List Region}
  (hx : CtxG R k fB gB aP C fs gs m₀ RD WR)
include hx

set_option linter.unusedSimpArgs false in
theorem step {b : Nat} (hb : b < 8) {s : State} (hI : Inv R k fB gB aP C fs gs m₀ RD WR b s) :
    WP isa (.block (rowBodyEg R.ld R.stv k ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      Inv R k fB gB aP C fs gs m₀ RD WR (b + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hx.k1; omega⟩
  have hrr : s.rd ++ s.wr = RD ++ WR := by rw [hI.rd, hI.wr]
  rw [show rowBodyEg R.ld R.stv (n + 1) ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
      [.vmovdquLoad .l256 .xmm13 (at_ .r8 0)] ++ (rowSums (rowMulEg R.ld) (n + 1) ++ (yconst .xmm13 0x05490549 ++
        (toY (vmont .xmm11 .xmm13 .xmm3 ++ vcadd .xmm11 .xmm3 ++ vmont .xmm12 .xmm13 .xmm3 ++ vcadd .xmm12 .xmm3) ++
        ([.vmovdquStore .l256 (at_ .rdi 0) .xmm11] ++ ([.vmovdquStore .l256 (at_ .rdi 32) .xmm12] ++
        ([.alu .add .rsi (.imm R.stv), .alu .add .rdx (.imm 64), .alu .add .rdi (.imm 64), .alu .add .r8 (.imm 32),
          .alu .sub .rcx (.imm 1)] : List Instr))))))
      from by simp [rowBodyEg], WP.block_append_iff]
  -- the `γ`s of block `b`
  have hz0 : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 0) 32 := by
    rw [hrr, hI.r8, wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact CallLay.inRegions_sub hx.inTab (by omega) (by omega)
  refine WP.mono (yld_ok hz0) fun s1 ⟨Z1, o1⟩ => ?_
  have hTs : TabY s.mem C := tabY.frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hx.dT.symm)
    hx.tab
  have LZ : ∀ l < 2, ZLanes (s1.lane .xmm13 l) (fun e => gamma (pairY b l e)) := fun l hl e he => by
    rw [Z1 l hl, hI.r8, word_readW _ _ he, wAddr, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
      show 2 * (16 * b) + (0 + (16 * l + 2 * e)) = 2 * (16 * b + 8 * l + e) by omega, ← wAddr, ← wordAt,
      hTs _ (by omega), gTabY, gIdxY_eq hl he, gTab_eq]
  -- the products
  rw [WP.block_append_iff]
  have hF1 : ∀ j < n + 1, R.Is s1.mem (fB + BitVec.ofNat 64 (o * j)) fs[j]! := fun j hj => by
    rw [o1.mem]
    exact R.frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact (hx.dF j hj).symm) (hx.F j hj)
  have hG1 : ∀ j < n + 1, Acc16 s1.mem (gB + BitVec.ofNat 64 (512 * j)) gs[j]! := fun j hj => by
    rw [o1.mem]
    exact acc16_frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact (hx.dG j hj).symm) (hx.G j hj)
  refine WP.mono (prodsREg_ok R hb (by rw [o1.gpr, hI.rsi]) (by rw [o1.gpr, hI.rdx])
    (o1.consts hI.c (by decide) (by decide)) LZ hx.k4 hx.fl hx.gl hF1 hG1
    (fun j hj => by rw [o1.rd, o1.wr, hrr]; exact hx.inF j hj)
    (fun j hj h hh => by
      rw [o1.rd, o1.wr, o1.gpr, hrr, hI.rdx, addrBG]
      exact CallLay.inRegions_sub (hx.inG j hj) (by omega) (by omega))) fun s2 ⟨A2, o2⟩ => ?_
  have o12 := o1.trans o2
  have c2 : YConsts s2 := o12.consts hI.c (by decide) (by decide)
  -- `R² mod q`, and the sums reduced
  rw [WP.block_append_iff]
  refine WP.mono (yconst_ok .xmm13 _ s2) fun s3 ⟨R3, k3, m3, x3, lo3⟩ => ?_
  have c3 : YConsts s3 := fun l hl =>
    ⟨by rw [State.proj_xmm, lo3 _ (by decide) l hl, ← State.proj_xmm]; exact (c2 l hl).q,
      by rw [State.proj_xmm, lo3 _ (by decide) l hl, ← State.proj_xmm]; exact (c2 l hl).qinv⟩
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_accRed (P := fun l t =>
      (∀ i < 8, word (t.xmm .xmm11) i = W.caddW (W.montW (word ((s3.proj l).xmm .xmm11) i)
        (word ((s3.proj l).xmm .xmm13) i))) ∧
      (∀ i < 8, word (t.xmm .xmm12) i = W.caddW (W.montW (word ((s3.proj l).xmm .xmm12) i)
        (word ((s3.proj l).xmm .xmm13) i))))
    fun l hl => WP.mono (accRed_ok (c3 l hl)) fun _ ⟨a, b', c⟩ => ⟨⟨a, b'⟩, c⟩) fun s4 ⟨Q4, o4⟩ => ?_
  have hk9 : 2 * (n + 1) ≤ 9 := by have := hx.k4; omega
  have can : ∀ l < 2, ∀ e < 8, (word (s4.lane .xmm11 l) e).toNat = ((dotP fs gs (n + 1))[2 * pairY b l e]!).val ∧
      (word (s4.lane .xmm12 l) e).toNat = ((dotP fs gs (n + 1))[2 * pairY b l e + 1]!).val := fun l hl e he => by
    have r13 : word ((s3.proj l).xmm .xmm13) e = W.r2W := by rw [State.proj_xmm, R3 l hl, RowY.r2D, word_r2V he]
    have a11 : (s3.proj l).xmm .xmm11 = (s2.proj l).xmm .xmm11 := by
      rw [State.proj_xmm, State.proj_xmm, lo3 _ (by decide) l hl]
    have a12 : (s3.proj l).xmm .xmm12 = (s2.proj l).xmm .xmm12 := by
      rw [State.proj_xmm, State.proj_xmm, lo3 _ (by decide) l hl]
    refine ⟨?_, ?_⟩
    · rw [← State.proj_xmm, (Q4 l hl).1 e he, r13, a11]
      exact cadd_rep (red2_rep ((A2 l hl).1 e he) hk9)
    · rw [← State.proj_xmm, (Q4 l hl).2 e he, r13, a12]
      exact cadd_rep (red2_rep ((A2 l hl).2 e he) hk9)
  -- the registers and memory the arithmetic left
  have g4 : ∀ r, r ≠ .rax → s4.gpr r = s.gpr r := fun r hr => by
    rw [o4.gpr, k3.gpr (by simpa using hr), o12.gpr]
  have m4 : s4.mem = s.mem := by rw [o4.mem, m3, o12.mem]
  have hw4 : s4.wr = WR := by rw [o4.wr, k3.2.2, o12.wr, hI.wr]
  have hrd4 : s4.rd = RD := by rw [o4.rd, k3.2.1, o12.rd, hI.rd]
  have di4 : s4.gpr .rdi = wAddr aP (32 * b) := by rw [g4 _ (by decide), hI.rdi]
  have hw : ∀ d, d + 32 ≤ 64 → InRegions s4.wr (s4.gpr .rdi + BitVec.ofNat 64 d) 32 := fun d hd => by
    rw [hw4, di4, wAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact CallLay.inRegions_sub hx.inA (by omega) (by omega)
  -- the sums, stored
  rw [WP.block_append_iff]
  refine WP.mono (ystore_ok (h := .xmm11) (hw 0 (by decide))) fun s5 ⟨hm5, g5, rd5, wr5, l5⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ystore_ok (h := .xmm12) (by rw [wr5, g5]; exact hw 32 (by decide)))
    fun s6 ⟨hm6, g6, rd6, wr6, l6⟩ => ?_
  have sx64 : BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (2 * 32) := by decide
  have sx32 : BitVec.signExtend 64 (32 : BitVec 32) = BitVec.ofNat 64 (2 * 16) := by decide
  have e0 : s4.gpr .rdi + BitVec.ofNat 64 0 = wAddr aP (32 * b) := by rw [di4, add_ofNat_zero]
  have e32 : s5.gpr .rdi + BitVec.ofNat 64 32 = wAddr aP (32 * b + 16) := by
    rw [g5, di4, show (BitVec.ofNat 64 32) = BitVec.ofNat 64 (2 * 16) from rfl, wAddr_add]
  rw [e0] at hm5
  rw [e32] at hm6
  have c6 : YConsts s6 := fun l hl => by
    have c4 : YConsts s4 := o4.consts c3 (by decide) (by decide)
    exact ⟨by rw [State.proj_xmm, l6, l5]; exact (c4 l hl).q, by rw [State.proj_xmm, l6, l5]; exact (c4 l hl).qinv⟩
  vrunm [g6, g5, sx32, R.hst, sx64]
  refine ⟨?_, by rw [g4 _ (by decide)], by rw [g4 _ (by decide)]⟩
  constructor
  all_goals try simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, setReg_mem, setFlags_mem, reduceCtorEq, ite_true, ite_false]
  case rsi => rw [g4 _ (by decide), hI.rsi, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]
  case rdx => rw [g4 _ (by decide), hI.rdx, wAddr_add, Nat.mul_succ]
  case rdi => rw [di4, wAddr_add, Nat.mul_succ]
  case r8 => rw [g4 _ (by decide), hI.r8, wAddr_add, Nat.mul_succ]
  case rd => rw [rd6, rd5, hrd4]
  case wr => rw [wr6, wr5, hw4]
  case c =>
    exact lanes_gpr (s := s6) (fun r l => by simp only [lane_setReg, lane_setFlags]) (YOnly.refl [] s6) c6
      (by decide) (by decide)
  case frame =>
    rw [hm6, hm5, m4]
    exact (hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  case done =>
    intro w hw
    rw [hm6, hm5, m4]
    by_cases h1 : w < 32 * b
    · rw [wordAt_write256 _ _ (by omega) _ (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        wordAt_write256 _ _ (by omega) _ (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega)), hI.done w h1]
    by_cases h2 : w < 32 * b + 16
    · rw [wordAt_write256 _ _ (by omega) _ (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        MulAccY.wordAt_ystore s4 _ _ _ (by omega) (by omega) (by omega) h2,
        show accIdx w = 2 * pairY b ((w - 32 * b) / 8) ((w - 32 * b) % 8) by unfold accIdx pairY; omega]
      exact (can _ (by omega) _ (Nat.mod_lt _ (by omega))).1
    · rw [MulAccY.wordAt_ystore s5 _ _ _ (by omega) (by omega) (by omega) (by omega), l5,
        show accIdx w = 2 * pairY b ((w - (32 * b + 16)) / 8) ((w - (32 * b + 16)) % 8) + 1 by
          unfold accIdx pairY; omega]
      exact (can _ (by omega) _ (Nat.mod_lt _ (by omega))).2

end

/-! ## A row -/

/-- `rowEg R.ld R.stv k`: the accumulator at `aP` of the sum of the products of
the `k` polynomials from `fB` (stored as `R` says) and accumulators from `gB`. -/
theorem rowEg_ok {o k : Nat} (R : FRep o) {fB gB aP C : Addr} {fs gs : List Poly} {s : State}
    (hx : CtxG R k fB gB aP C fs gs s.mem s.rd s.wr) (hrsi : s.gpr .rsi = fB) (hrdx : s.gpr .rdx = gB)
    (hrdi : s.gpr .rdi = aP) (hrcx : s.gpr .rcx = C) :
    WP isa (rowEg R.ld R.stv k) s fun s' => Acc16 s'.mem aP (dotP fs gs k) ∧
      Frame [sR aP] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold rowEg
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (yconsts_ok s) fun s1 ⟨c1, m1, k1⟩ => ?_
  have sx : BitVec.signExtend 64 (BitVec.ofNat 32 3328) = BitVec.ofNat 64 3328 := by decide
  refine WP.mono (Q := fun (s2 : State) => s2.gpr .r8 = C + BitVec.ofNat 64 3328 ∧ s2.gpr .rsi = fB ∧
      s2.gpr .rdx = gB ∧ s2.gpr .rdi = aP ∧ s2.rd = s.rd ∧ s2.wr = s.wr ∧ s2.mem = s.mem ∧ YConsts s2)
    (by
      simp only [leaR, oTabY]
      vrunm [sx]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun l hl => ⟨(c1 l hl).q, (c1 l hl).qinv⟩⟩
      · rw [k1.gpr (by decide), hrcx]
      · rw [k1.gpr (by decide), hrsi]
      · rw [k1.gpr (by decide), hrdx]
      · rw [k1.gpr (by decide), hrdi]
      · exact k1.2.1
      · exact k1.2.2
      · exact m1) fun s2 ⟨h8, h2si, h2dx, h2di, h2rd, h2wr, h2m, c2⟩ => ?_
  refine WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide) (Inv R k fB gB aP C fs gs s.mem s.rd s.wr)
    (fun u o hy _ =>
      { rsi := by rw [o.keep.gpr (by decide), h2si, Nat.mul_zero, add_ofNat_zero]
        rdx := by rw [o.keep.gpr (by decide), h2dx, show 32 * 0 = 0 from rfl, wAddr, Nat.mul_zero, add_ofNat_zero]
        rdi := by rw [o.keep.gpr (by decide), h2di, show 32 * 0 = 0 from rfl, wAddr, Nat.mul_zero, add_ofNat_zero]
        r8 := by rw [o.keep.gpr (by decide), h8, RowY.wAddr_zero]
        rd := by rw [o.keep.2.1, h2rd]
        wr := by rw [o.keep.2.2, h2wr]
        c := fun l hl =>
          ⟨by rw [State.proj_xmm, show u.lane .xmm15 l = s2.lane .xmm15 l by simp only [State.lane]; rw [o.xmm, hy],
              ← State.proj_xmm]; exact (c2 l hl).q,
            by rw [State.proj_xmm, show u.lane .xmm14 l = s2.lane .xmm14 l by simp only [State.lane]; rw [o.xmm, hy],
              ← State.proj_xmm]; exact (c2 l hl).qinv⟩
        frame := by rw [o.mem, h2m]; exact Frame.refl _ _
        done := fun w hw => absurd hw (by omega) })
    fun b hb u hI => step hx hb hI) fun u hI => ⟨fun w hw => hI.done w (by omega), hI.frame, hI.rd, hI.wr⟩

/-- `rowEY o k`: `rowEg_ok` of polynomials of `u32`s. -/
theorem rowEY_ok {o k : Nat} {fB gB aP C : Addr} {fs gs : List Poly} {s : State}
    (hx : Ctx o k fB gB aP C fs gs s.mem s.rd s.wr) (hrsi : s.gpr .rsi = fB) (hrdx : s.gpr .rdx = gB)
    (hrdi : s.gpr .rdi = aP) (hrcx : s.gpr .rcx = C) :
    WP isa (rowEY o k) s fun s' => Acc16 s'.mem aP (dotP fs gs k) ∧
      Frame [sR aP] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  rowEg_ok (FRep.u32 o) hx.toG hrsi hrdx hrdi hrcx

end RowEY

/-- What `rowEY` may write: `rax` (the constants), `rcx` (the count) and the
pointers. -/
theorem rowEY_wo {o k : Nat} (hk : k = 3 ∨ k = 4) (ho : o = 1024 ∨ o = 1024 * k) :
    writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8] (rowEY o k) = true := by
  rcases hk with rfl | rfl <;> rcases ho with rfl | rfl <;> decide +kernel

end VG.Proof.MlKem.X86_64
