module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallSample
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.X86_64.Round
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Entry
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.MlKem.X86_64.VLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLanes
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `MlDsa.X86_64.Verify.Blocks`, which this module and modules that import it used -/

section

/-!
# ML-DSA verification on x86-64: the blocks between the calls

A byte store (`setB_ok`), a copy (`copy_ok`), the mask of a sampler's output
by its result (`mask_ok`: unchanged if 1, zero if 0), and the updates of the
result in `r15` (`and15_ok`, `mov15_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlKem.X86_64 (at_)
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## A byte -/

theorem b8_ofNat {v : Nat} (_hv : v < 256) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.ofNat 32 v)) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using []

theorem setB_ok (p : Ptr) (v : Nat) (hr : p.1 ≠ .rax) (hv : v < 256) (s : State)
    (hw : InRegions s.wr (pa s p) 1) :
    WP isa (.block (setB p v)) s fun s' =>
      s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v) ∧ Keep [.rax] s s' := by
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.mem = s.mem.writeW (pa s p) (BitVec.ofNat 8 v)) ?_ (by rfl))
    fun s' ⟨h, k⟩ => ⟨h, k⟩
  unfold setB
  have e : s.ea (at_ p.1 p.2) = pa s p := ea_at s p.1 p.2
  xrun [hw, hr, b8_ofNat hv, e]

/-! ## A copy -/

theorem b8b (x : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega_using []

theorem copyBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1) (h1 : InRegions s.wr (s.gpr .rdi) 1) :
    WP isa (.block [.movzx8 .rax (at_ .rsi 0), .store8 (at_ .rdi 0) .rax, .alu .add .rdi (.imm 1),
      .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (s.mem (s.gpr .rsi)) ∧ s'.gpr .rdi = s.gpr .rdi + 1 ∧
        s'.gpr .rsi = s.gpr .rsi + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdi, .rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  xrun [h0, h1, b8b]

theorem inRegions_byte {rs : List Region} {a : Addr} {n k : Nat} (h : InRegions rs a n) (hk : k < n)
    (hn : n < 2 ^ 64) : InRegions rs (a + BitVec.ofNat 64 k) 1 := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega_using [hk, hn])]; exact hk)⟩

abbrev copyArgs (dst src : Ptr) (n : Nat) : List (Reg × Arg) := [(.rdi, .ptr dst), (.rsi, .ptr src), (.rcx, .imm n)]

theorem copy_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {dst src : Ptr} {n : Nat}
    (hn0 : 0 < n) (hsd : sepB (rbs ++ wbs) src n dst n = true) (hw : inB wbs dst n = true) :
    WP isa (copy dst src n) s fun s' => PPostB s s' [(dst, n)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (pa s dst) n = bytesAt s.mem (pa s src) n := by
  have hsd' := sepB_spec hsd
  have hS := L.ok
  have hn : n < 2 ^ 31 := by
    obtain ⟨m, hm, hl⟩ := inB_spec hsd'.1; have := (hS _ hm).1; omega
  have hok : ∀ a ∈ copyArgs dst src n, a.2.Ok ∧ a.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨ptr_ok hS hsd'.2.1, by decide⟩, ⟨ptr_ok hS hsd'.1, by decide⟩, ⟨hn, by decide⟩⟩
  have hrd := L.inR hsd'.1
  have hwr := L.inW hw
  have hdj := L.disj hsd
  unfold copy
  refine WP.seq (WP.mono (glue_ok' hok (by simp only [List.map_cons, List.map_nil]; decide) s)
    fun s1 (h1 : Args (copyArgs dst src n) s s1) => ?_)
  refine WP.mono (wp_countdown (cnt := .rcx) (N := n) (by omega_using [hn]) hn0 (fun k s' =>
      s'.gpr .rdi = pa s dst + BitVec.ofNat 64 k ∧ s'.gpr .rsi = pa s src + BitVec.ofNat 64 k ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨pa s dst, n⟩] s.mem s'.mem ∧
      (∀ j < k, s'.mem (pa s dst + BitVec.ofNat 64 j) = s.mem (pa s src + BitVec.ofNat 64 j)) ∧
      Keep argRegs s s')
    (fun k hk s' ⟨hdi, hsi, hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [h1.r0]; simp [Arg.val], by rw [h1.r1]; simp [Arg.val], h1.2.2.1, h1.2.2.2,
      by rw [h1.1.2]; exact Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _), h1.2⟩ (by rw [h1.r2]; rfl))
    fun s' ⟨_, _, _, _, hf, hc, kk⟩ => ⟨postB_of_keep kk (by decide) (by simpa using hf), kk.gpr (by decide), ?_⟩
  · refine WP.mono (copyBody_ok s' (by rw [hrd', hwr', hsi]; exact inRegions_byte hrd hk (by omega_using [hn]))
      (by rw [hwr', hdi]; exact inRegions_byte hwr hk (by omega_using [hn]))) fun s'' ⟨⟨hm, hdi', hsi', hcx, hz⟩, k'⟩ =>
        ⟨⟨by rw [hdi', hdi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, BitVec.ofNat_add],
          by rw [hsi', hsi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, BitVec.ofNat_add],
          k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_, (kk.trans k').mono (by decide)⟩, hcx, hz⟩
    · rw [hm, hdi]
      exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega_using [hk]) (by omega_using [hn]))
    · have hsrc : s'.mem (pa s src + BitVec.ofNat 64 k) = s.mem (pa s src + BitVec.ofNat 64 k) :=
        hf.bytes (R := ⟨pa s src, n⟩) (by simpa using hdj) (show n ≤ 2 ^ 64 by omega_using [hn]) hk
      rw [hm, hdi, hsi, VG.WriteBytes.writeW8_apply]
      by_cases e : j = k
      · subst e; rw [ifp rfl, hsrc]
      · rw [ifn (fun h => e (by have := congrArg BitVec.toNat h; simp at this; omega_using [hn, hk, hj, this])), hc j (by omega_using [hj, e])]
  · simp only [bytesAt]
    exact List.map_congr_left fun i hi => hc i (List.mem_range.mp hi)


/-! ## The mask -/

theorem maskPre_ok (s : State) :
    WP isa (.block [.mov32 .rdx (.imm 0), .alu32 .sub .rdx (.reg .rax), .xop (.movq .xmm0 .rdx),
      .xop (.pshufd .xmm0 .xmm0 0)]) s fun s' =>
      (s'.mem = s.mem ∧ ∀ j < 4, dword (s'.xmm .xmm0) j = 0 - (s.gpr .rax).setWidth 32) ∧ Keep [.rdx] s s' := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  vrunm
  intro j hj
  rw [show (0 : BitVec 8) = BitVec.ofNat 8 (0x55 * 0) from rfl, dword_shufDwords_bcast _ (by decide) hj]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [dword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append, ifp (by omega_using [hi]), BitVec.getLsbD_setWidth]
  simp [hi, show i < 64 by omega_using [hi]]

theorem maskBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16) (h1 : InRegions s.wr (s.gpr .rdi) 16) :
    WP isa (.block [.movdquLoad .xmm1 (at_ .rdi 0), .xop (.bin .pand .xmm1 .xmm0), .movdquStore (at_ .rdi 0) .xmm1,
      .alu .add .rdi (.imm 16), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (s.mem.readW (s.gpr .rdi) 128 &&& s.xmm .xmm0) ∧
        s'.gpr .rdi = s.gpr .rdi + 16 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.xmm .xmm0 = s.xmm .xmm0 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  vrunm [h0, h1]
  rfl

theorem dword_and (a b : BitVec 128) (i : Nat) : dword (a &&& b) i = dword a i &&& dword b i :=
  VG.Proof.MlDsa.X86_64.Arith.dword_pand a b i

theorem coeffAt_def (m : Mem) (p : Addr) (i : Nat) : m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = coeffAt m p i :=
  rfl

/-- A coefficient after a write of the 16 bytes at coefficient `4 k`. -/
theorem coeffAt_writeW16 (m : Mem) (p : Addr) {N i k : Nat} (hN : 4 * N < 2 ^ 63) (hi : i < N) (hk : 4 * k + 4 ≤ N)
    (v : BitVec 128) :
    coeffAt (m.writeW (p + BitVec.ofNat 64 (16 * k)) v) p i =
      if 4 * k ≤ i ∧ i < 4 * k + 4 then dword v (i - 4 * k) else coeffAt m p i := by
  unfold coeffAt
  split
  · rename_i h
    have e := readW_writeW_inside m (p + BitVec.ofNat 64 (16 * k)) v (k := 4 * (i - 4 * k)) (n := 4) (by omega_using [h])
      (by decide)
    rw [VG.Offset.add_add, show 16 * k + 4 * (i - 4 * k) = 4 * i by omega_using [h]] at e
    refine e.trans ?_
    rw [dword_eq, show 8 * (4 * (i - 4 * k)) = 32 * (i - 4 * k) by omega_using []]
  · rename_i h
    exact readW_writeW_off m p v (d := 4 * i) (e := 16 * k) (n := 4) (by omega_using [hN, hi]) (by omega_using [hN, hk]) (by omega_using [h])

/-- The mask of the `N` coefficients from `a` by `eax`: each `∧ -eax`. -/
theorem maskN_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {a : Ptr} {N : Nat} (hN0 : 0 < N)
    (hN4 : N % 4 = 0) (hN : N < 2 ^ 29) (hi : inB (rbs ++ wbs) a (4 * N) = true) (hw : inB wbs a (4 * N) = true) :
    WP isa (mask a N) s fun s' => PPostB s s' [(a, 4 * N)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      ∀ i < N, coeffAt s'.mem (pa s a) i = coeffAt s.mem (pa s a) i &&& (0 - (s.gpr .rax).setWidth 32) := by
  have hS := L.ok
  have hok : ∀ x ∈ ([(.rdi, .ptr a), (.rcx, .imm (N / 4))] : List (Reg × Arg)), x.2.Ok ∧ x.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨ptr_ok hS hi, by decide⟩, ⟨show N / 4 < 2 ^ 31 by omega_using [hN], by decide⟩⟩
  have hrd := L.inR hi
  have hwr := L.inW hw
  unfold mask
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (glue_ok _ hok (by simp only [List.map_cons, List.map_nil]; decide) s)
    fun s₀ ⟨⟨hv1, hm1⟩, k1⟩ => ?_
  refine WP.mono (maskPre_ok s₀) fun s1 ⟨⟨hm₀, hd₀⟩, k₀⟩ => ?_
  have e1 : s1.gpr .rdi = pa s a := by
    rw [k₀.gpr (by decide), hv1 _ (List.mem_cons_self ..)]; simp only [Arg.val, pa]
  have e2 : s1.gpr .rcx = BitVec.ofNat 64 (N / 4) := by
    rw [k₀.gpr (by decide)]; exact hv1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hx1 : ∀ j < 4, dword (s1.xmm .xmm0) j = 0 - (s.gpr .rax).setWidth 32 := fun j hj => by
    rw [hd₀ j hj, k1.gpr (by simp)]
  have k01 : Keep [.rdx, .rdi, .rcx] s s1 := (k1.trans k₀).mono (by simp)
  have hm01 : s1.mem = s.mem := hm₀.trans hm1
  refine WP.mono (wp_countdown (cnt := .rcx) (N := N / 4) (by omega_using [hN]) (by omega_using [hN0, hN4]) (fun k s' =>
      s'.gpr .rdi = pa s a + BitVec.ofNat 64 (16 * k) ∧
      (∀ j < 4, dword (s'.xmm .xmm0) j = 0 - (s.gpr .rax).setWidth 32) ∧
      Frame [⟨pa s a, 4 * N⟩] s.mem s'.mem ∧
      (∀ i < N, coeffAt s'.mem (pa s a) i =
        if i < 4 * k then coeffAt s.mem (pa s a) i &&& (0 - (s.gpr .rax).setWidth 32) else coeffAt s.mem (pa s a) i) ∧
      Keep [.rdx, .rdi, .rcx] s s')
    (fun k hk s' ⟨hdi, hdx, hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [e1]; simp, hx1, by rw [hm01]; exact Frame.refl _ _, fun i _ => by rw [hm01, ifn (Nat.not_lt_zero _)],
      k01⟩ e2)
    fun s' ⟨_, _, hf, hc, kk⟩ => ⟨postB_of_keep kk (by decide) (by simpa using hf),
      kk.gpr (by decide), fun i hi => by rw [hc i hi, ifp (by omega_using [hN4, hi])]⟩
  refine WP.mono (maskBody_ok s' (by rw [kk.2.1, kk.2.2, hdi]; exact inRegions_sub hrd (by omega_using [hk]) (by omega_using [hN]))
      (by rw [kk.2.2, hdi]; exact inRegions_sub hwr (by omega_using [hk]) (by omega_using [hN])))
    fun s'' ⟨⟨hm, hdi', hcx, hx', hz⟩, k'⟩ => ⟨⟨?_, by rw [hx']; exact hdx, ?_, fun i hi => ?_,
      (kk.trans k').mono (by simp)⟩, hcx, hz⟩
  · rw [hdi', hdi, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * k + 16 = 16 * (k + 1) by omega_using []]
  · rw [hm, hdi]
    exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega_using [hk]) (by omega_using [hN]))
  · rw [hm, hdi, coeffAt_writeW16 _ _ (N := N) (by omega_using [hN]) hi (by omega_using [hk])]
    split
    · rename_i h
      rw [dword_and, hdx _ (by omega_using [h]), dword_readW _ _ (by omega_using [h]), VG.Offset.add_add,
        show 16 * k + 4 * (i - 4 * k) = 4 * i by omega_using [h]]
      refine (congrArg (· &&& _) ((coeffAt_def _ _ _).trans (hc i hi))).trans ?_
      rw [ifn (by omega_using [h]), ifp (by omega_using [h])]
    · rename_i h
      rw [hc i hi]
      by_cases h' : i < 4 * k
      · rw [ifp h', ifp (by omega_using [h'])]
      · rw [ifn h', ifn (by omega_using [h, h'])]

/-- The mask of the polynomial at `a` by `eax`: each coefficient `∧ -eax`. -/
theorem mask_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {a : Ptr}
    (hi : inB (rbs ++ wbs) a 1024 = true) (hw : inB wbs a 1024 = true) :
    WP isa (mask a) s fun s' => PPostB s s' [(a, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      ∀ i < n, coeffAt s'.mem (pa s a) i = coeffAt s.mem (pa s a) i &&& (0 - (s.gpr .rax).setWidth 32) :=
  maskN_ok L (N := 256) (by decide) (by decide) (by decide) hi hw

end VG.Proof.MlDsa.X86_64.Verify

end

end

/-!
# ML-DSA verification on x86-64: the result in `r15`, and the samplers

The result so far is kept in `r15` as 1 or 0 (`flag`); `and15` and `mov32 r15,
eax` update it from a callee's result. A sampler's call, its result ANDed into
`r15` and its output masked with it (`sampled`) leaves a reduced polynomial
either way, the sampled one if the sampler succeeded (`sampled_ok`, and
`sampled4_ok` for four polynomials).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlKem.X86_64 (at_)
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- 1 if `p`, 0 otherwise. -/
def flag (p : Prop) [Decidable p] : BitVec 64 := if p then 1 else 0

theorem flag_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : flag p = flag q := by
  unfold flag; by_cases hp : p
  · rw [ifp hp, ifp (h.mp hp)]
  · rw [ifn hp, ifn (fun hq => hp (h.mpr hq))]

theorem and15_ok (s : State) :
    WP isa (.block and15) s fun s' =>
      (s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem) ∧
        Keep [.r15] s s' := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  unfold and15
  xrun

theorem mov15_ok (s : State) :
    WP isa (.block [.mov32 .r15 (.reg .rax)]) s fun s' =>
      (s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem) ∧ Keep [.r15] s s' := by
  refine WP.keep _ ?_ (Proof.MlKem.X86_64.writesOnly_of (by decide))
  xrun

/-- `r15 ∧ eax` of a flag and a result 0 or 1. -/
theorem and_flag {p : Prop} [Decidable p] {r : BitVec 32} (hr : r = 1 ∨ r = 0) :
    BitVec.setWidth 64 ((flag p).setWidth 32 &&& r) = flag (p ∧ r = 1) := by
  unfold flag
  rcases hr with rfl | rfl <;> by_cases hp : p <;> simp [hp]

/-! ## The mask -/

theorem mask_one {m : Mem} {p : Addr} (x : BitVec 32) (h : x = 1) :
    ∀ i < n, coeffAt m p i &&& (0 - x) = coeffAt m p i := by
  intro i _; subst h
  rw [show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]

theorem mask_zero {m : Mem} {p : Addr} (x : BitVec 32) (h : x = 0) :
    ∀ i < n, coeffAt m p i &&& (0 - x) = 0 := by
  intro i _; subst h; simp

theorem polyAt_eq_of_coeffAt {m m' : Mem} {p : Addr} (h : ∀ i < n, coeffAt m' p i = coeffAt m p i) :
    polyAt m' p = polyAt m p := by
  apply Vector.ext
  intro i hi
  simp only [polyAt, Vector.getElem_ofFn, h i hi]

theorem reduced_of_coeffAt {m m' : Mem} {p : Addr} (h : ∀ i < n, coeffAt m' p i = coeffAt m p i) (hr : Reduced m p) :
    Reduced m' p := fun i hi => by rw [h i hi]; exact hr i hi


/-- A sampler's call, its result ANDed into `r15`, and its output masked. -/
theorem sampled_ok {call : Prog isa} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {a : Ptr}
    (hi : inB (rbs ++ wbs) a 1024 = true) (hw : inB wbs a 1024 = true) {p : Prop} [Decidable p]
    (h15 : s.gpr .r15 = flag p) {ws : List (Ptr × Nat)} (haw : (a, 1024) ∈ ws)
    {F : Bounds → Option Poly}
    (hcall : WP isa call s fun s' => PPostB s s' ws ∧ s'.gpr .r15 = s.gpr .r15 ∧
      (res s' = 1 → Reduced s'.mem (pa s a)) ∧ Outcome F (res s') (polyAt s'.mem (pa s a))) :
    WP isa (sampled call a) s fun s' => PPostB s s' ws ∧ Reduced s'.mem (pa s a) ∧
      ∃ r : BitVec 32, (r = 1 ∨ r = 0) ∧ s'.gpr .r15 = flag (p ∧ r = 1) ∧
        (r = 1 → ∃ b, F b = some (polyAt s'.mem (pa s a))) ∧ (r = 0 → F minBounds = none) := by
  unfold sampled
  refine WP.seq (WP.mono hcall fun s₁ ⟨hP₁, h15₁, hr₁, ho₁⟩ => ?_)
  have L₁ := L.post hP₁
  have hab := ptr_bs L.ok hi
  have e₁ : pa s₁ a = pa s a := hP₁.pa hab
  have hr : res s₁ = 1 ∨ res s₁ = 0 := by rcases ho₁ with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact .inl h; exact .inr h]
  refine WP.seq (WP.mono (and15_ok s₁) fun s₂ ⟨⟨h15₂, hm₂⟩, k₂⟩ => ?_)
  have hP₂ : PPostB s₁ s₂ [] := postB_of_keep k₂ (by decide) (by rw [hm₂]; exact Frame.refl _ _)
  have L₂ := L₁.post hP₂
  have e₂ : pa s₂ a = pa s₁ a := hP₂.pa hab
  have hax : (s₂.gpr .rax).setWidth 32 = res s₁ := by rw [k₂.gpr (by decide)]
  refine WP.mono (mask_ok L₂ hi hw) fun s₃ ⟨hP₃, h15₃, hc₃⟩ => ?_
  have hsub : ∀ w ∈ [(a, 1024)], w ∈ ws := by simp only [List.mem_singleton, forall_eq]; exact haw
  have hcs : ∀ w ∈ [(a, 1024)], w.1.1 ∈ bases := by simp only [List.mem_singleton, forall_eq]; exact hab
  have hP₁₂ : PPostB s s₂ ws := PPostB.trans hP₁ hP₂ (fun _ h => absurd h List.not_mem_nil) (fun w hw => hw)
    (fun _ h => absurd h List.not_mem_nil)
  have hP : PPostB s s₃ ws := PPostB.trans hP₁₂ hP₃ hcs (fun w hw => hw) hsub
  rw [e₂, e₁, hax, hm₂] at hc₃
  refine ⟨hP, ?_, res s₁, hr, by rw [h15₃, h15₂, h15₁, h15, and_flag hr], fun h1 => ?_, fun h0 => ?_⟩
  · rcases hr with h1 | h0
    · exact reduced_of_coeffAt (fun i hi => by rw [hc₃ i hi, mask_one _ h1 i hi]) (hr₁ h1)
    · exact (Proof.MlDsa.Verify.polyIs_zero fun i hi => by rw [hc₃ i hi, mask_zero _ h0 i hi]).1
  · rcases ho₁ with ⟨_, b, hb⟩ | ⟨h0, _⟩
    · refine ⟨b, ?_⟩
      rw [hb, polyAt_eq_of_coeffAt fun i hi => by rw [hc₃ i hi, mask_one _ h1 i hi]]
    · rw [h1] at h0; cases h0
  · rcases ho₁ with ⟨h1, _⟩ | ⟨_, hn⟩
    · rw [h1] at h0; cases h0
    · exact hn

theorem coeffAt_poly4 (m : Mem) (p : Addr) (k j : Nat) : coeffAt m (poly4 p k) j = coeffAt m p (256 * k + j) := by
  unfold coeffAt poly4
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * k + 4 * j = 4 * (256 * k + j) by omega_using []]

/-- `sampled_ok` for a call that samples the four polynomials from `a`, each
from `F k`. -/
theorem sampled4_ok {call : Prog isa} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {a : Ptr}
    (hi : inB (rbs ++ wbs) a 4096 = true) (hw : inB wbs a 4096 = true) {p : Prop} [Decidable p]
    (h15 : s.gpr .r15 = flag p) {ws : List (Ptr × Nat)} (haw : (a, 4096) ∈ ws)
    {F : Nat → Bounds → Option Poly}
    (hcall : WP isa call s fun s' => PPostB s s' ws ∧ s'.gpr .r15 = s.gpr .r15 ∧
      (res s' = 1 → ∀ k < 4, Reduced s'.mem (poly4 (pa s a) k)) ∧
      ((res s' = 1 ∧ ∀ k < 4, ∃ b, F k b = some (polyAt s'.mem (poly4 (pa s a) k))) ∨
        (res s' = 0 ∧ ∃ k < 4, F k minBounds = none))) :
    WP isa (sampled4 call a) s fun s' => PPostB s s' ws ∧ (∀ k < 4, Reduced s'.mem (poly4 (pa s a) k)) ∧
      ∃ r : BitVec 32, (r = 1 ∨ r = 0) ∧ s'.gpr .r15 = flag (p ∧ r = 1) ∧
        (r = 1 → ∀ k < 4, ∃ b, F k b = some (polyAt s'.mem (poly4 (pa s a) k))) ∧
        (r = 0 → ∃ k < 4, F k minBounds = none) := by
  unfold sampled4
  refine WP.seq (WP.mono hcall fun s₁ ⟨hP₁, h15₁, hr₁, ho₁⟩ => ?_)
  have L₁ := L.post hP₁
  have hab := ptr_bs L.ok hi
  have e₁ : pa s₁ a = pa s a := hP₁.pa hab
  have hr : res s₁ = 1 ∨ res s₁ = 0 := by rcases ho₁ with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact .inl h; exact .inr h]
  refine WP.seq (WP.mono (and15_ok s₁) fun s₂ ⟨⟨h15₂, hm₂⟩, k₂⟩ => ?_)
  have hP₂ : PPostB s₁ s₂ [] := postB_of_keep k₂ (by decide) (by rw [hm₂]; exact Frame.refl _ _)
  have L₂ := L₁.post hP₂
  have e₂ : pa s₂ a = pa s₁ a := hP₂.pa hab
  have hax : (s₂.gpr .rax).setWidth 32 = res s₁ := by rw [k₂.gpr (by decide)]
  refine WP.mono (maskN_ok L₂ (N := 1024) (by decide) (by decide) (by decide) hi hw) fun s₃ ⟨hP₃, h15₃, hc₃⟩ => ?_
  have hsub : ∀ w ∈ [(a, 4 * 1024)], w ∈ ws := by simp only [List.mem_singleton, forall_eq]; exact haw
  have hcs : ∀ w ∈ [(a, 4 * 1024)], w.1.1 ∈ bases := by simp only [List.mem_singleton, forall_eq]; exact hab
  have hP₁₂ : PPostB s s₂ ws := PPostB.trans hP₁ hP₂ (fun _ h => absurd h List.not_mem_nil) (fun w hw => hw)
    (fun _ h => absurd h List.not_mem_nil)
  have hP : PPostB s s₃ ws := PPostB.trans hP₁₂ hP₃ hcs (fun w hw => hw) hsub
  rw [e₂, e₁, hax, hm₂] at hc₃
  have hc : ∀ k < 4, ∀ j < n, coeffAt s₃.mem (poly4 (pa s a) k) j =
      coeffAt s₁.mem (poly4 (pa s a) k) j &&& (0 - res s₁) := fun k hk j hj => by
    rw [coeffAt_poly4, coeffAt_poly4, hc₃ _ (by simp only [n] at hj; omega_using [hk, hj])]
  refine ⟨hP, fun k hk => ?_, res s₁, hr, by rw [h15₃, h15₂, h15₁, h15, and_flag hr], fun h1 k hk => ?_,
    fun h0 => ?_⟩
  · rcases hr with h1 | h0
    · exact reduced_of_coeffAt (fun i hi => by rw [hc k hk i hi, mask_one _ h1 i hi]) (hr₁ h1 k hk)
    · exact (Proof.MlDsa.Verify.polyIs_zero fun i hi => by rw [hc k hk i hi, mask_zero _ h0 i hi]).1
  · rcases ho₁ with ⟨_, hb⟩ | ⟨h0, _⟩
    · obtain ⟨b, hb⟩ := hb k hk
      refine ⟨b, ?_⟩
      rw [hb, polyAt_eq_of_coeffAt fun i hi => by rw [hc k hk i hi, mask_one _ h1 i hi]]
    · rw [h1] at h0; cases h0
  · rcases ho₁ with ⟨h1, _⟩ | ⟨_, hn⟩
    · rw [h1] at h0; cases h0
    · exact hn

end VG.Proof.MlDsa.X86_64.Verify
