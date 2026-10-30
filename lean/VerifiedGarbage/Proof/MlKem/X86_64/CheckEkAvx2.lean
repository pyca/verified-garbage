module

public import VerifiedGarbage.Impl.MlKem.X86_64.CheckEkAvx2
public import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
public import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.MlKem.X86_64.CheckEkAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.CheckEk
meta import VerifiedGarbage.Proof.MlKem.X86_64.Decode12Avx2
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# ML-KEM on x86-64: the key check with AVX2

For a parameter set `p` of rank `k`, against the contract of the scalar
check (`checkEkC`, `CheckEk.lean`). Value `e < 8` of group `g` of 12 bytes
is the candidate `candN` of `vg_mlkem_sample_ntt4_avx2` (`S4.cand_dword`),
which is field `e % 2` of the group of 3 bytes `4 g + e / 2` (`gv_eq`). Its
doubleword less `q` is negative exactly when it is less than `q`
(`msb_sub_q`), and the sign bits of `ymm2` are those common to every group
so far (`CkY.Inv`). At the end, the mask of `vpmovmskb` is all ones exactly
when every one is set (`bsum_full`), that is, when every field is less than
`q`, which is the check (`ekCheck_iff`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.CkY

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open D12Y (DC consts_ok yconst_ok' wp_mov32i wp_subi' wp_vsh wp_vzu)
open S4 (shV maskV qV4 candN cb candV cand_dword LUpd wp_vbin wp_vvar wp_vbcast128 wp_vpmovmskb GUpd wp_addi'
  itT itF dword_qV4 candN_lt bsum bsum_lt byteMask_eq)

/-! ## The values -/

/-- Value `e` of group `g` of 12 bytes of `E`. -/
abbrev gv (E : List Byte) (g e : Nat) : Nat := candN (fun t => (E.getD (12 * g + t) 0).toNat) e

theorem gv_eq (E : List Byte) (g : Nat) {e : Nat} (_he : e < 8) :
    gv E g e = if e % 2 = 0 then field0 E (4 * g + e / 2) else field1 E (4 * g + e / 2) := by
  unfold gv candN field0 field1
  dsimp only
  split
  · rename_i h
    have e0 : 12 * g + cb e = 3 * (4 * g + e / 2) := by simp only [cb]; omega_arith
    have e1 : 12 * g + (cb e + 1) = 3 * (4 * g + e / 2) + 1 := by simp only [cb]; omega_arith
    rw [e0, e1]
  · rename_i h
    have e0 : 12 * g + cb e = 3 * (4 * g + e / 2) + 1 := by simp only [cb]; omega_arith
    have e1 : 12 * g + (cb e + 1) = 3 * (4 * g + e / 2) + 2 := by simp only [cb]; omega_arith
    rw [e0, e1]

/-- Every value of the first `n` groups is less than `q` exactly when every field of the first `4 n` groups of
3 bytes is. -/
theorem gv_all (E : List Byte) (n : Nat) :
    (∀ g < n, ∀ e < 8, gv E g e < q) ↔ ∀ t < 4 * n, field0 E t < q ∧ field1 E t < q := by
  constructor
  · intro h t ht
    have h0 := h (t / 4) (by omega_arith) (2 * (t % 4)) (by omega_arith)
    have h1 := h (t / 4) (by omega_arith) (2 * (t % 4) + 1) (by omega_arith)
    rw [gv_eq _ _ (by omega_arith), itT (by omega_arith), show 4 * (t / 4) + 2 * (t % 4) / 2 = t by omega_arith] at h0
    rw [gv_eq _ _ (by omega_arith), itF (by omega_arith), show 4 * (t / 4) + (2 * (t % 4) + 1) / 2 = t by omega_arith] at h1
    exact ⟨h0, h1⟩
  · intro h g hg e he
    rw [gv_eq _ _ he]
    have := h (4 * g + e / 2) (by omega_arith)
    split
    · exact this.1
    · exact this.2

theorem msb_sub_q {c : Nat} (hc : c < 4096) : (BitVec.ofNat 32 c - 3329#32).msb = decide (c < q) := by
  rw [q_eq, BitVec.msb_eq_decide, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  by_cases h : c < 3329
  · rw [decide_eq_true h, decide_eq_true (by omega_arith)]
  · rw [decide_eq_false h, decide_eq_false (by omega_arith)]

theorem candN_congr {b b' : Nat → Nat} (h : ∀ t < 12, b t = b' t) {e : Nat} (he : e < 8) : candN b e = candN b' e := by
  unfold candN; rw [h (cb e) (by simp only [cb]; omega_arith), h (cb e + 1) (by simp only [cb]; omega_arith)]

/-- `∑ i < n, f i · 2ⁱ` is `2ⁿ - 1` exactly when every `f i` is set. -/
theorem bsum_full (f : Nat → Bool) : ∀ n, bsum f n = 2 ^ n - 1 ↔ ∀ i < n, f i = true
  | 0 => by simp [bsum]
  | n + 1 => by
    have ih := bsum_full f n
    have hl := bsum_lt f n
    have hp : 0 < 2 ^ n := Nat.two_pow_pos n
    simp only [bsum, Nat.pow_succ]
    constructor
    · intro h i hi
      cases hf : f n
      · rw [hf] at h; simp at h; omega_arith
      · rw [hf] at h; simp only [Bool.toNat_true, Nat.one_mul] at h
        by_cases hin : i = n
        · rw [hin, hf]
        · exact ih.mp (by omega_arith) i (by omega_arith)
    · intro h
      rw [ih.mpr fun i hi => h i (by omega_arith), h n (by omega_arith)]
      simp only [Bool.toNat_true, Nat.one_mul]
      omega_arith

/-! ## The loop -/

theorem dc_keep {s s' : State} (h : DC s) (ho : ∀ x, x ≠ .xmm2 → ∀ l < 2, s'.lane x l = s.lane x l) : DC s' :=
  ⟨fun l hl => by rw [ho _ (by decide) l hl, h.c8 l hl], fun l hl => by rw [ho _ (by decide) l hl, h.c9 l hl],
    fun l hl => by rw [ho _ (by decide) l hl, h.c10 l hl], fun l hl => by rw [ho _ (by decide) l hl, h.c11 l hl],
    fun l hl => by rw [ho _ (by decide) l hl, h.c12 l hl]⟩

theorem dc_xmm2 {s s' : State} (h : DC s) {v : Nat → BitVec 128} (hu : LUpd s s' .xmm2 v) : DC s' :=
  dc_keep h hu.other

section
variable (p : Params) (s₀ : State)
abbrev eP : Addr := s₀.gpr .rdi
abbrev E : List Byte := bytesAt s₀.mem (eP s₀) p.ekLen
end

/-- The sign of doubleword `j` of lane `l` of `ymm2` after `i` groups. -/
abbrev acc (p : Params) (s₀ : State) (i l j : Nat) : Bool := decide (∀ g < i, gv (E p s₀) g (4 * l + j) < q)

/-- After `i` groups. -/
structure Inv (p : Params) (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = eP s₀ + BitVec.ofNat 64 (12 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = s₀.mem
  dc : DC s
  sg : ∀ l < 2, ∀ j < 4, (dword (s.lane .xmm2 l) j).msb = acc p s₀ i l j

section
variable {p : Params} (hk : 0 < p.k ∧ p.k ≤ 4) {s₀ : State} (hp : (checkEkC p).pre s₀)
include hk hp

theorem step {i : Nat} (hi : i < 32 * p.k) {s : State} (hI : Inv p s₀ i s) :
    WP isa (.block ckBody) s fun s' => Inv p s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 16 := by
    rw [hI.rd, hI.wr, hp.1, hp.2.1, hI.rdi]
    exact ⟨⟨eP s₀, p.ekLen⟩, by simp, Offset.contains_base _ (by simp only [Params.ekLen]; omega_arith) (by omega_arith)⟩
  simp only [ckBody, yb]
  refine wp_vbcast128 (a := s.gpr .rdi) (by rw [ea_at, add_ofNat_zero]) hin fun s1 u1 => ?_
  refine wp_vbin fun s2 u2 => wp_vvar fun s3 u3 => wp_vbin fun s4 u4 => wp_vbin fun s5 u5 =>
    wp_vbin fun s6 u6 => wp_addi' fun s7 u7 => wp_subi' fun s8 u8 hz => WP.block_nil ?_
  have c1 := hI.dc.lupd u1 (.inl rfl)
  have c2 := c1.lupd u2 (.inl rfl)
  have c3 := c2.lupd u3 (.inl rfl)
  have c4 := c3.lupd u4 (.inl rfl)
  have c5 := c4.lupd u5 (.inl rfl)
  have hg6 : s6.gpr = s.gpr := by rw [u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  generalize hL : s.mem.readW (s.gpr .rdi) 128 = L at u1
  have h5 : ∀ l < 2, s5.lane .xmm0 l = XBinOp.eval .psubd (candV L l) qV4 := fun l hl => by
    rw [u5.val l hl, u4.val l hl, u3.val l hl, u2.val l hl, u1.val l hl, u1.other .xmm8 (by decide) l hl,
      hI.dc.c8 l hl, c2.c9 l hl, c3.c10 l hl, c4.c11 l hl]; rfl
  have h2 : ∀ l < 2, s5.lane .xmm2 l = s.lane .xmm2 l := fun l hl => by
    rw [u5.other _ (by decide) l hl, u4.other _ (by decide) l hl, u3.other _ (by decide) l hl,
      u2.other _ (by decide) l hl, u1.other _ (by decide) l hl]
  have hb : ∀ t < 12, (byte L t).toNat = ((E p s₀).getD (12 * i + t) 0).toNat := fun t ht => by
    rw [← hL, byte, byte_readW _ _ (by omega_arith), hI.rdi, hI.mem, Offset.add_add,
      bytesAt_getD _ _ (by simp only [Params.ekLen]; omega_arith)]
  refine ⟨⟨?_, by rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, hI.rd],
    by rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, hI.wr],
    by rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, hI.mem],
    ((dc_xmm2 c5 u6).gupd u7.lane).gupd u8.lane, fun l hl j hj => ?_⟩, ?_, ?_⟩
  · rw [u8.other _ (by decide), u7.gpr, hg6, hI.rdi,
      show BitVec.signExtend 64 (12 : BitVec 32) = BitVec.ofNat 64 12 by decide, BitVec.add_assoc,
      ← BitVec.ofNat_add, show 12 * i + 12 = 12 * (i + 1) by omega_arith]
  · rw [u8.lane, u7.lane, u6.val l hl, h2 l hl, h5 l hl]
    simp only [reduceVBinOpSse]
    rw [dword_pand, dword_psubd _ _ hj, dword_qV4 hj, cand_dword L hl hj, BitVec.msb_and, hI.sg l hl j hj,
      msb_sub_q (candN_lt _ (fun t => (byte L t).isLt) _), candN_congr (b' := fun t => ((E p s₀).getD (12 * i + t) 0).toNat)
        hb (by omega_arith)]
    rw [← Bool.decide_and]
    refine decide_eq_decide.mpr ⟨fun ⟨h₁, h₂⟩ g hg => ?_, fun h => ⟨fun g hg => h g (by omega_arith), h i (by omega_arith)⟩⟩
    by_cases hgi : g = i
    · subst hgi; exact h₂
    · exact h₁ g (by omega_arith)
  · rw [u8.gpr, u7.other _ (by decide), hg6]; rfl
  · rw [hz, u7.other _ (by decide), hg6]; rfl

omit hp in
/-- The start: the constants, every sign of `ymm2` set, and the count of groups in `rcx`. -/
theorem init {Q : State → Prop} (k : ∀ s, Inv p s₀ 0 s → s.gpr .rcx = BitVec.ofNat 64 (32 * p.k) → WP isa (.seq (.loop (.block ckBody) .ne) (.block ckFin)) s Q) :
    WP isa (checkEkAvx2K p.k) s₀ Q := by
  unfold checkEkAvx2K
  refine WP.seq (consts_ok fun s1 hc1 hg1 hm1 hr1 hw1 => yconst_ok' .xmm2 _ fun s2 a2 o2 g2 m2 r2 w2 =>
    wp_mov32i fun s3 u3 => WP.block_nil (k s3 ⟨?_, by rw [u3.rd, r2, hr1], by rw [u3.wr, w2, hw1],
      by rw [u3.mem, m2, hm1], (dc_keep hc1 o2).gupd u3.lane, fun l hl j hj => ?_⟩ ?_))
  · rw [u3.other _ (by decide), g2 _ (by decide), hg1 _ (by decide)]; simp
  · rw [u3.lane, a2 l hl]
    have e : acc p s₀ 0 l j = true := decide_eq_true fun g hg => absurd hg (Nat.not_lt_zero g)
    rw [e]
    rcases cases4 hj with rfl | rfl | rfl | rfl <;>
      simp only [dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3] <;> decide
  · rw [u3.gpr]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_arith

omit hk hp in
theorem sgn_bit (x : BitVec 128) {m : Nat} (hm : m < 16) :
    (XShiftOp.eval .psrad x 31).getLsbD (8 * m + 7) = (dword x (m / 4)).msb := by
  have e := getLsbD_dword (XShiftOp.eval .psrad x 31) (m / 4) (8 * (m % 4) + 7)
  rw [decide_eq_true (by omega_arith), Bool.true_and, show 32 * (m / 4) + (8 * (m % 4) + 7) = 8 * m + 7 by omega_arith,
    dword_psrad31 _ (by omega_arith)] at e
  rw [← e, BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  simp only [show ¬ (32 ≤ 8 * (m % 4) + 7) by omega_arith, decide_false, Bool.not_false, Bool.true_and,
    show ¬ (31 + (8 * (m % 4) + 7) < 32) by omega_arith, ↓reduceIte]

omit hk hp in
theorem ckTail_ok (s : State) :
    WP isa (.block [.alu .add .rax (.imm 1), .shift .shr .rax 32, .vop .vzeroupper]) s
      fun s' => (s'.gpr .rax).toNat = ((s.gpr .rax).toNat + 1) % 2 ^ 64 / 2 ^ 32 := by
  xrun
  rw [show ∀ st : State, (VOp.vzeroupper.exec st).gpr = st.gpr from fun _ => rfl, RegUpd.gpr_setReg_self,
    BitVec.toNat_ushiftRight, BitVec.toNat_add, Nat.shiftRight_eq_div_pow]
  rfl

omit hk hp in
theorem fin_ok {s : State} (hI : Inv p s₀ (32 * p.k) s) :
    WP isa (.block ckFin) s fun s' => (s'.gpr .rax).setWidth 32 = if ekCheck p (E p s₀) then 1 else 0 := by
  simp only [ckFin]
  refine wp_vsh fun s4 u4 => wp_vpmovmskb fun s5 u5 => WP.mono (ckTail_ok s5) fun s6 h6 => ?_
  have hf : ∀ i < 32, (s4.ymm .xmm2).getLsbD (8 * i + 7) = acc p s₀ (32 * p.k) (i / 16) (i % 16 / 4) := fun i hi => by
    rw [State.ymm_eq, BitVec.getLsbD_append]
    by_cases h : i < 16
    · rw [itT (show 8 * i + 7 < 128 by omega_arith), u4.val 0 (by decide), sgn_bit _ h, hI.sg 0 (by decide) _ (by omega_arith),
        Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    · rw [itF (show ¬ 8 * i + 7 < 128 by omega_arith), u4.val 1 (by decide), show 8 * i + 7 - 128 = 8 * (i - 16) + 7 by omega_arith,
        sgn_bit _ (show i - 16 < 16 by omega_arith), hI.sg 1 (by decide) _ (by omega_arith), show i / 16 = 1 by omega_arith,
        show i % 16 = i - 16 by omega_arith]
  have hb : (s5.gpr .rax).toNat = bsum (fun i => (s4.ymm .xmm2).getLsbD (8 * i + 7)) 32 := by
    rw [u5.gpr, byteMask_eq _ (by decide), BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (bsum_lt _ 32) (by decide))
  have hl := bsum_lt (fun i => (s4.ymm .xmm2).getLsbD (8 * i + 7)) 32
  have hall : (∀ i < 32, (s4.ymm .xmm2).getLsbD (8 * i + 7) = true) ↔ ekCheck p (E p s₀) = true := by
    rw [ekCheck_iff p _ (bytesAt_length _ _ _), show 128 * p.k = 4 * (32 * p.k) by omega_arith, ← gv_all]
    constructor
    · intro h g hg e he
      have := h (16 * (e / 4) + 4 * (e % 4)) (by omega_arith)
      rw [hf _ (by omega_arith), show (16 * (e / 4) + 4 * (e % 4)) / 16 = e / 4 by omega_arith,
        show (16 * (e / 4) + 4 * (e % 4)) % 16 / 4 = e % 4 by omega_arith] at this
      have := of_decide_eq_true this g hg
      rwa [show 4 * (e / 4) + e % 4 = e by omega_arith] at this
    · intro h i hi
      rw [hf i hi]
      exact decide_eq_true fun g hg => h g hg _ (by omega_arith)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h6, hb]
  by_cases hc : ekCheck p (E p s₀) = true
  · rw [(bsum_full _ 32).mpr (hall.mpr hc), itT hc]; decide
  · rw [itF hc]
    have hne : bsum (fun i => (s4.ymm .xmm2).getLsbD (8 * i + 7)) 32 ≠ 2 ^ 32 - 1 := fun h =>
      hc (hall.mp ((bsum_full _ 32).mp h))
    show _ = 0
    omega_arith

theorem main : WP isa (checkEkAvx2K p.k) s₀ fun s => (s.gpr .rax).setWidth 32 = if ekCheck p (E p s₀) then 1 else 0 :=
  init hk fun s hI hc => WP.seq (wp_countdown (cnt := .rcx) (N := 32 * p.k) (by omega_arith) (by omega_arith) (Inv p s₀)
    (fun i hi s hI _ => step hk hp hi hI) (fun s hI => fin_ok hI) hI hc)

theorem correct : ∃ t s', Exec isa (checkEkAvx2K p.k) s₀ t s' ∧ abiPreserved s₀ s' ∧ (checkEkC p).post s₀ s' := by
  obtain ⟨t, s', he, hr, hk'⟩ := WP.keep (c := checkEkAvx2K p.k) [.rax, .rdi, .rcx] (main hk hp) (by rfl)
  exact ⟨t, s', he, abiPreserved_of_exec (by rfl) he
    (gprPreserved_of hk' (by decide) (ws := [])
      (by have := (Exec.regions he (by rfl)).2.2; rwa [hp.2.1] at this) (by simp)), hr⟩

end

end VG.Proof.MlKem.X86_64.CkY

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- Constant time, from the taint check of the code of the parameter set. -/
theorem checkEkAvx2_ct (p : Params) {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rdi, .rsp]) (checkEkAvx2K p.k) h).isSome = true) :
    ConstantTime isa (checkEkC p).pre (checkEkC p).pub (checkEkAvx2K p.k) :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsp])
    (fun _ _ _ _ hp => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.1, hp.2]) ht

theorem checkEkAvx2_verified :
    Verified X86_64.target Impl.MlKem.X86_64.checkEkAvx2 (Spec.MlKem.checkEkContract X86_64.abi) :=
  Verified.of_correct (fun s hs => CkY.correct (p := mlKem768) (by decide) hs) (checkEkAvx2_ct mlKem768 (by taint_decide)) (by
    mlkem_implies [Spec.MlKem.checkEkContract, Spec.MlKem.checkEkSig, checkEkC, X86_64.abi,
      X86_64.argRegs, Params.ekLen, mlKem768] [checkEkSat] using checkEkSat)

end VG.Proof.MlKem.X86_64
