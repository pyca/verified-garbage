module

public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Contract
public import VerifiedGarbage.Impl.Rsa.X86_64.PrivPre
public import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_private_precompute` on x86-64: the entry

What the code uses of `ppContract.pre` (`ppCtx_of`), and `entry`, which
saves the callee-saved registers and the arguments in the header of the
working space and leaves its base in `rdi` (`entry_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-! ## The precondition, as the code uses it -/

/-- What the code uses of its contract's precondition, for the working
space (stack argument 2) of `(stackArg s 3).toNat * 8` bytes. -/
structure PPCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .rcx).toNat
  hk2 : (s.gpr .rcx).toNat ≤ 1024
  hpl1 : 1 ≤ (s.gpr .r9).toNat
  hpl2 : (s.gpr .r9).toNat < (s.gpr .rcx).toNat
  hql1 : 1 ≤ (stackArg s 1).toNat
  hql2 : (stackArg s 1).toNat < (s.gpr .rcx).toNat
  hL : (s.gpr .rsi).toNat = Spec.Rsa.privatePrecomputedWords (s.gpr .rcx).toNat (s.gpr .r9).toNat
    (stackArg s 1).toNat
  hZ : 128 * (s.gpr .rcx).toNat + 256 ≤ (stackArg s 3).toNat * 8
  hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8)
  ha : ∀ j < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8
  hnb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rdx)
    (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  hpb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .r8)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
  hqb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
  hout : ∀ j < (s.gpr .rsi).toNat * 8, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1
  houts : ∀ j < (s.gpr .rsi).toNat * 8, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) (s.gpr .rdi + BitVec.ofNat 64 j)
  hwrap : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64
  hon : ∀ j < (s.gpr .rsi).toNat * 8, ∀ i < (s.gpr .rcx).toNat, s.gpr .rdi + BitVec.ofNat 64 j ≠ s.gpr .rdx + BitVec.ofNat 64 i
  hop : ∀ j < (s.gpr .rsi).toNat * 8, ∀ i < (s.gpr .r9).toNat, s.gpr .rdi + BitVec.ofNat 64 j ≠ s.gpr .r8 + BitVec.ofNat 64 i
  hoq : ∀ j < (s.gpr .rsi).toNat * 8, ∀ i < (stackArg s 1).toNat,
    s.gpr .rdi + BitVec.ofNat 64 j ≠ stackArg s 0 + BitVec.ofNat 64 i
  hret : ∀ b < 8, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    ∀ j < (s.gpr .rsi).toNat * 8, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j
  hpreR : (⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩ : Region) ∈ s.wr
  hS : ∀ x, ofs (stackArg s 2) x < (stackArg s 3).toNat * 8 → (s.gpr .rsi).toNat * 8 ≤ ofs (s.gpr .rdi) x
  hretP : ∀ b < 8, (s.gpr .rsi).toNat * 8 ≤ ofs (s.gpr .rdi) (s.gpr .rsp + BitVec.ofNat 64 b)

/-- Bytes of two disjoint regions differ. -/
theorem disjoint_ne {a b : Addr} {la lb : Nat} (hd : (⟨a, la⟩ : Region).Disjoint ⟨b, lb⟩) (ha : la ≤ 2 ^ 64)
    (hb : lb ≤ 2 ^ 64) : ∀ j < la, ∀ i < lb, a + BitVec.ofNat 64 j ≠ b + BitVec.ofNat 64 i := by
  intro j hj i hi he
  exact hd _ (contains_byte a hj ha) (by rw [he]; exact contains_byte b hi hb)

theorem ppCtx_of {s : State} (h : ppContract.pre s) : PPCtx s := by
  simp only [ppContract] at h
  sig_split h
  rename_i hsp hrd hwr dPn dPp dPq dPs dPa dns dps dqs dsa dRo dRn dRp dRq dRs dRa wO wN wP wQ wS hk hpl1 hpl2
    hql1 hql2 hL
  have hsl := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  have hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) wS
  have hn := hs.nowrap
  have hargs : (⟨stackArgAddr s 0, 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨hk1, hk2, hpl1, hpl2, hql1, hql2, hL, by omega_arith, hs,
    fun j hj => ⟨_, hargs, by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dns,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dps,
    src_of_region (by rw [hrd]; simp) (by omega_arith) dqs,
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self, contains_byte _ hj (by omega_arith)⟩,
    fun j hj => out_scr dPs (contains_byte _ hj (by omega_arith)), wO,
    disjoint_ne dPn (by omega_arith) (by omega_arith), disjoint_ne dPp (by omega_arith) (by omega_arith),
    disjoint_ne dPq (by omega_arith) (by omega_arith), fun b hb => ?_, by rw [hwr]; exact List.mem_cons_self,
    fun x hx => ?_, fun b hb => ?_⟩
  · have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) hb (by omega_arith)
    exact ⟨out_scr dRs hc, fun j hj he => dRo _ hc (by rw [he]; exact contains_byte _ hj (by omega_arith))⟩
  · refine Nat.le_of_not_lt fun h' => dPs x ?_ ?_
    · show (x - s.gpr .rdi).toNat + 1 ≤ (s.gpr .rsi).toNat * 8
      unfold ofs at h'; omega
    · show (x - stackArg s 2).toNat + 1 ≤ (stackArg s 3).toNat * 8
      unfold ofs at hx; omega
  · have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) hb (by omega_arith)
    refine Nat.le_of_not_lt fun h' => dRo _ hc ?_
    show (s.gpr .rsp + BitVec.ofNat 64 b - s.gpr .rdi).toNat + 1 ≤ (s.gpr .rsi).toNat * 8
    unfold ofs at h'; omega

/-! ## The entry -/

theorem entry_eq : PrivPre.entry = ([.mov .r11 (.mem { base := .rsp, disp := 24 }),
    .mov .r10 (.mem { base := .rsp, disp := 8 }), .mov .rax (.mem { base := .rsp, disp := 16 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sOut) .rdi, .store (hdr11 sN) .rdx, .store (hdr11 sK) .rcx, .store (hdr11 sIn) .rdi,
    .store (hdr11 sP) .r8, .store (hdr11 sPlen) .r9, .store (hdr11 sDp) .r8, .store (hdr11 sQinv) .rdi,
    .store (hdr11 sQ) .r10, .store (hdr11 sDq) .r10, .store (hdr11 sQlen) .rax,
    .mov .rdi (.reg .r11)] : List Instr) := rfl

/-- The header after the entry's stores. -/
def entryMem (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk vp vpl vq vql : BitVec 64) : Mem :=
  ((((((((((((((((m.writeW (off B (8 * 0)) v0).writeW (off B (8 * 1)) v1).writeW (off B (8 * 2)) v2).writeW
    (off B (8 * 3)) v3).writeW (off B (8 * 4)) v4).writeW (off B (8 * 5)) v5).writeW (off B (8 * sOut)) vo).writeW
    (off B (8 * sN)) vn).writeW (off B (8 * sK)) vk).writeW (off B (8 * sIn)) vo).writeW
    (off B (8 * sP)) vp).writeW (off B (8 * sPlen)) vpl).writeW (off B (8 * sDp)) vp).writeW
    (off B (8 * sQinv)) vo).writeW (off B (8 * sQ)) vq).writeW (off B (8 * sDq)) vq).writeW (off B (8 * sQlen)) vql

theorem entryMem_facts (m : Mem) (B : Addr) (v0 v1 v2 v3 v4 v5 vo vn vk vp vpl vq vql : BitVec 64) :
    let m' := entryMem m B v0 v1 v2 v3 v4 v5 vo vn vk vp vpl vq vql
    word m' B (8 * 0) = v0 ∧ word m' B (8 * 1) = v1 ∧ word m' B (8 * 2) = v2 ∧ word m' B (8 * 3) = v3 ∧
    word m' B (8 * 4) = v4 ∧ word m' B (8 * 5) = v5 ∧ word m' B (8 * sOut) = vo ∧ word m' B (8 * sN) = vn ∧
    word m' B (8 * sK) = vk ∧ word m' B (8 * sIn) = vo ∧ word m' B (8 * sP) = vp ∧ word m' B (8 * sPlen) = vpl ∧
    word m' B (8 * sQ) = vq ∧ word m' B (8 * sQlen) = vql ∧ word m' B (8 * sDp) = vp ∧
    word m' B (8 * sDq) = vq ∧ word m' B (8 * sQinv) = vo ∧ Outside B 0 (8 * 32) m m' := by
  intro m'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold m' entryMem
  all_goals first
    | (repeat (first | refine word_skip ?_ (by decide) (by decide) (by decide) |
        exact word_writeW_self _ _ _ _)); done
    | (repeat (first | exact Outside.refl _ _ _ _ | refine Outside.store_hdr ?_ (by decide) (by decide) _))

/-- `entry`: the header, from the arguments, and the working space's base
(stack argument 2) in `rdi`. -/
theorem entry_ok {s : State} (c : PPCtx s) :
    WP isa (.block PrivPre.entry) s fun t => t.gpr .rdi = stackArg s 2 ∧
      (∀ i < 6, word t.mem (stackArg s 2) (8 * i) = s.gpr (saved.getD i .rax)) ∧
      word t.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi ∧ word t.mem (stackArg s 2) (8 * sN) = s.gpr .rdx ∧
      word t.mem (stackArg s 2) (8 * sK) = s.gpr .rcx ∧ word t.mem (stackArg s 2) (8 * sIn) = s.gpr .rdi ∧
      word t.mem (stackArg s 2) (8 * sP) = s.gpr .r8 ∧ word t.mem (stackArg s 2) (8 * sPlen) = s.gpr .r9 ∧
      word t.mem (stackArg s 2) (8 * sQ) = stackArg s 0 ∧ word t.mem (stackArg s 2) (8 * sQlen) = stackArg s 1 ∧
      word t.mem (stackArg s 2) (8 * sDp) = s.gpr .r8 ∧ word t.mem (stackArg s 2) (8 * sDq) = stackArg s 0 ∧
      word t.mem (stackArg s 2) (8 * sQinv) = s.gpr .rdi ∧
      Outside (stackArg s 2) 0 (8 * 32) s.mem t.mem ∧ Keep [.r11, .r10, .rax, .rdi] s t := by
  have hn := c.hs.nowrap
  have hZ := c.hZ
  have hk1 := c.hk1
  have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega_arith)
  have e0 : s.gpr .rsp + BitVec.ofInt 64 8 = stackArgAddr s 0 := rfl
  have e1 : s.gpr .rsp + BitVec.ofInt 64 16 = stackArgAddr s 1 := rfl
  have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
  have r0 : s.mem.readW (stackArgAddr s 0) 64 = stackArg s 0 := rfl
  have r1 : s.mem.readW (stackArgAddr s 1) 64 = stackArg s 1 := rfl
  have r2 : s.mem.readW (stackArgAddr s 2) 64 = stackArg s 2 := rfl
  rw [entry_eq]
  refine WP.mono (WP.keep [.r11, .r10, .rax, .rdi] (Q := fun t => t.gpr .rdi = stackArg s 2 ∧
      t.mem = entryMem s.mem (stackArg s 2) (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
        (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0)
        (stackArg s 1)) ?_ rfl) fun t ⟨⟨hdi, hm⟩, k⟩ => ?_
  · xrun [State.ea, hdr11, e0, e1, e2, c.ha 0 (by decide), c.ha 1 (by decide), c.ha 2 (by decide), r0, r1, r2,
      hdrOff, hw 0 (by decide), hw 1 (by decide), hw 2 (by decide), hw 3 (by decide), hw 4 (by decide),
      hw 5 (by decide), hw sOut (by decide), hw sN (by decide), hw sK (by decide), hw sIn (by decide),
      hw sP (by decide), hw sPlen (by decide), hw sDp (by decide), hw sQinv (by decide), hw sQ (by decide),
      hw sDq (by decide), hw sQlen (by decide)]
    rfl
  rw [hm]
  obtain ⟨h0, h1, h2, h3, h4, h5, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho⟩ :=
    entryMem_facts s.mem (stackArg s 2) (s.gpr .rbx) (s.gpr .rbp) (s.gpr .r12) (s.gpr .r13) (s.gpr .r14)
      (s.gpr .r15) (s.gpr .rdi) (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8) (s.gpr .r9) (stackArg s 0) (stackArg s 1)
  refine ⟨hdi, fun i hi => ?_, hO, hN, hK, hI, hP, hPl, hQ, hQl, hDp, hDq, hQi, ho, k⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end VG.Proof.Bignum.X86_64.PrivPre
