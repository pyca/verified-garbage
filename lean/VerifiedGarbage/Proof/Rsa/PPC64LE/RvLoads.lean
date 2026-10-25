module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvEntry
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvCtx
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBytes
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvStores
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_rsa_recover_primes` on PPC64LE: reading the numbers

`ldR_ok`: a number from its bytes, in either view of the working space.
`InR s0 P L`: the `L` bytes at `P` are readable and apart from the
working space; `in_n`, `in_e`, `in_d`: `n`, `e` and `d` are.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Recover (loadR)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num)

/-- An input: readable, apart from the working space. -/
structure InR (s0 : State) (P : Addr) (L : Nat) : Prop where
  rd : (⟨P, L⟩ : Region) ∈ s0.rd
  disj : (⟨P, L⟩ : Region).Disjoint ⟨rvB s0, rvZ s0⟩
  nowrap : P.toNat + L ≤ 2 ^ 64

theorem in_n {s0 : State} (h : rvP.pre s0) : InR s0 (s0.gpr .r7) (kK s0) := by
  obtain ⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, ns, -, -, -, -, -, wn, -⟩ := h
  exact ⟨by rw [hrd]; simp, ns, wn⟩

theorem in_e {s0 : State} (h : rvP.pre s0) : InR s0 (s0.gpr .r9) (s0.gpr .r10).toNat := by
  obtain ⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, es, -, -, -, -, -, we, -⟩ := h
  exact ⟨by rw [hrd]; simp, es, we⟩

theorem in_d {s0 : State} (h : rvP.pre s0) :
    InR s0 (PPC64LE.stackArg s0 0) (PPC64LE.stackArg s0 1).toNat := by
  obtain ⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ds, -, -, -, -, -, wd, -⟩ := h
  exact ⟨by rw [hrd]; simp, ds, wd⟩

/-- `loadR rP rL j`: array `j` (of `v` digits), 0, := the `L` bytes at `P`. -/
theorem ldR_ok {s0 t : State} (b : RBase s0 t) {v N : Nat} (h : Ws t (rvB s0) (rvZ s0) v N) {j : Nat}
    (hj : j < N) (hN : N ≤ 256) {rP rL : Reg} (hrP : rP ≠ .r0) (hrL : rL ≠ .r0) (hrL6 : rL ≠ .r6)
    {P : Addr} {L : Nat} (hP : t.gpr rP = P) (hL : t.gpr rL = BitVec.ofNat 64 L) (hL1 : 1 ≤ L)
    (hLw : L ≤ 4 * v) (hi : InR s0 P L)
    (hz : ∀ i < v, w32 t.mem (rvB s0) (arr v j + 4 * i) = 0) :
    WP isa (seqs (loadR rP rL j)) t fun u =>
      Ws u (rvB s0) (rvZ s0) v N ∧ KeyWorkspace.Keep (rvB s0) v [j] [] t.mem u.mem ∧
      num u.mem (rvB s0) v j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem P L) ∧
      Outside (rvB s0) (arr v j) (4 * v) t.mem u.mem ∧ Keep [.r0, .r5, .r6, .r8] t u := by
  rw [loadR]
  refine WP.seq (WP.mono (CrtValues.mv2_ok (s := t) (d₁ := .r6) (d₂ := .r8) hrP hrL hrL6 (by decide))
    fun u ⟨⟨u6, u8, um⟩, ku⟩ => ?_)
  have hu := h.of_keep ku
  have hP' := hi.nowrap
  have hc : ∀ i < L, (⟨P, L⟩ : Region).Contains (off P i) 1 := fun i hi =>
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hz' : val32 u.mem (rvB s0) (arr v j) v = 0 := by rw [um]; exact CrtValues.val32_of_zero hz
  refine WP.mono (load_ok hu hj hN (u6.trans hP) (u8.trans hL) hL1 hLw
    (fun i hi' => ⟨_, List.mem_append_left _ (by rw [ku.rd, b.rd]; exact hi.rd), hc i hi'⟩)
    (fun i hi' x hx e => by have := CrtValues.past_of_disjoint hi.disj (hc i hi'); rw [e] at this; omega_arith)
    (fun p hp => by rw [← off_add]; exact VG.Proof.Bignum.byte_zero_of_val32 hz' hp))
    fun w' ⟨hv, k, val, kv, o⟩ => ⟨hv, um ▸ k, ?_, um ▸ o, (ku.trans kv).mono⟩
  rw [val]
  congr 1
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun c hc' => ?_
  rw [um]
  exact b.frame _ (CrtValues.past_of_disjoint hi.disj (hc c (List.mem_range.mp hc')))

end VG.Proof.Rsa.PPC64LE.Recover

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Recover (loadR loads zeroAll ctxW nArr aN aOne aZ wZ wE wD wM wMod)
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Rsa.KeyWorkspace (arr S num)

/-- `W = 2 w + 2`. -/
abbrev wW (k : Nat) : Nat := 2 * ww k + 2

/-- The bits of `d e`: `c = 8 (e_len + d_len)`. -/
abbrev cB (s0 : State) : Nat := 8 * ((s0.gpr .r10).toNat + (PPC64LE.stackArg s0 1).toNat)

abbrev nV (s0 : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kK s0))
abbrev eV (s0 : State) : Nat := Spec.Rsa.os2ip (eB s0)
abbrev dV (s0 : State) : Nat := Spec.Rsa.os2ip (dB s0)

theorem w32_out {B : Addr} {a n : Nat} {m m' : Mem} (o : Outside B a n m m') {d : Nat}
    (h : d + 4 ≤ a ∨ a + n ≤ d) (hd : d + 4 ≤ 2 ^ 64) : w32 m' B d = w32 m B d := by
  have := Outs.val32 (k := 1) (d := d) (Outs.of_outside o (List.mem_singleton_self _))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; dsimp only; omega_arith) (by omega_arith)
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using this

/-- The sizes. -/
structure Sz (s0 : State) : Prop where
  w1 : 18 ≤ ww (kK s0)
  w2 : ww (kK s0) ≤ 258
  kw : kK s0 ≤ 4 * ww (kK s0) - 8
  svw : sv (kK s0) = arr (ww (kK s0)) nArr
  svW : arr (wW (kK s0)) 16 ≤ sv (kK s0)
  svZ : sv (kK s0) + 2 * S (ww (kK s0)) ≤ rvZ s0
  nw : (rvB s0).toNat + rvZ s0 ≤ 2 ^ 64

theorem RBase.sz {s0 t : State} (b : RBase s0 t) : Sz s0 := by
  have hp := rv_kpre b.pre
  have k1 := hp.k64; have k2 := hp.k1024
  have h8 : 8 * ((kK s0 + 7) / 8) ≤ kK s0 + 7 := Nat.mul_div_le _ _
  have h8' : kK s0 + 7 < 8 * ((kK s0 + 7) / 8) + 8 := by omega_arith
  refine ⟨by simp only [ww]; omega_arith, by simp only [ww]; omega_arith, by simp only [ww]; omega_arith, rfl, ?_, b.svZ, b.nowrap⟩
  simp only [sv, wW, arr, S, nArr, VG.Proof.Rsa.KeyWorkspace.hdr]
  generalize ww (kK s0) = w
  omega_arith

/-- After the numbers are read. -/
structure LdD (s0 t : State) : Prop where
  base : RBase s0 t
  ws : Ws t (rvB s0) (rvZ s0) (wW (kK s0)) 16
  r21 : t.gpr .r21 = s0.gpr .r3
  r23 : t.gpr .r23 = s0.gpr .r5
  r24 : t.gpr .r24 = s0.gpr .r7
  r25 : t.gpr .r25 = s0.gpr .r8
  r26 : t.gpr .r26 = BitVec.ofNat 64 (cB s0)
  r27 : t.gpr .r27 = s0.gpr .r10
  vN : num t.mem (rvB s0) (ww (kK s0)) aN = nV s0
  vE : num t.mem (rvB s0) (wW (kK s0)) wE = eV s0
  vD : num t.mem (rvB s0) (wW (kK s0)) wD = dV s0
  zW : ∀ j ∈ [wZ, wM, wMod], ∀ i < wW (kK s0) + 2, w32 t.mem (rvB s0) (arr (wW (kK s0)) j + 4 * i) = 0
  zK : ∀ j ∈ [aOne, aZ], ∀ i < ww (kK s0) + 2, w32 t.mem (rvB s0) (arr (ww (kK s0)) j + 4 * i) = 0

theorem val32_out {B : Addr} {a n : Nat} {m m' : Mem} (o : Outside B a n m m') {d k : Nat}
    (h : d + 4 * k ≤ a ∨ a + n ≤ d) (hd : d + 4 * k ≤ 2 ^ 64) : val32 m' B d k = val32 m B d k :=
  Outs.val32 (Outs.of_outside o (List.mem_singleton_self _))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; dsimp only; omega_arith) hd

theorem c_val (a b : BitVec 64) :
    (a + b) <<< 3 = BitVec.ofNat 64 (8 * (a.toNat + b.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-- The entry's state is a working space of `w` digits. -/
theorem REnt.ws {s0 t : State} (e : REnt s0 t) : Ws t (rvB s0) (rvZ s0) (ww (kK s0)) nArr := by
  have hp := rv_kpre e.base.pre
  have z := e.base.sz
  exact ⟨Scr.of_mem (by rw [e.base.wr]; exact hp.wr) hp.nowrap, by rw [← z.svw]; have := z.svZ; omega_arith,
    by have := z.w1; omega_arith, by have := z.w2; omega_arith, e.r29, e.r30, e.base.r31⟩

/-- The registers the reading of the numbers changes. -/
abbrev ldRegs : List Reg := [.r0, .r3, .r5, .r6, .r7, .r8, .r9, .r26, .r29, .r30]

theorem loads_ok {s0 t : State} (e : REnt s0 t) : WP isa loads t fun u => LdD s0 u ∧ Keep ldRegs t u := by
  have b := e.base
  have z := b.sz
  have hp := rv_kpre b.pre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -, -, e1, e2, d1, d2,
    -⟩ := id b.pre
  have w1 := z.w1; have w2 := z.w2; have kw := z.kw; have svW := z.svW
  have svw := z.svw
  have hkK : kK s0 = (s0.gpr .r8).toNat := rfl
  have hS : S (ww (kK s0)) = 4 * (ww (kK s0) + 2) := rfl
  have hSW : S (wW (kK s0)) = 4 * (2 * ww (kK s0) + 4) := rfl
  have nw := z.nw; have svZ := z.svZ
  simp only [loads, List.append_assoc, List.cons_append, List.nil_append]
  rw [wp_seqs_cons (by simp [loadR])]
  refine WP.mono (zeroAll_ok e.ws (by rw [← svw]; omega_arith)) fun t1 ⟨w1', z1, o1, k1⟩ => ?_
  have b1 : RBase s0 t1 := b.of_outs (Outs.of_outside o1 (List.mem_singleton_self _))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      show 160 + 4 * (nArr * (ww (kK s0) + 2)) ≤ sv (kK s0)
      simp only [sv, arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; rw [Nat.mul_left_comm]) k1
  -- `n`.
  rw [wp_seqs_append (by simp [loadR]) (by simp)]
  have zn : ∀ i < ww (kK s0), w32 t1.mem (rvB s0) (arr (ww (kK s0)) aN + 4 * i) = 0 := fun i hi => by
    have := z1 (32 * (ww (kK s0) + 2) + i) (by simp only [nArr]; omega_arith)
    rwa [show 160 + 4 * (32 * (ww (kK s0) + 2) + i) = arr (ww (kK s0)) aN + 4 * i by
      simp only [arr, S, aN, VG.Proof.Rsa.KeyWorkspace.hdr]; omega_arith] at this
  have a25 : t1.gpr .r25 = BitVec.ofNat 64 (kK s0) := by
    rw [k1.gpr _ (by decide), e.args.r25]; exact CrtValues.ofNat_toNat64 _
  refine WP.mono (ldR_ok b1 w1' (j := aN) (by decide) (by decide) (rP := .r24) (rL := .r25) (by decide) (by decide)
    (by decide) (by rw [k1.gpr _ (by decide), e.args.r24]) a25 (by simp only [kK]; omega_arith) (by omega_arith) (in_n b.pre)
    zn) fun t2 ⟨w2, kk2, v2, o2, k2⟩ => ?_
  have b2 : RBase s0 t2 := b1.of_keep kk2 (fun j hj => by
    simp only [List.mem_singleton] at hj; subst hj; rw [svw]; exact VG.Proof.Rsa.KeyWorkspace.arr_end (by decide))
    (by simp) k2
  -- `W`.
  rw [wp_seqs_cons (by simp [loadR]), ← List.append_nil ctxW]
  refine ctxW_ok w2 (by omega_arith) (Nat.le_trans svW (Nat.le_trans (Nat.le_add_right _ _) svZ)) fun t3 w3 m3 k3 =>
    WP.block_nil ?_
  have b3 := b2.of_regs k3 m3
  have hWw : 2 * ww (kK s0) + 2 = wW (kK s0) := rfl
  rw [hWw] at w3
  -- The digits still 0 after `n` is read: any outside `n`'s array.
  have zz2 : ∀ i < nArr * (ww (kK s0) + 2), (160 + 4 * i + 4 ≤ arr (ww (kK s0)) aN ∨
      arr (ww (kK s0)) aN + 4 * ww (kK s0) ≤ 160 + 4 * i) → w32 t2.mem (rvB s0) (160 + 4 * i) = 0 :=
    fun i hi hs => by rw [w32_out o2 hs (by simp only [nArr] at hi; omega_arith)]; exact z1 i hi
  have hA : ∀ j i, arr (wW (kK s0)) j + 4 * i = 160 + 4 * (j * (wW (kK s0) + 2) + i) := fun j i => by
    simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; rw [Nat.mul_left_comm, Nat.mul_add 4 _ i, Nat.add_assoc]
  have hAw : ∀ j i, arr (ww (kK s0)) j + 4 * i = 160 + 4 * (j * (ww (kK s0) + 2) + i) := fun j i => by
    simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; rw [Nat.mul_left_comm, Nat.mul_add 4 _ i, Nat.add_assoc]
  have haN : arr (ww (kK s0)) aN = 160 + 4 * (32 * (ww (kK s0) + 2)) := by
    have := hAw aN 0; simp only [aN, Nat.mul_zero, Nat.add_zero] at this; exact this
  -- `e`.
  rw [wp_seqs_append (by simp [loadR]) (by simp [loadR])]
  have a27 : t3.gpr .r27 = BitVec.ofNat 64 (s0.gpr .r10).toNat := by
    rw [k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), e.args.r27]
    exact CrtValues.ofNat_toNat64 _
  refine WP.mono (ldR_ok b3 w3 (j := wE) (by decide) (by decide) (rP := .r26) (rL := .r27) (by decide) (by decide)
    (by decide) (by rw [k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), e.args.r26]) a27 e1
    (by simp only [wW]; omega_arith) (in_e b.pre) (fun i hi => by
      rw [m3, hA, zz2 _ (by simp only [nArr, wE, wW] at hi ⊢; omega_arith) (by rw [haN]; simp only [wE, wW] at hi ⊢; omega_arith)]))
    fun t4 ⟨w4, kk4, v4, o4, k4⟩ => ?_
  have b4 : RBase s0 t4 := b3.of_keep kk4 (fun j hj => by
    simp only [List.mem_singleton] at hj; subst hj
    exact Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_end (by decide)) svW) (by simp) k4
  -- `d`.
  rw [wp_seqs_append (by simp [loadR]) (by simp)]
  have a22 : t4.gpr .r22 = BitVec.ofNat 64 (PPC64LE.stackArg s0 1).toNat := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide), e.args.r22]
    exact CrtValues.ofNat_toNat64 _
  refine WP.mono (ldR_ok b4 w4 (j := wD) (by decide) (by decide) (rP := .r28) (rL := .r22) (by decide) (by decide)
    (by decide) (by rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide),
      e.args.r28]) a22 d1 (by simp only [wW]; omega_arith) (in_d b.pre) (fun i hi => by
      rw [w32_out o4 (by rw [hA, hA]; simp only [wE, wD, wW] at hi ⊢; omega_arith) (by rw [hA]; simp only [wD, wW] at hi ⊢; omega_arith),
        m3, hA, zz2 _ (by simp only [nArr, wD, wW] at hi ⊢; omega_arith) (by rw [haN]; simp only [wD, wW] at hi ⊢; omega_arith)]))
    fun t5 ⟨w5, kk5, v5, o5, k5⟩ => ?_
  have b5 : RBase s0 t5 := b4.of_keep kk5 (fun j hj => by
    simp only [List.mem_singleton] at hj; subst hj
    exact Nat.le_trans (VG.Proof.Rsa.KeyWorkspace.arr_end (by decide)) svW) (by simp) k5
  -- `c`.
  rw [show seqs [.block [.add .r26 .r27 .r22, .lsl .r26 .r26 3]] = .block [.add .r26 .r27 .r22, .lsl .r26 .r26 3]
    from rfl]
  have a27' : t5.gpr .r27 = BitVec.ofNat 64 (s0.gpr .r10).toNat := by
    rw [k5.gpr _ (by decide), k4.gpr _ (by decide)]; exact a27
  have a22' : t5.gpr .r22 = BitVec.ofNat 64 (PPC64LE.stackArg s0 1).toNat := by rw [k5.gpr _ (by decide)]; exact a22
  refine WP.mono (WP.keep [.r26] (Q := fun u => u.gpr .r26 = BitVec.ofNat 64 (cB s0) ∧ u.mem = t5.mem)
    (by
      prun [a27', a22', c_val]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (s0.gpr .r10).toNat < 2 ^ 64 by omega_arith),
        Nat.mod_eq_of_lt (show (PPC64LE.stackArg s0 1).toNat < 2 ^ 64 by omega_arith)]) (by decide))
    fun u ⟨⟨u26, um⟩, ku⟩ => ?_
  have K : Keep ldRegs t u := (((((k1.trans k2).trans k3).trans k4).trans k5).trans ku).mono
  have g : ∀ r ∈ [Reg.r21, .r23, .r24, .r25, .r27], u.gpr r = t.gpr r := fun r hr => K.gpr r (by revert r hr; decide)
  -- The digits still 0 at the end.
  have zz : ∀ i < nArr * (ww (kK s0) + 2), (160 + 4 * i + 4 ≤ arr (ww (kK s0)) aN ∨
      arr (ww (kK s0)) aN + 4 * ww (kK s0) ≤ 160 + 4 * i) →
      (160 + 4 * i + 4 ≤ arr (wW (kK s0)) wE ∨ arr (wW (kK s0)) wE + 4 * wW (kK s0) ≤ 160 + 4 * i) →
      (160 + 4 * i + 4 ≤ arr (wW (kK s0)) wD ∨ arr (wW (kK s0)) wD + 4 * wW (kK s0) ≤ 160 + 4 * i) →
      w32 u.mem (rvB s0) (160 + 4 * i) = 0 := fun i hi h1 h2 h3 => by
    have := hi; simp only [nArr] at this
    rw [um, w32_out o5 h3 (by omega_arith), w32_out o4 h2 (by omega_arith), m3]
    exact zz2 i hi h1
  have haE : arr (wW (kK s0)) wE = 160 + 4 * (wW (kK s0) + 2) := by
    have := hA wE 0; simp only [wE, Nat.one_mul, Nat.mul_zero, Nat.add_zero] at this; exact this
  have haD : arr (wW (kK s0)) wD = 160 + 4 * (2 * (wW (kK s0) + 2)) := by
    have := hA wD 0; simp only [wD, Nat.mul_zero, Nat.add_zero] at this; exact this
  refine ⟨⟨b5.of_regs ku um, w5.of_keep ku, (g _ (by decide)).trans e.args.r21, (g _ (by decide)).trans e.args.r23,
    (g _ (by decide)).trans e.args.r24, (g _ (by decide)).trans e.args.r25, u26, (g _ (by decide)).trans e.args.r27,
    ?_, ?_, ?_, ?_, ?_⟩, K⟩
  · simp only [VG.Proof.Rsa.KeyWorkspace.num]
    rw [um, val32_out o5 (by rw [haN, haD]; simp only [wW]; omega_arith) (by rw [haN]; simp only [nArr] at *; omega_arith),
      val32_out o4 (by rw [haN, haE]; simp only [wW]; omega_arith) (by rw [haN]; simp only [nArr] at *; omega_arith), m3]
    exact v2
  · simp only [VG.Proof.Rsa.KeyWorkspace.num]
    rw [um, val32_out o5 (by rw [haE, haD]; simp only [wW]; omega_arith) (by rw [haE]; simp only [wW]; omega_arith)]
    exact v4
  · rw [um]; exact v5
  · intro j hj i hi
    simp only [wZ, wM, wMod, List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [hA]
    rcases hj with rfl | rfl | rfl <;>
      exact zz _ (by simp only [nArr, wW] at hi ⊢; omega_arith) (by rw [haN]; simp only [wW] at hi ⊢; omega_arith)
        (by rw [haE]; simp only [wW] at hi ⊢; omega_arith) (by rw [haD]; simp only [wW] at hi ⊢; omega_arith)
  · intro j hj i hi
    simp only [aOne, aZ, List.mem_cons, List.not_mem_nil, or_false] at hj
    rw [hAw]
    rcases hj with rfl | rfl <;>
      exact zz _ (by simp only [nArr] at hi ⊢; omega_arith) (by rw [haN]; omega_arith)
        (by rw [haE]; simp only [wW] at hi ⊢; omega_arith) (by rw [haD]; simp only [wW] at hi ⊢; omega_arith)

end VG.Proof.Rsa.PPC64LE.Recover
