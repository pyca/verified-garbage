module

public import VerifiedGarbage.Proof.MlKem.X86_64.FragKM
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKg
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEnc
public import VerifiedGarbage.Proof.MlKem.X86_64.KpkeDec
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ML-KEM on x86-64: the calls of the K-PKE functions

What a call of `vg_mlkem*_kpke_keygen`, `vg_mlkem*_kpke_encrypt` or
`vg_mlkem*_kpke_decrypt` (with AVX2, on polynomials of `u16`s) needs of the
state (`KpkeKgH`, `KpkeEncH`, `KpkeDecH`) and of a layout (`kpChk`,
`keChk`, `kdChk`), what it computes, as of the caller's memory
(`kpkeKgAt_ok`, …), and that two runs leak the same (`kpkeKgAt_tr`, …).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The bytes of a region apart from the stack read the same on entry to a callee. -/
theorem ce_mem (st : State) {p : Addr} {n : Nat} (hn : n ≤ 2 ^ 64) (h : (below (st.gpr .rsp) 32).Disjoint ⟨p, n⟩) :
    ∀ i < n, st.callEntry.mem (p + BitVec.ofNat 64 i) = st.mem (p + BitVec.ofNat 64 i) :=
  fun _ hi => callEntry_bytes st (R := ⟨p, n⟩) (k16 st h) hn hi

/-- The calls of the K-PKE functions: each one's contract, met by its code. -/
structure KpkeOk (L : Kem) : Prop where
  kg : CalleeOk (kpkeKgK L) (kpkeKg L .avx2 keygenMul16Y)
  enc : CalleeOk (kpkeEncK L) (kpkeEnc L .avx2 encryptMul16Y)
  dec : CalleeOk (kpkeDecK L) (kpkeDec L .avx2 Kpke16.dmInnerY)

/-- What a call of `vg_mlkem*_kpke_keygen` of the parameter set `L` needs. -/
structure KpkeKgH (L : Kem) (ek dk a se z : Ptr) (st : State) : Prop where
  off : ek.2 < 2 ^ 31 ∧ dk.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ se.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  redA : VecReducedW 16 st.mem (pa st a) (L.k * L.k)
  redSE : VecReducedW 16 st.mem (pa st se) (2 * L.k)
  ed : Region.Disjoint ⟨pa st ek, 384 * L.k⟩ ⟨pa st dk, 384 * L.k⟩
  ea : Region.Disjoint ⟨pa st ek, 384 * L.k⟩ ⟨pa st a, 512 * (L.k * L.k)⟩
  es : Region.Disjoint ⟨pa st ek, 384 * L.k⟩ ⟨pa st se, 1024 * L.k⟩
  ez : Region.Disjoint ⟨pa st ek, 384 * L.k⟩ ⟨pa st z, kScrE⟩
  da : Region.Disjoint ⟨pa st dk, 384 * L.k⟩ ⟨pa st a, 512 * (L.k * L.k)⟩
  ds : Region.Disjoint ⟨pa st dk, 384 * L.k⟩ ⟨pa st se, 1024 * L.k⟩
  dz : Region.Disjoint ⟨pa st dk, 384 * L.k⟩ ⟨pa st z, kScrE⟩
  as : Region.Disjoint ⟨pa st a, 512 * (L.k * L.k)⟩ ⟨pa st se, 1024 * L.k⟩
  az : Region.Disjoint ⟨pa st a, 512 * (L.k * L.k)⟩ ⟨pa st z, kScrE⟩
  sz : Region.Disjoint ⟨pa st se, 1024 * L.k⟩ ⟨pa st z, kScrE⟩
  kE : (below (st.gpr .rsp) 32).Disjoint ⟨pa st ek, 384 * L.k⟩
  kD : (below (st.gpr .rsp) 32).Disjoint ⟨pa st dk, 384 * L.k⟩
  kA : (below (st.gpr .rsp) 32).Disjoint ⟨pa st a, 512 * (L.k * L.k)⟩
  kS : (below (st.gpr .rsp) 32).Disjoint ⟨pa st se, 1024 * L.k⟩
  kZ : (below (st.gpr .rsp) 32).Disjoint ⟨pa st z, kScrE⟩
  nE : (pa st ek).toNat + 384 * L.k ≤ 2 ^ 64
  nD : (pa st dk).toNat + 384 * L.k ≤ 2 ^ 64
  nA : (pa st a).toNat + 512 * (L.k * L.k) ≤ 2 ^ 64
  nS : (pa st se).toNat + 1024 * L.k ≤ 2 ^ 64
  nZ : (pa st z).toNat + kScrE ≤ 2 ^ 64
  c : Covers ([⟨pa st a, 512 * (L.k * L.k)⟩] ++
    [⟨pa st ek, 384 * L.k⟩, ⟨pa st dk, 384 * L.k⟩, ⟨pa st se, 1024 * L.k⟩, ⟨pa st z, kScrE⟩]) (st.rd ++ st.wr)
  wc : Covers [⟨pa st ek, 384 * L.k⟩, ⟨pa st dk, 384 * L.k⟩, ⟨pa st se, 1024 * L.k⟩, ⟨pa st z, kScrE⟩] st.wr

/-- The regions a call of `vg_mlkem*_kpke_keygen` reads and writes. -/
abbrev kpRd (L : Kem) (st : State) (a : Ptr) : List Region := [⟨pa st a, 512 * (L.k * L.k)⟩]
abbrev kpWr (L : Kem) (st : State) (ek dk se z : Ptr) : List Region :=
  [⟨pa st ek, 384 * L.k⟩, ⟨pa st dk, 384 * L.k⟩, ⟨pa st se, 1024 * L.k⟩, ⟨pa st z, kScrE⟩]

theorem kpPre {L : Kem} {ek dk a se z : Ptr} {st s1 : State} (H : KpkeKgH L ek dk a se z st)
    (hv : s1.gpr .rdi = pa st ek ∧ s1.gpr .rsi = pa st dk ∧ s1.gpr .rdx = pa st a ∧ s1.gpr .rcx = pa st se ∧
      s1.gpr .r8 = pa st z)
    (hm : s1.mem = st.mem) (k1 : Keep argRegs st s1) :
    (kpkeKgK L).pre (s1.callEntry.withRegions (kpRd L st a) (kpWr L st ek dk se z)) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  simp only [kpkeKgK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.r8 ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
  refine ⟨trivial, trivial, H.ed, H.ea, H.es, H.ez, H.da, H.ds, H.dz, H.as, H.az, H.sz,
    ret_disj s1 (by rw [hsp]; exact H.kE), ret_disj s1 (by rw [hsp]; exact H.kD),
    ret_disj s1 (by rw [hsp]; exact H.kA), ret_disj s1 (by rw [hsp]; exact H.kS),
    ret_disj s1 (by rw [hsp]; exact H.kZ), H.nE, H.nD, H.nA, H.nS, H.nZ, ?_, ?_⟩
  · rw [vecReducedW16_congr (fun i hi => (ce_mem s1 (by have := H.nA; omega) (by rw [hsp]; exact H.kA) i hi).trans (by rw [hm]))]
    exact H.redA
  · rw [vecReducedW16_congr (fun i hi => (ce_mem s1 (n := 1024 * L.k) (by have := H.nS; omega) (by rw [hsp]; exact H.kS) i (by omega)).trans
      (by rw [hm]))]
    exact H.redSE

/-- `ŝ` and `ê`, read from `se`. -/
abbrev sHatW (m : Mem) (se : Addr) (k : Nat) : List Poly := (vecAtW 16 m se k).map ntt
abbrev eHatW (m : Mem) (se : Addr) (k : Nat) : List Poly := (vecAtW 16 m (se + BitVec.ofNat 64 (512 * k)) k).map ntt

theorem kpkeKgAt_ok {L : Kem} (hK : KpkeOk L) {ek dk a se z : Ptr} (hd : NA dk) (ha : NA a) (hs : NA se) (hz : NA z)
    {st : State} (H : KpkeKgH L ek dk a se z st) :
    WP isa (L.kpkeKgAt ek dk a se z) st fun s' => Post st s' (kpWr L st ek dk se z) ∧
      bytesAt s'.mem (pa st ek) (384 * L.k) = encodeVec (addVec (mulMatVec (matAtW 16 st.mem (pa st a) L.k)
        (sHatW st.mem (pa st se) L.k)) (eHatW st.mem (pa st se) L.k)) ∧
      bytesAt s'.mem (pa st dk) (384 * L.k) = encodeVec (sHatW st.mem (pa st se) L.k) := by
  refine WP.mono (glueCall_ok hK.kg.ok hK.kg.nosp (by rw [hK.kg.depth]; decide)
    (kmGlue_ok ek dk a se z H.off hd ha hs hz st) (fun s1 hv hm k => kpPre H hv hm k) H.c H.wc)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  have hS := H.nS
  have eA : matAtW 16 s1.callEntry.mem (pa st a) L.k = matAtW 16 st.mem (pa st a) L.k :=
    matAtW16_congr fun i hi =>
      (ce_mem s1 (by have := H.nA; omega) (by rw [hsp]; exact H.kA) i hi).trans (by rw [hm])
  have eS : vecAtW 16 s1.callEntry.mem (pa st se) L.k = vecAtW 16 st.mem (pa st se) L.k :=
    vecAtW16_congr fun i hi =>
      (ce_mem s1 (n := 1024 * L.k) (by omega) (by rw [hsp]; exact H.kS) i (by omega)).trans (by rw [hm])
  have eE : vecAtW 16 s1.callEntry.mem (pa st se + BitVec.ofNat 64 (512 * L.k)) L.k =
      vecAtW 16 st.mem (pa st se + BitVec.ofNat 64 (512 * L.k)) L.k :=
    vecAtW16_congr fun i hi => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact (ce_mem s1 (n := 1024 * L.k) (by omega) (by rw [hsp]; exact H.kS) _ (by omega)).trans (by rw [hm])
  simp only [kpkeKgK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hm₂, eA, eS, eE] at hq
  exact hq

theorem kpkeKgAt_tr {L : Kem} (hK : KpkeOk L) {ek dk a se z : Ptr} (hd : NA dk) (ha : NA a) (hs : NA se)
    (hz : NA z) :
    RelCT isa (fun x y' => KpkeKgH L ek dk a se z x ∧ KpkeKgH L ek dk a se z y' ∧ x.gpr ek.1 = y'.gpr ek.1 ∧
      x.gpr dk.1 = y'.gpr dk.1 ∧ x.gpr a.1 = y'.gpr a.1 ∧ x.gpr se.1 = y'.gpr se.1 ∧ x.gpr z.1 = y'.gpr z.1 ∧
      x.gpr .rsp = y'.gpr .rsp)
      (L.kpkeKgAt ek dk a se z) fun _ _ => True :=
  glueCall_tr hK.kg.ok hK.kg.ct (V := fun x x1 => ((x1.gpr .rdi = pa x ek ∧
      x1.gpr .rsi = pa x dk ∧ x1.gpr .rdx = pa x a ∧ x1.gpr .rcx = pa x se ∧ x1.gpr .r8 = pa x z) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _))
      (lea_nomem _ _)) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y' ⟨hx, hy', _⟩ => ⟨kmGlue_ok ek dk a se z hx.off hd ha hs hz x, kmGlue_ok ek dk a se z hy'.off hd ha hs hz y'⟩)
    fun x y' x1 y1 ⟨hx, hy', e1, e2, e3, e4, e5, e6⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, kpPre hx hv1 hm1 k1, kpPre hy' hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy'.c, by rw [k2.2.2]; exact hy'.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e6]⟩
      simp only [kpkeKgK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2.1, hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2, pa, e1, e2, e3, e4, e5,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e6, and_self]

/-! ## `vg_mlkem*_kpke_encrypt` -/

/-- Memory that agrees on `n` bytes from `p` agrees on `l` of them from `p + o`. -/
theorem agree_off {m m' : Mem} {p : Addr} {n o l : Nat}
    (h : ∀ i < n, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) (hl : o + l ≤ n) :
    ∀ i < l, m' (p + BitVec.ofNat 64 o + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 o + BitVec.ofNat 64 i) :=
  fun i hi => by rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact h _ (by omega)

/-- The ciphertext of `K-PKE.Encrypt`, from memory that agrees on its inputs. -/
theorem encCt_congr (L : Kem) {m m' : Mem} {a t r msg : Addr}
    (hA : ∀ i < 512 * (L.k * L.k), m' (a + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i))
    (hT : ∀ i < 384 * L.k, m' (t + BitVec.ofNat 64 i) = m (t + BitVec.ofNat 64 i))
    (hR : ∀ i < 512 * (2 * L.k + 1), m' (r + BitVec.ofNat 64 i) = m (r + BitVec.ofNat 64 i))
    (hM : ∀ i < 32, m' (msg + BitVec.ofNat 64 i) = m (msg + BitVec.ofNat 64 i)) :
    encCt L m' a t r msg = encCt L m a t r msg := by
  have h0 : ∀ i < 512 * L.k, m' (r + BitVec.ofNat 64 i) = m (r + BitVec.ofNat 64 i) := fun i hi => hR i (by omega)
  simp only [encCt, matAtW16_congr hA, bytesAt_congr hT, bytesAt_congr hM, vecAtW16_congr h0,
    vecAtW16_congr (agree_off hR (o := 512 * L.k) (l := 512 * L.k) (by omega)),
    polyAtW16_congr (agree_off hR (o := 1024 * L.k) (l := 512) (by omega))]

theorem kpEncGlue_ok (ct a t r m z : Ptr)
    (ho : ct.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ t.2 < 2 ^ 31 ∧ r.2 < 2 ^ 31 ∧ m.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31)
    (ha : NA a) (ht : NA t) (hr : NA r) (hm : NA m) (hz : NA z) (st : State) :
    WP isa (.block (lea .rdi ct ++ lea .rsi a ++ lea .rdx t ++ lea .rcx r ++ lea .r8 m ++ lea .r9 z)) st fun s1 =>
      ((s1.gpr .rdi = pa st ct ∧ s1.gpr .rsi = pa st a ∧ s1.gpr .rdx = pa st t ∧ s1.gpr .rcx = pa st r ∧
        s1.gpr .r8 = pa st m ∧ s1.gpr .r9 = pa st z) ∧ s1.mem = st.mem) ∧ Keep argRegs st s1 := by
  have a1 : a.1 ≠ .rdi := fun e => ha (by rw [e]; decide)
  have t1 : t.1 ≠ .rdi := fun e => ht (by rw [e]; decide)
  have t2 : t.1 ≠ .rsi := fun e => ht (by rw [e]; decide)
  have r1 : r.1 ≠ .rdi := fun e => hr (by rw [e]; decide)
  have r2 : r.1 ≠ .rsi := fun e => hr (by rw [e]; decide)
  have r3 : r.1 ≠ .rdx := fun e => hr (by rw [e]; decide)
  have m1 : m.1 ≠ .rdi := fun e => hm (by rw [e]; decide)
  have m2 : m.1 ≠ .rsi := fun e => hm (by rw [e]; decide)
  have m3 : m.1 ≠ .rdx := fun e => hm (by rw [e]; decide)
  have m4 : m.1 ≠ .rcx := fun e => hm (by rw [e]; decide)
  have z1 : z.1 ≠ .rdi := fun e => hz (by rw [e]; decide)
  have z2 : z.1 ≠ .rsi := fun e => hz (by rw [e]; decide)
  have z3 : z.1 ≠ .rdx := fun e => hz (by rw [e]; decide)
  have z4 : z.1 ≠ .rcx := fun e => hz (by rw [e]; decide)
  have z5 : z.1 ≠ .r8 := fun e => hz (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2.1, sx_ofNat ho.2.2.1, sx_ofNat ho.2.2.2.1, sx_ofNat ho.2.2.2.2.1,
    sx_ofNat ho.2.2.2.2.2, a1, t1, t2, r1, r2, r3, m1, m2, m3, m4, z1, z2, z3, z4, z5, List.cons_append,
    List.nil_append]

/-- What a call of `vg_mlkem*_kpke_encrypt` of the parameter set `L` needs. -/
structure KpkeEncH (L : Kem) (ct a t r m z : Ptr) (st : State) : Prop where
  off : ct.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ t.2 < 2 ^ 31 ∧ r.2 < 2 ^ 31 ∧ m.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  redA : VecReducedW 16 st.mem (pa st a) (L.k * L.k)
  redR : VecReducedW 16 st.mem (pa st r) (2 * L.k + 1)
  ca : Region.Disjoint ⟨pa st ct, L.ctLen⟩ ⟨pa st a, 512 * (L.k * L.k)⟩
  ct' : Region.Disjoint ⟨pa st ct, L.ctLen⟩ ⟨pa st t, 384 * L.k⟩
  cr : Region.Disjoint ⟨pa st ct, L.ctLen⟩ ⟨pa st r, 512 * (2 * L.k + 1)⟩
  cm : Region.Disjoint ⟨pa st ct, L.ctLen⟩ ⟨pa st m, 32⟩
  cz : Region.Disjoint ⟨pa st ct, L.ctLen⟩ ⟨pa st z, kScrE⟩
  ar : Region.Disjoint ⟨pa st a, 512 * (L.k * L.k)⟩ ⟨pa st r, 512 * (2 * L.k + 1)⟩
  az : Region.Disjoint ⟨pa st a, 512 * (L.k * L.k)⟩ ⟨pa st z, kScrE⟩
  tr : Region.Disjoint ⟨pa st t, 384 * L.k⟩ ⟨pa st r, 512 * (2 * L.k + 1)⟩
  tz : Region.Disjoint ⟨pa st t, 384 * L.k⟩ ⟨pa st z, kScrE⟩
  rm : Region.Disjoint ⟨pa st r, 512 * (2 * L.k + 1)⟩ ⟨pa st m, 32⟩
  rz : Region.Disjoint ⟨pa st r, 512 * (2 * L.k + 1)⟩ ⟨pa st z, kScrE⟩
  mz : Region.Disjoint ⟨pa st m, 32⟩ ⟨pa st z, kScrE⟩
  kC : (below (st.gpr .rsp) 32).Disjoint ⟨pa st ct, L.ctLen⟩
  kA : (below (st.gpr .rsp) 32).Disjoint ⟨pa st a, 512 * (L.k * L.k)⟩
  kT : (below (st.gpr .rsp) 32).Disjoint ⟨pa st t, 384 * L.k⟩
  kR : (below (st.gpr .rsp) 32).Disjoint ⟨pa st r, 512 * (2 * L.k + 1)⟩
  kM : (below (st.gpr .rsp) 32).Disjoint ⟨pa st m, 32⟩
  kZ : (below (st.gpr .rsp) 32).Disjoint ⟨pa st z, kScrE⟩
  nC : (pa st ct).toNat + L.ctLen ≤ 2 ^ 64
  nA : (pa st a).toNat + 512 * (L.k * L.k) ≤ 2 ^ 64
  nT : (pa st t).toNat + 384 * L.k ≤ 2 ^ 64
  nR : (pa st r).toNat + 512 * (2 * L.k + 1) ≤ 2 ^ 64
  nM : (pa st m).toNat + 32 ≤ 2 ^ 64
  nZ : (pa st z).toNat + kScrE ≤ 2 ^ 64
  c : Covers ([⟨pa st a, 512 * (L.k * L.k)⟩, ⟨pa st t, 384 * L.k⟩, ⟨pa st m, 32⟩] ++
    [⟨pa st ct, L.ctLen⟩, ⟨pa st r, 512 * (2 * L.k + 1)⟩, ⟨pa st z, kScrE⟩]) (st.rd ++ st.wr)
  wc : Covers [⟨pa st ct, L.ctLen⟩, ⟨pa st r, 512 * (2 * L.k + 1)⟩, ⟨pa st z, kScrE⟩] st.wr

/-- The regions a call of `vg_mlkem*_kpke_encrypt` reads and writes. -/
abbrev keRd (L : Kem) (st : State) (a t m : Ptr) : List Region :=
  [⟨pa st a, 512 * (L.k * L.k)⟩, ⟨pa st t, 384 * L.k⟩, ⟨pa st m, 32⟩]
abbrev keWr (L : Kem) (st : State) (ct r z : Ptr) : List Region :=
  [⟨pa st ct, L.ctLen⟩, ⟨pa st r, 512 * (2 * L.k + 1)⟩, ⟨pa st z, kScrE⟩]

/-- The arguments of `vg_mlkem*_kpke_encrypt`, moved. -/
abbrev KeV (st : State) (ct a t r m z : Ptr) (s1 : State) : Prop :=
  s1.gpr .rdi = pa st ct ∧ s1.gpr .rsi = pa st a ∧ s1.gpr .rdx = pa st t ∧ s1.gpr .rcx = pa st r ∧
    s1.gpr .r8 = pa st m ∧ s1.gpr .r9 = pa st z

theorem kePre {L : Kem} {ct a t r m z : Ptr} {st s1 : State} (H : KpkeEncH L ct a t r m z st)
    (hv : KeV st ct a t r m z s1) (hm : s1.mem = st.mem) (k1 : Keep argRegs st s1) :
    (kpkeEncK L).pre (s1.callEntry.withRegions (keRd L st a t m) (keWr L st ct r z)) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hv
  simp only [kpkeEncK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.r8 ≠ .rsp), ce_gpr' s1 (by decide : Reg.r9 ≠ .rsp), h1, h2, h3, h4, h5, h6]
  refine ⟨trivial, trivial, H.ca, H.ct', H.cr, H.cm, H.cz, H.ar, H.az, H.tr, H.tz, H.rm, H.rz, H.mz,
    ret_disj s1 (by rw [hsp]; exact H.kC), ret_disj s1 (by rw [hsp]; exact H.kA),
    ret_disj s1 (by rw [hsp]; exact H.kT), ret_disj s1 (by rw [hsp]; exact H.kR),
    ret_disj s1 (by rw [hsp]; exact H.kM), ret_disj s1 (by rw [hsp]; exact H.kZ),
    H.nC, H.nA, H.nT, H.nR, H.nM, H.nZ, ?_, ?_⟩
  · rw [vecReducedW16_congr (fun i hi => (ce_mem s1 (by have := H.nA; omega) (by rw [hsp]; exact H.kA) i hi).trans
      (by rw [hm]))]
    exact H.redA
  · refine (vecReducedW16_congr (l := 2 * L.k + 1) fun i hi => ?_).mpr H.redR
    have hn : 512 * (2 * L.k + 1) ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left _ _) H.nR
    have hk : (below (s1.gpr .rsp) 32).Disjoint ⟨pa st r, 512 * (2 * L.k + 1)⟩ := by rw [hsp]; exact H.kR
    have := ce_mem s1 hn hk i hi
    rw [this, hm]

theorem kpkeEncAt_ok {L : Kem} (hK : KpkeOk L) {ct a t r m z : Ptr} (ha : NA a) (ht : NA t) (hr : NA r) (hm' : NA m)
    (hz : NA z) {st : State} (H : KpkeEncH L ct a t r m z st) :
    WP isa (L.kpkeEncAt ct a t r m z) st fun s' => Post st s' (keWr L st ct r z) ∧
      bytesAt s'.mem (pa st ct) L.ctLen = encCt L st.mem (pa st a) (pa st t) (pa st r) (pa st m) := by
  refine WP.mono (glueCall_ok hK.enc.ok hK.enc.nosp (by rw [hK.enc.depth]; decide)
    (kpEncGlue_ok ct a t r m z H.off ha ht hr hm' hz st) (fun s1 hv hm k => kePre H hv hm k) H.c H.wc)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  have ag : ∀ {p : Ptr} {n : Nat}, (pa st p).toNat + n ≤ 2 ^ 64 → (below (st.gpr .rsp) 32).Disjoint ⟨pa st p, n⟩ →
      ∀ i < n, s1.callEntry.mem (pa st p + BitVec.ofNat 64 i) = st.mem (pa st p + BitVec.ofNat 64 i) :=
    fun hn hk i hi => (ce_mem s1 (by omega) (by rw [hsp]; exact hk) i hi).trans (by rw [hm])
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := hV
  simp only [kpkeEncK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), ce_gpr' s1 (by decide : Reg.r8 ≠ .rsp), h1, h2, h3, h4, h5, hm₂,
    encCt_congr L (ag H.nA H.kA) (ag H.nT H.kT) (ag H.nR H.kR) (ag H.nM H.kM)] at hq
  exact hq

theorem kpkeEncAt_tr {L : Kem} (hK : KpkeOk L) {ct a t r m z : Ptr} (ha : NA a) (ht : NA t) (hr : NA r)
    (hm' : NA m) (hz : NA z) :
    RelCT isa (fun x y' => KpkeEncH L ct a t r m z x ∧ KpkeEncH L ct a t r m z y' ∧ x.gpr ct.1 = y'.gpr ct.1 ∧
      x.gpr a.1 = y'.gpr a.1 ∧ x.gpr t.1 = y'.gpr t.1 ∧ x.gpr r.1 = y'.gpr r.1 ∧ x.gpr m.1 = y'.gpr m.1 ∧
      x.gpr z.1 = y'.gpr z.1 ∧ x.gpr .rsp = y'.gpr .rsp)
      (L.kpkeEncAt ct a t r m z) fun _ _ => True :=
  glueCall_tr hK.enc.ok hK.enc.ct (V := fun x x1 => (KeV x ct a t r m z x1 ∧ x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _)
      (lea_nomem _ _)) (lea_nomem _ _)) (lea_nomem _ _)) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y' ⟨hx, hy', _⟩ => ⟨kpEncGlue_ok ct a t r m z hx.off ha ht hr hm' hz x,
      kpEncGlue_ok ct a t r m z hy'.off ha ht hr hm' hz y'⟩)
    fun x y' x1 y1 ⟨hx, hy', e1, e2, e3, e4, e5, e6, e7⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, kePre hx hv1 hm1 k1, kePre hy' hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy'.c, by rw [k2.2.2]; exact hy'.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e7]⟩
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hv1
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hv2
      simp only [kpkeEncK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), ce_gpr' _ (by decide : Reg.r8 ≠ .rsp),
        ce_gpr' _ (by decide : Reg.r9 ≠ .rsp), a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, pa, e1, e2, e3, e4,
        e5, e6, k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e7, and_self]

/-! ## `vg_mlkem*_kpke_decrypt` -/

/-- What a call of `vg_mlkem*_kpke_decrypt` of the parameter set `L` needs. -/
structure KpkeDecH (L : Kem) (m s ct z : Ptr) (st : State) : Prop where
  off : m.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ ct.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  ms : Region.Disjoint ⟨pa st m, 32⟩ ⟨pa st s, 384 * L.k⟩
  mc : Region.Disjoint ⟨pa st m, 32⟩ ⟨pa st ct, L.ctLen⟩
  mz : Region.Disjoint ⟨pa st m, 32⟩ ⟨pa st z, kScr⟩
  sz : Region.Disjoint ⟨pa st s, 384 * L.k⟩ ⟨pa st z, kScr⟩
  cz : Region.Disjoint ⟨pa st ct, L.ctLen⟩ ⟨pa st z, kScr⟩
  kM : (below (st.gpr .rsp) 32).Disjoint ⟨pa st m, 32⟩
  kS : (below (st.gpr .rsp) 32).Disjoint ⟨pa st s, 384 * L.k⟩
  kC : (below (st.gpr .rsp) 32).Disjoint ⟨pa st ct, L.ctLen⟩
  kZ : (below (st.gpr .rsp) 32).Disjoint ⟨pa st z, kScr⟩
  nM : (pa st m).toNat + 32 ≤ 2 ^ 64
  nS : (pa st s).toNat + 384 * L.k ≤ 2 ^ 64
  nC : (pa st ct).toNat + L.ctLen ≤ 2 ^ 64
  nZ : (pa st z).toNat + kScr ≤ 2 ^ 64
  c : Covers ([⟨pa st s, 384 * L.k⟩, ⟨pa st ct, L.ctLen⟩] ++ [⟨pa st m, 32⟩, ⟨pa st z, kScr⟩]) (st.rd ++ st.wr)
  wc : Covers [⟨pa st m, 32⟩, ⟨pa st z, kScr⟩] st.wr

/-- The regions a call of `vg_mlkem*_kpke_decrypt` reads and writes. -/
abbrev kdRd (L : Kem) (st : State) (s ct : Ptr) : List Region := [⟨pa st s, 384 * L.k⟩, ⟨pa st ct, L.ctLen⟩]
abbrev kdWr (st : State) (m z : Ptr) : List Region := [⟨pa st m, 32⟩, ⟨pa st z, kScr⟩]

theorem kdPre {L : Kem} {m s ct z : Ptr} {st s1 : State} (H : KpkeDecH L m s ct z st)
    (hv : s1.gpr .rdi = pa st m ∧ s1.gpr .rsi = pa st s ∧ s1.gpr .rdx = pa st ct ∧ s1.gpr .rcx = pa st z)
    (k1 : Keep argRegs st s1) :
    (kpkeDecK L).pre (s1.callEntry.withRegions (kdRd L st s ct) (kdWr st m z)) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  simp only [kpkeDecK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  exact ⟨trivial, trivial, H.ms, H.mc, H.mz, H.sz, H.cz,
    ret_disj s1 (by rw [hsp]; exact H.kM), ret_disj s1 (by rw [hsp]; exact H.kS),
    ret_disj s1 (by rw [hsp]; exact H.kC), ret_disj s1 (by rw [hsp]; exact H.kZ), H.nM, H.nS, H.nC, H.nZ⟩

theorem kpkeDecAt_ok {L : Kem} (hK : KpkeOk L) {m s ct z : Ptr} (hs : NA s) (hc : NA ct) (hz : NA z) {st : State}
    (H : KpkeDecH L m s ct z st) :
    WP isa (L.kpkeDecAt m s ct z) st fun s' => Post st s' (kdWr st m z) ∧
      bytesAt s'.mem (pa st m) 32 =
        kpkeDecrypt L.p (bytesAt st.mem (pa st s) (384 * L.k)) (bytesAt st.mem (pa st ct) L.ctLen) := by
  refine WP.mono (glueCall_ok hK.dec.ok hK.dec.nosp (by rw [hK.dec.depth]; decide)
    (dmGlue_ok m s ct z H.off hs hc hz st) (fun s1 hv _ k => kdPre H hv k) H.c H.wc)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  have hS := H.nS
  have hC := H.nC
  simp only [kpkeDecK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hm₂,
    bytesAt_congr (ce_mem s1 (n := 384 * L.k) (by omega) (by rw [hsp]; exact H.kS)),
    bytesAt_congr (ce_mem s1 (n := L.ctLen) (by omega) (by rw [hsp]; exact H.kC)), hm] at hq
  exact hq

theorem kpkeDecAt_tr {L : Kem} (hK : KpkeOk L) {m s ct z : Ptr} (hs : NA s) (hc : NA ct) (hz : NA z) :
    RelCT isa (fun x y' => KpkeDecH L m s ct z x ∧ KpkeDecH L m s ct z y' ∧ x.gpr m.1 = y'.gpr m.1 ∧
      x.gpr s.1 = y'.gpr s.1 ∧ x.gpr ct.1 = y'.gpr ct.1 ∧ x.gpr z.1 = y'.gpr z.1 ∧ x.gpr .rsp = y'.gpr .rsp)
      (L.kpkeDecAt m s ct z) fun _ _ => True :=
  glueCall_tr hK.dec.ok hK.dec.ct (V := fun x x1 => ((x1.gpr .rdi = pa x m ∧ x1.gpr .rsi = pa x s ∧
      x1.gpr .rdx = pa x ct ∧ x1.gpr .rcx = pa x z) ∧ x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _))
      (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y' ⟨hx, hy', _⟩ => ⟨dmGlue_ok m s ct z hx.off hs hc hz x, dmGlue_ok m s ct z hy'.off hs hc hz y'⟩)
    fun x y' x1 y1 ⟨hx, hy', e1, e2, e3, e4, e5⟩ ⟨⟨hv1, _⟩, k1⟩ ⟨⟨hv2, _⟩, k2⟩ => by
      refine ⟨_, _, _, _, kdPre hx hv1 k1, kdPre hy' hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy'.c, by rw [k2.2.2]; exact hy'.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e5]⟩
      simp only [kpkeDecK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1,
        hv2.2.2.2, pa, e1, e2, e3, e4, k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e5, and_self]

/-! ## In a layout -/

section
variable {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay rbs wbs s) {ws : List (Ptr × Nat)} {p : Ptr}
include L

theorem Lay.keepPolyW {f : Poly} (hP : PPostB s s' ws) (hc : keepB (rbs ++ wbs) ws p 512 = true)
    (h : PolyIsW 16 s.mem (pa s p) f) : PolyIsW 16 s'.mem (pa s' p) f := by
  rw [hP.pa (keepB_cs hc)]
  exact polyIsW16_frame hP.frame (L.fdisj hc) h

end

/-- The layout of a call of `vg_mlkem*_kpke_keygen`. -/
def kpChk (bs wbs : List (Reg × Nat)) (L : Kem) (ek dk a se z : Ptr) : Bool :=
  wrOk bs wbs ek (384 * L.k) && wrOk bs wbs dk (384 * L.k) && rdOk bs a (512 * (L.k * L.k)) &&
    wrOk bs wbs se (1024 * L.k) && wrOk bs wbs z kScrE &&
    sepB bs ek (384 * L.k) dk (384 * L.k) && sepB bs ek (384 * L.k) a (512 * (L.k * L.k)) &&
    sepB bs ek (384 * L.k) se (1024 * L.k) && sepB bs ek (384 * L.k) z kScrE &&
    sepB bs dk (384 * L.k) a (512 * (L.k * L.k)) && sepB bs dk (384 * L.k) se (1024 * L.k) &&
    sepB bs dk (384 * L.k) z kScrE && sepB bs a (512 * (L.k * L.k)) se (1024 * L.k) &&
    sepB bs a (512 * (L.k * L.k)) z kScrE && sepB bs se (1024 * L.k) z kScrE

section
variable {rbs wbs : List (Reg × Nat)} {st : State} (La : Lay rbs wbs st)
include La

theorem KpkeKgH.of {L : Kem} {ek dk a se z : Ptr} (hc : kpChk (rbs ++ wbs) wbs L ek dk a se z = true)
    (redA : VecReducedW 16 st.mem (pa st a) (L.k * L.k)) (redSE : VecReducedW 16 st.mem (pa st se) (2 * L.k)) :
    KpkeKgH L ek dk a se z st := by
  simp only [kpChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hoe, hre⟩, hwe⟩, ⟨⟨hod, hrd⟩, hwd⟩⟩, ⟨hoa, hra⟩⟩, ⟨⟨hos, hrs⟩, hws⟩⟩, ⟨⟨hoz, hrz⟩, hwz⟩⟩, s1⟩, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩, s10⟩ := hc
  exact ⟨⟨hoe, hod, hoa, hos, hoz⟩, redA, redSE, La.disj s1, La.disj s2, La.disj s3, La.disj s4, La.disj s5,
    La.disj s6, La.disj s7, La.disj s8, La.disj s9, La.disj s10, La.stkD hre, La.stkD hrd, La.stkD hra, La.stkD hrs,
    La.stkD hrz, La.nwp hre, La.nwp hrd, La.nwp hra, La.nwp hrs, La.nwp hrz,
    covers_append (covers_cons (La.cR hra) covers_nil)
      (covers_cons (La.cR hre) (covers_cons (La.cR hrd) (covers_cons (La.cR hrs) (covers_cons (La.cR hrz) covers_nil)))),
    covers_cons (La.cW hwe) (covers_cons (La.cW hwd) (covers_cons (La.cW hws) (covers_cons (La.cW hwz) covers_nil)))⟩

end

theorem kpChk_in {bs wbs : List (Reg × Nat)} {L : Kem} {ek dk a se z : Ptr} (hc : kpChk bs wbs L ek dk a se z = true) :
    inB bs ek (384 * L.k) = true ∧ inB bs dk (384 * L.k) = true ∧ inB bs a (512 * (L.k * L.k)) = true ∧
      inB bs se (1024 * L.k) = true ∧ inB bs z kScrE = true := by
  simp only [kpChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, wrOk_in h2, rdOk_in h3, wrOk_in h4, wrOk_in h5⟩

section
variable {L : Kem} (hK : KpkeOk L) {rbs wbs : List (Reg × Nat)}
include hK

theorem kpkeKgAt_okL {st : State} (La : Lay rbs wbs st) {ek dk a se z : Ptr} (hd : NA dk) (ha : NA a) (hs : NA se)
    (hz : NA z) (hc : kpChk (rbs ++ wbs) wbs L ek dk a se z = true)
    (redA : VecReducedW 16 st.mem (pa st a) (L.k * L.k)) (redSE : VecReducedW 16 st.mem (pa st se) (2 * L.k)) :
    WP isa (L.kpkeKgAt ek dk a se z) st fun s' =>
      PPost st s' [(ek, 384 * L.k), (dk, 384 * L.k), (se, 1024 * L.k), (z, kScrE)] ∧
      bytesAt s'.mem (pa st ek) (384 * L.k) = encodeVec (addVec (mulMatVec (matAtW 16 st.mem (pa st a) L.k)
        (sHatW st.mem (pa st se) L.k)) (eHatW st.mem (pa st se) L.k)) ∧
      bytesAt s'.mem (pa st dk) (384 * L.k) = encodeVec (sHatW st.mem (pa st se) L.k) :=
  kpkeKgAt_ok hK hd ha hs hz (KpkeKgH.of La hc redA redSE)

theorem kpkeKgAt_trL {ek dk a se z : Ptr} (hd : NA dk) (ha : NA a) (hs : NA se) (hz : NA z)
    (hc : kpChk (rbs ++ wbs) wbs L ek dk a se z = true) :
    RelCT isa (fun x y' => LRel rbs wbs x y' ∧
      (VecReducedW 16 x.mem (pa x a) (L.k * L.k) ∧ VecReducedW 16 x.mem (pa x se) (2 * L.k)) ∧
      (VecReducedW 16 y'.mem (pa y' a) (L.k * L.k) ∧ VecReducedW 16 y'.mem (pa y' se) (2 * L.k)))
      (L.kpkeKgAt ek dk a se z) fun _ _ => True :=
  RelCT.mono (kpkeKgAt_tr hK hd ha hs hz) (fun _ _ ⟨e, ⟨r1, r2⟩, r3, r4⟩ =>
    ⟨KpkeKgH.of e.1 hc r1 r2, KpkeKgH.of e.2.1 hc r3 r4, e.eq (kpChk_in hc).1, e.eq (kpChk_in hc).2.1,
      e.eq (kpChk_in hc).2.2.1, e.eq (kpChk_in hc).2.2.2.1, e.eq (kpChk_in hc).2.2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

end

/-- The layout of a call of `vg_mlkem*_kpke_encrypt`. -/
def keChk (bs wbs : List (Reg × Nat)) (L : Kem) (ct a t r m z : Ptr) : Bool :=
  wrOk bs wbs ct L.ctLen && rdOk bs a (512 * (L.k * L.k)) && rdOk bs t (384 * L.k) &&
    wrOk bs wbs r (512 * (2 * L.k + 1)) && rdOk bs m 32 && wrOk bs wbs z kScrE &&
    sepB bs ct L.ctLen a (512 * (L.k * L.k)) && sepB bs ct L.ctLen t (384 * L.k) &&
    sepB bs ct L.ctLen r (512 * (2 * L.k + 1)) && sepB bs ct L.ctLen m 32 && sepB bs ct L.ctLen z kScrE &&
    sepB bs a (512 * (L.k * L.k)) r (512 * (2 * L.k + 1)) && sepB bs a (512 * (L.k * L.k)) z kScrE &&
    sepB bs t (384 * L.k) r (512 * (2 * L.k + 1)) && sepB bs t (384 * L.k) z kScrE &&
    sepB bs r (512 * (2 * L.k + 1)) m 32 && sepB bs r (512 * (2 * L.k + 1)) z kScrE && sepB bs m 32 z kScrE

section
variable {rbs wbs : List (Reg × Nat)} {st : State} (La : Lay rbs wbs st)
include La

theorem KpkeEncH.of {L : Kem} {ct a t r m z : Ptr} (hc : keChk (rbs ++ wbs) wbs L ct a t r m z = true)
    (redA : VecReducedW 16 st.mem (pa st a) (L.k * L.k)) (redR : VecReducedW 16 st.mem (pa st r) (2 * L.k + 1)) :
    KpkeEncH L ct a t r m z st := by
  simp only [keChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hoc, hrc⟩, hwc⟩, ⟨hoa, hra⟩⟩, ⟨hot, hrt⟩⟩, ⟨⟨hor, hrr⟩, hwr⟩⟩, ⟨hom, hrm⟩⟩, ⟨⟨hoz, hrz⟩, hwz⟩⟩, s1⟩, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩, s10⟩, s11⟩, s12⟩ := hc
  exact ⟨⟨hoc, hoa, hot, hor, hom, hoz⟩, redA, redR, La.disj s1, La.disj s2, La.disj s3, La.disj s4, La.disj s5,
    La.disj s6, La.disj s7, La.disj s8, La.disj s9, La.disj s10, La.disj s11, La.disj s12, La.stkD hrc,
    La.stkD hra, La.stkD hrt, La.stkD hrr, La.stkD hrm, La.stkD hrz, La.nwp hrc, La.nwp hra, La.nwp hrt,
    La.nwp hrr, La.nwp hrm, La.nwp hrz,
    covers_append (covers_cons (La.cR hra) (covers_cons (La.cR hrt) (covers_cons (La.cR hrm) covers_nil)))
      (covers_cons (La.cR hrc) (covers_cons (La.cR hrr) (covers_cons (La.cR hrz) covers_nil))),
    covers_cons (La.cW hwc) (covers_cons (La.cW hwr) (covers_cons (La.cW hwz) covers_nil))⟩

end

theorem keChk_in {bs wbs : List (Reg × Nat)} {L : Kem} {ct a t r m z : Ptr}
    (hc : keChk bs wbs L ct a t r m z = true) :
    inB bs ct L.ctLen = true ∧ inB bs a (512 * (L.k * L.k)) = true ∧ inB bs t (384 * L.k) = true ∧
      inB bs r (512 * (2 * L.k + 1)) = true ∧ inB bs m 32 = true ∧ inB bs z kScrE = true := by
  simp only [keChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, rdOk_in h2, rdOk_in h3, wrOk_in h4, rdOk_in h5, wrOk_in h6⟩

/-- The layout of a call of `vg_mlkem*_kpke_decrypt`. -/
def kdChk (bs wbs : List (Reg × Nat)) (L : Kem) (m s ct z : Ptr) : Bool :=
  wrOk bs wbs m 32 && rdOk bs s (384 * L.k) && rdOk bs ct L.ctLen && wrOk bs wbs z kScr &&
    sepB bs m 32 s (384 * L.k) && sepB bs m 32 ct L.ctLen && sepB bs m 32 z kScr && sepB bs s (384 * L.k) z kScr &&
    sepB bs ct L.ctLen z kScr

section
variable {rbs wbs : List (Reg × Nat)} {st : State} (La : Lay rbs wbs st)
include La

theorem KpkeDecH.of {L : Kem} {m s ct z : Ptr} (hc : kdChk (rbs ++ wbs) wbs L m s ct z = true) :
    KpkeDecH L m s ct z st := by
  simp only [kdChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hom, hrm⟩, hwm⟩, ⟨hos, hrs⟩⟩, ⟨hoc, hrc⟩⟩, ⟨⟨hoz, hrz⟩, hwz⟩⟩, s1⟩, s2⟩, s3⟩, s4⟩, s5⟩ := hc
  exact ⟨⟨hom, hos, hoc, hoz⟩, La.disj s1, La.disj s2, La.disj s3, La.disj s4, La.disj s5, La.stkD hrm,
    La.stkD hrs, La.stkD hrc, La.stkD hrz, La.nwp hrm, La.nwp hrs, La.nwp hrc, La.nwp hrz,
    covers_append (covers_cons (La.cR hrs) (covers_cons (La.cR hrc) covers_nil))
      (covers_cons (La.cR hrm) (covers_cons (La.cR hrz) covers_nil)),
    covers_cons (La.cW hwm) (covers_cons (La.cW hwz) covers_nil)⟩

end

theorem kdChk_in {bs wbs : List (Reg × Nat)} {L : Kem} {m s ct z : Ptr} (hc : kdChk bs wbs L m s ct z = true) :
    inB bs m 32 = true ∧ inB bs s (384 * L.k) = true ∧ inB bs ct L.ctLen = true ∧ inB bs z kScr = true := by
  simp only [kdChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, rdOk_in h2, rdOk_in h3, wrOk_in h4⟩

section
variable {L : Kem} (hK : KpkeOk L) {rbs wbs : List (Reg × Nat)}
include hK

theorem kpkeEncAt_okL {st : State} (La : Lay rbs wbs st) {ct a t r m z : Ptr} (ha : NA a) (ht : NA t) (hr : NA r)
    (hm : NA m) (hz : NA z) (hc : keChk (rbs ++ wbs) wbs L ct a t r m z = true)
    (redA : VecReducedW 16 st.mem (pa st a) (L.k * L.k)) (redR : VecReducedW 16 st.mem (pa st r) (2 * L.k + 1)) :
    WP isa (L.kpkeEncAt ct a t r m z) st fun s' =>
      PPost st s' [(ct, L.ctLen), (r, 512 * (2 * L.k + 1)), (z, kScrE)] ∧
      bytesAt s'.mem (pa st ct) L.ctLen = encCt L st.mem (pa st a) (pa st t) (pa st r) (pa st m) :=
  kpkeEncAt_ok hK ha ht hr hm hz (KpkeEncH.of La hc redA redR)

theorem kpkeEncAt_trL {ct a t r m z : Ptr} (ha : NA a) (ht : NA t) (hr : NA r) (hm : NA m) (hz : NA z)
    (hc : keChk (rbs ++ wbs) wbs L ct a t r m z = true) :
    RelCT isa (fun x y' => LRel rbs wbs x y' ∧
      (VecReducedW 16 x.mem (pa x a) (L.k * L.k) ∧ VecReducedW 16 x.mem (pa x r) (2 * L.k + 1)) ∧
      (VecReducedW 16 y'.mem (pa y' a) (L.k * L.k) ∧ VecReducedW 16 y'.mem (pa y' r) (2 * L.k + 1)))
      (L.kpkeEncAt ct a t r m z) fun _ _ => True :=
  RelCT.mono (kpkeEncAt_tr hK ha ht hr hm hz) (fun _ _ ⟨e, ⟨r1, r2⟩, r3, r4⟩ =>
    ⟨KpkeEncH.of e.1 hc r1 r2, KpkeEncH.of e.2.1 hc r3 r4, e.eq (keChk_in hc).1, e.eq (keChk_in hc).2.1,
      e.eq (keChk_in hc).2.2.1, e.eq (keChk_in hc).2.2.2.1, e.eq (keChk_in hc).2.2.2.2.1,
      e.eq (keChk_in hc).2.2.2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

theorem kpkeDecAt_okL {st : State} (La : Lay rbs wbs st) {m s ct z : Ptr} (hs : NA s) (hct : NA ct) (hz : NA z)
    (hc : kdChk (rbs ++ wbs) wbs L m s ct z = true) :
    WP isa (L.kpkeDecAt m s ct z) st fun s' => PPost st s' [(m, 32), (z, kScr)] ∧
      bytesAt s'.mem (pa st m) 32 =
        kpkeDecrypt L.p (bytesAt st.mem (pa st s) (384 * L.k)) (bytesAt st.mem (pa st ct) L.ctLen) :=
  kpkeDecAt_ok hK hs hct hz (KpkeDecH.of La hc)

theorem kpkeDecAt_trL {m s ct z : Ptr} (hs : NA s) (hct : NA ct) (hz : NA z)
    (hc : kdChk (rbs ++ wbs) wbs L m s ct z = true) :
    RelCT isa (LRel rbs wbs) (L.kpkeDecAt m s ct z) fun _ _ => True :=
  RelCT.mono (kpkeDecAt_tr hK hs hct hz) (fun _ _ e =>
    ⟨KpkeDecH.of e.1 hc, KpkeDecH.of e.2.1 hc, e.eq (kdChk_in hc).1, e.eq (kdChk_in hc).2.1,
      e.eq (kdChk_in hc).2.2.1, e.eq (kdChk_in hc).2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

end

end VG.Proof.MlKem.X86_64
