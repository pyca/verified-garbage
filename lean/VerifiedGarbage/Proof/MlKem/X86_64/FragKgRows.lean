module

public import VerifiedGarbage.Proof.MlKem.X86_64.KgNtt
public import VerifiedGarbage.Proof.MlKem.X86_64.KgRow
import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
import VerifiedGarbage.Proof.MlKem.X86_64.FragDM
import VerifiedGarbage.Proof.MlKem.X86_64.FragL
import VerifiedGarbage.Proof.MlKem.PolyW
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem
public import VerifiedGarbage.Proof.MlKem.X86_64.FragOf
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem
public import VerifiedGarbage.Proof.MlKem.X86_64.FragOf

/-!
# ML-KEM on x86-64: the calls of K-PKE key generation a row at a time

As the call of `vg_mlkem*_kpke_keygen` (`FragKpke.lean`): what a call of
`vg_mlkem*_kpke_keygen_ntt` or `vg_mlkem*_kpke_keygen_row`
(`KpkeKgRows.lean`) needs of the state (`KgNttH`, `KgRowH`) and of a layout
(`knChk`, `krChk`), what it computes, as of the caller's memory
(`kgNttAt_okL`, `kgRowAt_okL`), and that two runs leak the same
(`kgNttAt_trL`, `kgRowAt_trL`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The two functions of K-PKE key generation a row at a time of the
parameter set `L`: each one's contract, met by its code. -/
structure KgRowsOk (L : Kem) : Prop where
  ntt : CalleeOk (kgNttK L.k) (KpkeKgRows.kgNtt L .avx2)
  row : CalleeOk (kgRowK L.k) (KpkeKgRows.kgRow L .avx2)

/-! ## `vg_mlkem*_kpke_keygen_ntt` -/

/-- What a call of `vg_mlkem*_kpke_keygen_ntt` of rank `k` needs. -/
structure KgNttH (k : Nat) (dk s e se z : Ptr) (st : State) : Prop where
  off : dk.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ e.2 < 2 ^ 31 ∧ se.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  red : VecReducedW 16 st.mem (pa st se) (2 * k)
  dS : Region.Disjoint ⟨pa st dk, 384 * k⟩ (vR (pa st s) k)
  dE : Region.Disjoint ⟨pa st dk, 384 * k⟩ (vR (pa st e) k)
  dR : Region.Disjoint ⟨pa st dk, 384 * k⟩ ⟨pa st se, 1024 * k⟩
  dC : Region.Disjoint ⟨pa st dk, 384 * k⟩ (cR (pa st z))
  sE : Region.Disjoint (vR (pa st s) k) (vR (pa st e) k)
  sR : Region.Disjoint (vR (pa st s) k) ⟨pa st se, 1024 * k⟩
  sC : Region.Disjoint (vR (pa st s) k) (cR (pa st z))
  eR : Region.Disjoint (vR (pa st e) k) ⟨pa st se, 1024 * k⟩
  eC : Region.Disjoint (vR (pa st e) k) (cR (pa st z))
  rC : Region.Disjoint ⟨pa st se, 1024 * k⟩ (cR (pa st z))
  kD : (below (st.gpr .rsp) 32).Disjoint ⟨pa st dk, 384 * k⟩
  kS : (below (st.gpr .rsp) 32).Disjoint (vR (pa st s) k)
  kE : (below (st.gpr .rsp) 32).Disjoint (vR (pa st e) k)
  kR : (below (st.gpr .rsp) 32).Disjoint ⟨pa st se, 1024 * k⟩
  kZ : (below (st.gpr .rsp) 32).Disjoint (cR (pa st z))
  nD : (pa st dk).toNat + 384 * k ≤ 2 ^ 64
  nS : (pa st s).toNat + 1024 * k ≤ 2 ^ 64
  nE : (pa st e).toNat + 1024 * k ≤ 2 ^ 64
  nR : (pa st se).toNat + 1024 * k ≤ 2 ^ 64
  nZ : (pa st z).toNat + 4096 ≤ 2 ^ 64
  c : Covers ([⟨pa st se, 1024 * k⟩] ++ [⟨pa st dk, 384 * k⟩, vR (pa st s) k, vR (pa st e) k, cR (pa st z)])
    (st.rd ++ st.wr)
  wc : Covers [⟨pa st dk, 384 * k⟩, vR (pa st s) k, vR (pa st e) k, cR (pa st z)] st.wr

theorem knPre {k : Nat} {dk s e se z : Ptr} {st s1 : State} (H : KgNttH k dk s e se z st)
    (hv : s1.gpr .rdi = pa st dk ∧ s1.gpr .rsi = pa st s ∧ s1.gpr .rdx = pa st e ∧ s1.gpr .rcx = pa st se ∧
      s1.gpr .r8 = pa st z)
    (hm : s1.mem = st.mem) (k1 : Keep argRegs st s1) :
    (kgNttK k).pre (s1.callEntry.withRegions [⟨pa st se, 1024 * k⟩]
      [⟨pa st dk, 384 * k⟩, vR (pa st s) k, vR (pa st e) k, cR (pa st z)]) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  simp only [kgNttK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.r8 ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
  refine ⟨trivial, trivial, H.dS, H.dE, H.dR, H.dC, H.sE, H.sR, H.sC, H.eR, H.eC, H.rC,
    ret_disj s1 (by rw [hsp]; exact H.kD), ret_disj s1 (by rw [hsp]; exact H.kS),
    ret_disj s1 (by rw [hsp]; exact H.kE), ret_disj s1 (by rw [hsp]; exact H.kR),
    ret_disj s1 (by rw [hsp]; exact H.kZ), H.nD, H.nS, H.nE, H.nR, H.nZ, ?_⟩
  rw [vecReducedW16_congr (fun i hi => (ce_mem s1 (n := 1024 * k) (by have := H.nR; omega)
    (by rw [hsp]; exact H.kR) i (by omega)).trans (by rw [hm]))]
  exact H.red

section
variable {L : Kem} (hK : KgRowsOk L)
include hK

theorem kgNttAt_ok {dk s e se z : Ptr} (hs : NA s) (he : NA e) (hse : NA se) (hz : NA z) {st : State}
    (H : KgNttH L.k dk s e se z st) :
    WP isa (L.kgNttAt dk s e se z) st fun s' =>
      Post st s' [⟨pa st dk, 384 * L.k⟩, vR (pa st s) L.k, vR (pa st e) L.k, cR (pa st z)] ∧
      VecIs s'.mem (pa st s) L.k ((vecAtW 16 st.mem (pa st se) L.k).map ntt) ∧
      VecIs s'.mem (pa st e) L.k ((vecAtW 16 st.mem (pa st se + BitVec.ofNat 64 (512 * L.k)) L.k).map ntt) ∧
      bytesAt s'.mem (pa st dk) (384 * L.k) = encodeVec ((vecAtW 16 st.mem (pa st se) L.k).map ntt) := by
  refine WP.mono (glueCall_ok hK.ntt.ok hK.ntt.nosp (by rw [hK.ntt.depth]; decide)
    (kmGlue_ok dk s e se z H.off hs he hse hz st) (fun s1 hv hm k => knPre H hv hm k) H.c H.wc)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  have hR := H.nR
  have eS : vecAtW 16 s1.callEntry.mem (pa st se) L.k = vecAtW 16 st.mem (pa st se) L.k :=
    vecAtW16_congr fun i hi =>
      (ce_mem s1 (n := 1024 * L.k) (by omega) (by rw [hsp]; exact H.kR) i (by omega)).trans (by rw [hm])
  have eE : vecAtW 16 s1.callEntry.mem (pa st se + BitVec.ofNat 64 (512 * L.k)) L.k =
      vecAtW 16 st.mem (pa st se + BitVec.ofNat 64 (512 * L.k)) L.k :=
    vecAtW16_congr fun i hi => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact (ce_mem s1 (n := 1024 * L.k) (by omega) (by rw [hsp]; exact H.kR) _ (by omega)).trans (by rw [hm])
  simp only [kgNttK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hm₂, eS, eE] at hq
  exact hq

theorem kgNttAt_tr {dk s e se z : Ptr} (hs : NA s) (he : NA e) (hse : NA se) (hz : NA z) :
    RelCT isa (fun x y' => KgNttH L.k dk s e se z x ∧ KgNttH L.k dk s e se z y' ∧ x.gpr dk.1 = y'.gpr dk.1 ∧
      x.gpr s.1 = y'.gpr s.1 ∧ x.gpr e.1 = y'.gpr e.1 ∧ x.gpr se.1 = y'.gpr se.1 ∧ x.gpr z.1 = y'.gpr z.1 ∧
      x.gpr .rsp = y'.gpr .rsp)
      (L.kgNttAt dk s e se z) fun _ _ => True :=
  glueCall_tr hK.ntt.ok hK.ntt.ct (V := fun x x1 => ((x1.gpr .rdi = pa x dk ∧
      x1.gpr .rsi = pa x s ∧ x1.gpr .rdx = pa x e ∧ x1.gpr .rcx = pa x se ∧ x1.gpr .r8 = pa x z) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _))
      (lea_nomem _ _)) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y' ⟨hx, hy', _⟩ => ⟨kmGlue_ok dk s e se z hx.off hs he hse hz x,
      kmGlue_ok dk s e se z hy'.off hs he hse hz y'⟩)
    fun x y' x1 y1 ⟨hx, hy', e1, e2, e3, e4, e5, e6⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, knPre hx hv1 hm1 k1, knPre hy' hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy'.c, by rw [k2.2.2]; exact hy'.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e6]⟩
      simp only [kgNttK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2.1, hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2, pa, e1, e2, e3, e4, e5,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e6, and_self]

end

/-! ## `vg_mlkem*_kpke_keygen_row` -/

/-- What a call of `vg_mlkem*_kpke_keygen_row` of rank `k` needs. -/
structure KgRowH (k : Nat) (ek a s e z : Ptr) (st : State) : Prop where
  off : ek.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ e.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  redA : VecReducedW 16 st.mem (pa st a) k
  redS : VecReduced st.mem (pa st s) k
  redE : Reduced st.mem (pa st e)
  kA : Region.Disjoint ⟨pa st ek, 384⟩ ⟨pa st a, 512 * k⟩
  kS : Region.Disjoint ⟨pa st ek, 384⟩ (vR (pa st s) k)
  kE : Region.Disjoint ⟨pa st ek, 384⟩ (pR (pa st e))
  kC : Region.Disjoint ⟨pa st ek, 384⟩ (cR (pa st z))
  aE : Region.Disjoint ⟨pa st a, 512 * k⟩ (pR (pa st e))
  aC : Region.Disjoint ⟨pa st a, 512 * k⟩ (cR (pa st z))
  sE : Region.Disjoint (vR (pa st s) k) (pR (pa st e))
  sC : Region.Disjoint (vR (pa st s) k) (cR (pa st z))
  eC : Region.Disjoint (pR (pa st e)) (cR (pa st z))
  xK : (below (st.gpr .rsp) 32).Disjoint ⟨pa st ek, 384⟩
  xA : (below (st.gpr .rsp) 32).Disjoint ⟨pa st a, 512 * k⟩
  xS : (below (st.gpr .rsp) 32).Disjoint (vR (pa st s) k)
  xE : (below (st.gpr .rsp) 32).Disjoint (pR (pa st e))
  xZ : (below (st.gpr .rsp) 32).Disjoint (cR (pa st z))
  nK : (pa st ek).toNat + 384 ≤ 2 ^ 64
  nA : (pa st a).toNat + 512 * k ≤ 2 ^ 64
  nS : (pa st s).toNat + 1024 * k ≤ 2 ^ 64
  nE : (pa st e).toNat + 1024 ≤ 2 ^ 64
  nZ : (pa st z).toNat + 4096 ≤ 2 ^ 64
  c : Covers ([⟨pa st a, 512 * k⟩, vR (pa st s) k] ++ [⟨pa st ek, 384⟩, pR (pa st e), cR (pa st z)])
    (st.rd ++ st.wr)
  wc : Covers [⟨pa st ek, 384⟩, pR (pa st e), cR (pa st z)] st.wr

theorem krPre {k : Nat} {ek a s e z : Ptr} {st s1 : State} (H : KgRowH k ek a s e z st)
    (hv : s1.gpr .rdi = pa st ek ∧ s1.gpr .rsi = pa st a ∧ s1.gpr .rdx = pa st s ∧ s1.gpr .rcx = pa st e ∧
      s1.gpr .r8 = pa st z)
    (hm : s1.mem = st.mem) (k1 : Keep argRegs st s1) :
    (kgRowK k).pre (s1.callEntry.withRegions [⟨pa st a, 512 * k⟩, vR (pa st s) k]
      [⟨pa st ek, 384⟩, pR (pa st e), cR (pa st z)]) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  simp only [kgRowK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.r8 ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
  refine ⟨trivial, trivial, H.kA, H.kS, H.kE, H.kC, H.aE, H.aC, H.sE, H.sC, H.eC,
    ret_disj s1 (by rw [hsp]; exact H.xK), ret_disj s1 (by rw [hsp]; exact H.xA),
    ret_disj s1 (by rw [hsp]; exact H.xS), ret_disj s1 (by rw [hsp]; exact H.xE),
    ret_disj s1 (by rw [hsp]; exact H.xZ), H.nK, H.nA, H.nS, H.nE, H.nZ, ?_, fun i hi => ?_, ?_⟩
  · rw [vecReducedW16_congr (fun i hi => (ce_mem s1 (n := 512 * k) (by have := H.nA; omega)
      (by rw [hsp]; exact H.xA) i hi).trans (by rw [hm]))]
    exact H.redA
  · rw [ce_reduced s1 (by rw [hsp]; exact H.xS.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redS i hi
  · rw [ce_reduced s1 (by rw [hsp]; exact H.xE), hm]; exact H.redE

section
variable {L : Kem} (hK : KgRowsOk L)
include hK

theorem kgRowAt_ok {ek a s e z : Ptr} (ha : NA a) (hs : NA s) (he : NA e) (hz : NA z) {st : State}
    (H : KgRowH L.k ek a s e z st) :
    WP isa (L.kgRowAt ek a s e z) st fun s' =>
      Post st s' [⟨pa st ek, 384⟩, pR (pa st e), cR (pa st z)] ∧
      bytesAt s'.mem (pa st ek) 384 =
        encode12 (add (dot (vecAtW 16 st.mem (pa st a) L.k) (vecAt st.mem (pa st s) L.k)) (polyAt st.mem (pa st e))) := by
  refine WP.mono (glueCall_ok hK.row.ok hK.row.nosp (by rw [hK.row.depth]; decide)
    (kmGlue_ok ek a s e z H.off ha hs he hz st) (fun s1 hv hm k => krPre H hv hm k) H.c H.wc)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  have hA := H.nA
  have eA : vecAtW 16 s1.callEntry.mem (pa st a) L.k = vecAtW 16 st.mem (pa st a) L.k :=
    vecAtW16_congr fun i hi =>
      (ce_mem s1 (n := 512 * L.k) (by omega) (by rw [hsp]; exact H.xA) i hi).trans (by rw [hm])
  simp only [kgRowK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hm₂, eA,
    ce_vecAt s1 (by rw [hsp]; exact H.xS), ce_polyAt s1 (by rw [hsp]; exact H.xE), hm] at hq
  exact hq

theorem kgRowAt_tr {ek a s e z : Ptr} (ha : NA a) (hs : NA s) (he : NA e) (hz : NA z) :
    RelCT isa (fun x y' => KgRowH L.k ek a s e z x ∧ KgRowH L.k ek a s e z y' ∧ x.gpr ek.1 = y'.gpr ek.1 ∧
      x.gpr a.1 = y'.gpr a.1 ∧ x.gpr s.1 = y'.gpr s.1 ∧ x.gpr e.1 = y'.gpr e.1 ∧ x.gpr z.1 = y'.gpr z.1 ∧
      x.gpr .rsp = y'.gpr .rsp)
      (L.kgRowAt ek a s e z) fun _ _ => True :=
  glueCall_tr hK.row.ok hK.row.ct (V := fun x x1 => ((x1.gpr .rdi = pa x ek ∧
      x1.gpr .rsi = pa x a ∧ x1.gpr .rdx = pa x s ∧ x1.gpr .rcx = pa x e ∧ x1.gpr .r8 = pa x z) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _))
      (lea_nomem _ _)) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y' ⟨hx, hy', _⟩ => ⟨kmGlue_ok ek a s e z hx.off ha hs he hz x,
      kmGlue_ok ek a s e z hy'.off ha hs he hz y'⟩)
    fun x y' x1 y1 ⟨hx, hy', e1, e2, e3, e4, e5, e6⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, krPre hx hv1 hm1 k1, krPre hy' hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy'.c, by rw [k2.2.2]; exact hy'.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e6]⟩
      simp only [kgRowK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2.1, hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2, pa, e1, e2, e3, e4, e5,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e6, and_self]

end

/-! ## In a layout -/

/-- The layout of a call of `vg_mlkem*_kpke_keygen_ntt`. -/
def knChk (bs wbs : List (Reg × Nat)) (k : Nat) (dk s e se z : Ptr) : Bool :=
  wrOk bs wbs dk (384 * k) && wrOk bs wbs s (1024 * k) && wrOk bs wbs e (1024 * k) && rdOk bs se (1024 * k) &&
    wrOk bs wbs z 4096 &&
    sepB bs dk (384 * k) s (1024 * k) && sepB bs dk (384 * k) e (1024 * k) && sepB bs dk (384 * k) se (1024 * k) &&
    sepB bs dk (384 * k) z 4096 && sepB bs s (1024 * k) e (1024 * k) && sepB bs s (1024 * k) se (1024 * k) &&
    sepB bs s (1024 * k) z 4096 && sepB bs e (1024 * k) se (1024 * k) && sepB bs e (1024 * k) z 4096 &&
    sepB bs se (1024 * k) z 4096

/-- The layout of a call of `vg_mlkem*_kpke_keygen_row`. -/
def krChk (bs wbs : List (Reg × Nat)) (k : Nat) (ek a s e z : Ptr) : Bool :=
  wrOk bs wbs ek 384 && rdOk bs a (512 * k) && rdOk bs s (1024 * k) && wrOk bs wbs e 1024 &&
    wrOk bs wbs z 4096 &&
    sepB bs ek 384 a (512 * k) && sepB bs ek 384 s (1024 * k) && sepB bs ek 384 e 1024 && sepB bs ek 384 z 4096 &&
    sepB bs a (512 * k) e 1024 && sepB bs a (512 * k) z 4096 && sepB bs s (1024 * k) e 1024 &&
    sepB bs s (1024 * k) z 4096 && sepB bs e 1024 z 4096

section
variable {rbs wbs : List (Reg × Nat)} {st : State} (La : Lay rbs wbs st)
include La

theorem KgNttH.of {k : Nat} {dk s e se z : Ptr} (hc : knChk (rbs ++ wbs) wbs k dk s e se z = true)
    (red : VecReducedW 16 st.mem (pa st se) (2 * k)) : KgNttH k dk s e se z st := by
  simp only [knChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hod, hrd⟩, hwd⟩, ⟨⟨hos, hrs⟩, hws⟩⟩, ⟨⟨hoe, hre⟩, hwe⟩⟩, ⟨hor, hrr⟩⟩, ⟨⟨hoz, hrz⟩, hwz⟩⟩,
    s1⟩, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩, s10⟩ := hc
  exact ⟨⟨hod, hos, hoe, hor, hoz⟩, red, La.disj s1, La.disj s2, La.disj s3, La.disj s4, La.disj s5,
    La.disj s6, La.disj s7, La.disj s8, La.disj s9, La.disj s10, La.stkD hrd, La.stkD hrs, La.stkD hre,
    La.stkD hrr, La.stkD hrz, La.nwp hrd, La.nwp hrs, La.nwp hre, La.nwp hrr, La.nwp hrz,
    covers_append (covers_cons (La.cR hrr) covers_nil)
      (covers_cons (La.cR hrd) (covers_cons (La.cR hrs) (covers_cons (La.cR hre) (covers_cons (La.cR hrz) covers_nil)))),
    covers_cons (La.cW hwd) (covers_cons (La.cW hws) (covers_cons (La.cW hwe) (covers_cons (La.cW hwz) covers_nil)))⟩

theorem KgRowH.of {k : Nat} {ek a s e z : Ptr} (hc : krChk (rbs ++ wbs) wbs k ek a s e z = true)
    (redA : VecReducedW 16 st.mem (pa st a) k) (redS : VecReduced st.mem (pa st s) k)
    (redE : Reduced st.mem (pa st e)) : KgRowH k ek a s e z st := by
  simp only [krChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hok, hrk⟩, hwk⟩, ⟨hoa, hra⟩⟩, ⟨hos, hrs⟩⟩, ⟨⟨hoe, hre⟩, hwe⟩⟩, ⟨⟨hoz, hrz⟩, hwz⟩⟩,
    s1⟩, s2⟩, s3⟩, s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩ := hc
  exact ⟨⟨hok, hoa, hos, hoe, hoz⟩, redA, redS, redE, La.disj s1, La.disj s2, La.disj s3, La.disj s4,
    La.disj s5, La.disj s6, La.disj s7, La.disj s8, La.disj s9, La.stkD hrk, La.stkD hra, La.stkD hrs,
    La.stkD hre, La.stkD hrz, La.nwp hrk, La.nwp hra, La.nwp hrs, La.nwp hre, La.nwp hrz,
    covers_append (covers_cons (La.cR hra) (covers_cons (La.cR hrs) covers_nil))
      (covers_cons (La.cR hrk) (covers_cons (La.cR hre) (covers_cons (La.cR hrz) covers_nil))),
    covers_cons (La.cW hwk) (covers_cons (La.cW hwe) (covers_cons (La.cW hwz) covers_nil))⟩

end

theorem knChk_in {bs wbs : List (Reg × Nat)} {k : Nat} {dk s e se z : Ptr} (hc : knChk bs wbs k dk s e se z = true) :
    inB bs dk (384 * k) = true ∧ inB bs s (1024 * k) = true ∧ inB bs e (1024 * k) = true ∧
      inB bs se (1024 * k) = true ∧ inB bs z 4096 = true := by
  simp only [knChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, wrOk_in h2, wrOk_in h3, rdOk_in h4, wrOk_in h5⟩

theorem krChk_in {bs wbs : List (Reg × Nat)} {k : Nat} {ek a s e z : Ptr} (hc : krChk bs wbs k ek a s e z = true) :
    inB bs ek 384 = true ∧ inB bs a (512 * k) = true ∧ inB bs s (1024 * k) = true ∧
      inB bs e 1024 = true ∧ inB bs z 4096 = true := by
  simp only [krChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, rdOk_in h2, rdOk_in h3, wrOk_in h4, wrOk_in h5⟩

section
variable {L : Kem} (hK : KgRowsOk L) {rbs wbs : List (Reg × Nat)}
include hK

theorem kgNttAt_okL {st : State} (La : Lay rbs wbs st) {dk s e se z : Ptr} (hs : NA s) (he : NA e) (hse : NA se)
    (hz : NA z) (hc : knChk (rbs ++ wbs) wbs L.k dk s e se z = true)
    (red : VecReducedW 16 st.mem (pa st se) (2 * L.k)) :
    WP isa (L.kgNttAt dk s e se z) st fun s' =>
      PPost st s' [(dk, 384 * L.k), (s, 1024 * L.k), (e, 1024 * L.k), (z, 4096)] ∧
      VecIs s'.mem (pa st s) L.k ((vecAtW 16 st.mem (pa st se) L.k).map ntt) ∧
      VecIs s'.mem (pa st e) L.k ((vecAtW 16 st.mem (pa st se + BitVec.ofNat 64 (512 * L.k)) L.k).map ntt) ∧
      bytesAt s'.mem (pa st dk) (384 * L.k) = encodeVec ((vecAtW 16 st.mem (pa st se) L.k).map ntt) :=
  kgNttAt_ok hK hs he hse hz (KgNttH.of La hc red)

theorem kgNttAt_trL {dk s e se z : Ptr} (hs : NA s) (he : NA e) (hse : NA se) (hz : NA z)
    (hc : knChk (rbs ++ wbs) wbs L.k dk s e se z = true) :
    RelCT isa (fun x y' => LRel rbs wbs x y' ∧ VecReducedW 16 x.mem (pa x se) (2 * L.k) ∧
      VecReducedW 16 y'.mem (pa y' se) (2 * L.k))
      (L.kgNttAt dk s e se z) fun _ _ => True :=
  RelCT.mono (kgNttAt_tr hK hs he hse hz) (fun _ _ ⟨e, r1, r2⟩ =>
    ⟨KgNttH.of e.1 hc r1, KgNttH.of e.2.1 hc r2, e.eq (knChk_in hc).1, e.eq (knChk_in hc).2.1,
      e.eq (knChk_in hc).2.2.1, e.eq (knChk_in hc).2.2.2.1, e.eq (knChk_in hc).2.2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

theorem kgRowAt_okL {st : State} (La : Lay rbs wbs st) {ek a s e z : Ptr} (ha : NA a) (hs : NA s) (he : NA e)
    (hz : NA z) (hc : krChk (rbs ++ wbs) wbs L.k ek a s e z = true)
    (redA : VecReducedW 16 st.mem (pa st a) L.k) (redS : VecReduced st.mem (pa st s) L.k)
    (redE : Reduced st.mem (pa st e)) :
    WP isa (L.kgRowAt ek a s e z) st fun s' => PPost st s' [(ek, 384), (e, 1024), (z, 4096)] ∧
      bytesAt s'.mem (pa st ek) 384 =
        encode12 (add (dot (vecAtW 16 st.mem (pa st a) L.k) (vecAt st.mem (pa st s) L.k)) (polyAt st.mem (pa st e))) :=
  kgRowAt_ok hK ha hs he hz (KgRowH.of La hc redA redS redE)

theorem kgRowAt_trL {ek a s e z : Ptr} (ha : NA a) (hs : NA s) (he : NA e) (hz : NA z)
    (hc : krChk (rbs ++ wbs) wbs L.k ek a s e z = true) :
    RelCT isa (fun x y' => LRel rbs wbs x y' ∧
      (VecReducedW 16 x.mem (pa x a) L.k ∧ VecReduced x.mem (pa x s) L.k ∧ Reduced x.mem (pa x e)) ∧
      (VecReducedW 16 y'.mem (pa y' a) L.k ∧ VecReduced y'.mem (pa y' s) L.k ∧ Reduced y'.mem (pa y' e)))
      (L.kgRowAt ek a s e z) fun _ _ => True :=
  RelCT.mono (kgRowAt_tr hK ha hs he hz) (fun _ _ ⟨e, ⟨r1, r2, r3⟩, r4, r5, r6⟩ =>
    ⟨KgRowH.of e.1 hc r1 r2 r3, KgRowH.of e.2.1 hc r4 r5 r6, e.eq (krChk_in hc).1, e.eq (krChk_in hc).2.1,
      e.eq (krChk_in hc).2.2.1, e.eq (krChk_in hc).2.2.2.1, e.eq (krChk_in hc).2.2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

end

end VG.Proof.MlKem.X86_64
