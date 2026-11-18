module

public import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
meta import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
public import VerifiedGarbage.Proof.MlKem.X86_64.FragS4
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragS4
public import VerifiedGarbage.Proof.MlKem.X86_64.Prfs
meta import VerifiedGarbage.Proof.MlKem.X86_64.Prfs
public import VerifiedGarbage.Impl.MlKem.X86_64.KeyGen
meta import VerifiedGarbage.Impl.MlKem.X86_64.KeyGen
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.Bignum.Layout
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Words
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.PolyW
meta import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragC
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragL
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Word
meta import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem
public import VerifiedGarbage.Proof.MlKem.X86_64.FragOf
import VerifiedGarbage.Proof.MlKem.X86_64.FragL
meta import VerifiedGarbage.Impl.MlKem.X86_64.Kem
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragOf

/-! ### `MlKem.X86_64.FragKM`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.FragEM`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.FragDM`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: the call of `vg_mlkem*_decrypt_mul`

As the calls of the polynomial primitives (`FragPrim.lean`, `FragOf.lean`,
`FragL.lean`): what a call of `vg_mlkem*_decrypt_mul` writing `w` from the
`k` polynomials from `s` and from `u`, with the working space `z`, needs of
the state (`DecMulH`), of a layout (`dmChk`, `DecMulH.of`), what it
computes (`decMulAt_ok`) and that two runs leak the same (`decMulAt_tr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- What a call of `vg_mlkem*_decrypt_mul` of rank `k` needs. -/
structure DecMulH (k : Nat) (w s u z : Ptr) (st : State) : Prop where
  off : w.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ u.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  redS : VecReduced st.mem (pa st s) k
  redU : VecReduced st.mem (pa st u) k
  ws : (pR (pa st w)).Disjoint (vR (pa st s) k)
  wu : (pR (pa st w)).Disjoint (vR (pa st u) k)
  wz : (pR (pa st w)).Disjoint (cR (pa st z))
  sz : (vR (pa st s) k).Disjoint (cR (pa st z))
  uz : (vR (pa st u) k).Disjoint (cR (pa st z))
  kW : (below (st.gpr .rsp) 32).Disjoint (pR (pa st w))
  kS : (below (st.gpr .rsp) 32).Disjoint (vR (pa st s) k)
  kU : (below (st.gpr .rsp) 32).Disjoint (vR (pa st u) k)
  kZ : (below (st.gpr .rsp) 32).Disjoint (cR (pa st z))
  c : Covers ([vR (pa st s) k, vR (pa st u) k] ++ [pR (pa st w), cR (pa st z)]) (st.rd ++ st.wr)
  wc : Covers [pR (pa st w), cR (pa st z)] st.wr

theorem dmGlue_ok (w s u z : Ptr) (ho : w.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ u.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31) (hs : NA s)
    (hu : NA u) (hz : NA z) (st : State) :
    WP isa (.block (lea .rdi w ++ lea .rsi s ++ lea .rdx u ++ lea .rcx z)) st fun s1 =>
      ((s1.gpr .rdi = pa st w ∧ s1.gpr .rsi = pa st s ∧ s1.gpr .rdx = pa st u ∧ s1.gpr .rcx = pa st z) ∧
        s1.mem = st.mem) ∧ Keep argRegs st s1 := by
  have s1 : s.1 ≠ .rdi := fun e => hs (by rw [e]; decide)
  have u1 : u.1 ≠ .rdi := fun e => hu (by rw [e]; decide)
  have u2 : u.1 ≠ .rsi := fun e => hu (by rw [e]; decide)
  have z1 : z.1 ≠ .rdi := fun e => hz (by rw [e]; decide)
  have z2 : z.1 ≠ .rsi := fun e => hz (by rw [e]; decide)
  have z3 : z.1 ≠ .rdx := fun e => hz (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2.1, sx_ofNat ho.2.2.1, sx_ofNat ho.2.2.2, s1, u1, u2, z1, z2, z3,
    List.cons_append, List.nil_append]

/-- The vector at `p` reads the same on entry to a callee. -/
theorem ce_vecAt (st : State) {p : Addr} {k : Nat} (h : (below (st.gpr .rsp) 32).Disjoint (vR p k)) :
    vecAt st.callEntry.mem p k = vecAt st.mem p k := by
  simp only [vecAt]
  exact List.map_congr_left fun i hi => ce_polyAt st (h.sub_right (DecMul.sub_v p (List.mem_range.mp hi)))

theorem dmPre {k : Nat} {w s u z : Ptr} {st s1 : State} (H : DecMulH k w s u z st)
    (hv : s1.gpr .rdi = pa st w ∧ s1.gpr .rsi = pa st s ∧ s1.gpr .rdx = pa st u ∧ s1.gpr .rcx = pa st z)
    (hm : s1.mem = st.mem) (k1 : Keep argRegs st s1) :
    (decMulK k).pre (s1.callEntry.withRegions [vR (pa st s) k, vR (pa st u) k] [pR (pa st w), cR (pa st z)]) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  simp only [decMulK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  refine ⟨trivial, trivial, H.ws, H.wu, H.wz, H.sz, H.uz, ret_disj s1 (by rw [hsp]; exact H.kW),
    ret_disj s1 (by rw [hsp]; exact H.kS), ret_disj s1 (by rw [hsp]; exact H.kU),
    ret_disj s1 (by rw [hsp]; exact H.kZ), fun i hi => ?_, fun i hi => ?_⟩
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kS.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redS i hi
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kU.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redU i hi

section
variable {A : Arith} (hA : ArithOk A) {L : Kem} (hk : L.k = 3 ∨ L.k = 4)
include hA hk

theorem decMulAt_ok {w s u z : Ptr} (hs : NA s) (hu : NA u) (hz : NA z) {st : State} (H : DecMulH L.k w s u z st) :
    WP isa (L.decMulAt A w s u z) st fun s' => Post st s' [pR (pa st w), cR (pa st z)] ∧
      PolyIs s'.mem (pa st w) (nttInv (dot (vecAt st.mem (pa st s) L.k) ((vecAt st.mem (pa st u) L.k).map ntt))) := by
  have hC := hA.dm L.k hk
  refine WP.mono (glueCall_ok hC.ok hC.nosp (by rw [hC.depth]; decide) (dmGlue_ok w s u z H.off hs hu hz st)
    (fun s1 hv hm k => dmPre H hv hm k) H.c H.wc) fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  simp only [decMulK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hm₂,
    ce_vecAt s1 (by rw [hsp]; exact H.kS), ce_vecAt s1 (by rw [hsp]; exact H.kU), hm] at hq
  exact hq

theorem decMulAt_tr {w s u z : Ptr} (hs : NA s) (hu : NA u) (hz : NA z) :
    RelCT isa (fun x y => DecMulH L.k w s u z x ∧ DecMulH L.k w s u z y ∧ x.gpr w.1 = y.gpr w.1 ∧
      x.gpr s.1 = y.gpr s.1 ∧ x.gpr u.1 = y.gpr u.1 ∧ x.gpr z.1 = y.gpr z.1 ∧ x.gpr .rsp = y.gpr .rsp)
      (L.decMulAt A w s u z) fun _ _ => True :=
  glueCall_tr (hA.dm L.k hk).ok (hA.dm L.k hk).ct (V := fun x x1 => ((x1.gpr .rdi = pa x w ∧ x1.gpr .rsi = pa x s ∧
      x1.gpr .rdx = pa x u ∧ x1.gpr .rcx = pa x z) ∧ x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _))
      (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨dmGlue_ok w s u z hx.off hs hu hz x, dmGlue_ok w s u z hy.off hs hu hz y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3, e4, e5⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, dmPre hx hv1 hm1 k1, dmPre hy hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e5]⟩
      simp only [decMulK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1,
        hv2.2.2.2, pa, e1, e2, e3, e4, k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e5, and_self]

end

/-! ## In a layout -/

def dmChk (bs wbs : List (Reg × Nat)) (k : Nat) (w s u z : Ptr) : Bool :=
  wrOk bs wbs w 1024 && rdOk bs s (1024 * k) && rdOk bs u (1024 * k) && wrOk bs wbs z 4096 &&
    sepB bs w 1024 s (1024 * k) && sepB bs w 1024 u (1024 * k) && sepB bs w 1024 z 4096 &&
    sepB bs s (1024 * k) z 4096 && sepB bs u (1024 * k) z 4096

section
variable {rbs wbs : List (Reg × Nat)} {st : State} (L : Lay rbs wbs st)
include L

theorem DecMulH.of {k : Nat} {w s u z : Ptr} (hc : dmChk (rbs ++ wbs) wbs k w s u z = true)
    (redS : VecReduced st.mem (pa st s) k) (redU : VecReduced st.mem (pa st u) k) : DecMulH k w s u z st := by
  simp only [dmChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨how, hrw⟩, hww⟩, hos, hrs⟩, hou, hru⟩, ⟨hoz, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩, s4⟩, s5⟩ := hc
  exact ⟨⟨how, hos, hou, hoz⟩, redS, redU, L.disj s1, L.disj s2, L.disj s3, L.disj s4, L.disj s5, L.stkD hrw,
    L.stkD hrs, L.stkD hru, L.stkD hrz,
    covers_append (covers_cons (L.cR hrs) (covers_cons (L.cR hru) covers_nil))
      (covers_cons (L.cR hrw) (covers_cons (L.cR hrz) covers_nil)),
    covers_cons (L.cW hww) (covers_cons (L.cW hwz) covers_nil)⟩

end

theorem dmChk_in {bs wbs : List (Reg × Nat)} {k : Nat} {w s u z : Ptr} (hc : dmChk bs wbs k w s u z = true) :
    inB bs w 1024 = true ∧ inB bs s (1024 * k) = true ∧ inB bs u (1024 * k) = true ∧ inB bs z 4096 = true := by
  simp only [dmChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, rdOk_in h2, rdOk_in h3, wrOk_in h4⟩

section
variable {A : Arith} (hA : ArithOk A) {L : Kem} (hk : L.k = 3 ∨ L.k = 4) {rbs wbs : List (Reg × Nat)}
include hA hk

theorem decMulAt_okL {st : State} (La : Lay rbs wbs st) {w s u z : Ptr} (hs : NA s) (hu : NA u) (hz : NA z)
    (hc : dmChk (rbs ++ wbs) wbs L.k w s u z = true) (redS : VecReduced st.mem (pa st s) L.k)
    (redU : VecReduced st.mem (pa st u) L.k) :
    WP isa (L.decMulAt A w s u z) st fun s' => PPost st s' [(w, 1024), (z, 4096)] ∧
      PolyIs s'.mem (pa st w) (nttInv (dot (vecAt st.mem (pa st s) L.k) ((vecAt st.mem (pa st u) L.k).map ntt))) :=
  decMulAt_ok hA hk hs hu hz (DecMulH.of La hc redS redU)

theorem decMulAt_trL {w s u z : Ptr} (hs : NA s) (hu : NA u) (hz : NA z)
    (hc : dmChk (rbs ++ wbs) wbs L.k w s u z = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧
      (VecReduced x.mem (pa x s) L.k ∧ VecReduced x.mem (pa x u) L.k) ∧
      (VecReduced y.mem (pa y s) L.k ∧ VecReduced y.mem (pa y u) L.k)) (L.decMulAt A w s u z) fun _ _ => True :=
  RelCT.mono (decMulAt_tr hA hk hs hu hz) (fun _ _ ⟨e, ⟨r1, r2⟩, r3, r4⟩ => ⟨DecMulH.of e.1 hc r1 r2,
    DecMulH.of e.2.1 hc r3 r4, e.eq (dmChk_in hc).1, e.eq (dmChk_in hc).2.1, e.eq (dmChk_in hc).2.2.1,
    e.eq (dmChk_in hc).2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

end

/-- The `k` polynomials from polynomial `b` of the working space. -/
theorem pa_pS (st : State) (b i : Nat) : pa st (pS (b + i)) = pa st (pS b) + BitVec.ofNat 64 (1024 * i) := by
  simp only [pa, oP]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add, Nat.add_assoc]

theorem vecReduced_pS {m : Mem} {st : State} {b k : Nat} (h : ∀ i < k, Reduced m (pa st (pS (b + i)))) :
    VecReduced m (pa st (pS b)) k := fun i hi => by rw [← pa_pS]; exact h i hi

theorem vecAt_pS (m : Mem) (st : State) (b k : Nat) :
    vecAt m (pa st (pS b)) k = (List.range k).map fun i => polyAt m (pa st (pS (b + i))) := by
  simp only [vecAt, pa_pS]

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: the call of `vg_mlkem*_encrypt_mul`

As the call of `vg_mlkem*_decrypt_mul` (`FragDM.lean`): what a call of
`vg_mlkem*_encrypt_mul` writing the `k + 1` polynomials from `u` from the
`k²` from `a` and the `k` from `t` and from `y`, with the working space `z`,
needs of the state (`EncMulH`), of a layout (`emChk`, `EncMulH.of`), what it
computes (`encMulAt_ok`) and that two runs leak the same (`encMulAt_tr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- What a call of `vg_mlkem*_encrypt_mul` of rank `k` needs. -/
structure EncMulH (k : Nat) (u a t y z : Ptr) (st : State) : Prop where
  off : u.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ t.2 < 2 ^ 31 ∧ y.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  redA : VecReduced st.mem (pa st a) (k * k)
  redT : VecReduced st.mem (pa st t) k
  redY : VecReduced st.mem (pa st y) k
  ua : (vR (pa st u) (k + 1)).Disjoint (vR (pa st a) (k * k))
  ut : (vR (pa st u) (k + 1)).Disjoint (vR (pa st t) k)
  uy : (vR (pa st u) (k + 1)).Disjoint (vR (pa st y) k)
  uz : (vR (pa st u) (k + 1)).Disjoint (cR (pa st z))
  az : (vR (pa st a) (k * k)).Disjoint (cR (pa st z))
  tz : (vR (pa st t) k).Disjoint (cR (pa st z))
  yz : (vR (pa st y) k).Disjoint (cR (pa st z))
  kU : (below (st.gpr .rsp) 32).Disjoint (vR (pa st u) (k + 1))
  kA : (below (st.gpr .rsp) 32).Disjoint (vR (pa st a) (k * k))
  kT : (below (st.gpr .rsp) 32).Disjoint (vR (pa st t) k)
  kY : (below (st.gpr .rsp) 32).Disjoint (vR (pa st y) k)
  kZ : (below (st.gpr .rsp) 32).Disjoint (cR (pa st z))
  c : Covers ([vR (pa st a) (k * k), vR (pa st t) k, vR (pa st y) k] ++ [vR (pa st u) (k + 1), cR (pa st z)])
    (st.rd ++ st.wr)
  wc : Covers [vR (pa st u) (k + 1), cR (pa st z)] st.wr

theorem emGlue_ok (u a t y z : Ptr) (ho : u.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ t.2 < 2 ^ 31 ∧ y.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31)
    (ha : NA a) (ht : NA t) (hy : NA y) (hz : NA z) (st : State) :
    WP isa (.block (lea .rdi u ++ lea .rsi a ++ lea .rdx t ++ lea .rcx y ++ lea .r8 z)) st fun s1 =>
      ((s1.gpr .rdi = pa st u ∧ s1.gpr .rsi = pa st a ∧ s1.gpr .rdx = pa st t ∧ s1.gpr .rcx = pa st y ∧
        s1.gpr .r8 = pa st z) ∧ s1.mem = st.mem) ∧ Keep argRegs st s1 := by
  have a1 : a.1 ≠ .rdi := fun e => ha (by rw [e]; decide)
  have t1 : t.1 ≠ .rdi := fun e => ht (by rw [e]; decide)
  have t2 : t.1 ≠ .rsi := fun e => ht (by rw [e]; decide)
  have y1 : y.1 ≠ .rdi := fun e => hy (by rw [e]; decide)
  have y2 : y.1 ≠ .rsi := fun e => hy (by rw [e]; decide)
  have y3 : y.1 ≠ .rdx := fun e => hy (by rw [e]; decide)
  have z1 : z.1 ≠ .rdi := fun e => hz (by rw [e]; decide)
  have z2 : z.1 ≠ .rsi := fun e => hz (by rw [e]; decide)
  have z3 : z.1 ≠ .rdx := fun e => hz (by rw [e]; decide)
  have z4 : z.1 ≠ .rcx := fun e => hz (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2.1, sx_ofNat ho.2.2.1, sx_ofNat ho.2.2.2.1, sx_ofNat ho.2.2.2.2, a1, t1, t2,
    y1, y2, y3, z1, z2, z3, z4, List.cons_append, List.nil_append]

/-- The matrix at `p` reads the same on entry to a callee. -/
theorem ce_matAt (st : State) {p : Addr} {k : Nat} (h : (below (st.gpr .rsp) 32).Disjoint (vR p (k * k))) :
    matAt st.callEntry.mem p k = matAt st.mem p k := by
  simp only [matAt, vecAt]
  refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
  have hi := List.mem_range.mp hi
  have hj := List.mem_range.mp hj
  have e : k * i + j < k * k := by
    have := Nat.mul_le_mul_left k (show i + 1 ≤ k by omega_using [hi]); rw [Nat.mul_succ] at this; omega_using [hj, this]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add]
  exact ce_polyAt st (h.sub_right (DecMul.sub_v p e))

theorem emPre {k : Nat} {u a t y z : Ptr} {st s1 : State} (H : EncMulH k u a t y z st)
    (hv : s1.gpr .rdi = pa st u ∧ s1.gpr .rsi = pa st a ∧ s1.gpr .rdx = pa st t ∧ s1.gpr .rcx = pa st y ∧
      s1.gpr .r8 = pa st z)
    (hm : s1.mem = st.mem) (k1 : Keep argRegs st s1) :
    (encMulK k).pre (s1.callEntry.withRegions [vR (pa st a) (k * k), vR (pa st t) k, vR (pa st y) k]
      [vR (pa st u) (k + 1), cR (pa st z)]) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  simp only [encMulK, encMulKA, encMulKG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.r8 ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
  refine ⟨trivial, trivial, H.ua, H.ut, H.uy, H.uz, H.az, H.tz, H.yz, ret_disj s1 (by rw [hsp]; exact H.kU),
    ret_disj s1 (by rw [hsp]; exact H.kA), ret_disj s1 (by rw [hsp]; exact H.kT),
    ret_disj s1 (by rw [hsp]; exact H.kY), ret_disj s1 (by rw [hsp]; exact H.kZ), fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_⟩
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kA.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redA i hi
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kT.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redT i hi
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kY.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redY i hi

section
variable {A : Arith} (hA : ArithOk A) {L : Kem} (hk : L.k = 3 ∨ L.k = 4)
include hA hk

theorem encMulAt_ok {u a t y z : Ptr} (ha : NA a) (ht : NA t) (hy : NA y) (hz : NA z) {st : State}
    (H : EncMulH L.k u a t y z st) :
    WP isa (L.encMulAt A u a t y z) st fun s' => Post st s' [vR (pa st u) (L.k + 1), cR (pa st z)] ∧
      VecIs s'.mem (pa st u) (L.k + 1)
        (((mulMatTVec L.k (matAt st.mem (pa st a) L.k) ((vecAt st.mem (pa st y) L.k).map ntt)).map nttInv) ++
          [nttInv (dot (vecAt st.mem (pa st t) L.k) ((vecAt st.mem (pa st y) L.k).map ntt))]) := by
  have hC := hA.em L.k hk
  refine WP.mono (glueCall_ok hC.ok hC.nosp (by rw [hC.depth]; decide) (emGlue_ok u a t y z H.off ha ht hy hz st)
    (fun s1 hv hm k => emPre H hv hm k) H.c H.wc) fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  simp only [encMulK, encMulKA, encMulKG, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hm₂,
    ce_matAt s1 (by rw [hsp]; exact H.kA), ce_vecAt s1 (by rw [hsp]; exact H.kT),
    ce_vecAt s1 (by rw [hsp]; exact H.kY), hm] at hq
  exact hq

theorem encMulAt_tr {u a t y z : Ptr} (ha : NA a) (ht : NA t) (hy : NA y) (hz : NA z) :
    RelCT isa (fun x y' => EncMulH L.k u a t y z x ∧ EncMulH L.k u a t y z y' ∧ x.gpr u.1 = y'.gpr u.1 ∧
      x.gpr a.1 = y'.gpr a.1 ∧ x.gpr t.1 = y'.gpr t.1 ∧ x.gpr y.1 = y'.gpr y.1 ∧ x.gpr z.1 = y'.gpr z.1 ∧
      x.gpr .rsp = y'.gpr .rsp)
      (L.encMulAt A u a t y z) fun _ _ => True :=
  glueCall_tr (hA.em L.k hk).ok (hA.em L.k hk).ct (V := fun x x1 => ((x1.gpr .rdi = pa x u ∧
      x1.gpr .rsi = pa x a ∧ x1.gpr .rdx = pa x t ∧ x1.gpr .rcx = pa x y ∧ x1.gpr .r8 = pa x z) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _))
      (lea_nomem _ _)) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y' ⟨hx, hy', _⟩ => ⟨emGlue_ok u a t y z hx.off ha ht hy hz x, emGlue_ok u a t y z hy'.off ha ht hy hz y'⟩)
    fun x y' x1 y1 ⟨hx, hy', e1, e2, e3, e4, e5, e6⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, emPre hx hv1 hm1 k1, emPre hy' hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy'.c, by rw [k2.2.2]; exact hy'.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e6]⟩
      simp only [encMulK, encMulKA, encMulKG, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2.1, hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2, pa, e1, e2, e3, e4, e5,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e6, and_self]

end

/-! ## In a layout -/

def emChk (bs wbs : List (Reg × Nat)) (k : Nat) (u a t y z : Ptr) : Bool :=
  wrOk bs wbs u (1024 * (k + 1)) && rdOk bs a (1024 * (k * k)) && rdOk bs t (1024 * k) && rdOk bs y (1024 * k) &&
    wrOk bs wbs z 4096 && sepB bs u (1024 * (k + 1)) a (1024 * (k * k)) && sepB bs u (1024 * (k + 1)) t (1024 * k) &&
    sepB bs u (1024 * (k + 1)) y (1024 * k) && sepB bs u (1024 * (k + 1)) z 4096 && sepB bs a (1024 * (k * k)) z 4096 &&
    sepB bs t (1024 * k) z 4096 && sepB bs y (1024 * k) z 4096

section
variable {rbs wbs : List (Reg × Nat)} {st : State} (L : Lay rbs wbs st)
include L

theorem EncMulH.of {k : Nat} {u a t y z : Ptr} (hc : emChk (rbs ++ wbs) wbs k u a t y z = true)
    (redA : VecReduced st.mem (pa st a) (k * k)) (redT : VecReduced st.mem (pa st t) k)
    (redY : VecReduced st.mem (pa st y) k) : EncMulH k u a t y z st := by
  simp only [emChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hou, hru⟩, hwu⟩, hoa, hra⟩, hot, hrt⟩, hoy, hry⟩, ⟨hoz, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩, s4⟩, s5⟩,
    s6⟩, s7⟩ := hc
  exact ⟨⟨hou, hoa, hot, hoy, hoz⟩, redA, redT, redY, L.disj s1, L.disj s2, L.disj s3, L.disj s4, L.disj s5,
    L.disj s6, L.disj s7, L.stkD hru, L.stkD hra, L.stkD hrt, L.stkD hry, L.stkD hrz,
    covers_append (covers_cons (L.cR hra) (covers_cons (L.cR hrt) (covers_cons (L.cR hry) covers_nil)))
      (covers_cons (L.cR hru) (covers_cons (L.cR hrz) covers_nil)),
    covers_cons (L.cW hwu) (covers_cons (L.cW hwz) covers_nil)⟩

end

theorem emChk_in {bs wbs : List (Reg × Nat)} {k : Nat} {u a t y z : Ptr} (hc : emChk bs wbs k u a t y z = true) :
    inB bs u (1024 * (k + 1)) = true ∧ inB bs a (1024 * (k * k)) = true ∧ inB bs t (1024 * k) = true ∧
      inB bs y (1024 * k) = true ∧ inB bs z 4096 = true := by
  simp only [emChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, rdOk_in h2, rdOk_in h3, rdOk_in h4, wrOk_in h5⟩

section
variable {A : Arith} (hA : ArithOk A) {L : Kem} (hk : L.k = 3 ∨ L.k = 4) {rbs wbs : List (Reg × Nat)}
include hA hk

theorem encMulAt_okL {st : State} (La : Lay rbs wbs st) {u a t y z : Ptr} (ha : NA a) (ht : NA t) (hy : NA y)
    (hz : NA z) (hc : emChk (rbs ++ wbs) wbs L.k u a t y z = true) (redA : VecReduced st.mem (pa st a) (L.k * L.k))
    (redT : VecReduced st.mem (pa st t) L.k) (redY : VecReduced st.mem (pa st y) L.k) :
    WP isa (L.encMulAt A u a t y z) st fun s' => PPost st s' [(u, 1024 * (L.k + 1)), (z, 4096)] ∧
      VecIs s'.mem (pa st u) (L.k + 1)
        (((mulMatTVec L.k (matAt st.mem (pa st a) L.k) ((vecAt st.mem (pa st y) L.k).map ntt)).map nttInv) ++
          [nttInv (dot (vecAt st.mem (pa st t) L.k) ((vecAt st.mem (pa st y) L.k).map ntt))]) :=
  encMulAt_ok hA hk ha ht hy hz (EncMulH.of La hc redA redT redY)

theorem encMulAt_trL {u a t y z : Ptr} (ha : NA a) (ht : NA t) (hy : NA y) (hz : NA z)
    (hc : emChk (rbs ++ wbs) wbs L.k u a t y z = true) :
    RelCT isa (fun x y' => LRel rbs wbs x y' ∧
      (VecReduced x.mem (pa x a) (L.k * L.k) ∧ VecReduced x.mem (pa x t) L.k ∧ VecReduced x.mem (pa x y) L.k) ∧
      (VecReduced y'.mem (pa y' a) (L.k * L.k) ∧ VecReduced y'.mem (pa y' t) L.k ∧ VecReduced y'.mem (pa y' y) L.k))
      (L.encMulAt A u a t y z) fun _ _ => True :=
  RelCT.mono (encMulAt_tr hA hk ha ht hy hz) (fun _ _ ⟨e, ⟨r1, r2, r3⟩, r4, r5, r6⟩ =>
    ⟨EncMulH.of e.1 hc r1 r2 r3, EncMulH.of e.2.1 hc r4 r5 r6, e.eq (emChk_in hc).1, e.eq (emChk_in hc).2.1,
      e.eq (emChk_in hc).2.2.1, e.eq (emChk_in hc).2.2.2.1, e.eq (emChk_in hc).2.2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

end

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: the call of `vg_mlkem*_keygen_mul`

As the call of `vg_mlkem*_encrypt_mul` (`FragEM.lean`): what a call of
`vg_mlkem*_keygen_mul` writing the `k` polynomials from `t` and from `s`,
from those from `s`, the `k²` from `a` and the `k` from `e`, with the
working space `z`, needs of the state (`KgMulH`), of a layout (`kmChk`,
`KgMulH.of`), what it computes (`kgMulAt_ok`) and that two runs leak the
same (`kgMulAt_tr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-- What a call of `vg_mlkem*_keygen_mul` of rank `k` needs. -/
structure KgMulH (k : Nat) (t s a e z : Ptr) (st : State) : Prop where
  off : t.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ e.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31
  redS : VecReduced st.mem (pa st s) k
  redA : VecReduced st.mem (pa st a) (k * k)
  redE : VecReduced st.mem (pa st e) k
  ts : (vR (pa st t) k).Disjoint (vR (pa st s) k)
  ta : (vR (pa st t) k).Disjoint (vR (pa st a) (k * k))
  te : (vR (pa st t) k).Disjoint (vR (pa st e) k)
  tz : (vR (pa st t) k).Disjoint (cR (pa st z))
  sa : (vR (pa st s) k).Disjoint (vR (pa st a) (k * k))
  se : (vR (pa st s) k).Disjoint (vR (pa st e) k)
  sz : (vR (pa st s) k).Disjoint (cR (pa st z))
  az : (vR (pa st a) (k * k)).Disjoint (cR (pa st z))
  ez : (vR (pa st e) k).Disjoint (cR (pa st z))
  kT : (below (st.gpr .rsp) 32).Disjoint (vR (pa st t) k)
  kS : (below (st.gpr .rsp) 32).Disjoint (vR (pa st s) k)
  kA : (below (st.gpr .rsp) 32).Disjoint (vR (pa st a) (k * k))
  kE : (below (st.gpr .rsp) 32).Disjoint (vR (pa st e) k)
  kZ : (below (st.gpr .rsp) 32).Disjoint (cR (pa st z))
  c : Covers ([vR (pa st a) (k * k), vR (pa st e) k] ++ [vR (pa st t) k, vR (pa st s) k, cR (pa st z)])
    (st.rd ++ st.wr)
  wc : Covers [vR (pa st t) k, vR (pa st s) k, cR (pa st z)] st.wr

theorem kmGlue_ok (t s a e z : Ptr) (ho : t.2 < 2 ^ 31 ∧ s.2 < 2 ^ 31 ∧ a.2 < 2 ^ 31 ∧ e.2 < 2 ^ 31 ∧ z.2 < 2 ^ 31)
    (hs : NA s) (ha : NA a) (he : NA e) (hz : NA z) (st : State) :
    WP isa (.block (lea .rdi t ++ lea .rsi s ++ lea .rdx a ++ lea .rcx e ++ lea .r8 z)) st fun s1 =>
      ((s1.gpr .rdi = pa st t ∧ s1.gpr .rsi = pa st s ∧ s1.gpr .rdx = pa st a ∧ s1.gpr .rcx = pa st e ∧
        s1.gpr .r8 = pa st z) ∧ s1.mem = st.mem) ∧ Keep argRegs st s1 := by
  have s1 : s.1 ≠ .rdi := fun h => hs (by rw [h]; decide)
  have a1 : a.1 ≠ .rdi := fun h => ha (by rw [h]; decide)
  have a2 : a.1 ≠ .rsi := fun h => ha (by rw [h]; decide)
  have e1 : e.1 ≠ .rdi := fun h => he (by rw [h]; decide)
  have e2 : e.1 ≠ .rsi := fun h => he (by rw [h]; decide)
  have e3 : e.1 ≠ .rdx := fun h => he (by rw [h]; decide)
  have z1 : z.1 ≠ .rdi := fun h => hz (by rw [h]; decide)
  have z2 : z.1 ≠ .rsi := fun h => hz (by rw [h]; decide)
  have z3 : z.1 ≠ .rdx := fun h => hz (by rw [h]; decide)
  have z4 : z.1 ≠ .rcx := fun h => hz (by rw [h]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2.1, sx_ofNat ho.2.2.1, sx_ofNat ho.2.2.2.1, sx_ofNat ho.2.2.2.2, s1, a1, a2,
    e1, e2, e3, z1, z2, z3, z4, List.cons_append, List.nil_append]

theorem kmPre {k : Nat} {t s a e z : Ptr} {st s1 : State} (H : KgMulH k t s a e z st)
    (hv : s1.gpr .rdi = pa st t ∧ s1.gpr .rsi = pa st s ∧ s1.gpr .rdx = pa st a ∧ s1.gpr .rcx = pa st e ∧
      s1.gpr .r8 = pa st z)
    (hm : s1.mem = st.mem) (k1 : Keep argRegs st s1) :
    (kgMulK k).pre (s1.callEntry.withRegions [vR (pa st a) (k * k), vR (pa st e) k]
      [vR (pa st t) k, vR (pa st s) k, cR (pa st z)]) := by
  have hsp : s1.gpr .rsp = st.gpr .rsp := k1.gpr (by decide)
  simp only [kgMulK, kgMulKA, kgMulKG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.r8 ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
  refine ⟨trivial, trivial, H.ts, H.ta, H.te, H.tz, H.sa, H.se, H.sz, H.az, H.ez,
    ret_disj s1 (by rw [hsp]; exact H.kT), ret_disj s1 (by rw [hsp]; exact H.kS),
    ret_disj s1 (by rw [hsp]; exact H.kA), ret_disj s1 (by rw [hsp]; exact H.kE),
    ret_disj s1 (by rw [hsp]; exact H.kZ), fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kS.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redS i hi
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kA.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redA i hi
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kE.sub_right (DecMul.sub_v _ hi)), hm]; exact H.redE i hi

section
variable {A : Arith} (hA : ArithOk A) {L : Kem} (hk : L.k = 3 ∨ L.k = 4)
include hA hk

theorem kgMulAt_ok {t s a e z : Ptr} (hs : NA s) (ha : NA a) (he : NA e) (hz : NA z) {st : State}
    (H : KgMulH L.k t s a e z st) :
    WP isa (L.kgMulAt A t s a e z) st fun s' => Post st s' [vR (pa st t) L.k, vR (pa st s) L.k, cR (pa st z)] ∧
      VecIs s'.mem (pa st s) L.k ((vecAt st.mem (pa st s) L.k).map ntt) ∧
      VecIs s'.mem (pa st t) L.k (addVec (mulMatVec (matAt st.mem (pa st a) L.k)
        ((vecAt st.mem (pa st s) L.k).map ntt)) ((vecAt st.mem (pa st e) L.k).map ntt)) := by
  have hC := hA.km L.k hk
  refine WP.mono (glueCall_ok hC.ok hC.nosp (by rw [hC.depth]; decide) (kmGlue_ok t s a e z H.off hs ha he hz st)
    (fun s1 hv hm k => kmPre H hv hm k) H.c H.wc) fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = st.gpr .rsp := k.gpr (by decide)
  simp only [kgMulK, kgMulKA, kgMulKG, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hm₂,
    ce_matAt s1 (by rw [hsp]; exact H.kA), ce_vecAt s1 (by rw [hsp]; exact H.kS),
    ce_vecAt s1 (by rw [hsp]; exact H.kE), hm] at hq
  exact hq

theorem kgMulAt_tr {t s a e z : Ptr} (hs : NA s) (ha : NA a) (he : NA e) (hz : NA z) :
    RelCT isa (fun x y' => KgMulH L.k t s a e z x ∧ KgMulH L.k t s a e z y' ∧ x.gpr t.1 = y'.gpr t.1 ∧
      x.gpr s.1 = y'.gpr s.1 ∧ x.gpr a.1 = y'.gpr a.1 ∧ x.gpr e.1 = y'.gpr e.1 ∧ x.gpr z.1 = y'.gpr z.1 ∧
      x.gpr .rsp = y'.gpr .rsp)
      (L.kgMulAt A t s a e z) fun _ _ => True :=
  glueCall_tr (hA.km L.k hk).ok (hA.km L.k hk).ct (V := fun x x1 => ((x1.gpr .rdi = pa x t ∧
      x1.gpr .rsi = pa x s ∧ x1.gpr .rdx = pa x a ∧ x1.gpr .rcx = pa x e ∧ x1.gpr .r8 = pa x z) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (nomem_append (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _))
      (lea_nomem _ _)) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y' ⟨hx, hy', _⟩ => ⟨kmGlue_ok t s a e z hx.off hs ha he hz x, kmGlue_ok t s a e z hy'.off hs ha he hz y'⟩)
    fun x y' x1 y1 ⟨hx, hy', e1, e2, e3, e4, e5, e6⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, kmPre hx hv1 hm1 k1, kmPre hy' hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.wc, by rw [k2.2.1, k2.2.2]; exact hy'.c, by rw [k2.2.2]; exact hy'.wc,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e6]⟩
      simp only [kgMulK, kgMulKA, kgMulKG, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2.1, hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2, pa, e1, e2, e3, e4, e5,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e6, and_self]

end

/-! ## In a layout -/

def kmChk (bs wbs : List (Reg × Nat)) (k : Nat) (t s a e z : Ptr) : Bool :=
  wrOk bs wbs t (1024 * k) && wrOk bs wbs s (1024 * k) && rdOk bs a (1024 * (k * k)) && rdOk bs e (1024 * k) &&
    wrOk bs wbs z 4096 && sepB bs t (1024 * k) s (1024 * k) && sepB bs t (1024 * k) a (1024 * (k * k)) &&
    sepB bs t (1024 * k) e (1024 * k) && sepB bs t (1024 * k) z 4096 && sepB bs s (1024 * k) a (1024 * (k * k)) &&
    sepB bs s (1024 * k) e (1024 * k) && sepB bs s (1024 * k) z 4096 && sepB bs a (1024 * (k * k)) z 4096 &&
    sepB bs e (1024 * k) z 4096

section
variable {rbs wbs : List (Reg × Nat)} {st : State} (L : Lay rbs wbs st)
include L

theorem KgMulH.of {k : Nat} {t s a e z : Ptr} (hc : kmChk (rbs ++ wbs) wbs k t s a e z = true)
    (redS : VecReduced st.mem (pa st s) k) (redA : VecReduced st.mem (pa st a) (k * k))
    (redE : VecReduced st.mem (pa st e) k) : KgMulH k t s a e z st := by
  simp only [kmChk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hot, hrt⟩, hwt⟩, ⟨hos, hrs⟩, hws⟩, hoa, hra⟩, hoe, hre⟩, ⟨hoz, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩,
    s4⟩, s5⟩, s6⟩, s7⟩, s8⟩, s9⟩ := hc
  exact ⟨⟨hot, hos, hoa, hoe, hoz⟩, redS, redA, redE, L.disj s1, L.disj s2, L.disj s3, L.disj s4, L.disj s5,
    L.disj s6, L.disj s7, L.disj s8, L.disj s9, L.stkD hrt, L.stkD hrs, L.stkD hra, L.stkD hre, L.stkD hrz,
    covers_append (covers_cons (L.cR hra) (covers_cons (L.cR hre) covers_nil))
      (covers_cons (L.cR hrt) (covers_cons (L.cR hrs) (covers_cons (L.cR hrz) covers_nil))),
    covers_cons (L.cW hwt) (covers_cons (L.cW hws) (covers_cons (L.cW hwz) covers_nil))⟩

end

theorem kmChk_in {bs wbs : List (Reg × Nat)} {k : Nat} {t s a e z : Ptr} (hc : kmChk bs wbs k t s a e z = true) :
    inB bs t (1024 * k) = true ∧ inB bs s (1024 * k) = true ∧ inB bs a (1024 * (k * k)) = true ∧
      inB bs e (1024 * k) = true ∧ inB bs z 4096 = true := by
  simp only [kmChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨wrOk_in h1, wrOk_in h2, rdOk_in h3, rdOk_in h4, wrOk_in h5⟩

section
variable {A : Arith} (hA : ArithOk A) {L : Kem} (hk : L.k = 3 ∨ L.k = 4) {rbs wbs : List (Reg × Nat)}
include hA hk

theorem kgMulAt_okL {st : State} (La : Lay rbs wbs st) {t s a e z : Ptr} (hs : NA s) (ha : NA a) (he : NA e)
    (hz : NA z) (hc : kmChk (rbs ++ wbs) wbs L.k t s a e z = true) (redS : VecReduced st.mem (pa st s) L.k)
    (redA : VecReduced st.mem (pa st a) (L.k * L.k)) (redE : VecReduced st.mem (pa st e) L.k) :
    WP isa (L.kgMulAt A t s a e z) st fun s' => PPost st s' [(t, 1024 * L.k), (s, 1024 * L.k), (z, 4096)] ∧
      VecIs s'.mem (pa st s) L.k ((vecAt st.mem (pa st s) L.k).map ntt) ∧
      VecIs s'.mem (pa st t) L.k (addVec (mulMatVec (matAt st.mem (pa st a) L.k)
        ((vecAt st.mem (pa st s) L.k).map ntt)) ((vecAt st.mem (pa st e) L.k).map ntt)) :=
  kgMulAt_ok hA hk hs ha he hz (KgMulH.of La hc redS redA redE)

theorem kgMulAt_trL {t s a e z : Ptr} (hs : NA s) (ha : NA a) (he : NA e) (hz : NA z)
    (hc : kmChk (rbs ++ wbs) wbs L.k t s a e z = true) :
    RelCT isa (fun x y' => LRel rbs wbs x y' ∧
      (VecReduced x.mem (pa x s) L.k ∧ VecReduced x.mem (pa x a) (L.k * L.k) ∧ VecReduced x.mem (pa x e) L.k) ∧
      (VecReduced y'.mem (pa y' s) L.k ∧ VecReduced y'.mem (pa y' a) (L.k * L.k) ∧ VecReduced y'.mem (pa y' e) L.k))
      (L.kgMulAt A t s a e z) fun _ _ => True :=
  RelCT.mono (kgMulAt_tr hA hk hs ha he hz) (fun _ _ ⟨e, ⟨r1, r2, r3⟩, r4, r5, r6⟩ =>
    ⟨KgMulH.of e.1 hc r1 r2 r3, KgMulH.of e.2.1 hc r4 r5 r6, e.eq (kmChk_in hc).1, e.eq (kmChk_in hc).2.1,
      e.eq (kmChk_in hc).2.2.1, e.eq (kmChk_in hc).2.2.2.1, e.eq (kmChk_in hc).2.2.2.2, e.2.2.2⟩) fun _ _ _ => trivial

end

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: key generation, its contract, layout, checks and entry

For a parameter set `L` (`Impl/MlKem/X86_64/Kem.lean`): the contract the
proof is written against (`keyGenK L`, which the shared contract of
ML-KEM-768 or ML-KEM-1024 implies), the layout of the function's buffers
(`seed` in `rbp`; `scratch`, `ek`, `dk` in `rbx`, `r12`, `r13`), what holds
throughout (`KC`: `Top`, and `d ‖ z` at `seed`), the prologue, and the
checks of the layout every piece needs (`KgWf L`), which each parameter set
evaluates.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `kemKeyGen L (seed = rdi, ek = rsi, dk = rdx, scratch = rcx) -> eax`, with 32 bytes of stack. -/
def keyGenK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 64⟩] ∧ s.wr = [⟨s.gpr .rsi, L.ekLen⟩, ⟨s.gpr .rdx, L.dkLen⟩, ⟨s.gpr .rcx, L.scr⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rsi, L.ekLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rdx, L.dkLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 64⟩ ⟨s.gpr .rcx, L.scr⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, L.ekLen⟩ ⟨s.gpr .rdx, L.dkLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, L.ekLen⟩ ⟨s.gpr .rcx, L.scr⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, L.dkLen⟩ ⟨s.gpr .rcx, L.scr⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 64⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, L.ekLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, L.dkLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, L.scr⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, 64⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, L.ekLen⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, L.dkLen⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, L.scr⟩ ∧
    (s.gpr .rdi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + L.ekLen ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + L.dkLen ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + L.scr ≤ 2 ^ 64
  post s s' :=
    Outcome (fun iters => keyGenInternal L.p iters (bytesAt s.mem (s.gpr .rdi) 32)
      (bytesAt s.mem (s.gpr .rdi + 32) 32)) ((s'.gpr .rax).setWidth 32)
      (bytesAt s'.mem (s.gpr .rsi) L.ekLen, bytesAt s'.mem (s.gpr .rdx) L.dkLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    keyGenRho L.p (bytesAt s₁.mem (s₁.gpr .rdi) 32) = keyGenRho L.p (bytesAt s₂.mem (s₂.gpr .rdi) 32)

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

variable (L : Kem)

/-- The pointers the function keeps. -/
abbrev kgM : List (Reg × Reg) := [(.rbx, .rcx), (.rbp, .rdi), (.r12, .rsi), (.r13, .rdx)]
/-- `seed`. -/
abbrev kgR : List (Reg × Nat) := [(.rbp, 64)]
/-- `scratch`, `ek` and `dk`. -/
abbrev kgW : List (Reg × Nat) := [(.rbx, L.scr), (.r12, L.ekLen), (.r13, L.dkLen)]
abbrev kgB : List (Reg × Nat) := kgR ++ kgW L

theorem kgB_bases : ∀ b ∈ kgB L, b.1 ∈ bases := by
  intro b hb; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp [bases]

theorem kgM_bases : ∀ p ∈ kgM, p.1 ∈ bases := by decide

/-- A piece that writes `ws` keeps `KC`. -/
def kcChk (ws : List (Ptr × Nat)) : Bool :=
  topChk (kgB L) ws && keepB (kgB L) ws (.rbp, 0) 32 && keepB (kgB L) ws (.rbp, 32) 32

/-! ## The checks of the pieces -/

/-- What entry `e` of `Â` writes. -/
abbrev ijW (e : Nat) : List (Ptr × Nat) :=
  [(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)] ++ [(pS (L.pA + e), 1024), (sc oSS, 2048)]

/-- Entry `e` of `Â`, on its own. -/
def kbChk (e : Nat) : Bool :=
  ijChk (kgB L) (kgW L) (pS (L.pA + e)) && kcChk L (ijW L e) && keepB (kgB L) (ijW L e) (sc oG) 32 &&
    keepB (kgB L) (ijW L e) sigP 32 && keepB (kgB L) (ijW L e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB (kgB L) (ijW L e) (pS (L.pA + e')) 1024

/-- What entries `e, …, e + 3` of `Â` write. -/
abbrev qW (e : Nat) : List (Ptr × Nat) := quadW (oP (L.pA + e)) (oP L.pW)

/-- Entries `e, …, e + 3` of `Â`, at once. -/
def kqChk (e : Nat) : Bool :=
  quadChk (kgB L) (kgW L) (oP (L.pA + e)) (oP L.pW) && kcChk L (qW L e) && keepB (kgB L) (qW L e) (sc oG) 32 &&
    keepB (kgB L) (qW L e) sigP 32 && keepB (kgB L) (qW L e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB (kgB L) (qW L e) (pS (L.pA + e')) 1024

/-- `PRF₂(σ, N)`, in the outputs of `prfs`. -/
abbrev prfO (N : Nat) : Ptr := sc (L.oPR + 128 * N)

/-- A piece that writes `ws` keeps `KRest n r e`. -/
def restChk (n r e : Nat) (ws : List (Ptr × Nat)) : Bool :=
  kcChk L ws && keepB (kgB L) ws (sc oG) 32 && keepB (kgB L) ws sigP 32 &&
    (List.range (L.k * L.k)).all (fun e => keepB (kgB L) ws (pS (L.pA + e)) 1024) &&
    (List.range (2 * L.k)).all (fun N => keepB (kgB L) ws (prfO L N) 128) &&
    (List.range n).all (fun k => keepB (kgB L) ws (pS k) 1024) &&
    (List.range r).all (fun i => keepB (kgB L) ws (.r12, 384 * i) 384) &&
    (List.range e).all (fun j => keepB (kgB L) ws (.r13, 384 * j) 384)

def prfsKChk : Bool :=
  prfsChk (kgB L) (kgW L) (2 * L.k) L.oPR L.lPW && kcChk L (prfsW (2 * L.k) L.oPR L.lPW) &&
    keepB (kgB L) (prfsW (2 * L.k) L.oPR L.lPW) (sc oG) 32 && keepB (kgB L) (prfsW (2 * L.k) L.oPR L.lPW) sigP 32 &&
    (List.range (L.k * L.k)).all (fun e => keepB (kgB L) (prfsW (2 * L.k) L.oPR L.lPW) (pS (L.pA + e)) 1024)

/-- What `se N` writes. -/
abbrev seW (N : Nat) : List (Ptr × Nat) := [(pS N, 1024)]

def seChk (N : Nat) : Bool :=
  twoChk (kgB L) (kgW L) (prfO L N) 128 (pS N) 1024 && restChk L N 0 0 (seW N)

/-- What `vg_mlkem*_keygen_mul` writes. -/
abbrev kmW : List (Ptr × Nat) := [(pS L.pU, 1024 * L.k), (pS 0, 1024 * L.k), (pS L.pZ, 4096)]

/-- After `vg_mlkem*_keygen_mul`: what a piece writing `ws` keeps, with `r`
rows of `ek` and `e` of `dk` written. -/
def restTChk (r e : Nat) (ws : List (Ptr × Nat)) : Bool :=
  kcChk L ws && keepB (kgB L) ws (sc oG) 32 && (List.range L.k).all (fun j => keepB (kgB L) ws (pS j) 1024) &&
    (List.range L.k).all (fun i => keepB (kgB L) ws (pS (L.pU + i)) 1024) &&
    (List.range r).all (fun i => keepB (kgB L) ws (.r12, 384 * i) 384) &&
    (List.range e).all (fun j => keepB (kgB L) ws (.r13, 384 * j) 384)

def encTChk (i : Nat) : Bool :=
  twoChk (kgB L) (kgW L) (pS (L.pU + i)) 1024 (.r12, 384 * i) 384 && restTChk L i 0 [((.r12, 384 * i), 384)]

def encSChk (j : Nat) : Bool :=
  twoChk (kgB L) (kgW L) (pS j) 1024 (.r13, 384 * j) 384 && restTChk L L.k j [((.r13, 384 * j), 384)]

/-- The writes of `fin`. -/
abbrev finW₁ : List (Ptr × Nat) := [((.r12, 384 * L.k), 32)]
abbrev finW₂ : List (Ptr × Nat) := [((.r13, 384 * L.k), L.ekLen)]
abbrev finW₃ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), ((.r13, 384 * L.k + L.ekLen), 32)]
abbrev finW₄ : List (Ptr × Nat) := [((.r13, 384 * L.k + L.ekLen + 32), 32)]

end KeyGen

/-- What all the top-level functions need of the parameter set: its rank,
`η₁ = η₂ = 2`, and the constant time of the indices of the seeds of `Â`. -/
structure KemWf (L : Kem) : Prop where
  k : 0 < L.k ∧ L.k ≤ 4
  k34 : L.k = 3 ∨ L.k = 4
  eta : L.p.η₁ = 2 ∧ L.p.η₂ = 2
  ijT : ∀ e < L.k * L.k, (taint.check (X86_64.Taint.ofRegs [.rbx])
    (.block (setB (sc (oSB + 32)) (e % L.k) ++ setB (sc (oSB + 33)) (e / L.k))) (.block [])).isSome = true

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

variable (L : Kem)

/-- What the pieces of key generation that do not depend on how it stores
its polynomials need of the layout (`G(d ‖ k)`, the keys' last pieces and
the end), evaluated for each parameter set. -/
structure KgWfB : Prop extends KemWf L where
  scr : 888 ≤ L.scr ∧ L.scr < 2 ^ 32
  small : ∀ b ∈ kgB L, b.2 < 2 ^ 32
  -- `G(d ‖ k)`
  nb : inB (kgW L) (sc oNB) 1 = true
  nbK : kcChk L [(sc oNB, 1)] = true
  gH : hashChk (kgB L) (kgW L) [((.rbp, 0), 32), (sc oNB, 1)] 72 (sc oG) 64 = true
  gK : kcChk L [(sc 0, 200), (sc 200, 640), (sc oG, 64)] = true
  gC : copyChk (kgB L) (kgW L) (sc oSB) (sc oG) 32 = true
  gCK : kcChk L [(sc oSB, 32)] = true
  gG : keepB (kgB L) [(sc oSB, 32)] (sc oG) 32 = true
  gS : keepB (kgB L) [(sc oSB, 32)] sigP 32 = true
  flag : kcChk L [] = true
  flagG : keepB (kgB L) [] (sc oG) 32 = true
  flagS : keepB (kgB L) [] sigP 32 = true
  flagB : keepB (kgB L) [] (sc oSB) 32 = true
  f₁ : copyChk (kgB L) (kgW L) (.r12, 384 * L.k) (sc oG) 32 = true
  f₁K : kcChk L (finW₁ L) = true
  f₁E : keepB (kgB L) (finW₁ L) (.r12, 0) (384 * L.k) = true
  f₂ : copyChk (kgB L) (kgW L) (.r13, 384 * L.k) (.r12, 0) L.ekLen = true
  f₂K : kcChk L (finW₂ L) = true
  f₂E : keepB (kgB L) (finW₂ L) (.r12, 0) L.ekLen = true
  f₃ : hashChk (kgB L) (kgW L) [((.r12, 0), L.ekLen)] 136 (.r13, 384 * L.k + L.ekLen) 32 = true
  f₃K : kcChk L (finW₃ L) = true
  f₃E : keepB (kgB L) (finW₃ L) (.r12, 0) L.ekLen = true
  f₄ : copyChk (kgB L) (kgW L) (.r13, 384 * L.k + L.ekLen + 32) (.rbp, 32) 32 = true
  f₄K : kcChk L (finW₄ L) = true
  f₄E : keepB (kgB L) (finW₄ L) (.r12, 0) L.ekLen = true
  dkS : keepB (kgB L) (finW₁ L ++ finW₂ L ++ finW₃ L ++ finW₄ L) (.r13, 0) (384 * L.k) = true
  dkE : keepB (kgB L) (finW₃ L ++ finW₄ L) (.r13, 384 * L.k) L.ekLen = true
  dkH : keepB (kgB L) (finW₄ L) (.r13, 384 * L.k + L.ekLen) 32 = true
  -- the end
  sv : ∀ k < 6, inB (kgB L) (sc (oSV + 8 * k)) 8 = true
  -- constant time
  inBs : inB (kgB L) (sc 0) 1 = true ∧ inB (kgB L) (.r12, 0) 1 = true ∧ inB (kgB L) (.r13, 0) 1 = true
  nbT : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc oNB) L.k)) (.block [])).isSome = true
  finT₁ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) (copy (.r12, 384 * L.k) (sc oG) 32)
    h).isSome = true
  finT₂ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) (copy (.r13, 384 * L.k) (.r12, 0) L.ekLen)
    h).isSome = true
  finT₄ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13])
    (copy (.r13, 384 * L.k + L.ekLen + 32) (.rbp, 32) 32) h).isSome = true

/-- What every piece of key generation with polynomials of `u32`s needs of
the layout, evaluated for each parameter set. -/
structure KgWf : Prop extends KgWfB L where
  -- the matrix
  kq : ∀ q < L.k * L.k / 4, kqChk L (4 * q) = true
  kb : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → kbChk L e = true
  flagA : ∀ e < L.k * L.k, keepB (kgB L) [] (pS (L.pA + e)) 1024 = true
  -- the keys
  prfs : prfsKChk L = true
  se : ∀ N < 2 * L.k, seChk L N = true
  km : kmChk (kgB L) (kgW L) L.k (pS L.pU) (pS 0) (pS L.pA) (pS L.k) (pS L.pZ) = true
  kmK : kcChk L (kmW L) = true
  kmG : keepB (kgB L) (kmW L) (sc oG) 32 = true
  encT : ∀ i < L.k, encTChk L i = true
  encS : ∀ j < L.k, encSChk L j = true

instance : CoeOut (KgWf L) (KgWfB L) := ⟨KgWf.toKgWfB⟩

section
variable {L : Kem} (W : KgWfB L) {σ : State} (hp : (keyGenK L).pre σ)
include W hp

theorem kgLay {s : State} (h : Top kgM σ s) : Lay kgR (kgW L) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .rcx := h.regs (.rbx, .rcx) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rsi := h.regs (.r12, .rsi) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .rdx := h.regs (.r13, .rdx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of W.small (pw4 ?_ ?_ ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_)
    (fa3 ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, h.rsp, retR]
  · exact fun _ => d3
  · exact fun _ => d1
  · exact fun _ => d2
  · exact fun _ => d5.symm
  · exact fun _ => d6.symm
  · exact fun _ => d4
  exacts [k1, k4, k2, k3, n1, n4, n2, n3,
    mem ⟨σ.gpr .rdi, 64⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rcx, L.scr⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .rsi, L.ekLen⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, L.dkLen⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r1, r4, r2, r3]

end

/-- `d` and `z`. -/
abbrev kgD (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 32
abbrev kgZ (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi + 32) 32

/-- What holds throughout. -/
structure KC (σ s : State) : Prop where
  top : Top kgM σ s
  d : bytesAt s.mem (pa s (.rbp, 0)) 32 = kgD σ
  z : bytesAt s.mem (pa s (.rbp, 32)) 32 = kgZ σ

section
variable {L : Kem} (W : KgWfB L) {σ : State} (hp : (keyGenK L).pre σ)
include W hp

theorem KC.lay {s : State} (h : KC σ s) : Lay kgR (kgW L) s := kgLay W hp h.top

theorem KC.step {s s' : State} (h : KC σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (hc : kcChk L ws = true) : KC σ s' := by
  simp only [kcChk, Bool.and_eq_true] at hc
  have L' := h.lay W hp
  exact ⟨h.top.step L' hP kgM_bases hc.1.1, by rw [L'.keepBytes hP hc.1.2]; exact h.d,
    by rw [L'.keepBytes hP hc.2]; exact h.z⟩

end

theorem pro_eq : pro = [.store (at_ .rcx 840) .rbx, .store (at_ .rcx 848) .rbp, .store (at_ .rcx 856) .r12,
    .store (at_ .rcx 864) .r13, .store (at_ .rcx 872) .r14, .store (at_ .rcx 880) .r15, .mov .rbx (.reg .rcx),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {L : Kem} (W : KgWfB L) {σ : State} (hp : (keyGenK L).pre σ) :
    WP isa (.block pro) σ fun s => KC σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp'
  have hsc := W.scr
  have hS : ⟨σ.gpr .rcx, L.scr⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ L.scr → (⟨σ.gpr .rcx, L.scr⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega_using [hsc])
  have w : ∀ o, o + 8 ≤ L.scr → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega_using [hsc]); have w1 := w 848 (by omega_using [hsc]); have w2 := w 856 (by omega_using [hsc])
  have w3 := w 864 (by omega_using [hsc]); have w4 := w 872 (by omega_using [hsc]); have w5 := w 880 (by omega_using [hsc])
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .rcx + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .rcx + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .rcx + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r12 = σ.gpr .rsi ∧ s.gpr .r13 = σ.gpr .rdx ∧
    s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13, h15⟩, k⟩ => ⟨?_, h15⟩
  have hf : Frame [⟨σ.gpr .rcx, L.scr⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega_using [hsc]))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega_using [hsc]))).writeW (List.mem_singleton_self _) _ (c 856 (by omega_using [hsc]))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega_using [hsc]))).writeW (List.mem_singleton_self _) _ (c 872 (by omega_using [hsc]))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega_using [hsc])))
  have hsd : bytesAt s.mem (σ.gpr .rdi) 64 = bytesAt σ.mem (σ.gpr .rdi) 64 :=
    bytesAt_frame hf (by simpa using d3) (by decide)
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa4 hbx hbp h12 h13, fun j hj => ?_, ?_⟩, ?_, ?_⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .rcx) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r4) (by decide)
  · rw [pa, hbp, add_ofNat_zero, ← bytesAt_take s.mem _ (show 32 ≤ 64 by decide), hsd,
      bytesAt_take σ.mem _ (show 32 ≤ 64 by decide)]
  · rw [pa, hbp, ← bytesAt_slice s.mem _ (show 32 + 32 ≤ 64 by decide), hsd,
      bytesAt_slice σ.mem _ (show 32 + 32 ≤ 64 by decide)]
    rfl

end KeyGen

/-- Proves the checks of a parameter set's layout (`KemWf`, `KeyGen.KgWf`, …),
each field evaluated by the kernel: the taint checks with `taint_decide`, the
others with `decide +kernel`; `kem_wf w` takes the checks of `KemWf` from `w`. -/
syntax "kem_wf" (ppSpace term)? : tactic
macro_rules
  | `(tactic| kem_wf) =>
    `(tactic| constructor <;> first | exact ⟨_, by taint_decide⟩ | taint_decide | decide +kernel)
  | `(tactic| kem_wf $w) =>
    `(tactic| constructor <;> first | exact $w | exact ⟨_, by taint_decide⟩ | taint_decide | decide +kernel |
      kem_wf $w)

end VG.Proof.MlKem.X86_64
