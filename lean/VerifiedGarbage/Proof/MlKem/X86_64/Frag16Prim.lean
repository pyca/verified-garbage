module

public import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
public import VerifiedGarbage.Impl.MlKem.X86_64.Frag16
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# ML-KEM on x86-64: the calls of the samplers with 16-bit coefficients

As `FragPrim.lean`'s, for polynomials of 16-bit coefficients (512 bytes):
`SamplePolyCBD₂` (`cbd2_16At_ok`, `cbd2_16At_tr`) and `SampleNTT` of the seed
at `SB` (`sampleAt16_ok`, `sampleAt16_tr`), with its working space `scr`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## `SamplePolyCBD₂` -/

theorem cbd16Pre {p q : Ptr} {s s1 : State} (h : TwoH p q 128 512 s) (hv : s1.gpr .rdi = pa s p ∧ s1.gpr .rsi = pa s q)
    (k : Keep argRegs s s1) : Cbd16.cbd2_16K.pre (s1.callEntry.withRegions [⟨pa s p, 128⟩] [sR (pa s q)]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [Cbd16.cbd2_16K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2]
  exact ⟨trivial, trivial, h.d, ret_disj s1 (by rw [hsp]; exact h.kP), ret_disj s1 (by rw [hsp]; exact h.kQ)⟩

theorem cbd2_16At_ok {A : Arith} (hA : ArithOk A) {p q : Ptr} (hq : NA q) {s : State} (h : TwoH p q 128 512 s) :
    WP isa (cbd2_16At A p q) s fun s' => Post s s' [sR (pa s q)] ∧
      PolyIsW 16 s'.mem (pa s q) (samplePolyCBD 2 (bytesAt s.mem (pa s p) 128)) := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  refine WP.mono (glueCall_ok hA.cbd16.ok hA.cbd16.nosp (by rw [hA.cbd16.depth]; decide)
    (accGlue_ok p q h.off.1 h.off.2 hq1 s) (fun s1 hv _ k => cbd16Pre h hv k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [Cbd16.cbd2_16K, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hV.1, hV.2, hm₂,
    ce_bytesAt s1 (n := 128) (by decide) (by rw [hsp]; exact h.kP), hm] at hq
  exact hq

theorem cbd2_16At_tr {A : Arith} (hA : ArithOk A) {p q : Ptr} (hq : NA q) :
    RelCT isa (fun x y => TwoH p q 128 512 x ∧ TwoH p q 128 512 y ∧ x.gpr p.1 = y.gpr p.1 ∧
      x.gpr q.1 = y.gpr q.1 ∧ x.gpr .rsp = y.gpr .rsp) (cbd2_16At A p q) fun _ _ => True := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  exact glueCall_tr hA.cbd16.ok hA.cbd16.ct (V := fun x x1 => ((x1.gpr .rdi = pa x p ∧ x1.gpr .rsi = pa x q) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (block_nomem_tr (nomem_append (lea_nomem _ _) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨accGlue_ok p q hx.off.1 hx.off.2 hq1 x, accGlue_ok p q hy.off.1 hy.off.2 hq1 y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, _⟩, k1⟩ ⟨⟨hv2, _⟩, k2⟩ => by
      refine ⟨_, _, _, _, cbd16Pre hx hv1 k1, cbd16Pre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [Cbd16.cbd2_16K, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), hv1.1, hv1.2, hv2.1, hv2.2, pa, e1, e2,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e3, and_self]

/-! ## `SampleNTT` -/

/-- What a call of `vg_mlkem16_sample_ntt` of the seed at `SB` to `a`, with
the working space `z`, needs. -/
structure SampH16 (a z : Ptr) (s : State) : Prop where
  off : a.2 < 2 ^ 31
  offZ : z.2 < 2 ^ 31
  dSA : Region.Disjoint ⟨pa s (sc oSB), 34⟩ (sR (pa s a))
  dSZ : Region.Disjoint ⟨pa s (sc oSB), 34⟩ ⟨pa s z, 2048⟩
  dAZ : (sR (pa s a)).Disjoint ⟨pa s z, 2048⟩
  kS : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc oSB), 34⟩
  kA : (below (s.gpr .rsp) 32).Disjoint (sR (pa s a))
  kZ : (below (s.gpr .rsp) 32).Disjoint ⟨pa s z, 2048⟩
  nw : (pa s z).toNat + 2048 ≤ 2 ^ 64
  c : Covers ([⟨pa s (sc oSB), 34⟩] ++ [sR (pa s a), ⟨pa s z, 2048⟩]) (s.rd ++ s.wr)
  w : Covers [sR (pa s a), ⟨pa s z, 2048⟩] s.wr

theorem samp16Glue_ok (a z : Ptr) (ha : a.2 < 2 ^ 31) (hz : z.2 < 2 ^ 31) (hna : NA a) (hnz : NA z) (s : State) :
    WP isa (.block (lea .rdi (sc oSB) ++ lea .rsi a ++ lea .rdx z)) s fun s1 =>
      ((s1.gpr .rdi = pa s (sc oSB) ∧ s1.gpr .rsi = pa s a ∧ s1.gpr .rdx = pa s z) ∧ s1.mem = s.mem) ∧
        Keep argRegs s s1 := by
  have o1 : a.1 ≠ .rdi := fun e => hna (by rw [e]; decide)
  have o2 : z.1 ≠ .rdi := fun e => hnz (by rw [e]; decide)
  have o3 : z.1 ≠ .rsi := fun e => hnz (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ha, sx_ofNat hz, sx_ofNat (show oSB < 2 ^ 31 by decide), o1, o2, o3,
    List.cons_append, List.nil_append]

theorem samp16Pre {a z : Ptr} {s s1 : State} (h : SampH16 a z s)
    (hv : s1.gpr .rdi = pa s (sc oSB) ∧ s1.gpr .rsi = pa s a ∧ s1.gpr .rdx = pa s z)
    (k : Keep argRegs s s1) :
    (sampleKW true).pre (s1.callEntry.withRegions [⟨pa s (sc oSB), 34⟩] [sR (pa s a), ⟨pa s z, 2048⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [sampleKW, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), hv.1, hv.2.1, hv.2.2]
  exact ⟨trivial, rfl, h.dSA, h.dSZ, h.dAZ, ret_disj s1 (by rw [hsp]; exact h.kS),
    ret_disj s1 (by rw [hsp]; exact h.kA), ret_disj s1 (by rw [hsp]; exact h.kZ),
    stk_disj s1 (by rw [hsp]; exact h.kS), stk_disj s1 (by rw [hsp]; exact h.kA),
    stk_disj s1 (by rw [hsp]; exact h.kZ), h.nw⟩

/-- What a call of `vg_mlkem16_sample_ntt` leaves. -/
structure SampPost16 (a z : Ptr) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  frame : Frame ([sR (pa s a), ⟨pa s z, 2048⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem
  r15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
    (if (sampleNTT minIterations (bytesAt s.mem (pa s (sc oSB)) 34)).isSome then 1 else 0))
  res : ∀ f, sampleNTT minIterations (bytesAt s.mem (pa s (sc oSB)) 34) = some f → PolyIsW 16 s'.mem (pa s a) f

theorem sampleAt16_ok {a z : Ptr} (hna : NA a) (hnz : NA z) {s : State} (h : SampH16 a z s) :
    WP isa (sampleAt16 a z) s (SampPost16 a z s) := by
  refine WP.seq (WP.mono (samp16Glue_ok a z h.off h.offZ hna hnz s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine WP.seq (WP.call (sampleW_correct true) (sampleW_nosp true) (by rw [sampleW_depth]; decide)
    (samp16Pre h hv k) (by rw [k.2.1, k.2.2]; exact h.c) (by rw [k.2.2]; exact h.w)
    fun s2 hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_)
  refine WP.mono (and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  simp only [sampleKW, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2.1, hm₂, ce_bytesAt s1 (n := 34) (by decide)
    (by rw [hsp]; exact h.kS), hm] at hpost
  rw [hg₂ .rax (by decide)] at hpost
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_, ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm, ← hsp]
    rw [sampleW_depth] at hf
    exact Frame.below_mono hf (by omega) (by omega)
  · rw [h15, hcs .r15 (by decide), k.gpr (by decide), hpost.1]
  · rw [hm3]; exact hpost.2

theorem sampleAt16_tr {a z : Ptr} (hna : NA a) (hnz : NA z) :
    RelCT isa (fun x y => SampH16 a z x ∧ SampH16 a z y ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr a.1 = y.gpr a.1 ∧
      x.gpr z.1 = y.gpr z.1 ∧ x.gpr .rsp = y.gpr .rsp ∧
      bytesAt x.mem (pa x (sc oSB)) 34 = bytesAt y.mem (pa y (sc oSB)) 34)
      (sampleAt16 a z) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (SampH16 a z x ∧ SampH16 a z y ∧
      x.gpr .rbx = y.gpr .rbx ∧ x.gpr a.1 = y.gpr a.1 ∧ x.gpr z.1 = y.gpr z.1 ∧ x.gpr .rsp = y.gpr .rsp ∧
      bytesAt x.mem (pa x (sc oSB)) 34 = bytesAt y.mem (pa y (sc oSB)) 34) ∧
      (((x1.gpr .rdi = pa x (sc oSB) ∧ x1.gpr .rsi = pa x a ∧ x1.gpr .rdx = pa x z) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = pa y (sc oSB) ∧ y1.gpr .rsi = pa y a ∧ y1.gpr .rdx = pa y z) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨samp16Glue_ok a z hx.off hx.offZ hna hnz x, samp16Glue_ok a z hy.off hy.offZ hna hnz y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.seq (RelCT.callEx (sampleW_correct true) (sampleW_ct true) ?_)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
  rintro x1 y1 ⟨x, y, ⟨hx, hy, e1, e2, e5, e3, e4⟩, ⟨⟨hv1, hm1⟩, k1⟩, ⟨⟨hv2, hm2⟩, k2⟩⟩
  have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
  have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
  refine ⟨_, _, _, _, samp16Pre hx hv1 k1, samp16Pre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
    by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
    by rw [hs1, hs2, e3]⟩
  simp only [sampleKW, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
    ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2]
  rw [ce_bytesAt x1 (n := 34) (by decide) (by rw [hs1]; exact hx.kS),
    ce_bytesAt y1 (n := 34) (by decide) (by rw [hs2]; exact hy.kS), hm1, hm2, e4]
  simp only [pa, e1, e2, e5, hs1, hs2, e3, and_self]

end VG.Proof.MlKem.X86_64
