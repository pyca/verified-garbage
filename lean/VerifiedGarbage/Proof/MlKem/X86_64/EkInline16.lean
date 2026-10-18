module

public import VerifiedGarbage.Proof.MlKem.X86_64.EkInline
meta import VerifiedGarbage.Proof.MlKem.X86_64.EkInline
public import VerifiedGarbage.Proof.MlKem.X86_64.FragS4_16
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragS4_16
import all Init.Data.Nat.Bitwise.Basic
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
meta import Mathlib.Tactic.Conv
meta import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-KEM on x86-64: a fragment `Sample4.sampleH` with 16-bit coefficients, inlined

As `EkInline.lean`, for a fragment meeting `sampleHKW true` (`BatchHOk16`):
the polynomials from `sc oa` are of 16-bit coefficients, 512 bytes each
(`SHH16`, `sampleHAt16_ok`, `sampleHAt16_tr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

/-- What inlining the fragment needs: `S4H`, and the return address apart. -/
structure SHH16 (oa oz : Nat) (s : State) : Prop extends S4H16 oa oz s where
  rS : (retR s).Disjoint ⟨pa s (sc 0), 136⟩
  rA : (retR s).Disjoint ⟨pa s (sc oa), 2048⟩
  rZ : (retR s).Disjoint ⟨pa s (sc oz), 8192⟩

theorem SHH16.of {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay rbs wbs s) {oa oz : Nat}
    (hc : s4_16Chk (rbs ++ wbs) wbs oa oz = true) : SHH16 oa oz s := by
  have h := S4H16.of L hc
  simp only [s4_16Chk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨_, hrs⟩, ⟨_, hra⟩, _⟩, ⟨_, hrz⟩, _⟩, _⟩, _⟩, _⟩ := hc
  have ret : ∀ {p : Ptr} {l : Nat}, inB (rbs ++ wbs) p l = true → (retR s).Disjoint ⟨pa s p, l⟩ := fun hp => by
    obtain ⟨n, hn, hsub⟩ := L.sub hp
    exact (L.ret _ hn).sub_right hsub
  exact ⟨h, ret hrs, ret hra, ret hrz⟩

/-- The fragment's precondition, on its permissions. -/
theorem shPre16 {oa oz : Nat} {s s1 : State} (h : SHH16 oa oz s)
    (hv : s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = pa s (sc oa) ∧ s1.gpr .rdx = pa s (sc oz))
    (k : Keep argRegs s s1) :
    (sampleHKW true).pre (s1.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have rr : ∀ rd wr, retR (s1.withRegions rd wr) = retR s := fun _ _ => by
    simp only [retR, State.withRegions_gpr, hsp]
  have b24 : ∀ {R : Region}, (below (s.gpr .rsp) 32).Disjoint R → (below (s1.gpr .rsp) 24).Disjoint R :=
    fun hd => by rw [hsp]; exact hd.sub_left (below_sub (by omega) (by omega))
  simp only [sampleHKW, sample4KW, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, hv.1, hv.2.1,
    hv.2.2]
  exact ⟨trivial, rfl, h.dSA, h.dSZ, h.dAZ, by rw [rr]; exact h.rS, by rw [rr]; exact h.rA,
    by rw [rr]; exact h.rZ, b24 h.kS, b24 h.kA, b24 h.kZ, h.nwA, h.nwZ⟩

/-- Whether `SampleNTT` of the first three seeds at `p` all succeed within 280 iterations. -/
abbrev all3_16 (m : Mem) (p : Addr) : Bool :=
  (List.range 3).all fun k => (sampleNTT minIterations (seed4 m p k)).isSome

/-- What the fragment leaves. -/
structure SHPost16 (oa oz : Nat) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  frame : Frame ([⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem
  r15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (if all3_16 s.mem (pa s (sc 0)) then 1 else 0))
  res : ∀ k < 3, ∀ f, sampleNTT minIterations (seed4 s.mem (pa s (sc 0)) k) = some f →
    PolyIsW 16 s'.mem (poly4W true (pa s (sc oa)) k) f
  hs : stateAt s'.mem (pa s (sc oz) + BitVec.ofNat 64 Sample4.oHS) =
    SH.habs (stateAt s.mem (pa s (sc oz) + BitVec.ofNat 64 Sample4.oHS))
      (fun i => bytesAt s.mem (pa s (sc oz) + BitVec.ofNat 64 (Sample4.oHB + 136 * i)) 136) 3

theorem SHPost16.b {oa oz : Nat} {s s' : State} (h : SHPost16 oa oz s s') :
    PPostB s s' [(sc oa, 2048), (sc oz, 8192)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

/-- The fragment inlined, on the seeds at `scratch`, to the polynomials from `sc oa`. -/
theorem sampleHAt16_ok {b : Prog isa} (hb : BatchHOk16 b) {oa oz : Nat} {s : State} (h : SHH16 oa oz s) :
    WP isa (Encaps.sampleHAt b (sc oa) (sc oz)) s (SHPost16 oa oz s) := by
  refine WP.seq (WP.mono (s4Glue_ok oa oz h.offA h.offZ s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have hc : Covers ([⟨pa s (sc 0), 136⟩] ++ [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]) (s1.rd ++ s1.wr) := by
    rw [k.2.1, k.2.2]; exact h.c
  have hw : Covers [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s1.wr := by rw [k.2.2]; exact h.w
  refine WP.seq (WP.mono (WP.inline hb.ok (shPre16 h hv k) hc hw (Q := fun s2 => s2.rd = s1.rd ∧ s2.wr = s1.wr ∧
      abiPreserved s1 s2 ∧ Frame [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s1.mem s2.mem ∧
      (sampleHKW true).post (s1.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩])
        (s2.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]))
    (fun s2 hrd hwr habi hf _ hpost => ⟨hrd, hwr, habi, hf, hpost⟩) hb.noCalls) fun s2 ⟨hrd, hwr, habi, hf, hpost⟩ => ?_)
  refine WP.mono (and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  simp only [sampleHKW, State.withRegions_gpr, State.withRegions_mem, hv.1, hv.2.1, hv.2.2, hm] at hpost
  obtain ⟨hax, hres, hhs⟩ := hpost
  have hcs : ∀ r ∈ calleeSaved, s2.gpr r = s1.gpr r := habi.1
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_,
    fun j hj f hf => ?_, ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm]
    exact hf.mono fun r hr => List.mem_append_left _ hr
  · rw [h15, hcs .r15 (by decide), k.gpr (by decide), hax]
  · rw [hm3]; exact hres j hj f hf
  · rw [hm3]; exact hhs

/-- Two runs of the fragment inlined, from the same seeds and pointers. -/
theorem sampleHAt16_tr {b : Prog isa} (hb : BatchHOk16 b) {oa oz : Nat} :
    RelCT isa (fun x y => SHH16 oa oz x ∧ SHH16 oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp ∧
      bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136)
      (Encaps.sampleHAt b (sc oa) (sc oz)) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (SHH16 oa oz x ∧ SHH16 oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr .rsp = y.gpr .rsp ∧ bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136) ∧
      (((x1.gpr .rdi = pa x (sc 0) ∧ x1.gpr .rsi = pa x (sc oa) ∧ x1.gpr .rdx = pa x (sc oz)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = pa y (sc 0) ∧ y1.gpr .rsi = pa y (sc oa) ∧ y1.gpr .rdx = pa y (sc oz)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨s4Glue_ok oa oz hx.offA hx.offZ x, s4Glue_ok oa oz hy.offA hy.offZ y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.seq (regionModel.relCT_inline (Pre := (sampleHKW true).pre)
      (Pub := (sampleHKW true).pub) (fun s hs => let ⟨t, s', e, _, p⟩ := hb.ok s hs; ⟨t, s', e, p⟩) hb.ct ?_)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
  rintro x1 y1 ⟨x, y, ⟨hx, hy, e1, e3, e4⟩, ⟨⟨hv1, hm1⟩, k1⟩, ⟨⟨hv2, hm2⟩, k2⟩⟩
  have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
  have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
  refine ⟨_, _, _, _, shPre16 hx hv1 k1, shPre16 hy hv2 k2, ?_,
    by show Covers _ (x1.rd ++ x1.wr); rw [k1.2.1, k1.2.2]; exact hx.c,
    by show Covers _ x1.wr; rw [k1.2.2]; exact hx.w,
    by show Covers _ (y1.rd ++ y1.wr); rw [k2.2.1, k2.2.2]; exact hy.c,
    by show Covers _ y1.wr; rw [k2.2.2]; exact hy.w⟩
  show sample4K.pub (x1.withRegions _ _) (y1.withRegions _ _)
  simp only [sample4K, State.withRegions_gpr, State.withRegions_mem, hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1,
    hv2.2.2, hm1, hm2, e4, hs1, hs2, e3]
  simp only [pa, e1, and_self]

end VG.Proof.MlKem.X86_64
