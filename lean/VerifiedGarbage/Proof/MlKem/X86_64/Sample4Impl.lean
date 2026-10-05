import VerifiedGarbage.Proof.MlKem.X86_64.Mul
import VerifiedGarbage.Proof.MlKem.X86_64.MulAvx2
import VerifiedGarbage.Proof.MlKem.X86_64.NttAvx2
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.X86_64.Kem
import VerifiedGarbage.Proof.Sha3.Seed34
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.Sha3.X86_64.X4.Bytes
import VerifiedGarbage.Impl.MlKem.X86_64.Sample4
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlKem.X86_64.AddSub
import VerifiedGarbage.Proof.Framework.KernelRfl

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.ArithOk`. -/
section

/-!
# The polynomial arithmetic a top-level function of ML-KEM calls on x86-64

What the top-level functions need of the implementations of
`vg_mlkem_multiply_ntts`, `vg_mlkem_ntt` and `vg_mlkem_inv_ntt` they call
(`Impl.MlKem.X86_64.Arith`): each meets its contract, is constant time, never
writes the stack pointer, makes no calls, and keeps MXCSR's control bits
(`ArithOk`). Both `Arith.sse` and `Arith.avx2` do (`ArithOk.sse`,
`ArithOk.avx2`); the top-level functions call the one that goes with their
implementation of `vg_mlkem_sample_ntt4` (`Callee4.arith`,
`Sample4Impl.arith`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem nosp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

/-- What a caller needs of a function with the contract `k`. -/
structure CalleeOk (k : Contract isa) (c : Prog isa) : Prop where
  ok : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c
  nosp : NoSp c
  depth : c.depth = 0
  ctl : ctlOk c = true
  sp : c.all (fun i => !isa.writesSp i) = true

/-- The polynomial arithmetic `A` is correct, constant time, and safe to call. -/
structure ArithOk (A : Arith) : Prop where
  mul : VG.Proof.MlKem.X86_64.CalleeOk mulK A.mul
  ntt : VG.Proof.MlKem.X86_64.CalleeOk (inPlaceK ntt) A.ntt
  nttInv : VG.Proof.MlKem.X86_64.CalleeOk (inPlaceK nttInv) A.nttInv

theorem ArithOk.sse : VG.Proof.MlKem.X86_64.ArithOk .sse where
  mul := ⟨mul_correct, mul_ct, VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel), by decide +kernel, by decide +kernel,
    Code.all_of_allInstrs (by decide +kernel)⟩
  ntt := ⟨ntt_correct, ntt_ct, VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel), by decide +kernel, by decide +kernel,
    Code.all_of_allInstrs (by decide +kernel)⟩
  nttInv := ⟨nttInv_correct, nttInv_ct, VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel), by decide +kernel, by decide +kernel,
    Code.all_of_allInstrs (by decide +kernel)⟩

theorem ArithOk.avx2 : VG.Proof.MlKem.X86_64.ArithOk .avx2 where
  mul := ⟨mulY_correct, mulY_ct, VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel), by decide +kernel, by decide +kernel,
    Code.all_of_allInstrs (by decide +kernel)⟩
  ntt := ⟨nttY_correct, nttY_ct, VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel), by decide +kernel, by decide +kernel,
    Code.all_of_allInstrs (by decide +kernel)⟩
  nttInv := ⟨nttInvY_correct, nttInvY_ct, VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel), by decide +kernel, by decide +kernel,
    Code.all_of_allInstrs (by decide +kernel)⟩

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.FragPrim`. -/
section

/-!
# ML-KEM-768 on x86-64: the calls of the polynomial primitives

For each call of a polynomial primitive from a top-level function: what it
needs of the state (`…H`), what it does (`…_ok`), and that two runs that agree
on its public data leak the same (`…_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem execBlock_nomem {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) :
    ∀ {s s' : State} {t : List Leak}, execBlock isa is s = some (s', t) → t = [] := by
  induction is with
  | nil => intro s s' t e; simp [execBlock] at e; exact e.2
  | cons i is ih =>
    intro s s' t e
    simp only [execBlock] at e
    split at e
    · cases e
    · obtain ⟨⟨s₂, t₂⟩, e₂, he⟩ := Option.map_eq_some_iff.mp e
      simp only [Prod.mk.injEq] at he
      rw [← he.2, show addrs i s = [] from h i (List.mem_cons_self ..) s,
        ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) e₂]
      rfl

/-- A block that accesses no memory leaks nothing. -/
theorem block_nomem_tr {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) {P : State → State → Prop} :
    RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨(VG.Proof.MlKem.X86_64.execBlock_nomem h e₁).trans (VG.Proof.MlKem.X86_64.execBlock_nomem h e₂).symm, trivial⟩

theorem lea_nomem (d : Reg) (p : Ptr) : ∀ i ∈ lea d p, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [lea, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem nomem_append {a b : List Instr} (ha : ∀ i ∈ a, ∀ s, isa.addrs i s = [])
    (hb : ∀ i ∈ b, ∀ s, isa.addrs i s = []) : ∀ i ∈ a ++ b, ∀ s, isa.addrs i s = [] := by
  intro i hi s
  rcases List.mem_append.mp hi with h | h
  exacts [ha i h s, hb i h s]

theorem mov32i_nomem (d : Reg) (v : BitVec 32) : ∀ i ∈ ([.mov32 d (.imm v)] : List Instr), ∀ s, isa.addrs i s = [] := by
  intro i hi s
  simp only [List.mem_singleton] at hi
  subst hi; rfl

theorem covers_nil_wr {rs : List Region} {s : State} (h : Covers rs s.wr) : Covers ([] ++ rs) (s.rd ++ s.wr) :=
  fun a n hi => by
    rw [List.nil_append] at hi
    obtain ⟨r, hr, hc⟩ := h a n hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩

/-! ## The callees' stack -/

theorem ntt_nosp : NoSp Impl.MlKem.X86_64.ntt := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)
theorem nttInv_nosp : NoSp Impl.MlKem.X86_64.nttInv := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)
theorem mul_nosp : NoSp multiplyNTTs := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)
theorem add_nosp : NoSp Impl.MlKem.X86_64.add := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)
theorem sub_nosp : NoSp Impl.MlKem.X86_64.sub := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)
theorem cbd2_nosp : NoSp cbd2 := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)
theorem encode12_nosp : NoSp encode12 := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)
theorem decode12_nosp : NoSp decode12 := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)
theorem ce_nosp : NoSp compressEncode := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)
theorem dd_nosp : NoSp decodeDecompress := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)
theorem sample_nosp : NoSp sampleNTT := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)

theorem ntt_depth : Impl.MlKem.X86_64.ntt.depth = 0 := by decide +kernel
theorem nttInv_depth : Impl.MlKem.X86_64.nttInv.depth = 0 := by decide +kernel
theorem mul_depth : multiplyNTTs.depth = 0 := by decide +kernel
theorem add_depth : Impl.MlKem.X86_64.add.depth = 0 := by decide +kernel
theorem sub_depth : Impl.MlKem.X86_64.sub.depth = 0 := by decide +kernel
theorem cbd2_depth : cbd2.depth = 0 := by decide +kernel
theorem encode12_depth : encode12.depth = 0 := by decide +kernel
theorem decode12_depth : decode12.depth = 0 := by decide +kernel
theorem ce_depth : compressEncode.depth = 0 := by decide +kernel
theorem dd_depth : decodeDecompress.depth = 0 := by decide +kernel
theorem sample_depth : sampleNTT.depth = 2 := by decide +kernel

/-! ## `NTT` and `NTT⁻¹` in place -/

/-- What a call of `vg_mlkem_ntt` or `vg_mlkem_inv_ntt` on `f` needs. -/
structure IpH (f : Ptr) (s : State) : Prop where
  off : f.2 < 2 ^ 31
  red : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)
  d : (pR (VG.Proof.MlKem.X86_64.pa s f)).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s (sc oSS)))
  kF : (below (s.gpr .rsp) 32).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s f))
  kZ : (below (s.gpr .rsp) 32).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s (sc oSS)))
  w : Covers [pR (VG.Proof.MlKem.X86_64.pa s f), pR (VG.Proof.MlKem.X86_64.pa s (sc oSS))] s.wr

theorem ipGlue_ok (f : Ptr) (hf : f.2 < 2 ^ 31) (s : State) :
    WP isa (.block (lea .rdi f ++ lea .rsi (sc oSS))) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s (sc oSS)) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat hf, sx_ofNat (show oSS < 2 ^ 31 by decide), List.cons_append, List.nil_append]

theorem ipPre {t : Poly → Poly} {f : Ptr} {s s1 : State} (h : VG.Proof.MlKem.X86_64.IpH f s) (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s (sc oSS))
    (hm : s1.mem = s.mem) (k : Keep argRegs s s1) :
    (inPlaceK t).pre (s1.callEntry.withRegions [] [pR (VG.Proof.MlKem.X86_64.pa s f), pR (VG.Proof.MlKem.X86_64.pa s (sc oSS))]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [inPlaceK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2]
  refine ⟨trivial, trivial, h.d, ret_disj s1 (by rw [hsp]; exact h.kF), ret_disj s1 (by rw [hsp]; exact h.kZ), ?_⟩
  rw [ce_reduced s1 (by rw [hsp]; exact h.kF), hm]; exact h.red

/-- A call of an in-place transformation `t` (`NTT` or `NTT⁻¹`). -/
theorem ipAt_ok {t : Poly → Poly} {n : String} {c : Prog isa}
    (hv : ∀ s, (inPlaceK t).pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (inPlaceK t).post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 2) {f : Ptr} {s : State} (h : VG.Proof.MlKem.X86_64.IpH f s) :
    WP isa (.seq (.block (lea .rdi f ++ lea .rsi (sc oSS))) (.call n c)) s fun s' =>
      Post s s' [pR (VG.Proof.MlKem.X86_64.pa s f), pR (VG.Proof.MlKem.X86_64.pa s (sc oSS))] ∧ PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s f) (t (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f))) := by
  refine WP.mono (glueCall_ok hv hsp (Nat.le_succ_of_le hd) (VG.Proof.MlKem.X86_64.ipGlue_ok f h.off s) (fun s1 hv hm k => VG.Proof.MlKem.X86_64.ipPre h hv hm k)
    (VG.Proof.MlKem.X86_64.covers_nil_wr h.w) h.w) fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [inPlaceK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    hV.1, hm₂, ce_polyAt s1 (by rw [hsp]; exact h.kF), hm] at hq
  exact hq


theorem ipAt_tr {t : Poly → Poly} {n : String} {c : Prog isa}
    (hv : ∀ s, (inPlaceK t).pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (inPlaceK t).post s s')
    (hct : ConstantTime isa (inPlaceK t).pre (inPlaceK t).pub c) {f : Ptr} :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.IpH f x ∧ VG.Proof.MlKem.X86_64.IpH f y ∧ x.gpr f.1 = y.gpr f.1 ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr .rsp = y.gpr .rsp) (.seq (.block (lea .rdi f ++ lea .rsi (sc oSS))) (.call n c)) fun _ _ => True :=
  glueCall_tr hv hct (V := fun x x1 => ((x1.gpr .rdi = VG.Proof.MlKem.X86_64.pa x f ∧ x1.gpr .rsi = VG.Proof.MlKem.X86_64.pa x (sc oSS)) ∧ x1.mem = x.mem) ∧
      Keep argRegs x x1)
    (VG.Proof.MlKem.X86_64.block_nomem_tr (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.lea_nomem _ _) (VG.Proof.MlKem.X86_64.lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.ipGlue_ok f hx.off x, VG.Proof.MlKem.X86_64.ipGlue_ok f hy.off y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨[], _, [], _, VG.Proof.MlKem.X86_64.ipPre hx hv1 hm1 k1, VG.Proof.MlKem.X86_64.ipPre hy hv2 hm2 k2, ?_, VG.Proof.MlKem.X86_64.covers_nil_wr (by rw [k1.2.2]; exact hx.w),
        by rw [k1.2.2]; exact hx.w, VG.Proof.MlKem.X86_64.covers_nil_wr (by rw [k2.2.2]; exact hy.w), by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [inPlaceK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), hv1.1, hv1.2, hv2.1, hv2.2, VG.Proof.MlKem.X86_64.pa, e1, e2, k1.gpr (r := .rsp) (by decide),
        k2.gpr (r := .rsp) (by decide), e3, and_self]

/-! ## Addition and subtraction -/

/-- What a call of `vg_mlkem_add` or `vg_mlkem_sub` on `f`, `g` needs. -/
structure AccH (f g : Ptr) (s : State) : Prop where
  off : f.2 < 2 ^ 31 ∧ g.2 < 2 ^ 31
  redF : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)
  redG : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g)
  d : (pR (VG.Proof.MlKem.X86_64.pa s f)).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s g))
  kF : (below (s.gpr .rsp) 32).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s f))
  kG : (below (s.gpr .rsp) 32).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s g))
  c : Covers ([pR (VG.Proof.MlKem.X86_64.pa s g)] ++ [pR (VG.Proof.MlKem.X86_64.pa s f)]) (s.rd ++ s.wr)
  w : Covers [pR (VG.Proof.MlKem.X86_64.pa s f)] s.wr

theorem accGlue_ok (f g : Ptr) (hf : f.2 < 2 ^ 31) (hg : g.2 < 2 ^ 31) (hgr : g.1 ≠ .rdi) (s : State) :
    WP isa (.block (lea .rdi f ++ lea .rsi g)) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s g) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat hf, sx_ofNat hg, hgr, List.cons_append, List.nil_append]

theorem accPre {t : Poly → Poly → Poly} {f g : Ptr} {s s1 : State} (h : VG.Proof.MlKem.X86_64.AccH f g s)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s g) (hm : s1.mem = s.mem) (k : Keep argRegs s s1) :
    (accK t).pre (s1.callEntry.withRegions [pR (VG.Proof.MlKem.X86_64.pa s g)] [pR (VG.Proof.MlKem.X86_64.pa s f)]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [accK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2]
  refine ⟨trivial, trivial, h.d, ret_disj s1 (by rw [hsp]; exact h.kF), ret_disj s1 (by rw [hsp]; exact h.kG),
    ?_, ?_⟩
  · rw [ce_reduced s1 (by rw [hsp]; exact h.kF), hm]; exact h.redF
  · rw [ce_reduced s1 (by rw [hsp]; exact h.kG), hm]; exact h.redG

theorem accAt_ok {t : Poly → Poly → Poly} {n : String} {c : Prog isa}
    (hv : ∀ s, (accK t).pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (accK t).post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 2) {f g : Ptr} (hgr : g.1 ≠ .rdi) {s : State} (h : VG.Proof.MlKem.X86_64.AccH f g s) :
    WP isa (.seq (.block (lea .rdi f ++ lea .rsi g)) (.call n c)) s fun s' =>
      Post s s' [pR (VG.Proof.MlKem.X86_64.pa s f)] ∧ PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s f) (t (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f)) (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s g))) := by
  refine WP.mono (glueCall_ok hv hsp (Nat.le_succ_of_le hd) (VG.Proof.MlKem.X86_64.accGlue_ok f g h.off.1 h.off.2 hgr s) (fun s1 hv hm k => VG.Proof.MlKem.X86_64.accPre h hv hm k)
    h.c h.w) fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [accK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hV.1, hV.2, hm₂, ce_polyAt s1 (by rw [hsp]; exact h.kF),
    ce_polyAt s1 (by rw [hsp]; exact h.kG), hm] at hq
  exact hq

theorem accAt_tr {t : Poly → Poly → Poly} {n : String} {c : Prog isa}
    (hv : ∀ s, (accK t).pre s → ∃ tr s', Exec isa c s tr s' ∧ abiPreserved s s' ∧ (accK t).post s s')
    (hct : ConstantTime isa (accK t).pre (accK t).pub c) {f g : Ptr} (hgr : g.1 ≠ .rdi) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.AccH f g x ∧ VG.Proof.MlKem.X86_64.AccH f g y ∧ x.gpr f.1 = y.gpr f.1 ∧ x.gpr g.1 = y.gpr g.1 ∧
      x.gpr .rsp = y.gpr .rsp) (.seq (.block (lea .rdi f ++ lea .rsi g)) (.call n c)) fun _ _ => True :=
  glueCall_tr hv hct (V := fun x x1 => ((x1.gpr .rdi = VG.Proof.MlKem.X86_64.pa x f ∧ x1.gpr .rsi = VG.Proof.MlKem.X86_64.pa x g) ∧ x1.mem = x.mem) ∧
      Keep argRegs x x1)
    (VG.Proof.MlKem.X86_64.block_nomem_tr (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.lea_nomem _ _) (VG.Proof.MlKem.X86_64.lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.accGlue_ok f g hx.off.1 hx.off.2 hgr x, VG.Proof.MlKem.X86_64.accGlue_ok f g hy.off.1 hy.off.2 hgr y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.accPre hx hv1 hm1 k1, VG.Proof.MlKem.X86_64.accPre hy hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [accK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), hv1.1, hv1.2, hv2.1, hv2.2, VG.Proof.MlKem.X86_64.pa, e1, e2, k1.gpr (r := .rsp) (by decide),
        k2.gpr (r := .rsp) (by decide), e3, and_self]


/-! ## `MultiplyNTTs` -/

/-- What a call of `vg_mlkem_multiply_ntts` writing `h` from `f`, `g` needs. -/
structure MulH (h f g : Ptr) (s : State) : Prop where
  off : h.2 < 2 ^ 31 ∧ f.2 < 2 ^ 31 ∧ g.2 < 2 ^ 31
  redF : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)
  redG : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g)
  hf : (pR (VG.Proof.MlKem.X86_64.pa s h)).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s f))
  hg : (pR (VG.Proof.MlKem.X86_64.pa s h)).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s g))
  hz : (pR (VG.Proof.MlKem.X86_64.pa s h)).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s (sc oSS)))
  fz : (pR (VG.Proof.MlKem.X86_64.pa s f)).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s (sc oSS)))
  gz : (pR (VG.Proof.MlKem.X86_64.pa s g)).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s (sc oSS)))
  kH : (below (s.gpr .rsp) 32).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s h))
  kF : (below (s.gpr .rsp) 32).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s f))
  kG : (below (s.gpr .rsp) 32).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s g))
  kZ : (below (s.gpr .rsp) 32).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s (sc oSS)))
  c : Covers ([pR (VG.Proof.MlKem.X86_64.pa s f), pR (VG.Proof.MlKem.X86_64.pa s g)] ++ [pR (VG.Proof.MlKem.X86_64.pa s h), pR (VG.Proof.MlKem.X86_64.pa s (sc oSS))]) (s.rd ++ s.wr)
  w : Covers [pR (VG.Proof.MlKem.X86_64.pa s h), pR (VG.Proof.MlKem.X86_64.pa s (sc oSS))] s.wr

/-- The bases of the arguments are not argument registers. -/
abbrev NA (p : Ptr) : Prop := p.1 ∉ argRegs

theorem mulGlue_ok (h f g : Ptr) (ho : h.2 < 2 ^ 31 ∧ f.2 < 2 ^ 31 ∧ g.2 < 2 ^ 31) (hf : VG.Proof.MlKem.X86_64.NA f) (hg : VG.Proof.MlKem.X86_64.NA g)
    (s : State) :
    WP isa (.block (lea .rdi h ++ lea .rsi f ++ lea .rdx g ++ lea .rcx (sc oSS))) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s h ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s g ∧ s1.gpr .rcx = VG.Proof.MlKem.X86_64.pa s (sc oSS)) ∧
        s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  have f1 : f.1 ≠ .rdi := fun e => hf (by rw [e]; decide)
  have g1 : g.1 ≠ .rdi := fun e => hg (by rw [e]; decide)
  have g2 : g.1 ≠ .rsi := fun e => hg (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2.1, sx_ofNat ho.2.2, sx_ofNat (show oSS < 2 ^ 31 by decide), f1, g1, g2,
    List.cons_append, List.nil_append]

theorem mulPre {h f g : Ptr} {s s1 : State} (H : VG.Proof.MlKem.X86_64.MulH h f g s)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s h ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s g ∧ s1.gpr .rcx = VG.Proof.MlKem.X86_64.pa s (sc oSS))
    (hm : s1.mem = s.mem) (k : Keep argRegs s s1) :
    mulK.pre (s1.callEntry.withRegions [pR (VG.Proof.MlKem.X86_64.pa s f), pR (VG.Proof.MlKem.X86_64.pa s g)] [pR (VG.Proof.MlKem.X86_64.pa s h), pR (VG.Proof.MlKem.X86_64.pa s (sc oSS))]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [mulK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  refine ⟨trivial, trivial, H.hf, H.hg, H.hz, H.fz, H.gz, ret_disj s1 (by rw [hsp]; exact H.kH),
    ret_disj s1 (by rw [hsp]; exact H.kF), ret_disj s1 (by rw [hsp]; exact H.kG),
    ret_disj s1 (by rw [hsp]; exact H.kZ), ?_, ?_⟩
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kF), hm]; exact H.redF
  · rw [ce_reduced s1 (by rw [hsp]; exact H.kG), hm]; exact H.redG

theorem mulAt_ok {A : Arith} (hA : VG.Proof.MlKem.X86_64.ArithOk A) {h f g : Ptr} (hf : VG.Proof.MlKem.X86_64.NA f) (hg : VG.Proof.MlKem.X86_64.NA g) {s : State}
    (H : VG.Proof.MlKem.X86_64.MulH h f g s) :
    WP isa (mulAt A h f g) s fun s' => Post s s' [pR (VG.Proof.MlKem.X86_64.pa s h), pR (VG.Proof.MlKem.X86_64.pa s (sc oSS))] ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s h) (multiplyNTTs (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f)) (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s g))) := by
  refine WP.mono (glueCall_ok hA.mul.ok hA.mul.nosp (by rw [hA.mul.depth]; decide) (VG.Proof.MlKem.X86_64.mulGlue_ok h f g H.off hf hg s)
    (fun s1 hv hm k => VG.Proof.MlKem.X86_64.mulPre H hv hm k) H.c H.w) fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [mulK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1, hm₂,
    ce_polyAt s1 (by rw [hsp]; exact H.kF), ce_polyAt s1 (by rw [hsp]; exact H.kG), hm] at hq
  exact hq

theorem mulAt_tr {A : Arith} (hA : VG.Proof.MlKem.X86_64.ArithOk A) {h f g : Ptr} (hf : VG.Proof.MlKem.X86_64.NA f) (hg : VG.Proof.MlKem.X86_64.NA g) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.MulH h f g x ∧ VG.Proof.MlKem.X86_64.MulH h f g y ∧ x.gpr h.1 = y.gpr h.1 ∧ x.gpr f.1 = y.gpr f.1 ∧
      x.gpr g.1 = y.gpr g.1 ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp) (mulAt A h f g) fun _ _ => True :=
  glueCall_tr hA.mul.ok hA.mul.ct (V := fun x x1 => ((x1.gpr .rdi = VG.Proof.MlKem.X86_64.pa x h ∧ x1.gpr .rsi = VG.Proof.MlKem.X86_64.pa x f ∧
      x1.gpr .rdx = VG.Proof.MlKem.X86_64.pa x g ∧ x1.gpr .rcx = VG.Proof.MlKem.X86_64.pa x (sc oSS)) ∧ x1.mem = x.mem) ∧ Keep argRegs x x1)
    (VG.Proof.MlKem.X86_64.block_nomem_tr (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.lea_nomem _ _) (VG.Proof.MlKem.X86_64.lea_nomem _ _)) (VG.Proof.MlKem.X86_64.lea_nomem _ _))
      (VG.Proof.MlKem.X86_64.lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.mulGlue_ok h f g hx.off hf hg x, VG.Proof.MlKem.X86_64.mulGlue_ok h f g hy.off hf hg y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3, e4, e5⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.mulPre hx hv1 hm1 k1, VG.Proof.MlKem.X86_64.mulPre hy hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e5]⟩
      simp only [mulK, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), ce_gpr' _ (by decide : Reg.rdx ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1, hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1,
        hv2.2.2.2, VG.Proof.MlKem.X86_64.pa, e1, e2, e3, e4, k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e5, and_self]


/-! ## Two-pointer calls: `SamplePolyCBD₂`, `ByteEncode₁₂`, `ByteDecode₁₂` -/

/-- What a call reading `n` bytes (or a polynomial) at `p` and writing `m` bytes (or a polynomial) at `q` needs. -/
structure TwoH (p q : Ptr) (n m : Nat) (s : State) : Prop where
  off : p.2 < 2 ^ 31 ∧ q.2 < 2 ^ 31
  d : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s p, n⟩ ⟨VG.Proof.MlKem.X86_64.pa s q, m⟩
  kP : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s p, n⟩
  kQ : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s q, m⟩
  c : Covers ([⟨VG.Proof.MlKem.X86_64.pa s p, n⟩] ++ [⟨VG.Proof.MlKem.X86_64.pa s q, m⟩]) (s.rd ++ s.wr)
  w : Covers [⟨VG.Proof.MlKem.X86_64.pa s q, m⟩] s.wr

theorem cbdPre {p q : Ptr} {s s1 : State} (h : VG.Proof.MlKem.X86_64.TwoH p q 128 1024 s) (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s p ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s q)
    (k : Keep argRegs s s1) : cbd2K.pre (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s p, 128⟩] [pR (VG.Proof.MlKem.X86_64.pa s q)]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [cbd2K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2]
  exact ⟨trivial, trivial, h.d, ret_disj s1 (by rw [hsp]; exact h.kP), ret_disj s1 (by rw [hsp]; exact h.kQ)⟩

theorem cbd2At_ok {p q : Ptr} (hq : VG.Proof.MlKem.X86_64.NA q) {s : State} (h : VG.Proof.MlKem.X86_64.TwoH p q 128 1024 s) :
    WP isa (cbd2At p q) s fun s' => Post s s' [pR (VG.Proof.MlKem.X86_64.pa s q)] ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s q) (samplePolyCBD 2 (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s p) 128)) := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  refine WP.mono (glueCall_ok cbd2_correct VG.Proof.MlKem.X86_64.cbd2_nosp (by rw [VG.Proof.MlKem.X86_64.cbd2_depth]; decide)
    (VG.Proof.MlKem.X86_64.accGlue_ok p q h.off.1 h.off.2 hq1 s) (fun s1 hv _ k => VG.Proof.MlKem.X86_64.cbdPre h hv k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [cbd2K, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hV.1, hV.2, hm₂,
    ce_bytesAt s1 (n := 128) (by decide) (by rw [hsp]; exact h.kP), hm] at hq
  exact hq

theorem cbd2At_tr {p q : Ptr} (hq : VG.Proof.MlKem.X86_64.NA q) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.TwoH p q 128 1024 x ∧ VG.Proof.MlKem.X86_64.TwoH p q 128 1024 y ∧ x.gpr p.1 = y.gpr p.1 ∧
      x.gpr q.1 = y.gpr q.1 ∧ x.gpr .rsp = y.gpr .rsp) (cbd2At p q) fun _ _ => True := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  exact glueCall_tr cbd2_correct cbd2_ct (V := fun x x1 => ((x1.gpr .rdi = VG.Proof.MlKem.X86_64.pa x p ∧ x1.gpr .rsi = VG.Proof.MlKem.X86_64.pa x q) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (VG.Proof.MlKem.X86_64.block_nomem_tr (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.lea_nomem _ _) (VG.Proof.MlKem.X86_64.lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.accGlue_ok p q hx.off.1 hx.off.2 hq1 x, VG.Proof.MlKem.X86_64.accGlue_ok p q hy.off.1 hy.off.2 hq1 y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, _⟩, k1⟩ ⟨⟨hv2, _⟩, k2⟩ => by
      refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.cbdPre hx hv1 k1, VG.Proof.MlKem.X86_64.cbdPre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [cbd2K, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), hv1.1, hv1.2, hv2.1, hv2.2, VG.Proof.MlKem.X86_64.pa, e1, e2,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e3, and_self]

theorem encPre {p q : Ptr} {s s1 : State} (h : VG.Proof.MlKem.X86_64.TwoH p q 1024 384 s) (hr : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s p))
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s p ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s q) (hm : s1.mem = s.mem) (k : Keep argRegs s s1) :
    encode12K.pre (s1.callEntry.withRegions [pR (VG.Proof.MlKem.X86_64.pa s p)] [⟨VG.Proof.MlKem.X86_64.pa s q, 384⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [encode12K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2]
  refine ⟨trivial, trivial, h.d, ret_disj s1 (by rw [hsp]; exact h.kP), ret_disj s1 (by rw [hsp]; exact h.kQ), ?_⟩
  rw [ce_reduced s1 (by rw [hsp]; exact h.kP), hm]; exact hr

theorem enc12At_ok {p q : Ptr} (hq : VG.Proof.MlKem.X86_64.NA q) {s : State} (h : VG.Proof.MlKem.X86_64.TwoH p q 1024 384 s) (hr : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s p)) :
    WP isa (enc12At p q) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s q, 384⟩] ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s q) 384 = encode12 (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s p)) := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  refine WP.mono (glueCall_ok encode12_correct VG.Proof.MlKem.X86_64.encode12_nosp (by rw [VG.Proof.MlKem.X86_64.encode12_depth]; decide)
    (VG.Proof.MlKem.X86_64.accGlue_ok p q h.off.1 h.off.2 hq1 s) (fun s1 hv hm k => VG.Proof.MlKem.X86_64.encPre h hr hv hm k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [encode12K, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hV.1, hV.2, hm₂, ce_polyAt s1 (by rw [hsp]; exact h.kP), hm] at hq
  exact hq

theorem enc12At_tr {p q : Ptr} (hq : VG.Proof.MlKem.X86_64.NA q) :
    RelCT isa (fun x y => (VG.Proof.MlKem.X86_64.TwoH p q 1024 384 x ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x p)) ∧ (VG.Proof.MlKem.X86_64.TwoH p q 1024 384 y ∧
      Reduced y.mem (VG.Proof.MlKem.X86_64.pa y p)) ∧ x.gpr p.1 = y.gpr p.1 ∧ x.gpr q.1 = y.gpr q.1 ∧ x.gpr .rsp = y.gpr .rsp)
      (enc12At p q) fun _ _ => True := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  exact glueCall_tr encode12_correct encode12_ct (V := fun x x1 => ((x1.gpr .rdi = VG.Proof.MlKem.X86_64.pa x p ∧ x1.gpr .rsi = VG.Proof.MlKem.X86_64.pa x q) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (VG.Proof.MlKem.X86_64.block_nomem_tr (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.lea_nomem _ _) (VG.Proof.MlKem.X86_64.lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.accGlue_ok p q hx.1.off.1 hx.1.off.2 hq1 x, VG.Proof.MlKem.X86_64.accGlue_ok p q hy.1.off.1 hy.1.off.2 hq1 y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.encPre hx.1 hx.2 hv1 hm1 k1, VG.Proof.MlKem.X86_64.encPre hy.1 hy.2 hv2 hm2 k2, ?_,
        by rw [k1.2.1, k1.2.2]; exact hx.1.c, by rw [k1.2.2]; exact hx.1.w, by rw [k2.2.1, k2.2.2]; exact hy.1.c,
        by rw [k2.2.2]; exact hy.1.w, by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [encode12K, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), hv1.1, hv1.2, hv2.1, hv2.2, VG.Proof.MlKem.X86_64.pa, e1, e2,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e3, and_self]

theorem decPre {p q : Ptr} {s s1 : State} (h : VG.Proof.MlKem.X86_64.TwoH p q 384 1024 s) (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s p ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s q)
    (k : Keep argRegs s s1) : decode12K.pre (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s p, 384⟩] [pR (VG.Proof.MlKem.X86_64.pa s q)]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [decode12K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2]
  exact ⟨trivial, trivial, h.d, ret_disj s1 (by rw [hsp]; exact h.kP), ret_disj s1 (by rw [hsp]; exact h.kQ)⟩

theorem dec12At_ok {p q : Ptr} (hq : VG.Proof.MlKem.X86_64.NA q) {s : State} (h : VG.Proof.MlKem.X86_64.TwoH p q 384 1024 s) :
    WP isa (dec12At p q) s fun s' => Post s s' [pR (VG.Proof.MlKem.X86_64.pa s q)] ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s q) (decode12 (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s p) 384)) := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  refine WP.mono (glueCall_ok decode12_correct VG.Proof.MlKem.X86_64.decode12_nosp (by rw [VG.Proof.MlKem.X86_64.decode12_depth]; decide)
    (VG.Proof.MlKem.X86_64.accGlue_ok p q h.off.1 h.off.2 hq1 s) (fun s1 hv _ k => VG.Proof.MlKem.X86_64.decPre h hv k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [decode12K, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hV.1, hV.2, hm₂,
    ce_bytesAt s1 (n := 384) (by decide) (by rw [hsp]; exact h.kP), hm] at hq
  exact hq

theorem dec12At_tr {p q : Ptr} (hq : VG.Proof.MlKem.X86_64.NA q) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.TwoH p q 384 1024 x ∧ VG.Proof.MlKem.X86_64.TwoH p q 384 1024 y ∧ x.gpr p.1 = y.gpr p.1 ∧
      x.gpr q.1 = y.gpr q.1 ∧ x.gpr .rsp = y.gpr .rsp) (dec12At p q) fun _ _ => True := by
  have hq1 : q.1 ≠ .rdi := fun e => hq (by rw [e]; decide)
  exact glueCall_tr decode12_correct decode12_ct (V := fun x x1 => ((x1.gpr .rdi = VG.Proof.MlKem.X86_64.pa x p ∧ x1.gpr .rsi = VG.Proof.MlKem.X86_64.pa x q) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (VG.Proof.MlKem.X86_64.block_nomem_tr (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.lea_nomem _ _) (VG.Proof.MlKem.X86_64.lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.accGlue_ok p q hx.off.1 hx.off.2 hq1 x, VG.Proof.MlKem.X86_64.accGlue_ok p q hy.off.1 hy.off.2 hq1 y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, _⟩, k1⟩ ⟨⟨hv2, _⟩, k2⟩ => by
      refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.decPre hx hv1 k1, VG.Proof.MlKem.X86_64.decPre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [decode12K, State.withRegions_gpr, State.callEntry_rsp, ce_gpr' _ (by decide : Reg.rdi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rsi ≠ .rsp), hv1.1, hv1.2, hv2.1, hv2.2, VG.Proof.MlKem.X86_64.pa, e1, e2,
        k1.gpr (r := .rsp) (by decide), k2.gpr (r := .rsp) (by decide), e3, and_self]


/-! ## `ByteEncode_d ∘ Compress_d` and `Decompress_d ∘ ByteDecode_d` -/

theorem sw32_64' (d : Nat) (hd : d < 2 ^ 32) : ((BitVec.ofNat 64 d).setWidth 32).toNat = d := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A verified implementation `c`, named `n`, of the compression for the
widths `ws` (`vg_mlkem_compress_encode`, `vg_mlkem1024_compress_encode`). -/
structure CEImpl (n : String) (c : Prog isa) (ws : List Nat) : Prop where
  le : ∀ d ∈ ws, d ≤ 11
  correct : ∀ s, (compressEncodeWK ws).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (compressEncodeWK ws).post s s'
  ct : ConstantTime isa (compressEncodeWK ws).pre (compressEncodeWK ws).pub c
  nosp : NoSp c
  depth : c.depth = 0

/-- A verified implementation `c`, named `n`, of the decompression for the
widths `ws` (`vg_mlkem_decode_decompress`, `vg_mlkem1024_decode_decompress`). -/
structure DDImpl (n : String) (c : Prog isa) (ws : List Nat) : Prop where
  le : ∀ d ∈ ws, d ≤ 11
  correct : ∀ s, (decodeDecompressWK ws).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (decodeDecompressWK ws).post s s'
  ct : ConstantTime isa (decodeDecompressWK ws).pre (decodeDecompressWK ws).pub c
  nosp : NoSp c
  depth : c.depth = 0

/-- What a call of a compression of `f` to `out` with width `d` in `ws` needs. -/
structure CEH (ws : List Nat) (f out : Ptr) (d : Nat) (s : State) : Prop where
  off : f.2 < 2 ^ 31 ∧ out.2 < 2 ^ 31
  dw : d ∈ ws
  red : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)
  dj : Region.Disjoint (pR (VG.Proof.MlKem.X86_64.pa s f)) ⟨VG.Proof.MlKem.X86_64.pa s out, 32 * d⟩
  kF : (below (s.gpr .rsp) 32).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s f))
  kO : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s out, 32 * d⟩
  c : Covers ([pR (VG.Proof.MlKem.X86_64.pa s f)] ++ [⟨VG.Proof.MlKem.X86_64.pa s out, 32 * d⟩]) (s.rd ++ s.wr)
  w : Covers [⟨VG.Proof.MlKem.X86_64.pa s out, 32 * d⟩] s.wr

theorem ceGlue_ok (f out : Ptr) (d : Nat) (ho : f.2 < 2 ^ 31 ∧ out.2 < 2 ^ 31) (hd : d ≤ 11) (hout : VG.Proof.MlKem.X86_64.NA out) (s : State) :
    WP isa (.block (lea .rdi f ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 d))] : List Instr) ++ lea .rdx out ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 (32 * d)))] : List Instr))) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rsi = BitVec.ofNat 64 d ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s out ∧
        s1.gpr .rcx = BitVec.ofNat 64 (32 * d)) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  have o1 : out.1 ≠ .rsi := fun e => hout (by rw [e]; decide)
  have o2 : out.1 ≠ .rdi := fun e => hout (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2, o1, o2, sw_ofNat (show d < 2 ^ 32 by omega),
    sw_ofNat (show 32 * d < 2 ^ 32 by omega), List.cons_append, List.nil_append]

theorem cePre {ws : List Nat} (hle : ∀ d ∈ ws, d ≤ 11) {f out : Ptr} {d : Nat} {s s1 : State} (h : VG.Proof.MlKem.X86_64.CEH ws f out d s)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s f ∧ s1.gpr .rsi = BitVec.ofNat 64 d ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s out ∧
      s1.gpr .rcx = BitVec.ofNat 64 (32 * d)) (hm : s1.mem = s.mem) (k : Keep argRegs s s1) :
    (compressEncodeWK ws).pre (s1.callEntry.withRegions [pR (VG.Proof.MlKem.X86_64.pa s f)] [⟨VG.Proof.MlKem.X86_64.pa s out, 32 * d⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have hd := hle d h.dw
  simp only [compressEncodeWK, dArg, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2,
    ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), VG.Proof.MlKem.X86_64.sw32_64' d (by omega)]
  refine ⟨trivial, trivial, h.dj, ret_disj s1 (by rw [hsp]; exact h.kF), ret_disj s1 (by rw [hsp]; exact h.kO),
    h.dw, trivial, ?_⟩
  rw [ce_reduced s1 (by rw [hsp]; exact h.kF), hm]; exact h.red

theorem ceCall_ok {n : String} {c : Prog isa} {ws : List Nat} (I : VG.Proof.MlKem.X86_64.CEImpl n c ws) {f out : Ptr} {d : Nat}
    (hout : VG.Proof.MlKem.X86_64.NA out) {s : State} (h : VG.Proof.MlKem.X86_64.CEH ws f out d s) :
    WP isa (ceCall n c f d out) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s out, 32 * d⟩] ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s out) (32 * d) = compressEncode d (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f)) := by
  have hd := I.le d h.dw
  refine WP.mono (glueCall_ok I.correct I.nosp (by rw [I.depth]; decide)
    (VG.Proof.MlKem.X86_64.ceGlue_ok f out d h.off hd hout s) (fun s1 hv hm k => VG.Proof.MlKem.X86_64.cePre I.le h hv hm k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [compressEncodeWK, dArg, State.withRegions_gpr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2, hm₂, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), VG.Proof.MlKem.X86_64.sw32_64' d (by omega),
    ce_polyAt s1 (by rw [hsp]; exact h.kF), hm] at hq
  exact hq

theorem ceCall_tr {n : String} {c : Prog isa} {ws : List Nat} (I : VG.Proof.MlKem.X86_64.CEImpl n c ws) {f out : Ptr} {d : Nat}
    (hout : VG.Proof.MlKem.X86_64.NA out) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.CEH ws f out d x ∧ VG.Proof.MlKem.X86_64.CEH ws f out d y ∧ x.gpr f.1 = y.gpr f.1 ∧ x.gpr out.1 = y.gpr out.1 ∧
      x.gpr .rsp = y.gpr .rsp) (ceCall n c f d out) fun _ _ => True :=
  glueCall_tr I.correct I.ct (V := fun x x1 => ((x1.gpr .rdi = VG.Proof.MlKem.X86_64.pa x f ∧
      x1.gpr .rsi = BitVec.ofNat 64 d ∧ x1.gpr .rdx = VG.Proof.MlKem.X86_64.pa x out ∧ x1.gpr .rcx = BitVec.ofNat 64 (32 * d)) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (VG.Proof.MlKem.X86_64.block_nomem_tr (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.lea_nomem _ _) (VG.Proof.MlKem.X86_64.mov32i_nomem _ _)) (VG.Proof.MlKem.X86_64.lea_nomem _ _))
      (VG.Proof.MlKem.X86_64.mov32i_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.ceGlue_ok f out d hx.off (I.le d hx.dw) hout x,
      VG.Proof.MlKem.X86_64.ceGlue_ok f out d hy.off (I.le d hy.dw) hout y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, hm1⟩, k1⟩ ⟨⟨hv2, hm2⟩, k2⟩ => by
      refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.cePre I.le hx hv1 hm1 k1, VG.Proof.MlKem.X86_64.cePre I.le hy hv2 hm2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [compressEncodeWK, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2, VG.Proof.MlKem.X86_64.pa, e1, e2, k1.gpr (r := .rsp) (by decide),
        k2.gpr (r := .rsp) (by decide), e3, and_self]

/-- What a call of a decompression of the `32d` bytes at `b` to `f`, with `d` in `ws`, needs. -/
structure DDH (ws : List Nat) (b f : Ptr) (d : Nat) (s : State) : Prop where
  off : b.2 < 2 ^ 31 ∧ f.2 < 2 ^ 31
  dw : d ∈ ws
  dj : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s b, 32 * d⟩ (pR (VG.Proof.MlKem.X86_64.pa s f))
  kB : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s b, 32 * d⟩
  kF : (below (s.gpr .rsp) 32).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s f))
  c : Covers ([⟨VG.Proof.MlKem.X86_64.pa s b, 32 * d⟩] ++ [pR (VG.Proof.MlKem.X86_64.pa s f)]) (s.rd ++ s.wr)
  w : Covers [pR (VG.Proof.MlKem.X86_64.pa s f)] s.wr

theorem ddGlue_ok (b f : Ptr) (d : Nat) (ho : b.2 < 2 ^ 31 ∧ f.2 < 2 ^ 31) (hd : d ≤ 11) (hf : VG.Proof.MlKem.X86_64.NA f) (s : State) :
    WP isa (.block (lea .rdi b ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 (32 * d))),
      .mov32 .rdx (.imm (BitVec.ofNat 32 d))] : List Instr) ++ lea .rcx f)) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s b ∧ s1.gpr .rsi = BitVec.ofNat 64 (32 * d) ∧ s1.gpr .rdx = BitVec.ofNat 64 d ∧
        s1.gpr .rcx = VG.Proof.MlKem.X86_64.pa s f) ∧ s1.mem = s.mem) ∧ Keep argRegs s s1 := by
  have o1 : f.1 ≠ .rsi := fun e => hf (by rw [e]; decide)
  have o2 : f.1 ≠ .rdi := fun e => hf (by rw [e]; decide)
  have o3 : f.1 ≠ .rdx := fun e => hf (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho.1, sx_ofNat ho.2, o1, o2, o3, sw_ofNat (show d < 2 ^ 32 by omega),
    sw_ofNat (show 32 * d < 2 ^ 32 by omega), List.cons_append, List.nil_append]

theorem ddPre {ws : List Nat} (hle : ∀ d ∈ ws, d ≤ 11) {b f : Ptr} {d : Nat} {s s1 : State} (h : VG.Proof.MlKem.X86_64.DDH ws b f d s)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s b ∧ s1.gpr .rsi = BitVec.ofNat 64 (32 * d) ∧ s1.gpr .rdx = BitVec.ofNat 64 d ∧
      s1.gpr .rcx = VG.Proof.MlKem.X86_64.pa s f) (k : Keep argRegs s s1) :
    (decodeDecompressWK ws).pre (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s b, 32 * d⟩] [pR (VG.Proof.MlKem.X86_64.pa s f)]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  have hd := hle d h.dw
  simp only [decodeDecompressWK, dArg, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hv.1, hv.2.1, hv.2.2.1, hv.2.2.2,
    ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), VG.Proof.MlKem.X86_64.sw32_64' d (by omega)]
  exact ⟨trivial, trivial, h.dj, ret_disj s1 (by rw [hsp]; exact h.kB), ret_disj s1 (by rw [hsp]; exact h.kF),
    h.dw, trivial⟩

theorem ddCall_ok {n : String} {c : Prog isa} {ws : List Nat} (I : VG.Proof.MlKem.X86_64.DDImpl n c ws) {b f : Ptr} {d : Nat} (hf : VG.Proof.MlKem.X86_64.NA f)
    {s : State} (h : VG.Proof.MlKem.X86_64.DDH ws b f d s) :
    WP isa (ddCall n c b d f) s fun s' => Post s s' [pR (VG.Proof.MlKem.X86_64.pa s f)] ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s f) (decodeDecompress d (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s b) (32 * d))) := by
  have hd := I.le d h.dw
  refine WP.mono (glueCall_ok I.correct I.nosp (by rw [I.depth]; decide)
    (VG.Proof.MlKem.X86_64.ddGlue_ok b f d h.off hd hf s) (fun s1 hv _ k => VG.Proof.MlKem.X86_64.ddPre I.le h hv k) h.c h.w)
    fun s' ⟨hpost, s1, hV, hm, k, s₂, hm₂, _, hq⟩ => ⟨hpost, ?_⟩
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [decodeDecompressWK, dArg, State.withRegions_gpr, State.withRegions_mem,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), ce_gpr' s1 (by decide : Reg.rcx ≠ .rsp), hV.1, hV.2.1, hV.2.2.1,
    hV.2.2.2, hm₂, ofNat_toNat' (show 32 * d < 2 ^ 64 by omega), VG.Proof.MlKem.X86_64.sw32_64' d (by omega),
    ce_bytesAt s1 (n := 32 * d) (by omega) (by rw [hsp]; exact h.kB), hm] at hq
  exact hq

theorem ddCall_tr {n : String} {c : Prog isa} {ws : List Nat} (I : VG.Proof.MlKem.X86_64.DDImpl n c ws) {b f : Ptr} {d : Nat} (hf : VG.Proof.MlKem.X86_64.NA f) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.DDH ws b f d x ∧ VG.Proof.MlKem.X86_64.DDH ws b f d y ∧ x.gpr b.1 = y.gpr b.1 ∧ x.gpr f.1 = y.gpr f.1 ∧
      x.gpr .rsp = y.gpr .rsp) (ddCall n c b d f) fun _ _ => True :=
  glueCall_tr I.correct I.ct (V := fun x x1 => ((x1.gpr .rdi = VG.Proof.MlKem.X86_64.pa x b ∧
      x1.gpr .rsi = BitVec.ofNat 64 (32 * d) ∧ x1.gpr .rdx = BitVec.ofNat 64 d ∧ x1.gpr .rcx = VG.Proof.MlKem.X86_64.pa x f) ∧
      x1.mem = x.mem) ∧ Keep argRegs x x1)
    (VG.Proof.MlKem.X86_64.block_nomem_tr (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.lea_nomem _ _) (fun i hi s => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> rfl)) (VG.Proof.MlKem.X86_64.lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.ddGlue_ok b f d hx.off (I.le d hx.dw) hf x,
      VG.Proof.MlKem.X86_64.ddGlue_ok b f d hy.off (I.le d hy.dw) hf y⟩)
    fun x y x1 y1 ⟨hx, hy, e1, e2, e3⟩ ⟨⟨hv1, _⟩, k1⟩ ⟨⟨hv2, _⟩, k2⟩ => by
      refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.ddPre I.le hx hv1 k1, VG.Proof.MlKem.X86_64.ddPre I.le hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
        by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e3]⟩
      simp only [decodeDecompressWK, State.withRegions_gpr, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
        hv1.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2, VG.Proof.MlKem.X86_64.pa, e1, e2, k1.gpr (r := .rsp) (by decide),
        k2.gpr (r := .rsp) (by decide), e3, and_self]

theorem widths_lt {d : Nat} (h : d ∈ compressWidths) : d ≤ 11 := by
  simp only [compressWidths, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-- `vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress`. -/
theorem ceImpl : VG.Proof.MlKem.X86_64.CEImpl "vg_mlkem_compress_encode" compressEncode compressWidths :=
  ⟨fun _ => VG.Proof.MlKem.X86_64.widths_lt, compressEncode_correct, compressEncode_ct, VG.Proof.MlKem.X86_64.ce_nosp, VG.Proof.MlKem.X86_64.ce_depth⟩

theorem ddImpl : VG.Proof.MlKem.X86_64.DDImpl "vg_mlkem_decode_decompress" decodeDecompress compressWidths :=
  ⟨fun _ => VG.Proof.MlKem.X86_64.widths_lt, decodeDecompress_correct, decodeDecompress_ct, VG.Proof.MlKem.X86_64.dd_nosp, VG.Proof.MlKem.X86_64.dd_depth⟩

/-! ## `SampleNTT` -/

/-- What a call of `vg_mlkem_sample_ntt` of the seed at `SB` to `a` needs. -/
structure SampH (a : Ptr) (s : State) : Prop where
  off : a.2 < 2 ^ 31
  dSA : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc oSB), 34⟩ (pR (VG.Proof.MlKem.X86_64.pa s a))
  dSZ : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc oSB), 34⟩ ⟨VG.Proof.MlKem.X86_64.pa s (sc oSS), 2048⟩
  dAZ : (pR (VG.Proof.MlKem.X86_64.pa s a)).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc oSS), 2048⟩
  kS : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc oSB), 34⟩
  kA : (below (s.gpr .rsp) 32).Disjoint (pR (VG.Proof.MlKem.X86_64.pa s a))
  kZ : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc oSS), 2048⟩
  nw : (VG.Proof.MlKem.X86_64.pa s (sc oSS)).toNat + 2048 ≤ 2 ^ 64
  c : Covers ([⟨VG.Proof.MlKem.X86_64.pa s (sc oSB), 34⟩] ++ [pR (VG.Proof.MlKem.X86_64.pa s a), ⟨VG.Proof.MlKem.X86_64.pa s (sc oSS), 2048⟩]) (s.rd ++ s.wr)
  w : Covers [pR (VG.Proof.MlKem.X86_64.pa s a), ⟨VG.Proof.MlKem.X86_64.pa s (sc oSS), 2048⟩] s.wr

theorem sampGlue_ok (a : Ptr) (ha : a.2 < 2 ^ 31) (hna : VG.Proof.MlKem.X86_64.NA a) (s : State) :
    WP isa (.block (lea .rdi (sc oSB) ++ lea .rsi a ++ lea .rdx (sc oSS))) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s (sc oSB) ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s a ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s (sc oSS)) ∧ s1.mem = s.mem) ∧
        Keep argRegs s s1 := by
  have o1 : a.1 ≠ .rdi := fun e => hna (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ha, sx_ofNat (show oSB < 2 ^ 31 by decide), sx_ofNat (show oSS < 2 ^ 31 by decide), o1,
    List.cons_append, List.nil_append]

theorem sampPre {a : Ptr} {s s1 : State} (h : VG.Proof.MlKem.X86_64.SampH a s)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s (sc oSB) ∧ s1.gpr .rsi = VG.Proof.MlKem.X86_64.pa s a ∧ s1.gpr .rdx = VG.Proof.MlKem.X86_64.pa s (sc oSS))
    (k : Keep argRegs s s1) :
    sampleK.pre (s1.callEntry.withRegions [⟨VG.Proof.MlKem.X86_64.pa s (sc oSB), 34⟩] [pR (VG.Proof.MlKem.X86_64.pa s a), ⟨VG.Proof.MlKem.X86_64.pa s (sc oSS), 2048⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [sampleK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), hv.1, hv.2.1, hv.2.2]
  exact ⟨trivial, trivial, h.dSA, h.dSZ, h.dAZ, ret_disj s1 (by rw [hsp]; exact h.kS),
    ret_disj s1 (by rw [hsp]; exact h.kA), ret_disj s1 (by rw [hsp]; exact h.kZ),
    stk_disj s1 (by rw [hsp]; exact h.kS), stk_disj s1 (by rw [hsp]; exact h.kA),
    stk_disj s1 (by rw [hsp]; exact h.kZ), h.nw⟩

theorem and15_ok (s : State) :
    WP isa (.block [.alu32 .and .r15 (.reg .rax)]) s fun s' =>
      (s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem) ∧
        Keep [.r15] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- What a call of `SampleNTT` leaves. -/
structure SampPost (a : Ptr) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  frame : Frame ([pR (VG.Proof.MlKem.X86_64.pa s a), ⟨VG.Proof.MlKem.X86_64.pa s (sc oSS), 2048⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem
  r15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
    (if (sampleNTT minIterations (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (sc oSB)) 34)).isSome then 1 else 0))
  res : ∀ f, sampleNTT minIterations (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (sc oSB)) 34) = some f → PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s a) f

theorem sampleAt_ok {a : Ptr} (hna : VG.Proof.MlKem.X86_64.NA a) {s : State} (h : VG.Proof.MlKem.X86_64.SampH a s) : WP isa (sampleAt a) s (VG.Proof.MlKem.X86_64.SampPost a s) := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.sampGlue_ok a h.off hna s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine WP.seq (WP.call sample_correct VG.Proof.MlKem.X86_64.sample_nosp (by rw [VG.Proof.MlKem.X86_64.sample_depth]; decide) (VG.Proof.MlKem.X86_64.sampPre h hv k)
    (by rw [k.2.1, k.2.2]; exact h.c) (by rw [k.2.2]; exact h.w) fun s2 hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_)
  refine WP.mono (VG.Proof.MlKem.X86_64.and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  simp only [sampleK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2.1, hm₂, ce_bytesAt s1 (n := 34) (by decide)
    (by rw [hsp]; exact h.kS), hm] at hpost
  rw [hg₂ .rax (by decide)] at hpost
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_, ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm, ← hsp]
    rw [VG.Proof.MlKem.X86_64.sample_depth] at hf
    exact Frame.below_mono hf (by omega) (by omega)
  · rw [h15, hcs .r15 (by decide), k.gpr (by decide), hpost.1]
  · rw [hm3]; exact hpost.2

theorem sampleAt_tr {a : Ptr} (hna : VG.Proof.MlKem.X86_64.NA a) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.SampH a x ∧ VG.Proof.MlKem.X86_64.SampH a y ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr a.1 = y.gpr a.1 ∧
      x.gpr .rsp = y.gpr .rsp ∧ bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (sc oSB)) 34 = bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y (sc oSB)) 34)
      (sampleAt a) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (VG.Proof.MlKem.X86_64.SampH a x ∧ VG.Proof.MlKem.X86_64.SampH a y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr a.1 = y.gpr a.1 ∧ x.gpr .rsp = y.gpr .rsp ∧
      bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (sc oSB)) 34 = bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y (sc oSB)) 34) ∧
      (((x1.gpr .rdi = VG.Proof.MlKem.X86_64.pa x (sc oSB) ∧ x1.gpr .rsi = VG.Proof.MlKem.X86_64.pa x a ∧ x1.gpr .rdx = VG.Proof.MlKem.X86_64.pa x (sc oSS)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = VG.Proof.MlKem.X86_64.pa y (sc oSB) ∧ y1.gpr .rsi = VG.Proof.MlKem.X86_64.pa y a ∧ y1.gpr .rdx = VG.Proof.MlKem.X86_64.pa y (sc oSS)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (VG.Proof.MlKem.X86_64.block_nomem_tr (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.lea_nomem _ _) (VG.Proof.MlKem.X86_64.lea_nomem _ _)) (VG.Proof.MlKem.X86_64.lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.sampGlue_ok a hx.off hna x, VG.Proof.MlKem.X86_64.sampGlue_ok a hy.off hna y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.seq (RelCT.callEx sample_correct sample_ct ?_)
      (VG.Proof.MlKem.X86_64.block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
  rintro x1 y1 ⟨x, y, ⟨hx, hy, e1, e2, e3, e4⟩, ⟨⟨hv1, hm1⟩, k1⟩, ⟨⟨hv2, hm2⟩, k2⟩⟩
  have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
  have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
  refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.sampPre hx hv1 k1, VG.Proof.MlKem.X86_64.sampPre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
    by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
    by rw [hs1, hs2, e3]⟩
  simp only [sampleK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
    ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2]
  rw [ce_bytesAt x1 (n := 34) (by decide) (by rw [hs1]; exact hx.kS),
    ce_bytesAt y1 (n := 34) (by decide) (by rw [hs2]; exact hy.kS), hm1, hm2, e4]
  simp only [VG.Proof.MlKem.X86_64.pa, e1, e2, hs1, hs2, e3, and_self]

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.FragK`. -/
section

/-!
# ML-KEM-768 on x86-64: the calls of the SHA-3 sponge

Zeroing the Keccak state at `scratch` (`kzero_ok`), and the calls of
`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` on it, with the
working space at `scratch + 200` (`kabs_ok`, `kpad_ok`, `ksqz_ok`), and their
traces.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom)

/-! ## Zeroing -/

theorem kzero_ok (s : State) (hw : Covers [⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩] s.wr) :
    WP isa (.block kzero) s fun s' =>
      stateAt s'.mem (VG.Proof.MlKem.X86_64.pa s (sc 0)) = Spec.Sha3.zero ∧ Frame [⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩] s.mem s'.mem ∧
        Keep [.rax] s s' := by
  rw [kzero, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = s.mem ∧ s1.gpr .rax = 0) (by xrun) (by decide))
    fun s1 ⟨⟨hm, hax⟩, k1⟩ => ?_
  have hbx : s1.gpr .rbx = s.gpr .rbx := k1.gpr (by decide)
  refine WP.mono (zeroSt_ok .rbx 0 s1 hax fun i hi => ?_) fun s2 ⟨hz, hf, k2⟩ => ?_
  · rw [k1.2.2, hbx]
    exact hw _ _ ⟨_, List.mem_singleton_self _, contains_offset' (by omega) (by omega)⟩
  · rw [hbx] at hz hf
    exact ⟨hz, by rw [← hm]; exact hf, (k1.trans k2).mono (by decide)⟩

theorem kzero_tr {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .rbx = y.gpr .rbx) :
    RelCT isa P (.block kzero) fun _ _ => True :=
  taintRel [.rbx] (fun x y hp r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h x y hp)
    (by taint_decide)

/-! ## Absorbing -/

/-- What a call of `vg_keccak_absorb` of the `len` bytes at `src` needs. -/
structure KAbsH (src : Ptr) (len rate pos : Nat) (s : State) : Prop where
  hoff : src.2 < 2 ^ 31
  hlen : len < 2 ^ 31
  hrate : rate ∈ rates
  hpos : pos < rate
  st_scr : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩ ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩
  d_st : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s src, len⟩ ⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩
  d_scr : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s src, len⟩ ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩
  k_st : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩
  k_d : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s src, len⟩
  k_scr : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩
  c : Covers ([⟨VG.Proof.MlKem.X86_64.pa s src, len⟩] ++ [⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩, ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩]) (s.rd ++ s.wr)
  w : Covers [⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩, ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩] s.wr

theorem pa_sc0 (s : State) : VG.Proof.MlKem.X86_64.pa s (sc 0) = s.gpr .rbx := BitVec.add_zero _

theorem rate_small {rate : Nat} (h : rate ∈ rates) : rate < 2 ^ 31 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem kabsGlue_ok (src : Ptr) (len rate pos : Nat) (ho : src.2 < 2 ^ 31) (hl : len < 2 ^ 31) (hr : rate < 2 ^ 31)
    (hp : pos < 2 ^ 31) (hs : VG.Proof.MlKem.X86_64.NA src) (s : State) :
    WP isa (.block (lea .rdi (sc 0) ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 rate)),
      .mov32 .rdx (.imm (BitVec.ofNat 32 pos))] : List Instr) ++ lea .rcx src ++
      ([.mov32 .r8 (.imm (BitVec.ofNat 32 len))] : List Instr) ++ lea .r9 (sc 200))) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s (sc 0) ∧ s1.gpr .rsi = BitVec.ofNat 64 rate ∧ s1.gpr .rdx = BitVec.ofNat 64 pos ∧
        s1.gpr .rcx = VG.Proof.MlKem.X86_64.pa s src ∧ s1.gpr .r8 = BitVec.ofNat 64 len ∧ s1.gpr .r9 = VG.Proof.MlKem.X86_64.pa s (sc 200)) ∧ s1.mem = s.mem) ∧
        Keep argRegs s s1 := by
  have o1 : src.1 ≠ .rsi := fun e => hs (by rw [e]; decide)
  have o2 : src.1 ≠ .rdi := fun e => hs (by rw [e]; decide)
  have o3 : src.1 ≠ .rdx := fun e => hs (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho, sx_ofNat (show (0 : Nat) < 2 ^ 31 by decide), sx_ofNat (show (200 : Nat) < 2 ^ 31 by decide),
    o1, o2, o3, sw_ofNat (show rate < 2 ^ 32 by omega), sw_ofNat (show pos < 2 ^ 32 by omega),
    sw_ofNat (show len < 2 ^ 32 by omega), List.cons_append, List.nil_append, VG.Proof.MlKem.X86_64.pa_sc0]

theorem kabsArgs {src : Ptr} {len rate pos : Nat} {s s1 : State} (h : VG.Proof.MlKem.X86_64.KAbsH src len rate pos s)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s (sc 0) ∧ s1.gpr .rsi = BitVec.ofNat 64 rate ∧ s1.gpr .rdx = BitVec.ofNat 64 pos ∧
      s1.gpr .rcx = VG.Proof.MlKem.X86_64.pa s src ∧ s1.gpr .r8 = BitVec.ofNat 64 len ∧ s1.gpr .r9 = VG.Proof.MlKem.X86_64.pa s (sc 200))
    (k : Keep argRegs s s1) : AbsorbArgs s1 (VG.Proof.MlKem.X86_64.pa s (sc 0)) (VG.Proof.MlKem.X86_64.pa s src) (VG.Proof.MlKem.X86_64.pa s (sc 200)) rate pos len := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2, h.hrate, h.hpos, by have := h.hlen; omega,
    h.st_scr, h.d_st, h.d_scr, k16 s1 (by rw [hsp]; exact h.k_st), k16 s1 (by rw [hsp]; exact h.k_d),
    k16 s1 (by rw [hsp]; exact h.k_scr)⟩

theorem kabs_ok {src : Ptr} {len rate pos : Nat} (hs : VG.Proof.MlKem.X86_64.NA src) {s : State} (h : VG.Proof.MlKem.X86_64.KAbsH src len rate pos s) :
    WP isa (kabs src len rate pos) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩, ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩] ∧
      ∀ msg, Spec.Sha3.Repr s.mem (VG.Proof.MlKem.X86_64.pa s (sc 0)) rate msg → pos = msg.length % rate →
        Spec.Sha3.Repr s'.mem (VG.Proof.MlKem.X86_64.pa s (sc 0)) rate (msg ++ bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s src) len) := by
  have hr := VG.Proof.MlKem.X86_64.rate_small h.hrate
  have := h.hpos
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.kabsGlue_ok src len rate pos h.hoff h.hlen hr (by omega) hs s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine absorb_call (VG.Proof.MlKem.X86_64.kabsArgs h hv k) (by rw [k.2.1, k.2.2]; exact h.c) (by rw [k.2.2]; exact h.w)
    fun s' hrd hwr hcs hf hR _ => ⟨⟨hrd.trans k.2.1, hwr.trans k.2.2,
      fun r hr => by rw [hcs r hr, k.gpr (argRegs_cs r hr)], ?_⟩, ?_⟩
  · rw [← hm, ← hsp]; exact Frame.below_mono hf (by omega) (by omega)
  · intro msg hmsg hpos
    rw [← hm] at hmsg ⊢
    exact hR msg hmsg hpos

theorem kabs_tr {src : Ptr} {len rate pos : Nat} (hs : VG.Proof.MlKem.X86_64.NA src) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.KAbsH src len rate pos x ∧ VG.Proof.MlKem.X86_64.KAbsH src len rate pos y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr src.1 = y.gpr src.1 ∧ x.gpr .rsp = y.gpr .rsp) (kabs src len rate pos) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (VG.Proof.MlKem.X86_64.KAbsH src len rate pos x ∧ VG.Proof.MlKem.X86_64.KAbsH src len rate pos y ∧
      x.gpr .rbx = y.gpr .rbx ∧ x.gpr src.1 = y.gpr src.1 ∧ x.gpr .rsp = y.gpr .rsp) ∧
      (((x1.gpr .rdi = VG.Proof.MlKem.X86_64.pa x (sc 0) ∧ x1.gpr .rsi = BitVec.ofNat 64 rate ∧ x1.gpr .rdx = BitVec.ofNat 64 pos ∧
        x1.gpr .rcx = VG.Proof.MlKem.X86_64.pa x src ∧ x1.gpr .r8 = BitVec.ofNat 64 len ∧ x1.gpr .r9 = VG.Proof.MlKem.X86_64.pa x (sc 200)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = VG.Proof.MlKem.X86_64.pa y (sc 0) ∧ y1.gpr .rsi = BitVec.ofNat 64 rate ∧ y1.gpr .rdx = BitVec.ofNat 64 pos ∧
        y1.gpr .rcx = VG.Proof.MlKem.X86_64.pa y src ∧ y1.gpr .r8 = BitVec.ofNat 64 len ∧ y1.gpr .r9 = VG.Proof.MlKem.X86_64.pa y (sc 200)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (VG.Proof.MlKem.X86_64.block_nomem_tr (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.lea_nomem _ _) (fun i hi s => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> rfl)) (VG.Proof.MlKem.X86_64.lea_nomem _ _))
      (VG.Proof.MlKem.X86_64.mov32i_nomem _ _)) (VG.Proof.MlKem.X86_64.lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.kabsGlue_ok src len rate pos hx.hoff hx.hlen (VG.Proof.MlKem.X86_64.rate_small hx.hrate)
      (by have := VG.Proof.MlKem.X86_64.rate_small hx.hrate; have := hx.hpos; omega) hs x,
      VG.Proof.MlKem.X86_64.kabsGlue_ok src len rate pos hy.hoff hy.hlen (VG.Proof.MlKem.X86_64.rate_small hy.hrate)
      (by have := VG.Proof.MlKem.X86_64.rate_small hy.hrate; have := hy.hpos; omega) hs y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Absorb.absorb_correct Proof.Sha3.X86_64.Stream.Absorb.absorb_ct
      fun x1 y1 ⟨x, y, ⟨hx, hy, e1, e2, e3⟩, ⟨⟨hv1, _⟩, k1⟩, ⟨⟨hv2, _⟩, k2⟩⟩ => by
        have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
        have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
        refine ⟨_, _, _, _, absorb_pre (VG.Proof.MlKem.X86_64.kabsArgs hx hv1 k1), absorb_pre (VG.Proof.MlKem.X86_64.kabsArgs hy hv2 k2), ?_,
          by rw [k1.2.1, k1.2.2]; exact hx.c, by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c,
          by rw [k2.2.2]; exact hy.w, by rw [hs1, hs2, e3]⟩
        simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
          ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
          ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp),
          ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), ce_gpr' _ (by decide : Reg.r9 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
          hv1.2.2.2.1, hv1.2.2.2.2.1, hv1.2.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2.1,
          hv2.2.2.2.2.2, VG.Proof.MlKem.X86_64.pa, e1, e2, hs1, hs2, e3, and_self])

/-! ## Padding -/

/-- What a call of `vg_keccak_pad` at position `pos` needs. -/
structure KPadH (rate pos : Nat) (s : State) : Prop where
  hrate : rate ∈ rates
  hpos : pos < rate
  st_scr : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩ ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩
  k_st : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩
  k_scr : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩
  w : Covers [⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩, ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩] s.wr

theorem b8_ofNat64 {v : Nat} (_hv : v < 256) : BitVec.setWidth 8 (BitVec.ofNat 64 v) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem kpadGlue_ok (rate pos suffix : Nat) (hr : rate < 2 ^ 31) (hp : pos < 2 ^ 31) (hs : suffix < 256) (s : State) :
    WP isa (.block (lea .rdi (sc 0) ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 rate)),
      .mov32 .rdx (.imm (BitVec.ofNat 32 pos)), .mov32 .rcx (.imm (BitVec.ofNat 32 suffix))] : List Instr) ++
      lea .r8 (sc 200))) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s (sc 0) ∧ s1.gpr .rsi = BitVec.ofNat 64 rate ∧ s1.gpr .rdx = BitVec.ofNat 64 pos ∧
        s1.gpr .rcx = BitVec.ofNat 64 suffix ∧ s1.gpr .r8 = VG.Proof.MlKem.X86_64.pa s (sc 200)) ∧ s1.mem = s.mem) ∧
        Keep argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat (show (0 : Nat) < 2 ^ 31 by decide), sx_ofNat (show (200 : Nat) < 2 ^ 31 by decide),
    sw_ofNat (show rate < 2 ^ 32 by omega), sw_ofNat (show pos < 2 ^ 32 by omega),
    sw_ofNat (show suffix < 2 ^ 32 by omega), List.cons_append, List.nil_append, VG.Proof.MlKem.X86_64.pa_sc0]

theorem kpadArgs {rate pos suffix : Nat} {s s1 : State} (h : VG.Proof.MlKem.X86_64.KPadH rate pos s)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s (sc 0) ∧ s1.gpr .rsi = BitVec.ofNat 64 rate ∧ s1.gpr .rdx = BitVec.ofNat 64 pos ∧
      s1.gpr .rcx = BitVec.ofNat 64 suffix ∧ s1.gpr .r8 = VG.Proof.MlKem.X86_64.pa s (sc 200))
    (k : Keep argRegs s s1) : PadArgs s1 (VG.Proof.MlKem.X86_64.pa s (sc 0)) (VG.Proof.MlKem.X86_64.pa s (sc 200)) rate pos := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.2, h.hrate, h.hpos, h.st_scr, k16 s1 (by rw [hsp]; exact h.k_st),
    k16 s1 (by rw [hsp]; exact h.k_scr)⟩

theorem kpad_ok {rate pos suffix : Nat} (hs : suffix < 256) {s : State} (h : VG.Proof.MlKem.X86_64.KPadH rate pos s) :
    WP isa (kpad rate pos suffix) s fun s' => Post s s' [⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩, ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩] ∧
      ∀ msg, Spec.Sha3.Repr s.mem (VG.Proof.MlKem.X86_64.pa s (sc 0)) rate msg → pos = msg.length % rate →
        stateAt s'.mem (VG.Proof.MlKem.X86_64.pa s (sc 0)) = absorb rate (pad rate (BitVec.ofNat 8 suffix) msg) := by
  have hr := VG.Proof.MlKem.X86_64.rate_small h.hrate
  have := h.hpos
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.kpadGlue_ok rate pos suffix hr (by omega) hs s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine pad_call (VG.Proof.MlKem.X86_64.kpadArgs h hv k) (VG.Proof.MlKem.X86_64.covers_nil_wr (by rw [k.2.2]; exact h.w)) (by rw [k.2.2]; exact h.w)
    fun s' hrd hwr hcs hf hR => ⟨⟨hrd.trans k.2.1, hwr.trans k.2.2,
      fun r hr => by rw [hcs r hr, k.gpr (argRegs_cs r hr)], ?_⟩, ?_⟩
  · rw [← hm, ← hsp]; exact Frame.below_mono hf (by omega) (by omega)
  · intro msg hmsg hpos
    rw [← hm] at hmsg
    rw [hR msg hmsg hpos, hv.2.2.2.1, VG.Proof.MlKem.X86_64.b8_ofNat64 hs]

theorem kpad_tr {rate pos suffix : Nat} (hs : suffix < 256) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.KPadH rate pos x ∧ VG.Proof.MlKem.X86_64.KPadH rate pos y ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp)
      (kpad rate pos suffix) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (VG.Proof.MlKem.X86_64.KPadH rate pos x ∧ VG.Proof.MlKem.X86_64.KPadH rate pos y ∧
      x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp) ∧
      (((x1.gpr .rdi = VG.Proof.MlKem.X86_64.pa x (sc 0) ∧ x1.gpr .rsi = BitVec.ofNat 64 rate ∧ x1.gpr .rdx = BitVec.ofNat 64 pos ∧
        x1.gpr .rcx = BitVec.ofNat 64 suffix ∧ x1.gpr .r8 = VG.Proof.MlKem.X86_64.pa x (sc 200)) ∧ x1.mem = x.mem) ∧ Keep argRegs x x1) ∧
      (((y1.gpr .rdi = VG.Proof.MlKem.X86_64.pa y (sc 0) ∧ y1.gpr .rsi = BitVec.ofNat 64 rate ∧ y1.gpr .rdx = BitVec.ofNat 64 pos ∧
        y1.gpr .rcx = BitVec.ofNat 64 suffix ∧ y1.gpr .r8 = VG.Proof.MlKem.X86_64.pa y (sc 200)) ∧ y1.mem = y.mem) ∧ Keep argRegs y y1))
    (VG.Proof.MlKem.X86_64.block_nomem_tr (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.lea_nomem _ _) (fun i hi s => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl | rfl <;> rfl))
      (VG.Proof.MlKem.X86_64.lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.kpadGlue_ok rate pos suffix (VG.Proof.MlKem.X86_64.rate_small hx.hrate)
      (by have := VG.Proof.MlKem.X86_64.rate_small hx.hrate; have := hx.hpos; omega) hs x,
      VG.Proof.MlKem.X86_64.kpadGlue_ok rate pos suffix (VG.Proof.MlKem.X86_64.rate_small hy.hrate) (by have := VG.Proof.MlKem.X86_64.rate_small hy.hrate; have := hy.hpos; omega) hs y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Pad.pad_correct Proof.Sha3.X86_64.Stream.Pad.pad_ct
      fun x1 y1 ⟨x, y, ⟨hx, hy, e1, e3⟩, ⟨⟨hv1, _⟩, k1⟩, ⟨⟨hv2, _⟩, k2⟩⟩ => by
        have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
        have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
        refine ⟨_, _, _, _, pad_pre (VG.Proof.MlKem.X86_64.kpadArgs hx hv1 k1), pad_pre (VG.Proof.MlKem.X86_64.kpadArgs hy hv2 k2), ?_,
          VG.Proof.MlKem.X86_64.covers_nil_wr (by rw [k1.2.2]; exact hx.w), by rw [k1.2.2]; exact hx.w,
          VG.Proof.MlKem.X86_64.covers_nil_wr (by rw [k2.2.2]; exact hy.w), by rw [k2.2.2]; exact hy.w, by rw [hs1, hs2, e3]⟩
        simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
          ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
          ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
          hv1.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.2, VG.Proof.MlKem.X86_64.pa, e1, hs1, hs2, e3, and_self])

/-! ## Squeezing -/

/-- What a call of `vg_keccak_squeeze` of `len` bytes to `dst` from position 0 needs. -/
structure KSqzH (dst : Ptr) (len rate : Nat) (s : State) : Prop where
  hoff : dst.2 < 2 ^ 31
  hlen : len < 2 ^ 31
  hrate : rate ∈ rates
  st_out : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩ ⟨VG.Proof.MlKem.X86_64.pa s dst, len⟩
  st_scr : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩ ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩
  out_scr : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s dst, len⟩ ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩
  k_st : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩
  k_out : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s dst, len⟩
  k_scr : (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩
  w : Covers [⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩, ⟨VG.Proof.MlKem.X86_64.pa s dst, len⟩, ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩] s.wr

theorem ksqzGlue_ok (dst : Ptr) (len rate : Nat) (ho : dst.2 < 2 ^ 31) (hl : len < 2 ^ 31) (hr : rate < 2 ^ 31)
    (hs : VG.Proof.MlKem.X86_64.NA dst) (s : State) :
    WP isa (.block (lea .rdi (sc 0) ++ ([.mov32 .rsi (.imm (BitVec.ofNat 32 rate)), .mov32 .rdx (.imm 0)] : List Instr) ++
      lea .rcx dst ++ ([.mov32 .r8 (.imm (BitVec.ofNat 32 len))] : List Instr) ++ lea .r9 (sc 200))) s fun s1 =>
      ((s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s (sc 0) ∧ s1.gpr .rsi = BitVec.ofNat 64 rate ∧ s1.gpr .rdx = BitVec.ofNat 64 0 ∧
        s1.gpr .rcx = VG.Proof.MlKem.X86_64.pa s dst ∧ s1.gpr .r8 = BitVec.ofNat 64 len ∧ s1.gpr .r9 = VG.Proof.MlKem.X86_64.pa s (sc 200)) ∧ s1.mem = s.mem) ∧
        Keep argRegs s s1 := by
  have o1 : dst.1 ≠ .rsi := fun e => hs (by rw [e]; decide)
  have o2 : dst.1 ≠ .rdi := fun e => hs (by rw [e]; decide)
  have o3 : dst.1 ≠ .rdx := fun e => hs (by rw [e]; decide)
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ho, sx_ofNat (show (0 : Nat) < 2 ^ 31 by decide), sx_ofNat (show (200 : Nat) < 2 ^ 31 by decide),
    o1, o2, o3, sw_ofNat (show rate < 2 ^ 32 by omega), sw_ofNat (show (0 : Nat) < 2 ^ 32 by decide),
    sw_ofNat (show len < 2 ^ 32 by omega), List.cons_append, List.nil_append, VG.Proof.MlKem.X86_64.pa_sc0]

theorem ksqzArgs {dst : Ptr} {len rate : Nat} {s s1 : State} (h : VG.Proof.MlKem.X86_64.KSqzH dst len rate s)
    (hv : s1.gpr .rdi = VG.Proof.MlKem.X86_64.pa s (sc 0) ∧ s1.gpr .rsi = BitVec.ofNat 64 rate ∧ s1.gpr .rdx = BitVec.ofNat 64 0 ∧
      s1.gpr .rcx = VG.Proof.MlKem.X86_64.pa s dst ∧ s1.gpr .r8 = BitVec.ofNat 64 len ∧ s1.gpr .r9 = VG.Proof.MlKem.X86_64.pa s (sc 200))
    (k : Keep argRegs s s1) : SqueezeArgs s1 (VG.Proof.MlKem.X86_64.pa s (sc 0)) (VG.Proof.MlKem.X86_64.pa s dst) (VG.Proof.MlKem.X86_64.pa s (sc 200)) rate 0 len := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2.1, hv.2.2.2.2.2, h.hrate, Nat.zero_le _,
    by have := h.hlen; omega, h.st_out, h.st_scr, h.out_scr, k16 s1 (by rw [hsp]; exact h.k_st),
    k16 s1 (by rw [hsp]; exact h.k_out), k16 s1 (by rw [hsp]; exact h.k_scr)⟩

theorem ksqz_ok {dst : Ptr} {len rate : Nat} (hs : VG.Proof.MlKem.X86_64.NA dst) {s : State} (h : VG.Proof.MlKem.X86_64.KSqzH dst len rate s) :
    WP isa (ksqz rate dst len) s fun s' =>
      Post s s' [⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩, ⟨VG.Proof.MlKem.X86_64.pa s dst, len⟩, ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩] ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s dst) len = Spec.Sha3.squeezeFrom rate (stateAt s.mem (VG.Proof.MlKem.X86_64.pa s (sc 0))) 0 len := by
  have hr := VG.Proof.MlKem.X86_64.rate_small h.hrate
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.ksqzGlue_ok dst len rate h.hoff h.hlen hr hs s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine squeeze_call (VG.Proof.MlKem.X86_64.ksqzArgs h hv k) (VG.Proof.MlKem.X86_64.covers_nil_wr (by rw [k.2.2]; exact h.w)) (by rw [k.2.2]; exact h.w)
    fun s' hrd hwr hcs hf ho => ⟨⟨hrd.trans k.2.1, hwr.trans k.2.2,
      fun r hr => by rw [hcs r hr, k.gpr (argRegs_cs r hr)], ?_⟩, ?_⟩
  · rw [← hm, ← hsp]; exact Frame.below_mono hf (by omega) (by omega)
  · rw [ho, hm]

theorem ksqz_tr {dst : Ptr} {len rate : Nat} (hs : VG.Proof.MlKem.X86_64.NA dst) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.KSqzH dst len rate x ∧ VG.Proof.MlKem.X86_64.KSqzH dst len rate y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr dst.1 = y.gpr dst.1 ∧ x.gpr .rsp = y.gpr .rsp) (ksqz rate dst len) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (VG.Proof.MlKem.X86_64.KSqzH dst len rate x ∧ VG.Proof.MlKem.X86_64.KSqzH dst len rate y ∧
      x.gpr .rbx = y.gpr .rbx ∧ x.gpr dst.1 = y.gpr dst.1 ∧ x.gpr .rsp = y.gpr .rsp) ∧
      (((x1.gpr .rdi = VG.Proof.MlKem.X86_64.pa x (sc 0) ∧ x1.gpr .rsi = BitVec.ofNat 64 rate ∧ x1.gpr .rdx = BitVec.ofNat 64 0 ∧
        x1.gpr .rcx = VG.Proof.MlKem.X86_64.pa x dst ∧ x1.gpr .r8 = BitVec.ofNat 64 len ∧ x1.gpr .r9 = VG.Proof.MlKem.X86_64.pa x (sc 200)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = VG.Proof.MlKem.X86_64.pa y (sc 0) ∧ y1.gpr .rsi = BitVec.ofNat 64 rate ∧ y1.gpr .rdx = BitVec.ofNat 64 0 ∧
        y1.gpr .rcx = VG.Proof.MlKem.X86_64.pa y dst ∧ y1.gpr .r8 = BitVec.ofNat 64 len ∧ y1.gpr .r9 = VG.Proof.MlKem.X86_64.pa y (sc 200)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (VG.Proof.MlKem.X86_64.block_nomem_tr (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.nomem_append (VG.Proof.MlKem.X86_64.lea_nomem _ _) (fun i hi s => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> rfl)) (VG.Proof.MlKem.X86_64.lea_nomem _ _))
      (VG.Proof.MlKem.X86_64.mov32i_nomem _ _)) (VG.Proof.MlKem.X86_64.lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.ksqzGlue_ok dst len rate hx.hoff hx.hlen (VG.Proof.MlKem.X86_64.rate_small hx.hrate) hs x,
      VG.Proof.MlKem.X86_64.ksqzGlue_ok dst len rate hy.hoff hy.hlen (VG.Proof.MlKem.X86_64.rate_small hy.hrate) hs y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callEx Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct
      fun x1 y1 ⟨x, y, ⟨hx, hy, e1, e2, e3⟩, ⟨⟨hv1, _⟩, k1⟩, ⟨⟨hv2, _⟩, k2⟩⟩ => by
        have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
        have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
        refine ⟨_, _, _, _, squeeze_pre (VG.Proof.MlKem.X86_64.ksqzArgs hx hv1 k1), squeeze_pre (VG.Proof.MlKem.X86_64.ksqzArgs hy hv2 k2), ?_,
          VG.Proof.MlKem.X86_64.covers_nil_wr (by rw [k1.2.2]; exact hx.w), by rw [k1.2.2]; exact hx.w,
          VG.Proof.MlKem.X86_64.covers_nil_wr (by rw [k2.2.2]; exact hy.w), by rw [k2.2.2]; exact hy.w, by rw [hs1, hs2, e3]⟩
        simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
          ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
          ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), ce_gpr' _ (by decide : Reg.rcx ≠ .rsp),
          ce_gpr' _ (by decide : Reg.r8 ≠ .rsp), ce_gpr' _ (by decide : Reg.r9 ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2.1,
          hv1.2.2.2.1, hv1.2.2.2.2.1, hv1.2.2.2.2.2, hv2.1, hv2.2.1, hv2.2.2.1, hv2.2.2.2.1, hv2.2.2.2.2.1,
          hv2.2.2.2.2.2, VG.Proof.MlKem.X86_64.pa, e1, e2, hs1, hs2, e3, and_self])

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.Lay`. -/
section

/-!
# ML-KEM-768 on x86-64: the buffers of the top-level functions

The top-level functions keep the address of each buffer they work in (their
arguments and their working space) in a callee-saved register; a layout
(`Lay`) lists these registers with the lengths of their buffers, which are
apart from each other and from the stack. A pointer (a register and an offset)
into a buffer, and two pointers into the same buffer or different ones, are
then checked by evaluation (`inB`, `sepB`): each pair of regions a call needs
apart is, and each region is readable or writable (`Lay.disj`, `Lay.stk`,
`Lay.cR`, `Lay.cW`). A call leaves the layout as it was (`Lay.post`), and the
bytes of a region apart from those it writes (`Lay.keepBytes`,
`Lay.keepPoly`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Checks -/

/-- The `len` bytes at `p` lie within the buffer of its register in the layout `bs`. -/
def inB (bs : List (Reg × Nat)) (p : Ptr) (len : Nat) : Bool :=
  match bs.lookup p.1 with
  | some n => decide (p.2 + len ≤ n)
  | none => false

/-- The registers of the buffers the top-level functions write (`scratch`
and the outputs): a buffer they only read may overlap another such
buffer, but not one of these. -/
abbrev wRegs : List Reg := [.rbx, .r12, .r13]

/-- The `l` bytes at `p` and the `k` bytes at `q` lie within their buffers,
apart: in different buffers, one of them written, or in the same buffer. -/
def sepB (bs : List (Reg × Nat)) (p : Ptr) (l : Nat) (q : Ptr) (k : Nat) : Bool :=
  VG.Proof.MlKem.X86_64.inB bs p l && VG.Proof.MlKem.X86_64.inB bs q k &&
    ((p.1 != q.1 && (decide (p.1 ∈ VG.Proof.MlKem.X86_64.wRegs) || decide (q.1 ∈ VG.Proof.MlKem.X86_64.wRegs))) ||
      (p.1 == q.1 && (decide (p.2 + l ≤ q.2) || decide (q.2 + k ≤ p.2))))

theorem lookup_mem : ∀ {bs : List (Reg × Nat)} {r : Reg} {n : Nat}, bs.lookup r = some n → (r, n) ∈ bs
  | [], _, _, h => by simp [List.lookup] at h
  | (r', n') :: bs, r, n, h => by
    unfold List.lookup at h
    by_cases e : r = r'
    · subst e
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · have : (r == r') = false := by simp [e]
      rw [this] at h
      exact List.mem_cons_of_mem _ (VG.Proof.MlKem.X86_64.lookup_mem h)

theorem inB_spec {bs : List (Reg × Nat)} {p : Ptr} {l : Nat} (h : VG.Proof.MlKem.X86_64.inB bs p l = true) :
    ∃ n, (p.1, n) ∈ bs ∧ p.2 + l ≤ n := by
  unfold VG.Proof.MlKem.X86_64.inB at h
  split at h
  · rename_i n hn; exact ⟨n, VG.Proof.MlKem.X86_64.lookup_mem hn, of_decide_eq_true h⟩
  · cases h

theorem sepB_spec {bs : List (Reg × Nat)} {p q : Ptr} {l k : Nat} (h : VG.Proof.MlKem.X86_64.sepB bs p l q k = true) :
    VG.Proof.MlKem.X86_64.inB bs p l = true ∧ VG.Proof.MlKem.X86_64.inB bs q k = true ∧
      ((p.1 ≠ q.1 ∧ (p.1 ∈ VG.Proof.MlKem.X86_64.wRegs ∨ q.1 ∈ VG.Proof.MlKem.X86_64.wRegs)) ∨ (p.1 = q.1 ∧ (p.2 + l ≤ q.2 ∨ q.2 + k ≤ p.2))) := by
  simp only [VG.Proof.MlKem.X86_64.sepB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1 |> fun h1 => ⟨h1, h.1.2, h.2⟩

/-! ## Regions -/

theorem inRegions_sub {X : List Region} {a : Addr} {n off l : Nat} (h : InRegions X a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : InRegions X (a + BitVec.ofNat 64 off) l := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  rw [show a + BitVec.ofNat 64 off - r.base = (a - r.base) + BitVec.ofNat 64 off by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]
  have := Nat.mod_le ((a - r.base).toNat + off) (2 ^ 64)
  omega

theorem covers_one {X : List Region} {a : Addr} {l : Nat} (h : InRegions X a l) : Covers [⟨a, l⟩] X := by
  intro a' n' ⟨r0, hr0, hc⟩
  simp only [List.mem_singleton] at hr0
  subst hr0
  obtain ⟨r, hr, hc'⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc hc' ⊢
  rw [show a' - r.base = (a' - a) + (a - r.base) by bv_omega, BitVec.toNat_add]
  have := Nat.mod_le ((a' - a).toNat + (a - r.base).toNat) (2 ^ 64)
  omega

theorem covers_nil {X : List Region} : Covers [] X := fun _ _ ⟨_, h, _⟩ => absurd h List.not_mem_nil

theorem covers_cons {r : Region} {rs X : List Region} (h : Covers [r] X) (h' : Covers rs X) :
    Covers (r :: rs) X := by
  intro a n ⟨r0, hr0, hc⟩
  rcases List.mem_cons.mp hr0 with rfl | hr0
  · exact h a n ⟨r0, List.mem_singleton_self _, hc⟩
  · exact h' a n ⟨r0, hr0, hc⟩

theorem covers_append {rs ts X : List Region} (h : Covers rs X) (h' : Covers ts X) : Covers (rs ++ ts) X := by
  intro a n ⟨r0, hr0, hc⟩
  rcases List.mem_append.mp hr0 with hr0 | hr0
  · exact h a n ⟨r0, hr0, hc⟩
  · exact h' a n ⟨r0, hr0, hc⟩

/-! ## Layouts -/

/-- The buffers of `rbs` (read) and `wbs` (written), at the addresses in
their registers: small, apart from each other and from the stack, not
wrapping around, and permitted. -/
structure Lay (rbs wbs : List (Reg × Nat)) (s : State) : Prop where
  small : ∀ b ∈ rbs ++ wbs, b.2 < 2 ^ 32
  dj : ∀ b ∈ rbs ++ wbs, ∀ b' ∈ rbs ++ wbs, b.1 ≠ b'.1 → (b.1 ∈ VG.Proof.MlKem.X86_64.wRegs ∨ b'.1 ∈ VG.Proof.MlKem.X86_64.wRegs) →
    Region.Disjoint ⟨s.gpr b.1, b.2⟩ ⟨s.gpr b'.1, b'.2⟩
  stk : ∀ b ∈ rbs ++ wbs, (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr b.1, b.2⟩
  nw : ∀ b ∈ rbs ++ wbs, (s.gpr b.1).toNat + b.2 ≤ 2 ^ 64
  rd : ∀ b ∈ rbs ++ wbs, InRegions (s.rd ++ s.wr) (s.gpr b.1) b.2
  wr : ∀ b ∈ wbs, InRegions s.wr (s.gpr b.1) b.2
  ret : ∀ b ∈ rbs ++ wbs, (retR s).Disjoint ⟨s.gpr b.1, b.2⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s)
include L

theorem Lay.sub {p : Ptr} {l : Nat} (h : VG.Proof.MlKem.X86_64.inB (rbs ++ wbs) p l = true) :
    ∃ n, (p.1, n) ∈ rbs ++ wbs ∧ Region.Sub ⟨VG.Proof.MlKem.X86_64.pa s p, l⟩ ⟨s.gpr p.1, n⟩ := by
  obtain ⟨n, hm, hl⟩ := VG.Proof.MlKem.X86_64.inB_spec h
  exact ⟨n, hm, sub_offset' hl (by have := L.small _ hm; omega)⟩

theorem Lay.disj {p q : Ptr} {l k : Nat} (h : VG.Proof.MlKem.X86_64.sepB (rbs ++ wbs) p l q k = true) :
    Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s p, l⟩ ⟨VG.Proof.MlKem.X86_64.pa s q, k⟩ := by
  obtain ⟨hp, hq, hs⟩ := VG.Proof.MlKem.X86_64.sepB_spec h
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlKem.X86_64.inB_spec hp
  obtain ⟨m, hm, hk⟩ := VG.Proof.MlKem.X86_64.inB_spec hq
  have sn := L.small _ hn
  have sm := L.small _ hm
  rcases hs with ⟨e, hw⟩ | ⟨e, hs⟩
  · exact ((L.dj _ hn _ hm e hw).sub_left (sub_offset' hl (by omega))).sub_right (sub_offset' hk (by omega))
  · show Region.Disjoint ⟨s.gpr p.1 + _, l⟩ ⟨s.gpr q.1 + _, k⟩
    rw [← e]
    rcases hs with h1 | h2
    · exact off_disj h1 (by omega)
    · exact (off_disj h2 (by omega)).symm

theorem Lay.stkD {p : Ptr} {l : Nat} (h : VG.Proof.MlKem.X86_64.inB (rbs ++ wbs) p l = true) :
    (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := L.sub h
  exact (L.stk _ hn).sub_right hsub

theorem Lay.nwp {p : Ptr} {l : Nat} (h : VG.Proof.MlKem.X86_64.inB (rbs ++ wbs) p l = true) : (VG.Proof.MlKem.X86_64.pa s p).toNat + l ≤ 2 ^ 64 := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlKem.X86_64.inB_spec h
  have h1 := L.nw _ hn
  have h2 := L.small _ hn
  simp only at h1 h2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.2) (by omega)]
  have := Nat.mod_le ((s.gpr p.1).toNat + p.2) (2 ^ 64)
  omega

theorem Lay.cR {p : Ptr} {l : Nat} (h : VG.Proof.MlKem.X86_64.inB (rbs ++ wbs) p l = true) : Covers [⟨VG.Proof.MlKem.X86_64.pa s p, l⟩] (s.rd ++ s.wr) := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlKem.X86_64.inB_spec h
  exact VG.Proof.MlKem.X86_64.covers_one (VG.Proof.MlKem.X86_64.inRegions_sub (L.rd (p.1, n) hn) hl (by have := L.small _ hn; omega))

theorem Lay.cW {p : Ptr} {l : Nat} (h : VG.Proof.MlKem.X86_64.inB wbs p l = true) : Covers [⟨VG.Proof.MlKem.X86_64.pa s p, l⟩] s.wr := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlKem.X86_64.inB_spec h
  exact VG.Proof.MlKem.X86_64.covers_one (VG.Proof.MlKem.X86_64.inRegions_sub (L.wr (p.1, n) hn) hl (by have := L.small _ (List.mem_append_right _ hn); omega))

end

/-! ## What a call leaves -/

/-- The region of `w.2` bytes at the pointer `w.1`. -/
abbrev toR (s : State) (w : Ptr × Nat) : Region := ⟨VG.Proof.MlKem.X86_64.pa s w.1, w.2⟩

/-- `Post`, with the regions written given as pointers. -/
abbrev PPost (s s' : State) (ws : List (Ptr × Nat)) : Prop := Post s s' (ws.map (VG.Proof.MlKem.X86_64.toR s))

/-- The registers the top-level functions keep the addresses of their buffers in. -/
abbrev bases : List Reg := [.rbx, .rbp, .r12, .r13, .r14]

/-- What a piece of code leaves: the permissions, the registers `bases` and
the stack pointer, and memory but within `W` and the stack. (A call keeps
every callee-saved register, `Post`; a call of `SampleNTT` changes `r15`.) -/
structure PostB (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bs : ∀ r ∈ VG.Proof.MlKem.X86_64.bases, s'.gpr r = s.gpr r
  rsp : s'.gpr .rsp = s.gpr .rsp
  frame : Frame (W ++ [below (s.gpr .rsp) 32]) s.mem s'.mem

theorem Post.b {s s' : State} {W : List Region} (h : Post s s' W) : VG.Proof.MlKem.X86_64.PostB s s' W :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
    simp only [VG.Proof.MlKem.X86_64.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), h.rsp, h.frame⟩

/-- `PostB`, with the regions written given as pointers. -/
abbrev PPostB (s s' : State) (ws : List (Ptr × Nat)) : Prop := VG.Proof.MlKem.X86_64.PostB s s' (ws.map (VG.Proof.MlKem.X86_64.toR s))

/-- The `l` bytes at `p` lie in the layout, apart from the regions `ws`, and
`p`'s register is one of `bases`. -/
def keepB (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (p : Ptr) (l : Nat) : Bool :=
  decide (p.1 ∈ VG.Proof.MlKem.X86_64.bases) && VG.Proof.MlKem.X86_64.inB bs p l && ws.all fun w => VG.Proof.MlKem.X86_64.sepB bs p l w.1 w.2

theorem Post.pa {s s' : State} {W : List Region} (hP : Post s s' W) {p : Ptr} (h : p.1 ∈ calleeSaved) :
    VG.Proof.MlKem.X86_64.pa s' p = VG.Proof.MlKem.X86_64.pa s p := by
  simp only [VG.Proof.MlKem.X86_64.pa, hP.cs _ h]

theorem PostB.pa {s s' : State} {W : List Region} (hP : VG.Proof.MlKem.X86_64.PostB s s' W) {p : Ptr} (h : p.1 ∈ VG.Proof.MlKem.X86_64.bases) :
    VG.Proof.MlKem.X86_64.pa s' p = VG.Proof.MlKem.X86_64.pa s p := by
  simp only [VG.Proof.MlKem.X86_64.pa, hP.bs _ h]

theorem Lay.post {rbs wbs : List (Reg × Nat)} {s s' : State} {W : List Region} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s)
    (hP : VG.Proof.MlKem.X86_64.PostB s s' W) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) : VG.Proof.MlKem.X86_64.Lay rbs wbs s' := by
  have e : ∀ b ∈ rbs ++ wbs, s'.gpr b.1 = s.gpr b.1 := fun b hb => hP.bs _ (hcs b hb)
  refine ⟨L.small, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_⟩
  · rw [e b hb, e b' hb']; exact L.dj b hb b' hb' hne hw
  · rw [e b hb, hP.rsp]; exact L.stk b hb
  · rw [e b hb]; exact L.nw b hb
  · rw [e b hb, hP.rd, hP.wr]; exact L.rd b hb
  · rw [e b (List.mem_append_right _ hb), hP.wr]; exact L.wr b hb
  · simp only [retR, e b hb, hP.rsp]; exact L.ret b hb

section
variable {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {ws : List (Ptr × Nat)}
  {p : Ptr} {l : Nat}
include L

theorem Lay.fdisj (hc : VG.Proof.MlKem.X86_64.keepB (rbs ++ wbs) ws p l = true) :
    ∀ r ∈ ws.map (VG.Proof.MlKem.X86_64.toR s) ++ [below (s.gpr .rsp) 32], Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s p, l⟩ r := by
  simp only [VG.Proof.MlKem.X86_64.keepB, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨_, hin⟩, hall⟩ := hc
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact L.disj (hall w hw)
  · rw [List.mem_singleton] at hr
    subst hr
    exact (L.stkD hin).symm

omit L in
theorem keepB_cs (hc : VG.Proof.MlKem.X86_64.keepB (rbs ++ wbs) ws p l = true) : p.1 ∈ VG.Proof.MlKem.X86_64.bases := by
  simp only [VG.Proof.MlKem.X86_64.keepB, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1.1

theorem Lay.keepBytes (hP : VG.Proof.MlKem.X86_64.PPostB s s' ws) (hc : VG.Proof.MlKem.X86_64.keepB (rbs ++ wbs) ws p l = true) :
    bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s' p) l = bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s p) l := by
  rw [hP.pa (VG.Proof.MlKem.X86_64.keepB_cs hc)]
  have hin : VG.Proof.MlKem.X86_64.inB (rbs ++ wbs) p l = true := by
    simp only [VG.Proof.MlKem.X86_64.keepB, Bool.and_eq_true] at hc; exact hc.1.2
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlKem.X86_64.inB_spec hin
  exact bytesAt_frame hP.frame (L.fdisj hc) (by have := L.small _ hn; omega)

theorem Lay.keepPoly {f : Poly} (hP : VG.Proof.MlKem.X86_64.PPostB s s' ws) (hc : VG.Proof.MlKem.X86_64.keepB (rbs ++ wbs) ws p 1024 = true)
    (h : PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s p) f) : PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s' p) f := by
  rw [hP.pa (VG.Proof.MlKem.X86_64.keepB_cs hc)]
  exact polyIs_frame hP.frame (L.fdisj hc) h

theorem Lay.keepRed (hP : VG.Proof.MlKem.X86_64.PPostB s s' ws) (hc : VG.Proof.MlKem.X86_64.keepB (rbs ++ wbs) ws p 1024 = true)
    (h : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s p)) : Reduced s'.mem (VG.Proof.MlKem.X86_64.pa s' p) := by
  rw [hP.pa (VG.Proof.MlKem.X86_64.keepB_cs hc)]
  exact reduced_frame hP.frame (L.fdisj hc) h

theorem Lay.keepW (hP : VG.Proof.MlKem.X86_64.PPostB s s' ws) (hc : VG.Proof.MlKem.X86_64.keepB (rbs ++ wbs) ws p 8 = true) :
    s'.mem.readW (VG.Proof.MlKem.X86_64.pa s' p) 64 = s.mem.readW (VG.Proof.MlKem.X86_64.pa s p) 64 := by
  rw [hP.pa (VG.Proof.MlKem.X86_64.keepB_cs hc)]
  exact hP.frame.readW (Region.contains_self _ _) (L.fdisj hc) (by decide)

end

theorem ret_below32 (sp : Addr) : Region.Disjoint ⟨sp, 8⟩ (below sp 32) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

/-- The return address is kept by code that writes within the layout and the stack. -/
theorem Lay.keepRet {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {ws : List (Ptr × Nat)}
    (hP : VG.Proof.MlKem.X86_64.PPostB s s' ws) (hin : ∀ w ∈ ws, VG.Proof.MlKem.X86_64.inB (rbs ++ wbs) w.1 w.2 = true) :
    s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  refine hP.frame.readW (r := retR s) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    obtain ⟨n, hn, hsub⟩ := L.sub (hin w hw)
    exact (L.ret _ hn).sub_right hsub
  · rw [List.mem_singleton] at hr; subst hr
    exact VG.Proof.MlKem.X86_64.ret_below32 _

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.FragOf`. -/
section

/-!
# ML-KEM-768 on x86-64: the calls, in a layout

What each call of the top-level functions needs (`IpH`, `MulH`, …) from a
layout (`Lay`) and a check of its pointers that evaluates to `true` (`ipChk`,
`mulChk`, …), and two runs in the same layout (`LRel`), with the same
addresses in its registers, which every call keeps.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt rates)

/-! ## Checks -/

/-- A pointer an argument is moved from: its offset fits an immediate, and its bytes are readable. -/
def rdOk (bs : List (Reg × Nat)) (p : Ptr) (l : Nat) : Bool := decide (p.2 < 2 ^ 31) && VG.Proof.MlKem.X86_64.inB bs p l

/-- A pointer to bytes that a call writes. -/
def wrOk (bs wbs : List (Reg × Nat)) (p : Ptr) (l : Nat) : Bool := VG.Proof.MlKem.X86_64.rdOk bs p l && VG.Proof.MlKem.X86_64.inB wbs p l

def ipChk (bs wbs : List (Reg × Nat)) (f : Ptr) : Bool :=
  VG.Proof.MlKem.X86_64.wrOk bs wbs f 1024 && VG.Proof.MlKem.X86_64.wrOk bs wbs (sc oSS) 1024 && VG.Proof.MlKem.X86_64.sepB bs f 1024 (sc oSS) 1024

def accChk (bs wbs : List (Reg × Nat)) (f g : Ptr) : Bool :=
  VG.Proof.MlKem.X86_64.wrOk bs wbs f 1024 && VG.Proof.MlKem.X86_64.rdOk bs g 1024 && VG.Proof.MlKem.X86_64.sepB bs f 1024 g 1024

def mulChk (bs wbs : List (Reg × Nat)) (h f g : Ptr) : Bool :=
  VG.Proof.MlKem.X86_64.wrOk bs wbs h 1024 && VG.Proof.MlKem.X86_64.rdOk bs f 1024 && VG.Proof.MlKem.X86_64.rdOk bs g 1024 && VG.Proof.MlKem.X86_64.wrOk bs wbs (sc oSS) 1024 &&
    VG.Proof.MlKem.X86_64.sepB bs h 1024 f 1024 && VG.Proof.MlKem.X86_64.sepB bs h 1024 g 1024 && VG.Proof.MlKem.X86_64.sepB bs h 1024 (sc oSS) 1024 &&
    VG.Proof.MlKem.X86_64.sepB bs f 1024 (sc oSS) 1024 && VG.Proof.MlKem.X86_64.sepB bs g 1024 (sc oSS) 1024

def twoChk (bs wbs : List (Reg × Nat)) (p : Ptr) (n : Nat) (q : Ptr) (m : Nat) : Bool :=
  VG.Proof.MlKem.X86_64.rdOk bs p n && VG.Proof.MlKem.X86_64.wrOk bs wbs q m && VG.Proof.MlKem.X86_64.sepB bs p n q m

def sampChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  VG.Proof.MlKem.X86_64.rdOk bs (sc oSB) 34 && VG.Proof.MlKem.X86_64.wrOk bs wbs a 1024 && VG.Proof.MlKem.X86_64.wrOk bs wbs (sc oSS) 2048 && VG.Proof.MlKem.X86_64.sepB bs (sc oSB) 34 a 1024 &&
    VG.Proof.MlKem.X86_64.sepB bs (sc oSB) 34 (sc oSS) 2048 && VG.Proof.MlKem.X86_64.sepB bs a 1024 (sc oSS) 2048

/-- The Keccak state and the sponge functions' working space. -/
def kChk (bs wbs : List (Reg × Nat)) : Bool :=
  VG.Proof.MlKem.X86_64.wrOk bs wbs (sc 0) 200 && VG.Proof.MlKem.X86_64.wrOk bs wbs (sc 200) 640 && VG.Proof.MlKem.X86_64.sepB bs (sc 0) 200 (sc 200) 640

def kabsChk (bs wbs : List (Reg × Nat)) (src : Ptr) (len : Nat) : Bool :=
  VG.Proof.MlKem.X86_64.kChk bs wbs && VG.Proof.MlKem.X86_64.rdOk bs src len && decide (len < 2 ^ 31) && VG.Proof.MlKem.X86_64.sepB bs src len (sc 0) 200 &&
    VG.Proof.MlKem.X86_64.sepB bs src len (sc 200) 640

def ksqzChk (bs wbs : List (Reg × Nat)) (dst : Ptr) (len : Nat) : Bool :=
  VG.Proof.MlKem.X86_64.kChk bs wbs && VG.Proof.MlKem.X86_64.wrOk bs wbs dst len && decide (len < 2 ^ 31) && VG.Proof.MlKem.X86_64.sepB bs (sc 0) 200 dst len &&
    VG.Proof.MlKem.X86_64.sepB bs dst len (sc 200) 640

/-! ## What the calls need -/

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s)
include L

theorem IpH.of {f : Ptr} (hc : VG.Proof.MlKem.X86_64.ipChk (rbs ++ wbs) wbs f = true) (red : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) : VG.Proof.MlKem.X86_64.IpH f s := by
  simp only [VG.Proof.MlKem.X86_64.ipChk, VG.Proof.MlKem.X86_64.wrOk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨ho, hr⟩, hw⟩, ⟨_, hr2⟩, hw2⟩, hs⟩ := hc
  exact ⟨ho, red, L.disj hs, L.stkD hr, L.stkD hr2, VG.Proof.MlKem.X86_64.covers_cons (L.cW hw) (VG.Proof.MlKem.X86_64.covers_cons (L.cW hw2) VG.Proof.MlKem.X86_64.covers_nil)⟩

theorem AccH.of {f g : Ptr} (hc : VG.Proof.MlKem.X86_64.accChk (rbs ++ wbs) wbs f g = true) (redF : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f))
    (redG : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g)) : VG.Proof.MlKem.X86_64.AccH f g s := by
  simp only [VG.Proof.MlKem.X86_64.accChk, VG.Proof.MlKem.X86_64.wrOk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨ho, hr⟩, hw⟩, ho2, hr2⟩, hs⟩ := hc
  exact ⟨⟨ho, ho2⟩, redF, redG, L.disj hs, L.stkD hr, L.stkD hr2,
    VG.Proof.MlKem.X86_64.covers_append (VG.Proof.MlKem.X86_64.covers_cons (L.cR hr2) VG.Proof.MlKem.X86_64.covers_nil) (VG.Proof.MlKem.X86_64.covers_cons (L.cR hr) VG.Proof.MlKem.X86_64.covers_nil),
    VG.Proof.MlKem.X86_64.covers_cons (L.cW hw) VG.Proof.MlKem.X86_64.covers_nil⟩

theorem MulH.of {h f g : Ptr} (hc : VG.Proof.MlKem.X86_64.mulChk (rbs ++ wbs) wbs h f g = true) (redF : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f))
    (redG : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g)) : VG.Proof.MlKem.X86_64.MulH h f g s := by
  simp only [VG.Proof.MlKem.X86_64.mulChk, VG.Proof.MlKem.X86_64.wrOk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hoh, hrh⟩, hwh⟩, hof, hrf⟩, hog, hrg⟩, ⟨_, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩, s4⟩, s5⟩ := hc
  exact ⟨⟨hoh, hof, hog⟩, redF, redG, L.disj s1, L.disj s2, L.disj s3, L.disj s4, L.disj s5, L.stkD hrh,
    L.stkD hrf, L.stkD hrg, L.stkD hrz,
    VG.Proof.MlKem.X86_64.covers_append (VG.Proof.MlKem.X86_64.covers_cons (L.cR hrf) (VG.Proof.MlKem.X86_64.covers_cons (L.cR hrg) VG.Proof.MlKem.X86_64.covers_nil))
      (VG.Proof.MlKem.X86_64.covers_cons (L.cR hrh) (VG.Proof.MlKem.X86_64.covers_cons (L.cR hrz) VG.Proof.MlKem.X86_64.covers_nil)),
    VG.Proof.MlKem.X86_64.covers_cons (L.cW hwh) (VG.Proof.MlKem.X86_64.covers_cons (L.cW hwz) VG.Proof.MlKem.X86_64.covers_nil)⟩

theorem TwoH.of {p q : Ptr} {n m : Nat} (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs p n q m = true) : VG.Proof.MlKem.X86_64.TwoH p q n m s := by
  simp only [VG.Proof.MlKem.X86_64.twoChk, VG.Proof.MlKem.X86_64.wrOk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hop, hrp⟩, ⟨hoq, hrq⟩, hwq⟩, hs⟩ := hc
  exact ⟨⟨hop, hoq⟩, L.disj hs, L.stkD hrp, L.stkD hrq,
    VG.Proof.MlKem.X86_64.covers_append (VG.Proof.MlKem.X86_64.covers_cons (L.cR hrp) VG.Proof.MlKem.X86_64.covers_nil) (VG.Proof.MlKem.X86_64.covers_cons (L.cR hrq) VG.Proof.MlKem.X86_64.covers_nil),
    VG.Proof.MlKem.X86_64.covers_cons (L.cW hwq) VG.Proof.MlKem.X86_64.covers_nil⟩

theorem CEH.of {ws : List Nat} {f out : Ptr} {d : Nat} (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs f 1024 out (32 * d) = true)
    (hd : d ∈ ws) (red : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) : VG.Proof.MlKem.X86_64.CEH ws f out d s :=
  have h := TwoH.of L hc
  ⟨h.off, hd, red, h.d, h.kP, h.kQ, h.c, h.w⟩

theorem DDH.of {ws : List Nat} {b f : Ptr} {d : Nat} (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs b (32 * d) f 1024 = true)
    (hd : d ∈ ws) : VG.Proof.MlKem.X86_64.DDH ws b f d s :=
  have h := TwoH.of L hc
  ⟨h.off, hd, h.d, h.kP, h.kQ, h.c, h.w⟩

theorem SampH.of {a : Ptr} (hc : VG.Proof.MlKem.X86_64.sampChk (rbs ++ wbs) wbs a = true) : VG.Proof.MlKem.X86_64.SampH a s := by
  simp only [VG.Proof.MlKem.X86_64.sampChk, VG.Proof.MlKem.X86_64.wrOk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨_, hrs⟩, ⟨hoa, hra⟩, hwa⟩, ⟨_, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩ := hc
  exact ⟨hoa, L.disj s1, L.disj s2, L.disj s3, L.stkD hrs, L.stkD hra, L.stkD hrz, L.nwp hrz,
    VG.Proof.MlKem.X86_64.covers_append (VG.Proof.MlKem.X86_64.covers_cons (L.cR hrs) VG.Proof.MlKem.X86_64.covers_nil) (VG.Proof.MlKem.X86_64.covers_cons (L.cR hra) (VG.Proof.MlKem.X86_64.covers_cons (L.cR hrz) VG.Proof.MlKem.X86_64.covers_nil)),
    VG.Proof.MlKem.X86_64.covers_cons (L.cW hwa) (VG.Proof.MlKem.X86_64.covers_cons (L.cW hwz) VG.Proof.MlKem.X86_64.covers_nil)⟩

theorem kChk_spec (hc : VG.Proof.MlKem.X86_64.kChk (rbs ++ wbs) wbs = true) :
    Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩ ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩ ∧
    Covers [⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩] (s.rd ++ s.wr) ∧ Covers [⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩] (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩] s.wr ∧ Covers [⟨VG.Proof.MlKem.X86_64.pa s (sc 200), 640⟩] s.wr := by
  simp only [VG.Proof.MlKem.X86_64.kChk, VG.Proof.MlKem.X86_64.wrOk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨_, h1⟩, w1⟩, ⟨_, h2⟩, w2⟩, hs⟩ := hc
  exact ⟨L.disj hs, L.stkD h1, L.stkD h2, L.cR h1, L.cR h2, L.cW w1, L.cW w2⟩

theorem KAbsH.of {src : Ptr} {len rate pos : Nat} (hc : VG.Proof.MlKem.X86_64.kabsChk (rbs ++ wbs) wbs src len = true)
    (hrate : rate ∈ rates) (hpos : pos < rate) : VG.Proof.MlKem.X86_64.KAbsH src len rate pos s := by
  simp only [VG.Proof.MlKem.X86_64.kabsChk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hk, ho, hr⟩, hl⟩, s1⟩, s2⟩ := hc
  obtain ⟨d0, k0, k1, c0, c1, w0, w1⟩ := VG.Proof.MlKem.X86_64.kChk_spec L hk
  exact ⟨ho, hl, hrate, hpos, d0, L.disj s1, L.disj s2, k0, L.stkD hr, k1,
    VG.Proof.MlKem.X86_64.covers_append (VG.Proof.MlKem.X86_64.covers_cons (L.cR hr) VG.Proof.MlKem.X86_64.covers_nil) (VG.Proof.MlKem.X86_64.covers_cons c0 (VG.Proof.MlKem.X86_64.covers_cons c1 VG.Proof.MlKem.X86_64.covers_nil)),
    VG.Proof.MlKem.X86_64.covers_cons w0 (VG.Proof.MlKem.X86_64.covers_cons w1 VG.Proof.MlKem.X86_64.covers_nil)⟩

theorem KPadH.of {rate pos : Nat} (hc : VG.Proof.MlKem.X86_64.kChk (rbs ++ wbs) wbs = true) (hrate : rate ∈ rates) (hpos : pos < rate) :
    VG.Proof.MlKem.X86_64.KPadH rate pos s := by
  obtain ⟨d0, k0, k1, _, _, w0, w1⟩ := VG.Proof.MlKem.X86_64.kChk_spec L hc
  exact ⟨hrate, hpos, d0, k0, k1, VG.Proof.MlKem.X86_64.covers_cons w0 (VG.Proof.MlKem.X86_64.covers_cons w1 VG.Proof.MlKem.X86_64.covers_nil)⟩

theorem KSqzH.of {dst : Ptr} {len rate : Nat} (hc : VG.Proof.MlKem.X86_64.ksqzChk (rbs ++ wbs) wbs dst len = true) (hrate : rate ∈ rates) :
    VG.Proof.MlKem.X86_64.KSqzH dst len rate s := by
  simp only [VG.Proof.MlKem.X86_64.ksqzChk, VG.Proof.MlKem.X86_64.wrOk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hk, ⟨ho, hr⟩, hw⟩, hl⟩, s1⟩, s2⟩ := hc
  obtain ⟨d0, k0, k1, _, _, w0, w1⟩ := VG.Proof.MlKem.X86_64.kChk_spec L hk
  exact ⟨ho, hl, hrate, L.disj s1, d0, L.disj s2, k0, L.stkD hr, k1,
    VG.Proof.MlKem.X86_64.covers_cons w0 (VG.Proof.MlKem.X86_64.covers_cons (L.cW hw) (VG.Proof.MlKem.X86_64.covers_cons w1 VG.Proof.MlKem.X86_64.covers_nil))⟩

end

/-! ## Two runs in a layout -/

/-- Two states in the layout, with the same addresses in its registers and the same stack pointer. -/
def LRel (rbs wbs : List (Reg × Nat)) (x y : State) : Prop :=
  VG.Proof.MlKem.X86_64.Lay rbs wbs x ∧ VG.Proof.MlKem.X86_64.Lay rbs wbs y ∧ (∀ b ∈ rbs ++ wbs, x.gpr b.1 = y.gpr b.1) ∧ x.gpr .rsp = y.gpr .rsp

theorem LRel.eq {rbs wbs : List (Reg × Nat)} {x y : State} (h : VG.Proof.MlKem.X86_64.LRel rbs wbs x y) {p : Ptr} {l : Nat}
    (hin : VG.Proof.MlKem.X86_64.inB (rbs ++ wbs) p l = true) : x.gpr p.1 = y.gpr p.1 := by
  obtain ⟨n, hn, _⟩ := VG.Proof.MlKem.X86_64.inB_spec hin
  exact h.2.2.1 (p.1, n) hn

theorem LRel.pa {rbs wbs : List (Reg × Nat)} {x y : State} (h : VG.Proof.MlKem.X86_64.LRel rbs wbs x y) {p : Ptr} {l : Nat}
    (hin : VG.Proof.MlKem.X86_64.inB (rbs ++ wbs) p l = true) : VG.Proof.MlKem.X86_64.pa x p = VG.Proof.MlKem.X86_64.pa y p := by
  simp only [VG.Proof.MlKem.X86_64.pa, h.eq hin]

theorem LRel.post {rbs wbs : List (Reg × Nat)} {x y x' y' : State} {W₁ W₂ : List Region} (h : VG.Proof.MlKem.X86_64.LRel rbs wbs x y)
    (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) (hx : VG.Proof.MlKem.X86_64.PostB x x' W₁) (hy : VG.Proof.MlKem.X86_64.PostB y y' W₂) : VG.Proof.MlKem.X86_64.LRel rbs wbs x' y' :=
  ⟨h.1.post hx hcs, h.2.1.post hy hcs, fun b hb => by rw [hx.bs _ (hcs b hb), hy.bs _ (hcs b hb)]; exact h.2.2.1 b hb,
    by rw [hx.rsp, hy.rsp]; exact h.2.2.2⟩

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.FragHash`. -/
section

/-!
# ML-KEM-768 on x86-64: the hash functions of the top-level functions

`hashAt ps rate suffix out len` zeroes the Keccak state, absorbs the pieces
`ps`, pads and squeezes `len` bytes to `out`: the output of the sponge from
the padded state of their concatenation (`hash_ok`, which
`Proof/MlKem/KPke.lean` relates to `G`, `H`, `J` and `PRF`), leaking only the
addresses (`hash_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt rates Repr squeezeFrom)

/-! ## Composing what calls leave -/

theorem Post.refl (s : State) (W : List Region) : Post s s W := ⟨rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem Post.trans {s s₁ s₂ : State} {W₁ W₂ W : List Region} (h₁ : Post s s₁ W₁) (h₂ : Post s₁ s₂ W₂)
    (hw₁ : ∀ r ∈ W₁, r ∈ W) (hw₂ : ∀ r ∈ W₂, r ∈ W) : Post s s₂ W := by
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.cs r hr).trans (h₁.cs r hr), ?_⟩
  have f₂ := h₂.frame
  rw [h₁.rsp] at f₂
  refine (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₁ r hr), List.mem_append_right _ hr]
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₂ r hr), List.mem_append_right _ hr]

theorem map_toR_post {s s' : State} {W : List Region} (hP : Post s s' W) {ws : List (Ptr × Nat)}
    (h : ∀ w ∈ ws, w.1.1 ∈ calleeSaved) : ws.map (VG.Proof.MlKem.X86_64.toR s') = ws.map (VG.Proof.MlKem.X86_64.toR s) :=
  List.map_congr_left fun w hw => by simp only [VG.Proof.MlKem.X86_64.toR, hP.pa (h w hw)]

theorem PPost.trans {s s₁ s₂ : State} {ws₁ ws₂ ws : List (Ptr × Nat)} (h₁ : VG.Proof.MlKem.X86_64.PPost s s₁ ws₁)
    (h₂ : VG.Proof.MlKem.X86_64.PPost s₁ s₂ ws₂) (hcs : ∀ w ∈ ws₂, w.1.1 ∈ calleeSaved) (hw₁ : ∀ w ∈ ws₁, w ∈ ws)
    (hw₂ : ∀ w ∈ ws₂, w ∈ ws) : VG.Proof.MlKem.X86_64.PPost s s₂ ws := by
  have h₂' : Post s₁ s₂ (ws₂.map (VG.Proof.MlKem.X86_64.toR s)) := by rw [← VG.Proof.MlKem.X86_64.map_toR_post h₁ hcs]; exact h₂
  refine Post.trans h₁ h₂' (fun r hr => ?_) fun r hr => ?_
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₁ w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₂ w hw)

/-- A block that keeps the callee-saved registers and the permissions, and writes within `W`. -/
theorem post_of_keep {rs : List Reg} {s s' : State} {W : List Region} (k : Keep rs s s')
    (hrs : ∀ r ∈ calleeSaved, r ∉ rs) (hf : Frame W s.mem s'.mem) : Post s s' W :=
  ⟨k.2.1, k.2.2, fun r hr => k.gpr (hrs r hr), hf.mono fun _ hr => List.mem_append_left _ hr⟩

theorem sub_a {α : Type} {a b c : α} : ∀ w ∈ [a], w ∈ [a, b, c] := fun w hw => by
  rw [List.mem_singleton] at hw; subst hw; exact List.mem_cons_self ..

theorem sub_ab {α : Type} {a b c : α} : ∀ w ∈ [a, b], w ∈ [a, b, c] := fun w hw => by
  rcases List.mem_cons.mp hw with rfl | hw
  · exact List.mem_cons_self ..
  · rw [List.mem_singleton] at hw; subst hw; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem sub_acb {α : Type} {a b c : α} : ∀ w ∈ [a, c, b], w ∈ [a, b, c] := fun w hw => by
  rcases List.mem_cons.mp hw with rfl | hw
  · exact List.mem_cons_self ..
  rcases List.mem_cons.mp hw with rfl | hw
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · rw [List.mem_singleton] at hw; subst hw; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem cs3 {a b c : Ptr × Nat} (ha : a.1.1 ∈ calleeSaved) (hb : b.1.1 ∈ calleeSaved) (hc : c.1.1 ∈ calleeSaved) :
    ∀ w ∈ [a, b, c], w.1.1 ∈ calleeSaved := fun w hw => by
  rcases List.mem_cons.mp hw with rfl | hw
  · exact ha
  rcases List.mem_cons.mp hw with rfl | hw
  · exact hb
  · rw [List.mem_singleton] at hw; subst hw; exact hc

/-! ## Zeroing the state -/

theorem kzero_okP (s : State) (hw : Covers [⟨VG.Proof.MlKem.X86_64.pa s (sc 0), 200⟩] s.wr) :
    WP isa (.block kzero) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(sc 0, 200)] ∧ stateAt s'.mem (VG.Proof.MlKem.X86_64.pa s (sc 0)) = Spec.Sha3.zero :=
  WP.mono (VG.Proof.MlKem.X86_64.kzero_ok s hw) fun _ ⟨hz, hf, k⟩ => ⟨VG.Proof.MlKem.X86_64.post_of_keep k (by decide) hf, hz⟩

/-! ## Absorbing pieces -/

/-- A piece of the message: absorbed as `vg_keccak_absorb` needs, its register kept by the calls. -/
def pieceChk (bs wbs : List (Reg × Nat)) (p : Ptr × Nat) : Bool :=
  VG.Proof.MlKem.X86_64.kabsChk bs wbs p.1 p.2 && decide (VG.Proof.MlKem.X86_64.NA p.1) && decide (p.1.1 ∈ VG.Proof.MlKem.X86_64.bases)

theorem pieceChk_keep {bs wbs : List (Reg × Nat)} {p : Ptr × Nat} (h : VG.Proof.MlKem.X86_64.pieceChk bs wbs p = true) :
    VG.Proof.MlKem.X86_64.keepB bs [(sc 0, 200), (sc 200, 640)] p.1 p.2 = true := by
  simp only [VG.Proof.MlKem.X86_64.pieceChk, VG.Proof.MlKem.X86_64.kabsChk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _, hin⟩, _⟩, s1⟩, s2⟩, _⟩, hcs⟩ := h
  simp only [VG.Proof.MlKem.X86_64.keepB, List.all_cons, List.all_nil, s1, s2, hin, decide_eq_true hcs, Bool.and_self]

/-- The bytes of the pieces, concatenated. -/
abbrev pieces (s : State) (ps : List (Ptr × Nat)) : List Byte := ps.flatMap fun p => bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s p.1) p.2

theorem pieces_length (s : State) (ps : List (Ptr × Nat)) : (VG.Proof.MlKem.X86_64.pieces s ps).length = totLen ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [VG.Proof.MlKem.X86_64.pieces, List.flatMap_cons, List.length_append, bytesAt_length] at ih ⊢
    rw [ih]; simp [totLen]

theorem pieces_keep {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {ws : List (Ptr × Nat)}
    (hP : VG.Proof.MlKem.X86_64.PPostB s s' ws) : ∀ {ps : List (Ptr × Nat)},
    (∀ p ∈ ps, VG.Proof.MlKem.X86_64.keepB (rbs ++ wbs) ws p.1 p.2 = true) → VG.Proof.MlKem.X86_64.pieces s' ps = VG.Proof.MlKem.X86_64.pieces s ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [VG.Proof.MlKem.X86_64.pieces, List.flatMap_cons]
    rw [L.keepBytes hP (h p (List.mem_cons_self ..))]
    exact congrArg _ (VG.Proof.MlKem.X86_64.pieces_keep L hP fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- What absorbing the pieces `ps` from position `pos` does. -/
def AbsOk (rbs wbs : List (Reg × Nat)) (rate : Nat) (ps : List (Ptr × Nat)) : Prop :=
  ∀ {s : State} (_ : VG.Proof.MlKem.X86_64.Lay rbs wbs s) (pos : Nat) (msg : List Byte),
    ps.all (VG.Proof.MlKem.X86_64.pieceChk (rbs ++ wbs) wbs) = true → pos < rate → pos = msg.length % rate →
    Repr s.mem (VG.Proof.MlKem.X86_64.pa s (sc 0)) rate msg →
    WP isa (absAll rate ps pos) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(sc 0, 200), (sc 200, 640)] ∧
      Repr s'.mem (VG.Proof.MlKem.X86_64.pa s (sc 0)) rate (msg ++ VG.Proof.MlKem.X86_64.pieces s ps)

theorem absAll_nil (rbs wbs : List (Reg × Nat)) (rate : Nat) : VG.Proof.MlKem.X86_64.AbsOk rbs wbs rate [] :=
  fun _ _ _ _ _ _ hR => WP.block_nil ⟨Post.refl _ _, by simpa using hR⟩

theorem absAll_cons {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases)
    {rate : Nat} (hrate : rate ∈ rates) (p : Ptr) (l : Nat) {ps : List (Ptr × Nat)}
    (IH : VG.Proof.MlKem.X86_64.AbsOk rbs wbs rate ps) : VG.Proof.MlKem.X86_64.AbsOk rbs wbs rate ((p, l) :: ps) := by
  intro s L pos msg hps hpos hm hR
  simp only [List.all_cons, Bool.and_eq_true] at hps
  have hp := hps.1
  have hna : VG.Proof.MlKem.X86_64.NA p := by
    simp only [VG.Proof.MlKem.X86_64.pieceChk, Bool.and_eq_true, decide_eq_true_eq] at hp; exact hp.1.2
  have hkc : VG.Proof.MlKem.X86_64.kabsChk (rbs ++ wbs) wbs p l = true := by
    simp only [VG.Proof.MlKem.X86_64.pieceChk, Bool.and_eq_true] at hp; exact hp.1.1
  have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
  rw [absAll]
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.kabs_ok hna (KAbsH.of L hkc hrate hpos)) fun s₁ ⟨hP₁, hR₁⟩ => ?_)
  have hP₁' : VG.Proof.MlKem.X86_64.PPost s s₁ [(sc 0, 200), (sc 200, 640)] := hP₁
  have L₁ := L.post hP₁.b hcs
  have e0 : VG.Proof.MlKem.X86_64.pa s₁ (sc 0) = VG.Proof.MlKem.X86_64.pa s (sc 0) := hP₁.pa (by decide)
  have hR₁' := hR₁ msg hR hm
  rw [← e0] at hR₁'
  have h3 : ((pos + l) % rate) = (msg ++ bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s p) l).length % rate := by
    rw [List.length_append, bytesAt_length, hm, Nat.mod_add_mod]
  refine WP.mono (IH L₁ ((pos + l) % rate) (msg ++ bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s p) l) hps.2 (Nat.mod_lt _ hr0) h3 hR₁')
    fun s₂ ⟨hP₂, hR₂⟩ => ⟨PPost.trans hP₁' hP₂ (by decide) (fun w hw => hw) (fun w hw => hw), ?_⟩
  rw [e0, VG.Proof.MlKem.X86_64.pieces_keep L hP₁'.b fun q hq => VG.Proof.MlKem.X86_64.pieceChk_keep (List.all_eq_true.mp hps.2 q hq)] at hR₂
  simpa only [VG.Proof.MlKem.X86_64.pieces, List.flatMap_cons, List.append_assoc] using hR₂

theorem absAll_ok {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {rate : Nat}
    (hrate : rate ∈ rates) (ps : List (Ptr × Nat)) : VG.Proof.MlKem.X86_64.AbsOk rbs wbs rate ps := by
  induction ps with
  | nil => exact VG.Proof.MlKem.X86_64.absAll_nil rbs wbs rate
  | cons p ps ih => exact VG.Proof.MlKem.X86_64.absAll_cons hcs hrate p.1 p.2 ih

/-! ## The hash -/

/-- The output: `len` bytes to `out`, from position 0. -/
def hashChk (bs wbs : List (Reg × Nat)) (ps : List (Ptr × Nat)) (rate : Nat) (out : Ptr) (len : Nat) : Bool :=
  decide (rate ∈ rates) && VG.Proof.MlKem.X86_64.kChk bs wbs && ps.all (VG.Proof.MlKem.X86_64.pieceChk bs wbs) && VG.Proof.MlKem.X86_64.ksqzChk bs wbs out len &&
    decide (VG.Proof.MlKem.X86_64.NA out) && decide (out.1 ∈ calleeSaved)

theorem hashChk_spec {bs wbs : List (Reg × Nat)} {ps : List (Ptr × Nat)} {rate : Nat} {out : Ptr} {len : Nat}
    (h : VG.Proof.MlKem.X86_64.hashChk bs wbs ps rate out len = true) :
    rate ∈ rates ∧ VG.Proof.MlKem.X86_64.kChk bs wbs = true ∧ ps.all (VG.Proof.MlKem.X86_64.pieceChk bs wbs) = true ∧ VG.Proof.MlKem.X86_64.ksqzChk bs wbs out len = true ∧
      VG.Proof.MlKem.X86_64.NA out ∧ out.1 ∈ calleeSaved := by
  simp only [VG.Proof.MlKem.X86_64.hashChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem hash_ok {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases)
    {ps : List (Ptr × Nat)} {rate suffix : Nat} {out : Ptr} {len : Nat}
    (hc : VG.Proof.MlKem.X86_64.hashChk (rbs ++ wbs) wbs ps rate out len = true) (hsuf : suffix < 256) {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) :
    WP isa (hashAt ps rate suffix out len) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(sc 0, 200), (sc 200, 640), (out, len)] ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s out) len =
        squeezeFrom rate (padded rate (BitVec.ofNat 8 suffix) (VG.Proof.MlKem.X86_64.pieces s ps)) 0 len := by
  obtain ⟨hrate, hk, hps, hsq, hna, hocs⟩ := VG.Proof.MlKem.X86_64.hashChk_spec hc
  obtain ⟨_, _, _, _, _, w0, _⟩ := VG.Proof.MlKem.X86_64.kChk_spec L hk
  have hr0 : 0 < rate := by
    simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at hrate; omega
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.kzero_okP s w0) fun s₁ ⟨hP₁, hz⟩ => ?_)
  have L₁ := L.post hP₁.b hcs
  have e1 : VG.Proof.MlKem.X86_64.pa s₁ (sc 0) = VG.Proof.MlKem.X86_64.pa s (sc 0) := hP₁.pa (by decide)
  have hpk : ∀ p ∈ ps, VG.Proof.MlKem.X86_64.keepB (rbs ++ wbs) [(sc 0, 200)] p.1 p.2 = true := fun p hp => by
    have := VG.Proof.MlKem.X86_64.pieceChk_keep (List.all_eq_true.mp hps p hp)
    simp only [VG.Proof.MlKem.X86_64.keepB, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this ⊢
    exact ⟨this.1, this.2.1⟩
  have epc : VG.Proof.MlKem.X86_64.pieces s₁ ps = VG.Proof.MlKem.X86_64.pieces s ps := VG.Proof.MlKem.X86_64.pieces_keep L hP₁.b hpk
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.absAll_ok hcs hrate ps L₁ 0 [] hps hr0 rfl (by rw [e1]; exact repr_nil hz))
    fun s₂ ⟨hP₂, hR₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b hcs
  have e2 : VG.Proof.MlKem.X86_64.pa s₂ (sc 0) = VG.Proof.MlKem.X86_64.pa s₁ (sc 0) := hP₂.pa (by decide)
  rw [List.nil_append, epc] at hR₂
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.kpad_ok hsuf (KPadH.of L₂ hk hrate (pos := totLen ps % rate) (Nat.mod_lt _ hr0)))
    fun s₃ ⟨hP₃, hS₃⟩ => ?_)
  have hP₃' : VG.Proof.MlKem.X86_64.PPost s₂ s₃ [(sc 0, 200), (sc 200, 640)] := hP₃
  have L₃ := L₂.post hP₃.b hcs
  have e3 : VG.Proof.MlKem.X86_64.pa s₃ (sc 0) = VG.Proof.MlKem.X86_64.pa s₂ (sc 0) := hP₃.pa (by decide)
  have hS := hS₃ (VG.Proof.MlKem.X86_64.pieces s ps) (by rw [e2]; exact hR₂) (by rw [VG.Proof.MlKem.X86_64.pieces_length])
  refine WP.mono (VG.Proof.MlKem.X86_64.ksqz_ok hna (KSqzH.of L₃ hsq hrate)) fun s₄ ⟨hP₄, ho⟩ => ?_
  have hP₄' : VG.Proof.MlKem.X86_64.PPost s₃ s₄ [(sc 0, 200), (out, len), (sc 200, 640)] := hP₄
  have eo : VG.Proof.MlKem.X86_64.pa s₃ out = VG.Proof.MlKem.X86_64.pa s out := by
    rw [hP₃.pa hocs, hP₂.pa hocs, hP₁.pa hocs]
  refine ⟨PPost.trans (PPost.trans (PPost.trans hP₁ hP₂ (by decide) VG.Proof.MlKem.X86_64.sub_a VG.Proof.MlKem.X86_64.sub_ab) hP₃'
    (by decide) (fun w hw => hw) VG.Proof.MlKem.X86_64.sub_ab) hP₄' (VG.Proof.MlKem.X86_64.cs3 (by decide) hocs (by decide)) (fun w hw => hw) VG.Proof.MlKem.X86_64.sub_acb, ?_⟩
  rw [← eo, ho, e3, hS]

/-! ## Constant time -/

/-- A piece of code that keeps the layout, from two runs in it, leaves two runs in it. -/
theorem LRel.step {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {c : Prog isa}
    (htr : RelCT isa (VG.Proof.MlKem.X86_64.LRel rbs wbs) c fun _ _ => True)
    (hok : ∀ x, VG.Proof.MlKem.X86_64.Lay rbs wbs x → WP isa c x fun x' => ∃ W, Post x x' W) :
    RelCT isa (VG.Proof.MlKem.X86_64.LRel rbs wbs) c (VG.Proof.MlKem.X86_64.LRel rbs wbs) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, Post x x' W) (fun x y h => ⟨hok x h.1, hok y h.2.1⟩)
    fun _ _ _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => h.post hcs hx.b hy.b

theorem nil_tr {P : State → State → Prop} : RelCT isa P (.block []) P :=
  RelCT.postDep (VG.Proof.MlKem.X86_64.block_nomem_tr fun _ hi => absurd hi List.not_mem_nil) (F := fun x x' => x' = x)
    (fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) fun _ _ _ _ h hx hy => hx ▸ hy ▸ h

theorem kChk_in {bs wbs : List (Reg × Nat)} (h : VG.Proof.MlKem.X86_64.kChk bs wbs = true) : VG.Proof.MlKem.X86_64.inB bs (sc 0) 200 = true := by
  simp only [VG.Proof.MlKem.X86_64.kChk, VG.Proof.MlKem.X86_64.wrOk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true] at h
  exact h.1.1.1.2

theorem absAll_tr {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {rate : Nat}
    (hrate : rate ∈ rates) (hk : VG.Proof.MlKem.X86_64.kChk (rbs ++ wbs) wbs = true) :
    ∀ (ps : List (Ptr × Nat)) (pos : Nat), ps.all (VG.Proof.MlKem.X86_64.pieceChk (rbs ++ wbs) wbs) = true → pos < rate →
      RelCT isa (VG.Proof.MlKem.X86_64.LRel rbs wbs) (absAll rate ps pos) (VG.Proof.MlKem.X86_64.LRel rbs wbs)
  | [], _, _, _ => VG.Proof.MlKem.X86_64.nil_tr
  | (p, l) :: ps, pos, hps, hpos => by
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hp := hps.1
    have hna : VG.Proof.MlKem.X86_64.NA p := by
      simp only [VG.Proof.MlKem.X86_64.pieceChk, Bool.and_eq_true, decide_eq_true_eq] at hp; exact hp.1.2
    have hkc : VG.Proof.MlKem.X86_64.kabsChk (rbs ++ wbs) wbs p l = true := by
      simp only [VG.Proof.MlKem.X86_64.pieceChk, Bool.and_eq_true] at hp; exact hp.1.1
    have hin : VG.Proof.MlKem.X86_64.inB (rbs ++ wbs) p l = true := by
      simp only [VG.Proof.MlKem.X86_64.kabsChk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true] at hkc; exact hkc.1.1.1.2.2
    have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
    rw [absAll]
    exact RelCT.seq (LRel.step hcs (RelCT.mono (VG.Proof.MlKem.X86_64.kabs_tr hna) (fun x y h =>
        ⟨KAbsH.of h.1 hkc hrate hpos, KAbsH.of h.2.1 hkc hrate hpos, h.eq (VG.Proof.MlKem.X86_64.kChk_in hk), h.eq hin, h.2.2.2⟩)
        fun _ _ _ => trivial)
      fun x Lx => WP.mono (VG.Proof.MlKem.X86_64.kabs_ok hna (KAbsH.of Lx hkc hrate hpos)) fun _ h => ⟨_, h.1⟩)
      (VG.Proof.MlKem.X86_64.absAll_tr hcs hrate hk ps ((pos + l) % rate) hps.2 (Nat.mod_lt _ hr0))

theorem hash_tr {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases)
    {ps : List (Ptr × Nat)} {rate suffix : Nat} {out : Ptr} {len : Nat}
    (hc : VG.Proof.MlKem.X86_64.hashChk (rbs ++ wbs) wbs ps rate out len = true) (hsuf : suffix < 256) :
    RelCT isa (VG.Proof.MlKem.X86_64.LRel rbs wbs) (hashAt ps rate suffix out len) fun _ _ => True := by
  obtain ⟨hrate, hk, hps, hsq, hna, _⟩ := VG.Proof.MlKem.X86_64.hashChk_spec hc
  have hr0 : 0 < rate := by
    simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at hrate; omega
  have hin : VG.Proof.MlKem.X86_64.inB (rbs ++ wbs) out len = true := by
    simp only [VG.Proof.MlKem.X86_64.ksqzChk, VG.Proof.MlKem.X86_64.wrOk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true] at hsq; exact hsq.1.1.1.2.1.2
  refine RelCT.seq (LRel.step hcs (VG.Proof.MlKem.X86_64.kzero_tr fun x y h => h.eq (VG.Proof.MlKem.X86_64.kChk_in hk))
    fun x Lx => WP.mono (VG.Proof.MlKem.X86_64.kzero_okP x (VG.Proof.MlKem.X86_64.kChk_spec Lx hk).2.2.2.2.2.1) fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (VG.Proof.MlKem.X86_64.absAll_tr hcs hrate hk ps 0 hps hr0) (RelCT.seq (LRel.step hcs (RelCT.mono (VG.Proof.MlKem.X86_64.kpad_tr hsuf)
      (fun x y h => ⟨KPadH.of h.1 hk hrate (Nat.mod_lt _ hr0), KPadH.of h.2.1 hk hrate (Nat.mod_lt _ hr0),
        h.eq (VG.Proof.MlKem.X86_64.kChk_in hk), h.2.2.2⟩) fun _ _ _ => trivial)
      fun x Lx => WP.mono (VG.Proof.MlKem.X86_64.kpad_ok hsuf (KPadH.of Lx hk hrate (Nat.mod_lt _ hr0))) fun _ h => ⟨_, h.1⟩)
      (RelCT.mono (VG.Proof.MlKem.X86_64.ksqz_tr hna) (fun x y h => ⟨KSqzH.of h.1 hsq hrate, KSqzH.of h.2.1 hsq hrate,
        h.eq (VG.Proof.MlKem.X86_64.kChk_in hk), h.eq hin, h.2.2.2⟩) fun _ _ _ => trivial)))

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.FragL`. -/
section

/-!
# ML-KEM-768 on x86-64: the calls of the polynomial primitives, in a layout

Each call of a primitive from a state in a layout whose pointers pass its
check: what it leaves (`PPost`) and computes (`nttAt_ok`, …), and that two
runs in the layout leak the same (`nttAt_tr`, …); and the same for the byte
stores and copies between them.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt rates)

section
variable {rbs wbs : List (Reg × Nat)}

theorem rdOk_in {bs : List (Reg × Nat)} {p : Ptr} {l : Nat} (h : VG.Proof.MlKem.X86_64.rdOk bs p l = true) : VG.Proof.MlKem.X86_64.inB bs p l = true := by
  simp only [VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true] at h; exact h.2

theorem wrOk_in {bs wbs : List (Reg × Nat)} {p : Ptr} {l : Nat} (h : VG.Proof.MlKem.X86_64.wrOk bs wbs p l = true) : VG.Proof.MlKem.X86_64.inB bs p l = true := by
  simp only [VG.Proof.MlKem.X86_64.wrOk, Bool.and_eq_true] at h; exact VG.Proof.MlKem.X86_64.rdOk_in h.1

/-! ## `NTT` and `NTT⁻¹` -/

theorem ipChk_in {bs wbs : List (Reg × Nat)} {f : Ptr} (hc : VG.Proof.MlKem.X86_64.ipChk bs wbs f = true) :
    VG.Proof.MlKem.X86_64.inB bs f 1024 = true ∧ VG.Proof.MlKem.X86_64.inB bs (sc oSS) 1024 = true := by
  simp only [VG.Proof.MlKem.X86_64.ipChk, Bool.and_eq_true] at hc; exact ⟨VG.Proof.MlKem.X86_64.wrOk_in hc.1.1, VG.Proof.MlKem.X86_64.wrOk_in hc.1.2⟩

theorem nttAt_ok {A : Arith} (hA : VG.Proof.MlKem.X86_64.ArithOk A) {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {f : Ptr}
    (hc : VG.Proof.MlKem.X86_64.ipChk (rbs ++ wbs) wbs f = true) (red : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) :
    WP isa (nttAt A f) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(f, 1024), (sc oSS, 1024)] ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s f) (ntt (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f))) :=
  VG.Proof.MlKem.X86_64.ipAt_ok hA.ntt.ok hA.ntt.nosp (by rw [hA.ntt.depth]; decide) (IpH.of L hc red)

theorem nttInvAt_ok {A : Arith} (hA : VG.Proof.MlKem.X86_64.ArithOk A) {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {f : Ptr}
    (hc : VG.Proof.MlKem.X86_64.ipChk (rbs ++ wbs) wbs f = true) (red : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) :
    WP isa (nttInvAt A f) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(f, 1024), (sc oSS, 1024)] ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s f) (nttInv (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f))) :=
  VG.Proof.MlKem.X86_64.ipAt_ok hA.nttInv.ok hA.nttInv.nosp (by rw [hA.nttInv.depth]; decide) (IpH.of L hc red)

theorem nttAt_tr {A : Arith} (hA : VG.Proof.MlKem.X86_64.ArithOk A) {f : Ptr} (hc : VG.Proof.MlKem.X86_64.ipChk (rbs ++ wbs) wbs f = true) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x f) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y f)) (nttAt A f)
      fun _ _ => True :=
  RelCT.mono (VG.Proof.MlKem.X86_64.ipAt_tr hA.ntt.ok hA.ntt.ct) (fun _ _ ⟨h, rx, ry⟩ => ⟨IpH.of h.1 hc rx, IpH.of h.2.1 hc ry,
    h.eq (VG.Proof.MlKem.X86_64.ipChk_in hc).1, h.eq (VG.Proof.MlKem.X86_64.ipChk_in hc).2, h.2.2.2⟩) fun _ _ _ => trivial

theorem nttInvAt_tr {A : Arith} (hA : VG.Proof.MlKem.X86_64.ArithOk A) {f : Ptr} (hc : VG.Proof.MlKem.X86_64.ipChk (rbs ++ wbs) wbs f = true) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x f) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y f)) (nttInvAt A f)
      fun _ _ => True :=
  RelCT.mono (VG.Proof.MlKem.X86_64.ipAt_tr hA.nttInv.ok hA.nttInv.ct) (fun _ _ ⟨h, rx, ry⟩ => ⟨IpH.of h.1 hc rx, IpH.of h.2.1 hc ry,
    h.eq (VG.Proof.MlKem.X86_64.ipChk_in hc).1, h.eq (VG.Proof.MlKem.X86_64.ipChk_in hc).2, h.2.2.2⟩) fun _ _ _ => trivial

/-! ## Addition and subtraction -/

theorem accChk_in {bs wbs : List (Reg × Nat)} {f g : Ptr} (hc : VG.Proof.MlKem.X86_64.accChk bs wbs f g = true) :
    VG.Proof.MlKem.X86_64.inB bs f 1024 = true ∧ VG.Proof.MlKem.X86_64.inB bs g 1024 = true := by
  simp only [VG.Proof.MlKem.X86_64.accChk, Bool.and_eq_true] at hc; exact ⟨VG.Proof.MlKem.X86_64.wrOk_in hc.1.1, VG.Proof.MlKem.X86_64.rdOk_in hc.1.2⟩

theorem addAt_ok {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {f g : Ptr} (hg : VG.Proof.MlKem.X86_64.NA g) (hc : VG.Proof.MlKem.X86_64.accChk (rbs ++ wbs) wbs f g = true)
    (rf : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) (rg : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g)) :
    WP isa (addAt f g) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(f, 1024)] ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s f) (add (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f)) (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s g))) :=
  VG.Proof.MlKem.X86_64.accAt_ok add_correct VG.Proof.MlKem.X86_64.add_nosp (by rw [VG.Proof.MlKem.X86_64.add_depth]; decide) (fun e => hg (by rw [e]; decide)) (AccH.of L hc rf rg)

theorem subAt_ok {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {f g : Ptr} (hg : VG.Proof.MlKem.X86_64.NA g) (hc : VG.Proof.MlKem.X86_64.accChk (rbs ++ wbs) wbs f g = true)
    (rf : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) (rg : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g)) :
    WP isa (subAt f g) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(f, 1024)] ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s f) (VG.Spec.MlKem.sub (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f)) (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s g))) :=
  VG.Proof.MlKem.X86_64.accAt_ok sub_correct VG.Proof.MlKem.X86_64.sub_nosp (by rw [VG.Proof.MlKem.X86_64.sub_depth]; decide) (fun e => hg (by rw [e]; decide)) (AccH.of L hc rf rg)

theorem addAt_tr {f g : Ptr} (hg : VG.Proof.MlKem.X86_64.NA g) (hc : VG.Proof.MlKem.X86_64.accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlKem.X86_64.pa x f) ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlKem.X86_64.pa y f) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y g))) (addAt f g) fun _ _ => True :=
  RelCT.mono (VG.Proof.MlKem.X86_64.accAt_tr add_correct add_ct (fun e => hg (by rw [e]; decide)))
    (fun _ _ ⟨h, ⟨r1, r2⟩, r3, r4⟩ => ⟨AccH.of h.1 hc r1 r2, AccH.of h.2.1 hc r3 r4, h.eq (VG.Proof.MlKem.X86_64.accChk_in hc).1,
      h.eq (VG.Proof.MlKem.X86_64.accChk_in hc).2, h.2.2.2⟩) fun _ _ _ => trivial

theorem subAt_tr {f g : Ptr} (hg : VG.Proof.MlKem.X86_64.NA g) (hc : VG.Proof.MlKem.X86_64.accChk (rbs ++ wbs) wbs f g = true) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlKem.X86_64.pa x f) ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlKem.X86_64.pa y f) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y g))) (subAt f g) fun _ _ => True :=
  RelCT.mono (VG.Proof.MlKem.X86_64.accAt_tr sub_correct sub_ct (fun e => hg (by rw [e]; decide)))
    (fun _ _ ⟨h, ⟨r1, r2⟩, r3, r4⟩ => ⟨AccH.of h.1 hc r1 r2, AccH.of h.2.1 hc r3 r4, h.eq (VG.Proof.MlKem.X86_64.accChk_in hc).1,
      h.eq (VG.Proof.MlKem.X86_64.accChk_in hc).2, h.2.2.2⟩) fun _ _ _ => trivial

/-! ## `MultiplyNTTs` -/

theorem mulChk_in {bs wbs : List (Reg × Nat)} {h f g : Ptr} (hc : VG.Proof.MlKem.X86_64.mulChk bs wbs h f g = true) :
    VG.Proof.MlKem.X86_64.inB bs h 1024 = true ∧ VG.Proof.MlKem.X86_64.inB bs f 1024 = true ∧ VG.Proof.MlKem.X86_64.inB bs g 1024 = true ∧ VG.Proof.MlKem.X86_64.inB bs (sc oSS) 1024 = true := by
  simp only [VG.Proof.MlKem.X86_64.mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨VG.Proof.MlKem.X86_64.wrOk_in h1, VG.Proof.MlKem.X86_64.rdOk_in h2, VG.Proof.MlKem.X86_64.rdOk_in h3, VG.Proof.MlKem.X86_64.wrOk_in h4⟩

theorem mulAt_okL {A : Arith} (hA : VG.Proof.MlKem.X86_64.ArithOk A) {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {h f g : Ptr} (hf : VG.Proof.MlKem.X86_64.NA f)
    (hg : VG.Proof.MlKem.X86_64.NA g) (hc : VG.Proof.MlKem.X86_64.mulChk (rbs ++ wbs) wbs h f g = true) (rf : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f))
    (rg : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s g)) :
    WP isa (mulAt A h f g) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(h, 1024), (sc oSS, 1024)] ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s h) (multiplyNTTs (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f)) (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s g))) :=
  VG.Proof.MlKem.X86_64.mulAt_ok hA hf hg (MulH.of L hc rf rg)

theorem mulAt_trL {A : Arith} (hA : VG.Proof.MlKem.X86_64.ArithOk A) {h f g : Ptr} (hf : VG.Proof.MlKem.X86_64.NA f) (hg : VG.Proof.MlKem.X86_64.NA g)
    (hc : VG.Proof.MlKem.X86_64.mulChk (rbs ++ wbs) wbs h f g = true) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ (Reduced x.mem (VG.Proof.MlKem.X86_64.pa x f) ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlKem.X86_64.pa y f) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y g))) (mulAt A h f g) fun _ _ => True :=
  RelCT.mono (VG.Proof.MlKem.X86_64.mulAt_tr hA hf hg) (fun _ _ ⟨e, ⟨r1, r2⟩, r3, r4⟩ => ⟨MulH.of e.1 hc r1 r2, MulH.of e.2.1 hc r3 r4,
    e.eq (VG.Proof.MlKem.X86_64.mulChk_in hc).1, e.eq (VG.Proof.MlKem.X86_64.mulChk_in hc).2.1, e.eq (VG.Proof.MlKem.X86_64.mulChk_in hc).2.2.1, e.eq (VG.Proof.MlKem.X86_64.mulChk_in hc).2.2.2,
    e.2.2.2⟩) fun _ _ _ => trivial

/-! ## Two pointers: `SamplePolyCBD₂`, `ByteEncode₁₂`, `ByteDecode₁₂` and the compressions -/

theorem twoChk_in {bs wbs : List (Reg × Nat)} {p q : Ptr} {n m : Nat} (hc : VG.Proof.MlKem.X86_64.twoChk bs wbs p n q m = true) :
    VG.Proof.MlKem.X86_64.inB bs p n = true ∧ VG.Proof.MlKem.X86_64.inB bs q m = true := by
  simp only [VG.Proof.MlKem.X86_64.twoChk, Bool.and_eq_true] at hc; exact ⟨VG.Proof.MlKem.X86_64.rdOk_in hc.1.1, VG.Proof.MlKem.X86_64.wrOk_in hc.1.2⟩

theorem cbd2At_okL {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {p q : Ptr} (hq : VG.Proof.MlKem.X86_64.NA q)
    (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs p 128 q 1024 = true) :
    WP isa (cbd2At p q) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(q, 1024)] ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s q) (samplePolyCBD 2 (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s p) 128)) :=
  VG.Proof.MlKem.X86_64.cbd2At_ok hq (TwoH.of L hc)

theorem cbd2At_trL {p q : Ptr} (hq : VG.Proof.MlKem.X86_64.NA q) (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs p 128 q 1024 = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.LRel rbs wbs) (cbd2At p q) fun _ _ => True :=
  RelCT.mono (VG.Proof.MlKem.X86_64.cbd2At_tr hq) (fun _ _ e => ⟨TwoH.of e.1 hc, TwoH.of e.2.1 hc, e.eq (VG.Proof.MlKem.X86_64.twoChk_in hc).1,
    e.eq (VG.Proof.MlKem.X86_64.twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem enc12At_okL {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {p q : Ptr} (hq : VG.Proof.MlKem.X86_64.NA q)
    (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs p 1024 q 384 = true) (red : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s p)) :
    WP isa (enc12At p q) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(q, 384)] ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s q) 384 = encode12 (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s p)) :=
  VG.Proof.MlKem.X86_64.enc12At_ok hq (TwoH.of L hc) red

theorem enc12At_trL {p q : Ptr} (hq : VG.Proof.MlKem.X86_64.NA q) (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs p 1024 q 384 = true) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x p) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y p)) (enc12At p q)
      fun _ _ => True :=
  RelCT.mono (VG.Proof.MlKem.X86_64.enc12At_tr hq) (fun _ _ ⟨e, r1, r2⟩ => ⟨⟨TwoH.of e.1 hc, r1⟩, ⟨TwoH.of e.2.1 hc, r2⟩,
    e.eq (VG.Proof.MlKem.X86_64.twoChk_in hc).1, e.eq (VG.Proof.MlKem.X86_64.twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem dec12At_okL {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {p q : Ptr} (hq : VG.Proof.MlKem.X86_64.NA q)
    (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs p 384 q 1024 = true) :
    WP isa (dec12At p q) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(q, 1024)] ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s q) (decode12 (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s p) 384)) :=
  VG.Proof.MlKem.X86_64.dec12At_ok hq (TwoH.of L hc)

theorem dec12At_trL {p q : Ptr} (hq : VG.Proof.MlKem.X86_64.NA q) (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs p 384 q 1024 = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.LRel rbs wbs) (dec12At p q) fun _ _ => True :=
  RelCT.mono (VG.Proof.MlKem.X86_64.dec12At_tr hq) (fun _ _ e => ⟨TwoH.of e.1 hc, TwoH.of e.2.1 hc, e.eq (VG.Proof.MlKem.X86_64.twoChk_in hc).1,
    e.eq (VG.Proof.MlKem.X86_64.twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem ceCall_okL {n : String} {c : Prog isa} {ws : List Nat} (I : VG.Proof.MlKem.X86_64.CEImpl n c ws) {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s)
    {f out : Ptr} {d : Nat} (hout : VG.Proof.MlKem.X86_64.NA out) (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs f 1024 out (32 * d) = true) (hd : d ∈ ws)
    (red : Reduced s.mem (VG.Proof.MlKem.X86_64.pa s f)) :
    WP isa (ceCall n c f d out) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(out, 32 * d)] ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s out) (32 * d) = compressEncode d (polyAt s.mem (VG.Proof.MlKem.X86_64.pa s f)) :=
  VG.Proof.MlKem.X86_64.ceCall_ok I hout (CEH.of L hc hd red)

theorem ceCall_trL {n : String} {c : Prog isa} {ws : List Nat} (I : VG.Proof.MlKem.X86_64.CEImpl n c ws) {f out : Ptr} {d : Nat}
    (hout : VG.Proof.MlKem.X86_64.NA out) (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs f 1024 out (32 * d) = true) (hd : d ∈ ws) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x f) ∧ Reduced y.mem (VG.Proof.MlKem.X86_64.pa y f)) (ceCall n c f d out)
      fun _ _ => True :=
  RelCT.mono (VG.Proof.MlKem.X86_64.ceCall_tr I hout) (fun _ _ ⟨e, r1, r2⟩ => ⟨CEH.of e.1 hc hd r1, CEH.of e.2.1 hc hd r2,
    e.eq (VG.Proof.MlKem.X86_64.twoChk_in hc).1, e.eq (VG.Proof.MlKem.X86_64.twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

theorem ddCall_okL {n : String} {c : Prog isa} {ws : List Nat} (I : VG.Proof.MlKem.X86_64.DDImpl n c ws) {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s)
    {b f : Ptr} {d : Nat} (hf : VG.Proof.MlKem.X86_64.NA f) (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs b (32 * d) f 1024 = true) (hd : d ∈ ws) :
    WP isa (ddCall n c b d f) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(f, 1024)] ∧
      PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s f) (decodeDecompress d (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s b) (32 * d))) :=
  VG.Proof.MlKem.X86_64.ddCall_ok I hf (DDH.of L hc hd)

theorem ddCall_trL {n : String} {c : Prog isa} {ws : List Nat} (I : VG.Proof.MlKem.X86_64.DDImpl n c ws) {b f : Ptr} {d : Nat} (hf : VG.Proof.MlKem.X86_64.NA f)
    (hc : VG.Proof.MlKem.X86_64.twoChk (rbs ++ wbs) wbs b (32 * d) f 1024 = true) (hd : d ∈ ws) :
    RelCT isa (VG.Proof.MlKem.X86_64.LRel rbs wbs) (ddCall n c b d f) fun _ _ => True :=
  RelCT.mono (VG.Proof.MlKem.X86_64.ddCall_tr I hf) (fun _ _ e => ⟨DDH.of e.1 hc hd, DDH.of e.2.1 hc hd, e.eq (VG.Proof.MlKem.X86_64.twoChk_in hc).1,
    e.eq (VG.Proof.MlKem.X86_64.twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

/-! ## `SampleNTT` -/

theorem sampChk_in {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : VG.Proof.MlKem.X86_64.sampChk bs wbs a = true) :
    VG.Proof.MlKem.X86_64.inB bs (sc oSB) 34 = true ∧ VG.Proof.MlKem.X86_64.inB bs a 1024 = true := by
  simp only [VG.Proof.MlKem.X86_64.sampChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨VG.Proof.MlKem.X86_64.rdOk_in h1, VG.Proof.MlKem.X86_64.wrOk_in h2⟩

theorem sampleAt_trL {a : Ptr} (hna : VG.Proof.MlKem.X86_64.NA a) (hc : VG.Proof.MlKem.X86_64.sampChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (sc oSB)) 34 = bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y (sc oSB)) 34)
      (sampleAt a) fun _ _ => True :=
  RelCT.mono (VG.Proof.MlKem.X86_64.sampleAt_tr hna) (fun _ _ ⟨e, hb⟩ => ⟨SampH.of e.1 hc, SampH.of e.2.1 hc,
    e.eq (VG.Proof.MlKem.X86_64.sampChk_in hc).1, e.eq (VG.Proof.MlKem.X86_64.sampChk_in hc).2, e.2.2.2, hb⟩) fun _ _ _ => trivial

end

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.FragS`. -/
section

/-!
# ML-KEM-768 on x86-64: byte stores, copies, and the calls of `SampleNTT`

In a layout: a byte store (`setB_okL`), a copy (`copy_okL`), and the entry
`Â[i, j]` of the matrix, `SampleNTT(ρ ‖ j ‖ i)` with `ρ` at `SB`
(`sampleIJ_ok`, `sampleIJ_tr`), which changes `r15` (so what it leaves is
`PostB`, not `Post`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem rbx_cs : Reg.rbx ∈ calleeSaved := by decide
theorem rbx_na : Reg.rbx ∉ argRegs := by decide
theorem rbx_bases : Reg.rbx ∈ VG.Proof.MlKem.X86_64.bases := by decide

/-! ## Composing what pieces leave -/

theorem PostB.refl (s : State) (W : List Region) : VG.Proof.MlKem.X86_64.PostB s s W :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, Frame.refl _ _⟩

theorem PPostB.app {s s₁ s₂ : State} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : VG.Proof.MlKem.X86_64.PPostB s s₁ ws₁) (h₂ : VG.Proof.MlKem.X86_64.PPostB s₁ s₂ ws₂)
    (hb : ∀ w ∈ ws₂, w.1.1 ∈ VG.Proof.MlKem.X86_64.bases) : VG.Proof.MlKem.X86_64.PPostB s s₂ (ws₁ ++ ws₂) := by
  have e : ws₂.map (VG.Proof.MlKem.X86_64.toR s₁) = ws₂.map (VG.Proof.MlKem.X86_64.toR s) := List.map_congr_left fun w hw => by simp only [VG.Proof.MlKem.X86_64.toR, h₁.pa (hb w hw)]
  have f₂ := h₂.frame
  rw [e, h₁.rsp] at f₂
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.bs r hr).trans (h₁.bs r hr), h₂.rsp.trans h₁.rsp,
    (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)⟩
  · rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ (by rw [List.map_append]; exact List.mem_append_left _ hr)
    · exact List.mem_append_right _ hr
  · rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ (by rw [List.map_append]; exact List.mem_append_right _ hr)
    · exact List.mem_append_right _ hr

theorem PPost.app {s s₁ s₂ : State} {ws₁ ws₂ : List (Ptr × Nat)} (h₁ : VG.Proof.MlKem.X86_64.PPost s s₁ ws₁) (h₂ : VG.Proof.MlKem.X86_64.PPost s₁ s₂ ws₂)
    (hcs : ∀ w ∈ ws₂, w.1.1 ∈ calleeSaved) : VG.Proof.MlKem.X86_64.PPost s s₂ (ws₁ ++ ws₂) :=
  PPost.trans h₁ h₂ hcs (fun _ hw => List.mem_append_left _ hw) (fun _ hw => List.mem_append_right _ hw)

/-! ## A byte -/

section
variable {rbs wbs : List (Reg × Nat)}

theorem bytesAt_one (m : Mem) (a : Addr) : bytesAt m a 1 = [m a] := by
  simp [bytesAt]

theorem setB_okL {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {p : Ptr} {v : Nat} (hr : p.1 ≠ .rax) (hv : v < 256)
    (hc : VG.Proof.MlKem.X86_64.inB wbs p 1 = true) :
    WP isa (.block (setB p v)) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(p, 1)] ∧ bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s p) 1 = [BitVec.ofNat 8 v] := by
  have hw : InRegions s.wr (VG.Proof.MlKem.X86_64.pa s p) 1 := L.cW hc _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (setB_ok p v hr hv s hw) fun s' ⟨hm, k⟩ => ⟨VG.Proof.MlKem.X86_64.post_of_keep k (by decide) ?_, ?_⟩
  · rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [hm, VG.Proof.MlKem.X86_64.bytesAt_one, VG.WriteBytes.writeW8_apply, ifp rfl]

/-! ## A copy -/

def copyChk (bs wbs : List (Reg × Nat)) (dst src : Ptr) (n : Nat) : Bool :=
  VG.Proof.MlKem.X86_64.wrOk bs wbs dst n && VG.Proof.MlKem.X86_64.rdOk bs src n && VG.Proof.MlKem.X86_64.sepB bs src n dst n && decide (0 < n) && decide (n < 2 ^ 31)

theorem copy_okL {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {dst src : Ptr} {n : Nat} (hsr : src.1 ≠ .rdi)
    (hc : VG.Proof.MlKem.X86_64.copyChk (rbs ++ wbs) wbs dst src n = true) :
    WP isa (copy dst src n) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' [(dst, n)] ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s dst) n = bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s src) n := by
  simp only [VG.Proof.MlKem.X86_64.copyChk, VG.Proof.MlKem.X86_64.wrOk, VG.Proof.MlKem.X86_64.rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hod, hid⟩, hwd⟩, hos, his⟩, hs⟩, hn0⟩, hn⟩ := hc
  have hrd : InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.pa s src) n := L.cR his _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  have hwr : InRegions s.wr (VG.Proof.MlKem.X86_64.pa s dst) n := L.cW hwd _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  exact WP.mono (copy_ok dst src n hn0 hn hod hos hsr s hrd hwr (L.disj hs))
    fun s' ⟨hb, hf, k⟩ => ⟨VG.Proof.MlKem.X86_64.post_of_keep k (by decide) hf, hb⟩

end

/-! ## The seed of `SampleNTT` -/

/-- What `SampleNTT` leaves, as `PostB`. -/
theorem SampPost.b {a : Ptr} {s s' : State} (h : VG.Proof.MlKem.X86_64.SampPost a s s') :
    VG.Proof.MlKem.X86_64.PPostB s s' [(a, 1024), (sc oSS, 2048)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [VG.Proof.MlKem.X86_64.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [VG.Proof.MlKem.X86_64.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

/-- The checks of `Â[i, j]`: its call, and the two bytes of the seed. -/
def ijChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  VG.Proof.MlKem.X86_64.sampChk bs wbs a && VG.Proof.MlKem.X86_64.inB wbs (sc (oSB + 32)) 1 && VG.Proof.MlKem.X86_64.inB wbs (sc (oSB + 33)) 1 &&
    VG.Proof.MlKem.X86_64.keepB bs [(sc (oSB + 32), 1)] (sc oSB) 32 && VG.Proof.MlKem.X86_64.keepB bs [(sc (oSB + 33), 1)] (sc oSB) 32 &&
    VG.Proof.MlKem.X86_64.keepB bs [(sc (oSB + 33), 1)] (sc (oSB + 32)) 1

theorem ijChk_spec {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : VG.Proof.MlKem.X86_64.ijChk bs wbs a = true) :
    VG.Proof.MlKem.X86_64.sampChk bs wbs a = true ∧ VG.Proof.MlKem.X86_64.inB wbs (sc (oSB + 32)) 1 = true ∧ VG.Proof.MlKem.X86_64.inB wbs (sc (oSB + 33)) 1 = true ∧
      VG.Proof.MlKem.X86_64.keepB bs [(sc (oSB + 32), 1)] (sc oSB) 32 = true ∧ VG.Proof.MlKem.X86_64.keepB bs [(sc (oSB + 33), 1)] (sc oSB) 32 = true ∧
      VG.Proof.MlKem.X86_64.keepB bs [(sc (oSB + 33), 1)] (sc (oSB + 32)) 1 = true := by
  simp only [VG.Proof.MlKem.X86_64.ijChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The two indices of the seed `ρ ‖ j ‖ i`. -/
theorem setIJ_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s)
    (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {i j : Nat} (hi : i < 256) (hj : j < 256) {a : Ptr}
    (hc : VG.Proof.MlKem.X86_64.ijChk (rbs ++ wbs) wbs a = true) :
    WP isa (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i)) s fun s' =>
      VG.Proof.MlKem.X86_64.PPost s s' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)]) ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s' (sc oSB)) 34 = matSeed (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (sc oSB)) 32) i j := by
  obtain ⟨_, h32, h33, k1, k2, k3⟩ := VG.Proof.MlKem.X86_64.ijChk_spec hc
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.setB_okL L (by decide) hj h32) fun s₁ ⟨hP₁, hb₁⟩ => ?_
  have L₁ := L.post hP₁.b hcs
  refine WP.mono (VG.Proof.MlKem.X86_64.setB_okL L₁ (by decide) hi h33) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have e1 : ∀ o, VG.Proof.MlKem.X86_64.pa s₁ (sc o) = VG.Proof.MlKem.X86_64.pa s (sc o) := fun o => hP₁.pa VG.Proof.MlKem.X86_64.rbx_cs
  have e2 : ∀ o, VG.Proof.MlKem.X86_64.pa s₂ (sc o) = VG.Proof.MlKem.X86_64.pa s₁ (sc o) := fun o => hP₂.pa VG.Proof.MlKem.X86_64.rbx_cs
  have hρ : bytesAt s₂.mem (VG.Proof.MlKem.X86_64.pa s₂ (sc oSB)) 32 = bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (sc oSB)) 32 := by
    rw [L₁.keepBytes hP₂.b k2, L.keepBytes hP₁.b k1]
  have hjb : bytesAt s₂.mem (VG.Proof.MlKem.X86_64.pa s₂ (sc (oSB + 32))) 1 = [BitVec.ofNat 8 j] := by
    rw [L₁.keepBytes hP₂.b k3, e1]; exact hb₁
  have hib : bytesAt s₂.mem (VG.Proof.MlKem.X86_64.pa s₂ (sc (oSB + 33))) 1 = [BitVec.ofNat 8 i] := by
    rw [e2]; exact hb₂
  refine ⟨PPost.app hP₁ hP₂ (by decide), seed_eq hρ ?_ ?_⟩
  · refine mem_of_bytesAt_one ?_; rw [← hjb, VG.Proof.MlKem.X86_64.pa, VG.Proof.MlKem.X86_64.pa, off_add]
  · refine mem_of_bytesAt_one ?_; rw [← hib, VG.Proof.MlKem.X86_64.pa, VG.Proof.MlKem.X86_64.pa, off_add]

theorem sampleIJ_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s)
    (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {a : Ptr} (hna : VG.Proof.MlKem.X86_64.NA a) {i j : Nat} (hi : i < 256)
    (hj : j < 256) (hc : VG.Proof.MlKem.X86_64.ijChk (rbs ++ wbs) wbs a = true) :
    WP isa (sampleIJ a i j) s fun s' =>
      VG.Proof.MlKem.X86_64.PPostB s s' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)] ++ [(a, 1024), (sc oSS, 2048)]) ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (sampleNTT minIterations (matSeed (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (sc oSB)) 32) i j)).isSome then 1 else 0)) ∧
      ∀ f, sampleNTT minIterations (matSeed (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (sc oSB)) 32) i j) = some f →
        PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s a) f := by
  unfold sampleIJ
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.setIJ_ok L hcs hi hj hc) fun s₂ ⟨hP₂, hseed⟩ => ?_
  have L₂ := L.post hP₂.b hcs
  refine WP.mono (VG.Proof.MlKem.X86_64.sampleAt_ok hna (SampH.of L₂ (VG.Proof.MlKem.X86_64.ijChk_spec hc).1)) fun s₃ h => ?_
  have hab : a.1 ∈ VG.Proof.MlKem.X86_64.bases := by
    obtain ⟨n, hn, _⟩ := VG.Proof.MlKem.X86_64.inB_spec (VG.Proof.MlKem.X86_64.sampChk_in (VG.Proof.MlKem.X86_64.ijChk_spec hc).1).2
    exact hcs (a.1, n) hn
  have e3 : VG.Proof.MlKem.X86_64.pa s₂ a = VG.Proof.MlKem.X86_64.pa s a := hP₂.b.pa hab
  refine ⟨PPostB.app hP₂.b h.b (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    exacts [hab, by decide]), ?_, fun f hf => ?_⟩
  · rw [h.r15, hseed, hP₂.cs .r15 (by decide)]
  · rw [← e3]; exact h.res f (by rw [hseed]; exact hf)

theorem sampleIJ_tr {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {a : Ptr} (hna : VG.Proof.MlKem.X86_64.NA a)
    {i j : Nat} (hi : i < 256) (hj : j < 256) (hc : VG.Proof.MlKem.X86_64.ijChk (rbs ++ wbs) wbs a = true)
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i))
      (.block [])).isSome = true) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (sc oSB)) 32 = bytesAt y.mem (VG.Proof.MlKem.X86_64.pa y (sc oSB)) 32)
      (sampleIJ a i j) fun _ _ => True := by
  have hin : VG.Proof.MlKem.X86_64.inB (rbs ++ wbs) (sc oSB) 34 = true := (VG.Proof.MlKem.X86_64.sampChk_in (VG.Proof.MlKem.X86_64.ijChk_spec hc).1).1
  unfold sampleIJ
  refine RelCT.seq (RelCT.postDep (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1.eq hin) ht)
    (F := fun x x' => VG.Proof.MlKem.X86_64.PPost x x' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)]) ∧
      bytesAt x'.mem (VG.Proof.MlKem.X86_64.pa x' (sc oSB)) 34 = matSeed (bytesAt x.mem (VG.Proof.MlKem.X86_64.pa x (sc oSB)) 32) i j)
    (fun x y h => ⟨VG.Proof.MlKem.X86_64.setIJ_ok h.1.1 hcs hi hj hc, VG.Proof.MlKem.X86_64.setIJ_ok h.1.2.1 hcs hi hj hc⟩)
    fun x y x' y' h hx hy => ⟨h.1.post hcs hx.1.b hy.1.b, by rw [hx.2, hy.2, h.2]⟩)
    (VG.Proof.MlKem.X86_64.sampleAt_trL hna (VG.Proof.MlKem.X86_64.ijChk_spec hc).1)

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.FragC`. -/
section

/-!
# ML-KEM on x86-64: the input of `PRF`, and sequences in a layout

In a layout: the input of `PRF₂(σ, N)` (`prf_pieces`, for `Prfs.lean`), and
two pieces of code in sequence, for constant time (`RelCT.seqL`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem keepB_sub {bs : List (Reg × Nat)} {ws ws' : List (Ptr × Nat)} {p : Ptr} {l : Nat}
    (h : VG.Proof.MlKem.X86_64.keepB bs ws p l = true) (hs : ∀ w ∈ ws', w ∈ ws) : VG.Proof.MlKem.X86_64.keepB bs ws' p l = true := by
  simp only [VG.Proof.MlKem.X86_64.keepB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun w hw => h.2 w (hs w hw)⟩

/-! ## `PRF₂(σ, N)` -/

theorem shake31 : BitVec.ofNat 8 0x1f = Spec.Sha3.shakeSuffix := by decide

/-- The bytes absorbed: `σ ‖ N`. -/
theorem prf_pieces {s : State} {N : Nat} (hN : bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s (sc oNB)) 1 = [BitVec.ofNat 8 N]) :
    VG.Proof.MlKem.X86_64.pieces s [(sigP, 32), (sc oNB, 1)] = bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s sigP) 32 ++ [BitVec.ofNat 8 N] := by
  simp only [VG.Proof.MlKem.X86_64.pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hN]

/-! ## Sequences, for constant time -/

/-- Two pieces of code in sequence, from two runs in a layout that satisfy
`I` (what the first piece needs), each piece leaving the layout. -/
theorem RelCT.seqL {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {c₁ c₂ : Prog isa}
    {I J : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ I x ∧ I y) c₁ fun _ _ => True)
    (w₁ : ∀ x, VG.Proof.MlKem.X86_64.Lay rbs wbs x → I x → WP isa c₁ x fun x' => (∃ W, VG.Proof.MlKem.X86_64.PostB x x' W) ∧ J x')
    (h₂ : RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ J x ∧ J y) c₂ Q) :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ I x ∧ I y) (.seq c₁ c₂) Q :=
  RelCT.seq (RelCT.postDep h₁ (F := fun x x' => (∃ W, VG.Proof.MlKem.X86_64.PostB x x' W) ∧ J x')
    (fun x y h => ⟨w₁ x h.1.1 h.2.1, w₁ y h.1.2.1 h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post hcs hx hy, jx, jy⟩) h₂

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.Dot`. -/
section

/-!
# ML-KEM on x86-64: sums of products

`a₀ ×_T b₀ + ⋯ + a_{n-1} ×_T b_{n-1}` to polynomial 15 (`dotN`), proven for
every `n` by induction (`dotN_ok`, `dotN_tr`): `KPke.dotK`, accumulated left
to right.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The polynomials a sum of products writes. -/
abbrev W3 : List (Ptr × Nat) := [(pS 15, 1024), (pS 16, 1024), (sc oSS, 1024)]

/-- What a sum of `n` products writes. -/
def dotW : Nat → List (Ptr × Nat)
  | 0 => []
  | 1 => [(pS 15, 1024), (sc oSS, 1024)]
  | n + 2 => VG.Proof.MlKem.X86_64.dotW (n + 1) ++ [(pS 16, 1024), (sc oSS, 1024)] ++ [(pS 15, 1024)]

theorem dotW_W3 : ∀ n, ∀ w ∈ VG.Proof.MlKem.X86_64.dotW n, w ∈ VG.Proof.MlKem.X86_64.W3
  | 0 => fun _ h => absurd h List.not_mem_nil
  | 1 => by decide
  | n + 2 => fun w hw => by
    simp only [VG.Proof.MlKem.X86_64.dotW, List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · exact VG.Proof.MlKem.X86_64.dotW_W3 (n + 1) w hw
    · revert w; decide
    · revert w; decide

/-- The checks of a sum of `n` products of `f k` and `g k`. -/
def dotChk (bs wbs : List (Reg × Nat)) (f g : Nat → Ptr) (n : Nat) : Bool :=
  (List.range n).all (fun k => VG.Proof.MlKem.X86_64.keepB bs VG.Proof.MlKem.X86_64.W3 (f k) 1024 && VG.Proof.MlKem.X86_64.keepB bs VG.Proof.MlKem.X86_64.W3 (g k) 1024 && decide (VG.Proof.MlKem.X86_64.NA (f k)) &&
      decide (VG.Proof.MlKem.X86_64.NA (g k))) &&
    VG.Proof.MlKem.X86_64.mulChk bs wbs (pS 15) (f 0) (g 0) && (List.range n).all (fun k => VG.Proof.MlKem.X86_64.mulChk bs wbs (pS 16) (f k) (g k)) &&
    VG.Proof.MlKem.X86_64.accChk bs wbs (pS 15) (pS 16) && VG.Proof.MlKem.X86_64.keepB bs [(pS 16, 1024), (sc oSS, 1024)] (pS 15) 1024

/-- `dotChk`, as facts. -/
structure DotChks (bs wbs : List (Reg × Nat)) (f g : Nat → Ptr) (n : Nat) : Prop where
  k : ∀ k < n, VG.Proof.MlKem.X86_64.keepB bs VG.Proof.MlKem.X86_64.W3 (f k) 1024 = true ∧ VG.Proof.MlKem.X86_64.keepB bs VG.Proof.MlKem.X86_64.W3 (g k) 1024 = true ∧ VG.Proof.MlKem.X86_64.NA (f k) ∧ VG.Proof.MlKem.X86_64.NA (g k)
  m0 : VG.Proof.MlKem.X86_64.mulChk bs wbs (pS 15) (f 0) (g 0) = true
  m : ∀ k < n, VG.Proof.MlKem.X86_64.mulChk bs wbs (pS 16) (f k) (g k) = true
  acc : VG.Proof.MlKem.X86_64.accChk bs wbs (pS 15) (pS 16) = true
  k15 : VG.Proof.MlKem.X86_64.keepB bs [(pS 16, 1024), (sc oSS, 1024)] (pS 15) 1024 = true

theorem dotChk_spec {bs wbs : List (Reg × Nat)} {f g : Nat → Ptr} {n : Nat} (h : VG.Proof.MlKem.X86_64.dotChk bs wbs f g n = true) :
    VG.Proof.MlKem.X86_64.DotChks bs wbs f g n := by
  simp only [VG.Proof.MlKem.X86_64.dotChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun k hk => by have := h0 k hk; exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩, h1, h2, h3, h4⟩

theorem DotChks.mono {bs wbs : List (Reg × Nat)} {f g : Nat → Ptr} {n n' : Nat} (h : VG.Proof.MlKem.X86_64.DotChks bs wbs f g n)
    (hn : n' ≤ n) : VG.Proof.MlKem.X86_64.DotChks bs wbs f g n' :=
  ⟨fun k hk => h.k k (by omega), h.m0, fun k hk => h.m k (by omega), h.acc, h.k15⟩

/-- The sum of products `a₀ b₀ + ⋯ + a_{n-1} b_{n-1}`, accumulated left to right. -/
theorem dotN_ok {A : Arith} (hA : VG.Proof.MlKem.X86_64.ArithOk A) {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases)
    {f g : Nat → Ptr} {a b : Nat → Poly} :
    ∀ {n : Nat}, 0 < n → VG.Proof.MlKem.X86_64.DotChks (rbs ++ wbs) wbs f g n → ∀ {s : State}, VG.Proof.MlKem.X86_64.Lay rbs wbs s →
      (∀ k < n, PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (f k)) (a k)) → (∀ k < n, PolyIs s.mem (VG.Proof.MlKem.X86_64.pa s (g k)) (b k)) →
      WP isa (dotN A f g n) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' (VG.Proof.MlKem.X86_64.dotW n) ∧ PolyIs s'.mem (VG.Proof.MlKem.X86_64.pa s (pS 15)) (KPke.dotK a b n)
  | 0, h, _, _, _, _, _ => absurd h (Nat.lt_irrefl 0)
  | 1, _, hc, s, L, ha, hb => by
    refine WP.mono (VG.Proof.MlKem.X86_64.mulAt_okL hA L (hc.k 0 (by decide)).2.2.1 (hc.k 0 (by decide)).2.2.2 hc.m0 (ha 0 (by decide)).1
      (hb 0 (by decide)).1) fun s₁ ⟨hP₁, hp₁⟩ => ⟨hP₁, ?_⟩
    rw [(ha 0 (by decide)).2, (hb 0 (by decide)).2] at hp₁
    exact hp₁
  | n + 2, _, hc, s, L, ha, hb => by
    have W3s : ∀ {ws : List (Ptr × Nat)}, (∀ w ∈ ws, w ∈ VG.Proof.MlKem.X86_64.W3) → ∀ k < n + 2,
        VG.Proof.MlKem.X86_64.keepB (rbs ++ wbs) ws (f k) 1024 = true ∧ VG.Proof.MlKem.X86_64.keepB (rbs ++ wbs) ws (g k) 1024 = true :=
      fun hws k hk => ⟨VG.Proof.MlKem.X86_64.keepB_sub (hc.k k hk).1 hws, VG.Proof.MlKem.X86_64.keepB_sub (hc.k k hk).2.1 hws⟩
    refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.dotN_ok hA hcs (n := n + 1) (by omega) (hc.mono (by omega)) L
      (fun k hk => ha k (by omega)) (fun k hk => hb k (by omega))) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
    have L₁ := L.post hP₁.b hcs
    have ha₁ := L.keepPoly hP₁.b (W3s (VG.Proof.MlKem.X86_64.dotW_W3 _) (n + 1) (by omega)).1 (ha (n + 1) (by omega))
    have hb₁ := L.keepPoly hP₁.b (W3s (VG.Proof.MlKem.X86_64.dotW_W3 _) (n + 1) (by omega)).2 (hb (n + 1) (by omega))
    rw [← hP₁.pa VG.Proof.MlKem.X86_64.rbx_cs] at hp₁
    refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.mulAt_okL hA L₁ (hc.k (n + 1) (by omega)).2.2.1 (hc.k (n + 1) (by omega)).2.2.2
      (hc.m (n + 1) (by omega)) ha₁.1 hb₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
    have L₂ := L₁.post hP₂.b hcs
    rw [ha₁.2, hb₁.2, ← hP₂.pa VG.Proof.MlKem.X86_64.rbx_cs] at hp₂
    have hq₂ := L₁.keepPoly hP₂.b hc.k15 hp₁
    refine WP.mono (VG.Proof.MlKem.X86_64.addAt_ok L₂ VG.Proof.MlKem.X86_64.rbx_na hc.acc hq₂.1 hp₂.1) fun s₃ ⟨hP₃, hp₃⟩ =>
      ⟨PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide), ?_⟩
    rw [hq₂.2, hp₂.2, hP₂.pa VG.Proof.MlKem.X86_64.rbx_cs, hP₁.pa VG.Proof.MlKem.X86_64.rbx_cs] at hp₃
    exact hp₃

/-- The inputs of a sum of `n` products, reduced. -/
abbrev DotIn (f g : Nat → Ptr) (n : Nat) (s : State) : Prop :=
  ∀ k < n, Reduced s.mem (VG.Proof.MlKem.X86_64.pa s (f k)) ∧ Reduced s.mem (VG.Proof.MlKem.X86_64.pa s (g k))

theorem dotN_tr {A : Arith} (hA : VG.Proof.MlKem.X86_64.ArithOk A) {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases)
    {f g : Nat → Ptr} : ∀ {n : Nat}, 0 < n → VG.Proof.MlKem.X86_64.DotChks (rbs ++ wbs) wbs f g n →
      RelCT isa (fun x y => VG.Proof.MlKem.X86_64.LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.DotIn f g n x ∧ VG.Proof.MlKem.X86_64.DotIn f g n y) (dotN A f g n) fun _ _ => True
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | 1, _, hc => RelCT.mono (VG.Proof.MlKem.X86_64.mulAt_trL hA (hc.k 0 (by decide)).2.2.1 (hc.k 0 (by decide)).2.2.2 hc.m0)
      (fun _ _ ⟨e, i1, i2⟩ => ⟨e, i1 0 (by decide), i2 0 (by decide)⟩) fun _ _ _ => trivial
  | n + 2, _, hc => by
    have keep : ∀ {x x' : State} {ws : List (Ptr × Nat)}, VG.Proof.MlKem.X86_64.Lay rbs wbs x → VG.Proof.MlKem.X86_64.PPostB x x' ws → (∀ w ∈ ws, w ∈ VG.Proof.MlKem.X86_64.W3) →
        VG.Proof.MlKem.X86_64.DotIn f g (n + 2) x → VG.Proof.MlKem.X86_64.DotIn f g (n + 2) x' := fun Lx hP hws hi k hk =>
      ⟨Lx.keepRed hP (VG.Proof.MlKem.X86_64.keepB_sub (hc.k k hk).1 hws) (hi k hk).1, Lx.keepRed hP (VG.Proof.MlKem.X86_64.keepB_sub (hc.k k hk).2.1 hws) (hi k hk).2⟩
    refine RelCT.seqL (J := fun x => VG.Proof.MlKem.X86_64.DotIn f g (n + 2) x ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (pS 15))) hcs
      (RelCT.mono (VG.Proof.MlKem.X86_64.dotN_tr hA hcs (n := n + 1) (by omega) (hc.mono (by omega)))
        (fun _ _ ⟨e, i1, i2⟩ => ⟨e, fun k hk => i1 k (by omega), fun k hk => i2 k (by omega)⟩) fun _ _ _ => trivial)
      (fun x Lx hi => WP.mono (VG.Proof.MlKem.X86_64.dotN_ok hA hcs (a := fun k => polyAt x.mem (VG.Proof.MlKem.X86_64.pa x (f k)))
        (b := fun k => polyAt x.mem (VG.Proof.MlKem.X86_64.pa x (g k))) (n := n + 1) (by omega) (hc.mono (by omega)) Lx
        (fun k hk => ⟨(hi k (by omega)).1, rfl⟩) (fun k hk => ⟨(hi k (by omega)).2, rfl⟩))
        fun x' ⟨hP, hp⟩ => ⟨⟨_, hP.b⟩, keep Lx hP.b (VG.Proof.MlKem.X86_64.dotW_W3 _) hi, by rw [hP.pa VG.Proof.MlKem.X86_64.rbx_cs]; exact hp.1⟩) ?_
    refine RelCT.seqL (J := fun x => Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (pS 15)) ∧ Reduced x.mem (VG.Proof.MlKem.X86_64.pa x (pS 16))) hcs
      (RelCT.mono (VG.Proof.MlKem.X86_64.mulAt_trL hA (hc.k (n + 1) (by omega)).2.2.1 (hc.k (n + 1) (by omega)).2.2.2
          (hc.m (n + 1) (by omega)))
        (fun _ _ ⟨e, i1, i2⟩ => ⟨e, i1.1 (n + 1) (by omega), i2.1 (n + 1) (by omega)⟩) fun _ _ _ => trivial)
      (fun x Lx hi => WP.mono (VG.Proof.MlKem.X86_64.mulAt_okL hA Lx (hc.k (n + 1) (by omega)).2.2.1 (hc.k (n + 1) (by omega)).2.2.2
        (hc.m (n + 1) (by omega)) (hi.1 (n + 1) (by omega)).1 (hi.1 (n + 1) (by omega)).2) fun x' ⟨hP, hp⟩ =>
          ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hc.k15 hi.2, by rw [hP.pa VG.Proof.MlKem.X86_64.rbx_cs]; exact hp.1⟩) ?_
    exact RelCT.mono (VG.Proof.MlKem.X86_64.addAt_tr VG.Proof.MlKem.X86_64.rbx_na hc.acc) (fun _ _ ⟨e, i1, i2⟩ => ⟨e, i1, i2⟩) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.S4Base`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the layout

The contract the proof is written against (`sample4K`), what holds between the
pieces of the function (`Env`, relative to the entry state `σ`), and the
prologue.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mlkem_sample_ntt4_avx2(seeds = rdi, a = rsi, scratch = rdx) -> eax`,
with 24 bytes of stack below `rsp`. -/
def sample4K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 136⟩] ∧ s.wr = [⟨s.gpr .rsi, 4096⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 136⟩ ⟨s.gpr .rsi, 4096⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 136⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 4096⟩ ⟨s.gpr .rdx, 8192⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 136⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 4096⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdi, 136⟩ ∧ (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rsi, 4096⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rsi).toNat + 4096 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    (s'.gpr .rax).setWidth 32 =
        (if (List.range 4).all fun k => (sampleNTT minIterations (seed4 s.mem (s.gpr .rdi) k)).isSome
          then 1 else 0) ∧
      ∀ k < 4, ∀ f, sampleNTT minIterations (seed4 s.mem (s.gpr .rdi) k) = some f →
        PolyIs s'.mem (poly4 (s.gpr .rsi) k) f
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ bytesAt s₁.mem (s₁.gpr .rdi) 136 = bytesAt s₂.mem (s₂.gpr .rdi) 136

namespace S4

open VG.Impl.MlKem.X86_64.Sample4

section
variable (σ : State)
abbrev sd : Addr := σ.gpr .rdi
abbrev aP : Addr := σ.gpr .rsi
abbrev scr : Addr := σ.gpr .rdx
/-- Seed `k`. -/
abbrev B (k : Nat) : List Byte := seed4 σ.mem (VG.Proof.MlKem.X86_64.S4.sd σ) k
abbrev sdR : Region := ⟨VG.Proof.MlKem.X86_64.S4.sd σ, 136⟩
abbrev aR : Region := ⟨VG.Proof.MlKem.X86_64.S4.aP σ, 4096⟩
abbrev scrR : Region := ⟨VG.Proof.MlKem.X86_64.S4.scr σ, 8192⟩
abbrev stkR : Region := below (σ.gpr .rsp) 24
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := VG.Proof.MlKem.X86_64.S4.scr σ + BitVec.ofNat 64 off
end

/-- The precondition, by name. -/
structure Pre (σ : State) : Prop where
  rd : σ.rd = [VG.Proof.MlKem.X86_64.S4.sdR σ]
  wr : σ.wr = [VG.Proof.MlKem.X86_64.S4.aR σ, VG.Proof.MlKem.X86_64.S4.scrR σ]
  sd_a : (VG.Proof.MlKem.X86_64.S4.sdR σ).Disjoint (VG.Proof.MlKem.X86_64.S4.aR σ)
  sd_scr : (VG.Proof.MlKem.X86_64.S4.sdR σ).Disjoint (VG.Proof.MlKem.X86_64.S4.scrR σ)
  a_scr : (VG.Proof.MlKem.X86_64.S4.aR σ).Disjoint (VG.Proof.MlKem.X86_64.S4.scrR σ)
  ret_sd : (retR σ).Disjoint (VG.Proof.MlKem.X86_64.S4.sdR σ)
  ret_a : (retR σ).Disjoint (VG.Proof.MlKem.X86_64.S4.aR σ)
  ret_scr : (retR σ).Disjoint (VG.Proof.MlKem.X86_64.S4.scrR σ)
  stk_sd : (VG.Proof.MlKem.X86_64.S4.stkR σ).Disjoint (VG.Proof.MlKem.X86_64.S4.sdR σ)
  stk_a : (VG.Proof.MlKem.X86_64.S4.stkR σ).Disjoint (VG.Proof.MlKem.X86_64.S4.aR σ)
  stk_scr : (VG.Proof.MlKem.X86_64.S4.stkR σ).Disjoint (VG.Proof.MlKem.X86_64.S4.scrR σ)
  a_lt : (VG.Proof.MlKem.X86_64.S4.aP σ).toNat + 4096 ≤ 2 ^ 64
  scr_lt : (VG.Proof.MlKem.X86_64.S4.scr σ).toNat + 8192 ≤ 2 ^ 64

theorem pre_of {σ : State} (h : sample4K.pre σ) : VG.Proof.MlKem.X86_64.S4.Pre σ :=
  let ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- What holds between the pieces. -/
structure Env (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rbx : s.gpr .rbx = VG.Proof.MlKem.X86_64.S4.scr σ
  r12 : s.gpr .r12 = VG.Proof.MlKem.X86_64.S4.sd σ
  r13 : s.gpr .r13 = VG.Proof.MlKem.X86_64.S4.aP σ
  rsp : s.gpr .rsp = σ.gpr .rsp
  r15 : s.gpr .r15 = σ.gpr .r15
  saved : ∀ i < 5, s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (oSave + 8 * i)) 64 = σ.gpr (saved.getD i .rbx)
  frame : Frame [VG.Proof.MlKem.X86_64.S4.aR σ, VG.Proof.MlKem.X86_64.S4.scrR σ, VG.Proof.MlKem.X86_64.S4.stkR σ] σ.mem s.mem

section
variable {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ)
include hp

omit hp in
theorem sub_scr {a n : Nat} (h : a + n ≤ 8192) : Region.Sub ⟨VG.Proof.MlKem.X86_64.S4.at' σ a, n⟩ (VG.Proof.MlKem.X86_64.S4.scrR σ) := Offset.sub_base _ h

omit hp in
theorem sub_a {a n : Nat} (h : a + n ≤ 4096) : Region.Sub ⟨VG.Proof.MlKem.X86_64.S4.aP σ + BitVec.ofNat 64 a, n⟩ (VG.Proof.MlKem.X86_64.S4.aR σ) :=
  Offset.sub_base _ h

theorem in_scr {s : State} (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 8192) : InRegions s.wr (VG.Proof.MlKem.X86_64.S4.at' σ a) n := by
  rw [hw, hp.wr]; exact ⟨VG.Proof.MlKem.X86_64.S4.scrR σ, by simp, Offset.contains_base _ h (by omega)⟩

theorem in_scr' {s : State} (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.S4.at' σ a) n := by
  rw [hr, hw, hp.rd, hp.wr]; exact ⟨VG.Proof.MlKem.X86_64.S4.scrR σ, by simp, Offset.contains_base _ h (by omega)⟩

theorem in_sd' {s : State} (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 136) :
    InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 a) n := by
  rw [hr, hw, hp.rd, hp.wr]; exact ⟨VG.Proof.MlKem.X86_64.S4.sdR σ, by simp, Offset.contains_base _ h (by omega)⟩

/-- The seeds are not written. -/
theorem seeds_frame {m : Mem} (hf : Frame [VG.Proof.MlKem.X86_64.S4.aR σ, VG.Proof.MlKem.X86_64.S4.scrR σ, VG.Proof.MlKem.X86_64.S4.stkR σ] σ.mem m) {a : Nat} (ha : a < 136) :
    m (VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 a) = σ.mem (VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 a) :=
  hf.bytes (R := VG.Proof.MlKem.X86_64.S4.sdR σ) (by simpa using ⟨hp.sd_a, hp.sd_scr, hp.stk_sd.symm⟩) (by simp) ha

/-- Byte `a` of seed `k`. -/
theorem seed_byte {m : Mem} (hf : Frame [VG.Proof.MlKem.X86_64.S4.aR σ, VG.Proof.MlKem.X86_64.S4.scrR σ, VG.Proof.MlKem.X86_64.S4.stkR σ] σ.mem m) {k a : Nat} (hk : k < 4) (ha : a < 34) :
    m (VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 (34 * k + a)) = (VG.Proof.MlKem.X86_64.S4.B σ k).getD a 0 := by
  rw [VG.Proof.MlKem.X86_64.S4.seeds_frame hp hf (by omega), VG.Proof.MlKem.X86_64.S4.B, seed4, ← Offset.add_add]
  simp [bytesAt, ha]

end

/-! ## The prologue -/

/-- A read of 8 bytes at `scratch + d` after a write of 8 elsewhere. -/
theorem rd64_off {σ : State} {m : Mem} {d e : Nat} {v : BitVec 64} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) : (m.writeW (VG.Proof.MlKem.X86_64.S4.at' σ e) v).readW (VG.Proof.MlKem.X86_64.S4.at' σ d) 64 = m.readW (VG.Proof.MlKem.X86_64.S4.at' σ d) 64 :=
  readW_writeW_off m _ v (n := 8) (by omega) (by omega) h

theorem pro_eq : pro = [.store (at_ .rdx 4384) .rbx, .store (at_ .rdx 4392) .rbp, .store (at_ .rdx 4400) .r12,
    .store (at_ .rdx 4408) .r13, .store (at_ .rdx 4416) .r14, .mov .rbx (.reg .rdx), .mov .r12 (.reg .rdi),
    .mov .r13 (.reg .rsi), .mov32 .r14 (.imm 1)] := rfl

/-- After the prologue. -/
structure I0 (σ s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.S4.Env σ s
  r14 : s.gpr .r14 = 1

theorem pro_ok {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) : WP isa (.block pro) σ (VG.Proof.MlKem.X86_64.S4.I0 σ) := by
  rw [VG.Proof.MlKem.X86_64.S4.pro_eq]
  refine WP.mono (WP.keep [.rbx, .r12, .r13, .r14] (Q := fun s =>
      s.mem = ((((σ.mem.writeW (VG.Proof.MlKem.X86_64.S4.at' σ 4384) (σ.gpr .rbx)).writeW (VG.Proof.MlKem.X86_64.S4.at' σ 4392) (σ.gpr .rbp)).writeW (VG.Proof.MlKem.X86_64.S4.at' σ 4400)
          (σ.gpr .r12)).writeW (VG.Proof.MlKem.X86_64.S4.at' σ 4408) (σ.gpr .r13)).writeW (VG.Proof.MlKem.X86_64.S4.at' σ 4416) (σ.gpr .r14) ∧
        s.gpr .rbx = VG.Proof.MlKem.X86_64.S4.scr σ ∧ s.gpr .r12 = VG.Proof.MlKem.X86_64.S4.sd σ ∧ s.gpr .r13 = VG.Proof.MlKem.X86_64.S4.aP σ ∧ s.gpr .r14 = 1)
    (by xrun [VG.Proof.MlKem.X86_64.S4.in_scr hp rfl (a := 4384) (n := 8) (by omega), VG.Proof.MlKem.X86_64.S4.in_scr hp rfl (a := 4392) (n := 8) (by omega),
      VG.Proof.MlKem.X86_64.S4.in_scr hp rfl (a := 4400) (n := 8) (by omega), VG.Proof.MlKem.X86_64.S4.in_scr hp rfl (a := 4408) (n := 8) (by omega),
      VG.Proof.MlKem.X86_64.S4.in_scr hp rfl (a := 4416) (n := 8) (by omega)])
    (by decide)) fun s1 ⟨⟨hm1, hbx, h12, h13, h14⟩, k1⟩ => ⟨⟨k1.2.1, k1.2.2, hbx, h12, h13,
      k1.gpr (by decide), k1.gpr (by decide), fun i hi => ?_, ?_⟩, h14⟩
  · rw [hm1]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := omega) only [oSave, Mem.readW_writeW_self64, VG.Proof.MlKem.X86_64.S4.rd64_off, Nat.reduceMul, Nat.reduceAdd] <;> rfl
  · rw [hm1]
    have hin : ∀ a, a + 8 ≤ 8192 → (VG.Proof.MlKem.X86_64.S4.scrR σ).Contains (VG.Proof.MlKem.X86_64.S4.at' σ a) (64 / 8) := fun a ha =>
      Offset.contains_base _ (by omega) (by omega)
    exact ((((((Frame.refl _ _).writeW (by simp) _ (hin 4384 (by omega))).writeW (by simp) _
      (hin 4392 (by omega))).writeW (by simp) _ (hin 4400 (by omega))).writeW (by simp) _
      (hin 4408 (by omega))).writeW (by simp) _ (hin 4416 (by omega)))

end S4

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.S4Absorb`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the round constants and the padded seeds

After the prologue, the table of the round constants (`rc_ok`), and the four
states holding the padded seeds, byte by byte (`absorb_ok`).
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Proof.Sha3.X86_64.X4 (q4 VUpd la ba Lanes4 wp_vmovq wp_vbcast wp_vst wp_vxor readW_write256 q4_ymm)
open VG.Proof.Sha3.X86_64 (wp_movi64)

/-- `Env` after writes below the saved registers. -/
theorem Env.write {σ s s' : State} (he : VG.Proof.MlKem.X86_64.S4.Env σ s) {a n : Nat} (h : a + n ≤ oSave)
    (hf : Frame [⟨VG.Proof.MlKem.X86_64.S4.at' σ a, n⟩] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) : VG.Proof.MlKem.X86_64.S4.Env σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using Offset.disjoint (VG.Proof.MlKem.X86_64.S4.scr σ) (d := oSave + 8 * i) (n := 8) (e := a) (k := n) (by simp only [oSave] at h ⊢; omega)
          (by simp only [oSave]; omega) (by simp only [oSave] at h; omega)) (by decide)]
    exact he.saved i hi
  · refine he.frame.trans (hf.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.MlKem.X86_64.S4.scrR σ, by simp, Offset.sub_base _ (by simp only [oSave] at h; omega)⟩

/-! ## Bytes written -/

/-- A byte of a write at `p + e`. -/
theorem wb_in (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {e d : Nat} (h₁ : e ≤ d) (h₂ : 8 * (d - e + 1) ≤ w)
    (hw : w < 2 ^ 64) : (m.writeW (p + BitVec.ofNat 64 e) v) (p + BitVec.ofNat 64 d) = v.extractLsb' (8 * (d - e)) 8 := by
  rw [← writeW_byte m _ v h₂ hw, Offset.add_add, Nat.add_sub_cancel' h₁]

/-- A byte outside a write at `p + e`. -/
theorem wb_out (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {e d : Nat} (h : d < e ∨ e + w / 8 ≤ d)
    (hd : d < 2 ^ 63) (he : e + w / 8 < 2 ^ 63) :
    (m.writeW (p + BitVec.ofNat 64 e) v) (p + BitVec.ofNat 64 d) = m (p + BitVec.ofNat 64 d) := by
  refine writeW_byte_off _ _ _ _ ?_
  rw [Offset.sub_toNat' _ (by bdd_omega) (by bdd_omega)]
  split <;> omega

/-! ## The round constants -/

/-- After the first `n` round constants. -/
structure RcInv (σ s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep [.rax] s₀ s
  frame : Frame [⟨VG.Proof.MlKem.X86_64.S4.at' σ oRc, 768⟩] s₀.mem s.mem
  rc : ∀ r < n, ∀ k < 4, s.mem.readW (la (VG.Proof.MlKem.X86_64.S4.scr σ) (50 + r) k) 64 = Spec.Sha3.RC r

theorem rc_step {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {s₀ : State} (he : VG.Proof.MlKem.X86_64.S4.Env σ s₀) {r : Nat} (hr : r < 24) {s : State}
    (h : VG.Proof.MlKem.X86_64.S4.RcInv σ s₀ r s) :
    WP isa (.block [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax),
      .vop (.vpbroadcastq .l256 .xmm0 .xmm0), Impl.Sha3.X86_64.X4.st .rbx (oRc / 32 + r) .xmm0]) s
      (VG.Proof.MlKem.X86_64.S4.RcInv σ s₀ (r + 1)) := by
  have hbx : s.gpr .rbx = VG.Proof.MlKem.X86_64.S4.scr σ := by rw [h.keep.gpr (by decide), he.rbx]
  refine wp_movi64 fun s₁ u₁ => wp_vmovq fun s₂ u₂ => wp_vbcast fun s₃ u₃ =>
    wp_vst (a := VG.Proof.MlKem.X86_64.S4.at' σ (32 * (50 + r))) (by rw [VG.Proof.Sha3.X86_64.ea_at, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hbx]; rfl)
      (by rw [u₃.wr, u₂.wr, u₁.wr, h.keep.2.2, he.wr]; exact VG.Proof.MlKem.X86_64.S4.in_scr hp rfl (by bdd_omega))
      fun s₄ g₄ _ m₄ r₄ w₄ => VG.Proof.Sha3.X86_64.wp_nil ?_
  have hv : ∀ k < 4, q4 s₃ .xmm0 k = Spec.Sha3.RC r := fun k hk => by
    rw [u₃.val k hk, u₂.val 0 (by decide), ite_eq_left rfl, u₁.gpr]
  have hm : s₄.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.S4.at' σ (32 * (50 + r))) (s₃.ymm .xmm0) := by rw [m₄, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨⟨fun g hg => by rw [g₄, u₃.gpr, u₂.gpr, u₁.other g (by simpa using hg), h.keep.gpr hg],
      by rw [r₄, u₃.rd, u₂.rd, u₁.rd, h.keep.2.1], by rw [w₄, u₃.wr, u₂.wr, u₁.wr, h.keep.2.2]⟩, ?_,
    fun r' hr' k hk => ?_⟩
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by simp only [oRc]; omega)
      (by simp only [oRc]; omega) (by simp only [oRc]; omega))
  · rw [hm]
    by_cases e : r' = r
    · subst e
      rw [la, ← Offset.add_add, readW_write256 _ _ _ hk, q4_ymm _ _ hk, hv k hk]
    · have e := readW_writeW_off s.mem (VG.Proof.MlKem.X86_64.S4.scr σ) (s₃.ymm .xmm0) (d := 32 * (50 + r') + 8 * k)
        (e := 32 * (50 + r)) (n := 8) (by bdd_omega) (by bdd_omega) (by bdd_omega)
      exact e.trans (h.rc r' (by bdd_omega) k hk)

theorem rcTable_eq : Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) = (List.range 24).flatMap fun r =>
    [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax), .vop (.vpbroadcastq .l256 .xmm0 .xmm0),
      Impl.Sha3.X86_64.X4.st .rbx (oRc / 32 + r) .xmm0] := rfl

/-- The table of the round constants. -/
theorem rc_ok {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {s₀ : State} (he : VG.Proof.MlKem.X86_64.S4.Env σ s₀) :
    WP isa (.block (Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32))) s₀ (VG.Proof.MlKem.X86_64.S4.RcInv σ s₀ 24) := by
  rw [VG.Proof.MlKem.X86_64.S4.rcTable_eq]
  exact wp_range_flatMap (M := isa) (VG.Proof.MlKem.X86_64.S4.RcInv σ s₀) (fun r s hr h => VG.Proof.MlKem.X86_64.S4.rc_step hp he hr h) 24 (Nat.le_refl _) s₀
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by bdd_omega)⟩


/-! ## The states, byte by byte -/

/-- The offset of byte `q` of state `k`. -/
abbrev off4 (k q : Nat) : Nat := 32 * (q / 8) + 8 * k + q % 8

/-- The bytes of the states after a write at `p + e`. -/
theorem bytes_write {m : Mem} {p : Addr} {F : Nat → Nat → Byte}
    (h : ∀ k < 4, ∀ q < 200, m (ba p k q) = F k q) {w : Nat} (v : BitVec w) {e : Nat} (hw : w < 2 ^ 64)
    (he : e + w / 8 < 2 ^ 62) {k q : Nat} (hk : k < 4) (hq : q < 200) :
    (m.writeW (p + BitVec.ofNat 64 e) v) (ba p k q) =
      if e ≤ VG.Proof.MlKem.X86_64.S4.off4 k q ∧ VG.Proof.MlKem.X86_64.S4.off4 k q < e + w / 8 then v.extractLsb' (8 * (VG.Proof.MlKem.X86_64.S4.off4 k q - e)) 8 else F k q := by
  split
  · rename_i hc
    simp only [VG.Proof.MlKem.X86_64.S4.off4] at hc
    exact VG.Proof.MlKem.X86_64.S4.wb_in m p v hc.1 (by bdd_omega) hw
  · rename_i hc
    simp only [VG.Proof.MlKem.X86_64.S4.off4] at hc
    rw [ba, VG.Proof.MlKem.X86_64.S4.wb_out m p v (by bdd_omega) (by bdd_omega) (by bdd_omega)]
    exact h k hk q hq

/-- The four states hold `F`. -/
def SB (σ : State) (m : Mem) (F : Nat → Nat → Byte) : Prop :=
  ∀ k < 4, ∀ q < 200, m (ba (VG.Proof.MlKem.X86_64.S4.scr σ) k q) = F k q

/-- During the writes to the states, after the round constants (in `m₁`). -/
structure AI (σ : State) (m₁ : Mem) (s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.S4.Env σ s
  r14 : s.gpr .r14 = 1
  frame : Frame [⟨VG.Proof.MlKem.X86_64.S4.scr σ, 800⟩] m₁ s.mem

theorem AI.write {σ : State} {m₁ : Mem} {s s' : State} (h : VG.Proof.MlKem.X86_64.S4.AI σ m₁ s) {e n : Nat} (hn : e + n ≤ 800)
    (hm : ∃ v : BitVec (8 * n), s'.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.S4.at' σ e) v) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ≠ .rax → s'.gpr r = s.gpr r) : VG.Proof.MlKem.X86_64.S4.AI σ m₁ s' := by
  obtain ⟨v, hv⟩ := hm
  have hf : Frame [⟨VG.Proof.MlKem.X86_64.S4.at' σ e, n⟩] s.mem s'.mem := by
    rw [hv]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
      rw [show 8 * n / 8 = n by bdd_omega]; exact Region.contains_self _ _)
  refine ⟨h.env.write (by simp only [oSave]; omega) hf hrd hwr fun r hr => hg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hg _ (by decide), h.r14], h.frame.trans (hf.sub fun r hr => ?_)⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ hn⟩

/-! ### Zeroing -/

/-- After zeroing the first `n` lanes of each state. -/
structure ZInv (σ : State) (m₁ : Mem) (n : Nat) (s : State) : Prop where
  ai : VG.Proof.MlKem.X86_64.S4.AI σ m₁ s
  x0 : ∀ k < 4, q4 s .xmm0 k = 0
  bytes : ∀ k < 4, ∀ q < 200, q / 8 < n → s.mem (ba (VG.Proof.MlKem.X86_64.S4.scr σ) k q) = 0

theorem zero_step {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {m₁ : Mem} {i : Nat} (hi : i < 25) {s : State} (h : VG.Proof.MlKem.X86_64.S4.ZInv σ m₁ i s) :
    WP isa (.block [Impl.Sha3.X86_64.X4.st .rbx i .xmm0]) s (VG.Proof.MlKem.X86_64.S4.ZInv σ m₁ (i + 1)) := by
  refine wp_vst (a := VG.Proof.MlKem.X86_64.S4.at' σ (32 * i)) (by rw [VG.Proof.Sha3.X86_64.ea_at, h.ai.env.rbx])
    (by rw [h.ai.env.wr]; exact VG.Proof.MlKem.X86_64.S4.in_scr hp rfl (by bdd_omega)) fun s' g' q' m' r' w' => VG.Proof.Sha3.X86_64.wp_nil ?_
  refine ⟨h.ai.write (e := 32 * i) (n := 32) (by bdd_omega) ⟨_, m'⟩ r' w' fun r _ => by rw [g'],
    fun k hk => by rw [q', h.x0 k hk], fun k hk q hq hn => ?_⟩
  rw [m']
  have hb := VG.Proof.MlKem.X86_64.S4.bytes_write (m := s.mem) (p := VG.Proof.MlKem.X86_64.S4.scr σ) (F := fun k q => s.mem (ba (VG.Proof.MlKem.X86_64.S4.scr σ) k q))
    (fun _ _ _ _ => rfl) (s.ymm .xmm0) (e := 32 * i) (by decide) (by bdd_omega) hk hq
  rw [hb]
  split
  · rename_i hc
    simp only [VG.Proof.MlKem.X86_64.S4.off4] at hc ⊢
    rw [show 8 * (32 * (q / 8) + 8 * k + q % 8 - 32 * i) = 64 * k + 8 * (q % 8) by bdd_omega, ← extract_extract (s.ymm .xmm0) (64 * k) 64 (8 * (q % 8)) 8 (by bdd_omega),
      q4_ymm _ _ hk, h.x0 k hk]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  · rename_i hc
    simp only [VG.Proof.MlKem.X86_64.S4.off4] at hc
    exact h.bytes k hk q hq (by bdd_omega)

theorem zero4_eq : zero4 = Impl.Sha3.X86_64.X4.vb .vpxor .xmm0 .xmm0 .xmm0 ::
    (List.range 25).flatMap fun i => [Impl.Sha3.X86_64.X4.st .rbx i .xmm0] := rfl

theorem zero_ok {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {m₁ : Mem} {s : State} (h : VG.Proof.MlKem.X86_64.S4.AI σ m₁ s) :
    WP isa (.block zero4) s (fun s' => VG.Proof.MlKem.X86_64.S4.AI σ m₁ s' ∧ VG.Proof.MlKem.X86_64.S4.SB σ s'.mem fun _ _ => 0) := by
  rw [VG.Proof.MlKem.X86_64.S4.zero4_eq]
  refine wp_vxor fun s₁ u₁ => WP.mono (wp_range_flatMap (M := isa) (VG.Proof.MlKem.X86_64.S4.ZInv σ m₁) (fun i s hi h => VG.Proof.MlKem.X86_64.S4.zero_step hp hi h)
    25 (Nat.le_refl _) s₁ ⟨h.write (e := 0) (n := 0) (by bdd_omega) ⟨0, ?_⟩ u₁.rd u₁.wr fun r _ => by rw [u₁.gpr],
      fun k hk => by rw [u₁.val k hk, BitVec.xor_self]; rfl, fun _ _ _ _ h => absurd h (by bdd_omega)⟩)
    fun s' h' => ⟨h'.ai, fun k hk q hq => h'.bytes k hk q hq (by bdd_omega)⟩
  rw [u₁.mem]
  funext x
  simp [Mem.writeW, Mem.write]


/-! ### The seeds -/

/-- Byte `q` of seed `k` (0 past its end). -/
abbrev Bq (σ : State) (k q : Nat) : Byte := (VG.Proof.MlKem.X86_64.S4.B σ k).getD q 0

/-- The states after the first `K` seeds, and the first `i` lanes of seed `K`. -/
def HF (σ : State) (K i : Nat) (k q : Nat) : Byte :=
  if (k < K ∧ q < 34) ∨ (k = K ∧ q < 8 * i) then VG.Proof.MlKem.X86_64.S4.Bq σ k q else 0

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_movzx8 wp_store8 wp_mov32i wp_nil) in
theorem lane_step {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {m₁ : Mem} {K i : Nat} (hK : K < 4) (hi : i < 4) {s : State}
    (h : VG.Proof.MlKem.X86_64.S4.AI σ m₁ s ∧ VG.Proof.MlKem.X86_64.S4.SB σ s.mem (VG.Proof.MlKem.X86_64.S4.HF σ K i)) :
    WP isa (.block [.mov .rax (.mem (at_ .r12 (34 * K + 8 * i))), .store (at_ .rbx (32 * i + 8 * K)) .rax]) s
      (fun s' => VG.Proof.MlKem.X86_64.S4.AI σ m₁ s' ∧ VG.Proof.MlKem.X86_64.S4.SB σ s'.mem (VG.Proof.MlKem.X86_64.S4.HF σ K (i + 1))) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movm (a := VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 (34 * K + 8 * i)) (by rw [ea_at, ha.env.r12])
    (VG.Proof.MlKem.X86_64.S4.in_sd' hp ha.env.rd ha.env.wr (by bdd_omega)) fun s₁ u₁ => wp_store (a := VG.Proof.MlKem.X86_64.S4.at' σ (32 * i + 8 * K))
      (by rw [ea_at, u₁.other _ (by decide), ha.env.rbx]) (by rw [u₁.wr]; exact VG.Proof.MlKem.X86_64.S4.in_scr hp ha.env.wr (by bdd_omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.S4.at' σ (32 * i + 8 * K)) (s.mem.readW (VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 (34 * K + 8 * i)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  refine ⟨ha.write (e := 32 * i + 8 * K) (n := 8) (by bdd_omega) ⟨_, hm⟩ (r₂.trans u₁.rd) (w₂.trans u₁.wr)
    fun r hr => by rw [g₂, u₁.other r hr], fun k hk q hq => ?_⟩
  rw [hm, VG.Proof.MlKem.X86_64.S4.bytes_write hb _ (by decide) (by bdd_omega) hk hq]
  simp only [VG.Proof.MlKem.X86_64.S4.off4]
  by_cases hc : 32 * i + 8 * K ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 32 * i + 8 * K + 64 / 8
  · have hk' : k = K := by bdd_omega
    have hq' : q / 8 = i := by bdd_omega
    subst hk'
    rw [ifp hc, VG.Proof.MlKem.X86_64.S4.HF, ifp (.inr ⟨rfl, by bdd_omega⟩),
      show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * i + 8 * k)) = 8 * (q % 8) by bdd_omega,
      byte_readW _ _ (by bdd_omega), Offset.add_add, show 34 * k + 8 * i + q % 8 = 34 * k + q by bdd_omega,
      VG.Proof.MlKem.X86_64.S4.seed_byte hp ha.env.frame hK (by bdd_omega)]
  · rw [ifn hc, VG.Proof.MlKem.X86_64.S4.HF, VG.Proof.MlKem.X86_64.S4.HF]
    by_cases hc' : (k < K ∧ q < 34) ∨ (k = K ∧ q < 8 * i)
    · rw [ifp hc', ifp (by bdd_omega)]
    · rw [ifn hc', ifn (by bdd_omega)]

theorem byte_setWidth (b : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 b) = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_movzx8 wp_store8 wp_mov32i wp_nil) in
/-- Byte `32 + j` of seed `K`. -/
theorem byte_step {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {m₁ : Mem} {K j : Nat} (hK : K < 4) (hj : j < 2) {s : State}
    (h : VG.Proof.MlKem.X86_64.S4.AI σ m₁ s ∧ VG.Proof.MlKem.X86_64.S4.SB σ s.mem fun k q => if (k < K ∧ q < 34) ∨ (k = K ∧ q < 32 + j) then VG.Proof.MlKem.X86_64.S4.Bq σ k q else 0) :
    WP isa (.block [.movzx8 .rax (at_ .r12 (34 * K + (32 + j))), .store8 (at_ .rbx (128 + 8 * K + j)) .rax]) s
      (fun s' => VG.Proof.MlKem.X86_64.S4.AI σ m₁ s' ∧
        VG.Proof.MlKem.X86_64.S4.SB σ s'.mem fun k q => if (k < K ∧ q < 34) ∨ (k = K ∧ q < 32 + (j + 1)) then VG.Proof.MlKem.X86_64.S4.Bq σ k q else 0) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movzx8 (a := VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 (34 * K + (32 + j))) (by rw [ea_at, ha.env.r12])
    (VG.Proof.MlKem.X86_64.S4.in_sd' hp ha.env.rd ha.env.wr (by bdd_omega)) fun s₁ u₁ => wp_store8 (a := VG.Proof.MlKem.X86_64.S4.at' σ (128 + 8 * K + j))
      (by rw [ea_at, u₁.other _ (by decide), ha.env.rbx]) (by rw [u₁.wr]; exact VG.Proof.MlKem.X86_64.S4.in_scr hp ha.env.wr (by bdd_omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.S4.at' σ (128 + 8 * K + j)) (s.mem (VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 (34 * K + (32 + j)))) := by
    rw [m₂, u₁.mem, u₁.gpr, VG.Proof.MlKem.X86_64.S4.byte_setWidth]
  refine ⟨ha.write (e := 128 + 8 * K + j) (n := 1) (by bdd_omega) ⟨_, hm⟩ (r₂.trans u₁.rd) (w₂.trans u₁.wr)
    fun r hr => by rw [g₂, u₁.other r hr], fun k hk q hq => ?_⟩
  rw [hm, VG.Proof.MlKem.X86_64.S4.bytes_write hb _ (by decide) (by bdd_omega) hk hq]
  simp only [VG.Proof.MlKem.X86_64.S4.off4]
  by_cases hc : 128 + 8 * K + j ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 128 + 8 * K + j + 8 / 8
  · have hk' : k = K := by bdd_omega
    have hq' : q = 32 + j := by bdd_omega
    subst hk' hq'
    rw [ifp hc, ifp (.inr ⟨rfl, by bdd_omega⟩), show 8 * (32 * ((32 + j) / 8) + 8 * k + (32 + j) % 8 -
      (128 + 8 * k + j)) = 0 by bdd_omega, Proof.Sha3.extractLsb'_byte, VG.Proof.MlKem.X86_64.S4.seed_byte hp ha.env.frame hK (by bdd_omega)]
  · rw [ifn hc]
    by_cases hc' : (k < K ∧ q < 34) ∨ (k = K ∧ q < 32 + j)
    · rw [ifp hc', ifp (by bdd_omega)]
    · rw [ifn hc', ifn (by bdd_omega)]

theorem seedLanes_eq (K : Nat) : seedLanes K = (List.range 4).flatMap (fun i =>
    [.mov .rax (.mem (at_ .r12 (34 * K + 8 * i))), .store (at_ .rbx (32 * i + 8 * K)) .rax]) ++
    (([.movzx8 .rax (at_ .r12 (34 * K + (32 + 0))), .store8 (at_ .rbx (128 + 8 * K + 0)) .rax] : List Instr) ++
      ([.movzx8 .rax (at_ .r12 (34 * K + (32 + 1))), .store8 (at_ .rbx (128 + 8 * K + 1)) .rax] : List Instr)) := by
  simp only [seedLanes, Nat.add_zero]; rfl

/-- The states after the first `K` seeds. -/
def GF (σ : State) (K : Nat) (k q : Nat) : Byte := if k < K ∧ q < 34 then VG.Proof.MlKem.X86_64.S4.Bq σ k q else 0

theorem seed_step {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {m₁ : Mem} {K : Nat} (hK : K < 4) {s : State}
    (h : VG.Proof.MlKem.X86_64.S4.AI σ m₁ s ∧ VG.Proof.MlKem.X86_64.S4.SB σ s.mem (VG.Proof.MlKem.X86_64.S4.GF σ K)) :
    WP isa (.block (seedLanes K)) s (fun s' => VG.Proof.MlKem.X86_64.S4.AI σ m₁ s' ∧ VG.Proof.MlKem.X86_64.S4.SB σ s'.mem (VG.Proof.MlKem.X86_64.S4.GF σ (K + 1))) := by
  rw [VG.Proof.MlKem.X86_64.S4.seedLanes_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s => VG.Proof.MlKem.X86_64.S4.AI σ m₁ s ∧ VG.Proof.MlKem.X86_64.S4.SB σ s.mem (VG.Proof.MlKem.X86_64.S4.HF σ K i))
    (fun i s hi h => VG.Proof.MlKem.X86_64.S4.lane_step hp hK hi h) 4 (Nat.le_refl _) s ⟨h.1, fun k hk q hq => ?_⟩) fun s₁ h₁ => ?_
  · rw [h.2 k hk q hq, VG.Proof.MlKem.X86_64.S4.GF, VG.Proof.MlKem.X86_64.S4.HF]
    by_cases hc : k < K ∧ q < 34
    · rw [ifp hc, ifp (.inl hc)]
    · rw [ifn hc, ifn (by bdd_omega)]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.S4.byte_step hp (j := 0) hK (by decide) ⟨h₁.1, fun k hk q hq => ?_⟩) fun s₂ h₂ =>
    WP.mono (VG.Proof.MlKem.X86_64.S4.byte_step hp (j := 1) hK (by decide) h₂) fun s₃ ⟨h₃, b₃⟩ => ⟨h₃, fun k hk q hq => ?_⟩
  · rw [h₁.2 k hk q hq, VG.Proof.MlKem.X86_64.S4.HF]
  · rw [b₃ k hk q hq, VG.Proof.MlKem.X86_64.S4.GF]
    dsimp only
    by_cases hc : (k < K ∧ q < 34) ∨ (k = K ∧ q < 32 + (1 + 1))
    · rw [ifp hc]
      by_cases hc' : k < K + 1 ∧ q < 34
      · rw [ifp hc']
      · rw [ifn hc']; omega
    · rw [ifn hc]
      by_cases hc' : k < K + 1 ∧ q < 34
      · omega
      · rw [ifn hc']


/-! ### The padding -/

open VG.Proof.Sha3.X86_64 (wp_store8 wp_mov32i wp_nil) in
/-- The byte `c` (in `rax`) to byte `q₀` of state `K`. -/
theorem cbyte_step {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {m₁ : Mem} {F : Nat → Nat → Byte} {K q₀ : Nat} (hK : K < 4)
    (hq₀ : q₀ < 200) {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64) (h : VG.Proof.MlKem.X86_64.S4.AI σ m₁ s ∧ VG.Proof.MlKem.X86_64.S4.SB σ s.mem F) :
    WP isa (.block [.store8 (at_ .rbx (32 * (q₀ / 8) + 8 * K + q₀ % 8)) .rax]) s
      (fun s' => VG.Proof.MlKem.X86_64.S4.AI σ m₁ s' ∧ s'.gpr .rax = s.gpr .rax ∧
        VG.Proof.MlKem.X86_64.S4.SB σ s'.mem fun k q => if k = K ∧ q = q₀ then c else F k q) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_store8 (a := VG.Proof.MlKem.X86_64.S4.at' σ (32 * (q₀ / 8) + 8 * K + q₀ % 8)) (by rw [ea_at, ha.env.rbx])
    (by exact VG.Proof.MlKem.X86_64.S4.in_scr hp ha.env.wr (by bdd_omega)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.S4.at' σ (32 * (q₀ / 8) + 8 * K + q₀ % 8)) c := by
    rw [m₂, hax, VG.Proof.MlKem.X86_64.S4.byte_setWidth]
  refine ⟨ha.write (n := 1) (by bdd_omega) ⟨_, hm⟩ r₂ w₂ fun r _ => by rw [g₂], by rw [g₂], fun k hk q hq => ?_⟩
  rw [hm, VG.Proof.MlKem.X86_64.S4.bytes_write hb _ (by decide) (by bdd_omega) hk hq]
  simp only [VG.Proof.MlKem.X86_64.S4.off4]
  by_cases hc : 32 * (q₀ / 8) + 8 * K + q₀ % 8 ≤ 32 * (q / 8) + 8 * k + q % 8 ∧
      32 * (q / 8) + 8 * k + q % 8 < 32 * (q₀ / 8) + 8 * K + q₀ % 8 + 8 / 8
  · have e : k = K ∧ q = q₀ := by bdd_omega
    rw [ifp hc, ifp e, show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * (q₀ / 8) + 8 * K + q₀ % 8)) = 0 by bdd_omega,
      Proof.Sha3.extractLsb'_byte]
  · rw [ifn hc, ifn (by bdd_omega)]

/-- The four states hold their padded seeds. -/
def PF (σ : State) (k q : Nat) : Byte :=
  if q < 34 then VG.Proof.MlKem.X86_64.S4.Bq σ k q else if q = 34 then 0x1f else if q = 167 then 0x80 else 0

theorem sfx_eq : (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (128 + 8 * k + 2)) .rax]) =
    (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (32 * (34 / 8) + 8 * k + 34 % 8)) .rax]) := rfl

theorem last_eq : (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (640 + 8 * k + 7)) .rax]) =
    (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (32 * (167 / 8) + 8 * k + 167 % 8)) .rax]) := rfl

/-- The byte `c` to byte `q₀` of each state. -/
theorem cbytes_ok {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {m₁ : Mem} {F : Nat → Nat → Byte} {q₀ : Nat} (hq₀ : q₀ < 200)
    {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64) (h : VG.Proof.MlKem.X86_64.S4.AI σ m₁ s ∧ VG.Proof.MlKem.X86_64.S4.SB σ s.mem F) :
    WP isa (.block ((List.range 4).flatMap fun k => [.store8 (at_ .rbx (32 * (q₀ / 8) + 8 * k + q₀ % 8)) .rax])) s
      (fun s' => VG.Proof.MlKem.X86_64.S4.AI σ m₁ s' ∧ VG.Proof.MlKem.X86_64.S4.SB σ s'.mem fun k q => if q = q₀ then c else F k q) := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s' => VG.Proof.MlKem.X86_64.S4.AI σ m₁ s' ∧ s'.gpr .rax = c.setWidth 64 ∧
      VG.Proof.MlKem.X86_64.S4.SB σ s'.mem fun k q => if k < K ∧ q = q₀ then c else F k q)
    (fun K s' hK ⟨ha, hx, hb⟩ => WP.mono (VG.Proof.MlKem.X86_64.S4.cbyte_step hp hK hq₀ hx ⟨ha, hb⟩) fun s'' ⟨ha', hx', hb'⟩ =>
      ⟨ha', hx'.trans hx, fun k hk q hq => ?_⟩) 4 (Nat.le_refl _) s ⟨h.1, hax, fun k hk q hq => ?_⟩)
    fun s' ⟨ha, _, hb⟩ => ⟨ha, fun k hk q hq => ?_⟩
  · rw [hb' k hk q hq]
    dsimp only
    by_cases e : k = K ∧ q = q₀
    · rw [ifp e, ifp (by bdd_omega)]
    · rw [ifn e]
      by_cases e' : k < K ∧ q = q₀
      · rw [ifp e', ifp (by bdd_omega)]
      · rw [ifn e', ifn (by bdd_omega)]
  · rw [h.2 k hk q hq]; dsimp only; rw [ifn (by bdd_omega)]
  · rw [hb k hk q hq]
    dsimp only
    by_cases e : q = q₀
    · rw [ifp e, ifp ⟨hk, e⟩]
    · rw [ifn e, ifn (by bdd_omega)]

theorem absorb4_eq : absorb4 = zero4 ++ ((List.range 4).flatMap seedLanes ++
    (([.mov32 .rax (.imm 0x1f)] : List Instr) ++ ((List.range 4).flatMap (fun k =>
      [Instr.store8 (at_ .rbx (32 * (34 / 8) + 8 * k + 34 % 8)) .rax]) ++
    (([.mov32 .rax (.imm 0x80)] : List Instr) ++ (List.range 4).flatMap (fun k =>
      [Instr.store8 (at_ .rbx (32 * (167 / 8) + 8 * k + 167 % 8)) .rax]))))) := by
  simp only [absorb4, List.append_assoc, List.cons_append, List.nil_append]

open VG.Proof.Sha3.X86_64 (wp_mov32i) in
/-- The padded seeds in the four states. -/
theorem absorb_ok {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {m₁ : Mem} {s : State} (h : VG.Proof.MlKem.X86_64.S4.AI σ m₁ s) :
    WP isa (.block absorb4) s (fun s' => VG.Proof.MlKem.X86_64.S4.AI σ m₁ s' ∧ VG.Proof.MlKem.X86_64.S4.SB σ s'.mem (VG.Proof.MlKem.X86_64.S4.PF σ)) := by
  rw [VG.Proof.MlKem.X86_64.S4.absorb4_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.S4.zero_ok hp h) fun s₁ ⟨h₁, z₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => VG.Proof.MlKem.X86_64.S4.AI σ m₁ s ∧ VG.Proof.MlKem.X86_64.S4.SB σ s.mem (VG.Proof.MlKem.X86_64.S4.GF σ K))
    (fun K s hK h => VG.Proof.MlKem.X86_64.S4.seed_step hp hK h) 4 (Nat.le_refl _) s₁ ⟨h₁, fun k hk q hq => ?_⟩) fun s₂ h₂ => ?_
  · rw [z₁ k hk q hq, VG.Proof.MlKem.X86_64.S4.GF, ifn (by bdd_omega)]
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₃ u₃ => VG.Proof.Sha3.X86_64.wp_nil
    (Q := fun s₃ => VG.Proof.MlKem.X86_64.S4.AI σ m₁ s₃ ∧ s₃.gpr .rax = (0x1f : Byte).setWidth 64 ∧ VG.Proof.MlKem.X86_64.S4.SB σ s₃.mem (VG.Proof.MlKem.X86_64.S4.GF σ 4))
    ⟨h₂.1.write (e := 0) (n := 0) (by bdd_omega) ⟨0, ?_⟩ u₃.rd u₃.wr fun r hr => u₃.other r hr, by rw [u₃.gpr]; rfl,
      by rw [u₃.mem]; exact h₂.2⟩) fun s₃ ⟨a₃, x₃, b₃⟩ => ?_
  · rw [u₃.mem]; funext x; simp [Mem.writeW, Mem.write]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.S4.cbytes_ok hp (by decide) x₃ ⟨a₃, b₃⟩) fun s₄ ⟨a₄, b₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₅ u₅ => VG.Proof.Sha3.X86_64.wp_nil
    (Q := fun s₅ => VG.Proof.MlKem.X86_64.S4.AI σ m₁ s₅ ∧ s₅.gpr .rax = (0x80 : Byte).setWidth 64 ∧
      VG.Proof.MlKem.X86_64.S4.SB σ s₅.mem fun k q => if q = 34 then 0x1f else VG.Proof.MlKem.X86_64.S4.GF σ 4 k q)
    ⟨a₄.write (e := 0) (n := 0) (by bdd_omega) ⟨0, ?_⟩ u₅.rd u₅.wr fun r hr => u₅.other r hr, by rw [u₅.gpr]; rfl,
      by rw [u₅.mem]; exact b₄⟩) fun s₅ ⟨a₅, x₅, b₅⟩ => ?_
  · rw [u₅.mem]; funext x; simp [Mem.writeW, Mem.write]
  refine WP.mono (VG.Proof.MlKem.X86_64.S4.cbytes_ok hp (by decide) x₅ ⟨a₅, b₅⟩) fun s₆ ⟨a₆, b₆⟩ => ⟨a₆, fun k hk q hq => ?_⟩
  rw [b₆ k hk q hq, VG.Proof.MlKem.X86_64.S4.PF]
  dsimp only
  rw [VG.Proof.MlKem.X86_64.S4.GF]
  by_cases e1 : q < 34
  · rw [ifn (show ¬ q = 167 by bdd_omega), ifn (show ¬ q = 34 by bdd_omega), ifp (show k < 4 ∧ q < 34 from ⟨hk, e1⟩),
      ifp e1]
  · rw [ifn e1, ifn (show ¬ (k < 4 ∧ q < 34) by bdd_omega)]
    by_cases e2 : q = 34
    · rw [ifn (show ¬ q = 167 by bdd_omega), ifp e2, ifp e2]
    · rw [ifn e2, ifn e2]

end VG.Proof.MlKem.X86_64.S4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, squeezing

The padded seeds are the states that `Keccak-f` turns into the absorbed ones
(`padded_A0`), and the four states hold them after `absorb4` (`lanes_A0`).
Each `squeeze4 n` permutes the four states (`permute4_ok`) and copies the
first 168 bytes of each to its output, which then holds the first `168 (n +
1)` bytes of the seed's XOF output (`sq_ok`).
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Spec.Sha3 (keccakF RC)
open VG.Proof.Sha3 (byteOf Rep xorByte byteOf_xorByte byteOf_xorBytes absorb_pad iterF iterF_succ iterF_keccakF)
open VG.Proof.MlKem (padded xofByte)
open VG.Proof.Sha3.X86_64.X4 (la ba Lanes4 lanes4_of_bytes byte_of_lanes4 Pre4 permute4_ok)

/-! ## The padded seeds -/

export VG.Proof.Sha3.Seed34 (A0 padded_A0 byteOf_A0 xofByte_A0)

theorem B_length (σ : State) (k : Nat) : (VG.Proof.MlKem.X86_64.S4.B σ k).length = 34 := VG.Proof.Sha3.bytesAt_length _ _ _

/-! ## `Env` after writes -/

/-- `Env` after writes below the saved registers. -/
theorem Env.low {σ s s' : State} (he : VG.Proof.MlKem.X86_64.S4.Env σ s) {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨VG.Proof.MlKem.X86_64.S4.scr σ, oSave⟩)
    (hf : Frame rs s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], s'.gpr r = s.gpr r) : VG.Proof.MlKem.X86_64.S4.Env σ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hg .rbx (by simp), he.rbx], by rw [hg .r12 (by simp), he.r12],
    by rw [hg .r13 (by simp), he.r13], by rw [hg .rsp (by simp), he.rsp], by rw [hg .r15 (by simp), he.r15],
    fun i hi => ?_, ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (fun r hr => ((Offset.base_disjoint (VG.Proof.MlKem.X86_64.S4.scr σ) (k := oSave)
        (e := oSave + 8 * i) (n := 8) (by omega) (by simp only [oSave]; omega)).symm).sub_right (hrs r hr))
      (by decide)]
    exact he.saved i hi
  · refine he.frame.trans (hf.sub fun r hr => ⟨VG.Proof.MlKem.X86_64.S4.scrR σ, by simp, fun x hx => Offset.sub_base (VG.Proof.MlKem.X86_64.S4.scr σ) (d := 0)
      (n := oSave) (k := 8192) (by simp only [oSave]; omega) x (by rw [BitVec.add_zero]; exact hrs r hr x hx)⟩)

/-- `Env` after code that writes no memory and keeps its registers. -/
theorem Env.keep {σ s s' : State} (he : VG.Proof.MlKem.X86_64.S4.Env σ s) (hm : s'.mem = s.mem) {rs : List Reg} (hk : Keep rs s s')
    (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15], r ∉ rs) : VG.Proof.MlKem.X86_64.S4.Env σ s' :=
  Env.low he (rs := []) (by simp) (by rw [hm]; exact Frame.refl _ _) hk.2.1 hk.2.2 fun r hr => hk.gpr (hrs r hr)

/-! ## The squeezes -/

/-- After `n` squeezes. -/
structure SqInv (σ : State) (n : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.S4.Env σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (VG.Proof.MlKem.X86_64.S4.scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (VG.Proof.MlKem.X86_64.S4.scr σ) fun k => iterF n (VG.Proof.Sha3.Seed34.A0 (VG.Proof.MlKem.X86_64.S4.B σ k))
  buf : ∀ k < 4, ∀ p < 168 * n, s.mem (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * k + p)) = xofByte (VG.Proof.MlKem.X86_64.S4.B σ k) p

theorem lanes_A0 {σ : State} {m : Mem} (h : VG.Proof.MlKem.X86_64.S4.SB σ m (VG.Proof.MlKem.X86_64.S4.PF σ)) : Lanes4 m (VG.Proof.MlKem.X86_64.S4.scr σ) fun k => iterF 0 (VG.Proof.Sha3.Seed34.A0 (VG.Proof.MlKem.X86_64.S4.B σ k)) :=
  lanes4_of_bytes fun k hk q hq => by
    rw [h k hk q hq, show iterF 0 (VG.Proof.Sha3.Seed34.A0 (VG.Proof.MlKem.X86_64.S4.B σ k)) = VG.Proof.Sha3.Seed34.A0 (VG.Proof.MlKem.X86_64.S4.B σ k) from rfl, VG.Proof.Sha3.Seed34.byteOf_A0 (VG.Proof.MlKem.X86_64.S4.B_length σ k) hq, VG.Proof.MlKem.X86_64.S4.PF]



theorem la_tbl (σ : State) (r k : Nat) : la (VG.Proof.MlKem.X86_64.S4.at' σ 1600) r k = la (VG.Proof.MlKem.X86_64.S4.scr σ) (50 + r) k := by
  rw [la, la, VG.Proof.MlKem.X86_64.S4.at', Offset.add_add, show 1600 + (32 * r + 8 * k) = 32 * (50 + r) + 8 * k by omega]

theorem sx800 : BitVec.signExtend 64 (BitVec.ofNat 32 oTmp) = BitVec.ofNat 64 800 := by decide
theorem sx1600 : BitVec.signExtend 64 (BitVec.ofNat 32 oRc) = BitVec.ofNat 64 1600 := by decide
theorem sx2368 : BitVec.signExtend 64 (BitVec.ofNat 32 oBuf) = BitVec.ofNat 64 2368 := by decide

theorem args_ok {σ s : State} (he : VG.Proof.MlKem.X86_64.S4.Env σ s) :
    WP isa (.block permArgs) s fun s' => (s'.mem = s.mem ∧ s'.gpr .rdi = VG.Proof.MlKem.X86_64.S4.scr σ ∧ s'.gpr .rsi = VG.Proof.MlKem.X86_64.S4.at' σ 800 ∧
      s'.gpr .rdx = VG.Proof.MlKem.X86_64.S4.at' σ 1600 ∧ s'.gpr .rcx = VG.Proof.MlKem.X86_64.S4.at' σ 2368) ∧ Keep [.rdi, .rsi, .rdx, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold permArgs
  xrun [he.rbx, VG.Proof.MlKem.X86_64.S4.sx800, VG.Proof.MlKem.X86_64.S4.sx1600, VG.Proof.MlKem.X86_64.S4.sx2368]

/-- The permutation's precondition, in the scratch space. -/
theorem pre4 {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {s : State} (hrd : s.rd = σ.rd) (hwr : s.wr = σ.wr)
    (hrc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (VG.Proof.MlKem.X86_64.S4.scr σ) (50 + r) k) 64 = RC r) :
    Pre4 s (VG.Proof.MlKem.X86_64.S4.scr σ) (VG.Proof.MlKem.X86_64.S4.at' σ 800) (VG.Proof.MlKem.X86_64.S4.at' σ 1600) :=
  ⟨fun i _ => VG.Proof.MlKem.X86_64.S4.in_scr hp hwr (a := 32 * i) (by omega),
    fun i _ => by rw [VG.Proof.MlKem.X86_64.S4.at', Offset.add_add]; exact VG.Proof.MlKem.X86_64.S4.in_scr hp hwr (by omega),
    fun r _ => by rw [VG.Proof.MlKem.X86_64.S4.at', Offset.add_add]; exact VG.Proof.MlKem.X86_64.S4.in_scr' hp hrd hwr (by omega),
    Offset.base_disjoint _ (by omega) (by omega),
    Offset.base_disjoint _ (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    fun r hr k hk => by rw [VG.Proof.MlKem.X86_64.S4.la_tbl]; exact hrc r hr k hk⟩

/-- A buffer byte, read through a frame of the states. -/
theorem buf_frame {σ : State} {m m' : Mem} {rs : List Region}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨VG.Proof.MlKem.X86_64.S4.at' σ oBuf, 2016⟩ r) (hf : Frame rs m m') {k p : Nat} (hk : k < 4)
    (hp' : p < 504) : m' (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * k + p)) = m (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * k + p)) := by
  have := hf.bytes (R := ⟨VG.Proof.MlKem.X86_64.S4.at' σ oBuf, 2016⟩) hd (by simp only; omega) (i := 504 * k + p) (by simp only; omega)
  simpa only [VG.Proof.MlKem.X86_64.S4.at', Offset.add_add, Nat.add_assoc] using this

/-- The permutation, after `n` squeezes. -/
theorem perm_ok {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {n : Nat} (hn : n < 3) {s : State} (h : VG.Proof.MlKem.X86_64.S4.SqInv σ n s)
    {rest : Prog isa} {Q : State → Prop} (kont : ∀ s', VG.Proof.MlKem.X86_64.S4.Env σ s' ∧ s'.gpr .r14 = 1 ∧
      (∀ r < 24, ∀ k < 4, s'.mem.readW (la (VG.Proof.MlKem.X86_64.S4.scr σ) (50 + r) k) 64 = RC r) ∧
      Lanes4 s'.mem (VG.Proof.MlKem.X86_64.S4.scr σ) (fun k => iterF (n + 1) (VG.Proof.Sha3.Seed34.A0 (VG.Proof.MlKem.X86_64.S4.B σ k))) ∧
      (∀ k < 4, ∀ p < 168 * n, s'.mem (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * k + p)) = xofByte (VG.Proof.MlKem.X86_64.S4.B σ k) p) → WP isa rest s' Q) :
    WP isa (.seq (.block permArgs) (.seq Impl.Sha3.X86_64.X4.permute4 rest)) s Q := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.args_ok h.env) fun s₁ ⟨⟨hm, hdi, hsi, hdx, hcx⟩, k₁⟩ => ?_)
  have hrd : s₁.rd = σ.rd := k₁.2.1.trans h.env.rd
  have hwr : s₁.wr = σ.wr := k₁.2.2.trans h.env.wr
  refine WP.seq (WP.mono (permute4_ok (A := fun k => iterF n (VG.Proof.Sha3.Seed34.A0 (VG.Proof.MlKem.X86_64.S4.B σ k))) (VG.Proof.MlKem.X86_64.S4.pre4 hp hrd hwr (by rw [hm]; exact h.rc))
    hdi hsi hdx (by rw [hcx, VG.Proof.MlKem.X86_64.S4.at', VG.Proof.MlKem.X86_64.S4.at', Offset.add_add]) (by rw [hm]; exact h.lanes))
    fun s₂ ⟨hl, hf, hrd₂, hwr₂, _, hg⟩ => kont s₂ ?_)
  have hsub : ∀ r ∈ [(⟨VG.Proof.MlKem.X86_64.S4.scr σ, 800⟩ : Region), ⟨VG.Proof.MlKem.X86_64.S4.at' σ 800, 800⟩], Region.Sub r ⟨VG.Proof.MlKem.X86_64.S4.scr σ, oSave⟩ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by simp only [oSave]; omega)
    · exact Offset.sub_base _ (by simp only [oSave]; omega)
  refine ⟨Env.low (h.env.keep hm k₁ (by decide)) hsub hf hrd₂ hwr₂ fun r hr => hg r
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hg _ (by decide) (by decide), k₁.gpr (by decide), h.r14], fun r hr k hk => ?_, ?_, fun k hk p hp' => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using ⟨Offset.disjoint_base (VG.Proof.MlKem.X86_64.S4.scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega) (by omega),
          Offset.disjoint (VG.Proof.MlKem.X86_64.S4.scr σ) (d := 32 * (50 + r) + 8 * k) (n := 8) (e := 800) (k := 800) (by omega) (by omega)
            (by omega)⟩) (by decide), hm]
    exact h.rc r hr k hk
  · intro i hi k hk
    rw [hl i hi k hk]
    rfl
  · rw [VG.Proof.MlKem.X86_64.S4.buf_frame (by simpa using ⟨Offset.disjoint_base (VG.Proof.MlKem.X86_64.S4.scr σ) (k := 800) (d := oBuf) (n := 2016) (by simp only [oBuf]; omega)
                                 (by simp only [oBuf]; omega), Offset.disjoint (VG.Proof.MlKem.X86_64.S4.scr σ) (d := oBuf) (n := 2016) (e := 800) (k := 800)
                                   (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by omega)⟩) hf hk (by omega), hm]
    exact h.buf k hk p hp'


/-! ## Copying the output -/

/-- During the copy of block `n`: the first `I` lanes of state `K` copied,
and all of the states before it. -/
structure EXI (σ : State) (n K I : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.S4.Env σ s
  r14 : s.gpr .r14 = 1
  rc : ∀ r < 24, ∀ k < 4, s.mem.readW (la (VG.Proof.MlKem.X86_64.S4.scr σ) (50 + r) k) 64 = RC r
  lanes : Lanes4 s.mem (VG.Proof.MlKem.X86_64.S4.scr σ) (fun k => iterF (n + 1) (VG.Proof.Sha3.Seed34.A0 (VG.Proof.MlKem.X86_64.S4.B σ k)))
  buf : ∀ k < 4, ∀ p < 504, (p < 168 * n ∨ (168 * n ≤ p ∧ p < 168 * n + 168 ∧ (k < K ∨ (k = K ∧ p < 168 * n + 8 * I)))) →
    s.mem (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * k + p)) = xofByte (VG.Proof.MlKem.X86_64.S4.B σ k) p

open VG.Proof.Sha3.X86_64 (wp_movm wp_store wp_nil) in
theorem ext_step {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {n K I : Nat} (hn : n < 3) (hK : K < 4) (hI : I < 21) {s : State}
    (h : VG.Proof.MlKem.X86_64.S4.EXI σ n K I s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))),
      .store (at_ .rbx (oBuf + 504 * K + 168 * n + 8 * I)) .rax]) s (VG.Proof.MlKem.X86_64.S4.EXI σ n K (I + 1)) := by
  refine wp_movm (a := VG.Proof.MlKem.X86_64.S4.at' σ (32 * I + 8 * K)) (by rw [ea_at, h.env.rbx])
    (VG.Proof.MlKem.X86_64.S4.in_scr' hp h.env.rd h.env.wr (by omega)) fun s₁ u₁ => wp_store (a := VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K + 168 * n + 8 * I))
      (by rw [ea_at, u₁.other _ (by decide), h.env.rbx]) (by rw [u₁.wr]; exact VG.Proof.MlKem.X86_64.S4.in_scr hp h.env.wr (by simp only [oBuf]; omega))
      fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K + 168 * n + 8 * I)) (s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (32 * I + 8 * K)) 64) := by
    rw [m₂, u₁.mem, u₁.gpr]
  have hf : Frame [⟨VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K + 168 * n + 8 * I), 8⟩] s.mem s₂.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨Env.low h.env (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.sub_base _ (by simp only [oBuf, oSave]; omega)) hf (r₂.trans u₁.rd) (w₂.trans u₁.wr)
      fun r hr => by
        rw [g₂, u₁.other r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)],
    by rw [g₂, u₁.other _ (by decide), h.r14], fun r hr k hk => ?_, fun i hi k hk => ?_, fun k hk p hp' hc => ?_⟩
  · have e := readW_writeW_off s.mem (VG.Proof.MlKem.X86_64.S4.scr σ) (s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (32 * I + 8 * K)) 64) (d := 32 * (50 + r) + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.rc r hr k hk)
  · have e := readW_writeW_off s.mem (VG.Proof.MlKem.X86_64.S4.scr σ) (s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (32 * I + 8 * K)) 64) (d := 32 * i + 8 * k)
      (e := oBuf + 504 * K + 168 * n + 8 * I) (n := 8) (by omega) (by simp only [oBuf]; omega)
      (by simp only [oBuf]; omega)
    rw [hm]; exact e.trans (h.lanes i hi k hk)
  · rw [hm]
    by_cases hw : k = K ∧ 168 * n + 8 * I ≤ p ∧ p < 168 * n + 8 * I + 8
    · obtain ⟨rfl, h₁, h₂⟩ := hw
      rw [VG.Proof.MlKem.X86_64.S4.wb_in _ _ _ (by omega) (by simp only [oBuf]; omega) (by decide),
        show 8 * (oBuf + 504 * k + p - (oBuf + 504 * k + 168 * n + 8 * I)) = 8 * (p - 168 * n - 8 * I) by omega,
        byte_readW _ _ (by omega), VG.Proof.MlKem.X86_64.S4.at', Offset.add_add,
        show 32 * I + 8 * k + (p - 168 * n - 8 * I) = 32 * ((8 * I + (p - 168 * n - 8 * I)) / 8) + 8 * k +
          (8 * I + (p - 168 * n - 8 * I)) % 8 by omega,
        byte_of_lanes4 h.lanes hk (by omega), ← VG.Proof.Sha3.Seed34.xofByte_A0 (VG.Proof.MlKem.X86_64.S4.B_length σ k) (by omega),
        show 168 * n + (8 * I + (p - 168 * n - 8 * I)) = p by omega]
    · rw [VG.Proof.MlKem.X86_64.S4.wb_out _ _ _ (by simp only [oBuf]; omega) (by simp only [oBuf]; omega) (by simp only [oBuf]; omega)]
      exact h.buf k hk p hp' (by omega)

theorem extract_eq (n : Nat) : VG.Impl.MlKem.X86_64.Sample4.extract n = (List.range 4).flatMap fun K => (List.range 21).flatMap fun I =>
    [.mov .rax (.mem (at_ .rbx (32 * I + 8 * K))), .store (at_ .rbx (oBuf + 504 * K + 168 * n + 8 * I)) .rax] := rfl

/-- Block `n` of each state's output. -/
theorem extract_ok {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {n : Nat} (hn : n < 3) {s : State} (h : VG.Proof.MlKem.X86_64.S4.EXI σ n 0 0 s) :
    WP isa (.block (VG.Impl.MlKem.X86_64.Sample4.extract n)) s (VG.Proof.MlKem.X86_64.S4.SqInv σ (n + 1)) := by
  rw [VG.Proof.MlKem.X86_64.S4.extract_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => VG.Proof.MlKem.X86_64.S4.EXI σ n K 0 s) (fun K s hK h => ?_) 4 (Nat.le_refl _) s h)
    fun s' h' => ⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' => h'.buf k hk p (by omega) (by omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun I s => VG.Proof.MlKem.X86_64.S4.EXI σ n K I s) (fun I s hI h => VG.Proof.MlKem.X86_64.S4.ext_step hp hn hK hI h)
    21 (Nat.le_refl _) s h) fun s' h' => ⟨h'.env, h'.r14, h'.rc, h'.lanes, fun k hk p hp' hc => h'.buf k hk p hp' (by omega)⟩

/-- `squeeze4 n`: after `n + 1` squeezes. -/
theorem sq_ok {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {n : Nat} (hn : n < 3) {s : State} (h : VG.Proof.MlKem.X86_64.S4.SqInv σ n s) :
    WP isa (squeeze4 n) s (VG.Proof.MlKem.X86_64.S4.SqInv σ (n + 1)) := by
  unfold squeeze4
  exact VG.Proof.MlKem.X86_64.S4.perm_ok hp hn h fun s' ⟨he, h14, hrc, hl, hb⟩ =>
    VG.Proof.MlKem.X86_64.S4.extract_ok hp hn ⟨he, h14, hrc, hl, fun k hk p _ hc => hb k hk p (by omega)⟩

end VG.Proof.MlKem.X86_64.S4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.S4Parse`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, sampling

What holds before and during `parse k` (`PInv`, `LAt`), an iteration of
`vg_mlkem_sample_ntt`'s loop on the XOF output of seed `k` (`lat_step`, as
`SampleNtt.lean`'s), and, if the iterations sample fewer than 256
coefficients, the call of `vg_mlkem_sample_ntt` on the seed (`fallback_ok`).
Either way, polynomial `k` is then the seed's `SampleNTT`, if it succeeds, and
`r14` records whether the first `k + 1` do. The loop of `parse k` is in
`S4Loop.lean`.
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Proof.MlKem (xofByte sampleAfter)
open VG.Spec.Sha3 (bytesAt)

/-- Whether the first `K` seeds sample their polynomials. -/
def okN (σ : State) (K : Nat) : Nat :=
  if (List.range K).all fun k => (sampleNTT minIterations (VG.Proof.MlKem.X86_64.S4.B σ k)).isSome then 1 else 0

/-- The output of the squeezes: the first 504 bytes of each seed's XOF output. -/
abbrev BufOK (σ : State) (m : Mem) : Prop :=
  ∀ k < 4, ∀ p < 504, m (VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * k + p)) = xofByte (VG.Proof.MlKem.X86_64.S4.B σ k) p

/-- The table of the sampling and the constants of the vector code, from
byte 0 of `scratch`. -/
def TabOK (σ : State) (m : Mem) : Prop := ∀ i < 280, m.readW (VG.Proof.MlKem.X86_64.S4.at' σ (8 * i)) 64 = tabQ i

/-- The output of the squeezes, and the table. -/
abbrev BufT (σ : State) (m : Mem) : Prop := VG.Proof.MlKem.X86_64.S4.BufOK σ m ∧ VG.Proof.MlKem.X86_64.S4.TabOK σ m

/-- The table is kept by writes elsewhere. -/
theorem tab_frame {σ : State} {m m' : Mem} {rs : List Region} (hd : ∀ r ∈ rs, Region.Disjoint ⟨VG.Proof.MlKem.X86_64.S4.at' σ 0, 2240⟩ r)
    (hf : Frame rs m m') (h : VG.Proof.MlKem.X86_64.S4.TabOK σ m) : VG.Proof.MlKem.X86_64.S4.TabOK σ m' := fun i hi => by
  rw [← h i hi]
  exact hf.readW (Offset.contains _ (by omega) (by omega) (by omega)) hd (by decide)

/-- Before the `K`-th polynomial, with `X` of the memory. -/
structure PC (X : Mem → Prop) (σ : State) (K : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.S4.Env σ s
  buf : X s.mem
  r14 : s.gpr .r14 = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.S4.okN σ K)
  polys : ∀ k < K, ∀ f, sampleNTT minIterations (VG.Proof.MlKem.X86_64.S4.B σ k) = some f → PolyIs s.mem (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) k) f

/-- Before `parse K`. -/
abbrev PInv (σ : State) (K : Nat) (s : State) : Prop := VG.Proof.MlKem.X86_64.S4.PC (VG.Proof.MlKem.X86_64.S4.BufT σ) σ K s

/-- The coefficients of seed `K` after `t` iterations. -/
abbrev Lt (σ : State) (K t : Nat) : List Zq := sampleAfter [] (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) t

/-- At the start of iteration `t` of `parse K`. -/
structure LAt (σ : State) (K t : Nat) (s : State) : Prop where
  pinv : VG.Proof.MlKem.X86_64.S4.PInv σ K s
  rsi : s.gpr .rsi = VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K) + BitVec.ofNat 64 (3 * t)
  rdi : s.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length
  rbp : s.gpr .rbp = poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K
  stored : Stored s.mem (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K) (VG.Proof.MlKem.X86_64.S4.Lt σ K t)

section
variable {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ)
include hp

omit hp in
theorem sub_poly {K : Nat} (hK : K < 4) : Region.Sub (pR (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K)) (VG.Proof.MlKem.X86_64.S4.aR σ) := Offset.sub_base _ (by omega)

/-- Writes to polynomial `K` keep `PInv` but for polynomial `K`, and the registers. -/
theorem PInv.poly {K : Nat} (hK : K < 4) {s s' : State} (h : VG.Proof.MlKem.X86_64.S4.PInv σ K s)
    (hf : Frame [pR (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K)] s.mem s'.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r, r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14] → s'.gpr r = s.gpr r) : VG.Proof.MlKem.X86_64.S4.PInv σ K s' := by
  have hsub := VG.Proof.MlKem.X86_64.S4.sub_poly (σ := σ) hK
  refine ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, by rw [hg .rbx (by simp), h.env.rbx],
      by rw [hg .r12 (by simp), h.env.r12], by rw [hg .r13 (by simp), h.env.r13], by rw [hg .rsp (by simp), h.env.rsp],
      by rw [hg .r15 (by simp), h.env.r15], fun i hi => ?_, h.env.frame.trans (hf.sub fun r hr => ?_)⟩,
    ⟨fun k hk p hp' => ?_, VG.Proof.MlKem.X86_64.S4.tab_frame (by
      simpa using (hp.a_scr.symm.sub_left (VG.Proof.MlKem.X86_64.S4.sub_scr (a := 0) (n := 2240) (by omega))).sub_right hsub) hf h.buf.2⟩,
    by rw [hg .r14 (by simp), h.r14], fun k hk f e => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (by
        simpa using (hp.a_scr.symm.sub_left (VG.Proof.MlKem.X86_64.S4.sub_scr (by simp only [oSave]; omega))).sub_right hsub) (by decide)]
    exact h.env.saved i hi
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.MlKem.X86_64.S4.aR σ, by simp, hsub⟩
  · rw [VG.Proof.MlKem.X86_64.S4.buf_frame (by simpa using (hp.a_scr.symm.sub_left (VG.Proof.MlKem.X86_64.S4.sub_scr (by simp only [oBuf]; omega))).sub_right hsub)
      hf hk hp']
    exact h.buf.1 k hk p hp'
  · have hd := Offset.disjoint (VG.Proof.MlKem.X86_64.S4.aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega) (by omega)
      (by omega)
    exact polyIs_frame hf (by simpa [poly4] using hd) (h.polys k hk f e)

omit hp in
theorem out_byte {K t : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K t s) {j : Nat} (hj : 3 * t + j < 504) :
    s.mem (s.gpr .rsi + BitVec.ofNat 64 j) = xofByte (VG.Proof.MlKem.X86_64.S4.B σ K) (3 * t + j) := by
  have e := h.pinv.buf.1 K hK (3 * t + j) hj
  rw [VG.Proof.MlKem.X86_64.S4.at'] at e
  rw [h.rsi, VG.Proof.MlKem.X86_64.S4.at', Offset.add_add, Offset.add_add]
  exact e

theorem lat_regions {K t : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K t s) {j : Nat} (hj : 3 * t + j < 504) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 j) 1 := by
  rw [h.rsi, VG.Proof.MlKem.X86_64.S4.at', Offset.add_add, Offset.add_add]
  exact VG.Proof.MlKem.X86_64.S4.in_scr' hp h.pinv.env.rd h.pinv.env.wr (by simp only [oBuf]; omega)

/-- An iteration. -/
theorem lat_step {K t : Nat} (hK : K < 4) (ht : t < 168) {s : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K t s) :
    WP isa snBody s fun s' => VG.Proof.MlKem.X86_64.S4.LAt σ K (t + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hL : (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ t
  have hw : WrA s.wr (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K) := fun j hj => by
    rw [h.pinv.env.wr, hp.wr]
    refine ⟨VG.Proof.MlKem.X86_64.S4.aR σ, by simp, ?_⟩
    rw [coeffAddr, poly4, Offset.add_add]
    exact Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (snBody_ok s (aP := poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K) h.rbp h.rdi hL hw h.stored
    (by simpa using VG.Proof.MlKem.X86_64.S4.lat_regions hp hK h (j := 0) (by omega)) (VG.Proof.MlKem.X86_64.S4.lat_regions hp hK h (by omega))
    (VG.Proof.MlKem.X86_64.S4.lat_regions hp hK h (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have e0 := VG.Proof.MlKem.X86_64.S4.out_byte hK h (j := 0) (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  rw [e0, VG.Proof.MlKem.X86_64.S4.out_byte hK h (j := 1) (by omega), VG.Proof.MlKem.X86_64.S4.out_byte hK h (j := 2) (by omega), ← sampleAfter_succ] at hdi hst
  refine ⟨⟨h.pinv.poly hp hK hf hk.2.1 hk.2.2 fun r hr => hk.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    by rw [hsi, h.rsi, show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, Offset.add_add, Nat.mul_succ], hdi,
    by rw [hk.gpr (by decide), h.rbp], hst⟩, hcx, hz⟩

omit hp in
/-- `PC` after code that writes no memory and keeps its registers. -/
theorem PC.keep {X : Mem → Prop} {K : Nat} {s s' : State} (h : VG.Proof.MlKem.X86_64.S4.PC X σ K s) (hm : s'.mem = s.mem) {rs : List Reg}
    (hk : Keep rs s s') (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], r ∉ rs) : VG.Proof.MlKem.X86_64.S4.PC X σ K s' :=
  ⟨h.env.keep hm hk fun r hr => hrs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;> simp [h]),
    by rw [hm]; exact h.buf, by rw [hk.gpr (hrs .r14 (by simp)), h.r14],
    by rw [hm]; exact h.polys⟩

/-! ## The fallback -/

omit hp in
theorem okN_succ (K : Nat) : BitVec.setWidth 64 ((BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.S4.okN σ K)).setWidth 32 &&&
    (if (sampleNTT minIterations (VG.Proof.MlKem.X86_64.S4.B σ K)).isSome then 1 else 0)) = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.S4.okN σ (K + 1)) := by
  simp only [VG.Proof.MlKem.X86_64.S4.okN, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  cases (List.range K).all fun k => (sampleNTT minIterations (VG.Proof.MlKem.X86_64.S4.B σ k)).isSome <;>
    cases (sampleNTT minIterations (VG.Proof.MlKem.X86_64.S4.B σ K)).isSome <;> rfl

/-- The seed at `seeds + 34 K`. -/
theorem seed_bytes {K : Nat} (hK : K < 4) {m : Mem} (hf : Frame [VG.Proof.MlKem.X86_64.S4.aR σ, VG.Proof.MlKem.X86_64.S4.scrR σ, VG.Proof.MlKem.X86_64.S4.stkR σ] σ.mem m) :
    bytesAt m (VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 (34 * K)) 34 = VG.Proof.MlKem.X86_64.S4.B σ K := by
  rw [bytesAt_frame hf (by simpa using ⟨hp.sd_a.sub_left (Offset.sub_base _ (by omega)),
    hp.sd_scr.sub_left (Offset.sub_base _ (by omega)), (hp.stk_sd.sub_right (Offset.sub_base _ (by omega))).symm⟩)
    (by decide)]
  rfl

theorem scr6144_lt : (VG.Proof.MlKem.X86_64.S4.at' σ oScalar).toNat + 2048 ≤ 2 ^ 64 := by
  have := hp.scr_lt
  rw [VG.Proof.MlKem.X86_64.S4.at', Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show oScalar < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (by simp only [oScalar]; omega)]
  simp only [oScalar]; omega

/-- The regions of `vg_mlkem_sample_ntt`'s call for seed `K`. -/
abbrev cRd (σ : State) (K : Nat) : List Region := [⟨VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 (34 * K), 34⟩]
abbrev cWr (σ : State) (K : Nat) : List Region := [pR (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K), ⟨VG.Proof.MlKem.X86_64.S4.at' σ oScalar, 2048⟩]

omit hp in
theorem c_sub {K : Nat} (hK : K < 4) : ∀ r ∈ VG.Proof.MlKem.X86_64.S4.cWr σ K ++ [VG.Proof.MlKem.X86_64.S4.stkR σ],
    (∃ R ∈ [VG.Proof.MlKem.X86_64.S4.aR σ, VG.Proof.MlKem.X86_64.S4.scrR σ, VG.Proof.MlKem.X86_64.S4.stkR σ], Region.Sub r R) := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact ⟨VG.Proof.MlKem.X86_64.S4.aR σ, by simp, VG.Proof.MlKem.X86_64.S4.sub_poly hK⟩
  · exact ⟨VG.Proof.MlKem.X86_64.S4.scrR σ, by simp, VG.Proof.MlKem.X86_64.S4.sub_scr (by simp only [oScalar]; omega)⟩
  · exact ⟨VG.Proof.MlKem.X86_64.S4.stkR σ, by simp, fun _ h => h⟩

/-- A region the call writes is apart from `⟨at' σ a, n⟩` in the scratch space below 6144. -/
theorem c_disj {K : Nat} (hK : K < 4) {a n : Nat} (h : a + n ≤ oScalar) :
    ∀ r ∈ VG.Proof.MlKem.X86_64.S4.cWr σ K ++ [VG.Proof.MlKem.X86_64.S4.stkR σ], Region.Disjoint ⟨VG.Proof.MlKem.X86_64.S4.at' σ a, n⟩ r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl) | rfl
  · exact (hp.a_scr.symm.sub_left (VG.Proof.MlKem.X86_64.S4.sub_scr (by simp only [oScalar] at h; omega))).sub_right (VG.Proof.MlKem.X86_64.S4.sub_poly hK)
  · exact Offset.disjoint _ (.inl h) (by simp only [oScalar] at h; omega) (by simp only [oScalar]; omega)
  · exact (hp.stk_scr.sub_right (VG.Proof.MlKem.X86_64.S4.sub_scr (by simp only [oScalar] at h; omega))).symm

/-- `PC` after the call. -/
theorem PC.call {X : Mem → Prop} {K : Nat} (hK : K < 4) {s s' : State} (h : VG.Proof.MlKem.X86_64.S4.PC X σ K s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], s'.gpr r = s.gpr r)
    (hf : Frame (VG.Proof.MlKem.X86_64.S4.cWr σ K ++ [VG.Proof.MlKem.X86_64.S4.stkR σ]) s.mem s'.mem)
    (hX : ∀ m m', Frame (VG.Proof.MlKem.X86_64.S4.cWr σ K ++ [VG.Proof.MlKem.X86_64.S4.stkR σ]) m m' → X m → X m') : VG.Proof.MlKem.X86_64.S4.PC X σ K s' := by
  refine ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, by rw [hg .rbx (by simp), h.env.rbx],
      by rw [hg .r12 (by simp), h.env.r12], by rw [hg .r13 (by simp), h.env.r13], by rw [hg .rsp (by simp), h.env.rsp],
      by rw [hg .r15 (by simp), h.env.r15], fun i hi => ?_, h.env.frame.trans (hf.sub (VG.Proof.MlKem.X86_64.S4.c_sub (σ := σ) hK))⟩,
    ?_, by rw [hg .r14 (by simp), h.r14], fun k hk f e => ?_⟩
  · rw [hf.readW (Region.contains_self _ _) (VG.Proof.MlKem.X86_64.S4.c_disj hp hK (by simp only [oSave, oScalar]; omega)) (by decide)]
    exact h.env.saved i hi
  · exact hX _ _ hf h.buf
  · refine polyIs_frame hf (fun r hr => ?_) (h.polys k hk f e)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · have hd := Offset.disjoint (VG.Proof.MlKem.X86_64.S4.aP σ) (d := 1024 * k) (n := 1024) (e := 1024 * K) (k := 1024) (by omega) (by omega)
        (by omega)
      simpa [poly4] using hd
    · exact (hp.a_scr.sub_left (VG.Proof.MlKem.X86_64.S4.sub_poly (by omega))).sub_right (VG.Proof.MlKem.X86_64.S4.sub_scr (by simp only [oScalar]; omega))
    · exact (hp.stk_a.sub_right (VG.Proof.MlKem.X86_64.S4.sub_poly (by omega))).symm

theorem bufOK_call {K : Nat} (hK : K < 4) : ∀ m m', Frame (VG.Proof.MlKem.X86_64.S4.cWr σ K ++ [VG.Proof.MlKem.X86_64.S4.stkR σ]) m m' → VG.Proof.MlKem.X86_64.S4.BufT σ m → VG.Proof.MlKem.X86_64.S4.BufT σ m' :=
  fun _ _ hf h => ⟨fun k hk p hp' => by
    rw [VG.Proof.MlKem.X86_64.S4.buf_frame (VG.Proof.MlKem.X86_64.S4.c_disj hp hK (by simp only [oBuf, oScalar]; omega)) hf hk hp']
    exact h.1 k hk p hp', VG.Proof.MlKem.X86_64.S4.tab_frame (VG.Proof.MlKem.X86_64.S4.c_disj hp hK (a := 0) (n := 2240) (by simp only [oScalar]; omega)) hf h.2⟩

omit hp in
theorem sx6144 : BitVec.signExtend 64 (BitVec.ofNat 32 oScalar) = BitVec.ofNat 64 6144 := by decide

theorem regs {s : State} (he : VG.Proof.MlKem.X86_64.S4.Env σ s) : s.rd ++ s.wr = [VG.Proof.MlKem.X86_64.S4.sdR σ, VG.Proof.MlKem.X86_64.S4.aR σ, VG.Proof.MlKem.X86_64.S4.scrR σ] := by
  rw [he.rd, he.wr, hp.rd, hp.wr]; rfl

theorem cov {s : State} (he : VG.Proof.MlKem.X86_64.S4.Env σ s) {K : Nat} (hK : K < 4) :
    Covers (VG.Proof.MlKem.X86_64.S4.cRd σ K ++ VG.Proof.MlKem.X86_64.S4.cWr σ K) (s.rd ++ s.wr) ∧ Covers (VG.Proof.MlKem.X86_64.S4.cWr σ K) s.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · rw [VG.Proof.MlKem.X86_64.S4.regs hp he]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.MlKem.X86_64.S4.sdR σ, by simp, 34 * K, rfl, by simp only; omega⟩
    · exact ⟨VG.Proof.MlKem.X86_64.S4.aR σ, by simp, 1024 * K, rfl, by simp only; omega⟩
    · exact ⟨VG.Proof.MlKem.X86_64.S4.scrR σ, by simp, oScalar, rfl, by simp only [oScalar]; omega⟩
  · rw [he.wr, hp.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.MlKem.X86_64.S4.aR σ, by simp, 1024 * K, rfl, by simp only; omega⟩
    · exact ⟨VG.Proof.MlKem.X86_64.S4.scrR σ, by simp, oScalar, rfl, by simp only [oScalar]; omega⟩

omit hp in
theorem sx34 {K : Nat} (hK : K < 4) : BitVec.signExtend 64 (BitVec.ofNat 32 (34 * K)) = BitVec.ofNat 64 (34 * K) :=
  sx_ofNat (by omega)

omit hp in
theorem sx1024 {K : Nat} (hK : K < 4) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (1024 * K)) = BitVec.ofNat 64 (1024 * K) := sx_ofNat (by omega)

omit hp in
theorem and14_ok (s : State) :
    WP isa (.block [.alu32 .and .r14 (.reg .rax)]) s fun s' =>
      (s'.gpr .r14 = BitVec.setWidth 64 ((s.gpr .r14).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem) ∧
        Keep [.r14] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- The arguments of the call of `vg_mlkem_sample_ntt` on seed `K`. -/
structure ArgI (X : Mem → Prop) (σ : State) (K : Nat) (s : State) : Prop where
  pinv : VG.Proof.MlKem.X86_64.S4.PC X σ K s
  rdi : s.gpr .rdi = VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 (34 * K)
  rsi : s.gpr .rsi = poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K
  rdx : s.gpr .rdx = VG.Proof.MlKem.X86_64.S4.at' σ oScalar

omit hp in
theorem argsK_ok {X : Mem → Prop} {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlKem.X86_64.S4.PC X σ K s) :
    WP isa (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
      .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
      .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) s (VG.Proof.MlKem.X86_64.S4.ArgI X σ K) :=
  WP.mono (WP.keep [.rdi, .rsi, .rdx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 (34 * K) ∧ s'.gpr .rsi = poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K ∧ s'.gpr .rdx = VG.Proof.MlKem.X86_64.S4.at' σ oScalar)
    (by xrun [h.env.r12, h.env.r13, h.env.rbx, VG.Proof.MlKem.X86_64.S4.sx34 hK, VG.Proof.MlKem.X86_64.S4.sx1024 hK, VG.Proof.MlKem.X86_64.S4.sx6144]; exact ⟨rfl, rfl⟩) rfl)
    fun _ ⟨⟨hm₂, hdi, hsi, hdx⟩, k₂⟩ => ⟨h.keep hm₂ k₂ (by decide), hdi, hsi, hdx⟩

theorem argK_kS {X : Mem → Prop} {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlKem.X86_64.S4.ArgI X σ K s) :
    (below (s.gpr .rsp) 24).Disjoint ⟨VG.Proof.MlKem.X86_64.S4.sd σ + BitVec.ofNat 64 (34 * K), 34⟩ := by
  rw [h.pinv.env.rsp]; exact hp.stk_sd.sub_right (Offset.sub_base (VG.Proof.MlKem.X86_64.S4.sd σ) (d := 34 * K) (n := 34) (by omega))

theorem argK_pre {X : Mem → Prop} {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlKem.X86_64.S4.ArgI X σ K s) :
    sampleK.pre (s.callEntry.withRegions (VG.Proof.MlKem.X86_64.S4.cRd σ K) (VG.Proof.MlKem.X86_64.S4.cWr σ K)) := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := h.pinv.env.rsp
  have kS := VG.Proof.MlKem.X86_64.S4.argK_kS hp hK h
  have kA : (below (s.gpr .rsp) 24).Disjoint (pR (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K)) := by
    rw [hsp]; exact hp.stk_a.sub_right (VG.Proof.MlKem.X86_64.S4.sub_poly (σ := σ) hK)
  have kZ : (below (s.gpr .rsp) 24).Disjoint ⟨VG.Proof.MlKem.X86_64.S4.at' σ oScalar, 2048⟩ := by
    rw [hsp]; exact hp.stk_scr.sub_right (VG.Proof.MlKem.X86_64.S4.sub_scr (σ := σ) (a := oScalar) (n := 2048) (by simp only [oScalar]; omega))
  simp only [sampleK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s (by decide : Reg.rdi ≠ .rsp), ce_gpr' s (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rdx ≠ .rsp), h.rdi, h.rsi, h.rdx]
  exact ⟨trivial, trivial,
    (hp.sd_a.sub_left (Offset.sub_base _ (by omega))).sub_right (VG.Proof.MlKem.X86_64.S4.sub_poly hK),
    (hp.sd_scr.sub_left (Offset.sub_base _ (by omega))).sub_right (VG.Proof.MlKem.X86_64.S4.sub_scr (by simp only [oScalar]; omega)),
    (hp.a_scr.sub_left (VG.Proof.MlKem.X86_64.S4.sub_poly hK)).sub_right (VG.Proof.MlKem.X86_64.S4.sub_scr (by simp only [oScalar]; omega)),
    ret_disj24 s kS, ret_disj24 s kA, ret_disj24 s kZ, stk_disj24' s kS, stk_disj24' s kA, stk_disj24' s kZ,
    VG.Proof.MlKem.X86_64.S4.scr6144_lt hp⟩

/-- After the call of `vg_mlkem_sample_ntt` on seed `K`. -/
structure CallI (X : Mem → Prop) (σ : State) (K : Nat) (s : State) : Prop where
  pinv : VG.Proof.MlKem.X86_64.S4.PC X σ K s
  rax : (s.gpr .rax).setWidth 32 = if (sampleNTT minIterations (VG.Proof.MlKem.X86_64.S4.B σ K)).isSome then 1 else 0
  poly : ∀ f, sampleNTT minIterations (VG.Proof.MlKem.X86_64.S4.B σ K) = some f → PolyIs s.mem (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K) f

theorem callK_ok {X : Mem → Prop} {K : Nat} (hK : K < 4)
    (hX : ∀ m m', Frame (VG.Proof.MlKem.X86_64.S4.cWr σ K ++ [VG.Proof.MlKem.X86_64.S4.stkR σ]) m m' → X m → X m') {s : State} (h : VG.Proof.MlKem.X86_64.S4.ArgI X σ K s) :
    WP isa (.call "vg_mlkem_sample_ntt" sampleNTT) s (VG.Proof.MlKem.X86_64.S4.CallI X σ K) := by
  have hcv := VG.Proof.MlKem.X86_64.S4.cov hp h.pinv.env hK
  refine WP.call sample_correct VG.Proof.MlKem.X86_64.sample_nosp (by rw [VG.Proof.MlKem.X86_64.sample_depth]; decide) (VG.Proof.MlKem.X86_64.S4.argK_pre hp hK h) hcv.1 hcv.2
    fun s₃ hrd hwr hcs hf _ ⟨s₃', hm₃, hg₃, hpost⟩ => ?_
  rw [VG.Proof.MlKem.X86_64.sample_depth, h.pinv.env.rsp] at hf
  have h₃ : VG.Proof.MlKem.X86_64.S4.PC X σ K s₃ := h.pinv.call hp hK hrd hwr (fun r hr => hcs r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) hf hX
  simp only [sampleK, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s (by decide : Reg.rsi ≠ .rsp), h.rdi, h.rsi, hm₃, ce_bytesAt24 s (n := 34) (by decide) (VG.Proof.MlKem.X86_64.S4.argK_kS hp hK h),
    VG.Proof.MlKem.X86_64.S4.seed_bytes hp hK h.pinv.env.frame] at hpost
  rw [hg₃ .rax (by decide)] at hpost
  exact ⟨h₃, hpost.1, hpost.2⟩

omit hp in
theorem andK_ok {X : Mem → Prop} {K : Nat} {s : State} (h : VG.Proof.MlKem.X86_64.S4.CallI X σ K s) :
    WP isa (.block [.alu32 .and .r14 (.reg .rax)]) s (VG.Proof.MlKem.X86_64.S4.PC X σ (K + 1)) := by
  refine WP.mono (VG.Proof.MlKem.X86_64.S4.and14_ok s) fun s₄ ⟨⟨h14, hm₄⟩, k₄⟩ => ?_
  have h₃ := h.pinv
  refine ⟨⟨k₄.2.1.trans h₃.env.rd, k₄.2.2.trans h₃.env.wr, by rw [k₄.gpr (by decide), h₃.env.rbx],
      by rw [k₄.gpr (by decide), h₃.env.r12], by rw [k₄.gpr (by decide), h₃.env.r13],
      by rw [k₄.gpr (by decide), h₃.env.rsp], by rw [k₄.gpr (by decide), h₃.env.r15],
      by rw [hm₄]; exact h₃.env.saved, by rw [hm₄]; exact h₃.env.frame⟩,
    by rw [hm₄]; exact h₃.buf, by rw [h14, h₃.r14, h.rax, VG.Proof.MlKem.X86_64.S4.okN_succ], fun k hk f e => ?_⟩
  rw [hm₄]
  by_cases ek : k = K
  · subst ek; exact h.poly f e
  · exact h₃.polys k (by omega) f e

/-- The call of `vg_mlkem_sample_ntt` on seed `K`. -/
theorem call_ok {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlKem.X86_64.S4.PInv σ K s) :
    WP isa (.seq (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
          .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
          .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))])
        (.seq (.call "vg_mlkem_sample_ntt" sampleNTT) (.block [.alu32 .and .r14 (.reg .rax)]))) s
      (VG.Proof.MlKem.X86_64.S4.PInv σ (K + 1)) :=
  WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.argsK_ok hK h) fun _ h₂ => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.callK_ok hp hK (VG.Proof.MlKem.X86_64.S4.bufOK_call hp hK) h₂)
    fun _ h₃ => VG.Proof.MlKem.X86_64.S4.andK_ok h₃))

/-- After the check of `j`. -/
structure MI (σ : State) (K : Nat) (s : State) : Prop where
  pinv : VG.Proof.MlKem.X86_64.S4.PInv σ K s
  stored : Stored s.mem (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K) (VG.Proof.MlKem.X86_64.S4.Lt σ K 168)
  cf : s.cf = some (decide ((VG.Proof.MlKem.X86_64.S4.Lt σ K 168).length < 256))

omit hp in
theorem cmpK_ok {K : Nat} {s : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K 168 s) : WP isa (.block [.alu .cmp .rdi (.imm 256)]) s (VG.Proof.MlKem.X86_64.S4.MI σ K) := by
  refine WP.mono (cmpRdi_ok s) fun s₁ ⟨hc, hm, hg, hrd, hwr⟩ => ?_
  have hL : (VG.Proof.MlKem.X86_64.S4.Lt σ K 168).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ 168
  rw [h.rdi, ofNat64_toNat (by omega)] at hc
  exact ⟨h.pinv.keep hm (rs := []) ⟨fun r _ => by rw [hg], hrd, hwr⟩ (by simp), by rw [hm]; exact h.stored, hc⟩

omit hp in
/-- Without the call, if `j = 256`. -/
theorem skipK_ok {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlKem.X86_64.S4.MI σ K s) (hb : s.cf = some false) : VG.Proof.MlKem.X86_64.S4.PInv σ (K + 1) s := by
  have hL : (VG.Proof.MlKem.X86_64.S4.Lt σ K 168).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ 168
  have hfull : (VG.Proof.MlKem.X86_64.S4.Lt σ K 168).length = 256 := by
    rw [h.cf, Option.some.injEq, decide_eq_false_iff_not] at hb; omega
  have hs : sampleNTT minIterations (VG.Proof.MlKem.X86_64.S4.B σ K) = some (toPoly (VG.Proof.MlKem.X86_64.S4.Lt σ K 168)) :=
    sampleNTT_of_full (by decide) (by rw [n_eq]; exact hfull)
  refine ⟨h.pinv.env, h.pinv.buf, ?_, fun k hk f e => ?_⟩
  · have e : VG.Proof.MlKem.X86_64.S4.okN σ (K + 1) = VG.Proof.MlKem.X86_64.S4.okN σ K := by
      simp only [VG.Proof.MlKem.X86_64.S4.okN, List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true, hs,
        Option.isSome_some]
    rw [h.pinv.r14, e]
  · by_cases ek : k = K
    · subst ek
      rw [hs] at e
      rw [← Option.some.inj e]
      exact SampleNtt.stored_polyAt h.stored hfull
    · exact h.pinv.polys k (by omega) f e

/-- The check of `j`, and the call if it is less than 256. -/
theorem fallback_ok {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K 168 s) :
    WP isa (fallback K) s (VG.Proof.MlKem.X86_64.S4.PInv σ (K + 1)) := by
  unfold fallback
  exact WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.cmpK_ok h) fun s₁ h₁ => WP.ite _ h₁.cf (fun _ => VG.Proof.MlKem.X86_64.S4.call_ok hp hK h₁.pinv)
    fun hb => WP.block_nil (VG.Proof.MlKem.X86_64.S4.skipK_ok hK h₁ (by rw [h₁.cf, hb])))

end

end VG.Proof.MlKem.X86_64.S4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.S4Tab`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the table

After the squeezes, the code writes the table of the sampling and the
constants of the vector code over the states, quadword by quadword (`tab_ok`);
with the output of the squeezes, which it does not touch, they make `PInv σ 0`
(`pinv0_ok`).
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Proof.Sha3.X86_64 (wp_movi64 wp_store wp_nil)

/-- During the writes of the table, from `s₀`. -/
structure TabInv (σ s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep [.rax] s₀ s
  frame : Frame [⟨VG.Proof.MlKem.X86_64.S4.at' σ 0, 2240⟩] s₀.mem s.mem
  tab : ∀ i < n, s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (8 * i)) 64 = tabQ i

theorem tab_step {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {s₀ : State} (he : VG.Proof.MlKem.X86_64.S4.Env σ s₀) {i : Nat} (hi : i < 280) {s : State}
    (h : VG.Proof.MlKem.X86_64.S4.TabInv σ s₀ i s) :
    WP isa (.block [.movImm64 .rax (tabQ i), .store (at_ .rbx (8 * i)) .rax]) s (VG.Proof.MlKem.X86_64.S4.TabInv σ s₀ (i + 1)) := by
  have hbx : s.gpr .rbx = VG.Proof.MlKem.X86_64.S4.scr σ := by rw [h.keep.gpr (by decide), he.rbx]
  refine wp_movi64 fun s₁ u₁ => wp_store (a := VG.Proof.MlKem.X86_64.S4.at' σ (8 * i)) (by rw [ea_at, u₁.other _ (by decide), hbx])
    (by rw [u₁.wr, h.keep.2.2, he.wr]; exact VG.Proof.MlKem.X86_64.S4.in_scr hp rfl (by omega)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.S4.at' σ (8 * i)) (tabQ i) := by rw [m₂, u₁.mem, u₁.gpr]
  refine ⟨⟨fun g hg => by rw [g₂, u₁.other g (by simpa using hg), h.keep.gpr hg], by rw [r₂, u₁.rd, h.keep.2.1],
    by rw [w₂, u₁.wr, h.keep.2.2]⟩, ?_, fun i' hi' => ?_⟩
  · rw [hm]
    exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  · rw [hm]
    by_cases e : i' = i
    · subst e; exact Mem.readW_writeW_self64 _ _ _
    · rw [VG.Proof.MlKem.X86_64.S4.rd64_off (by omega) (by omega) (by omega)]
      exact h.tab i' (by omega)

theorem tabBuild_eq : tabBuild = (List.range 280).flatMap fun i =>
    [.movImm64 .rax (tabQ i), .store (at_ .rbx (8 * i)) .rax] := rfl

/-- The table and the constants. -/
theorem tab_ok {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {s₀ : State} (he : VG.Proof.MlKem.X86_64.S4.Env σ s₀) :
    WP isa (.block tabBuild) s₀ (VG.Proof.MlKem.X86_64.S4.TabInv σ s₀ 280) := by
  rw [VG.Proof.MlKem.X86_64.S4.tabBuild_eq]
  exact wp_range_flatMap (M := isa) (VG.Proof.MlKem.X86_64.S4.TabInv σ s₀) (fun i s hi h => VG.Proof.MlKem.X86_64.S4.tab_step hp he hi h) 280 (Nat.le_refl _) s₀
    ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (by omega)⟩

/-- After the squeezes and the table, before the first polynomial. -/
theorem pinv0_ok {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ) {s : State} (h : VG.Proof.MlKem.X86_64.S4.SqInv σ 3 s) :
    WP isa (.block tabBuild) s (VG.Proof.MlKem.X86_64.S4.PInv σ 0) := by
  refine WP.mono (VG.Proof.MlKem.X86_64.S4.tab_ok hp h.env) fun s' h' => ?_
  have hsub : ∀ r ∈ [(⟨VG.Proof.MlKem.X86_64.S4.at' σ 0, 2240⟩ : Region)], Region.Sub r ⟨VG.Proof.MlKem.X86_64.S4.scr σ, oSave⟩ := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [oSave]; omega)
  refine ⟨Env.low h.env hsub h'.frame h'.keep.2.1 h'.keep.2.2 fun r hr => h'.keep.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    ⟨fun k hk p hp' => ?_, fun i hi => h'.tab i hi⟩, by rw [h'.keep.gpr (by decide), h.r14]; rfl,
    fun _ h _ _ => absurd h (by omega)⟩
  have hd := Offset.disjoint (VG.Proof.MlKem.X86_64.S4.scr σ) (d := oBuf) (n := 2016) (e := 0) (k := 2240) (.inr (by simp only [oBuf]; omega))
    (by simp only [oBuf]; omega) (by omega)
  rw [VG.Proof.MlKem.X86_64.S4.buf_frame (by simpa using hd) h'.frame hk hp']
  exact h.buf k hk p (by omega)

end VG.Proof.MlKem.X86_64.S4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.S4Vec`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, the vector sampling

Four iterations of `SampleNTT`'s loop, from fewer than 249 coefficients,
append the candidates less than `q` of their 12 bytes (`sampleAfter_four`).
The code computes the eight candidates in the doublewords of `ymm0`
(`cand_dword`) and their mask in `eax` (`vcand_ok`), and stores the
doublewords that the table's entry for the mask selects (`vput_ok`): those of
the candidates less than `q`, in order (`setBits_bsum`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- Candidate `k < 8` of the four chunks of `out` from byte `p`: `d₁` (`k`
even) or `d₂` (`k` odd) of chunk `k / 2`. -/
def cand4 (out : Nat → Byte) (p k : Nat) : Nat :=
  if k % 2 = 0 then (out (p + 3 * (k / 2))).toNat + 256 * ((out (p + 3 * (k / 2) + 1)).toNat % 16)
  else (out (p + 3 * (k / 2) + 1)).toNat / 16 + 16 * (out (p + 3 * (k / 2) + 2)).toNat

/-- The candidates less than `q` of the four chunks from byte `p`, as coefficients. -/
def acc4 (out : Nat → Byte) (p : Nat) : List Zq :=
  ((List.range 8).filter fun k => decide (VG.Proof.MlKem.cand4 out p k < q)).map fun k => ofNat (VG.Proof.MlKem.cand4 out p k)

/-- The coefficients a chunk adds, if there is room for two. -/
def pair (c₀ c₁ c₂ : Byte) : List Zq :=
  (if c₀.toNat + 256 * (c₁.toNat % 16) < q then [ofNat (c₀.toNat + 256 * (c₁.toNat % 16))] else []) ++
    (if c₁.toNat / 16 + 16 * c₂.toNat < q then [ofNat (c₁.toNat / 16 + 16 * c₂.toNat)] else [])

theorem pair_length (c₀ c₁ c₂ : Byte) : (VG.Proof.MlKem.pair c₀ c₁ c₂).length ≤ 2 := by
  unfold VG.Proof.MlKem.pair; split <;> split <;> simp

theorem sampleStepCap_room {a : List Zq} (h : a.length + 2 ≤ n) (c₀ c₁ c₂ : Byte) :
    sampleStepCap a c₀ c₁ c₂ = a ++ VG.Proof.MlKem.pair c₀ c₁ c₂ := by
  unfold sampleStepCap sampleStep VG.Proof.MlKem.pair
  rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by bdd_omega))]
  dsimp only
  split <;> split <;> simp_all <;> omega

theorem fm2 {α : Type} (p : Nat → Bool) (f : Nat → α) (k : Nat) :
    ([k, k + 1].filter p).map f = (if p k then [f k] else []) ++ (if p (k + 1) then [f (k + 1)] else []) := by
  simp only [List.filter_cons, List.filter_nil]
  cases p k <;> cases p (k + 1) <;> rfl

theorem acc4_eq (out : Nat → Byte) (p : Nat) : VG.Proof.MlKem.acc4 out p =
    VG.Proof.MlKem.pair (out p) (out (p + 1)) (out (p + 2)) ++ VG.Proof.MlKem.pair (out (p + 3)) (out (p + 4)) (out (p + 5)) ++
      VG.Proof.MlKem.pair (out (p + 6)) (out (p + 7)) (out (p + 8)) ++ VG.Proof.MlKem.pair (out (p + 9)) (out (p + 10)) (out (p + 11)) := by
  rw [VG.Proof.MlKem.acc4, show List.range 8 = [0, 0 + 1] ++ [2, 2 + 1] ++ [4, 4 + 1] ++ [6, 6 + 1] from rfl]
  simp only [List.filter_append, List.map_append, VG.Proof.MlKem.fm2, decide_eq_true_eq, VG.Proof.MlKem.pair, VG.Proof.MlKem.cand4]
  simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul, ite_true, Nat.add_zero, Nat.add_assoc,
    Nat.zero_add, show (1 % 2 = 0) = False from by decide, ite_false, List.append_assoc, decide_eq_true_eq]

theorem sampleAfter_four {a : List Zq} {out : Nat → Byte} {t : Nat}
    (h : (sampleAfter a out t).length + 8 ≤ n) :
    sampleAfter a out (t + 4) = sampleAfter a out t ++ VG.Proof.MlKem.acc4 out (3 * t) := by
  have p0 := VG.Proof.MlKem.pair_length (out (3 * t)) (out (3 * t + 1)) (out (3 * t + 2))
  have p1 := VG.Proof.MlKem.pair_length (out (3 * (t + 1))) (out (3 * (t + 1) + 1)) (out (3 * (t + 1) + 2))
  have p2 := VG.Proof.MlKem.pair_length (out (3 * (t + 2))) (out (3 * (t + 2) + 1)) (out (3 * (t + 2) + 2))
  rw [sampleAfter_succ, sampleAfter_succ, sampleAfter_succ, sampleAfter_succ,
    VG.Proof.MlKem.sampleStepCap_room (a := sampleAfter a out t) (by bdd_omega),
    VG.Proof.MlKem.sampleStepCap_room (a := sampleAfter a out t ++ _) (by simp only [List.length_append]; omega),
    VG.Proof.MlKem.sampleStepCap_room (a := sampleAfter a out t ++ _ ++ _) (by simp only [List.length_append]; omega),
    VG.Proof.MlKem.sampleStepCap_room (a := sampleAfter a out t ++ _ ++ _ ++ _) (by simp only [List.length_append]; omega),
    VG.Proof.MlKem.acc4_eq]
  simp only [List.append_assoc, show 3 * (t + 1) = 3 * t + 3 by bdd_omega, show 3 * (t + 2) = 3 * t + 6 by bdd_omega,
    show 3 * (t + 3) = 3 * t + 9 by bdd_omega, Nat.add_assoc, Nat.reduceAdd]

end VG.Proof.MlKem

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Spec.MlKem

/-- The coefficients `L ++ A` are stored after a write of eight doublewords `V` at
`a[|L|]`, whose first `|A|` doublewords are `A`. -/
theorem stored_write8 {m : Mem} {aP : Addr} {L A : List Zq} (h : Stored m aP L) (hl : L.length + 8 ≤ 256)
    (hA : A.length ≤ 8) (V : BitVec 256)
    (hV : ∀ i < A.length, V.extractLsb' (32 * i) 32 = BitVec.ofNat 32 (A.getD i 0).val) :
    Stored (m.writeW (coeffAddr aP L.length) V) aP (L ++ A) := by
  intro k hk
  rw [List.length_append] at hk
  rw [coeffAt_eq]
  by_cases hkL : k < L.length
  · rw [readW_writeW_off m aP V (d := 4 * k) (e := 4 * L.length) (n := 4) (by bdd_omega) (by bdd_omega) (by bdd_omega),
      show (L ++ A).getD k 0 = L.getD k 0 by simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hkL]]
    exact h k hkL
  · have e := readW_writeW_inside m (coeffAddr aP L.length) V (k := 4 * (k - L.length)) (n := 4) (by bdd_omega)
      (by decide)
    rw [coeffAddr, Offset.add_add, show 4 * L.length + 4 * (k - L.length) = 4 * k by bdd_omega] at e
    rw [e, show 8 * (4 * (k - L.length)) = 32 * (k - L.length) by bdd_omega, hV _ (by bdd_omega),
      show (L ++ A).getD k 0 = A.getD (k - L.length) 0 by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show L.length ≤ k by bdd_omega)]]

end VG.Proof.MlKem.X86_64

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64
open VG.Impl.MlKem.X86_64.Sample4 (vcand vput tabE aV setBits)
open VG.Proof.Sha3.X86_64 (WP.cons Upd)

def shuf0 : BitVec 128 := 0x80800504808004038080020180800100#128
def shuf1 : BitVec 128 := 0x80800b0a80800a098080080780800706#128
def shV : BitVec 128 := 0x00000004000000000000000400000000#128
def maskV : BitVec 128 := 0x00000fff00000fff00000fff00000fff#128

/-- The first byte of candidate `k`'s pair: `3 (k / 2) + k % 2`. -/
abbrev cb (k : Nat) : Nat := 3 * (k / 2) + k % 2

/-- Candidate `k` of the bytes `b`. -/
def candN (b : Nat → Nat) (k : Nat) : Nat :=
  if k % 2 = 0 then b (VG.Proof.MlKem.X86_64.S4.cb k) + 256 * (b (VG.Proof.MlKem.X86_64.S4.cb k + 1) % 16) else b (VG.Proof.MlKem.X86_64.S4.cb k) / 16 + 16 * b (VG.Proof.MlKem.X86_64.S4.cb k + 1)

theorem gb {f : Nat → BitVec 8} {a b c d : Nat} (h1 : a = c) (h2 : b = d) :
    (f a).getLsbD b = (f c).getLsbD d := by subst h1 h2; rfl

theorem toNat_dword_ofBytes (f : Nat → BitVec 8) {j : Nat} (hj : j < 4) :
    (dword (ofBytes f) j).toNat = (f (4 * j)).toNat + 256 * (f (4 * j + 1)).toNat +
      65536 * (f (4 * j + 2)).toNat + 16777216 * (f (4 * j + 3)).toNat := by
  have e : dword (ofBytes f) j = f (4 * j + 3) ++ f (4 * j + 2) ++ f (4 * j + 1) ++ f (4 * j) := by
    apply BitVec.eq_of_getLsbD_eq; intro m hm
    rw [getLsbD_dword_ofBytes _ hj hm]
    simp only [BitVec.getLsbD_append]
    have h8 := Nat.mod_lt m (show 8 > 0 by decide)
    by_cases a : m < 8
    · simp only [a, ite_true]; exact VG.Proof.MlKem.X86_64.S4.gb (by bdd_omega) (by bdd_omega)
    by_cases b : m - 8 < 8
    · simp only [a, b, ite_true, ite_false]; exact VG.Proof.MlKem.X86_64.S4.gb (by bdd_omega) (by bdd_omega)
    by_cases c : m - 8 - 8 < 8
    · simp only [a, b, c, ite_true, ite_false]; exact VG.Proof.MlKem.X86_64.S4.gb (by bdd_omega) (by bdd_omega)
    · simp only [a, b, c, ite_false]; exact VG.Proof.MlKem.X86_64.S4.gb (by bdd_omega) (by bdd_omega)
  rw [e]
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (f (4 * j + 2)).isLt, ← Nat.shiftLeft_add_eq_or_of_lt (f (4 * j + 1)).isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt (f (4 * j)).isLt]
  simp only [Nat.shiftLeft_eq]
  have := (f (4 * j)).isLt; have := (f (4 * j + 1)).isLt; have := (f (4 * j + 2)).isLt
  have := (f (4 * j + 3)).isLt
  omega

theorem pshufb_shuf0 (a : BitVec 128) : XBinOp.eval .pshufb a VG.Proof.MlKem.X86_64.S4.shuf0 =
    ofBytes fun i => if i % 4 < 2 then VG.X86_64.byte a (VG.Proof.MlKem.X86_64.S4.cb (i / 4) + i % 4) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_shuf1 (a : BitVec 128) : XBinOp.eval .pshufb a VG.Proof.MlKem.X86_64.S4.shuf1 =
    ofBytes fun i => if i % 4 < 2 then VG.X86_64.byte a (6 + VG.Proof.MlKem.X86_64.S4.cb (i / 4) + i % 4) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

/-- The `vpshufb` mask of lane `l`. -/
abbrev shuf (l : Nat) : BitVec 128 := if l = 0 then VG.Proof.MlKem.X86_64.S4.shuf0 else VG.Proof.MlKem.X86_64.S4.shuf1

/-- The candidates in lane `l` of `ymm0`, from `a`, the 16 bytes in both. -/
abbrev candV (a : BitVec 128) (l : Nat) : BitVec 128 :=
  XBinOp.eval .pand (VVarOp.eval .vpsrlvd (XBinOp.eval .pshufb a (VG.Proof.MlKem.X86_64.S4.shuf l)) VG.Proof.MlKem.X86_64.S4.shV) VG.Proof.MlKem.X86_64.S4.maskV

theorem toNat_and_fff (x : BitVec 32) : (x &&& 0xfff#32).toNat = x.toNat % 4096 := by
  rw [BitVec.toNat_and, show (0xfff#32).toNat = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem cand_dword (a : BitVec 128) {l j : Nat} (hl : l < 2) (hj : j < 4) :
    dword (VG.Proof.MlKem.X86_64.S4.candV a l) j = BitVec.ofNat 32 (VG.Proof.MlKem.X86_64.S4.candN (fun i => (VG.X86_64.byte a i).toNat) (4 * l + j)) := by
  apply BitVec.eq_of_toNat_eq
  rw [dword_pand, (show ∀ i < 4, dword VG.Proof.MlKem.X86_64.S4.maskV i = 0xfff#32 by decide) j hj, VG.Proof.MlKem.X86_64.S4.toNat_and_fff]
  have hb : ∀ i, (VG.X86_64.byte a i).toNat < 256 := fun i => (VG.X86_64.byte a i).isLt
  rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rcases cases4 hj with rfl | rfl | rfl | rfl <;>
  simp only [VG.Proof.MlKem.X86_64.S4.shuf, VVarOp.eval, VG.Proof.MlKem.X86_64.S4.pshufb_shuf0, VG.Proof.MlKem.X86_64.S4.pshufb_shuf1, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, ↓reduceIte, show (dword VG.Proof.MlKem.X86_64.S4.shV 0).toNat = 0 from rfl, show (dword VG.Proof.MlKem.X86_64.S4.shV 1).toNat = 4 from rfl,
    show (dword VG.Proof.MlKem.X86_64.S4.shV 2).toNat = 0 from rfl, show (dword VG.Proof.MlKem.X86_64.S4.shV 3).toNat = 4 from rfl, Nat.reduceLT,
    BitVec.toNat_ushiftRight,
    VG.Proof.MlKem.X86_64.S4.toNat_dword_ofBytes _ (show 0 < 4 by decide), VG.Proof.MlKem.X86_64.S4.toNat_dword_ofBytes _ (show 1 < 4 by decide),
    VG.Proof.MlKem.X86_64.S4.toNat_dword_ofBytes _ (show 2 < 4 by decide), VG.Proof.MlKem.X86_64.S4.toNat_dword_ofBytes _ (show 3 < 4 by decide),
    VG.Proof.MlKem.X86_64.S4.candN, VG.Proof.MlKem.X86_64.S4.cb, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show (0 : BitVec 8).toNat = 0 from rfl, Nat.reduceEqDiff, Nat.add_zero] <;>
  omega

def qV4 : BitVec 128 := 0x00000d0100000d0100000d0100000d01#128
def sign0 : BitVec 128 := 0x0f0b0703808080808080808080808080#128
def sign1 : BitVec 128 := 0x8080808080808080808080800f0b0703#128

theorem pshufb_sign0 (a : BitVec 128) : XBinOp.eval .pshufb a VG.Proof.MlKem.X86_64.S4.sign0 =
    ofBytes fun i => if 12 ≤ i then VG.X86_64.byte a (4 * (i - 12) + 3) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

theorem pshufb_sign1 (a : BitVec 128) : XBinOp.eval .pshufb a VG.Proof.MlKem.X86_64.S4.sign1 =
    ofBytes fun i => if i < 4 then VG.X86_64.byte a (4 * i + 3) else 0 := by
  simp only [XBinOp.eval, ofBytes]
  rfl

/-- `∑ i < n, f i · 2ⁱ`. -/
def bsum (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => VG.Proof.MlKem.X86_64.S4.bsum f n + (f n).toNat * 2 ^ n

theorem bsum_lt (f : Nat → Bool) : ∀ n, VG.Proof.MlKem.X86_64.S4.bsum f n < 2 ^ n
  | 0 => by simp [VG.Proof.MlKem.X86_64.S4.bsum]
  | n + 1 => by
    have := VG.Proof.MlKem.X86_64.S4.bsum_lt f n
    simp only [VG.Proof.MlKem.X86_64.S4.bsum, Nat.pow_succ]
    cases f n <;> simp <;> omega

theorem byteMask_eq (x : BitVec 256) {n : Nat} (hn : n ≤ 64) :
    byteMask x n = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.S4.bsum (fun i => x.getLsbD (8 * i + 7)) n) := by
  unfold byteMask
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih (by bdd_omega), List.foldl_cons, List.foldl_nil, VG.Proof.MlKem.X86_64.S4.bsum]
    have hl := VG.Proof.MlKem.X86_64.S4.bsum_lt (fun i => x.getLsbD (8 * i + 7)) n
    have h1 : 2 ^ n < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by bdd_omega)
    cases x.getLsbD (8 * n + 7)
    · simp
    · simp only [ite_true, Bool.toNat_true, Nat.one_mul]
      apply BitVec.eq_of_toNat_eq
      have h2 : 2 ^ n ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by bdd_omega)
      have e := Nat.two_pow_add_eq_or_of_lt hl 1
      rw [Nat.mul_one] at e
      rw [BitVec.toNat_or, BitVec.toNat_twoPow, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
        Nat.mod_eq_of_lt (by bdd_omega), Nat.mod_eq_of_lt (by bdd_omega), Nat.or_comm, ← e, Nat.add_comm]

theorem bsum_congr {f g : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = g i) : VG.Proof.MlKem.X86_64.S4.bsum f n = VG.Proof.MlKem.X86_64.S4.bsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.MlKem.X86_64.S4.bsum, VG.Proof.MlKem.X86_64.S4.bsum, ih fun i hi => h i (by bdd_omega), h n (by bdd_omega)]

theorem itT {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a :=
  ite_eq_left_of_eq_true a b (eq_true h)

theorem itF {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b :=
  ite_eq_right_of_eq_false a b (eq_false h)

theorem byte3_bit7 (X : BitVec 128) (j : Nat) : (VG.X86_64.byte X (4 * j + 3)).getLsbD 7 = (dword X j).getLsbD 31 := by
  rw [VG.X86_64.byte, BitVec.getLsbD_extractLsb', getLsbD_dword]
  simp only [show 7 < 8 by decide, show 31 < 32 by decide, decide_true, Bool.true_and]
  exact congrArg _ (by bdd_omega)

/-- Bit 7 of byte `i` of the two lanes after the `vpshufb` with the sign masks. -/
theorem sign_bit (X0 X1 : BitVec 128) {i : Nat} (hi : i < 32) :
    (XBinOp.eval .pshufb X1 VG.Proof.MlKem.X86_64.S4.sign1 ++ XBinOp.eval .pshufb X0 VG.Proof.MlKem.X86_64.S4.sign0).getLsbD (8 * i + 7) =
      if 12 ≤ i ∧ i < 16 then (dword X0 (i - 12)).getLsbD 31
      else if 16 ≤ i ∧ i < 20 then (dword X1 (i - 16)).getLsbD 31 else false := by
  rw [BitVec.getLsbD_append, VG.Proof.MlKem.X86_64.S4.pshufb_sign0, VG.Proof.MlKem.X86_64.S4.pshufb_sign1]
  by_cases h : i < 16
  · have h7 : 8 * i + 7 < 128 := by bdd_omega
    rw [VG.Proof.MlKem.X86_64.S4.itT h7, getLsbD_ofBytes _ h (by decide)]
    by_cases h' : 12 ≤ i
    · rw [VG.Proof.MlKem.X86_64.S4.itT h', VG.Proof.MlKem.X86_64.S4.itT (show 12 ≤ i ∧ i < 16 from ⟨h', h⟩), VG.Proof.MlKem.X86_64.S4.byte3_bit7]
    · rw [VG.Proof.MlKem.X86_64.S4.itF h', VG.Proof.MlKem.X86_64.S4.itF (show ¬ (12 ≤ i ∧ i < 16) by bdd_omega), VG.Proof.MlKem.X86_64.S4.itF (show ¬ (16 ≤ i ∧ i < 20) by bdd_omega)]; rfl
  · have h7 : ¬ 8 * i + 7 < 128 := by bdd_omega
    have hk : i - 16 < 16 := by bdd_omega
    rw [VG.Proof.MlKem.X86_64.S4.itF h7, show 8 * i + 7 - 128 = 8 * (i - 16) + 7 by bdd_omega, getLsbD_ofBytes _ hk (by decide),
      VG.Proof.MlKem.X86_64.S4.itF (show ¬ (12 ≤ i ∧ i < 16) by bdd_omega)]
    by_cases h' : i < 20
    · rw [VG.Proof.MlKem.X86_64.S4.itT (show i - 16 < 4 by bdd_omega), VG.Proof.MlKem.X86_64.S4.itT (show 16 ≤ i ∧ i < 20 from ⟨by bdd_omega, h'⟩), VG.Proof.MlKem.X86_64.S4.byte3_bit7]
    · rw [VG.Proof.MlKem.X86_64.S4.itF (show ¬ i - 16 < 4 by bdd_omega), VG.Proof.MlKem.X86_64.S4.itF (show ¬ (16 ≤ i ∧ i < 20) by bdd_omega)]; rfl

theorem bsum_add (f : Nat → Bool) (n : Nat) :
    ∀ m, VG.Proof.MlKem.X86_64.S4.bsum f (n + m) = VG.Proof.MlKem.X86_64.S4.bsum f n + 2 ^ n * VG.Proof.MlKem.X86_64.S4.bsum (fun i => f (n + i)) m
  | 0 => by rw [Nat.add_zero, VG.Proof.MlKem.X86_64.S4.bsum, Nat.mul_zero, Nat.add_zero]
  | m + 1 => by
    rw [← Nat.add_assoc, VG.Proof.MlKem.X86_64.S4.bsum, VG.Proof.MlKem.X86_64.S4.bsum_add f n m, VG.Proof.MlKem.X86_64.S4.bsum, Nat.pow_add, Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm]

theorem bsum_false {f : Nat → Bool} {n : Nat} (h : ∀ i < n, f i = false) : VG.Proof.MlKem.X86_64.S4.bsum f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VG.Proof.MlKem.X86_64.S4.bsum, ih fun i hi => h i (by bdd_omega), h n (by bdd_omega), Bool.toNat_false, Nat.zero_mul]

theorem mask_bsum (X0 X1 : BitVec 128) :
    VG.Proof.MlKem.X86_64.S4.bsum (fun i => (XBinOp.eval .pshufb X1 VG.Proof.MlKem.X86_64.S4.sign1 ++ XBinOp.eval .pshufb X0 VG.Proof.MlKem.X86_64.S4.sign0).getLsbD (8 * i + 7)) 32 =
      4096 * VG.Proof.MlKem.X86_64.S4.bsum (fun k => if k < 4 then (dword X0 k).getLsbD 31 else (dword X1 (k - 4)).getLsbD 31) 8 := by
  rw [VG.Proof.MlKem.X86_64.S4.bsum_congr fun i hi => VG.Proof.MlKem.X86_64.S4.sign_bit X0 X1 hi, show ∀ g, VG.Proof.MlKem.X86_64.S4.bsum g 32 = VG.Proof.MlKem.X86_64.S4.bsum g (12 + 8 + 12) from fun _ => rfl,
    VG.Proof.MlKem.X86_64.S4.bsum_add, VG.Proof.MlKem.X86_64.S4.bsum_add]
  have h0 : ∀ i < 12, (if 12 ≤ i ∧ i < 16 then (dword X0 (i - 12)).getLsbD 31
      else if 16 ≤ i ∧ i < 20 then (dword X1 (i - 16)).getLsbD 31 else false) = false := fun i hi => by
    rw [VG.Proof.MlKem.X86_64.S4.itF (show ¬ (12 ≤ i ∧ i < 16) by bdd_omega), VG.Proof.MlKem.X86_64.S4.itF (show ¬ (16 ≤ i ∧ i < 20) by bdd_omega)]
  have h2 : ∀ i < 12, (if 12 ≤ 12 + 8 + i ∧ 12 + 8 + i < 16 then (dword X0 (12 + 8 + i - 12)).getLsbD 31
      else if 16 ≤ 12 + 8 + i ∧ 12 + 8 + i < 20 then (dword X1 (12 + 8 + i - 16)).getLsbD 31 else false) = false :=
    fun i _ => by
      rw [VG.Proof.MlKem.X86_64.S4.itF (show ¬ (12 ≤ 12 + 8 + i ∧ 12 + 8 + i < 16) by bdd_omega),
        VG.Proof.MlKem.X86_64.S4.itF (show ¬ (16 ≤ 12 + 8 + i ∧ 12 + 8 + i < 20) by bdd_omega)]
  have h1 : ∀ k < 8, (if 12 ≤ 12 + k ∧ 12 + k < 16 then (dword X0 (12 + k - 12)).getLsbD 31
      else if 16 ≤ 12 + k ∧ 12 + k < 20 then (dword X1 (12 + k - 16)).getLsbD 31 else false) =
      if k < 4 then (dword X0 k).getLsbD 31 else (dword X1 (k - 4)).getLsbD 31 := fun k _ => by
    by_cases h : k < 4
    · rw [VG.Proof.MlKem.X86_64.S4.itT (show 12 ≤ 12 + k ∧ 12 + k < 16 by bdd_omega), VG.Proof.MlKem.X86_64.S4.itT h, show 12 + k - 12 = k by bdd_omega]
    · rw [VG.Proof.MlKem.X86_64.S4.itF (show ¬ (12 ≤ 12 + k ∧ 12 + k < 16) by bdd_omega), VG.Proof.MlKem.X86_64.S4.itT (show 16 ≤ 12 + k ∧ 12 + k < 20 by bdd_omega), VG.Proof.MlKem.X86_64.S4.itF h,
        show 12 + k - 16 = k - 4 by bdd_omega]
  rw [VG.Proof.MlKem.X86_64.S4.bsum_false h0, VG.Proof.MlKem.X86_64.S4.bsum_false h2, VG.Proof.MlKem.X86_64.S4.bsum_congr h1, Nat.zero_add, Nat.mul_zero, Nat.add_zero]

theorem dword_qV4 {j : Nat} (hj : j < 4) : dword VG.Proof.MlKem.X86_64.S4.qV4 j = 3329#32 := by
  rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl

/-- The sign of `c - q`: whether `c < q`. -/
theorem sign_sub_q {c : Nat} (hc : c < 4096) : (BitVec.ofNat 32 c - 3329#32).getLsbD 31 = decide (c < 3329) := by
  rw [BitVec.getLsbD, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  exact decide_eq_decide.mpr (by bdd_omega)

/-- Word `i` of `x ++ y`, for a word `y`. -/
theorem ext_last {w : Nat} (x : BitVec w) (y : BitVec 32) (i : Nat) :
    (x ++ y).extractLsb' (32 * i) 32 = if i = 0 then y else x.extractLsb' (32 * (i - 1)) 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases h : i = 0
  · rw [VG.Proof.MlKem.X86_64.S4.itT h, VG.Proof.MlKem.X86_64.S4.itT (show 32 * i + j < 32 by bdd_omega)]; exact congrArg _ (by bdd_omega)
  · rw [VG.Proof.MlKem.X86_64.S4.itF h, VG.Proof.MlKem.X86_64.S4.itF (show ¬ 32 * i + j < 32 by bdd_omega), BitVec.getLsbD_extractLsb', decide_eq_true hj,
      Bool.true_and]
    exact congrArg _ (by bdd_omega)

theorem ext_last0 {w : Nat} (x : BitVec w) (y : BitVec 32) : (x ++ y).extractLsb' 0 32 = y := by
  have h := VG.Proof.MlKem.X86_64.S4.ext_last x y 0
  rwa [Nat.mul_zero, VG.Proof.MlKem.X86_64.S4.itT rfl] at h

theorem ext_app8 (a : Nat → BitVec 32) {i : Nat} (hi : i < 8) :
    (a 7 ++ a 6 ++ a 5 ++ a 4 ++ a 3 ++ a 2 ++ a 1 ++ a 0).extractLsb' (32 * i) 32 = a i := by
  rcases (by bdd_omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [VG.Proof.MlKem.X86_64.S4.ext_last, VG.Proof.MlKem.X86_64.S4.ext_last0, Nat.reduceEqDiff, Nat.reduceSub, ite_false, Nat.mul_zero,
    BitVec.extractLsb'_eq_self]

theorem dw8_permDwords (idx x : BitVec 256) {i : Nat} (hi : i < 8) :
    (permDwords idx x).extractLsb' (32 * i) 32 = x.extractLsb' (32 * (idx.extractLsb' (32 * i) 3).toNat) 32 :=
  VG.Proof.MlKem.X86_64.S4.ext_app8 (fun k => x.extractLsb' (32 * (idx.extractLsb' (32 * k) 3).toNat) 32) hi

def nib0 : BitVec 128 := 0x0000000c000000080000000400000000#128
def nib1 : BitVec 128 := 0x0000001c000000180000001400000010#128

/-- The indices: `E` shifted right by `4 i` in doubleword `i`. -/
abbrev idxV (E : BitVec 32) : BitVec 256 :=
  VVarOp.eval .vpsrlvd (ofDwords E E E E) VG.Proof.MlKem.X86_64.S4.nib1 ++ VVarOp.eval .vpsrlvd (ofDwords E E E E) VG.Proof.MlKem.X86_64.S4.nib0

theorem ext_app2 (h l : BitVec 128) {i : Nat} (hi : i < 8) :
    (h ++ l).extractLsb' (32 * i) 32 = dword (if i < 4 then l else h) (i % 4) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', getLsbD_dword, hj, decide_true, Bool.true_and, BitVec.getLsbD_append]
  by_cases h4 : i < 4
  · rw [VG.Proof.MlKem.X86_64.S4.itT (show 32 * i + j < 128 by bdd_omega), VG.Proof.MlKem.X86_64.S4.itT h4]; exact congrArg _ (by bdd_omega)
  · rw [VG.Proof.MlKem.X86_64.S4.itF (show ¬ 32 * i + j < 128 by bdd_omega), VG.Proof.MlKem.X86_64.S4.itF h4]; exact congrArg _ (by bdd_omega)

theorem nib_dword {l j : Nat} (hl : l < 2) (hj : j < 4) :
    (dword (if l = 0 then VG.Proof.MlKem.X86_64.S4.nib0 else VG.Proof.MlKem.X86_64.S4.nib1) j).toNat = 4 * (4 * l + j) := by
  rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rcases cases4 hj with rfl | rfl | rfl | rfl <;> rfl

theorem idx_toNat (E : BitVec 32) {i : Nat} (hi : i < 8) :
    ((VG.Proof.MlKem.X86_64.S4.idxV E).extractLsb' (32 * i) 3).toNat = E.toNat / 16 ^ i % 8 := by
  rw [show (VG.Proof.MlKem.X86_64.S4.idxV E).extractLsb' (32 * i) 3 = ((VG.Proof.MlKem.X86_64.S4.idxV E).extractLsb' (32 * i) 32).extractLsb' 0 3 by
      rw [extract_extract _ _ _ _ _ (by bdd_omega), Nat.add_zero], VG.Proof.MlKem.X86_64.S4.ext_app2 _ _ hi]
  have hn : ∀ l < 2, ∀ j < 4, dword (VVarOp.eval .vpsrlvd (ofDwords E E E E) (if l = 0 then VG.Proof.MlKem.X86_64.S4.nib0 else VG.Proof.MlKem.X86_64.S4.nib1)) j =
      E >>> (4 * (4 * l + j)) := by
    intro l hl j hj
    have e := VG.Proof.MlKem.X86_64.S4.nib_dword hl hj
    rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp only [VVarOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, e,
      VG.Proof.MlKem.X86_64.S4.itT (show 4 * (4 * l + 0) < 32 by bdd_omega), VG.Proof.MlKem.X86_64.S4.itT (show 4 * (4 * l + 1) < 32 by bdd_omega),
      VG.Proof.MlKem.X86_64.S4.itT (show 4 * (4 * l + 2) < 32 by bdd_omega), VG.Proof.MlKem.X86_64.S4.itT (show 4 * (4 * l + 3) < 32 by bdd_omega)]
  have e : dword (if i < 4 then VVarOp.eval .vpsrlvd (ofDwords E E E E) VG.Proof.MlKem.X86_64.S4.nib0
      else VVarOp.eval .vpsrlvd (ofDwords E E E E) VG.Proof.MlKem.X86_64.S4.nib1) (i % 4) = E >>> (4 * i) := by
    by_cases h4 : i < 4
    · rw [VG.Proof.MlKem.X86_64.S4.itT h4]; have := hn 0 (by decide) (i % 4) (by bdd_omega); rw [VG.Proof.MlKem.X86_64.S4.itT rfl] at this
      rw [this]; congr 1; omega
    · rw [VG.Proof.MlKem.X86_64.S4.itF h4]; have := hn 1 (by decide) (i % 4) (by bdd_omega); rw [VG.Proof.MlKem.X86_64.S4.itF (by decide)] at this
      rw [this]; congr 1; omega
  rw [e, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow,
    Nat.pow_mul]

/-- `s'` is `s` with the two lanes of `d` set to `v 0` and `v 1` (flags aside). -/
structure LUpd (s s' : State) (d : XReg) (v : Nat → BitVec 128) : Prop where
  val : ∀ l < 2, s'.lane d l = v l
  other : ∀ r, r ≠ d → ∀ l < 2, s'.lane r l = s.lane r l
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem LUpd.setV256 (s : State) (d : XReg) (lo hi : BitVec 128) :
    VG.Proof.MlKem.X86_64.S4.LUpd s (s.setV .l256 d lo hi) d fun l => if l = 0 then lo else hi :=
  ⟨fun l _ => by rw [State.lane_setV256, ite_eq_left rfl], fun r hr l _ => by rw [State.lane_setV256, ite_eq_right hr],
    rfl, rfl, rfl, rfl⟩

theorem LUpd.setV128 (s : State) (d : XReg) (lo hi : BitVec 128) :
    VG.Proof.MlKem.X86_64.S4.LUpd s (s.setV .l128 d lo hi) d fun l => if l = 0 then lo else 0 :=
  ⟨fun l _ => by rw [State.lane_setV128, ite_eq_left rfl], fun r hr l _ => by rw [State.lane_setV128, ite_eq_right hr],
    rfl, rfl, rfl, rfl⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_vbin {op : VBinOp} {d a b : XReg}
    (k : ∀ s', VG.Proof.MlKem.X86_64.S4.LUpd s s' d (fun l => op.sse.eval (s.lane a l) (s.lane b l)) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vbin op .l256 d a b) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1)))
    rfl (k _ (by
    have h := LUpd.setV256 s d (op.sse.eval (s.lane a 0) (s.lane b 0)) (op.sse.eval (s.lane a 1) (s.lane b 1))
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr⟩))

theorem wp_vvar {op : VVarOp} {d a b : XReg}
    (k : ∀ s', VG.Proof.MlKem.X86_64.S4.LUpd s s' d (fun l => op.eval (s.lane a l) (s.lane b l)) → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vvar op .l256 d a b) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (op.eval (s.lane a 0) (s.lane b 0)) (op.eval (s.lane a 1) (s.lane b 1)))
    rfl (k _ (by
    have h := LUpd.setV256 s d (op.eval (s.lane a 0) (s.lane b 0)) (op.eval (s.lane a 1) (s.lane b 1))
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr⟩))

theorem wp_vpbcastd {d a : XReg}
    (k : ∀ s', VG.Proof.MlKem.X86_64.S4.LUpd s s' d (fun _ => let v := dword (s.lane a 0) 0; ofDwords v v v v) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpbroadcastd .l256 d a) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d (let v := dword (s.xmm a) 0; ofDwords v v v v)
      (let v := dword (s.xmm a) 0; ofDwords v v v v)) rfl (k _ (by
    have h := LUpd.setV256 s d (let v := dword (s.xmm a) 0; ofDwords v v v v)
      (let v := dword (s.xmm a) 0; ofDwords v v v v)
    exact ⟨fun l hl => by rw [h.val l hl]; split <;> rfl, h.other, h.gpr, h.mem, h.rd, h.wr⟩))

theorem wp_vpermd {d i a : XReg}
    (k : ∀ s', VG.Proof.MlKem.X86_64.S4.LUpd s s' d (fun l => (permDwords (s.ymm i) (s.ymm a)).extractLsb' (128 * l) 128) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.vpermd d i a) :: is)) s Q :=
  WP.cons (s' := s.setV .l256 d ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 0 128)
      ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 128 128)) rfl (k _ (by
    have h := LUpd.setV256 s d ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 0 128)
      ((permDwords (s.ymm i) (s.ymm a)).extractLsb' 128 128)
    exact ⟨fun l hl => by rw [h.val l hl]; rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
      h.other, h.gpr, h.mem, h.rd, h.wr⟩))

theorem wp_vbcast128 {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', VG.Proof.MlKem.X86_64.S4.LUpd s s' d (fun _ => s.mem.readW a 128) → WP isa (.block is) s' Q) :
    WP isa (.block (.vbroadcasti128 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d (s.mem.readW a 128) (s.mem.readW a 128))
    (by simp [exec, ha, State.load128, hin]) (k _ ?_)
  have h := LUpd.setV256 s d (s.mem.readW a 128) (s.mem.readW a 128)
  exact ⟨fun l hl => by rw [h.val l hl]; split <;> rfl, h.other, h.gpr, h.mem, h.rd, h.wr⟩

theorem wp_vld128 {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : ∀ s', VG.Proof.MlKem.X86_64.S4.LUpd s s' d (fun l => if l = 0 then s.mem.readW a 128 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquLoad .l128 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l128 d (s.mem.readW a 128) 0)
    (by simp [exec, ha, State.load128, hin]) (k _ (LUpd.setV128 s d _ _))

theorem wp_vld256 {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 32)
    (k : ∀ s', VG.Proof.MlKem.X86_64.S4.LUpd s s' d (fun l => (s.mem.readW a 256).extractLsb' (128 * l) 128) → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquLoad .l256 d m :: is)) s Q := by
  refine WP.cons (s' := s.setV .l256 d ((s.mem.readW a 256).extractLsb' 0 128)
    ((s.mem.readW a 256).extractLsb' 128 128)) (by simp [exec, ha, State.load256, hin]) (k _ ?_)
  have h := LUpd.setV256 s d ((s.mem.readW a 256).extractLsb' 0 128) ((s.mem.readW a 256).extractLsb' 128 128)
  exact ⟨fun l hl => by rw [h.val l hl]; rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl,
    h.other, h.gpr, h.mem, h.rd, h.wr⟩

theorem wp_vst256 {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 32)
    (k : ∀ s', s'.gpr = s.gpr → (∀ x l, s'.lane x l = s.lane x l) → s'.mem = s.mem.writeW a (s.ymm r) →
      s'.rd = s.rd → s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.vmovdquStore .l256 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.ymm r) }) ?_ (k _ rfl (fun _ _ => rfl) rfl rfl rfl)
  simp [exec, State.store256, ha, hout]

/-- `s'` is `s` with register `d` set to `v`, the vector registers as they were (flags aside). -/
structure GUpd (s s' : State) (d : Reg) (v : BitVec 64) : Prop extends Upd s s' d v where
  lane : ∀ x l, s'.lane x l = s.lane x l

theorem GUpd.setReg (s : State) (d : Reg) (v : BitVec 64) : VG.Proof.MlKem.X86_64.S4.GUpd s (s.setReg d v) d v :=
  ⟨Upd.setReg s d v, fun _ _ => rfl⟩

theorem GUpd.withFlags (s : State) (cf o zf sf : Option Bool) (d : Reg) (v : BitVec 64) :
    VG.Proof.MlKem.X86_64.S4.GUpd s ((s.setFlags cf o zf sf).setReg d v) d v :=
  ⟨Upd.withFlags s cf o zf sf d v, fun _ _ => rfl⟩

theorem wp_vpmovmskb {d : Reg} {r : XReg}
    (k : ∀ s', VG.Proof.MlKem.X86_64.S4.GUpd s s' d (byteMask (s.ymm r) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.vpmovmskb .l256 d r :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.setReg _ _ _))

theorem wp_shr32 {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 31)
    (k : ∀ s', VG.Proof.MlKem.X86_64.S4.GUpd s s' d ((((s.gpr d).setWidth 32) >>> n).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift32 .shr d n :: is)) s Q := by
  let a := (s.gpr d).setWidth 32
  refine WP.cons (s' := (s.setFlags (some (a.getLsbD (n - 1))) (if n = 1 then some a.msb else none)
    (some (a >>> n == 0)) (some (a >>> n).msb)).setReg d ((a >>> n).setWidth 64)) ?_
    (k _ (GUpd.withFlags _ _ _ _ _ _ _))
  simp only [exec, execShift32, h₁, h₂, and_self, ite_true, State.setReg32]
  rfl

theorem wp_add32m {d : Reg} {m : MemOp} {a' : Addr} (ha : s.ea m = a') (hin : InRegions (s.rd ++ s.wr) a' 4)
    (k : ∀ s', VG.Proof.MlKem.X86_64.S4.GUpd s s' d (((s.gpr d).setWidth 32 + s.mem.readW a' 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu32 .add d (.mem m) :: is)) s Q := by
  let a := (s.gpr d).setWidth 32
  let b := s.mem.readW a' 32
  refine WP.cons (s' := (arithFlags s (a + b) (2 ^ 32 ≤ a.toNat + b.toNat) (addOverflow a b (a + b))).setReg d
    ((a + b).setWidth 64)) ?_ (k _ (GUpd.withFlags _ _ _ _ _ _ _))
  simp [exec, execAlu32, readSrc32, State.load32, ha, hin, State.setReg32, a, b]

theorem wp_addi' {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.MlKem.X86_64.S4.GUpd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (GUpd.withFlags _ _ _ _ _ _ _))

end


/-! ## The candidates and their mask -/

abbrev sgn (l : Nat) : BitVec 128 := if l = 0 then VG.Proof.MlKem.X86_64.S4.sign0 else VG.Proof.MlKem.X86_64.S4.sign1
abbrev nib (l : Nat) : BitVec 128 := if l = 0 then VG.Proof.MlKem.X86_64.S4.nib0 else VG.Proof.MlKem.X86_64.S4.nib1

/-- The constants of the vector code in `ymm8` to `ymm13`. -/
structure VC (s : State) : Prop where
  c8 : ∀ l < 2, s.lane .xmm8 l = VG.Proof.MlKem.X86_64.S4.shuf l
  c9 : ∀ l < 2, s.lane .xmm9 l = VG.Proof.MlKem.X86_64.S4.shV
  c10 : ∀ l < 2, s.lane .xmm10 l = VG.Proof.MlKem.X86_64.S4.maskV
  c11 : ∀ l < 2, s.lane .xmm11 l = VG.Proof.MlKem.X86_64.S4.qV4
  c12 : ∀ l < 2, s.lane .xmm12 l = VG.Proof.MlKem.X86_64.S4.sgn l
  c13 : ∀ l < 2, s.lane .xmm13 l = VG.Proof.MlKem.X86_64.S4.nib l

theorem VC.lupd {s s' : State} (h : VG.Proof.MlKem.X86_64.S4.VC s) {d : XReg} {v : Nat → BitVec 128} (hu : VG.Proof.MlKem.X86_64.S4.LUpd s s' d v)
    (hd : d = .xmm0 ∨ d = .xmm1) : VG.Proof.MlKem.X86_64.S4.VC s' := by
  have e : ∀ r, r = XReg.xmm8 ∨ r = .xmm9 ∨ r = .xmm10 ∨ r = .xmm11 ∨ r = .xmm12 ∨ r = .xmm13 →
      ∀ l < 2, s'.lane r l = s.lane r l := fun r hr l hl => hu.other r (by
    rcases hd with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) l hl
  exact ⟨fun l hl => by rw [e _ (by simp) l hl, h.c8 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c9 l hl],
    fun l hl => by rw [e _ (by simp) l hl, h.c10 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c11 l hl],
    fun l hl => by rw [e _ (by simp) l hl, h.c12 l hl], fun l hl => by rw [e _ (by simp) l hl, h.c13 l hl]⟩

theorem VC.gupd {s s' : State} (h : VG.Proof.MlKem.X86_64.S4.VC s) {d : Reg} {v : BitVec 64} (hu : VG.Proof.MlKem.X86_64.S4.GUpd s s' d v) : VG.Proof.MlKem.X86_64.S4.VC s' :=
  ⟨fun l hl => by rw [hu.lane, h.c8 l hl], fun l hl => by rw [hu.lane, h.c9 l hl],
    fun l hl => by rw [hu.lane, h.c10 l hl], fun l hl => by rw [hu.lane, h.c11 l hl],
    fun l hl => by rw [hu.lane, h.c12 l hl], fun l hl => by rw [hu.lane, h.c13 l hl]⟩

theorem candN_lt (b : Nat → Nat) (hb : ∀ i, b i < 256) (k : Nat) : VG.Proof.MlKem.X86_64.S4.candN b k < 4096 := by
  unfold VG.Proof.MlKem.X86_64.S4.candN; have := hb (VG.Proof.MlKem.X86_64.S4.cb k); have := hb (VG.Proof.MlKem.X86_64.S4.cb k + 1); split <;> omega

/-- The mask of the candidates less than `q`. -/
abbrev maskN (b : Nat → Nat) : Nat := VG.Proof.MlKem.X86_64.S4.bsum (fun k => decide (VG.Proof.MlKem.X86_64.S4.candN b k < 3329)) 8

theorem vcand_ok {s : State} (hc : VG.Proof.MlKem.X86_64.S4.VC s) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16) :
    WP isa (.block vcand) s fun s' =>
      s'.gpr .rax = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.S4.maskN fun i => (VG.X86_64.byte (s.mem.readW (s.gpr .rsi) 128) i).toNat) ∧
      (∀ l < 2, s'.lane .xmm0 l = VG.Proof.MlKem.X86_64.S4.candV (s.mem.readW (s.gpr .rsi) 128) l) ∧ VG.Proof.MlKem.X86_64.S4.VC s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  open VG.Proof.MlKem.X86_64 (ea_at add_ofNat_zero) in
  refine VG.Proof.MlKem.X86_64.S4.wp_vbcast128 (a := s.gpr .rsi) (by rw [ea_at, add_ofNat_zero]) hin fun s1 u1 => ?_
  refine VG.Proof.MlKem.X86_64.S4.wp_vbin fun s2 u2 => VG.Proof.MlKem.X86_64.S4.wp_vvar fun s3 u3 => VG.Proof.MlKem.X86_64.S4.wp_vbin fun s4 u4 => VG.Proof.MlKem.X86_64.S4.wp_vbin fun s5 u5 =>
    VG.Proof.MlKem.X86_64.S4.wp_vbin fun s6 u6 => VG.Proof.MlKem.X86_64.S4.wp_vpmovmskb fun s7 u7 => VG.Proof.MlKem.X86_64.S4.wp_shr32 (by decide) (by decide) fun s8 u8 => WP.block_nil ?_
  have c1 := hc.lupd u1 (.inl rfl)
  have c2 := c1.lupd u2 (.inl rfl)
  have c3 := c2.lupd u3 (.inl rfl)
  have c4 := c3.lupd u4 (.inl rfl)
  have c5 := c4.lupd u5 (.inr rfl)
  have c6 := c5.lupd u6 (.inr rfl)
  have c7 := c6.gupd u7
  generalize s.mem.readW (s.gpr .rsi) 128 = L at u1 ⊢
  have h4 : ∀ l < 2, s4.lane .xmm0 l = VG.Proof.MlKem.X86_64.S4.candV L l := fun l hl => by
    rw [u4.val l hl, u3.val l hl, u2.val l hl, u1.val l hl, c1.c8 l hl, c2.c9 l hl, c3.c10 l hl]; rfl
  have h6 : ∀ l < 2, s6.lane .xmm1 l = XBinOp.eval .pshufb (XBinOp.eval .psubd (VG.Proof.MlKem.X86_64.S4.candV L l) VG.Proof.MlKem.X86_64.S4.qV4) (VG.Proof.MlKem.X86_64.S4.sgn l) :=
    fun l hl => by rw [u6.val l hl, u5.val l hl, h4 l hl, c4.c11 l hl, c5.c12 l hl]; rfl
  have h0 : ∀ l < 2, s8.lane .xmm0 l = VG.Proof.MlKem.X86_64.S4.candV L l := fun l hl => by
    rw [u8.lane, u7.lane, u6.other _ (by decide) l hl, u5.other _ (by decide) l hl, h4 l hl]
  have hb : ∀ i, (VG.X86_64.byte L i).toNat < 256 := fun i => (VG.X86_64.byte L i).isLt
  have hm : byteMask (s6.ymm .xmm1) 32 = BitVec.ofNat 64 (4096 * VG.Proof.MlKem.X86_64.S4.maskN fun i => (VG.X86_64.byte L i).toNat) := by
    rw [State.ymm_eq, h6 1 (by decide), h6 0 (by decide), VG.Proof.MlKem.X86_64.S4.byteMask_eq _ (by decide)]
    simp only [VG.Proof.MlKem.X86_64.S4.sgn, show (1 : Nat) ≠ 0 by decide, ite_false, ite_true]
    rw [VG.Proof.MlKem.X86_64.S4.mask_bsum, VG.Proof.MlKem.X86_64.S4.maskN]
    congr 2
    apply VG.Proof.MlKem.X86_64.S4.bsum_congr
    intro k hk
    by_cases h : k < 4
    · rw [VG.Proof.MlKem.X86_64.S4.itT h, dword_psubd _ _ h, VG.Proof.MlKem.X86_64.S4.dword_qV4 h, VG.Proof.MlKem.X86_64.S4.cand_dword _ (show 0 < 2 by decide) h,
        VG.Proof.MlKem.X86_64.S4.sign_sub_q (VG.Proof.MlKem.X86_64.S4.candN_lt _ hb _), Nat.mul_zero, Nat.zero_add]
    · rw [VG.Proof.MlKem.X86_64.S4.itF h, dword_psubd _ _ (by bdd_omega), VG.Proof.MlKem.X86_64.S4.dword_qV4 (by bdd_omega), VG.Proof.MlKem.X86_64.S4.cand_dword _ (show 1 < 2 by decide) (by bdd_omega),
        VG.Proof.MlKem.X86_64.S4.sign_sub_q (VG.Proof.MlKem.X86_64.S4.candN_lt _ hb _), show 4 * 1 + (k - 4) = k by bdd_omega]
  have hM : VG.Proof.MlKem.X86_64.S4.maskN (fun i => (VG.X86_64.byte L i).toNat) < 2 ^ 8 := VG.Proof.MlKem.X86_64.S4.bsum_lt _ 8
  refine ⟨?_, h0, c7.gupd u8, by rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem],
    by rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr], fun r hr => ?_⟩
  · rw [u8.gpr, u7.gpr, hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · rw [u8.other r hr, u7.other r hr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]

/-! ## The compaction -/

theorem ymm_halves (x : BitVec 256) : x.extractLsb' 128 128 ++ x.extractLsb' 0 128 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 128
  · rw [VG.Proof.MlKem.X86_64.S4.itT h]; simp [h]
  · rw [VG.Proof.MlKem.X86_64.S4.itF h]; simp only [show j - 128 < 128 by bdd_omega, decide_true, Bool.true_and]; exact congrArg _ (by bdd_omega)

theorem ea_tabE {s : State} {M : Nat} (h : s.gpr .rax = BitVec.ofNat 64 M) :
    s.ea tabE = s.gpr .rbx + BitVec.ofNat 64 (8 * M) := by
  simp only [State.ea, tabE, h, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem ea_tabE4 {s : State} {M : Nat} (h : s.gpr .rax = BitVec.ofNat 64 M) :
    s.ea { tabE with disp := 4 } = s.gpr .rbx + BitVec.ofNat 64 (8 * M + 4) := by
  simp only [State.ea, tabE, h]
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, show BitVec.ofInt 64 4 = 4#64 from rfl]
  omega

theorem ea_aV (s : State) : s.ea aV = s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat) := by
  simp only [State.ea, aV, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- The doublewords stored: candidate `E / 16ⁱ mod 8` in doubleword `i`. -/
theorem vput_ok {s : State} (hc : VG.Proof.MlKem.X86_64.S4.VC s) {L : BitVec 128} (h0 : ∀ l < 2, s.lane .xmm0 l = VG.Proof.MlKem.X86_64.S4.candV L l)
    {M : Nat} (hrax : s.gpr .rax = BitVec.ofNat 64 M)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (8 * M)) 16)
    (hin4 : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (8 * M + 4)) 4)
    (hout : InRegions s.wr (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) 32)
    (hd : ∀ V : BitVec 256, (s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) V).readW
      (s.gpr .rbx + BitVec.ofNat 64 (8 * M + 4)) 32 = s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * M + 4)) 32) :
    WP isa (.block vput) s fun s' =>
      (∃ V : BitVec 256, s'.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) V ∧
        ∀ i < 8, V.extractLsb' (32 * i) 32 = BitVec.ofNat 32 (VG.Proof.MlKem.X86_64.S4.candN (fun i => (VG.X86_64.byte L i).toNat)
          ((dword (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * M)) 128) 0).toNat / 16 ^ i % 8))) ∧
      s'.gpr .rdi = (((s.gpr .rdi).setWidth 32 +
        s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * M + 4)) 32).setWidth 64) ∧
      s'.gpr .rsi = s.gpr .rsi + 12 ∧ VG.Proof.MlKem.X86_64.S4.VC s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ r, r ≠ .rdi → r ≠ .rsi → s'.gpr r = s.gpr r := by
  refine VG.Proof.MlKem.X86_64.S4.wp_vld128 (VG.Proof.MlKem.X86_64.S4.ea_tabE hrax) hin fun s1 u1 => VG.Proof.MlKem.X86_64.S4.wp_vpbcastd fun s2 u2 => VG.Proof.MlKem.X86_64.S4.wp_vvar fun s3 u3 => VG.Proof.MlKem.X86_64.S4.wp_vpermd fun s4 u4 => ?_
  have g4 : s4.gpr = s.gpr := by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  refine VG.Proof.MlKem.X86_64.S4.wp_vst256 (a := s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) (by rw [VG.Proof.MlKem.X86_64.S4.ea_aV, g4])
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact hout) fun s5 g5 l5 m5 r5 w5 => ?_
  refine VG.Proof.MlKem.X86_64.S4.wp_add32m (a' := s.gpr .rbx + BitVec.ofNat 64 (8 * M + 4)) (by rw [← VG.Proof.MlKem.X86_64.S4.ea_tabE4 hrax]; simp only [State.ea, g5, g4])
    (by rw [r5, w5, u4.rd, u3.rd, u2.rd, u1.rd, u4.wr, u3.wr, u2.wr, u1.wr]; exact hin4) fun s6 u6 =>
    VG.Proof.MlKem.X86_64.S4.wp_addi' fun s7 u7 => WP.block_nil ?_
  have c4 : VG.Proof.MlKem.X86_64.S4.VC s4 := ((hc.lupd u1 (.inr rfl)).lupd u2 (.inr rfl)).lupd u3 (.inr rfl) |>.lupd u4 (.inl rfl)
  have c5 : VG.Proof.MlKem.X86_64.S4.VC s5 := ⟨fun l hl => by rw [l5, c4.c8 l hl], fun l hl => by rw [l5, c4.c9 l hl],
    fun l hl => by rw [l5, c4.c10 l hl], fun l hl => by rw [l5, c4.c11 l hl], fun l hl => by rw [l5, c4.c12 l hl],
    fun l hl => by rw [l5, c4.c13 l hl]⟩
  have hm5 : s5.mem = s.mem.writeW (s.gpr .rbp + BitVec.ofNat 64 (4 * (s.gpr .rdi).toNat)) (s4.ymm .xmm0) := by
    rw [m5, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨⟨s4.ymm .xmm0, by rw [u7.mem, u6.mem, hm5], fun i hi => ?_⟩, ?_, ?_, (c5.gupd u6).gupd u7,
    by rw [u7.rd, u6.rd, r5, u4.rd, u3.rd, u2.rd, u1.rd], by rw [u7.wr, u6.wr, w5, u4.wr, u3.wr, u2.wr, u1.wr],
    fun r h1 h2 => by rw [u7.other r h2, u6.other r h1, g5, g4]⟩
  · -- the stored doublewords
    have hy4 : s4.ymm .xmm0 = permDwords (s3.ymm .xmm1) (s3.ymm .xmm0) := by
      rw [State.ymm_eq, u4.val 1 (by decide), u4.val 0 (by decide), Nat.mul_one, Nat.mul_zero, VG.Proof.MlKem.X86_64.S4.ymm_halves]
    have hx3 : s3.ymm .xmm0 = VG.Proof.MlKem.X86_64.S4.candV L 1 ++ VG.Proof.MlKem.X86_64.S4.candV L 0 := by
      rw [State.ymm_eq, u3.other .xmm0 (by decide) 1 (by decide), u3.other .xmm0 (by decide) 0 (by decide),
        u2.other .xmm0 (by decide) 1 (by decide), u2.other .xmm0 (by decide) 0 (by decide),
        u1.other .xmm0 (by decide) 1 (by decide), u1.other .xmm0 (by decide) 0 (by decide), h0 1 (by decide),
        h0 0 (by decide)]
    have hi3 : s3.ymm .xmm1 = VG.Proof.MlKem.X86_64.S4.idxV (dword (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * M)) 128) 0) := by
      rw [State.ymm_eq, u3.val 1 (by decide), u3.val 0 (by decide), u2.val 1 (by decide), u2.val 0 (by decide),
        u2.other .xmm13 (by decide) 1 (by decide), u2.other .xmm13 (by decide) 0 (by decide),
        u1.other .xmm13 (by decide) 1 (by decide), u1.other .xmm13 (by decide) 0 (by decide),
        u1.val 0 (by decide), hc.c13 1 (by decide), hc.c13 0 (by decide)]
      rfl
    rw [hy4, VG.Proof.MlKem.X86_64.S4.dw8_permDwords _ _ hi, hi3, VG.Proof.MlKem.X86_64.S4.idx_toNat _ hi, hx3]
    have hp : (dword (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * M)) 128) 0).toNat / 16 ^ i % 8 < 8 :=
      Nat.mod_lt _ (by decide)
    rw [VG.Proof.MlKem.X86_64.S4.ext_app2 _ _ hp]
    by_cases h4 : (dword (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * M)) 128) 0).toNat / 16 ^ i % 8 < 4
    · rw [VG.Proof.MlKem.X86_64.S4.itT h4, VG.Proof.MlKem.X86_64.S4.cand_dword _ (show 0 < 2 by decide) (Nat.mod_lt _ (by decide))]
      congr 2; omega
    · rw [VG.Proof.MlKem.X86_64.S4.itF h4, VG.Proof.MlKem.X86_64.S4.cand_dword _ (show 1 < 2 by decide) (Nat.mod_lt _ (by decide))]
      congr 2; omega
  · rw [u7.other _ (by decide), u6.gpr, g5, g4, hm5, hd]
  · rw [u7.gpr, u6.other _ (by decide), g5, g4]; rfl

theorem bsum8_bit (f : Nat → Bool) {k : Nat} (hk : k < 8) : VG.Proof.MlKem.X86_64.S4.bsum f 8 / 2 ^ k % 2 = (f k).toNat := by
  have e : VG.Proof.MlKem.X86_64.S4.bsum f 8 = VG.Proof.MlKem.X86_64.S4.bsum f k + 2 ^ k * VG.Proof.MlKem.X86_64.S4.bsum (fun i => f (k + i)) (1 + (7 - k)) := by
    rw [← VG.Proof.MlKem.X86_64.S4.bsum_add, show k + (1 + (7 - k)) = 8 by bdd_omega]
  rw [e, VG.Proof.MlKem.X86_64.S4.bsum_add _ 1, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt (VG.Proof.MlKem.X86_64.S4.bsum_lt f k),
    Nat.zero_add, Nat.pow_one, Nat.add_mul_mod_self_left]
  simp only [VG.Proof.MlKem.X86_64.S4.bsum, Nat.add_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  exact Nat.mod_eq_of_lt (Bool.toNat_lt _)

theorem setBits_bsum (f : Nat → Bool) : setBits (VG.Proof.MlKem.X86_64.S4.bsum f 8) = (List.range 8).filter f := by
  unfold setBits
  apply List.filter_congr
  intro k hk
  rw [VG.Proof.MlKem.X86_64.S4.bsum8_bit f (List.mem_range.mp hk)]
  cases f k <;> rfl

end VG.Proof.MlKem.X86_64.S4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.S4Loop`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, sampling

`parse k` loads the constants of the vector code from the table (`setup_ok`),
and runs 42 groups of four iterations of `SampleNTT`'s loop on the 504 bytes
of XOF output of seed `k`, to polynomial `k` (`vgrp_ok`): with the vector code
while there are fewer than 249 coefficients (`vec_ok`), and otherwise four
iterations of `vg_mlkem_sample_ntt`'s loop (`sca_ok`). Then, if they sample
fewer than 256 coefficients, it calls `vg_mlkem_sample_ntt` on the seed
(`fallback_ok`). Either way, polynomial `k` is then the seed's `SampleNTT`, if
it succeeds, and `r14` records whether the first `k + 1` do (`parse_ok`).
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Proof.MlKem (xofByte sampleAfter)

/-! ## The constants -/

/-- 16 bytes as two quadwords. -/
theorem readW128_q (m : Mem) (a : Addr) : m.readW a 128 = m.readW (a + BitVec.ofNat 64 8) 64 ++ m.readW a 64 := by
  have e1 := readW_extract m a (w := 128) (k := 8) (n := 8) (by bdd_omega)
  have e0 := readW_extract m a (w := 128) (k := 0) (n := 8) (by bdd_omega)
  rw [add_ofNat_zero] at e0
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_append]
  by_cases h : j < 64
  · rw [VG.Proof.MlKem.X86_64.S4.itT h, ← e0]; simp only [BitVec.getLsbD_extractLsb', h, decide_true, Bool.true_and]
    exact congrArg _ (by bdd_omega)
  · rw [VG.Proof.MlKem.X86_64.S4.itF h, ← e1]; simp only [BitVec.getLsbD_extractLsb', show j - 64 < 64 by bdd_omega, decide_true, Bool.true_and]
    exact congrArg _ (by bdd_omega)

/-- Lane `l` of constant `c`, from the table. -/
theorem cst_lane {σ : State} {m : Mem} (h : VG.Proof.MlKem.X86_64.S4.TabOK σ m) {c l : Nat} (hc : c < 6) (hl : l < 2) :
    (m.readW (VG.Proof.MlKem.X86_64.S4.at' σ (oCst + 32 * c)) 256).extractLsb' (128 * l) 128 =
      tabQ (256 + 4 * c + 2 * l + 1) ++ tabQ (256 + 4 * c + 2 * l) := by
  have a1 : VG.Proof.MlKem.X86_64.S4.at' σ (oCst + 32 * c) + BitVec.ofNat 64 (16 * l) + BitVec.ofNat 64 8 =
      VG.Proof.MlKem.X86_64.S4.at' σ (8 * (256 + 4 * c + 2 * l + 1)) := by
    rw [VG.Proof.MlKem.X86_64.S4.at', Offset.add_add, Offset.add_add]; exact congrArg (fun x => VG.Proof.MlKem.X86_64.S4.scr σ + BitVec.ofNat 64 x) (by simp only [oCst]; omega)
  have a0 : VG.Proof.MlKem.X86_64.S4.at' σ (oCst + 32 * c) + BitVec.ofNat 64 (16 * l) = VG.Proof.MlKem.X86_64.S4.at' σ (8 * (256 + 4 * c + 2 * l)) := by
    rw [VG.Proof.MlKem.X86_64.S4.at', Offset.add_add]; exact congrArg (fun x => VG.Proof.MlKem.X86_64.S4.scr σ + BitVec.ofNat 64 x) (by simp only [oCst]; omega)
  rw [show 128 * l = 8 * (16 * l) by bdd_omega, readW_extract _ _ (n := 16) (by bdd_omega), VG.Proof.MlKem.X86_64.S4.readW128_q, a1, a0,
    h _ (by bdd_omega), h _ (by bdd_omega)]

theorem cst_vals : (tabQ 257 ++ tabQ 256 = VG.Proof.MlKem.X86_64.S4.shuf 0 ∧ tabQ 259 ++ tabQ 258 = VG.Proof.MlKem.X86_64.S4.shuf 1) ∧
    (tabQ 261 ++ tabQ 260 = VG.Proof.MlKem.X86_64.S4.shV ∧ tabQ 263 ++ tabQ 262 = VG.Proof.MlKem.X86_64.S4.shV) ∧
    (tabQ 265 ++ tabQ 264 = VG.Proof.MlKem.X86_64.S4.maskV ∧ tabQ 267 ++ tabQ 266 = VG.Proof.MlKem.X86_64.S4.maskV) ∧
    (tabQ 269 ++ tabQ 268 = VG.Proof.MlKem.X86_64.S4.qV4 ∧ tabQ 271 ++ tabQ 270 = VG.Proof.MlKem.X86_64.S4.qV4) ∧
    (tabQ 273 ++ tabQ 272 = VG.Proof.MlKem.X86_64.S4.sgn 0 ∧ tabQ 275 ++ tabQ 274 = VG.Proof.MlKem.X86_64.S4.sgn 1) ∧
    (tabQ 277 ++ tabQ 276 = VG.Proof.MlKem.X86_64.S4.nib 0 ∧ tabQ 279 ++ tabQ 278 = VG.Proof.MlKem.X86_64.S4.nib 1) := by
  decide

/-- The table: the number of set bits of `m` in the high doubleword of
entry `m`, and their positions in the nibbles of the low one. -/
theorem tab_facts : ∀ m < 256, tabEntry m < 2 ^ 64 ∧ tabEntry m / 2 ^ 32 = (setBits m).length ∧
    ∀ i < (setBits m).length, tabEntry m % 2 ^ 32 / 16 ^ i % 8 = (setBits m).getD i 0 := by
  decide +kernel

theorem setBits_length (m : Nat) : (setBits m).length ≤ 8 := by
  unfold setBits; exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-! ## The loop -/

/-- The coefficients only grow. -/
theorem Lt_mono (σ : State) (K t : Nat) : ∀ u, (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length ≤ (VG.Proof.MlKem.X86_64.S4.Lt σ K (t + u)).length
  | 0 => Nat.le_refl _
  | u + 1 => Nat.le_trans (VG.Proof.MlKem.X86_64.S4.Lt_mono σ K t u) (by
      simp only [VG.Proof.MlKem.X86_64.S4.Lt]
      rw [← Nat.add_assoc, sampleAfter_succ]
      exact (Proof.MlKem.sampleStepCap_prefix _ _ _ _).length_le)

/-- At iteration `t` of the loop of `parse K`: the constants are in place
while there are fewer than 249 coefficients. -/
structure LV (σ : State) (K t : Nat) (s : State) : Prop where
  lat : VG.Proof.MlKem.X86_64.S4.LAt σ K t s
  vc : (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length < 249 → VG.Proof.MlKem.X86_64.S4.VC s

theorem LAt.same {σ : State} {K t : Nat} {s s' : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K t s) (g : s'.gpr = s.gpr) (m : s'.mem = s.mem)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) : VG.Proof.MlKem.X86_64.S4.LAt σ K t s' :=
  ⟨h.pinv.keep m (rs := []) ⟨fun r _ => by rw [g], rd, wr⟩ (by simp), by rw [g]; exact h.rsi,
    by rw [g]; exact h.rdi, by rw [g]; exact h.rbp, by rw [m]; exact h.stored⟩

theorem LAt.same' {σ : State} {K t : Nat} {s s' : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K t s) (m : s'.mem = s.mem) {rs : List Reg}
    (k : Keep rs s s') (hrs : ∀ r ∈ [Reg.rbx, .r12, .r13, .rsp, .r15, .r14], r ∉ rs := by decide)
    (hrs' : Reg.rsi ∉ rs ∧ Reg.rdi ∉ rs ∧ Reg.rbp ∉ rs := by decide) : VG.Proof.MlKem.X86_64.S4.LAt σ K t s' :=
  ⟨h.pinv.keep m k hrs, by rw [k.gpr hrs'.1]; exact h.rsi, by rw [k.gpr hrs'.2.1]; exact h.rdi,
    by rw [k.gpr hrs'.2.2]; exact h.rbp, by rw [m]; exact h.stored⟩

theorem setup_eq (K : Nat) : setup K = [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))),
    .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * K))),
    .mov32 .r10 (.imm 21)] := rfl

theorem cstLoad_eq : cstLoad = [.vmovdquLoad .l256 .xmm8 (at_ .rbx (oCst + 32 * 0)),
    .vmovdquLoad .l256 .xmm9 (at_ .rbx (oCst + 32 * 1)), .vmovdquLoad .l256 .xmm10 (at_ .rbx (oCst + 32 * 2)),
    .vmovdquLoad .l256 .xmm11 (at_ .rbx (oCst + 32 * 3)), .vmovdquLoad .l256 .xmm12 (at_ .rbx (oCst + 32 * 4)),
    .vmovdquLoad .l256 .xmm13 (at_ .rbx (oCst + 32 * 5))] := rfl

section
variable {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ)
include hp

/-- The setup of the loop of `parse K`. -/
theorem setup_ok {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlKem.X86_64.S4.PInv σ K s) :
    WP isa (.block (setup K ++ cstLoad)) s fun s' => VG.Proof.MlKem.X86_64.S4.LV σ K 0 s' ∧ s'.gpr .r10 = BitVec.ofNat 64 21 := by
  rw [WP.block_append_iff, VG.Proof.MlKem.X86_64.S4.setup_eq]
  refine WP.mono (WP.keep [.rsi, .rdi, .rbp, .r10] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K) ∧ s'.gpr .rdi = 0 ∧ s'.gpr .rbp = poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K ∧
      s'.gpr .r10 = BitVec.ofNat 64 21)
    (by xrun [h.env.rbx, h.env.r13, sx_ofNat (show oBuf + 504 * K < 2 ^ 31 by simp only [oBuf]; omega),
      sx_ofNat (show 1024 * K < 2 ^ 31 by bdd_omega)]; rfl) rfl) fun s₁ ⟨⟨hm, hsi, hdi, hbp, h10⟩, k₁⟩ => ?_
  have l₁ : VG.Proof.MlKem.X86_64.S4.LAt σ K 0 s₁ := ⟨h.keep hm k₁ (by decide), by rw [hsi, Nat.mul_zero, add_ofNat_zero], by rw [hdi]; rfl,
    hbp, fun k hk => absurd hk (by simp [sampleAfter])⟩
  have hbx : s₁.gpr .rbx = VG.Proof.MlKem.X86_64.S4.scr σ := l₁.pinv.env.rbx
  have hin : ∀ c < 6, InRegions (s₁.rd ++ s₁.wr) (VG.Proof.MlKem.X86_64.S4.at' σ (oCst + 32 * c)) 32 := fun c hc =>
    VG.Proof.MlKem.X86_64.S4.in_scr' hp l₁.pinv.env.rd l₁.pinv.env.wr (by simp only [oCst]; omega)
  have tab := l₁.pinv.buf.2
  rw [VG.Proof.MlKem.X86_64.S4.cstLoad_eq]
  refine VG.Proof.MlKem.X86_64.S4.wp_vld256 (by rw [ea_at, hbx]) (hin 0 (by decide)) fun s₂ u₂ =>
    VG.Proof.MlKem.X86_64.S4.wp_vld256 (by rw [ea_at, u₂.gpr, hbx]) (by rw [u₂.rd, u₂.wr]; exact hin 1 (by decide)) fun s₃ u₃ =>
    VG.Proof.MlKem.X86_64.S4.wp_vld256 (by rw [ea_at, u₃.gpr, u₂.gpr, hbx]) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin 2 (by decide))
      fun s₄ u₄ =>
    VG.Proof.MlKem.X86_64.S4.wp_vld256 (by rw [ea_at, u₄.gpr, u₃.gpr, u₂.gpr, hbx])
      (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin 3 (by decide)) fun s₅ u₅ =>
    VG.Proof.MlKem.X86_64.S4.wp_vld256 (by rw [ea_at, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, hbx])
      (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin 4 (by decide)) fun s₆ u₆ =>
    VG.Proof.MlKem.X86_64.S4.wp_vld256 (by rw [ea_at, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, hbx])
      (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact hin 5 (by decide))
      fun s₇ u₇ => WP.block_nil ?_
  have g : s₇.gpr = s₁.gpr := by rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr]
  have m : s₇.mem = s₁.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain ⟨⟨c0, c1⟩, ⟨c2, c3⟩, ⟨c4, c5⟩, ⟨c6, c7⟩, ⟨c8, c9⟩, ⟨c10, c11⟩⟩ := VG.Proof.MlKem.X86_64.S4.cst_vals
  have cl : ∀ c < 6, ∀ l < 2, (s₁.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (oCst + 32 * c)) 256).extractLsb' (128 * l) 128 =
      tabQ (256 + 4 * c + 2 * l + 1) ++ tabQ (256 + 4 * c + 2 * l) := fun c hc l hl => VG.Proof.MlKem.X86_64.S4.cst_lane tab hc hl
  refine ⟨⟨l₁.same g m (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd]) (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr]),
    fun _ => ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩⟩,
    by rw [g]; exact h10⟩
  · rw [u₇.other _ (by decide) l hl, u₆.other _ (by decide) l hl, u₅.other _ (by decide) l hl,
      u₄.other _ (by decide) l hl, u₃.other _ (by decide) l hl, u₂.val l hl, cl 0 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c0, c1]
  · rw [u₇.other _ (by decide) l hl, u₆.other _ (by decide) l hl, u₅.other _ (by decide) l hl,
      u₄.other _ (by decide) l hl, u₃.val l hl, u₂.mem, cl 1 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c2, c3]
  · rw [u₇.other _ (by decide) l hl, u₆.other _ (by decide) l hl, u₅.other _ (by decide) l hl,
      u₄.val l hl, u₃.mem, u₂.mem, cl 2 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c4, c5]
  · rw [u₇.other _ (by decide) l hl, u₆.other _ (by decide) l hl, u₅.val l hl, u₄.mem, u₃.mem, u₂.mem,
      cl 3 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c6, c7]
  · rw [u₇.other _ (by decide) l hl, u₆.val l hl, u₅.mem, u₄.mem, u₃.mem, u₂.mem, cl 4 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c8, c9]
  · rw [u₇.val l hl, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, cl 5 (by decide) l hl]
    rcases (by bdd_omega : l = 0 ∨ l = 1) with rfl | rfl; exacts [c10, c11]

/-- Four iterations of `vg_mlkem_sample_ntt`'s loop. -/
theorem sca_ok {K t : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) {s : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K t s) :
    WP isa (.seq (.block [.mov32 .rcx (.imm 4)]) (.loop snBody .ne)) s fun s' =>
      VG.Proof.MlKem.X86_64.S4.LAt σ K (t + 4) s' ∧ s'.gpr .r10 = s.gpr .r10 :=
  wp_counted (N := 4) rfl (by decide) (fun u s' => VG.Proof.MlKem.X86_64.S4.LAt σ K (t + u) s' ∧ s'.gpr .r10 = s.gpr .r10)
    (fun s' hm k => ⟨h.same' hm k, k.gpr (by decide)⟩)
    fun u hu s' ⟨hl, h10⟩ => WP.mono (WP.gpr (VG.Proof.MlKem.X86_64.S4.lat_step hp hK (by bdd_omega) hl) (r := .r10) (by decide))
      fun s'' ⟨⟨hl', hc, hz⟩, h10'⟩ => ⟨⟨by rw [← Nat.add_assoc]; exact hl', h10'.trans h10⟩, hc, hz⟩

omit hp in
/-- The 12 bytes of the iterations `t` to `t + 3`. -/
theorem vbytes {K t : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) {s : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K t s) {i : Nat} (hi : i < 12) :
    (byte (s.mem.readW (s.gpr .rsi) 128) i).toNat = (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K) (3 * t + i)).toNat := by
  rw [byte, byte_readW _ _ (by bdd_omega), VG.Proof.MlKem.X86_64.S4.out_byte hK h (by bdd_omega)]

omit hp in
theorem vcand_eq {K t : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) {s : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K t s) {k : Nat} (hk : k < 8) :
    VG.Proof.MlKem.X86_64.S4.candN (fun i => (byte (s.mem.readW (s.gpr .rsi) 128) i).toNat) k = VG.Proof.MlKem.cand4 (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) (3 * t) k := by
  unfold VG.Proof.MlKem.X86_64.S4.candN VG.Proof.MlKem.cand4 VG.Proof.MlKem.X86_64.S4.cb
  dsimp only
  rw [VG.Proof.MlKem.X86_64.S4.vbytes hK ht h (i := 3 * (k / 2) + k % 2) (by bdd_omega), VG.Proof.MlKem.X86_64.S4.vbytes hK ht h (i := 3 * (k / 2) + k % 2 + 1) (by bdd_omega)]
  split
  · rw [show 3 * t + (3 * (k / 2) + k % 2) = 3 * t + 3 * (k / 2) by bdd_omega,
      show 3 * t + (3 * (k / 2) + k % 2 + 1) = 3 * t + 3 * (k / 2) + 1 by bdd_omega]
  · rw [show 3 * t + (3 * (k / 2) + k % 2) = 3 * t + 3 * (k / 2) + 1 by bdd_omega,
      show 3 * t + (3 * (k / 2) + k % 2 + 1) = 3 * t + 3 * (k / 2) + 2 by bdd_omega]

/-- After the candidates and their mask, from iteration `t` with fewer than 249 coefficients. -/
structure VI (σ : State) (K t : Nat) (s : State) : Prop where
  lat : VG.Proof.MlKem.X86_64.S4.LAt σ K t s
  len : (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length < 249
  vc : VG.Proof.MlKem.X86_64.S4.VC s
  rax : s.gpr .rax = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.S4.bsum (fun k => decide (VG.Proof.MlKem.cand4 (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) (3 * t) k < 3329)) 8)
  cand : ∀ l < 2, s.lane .xmm0 l = VG.Proof.MlKem.X86_64.S4.candV (s.mem.readW (s.gpr .rsi) 128) l

/-- The candidates of the four iterations and their mask. -/
theorem vec1_ok {K t : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) {s : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K t s) (hv : VG.Proof.MlKem.X86_64.S4.VC s)
    (hl : (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length < 249) :
    WP isa (.block vcand) s fun s' => VG.Proof.MlKem.X86_64.S4.VI σ K t s' ∧ s'.gpr .r10 = s.gpr .r10 := by
  have hrsi : s.gpr .rsi = VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K + 3 * t) := by rw [h.rsi, VG.Proof.MlKem.X86_64.S4.at', VG.Proof.MlKem.X86_64.S4.at', Offset.add_add]
  have hin16 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 16 := by
    rw [hrsi]; exact VG.Proof.MlKem.X86_64.S4.in_scr' hp h.pinv.env.rd h.pinv.env.wr (by simp only [oBuf]; omega)
  refine WP.mono (VG.Proof.MlKem.X86_64.S4.vcand_ok hv hin16) fun s₁ ⟨hax, h0, c₁, m₁, rd₁, wr₁, g₁⟩ => ?_
  have hM : VG.Proof.MlKem.X86_64.S4.maskN (fun i => (byte (s.mem.readW (s.gpr .rsi) 128) i).toNat) =
      VG.Proof.MlKem.X86_64.S4.bsum (fun k => decide (VG.Proof.MlKem.cand4 (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) (3 * t) k < 3329)) 8 :=
    VG.Proof.MlKem.X86_64.S4.bsum_congr fun k hk => by rw [VG.Proof.MlKem.X86_64.S4.vcand_eq hK ht h hk]
  refine ⟨⟨h.same' m₁ (rs := [.rax]) ⟨fun r hr => g₁ r (by simpa using hr), rd₁, wr₁⟩, hl, c₁, by rw [hax, hM],
    fun l hl' => by rw [h0 l hl', m₁, g₁ _ (by decide)]⟩, g₁ _ (by decide)⟩

/-- The candidates less than `q` to the polynomial, and `j` counting them. -/
theorem vec2_ok {K t : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) {s₁ : State} (hi : VG.Proof.MlKem.X86_64.S4.VI σ K t s₁) :
    WP isa (.block vput) s₁ fun s' => VG.Proof.MlKem.X86_64.S4.LAt σ K (t + 4) s' ∧ VG.Proof.MlKem.X86_64.S4.VC s' ∧ s'.gpr .r10 = s₁.gpr .r10 := by
  have h := hi.lat
  have c₁ := hi.vc
  have hl := hi.len
  have h0 := hi.cand
  have hax := hi.rax
  have hcand : ∀ k < 8, _ := fun k (hk : k < 8) => VG.Proof.MlKem.X86_64.S4.vcand_eq hK ht h hk
  generalize hMd : VG.Proof.MlKem.X86_64.S4.bsum (fun k => decide (VG.Proof.MlKem.cand4 (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) (3 * t) k < 3329)) 8 = M at hax
  have hM : M = VG.Proof.MlKem.X86_64.S4.bsum (fun k => decide (VG.Proof.MlKem.cand4 (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) (3 * t) k < 3329)) 8 := hMd.symm
  have hM8 : M < 256 := by rw [hM]; exact VG.Proof.MlKem.X86_64.S4.bsum_lt _ 8
  have hsb : setBits M = (List.range 8).filter fun k => decide (VG.Proof.MlKem.cand4 (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) (3 * t) k < 3329) := by
    rw [hM]; exact VG.Proof.MlKem.X86_64.S4.setBits_bsum _
  obtain ⟨hE, hcnt, hnib⟩ := VG.Proof.MlKem.X86_64.S4.tab_facts M hM8
  have htab : s₁.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (8 * M)) 64 = BitVec.ofNat 64 (tabEntry M) := by
    rw [h.pinv.buf.2 M (by bdd_omega), tabQ, ite_eq_left hM8]
  have hbx : s₁.gpr .rbx = VG.Proof.MlKem.X86_64.S4.scr σ := h.pinv.env.rbx
  have hbp : s₁.gpr .rbp = poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K := h.rbp
  have hlen : (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ t
  have hdi : (s₁.gpr .rdi).toNat = (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length := by rw [h.rdi, ofNat64_toNat (by bdd_omega)]
  have haddr : s₁.gpr .rbp + BitVec.ofNat 64 (4 * (s₁.gpr .rdi).toNat) = coeffAddr (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K) (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length := by
    rw [hbp, hdi]
  have hrd : s₁.rd ++ s₁.wr = [VG.Proof.MlKem.X86_64.S4.sdR σ, VG.Proof.MlKem.X86_64.S4.aR σ, VG.Proof.MlKem.X86_64.S4.scrR σ] := VG.Proof.MlKem.X86_64.S4.regs hp h.pinv.env
  have hout : InRegions s₁.wr (coeffAddr (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K) (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length) 32 := by
    rw [h.pinv.env.wr, hp.wr]
    exact ⟨VG.Proof.MlKem.X86_64.S4.aR σ, by simp, by rw [coeffAddr, poly4, Offset.add_add]; exact Offset.contains_base _ (by bdd_omega) (by bdd_omega)⟩
  have hsep : ∀ V : BitVec 256, (s₁.mem.writeW (coeffAddr (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K) (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length) V).readW
      (VG.Proof.MlKem.X86_64.S4.at' σ (8 * M + 4)) 32 = s₁.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (8 * M + 4)) 32 := fun V =>
    ((Frame.refl _ _).writeW (List.mem_singleton_self (VG.Proof.MlKem.X86_64.S4.aR σ)) V (by
        rw [coeffAddr, poly4, Offset.add_add]; exact Offset.contains_base _ (by bdd_omega) (by bdd_omega))).readW
      (r := VG.Proof.MlKem.X86_64.S4.scrR σ) (Offset.contains_base _ (by bdd_omega) (by bdd_omega)) (by simpa using hp.a_scr.symm) (by decide)
  refine WP.mono (VG.Proof.MlKem.X86_64.S4.vput_ok c₁ h0 hax
    (by rw [hbx, hrd]; exact ⟨VG.Proof.MlKem.X86_64.S4.scrR σ, by simp, Offset.contains_base _ (by bdd_omega) (by bdd_omega)⟩)
    (by rw [hbx, hrd]; exact ⟨VG.Proof.MlKem.X86_64.S4.scrR σ, by simp, Offset.contains_base _ (by bdd_omega) (by bdd_omega)⟩)
    (by rw [haddr]; exact hout) (by rw [haddr, hbx]; exact hsep))
    fun s₂ ⟨⟨V, hm₂, hV⟩, hdi₂, hsi₂, c₂, rd₂, wr₂, g₂⟩ => ?_
  rw [hbx] at hV hdi₂
  rw [haddr] at hm₂
  -- the table's entry
  have hlo : (dword (s₁.mem.readW (VG.Proof.MlKem.X86_64.S4.scr σ + BitVec.ofNat 64 (8 * M)) 128) 0).toNat = tabEntry M % 2 ^ 32 := by
    have e := readW_extract s₁.mem (VG.Proof.MlKem.X86_64.S4.scr σ + BitVec.ofNat 64 (8 * M)) (w := 64) (k := 0) (n := 4) (by bdd_omega)
    rw [add_ofNat_zero] at e
    rw [dword_readW _ _ (by decide), Nat.mul_zero, add_ofNat_zero, ← e, ← VG.Proof.MlKem.X86_64.S4.at', htab, BitVec.extractLsb'_toNat,
      BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.mod_eq_of_lt hE]
  have hhi : (s₁.mem.readW (VG.Proof.MlKem.X86_64.S4.scr σ + BitVec.ofNat 64 (8 * M + 4)) 32).toNat = (setBits M).length := by
    have e := readW_extract s₁.mem (VG.Proof.MlKem.X86_64.S4.scr σ + BitVec.ofNat 64 (8 * M)) (w := 64) (k := 4) (n := 4) (by bdd_omega)
    rw [Offset.add_add] at e
    rw [← e, ← VG.Proof.MlKem.X86_64.S4.at', htab, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hE, hcnt]
    have := VG.Proof.MlKem.X86_64.S4.setBits_length M
    exact Nat.mod_eq_of_lt (by bdd_omega)
  -- the coefficients
  have hacc : VG.Proof.MlKem.acc4 (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) (3 * t) = (setBits M).map fun k => ofNat (VG.Proof.MlKem.cand4 (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) (3 * t) k) := by
    rw [VG.Proof.MlKem.acc4, hsb, q_eq]
  have hl' : (sampleAfter [] (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) t).length < 249 := hl
  have hL4 : VG.Proof.MlKem.X86_64.S4.Lt σ K (t + 4) = VG.Proof.MlKem.X86_64.S4.Lt σ K t ++ VG.Proof.MlKem.acc4 (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) (3 * t) := VG.Proof.MlKem.sampleAfter_four (by rw [n_eq]; omega)
  have hmem : ∀ k ∈ setBits M, k < 8 ∧ VG.Proof.MlKem.cand4 (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) (3 * t) k < 3329 := fun k hk => by
    rw [hsb, List.mem_filter, List.mem_range, decide_eq_true_eq] at hk; exact hk
  have hst : Stored s₂.mem (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K) (VG.Proof.MlKem.X86_64.S4.Lt σ K (t + 4)) := by
    rw [hL4, hm₂]
    refine VG.Proof.MlKem.X86_64.stored_write8 h.stored (by bdd_omega) (by rw [hacc, List.length_map]; exact VG.Proof.MlKem.X86_64.S4.setBits_length M) V fun i hi => ?_
    rw [hacc, List.length_map] at hi
    have hp' := hmem ((setBits M).getD i 0) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi)
    have hmap : ((setBits M).map fun k => ofNat (VG.Proof.MlKem.cand4 (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) (3 * t) k)).getD i 0 =
        ofNat (VG.Proof.MlKem.cand4 (xofByte (VG.Proof.MlKem.X86_64.S4.B σ K)) (3 * t) ((setBits M).getD i 0)) := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
        Option.getD_some]
    rw [hV i (by have := VG.Proof.MlKem.X86_64.S4.setBits_length M; omega), hlo, hnib i hi, hcand _ hp'.1, hacc, hmap, ofNat,
      Fin.val_ofNat, Nat.mod_eq_of_lt (by rw [q_eq]; exact hp'.2)]
  have hf : Frame [pR (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K)] s₁.mem s₂.mem := by
    rw [hm₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) V (Offset.contains_base _ (by bdd_omega) (by bdd_omega))
  have gk : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → s₂.gpr r = s₁.gpr r := fun r _ h2 h3 => g₂ r h2 h3
  refine ⟨⟨h.pinv.poly hp hK hf rd₂ wr₂ fun r hr => gk r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    ?_, ?_, by rw [gk _ (by decide) (by decide) (by decide), h.rbp], hst⟩, c₂, gk _ (by decide) (by decide) (by decide)⟩
  · rw [hsi₂, h.rsi, show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl, Offset.add_add]
    exact congrArg (fun x => VG.Proof.MlKem.X86_64.S4.at' σ (oBuf + 504 * K) + BitVec.ofNat 64 x) (by bdd_omega)
  · rw [hdi₂, hL4, List.length_append, hacc, List.length_map]
    apply BitVec.eq_of_toNat_eq
    have := VG.Proof.MlKem.X86_64.S4.setBits_length M
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_setWidth, hdi, hhi, BitVec.toNat_ofNat]
    omega

theorem vec_ok {K t : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) {s : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K t s) (hv : VG.Proof.MlKem.X86_64.S4.VC s)
    (hl : (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length < 249) :
    WP isa (.seq (.block vcand) (.block vput)) s fun s' => VG.Proof.MlKem.X86_64.S4.LAt σ K (t + 4) s' ∧ VG.Proof.MlKem.X86_64.S4.VC s' ∧ s'.gpr .r10 = s.gpr .r10 :=
  WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.vec1_ok hp hK ht h hv hl) fun _ ⟨hi, h10⟩ =>
    WP.mono (VG.Proof.MlKem.X86_64.S4.vec2_ok hp hK ht hi) fun _ ⟨l, c, h10'⟩ => ⟨l, c, h10'.trans h10⟩)

omit hp in
theorem cmp249_ok (s : State) :
    WP isa (.block [.alu .cmp .rdi (.imm 249)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .rdi).toNat < 249)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ x l, s'.lane x l = s.lane x l := by
  xrun [show BitVec.signExtend 64 (249 : BitVec 32) = 249 by decide, show (249 : BitVec 64).toNat = 249 from rfl]
  exact fun _ _ => rfl

omit hp in
theorem VC.same {s s' : State} (h : VG.Proof.MlKem.X86_64.S4.VC s) (hl : ∀ x l, s'.lane x l = s.lane x l) : VG.Proof.MlKem.X86_64.S4.VC s' :=
  ⟨fun l hl' => by rw [hl, h.c8 l hl'], fun l hl' => by rw [hl, h.c9 l hl'], fun l hl' => by rw [hl, h.c10 l hl'],
    fun l hl' => by rw [hl, h.c11 l hl'], fun l hl' => by rw [hl, h.c12 l hl'], fun l hl' => by rw [hl, h.c13 l hl']⟩

/-- Four iterations of the loop. -/
theorem vgrp_ok {K t : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) {s : State} (h : VG.Proof.MlKem.X86_64.S4.LV σ K t s) :
    WP isa vgrp s fun s' => VG.Proof.MlKem.X86_64.S4.LV σ K (t + 4) s' ∧ s'.gpr .r10 = s.gpr .r10 := by
  unfold vgrp
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.cmp249_ok s) fun s₁ ⟨hcf, hm, hg, hrd, hwr, hl⟩ => ?_)
  have l₁ : VG.Proof.MlKem.X86_64.S4.LAt σ K t s₁ := h.lat.same hg hm hrd hwr
  have hlen : (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ t
  rw [h.lat.rdi, ofNat64_toNat (by bdd_omega)] at hcf
  refine WP.ite _ hcf (fun hb => ?_) fun hb => ?_
  · have hb' : (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length < 249 := of_decide_eq_true hb
    exact WP.mono (VG.Proof.MlKem.X86_64.S4.vec_ok hp hK ht l₁ ((h.vc hb').same hl) hb') fun s' ⟨l', c', h10⟩ =>
      ⟨⟨l', fun _ => c'⟩, by rw [h10, hg]⟩
  · have hb' : ¬ (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length < 249 := of_decide_eq_false hb
    exact WP.mono (VG.Proof.MlKem.X86_64.S4.sca_ok hp hK ht l₁) fun s' ⟨l', h10⟩ =>
      ⟨⟨l', fun h' => absurd (Nat.lt_of_le_of_lt (VG.Proof.MlKem.X86_64.S4.Lt_mono σ K t 4) h') hb'⟩, by rw [h10, hg]⟩

omit hp in
theorem sub10_ok (s : State) :
    WP isa (.block [.alu .sub .r10 (.imm 1)]) s fun s' => (s'.mem = s.mem ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.zf = some (s.gpr .r10 - 1 == 0) ∧ ∀ x l, s'.lane x l = s.lane x l) ∧ Keep [.r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun
  exact fun _ _ => rfl

/-- The 42 groups of four iterations. -/
theorem loop_ok {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlKem.X86_64.S4.LV σ K 0 s) (h10 : s.gpr .r10 = BitVec.ofNat 64 21) :
    WP isa (.loop Sample4.vbody .ne) s (VG.Proof.MlKem.X86_64.S4.LAt σ K 168) := by
  refine wp_countdown (cnt := .r10) (N := 21) (by decide) (by decide) (fun i s => VG.Proof.MlKem.X86_64.S4.LV σ K (8 * i) s)
    (fun i hi s hs _ => ?_) (fun _ h => h.lat) h h10
  unfold Sample4.vbody
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.vgrp_ok hp hK (by bdd_omega) hs) fun s₁ ⟨h₁, g₁⟩ =>
    WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.vgrp_ok hp hK (by bdd_omega) h₁) fun s₂ ⟨h₂, g₂⟩ =>
      WP.mono (VG.Proof.MlKem.X86_64.S4.sub10_ok s₂) fun s₃ ⟨⟨hm, h10', hz, hl⟩, k⟩ => ?_))
  have e : 8 * i + 4 + 4 = 8 * (i + 1) := by bdd_omega
  rw [e] at h₂
  exact ⟨⟨h₂.lat.same' hm k, fun h' => (h₂.vc h').same hl⟩, by rw [h10', g₂, g₁], by rw [hz, g₂, g₁]⟩

omit hp in
/-- `vzeroupper` changes no register or memory the invariants see. -/
theorem vz_ok (s : State) :
    WP isa (.block [.vop .vzeroupper]) s fun s' => s'.mem = s.mem ∧ Keep [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left', Keep]
  exact ⟨rfl, fun _ _ => rfl, rfl, rfl⟩

omit hp in
theorem vz_lat {K t : Nat} {s : State} (h : VG.Proof.MlKem.X86_64.S4.LAt σ K t s) : WP isa (.block [.vop .vzeroupper]) s (VG.Proof.MlKem.X86_64.S4.LAt σ K t) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  exact h.same rfl rfl rfl rfl

/-- `parse K`. -/
theorem parse_ok {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlKem.X86_64.S4.PInv σ K s) : WP isa (parse K) s (VG.Proof.MlKem.X86_64.S4.PInv σ (K + 1)) := by
  unfold parse
  exact WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.setup_ok hp hK h) fun _ ⟨h₁, h10⟩ => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.loop_ok hp hK h₁ h10)
    fun _ h₂ => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.vz_lat h₂) fun _ h₃ => VG.Proof.MlKem.X86_64.S4.fallback_ok hp hK h₃)))

end

end VG.Proof.MlKem.X86_64.S4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.S4Top`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, correctness

The pieces, in order: the prologue, the round constants and the padded seeds
(`S4Absorb.lean`), three squeezes (`S4Squeeze.lean`), the table (`S4Tab.lean`),
the four polynomials (`S4Loop.lean`), and the epilogue, which returns whether
every seed sampled its polynomial.
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Proof.Sha3.X86_64.X4 (la)

section
variable {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ)
include hp

/-- The prologue, the round constants and the padded seeds. -/
theorem start_ok : WP isa (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4)) σ (VG.Proof.MlKem.X86_64.S4.SqInv σ 0) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.S4.pro_ok hp) fun s₁ h₁ => WP.mono (VG.Proof.MlKem.X86_64.S4.rc_ok hp h₁.env) fun s₂ h₂ => ?_
  have he₂ : VG.Proof.MlKem.X86_64.S4.Env σ s₂ := Env.low h₁.env (rs := [⟨VG.Proof.MlKem.X86_64.S4.at' σ oRc, 768⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by simp only [oRc, oSave]; omega))
    h₂.frame h₂.keep.2.1 h₂.keep.2.2 fun r hr => h₂.keep.gpr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.mono (VG.Proof.MlKem.X86_64.S4.absorb_ok hp (m₁ := s₂.mem) ⟨he₂, by rw [h₂.keep.gpr (by decide), h₁.r14], Frame.refl _ _⟩)
    fun s₃ ⟨a₃, b₃⟩ => ⟨a₃.env, a₃.r14, fun r hr k hk => ?_, VG.Proof.MlKem.X86_64.S4.lanes_A0 b₃, fun _ _ p hp' => absurd hp' (by omega)⟩
  rw [a₃.frame.readW (Region.contains_self _ _) (by
    simpa using Offset.disjoint_base (VG.Proof.MlKem.X86_64.S4.scr σ) (k := 800) (d := 32 * (50 + r) + 8 * k) (n := 8) (by omega) (by omega))
    (by decide)]
  exact h₂.rc r hr k hk

omit hp in
theorem epi_eq : epi = [.mov32 .rax (.reg .r14), .mov .r14 (.mem (at_ .rbx 4416)), .mov .r13 (.mem (at_ .rbx 4408)),
    .mov .r12 (.mem (at_ .rbx 4400)), .mov .rbp (.mem (at_ .rbx 4392)), .mov .rbx (.mem (at_ .rbx 4384))] := rfl

/-- The return value, and the callee-saved registers restored. -/
theorem end_ok {X : Mem → Prop} {s : State} (h : VG.Proof.MlKem.X86_64.S4.PC X σ 4 s) :
    WP isa (.block epi) s fun s' => sample4K.post σ s' ∧ gprPreserved σ s' := by
  have hin : ∀ i < 5, InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.S4.scr σ + BitVec.ofNat 64 (oSave + 8 * i)) 8 := fun i hi =>
    VG.Proof.MlKem.X86_64.S4.in_scr' hp h.env.rd h.env.wr (by simp only [oSave]; omega)
  rw [VG.Proof.MlKem.X86_64.S4.epi_eq]
  refine WP.mono (WP.keep [.rax, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' => s'.mem = s.mem ∧
      (s'.gpr .rax).setWidth 32 = (s.gpr .r14).setWidth 32 ∧
      s'.gpr .r14 = s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (oSave + 8 * 4)) 64 ∧ s'.gpr .r13 = s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (oSave + 8 * 3)) 64 ∧
      s'.gpr .r12 = s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (oSave + 8 * 2)) 64 ∧ s'.gpr .rbp = s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (oSave + 8 * 1)) 64 ∧
      s'.gpr .rbx = s.mem.readW (VG.Proof.MlKem.X86_64.S4.at' σ (oSave + 8 * 0)) 64)
    (by
      have h0 := hin 0 (by decide); have h1 := hin 1 (by decide); have h2 := hin 2 (by decide)
      have h3 := hin 3 (by decide); have h4 := hin 4 (by decide)
      simp only [oSave, Nat.reduceMul, Nat.reduceAdd] at h0 h1 h2 h3 h4
      xrun [h0, h1, h2, h3, h4, h.env.rbx]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (by decide)) fun s' ⟨⟨hm, hax, h14, h13, h12, hbp, hbx⟩, k⟩ => ?_
  refine ⟨⟨?_, fun k hk f e => ?_⟩, fun r hr => ?_, ?_⟩
  · rw [hax, h.r14, VG.Proof.MlKem.X86_64.S4.okN]
    split <;> rfl
  · rw [hm]; exact h.polys k hk f e
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hbx]; exact h.env.saved 0 (by decide)
    · rw [hbp]; exact h.env.saved 1 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.rsp
    · rw [h12]; exact h.env.saved 2 (by decide)
    · rw [h13]; exact h.env.saved 3 (by decide)
    · rw [h14]; exact h.env.saved 4 (by decide)
    · rw [k.gpr (by decide)]; exact h.env.r15
  · rw [hm]
    exact h.env.frame.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.ret_a, hp.ret_scr, Offset.base_disjoint_below (σ.gpr .rsp) (n := 24) (k := 8) (by omega)⟩)
      (by decide)

/-- The three squeezes, the table and the four polynomials. -/
theorem squeezes_ok {s : State} (h : VG.Proof.MlKem.X86_64.S4.SqInv σ 0 s) :
    WP isa (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (squeeze4 2) (.seq (.block tabBuild)
      (.seq (parse 0) (.seq (parse 1) (.seq (parse 2) (.seq (parse 3) (.block epi))))))))) s fun s' =>
      sample4K.post σ s' ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.sq_ok hp (by decide) h) fun s₁ h₁ => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.sq_ok hp (by decide) h₁)
    fun s₂ h₂ => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.sq_ok hp (by decide) h₂) fun s₃' h₃' =>
      WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.pinv0_ok hp h₃') fun s₃ p₀ => ?_))))
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.parse_ok hp (by decide) p₀) fun s₄ p₁ => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.parse_ok hp (by decide) p₁)
    fun s₅ p₂ => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.parse_ok hp (by decide) p₂) fun s₆ p₃ =>
      WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.parse_ok hp (by decide) p₃) fun s₇ p₄ => VG.Proof.MlKem.X86_64.S4.end_ok hp p₄))))

end

theorem correct (σ : State) (hs : sample4K.pre σ) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 σ t s' ∧ abiPreserved σ s' ∧ sample4K.post σ s' := by
  have hp := VG.Proof.MlKem.X86_64.S4.pre_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.start_ok hp) fun _ h => VG.Proof.MlKem.X86_64.S4.squeezes_ok hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlKem.X86_64.S4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.PrfBatch`. -/
section

/-!
# ML-KEM on x86-64: four instances of `PRF₂` at once

`Prf4.batch N₀ m o wl` (`Impl/MlKem/X86_64/Frag.lean`) writes `PRF₂(σ, N₀ +
k)` to `scratch + o + 128 k` for each `k < m`, with `σ` at `scratch + 1056`
and `scratch` in `rbx` (`batch_ok`). The input `σ ‖ N` is one block, whose
padded state (`P0`) the code writes into each of the four states, byte by byte
as `vg_mlkem_sample_ntt4_avx2` does (`S4Absorb.lean`); the permutation is
`permute4` (`permute4_ok`), and the output the first 128 bytes of each
permuted state (`prf_byte`).
-/

namespace VG.Proof.MlKem.X86_64.Prf4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Prf4
open VG.Spec.MlKem
open VG.Spec.Sha3 (keccakF RC bytesAt)
open VG.Proof.Sha3 (byteOf Rep xorByte byteOf_xorByte byteOf_xorBytes absorb_pad iterF)
open VG.Proof.MlKem (padded prf_eq prf_length)
open VG.Proof.Sha3.X86_64.X4 (q4 la ba la_byte Lanes4 lanes4_of_bytes byte_of_lanes4 Pre4 permute4_ok wp_vmovq wp_vbcast
  wp_vst wp_vxor readW_write256 q4_ymm)
open VG.Proof.MlKem.X86_64.S4 (bytes_write wb_in wb_out byte_setWidth vz_ok)
open VG.Proof.Sha3.X86_64 (wp_movi64 wp_movm wp_store wp_store8 wp_mov32i wp_nil)

/-! ## The padded input and the output -/

/-- The state whose permutation is the padded `σ ‖ n` (one block of SHAKE256). -/
def P0 (σ : List Byte) (n : Byte) : Spec.Sha3.State :=
  xorByte (xorByte (Rep 136 (σ ++ [n])) 33 0x1f) 135 0x80

theorem padded_P0 {σ : List Byte} (h : σ.length = 32) (n : Byte) :
    padded 136 Spec.Sha3.shakeSuffix (σ ++ [n]) = keccakF (VG.Proof.MlKem.X86_64.Prf4.P0 σ n) := by
  rw [padded, absorb_pad (by decide) (by decide), List.length_append, h]; rfl

/-- Byte `q` of the padded state. -/
abbrev PF (σ : List Byte) (n : Byte) (q : Nat) : Byte :=
  if q < 32 then σ.getD q 0 else if q = 32 then n else if q = 33 then 0x1f else if q = 135 then 0x80 else 0

theorem byteOf_P0 {σ : List Byte} (h : σ.length = 32) (n : Byte) {q : Nat} (hq : q < 200) :
    byteOf (VG.Proof.MlKem.X86_64.Prf4.P0 σ n) q = VG.Proof.MlKem.X86_64.Prf4.PF σ n q := by
  have hz : byteOf Spec.Sha3.zero q = 0 := by
    simp only [byteOf, Spec.Sha3.zero, getElem!_pos (Vector.replicate 25 (0 : BitVec 64)) (q / 8) (by bdd_omega),
      Vector.getElem_replicate]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  have hl : (σ ++ [n]).length = 33 := by rw [List.length_append, h]; rfl
  have ha : Spec.Sha3.absorb 136 (σ ++ [n]) = Spec.Sha3.zero := by simp [Spec.Sha3.absorb, hl]
  have hr : byteOf (Rep 136 (σ ++ [n])) q = (σ ++ [n]).getD q 0 := by
    rw [Rep, ha, byteOf_xorBytes _ _ hq, hz, hl, show 136 * (33 / 136) = 0 from rfl, List.drop_zero]
    exact BitVec.zero_xor
  have hg : (σ ++ [n]).getD q 0 = if q < 32 then σ.getD q 0 else if q = 32 then n else 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append]
    by_cases e1 : q < 32
    · rw [ifp (show q < σ.length by bdd_omega), ifp e1, List.getD_eq_getElem?_getD]
    · rw [ifn (show ¬ q < σ.length by bdd_omega), ifn e1, h]
      by_cases e2 : q = 32
      · subst e2; rw [ifp rfl]; rfl
      · rw [ifn e2, List.getElem?_singleton, ifn (by bdd_omega)]; rfl
  rw [VG.Proof.MlKem.X86_64.Prf4.P0, byteOf_xorByte _ _ _ hq, byteOf_xorByte _ _ _ hq, hr, hg, VG.Proof.MlKem.X86_64.Prf4.PF]
  by_cases e1 : q < 32
  · rw [ifn (show ¬ q = 135 by bdd_omega), ifn (show ¬ q = 33 by bdd_omega), ifp e1, ifp e1]
  · rw [ifn e1, ifn e1]
    by_cases e2 : q = 32
    · rw [ifn (show ¬ q = 135 by bdd_omega), ifn (show ¬ q = 33 by bdd_omega), ifp e2, ifp e2]
    · rw [ifn e2, ifn e2]
      by_cases e3 : q = 33
      · rw [ifn (show ¬ q = 135 by bdd_omega), ifp e3, ifp e3]; exact BitVec.zero_xor
      · rw [ifn e3, ifn e3]
        by_cases e4 : q = 135
        · rw [ifp e4, ifp e4]; exact BitVec.zero_xor
        · rw [ifn e4, ifn e4]

/-- Byte `j` of `PRF₂(σ, n)`: of the permuted padded state. -/
theorem prf_byte {σ : List Byte} (h : σ.length = 32) (n : Byte) {j : Nat} (hj : j < 128) :
    (prf 2 σ n)[j]'(by rw [prf_length]; exact hj) = byteOf (keccakF (VG.Proof.MlKem.X86_64.Prf4.P0 σ n)) j := by
  have e := Proof.Sha3.squeezeFrom_getElem (rate := 136) (by decide) (by decide)
    (padded 136 Spec.Sha3.shakeSuffix (σ ++ [n])) (pos := 0) (d := 64 * 2) (i := j) (by bdd_omega)
  rw [List.getElem_of_eq (prf_eq 2 σ n), e, show (0 + j) / 136 = 0 by bdd_omega, show (0 + j) % 136 = j by bdd_omega,
    VG.Proof.MlKem.X86_64.Prf4.padded_P0 h]
  rfl

/-- `PRF₂(σ, n)` in memory, from its bytes. -/
theorem bytes_prf {m : Mem} {p : Addr} {σ : List Byte} (h : σ.length = 32) {n : Byte}
    (hb : ∀ j < 128, m (p + BitVec.ofNat 64 j) = byteOf (keccakF (VG.Proof.MlKem.X86_64.Prf4.P0 σ n)) j) :
    bytesAt m p 128 = prf 2 σ n := by
  apply List.ext_getElem (by rw [prf_length]; simp [bytesAt])
  intro j h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  rw [VG.Proof.MlKem.X86_64.Prf4.prf_byte h n h₁]
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  exact hb j h₁

/-! ## Where the code works -/

section
variable (b : Addr) (wl o m : Nat)
/-- The four states, from lane `wl` of `scratch` (at `b`). -/
abbrev sP : Addr := b + BitVec.ofNat 64 (32 * wl)
/-- `σ`. -/
abbrev sS : Addr := b + BitVec.ofNat 64 (oG + 32)
/-- The working space. -/
abbrev wR : Region := ⟨VG.Proof.MlKem.X86_64.Prf4.sP b wl, 2368⟩
/-- The outputs. -/
abbrev oR : Region := ⟨b + BitVec.ofNat 64 o, 128 * m⟩
abbrev sR : Region := ⟨VG.Proof.MlKem.X86_64.Prf4.sS b, 32⟩
end

/-- What `batch N₀ m o wl` needs of the state `s₀` it starts from, with
`scratch` at `b`. -/
structure BPre (b : Addr) (wl o m : Nat) (s₀ : State) : Prop where
  rbx : s₀.gpr .rbx = b
  w : InRegions s₀.wr (VG.Proof.MlKem.X86_64.Prf4.sP b wl) 2368
  out : InRegions s₀.wr (b + BitVec.ofNat 64 o) (128 * m)
  sig : InRegions (s₀.rd ++ s₀.wr) (VG.Proof.MlKem.X86_64.Prf4.sS b) 32
  dWO : (VG.Proof.MlKem.X86_64.Prf4.wR b wl).Disjoint (VG.Proof.MlKem.X86_64.Prf4.oR b o m)
  dWS : (VG.Proof.MlKem.X86_64.Prf4.wR b wl).Disjoint (VG.Proof.MlKem.X86_64.Prf4.sR b)
  dOS : (VG.Proof.MlKem.X86_64.Prf4.oR b o m).Disjoint (VG.Proof.MlKem.X86_64.Prf4.sR b)
  hm : m ≤ 4
  small : 32 * wl + 2368 < 2 ^ 31

/-- Between the pieces of `batch`, from `s₀`. -/
structure BEnv (b : Addr) (wl o m : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cs : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  frame : Frame [VG.Proof.MlKem.X86_64.Prf4.wR b wl, VG.Proof.MlKem.X86_64.Prf4.oR b o m] s₀.mem s.mem

theorem rax_ncs : ∀ r ∈ calleeSaved, r ≠ .rax := by decide

/-- `σ`, from `s₀`. -/
abbrev sig (b : Addr) (s₀ : State) : List Byte := bytesAt s₀.mem (VG.Proof.MlKem.X86_64.Prf4.sS b) 32

theorem sig_length (b : Addr) (s₀ : State) : (VG.Proof.MlKem.X86_64.Prf4.sig b s₀).length = 32 := by simp [bytesAt]

theorem sig_getD (b : Addr) (s₀ : State) {q : Nat} (hq : q < 32) :
    (VG.Proof.MlKem.X86_64.Prf4.sig b s₀).getD q 0 = s₀.mem (VG.Proof.MlKem.X86_64.Prf4.sS b + BitVec.ofNat 64 q) := by
  simp [bytesAt, hq]

/-- An address of the working space. -/
theorem at_w (b : Addr) {wl x d : Nat} (h : x = 32 * wl + d) :
    b + BitVec.ofNat 64 x = VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 d := by
  rw [VG.Proof.MlKem.X86_64.Prf4.sP, Offset.add_add, h]

section
variable {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀)
include hp

theorem BEnv.rbx {s : State} (he : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s) : s.gpr .rbx = b := (he.cs .rbx (by decide)).trans hp.rbx

omit hp in
theorem BEnv.refl : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s₀ := ⟨rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem in_w {s : State} (he : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s) {a n : Nat} (h : a + n ≤ 2368) :
    InRegions s.wr (VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 a) n := by
  rw [he.wr]; exact VG.Proof.MlKem.X86_64.inRegions_sub hp.w h (by decide)

theorem in_w' {s : State} (he : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s) {a n : Nat} (h : a + n ≤ 2368) :
    InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 a) n :=
  VG.Proof.Sha3.X86_64.X4.in_append (VG.Proof.MlKem.X86_64.Prf4.in_w hp he h)

theorem in_o {s : State} (he : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s) {a n : Nat} (h : a + n ≤ 128 * m) :
    InRegions s.wr (b + BitVec.ofNat 64 o + BitVec.ofNat 64 a) n := by
  rw [he.wr]; exact VG.Proof.MlKem.X86_64.inRegions_sub hp.out h (by have := hp.hm; omega)

theorem in_s {s : State} (he : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s) {a n : Nat} (h : a + n ≤ 32) :
    InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.Prf4.sS b + BitVec.ofNat 64 a) n := by
  rw [he.rd, he.wr]; exact VG.Proof.MlKem.X86_64.inRegions_sub hp.sig h (by decide)

/-- `σ` is not written. -/
theorem sig_readW {s : State} (he : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s) {i : Nat} (hi : i < 4) :
    s.mem.readW (VG.Proof.MlKem.X86_64.Prf4.sS b + BitVec.ofNat 64 (8 * i)) 64 = s₀.mem.readW (VG.Proof.MlKem.X86_64.Prf4.sS b + BitVec.ofNat 64 (8 * i)) 64 :=
  he.frame.readW (r := VG.Proof.MlKem.X86_64.Prf4.sR b) (Offset.contains_base _ (by bdd_omega) (by bdd_omega))
    (by simpa using ⟨hp.dWS.symm, hp.dOS.symm⟩) (by decide)

omit hp in
/-- A write within the working space. -/
theorem BEnv.write {s s' : State} (he : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s) {e n : Nat} (hn : e + n ≤ 2368)
    {v : BitVec (8 * n)} (hm : s'.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 e) v) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, fun r hr => (hg r hr).trans (he.cs r hr), ?_⟩
  rw [hm]
  exact he.frame.writeW (List.mem_cons_self ..) v (by
    rw [show 8 * n / 8 = n by bdd_omega]; exact Offset.contains_base _ hn (by bdd_omega))

/-- A write within the outputs. -/
theorem BEnv.writeO {s s' : State} (he : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s) {e n : Nat} (hn : e + n ≤ 128 * m)
    {v : BitVec (8 * n)} (hm : s'.mem = s.mem.writeW (b + BitVec.ofNat 64 o + BitVec.ofNat 64 e) v)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s' := by
  have := hp.hm
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, fun r hr => (hg r hr).trans (he.cs r hr), ?_⟩
  rw [hm]
  exact he.frame.writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) v (by
    rw [show 8 * n / 8 = n by bdd_omega]; exact Offset.contains_base _ hn (by bdd_omega))

end

/-! ## The round constants -/

/-- The table of the round constants, from lane 50 of the states. -/
abbrev Tbl (p : Addr) (n : Nat) (mem : Mem) : Prop := ∀ r < n, ∀ k < 4, mem.readW (la p (50 + r) k) 64 = RC r

theorem rc_step {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {r : Nat} (hr : r < 24) {s : State}
    (h : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s ∧ VG.Proof.MlKem.X86_64.Prf4.Tbl (VG.Proof.MlKem.X86_64.Prf4.sP b wl) r s.mem) :
    WP isa (.block [.movImm64 .rax (RC r), .vop (.vmovq .xmm0 .rax),
      .vop (.vpbroadcastq .l256 .xmm0 .xmm0), Impl.Sha3.X86_64.X4.st .rbx (wl + 50 + r) .xmm0]) s
      (fun s' => VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s' ∧ VG.Proof.MlKem.X86_64.Prf4.Tbl (VG.Proof.MlKem.X86_64.Prf4.sP b wl) (r + 1) s'.mem) := by
  obtain ⟨he, ht⟩ := h
  have hbx := he.rbx hp
  have := hp.small
  refine wp_movi64 fun s₁ u₁ => wp_vmovq fun s₂ u₂ => wp_vbcast fun s₃ u₃ =>
    wp_vst (a := VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 (32 * (50 + r)))
      (by rw [VG.Proof.Sha3.X86_64.ea_at, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hbx]; exact VG.Proof.MlKem.X86_64.Prf4.at_w b (by bdd_omega))
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact VG.Proof.MlKem.X86_64.Prf4.in_w hp he (by bdd_omega))
      fun s₄ g₄ _ m₄ r₄ w₄ => wp_nil ?_
  have hv : ∀ k < 4, q4 s₃ .xmm0 k = RC r := fun k hk => by
    rw [u₃.val k hk, u₂.val 0 (by decide), ite_eq_left rfl, u₁.gpr]
  have hm : s₄.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 (32 * (50 + r))) (s₃.ymm .xmm0) := by
    rw [m₄, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨he.write (n := 32) (by bdd_omega) hm (by rw [r₄, u₃.rd, u₂.rd, u₁.rd]) (by rw [w₄, u₃.wr, u₂.wr, u₁.wr])
    fun g hg => by rw [g₄, u₃.gpr, u₂.gpr, u₁.other g (VG.Proof.MlKem.X86_64.Prf4.rax_ncs g hg)], fun r' hr' k hk => ?_⟩
  rw [hm]
  by_cases e : r' = r
  · subst e
    rw [la, ← Offset.add_add, readW_write256 _ _ _ hk, q4_ymm _ _ hk, hv k hk]
  · have e := readW_writeW_off s.mem (VG.Proof.MlKem.X86_64.Prf4.sP b wl) (s₃.ymm .xmm0) (d := 32 * (50 + r') + 8 * k)
      (e := 32 * (50 + r)) (n := 8) (by bdd_omega) (by bdd_omega) (by bdd_omega)
    exact e.trans (ht r' (by bdd_omega) k hk)

theorem rcTable_eq (wl : Nat) : Impl.Sha3.X86_64.X4.rcTable .rbx (wl + 50) = (List.range 24).flatMap fun r =>
    [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax), .vop (.vpbroadcastq .l256 .xmm0 .xmm0),
      Impl.Sha3.X86_64.X4.st .rbx (wl + 50 + r) .xmm0] := rfl

theorem rc_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {s : State}
    (he : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s) :
    WP isa (.block (Impl.Sha3.X86_64.X4.rcTable .rbx (wl + 50))) s
      (fun s' => VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s' ∧ VG.Proof.MlKem.X86_64.Prf4.Tbl (VG.Proof.MlKem.X86_64.Prf4.sP b wl) 24 s'.mem) := by
  rw [VG.Proof.MlKem.X86_64.Prf4.rcTable_eq]
  exact wp_range_flatMap (M := isa) (fun r s => VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s ∧ VG.Proof.MlKem.X86_64.Prf4.Tbl (VG.Proof.MlKem.X86_64.Prf4.sP b wl) r s.mem)
    (fun r s hr h => VG.Proof.MlKem.X86_64.Prf4.rc_step hp hr h) 24 (Nat.le_refl _) s ⟨he, fun _ h => absurd h (by bdd_omega)⟩

/-! ## The padded inputs, byte by byte -/

/-- The four states at `p` hold `F`. -/
def SB (p : Addr) (mem : Mem) (F : Nat → Nat → Byte) : Prop := ∀ k < 4, ∀ q < 200, mem (ba p k q) = F k q

/-- While the states are written, after the table (in `m₁`). -/
structure AI (b : Addr) (wl o m : Nat) (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s
  fr : Frame [⟨VG.Proof.MlKem.X86_64.Prf4.sP b wl, 800⟩] m₁ s.mem

theorem AI.write {b : Addr} {wl o m : Nat} {s₀ : State} {m₁ : Mem} {s s' : State}
    (h : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s) {e n : Nat} (hn : e + n ≤ 800)
    {v : BitVec (8 * n)} (hm : s'.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 e) v) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s' :=
  ⟨h.env.write (by bdd_omega) hm hrd hwr hg, by
    rw [hm]
    exact h.fr.writeW (List.mem_singleton_self _) v (by
      rw [show 8 * n / 8 = n by bdd_omega]; exact Offset.contains_base _ hn (by bdd_omega))⟩

/-- A step that writes no memory and no callee-saved register. -/
theorem AI.keep {b : Addr} {wl o m : Nat} {s₀ : State} {m₁ : Mem} {s s' : State}
    (h : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s' :=
  h.write (e := 0) (n := 0) (v := 0) (by bdd_omega) (by rw [hm]; funext x; simp [Mem.writeW, Mem.write]) hrd hwr hg

/-! ### Zeroing -/

structure ZInv (b : Addr) (wl o m : Nat) (s₀ : State) (m₁ : Mem) (n : Nat) (s : State) : Prop where
  ai : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s
  x0 : ∀ k < 4, q4 s .xmm0 k = 0
  bytes : ∀ k < 4, ∀ q < 200, q / 8 < n → s.mem (ba (VG.Proof.MlKem.X86_64.Prf4.sP b wl) k q) = 0

theorem zero_step {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {m₁ : Mem} {i : Nat}
    (hi : i < 25) {s : State} (h : VG.Proof.MlKem.X86_64.Prf4.ZInv b wl o m s₀ m₁ i s) :
    WP isa (.block [Impl.Sha3.X86_64.X4.st .rbx (wl + i) .xmm0]) s (VG.Proof.MlKem.X86_64.Prf4.ZInv b wl o m s₀ m₁ (i + 1)) := by
  have := hp.small
  refine wp_vst (a := VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 (32 * i))
    (by rw [VG.Proof.Sha3.X86_64.ea_at, h.ai.env.rbx hp]; exact VG.Proof.MlKem.X86_64.Prf4.at_w b (by bdd_omega))
    (VG.Proof.MlKem.X86_64.Prf4.in_w hp h.ai.env (by bdd_omega)) fun s' g' q' m' r' w' => wp_nil ?_
  refine ⟨h.ai.write (e := 32 * i) (n := 32) (by bdd_omega) m' r' w' fun r _ => by rw [g'],
    fun k hk => by rw [q', h.x0 k hk], fun k hk q hq hn => ?_⟩
  rw [m']
  have hb := VG.Proof.MlKem.X86_64.S4.bytes_write (m := s.mem) (p := VG.Proof.MlKem.X86_64.Prf4.sP b wl) (F := fun k q => s.mem (ba (VG.Proof.MlKem.X86_64.Prf4.sP b wl) k q))
    (fun _ _ _ _ => rfl) (s.ymm .xmm0) (e := 32 * i) (by decide) (by bdd_omega) hk hq
  rw [hb]
  split
  · rename_i hc
    simp only [S4.off4] at hc ⊢
    rw [show 8 * (32 * (q / 8) + 8 * k + q % 8 - 32 * i) = 64 * k + 8 * (q % 8) by bdd_omega,
      ← extract_extract (s.ymm .xmm0) (64 * k) 64 (8 * (q % 8)) 8 (by bdd_omega), q4_ymm _ _ hk, h.x0 k hk]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  · rename_i hc
    simp only [S4.off4] at hc
    exact h.bytes k hk q hq (by bdd_omega)

theorem zero_eq (wl : Nat) : zero wl = Impl.Sha3.X86_64.X4.vb .vpxor .xmm0 .xmm0 .xmm0 ::
    (List.range 25).flatMap fun i => [Impl.Sha3.X86_64.X4.st .rbx (wl + i) .xmm0] := rfl

theorem zero_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {m₁ : Mem} {s : State}
    (h : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s) :
    WP isa (.block (zero wl)) s (fun s' => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s' ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s'.mem fun _ _ => 0) := by
  rw [VG.Proof.MlKem.X86_64.Prf4.zero_eq]
  refine wp_vxor fun s₁ u₁ => WP.mono (wp_range_flatMap (M := isa) (VG.Proof.MlKem.X86_64.Prf4.ZInv b wl o m s₀ m₁)
    (fun i s hi h => VG.Proof.MlKem.X86_64.Prf4.zero_step hp hi h) 25 (Nat.le_refl _) s₁
    ⟨h.keep u₁.mem u₁.rd u₁.wr fun r _ => by rw [u₁.gpr],
      fun k hk => by rw [u₁.val k hk, BitVec.xor_self]; rfl, fun _ _ _ _ h => absurd h (by bdd_omega)⟩)
    fun s' h' => ⟨h'.ai, fun k hk q hq => h'.bytes k hk q hq (by bdd_omega)⟩

/-! ### `σ` -/

/-- The states after the first `I` lanes of `σ` (and the first `K` states of lane `I`). -/
def GF (b : Addr) (s₀ : State) (I K : Nat) (k q : Nat) : Byte :=
  if q < 8 * I ∨ (q / 8 = I ∧ k < K) then s₀.mem (VG.Proof.MlKem.X86_64.Prf4.sS b + BitVec.ofNat 64 q) else 0

theorem sig_store {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {m₁ : Mem} {I K : Nat}
    (hI : I < 4) (hK : K < 4) {s : State}
    (h : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s ∧ s.gpr .rax = s₀.mem.readW (VG.Proof.MlKem.X86_64.Prf4.sS b + BitVec.ofNat 64 (8 * I)) 64 ∧
      VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s.mem (VG.Proof.MlKem.X86_64.Prf4.GF b s₀ I K)) :
    WP isa (.block [.store (at_ .rbx (32 * (wl + I) + 8 * K)) .rax]) s (fun s' => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s' ∧
      s'.gpr .rax = s₀.mem.readW (VG.Proof.MlKem.X86_64.Prf4.sS b + BitVec.ofNat 64 (8 * I)) 64 ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s'.mem (VG.Proof.MlKem.X86_64.Prf4.GF b s₀ I (K + 1))) := by
  obtain ⟨ha, hx, hb⟩ := h
  have := hp.small
  refine wp_store (a := VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 (32 * I + 8 * K))
    (by rw [ea_at, ha.env.rbx hp]; exact VG.Proof.MlKem.X86_64.Prf4.at_w b (by bdd_omega)) (VG.Proof.MlKem.X86_64.Prf4.in_w hp ha.env (by bdd_omega))
    fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 (32 * I + 8 * K))
      (s₀.mem.readW (VG.Proof.MlKem.X86_64.Prf4.sS b + BitVec.ofNat 64 (8 * I)) 64) := by rw [m₂, hx]
  refine ⟨ha.write (n := 8) (by bdd_omega) hm r₂ w₂ fun r _ => by rw [g₂], by rw [g₂, hx], fun k hk q hq => ?_⟩
  rw [hm, VG.Proof.MlKem.X86_64.S4.bytes_write hb _ (by decide) (by bdd_omega) hk hq]
  simp only [S4.off4]
  by_cases hc : 32 * I + 8 * K ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 32 * I + 8 * K + 64 / 8
  · have hk' : k = K := by bdd_omega
    have hq' : q / 8 = I := by bdd_omega
    subst hk'
    rw [ifp hc, VG.Proof.MlKem.X86_64.Prf4.GF, ifp (.inr ⟨hq', by bdd_omega⟩),
      show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * I + 8 * k)) = 8 * (q % 8) by bdd_omega,
      byte_readW _ _ (by bdd_omega), Offset.add_add, show 8 * I + q % 8 = q by bdd_omega]
  · rw [ifn hc, VG.Proof.MlKem.X86_64.Prf4.GF, VG.Proof.MlKem.X86_64.Prf4.GF]
    by_cases hc' : q < 8 * I ∨ (q / 8 = I ∧ k < K)
    · rw [ifp hc', ifp (by bdd_omega)]
    · rw [ifn hc', ifn (by bdd_omega)]

theorem sig_lane {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {m₁ : Mem} {I : Nat}
    (hI : I < 4) {s : State} (h : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s.mem (VG.Proof.MlKem.X86_64.Prf4.GF b s₀ I 0)) :
    WP isa (.block (.mov .rax (.mem (at_ .rbx (oG + 32 + 8 * I))) ::
      (List.range 4).flatMap fun k => [.store (at_ .rbx (32 * (wl + I) + 8 * k)) .rax])) s
      (fun s' => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s' ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s'.mem (VG.Proof.MlKem.X86_64.Prf4.GF b s₀ (I + 1) 0)) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movm (a := VG.Proof.MlKem.X86_64.Prf4.sS b + BitVec.ofNat 64 (8 * I)) (by rw [ea_at, ha.env.rbx hp, Offset.add_add])
    (VG.Proof.MlKem.X86_64.Prf4.in_s hp ha.env (by bdd_omega)) fun s₁ u₁ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s ∧
      s.gpr .rax = s₀.mem.readW (VG.Proof.MlKem.X86_64.Prf4.sS b + BitVec.ofNat 64 (8 * I)) 64 ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s.mem (VG.Proof.MlKem.X86_64.Prf4.GF b s₀ I K))
    (fun K s hK h => VG.Proof.MlKem.X86_64.Prf4.sig_store hp hI hK h) 4 (Nat.le_refl _) s₁
    ⟨ha.keep u₁.mem u₁.rd u₁.wr fun r hr => u₁.other r (VG.Proof.MlKem.X86_64.Prf4.rax_ncs r hr), by
      rw [u₁.gpr, VG.Proof.MlKem.X86_64.Prf4.sig_readW hp ha.env hI], by rw [u₁.mem]; exact hb⟩) fun s' ⟨ha', _, hb'⟩ =>
    ⟨ha', fun k hk q hq => ?_⟩
  rw [hb' k hk q hq, VG.Proof.MlKem.X86_64.Prf4.GF, VG.Proof.MlKem.X86_64.Prf4.GF]
  by_cases hc : q < 8 * I ∨ (q / 8 = I ∧ k < 4)
  · rw [ifp hc, ifp (by bdd_omega)]
  · rw [ifn hc, ifn (by bdd_omega)]

theorem sigLanes_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {m₁ : Mem} {s : State}
    (h : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s.mem fun _ _ => 0) :
    WP isa (.block (sigLanes wl)) s (fun s' => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s' ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s'.mem (VG.Proof.MlKem.X86_64.Prf4.GF b s₀ 4 0)) :=
  wp_range_flatMap (M := isa) (fun I s => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s.mem (VG.Proof.MlKem.X86_64.Prf4.GF b s₀ I 0))
    (fun I s hI h => VG.Proof.MlKem.X86_64.Prf4.sig_lane hp hI h) 4 (Nat.le_refl _) s
    ⟨h.1, fun k hk q hq => by rw [h.2 k hk q hq, VG.Proof.MlKem.X86_64.Prf4.GF, ifn (by bdd_omega)]⟩

/-! ### The indices and the padding -/

/-- The byte `c` (in `rax`) to byte `q₀` of state `K`. -/
theorem cbyte_step {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {m₁ : Mem}
    {F : Nat → Nat → Byte} {K q₀ : Nat} (hK : K < 4) (hq₀ : q₀ < 200) {c : Byte} {s : State}
    (hax : s.gpr .rax = c.setWidth 64) (h : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s.mem F) :
    WP isa (.block [.store8 (at_ .rbx (32 * (wl + q₀ / 8) + 8 * K + q₀ % 8)) .rax]) s
      (fun s' => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s' ∧ s'.gpr .rax = s.gpr .rax ∧
        VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s'.mem fun k q => if k = K ∧ q = q₀ then c else F k q) := by
  obtain ⟨ha, hb⟩ := h
  have := hp.small
  refine wp_store8 (a := VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 (32 * (q₀ / 8) + 8 * K + q₀ % 8))
    (by rw [ea_at, ha.env.rbx hp]; exact VG.Proof.MlKem.X86_64.Prf4.at_w b (by bdd_omega)) (VG.Proof.MlKem.X86_64.Prf4.in_w hp ha.env (by bdd_omega))
    fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 (32 * (q₀ / 8) + 8 * K + q₀ % 8)) c := by
    rw [m₂, hax, VG.Proof.MlKem.X86_64.S4.byte_setWidth]
  refine ⟨ha.write (n := 1) (by bdd_omega) hm r₂ w₂ fun r _ => by rw [g₂], by rw [g₂], fun k hk q hq => ?_⟩
  rw [hm, VG.Proof.MlKem.X86_64.S4.bytes_write hb _ (by decide) (by bdd_omega) hk hq]
  simp only [S4.off4]
  by_cases hc : 32 * (q₀ / 8) + 8 * K + q₀ % 8 ≤ 32 * (q / 8) + 8 * k + q % 8 ∧
      32 * (q / 8) + 8 * k + q % 8 < 32 * (q₀ / 8) + 8 * K + q₀ % 8 + 8 / 8
  · have e : k = K ∧ q = q₀ := by bdd_omega
    rw [ifp hc, ifp e, show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * (q₀ / 8) + 8 * K + q₀ % 8)) = 0 by bdd_omega,
      Proof.Sha3.extractLsb'_byte]
  · rw [ifn hc, ifn (by bdd_omega)]

theorem b8_of32 {n : Nat} (hn : n < 256) :
    ((BitVec.ofNat 32 n).setWidth 64 : BitVec 64) = (BitVec.ofNat 8 n).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by bdd_omega : n < 4294967296), Nat.mod_eq_of_lt (by bdd_omega : n < 18446744073709551616),
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by bdd_omega : n < 18446744073709551616)]

/-- The states after the indices of the first `K`. -/
def NF (b : Addr) (s₀ : State) (N₀ K : Nat) (k q : Nat) : Byte :=
  if q = 32 ∧ k < K then BitVec.ofNat 8 (N₀ + k) else VG.Proof.MlKem.X86_64.Prf4.GF b s₀ 4 0 k q

theorem nonces_eq (N₀ wl : Nat) : nonces N₀ wl = (List.range 4).flatMap fun k =>
    ([.mov32 .rax (.imm (BitVec.ofNat 32 (N₀ + k)))] : List Instr) ++
      ([.store8 (at_ .rbx (32 * (wl + 32 / 8) + 8 * k + 32 % 8)) .rax] : List Instr) := rfl

theorem nonces_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {m₁ : Mem} {N₀ : Nat}
    (hN : N₀ + 4 ≤ 256) {s : State} (h : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s.mem (VG.Proof.MlKem.X86_64.Prf4.GF b s₀ 4 0)) :
    WP isa (.block (nonces N₀ wl)) s (fun s' => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s' ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s'.mem (VG.Proof.MlKem.X86_64.Prf4.NF b s₀ N₀ 4)) := by
  rw [VG.Proof.MlKem.X86_64.Prf4.nonces_eq]
  refine wp_range_flatMap (M := isa) (fun K s => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s.mem (VG.Proof.MlKem.X86_64.Prf4.NF b s₀ N₀ K))
    (fun K s hK ⟨ha, hb⟩ => ?_) 4 (Nat.le_refl _) s ⟨h.1, fun k hk q hq => by rw [h.2 k hk q hq, VG.Proof.MlKem.X86_64.Prf4.NF, ifn (by bdd_omega)]⟩
  rw [WP.block_append_iff]
  refine wp_mov32i fun s₁ u₁ => wp_nil ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.Prf4.cbyte_step hp (F := VG.Proof.MlKem.X86_64.Prf4.NF b s₀ N₀ K) (q₀ := 32) (c := BitVec.ofNat 8 (N₀ + K)) hK (by decide)
    (by rw [u₁.gpr, VG.Proof.MlKem.X86_64.Prf4.b8_of32 (by bdd_omega)]) ⟨ha.keep u₁.mem u₁.rd u₁.wr fun r hr => u₁.other r (VG.Proof.MlKem.X86_64.Prf4.rax_ncs r hr),
      by rw [u₁.mem]; exact hb⟩) fun s' ⟨ha', _, hb'⟩ => ⟨ha', fun k hk q hq => ?_⟩
  rw [hb' k hk q hq]
  simp only [VG.Proof.MlKem.X86_64.Prf4.NF]
  by_cases e : k = K ∧ q = 32
  · rw [ifp e, ifp ⟨e.2, by bdd_omega⟩, e.1]
  · rw [ifn e]
    by_cases e' : q = 32 ∧ k < K
    · rw [ifp e', ifp ⟨e'.1, by bdd_omega⟩]
    · rw [ifn e', ifn (by bdd_omega)]

/-- The byte `c` to byte `q₀` of each state. -/
theorem cbytes_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {m₁ : Mem}
    {F : Nat → Nat → Byte} {q₀ : Nat} (hq₀ : q₀ < 200) {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64)
    (h : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s.mem F) :
    WP isa (.block ((List.range 4).flatMap fun k => [.store8 (at_ .rbx (32 * (wl + q₀ / 8) + 8 * k + q₀ % 8)) .rax])) s
      (fun s' => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s' ∧ s'.gpr .rax = s.gpr .rax ∧
        VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s'.mem fun k q => if q = q₀ then c else F k q) := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s' => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s' ∧ s'.gpr .rax = c.setWidth 64 ∧
      VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s'.mem fun k q => if k < K ∧ q = q₀ then c else F k q)
    (fun K s' hK ⟨ha, hx, hb⟩ => WP.mono (VG.Proof.MlKem.X86_64.Prf4.cbyte_step hp hK hq₀ hx ⟨ha, hb⟩) fun s'' ⟨ha', hx', hb'⟩ =>
      ⟨ha', hx'.trans hx, fun k hk q hq => ?_⟩) 4 (Nat.le_refl _) s ⟨h.1, hax, fun k hk q hq => ?_⟩)
    fun s' ⟨ha, hx, hb⟩ => ⟨ha, hx.trans hax.symm, fun k hk q hq => ?_⟩
  · rw [hb' k hk q hq]
    dsimp only
    by_cases e : k = K ∧ q = q₀
    · rw [ifp e, ifp (by bdd_omega)]
    · rw [ifn e]
      by_cases e' : k < K ∧ q = q₀
      · rw [ifp e', ifp (by bdd_omega)]
      · rw [ifn e', ifn (by bdd_omega)]
  · rw [h.2 k hk q hq]; dsimp only; rw [ifn (by bdd_omega)]
  · rw [hb k hk q hq]
    dsimp only
    by_cases e : q = q₀
    · rw [ifp e, ifp ⟨hk, e⟩]
    · rw [ifn e, ifn (by bdd_omega)]

theorem pads_eq (wl : Nat) : pads wl = ([.mov32 .rax (.imm 0x1f)] : List Instr) ++
    ((List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (32 * (wl + 33 / 8) + 8 * k + 33 % 8)) .rax]) ++
    (([.mov32 .rax (.imm 0x80)] : List Instr) ++
      (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (32 * (wl + 135 / 8) + 8 * k + 135 % 8)) .rax]))) :=
  rfl

/-- The padded inputs, from the states that hold `σ` and the indices. -/
theorem pads_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {m₁ : Mem} {N₀ : Nat}
    {s : State} (h : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s.mem (VG.Proof.MlKem.X86_64.Prf4.NF b s₀ N₀ 4)) :
    WP isa (.block (pads wl)) s (fun s' => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s' ∧
      VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s'.mem fun k q => VG.Proof.MlKem.X86_64.Prf4.PF (VG.Proof.MlKem.X86_64.Prf4.sig b s₀) (BitVec.ofNat 8 (N₀ + k)) q) := by
  rw [VG.Proof.MlKem.X86_64.Prf4.pads_eq, WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₁ u₁ => wp_nil
    (Q := fun s₁ => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s₁ ∧ s₁.gpr .rax = (0x1f : Byte).setWidth 64 ∧ VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s₁.mem (VG.Proof.MlKem.X86_64.Prf4.NF b s₀ N₀ 4))
    ⟨h.1.keep u₁.mem u₁.rd u₁.wr fun r hr => u₁.other r (VG.Proof.MlKem.X86_64.Prf4.rax_ncs r hr), by rw [u₁.gpr]; rfl,
      by rw [u₁.mem]; exact h.2⟩) fun s₁ ⟨a₁, x₁, b₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.Prf4.cbytes_ok hp (by decide) x₁ ⟨a₁, b₁⟩) fun s₂ ⟨a₂, _, b₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₃ u₃ => wp_nil
    (Q := fun s₃ => VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ m₁ s₃ ∧ s₃.gpr .rax = (0x80 : Byte).setWidth 64 ∧
      VG.Proof.MlKem.X86_64.Prf4.SB (VG.Proof.MlKem.X86_64.Prf4.sP b wl) s₃.mem fun k q => if q = 33 then 0x1f else VG.Proof.MlKem.X86_64.Prf4.NF b s₀ N₀ 4 k q)
    ⟨a₂.keep u₃.mem u₃.rd u₃.wr fun r hr => u₃.other r (VG.Proof.MlKem.X86_64.Prf4.rax_ncs r hr), by rw [u₃.gpr]; rfl,
      by rw [u₃.mem]; exact b₂⟩) fun s₃ ⟨a₃, x₃, b₃⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.Prf4.cbytes_ok hp (by decide) x₃ ⟨a₃, b₃⟩) fun s₄ ⟨a₄, _, b₄⟩ => ⟨a₄, fun k hk q hq => ?_⟩
  rw [b₄ k hk q hq]
  dsimp only [VG.Proof.MlKem.X86_64.Prf4.PF]
  rw [VG.Proof.MlKem.X86_64.Prf4.NF, VG.Proof.MlKem.X86_64.Prf4.GF]
  by_cases e1 : q < 32
  · rw [ifn (show ¬ q = 135 by bdd_omega), ifn (show ¬ q = 33 by bdd_omega), ifn (show ¬ (q = 32 ∧ k < 4) by bdd_omega),
      ifp (show q < 8 * 4 ∨ (q / 8 = 4 ∧ k < 0) by bdd_omega), ifp e1, VG.Proof.MlKem.X86_64.Prf4.sig_getD b s₀ e1]
  · rw [ifn e1]
    by_cases e2 : q = 32
    · rw [ifn (show ¬ q = 135 by bdd_omega), ifn (show ¬ q = 33 by bdd_omega), ifp ⟨e2, hk⟩, ifp e2]
    · rw [ifn e2, ifn (show ¬ (q = 32 ∧ k < 4) by bdd_omega), ifn (show ¬ (q < 8 * 4 ∨ (q / 8 = 4 ∧ k < 0)) by bdd_omega)]
      by_cases e3 : q = 33
      · rw [ifn (show ¬ q = 135 by bdd_omega), ifp e3, ifp e3]
      · rw [ifn e3, ifn e3]

/-! ## The setup -/

theorem setup_eq (N₀ wl : Nat) : setup N₀ wl =
    Impl.Sha3.X86_64.X4.rcTable .rbx (wl + 50) ++ (zero wl ++ (sigLanes wl ++ (nonces N₀ wl ++ (pads wl ++ args wl)))) := by
  simp only [setup, List.append_assoc]

theorem args_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {s : State}
    (he : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s) :
    WP isa (.block (args wl)) s fun s' => (s'.mem = s.mem ∧ s'.gpr .rdi = VG.Proof.MlKem.X86_64.Prf4.sP b wl ∧
      s'.gpr .rsi = VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 800 ∧ s'.gpr .rdx = VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 1600 ∧
      s'.gpr .rcx = VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 2368) ∧ Keep [.rdi, .rsi, .rdx, .rcx] s s' := by
  have := hp.small
  have e1 : b + BitVec.ofNat 64 (32 * (wl + 25)) = VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 800 := VG.Proof.MlKem.X86_64.Prf4.at_w b (by bdd_omega)
  have e2 : b + BitVec.ofNat 64 (32 * (wl + 50)) = VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 1600 := VG.Proof.MlKem.X86_64.Prf4.at_w b (by bdd_omega)
  have e3 : b + BitVec.ofNat 64 (32 * (wl + 74)) = VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 2368 := VG.Proof.MlKem.X86_64.Prf4.at_w b (by bdd_omega)
  refine WP.keep _ ?_ (by kernel_rfl)
  unfold args
  xrun [he.rbx hp, sx_ofNat (show 32 * wl < 2 ^ 31 by bdd_omega), sx_ofNat (show 32 * (wl + 25) < 2 ^ 31 by bdd_omega),
    sx_ofNat (show 32 * (wl + 50) < 2 ^ 31 by bdd_omega), sx_ofNat (show 32 * (wl + 74) < 2 ^ 31 by bdd_omega), e1, e2, e3]

/-- After the setup: the table, the padded inputs, and the arguments of the permutation. -/
structure SetupPost (b : Addr) (wl o m N₀ : Nat) (s₀ s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s
  tbl : VG.Proof.MlKem.X86_64.Prf4.Tbl (VG.Proof.MlKem.X86_64.Prf4.sP b wl) 24 s.mem
  lanes : Lanes4 s.mem (VG.Proof.MlKem.X86_64.Prf4.sP b wl) fun k => VG.Proof.MlKem.X86_64.Prf4.P0 (VG.Proof.MlKem.X86_64.Prf4.sig b s₀) (BitVec.ofNat 8 (N₀ + k))
  rdi : s.gpr .rdi = VG.Proof.MlKem.X86_64.Prf4.sP b wl
  rsi : s.gpr .rsi = VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 800
  rdx : s.gpr .rdx = VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 1600
  rcx : s.gpr .rcx = VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 2368

theorem setup_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {N₀ : Nat} (hN : N₀ + 4 ≤ 256) :
    WP isa (.block (setup N₀ wl)) s₀ (VG.Proof.MlKem.X86_64.Prf4.SetupPost b wl o m N₀ s₀) := by
  rw [VG.Proof.MlKem.X86_64.Prf4.setup_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.Prf4.rc_ok hp (BEnv.refl (b := b) (wl := wl) (o := o) (m := m) (s₀ := s₀))) fun s₁ ⟨e₁, t₁⟩ => ?_
  have a₁ : VG.Proof.MlKem.X86_64.Prf4.AI b wl o m s₀ s₁.mem s₁ := ⟨e₁, Frame.refl _ _⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.Prf4.zero_ok hp a₁) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.Prf4.sigLanes_ok hp h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.Prf4.nonces_ok hp hN h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.Prf4.pads_ok hp h₄) fun s₅ ⟨a₅, b₅⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.Prf4.args_ok hp a₅.env) fun s₆ ⟨⟨hm, hdi, hsi, hdx, hcx⟩, k⟩ => ?_
  refine ⟨⟨k.2.1.trans a₅.env.rd, k.2.2.trans a₅.env.wr,
      fun r hr => (k.gpr (by revert hr; decide +revert)).trans (a₅.env.cs r hr), by rw [hm]; exact a₅.env.frame⟩,
    fun r hr j hj => ?_, ?_, hdi, hsi, hdx, hcx⟩
  · rw [hm, a₅.fr.readW (Region.contains_self _ _) (by
      simpa using Offset.disjoint_base (VG.Proof.MlKem.X86_64.Prf4.sP b wl) (k := 800) (d := 32 * (50 + r) + 8 * j) (n := 8) (by bdd_omega)
        (by bdd_omega)) (by decide)]
    exact t₁ r hr j hj
  · rw [hm]
    exact lanes4_of_bytes fun k hk q hq => by rw [b₅ k hk q hq, VG.Proof.MlKem.X86_64.Prf4.byteOf_P0 (VG.Proof.MlKem.X86_64.Prf4.sig_length b s₀) _ hq]

/-! ## The permutation -/

theorem perm_ok {b : Addr} {wl o m N₀ : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {s : State}
    (h : VG.Proof.MlKem.X86_64.Prf4.SetupPost b wl o m N₀ s₀ s) :
    WP isa Impl.Sha3.X86_64.X4.permute4 s fun s' => VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s' ∧
      Lanes4 s'.mem (VG.Proof.MlKem.X86_64.Prf4.sP b wl) fun k => keccakF (VG.Proof.MlKem.X86_64.Prf4.P0 (VG.Proof.MlKem.X86_64.Prf4.sig b s₀) (BitVec.ofNat 8 (N₀ + k))) := by
  have := hp.small
  have pre : Pre4 s (VG.Proof.MlKem.X86_64.Prf4.sP b wl) (VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 800) (VG.Proof.MlKem.X86_64.Prf4.sP b wl + BitVec.ofNat 64 1600) :=
    ⟨fun i _ => VG.Proof.MlKem.X86_64.Prf4.in_w hp h.env (by bdd_omega),
      fun i _ => by rw [Offset.add_add]; exact VG.Proof.MlKem.X86_64.Prf4.in_w hp h.env (by bdd_omega),
      fun r _ => by rw [Offset.add_add]; exact VG.Proof.MlKem.X86_64.Prf4.in_w' hp h.env (by bdd_omega),
      Offset.base_disjoint _ (by bdd_omega) (by bdd_omega),
      Offset.base_disjoint _ (by bdd_omega) (by bdd_omega),
      Offset.disjoint _ (by bdd_omega) (by bdd_omega) (by bdd_omega),
      fun r hr k hk => by
        rw [la, Offset.add_add, show 1600 + (32 * r + 8 * k) = 32 * (50 + r) + 8 * k by bdd_omega]
        exact h.tbl r hr k hk⟩
  refine WP.mono (permute4_ok pre h.rdi h.rsi h.rdx (by rw [h.rcx, Offset.add_add (VG.Proof.MlKem.X86_64.Prf4.sP b wl) 1600 768]) h.lanes)
    fun s' ⟨hl, hf, hrd, hwr, _, hg⟩ => ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, fun r hr => ?_,
      h.env.frame.trans (hf.sub fun r hr => ⟨VG.Proof.MlKem.X86_64.Prf4.wR b wl, by simp, ?_⟩)⟩, hl⟩
  · rw [hg r (VG.Proof.MlKem.X86_64.Prf4.rax_ncs r hr) (by revert hr; decide +revert)]; exact h.env.cs r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by bdd_omega)
    · exact Offset.sub_base _ (by bdd_omega)

/-! ## The outputs -/

/-- During the copies: the first `I` lanes of state `K` copied, and all of the states before it. -/
structure EXI (b : Addr) (wl o m : Nat) (s₀ : State) (L : Nat → Spec.Sha3.State) (K I : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s
  lanes : Lanes4 s.mem (VG.Proof.MlKem.X86_64.Prf4.sP b wl) L
  out : ∀ k < m, ∀ j < 128, (k < K ∨ (k = K ∧ j < 8 * I)) →
    s.mem (b + BitVec.ofNat 64 o + BitVec.ofNat 64 (128 * k + j)) = byteOf (L k) j

theorem ext_step {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {L : Nat → Spec.Sha3.State}
    {K I : Nat} (hK : K < m) (hI : I < 16) {s : State} (h : VG.Proof.MlKem.X86_64.Prf4.EXI b wl o m s₀ L K I s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * (wl + I) + 8 * K))),
      .store (at_ .rbx (o + 128 * K + 8 * I)) .rax]) s (VG.Proof.MlKem.X86_64.Prf4.EXI b wl o m s₀ L K (I + 1)) := by
  have := hp.small
  have hm4 := hp.hm
  refine wp_movm (a := la (VG.Proof.MlKem.X86_64.Prf4.sP b wl) I K) (by rw [ea_at, h.env.rbx hp, la]; exact VG.Proof.MlKem.X86_64.Prf4.at_w b (by bdd_omega))
    (VG.Proof.MlKem.X86_64.Prf4.in_w' hp h.env (by bdd_omega)) fun s₁ u₁ => wp_store (a := b + BitVec.ofNat 64 o + BitVec.ofNat 64 (128 * K + 8 * I))
      (by rw [ea_at, u₁.other _ (by decide), h.env.rbx hp, Offset.add_add, Nat.add_assoc])
      (by rw [u₁.wr]; exact VG.Proof.MlKem.X86_64.Prf4.in_o hp h.env (by bdd_omega)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (b + BitVec.ofNat 64 o + BitVec.ofNat 64 (128 * K + 8 * I))
      (s.mem.readW (la (VG.Proof.MlKem.X86_64.Prf4.sP b wl) I K) 64) := by rw [m₂, u₁.mem, u₁.gpr]
  refine ⟨h.env.writeO hp (n := 8) (by bdd_omega) hm (r₂.trans u₁.rd) (w₂.trans u₁.wr)
      fun r hr => by rw [g₂, u₁.other r (VG.Proof.MlKem.X86_64.Prf4.rax_ncs r hr)], fun i hi k hk => ?_, fun k hk j hj hc => ?_⟩
  · rw [hm, Mem.readW_writeW_sep (((hp.dWO.sub_left (Offset.sub_base (VG.Proof.MlKem.X86_64.Prf4.sP b wl) (d := 32 * i + 8 * k) (n := 8)
      (k := 2368) (by bdd_omega))).sub_right (Offset.sub_base (b + BitVec.ofNat 64 o) (d := 128 * K + 8 * I) (n := 8)
      (k := 128 * m) (by bdd_omega))).sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
    exact h.lanes i hi k hk
  · rw [hm]
    by_cases hw : k = K ∧ 8 * I ≤ j ∧ j < 8 * I + 8
    · obtain ⟨rfl, h₁, h₂⟩ := hw
      rw [VG.Proof.MlKem.X86_64.S4.wb_in _ _ _ (by bdd_omega) (by bdd_omega) (by decide),
        show 8 * (128 * k + j - (128 * k + 8 * I)) = 8 * (j - 8 * I) by bdd_omega,
        byte_readW _ _ (by bdd_omega), la_byte _ (by bdd_omega), byte_of_lanes4 h.lanes (by bdd_omega) (by bdd_omega),
        show 8 * I + (j - 8 * I) = j by bdd_omega]
    · rw [VG.Proof.MlKem.X86_64.S4.wb_out _ _ _ (by bdd_omega) (by bdd_omega) (by bdd_omega)]
      exact h.out k hk j hj (by bdd_omega)

theorem extract_eq (m o wl : Nat) : extract m o wl = (List.range m).flatMap fun K => (List.range 16).flatMap fun I =>
    [.mov .rax (.mem (at_ .rbx (32 * (wl + I) + 8 * K))), .store (at_ .rbx (o + 128 * K + 8 * I)) .rax] := rfl

theorem extract_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {L : Nat → Spec.Sha3.State}
    {s : State} (he : VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s) (hl : Lanes4 s.mem (VG.Proof.MlKem.X86_64.Prf4.sP b wl) L) :
    WP isa (.block (extract m o wl)) s fun s' => VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s' ∧
      ∀ k < m, ∀ j < 128, s'.mem (b + BitVec.ofNat 64 o + BitVec.ofNat 64 (128 * k + j)) = byteOf (L k) j := by
  rw [VG.Proof.MlKem.X86_64.Prf4.extract_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => VG.Proof.MlKem.X86_64.Prf4.EXI b wl o m s₀ L K 0 s) (fun K s hK h => ?_) m
    (Nat.le_refl _) s ⟨he, hl, fun _ _ _ _ hc => absurd hc (by bdd_omega)⟩)
    fun s' h' => ⟨h'.env, fun k hk j hj => h'.out k hk j hj (by bdd_omega)⟩
  exact WP.mono (wp_range_flatMap (M := isa) (fun I s => VG.Proof.MlKem.X86_64.Prf4.EXI b wl o m s₀ L K I s)
    (fun I s hI h => VG.Proof.MlKem.X86_64.Prf4.ext_step hp hK hI h) 16 (Nat.le_refl _) s h)
    fun s' h' => ⟨h'.env, h'.lanes, fun k hk j hj hc => h'.out k hk j hj (by bdd_omega)⟩

/-! ## The whole -/

/-- `batch N₀ m o wl`: `PRF₂(σ, N₀ + k)` to `scratch + o + 128 k` for each `k < m`. -/
theorem batch_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s₀) {N₀ : Nat} (hN : N₀ + 4 ≤ 256) :
    WP isa (batch N₀ m o wl) s₀ fun s => VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o m s₀ s ∧
      ∀ k < m, bytesAt s.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 = prf 2 (VG.Proof.MlKem.X86_64.Prf4.sig b s₀) (BitVec.ofNat 8 (N₀ + k)) := by
  unfold batch
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Prf4.setup_ok hp hN) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Prf4.perm_ok hp h₁) fun s₂ ⟨e₂, l₂⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.Prf4.extract_ok hp e₂ l₂) fun s₃ ⟨e₃, o₃⟩ => WP.mono (VG.Proof.MlKem.X86_64.S4.vz_ok s₃) fun s₄ ⟨hm, k⟩ =>
    ⟨⟨k.2.1.trans e₃.rd, k.2.2.trans e₃.wr, fun r hr => (k.gpr List.not_mem_nil).trans (e₃.cs r hr),
      by rw [hm]; exact e₃.frame⟩, fun k hk => ?_⟩
  rw [hm]
  refine VG.Proof.MlKem.X86_64.Prf4.bytes_prf (VG.Proof.MlKem.X86_64.Prf4.sig_length b s₀) fun j hj => ?_
  have e := o₃ k hk j hj
  rw [Offset.add_add, ← Nat.add_assoc] at e
  rw [Offset.add_add]
  exact e

/-! ## Constant time -/

/-- `batch` leaks only the address in `rbx`: the immediates (the indices
and offsets) are the same in every run, and no address or branch depends on
the data. -/
theorem batch_tr {P : State → State → Prop} (hP : ∀ x y, P x y → x.gpr .rbx = y.gpr .rbx) (N₀ o wl : Nat)
    {m : Nat} (hm : m ≤ 4) : RelCT isa P (batch N₀ m o wl) fun x y => x.gpr .rbx = y.gpr .rbx := by
  have hx : ((taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (extract m o wl ++ ([.vop .vzeroupper] : List Instr)))
      (.block [])).map fun τ' => (RegSet.ofList [Reg.rbx]).subset τ'.regs) = some true := by
    rcases (by bdd_omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with rfl | rfl | rfl | rfl | rfl <;> kernel_rfl
  unfold batch
  refine RelCT.seq (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx])
    (fun x y h => X86_64.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP x y h) [.rbx, .rdi, .rsi, .rdx, .rcx]
    (hc := .block []) (by kernel_rfl)) ?_
  refine RelCT.seq (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx, .rdi, .rsi, .rdx, .rcx])
    (fun x y h => X86_64.Taint.agree_ofRegs h) [.rbx] (by taint_decide)) ?_
  exact RelCT.mono (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx]) (fun x y h => X86_64.Taint.agree_ofRegs h)
    [.rbx] hx) (fun _ _ h => h) fun _ _ h => h _ (List.mem_singleton_self _)

end VG.Proof.MlKem.X86_64.Prf4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.TopBase`. -/
section

/-!
# ML-KEM-768 on x86-64: entry and exit of the top-level functions

What holds of the state of a top-level function throughout (`Top`): the
permissions and the stack pointer of entry, its pointers in their registers,
its caller's callee-saved registers saved in `scratch`, and the return
address; its buffers make a layout (`Lay.of`). The saves (`stores_read`), the
return (`topEpi_ok`), the branch on the results of `SampleNTT` (`ifOk_ok`,
`ifOk_tr`), and sequences of pieces indexed by a number (`seqR_ok`,
`seqR_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Layouts from the facts of a contract -/

theorem pairwise_sym {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with e | ha'
    · rcases List.mem_cons.mp hb with e' | hb'
      · exact absurd (e.trans e'.symm) hne
      · rw [e]; exact h.1 _ hb'
    · rcases List.mem_cons.mp hb with e' | hb'
      · rw [e']; exact hs _ _ (h.1 _ ha')
      · exact VG.Proof.MlKem.X86_64.pairwise_sym hs h.2 ha' hb' hne

theorem Lay.of {rbs wbs : List (Reg × Nat)} {s : State} (small : ∀ b ∈ rbs ++ wbs, b.2 < 2 ^ 32)
    (pw : (rbs ++ wbs).Pairwise fun b b' => (b.1 ∈ VG.Proof.MlKem.X86_64.wRegs ∨ b'.1 ∈ VG.Proof.MlKem.X86_64.wRegs) →
      Region.Disjoint ⟨s.gpr b.1, b.2⟩ ⟨s.gpr b'.1, b'.2⟩)
    (stk : ∀ b ∈ rbs ++ wbs, (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr b.1, b.2⟩)
    (nw : ∀ b ∈ rbs ++ wbs, (s.gpr b.1).toNat + b.2 ≤ 2 ^ 64)
    (rd : ∀ b ∈ rbs ++ wbs, InRegions (s.rd ++ s.wr) (s.gpr b.1) b.2)
    (wr : ∀ b ∈ wbs, InRegions s.wr (s.gpr b.1) b.2)
    (ret : ∀ b ∈ rbs ++ wbs, (retR s).Disjoint ⟨s.gpr b.1, b.2⟩) : VG.Proof.MlKem.X86_64.Lay rbs wbs s := by
  exact ⟨small, fun b hb b' hb' hne hw => VG.Proof.MlKem.X86_64.pairwise_sym (fun _ _ h hw => (h hw.symm).symm) pw hb hb'
    (fun e => hne (by rw [e])) hw, stk, nw, rd, wr, ret⟩

theorem fa2 {α : Type} {p : α → Prop} {a b : α} (ha : p a) (hb : p b) : ∀ x ∈ [a, b], p x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> with_reducible assumption

theorem fa3 {α : Type} {p : α → Prop} {a b c : α} (ha : p a) (hb : p b) (hc : p c) : ∀ x ∈ [a, b, c], p x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> with_reducible assumption

theorem fa4 {α : Type} {p : α → Prop} {a b c d : α} (ha : p a) (hb : p b) (hc : p c) (hd : p d) :
    ∀ x ∈ [a, b, c, d], p x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem fa5 {α : Type} {p : α → Prop} {a b c d e : α} (ha : p a) (hb : p b) (hc : p c) (hd : p d) (he : p e) :
    ∀ x ∈ [a, b, c, d, e], p x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem pw4 {α : Type} {R : α → α → Prop} {a b c d : α} (hab : R a b) (hac : R a c) (had : R a d) (hbc : R b c)
    (hbd : R b d) (hcd : R c d) : [a, b, c, d].Pairwise R := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, false_implies, implies_true, and_true]
  exact ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩

theorem pw5 {α : Type} {R : α → α → Prop} {a b c d e : α} (hab : R a b) (hac : R a c) (had : R a d) (hae : R a e)
    (hbc : R b c) (hbd : R b d) (hbe : R b e) (hcd : R c d) (hce : R c e) (hde : R d e) :
    [a, b, c, d, e].Pairwise R := by
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, false_implies, implies_true, and_true]
  exact ⟨⟨hab, hac, had, hae⟩, ⟨hbc, hbd, hbe⟩, ⟨hcd, hce⟩, hde⟩

/-! ## The state of a top-level function -/

/-- The register saved at `scratch + 840 + 8k`. -/
abbrev savedReg (k : Nat) : Reg := savedRegs.getD k .rbx

/-- What holds throughout a top-level function entered in `σ`, which keeps
the pointers of `m` (a register, and the register of entry it holds). -/
structure Top (m : List (Reg × Reg)) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  regs : ∀ p ∈ m, s.gpr p.1 = σ.gpr p.2
  saved : ∀ k < 6, s.mem.readW (VG.Proof.MlKem.X86_64.pa s (sc (oSV + 8 * k))) 64 = σ.gpr (VG.Proof.MlKem.X86_64.savedReg k)
  ret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64

/-- The saved registers and the return address are apart from the regions `ws`. -/
def topChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) : Bool :=
  (List.range 6).all (fun k => VG.Proof.MlKem.X86_64.keepB bs ws (sc (oSV + 8 * k)) 8) && ws.all fun w => VG.Proof.MlKem.X86_64.inB bs w.1 w.2

theorem Top.step {m : List (Reg × Reg)} {σ s s' : State} {rbs wbs : List (Reg × Nat)} (h : VG.Proof.MlKem.X86_64.Top m σ s)
    (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) {ws : List (Ptr × Nat)} (hP : VG.Proof.MlKem.X86_64.PPostB s s' ws) (hm : ∀ p ∈ m, p.1 ∈ VG.Proof.MlKem.X86_64.bases)
    (hc : VG.Proof.MlKem.X86_64.topChk (rbs ++ wbs) ws = true) : VG.Proof.MlKem.X86_64.Top m σ s' := by
  simp only [VG.Proof.MlKem.X86_64.topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.rsp.trans h.rsp, fun p hp => (hP.bs _ (hm p hp)).trans (h.regs p hp),
    fun k hk => ?_, ?_⟩
  · rw [L.keepW hP (hc.1 k hk)]; exact h.saved k hk
  · have := L.keepRet hP hc.2
    rw [h.rsp] at this
    rw [this, h.ret]

/-! ## Saving the registers -/

theorem readW_writeW_slot (m : Mem) (a : Addr) {x y : Nat} (v : BitVec 64) (hxy : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (m.writeW (a + BitVec.ofNat 64 y) v).readW (a + BitVec.ofNat 64 x) 64 = m.readW (a + BitVec.ofNat 64 x) 64 := by
  refine Mem.readW_writeW_sep ?_ (by decide)
  rcases hxy with h | h
  · exact (off_disj (p := a) h (by omega)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  · exact (off_disj (p := a) h (by omega)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- The six stores of `topPro`: each slot holds its register. -/
theorem stores_read (m : Mem) (a : Addr) (v : Nat → BitVec 64) : ∀ k < 6,
    ((((((m.writeW (a + BitVec.ofNat 64 840) (v 0)).writeW (a + BitVec.ofNat 64 848) (v 1)).writeW
      (a + BitVec.ofNat 64 856) (v 2)).writeW (a + BitVec.ofNat 64 864) (v 3)).writeW (a + BitVec.ofNat 64 872)
      (v 4)).writeW (a + BitVec.ofNat 64 880) (v 5)).readW (a + BitVec.ofNat 64 (oSV + 8 * k)) 64 = v k := by
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := omega) only [oSV, Nat.reduceMul, Nat.reduceAdd, VG.Proof.MlKem.X86_64.readW_writeW_slot, Mem.readW_writeW_self64]

/-! ## The return -/

theorem topEpi_eq : topEpi = [.mov32 .rax (.reg .r15), .mov .r15 (.mem (at_ .rbx 880)), .mov .r14 (.mem (at_ .rbx 872)),
    .mov .r13 (.mem (at_ .rbx 864)), .mov .r12 (.mem (at_ .rbx 856)), .mov .rbp (.mem (at_ .rbx 848)),
    .mov .rbx (.mem (at_ .rbx 840))] := rfl

theorem topEpi_ok {m : List (Reg × Reg)} {σ s : State} (h : VG.Proof.MlKem.X86_64.Top m σ s)
    (hin : ∀ k < 6, InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.pa s (sc (oSV + 8 * k))) 8) :
    WP isa (.block topEpi) s fun s' => (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32 ∧
      gprPreserved σ s' ∧ s'.mem = s.mem := by
  have e : ∀ k < 6, s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (840 + 8 * k)) 64 = σ.gpr (VG.Proof.MlKem.X86_64.savedReg k) :=
    fun k hk => h.saved k hk
  have i : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (840 + 8 * k)) 8 := hin
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide); have e5 := e 5 (by decide)
  have i0 := i 0 (by decide); have i1 := i 1 (by decide); have i2 := i 2 (by decide)
  have i3 := i 3 (by decide); have i4 := i 4 (by decide); have i5 := i 5 (by decide)
  rw [show VG.Proof.MlKem.X86_64.savedReg 0 = .rbx from rfl] at e0; rw [show VG.Proof.MlKem.X86_64.savedReg 1 = .rbp from rfl] at e1
  rw [show VG.Proof.MlKem.X86_64.savedReg 2 = .r12 from rfl] at e2; rw [show VG.Proof.MlKem.X86_64.savedReg 3 = .r13 from rfl] at e3
  rw [show VG.Proof.MlKem.X86_64.savedReg 4 = .r14 from rfl] at e4; rw [show VG.Proof.MlKem.X86_64.savedReg 5 = .r15 from rfl] at e5
  simp only [Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 i0 i1 i2 i3 i4 i5
  rw [VG.Proof.MlKem.X86_64.topEpi_eq]
  refine WP.mono (WP.keep [.rax, .r15, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' =>
    s'.gpr .rax = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32) ∧ s'.gpr .r15 = σ.gpr .r15 ∧
    s'.gpr .r14 = σ.gpr .r14 ∧ s'.gpr .r13 = σ.gpr .r13 ∧ s'.gpr .r12 = σ.gpr .r12 ∧ s'.gpr .rbp = σ.gpr .rbp ∧
    s'.gpr .rbx = σ.gpr .rbx ∧ s'.mem = s.mem) (by xrun [i0, i1, i2, i3, i4, i5, e0, e1, e2, e3, e4, e5]) (by decide))
    fun s' ⟨⟨hax, h15, h14, h13, h12, hbp, hbx, hm⟩, k⟩ => ⟨?_, ⟨fun r hr => ?_, ?_⟩, hm⟩
  · rw [hax]; apply BitVec.eq_of_toNat_eq; simp
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, by rw [k.gpr (by decide), h.rsp], h12, h13, h14, h15]
  · rw [hm]; exact h.ret

/-! ## The branch on the results of `SampleNTT` -/

/-- A block that writes only `r15`, with its old value, and flags. -/
theorem post_of_keep15 {s s' : State} (k : Keep [.r15] s s') (h15 : s'.gpr .r15 = s.gpr .r15)
    (hm : s'.mem = s.mem) (ws : List (Ptr × Nat)) : VG.Proof.MlKem.X86_64.PPost s s' ws :=
  ⟨k.2.1, k.2.2, fun r _ => by
    by_cases e : r = .r15
    · rw [e, h15]
    · exact k.gpr (by simpa using e), by rw [hm]; exact Frame.refl _ _⟩

theorem test15_ok (s : State) :
    WP isa (.block [.alu32 .test .r15 (.reg .r15)]) s fun s₁ => VG.Proof.MlKem.X86_64.PPost s s₁ [] ∧
      s₁.zf = some ((s.gpr .r15).setWidth 32 == 0) :=
  WP.mono (WP.keep [.r15] (Q := fun s₁ => s₁.mem = s.mem ∧ s₁.gpr .r15 = s.gpr .r15 ∧
      s₁.zf = some (((s.gpr .r15).setWidth 32 &&& (s.gpr .r15).setWidth 32) == 0)) (by xrun) (by decide))
    fun _ ⟨⟨hm, h15, hz⟩, k⟩ => ⟨VG.Proof.MlKem.X86_64.post_of_keep15 k h15 hm [], by rw [hz, BitVec.and_self]⟩

theorem ifOk_ok {c : Prog isa} {s : State} {Q : State → Prop}
    (ht : ∀ s₁, VG.Proof.MlKem.X86_64.PPost s s₁ [] → (s.gpr .r15).setWidth 32 ≠ 0 → WP isa c s₁ Q)
    (he : ∀ s₁, VG.Proof.MlKem.X86_64.PPost s s₁ [] → (s.gpr .r15).setWidth 32 = 0 → Q s₁) : WP isa (ifOk c) s Q := by
  unfold ifOk
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.test15_ok s) fun s₁ ⟨hP, hz⟩ => ?_)
  refine WP.ite (M := isa) (!((s.gpr .r15).setWidth 32 == 0))
    (show s₁.zf.map (!·) = _ by rw [hz]; rfl) (fun hb => ?_) fun hb => ?_
  · exact ht s₁ hP (by simpa using hb)
  · exact WP.block_nil (he s₁ hP (by simpa using hb))

theorem ifOk_tr {c : Prog isa} {P Q : State → State → Prop}
    (he : ∀ x y, P x y → (x.gpr .r15).setWidth 32 = (y.gpr .r15).setWidth 32)
    (ht : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ VG.Proof.MlKem.X86_64.PPost x₀ x [] ∧ VG.Proof.MlKem.X86_64.PPost y₀ y [] ∧
      (x₀.gpr .r15).setWidth 32 ≠ 0) c Q)
    (hq : ∀ x y, (∃ x₀ y₀, P x₀ y₀ ∧ VG.Proof.MlKem.X86_64.PPost x₀ x [] ∧ VG.Proof.MlKem.X86_64.PPost y₀ y [] ∧ (x₀.gpr .r15).setWidth 32 = 0) → Q x y) :
    RelCT isa P (ifOk c) Q := by
  unfold ifOk
  refine RelCT.seq (RelCT.postDep (VG.Proof.MlKem.X86_64.block_nomem_tr fun i hi s => by
      simp only [List.mem_singleton] at hi; subst hi; rfl)
    (F := fun x x₁ => VG.Proof.MlKem.X86_64.PPost x x₁ [] ∧ x₁.zf = some ((x.gpr .r15).setWidth 32 == 0))
    (fun x y _ => ⟨VG.Proof.MlKem.X86_64.test15_ok x, VG.Proof.MlKem.X86_64.test15_ok y⟩) (Q := fun x₁ y₁ => ∃ x₀ y₀, P x₀ y₀ ∧
      (VG.Proof.MlKem.X86_64.PPost x₀ x₁ [] ∧ x₁.zf = some ((x₀.gpr .r15).setWidth 32 == 0)) ∧
      (VG.Proof.MlKem.X86_64.PPost y₀ y₁ [] ∧ y₁.zf = some ((y₀.gpr .r15).setWidth 32 == 0)))
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.ite ?_ ?_ ?_)
  · rintro x₁ y₁ ⟨x₀, y₀, hp, ⟨_, hx⟩, ⟨_, hy⟩⟩
    show x₁.zf.map (!·) = y₁.zf.map (!·)
    rw [hx, hy, he x₀ y₀ hp]
  · refine RelCT.mono ht (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩) fun _ _ h => h
    have hc' : x₁.zf.map (!·) = some true := hc
    rw [hx] at hc'
    simpa using hc'
  · refine RelCT.mono VG.Proof.MlKem.X86_64.nil_tr (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun x y h => hq x y h
    have hc' : x₁.zf.map (!·) = some false := hc
    rw [hx] at hc'
    simpa using hc'

/-! ## Sequences -/

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [seqR]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega) s hs) fun s₁ h₁ => ?_)
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact VG.Proof.MlKem.X86_64.seqR_ok n (a + 1) (fun k hk hk' => h k (by omega) (by omega)) s₁ h₁

theorem seqR_tr {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (seqR f a n) (R (a + n))
  | 0, _, _ => VG.Proof.MlKem.X86_64.nil_tr
  | n + 1, a, h => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega)) (VG.Proof.MlKem.X86_64.seqR_tr n (a + 1) fun k hk hk' => h k (by omega) (by omega))

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.Prfs`. -/
section

/-!
# ML-KEM on x86-64: several outputs of `PRF₂`

In a layout: `PRF₂(σ, N₀ + i)` to `scratch + o + 128 i` for each `i < n`, with
`σ` at `G + 32` (`PrfsPost`), one at a time (`prfsScalar_ok`, `prfsScalar_tr`)
or four at a time with AVX2, but for the first `prfsLead n`, one at a time
(`prfsAvx2_ok`, `prfsAvx2_tr`), whichever implementation of
`vg_mlkem_sample_ntt4` the top-level functions call goes with
(`Callee4.prfs`). Both write within `prfsW` and need what `prfsChk` checks of
the layout.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {rbs wbs : List (Reg × Nat)}

/-! ## Properties of every instruction, piece by piece -/

theorem ctlOk_seq {a b : Prog isa} (ha : ctlOk a = true) (hb : ctlOk b = true) : ctlOk (.seq a b) = true := by
  simp only [ctlOk, ha, hb, Bool.and_self, Bool.or_true]

theorem ctlOk_call {n : String} {c : Prog isa} (h : ctlOk c = true) : ctlOk (.call n c) = true := h

theorem all_call {p : Instr → Bool} {n : String} {c : Prog isa} (h : c.all p = true) :
    (Code.call n c : Prog isa).all p = true := h

theorem ctlOk_ite {c : Cond} {t e : Prog isa} (ht : ctlOk t = true) (he : ctlOk e = true) :
    ctlOk (.ite c t e) = true := by
  simp only [ctlOk, ht, he, Bool.and_self]

theorem all_ite {p : Instr → Bool} {c : Cond} {t e : Prog isa} (ht : t.all p = true) (he : e.all p = true) :
    (Code.ite c t e : Prog isa).all p = true := by
  simp only [Code.all, ht, he, Bool.and_self]

theorem all_seq {p : Instr → Bool} {a b : Prog isa} (ha : a.all p = true) (hb : b.all p = true) :
    (Code.seq a b : Prog isa).all p = true := by
  simp only [Code.all, ha, hb, Bool.and_self]


/-! ## What a piece writes, weakened -/

/-- `PPost` for larger regions. -/
theorem PPost.weaken {s s' : State} {ws ws' : List (Ptr × Nat)} (h : VG.Proof.MlKem.X86_64.PPost s s' ws)
    (hs : ∀ w ∈ ws, ∃ w' ∈ ws', Region.Sub (VG.Proof.MlKem.X86_64.toR s w) (VG.Proof.MlKem.X86_64.toR s w')) : VG.Proof.MlKem.X86_64.PPost s s' ws' :=
  ⟨h.rd, h.wr, h.cs, h.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      obtain ⟨w', hw', hsub⟩ := hs w hw
      exact ⟨VG.Proof.MlKem.X86_64.toR s w', List.mem_append_left _ (List.mem_map_of_mem hw'), hsub⟩
    · exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩⟩

/-! ## One output -/

/-- What `prf1 N out` writes. -/
abbrev prf1W (out : Ptr) : List (Ptr × Nat) := [(sc oNB, 1), (sc 0, 200), (sc 200, 640), (out, 128)]

def prf1Chk (bs wbs : List (Reg × Nat)) (out : Ptr) : Bool :=
  VG.Proof.MlKem.X86_64.inB bs (sc oNB) 1 && VG.Proof.MlKem.X86_64.inB wbs (sc oNB) 1 && VG.Proof.MlKem.X86_64.hashChk bs wbs [(sigP, 32), (sc oNB, 1)] 136 out 128 &&
    VG.Proof.MlKem.X86_64.keepB bs [(sc oNB, 1)] sigP 32

theorem prf1Chk_spec {bs wbs : List (Reg × Nat)} {out : Ptr} (h : VG.Proof.MlKem.X86_64.prf1Chk bs wbs out = true) :
    VG.Proof.MlKem.X86_64.inB bs (sc oNB) 1 = true ∧ VG.Proof.MlKem.X86_64.inB wbs (sc oNB) 1 = true ∧
      VG.Proof.MlKem.X86_64.hashChk bs wbs [(sigP, 32), (sc oNB, 1)] 136 out 128 = true ∧ VG.Proof.MlKem.X86_64.keepB bs [(sc oNB, 1)] sigP 32 = true := by
  simp only [VG.Proof.MlKem.X86_64.prf1Chk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  exact ⟨h0, h1, h2, h3⟩

theorem prf1_ok {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {N : Nat} (hN : N < 256)
    {out : Ptr} (hc : VG.Proof.MlKem.X86_64.prf1Chk (rbs ++ wbs) wbs out = true) :
    WP isa (prf1 N out) s fun s' => VG.Proof.MlKem.X86_64.PPost s s' (VG.Proof.MlKem.X86_64.prf1W out) ∧
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s out) 128 = prf 2 (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s sigP) 32) (BitVec.ofNat 8 N) := by
  obtain ⟨_, hNB, hh, hk⟩ := VG.Proof.MlKem.X86_64.prf1Chk_spec hc
  have hocs : out.1 ∈ calleeSaved := (VG.Proof.MlKem.X86_64.hashChk_spec hh).2.2.2.2.2
  unfold prf1
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.setB_okL L (by decide) hN hNB) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have L₁ := L.post hP₁.b hcs
  refine WP.mono (VG.Proof.MlKem.X86_64.hash_ok hcs hh (by decide) L₁) fun s₂ ⟨hP₂, ho₂⟩ =>
    ⟨PPost.app hP₁ hP₂ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro w (rfl | rfl | rfl) <;>
      first | decide | exact hocs), ?_⟩
  have e1 : VG.Proof.MlKem.X86_64.pa s₁ (sc oNB) = VG.Proof.MlKem.X86_64.pa s (sc oNB) := hP₁.pa VG.Proof.MlKem.X86_64.rbx_cs
  have eo : VG.Proof.MlKem.X86_64.pa s₁ out = VG.Proof.MlKem.X86_64.pa s out := hP₁.pa hocs
  have hσ : bytesAt s₁.mem (VG.Proof.MlKem.X86_64.pa s₁ sigP) 32 = bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s sigP) 32 := L.keepBytes hP₁.b hk
  rw [← eo, ho₂, VG.Proof.MlKem.X86_64.prf_pieces (by rw [e1]; exact hb₁), hσ, VG.Proof.MlKem.X86_64.shake31]
  exact (prf_eq 2 _ _).symm

theorem setNB_taint (N : Nat) :
    (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc oNB) N)) (.block [])).isSome = true := by
  kernel_rfl

theorem prf1_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {N : Nat} (hN : N < 256) {out : Ptr}
    (hc : VG.Proof.MlKem.X86_64.prf1Chk (rbs ++ wbs) wbs out = true) : RelCT isa (VG.Proof.MlKem.X86_64.LRel rbs wbs) (prf1 N out) (VG.Proof.MlKem.X86_64.LRel rbs wbs) := by
  obtain ⟨hin, hNB, hh, _⟩ := VG.Proof.MlKem.X86_64.prf1Chk_spec hc
  unfold prf1
  exact RelCT.seq (LRel.step hcs (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq hin) (VG.Proof.MlKem.X86_64.setNB_taint N))
    fun x Lx => WP.mono (VG.Proof.MlKem.X86_64.setB_okL Lx (by decide) hN hNB) fun _ h => ⟨_, h.1⟩)
    (LRel.step hcs (VG.Proof.MlKem.X86_64.hash_tr hcs hh (by decide)) fun x Lx => WP.mono (VG.Proof.MlKem.X86_64.hash_ok hcs hh (by decide) Lx) fun _ h => ⟨_, h.1⟩)

theorem prf1_ctl (N : Nat) (out : Ptr) : ctlOk (prf1 N out) = true := by kernel_rfl

theorem prf1_sp (N : Nat) (out : Ptr) : (prf1 N out).all (fun i => !isa.writesSp i) = true := by kernel_rfl

/-! ## Several outputs -/

/-- What `prfs N₀ n o wl` writes, of either implementation: the index `N`,
the Keccak state and the sponge functions' working space, 2368 bytes of
working space from lane `wl`, and the outputs. -/
abbrev prfsW (n o wl : Nat) : List (Ptr × Nat) :=
  [(sc oNB, 1), (sc 0, 200), (sc 200, 640), (sc (32 * wl), 2368), (sc o, 128 * n)]

/-- What `prfs N₀ n o wl` needs of the layout, of either implementation:
for each output, what computing it on its own needs, and that this keeps `σ`
and the outputs before it; and that the working space, the outputs and `σ`
are apart. -/
def prfsChk (bs wbs : List (Reg × Nat)) (n o wl : Nat) : Bool :=
  (List.range n).all (fun i => VG.Proof.MlKem.X86_64.prf1Chk bs wbs (sc (o + 128 * i)) && VG.Proof.MlKem.X86_64.keepB bs (VG.Proof.MlKem.X86_64.prf1W (sc (o + 128 * i))) sigP 32 &&
    (List.range i).all fun j => VG.Proof.MlKem.X86_64.keepB bs (VG.Proof.MlKem.X86_64.prf1W (sc (o + 128 * i))) (sc (o + 128 * j)) 128) &&
  VG.Proof.MlKem.X86_64.wrOk bs wbs (sc (32 * wl)) 2368 && VG.Proof.MlKem.X86_64.wrOk bs wbs (sc o) (128 * n) && VG.Proof.MlKem.X86_64.rdOk bs sigP 32 &&
  VG.Proof.MlKem.X86_64.sepB bs (sc (32 * wl)) 2368 (sc o) (128 * n) && VG.Proof.MlKem.X86_64.sepB bs (sc (32 * wl)) 2368 sigP 32 &&
  VG.Proof.MlKem.X86_64.sepB bs (sc o) (128 * n) sigP 32 && decide (32 * wl + 2368 < 2 ^ 31)

theorem prfsChk_spec {bs wbs : List (Reg × Nat)} {n o wl : Nat} (h : VG.Proof.MlKem.X86_64.prfsChk bs wbs n o wl = true) :
    (∀ i < n, VG.Proof.MlKem.X86_64.prf1Chk bs wbs (sc (o + 128 * i)) = true ∧ VG.Proof.MlKem.X86_64.keepB bs (VG.Proof.MlKem.X86_64.prf1W (sc (o + 128 * i))) sigP 32 = true ∧
      ∀ j < i, VG.Proof.MlKem.X86_64.keepB bs (VG.Proof.MlKem.X86_64.prf1W (sc (o + 128 * i))) (sc (o + 128 * j)) 128 = true) ∧
    VG.Proof.MlKem.X86_64.wrOk bs wbs (sc (32 * wl)) 2368 = true ∧ VG.Proof.MlKem.X86_64.wrOk bs wbs (sc o) (128 * n) = true ∧ VG.Proof.MlKem.X86_64.rdOk bs sigP 32 = true ∧
    VG.Proof.MlKem.X86_64.sepB bs (sc (32 * wl)) 2368 (sc o) (128 * n) = true ∧ VG.Proof.MlKem.X86_64.sepB bs (sc (32 * wl)) 2368 sigP 32 = true ∧
    VG.Proof.MlKem.X86_64.sepB bs (sc o) (128 * n) sigP 32 = true ∧ 32 * wl + 2368 < 2 ^ 31 := by
  simp only [VG.Proof.MlKem.X86_64.prfsChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨fun i hi => ⟨(h0 i hi).1.1, (h0 i hi).1.2, (h0 i hi).2⟩, h1, h2, h3, h4, h5, h6, h7⟩

/-- What `prfs N₀ n o wl` leaves, from `s`. -/
def PrfsPost (s : State) (N₀ n o wl : Nat) (s' : State) : Prop :=
  VG.Proof.MlKem.X86_64.PPost s s' (VG.Proof.MlKem.X86_64.prfsW n o wl) ∧
    ∀ i < n, bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s (sc (o + 128 * i))) 128 =
      prf 2 (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s sigP) 32) (BitVec.ofNat 8 (N₀ + i))

/-! ## One at a time -/

/-- Output `i` lies within the outputs. -/
theorem out_sub (s : State) {n o i : Nat} (hi : i < n) :
    Region.Sub (VG.Proof.MlKem.X86_64.toR s (sc (o + 128 * i), 128)) (VG.Proof.MlKem.X86_64.toR s (sc o, 128 * n)) :=
  show Region.Sub ⟨s.gpr .rbx + BitVec.ofNat 64 (o + 128 * i), 128⟩ ⟨s.gpr .rbx + BitVec.ofNat 64 o, 128 * n⟩ from
    Offset.sub _ (by omega) (by omega)

/-- After the first `k` outputs. -/
structure ScInv (s : State) (N₀ n o wl k : Nat) (s' : State) : Prop where
  post : VG.Proof.MlKem.X86_64.PPost s s' (VG.Proof.MlKem.X86_64.prfsW n o wl)
  sig : bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s' sigP) 32 = bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s sigP) 32
  outs : ∀ j < k, bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s (sc (o + 128 * j))) 128 =
    prf 2 (bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s sigP) 32) (BitVec.ofNat 8 (N₀ + j))

/-- The first `r` of `n` outputs, one at a time. -/
theorem prfsScalar_lead {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {N₀ r n o wl : Nat}
    (hN : N₀ + r ≤ 256) (hr : r ≤ n)
    (hs : ∀ i < r, VG.Proof.MlKem.X86_64.prf1Chk (rbs ++ wbs) wbs (sc (o + 128 * i)) = true ∧
      VG.Proof.MlKem.X86_64.keepB (rbs ++ wbs) (VG.Proof.MlKem.X86_64.prf1W (sc (o + 128 * i))) sigP 32 = true ∧
      ∀ j < i, VG.Proof.MlKem.X86_64.keepB (rbs ++ wbs) (VG.Proof.MlKem.X86_64.prf1W (sc (o + 128 * i))) (sc (o + 128 * j)) 128 = true) :
    WP isa (prfsScalar N₀ r o wl) s (VG.Proof.MlKem.X86_64.ScInv s N₀ n o wl r) := by
  have h := VG.Proof.MlKem.X86_64.seqR_ok (f := fun i => prf1 (N₀ + i) (sc (o + 128 * i))) (I := VG.Proof.MlKem.X86_64.ScInv s N₀ n o wl) r 0
    (fun k _ hk s₁ h₁ => by
      obtain ⟨c1, cs, cj⟩ := hs k (by omega)
      have L₁ := L.post h₁.post.b hcs
      refine WP.mono (VG.Proof.MlKem.X86_64.prf1_ok L₁ hcs (by omega) c1) fun s₂ ⟨hP, hb⟩ => ?_
      have e₁ : ∀ x, VG.Proof.MlKem.X86_64.pa s₁ (sc x) = VG.Proof.MlKem.X86_64.pa s (sc x) := fun x => h₁.post.pa VG.Proof.MlKem.X86_64.rbx_cs
      refine ⟨PPost.trans h₁.post (hP.weaken fun w hw => ?_) (fun w hw => by
          simp only [VG.Proof.MlKem.X86_64.prfsW, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact VG.Proof.MlKem.X86_64.rbx_cs) (fun w hw => hw) (fun w hw => hw),
        by rw [L₁.keepBytes hP.b cs]; exact h₁.sig, fun j hj => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
        · exact ⟨_, by simp, VG.Proof.MlKem.X86_64.out_sub s₁ (o := o) (show k < n by omega)⟩
      · rcases (by omega : j < k ∨ j = k) with hj | rfl
        · rw [← e₁, ← hP.pa VG.Proof.MlKem.X86_64.rbx_cs, L₁.keepBytes hP.b (cj j hj), e₁]; exact h₁.outs j hj
        · rw [← e₁, hb, h₁.sig])
    s ⟨Post.refl _ _, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact WP.mono h fun s' h' => by rwa [Nat.zero_add] at h'

theorem prfsScalar_ok {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {N₀ n o wl : Nat}
    (hN : N₀ + n + 4 ≤ 256) (hc : VG.Proof.MlKem.X86_64.prfsChk (rbs ++ wbs) wbs n o wl = true) :
    WP isa (prfsScalar N₀ n o wl) s (VG.Proof.MlKem.X86_64.PrfsPost s N₀ n o wl) :=
  WP.mono (VG.Proof.MlKem.X86_64.prfsScalar_lead L hcs (by omega) (Nat.le_refl n) (VG.Proof.MlKem.X86_64.prfsChk_spec hc).1) fun _ h' => ⟨h'.post, h'.outs⟩

theorem prfsScalar_trL (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {N₀ r o wl : Nat} (hN : N₀ + r ≤ 256)
    (hs : ∀ i < r, VG.Proof.MlKem.X86_64.prf1Chk (rbs ++ wbs) wbs (sc (o + 128 * i)) = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.LRel rbs wbs) (prfsScalar N₀ r o wl) (VG.Proof.MlKem.X86_64.LRel rbs wbs) := by
  have := VG.Proof.MlKem.X86_64.seqR_tr (f := fun i => prf1 (N₀ + i) (sc (o + 128 * i))) (R := fun _ => VG.Proof.MlKem.X86_64.LRel rbs wbs) r 0 fun k _ hk =>
    VG.Proof.MlKem.X86_64.prf1_tr hcs (by omega) (hs k (by omega))
  exact this

theorem prfsScalar_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {N₀ n o wl : Nat} (hN : N₀ + n + 4 ≤ 256)
    (hc : VG.Proof.MlKem.X86_64.prfsChk (rbs ++ wbs) wbs n o wl = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.LRel rbs wbs) (prfsScalar N₀ n o wl) fun _ _ => True :=
  RelCT.mono (VG.Proof.MlKem.X86_64.prfsScalar_trL hcs (by omega) fun i hi => ((VG.Proof.MlKem.X86_64.prfsChk_spec hc).1 i hi).1) (fun _ _ h => h)
    fun _ _ _ => trivial

theorem ctlOk_seqR {f : Nat → Prog isa} (h : ∀ k, ctlOk (f k) = true) : ∀ n a, ctlOk (seqR f a n) = true
  | 0, _ => rfl
  | n + 1, a => VG.Proof.MlKem.X86_64.ctlOk_seq (h a) (VG.Proof.MlKem.X86_64.ctlOk_seqR h n (a + 1))

theorem all_seqR {p : Instr → Bool} {f : Nat → Prog isa} (h : ∀ k, (f k).all p = true) :
    ∀ n a, (seqR f a n).all p = true
  | 0, _ => rfl
  | n + 1, a => VG.Proof.MlKem.X86_64.all_seq (h a) (VG.Proof.MlKem.X86_64.all_seqR h n (a + 1))

theorem prfsScalar_ctl (N₀ n o wl : Nat) : ctlOk (prfsScalar N₀ n o wl) = true :=
  VG.Proof.MlKem.X86_64.ctlOk_seqR (fun _ => VG.Proof.MlKem.X86_64.prf1_ctl _ _) n 0

theorem prfsScalar_sp (N₀ n o wl : Nat) : (prfsScalar N₀ n o wl).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.MlKem.X86_64.all_seqR (fun _ => VG.Proof.MlKem.X86_64.prf1_sp _ _) n 0

/-! ## Four at a time -/

namespace Prf4

open VG.Impl.MlKem.X86_64.Prf4

/-- What `prfsX4 N₀ n o wl` needs, with `scratch` at `b`. -/
structure RawPre (b : Addr) (n o wl : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = b
  w : InRegions s.wr (VG.Proof.MlKem.X86_64.Prf4.sP b wl) 2368
  out : InRegions s.wr (b + BitVec.ofNat 64 o) (128 * n)
  sig : InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.Prf4.sS b) 32
  dWO : (VG.Proof.MlKem.X86_64.Prf4.wR b wl).Disjoint (VG.Proof.MlKem.X86_64.Prf4.oR b o n)
  dWS : (VG.Proof.MlKem.X86_64.Prf4.wR b wl).Disjoint (VG.Proof.MlKem.X86_64.Prf4.sR b)
  dOS : (VG.Proof.MlKem.X86_64.Prf4.oR b o n).Disjoint (VG.Proof.MlKem.X86_64.Prf4.sR b)
  small : 32 * wl + 2368 < 2 ^ 31
  so : o + 128 * n < 2 ^ 32

theorem lt64 {a o : Nat} (h : o + a < 2 ^ 32) : a < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_trans h (by decide))

theorem RawPre.bpre {b : Addr} {n o wl : Nat} {s : State} (h : VG.Proof.MlKem.X86_64.Prf4.RawPre b n o wl s) {m : Nat} (hm : m ≤ 4)
    (hmn : m ≤ n) : VG.Proof.MlKem.X86_64.Prf4.BPre b wl o m s := by
  have hs : Region.Sub (VG.Proof.MlKem.X86_64.Prf4.oR b o m) (VG.Proof.MlKem.X86_64.Prf4.oR b o n) := Region.sub_prefix (by omega)
  refine ⟨h.rbx, h.w, ?_, h.sig, h.dWO.sub_right hs, h.dWS, h.dOS.sub_left hs, hm, h.small⟩
  have := VG.Proof.MlKem.X86_64.inRegions_sub h.out (off := 0) (l := 128 * m) (by omega) (VG.Proof.MlKem.X86_64.Prf4.lt64 h.so)
  rwa [add_ofNat_zero] at this

theorem prfsX4_raw {b : Addr} {wl : Nat} :
    ∀ (n N₀ o : Nat) (s : State), VG.Proof.MlKem.X86_64.Prf4.RawPre b n o wl s → N₀ + n + 4 ≤ 256 →
      WP isa (prfsX4 N₀ n o wl) s fun s' => VG.Proof.MlKem.X86_64.Prf4.BEnv b wl o n s s' ∧
        ∀ k < n, bytesAt s'.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 =
          prf 2 (VG.Proof.MlKem.X86_64.Prf4.sig b s) (BitVec.ofNat 8 (N₀ + k))
  | 0, _, _, _, _, _ => WP.block_nil ⟨BEnv.refl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | 1, N₀, o, s, h, hN =>
    show WP isa (batch N₀ 1 o wl) s _ from VG.Proof.MlKem.X86_64.Prf4.batch_ok (h.bpre (m := 1) (by decide) (by decide)) (by omega)
  | 2, N₀, o, s, h, hN =>
    show WP isa (batch N₀ 2 o wl) s _ from VG.Proof.MlKem.X86_64.Prf4.batch_ok (h.bpre (m := 2) (by decide) (by decide)) (by omega)
  | 3, N₀, o, s, h, hN =>
    show WP isa (batch N₀ 3 o wl) s _ from VG.Proof.MlKem.X86_64.Prf4.batch_ok (h.bpre (m := 3) (by decide) (by decide)) (by omega)
  | n + 4, N₀, o, s, h, hN => by
    show WP isa (.seq (batch N₀ 4 o wl) (prfsX4 (N₀ + 4) n (o + 512) wl)) s _
    have so := h.so
    have hs4 : Region.Sub (VG.Proof.MlKem.X86_64.Prf4.oR b o 4) (VG.Proof.MlKem.X86_64.Prf4.oR b o (n + 4)) := Region.sub_prefix (by omega)
    have hsn : Region.Sub (VG.Proof.MlKem.X86_64.Prf4.oR b (o + 512) n) (VG.Proof.MlKem.X86_64.Prf4.oR b o (n + 4)) := Offset.sub _ (by omega) (by omega)
    refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Prf4.batch_ok (h.bpre (by decide) (by omega)) (by omega)) fun s₁ ⟨e₁, r₁⟩ => ?_)
    have hsig : VG.Proof.MlKem.X86_64.Prf4.sig b s₁ = VG.Proof.MlKem.X86_64.Prf4.sig b s := bytesAt_frame e₁.frame (by
      simpa using ⟨h.dWS.symm, (h.dOS.sub_left hs4).symm⟩) (by decide)
    have h₁ : VG.Proof.MlKem.X86_64.Prf4.RawPre b n (o + 512) wl s₁ := by
      refine ⟨(e₁.cs .rbx (by decide)).trans h.rbx, by rw [e₁.wr]; exact h.w, ?_, by rw [e₁.rd, e₁.wr]; exact h.sig,
        h.dWO.sub_right hsn, h.dWS, h.dOS.sub_left hsn, h.small, by omega⟩
      have := VG.Proof.MlKem.X86_64.inRegions_sub h.out (off := 512) (l := 128 * n) (by omega) (VG.Proof.MlKem.X86_64.Prf4.lt64 h.so)
      rw [e₁.wr, ← Offset.add_add]; exact this
    refine WP.mono (VG.Proof.MlKem.X86_64.Prf4.prfsX4_raw n (N₀ + 4) (o + 512) s₁ h₁ (by omega)) fun s₂ ⟨e₂, r₂⟩ =>
      ⟨⟨e₂.rd.trans e₁.rd, e₂.wr.trans e₁.wr, fun r hr => (e₂.cs r hr).trans (e₁.cs r hr),
        (e₁.frame.sub ?_).trans (e₂.frame.sub ?_)⟩, fun k hk => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hs4⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hsn⟩
    · rcases (by omega : k < 4 ∨ 4 ≤ k) with hk' | hk'
      · rw [bytesAt_frame e₂.frame (by
          have hk4 : Region.Sub ⟨b + BitVec.ofNat 64 (o + 128 * k), 128⟩ (VG.Proof.MlKem.X86_64.Prf4.oR b o (n + 4)) :=
            Offset.sub _ (by omega) (by omega)
          have hd : Region.Disjoint ⟨b + BitVec.ofNat 64 (o + 128 * k), 128⟩ (VG.Proof.MlKem.X86_64.Prf4.oR b (o + 512) n) :=
            Offset.disjoint _ (by omega) (by omega) (by omega)
          simpa using ⟨(h.dWO.sub_right hk4).symm, hd⟩) (by decide)]
        exact r₁ k hk'
      · have := r₂ (k - 4) (by omega)
        rwa [hsig, show o + 512 + 128 * (k - 4) = o + 128 * k by omega, show N₀ + 4 + (k - 4) = N₀ + k by omega]
          at this

theorem prfsX4_rtr {wl : Nat} : ∀ (n N₀ o : Nat),
    RelCT isa (fun x y => x.gpr .rbx = y.gpr .rbx) (prfsX4 N₀ n o wl) fun x y => x.gpr .rbx = y.gpr .rbx
  | 0, _, _ => VG.Proof.MlKem.X86_64.nil_tr
  | 1, _, _ => VG.Proof.MlKem.X86_64.Prf4.batch_tr (m := 1) (fun _ _ h => h) _ _ _ (by decide)
  | 2, _, _ => VG.Proof.MlKem.X86_64.Prf4.batch_tr (m := 2) (fun _ _ h => h) _ _ _ (by decide)
  | 3, _, _ => VG.Proof.MlKem.X86_64.Prf4.batch_tr (m := 3) (fun _ _ h => h) _ _ _ (by decide)
  | n + 4, N₀, o => RelCT.seq (VG.Proof.MlKem.X86_64.Prf4.batch_tr (m := 4) (fun _ _ h => h) _ _ _ (by decide)) (VG.Proof.MlKem.X86_64.Prf4.prfsX4_rtr n (N₀ + 4) (o + 512))

theorem prfsX4_ctl {wl : Nat} : ∀ (n N₀ o : Nat), ctlOk (prfsX4 N₀ n o wl) = true
  | 0, _, _ => rfl
  | 1, _, _ => by kernel_rfl
  | 2, _, _ => by kernel_rfl
  | 3, _, _ => by kernel_rfl
  | n + 4, N₀, o => VG.Proof.MlKem.X86_64.ctlOk_seq (by kernel_rfl) (VG.Proof.MlKem.X86_64.Prf4.prfsX4_ctl n (N₀ + 4) (o + 512))

theorem prfsX4_sp {wl : Nat} : ∀ (n N₀ o : Nat), (prfsX4 N₀ n o wl).all (fun i => !isa.writesSp i) = true
  | 0, _, _ => rfl
  | 1, _, _ => by kernel_rfl
  | 2, _, _ => by kernel_rfl
  | 3, _, _ => by kernel_rfl
  | n + 4, N₀, o => VG.Proof.MlKem.X86_64.all_seq (by kernel_rfl) (VG.Proof.MlKem.X86_64.Prf4.prfsX4_sp n (N₀ + 4) (o + 512))

end Prf4

theorem cover_in {X : List Region} {a : Addr} {n : Nat} (h : Covers [⟨a, n⟩] X) : InRegions X a n :=
  h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem prfsLead_le (n : Nat) : prfsLead n ≤ n := by
  unfold prfsLead; split <;> omega

theorem prfsAvx2_ok {s : State} (L : VG.Proof.MlKem.X86_64.Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {N₀ n o wl : Nat}
    (hN : N₀ + n + 4 ≤ 256) (hc : VG.Proof.MlKem.X86_64.prfsChk (rbs ++ wbs) wbs n o wl = true) :
    WP isa (prfsAvx2 N₀ n o wl) s (VG.Proof.MlKem.X86_64.PrfsPost s N₀ n o wl) := by
  obtain ⟨hs, hw, ho, hsg, dwo, dws, dos, hsm⟩ := VG.Proof.MlKem.X86_64.prfsChk_spec hc
  have hw' : VG.Proof.MlKem.X86_64.inB wbs (sc (32 * wl)) 2368 = true := ((Bool.and_eq_true _ _).mp hw).2
  have ho' : VG.Proof.MlKem.X86_64.inB wbs (sc o) (128 * n) = true := ((Bool.and_eq_true _ _).mp ho).2
  obtain ⟨n₀, hn₀, hl⟩ := VG.Proof.MlKem.X86_64.inB_spec (VG.Proof.MlKem.X86_64.rdOk_in ((Bool.and_eq_true _ _).mp ho).1)
  have := L.small _ hn₀
  have hb : o + 128 * n < 2 ^ 32 := Nat.lt_of_le_of_lt (show o + 128 * n ≤ n₀ from hl) this
  have i1 := VG.Proof.MlKem.X86_64.cover_in (L.cW hw')
  have i2 := VG.Proof.MlKem.X86_64.cover_in (L.cW ho')
  have i3 := VG.Proof.MlKem.X86_64.cover_in (L.cR (VG.Proof.MlKem.X86_64.rdOk_in hsg))
  have d1 := L.disj dwo
  have d2 := L.disj dws
  have d3 := L.disj dos
  have hr := VG.Proof.MlKem.X86_64.prfsLead_le n
  unfold prfsAvx2
  generalize prfsLead n = r at hr ⊢
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.prfsScalar_lead L hcs (by omega) hr fun i hi => hs i (by omega)) fun s₁ h₁ => ?_)
  have e₁ : s₁.gpr .rbx = s.gpr .rbx := h₁.post.cs .rbx (by decide)
  have hsub : Region.Sub (Prf4.oR (s.gpr .rbx) (o + 128 * r) (n - r)) (Prf4.oR (s.gpr .rbx) o n) :=
    Offset.sub _ (by omega) (by omega)
  have raw : Prf4.RawPre (s.gpr .rbx) (n - r) (o + 128 * r) wl s₁ := by
    refine ⟨e₁, by rw [h₁.post.wr]; exact i1, ?_, by rw [h₁.post.rd, h₁.post.wr]; exact i3, d1.sub_right hsub, d2,
      d3.sub_left hsub, hsm, by omega⟩
    have := VG.Proof.MlKem.X86_64.inRegions_sub i2 (off := 128 * r) (l := 128 * (n - r)) (by omega) (Prf4.lt64 hb)
    rw [h₁.post.wr, ← Offset.add_add]; exact this
  have hsig : Prf4.sig (s.gpr .rbx) s₁ = bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s sigP) 32 := by
    rw [← h₁.sig]; simp only [Prf4.sig, Prf4.sS, VG.Proof.MlKem.X86_64.pa, e₁]
  refine WP.mono (Prf4.prfsX4_raw (n - r) (N₀ + r) (o + 128 * r) s₁ raw (by omega)) fun s' ⟨e, out⟩ =>
    ⟨PPost.trans h₁.post ⟨e.rd, e.wr, e.cs, e.frame.sub fun r' hr' => ?_⟩ (fun w hw => by
      simp only [VG.Proof.MlKem.X86_64.prfsW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact VG.Proof.MlKem.X86_64.rbx_cs) (fun w hw => hw) (fun w hw => hw), fun i hi => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · refine ⟨VG.Proof.MlKem.X86_64.toR s₁ (sc (32 * wl), 2368), List.mem_append_left _ (List.mem_map_of_mem
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))), ?_⟩
      simp only [VG.Proof.MlKem.X86_64.toR, VG.Proof.MlKem.X86_64.pa, e₁]; exact fun _ h => h
    · refine ⟨VG.Proof.MlKem.X86_64.toR s₁ (sc o, 128 * n), List.mem_append_left _ (List.mem_map_of_mem
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _)))))), ?_⟩
      simp only [VG.Proof.MlKem.X86_64.toR, VG.Proof.MlKem.X86_64.pa, e₁]; exact hsub
  · rcases (by omega : i < r ∨ r ≤ i) with hi' | hi'
    · rw [bytesAt_frame e.frame (by
        have hk : Region.Sub ⟨s.gpr .rbx + BitVec.ofNat 64 (o + 128 * i), 128⟩ (Prf4.oR (s.gpr .rbx) o n) :=
          Offset.sub _ (by omega) (by omega)
        have hd : Region.Disjoint ⟨s.gpr .rbx + BitVec.ofNat 64 (o + 128 * i), 128⟩
            (Prf4.oR (s.gpr .rbx) (o + 128 * r) (n - r)) := Offset.disjoint _ (by omega) (by omega) (by omega)
        simpa using ⟨(d1.sub_right hk).symm, hd⟩) (by decide)]
      exact h₁.outs i hi'
    · have := out (i - r) (by omega)
      rwa [hsig, show o + 128 * r + 128 * (i - r) = o + 128 * i by omega,
        show N₀ + r + (i - r) = N₀ + i by omega] at this

theorem prfsAvx2_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) {N₀ n o wl : Nat} (hN : N₀ + n + 4 ≤ 256)
    (hc : VG.Proof.MlKem.X86_64.prfsChk (rbs ++ wbs) wbs n o wl = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.LRel rbs wbs) (prfsAvx2 N₀ n o wl) fun _ _ => True := by
  obtain ⟨hs, -, -, hsg, -⟩ := VG.Proof.MlKem.X86_64.prfsChk_spec hc
  have hr := VG.Proof.MlKem.X86_64.prfsLead_le n
  unfold prfsAvx2
  generalize prfsLead n = r at hr ⊢
  exact RelCT.seq (VG.Proof.MlKem.X86_64.prfsScalar_trL hcs (by omega) fun i hi => (hs i (by omega)).1)
    (RelCT.mono (Prf4.prfsX4_rtr _ _ _) (fun _ _ h => h.eq (VG.Proof.MlKem.X86_64.rdOk_in hsg)) fun _ _ _ => trivial)

theorem prfsAvx2_ctl (N₀ n o wl : Nat) : ctlOk (prfsAvx2 N₀ n o wl) = true :=
  VG.Proof.MlKem.X86_64.ctlOk_seq (VG.Proof.MlKem.X86_64.prfsScalar_ctl _ _ _ _) (Prf4.prfsX4_ctl _ _ _)

theorem prfsAvx2_sp (N₀ n o wl : Nat) : (prfsAvx2 N₀ n o wl).all (fun i => !isa.writesSp i) = true :=
  VG.Proof.MlKem.X86_64.all_seq (VG.Proof.MlKem.X86_64.prfsScalar_sp _ _ _ _) (Prf4.prfsX4_sp _ _ _)

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.S4CT`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, constant time but for the seeds

Two runs whose seeds (the declared leak) and pointers agree leak the same. The
code but for the loops of `parse` and their fallbacks is proven by the taint
analysis, from the pointers. Both runs read the same XOF output, so in the
loops they are at the same iteration with the same coefficients sampled: each
group of four iterations takes the same branch (on `j < 249`, `vgrp_ct`); the
vector code computes the same mask of the candidates in `eax` (`VI.rax`), so
it loads the same entry of the table, stores to the same address and counts
the same (the taint analysis, from `rax`, `rbx`, `rbp`, `rdi` and `rsi`), and
`vg_mlkem_sample_ntt`'s loop runs as in that function (`body_ct`). The
fallbacks take the same branch, and call `vg_mlkem_sample_ntt` on the same
seed.
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- Two runs related by `I`, from entry states that agree on what is public. -/
abbrev R4 (I : State → State → Prop) : State → State → Prop := Rel2 sample4K.pre sample4K.pub I

section
variable {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂)
include hq

theorem pub_scr : VG.Proof.MlKem.X86_64.S4.scr σ₁ = VG.Proof.MlKem.X86_64.S4.scr σ₂ := hq.2.2.1
theorem pub_aP : VG.Proof.MlKem.X86_64.S4.aP σ₁ = VG.Proof.MlKem.X86_64.S4.aP σ₂ := hq.2.1
theorem pub_sd : VG.Proof.MlKem.X86_64.S4.sd σ₁ = VG.Proof.MlKem.X86_64.S4.sd σ₂ := hq.1
theorem pub_sp : σ₁.gpr .rsp = σ₂.gpr .rsp := hq.2.2.2.1

theorem pub_B {k : Nat} (hk : k < 4) : VG.Proof.MlKem.X86_64.S4.B σ₁ k = VG.Proof.MlKem.X86_64.S4.B σ₂ k := by
  have e := hq.2.2.2.2
  simp only [VG.Proof.MlKem.X86_64.S4.B, seed4, VG.Proof.MlKem.X86_64.S4.sd, bytesAt] at e ⊢
  rw [← hq.1] at e ⊢
  apply List.ext_getElem (by simp)
  intro i h₁ _
  have := congrArg (fun L => L[34 * k + i]?) e
  simp only [List.getElem?_map, List.getElem?_range (show 34 * k + i < 136 by simp at h₁; omega),
    Option.map_some, Option.some.injEq] at this
  simp only [List.getElem_map, List.getElem_range, Offset.add_add]
  exact this

end

theorem start_ct : RelCT isa (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => s = σ)
    (.block (pro ++ Impl.Sha3.X86_64.X4.rcTable .rbx (oRc / 32) ++ absorb4)) (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.SqInv σ 0 s) :=
  relInv (fun σ s hp h => by subst h; exact VG.Proof.MlKem.X86_64.S4.start_ok (VG.Proof.MlKem.X86_64.S4.pre_of hp))
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) (by taint_decide))


theorem env_rbx {σ₁ σ₂ s₁ s₂ : State} (hq : sample4K.pub σ₁ σ₂) (e₁ : VG.Proof.MlKem.X86_64.S4.Env σ₁ s₁) (e₂ : VG.Proof.MlKem.X86_64.S4.Env σ₂ s₂) :
    s₁.gpr .rbx = s₂.gpr .rbx := by rw [e₁.rbx, e₂.rbx, VG.Proof.MlKem.X86_64.S4.pub_scr hq]

/-- `squeeze4 n`, given its taint analysis. -/
theorem sq_ct (n : Nat) (hn : n < 3) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 n) hc).isSome = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.SqInv σ n s) (squeeze4 n) (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.SqInv σ (n + 1) s) :=
  relInv (fun σ s hp h => VG.Proof.MlKem.X86_64.S4.sq_ok (VG.Proof.MlKem.X86_64.S4.pre_of hp) hn h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlKem.X86_64.S4.env_rbx hq h₁.env h₂.env) c)

theorem sq0_ct : RelCT isa (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.SqInv σ 0 s) (squeeze4 0) (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.SqInv σ 1 s) :=
  VG.Proof.MlKem.X86_64.S4.sq_ct 0 (by decide) (by taint_decide)

/-! ## The groups of four iterations -/

theorem pub_Lt {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) {K : Nat} (hK : K < 4) (t : Nat) :
    VG.Proof.MlKem.X86_64.S4.Lt σ₁ K t = VG.Proof.MlKem.X86_64.S4.Lt σ₂ K t := by simp only [VG.Proof.MlKem.X86_64.S4.Lt, VG.Proof.MlKem.X86_64.S4.pub_B hq hK]

theorem bpre {σ : State} (hp : sample4K.pre σ) {K t : Nat} (hK : K < 4) (ht : t < 168) {s : State}
    (h : VG.Proof.MlKem.X86_64.S4.LAt σ K t s) : VG.Proof.MlKem.X86_64.BPre s (poly4 (VG.Proof.MlKem.X86_64.S4.aP σ) K) (VG.Proof.MlKem.X86_64.S4.Lt σ K t) := by
  have hp' := VG.Proof.MlKem.X86_64.S4.pre_of hp
  refine ⟨h.rbp, h.rdi, sampleAfter_length_le (a := []) (by simp) _ t, fun j hj => ?_, h.stored,
    by simpa using VG.Proof.MlKem.X86_64.S4.lat_regions hp' hK h (j := 0) (by bdd_omega), VG.Proof.MlKem.X86_64.S4.lat_regions hp' hK h (by bdd_omega),
    VG.Proof.MlKem.X86_64.S4.lat_regions hp' hK h (by bdd_omega)⟩
  rw [h.pinv.env.wr, hp'.wr]
  refine ⟨VG.Proof.MlKem.X86_64.S4.aR σ, by simp, ?_⟩
  rw [coeffAddr, poly4, Offset.add_add]
  exact Offset.contains_base _ (by bdd_omega) (by bdd_omega)

/-- Two runs at iteration `t + u` of the scalar group from iteration `t`, `n = 4 - u` iterations from its
end. -/
def GI (K t : Nat) (c : BitVec 64) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ u, sample4K.pre σ₁ ∧ sample4K.pre σ₂ ∧ sample4K.pub σ₁ σ₂ ∧ n = 4 - u ∧ u < 4 ∧
    VG.Proof.MlKem.X86_64.S4.LAt σ₁ K (t + u) s₁ ∧ VG.Proof.MlKem.X86_64.S4.LAt σ₂ K (t + u) s₂ ∧ s₁.gpr .rcx = BitVec.ofNat 64 (4 - u) ∧
    s₂.gpr .rcx = BitVec.ofNat 64 (4 - u) ∧ s₁.gpr .r10 = c ∧ s₂.gpr .r10 = c ∧
    ¬ (VG.Proof.MlKem.X86_64.S4.Lt σ₁ K t).length < 249 ∧ ¬ (VG.Proof.MlKem.X86_64.S4.Lt σ₂ K t).length < 249

theorem gi_brel {K t : Nat} {c : BitVec 64} {n : Nat} (hK : K < 4) (ht : t + 4 ≤ 168) {s₁ s₂ : State}
    (h : VG.Proof.MlKem.X86_64.S4.GI K t c n s₁ s₂) : BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, u, p₁, p₂, hq, _, hu, l₁, l₂, c₁, c₂, -⟩ := h
  refine ⟨poly4 (VG.Proof.MlKem.X86_64.S4.aP σ₁) K, VG.Proof.MlKem.X86_64.S4.Lt σ₁ K (t + u), VG.Proof.MlKem.X86_64.S4.bpre p₁ hK (by bdd_omega) l₁,
    by rw [VG.Proof.MlKem.X86_64.S4.pub_aP hq, VG.Proof.MlKem.X86_64.S4.pub_Lt hq hK]; exact VG.Proof.MlKem.X86_64.S4.bpre p₂ hK (by bdd_omega) l₂,
    by rw [l₁.rsi, l₂.rsi, VG.Proof.MlKem.X86_64.S4.at', VG.Proof.MlKem.X86_64.S4.at', VG.Proof.MlKem.X86_64.S4.pub_scr hq], by rw [c₁, c₂], fun k hk => ?_⟩
  rw [VG.Proof.MlKem.X86_64.S4.out_byte hK l₁ (by bdd_omega), VG.Proof.MlKem.X86_64.S4.out_byte hK l₂ (by bdd_omega), VG.Proof.MlKem.X86_64.S4.pub_B hq hK]

/-- The four iterations of `vg_mlkem_sample_ntt`'s loop. -/
theorem iloop_ct {K t : Nat} {c : BitVec 64} (hK : K < 4) (ht : t + 4 ≤ 168) (n : Nat) :
    RelCT isa (VG.Proof.MlKem.X86_64.S4.GI K t c n) (.loop snBody .ne)
      (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.LAt σ K (t + 4) s ∧ s.gpr .r10 = c ∧ ¬ (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length < 249) := by
  refine RelCT.loop (M := isa) (VG.Proof.MlKem.X86_64.S4.GI K t c) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × Nat, sample4K.pre p.1 ∧ p.2 < 4 ∧
      VG.Proof.MlKem.X86_64.S4.LAt p.1 K (t + p.2) x → (VG.Proof.MlKem.X86_64.S4.LAt p.1 K (t + p.2 + 1) x' ∧ x'.gpr .rcx = x.gpr .rcx - 1 ∧
        x'.zf = some (x.gpr .rcx - 1 == 0)) ∧ x'.gpr .r10 = x.gpr .r10)
    (RelCT.mono body_ct (fun x y h => VG.Proof.MlKem.X86_64.S4.gi_brel hK ht h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, u, p₁, p₂, _, _, hu, l₁, l₂, _⟩ := h
    exact ⟨WP.all (fun p hp' => WP.gpr (VG.Proof.MlKem.X86_64.S4.lat_step (VG.Proof.MlKem.X86_64.S4.pre_of hp'.1) hK (by bdd_omega) hp'.2.2) (r := .r10) (by decide))
        ⟨(σ₁, u), p₁, hu, l₁⟩,
      WP.all (fun p hp' => WP.gpr (VG.Proof.MlKem.X86_64.S4.lat_step (VG.Proof.MlKem.X86_64.S4.pre_of hp'.1) hK (by bdd_omega) hp'.2.2) (r := .r10) (by decide))
        ⟨(σ₂, u), p₂, hu, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, u, p₁, p₂, hq, hn, hu, l₁, l₂, c₁, c₂, d₁, d₂, v₁, v₂⟩ f₁ f₂
    obtain ⟨⟨l₁', r₁, z₁⟩, e₁⟩ := f₁ (σ₁, u) ⟨p₁, hu, l₁⟩
    obtain ⟨⟨l₂', r₂, z₂⟩, e₂⟩ := f₂ (σ₂, u) ⟨p₂, hu, l₂⟩
    rw [c₁, SampleNtt.zf_last (by decide) hu] at z₁
    rw [c₂, SampleNtt.zf_last (by decide) hu] at z₂
    rw [c₁, ofNat64_pred (by bdd_omega) (by bdd_omega)] at r₁
    rw [c₂, ofNat64_pred (by bdd_omega) (by bdd_omega)] at r₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : u + 1 = 4 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [Nat.add_assoc, this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁', by rw [e₁, d₁], v₁⟩, ⟨l₂', by rw [e₂, d₂], v₂⟩⟩
    · have : u + 1 ≠ 4 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨4 - (u + 1), by bdd_omega, σ₁, σ₂, u + 1, p₁, p₂, hq, rfl, by bdd_omega, by rw [← Nat.add_assoc]; exact l₁',
        by rw [← Nat.add_assoc]; exact l₂', by rw [r₁]; congr 1, by rw [r₂]; congr 1, by rw [e₁, d₁], by rw [e₂, d₂],
        v₁, v₂⟩

/-- The relation of two runs at a group: iteration `t`, the constants in place while there are
fewer than 249 coefficients, and `r10 = c`. -/
abbrev RV (K t : Nat) (c : BitVec 64) : State → State → Prop := VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.LV σ K t s ∧ s.gpr .r10 = c

theorem cmpG_ok {σ : State} {K t : Nat} {c : BitVec 64} {s : State} (h : VG.Proof.MlKem.X86_64.S4.LV σ K t s ∧ s.gpr .r10 = c) :
    WP isa (.block [.alu .cmp .rdi (.imm 249)]) s fun s' => (VG.Proof.MlKem.X86_64.S4.LV σ K t s' ∧ s'.gpr .r10 = c) ∧
      s'.cf = some (decide ((VG.Proof.MlKem.X86_64.S4.Lt σ K t).length < 249)) := by
  have hlen : (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ t
  refine WP.mono (VG.Proof.MlKem.X86_64.S4.cmp249_ok s) fun s' ⟨hcf, hm, hg, hrd, hwr, hl⟩ => ?_
  exact ⟨⟨⟨h.1.lat.same hg hm hrd hwr, fun h' => (h.1.vc h').same hl⟩, by rw [hg]; exact h.2⟩,
    by rw [hcf, h.1.lat.rdi, ofNat64_toNat (by bdd_omega)]⟩

/-- A group of four iterations. -/
theorem vgrp_ct {K t : Nat} {c : BitVec 64} (hK : K < 4) (ht : t + 4 ≤ 168) :
    RelCT isa (VG.Proof.MlKem.X86_64.S4.RV K t c) vgrp (VG.Proof.MlKem.X86_64.S4.RV K (t + 4) c) := by
  unfold vgrp
  refine RelCT.seq (relInv (I' := fun σ s => (VG.Proof.MlKem.X86_64.S4.LV σ K t s ∧ s.gpr .r10 = c) ∧
      s.cf = some (decide ((VG.Proof.MlKem.X86_64.S4.Lt σ K t).length < 249))) (fun σ s _ h => VG.Proof.MlKem.X86_64.S4.cmpG_ok h)
    (taintRel [.rdi] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.lat.rdi, h₂.1.lat.rdi, VG.Proof.MlKem.X86_64.S4.pub_Lt hq hK])
      (by taint_decide))) (RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
        show x.cf = y.cf; rw [h₁.2, h₂.2, VG.Proof.MlKem.X86_64.S4.pub_Lt hq hK]) ?_ ?_)
  · -- with the vector code
    refine RelCT.mono (P := VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.LAt σ K t s ∧ VG.Proof.MlKem.X86_64.S4.VC s ∧ (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length < 249 ∧ s.gpr .r10 = c)
      (RelCT.seq (relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.S4.VI σ K t s ∧ s.gpr .r10 = c)
          (fun σ s hp h => WP.mono (VG.Proof.MlKem.X86_64.S4.vec1_ok (VG.Proof.MlKem.X86_64.S4.pre_of hp) hK ht h.1 h.2.1 h.2.2.1) fun _ ⟨hi, h10⟩ =>
            ⟨hi, by rw [h10]; exact h.2.2.2⟩)
          (taintRel [.rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.rsi, h₂.1.rsi, VG.Proof.MlKem.X86_64.S4.at', VG.Proof.MlKem.X86_64.S4.at', VG.Proof.MlKem.X86_64.S4.pub_scr hq])
            (by taint_decide)))
        (relInv (fun σ s hp h => WP.mono (VG.Proof.MlKem.X86_64.S4.vec2_ok (VG.Proof.MlKem.X86_64.S4.pre_of hp) hK ht h.1) fun _ ⟨l, v, h10⟩ =>
            ⟨⟨l, fun _ => v⟩, by rw [h10]; exact h.2⟩)
          (taintRel [.rbx, .rax, .rbp, .rdi, .rsi] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl
            · exact VG.Proof.MlKem.X86_64.S4.env_rbx hq h₁.1.lat.pinv.env h₂.1.lat.pinv.env
            · rw [h₁.1.rax, h₂.1.rax, VG.Proof.MlKem.X86_64.S4.pub_B hq hK]
            · rw [h₁.1.lat.rbp, h₂.1.lat.rbp, VG.Proof.MlKem.X86_64.S4.pub_aP hq]
            · rw [h₁.1.lat.rdi, h₂.1.lat.rdi, VG.Proof.MlKem.X86_64.S4.pub_Lt hq hK]
            · rw [h₁.1.lat.rsi, h₂.1.lat.rsi, VG.Proof.MlKem.X86_64.S4.at', VG.Proof.MlKem.X86_64.S4.at', VG.Proof.MlKem.X86_64.S4.pub_scr hq]) (by taint_decide))))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨⟨l₁, v₁⟩, d₁⟩, f₁⟩, ⟨⟨⟨l₂, v₂⟩, d₂⟩, f₂⟩⟩, hb⟩ => ?_) fun _ _ h => h
    have hb' : (VG.Proof.MlKem.X86_64.S4.Lt σ₁ K t).length < 249 := by
      have : x.cf = some true := hb
      rw [f₁] at this; simpa using this
    have hb'' : (VG.Proof.MlKem.X86_64.S4.Lt σ₂ K t).length < 249 := by rw [← VG.Proof.MlKem.X86_64.S4.pub_Lt hq hK]; exact hb'
    exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁, v₁ hb', hb', d₁⟩, ⟨l₂, v₂ hb'', hb'', d₂⟩⟩
  · -- with `snBody`
    refine RelCT.mono (P := VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.LAt σ K t s ∧ ¬ (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length < 249 ∧ s.gpr .r10 = c) ?_ ?_
      fun _ _ h => h
    · refine RelCT.seq (relInv (I' := fun σ s => (VG.Proof.MlKem.X86_64.S4.LAt σ K t s ∧ ¬ (VG.Proof.MlKem.X86_64.S4.Lt σ K t).length < 249 ∧ s.gpr .r10 = c) ∧
          s.gpr .rcx = BitVec.ofNat 64 4) ?_ ?_) ?_
      · intro σ s _ h
        refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 4)
          (by xrun) (by decide)) fun s' ⟨⟨hm, hc⟩, k⟩ => ?_
        exact ⟨⟨h.1.same' hm k, h.2.1, by rw [k.gpr (by decide)]; exact h.2.2⟩, hc⟩
      · exact taintRel [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)
      · refine RelCT.mono (VG.Proof.MlKem.X86_64.S4.iloop_ct (c := c) hK ht 4) ?_ ?_
        · rintro x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨l₁, v₁, d₁⟩, c₁⟩, ⟨⟨l₂, v₂, d₂⟩, c₂⟩⟩
          exact ⟨σ₁, σ₂, 0, p₁, p₂, hq, rfl, by decide, l₁, l₂, c₁, c₂, d₁, d₂, v₁, v₂⟩
        · rintro x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁, d₁, v₁⟩, ⟨l₂, d₂, v₂⟩⟩
          exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨l₁, fun h' => absurd (Nat.lt_of_le_of_lt (VG.Proof.MlKem.X86_64.S4.Lt_mono σ₁ K t 4) h') v₁⟩, d₁⟩,
            ⟨⟨l₂, fun h' => absurd (Nat.lt_of_le_of_lt (VG.Proof.MlKem.X86_64.S4.Lt_mono σ₂ K t 4) h') v₂⟩, d₂⟩⟩
    · rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, ⟨⟨⟨l₁, -⟩, d₁⟩, f₁⟩, ⟨⟨⟨l₂, -⟩, d₂⟩, f₂⟩⟩, hb⟩
      have hb' : ¬ (VG.Proof.MlKem.X86_64.S4.Lt σ₁ K t).length < 249 := by
        have : x.cf = some false := hb
        rw [f₁] at this; simpa using this
      have hb'' : ¬ (VG.Proof.MlKem.X86_64.S4.Lt σ₂ K t).length < 249 := by rw [← VG.Proof.MlKem.X86_64.S4.pub_Lt hq hK]; exact hb'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁, hb', d₁⟩, ⟨l₂, hb'', d₂⟩⟩

/-! ## The fallbacks -/

/-- The call of `vg_mlkem_sample_ntt` on seed `K`, with `X σ` of the memory, which its writes keep. -/
theorem call_ct {X : State → Mem → Prop} {K : Nat} (hK : K < 4)
    (hX : ∀ σ, sample4K.pre σ → ∀ m m', Frame (VG.Proof.MlKem.X86_64.S4.cWr σ K ++ [VG.Proof.MlKem.X86_64.S4.stkR σ]) m m' → X σ m → X σ m') :
    RelCT isa (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.ArgI (X σ) σ K s) (.call "vg_mlkem_sample_ntt" sampleNTT)
      (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.CallI (X σ) σ K s) :=
  relInv (fun σ s hp h => VG.Proof.MlKem.X86_64.S4.callK_ok (VG.Proof.MlKem.X86_64.S4.pre_of hp) hK (hX σ hp) h) (RelCT.callEx sample_correct sample_ct
    fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      have hsp : s₁.gpr .rsp = s₂.gpr .rsp := by rw [h₁.pinv.env.rsp, h₂.pinv.env.rsp, VG.Proof.MlKem.X86_64.S4.pub_sp hq]
      refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.S4.argK_pre (VG.Proof.MlKem.X86_64.S4.pre_of p₁) hK h₁, VG.Proof.MlKem.X86_64.S4.argK_pre (VG.Proof.MlKem.X86_64.S4.pre_of p₂) hK h₂, ?_,
        (VG.Proof.MlKem.X86_64.S4.cov (VG.Proof.MlKem.X86_64.S4.pre_of p₁) h₁.pinv.env hK).1, (VG.Proof.MlKem.X86_64.S4.cov (VG.Proof.MlKem.X86_64.S4.pre_of p₁) h₁.pinv.env hK).2,
        (VG.Proof.MlKem.X86_64.S4.cov (VG.Proof.MlKem.X86_64.S4.pre_of p₂) h₂.pinv.env hK).1, (VG.Proof.MlKem.X86_64.S4.cov (VG.Proof.MlKem.X86_64.S4.pre_of p₂) h₂.pinv.env hK).2, hsp⟩
      simp only [sampleK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
        ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
        ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), h₁.rdi, h₂.rdi, h₁.rsi, h₂.rsi, h₁.rdx, h₂.rdx]
      rw [ce_bytesAt24 s₁ (n := 34) (by decide) (VG.Proof.MlKem.X86_64.S4.argK_kS (VG.Proof.MlKem.X86_64.S4.pre_of p₁) hK h₁),
        ce_bytesAt24 s₂ (n := 34) (by decide) (VG.Proof.MlKem.X86_64.S4.argK_kS (VG.Proof.MlKem.X86_64.S4.pre_of p₂) hK h₂),
        VG.Proof.MlKem.X86_64.S4.seed_bytes (VG.Proof.MlKem.X86_64.S4.pre_of p₁) hK h₁.pinv.env.frame, VG.Proof.MlKem.X86_64.S4.seed_bytes (VG.Proof.MlKem.X86_64.S4.pre_of p₂) hK h₂.pinv.env.frame, VG.Proof.MlKem.X86_64.S4.pub_B hq hK]
      simp only [VG.Proof.MlKem.X86_64.S4.pub_sd hq, VG.Proof.MlKem.X86_64.S4.pub_aP hq, VG.Proof.MlKem.X86_64.S4.at', VG.Proof.MlKem.X86_64.S4.pub_scr hq, hsp, and_self])

/-- The arguments of the call on seed `K`, given their taint analysis. -/
theorem args_ct {X : State → Mem → Prop} {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.PC (X σ) σ K s)
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.ArgI (X σ) σ K s) :=
  relInv (fun σ s _ h => VG.Proof.MlKem.X86_64.S4.argsK_ok hK h) (taintRel [.r12, .r13, .rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.env.r12, h₂.env.r12, VG.Proof.MlKem.X86_64.S4.pub_sd hq]
    · rw [h₁.env.r13, h₂.env.r13, VG.Proof.MlKem.X86_64.S4.pub_aP hq]
    · exact VG.Proof.MlKem.X86_64.S4.env_rbx hq h₁.env h₂.env) c)

theorem and_ct {X : State → Mem → Prop} {K : Nat} :
    RelCT isa (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.CallI (X σ) σ K s) (.block [.alu32 .and .r14 (.reg .rax)])
      (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.PC (X σ) σ (K + 1) s) :=
  relInv (fun σ s _ h => VG.Proof.MlKem.X86_64.S4.andK_ok h) (taintRel [] SampleNtt.nil_regs (by taint_decide))

/-- The check of `j` and the call, given the taint analysis of the call's arguments. -/
theorem fallback_ct {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.LAt σ K 168 s) (fallback K) (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.PInv σ (K + 1) s) := by
  unfold fallback
  refine RelCT.seq (relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.S4.MI σ K s) (fun σ s _ h => VG.Proof.MlKem.X86_64.S4.cmpK_ok h)
    (taintRel [] SampleNtt.nil_regs (by taint_decide))) (RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
      show x.cf = y.cf; rw [h₁.cf, h₂.cf, VG.Proof.MlKem.X86_64.S4.pub_Lt hq hK]) ?_ ?_)
  · refine RelCT.mono (P := VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.PInv σ K s)
      (RelCT.seq (VG.Proof.MlKem.X86_64.S4.args_ct (X := VG.Proof.MlKem.X86_64.S4.BufT) hK c) (RelCT.seq (VG.Proof.MlKem.X86_64.S4.call_ct hK fun σ hp => VG.Proof.MlKem.X86_64.S4.bufOK_call (VG.Proof.MlKem.X86_64.S4.pre_of hp) hK) VG.Proof.MlKem.X86_64.S4.and_ct))
      (fun _ _ ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, _⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, h₁.pinv, h₂.pinv⟩) fun _ _ h => h
  · refine RelCT.mono (P := VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.MI σ K s ∧ s.cf = some false)
      (relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.S4.PInv σ (K + 1) s) (fun σ s _ h => WP.block_nil (VG.Proof.MlKem.X86_64.S4.skipK_ok hK h.1 h.2))
        (taintRel [] SampleNtt.nil_regs (by taint_decide)))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hc⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, hc⟩, ⟨h₂, ?_⟩⟩) fun _ _ h => h
    have hc' : x.cf = some false := hc
    rw [h₂.cf, ← VG.Proof.MlKem.X86_64.S4.pub_Lt hq hK, ← h₁.cf, hc']

/-! ## The loop of `parse K` -/

/-- Two runs at group `2 i` of the loop, `n = 21 - i` iterations from its end. -/
def LI (K n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ i, n = 21 - i ∧ i < 21 ∧ VG.Proof.MlKem.X86_64.S4.RV K (8 * i) (BitVec.ofNat 64 (21 - i)) s₁ s₂

theorem sub10_ct {K t : Nat} {c : BitVec 64} :
    RelCT isa (VG.Proof.MlKem.X86_64.S4.RV K t c) (.block [.alu .sub .r10 (.imm 1)])
      (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.LV σ K t s ∧ s.gpr .r10 = c - 1 ∧ s.zf = some (c - 1 == 0)) :=
  relInv (fun σ s _ h => WP.mono (VG.Proof.MlKem.X86_64.S4.sub10_ok s) fun s' ⟨⟨hm, h10, hz, hl⟩, k⟩ =>
      ⟨⟨h.1.lat.same' hm k, fun h' => (h.1.vc h').same hl⟩, by rw [h10, h.2], by rw [hz, h.2]⟩)
    (taintRel [.r10] (fun x y ⟨σ₁, σ₂, _, _, _, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) (by taint_decide))

theorem loopV_ct {K : Nat} (hK : K < 4) (n : Nat) :
    RelCT isa (VG.Proof.MlKem.X86_64.S4.LI K n) (.loop Sample4.vbody .ne) (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.LAt σ K 168 s) := by
  refine RelCT.loop (M := isa) (VG.Proof.MlKem.X86_64.S4.LI K) (fun n => ?_) n
  refine RelCT.mono (P := fun s₁ s₂ => ∃ i, n = 21 - i ∧ i < 21 ∧ VG.Proof.MlKem.X86_64.S4.RV K (8 * i) (BitVec.ofNat 64 (21 - i)) s₁ s₂)
    (RelCT.exists_ fun i => ?_) (fun _ _ h => by unfold VG.Proof.MlKem.X86_64.S4.LI at h; exact h) fun _ _ h => h
  by_cases hi : i < 21 ∧ n = 21 - i
  · obtain ⟨hi, hn⟩ := hi
    refine RelCT.mono (P := VG.Proof.MlKem.X86_64.S4.RV K (8 * i) (BitVec.ofNat 64 (21 - i)))
      (RelCT.seq (VG.Proof.MlKem.X86_64.S4.vgrp_ct hK (by bdd_omega)) (RelCT.seq (VG.Proof.MlKem.X86_64.S4.vgrp_ct hK (by bdd_omega)) VG.Proof.MlKem.X86_64.S4.sub10_ct))
      (fun _ _ h => h.2.2) fun x y ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁, d₁, z₁⟩, ⟨l₂, d₂, z₂⟩⟩ => ?_
    rw [ofNat64_pred (by bdd_omega) (by bdd_omega)] at d₁ d₂ z₁ z₂
    rw [ofNat64_beq_zero (by bdd_omega)] at z₁ z₂
    rw [show 8 * i + 4 + 4 = 8 * (i + 1) by bdd_omega] at l₁ l₂
    refine ⟨by show x.zf.map _ = y.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht => ?_⟩
    · have : 21 - i - 1 = 0 := by
        have : x.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [show i + 1 = 21 by bdd_omega] at l₁ l₂
      exact ⟨σ₁, σ₂, p₁, p₂, hq, l₁.lat, l₂.lat⟩
    · have : 21 - i - 1 ≠ 0 := by
        have : x.zf.map (!·) = some true := ht
        rw [z₁] at this; simpa using this
      exact ⟨21 - (i + 1), by bdd_omega, i + 1, rfl, by bdd_omega, σ₁, σ₂, p₁, p₂, hq,
        ⟨l₁, by rw [d₁]; congr 1⟩, ⟨l₂, by rw [d₂]; congr 1⟩⟩
  · exact RelCT.of_false fun _ _ h => hi ⟨h.2.1, h.1⟩

/-- `parse K`. -/
theorem parse_ct {K : Nat} (hK : K < 4) {h₁ h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (setup K ++ cstLoad)) h₁).isSome = true)
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) h₂).isSome = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.PInv σ K s) (parse K) (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.PInv σ (K + 1) s) := by
  unfold parse
  refine RelCT.seq (RelCT.mono (relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.S4.LV σ K 0 s ∧ s.gpr .r10 = BitVec.ofNat 64 21)
      (fun σ s hp h => VG.Proof.MlKem.X86_64.S4.setup_ok (VG.Proof.MlKem.X86_64.S4.pre_of hp) hK h)
      (taintRel [.rbx, .r13] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.MlKem.X86_64.S4.env_rbx hq h₁.env h₂.env
        · rw [h₁.env.r13, h₂.env.r13, VG.Proof.MlKem.X86_64.S4.pub_aP hq]) c₁)) (fun _ _ h => h)
      (Q' := VG.Proof.MlKem.X86_64.S4.LI K 21) fun x y h => ⟨0, rfl, by decide, h⟩)
    (RelCT.seq (VG.Proof.MlKem.X86_64.S4.loopV_ct hK 21) (RelCT.seq (relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.S4.LAt σ K 168 s) (fun _ _ _ h => VG.Proof.MlKem.X86_64.S4.vz_lat h)
      (taintRel [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide))) (VG.Proof.MlKem.X86_64.S4.fallback_ct hK c₂)))

theorem tab_ct : RelCT isa (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.SqInv σ 3 s) (.block tabBuild) (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.PInv σ 0 s) :=
  relInv (fun σ s hp h => VG.Proof.MlKem.X86_64.S4.pinv0_ok (VG.Proof.MlKem.X86_64.S4.pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlKem.X86_64.S4.env_rbx hq h₁.env h₂.env) (by taint_decide))

theorem ct : ConstantTime isa sample4K.pre sample4K.pub Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq VG.Proof.MlKem.X86_64.S4.start_ct (RelCT.seq VG.Proof.MlKem.X86_64.S4.sq0_ct
    (RelCT.seq (VG.Proof.MlKem.X86_64.S4.sq_ct 1 (by decide) (by taint_decide)) (RelCT.seq (VG.Proof.MlKem.X86_64.S4.sq_ct 2 (by decide) (by taint_decide))
      (RelCT.seq VG.Proof.MlKem.X86_64.S4.tab_ct ?_)))))
  refine RelCT.seq (VG.Proof.MlKem.X86_64.S4.parse_ct (K := 0) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlKem.X86_64.S4.parse_ct (K := 1) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlKem.X86_64.S4.parse_ct (K := 2) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (VG.Proof.MlKem.X86_64.S4.parse_ct (K := 3) (by decide) (by taint_decide) (by taint_decide)) ?_
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlKem.X86_64.S4.env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlKem.X86_64.S4

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.S4Verified`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, verified

The contract of the proof (`sample4K`) implies the shared one of `Spec/`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition. -/
def sample4Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x4000 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 136⟩]
  wr := [⟨0x2000, 4096⟩, ⟨0x4000, 8192⟩]

theorem sample4_post {s s' : State} (h : sample4K.post s s') :
    let r := (s'.gpr .rax).setWidth 32
    (r = 1 → ∀ k < 4, Spec.MlKem.Reduced s'.mem (Spec.MlKem.poly4 (s.gpr .rsi) k)) ∧
      ((r = 1 ∧ ∀ k < 4, ∃ iters, Spec.MlKem.sampleNTT iters (Spec.MlKem.seed4 s.mem (s.gpr .rdi) k) =
          some (Spec.MlKem.polyAt s'.mem (Spec.MlKem.poly4 (s.gpr .rsi) k))) ∨
        (r = 0 ∧ ∃ k < 4, Spec.MlKem.sampleNTT Spec.MlKem.minIterations
          (Spec.MlKem.seed4 s.mem (s.gpr .rdi) k) = none)) := by
  obtain ⟨hr, hp⟩ := h
  intro r
  by_cases hall : ((List.range 4).all fun k =>
      (Spec.MlKem.sampleNTT Spec.MlKem.minIterations (Spec.MlKem.seed4 s.mem (s.gpr .rdi) k)).isSome) = true
  · rw [ite_eq_left hall] at hr
    have hs : ∀ k < 4, ∃ f, Spec.MlKem.sampleNTT Spec.MlKem.minIterations
        (Spec.MlKem.seed4 s.mem (s.gpr .rdi) k) = some f := fun k hk => by
      have := List.all_eq_true.mp hall k (List.mem_range.mpr hk)
      exact Option.isSome_iff_exists.mp this
    refine ⟨fun _ k hk => ?_, .inl ⟨hr, fun k hk => ?_⟩⟩
    · obtain ⟨f, e⟩ := hs k hk; exact (hp k hk f e).1
    · obtain ⟨f, e⟩ := hs k hk
      exact ⟨Spec.MlKem.minIterations, by rw [e, (hp k hk f e).2]⟩
  · rw [ite_eq_right hall] at hr
    refine ⟨fun h1 => absurd (hr.symm.trans h1) (by decide), .inr ⟨hr, ?_⟩⟩
    simp only [List.all_eq_true, List.mem_range, Classical.not_forall] at hall
    obtain ⟨k, hk, hk'⟩ := hall
    exact ⟨k, hk, Option.not_isSome_iff_eq_none.mp hk'⟩

theorem sample4_verified : Verified X86_64.target Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2
    (Spec.MlKem.sampleNTT4Contract X86_64.abi 24) :=
  Verified.of_correct S4.correct S4.ct
    { pre := by sig_implies_pre [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, VG.Proof.MlKem.X86_64.sample4K, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, VG.Proof.MlKem.X86_64.sample4K, X86_64.abi, X86_64.argRegs]
        exact VG.Proof.MlKem.X86_64.sample4_post h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, VG.Proof.MlKem.X86_64.sample4K, X86_64.abi, X86_64.argRegs] at h
        sig_split h
        sig_reduce [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, VG.Proof.MlKem.X86_64.sample4K, X86_64.abi, X86_64.argRegs]
        sig_simp [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, VG.Proof.MlKem.X86_64.sample4K, X86_64.abi, X86_64.argRegs]
          [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first | with_reducible assumption | exact map_toNat_inj ‹_›
      sat := by
        sig_implies_sat [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, VG.Proof.MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] [sample4Sat] using VG.Proof.MlKem.X86_64.sample4Sat }

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.S4Scalar`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4`, verified

The baseline implementation of `vg_mlkem_sample_ntt4` calls
`vg_mlkem_sample_ntt` on each seed, between the prologue and the epilogue of
the one for AVX2; its proofs are the pieces of that one's for the calls
(`S4Parse.lean`, `S4CT.lean`), with nothing to keep of the memory but the
polynomials already sampled.
-/

namespace VG.Proof.MlKem.X86_64.S4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Spec.MlKem

/-- Nothing of the memory. -/
abbrev NoX (_ : Mem) : Prop := True

section
variable {σ : State} (hp : VG.Proof.MlKem.X86_64.S4.Pre σ)
include hp

theorem callK_ok' {K : Nat} (hK : K < 4) {s : State} (h : VG.Proof.MlKem.X86_64.S4.PC VG.Proof.MlKem.X86_64.S4.NoX σ K s) : WP isa (callK K) s (VG.Proof.MlKem.X86_64.S4.PC VG.Proof.MlKem.X86_64.S4.NoX σ (K + 1)) :=
  WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.argsK_ok hK h) fun _ h₂ => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.callK_ok hp hK (fun _ _ _ _ => trivial) h₂)
    fun _ h₃ => VG.Proof.MlKem.X86_64.S4.andK_ok h₃))

theorem scalar_body_ok {s : State} (h : VG.Proof.MlKem.X86_64.S4.I0 σ s) :
    WP isa (.seq (callK 0) (.seq (callK 1) (.seq (callK 2) (.seq (callK 3) (.block epi))))) s fun s' =>
      sample4K.post σ s' ∧ gprPreserved σ s' := by
  have p₀ : VG.Proof.MlKem.X86_64.S4.PC VG.Proof.MlKem.X86_64.S4.NoX σ 0 s := ⟨h.env, trivial, by rw [h.r14]; rfl, fun _ h _ _ => absurd h (by omega)⟩
  exact WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.callK_ok' hp (by decide) p₀) fun _ p₁ => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.callK_ok' hp (by decide) p₁)
    fun _ p₂ => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.callK_ok' hp (by decide) p₂) fun _ p₃ =>
      WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.callK_ok' hp (by decide) p₃) fun _ p₄ => VG.Proof.MlKem.X86_64.S4.end_ok hp p₄))))

end

theorem correct_scalar (σ : State) (hs : sample4K.pre σ) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.Sample4.sampleNTT4 σ t s' ∧ abiPreserved σ s' ∧ sample4K.post σ s' := by
  have hp := VG.Proof.MlKem.X86_64.S4.pre_of hs
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlKem.X86_64.S4.pro_ok hp) fun _ h => VG.Proof.MlKem.X86_64.S4.scalar_body_ok hp h)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

/-- The call on seed `K`, given the taint analysis of its arguments. -/
theorem callK_ct {K : Nat} (hK : K < 4) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.r12, .r13, .rbx])
      (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * K))),
        .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * K))), .mov .rdx (.reg .rbx),
        .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))]) hc).isSome = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.PC VG.Proof.MlKem.X86_64.S4.NoX σ K s) (callK K) (VG.Proof.MlKem.X86_64.S4.R4 fun σ s => VG.Proof.MlKem.X86_64.S4.PC VG.Proof.MlKem.X86_64.S4.NoX σ (K + 1) s) :=
  RelCT.seq (VG.Proof.MlKem.X86_64.S4.args_ct (X := fun _ => VG.Proof.MlKem.X86_64.S4.NoX) hK c) (RelCT.seq (VG.Proof.MlKem.X86_64.S4.call_ct hK fun _ _ _ _ _ _ => trivial) VG.Proof.MlKem.X86_64.S4.and_ct)

theorem ct_scalar : ConstantTime isa sample4K.pre sample4K.pub Impl.MlKem.X86_64.Sample4.sampleNTT4 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq (RelCT.mono (relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.S4.PC VG.Proof.MlKem.X86_64.S4.NoX σ 0 s)
    (fun σ s hp h => by
      subst h
      exact WP.mono (VG.Proof.MlKem.X86_64.S4.pro_ok (VG.Proof.MlKem.X86_64.S4.pre_of hp)) fun _ h => ⟨h.env, trivial, by rw [h.r14]; rfl, fun _ h _ _ => absurd h (by omega)⟩)
    (taintRel [.rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1]) (by taint_decide))) (fun _ _ h => h) fun _ _ h => h) ?_)
  refine RelCT.seq (VG.Proof.MlKem.X86_64.S4.callK_ct (K := 0) (by decide) (by taint_decide)) (RelCT.seq (VG.Proof.MlKem.X86_64.S4.callK_ct (K := 1) (by decide)
    (by taint_decide)) (RelCT.seq (VG.Proof.MlKem.X86_64.S4.callK_ct (K := 2) (by decide) (by taint_decide))
      (RelCT.seq (VG.Proof.MlKem.X86_64.S4.callK_ct (K := 3) (by decide) (by taint_decide)) ?_)))
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlKem.X86_64.S4.env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlKem.X86_64.S4

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

theorem sample4_scalar_verified : Verified X86_64.target Impl.MlKem.X86_64.Sample4.sampleNTT4
    (Spec.MlKem.sampleNTT4Contract X86_64.abi 24) :=
  Verified.of_correct S4.correct_scalar S4.ct_scalar
    { pre := by sig_implies_pre [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, VG.Proof.MlKem.X86_64.sample4K, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, VG.Proof.MlKem.X86_64.sample4K, X86_64.abi, X86_64.argRegs]
        exact VG.Proof.MlKem.X86_64.sample4_post h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, VG.Proof.MlKem.X86_64.sample4K, X86_64.abi, X86_64.argRegs] at h
        sig_split h
        sig_reduce [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, VG.Proof.MlKem.X86_64.sample4K, X86_64.abi, X86_64.argRegs]
        sig_simp [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, VG.Proof.MlKem.X86_64.sample4K, X86_64.abi, X86_64.argRegs]
          [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first | with_reducible assumption | exact map_toNat_inj ‹_›
      sat := by
        sig_implies_sat [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, VG.Proof.MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] [sample4Sat] using VG.Proof.MlKem.X86_64.sample4Sat }

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl`. -/
section

/-!
# Implementations of `vg_mlkem_sample_ntt4` on x86-64

A `Sample4Impl` is what a function that calls `vg_mlkem_sample_ntt4` needs
of it, so that its proof holds for every implementation: each is a variant
of the interface `MlKemSample4` on x86-64 (`Variants/MlKemSample4/X86_64/`),
and each caller (the top-level functions of ML-KEM-768 and ML-KEM-1024, in
`Generic/MlKemSample4/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Both implementations use 24 bytes of stack below their
return address (`vg_mlkem_sample_ntt`'s calls, three deep).

Each also comes with the computation of several outputs of `PRF₂` that its
callers inline (`Callee4.prfs`): one at a time for the baseline, and four
at a time with AVX2 for `vg_mlkem_sample_ntt4_avx2` (`Prfs.lean`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- An implementation of `vg_mlkem_sample_ntt4` on x86-64. -/
structure Sample4Impl where
  /-- Its symbol and code. -/
  callee : Impl.MlKem.X86_64.Callee4
  /-- It is correct. -/
  ok : ∀ s, sample4K.pre s → ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ sample4K.post s s'
  /-- It is constant time. -/
  ct : ConstantTime isa sample4K.pre sample4K.pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- Its calls are at most three deep. -/
  depth_le : callee.code.depth ≤ 3
  /-- It keeps MXCSR's control bits. -/
  mxcsr : ctlOk callee.code = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- Its outputs of `PRF₂` are correct. -/
  prfs_ok : ∀ {rbs wbs : List (Reg × Nat)} {s : State}, VG.Proof.MlKem.X86_64.Lay rbs wbs s → (∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) →
    ∀ {N₀ n o wl : Nat}, N₀ + n + 4 ≤ 256 → VG.Proof.MlKem.X86_64.prfsChk (rbs ++ wbs) wbs n o wl = true →
      WP isa (callee.prfs N₀ n o wl) s (VG.Proof.MlKem.X86_64.PrfsPost s N₀ n o wl)
  /-- They are constant time. -/
  prfs_tr : ∀ {rbs wbs : List (Reg × Nat)}, (∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlKem.X86_64.bases) →
    ∀ {N₀ n o wl : Nat}, N₀ + n + 4 ≤ 256 → VG.Proof.MlKem.X86_64.prfsChk (rbs ++ wbs) wbs n o wl = true →
      RelCT isa (VG.Proof.MlKem.X86_64.LRel rbs wbs) (callee.prfs N₀ n o wl) fun _ _ => True
  prfs_ctl : ∀ N₀ n o wl, ctlOk (callee.prfs N₀ n o wl) = true
  prfs_sp : ∀ N₀ n o wl, (callee.prfs N₀ n o wl).all (fun i => !isa.writesSp i) = true
  /-- The polynomial arithmetic that goes with it is correct, constant
  time, and safe to call. -/
  arith : VG.Proof.MlKem.X86_64.ArithOk callee.arith
  /-- What the names of its callers' instances end with (e.g. `_avx2`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- How its callers compute the outputs of `PRF₂`, for their documentation. -/
  prfsDoc : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace Sample4Impl

/-- The baseline implementation, `vg_mlkem_sample_ntt4`, which calls `vg_mlkem_sample_ntt`. -/
def scalar : VG.Proof.MlKem.X86_64.Sample4Impl where
  callee := .scalar
  ok := S4.correct_scalar
  ct := S4.ct_scalar
  nosp := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)
  depth_le := by decide +kernel
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  prfs_ok := fun L hcs => VG.Proof.MlKem.X86_64.prfsScalar_ok L hcs
  prfs_tr := fun hcs => VG.Proof.MlKem.X86_64.prfsScalar_tr hcs
  prfs_ctl := VG.Proof.MlKem.X86_64.prfsScalar_ctl
  prfs_sp := VG.Proof.MlKem.X86_64.prfsScalar_sp
  arith := ArithOk.sse
  suffix := ""
  prfsDoc := "one at a time"
  features := []

/-- The AVX2 implementation, `vg_mlkem_sample_ntt4_avx2`. -/
def avx2 : VG.Proof.MlKem.X86_64.Sample4Impl where
  callee := .avx2
  ok := S4.correct
  ct := S4.ct
  nosp := VG.Proof.MlKem.X86_64.nosp_of (by decide +kernel)
  depth_le := by decide +kernel
  mxcsr := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)
  prfs_ok := fun L hcs => VG.Proof.MlKem.X86_64.prfsAvx2_ok L hcs
  prfs_tr := fun hcs => VG.Proof.MlKem.X86_64.prfsAvx2_tr hcs
  prfs_ctl := VG.Proof.MlKem.X86_64.prfsAvx2_ctl
  prfs_sp := VG.Proof.MlKem.X86_64.prfsAvx2_sp
  arith := ArithOk.avx2
  suffix := "_avx2"
  prfsDoc := "four at a time, with AVX2 (and the first one or two of `4k + 1` or `4k + 2` on their own)"
  features := ["avx", "avx2"]

end Sample4Impl

open Lean Elab Tactic in
/-- Fails if the goal mentions the variable `v`: the kernel evaluates only
code that does not call the implementation `v`, each part once (rather than
failing on code that does, after evaluating its other parts). -/
elab "closed_in " v:ident : tactic => withMainContext do
  let e ← elabTerm v none
  if (← instantiateMVars (← getMainTarget)).containsFVar e.fvarId! then
    throwError "the goal mentions {e}"

/-- `ctlOk` of code that calls the implementation `v`: evaluated by the
kernel but for the calls of `v`. -/
macro "s4_ctl " v:ident : tactic =>
  `(tactic| repeat' (first | (closed_in $v; decide +kernel) | apply ctlOk_seq | apply ctlOk_ite |
    (apply ctlOk_call; exact ($v).mxcsr) | exact ($v).prfs_ctl _ _ _ _ | exact ($v).arith.mul.ctl |
    exact ($v).arith.ntt.ctl | exact ($v).arith.nttInv.ctl | rfl))

/-- Code that does not call the implementation `v` never writes the stack pointer: by evaluation. -/
macro "s4_sp_closed " v:ident : tactic =>
  `(tactic| (closed_in $v; exact Code.all_of_allInstrs (by decide +kernel)))

/-- That code that calls the implementation `v` never writes the stack pointer. -/
macro "s4_sp " v:ident : tactic =>
  `(tactic| repeat' (first | s4_sp_closed $v | apply all_seq | apply all_ite | (apply all_call; exact ($v).spSafe) |
    exact ($v).prfs_sp _ _ _ _ | exact ($v).arith.mul.sp | exact ($v).arith.ntt.sp | exact ($v).arith.nttInv.sp | rfl))

end VG.Proof.MlKem.X86_64

end
