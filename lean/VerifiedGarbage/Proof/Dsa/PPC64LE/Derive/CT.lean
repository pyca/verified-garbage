module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Front
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Front
import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.SizesRest
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.SizesRest
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.CT
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.CT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Base

/-!
# DSA key derivation on PPC64LE: constant time

`deriveKey_ct`: two runs from states that satisfy `dContract` and agree on its
public data (the arguments' registers, the stack's argument, the domain and
the result) leak the same trace. The entry (`dentry_rel`), the checks of the
domain shared with the other functions (`sizes_rel`, `paramsTail_rel`, for
the public data `dvdOf`: the domain's octets, x's address as the signature's
and `out`'s as the digest's), then the derivation (`dbody_rel`), which
branches on nothing, or the zeroing of `out` (`dzero_rel`), and `restore`
follow one another.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- A call's public data: the layout, the domain and its octets, x's address
(as the signature's) and `out` (as the digest's, of no octets). -/
def dvdOf (s : State) : VD :=
  ⟨dlayOf s, s.gpr .r5, s.gpr .r8, s.gpr .r3, 0,
    Spec.Rsa.bytesAt s.mem (s.gpr .r5) (2 * (s.gpr .r7).toNat + (s.gpr .r9).toNat),
    2 * (s.gpr .r7).toNat + (s.gpr .r9).toNat, (s.gpr .r9).toNat, none,
    2 * (s.gpr .r7).toNat + (s.gpr .r9).toNat⟩

/-- A buffer of the contract apart from `scratch`. -/
theorem dsrc {s : State} {A : Addr} {n k : Nat} (hm : (⟨A, n⟩ : Region) ∈ s.rd)
    (hd : (⟨A, n⟩ : Region).Disjoint ⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩)
    (hn : n < 2 ^ 64) (hk : k ≤ n) {t : State} (hr : t.rd = s.rd) (hw : t.wr = s.wr) : Src t (dlayOf s) A k :=
  ⟨fun i hi => ⟨_, by rw [hr, hw]; exact List.mem_append_left _ hm, Offset.contains_base _ (by omega) (by omega)⟩,
    fun i hi => Pub.ne_of_disjoint hd (by omega) i (by omega)⟩

/-- On entry. -/
def DC0 (v : VD) (s : State) : Prop := dContract.pre s ∧ dvdOf s = v

theorem pins_DC0 : Pins DC0 [.r3, .r5, .r7, .r8, .r9, .r10] := by
  intro v s₁ s₂ h₁ h₂ r hr
  obtain ⟨-, e₁⟩ := h₁
  obtain ⟨-, e₂⟩ := h₂
  have e := e₁.trans e₂.symm
  have hk := congrArg VD.key e
  have hs := congrArg VD.sig e
  have hd := congrArg VD.dig e
  have hL := congrArg VD.L e
  simp only [dvdOf, dlayOf, Lay.mk.injEq] at hk hs hd hL
  obtain ⟨h10, -, h7, h9⟩ := hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hd
  · exact hk
  · exact BitVec.eq_of_toNat_eq h7
  · exact hs
  · exact BitVec.eq_of_toNat_eq h9
  · exact h10

theorem dfront_S0 {v : VD} {s : State} (h : DC0 v s) : WP isa (.block Derive.entry) s (S0 v) := by
  obtain ⟨hp, rfl⟩ := h
  have hL := dlayOf_ok hp
  have hZ := hL.z256
  have hpre := hp
  obtain ⟨-, hrd, -, -, -, -, -, dPS, dXS, -, -, -, -, -, -, -, hpl, -⟩ := hp
  refine WP.mono (dfront_ok hpre) fun t ⟨⟨hr, scr, r2, _, out⟩, k⟩ => ?_
  have Out : Outside (dlayOf s).S 0 (dlayOf s).Z s.mem t.mem :=
    out.mono (Nat.le_refl _) (by simp only [dlayOf] at hZ ⊢; omega)
  have hK : ∀ {u : State}, u.rd = s.rd → u.wr = s.wr →
      Src u (dlayOf s) (s.gpr .r5) (2 * (s.gpr .r7).toNat + (s.gpr .r9).toNat) :=
    fun hr hw => dsrc (A := s.gpr .r5) (by rw [hrd]; simp) dPS (s.gpr .r6).isLt (by omega) hr hw
  exact ⟨⟨hL, hr, scr, hK k.rd k.wr,
    dsrc (A := s.gpr .r8) (k := (s.gpr .r9).toNat) (by rw [hrd]; simp) dXS (s.gpr .r9).isLt
      (Nat.le_refl _) k.rd k.wr,
    src_zero _ _ _ rfl, (hK rfl rfl).kept Out, hK k.rd k.wr, (fun _ h => nomatch h), (fun h => nomatch h),
    Nat.le_refl _⟩, r2, fixL_nil t, trivial⟩

theorem dentry_rel : RelCT isa (Two DC0) (.block Derive.entry) (Two S0) :=
  two_post (two_taint _ pins_DC0 (by taint_decide)) fun _ _ h => dfront_S0 h

theorem dbody_rel : RelCT isa (Two fun v s => K8 v s ∧ True) Derive.body (Two End) :=
  rel_end (two_taint _ (pins_and (pins_PP _)) (by taint_decide)) (fun _ _ h => h.1.1.regs.r21)
    (by rw [← Code.allInstrs_eq]; decide +kernel) (by decide +kernel)

/-- `out` and its length, to zero it. -/
def dzL (v : VD) : List (Reg × BitVec 64) :=
  [(.r16, v.dig), (.r17, BitVec.ofNat 64 (3 * v.L.pl + 2 * v.L.ql)), (.r0, 0)]

theorem pins_dzL : Pins (fun v s => FixL (dzL v) s) [.r16, .r17, .r0] := by
  intro v s₁ s₂ h₁ h₂ r hr
  rw [show [Reg.r16, .r17, .r0] = (dzL v).map Prod.fst from rfl] at hr
  obtain ⟨p, hm, rfl⟩ := List.mem_map.mp hr
  rw [h₁ p hm, h₂ p hm]

theorem dzfront_ok {v : VD} {s : State} (h : Base v s) :
    WP isa (.block (([.addi .r16 .r26 0] : List Instr) ++ getP .r17 ++ getQ .r0 ++
        ([.add .r0 .r0 .r17, .add .r17 .r17 .r0, .add .r17 .r17 .r0, .li .r0 0] : List Instr))) s
      fun t => FixL (dzL v) t := by
  have hr := h.regs
  refine WP.mono (WP.keep [.r16, .r17, .r0] (Q := fun u => u.gpr .r16 = v.dig ∧
      u.gpr .r17 = BitVec.ofNat 64 (3 * v.L.pl + 2 * v.L.ql) ∧ u.gpr .r0 = 0) (by
      unfold getP getQ
      prun [hr.r26, Regs.p_eq hr, Regs.q_eq hr, BitVec.add_zero]
      exact ⟨by simp only [BitVec.ofNat_add_ofNat]; congr 1; omega, rfl⟩) (by decide))
    fun t ⟨⟨a16, a17, a0⟩, _⟩ => ?_
  simp only [FixL, dzL, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, imp_true_iff, and_true]
  exact ⟨a16, a17, a0⟩

theorem dzero_rel {Φ : VD → State → Prop} (h : ∀ v s, Φ v s → Base v s) :
    RelCT isa (Two Φ) Derive.zeroOut (Two End) := by
  refine rel_end ?_ (fun v s hs => (h v s hs).regs.r21) (by decide) (by decide)
  unfold Derive.zeroOut
  exact RelCT.seq (two_post (two_taint [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)) fun v s hs => dzfront_ok (h v s hs))
    (two_taint _ pins_dzL (by taint_decide))

theorem dcheck_rel : RelCT isa (Two S0) (checkParams Derive.body Derive.zeroOut) (Two End) :=
  (sizes_rel (G := fun _ => True) (paramsTail_rel dbody_rel
      fun _ h => dzero_rel fun v s h' => (h v s h').1) fun _ h => dzero_rel fun v s h' => (h v s h').1).mono
    (fun _ _ => two_mono fun _ _ h => ⟨h, trivial⟩) fun _ _ h => h

theorem deriveKey_rel : RelCT isa (Two DC0) Derive.derive fun _ _ => True := by
  unfold Derive.derive
  exact RelCT.seq dentry_rel (RelCT.seq dcheck_rel (two_taint _ pins_End (by taint_decide)))

/-- Runs that agree on the contract's public data have the same public data `dvdOf`. -/
theorem dvdOf_eq {s t : State} (hs : dContract.pre s) (hp : dContract.pub s t) : dvdOf s = dvdOf t := by
  obtain ⟨-, h3, h4, h5, h6, h7, h8, h9, h10, a0, hl⟩ := hp
  obtain ⟨e, -⟩ := List.append_inj' hl rfl
  have e := map_toNat_inj e
  have hk := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [← h5, ← h6, hk] at e
  simp only [dvdOf, dlayOf, ← h3, ← h5, ← h7, ← h8, ← h9, ← h10, ← a0, e]

theorem deriveKey_ct : ConstantTime isa dContract.pre dContract.pub Derive.derive :=
  RelCT.constantTime (deriveKey_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨dvdOf s, ⟨hs, rfl⟩, ⟨ht, (dvdOf_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.PPC64LE
