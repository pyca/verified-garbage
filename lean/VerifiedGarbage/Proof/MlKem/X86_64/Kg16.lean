module

public import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
public import VerifiedGarbage.Proof.MlKem.X86_64.EncBase
public import VerifiedGarbage.Impl.MlKem.X86_64.Frag16
public import VerifiedGarbage.Proof.MlKem.X86_64.FragKpke
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
public import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.MlKem.X86_64.FragOf
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
public import VerifiedGarbage.Impl.MlKem.X86_64.Kem16
public import VerifiedGarbage.Proof.MlKem.X86_64.FragS4
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragS4
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `MlKem.X86_64.FragS4_16`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: four entries of a matrix with 16-bit coefficients at once

As `FragS4.lean`, with the implementation's code for 16-bit coefficients
(`S16Ok`, from `Sample4Impl.s16`): the four polynomials from `a` are 512 bytes each
(`poly4W true`), and the working space 8192 bytes (`sample4At16_ok`,
`quad16_ok`, `quad16_tr`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {rbs wbs : List (Reg × Nat)}

/-! ## The call -/

/-- The seeds, the four polynomials from `sc oa` and the working space at `sc oz`. -/
def s4_16Chk (bs wbs : List (Reg × Nat)) (oa oz : Nat) : Bool :=
  rdOk bs (sc 0) 136 && wrOk bs wbs (sc oa) 2048 && wrOk bs wbs (sc oz) 8192 && sepB bs (sc 0) 136 (sc oa) 2048 &&
    sepB bs (sc 0) 136 (sc oz) 8192 && sepB bs (sc oa) 2048 (sc oz) 8192

/-- What a call of `vg_mlkem_sample_ntt4` of the seeds at `scratch` to `sc oa` needs. -/
structure S4H16 (oa oz : Nat) (s : State) : Prop where
  offA : oa < 2 ^ 31
  offZ : oz < 2 ^ 31
  dSA : Region.Disjoint ⟨pa s (sc 0), 136⟩ ⟨pa s (sc oa), 2048⟩
  dSZ : Region.Disjoint ⟨pa s (sc 0), 136⟩ ⟨pa s (sc oz), 8192⟩
  dAZ : Region.Disjoint ⟨pa s (sc oa), 2048⟩ ⟨pa s (sc oz), 8192⟩
  kS : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 0), 136⟩
  kA : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc oa), 2048⟩
  kZ : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc oz), 8192⟩
  nwA : (pa s (sc oa)).toNat + 2048 ≤ 2 ^ 64
  nwZ : (pa s (sc oz)).toNat + 8192 ≤ 2 ^ 64
  c : Covers ([⟨pa s (sc 0), 136⟩] ++ [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]) (s.rd ++ s.wr)
  w : Covers [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] s.wr

theorem S4H16.of {s : State} (L : Lay rbs wbs s) {oa oz : Nat} (hc : s4_16Chk (rbs ++ wbs) wbs oa oz = true) :
    S4H16 oa oz s := by
  simp only [s4_16Chk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨_, hrs⟩, ⟨hoa, hra⟩, hwa⟩, ⟨hoz, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩ := hc
  exact ⟨hoa, hoz, L.disj s1, L.disj s2, L.disj s3, L.stkD hrs, L.stkD hra, L.stkD hrz, L.nwp hra, L.nwp hrz,
    covers_append (covers_cons (L.cR hrs) covers_nil) (covers_cons (L.cR hra) (covers_cons (L.cR hrz) covers_nil)),
    covers_cons (L.cW hwa) (covers_cons (L.cW hwz) covers_nil)⟩

theorem s4_16Pre {oa oz : Nat} {s s1 : State} (h : S4H16 oa oz s)
    (hv : s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = pa s (sc oa) ∧ s1.gpr .rdx = pa s (sc oz))
    (k : Keep argRegs s s1) :
    (sample4KW true).pre (s1.callEntry.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [sample4KW, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), hv.1, hv.2.1, hv.2.2]
  exact ⟨trivial, rfl, h.dSA, h.dSZ, h.dAZ, ret_disj s1 (by rw [hsp]; exact h.kS),
    ret_disj s1 (by rw [hsp]; exact h.kA), ret_disj s1 (by rw [hsp]; exact h.kZ),
    stk_disj24 s1 (by rw [hsp]; exact h.kS), stk_disj24 s1 (by rw [hsp]; exact h.kA),
    stk_disj24 s1 (by rw [hsp]; exact h.kZ), h.nwA, h.nwZ⟩

/-- What a call of `vg_mlkem_sample_ntt4` leaves. -/
structure S4Post16 (oa oz : Nat) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  frame : Frame ([⟨pa s (sc oa), 2048⟩, ⟨pa s (sc oz), 8192⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem
  r15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (if all4 s.mem (pa s (sc 0)) then 1 else 0))
  res : ∀ k < 4, ∀ f, sampleNTT minIterations (seed4 s.mem (pa s (sc 0)) k) = some f →
    PolyIsW 16 s'.mem (poly4W true (pa s (sc oa)) k) f

theorem S4Post16.b {oa oz : Nat} {s s' : State} (h : S4Post16 oa oz s s') :
    PPostB s s' [(sc oa, 2048), (sc oz, 8192)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

theorem sample4At16_ok {n : String} {c : Prog isa} (v : S16Ok c) {oa oz : Nat} {s : State} (h : S4H16 oa oz s) :
    WP isa (sample4At16 (n, c) (sc oa) (sc oz)) s (S4Post16 oa oz s) := by
  have hd := v.depth_le
  refine WP.seq (WP.mono (s4Glue_ok oa oz h.offA h.offZ s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine WP.seq (WP.call v.ok v.nosp (by omega_using [hd]) (s4_16Pre h hv k) (by rw [k.2.1, k.2.2]; exact h.c)
    (by rw [k.2.2]; exact h.w) fun s2 hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_)
  refine WP.mono (and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  have hsd : ∀ k < 4, seed4 s1.callEntry.mem (pa s (sc 0)) k = seed4 s.mem (pa s (sc 0)) k := fun k hk => by
    unfold seed4
    rw [ce_bytesAt s1 (p := pa s (sc 0) + BitVec.ofNat 64 (34 * k)) (n := 34) (by decide) (by rw [hsp]; exact h.kS.sub_right (Offset.sub_base _ (by omega_using [hk]))), hm]
  simp only [sample4KW, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2.1, hm₂] at hpost
  rw [hg₂ .rax (by decide), range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
    (hsd k hk)] at hpost
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_,
    fun j hj f hf => ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm, ← hsp]
    exact Frame.below_mono hf (by omega_using [hd]) (by omega_using [])
  · rw [h15, hcs .r15 (by decide), k.gpr (by decide), hpost.1]
  · rw [hm3]; exact hpost.2 j hj f (by rw [hsd j hj]; exact hf)

theorem sample4At16_tr {n : String} {c : Prog isa} (v : S16Ok c) {oa oz : Nat} :
    RelCT isa (fun x y => S4H16 oa oz x ∧ S4H16 oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp ∧
      bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136)
      (sample4At16 (n, c) (sc oa) (sc oz)) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (S4H16 oa oz x ∧ S4H16 oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr .rsp = y.gpr .rsp ∧ bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136) ∧
      (((x1.gpr .rdi = pa x (sc 0) ∧ x1.gpr .rsi = pa x (sc oa) ∧ x1.gpr .rdx = pa x (sc oz)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = pa y (sc 0) ∧ y1.gpr .rsi = pa y (sc oa) ∧ y1.gpr .rdx = pa y (sc oz)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨s4Glue_ok oa oz hx.offA hx.offZ x, s4Glue_ok oa oz hy.offA hy.offZ y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.seq (RelCT.callEx v.ok v.ct ?_)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
  rintro x1 y1 ⟨x, y, ⟨hx, hy, e1, e3, e4⟩, ⟨⟨hv1, hm1⟩, k1⟩, ⟨⟨hv2, hm2⟩, k2⟩⟩
  have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
  have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
  refine ⟨_, _, _, _, s4_16Pre hx hv1 k1, s4_16Pre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
    by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
    by rw [hs1, hs2, e3]⟩
  simp only [sample4KW, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
    ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2]
  rw [ce_bytesAt x1 (n := 136) (by decide) (by rw [hs1]; exact hx.kS),
    ce_bytesAt y1 (n := 136) (by decide) (by rw [hs2]; exact hy.kS), hm1, hm2, e4]
  simp only [pa, e1, hs1, hs2, e3, and_self]

/-! ## Four entries -/

/-- What entries `e₀, …, e₀ + 3` write. -/
abbrev quad16W (oa oz : Nat) : List (Ptr × Nat) :=
  seedW 0 ++ seedW 1 ++ seedW 2 ++ seedW 3 ++ [(sc oa, 2048), (sc oz, 8192)]

def quad16Chk (bs wbs : List (Reg × Nat)) (oa oz : Nat) : Bool :=
  seedsChk bs wbs 0 && seedsChk bs wbs 1 && seedsChk bs wbs 2 && seedsChk bs wbs 3 && s4_16Chk bs wbs oa oz

theorem quad16Chk_spec {bs wbs : List (Reg × Nat)} {oa oz : Nat} (hc : quad16Chk bs wbs oa oz = true) :
    seedsChk bs wbs 0 = true ∧ seedsChk bs wbs 1 = true ∧ seedsChk bs wbs 2 = true ∧ seedsChk bs wbs 3 = true ∧
      s4_16Chk bs wbs oa oz = true := by
  simp only [quad16Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  exact ⟨h0, h1, h2, h3, h4⟩

/-- The four seeds, then `vg_mlkem_sample_ntt4`, in a layout. -/
theorem quad16_4_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {ρ : List Byte}
    {n e₀ : Nat} (he : e₀ + 4 ≤ 256) {oa oz : Nat} (hc : quad16Chk (rbs ++ wbs) wbs oa oz = true)
    (h : SeedsIs ρ n e₀ 0 s) {p : String × Prog isa} {Q : State → Prop}
    (hQ : ∀ s₄, PPost s s₄ (seedW 0 ++ seedW 1 ++ seedW 2 ++ seedW 3) → SeedsIs ρ n e₀ 4 s₄ →
      Lay rbs wbs s₄ → WP isa (sample4At16 p (sc oa) (sc oz)) s₄ Q) :
    WP isa (quad16 p n e₀ (sc oa) (sc oz)) s Q := by
  obtain ⟨c0, c1, c2, c3, _⟩ := quad16Chk_spec hc
  unfold quad16
  refine WP.seq (WP.mono (seed_step L hcs (by omega_using [he]) c0 h) fun s₁ ⟨P₁, h₁⟩ => ?_)
  have L₁ := L.post P₁.b hcs
  refine WP.seq (WP.mono (seed_step L₁ hcs (by omega_using [he]) c1 h₁) fun s₂ ⟨P₂, h₂⟩ => ?_)
  have L₂ := L₁.post P₂.b hcs
  refine WP.seq (WP.mono (seed_step L₂ hcs (by omega_using [he]) c2 h₂) fun s₃ ⟨P₃, h₃⟩ => ?_)
  have L₃ := L₂.post P₃.b hcs
  refine WP.seq (WP.mono (seed_step L₃ hcs (by omega_using [he]) c3 h₃) fun s₄ ⟨P₄, h₄⟩ => ?_)
  exact hQ s₄ (PPost.app (PPost.app (PPost.app P₁ P₂ (by decide)) P₃ (by decide)) P₄ (by decide)) h₄
    (L₃.post P₄.b hcs)

theorem quad16_ok {n' : String} {c : Prog isa} (v : S16Ok c) {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases)
    {n e₀ : Nat} (he : e₀ + 4 ≤ 256) {oa oz : Nat} (hc : quad16Chk (rbs ++ wbs) wbs oa oz = true) :
    WP isa (quad16 (n', c) n e₀ (sc oa) (sc oz)) s fun s' => PPostB s s' (quad16W oa oz) ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (List.range 4).all (fun k => (sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e₀ + k) / n) ((e₀ + k) % n))).isSome) then 1 else 0)) ∧
      ∀ k < 4, ∀ f, sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e₀ + k) / n) ((e₀ + k) % n)) = some f →
        PolyIsW 16 s'.mem (pa s (sc (oa + 512 * k))) f := by
  refine quad16_4_ok L hcs he hc ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ fun s₄ P h₄ L₄ => ?_
  refine WP.mono (sample4At16_ok (n := n') v (S4H16.of L₄ (quad16Chk_spec hc).2.2.2.2)) fun s' h' => ?_
  have ea : pa s₄ (sc oa) = pa s (sc oa) := P.pa rbx_cs
  refine ⟨PPostB.app P.b h'.b (by simp [bases]), ?_, fun k hk f hf => ?_⟩
  · rw [h'.r15, P.cs .r15 (by decide), all4, range_all_congr fun k hk => congrArg
      (fun B => (sampleNTT minIterations B).isSome) (seed4_eq h₄ hk)]
  · have := h'.res k hk f (by rw [seed4_eq h₄ hk]; exact hf)
    rwa [poly4W, pBytes_true, ea, pa, off_add] at this

/-! ## Constant time -/

/-- The constant time of the four entries, for a given `ρ`. -/
theorem quad16_tr {n' : String} {c : Prog isa} (v : S16Ok c) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {ρ : List Byte} {n e₀ : Nat}
    (he : e₀ + 4 ≤ 256) (hij : ∀ k < 4, (e₀ + k) / n < 4 ∧ (e₀ + k) % n < 4) {oa oz : Nat}
    (hc : quad16Chk (rbs ++ wbs) wbs oa oz = true) :
    RelCT isa (RQ rbs wbs ρ n e₀ 0) (quad16 (n', c) n e₀ (sc oa) (sc oz)) fun _ _ => True := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := quad16Chk_spec hc
  have hin : inB (rbs ++ wbs) (sc 0) 136 = true := by
    simp only [s4_16Chk, rdOk, Bool.and_eq_true] at c4; exact c4.1.1.1.1.1.2
  unfold quad16
  refine RelCT.seq (seed_tr hcs (by omega_using [he]) (by decide) (hij 0 (by decide)).1 (hij 0 (by decide)).2 c0) ?_
  refine RelCT.seq (seed_tr hcs (by omega_using [he]) (by decide) (hij 1 (by decide)).1 (hij 1 (by decide)).2 c1) ?_
  refine RelCT.seq (seed_tr hcs (by omega_using [he]) (by decide) (hij 2 (by decide)).1 (hij 2 (by decide)).2 c2) ?_
  refine RelCT.seq (seed_tr hcs (by omega_using [he]) (by decide) (hij 3 (by decide)).1 (hij 3 (by decide)).2 c3) ?_
  refine RelCT.mono (sample4At16_tr (n := n') v) (fun x y h => ⟨S4H16.of h.1.1 c4, S4H16.of h.1.2.1 c4, h.1.eq hin, h.1.2.2.2, ?_⟩)
    fun _ _ h => h
  rw [bytesAt136, bytesAt136, seed4_eq h.2.1 (k := 0) (by decide), seed4_eq h.2.1 (k := 1) (by decide),
    seed4_eq h.2.1 (k := 2) (by decide), seed4_eq h.2.1 (k := 3) (by decide), seed4_eq h.2.2 (k := 0) (by decide),
    seed4_eq h.2.2 (k := 1) (by decide), seed4_eq h.2.2 (k := 2) (by decide), seed4_eq h.2.2 (k := 3) (by decide)]

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.Kg16Tail`, which this module and modules that import it used -/

section

/-! ### `MlKem.X86_64.FragS16`, which only this module used -/

section

/-! ### `MlKem.X86_64.Frag16Prim`, which only this module used -/

section

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
    exact Frame.below_mono hf (by omega_using []) (by omega_using [])
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

end

end


/-!
# ML-KEM on x86-64: `SamplePolyCBD₂` and `Â[i, j]` with 16-bit coefficients, in a layout

As `FragL.lean`'s `cbd2At_okL` and `FragS.lean`'s `sampleIJ_ok`, for
polynomials of 16-bit coefficients (512 bytes), with the working space `z`
(2048 bytes) of `vg_mlkem16_sample_ntt`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable {rbs wbs : List (Reg × Nat)}

/-! ## `SamplePolyCBD₂` -/

theorem cbd2_16At_okL {A : Arith} (hA : ArithOk A) {s : State} (L : Lay rbs wbs s) {p q : Ptr} (hq : NA q)
    (hc : twoChk (rbs ++ wbs) wbs p 128 q 512 = true) :
    WP isa (cbd2_16At A p q) s fun s' => PPost s s' [(q, 512)] ∧
      PolyIsW 16 s'.mem (pa s q) (samplePolyCBD 2 (bytesAt s.mem (pa s p) 128)) :=
  cbd2_16At_ok hA hq (TwoH.of L hc)

theorem cbd2_16At_trL {A : Arith} (hA : ArithOk A) {p q : Ptr} (hq : NA q)
    (hc : twoChk (rbs ++ wbs) wbs p 128 q 512 = true) :
    RelCT isa (LRel rbs wbs) (cbd2_16At A p q) fun _ _ => True :=
  RelCT.mono (cbd2_16At_tr hA hq) (fun _ _ e => ⟨TwoH.of e.1 hc, TwoH.of e.2.1 hc, e.eq (twoChk_in hc).1,
    e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

/-! ## `SampleNTT` of the seed at `SB` -/

/-- The checks of a call of `vg_mlkem16_sample_ntt` to `a`, with the working space `z`. -/
def samp16Chk (bs wbs : List (Reg × Nat)) (a z : Ptr) : Bool :=
  rdOk bs (sc oSB) 34 && wrOk bs wbs a 512 && wrOk bs wbs z 2048 && sepB bs (sc oSB) 34 a 512 &&
    sepB bs (sc oSB) 34 z 2048 && sepB bs a 512 z 2048

theorem samp16Chk_in {bs wbs : List (Reg × Nat)} {a z : Ptr} (hc : samp16Chk bs wbs a z = true) :
    inB bs (sc oSB) 34 = true ∧ inB bs a 512 = true ∧ inB bs z 2048 = true := by
  simp only [samp16Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨rdOk_in h1, wrOk_in h2, wrOk_in h3⟩

theorem SampH16.of {s : State} (L : Lay rbs wbs s) {a z : Ptr} (hc : samp16Chk (rbs ++ wbs) wbs a z = true) :
    SampH16 a z s := by
  simp only [samp16Chk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨_, hrs⟩, ⟨hoa, hra⟩, hwa⟩, ⟨hoz, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩ := hc
  exact ⟨hoa, hoz, L.disj s1, L.disj s2, L.disj s3, L.stkD hrs, L.stkD hra, L.stkD hrz, L.nwp hrz,
    covers_append (covers_cons (L.cR hrs) covers_nil) (covers_cons (L.cR hra) (covers_cons (L.cR hrz) covers_nil)),
    covers_cons (L.cW hwa) (covers_cons (L.cW hwz) covers_nil)⟩

/-- What `vg_mlkem16_sample_ntt` leaves, as `PostB`. -/
theorem SampPost16.b {a z : Ptr} {s s' : State} (h : SampPost16 a z s s') :
    PPostB s s' [(a, 512), (z, 2048)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

theorem sampleAt16_trL {a z : Ptr} (hna : NA a) (hnz : NA z) (hc : samp16Chk (rbs ++ wbs) wbs a z = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ bytesAt x.mem (pa x (sc oSB)) 34 = bytesAt y.mem (pa y (sc oSB)) 34)
      (sampleAt16 a z) fun _ _ => True :=
  RelCT.mono (sampleAt16_tr hna hnz) (fun _ _ ⟨e, hb⟩ => ⟨SampH16.of e.1 hc, SampH16.of e.2.1 hc,
    e.eq (samp16Chk_in hc).1, e.eq (samp16Chk_in hc).2.1, e.eq (samp16Chk_in hc).2.2, e.2.2.2, hb⟩)
    fun _ _ _ => trivial

/-! ## `Â[i, j]` -/

/-- The checks of `Â[i, j]`: its call, and the two bytes of the seed. -/
def ij16Chk (bs wbs : List (Reg × Nat)) (a z : Ptr) : Bool :=
  samp16Chk bs wbs a z && inB wbs (sc (oSB + 32)) 1 && inB wbs (sc (oSB + 33)) 1 &&
    keepB bs [(sc (oSB + 32), 1)] (sc oSB) 32 && keepB bs [(sc (oSB + 33), 1)] (sc oSB) 32 &&
    keepB bs [(sc (oSB + 33), 1)] (sc (oSB + 32)) 1

theorem ij16Chk_parts {bs wbs : List (Reg × Nat)} {a z : Ptr} (hc : ij16Chk bs wbs a z = true) :
    samp16Chk bs wbs a z = true ∧ inB wbs (sc (oSB + 32)) 1 = true ∧ inB wbs (sc (oSB + 33)) 1 = true ∧
      keepB bs [(sc (oSB + 32), 1)] (sc oSB) 32 = true ∧ keepB bs [(sc (oSB + 33), 1)] (sc oSB) 32 = true ∧
      keepB bs [(sc (oSB + 33), 1)] (sc (oSB + 32)) 1 = true := by
  simp only [ij16Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The two indices of the seed `ρ ‖ j ‖ i`. -/
theorem setIJ16_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {i j : Nat}
    (hi : i < 256) (hj : j < 256) {a z : Ptr} (hc : ij16Chk (rbs ++ wbs) wbs a z = true) :
    WP isa (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i)) s fun s' =>
      PPost s s' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)]) ∧
      bytesAt s'.mem (pa s' (sc oSB)) 34 = matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j := by
  obtain ⟨_, h32, h33, k1, k2, k3⟩ := ij16Chk_parts hc
  rw [WP.block_append_iff]
  refine WP.mono (setB_okL L (by decide) hj h32) fun s₁ ⟨hP₁, hb₁⟩ => ?_
  have L₁ := L.post hP₁.b hcs
  refine WP.mono (setB_okL L₁ (by decide) hi h33) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have e1 : ∀ o, pa s₁ (sc o) = pa s (sc o) := fun o => hP₁.pa rbx_cs
  have e2 : ∀ o, pa s₂ (sc o) = pa s₁ (sc o) := fun o => hP₂.pa rbx_cs
  have hρ : bytesAt s₂.mem (pa s₂ (sc oSB)) 32 = bytesAt s.mem (pa s (sc oSB)) 32 := by
    rw [L₁.keepBytes hP₂.b k2, L.keepBytes hP₁.b k1]
  have hjb : bytesAt s₂.mem (pa s₂ (sc (oSB + 32))) 1 = [BitVec.ofNat 8 j] := by
    rw [L₁.keepBytes hP₂.b k3, e1]; exact hb₁
  have hib : bytesAt s₂.mem (pa s₂ (sc (oSB + 33))) 1 = [BitVec.ofNat 8 i] := by
    rw [e2]; exact hb₂
  refine ⟨PPost.app hP₁ hP₂ (by decide), seed_eq hρ ?_ ?_⟩
  · refine mem_of_bytesAt_one ?_; rw [← hjb, pa, pa, off_add]
  · refine mem_of_bytesAt_one ?_; rw [← hib, pa, pa, off_add]

theorem sampleIJ16_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {a z : Ptr} (hna : NA a)
    (hnz : NA z) {i j : Nat} (hi : i < 256) (hj : j < 256) (hc : ij16Chk (rbs ++ wbs) wbs a z = true) :
    WP isa (sampleIJ16 a i j z) s fun s' =>
      PPostB s s' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)] ++ [(a, 512), (z, 2048)]) ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j)).isSome then 1 else 0)) ∧
      ∀ f, sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j) = some f →
        PolyIsW 16 s'.mem (pa s a) f := by
  unfold sampleIJ16
  rw [WP.seq_iff]
  refine WP.mono (setIJ16_ok L hcs hi hj hc) fun s₂ ⟨hP₂, hseed⟩ => ?_
  have L₂ := L.post hP₂.b hcs
  refine WP.mono (sampleAt16_ok hna hnz (SampH16.of L₂ (ij16Chk_parts hc).1)) fun s₃ h => ?_
  have hab : a.1 ∈ bases := by
    obtain ⟨n, hn, _⟩ := inB_spec (samp16Chk_in (ij16Chk_parts hc).1).2.1
    exact hcs (a.1, n) hn
  have hzb : z.1 ∈ bases := by
    obtain ⟨n, hn, _⟩ := inB_spec (samp16Chk_in (ij16Chk_parts hc).1).2.2
    exact hcs (z.1, n) hn
  have e3 : pa s₂ a = pa s a := hP₂.b.pa hab
  refine ⟨PPostB.app hP₂.b h.b (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    exacts [hab, hzb]), ?_, fun f hf => ?_⟩
  · rw [h.r15, hseed, hP₂.cs .r15 (by decide)]
  · rw [← e3]; exact h.res f (by rw [hseed]; exact hf)

theorem sampleIJ16_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {a z : Ptr} (hna : NA a) (hnz : NA z)
    {i j : Nat} (hi : i < 256) (hj : j < 256) (hc : ij16Chk (rbs ++ wbs) wbs a z = true)
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i))
      (.block [])).isSome = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ bytesAt x.mem (pa x (sc oSB)) 32 = bytesAt y.mem (pa y (sc oSB)) 32)
      (sampleIJ16 a i j z) fun _ _ => True := by
  have hin : inB (rbs ++ wbs) (sc oSB) 34 = true := (samp16Chk_in (ij16Chk_parts hc).1).1
  unfold sampleIJ16
  refine RelCT.seq (RelCT.postDep (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1.eq hin) ht)
    (F := fun x x' => PPost x x' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)]) ∧
      bytesAt x'.mem (pa x' (sc oSB)) 34 = matSeed (bytesAt x.mem (pa x (sc oSB)) 32) i j)
    (fun x y h => ⟨setIJ16_ok h.1.1 hcs hi hj hc, setIJ16_ok h.1.2.1 hcs hi hj hc⟩)
    fun x y x' y' h hx hy => ⟨h.1.post hcs hx.1.b hy.1.b, by rw [hx.2, hy.2, h.2]⟩)
    (sampleAt16_trL hna hnz (ij16Chk_parts hc).1)

end

end VG.Proof.MlKem.X86_64

end

end


/-!
# ML-KEM on x86-64: key generation with 16-bit polynomials, after the samples

When `Â`, `s` and `e` are sampled as `u16`s (`KRest16`): `vg_mlkem*_kpke_keygen`
writes `t̂` and `ŝ`, encoded, to the keys (`kgCore_eq`: as `K-PKE.KeyGen`
states them), and the rest of the keys is as with polynomials of `u32`s
(`KeyGen.fin_ok`): `tail_ok`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem w16_off (p : Addr) (o j : Nat) :
    p + BitVec.ofNat 64 o + BitVec.ofNat 64 (32 * 16 * j) = p + BitVec.ofNat 64 (o + 512 * j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 * 16 * j = 512 * j by omega_using []]

/-- The matrix of `u16`s from `aP`, from its entries. -/
theorem matAtW_eq {k : Nat} {m : Mem} {aP : Addr} {a : Nat → Nat → Poly}
    (hA : ∀ i < k, ∀ j < k, polyAtW 16 m (aP + BitVec.ofNat 64 (512 * (k * i + j))) = a i j) :
    matAtW 16 m aP k = matrix k a := by
  refine List.map_congr_left fun i hi => List.map_congr_left fun j hj => ?_
  rw [w16_off, show 32 * 16 * (k * i) + 512 * j = 512 * (k * i + j) by omega_using []]
  exact hA i (List.mem_range.mp hi) j (List.mem_range.mp hj)

/-- What `vg_mlkem*_kpke_keygen` writes, as `K-PKE.KeyGen` states it: `t̂` and `ŝ`, encoded. -/
theorem kgCore_eq {L : Kem} {m : Mem} {aP se : Addr} {a : Nat → Nat → Poly} {d : List Byte}
    (hA : ∀ i < L.k, ∀ j < L.k, polyAtW 16 m (aP + BitVec.ofNat 64 (512 * (L.k * i + j))) = a i j)
    (hS : ∀ N < 2 * L.k, polyAtW 16 m (se + BitVec.ofNat 64 (512 * N)) = cbd (KPke.kgSigma L.p d) N) :
    encodeVec (addVec (mulMatVec (matAtW 16 m aP L.k) (sHatW m se L.k)) (eHatW m se L.k)) =
        KPke.catK (fun i => encode12 (KPke.kgT L.p a d i)) L.k ∧
      encodeVec (sHatW m se L.k) = KPke.catK (fun j => encode12 (KPke.kgS L.p d j)) L.k := by
  have eS : sHatW m se L.k = (List.range L.k).map (KPke.kgS L.p d) := by
    simp only [sHatW, vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, KPke.kgS]
    rw [show 32 * 16 * j = 512 * j by omega_using [], hS j (by have := List.mem_range.mp hj; omega_using [this])]
  have eE : eHatW m se L.k = (List.range L.k).map (KPke.kgE L.p d) := by
    simp only [eHatW, vecAtW, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp, KPke.kgE]
    rw [w16_off, ← Nat.mul_add, hS _ (by have := List.mem_range.mp hj; omega_using [this])]
  rw [matAtW_eq hA, eS, eE, KPke.mulMatVec_matrix, KPke.addVec_map, KPke.catK_eq, KPke.catK_eq]
  simp only [encodeVec, List.flatMap_map]
  exact ⟨rfl, trivial⟩

namespace KeyGen16

open KeyGen VG.Impl.MlKem.X86_64.Top16

variable (K : Kem16)

/-- What `vg_mlkem*_kpke_keygen` writes. -/
abbrev kpW : List (Ptr × Nat) :=
  [((.r12, 0), 384 * K.L.k), ((.r13, 0), 384 * K.L.k), (sc K.oR, 1024 * K.L.k), (sc K.oZ, kScrE)]

/-- What entry `e` of `Â` writes. -/
abbrev ijW (e : Nat) : List (Ptr × Nat) :=
  [(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)] ++ [(aP K e, 512), (sc K.oW, 2048)]

/-- A piece writing `ws` keeps `KA` and the first `e` entries of `Â`. -/
def matKeep (e : Nat) (ws : List (Ptr × Nat)) : Bool :=
  kcChk K.L ws && keepB (kgB K.L) ws (sc oG) 32 && keepB (kgB K.L) ws sigP 32 &&
    keepB (kgB K.L) ws (sc oSB) 32 && (List.range e).all fun e' => keepB (kgB K.L) ws (aP K e') 512

/-- Entry `e` of `Â`, on its own. -/
def kbChk (e : Nat) : Bool := ij16Chk (kgB K.L) (kgW K.L) (aP K e) (sc K.oW) && matKeep K e (ijW K e)

/-- Entries `4q, …, 4q + 3` of `Â`, at once. -/
def kqChk (q : Nat) : Bool :=
  quad16Chk (kgB K.L) (kgW K.L) (K.oA + 512 * (4 * q)) K.oW &&
    matKeep K (4 * q) (quad16W (K.oA + 512 * (4 * q)) K.oW)

/-- A piece writing `ws` keeps `KRest16 n`. -/
def restChk (n : Nat) (ws : List (Ptr × Nat)) : Bool :=
  kcChk K.L ws && keepB (kgB K.L) ws (sc oG) 32 && keepB (kgB K.L) ws sigP 32 &&
    (List.range (K.L.k * K.L.k)).all (fun e => keepB (kgB K.L) ws (aP K e) 512) &&
    (List.range (2 * K.L.k)).all (fun N => keepB (kgB K.L) ws (prfO K N) 128) &&
    (List.range n).all (fun N => keepB (kgB K.L) ws (rP K N) 512)

/-- What `prfs` writes. -/
abbrev prW : List (Ptr × Nat) := prfsW (2 * K.L.k) K.oPR (K.oW / 32)

def prChk : Bool :=
  prfsChk (kgB K.L) (kgW K.L) (2 * K.L.k) K.oPR (K.oW / 32) && kcChk K.L (prW K) &&
    keepB (kgB K.L) (prW K) (sc oG) 32 && keepB (kgB K.L) (prW K) sigP 32 &&
    (List.range (K.L.k * K.L.k)).all (fun e => keepB (kgB K.L) (prW K) (aP K e) 512)

def seChk (N : Nat) : Bool :=
  twoChk (kgB K.L) (kgW K.L) (prfO K N) 128 (rP K N) 512 && restChk K N [(rP K N, 512)]

/-- What key generation with 16-bit polynomials needs of the layout, evaluated for each parameter set. -/
structure Kg16Wf : Prop extends KgWfB K.L where
  -- the matrix
  kq : ∀ q < K.L.k * K.L.k / 4, kqChk K q = true
  kb : ∀ e < K.L.k * K.L.k, 4 * (K.L.k * K.L.k / 4) ≤ e → kbChk K e = true
  flagA : ∀ e < K.L.k * K.L.k, keepB (kgB K.L) [] (aP K e) 512 = true
  -- the samples
  pr : prChk K = true
  se : ∀ N < 2 * K.L.k, seChk K N = true
  -- the K-PKE function
  kp : kpChk (kgB K.L) (kgW K.L) K.L (.r12, 0) (.r13, 0) (sc K.oA) (sc K.oR) (sc K.oZ) = true
  kpK : kcChk K.L (kpW K) = true
  kpG : keepB (kgB K.L) (kpW K) (sc oG) 32 = true

instance : CoeOut (Kg16Wf K) (KgWfB K.L) := ⟨Kg16Wf.toKgWfB⟩

/-- After the outputs of `PRF₂` and the first `n` of `s ‖ e`, as `u16`s. -/
structure KRest16 (n : Nat) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK K.L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma K.L.p (kgD σ)
  r15 : s.gpr .r15 = 1
  mat : ∀ e < K.L.k * K.L.k, PolyIsW 16 s.mem (pa s (aP K e)) (aHat (rhoK K.L σ) (e / K.L.k) (e % K.L.k))
  prf : ∀ N < 2 * K.L.k, bytesAt s.mem (pa s (prfO K N)) 128 =
    prf 2 (KPke.kgSigma K.L.p (kgD σ)) (BitVec.ofNat 8 N)
  se : ∀ N < n, PolyIsW 16 s.mem (pa s (rP K N)) (cbd (KPke.kgSigma K.L.p (kgD σ)) N)

theorem sc_w16 (s : State) (o e : Nat) :
    pa s (sc o) + BitVec.ofNat 64 (32 * 16 * e) = pa s (sc (o + 512 * e)) := by
  simp only [pa]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 * 16 * e = 512 * e by omega_using []]

theorem sc_512 (s : State) (o e : Nat) : pa s (sc o) + BitVec.ofNat 64 (512 * e) = pa s (sc (o + 512 * e)) := by
  simp only [pa]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

section
variable {K : Kem16} (W : Kg16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

omit W hp in
theorem KRest16.redA {s : State} (h : KRest16 K (2 * K.L.k) σ s) :
    VecReducedW 16 s.mem (pa s (sc K.oA)) (K.L.k * K.L.k) := fun e he => by
  rw [sc_w16]; exact (h.mat e he).1

omit W hp in
theorem KRest16.redS {s : State} (h : KRest16 K (2 * K.L.k) σ s) :
    VecReducedW 16 s.mem (pa s (sc K.oR)) (2 * K.L.k) := fun N hN => by
  rw [sc_w16]; exact (h.se N hN).1

/-- `t̂` and `ŝ`, encoded to the keys. -/
theorem core_ok (hK : KpkeOk K.L) {s : State} (h : KRest16 K (2 * K.L.k) σ s) :
    WP isa (K.L.kpkeKgAt (.r12, 0) (.r13, 0) (sc K.oA) (sc K.oR) (sc K.oZ)) s (KFinPre K.L σ) := by
  have L₀ := h.kc.lay W hp
  refine WP.mono (kpkeKgAt_okL hK L₀ r13_na rbx_na rbx_na rbx_na W.kp h.redA h.redS)
    fun s' ⟨hP, hek, hdk⟩ => ?_
  have hc := kgCore_eq (L := K.L) (m := s.mem) (aP := pa s (sc K.oA)) (se := pa s (sc K.oR))
    (a := aHat (rhoK K.L σ)) (d := kgD σ)
    (fun i hi j hj => by
      have := (h.mat (K.L.k * i + j) (ij_lt hi hj)).2
      rwa [(divmod_ij hj).1, (divmod_ij hj).2, aP, ← sc_512] at this)
    (fun N hN => by have := (h.se N hN).2; rwa [rP, ← sc_512] at this)
  refine ⟨h.kc.step W hp hP.b W.kpK, by rw [L₀.keepBytes hP.b W.kpG]; exact h.rho,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, ?_, ?_⟩
  · rw [hP.pa r12_cs, hek, hc.1]
  · rw [hP.pa r13_cs, hdk, hc.2]

/-- `ŝ`, `t̂` encoded to the keys, and the keys' last pieces. -/
theorem tail_ok (hK : KpkeOk K.L) {s : State} (h : KRest16 K (2 * K.L.k) σ s) :
    WP isa (kgTail K) s (KFin K.L σ) :=
  WP.seq (WP.mono (core_ok W hp hK h) fun _ h' => fin_ok W hp h')

end

theorem tail_tr {K : Kem16} (hK : KpkeOk K.L) (W : Kg16Wf K) :
    RelCT isa (Rel2 (keyGenK K.L).pre (keyGenK K.L).pub (KRest16 K (2 * K.L.k))) (kgTail K) fun _ _ => True := by
  unfold kgTail
  refine RelCT.seq (relInv (I' := KFinPre K.L) (fun σ s hp hs => core_ok W hp hK hs)
    (rel2_of (kpkeKgAt_trL hK r13_na rbx_na rbx_na rbx_na W.kp)
      fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨kc_lrel W p₁ p₂ pub h₁.kc h₂.kc, ⟨h₁.redA, h₁.redS⟩,
        ⟨h₂.redA, h₂.redS⟩⟩)) ?_
  exact RelCT.mono (fin_tr W fun h => h.kc) (fun _ _ h => h) fun _ _ _ => trivial

end KeyGen16

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.KgA16`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: sampling a matrix of polynomials with 16-bit coefficients

As `KgA.lean`'s `MatB`, `ents_ok` and `ents_tr`, for the matrix `Â` (`k × k`)
whose entry `e = k i + j` is the 512 bytes at `sc (oa + 512 e)` (`ents16`):
after the first `e` entries, `r15` is 1 exactly when all of them succeeded
within 280 iterations (`allOk`), and each one that did holds its polynomial
(`MatB16`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay rbs wbs s) {ws : List (Ptr × Nat)} {p : Ptr}
include L

/-- A polynomial of 16-bit coefficients that a piece does not write is kept. -/
theorem Lay.keepPoly16 {f : Poly} (hP : PPostB s s' ws) (hc : keepB (rbs ++ wbs) ws p 512 = true)
    (h : PolyIsW 16 s.mem (pa s p) f) : PolyIsW 16 s'.mem (pa s' p) f := by
  rw [hP.pa (keepB_cs hc)]
  exact polyIsW_frame true hP.frame (L.fdisj hc) h

end

/-- After the first `e` entries of the `k × k` matrix at `sc oa`: `r15`, and
the entries sampled, for the seed `ρ`. -/
structure MatB16 (k oa : Nat) (ρ : List Byte) (e : Nat) (s : State) : Prop where
  r15 : s.gpr .r15 = if allOk k ρ e then 1 else 0
  mat : ∀ e' < e, ∀ f, sampleNTT minIterations (matSeed ρ (e' / k) (e' % k)) = some f →
    PolyIsW 16 s.mem (pa s (sc (oa + 512 * e'))) f

/-- The step of one entry. -/
theorem MatB16.single {k oa : Nat} {ρ : List Byte} {e : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (h : MatB16 k oa ρ e s) (hsb : bytesAt s.mem (pa s (sc oSB)) 32 = ρ) (Lx : Lay rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (kA : ∀ e' < e, keepB (rbs ++ wbs) ws (sc (oa + 512 * e')) 512 = true)
    (h15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) (e / k) (e % k))).isSome
          then 1 else 0)))
    (hres : ∀ f, sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) (e / k) (e % k)) = some f →
        PolyIsW 16 s'.mem (pa s (sc (oa + 512 * e))) f) : MatB16 k oa ρ (e + 1) s' := by
  refine ⟨?_, fun e' he' f hf => ?_⟩
  · rw [h15, hsb, and_acc h.r15]
    exact ite_congr (propext allOk_succ.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega_using [he'] : e' < e ∨ e' = e) with he' | rfl
    · exact Lx.keepPoly16 hP (kA e' he') (h.mat e' he' f hf)
    · rw [hP.pa rbx_bases]
      exact hres f (by rw [hsb]; exact hf)

/-- The step of four entries. -/
theorem MatB16.four {k oa : Nat} {ρ : List Byte} {e : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (h : MatB16 k oa ρ e s) (hsb : bytesAt s.mem (pa s (sc oSB)) 32 = ρ) (Lx : Lay rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (kA : ∀ e' < e, keepB (rbs ++ wbs) ws (sc (oa + 512 * e')) 512 = true)
    (h15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (List.range 4).all (fun t => (sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e + t) / k) ((e + t) % k))).isSome) then 1 else 0)))
    (hres : ∀ t < 4, ∀ f, sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e + t) / k) ((e + t) % k)) = some f →
        PolyIsW 16 s'.mem (pa s (sc (oa + 512 * e + 512 * t))) f) : MatB16 k oa ρ (e + 4) s' := by
  refine ⟨?_, fun e' he' f hf => ?_⟩
  · rw [h15, hsb, and_acc h.r15]
    exact ite_congr (propext allOk_add4.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega_using [] : e' < e ∨ e ≤ e') with he'' | he''
    · exact Lx.keepPoly16 hP (kA e' he'') (h.mat e' he'' f hf)
    · have := hres (e' - e) (by omega_using [he']) f (by rw [hsb, Nat.add_sub_cancel' he'']; exact hf)
      rw [hP.pa rbx_bases]
      rwa [show oa + 512 * e + 512 * (e' - e) = oa + 512 * e' by omega_using [he'']] at this

theorem MatB16.zero (k oa : Nat) (ρ : List Byte) {s : State} (h15 : s.gpr .r15 = 1) : MatB16 k oa ρ 0 s :=
  ⟨by rw [h15, ifp (allOk_zero _ _)], fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- The entries `e, …, e + n - 1`, from any invariant `I e` whose steps are
those of one entry and of four (`ents16`). -/
theorem ents16_ok (p : String × Prog isa) (k oa : Nat) (scr : Ptr) {I : Nat → State → Prop}
    (h1 : ∀ e < k * k, 4 * (k * k / 4) ≤ e → ∀ s, I e s →
      WP isa (sampleIJ16 (sc (oa + 512 * e)) (e / k) (e % k) scr) s (I (e + 1)))
    (h4 : ∀ q < k * k / 4, ∀ s, I (4 * q) s →
      WP isa (quad16 p k (4 * q) (sc (oa + 512 * (4 * q))) scr) s (I (4 * q + 4))) :
    ∀ n e, e + n = k * k → (e % 4 = 0 ∨ 4 * (k * k / 4) ≤ e) → ∀ s, I e s →
      WP isa (ents16 p k oa scr e n) s (I (e + n))
  | 0, e, _, _, s, hs => by simp only [ents16]; exact WP.block_nil hs
  | 1, e, he, hq, s, hs => by
    simp only [ents16]; exact h1 e (by omega_using [he]) (by omega_using [he, hq]) s hs
  | 2, e, he, hq, s, hs => by
    simp only [ents16]
    exact WP.seq (WP.mono (h1 e (by omega_using [he]) (by omega_using [he, hq]) s hs) fun s₁ h₁ =>
      ents16_ok p k oa scr h1 h4 1 (e + 1) (by omega_using [he]) (by omega_using [he, hq]) s₁ h₁)
  | 3, e, he, hq, s, hs => by
    simp only [ents16]
    refine WP.seq (WP.mono (h1 e (by omega_using [he]) (by omega_using [he, hq]) s hs) fun s₁ h₁ => ?_)
    have := ents16_ok p k oa scr h1 h4 2 (e + 1) (by omega_using [he]) (by omega_using [he, hq]) s₁ h₁
    rwa [show e + 1 + 2 = e + 3 by omega_using []] at this
  | 4, e, he, hq, s, hs => by
    simp only [ents16]
    have := h4 (e / 4) (by omega_using [he]) s (by rwa [show 4 * (e / 4) = e by omega_using [he, hq]])
    rwa [show 4 * (e / 4) = e by omega_using [he, hq]] at this
  | n + 5, e, he, hq, s, hs => by
    simp only [ents16]
    have := h4 (e / 4) (by omega_using [he]) s (by rwa [show 4 * (e / 4) = e by omega_using [he, hq]])
    rw [show 4 * (e / 4) = e by omega_using [he, hq]] at this
    refine WP.seq (WP.mono this fun s₁ h₁ => ?_)
    have := ents16_ok p k oa scr h1 h4 (n + 1) (e + 4) (by omega_using [he]) (by omega_using [hq]) s₁ h₁
    rwa [show e + 4 + (n + 1) = e + (n + 5) by omega_using []] at this

theorem samples16_ok' (p : String × Prog isa) (k oa : Nat) (scr : Ptr) {I : Nat → State → Prop}
    (h1 : ∀ e < k * k, 4 * (k * k / 4) ≤ e → ∀ s, I e s →
      WP isa (sampleIJ16 (sc (oa + 512 * e)) (e / k) (e % k) scr) s (I (e + 1)))
    (h4 : ∀ q < k * k / 4, ∀ s, I (4 * q) s →
      WP isa (quad16 p k (4 * q) (sc (oa + 512 * (4 * q))) scr) s (I (4 * q + 4)))
    {s : State} (h : I 0 s) : WP isa (samples16 p k oa scr) s (I (k * k)) := by
  have := ents16_ok p k oa scr h1 h4 (k * k) 0 (by omega_using []) (by omega_using []) s h
  rwa [Nat.zero_add] at this

/-- `ents16_ok`, for constant time. -/
theorem ents16_tr (p : String × Prog isa) (k oa : Nat) (scr : Ptr) {R : Nat → State → State → Prop}
    (h1 : ∀ e < k * k, 4 * (k * k / 4) ≤ e →
      RelCT isa (R e) (sampleIJ16 (sc (oa + 512 * e)) (e / k) (e % k) scr) (R (e + 1)))
    (h4 : ∀ q < k * k / 4,
      RelCT isa (R (4 * q)) (quad16 p k (4 * q) (sc (oa + 512 * (4 * q))) scr) (R (4 * q + 4))) :
    ∀ n e, e + n = k * k → (e % 4 = 0 ∨ 4 * (k * k / 4) ≤ e) → RelCT isa (R e) (ents16 p k oa scr e n) (R (e + n))
  | 0, e, _, _ => by simp only [ents16]; exact nil_tr
  | 1, e, he, hq => by simp only [ents16]; exact h1 e (by omega_using [he]) (by omega_using [he, hq])
  | 2, e, he, hq => by
    simp only [ents16]
    exact RelCT.seq (h1 e (by omega_using [he]) (by omega_using [he, hq])) (ents16_tr p k oa scr h1 h4 1 (e + 1) (by omega_using [he]) (by omega_using [he, hq]))
  | 3, e, he, hq => by
    simp only [ents16]
    have := ents16_tr p k oa scr h1 h4 2 (e + 1) (by omega_using [he]) (by omega_using [he, hq])
    rw [show e + 1 + 2 = e + 3 by omega_using []] at this
    exact RelCT.seq (h1 e (by omega_using [he]) (by omega_using [he, hq])) this
  | 4, e, he, hq => by
    simp only [ents16]
    have := h4 (e / 4) (by omega_using [he])
    rwa [show 4 * (e / 4) = e by omega_using [he, hq]] at this
  | n + 5, e, he, hq => by
    simp only [ents16]
    have := h4 (e / 4) (by omega_using [he])
    rw [show 4 * (e / 4) = e by omega_using [he, hq]] at this
    have h' := ents16_tr p k oa scr h1 h4 (n + 1) (e + 4) (by omega_using [he]) (by omega_using [hq])
    rw [show e + 4 + (n + 1) = e + (n + 5) by omega_using []] at h'
    exact RelCT.seq this h'

theorem samples16_tr' (p : String × Prog isa) (k oa : Nat) (scr : Ptr) {R : Nat → State → State → Prop}
    (h1 : ∀ e < k * k, 4 * (k * k / 4) ≤ e →
      RelCT isa (R e) (sampleIJ16 (sc (oa + 512 * e)) (e / k) (e % k) scr) (R (e + 1)))
    (h4 : ∀ q < k * k / 4,
      RelCT isa (R (4 * q)) (quad16 p k (4 * q) (sc (oa + 512 * (4 * q))) scr) (R (4 * q + 4))) :
    RelCT isa (R 0) (samples16 p k oa scr) (R (k * k)) := by
  have := ents16_tr p k oa scr h1 h4 (k * k) 0 (by omega_using []) (by omega_using [])
  rwa [Nat.zero_add] at this

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: key generation with 16-bit polynomials, the samples

After `G(d ‖ k)` (`KeyGen.KA`): the entries of `Â`, as `u16`s
(`samples_ok`), and when every `SampleNTT` succeeded, the outputs of `PRF₂`
(`prfs_ok`) and `s ‖ e` from them (`se_ok`), as `u16`s (`KRest16`), and
their constant time.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace KeyGen16

open KeyGen VG.Impl.MlKem.X86_64.Top16

/-- After the first `e` entries of `Â`. -/
structure KB16 (K : Kem16) (e : Nat) (σ s : State) : Prop where
  a : KA K.L σ s
  m : MatB16 K.L.k K.oA (KPke.kgRho K.L.p (kgD σ)) e s

/-- After the matrix, when every `SampleNTT` succeeded. -/
structure KR0 (K : Kem16) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = rhoK K.L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma K.L.p (kgD σ)
  r15 : s.gpr .r15 = 1
  mat : ∀ e < K.L.k * K.L.k, PolyIsW 16 s.mem (pa s (aP K e)) (aHat (rhoK K.L σ) (e / K.L.k) (e % K.L.k))

section
variable {K : Kem16} (W : Kg16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

theorem matKeep_ok {e : Nat} {s s' : State} (h : KA K.L σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (hc : matKeep K e ws = true) :
    KA K.L σ s' ∧ ∀ e' < e, keepB (kgB K.L) ws (sc (K.oA + 512 * e')) 512 = true := by
  simp only [matKeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hkc, kG⟩, kS⟩, kB⟩, kA⟩ := hc
  exact ⟨h.keep W hp hP hkc kG kS kB, kA⟩

theorem sample_step {e : Nat} (he : e < K.L.k * K.L.k) (he' : 4 * (K.L.k * K.L.k / 4) ≤ e) {s : State}
    (h : KB16 K e σ s) : WP isa (sampleIJ16 (sc (K.oA + 512 * e)) (e / K.L.k) (e % K.L.k) (sc K.oW)) s
      (KB16 K (e + 1) σ) := by
  have hc := W.kb e he he'
  simp only [kbChk, Bool.and_eq_true] at hc
  have hk := W.k
  have L₀ := h.a.kc.lay W hp
  refine WP.mono (sampleIJ16_ok L₀ (kgB_bases K.L) rbx_na rbx_na (by have := div_lt_k he; omega_using [hk, this])
    (by have := mod_lt_k he; omega_using [hk, this]) hc.1) fun s' ⟨hP, h15, hres⟩ => ?_
  have ⟨ka, kA⟩ := matKeep_ok W hp h.a hP hc.2
  exact ⟨ka, h.m.single h.a.sb L₀ hP kA h15 hres⟩

theorem quad_step {n : String} {c : Prog isa} (v : S16Ok c) {q : Nat} (hq : q < K.L.k * K.L.k / 4) {s : State}
    (h : KB16 K (4 * q) σ s) : WP isa (quad16 (n, c) K.L.k (4 * q) (sc (K.oA + 512 * (4 * q))) (sc K.oW)) s
      (KB16 K (4 * q + 4) σ) := by
  have hc := W.kq q hq
  simp only [kqChk, Bool.and_eq_true] at hc
  have hk := W.k
  have L₀ := h.a.kc.lay W hp
  refine WP.mono (quad16_ok v L₀ (kgB_bases K.L) (by have : K.L.k * K.L.k ≤ 16 := Nat.mul_le_mul hk.2 hk.2; omega_using [hq, this])
    hc.1) fun s' ⟨hP, h15, hres⟩ => ?_
  have ⟨ka, kA⟩ := matKeep_ok W hp h.a hP hc.2
  exact ⟨ka, h.m.four h.a.sb L₀ hP kA h15 hres⟩

theorem samples_ok {n : String} {c : Prog isa} (v : S16Ok c) {s : State} (h : KB16 K 0 σ s) :
    WP isa (mat K (n, c)) s (KB16 K (K.L.k * K.L.k) σ) :=
  samples16_ok' (n, c) K.L.k K.oA (sc K.oW) (I := fun e => KB16 K e σ)
    (fun _ he he' _ hs => sample_step W hp he he' hs) (fun _ hq _ hs => quad_step W hp v hq hs) h

theorem KB16.flag {e : Nat} (he : e ≤ K.L.k * K.L.k) {s s' : State} (h : KB16 K e σ s) (hP : PPost s s' []) :
    KB16 K e σ s' := by
  have L₀ := h.a.kc.lay W hp
  exact ⟨h.a.keep W hp hP.b W.flag W.flagG W.flagS W.flagB, by rw [hP.cs .r15 (by decide)]; exact h.m.r15,
    fun e' he' f hf => L₀.keepPoly16 hP.b (W.flagA e' (by omega_using [he, he'])) (h.m.mat e' he' f hf)⟩

end

theorem KR0.start {K : Kem16} {σ s : State} (h : KB16 K (K.L.k * K.L.k) σ s)
    (ho : allOk K.L.k (rhoK K.L σ) (K.L.k * K.L.k)) : KR0 K σ s :=
  ⟨h.a.kc, h.a.rho, h.a.sig, by rw [h.m.r15, ifp ho], fun e he =>
    h.m.mat e he _ (aHat_eq ho (div_lt_k he) (mod_lt_k he))⟩

section
variable {K : Kem16} (W : Kg16Wf K) {σ : State} (hp : (keyGenK K.L).pre σ)
include W hp

theorem KRest16.keep {n : Nat} {s s' : State} (h : KRest16 K n σ s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws)
    (hc : restChk K n ws = true) : KRest16 K n σ s' := by
  simp only [restChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hkc, kG⟩, kS⟩, kA⟩, kR⟩, kP⟩ := hc
  have L₀ := h.kc.lay W hp
  exact ⟨h.kc.step W hp hP.b hkc, by rw [L₀.keepBytes hP.b kG]; exact h.rho,
    by rw [L₀.keepBytes hP.b kS]; exact h.sig, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    fun e he => L₀.keepPoly16 hP.b (kA e he) (h.mat e he),
    fun N hN => by rw [L₀.keepBytes hP.b (kR N hN)]; exact h.prf N hN,
    fun N hN => L₀.keepPoly16 hP.b (kP N hN) (h.se N hN)⟩

theorem prfs_ok (v : Sample4Impl) {s : State} (h : KR0 K σ s) :
    WP isa (v.callee.prfs 0 (2 * K.L.k) K.oPR (K.oW / 32)) s (KRest16 K 0 σ) := by
  have hc := W.pr
  simp only [prChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hpc, hkc⟩, kG⟩, kS⟩, kA⟩ := hc
  have L₀ := h.kc.lay W hp
  refine WP.mono (v.prfs_ok L₀ (kgB_bases K.L) (by have := W.k; omega_using [this]) hpc) fun s' ⟨hP, hb⟩ => ?_
  have hσ : bytesAt s'.mem (pa s' sigP) 32 = bytesAt s.mem (pa s sigP) 32 := L₀.keepBytes hP.b kS
  refine ⟨h.kc.step W hp hP.b hkc, by rw [L₀.keepBytes hP.b kG]; exact h.rho, hσ.trans h.sig,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e he => L₀.keepPoly16 hP.b (kA e he) (h.mat e he),
    fun N hN => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [Top16.prfO, hP.pa rbx_cs, hb N hN, h.sig, Nat.zero_add]

theorem se_ok {A : Arith} (hA : ArithOk A) {N : Nat} (hN : N < 2 * K.L.k) {s : State} (h : KRest16 K N σ s) :
    WP isa (cbdN K A N) s (KRest16 K (N + 1) σ) := by
  have hc := W.se N hN
  simp only [seChk, Bool.and_eq_true] at hc
  have L₀ := h.kc.lay W hp
  refine WP.mono (cbd2_16At_okL hA L₀ rbx_na hc.1) fun s₁ ⟨hP₁, hp₁⟩ => ?_
  rw [h.prf N hN, ← hP₁.pa rbx_cs] at hp₁
  have hk := h.keep W hp hP₁ hc.2
  refine ⟨hk.kc, hk.rho, hk.sig, hk.r15, hk.mat, hk.prf, fun k hk' => ?_⟩
  rcases (by omega_using [hk'] : k < N ∨ k = N) with hk' | rfl
  · exact hk.se k hk'
  · exact hp₁

/-- The samples and the keys, when every `SampleNTT` succeeded. -/
theorem rest_ok (hK : KpkeOk K.L) (v : Sample4Impl) {s : State} (h : KR0 K σ s) :
    WP isa (kgRest K v.callee) s (KFin K.L σ) := by
  unfold kgRest noise
  refine WP.seq (WP.seq (WP.mono (prfs_ok W hp v h) fun s₀ h₀ => WP.mono (seqR_ok (I := fun k => KRest16 K k σ)
    (2 * K.L.k) 0 (fun k _ hk s hs => se_ok W hp v.arith (by omega_using [hk]) hs) s₀ h₀) fun s₁ h₁ => ?_))
  rw [Nat.zero_add] at h₁
  exact tail_ok W hp hK h₁

end

end KeyGen16

end VG.Proof.MlKem.X86_64
