module

public import VerifiedGarbage.Proof.MlKem.X86_64.FragS4
public import VerifiedGarbage.Impl.MlKem.X86_64.Frag16
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragS4
import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset

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
  refine WP.seq (WP.call v.ok v.nosp (by omega) (s4_16Pre h hv k) (by rw [k.2.1, k.2.2]; exact h.c)
    (by rw [k.2.2]; exact h.w) fun s2 hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_)
  refine WP.mono (and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  have hsd : ∀ k < 4, seed4 s1.callEntry.mem (pa s (sc 0)) k = seed4 s.mem (pa s (sc 0)) k := fun k hk => by
    unfold seed4
    rw [ce_bytesAt s1 (p := pa s (sc 0) + BitVec.ofNat 64 (34 * k)) (n := 34) (by decide) (by rw [hsp]; exact h.kS.sub_right (Offset.sub_base _ (by omega))), hm]
  simp only [sample4KW, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2.1, hm₂] at hpost
  rw [hg₂ .rax (by decide), range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
    (hsd k hk)] at hpost
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_,
    fun j hj f hf => ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm, ← hsp]
    exact Frame.below_mono hf (by omega) (by omega)
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
  refine WP.seq (WP.mono (seed_step L hcs (by omega) c0 h) fun s₁ ⟨P₁, h₁⟩ => ?_)
  have L₁ := L.post P₁.b hcs
  refine WP.seq (WP.mono (seed_step L₁ hcs (by omega) c1 h₁) fun s₂ ⟨P₂, h₂⟩ => ?_)
  have L₂ := L₁.post P₂.b hcs
  refine WP.seq (WP.mono (seed_step L₂ hcs (by omega) c2 h₂) fun s₃ ⟨P₃, h₃⟩ => ?_)
  have L₃ := L₂.post P₃.b hcs
  refine WP.seq (WP.mono (seed_step L₃ hcs (by omega) c3 h₃) fun s₄ ⟨P₄, h₄⟩ => ?_)
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
  refine RelCT.seq (seed_tr hcs (by omega) (by decide) (hij 0 (by decide)).1 (hij 0 (by decide)).2 c0) ?_
  refine RelCT.seq (seed_tr hcs (by omega) (by decide) (hij 1 (by decide)).1 (hij 1 (by decide)).2 c1) ?_
  refine RelCT.seq (seed_tr hcs (by omega) (by decide) (hij 2 (by decide)).1 (hij 2 (by decide)).2 c2) ?_
  refine RelCT.seq (seed_tr hcs (by omega) (by decide) (hij 3 (by decide)).1 (hij 3 (by decide)).2 c3) ?_
  refine RelCT.mono (sample4At16_tr (n := n') v) (fun x y h => ⟨S4H16.of h.1.1 c4, S4H16.of h.1.2.1 c4, h.1.eq hin, h.1.2.2.2, ?_⟩)
    fun _ _ h => h
  rw [bytesAt136, bytesAt136, seed4_eq h.2.1 (k := 0) (by decide), seed4_eq h.2.1 (k := 1) (by decide),
    seed4_eq h.2.1 (k := 2) (by decide), seed4_eq h.2.1 (k := 3) (by decide), seed4_eq h.2.2 (k := 0) (by decide),
    seed4_eq h.2.2 (k := 1) (by decide), seed4_eq h.2.2 (k := 2) (by decide), seed4_eq h.2.2 (k := 3) (by decide)]

end VG.Proof.MlKem.X86_64
