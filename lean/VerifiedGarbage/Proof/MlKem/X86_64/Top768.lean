import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
import VerifiedGarbage.Impl.MlKem.X86_64.KeyGen
import VerifiedGarbage.Impl.MlKem.X86_64.Encrypt
import VerifiedGarbage.Impl.MlKem.X86_64.Decaps
import VerifiedGarbage.Impl.MlKem.X86_64.Encaps

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.FragS4`. -/
section

/-!
# ML-KEM on x86-64: four entries of the matrix at once

In a layout: the seed `ρ ‖ j ‖ i` of an entry, with `ρ` at `SB`, to `34 k`
bytes into `scratch` (`seedAt_ok`), and the four seeds of entries `e₀, …, e₀ +
3` of a matrix of `n` columns (`SeedsIs`); then `vg_mlkem_sample_ntt4`, of any
implementation (`Sample4Impl`), of those seeds to the four polynomials from
`a` (`sample4At_ok`), which changes `r15` (so what it leaves is `PostB`), and
the whole (`quad_ok`), and its constant time for a given `ρ` (`quad_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {rbs wbs : List (Reg × Nat)}

/-! ## A seed -/

theorem rbx_ne_rax : Reg.rbx ≠ .rax := by decide

/-- What seed `k` writes. -/
abbrev seedW (k : Nat) : List (Ptr × Nat) :=
  [(sc (34 * k), 32)] ++ ([(sc (34 * k + 32), 1)] ++ [(sc (34 * k + 33), 1)])

/-- The copy of `ρ` and the two bytes of seed `k`. -/
def seedChk (bs wbs : List (Reg × Nat)) (k : Nat) : Bool :=
  copyChk bs wbs (sc (34 * k)) (sc oSB) 32 && inB wbs (sc (34 * k + 32)) 1 && inB wbs (sc (34 * k + 33)) 1 &&
    keepB bs [(sc (34 * k + 32), 1)] (sc (34 * k)) 32 && keepB bs [(sc (34 * k + 33), 1)] (sc (34 * k)) 32 &&
    keepB bs [(sc (34 * k + 33), 1)] (sc (34 * k + 32)) 1

theorem seedAt_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {k i j : Nat}
    (hi : i < 256) (hj : j < 256) (hc : VG.Proof.MlKem.X86_64.seedChk (rbs ++ wbs) wbs k = true) :
    WP isa (seedAt k i j) s fun s' => PPost s s' (VG.Proof.MlKem.X86_64.seedW k) ∧
      bytesAt s'.mem (pa s' (sc (34 * k))) 34 = matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j := by
  simp only [VG.Proof.MlKem.X86_64.seedChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨hcp, h32⟩, h33⟩, k1⟩, k2⟩, k3⟩ := hc
  unfold seedAt
  refine WP.seq (WP.mono (copy_okL L (by decide) hcp) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have L₁ := L.post hP₁.b hcs
  rw [WP.block_append_iff]
  refine WP.mono (setB_okL L₁ VG.Proof.MlKem.X86_64.rbx_ne_rax hj h32) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have L₂ := L₁.post hP₂.b hcs
  refine WP.mono (setB_okL L₂ VG.Proof.MlKem.X86_64.rbx_ne_rax hi h33) fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have e2 : ∀ o, pa s₂ (sc o) = pa s₁ (sc o) := fun o => hP₂.pa rbx_cs
  have e3 : ∀ o, pa s₃ (sc o) = pa s₂ (sc o) := fun o => hP₃.pa rbx_cs
  have hρ : bytesAt s₃.mem (pa s₃ (sc (34 * k))) 32 = bytesAt s.mem (pa s (sc oSB)) 32 := by
    rw [L₂.keepBytes hP₃.b k2, L₁.keepBytes hP₂.b k1, show pa s₁ (sc (34 * k)) = pa s (sc (34 * k)) from hP₁.pa rbx_cs,
      hb₁]
  have hjb : bytesAt s₃.mem (pa s₃ (sc (34 * k + 32))) 1 = [BitVec.ofNat 8 j] := by
    rw [L₂.keepBytes hP₃.b k3, e2]; exact hb₂
  have hib : bytesAt s₃.mem (pa s₃ (sc (34 * k + 33))) 1 = [BitVec.ofNat 8 i] := by
    rw [e3]; exact hb₃
  refine ⟨PPost.app hP₁ (PPost.app hP₂ hP₃ fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact rbx_cs)
    (fun w hw => by
      simp only [List.mem_append, List.mem_singleton] at hw; rcases hw with rfl | rfl <;> exact rbx_cs),
    seed_eq hρ ?_ ?_⟩
  · refine mem_of_bytesAt_one ?_; rw [← hjb, pa, pa, off_add]
  · refine mem_of_bytesAt_one ?_; rw [← hib, pa, pa, off_add]

/-- `ρ` at `SB`, and the seeds of entries `e₀, …, e₀ + K - 1` of a matrix
of `n` columns, from `scratch`. -/
structure SeedsIs (ρ : List Byte) (n e₀ K : Nat) (s : State) : Prop where
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = ρ
  seeds : ∀ k < K, bytesAt s.mem (pa s (sc (34 * k))) 34 = matSeed ρ ((e₀ + k) / n) ((e₀ + k) % n)

/-- Seed `K`, keeping `ρ` and the seeds before it. -/
def seedsChk (bs wbs : List (Reg × Nat)) (K : Nat) : Bool :=
  VG.Proof.MlKem.X86_64.seedChk bs wbs K && keepB bs (VG.Proof.MlKem.X86_64.seedW K) (sc oSB) 32 &&
    (List.range K).all fun k => keepB bs (VG.Proof.MlKem.X86_64.seedW K) (sc (34 * k)) 34

theorem seed_step {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {ρ : List Byte}
    {n e₀ K : Nat} (he : e₀ + K < 256) (hc : VG.Proof.MlKem.X86_64.seedsChk (rbs ++ wbs) wbs K = true) (h : VG.Proof.MlKem.X86_64.SeedsIs ρ n e₀ K s) :
    WP isa (seedAt K ((e₀ + K) / n) ((e₀ + K) % n)) s fun s' =>
      PPost s s' (VG.Proof.MlKem.X86_64.seedW K) ∧ VG.Proof.MlKem.X86_64.SeedsIs ρ n e₀ (K + 1) s' := by
  simp only [VG.Proof.MlKem.X86_64.seedsChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hs, kB⟩, kS⟩ := hc
  refine WP.mono (VG.Proof.MlKem.X86_64.seedAt_ok L hcs (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) he)
    (Nat.lt_of_le_of_lt (Nat.mod_le _ _) he) hs) fun s' ⟨hP, hb⟩ => ⟨hP, ?_, fun k hk => ?_⟩
  · rw [L.keepBytes hP.b kB]; exact h.sb
  · rcases (by omega : k < K ∨ k = K) with hk | rfl
    · rw [L.keepBytes hP.b (kS k hk)]; exact h.seeds k hk
    · rw [hb, h.sb]

/-! ## The call -/

/-- The seeds, the four polynomials from `sc oa` and the working space at `sc oz`. -/
def s4Chk (bs wbs : List (Reg × Nat)) (oa oz : Nat) : Bool :=
  rdOk bs (sc 0) 136 && wrOk bs wbs (sc oa) 4096 && wrOk bs wbs (sc oz) 8192 && sepB bs (sc 0) 136 (sc oa) 4096 &&
    sepB bs (sc 0) 136 (sc oz) 8192 && sepB bs (sc oa) 4096 (sc oz) 8192

/-- What a call of `vg_mlkem_sample_ntt4` of the seeds at `scratch` to `sc oa` needs. -/
structure S4H (oa oz : Nat) (s : State) : Prop where
  offA : oa < 2 ^ 31
  offZ : oz < 2 ^ 31
  dSA : Region.Disjoint ⟨pa s (sc 0), 136⟩ ⟨pa s (sc oa), 4096⟩
  dSZ : Region.Disjoint ⟨pa s (sc 0), 136⟩ ⟨pa s (sc oz), 8192⟩
  dAZ : Region.Disjoint ⟨pa s (sc oa), 4096⟩ ⟨pa s (sc oz), 8192⟩
  kS : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc 0), 136⟩
  kA : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc oa), 4096⟩
  kZ : (below (s.gpr .rsp) 32).Disjoint ⟨pa s (sc oz), 8192⟩
  nwA : (pa s (sc oa)).toNat + 4096 ≤ 2 ^ 64
  nwZ : (pa s (sc oz)).toNat + 8192 ≤ 2 ^ 64
  c : Covers ([⟨pa s (sc 0), 136⟩] ++ [⟨pa s (sc oa), 4096⟩, ⟨pa s (sc oz), 8192⟩]) (s.rd ++ s.wr)
  w : Covers [⟨pa s (sc oa), 4096⟩, ⟨pa s (sc oz), 8192⟩] s.wr

theorem S4H.of {s : State} (L : Lay rbs wbs s) {oa oz : Nat} (hc : VG.Proof.MlKem.X86_64.s4Chk (rbs ++ wbs) wbs oa oz = true) :
    VG.Proof.MlKem.X86_64.S4H oa oz s := by
  simp only [VG.Proof.MlKem.X86_64.s4Chk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨_, hrs⟩, ⟨hoa, hra⟩, hwa⟩, ⟨hoz, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩ := hc
  exact ⟨hoa, hoz, L.disj s1, L.disj s2, L.disj s3, L.stkD hrs, L.stkD hra, L.stkD hrz, L.nwp hra, L.nwp hrz,
    covers_append (covers_cons (L.cR hrs) covers_nil) (covers_cons (L.cR hra) (covers_cons (L.cR hrz) covers_nil)),
    covers_cons (L.cW hwa) (covers_cons (L.cW hwz) covers_nil)⟩

theorem s4Glue_ok (oa oz : Nat) (ha : oa < 2 ^ 31) (hz : oz < 2 ^ 31) (s : State) :
    WP isa (.block (lea .rdi (sc 0) ++ lea .rsi (sc oa) ++ lea .rdx (sc oz))) s fun s1 =>
      ((s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = pa s (sc oa) ∧ s1.gpr .rdx = pa s (sc oz)) ∧ s1.mem = s.mem) ∧
        Keep argRegs s s1 := by
  refine WP.keep _ ?_ (by rfl)
  unfold lea
  xrun [sx_ofNat ha, sx_ofNat hz, sx_ofNat (show 0 < 2 ^ 31 by decide), pa_sc0, List.cons_append, List.nil_append]

theorem s4Pre {oa oz : Nat} {s s1 : State} (h : VG.Proof.MlKem.X86_64.S4H oa oz s)
    (hv : s1.gpr .rdi = pa s (sc 0) ∧ s1.gpr .rsi = pa s (sc oa) ∧ s1.gpr .rdx = pa s (sc oz))
    (k : Keep argRegs s s1) :
    sample4K.pre (s1.callEntry.withRegions [⟨pa s (sc 0), 136⟩] [⟨pa s (sc oa), 4096⟩, ⟨pa s (sc oz), 8192⟩]) := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  simp only [sample4K, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp), ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rdx ≠ .rsp), hv.1, hv.2.1, hv.2.2]
  exact ⟨trivial, trivial, h.dSA, h.dSZ, h.dAZ, ret_disj s1 (by rw [hsp]; exact h.kS),
    ret_disj s1 (by rw [hsp]; exact h.kA), ret_disj s1 (by rw [hsp]; exact h.kZ),
    stk_disj24 s1 (by rw [hsp]; exact h.kS), stk_disj24 s1 (by rw [hsp]; exact h.kA),
    stk_disj24 s1 (by rw [hsp]; exact h.kZ), h.nwA, h.nwZ⟩

theorem range_all_congr {n : Nat} {f g : Nat → Bool} (h : ∀ k < n, f k = g k) :
    (List.range n).all f = (List.range n).all g := by
  refine Bool.eq_iff_iff.mpr ?_
  simp only [List.all_eq_true, List.mem_range]
  exact ⟨fun H k hk => h k hk ▸ H k hk, fun H k hk => (h k hk).symm ▸ H k hk⟩

/-- Whether `SampleNTT` of the four seeds at `p` all succeed within 280 iterations. -/
abbrev all4 (m : Mem) (p : Addr) : Bool :=
  (List.range 4).all fun k => (sampleNTT minIterations (seed4 m p k)).isSome

/-- What a call of `vg_mlkem_sample_ntt4` leaves. -/
structure S4Post (oa oz : Nat) (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, r ≠ .r15 → s'.gpr r = s.gpr r
  frame : Frame ([⟨pa s (sc oa), 4096⟩, ⟨pa s (sc oz), 8192⟩] ++ [below (s.gpr .rsp) 32]) s.mem s'.mem
  r15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (if VG.Proof.MlKem.X86_64.all4 s.mem (pa s (sc 0)) then 1 else 0))
  res : ∀ k < 4, ∀ f, sampleNTT minIterations (seed4 s.mem (pa s (sc 0)) k) = some f →
    PolyIs s'.mem (poly4 (pa s (sc oa)) k) f

theorem S4Post.b {oa oz : Nat} {s s' : State} (h : VG.Proof.MlKem.X86_64.S4Post oa oz s s') :
    PPostB s s' [(sc oa, 4096), (sc oz, 8192)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

theorem sample4At_ok (v : Sample4Impl) {oa oz : Nat} {s : State} (h : VG.Proof.MlKem.X86_64.S4H oa oz s) :
    WP isa (sample4At v.callee (sc oa) (sc oz)) s (VG.Proof.MlKem.X86_64.S4Post oa oz s) := by
  have hd := v.depth_le
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.s4Glue_ok oa oz h.offA h.offZ s) fun s1 ⟨⟨hv, hm⟩, k⟩ => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine WP.seq (WP.call v.ok v.nosp (by omega) (VG.Proof.MlKem.X86_64.s4Pre h hv k) (by rw [k.2.1, k.2.2]; exact h.c)
    (by rw [k.2.2]; exact h.w) fun s2 hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ => ?_)
  refine WP.mono (and15_ok s2) fun s3 ⟨⟨h15, hm3⟩, k3⟩ => ?_
  have hsd : ∀ k < 4, seed4 s1.callEntry.mem (pa s (sc 0)) k = seed4 s.mem (pa s (sc 0)) k := fun k hk => by
    unfold seed4
    rw [ce_bytesAt s1 (p := pa s (sc 0) + BitVec.ofNat 64 (34 * k)) (n := 34) (by decide) (by rw [hsp]; exact h.kS.sub_right (Offset.sub_base _ (by omega))), hm]
  simp only [sample4K, State.withRegions_gpr, State.withRegions_mem, ce_gpr' s1 (by decide : Reg.rdi ≠ .rsp),
    ce_gpr' s1 (by decide : Reg.rsi ≠ .rsp), hv.1, hv.2.1, hm₂] at hpost
  rw [hg₂ .rax (by decide), VG.Proof.MlKem.X86_64.range_all_congr fun k hk => congrArg (fun B => (sampleNTT minIterations B).isSome)
    (hsd k hk)] at hpost
  refine ⟨k3.2.1.trans (hrd.trans k.2.1), k3.2.2.trans (hwr.trans k.2.2), fun r hr h15' => ?_, ?_, ?_,
    fun j hj f hf => ?_⟩
  · rw [k3.gpr (by simpa using h15'), hcs r hr, k.gpr (argRegs_cs r hr)]
  · rw [hm3, ← hm, ← hsp]
    exact Frame.below_mono hf (by omega) (by omega)
  · rw [h15, hcs .r15 (by decide), k.gpr (by decide), hpost.1]
  · rw [hm3]; exact hpost.2 j hj f (by rw [hsd j hj]; exact hf)

theorem sample4At_tr (v : Sample4Impl) {oa oz : Nat} :
    RelCT isa (fun x y => VG.Proof.MlKem.X86_64.S4H oa oz x ∧ VG.Proof.MlKem.X86_64.S4H oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧ x.gpr .rsp = y.gpr .rsp ∧
      bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136)
      (sample4At v.callee (sc oa) (sc oz)) fun _ _ => True := by
  refine RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, (VG.Proof.MlKem.X86_64.S4H oa oz x ∧ VG.Proof.MlKem.X86_64.S4H oa oz y ∧ x.gpr .rbx = y.gpr .rbx ∧
      x.gpr .rsp = y.gpr .rsp ∧ bytesAt x.mem (pa x (sc 0)) 136 = bytesAt y.mem (pa y (sc 0)) 136) ∧
      (((x1.gpr .rdi = pa x (sc 0) ∧ x1.gpr .rsi = pa x (sc oa) ∧ x1.gpr .rdx = pa x (sc oz)) ∧ x1.mem = x.mem) ∧
        Keep argRegs x x1) ∧
      (((y1.gpr .rdi = pa y (sc 0) ∧ y1.gpr .rsi = pa y (sc oa) ∧ y1.gpr .rdx = pa y (sc oz)) ∧ y1.mem = y.mem) ∧
        Keep argRegs y y1))
    (block_nomem_tr (nomem_append (nomem_append (lea_nomem _ _) (lea_nomem _ _)) (lea_nomem _ _)))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlKem.X86_64.s4Glue_ok oa oz hx.offA hx.offZ x, VG.Proof.MlKem.X86_64.s4Glue_ok oa oz hy.offA hy.offZ y⟩)
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.seq (RelCT.callEx v.ok v.ct ?_)
      (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl))
  rintro x1 y1 ⟨x, y, ⟨hx, hy, e1, e3, e4⟩, ⟨⟨hv1, hm1⟩, k1⟩, ⟨⟨hv2, hm2⟩, k2⟩⟩
  have hs1 : x1.gpr .rsp = x.gpr .rsp := k1.gpr (by decide)
  have hs2 : y1.gpr .rsp = y.gpr .rsp := k2.gpr (by decide)
  refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.s4Pre hx hv1 k1, VG.Proof.MlKem.X86_64.s4Pre hy hv2 k2, ?_, by rw [k1.2.1, k1.2.2]; exact hx.c,
    by rw [k1.2.2]; exact hx.w, by rw [k2.2.1, k2.2.2]; exact hy.c, by rw [k2.2.2]; exact hy.w,
    by rw [hs1, hs2, e3]⟩
  simp only [sample4K, State.withRegions_gpr, State.withRegions_mem, State.callEntry_rsp,
    ce_gpr' _ (by decide : Reg.rdi ≠ .rsp), ce_gpr' _ (by decide : Reg.rsi ≠ .rsp),
    ce_gpr' _ (by decide : Reg.rdx ≠ .rsp), hv1.1, hv1.2.1, hv1.2.2, hv2.1, hv2.2.1, hv2.2.2]
  rw [ce_bytesAt x1 (n := 136) (by decide) (by rw [hs1]; exact hx.kS),
    ce_bytesAt y1 (n := 136) (by decide) (by rw [hs2]; exact hy.kS), hm1, hm2, e4]
  simp only [pa, e1, hs1, hs2, e3, and_self]

/-! ## Four entries -/

/-- What entries `e₀, …, e₀ + 3` write. -/
abbrev quadW (oa oz : Nat) : List (Ptr × Nat) :=
  VG.Proof.MlKem.X86_64.seedW 0 ++ VG.Proof.MlKem.X86_64.seedW 1 ++ VG.Proof.MlKem.X86_64.seedW 2 ++ VG.Proof.MlKem.X86_64.seedW 3 ++ [(sc oa, 4096), (sc oz, 8192)]

def quadChk (bs wbs : List (Reg × Nat)) (oa oz : Nat) : Bool :=
  VG.Proof.MlKem.X86_64.seedsChk bs wbs 0 && VG.Proof.MlKem.X86_64.seedsChk bs wbs 1 && VG.Proof.MlKem.X86_64.seedsChk bs wbs 2 && VG.Proof.MlKem.X86_64.seedsChk bs wbs 3 && VG.Proof.MlKem.X86_64.s4Chk bs wbs oa oz

theorem quadChk_spec {bs wbs : List (Reg × Nat)} {oa oz : Nat} (hc : VG.Proof.MlKem.X86_64.quadChk bs wbs oa oz = true) :
    VG.Proof.MlKem.X86_64.seedsChk bs wbs 0 = true ∧ VG.Proof.MlKem.X86_64.seedsChk bs wbs 1 = true ∧ VG.Proof.MlKem.X86_64.seedsChk bs wbs 2 = true ∧ VG.Proof.MlKem.X86_64.seedsChk bs wbs 3 = true ∧
      VG.Proof.MlKem.X86_64.s4Chk bs wbs oa oz = true := by
  simp only [VG.Proof.MlKem.X86_64.quadChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hc
  exact ⟨h0, h1, h2, h3, h4⟩

theorem seed4_eq {ρ : List Byte} {n e₀ : Nat} {s : State} (h : VG.Proof.MlKem.X86_64.SeedsIs ρ n e₀ 4 s) {k : Nat} (hk : k < 4) :
    seed4 s.mem (pa s (sc 0)) k = matSeed ρ ((e₀ + k) / n) ((e₀ + k) % n) := by
  unfold seed4
  rw [pa, off_add, Nat.zero_add]
  exact h.seeds k hk

/-- The four seeds, then `vg_mlkem_sample_ntt4`, in a layout. -/
theorem quad4_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {ρ : List Byte}
    {n e₀ : Nat} (he : e₀ + 4 ≤ 256) {oa oz : Nat} (hc : VG.Proof.MlKem.X86_64.quadChk (rbs ++ wbs) wbs oa oz = true)
    (h : VG.Proof.MlKem.X86_64.SeedsIs ρ n e₀ 0 s) {v : Callee4} {Q : State → Prop}
    (hQ : ∀ s₄, PPost s s₄ (VG.Proof.MlKem.X86_64.seedW 0 ++ VG.Proof.MlKem.X86_64.seedW 1 ++ VG.Proof.MlKem.X86_64.seedW 2 ++ VG.Proof.MlKem.X86_64.seedW 3) → VG.Proof.MlKem.X86_64.SeedsIs ρ n e₀ 4 s₄ →
      Lay rbs wbs s₄ → WP isa (sample4At v (sc oa) (sc oz)) s₄ Q) :
    WP isa (quad v n e₀ (sc oa) (sc oz)) s Q := by
  obtain ⟨c0, c1, c2, c3, _⟩ := VG.Proof.MlKem.X86_64.quadChk_spec hc
  unfold quad
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.seed_step L hcs (by omega) c0 h) fun s₁ ⟨P₁, h₁⟩ => ?_)
  have L₁ := L.post P₁.b hcs
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.seed_step L₁ hcs (by omega) c1 h₁) fun s₂ ⟨P₂, h₂⟩ => ?_)
  have L₂ := L₁.post P₂.b hcs
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.seed_step L₂ hcs (by omega) c2 h₂) fun s₃ ⟨P₃, h₃⟩ => ?_)
  have L₃ := L₂.post P₃.b hcs
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.seed_step L₃ hcs (by omega) c3 h₃) fun s₄ ⟨P₄, h₄⟩ => ?_)
  exact hQ s₄ (PPost.app (PPost.app (PPost.app P₁ P₂ (by decide)) P₃ (by decide)) P₄ (by decide)) h₄
    (L₃.post P₄.b hcs)

theorem quad_ok (v : Sample4Impl) {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases)
    {n e₀ : Nat} (he : e₀ + 4 ≤ 256) {oa oz : Nat} (hc : VG.Proof.MlKem.X86_64.quadChk (rbs ++ wbs) wbs oa oz = true) :
    WP isa (quad v.callee n e₀ (sc oa) (sc oz)) s fun s' => PPostB s s' (VG.Proof.MlKem.X86_64.quadW oa oz) ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (List.range 4).all (fun k => (sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e₀ + k) / n) ((e₀ + k) % n))).isSome) then 1 else 0)) ∧
      ∀ k < 4, ∀ f, sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e₀ + k) / n) ((e₀ + k) % n)) = some f →
        PolyIs s'.mem (pa s (sc (oa + 1024 * k))) f := by
  refine VG.Proof.MlKem.X86_64.quad4_ok L hcs he hc ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩ fun s₄ P h₄ L₄ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.sample4At_ok v (S4H.of L₄ (VG.Proof.MlKem.X86_64.quadChk_spec hc).2.2.2.2)) fun s' h' => ?_
  have ea : pa s₄ (sc oa) = pa s (sc oa) := P.pa rbx_cs
  refine ⟨PPostB.app P.b h'.b (by simp [bases]), ?_, fun k hk f hf => ?_⟩
  · rw [h'.r15, P.cs .r15 (by decide), VG.Proof.MlKem.X86_64.all4, VG.Proof.MlKem.X86_64.range_all_congr fun k hk => congrArg
      (fun B => (sampleNTT minIterations B).isSome) (VG.Proof.MlKem.X86_64.seed4_eq h₄ hk)]
  · have := h'.res k hk f (by rw [VG.Proof.MlKem.X86_64.seed4_eq h₄ hk]; exact hf)
    rwa [poly4, ea, pa, off_add] at this

/-! ## Constant time -/

theorem copyT0 : (taint.check (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 0)) (sc oSB) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 0)) (sc oSB) 32))).isSome = true := by
  taint_decide

theorem copyT1 : (taint.check (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 1)) (sc oSB) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 1)) (sc oSB) 32))).isSome = true := by
  taint_decide

theorem copyT2 : (taint.check (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 2)) (sc oSB) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 2)) (sc oSB) 32))).isSome = true := by
  taint_decide

theorem copyT3 : (taint.check (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 3)) (sc oSB) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * 3)) (sc oSB) 32))).isSome = true := by
  taint_decide

theorem copyT {k : Nat} (hk : k < 4) : (taint.check (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * k)) (sc oSB) 32)
    (Taint.hintOf taint (X86_64.Taint.ofRegs [.rbx]) (copy (sc (34 * k)) (sc oSB) 32))).isSome = true := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  exacts [VG.Proof.MlKem.X86_64.copyT0, VG.Proof.MlKem.X86_64.copyT1, VG.Proof.MlKem.X86_64.copyT2, VG.Proof.MlKem.X86_64.copyT3]

theorem setT : ∀ k < 4, ∀ i < 4, ∀ j < 4, (taint.check (X86_64.Taint.ofRegs [.rbx])
    (.block (setB (sc (34 * k + 32)) j ++ setB (sc (34 * k + 33)) i)) (.block [])).isSome = true := by
  decide +kernel

/-- Two runs in a layout, each with `ρ` and the first `K` seeds. -/
abbrev RQ (rbs wbs : List (Reg × Nat)) (ρ : List Byte) (n e₀ K : Nat) (x y : State) : Prop :=
  LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.SeedsIs ρ n e₀ K x ∧ VG.Proof.MlKem.X86_64.SeedsIs ρ n e₀ K y

theorem copyChk_dst {bs wbs : List (Reg × Nat)} {dst src : Ptr} {n : Nat} (hc : copyChk bs wbs dst src n = true) :
    inB bs dst n = true := by
  simp only [copyChk, wrOk, rdOk, Bool.and_eq_true] at hc
  exact hc.1.1.1.1.1.2

theorem seed_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {ρ : List Byte} {n e₀ K : Nat} (he : e₀ + K < 256)
    (hK : K < 4) (hi : (e₀ + K) / n < 4) (hj : (e₀ + K) % n < 4) (hc : VG.Proof.MlKem.X86_64.seedsChk (rbs ++ wbs) wbs K = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.RQ rbs wbs ρ n e₀ K) (seedAt K ((e₀ + K) / n) ((e₀ + K) % n)) (VG.Proof.MlKem.X86_64.RQ rbs wbs ρ n e₀ (K + 1)) := by
  have hs : VG.Proof.MlKem.X86_64.seedChk (rbs ++ wbs) wbs K = true := by
    simp only [VG.Proof.MlKem.X86_64.seedsChk, Bool.and_eq_true] at hc; exact hc.1.1
  have hcp : copyChk (rbs ++ wbs) wbs (sc (34 * K)) (sc oSB) 32 = true := by
    simp only [VG.Proof.MlKem.X86_64.seedChk, Bool.and_eq_true] at hs; exact hs.1.1.1.1.1
  have hin := VG.Proof.MlKem.X86_64.copyChk_dst hcp
  have htr : RelCT isa (LRel rbs wbs) (seedAt K ((e₀ + K) / n) ((e₀ + K) % n)) fun _ _ => True := by
    unfold seedAt
    refine RelCT.seq (LRel.step hcs (taintRel [.rbx] (fun x y h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.eq hin) (VG.Proof.MlKem.X86_64.copyT hK))
      fun x Lx => WP.mono (copy_okL Lx (by decide) hcp) fun _ h => ⟨_, h.1⟩) ?_
    exact taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq hin) (VG.Proof.MlKem.X86_64.setT K hK _ hi _ hj)
  exact RelCT.postDep (F := fun x x' => PPost x x' (VG.Proof.MlKem.X86_64.seedW K) ∧ VG.Proof.MlKem.X86_64.SeedsIs ρ n e₀ (K + 1) x')
    (RelCT.mono htr (fun _ _ h => h.1) fun _ _ h => h)
    (fun x y h => ⟨VG.Proof.MlKem.X86_64.seed_step h.1.1 hcs he hc h.2.1, VG.Proof.MlKem.X86_64.seed_step h.1.2.1 hcs he hc h.2.2⟩)
    fun x y x' y' h hx hy => ⟨h.1.post hcs hx.1.b hy.1.b, hx.2, hy.2⟩

theorem bytesAt136 (m : Mem) (p : Addr) :
    bytesAt m p 136 = seed4 m p 0 ++ (seed4 m p 1 ++ (seed4 m p 2 ++ seed4 m p 3)) := by
  rw [show (136 : Nat) = 34 + (34 + (34 + 34)) from rfl, bytesAt_add, bytesAt_add, bytesAt_add]
  simp only [seed4, off_add, Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero]

/-- The constant time of the four entries, for a given `ρ`. -/
theorem quad_tr (v : Sample4Impl) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {ρ : List Byte} {n e₀ : Nat}
    (he : e₀ + 4 ≤ 256) (hij : ∀ k < 4, (e₀ + k) / n < 4 ∧ (e₀ + k) % n < 4) {oa oz : Nat}
    (hc : VG.Proof.MlKem.X86_64.quadChk (rbs ++ wbs) wbs oa oz = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.RQ rbs wbs ρ n e₀ 0) (quad v.callee n e₀ (sc oa) (sc oz)) fun _ _ => True := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := VG.Proof.MlKem.X86_64.quadChk_spec hc
  have hin : inB (rbs ++ wbs) (sc 0) 136 = true := by
    simp only [VG.Proof.MlKem.X86_64.s4Chk, rdOk, Bool.and_eq_true] at c4; exact c4.1.1.1.1.1.2
  unfold quad
  refine RelCT.seq (VG.Proof.MlKem.X86_64.seed_tr hcs (by omega) (by decide) (hij 0 (by decide)).1 (hij 0 (by decide)).2 c0) ?_
  refine RelCT.seq (VG.Proof.MlKem.X86_64.seed_tr hcs (by omega) (by decide) (hij 1 (by decide)).1 (hij 1 (by decide)).2 c1) ?_
  refine RelCT.seq (VG.Proof.MlKem.X86_64.seed_tr hcs (by omega) (by decide) (hij 2 (by decide)).1 (hij 2 (by decide)).2 c2) ?_
  refine RelCT.seq (VG.Proof.MlKem.X86_64.seed_tr hcs (by omega) (by decide) (hij 3 (by decide)).1 (hij 3 (by decide)).2 c3) ?_
  refine RelCT.mono (VG.Proof.MlKem.X86_64.sample4At_tr v) (fun x y h => ⟨S4H.of h.1.1 c4, S4H.of h.1.2.1 c4, h.1.eq hin, h.1.2.2.2, ?_⟩)
    fun _ _ h => h
  rw [VG.Proof.MlKem.X86_64.bytesAt136, VG.Proof.MlKem.X86_64.bytesAt136, VG.Proof.MlKem.X86_64.seed4_eq h.2.1 (k := 0) (by decide), VG.Proof.MlKem.X86_64.seed4_eq h.2.1 (k := 1) (by decide),
    VG.Proof.MlKem.X86_64.seed4_eq h.2.1 (k := 2) (by decide), VG.Proof.MlKem.X86_64.seed4_eq h.2.1 (k := 3) (by decide), VG.Proof.MlKem.X86_64.seed4_eq h.2.2 (k := 0) (by decide),
    VG.Proof.MlKem.X86_64.seed4_eq h.2.2 (k := 1) (by decide), VG.Proof.MlKem.X86_64.seed4_eq h.2.2 (k := 2) (by decide), VG.Proof.MlKem.X86_64.seed4_eq h.2.2 (k := 3) (by decide)]

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.KgBase`. -/
section

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
abbrev kgB : List (Reg × Nat) := VG.Proof.MlKem.X86_64.KeyGen.kgR ++ VG.Proof.MlKem.X86_64.KeyGen.kgW L

theorem kgB_bases : ∀ b ∈ VG.Proof.MlKem.X86_64.KeyGen.kgB L, b.1 ∈ bases := by
  intro b hb; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp [bases]

theorem kgM_bases : ∀ p ∈ VG.Proof.MlKem.X86_64.KeyGen.kgM, p.1 ∈ bases := by decide

/-- A piece that writes `ws` keeps `KC`. -/
def kcChk (ws : List (Ptr × Nat)) : Bool :=
  topChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws && keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws (.rbp, 0) 32 && keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws (.rbp, 32) 32

/-! ## The checks of the pieces -/

/-- `ρ` of `Â`'s entry `e`. -/
abbrev aE (e : Nat) : Ptr := L.aS (e / L.k) (e % L.k)

/-- What entry `e` of `Â` writes. -/
abbrev ijW (e : Nat) : List (Ptr × Nat) :=
  [(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)] ++ [(pS (L.pA + e), 1024), (sc oSS, 2048)]

/-- Entry `e` of `Â`, on its own. -/
def kbChk (e : Nat) : Bool :=
  ijChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (pS (L.pA + e)) && VG.Proof.MlKem.X86_64.KeyGen.kcChk L (VG.Proof.MlKem.X86_64.KeyGen.ijW L e) && keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.ijW L e) (sc oG) 32 &&
    keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.ijW L e) sigP 32 && keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.ijW L e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.ijW L e) (pS (L.pA + e')) 1024

/-- What entries `e, …, e + 3` of `Â` write. -/
abbrev qW (e : Nat) : List (Ptr × Nat) := VG.Proof.MlKem.X86_64.quadW (oP (L.pA + e)) (oP L.pW)

/-- Entries `e, …, e + 3` of `Â`, at once. -/
def kqChk (e : Nat) : Bool :=
  VG.Proof.MlKem.X86_64.quadChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (oP (L.pA + e)) (oP L.pW) && VG.Proof.MlKem.X86_64.KeyGen.kcChk L (VG.Proof.MlKem.X86_64.KeyGen.qW L e) && keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.qW L e) (sc oG) 32 &&
    keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.qW L e) sigP 32 && keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.qW L e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.qW L e) (pS (L.pA + e')) 1024

/-- `PRF₂(σ, N)`, in the outputs of `prfs`. -/
abbrev prfO (N : Nat) : Ptr := sc (L.oPR + 128 * N)

/-- A piece that writes `ws` keeps `KRest n r e`. -/
def restChk (n r e : Nat) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlKem.X86_64.KeyGen.kcChk L ws && keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws (sc oG) 32 && keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws sigP 32 &&
    (List.range (L.k * L.k)).all (fun e => keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws (pS (L.pA + e)) 1024) &&
    (List.range (2 * L.k)).all (fun N => keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws (VG.Proof.MlKem.X86_64.KeyGen.prfO L N) 128) &&
    (List.range n).all (fun k => keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws (pS k) 1024) &&
    (List.range r).all (fun i => keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws (.r12, 384 * i) 384) &&
    (List.range e).all (fun j => keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws (.r13, 384 * j) 384)

def prfsKChk : Bool :=
  prfsChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (2 * L.k) L.oPR L.lPW && VG.Proof.MlKem.X86_64.KeyGen.kcChk L (prfsW (2 * L.k) L.oPR L.lPW) &&
    keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (prfsW (2 * L.k) L.oPR L.lPW) (sc oG) 32 && keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (prfsW (2 * L.k) L.oPR L.lPW) sigP 32 &&
    (List.range (L.k * L.k)).all (fun e => keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (prfsW (2 * L.k) L.oPR L.lPW) (pS (L.pA + e)) 1024)

/-- What `se N` writes. -/
abbrev seW (N : Nat) : List (Ptr × Nat) := [(pS N, 1024)] ++ [(pS N, 1024), (sc oSS, 1024)]

def seChk (N : Nat) : Bool :=
  twoChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (VG.Proof.MlKem.X86_64.KeyGen.prfO L N) 128 (pS N) 1024 && ipChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (pS N) && VG.Proof.MlKem.X86_64.KeyGen.restChk L N 0 0 (VG.Proof.MlKem.X86_64.KeyGen.seW N)

/-- What `row i` writes. -/
abbrev rowW (i : Nat) : List (Ptr × Nat) := dotW L.k ++ [(pS 15, 1024)] ++ [((.r12, 384 * i), 384)]

def rowChk (i : Nat) : Bool :=
  dotChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (fun j => L.aS i j) pS L.k && accChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (pS 15) (pS (L.k + i)) &&
    keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (dotW L.k) (pS (L.k + i)) 1024 && twoChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (pS 15) 1024 (.r12, 384 * i) 384 &&
    VG.Proof.MlKem.X86_64.KeyGen.restChk L (2 * L.k) i 0 (VG.Proof.MlKem.X86_64.KeyGen.rowW L i)

def encSChk (j : Nat) : Bool :=
  twoChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (pS j) 1024 (.r13, 384 * j) 384 && VG.Proof.MlKem.X86_64.KeyGen.restChk L (2 * L.k) L.k j [((.r13, 384 * j), 384)]

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
  eta : L.p.η₁ = 2 ∧ L.p.η₂ = 2
  ijT : ∀ e < L.k * L.k, (taint.check (X86_64.Taint.ofRegs [.rbx])
    (.block (setB (sc (oSB + 32)) (e % L.k) ++ setB (sc (oSB + 33)) (e / L.k))) (.block [])).isSome = true

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

variable (L : Kem)

/-- What every piece of key generation needs of the layout, evaluated for each parameter set. -/
structure KgWf : Prop extends VG.Proof.MlKem.X86_64.KemWf L where
  scr : 888 ≤ L.scr ∧ L.scr < 2 ^ 32
  small : ∀ b ∈ VG.Proof.MlKem.X86_64.KeyGen.kgB L, b.2 < 2 ^ 32
  -- `G(d ‖ k)`
  nb : inB (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (sc oNB) 1 = true
  nbK : VG.Proof.MlKem.X86_64.KeyGen.kcChk L [(sc oNB, 1)] = true
  gH : hashChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) [((.rbp, 0), 32), (sc oNB, 1)] 72 (sc oG) 64 = true
  gK : VG.Proof.MlKem.X86_64.KeyGen.kcChk L [(sc 0, 200), (sc 200, 640), (sc oG, 64)] = true
  gC : copyChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (sc oSB) (sc oG) 32 = true
  gCK : VG.Proof.MlKem.X86_64.KeyGen.kcChk L [(sc oSB, 32)] = true
  gG : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) [(sc oSB, 32)] (sc oG) 32 = true
  gS : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) [(sc oSB, 32)] sigP 32 = true
  -- the matrix
  kq : ∀ q < L.k * L.k / 4, VG.Proof.MlKem.X86_64.KeyGen.kqChk L (4 * q) = true
  kb : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → VG.Proof.MlKem.X86_64.KeyGen.kbChk L e = true
  flag : VG.Proof.MlKem.X86_64.KeyGen.kcChk L [] = true
  flagG : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) [] (sc oG) 32 = true
  flagS : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) [] sigP 32 = true
  flagB : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) [] (sc oSB) 32 = true
  flagA : ∀ e < L.k * L.k, keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) [] (pS (L.pA + e)) 1024 = true
  -- the keys
  prfs : VG.Proof.MlKem.X86_64.KeyGen.prfsKChk L = true
  se : ∀ N < 2 * L.k, VG.Proof.MlKem.X86_64.KeyGen.seChk L N = true
  row : ∀ i < L.k, VG.Proof.MlKem.X86_64.KeyGen.rowChk L i = true
  encS : ∀ j < L.k, VG.Proof.MlKem.X86_64.KeyGen.encSChk L j = true
  f₁ : copyChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (.r12, 384 * L.k) (sc oG) 32 = true
  f₁K : VG.Proof.MlKem.X86_64.KeyGen.kcChk L (VG.Proof.MlKem.X86_64.KeyGen.finW₁ L) = true
  f₁E : ∀ i < L.k, keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.finW₁ L) (.r12, 384 * i) 384 = true
  f₂ : copyChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (.r13, 384 * L.k) (.r12, 0) L.ekLen = true
  f₂K : VG.Proof.MlKem.X86_64.KeyGen.kcChk L (VG.Proof.MlKem.X86_64.KeyGen.finW₂ L) = true
  f₂E : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.finW₂ L) (.r12, 0) L.ekLen = true
  f₃ : hashChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) [((.r12, 0), L.ekLen)] 136 (.r13, 384 * L.k + L.ekLen) 32 = true
  f₃K : VG.Proof.MlKem.X86_64.KeyGen.kcChk L (VG.Proof.MlKem.X86_64.KeyGen.finW₃ L) = true
  f₃E : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.finW₃ L) (.r12, 0) L.ekLen = true
  f₄ : copyChk (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.kgW L) (.r13, 384 * L.k + L.ekLen + 32) (.rbp, 32) 32 = true
  f₄K : VG.Proof.MlKem.X86_64.KeyGen.kcChk L (VG.Proof.MlKem.X86_64.KeyGen.finW₄ L) = true
  f₄E : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.finW₄ L) (.r12, 0) L.ekLen = true
  dkS : ∀ j < L.k, keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.finW₁ L ++ VG.Proof.MlKem.X86_64.KeyGen.finW₂ L ++ VG.Proof.MlKem.X86_64.KeyGen.finW₃ L ++ VG.Proof.MlKem.X86_64.KeyGen.finW₄ L) (.r13, 384 * j) 384 = true
  dkE : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.finW₃ L ++ VG.Proof.MlKem.X86_64.KeyGen.finW₄ L) (.r13, 384 * L.k) L.ekLen = true
  dkH : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (VG.Proof.MlKem.X86_64.KeyGen.finW₄ L) (.r13, 384 * L.k + L.ekLen) 32 = true
  -- the end
  sv : ∀ k < 6, inB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (sc (oSV + 8 * k)) 8 = true
  -- constant time
  inBs : inB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (sc 0) 1 = true ∧ inB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (.r12, 0) 1 = true ∧ inB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) (.r13, 0) 1 = true
  nbT : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc oNB) L.k)) (.block [])).isSome = true
  finT₁ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) (copy (.r12, 384 * L.k) (sc oG) 32)
    h).isSome = true
  finT₂ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) (copy (.r13, 384 * L.k) (.r12, 0) L.ekLen)
    h).isSome = true
  finT₄ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13])
    (copy (.r13, 384 * L.k + L.ekLen + 32) (.rbp, 32) 32) h).isSome = true

section
variable {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ)
include W hp

theorem kgLay {s : State} (h : Top VG.Proof.MlKem.X86_64.KeyGen.kgM σ s) : Lay VG.Proof.MlKem.X86_64.KeyGen.kgR (VG.Proof.MlKem.X86_64.KeyGen.kgW L) s := by
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
  top : Top VG.Proof.MlKem.X86_64.KeyGen.kgM σ s
  d : bytesAt s.mem (pa s (.rbp, 0)) 32 = VG.Proof.MlKem.X86_64.KeyGen.kgD σ
  z : bytesAt s.mem (pa s (.rbp, 32)) 32 = VG.Proof.MlKem.X86_64.KeyGen.kgZ σ

section
variable {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ)
include W hp

theorem KC.lay {s : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KC σ s) : Lay VG.Proof.MlKem.X86_64.KeyGen.kgR (VG.Proof.MlKem.X86_64.KeyGen.kgW L) s := VG.Proof.MlKem.X86_64.KeyGen.kgLay W hp h.top

theorem KC.step {s s' : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KC σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (hc : VG.Proof.MlKem.X86_64.KeyGen.kcChk L ws = true) : VG.Proof.MlKem.X86_64.KeyGen.KC σ s' := by
  simp only [VG.Proof.MlKem.X86_64.KeyGen.kcChk, Bool.and_eq_true] at hc
  have L' := h.lay W hp
  exact ⟨h.top.step L' hP VG.Proof.MlKem.X86_64.KeyGen.kgM_bases hc.1.1, by rw [L'.keepBytes hP hc.1.2]; exact h.d,
    by rw [L'.keepBytes hP hc.2]; exact h.z⟩

end

theorem pro_eq : VG.Impl.MlKem.X86_64.KeyGen.pro = [.store (at_ .rcx 840) .rbx, .store (at_ .rcx 848) .rbp, .store (at_ .rcx 856) .r12,
    .store (at_ .rcx 864) .r13, .store (at_ .rcx 872) .r14, .store (at_ .rcx 880) .r15, .mov .rbx (.reg .rcx),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) :
    WP isa (.block VG.Impl.MlKem.X86_64.KeyGen.pro) σ fun s => VG.Proof.MlKem.X86_64.KeyGen.KC σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp'
  have hsc := W.scr
  have hS : ⟨σ.gpr .rcx, L.scr⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ L.scr → (⟨σ.gpr .rcx, L.scr⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ L.scr → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [VG.Proof.MlKem.X86_64.KeyGen.pro_eq]
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
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
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
    `(tactic| constructor <;> first | exact $w | exact ⟨_, by taint_decide⟩ | taint_decide | decide +kernel)

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.KgA`. -/
section

/-!
# ML-KEM on x86-64: key generation, `G` and the matrix

`(ρ, σ) = G(d ‖ k)` to `G`, and `ρ` to `SB` (`gRho_ok`); then `Â[i, j] =
SampleNTT(ρ ‖ j ‖ i)` for the `k²` entries `e = k i + j` (`samples_ok`), four
at a time with `vg_mlkem_sample_ntt4` (`quad_step`) and the last `k² mod 4`
on their own (`sample_step`), with `r15` the AND of the results: 1 exactly
when all of them succeed within 280 iterations (`allOk`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- Entry `e = k i + j` of a `k × k` matrix is `(i, j)`. -/
theorem divmod_ij {k i j : Nat} (hj : j < k) : (k * i + j) / k = i ∧ (k * i + j) % k = j :=
  ⟨by rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj, Nat.add_zero],
    by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]⟩

theorem ij_lt {k i j : Nat} (hi : i < k) (hj : j < k) : k * i + j < k * k :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi)

theorem div_lt_k {k e : Nat} (he : e < k * k) : e / k < k := Nat.div_lt_of_lt_mul he

theorem mod_lt_k {k e : Nat} (he : e < k * k) : e % k < k := Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by
  subst h; exact absurd he (Nat.not_lt_zero _))

/-- The first `e` entries of `Â` (`k × k`) sampled within 280 iterations. -/
def allOk (k : Nat) (ρ : List Byte) (e : Nat) : Prop :=
  ∀ e' < e, (sampleNTT minIterations (matSeed ρ (e' / k) (e' % k))).isSome

instance (k : Nat) (ρ : List Byte) (e : Nat) : Decidable (VG.Proof.MlKem.X86_64.allOk k ρ e) := by unfold VG.Proof.MlKem.X86_64.allOk; infer_instance

theorem allOk_succ {k : Nat} {ρ : List Byte} {e : Nat} :
    VG.Proof.MlKem.X86_64.allOk k ρ (e + 1) ↔ VG.Proof.MlKem.X86_64.allOk k ρ e ∧ (sampleNTT minIterations (matSeed ρ (e / k) (e % k))).isSome := by
  constructor
  · intro h; exact ⟨fun e' he => h e' (by omega), h e (by omega)⟩
  · rintro ⟨h, hk⟩ e' he
    rcases (by omega : e' < e ∨ e' = e) with he | rfl
    · exact h e' he
    · exact hk

theorem allOk_add4 {k : Nat} {ρ : List Byte} {e : Nat} :
    VG.Proof.MlKem.X86_64.allOk k ρ (e + 4) ↔ VG.Proof.MlKem.X86_64.allOk k ρ e ∧ ((List.range 4).all fun t =>
      (sampleNTT minIterations (matSeed ρ ((e + t) / k) ((e + t) % k))).isSome) = true := by
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h; exact ⟨fun e' he => h e' (by omega), fun t ht => h (e + t) (by omega)⟩
  · rintro ⟨h, h4⟩ e' he
    rcases (by omega : e' < e ∨ e ≤ e') with he' | he'
    · exact h e' he'
    · have := h4 (e' - e) (by omega)
      rwa [Nat.add_sub_cancel' he'] at this

theorem allOk_zero (k : Nat) (ρ : List Byte) : VG.Proof.MlKem.X86_64.allOk k ρ 0 := fun _ h => absurd h (Nat.not_lt_zero _)

/-- `r15` after one more `SampleNTT`. -/
theorem and_acc {r : BitVec 64} {p q : Prop} [Decidable p] [Decidable q] (hr : r = if p then 1 else 0) :
    BitVec.setWidth 64 (r.setWidth 32 &&& (if q then 1 else 0)) = if p ∧ q then 1 else 0 := by
  subst hr
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- `Â[i, j]`, if its `SampleNTT` succeeds. -/
def aHat (ρ : List Byte) (i j : Nat) : Poly := (sampleNTT minIterations (matSeed ρ i j)).getD VG.Spec.MlKem.zero

theorem aHat_eq {k : Nat} {ρ : List Byte} (h : VG.Proof.MlKem.X86_64.allOk k ρ (k * k)) {i j : Nat} (hi : i < k) (hj : j < k) :
    sampleNTT minIterations (matSeed ρ i j) = some (VG.Proof.MlKem.X86_64.aHat ρ i j) := by
  have := h (k * i + j) (VG.Proof.MlKem.X86_64.ij_lt hi hj)
  rw [(VG.Proof.MlKem.X86_64.divmod_ij hj).1, (VG.Proof.MlKem.X86_64.divmod_ij hj).2] at this
  unfold VG.Proof.MlKem.X86_64.aHat
  cases e : sampleNTT minIterations (matSeed ρ i j) with
  | none => rw [e] at this; cases this
  | some f => rfl

theorem not_allOk {k : Nat} {ρ : List Byte} (h : ¬ VG.Proof.MlKem.X86_64.allOk k ρ (k * k)) :
    ∃ i < k, ∃ j < k, sampleNTT minIterations (matSeed ρ i j) = none := by
  unfold VG.Proof.MlKem.X86_64.allOk at h
  simp only [Classical.not_forall] at h
  obtain ⟨e, he, hs⟩ := h
  refine ⟨e / k, VG.Proof.MlKem.X86_64.div_lt_k he, e % k, VG.Proof.MlKem.X86_64.mod_lt_k he, ?_⟩
  cases e' : sampleNTT minIterations (matSeed ρ (e / k) (e % k)) with
  | none => rfl
  | some f => rw [e'] at hs; exact absurd rfl hs

/-- Entry `e` of `Â` (`k × k`), as polynomial `pA + e`. -/
theorem aS_eq (L : Kem) (e : Nat) : L.aS (e / L.k) (e % L.k) = pS (L.pA + e) := by
  rw [Kem.aS, Nat.add_assoc, Nat.div_add_mod]

theorem aS_ij (L : Kem) (i j : Nat) : L.aS i j = pS (L.pA + (L.k * i + j)) := by
  rw [Kem.aS, Nat.add_assoc]

/-! ## Sampling the matrix, for any layout -/

/-- After the first `e` entries of `Â` (`k × k`, from polynomial `pA`): `r15`,
and the entries sampled, for the seed `ρ`. -/
structure MatB (L : Kem) (ρ : List Byte) (e : Nat) (s : State) : Prop where
  r15 : s.gpr .r15 = if VG.Proof.MlKem.X86_64.allOk L.k ρ e then 1 else 0
  mat : ∀ e' < e, ∀ f, sampleNTT minIterations (matSeed ρ (e' / L.k) (e' % L.k)) = some f →
    PolyIs s.mem (pa s (pS (L.pA + e'))) f

/-- The step of one entry. -/
theorem MatB.single {L : Kem} {ρ : List Byte} {e : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (h : VG.Proof.MlKem.X86_64.MatB L ρ e s) (hsb : bytesAt s.mem (pa s (sc oSB)) 32 = ρ) (Lx : Lay rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (kA : ∀ e' < e, keepB (rbs ++ wbs) ws (pS (L.pA + e')) 1024 = true)
    (h15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) (e / L.k) (e % L.k))).isSome
          then 1 else 0)))
    (hres : ∀ f, sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) (e / L.k) (e % L.k)) = some f →
        PolyIs s'.mem (pa s (pS (L.pA + e))) f) : VG.Proof.MlKem.X86_64.MatB L ρ (e + 1) s' := by
  refine ⟨?_, fun e' he' f hf => ?_⟩
  · rw [h15, hsb, VG.Proof.MlKem.X86_64.and_acc h.r15]
    exact ite_congr (propext allOk_succ.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · exact Lx.keepPoly hP (kA e' he') (h.mat e' he' f hf)
    · rw [hP.pa rbx_bases]
      exact hres f (by rw [hsb]; exact hf)

/-- The step of four entries. -/
theorem MatB.four {L : Kem} {ρ : List Byte} {e : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (h : VG.Proof.MlKem.X86_64.MatB L ρ e s) (hsb : bytesAt s.mem (pa s (sc oSB)) 32 = ρ) (Lx : Lay rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (kA : ∀ e' < e, keepB (rbs ++ wbs) ws (pS (L.pA + e')) 1024 = true)
    (h15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (List.range 4).all (fun t => (sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e + t) / L.k) ((e + t) % L.k))).isSome) then 1 else 0)))
    (hres : ∀ t < 4, ∀ f, sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e + t) / L.k) ((e + t) % L.k)) = some f →
        PolyIs s'.mem (pa s (sc (oP (L.pA + e) + 1024 * t))) f) : VG.Proof.MlKem.X86_64.MatB L ρ (e + 4) s' := by
  refine ⟨?_, fun e' he' f hf => ?_⟩
  · rw [h15, hsb, VG.Proof.MlKem.X86_64.and_acc h.r15]
    exact ite_congr (propext allOk_add4.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e ≤ e') with he'' | he''
    · exact Lx.keepPoly hP (kA e' he'') (h.mat e' he'' f hf)
    · have := hres (e' - e) (by omega) f (by rw [hsb, Nat.add_sub_cancel' he'']; exact hf)
      rw [hP.pa rbx_bases]
      rwa [show oP (L.pA + e) + 1024 * (e' - e) = oP (L.pA + e') by simp only [oP]; omega] at this

theorem MatB.zero (L : Kem) (ρ : List Byte) {s : State} (h15 : s.gpr .r15 = 1) : VG.Proof.MlKem.X86_64.MatB L ρ 0 s :=
  ⟨by rw [h15, ifp (VG.Proof.MlKem.X86_64.allOk_zero _ _)], fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- Every entry of `Â`, once all were sampled. -/
theorem MatB.all {L : Kem} {ρ : List Byte} {s : State} (h : VG.Proof.MlKem.X86_64.MatB L ρ (L.k * L.k) s)
    (ho : VG.Proof.MlKem.X86_64.allOk L.k ρ (L.k * L.k)) : ∀ i < L.k, ∀ j < L.k, PolyIs s.mem (pa s (L.aS i j)) (VG.Proof.MlKem.X86_64.aHat ρ i j) :=
  fun i hi j hj => by
    have := h.mat (L.k * i + j) (VG.Proof.MlKem.X86_64.ij_lt hi hj) (VG.Proof.MlKem.X86_64.aHat ρ i j)
    rw [(VG.Proof.MlKem.X86_64.divmod_ij hj).1, (VG.Proof.MlKem.X86_64.divmod_ij hj).2] at this
    rw [VG.Proof.MlKem.X86_64.aS_ij L i j]
    exact this (VG.Proof.MlKem.X86_64.aHat_eq ho hi hj)

/-- The entries `e, …, e + n - 1`, from any invariant `I e` whose steps are
those of one entry and of four (`ents`). -/
theorem ents_ok (L : Kem) (c : Callee4) {I : Nat → State → Prop}
    (h1 : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → ∀ s, I e s →
      WP isa (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) s (I (e + 1)))
    (h4 : ∀ q < L.k * L.k / 4, ∀ s, I (4 * q) s →
      WP isa (quad c L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) s (I (4 * q + 4))) :
    ∀ n e, e + n = L.k * L.k → (e % 4 = 0 ∨ 4 * (L.k * L.k / 4) ≤ e) → ∀ s, I e s → WP isa (L.ents c e n) s (I (e + n))
  | 0, e, _, _, s, hs => by simp only [Kem.ents]; exact WP.block_nil hs
  | 1, e, he, hq, s, hs => by
    simp only [Kem.ents]; exact h1 e (by omega) (by omega) s hs
  | 2, e, he, hq, s, hs => by
    simp only [Kem.ents]
    exact WP.seq (WP.mono (h1 e (by omega) (by omega) s hs) fun s₁ h₁ =>
      VG.Proof.MlKem.X86_64.ents_ok L c h1 h4 1 (e + 1) (by omega) (by omega) s₁ h₁)
  | 3, e, he, hq, s, hs => by
    simp only [Kem.ents]
    refine WP.seq (WP.mono (h1 e (by omega) (by omega) s hs) fun s₁ h₁ => ?_)
    have := VG.Proof.MlKem.X86_64.ents_ok L c h1 h4 2 (e + 1) (by omega) (by omega) s₁ h₁
    rwa [show e + 1 + 2 = e + 3 by omega] at this
  | 4, e, he, hq, s, hs => by
    simp only [Kem.ents]
    have := h4 (e / 4) (by omega) s (by rwa [show 4 * (e / 4) = e by omega])
    rwa [show 4 * (e / 4) = e by omega] at this
  | n + 5, e, he, hq, s, hs => by
    simp only [Kem.ents]
    have := h4 (e / 4) (by omega) s (by rwa [show 4 * (e / 4) = e by omega])
    rw [show 4 * (e / 4) = e by omega] at this
    refine WP.seq (WP.mono this fun s₁ h₁ => ?_)
    have := VG.Proof.MlKem.X86_64.ents_ok L c h1 h4 (n + 1) (e + 4) (by omega) (by omega) s₁ h₁
    rwa [show e + 4 + (n + 1) = e + (n + 5) by omega] at this

theorem samples_ok' (L : Kem) (c : Callee4) {I : Nat → State → Prop}
    (h1 : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → ∀ s, I e s →
      WP isa (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) s (I (e + 1)))
    (h4 : ∀ q < L.k * L.k / 4, ∀ s, I (4 * q) s →
      WP isa (quad c L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) s (I (4 * q + 4)))
    {s : State} (h : I 0 s) : WP isa (L.samples c) s (I (L.k * L.k)) := by
  have := VG.Proof.MlKem.X86_64.ents_ok L c h1 h4 (L.k * L.k) 0 (by omega) (by omega) s h
  rwa [Nat.zero_add] at this

/-- `ents_ok`, for constant time. -/
theorem ents_tr (L : Kem) (c : Callee4) {R : Nat → State → State → Prop}
    (h1 : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e →
      RelCT isa (R e) (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) (R (e + 1)))
    (h4 : ∀ q < L.k * L.k / 4, RelCT isa (R (4 * q)) (quad c L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) (R (4 * q + 4))) :
    ∀ n e, e + n = L.k * L.k → (e % 4 = 0 ∨ 4 * (L.k * L.k / 4) ≤ e) → RelCT isa (R e) (L.ents c e n) (R (e + n))
  | 0, e, _, _ => by simp only [Kem.ents]; exact nil_tr
  | 1, e, he, hq => by simp only [Kem.ents]; exact h1 e (by omega) (by omega)
  | 2, e, he, hq => by
    simp only [Kem.ents]
    exact RelCT.seq (h1 e (by omega) (by omega)) (VG.Proof.MlKem.X86_64.ents_tr L c h1 h4 1 (e + 1) (by omega) (by omega))
  | 3, e, he, hq => by
    simp only [Kem.ents]
    have := VG.Proof.MlKem.X86_64.ents_tr L c h1 h4 2 (e + 1) (by omega) (by omega)
    rw [show e + 1 + 2 = e + 3 by omega] at this
    exact RelCT.seq (h1 e (by omega) (by omega)) this
  | 4, e, he, hq => by
    simp only [Kem.ents]
    have := h4 (e / 4) (by omega)
    rwa [show 4 * (e / 4) = e by omega] at this
  | n + 5, e, he, hq => by
    simp only [Kem.ents]
    have := h4 (e / 4) (by omega)
    rw [show 4 * (e / 4) = e by omega] at this
    have h' := VG.Proof.MlKem.X86_64.ents_tr L c h1 h4 (n + 1) (e + 4) (by omega) (by omega)
    rw [show e + 4 + (n + 1) = e + (n + 5) by omega] at h'
    exact RelCT.seq this h'

theorem samples_tr' (L : Kem) (c : Callee4) {R : Nat → State → State → Prop}
    (h1 : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e →
      RelCT isa (R e) (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) (R (e + 1)))
    (h4 : ∀ q < L.k * L.k / 4, RelCT isa (R (4 * q)) (quad c L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) (R (4 * q + 4))) :
    RelCT isa (R 0) (L.samples c) (R (L.k * L.k)) := by
  have := VG.Proof.MlKem.X86_64.ents_tr L c h1 h4 (L.k * L.k) 0 (by omega) (by omega)
  rwa [Nat.zero_add] at this

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

/-! ## `G(d ‖ k)` -/

theorem sha3Suffix6 : BitVec.ofNat 8 6 = Spec.Sha3.sha3Suffix := by decide

/-- After `G`: `ρ` and `σ` at `G`, and `ρ` at `SB`. -/
structure KA (L : Kem) (σ s : State) : Prop where
  kc : VG.Proof.MlKem.X86_64.KeyGen.KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = KPke.kgRho L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ)
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ)
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = KPke.kgRho L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ)

theorem gRho_ok {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {s : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KC σ s)
    (h15 : s.gpr .r15 = 1) : WP isa (gRho L) s fun s' => VG.Proof.MlKem.X86_64.KeyGen.KA L σ s' ∧ s'.gpr .r15 = 1 := by
  have L₀ := h.lay W hp
  unfold gRho
  refine WP.seq (WP.mono (setB_okL L₀ (by decide) (by have := W.k; omega) (p := sc oNB) (v := L.k) W.nb)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have h₁ := h.step W hp hP₁.b W.nbK
  have L₁ := h₁.lay W hp
  refine WP.seq (WP.mono (hash_ok (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (ps := [((.rbp, 0), 32), (sc oNB, 1)]) (rate := 72) (out := sc oG)
    (len := 64) W.gH (show 6 < 256 by decide) L₁) fun s₂ ⟨hP₂, ho₂⟩ => ?_)
  have h₂ := h₁.step W hp hP₂.b W.gK
  have L₂ := h₂.lay W hp
  refine WP.mono (copy_okL L₂ (dst := sc oSB) (src := sc oG) (n := 32) (by decide) W.gC)
    fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have h₃ := h₂.step W hp hP₃.b W.gCK
  -- The output of `G`.
  have hpc : pieces s₁ [((.rbp, 0), 32), (sc oNB, 1)] = VG.Proof.MlKem.X86_64.KeyGen.kgD σ ++ [BitVec.ofNat 8 L.k] := by
    simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h₁.d]
    rw [show pa s₁ (sc oNB) = pa s (sc oNB) from hP₁.pa rbx_cs, hb₁]
  rw [hpc, VG.Proof.MlKem.X86_64.KeyGen.sha3Suffix6, ← sha3_512_eq] at ho₂
  have eG : pa s₂ (sc oG) = pa s₁ (sc oG) := hP₂.pa rbx_cs
  have hG : bytesAt s₂.mem (pa s₂ (sc oG)) 64 = Spec.Sha3.sha3_512 (VG.Proof.MlKem.X86_64.KeyGen.kgD σ ++ [BitVec.ofNat 8 L.k]) := by
    rw [eG]; exact ho₂
  have hρ : bytesAt s₂.mem (pa s₂ (sc oG)) 32 = KPke.kgRho L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ) := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hG]; rfl
  have hσ : bytesAt s₂.mem (pa s₂ sigP) 32 = KPke.kgSigma L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ) := by
    have e := bytesAt_drop s₂.mem (pa s₂ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₂.mem (pa s₂ (sc oG)) 64).drop 32 = bytesAt s₂.mem (pa s₂ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hG]; rfl
  refine ⟨⟨h₃, ?_, ?_, ?_⟩, ?_⟩
  · rw [L₂.keepBytes hP₃.b W.gG]; exact hρ
  · rw [L₂.keepBytes hP₃.b W.gS]; exact hσ
  · rw [show pa s₃ (sc oSB) = pa s₂ (sc oSB) from hP₃.pa rbx_cs, hb₃, hρ]
  · rw [hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h15]

/-! ## The matrix -/

/-- After the first `e` entries of `Â`. -/
structure KB (L : Kem) (e : Nat) (σ s : State) : Prop where
  a : VG.Proof.MlKem.X86_64.KeyGen.KA L σ s
  m : VG.Proof.MlKem.X86_64.MatB L (KPke.kgRho L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ)) e s

theorem KB.zero {L : Kem} {σ s : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KA L σ s) (h15 : s.gpr .r15 = 1) : VG.Proof.MlKem.X86_64.KeyGen.KB L 0 σ s :=
  ⟨h, MatB.zero L _ h15⟩

/-- The pieces of the key's state that a piece writing `ws` keeps. -/
theorem KA.keep {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {s s' : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KA L σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hkc : VG.Proof.MlKem.X86_64.KeyGen.kcChk L ws = true) (kG : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws (sc oG) 32 = true)
    (kS : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws sigP 32 = true) (kB : keepB (VG.Proof.MlKem.X86_64.KeyGen.kgB L) ws (sc oSB) 32 = true) : VG.Proof.MlKem.X86_64.KeyGen.KA L σ s' := by
  have L₀ := h.kc.lay W hp
  exact ⟨h.kc.step W hp hP hkc, by rw [L₀.keepBytes hP kG]; exact h.rho, by rw [L₀.keepBytes hP kS]; exact h.sig,
    by rw [L₀.keepBytes hP kB]; exact h.sb⟩

theorem sample_step {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {e : Nat} (he : e < L.k * L.k)
    (he' : 4 * (L.k * L.k / 4) ≤ e) {s : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KB L e σ s) :
    WP isa (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) s (VG.Proof.MlKem.X86_64.KeyGen.KB L (e + 1) σ) := by
  have hc := W.kb e he he'
  simp only [VG.Proof.MlKem.X86_64.KeyGen.kbChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hij, hkc⟩, kG⟩, kS⟩, kB⟩, kA⟩ := hc
  have hk := W.k
  have L₀ := h.a.kc.lay W hp
  refine WP.mono (sampleIJ_ok L₀ (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) rbx_na (by have := VG.Proof.MlKem.X86_64.div_lt_k he; omega) (by have := VG.Proof.MlKem.X86_64.mod_lt_k he; omega) hij)
    fun s' ⟨hP, h15, hres⟩ => ⟨h.a.keep W hp hP hkc kG kS kB, h.m.single h.a.sb L₀ hP kA h15 hres⟩

theorem quad_step (v : Sample4Impl) {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {q : Nat}
    (hq : q < L.k * L.k / 4) {s : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KB L (4 * q) σ s) :
    WP isa (quad v.callee L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) s (VG.Proof.MlKem.X86_64.KeyGen.KB L (4 * q + 4) σ) := by
  have hc := W.kq q hq
  simp only [VG.Proof.MlKem.X86_64.KeyGen.kqChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hq', hkc⟩, kG⟩, kS⟩, kB⟩, kA⟩ := hc
  have hk := W.k
  have L₀ := h.a.kc.lay W hp
  refine WP.mono (VG.Proof.MlKem.X86_64.quad_ok v L₀ (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (by have : L.k * L.k ≤ 16 := Nat.mul_le_mul hk.2 hk.2; omega) hq')
    fun s' ⟨hP, h15, hres⟩ => ⟨h.a.keep W hp hP hkc kG kS kB, h.m.four h.a.sb L₀ hP kA h15 hres⟩

theorem samples_ok (v : Sample4Impl) {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {s : State}
    (h : VG.Proof.MlKem.X86_64.KeyGen.KB L 0 σ s) : WP isa (L.samples v.callee) s (VG.Proof.MlKem.X86_64.KeyGen.KB L (L.k * L.k) σ) :=
  VG.Proof.MlKem.X86_64.samples_ok' L v.callee (I := fun e => VG.Proof.MlKem.X86_64.KeyGen.KB L e σ) (fun _ he he' _ hs => VG.Proof.MlKem.X86_64.KeyGen.sample_step W hp he he' hs)
    (fun _ hq _ hs => VG.Proof.MlKem.X86_64.KeyGen.quad_step v W hp hq hs) h

end KeyGen

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.KgB`. -/
section

/-!
# ML-KEM on x86-64: key generation, the keys

When every entry of `Â` was sampled (`allOk`): `ŝ` and `ê` (`se_ok`), `t̂`
encoded to `ek` (`row_ok`), `ŝ` encoded to `dk` (`encS_ok`), and `ρ`, `ek`,
`H(ek)` and `z` to the keys (`fin_ok`). Between the steps, `KRest n r e`: the
first `n` of `ŝ ‖ ê`, `r` rows of `ek` and `e` of `dk` are done.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem bytesAt_split (m : Mem) (s : State) (r : Reg) (o a b : Nat) :
    bytesAt m (pa s (r, o)) (a + b) = bytesAt m (pa s (r, o)) a ++ bytesAt m (pa s (r, o + a)) b := by
  rw [bytesAt_add, pa, pa, off_add]

/-- `k` consecutive pieces of `c` bytes. -/
theorem bytesAt_catK (m : Mem) (s : State) (r : Reg) (o c : Nat) (f : Nat → List Byte) :
    ∀ k, (∀ i < k, bytesAt m (pa s (r, o + c * i)) c = f i) → bytesAt m (pa s (r, o)) (c * k) = KPke.catK f k
  | 0, _ => rfl
  | k + 1, h => by
    rw [KPke.catK, KPke.foldK_succ List.nil_append, ← KPke.catK, Nat.mul_succ, VG.Proof.MlKem.X86_64.bytesAt_split,
      VG.Proof.MlKem.X86_64.bytesAt_catK m s r o c f k fun i hi => h i (by omega), h k (by omega)]

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

/-- `ρ` of `σ`. -/
abbrev rhoK (L : Kem) (σ : State) : List Byte := KPke.kgRho L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ)

/-- After the matrix, when every `SampleNTT` succeeded. -/
structure KRest0 (L : Kem) (σ s : State) : Prop where
  kc : VG.Proof.MlKem.X86_64.KeyGen.KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ)
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) (e / L.k) (e % L.k))

/-- The steps done after the outputs of `PRF₂`. -/
structure KRest (L : Kem) (n r e : Nat) (σ s : State) : Prop where
  kc : VG.Proof.MlKem.X86_64.KeyGen.KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ)
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) (e / L.k) (e % L.k))
  prf : ∀ N < 2 * L.k, bytesAt s.mem (pa s (VG.Proof.MlKem.X86_64.KeyGen.prfO L N)) 128 = prf 2 (KPke.kgSigma L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ)) (BitVec.ofNat 8 N)
  se : ∀ k < n, PolyIs s.mem (pa s (pS k)) (ntt (cbd (KPke.kgSigma L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ)) k))
  ek : ∀ i < r, bytesAt s.mem (pa s (.r12, 384 * i)) 384 = encode12 (KPke.kgT L.p (VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ)) (VG.Proof.MlKem.X86_64.KeyGen.kgD σ) i)
  dk : ∀ j < e, bytesAt s.mem (pa s (.r13, 384 * j)) 384 = encode12 (KPke.kgS L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ) j)

theorem KRest.keep {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {n r e : Nat} {s s' : State}
    (h : VG.Proof.MlKem.X86_64.KeyGen.KRest L n r e σ s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : VG.Proof.MlKem.X86_64.KeyGen.restChk L n r e ws = true) :
    VG.Proof.MlKem.X86_64.KeyGen.KRest L n r e σ s' := by
  simp only [VG.Proof.MlKem.X86_64.KeyGen.restChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hkc, kG⟩, kS⟩, kA⟩, kR⟩, kP⟩, kE⟩, kD⟩ := hc
  have L₀ := h.kc.lay W hp
  exact ⟨h.kc.step W hp hP.b hkc, by rw [L₀.keepBytes hP.b kG]; exact h.rho, by rw [L₀.keepBytes hP.b kS]; exact h.sig,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he),
    fun N hN => by rw [L₀.keepBytes hP.b (kR N hN)]; exact h.prf N hN, fun k hk => L₀.keepPoly hP.b (kP k hk) (h.se k hk),
    fun i hi => by rw [L₀.keepBytes hP.b (kE i hi)]; exact h.ek i hi,
    fun j hj => by rw [L₀.keepBytes hP.b (kD j hj)]; exact h.dk j hj⟩

/-- After the matrix, when every `SampleNTT` succeeded. -/
theorem KRest0.start {L : Kem} {σ : State} {s : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KB L (L.k * L.k) σ s) (ho : VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) (L.k * L.k)) :
    VG.Proof.MlKem.X86_64.KeyGen.KRest0 L σ s :=
  ⟨h.a.kc, h.a.rho, h.a.sig, by rw [h.m.r15, ifp ho], fun e he =>
    h.m.mat e he _ (VG.Proof.MlKem.X86_64.aHat_eq ho (VG.Proof.MlKem.X86_64.div_lt_k he) (VG.Proof.MlKem.X86_64.mod_lt_k he))⟩

/-- `Â[i, j]`, from the entries. -/
theorem KRest.matIJ {L : Kem} {n r e : Nat} {σ s : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KRest L n r e σ s) {i j : Nat} (hi : i < L.k)
    (hj : j < L.k) : PolyIs s.mem (pa s (L.aS i j)) (VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) i j) := by
  have := h.mat (L.k * i + j) (VG.Proof.MlKem.X86_64.ij_lt hi hj)
  rwa [(VG.Proof.MlKem.X86_64.divmod_ij hj).1, (VG.Proof.MlKem.X86_64.divmod_ij hj).2, ← VG.Proof.MlKem.X86_64.aS_ij] at this

/-! ## The outputs of `PRF₂` -/

theorem prfs_okK (v : Sample4Impl) {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {s : State}
    (h : VG.Proof.MlKem.X86_64.KeyGen.KRest0 L σ s) : WP isa (v.callee.prfs 0 (2 * L.k) L.oPR L.lPW) s (VG.Proof.MlKem.X86_64.KeyGen.KRest L 0 0 0 σ) := by
  have hc := W.prfs
  simp only [VG.Proof.MlKem.X86_64.KeyGen.prfsKChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hpc, hkc⟩, kG⟩, kS⟩, kA⟩ := hc
  have L₀ := h.kc.lay W hp
  refine WP.mono (v.prfs_ok L₀ (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (by have := W.k; omega) hpc) fun s' ⟨hP, hb⟩ => ?_
  have hσ : bytesAt s'.mem (pa s' sigP) 32 = bytesAt s.mem (pa s sigP) 32 := L₀.keepBytes hP.b kS
  refine ⟨h.kc.step W hp hP.b hkc, by rw [L₀.keepBytes hP.b kG]; exact h.rho, hσ.trans h.sig,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he), fun N hN => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [VG.Proof.MlKem.X86_64.KeyGen.prfO, hP.pa rbx_cs, hb N hN, h.sig, Nat.zero_add]

/-! ## `ŝ` and `ê` -/

theorem se_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {N : Nat}
    (hN : N < 2 * L.k) {s : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KRest L N 0 0 σ s) : WP isa (se L A N) s (VG.Proof.MlKem.X86_64.KeyGen.KRest L (N + 1) 0 0 σ) := by
  have hc := W.se N hN
  simp only [VG.Proof.MlKem.X86_64.KeyGen.seChk, Bool.and_eq_true] at hc
  obtain ⟨⟨htw, hic⟩, hrc⟩ := hc
  have L₀ := h.kc.lay W hp
  unfold se
  refine WP.seq (WP.mono (cbd2At_okL L₀ rbx_na htw) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L₀.post hP₁.b (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L)
  rw [h.prf N hN, ← hP₁.pa rbx_cs] at hp₁
  refine WP.mono (nttAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_
  have hk := h.keep W hp (PPost.app hP₁ hP₂ (by simp [calleeSaved])) hrc
  refine ⟨hk.kc, hk.rho, hk.sig, hk.r15, hk.mat, hk.prf, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : k < N ∨ k = N) with hk' | rfl
  · exact hk.se k hk'
  · rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂; exact hp₂

theorem r12_na : Reg.r12 ∉ argRegs := by decide
theorem r13_na : Reg.r13 ∉ argRegs := by decide
theorem r12_cs : Reg.r12 ∈ calleeSaved := by decide
theorem r13_cs : Reg.r13 ∈ calleeSaved := by decide

/-! ## `t̂`, encoded to `ek` -/

theorem row_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {i : Nat}
    (hi : i < L.k) {s : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KRest L (2 * L.k) i 0 σ s) : WP isa (row L A i) s (VG.Proof.MlKem.X86_64.KeyGen.KRest L (2 * L.k) (i + 1) 0 σ) := by
  have hc := W.row i hi
  simp only [VG.Proof.MlKem.X86_64.KeyGen.rowChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hdc, hac⟩, hk3⟩, htw⟩, hrc⟩ := hc
  have L₀ := h.kc.lay W hp
  unfold row
  refine WP.seq (WP.mono (dotN_ok hA (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) W.k.1 (dotChk_spec hdc) L₀ (a := fun j => VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) i j)
    (b := KPke.kgS L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ)) (fun k hk => h.matIJ hi hk) (fun k hk => h.se k (by omega))) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L₀.post hP₁.b (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L)
  rw [← hP₁.pa rbx_cs] at hp₁
  have he₁ := L₀.keepPoly hP₁.b hk3 (h.se (L.k + i) (by omega))
  refine WP.seq (WP.mono (addAt_ok L₁ rbx_na hac hp₁.1 he₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L)
  rw [hp₁.2, he₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.mono (enc12At_okL L₂ VG.Proof.MlKem.X86_64.KeyGen.r12_na htw hp₂.1) fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have hk := h.keep W hp (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by simp [calleeSaved])) hrc
  refine ⟨hk.kc, hk.rho, hk.sig, hk.r15, hk.mat, hk.prf, hk.se, fun i' hi' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk.ek i' hi'
  · rw [hP₃.pa VG.Proof.MlKem.X86_64.KeyGen.r12_cs, hb₃, hp₂.2]; rfl

/-! ## `ŝ`, encoded to `dk` -/

theorem encS_ok {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {j : Nat} (hj : j < L.k) {s : State}
    (h : VG.Proof.MlKem.X86_64.KeyGen.KRest L (2 * L.k) L.k j σ s) : WP isa (encS j) s (VG.Proof.MlKem.X86_64.KeyGen.KRest L (2 * L.k) L.k (j + 1) σ) := by
  have hc := W.encS j hj
  simp only [VG.Proof.MlKem.X86_64.KeyGen.encSChk, Bool.and_eq_true] at hc
  have L₀ := h.kc.lay W hp
  have hs := h.se j (by omega)
  refine WP.mono (enc12At_okL L₀ VG.Proof.MlKem.X86_64.KeyGen.r13_na hc.1 hs.1) fun s' ⟨hP, hb⟩ => ?_
  have hk := h.keep W hp hP hc.2
  refine ⟨hk.kc, hk.rho, hk.sig, hk.r15, hk.mat, hk.prf, hk.se, hk.ek, fun j' hj' => ?_⟩
  rcases (by omega : j' < j ∨ j' = j) with hj' | rfl
  · exact hk.dk j' hj'
  · rw [hP.pa VG.Proof.MlKem.X86_64.KeyGen.r13_cs, hb, hs.2]; rfl

/-! ## The rest of the keys -/

/-- `ek` and `dk_PKE`. -/
abbrev ekK (L : Kem) (σ : State) : List Byte := KPke.ekPKE L.p (VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ)) (VG.Proof.MlKem.X86_64.KeyGen.kgD σ)
abbrev dkK (L : Kem) (σ : State) : List Byte := KPke.dkPKE L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ)

/-- The keys. -/
structure KFin (L : Kem) (σ s : State) : Prop where
  kc : VG.Proof.MlKem.X86_64.KeyGen.KC σ s
  r15 : s.gpr .r15 = 1
  ek : bytesAt s.mem (pa s (.r12, 0)) L.ekLen = VG.Proof.MlKem.X86_64.KeyGen.ekK L σ
  dk : bytesAt s.mem (pa s (.r13, 0)) L.dkLen = VG.Proof.MlKem.X86_64.KeyGen.dkK L σ ++ VG.Proof.MlKem.X86_64.KeyGen.ekK L σ ++ H (VG.Proof.MlKem.X86_64.KeyGen.ekK L σ) ++ VG.Proof.MlKem.X86_64.KeyGen.kgZ σ

theorem fin_ok {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {s : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KRest L (2 * L.k) L.k L.k σ s) :
    WP isa (fin L) s (VG.Proof.MlKem.X86_64.KeyGen.KFin L σ) := by
  have L₀ := h.kc.lay W hp
  unfold fin
  -- `ρ` to `ek`.
  refine WP.seq (WP.mono (copy_okL L₀ (dst := (.r12, 384 * L.k)) (src := sc oG) (n := 32) (by decide) W.f₁)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.kc.step W hp hP₁.b W.f₁K
  have L₁ := k₁.lay W hp
  have hek : bytesAt s₁.mem (pa s₁ (.r12, 0)) L.ekLen = VG.Proof.MlKem.X86_64.KeyGen.ekK L σ := by
    rw [Kem.ekLen, Params.ekLen, VG.Proof.MlKem.X86_64.bytesAt_split, show 0 + 384 * L.p.k = 384 * L.k from Nat.zero_add _,
      hP₁.pa (p := (.r12, 384 * L.k)) VG.Proof.MlKem.X86_64.KeyGen.r12_cs, hb₁, h.rho, VG.Proof.MlKem.X86_64.KeyGen.ekK, KPke.ekPKE]
    refine congrArg (· ++ _) (VG.Proof.MlKem.X86_64.bytesAt_catK _ _ _ _ _ _ L.k fun i hi => ?_)
    rw [Nat.zero_add, L₀.keepBytes hP₁.b (W.f₁E i hi)]
    exact h.ek i hi
  -- `ek` to `dk`.
  refine WP.seq (WP.mono (copy_okL L₁ (dst := (.r13, 384 * L.k)) (src := (.r12, 0)) (n := L.ekLen) (by decide) W.f₂)
    fun s₂ ⟨hP₂, hb₂⟩ => ?_)
  have k₂ := k₁.step W hp hP₂.b W.f₂K
  have L₂ := k₂.lay W hp
  rw [hek] at hb₂
  have hek₂ : bytesAt s₂.mem (pa s₂ (.r12, 0)) L.ekLen = VG.Proof.MlKem.X86_64.KeyGen.ekK L σ := by
    rw [L₁.keepBytes hP₂.b W.f₂E]; exact hek
  -- `H(ek)`.
  refine WP.seq (WP.mono (hash_ok (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (ps := [((.r12, 0), L.ekLen)]) (rate := 136)
    (out := (.r13, 384 * L.k + L.ekLen)) (len := 32) W.f₃ (show 6 < 256 by decide) L₂) fun s₃ ⟨hP₃, hb₃⟩ => ?_)
  have k₃ := k₂.step W hp hP₃.b W.f₃K
  have L₃ := k₃.lay W hp
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hek₂, VG.Proof.MlKem.X86_64.KeyGen.sha3Suffix6] at hb₃
  rw [← H_eq] at hb₃
  -- `z`.
  refine WP.mono (copy_okL L₃ (dst := (.r13, 384 * L.k + L.ekLen + 32)) (src := (.rbp, 32)) (n := 32) (by decide) W.f₄)
    fun s₄ ⟨hP₄, hb₄⟩ => ?_
  have k₄ := k₃.step W hp hP₄.b W.f₄K
  rw [k₃.z] at hb₄
  refine ⟨k₄, ?_, ?_, ?_⟩
  · rw [hP₄.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15]
  · rw [L₃.keepBytes hP₄.b W.f₄E, L₂.keepBytes hP₃.b W.f₃E]; exact hek₂
  · have hP := PPost.app (PPost.app (PPost.app hP₁ hP₂ (by simp [calleeSaved])) hP₃ (by simp [calleeSaved])) hP₄
      (by simp [calleeSaved])
    have hP' := PPost.app hP₃ hP₄ (by simp [calleeSaved])
    rw [show L.dkLen = 384 * L.k + L.ekLen + 32 + 32 by
        simp only [Kem.k, Kem.dkLen, Kem.ekLen, Params.dkLen, Params.ekLen]; omega,
      VG.Proof.MlKem.X86_64.bytesAt_split, VG.Proof.MlKem.X86_64.bytesAt_split, VG.Proof.MlKem.X86_64.bytesAt_split, Nat.zero_add, Nat.zero_add, Nat.zero_add]
    rw [hP₄.pa (p := (.r13, 384 * L.k + L.ekLen + 32)) VG.Proof.MlKem.X86_64.KeyGen.r13_cs, hb₄,
      L₃.keepBytes hP₄.b W.dkH, hP₃.pa (p := (.r13, 384 * L.k + L.ekLen)) VG.Proof.MlKem.X86_64.KeyGen.r13_cs, hb₃,
      L₂.keepBytes hP'.b W.dkE, hP₂.pa (p := (.r13, 384 * L.k)) VG.Proof.MlKem.X86_64.KeyGen.r13_cs, hb₂, VG.Proof.MlKem.X86_64.KeyGen.dkK, KPke.dkPKE]
    refine congrArg (· ++ _ ++ _ ++ _) (VG.Proof.MlKem.X86_64.bytesAt_catK _ _ _ _ _ _ L.k fun j hj => ?_)
    rw [Nat.zero_add, L₀.keepBytes hP.b (W.dkS j hj)]
    exact h.dk j hj

end KeyGen

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.KgCT`. -/
section

/-!
# ML-KEM on x86-64: key generation, constant time of the pieces

Two runs from entry states that agree on the public data (`keyGenK.pub`: the
pointers, the stack pointer and `ρ`), each at the same step with its invariant
(`Rel2`), are in the same layout (`kc_lrel`), and each piece leaks the same in
both (`gRho_tr`, `samples_tr`, `se_tr`, `row_tr`, `encS_tr`, `fin_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- A piece's constant time in a relation implied by the invariants of two runs. -/
theorem rel2_of {Pre : State → Prop} {Pub : State → State → Prop} {I : State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, Pre σ₁ → Pre σ₂ → Pub σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (Rel2 Pre Pub I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

variable {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L)
include W

theorem kc_lrel {σ₁ σ₂ x y : State} (p₁ : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ₁) (p₂ : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ₂) (pub : (VG.Proof.MlKem.X86_64.keyGenK L).pub σ₁ σ₂)
    (h₁ : VG.Proof.MlKem.X86_64.KeyGen.KC σ₁ x) (h₂ : VG.Proof.MlKem.X86_64.KeyGen.KC σ₂ y) : LRel VG.Proof.MlKem.X86_64.KeyGen.kgR (VG.Proof.MlKem.X86_64.KeyGen.kgW L) x y := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := pub
  refine ⟨h₁.lay W p₁, h₂.lay W p₂, fa4 ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e5]⟩
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.rbx, .rcx) (by decide), h₂.top.regs (.rbx, .rcx) (by decide), e4]
  · rw [h₁.top.regs (.r12, .rsi) (by decide), h₂.top.regs (.r12, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.r13, .rdx) (by decide), h₂.top.regs (.r13, .rdx) (by decide), e3]

omit W in
theorem rho_pub {σ₁ σ₂ : State} (pub : (VG.Proof.MlKem.X86_64.keyGenK L).pub σ₁ σ₂) : VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ₁ = VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ₂ := pub.2.2.2.2.2

/-! ## `G` -/

theorem gRho_trL : RelCT isa (LRel VG.Proof.MlKem.X86_64.KeyGen.kgR (VG.Proof.MlKem.X86_64.KeyGen.kgW L)) (gRho L) fun _ _ => True := by
  unfold gRho
  refine RelCT.seq (LRel.step (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq (p := sc 0) (l := 1) W.inBs.1) W.nbT)
    fun x Lx => WP.mono (setB_okL Lx (by decide) (by have := W.k; omega) (p := sc oNB) (v := L.k) W.nb)
      fun _ h => ⟨_, h.1⟩) (RelCT.seq (LRel.step (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (hash_tr (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L)
        (ps := [((.rbp, 0), 32), (sc oNB, 1)]) (rate := 72) (out := sc oG) (len := 64) W.gH (show 6 < 256 by decide))
    fun x Lx => WP.mono (hash_ok (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (ps := [((.rbp, 0), 32), (sc oNB, 1)]) (rate := 72) (out := sc oG)
      (len := 64) W.gH (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq (p := sc 0) (l := 1) W.inBs.1) (by taint_decide)))

theorem gRho_tr : RelCT isa (Rel2 (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub fun σ s => VG.Proof.MlKem.X86_64.KeyGen.KC σ s ∧ s.gpr .r15 = 1) (gRho L)
    fun _ _ => True :=
  VG.Proof.MlKem.X86_64.rel2_of (VG.Proof.MlKem.X86_64.KeyGen.gRho_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlKem.X86_64.KeyGen.kc_lrel W p₁ p₂ pub h₁.1 h₂.1

/-! ## The matrix -/

theorem sample_tr {e : Nat} (he : e < L.k * L.k) (he' : 4 * (L.k * L.k / 4) ≤ e) :
    RelCT isa (Rel2 (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub (VG.Proof.MlKem.X86_64.KeyGen.KB L e)) (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k))
      fun _ _ => True := by
  have hc := W.kb e he he'
  simp only [VG.Proof.MlKem.X86_64.KeyGen.kbChk, Bool.and_eq_true] at hc
  have hk := W.k
  exact VG.Proof.MlKem.X86_64.rel2_of (sampleIJ_tr (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) rbx_na (by have := VG.Proof.MlKem.X86_64.div_lt_k he; omega) (by have := VG.Proof.MlKem.X86_64.mod_lt_k he; omega)
      hc.1.1.1.1.1 (W.ijT e he))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlKem.X86_64.KeyGen.kc_lrel W p₁ p₂ pub h₁.a.kc h₂.a.kc, by rw [h₁.a.sb, h₂.a.sb]; exact VG.Proof.MlKem.X86_64.KeyGen.rho_pub pub⟩

theorem quad_trK (v : Sample4Impl) {q : Nat} (hq : q < L.k * L.k / 4) :
    RelCT isa (Rel2 (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub (VG.Proof.MlKem.X86_64.KeyGen.KB L (4 * q)))
      (quad v.callee L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) fun _ _ => True := by
  have hc := W.kq q hq
  simp only [VG.Proof.MlKem.X86_64.KeyGen.kqChk, Bool.and_eq_true] at hc
  have hk := W.k
  have h16 : L.k * L.k ≤ 16 := Nat.mul_le_mul hk.2 hk.2
  exact VG.Proof.MlKem.X86_64.rel2_of (RelCT.exists_ fun ρ => VG.Proof.MlKem.X86_64.quad_tr (ρ := ρ) v (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (by omega)
      (fun t ht => ⟨by have := VG.Proof.MlKem.X86_64.div_lt_k (show 4 * q + t < L.k * L.k by omega); omega,
        by have := VG.Proof.MlKem.X86_64.mod_lt_k (show 4 * q + t < L.k * L.k by omega); omega⟩) hc.1.1.1.1.1)
    fun σ₁ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨KPke.kgRho L.p (VG.Proof.MlKem.X86_64.KeyGen.kgD σ₁), VG.Proof.MlKem.X86_64.KeyGen.kc_lrel W p₁ p₂ pub h₁.a.kc h₂.a.kc,
      ⟨h₁.a.sb, fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      ⟨h₂.a.sb.trans (VG.Proof.MlKem.X86_64.KeyGen.rho_pub pub).symm, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩

theorem samples_tr (v : Sample4Impl) : RelCT isa (Rel2 (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub (VG.Proof.MlKem.X86_64.KeyGen.KB L 0)) (L.samples v.callee)
    (Rel2 (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub (VG.Proof.MlKem.X86_64.KeyGen.KB L (L.k * L.k))) :=
  VG.Proof.MlKem.X86_64.samples_tr' L v.callee (R := fun e => Rel2 (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub (VG.Proof.MlKem.X86_64.KeyGen.KB L e))
    (fun _ he he' => relInv (fun _ _ hp hs => VG.Proof.MlKem.X86_64.KeyGen.sample_step W hp he he' hs) (VG.Proof.MlKem.X86_64.KeyGen.sample_tr W he he'))
    (fun _ hq => relInv (fun _ _ hp hs => VG.Proof.MlKem.X86_64.KeyGen.quad_step v W hp hq hs) (VG.Proof.MlKem.X86_64.KeyGen.quad_trK W v hq))

/-! ## `ŝ` and `ê` -/

theorem prfs_trK (v : Sample4Impl) :
    RelCT isa (Rel2 (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub (VG.Proof.MlKem.X86_64.KeyGen.KRest0 L)) (v.callee.prfs 0 (2 * L.k) L.oPR L.lPW)
      fun _ _ => True := by
  have hc := W.prfs
  simp only [VG.Proof.MlKem.X86_64.KeyGen.prfsKChk, Bool.and_eq_true] at hc
  exact VG.Proof.MlKem.X86_64.rel2_of (v.prfs_tr (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (by have := W.k; omega) hc.1.1.1.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    VG.Proof.MlKem.X86_64.KeyGen.kc_lrel W p₁ p₂ pub h₁.kc h₂.kc

theorem se_tr {A : Arith} (hA : ArithOk A) {N : Nat} (hN : N < 2 * L.k) :
    RelCT isa (Rel2 (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub (VG.Proof.MlKem.X86_64.KeyGen.KRest L N 0 0)) (se L A N) fun _ _ => True := by
  have hc := W.se N hN
  simp only [VG.Proof.MlKem.X86_64.KeyGen.seChk, Bool.and_eq_true] at hc
  obtain ⟨⟨htw, hic⟩, _⟩ := hc
  unfold se
  refine VG.Proof.MlKem.X86_64.rel2_of (Q := fun x y => LRel VG.Proof.MlKem.X86_64.KeyGen.kgR (VG.Proof.MlKem.X86_64.KeyGen.kgW L) x y ∧ True ∧ True)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS N))) (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L)
      (RelCT.mono (cbd2At_trL rbx_na htw) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx _ => WP.mono (cbd2At_okL Lx rbx_na htw) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩) (nttAt_tr hA hic))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlKem.X86_64.KeyGen.kc_lrel W p₁ p₂ pub h₁.kc h₂.kc, trivial, trivial⟩

/-! ## The rows of `ek` -/

theorem row_tr {A : Arith} (hA : ArithOk A) {i : Nat} (hi : i < L.k) :
    RelCT isa (Rel2 (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub (VG.Proof.MlKem.X86_64.KeyGen.KRest L (2 * L.k) i 0)) (row L A i) fun _ _ => True := by
  have hc := W.row i hi
  simp only [VG.Proof.MlKem.X86_64.KeyGen.rowChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hdc, hac⟩, hk3⟩, htw⟩, _⟩ := hc
  unfold row
  refine VG.Proof.MlKem.X86_64.rel2_of (Q := fun x y => LRel VG.Proof.MlKem.X86_64.KeyGen.kgR (VG.Proof.MlKem.X86_64.KeyGen.kgW L) x y ∧ (DotIn (fun j => L.aS i j) pS L.k x ∧
      Reduced x.mem (pa x (pS (L.k + i)))) ∧ (DotIn (fun j => L.aS i j) pS L.k y ∧
        Reduced y.mem (pa y (pS (L.k + i)))))
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS (L.k + i)))) (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L)
      (RelCT.mono (dotN_tr hA (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) W.k.1 (dotChk_spec hdc)) (fun _ _ ⟨e, h₁, h₂⟩ => ⟨e, h₁.1, h₂.1⟩)
        fun _ _ h => h)
      (fun x Lx hx => ?_)
      (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (addAt_tr rbx_na hac)
        (fun x Lx hx => WP.mono (addAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
          ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩) (enc12At_trL VG.Proof.MlKem.X86_64.KeyGen.r12_na htw)))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlKem.X86_64.KeyGen.kc_lrel W p₁ p₂ pub h₁.kc h₂.kc,
      ⟨fun k hk => ⟨(h₁.matIJ hi hk).1, (h₁.se k (by omega)).1⟩, (h₁.se (L.k + i) (by omega)).1⟩,
      ⟨fun k hk => ⟨(h₂.matIJ hi hk).1, (h₂.se k (by omega)).1⟩, (h₂.se (L.k + i) (by omega)).1⟩⟩
  -- The sum of products, from reduced inputs.
  refine WP.mono (dotN_ok hA (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) W.k.1 (dotChk_spec hdc) Lx (a := fun k => polyAt x.mem (pa x (L.aS i k)))
    (b := fun k => polyAt x.mem (pa x (pS k))) (fun k hk => ⟨(hx.1 k hk).1, rfl⟩) (fun k hk => ⟨(hx.1 k hk).2, rfl⟩))
    fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1, Lx.keepRed hP.b hk3 hx.2⟩

/-! ## The rows of `dk` -/

theorem encS_tr {j : Nat} (hj : j < L.k) :
    RelCT isa (Rel2 (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub (VG.Proof.MlKem.X86_64.KeyGen.KRest L (2 * L.k) L.k j)) (encS j) fun _ _ => True := by
  have hc := W.encS j hj
  simp only [VG.Proof.MlKem.X86_64.KeyGen.encSChk, Bool.and_eq_true] at hc
  exact VG.Proof.MlKem.X86_64.rel2_of (enc12At_trL VG.Proof.MlKem.X86_64.KeyGen.r13_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    ⟨VG.Proof.MlKem.X86_64.KeyGen.kc_lrel W p₁ p₂ pub h₁.kc h₂.kc, (h₁.se j (by omega)).1, (h₂.se j (by omega)).1⟩

/-! ## The rest of the keys -/

theorem fin_trL : RelCT isa (LRel VG.Proof.MlKem.X86_64.KeyGen.kgR (VG.Proof.MlKem.X86_64.KeyGen.kgW L)) (fin L) fun _ _ => True := by
  unfold fin
  have tr : ∀ {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T},
      (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13]) c h).isSome = true →
      RelCT isa (LRel VG.Proof.MlKem.X86_64.KeyGen.kgR (VG.Proof.MlKem.X86_64.KeyGen.kgW L)) c fun _ _ => True := fun ht => taintRel [.rbx, .rbp, .r12, .r13] (fun x y h =>
    fa4 (h.eq (p := sc 0) (l := 1) W.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) rfl)
      (h.eq (p := (.r12, 0)) (l := 1) W.inBs.2.1) (h.eq (p := (.r13, 0)) (l := 1) W.inBs.2.2)) ht
  obtain ⟨_, t₁⟩ := W.finT₁
  obtain ⟨_, t₂⟩ := W.finT₂
  obtain ⟨_, t₄⟩ := W.finT₄
  refine RelCT.seq (LRel.step (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (tr t₁) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r12, 384 * L.k)) (src := sc oG) (n := 32) (by decide) W.f₁)
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (tr t₂) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r13, 384 * L.k)) (src := (.r12, 0)) (n := L.ekLen) (by decide) W.f₂)
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (hash_tr (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (ps := [((.r12, 0), L.ekLen)]) (rate := 136)
      (out := (.r13, 384 * L.k + L.ekLen)) (len := 32) W.f₃ (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok (VG.Proof.MlKem.X86_64.KeyGen.kgB_bases L) (ps := [((.r12, 0), L.ekLen)]) (rate := 136) (out := (.r13, 384 * L.k + L.ekLen))
        (len := 32) W.f₃ (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (tr t₄)))

theorem fin_tr : RelCT isa (Rel2 (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub (VG.Proof.MlKem.X86_64.KeyGen.KRest L (2 * L.k) L.k L.k)) (fin L) fun _ _ => True :=
  VG.Proof.MlKem.X86_64.rel2_of (VG.Proof.MlKem.X86_64.KeyGen.fin_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlKem.X86_64.KeyGen.kc_lrel W p₁ p₂ pub h₁.kc h₂.kc

end KeyGen

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.KgTop`. -/
section

/-!
# ML-KEM on x86-64: key generation

The function, piece by piece (`KeyGen.*_ok`): it returns 1 with
`KeyGen_internal(d, z)` in `ek` and `dk` if every `SampleNTT` succeeded within
280 iterations (`allOk`), and 0 otherwise (`keyGen_correct`); it leaks only
the pointers and `ρ` (`keyGen_ct`). Each parameter set's file moves this to
its shared contract.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

/-- `KB` is kept by a piece that only sets flags. -/
theorem KB.flag {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {e : Nat} (he : e ≤ L.k * L.k)
    {s s' : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KB L e σ s) (hP : PPost s s' []) : VG.Proof.MlKem.X86_64.KeyGen.KB L e σ s' := by
  have L₀ := h.a.kc.lay W hp
  exact ⟨h.a.keep W hp hP.b W.flag W.flagG W.flagS W.flagB, by rw [hP.cs .r15 (by decide)]; exact h.m.r15,
    fun e' he' f hf => L₀.keepPoly hP.b (W.flagA e' (by omega)) (h.m.mat e' he' f hf)⟩

/-- At the end: `r15` as `allOk`, and the keys if it is 1. -/
structure KEnd (L : Kem) (σ s : State) : Prop where
  kc : VG.Proof.MlKem.X86_64.KeyGen.KC σ s
  r15 : s.gpr .r15 = if VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) (L.k * L.k) then 1 else 0
  keys : VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) (L.k * L.k) → VG.Proof.MlKem.X86_64.KeyGen.KFin L σ s

theorem r15_ne {k : Nat} {ρ : List Byte} {r : BitVec 64} (h : r = if VG.Proof.MlKem.X86_64.allOk k ρ (k * k) then 1 else 0)
    (hne : r.setWidth 32 ≠ 0) : VG.Proof.MlKem.X86_64.allOk k ρ (k * k) := by
  by_contra ho
  rw [ifn ho] at h
  exact hne (by rw [h]; rfl)

theorem r15_eq {k : Nat} {ρ : List Byte} {r : BitVec 64} (h : r = if VG.Proof.MlKem.X86_64.allOk k ρ (k * k) then 1 else 0)
    (he : r.setWidth 32 = 0) : ¬ VG.Proof.MlKem.X86_64.allOk k ρ (k * k) := by
  intro ho
  rw [ifp ho] at h
  rw [h] at he
  exact absurd he (by decide)

theorem rest_ok (v : Sample4Impl) {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {s : State}
    (h : VG.Proof.MlKem.X86_64.KeyGen.KRest0 L σ s) : WP isa (VG.Impl.MlKem.X86_64.KeyGen.rest L v.callee) s (VG.Proof.MlKem.X86_64.KeyGen.KFin L σ) := by
  unfold VG.Impl.MlKem.X86_64.KeyGen.rest
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.KeyGen.prfs_okK v W hp h) fun s₀ h₀ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => VG.Proof.MlKem.X86_64.KeyGen.KRest L k 0 0 σ) (2 * L.k) 0
    (fun k _ hk s hs => VG.Proof.MlKem.X86_64.KeyGen.se_ok v.arith W hp (by omega) hs) s₀ h₀) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => VG.Proof.MlKem.X86_64.KeyGen.KRest L (2 * L.k) k 0 σ) L.k 0
    (fun k _ hk s hs => VG.Proof.MlKem.X86_64.KeyGen.row_ok v.arith W hp (by omega) hs) s₁ (by rwa [Nat.zero_add] at h₁)) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => VG.Proof.MlKem.X86_64.KeyGen.KRest L (2 * L.k) L.k k σ) L.k 0
    (fun k _ hk s hs => VG.Proof.MlKem.X86_64.KeyGen.encS_ok W hp (by omega) hs) s₂ (by rwa [Nat.zero_add] at h₂)) fun s₃ h₃ => ?_)
  exact VG.Proof.MlKem.X86_64.KeyGen.fin_ok W hp (by rwa [Nat.zero_add] at h₃)

theorem body_ok (v : Sample4Impl) {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) {s : State}
    (h : VG.Proof.MlKem.X86_64.KeyGen.KB L (L.k * L.k) σ s) : WP isa (ifOk (VG.Impl.MlKem.X86_64.KeyGen.rest L v.callee)) s (VG.Proof.MlKem.X86_64.KeyGen.KEnd L σ) := by
  refine ifOk_ok (fun s₁ hP hne => ?_) fun s₁ hP he => ?_
  · have ho := VG.Proof.MlKem.X86_64.KeyGen.r15_ne h.m.r15 hne
    exact WP.mono (VG.Proof.MlKem.X86_64.KeyGen.rest_ok v W hp (KRest0.start (h.flag W hp (Nat.le_refl _) hP) ho)) fun s' hf =>
      ⟨hf.kc, by rw [hf.r15, ifp ho], fun _ => hf⟩
  · have ho := VG.Proof.MlKem.X86_64.KeyGen.r15_eq h.m.r15 he
    have h' := h.flag W hp (Nat.le_refl _) hP
    exact ⟨h'.a.kc, h'.m.r15, fun h => absurd h ho⟩

/-- The postcondition, from the keys. -/
theorem post_of {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ s : State} (h : VG.Proof.MlKem.X86_64.KeyGen.KEnd L σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : (VG.Proof.MlKem.X86_64.keyGenK L).post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rsi := by
    rw [pa, h.kc.top.regs (.r12, .rsi) (by decide), add_ofNat_zero]
  have e13 : pa s (.r13, 0) = σ.gpr .rdx := by
    rw [pa, h.kc.top.regs (.r13, .rdx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) (L.k * L.k)
  · have hf := h.keys ho
    refine .inl ⟨by rw [hr, hf.r15]; rfl, minIterations, ?_⟩
    show keyGenInternal L.p minIterations _ _ = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_some W.eta.1 (a := VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ))
      fun i hi j hj => VG.Proof.MlKem.X86_64.aHat_eq ho hi hj, Option.map_some, hm, ← e12, ← e13, hf.ek, hf.dk]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := VG.Proof.MlKem.X86_64.not_allOk ho
    show keyGenInternal L.p minIterations _ _ = _
    rw [KPke.keyGenInternal_eq, KPke.kpkeKeyGen_none hi hj hn]
    rfl

theorem KEnd.hin {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) {σ s : State} (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) (h : VG.Proof.MlKem.X86_64.KeyGen.KEnd L σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk =>
  (h.kc.lay W hp).cR (W.sv k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

end KeyGen

open KeyGen in
theorem kemKeyGen_correct (v : Sample4Impl) {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) (hctl : ctlOk (kemKeyGen L v.callee) = true)
    (σ : State) (hp : (VG.Proof.MlKem.X86_64.keyGenK L).pre σ) :
    ∃ t s', Exec isa (kemKeyGen L v.callee) σ t s' ∧ abiPreserved σ s' ∧ (VG.Proof.MlKem.X86_64.keyGenK L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlKem.X86_64.KeyGen.pro_ok W hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (VG.Proof.MlKem.X86_64.KeyGen.gRho_ok W hp h₁ h15) fun s₂ ⟨h₂, h15'⟩ =>
      WP.seq (WP.mono (VG.Proof.MlKem.X86_64.KeyGen.samples_ok v W hp (KB.zero h₂ h15')) fun s₃ h₃ =>
        WP.seq (WP.mono (VG.Proof.MlKem.X86_64.KeyGen.body_ok v W hp h₃) fun s₄ h₄ =>
          WP.mono (topEpi_ok h₄.kc.top (h₄.hin W hp)) fun s₅ ⟨hr, hg, hm⟩ =>
            (⟨hg, VG.Proof.MlKem.X86_64.KeyGen.post_of W h₄ hr hm⟩ : gprPreserved σ s₅ ∧ (VG.Proof.MlKem.X86_64.keyGenK L).post σ s₅)))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

/-! ## Constant time -/

/-- `relInv`, with a fact about the entry state carried along. -/
theorem relInvC {Pre : State → Prop} {Pub : State → State → Prop} {I I' : State → State → Prop} {C : State → Prop}
    {c : Prog isa} (hw : ∀ σ s, Pre σ → I σ s → WP isa c s (I' σ))
    (ht : RelCT isa (Rel2 Pre Pub I) c fun _ _ => True) :
    RelCT isa (Rel2 Pre Pub fun σ s => I σ s ∧ C σ) c (Rel2 Pre Pub fun σ s => I' σ s ∧ C σ) :=
  relInv (fun σ s hp hs => WP.mono (hw σ s hp hs.1) fun _ h => ⟨h, hs.2⟩)
    (RelCT.mono ht (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, i₁.1, i₂.1⟩) fun _ _ h => h)

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

variable {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L)
include W

abbrev R (L : Kem) (I : State → State → Prop) : State → State → Prop := Rel2 (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub I

theorem rest_tr (v : Sample4Impl) :
    RelCT isa (VG.Proof.MlKem.X86_64.KeyGen.R L fun σ s => VG.Proof.MlKem.X86_64.KeyGen.KRest0 L σ s ∧ VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) (L.k * L.k)) (VG.Impl.MlKem.X86_64.KeyGen.rest L v.callee)
      (VG.Proof.MlKem.X86_64.KeyGen.R L fun σ s => VG.Proof.MlKem.X86_64.KeyGen.KFin L σ s ∧ VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) (L.k * L.k)) := by
  unfold VG.Impl.MlKem.X86_64.KeyGen.rest
  refine RelCT.seq (VG.Proof.MlKem.X86_64.relInvC (fun σ s hp hs => VG.Proof.MlKem.X86_64.KeyGen.prfs_okK v W hp hs) (VG.Proof.MlKem.X86_64.KeyGen.prfs_trK W v)) ?_
  refine RelCT.seq (seqR_tr (R := fun k => VG.Proof.MlKem.X86_64.KeyGen.R L fun σ s => VG.Proof.MlKem.X86_64.KeyGen.KRest L k 0 0 σ s ∧ VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) (L.k * L.k))
    (2 * L.k) 0 fun k _ hk => VG.Proof.MlKem.X86_64.relInvC (fun σ s hp hs => VG.Proof.MlKem.X86_64.KeyGen.se_ok v.arith W hp (by omega) hs)
      (VG.Proof.MlKem.X86_64.KeyGen.se_tr W v.arith (by omega))) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k => VG.Proof.MlKem.X86_64.KeyGen.R L fun σ s => VG.Proof.MlKem.X86_64.KeyGen.KRest L (2 * L.k) k 0 σ s ∧ VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) (L.k * L.k))
    L.k 0 fun k _ hk => VG.Proof.MlKem.X86_64.relInvC (fun σ s hp hs => VG.Proof.MlKem.X86_64.KeyGen.row_ok v.arith W hp (by omega) hs) (VG.Proof.MlKem.X86_64.KeyGen.row_tr W v.arith (by omega))) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k => VG.Proof.MlKem.X86_64.KeyGen.R L fun σ s => VG.Proof.MlKem.X86_64.KeyGen.KRest L (2 * L.k) L.k k σ s ∧ VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ) (L.k * L.k))
    L.k 0 fun k _ hk => VG.Proof.MlKem.X86_64.relInvC (fun σ s hp hs => VG.Proof.MlKem.X86_64.KeyGen.encS_ok W hp (by omega) hs) (VG.Proof.MlKem.X86_64.KeyGen.encS_tr W (by omega))) ?_
  rw [Nat.zero_add]
  exact VG.Proof.MlKem.X86_64.relInvC (fun σ s hp hs => VG.Proof.MlKem.X86_64.KeyGen.fin_ok W hp hs) (VG.Proof.MlKem.X86_64.KeyGen.fin_tr W)

omit W in
theorem r15_pub {σ₁ σ₂ x y : State} (pub : (VG.Proof.MlKem.X86_64.keyGenK L).pub σ₁ σ₂) (h₁ : VG.Proof.MlKem.X86_64.KeyGen.KB L (L.k * L.k) σ₁ x)
    (h₂ : VG.Proof.MlKem.X86_64.KeyGen.KB L (L.k * L.k) σ₂ y) : x.gpr .r15 = y.gpr .r15 := by
  rw [h₁.m.r15, h₂.m.r15]; exact congrArg (fun ρ => if VG.Proof.MlKem.X86_64.allOk L.k ρ (L.k * L.k) then (1 : BitVec 64) else 0) (VG.Proof.MlKem.X86_64.KeyGen.rho_pub pub)

theorem body_tr (v : Sample4Impl) : RelCT isa (VG.Proof.MlKem.X86_64.KeyGen.R L (VG.Proof.MlKem.X86_64.KeyGen.KB L (L.k * L.k))) (ifOk (VG.Impl.MlKem.X86_64.KeyGen.rest L v.callee)) (VG.Proof.MlKem.X86_64.KeyGen.R L (VG.Proof.MlKem.X86_64.KeyGen.KEnd L)) := by
  refine ifOk_tr (fun x y ⟨_, _, _, _, pub, h₁, h₂⟩ => by rw [VG.Proof.MlKem.X86_64.KeyGen.r15_pub pub h₁ h₂]) ?_ ?_
  · refine RelCT.mono (VG.Proof.MlKem.X86_64.KeyGen.rest_tr W v) (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, hne⟩ => ?_)
      fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ =>
        ⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁.1.kc, by rw [h₁.1.r15, ifp h₁.2], fun _ => h₁.1⟩,
          ⟨h₂.1.kc, by rw [h₂.1.r15, ifp h₂.2], fun _ => h₂.1⟩⟩
    have o₁ := VG.Proof.MlKem.X86_64.KeyGen.r15_ne h₁.m.r15 hne
    have o₂ : VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ₂) (L.k * L.k) := by rw [← VG.Proof.MlKem.X86_64.KeyGen.rho_pub pub]; exact o₁
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨KRest0.start (h₁.flag W p₁ (Nat.le_refl _) hx) o₁, o₁⟩,
      ⟨KRest0.start (h₂.flag W p₂ (Nat.le_refl _) hy) o₂, o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hx, hy, he⟩
    have o₁ := VG.Proof.MlKem.X86_64.KeyGen.r15_eq h₁.m.r15 he
    have o₂ : ¬ VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.KeyGen.rhoK L σ₂) (L.k * L.k) := by rw [← VG.Proof.MlKem.X86_64.KeyGen.rho_pub pub]; exact o₁
    have k₁ := h₁.flag W p₁ (Nat.le_refl _) hx
    have k₂ := h₂.flag W p₂ (Nat.le_refl _) hy
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨k₁.a.kc, k₁.m.r15, fun h => absurd h o₁⟩, ⟨k₂.a.kc, k₂.m.r15, fun h => absurd h o₂⟩⟩

omit W in
theorem pro_tr : RelCT isa (VG.Proof.MlKem.X86_64.KeyGen.R L fun σ s => s = σ) (.block VG.Impl.MlKem.X86_64.KeyGen.pro) fun _ _ => True :=
  taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa4 pub.2.2.2.1 pub.1 pub.2.1 pub.2.2.1) (by taint_decide)

omit W in
theorem epi_tr : RelCT isa (VG.Proof.MlKem.X86_64.KeyGen.R L (VG.Proof.MlKem.X86_64.KeyGen.KEnd L)) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.kc.top.regs (.rbx, .rcx) (by decide), h₂.kc.top.regs (.rbx, .rcx) (by decide), pub.2.2.2.1])
    (by taint_decide)

end KeyGen

open KeyGen in
theorem kemKeyGen_ct (v : Sample4Impl) {L : Kem} (W : VG.Proof.MlKem.X86_64.KeyGen.KgWf L) :
    ConstantTime isa (VG.Proof.MlKem.X86_64.keyGenK L).pre (VG.Proof.MlKem.X86_64.keyGenK L).pub (kemKeyGen L v.callee) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemKeyGen
  refine RelCT.seq (relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.KeyGen.KC σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact VG.Proof.MlKem.X86_64.KeyGen.pro_ok W hp) VG.Proof.MlKem.X86_64.KeyGen.pro_tr) ?_
  refine RelCT.seq (relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.KeyGen.KA L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => VG.Proof.MlKem.X86_64.KeyGen.gRho_ok W hp hs.1 hs.2) (VG.Proof.MlKem.X86_64.KeyGen.gRho_tr W)) ?_
  refine RelCT.seq (RelCT.mono (VG.Proof.MlKem.X86_64.KeyGen.samples_tr W v)
    (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, KB.zero h₁.1 h₁.2, KB.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  exact RelCT.seq (VG.Proof.MlKem.X86_64.KeyGen.body_tr W v) (RelCT.mono VG.Proof.MlKem.X86_64.KeyGen.epi_tr (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.EncBase`. -/
section

/-!
# ML-KEM on x86-64: K-PKE.Encrypt, its context and the matrix

`encrypt L` runs in both encapsulation and decapsulation, in their layouts,
and keeps what each of them holds of its state (`Ctx`: a predicate `Out` kept
by the pieces whose writes pass `chk`). Its inputs (`EIn`): the encryption
key at `E`, the message at `M`, the randomness at `G + 32`. The matrix `Â`
from `ρ` (the last 32 bytes of the key), as in key generation (`mat_ok`), and
its constant time, for a given `ρ` (`mat_tr`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- What a top-level function holds of its state, in its layout. -/
structure Ctx (rbs wbs : List (Reg × Nat)) where
  Out : State → Prop
  chk : List (Ptr × Nat) → Bool
  bs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases
  lay : ∀ {s}, Out s → Lay rbs wbs s
  step : ∀ {s s' : State} {ws : List (Ptr × Nat)}, Out s → PPostB s s' ws → chk ws = true → Out s'

/-- Two runs in a layout, each satisfying `I`, each piece keeping the layout. -/
theorem RelCT.stepL {rbs wbs : List (Reg × Nat)} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {c : Prog isa}
    {I J : State → Prop} (htr : RelCT isa (fun x y => LRel rbs wbs x y ∧ I x ∧ I y) c fun _ _ => True)
    (hw : ∀ x, I x → WP isa c x fun x' => (∃ W, PostB x x' W) ∧ J x') :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ I x ∧ I y) c (fun x y => LRel rbs wbs x y ∧ J x ∧ J y) :=
  RelCT.postDep htr (F := fun x x' => (∃ W, PostB x x' W) ∧ J x') (fun x y h => ⟨hw x h.2.1, hw y h.2.2⟩)
    fun _ _ _ _ h ⟨⟨_, hx⟩, jx⟩ ⟨⟨_, hy⟩, jy⟩ => ⟨h.1.post hcs hx hy, jx, jy⟩

/-- The compression and decompression the parameter set `L` calls, verified
for widths `wc` and `wd` that include `d_u` and `d_v`. -/
structure KemCalls (L : Kem) (wc wd : List Nat) : Prop where
  ce : CEImpl L.ceN L.ce wc
  dd : DDImpl L.ddN L.dd wd
  du : L.du ∈ wc ∧ L.du ∈ wd
  dv : L.dv ∈ wc ∧ L.dv ∈ wd

namespace Enc

open VG.Impl.MlKem.X86_64.Encrypt

variable {rbs wbs : List (Reg × Nat)}

/-- `ρ` of the key. -/
abbrev rhoE (L : Kem) (ek : List Byte) : List Byte := ekRho L.p ek

/-- The inputs: `ek` at `E`, `m` at `M` and `r` at `G + 32`. -/
structure EIn (L : Kem) (C : VG.Proof.MlKem.X86_64.Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  out : C.Out s
  ek : bytesAt s.mem (pa s E) L.ekLen = ek
  m : bytesAt s.mem (pa s (sc oM)) 32 = m
  r : bytesAt s.mem (pa s sigP) 32 = r

/-- A piece writing `ws` keeps the inputs. -/
def inKeep (L : Kem) (bs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (ws : List (Ptr × Nat)) :
    Bool :=
  chk ws && keepB bs ws E L.ekLen && keepB bs ws (sc oM) 32 && keepB bs ws sigP 32

theorem EIn.keep {L : Kem} {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {s s' : State} (h : VG.Proof.MlKem.X86_64.Enc.EIn L C E ek m r s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : VG.Proof.MlKem.X86_64.Enc.inKeep L (rbs ++ wbs) C.chk E ws = true) :
    VG.Proof.MlKem.X86_64.Enc.EIn L C E ek m r s' := by
  simp only [VG.Proof.MlKem.X86_64.Enc.inKeep, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hc, k1⟩, k2⟩, k3⟩ := hc
  have L₀ := C.lay h.out
  exact ⟨C.step h.out hP hc, by rw [L₀.keepBytes hP k1]; exact h.ek, by rw [L₀.keepBytes hP k2]; exact h.m,
    by rw [L₀.keepBytes hP k3]; exact h.r⟩

theorem EIn.rho {L : Kem} {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {s : State} (h : VG.Proof.MlKem.X86_64.Enc.EIn L C E ek m r s) :
    bytesAt s.mem (pa s (E.1, E.2 + 384 * L.k)) 32 = VG.Proof.MlKem.X86_64.Enc.rhoE L ek := by
  rw [← h.ek]
  show _ = ((bytesAt s.mem (pa s E) (384 * L.k + 32)).drop (384 * L.k)).take 32
  rw [bytesAt_slice _ _ (show 384 * L.k + 32 ≤ 384 * L.k + 32 from Nat.le_refl _), pa, pa, off_add]

theorem r14_na : Reg.r14 ∉ argRegs := by decide
theorem r14_cs : Reg.r14 ∈ calleeSaved := by decide

/-! ## The matrix -/

/-- After the first `e` entries of `Â`. -/
structure EB (L : Kem) (C : VG.Proof.MlKem.X86_64.Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (e : Nat) (s : State) : Prop where
  i : VG.Proof.MlKem.X86_64.Enc.EIn L C E ek m r s
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = VG.Proof.MlKem.X86_64.Enc.rhoE L ek
  m : VG.Proof.MlKem.X86_64.MatB L (VG.Proof.MlKem.X86_64.Enc.rhoE L ek) e s

/-- The copy of `ρ`. -/
def matChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  copyChk bs wbs (sc oSB) (E.1, E.2 + 384 * L.k) 32 && decide (E.1 ≠ .rdi) && VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E [(sc oSB, 32)]

/-- Entry `e` of `Â`. -/
def sampEChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (e : Nat) : Bool :=
  ijChk bs wbs (pS (L.pA + e)) && VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E (KeyGen.ijW L e) && keepB bs (KeyGen.ijW L e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB bs (KeyGen.ijW L e) (pS (L.pA + e')) 1024

theorem sampE_step {L : Kem} {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {e : Nat} (hk : L.k ≤ 4)
    (he : e < L.k * L.k) (hc : VG.Proof.MlKem.X86_64.Enc.sampEChk L (rbs ++ wbs) wbs C.chk E e = true) {s : State} (h : VG.Proof.MlKem.X86_64.Enc.EB L C E ek m r e s) :
    WP isa (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) s fun s' =>
      PPostB s s' (KeyGen.ijW L e) ∧ VG.Proof.MlKem.X86_64.Enc.EB L C E ek m r (e + 1) s' := by
  simp only [VG.Proof.MlKem.X86_64.Enc.sampEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hij, hkc⟩, kB⟩, kA⟩ := hc
  have L₀ := C.lay h.i.out
  refine WP.mono (sampleIJ_ok L₀ C.bs rbx_na (by have := VG.Proof.MlKem.X86_64.div_lt_k he; omega) (by have := VG.Proof.MlKem.X86_64.mod_lt_k he; omega) hij)
    fun s' ⟨hP, h15, hres⟩ => ⟨hP, h.i.keep hP hkc, by rw [L₀.keepBytes hP kB]; exact h.sb,
      h.m.single h.sb L₀ hP kA h15 hres⟩

/-- Entries `e, …, e + 3` of `Â`. -/
def quadEChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (e : Nat) : Bool :=
  VG.Proof.MlKem.X86_64.quadChk bs wbs (oP (L.pA + e)) (oP L.pW) && VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E (KeyGen.qW L e) &&
    keepB bs (KeyGen.qW L e) (sc oSB) 32 && (List.range e).all fun e' => keepB bs (KeyGen.qW L e) (pS (L.pA + e')) 1024

theorem quadE_step (v : Sample4Impl) {L : Kem} {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {E : Ptr} {ek m r : List Byte} {e : Nat}
    (he : e + 4 ≤ 256) (hc : VG.Proof.MlKem.X86_64.Enc.quadEChk L (rbs ++ wbs) wbs C.chk E e = true) {s : State} (h : VG.Proof.MlKem.X86_64.Enc.EB L C E ek m r e s) :
    WP isa (quad v.callee L.k e (pS (L.pA + e)) (pS L.pW)) s fun s' =>
      PPostB s s' (KeyGen.qW L e) ∧ VG.Proof.MlKem.X86_64.Enc.EB L C E ek m r (e + 4) s' := by
  simp only [VG.Proof.MlKem.X86_64.Enc.quadEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨hq, hkc⟩, kB⟩, kA⟩ := hc
  have L₀ := C.lay h.i.out
  refine WP.mono (VG.Proof.MlKem.X86_64.quad_ok v L₀ C.bs he hq) fun s' ⟨hP, h15, hres⟩ =>
    ⟨hP, h.i.keep hP hkc, by rw [L₀.keepBytes hP kB]; exact h.sb, h.m.four h.sb L₀ hP kA h15 hres⟩

theorem mat_ok (v : Sample4Impl) {L : Kem} {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {E : Ptr} (hk : L.k ≤ 4)
    (hc₁ : VG.Proof.MlKem.X86_64.Enc.matChk L (rbs ++ wbs) wbs C.chk E = true)
    (hq : ∀ q < L.k * L.k / 4, VG.Proof.MlKem.X86_64.Enc.quadEChk L (rbs ++ wbs) wbs C.chk E (4 * q) = true)
    (hs : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → VG.Proof.MlKem.X86_64.Enc.sampEChk L (rbs ++ wbs) wbs C.chk E e = true)
    {ek m r : List Byte} {s : State} (h : VG.Proof.MlKem.X86_64.Enc.EIn L C E ek m r s) (h15 : s.gpr .r15 = 1) :
    WP isa (mat L v.callee E) s (VG.Proof.MlKem.X86_64.Enc.EB L C E ek m r (L.k * L.k)) := by
  simp only [VG.Proof.MlKem.X86_64.Enc.matChk, Bool.and_eq_true, decide_eq_true_eq] at hc₁
  have L₀ := C.lay h.out
  unfold mat
  refine WP.seq (WP.mono (copy_okL L₀ hc₁.1.2 hc₁.1.1) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have h₁ := h.keep hP₁.b hc₁.2
  refine VG.Proof.MlKem.X86_64.samples_ok' L v.callee (I := VG.Proof.MlKem.X86_64.Enc.EB L C E ek m r) (fun e he he' s hs' => WP.mono (VG.Proof.MlKem.X86_64.Enc.sampE_step hk he (hs e he he') hs')
    fun _ h => h.2) (fun q hq' s hs' => WP.mono (VG.Proof.MlKem.X86_64.Enc.quadE_step v (by
      have : L.k * L.k ≤ 16 := Nat.mul_le_mul hk hk
      omega) (hq q hq') hs') fun _ h => h.2)
    ⟨h₁, ?_, MatB.zero L _ (by rw [hP₁.cs .r15 (by decide), h15])⟩
  rw [show pa s₁ (sc oSB) = pa s (sc oSB) from hP₁.pa rbx_cs, hb₁]
  exact h.rho

/-! ## Constant time, for a given `ρ` -/

/-- The entries of `Â` sampled so far, for the `ρ` of `ek`. -/
abbrev EBρ (L : Kem) (C : VG.Proof.MlKem.X86_64.Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (e : Nat) (s : State) : Prop :=
  ∃ ek m r, VG.Proof.MlKem.X86_64.Enc.rhoE L ek = ρ ∧ VG.Proof.MlKem.X86_64.Enc.EB L C E ek m r e s

theorem sampE_tr {L : Kem} {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {E : Ptr} {ρ : List Byte} {e : Nat} (hk : L.k ≤ 4) (he : e < L.k * L.k)
    (hc : VG.Proof.MlKem.X86_64.Enc.sampEChk L (rbs ++ wbs) wbs C.chk E e = true)
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx])
      (.block (setB (sc (oSB + 32)) (e % L.k) ++ setB (sc (oSB + 33)) (e / L.k))) (.block [])).isSome = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ e x ∧ VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ e y)
      (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k))
      (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ (e + 1) x ∧ VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ (e + 1) y) := by
  have hc' := hc
  simp only [VG.Proof.MlKem.X86_64.Enc.sampEChk, Bool.and_eq_true] at hc'
  refine RelCT.stepL C.bs (RelCT.mono (sampleIJ_tr C.bs rbx_na (by have := VG.Proof.MlKem.X86_64.div_lt_k he; omega)
      (by have := VG.Proof.MlKem.X86_64.mod_lt_k he; omega) hc'.1.1.1 ht)
    (fun x y ⟨hl, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => ⟨hl, by rw [h₁.sb, h₂.sb, e₁, e₂]⟩) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (VG.Proof.MlKem.X86_64.Enc.sampE_step hk he hc hx) fun x' hx' => ⟨⟨_, hx'.1⟩, ek, m, r, eρ, hx'.2⟩

/-- The inputs, for the `ρ` of `ek`, with `r15 = 1`. -/
abbrev EIρ (L : Kem) (C : VG.Proof.MlKem.X86_64.Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, VG.Proof.MlKem.X86_64.Enc.rhoE L ek = ρ ∧ VG.Proof.MlKem.X86_64.Enc.EIn L C E ek m r s ∧ s.gpr .r15 = 1

theorem quadE_tr (v : Sample4Impl) {L : Kem} {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {E : Ptr} {ρ : List Byte} {e : Nat} (hk : L.k ≤ 4)
    (he : e + 4 ≤ L.k * L.k) (hc : VG.Proof.MlKem.X86_64.Enc.quadEChk L (rbs ++ wbs) wbs C.chk E e = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ e x ∧ VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ e y)
      (quad v.callee L.k e (pS (L.pA + e)) (pS L.pW))
      (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ (e + 4) x ∧ VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ (e + 4) y) := by
  have hc' := hc
  simp only [VG.Proof.MlKem.X86_64.Enc.quadEChk, Bool.and_eq_true] at hc'
  have h16 : L.k * L.k ≤ 16 := Nat.mul_le_mul hk hk
  refine RelCT.stepL C.bs (RelCT.mono (VG.Proof.MlKem.X86_64.quad_tr (ρ := ρ) v C.bs (by omega)
      (fun t ht => ⟨by have := VG.Proof.MlKem.X86_64.div_lt_k (show e + t < L.k * L.k by omega); omega,
        by have := VG.Proof.MlKem.X86_64.mod_lt_k (show e + t < L.k * L.k by omega); omega⟩) hc'.1.1.1)
    (fun x y ⟨hl, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => ⟨hl, ⟨by rw [h₁.sb, e₁], fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      ⟨by rw [h₂.sb, e₂], fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (VG.Proof.MlKem.X86_64.Enc.quadE_step v (by omega) hc hx) fun x' hx' =>
      ⟨⟨_, hx'.1⟩, ek, m, r, eρ, hx'.2⟩

theorem mat_tr (v : Sample4Impl) {L : Kem} {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {E : Ptr} (hk : L.k ≤ 4)
    (hc₁ : VG.Proof.MlKem.X86_64.Enc.matChk L (rbs ++ wbs) wbs C.chk E = true)
    (hq : ∀ q < L.k * L.k / 4, VG.Proof.MlKem.X86_64.Enc.quadEChk L (rbs ++ wbs) wbs C.chk E (4 * q) = true)
    (hs : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → VG.Proof.MlKem.X86_64.Enc.sampEChk L (rbs ++ wbs) wbs C.chk E e = true)
    (hij : ∀ e < L.k * L.k, (taint.check (X86_64.Taint.ofRegs [.rbx])
      (.block (setB (sc (oSB + 32)) (e % L.k) ++ setB (sc (oSB + 33)) (e / L.k))) (.block [])).isSome = true)
    {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, E.1]) (copy (sc oSB) (E.1, E.2 + 384 * L.k) 32) h).isSome = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.EIρ L C E ρ x ∧ VG.Proof.MlKem.X86_64.Enc.EIρ L C E ρ y) (mat L v.callee E)
      (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ (L.k * L.k) x ∧ VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ (L.k * L.k) y) := by
  have hc₁' := hc₁
  simp only [VG.Proof.MlKem.X86_64.Enc.matChk, copyChk, wrOk, rdOk, Bool.and_eq_true] at hc₁'
  have hin₁ : inB (rbs ++ wbs) (sc oSB) 32 = true := hc₁'.1.1.1.1.1.1.1.2
  have hin₂ : inB (rbs ++ wbs) (E.1, E.2 + 384 * L.k) 32 = true := hc₁'.1.1.1.1.1.2.2
  unfold mat
  refine RelCT.seq (RelCT.stepL (J := VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ 0) C.bs (taintRel [.rbx, E.1] (fun x y h =>
      fa2 (h.1.eq hin₁) (h.1.eq (p := (E.1, E.2 + 384 * L.k)) hin₂)) ht) fun x ⟨ek, m, r, eρ, hx, h15⟩ => ?_)
    (VG.Proof.MlKem.X86_64.samples_tr' L v.callee (R := fun e x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ e x ∧ VG.Proof.MlKem.X86_64.Enc.EBρ L C E ρ e y)
      (fun e he he' => VG.Proof.MlKem.X86_64.Enc.sampE_tr hk he (hs e he he') (hij e he))
      (fun q hq' => VG.Proof.MlKem.X86_64.Enc.quadE_tr v hk (by omega) (hq q hq')))
  simp only [VG.Proof.MlKem.X86_64.Enc.matChk, Bool.and_eq_true, decide_eq_true_eq] at hc₁
  have L₀ := C.lay hx.out
  refine WP.mono (copy_okL L₀ hc₁.1.2 hc₁.1.1) fun x₁ ⟨hP₁, hb₁⟩ => ⟨⟨_, hP₁.b⟩, ek, m, r, eρ, ?_⟩
  refine ⟨hx.keep hP₁.b hc₁.2, ?_, MatB.zero L _ (by rw [hP₁.cs .r15 (by decide), h15])⟩
  rw [show pa x₁ (sc oSB) = pa x (sc oSB) from hP₁.pa rbx_cs, hb₁]
  exact hx.rho

end Enc

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.EncRest`. -/
section

/-!
# ML-KEM on x86-64: K-PKE.Encrypt, the ciphertext

When every entry of `Â` was sampled: `ŷ` (`y_ok`), `u` to the ciphertext
(`u_ok`), `t̂` (`t_ok`) and `v` to the ciphertext (`v_ok`). Between the steps,
`ER ny nu nt`: the first `ny` of `ŷ`, `nu` of `u` and `nt` of `t̂` are done.
Each with its constant time, for a given `ρ`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Enc

open VG.Impl.MlKem.X86_64.Encrypt

variable {rbs wbs : List (Reg × Nat)} {E : Ptr} {L : Kem}

/-- The steps done after the matrix. -/
structure ER (L : Kem) (C : VG.Proof.MlKem.X86_64.Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (ny nu nt : Nat) (s : State) : Prop where
  ok : VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.Enc.rhoE L ek) (L.k * L.k)
  i : VG.Proof.MlKem.X86_64.Enc.EIn L C E ek m r s
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.Enc.rhoE L ek) (e / L.k) (e % L.k))
  prf : ∀ N < 2 * L.k + 1, bytesAt s.mem (pa s (VG.Impl.MlKem.X86_64.Encrypt.prfO L N)) 128 = prf 2 r (BitVec.ofNat 8 N)
  y : ∀ k < ny, PolyIs s.mem (pa s (pS k)) (encY r k)
  u : ∀ i < nu, bytesAt s.mem (pa s (sc (L.oCT + 32 * L.du * i))) (32 * L.du) =
    compressEncode L.du (KPke.encU L.p (VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.Enc.rhoE L ek)) r i)
  t : ∀ i < nt, PolyIs s.mem (pa s (pS (L.k + i))) (ekT ek i)

/-- A piece that writes `ws` keeps `ER ny nu nt`. -/
def erChk (L : Kem) (bs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (ny nu nt : Nat)
    (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E ws && (List.range (L.k * L.k)).all (fun e => keepB bs ws (pS (L.pA + e)) 1024) &&
    (List.range (2 * L.k + 1)).all (fun N => keepB bs ws (VG.Impl.MlKem.X86_64.Encrypt.prfO L N) 128) &&
    (List.range ny).all (fun k => keepB bs ws (pS k) 1024) &&
    (List.range nu).all (fun i => keepB bs ws (sc (L.oCT + 32 * L.du * i)) (32 * L.du)) &&
    (List.range nt).all (fun i => keepB bs ws (pS (L.k + i)) 1024)

theorem ER.keep {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {ek m r : List Byte} {ny nu nt : Nat} {s s' : State}
    (h : VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r ny nu nt s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws)
    (hc : VG.Proof.MlKem.X86_64.Enc.erChk L (rbs ++ wbs) C.chk E ny nu nt ws = true) : VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r ny nu nt s' := by
  simp only [VG.Proof.MlKem.X86_64.Enc.erChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hin, kA⟩, kR⟩, kY⟩, kU⟩, kT⟩ := hc
  have L₀ := C.lay h.i.out
  exact ⟨h.ok, h.i.keep hP.b hin, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he),
    fun N hN => by rw [L₀.keepBytes hP.b (kR N hN)]; exact h.prf N hN, fun k hk => L₀.keepPoly hP.b (kY k hk) (h.y k hk),
    fun i hi => by rw [L₀.keepBytes hP.b (kU i hi)]; exact h.u i hi, fun i hi => L₀.keepPoly hP.b (kT i hi) (h.t i hi)⟩

/-- `Â[i, j]`, from the entries. -/
theorem ER.matIJ {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {ek m r : List Byte} {ny nu nt : Nat} {s : State}
    (h : VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r ny nu nt s) {i j : Nat} (hi : i < L.k) (hj : j < L.k) :
    PolyIs s.mem (pa s (L.aS i j)) (VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.Enc.rhoE L ek) i j) := by
  have := h.mat (L.k * i + j) (VG.Proof.MlKem.X86_64.ij_lt hi hj)
  rwa [(VG.Proof.MlKem.X86_64.divmod_ij hj).1, (VG.Proof.MlKem.X86_64.divmod_ij hj).2, ← VG.Proof.MlKem.X86_64.aS_ij] at this

theorem EB.flag {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {ek m r : List Byte} {s s' : State} (h : VG.Proof.MlKem.X86_64.Enc.EB L C E ek m r (L.k * L.k) s)
    (hP : PPost s s' []) (hc : VG.Proof.MlKem.X86_64.Enc.inKeep L (rbs ++ wbs) C.chk E [] = true)
    (hk : ∀ e < L.k * L.k, keepB (rbs ++ wbs) [] (pS (L.pA + e)) 1024 = true)
    (hsb : keepB (rbs ++ wbs) [] (sc oSB) 32 = true) : VG.Proof.MlKem.X86_64.Enc.EB L C E ek m r (L.k * L.k) s' := by
  have L₀ := C.lay h.i.out
  exact ⟨h.i.keep hP.b hc, by rw [L₀.keepBytes hP.b hsb]; exact h.sb, by rw [hP.cs .r15 (by decide)]; exact h.m.r15,
    fun e he f hf => L₀.keepPoly hP.b (hk e he) (h.m.mat e he f hf)⟩

/-- After the matrix, when every `SampleNTT` succeeded. -/
structure ER0 (L : Kem) (C : VG.Proof.MlKem.X86_64.Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  ok : VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.Enc.rhoE L ek) (L.k * L.k)
  i : VG.Proof.MlKem.X86_64.Enc.EIn L C E ek m r s
  r15 : s.gpr .r15 = 1
  mat : ∀ e < L.k * L.k, PolyIs s.mem (pa s (pS (L.pA + e))) (VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.Enc.rhoE L ek) (e / L.k) (e % L.k))

theorem ER0.start {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {ek m r : List Byte} {s : State} (h : VG.Proof.MlKem.X86_64.Enc.EB L C E ek m r (L.k * L.k) s)
    (ho : VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.Enc.rhoE L ek) (L.k * L.k)) : VG.Proof.MlKem.X86_64.Enc.ER0 L C E ek m r s :=
  ⟨ho, h.i, by rw [h.m.r15, ifp ho], fun e he => h.m.mat e he _ (VG.Proof.MlKem.X86_64.aHat_eq ho (VG.Proof.MlKem.X86_64.div_lt_k he) (VG.Proof.MlKem.X86_64.mod_lt_k he))⟩

/-- The steps, for the `ρ` of `ek`. -/
abbrev ERρ (L : Kem) (C : VG.Proof.MlKem.X86_64.Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (ny nu nt : Nat) (s : State) : Prop :=
  ∃ ek m r, VG.Proof.MlKem.X86_64.Enc.rhoE L ek = ρ ∧ VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r ny nu nt s

/-! ## The outputs of `PRF₂` -/

def prfsEChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  prfsChk bs wbs (2 * L.k + 1) L.oPR L.lPW && VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E (prfsW (2 * L.k + 1) L.oPR L.lPW) &&
    (List.range (L.k * L.k)).all (fun e => keepB bs (prfsW (2 * L.k + 1) L.oPR L.lPW) (pS (L.pA + e)) 1024)

theorem prfsE_ok (v : Sample4Impl) {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} (hk : L.k ≤ 4) (hc : VG.Proof.MlKem.X86_64.Enc.prfsEChk L (rbs ++ wbs) wbs C.chk E = true)
    {ek m r : List Byte} {s : State} (h : VG.Proof.MlKem.X86_64.Enc.ER0 L C E ek m r s) :
    WP isa (v.callee.prfs 0 (2 * L.k + 1) L.oPR L.lPW) s fun s' =>
      PPost s s' (prfsW (2 * L.k + 1) L.oPR L.lPW) ∧ VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r 0 0 0 s' := by
  simp only [VG.Proof.MlKem.X86_64.Enc.prfsEChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hpc, hin⟩, kA⟩ := hc
  have L₀ := C.lay h.i.out
  refine WP.mono (v.prfs_ok L₀ C.bs (by omega) hpc) fun s' ⟨hP, hb⟩ => ⟨hP, h.ok, h.i.keep hP.b hin,
    by rw [hP.cs .r15 (by decide)]; exact h.r15, fun e he => L₀.keepPoly hP.b (kA e he) (h.mat e he), fun N hN => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rw [VG.Impl.MlKem.X86_64.Encrypt.prfO, hP.pa rbx_cs, hb N hN, h.i.r, Nat.zero_add]

/-- After the matrix, for the `ρ` of `ek`. -/
abbrev ER0ρ (L : Kem) (C : VG.Proof.MlKem.X86_64.Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, VG.Proof.MlKem.X86_64.Enc.rhoE L ek = ρ ∧ VG.Proof.MlKem.X86_64.Enc.ER0 L C E ek m r s

theorem prfsE_tr (v : Sample4Impl) {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} (hk : L.k ≤ 4) (hc : VG.Proof.MlKem.X86_64.Enc.prfsEChk L (rbs ++ wbs) wbs C.chk E = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ER0ρ L C E ρ x ∧ VG.Proof.MlKem.X86_64.Enc.ER0ρ L C E ρ y) (v.callee.prfs 0 (2 * L.k + 1) L.oPR L.lPW)
      (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ 0 0 0 x ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ 0 0 0 y) := by
  have hc' := hc
  simp only [VG.Proof.MlKem.X86_64.Enc.prfsEChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (v.prfs_tr C.bs (by omega) hc'.1.1) (fun _ _ h => h.1) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (VG.Proof.MlKem.X86_64.Enc.prfsE_ok v hk hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## `ŷ` -/

def yChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (N : Nat) : Bool :=
  twoChk bs wbs (VG.Impl.MlKem.X86_64.Encrypt.prfO L N) 128 (pS N) 1024 && ipChk bs wbs (pS N) && VG.Proof.MlKem.X86_64.Enc.erChk L bs chk E N 0 0 (KeyGen.seW N)

theorem y_ok {A : Arith} (hA : ArithOk A) {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {N : Nat} (hN : N < L.k)
    (hc : VG.Proof.MlKem.X86_64.Enc.yChk L (rbs ++ wbs) wbs C.chk E N = true) {ek m r : List Byte} {s : State} (h : VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r N 0 0 s) :
    WP isa (y L A N) s fun s' => PPost s s' (KeyGen.seW N) ∧ VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r (N + 1) 0 0 s' := by
  simp only [VG.Proof.MlKem.X86_64.Enc.yChk, Bool.and_eq_true] at hc
  obtain ⟨⟨htw, hic⟩, hrc⟩ := hc
  have L₀ := C.lay h.i.out
  unfold y
  refine WP.seq (WP.mono (cbd2At_okL L₀ rbx_na htw) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L₀.post hP₁.b C.bs
  rw [h.prf N (by omega), ← hP₁.pa rbx_cs] at hp₁
  refine WP.mono (nttAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_
  have hP := PPost.app hP₁ hP₂ (by simp [calleeSaved])
  have hk := h.keep hP hrc
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : k < N ∨ k = N) with hk' | rfl
  · exact hk.y k hk'
  · rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂; exact hp₂

theorem y_tr {A : Arith} (hA : ArithOk A) {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {N : Nat} (hN : N < L.k)
    (hc : VG.Proof.MlKem.X86_64.Enc.yChk L (rbs ++ wbs) wbs C.chk E N = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ N 0 0 x ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ N 0 0 y) (y L A N)
      (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ (N + 1) 0 0 x ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ (N + 1) 0 0 y) := by
  have hc' := hc
  simp only [VG.Proof.MlKem.X86_64.Enc.yChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨htw, hic⟩, _⟩ := hc'
  refine RelCT.stepL C.bs ?_ fun x ⟨ek, m, r, eρ, hx⟩ =>
    WP.mono (VG.Proof.MlKem.X86_64.Enc.y_ok hA hN hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩
  unfold y
  exact RelCT.mono (RelCT.seqL (I := fun _ => True) (J := fun x => Reduced x.mem (pa x (pS N))) C.bs
    (RelCT.mono (cbd2At_trL rbx_na htw) (fun _ _ h => h.1) fun _ _ h => h)
    (fun x Lx _ => WP.mono (cbd2At_okL Lx rbx_na htw) fun x' ⟨hP, hq⟩ =>
      ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩) (nttAt_tr hA hic)) (fun _ _ h => ⟨h.1, trivial, trivial⟩)
    fun _ _ h => h

/-! ## `u` -/

/-- What `SamplePolyCBD₂(PRF₂(r, N))` to polynomial 16 writes. -/
abbrev prfW16 : List (Ptr × Nat) := [(pS 16, 1024)]

abbrev uW (L : Kem) (i : Nat) : List (Ptr × Nat) :=
  dotW L.k ++ [(pS 15, 1024), (sc oSS, 1024)] ++ VG.Proof.MlKem.X86_64.Enc.prfW16 ++ [(pS 15, 1024)] ++
    [(sc (L.oCT + 32 * L.du * i), 32 * L.du)]

def uChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (i : Nat) : Bool :=
  dotChk bs wbs (fun j => L.aS j i) pS L.k && ipChk bs wbs (pS 15) &&
    twoChk bs wbs (VG.Impl.MlKem.X86_64.Encrypt.prfO L (L.k + i)) 128 (pS 16) 1024 && keepB bs VG.Proof.MlKem.X86_64.Enc.prfW16 (pS 15) 1024 && accChk bs wbs (pS 15) (pS 16) &&
    twoChk bs wbs (pS 15) 1024 (sc (L.oCT + 32 * L.du * i)) (32 * L.du) && VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E (dotW L.k) &&
    VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E [(pS 15, 1024), (sc oSS, 1024)] && VG.Proof.MlKem.X86_64.Enc.erChk L bs chk E L.k i 0 (VG.Proof.MlKem.X86_64.Enc.uW L i) &&
    keepB bs (dotW L.k) (VG.Impl.MlKem.X86_64.Encrypt.prfO L (L.k + i)) 128 && keepB bs [(pS 15, 1024), (sc oSS, 1024)] (VG.Impl.MlKem.X86_64.Encrypt.prfO L (L.k + i)) 128

theorem u_ok {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) (hk0 : 0 < L.k) {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs}
    {i : Nat} (hi : i < L.k) (hc : VG.Proof.MlKem.X86_64.Enc.uChk L (rbs ++ wbs) wbs C.chk E i = true) {ek m r : List Byte} {s : State}
    (h : VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r L.k i 0 s) :
    WP isa (u L A i) s fun s' => PPost s s' (VG.Proof.MlKem.X86_64.Enc.uW L i) ∧ VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r L.k (i + 1) 0 s' := by
  simp only [VG.Proof.MlKem.X86_64.Enc.uChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hpc⟩, hk15⟩, hac⟩, htw⟩, hi₁⟩, hi₂⟩, hrc⟩, kp₁⟩, kp₂⟩ := hc
  have L₀ := C.lay h.i.out
  unfold u
  refine WP.seq (WP.mono (dotN_ok hA C.bs hk0 (dotChk_spec hdc) L₀ (a := fun j => VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.Enc.rhoE L ek) j i) (b := encY r)
    (fun k hk => h.matIJ hk hi) (fun k hk => h.y k hk)) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have e₁ := h.i.keep hP₁.b hi₁
  have L₁ := C.lay e₁.out
  rw [← hP₁.pa rbx_cs] at hp₁
  refine WP.seq (WP.mono (nttInvAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have e₂ := e₁.keep hP₂.b hi₂
  have L₂ := C.lay e₂.out
  rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.seq (WP.mono (cbd2At_okL L₂ rbx_na hpc) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have L₃ := L₂.post hP₃.b C.bs
  rw [L₁.keepBytes hP₂.b kp₂, L₀.keepBytes hP₁.b kp₁, h.prf (L.k + i) (by omega), ← hP₃.pa rbx_cs] at hp₃
  have hq₃ := L₂.keepPoly hP₃.b hk15 hp₂
  refine WP.seq (WP.mono (addAt_ok L₃ rbx_na hac hq₃.1 hp₃.1) fun s₄ ⟨hP₄, hp₄⟩ => ?_)
  have L₄ := L₃.post hP₄.b C.bs
  rw [hq₃.2, hp₃.2, ← hP₄.pa rbx_cs] at hp₄
  refine WP.mono (ceCall_okL K.ce L₄ rbx_na htw K.du.1 hp₄.1) fun s₅ ⟨hP₅, hb₅⟩ => ?_
  have hP := PPost.app (PPost.app (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide)) hP₄ (by decide)) hP₅
    (by simp [calleeSaved])
  have hk := h.keep hP hrc
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, hk.y, fun i' hi' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk.u i' hi'
  · rw [hP₅.pa rbx_cs, hb₅, hp₄.2]; rfl

theorem u_tr {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) (hk0 : 0 < L.k) {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs}
    {i : Nat} (hi : i < L.k) (hc : VG.Proof.MlKem.X86_64.Enc.uChk L (rbs ++ wbs) wbs C.chk E i = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k i 0 x ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k i 0 y) (u L A i)
      (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k (i + 1) 0 x ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k (i + 1) 0 y) := by
  have hc' := hc
  simp only [VG.Proof.MlKem.X86_64.Enc.uChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hpc⟩, hk15⟩, hac⟩, htw⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc'
  refine RelCT.stepL C.bs ?_ fun x ⟨ek, m, r, eρ, hx⟩ =>
    WP.mono (VG.Proof.MlKem.X86_64.Enc.u_ok hA K hk0 hi hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩
  unfold u
  refine RelCT.mono (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs
    (RelCT.mono (dotN_tr hA C.bs hk0 (dotChk_spec hdc)) (fun _ _ h => h) fun _ _ h => h)
    (fun x Lx hx => WP.mono (dotN_ok hA C.bs hk0 (dotChk_spec hdc) Lx (a := fun k => polyAt x.mem (pa x (L.aS k i)))
      (b := fun k => polyAt x.mem (pa x (pS k))) (fun k hk => ⟨(hx k hk).1, rfl⟩) (fun k hk => ⟨(hx k hk).2, rfl⟩))
      fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs (nttInvAt_tr hA hic)
      (fun x Lx hx => WP.mono (nttInvAt_ok hA Lx hic hx) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS 16))) C.bs
      (RelCT.mono (cbd2At_trL rbx_na hpc) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (cbd2At_okL Lx rbx_na hpc) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hk15 hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs (addAt_tr rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceCall_trL K.ce rbx_na htw K.du.1))))) (fun x y ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ =>
        ⟨hl, fun k hk => ⟨(h₁.matIJ hk hi).1, (h₁.y k hk).1⟩, fun k hk => ⟨(h₂.matIJ hk hi).1, (h₂.y k hk).1⟩⟩)
    fun _ _ h => h

/-! ## `t̂` -/

def tChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) (i : Nat) : Bool :=
  twoChk bs wbs (E.1, E.2 + 384 * i) 384 (pS (L.k + i)) 1024 && VG.Proof.MlKem.X86_64.Enc.erChk L bs chk E L.k L.k i [(pS (L.k + i), 1024)]

theorem t_ok {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {i : Nat} (hi : i < L.k) (hc : VG.Proof.MlKem.X86_64.Enc.tChk L (rbs ++ wbs) wbs C.chk E i = true)
    {ek m r : List Byte} {s : State} (h : VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r L.k L.k i s) :
    WP isa (t L E i) s fun s' => PPost s s' [(pS (L.k + i), 1024)] ∧ VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r L.k L.k (i + 1) s' := by
  simp only [VG.Proof.MlKem.X86_64.Enc.tChk, Bool.and_eq_true] at hc
  have L₀ := C.lay h.i.out
  refine WP.mono (dec12At_okL L₀ rbx_na hc.1) fun s' ⟨hP, hp⟩ => ?_
  have hk := h.keep hP hc.2
  refine ⟨hP, hk.ok, hk.i, hk.r15, hk.mat, hk.prf, hk.y, hk.u, fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk.t i' hi'
  · rw [hP.pa rbx_cs]
    have e : bytesAt s.mem (pa s (E.1, E.2 + 384 * i')) 384 = (ek.drop (384 * i')).take 384 := by
      rw [← h.i.ek]
      show _ = ((bytesAt s.mem (pa s E) (384 * L.k + 32)).drop (384 * i')).take 384
      rw [bytesAt_slice _ _ (show 384 * i' + 384 ≤ 384 * L.k + 32 by omega), pa, pa, off_add]
    rw [e] at hp
    exact hp

theorem t_tr {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} {i : Nat} (hi : i < L.k) (hc : VG.Proof.MlKem.X86_64.Enc.tChk L (rbs ++ wbs) wbs C.chk E i = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k L.k i x ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k L.k i y) (t L E i)
      (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k L.k (i + 1) x ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k L.k (i + 1) y) := by
  have hc' := hc
  simp only [VG.Proof.MlKem.X86_64.Enc.tChk, Bool.and_eq_true] at hc'
  exact RelCT.stepL C.bs (RelCT.mono (dec12At_trL rbx_na hc'.1) (fun _ _ h => h.1) fun _ _ h => h)
    fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (VG.Proof.MlKem.X86_64.Enc.t_ok hi hc hx) fun _ h => ⟨⟨_, h.1.b⟩, ek, m, r, eρ, h.2⟩

/-! ## `v` -/

abbrev vW (L : Kem) : List (Ptr × Nat) := dotW L.k ++ [(pS 15, 1024), (sc oSS, 1024)] ++ VG.Proof.MlKem.X86_64.Enc.prfW16 ++ [(pS 15, 1024)] ++
  [(pS 16, 1024)] ++ [(pS 15, 1024)] ++ [(sc (L.oCT + 32 * L.du * L.k), 32 * L.dv)]

def vChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  dotChk bs wbs (fun j => pS (L.k + j)) pS L.k && ipChk bs wbs (pS 15) &&
    twoChk bs wbs (VG.Impl.MlKem.X86_64.Encrypt.prfO L (2 * L.k)) 128 (pS 16) 1024 && keepB bs VG.Proof.MlKem.X86_64.Enc.prfW16 (pS 15) 1024 && accChk bs wbs (pS 15) (pS 16) &&
    twoChk bs wbs (sc oM) 32 (pS 16) 1024 && keepB bs [(pS 16, 1024)] (pS 15) 1024 &&
    twoChk bs wbs (pS 15) 1024 (sc (L.oCT + 32 * L.du * L.k)) (32 * L.dv) && VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E (dotW L.k) &&
    VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E [(pS 15, 1024), (sc oSS, 1024)] && VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E VG.Proof.MlKem.X86_64.Enc.prfW16 && VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E [(pS 15, 1024)] &&
    VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E [(pS 16, 1024)] && VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E [(sc (L.oCT + 32 * L.du * L.k), 32 * L.dv)] &&
    (List.range L.k).all (fun i => keepB bs (VG.Proof.MlKem.X86_64.Enc.vW L) (sc (L.oCT + 32 * L.du * i)) (32 * L.du)) &&
    keepB bs (dotW L.k) (VG.Impl.MlKem.X86_64.Encrypt.prfO L (2 * L.k)) 128 && keepB bs [(pS 15, 1024), (sc oSS, 1024)] (VG.Impl.MlKem.X86_64.Encrypt.prfO L (2 * L.k)) 128

theorem v_ok {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) (hk0 : 0 < L.k) {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs}
    (hc : VG.Proof.MlKem.X86_64.Enc.vChk L (rbs ++ wbs) wbs C.chk E = true) {ek m r : List Byte} {s : State} (h : VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r L.k L.k L.k s) :
    WP isa (v L A) s fun s' => PPost s s' (VG.Proof.MlKem.X86_64.Enc.vW L) ∧ C.Out s' ∧ s'.gpr .r15 = 1 ∧
      bytesAt s'.mem (pa s' (sc L.oCT)) L.ctLen = KPke.ct L.p (VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.Enc.rhoE L ek)) ek m r := by
  simp only [VG.Proof.MlKem.X86_64.Enc.vChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hpc⟩, hk15⟩, hac⟩, hdd⟩, hk16⟩, htw⟩, i₁⟩, i₂⟩, i₃⟩, i₄⟩, i₅⟩, i₇⟩, hu⟩, kp₁⟩,
    kp₂⟩ := hc
  have L₀ := C.lay h.i.out
  unfold v
  refine WP.seq (WP.mono (dotN_ok hA C.bs hk0 (dotChk_spec hdc) L₀ (a := ekT ek) (b := encY r) (fun k hk => h.t k hk)
    (fun k hk => h.y k hk)) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have e₁ := h.i.keep hP₁.b i₁
  have L₁ := C.lay e₁.out
  rw [← hP₁.pa rbx_cs] at hp₁
  refine WP.seq (WP.mono (nttInvAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have e₂ := e₁.keep hP₂.b i₂
  have L₂ := C.lay e₂.out
  rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.seq (WP.mono (cbd2At_okL L₂ rbx_na hpc) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have e₃ := e₂.keep hP₃.b i₃
  have L₃ := C.lay e₃.out
  rw [L₁.keepBytes hP₂.b kp₂, L₀.keepBytes hP₁.b kp₁, h.prf (2 * L.k) (by omega), ← hP₃.pa rbx_cs] at hp₃
  have hq₃ := L₂.keepPoly hP₃.b hk15 hp₂
  refine WP.seq (WP.mono (addAt_ok L₃ rbx_na hac hq₃.1 hp₃.1) fun s₄ ⟨hP₄, hp₄⟩ => ?_)
  have e₄ := e₃.keep hP₄.b i₄
  have L₄ := C.lay e₄.out
  rw [hq₃.2, hp₃.2, ← hP₄.pa rbx_cs] at hp₄
  refine WP.seq (WP.mono (ddCall_okL ddImpl L₄ (d := 1) rbx_na hdd (by decide)) fun s₅ ⟨hP₅, hp₅⟩ => ?_)
  have e₅ := e₄.keep hP₅.b i₅
  have L₅ := C.lay e₅.out
  rw [e₄.m, ← hP₅.pa rbx_cs] at hp₅
  have hq₅ := L₄.keepPoly hP₅.b hk16 hp₄
  refine WP.seq (WP.mono (addAt_ok L₅ rbx_na hac hq₅.1 hp₅.1) fun s₆ ⟨hP₆, hp₆⟩ => ?_)
  have e₆ := e₅.keep hP₆.b i₄
  have L₆ := C.lay e₆.out
  rw [hq₅.2, hp₅.2, ← hP₆.pa rbx_cs] at hp₆
  refine WP.mono (ceCall_okL K.ce L₆ (d := L.dv) rbx_na htw K.dv.1 hp₆.1) fun s₇ ⟨hP₇, hb₇⟩ => ?_
  have e₇ := e₆.keep hP₇.b i₇
  have hP₆' := PPost.app (PPost.app (PPost.app (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide))
    hP₄ (by decide)) hP₅ (by decide)) hP₆ (by decide)
  have hP := PPost.app hP₆' hP₇ (by simp [calleeSaved])
  rw [hP₆'.pa rbx_cs] at hb₇
  refine ⟨hP, e₇.out, by
    rw [hP₇.cs .r15 (by decide), hP₆.cs .r15 (by decide), hP₅.cs .r15 (by decide), hP₄.cs .r15 (by decide),
      hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15], ?_⟩
  rw [Kem.ctLen, Params.ctLen, show 32 * (L.p.du * L.p.k + L.p.dv) = 32 * L.du * L.k + 32 * L.dv by
      simp only [Kem.du, Kem.dv, Kem.k]; rw [Nat.mul_add, Nat.mul_assoc], hP.pa rbx_cs, sc, VG.Proof.MlKem.X86_64.bytesAt_split,
    hb₇, hp₆.2, KPke.ct]
  refine congrArg (· ++ _) (VG.Proof.MlKem.X86_64.bytesAt_catK _ _ _ _ _ _ L.k fun i hi => ?_)
  rw [← hP.pa (p := sc (L.oCT + 32 * L.du * i)) rbx_cs, L₀.keepBytes hP.b (hu i hi), h.u i hi]

/-! ## The end of K-PKE.Encrypt -/

/-- The end: `r15` as `allOk`, and the ciphertext if it is 1. -/
structure EOut (L : Kem) (C : VG.Proof.MlKem.X86_64.Ctx rbs wbs) (E : Ptr) (ek m r : List Byte) (s : State) : Prop where
  out : C.Out s
  r15 : s.gpr .r15 = if VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.Enc.rhoE L ek) (L.k * L.k) then 1 else 0
  ct : VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.Enc.rhoE L ek) (L.k * L.k) →
    bytesAt s.mem (pa s (sc L.oCT)) L.ctLen = KPke.ct L.p (VG.Proof.MlKem.X86_64.aHat (VG.Proof.MlKem.X86_64.Enc.rhoE L ek)) ek m r

/-- The end, for the `ρ` of `ek`. -/
abbrev EOρ (L : Kem) (C : VG.Proof.MlKem.X86_64.Ctx rbs wbs) (E : Ptr) (ρ : List Byte) (s : State) : Prop :=
  ∃ ek m r, VG.Proof.MlKem.X86_64.Enc.rhoE L ek = ρ ∧ VG.Proof.MlKem.X86_64.Enc.EOut L C E ek m r s

theorem v_tr {A : Arith} (hA : ArithOk A) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) (hk0 : 0 < L.k) {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs}
    (hc : VG.Proof.MlKem.X86_64.Enc.vChk L (rbs ++ wbs) wbs C.chk E = true) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k L.k L.k x ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k L.k L.k y) (v L A)
      (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.EOρ L C E ρ x ∧ VG.Proof.MlKem.X86_64.Enc.EOρ L C E ρ y) := by
  have hc' := hc
  simp only [VG.Proof.MlKem.X86_64.Enc.vChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hpc⟩, hk15⟩, hac⟩, hdd⟩, hk16⟩, htw⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc'
  refine RelCT.stepL C.bs ?_ fun x ⟨ek, m, r, eρ, hx⟩ => WP.mono (VG.Proof.MlKem.X86_64.Enc.v_ok hA K hk0 hc hx) fun _ ⟨hP, ho, h15, hct⟩ =>
    ⟨⟨_, hP.b⟩, ek, m, r, eρ, ho, by rw [h15, ifp hx.ok], fun _ => hct⟩
  unfold v
  refine RelCT.mono (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs
    (RelCT.mono (dotN_tr hA C.bs hk0 (dotChk_spec hdc)) (fun _ _ h => h) fun _ _ h => h)
    (fun x Lx hx => WP.mono (dotN_ok hA C.bs hk0 (dotChk_spec hdc) Lx
      (a := fun k => polyAt x.mem (pa x (pS (L.k + k)))) (b := fun k => polyAt x.mem (pa x (pS k)))
      (fun k hk => ⟨(hx k hk).1, rfl⟩) (fun k hk => ⟨(hx k hk).2, rfl⟩))
      fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs (nttInvAt_tr hA hic)
      (fun x Lx hx => WP.mono (nttInvAt_ok hA Lx hic hx) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS 16))) C.bs
      (RelCT.mono (cbd2At_trL rbx_na hpc) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (cbd2At_okL Lx rbx_na hpc) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hk15 hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs (addAt_tr rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15)) ∧ Reduced x.mem (pa x (pS 16))) C.bs
      (RelCT.mono (ddCall_trL ddImpl (d := 1) rbx_na hdd (by decide)) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (ddCall_okL ddImpl Lx (d := 1) rbx_na hdd (by decide)) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, Lx.keepRed hP.b hk16 hx, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) C.bs (addAt_tr rbx_na hac)
      (fun x Lx hx => WP.mono (addAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceCall_trL K.ce (d := L.dv) rbx_na htw K.dv.1))))))) (fun x y ⟨hl, ⟨_, _, _, _, h₁⟩, ⟨_, _, _, _, h₂⟩⟩ =>
        ⟨hl, fun k hk => ⟨(h₁.t k hk).1, (h₁.y k hk).1⟩, fun k hk => ⟨(h₂.t k hk).1, (h₂.y k hk).1⟩⟩)
    fun _ _ h => h

end Enc

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.EncTop`. -/
section

/-!
# ML-KEM on x86-64: K-PKE.Encrypt

`encrypt L`, from its inputs and `r15 = 1`: `r15` is 1 exactly when every
`SampleNTT` succeeded, and then the ciphertext is `K-PKE.Encrypt(ek, m, r)`
(`encrypt_ok`); for a given `ρ`, it leaks the same in two runs (`encrypt_tr`).
Every check of the pieces is one Boolean (`encChk`), which the callers
evaluate in their layouts, for each parameter set.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Enc

open VG.Impl.MlKem.X86_64.Encrypt

variable {rbs wbs : List (Reg × Nat)} {E : Ptr} {L : Kem}

/-- Every check of `encrypt`. -/
def encChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  VG.Proof.MlKem.X86_64.Enc.matChk L bs wbs chk E && (List.range (L.k * L.k / 4)).all (fun q => VG.Proof.MlKem.X86_64.Enc.quadEChk L bs wbs chk E (4 * q)) &&
    (List.range (L.k * L.k)).all (fun e => !decide (4 * (L.k * L.k / 4) ≤ e) || sampEChk L bs wbs chk E e) &&
    VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E [] && VG.Proof.MlKem.X86_64.Enc.prfsEChk L bs wbs chk E &&
    (List.range (L.k * L.k)).all (fun e => keepB bs [] (pS (L.pA + e)) 1024) && keepB bs [] (sc oSB) 32 &&
    (List.range L.k).all (VG.Proof.MlKem.X86_64.Enc.yChk L bs wbs chk E) && (List.range L.k).all (VG.Proof.MlKem.X86_64.Enc.uChk L bs wbs chk E) &&
    (List.range L.k).all (VG.Proof.MlKem.X86_64.Enc.tChk L bs wbs chk E) && VG.Proof.MlKem.X86_64.Enc.vChk L bs wbs chk E

structure EncChks (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Prop where
  mat : VG.Proof.MlKem.X86_64.Enc.matChk L bs wbs chk E = true
  q : ∀ q < L.k * L.k / 4, VG.Proof.MlKem.X86_64.Enc.quadEChk L bs wbs chk E (4 * q) = true
  s : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → VG.Proof.MlKem.X86_64.Enc.sampEChk L bs wbs chk E e = true
  inK : VG.Proof.MlKem.X86_64.Enc.inKeep L bs chk E [] = true
  prfs : VG.Proof.MlKem.X86_64.Enc.prfsEChk L bs wbs chk E = true
  aK : ∀ e < L.k * L.k, keepB bs [] (pS (L.pA + e)) 1024 = true
  sbK : keepB bs [] (sc oSB) 32 = true
  y : ∀ N < L.k, VG.Proof.MlKem.X86_64.Enc.yChk L bs wbs chk E N = true
  u : ∀ i < L.k, VG.Proof.MlKem.X86_64.Enc.uChk L bs wbs chk E i = true
  t : ∀ i < L.k, VG.Proof.MlKem.X86_64.Enc.tChk L bs wbs chk E i = true
  v : VG.Proof.MlKem.X86_64.Enc.vChk L bs wbs chk E = true

theorem encChk_spec {bs wbs : List (Reg × Nat)} {chk : List (Ptr × Nat) → Bool} {E : Ptr}
    (h : VG.Proof.MlKem.X86_64.Enc.encChk L bs wbs chk E = true) : VG.Proof.MlKem.X86_64.Enc.EncChks L bs wbs chk E := by
  simp only [VG.Proof.MlKem.X86_64.Enc.encChk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hq⟩, hs⟩, h3⟩, hp⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, hq, fun e he he' => (hs e he).resolve_left (fun h => h he'), h3, hp, h4, h5, h6, h7, h8, h9⟩

theorem rest_ok (v : Sample4Impl) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) (hk : 0 < L.k ∧ L.k ≤ 4) {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs}
    (hc : VG.Proof.MlKem.X86_64.Enc.EncChks L (rbs ++ wbs) wbs C.chk E) {ek m r : List Byte} {s : State} (h : VG.Proof.MlKem.X86_64.Enc.ER0 L C E ek m r s) :
    WP isa (rest L v.callee E) s (VG.Proof.MlKem.X86_64.Enc.EOut L C E ek m r) := by
  unfold rest
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Enc.prfsE_ok v hk.2 hc.prfs h) fun s₀ h₀ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r k 0 0) L.k 0
    (fun k _ hk' s hs => WP.mono (VG.Proof.MlKem.X86_64.Enc.y_ok v.arith (by omega) (hc.y k (by omega)) hs) fun _ h => h.2) s₀ h₀.2)
    fun s₁ h₁ => ?_)
  rw [Nat.zero_add] at h₁
  refine WP.seq (WP.mono (seqR_ok (I := fun k => VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r L.k k 0) L.k 0
    (fun k _ hk' s hs => WP.mono (VG.Proof.MlKem.X86_64.Enc.u_ok v.arith K hk.1 (by omega) (hc.u k (by omega)) hs) fun _ h => h.2) s₁ h₁)
    fun s₂ h₂ => ?_)
  rw [Nat.zero_add] at h₂
  refine WP.seq (WP.mono (seqR_ok (I := fun k => VG.Proof.MlKem.X86_64.Enc.ER L C E ek m r L.k L.k k) L.k 0
    (fun k _ hk' s hs => WP.mono (VG.Proof.MlKem.X86_64.Enc.t_ok (by omega) (hc.t k (by omega)) hs) fun _ h => h.2) s₂ h₂) fun s₃ h₃ => ?_)
  rw [Nat.zero_add] at h₃
  exact WP.mono (VG.Proof.MlKem.X86_64.Enc.v_ok v.arith K hk.1 hc.v h₃) fun _ ⟨_, ho, h15, hct⟩ => ⟨ho, by rw [h15, ifp h₃.ok], fun _ => hct⟩

theorem encrypt_ok (v : Sample4Impl) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) (hk : 0 < L.k ∧ L.k ≤ 4)
    {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} (hc : VG.Proof.MlKem.X86_64.Enc.encChk L (rbs ++ wbs) wbs C.chk E = true) {ek m r : List Byte} {s : State}
    (h : VG.Proof.MlKem.X86_64.Enc.EIn L C E ek m r s) (h15 : s.gpr .r15 = 1) : WP isa (encrypt L v.callee E) s (VG.Proof.MlKem.X86_64.Enc.EOut L C E ek m r) := by
  have hc := VG.Proof.MlKem.X86_64.Enc.encChk_spec hc
  unfold encrypt
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Enc.mat_ok v hk.2 hc.mat hc.q hc.s h h15) fun s₁ h₁ => ?_)
  refine ifOk_ok (fun s₂ hP hne => ?_) fun s₂ hP he => ?_
  · exact VG.Proof.MlKem.X86_64.Enc.rest_ok v K hk hc (ER0.start (h₁.flag hP hc.inK hc.aK hc.sbK) (KeyGen.r15_ne h₁.m.r15 hne))
  · have h₂ := h₁.flag hP hc.inK hc.aK hc.sbK
    exact ⟨h₂.i.out, h₂.m.r15, fun ho => absurd ho (KeyGen.r15_eq h₁.m.r15 he)⟩

theorem rest_tr (v : Sample4Impl) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) (hk : 0 < L.k ∧ L.k ≤ 4)
    {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs} (hc : VG.Proof.MlKem.X86_64.Enc.EncChks L (rbs ++ wbs) wbs C.chk E) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ER0ρ L C E ρ x ∧ VG.Proof.MlKem.X86_64.Enc.ER0ρ L C E ρ y) (rest L v.callee E)
      (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.EOρ L C E ρ x ∧ VG.Proof.MlKem.X86_64.Enc.EOρ L C E ρ y) := by
  unfold rest
  refine RelCT.seq (VG.Proof.MlKem.X86_64.Enc.prfsE_tr v hk.2 hc.prfs) ?_
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ k 0 0 x ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ k 0 0 y) L.k 0
    fun k _ hk' => VG.Proof.MlKem.X86_64.Enc.y_tr v.arith (by omega) (hc.y k (by omega))) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k k 0 x ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k k 0 y) L.k 0
    fun k _ hk' => VG.Proof.MlKem.X86_64.Enc.u_tr v.arith K hk.1 (by omega) (hc.u k (by omega))) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k L.k k x ∧
    VG.Proof.MlKem.X86_64.Enc.ERρ L C E ρ L.k L.k k y) L.k 0 fun k _ hk' => VG.Proof.MlKem.X86_64.Enc.t_tr (by omega) (hc.t k (by omega))) ?_
  rw [Nat.zero_add]
  exact VG.Proof.MlKem.X86_64.Enc.v_tr v.arith K hk.1 hc.v

theorem encrypt_tr (v : Sample4Impl) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) (W : VG.Proof.MlKem.X86_64.KemWf L) {C : VG.Proof.MlKem.X86_64.Ctx rbs wbs}
    (hc : VG.Proof.MlKem.X86_64.Enc.encChk L (rbs ++ wbs) wbs C.chk E = true) {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, E.1]) (copy (sc oSB) (E.1, E.2 + 384 * L.k) 32) h).isSome = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.EIρ L C E ρ x ∧ VG.Proof.MlKem.X86_64.Enc.EIρ L C E ρ y) (encrypt L v.callee E)
      (fun x y => LRel rbs wbs x y ∧ VG.Proof.MlKem.X86_64.Enc.EOρ L C E ρ x ∧ VG.Proof.MlKem.X86_64.Enc.EOρ L C E ρ y) := by
  have hc := VG.Proof.MlKem.X86_64.Enc.encChk_spec hc
  unfold encrypt
  refine RelCT.seq (VG.Proof.MlKem.X86_64.Enc.mat_tr v W.k.2 hc.mat hc.q hc.s W.ijT ht) (ifOk_tr
    (fun x y ⟨_, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => by rw [h₁.m.r15, h₂.m.r15, e₁, e₂])
    (RelCT.mono (VG.Proof.MlKem.X86_64.Enc.rest_tr v K W.k hc) ?_ fun _ _ h => h) ?_)
  · rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, hne⟩
    have o₁ := KeyGen.r15_ne h₁.m.r15 hne
    have o₂ : VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.Enc.rhoE L ek₂) (L.k * L.k) := by rw [e₂, ← e₁]; exact o₁
    exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, ER0.start (h₁.flag hx hc.inK hc.aK hc.sbK) o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, ER0.start (h₂.flag hy hc.inK hc.aK hc.sbK) o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, he⟩
    have o₁ := KeyGen.r15_eq h₁.m.r15 he
    have o₂ : ¬ VG.Proof.MlKem.X86_64.allOk L.k (VG.Proof.MlKem.X86_64.Enc.rhoE L ek₂) (L.k * L.k) := by rw [e₂, ← e₁]; exact o₁
    have k₁ := h₁.flag hx hc.inK hc.aK hc.sbK
    have k₂ := h₂.flag hy hc.inK hc.aK hc.sbK
    exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, k₁.i.out, k₁.m.r15, fun h => absurd h o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, k₂.i.out, k₂.m.r15, fun h => absurd h o₂⟩⟩

end Enc

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.DcSel`. -/
section

/-!
# ML-KEM on x86-64: decapsulation, the choice of the key

The comparison of the ciphertexts of `N` bytes (`cmp_ok`: the OR of the XORs
of their bytes), the mask (`mid_ok`), and the choice of each byte of the key
(`sel_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.Sha3 (bytesAt)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

theorem cmpBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 1) :
    WP isa cmpBody s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rdx = s.gpr .rdx ||| (BitVec.setWidth 64 (s.mem (s.gpr .rsi)) ^^^
          BitVec.setWidth 64 (s.mem (s.gpr .rdi))) ∧ s'.gpr .rsi = s.gpr .rsi + 1 ∧
        s'.gpr .rdi = s.gpr .rdi + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold cmpBody
  xrun [h0, h1]

theorem selBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 1) (h2 : InRegions s.wr (s.gpr .r8) 1) :
    WP isa selBody s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r8) (BitVec.setWidth 8 (((BitVec.setWidth 64 (s.mem (s.gpr .rsi)) ^^^
          BitVec.setWidth 64 (s.mem (s.gpr .rdi))) &&& s.gpr .rax) ^^^ BitVec.setWidth 64 (s.mem (s.gpr .rdi)))) ∧
        s'.gpr .rax = s.gpr .rax ∧ s'.gpr .rsi = s.gpr .rsi + 1 ∧ s'.gpr .rdi = s.gpr .rdi + 1 ∧
        s'.gpr .r8 = s.gpr .r8 + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.r9, .r10, .rsi, .rdi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold selBody
  xrun [h0, h1, h2]

/-- The block between the loops: the mask, and the pointers of the choice. -/
abbrev midB : List Instr := [.alu .sub .rdx (.imm 1), .alu .sbb .rax (.reg .rax), .mov .rsi (.reg .rbx),
  .alu .add .rsi (.imm (BitVec.ofNat 32 oG)), .mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 oKB)),
  .mov .r8 (.reg .r12), .mov32 .rcx (.imm 32)]

theorem mask_eq (x : BitVec 64) :
    0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < BitVec.toNat (1 : BitVec 64)))) =
      if x = 0 then BitVec.allOnes 64 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · have : ¬ x.toNat < 1 := fun h' => h (BitVec.eq_of_toNat_eq (by simp; omega))
    rw [ifn h, show BitVec.toNat (1 : BitVec 64) = 1 from rfl, decide_eq_false this]
    decide

theorem mid_ok (s : State) :
    WP isa (.block VG.Proof.MlKem.X86_64.Decaps.midB) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rax = (if s.gpr .rdx = 0 then BitVec.allOnes 64 else 0) ∧
        s'.gpr .rsi = pa s (sc oG) ∧ s'.gpr .rdi = pa s (sc oKB) ∧ s'.gpr .r8 = pa s (.r12, 0) ∧
        s'.gpr .rcx = BitVec.ofNat 64 32) ∧
      Keep [.rax, .rdx, .rsi, .rdi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [sx_ofNat (show oG < 2 ^ 31 by decide), sx_ofNat (show oKB < 2 ^ 31 by decide)]
  exact ⟨VG.Proof.MlKem.X86_64.Decaps.mask_eq _, by rw [pa, add_ofNat_zero]⟩

/-! ## The loops -/

/-- The OR of the XORs of the bytes of `xs` and `ys`. -/
def accX (xs ys : List Byte) : Byte := (List.zipWith (· ^^^ ·) xs ys).foldl (· ||| ·) 0

theorem bytesAt_succ (m : Mem) (p : Addr) (k : Nat) :
    bytesAt m p (k + 1) = bytesAt m p k ++ [m (p + BitVec.ofNat 64 k)] := by
  rw [bytesAt_add, bytesAt_one]

theorem accX_snoc {xs ys : List Byte} (h : xs.length = ys.length) (x y : Byte) :
    VG.Proof.MlKem.X86_64.Decaps.accX (xs ++ [x]) (ys ++ [y]) = VG.Proof.MlKem.X86_64.Decaps.accX xs ys ||| (x ^^^ y) := by
  simp only [VG.Proof.MlKem.X86_64.Decaps.accX, List.zipWith_append h, List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem zx_or_xor (a x y : Byte) :
    BitVec.setWidth 64 a ||| (BitVec.setWidth 64 x ^^^ BitVec.setWidth 64 y) = BitVec.setWidth 64 (a ||| (x ^^^ y)) := by
  ext i hi
  simp

theorem sel_byte (x y : Byte) (e : Bool) :
    BitVec.setWidth 8 (((BitVec.setWidth 64 x ^^^ BitVec.setWidth 64 y) &&& (if e then BitVec.allOnes 64 else 0)) ^^^
      BitVec.setWidth 64 y) = if e then x else y := by
  cases e
  · ext i hi; simp
  · rw [ifp rfl, ifp rfl, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact b8b x

theorem cmp_ok (s : State) {N : Nat} (hN : N < 2 ^ 32) (hN0 : 0 < N) {a b : Addr}
    (ha : InRegions (s.rd ++ s.wr) a N) (hb : InRegions (s.rd ++ s.wr) b N)
    (hsi : s.gpr .rsi = a) (hdi : s.gpr .rdi = b) (hdx : s.gpr .rdx = 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 N) :
    WP isa (.loop cmpBody .ne) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.gpr .rdx = BitVec.setWidth 64 (VG.Proof.MlKem.X86_64.Decaps.accX (bytesAt s.mem a N) (bytesAt s.mem b N)) ∧
      Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s' := by
  refine wp_countdown (cnt := .rcx) (N := N) (by omega) hN0 (fun k s' =>
      s'.gpr .rsi = a + BitVec.ofNat 64 k ∧ s'.gpr .rdi = b + BitVec.ofNat 64 k ∧
      s'.gpr .rdx = BitVec.setWidth 64 (VG.Proof.MlKem.X86_64.Decaps.accX (bytesAt s.mem a k) (bytesAt s.mem b k)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s')
    (fun k hk s' ⟨hsi', hdi', hdx', hm', hrd', hwr', kk⟩ _ => ?_) (fun _ ⟨_, _, h1, h2, h3, h4, h5⟩ => ⟨h2, h3, h4, h1, h5⟩)
    ⟨by rw [hsi]; simp, by rw [hdi]; simp, by rw [hdx]; rfl, rfl, rfl, rfl, Keep.refl _ _⟩ hcx
  refine WP.mono (VG.Proof.MlKem.X86_64.Decaps.cmpBody_ok s' (by rw [hrd', hwr', hsi']; exact inRegions_byte ha hk (by omega))
    (by rw [hrd', hwr', hdi']; exact inRegions_byte hb hk (by omega))) fun s'' ⟨⟨hm, hdx, hsi'', hdi'', hcx, hz⟩, k'⟩ =>
      ⟨⟨by rw [hsi'', hsi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
        by rw [hdi'', hdi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add], ?_, hm.trans hm',
        k'.2.1.trans hrd', k'.2.2.trans hwr', (kk.trans k').mono (by decide)⟩, hcx, hz⟩
  rw [hdx, hdx', hsi', hdi', hm', VG.Proof.MlKem.X86_64.Decaps.zx_or_xor, VG.Proof.MlKem.X86_64.Decaps.bytesAt_succ, VG.Proof.MlKem.X86_64.Decaps.bytesAt_succ,
    VG.Proof.MlKem.X86_64.Decaps.accX_snoc (by rw [bytesAt_length, bytesAt_length])]

theorem sel_ok (s : State) {g kb key : Addr} (e : Bool) (hg : InRegions (s.rd ++ s.wr) g 32)
    (hkb : InRegions (s.rd ++ s.wr) kb 32) (hkey : InRegions s.wr key 32)
    (dg : Region.Disjoint ⟨g, 32⟩ ⟨key, 32⟩) (dkb : Region.Disjoint ⟨kb, 32⟩ ⟨key, 32⟩)
    (hsi : s.gpr .rsi = g) (hdi : s.gpr .rdi = kb) (h8 : s.gpr .r8 = key)
    (hax : s.gpr .rax = if e then BitVec.allOnes 64 else 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 32) :
    WP isa (.loop selBody .ne) s fun s' =>
      bytesAt s'.mem key 32 = (if e then bytesAt s.mem g 32 else bytesAt s.mem kb 32) ∧
      Frame [⟨key, 32⟩] s.mem s'.mem ∧ Keep [.r9, .r10, .rsi, .rdi, .r8, .rcx] s s' := by
  refine WP.mono (wp_countdown (cnt := .rcx) (N := 32) (by decide) (by decide) (fun k s' =>
      s'.gpr .rsi = g + BitVec.ofNat 64 k ∧ s'.gpr .rdi = kb + BitVec.ofNat 64 k ∧
      s'.gpr .r8 = key + BitVec.ofNat 64 k ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨key, 32⟩] s.mem s'.mem ∧
      (∀ j < k, s'.mem (key + BitVec.ofNat 64 j) =
        if e then s.mem (g + BitVec.ofNat 64 j) else s.mem (kb + BitVec.ofNat 64 j)) ∧
      Keep [.r9, .r10, .rsi, .rdi, .r8, .rcx] s s')
    (fun k hk s' ⟨hsi', hdi', h8', hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [hsi]; simp, by rw [hdi]; simp, by rw [h8]; simp, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _), Keep.refl _ _⟩ hcx) fun s' ⟨_, _, _, _, _, hf, hc, kk⟩ => ⟨?_, hf, kk⟩
  · have hax' : s'.gpr .rax = if e then BitVec.allOnes 64 else 0 := by rw [kk.gpr (by decide)]; exact hax
    refine WP.mono (VG.Proof.MlKem.X86_64.Decaps.selBody_ok s' (by rw [hrd', hwr', hsi']; exact inRegions_byte hg hk (by omega))
      (by rw [hrd', hwr', hdi']; exact inRegions_byte hkb hk (by omega))
      (by rw [hwr', h8']; exact inRegions_byte hkey hk (by omega)))
      fun s'' ⟨⟨hm, hax'', hsi'', hdi'', h8'', hcx, hz⟩, k'⟩ =>
        ⟨⟨by rw [hsi'', hsi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
          by rw [hdi'', hdi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
          by rw [h8'', h8', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
          k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_, (kk.trans k').mono (by decide)⟩, hcx, hz⟩
    · rw [hm, h8']
      exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega) (by omega))
    · have eg : s'.mem (g + BitVec.ofNat 64 k) = s.mem (g + BitVec.ofNat 64 k) :=
        hf.bytes (R := ⟨g, 32⟩) (by simpa using dg) (show 32 ≤ 2 ^ 64 by decide) hk
      have ekb : s'.mem (kb + BitVec.ofNat 64 k) = s.mem (kb + BitVec.ofNat 64 k) :=
        hf.bytes (R := ⟨kb, 32⟩) (by simpa using dkb) (show 32 ≤ 2 ^ 64 by decide) hk
      rw [hm, h8', VG.WriteBytes.writeW8_apply]
      by_cases ej : j = k
      · subst ej
        rw [ifp rfl, hsi', hdi', hax', VG.Proof.MlKem.X86_64.Decaps.sel_byte, eg, ekb]
      · rw [ifn (fun h => ej (by have := congrArg BitVec.toNat h; simp at this; omega)), hc j (by omega)]
  · cases e
    · simp only [bytesAt, Bool.false_eq_true, ite_false]
      exact List.map_congr_left fun i hi => by simpa using hc i (List.mem_range.mp hi)
    · simp only [bytesAt, ite_true]
      exact List.map_congr_left fun i hi => by simpa using hc i (List.mem_range.mp hi)

/-! ## The choice -/

abbrev setupB (L : Kem) : List Instr := [.mov .rsi (.reg .r14), .mov .rdi (.reg .rbx),
  .alu .add .rdi (.imm (BitVec.ofNat 32 L.oCT)), .mov32 .rcx (.imm (BitVec.ofNat 32 L.ctLen)), .mov32 .rdx (.imm 0)]

theorem setup_ok {L : Kem} (ho : L.oCT < 2 ^ 31) (hn : L.ctLen < 2 ^ 32) (s : State) :
    WP isa (.block (VG.Proof.MlKem.X86_64.Decaps.setupB L)) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rsi = pa s (.r14, 0) ∧ s'.gpr .rdi = pa s (sc L.oCT) ∧
        s'.gpr .rcx = BitVec.ofNat 64 L.ctLen ∧ s'.gpr .rdx = 0) ∧
      Keep [.rsi, .rdi, .rcx, .rdx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [sx_ofNat ho, sw_ofNat hn]
  rw [pa, add_ofNat_zero]

theorem zx_eq_zero {x : Byte} : BitVec.setWidth 64 x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have := congrArg (BitVec.setWidth 8) h
    rwa [b8b] at this
  · intro h; rw [h]; rfl

theorem select_ok {L : Kem} (ho : L.oCT < 2 ^ 31) (hn : L.ctLen < 2 ^ 32) (hn0 : 0 < L.ctLen) {s : State}
    (hc : InRegions (s.rd ++ s.wr) (pa s (.r14, 0)) L.ctLen)
    (hct : InRegions (s.rd ++ s.wr) (pa s (sc L.oCT)) L.ctLen) (hg : InRegions (s.rd ++ s.wr) (pa s (sc oG)) 32)
    (hkb : InRegions (s.rd ++ s.wr) (pa s (sc oKB)) 32) (hkey : InRegions s.wr (pa s (.r12, 0)) 32)
    (dg : Region.Disjoint ⟨pa s (sc oG), 32⟩ ⟨pa s (.r12, 0), 32⟩)
    (dkb : Region.Disjoint ⟨pa s (sc oKB), 32⟩ ⟨pa s (.r12, 0), 32⟩) :
    WP isa (select L) s fun s' => PPost s s' [((.r12, 0), 32)] ∧
      bytesAt s'.mem (pa s (.r12, 0)) 32 =
        if bytesAt s.mem (pa s (.r14, 0)) L.ctLen = bytesAt s.mem (pa s (sc L.oCT)) L.ctLen then
          bytesAt s.mem (pa s (sc oG)) 32 else bytesAt s.mem (pa s (sc oKB)) 32 := by
  unfold select
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Decaps.setup_ok ho hn s) fun s₁ ⟨⟨hm₁, hsi₁, hdi₁, hcx₁, hdx₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Decaps.cmp_ok s₁ hn hn0 (by rw [k₁.2.1, k₁.2.2]; exact hc) (by rw [k₁.2.1, k₁.2.2]; exact hct) hsi₁ hdi₁
    hdx₁ hcx₁) fun s₂ ⟨hm₂, hrd₂, hwr₂, hdx₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Decaps.mid_ok s₂) fun s₃ ⟨⟨hm₃, hax₃, hsi₃, hdi₃, h8₃, hcx₃⟩, k₃⟩ => ?_)
  have e12 : ∀ r ∈ [Reg.rbx, Reg.r12], s₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.gpr (by simp at hr; rcases hr with rfl | rfl <;> decide),
      k₁.gpr (by simp at hr; rcases hr with rfl | rfl <;> decide)]
  have pG : pa s₂ (sc oG) = pa s (sc oG) := by rw [pa, pa, e12 .rbx (by simp)]
  have pKB : pa s₂ (sc oKB) = pa s (sc oKB) := by rw [pa, pa, e12 .rbx (by simp)]
  have pK : pa s₂ (.r12, 0) = pa s (.r12, 0) := by rw [pa, pa, e12 .r12 (by simp)]
  rw [pG] at hsi₃; rw [pKB] at hdi₃; rw [pK] at h8₃
  have hmem : s₃.mem = s.mem := by rw [hm₃, hm₂, hm₁]
  have hrd : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [k₃.2.1, k₃.2.2, hrd₂, hwr₂, k₁.2.1, k₁.2.2]
  have hwr : s₃.wr = s.wr := by rw [k₃.2.2, hwr₂, k₁.2.2]
  have hax : s₃.gpr .rax = if decide (bytesAt s.mem (pa s (.r14, 0)) L.ctLen = bytesAt s.mem (pa s (sc L.oCT)) L.ctLen) then
      BitVec.allOnes 64 else 0 := by
    rw [hax₃, hdx₂, hm₁, ← hsi₁, ← hdi₁, hsi₁, hdi₁]
    exact ite_congr (propext (zx_eq_zero.trans ((eq_iff_foldl_or_xor
      (by rw [bytesAt_length, bytesAt_length])).symm.trans decide_eq_true_iff.symm)))
      (fun _ => rfl) (fun _ => rfl)
  refine WP.mono (VG.Proof.MlKem.X86_64.Decaps.sel_ok s₃ _ (by rw [hrd]; exact hg) (by rw [hrd]; exact hkb) (by rw [hwr]; exact hkey) dg dkb hsi₃
    hdi₃ h8₃ hax hcx₃) fun s₄ ⟨hb, hf, k₄⟩ => ⟨?_, ?_⟩
  · refine post_of_keep ((((k₁.trans k₂).trans k₃).trans k₄).mono (rs' := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10])
      (by decide)) (by decide) ?_
    rw [← hmem]; exact hf
  · rw [hb, hmem]
    simp only [decide_eq_true_eq]

end Decaps

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.DcBase`. -/
section

/-!
# ML-KEM on x86-64: decapsulation, its contract, layout, checks and entry

For a parameter set `L`: the contract the proof is written against
(`decapsK L`, which the shared contract implies), the layout of the
function's buffers (`dk` and `c` in `rbp` and `r14`, which may overlap each
other; `scratch` and `key` in `rbx` and `r12`), what holds throughout (`DC`:
`Top`, and `dk` and `c` at their pointers), the checks of the layout every
piece needs (`DcWf L`), and the prologue.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `kemDecaps L (dk = rdi, ct = rsi, key = rdx, scratch = rcx) -> eax`, with 32 bytes of stack. -/
def decapsK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, L.dkLen⟩, ⟨s.gpr .rsi, L.ctLen⟩] ∧ s.wr = [⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, L.scr⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, L.dkLen⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, L.dkLen⟩ ⟨s.gpr .rcx, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, L.ctLen⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, L.ctLen⟩ ⟨s.gpr .rcx, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, L.scr⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, L.dkLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, L.ctLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, L.scr⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, L.dkLen⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, L.ctLen⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, L.scr⟩ ∧
    (s.gpr .rdi).toNat + L.dkLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + L.ctLen ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + L.scr ≤ 2 ^ 64
  post s s' :=
    Outcome (fun iters => decapsInternal L.p iters (bytesAt s.mem (s.gpr .rdi) L.dkLen)
      (bytesAt s.mem (s.gpr .rsi) L.ctLen)) ((s'.gpr .rax).setWidth 32) (bytesAt s'.mem (s.gpr .rdx) 32)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    dkRho L.p (bytesAt s₁.mem (s₁.gpr .rdi) L.dkLen) = dkRho L.p (bytesAt s₂.mem (s₂.gpr .rdi) L.dkLen)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

variable (L : Kem)

/-- The pointers the function keeps. -/
abbrev dcM : List (Reg × Reg) := [(.rbx, .rcx), (.rbp, .rdi), (.r14, .rsi), (.r12, .rdx)]
/-- `dk` and `c`. -/
abbrev dcR : List (Reg × Nat) := [(.rbp, L.dkLen), (.r14, L.ctLen)]
/-- `scratch` and `key`. -/
abbrev dcW : List (Reg × Nat) := [(.rbx, L.scr), (.r12, 32)]
abbrev dcB : List (Reg × Nat) := VG.Proof.MlKem.X86_64.Decaps.dcR L ++ VG.Proof.MlKem.X86_64.Decaps.dcW L

theorem dcB_bases : ∀ b ∈ VG.Proof.MlKem.X86_64.Decaps.dcB L, b.1 ∈ bases := by
  intro b hb; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp [bases]

theorem dcM_bases : ∀ p ∈ VG.Proof.MlKem.X86_64.Decaps.dcM, p.1 ∈ bases := by decide

/-- A piece that writes `ws` keeps `DC`. -/
def dcChk (ws : List (Ptr × Nat)) : Bool :=
  topChk (VG.Proof.MlKem.X86_64.Decaps.dcB L) ws && keepB (VG.Proof.MlKem.X86_64.Decaps.dcB L) ws (.rbp, 0) L.dkLen && keepB (VG.Proof.MlKem.X86_64.Decaps.dcB L) ws (.r14, 0) L.ctLen

/-- A piece that writes `ws` keeps `DR nu ns`. -/
def drChk (nu ns : Nat) (ws : List (Ptr × Nat)) : Bool :=
  VG.Proof.MlKem.X86_64.Decaps.dcChk L ws && (List.range nu).all (fun i => keepB (VG.Proof.MlKem.X86_64.Decaps.dcB L) ws (pS i) 1024) &&
    (List.range ns).all (fun i => keepB (VG.Proof.MlKem.X86_64.Decaps.dcB L) ws (pS (L.k + i)) 1024)

abbrev uW (i : Nat) : List (Ptr × Nat) := [(pS i, 1024)] ++ [(pS i, 1024), (sc oSS, 1024)]

def uChk (i : Nat) : Bool :=
  twoChk (VG.Proof.MlKem.X86_64.Decaps.dcB L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) (.r14, 32 * L.du * i) (32 * L.du) (pS i) 1024 && ipChk (VG.Proof.MlKem.X86_64.Decaps.dcB L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) (pS i) &&
    VG.Proof.MlKem.X86_64.Decaps.drChk L i 0 (VG.Proof.MlKem.X86_64.Decaps.uW i)

def sChk (i : Nat) : Bool :=
  twoChk (VG.Proof.MlKem.X86_64.Decaps.dcB L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) (.rbp, 384 * i) 384 (pS (L.k + i)) 1024 && VG.Proof.MlKem.X86_64.Decaps.drChk L L.k i [(pS (L.k + i), 1024)]

abbrev tailW : List (Ptr × Nat) := dotW L.k ++ [(pS 15, 1024), (sc oSS, 1024)] ++ [(pS 16, 1024)] ++
  [(pS 16, 1024)] ++ [(sc oM, 32 * 1)]

def tailChk : Bool :=
  dotChk (VG.Proof.MlKem.X86_64.Decaps.dcB L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) (fun j => pS (L.k + j)) pS L.k && ipChk (VG.Proof.MlKem.X86_64.Decaps.dcB L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) (pS 15) &&
    twoChk (VG.Proof.MlKem.X86_64.Decaps.dcB L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) (.r14, 32 * L.du * L.k) (32 * L.dv) (pS 16) 1024 &&
    keepB (VG.Proof.MlKem.X86_64.Decaps.dcB L) [(pS 16, 1024)] (pS 15) 1024 && accChk (VG.Proof.MlKem.X86_64.Decaps.dcB L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) (pS 16) (pS 15) &&
    twoChk (VG.Proof.MlKem.X86_64.Decaps.dcB L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) (pS 16) 1024 (sc oM) (32 * 1) && VG.Proof.MlKem.X86_64.Decaps.dcChk L (VG.Proof.MlKem.X86_64.Decaps.tailW L) &&
    VG.Proof.MlKem.X86_64.Decaps.dcChk L (dotW L.k ++ [(pS 15, 1024), (sc oSS, 1024)])

def dckChk (ws : List (Ptr × Nat)) : Bool := VG.Proof.MlKem.X86_64.Decaps.dcChk L ws && keepB (VG.Proof.MlKem.X86_64.Decaps.dcB L) ws (sc oG) 32 && keepB (VG.Proof.MlKem.X86_64.Decaps.dcB L) ws (sc oKB) 32

/-- The writes of the hashes. -/
abbrev hW₁ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), (sc oG, 64)]
abbrev hW₂ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), (sc oKB, 32)]

/-- What every piece of decapsulation needs of the layout, evaluated for each parameter set. -/
structure DcWf : Prop extends VG.Proof.MlKem.X86_64.KemWf L where
  scr : 888 ≤ L.scr ∧ L.scr < 2 ^ 32
  small : ∀ b ∈ VG.Proof.MlKem.X86_64.Decaps.dcB L, b.2 < 2 ^ 32
  -- K-PKE.Decrypt
  u : ∀ i < L.k, VG.Proof.MlKem.X86_64.Decaps.uChk L i = true
  s : ∀ i < L.k, VG.Proof.MlKem.X86_64.Decaps.sChk L i = true
  tail : VG.Proof.MlKem.X86_64.Decaps.tailChk L = true
  -- the hashes
  h₁ : hashChk (VG.Proof.MlKem.X86_64.Decaps.dcB L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)] 72 (sc oG) 64 = true
  h₁K : VG.Proof.MlKem.X86_64.Decaps.dcChk L VG.Proof.MlKem.X86_64.Decaps.hW₁ = true
  h₁M : keepB (VG.Proof.MlKem.X86_64.Decaps.dcB L) VG.Proof.MlKem.X86_64.Decaps.hW₁ (sc oM) 32 = true
  h₂ : hashChk (VG.Proof.MlKem.X86_64.Decaps.dcB L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) [((.rbp, 768 * L.k + 64), 32), ((.r14, 0), L.ctLen)] 136 (sc oKB) 32 = true
  h₂K : VG.Proof.MlKem.X86_64.Decaps.dcChk L VG.Proof.MlKem.X86_64.Decaps.hW₂ = true
  h₂G : keepB (VG.Proof.MlKem.X86_64.Decaps.dcB L) VG.Proof.MlKem.X86_64.Decaps.hW₂ (sc oG) 64 = true
  h₂M : keepB (VG.Proof.MlKem.X86_64.Decaps.dcB L) VG.Proof.MlKem.X86_64.Decaps.hW₂ (sc oM) 32 = true
  enc : Enc.encChk L (VG.Proof.MlKem.X86_64.Decaps.dcB L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) (VG.Proof.MlKem.X86_64.Decaps.dckChk L) (.rbp, 384 * L.k) = true
  -- the choice of the key
  selK : VG.Proof.MlKem.X86_64.Decaps.dcChk L [((.r12, 0), 32)] = true
  sel : inB (VG.Proof.MlKem.X86_64.Decaps.dcB L) (.r14, 0) L.ctLen = true ∧ inB (VG.Proof.MlKem.X86_64.Decaps.dcB L) (sc L.oCT) L.ctLen = true ∧
    inB (VG.Proof.MlKem.X86_64.Decaps.dcB L) (sc oG) 32 = true ∧ inB (VG.Proof.MlKem.X86_64.Decaps.dcB L) (sc oKB) 32 = true ∧ inB (VG.Proof.MlKem.X86_64.Decaps.dcW L) (.r12, 0) 32 = true ∧
    sepB (VG.Proof.MlKem.X86_64.Decaps.dcB L) (sc oG) 32 (.r12, 0) 32 = true ∧ sepB (VG.Proof.MlKem.X86_64.Decaps.dcB L) (sc oKB) 32 (.r12, 0) 32 = true
  ct : L.oCT < 2 ^ 31 ∧ L.ctLen < 2 ^ 32 ∧ 0 < L.ctLen
  sv : ∀ k < 6, inB (VG.Proof.MlKem.X86_64.Decaps.dcB L) (sc (oSV + 8 * k)) 8 = true
  -- constant time
  inBs : inB (VG.Proof.MlKem.X86_64.Decaps.dcB L) (sc 0) 1 = true ∧ inB (VG.Proof.MlKem.X86_64.Decaps.dcB L) (.r12, 0) 1 = true ∧ inB (VG.Proof.MlKem.X86_64.Decaps.dcB L) (.r14, 0) 1 = true
  selT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .r12, .r14]) (select L) h).isSome = true
  rhoT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp]) (copy (sc oSB) (.rbp, 384 * L.k + 384 * L.k) 32)
    h).isSome = true

section
variable {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.decapsK L).pre σ)
include W hp

theorem dcLay {s : State} (h : Top VG.Proof.MlKem.X86_64.Decaps.dcM σ s) : Lay (VG.Proof.MlKem.X86_64.Decaps.dcR L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .rcx := h.regs (.rbx, .rcx) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r14 = σ.gpr .rsi := h.regs (.r14, .rsi) (by decide)
  have e4 : s.gpr .r12 = σ.gpr .rdx := h.regs (.r12, .rdx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of W.small (pw4 ?_ ?_ ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_)
    (fa2 ?_ ?_) (fa4 ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, h.rsp, retR]
  · exact fun hw => absurd hw (by decide)
  · exact fun _ => d2
  · exact fun _ => d1
  · exact fun _ => d4
  · exact fun _ => d3
  · exact fun _ => d5.symm
  exacts [k1, k2, k4, k3, n1, n2, n4, n3,
    mem ⟨σ.gpr .rdi, L.dkLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rsi, L.ctLen⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .rcx, L.scr⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, 32⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    r1, r2, r4, r3]

end

/-- `dk` and `c`. -/
abbrev dcDk (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) L.dkLen
abbrev dcC (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) L.ctLen

/-- What holds throughout. -/
structure DC (L : Kem) (σ s : State) : Prop where
  top : Top VG.Proof.MlKem.X86_64.Decaps.dcM σ s
  dk : bytesAt s.mem (pa s (.rbp, 0)) L.dkLen = VG.Proof.MlKem.X86_64.Decaps.dcDk L σ
  c : bytesAt s.mem (pa s (.r14, 0)) L.ctLen = VG.Proof.MlKem.X86_64.Decaps.dcC L σ

section
variable {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.decapsK L).pre σ)
include W hp

theorem DC.lay {s : State} (h : VG.Proof.MlKem.X86_64.Decaps.DC L σ s) : Lay (VG.Proof.MlKem.X86_64.Decaps.dcR L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) s := VG.Proof.MlKem.X86_64.Decaps.dcLay W hp h.top

theorem DC.step {s s' : State} (h : VG.Proof.MlKem.X86_64.Decaps.DC L σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (hc : VG.Proof.MlKem.X86_64.Decaps.dcChk L ws = true) : VG.Proof.MlKem.X86_64.Decaps.DC L σ s' := by
  simp only [VG.Proof.MlKem.X86_64.Decaps.dcChk, Bool.and_eq_true] at hc
  have L₀ := h.lay W hp
  exact ⟨h.top.step L₀ hP VG.Proof.MlKem.X86_64.Decaps.dcM_bases hc.1.1, by rw [L₀.keepBytes hP hc.1.2]; exact h.dk,
    by rw [L₀.keepBytes hP hc.2]; exact h.c⟩

end

/-- Bytes of a buffer. -/
theorem slice_of {s : State} {r : Reg} {n : Nat} {B : List Byte} (h : bytesAt s.mem (pa s (r, 0)) n = B) {o l : Nat}
    (hol : o + l ≤ n) : bytesAt s.mem (pa s (r, o)) l = (B.drop o).take l := by
  rw [← h, bytesAt_slice _ _ hol, pa, pa, off_add, Nat.zero_add]

theorem pro_eq : VG.Impl.MlKem.X86_64.Decaps.pro = [.store (at_ .rcx 840) .rbx, .store (at_ .rcx 848) .rbp, .store (at_ .rcx 856) .r12,
    .store (at_ .rcx 864) .r13, .store (at_ .rcx 872) .r14, .store (at_ .rcx 880) .r15, .mov .rbx (.reg .rcx),
    .mov .rbp (.reg .rdi), .mov .r14 (.reg .rsi), .mov .r12 (.reg .rdx), .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.decapsK L).pre σ) :
    WP isa (.block VG.Impl.MlKem.X86_64.Decaps.pro) σ fun s => VG.Proof.MlKem.X86_64.Decaps.DC L σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp'
  have hsc := W.scr
  have hS : ⟨σ.gpr .rcx, L.scr⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ L.scr → (⟨σ.gpr .rcx, L.scr⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ L.scr → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [VG.Proof.MlKem.X86_64.Decaps.pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r14, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .rcx + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .rcx + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .rcx + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r14 = σ.gpr .rsi ∧ s.gpr .r12 = σ.gpr .rdx ∧
    s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h14, h12, h15⟩, k⟩ => ⟨?_, h15⟩
  have hf : Frame [⟨σ.gpr .rcx, L.scr⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  have hdk := W.small (.rbp, L.dkLen) (by simp)
  have hct := W.small (.r14, L.ctLen) (by simp)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa4 hbx hbp h14 h12, fun j hj => ?_, ?_⟩, ?_, ?_⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .rcx) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r4) (by decide)
  · rw [pa, hbp, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d2) (by simp only at hdk; omega)
  · rw [pa, h14, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d4) (by simp only at hct; omega)

end Decaps

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.DcDec`. -/
section

/-!
# ML-KEM on x86-64: decapsulation, K-PKE.Decrypt

`NTT(u'[i])` (`u_ok`), `ŝ[i]` (`s_ok`), and `m' = ByteEncode₁(Compress₁(v' -
NTT⁻¹(ŝ ∘ û)))` to `M` (`tail_ok`): `m' = K-PKE.Decrypt(dk_PKE, c)`. Between
the steps, `DR nu ns`: the first `nu` of `û` and `ns` of `ŝ` are done. Each
with its constant time.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

abbrev R (L : Kem) (I : State → State → Prop) : State → State → Prop := Rel2 (VG.Proof.MlKem.X86_64.decapsK L).pre (VG.Proof.MlKem.X86_64.decapsK L).pub I

theorem dc_lrel {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {σ₁ σ₂ x y : State} (p₁ : (VG.Proof.MlKem.X86_64.decapsK L).pre σ₁) (p₂ : (VG.Proof.MlKem.X86_64.decapsK L).pre σ₂)
    (pub : (VG.Proof.MlKem.X86_64.decapsK L).pub σ₁ σ₂) (h₁ : VG.Proof.MlKem.X86_64.Decaps.DC L σ₁ x) (h₂ : VG.Proof.MlKem.X86_64.Decaps.DC L σ₂ y) : LRel (VG.Proof.MlKem.X86_64.Decaps.dcR L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) x y := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := pub
  refine ⟨h₁.lay W p₁, h₂.lay W p₂, fa4 ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e5]⟩
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.r14, .rsi) (by decide), h₂.top.regs (.r14, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.rbx, .rcx) (by decide), h₂.top.regs (.rbx, .rcx) (by decide), e4]
  · rw [h₁.top.regs (.r12, .rdx) (by decide), h₂.top.regs (.r12, .rdx) (by decide), e3]

/-- The steps of K-PKE.Decrypt. -/
structure DR (L : Kem) (nu ns : Nat) (σ s : State) : Prop where
  dc : VG.Proof.MlKem.X86_64.Decaps.DC L σ s
  r15 : s.gpr .r15 = 1
  u : ∀ i < nu, PolyIs s.mem (pa s (pS i)) (ntt (KPke.dcU L.p (VG.Proof.MlKem.X86_64.Decaps.dcC L σ) i))
  sh : ∀ i < ns, PolyIs s.mem (pa s (pS (L.k + i))) (dcS (KPke.dkPke L.p (VG.Proof.MlKem.X86_64.Decaps.dcDk L σ)) i)

theorem DR.keep {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.decapsK L).pre σ) {nu ns : Nat} {s s' : State}
    (h : VG.Proof.MlKem.X86_64.Decaps.DR L nu ns σ s) {ws : List (Ptr × Nat)} (hP : PPost s s' ws) (hc : VG.Proof.MlKem.X86_64.Decaps.drChk L nu ns ws = true) :
    VG.Proof.MlKem.X86_64.Decaps.DR L nu ns σ s' := by
  simp only [VG.Proof.MlKem.X86_64.Decaps.drChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨hdc, kU⟩, kS⟩ := hc
  have L₀ := h.dc.lay W hp
  exact ⟨h.dc.step W hp hP.b hdc, by rw [hP.cs .r15 (by decide)]; exact h.r15,
    fun i hi => L₀.keepPoly hP.b (kU i hi) (h.u i hi), fun i hi => L₀.keepPoly hP.b (kS i hi) (h.sh i hi)⟩

theorem DR.zero {L : Kem} {σ s : State} (h : VG.Proof.MlKem.X86_64.Decaps.DC L σ s) (h15 : s.gpr .r15 = 1) : VG.Proof.MlKem.X86_64.Decaps.DR L 0 0 σ s :=
  ⟨h, h15, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- `32 d_u (i + 1) ≤ |c|`. -/
theorem uSlice_le (L : Kem) {i : Nat} (hi : i < L.k) : 32 * L.du * i + 32 * L.du ≤ L.ctLen := by
  have : 32 * L.du * (i + 1) ≤ 32 * L.du * L.k := Nat.mul_le_mul_left _ hi
  simp only [Kem.ctLen, Params.ctLen, Kem.du, Kem.k] at this ⊢
  rw [Nat.mul_succ] at this
  rw [Nat.mul_add, ← Nat.mul_assoc]
  omega

/-! ## `û` -/

theorem u_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) {σ : State}
    (hp : (VG.Proof.MlKem.X86_64.decapsK L).pre σ) {i : Nat} (hi : i < L.k) {s : State} (h : VG.Proof.MlKem.X86_64.Decaps.DR L i 0 σ s) :
    WP isa (uHat L A i) s (VG.Proof.MlKem.X86_64.Decaps.DR L (i + 1) 0 σ) := by
  have hc := W.u i hi
  simp only [VG.Proof.MlKem.X86_64.Decaps.uChk, Bool.and_eq_true] at hc
  obtain ⟨⟨hdd, hic⟩, hrc⟩ := hc
  have L₀ := h.dc.lay W hp
  unfold uHat
  refine WP.seq (WP.mono (ddCall_okL K.dd L₀ (d := L.du) rbx_na hdd K.du.2) fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L₀.post hP₁.b (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L)
  rw [← hP₁.pa rbx_cs] at hp₁
  refine WP.mono (nttAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_
  have hk := h.keep W hp (PPost.app hP₁ hP₂ (by simp [calleeSaved])) hrc
  refine ⟨hk.dc, hk.r15, fun k hk' => ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  rcases (by omega : k < i ∨ k = i) with hk' | rfl
  · exact hk.u k hk'
  · rw [hp₁.2, ← hP₂.pa rbx_cs, VG.Proof.MlKem.X86_64.Decaps.slice_of h.dc.c (VG.Proof.MlKem.X86_64.Decaps.uSlice_le L hi)] at hp₂
    exact hp₂

theorem u_tr {A : Arith} (hA : ArithOk A) {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) {i : Nat}
    (hi : i < L.k) : RelCT isa (VG.Proof.MlKem.X86_64.Decaps.R L (VG.Proof.MlKem.X86_64.Decaps.DR L i 0)) (uHat L A i) fun _ _ => True := by
  have hc := W.u i hi
  simp only [VG.Proof.MlKem.X86_64.Decaps.uChk, Bool.and_eq_true] at hc
  obtain ⟨⟨hdd, hic⟩, _⟩ := hc
  unfold uHat
  exact VG.Proof.MlKem.X86_64.rel2_of (Q := fun x y => LRel (VG.Proof.MlKem.X86_64.Decaps.dcR L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) x y ∧ True ∧ True)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS i))) (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L)
      (RelCT.mono (ddCall_trL K.dd (d := L.du) rbx_na hdd K.du.2) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx _ => WP.mono (ddCall_okL K.dd Lx (d := L.du) rbx_na hdd K.du.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩) (nttAt_tr hA hic))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlKem.X86_64.Decaps.dc_lrel W p₁ p₂ pub h₁.dc h₂.dc, trivial, trivial⟩

/-! ## `ŝ` -/

theorem s_ok {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.decapsK L).pre σ) {i : Nat} (hi : i < L.k) {s : State}
    (h : VG.Proof.MlKem.X86_64.Decaps.DR L L.k i σ s) : WP isa (sHat L i) s (VG.Proof.MlKem.X86_64.Decaps.DR L L.k (i + 1) σ) := by
  have hc := W.s i hi
  simp only [VG.Proof.MlKem.X86_64.Decaps.sChk, Bool.and_eq_true] at hc
  have L₀ := h.dc.lay W hp
  refine WP.mono (dec12At_okL L₀ rbx_na hc.1) fun s' ⟨hP, hq⟩ => ?_
  have hk := h.keep W hp hP hc.2
  refine ⟨hk.dc, hk.r15, hk.u, fun k hk' => ?_⟩
  rcases (by omega : k < i ∨ k = i) with hk' | rfl
  · exact hk.sh k hk'
  · rw [hP.pa rbx_cs]
    rw [VG.Proof.MlKem.X86_64.Decaps.slice_of h.dc.dk (show 384 * k + 384 ≤ L.dkLen by simp only [Kem.dkLen, Params.dkLen, Kem.k] at hi ⊢; omega)]
      at hq
    rw [dcS, KPke.dkPke, slice_take _ (show 384 * k + 384 ≤ 384 * L.p.k by simp only [Kem.k] at hi; omega)]
    exact hq

theorem s_tr {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {i : Nat} (hi : i < L.k) : RelCT isa (VG.Proof.MlKem.X86_64.Decaps.R L (VG.Proof.MlKem.X86_64.Decaps.DR L L.k i)) (sHat L i) fun _ _ => True := by
  have hc := W.s i hi
  simp only [VG.Proof.MlKem.X86_64.Decaps.sChk, Bool.and_eq_true] at hc
  exact VG.Proof.MlKem.X86_64.rel2_of (dec12At_trL rbx_na hc.1) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlKem.X86_64.Decaps.dc_lrel W p₁ p₂ pub h₁.dc h₂.dc

/-! ## `m'` -/

/-- After K-PKE.Decrypt: `m'` at `M`. -/
structure DM (L : Kem) (σ s : State) : Prop where
  dc : VG.Proof.MlKem.X86_64.Decaps.DC L σ s
  r15 : s.gpr .r15 = 1
  m : bytesAt s.mem (pa s (sc oM)) 32 = KPke.decM L.p (VG.Proof.MlKem.X86_64.Decaps.dcDk L σ) (VG.Proof.MlKem.X86_64.Decaps.dcC L σ)

/-- The rest of `decrypt`. -/
abbrev tail (L : Kem) (A : Arith) : Prog isa :=
  .seq (dotN A (fun j => pS (L.k + j)) pS L.k) (.seq (nttInvAt A (pS 15))
    (.seq (L.ddAt (.r14, 32 * L.du * L.k) L.dv (pS 16)) (.seq (subAt (pS 16) (pS 15)) (ceAt (pS 16) 1 (sc oM)))))

theorem tail_ok {A : Arith} (hA : ArithOk A) {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd)
    {σ : State} (hp : (VG.Proof.MlKem.X86_64.decapsK L).pre σ) {s : State} (h : VG.Proof.MlKem.X86_64.Decaps.DR L L.k L.k σ s) : WP isa (VG.Proof.MlKem.X86_64.Decaps.tail L A) s (VG.Proof.MlKem.X86_64.Decaps.DM L σ) := by
  have hc := W.tail
  simp only [VG.Proof.MlKem.X86_64.Decaps.tailChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hdd⟩, hk15⟩, hac⟩, htw⟩, hkc⟩, hk₂⟩ := hc
  have L₀ := h.dc.lay W hp
  refine WP.seq (WP.mono (dotN_ok hA (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L) W.k.1 (dotChk_spec hdc) L₀ (a := dcS (KPke.dkPke L.p (VG.Proof.MlKem.X86_64.Decaps.dcDk L σ)))
    (b := fun i => ntt (KPke.dcU L.p (VG.Proof.MlKem.X86_64.Decaps.dcC L σ) i)) (fun k hk => h.sh k hk) (fun k hk => h.u k hk))
    fun s₁ ⟨hP₁, hp₁⟩ => ?_)
  have L₁ := L₀.post hP₁.b (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L)
  rw [← hP₁.pa rbx_cs] at hp₁
  refine WP.seq (WP.mono (nttInvAt_ok hA L₁ hic hp₁.1) fun s₂ ⟨hP₂, hp₂⟩ => ?_)
  have L₂ := L₁.post hP₂.b (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L)
  rw [hp₁.2, ← hP₂.pa rbx_cs] at hp₂
  refine WP.seq (WP.mono (ddCall_okL K.dd L₂ (d := L.dv) rbx_na hdd K.dv.2) fun s₃ ⟨hP₃, hp₃⟩ => ?_)
  have L₃ := L₂.post hP₃.b (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L)
  have hc₃ : bytesAt s₂.mem (pa s₂ (.r14, 32 * L.du * L.k)) (32 * L.dv) =
      ((VG.Proof.MlKem.X86_64.Decaps.dcC L σ).drop (32 * L.du * L.k)).take (32 * L.dv) := by
    have k₂ := h.dc.step W hp (PPost.app hP₁ hP₂ (by decide)).b hk₂
    exact VG.Proof.MlKem.X86_64.Decaps.slice_of k₂.c (by simp only [Kem.ctLen, Params.ctLen, Kem.du, Kem.dv, Kem.k]; rw [Nat.mul_add, ← Nat.mul_assoc])
  rw [hc₃, ← hP₃.pa rbx_cs] at hp₃
  have hq₃ := L₂.keepPoly hP₃.b hk15 hp₂
  refine WP.seq (WP.mono (subAt_ok L₃ rbx_na hac hp₃.1 hq₃.1) fun s₄ ⟨hP₄, hp₄⟩ => ?_)
  have L₄ := L₃.post hP₄.b (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L)
  rw [hp₃.2, hq₃.2, ← hP₄.pa rbx_cs] at hp₄
  refine WP.mono (ceCall_okL ceImpl L₄ (d := 1) rbx_na htw (by decide) hp₄.1) fun s₅ ⟨hP₅, hb₅⟩ => ?_
  have hP := PPost.app (PPost.app (PPost.app (PPost.app hP₁ hP₂ (by decide)) hP₃ (by decide)) hP₄ (by decide)) hP₅
    (by decide)
  refine ⟨h.dc.step W hp hP.b hkc, ?_, ?_⟩
  · rw [hP₅.cs .r15 (by decide), hP₄.cs .r15 (by decide), hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide),
      hP₁.cs .r15 (by decide), h.r15]
  · rw [hP₅.pa rbx_cs, hb₅, hp₄.2, KPke.decM, KPke.kpkeDecrypt_eq]
    rfl

theorem tail_tr {A : Arith} (hA : ArithOk A) {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) :
    RelCT isa (VG.Proof.MlKem.X86_64.Decaps.R L (VG.Proof.MlKem.X86_64.Decaps.DR L L.k L.k)) (VG.Proof.MlKem.X86_64.Decaps.tail L A) fun _ _ => True := by
  have hc := W.tail
  simp only [VG.Proof.MlKem.X86_64.Decaps.tailChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hdc, hic⟩, hdd⟩, hk15⟩, hac⟩, htw⟩, _⟩, _⟩ := hc
  refine VG.Proof.MlKem.X86_64.rel2_of (Q := fun x y => LRel (VG.Proof.MlKem.X86_64.Decaps.dcR L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) x y ∧ DotIn (fun j => pS (L.k + j)) pS L.k x ∧
      DotIn (fun j => pS (L.k + j)) pS L.k y) (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L)
    (RelCT.mono (dotN_tr hA (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L) W.k.1 (dotChk_spec hdc)) (fun _ _ h => h) fun _ _ h => h)
    (fun x Lx hx => WP.mono (dotN_ok hA (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L) W.k.1 (dotChk_spec hdc) Lx
      (a := fun k => polyAt x.mem (pa x (pS (L.k + k)))) (b := fun k => polyAt x.mem (pa x (pS k)))
      (fun k hk => ⟨(hx k hk).1, rfl⟩) (fun k hk => ⟨(hx k hk).2, rfl⟩))
      fun x' ⟨hP, hq⟩ => ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 15))) (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L) (nttInvAt_tr hA hic)
      (fun x Lx hx => WP.mono (nttInvAt_ok hA Lx hic hx) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 16)) ∧ Reduced x.mem (pa x (pS 15))) (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L)
      (RelCT.mono (ddCall_trL K.dd (d := L.dv) rbx_na hdd K.dv.2) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x Lx hx => WP.mono (ddCall_okL K.dd Lx (d := L.dv) rbx_na hdd K.dv.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1, Lx.keepRed hP.b hk15 hx⟩)
    (RelCT.seqL (J := fun x => Reduced x.mem (pa x (pS 16))) (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L) (subAt_tr rbx_na hac)
      (fun x Lx hx => WP.mono (subAt_ok Lx rbx_na hac hx.1 hx.2) fun x' ⟨hP, hq⟩ =>
        ⟨⟨_, hP.b⟩, by rw [hP.pa rbx_cs]; exact hq.1⟩)
      (ceCall_trL ceImpl (d := 1) rbx_na htw (by decide))))))
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => ⟨VG.Proof.MlKem.X86_64.Decaps.dc_lrel W p₁ p₂ pub h₁.dc h₂.dc,
      fun k hk => ⟨(h₁.sh k hk).1, (h₁.u k hk).1⟩, fun k hk => ⟨(h₂.sh k hk).1, (h₂.u k hk).1⟩⟩

end Decaps

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.DcTop`. -/
section

/-!
# ML-KEM on x86-64: decapsulation

After K-PKE.Decrypt (`DcDec.lean`): `G(m' ‖ h)` and `J(z ‖ c)` (`hashes_ok`),
K-PKE.Encrypt in the context `dcX` (which keeps `K'` and `K̄`), and the choice
of the key (`select_okD`). The function returns 1 with
`ML-KEM.Decaps_internal(dk, c)` in `key` if every `SampleNTT` succeeded within
280 iterations (`allOk`), and 0 otherwise (`kemDecaps_correct`); it leaks
only the pointers and `ρ` (`kemDecaps_ct`). Each parameter set's file moves
this to its shared contract.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

variable {L : Kem}

/-- `m'`, `(K', r') = G(m' ‖ h)`, `K̄ = J(z ‖ c)` and the encryption key of `σ`. -/
abbrev dcM' (L : Kem) (σ : State) : List Byte := KPke.decM L.p (VG.Proof.MlKem.X86_64.Decaps.dcDk L σ) (VG.Proof.MlKem.X86_64.Decaps.dcC L σ)
abbrev dcG (L : Kem) (σ : State) : List Byte × List Byte := G (VG.Proof.MlKem.X86_64.Decaps.dcM' L σ ++ KPke.dkH L.p (VG.Proof.MlKem.X86_64.Decaps.dcDk L σ))
abbrev dcKb (L : Kem) (σ : State) : List Byte := J (KPke.dkZ L.p (VG.Proof.MlKem.X86_64.Decaps.dcDk L σ) ++ VG.Proof.MlKem.X86_64.Decaps.dcC L σ)
abbrev dcEk (L : Kem) (σ : State) : List Byte := KPke.dkEk L.p (VG.Proof.MlKem.X86_64.Decaps.dcDk L σ)

/-- What `K-PKE.Encrypt` keeps: `DC`, `K'` at `G` and `K̄` at `KB`. -/
structure DCK (L : Kem) (σ s : State) : Prop where
  dc : VG.Proof.MlKem.X86_64.Decaps.DC L σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (VG.Proof.MlKem.X86_64.Decaps.dcG L σ).1
  kb : bytesAt s.mem (pa s (sc oKB)) 32 = VG.Proof.MlKem.X86_64.Decaps.dcKb L σ

theorem DCK.step (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.decapsK L).pre σ) {s s' : State} (h : VG.Proof.MlKem.X86_64.Decaps.DCK L σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : VG.Proof.MlKem.X86_64.Decaps.dckChk L ws = true) : VG.Proof.MlKem.X86_64.Decaps.DCK L σ s' := by
  simp only [VG.Proof.MlKem.X86_64.Decaps.dckChk, Bool.and_eq_true] at hc
  have L₀ := h.dc.lay W hp
  exact ⟨h.dc.step W hp hP hc.1.1, by rw [L₀.keepBytes hP hc.1.2]; exact h.k, by rw [L₀.keepBytes hP hc.2]; exact h.kb⟩

/-- The context of `K-PKE.Encrypt` in a run from `σ`. -/
def dcX (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) (σ : State) : VG.Proof.MlKem.X86_64.Ctx (VG.Proof.MlKem.X86_64.Decaps.dcR L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) where
  Out s := (VG.Proof.MlKem.X86_64.decapsK L).pre σ ∧ VG.Proof.MlKem.X86_64.Decaps.DCK L σ s
  chk := VG.Proof.MlKem.X86_64.Decaps.dckChk L
  bs := VG.Proof.MlKem.X86_64.Decaps.dcB_bases L
  lay h := h.2.dc.lay W h.1
  step h hP hc := ⟨h.1, h.2.step W h.1 hP hc⟩

/-- The context of `K-PKE.Encrypt` in any run. -/
def dcXA (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) : VG.Proof.MlKem.X86_64.Ctx (VG.Proof.MlKem.X86_64.Decaps.dcR L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) where
  Out s := ∃ σ, (VG.Proof.MlKem.X86_64.decapsK L).pre σ ∧ VG.Proof.MlKem.X86_64.Decaps.DCK L σ s
  chk := VG.Proof.MlKem.X86_64.Decaps.dckChk L
  bs := VG.Proof.MlKem.X86_64.Decaps.dcB_bases L
  lay := fun ⟨_, hp, h⟩ => h.dc.lay W hp
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step W hp hP hc⟩

/-! ## `G(m' ‖ h)` and `J(z ‖ c)` -/

theorem shakeSuffix31 : BitVec.ofNat 8 0x1f = Spec.Sha3.shakeSuffix := by decide

/-- The inputs of `K-PKE.Encrypt`, and `r15 = 1`. -/
abbrev EncI (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) (σ s : State) : Prop :=
  Enc.EIn L (VG.Proof.MlKem.X86_64.Decaps.dcX W σ) (.rbp, 384 * L.k) (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ) (VG.Proof.MlKem.X86_64.Decaps.dcM' L σ) (VG.Proof.MlKem.X86_64.Decaps.dcG L σ).2 s ∧ s.gpr .r15 = 1

theorem hashes_ok (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.decapsK L).pre σ) {s : State} (h : VG.Proof.MlKem.X86_64.Decaps.DM L σ s) :
    WP isa (VG.Impl.MlKem.X86_64.Decaps.hashes L) s (VG.Proof.MlKem.X86_64.Decaps.EncI W σ) := by
  have L₀ := h.dc.lay W hp
  have hdk : 768 * L.k + 96 = L.dkLen := rfl
  unfold VG.Impl.MlKem.X86_64.Decaps.hashes
  -- `G(m' ‖ h)`.
  refine WP.seq (WP.mono (hash_ok (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L) (ps := [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)]) (rate := 72)
    (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide) L₀) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.dc.step W hp hP₁.b W.h₁K
  have L₁ := k₁.lay W hp
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h.m,
    VG.Proof.MlKem.X86_64.Decaps.slice_of h.dc.dk (show 768 * L.k + 32 + 32 ≤ L.dkLen by omega), KeyGen.sha3Suffix6] at hb₁
  rw [← sha3_512_eq, ← hP₁.pa rbx_cs] at hb₁
  -- `J(z ‖ c)`.
  refine WP.mono (hash_ok (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L) (ps := [((.rbp, 768 * L.k + 64), 32), ((.r14, 0), L.ctLen)]) (rate := 136)
    (out := sc oKB) (len := 32) W.h₂ (show 0x1f < 256 by decide) L₁) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have k₂ := k₁.step W hp hP₂.b W.h₂K
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, k₁.c,
    VG.Proof.MlKem.X86_64.Decaps.slice_of k₁.dk (show 768 * L.k + 64 + 32 ≤ L.dkLen by omega), VG.Proof.MlKem.X86_64.Decaps.shakeSuffix31] at hb₂
  rw [← J_eq, ← hP₂.pa rbx_cs] at hb₂
  have hG : bytesAt s₂.mem (pa s₂ (sc oG)) 64 = Spec.Sha3.sha3_512 (VG.Proof.MlKem.X86_64.Decaps.dcM' L σ ++ KPke.dkH L.p (VG.Proof.MlKem.X86_64.Decaps.dcDk L σ)) := by
    rw [L₁.keepBytes hP₂.b W.h₂G]; exact hb₁
  have hK : bytesAt s₂.mem (pa s₂ (sc oG)) 32 = (VG.Proof.MlKem.X86_64.Decaps.dcG L σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hG]; rfl
  have hr : bytesAt s₂.mem (pa s₂ sigP) 32 = (VG.Proof.MlKem.X86_64.Decaps.dcG L σ).2 := by
    have e := bytesAt_drop s₂.mem (pa s₂ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₂.mem (pa s₂ (sc oG)) 64).drop 32 = bytesAt s₂.mem (pa s₂ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hG]; rfl
  refine ⟨⟨⟨hp, k₂, hK, hb₂⟩, VG.Proof.MlKem.X86_64.Decaps.slice_of k₂.dk (show 384 * L.k + (384 * L.k + 32) ≤ L.dkLen by omega), ?_, hr⟩, ?_⟩
  · rw [L₁.keepBytes hP₂.b W.h₂M, L₀.keepBytes hP₁.b W.h₁M]; exact h.m
  · rw [hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15]

/-! ## The key -/

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) (σ s : State) : Prop :=
  Enc.EOut L (VG.Proof.MlKem.X86_64.Decaps.dcX W σ) (.rbp, 384 * L.k) (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ) (VG.Proof.MlKem.X86_64.Decaps.dcM' L σ) (VG.Proof.MlKem.X86_64.Decaps.dcG L σ).2 s

/-- At the end: `r15` as `allOk`, and the key if it is 1. -/
structure DEnd (L : Kem) (σ s : State) : Prop where
  dc : VG.Proof.MlKem.X86_64.Decaps.DC L σ s
  r15 : s.gpr .r15 = if VG.Proof.MlKem.X86_64.allOk L.k (Enc.rhoE L (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ)) (L.k * L.k) then 1 else 0
  key : VG.Proof.MlKem.X86_64.allOk L.k (Enc.rhoE L (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ)) (L.k * L.k) → bytesAt s.mem (pa s (.r12, 0)) 32 =
    if VG.Proof.MlKem.X86_64.Decaps.dcC L σ = KPke.ct L.p (VG.Proof.MlKem.X86_64.aHat (Enc.rhoE L (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ))) (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ) (VG.Proof.MlKem.X86_64.Decaps.dcM' L σ) (VG.Proof.MlKem.X86_64.Decaps.dcG L σ).2 then (VG.Proof.MlKem.X86_64.Decaps.dcG L σ).1
    else VG.Proof.MlKem.X86_64.Decaps.dcKb L σ

theorem select_okD (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {σ : State} {s : State} (h : VG.Proof.MlKem.X86_64.Decaps.EncO W σ s) : WP isa (select L) s (VG.Proof.MlKem.X86_64.Decaps.DEnd L σ) := by
  have hp := h.out.1
  have k := h.out.2
  have L₀ := k.dc.lay W hp
  have cR : ∀ {p : Ptr} {l : Nat}, inB (VG.Proof.MlKem.X86_64.Decaps.dcB L) p l = true → InRegions (s.rd ++ s.wr) (pa s p) l := fun hi =>
    L₀.cR hi _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  obtain ⟨i1, i2, i3, i4, i5, s1, s2⟩ := W.sel
  refine WP.mono (VG.Proof.MlKem.X86_64.Decaps.select_ok W.ct.1 W.ct.2.1 W.ct.2.2 (cR i1) (cR i2) (cR i3) (cR i4)
    (L₀.cW i5 _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩) (L₀.disj s1) (L₀.disj s2))
    fun s' ⟨hP, hb⟩ => ?_
  refine ⟨k.dc.step W hp hP.b W.selK, by rw [hP.cs .r15 (by decide)]; exact h.r15, fun ho => ?_⟩
  rw [hP.pa KeyGen.r12_cs, hb]
  exact ite_congr (propext (by rw [k.dc.c, h.ct ho])) (fun _ => k.k) (fun _ => k.kb)

theorem DEnd.hin (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {σ s : State} (hp : (VG.Proof.MlKem.X86_64.decapsK L).pre σ) (h : VG.Proof.MlKem.X86_64.Decaps.DEnd L σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk =>
  (h.dc.lay W hp).cR (W.sv k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- The postcondition, from the key. -/
theorem post_of (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {σ s : State} (h : VG.Proof.MlKem.X86_64.Decaps.DEnd L σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : (VG.Proof.MlKem.X86_64.decapsK L).post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rdx := by
    rw [pa, h.dc.top.regs (.r12, .rdx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : VG.Proof.MlKem.X86_64.allOk L.k (Enc.rhoE L (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ)) (L.k * L.k)
  · refine .inl ⟨by rw [hr, h.r15, ifp ho]; rfl, minIterations, ?_⟩
    show decapsInternal L.p minIterations _ _ = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_some W.eta (a := VG.Proof.MlKem.X86_64.aHat (Enc.rhoE L (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ)))
      fun i hi j hj => VG.Proof.MlKem.X86_64.aHat_eq ho hi hj, Option.map_some, hm, ← e12, h.key ho]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := VG.Proof.MlKem.X86_64.not_allOk ho
    show decapsInternal L.p minIterations _ _ = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_none hi hj hn]
    rfl

theorem decrypt_ok {A : Arith} (hA : ArithOk A) (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) {σ : State}
    (hp : (VG.Proof.MlKem.X86_64.decapsK L).pre σ) {s : State} (h : VG.Proof.MlKem.X86_64.Decaps.DC L σ s) (h15 : s.gpr .r15 = 1) : WP isa (decrypt L A) s (VG.Proof.MlKem.X86_64.Decaps.DM L σ) := by
  unfold decrypt
  refine WP.seq (WP.mono (seqR_ok (I := fun k => VG.Proof.MlKem.X86_64.Decaps.DR L k 0 σ) L.k 0 (fun k _ hk s hs => VG.Proof.MlKem.X86_64.Decaps.u_ok hA W K hp (by omega) hs) s
    (DR.zero h h15)) fun s₁ h₁ => ?_)
  rw [Nat.zero_add] at h₁
  refine WP.seq (WP.mono (seqR_ok (I := fun k => VG.Proof.MlKem.X86_64.Decaps.DR L L.k k σ) L.k 0 (fun k _ hk s hs => VG.Proof.MlKem.X86_64.Decaps.s_ok W hp (by omega) hs) s₁ h₁)
    fun s₂ h₂ => ?_)
  rw [Nat.zero_add] at h₂
  exact VG.Proof.MlKem.X86_64.Decaps.tail_ok hA W K hp h₂

end Decaps

open Decaps in
theorem kemDecaps_correct (v : Sample4Impl) {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd)
    (hctl : ctlOk (kemDecaps L v.callee) = true) (σ : State) (hp : (VG.Proof.MlKem.X86_64.decapsK L).pre σ) :
    ∃ t s', Exec isa (kemDecaps L v.callee) σ t s' ∧ abiPreserved σ s' ∧ (VG.Proof.MlKem.X86_64.decapsK L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Decaps.pro_ok W hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Decaps.decrypt_ok v.arith W K hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Decaps.hashes_ok W hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (Enc.encrypt_ok v K W.k (C := VG.Proof.MlKem.X86_64.Decaps.dcX W σ) W.enc h₃.1 h₃.2) fun s₄ h₄ =>
          WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Decaps.select_okD W h₄) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.dc.top (h₅.hin W hp)) fun s₆ ⟨hr, hg, hm⟩ =>
              (⟨hg, VG.Proof.MlKem.X86_64.Decaps.post_of W h₅ hr hm⟩ : gprPreserved σ s₆ ∧ (VG.Proof.MlKem.X86_64.decapsK L).post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

/-! ## Constant time -/

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

variable {L : Kem}

theorem rho_pub {σ₁ σ₂ : State} (pub : (VG.Proof.MlKem.X86_64.decapsK L).pub σ₁ σ₂) : Enc.rhoE L (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ₁) = Enc.rhoE L (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ₂) := by
  rw [Enc.rhoE, Enc.rhoE, KPke.ekRho_dkEk, KPke.ekRho_dkEk]; exact pub.2.2.2.2.2

theorem decrypt_tr {A : Arith} (hA : ArithOk A) (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) :
    RelCT isa (VG.Proof.MlKem.X86_64.Decaps.R L fun σ s => VG.Proof.MlKem.X86_64.Decaps.DC L σ s ∧ s.gpr .r15 = 1) (decrypt L A) fun _ _ => True := by
  unfold decrypt
  refine RelCT.seq (RelCT.mono (seqR_tr (R := fun k => VG.Proof.MlKem.X86_64.Decaps.R L (VG.Proof.MlKem.X86_64.Decaps.DR L k 0)) L.k 0
    fun k _ hk => relInv (fun σ s hp hs => VG.Proof.MlKem.X86_64.Decaps.u_ok hA W K hp (by omega) hs) (VG.Proof.MlKem.X86_64.Decaps.u_tr hA W K (by omega)))
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, DR.zero h₁.1 h₁.2, DR.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k => VG.Proof.MlKem.X86_64.Decaps.R L (VG.Proof.MlKem.X86_64.Decaps.DR L L.k k)) L.k 0
    fun k _ hk => relInv (fun σ s hp hs => VG.Proof.MlKem.X86_64.Decaps.s_ok W hp (by omega) hs) (VG.Proof.MlKem.X86_64.Decaps.s_tr W (by omega))) ?_
  rw [Nat.zero_add]
  exact VG.Proof.MlKem.X86_64.Decaps.tail_tr hA W K

theorem hashes_trL (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) : RelCT isa (LRel (VG.Proof.MlKem.X86_64.Decaps.dcR L) (VG.Proof.MlKem.X86_64.Decaps.dcW L)) (VG.Impl.MlKem.X86_64.Decaps.hashes L) fun _ _ => True := by
  unfold VG.Impl.MlKem.X86_64.Decaps.hashes
  exact RelCT.seq (LRel.step (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L) (hash_tr (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L) (ps := [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)])
      (rate := 72) (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L) (ps := [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)]) (rate := 72) (out := sc oG)
        (len := 64) W.h₁ (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (hash_tr (VG.Proof.MlKem.X86_64.Decaps.dcB_bases L) (ps := [((.rbp, 768 * L.k + 64), 32), ((.r14, 0), L.ctLen)]) (rate := 136) (out := sc oKB)
      (len := 32) W.h₂ (show 0x1f < 256 by decide))

theorem hashes_tr (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) : RelCT isa (VG.Proof.MlKem.X86_64.Decaps.R L (VG.Proof.MlKem.X86_64.Decaps.DM L)) (VG.Impl.MlKem.X86_64.Decaps.hashes L) fun _ _ => True :=
  VG.Proof.MlKem.X86_64.rel2_of (VG.Proof.MlKem.X86_64.Decaps.hashes_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlKem.X86_64.Decaps.dc_lrel W p₁ p₂ pub h₁.dc h₂.dc

theorem EIn.any {W : VG.Proof.MlKem.X86_64.Decaps.DcWf L} {σ : State} {E : Ptr} {ek m r : List Byte} {s : State}
    (h : Enc.EIn L (VG.Proof.MlKem.X86_64.Decaps.dcX W σ) E ek m r s) : Enc.EIn L (VG.Proof.MlKem.X86_64.Decaps.dcXA W) E ek m r s :=
  ⟨⟨σ, h.out⟩, h.ek, h.m, h.r⟩

theorem encrypt_tr (v : Sample4Impl) (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) :
    RelCT isa (VG.Proof.MlKem.X86_64.Decaps.R L (VG.Proof.MlKem.X86_64.Decaps.EncI W)) (encrypt L v.callee (.rbp, 384 * L.k)) fun _ _ => True := by
  obtain ⟨_, rhoT⟩ := W.rhoT
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (VG.Proof.MlKem.X86_64.Decaps.dcR L) (VG.Proof.MlKem.X86_64.Decaps.dcW L) x y ∧
      Enc.EIρ L (VG.Proof.MlKem.X86_64.Decaps.dcXA W) (.rbp, 384 * L.k) ρ x ∧ Enc.EIρ L (VG.Proof.MlKem.X86_64.Decaps.dcXA W) (.rbp, 384 * L.k) ρ y) (Q := fun _ _ => True)
      fun ρ => RelCT.mono (Enc.encrypt_tr v K W.toKemWf (C := VG.Proof.MlKem.X86_64.Decaps.dcXA W) W.enc rhoT (ρ := ρ)) (fun _ _ h => h)
        fun _ _ _ => trivial) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  have i₁ : Enc.EIρ L (VG.Proof.MlKem.X86_64.Decaps.dcXA W) (.rbp, 384 * L.k) (Enc.rhoE L (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ₁)) x := ⟨_, _, _, rfl, EIn.any h₁.1, h₁.2⟩
  have i₂ : Enc.EIρ L (VG.Proof.MlKem.X86_64.Decaps.dcXA W) (.rbp, 384 * L.k) (Enc.rhoE L (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ₁)) y :=
    ⟨_, _, _, (VG.Proof.MlKem.X86_64.Decaps.rho_pub pub).symm, EIn.any h₂.1, h₂.2⟩
  exact ⟨Enc.rhoE L (VG.Proof.MlKem.X86_64.Decaps.dcEk L σ₁), VG.Proof.MlKem.X86_64.Decaps.dc_lrel W p₁ p₂ pub h₁.1.out.2.dc h₂.1.out.2.dc, i₁, i₂⟩

theorem select_tr (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) : RelCT isa (VG.Proof.MlKem.X86_64.Decaps.R L (VG.Proof.MlKem.X86_64.Decaps.EncO W)) (select L) fun _ _ => True := by
  obtain ⟨_, selT⟩ := W.selT
  exact VG.Proof.MlKem.X86_64.rel2_of (Q := LRel (VG.Proof.MlKem.X86_64.Decaps.dcR L) (VG.Proof.MlKem.X86_64.Decaps.dcW L)) (taintRel [.rbx, .r12, .r14] (fun _ _ h =>
    fa3 (h.eq (p := sc 0) (l := 1) W.inBs.1) (h.eq (p := (.r12, 0)) (l := 1) W.inBs.2.1)
      (h.eq (p := (.r14, 0)) (l := 1) W.inBs.2.2)) selT)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlKem.X86_64.Decaps.dc_lrel W p₁ p₂ pub h₁.out.2.dc h₂.out.2.dc

theorem pro_tr : RelCT isa (VG.Proof.MlKem.X86_64.Decaps.R L fun σ s => s = σ) (.block VG.Impl.MlKem.X86_64.Decaps.pro) fun _ _ => True :=
  taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa4 pub.2.2.2.1 pub.1 pub.2.1 pub.2.2.1) (by taint_decide)

theorem epi_tr : RelCT isa (VG.Proof.MlKem.X86_64.Decaps.R L (VG.Proof.MlKem.X86_64.Decaps.DEnd L)) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.dc.top.regs (.rbx, .rcx) (by decide), h₂.dc.top.regs (.rbx, .rcx) (by decide), pub.2.2.2.1])
    (by taint_decide)

end Decaps

open Decaps in
theorem kemDecaps_ct (v : Sample4Impl) {L : Kem} (W : VG.Proof.MlKem.X86_64.Decaps.DcWf L) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) :
    ConstantTime isa (VG.Proof.MlKem.X86_64.decapsK L).pre (VG.Proof.MlKem.X86_64.decapsK L).pub (kemDecaps L v.callee) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemDecaps
  refine RelCT.seq (relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.Decaps.DC L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact VG.Proof.MlKem.X86_64.Decaps.pro_ok W hp) VG.Proof.MlKem.X86_64.Decaps.pro_tr) ?_
  refine RelCT.seq (relInv (I' := VG.Proof.MlKem.X86_64.Decaps.DM L) (fun σ s hp hs => VG.Proof.MlKem.X86_64.Decaps.decrypt_ok v.arith W K hp hs.1 hs.2)
    (VG.Proof.MlKem.X86_64.Decaps.decrypt_tr v.arith W K)) ?_
  refine RelCT.seq (relInv (I' := VG.Proof.MlKem.X86_64.Decaps.EncI W) (fun σ s hp hs => VG.Proof.MlKem.X86_64.Decaps.hashes_ok W hp hs) (VG.Proof.MlKem.X86_64.Decaps.hashes_tr W)) ?_
  refine RelCT.seq (relInv (I' := VG.Proof.MlKem.X86_64.Decaps.EncO W) (fun σ s _ hs => Enc.encrypt_ok v K W.k (C := VG.Proof.MlKem.X86_64.Decaps.dcX W σ) W.enc hs.1 hs.2)
    (VG.Proof.MlKem.X86_64.Decaps.encrypt_tr v W K)) ?_
  refine RelCT.seq (relInv (I' := VG.Proof.MlKem.X86_64.Decaps.DEnd L) (fun σ s _ hs => VG.Proof.MlKem.X86_64.Decaps.select_okD W hs) (VG.Proof.MlKem.X86_64.Decaps.select_tr W)) ?_
  exact RelCT.mono VG.Proof.MlKem.X86_64.Decaps.epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.EcBase`. -/
section

/-!
# ML-KEM on x86-64: encapsulation, its contract, layout, entry and hashes

For a parameter set `L`: the contract the proof is written against
(`encapsK L`, which the shared contract implies), the layout of the
function's buffers (`ek` and `m` in `r14` and `rbp`, which may overlap each
other; `scratch`, `key`, `ct` in `rbx`, `r12`, `r13`), what holds throughout
(`EC`: `Top`, and `ek` and `m` at their pointers), the checks of the layout
every piece needs (`EcWf L`), the prologue, `H(ek)` and `G(m ‖ H(ek))`
(`hashes_ok`), and the context `K-PKE.Encrypt` runs in (`ecC`, which also
keeps `K`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- `kemEncaps L (ek = rdi, m = rsi, key = rdx, ct = rcx, scratch = r8) -> eax`, with 32 bytes of stack. -/
def encapsK (L : Kem) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, L.ekLen⟩, ⟨s.gpr .rsi, 32⟩] ∧
    s.wr = [⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, L.ctLen⟩, ⟨s.gpr .r8, L.scr⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ⟨s.gpr .rdx, 32⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ⟨s.gpr .rcx, L.ctLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ⟨s.gpr .r8, L.scr⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rdx, 32⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .rcx, L.ctLen⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 32⟩ ⟨s.gpr .r8, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, L.ctLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r8, L.scr⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, L.ctLen⟩ ⟨s.gpr .r8, L.scr⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 32⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, L.ctLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, L.scr⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdi, L.ekLen⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rsi, 32⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .rcx, L.ctLen⟩ ∧
    (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr .r8, L.scr⟩ ∧
    (s.gpr .rdi).toNat + L.ekLen ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + L.ctLen ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + L.scr ≤ 2 ^ 64
  post s s' :=
    Outcome (fun iters => encapsInternal L.p iters (bytesAt s.mem (s.gpr .rdi) L.ekLen)
      (bytesAt s.mem (s.gpr .rsi) 32)) ((s'.gpr .rax).setWidth 32)
      (bytesAt s'.mem (s.gpr .rdx) 32, bytesAt s'.mem (s.gpr .rcx) L.ctLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    ekRho L.p (bytesAt s₁.mem (s₁.gpr .rdi) L.ekLen) = ekRho L.p (bytesAt s₂.mem (s₂.gpr .rdi) L.ekLen)

namespace Encaps

open VG.Impl.MlKem.X86_64.Encaps

variable (L : Kem)

/-- The pointers the function keeps. -/
abbrev ecM : List (Reg × Reg) := [(.rbx, .r8), (.rbp, .rsi), (.r12, .rdx), (.r13, .rcx), (.r14, .rdi)]
/-- `ek` and `m`. -/
abbrev ecR : List (Reg × Nat) := [(.r14, L.ekLen), (.rbp, 32)]
/-- `scratch`, `key` and `ct`. -/
abbrev ecW : List (Reg × Nat) := [(.rbx, L.scr), (.r12, 32), (.r13, L.ctLen)]
abbrev ecB : List (Reg × Nat) := VG.Proof.MlKem.X86_64.Encaps.ecR L ++ VG.Proof.MlKem.X86_64.Encaps.ecW L

theorem ecB_bases : ∀ b ∈ VG.Proof.MlKem.X86_64.Encaps.ecB L, b.1 ∈ bases := by
  intro b hb; simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp [bases]

theorem ecM_bases : ∀ p ∈ VG.Proof.MlKem.X86_64.Encaps.ecM, p.1 ∈ bases := by decide

/-- A piece that writes `ws` keeps `EC`. -/
def ecChk (ws : List (Ptr × Nat)) : Bool :=
  topChk (VG.Proof.MlKem.X86_64.Encaps.ecB L) ws && keepB (VG.Proof.MlKem.X86_64.Encaps.ecB L) ws (.r14, 0) L.ekLen && keepB (VG.Proof.MlKem.X86_64.Encaps.ecB L) ws (.rbp, 0) 32

def eckChk (ws : List (Ptr × Nat)) : Bool := VG.Proof.MlKem.X86_64.Encaps.ecChk L ws && keepB (VG.Proof.MlKem.X86_64.Encaps.ecB L) ws (sc oG) 32

/-- The writes of the hashes and of the outputs. -/
abbrev hW₂ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), (sc oH, 32)]
abbrev hW₃ : List (Ptr × Nat) := [(sc 0, 200), (sc 200, 640), (sc oG, 64)]

/-- What every piece of encapsulation needs of the layout, evaluated for each parameter set. -/
structure EcWf : Prop extends VG.Proof.MlKem.X86_64.KemWf L where
  scr : 888 ≤ L.scr ∧ L.scr < 2 ^ 32
  small : ∀ b ∈ VG.Proof.MlKem.X86_64.Encaps.ecB L, b.2 < 2 ^ 32
  -- the hashes
  h₁ : copyChk (VG.Proof.MlKem.X86_64.Encaps.ecB L) (VG.Proof.MlKem.X86_64.Encaps.ecW L) (sc oM) (.rbp, 0) 32 = true
  h₁K : VG.Proof.MlKem.X86_64.Encaps.ecChk L [(sc oM, 32)] = true
  h₂ : hashChk (VG.Proof.MlKem.X86_64.Encaps.ecB L) (VG.Proof.MlKem.X86_64.Encaps.ecW L) [((.r14, 0), L.ekLen)] 136 (sc oH) 32 = true
  h₂K : VG.Proof.MlKem.X86_64.Encaps.ecChk L (VG.Proof.MlKem.X86_64.Encaps.hW₂) = true
  h₂M : keepB (VG.Proof.MlKem.X86_64.Encaps.ecB L) (VG.Proof.MlKem.X86_64.Encaps.hW₂) (sc oM) 32 = true
  h₃ : hashChk (VG.Proof.MlKem.X86_64.Encaps.ecB L) (VG.Proof.MlKem.X86_64.Encaps.ecW L) [(sc oM, 32), (sc oH, 32)] 72 (sc oG) 64 = true
  h₃K : VG.Proof.MlKem.X86_64.Encaps.ecChk L (VG.Proof.MlKem.X86_64.Encaps.hW₃) = true
  h₃M : keepB (VG.Proof.MlKem.X86_64.Encaps.ecB L) (VG.Proof.MlKem.X86_64.Encaps.hW₃) (sc oM) 32 = true
  enc : Enc.encChk L (VG.Proof.MlKem.X86_64.Encaps.ecB L) (VG.Proof.MlKem.X86_64.Encaps.ecW L) (VG.Proof.MlKem.X86_64.Encaps.eckChk L) (.r14, 0) = true
  -- the outputs
  o₁ : copyChk (VG.Proof.MlKem.X86_64.Encaps.ecB L) (VG.Proof.MlKem.X86_64.Encaps.ecW L) (.r12, 0) (sc oG) 32 = true
  o₁K : VG.Proof.MlKem.X86_64.Encaps.ecChk L [((.r12, 0), 32)] = true
  o₁C : keepB (VG.Proof.MlKem.X86_64.Encaps.ecB L) [((.r12, 0), 32)] (sc L.oCT) L.ctLen = true
  o₂ : copyChk (VG.Proof.MlKem.X86_64.Encaps.ecB L) (VG.Proof.MlKem.X86_64.Encaps.ecW L) (.r13, 0) (sc L.oCT) L.ctLen = true
  o₂K : VG.Proof.MlKem.X86_64.Encaps.ecChk L [((.r13, 0), L.ctLen)] = true
  o₂G : keepB (VG.Proof.MlKem.X86_64.Encaps.ecB L) [((.r13, 0), L.ctLen)] (.r12, 0) 32 = true
  sv : ∀ k < 6, inB (VG.Proof.MlKem.X86_64.Encaps.ecB L) (sc (oSV + 8 * k)) 8 = true
  -- constant time
  inBs : inB (VG.Proof.MlKem.X86_64.Encaps.ecB L) (sc 0) 1 = true ∧ inB (VG.Proof.MlKem.X86_64.Encaps.ecB L) (.r12, 0) 1 = true ∧ inB (VG.Proof.MlKem.X86_64.Encaps.ecB L) (.r13, 0) 1 = true ∧
    inB (VG.Proof.MlKem.X86_64.Encaps.ecB L) (.r14, 0) 1 = true
  hT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (copy (sc oM) (.rbp, 0) 32)
    h).isSome = true
  oT₁ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (copy (.r12, 0) (sc oG) 32)
    h).isSome = true
  oT₂ : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) (copy (.r13, 0) (sc L.oCT) L.ctLen)
    h).isSome = true
  rhoT : ∃ h, (taint.check (X86_64.Taint.ofRegs [.rbx, .r14]) (copy (sc oSB) (.r14, 0 + 384 * L.k) 32)
    h).isSome = true

section
variable {L : Kem} (W : VG.Proof.MlKem.X86_64.Encaps.EcWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.encapsK L).pre σ)
include W hp

theorem ecLay {s : State} (h : Top VG.Proof.MlKem.X86_64.Encaps.ecM σ s) : Lay (VG.Proof.MlKem.X86_64.Encaps.ecR L) (VG.Proof.MlKem.X86_64.Encaps.ecW L) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5⟩ :=
    hp
  have e1 : s.gpr .rbx = σ.gpr .r8 := h.regs (.rbx, .r8) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rsi := h.regs (.rbp, .rsi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rdx := h.regs (.r12, .rdx) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .rcx := h.regs (.r13, .rcx) (by decide)
  have e5 : s.gpr .r14 = σ.gpr .rdi := h.regs (.r14, .rdi) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine Lay.of W.small (pw5 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_)
    (fa5 ?_ ?_ ?_ ?_ ?_) (fa3 ?_ ?_ ?_) (fa5 ?_ ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, e5, h.rsp, retR]
  · exact fun hw => absurd hw (by decide)
  · exact fun _ => d3
  · exact fun _ => d1
  · exact fun _ => d2
  · exact fun _ => d6
  · exact fun _ => d4
  · exact fun _ => d5
  · exact fun _ => d8.symm
  · exact fun _ => d9.symm
  · exact fun _ => d7
  exacts [k1, k2, k5, k3, k4, n1, n2, n5, n3, n4,
    mem ⟨σ.gpr .rdi, L.ekLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rsi, 32⟩ (by rw [hrd]; simp),
    mem ⟨σ.gpr .r8, L.scr⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, 32⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .rcx, L.ctLen⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r1, r2, r5, r3, r4]

end

/-- `ek`, `m`, and `G(m ‖ H(ek))`. -/
abbrev ecEk (L : Kem) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) L.ekLen
abbrev ecMs (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) 32
abbrev ecG (L : Kem) (σ : State) : List Byte × List Byte := G (VG.Proof.MlKem.X86_64.Encaps.ecMs σ ++ H (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ))

/-- What holds throughout. -/
structure EC (L : Kem) (σ s : State) : Prop where
  top : Top VG.Proof.MlKem.X86_64.Encaps.ecM σ s
  ek : bytesAt s.mem (pa s (.r14, 0)) L.ekLen = VG.Proof.MlKem.X86_64.Encaps.ecEk L σ
  m : bytesAt s.mem (pa s (.rbp, 0)) 32 = VG.Proof.MlKem.X86_64.Encaps.ecMs σ

section
variable {L : Kem} (W : VG.Proof.MlKem.X86_64.Encaps.EcWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.encapsK L).pre σ)
include W hp

theorem EC.lay {s : State} (h : VG.Proof.MlKem.X86_64.Encaps.EC L σ s) : Lay (VG.Proof.MlKem.X86_64.Encaps.ecR L) (VG.Proof.MlKem.X86_64.Encaps.ecW L) s := VG.Proof.MlKem.X86_64.Encaps.ecLay W hp h.top

theorem EC.step {s s' : State} (h : VG.Proof.MlKem.X86_64.Encaps.EC L σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB s s' ws) (hc : VG.Proof.MlKem.X86_64.Encaps.ecChk L ws = true) : VG.Proof.MlKem.X86_64.Encaps.EC L σ s' := by
  simp only [VG.Proof.MlKem.X86_64.Encaps.ecChk, Bool.and_eq_true] at hc
  have L₀ := h.lay W hp
  exact ⟨h.top.step L₀ hP VG.Proof.MlKem.X86_64.Encaps.ecM_bases hc.1.1, by rw [L₀.keepBytes hP hc.1.2]; exact h.ek,
    by rw [L₀.keepBytes hP hc.2]; exact h.m⟩

end

/-- What `K-PKE.Encrypt` keeps: `EC`, and `K` at `G`. -/
structure ECK (L : Kem) (σ s : State) : Prop where
  ec : VG.Proof.MlKem.X86_64.Encaps.EC L σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (VG.Proof.MlKem.X86_64.Encaps.ecG L σ).1

theorem ECK.step {L : Kem} (W : VG.Proof.MlKem.X86_64.Encaps.EcWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.encapsK L).pre σ) {s s' : State} (h : VG.Proof.MlKem.X86_64.Encaps.ECK L σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : VG.Proof.MlKem.X86_64.Encaps.eckChk L ws = true) : VG.Proof.MlKem.X86_64.Encaps.ECK L σ s' := by
  simp only [VG.Proof.MlKem.X86_64.Encaps.eckChk, Bool.and_eq_true] at hc
  exact ⟨h.ec.step W hp hP hc.1, by rw [(h.ec.lay W hp).keepBytes hP hc.2]; exact h.k⟩

/-- The context of `K-PKE.Encrypt` in a run from `σ`. -/
def ecC {L : Kem} (W : VG.Proof.MlKem.X86_64.Encaps.EcWf L) (σ : State) : VG.Proof.MlKem.X86_64.Ctx (VG.Proof.MlKem.X86_64.Encaps.ecR L) (VG.Proof.MlKem.X86_64.Encaps.ecW L) where
  Out s := (VG.Proof.MlKem.X86_64.encapsK L).pre σ ∧ VG.Proof.MlKem.X86_64.Encaps.ECK L σ s
  chk := VG.Proof.MlKem.X86_64.Encaps.eckChk L
  bs := VG.Proof.MlKem.X86_64.Encaps.ecB_bases L
  lay h := h.2.ec.lay W h.1
  step h hP hc := ⟨h.1, h.2.step W h.1 hP hc⟩

/-- The context of `K-PKE.Encrypt` in any run. -/
def ecCA {L : Kem} (W : VG.Proof.MlKem.X86_64.Encaps.EcWf L) : VG.Proof.MlKem.X86_64.Ctx (VG.Proof.MlKem.X86_64.Encaps.ecR L) (VG.Proof.MlKem.X86_64.Encaps.ecW L) where
  Out s := ∃ σ, (VG.Proof.MlKem.X86_64.encapsK L).pre σ ∧ VG.Proof.MlKem.X86_64.Encaps.ECK L σ s
  chk := VG.Proof.MlKem.X86_64.Encaps.eckChk L
  bs := VG.Proof.MlKem.X86_64.Encaps.ecB_bases L
  lay := fun ⟨_, hp, h⟩ => h.ec.lay W hp
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step W hp hP hc⟩

theorem pro_eq : VG.Impl.MlKem.X86_64.Encaps.pro = [.store (at_ .r8 840) .rbx, .store (at_ .r8 848) .rbp, .store (at_ .r8 856) .r12,
    .store (at_ .r8 864) .r13, .store (at_ .r8 872) .r14, .store (at_ .r8 880) .r15, .mov .rbx (.reg .r8),
    .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .rcx), .mov .r14 (.reg .rdi),
    .mov32 .r15 (.imm 1)] := rfl

theorem pro_ok {L : Kem} (W : VG.Proof.MlKem.X86_64.Encaps.EcWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.encapsK L).pre σ) :
    WP isa (.block VG.Impl.MlKem.X86_64.Encaps.pro) σ fun s => VG.Proof.MlKem.X86_64.Encaps.EC L σ s ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, d8, d9, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4,
    n5⟩ := hp'
  have hsc := W.scr
  have hS : ⟨σ.gpr .r8, L.scr⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ L.scr → (⟨σ.gpr .r8, L.scr⟩ : Region).Contains (σ.gpr .r8 + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho (by omega)
  have w : ∀ o, o + 8 ≤ L.scr → InRegions σ.wr (σ.gpr .r8 + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [VG.Proof.MlKem.X86_64.Encaps.pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .r8 + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .r8 + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .r8 + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .rbp = σ.gpr .rsi ∧ s.gpr .r12 = σ.gpr .rdx ∧ s.gpr .r13 = σ.gpr .rcx ∧
    s.gpr .r14 = σ.gpr .rdi ∧ s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13, h14, h15⟩, k⟩ => ⟨?_, h15⟩
  have hf : Frame [⟨σ.gpr .r8, L.scr⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  have hek := W.small (.r14, L.ekLen) (by simp)
  refine ⟨⟨k.2.1, k.2.2, hsp, fa5 hbx hbp h12 h13 h14, fun j hj => ?_, ?_⟩, ?_, ?_⟩
  · simp only [pa, hbx, hm]
    exact stores_read σ.mem (σ.gpr .r8) (fun j => σ.gpr (savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using r5) (by decide)
  · rw [pa, h14, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d3) (by simp only at hek; omega)
  · rw [pa, hbp, add_ofNat_zero]
    exact bytesAt_frame hf (by simpa using d6) (by decide)

/-! ## `H(ek)` and `G(m ‖ H(ek))` -/

/-- The inputs of `K-PKE.Encrypt`, and `r15 = 1`. -/
abbrev EncI {L : Kem} (W : VG.Proof.MlKem.X86_64.Encaps.EcWf L) (σ s : State) : Prop :=
  Enc.EIn L (VG.Proof.MlKem.X86_64.Encaps.ecC W σ) (.r14, 0) (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ) (VG.Proof.MlKem.X86_64.Encaps.ecMs σ) (VG.Proof.MlKem.X86_64.Encaps.ecG L σ).2 s ∧ s.gpr .r15 = 1

theorem hashes_ok {L : Kem} (W : VG.Proof.MlKem.X86_64.Encaps.EcWf L) {σ : State} (hp : (VG.Proof.MlKem.X86_64.encapsK L).pre σ) {s : State} (h : VG.Proof.MlKem.X86_64.Encaps.EC L σ s)
    (h15 : s.gpr .r15 = 1) : WP isa (VG.Impl.MlKem.X86_64.Encaps.hashes L) s (VG.Proof.MlKem.X86_64.Encaps.EncI W σ) := by
  have L₀ := h.lay W hp
  unfold VG.Impl.MlKem.X86_64.Encaps.hashes
  -- `m` to `M`.
  refine WP.seq (WP.mono (copy_okL L₀ (dst := sc oM) (src := (.rbp, 0)) (n := 32) (by decide) W.h₁)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.step W hp hP₁.b W.h₁K
  have L₁ := k₁.lay W hp
  rw [h.m] at hb₁
  -- `H(ek)`.
  refine WP.seq (WP.mono (hash_ok (VG.Proof.MlKem.X86_64.Encaps.ecB_bases L) (ps := [((.r14, 0), L.ekLen)]) (rate := 136) (out := sc oH) (len := 32)
    W.h₂ (show 6 < 256 by decide) L₁) fun s₂ ⟨hP₂, hb₂⟩ => ?_)
  have k₂ := k₁.step W hp hP₂.b W.h₂K
  have L₂ := k₂.lay W hp
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, k₁.ek, KeyGen.sha3Suffix6] at hb₂
  rw [← H_eq, ← hP₂.pa rbx_cs] at hb₂
  have hM₂ : bytesAt s₂.mem (pa s₂ (sc oM)) 32 = VG.Proof.MlKem.X86_64.Encaps.ecMs σ := by
    rw [L₁.keepBytes hP₂.b W.h₂M, hP₁.pa rbx_cs, hb₁]
  -- `G(m ‖ H(ek))`.
  refine WP.mono (hash_ok (VG.Proof.MlKem.X86_64.Encaps.ecB_bases L) (ps := [(sc oM, 32), (sc oH, 32)]) (rate := 72) (out := sc oG) (len := 64)
    W.h₃ (show 6 < 256 by decide) L₂) fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have k₃ := k₂.step W hp hP₃.b W.h₃K
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, hM₂, hb₂, KeyGen.sha3Suffix6] at hb₃
  rw [← sha3_512_eq, ← hP₃.pa rbx_cs] at hb₃
  have hK : bytesAt s₃.mem (pa s₃ (sc oG)) 32 = (VG.Proof.MlKem.X86_64.Encaps.ecG L σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hb₃]; rfl
  have hr : bytesAt s₃.mem (pa s₃ sigP) 32 = (VG.Proof.MlKem.X86_64.Encaps.ecG L σ).2 := by
    have e := bytesAt_drop s₃.mem (pa s₃ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₃.mem (pa s₃ (sc oG)) 64).drop 32 = bytesAt s₃.mem (pa s₃ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hb₃]; rfl
  refine ⟨⟨⟨hp, k₃, hK⟩, k₃.ek, ?_, hr⟩, ?_⟩
  · rw [L₂.keepBytes hP₃.b W.h₃M]; exact hM₂
  · rw [hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h15]

end Encaps

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.EcTop`. -/
section

/-!
# ML-KEM on x86-64: encapsulation

The function, piece by piece: it returns 1 with `ML-KEM.Encaps_internal(ek,
m)` in `key` and `ct` if every `SampleNTT` succeeded within 280 iterations
(`allOk`), and 0 otherwise (`kemEncaps_correct`); it leaks only the pointers
and `ρ` (`kemEncaps_ct`). Each parameter set's file moves this to its shared
contract.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Encaps

open VG.Impl.MlKem.X86_64.Encaps

variable {L : Kem} (W : VG.Proof.MlKem.X86_64.Encaps.EcWf L)

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO (σ s : State) : Prop := Enc.EOut L (VG.Proof.MlKem.X86_64.Encaps.ecC W σ) (.r14, 0) (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ) (VG.Proof.MlKem.X86_64.Encaps.ecMs σ) (VG.Proof.MlKem.X86_64.Encaps.ecG L σ).2 s

/-- At the end: `r15` as `allOk`, `K` in `key`, and the ciphertext in `ct` if `r15` is 1. -/
structure ECEnd (L : Kem) (σ s : State) : Prop where
  ec : VG.Proof.MlKem.X86_64.Encaps.EC L σ s
  r15 : s.gpr .r15 = if VG.Proof.MlKem.X86_64.allOk L.k (Enc.rhoE L (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ)) (L.k * L.k) then 1 else 0
  key : bytesAt s.mem (pa s (.r12, 0)) 32 = (VG.Proof.MlKem.X86_64.Encaps.ecG L σ).1
  ct : VG.Proof.MlKem.X86_64.allOk L.k (Enc.rhoE L (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ)) (L.k * L.k) →
    bytesAt s.mem (pa s (.r13, 0)) L.ctLen = KPke.ct L.p (VG.Proof.MlKem.X86_64.aHat (Enc.rhoE L (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ))) (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ) (VG.Proof.MlKem.X86_64.Encaps.ecMs σ) (VG.Proof.MlKem.X86_64.Encaps.ecG L σ).2

include W

theorem out_ok {σ : State} {s : State} (h : VG.Proof.MlKem.X86_64.Encaps.EncO W σ s) : WP isa (out L) s (VG.Proof.MlKem.X86_64.Encaps.ECEnd L σ) := by
  have hp := h.out.1
  have L₀ := h.out.2.ec.lay W hp
  unfold out
  refine WP.seq (WP.mono (copy_okL L₀ (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) W.o₁)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.out.2.ec.step W hp hP₁.b W.o₁K
  have L₁ := k₁.lay W hp
  refine WP.mono (copy_okL L₁ (dst := (.r13, 0)) (src := sc L.oCT) (n := L.ctLen) (show Reg.rbx ≠ .rdi by decide) W.o₂)
    fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have k₂ := k₁.step W hp hP₂.b W.o₂K
  refine ⟨k₂, ?_, ?_, fun ho => ?_⟩
  · rw [hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide)]; exact h.r15
  · rw [L₁.keepBytes hP₂.b W.o₂G, hP₁.pa (by decide), hb₁]; exact h.out.2.k
  · rw [hP₂.pa (by decide), hb₂, L₀.keepBytes hP₁.b W.o₁C]; exact h.ct ho

theorem ECEnd.hin {σ s : State} (hp : (VG.Proof.MlKem.X86_64.encapsK L).pre σ) (h : VG.Proof.MlKem.X86_64.Encaps.ECEnd L σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk =>
  (h.ec.lay W hp).cR (W.sv k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- The postcondition, from the outputs. -/
theorem post_of {σ s : State} (h : VG.Proof.MlKem.X86_64.Encaps.ECEnd L σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : (VG.Proof.MlKem.X86_64.encapsK L).post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rdx := by
    rw [pa, h.ec.top.regs (.r12, .rdx) (by decide), add_ofNat_zero]
  have e13 : pa s (.r13, 0) = σ.gpr .rcx := by
    rw [pa, h.ec.top.regs (.r13, .rcx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : VG.Proof.MlKem.X86_64.allOk L.k (Enc.rhoE L (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ)) (L.k * L.k)
  · refine .inl ⟨by rw [hr, h.r15, ifp ho]; rfl, minIterations, ?_⟩
    show encapsInternal L.p minIterations _ _ = _
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_some W.eta (a := VG.Proof.MlKem.X86_64.aHat (Enc.rhoE L (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ)))
      fun i hi j hj => VG.Proof.MlKem.X86_64.aHat_eq ho hi hj, Option.map_some, hm, ← e12, ← e13, h.key, h.ct ho]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := VG.Proof.MlKem.X86_64.not_allOk ho
    show encapsInternal L.p minIterations _ _ = _
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_none hi hj hn]
    rfl

end Encaps

open Encaps in
theorem kemEncaps_correct (v : Sample4Impl) {L : Kem} (W : VG.Proof.MlKem.X86_64.Encaps.EcWf L) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd)
    (hctl : ctlOk (kemEncaps L v.callee) = true) (σ : State) (hp : (VG.Proof.MlKem.X86_64.encapsK L).pre σ) :
    ∃ t s', Exec isa (kemEncaps L v.callee) σ t s' ∧ abiPreserved σ s' ∧ (VG.Proof.MlKem.X86_64.encapsK L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Encaps.pro_ok W hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Encaps.hashes_ok W hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (Enc.encrypt_ok v K W.k (C := VG.Proof.MlKem.X86_64.Encaps.ecC W σ) W.enc h₂.1 h₂.2) fun s₃ h₃ =>
        WP.seq (WP.mono (VG.Proof.MlKem.X86_64.Encaps.out_ok W h₃) fun s₄ h₄ =>
          WP.mono (topEpi_ok h₄.ec.top (h₄.hin W hp)) fun s₅ ⟨hr, hg, hm⟩ =>
            (⟨hg, VG.Proof.MlKem.X86_64.Encaps.post_of W h₄ hr hm⟩ : gprPreserved σ s₅ ∧ (VG.Proof.MlKem.X86_64.encapsK L).post σ s₅)))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

/-! ## Constant time -/

namespace Encaps

open VG.Impl.MlKem.X86_64.Encaps

variable {L : Kem} (W : VG.Proof.MlKem.X86_64.Encaps.EcWf L)

abbrev R (L : Kem) (I : State → State → Prop) : State → State → Prop := Rel2 (VG.Proof.MlKem.X86_64.encapsK L).pre (VG.Proof.MlKem.X86_64.encapsK L).pub I

include W

theorem ec_lrel {σ₁ σ₂ x y : State} (p₁ : (VG.Proof.MlKem.X86_64.encapsK L).pre σ₁) (p₂ : (VG.Proof.MlKem.X86_64.encapsK L).pre σ₂)
    (pub : (VG.Proof.MlKem.X86_64.encapsK L).pub σ₁ σ₂) (h₁ : VG.Proof.MlKem.X86_64.Encaps.EC L σ₁ x) (h₂ : VG.Proof.MlKem.X86_64.Encaps.EC L σ₂ y) : LRel (VG.Proof.MlKem.X86_64.Encaps.ecR L) (VG.Proof.MlKem.X86_64.Encaps.ecW L) x y := by
  obtain ⟨e1, e2, e3, e4, e5, e6, _⟩ := pub
  refine ⟨h₁.lay W p₁, h₂.lay W p₂, fa5 ?_ ?_ ?_ ?_ ?_, by rw [h₁.top.rsp, h₂.top.rsp, e6]⟩
  · rw [h₁.top.regs (.r14, .rdi) (by decide), h₂.top.regs (.r14, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.rbp, .rsi) (by decide), h₂.top.regs (.rbp, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.rbx, .r8) (by decide), h₂.top.regs (.rbx, .r8) (by decide), e5]
  · rw [h₁.top.regs (.r12, .rdx) (by decide), h₂.top.regs (.r12, .rdx) (by decide), e3]
  · rw [h₁.top.regs (.r13, .rcx) (by decide), h₂.top.regs (.r13, .rcx) (by decide), e4]

omit W in
theorem rho_pub {σ₁ σ₂ : State} (pub : (VG.Proof.MlKem.X86_64.encapsK L).pub σ₁ σ₂) : Enc.rhoE L (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ₁) = Enc.rhoE L (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ₂) :=
  pub.2.2.2.2.2.2

/-- Code the taint analysis proves constant time from the pointers. -/
theorem trL {c : Prog isa} {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14]) c h).isSome = true) :
    RelCT isa (LRel (VG.Proof.MlKem.X86_64.Encaps.ecR L) (VG.Proof.MlKem.X86_64.Encaps.ecW L)) c fun _ _ => True :=
  taintRel [.rbx, .rbp, .r12, .r13, .r14] (fun _ _ h =>
    fa5 (h.eq (p := sc 0) (l := 1) W.inBs.1) (h.eq (p := (.rbp, 0)) (l := 1) rfl)
      (h.eq (p := (.r12, 0)) (l := 1) W.inBs.2.1) (h.eq (p := (.r13, 0)) (l := 1) W.inBs.2.2.1)
      (h.eq (p := (.r14, 0)) (l := 1) W.inBs.2.2.2)) ht

theorem hashes_trL : RelCT isa (LRel (VG.Proof.MlKem.X86_64.Encaps.ecR L) (VG.Proof.MlKem.X86_64.Encaps.ecW L)) (VG.Impl.MlKem.X86_64.Encaps.hashes L) fun _ _ => True := by
  unfold VG.Impl.MlKem.X86_64.Encaps.hashes
  obtain ⟨_, hT⟩ := W.hT
  refine RelCT.seq (LRel.step (VG.Proof.MlKem.X86_64.Encaps.ecB_bases L) (VG.Proof.MlKem.X86_64.Encaps.trL W hT) fun x Lx =>
      WP.mono (copy_okL Lx (dst := sc oM) (src := (.rbp, 0)) (n := 32) (by decide) W.h₁)
        fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (LRel.step (VG.Proof.MlKem.X86_64.Encaps.ecB_bases L) (hash_tr (VG.Proof.MlKem.X86_64.Encaps.ecB_bases L) (ps := [((.r14, 0), L.ekLen)]) (rate := 136)
      (out := sc oH) (len := 32) W.h₂ (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok (VG.Proof.MlKem.X86_64.Encaps.ecB_bases L) (ps := [((.r14, 0), L.ekLen)]) (rate := 136) (out := sc oH) (len := 32)
        W.h₂ (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (hash_tr (VG.Proof.MlKem.X86_64.Encaps.ecB_bases L) (ps := [(sc oM, 32), (sc oH, 32)]) (rate := 72) (out := sc oG) (len := 64) W.h₃
      (show 6 < 256 by decide)))

theorem hashes_tr : RelCT isa (VG.Proof.MlKem.X86_64.Encaps.R L fun σ s => VG.Proof.MlKem.X86_64.Encaps.EC L σ s ∧ s.gpr .r15 = 1) (VG.Impl.MlKem.X86_64.Encaps.hashes L) fun _ _ => True :=
  VG.Proof.MlKem.X86_64.rel2_of (VG.Proof.MlKem.X86_64.Encaps.hashes_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => VG.Proof.MlKem.X86_64.Encaps.ec_lrel W p₁ p₂ pub h₁.1 h₂.1

omit W in
theorem EIn.any {W : VG.Proof.MlKem.X86_64.Encaps.EcWf L} {σ : State} {E : Ptr} {ek m r : List Byte} {s : State} (h : Enc.EIn L (VG.Proof.MlKem.X86_64.Encaps.ecC W σ) E ek m r s) :
    Enc.EIn L (VG.Proof.MlKem.X86_64.Encaps.ecCA W) E ek m r s :=
  ⟨⟨σ, h.out⟩, h.ek, h.m, h.r⟩

theorem encrypt_tr (v : Sample4Impl) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) :
    RelCT isa (VG.Proof.MlKem.X86_64.Encaps.R L (VG.Proof.MlKem.X86_64.Encaps.EncI W)) (encrypt L v.callee (.r14, 0)) fun _ _ => True := by
  obtain ⟨_, rhoT⟩ := W.rhoT
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (VG.Proof.MlKem.X86_64.Encaps.ecR L) (VG.Proof.MlKem.X86_64.Encaps.ecW L) x y ∧ Enc.EIρ L (VG.Proof.MlKem.X86_64.Encaps.ecCA W) (.r14, 0) ρ x ∧
      Enc.EIρ L (VG.Proof.MlKem.X86_64.Encaps.ecCA W) (.r14, 0) ρ y) (Q := fun _ _ => True) fun ρ =>
      RelCT.mono (Enc.encrypt_tr v K W.toKemWf (C := VG.Proof.MlKem.X86_64.Encaps.ecCA W) W.enc rhoT (ρ := ρ)) (fun _ _ h => h)
        fun _ _ _ => trivial) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  have i₁ : Enc.EIρ L (VG.Proof.MlKem.X86_64.Encaps.ecCA W) (.r14, 0) (Enc.rhoE L (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ₁)) x := ⟨_, _, _, rfl, EIn.any h₁.1, h₁.2⟩
  have i₂ : Enc.EIρ L (VG.Proof.MlKem.X86_64.Encaps.ecCA W) (.r14, 0) (Enc.rhoE L (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ₁)) y :=
    ⟨_, _, _, (VG.Proof.MlKem.X86_64.Encaps.rho_pub pub).symm, EIn.any h₂.1, h₂.2⟩
  exact ⟨Enc.rhoE L (VG.Proof.MlKem.X86_64.Encaps.ecEk L σ₁), VG.Proof.MlKem.X86_64.Encaps.ec_lrel W p₁ p₂ pub h₁.1.out.2.ec h₂.1.out.2.ec, i₁, i₂⟩

theorem out_tr : RelCT isa (VG.Proof.MlKem.X86_64.Encaps.R L (VG.Proof.MlKem.X86_64.Encaps.EncO W)) (out L) fun _ _ => True := by
  refine VG.Proof.MlKem.X86_64.rel2_of (Q := LRel (VG.Proof.MlKem.X86_64.Encaps.ecR L) (VG.Proof.MlKem.X86_64.Encaps.ecW L)) ?_ fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    VG.Proof.MlKem.X86_64.Encaps.ec_lrel W p₁ p₂ pub h₁.out.2.ec h₂.out.2.ec
  unfold out
  obtain ⟨_, oT₁⟩ := W.oT₁
  obtain ⟨_, oT₂⟩ := W.oT₂
  exact RelCT.seq (LRel.step (VG.Proof.MlKem.X86_64.Encaps.ecB_bases L) (VG.Proof.MlKem.X86_64.Encaps.trL W oT₁) fun x Lx =>
      WP.mono (copy_okL Lx (dst := (.r12, 0)) (src := sc oG) (n := 32) (by decide) W.o₁)
        fun _ h => ⟨_, h.1⟩) (VG.Proof.MlKem.X86_64.Encaps.trL W oT₂)

omit W in
theorem pro_tr : RelCT isa (VG.Proof.MlKem.X86_64.Encaps.R L fun σ s => s = σ) (.block VG.Impl.MlKem.X86_64.Encaps.pro) fun _ _ => True :=
  taintRel [.r8, .rsi, .rdx, .rcx, .rdi] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa5 pub.2.2.2.2.1 pub.2.1 pub.2.2.1 pub.2.2.2.1 pub.1) (by taint_decide)

omit W in
theorem epi_tr : RelCT isa (VG.Proof.MlKem.X86_64.Encaps.R L (VG.Proof.MlKem.X86_64.Encaps.ECEnd L)) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.ec.top.regs (.rbx, .r8) (by decide), h₂.ec.top.regs (.rbx, .r8) (by decide), pub.2.2.2.2.1])
    (by taint_decide)

end Encaps

open Encaps in
theorem kemEncaps_ct (v : Sample4Impl) {L : Kem} (W : VG.Proof.MlKem.X86_64.Encaps.EcWf L) {wc wd : List Nat} (K : VG.Proof.MlKem.X86_64.KemCalls L wc wd) :
    ConstantTime isa (VG.Proof.MlKem.X86_64.encapsK L).pre (VG.Proof.MlKem.X86_64.encapsK L).pub (kemEncaps L v.callee) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemEncaps
  refine RelCT.seq (relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.Encaps.EC L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact VG.Proof.MlKem.X86_64.Encaps.pro_ok W hp) VG.Proof.MlKem.X86_64.Encaps.pro_tr) ?_
  refine RelCT.seq (relInv (I' := VG.Proof.MlKem.X86_64.Encaps.EncI W) (fun σ s hp hs => VG.Proof.MlKem.X86_64.Encaps.hashes_ok W hp hs.1 hs.2) (VG.Proof.MlKem.X86_64.Encaps.hashes_tr W)) ?_
  refine RelCT.seq (relInv (I' := VG.Proof.MlKem.X86_64.Encaps.EncO W) (fun σ s _ hs => Enc.encrypt_ok v K W.k (C := VG.Proof.MlKem.X86_64.Encaps.ecC W σ) W.enc hs.1 hs.2)
    (VG.Proof.MlKem.X86_64.Encaps.encrypt_tr W v K)) ?_
  refine RelCT.seq (relInv (I' := VG.Proof.MlKem.X86_64.Encaps.ECEnd L) (fun σ s _ hs => VG.Proof.MlKem.X86_64.Encaps.out_ok W hs) (VG.Proof.MlKem.X86_64.Encaps.out_tr W)) ?_
  exact RelCT.mono VG.Proof.MlKem.X86_64.Encaps.epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.Top768`. -/
section

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_keygen`, `vg_mlkem768_encaps` and `vg_mlkem768_decaps`

The proofs for any parameter set (`KgTop.lean`, `EcTop.lean`, `DcTop.lean`)
for ML-KEM-768 (`kem768`): its layout passes their checks, evaluated here,
it calls `vg_mlkem_compress_encode` and `vg_mlkem_decode_decompress` for its
widths, and the shared contracts imply the contracts the proofs are written
against.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem kemWf768 : VG.Proof.MlKem.X86_64.KemWf kem768 := by kem_wf

theorem kgWf768 : KeyGen.KgWf kem768 := by kem_wf VG.Proof.MlKem.X86_64.kemWf768
theorem ecWf768 : Encaps.EcWf kem768 := by kem_wf VG.Proof.MlKem.X86_64.kemWf768
theorem dcWf768 : Decaps.DcWf kem768 := by kem_wf VG.Proof.MlKem.X86_64.kemWf768

/-- The compressions it calls. -/
theorem calls768 : VG.Proof.MlKem.X86_64.KemCalls kem768 compressWidths compressWidths := ⟨ceImpl, ddImpl, by decide, by decide⟩

/-- States satisfying the shared contracts' preconditions. -/
def keyGenSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 64⟩]
  wr := [⟨0x2000, 1184⟩, ⟨0x3000, 2400⟩, ⟨0x10000, 32768⟩]

def encapsSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .r8 => 0x10000 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1184⟩, ⟨0x2000, 32⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x4000, 1088⟩, ⟨0x10000, 32768⟩]

def decapsSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x10000 | .rsp => 0x80000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 2400⟩, ⟨0x2000, 1088⟩]
  wr := [⟨0x3000, 32⟩, ⟨0x10000, 32768⟩]

theorem keyGen_verified (v : Sample4Impl) :
    Verified X86_64.target (kemKeyGen kem768 v.callee) (Spec.MlKem.keyGenContract X86_64.abi 32) :=
  Verified.of_correct (VG.Proof.MlKem.X86_64.kemKeyGen_correct v VG.Proof.MlKem.X86_64.kgWf768 (by s4_ctl v)) (VG.Proof.MlKem.X86_64.kemKeyGen_ct v VG.Proof.MlKem.X86_64.kgWf768)
    { pre := by sig_implies_pre [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, VG.Proof.MlKem.X86_64.keyGenK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      post := by sig_implies_post [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, VG.Proof.MlKem.X86_64.keyGenK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, VG.Proof.MlKem.X86_64.keyGenK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.keyGenContract, Spec.MlKem.keyGenSig, VG.Proof.MlKem.X86_64.keyGenK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768] [keyGenSat]
        using VG.Proof.MlKem.X86_64.keyGenSat }

theorem encaps_verified (v : Sample4Impl) :
    Verified X86_64.target (kemEncaps kem768 v.callee) (Spec.MlKem.encapsContract X86_64.abi 32) :=
  Verified.of_correct (VG.Proof.MlKem.X86_64.kemEncaps_correct v VG.Proof.MlKem.X86_64.ecWf768 VG.Proof.MlKem.X86_64.calls768 (by s4_ctl v)) (VG.Proof.MlKem.X86_64.kemEncaps_ct v VG.Proof.MlKem.X86_64.ecWf768 VG.Proof.MlKem.X86_64.calls768)
    { pre := by sig_implies_pre [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, VG.Proof.MlKem.X86_64.encapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      post := by sig_implies_post [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, VG.Proof.MlKem.X86_64.encapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, VG.Proof.MlKem.X86_64.encapsK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx, h8⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, h8, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.encapsContract, Spec.MlKem.encapsSig, VG.Proof.MlKem.X86_64.encapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768] [encapsSat]
        using VG.Proof.MlKem.X86_64.encapsSat }

theorem decaps_verified (v : Sample4Impl) :
    Verified X86_64.target (kemDecaps kem768 v.callee) (Spec.MlKem.decapsContract X86_64.abi 32) :=
  Verified.of_correct (VG.Proof.MlKem.X86_64.kemDecaps_correct v VG.Proof.MlKem.X86_64.dcWf768 VG.Proof.MlKem.X86_64.calls768 (by s4_ctl v)) (VG.Proof.MlKem.X86_64.kemDecaps_ct v VG.Proof.MlKem.X86_64.dcWf768 VG.Proof.MlKem.X86_64.calls768)
    { pre := by sig_implies_pre [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, VG.Proof.MlKem.X86_64.decapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      post := by sig_implies_post [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, VG.Proof.MlKem.X86_64.decapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, VG.Proof.MlKem.X86_64.decapsK, X86_64.abi, VG.X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
        exact ⟨hdi, hsi, hdx, hcx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.decapsContract, Spec.MlKem.decapsSig, VG.Proof.MlKem.X86_64.decapsK, X86_64.abi, VG.X86_64.argRegs, kem768, Kem.ekLen, Kem.dkLen, Kem.ctLen, Params.ekLen, Params.dkLen, Params.ctLen, mlKem768] [decapsSat]
        using VG.Proof.MlKem.X86_64.decapsSat }

end VG.Proof.MlKem.X86_64

end
