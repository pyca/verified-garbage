module

-- separate module: the two-run proofs of `forsSign`'s leaves, rebuilt only when they change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsLeaves
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTBase
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: `forsSign`'s leaves are constant time

A call of `thash4` on lanes, in two runs (`tcall_ct`): both have `scratch`
in `x19` and the same stack pointer, so its arguments are the same, and its
precondition holds in each. Four leaves (`leaf_ct`), in two runs at the same
leaf `J` of the same subtree `U2` of the same tree `V4`, with the same
signature `AU` (`LPre`, which every part of the body but the last keeps);
then the loop of leaves (`leaves_ct`), whose runs have the same counter.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.AArch64 (Layout thashArgs)
open VG.Proof.SlhDsa.AArch64.TreeBase
open VG.Proof.MlKem.AArch64 (Keep)

variable {p : Params}

/-! ## A call of `thash4` on lanes -/

/-- What `thashArgs` leaves. -/
structure TA (n : Nat) (S : Addr) (o st len : Nat) (t u : State) : Prop where
  x0 : u.gpr .x0 = at' S o
  x1 : u.gpr .x1 = BitVec.ofNat 64 st
  x2 : u.gpr .x2 = BitVec.ofNat 64 len
  x3 : u.gpr .x3 = at' S (o + n + 32)
  x4 : u.gpr .x4 = S
  sp : u.sp = t.sp
  wr : u.wr = t.wr
  other : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → u.gpr r = t.gpr r

theorem targs_wp (L : Layout) {o st len : Nat} (ho : o < 4096) (hst : st < 65536) (hlen : len < 65536)
    (hn : L.n + 32 < 4096) {S : Addr} {t : State} (h19 : t.gpr .x19 = S) :
    WP isa (.block (thashArgs L o st len)) t (TA L.n S o st len t) := by
  rw [Wots4.thashArgs_eq L ho]
  refine wp_addi (imm := o) ho fun t₂ e₂ => wp_movz fun t₃ e₃ => wp_movz fun t₄ e₄ =>
    wp_addi (imm := L.n + 32) hn fun t₅ e₅ => wp_mov fun t₆ e₆ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, by rw [e₆.sp, e₅.sp, e₄.sp, e₃.sp, e₂.sp], by rw [e₆.wr, e₅.wr, e₄.wr, e₃.wr, e₂.wr],
    fun r h0 h1 h2 h3 h4 => by rw [e₆.other _ h4, e₅.other _ h3, e₄.other _ h2, e₃.other _ h1, e₂.other _ h0]⟩
  · rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, h19]
  · rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.other _ (by decide), e₃.gpr, Wots4.movz_ofNat hst]
  · rw [e₆.other _ (by decide), e₅.other _ (by decide), e₄.gpr, Wots4.movz_ofNat hlen]
  · rw [e₆.other _ (by decide), e₅.gpr, e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, h19, at_add,
      Nat.add_assoc]
  · rw [e₆.gpr, e₅.other _ (by decide), e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), h19]

/-- A call of `thash4` on the lanes at `o`, in two runs with `scratch` in `x19`
and the same stack pointer. -/
theorem tcall_ct (T : Thash4Impl p.n) (name : String) (L : Layout) (hLn : L.n = p.n) (hn32 : p.n ≤ 32)
    {o st len : Nat}
    (hct : ∀ {P : State → State → Prop}, Agree P [.x19] → RelCT isa P (.block (thashArgs L o st len)) fun _ _ => True)
    (ho : 1024 ≤ o) (ho' : o < 4096) (hol : o + 4 * st ≤ 65536) (hlp : 0 < len) (hlm : len % 8 = 0)
    (hll : len ≤ st) (hno : p.n + 32 + p.n ≤ st) {S : Addr} (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    {A₁ A₂ : State → Prop} (h₁ : ∀ a, A₁ a → a.gpr .x19 = S ∧ (⟨S, 65536⟩ : Region) ∈ a.wr)
    (h₂ : ∀ b, A₂ b → b.gpr .x19 = S ∧ (⟨S, 65536⟩ : Region) ∈ b.wr)
    (hsp : ∀ a b, A₁ a → A₂ b → a.sp = b.sp) :
    RelCT isa (fun a b => A₁ a ∧ A₂ b) (Impl.SlhDsa.AArch64.thashCall L name T.code o st len) fun _ _ => True := by
  have hst : st < 65536 := by omega
  unfold Impl.SlhDsa.AArch64.thashCall
  refine relSeq (B₁ := fun u => ∃ a, A₁ a ∧ TA L.n S o st len a u) (B₂ := fun u => ∃ b, A₂ b ∧ TA L.n S o st len b u)
    (hct fun a b ⟨ha, hb⟩ => ⟨hsp a b ha hb, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [(h₁ a ha).1, (h₂ b hb).1]⟩)
    (fun a ha => WP.mono (targs_wp L ho' hst (by omega) (by omega) (h₁ a ha).1) fun u hu => ⟨a, ha, hu⟩)
    (fun b hb => WP.mono (targs_wp L ho' hst (by omega) (by omega) (h₂ b hb).1) fun u hu => ⟨b, hb, hu⟩) ?_
  refine RelCT.call T.verified.1 T.verified.2.1 [] (Wots4.t4wr S o st) fun u v ⟨⟨a, ha, hu⟩, ⟨b, hb, hv⟩⟩ => ?_
  have hu3 := hu.x3
  have hv3 := hv.x3
  rw [hLn] at hu3 hv3
  obtain ⟨c₁, w₁⟩ := Wots4.t4cov (s := u) (by rw [hu.wr]; exact (h₁ a ha).2) hol
  obtain ⟨c₂, w₂⟩ := Wots4.t4cov (s := v) (by rw [hv.wr]; exact (h₂ b hb).2) hol
  refine ⟨Wots4.t4pre hfit ho hol hu.x0 hu.x1 hu.x2 hu3 hu.x4 hlp hlm hll hno,
    Wots4.t4pre hfit ho hol hv.x0 hv.x1 hv.x2 hv3 hv.x4 hlp hlm hll hno, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, c₁, w₁, c₂, w₂⟩
  · rw [Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide), hu.x0, hv.x0]
  · rw [Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide), hu.x1, hv.x1]
  · rw [Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide), hu.x2, hv.x2]
  · rw [Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide), hu3, hv3]
  · rw [Wots4.ce_gpr _ _ (by decide), Wots4.ce_gpr _ _ (by decide), hu.x4, hv.x4]
  · simp only [State.withRegions_sp, State.callEntry_sp]; rw [hu.sp, hv.sp, hsp a b ha hb]

/-- A call of `thash4` on the lanes at `o`, from `scratch` in `x19`: what it keeps. -/
theorem tcall_wp (T : Thash4Impl p.n) (name : String) (L : Layout) (hLn : L.n = p.n) (hn32 : p.n ≤ 32)
    {o st len : Nat} (ho : 1024 ≤ o) (ho' : o < 4096) (hol : o + 4 * st ≤ 65536) (hlp : 0 < len)
    (hlm : len % 8 = 0) (hll : len ≤ st) (hno : p.n + 32 + p.n ≤ st) {S : Addr} {t : State}
    (h19 : t.gpr .x19 = S) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr) (hfit : S.toNat + 65536 ≤ 2 ^ 64) :
    WP isa (Impl.SlhDsa.AArch64.thashCall L name T.code o st len) t fun t' =>
      t'.sp = t.sp ∧ t'.wr = t.wr ∧ ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r := by
  unfold Impl.SlhDsa.AArch64.thashCall
  refine WP.seq (WP.mono (targs_wp L ho' (by omega) (by omega) (by omega) h19) fun u hu => ?_)
  have hu3 := hu.x3
  rw [hLn] at hu3
  refine Wots4.t4call_ok T name (by rw [hu.wr]; exact hw) hfit ho hol hu.x0 hu.x1 hu.x2 hu3 hu.x4 hlp hlm hll hno
    fun s' _ w sp g _ _ _ => ⟨by rw [sp, hu.sp], by rw [w, hu.wr], fun r hr h30 => ?_⟩
  rw [g r hr h30, hu.other r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)]

/-! ## Four leaves -/

/-- What every part of `leafBody` but the last needs and keeps: the leaf
`J` of the subtree `U2` of the tree `V4`, the signature `AU`, the tree's
index `idx`, and the stack pointer `sp`. -/
structure LPre (p : Params) (S AU : Addr) (V4 U2 J idx : Nat) (sp : BitVec 64) (u : State) : Prop where
  x19 : u.gpr .x19 = S
  kp : (u.gpr .x20).toNat < 2 ^ 32
  x21 : u.gpr .x21 = BitVec.ofNat 64 idx
  idx : idx < 2 ^ 32
  x24 : u.gpr .x24 = AU
  x25 : u.gpr .x25 = BitVec.ofNat 64 U2
  x26 : u.gpr .x26 = BitVec.ofNat 64 J
  x27 : u.gpr .x27 = BitVec.ofNat 64 V4
  sp : u.sp = sp
  scr : (⟨S, 65536⟩ : Region) ∈ u.wr
  fit : S.toNat + 65536 ≤ 2 ^ 64
  X : V4 + U2 + J + 4 < 2 ^ 32
  out : InRegions u.wr AU p.n
  d : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩

/-- The registers `LPre` reads. -/
abbrev lregs : List Reg := [.x19, .x20, .x21, .x24, .x25, .x26, .x27]

section
variable {S AU : Addr} {V4 U2 J idx : Nat} {sp : BitVec 64} {u v : State}

theorem LPre.of (h : LPre p S AU V4 U2 J idx sp u) (hg : ∀ r ∈ lregs, v.gpr r = u.gpr r) (hs : v.sp = u.sp)
    (hw : v.wr = u.wr) : LPre p S AU V4 U2 J idx sp v :=
  ⟨by rw [hg _ (by decide), h.x19], by rw [hg _ (by decide)]; exact h.kp, by rw [hg _ (by decide), h.x21], h.idx,
    by rw [hg _ (by decide), h.x24], by rw [hg _ (by decide), h.x25], by rw [hg _ (by decide), h.x26],
    by rw [hg _ (by decide), h.x27], by rw [hs, h.sp], by rw [hw]; exact h.scr, h.fit, h.X, by rw [hw]; exact h.out,
    h.d⟩

theorem LPre.keep {rs : List Reg} (h : LPre p S AU V4 U2 J idx sp u) (k : Keep rs u v)
    (hrs : ∀ r ∈ lregs, r ∉ rs := by decide) : LPre p S AU V4 U2 J idx sp v :=
  h.of (fun r hr => k.gpr r (hrs r hr)) k.sp k.wr

theorem LPre.acall (h : LPre p S AU V4 U2 J idx sp u) (k : ACall p S u v) : LPre p S AU V4 U2 J idx sp v :=
  h.of (fun r hr => k.cs r (by revert r; decide) (by revert r hr; decide)) k.sp k.wr

theorem LPre.agree {idx' : Nat} {v' : State} (h : LPre p S AU V4 U2 J idx sp u) (h' : LPre p S AU V4 U2 J idx' sp v')
    {rs : List Reg} (hrs : ∀ r ∈ rs, r ∈ [Reg.x19, .x24, .x25, .x26, .x27] := by decide) :
    u.sp = v'.sp ∧ ∀ r ∈ rs, u.gpr r = v'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp], fun r hr => ?_⟩
  have := hrs r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19]
  · rw [h.x24, h'.x24]
  · rw [h.x25, h'.x25]
  · rw [h.x26, h'.x26]
  · rw [h.x27, h'.x27]

end

/-- A call of `thash4` on the lanes `A`, in two runs with `LPre`. -/
theorem acall_ct (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (name : String) {S AU : Addr} {V4 U2 J idx₁ idx₂ : Nat}
    {sp : BitVec 64} :
    RelCT isa (fun a b => LPre p S AU V4 U2 J idx₁ sp a ∧ LPre p S AU V4 U2 J idx₂ sp b)
      (Impl.SlhDsa.AArch64.thashCall ⟨p.n, p.len⟩ name T.code Layout.oA Layout.strideA (2 * p.n + 32))
      fun _ _ => True := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have h16 := hz.n16
  by_cases hS : ∃ u, LPre p S AU V4 U2 J idx₁ sp u
  · obtain ⟨u₀, hu₀⟩ := hS
    exact tcall_ct T name ⟨p.n, p.len⟩ rfl hn32 (fun h => ct_argsA hz hA h) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by simp only [Layout.strideA]; omega) (by simp only [Layout.strideA]; omega) hu₀.fit
      (fun a h => ⟨h.x19, h.scr⟩) (fun b h => ⟨h.x19, h.scr⟩) fun a b h h' => by rw [h.sp, h'.sp]
  · exact RelCT.of_false fun a b ⟨h, _⟩ => hS ⟨a, h⟩

/-- Four leaves, in two runs at the same leaf of the same subtree. -/
theorem leaf_ct (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (name : String) {S AU : Addr} {V4 U2 J idx₁ idx₂ : Nat}
    {sp : BitVec 64} :
    RelCT isa (fun a b => LPre p S AU V4 U2 J idx₁ sp a ∧ LPre p S AU V4 U2 J idx₂ sp b)
      (Impl.SlhDsa.AArch64.Fors.leafBody ⟨p.n, p.len⟩ p.a name T.code) fun _ _ => True := by
  unfold Impl.SlhDsa.AArch64.Fors.leafBody
  refine relSeq (ct_lanes hz hA fun a b ⟨ha, hb⟩ => ha.agree hb)
    (fun a ha => WP.mono (blockA_ok hz ha.x19 ha.kp ha.x25 ha.x26 ha.x27 ha.X ha.scr) fun _ h => ha.keep h.keep)
    (fun b hb => WP.mono (blockA_ok hz hb.x19 hb.kp hb.x25 hb.x26 hb.x27 hb.X hb.scr) fun _ h => hb.keep h.keep) ?_
  refine relSeq (acall_ct hz hA T name) (fun a ha => acall_ok hz T name ha.x19 ha.scr ha.fit fun _ h => ha.acall h)
    (fun b hb => acall_ok hz T name hb.x19 hb.scr hb.fit fun _ h => hb.acall h) ?_
  refine relSeq (ct_cap hz hA fun a b ⟨ha, hb⟩ => ha.agree hb)
    (fun a ha => WP.mono (capB_ok hz ha.x19 ha.x21 ha.x24 ha.x25 ha.x26 (by have := ha.X; omega) ha.idx ha.scr
      ha.out ha.d) fun _ h => ha.keep h.keep)
    (fun b hb => WP.mono (capB_ok hz hb.x19 hb.x21 hb.x24 hb.x25 hb.x26 (by have := hb.X; omega) hb.idx hb.scr
      hb.out hb.d) fun _ h => hb.keep h.keep) ?_
  refine relSeq (acall_ct hz hA T name) (fun a ha => acall_ok hz T name ha.x19 ha.scr ha.fit fun _ h => ha.acall h)
    (fun b hb => acall_ok hz T name hb.x19 hb.scr hb.fit fun _ h => hb.acall h) ?_
  exact ct_out hz hA fun a b ⟨ha, hb⟩ => ha.agree hb

/-! ## The loop of leaves -/

section
variable {S AU : Addr} {V4 U2 idx : Nat} {pk a16 sk : List Byte} {t₀ : State}

/-- `LPre` from the loop's invariant. -/
theorem LI.lpre (h19 : t₀.gpr .x19 = S) (hKP : (t₀.gpr .x20).toNat < 2 ^ 32)
    (h21 : t₀.gpr .x21 = BitVec.ofNat 64 idx) (hidx : idx < 2 ^ 32) (h24 : t₀.gpr .x24 = AU)
    (h25 : t₀.gpr .x25 = BitVec.ofNat 64 U2) (h27 : t₀.gpr .x27 = BitVec.ofNat 64 V4)
    (hw : (⟨S, 65536⟩ : Region) ∈ t₀.wr) (hfit : S.toNat + 65536 ≤ 2 ^ 64)
    (hX : V4 + U2 + 2 ^ Impl.SlhDsa.AArch64.Fors.s p.a < 2 ^ 32) (hout : InRegions t₀.wr AU p.n)
    (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩) {kp m : Nat} {u : State}
    (h : LI p S AU pk a16 sk kp V4 U2 idx t₀ m u) :
    LPre p S AU V4 U2 (2 ^ Impl.SlhDsa.AArch64.Fors.s p.a - 4 * m) idx t₀.sp u := by
  obtain ⟨J, hJ, hm, hI⟩ := h
  have g := hI.cs
  rw [show 2 ^ Impl.SlhDsa.AArch64.Fors.s p.a - 4 * m = J by omega]
  exact ⟨by rw [g .x19 (by decide) (by decide) (by decide), h19],
    by rw [g .x20 (by decide) (by decide) (by decide)]; exact hKP, by rw [g .x21 (by decide) (by decide) (by decide), h21],
    hidx, by rw [g .x24 (by decide) (by decide) (by decide), h24], by rw [g .x25 (by decide) (by decide) (by decide), h25],
    hI.x26, by rw [g .x27 (by decide) (by decide) (by decide), h27], hI.sp, by rw [hI.wr]; exact hw, hfit,
    by omega, by rw [hI.wr]; exact hout, hd⟩

end

/-- The loop of leaves, in two runs of the same subtree of the same tree,
with the same signature and stack pointer. -/
theorem leaves_ct (hz : Sz p) (hA : As p) (T : Thash4Impl p.n) (name : String) {S AU : Addr} {V4 U2 idx₁ idx₂ : Nat}
    {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte} {t₁ t₂ : State}
    (h19₁ : t₁.gpr .x19 = S) (hKP₁ : (t₁.gpr .x20).toNat < 2 ^ 32) (h21₁ : t₁.gpr .x21 = BitVec.ofNat 64 idx₁)
    (hidx₁ : idx₁ < 2 ^ 32) (h24₁ : t₁.gpr .x24 = AU) (h25₁ : t₁.gpr .x25 = BitVec.ofNat 64 U2)
    (h27₁ : t₁.gpr .x27 = BitVec.ofNat 64 V4) (hw₁ : (⟨S, 65536⟩ : Region) ∈ t₁.wr) (hout₁ : InRegions t₁.wr AU p.n)
    (h19₂ : t₂.gpr .x19 = S) (hKP₂ : (t₂.gpr .x20).toNat < 2 ^ 32) (h21₂ : t₂.gpr .x21 = BitVec.ofNat 64 idx₂)
    (hidx₂ : idx₂ < 2 ^ 32) (h24₂ : t₂.gpr .x24 = AU) (h25₂ : t₂.gpr .x25 = BitVec.ofNat 64 U2)
    (h27₂ : t₂.gpr .x27 = BitVec.ofNat 64 V4) (hw₂ : (⟨S, 65536⟩ : Region) ∈ t₂.wr) (hout₂ : InRegions t₂.wr AU p.n)
    (hfit : S.toNat + 65536 ≤ 2 ^ 64) (hX : V4 + U2 + 2 ^ Impl.SlhDsa.AArch64.Fors.s p.a < 2 ^ 32)
    (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩) (hsp : t₁.sp = t₂.sp) (n : Nat) :
    RelCT isa (fun a b => LI p S AU pk₁ a₁ sk₁ (t₁.gpr .x20).toNat V4 U2 idx₁ t₁ n a ∧
        LI p S AU pk₂ a₂ sk₂ (t₂.gpr .x20).toNat V4 U2 idx₂ t₂ n b)
      (.loop (Impl.SlhDsa.AArch64.Fors.leafBody ⟨p.n, p.len⟩ p.a name T.code) (.nonzero .x .x9))
      fun a b => LS p S AU pk₁ a₁ sk₁ (t₁.gpr .x20).toNat V4 U2 idx₁ t₁ (2 ^ Impl.SlhDsa.AArch64.Fors.s p.a) a ∧
        LS p S AU pk₂ a₂ sk₂ (t₂.gpr .x20).toNat V4 U2 idx₂ t₂ (2 ^ Impl.SlhDsa.AArch64.Fors.s p.a) b :=
  relLoop (fun m => decide (m ≠ 1)) (fun m => m - 1)
    (fun m => RelCT.mono (leaf_ct hz hA T name (sp := t₁.sp))
      (fun a b ⟨ha, hb⟩ => ⟨LI.lpre h19₁ hKP₁ h21₁ hidx₁ h24₁ h25₁ h27₁ hw₁ hfit hX hout₁ hd ha,
        by have := LI.lpre h19₂ hKP₂ h21₂ hidx₂ h24₂ h25₂ h27₂ hw₂ hfit hX hout₂ hd hb; rw [← hsp] at this; exact this⟩)
      fun _ _ h => h)
    (leaves_step hz T name h19₁ hKP₁ h21₁ hidx₁ h24₁ h25₁ h27₁ hw₁ hfit hX hout₁ hd)
    (leaves_step hz T name h19₂ hKP₂ h21₂ hidx₂ h24₂ h25₂ h27₂ hw₂ hfit hX hout₂ hd) n

end VG.Proof.SlhDsa.AArch64.Fors
