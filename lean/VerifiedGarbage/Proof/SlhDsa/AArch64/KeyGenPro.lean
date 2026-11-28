module

-- separate module: the blocks of key generation, rebuilt only when they change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.Contracts
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Shake
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.SlhDsa.AArch64.Sz
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopShared
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopLanes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64: the blocks of key generation

`keygen(seeds = x0, sk = x1, pk = x2, scratch = x3)`
(`Impl.SlhDsa.AArch64.Shake.keyGen`) is a block, the call of `xmssTree` and
a block. The first (`proCode`) saves the caller's registers at `oTop`, keeps
`scratch`, `sk` and `pk` in `x19`–`x21`, copies `SK.seed`, `SK.prf` and
`PK.seed` to `oKeys`, writes `PK.seed` and the address of the top layer's
tree to every lane (`Env`) and sets up the arguments of the call (`pro_ok`,
`KPro`). The last (`tailCode`) copies the root the call left at `oMsg` to
`PK.root`, the keys out, and restores the caller's registers (`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.KeyGen

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout copyWords saveRegsAt restoreRegsAt movV lea)
open VG.Impl.SlhDsa.AArch64.Thash4 (mov)
open VG.Impl.SlhDsa.AArch64.Shake (topSaved seedLanes treeLanes writeKeys)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil)

/-! ## Copies of strings of `n` bytes -/

/-- The blocks of a `flatMap` over `range K` followed by `is`, one at a time. -/
theorem wp_flatMap {f : Nat → List Instr} {is : List Instr} {P : Nat → State → Prop} {Q : State → Prop} :
    ∀ (K : Nat) {s : State}, P 0 s →
      (∀ j < K, ∀ t (is' : List Instr), P j t → (∀ t', P (j + 1) t' → WP isa (.block is') t' Q) →
        WP isa (.block (f j ++ is')) t Q) →
      (∀ t, P K t → WP isa (.block is) t Q) →
      WP isa (.block ((List.range K).flatMap f ++ is)) s Q
  | 0, _, h0, _, k => by simpa using k _ h0
  | K + 1, _, h0, hs, k => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    exact wp_flatMap K h0 (fun j hj => hs j (by omega)) fun t ht => hs K (by omega) t is ht k

/-- After `c` of the copies of `K` strings of `n` bytes from `X + n c` to `D + (o + 32 c)`. -/
structure InI (n : Nat) (s : State) (D X : Addr) (o K c : Nat) (t : State) : Prop where
  keep : Keep [.x14] s t
  bytes : ∀ c' < c, bytesAt t.mem (D + BitVec.ofNat 64 (o + 32 * c')) n = bytesAt s.mem (X + BitVec.ofNat 64 (n * c')) n
  frame : Frame [⟨D + BitVec.ofNat 64 o, 32 * K⟩] s.mem t.mem

/-- `K ≤ 4` strings of `n` bytes from `xs + n c` (`xs` a register) to
`xd + o + 32 c`, regions apart. -/
theorem copyIn_ok {n : Nat} (hn : n ≤ 32) (h8 : n % 8 = 0) {s : State} {xd xs : Reg} (hd : xd ≠ .x14)
    (hs : xs ≠ .x14) {D X : Addr} (hD : s.gpr xd = D) (hX : s.gpr xs = X) {o K : Nat} (hK : K ≤ 4)
    (ho : o % 8 = 0 ∧ o + 32 * K ≤ 32768)
    (hw : InRegions s.wr (D + BitVec.ofNat 64 o) (32 * K)) (hr : InRegions (s.rd ++ s.wr) X (n * K))
    (hfo : D.toNat + o + 32 * K ≤ 2 ^ 64) (hfx : X.toNat + n * K ≤ 2 ^ 64)
    (hdis : Region.Disjoint ⟨X, n * K⟩ ⟨D + BitVec.ofNat 64 o, 32 * K⟩)
    {is : List Instr} {Q : State → Prop} (k : ∀ t, InI n s D X o K K t → WP isa (.block is) t Q) :
    WP isa (.block ((List.range K).flatMap (fun c => copyWords xd (o + 32 * c) xs (n * c) (n / 8)) ++ is)) s Q := by
  have h8n : 8 * (n / 8) = n := by omega
  have hnK : n * K ≤ 128 := Nat.mul_le_mul hn hK
  refine wp_flatMap (P := InI n s D X o K) K ⟨Keep.refl _ _, fun _ h => absurd h (by omega), Frame.refl _ _⟩
    (fun c hc t is' ht k' => ?_) k
  have hdt : t.gpr xd = D := by rw [ht.keep.get xd (by simpa using hd), hD]
  have hxt : t.gpr xs = X := by rw [ht.keep.get xs (by simpa using hs), hX]
  have hnc : n * c + n ≤ n * K := by
    have := Nat.mul_le_mul_left n (show c + 1 ≤ K by omega); rwa [Nat.mul_succ] at this
  have hsub : Region.Sub ⟨D + BitVec.ofNat 64 (o + 32 * c), n⟩ ⟨D + BitVec.ofNat 64 o, 32 * K⟩ :=
    Offset.sub D (by omega) (by omega)
  have hXs : Region.Sub ⟨X + BitVec.ofNat 64 (n * c), n⟩ ⟨X, n * K⟩ := Offset.sub_base X hnc
  refine copyWords_ok (t := xd) (sr := xs) (d₂ := o + 32 * c) (d₁ := n * c) (w := n / 8)
    ⟨hd, hs, ⟨Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero h8) c), by omega⟩, ⟨by omega, by omega⟩,
      by rw [ht.keep.rd, ht.keep.wr, hxt, h8n]; exact InRegions.sub hr hnc |>.elim (fun r ⟨hr', hc'⟩ => ⟨r, hr', hc'⟩) ,
      by
        rw [ht.keep.wr, hdt, h8n, ← addr_add]
        exact InRegions.sub hw (by omega),
      by rw [hdt, hxt, h8n]; exact (hdis.sub_left hXs).sub_right hsub |>.symm⟩ fun u ku fu bu => k' u ?_
  simp only [hdt, hxt, h8n] at fu bu
  have hcs : bytesAt u.mem (D + BitVec.ofNat 64 (o + 32 * c)) n = bytesAt s.mem (X + BitVec.ofNat 64 (n * c)) n := by
    rw [bu]
    exact bytesAt_frame ht.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hdis.sub_left hXs) (by omega)
  refine ⟨(ht.keep.trans ku).mono (by simp), fun c' hc' => ?_, ht.frame.trans (fu.sub fun r hr => ?_)⟩
  · by_cases e : c' = c
    · subst e; exact hcs
    · rw [bytesAt_frame fu (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint D (by omega) (by omega) (by omega)) (by omega)]
      exact ht.bytes c' (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, hsub⟩

/-- After `c` of the copies of `K` strings of `n` bytes from `S + (o + 32 c)` to `D + n c`. -/
structure OutI (n : Nat) (s : State) (S D : Addr) (o K c : Nat) (t : State) : Prop where
  keep : Keep [.x14] s t
  bytes : ∀ c' < c, bytesAt t.mem (D + BitVec.ofNat 64 (n * c')) n = bytesAt s.mem (S + BitVec.ofNat 64 (o + 32 * c')) n
  frame : Frame [⟨D, n * K⟩] s.mem t.mem

/-- `K ≤ 4` strings of `n` bytes from `xs + o + 32 c` to `xd + n c`, regions apart. -/
theorem copyOut_ok {n : Nat} (hn : n ≤ 32) (h8 : n % 8 = 0) {s : State} {xd xs : Reg} (hd : xd ≠ .x14)
    (hs : xs ≠ .x14) {D S : Addr} (hD : s.gpr xd = D) (hS : s.gpr xs = S) {o K : Nat} (hK : K ≤ 4)
    (ho : o % 8 = 0 ∧ o + 32 * K ≤ 32768)
    (hr : InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 o) (32 * K)) (hw : InRegions s.wr D (n * K))
    (hfo : S.toNat + o + 32 * K ≤ 2 ^ 64) (_hfd : D.toNat + n * K ≤ 2 ^ 64)
    (hdis : Region.Disjoint ⟨D, n * K⟩ ⟨S + BitVec.ofNat 64 o, 32 * K⟩)
    {is : List Instr} {Q : State → Prop} (k : ∀ t, OutI n s S D o K K t → WP isa (.block is) t Q) :
    WP isa (.block ((List.range K).flatMap (fun c => copyWords xd (n * c) xs (o + 32 * c) (n / 8)) ++ is)) s Q := by
  have h8n : 8 * (n / 8) = n := by omega
  have hnK : n * K ≤ 128 := Nat.mul_le_mul hn hK
  refine wp_flatMap (P := OutI n s S D o K) K ⟨Keep.refl _ _, fun _ h => absurd h (by omega), Frame.refl _ _⟩
    (fun c hc t is' ht k' => ?_) k
  have hdt : t.gpr xd = D := by rw [ht.keep.get xd (by simpa using hd), hD]
  have hst : t.gpr xs = S := by rw [ht.keep.get xs (by simpa using hs), hS]
  have hnc : n * c + n ≤ n * K := by
    have := Nat.mul_le_mul_left n (show c + 1 ≤ K by omega); rwa [Nat.mul_succ] at this
  have hsub : Region.Sub ⟨S + BitVec.ofNat 64 (o + 32 * c), n⟩ ⟨S + BitVec.ofNat 64 o, 32 * K⟩ :=
    Offset.sub S (by omega) (by omega)
  have hDs : Region.Sub ⟨D + BitVec.ofNat 64 (n * c), n⟩ ⟨D, n * K⟩ := Offset.sub_base D hnc
  refine copyWords_ok (t := xd) (sr := xs) (d₂ := n * c) (d₁ := o + 32 * c) (w := n / 8)
    ⟨hd, hs, ⟨by omega, by omega⟩, ⟨Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero h8) c), by omega⟩,
      by rw [ht.keep.rd, ht.keep.wr, hst, h8n, ← addr_add]; exact InRegions.sub hr (by omega),
      by rw [ht.keep.wr, hdt, h8n]; exact InRegions.sub hw hnc,
      by rw [hdt, hst, h8n]; exact (hdis.sub_left hDs).sub_right hsub⟩ fun u ku fu bu => k' u ?_
  simp only [hdt, hst, h8n] at fu bu
  have hcs : bytesAt u.mem (D + BitVec.ofNat 64 (n * c)) n = bytesAt s.mem (S + BitVec.ofNat 64 (o + 32 * c)) n := by
    rw [bu]
    exact bytesAt_frame ht.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hdis.sub_right hsub).symm.sub_right (fun x hx => hx)) (by omega)
  refine ⟨(ht.keep.trans ku).mono (by simp), fun c' hc' => ?_, ht.frame.trans (fu.sub fun r hr => ?_)⟩
  · by_cases e : c' = c
    · subst e; exact hcs
    · have : n * c' + n ≤ n * K := by
        have := Nat.mul_le_mul_left n (show c' + 1 ≤ K by omega); rwa [Nat.mul_succ] at this
      rw [bytesAt_frame fu (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint D (by
          rcases Nat.lt_or_gt_of_ne e with h | h
          · have := Nat.mul_le_mul_left n (show c' + 1 ≤ c by omega); left; rw [Nat.mul_succ] at this; omega
          · have := Nat.mul_le_mul_left n (show c + 1 ≤ c' by omega); right; rw [Nat.mul_succ] at this; omega)
          (by omega) (by omega)) (by omega)]
      exact ht.bytes c' (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, hDs⟩

/-- The first block of `keyGen`. -/
abbrev proCode (p : Params) : List Instr :=
  saveRegsAt Layout.oTop .x3 topSaved ++ [mov .x19 .x3, mov .x20 .x1, mov .x21 .x2] ++
    (List.range 3).flatMap (fun c => copyWords .x19 (Layout.oKeys + 32 * c) .x0 (p.n * c) (p.n / 8)) ++
    seedLanes p ++ [.movz .x .x10 (BitVec.ofNat 16 (p.d - 1)) 0, .movz .x .x11 0 0] ++ treeLanes p .x10 .x11 ++
    [mov .x0 .x19] ++ movV .x1 0xffffffff ++ lea .x2 .x19 Layout.oSigTmp

/-- The last block of `keyGen`. -/
abbrev tailCode (p : Params) : List Instr :=
  copyWords .x19 Layout.oPkRoot .x19 Layout.oMsg (p.n / 8) ++ writeKeys p ++ restoreRegsAt Layout.oTop topSaved

theorem keyGen_eq (p : Params) (f : Impl.SlhDsa.AArch64.Shake.Fns) :
    Impl.SlhDsa.AArch64.Shake.keyGen p f =
      .seq (.block (proCode p)) (.seq (.call f.xmssName (Impl.SlhDsa.AArch64.Shake.xmssCode p f))
        (.block (tailCode p))) := rfl

/-- The callee-saved registers the functions never write. -/
abbrev untouched : List Reg := [.x26, .x27, .x28]

/-- After the prologue, from the entry `σ` with `scratch = S` and `seeds = X`. -/
structure KPro (p : Params) (σ : State) (S X : Addr) (s : State) : Prop where
  x19 : s.gpr .x19 = S
  x20 : s.gpr .x20 = σ.gpr .x1
  x21 : s.gpr .x21 = σ.gpr .x2
  x0 : s.gpr .x0 = S
  x1 : s.gpr .x1 = BitVec.ofNat 64 0xffffffff
  x2 : s.gpr .x2 = at' S Layout.oSigTmp
  keep : ∀ r ∈ untouched, s.gpr r = σ.gpr r
  sp : s.sp = σ.sp
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  saved : ∀ i < 8, s.mem.readW (at' S (Layout.oTop + 8 * i)) 64 = σ.gpr (topSaved.getD i .x19)
  keys : ∀ c < 3, bytesAt s.mem (at' S (Layout.oKeys + 32 * c)) p.n = bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * c)) p.n
  env : Env p s.mem S (bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * 2)) p.n) (Proof.SlhDsa.layerTree (p.d - 1) 0)
  frame : Frame [⟨S, scratchLen⟩] σ.mem s.mem

/-- String `z` of the `c` strings of `n` bytes at `a`. -/
theorem chunk_bytesAt (m : Mem) (a : Addr) {n z c : Nat} (hz : z < c) :
    chunk (bytesAt m a (c * n)) n z = bytesAt m (a + BitVec.ofNat 64 (n * z)) n := by
  have hl : (chunk (bytesAt m a (c * n)) n z).length = n := by
    simp only [chunk, List.length_take, List.length_drop, bytesAt, List.length_map, List.length_range]
    have : n ≤ c * n - n * z := by
      rw [Nat.mul_comm n z, ← Nat.sub_mul]
      exact Nat.le_mul_of_pos_left n (by omega)
    omega
  apply List.ext_getElem (by rw [hl]; simp [bytesAt])
  intro i h₁ h₂
  have hi : i < n := by rw [hl] at h₁; exact h₁
  have hzn : n * z + i < c * n := by
    have : n * z + n ≤ c * n := by rw [Nat.mul_comm c n, ← Nat.mul_succ]; exact Nat.mul_le_mul_left n hz
    omega
  simp only [chunk, List.getElem_take, List.getElem_drop, bytesAt, List.getElem_map, List.getElem_range]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- A range of `scratch`, of a state that may write all of it. -/
theorem in_scr {wr : List Region} {S : Addr} (hw : (⟨S, scratchLen⟩ : Region) ∈ wr) {o l : Nat}
    (h : o + l ≤ scratchLen) : InRegions wr (S + BitVec.ofNat 64 o) l :=
  ⟨_, hw, Offset.contains_base _ h (by simp only [scratchLen] at h; omega)⟩

theorem pro_ok {p : Params} (hz : Sz p) (hd : p.d - 1 < 2 ^ 16) {σ : State} {S X : Addr}
    (hS : σ.gpr .x3 = S) (hX : σ.gpr .x0 = X) (hw : (⟨S, scratchLen⟩ : Region) ∈ σ.wr)
    (hr : (⟨X, 3 * p.n⟩ : Region) ∈ σ.rd) (hXf : X.toNat + 3 * p.n ≤ 2 ^ 64) (hSf : S.toNat + scratchLen ≤ 2 ^ 64)
    (hdis : Region.Disjoint ⟨X, 3 * p.n⟩ ⟨S, scratchLen⟩) :
    WP isa (.block (proCode p)) σ (KPro p σ S X) := by
  have hn := hz.n32
  have h8 := hz.n8
  have hsc : scratchLen = 65536 := rfl
  have eT : Layout.oTop = 1536 := rfl
  have eK : Layout.oKeys = 1664 := rfl
  have eS : Layout.oSigTmp = 30144 := rfl
  have hsub : ∀ {o l : Nat}, o + l ≤ scratchLen → Region.Sub ⟨S + BitVec.ofNat 64 o, l⟩ ⟨S, scratchLen⟩ :=
    fun h => Offset.sub_base S h
  simp only [proCode, List.append_assoc, List.cons_append, List.nil_append]
  refine saveRegsAt_ok (s := σ) (b := .x3) ⟨by decide, by decide⟩ (by rw [hS]; exact in_scr hw (by decide))
    fun s₁ k₁ sv₁ f₁ => ?_
  rw [hS] at sv₁ f₁
  refine MlKem.AArch64.wp_addImm (by decide) fun s₂ o₂ e₂ => MlKem.AArch64.wp_addImm (by decide) fun s₃ o₃ e₃ =>
    MlKem.AArch64.wp_addImm (by decide) fun s₄ o₄ e₄ => ?_
  have k₄ : Keep [.x19, .x20, .x21] σ s₄ := (k₁.trans ((o₂.trans o₃).trans o₄).keep).mono (by decide)
  have h19 : s₄.gpr .x19 = S := by
    rw [o₄.get .x19, o₃.get .x19, e₂, BitVec.add_zero, k₁.get .x3, hS]
  have hm₄ : s₄.mem = s₁.mem := by rw [o₄.mem, o₃.mem, o₂.mem]
  have hw₄ : (⟨S, scratchLen⟩ : Region) ∈ s₄.wr := by rw [k₄.wr]; exact hw
  -- the seeds
  refine copyIn_ok (n := p.n) hn h8 (xd := .x19) (xs := .x0) (by decide) (by decide) (D := S) (X := X) h19
    (by rw [k₄.get .x0, hX]) (o := Layout.oKeys) (K := 3) (by decide) ⟨by decide, by decide⟩
    (in_scr hw₄ (by decide)) ⟨_, List.mem_append_left _ (by rw [k₄.rd]; exact hr), by
      rw [Nat.mul_comm]; exact Region.contains_self _ _⟩ (by omega) (by rw [Nat.mul_comm]; omega)
    (by rw [Nat.mul_comm]; exact hdis.sub_right (hsub (by decide))) fun s₅ i₅ => ?_
  have h19₅ : s₅.gpr .x19 = S := by rw [i₅.keep.get .x19, h19]
  refine seedLanes_ok (p := p) hz.nv h19₅ (by rw [i₅.keep.wr]; exact hw₄) fun s₆ i₆ => ?_
  have h19₆ : s₆.gpr .x19 = S := by rw [i₆.keep.get .x19, h19₅]
  refine MlKem.AArch64.wp_movz fun s₇ o₇ e₇ => MlKem.AArch64.wp_movz fun s₈ o₈ e₈ => ?_
  have h10 : (s₈.gpr .x10).toNat = p.d - 1 := by
    rw [o₈.get .x10, e₇, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have h11 : (s₈.gpr .x11).toNat = 0 := by rw [e₈]; rfl
  have h19₈ : s₈.gpr .x19 = S := by rw [o₈.get .x19, o₇.get .x19, h19₆]
  refine treeLanes_ok (p := p) hz.nv (by decide) h19₈ (by rw [o₈.wr, o₇.wr, i₆.keep.wr, i₅.keep.wr]; exact hw₄)
    (by rw [h10]; omega) fun s₉ k₉ f₉ a₉ => ?_
  rw [h10, h11] at a₉
  have h19₉ : s₉.gpr .x19 = S := by rw [k₉.get .x19, h19₈]
  refine MlKem.AArch64.wp_addImm (by decide) fun s₁₀ o₁₀ e₁₀ => movV_ok (by decide) fun s₁₁ o₁₁ e₁₁ => ?_
  rw [← List.append_nil (lea .x2 .x19 Layout.oSigTmp)]
  refine lea_ok (.inr (by decide)) (by decide) fun s₁₂ o₁₂ e₁₂ => MlKem.AArch64.wp_nil ?_
  have k₁₂ : Keep [.x19, .x20, .x21, .x14, .x10, .x11, .x12, .x13, .x14, .x0, .x1, .x2] σ s₁₂ :=
    ((k₄.trans (i₅.keep.trans (i₆.keep.trans ((o₇.trans o₈).keep.trans (k₉.trans (o₁₀.trans (o₁₁.trans o₁₂)).keep)))))).mono
      (by decide)
  have hm : s₁₂.mem = s₉.mem := by rw [o₁₂.mem, o₁₁.mem, o₁₀.mem]
  have hm₈ : s₈.mem = s₆.mem := by rw [o₈.mem, o₇.mem]
  -- what each step wrote, in `scratch`
  have dK : ∀ {o l : Nat}, o + l ≤ Layout.oA → ∀ r ∈ adrsRegions p.n S ++ seedRegions p.n S,
      Region.Disjoint ⟨S + BitVec.ofNat 64 o, l⟩ r := fun {o l} h r hr => by
    simp only [adrsRegions, seedRegions, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ⟨k, hk, b, hb, rfl⟩ | ⟨k, hk, rfl | rfl⟩
    · have := laneAdrs_lt (n := p.n) hn hk hb
      exact Offset.disjoint S (by simp only [Layout.oA] at h; omega) (by simp only [Layout.oA] at h; omega) (by omega)
    · exact Offset.disjoint S (by simp only [Layout.oA, laneA_eq] at h ⊢; omega) (by simp only [Layout.oA] at h; omega)
        (by rw [laneA_eq]; omega)
    · exact Offset.disjoint S (by simp only [Layout.oA, laneB_eq] at h ⊢; omega) (by simp only [Layout.oA] at h; omega)
        (by rw [laneB_eq]; omega)
  have hlow : ∀ {o l : Nat}, o + l ≤ Layout.oA →
      bytesAt s₁₂.mem (S + BitVec.ofNat 64 o) l = bytesAt s₅.mem (S + BitVec.ofNat 64 o) l := fun {o l} h => by
    rw [hm, bytesAt_frame f₉ (fun r hr => dK h r (List.mem_append_left _ hr)) (by simp only [Layout.oA] at h; omega),
      hm₈, bytesAt_frame i₆.frame (fun r hr => dK h r (List.mem_append_right _ hr)) (by simp only [Layout.oA] at h; omega)]
  have hX₀ : ∀ c < 3, bytesAt s₄.mem (X + BitVec.ofNat 64 (p.n * c)) p.n = bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * c)) p.n :=
    fun c hc => by
      have : p.n * c + p.n ≤ 3 * p.n := by
        have := Nat.mul_le_mul_left p.n (show c + 1 ≤ 3 by omega); rw [Nat.mul_succ] at this; omega
      rw [hm₄, bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hdis.sub_left (Offset.sub_base X this)).sub_right (hsub (by simp only [topSaved, List.length]; omega)))
        (by omega)]
  have hkeys : ∀ c < 3, bytesAt s₁₂.mem (at' S (Layout.oKeys + 32 * c)) p.n = bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * c)) p.n :=
    fun c hc => by
      rw [hlow (by simp only [Layout.oA]; omega), i₅.bytes c hc, hX₀ c hc]
  have hpk : bytesAt s₅.mem (at' S Layout.oPkSeed) p.n = bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * 2)) p.n := by
    have := i₅.bytes 2 (by decide); rw [hX₀ 2 (by decide)] at this; exact this
  -- the lanes
  have hseed : ∀ k < 4, ∀ b < 2, bytesAt s₁₂.mem (at' S (if b = 0 then Layout.laneA k else Layout.laneB k)) p.n =
      bytesAt σ.mem (X + BitVec.ofNat 64 (p.n * 2)) p.n := fun k hk b hb => by
    rw [hm, bytesAt_frame f₉ (fun r hr => by
      simp only [adrsRegions, List.mem_flatMap, List.mem_range, List.mem_map] at hr
      obtain ⟨k', hk', b', hb', rfl⟩ := hr
      have h1 := laneAdrs_lt (n := p.n) hn hk' hb'
      have h2 := laneAdrs_lt (n := p.n) hn hk hb
      refine Offset.disjoint S ?_ (by split <;> simp only [laneA_eq, laneB_eq] <;> omega) (by omega)
      simp only [laneAdrs] at h1 h2 ⊢
      split <;> split <;> simp only [laneA_eq, laneB_eq] at * <;> omega) (by omega), hm₈, ← hpk]
    have := i₆.lanes k hk
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
    · exact this.1
    · exact this.2
  refine ⟨h19₉ ▸ by rw [o₁₂.get .x19, o₁₁.get .x19, o₁₀.get .x19, h19₉], ?_, ?_, ?_, ?_, ?_, fun r hr => ?_,
    ?_, fun r hr => ?_, ?_, ?_, fun i hi => ?_, hkeys, ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩,
    ?_⟩
  · rw [o₁₂.get .x20, o₁₁.get .x20, o₁₀.get .x20, k₉.get .x20, o₈.get .x20, o₇.get .x20, i₆.keep.get .x20,
      i₅.keep.get .x20, o₄.get .x20, e₃, BitVec.add_zero, o₂.get .x1, k₁.get .x1]
  · rw [o₁₂.get .x21, o₁₁.get .x21, o₁₀.get .x21, k₉.get .x21, o₈.get .x21, o₇.get .x21, i₆.keep.get .x21,
      i₅.keep.get .x21, e₄, BitVec.add_zero, o₃.get .x2, o₂.get .x2, k₁.get .x2]
  · rw [o₁₂.get .x0, o₁₁.get .x0, e₁₀, BitVec.add_zero, h19₉]
  · rw [o₁₂.get .x1, e₁₁]
  · rw [e₁₂, o₁₁.get .x19, o₁₀.get .x19, h19₉]
  · rw [k₁₂.get r (by revert r; decide)]
  · rw [k₁₂.sp]
  · rw [k₁₂.vcs r hr]
  · rw [k₁₂.rd]
  · rw [k₁₂.wr]
  · have hi8 : i < topSaved.length := by simp only [topSaved, List.length]; omega
    have dR : ∀ r ∈ adrsRegions p.n S ++ seedRegions p.n S,
        Region.Disjoint ⟨S + BitVec.ofNat 64 (Layout.oTop + 8 * i), 8⟩ r := dK (by simp only [Layout.oA]; omega)
    rw [hm, Frame.readW f₉ (Region.contains_self _ _) (fun r hr => dR r (List.mem_append_left _ hr)) (by decide), hm₈,
      Frame.readW i₆.frame (Region.contains_self _ _) (fun r hr => dR r (List.mem_append_right _ hr)) (by decide),
      Frame.readW i₅.frame (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
        (by decide), hm₄, sv₁ i hi8, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi8, Option.getD_some]
  · simpa using hseed k hk 0 (by decide)
  · simpa using hseed k hk 1 (by decide)
  · rw [hm]; simpa [laneAdrs] using a₉ k hk 0 (by decide)
  · rw [hm]; simpa [laneAdrs] using a₉ k hk 1 (by decide)
  · have hsc' : ∀ (rs : List Region), (∀ r ∈ rs, Region.Sub r ⟨S, scratchLen⟩) →
        ∀ r ∈ rs, ∃ r' ∈ [(⟨S, scratchLen⟩ : Region)], Region.Sub r r' :=
      fun rs h r hr => ⟨_, List.mem_singleton_self _, h r hr⟩
    have sA : ∀ r ∈ adrsRegions p.n S, Region.Sub r ⟨S, scratchLen⟩ := fun r hr => by
      simp only [adrsRegions, List.mem_flatMap, List.mem_range, List.mem_map] at hr
      obtain ⟨k, hk, b, hb, rfl⟩ := hr
      have := laneAdrs_lt (n := p.n) hn hk hb
      exact hsub (by omega)
    have sS : ∀ r ∈ seedRegions p.n S, Region.Sub r ⟨S, scratchLen⟩ := fun r hr => by
      simp only [seedRegions, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain ⟨k, hk, rfl | rfl⟩ := hr
      · exact hsub (by rw [laneA_eq]; omega)
      · exact hsub (by rw [laneB_eq]; omega)
    have F1 : Frame [⟨S, scratchLen⟩] σ.mem s₁.mem := f₁.sub (hsc' _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hsub (by simp only [topSaved, List.length]; omega))
    have F2 : Frame [⟨S, scratchLen⟩] s₁.mem s₅.mem := by
      rw [← hm₄]; exact i₅.frame.sub (hsc' _ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub (by omega))
    have F4 : Frame [⟨S, scratchLen⟩] s₆.mem s₉.mem := by rw [← hm₈]; exact f₉.sub (hsc' _ sA)
    rw [hm]
    exact F1.trans (F2.trans ((i₆.frame.sub (hsc' _ sS)).trans F4))


/-- After the tail, from the state `w` after the call. -/
structure KTail (p : Params) (σ w : State) (S SK PK : Addr) (t : State) : Prop where
  rd : t.rd = w.rd
  wr : t.wr = w.wr
  sp : t.sp = w.sp
  cs : ∀ r ∈ topSaved, t.gpr r = σ.gpr r
  keep : ∀ r ∈ untouched, t.gpr r = w.gpr r
  vcs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64
  sk : bytesAt t.mem SK (4 * p.n) = bytesAt w.mem (at' S Layout.oKeys) p.n ++
    bytesAt w.mem (at' S (Layout.oKeys + 32)) p.n ++ bytesAt w.mem (at' S (Layout.oKeys + 64)) p.n ++
    bytesAt w.mem (at' S Layout.oMsg) p.n
  pk : bytesAt t.mem PK (2 * p.n) = bytesAt w.mem (at' S (Layout.oKeys + 64)) p.n ++
    bytesAt w.mem (at' S Layout.oMsg) p.n

theorem bytesAt_add' (m : Mem) (a : Addr) (x y : Nat) :
    bytesAt m a (x + y) = bytesAt m a x ++ bytesAt m (a + BitVec.ofNat 64 x) y := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem bytesAt_four (m : Mem) (a : Addr) (n : Nat) :
    bytesAt m a (4 * n) = bytesAt m (a + BitVec.ofNat 64 (n * 0)) n ++ bytesAt m (a + BitVec.ofNat 64 (n * 1)) n ++
      bytesAt m (a + BitVec.ofNat 64 (n * 2)) n ++ bytesAt m (a + BitVec.ofNat 64 (n * 3)) n := by
  rw [show 4 * n = n + (n + (n + n)) by omega, bytesAt_add', bytesAt_add', bytesAt_add']
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.mul_zero, Nat.mul_one, BitVec.add_zero]
  rw [show n + n = n * 2 by omega, show n * 2 + n = n * 3 by omega]

theorem bytesAt_two (m : Mem) (a : Addr) (n : Nat) :
    bytesAt m a (2 * n) = bytesAt m (a + BitVec.ofNat 64 (n * 0)) n ++ bytesAt m (a + BitVec.ofNat 64 (n * 1)) n := by
  rw [show 2 * n = n + n by omega, bytesAt_add']
  simp only [Nat.mul_zero, Nat.mul_one, BitVec.add_zero]

theorem topSaved_nodup : topSaved.Nodup := by decide

theorem tail_ok {p : Params} (hz : Sz p) {σ w : State} {S SK PK : Addr}
    (hb : w.gpr .x19 = S) (h20 : w.gpr .x20 = SK) (h21 : w.gpr .x21 = PK)
    (hw : (⟨S, scratchLen⟩ : Region) ∈ w.wr)
    (hsk : (⟨SK, 4 * p.n⟩ : Region) ∈ w.wr) (hpk : (⟨PK, 2 * p.n⟩ : Region) ∈ w.wr)
    (fS : S.toNat + scratchLen ≤ 2 ^ 64) (fsk : SK.toNat + 4 * p.n ≤ 2 ^ 64) (fpk : PK.toNat + 2 * p.n ≤ 2 ^ 64)
    (dsk : Region.Disjoint ⟨SK, 4 * p.n⟩ ⟨S, scratchLen⟩) (dpk : Region.Disjoint ⟨PK, 2 * p.n⟩ ⟨S, scratchLen⟩)
    (dskpk : Region.Disjoint ⟨SK, 4 * p.n⟩ ⟨PK, 2 * p.n⟩)
    (hsv : ∀ i < 8, w.mem.readW (at' S (Layout.oTop + 8 * i)) 64 = σ.gpr (topSaved.getD i .x19)) :
    WP isa (.block (tailCode p)) w (KTail p σ w S SK PK) := by
  have hn := hz.n32
  have h8 := hz.n8
  have h8n : 8 * (p.n / 8) = p.n := by omega
  have hsc : scratchLen = 65536 := rfl
  have eK : Layout.oKeys = 1664 := rfl
  have eR : Layout.oPkRoot = 1760 := rfl
  have eM : Layout.oMsg = 1984 := rfl
  have eT : Layout.oTop = 1536 := rfl
  have hsub : ∀ {o l : Nat}, o + l ≤ scratchLen → Region.Sub ⟨S + BitVec.ofNat 64 o, l⟩ ⟨S, scratchLen⟩ :=
    fun h => Offset.sub_base S h
  simp only [tailCode, writeKeys, List.append_assoc]
  -- the root to `PK.root`
  refine copyWords_ok (t := .x19) (sr := .x19) (d₂ := Layout.oPkRoot) (d₁ := Layout.oMsg) (w := p.n / 8)
    ⟨by decide, by decide, ⟨by decide, by omega⟩, ⟨by decide, by omega⟩,
      by rw [hb]; exact InRegions.rdwr (in_scr hw (by omega)),
      by rw [hb]; exact in_scr hw (by omega),
      by rw [hb]; exact Offset.disjoint S (by omega) (by omega) (by omega)⟩ fun w₁ k₁ f₁ b₁ => ?_
  simp only [hb, h8n] at f₁ b₁
  have hb₁ : w₁.gpr .x19 = S := by rw [k₁.get .x19, hb]
  -- the private key
  refine copyOut_ok (n := p.n) hn h8 (xd := .x20) (xs := .x19) (by decide) (by decide) (D := SK) (S := S)
    (by rw [k₁.get .x20, h20]) hb₁ (o := Layout.oKeys) (K := 4) (by decide) ⟨by decide, by omega⟩
    (by rw [k₁.rd, k₁.wr]; exact InRegions.rdwr (in_scr hw (by omega)))
    (by rw [k₁.wr]; exact ⟨_, hsk, by rw [Nat.mul_comm]; exact Region.contains_self _ _⟩)
    (by omega) (by rw [Nat.mul_comm]; omega)
    (by rw [Nat.mul_comm]; exact dsk.sub_right (hsub (by omega))) fun w₂ o₂ => ?_
  have hb₂ : w₂.gpr .x19 = S := by rw [o₂.keep.get .x19, hb₁]
  -- the public key
  refine copyOut_ok (n := p.n) hn h8 (xd := .x21) (xs := .x19) (by decide) (by decide) (D := PK) (S := S)
    (by rw [o₂.keep.get .x21, k₁.get .x21, h21]) hb₂ (o := Layout.oKeys + 64) (K := 2) (by decide)
    ⟨by decide, by omega⟩
    (by rw [o₂.keep.rd, o₂.keep.wr, k₁.rd, k₁.wr]; exact InRegions.rdwr (in_scr hw (by omega)))
    (by rw [o₂.keep.wr, k₁.wr]; exact ⟨_, hpk, by rw [Nat.mul_comm]; exact Region.contains_self _ _⟩)
    (by omega) (by rw [Nat.mul_comm]; omega)
    (by rw [Nat.mul_comm]; exact dpk.sub_right (hsub (by omega))) fun w₃ o₃ => ?_
  have hb₃ : w₃.gpr .x19 = S := by rw [o₃.keep.get .x19, hb₂]
  -- the scratch's bytes are unchanged by the copies out
  have hsc₃ : ∀ {o l : Nat}, o + l ≤ scratchLen →
      ∀ a, Region.Contains ⟨S + BitVec.ofNat 64 o, l⟩ a 1 → w₃.mem a = w₁.mem a := fun {o l} h a ha => by
    have e₃ := o₃.frame a fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dpk.sub_right (hsub h) a (by rw [Nat.mul_comm] at hc; exact hc) ha
    have e₂ := o₂.frame a fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dsk.sub_right (hsub h) a (by rw [Nat.mul_comm] at hc; exact hc) ha
    rw [e₃, e₂]
  refine restoreRegsAt_ok (s := w₃) topSaved_nodup ⟨by decide, by decide⟩
    (by rw [hb₃, o₃.keep.rd, o₃.keep.wr, o₂.keep.rd, o₂.keep.wr, k₁.rd, k₁.wr]
        exact InRegions.rdwr (in_scr hw (by decide))) fun t ot vt => wp_nil ?_
  have hk : Keep (topSaved ++ [.x14]) w t :=
    ((k₁.trans (o₂.keep.trans o₃.keep)).trans ot.keep).mono (by decide)
  refine ⟨hk.rd, hk.wr, hk.sp, fun r hr => ?_, fun r hr => hk.get r (by revert r; decide), hk.vcs, ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
    rw [vt i hi, hb₃]
    have hi8 : i < 8 := by simp only [topSaved, List.length] at hi; omega
    have hsA : Region.Sub ⟨S + BitVec.ofNat 64 (Layout.oTop + 8 * i), 8⟩ ⟨S, scratchLen⟩ := hsub (by omega)
    have e : w₃.mem.readW (S + BitVec.ofNat 64 (Layout.oTop + 8 * i)) 64 = w.mem.readW (at' S (Layout.oTop + 8 * i)) 64 := by
      rw [Frame.readW o₃.frame (r := ⟨S + BitVec.ofNat 64 (Layout.oTop + 8 * i), 8⟩) (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            rw [Nat.mul_comm p.n]; exact (dpk.sub_right hsA).symm) (by decide),
        Frame.readW o₂.frame (r := ⟨S + BitVec.ofNat 64 (Layout.oTop + 8 * i), 8⟩) (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            rw [Nat.mul_comm p.n]; exact (dsk.sub_right hsA).symm) (by decide),
        Frame.readW f₁ (r := ⟨S + BitVec.ofNat 64 (Layout.oTop + 8 * i), 8⟩) (Region.contains_self _ _)
          (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint S (by omega) (by omega) (by omega)) (by decide)]
    rw [e, hsv i hi8, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi, Option.getD_some]
  · have hm : t.mem = w₃.mem := ot.mem
    have hsk3 : ∀ c < 4, bytesAt t.mem (SK + BitVec.ofNat 64 (p.n * c)) p.n =
        bytesAt w₁.mem (S + BitVec.ofNat 64 (Layout.oKeys + 32 * c)) p.n := fun c hc => by
      have : p.n * c + p.n ≤ 4 * p.n := by
        have := Nat.mul_le_mul_left p.n (show c + 1 ≤ 4 by omega); rw [Nat.mul_succ] at this; omega
      rw [hm, bytesAt_frame o₃.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [Nat.mul_comm p.n 2]; exact dskpk.sub_left (Offset.sub_base SK this)) (by omega)]
      exact o₂.bytes c hc
    have hk₁ : ∀ c < 3, bytesAt w₁.mem (S + BitVec.ofNat 64 (Layout.oKeys + 32 * c)) p.n =
        bytesAt w.mem (at' S (Layout.oKeys + 32 * c)) p.n := fun c hc =>
      bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
        (by omega)
    rw [bytesAt_four, hsk3 0 (by decide), hsk3 1 (by decide), hsk3 2 (by decide), hsk3 3 (by decide),
      hk₁ 0 (by decide), hk₁ 1 (by decide), hk₁ 2 (by decide), show Layout.oKeys + 32 * 3 = Layout.oPkRoot from rfl, b₁]
    rfl
  · have hm : t.mem = w₃.mem := ot.mem
    have hpk2 : ∀ c < 2, bytesAt t.mem (PK + BitVec.ofNat 64 (p.n * c)) p.n =
        bytesAt w₁.mem (S + BitVec.ofNat 64 (Layout.oKeys + 64 + 32 * c)) p.n := fun c hc => by
      rw [hm, o₃.bytes c hc]
      exact bytesAt_frame o₂.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [Nat.mul_comm p.n 4]; exact (dsk.sub_right (hsub (by omega))).symm) (by omega)
    have hk₁ : bytesAt w₁.mem (S + BitVec.ofNat 64 (Layout.oKeys + 64 + 32 * 0)) p.n =
        bytesAt w.mem (at' S (Layout.oKeys + 64)) p.n :=
      bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S (by omega) (by omega) (by omega))
        (by omega)
    rw [bytesAt_two, hpk2 0 (by decide), hpk2 1 (by decide), hk₁,
      show Layout.oKeys + 64 + 32 * 1 = Layout.oPkRoot from rfl, b₁]

end VG.Proof.SlhDsa.AArch64.KeyGen
