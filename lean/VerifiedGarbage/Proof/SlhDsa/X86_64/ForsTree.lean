module

-- separate module: the subtree's loop of leaves and heights, which `ForsSub` does not rebuild when it changes

public import VerifiedGarbage.Proof.SlhDsa.X86_64.ForsLeaf
public import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.SlhDsa.Lemmas

/-!
# SLH-DSA (SHAKE) on x86-64: `forsSign`, a subtree

The loop of `leafBody` over the `2^s` leaves of a subtree (`leaves_ok`), and
the subtree's heights (`levels`), its root to the subtree roots and its nodes
of the authentication path XORed into the signature's (`subHeights_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64.Fors

open VG VG.X86_64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.X86_64 (Layout setField setFieldR copyWords)
open VG.Impl.SlhDsa.X86_64.Fors
open VG.Proof.SlhDsa (fld)

/-- Leaf `x` of the FORS trees, as the code computes it. -/
abbrev leafv (p : Params) (pkSeed a16 skSeed : List Byte) (kp x : Nat) : List Byte :=
  F p pkSeed (fld a16 3 kp 0 x) (prf p pkSeed skSeed (fld a16 6 kp 0 x))

/-- Byte `j` of the private key value of leaf `x`. -/
abbrev skv (p : Params) (pkSeed a16 skSeed : List Byte) (kp x j : Nat) : Byte :=
  (prf p pkSeed skSeed (fld a16 6 kp 0 x)).getD j 0

/-- What the loop of leaves changes. -/
abbrev loopW (n : Nat) (S AU : Addr) (sp : Addr) (stack : Nat) : List Region :=
  [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, ⟨at' S (Layout.oVar 2 3), 8⟩, ⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, ⟨AU, n⟩,
    below sp stack] ++ laneRs n S

/-- The registers, regions and MXCSR a part of the tree keeps. -/
structure Fix (t₀ t : State) : Prop where
  cs : ∀ r ∈ calleeSaved, t.gpr r = t₀.gpr r
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  mx : t.mxcsr.extractLsb' 6 10 = t₀.mxcsr.extractLsb' 6 10

theorem Fix.refl (t : State) : Fix t t := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Fix.trans {t₀ t t' : State} (h : Fix t₀ t) (h' : Fix t t') : Fix t₀ t' :=
  ⟨fun r hr => by rw [h'.cs r hr, h.cs r hr], by rw [h'.rd, h.rd], by rw [h'.wr, h.wr], by rw [h'.mx, h.mx]⟩

/-- The state of the loop of leaves after `J` leaves of the subtree from
`U2` of the tree from `V4`, from its entry state `t₀`. -/
structure LS (p : Params) (stack : Nat) (S AU : Addr) (pkSeed a16 skSeed : List Byte) (kp V4 U2 idx : Nat)
    (t₀ : State) (J : Nat) (t : State) : Prop where
  fix : Fix t₀ t
  env : Env p t.mem S pkSeed a16
  sk : SkAt p t.mem S skSeed
  v1 : t.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU
  v2 : t.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2
  v3 : t.mem.readW (at' S (Layout.oVar 2 3)) 64 = BitVec.ofNat 64 J
  v4 : t.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 V4
  nodes : ∀ i < J, bytesAt t.mem (at' S (Layout.oN + i * p.n)) p.n = leafv p pkSeed a16 skSeed kp (V4 + U2 + i)
  skb : ∀ j < p.n, t.mem (AU + BitVec.ofNat 64 j) =
    if U2 ≤ idx ∧ idx < U2 + J then skv p pkSeed a16 skSeed kp (V4 + idx) j ^^^ t₀.mem (AU + BitVec.ofNat 64 j)
    else t₀.mem (AU + BitVec.ofNat 64 j)
  frame : Frame (loopW p.n S AU (t₀.gpr .rsp) stack) t₀.mem t.mem

/-- The loop's invariant at the measure `m` (the passes left). -/
abbrev LI (p : Params) (stack : Nat) (S AU : Addr) (pkSeed a16 skSeed : List Byte) (kp V4 U2 idx : Nat)
    (t₀ : State) (m : Nat) (u : State) : Prop :=
  ∃ J, J + 4 * m = 2 ^ s p.a ∧ 0 < m ∧ LS p stack S AU pkSeed a16 skSeed kp V4 U2 idx t₀ J u

/-- A pass of the loop of leaves. -/
theorem leaves_step {p : Params} (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 8 ≤ stack) (hs63 : stack < 2 ^ 63) {S AU : Addr}
    {KP : BitVec 64} {V4 U2 idx : Nat} {pkSeed a16 skSeed : List Byte} {t₀ : State}
    (hbx : t₀.gpr .rbx = S) (h12 : t₀.gpr .r12 = KP) (hKP : KP.toNat < 2 ^ 32)
    (h13 : t₀.gpr .r13 = BitVec.ofNat 64 idx) (hidx : idx < 2 ^ 32)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t₀.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t₀.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩)
    (hX : V4 + U2 + 2 ^ s p.a < 2 ^ 32)
    (hout : ∀ w < p.n / 8, InRegions t₀.wr (AU + BitVec.ofNat 64 (8 * w)) 8)
    (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩) (hAs : Region.Disjoint ⟨AU, p.n⟩ (below (t₀.gpr .rsp) stack)) (m : Nat) (u : State)
    (hI : LI p stack S AU pkSeed a16 skSeed KP.toNat V4 U2 idx t₀ m u) :
    WP isa (leafBody ⟨p.n, p.len⟩ p.a name T.code) u fun u' => isa.eval .b u' = some (decide (1 < m)) ∧
      (decide (1 < m) = false → LS p stack S AU pkSeed a16 skSeed KP.toNat V4 U2 idx t₀ (2 ^ s p.a) u') ∧
      (decide (1 < m) = true → m - 1 < m ∧ LI p stack S AU pkSeed a16 skSeed KP.toNat V4 U2 idx t₀ (m - 1) u') := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hs9 : s p.a ≤ 9 := Nat.min_le_right _ _
  have h512 : 2 ^ s p.a ≤ 512 := by
    calc 2 ^ s p.a ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hs9
      _ = 512 := rfl
  have eN : Layout.oN = 12640 := rfl
  have eNS : Layout.nodeSlots = 520 := rfl
  obtain ⟨J, hJ, hm, L⟩ := hI
  have hsp : u.gpr .rsp = t₀.gpr .rsp := L.fix.cs _ (by simp [calleeSaved])
  have hJ4 : (J + 4) * p.n ≤ 32 * Layout.nodeSlots := by
    have := Nat.mul_le_mul_right p.n (show J + 4 ≤ 520 by omega_using [hJ, hm, h512])
    rw [eNS]; omega_using [this, hn32]
  refine WP.mono (leaf_ok T name hn hf hst hs63 (V4 := V4) (U2 := U2) (J := J) (idx := idx) (AU := AU)
    (by rw [L.fix.cs _ (by simp [calleeSaved]), hbx]) (by rw [L.fix.cs _ (by simp [calleeSaved]), h12]) hKP
    (by rw [L.fix.cs _ (by simp [calleeSaved]), h13]) hidx (by rw [L.fix.wr]; exact hw) hS (by rw [hsp]; exact hstk)
    L.env L.sk L.v1 L.v2 L.v3 L.v4 (by omega_using [hX, hJ, hm]) hJ4 (fun w hw' => by rw [L.fix.wr]; exact hout w hw')
    hd (by rw [hsp]; exact hAs)) fun u' P => ?_
  have hJn : J * p.n + 4 * p.n ≤ 32 * Layout.nodeSlots := by rw [← Nat.add_mul]; exact hJ4
  -- the bytes the four leaves leave
  have keep : ∀ o l, o + l ≤ 31648 → 1600 ≤ o → (o + l ≤ 2368 ∨ 2400 ≤ o) →
      (o + l ≤ Layout.oVar 2 3 ∨ Layout.oVar 2 3 + 8 ≤ o) →
      (o + l ≤ Layout.oN + J * p.n ∨ Layout.oN + J * p.n + 4 * p.n ≤ o) →
      (∀ k < 4, o + l ≤ Layout.laneA k + p.n + 16 ∨ Layout.laneA k + p.n + 32 + p.n ≤ o) →
      ∀ r ∈ leafW p.n S AU J (u.gpr .rsp) stack, Region.Disjoint ⟨at' S o, l⟩ r := fun o l h₁ h₂ h₃ h₄ h₅ h₆ =>
    dW hn32 hd (by rw [hsp]; exact hstk) h₁ h₂ h₃ h₄ h₅ (by decide) (by omega_using [eN, hJn, eNS]) h₆
  have hv : ∀ i, Layout.oVar 2 i = 2704 + 8 * i := fun _ => rfl
  have kv : ∀ i, i < 9 → i ≠ 3 → u'.mem.readW (at' S (Layout.oVar 2 i)) 64 = u.mem.readW (at' S (Layout.oVar 2 i)) 64 :=
    fun i hi h3 => keepSW P.frame (keep _ _ (by rw [hv]; omega_using [hi]) (by rw [hv]; omega_using [])
      (by rw [hv]; omega_using []) (by rw [hv, hv]; omega_using [hi, h3]) (by rw [hv]; omega_using [eN, hi])
      fun k hk => .inl (by rw [hv, laneA_eq]; omega_using [hi]))
  have hL' : LS p stack S AU pkSeed a16 skSeed KP.toNat V4 U2 idx t₀ (J + 4) u' := by
    refine ⟨L.fix.trans ⟨P.cs, P.rd, P.wr, P.mx⟩, env_bytes hn32 L.env fun q hq => ?_, sk_bytes L.sk fun q h₁ h₂ => ?_,
      by rw [kv 1 (by decide) (by decide), L.v1], by rw [kv 2 (by decide) (by decide), L.v2], P.v3,
      by rw [kv 4 (by decide) (by decide), L.v4], fun i hi => ?_, fun j hj => ?_, ?_⟩
    · simp only [EnvB] at hq
      exact keepS P.frame (keep _ _ (by omega_using [hq]) (by omega_using [hq]) (by omega_using [hq])
        (by rw [hv]; omega_using [hq]) (by omega_using [hq, eN]) fun k hk => by rw [laneA_eq]; omega_using [hq, hk, hn32])
    · exact keepS P.frame (keep _ _ (by omega_using [h₂, hn32]) (by omega_using [h₁]) (by omega_using [h₁])
        (by rw [hv]; omega_using [h₁]) (by omega_using [h₂, eN, hn32]) fun k hk => .inl (by rw [laneA_eq]; omega_using [h₂, hn32]))
    · by_cases e : i < J
      · have hin : i * p.n + p.n ≤ J * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ e
        rw [keepSB P.frame (keep _ _ (by omega_using [hin, eN, hJn, eNS]) (by omega_using [eN]) (by omega_using [eN])
          (by rw [hv]; omega_using [eN]) (.inl (by omega_using [hin])) fun k hk => .inr (by rw [laneA_eq]; omega_using [hk, hn32, eN]))
          (by omega_using [hn32])]
        exact L.nodes i e
      · have e' : i = J + (i - J) := by omega_using [e]
        rw [e', P.nodes (i - J) (by omega_using [e, hi]), show V4 + U2 + J + (i - J) = V4 + U2 + (J + (i - J)) by
          omega_using []]
    · rw [P.sk j hj, L.skb j hj]
      by_cases e₁ : U2 + J ≤ idx ∧ idx < U2 + J + 4
      · rw [ite_eq_left e₁, ite_eq_right (by omega_using [e₁]), ite_eq_left (by omega_using [e₁])]
      · rw [ite_eq_right e₁]
        by_cases e₂ : U2 ≤ idx ∧ idx < U2 + J
        · rw [ite_eq_left e₂, ite_eq_left (by omega_using [e₂])]
        · rw [ite_eq_right e₂, ite_eq_right (by omega_using [e₁, e₂])]
    · refine L.frame.trans (P.frame.sub fun r hr => ?_)
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl) | hr
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨at' S Layout.oN, 32 * Layout.nodeSlots⟩, by simp, Offset.sub S (by omega_using []) (by omega_using [hJn])⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp [hsp], fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ hr, fun _ h => h⟩
  refine ⟨by rw [eval_b P.cf]; congr 1; exact decide_eq_decide.mpr (by omega_using [hJ]), fun hc => ?_, fun hc => ?_⟩
  · have : m = 1 := by have := of_decide_eq_false hc; omega_using [this, hm]
    subst this
    rw [show 2 ^ s p.a = J + 4 by omega_using [hJ]]; exact hL'
  · have := of_decide_eq_true hc
    exact ⟨by omega_using [this], J + 4, by omega_using [hJ, this], by omega_using [this], hL'⟩

/-- The loop of leaves: `2^s` leaves, four at a time. -/
theorem leaves_ok {p : Params} (T : Thash4Impl p.n) (name : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 8 ≤ stack) (hs63 : stack < 2 ^ 63) {S AU : Addr}
    {KP : BitVec 64} {V4 U2 idx : Nat} {pkSeed a16 skSeed : List Byte} {t₀ : State}
    (hbx : t₀.gpr .rbx = S) (h12 : t₀.gpr .r12 = KP) (hKP : KP.toNat < 2 ^ 32)
    (h13 : t₀.gpr .r13 = BitVec.ofNat 64 idx) (hidx : idx < 2 ^ 32)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ t₀.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (t₀.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩)
    (hX : V4 + U2 + 2 ^ s p.a < 2 ^ 32)
    (hout : ∀ w < p.n / 8, InRegions t₀.wr (AU + BitVec.ofNat 64 (8 * w)) 8)
    (hd : Region.Disjoint ⟨AU, p.n⟩ ⟨S, Layout.oSigTmp⟩) (hAs : Region.Disjoint ⟨AU, p.n⟩ (below (t₀.gpr .rsp) stack))
    {m : Nat} {t : State} (hm : 0 < m) {J : Nat} (hJ : J + 4 * m = 2 ^ s p.a)
    (hI : LS p stack S AU pkSeed a16 skSeed KP.toNat V4 U2 idx t₀ J t) :
    WP isa (.loop (leafBody ⟨p.n, p.len⟩ p.a name T.code) .b) t
      (LS p stack S AU pkSeed a16 skSeed KP.toNat V4 U2 idx t₀ (2 ^ s p.a)) :=
  Levels.wpLoop (I := LI p stack S AU pkSeed a16 skSeed KP.toNat V4 U2 idx t₀) (fun m => decide (1 < m)) (fun m => m - 1)
    (leaves_step T name hn hf hst hs63 hbx h12 hKP h13 hidx hw hS hstk hX hout hd hAs) m ⟨J, hJ, hm, hI⟩

/-! ## A call of `levels` -/

/-- The memory on entry to a call: the return address below `rsp`. -/
theorem frameCE (v : State) : Frame [below (v.gpr .rsp) 8] v.mem v.callEntry.mem := by
  rw [State.callEntry_mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- The precondition of a call of `levels`, as `lcall_ok` makes it. -/
theorem lcall_pre {p : Params} (T : Thash4Impl p.n) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {stack : Nat} (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S SG AU' : Addr} {L d h z₀ : Nat} {pkSeed a16 : List Byte} {v : State}
    (h1 : v.gpr .rdi = S) (h2 : v.gpr .rsi = at' S Layout.oN) (h3 : v.gpr .rdx = BitVec.ofNat 64 (2 ^ h))
    (h4 : v.gpr .rcx = BitVec.ofNat 64 z₀) (h5 : v.gpr .r8 = AU') (h6 : (v.gpr .r9).toNat < 2 ^ 32)
    (hh : 1 ≤ h) (hzh : z₀ + h ≤ 14) (hcnt : (2 ^ h + 8) * p.n ≤ 32 * Layout.nodeSlots)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ v.wr) (hwG : (⟨SG, L⟩ : Region) ∈ v.wr) (hAU : AU' = SG + BitVec.ofNat 64 d)
    (hdL : d + h * p.n ≤ L) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (v.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (hAf : AU'.toNat + h * p.n ≤ 2 ^ 64)
    (hAd : Region.Disjoint ⟨AU', h * p.n⟩ ⟨S, Layout.oSigTmp⟩)
    (hAs : Region.Disjoint ⟨AU', h * p.n⟩ (below (v.gpr .rsp) stack))
    (hE : Env p v.mem S pkSeed a16) (hv : ∀ i, 5 ≤ i → i ≤ 8 → (varAt v.mem S 4 i).toNat < 2 ^ 32) :
    (levelsContract p (stack - 8)).pre (v.callEntry.withRegions [] [⟨S, scratchLen⟩, ⟨AU', h * p.n⟩]) ∧
      Covers ([] ++ [⟨S, scratchLen⟩, ⟨AU', h * p.n⟩]) (v.rd ++ v.wr) ∧ Covers [⟨S, scratchLen⟩, ⟨AU', h * p.n⟩] v.wr := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  let W : List Region := [⟨S, scratchLen⟩, ⟨AU', h * p.n⟩]
  let v₀ := v.callEntry.withRegions [] W
  have hg : ∀ r, r ≠ .rsp → v₀.gpr r = v.gpr r := fun r hr => by
    simp only [v₀]; rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  have hsp₀ : v₀.gpr .rsp = v.gpr .rsp - 8 := by simp only [v₀]; rw [State.withRegions_gpr, State.callEntry_rsp]
  have hm₀ : v₀.mem = v.callEntry.mem := State.withRegions_mem _ _ _
  have h8 : (below (v.gpr .rsp) 8).Disjoint ⟨S, 2 ^ 16⟩ := hstk.sub_left (below_sub (by omega_using [hst]) (by omega_using [hs63]))
  have h8A : (below (v.gpr .rsp) 8).Disjoint ⟨AU', h * p.n⟩ :=
    hAs.symm.sub_left (below_sub (by omega_using [hst]) (by omega_using [hs63]))
  have h2h : 2 ^ h < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega_using [hzh])
  have hrdx : (BitVec.ofNat 64 (2 ^ h)).toNat = 2 ^ h := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h2h
  have hlog : heightsOf v₀ = h := by simp only [heightsOf]; rw [hg _ (by decide), h3, hrdx, Nat.log2_two_pow]
  -- the scratch on entry
  have hce : ∀ q, q < 2 ^ 16 → v.callEntry.mem (at' S q) = v.mem (at' S q) := fun q hq =>
    Levels.callEntry_byte' v h8 hq
  have hceB : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → bytesAt v.callEntry.mem (at' S o) l = bytesAt v.mem (at' S o) l :=
    fun {o l} hol => bytesAt_ext fun i hi => by rw [Levels.add_add]; exact hce _ (by omega_using [hol, hi])
  have hvar : ∀ i, i < 9 → varAt v₀.mem (v₀.gpr .rdi) 4 i = varAt v.mem S 4 i := fun i hi => by
    simp only [varAt]; rw [hg _ (by decide), h1, hm₀]
    exact Mem.readW_congr fun j hj => by
      rw [Levels.add_add]; exact hce _ (by rw [show Layout.oVar 4 i = 2960 + 8 * i from rfl]; omega_using [hi, hj])
  have hEnv₀ : Env p v.callEntry.mem S pkSeed a16 := env_bytes hn32 hE fun q hq => hce q (by
    simp only [EnvB] at hq; omega_using [hq])
  have hnodes : nodesAt p v.callEntry.mem (at' S Layout.oN) (2 ^ h) = nodesAt p v.mem (at' S Layout.oN) (2 ^ h) :=
    Levels.nodesAt_congr fun i hi => by
      have : i * p.n + p.n ≤ (2 ^ h + 8) * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_using [hi])
      rw [Levels.add_add]
      exact hceB (by rw [show Layout.oN = 12640 from rfl, show Layout.nodeSlots = 520 from rfl] at *; omega_using [this, hcnt])
  -- the precondition
  have hsub : Region.Sub ⟨AU', h * p.n⟩ ⟨SG, L⟩ := by rw [hAU]; exact Offset.sub_base SG hdL
  have hcov : Covers W v.wr := Covers.of_sub fun r hr => by
    simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hw, 0, Levels.scr0 S, by simp [scratchLen]⟩
    · exact ⟨_, hwG, d, hAU, hdL⟩
  have hret : retR v₀ = below (v.gpr .rsp) 8 := by simp [retR, hsp₀]
  have hcallee : Region.Sub (below (v₀.gpr .rsp) (stack - 8)) (below (v.gpr .rsp) stack) := by
    rw [hsp₀]
    exact fun x hx => below_sub (sp := v.gpr .rsp) (a := stack - 8 + 8) (by omega_using [hst]) (by omega_using [hs63]) x
      (below_callee _ _ x hx)
  have hpre : (levelsContract p (stack - 8)).pre v₀ := by
    refine ⟨⟨rfl, ?_, ?_, ?_, ?_, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, ?_, ?_,
      fun _ h => absurd h List.not_mem_nil, ?_, ?_, fun _ h => absurd h List.not_mem_nil⟩, ⟨pkSeed, a16, ?_⟩,
      .inl (by rw [hg _ (by decide), hg _ (by decide), h1, h2]), by rw [hlog]; exact hh,
      by rw [hlog, hg _ (by decide), h4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hzh])]; exact hzh,
      by rw [hlog, hg _ (by decide), h3, hrdx], fun _ => by rw [hg _ (by decide), h3, hrdx]; exact hcnt,
      fun e => ?_, by rw [hg _ (by decide)]; exact h6, by rw [hvar 5 (by decide)]; exact hv 5 (by decide) (by decide),
      by rw [hvar 6 (by decide)]; exact hv 6 (by decide) (by decide), by rw [hvar 7 (by decide)]; exact hv 7 (by decide) (by decide),
      by rw [hvar 8 (by decide)]; exact hv 8 (by decide) (by decide)⟩
    · simp only [v₀, State.withRegions_wr, W]; rw [hg _ (by decide), hg _ (by decide), h1, h5, hlog]
    · rw [hg _ (by decide), h1]; exact hS
    · rw [hg _ (by decide), hlog, h5]; exact hAf
    · rw [hg _ (by decide), hg _ (by decide), hlog, h5, h1]; exact hAd
    · rw [hret, hg _ (by decide), h1]; exact h8
    · rw [hret, hg _ (by decide), hlog, h5]; exact h8A
    · rw [hg .rdi (by decide), h1]; exact hstk.sub_left hcallee
    · rw [hg .r8 (by decide), hlog, h5]; exact hAs.symm.sub_left hcallee
    · rw [hg _ (by decide), hm₀, h1]; exact hEnv₀
    · rw [hg _ (by decide), hg _ (by decide), h1, h2] at e
      exact absurd e (Offset.add_ofNat_ne S (by decide) (by decide) (by decide))
  exact ⟨hpre, by rw [List.nil_append]; exact Covers.right hcov, hcov⟩

/-- A call of `levels` on the `2^h` nodes at `oN` of height `z₀`, the
authentication path at `AU'` (in the writable region `⟨SG, L⟩`), from `v`
with `stack` bytes below its stack pointer. -/
theorem lcall_ok {p : Params} (T : Thash4Impl p.n) (name ln : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S SG AU' : Addr} {L d h z₀ : Nat} {pkSeed a16 : List Byte} {v : State}
    (h1 : v.gpr .rdi = S) (h2 : v.gpr .rsi = at' S Layout.oN) (h3 : v.gpr .rdx = BitVec.ofNat 64 (2 ^ h))
    (h4 : v.gpr .rcx = BitVec.ofNat 64 z₀) (h5 : v.gpr .r8 = AU') (h6 : (v.gpr .r9).toNat < 2 ^ 32)
    (hh : 1 ≤ h) (hzh : z₀ + h ≤ 14) (hcnt : (2 ^ h + 8) * p.n ≤ 32 * Layout.nodeSlots)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ v.wr) (hwG : (⟨SG, L⟩ : Region) ∈ v.wr) (hAU : AU' = SG + BitVec.ofNat 64 d)
    (hdL : d + h * p.n ≤ L) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (v.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (hAf : AU'.toNat + h * p.n ≤ 2 ^ 64)
    (hAd : Region.Disjoint ⟨AU', h * p.n⟩ ⟨S, Layout.oSigTmp⟩)
    (hAs : Region.Disjoint ⟨AU', h * p.n⟩ (below (v.gpr .rsp) stack))
    (hE : Env p v.mem S pkSeed a16) (hv : ∀ i, 5 ≤ i → i ≤ 8 → (varAt v.mem S 4 i).toNat < 2 ^ 32) {Q : State → Prop}
    (hQ : ∀ v', Fix v v' → Env p v'.mem S pkSeed a16 →
      bytesAt v'.mem (at' S Layout.oN) p.n = (upNodes p pkSeed a16 (varAt v.mem S 4 7).toNat (varAt v.mem S 4 8).toNat
        (varAt v.mem S 4 6).toNat z₀ (nodesAt p v.mem (at' S Layout.oN) (2 ^ h)) h).getD 0 [] →
      (∀ r < h, bytesAt v'.mem (AU' + BitVec.ofNat 64 (r * p.n)) p.n =
        xorB (bytesAt v.mem (AU' + BitVec.ofNat 64 (r * p.n)) p.n)
          (pick p.n (upNodes p pkSeed a16 (varAt v.mem S 4 7).toNat (varAt v.mem S 4 8).toNat (varAt v.mem S 4 6).toNat z₀
            (nodesAt p v.mem (at' S Layout.oN) (2 ^ h)) r) ((varAt v.mem S 4 5).toNat / 2 ^ (z₀ + r))
            (v.gpr .r9).toNat (z₀ + r))) →
      Frame (levelsChanges p S (at' S Layout.oN) (2 ^ h) ++ [⟨AU', h * p.n⟩, below (v.gpr .rsp) stack]) v.mem v'.mem →
      Q v') :
    WP isa (.call ln (Impl.SlhDsa.X86_64.Tree.levels ⟨p.n, p.len⟩ name T.code)) v Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  let W : List Region := [⟨S, scratchLen⟩, ⟨AU', h * p.n⟩]
  let v₀ := v.callEntry.withRegions [] W
  have hg : ∀ r, r ≠ .rsp → v₀.gpr r = v.gpr r := fun r hr => by
    simp only [v₀]; rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  have hsp₀ : v₀.gpr .rsp = v.gpr .rsp - 8 := by simp only [v₀]; rw [State.withRegions_gpr, State.callEntry_rsp]
  have hm₀ : v₀.mem = v.callEntry.mem := State.withRegions_mem _ _ _
  have h8 : (below (v.gpr .rsp) 8).Disjoint ⟨S, 2 ^ 16⟩ := hstk.sub_left (below_sub (by omega_using [hst]) (by omega_using [hs63]))
  have h8A : (below (v.gpr .rsp) 8).Disjoint ⟨AU', h * p.n⟩ :=
    hAs.symm.sub_left (below_sub (by omega_using [hst]) (by omega_using [hs63]))
  have h2h : 2 ^ h < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega_using [hzh])
  have hrdx : (BitVec.ofNat 64 (2 ^ h)).toNat = 2 ^ h := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h2h
  have hlog : heightsOf v₀ = h := by simp only [heightsOf]; rw [hg _ (by decide), h3, hrdx, Nat.log2_two_pow]
  -- the scratch on entry
  have hce : ∀ q, q < 2 ^ 16 → v.callEntry.mem (at' S q) = v.mem (at' S q) := fun q hq =>
    Levels.callEntry_byte' v h8 hq
  have hceB : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → bytesAt v.callEntry.mem (at' S o) l = bytesAt v.mem (at' S o) l :=
    fun {o l} hol => bytesAt_ext fun i hi => by rw [Levels.add_add]; exact hce _ (by omega_using [hol, hi])
  have hvar : ∀ i, i < 9 → varAt v₀.mem (v₀.gpr .rdi) 4 i = varAt v.mem S 4 i := fun i hi => by
    simp only [varAt]; rw [hg _ (by decide), h1, hm₀]
    exact Mem.readW_congr fun j hj => by
      rw [Levels.add_add]; exact hce _ (by rw [show Layout.oVar 4 i = 2960 + 8 * i from rfl]; omega_using [hi, hj])
  have hEnv₀ : Env p v.callEntry.mem S pkSeed a16 := env_bytes hn32 hE fun q hq => hce q (by
    simp only [EnvB] at hq; omega_using [hq])
  have hnodes : nodesAt p v.callEntry.mem (at' S Layout.oN) (2 ^ h) = nodesAt p v.mem (at' S Layout.oN) (2 ^ h) :=
    Levels.nodesAt_congr fun i hi => by
      have : i * p.n + p.n ≤ (2 ^ h + 8) * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_using [hi])
      rw [Levels.add_add]
      exact hceB (by rw [show Layout.oN = 12640 from rfl, show Layout.nodeSlots = 520 from rfl] at *; omega_using [this, hcnt])
  -- the precondition
  have hsub : Region.Sub ⟨AU', h * p.n⟩ ⟨SG, L⟩ := by rw [hAU]; exact Offset.sub_base SG hdL
  have hcov : Covers W v.wr := Covers.of_sub fun r hr => by
    simp only [W, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hw, 0, Levels.scr0 S, by simp [scratchLen]⟩
    · exact ⟨_, hwG, d, hAU, hdL⟩
  have hret : retR v₀ = below (v.gpr .rsp) 8 := by simp [retR, hsp₀]
  have hcallee : Region.Sub (below (v₀.gpr .rsp) (stack - 8)) (below (v.gpr .rsp) stack) := by
    rw [hsp₀]
    exact fun x hx => below_sub (sp := v.gpr .rsp) (a := stack - 8 + 8) (by omega_using [hst]) (by omega_using [hs63]) x
      (below_callee _ _ x hx)
  have hpre : (levelsContract p (stack - 8)).pre v₀ := by
    refine ⟨⟨rfl, ?_, ?_, ?_, ?_, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil, ?_, ?_,
      fun _ h => absurd h List.not_mem_nil, ?_, ?_, fun _ h => absurd h List.not_mem_nil⟩, ⟨pkSeed, a16, ?_⟩,
      .inl (by rw [hg _ (by decide), hg _ (by decide), h1, h2]), by rw [hlog]; exact hh,
      by rw [hlog, hg _ (by decide), h4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hzh])]; exact hzh,
      by rw [hlog, hg _ (by decide), h3, hrdx], fun _ => by rw [hg _ (by decide), h3, hrdx]; exact hcnt,
      fun e => ?_, by rw [hg _ (by decide)]; exact h6, by rw [hvar 5 (by decide)]; exact hv 5 (by decide) (by decide),
      by rw [hvar 6 (by decide)]; exact hv 6 (by decide) (by decide), by rw [hvar 7 (by decide)]; exact hv 7 (by decide) (by decide),
      by rw [hvar 8 (by decide)]; exact hv 8 (by decide) (by decide)⟩
    · simp only [v₀, State.withRegions_wr, W]; rw [hg _ (by decide), hg _ (by decide), h1, h5, hlog]
    · rw [hg _ (by decide), h1]; exact hS
    · rw [hg _ (by decide), hlog, h5]; exact hAf
    · rw [hg _ (by decide), hg _ (by decide), hlog, h5, h1]; exact hAd
    · rw [hret, hg _ (by decide), h1]; exact h8
    · rw [hret, hg _ (by decide), hlog, h5]; exact h8A
    · rw [hg .rdi (by decide), h1]; exact hstk.sub_left hcallee
    · rw [hg .r8 (by decide), hlog, h5]; exact hAs.symm.sub_left hcallee
    · rw [hg _ (by decide), hm₀, h1]; exact hEnv₀
    · rw [hg _ (by decide), hg _ (by decide), h1, h2] at e
      exact absurd e (Offset.add_ofNat_ne S (by decide) (by decide) (by decide))
  refine Levels.levelscall_ok T name ln hn hf (stack := stack - 8) (by omega_using [hst]) (by omega_using [hs63])
    (rd := []) (wr := W) hpre (by rw [List.nil_append]; exact Covers.right hcov) hcov
    fun v' hrd hwr hcs _ ⟨s₂, hm₂, _, hpost⟩ hmx => ?_
  rw [show v.callEntry.withRegions [] W = v₀ from rfl] at hpost
  obtain ⟨e₁, e₂, e₃, e₄⟩ := hpost pkSeed a16 (by rw [hg _ (by decide), h1, hm₀]; exact hEnv₀)
  simp only [hg _ (by decide : Reg.rdi ≠ .rsp), hg _ (by decide : Reg.rsi ≠ .rsp), hg _ (by decide : Reg.rdx ≠ .rsp),
    hg _ (by decide : Reg.rcx ≠ .rsp), hg _ (by decide : Reg.r8 ≠ .rsp), hg _ (by decide : Reg.r9 ≠ .rsp), hlog, hm₀,
    h1, h2, h3, h4, h5, hrdx, hm₂] at e₁ e₂ e₃ e₄
  have hvar' : ∀ i, i < 9 → varAt v.callEntry.mem S 4 i = varAt v.mem S 4 i := fun i hi => by
    have := hvar i hi; rwa [hg _ (by decide), h1, hm₀] at this
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hzh])] at e₂ e₃
  rw [hvar' 6 (by decide), hvar' 7 (by decide), hvar' 8 (by decide), hnodes] at e₂
  rw [hvar' 5 (by decide), hvar' 6 (by decide), hvar' 7 (by decide), hvar' 8 (by decide), hnodes] at e₃
  refine hQ v' ⟨hcs, hrd, hwr, hmx⟩ e₁ e₂ (fun r hr => ?_) ?_
  · rw [e₃ r hr]
    congr 1
    refine bytesAt_ext fun i hi => ?_
    have hrn : r * p.n + p.n ≤ h * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hr
    rw [Levels.add_add]
    exact Proof.Sha3.X86_64.callEntry_byte v h8A (show h * p.n ≤ 2 ^ 64 by omega_using [hAf])
      (show r * p.n + i < h * p.n by omega_using [hrn, hi])
  · have f₁ := frameCE v
    rw [hsp₀] at e₄
    refine (f₁.sub fun r hr => ?_).trans (e₄.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below (v.gpr .rsp) stack, by simp, below_sub (by omega_using [hst]) (by omega_using [hs63])⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨below (v.gpr .rsp) stack, by simp, fun x hx => below_sub (sp := v.gpr .rsp) (a := stack - 8 + 8)
            (by omega_using [hst]) (by omega_using [hs63]) x (below_callee _ _ x hx)⟩

/-! ## The parameters of `levels` -/

/-- `mov r64, imm32`, which sign-extends. -/
theorem wp_movi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Proof.Sha3.X86_64.Upd s s' d (v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  Proof.Sha3.X86_64.WP.cons rfl (k _ (Proof.Sha3.X86_64.Upd.setReg _ _ _))

theorem oVar4 (i : Nat) : Layout.oVar 4 i = 2960 + 8 * i := rfl

/-- The four stores of `setParams`, of `V5` to `V8` (`rax` set to each in turn). -/
theorem stores_val {m : Mem} {S : Addr} (V5 V6 V7 V8 : BitVec 64) :
    let m' := (((m.writeW (at' S (Layout.oVar 4 5)) V5).writeW (at' S (Layout.oVar 4 6)) V6).writeW
      (at' S (Layout.oVar 4 7)) V7).writeW (at' S (Layout.oVar 4 8)) V8
    m'.readW (at' S (Layout.oVar 4 5)) 64 = V5 ∧ m'.readW (at' S (Layout.oVar 4 6)) 64 = V6 ∧
      m'.readW (at' S (Layout.oVar 4 7)) 64 = V7 ∧ m'.readW (at' S (Layout.oVar 4 8)) 64 = V8 ∧
      Frame [⟨at' S (Layout.oVar 4 5), 32⟩] m m' := by
  have sp : ∀ i j, i ≠ j → i < 9 → j < 9 → Mem.Sep (at' S (Layout.oVar 4 i)) (64 / 8) (at' S (Layout.oVar 4 j)) (64 / 8) :=
    fun i j h hi hj => Offset.sep S (by rw [oVar4, oVar4]; omega_using [h]) (by rw [oVar4]; omega_using [hi])
      (by rw [oVar4]; omega_using [hj])
  intro m'
  refine ⟨?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _, ?_⟩
  · rw [Mem.readW_writeW_sep (sp 5 8 (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sp 5 7 (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sp 5 6 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sp 6 8 (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (sp 6 7 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sp 7 8 (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · have c : ∀ i, 5 ≤ i → i ≤ 8 → (⟨at' S (Layout.oVar 4 5), 32⟩ : Region).Contains (at' S (Layout.oVar 4 i)) (64 / 8) :=
      fun i h₁ h₂ => by
        rw [show at' S (Layout.oVar 4 i) = at' S (Layout.oVar 4 5) + BitVec.ofNat 64 (8 * (i - 5)) by
          rw [Levels.add_add, oVar4, oVar4, show 2960 + 8 * 5 + 8 * (i - 5) = 2960 + 8 * i by omega_using [h₁]]]
        exact Offset.contains_base _ (by omega_using [h₂, h₁]) (by omega_using [h₂])
    exact ((((Frame.refl _ m).writeW (List.mem_singleton_self _) _ (c 5 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (c 6 (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (c 7 (by decide) (by decide))).writeW (List.mem_singleton_self _) _ (c 8 (by decide) (by decide))

/-- What the block before a call of `levels` leaves. -/
structure LB (n : Nat) (S : Addr) (u u' : State) (cnt z₀ : Nat) (AU' : Addr) (V5 V6 V7 V8 : BitVec 64) : Prop where
  gpr : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .rdi → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 →
    u'.gpr g = u.gpr g
  rdi : u'.gpr .rdi = S
  rsi : u'.gpr .rsi = at' S Layout.oN
  rdx : u'.gpr .rdx = BitVec.ofNat 64 cnt
  rcx : u'.gpr .rcx = BitVec.ofNat 64 z₀
  r8 : u'.gpr .r8 = AU'
  r9 : u'.gpr .r9 = u.gpr .r13
  rd : u'.rd = u.rd
  wr : u'.wr = u.wr
  mx : u'.mxcsr = u.mxcsr
  v5 : u'.mem.readW (at' S (Layout.oVar 4 5)) 64 = V5
  v6 : u'.mem.readW (at' S (Layout.oVar 4 6)) 64 = V6
  v7 : u'.mem.readW (at' S (Layout.oVar 4 7)) 64 = V7
  v8 : u'.mem.readW (at' S (Layout.oVar 4 8)) 64 = V8
  frame : Frame [⟨at' S (Layout.oVar 4 5), 32⟩] u.mem u'.mem

theorem setW (x : Nat) (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).setWidth 64 = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega_using [h]

/-- The block before the call of `levels` for a subtree: `capBase = U2`,
`adrsBase = V4 + U2`, `FORS_TREE`, `kp`; the `2^s` nodes at `oN` from height 0,
the path at `AU + n`. -/
theorem subB_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S AU : Addr} {U2 V4 : Nat} {u : State}
    (hbx : u.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr)
    (h1 : u.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU)
    (h2 : u.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2)
    (h4 : u.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 V4) :
    WP isa (.block (([.mov .r10 (.mem (var 1)), .alu .add .r10 (.imm (BitVec.ofNat 32 (⟨p.n, p.len⟩ : Layout).n)),
        .mov .rcx (.mem (var 4)), .alu .add .rcx (.mem (var 2))] : List Instr) ++
        Impl.SlhDsa.X86_64.Tree.setParams (.mem (var 2)) (.reg .rcx) (.imm 3) (.reg .r12) ++
        ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 Layout.oN)),
          .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ s p.a))), .mov32 .rcx (.imm 0),
          .mov .r8 (.reg .r10), .mov .r9 (.reg .r13)] : List Instr))) u
      fun u' => LB p.n S u u' (2 ^ s p.a) 0 (AU + BitVec.ofNat 64 p.n) (BitVec.ofNat 64 U2) (BitVec.ofNat 64 (V4 + U2))
        (BitVec.ofNat 64 3) (u.gpr .r12) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hs9 : s p.a ≤ 9 := Nat.min_le_right _ _
  have h512 : 2 ^ s p.a ≤ 512 := by
    calc 2 ^ s p.a ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hs9
      _ = 512 := rfl
  have hin : ∀ (t : State), t.rd = u.rd → t.wr = u.wr → ∀ f i, f < 5 → i < 9 →
      InRegions (t.rd ++ t.wr) (at' S (Layout.oVar f i)) 8 := fun t hr hw' f i hf hi => by
    rw [hr, hw']; exact Levels.in_scr' hw (by simp only [Layout.oVar, Layout.oFrame, Layout.oVars]; omega_using [hf, hi])
  refine WP.mono_mx (by simp [Code.allInstrs_eq, instrs, Impl.SlhDsa.X86_64.Tree.setParams, loadsMxcsr])
    (Q := fun u' => u'.mxcsr = u.mxcsr → LB p.n S u u' (2 ^ s p.a) 0 (AU + BitVec.ofNat 64 p.n) (BitVec.ofNat 64 U2)
      (BitVec.ofNat 64 (V4 + U2)) (BitVec.ofNat 64 3) (u.gpr .r12)) ?_ fun _ h hm => h hm
  simp only [Impl.SlhDsa.X86_64.Tree.setParams, Impl.SlhDsa.X86_64.Tree.var, List.cons_append, List.nil_append]
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 1)) (by rw [var, Proof.Sha3.X86_64.ea_at, hbx])
    (hin u rfl rfl 2 1 (by decide) (by decide)) fun u₁ e₁ => ?_
  refine Proof.Sha3.X86_64.wp_addi fun u₂ e₂ => ?_
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 4))
    (by rw [var, Proof.Sha3.X86_64.ea_at, e₂.other _ (by decide), e₁.other _ (by decide), hbx])
    (hin u₂ (by rw [e₂.rd, e₁.rd]) (by rw [e₂.wr, e₁.wr]) 2 4 (by decide) (by decide)) fun u₃ e₃ => ?_
  refine wp_addm (a := at' S (Layout.oVar 2 2))
    (by rw [var, Proof.Sha3.X86_64.ea_at, e₃.other _ (by decide), e₂.other _ (by decide), e₁.other _ (by decide), hbx])
    (hin u₃ (by rw [e₃.rd, e₂.rd, e₁.rd]) (by rw [e₃.wr, e₂.wr, e₁.wr]) 2 2 (by decide) (by decide)) fun u₄ e₄ => ?_
  have hm₄ : u₄.mem = u.mem := by rw [e₄.mem, e₃.mem, e₂.mem, e₁.mem]
  have hb₄ : u₄.gpr .rbx = S := by
    rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.other _ (by decide), e₁.other _ (by decide), hbx]
  have hr₄ : u₄.rd = u.rd := by rw [e₄.rd, e₃.rd, e₂.rd, e₁.rd]
  have hw₄ : u₄.wr = u.wr := by rw [e₄.wr, e₃.wr, e₂.wr, e₁.wr]
  have hcx : u₄.gpr .rcx = BitVec.ofNat 64 (V4 + U2) := by
    rw [e₄.gpr, e₃.gpr, e₃.mem, e₂.mem, e₁.mem, h4, h2, BitVec.ofNat_add_ofNat]
  have h10 : u₄.gpr .r10 = AU + BitVec.ofNat 64 p.n := by
    rw [e₄.other _ (by decide), e₃.other _ (by decide), e₂.gpr, e₁.gpr, h1, Levels.sx_ofNat (by omega_using [hn32])]
  -- the parameters
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 2)) (by rw [var, Proof.Sha3.X86_64.ea_at, hb₄])
    (hin u₄ hr₄ hw₄ 2 2 (by decide) (by decide)) fun u₅ e₅ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 4 5)) (by rw [Proof.Sha3.X86_64.ea_at, e₅.other _ (by decide), hb₄])
    (by rw [e₅.wr, hw₄]; exact Levels.in_scr hw (by rw [oVar4]; omega_using [])) fun u₆ g₆ m₆ r₆ w₆ => ?_
  refine Proof.Sha3.X86_64.wp_mov fun u₇ e₇ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 4 6))
    (by rw [Proof.Sha3.X86_64.ea_at, e₇.other _ (by decide), g₆, e₅.other _ (by decide), hb₄])
    (by rw [e₇.wr, w₆, e₅.wr, hw₄]; exact Levels.in_scr hw (by rw [oVar4]; omega_using [])) fun u₈ g₈ m₈ r₈ w₈ => ?_
  refine wp_movi fun u₉ e₉ => ?_
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 4 7))
    (by rw [Proof.Sha3.X86_64.ea_at, e₉.other _ (by decide), g₈, e₇.other _ (by decide), g₆, e₅.other _ (by decide), hb₄])
    (by rw [e₉.wr, w₈, e₇.wr, w₆, e₅.wr, hw₄]; exact Levels.in_scr hw (by rw [oVar4]; omega_using []))
    fun u₁₀ g₁₀ m₁₀ r₁₀ w₁₀ => ?_
  refine Proof.Sha3.X86_64.wp_mov fun u₁₁ e₁₁ => ?_
  have hb₁₁ : u₁₁.gpr .rbx = S := by
    rw [e₁₁.other _ (by decide), g₁₀, e₉.other _ (by decide), g₈, e₇.other _ (by decide), g₆, e₅.other _ (by decide), hb₄]
  refine Proof.Sha3.X86_64.wp_store (a := at' S (Layout.oVar 4 8)) (by rw [Proof.Sha3.X86_64.ea_at, hb₁₁])
    (by rw [e₁₁.wr, w₁₀, e₉.wr, w₈, e₇.wr, w₆, e₅.wr, hw₄]; exact Levels.in_scr hw (by rw [oVar4]; omega_using []))
    fun u₁₂ g₁₂ m₁₂ r₁₂ w₁₂ => ?_
  -- the arguments
  refine Proof.Sha3.X86_64.wp_mov fun u₁₃ e₁₃ => Proof.Sha3.X86_64.wp_mov fun u₁₄ e₁₄ =>
    Proof.Sha3.X86_64.wp_addi fun u₁₅ e₁₅ => Proof.Sha3.X86_64.wp_mov32i fun u₁₆ e₁₆ =>
    Proof.Sha3.X86_64.wp_mov32i fun u₁₇ e₁₇ => Proof.Sha3.X86_64.wp_mov fun u₁₈ e₁₈ =>
    Proof.Sha3.X86_64.wp_mov fun u₁₉ e₁₉ => WP.block_nil fun hmx => ?_
  -- the registers through the steps
  have G : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .rdi → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 →
      u₁₂.gpr g = u.gpr g := fun g h₀ h₁ _ _ _ _ _ h₇ => by
    rw [g₁₂, e₁₁.other _ h₀, g₁₀, e₉.other _ h₀, g₈, e₇.other _ h₀, g₆, e₅.other _ h₀, e₄.other _ h₁, e₃.other _ h₁,
      e₂.other _ h₇, e₁.other _ h₇]
  have hm₁₂ : u₁₂.mem = (((u.mem.writeW (at' S (Layout.oVar 4 5)) (BitVec.ofNat 64 U2)).writeW (at' S (Layout.oVar 4 6))
      (BitVec.ofNat 64 (V4 + U2))).writeW (at' S (Layout.oVar 4 7)) (BitVec.ofNat 64 3)).writeW
      (at' S (Layout.oVar 4 8)) (u.gpr .r12) := by
    rw [m₁₂, e₁₁.mem, m₁₀, e₉.mem, m₈, e₇.mem, m₆, e₅.mem, hm₄, e₁₁.gpr, g₁₀, e₉.other .r12 (by decide), g₈,
      e₇.other .r12 (by decide), g₆, e₅.other .r12 (by decide), e₄.other .r12 (by decide), e₃.other .r12 (by decide),
      e₂.other .r12 (by decide), e₁.other .r12 (by decide), e₉.gpr,
      show BitVec.signExtend 64 (3 : BitVec 32) = BitVec.ofNat 64 3 by decide, e₇.gpr, g₆,
      e₅.other .rcx (by decide), hcx, e₅.gpr, hm₄, h2]
  obtain ⟨s5, s6, s7, s8, sf⟩ := stores_val (m := u.mem) (S := S) (BitVec.ofNat 64 U2) (BitVec.ofNat 64 (V4 + U2))
    (BitVec.ofNat 64 3) (u.gpr .r12)
  have hm₁₉ : u₁₉.mem = u₁₂.mem := by rw [e₁₉.mem, e₁₈.mem, e₁₇.mem, e₁₆.mem, e₁₅.mem, e₁₄.mem, e₁₃.mem]
  refine ⟨fun g h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmx, by rw [hm₁₉, hm₁₂]; exact s5,
    by rw [hm₁₉, hm₁₂]; exact s6, by rw [hm₁₉, hm₁₂]; exact s7, by rw [hm₁₉, hm₁₂]; exact s8, by rw [hm₁₉, hm₁₂]; exact sf⟩
  · rw [e₁₉.other _ h₆, e₁₈.other _ h₅, e₁₇.other _ h₁, e₁₆.other _ h₂, e₁₅.other _ h₃, e₁₄.other _ h₃, e₁₃.other _ h₄,
      G g h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇]
  · rw [e₁₉.other _ (by decide), e₁₈.other _ (by decide), e₁₇.other _ (by decide), e₁₆.other _ (by decide),
      e₁₅.other _ (by decide), e₁₄.other _ (by decide), e₁₃.gpr, g₁₂, hb₁₁]
  · rw [e₁₉.other _ (by decide), e₁₈.other _ (by decide), e₁₇.other _ (by decide), e₁₆.other _ (by decide),
      e₁₅.gpr, e₁₄.gpr, e₁₃.other _ (by decide), g₁₂, hb₁₁, Levels.sx_ofNat (by decide)]
  · rw [e₁₉.other _ (by decide), e₁₈.other _ (by decide), e₁₇.other _ (by decide), e₁₆.gpr,
      setW _ (by omega_using [h512])]
  · rw [e₁₉.other _ (by decide), e₁₈.other _ (by decide), e₁₇.gpr]; rfl
  · rw [e₁₉.other _ (by decide), e₁₈.gpr, e₁₇.other _ (by decide), e₁₆.other _ (by decide), e₁₅.other _ (by decide),
      e₁₄.other _ (by decide), e₁₃.other _ (by decide), g₁₂, e₁₁.other _ (by decide), g₁₀, e₉.other _ (by decide), g₈,
      e₇.other _ (by decide), g₆, e₅.other _ (by decide), h10]
  · rw [e₁₉.gpr, e₁₈.other _ (by decide), e₁₇.other _ (by decide), e₁₆.other _ (by decide), e₁₅.other _ (by decide),
      e₁₄.other _ (by decide), e₁₃.other _ (by decide), G _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
  · rw [e₁₉.rd, e₁₈.rd, e₁₇.rd, e₁₆.rd, e₁₅.rd, e₁₄.rd, e₁₃.rd, r₁₂, e₁₁.rd, r₁₀, e₉.rd, r₈, e₇.rd, r₆, e₅.rd, hr₄]
  · rw [e₁₉.wr, e₁₈.wr, e₁₇.wr, e₁₆.wr, e₁₅.wr, e₁₄.wr, e₁₃.wr, w₁₂, e₁₁.wr, w₁₀, e₉.wr, w₈, e₇.wr, w₆, e₅.wr, hw₄]

theorem shr_ofNat {x : Nat} (hx : x < 2 ^ 64) (k : Nat) : BitVec.ofNat 64 x >>> k = BitVec.ofNat 64 (x / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by have := Nat.div_le_self x (2 ^ k); omega_using [this, hx])]

theorem rootCopy_nm (L : Layout) (k : Nat) : (([.mov .rdx (.mem (var 2)), .shift .shr .rdx k] : List Instr) ++
    Impl.SlhDsa.X86_64.Wots.mulN L.n .rdx .rcx ++ ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
    copyWords .rdx Layout.oRoots .rbx Layout.oN (L.n / 8) : List Instr).all (fun i => !loadsMxcsr i) = true := by
  simp only [List.all_append, mulN_nm, copyWords_nm]
  simp [loadsMxcsr]

/-- The root of a subtree, node 0 at `oN`, to subtree root `R` at `oRoots`
(`R` from variable 2, `U2 = R·2^s`). -/
theorem rootCopy_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) {S : Addr} {U2 : Nat} {u : State}
    (hbx : u.gpr .rbx = S) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr) (h2 : u.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2)
    (hU : U2 < 2 ^ 32) (hR : U2 / 2 ^ s p.a < 32) (hs1 : 1 ≤ s p.a) :
    WP isa (.block (([.mov .rdx (.mem (var 2)), .shift .shr .rdx (s p.a)] : List Instr) ++
        Impl.SlhDsa.X86_64.Wots.mulN (⟨p.n, p.len⟩ : Layout).n .rdx .rcx ++ ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
        copyWords .rdx Layout.oRoots .rbx Layout.oN ((⟨p.n, p.len⟩ : Layout).n / 8))) u fun u' =>
      (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → u'.gpr g = u.gpr g) ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.mxcsr = u.mxcsr ∧
      bytesAt u'.mem (at' S (Layout.oRoots + U2 / 2 ^ s p.a * p.n)) p.n = bytesAt u.mem (at' S Layout.oN) p.n ∧
      Frame [⟨at' S (Layout.oRoots + U2 / 2 ^ s p.a * p.n), p.n⟩] u.mem u'.mem := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hs9 : s p.a ≤ 9 := Nat.min_le_right _ _
  have eR : Layout.oRoots = 29280 := rfl
  have hRn : (U2 / 2 ^ s p.a + 1) * p.n ≤ 32 * 32 := Nat.mul_le_mul (by omega_using [hR]) hn32
  have hRn' : (U2 / 2 ^ s p.a + 1) * p.n = U2 / 2 ^ s p.a * p.n + p.n := Nat.succ_mul _ _
  refine WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using rootCopy_nm ⟨p.n, p.len⟩ (s p.a))
    (Q := fun u' => u'.mxcsr = u.mxcsr → _) ?_ fun _ h hm => h hm
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine Proof.Sha3.X86_64.wp_movm (a := at' S (Layout.oVar 2 2)) (by rw [var, Proof.Sha3.X86_64.ea_at, hbx])
    (Levels.in_scr' hw (by rw [oVar2]; omega_using [])) fun u₁ e₁ => ?_
  refine Levels.wp_shr hs1 (by omega_using [hs9]) fun u₂ e₂ => ?_
  refine Levels.mulN_ok hn (by decide) fun u₃ h₃ g₃ m₃ r₃ w₃ => ?_
  refine Levels.wp_add fun u₄ e₄ => ?_
  have hdx : u₄.gpr .rdx = at' S (U2 / 2 ^ s p.a * p.n) := by
    rw [e₄.gpr, h₃, e₂.gpr, e₁.gpr, h2, shr_ofNat (by omega_using [hU]), BitVec.ofNat_mul_ofNat,
      g₃ _ (by decide) (by decide), e₂.other _ (by decide), e₁.other _ (by decide), hbx, BitVec.add_comm]
  have hb₄ : u₄.gpr .rbx = S := by
    rw [e₄.other _ (by decide), g₃ _ (by decide) (by decide), e₂.other _ (by decide), e₁.other _ (by decide), hbx]
  have hm₄ : u₄.mem = u.mem := by rw [e₄.mem, m₃, e₂.mem, e₁.mem]
  have hw₄ : u₄.wr = u.wr := by rw [e₄.wr, w₃, e₂.wr, e₁.wr]
  refine WP.mono (Levels.copy_ok (S := S) (a := U2 / 2 ^ s p.a * p.n) (b := 0) (d₁ := Layout.oN) (d₂ := Layout.oRoots)
    (by decide) (by decide) (p.n / 8) u₄ hdx (by rw [hb₄]; exact Levels.scr0 S) (by rw [hw₄]; exact hw)
    (by rw [show Layout.oN = 12640 from rfl]; omega_using [e8, hn32]) (by omega_using [e8, eR, hRn, hRn'])
    (by rw [show Layout.oN = 12640 from rfl]; omega_using [e8, eR, hn32])) fun u' ⟨g', r', w', c', f'⟩ hmx => ?_
  rw [e8] at c' f'
  refine ⟨fun g h₀ h₁ h₂ => by rw [g' _ h₀, e₄.other _ h₂, g₃ _ h₂ h₁, e₂.other _ h₂, e₁.other _ h₂],
    by rw [r', e₄.rd, r₃, e₂.rd, e₁.rd], by rw [w', hw₄], hmx, ?_, ?_⟩
  · rw [← hm₄]
    refine bytesAt_ext fun i hi => ?_
    rw [Levels.add_add, Levels.add_add, show Layout.oRoots + U2 / 2 ^ s p.a * p.n + i =
      U2 / 2 ^ s p.a * p.n + Layout.oRoots + i by omega_using [], c' i hi, Nat.zero_add]
  · rw [hm₄, show U2 / 2 ^ s p.a * p.n + Layout.oRoots = Layout.oRoots + U2 / 2 ^ s p.a * p.n by omega_using []] at f'
    exact f'

/-! ## The heights of a subtree -/

/-- What a subtree's heights leave. -/
structure SubHP (p : Params) (S AU : Addr) (stack : Nat) (pkSeed a16 skSeed : List Byte) (kp V4 U2 idx : Nat)
    (u u' : State) : Prop where
  fix : Fix u u'
  env : Env p u'.mem S pkSeed a16
  root : bytesAt u'.mem (at' S (Layout.oRoots + U2 / 2 ^ s p.a * p.n)) p.n =
    node p skSeed pkSeed a16 kp ((V4 + U2) / 2 ^ s p.a) (s p.a)
  auth : ∀ r < s p.a, bytesAt u'.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
    xorB (bytesAt u.mem (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n)
      (if U2 / 2 ^ r ≤ sib idx r ∧ sib idx r < U2 / 2 ^ r + 2 ^ (s p.a - r) then
        node p skSeed pkSeed a16 kp (V4 / 2 ^ r + sib idx r) r else toByte 0 p.n)
  frame : Frame (levelsChanges p S (at' S Layout.oN) (2 ^ s p.a) ++
    [⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩, below (u.gpr .rsp) stack,
      ⟨at' S (Layout.oRoots + U2 / 2 ^ s p.a * p.n), p.n⟩]) u.mem u'.mem

theorem div_add_dvd {a b c : Nat} (h : c ∣ a) : (a + b) / c = a / c + b / c := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  obtain ⟨d, rfl⟩ := h
  rw [Nat.mul_add_div hc, Nat.mul_div_cancel_left _ hc]

theorem subHeights_ok {p : Params} (T : Thash4Impl p.n) (name ln : String) (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32)
    (hf : p.family = .shake) {stack : Nat} (hst : T.stack + 24 ≤ stack) (hs63 : stack < 2 ^ 63)
    {S SG AU : Addr} {L dA U2 V4 idx : Nat} {pkSeed a16 skSeed : List Byte} {u : State}
    (hbx : u.gpr .rbx = S) (hKP : (u.gpr .r12).toNat < 2 ^ 32) (h13 : u.gpr .r13 = BitVec.ofNat 64 idx)
    (hidx : idx < 2 ^ 32) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr) (hwG : (⟨SG, L⟩ : Region) ∈ u.wr)
    (hAU : AU = SG + BitVec.ofNat 64 dA) (hdA : dA + p.n + s p.a * p.n ≤ L) (hGf : SG.toNat + L ≤ 2 ^ 64)
    (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64) (hstk : (below (u.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩)
    (hGd : Region.Disjoint ⟨SG, L⟩ ⟨S, Layout.oSigTmp⟩) (hGs : Region.Disjoint ⟨SG, L⟩ (below (u.gpr .rsp) stack))
    (hE : Env p u.mem S pkSeed a16)
    (h1 : u.mem.readW (at' S (Layout.oVar 2 1)) 64 = AU)
    (h2 : u.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2)
    (h4 : u.mem.readW (at' S (Layout.oVar 2 4)) 64 = BitVec.ofNat 64 V4)
    (hX : V4 + U2 < 2 ^ 32) (hdv4 : 2 ^ s p.a ∣ V4) (hdv2 : 2 ^ s p.a ∣ U2) (hR : U2 / 2 ^ s p.a < 32)
    (hs6 : 6 ≤ s p.a)
    (hN : ∀ i < 2 ^ s p.a, bytesAt u.mem (at' S (Layout.oN + i * p.n)) p.n =
      node p skSeed pkSeed a16 (u.gpr .r12).toNat (V4 + U2 + i) 0) :
    WP isa (subtreeHeights ⟨p.n, p.len⟩ p.a name ln T.code) u
      (SubHP p S AU stack pkSeed a16 skSeed (u.gpr .r12).toNat V4 U2 idx u) := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hs9 : s p.a ≤ 9 := Nat.min_le_right _ _
  have h512 : 2 ^ s p.a ≤ 512 := by
    calc 2 ^ s p.a ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hs9
      _ = 512 := rfl
  have hsn : 1 ≤ s p.a * p.n := Nat.mul_pos (by omega_using [hs6]) (by omega_using [hn])
  have hcnt : (2 ^ s p.a + 8) * p.n ≤ 32 * Layout.nodeSlots := by
    have := Nat.mul_le_mul (show 2 ^ s p.a + 8 ≤ 520 by omega_using [h512]) hn32
    rw [show Layout.nodeSlots = 520 from rfl]; omega_using [this]
  unfold subtreeHeights
  refine WP.seq (WP.mono (subB_ok hn hbx hw h1 h2 h4) fun u₁ B => ?_)
  have kB : ∀ q, q < 2 ^ 16 → (q < 3000 ∨ 3032 ≤ q) → u₁.mem (at' S q) = u.mem (at' S q) := fun q hq h =>
    keepS B.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dS S (by rw [oVar4]; omega_using [h]) (by omega_using [hq]) (by rw [oVar4]; omega_using [])
  have hE₁ : Env p u₁.mem S pkSeed a16 := env_bytes hn32 hE fun q hq => kB q
    (by simp only [EnvB] at hq; omega_using [hq]) (by simp only [EnvB] at hq; omega_using [hq])
  have hsp₁ : u₁.gpr .rsp = u.gpr .rsp := B.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hAU' : AU + BitVec.ofNat 64 p.n = SG + BitVec.ofNat 64 (dA + p.n) := by rw [hAU, Levels.add_add]
  have hsubA : Region.Sub ⟨AU + BitVec.ofNat 64 p.n, s p.a * p.n⟩ ⟨SG, L⟩ := by
    rw [hAU']; exact Offset.sub_base SG (by omega_using [hdA])
  have ht : ∀ (x : Nat), x < 2 ^ 32 → (BitVec.ofNat 64 x).toNat = x := fun x hx => by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hx])
  have hvA : ∀ i, 5 ≤ i → i ≤ 8 → (varAt u₁.mem S 4 i).toNat < 2 ^ 32 := fun i h₁ h₂ => by
    simp only [varAt]
    rcases (show i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega_using [h₁, h₂]) with rfl | rfl | rfl | rfl
    · rw [B.v5, ht _ (by omega_using [hX])]; omega_using [hX]
    · rw [B.v6, ht _ hX]; exact hX
    · rw [B.v7]; decide
    · rw [B.v8]; exact hKP
  refine WP.seq (lcall_ok T name ln hn hf hst hs63 (h := s p.a) (z₀ := 0) (L := L) (d := dA + p.n) (pkSeed := pkSeed)
    (a16 := a16) B.rdi B.rsi B.rdx B.rcx B.r8 (by rw [B.r9, h13, ht _ hidx]; exact hidx) (by omega_using [hs6])
    (by omega_using [hs9]) hcnt
    (by rw [B.wr]; exact hw) (by rw [B.wr]; exact hwG) hAU' (by omega_using [hdA]) hS (by rw [hsp₁]; exact hstk)
    (by rw [hAU', Levels.toNat_at (by omega_using [hGf, hdA, hsn])]; omega_using [hGf, hdA])
    (hGd.sub_left hsubA) (by rw [hsp₁]; exact hGs.sub_left hsubA) hE₁ hvA fun v' fx ev rt au fr => ?_)
  -- the root to the subtree roots
  have hv2 : v'.mem.readW (at' S (Layout.oVar 2 2)) 64 = BitVec.ofNat 64 U2 := by
    rw [← h2]
    refine Mem.readW_congr fun j hj => ?_
    rw [Levels.add_add, oVar2, ← kB (2704 + 8 * 2 + j) (by omega_using [hj]) (by omega_using [hj])]
    refine keepS fr fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with ⟨k, hk, rfl⟩ | rfl | rfl | rfl | rfl
      · exact dS S (.inl (by rw [laneA_eq]; omega_using [hj])) (by omega_using [hj]) (by rw [laneA_eq]; omega_using [hk, hn32])
      · exact Offset.disjoint_base S (by omega_using []) (by omega_using [hj])
      · exact dS S (.inr (by omega_using [])) (by omega_using [hj]) (by decide)
      · exact dS S (.inl (by rw [show Layout.oFrame 4 = 2912 from rfl]; omega_using [hj])) (by omega_using [hj]) (by decide)
      · exact dS S (.inl (by rw [show Layout.oN = 12640 from rfl]; omega_using [hj])) (by omega_using [hj])
          (by rw [show Layout.oN = 12640 from rfl]; rw [show Layout.nodeSlots = 520 from rfl] at hcnt; omega_using [hcnt])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dqlow (hGd.sub_left hsubA) (by omega_using [hj])
      · rw [hsp₁]; exact (hstk.sub_right (Levels.sub_scr S (by omega_using [hj]))).symm
  refine WP.mono_mx (by simpa [Code.allInstrs_eq, instrs] using rootCopy_nm ⟨p.n, p.len⟩ (s p.a))
    (rootCopy_ok hn (by rw [fx.cs _ (by simp [calleeSaved]), B.gpr _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hbx]) (by rw [fx.wr, B.wr]; exact hw) hv2 (by omega_using [hX]) hR
      (by omega_using [hs6])) fun u' ⟨g', r', w', mx', c', f'⟩ mxu => ?_
  have hva : ∀ i, varAt u₁.mem S 4 i = u₁.mem.readW (at' S (Layout.oVar 4 i)) 64 := fun _ => rfl
  rw [hva, hva, hva, B.v6, B.v7, B.v8, ht (V4 + U2) hX, ht 3 (by decide)] at rt
  rw [hva, hva, hva, hva, B.v5, B.v6, B.v7, B.v8, ht (V4 + U2) hX, ht U2 (by omega_using [hX]), ht 3 (by decide),
    B.r9, h13, ht idx hidx] at au
  -- the nodes `levels` started from
  have hL0 : ∀ j < 2 ^ s p.a, (nodesAt p u₁.mem (at' S Layout.oN) (2 ^ s p.a)).getD j [] =
      node p skSeed pkSeed a16 (u.gpr .r12).toNat ((V4 + U2) / 2 ^ 0 + j) 0 := fun j hj => by
    rw [Levels.getD_nodesAt _ _ hj, Levels.add_add, Nat.pow_zero, Nat.div_one, ← hN j hj]
    have : j * p.n + p.n ≤ 2 ^ s p.a * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
    exact bytesAt_ext fun i hi => by
      rw [Levels.add_add]
      have h5n := Nat.mul_le_mul h512 hn32
      exact kB _ (by rw [show Layout.oN = 12640 from rfl]; omega_using [this, hi, h5n])
        (.inr (by rw [show Layout.oN = 12640 from rfl]; omega_using []))
  have hup := up_node p skSeed pkSeed a16 (u.gpr .r12).toNat (L := nodesAt p u₁.mem (at' S Layout.oN) (2 ^ s p.a))
    (Levels.length_nodesAt _ _ _) (by rw [Nat.zero_add]; exact Nat.dvd_add hdv4 hdv2) hL0
  -- the signature, which the last block leaves
  have kA : ∀ r < s p.a, ∀ (m m' : Mem) (rs : List Region), Frame rs m m' → (∀ x ∈ rs, Region.Sub x ⟨S, Layout.oSigTmp⟩) →
      bytesAt m' (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n =
        bytesAt m (AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n)) p.n := fun r hr m m' rs f h => by
    have hrn : r * p.n + p.n ≤ s p.a * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hr
    have hsub : Region.Sub ⟨AU + BitVec.ofNat 64 p.n + BitVec.ofNat 64 (r * p.n), p.n⟩ ⟨SG, L⟩ :=
      fun x hx => hsubA x (Offset.sub_base _ hrn x hx)
    exact bytesAt_frame f (fun x hx => (hGd.sub_left hsub).sub_right (h x hx)) (by omega_using [hn32])
  have fslot : ∀ x ∈ [(⟨at' S (Layout.oRoots + U2 / 2 ^ s p.a * p.n), p.n⟩ : Region)], Region.Sub x ⟨S, Layout.oSigTmp⟩ :=
    fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      have := Nat.mul_le_mul (show U2 / 2 ^ s p.a + 1 ≤ 32 by omega_using [hR]) hn32
      rw [Nat.succ_mul] at this
      exact Offset.sub_base S (by
        rw [show Layout.oRoots = 29280 from rfl, show Layout.oSigTmp = 31648 from rfl]; omega_using [this])
  have fvar : ∀ x ∈ [(⟨at' S (Layout.oVar 4 5), 32⟩ : Region)], Region.Sub x ⟨S, Layout.oSigTmp⟩ := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx
    exact Offset.sub_base S (by rw [oVar4, show Layout.oSigTmp = 31648 from rfl]; omega_using [])
  have hcsr : ∀ r ∈ calleeSaved, r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 :=
    fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨⟨fun r hr => ?_, by rw [r', fx.rd, B.rd], by rw [w', fx.wr, B.wr], by rw [mx', fx.mx, B.mx]⟩,
    env_bytes hn32 ev fun q hq => keepS f' fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      simp only [EnvB] at hq
      have := Nat.mul_le_mul (show U2 / 2 ^ s p.a + 1 ≤ 32 by omega_using [hR]) hn32
      rw [Nat.succ_mul] at this
      exact dS S (.inl (by rw [show Layout.oRoots = 29280 from rfl]; omega_using [hq]))
        (by omega_using [hq]) (by rw [show Layout.oRoots = 29280 from rfl]; omega_using [this]), ?_, fun r hr => ?_, ?_⟩
  · obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hcsr r hr
    rw [g' _ h₀ h₁ h₂, fx.cs r hr, B.gpr _ h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇]
  · rw [c', rt]
    have e := (hup (s p.a) (Nat.le_refl _)).2 0 (by simp)
    rw [Nat.zero_add, Nat.add_zero] at e
    exact e
  · rw [kA r hr _ _ _ f' fslot, au r hr, Nat.zero_add, kA r hr _ _ _ B.frame fvar]
    congr 1
    obtain ⟨hlen, hget⟩ := hup r (by omega_using [hr])
    have hdr : 2 ^ r ∣ V4 := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega_using [hr])) hdv4
    exact pick_eq hlen (fun x => node p skSeed pkSeed a16 (u.gpr .r12).toNat (V4 / 2 ^ r + x) r) fun j hj => by
      rw [Nat.zero_add] at hget
      rw [hget j hj, div_add_dvd hdr, Nat.add_assoc]
  · refine (B.frame.sub fun x hx => ?_).trans ((fr.sub fun x hx => ?_).trans (f'.sub fun x hx => ?_))
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨⟨at' S (Layout.oFrame 4), 128⟩, by simp [levelsChanges],
        Offset.sub S (by rw [oVar4, show Layout.oFrame 4 = 2912 from rfl]; omega_using [])
          (by rw [oVar4, show Layout.oFrame 4 = 2912 from rfl]; omega_using [])⟩
    · rw [hsp₁] at hx
      refine ⟨x, ?_, fun _ h => h⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> simp
    · simp only [List.mem_singleton] at hx; subst hx
      exact ⟨_, by simp, fun _ h => h⟩

end VG.Proof.SlhDsa.X86_64.Fors
