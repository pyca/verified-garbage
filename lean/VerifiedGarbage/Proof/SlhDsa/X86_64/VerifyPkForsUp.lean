module

-- separate module: the heights and groups of `forsPk`, a stage of its proof rebuilt only when it changes

public import VerifiedGarbage.Proof.SlhDsa.X86_64.VerifyPkFors
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.X86_64.LevelsCorrect

/-!
# SLH-DSA on x86-64, `forsPk`: the heights and the groups

A height of a group (`forsUp`): each lane's node and the authentication path's
node, one `H` (`forsUp_ok`); the heights (`upLoop_ok`); a group's roots to
lane 0 of `B` (`froots_ok`); a group (`forsGroup_ok`) and the groups
(`forsGroups_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.X86_64

open VG VG.X86_64
open VG.Impl.SlhDsa.X86_64 (Layout setField setFieldR copyWords)
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Spec.SlhDsa
open VG.Proof.Sha3.X86_64 (Upd wp_mov wp_movm wp_addi wp_mov32i wp_store ea_at)
open VG.Proof.SlhDsa.X86_64.Levels (sx_ofNat add_add wp_add in_scr in_scr')

/-- The parts of the lanes `A` below `K` a height writes. -/
def upR (p : Params) (S : Addr) (K : Nat) : List Region :=
  (List.range K).map (fun k => ⟨at' S (Layout.laneA k + p.n + 24), 8 + 2 * p.n⟩)

/-- A height's lanes after those below `K`. -/
structure UInv (p : Params) (S sig : Addr) (t₀ z : Nat) (I : Nat → Nat) (u₀ : State) (K : Nat) (u : State) : Prop where
  gpr : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → u.gpr g = u₀.gpr g
  rd : u.rd = u₀.rd
  wr : u.wr = u₀.wr
  frame : Frame (upR p S K) u₀.mem u.mem
  done : ∀ k < K, bytesAt u.mem (at' S (Layout.laneA k + p.n + 32)) (2 * p.n) =
      (if lOf p I t₀ k / 2 ^ z % 2 = 0 then
        bytesAt u₀.mem (at' S (Layout.laneA k + p.n + 32)) p.n ++ authOf p u₀.mem sig t₀ k z
      else authOf p u₀.mem sig t₀ k z ++ bytesAt u₀.mem (at' S (Layout.laneA k + p.n + 32)) p.n) ∧
    bytesAt u.mem (at' S (Layout.laneA k + p.n + 24)) 8 = toByte (z + 1) 4 ++ toByte (lOf p I t₀ k / 2 ^ (z + 1)) 4

/-- A part of `scratch` outside the lanes `A` below `K` is outside `upR`. -/
theorem upR_disj {p : Params} (hn : p.n ≤ 32) (S : Addr) {K o l : Nat} (hK : K ≤ 4) (h₁ : o + l ≤ 2 ^ 16)
    (h₂ : ∀ c < K, o + l ≤ Layout.laneA c + p.n + 24 ∨ Layout.laneA c + 3 * p.n + 32 ≤ o) :
    ∀ r ∈ upR p S K, Region.Disjoint ⟨at' S o, l⟩ r := by
  intro r hr
  simp only [upR, List.mem_map, List.mem_range] at hr
  obtain ⟨c, hc, rfl⟩ := hr
  have := h₂ c hc
  have eA : Layout.laneA c = 3296 + 128 * c := rfl
  rw [eA] at this ⊢
  exact Offset.disjoint S (by omega) (by omega) (by omega)

/-- One lane of a height. -/
theorem ustep {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35) {S sig : Addr} {t₀ z K : Nat} {I : Nat → Nat} {u₀ u : State} (hK : K < 4)
    (ht₀ : t₀ + 4 < 2 ^ 31) (hz : z < p.a)
    (hbx : u₀.gpr .rbx = S) (h14 : u₀.gpr .r14 = sig)
    (hv0 : u₀.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀)
    (hv1 : u₀.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z)
    (hI : ∀ t < p.k, u₀.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u₀.wr) (hsr : (⟨sig, p.forsSigLen⟩ : Region) ∈ u₀.rd)
    (hsfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩)
    (hu : UInv p S sig t₀ z I u₀ K u) {Q : State → Prop}
    (k : ∀ u', UInv p S sig t₀ z I u₀ (K + 1) u' → Q u') :
    WP isa (Impl.SlhDsa.X86_64.Verify.forsUpLane p K) u Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  have hg := hu.gpr
  have hR : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → (o + l ≤ 3296 ∨ 3808 ≤ o) →
      ∀ r ∈ upR p S K, Region.Disjoint ⟨at' S o, l⟩ r :=
    fun h₁ h₂ => upR_disj hn32 S (by omega) h₁ fun c hc => by rw [eA]; omega
  have hsigR : ∀ {o l : Nat}, o + l ≤ p.forsSigLen → ∀ r ∈ upR p S K,
      Region.Disjoint ⟨sig + BitVec.ofNat 64 o, l⟩ r := fun h r hr => by
    simp only [upR, List.mem_map, List.mem_range] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    exact (hss.sub_left (Offset.sub_base sig h)).sub_right (Offset.sub_base S (by rw [eA]; omega))
  refine upLane_ok hn ha1 ha hk1 hk hK ht₀ hz (I := I)
    (by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbx])
    (by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h14])
    (by rw [hu.frame.readW (Region.contains_self _ _) (hR (by rw [oVar20]; omega) (by rw [oVar20]; omega)) (by decide), hv0])
    (by rw [hu.frame.readW (Region.contains_self _ _) (hR (by rw [oVar21]; omega) (by rw [oVar21]; omega)) (by decide), hv1])
    (fun t ht => by
      rw [hu.frame.readW (Region.contains_self _ _) (hR (by rw [oFidx_eq]; omega) (by rw [oFidx_eq]; omega)) (by decide),
        hI t ht])
    hIa (by rw [hu.wr]; exact hw) (by rw [hu.rd]; exact hsr) hsfit hss fun u' g' r' w' m' f' F' => k u' ?_
  have hKd : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 →
      (o + l ≤ Layout.laneA K + p.n + 24 ∨ Layout.laneA K + 3 * p.n + 32 ≤ o) →
      ∀ r ∈ [(⟨at' S (Layout.laneA K + p.n + 24), 8⟩ : Region), ⟨at' S (Layout.laneA K + p.n + 32), 2 * p.n⟩],
        Region.Disjoint ⟨at' S o, l⟩ r :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (rw [eA] at h₂ ⊢; exact Offset.disjoint S (by omega) (by omega) (by omega))
  have htK : tOf p t₀ K < p.k := by simp only [tOf]; omega
  have hsl := forsSig_le htK (show z + 1 ≤ p.a by omega)
  have e1 : p.n * (tOf p t₀ K * (p.a + 1) + 1) = p.n * (tOf p t₀ K * (p.a + 1)) + p.n := Nat.mul_succ _ _
  have e2 : p.n * (z + 1) = p.n * z + p.n := Nat.mul_succ _ _
  have e3 : z * p.n = p.n * z := Nat.mul_comm _ _
  have hauK : authOf p u.mem sig t₀ K z = authOf p u₀.mem sig t₀ K z :=
    bytesAt_frame hu.frame (hsigR (by omega)) (by omega)
  have hnK : bytesAt u.mem (at' S (Layout.laneA K + p.n + 32)) p.n =
      bytesAt u₀.mem (at' S (Layout.laneA K + p.n + 32)) p.n :=
    bytesAt_frame hu.frame (upR_disj hn32 S (by omega) (by rw [eA]; omega) fun c hc => by
      right; rw [eA, eA]; omega) (by omega)
  rw [hauK, hnK] at m'
  refine ⟨fun g h1 h2 h3 h4 h5 h6 => by rw [g' _ h1 h2 h3 h4 h5 h6, hg _ h1 h2 h3 h4 h5 h6],
    by rw [r', hu.rd], by rw [w', hu.wr], ?_, fun k' hk' => ?_⟩
  · have e : upR p S (K + 1) = upR p S K ++ [⟨at' S (Layout.laneA K + p.n + 24), 8 + 2 * p.n⟩] := by
      simp only [upR, List.range_succ, List.map_append, List.map_singleton]
    rw [e]
    refine (hu.frame.mono fun r hr => List.mem_append_left _ hr).trans (F'.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), Offset.sub S (by omega) (by omega)⟩
    · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), Offset.sub S (by omega) (by omega)⟩
  by_cases he : k' = K
  · subst he; exact ⟨m', f'⟩
  · have d := hu.done k' (by omega)
    rw [bytesAt_frame F' (hKd (by rw [eA]; omega) (by rw [eA, eA]; omega)) (by omega),
      bytesAt_frame F' (hKd (by rw [eA]; omega) (by rw [eA, eA]; omega)) (by omega)]
    exact d

/-- The first eight bytes of lane `k`'s fields: `ty` and `kp`. -/
theorem fields8 {m : Mem} {S : Addr} {o ty kp z i : Nat}
    (h : bytesAt m (at' S o) 16 = toByte ty 4 ++ toByte kp 4 ++ toByte z 4 ++ toByte i 4) :
    bytesAt m (at' S o) 8 = toByte ty 4 ++ toByte kp 4 := by
  rw [show (16 : Nat) = 8 + 8 from rfl, at', bytesAt_split2, List.append_assoc] at h
  exact (List.append_inj h (by rw [bytesAt_length']; simp [length_toByte'])).1

/-- Sixteen bytes, from two halves. -/
theorem fields16 {m : Mem} {S : Addr} {o : Nat} {A B : List Byte} (h₁ : bytesAt m (at' S o) 8 = A)
    (h₂ : bytesAt m (at' S (o + 8)) 8 = B) : bytesAt m (at' S o) 16 = A ++ B := by
  rw [show (16 : Nat) = 8 + 8 from rfl, at', bytesAt_split2, ← h₁, ← h₂]

/-- Height `z` of a group (`forsUp`): each lane's node one `H` up, with the
authentication path's node `z`, in the order bit `z` of its leaf says; then
`z + 1` in variable 1, setting ZF when it is `a`. -/
theorem forsUp_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} {S sig : Addr} {kp t₀ z : Nat} {I : Nat → Nat} {pkSeed a16 : List Byte} {V : Nat → List Byte}
    (ht₀ : t₀ + 4 < 2 ^ 31) (hz : z < p.a)
    (hbx : s.gpr .rbx = S) (h14 : s.gpr .r14 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀)
    (hv1 : s.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z)
    (hI : ∀ t < p.k, s.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (henv : Env p s.mem S pkSeed a16)
    (hsr : (⟨sig, p.forsSigLen⟩ : Region) ∈ s.rd)
    (hsfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩)
    (hl : ∀ j < 4, FLane p S j kp z (lOf p I t₀ j / 2 ^ z) (V j) s.mem)
    {Q : State → Prop}
    (k : ∀ s', (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 (z + 1) →
      s'.zf = some (decide (z + 1 = p.a)) →
      (∀ j < 4, FLane p S j kp (z + 1) (lOf p I t₀ j / 2 ^ (z + 1))
        (H p pkSeed (adrsOf a16 3 kp (z + 1) (lOf p I t₀ j / 2 ^ (z + 1)))
          (if lOf p I t₀ j / 2 ^ z % 2 = 0 then V j ++ authOf p s.mem sig t₀ j z
          else authOf p s.mem sig t₀ j z ++ V j)) s'.mem) →
      Frame (gFrame p S (s.gpr .rsp) stack) s.mem s'.mem → Q s') :
    WP isa (Impl.SlhDsa.X86_64.Verify.forsUp p f) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have hn8 : p.n % 8 = 0 := by omega_using [hn]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  unfold Impl.SlhDsa.X86_64.Verify.forsUp
  have h₀ : UInv p S sig t₀ z I s 0 s := ⟨fun _ _ _ _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.seq (ustep hn ha1 ha hk1 hk (by decide) ht₀ hz hbx h14 hv0 hv1 hI hIa hw hsr hsfit hss h₀ fun u₁ hu₁ => ?_)
  refine WP.seq (ustep hn ha1 ha hk1 hk (by decide) ht₀ hz hbx h14 hv0 hv1 hI hIa hw hsr hsfit hss hu₁ fun u₂ hu₂ => ?_)
  refine WP.seq (ustep hn ha1 ha hk1 hk (by decide) ht₀ hz hbx h14 hv0 hv1 hI hIa hw hsr hsfit hss hu₂ fun u₃ hu₃ => ?_)
  refine WP.seq (ustep hn ha1 ha hk1 hk (by decide) ht₀ hz hbx h14 hv0 hv1 hI hIa hw hsr hsfit hss hu₃ fun u hu => ?_)
  have hg := hu.gpr
  have hbu : u.gpr .rbx = S := by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  have hspu : u.gpr .rsp = s.gpr .rsp := hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hR : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → (o + l ≤ 3296 ∨ 3808 ≤ o) →
      ∀ r ∈ upR p S 4, Region.Disjoint ⟨at' S o, l⟩ r :=
    fun h₁ h₂ => upR_disj hn32 S (by omega) h₁ fun c hc => by rw [eA]; omega
  have hUG : ∀ r ∈ upR p S 4, ∃ r' ∈ gFrame p S (s.gpr .rsp) stack, Region.Sub r r' := fun r hr => by
    simp only [upR, List.mem_map, List.mem_range] at hr
    obtain ⟨c, hc, rfl⟩ := hr
    exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)),
      Offset.sub S (by omega) (by simp only [Layout.strideA]; rw [eA]; omega)⟩
  have hFu : Frame (gFrame p S (s.gpr .rsp) stack) s.mem u.mem := hu.frame.sub hUG
  have henvu := Env.of_frame hn32 henv (hFu.sub (gFrame_sub p S _ stack)) hstk
  have hwu : (⟨S, 2 ^ 16⟩ : Region) ∈ u.wr := by rw [hu.wr]; exact hw
  rw [ht]
  refine WP.seq (lanes_ok (p := p) T f.t4name hn hst hs63 (o := Layout.oA) (st := Layout.strideA) (len := 3 * p.n + 32)
    (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega) (by simp only [Layout.strideA]; omega) hbu hwu hS
    (by rw [hspu]; exact hstk) henvu.rc fun s₁ r₁ w₁ g₁ o₁ _ F₁ => ?_)
  rw [hspu] at F₁
  have hb₁ : s₁.gpr .rbx = S := by rw [g₁ _ (by decide), hbu]
  -- what the call leaves: the fields and variable 1
  have hcall : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → 2400 ≤ o →
      (∀ c < 4, o + l ≤ Layout.laneA c + p.n + 32 ∨ Layout.laneA c + 2 * p.n + 32 ≤ o) →
      ∀ r ∈ lanesOut p S Layout.oA Layout.strideA ++ [⟨S, 1600⟩, ⟨at' S 2368, 32⟩, below (s.gpr .rsp) stack],
        Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ h₃ r hr => by
    simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
    · have e : Layout.oA + Layout.strideA * c + p.n + 32 = Layout.laneA c + p.n + 32 := rfl
      have := h₃ c hc
      rw [e]; rw [eA] at this ⊢; exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact Offset.disjoint_base S (by omega) (by omega)
    · exact Offset.disjoint S (by omega) (by omega) (by omega)
    · exact (hstk.sub_right (Offset.sub_base S h₁)).symm
  have hv1₁ : s₁.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z := by
    rw [F₁.readW (Region.contains_self _ _) (hcall (by rw [oVar21]; omega) (by rw [oVar21]; omega)
      fun c hc => by rw [oVar21, eA]; omega) (by decide),
      hu.frame.readW (Region.contains_self _ _) (hR (by rw [oVar21]; omega) (by rw [oVar21]; omega)) (by decide), hv1]
  -- `z + 1`
  refine wp_movm (a := at' S (Layout.oVar 2 1)) (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, hb₁])
    (by rw [r₁, w₁, hu.rd, hu.wr, oVar21]; exact in_scr' hw (by omega)) fun s₂ u₂ => ?_
  refine wp_addi fun s₃ u₃ => ?_
  refine wp_store (a := at' S (Layout.oVar 2 1))
    (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, u₃.other _ (by decide), u₂.other _ (by decide), hb₁])
    (by rw [u₃.wr, u₂.wr, w₁, hu.wr, oVar21]; exact in_scr hw (by omega)) fun s₄ g₄ m₄ r₄ w₄ => ?_
  refine Levels.wp_cmpi fun s₅ g₅ m₅ r₅ w₅ z₅ => WP.block_nil ?_
  have hrax : s₃.gpr .rax = BitVec.ofNat 64 (z + 1) := by
    rw [u₃.gpr, u₂.gpr, hv1₁, sx1']; exact (BitVec.ofNat_add z 1).symm
  have hm₅ : s₅.mem = s₁.mem.writeW (at' S (Layout.oVar 2 1)) (BitVec.ofNat 64 (z + 1)) := by
    rw [m₅, m₄, hrax, u₃.mem, u₂.mem]
  have F₅ : Frame [⟨at' S (Layout.oVar 2 1), 8⟩] s₁.mem s₅.mem := by
    rw [hm₅]; exact (frame_writeW _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, fun _ h => h⟩
  have hv5 : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → (o + l ≤ 2712 ∨ 2720 ≤ o) →
      bytesAt s₅.mem (at' S o) l = bytesAt s₁.mem (at' S o) l := fun h₁ h₂ =>
    bytesAt_frame F₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [oVar21]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by omega)
  refine k s₅ (fun r hr => ?_) (by rw [r₅, r₄, u₃.rd, u₂.rd, r₁, hu.rd]) (by rw [w₅, w₄, u₃.wr, u₂.wr, w₁, hu.wr])
    (by rw [hm₅]; exact Mem.readW_writeW_self64 _ _ _) ?_ (fun j hj => ?_) ?_
  · have h : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .r10 ∧ r ≠ .r11 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₅, g₄, u₃.other _ h.1, u₂.other _ h.1, g₁ r hr, hg _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2]
  · rw [z₅, g₄, hrax, sx_ofNat (by omega), cmp_eq (by omega) (by omega)]
  · obtain ⟨d₁, d₂⟩ := hu.done j hj
    have hla : Layout.laneA j + 128 ≤ 3808 := by rw [eA]; omega
    have hf8 : bytesAt u.mem (at' S (Layout.laneA j + p.n + 16)) 8 = toByte 3 4 ++ toByte kp 4 := by
      rw [bytesAt_frame hu.frame (upR_disj hn32 S (by omega) (by omega) fun c hc => by
        have e₁ := eA c
        have e₂ := eA j
        rcases Nat.lt_or_ge c j with h | h
        · right; omega
        · left; omega) (by omega)]
      exact fields8 (hl j hj).fields
    have hf16 : bytesAt u.mem (at' S (Layout.laneA j + p.n + 16)) 16 =
        toByte 3 4 ++ toByte kp 4 ++ toByte (z + 1) 4 ++ toByte (lOf p I t₀ j / 2 ^ (z + 1)) 4 := by
      rw [fields16 hf8 (B := toByte (z + 1) 4 ++ toByte (lOf p I t₀ j / 2 ^ (z + 1)) 4) (by rw [show Layout.laneA j + p.n + 16 + 8 = Layout.laneA j + p.n + 24 by omega]; exact d₂)]
      simp only [List.append_assoc]
    have hcall' : ∀ {o l : Nat}, o + l ≤ Layout.laneA j + p.n + 32 → Layout.laneA j ≤ o →
        bytesAt s₁.mem (at' S o) l = bytesAt u.mem (at' S o) l := fun h₁ h₂ =>
      bytesAt_frame F₁ (hcall (by omega) (by rw [eA] at h₂; omega) fun c hc => by
        have e₁ := eA c
        have e₂ := eA j
        rcases Nat.lt_or_ge c j with h | h
        · right; omega
        · left; omega) (by omega)
    refine ⟨by rw [hv5 (by omega) (Or.inr (by rw [eA]; omega)), hcall' (by omega) (by omega)]; exact hf16, ?_⟩
    have o₀ := o₁ j hj
    rw [show Layout.oA + Layout.strideA * j + p.n + 32 = Layout.laneA j + p.n + 32 from rfl] at o₀
    rw [hv5 (by omega) (Or.inr (by rw [eA]; omega)), o₀, show 3 * p.n + 32 = p.n + 32 + 2 * p.n by omega,
      lane_msg henvu hj (2 * p.n) hf16, d₁, (hl j hj).value, Levels.H_shake hfam]
  · refine hFu.trans ((F₁.sub fun r hr => ?_).trans (F₅.sub fun r hr => ?_))
    · simp only [lanesOut, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with ⟨c, hc, rfl⟩ | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩)),
          Offset.sub S (by simp only [Layout.laneA]; omega) (by simp only [Layout.laneA, Layout.strideA, Layout.oA]; omega)⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)), fun _ h => h⟩
      · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
          fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), fun _ h => h⟩

/-- Lane `k`'s tree's authentication path, `a` nodes after its private key value. -/
abbrev authL (p : Params) (m : Mem) (sig : Addr) (t₀ k' : Nat) : List Byte :=
  bytesAt m (sig + BitVec.ofNat 64 (p.n * (tOf p t₀ k' * (p.a + 1) + 1))) (p.a * p.n)

theorem authOf_chunk (p : Params) (m : Mem) (sig : Addr) (t₀ k' : Nat) {z : Nat} (hz : z < p.a) :
    authOf p m sig t₀ k' z = chunk (authL p m sig t₀ k') p.n z := by
  rw [authL, chunk_bytesAt _ _ hz, authOf, add_add]

/-- The heights of a group (`.loop forsUp`), from height 0 (variable 1): each
lane's node its tree's root, the path from its leaf. -/
theorem upLoop_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} {S sig : Addr} {kp t₀ : Nat} {I : Nat → Nat} {pkSeed a16 : List Byte} {V : Nat → List Byte}
    (ht₀ : t₀ + 4 < 2 ^ 31)
    (hbx : s.gpr .rbx = S) (h14 : s.gpr .r14 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀)
    (hv1 : s.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 0)
    (hI : ∀ t < p.k, s.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (henv : Env p s.mem S pkSeed a16)
    (hsr : (⟨sig, p.forsSigLen⟩ : Region) ∈ s.rd)
    (hsfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩)
    (hsb : Region.Disjoint ⟨sig, p.forsSigLen⟩ (below (s.gpr .rsp) stack))
    (hl : ∀ j < 4, FLane p S j kp 0 (lOf p I t₀ j) (V j) s.mem)
    {Q : State → Prop}
    (k : ∀ s', (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      (∀ j < 4, bytesAt s'.mem (at' S (Layout.laneA j + p.n + 32)) p.n =
        path p pkSeed a16 3 kp (lOf p I t₀ j) (authL p s.mem sig t₀ j) p.a (V j)) →
      Frame (gFrame p S (s.gpr .rsp) stack) s.mem s'.mem → Q s') :
    WP isa (.loop (Impl.SlhDsa.X86_64.Verify.forsUp p f) .ne) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  -- what the frame leaves
  have hG : ∀ {m : Mem}, Frame (gFrame p S (s.gpr .rsp) stack) s.mem m →
      m.readW (at' S (Layout.oVar 2 0)) 64 = s.mem.readW (at' S (Layout.oVar 2 0)) 64 ∧
      (∀ t < p.k, m.readW (at' S (Layout.oFidx + 8 * t)) 64 = s.mem.readW (at' S (Layout.oFidx + 8 * t)) 64) := fun hf =>
    ⟨hf.readW (Region.contains_self _ _) (gFrame_disj hn32 hstk (by rw [oVar20] <;> omega)
      (Or.inr (Or.inl ⟨by rw [oVar20] <;> omega, by rw [oVar20] <;> omega⟩))) (by decide),
     fun t ht => hf.readW (Region.contains_self _ _) (gFrame_disj hn32 hstk (by rw [oFidx_eq] <;> omega)
      (Or.inr (Or.inr (Or.inr (Or.inr (by rw [oFidx_eq] <;> omega)))))) (by decide)⟩
  have hsigG : ∀ {m : Mem}, Frame (gFrame p S (s.gpr .rsp) stack) s.mem m → ∀ {o l : Nat}, o + l ≤ p.forsSigLen →
      bytesAt m (sig + BitVec.ofNat 64 o) l = bytesAt s.mem (sig + BitVec.ofNat 64 o) l := fun {m} hf {o l} hol =>
    bytesAt_frame hf (gFrame_disj' hn32 (hss.sub_left (Offset.sub_base sig hol))
      (hsb.sub_left (Offset.sub_base sig hol))) (by omega)
  let Inv : Nat → State → Prop := fun m t => ∃ z, m = p.a - z ∧ z < p.a ∧
    (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    t.mem.readW (at' S (Layout.oVar 2 1)) 64 = BitVec.ofNat 64 z ∧
    (∀ j < 4, FLane p S j kp z (lOf p I t₀ j / 2 ^ z)
      (path p pkSeed a16 3 kp (lOf p I t₀ j) (authL p s.mem sig t₀ j) z (V j)) t.mem) ∧
    Frame (gFrame p S (s.gpr .rsp) stack) s.mem t.mem
  have hbxcs : Reg.rbx ∈ calleeSaved := by decide
  have h14cs : Reg.r14 ∈ calleeSaved := by decide
  have hspcs : Reg.rsp ∈ calleeSaved := by decide
  refine WP.loop (M := isa) Inv (fun m t ⟨z, hm, hz, gt, rt, wt, vt, lt, ft⟩ => ?_) (p.a - 0) s
    ⟨0, rfl, ha1, fun _ _ => rfl, rfl, rfl, hv1, fun j hj => by
      rw [Nat.pow_zero, Nat.div_one]; exact hl j hj, Frame.refl _ _⟩
  have hsp : t.gpr .rsp = s.gpr .rsp := gt _ hspcs
  have henvt := Env.of_frame hn32 henv (ft.sub (gFrame_sub p S _ stack)) hstk
  obtain ⟨hv0t, hIt⟩ := hG ft
  refine forsUp_ok T ht hn hfam ha1 ha hk1 hk hst hs63 ht₀ hz (by rw [gt _ hbxcs, hbx]) (by rw [gt _ h14cs, h14])
    (by rw [hv0t, hv0]) vt (fun t' ht' => by rw [hIt t' ht', hI t' ht']) hIa (by rw [wt]; exact hw) hS
    (by rw [hsp]; exact hstk) henvt (by rw [rt]; exact hsr) hsfit hss lt fun t' g' r' w' v' z' l' f' => ?_
  rw [hsp] at f'
  have ft' := ft.trans f'
  have hstep : ∀ j < 4, FLane p S j kp (z + 1) (lOf p I t₀ j / 2 ^ (z + 1))
      (path p pkSeed a16 3 kp (lOf p I t₀ j) (authL p s.mem sig t₀ j) (z + 1) (V j)) t'.mem := fun j hj => by
    have hj' := l' j hj
    have htj : tOf p t₀ j < p.k := by simp only [tOf]; omega
    have hsl := forsSig_le htj (show z + 1 ≤ p.a by omega)
    have e1 : p.n * (tOf p t₀ j * (p.a + 1) + 1) = p.n * (tOf p t₀ j * (p.a + 1)) + p.n := Nat.mul_succ _ _
    have e2 : p.n * (z + 1) = p.n * z + p.n := Nat.mul_succ _ _
    have e3 : z * p.n = p.n * z := Nat.mul_comm _ _
    rw [authOf, hsigG ft (by omega), ← authOf, authOf_chunk p s.mem sig t₀ j hz] at hj'
    exact ⟨hj'.fields, by rw [hj'.value, path]⟩
  by_cases hlast : z + 1 = p.a
  · refine Or.inl ⟨by show t'.zf.map (!·) = some false; rw [z', decide_eq_true hlast]; rfl, ?_⟩
    exact k t' (fun r hr => by rw [g' r hr, gt r hr]) (by rw [r', rt]) (by rw [w', wt])
      (fun j hj => by rw [(hstep j hj).value, hlast]) ft'
  · refine Or.inr ⟨by show t'.zf.map (!·) = some true; rw [z', decide_eq_false hlast]; rfl, p.a - (z + 1),
      by omega, z + 1, rfl, by omega, fun r hr => by rw [g' r hr, gt r hr], by rw [r', rt], by rw [w', wt], v',
      hstep, ft'⟩

/-! ## The roots -/

/-- Tree `t`'s root, from its leaf `t·2^a + I t` and the signature at `sig`. -/
def rootOf (p : Params) (m : Mem) (sig : Addr) (pkSeed a16 : List Byte) (kp : Nat) (I : Nat → Nat) (t : Nat) :
    List Byte :=
  path p pkSeed a16 3 kp (t * 2 ^ p.a + I t) (bytesAt m (sig + BitVec.ofNat 64 (p.n * (t * (p.a + 1) + 1))) (p.a * p.n))
    p.a (F p pkSeed (adrsOf a16 3 kp 0 (t * 2 ^ p.a + I t)) (bytesAt m (sig + BitVec.ofNat 64 (p.n * (t * (p.a + 1)))) p.n))

theorem block_assoc4 {a b c d e : List Instr} {s : State} {Q : State → Prop}
    (h : WP isa (.block (a ++ (b ++ (c ++ (d ++ e))))) s Q) : WP isa (.block ((a ++ (b ++ (c ++ d))) ++ e)) s Q := by
  simpa only [List.append_assoc] using h

/-- Lane `k`'s root copied to tree `t`'s place in lane 0 of `B`'s message. -/
theorem rootLane_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35) {k' t₀ : Nat} (hk' : k' < 4) (ht₀ : t₀ + 4 < 2 ^ 31)
    {s : State} {S sig : Addr} {I : Nat → Nat} {is : List Instr} {Q : State → Prop}
    (hbx : s.gpr .rbx = S) (h14 : s.gpr .r14 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀)
    (hI : ∀ t < p.k, s.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr)
    (k : ∀ s', (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → s'.gpr g = s.gpr g) →
      s'.rd = s.rd → s'.wr = s.wr →
      bytesAt s'.mem (at' S (Layout.laneB 0 + p.n + 32 + tOf p t₀ k' * p.n)) p.n =
        bytesAt s.mem (at' S (Layout.laneA k' + p.n + 32)) p.n →
      Frame [⟨at' S (Layout.laneB 0 + p.n + 32 + tOf p t₀ k' * p.n), p.n⟩] s.mem s'.mem →
      WP isa (.block is) s' Q) :
    WP isa (.block ((Impl.SlhDsa.X86_64.Verify.treeOf p k' ++ ([.mov .rdx (.reg .r10)] : List Instr) ++
      Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++ ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
      copyWords .rdx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
        (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8)) ++ is)) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have e8 : 8 * (p.n / 8) = p.n := by omega_using [hn]
  have hmsg : (Impl.SlhDsa.X86_64.Shake.layout p).msgOff = p.n + 32 := rfl
  have eA : Layout.laneA k' = 3296 + 128 * k' := rfl
  have eB : Layout.laneB 0 = 3808 := rfl
  rw [hmsg]
  obtain ⟨c, hc⟩ : ∃ c, c = min (t₀ + k') (p.k - 1) := ⟨_, rfl⟩
  have hc' : tOf p t₀ k' = c := hc.symm
  rw [hc'] at k
  have hcl : c < p.k := by omega
  have hcn : c * p.n + p.n ≤ 35 * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine treeOf_ok hn ha1 ha hk1 hk (by omega) hbx h14 hv0 hI hIa hw fun s₁ g₁ m₁ r₁ w₁ h10₁ _ _ => ?_
  rw [← hc] at h10₁
  refine wp_mov fun s₂ u₂ => Levels.mulN_ok hn (r := .rdx) (tmp := .rcx) (by decide) fun s₃ h₃ g₃ m₃ r₃ w₃ => ?_
  refine wp_add fun s₄ u₄ => WP.block_append ?_
  have hb₄ : s₄.gpr .rbx = S := by
    rw [u₄.other _ (by decide), g₃ _ (by decide) (by decide), u₂.other _ (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  have hdx : s₄.gpr .rdx = S + BitVec.ofNat 64 (c * p.n) := by
    rw [u₄.gpr, h₃, u₂.gpr, h10₁, g₃ _ (by decide) (by decide), u₂.other _ (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbx, BitVec.add_comm,
      ← BitVec.ofNat_mul]
  have hm₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃, u₂.mem, m₁]
  have hw₄ : (⟨S, 2 ^ 16⟩ : Region) ∈ s₄.wr := by rw [u₄.wr, w₃, u₂.wr, w₁]; exact hw
  refine WP.mono (Levels.copy_ok (S := S) (t := .rdx) (sr := .rbx) (by decide) (by decide) (a := c * p.n) (b := 0)
    (d₁ := Layout.laneA k' + (p.n + 32)) (d₂ := Layout.laneB 0 + (p.n + 32)) (p.n / 8) s₄ hdx
    (by rw [hb₄]; exact Levels.scr0 S) hw₄ (by omega) (by rw [eB]; omega) (by rw [eA, eB]; omega))
    fun s₅ ⟨g₅, r₅, w₅, c₅, f₅⟩ => ?_
  have ea : at' S (Layout.laneB 0 + p.n + 32 + c * p.n) = S + BitVec.ofNat 64 (c * p.n + (Layout.laneB 0 + (p.n + 32))) := by
    rw [at']; congr 2; omega
  refine k s₅ (fun g h1 h2 h3 h4 h5 h6 => ?_) (by rw [r₅, u₄.rd, r₃, u₂.rd, r₁]) (by rw [w₅, u₄.wr, w₃, u₂.wr, w₁])
    ?_ (by rw [ea, ← hm₄]; rw [e8] at f₅; exact f₅)
  · rw [g₅ _ h1, u₄.other _ h3, g₃ _ h3 h2, u₂.other _ h3, g₁ _ h1 h2 h3 h4 h5 h6]
  · simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [ea, add_add, c₅ i (by omega), hm₄, at', Nat.zero_add, add_add,
      show Layout.laneA k' + (p.n + 32) + i = Layout.laneA k' + p.n + 32 + i by omega]

/-- The roots of a group after the lanes below `K`. -/
structure FRInv (p : Params) (S : Addr) (t₀ : Nat) (I : Nat → Nat) (u₀ : State) (V : Nat → List Byte) (K : Nat)
    (u : State) : Prop where
  gpr : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → u.gpr g = u₀.gpr g
  rd : u.rd = u₀.rd
  wr : u.wr = u₀.wr
  frame : Frame [⟨at' S (Layout.laneB 0 + p.n + 32), p.k * p.n⟩] u₀.mem u.mem
  ends : ∀ c < p.k, bytesAt u.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n =
    if t₀ ≤ c ∧ c < t₀ + K then V c else bytesAt u₀.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n

/-- One lane's root. -/
theorem rstepF {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35)
    {S sig : Addr} {t₀ K : Nat} {I : Nat → Nat} {u₀ u : State} {V : Nat → List Byte} (hK : K < 4) (ht₀k : t₀ < p.k)
    (ht₀ : t₀ + 4 < 2 ^ 31) (hbx : u₀.gpr .rbx = S) (h14 : u₀.gpr .r14 = sig)
    (hv0 : u₀.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀)
    (hI : ∀ t < p.k, u₀.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u₀.wr)
    (hval : ∀ k < 4, bytesAt u₀.mem (at' S (Layout.laneA k + p.n + 32)) p.n = V (tOf p t₀ k))
    (hu : FRInv p S t₀ I u₀ V K u) {is : List Instr} {Q : State → Prop}
    (k : ∀ u', FRInv p S t₀ I u₀ V (K + 1) u' → WP isa (.block is) u' Q) :
    WP isa (.block ((Impl.SlhDsa.X86_64.Verify.treeOf p K ++ ([.mov .rdx (.reg .r10)] : List Instr) ++
      Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++ ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
      copyWords .rdx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
        (Layout.laneA K + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8)) ++ is)) u Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  have eB : Layout.laneB 0 = 3808 := rfl
  have h35 : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul hk hn32
  have hBd : ∀ {o l : Nat}, o + l ≤ 3808 + p.n + 32 ∨ 3808 + p.n + 32 + p.k * p.n ≤ o → o + l ≤ 2 ^ 16 →
      ∀ r ∈ [(⟨at' S (Layout.laneB 0 + p.n + 32), p.k * p.n⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r :=
    fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  have hg := hu.gpr
  refine rootLane_ok hn ha1 ha hk1 hk hK ht₀ (I := I)
    (by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbx])
    (by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h14])
    (by rw [hu.frame.readW (Region.contains_self _ _) (hBd (by rw [oVar20]; omega) (by rw [oVar20]; omega)) (by decide), hv0])
    (fun t ht => by
      rw [hu.frame.readW (Region.contains_self _ _) (hBd (by rw [oFidx_eq]; omega) (by rw [oFidx_eq]; omega)) (by decide),
        hI t ht])
    hIa (by rw [hu.wr]; exact hw) fun u' g' r' w' e' F' => k u' ?_
  obtain ⟨c, hc⟩ : ∃ c, c = tOf p t₀ K := ⟨_, rfl⟩
  rw [← hc] at e' F'
  have hcl : c < p.k := by simp only [hc, tOf]; omega
  have hcn : c * p.n + p.n ≤ p.k * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hcl
  have hvK : bytesAt u.mem (at' S (Layout.laneA K + p.n + 32)) p.n = V c := by
    rw [bytesAt_frame hu.frame (hBd (by rw [eA]; omega) (by rw [eA]; omega)) (by omega), hval K hK, hc]
  refine ⟨fun g h1 h2 h3 h4 h5 h6 => by rw [g' _ h1 h2 h3 h4 h5 h6, hg _ h1 h2 h3 h4 h5 h6], by rw [r', hu.rd],
    by rw [w', hu.wr],
    hu.frame.trans (F'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub S (by omega) (by omega)⟩),
    fun c' hc' => ?_⟩
  by_cases he : c' = c
  · subst he
    rw [e', hvK, ite_eq_left (by simp only [hc, tOf]; omega)]
  · rw [bytesAt_frame F' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact chunk_disj S (o := Layout.laneB 0 + p.n + 32) he (by rw [eB]; omega) (by omega) (by omega)) (by omega),
      hu.ends c' hc']
    have hcK : c = min (t₀ + K) (p.k - 1) := hc
    by_cases h1 : t₀ ≤ c' ∧ c' < t₀ + K
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]

/-- The roots of a group (the last block of `forsGroup`): each lane's root to
its tree's place in lane 0 of `B`'s message; then `t₀ + 4` in variable 0, CF
set while below `k`. -/
theorem froots_ok {p : Params} (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35)
    {S sig : Addr} {t₀ : Nat} {I : Nat → Nat} {u₀ : State} {V : Nat → List Byte} (ht₀k : t₀ < p.k)
    (hbx : u₀.gpr .rbx = S) (h14 : u₀.gpr .r14 = sig)
    (hv0 : u₀.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀)
    (hI : ∀ t < p.k, u₀.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a) (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ u₀.wr)
    (hval : ∀ k < 4, bytesAt u₀.mem (at' S (Layout.laneA k + p.n + 32)) p.n = V (tOf p t₀ k))
    {Q : State → Prop}
    (k : ∀ u, (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ .rsi → g ≠ .r10 → g ≠ .r11 → u.gpr g = u₀.gpr g) →
      u.rd = u₀.rd → u.wr = u₀.wr →
      u.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 (t₀ + 4) →
      u.cf = some (decide (t₀ + 4 < p.k)) →
      (∀ c < p.k, bytesAt u.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n =
        if t₀ ≤ c ∧ c < t₀ + 4 then V c else bytesAt u₀.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n) →
      Frame [⟨at' S (Layout.laneB 0 + p.n + 32), p.k * p.n⟩, ⟨at' S (Layout.oVar 2 0), 8⟩] u₀.mem u.mem → Q u) :
    WP isa (.block ((List.range 4).flatMap (fun k' => Impl.SlhDsa.X86_64.Verify.treeOf p k' ++
        ([.mov .rdx (.reg .r10)] : List Instr) ++ Impl.SlhDsa.X86_64.Wots.mulN p.n .rdx .rcx ++
        ([.alu .add .rdx (.reg .rbx)] : List Instr) ++
        copyWords .rdx (Layout.laneB 0 + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) .rbx
          (Layout.laneA k' + (Impl.SlhDsa.X86_64.Shake.layout p).msgOff) (p.n / 8)) ++
      ([.mov .rax (.mem (Impl.SlhDsa.X86_64.Fors.var 0)), .alu .add .rax (.imm 4),
        .store (Impl.SlhDsa.X86_64.Fors.var 0) .rax,
        .alu .cmp .rax (.imm (BitVec.ofNat 32 p.k))] : List Instr))) u₀ Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have ht₀ : t₀ + 4 < 2 ^ 31 := by omega
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine block_assoc4 ?_
  have hE₀ : FRInv p S t₀ I u₀ V 0 u₀ := ⟨fun _ _ _ _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _,
    fun c _ => by rw [ite_eq_right (by omega)]⟩
  refine rstepF hn ha1 ha hk1 hk (by decide) ht₀k ht₀ hbx h14 hv0 hI hIa hw hval hE₀ fun u₁ hu₁ => ?_
  refine rstepF hn ha1 ha hk1 hk (by decide) ht₀k ht₀ hbx h14 hv0 hI hIa hw hval hu₁ fun u₂ hu₂ => ?_
  refine rstepF hn ha1 ha hk1 hk (by decide) ht₀k ht₀ hbx h14 hv0 hI hIa hw hval hu₂ fun u₃ hu₃ => ?_
  refine rstepF hn ha1 ha hk1 hk (by decide) ht₀k ht₀ hbx h14 hv0 hI hIa hw hval hu₃ fun u hu => ?_
  have eB : Layout.laneB 0 = 3808 := rfl
  have h35 : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul hk hn32
  have hbu : u.gpr .rbx = S := by rw [hu.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hbx]
  have hv0u : u.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀ := by
    rw [hu.frame.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [oVar20, eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by decide), hv0]
  refine wp_movm (a := at' S (Layout.oVar 2 0)) (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, hbu])
    (by rw [hu.rd, hu.wr, oVar20]; exact in_scr' hw (by omega)) fun s₅ u₅ => ?_
  refine wp_addi fun s₆ u₆ => ?_
  refine wp_store (a := at' S (Layout.oVar 2 0))
    (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, u₆.other _ (by decide), u₅.other _ (by decide), hbu])
    (by rw [u₆.wr, u₅.wr, hu.wr, oVar20]; exact in_scr hw (by omega)) fun s₇ g₇ m₇ r₇ w₇ => ?_
  refine wp_cmpi_cf fun s₈ g₈ m₈ r₈ w₈ _ c₈ => WP.block_nil ?_
  have hrax : s₆.gpr .rax = BitVec.ofNat 64 (t₀ + 4) := by
    rw [u₆.gpr, u₅.gpr, hv0u, show BitVec.signExtend 64 (4 : BitVec 32) = BitVec.ofNat 64 4 by decide]
    exact (BitVec.ofNat_add t₀ 4).symm
  have hm₈ : s₈.mem = u.mem.writeW (at' S (Layout.oVar 2 0)) (BitVec.ofNat 64 (t₀ + 4)) := by
    rw [m₈, m₇, hrax, u₆.mem, u₅.mem]
  have F₈ : Frame [⟨at' S (Layout.oVar 2 0), 8⟩] u.mem s₈.mem := by
    rw [hm₈]; exact (frame_writeW _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, fun _ h => h⟩
  refine k s₈ (fun g h1 h2 h3 h4 h5 h6 => by rw [g₈, g₇, u₆.other _ h1, u₅.other _ h1, hu.gpr _ h1 h2 h3 h4 h5 h6])
    (by rw [r₈, r₇, u₆.rd, u₅.rd, hu.rd]) (by rw [w₈, w₇, u₆.wr, u₅.wr, hu.wr])
    (by rw [hm₈]; exact Mem.readW_writeW_self64 _ _ _) ?_ (fun c hc => ?_) ?_
  · rw [c₈, g₇, hrax, sx_ofNat (by omega)]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · have hcn : c * p.n + p.n ≤ p.k * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
    rw [bytesAt_frame F₈ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [oVar20, eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by omega), hu.ends c hc]
  · refine (hu.frame.sub fun r hr => ?_).trans (F₈.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

/-! ## A group -/

/-- What a group changes: `gFrame`, lane 0 of `B`'s roots and variable 0. -/
def grFrame (p : Params) (S sp : Addr) (stack : Nat) : List Region :=
  gFrame p S sp stack ++ [⟨at' S (Layout.laneB 0 + p.n + 32), p.k * p.n⟩, ⟨at' S (Layout.oVar 2 0), 8⟩]

theorem grFrame_sub {p : Params} (hk : p.k ≤ 35) (hn : p.n ≤ 32) (S sp : Addr) (stack : Nat) :
    ∀ r ∈ grFrame p S sp stack, ∃ r' ∈ changes p S ++ [below sp stack], Region.Sub r r' := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact gFrame_sub p S sp stack r hr
  · have h35 : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul hk hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by decide), List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩))),
        Offset.sub S (e := Layout.laneB 0 + p.n + 16) (k := Layout.strideB - p.n - 16) (by omega)
          (by simp only [Layout.laneB, Layout.oB, Layout.strideB]; omega)⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))),
        Offset.sub S (by rw [oVar20]; simp only [Layout.oVars]; omega) (by rw [oVar20]; simp only [Layout.oVars]; omega)⟩

/-- A group of four trees (`forsGroup`), from `t₀` (variable 0): each tree's
root at its place in lane 0 of `B`'s message; then `t₀ + 4` in variable 0,
CF set while below `k`. -/
theorem forsGroup_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} {S sig : Addr} {kp t₀ : Nat} {I : Nat → Nat} {pkSeed a16 : List Byte}
    (ht₀ : t₀ < p.k) (hkp : kp < 2 ^ 32)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 kp) (h14 : s.gpr .r14 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀)
    (hI : ∀ t < p.k, s.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (henv : Env p s.mem S pkSeed a16)
    (hsr : (⟨sig, p.forsSigLen⟩ : Region) ∈ s.rd)
    (hsfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩)
    (hsb : Region.Disjoint ⟨sig, p.forsSigLen⟩ (below (s.gpr .rsp) stack))
    {Q : State → Prop}
    (k : ∀ t', (∀ r ∈ calleeSaved, t'.gpr r = s.gpr r) → t'.rd = s.rd → t'.wr = s.wr →
      t'.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 (t₀ + 4) →
      t'.cf = some (decide (t₀ + 4 < p.k)) →
      (∀ c < p.k, bytesAt t'.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n =
        if t₀ ≤ c ∧ c < t₀ + 4 then rootOf p s.mem sig pkSeed a16 kp I c
        else bytesAt s.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n) →
      Frame (grFrame p S (s.gpr .rsp) stack) s.mem t'.mem → Q t') :
    WP isa (Impl.SlhDsa.X86_64.Verify.forsGroup p f) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eA : ∀ c, Layout.laneA c = 3296 + 128 * c := fun c => rfl
  have eB : Layout.laneB 0 = 3808 := rfl
  have h35 : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul hk hn32
  have ht₀' : t₀ + 4 < 2 ^ 31 := by omega
  have hbxcs : Reg.rbx ∈ calleeSaved := by decide
  have h14cs : Reg.r14 ∈ calleeSaved := by decide
  have hspcs : Reg.rsp ∈ calleeSaved := by decide
  have hG : ∀ {m : Mem}, Frame (gFrame p S (s.gpr .rsp) stack) s.mem m →
      m.readW (at' S (Layout.oVar 2 0)) 64 = s.mem.readW (at' S (Layout.oVar 2 0)) 64 ∧
      (∀ t < p.k, m.readW (at' S (Layout.oFidx + 8 * t)) 64 = s.mem.readW (at' S (Layout.oFidx + 8 * t)) 64) := fun hf =>
    ⟨hf.readW (Region.contains_self _ _) (gFrame_disj hn32 hstk (by rw [oVar20] <;> omega)
      (Or.inr (Or.inl ⟨by rw [oVar20] <;> omega, by rw [oVar20] <;> omega⟩))) (by decide),
     fun t ht => hf.readW (Region.contains_self _ _) (gFrame_disj hn32 hstk (by rw [oFidx_eq] <;> omega)
      (Or.inr (Or.inr (Or.inr (Or.inr (by rw [oFidx_eq] <;> omega)))))) (by decide)⟩
  have hsigG : ∀ {m : Mem}, Frame (gFrame p S (s.gpr .rsp) stack) s.mem m → ∀ {o l : Nat}, o + l ≤ p.forsSigLen →
      bytesAt m (sig + BitVec.ofNat 64 o) l = bytesAt s.mem (sig + BitVec.ofNat 64 o) l := fun {m} hf {o l} hol =>
    bytesAt_frame hf (gFrame_disj' hn32 (hss.sub_left (Offset.sub_base sig hol))
      (hsb.sub_left (Offset.sub_base sig hol))) (by omega)
  unfold Impl.SlhDsa.X86_64.Verify.forsGroup
  -- the leaves
  refine WP.seq (forsLeaves_ok T ht hn hfam ha1 ha hk1 hk hst hs63 ht₀' hkp hbx h12 h14 hv0 hI hIa hw hS hstk henv hsr
    hsfit hss fun s₁ g₁ r₁ w₁ l₁ F₁ => ?_)
  -- variable 1 ← 0
  have hb₁ : s₁.gpr .rbx = S := by rw [g₁ _ hbxcs, hbx]
  refine WP.seq (wp_mov32i fun s₂ u₂ => wp_store (a := at' S (Layout.oVar 2 1))
    (by rw [Impl.SlhDsa.X86_64.Fors.var, ea_at, u₂.other _ (by decide), hb₁])
    (by rw [u₂.wr, w₁, oVar21]; exact in_scr hw (by omega)) fun s₃ g₃ m₃ r₃ w₃ => WP.block_nil ?_)
  have hm₃ : s₃.mem = s₁.mem.writeW (at' S (Layout.oVar 2 1)) (BitVec.ofNat 64 0) := by
    rw [m₃, u₂.gpr, u₂.mem, mov32_zero]; rfl
  have F₃ : Frame [⟨at' S (Layout.oVar 2 1), 8⟩] s₁.mem s₃.mem := by
    rw [hm₃]; exact (frame_writeW _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, fun _ h => h⟩
  have Fs₃ : Frame (gFrame p S (s.gpr .rsp) stack) s.mem s₃.mem := F₁.trans (F₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))), fun _ h => h⟩)
  have hcs₃ : ∀ r ∈ calleeSaved, s₃.gpr r = s.gpr r := fun r hr => by
    have h : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₃, u₂.other _ h, g₁ r hr]
  have hl₃ : ∀ j < 4, FLane p S j kp 0 (lOf p I t₀ j)
      (F p pkSeed (adrsOf a16 3 kp 0 (lOf p I t₀ j)) (skOf p s.mem sig t₀ j)) s₃.mem := fun j hj => by
    have hd : ∀ {o l : Nat}, Layout.laneA 0 ≤ o → o + l ≤ 2 ^ 16 →
        bytesAt s₃.mem (at' S o) l = bytesAt s₁.mem (at' S o) l := fun h₁ h₂ =>
      bytesAt_frame F₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [oVar21]; rw [eA] at h₁; exact Offset.disjoint S (by omega) (by omega) (by omega)) (by omega)
    exact ⟨by rw [hd (by rw [eA, eA]; omega) (by rw [eA]; omega)]; exact (l₁ j hj).fields,
      by rw [hd (by rw [eA, eA]; omega) (by rw [eA]; omega)]; exact (l₁ j hj).value⟩
  obtain ⟨hv0₃, hI₃⟩ := hG Fs₃
  -- the heights
  refine WP.seq (upLoop_ok T ht hn hfam ha1 ha hk1 hk hst hs63 ht₀' (by rw [hcs₃ _ hbxcs, hbx])
    (by rw [hcs₃ _ h14cs, h14]) (by rw [hv0₃, hv0]) (by rw [hm₃]; exact Mem.readW_writeW_self64 _ _ _)
    (fun t ht => by rw [hI₃ t ht, hI t ht]) hIa (by rw [w₃, u₂.wr, w₁]; exact hw) hS
    (by rw [hcs₃ _ hspcs]; exact hstk) (Env.of_frame hn32 henv (Fs₃.sub (gFrame_sub p S _ stack)) hstk)
    (by rw [r₃, u₂.rd, r₁]; exact hsr) hsfit hss (by rw [hcs₃ _ hspcs]; exact hsb) hl₃
    fun s₄ g₄ r₄ w₄ v₄ F₄ => ?_)
  rw [hcs₃ _ hspcs] at F₄
  have Fs₄ := Fs₃.trans F₄
  obtain ⟨hv0₄, hI₄⟩ := hG Fs₄
  have hcs₄ : ∀ r ∈ calleeSaved, s₄.gpr r = s.gpr r := fun r hr => by rw [g₄ r hr, hcs₃ r hr]
  -- the roots
  refine froots_ok (V := rootOf p s.mem sig pkSeed a16 kp I) hn ha1 ha hk1 hk ht₀ (by rw [hcs₄ _ hbxcs, hbx])
    (by rw [hcs₄ _ h14cs, h14]) (by rw [hv0₄, hv0]) (fun t ht => by rw [hI₄ t ht, hI t ht]) hIa
    (by rw [w₄, w₃, u₂.wr, w₁]; exact hw) (fun j hj => ?_) fun u g' r' w' v' c' e' F' => ?_
  · have htj : tOf p t₀ j < p.k := by simp only [tOf]; omega
    have hsl := forsSig_le htj (Nat.le_refl p.a)
    have e1 : p.n * (tOf p t₀ j * (p.a + 1) + 1) = p.n * (tOf p t₀ j * (p.a + 1)) + p.n := Nat.mul_succ _ _
    have e2 : p.n * p.a = p.a * p.n := Nat.mul_comm _ _
    rw [v₄ j hj, authL, hsigG Fs₃ (by omega)]
    rfl
  refine k u (fun r hr => ?_) (by rw [r', r₄, r₃, u₂.rd, r₁]) (by rw [w', w₄, w₃, u₂.wr, w₁]) v' c' (fun c hc => ?_) ?_
  · have h : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .r10 ∧ r ≠ .r11 := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g' _ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2, hcs₄ r hr]
  · have hcn : c * p.n + p.n ≤ p.k * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc
    rw [e' c hc, bytesAt_frame Fs₄ (gFrame_disj hn32 hstk (by rw [eB]; omega)
      (Or.inr (Or.inr (Or.inr (Or.inr (by rw [eB]; omega)))))) (by omega)]
  · refine (Fs₄.mono fun r hr => List.mem_append_left _ hr).trans (F'.sub fun r hr => ?_)
    exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩

/-- The groups (`.loop forsGroup`), from tree 0 (variable 0): every tree's
root at its place in lane 0 of `B`'s message. -/
theorem forsGroups_ok {p : Params} {f : Impl.SlhDsa.X86_64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (hn : p.n = 16 ∨ p.n = 24 ∨ p.n = 32) (hfam : p.family = .shake) (ha1 : 1 ≤ p.a) (ha : p.a ≤ 14)
    (hk1 : 1 ≤ p.k) (hk : p.k ≤ 35) {stack : Nat} (hst : T.stack + 16 ≤ stack) (hs63 : stack < 2 ^ 63)
    {s : State} {S sig : Addr} {kp : Nat} {I : Nat → Nat} {pkSeed a16 : List Byte} (hkp : kp < 2 ^ 32)
    (hbx : s.gpr .rbx = S) (h12 : s.gpr .r12 = BitVec.ofNat 64 kp) (h14 : s.gpr .r14 = sig)
    (hv0 : s.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 0)
    (hI : ∀ t < p.k, s.mem.readW (at' S (Layout.oFidx + 8 * t)) 64 = BitVec.ofNat 64 (I t))
    (hIa : ∀ t < p.k, I t < 2 ^ p.a)
    (hw : (⟨S, 2 ^ 16⟩ : Region) ∈ s.wr) (hS : S.toNat + 2 ^ 16 ≤ 2 ^ 64)
    (hstk : (below (s.gpr .rsp) stack).Disjoint ⟨S, 2 ^ 16⟩) (henv : Env p s.mem S pkSeed a16)
    (hsr : (⟨sig, p.forsSigLen⟩ : Region) ∈ s.rd)
    (hsfit : sig.toNat + p.forsSigLen ≤ 2 ^ 64) (hss : Region.Disjoint ⟨sig, p.forsSigLen⟩ ⟨S, 2 ^ 16⟩)
    (hsb : Region.Disjoint ⟨sig, p.forsSigLen⟩ (below (s.gpr .rsp) stack))
    {Q : State → Prop}
    (k : ∀ t', (∀ r ∈ calleeSaved, t'.gpr r = s.gpr r) → t'.rd = s.rd → t'.wr = s.wr →
      (∀ c < p.k, bytesAt t'.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n =
        rootOf p s.mem sig pkSeed a16 kp I c) →
      Frame (grFrame p S (s.gpr .rsp) stack) s.mem t'.mem → Q t') :
    WP isa (.loop (Impl.SlhDsa.X86_64.Verify.forsGroup p f) .b) s Q := by
  have hn32 : p.n ≤ 32 := by omega_using [hn]
  have eB : Layout.laneB 0 = 3808 := rfl
  have h35 : p.k * p.n ≤ 35 * 32 := Nat.mul_le_mul hk hn32
  have hgr : ∀ {o l : Nat}, o + l ≤ 2 ^ 16 → 3808 + p.n + 32 + p.k * p.n ≤ o →
      ∀ r ∈ grFrame p S (s.gpr .rsp) stack, Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact gFrame_disj hn32 hstk h₁ (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))) r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [eB]; exact Offset.disjoint S (by omega) (by omega) (by omega)
      · rw [oVar20]; exact Offset.disjoint S (by omega) (by omega) (by omega)
  have hgr' : ∀ {R : Region}, R.Disjoint ⟨S, 2 ^ 16⟩ → R.Disjoint (below (s.gpr .rsp) stack) →
      ∀ r ∈ grFrame p S (s.gpr .rsp) stack, R.Disjoint r := fun h₁ h₂ r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact gFrame_disj' hn32 h₁ h₂ r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁.sub_right (Offset.sub_base S (by rw [eB]; omega))
      · exact h₁.sub_right (Offset.sub_base S (by rw [oVar20]; omega))
  have hroot : ∀ {m : Mem}, Frame (grFrame p S (s.gpr .rsp) stack) s.mem m → ∀ c < p.k,
      rootOf p m sig pkSeed a16 kp I c = rootOf p s.mem sig pkSeed a16 kp I c := fun {m} hf c hc => by
    have hsl := forsSig_le hc (Nat.le_refl p.a)
    have e1 : p.n * (c * (p.a + 1) + 1) = p.n * (c * (p.a + 1)) + p.n := Nat.mul_succ _ _
    have e2 : p.n * p.a = p.a * p.n := Nat.mul_comm _ _
    have hs : ∀ {o l : Nat}, o + l ≤ p.forsSigLen →
        bytesAt m (sig + BitVec.ofNat 64 o) l = bytesAt s.mem (sig + BitVec.ofNat 64 o) l := fun hol =>
      bytesAt_frame hf (hgr' (hss.sub_left (Offset.sub_base sig hol)) (hsb.sub_left (Offset.sub_base sig hol)))
        (by omega)
    simp only [rootOf]
    rw [hs (by omega), hs (by omega)]
  let Inv : Nat → State → Prop := fun m t => ∃ t₀, m = p.k - t₀ ∧ t₀ < p.k ∧
    (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    t.mem.readW (at' S (Layout.oVar 2 0)) 64 = BitVec.ofNat 64 t₀ ∧
    (∀ c < p.k, c < t₀ → bytesAt t.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n =
      rootOf p s.mem sig pkSeed a16 kp I c) ∧
    Frame (grFrame p S (s.gpr .rsp) stack) s.mem t.mem
  have hbxcs : Reg.rbx ∈ calleeSaved := by decide
  have h12cs : Reg.r12 ∈ calleeSaved := by decide
  have h14cs : Reg.r14 ∈ calleeSaved := by decide
  have hspcs : Reg.rsp ∈ calleeSaved := by decide
  refine WP.loop (M := isa) Inv (fun m t ⟨t₀, hm, ht₀, gt, rt, wt, v0t, et, Ft⟩ => ?_) (p.k - 0) s
    ⟨0, rfl, by omega, fun _ _ => rfl, rfl, rfl, hv0, fun _ _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _⟩
  have hsp : t.gpr .rsp = s.gpr .rsp := gt _ hspcs
  have henvt := Env.of_frame hn32 henv (Ft.sub (grFrame_sub hk hn32 S _ stack)) hstk
  refine forsGroup_ok T ht hn hfam ha1 ha hk1 hk hst hs63 ht₀ hkp (by rw [gt _ hbxcs, hbx])
    (by rw [gt _ h12cs, h12]) (by rw [gt _ h14cs, h14]) v0t
    (fun t' ht' => by
      rw [Ft.readW (Region.contains_self _ _) (hgr (by rw [oFidx_eq]; omega) (by rw [oFidx_eq]; omega)) (by decide),
        hI t' ht'])
    hIa (by rw [wt]; exact hw) hS (by rw [hsp]; exact hstk) henvt (by rw [rt]; exact hsr) hsfit hss
    (by rw [hsp]; exact hsb) fun t' g' r' w' v0' c' e' F' => ?_
  rw [hsp] at F'
  have Ft' : Frame (grFrame p S (s.gpr .rsp) stack) s.mem t'.mem :=
    Ft.trans (F'.sub fun r hr => ⟨r, hr, fun _ h => h⟩)
  have he' : ∀ c < p.k, c < t₀ + 4 → bytesAt t'.mem (at' S (Layout.laneB 0 + p.n + 32 + c * p.n)) p.n =
      rootOf p s.mem sig pkSeed a16 kp I c := fun c hc hc4 => by
    rw [e' c hc]
    by_cases hg : t₀ ≤ c ∧ c < t₀ + 4
    · rw [ite_eq_left hg, hroot Ft c hc]
    · rw [ite_eq_right hg]; exact et c hc (by omega)
  by_cases hlast : t₀ + 4 < p.k
  · refine Or.inr ⟨by show t'.cf = some true; rw [c', decide_eq_true hlast], p.k - (t₀ + 4), by omega, t₀ + 4, rfl,
      hlast, fun r hr => by rw [g' r hr, gt r hr], by rw [r', rt], by rw [w', wt], v0', fun c hc hc4 => he' c hc hc4,
      Ft'⟩
  · refine Or.inl ⟨by show t'.cf = some false; rw [c', decide_eq_false hlast], ?_⟩
    exact k t' (fun r hr => by rw [g' r hr, gt r hr]) (by rw [r', rt]) (by rw [w', wt])
      (fun c hc => he' c hc (by omega)) Ft'

end VG.Proof.SlhDsa.X86_64
